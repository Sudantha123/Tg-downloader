#!/usr/bin/env python3
from __future__ import annotations

import asyncio
import gc
import html
import json
import logging
import os
import re
import signal
import subprocess
import threading
import time
import uuid
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from urllib.parse import urlparse, parse_qs, urljoin

import yt_dlp
from pyrogram import Client, StopTransmission, filters
from pyrogram.errors import FloodWait, RPCError
from pyrogram.types import InlineKeyboardButton, InlineKeyboardMarkup
from yt_dlp.utils import DownloadError

try:
    from curl_cffi import requests as cffi_requests
    from curl_cffi.const import CurlHttpVersion
    HAS_CURL_CFFI = True
except ImportError:
    try:
        from curl_cffi import requests as cffi_requests
        CurlHttpVersion = None
        HAS_CURL_CFFI = True
    except ImportError:
        cffi_requests = None
        CurlHttpVersion = None
        HAS_CURL_CFFI = False

try:
    import cloudscraper
    HAS_CLOUDSCRAPER = True
except ImportError:
    cloudscraper = None
    HAS_CLOUDSCRAPER = False

HTTP_V1_1 = getattr(CurlHttpVersion, "V1_1", 2) if CurlHttpVersion else 2

# ==================== CONFIG (1GB RAM / 1 OCPU OPTIMIZED) ====================

BASE_DIR = Path(__file__).resolve().parent
ENV_FILE = BASE_DIR / ".env"
COOKIE_ROOT = BASE_DIR / "cookies"
DOWNLOAD_DIR = Path(os.getenv("DOWNLOAD_DIR", str(BASE_DIR / "downloads")))


def load_env_file():
    if not ENV_FILE.is_file():
        return

    for raw in ENV_FILE.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        os.environ.setdefault(
            key.strip(),
            value.strip().strip('"').strip("'"),
        )


load_env_file()

API_ID = int(os.getenv("API_ID", "0"))
API_HASH = os.getenv("API_HASH", "").strip()
BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()

MAX_FILE_SIZE_MB = int(os.getenv("MAX_FILE_SIZE_MB", "2000"))
# 1GB RAM VM එකේ අනෙකුත් services වලට බාධා නොවීමට default concurrent jobs 2කට සීමා කර ඇත
MAX_CONCURRENT = max(1, int(os.getenv("BOT_MAX_CONCURRENT", "2")))
PROGRESS_INTERVAL = max(1.5, float(os.getenv("PROGRESS_INTERVAL", "2.5")))

# Cloudflare WARP SOCKS5 Proxy
YTDLP_PROXY = os.getenv("YTDLP_PROXY", "socks5://127.0.0.1:40000").strip()

if not API_ID or not API_HASH or not BOT_TOKEN:
    raise SystemExit(f"Missing API_ID, API_HASH or TELEGRAM_BOT_TOKEN in {ENV_FILE}")

DOWNLOAD_DIR.mkdir(parents=True, exist_ok=True)
COOKIE_ROOT.mkdir(parents=True, exist_ok=True)

try:
    COOKIE_ROOT.chmod(0o700)
except OSError:
    pass

logging.basicConfig(
    level=os.getenv("LOG_LEVEL", "INFO"),
    format="%(asctime)s %(levelname)s %(name)s: %(message)s",
)
log = logging.getLogger("reclip")

DEFAULT_UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
)

AD_URL_KEYWORDS = (
    "preroll", "midroll", "postroll", "vast", "adserver", "doubleclick",
    "exoclick", "juicyads", "popads", "trafficjunky", "magsrv", "realsrv",
    "tsyndicate", "banner", "promo", "trailer", "preview", "teaser",
    "thumb", "sprite", "pixel", "analytics",
)

# 1GB RAM සඳහා Workers 4 කට optimize කර ඇත (අඩු RAM පරිභෝජනයක් සඳහා)
app = Client(
    "reclip_telegram_bot",
    api_id=API_ID,
    api_hash=API_HASH,
    bot_token=BOT_TOKEN,
    workers=4,
    sleep_threshold=30,
)

# Bounded Caches (RAM පිරීම වැළැක්වීම සඳහා)
MAX_CACHE_ENTRIES = 40
sessions: dict[int, dict] = {}
url_info_cache: dict[str, tuple[float, dict]] = {}
CACHE_TTL_SECONDS = 900  # විනාඩි 15ක Instant URL Cache එකක්

cookie_upload_targets = {}
active_users = set()
active_jobs: dict[int, dict] = {}
active_lock = threading.Lock()
last_edit = {}


class JobCancelledError(Exception):
    """Raised when a user forcefully cancels an active download/upload job."""


def trim_memory():
    """Keep memory footprint tiny on 1GB RAM VPS."""
    now = time.time()
    expired_urls = [k for k, (ts, _) in url_info_cache.items() if now - ts > CACHE_TTL_SECONDS]
    for k in expired_urls:
        url_info_cache.pop(k, None)

    while len(url_info_cache) > MAX_CACHE_ENTRIES:
        oldest_key = next(iter(url_info_cache))
        url_info_cache.pop(oldest_key, None)

    while len(sessions) > MAX_CACHE_ENTRIES:
        oldest_uid = next(iter(sessions))
        sessions.pop(oldest_uid, None)

    gc.collect()


# ==================== PROCESS KILL & LOW-PRIORITY CPU EXECUTION ====================

def cleanup_job_files(job_id: str):
    if not job_id:
        return
    for path in DOWNLOAD_DIR.glob(f"*{job_id}*"):
        try:
            if path.is_file() or path.is_symlink():
                path.unlink(missing_ok=True)
        except OSError as exc:
            log.debug("Failed to delete %s: %s", path, exc)


def _low_priority_preexec():
    """
    Set new process group AND lower CPU/IO priority (nice 15) so FFmpeg/curl
    never starves other services running on the 1 OCPU Oracle VM!
    """
    os.setsid()
    try:
        os.nice(15)
    except OSError:
        pass


def force_kill_process_tree(proc: subprocess.Popen | None):
    if proc is None:
        return

    try:
        pgid = os.getpgid(proc.pid)
        os.killpg(pgid, signal.SIGKILL)
    except Exception:
        pass

    try:
        proc.kill()
    except Exception:
        pass


def cancel_user_job(uid: int) -> bool:
    with active_lock:
        job = active_jobs.get(uid)
        if not job:
            return False

        job["cancelled"].set()
        proc = job.get("proc")
        job_id = job.get("job_id", "")

    force_kill_process_tree(proc)

    if job_id:
        try:
            subprocess.run(
                ["pkill", "-9", "-f", job_id],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
            )
        except Exception:
            pass

        cleanup_job_files(job_id)

    trim_memory()
    return True


def run_tracked_subprocess(cmd: list[str], uid: int, timeout: int = 900):
    with active_lock:
        job = active_jobs.get(uid)
        if job and job["cancelled"].is_set():
            raise JobCancelledError("Cancelled by user.")

    proc = subprocess.Popen(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        preexec_fn=_low_priority_preexec,
    )

    with active_lock:
        job = active_jobs.get(uid)
        if job:
            job["proc"] = proc
            if job["cancelled"].is_set():
                force_kill_process_tree(proc)
                raise JobCancelledError("Cancelled by user.")

    try:
        stdout, stderr = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        force_kill_process_tree(proc)
        raise RuntimeError("Process timed out.")
    finally:
        with active_lock:
            job = active_jobs.get(uid)
            if job and job.get("proc") is proc:
                job["proc"] = None

    with active_lock:
        job = active_jobs.get(uid)
        if job and job["cancelled"].is_set():
            raise JobCancelledError("Cancelled by user.")

    if proc.returncode != 0:
        err_msg = (stderr or b"").decode("utf-8", errors="replace").strip()
        raise RuntimeError(err_msg or f"Command failed with exit code {proc.returncode}")

    return stdout


# ==================== FFMPEG VIDEO VERIFICATION (1 OCPU SAFE) ====================

def probe_video_metadata(video_path: Path) -> dict:
    meta = {
        "duration": 0,
        "width": 0,
        "height": 0,
        "vcodec": "",
        "acodec": "",
        "has_video": False,
        "has_audio": False,
    }
    try:
        out = subprocess.check_output(
            [
                "ffprobe",
                "-threads", "1",
                "-v", "error",
                "-print_format", "json",
                "-show_format",
                "-show_streams",
                str(video_path),
            ],
            stderr=subprocess.DEVNULL,
            timeout=20,
        )
        data = json.loads(out.decode("utf-8", errors="replace"))

        fmt_dur = float((data.get("format") or {}).get("duration") or 0)
        v_stream = None
        a_stream = None
        for s in data.get("streams") or []:
            if s.get("codec_type") == "video" and v_stream is None:
                v_stream = s
            elif s.get("codec_type") == "audio" and a_stream is None:
                a_stream = s

        if a_stream:
            meta["has_audio"] = True
            meta["acodec"] = (a_stream.get("codec_name") or "").lower()

        if v_stream:
            meta["has_video"] = True
            meta["vcodec"] = (v_stream.get("codec_name") or "").lower()
            width = int(v_stream.get("width") or 0)
            height = int(v_stream.get("height") or 0)
            stream_dur = float(v_stream.get("duration") or 0)

            rotation = 0
            tags = v_stream.get("tags") or {}
            if "rotate" in tags:
                try:
                    rotation = abs(int(tags["rotate"]))
                except ValueError:
                    pass
            for side in v_stream.get("side_data_list") or []:
                if "rotation" in side:
                    try:
                        rotation = abs(int(float(side["rotation"])))
                    except ValueError:
                        pass

            if rotation in (90, 270):
                width, height = height, width

            sar = v_stream.get("sample_aspect_ratio")
            if sar and ":" in sar and width > 0:
                try:
                    num, den = map(int, sar.split(":"))
                    if num > 0 and den > 0 and num != den:
                        width = int(round(width * num / den))
                except ValueError:
                    pass

            meta["width"] = width
            meta["height"] = height
            meta["duration"] = int(round(fmt_dur or stream_dur or 0))
        else:
            meta["duration"] = int(round(fmt_dur))
    except Exception as exc:
        log.warning("ffprobe failed for %s: %s", video_path.name, exc)

    return meta


def ensure_playable_seekable_mp4(video_path: Path, job_id: str, uid: int) -> Path:
    if not video_path.is_file() or video_path.stat().st_size < 10 * 1024:
        raise RuntimeError(
            "Downloaded file is empty or corrupted (only header/moov atom received)."
        )

    initial_meta = probe_video_metadata(video_path)
    if not initial_meta["has_video"] or initial_meta["width"] == 0:
        raise RuntimeError(
            "Downloaded file has no playable video stream."
        )

    fixed_path = DOWNLOAD_DIR / f"{job_id}_seekable.mp4"
    vcodec = initial_meta["vcodec"]
    acodec = initial_meta["acodec"]

    can_stream_copy = vcodec in ("h264", "avc1", "hevc", "h265") and acodec in ("aac", "mp3", "")

    if can_stream_copy:
        cmd = [
            "ffmpeg", "-y",
            "-threads", "1",
            "-fflags", "+genpts+igndts",
            "-i", str(video_path),
            "-c", "copy",
            "-map", "0:v:0",
            "-map", "0:a:0?",
            "-dn",
            "-movflags", "+faststart",
            str(fixed_path),
        ]
        try:
            run_tracked_subprocess(cmd, uid, timeout=240)
            if fixed_path.is_file() and fixed_path.stat().st_size > 10 * 1024:
                check_meta = probe_video_metadata(fixed_path)
                if check_meta["has_video"] and check_meta["duration"] >= 0:
                    video_path.unlink(missing_ok=True)
                    fixed_path.rename(video_path)
                    return video_path
        except JobCancelledError:
            raise
        except Exception as exc:
            log.warning("Stream copy remux failed (%s), falling back to 1-thread H.264 encode", exc)
            fixed_path.unlink(missing_ok=True)

    # 1-Thread ultrafast re-encode so 1 OCPU VM stays responsive
    encode_cmd = [
        "ffmpeg", "-y",
        "-threads", "1",
        "-i", str(video_path),
        "-map", "0:v:0",
        "-map", "0:a:0?",
        "-c:v", "libx264",
        "-preset", "ultrafast",
        "-crf", "24",
        "-pix_fmt", "yuv420p",
        "-vf", "scale=trunc(iw/2)*2:trunc(ih/2)*2",
        "-c:a", "aac",
        "-b:a", "128k",
        "-movflags", "+faststart",
        str(fixed_path),
    ]
    try:
        run_tracked_subprocess(encode_cmd, uid, timeout=900)
        if fixed_path.is_file() and fixed_path.stat().st_size > 10 * 1024:
            video_path.unlink(missing_ok=True)
            fixed_path.rename(video_path)
    except JobCancelledError:
        raise
    except Exception as exc:
        log.warning("H.264 re-encode fallback skipped: %s", exc)
        fixed_path.unlink(missing_ok=True)

    return video_path


def generate_video_thumbnail(
    video_path: Path,
    job_id: str,
    duration: int,
    uid: int,
) -> Path | None:
    thumb_path = DOWNLOAD_DIR / f"{job_id}_thumb.jpg"
    seek_sec = max(1.0, min(float(duration) * 0.15, 5.0)) if duration > 2 else 0.0

    for ts in ([seek_sec, 0.0] if seek_sec > 0 else [0.0]):
        cmd = [
            "ffmpeg", "-y",
            "-threads", "1",
            "-ss", f"{ts:.2f}",
            "-i", str(video_path),
            "-frames:v", "1",
            "-vf", "scale='min(320,iw)':'min(320,ih)':force_original_aspect_ratio=decrease",
            "-q:v", "4",
            str(thumb_path),
        ]
        try:
            run_tracked_subprocess(cmd, uid, timeout=20)
            if thumb_path.is_file() and thumb_path.stat().st_size > 0:
                return thumb_path
        except JobCancelledError:
            raise
        except Exception as exc:
            log.debug("Thumbnail capture at %ss failed: %s", ts, exc)

    return None


# ==================== URL HELPERS ====================

def is_tiktok_url(url: str) -> bool:
    host = (urlparse(url).hostname or "").lower()
    return host == "tiktok.com" or host.endswith(".tiktok.com")


def is_known_ytdlp_site(url: str) -> bool:
    """Identify sites with fast native yt-dlp extractors vs generic KVS/HTML sites."""
    host = (urlparse(url).hostname or "").lower()
    known = (
        "youtube.com", "youtu.be", "facebook.com", "fb.watch", "instagram.com",
        "twitter.com", "x.com", "reddit.com", "redd.it", "vimeo.com",
        "dailymotion.com", "twitch.tv", "soundcloud.com", "pinterest.com",
        "pin.it", "bilibili.com", "vk.com", "ok.ru", "streamable.com",
        "rumble.com", "bitchute.com", "PORNHUB.COM".lower(), "xvideos.com",
        "xnxx.com", "xhamster.com", "spankbang.com", "eporner.com", "redtube.com",
        "youporn.com", "tube8.com", "thumbzilla.com",
    )
    return any(host == d or host.endswith("." + d) for d in known)


def is_ad_or_junk_url(url: str) -> bool:
    low = url.lower()
    return any(kw in low for kw in AD_URL_KEYWORDS)


def normalize_url(url: str) -> str:
    url = url.strip()

    try:
        parsed = urlparse(url)
        host = (parsed.hostname or "").lower()
        video_id = None

        if host == "youtu.be":
            video_id = parsed.path.strip("/").split("/")[0]

        elif host in {
            "youtube.com",
            "www.youtube.com",
            "m.youtube.com",
            "music.youtube.com",
        }:
            if parsed.path == "/watch":
                video_id = parse_qs(parsed.query).get("v", [None])[0]
            else:
                match = re.match(
                    r"^/(?:shorts|embed|live)/([A-Za-z0-9_-]{11})",
                    parsed.path,
                )
                if match:
                    video_id = match.group(1)

        if video_id and re.fullmatch(r"[A-Za-z0-9_-]{11}", video_id):
            return f"https://www.youtube.com/watch?v={video_id}"

    except Exception:
        log.debug("URL normalization failed", exc_info=True)

    return url


def valid_url(url: str) -> bool:
    try:
        parsed = urlparse(url.strip())
        return (
            parsed.scheme in ("http", "https")
            and bool(parsed.hostname)
            and not any(c.isspace() for c in url)
        )
    except Exception:
        return False


def normalize_domain(value: str):
    value = value.strip().lower()

    if "://" in value:
        value = urlparse(value).hostname or ""

    value = value.split("/", 1)[0].split(":", 1)[0].strip(".")

    if (
        not value
        or "." not in value
        or ".." in value
        or not re.fullmatch(r"[a-z0-9.-]+", value)
    ):
        return None

    return value


def strip_ansi(text: str) -> str:
    return re.sub(r"\x1b\[[0-9;]*m|\[[0-9;]*m", "", text)


# ==================== COOKIE MANAGER ====================

def cookie_profile_dir(uid: int) -> Path:
    folder = COOKIE_ROOT / str(uid)
    folder.mkdir(parents=True, exist_ok=True)

    try:
        folder.chmod(0o700)
    except OSError:
        pass

    return folder


def parse_cookie_file(path: Path) -> list[dict]:
    records = []

    with open(path, "r", encoding="utf-8", errors="replace") as stream:
        for raw in stream:
            line = raw.rstrip("\r\n")

            if not line:
                continue

            if line.startswith("#HttpOnly_"):
                line = line[len("#HttpOnly_"):]
            elif line.startswith("#"):
                continue

            fields = line.split("\t")

            if len(fields) != 7:
                raise ValueError(
                    "Invalid Netscape cookies.txt format: "
                    "expected 7 tab-separated fields per cookie."
                )

            domain, subdomains, cookie_path, secure, expiry, name, value = fields

            if not domain or not name:
                continue

            try:
                expires = int(expiry or "0")
            except ValueError as exc:
                raise ValueError("Invalid cookie expiry timestamp.") from exc

            records.append({
                "domain": domain.lstrip(".").lower(),
                "include_subdomains": (
                    subdomains.upper() == "TRUE" or domain.startswith(".")
                ),
                "path": cookie_path or "/",
                "secure": secure.upper() == "TRUE",
                "expiry": expires,
                "name": name,
            })

    if not records:
        raise ValueError("No valid Netscape cookie records found.")

    return records


def cookie_domain_matches(cookie_domain, include_subdomains, host):
    cookie_domain = cookie_domain.lstrip(".").lower()
    host = (host or "").strip(".").lower()

    if host == cookie_domain or (include_subdomains and host.endswith("." + cookie_domain)):
        return True

    if host.endswith("." + cookie_domain):
        return True

    return False


def cookie_profiles(uid: int) -> list[dict]:
    result = []

    for path in sorted(cookie_profile_dir(uid).glob("*.txt")):
        try:
            records = parse_cookie_file(path)
            now = int(time.time())

            result.append({
                "domain": path.stem,
                "path": path,
                "count": len(records),
                "expired": sum(
                    1 for r in records
                    if r["expiry"] and r["expiry"] <= now
                ),
            })

        except (ValueError, OSError):
            result.append({
                "domain": path.stem,
                "path": path,
                "count": 0,
                "expired": 0,
                "invalid": True,
            })

    return result


def cookie_file_for_url(uid: int, url: str):
    url = normalize_url(url)
    host = (urlparse(url).hostname or "").lower()

    if not host:
        return None

    now = int(time.time())
    candidates = []

    for profile in cookie_profiles(uid):
        if profile.get("invalid"):
            continue

        try:
            records = parse_cookie_file(profile["path"])
        except (ValueError, OSError):
            continue

        matching = [
            r for r in records
            if cookie_domain_matches(
                r["domain"],
                r["include_subdomains"],
                host,
            )
            and not (r["expiry"] and r["expiry"] <= now)
        ]

        if matching:
            candidates.append((
                len(profile["domain"]),
                len(matching),
                profile["path"],
            ))

    selected = max(
        candidates,
        default=(0, 0, None),
        key=lambda item: (item[0], item[1]),
    )[2]

    if selected:
        log.info(
            "Cookie profile selected: %s for host %s",
            selected.name,
            host,
        )
    return selected


def cookie_options_for_url(uid: int, url: str) -> dict:
    path = cookie_file_for_url(uid, url)

    if path and path.is_file():
        return {"cookiefile": str(path)}

    return {}


# ==================== YT-DLP OPTIONS ====================

def make_ytdlp_options(uid, url, extra=None, fast_fetch=False, use_proxy=True):
    parsed = urlparse(url)
    origin = f"{parsed.scheme}://{parsed.netloc}" if parsed.scheme and parsed.netloc else url

    options = {
        "quiet": True,
        "no_warnings": True,
        "no_color": True,
        "noplaylist": True,
        "geo_bypass": True,
        "source_address": "0.0.0.0",
        "socket_timeout": 6 if fast_fetch else 25,
        "retries": 1 if fast_fetch else 3,
        "extractor_retries": 1 if fast_fetch else 2,
        "fragment_retries": 3,
        # 1GB RAM VM එකේ CPU සහ Network තදබදය අවම කිරීමට concurrent_fragment_downloads=2
        "concurrent_fragment_downloads": 2,
        "format_sort": ["vcodec:h264", "acodec:aac", "ext:mp4:m4a"],
        "http_headers": {
            "User-Agent": DEFAULT_UA,
            "Referer": url,
            "Origin": origin,
        },
        "extractor_args": {
            "youtube": {
                "player_client": ["default", "web_embedded"],
            },
        },
    }

    if use_proxy and YTDLP_PROXY:
        options["proxy"] = YTDLP_PROXY

    cookie_options = cookie_options_for_url(uid, url)
    options.update(cookie_options)

    if extra:
        options.update(extra)

    return options


# ==================== SMART QUALITY PARSER & SELECTOR ====================

def infer_format_height(fmt: dict) -> int:
    h = fmt.get("height")
    w = fmt.get("width")
    if isinstance(h, (int, float)) and h > 0:
        if isinstance(w, (int, float)) and w > 0 and h > w:
            return int(w)
        return int(h)

    res = str(fmt.get("resolution") or "")
    m = re.search(r"(\d{3,4})x(\d{3,4})", res)
    if m:
        d1, d2 = int(m.group(1)), int(m.group(2))
        return min(d1, d2)

    for field in ("format_note", "format", "format_id", "url"):
        val = str(fmt.get(field) or "")
        m = re.search(r"(?:^|[^0-9])(144|240|360|480|540|720|1080|1440|2160)[pP]?(?:$|[^0-9])", val)
        if m:
            return int(m.group(1))

    fid_low = str(fmt.get("format_id") or "").lower()
    if "hd" in fid_low or "high" in fid_low:
        return 720
    if "sd" in fid_low or "low" in fid_low:
        return 480

    return 0


def unwrap_main_entry(info: dict) -> dict:
    if not info:
        return info

    entries = info.get("entries")
    if not entries:
        return info

    valid_entries = [e for e in entries if isinstance(e, dict) and (e.get("formats") or e.get("url"))]
    if not valid_entries:
        return info

    non_ad = [
        e for e in valid_entries
        if not is_ad_or_junk_url(str(e.get("url") or e.get("webpage_url") or ""))
        and not is_ad_or_junk_url(str(e.get("title") or ""))
    ]
    pool = non_ad or valid_entries

    best_entry = max(
        pool,
        key=lambda e: (
            float(e.get("duration") or 0),
            len(e.get("formats") or []),
        ),
    )
    return best_entry


def quality_options(info: dict) -> list[tuple[str, str]]:
    info = unwrap_main_entry(info)
    by_height: dict[int, tuple[tuple, str, int]] = {}
    duration = float(info.get("duration") or 0)

    for fmt in info.get("formats", []):
        vcodec = str(fmt.get("vcodec") or "").lower()
        acodec = str(fmt.get("acodec") or "").lower()

        if vcodec == "none" or "images" in str(fmt.get("format_note") or "").lower():
            continue
        if fmt.get("ext") in ("mhtml", "jpg", "png", "webp"):
            continue

        fmt_url = str(fmt.get("url") or "")
        if fmt_url and is_ad_or_junk_url(fmt_url):
            continue

        height = infer_format_height(fmt)
        if height < 120 or height > 4320:
            continue

        fmt_id = str(fmt.get("format_id") or "")
        if not fmt_id or len(fmt_id) > 35:
            continue

        is_h264 = 1 if ("avc" in vcodec or "h264" in vcodec) else 0
        has_audio = 1 if (acodec and acodec != "none") else 0
        fsize = int(fmt.get("filesize") or fmt.get("filesize_approx") or 0)
        tbr = float(fmt.get("tbr") or fmt.get("vbr") or 0)
        if not fsize and tbr > 0 and duration > 0:
            fsize = int(tbr * 1000 / 8 * duration)

        score = (is_h264, has_audio, tbr, fsize)
        old = by_height.get(height)

        if old is None or score > old[0]:
            by_height[height] = (score, fmt_id, fsize)

    result = []
    for height, (_, fmt_id, fsize) in sorted(by_height.items(), key=lambda x: x[0], reverse=True):
        if fsize > 0:
            label = f"{height}p ({human_size(fsize)})"
        else:
            label = f"{height}p"
        result.append((f"{fmt_id}|{height}", label))

    return result[:12]


def build_video_format_selector(info: dict, selection: str) -> str:
    if selection == "best" or not selection:
        return (
            "bestvideo[vcodec^=avc1]+bestaudio[acodec^=mp4a]/"
            "bestvideo[vcodec^=h264]+bestaudio/"
            "bestvideo+bestaudio/best"
        )

    if "|" in selection:
        fmt_id, height_str = selection.split("|", 1)
        try:
            height = int(height_str)
        except ValueError:
            height = 0
    else:
        fmt_id = selection
        height = 0

    has_bundled_audio = False
    for fmt in info.get("formats", []):
        if str(fmt.get("format_id", "")) == fmt_id:
            acodec = str(fmt.get("acodec") or "").lower()
            if acodec and acodec != "none":
                has_bundled_audio = True
            if not height:
                height = infer_format_height(fmt)
            break

    parts = []
    if has_bundled_audio:
        parts.append(f"{fmt_id}")
        parts.append(f"{fmt_id}+bestaudio")
    else:
        parts.append(f"{fmt_id}+bestaudio[acodec^=mp4a]")
        parts.append(f"{fmt_id}+bestaudio")
        parts.append(f"{fmt_id}")

    if height > 0:
        parts.append(f"bestvideo[height={height}][vcodec^=avc1]+bestaudio[acodec^=mp4a]")
        parts.append(f"bestvideo[height={height}]+bestaudio")
        parts.append(f"best[height={height}]")
        parts.append(f"bestvideo[height<={height}]+bestaudio/best[height<={height}]")

    return "/".join(parts)


# ==================== ULTRA-FAST PARALLEL RACING FETCHER ====================

def decrypt_kvs_url(real_url: str, license_code: str) -> str:
    real_url = real_url.strip()
    if not real_url.startswith("function/0/"):
        return real_url

    real_url = real_url[len("function/0/"):]
    if not license_code:
        return real_url

    lic_digits = [int(ch) for ch in license_code if ch.isdigit()]
    if not lic_digits:
        return real_url

    lic_str = "".join(str(d) for d in lic_digits)
    while len(lic_str) < 32:
        lic_str += lic_str
    lic_map = [int(ch) or 10 for ch in lic_str[:32]]

    parts = real_url.split("/")
    if len(parts) < 6:
        return real_url

    hash_part = parts[5][:32]
    if len(hash_part) == 32:
        chars = list(hash_part)
        for idx in range(31, -1, -1):
            swap_idx = (idx + sum(lic_map[idx:])) % 32
            chars[idx], chars[swap_idx] = chars[swap_idx], chars[idx]
        parts[5] = "".join(chars) + parts[5][32:]

    return "/".join(parts)


def extract_kvs_flashvars(page_html: str, base_url: str) -> list[tuple[str, int, str]]:
    lic_match = re.search(r"['\"]?license_code['\"]?\s*:\s*['\"]([^'\"]+)['\"]", page_html)
    license_code = lic_match.group(1) if lic_match else ""

    url_keys = [
        ("video_url", "video_url_text", 480),
        ("video_alt_url", "video_alt_url_text", 720),
        ("video_alt_url2", "video_alt_url2_text", 1080),
        ("video_alt_url3", "video_alt_url3_text", 1440),
    ]

    found = []
    seen_urls = set()

    for key, text_key, default_h in url_keys:
        m = re.search(rf"['\"]?{key}['\"]?\s*:\s*['\"]([^'\"]+)['\"]", page_html)
        if not m:
            continue

        raw_val = m.group(1).strip().replace("\\/", "/")
        if not raw_val or raw_val.startswith("#"):
            continue

        decrypted = decrypt_kvs_url(raw_val, license_code)
        full_url = urljoin(base_url, decrypted)

        if full_url in seen_urls or not full_url.startswith(("http://", "https://")):
            continue
        if is_ad_or_junk_url(full_url):
            continue
        seen_urls.add(full_url)

        height = default_h
        tm = re.search(rf"['\"]?{text_key}['\"]?\s*:\s*['\"]([^'\"]+)['\"]", page_html)
        if tm:
            hm = re.search(r"(\d{3,4})", tm.group(1))
            if hm:
                height = int(hm.group(1))
        else:
            hm = re.search(r"_(\d{3,4})p\.mp4", full_url, re.IGNORECASE)
            if hm:
                height = int(hm.group(1))

        found.append((f"kvs_{height}p", height, full_url))

    return found


def _is_valid_unblocked_html(text: str) -> bool:
    if not text or len(text) < 250:
        return False
    head = text[:1200]
    if "Just a moment..." in head or "Attention Required! | Cloudflare" in head:
        return False
    if "cf-browser-verification" in head or "_cf_chl_opt" in head:
        return False
    return True


def fetch_html_parallel_race(url: str, uid: int) -> tuple[str, dict[str, str]]:
    """
    Race multiple lightweight HTTP pathways concurrently (Direct Chrome TLS, WARP Chrome TLS,
    Mobile Safari TLS, and Cloudscraper) with a short 6-second timeout.
    Whichever pathway succeeds first returns immediately (< 1.5 seconds)!
    """
    saved_cookie_path = cookie_file_for_url(uid, url)
    saved_cookies_dict: dict[str, str] = {}
    if saved_cookie_path and saved_cookie_path.is_file():
        try:
            with open(saved_cookie_path, "r", encoding="utf-8", errors="replace") as cf:
                for line in cf:
                    if line.startswith("#") and not line.startswith("#HttpOnly_"):
                        continue
                    parts = line.rstrip("\r\n").split("\t")
                    if len(parts) == 7:
                        saved_cookies_dict[parts[5]] = parts[6]
        except Exception:
            pass

    headers = {
        "User-Agent": DEFAULT_UA,
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "en-US,en;q=0.9",
        "Referer": url,
    }

    def _try_cffi(proxy_val: str | None, target: str) -> tuple[str, dict[str, str]]:
        if not HAS_CURL_CFFI:
            raise RuntimeError("curl_cffi unavailable")
        resp = cffi_requests.get(
            url,
            impersonate=target,
            headers=headers,
            cookies=saved_cookies_dict or None,
            http_version=HTTP_V1_1,
            proxy=proxy_val,
            timeout=6,
            allow_redirects=True,
        )
        if resp.status_code == 200 and _is_valid_unblocked_html(resp.text):
            cookies = dict(saved_cookies_dict)
            if hasattr(resp, "cookies"):
                cookies.update(dict(resp.cookies))
            return resp.text, cookies
        raise RuntimeError(f"HTTP {resp.status_code}")

    def _try_cloudscraper(proxy_val: str | None) -> tuple[str, dict[str, str]]:
        if not HAS_CLOUDSCRAPER:
            raise RuntimeError("cloudscraper unavailable")
        scraper = cloudscraper.create_scraper(
            browser={"browser": "chrome", "platform": "windows", "mobile": False}
        )
        proxies = {"http": proxy_val, "https": proxy_val} if proxy_val else None
        resp = scraper.get(
            url,
            headers=headers,
            cookies=saved_cookies_dict or None,
            proxies=proxies,
            timeout=6,
        )
        if resp.status_code == 200 and _is_valid_unblocked_html(resp.text):
            cookies = dict(saved_cookies_dict)
            cookies.update(scraper.cookies.get_dict())
            return resp.text, cookies
        raise RuntimeError(f"Cloudscraper HTTP {resp.status_code}")

    def _try_urllib() -> tuple[str, dict[str, str]]:
        import urllib.request
        import http.cookiejar

        cj = http.cookiejar.CookieJar()
        opener = urllib.request.build_opener(urllib.request.HTTPCookieProcessor(cj))
        req_headers = dict(headers)
        if saved_cookies_dict:
            req_headers["Cookie"] = "; ".join(f"{k}={v}" for k, v in saved_cookies_dict.items())
        req = urllib.request.Request(url, headers=req_headers)
        with opener.open(req, timeout=5) as resp:
            page_html = resp.read().decode("utf-8", errors="replace")
            if _is_valid_unblocked_html(page_html):
                cookies = dict(saved_cookies_dict)
                for c in cj:
                    cookies[c.name] = c.value
                return page_html, cookies
        raise RuntimeError("urllib blocked")

    tasks = []
    if HAS_CURL_CFFI:
        if YTDLP_PROXY:
            tasks.append(lambda: _try_cffi(YTDLP_PROXY, "chrome110"))
            tasks.append(lambda: _try_cffi(YTDLP_PROXY, "safari15_5"))
        tasks.append(lambda: _try_cffi(None, "chrome110"))
    if HAS_CLOUDSCRAPER:
        if YTDLP_PROXY:
            tasks.append(lambda: _try_cloudscraper(YTDLP_PROXY))
        tasks.append(lambda: _try_cloudscraper(None))
    tasks.append(_try_urllib)

    last_err = None
    with ThreadPoolExecutor(max_workers=min(4, len(tasks))) as pool:
        futures = [pool.submit(fn) for fn in tasks]
        for fut in as_completed(futures):
            try:
                html_text, cookies = fut.result()
                if html_text:
                    return html_text, cookies
            except Exception as exc:
                last_err = exc

    raise last_err or RuntimeError("Cloudflare blocked all fast pathways. Upload cookies via /cookies domain.com")


def expand_hls_master_playlist(m3u8_url: str, referer: str, cookies: dict[str, str], uid: int) -> list[dict]:
    variants = []
    try:
        m3u8_text, _ = fetch_html_parallel_race(m3u8_url, uid)
        if "#EXT-X-STREAM-INF" not in m3u8_text:
            return []

        lines = [ln.strip() for ln in m3u8_text.splitlines() if ln.strip()]
        for i, line in enumerate(lines):
            if line.startswith("#EXT-X-STREAM-INF:") and i + 1 < len(lines):
                stream_line = lines[i + 1]
                if stream_line.startswith("#"):
                    continue
                variant_url = urljoin(m3u8_url, stream_line)
                height = 0
                res_m = re.search(r"RESOLUTION=(\d+)x(\d+)", line, re.IGNORECASE)
                if res_m:
                    height = min(int(res_m.group(1)), int(res_m.group(2)))
                if not height:
                    name_m = re.search(r"NAME=\"?(\d{3,4})p?\"?", line, re.IGNORECASE)
                    if name_m:
                        height = int(name_m.group(1))
                bw_m = re.search(r"BANDWIDTH=(\d+)", line, re.IGNORECASE)
                tbr = int(bw_m.group(1)) // 1000 if bw_m else (height * 3 if height else 1500)
                if height >= 144:
                    variants.append({
                        "format_id": f"hls_{height}p",
                        "height": height,
                        "vcodec": "h264",
                        "acodec": "aac",
                        "tbr": tbr,
                        "url": variant_url,
                    })
    except Exception as exc:
        log.debug("HLS master playlist expansion skipped: %s", exc)

    return variants


def generic_cffi_extract(url: str, uid: int = 0) -> dict:
    page_html, session_cookies = fetch_html_parallel_race(url, uid)

    if "flashvars" not in page_html and "video_url" not in page_html and "<video" not in page_html.lower():
        iframe_match = re.search(
            r'<iframe[^>]+src=["\']([^"\']*(?:embed|player|video)[^"\']*)["\']',
            page_html,
            re.IGNORECASE,
        )
        if iframe_match:
            embed_url = urljoin(url, iframe_match.group(1))
            if not is_ad_or_junk_url(embed_url):
                try:
                    embed_html, embed_cookies = fetch_html_parallel_race(embed_url, uid)
                    page_html = page_html + "\n" + embed_html
                    session_cookies.update(embed_cookies)
                except Exception:
                    pass

    title_match = re.search(r"<title[^>]*>(.*?)</title>", page_html, re.IGNORECASE | re.DOTALL)
    title = html.unescape(title_match.group(1).strip()) if title_match else "Video"

    thumb_match = re.search(
        r'<meta[^>]+property=["\']og:image["\'][^>]+content=["\']([^"\']+)["\']',
        page_html,
        re.IGNORECASE,
    )
    if not thumb_match:
        thumb_match = re.search(r"['\"]?preview_url['\"]?\s*:\s*['\"]([^'\"]+)['\"]", page_html)
    thumbnail = urljoin(url, thumb_match.group(1).replace("\\/", "/")) if thumb_match else None

    formats = []
    urls_map = {}

    # 1. KVS Player flashvars decryptor
    kvs_streams = extract_kvs_flashvars(page_html, url)
    for fid, height, stream_url in kvs_streams:
        formats.append({
            "format_id": fid,
            "height": height,
            "vcodec": "h264",
            "acodec": "aac",
            "tbr": height * 3,
            "url": stream_url,
        })
        urls_map[fid] = stream_url

    # 2. Scan for <source src="..." label="720p"> tags
    if not formats:
        for src_m in re.finditer(r"<source\b([^>]+)>", page_html, re.IGNORECASE):
            attrs = src_m.group(1)
            u_m = re.search(r'src=["\']([^"\']+)["\']', attrs, re.IGNORECASE)
            if not u_m:
                continue
            raw_u = urljoin(url, html.unescape(u_m.group(1).replace("\\/", "/")))
            if is_ad_or_junk_url(raw_u):
                continue
            lbl_m = re.search(r'(?:label|title|res|data-res|size)=["\']?(\d{3,4})p?["\']?', attrs, re.IGNORECASE)
            height = int(lbl_m.group(1)) if lbl_m else 0
            if not height:
                hm = re.search(r"(\d{3,4})p", raw_u, re.IGNORECASE)
                height = int(hm.group(1)) if hm else 720
            fid = f"src_{height}p"
            formats.append({
                "format_id": fid,
                "height": height,
                "vcodec": "h264",
                "acodec": "aac",
                "tbr": height * 3,
                "url": raw_u,
            })
            urls_map[fid] = raw_u

    # 3. Scan for raw .m3u8 / .mp4 / get_file URLs
    if not formats:
        raw_urls = re.findall(
            r'(?:https?:)?//[^\s"\'<>\\]+(?:\.(?:mp4|m3u8)|get_file/[^\s"\'<>\\]+)(?:\?[^\s"\'<>\\]*)?',
            page_html,
            re.IGNORECASE,
        )
        clean_urls = []
        for u in raw_urls:
            u_clean = html.unescape(u.replace("\\/", "/"))
            if u_clean.startswith("//"):
                u_clean = "https:" + u_clean
            if is_ad_or_junk_url(u_clean):
                continue
            if u_clean not in clean_urls:
                clean_urls.append(u_clean)

        for idx, media_url in enumerate(clean_urls[:8]):
            if ".m3u8" in media_url.lower():
                hls_variants = expand_hls_master_playlist(media_url, url, session_cookies, uid)
                if hls_variants:
                    for vf in hls_variants:
                        formats.append(vf)
                        urls_map[vf["format_id"]] = vf["url"]
                    continue

            hm = re.search(r"(?:_|/|-)(\d{3,4})p?(?:\.mp4|/|$|\?)", media_url, re.IGNORECASE)
            height = int(hm.group(1)) if hm else (720 if idx == 0 else 480)
            fid = f"stream_{height}p_{idx}"
            formats.append({
                "format_id": fid,
                "height": height,
                "vcodec": "h264",
                "acodec": "aac",
                "tbr": height * 3,
                "url": media_url,
            })
            urls_map[fid] = media_url

    if not formats:
        raise RuntimeError(
            "Cloudflare anti-bot blocked this page or no video streams were found. "
            "Upload fresh cookies with /cookies domain.com"
        )

    best_fmt = max(formats, key=lambda f: f.get("height") or 0)
    urls_map["best"] = best_fmt["url"]

    return {
        "id": uuid.uuid4().hex[:8],
        "title": title,
        "uploader": urlparse(url).hostname or "Web",
        "duration": None,
        "thumbnail": thumbnail,
        "formats": formats,
        "_tiktok_fallback": True,
        "_tiktok_urls": urls_map,
        "_referer": url,
        "_session_cookies": session_cookies,
    }


def tiktok_fallback_extract(url: str) -> dict:
    if HAS_CURL_CFFI:
        resp = cffi_requests.post(
            "https://www.tikwm.com/api/",
            data={"url": url, "hd": "1"},
            impersonate="chrome110",
            http_version=HTTP_V1_1,
            proxy=YTDLP_PROXY if YTDLP_PROXY else None,
            timeout=10,
        )
        payload = resp.json()
    else:
        import urllib.request
        import urllib.parse

        data = urllib.parse.urlencode({"url": url, "hd": "1"}).encode()
        req = urllib.request.Request("https://www.tikwm.com/api/", data=data)
        with urllib.request.urlopen(req, timeout=10) as resp:
            payload = json.loads(resp.read().decode())

    if payload.get("code") != 0 or not payload.get("data"):
        raise RuntimeError(payload.get("msg") or "TikTok fallback API returned an error.")

    d = payload["data"]

    def abs_tikwm_url(u: str | None) -> str | None:
        if not u:
            return None
        if u.startswith("//"):
            return "https:" + u
        if u.startswith("/"):
            return "https://www.tikwm.com" + u
        return u

    hd_play = abs_tikwm_url(d.get("hdplay") or d.get("play"))
    sd_play = abs_tikwm_url(d.get("play") or d.get("wmplay"))
    cover = abs_tikwm_url(d.get("cover") or d.get("origin_cover"))

    formats = []
    if hd_play:
        formats.append({
            "format_id": "hd",
            "height": 1080,
            "vcodec": "h264",
            "acodec": "aac",
            "tbr": 4000,
            "filesize": d.get("hd_size") or d.get("size") or 0,
            "url": hd_play,
        })
    if sd_play and sd_play != hd_play:
        formats.append({
            "format_id": "sd",
            "height": 540,
            "vcodec": "h264",
            "acodec": "aac",
            "tbr": 1500,
            "filesize": d.get("size") or 0,
            "url": sd_play,
        })

    return {
        "id": str(d.get("id") or uuid.uuid4().hex[:8]),
        "title": d.get("title") or "TikTok Video",
        "uploader": (d.get("author") or {}).get("nickname") or "TikTok User",
        "duration": d.get("duration"),
        "thumbnail": cover,
        "formats": formats,
        "_tiktok_fallback": True,
        "_tiktok_urls": {
            "hd": hd_play or sd_play,
            "sd": sd_play or hd_play,
            "best": hd_play or sd_play,
        },
    }


def resolve_fallback_stream_url(info: dict, selection: str) -> tuple[str, dict[str, str]]:
    if "|" in selection:
        fmt_id, height_str = selection.split("|", 1)
        try:
            target_h = int(height_str)
        except ValueError:
            target_h = 0
    else:
        fmt_id = selection
        target_h = 0

    urls_map = info.get("_tiktok_urls") or {}
    video_url = urls_map.get(fmt_id)
    fmt_headers: dict[str, str] = {}

    for fmt in info.get("formats") or []:
        if str(fmt.get("format_id", "")) == fmt_id and fmt.get("url"):
            video_url = fmt["url"]
            if isinstance(fmt.get("http_headers"), dict):
                fmt_headers.update(fmt["http_headers"])
            break

    if not video_url and target_h > 0:
        for fmt in info.get("formats") or []:
            if infer_format_height(fmt) == target_h and fmt.get("url"):
                video_url = fmt["url"]
                if isinstance(fmt.get("http_headers"), dict):
                    fmt_headers.update(fmt["http_headers"])
                break

    if not video_url:
        video_url = urls_map.get("best") or info.get("url")

    return video_url or "", fmt_headers


def direct_cffi_download(
    info: dict,
    mode: str,
    selection: str,
    job_id: str,
    uid: int,
    download_hook,
) -> Path:
    video_url, fmt_headers = resolve_fallback_stream_url(info, selection)
    if not video_url:
        raise RuntimeError("No direct stream URL found for selected quality.")

    raw_video_path = DOWNLOAD_DIR / f"{job_id}.mp4"
    referer = info.get("_referer") or info.get("webpage_url") or video_url
    parsed_ref = urlparse(referer)
    origin = f"{parsed_ref.scheme}://{parsed_ref.netloc}" if parsed_ref.scheme else ""

    headers = {
        "User-Agent": DEFAULT_UA,
        "Accept": "*/*",
        "Accept-Language": "en-US,en;q=0.9",
        "Referer": referer,
    }
    if origin:
        headers["Origin"] = origin
    headers.update(fmt_headers)

    session_cookies = dict(info.get("_session_cookies") or {})
    saved_cookie_path = cookie_file_for_url(uid, referer)
    if saved_cookie_path and saved_cookie_path.is_file():
        try:
            with open(saved_cookie_path, "r", encoding="utf-8", errors="replace") as cf:
                for line in cf:
                    if line.startswith("#") and not line.startswith("#HttpOnly_"):
                        continue
                    parts = line.rstrip("\r\n").split("\t")
                    if len(parts) == 7:
                        session_cookies.setdefault(parts[5], parts[6])
        except Exception:
            pass

    cookie_header_str = "; ".join(f"{k}={v}" for k, v in session_cookies.items())

    if ".m3u8" in video_url.lower():
        hdr_lines = [
            f"Referer: {referer}",
            f"User-Agent: {headers['User-Agent']}",
        ]
        if cookie_header_str:
            hdr_lines.append(f"Cookie: {cookie_header_str}")
        hdr_blob = "\r\n".join(hdr_lines) + "\r\n"

        run_tracked_subprocess(
            [
                "ffmpeg", "-y",
                "-threads", "1",
                "-headers", hdr_blob,
                "-i", video_url,
                "-c", "copy", "-bsf:a", "aac_adtstoasc",
                "-movflags", "+faststart",
                str(raw_video_path),
            ],
            uid,
            timeout=900,
        )
    else:
        downloaded_ok = False
        proxy_candidates = [YTDLP_PROXY, None] if YTDLP_PROXY else [None]

        if HAS_CURL_CFFI:
            for prx in proxy_candidates:
                if downloaded_ok:
                    break
                try:
                    resp = cffi_requests.get(
                        video_url,
                        impersonate="chrome110",
                        headers=headers,
                        cookies=session_cookies or None,
                        http_version=HTTP_V1_1,
                        proxy=prx,
                        stream=True,
                        allow_redirects=True,
                        timeout=30,
                    )
                    try:
                        resp.raise_for_status()
                        ctype = (resp.headers.get("content-type") or "").lower()
                        if "text/html" in ctype:
                            raise RuntimeError("CDN returned HTML instead of video stream.")

                        total = int(resp.headers.get("content-length") or 0)
                        done = 0
                        start = time.monotonic()

                        with open(raw_video_path, "wb") as f:
                            if hasattr(resp, "iter_content"):
                                try:
                                    iterator = resp.iter_content(chunk_size=65536)
                                except TypeError:
                                    iterator = resp.iter_content()

                                for chunk in iterator:
                                    with active_lock:
                                        job = active_jobs.get(uid)
                                        if job and job["cancelled"].is_set():
                                            raise JobCancelledError("Cancelled by user.")
                                    if not chunk:
                                        continue
                                    f.write(chunk)
                                    done += len(chunk)
                                    elapsed = max(0.001, time.monotonic() - start)
                                    download_hook({
                                        "status": "downloading",
                                        "downloaded_bytes": done,
                                        "total_bytes": total,
                                        "speed": done / elapsed,
                                        "eta": int((total - done) / (done / elapsed)) if total and done else None,
                                    })
                            else:
                                content = resp.content
                                f.write(content)
                                done = len(content)
                                download_hook({
                                    "status": "downloading",
                                    "downloaded_bytes": done,
                                    "total_bytes": done,
                                    "speed": done,
                                    "eta": 0,
                                })
                        if raw_video_path.is_file() and raw_video_path.stat().st_size > 20 * 1024:
                            downloaded_ok = True
                    finally:
                        if hasattr(resp, "close"):
                            try:
                                resp.close()
                            except Exception:
                                pass
                except JobCancelledError:
                    raise
                except Exception as cffi_exc:
                    log.debug("curl_cffi stream (proxy=%s) failed: %s", prx, cffi_exc)

        if not downloaded_ok:
            raise RuntimeError("HTTP 403 Forbidden or stream blocked by CDN.")

    if mode == "audio":
        mp3_path = DOWNLOAD_DIR / f"{job_id}.mp3"
        run_tracked_subprocess(
            [
                "ffmpeg", "-y", "-threads", "1", "-i", str(raw_video_path),
                "-vn", "-acodec", "libmp3lame", "-b:a", "192k",
                str(mp3_path),
            ],
            uid,
            timeout=300,
        )
        raw_video_path.unlink(missing_ok=True)
        download_hook({"status": "finished"})
        return mp3_path

    download_hook({"status": "finished"})
    return raw_video_path


# ==================== SMART ZERO-DELAY EXTRACTOR ROUTING ====================

def extract_info(url: str, uid: int) -> dict:
    url = normalize_url(url)

    # 1. Check Instant RAM Cache (0.01s response if fetched recently)
    cached = url_info_cache.get(url)
    if cached and (time.time() - cached[0] < CACHE_TTL_SECONDS):
        return dict(cached[1])

    # 2. TikTok Fast-Path: Go straight to TikWM API (< 1 second, no yt-dlp overhead)
    if is_tiktok_url(url):
        try:
            info = tiktok_fallback_extract(url)
            url_info_cache[url] = (time.time(), info)
            return info
        except Exception as tk_exc:
            log.debug("TikWM fast-path failed (%s), falling back to yt-dlp", tk_exc)

    # 3. Unknown/Generic KVS Sites: Go straight to Parallel HTTP/1.1 Racing Extractor first
    #    (Avoids waiting 10-20s for yt-dlp generic extractor to fail on Cloudflare/KVS v10!)
    if not is_known_ytdlp_site(url):
        try:
            info = generic_cffi_extract(url, uid)
            if info and info.get("formats"):
                url_info_cache[url] = (time.time(), info)
                return info
        except Exception as gen_exc:
            log.debug("Fast parallel generic extractor skipped (%s), trying yt-dlp", gen_exc)

    # 4. Known Sites (YouTube, FB, IG, X, etc.): Use fast yt-dlp extractor
    for use_prx in ([False, True] if YTDLP_PROXY else [False]):
        fast_options = make_ytdlp_options(
            uid,
            url,
            {"skip_download": True, "ignore_no_formats_error": True},
            fast_fetch=True,
            use_proxy=use_prx,
        )
        try:
            with yt_dlp.YoutubeDL(fast_options) as ydl:
                raw_info = ydl.extract_info(url, download=False)
                info = unwrap_main_entry(raw_info)
                if info and (info.get("formats") or info.get("url")):
                    info["_use_proxy"] = use_prx
                    quals = quality_options(info)
                    if len(quals) <= 1 and info.get("url") and ".m3u8" in str(info.get("url")).lower():
                        variants = expand_hls_master_playlist(info["url"], url, {}, uid)
                        if len(variants) > 1:
                            info["formats"] = variants
                    url_info_cache[url] = (time.time(), info)
                    return info
        except Exception as exc:
            err_text = str(exc)
            log.info("yt-dlp extract (proxy=%s) failed: %s", use_prx, err_text[:120])
            if "flashvars" in err_text.lower() or "403" in err_text or "[generic]" in err_text.lower():
                break

    # 5. Final fallback to Parallel Racing Extractor
    info = generic_cffi_extract(url, uid)
    url_info_cache[url] = (time.time(), info)
    return info


def run_ytdlp(options: dict, url: str):
    try:
        with yt_dlp.YoutubeDL(options) as ydl:
            ydl.download([url])
    except JobCancelledError:
        raise
    except Exception as exc:
        if "Cancelled by user" in str(exc):
            raise JobCancelledError("Cancelled by user.") from exc
        raise


# ==================== DISPLAY HELPERS ====================

def duration_text(seconds):
    if seconds is None:
        return "Unknown"

    seconds = int(seconds)
    hours, rem = divmod(seconds, 3600)
    minutes, seconds = divmod(rem, 60)

    return (
        f"{hours}:{minutes:02d}:{seconds:02d}"
        if hours else f"{minutes}:{seconds:02d}"
    )


def human_size(value):
    if value is None:
        return "Unknown"

    size = float(value)

    for unit in ("B", "KB", "MB", "GB", "TB"):
        if size < 1024 or unit == "TB":
            return f"{size:.1f} {unit}"
        size /= 1024

    return "Unknown"


def progress_bar(percent, width=14):
    filled = max(0, min(width, int(percent * width / 100)))
    return "█" * filled + "░" * (width - filled)


def safe_filename(name):
    name = re.sub(r'[\\/:*?"<>|\x00-\x1f]', "", name).strip(" .")
    name = re.sub(r"\s+", " ", name)[:140].strip()
    return name or "reclip-media"


async def edit_progress(message, text, force=False, reply_markup=None):
    key = (message.chat.id, message.id)
    now = time.monotonic()

    if not force and now - last_edit.get(key, 0) < PROGRESS_INTERVAL:
        return

    last_edit[key] = now

    try:
        await message.edit_text(
            text,
            disable_web_page_preview=True,
            reply_markup=reply_markup,
        )
    except Exception as exc:
        if "MESSAGE_NOT_MODIFIED" not in str(exc).upper():
            log.debug("Progress edit failed: %s", exc)


# ==================== KEYBOARDS ====================

def cancel_keyboard(uid: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("⛔ Cancel Download", callback_data=f"cancel:{uid}")]
    ])


def format_keyboard(uid):
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton("🎬 MP4 Video", callback_data=f"mode:video:{uid}"),
            InlineKeyboardButton("🎵 MP3 Audio", callback_data=f"mode:audio:{uid}"),
        ],
        [InlineKeyboardButton("🔄 New link", callback_data="new")],
    ])


def quality_keyboard(uid, qualities):
    rows = []
    row = []

    for selector_token, label in qualities:
        row.append(
            InlineKeyboardButton(label, callback_data=f"q:{uid}:{selector_token}")
        )

        if len(row) == 2:
            rows.append(row)
            row = []

    if row:
        rows.append(row)

    rows.append([
        InlineKeyboardButton("⭐ Best available", callback_data=f"q:{uid}:best")
    ])
    rows.append([
        InlineKeyboardButton("⬅️ Format", callback_data=f"back:{uid}")
    ])

    return InlineKeyboardMarkup(rows)


# ==================== COOKIE COMMANDS ====================

@app.on_message(filters.private & filters.command("cookies"))
async def cookies_command(client, message):
    uid = message.from_user.id
    args = message.text.split(maxsplit=1)

    if len(args) == 2:
        domain = normalize_domain(args[1])

        if not domain:
            await message.reply_text(
                "Send a valid domain, e.g. /cookies youtube.com"
            )
            return

        cookie_upload_targets[uid] = domain

        await message.reply_text(
            f"🍪 Upload target: <code>{html.escape(domain)}</code>\n"
            "Now upload your Netscape-format cookies.txt as a document."
        )
        return

    profiles = cookie_profiles(uid)

    if not profiles:
        await message.reply_text(
            "🍪 No cookie profiles saved.\n"
            "Use /cookies youtube.com, then upload cookies.txt."
        )
        return

    lines = ["🍪 <b>Your cookie profiles</b>"]

    for profile in profiles:
        status = (
            "invalid format"
            if profile.get("invalid")
            else f"{profile['count']} cookies · {profile['expired']} expired"
        )
        lines.append(
            f"• <code>{html.escape(profile['domain'])}</code> — {status}"
        )

    lines.append("\nUse /cookieinfo, /checkcookies URL, or /deletecookies domain.")
    await message.reply_text("\n".join(lines))


@app.on_message(filters.private & filters.command("cookieinfo"))
async def cookieinfo_command(client, message):
    profiles = cookie_profiles(message.from_user.id)

    if not profiles:
        await message.reply_text("No cookie profiles saved.")
        return

    lines = ["🍪 <b>Cookie profile details</b>"]

    for profile in profiles:
        lines.append(f"\n<b>{html.escape(profile['domain'])}</b>")

        if profile.get("invalid"):
            lines.append("Invalid cookie format")
            continue

        records = parse_cookie_file(profile["path"])
        domains = sorted({r["domain"] for r in records})
        lines.append(f"Records: {len(records)}")
        lines.append(
            "Expired: " + str(sum(
                1 for r in records
                if r["expiry"] and r["expiry"] <= int(time.time())
            ))
        )
        lines.append("Domains: " + html.escape(", ".join(domains[:15])))

    lines.append("\nCookie values are never displayed.")
    await message.reply_text("\n".join(lines))


@app.on_message(filters.private & filters.command("checkcookies"))
async def checkcookies_command(client, message):
    args = message.text.split(maxsplit=1)

    if len(args) != 2 or not valid_url(args[1]):
        await message.reply_text(
            "Usage: /checkcookies https://www.youtube.com/watch?v=VIDEO_ID"
        )
        return

    uid = message.from_user.id
    url = normalize_url(args[1])
    path = cookie_file_for_url(uid, url)

    if not path:
        await message.reply_text(
            "❌ No unexpired cookie records match this URL."
        )
        return

    status = await message.reply_text("⚡ Testing URL with saved cookies…")

    try:
        url_info_cache.pop(url, None)
        info = await asyncio.to_thread(extract_info, url, uid)
        quals = quality_options(info)

        await status.edit_text(
            "✅ <b>Extraction succeeded</b>\n"
            f"Title: {html.escape(str(info.get('title') or 'Unknown')[:180])}\n"
            f"Qualities: <code>{', '.join(lbl for _, lbl in quals) or 'None'}</code>\n"
            f"Cookie profile: <code>{html.escape(path.name)}</code>"
        )

    except Exception as exc:
        log.warning("Cookie extraction test failed: %s", exc)

        await status.edit_text(
            "⚠️ <b>Extraction failed</b>\n"
            + html.escape(strip_ansi(str(exc))[:700])
            + "\nThe site may reject this session or require verification."
        )


@app.on_message(filters.private & filters.command("deletecookies"))
async def deletecookies_command(client, message):
    args = message.text.split(maxsplit=1)

    if len(args) != 2:
        await message.reply_text("Usage: /deletecookies youtube.com")
        return

    domain = normalize_domain(args[1])

    if not domain:
        await message.reply_text("Invalid domain.")
        return

    path = cookie_profile_dir(message.from_user.id) / f"{domain}.txt"

    if not path.exists():
        await message.reply_text("No exact cookie profile found.")
        return

    path.unlink()
    cookie_upload_targets.pop(message.from_user.id, None)

    await message.reply_text(
        f"🗑 Deleted <code>{html.escape(domain)}</code> cookie profile."
    )


@app.on_message(filters.private & filters.document)
async def cookie_upload_handler(client, message):
    uid = message.from_user.id
    target = cookie_upload_targets.get(uid)
    document = message.document
    filename = (document.file_name or "").lower()

    if not target:
        await message.reply_text(
            "First send /cookies youtube.com, then upload cookies.txt."
        )
        return

    if not filename.endswith((".txt", ".cookies")):
        await message.reply_text("Upload a Netscape-format .txt cookie file.")
        return

    if document.file_size and document.file_size > 5 * 1024 * 1024:
        await message.reply_text("Cookie file maximum size is 5 MB.")
        return

    folder = cookie_profile_dir(uid)
    temp = folder / f".upload-{uuid.uuid4().hex}.tmp"

    try:
        await message.reply_text("🔎 Validating cookie file…")

        downloaded = await client.download_media(
            message,
            file_name=str(temp),
        )

        if not downloaded or not temp.exists():
            raise ValueError("Uploaded file was not saved.")

        records = parse_cookie_file(temp)
        profile_path = folder / f"{target}.txt"

        os.replace(temp, profile_path)

        try:
            profile_path.chmod(0o600)
        except OSError:
            pass

        matched = sum(
            1 for r in records
            if cookie_domain_matches(
                r["domain"],
                r["include_subdomains"],
                target,
            )
        )

        cookie_upload_targets.pop(uid, None)

        await message.reply_text(
            "✅ <b>Cookies saved</b>\n"
            f"Profile: <code>{html.escape(target)}</code>\n"
            f"Records: {len(records)}\n"
            f"Matching domain records: {matched}\n"
            "Now use /checkcookies URL to test it."
        )

    except Exception as exc:
        temp.unlink(missing_ok=True)

        await message.reply_text(
            "❌ Could not save cookies: "
            + html.escape(str(exc)[:500])
            + "\nExport Netscape-format cookies.txt and try again."
        )


# ==================== START / HELP / CANCEL ====================

@app.on_message(filters.private & filters.command(["start", "help"]))
async def start_handler(client, message):
    await message.reply_text(
        "👋 <b>Welcome to ReClip (Ultra-Light Edition)</b>\n\n"
        "Send a media URL to select MP4 quality or MP3 audio.\n\n"
        "• ⚡ Instant Parallel Link Fetching\n"
        "• 🎬 Smart Quality Selection + Exact Sizes\n"
        "• 🛠 Faststart Seekable MP4 + Auto Thumbnail\n"
        "• 🛑 Instant Force-Kill Cancel & Storage Cleanup\n"
        "• 🍪 Per-user cookie profiles (/cookies domain.com)\n"
        "• /cookieinfo · /checkcookies URL · /deletecookies\n"
        "• /cancel"
    )


@app.on_message(filters.private & filters.command("cancel"))
async def cancel_handler(client, message):
    uid = message.from_user.id
    sessions.pop(uid, None)
    was_running = cancel_user_job(uid)

    if was_running:
        await message.reply_text(
            "🛑 <b>Active download force-killed & VPS storage cleared!</b>"
        )
    else:
        await message.reply_text("🧹 Current link cleared.")


# ==================== LINK HANDLER ====================

@app.on_message(
    filters.private
    & filters.text
    & ~filters.command([
        "start", "help", "cancel", "cookies",
        "cookieinfo", "checkcookies", "deletecookies",
    ])
)
async def link_handler(client, message):
    uid = message.from_user.id
    url = normalize_url(message.text.strip())

    if not valid_url(url):
        await message.reply_text("Send a valid http:// or https:// URL.")
        return

    status = await message.reply_text("⚡ Fetching link details…")

    try:
        t0 = time.monotonic()
        info = await asyncio.to_thread(extract_info, url, uid)
        qualities = quality_options(info)
        elapsed = time.monotonic() - t0

        trim_memory()
        sessions[uid] = {
            "url": url,
            "info": info,
            "qualities": qualities,
        }

        title = html.escape(str(info.get("title") or "Untitled")[:180])
        uploader = html.escape(
            str(info.get("uploader") or info.get("channel") or "Unknown")[:100]
        )

        text = (
            f"🎞 <b>{title}</b>\n"
            f"👤 {uploader}\n"
            f"⏱ {duration_text(info.get('duration'))} · ⚡ {elapsed:.1f}s\n"
            f"🎚 {len(qualities)} video qualities found\n\n"
            "Choose output format:"
        )

        thumbnail = info.get("thumbnail")

        if thumbnail and thumbnail.startswith(("https://", "http://")):
            try:
                await client.send_photo(
                    message.chat.id,
                    thumbnail,
                    caption=text,
                    reply_markup=format_keyboard(uid),
                )
                await status.delete()
                return
            except Exception:
                log.debug("Thumbnail preview failed", exc_info=True)

        await status.edit_text(
            text,
            reply_markup=format_keyboard(uid),
            disable_web_page_preview=True,
        )

    except Exception as exc:
        log.warning("Metadata extraction failed: %s", exc)
        await status.edit_text(
            "❌ <b>Could not fetch this URL</b>\n"
            + html.escape(strip_ansi(str(exc))[:900])
        )


# ==================== DOWNLOAD / UPLOAD ====================

async def download_and_upload(
    client, chat_id, uid, status_message, mode, selection
):
    session = sessions.get(uid, {})
    url = normalize_url(session.get("url", ""))
    info = session.get("info", {})

    if not url:
        await edit_progress(status_message, "⚠️ Session expired.", True)
        with active_lock:
            active_users.discard(uid)
        return

    job_id = uuid.uuid4().hex[:12]
    cancel_event = threading.Event()

    with active_lock:
        active_jobs[uid] = {
            "job_id": job_id,
            "cancelled": cancel_event,
            "proc": None,
        }

    title = str(info.get("title") or "ReClip media")
    template = str(DOWNLOAD_DIR / f"{job_id}.%(ext)s")
    loop = asyncio.get_running_loop()
    last_hook = [0.0, -1.0]
    cancel_markup = cancel_keyboard(uid)

    def download_hook(data):
        if cancel_event.is_set():
            raise JobCancelledError("Cancelled by user.")

        state = data.get("status")

        if state == "finished":
            asyncio.run_coroutine_threadsafe(
                edit_progress(
                    status_message,
                    "✅ Download finished.\n🛠 Verifying & optimizing video…",
                    True,
                    reply_markup=cancel_markup,
                ),
                loop,
            )
            return

        if state != "downloading":
            return

        total = data.get("total_bytes") or data.get("total_bytes_estimate") or 0
        done = data.get("downloaded_bytes") or 0
        percent = done * 100 / total if total else 0
        now = time.monotonic()

        if (
            percent >= 100
            or (
                percent - last_hook[1] >= 2
                and now - last_hook[0] >= PROGRESS_INTERVAL
            )
        ):
            last_hook[:] = [now, percent]

            speed = (
                f"{human_size(data.get('speed'))}/s"
                if data.get("speed") else "calculating…"
            )
            eta = (
                duration_text(data.get("eta"))
                if data.get("eta") is not None else "—"
            )

            text = (
                "⬇️ <b>Downloading</b>\n"
                f"<code>{progress_bar(percent)}</code> {percent:.1f}%\n"
                f"{human_size(done)} / {human_size(total)}\n"
                f"⚡ {html.escape(speed)} · ETA {eta}"
            )

            asyncio.run_coroutine_threadsafe(
                edit_progress(status_message, text, reply_markup=cancel_markup),
                loop,
            )

    use_proxy = info.get("_use_proxy", False)
    options = make_ytdlp_options(
        uid,
        url,
        {
            "outtmpl": template,
            "progress_hooks": [download_hook],
            "continuedl": True,
            "overwrites": True,
        },
        fast_fetch=False,
        use_proxy=use_proxy,
    )

    if mode == "audio":
        options.update({
            "format": "bestaudio/best",
            "postprocessors": [{
                "key": "FFmpegExtractAudio",
                "preferredcodec": "mp3",
                "preferredquality": "192",
            }],
        })
    else:
        options.update({
            "format": build_video_format_selector(info, selection),
            "merge_output_format": "mp4",
            "postprocessor_args": {
                "merger": ["-threads", "1", "-movflags", "+faststart"],
            },
        })

    thumb_path: Path | None = None

    try:
        await edit_progress(
            status_message,
            "⬇️ <b>Starting download…</b>",
            True,
            reply_markup=cancel_markup,
        )

        if info.get("_tiktok_fallback"):
            await asyncio.to_thread(
                direct_cffi_download,
                info,
                mode,
                selection,
                job_id,
                uid,
                download_hook,
            )
        else:
            try:
                await asyncio.to_thread(run_ytdlp, options, url)
            except JobCancelledError:
                raise
            except Exception as ytdl_err:
                if cancel_event.is_set():
                    raise JobCancelledError("Cancelled by user.") from ytdl_err

                log.info("Primary yt-dlp download failed (%s), trying smart fallback", ytdl_err)
                cleanup_job_files(job_id)

                if is_tiktok_url(url):
                    fb_info = await asyncio.to_thread(tiktok_fallback_extract, url)
                    await asyncio.to_thread(
                        direct_cffi_download,
                        fb_info,
                        mode,
                        selection,
                        job_id,
                        uid,
                        download_hook,
                    )
                else:
                    try:
                        await asyncio.to_thread(
                            direct_cffi_download,
                            info,
                            mode,
                            selection,
                            job_id,
                            uid,
                            download_hook,
                        )
                    except JobCancelledError:
                        raise
                    except Exception:
                        cleanup_job_files(job_id)
                        fb_info = await asyncio.to_thread(generic_cffi_extract, url, uid)
                        await asyncio.to_thread(
                            direct_cffi_download,
                            fb_info,
                            mode,
                            selection,
                            job_id,
                            uid,
                            download_hook,
                        )

        if cancel_event.is_set():
            raise JobCancelledError("Cancelled by user.")

        candidates = [
            path for path in DOWNLOAD_DIR.glob(f"{job_id}.*")
            if path.is_file()
            and not path.name.endswith((".part", ".ytdl", "_thumb.jpg", "_seekable.mp4"))
        ]

        if not candidates:
            raise RuntimeError("Download finished but no valid output file was produced.")

        wanted_ext = ".mp3" if mode == "audio" else ".mp4"
        preferred = [
            path for path in candidates
            if path.suffix.lower() == wanted_ext
        ]
        path = max(preferred or candidates, key=lambda p: p.stat().st_size)

        video_meta = {"duration": int(info.get("duration") or 0), "width": 0, "height": 0}
        if mode == "video":
            await edit_progress(
                status_message,
                "🛠 <b>Verifying video stream, fixing seek index & capturing thumbnail…</b>",
                True,
                reply_markup=cancel_markup,
            )
            path = await asyncio.to_thread(ensure_playable_seekable_mp4, path, job_id, uid)
            probed = await asyncio.to_thread(probe_video_metadata, path)
            if probed["duration"] > 0:
                video_meta["duration"] = probed["duration"]
            video_meta["width"] = probed["width"]
            video_meta["height"] = probed["height"]

            thumb_path = await asyncio.to_thread(
                generate_video_thumbnail,
                path,
                job_id,
                video_meta["duration"],
                uid,
            )

        if cancel_event.is_set():
            raise JobCancelledError("Cancelled by user.")

        size = path.stat().st_size

        if size > MAX_FILE_SIZE_MB * 1024 * 1024:
            raise RuntimeError(
                f"File size {human_size(size)} exceeds the configured "
                f"{MAX_FILE_SIZE_MB} MB limit."
            )

        res_badge = f" · {video_meta['height']}p" if video_meta.get("height") else ""
        caption = (
            f"✅ <b>{html.escape(title[:180])}</b>\n"
            f"⏱ {duration_text(video_meta['duration'] or info.get('duration'))}"
            f"{res_badge} · 📦 {human_size(size)} · {path.suffix[1:].upper()}\n"
            "Downloaded with ReClip"
        )

        last_upload = [0.0, -1.0]

        async def upload_progress(current, total, *args):
            if cancel_event.is_set():
                client.stop_transmission()
                return

            percent = current * 100 / max(total, 1)
            now = time.monotonic()

            if (
                percent >= 100
                or (
                    percent - last_upload[1] >= 2
                    and now - last_upload[0] >= PROGRESS_INTERVAL
                )
            ):
                last_upload[:] = [now, percent]

                await edit_progress(
                    status_message,
                    "📤 <b>Uploading to Telegram</b>\n"
                    f"<code>{progress_bar(percent)}</code> {percent:.1f}%\n"
                    f"{human_size(current)} / {human_size(total)}",
                    force=percent >= 100,
                    reply_markup=None if percent >= 100 else cancel_markup,
                )

        await edit_progress(
            status_message,
            "📤 <b>Uploading…</b>",
            True,
            reply_markup=cancel_markup,
        )

        if mode == "audio" and path.suffix.lower() == ".mp3":
            audio_dur = int(info.get("duration") or 0)
            await client.send_audio(
                chat_id,
                audio=str(path),
                file_name=safe_filename(title) + ".mp3",
                title=title[:64],
                duration=audio_dur,
                caption=caption,
                progress=upload_progress,
            )

        elif path.suffix.lower() == ".mp4":
            await client.send_video(
                chat_id,
                video=str(path),
                file_name=safe_filename(title) + ".mp4",
                caption=caption,
                duration=video_meta["duration"],
                width=video_meta["width"],
                height=video_meta["height"],
                thumb=str(thumb_path) if thumb_path and thumb_path.is_file() else None,
                supports_streaming=True,
                progress=upload_progress,
            )

        else:
            await client.send_document(
                chat_id,
                document=str(path),
                file_name=safe_filename(title) + path.suffix,
                caption=caption,
                progress=upload_progress,
            )

        if cancel_event.is_set():
            raise JobCancelledError("Cancelled by user.")

        await edit_progress(
            status_message,
            "🎉 <b>Complete!</b>\nUploaded to Telegram.",
            True,
            reply_markup=None,
        )

    except (JobCancelledError, StopTransmission):
        log.info("Job forcefully cancelled by user %s (job_id=%s)", uid, job_id)
        cleanup_job_files(job_id)
        await edit_progress(
            status_message,
            "🛑 <b>Download Cancelled!</b>\nProcess killed & VPS storage cleared.",
            True,
            reply_markup=None,
        )

    except (DownloadError, RPCError, FloodWait, RuntimeError, OSError) as exc:
        if cancel_event.is_set() or "Cancelled by user" in str(exc):
            cleanup_job_files(job_id)
            await edit_progress(
                status_message,
                "🛑 <b>Download Cancelled!</b>\nProcess killed & VPS storage cleared.",
                True,
                reply_markup=None,
            )
        else:
            log.warning("Job failed for user %s: %s", uid, exc)
            await edit_progress(
                status_message,
                "❌ <b>Failed</b>\n" + html.escape(strip_ansi(str(exc))[:900]),
                True,
                reply_markup=None,
            )

    except Exception as exc:
        if cancel_event.is_set() or "Cancelled by user" in str(exc):
            cleanup_job_files(job_id)
            await edit_progress(
                status_message,
                "🛑 <b>Download Cancelled!</b>\nProcess killed & VPS storage cleared.",
                True,
                reply_markup=None,
            )
        else:
            log.exception("Unexpected download/upload failure")
            await edit_progress(
                status_message,
                "❌ Unexpected error:\n" + html.escape(strip_ansi(str(exc))[:700]),
                True,
                reply_markup=None,
            )

    finally:
        cleanup_job_files(job_id)
        with active_lock:
            active_jobs.pop(uid, None)
            active_users.discard(uid)
        trim_memory()


# ==================== CALLBACK HANDLER ====================

@app.on_callback_query()
async def callback_handler(client, query):
    uid = query.from_user.id
    data = query.data or ""

    if data == "new":
        await query.answer("Send another link.")
        await client.send_message(query.message.chat.id, "🔗 Send the next URL.")
        return

    parts = data.split(":", 2)

    if parts[0] == "cancel":
        try:
            owner = int(parts[1])
        except (ValueError, IndexError):
            owner = -1

        if owner != uid:
            await query.answer("This job belongs to another user.", show_alert=True)
            return

        killed = cancel_user_job(uid)
        if killed:
            await query.answer("🛑 Force-killing download & clearing storage…", show_alert=False)
            await edit_progress(
                query.message,
                "🛑 <b>Download Cancelled!</b>\nProcess killed & VPS storage cleared.",
                True,
                reply_markup=None,
            )
        else:
            await query.answer("No active download found.", show_alert=False)
        return

    if parts[0] in ("mode", "back", "q"):
        owner_index = 2 if parts[0] == "mode" else 1

        try:
            owner = int(parts[owner_index])
        except (ValueError, IndexError):
            owner = -1

        if owner != uid:
            await query.answer("This menu belongs to another user.", show_alert=True)
            return

    session = sessions.get(uid)

    if not session:
        await query.answer("Session expired. Send URL again.", show_alert=True)
        return

    is_photo = bool(getattr(query.message, "photo", None))

    async def edit_menu(text, markup):
        if is_photo:
            await query.message.edit_caption(text, reply_markup=markup)
        else:
            await query.message.edit_text(
                text,
                reply_markup=markup,
                disable_web_page_preview=True,
            )

    if parts[0] == "mode" and len(parts) == 3:
        mode = parts[1]

        if mode not in ("video", "audio"):
            await query.answer("Unknown format.")
            return

        session["mode"] = mode
        await query.answer("Selected.")

        if mode == "audio":
            markup = InlineKeyboardMarkup([
                [InlineKeyboardButton(
                    "⬇️ Download MP3",
                    callback_data=f"q:{uid}:best",
                )],
                [InlineKeyboardButton(
                    "⬅️ Format",
                    callback_data=f"back:{uid}",
                )],
            ])

            await edit_menu("🎵 <b>MP3 audio selected</b>", markup)
        else:
            await edit_menu(
                "🎬 <b>Choose video quality</b>",
                quality_keyboard(uid, session.get("qualities", [])),
            )

        return

    if parts[0] == "back":
        await query.answer()
        await edit_menu("Choose output format:", format_keyboard(uid))
        return

    if parts[0] == "q" and len(parts) == 3:
        mode = session.get("mode")

        if mode not in ("video", "audio"):
            await query.answer("Choose MP4 or MP3 first.", show_alert=True)
            return

        selection = parts[2] if mode == "video" else "best"
        allowed = {tok for tok, _ in session.get("qualities", [])}

        if selection != "best" and selection not in allowed:
            await query.answer("Invalid quality choice.", show_alert=True)
            return

        with active_lock:
            if uid in active_users:
                await query.answer("A download is already running.", show_alert=True)
                return

            if len(active_users) >= MAX_CONCURRENT:
                await query.answer("Bot is busy. Try again shortly.", show_alert=True)
                return

            active_users.add(uid)

        await query.answer("Starting download…")
        status = await client.send_message(
            query.message.chat.id,
            "⏳ Starting download…",
            reply_markup=cancel_keyboard(uid),
        )

        asyncio.create_task(
            download_and_upload(
                client,
                query.message.chat.id,
                uid,
                status,
                mode,
                selection,
            )
        )
        return

    await query.answer("Unknown action.")


# ==================== START BOT ====================

if __name__ == "__main__":
    log.info("Starting ReClip Telegram bot (Ultra-Light 1GB RAM Edition)")
    app.run()
