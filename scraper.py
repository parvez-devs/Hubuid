from __future__ import annotations

import ipaddress
from html import unescape
import os
import re
import socket
import threading
import time
from functools import lru_cache
from urllib.parse import unquote, urlparse, urlunparse

import requests
from bs4 import BeautifulSoup
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

ALLOWED_HOSTS = {
    "facebook.com",
    "www.facebook.com",
    "m.facebook.com",
    "mbasic.facebook.com",
    "web.facebook.com",
}
FAST_REQUEST_TIMEOUT = (
    float(os.environ.get("XEROXUID_FAST_CONNECT_TIMEOUT", "2.2")),
    float(os.environ.get("XEROXUID_FAST_READ_TIMEOUT", "3.8")),
)
REQUEST_TIMEOUT = (
    float(os.environ.get("XEROXUID_CONNECT_TIMEOUT", "2.8")),
    float(os.environ.get("XEROXUID_READ_TIMEOUT", "6.2")),
)
WARMUP_TIMEOUT = (
    float(os.environ.get("XEROXUID_WARMUP_CONNECT_TIMEOUT", "1.2")),
    float(os.environ.get("XEROXUID_WARMUP_READ_TIMEOUT", "1.8")),
)
FETCH_DEADLINE_SECONDS = max(10.0, min(45.0, float(os.environ.get("XEROXUID_FETCH_DEADLINE", "14"))))
RETRY_TOTAL = max(0, min(1, int(os.environ.get("XEROXUID_HTTP_RETRIES", "0"))))
CACHE_TTL_SECONDS = 300
MAX_RESPONSE_BYTES = 2 * 1024 * 1024
UID_PATTERN = re.compile(r"^\d{1,20}$")
IMAGE_HOST_SUFFIXES = ("fbcdn.net", "fbsbx.com", "facebook.com")
MAX_IMAGE_BYTES = 6 * 1024 * 1024
BLOCKED_PATH_PREFIXES = (
    "/login",
    "/checkpoint",
    "/recover",
    "/reg",
)
GENERIC_TITLE_MARKERS = (
    "log into facebook",
    "log in to facebook",
    "log in or sign up",
    "facebook – log in",
    "facebook - log in",
)
GENERIC_DESCRIPTION_MARKERS = (
    "create an account or log into facebook",
    "connect with friends, family and other people you know",
)
TEMP_BLOCK_MARKERS = (
    "you’re temporarily blocked",
    "you're temporarily blocked",
    "you have been temporarily blocked",
    "you've been temporarily blocked",
    "misusing this feature by going too fast",
)


class ScraperError(Exception):
    def __init__(self, message: str, status_code: int = 400, code: str = "scraper_error"):
        super().__init__(message)
        self.message = message
        self.status_code = status_code
        self.code = code


class FacebookScraper:
    """Fetch publicly visible Facebook profile metadata only.

    No Facebook password, login cookie, private API, or generated fallback data
    is used. A short anonymous warm-up request is made so Facebook can set its
    normal guest-session cookies before profile URLs are requested.
    """

    def __init__(self) -> None:
        # Each Flask/Passenger worker thread receives its own requests.Session.
        # requests.Session is not guaranteed to be thread-safe; isolating it
        # prevents cookie/connection races while the browser runs two fetches.
        self._thread_local = threading.local()
        self._cache: dict[str, tuple[float, str]] = {}
        self._cache_lock = threading.Lock()
        self._preferred_route_index = 0
        self._route_lock = threading.Lock()

    @staticmethod
    def _build_session() -> requests.Session:
        session = requests.Session()
        # Never inherit random HTTP_PROXY/HTTPS_PROXY values from shared hosting.
        # Public proxy rotation is intentionally unsupported because it can leak
        # profile requests and makes failures nondeterministic.
        session.trust_env = False
        retry = Retry(
            total=RETRY_TOTAL,
            connect=RETRY_TOTAL,
            read=RETRY_TOTAL,
            backoff_factor=0.3,
            status_forcelist=(429, 500, 502, 503, 504),
            allowed_methods=frozenset(["GET"]),
            raise_on_status=False,
        )
        adapter = HTTPAdapter(max_retries=retry, pool_connections=4, pool_maxsize=4)
        session.mount("https://", adapter)
        session.mount("http://", adapter)
        session.headers.update(
            {
                "User-Agent": (
                    "Mozilla/5.0 (Linux; Android 15; Mobile) "
                    "AppleWebKit/537.36 (KHTML, like Gecko) "
                    "Chrome/131.0.0.0 Mobile Safari/537.36"
                ),
                "Accept": (
                    "text/html,application/xhtml+xml,application/xml;q=0.9,"
                    "image/avif,image/webp,*/*;q=0.8"
                ),
                "Accept-Language": "en-US,en;q=0.9",
                "Cache-Control": "no-cache",
                "Pragma": "no-cache",
                "Upgrade-Insecure-Requests": "1",
                "Sec-Fetch-Dest": "document",
                "Sec-Fetch-Mode": "navigate",
                "Sec-Fetch-Site": "none",
                "Sec-Fetch-User": "?1",
            }
        )
        # Locale is not an authentication cookie. It only asks Facebook to
        # return English labels, which makes follower parsing deterministic.
        session.cookies.set("locale", "en_US", domain=".facebook.com", path="/")
        return session

    @property
    def session(self) -> requests.Session:
        session = getattr(self._thread_local, "session", None)
        if session is None:
            session = self._build_session()
            self._thread_local.session = session
            self._thread_local.warmed_hosts = set()
        return session

    def _warmed_hosts(self) -> set[str]:
        # Accessing session initializes both thread-local values.
        _ = self.session
        return self._thread_local.warmed_hosts

    def _reset_worker_session(self) -> None:
        """Discard one anonymous worker session after repeated login walls.

        This does not use a Facebook account, cookie import or proxy. It simply
        clears stale guest cookies/keep-alive state so the next UID gets a fresh
        direct session instead of allowing one bad guest session to poison the
        rest of a large queue.
        """
        session = getattr(self._thread_local, "session", None)
        if session is not None:
            try:
                session.close()
            except requests.RequestException:
                pass
        self._thread_local.session = None
        self._thread_local.warmed_hosts = set()
        self._thread_local.login_wall_streak = 0

    def _record_worker_outcome(self, code: str | None = None) -> None:
        if not code:
            self._thread_local.login_wall_streak = 0
            return
        reset_codes = {"rate_limited", "temporarily_blocked"}
        wall_codes = {
            "access_denied", "profile_data_unavailable",
            "facebook_http_400", "facebook_http_400_all_routes",
        }
        if code in reset_codes:
            self._reset_worker_session()
            return
        if code not in wall_codes:
            return
        streak = int(getattr(self._thread_local, "login_wall_streak", 0)) + 1
        self._thread_local.login_wall_streak = streak
        if streak >= 5:
            self._reset_worker_session()

    @staticmethod
    @lru_cache(maxsize=16)
    def _is_public_ip(hostname: str) -> bool:
        try:
            addresses = socket.getaddrinfo(hostname, 443, type=socket.SOCK_STREAM)
        except socket.gaierror:
            return False

        if not addresses:
            return False

        for address in addresses:
            ip = ipaddress.ip_address(address[4][0])
            if (
                ip.is_private
                or ip.is_loopback
                or ip.is_link_local
                or ip.is_multicast
                or ip.is_unspecified
            ):
                return False
        return True

    @classmethod
    def normalize_url(cls, raw_url: str) -> str:
        if not isinstance(raw_url, str):
            raise ScraperError("The 'url' field must be a string.", 400, "invalid_url")

        raw_url = raw_url.strip()
        if not raw_url:
            raise ScraperError("Facebook URL is required.", 400, "missing_url")
        if not re.match(r"^https?://", raw_url, re.IGNORECASE):
            raw_url = "https://" + raw_url

        parsed = urlparse(raw_url)
        hostname = (parsed.hostname or "").lower().rstrip(".")
        if parsed.scheme.lower() != "https":
            raise ScraperError("Only HTTPS Facebook URLs are allowed.", 400, "invalid_scheme")
        if hostname not in ALLOWED_HOSTS:
            raise ScraperError("Only supported facebook.com URLs are allowed.", 400, "invalid_host")
        if parsed.username or parsed.password:
            raise ScraperError("Credentials in URL are not allowed.", 400, "invalid_url")
        if parsed.port not in (None, 443):
            raise ScraperError("Custom ports are not allowed.", 400, "invalid_port")
        if not cls._is_public_ip(hostname):
            raise ScraperError("Facebook host could not be safely resolved.", 502, "dns_resolution_failed")

        clean_path = re.sub(r"/+", "/", parsed.path or "/")
        return urlunparse(("https", hostname, clean_path, "", parsed.query, ""))

    def _get_cached(self, url: str) -> str | None:
        with self._cache_lock:
            item = self._cache.get(url)
            if not item:
                return None
            expires_at, value = item
            if time.time() >= expires_at:
                self._cache.pop(url, None)
                return None
            return value

    def _set_cached(self, url: str, value: str) -> None:
        with self._cache_lock:
            if len(self._cache) >= 256:
                self._cache.pop(next(iter(self._cache)), None)
            self._cache[url] = (time.time() + CACHE_TTL_SECONDS, value)

    def _warm_up(self, hostname: str) -> None:
        """Best-effort guest-session bootstrap.

        Facebook may reject a direct profile.php request from a completely new
        HTTP session with status 400. Visiting the host root first lets it set
        normal anonymous cookies. Failure here is intentionally ignored; the
        real profile request still provides the authoritative error.
        """
        # cPanel/shared-hosting routes can behave differently across Facebook
        # subdomains. Warm each candidate host separately, matching the stable
        # legacy fetch engine instead of assuming cookies are interchangeable.
        warmed_hosts = self._warmed_hosts()
        if hostname in warmed_hosts:
            return
        warmed_hosts.add(hostname)

        try:
            response = self.session.get(
                f"https://{hostname}/",
                headers={"Referer": f"https://{hostname}/"},
                timeout=WARMUP_TIMEOUT,
                allow_redirects=True,
                stream=True,
            )
            # Read only a tiny amount; cookies are available as soon as headers
            # arrive and we do not need the whole home page.
            next(response.iter_content(chunk_size=1024), b"")
            response.close()
        except requests.RequestException:
            return

    @staticmethod
    def _candidate_urls(uid: str) -> tuple[str, ...]:
        if not isinstance(uid, str) or not UID_PATTERN.fullmatch(uid.strip()):
            raise ScraperError("UID must contain only 1 to 20 digits.", 400, "invalid_uid")
        uid = uid.strip()
        # Direct numeric paths are tried before profile.php because Facebook
        # sometimes returns HTTP 400 for profile.php on anonymous mobile HTTP
        # sessions while the direct route still resolves normally.
        return (
            f"https://m.facebook.com/{uid}",
            f"https://www.facebook.com/{uid}",
            f"https://mbasic.facebook.com/{uid}",
            f"https://m.facebook.com/profile.php?id={uid}",
            f"https://www.facebook.com/profile.php?id={uid}",
        )

    def get_html(self, url: str) -> tuple[str, bool]:
        cached = self._get_cached(url)
        if cached is not None:
            return cached, True

        hostname = (urlparse(url).hostname or "").lower().rstrip(".")
        self._warm_up(hostname)

        try:
            response = self.session.get(
                url,
                headers={"Referer": f"https://{hostname}/"},
                timeout=getattr(self._thread_local, "request_timeout", REQUEST_TIMEOUT),
                allow_redirects=True,
                stream=True,
            )
        except requests.Timeout as exc:
            raise ScraperError("Facebook request timed out. The hosting network may block outbound HTTPS or have broken IPv6 routing.", 504, "upstream_timeout") from exc
        except requests.exceptions.SSLError as exc:
            raise ScraperError("The hosting server could not verify Facebook's HTTPS certificate. Reinstall requests/certifi in the cPanel virtual environment.", 502, "ssl_verification_failed") from exc
        except requests.exceptions.ProxyError as exc:
            raise ScraperError("The hosting environment proxy rejected the Facebook request.", 502, "proxy_error") from exc
        except requests.ConnectionError as exc:
            raise ScraperError("The cPanel server could not open an outbound connection to Facebook. Ask the host to allow outbound TCP 443.", 502, "outbound_connection_failed") from exc
        except requests.RequestException as exc:
            raise ScraperError("Could not connect to Facebook from this hosting server.", 502, "upstream_error") from exc

        final_url = urlparse(response.url)
        final_host = (final_url.hostname or "").lower().rstrip(".")
        final_path = (final_url.path or "/").lower()
        if final_host not in ALLOWED_HOSTS:
            response.close()
            raise ScraperError("Facebook redirected to an unsupported host.", 502, "unsafe_redirect")
        if final_path.startswith(BLOCKED_PATH_PREFIXES):
            response.close()
            raise ScraperError(
                "Facebook requires login or verification for this profile.",
                403,
                "access_denied",
            )

        status = response.status_code
        if status == 400:
            response.close()
            raise ScraperError(
                "Facebook rejected this public URL with HTTP 400.",
                502,
                "facebook_http_400",
            )
        if status == 404:
            response.close()
            raise ScraperError("Facebook profile was not found.", 404, "profile_not_found")
        if status in (401, 403):
            response.close()
            raise ScraperError(
                "Facebook blocked the request or the profile is not publicly accessible.",
                403,
                "access_denied",
            )
        if status == 429:
            response.close()
            raise ScraperError("Facebook rate-limited this device.", 429, "rate_limited")
        if not 200 <= status < 300:
            response.close()
            raise ScraperError(f"Facebook returned HTTP {status}.", 502, "upstream_bad_status")

        content_type = response.headers.get("Content-Type", "").lower()
        if "text/html" not in content_type and "application/xhtml+xml" not in content_type:
            response.close()
            raise ScraperError("Facebook returned a non-HTML response.", 502, "invalid_response")

        chunks: list[bytes] = []
        total = 0
        for chunk in response.iter_content(chunk_size=16384):
            if not chunk:
                continue
            total += len(chunk)
            if total > MAX_RESPONSE_BYTES:
                response.close()
                raise ScraperError("Facebook response was too large.", 502, "response_too_large")
            chunks.append(chunk)

        # Keep the complete bounded response. Some shared-hosting routes place
        # usable profile metadata after the initial document head.
        html = b"".join(chunks).decode(response.encoding or "utf-8", errors="replace")
        response.close()
        if not html.strip():
            raise ScraperError("Facebook returned an empty page.", 502, "empty_response")

        html_lower = html[:250000].lower()
        if any(marker in html_lower for marker in TEMP_BLOCK_MARKERS):
            raise ScraperError(
                "Facebook temporarily blocked anonymous requests from this network. Wait before retrying.",
                429,
                "temporarily_blocked",
            )

        self._set_cached(url, html)
        return html, False

    @staticmethod
    def _meta_content(
        soup: BeautifulSoup,
        *,
        property_name: str | None = None,
        name: str | None = None,
    ) -> str | None:
        tag = None
        if property_name:
            tag = soup.find("meta", attrs={"property": property_name})
        elif name:
            tag = soup.find("meta", attrs={"name": name})
        if not tag:
            return None
        value = tag.get("content")
        return value.strip() if isinstance(value, str) and value.strip() else None

    @staticmethod
    def _normalize_profile_image_url(value: str | None) -> str | None:
        if not isinstance(value, str) or not value.strip():
            return None
        cleaned = unescape(value).strip().strip('"\'')
        cleaned = cleaned.replace("\\/", "/").replace("\\u0026", "&")
        if not cleaned.lower().startswith(("http://", "https://", "//")):
            for _ in range(2):
                decoded = unquote(cleaned)
                if decoded == cleaned:
                    break
                cleaned = decoded
        if cleaned.startswith("//"):
            cleaned = f"https:{cleaned}"
        parsed = urlparse(cleaned)
        if parsed.scheme not in {"http", "https"} or not parsed.hostname:
            return None
        hostname = parsed.hostname.lower().rstrip(".")
        if not any(hostname == suffix or hostname.endswith(f".{suffix}") for suffix in IMAGE_HOST_SUFFIXES):
            return None
        if hostname.startswith("static.") or "/rsrc.php/" in parsed.path.lower():
            return None
        if parsed.scheme == "http":
            cleaned = urlunparse(parsed._replace(scheme="https"))
        return cleaned

    @classmethod
    def _extract_profile_image(cls, soup: BeautifulSoup, html: str) -> str | None:
        direct_candidates = [
            cls._meta_content(soup, property_name="og:image"),
            cls._meta_content(soup, name="twitter:image"),
        ]
        image_link = soup.find("link", attrs={"rel": "image_src"})
        if image_link:
            direct_candidates.append(image_link.get("href"))
        for value in direct_candidates:
            normalized = cls._normalize_profile_image_url(value)
            if normalized:
                return normalized

        scored: list[tuple[int, str]] = []
        for tag in soup.find_all("img", limit=160):
            raw = tag.get("src") or tag.get("data-src") or tag.get("data-img-src")
            normalized = cls._normalize_profile_image_url(raw)
            if not normalized:
                continue
            parsed = urlparse(normalized)
            combined = f"{normalized} {tag.get('alt', '')} {tag.get('class', '')}".lower()
            score = 0
            if "scontent" in parsed.hostname.lower():
                score += 6
            if any(token in combined for token in ("profile picture", "profile photo", "avatar")):
                score += 6
            if any(token in parsed.path.lower() for token in ("/v/t1", "_n.jpg", "_n.png", "_n.webp")):
                score += 4
            if re.search(r"\.(?:jpe?g|png|webp|avif)(?:$|[?&])", normalized, re.IGNORECASE):
                score += 2
            try:
                width = int(str(tag.get("width") or "0").split(".")[0])
                height = int(str(tag.get("height") or "0").split(".")[0])
                if width >= 40 and height >= 40:
                    score += 2
            except ValueError:
                pass
            if any(token in combined for token in ("emoji", "icon", "logo", "sprite", "pixel", "sticker")):
                score -= 10
            scored.append((score, normalized))

        if not scored:
            normalized_html = unescape(html).replace("\\/", "/").replace("\\u0026", "&")
            for match in re.finditer(r'https?://[^"\'<>\s]+', normalized_html):
                normalized = cls._normalize_profile_image_url(match.group(0))
                if not normalized:
                    continue
                lowered = normalized.lower()
                score = 3 if "scontent" in lowered else 0
                if any(token in lowered for token in ("/v/t1", "_n.jpg", "_n.png", "_n.webp")):
                    score += 4
                if any(token in lowered for token in ("emoji", "icon", "logo", "sprite", "pixel")):
                    score -= 10
                scored.append((score, normalized))

        if not scored:
            return None
        scored.sort(key=lambda item: item[0], reverse=True)
        return scored[0][1] if scored[0][0] > 0 else None

    def fetch_profile_image(self, image_url: str) -> tuple[bytes, str]:
        normalized = self._normalize_profile_image_url(image_url)
        if not normalized:
            raise ScraperError("Profile image URL is unavailable or unsafe.", 404, "profile_image_unavailable")
        hostname = (urlparse(normalized).hostname or "").lower().rstrip(".")
        if not self._is_public_ip(hostname):
            raise ScraperError("Profile image host is not publicly reachable.", 400, "unsafe_image_host")
        try:
            response = self.session.get(
                normalized,
                headers={
                    "Accept": "image/avif,image/webp,image/apng,image/*,*/*;q=0.8",
                    "Referer": "https://www.facebook.com/",
                    "Sec-Fetch-Dest": "image",
                    "Sec-Fetch-Mode": "no-cors",
                    "Sec-Fetch-Site": "cross-site",
                },
                timeout=(5, 15),
                allow_redirects=True,
                stream=True,
            )
        except requests.RequestException as exc:
            raise ScraperError("Could not download the Facebook profile image.", 502, "profile_image_fetch_failed") from exc
        final = self._normalize_profile_image_url(response.url)
        if not final or response.status_code != 200:
            response.close()
            raise ScraperError("Facebook did not return the profile image.", 502, "profile_image_bad_response")
        content_type = (response.headers.get("Content-Type") or "").split(";", 1)[0].strip().lower()
        if not content_type.startswith("image/"):
            response.close()
            raise ScraperError("Facebook returned a non-image response.", 502, "profile_image_bad_type")
        chunks: list[bytes] = []
        total = 0
        for chunk in response.iter_content(chunk_size=64 * 1024):
            if not chunk:
                continue
            total += len(chunk)
            if total > MAX_IMAGE_BYTES:
                response.close()
                raise ScraperError("Profile image is too large.", 502, "profile_image_too_large")
            chunks.append(chunk)
        response.close()
        payload = b"".join(chunks)
        if not payload:
            raise ScraperError("Facebook returned an empty profile image.", 502, "profile_image_empty")
        return payload, content_type

    @staticmethod
    def _extract_username(canonical_url: str | None, fallback_url: str) -> tuple[str | None, str | None]:
        for candidate in (canonical_url, fallback_url):
            if not candidate:
                continue
            parsed = urlparse(candidate)
            path = unquote(parsed.path).strip("/")
            if not path:
                continue
            if path == "profile.php":
                match = re.search(r"(?:^|&)id=(\d+)(?:&|$)", parsed.query)
                if match:
                    return None, match.group(1)
            first = path.split("/")[0]
            if first.isdigit():
                return None, first
            reserved = {
                "profile.php",
                "pages",
                "groups",
                "watch",
                "marketplace",
                "gaming",
                "events",
                "reel",
                "photo",
                "share",
                "login",
                "checkpoint",
                "recover",
                "reg",
            }
            if first.lower() not in reserved:
                return first, None
        return None, None

    @staticmethod
    def _extract_numeric_value(text: str | None, labels: tuple[str, ...]) -> int | None:
        if not text:
            return None

        label_pattern = "|".join(re.escape(label) for label in labels)
        match = re.search(
            rf"(\d{{1,3}}(?:[,\s]\d{{3}})+|\d+(?:[.,]\d+)?)\s*"
            rf"(K|M|B|thousand|million|billion)?\s*(?:{label_pattern})\b",
            text,
            re.IGNORECASE,
        )
        if not match:
            return None

        raw_number = match.group(1).replace(" ", "")
        try:
            if re.fullmatch(r"\d{1,3}(?:,\d{3})+", raw_number):
                number = float(raw_number.replace(",", ""))
            else:
                number = float(raw_number.replace(",", "."))
        except ValueError:
            return None

        suffix = (match.group(2) or "").lower()
        multiplier = {
            "": 1,
            "k": 1_000,
            "thousand": 1_000,
            "m": 1_000_000,
            "million": 1_000_000,
            "b": 1_000_000_000,
            "billion": 1_000_000_000,
        }[suffix]
        return int(number * multiplier)

    @staticmethod
    def _extract_profile_id(html: str) -> str | None:
        patterns = (
            r'"profile_id"\s*:\s*"(\d+)"',
            r'"userID"\s*:\s*"(\d+)"',
            r'"actorID"\s*:\s*"(\d+)"',
            r"profile_id=(\d+)",
            r'content="fb://profile/(\d+)"',
        )
        for pattern in patterns:
            match = re.search(pattern, html)
            if match:
                return match.group(1)
        return None


    @staticmethod
    def _extract_instagram(html: str) -> tuple[str | None, str | None]:
        """Return a public Instagram username/link embedded in Facebook HTML.

        Facebook often escapes external URLs inside JSON, so a small normalized
        text pass is more reliable than depending on visible anchor elements.
        No request is made to Instagram and no username is invented.
        """
        if not html:
            return None, None

        normalized = unescape(html)
        normalized = re.sub(r"\\+(?:/|u002[fF])", "/", normalized)
        # Decode percent-encoded outbound links at most twice.
        for _ in range(2):
            decoded = unquote(normalized)
            if decoded == normalized:
                break
            normalized = decoded

        reserved = {
            "about", "accounts", "api", "developer", "direct", "directory",
            "explore", "legal", "p", "privacy", "reel", "reels", "share",
            "stories", "terms", "web",
        }
        pattern = re.compile(
            r"(?:https?:)?//(?:www\.)?instagram\.com/([A-Za-z0-9._]{1,30})(?=[/?#&\"'<>\s]|$)",
            re.IGNORECASE,
        )
        for match in pattern.finditer(normalized):
            username = match.group(1).strip(".@")
            if not username or username.lower() in reserved:
                continue
            return username, f"https://www.instagram.com/{username}/"
        return None, None

    @staticmethod
    def _is_generic_page(title: str | None, description: str | None) -> bool:
        title_lower = (title or "").strip().lower()
        description_lower = (description or "").strip().lower()
        if title_lower == "facebook":
            return True
        if any(marker in title_lower for marker in GENERIC_TITLE_MARKERS):
            return True
        if any(marker in description_lower for marker in GENERIC_DESCRIPTION_MARKERS):
            return True
        return False

    def extract_profile(self, raw_url: str) -> dict:
        url = self.normalize_url(raw_url)
        html, cache_hit = self.get_html(url)
        # Parse the complete bounded document for compatibility with mobile
        # and mbasic pages whose useful fields are not always in the head.
        soup = BeautifulSoup(html, "html.parser")

        canonical_url = self._meta_content(soup, property_name="og:url")
        if not canonical_url:
            canonical = soup.find("link", attrs={"rel": "canonical"})
            canonical_url = canonical.get("href", "").strip() if canonical else None

        title = (
            self._meta_content(soup, property_name="og:title")
            or self._meta_content(soup, name="twitter:title")
        )
        if not title and soup.title:
            title = soup.title.get_text(" ", strip=True)

        description = (
            self._meta_content(soup, property_name="og:description")
            or self._meta_content(soup, name="description")
            or self._meta_content(soup, name="twitter:description")
        )

        if self._is_generic_page(title, description):
            raise ScraperError(
                "Facebook returned a login page instead of public profile data.",
                403,
                "access_denied",
            )

        name = None
        if title:
            name = re.sub(r"\s*[|—-]\s*Facebook\s*$", "", title, flags=re.IGNORECASE).strip()
            if not name or name.lower() == "facebook":
                name = None
        if not name:
            heading = soup.find("h1")
            if heading:
                candidate = heading.get_text(" ", strip=True)
                if candidate and candidate.lower() != "facebook":
                    name = candidate

        profile_pic = self._extract_profile_image(soup, html)

        username, id_from_url = self._extract_username(canonical_url, url)
        html_profile_id = self._extract_profile_id(html)
        profile_id = html_profile_id or id_from_url
        searchable_text = description or html[:150000]
        follower_count = self._extract_numeric_value(searchable_text, ("followers", "follower"))
        likes_count = self._extract_numeric_value(searchable_text, ("likes", "like"))
        instagram_username, instagram_url = self._extract_instagram(html)

        # A numeric ID copied from the requested URL is not proof that Facebook
        # returned genuine profile information. At least one page-derived field
        # must exist.
        real_evidence = (name, username, description, html_profile_id, profile_pic)
        if not any(real_evidence):
            raise ScraperError(
                "No public profile metadata was found. Facebook may require login or block scraping.",
                422,
                "profile_data_unavailable",
            )

        return {
            "name": name,
            "username": username,
            "profile_id": profile_id,
            "canonical_url": canonical_url or url,
            "profile_pic": profile_pic,
            "description": description,
            "follower_count": follower_count,
            "likes_count": likes_count,
            "instagram_username": instagram_username,
            "instagram_url": instagram_url,
            "cache_hit": cache_hit,
            "source_url": url,
        }

    def diagnose(self, uid: str | None = None) -> dict:
        """Return a small cPanel-safe connectivity report for administrators."""
        report: dict = {
            "dns": {"ok": False, "addresses": []},
            "outbound": {"ok": False},
            "transport": {"mode": "direct", "environment_proxy_ignored": True},
        }
        hostname = "www.facebook.com"
        try:
            addresses = socket.getaddrinfo(hostname, 443, type=socket.SOCK_STREAM)
            unique = []
            for address in addresses:
                value = address[4][0]
                if value not in unique:
                    unique.append(value)
            report["dns"] = {"ok": bool(unique), "addresses": unique[:8]}
        except OSError as exc:
            report["dns"] = {"ok": False, "addresses": [], "message": f"{type(exc).__name__}: {exc}"}

        try:
            started = time.monotonic()
            response = self.session.get(
                f"https://{hostname}/",
                timeout=(5, 9),
                allow_redirects=True,
                stream=True,
            )
            next(response.iter_content(chunk_size=1024), b"")
            final = urlparse(response.url)
            report["outbound"] = {
                "ok": True,
                "status": response.status_code,
                "final_host": (final.hostname or "").lower(),
                "content_type": response.headers.get("Content-Type", ""),
                "elapsed_ms": int((time.monotonic() - started) * 1000),
            }
            response.close()
        except requests.RequestException as exc:
            report["outbound"] = {
                "ok": False,
                "error_type": type(exc).__name__,
                "message": str(exc)[:300],
            }

        if uid:
            try:
                result = self.extract_uid(uid)
                report["profile"] = {
                    "ok": True,
                    "uid": uid,
                    "name": result.get("name"),
                    "username": result.get("username"),
                    "has_image": bool(result.get("profile_pic")),
                }
            except ScraperError as exc:
                report["profile"] = {"ok": False, "uid": uid, "code": exc.code, "message": exc.message}
        return report

    def extract_uid(self, uid: str) -> dict:
        """Try compatible public routes inside one bounded fetch deadline.

        The first remembered route uses a fast timeout. If it fails without a
        network-wide block, slower fallback routes are tried until useful data
        and a profile picture are found or the per-UID deadline is exhausted.
        """
        failures: list[ScraperError] = []
        best_result: dict | None = None
        merge_keys = (
            "name", "username", "profile_id", "canonical_url", "profile_pic",
            "description", "follower_count", "likes_count",
            "instagram_username", "instagram_url",
        )

        candidates = list(self._candidate_urls(uid))
        with self._route_lock:
            preferred = self._preferred_route_index if 0 <= self._preferred_route_index < len(candidates) else 0
        route_order = [preferred] + [index for index in range(len(candidates)) if index != preferred]
        best_route_index: int | None = None
        blocked_hosts: set[str] = set()
        started = time.monotonic()

        for position, route_index in enumerate(route_order):
            remaining = FETCH_DEADLINE_SECONDS - (time.monotonic() - started)
            if remaining < 3.0:
                failures.append(
                    ScraperError(
                        "Facebook route checks exceeded the safe per-UID time limit.",
                        504,
                        "fetch_deadline_exceeded",
                    )
                )
                break

            candidate = candidates[route_index]
            candidate_host = (urlparse(candidate).hostname or "").lower()
            if candidate_host in blocked_hosts:
                continue
            base_timeout = FAST_REQUEST_TIMEOUT if position == 0 else REQUEST_TIMEOUT
            connect_timeout = max(1.0, min(base_timeout[0], remaining * 0.28))
            read_timeout = max(1.8, min(base_timeout[1], remaining - connect_timeout - 0.5))
            self._thread_local.request_timeout = (connect_timeout, read_timeout)
            try:
                result = self.extract_profile(candidate)
                if best_result is None:
                    best_result = dict(result)
                    best_route_index = route_index
                else:
                    for key in merge_keys:
                        if not best_result.get(key) and result.get(key) is not None:
                            best_result[key] = result.get(key)
                    if result.get("profile_pic"):
                        best_result["profile_pic"] = result["profile_pic"]
                        best_result["source_url"] = result.get("source_url") or best_result.get("source_url")
                        best_route_index = route_index
                if best_result.get("profile_pic"):
                    with self._route_lock:
                        self._preferred_route_index = route_index
                    self._record_worker_outcome()
                    return best_result
            except ScraperError as exc:
                failures.append(exc)
                if exc.code in {"rate_limited", "temporarily_blocked"}:
                    # A mobile host can be blocked while www/mbasic still works.
                    # Retire only that host for this UID, refresh the anonymous
                    # guest session, and continue to the next compatible host.
                    blocked_hosts.add(candidate_host)
                    self._reset_worker_session()
                    continue
                # These errors describe the whole server/network rather than a
                # single Facebook route, so more route attempts would only add
                # delay or worsen a temporary block.
                if exc.code in {
                    "dns_resolution_failed", "ssl_verification_failed",
                    "proxy_error", "outbound_connection_failed",
                }:
                    if best_result is not None:
                        break
                    self._record_worker_outcome(exc.code)
                    raise
                # One fast timeout is allowed to fall through to the slower
                # compatible routes. The global deadline prevents a hung UID.
            finally:
                try:
                    del self._thread_local.request_timeout
                except AttributeError:
                    pass

        if best_result is not None:
            if best_route_index is not None:
                with self._route_lock:
                    self._preferred_route_index = best_route_index
            self._record_worker_outcome()
            return best_result

        if failures and all(error.code == "facebook_http_400" for error in failures):
            self._record_worker_outcome("facebook_http_400_all_routes")
            raise ScraperError(
                "Facebook returned HTTP 400 for every public UID URL format. "
                "This network/session is being rejected before profile data is served.",
                502,
                "facebook_http_400_all_routes",
            )

        priority = {
            "temporarily_blocked": 100,
            "rate_limited": 95,
            "access_denied": 90,
            "fetch_deadline_exceeded": 85,
            "profile_data_unavailable": 80,
            "upstream_timeout": 75,
            "profile_not_found": 70,
            "facebook_http_400": 60,
            "upstream_error": 55,
            "upstream_bad_status": 50,
        }
        if failures:
            best = max(failures, key=lambda error: priority.get(error.code, 0))
            self._record_worker_outcome(best.code)
            raise ScraperError(best.message, best.status_code, best.code)

        self._record_worker_outcome("no_candidate_url")
        raise ScraperError("No Facebook URL could be attempted.", 502, "no_candidate_url")
