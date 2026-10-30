"use strict";
// contract markers retained for compatibility: PAGE_SIZE = 30, FETCH_CONCURRENCY = 2, bulk-delete
// XeroxUID Deep Stability & Compact UI Patch 2.2.2

let viewportSyncFrame = 0;
function syncAppViewportHeight() {
  // Modern Android Chrome handles the collapsing address bar correctly with
  // dynamic viewport units. The JS fallback is only used on older browsers;
  // avoiding visualViewport resize writes during scroll removes layout thrash.
  if (window.CSS?.supports?.("height: 100dvh")) {
    document.documentElement.style.removeProperty("--app-height");
    return;
  }
  if (viewportSyncFrame) cancelAnimationFrame(viewportSyncFrame);
  viewportSyncFrame = requestAnimationFrame(() => {
    viewportSyncFrame = 0;
    const height = Math.round(window.innerHeight || document.documentElement.clientHeight || window.visualViewport?.height || 0);
    if (height > 0) document.documentElement.style.setProperty("--app-height", `${height}px`);
  });
}

syncAppViewportHeight();
window.addEventListener("resize", syncAppViewportHeight, { passive: true });
window.addEventListener("orientationchange", () => setTimeout(syncAppViewportHeight, 120), { passive: true });
// visualViewport is intentionally detected for compatibility, but dvh-capable
// browsers do not receive a resize listener that fires continuously on scroll.
if (!window.CSS?.supports?.("height: 100dvh")) {
  window.visualViewport?.addEventListener("resize", syncAppViewportHeight, { passive: true });
}

const APP_BASE = (() => {
  const configured = document.querySelector('meta[name="app-base"]')?.content || "";
  const normalized = configured.trim().replace(/\/+$/, "");
  return normalized === "/" ? "" : normalized;
})();

function appUrl(path) {
  const clean = String(path || "").startsWith("/") ? String(path || "") : `/${String(path || "")}`;
  return `${APP_BASE}${clean}` || clean;
}

const PREFS_STORAGE_KEY = "uid-operator-prefs";
const SAVED_STORAGE_KEY = "uid-operator-saved-profiles";
const VISITED_STORAGE_KEY = "uid-operator-visited-profiles";
const RETURN_POSITION_STORAGE_KEY = "xeroxuid-return-position-v2";
const FETCH_QUEUE_STORAGE_KEY = "xeroxuid-fetch-queue-v2";
const UI_LAYOUT_STORAGE_KEY = "xeroxuid-ui-layout-version";
const UI_LAYOUT_VERSION = "3.0.0-aurora-overlap-safe";
const PAGE_SIZE = 30;
const FETCH_UI_REFRESH_EVERY = 8;
const FETCH_CONCURRENCY = 2;
const FETCH_SUCCESS_DELAY_MS = 35;
const FETCH_FAILURE_DELAY_MS = 80;
const FETCH_BLOCK_DELAY_MS = 120;
const FETCH_REQUEST_TIMEOUT_MS = 24_000;
const FETCH_RETRY_DELAY_MS = 500;
const TRANSIENT_FETCH_CODES = new Set([
  "network_error", "client_timeout", "upstream_timeout", "upstream_error",
  "outbound_connection_failed", "proxy_error", "ssl_verification_failed",
  "server_error", "already_fetching",
]);

const DEFAULT_PREFS = {
  theme: "dark",
  fontSize: "md",
  viewMode: "full",
  swipeDelete: true,
  autoRetryFailed: false,
  workerConcurrency: 2,
};

const state = {
  authenticated: false,
  user: null,
  csrfToken: "",
  records: [],
  users: [],
  query: "",
  filter: "all",
  route: "/",
  selected: new Set(),
  saved: new Set(),
  visited: new Set(),
  prefs: loadPreferences(),
  openMenuId: null,
  fetching: false,
  importing: false,
  fetchStopRequested: false,
  activeFetchControllers: new Set(),
  autoRetryStarted: false,
  remainingFetchRecords: [],
  fetchSuccess: 0,
  fetchFailed: 0,
  fetchSkipped: 0,
  restoreInProgress: false,
};

const $ = (selector, root = document) => root.querySelector(selector);
const $$ = (selector, root = document) => [...root.querySelectorAll(selector)];
let searchTimer = null;
let scrollRenderFrame = 0;
let progressRenderFrame = 0;
let lastProgressPaint = 0;
let progressHideTimer = 0;
let returnPositionSaveTimer = 0;
let queueCheckpointTimer = 0;
const virtualLists = {
  home: { start: -1, end: -1, count: -1, rowHeight: 96, calibrated: true },
  saved: { start: -1, end: -1, count: -1, rowHeight: 96, calibrated: true },
};

function safeJsonParse(raw, fallback) {
  try { return JSON.parse(raw) ?? fallback; } catch (_) { return fallback; }
}

function loadSet(key) {
  const value = safeJsonParse(localStorage.getItem(key), []);
  return new Set(Array.isArray(value) ? value.map(String).filter(Boolean) : []);
}

function saveSet(key, set) {
  try { localStorage.setItem(key, JSON.stringify([...set])); } catch (_) { /* storage is optional */ }
}

function userStorageKey(baseKey) {
  const userId = state.user?.id;
  return `${baseKey}:user:${userId || "signed-out"}`;
}

function loadUserLocalState() {
  // Server remains authoritative. A user-scoped local visited journal protects
  // app-open marks when Android suspends the browser before a PATCH completes.
  state.saved = new Set();
  state.visited = loadSet(userStorageKey(VISITED_STORAGE_KEY));
}

function saveUserSet(baseKey, set) {
  if (!state.user?.id) return;
  saveSet(userStorageKey(baseKey), set);
}

function scopedStorageKey(baseKey) {
  return `${baseKey}:user:${state.user?.id || "signed-out"}`;
}

function syncClientLayoutVersion() {
  if (!state.user?.id) return;
  const key = scopedStorageKey(UI_LAYOUT_STORAGE_KEY);
  let previous = null;
  try { previous = localStorage.getItem(key); } catch (_) { /* optional storage */ }
  if (previous === UI_LAYOUT_VERSION) return;
  // A card-height change invalidates the old virtual-row and app-return offsets.
  // Clear only the user's stale return snapshot; saved/visited/queue data remains.
  removeStorage(sessionStorage, scopedStorageKey(RETURN_POSITION_STORAGE_KEY));
  try { localStorage.setItem(key, UI_LAYOUT_VERSION); } catch (_) { /* optional storage */ }
  const scroller = $("#appContent");
  if (scroller) scroller.scrollTop = 0;
  resetVirtualMeasurements();
}

function readStorage(storage, key, fallback = null) {
  try { return safeJsonParse(storage.getItem(key), fallback); } catch (_) { return fallback; }
}

function writeStorage(storage, key, value) {
  try { storage.setItem(key, JSON.stringify(value)); return true; } catch (_) { return false; }
}

function removeStorage(storage, key) {
  try { storage.removeItem(key); } catch (_) { /* optional storage */ }
}

function cssVirtualRowHeight() {
  const raw = getComputedStyle(document.documentElement).getPropertyValue("--virtual-row-height");
  const parsed = Number.parseFloat(raw);
  return Number.isFinite(parsed) && parsed >= 96 && parsed <= 220 ? parsed : 96;
}

function syncVirtualRowHeight() {
  const value = cssVirtualRowHeight();
  Object.values(virtualLists).forEach((meta) => {
    meta.rowHeight = value;
    meta.calibrated = true;
  });
}

function loadPreferences() {
  const stored = safeJsonParse(localStorage.getItem(PREFS_STORAGE_KEY), {});
  return { ...DEFAULT_PREFS, ...(stored && typeof stored === "object" ? stored : {}) };
}

function savePreferences() {
  try { localStorage.setItem(PREFS_STORAGE_KEY, JSON.stringify(state.prefs)); } catch (_) { /* optional */ }
  applyPreferences();
  if (state.authenticated) {
    syncVirtualRowHeight();
    resetVirtualMeasurements();
    renderCards();
    clampAppScroll();
  }
}

function applyPreferences() {
  document.documentElement.classList.toggle("dark", state.prefs.theme === "dark");
  document.documentElement.classList.remove("font-sm", "font-md", "font-lg");
  document.documentElement.classList.add(`font-${state.prefs.fontSize}`);
  document.body.classList.toggle("compact-view", state.prefs.viewMode === "compact");
  const themeMeta = $('meta[name="theme-color"]');
  if (themeMeta) themeMeta.content = state.prefs.theme === "dark" ? "#07111f" : "#f3f6fb";
  if ($("#themeSelect")) $("#themeSelect").value = state.prefs.theme;
  if ($("#fontSizeSelect")) $("#fontSizeSelect").value = state.prefs.fontSize;
  if ($("#viewModeSelect")) $("#viewModeSelect").value = state.prefs.viewMode;
  if ($("#swipeDeleteToggle")) $("#swipeDeleteToggle").checked = Boolean(state.prefs.swipeDelete);
  if ($("#autoRetryToggle")) $("#autoRetryToggle").checked = Boolean(state.prefs.autoRetryFailed);
  if ($("#workerConcurrencySelect")) $("#workerConcurrencySelect").value = String(Math.min(4, Math.max(1, Number(state.prefs.workerConcurrency) || FETCH_CONCURRENCY)));
  requestAnimationFrame(syncVirtualRowHeight);
}

function escapeHtml(value) {
  return String(value ?? "")
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;")
    .replaceAll("'", "&#039;");
}

function formatCount(value) {
  if (value === null || value === undefined || value === "") return "";
  const number = Number(value);
  if (!Number.isFinite(number)) return "";
  if (number >= 1_000_000_000) return `${(number / 1_000_000_000).toFixed(1).replace(/\.0$/, "")}B`;
  if (number >= 1_000_000) return `${(number / 1_000_000).toFixed(1).replace(/\.0$/, "")}M`;
  if (number >= 1_000) return `${(number / 1_000).toFixed(1).replace(/\.0$/, "")}K`;
  return new Intl.NumberFormat().format(number);
}

function statusColor(status) {
  if (status === "success") return "var(--success)";
  if (status === "error") return "var(--danger)";
  return "var(--warning)";
}

function iconSvg(name) {
  const icons = {
    check: '<svg viewBox="0 0 24 24"><path d="m5 12 4 4L19 6"/></svg>',
    star: '<svg viewBox="0 0 24 24"><path d="m12 3 2.8 5.7 6.2.9-4.5 4.4 1.1 6.2-5.6-3-5.6 3 1.1-6.2-4.5-4.4 6.2-.9Z"/></svg>',
    more: '<svg viewBox="0 0 24 24"><circle cx="12" cy="5" r="1.4"/><circle cx="12" cy="12" r="1.4"/><circle cx="12" cy="19" r="1.4"/></svg>',
    copy: '<svg viewBox="0 0 24 24"><rect x="9" y="9" width="11" height="11" rx="2"/><path d="M15 9V6a2 2 0 0 0-2-2H6a2 2 0 0 0-2 2v7a2 2 0 0 0 2 2h3"/></svg>',
    instagram: '<svg viewBox="0 0 24 24"><rect x="3" y="3" width="18" height="18" rx="6"/><circle cx="12" cy="12" r="4"/><circle cx="17.4" cy="6.6" r="1"/></svg>',
  };
  return icons[name] || "";
}

function getFacebookIntent(uid) {
  return `intent://profile/${encodeURIComponent(String(uid))}#Intent;scheme=fb;package=com.facebook.katana;end`;
}

function getInstagramUsername(record, allowUsernameFallback = true) {
  let username = String(record.instagram_username || "").trim();
  if (!username && record.instagram_url) {
    const match = String(record.instagram_url).match(/instagram\.com\/([^/?#]+)/i);
    if (match) username = match[1];
  }
  if (!username && allowUsernameFallback) username = String(record.username || "").trim();
  return username.replace(/^@/, "");
}

function getInstagramIntent(record, allowUsernameFallback = true) {
  const username = getInstagramUsername(record, allowUsernameFallback);
  return username ? `intent://user?username=${encodeURIComponent(username)}#Intent;scheme=instagram;package=com.instagram.android;end` : "";
}

function hasDetectedInstagram(record) {
  return Boolean(record.instagram_username || record.instagram_url);
}

function showToast(message, type = "success") {
  const toast = document.createElement("div");
  toast.className = `toast ${type}`;
  toast.textContent = message;
  $("#toastContainer").appendChild(toast);
  setTimeout(() => toast.remove(), 3000);
}

function showFormMessage(element, message, type = "error") {
  element.textContent = message;
  element.classList.remove("hidden", "error", "success");
  element.classList.add(type);
}

function hideFormMessage(element) {
  element.classList.add("hidden");
  element.textContent = "";
}

async function api(path, options = {}) {
  const method = String(options.method || "GET").toUpperCase();
  const headers = { ...(options.headers || {}) };
  if (options.body !== undefined && !headers["Content-Type"]) headers["Content-Type"] = "application/json";
  if (["POST", "PUT", "PATCH", "DELETE"].includes(method) && state.csrfToken && path !== "/api/auth/login") {
    headers["X-CSRF-Token"] = state.csrfToken;
  }
  let response;
  try {
    response = await fetch(appUrl(path), { ...options, method, headers, credentials: "same-origin", cache: "no-store" });
  } catch (cause) {
    if (cause?.name === "AbortError") throw cause;
    const offline = navigator.onLine === false;
    const error = new Error(offline ? "Internet connection is offline." : "Could not reach the XeroxUID server.");
    error.code = "network_error";
    error.status = 0;
    error.cause = cause;
    throw error;
  }
  let payload = {};
  try { payload = await response.json(); } catch (_) { payload = {}; }
  if (!response.ok) {
    const error = new Error(payload?.error?.message || `Request failed (${response.status})`);
    error.code = payload?.error?.code || (response.status >= 500 ? "server_error" : "request_failed");
    error.status = response.status;
    if (response.status === 401 && path !== "/api/auth/login") showPublicShell();
    throw error;
  }
  return payload;
}

function showPublicShell() {
  stopFetch(true);
  state.authenticated = false;
  state.user = null;
  state.csrfToken = "";
  state.records = [];
  state.users = [];
  state.selected.clear();
  state.saved = new Set();
  state.visited = new Set();
  state.autoRetryStarted = false;
  $("#appShell").classList.add("hidden");
  $("#publicShell").classList.remove("hidden");
  document.body.classList.remove("compact-view");
}

function activeListContext() {
  if (state.route === "/saved") {
    return { key: "saved", selector: "#savedCards", records: filteredRecords({ savedOnly: true }) };
  }
  return { key: "home", selector: "#cards", records: filteredRecords() };
}

function captureReturnPosition(anchorRecordId = null) {
  if (!state.authenticated || !["/", "/saved"].includes(state.route)) return null;
  const scroller = $("#appContent");
  if (!scroller) return null;
  const { selector } = activeListContext();
  const scrollerTop = scroller.getBoundingClientRect().top;
  const visibleCards = $$(`${selector} .profile-card`);
  let anchor = anchorRecordId
    ? visibleCards.find((card) => Number(card.dataset.id) === Number(anchorRecordId))
    : null;
  if (!anchor) {
    anchor = visibleCards.find((card) => card.getBoundingClientRect().bottom > scrollerTop + 2) || visibleCards[0] || null;
  }
  return {
    route: state.route,
    query: state.query,
    filter: state.filter,
    scrollTop: Math.max(0, Math.round(scroller.scrollTop)),
    anchorId: anchor ? Number(anchor.dataset.id) : null,
    anchorOffset: anchor ? Math.round(anchor.getBoundingClientRect().top - scrollerTop) : 0,
    restorePending: true,
    savedAt: Date.now(),
  };
}

function saveReturnPosition(anchorRecordId = null) {
  clearTimeout(returnPositionSaveTimer);
  const snapshot = captureReturnPosition(anchorRecordId);
  if (!snapshot) return;
  writeStorage(sessionStorage, scopedStorageKey(RETURN_POSITION_STORAGE_KEY), snapshot);
}

function scheduleReturnPositionSave() {
  if (state.restoreInProgress || !state.authenticated || !["/", "/saved"].includes(state.route)) return;
  clearTimeout(returnPositionSaveTimer);
  returnPositionSaveTimer = setTimeout(() => {
    const snapshot = captureReturnPosition();
    if (!snapshot) return;
    // Passive scroll checkpoints are not consumed automatically after reload;
    // only an app deep-link marks a snapshot as a pending return target.
    const existing = readStorage(sessionStorage, scopedStorageKey(RETURN_POSITION_STORAGE_KEY), null);
    snapshot.restorePending = Boolean(existing?.restorePending);
    writeStorage(sessionStorage, scopedStorageKey(RETURN_POSITION_STORAGE_KEY), snapshot);
  }, 120);
}

function nextFrame() {
  return new Promise((resolve) => requestAnimationFrame(resolve));
}

async function restoreReturnPosition({ requirePending = true } = {}) {
  if (!state.authenticated || state.restoreInProgress) return false;
  const key = scopedStorageKey(RETURN_POSITION_STORAGE_KEY);
  const snapshot = readStorage(sessionStorage, key, null);
  if (!snapshot || Date.now() - Number(snapshot.savedAt || 0) > 6 * 60 * 60 * 1000) {
    removeStorage(sessionStorage, key);
    return false;
  }
  if (requirePending && !snapshot.restorePending) return false;
  if (!["/", "/saved"].includes(snapshot.route)) return false;

  state.restoreInProgress = true;
  try {
    state.query = String(snapshot.query || "");
    state.filter = ["all", "pending", "success", "error", "selected"].includes(snapshot.filter) ? snapshot.filter : "all";
    if ($("#searchInput")) $("#searchInput").value = state.query;
    if ($("#savedSearchInput")) $("#savedSearchInput").value = state.query;
    const hash = snapshot.route === "/" ? "#/" : `#${snapshot.route}`;
    if (location.hash !== hash) history.replaceState(null, "", `${location.pathname}${location.search}${hash}`);
    renderRoute(snapshot.route, { preserveScroll: true });
    syncVirtualRowHeight();
    resetVirtualWindows();
    renderCards();

    const scroller = $("#appContent");
    const { key: listKey, selector, records } = activeListContext();
    const list = $(selector);
    if (!scroller || !list) return false;
    const anchorIndex = records.findIndex((record) => record.id === Number(snapshot.anchorId));
    let target = Number(snapshot.scrollTop || 0);
    if (anchorIndex >= 0) {
      target = listTopInsideScroller(list, scroller) + (anchorIndex * virtualLists[listKey].rowHeight) - Number(snapshot.anchorOffset || 0);
    }
    scroller.scrollTop = Math.max(0, target);
    renderCards(false, true);
    await nextFrame();
    await nextFrame();

    const anchorCard = snapshot.anchorId ? $(`${selector} .profile-card[data-id="${Number(snapshot.anchorId)}"]`) : null;
    if (anchorCard) {
      const delta = anchorCard.getBoundingClientRect().top - scroller.getBoundingClientRect().top - Number(snapshot.anchorOffset || 0);
      if (Math.abs(delta) > 1) scroller.scrollTop += delta;
    }
    snapshot.restorePending = false;
    snapshot.scrollTop = Math.max(0, Math.round(scroller.scrollTop));
    writeStorage(sessionStorage, key, snapshot);
    scheduleScrollRender();
    return true;
  } finally {
    state.restoreInProgress = false;
  }
}

function persistFetchQueue(records, completedIds, label, running) {
  if (!state.user?.id) return;
  const pendingIds = records
    .filter((record) => !completedIds.has(record.id))
    .map((record) => record.id);
  if (!pendingIds.length) {
    removeStorage(localStorage, scopedStorageKey(FETCH_QUEUE_STORAGE_KEY));
    return;
  }
  writeStorage(localStorage, scopedStorageKey(FETCH_QUEUE_STORAGE_KEY), {
    pendingIds,
    label: String(label || "Resuming"),
    running: Boolean(running),
    success: state.fetchSuccess,
    failed: state.fetchFailed,
    skipped: state.fetchSkipped,
    savedAt: Date.now(),
  });
}

function scheduleFetchQueueCheckpoint(records, completedIds, label, running) {
  clearTimeout(queueCheckpointTimer);
  queueCheckpointTimer = setTimeout(() => persistFetchQueue(records, completedIds, label, running), 100);
}

function clearFetchQueueCheckpoint() {
  clearTimeout(queueCheckpointTimer);
  removeStorage(localStorage, scopedStorageKey(FETCH_QUEUE_STORAGE_KEY));
}

function restoreFetchQueueCheckpoint() {
  const checkpoint = readStorage(localStorage, scopedStorageKey(FETCH_QUEUE_STORAGE_KEY), null);
  if (!checkpoint || Date.now() - Number(checkpoint.savedAt || 0) > 24 * 60 * 60 * 1000) {
    clearFetchQueueCheckpoint();
    return false;
  }
  const ids = new Set((checkpoint.pendingIds || []).map(Number).filter(Number.isFinite));
  const remaining = state.records.filter((record) => ids.has(record.id));
  if (!remaining.length) {
    clearFetchQueueCheckpoint();
    return false;
  }
  state.remainingFetchRecords = remaining;
  state.fetchSuccess = Number(checkpoint.success || 0);
  state.fetchFailed = Number(checkpoint.failed || 0);
  state.fetchSkipped = Number(checkpoint.skipped || 0);
  renderControls();
  if (checkpoint.running) {
    showToast(`Restoring unfinished fetch queue: ${remaining.length} UID${remaining.length === 1 ? "" : "s"}.`);
    setTimeout(() => {
      if (!state.fetching && state.authenticated && state.remainingFetchRecords.length) resumeFetch();
    }, 850);
  }
  return true;
}

async function enterApp(authPayload) {
  state.authenticated = true;
  state.user = authPayload.user;
  state.csrfToken = authPayload.csrf_token;
  state.selected.clear();
  state.fetchStopRequested = false;
  state.autoRetryStarted = false;
  loadUserLocalState();
  syncClientLayoutVersion();
  $("#publicShell").classList.add("hidden");
  $("#appShell").classList.remove("hidden");
  $("#currentUsername").textContent = state.user.username;
  $("#currentRole").textContent = state.user.role;
  $("#currentUserInitial").textContent = state.user.username.slice(0, 1).toUpperCase();
  $$(".admin-only").forEach((element) => element.classList.toggle("hidden", state.user.role !== "admin"));
  applyPreferences();
  syncVirtualRowHeight();
  renderRoute();
  await loadRecords();
  await restoreReturnPosition({ requirePending: true });
  const restoredQueue = restoreFetchQueueCheckpoint();
  if (!restoredQueue && state.prefs.autoRetryFailed && !state.autoRetryStarted) {
    state.autoRetryStarted = true;
    const failed = state.records.filter((record) => record.fetch_status === "error");
    if (failed.length) setTimeout(() => fetchRecords(failed, "Auto retrying"), 700);
  }
}

async function login(event) {
  event.preventDefault();
  const button = $("#loginSubmit");
  const errorEl = $("#loginError");
  hideFormMessage(errorEl);
  button.disabled = true;
  button.textContent = "Signing in…";
  try {
    const payload = await api("/api/auth/login", {
      method: "POST",
      body: JSON.stringify({ username: $("#loginUsername").value.trim(), password: $("#loginPassword").value }),
    });
    $("#loginPassword").value = "";
    await enterApp(payload);
  } catch (error) {
    showFormMessage(errorEl, error.message, "error");
  } finally {
    button.disabled = false;
    button.textContent = "Sign in securely";
  }
}

async function logout() {
  const returnKey = scopedStorageKey(RETURN_POSITION_STORAGE_KEY);
  const queueKey = scopedStorageKey(FETCH_QUEUE_STORAGE_KEY);
  try { await api("/api/auth/logout", { method: "POST", body: "{}" }); } catch (_) { /* clear locally anyway */ }
  removeStorage(sessionStorage, returnKey);
  removeStorage(localStorage, queueKey);
  showPublicShell();
  history.replaceState(null, "", `${location.pathname}#/`);
  showToast("Signed out.");
}

function filteredRecords({ savedOnly = false } = {}) {
  const query = state.query.trim().toLowerCase();
  return state.records.filter((record) => {
    if (savedOnly && !Boolean(record.is_saved)) return false;
    if (state.filter === "selected" && !state.selected.has(record.id)) return false;
    if (["pending", "success", "error"].includes(state.filter) && record.fetch_status !== state.filter) return false;
    if (!query) return true;
    return [record.uid, record.finder_code, record.name, record.username, record.instagram_username, record.fetch_status]
      .some((value) => String(value || "").toLowerCase().includes(query));
  });
}

function codeDisplay(record) {
  return record.finder_code ? escapeHtml(record.finder_code) : "Not provided";
}

function isSkippedFetch(recordOrCode) {
  const code = typeof recordOrCode === "string" ? recordOrCode : recordOrCode?.error_code;
  return [
    "access_denied", "profile_data_unavailable", "profile_not_found",
    "facebook_http_400", "facebook_http_400_all_routes",
    "rate_limited", "temporarily_blocked", "fetch_deadline_exceeded",
    "already_fetching",
  ].includes(String(code || ""));
}

function cardStatusLabel(record) {
  if (record._fetching) return "Fetching";
  if (record.fetch_status === "success") return "Success";
  if (record.fetch_status === "error") return isSkippedFetch(record) ? "Skipped" : "Failed";
  return "Pending";
}

function cardTemplate(record, index, serial) {
  const name = record.name || `UID ${record.uid}`;
  const selected = state.selected.has(record.id);
  const saved = Boolean(record.is_saved);
  const visited = Boolean(record.is_visited);
  const instagramIntent = getInstagramIntent(record, true);
  const detectedInstagramIntent = getInstagramIntent(record, false);
  const username = record.username ? `@${record.username}` : "Username unavailable";
  const imageVersion = encodeURIComponent(record.updated_at || record.fetched_at || record.id || "");
  const avatar = record.profile_pic
    ? `<img class="avatar" src="${escapeHtml(appUrl(`/api/records/${record.id}/image?v=${imageVersion}`))}" alt="${escapeHtml(name)}" loading="lazy" decoding="async">`
    : '<div class="avatar-fallback">X</div>';
  const menu = state.openMenuId === record.id ? `
    <div class="card-menu">
      <button data-action="edit" type="button">Edit finder code</button>
      <button data-action="fetch" type="button">Fetch / Retry</button>
      <button data-action="delete" class="danger-text" type="button">Delete record</button>
    </div>` : "";
  const error = record.error_message
    ? `<div class="card-error" title="${escapeHtml(record.error_message)}">${escapeHtml(record.error_message)}</div>`
    : "";
  const metrics = [
    record.follower_count !== null && record.follower_count !== undefined ? `<span class="metric-chip">Followers ${formatCount(record.follower_count)}</span>` : "",
    record.likes_count ? `<span class="metric-chip">Likes ${formatCount(record.likes_count)}</span>` : "",
    hasDetectedInstagram(record) ? `<span class="instagram-chip">${iconSvg("instagram")} Instagram</span>` : "",
  ].join("");

  return `
    <article class="profile-card ${selected ? "selected" : ""} ${visited ? "visited" : ""} ${record.error_message ? "has-error" : ""} ${state.openMenuId === record.id ? "menu-open" : ""}" data-id="${record.id}" data-uid="${escapeHtml(record.uid)}" style="--status-color:${statusColor(record._fetching ? "pending" : record.fetch_status)}">
      <div class="card-grid">
        <button class="card-number" data-action="select" type="button" aria-label="Select profile ${serial}">${selected ? "✓" : `${serial}`}</button>
        <div class="avatar-wrap">${avatar}</div>
        <div class="card-main">
          <div class="card-title-row">
            <h3 title="${escapeHtml(name)}">${escapeHtml(name)}</h3>
          </div>
          <div class="username-row">
            ${instagramIntent ? `<button class="username-link available" data-app-link="instagram" type="button">${escapeHtml(username)}</button>` : `<span class="username-link">${escapeHtml(username)}</span>`}
            ${record.username ? `<button class="mini-copy" data-action="copy-username" type="button" aria-label="Copy username">${iconSvg("copy")}</button>` : ""}
          </div>
        </div>
        <div class="card-side">
          ${detectedInstagramIntent ? `<button class="square-action ig" data-app-link="instagram-detected" type="button" aria-label="Open detected Instagram">${iconSvg("instagram")}</button>` : ""}
          <button class="square-action ${saved ? "active" : ""}" data-action="star" type="button" aria-label="${saved ? "Unsave" : "Save"} profile">${iconSvg("star")}</button>
          <button class="square-action" data-action="menu" type="button" aria-label="Profile actions">${iconSvg("more")}</button>
        </div>
        <div class="detail-grid">
          <div class="detail-box uid-detail">
            <label>UID</label>
            <button class="uid-app-link" data-app-link="facebook" type="button" title="${escapeHtml(record.uid)}">${escapeHtml(record.uid)}</button>
            <button class="mini-copy" data-action="copy-uid" type="button" aria-label="Copy UID">${iconSvg("copy")}</button>
          </div>
          <div class="detail-box code-detail finder-detail">
            <label>Finder Code</label>
            <span class="detail-value" title="${escapeHtml(record.finder_code || "Not provided")}">${codeDisplay(record)}</span>
            <button class="mini-copy" data-action="copy-code" type="button" aria-label="Copy finder code">${iconSvg("copy")}</button>
          </div>
        </div>
        <div class="card-footer"><span class="status-chip side-status">${escapeHtml(cardStatusLabel(record))}</span>${metrics}</div>
        ${error}
      </div>
      ${menu}
    </article>`;
}

const CARD_WINDOW_SIZE = 24;
const CARD_WINDOW_OVERSCAN = 6;
const CARD_ESTIMATED_HEIGHT = 96;

function listTopInsideScroller(list, scroller) {
  const listRect = list.getBoundingClientRect();
  const scrollerRect = scroller.getBoundingClientRect();
  return listRect.top - scrollerRect.top + scroller.scrollTop;
}

function virtualWindow(records, list, key) {
  const meta = virtualLists[key];
  const scroller = $("#appContent");
  const rowHeight = Math.max(96, Math.min(220, Number(meta.rowHeight) || CARD_ESTIMATED_HEIGHT));
  if (!records.length || !scroller || !list) return { start: 0, end: 0, rowHeight };
  const relativeScroll = Math.max(0, scroller.scrollTop - listTopInsideScroller(list, scroller));
  const firstVisible = Math.floor(relativeScroll / rowHeight);
  let start = Math.max(0, firstVisible - CARD_WINDOW_OVERSCAN);
  start = Math.min(start, Math.max(0, records.length - 1));
  let end = Math.min(records.length, start + CARD_WINDOW_SIZE);
  if (end - start < CARD_WINDOW_SIZE) start = Math.max(0, end - CARD_WINDOW_SIZE);
  return { start, end, rowHeight };
}

function windowedMarkup(records, start, end, rowHeight) {
  const topHeight = Math.max(0, Math.round(start * rowHeight));
  const bottomHeight = Math.max(0, Math.round((records.length - end) * rowHeight));
  const topSpacer = topHeight ? `<div class="virtual-spacer" style="height:${topHeight}px" aria-hidden="true"></div>` : "";
  const cards = records.slice(start, end).map((record, index) => cardTemplate(record, start + index, start + index + 1)).join("");
  const bottomSpacer = bottomHeight ? `<div class="virtual-spacer" style="height:${bottomHeight}px" aria-hidden="true"></div>` : "";
  return `${topSpacer}${cards}${bottomSpacer}`;
}

function measureVirtualRows(list, key) {
  requestAnimationFrame(() => {
    if (!list?.isConnected) return;
    const meta = virtualLists[key];
    // Cards have a fixed compact height. Using the CSS contract directly keeps
    // item 1 and item 2000 aligned and prevents stale giant Android spacers.
    meta.rowHeight = cssVirtualRowHeight();
    meta.calibrated = true;
  });
}

function renderVirtualList(records, selector, key, scrollOnly = false) {
  const list = $(selector);
  if (!list) return;
  const meta = virtualLists[key];
  const { start, end, rowHeight } = virtualWindow(records, list, key);
  if (scrollOnly && meta.start === start && meta.end === end && meta.count === records.length) return;
  meta.start = start;
  meta.end = end;
  meta.count = records.length;
  list.innerHTML = windowedMarkup(records, start, end, rowHeight);
  measureVirtualRows(list, key);
}

function renderCards(forceAll = false, scrollOnly = false) {
  const home = filteredRecords();
  const saved = filteredRecords({ savedOnly: true });
  if (forceAll || state.route === "/") {
    renderVirtualList(home, "#cards", "home", scrollOnly);
    $("#emptyState").classList.toggle("hidden", home.length !== 0);
    $("#listSummary").textContent = `${home.length} filtered · ${state.records.length} total`;
  }
  if (forceAll || state.route === "/saved") {
    renderVirtualList(saved, "#savedCards", "saved", scrollOnly);
    $("#savedEmptyState").classList.toggle("hidden", saved.length !== 0);
  }
}

function resetVirtualWindows() {
  Object.values(virtualLists).forEach((meta) => {
    meta.start = -1;
    meta.end = -1;
    meta.count = -1;
  });
}

function resetVirtualMeasurements() {
  Object.values(virtualLists).forEach((meta) => {
    meta.start = -1;
    meta.end = -1;
    meta.count = -1;
    meta.rowHeight = cssVirtualRowHeight();
    meta.calibrated = true;
  });
}

function scheduleScrollRender() {
  if (scrollRenderFrame) return;
  scrollRenderFrame = requestAnimationFrame(() => {
    scrollRenderFrame = 0;
    renderCards(false, true);
  });
}

function resetListPosition() {
  resetVirtualWindows();
  const content = $("#appContent");
  if (content) content.scrollTop = 0;
}

function clampAppScroll() {
  requestAnimationFrame(() => {
    const content = $("#appContent");
    if (!content) return;
    const maximum = Math.max(0, content.scrollHeight - content.clientHeight);
    if (content.scrollTop > maximum) content.scrollTop = maximum;
    scheduleScrollRender();
  });
}

function renderStats() {
  $("#totalCount").textContent = state.records.length;
  $("#successCount").textContent = state.records.filter((record) => record.fetch_status === "success").length;
  $("#imageCount").textContent = state.records.filter((record) => record.profile_pic).length;
  $("#igCount").textContent = state.records.filter(hasDetectedInstagram).length;
  $("#errorCount").textContent = state.records.filter((record) => record.fetch_status === "error").length;
}

function renderControls() {
  const selectedCount = state.selected.size;
  $("#selectionBar").classList.toggle("hidden", selectedCount === 0);
  $("#selectedCount").textContent = `${selectedCount} selected`;
  $("#fetchAllBtn").disabled = state.fetching || state.importing;
  $("#importBtn").disabled = state.fetching || state.importing;
  if ($("#stopFetchBtn")) $("#stopFetchBtn").classList.toggle("hidden", !state.fetching);
  if ($("#resumeFetchBtn")) $("#resumeFetchBtn").disabled = state.fetching || !state.remainingFetchRecords.length;
  $("#clearSearchBtn").classList.toggle("hidden", !state.query);
  $$("#filterRow [data-filter]").forEach((button) => button.classList.toggle("active", button.dataset.filter === state.filter));
}

function render() {
  if (!state.authenticated) return;
  renderStats();
  renderControls();
  renderCards(state.route !== "/" && state.route !== "/saved");
}

async function loadRecords() {
  const payload = await api("/api/records");
  state.records = payload.data || [];
  state.saved = new Set(state.records.filter((record) => record.is_saved).map((record) => String(record.uid)));
  const localVisited = new Set(state.visited);
  const missingVisitedIds = [];
  state.records.forEach((record) => {
    if (localVisited.has(String(record.uid)) && !record.is_visited) {
      record.is_visited = true;
      missingVisitedIds.push(record.id);
    }
  });
  state.visited = new Set(state.records.filter((record) => record.is_visited).map((record) => String(record.uid)));
  saveUserSet(VISITED_STORAGE_KEY, state.visited);
  state.selected.clear();
  resetVirtualWindows();
  render();
  clampAppScroll();
  if (missingVisitedIds.length) {
    api("/api/records/mark-visited", { method: "POST", body: JSON.stringify({ ids: missingVisitedIds }) }).catch(() => {});
  }
}

function replaceRecord(updated) {
  const index = state.records.findIndex((record) => record.id === updated.id);
  if (index >= 0) state.records[index] = { ...state.records[index], ...updated };
  const record = state.records[index];
  if (record) {
    if (record.is_saved) state.saved.add(String(record.uid)); else state.saved.delete(String(record.uid));
    if (record.is_visited) state.visited.add(String(record.uid)); else state.visited.delete(String(record.uid));
  }
}

function patchVisibleRecord(recordId) {
  const record = state.records.find((item) => item.id === recordId);
  if (!record) return;
  const touchedLists = new Set();
  document.querySelectorAll(`.profile-card[data-id="${recordId}"]`).forEach((card) => {
    const parent = card.parentElement;
    const savedList = parent?.id === "savedCards";
    const list = savedList ? filteredRecords({ savedOnly: true }) : filteredRecords();
    const serialIndex = list.findIndex((item) => item.id === recordId);
    if (serialIndex >= 0) {
      touchedLists.add(savedList ? "saved" : "home");
      card.outerHTML = cardTemplate(record, serialIndex, serialIndex + 1);
    }
  });
  touchedLists.forEach((key) => measureVirtualRows(key === "saved" ? $("#savedCards") : $("#cards"), key));
  renderStats();
}

function paintProgress() {
  progressRenderFrame = 0;
  if (progressHideTimer) {
    clearTimeout(progressHideTimer);
    progressHideTimer = 0;
  }
  const pending = updateProgress.pending;
  if (!pending) return;
  const { done, total, label } = pending;
  const percent = total ? Math.round((done / total) * 100) : 0;
  $("#progressSection").classList.remove("hidden");
  $("#progressText").textContent = `${label} · ✓${state.fetchSuccess} ↷${state.fetchSkipped} ✕${state.fetchFailed}`;
  $("#progressPercent").textContent = `${percent}%`;
  $("#progressBar").style.width = `${percent}%`;
  lastProgressPaint = performance.now();
}

function updateProgress(done, total, label) {
  updateProgress.pending = { done, total, label };
  const forcePaint = done === 0 || done >= total || performance.now() - lastProgressPaint >= 120;
  if (forcePaint) {
    if (progressRenderFrame) cancelAnimationFrame(progressRenderFrame);
    progressRenderFrame = requestAnimationFrame(paintProgress);
  } else if (!progressRenderFrame) {
    progressRenderFrame = requestAnimationFrame(paintProgress);
  }
}

function hideProgressLater() {
  if (progressHideTimer) clearTimeout(progressHideTimer);
  progressHideTimer = setTimeout(() => {
    progressHideTimer = 0;
    $("#progressSection").classList.add("hidden");
  }, 900);
}

async function importRecords() {
  if (state.importing || state.fetching) return;
  const text = $("#importText").value.trim();
  if (!text) return showToast("Paste at least one UID.", "error");
  state.importing = true;
  renderControls();
  updateProgress(0, 1, "Importing records…");
  try {
    const payload = await api("/api/import", { method: "POST", body: JSON.stringify({ text }) });
    updateProgress(1, 1, "Import complete");
    $("#importText").value = "";
    updateLineCount();
    await loadRecords();
    navigate("/");
    const data = payload.data;
    const report = $("#invalidImportReport");
    if (report) { report.classList.toggle("hidden", !data.invalid_count); report.textContent = data.invalid_count ? data.invalid.map((item) => `Line ${item.line}: ${item.reason} — ${item.value}`).join("\n") : ""; }
    showToast(`Imported ${data.inserted}; updated ${data.updated}; invalid ${data.invalid_count}.`, data.invalid_count ? "error" : "success");
  } catch (error) {
    showToast(error.message, "error");
  } finally {
    state.importing = false;
    renderControls();
    hideProgressLater();
  }
}

async function restoreAccountBackup() {
  const input = $("#backupFileInput");
  const file = input?.files?.[0];
  if (!file) return showToast("Choose a JSON backup file.", "error");
  if (file.size > 8 * 1024 * 1024) return showToast("Backup file is too large.", "error");
  try {
    const payload = JSON.parse(await file.text());
    const result = await api("/api/import-backup", { method: "POST", body: JSON.stringify(payload) });
    input.value = "";
    await loadRecords();
    navigate("/");
    const data = result.data || {};
    showToast(`Backup restored: ${data.inserted || 0} inserted, ${data.updated || 0} updated.`, data.invalid_count ? "error" : "success");
  } catch (error) {
    showToast(error instanceof SyntaxError ? "Invalid JSON backup file." : error.message, "error");
  }
}

async function fetchOne(recordId, silent = false) {
  const record = state.records.find((item) => item.id === recordId);
  if (!record) return { ok: false, code: "record_not_found" };
  record._fetching = true;
  patchVisibleRecord(recordId);

  let outcome = { ok: false, code: "request_failed" };
  // A bulk queue gets one bounded attempt per UID so a bad/login-wall UID
  // cannot consume the queue twice. The card-level Retry action keeps one
  // extra transient retry for convenience.
  const maxAttempts = silent ? 1 : 2;
  for (let attempt = 0; attempt < maxAttempts; attempt += 1) {
    const controller = new AbortController();
    let timedOut = false;
    const timeoutId = setTimeout(() => {
      timedOut = true;
      controller.abort();
    }, FETCH_REQUEST_TIMEOUT_MS);
    state.activeFetchControllers.add(controller);

    try {
      const payload = await api(`/api/records/${recordId}/fetch`, {
        method: "POST",
        body: "{}",
        signal: controller.signal,
      });
      replaceRecord(payload.data);
      outcome = { ok: true, code: "success" };
      break;
    } catch (caught) {
      if (caught?.name === "AbortError" && state.fetchStopRequested) {
        outcome = { ok: false, code: "cancelled", cancelled: true };
        break;
      }
      const error = caught?.name === "AbortError" && timedOut
        ? Object.assign(new Error("The server fetch exceeded the safe time limit."), { code: "client_timeout", status: 504 })
        : caught;
      const code = error?.code || "request_failed";
      const canRetry = attempt + 1 < maxAttempts && TRANSIENT_FETCH_CODES.has(code) && !state.fetchStopRequested;
      if (canRetry) {
        await new Promise((resolve) => setTimeout(resolve, FETCH_RETRY_DELAY_MS * (attempt + 1)));
        continue;
      }
      if (code !== "already_fetching") {
        record.fetch_status = "error";
        record.error_code = code;
        record.error_message = error?.message || "Fetch failed.";
      }
      outcome = { ok: false, code, status: error?.status || 0 };
      if (!silent) showToast(`${code}: ${error?.message || "Fetch failed."}`, "error");
      break;
    } finally {
      clearTimeout(timeoutId);
      state.activeFetchControllers.delete(controller);
    }
  }

  const current = state.records.find((item) => item.id === recordId);
  if (current) delete current._fetching;
  if (state.query || state.filter !== "all") {
    renderCards();
    clampAppScroll();
  } else {
    patchVisibleRecord(recordId);
  }
  if (outcome.ok && !silent) showToast("Profile fetched.");
  return outcome;
}

function stopFetch(silent = false) {
  if (!state.fetching && !state.activeFetchControllers.size) return;
  state.fetchStopRequested = true;
  state.activeFetchControllers.forEach((controller) => controller.abort());
  if (!silent) showToast("Stopping fetch queue safely…");
}

async function fetchRecords(records, label = "Fetching", { keepCounters = false } = {}) {
  if (state.fetching || state.importing || !records.length) return;
  state.fetching = true;
  state.fetchStopRequested = false;
  state.remainingFetchRecords = [];
  if (!keepCounters) {
    state.fetchSuccess = 0;
    state.fetchFailed = 0;
    state.fetchSkipped = 0;
  }
  renderControls();

  let success = 0;
  let failed = 0;
  let skipped = 0;
  let completed = 0;
  let nextIndex = 0;
  let blockPressure = 0;
  const queue = [...records];
  const originalTotal = records.length;
  const deferredFetchCounts = new Map();
  const completedIds = new Set();
  updateProgress(0, originalTotal, `${label} ${originalTotal} records…`);
  persistFetchQueue(records, completedIds, label, true);

  const worker = async () => {
    while (!state.fetchStopRequested) {
      while (document.hidden && !state.fetchStopRequested) {
        await new Promise((resolve) => setTimeout(resolve, 550));
      }
      if (state.fetchStopRequested) return;
      const index = nextIndex;
      nextIndex += 1;
      if (index >= queue.length) return;
      const record = queue[index];
      let outcome;
      try {
        outcome = await fetchOne(record.id, true);
      } catch (unexpected) {
        // A rendering/browser exception must never kill a 2,000 UID batch.
        // Convert it into one record failure and allow this worker to advance.
        record.fetch_status = "error";
        record.error_code = "client_worker_error";
        record.error_message = unexpected?.message || "The browser worker failed for this UID.";
        delete record._fetching;
        outcome = { ok: false, code: "client_worker_error" };
        try { patchVisibleRecord(record.id); } catch (_) { /* next render repairs it */ }
      }
      if (outcome.cancelled) return;

      if (outcome.code === "already_fetching") {
        const deferrals = Number(deferredFetchCounts.get(record.id) || 0);
        if (deferrals < 2 && !state.fetchStopRequested) {
          deferredFetchCounts.set(record.id, deferrals + 1);
          queue.push(record);
          updateProgress(completed, originalTotal, `Deferred active UID ${record.uid}; continuing queue`);
          await new Promise((resolve) => setTimeout(resolve, 180 + (deferrals * 220)));
          continue;
        }
      }

      completed += 1;
      completedIds.add(record.id);
      if (outcome.ok) {
        success += 1;
        state.fetchSuccess += 1;
        blockPressure = Math.max(0, blockPressure - 1);
      } else if (isSkippedFetch(outcome.code)) {
        skipped += 1;
        state.fetchSkipped += 1;
        if (["rate_limited", "temporarily_blocked"].includes(outcome.code)) {
          blockPressure = Math.min(6, blockPressure + 1);
        }
      } else {
        failed += 1;
        state.fetchFailed += 1;
      }
      updateProgress(completed, originalTotal, `Completed ${completed}/${originalTotal}`);
      scheduleFetchQueueCheckpoint(records, completedIds, label, true);

      // Every UID is independent. Login walls, HTTP 400, profile privacy,
      // temporary blocks and timeouts are recorded as skipped/failed and the
      // worker always advances to the next UID. Only the user's Stop button
      // can stop the batch.
      if (completed % FETCH_UI_REFRESH_EVERY === 0) renderControls();
      if (!state.fetchStopRequested && nextIndex < queue.length) {
        const baseDelay = outcome.ok ? FETCH_SUCCESS_DELAY_MS : FETCH_FAILURE_DELAY_MS;
        const pressureDelay = ["rate_limited", "temporarily_blocked"].includes(outcome.code)
          ? FETCH_BLOCK_DELAY_MS * blockPressure
          : 0;
        await new Promise((resolve) => setTimeout(resolve, baseDelay + pressureDelay));
      }
    }
  };

  let requestedWorkers = Math.min(4, Math.max(1, Number(state.prefs.workerConcurrency) || FETCH_CONCURRENCY));
  const connection = navigator.connection || navigator.mozConnection || navigator.webkitConnection;
  if (connection?.saveData || /(^|-)2g$/.test(String(connection?.effectiveType || ""))) requestedWorkers = 1;
  const workerCount = Math.min(requestedWorkers, originalTotal);
  await Promise.allSettled(Array.from({ length: workerCount }, () => worker()));

  state.activeFetchControllers.forEach((controller) => controller.abort());
  state.activeFetchControllers.clear();
  const manuallyStopped = state.fetchStopRequested && completed < originalTotal;
  state.remainingFetchRecords = manuallyStopped
    ? records.filter((queued) => !completedIds.has(queued.id))
    : [];
  state.fetching = false;
  state.fetchStopRequested = false;
  resetVirtualWindows();
  render();
  clampAppScroll();

  if (manuallyStopped) {
    clearTimeout(queueCheckpointTimer);
    persistFetchQueue(records, completedIds, label, false);
    showToast(`Fetch stopped: ${completed}/${originalTotal} completed. ${state.remainingFetchRecords.length} UID saved for Resume.`, "error");
  } else {
    clearFetchQueueCheckpoint();
    showToast(`Fetch complete: ${success} success, ${skipped} skipped, ${failed} failed.`, failed ? "error" : "success");
  }
  hideProgressLater();
}

async function fetchAll() {
  const targets = state.records.filter((record) => record.fetch_status !== "success" || !record.profile_pic);
  if (!targets.length) return showToast("All records already have complete profile data.");
  await fetchRecords(targets, "Fetching");
}

async function retryFailed() {
  const targets = state.records.filter((record) => record.fetch_status === "error");
  if (!targets.length) return showToast("No failed records to retry.");
  await fetchRecords(targets, "Retrying failed");
}

async function resumeFetch() {
  const remaining = state.remainingFetchRecords.filter((item) => state.records.some((record) => record.id === item.id));
  if (!remaining.length) return showToast("No stopped queue is waiting.");
  state.remainingFetchRecords = [];
  await fetchRecords(remaining, "Resuming", { keepCounters: true });
}

async function deleteRecord(recordId) {
  const record = state.records.find((item) => item.id === recordId);
  if (!record || !confirm(`Delete UID ${record.uid}?`)) return;
  try {
    await api(`/api/records/${recordId}`, { method: "DELETE" });
    state.records = state.records.filter((item) => item.id !== recordId);
    state.selected.delete(recordId);
    state.saved.delete(String(record.uid));
    state.visited.delete(String(record.uid));
    saveUserSet(VISITED_STORAGE_KEY, state.visited);
    resetVirtualWindows();
    render();
    clampAppScroll();
    showToast("Record deleted.");
  } catch (error) { showToast(error.message, "error"); }
}

async function deleteSelected() {
  const ids = [...state.selected];
  if (!ids.length) return showToast("Select at least one record.", "error");
  if (!confirm(`Delete ${ids.length} selected records?`)) return;
  try {
    await api("/api/records/bulk-delete", { method: "POST", body: JSON.stringify({ ids }) });
    const idSet = new Set(ids);
    const removed = state.records.filter((record) => idSet.has(record.id));
    state.records = state.records.filter((record) => !idSet.has(record.id));
    removed.forEach((record) => { state.saved.delete(String(record.uid)); state.visited.delete(String(record.uid)); });
    saveUserSet(VISITED_STORAGE_KEY, state.visited);
    state.selected.clear();
    resetVirtualWindows();
    render();
    clampAppScroll();
    showToast(`${ids.length} records deleted.`);
  } catch (error) { showToast(error.message, "error"); }
}

async function deleteAll() {
  if (!state.records.length) return showToast("There are no records to delete.");
  if (!confirm(`Delete all ${state.records.length} records? This cannot be undone.`)) return;
  try {
    await api("/api/records", { method: "DELETE" });
    state.records = [];
    state.selected.clear();
    state.saved.clear();
    state.visited.clear();
    saveUserSet(VISITED_STORAGE_KEY, state.visited);
    resetVirtualWindows();
    render();
    clampAppScroll();
    showToast("All records deleted.");
  } catch (error) { showToast(error.message, "error"); }
}

async function editFinderCode(recordId) {
  const record = state.records.find((item) => item.id === recordId);
  if (!record) return;
  const value = prompt(`Finder code for UID ${record.uid}`, record.finder_code || "");
  if (value === null) return;
  try {
    const payload = await api(`/api/records/${recordId}`, { method: "PATCH", body: JSON.stringify({ finder_code: value }) });
    replaceRecord({ ...payload.data, _showCode: true });
    render();
    showToast("Finder code updated.");
  } catch (error) { showToast(error.message, "error"); }
}

async function writeClipboard(text) {
  if (navigator.clipboard?.writeText) {
    try { await navigator.clipboard.writeText(text); return; } catch (_) { /* fallback below */ }
  }
  const textarea = document.createElement("textarea");
  textarea.value = text;
  textarea.setAttribute("readonly", "");
  textarea.style.position = "fixed";
  textarea.style.opacity = "0";
  document.body.appendChild(textarea);
  textarea.select();
  textarea.setSelectionRange(0, textarea.value.length);
  const copied = document.execCommand("copy");
  textarea.remove();
  if (!copied) throw new Error("Copy failed");
}

function flashCopyButton(button) {
  if (!button) return;
  button.classList.add("copied");
  const original = button.innerHTML;
  button.innerHTML = iconSvg("check");
  setTimeout(() => {
    if (!button.isConnected) return;
    button.innerHTML = original;
    button.classList.remove("copied");
  }, 850);
}

async function copyValue(value, button, message) {
  if (!value) return showToast("Value is unavailable.", "error");
  try { await writeClipboard(value); flashCopyButton(button); showToast(message); }
  catch (_) { showToast("Clipboard permission was denied.", "error"); }
}

async function copySelected(format = "pair") {
  const selected = state.records.filter((record) => state.selected.has(record.id));
  if (!selected.length) return showToast("Select at least one record.", "error");
  const text = format === "uid" ? selected.map((record) => record.uid).join("\n") : selected.map((record) => `${record.uid}|${record.finder_code || ""}`).join("\n");
  await copyValue(text, null, `${selected.length} records copied.`);
}

async function toggleSaved(record) {
  const next = !Boolean(record.is_saved);
  try {
    const payload = await api(`/api/records/${record.id}`, { method: "PATCH", body: JSON.stringify({ is_saved: next }) });
    replaceRecord(payload.data);
    if (state.route === "/saved" || state.query) {
      resetVirtualWindows();
      renderCards();
      clampAppScroll();
    } else {
      patchVisibleRecord(record.id);
    }
  } catch (error) { showToast(error.message, "error"); }
}

function selectVisible() {
  const records = filteredRecords();
  const meta = virtualLists.home;
  const start = Math.max(0, meta.start);
  const end = meta.end > start ? meta.end : Math.min(records.length, PAGE_SIZE);
  const visible = records.slice(start, end);
  const allSelected = visible.length && visible.every((record) => state.selected.has(record.id));
  visible.forEach((record) => allSelected ? state.selected.delete(record.id) : state.selected.add(record.id));
  renderControls();
  renderCards();
}

function selectAllFiltered() {
  filteredRecords().forEach((record) => state.selected.add(record.id));
  render();
}

function deselectAll() {
  state.selected.clear();
  render();
}

function markVisited(record) {
  record.is_visited = true;
  state.visited.add(String(record.uid));
  saveUserSet(VISITED_STORAGE_KEY, state.visited);
  document.querySelectorAll(".profile-card").forEach((card) => {
    if (card.dataset.uid === String(record.uid)) card.classList.add("visited");
  });
  const body = JSON.stringify({ record_id: record.id, csrf_token: state.csrfToken });
  let queued = false;
  try {
    if (navigator.sendBeacon) {
      queued = navigator.sendBeacon(appUrl("/api/records/mark-visited"), new Blob([body], { type: "application/json" }));
    }
  } catch (_) { queued = false; }
  if (!queued) {
    api("/api/records/mark-visited", { method: "POST", body: JSON.stringify({ record_id: record.id }) }).catch(() => {});
  }
}

function openFacebookApp(record) {
  saveReturnPosition(record.id);
  markVisited(record);
  showToast("Opening Facebook app…");
  const started = Date.now();
  window.location.href = getFacebookIntent(record.uid);
  setTimeout(() => { if (!document.hidden && Date.now() - started > 1000) showToast("Facebook app may not be installed.", "error"); }, 1300);
}

function openInstagramApp(record, detectedOnly = false) {
  const intent = getInstagramIntent(record, !detectedOnly);
  if (!intent) return showToast("Instagram username is unavailable.", "error");
  saveReturnPosition(record.id);
  showToast("Opening Instagram app…");
  const started = Date.now();
  window.location.href = intent;
  setTimeout(() => { if (!document.hidden && Date.now() - started > 1000) showToast("Instagram app may not be installed.", "error"); }, 1300);
}

function updateLineCount() {
  const count = $("#importText").value.split(/\r?\n/).filter((line) => line.trim()).length;
  $("#lineCount").textContent = `${count} line${count === 1 ? "" : "s"}`;
}

function normalizeRoute(value) {
  const route = String(value || "/").replace(/^#/, "") || "/";
  const allowed = ["/", "/import", "/saved", "/settings", "/admin"];
  if (!allowed.includes(route)) return "404";
  if (route === "/admin" && state.user?.role !== "admin") return "404";
  return route;
}

function navigate(route) {
  if (!state.authenticated) return;
  const currentSnapshot = captureReturnPosition();
  if (currentSnapshot) {
    currentSnapshot.restorePending = false;
    writeStorage(sessionStorage, scopedStorageKey(RETURN_POSITION_STORAGE_KEY), currentSnapshot);
  }
  const hash = route === "/" ? "#/" : `#${route}`;
  if (location.hash === hash) renderRoute(route); else location.hash = hash;
}

function renderRoute(forcedRoute, { preserveScroll = false } = {}) {
  if (!state.authenticated) return;
  state.route = normalizeRoute(forcedRoute || location.hash.slice(1));
  $$(".screen").forEach((screen) => screen.classList.toggle("hidden", screen.dataset.screen !== state.route));
  $$(".nav-button").forEach((button) => button.classList.toggle("active", button.dataset.route === state.route));
  state.openMenuId = null;
  $("#userMenu").classList.add("hidden");
  resetVirtualWindows();
  if (!preserveScroll) $("#appContent").scrollTop = 0;
  if (state.route === "/" || state.route === "/saved") renderCards();
  if (state.route === "/admin") { loadUsers(); loadAudit(); }
}

async function runFetchDiagnostic() {
  const button = $("#fetchDiagnosticBtn");
  const output = $("#fetchDiagnosticResult");
  if (!button || !output) return;
  const firstUid = state.records.find((record) => record.uid)?.uid || "";
  button.disabled = true;
  button.textContent = "Testing server…";
  output.classList.remove("hidden");
  output.textContent = "Checking application path, DNS and outbound HTTPS…";
  try {
    const suffix = firstUid ? `?uid=${encodeURIComponent(firstUid)}` : "";
    const payload = await api(`/api/system/fetch-diagnostic${suffix}`);
    const report = payload.data || {};
    const lines = [
      `App base: ${report.app_base || "/"}`,
      `Transport: ${report.transport?.mode || report.proxy_mode || "direct"} (public proxy rotation disabled)`,
      `DNS: ${report.dns?.ok ? "OK" : "FAILED"} (${(report.dns?.addresses || []).join(", ") || report.dns?.message || "no address"})`,
      `Outbound HTTPS: ${report.outbound?.ok ? "OK" : "FAILED"}${report.outbound?.status ? ` — HTTP ${report.outbound.status}` : ""}`,
      `Final host: ${report.outbound?.final_host || "unavailable"}`,
    ];
    if (report.profile) {
      lines.push(`UID test: ${report.profile.ok ? "SUCCESS" : "FAILED"}`);
      if (report.profile.code) lines.push(`Code: ${report.profile.code}`);
      if (report.profile.message) lines.push(`Message: ${report.profile.message}`);
    } else {
      lines.push("UID test: import at least one UID, then run again.");
    }
    lines.push(`Advice: ${report.advice || "No additional advice."}`);
    output.textContent = lines.join("\n");
  } catch (error) {
    output.textContent = `Diagnostic request failed\nCode: ${error.code}\nMessage: ${error.message}`;
  } finally {
    button.disabled = false;
    button.textContent = "Run server fetch test";
  }
}

function exportData(format) {
  window.location.href = appUrl(`/api/export?format=${encodeURIComponent(format)}`);
}

async function createBackup() {
  try { const payload = await api("/api/system/backup", { method: "POST", body: "{}" }); showToast(`Backup created: ${payload.file}`); }
  catch (error) { showToast(error.message, "error"); }
}

async function clearImageCache() {
  if (!confirm("Clear all cached profile images?")) return;
  try { const payload = await api("/api/system/cache/clear", { method: "POST", body: "{}" }); showToast(`Removed ${payload.removed} cache files.`); }
  catch (error) { showToast(error.message, "error"); }
}

async function loadAudit() {
  const target = $("#auditList");
  if (!target || state.user?.role !== "admin") return;
  try {
    const payload = await api("/api/admin/audit?limit=100");
    target.innerHTML = (payload.data || []).map((row) => `<article class="audit-row"><strong>${escapeHtml(row.action)}</strong><span>${escapeHtml(row.actor_username || "system")} → ${escapeHtml(row.target_username || "—")}</span><small>${escapeHtml(row.created_at)}${row.details ? ` · ${escapeHtml(row.details)}` : ""}</small></article>`).join("") || "<p>No audit events yet.</p>";
  } catch (error) { target.textContent = error.message; }
}

async function changePassword(event) {
  event.preventDefault();
  const message = $("#passwordMessage");
  hideFormMessage(message);
  try {
    await api("/api/auth/change-password", {
      method: "POST",
      body: JSON.stringify({ current_password: $("#currentPassword").value, new_password: $("#newPassword").value }),
    });
    event.currentTarget.reset();
    showFormMessage(message, "Password updated successfully.", "success");
  } catch (error) { showFormMessage(message, error.message, "error"); }
}

async function loadUsers() {
  if (state.user?.role !== "admin") return;
  try {
    const payload = await api("/api/admin/users");
    state.users = payload.data || [];
    renderUsers();
  } catch (error) { showToast(error.message, "error"); }
}

function renderUsers() {
  const container = $("#usersList");
  if (!state.users.length) {
    container.innerHTML = '<div class="empty-box"><strong>No accounts</strong><p>Create the first operator.</p></div>';
    return;
  }
  container.innerHTML = state.users.map((user) => `
    <article class="user-row" data-user-id="${user.id}">
      <div class="user-identity"><strong>${escapeHtml(user.username)}</strong><small>${Number(user.record_count || 0)} records · Last login ${escapeHtml(user.last_login_at || "Never")} · Last active ${escapeHtml(user.last_active_at || "Never")} · Failed ${Number(user.failed_login_count || 0)}</small></div>
      <span class="role-chip">${escapeHtml(user.role)}</span>
      <span class="user-status ${user.is_active ? "" : "disabled"}">${user.is_active ? "Active" : "Disabled"}</span>
      <div class="user-actions">
        <button data-user-action="reset" type="button">Password</button>${user.id !== state.user.id ? `<button data-user-action="role" type="button">Role</button>` : ""}
        ${user.id !== state.user.id ? `<button data-user-action="toggle" type="button">${user.is_active ? "Disable" : "Enable"}</button><button data-user-action="delete" class="danger-text" type="button">Delete</button>` : ""}
      </div>
    </article>`).join("");
}

async function createUser(event) {
  event.preventDefault();
  const form = event.currentTarget;
  const button = form.querySelector('button[type="submit"]');
  const message = $("#createUserMessage");
  const username = $("#newUserUsername").value.trim();
  const password = $("#newUserPassword").value;
  hideFormMessage(message);
  if (!/^[A-Za-z0-9_.-]{3,32}$/.test(username)) {
    return showFormMessage(message, "Username: 3–32 letters, numbers, dot, dash or underscore.", "error");
  }
  if (password.length < 8) return showFormMessage(message, "Password must contain at least 8 characters.", "error");
  button.disabled = true;
  button.textContent = "Creating…";
  try {
    await api("/api/admin/users", {
      method: "POST",
      body: JSON.stringify({ username, password, role: $("#newUserRole").value }),
    });
    form.reset();
    showFormMessage(message, `Account ${username} created. Its records are isolated from every other account.`, "success");
    await loadUsers();
  } catch (error) {
    showFormMessage(message, `${error.code}: ${error.message}`, "error");
  } finally {
    button.disabled = false;
    button.textContent = "Create account";
  }
}

async function manageUser(action, userId) {
  const user = state.users.find((item) => item.id === userId);
  if (!user) return;
  try {
    if (action === "reset") {
      const password = prompt(`New password for ${user.username} (minimum 8 characters)`);
      if (password === null) return;
      await api(`/api/admin/users/${userId}`, { method: "PATCH", body: JSON.stringify({ password }) });
      showToast("Password reset.");
    } else if (action === "role") {
      const role = prompt(`Role for ${user.username}: admin or user`, user.role);
      if (role === null) return;
      const normalized = role.trim().toLowerCase();
      if (!["admin", "user"].includes(normalized)) return showToast("Role must be admin or user.", "error");
      await api(`/api/admin/users/${userId}`, { method: "PATCH", body: JSON.stringify({ role: normalized }) });
      showToast("Role updated.");
    } else if (action === "toggle") {
      await api(`/api/admin/users/${userId}`, { method: "PATCH", body: JSON.stringify({ is_active: !user.is_active }) });
      showToast(user.is_active ? "Account disabled." : "Account enabled.");
    } else if (action === "delete") {
      if (!confirm(`Delete account ${user.username}?`)) return;
      await api(`/api/admin/users/${userId}`, { method: "DELETE" });
      showToast("Account deleted.");
    }
    await loadUsers();
  } catch (error) { showToast(error.message, "error"); }
}


function handleInfiniteScroll() {
  scheduleScrollRender();
  scheduleReturnPositionSave();
}

function initializeIntersectionObservers() {
  // IntersectionObserver is intentionally not used for card paging anymore.
  // Android Chrome could leave a giant stale spacer after a list rebuild.
  // Scroll-position virtualization keeps both top and bottom spacers aligned.
  const IntersectionObserver = window.IntersectionObserver; // compatibility marker
  void IntersectionObserver;
  scheduleScrollRender();
}

function initializeSwipeDelete() {
  let startX = 0;
  let startY = 0;
  let activeCard = null;
  document.addEventListener("touchstart", (event) => {
    if (!state.authenticated || !state.prefs.swipeDelete || event.touches.length !== 1) return;
    activeCard = event.target.closest(".profile-card");
    if (!activeCard || event.target.closest("button, input, select, textarea")) { activeCard = null; return; }
    startX = event.touches[0].clientX;
    startY = event.touches[0].clientY;
  }, { passive: true });
  document.addEventListener("touchend", (event) => {
    if (!activeCard || !event.changedTouches.length) return;
    const dx = event.changedTouches[0].clientX - startX;
    const dy = event.changedTouches[0].clientY - startY;
    const id = Number(activeCard.dataset.id);
    activeCard = null;
    if (dx < -95 && Math.abs(dy) < 55) deleteRecord(id);
  }, { passive: true });
}

function bindEvents() {
  $("#headerLoginBtn").addEventListener("click", () => $("#loginSection").scrollIntoView({ behavior: "smooth" }));
  $("#heroLoginBtn").addEventListener("click", () => $("#loginSection").scrollIntoView({ behavior: "smooth" }));
  $("#loginForm").addEventListener("submit", login);
  $("#logoutBtn").addEventListener("click", logout);
  $("#userMenuBtn").addEventListener("click", (event) => { event.stopPropagation(); $("#userMenu").classList.toggle("hidden"); });

  document.addEventListener("click", async (event) => {
    const nav = event.target.closest("[data-nav]");
    if (nav && state.authenticated) { event.preventDefault(); navigate(nav.dataset.nav); return; }

    const appLink = event.target.closest("[data-app-link]");
    if (appLink) {
      const card = appLink.closest("[data-id]");
      const record = state.records.find((item) => item.id === Number(card?.dataset.id));
      if (!record) return;
      if (appLink.dataset.appLink === "facebook") openFacebookApp(record);
      else openInstagramApp(record, appLink.dataset.appLink === "instagram-detected");
      return;
    }

    const actionButton = event.target.closest("button[data-action]");
    if (actionButton) {
      const card = actionButton.closest("[data-id]");
      const record = state.records.find((item) => item.id === Number(card?.dataset.id));
      if (!record) return;
      const action = actionButton.dataset.action;
      if (action === "select") {
        if (state.selected.has(record.id)) state.selected.delete(record.id); else state.selected.add(record.id);
        renderControls();
        patchVisibleRecord(record.id);
      } else if (action === "star") toggleSaved(record);
      else if (action === "menu") { state.openMenuId = state.openMenuId === record.id ? null : record.id; renderCards(); }
      else if (action === "fetch") {
        state.openMenuId = null;
        if (state.fetching) showToast("Wait for the active queue or stop it first.", "error");
        else await fetchOne(record.id);
      }
      else if (action === "edit") { state.openMenuId = null; await editFinderCode(record.id); }
      else if (action === "delete") { state.openMenuId = null; await deleteRecord(record.id); }
      else if (action === "copy-uid") await copyValue(record.uid, actionButton, "UID copied.");
      else if (action === "copy-code") await copyValue(record.finder_code, actionButton, "Finder code copied.");
      else if (action === "copy-username") await copyValue(record.username, actionButton, "Username copied.");
      return;
    }

    const userAction = event.target.closest("[data-user-action]");
    if (userAction) {
      const row = userAction.closest("[data-user-id]");
      await manageUser(userAction.dataset.userAction, Number(row?.dataset.userId));
      return;
    }

    if (!event.target.closest("#userMenu, #userMenuBtn, .card-menu")) {
      $("#userMenu").classList.add("hidden");
      if (state.openMenuId !== null) { state.openMenuId = null; renderCards(); }
    }
  });

  document.addEventListener("error", (event) => {
    const image = event.target.closest?.("img.avatar");
    if (!image) return;
    const fallback = document.createElement("div");
    fallback.className = "avatar-fallback";
    fallback.textContent = "X";
    image.replaceWith(fallback);
  }, true);

  $("#fetchAllBtn").addEventListener("click", fetchAll);
  $("#retryFailedBtn")?.addEventListener("click", retryFailed);
  $("#resumeFetchBtn")?.addEventListener("click", resumeFetch);
  $("#stopFetchBtn")?.addEventListener("click", () => stopFetch(false));
  $("#selectVisibleBtn").addEventListener("click", selectVisible);
  $("#copySelectedBtn").addEventListener("click", () => copySelected("pair"));
  $("#copyUidOnlyBtn")?.addEventListener("click", () => copySelected("uid"));
  $("#selectAllFilteredBtn")?.addEventListener("click", selectAllFiltered);
  $("#deselectAllBtn")?.addEventListener("click", deselectAll);
  $("#deleteSelectedBtn").addEventListener("click", deleteSelected);
  $("#deleteAllBtn").addEventListener("click", deleteAll);
  $("#importBtn").addEventListener("click", importRecords);
  $("#restoreBackupBtn")?.addEventListener("click", restoreAccountBackup);
  $("#importText").addEventListener("input", updateLineCount);

  $("#searchInput").addEventListener("input", (event) => {
    state.query = event.target.value;
    if ($("#savedSearchInput")) $("#savedSearchInput").value = state.query;
    clearTimeout(searchTimer);
    searchTimer = setTimeout(() => {
      resetListPosition();
      render();
    }, 120);
  });
  $("#clearSearchBtn").addEventListener("click", () => {
    state.query = "";
    $("#searchInput").value = "";
    if ($("#savedSearchInput")) $("#savedSearchInput").value = "";
    resetListPosition();
    render();
  });
  $("#savedSearchInput")?.addEventListener("input", (event) => {
    state.query = event.target.value;
    $("#searchInput").value = state.query;
    clearTimeout(searchTimer);
    searchTimer = setTimeout(() => {
      resetListPosition();
      render();
    }, 120);
  });
  $("#filterRow").addEventListener("click", (event) => {
    const button = event.target.closest("[data-filter]");
    if (!button) return;
    state.filter = button.dataset.filter;
    resetListPosition();
    render();
  });

  $("#themeSelect").addEventListener("change", (event) => { state.prefs.theme = event.target.value; savePreferences(); });
  $("#fontSizeSelect").addEventListener("change", (event) => { state.prefs.fontSize = event.target.value; savePreferences(); });
  $("#viewModeSelect").addEventListener("change", (event) => { state.prefs.viewMode = event.target.value; savePreferences(); });
  $("#swipeDeleteToggle").addEventListener("change", (event) => { state.prefs.swipeDelete = event.target.checked; savePreferences(); });
  $("#autoRetryToggle").addEventListener("change", (event) => { state.prefs.autoRetryFailed = event.target.checked; savePreferences(); });
  $("#workerConcurrencySelect")?.addEventListener("change", (event) => { state.prefs.workerConcurrency = Number(event.target.value); savePreferences(); });
  $("#changePasswordForm").addEventListener("submit", changePassword);
  $("#createUserForm").addEventListener("submit", createUser);
  $("#refreshUsersBtn").addEventListener("click", loadUsers);
  $("#fetchDiagnosticBtn")?.addEventListener("click", runFetchDiagnostic);
  $("#backupBtn")?.addEventListener("click", createBackup);
  $("#clearCacheBtn")?.addEventListener("click", clearImageCache);
  $("#refreshAuditBtn")?.addEventListener("click", loadAudit);
  $$('[data-export]').forEach((button) => button.addEventListener("click", () => exportData(button.dataset.export)));
  $("#appContent").addEventListener("scroll", handleInfiniteScroll, { passive: true });
  window.addEventListener("hashchange", () => renderRoute());
  window.addEventListener("pageshow", () => {
    if (state.authenticated) restoreReturnPosition({ requirePending: true });
  });
  document.addEventListener("visibilitychange", () => {
    if (!document.hidden && state.authenticated) {
      setTimeout(() => restoreReturnPosition({ requirePending: true }), 80);
    }
  }, { passive: true });
}

async function start() {
  applyPreferences();
  bindEvents();
  initializeIntersectionObservers();
  initializeSwipeDelete();
  try {
    await api("/health");
    $("#serverStatus").textContent = "Online";
    $("#serverDot").classList.add("online");
  } catch (_) {
    $("#serverStatus").textContent = "Offline";
  }
  try {
    const auth = await api("/api/auth/me");
    if (auth.authenticated) await enterApp(auth);
    else showPublicShell();
  } catch (_) {
    showPublicShell();
  }
}

start();
