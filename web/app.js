/* MathProver frontend. Vanilla JS, no build step. */
"use strict";

const API = (window.MATHPROVER_API_BASE || "").replace(/\/+$/, "");
const LS_JOBS = "mathprover.jobs";
const $ = (id) => document.getElementById(id);

const state = {
  mode: "nl",
  nl: "",
  jobId: null,
  revision: 0,
  timer: null,
  unchanged: 0,
};

/* ------------------------------------------------------------------ api */

class ApiError extends Error {
  constructor(code, message, details, status) {
    super(message);
    this.code = code;
    this.details = details || {};
    this.status = status;
  }
}

async function api(path, options = {}) {
  let response;
  try {
    response = await fetch(API + path, {
      ...options,
      headers: { "Content-Type": "application/json", ...(options.headers || {}) },
    });
  } catch (err) {
    throw new ApiError("network", "Cannot reach the prover server. It may be offline.", {}, 0);
  }
  if (response.status === 304) return { notModified: true };
  const text = await response.text();
  let body = {};
  try { body = text ? JSON.parse(text) : {}; } catch (_) { /* non-JSON */ }

  if (!response.ok) {
    const e = body.error || {};
    throw new ApiError(e.code || "http_" + response.status,
      e.message || `Request failed (${response.status}).`, e.details, response.status);
  }
  return body;
}

/* --------------------------------------------------------------- helpers */

const esc = (s) => String(s == null ? "" : s)
  .replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");

function show(screen) {
  document.body.className = "screen-" + screen;
  window.scrollTo(0, 0);
}

function ago(ts) {
  if (!ts) return "";
  const s = Math.max(0, Math.floor(Date.now() / 1000 - ts));
  if (s < 60) return s + "s ago";
  if (s < 3600) return Math.floor(s / 60) + "m ago";
  if (s < 86400) return Math.floor(s / 3600) + "h ago";
  return Math.floor(s / 86400) + "d ago";
}

function duration(s) {
  s = Math.floor(s || 0);
  return s < 60 ? s + "s" : Math.floor(s / 60) + "m " + (s % 60) + "s";
}

function renderErrors(node, errors, warnings) {
  const items = [];
  (errors || []).forEach((e) => items.push({ ...e, severity: "error" }));
  (warnings || []).forEach((w) => items.push({ ...w, severity: "warning" }));
  if (!items.length) { node.innerHTML = ""; return; }
  node.innerHTML = items.map((e) => {
    const loc = e.line != null ? `line ${e.line}:${e.column ?? 0}` : "";
    return `<div class="err ${e.severity === "warning" ? "warn" : ""}">` +
      (loc ? `<span class="loc">${esc(loc)}</span>  ` : "") + esc(e.message) + `</div>`;
  }).join("");
}

function banner(node, kind, html) {
  node.className = "banner " + kind;
  node.innerHTML = html;
  node.classList.remove("hidden");
}

function handleError(node, err) {
  if (err.code === "rate_limited") {
    const mins = Math.max(1, Math.round((err.details.retry_after_seconds || 60) / 60));
    banner(node, "warn", `${esc(err.message)} <br><span class="small">` +
      `Limit: ${err.details.limit} per hour. Your text is saved — try again in ${mins} minute(s).</span>`);
  } else if (err.code === "checker_warming") {
    banner(node, "warn", "The Lean environment is still starting up (this takes a couple of " +
      "minutes after a restart). Please try again shortly.");
  } else {
    banner(node, "error", esc(err.message));
  }
  refreshLimits();
}

/* --------------------------------------------------------- local job list */

const localJobs = {
  read() {
    try { return JSON.parse(localStorage.getItem(LS_JOBS) || "[]"); } catch (_) { return []; }
  },
  add(id, title, mode) {
    const jobs = localJobs.read().filter((j) => j.id !== id);
    jobs.unshift({ id, title, mode, created_at: Date.now() / 1000 });
    localStorage.setItem(LS_JOBS, JSON.stringify(jobs.slice(0, 40)));
  },
};

/* ------------------------------------------------------------- limits bar */

async function refreshLimits() {
  try {
    const l = await api("/api/limits");
    const j = l.job || {};
    $("limits").textContent =
      `${j.remaining ?? "?"} of ${j.limit ?? "?"} submissions left this hour`;
    $("btn-solve").dataset.exhausted = (j.remaining === 0) ? "1" : "";
  } catch (_) { $("limits").textContent = ""; }
}

/* ---------------------------------------------------------------- sidebar */

async function refreshJobList() {
  let server = [];
  try {
    server = (await api("/api/jobs")).jobs || [];
  } catch (_) { /* offline: fall back to local memory only */ }

  const known = new Set(server.map((j) => j.id));
  const merged = server.slice();
  // Anything we remember but the server does not: it aged out, or the server
  // restarted (job state is in memory only), or our IP changed.
  localJobs.read().forEach((j) => {
    if (!known.has(j.id)) merged.push({ ...j, phase: "expired", verdict: null });
  });

  const list = $("joblist");
  $("jobs-empty").classList.toggle("hidden", merged.length > 0);
  list.innerHTML = merged.map((j) => `
    <li data-id="${esc(j.id)}">
      <div class="jt"><span class="dot ${esc(j.phase)}"></span>${esc(j.title || j.id)}</div>
      <div class="jm"><span>${esc(j.mode === "nl" ? "natural language" : "Lean")}</span>
        <span>${esc(j.phase)}${j.created_at ? " · " + ago(j.created_at) : ""}</span></div>
    </li>`).join("");

  list.querySelectorAll("li").forEach((li) => {
    li.onclick = () => openJob(li.dataset.id);
  });
}

/* ------------------------------------------------------------------ home */

function setMode(mode) {
  state.mode = mode;
  document.querySelectorAll(".tab").forEach((t) =>
    t.classList.toggle("active", t.dataset.mode === mode));
  $("pane-nl").classList.toggle("hidden", mode !== "nl");
  $("pane-lean").classList.toggle("hidden", mode !== "lean");
  $("home-error").classList.add("hidden");
}

async function doFormalize() {
  const nl = $("input-nl").value.trim();
  if (!nl) return;
  state.nl = nl;
  const btn = $("btn-formalize");
  btn.disabled = true;
  btn.textContent = "Converting…";
  $("home-error").classList.add("hidden");

  try {
    const r = await api("/api/formalize", { method: "POST", body: JSON.stringify({ nl }) });
    $("review-nl").textContent = nl;
    $("review-restatement").textContent = r.informal_restatement || "(none provided)";
    $("review-lean").value = r.lean;
    $("col-original").classList.remove("hidden");
    $("restatement-head").classList.remove("hidden");
    $("btn-regenerate").classList.remove("hidden");
    $("review-title").textContent = "Confirm the Lean translation";
    $("review-sub").textContent = "Check that this says the same thing as your problem. " +
      "Edit it if not — the prover proves exactly what is written here, not what you meant.";
    applyCheck({ ok: r.compiles, errors: r.errors, warnings: [] });
    if (r.repaired) {
      banner($("review-error"), "warn",
        "The first translation did not compile, so it was automatically revised. Read it carefully.");
    }
    show("review");
  } catch (err) {
    handleError($("home-error"), err);
  } finally {
    btn.disabled = false;
    btn.textContent = "Convert to Lean →";
  }
}

async function doCheckLean() {
  const lean = $("input-lean").value.trim();
  if (!lean) return;
  state.nl = "";
  $("review-lean").value = lean;
  $("col-original").classList.add("hidden");
  $("btn-regenerate").classList.add("hidden");
  $("review-title").textContent = "Fix the Lean statement";
  $("review-sub").textContent =
    "The statement must compile before it can be queued. `sorry` is expected — that is what gets proved.";
  show("review");
  await recheck();
}

/* ---------------------------------------------------------------- review */

function applyCheck(result) {
  const badge = $("review-badge");
  const solve = $("btn-solve");
  if (result.ok) {
    badge.className = "badge ok";
    badge.textContent = "compiles";
    solve.disabled = false;
  } else {
    badge.className = "badge bad";
    badge.textContent = "does not compile";
    solve.disabled = true;
  }
  renderErrors($("review-errors"), result.errors,
    (result.warnings || []).filter((w) => !/uses 'sorry'/.test(w.message || "")));

  (result.rejections || []).forEach((r) => {
    banner($("review-error"), "error", esc(r.message));
    solve.disabled = true;
  });
}

async function recheck() {
  const lean = $("review-lean").value.trim();
  if (!lean) return;
  const badge = $("review-badge");
  badge.className = "badge wait";
  badge.textContent = "checking…";
  $("review-error").classList.add("hidden");
  try {
    const r = await api("/api/lean/check", { method: "POST", body: JSON.stringify({ lean }) });
    applyCheck(r);
  } catch (err) {
    badge.className = "badge bad";
    badge.textContent = "check failed";
    handleError($("review-error"), err);
  }
}

async function doSolve() {
  const lean = $("review-lean").value.trim();
  const btn = $("btn-solve");
  btn.disabled = true;
  btn.textContent = "Submitting…";
  $("review-error").classList.add("hidden");

  const payload = { mode: state.nl ? "nl" : "lean", lean };
  if (state.nl) payload.nl = state.nl;

  try {
    const job = await api("/api/jobs", { method: "POST", body: JSON.stringify(payload) });
    localJobs.add(job.id, job.title, job.mode);
    refreshLimits();
    openJob(job.id, job);
  } catch (err) {
    if (err.code === "compile_error") {
      applyCheck({ ok: false, errors: err.details.errors || [] });
    }
    handleError($("review-error"), err);
    btn.disabled = false;
  } finally {
    btn.textContent = "Confirm & solve";
  }
}

/* ------------------------------------------------------------------- job */

const PHASE_TEXT = {
  queued: "Waiting for a free slot.",
  preparing: "Setting up the workspace.",
  checking: "Compiling your statement into a reference specification — this takes about a minute.",
  proving: "The prover is working. Each attempt loads Mathlib, so the first iteration is slow.",
  verifying: "Checking the proof with SafeVerify.",
  succeeded: "Proved and verified.",
  failed: "No verified proof was found.",
  timeout: "Ran out of time.",
  cancelled: "Cancelled.",
};

function openJob(id, seed) {
  stopPolling();
  state.jobId = id;
  state.revision = 0;
  state.unchanged = 0;
  history.replaceState(null, "", "?job=" + encodeURIComponent(id));
  show("job");

  $("job-lean").textContent = "waiting for the first attempt…";
  $("job-log").innerHTML = "";
  $("job-banner").classList.add("hidden");
  $("job-errors-wrap").classList.add("hidden");
  $("job-nl-wrap").classList.add("hidden");
  $("btn-download").classList.add("hidden");

  if (seed) renderJob(seed);
  poll();
}

function stopPolling() {
  if (state.timer) { clearTimeout(state.timer); state.timer = null; }
}

function scheduleNext(phase) {
  const base = (phase === "proving" || phase === "verifying") ? 2000 : 3000;
  const slow = state.unchanged > 10 ? 2 : 1;   // back off during long model turns
  const jitter = 0.9 + Math.random() * 0.2;
  state.timer = setTimeout(poll, base * slow * jitter);
}

async function poll() {
  if (!state.jobId) return;
  try {
    const r = await api(`/api/jobs/${encodeURIComponent(state.jobId)}?since=${state.revision}`);
    if (r.notModified) {
      state.unchanged++;
      scheduleNext($("job-phase").textContent);
      return;
    }
    state.unchanged = 0;
    state.revision = r.revision || 0;
    renderJob(r);
    if (["succeeded", "failed", "timeout", "cancelled"].includes(r.phase)) {
      refreshJobList();
      return;   // terminal: stop polling
    }
    scheduleNext(r.phase);
  } catch (err) {
    if (err.code === "job_unknown") {
      banner($("job-banner"), "error", esc(err.message));
      $("job-phase").textContent = "expired";
      refreshJobList();
      return;
    }
    state.unchanged++;
    scheduleNext("queued");
  }
}

function renderJob(j) {
  $("job-title").textContent = j.title || j.id;
  $("job-meta").textContent =
    `${j.mode === "nl" ? "natural language" : "Lean"} · submitted ${ago(j.created_at)}`;
  $("job-phase").textContent = j.phase;
  $("job-phase").className = "pill " + j.phase;

  const stats = [];
  if (j.queue_position) stats.push(`<span>position <b>${j.queue_position}</b> in queue</span>`);
  stats.push(`<span>elapsed <b>${duration(j.elapsed_seconds)}</b> of ${duration(j.time_budget_seconds)}</span>`);
  if (j.iteration) stats.push(`<span>iteration <b>${j.iteration}</b></span>`);
  if (j.blocks_total) stats.push(`<span><b>${j.blocks_closed}</b> of <b>${j.blocks_total}</b> blocks closed</span>`);
  (j.workers || []).forEach((w) => stats.push(
    `<span>worker ${w.worker_id ?? "?"} <b>${w.alive === false ? "done" : "iter " + (w.iteration || 0)}</b></span>`));
  $("job-stats").innerHTML = stats.join("");

  const pct = j.blocks_total
    ? Math.round(100 * j.blocks_closed / j.blocks_total)
    : Math.min(95, Math.round(100 * (j.elapsed_seconds || 0) / (j.time_budget_seconds || 1)));
  $("job-bar").style.width = (j.phase === "succeeded" ? 100 : pct) + "%";

  if (j.current_lean) $("job-lean").textContent = j.current_lean;
  if (j.current_nl) {
    $("job-nl-wrap").classList.remove("hidden");
    $("job-nl").textContent = j.current_nl;
  }

  const errs = (j.errors || []).filter((e) => e.severity === "error");
  $("job-errors-wrap").classList.toggle("hidden", errs.length === 0);
  if (errs.length) renderErrors($("job-errors"), errs, []);

  $("job-log").innerHTML = (j.log_tail || []).slice().reverse().map((e) => {
    const t = e.ts ? new Date(e.ts * 1000).toLocaleTimeString() : "";
    return `<li><span class="t">${esc(t)}</span>${esc(e.summary || e.event)}</li>`;
  }).join("");

  const terminal = ["succeeded", "failed", "timeout", "cancelled"].includes(j.phase);
  $("btn-cancel").classList.toggle("hidden", terminal);

  if (j.phase === "succeeded") {
    banner($("job-banner"), "good",
      "<b>Proved.</b> SafeVerify confirmed the proof matches your statement and uses only the " +
      "standard axioms. Note this verifies the proof against the statement you submitted — " +
      "it does not judge whether the statement itself is the one you meant.");
    $("btn-download").classList.remove("hidden");
  } else if (terminal) {
    const sv = j.safeverify;
    let extra = "";
    if (sv && sv.success === false) extra = `<br><span class="small">SafeVerify: ${esc(sv.status)} — ${esc(sv.message || "")}</span>`;
    banner($("job-banner"), "error",
      esc(j.error_message || PHASE_TEXT[j.phase] || "Finished without a proof.") + extra);
  } else {
    banner($("job-banner"), "", esc(PHASE_TEXT[j.phase] || ""));
  }
}

async function doCancel() {
  if (!state.jobId) return;
  $("btn-cancel").disabled = true;
  try {
    await api(`/api/jobs/${encodeURIComponent(state.jobId)}/cancel`, { method: "POST" });
    setTimeout(poll, 300);
  } catch (err) { handleError($("job-banner"), err); }
  finally { $("btn-cancel").disabled = false; }
}

function doDownload() {
  const text = $("job-lean").textContent || "";
  const blob = new Blob([text], { type: "text/plain" });
  const a = document.createElement("a");
  a.href = URL.createObjectURL(blob);
  a.download = ($("job-title").textContent || "proof") + ".lean";
  a.click();
  URL.revokeObjectURL(a.href);
}

/* ------------------------------------------------------------------ init */

document.querySelectorAll(".tab").forEach((t) => { t.onclick = () => setMode(t.dataset.mode); });
$("btn-formalize").onclick = doFormalize;
$("btn-check").onclick = doCheckLean;
$("btn-recheck").onclick = recheck;
$("btn-regenerate").onclick = doFormalize;
$("btn-solve").onclick = doSolve;
$("btn-cancel").onclick = doCancel;
$("btn-download").onclick = doDownload;
$("btn-back").onclick = () => { stopPolling(); show("home"); };
$("btn-new").onclick = () => {
  stopPolling(); state.jobId = null;
  history.replaceState(null, "", location.pathname);
  show("home");
};
$("brand").onclick = () => { stopPolling(); show("home"); };

refreshLimits();
refreshJobList();
setInterval(refreshJobList, 30000);

const deepLink = new URLSearchParams(location.search).get("job");
if (deepLink) openJob(deepLink); else show("home");
