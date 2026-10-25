/* RFA Tutors reader, built on Mozilla pdf.js (Apache-2.0, see lib/LICENSE.txt).

   Deliberately written as a plain ES5 script rather than a module: it has to
   start on old iPads, old Android WebViews and locked-down desktops inside
   an LMS iframe, where ES modules, optional chaining and fetch() are not all
   safe bets. Everything here uses var, function, XMLHttpRequest and feature
   detection.

   The page never contains selectable text. Search, read-aloud and the answer
   hotspots all work from geometry captured once from the PDF, and every
   overlay is positioned in percentages so zooming never re-measures. */

(function () {
'use strict';

var CFG = window.RFA_CONFIG || {};
function cfg(name, fallback) { return CFG[name] === undefined ? fallback : CFG[name]; }

var SRC        = cfg('src', 'data/book.pdf');
var KEY        = cfg('key', '');
var QUIZ_ON    = cfg('quiz', true);
var QUIZ_START = cfg('quizStartOn', true);
var GATE       = cfg('gateReveal', true);
var MASTERY    = cfg('mastery', 80);
var BLUR_BLUR  = cfg('blurOnBlur', false);
var BLOCK_PRNT = cfg('blockPrint', true);
var SPEAK_ON   = cfg('readAloud', true);
var THUMBS_ON  = cfg('thumbs', true);
var SEND_INTER = cfg('reportInteractions', true);
var TIMER_ON   = cfg('timer', true);
var EXAM_SECS  = cfg('examSeconds', 0);      /* 0 = derive from the question count */
var PER_Q_SECS = cfg('secondsPerQuestion', 90);
var TIMER_AUTO = cfg('timerAutostart', false);
var AUTO_SUBMIT= cfg('autoSubmit', false);
var ANALYSIS_ON= cfg('analysis', true);
var MODULES    = cfg('modules', []) || [];
var DWELL_MS   = Math.max(0, cfg('dwellSeconds', 0)) * 1000;
var PAGE_CAP   = Math.max(0, cfg('pageCap', 0));
var SHORT_TOC  = cfg('shortToc', false);
var STORE_KEY  = 'rfa.' + (cfg('id', 'COURSE'));

var GAP = 18;
var MIN_SCALE = 0.35;
var MAX_SCALE = 5;
var THEMES = ['paper'];
var THEME_NAMES = ['Paper'];
var MASK_L = 0.055, MASK_R = 0.945;
var SUSPEND_BUDGET = 3800;          /* cmi.suspend_data is capped at 4096 */

/* ------------------------------------------------------------- helpers */

function el(id) { return document.getElementById(id); }
function on(node, evt, fn, opts) { if (node) { node.addEventListener(evt, fn, opts || false); } }
function make(tag, cls) { var n = document.createElement(tag); if (cls) { n.className = cls; } return n; }
function clear(node) { while (node && node.firstChild) { node.removeChild(node.firstChild); } }
function pct(v) { return (v * 100) + '%'; }
function clamp(v, lo, hi) { return v < lo ? lo : (v > hi ? hi : v); }
function esc(s) {
  return String(s).replace(/[&<>"]/g, function (c) {
    return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c];
  });
}
function now() { return (new Date()).getTime(); }

var toastTimer = null;
function toast(msg, ms) {
  var t = el('toast');
  if (!t) { return; }
  t.textContent = msg;
  t.hidden = false;
  clearTimeout(toastTimer);
  toastTimer = setTimeout(function () { t.hidden = true; }, ms || 1800);
}

/* ------------------------------------------------- device / connection */

var ua = navigator.userAgent || '';
var isPhone = Math.min(screen.width || 1024, screen.height || 768) <= 700 || /Mobi|Android|iPhone/i.test(ua);
var conn = navigator.connection || navigator.mozConnection || navigator.webkitConnection || null;
var slowLink = !!(conn && (conn.saveData === true ||
  /(^|-)(2g|slow-2g)$/.test(String(conn.effectiveType || ''))));
var lowPower = (navigator.deviceMemory && navigator.deviceMemory <= 2) ||
               (navigator.hardwareConcurrency && navigator.hardwareConcurrency <= 2);

/* Render quality adapts itself to the device and connection. */
function lite() { return slowLink || lowPower || isPhone; }
function dprCap() { return lite() ? 1 : 2; }
function pixelCap() { return lite() ? 2600000 : (isPhone ? 4200000 : 12000000); }
function liveLimit() { return lite() ? 3 : 7; }

/* ----------------------------------------------------------- app state */

var dom = {};
var state = {
  doc: null, total: 0, current: 1,
  fit: 'width', scale: null,
  pages: [], seen: {}, seenCount: 0,
  marks: [],
  lines: {}, plain: {},
  outline: [], masks: [], qs: [], qByN: {},
  quiz: false, theme: 0,
  analysed: 0, done: false, completed: false,
  speaking: false,
  interCount: 0, started: now(),
  locked: false,                      /* the timed attempt is over */
  capped: false,                      /* this session's page limit is spent */
  sessionNew: 0, dwellFrom: 0, lastTurn: 0,
  timer: { total: 0, elapsed: 0, running: false, at: 0, expired: false, over: false, started: false, shown: false }
};

/* ---------------------------------------------------------------- SCORM */

var live = false;

function packSeen() {
  var bytes = [], i, n;
  for (n = 1; n <= state.total; n++) {
    if (state.seen[n]) {
      i = (n - 1) >> 3;
      while (bytes.length <= i) { bytes.push(0); }
      bytes[i] |= 1 << ((n - 1) & 7);
    }
  }
  var s = '';
  for (i = 0; i < bytes.length; i++) { s += String.fromCharCode(bytes[i]); }
  try { return window.btoa(s); } catch (e) { return ''; }
}

function unpackSeen(b64) {
  if (!b64) { return; }
  var s;
  try { s = window.atob(b64); } catch (e) { return; }
  for (var i = 0; i < s.length; i++) {
    var byte = s.charCodeAt(i);
    for (var bit = 0; bit < 8; bit++) {
      if (byte & (1 << bit)) { markSeen(i * 8 + bit + 1, true); }
    }
  }
}

function markSeen(n, quiet) {
  if (n < 1 || (state.total && n > state.total)) { return; }
  if (state.seen[n]) { return; }
  state.seen[n] = 1;
  state.seenCount++;
  if (quiet) { return; }                      /* restored from a previous attempt */
  state.sessionNew++;
  if (PAGE_CAP && state.sessionNew > PAGE_CAP) { capSession(); }
  drawProgress();
}

function packState() {
  var data = {
    v: 2,
    p: state.current,
    z: state.fit || state.scale,
    t: state.theme,
    qz: state.quiz ? 1 : 0,
    s: packSeen(),
    b: [],
    a: {}, f: [], ms: {},
    tm: TIMER_ON ? [Math.round(timerElapsed()), state.timer.expired ? 1 : 0,
                    state.locked ? 1 : 0, state.timer.started ? 1 : 0, 1] : null
  };
  var g = RFA_GUARD.pack(), k;
  for (k in g) { if (g.hasOwnProperty(k)) { data[k] = g[k]; } }
  var i, q;
  for (i = 0; i < state.marks.length; i++) { data.b.push([state.marks[i].page, state.marks[i].at]); }
  for (i = 0; i < state.qs.length; i++) {
    q = state.qs[i];
    if (q.ans) { data.a[q.n] = q.ans; }
    if (q.flag) { data.f.push(q.n); }
    if (q.ms) { data.ms[q.n] = Math.round(q.ms / 1000); }
  }
  return data;
}

/* The LMS field is small: per-question timings, then bookmarks, are dropped
   before anything that carries progress. */
function suspendPayload() {
  var core = packState();
  var order = ['g', 'ip', 'ms', 'dy', 'dv', 'v'];
  var s = JSON.stringify(core), i;
  if (s.length <= SUSPEND_BUDGET) { return s; }
  for (i = 0; i < order.length; i++) {
    delete core[order[i]];
    s = JSON.stringify(core);
    if (s.length <= SUSPEND_BUDGET) { return s; }
  }
  core.b = [];                                /* bookmarks before answers */
  s = JSON.stringify(core);
  if (s.length <= SUSPEND_BUDGET) { return s; }
  return s.slice(0, SUSPEND_BUDGET);
}

var saveTimer = null;

function flush() {
  clearTimeout(saveTimer);
  saveTimer = null;
  try { window.localStorage.setItem(STORE_KEY, JSON.stringify(packState())); } catch (e) { /* private mode */ }
  if (live) {
    SCORM.setProgress(suspendPayload());
    reportOutcome();
  }
}

/* Writes are batched, but never left pending: the page can be closed, hidden
   or navigated away from at any moment inside an LMS frame. */
function save() {
  clearTimeout(saveTimer);
  saveTimer = setTimeout(flush, 500);
}

function readStore() {
  var lms = null, loc = null;
  if (live) { try { lms = JSON.parse(SCORM.getProgress() || 'null'); } catch (e) { lms = null; } }
  try { loc = JSON.parse(window.localStorage.getItem(STORE_KEY) || 'null'); } catch (e) { loc = null; }
  if (!lms) { return loc; }
  if (loc) {
  }
  return lms;
}

function restore() {
  var s = readStore();
  if (!s) { return; }
  var i;
  if (typeof s.p === 'number') { state.current = s.p; }
  if (s.z === 'width' || s.z === 'page') { state.fit = s.z; }
  else if (typeof s.z === 'number') { state.fit = null; state.scale = s.z; }
  if (typeof s.t === 'number') { state.theme = s.t % THEMES.length; }
  /* only override the default when this learner has a saved preference */
  if (typeof s.qz !== 'undefined') { state.quiz = QUIZ_ON && !!s.qz; }
  if (s.b && s.b.length) {
    for (i = 0; i < s.b.length; i++) { state.marks.push({ page: s.b[i][0], at: s.b[i][1] }); }
  }
  RFA_GUARD.restore(s);
  state.restoredSeen = s.s;
  state.restoredAns = s.a || {};
  state.restoredFlags = s.f || [];
  state.restoredMs = s.ms || {};
  if (s.tm && s.tm.length) {
    /* The clock always comes back paused. An LMS can close a SCO without
       warning, and nobody should lose minutes to a dropped connection. */
    state.restoredTimer = { value: s.tm[0], expired: !!s.tm[1], locked: !!s.tm[2], started: !!s.tm[3], sw: !!s.tm[4] };
  }
}

/* ------------------------------------------- dwell and the page limit

   Two pieces of friction against somebody photographing a whole book in
   four minutes. Neither stops a determined person; both turn it into an
   hour of tedium, which is the most this side of the screen can do. */

function dwellLeft() {
  if (!DWELL_MS || !state.dwellFrom) { return 0; }
  var left = DWELL_MS - (now() - state.dwellFrom);
  return left > 0 ? left : 0;
}

function dwellBlock() {
  var left = dwellLeft();
  if (!left) { return false; }
  toast('A moment more on this page \u2014 ' + Math.ceil(left / 1000) + 's.', 1200);
  return true;
}

/* The scroll is pinned at the FOOT of the current page rather than the top,
   so the whole of it stays readable and only the next one is out of reach. */
function clampScroll() {
  if (!DWELL_MS || !dwellLeft() || !state.pages.length) { return; }
  var p = state.pages[state.current - 1];
  if (!p) { return; }
  var foot = p.wrap.offsetTop + p.wrap.offsetHeight - dom.stage.clientHeight;
  if (dom.stage.scrollTop > foot) { dom.stage.scrollTop = foot > 0 ? foot : 0; }
}

function capSession() {
  if (state.capped) { return; }
  state.capped = true;
  RFA_GUARD.lock(true);
  RFA_GUARD.shield('You have reached this session\u2019s page limit. Close the course and open ' +
                   'it again to carry on \u2014 your place, answers and bookmarks are saved.', 0);
  flush();
}

function quizTotal() {
  var n = 0;
  for (var i = 0; i < state.qs.length; i++) { if (state.qs[i].correct) { n++; } }
  return n;
}

function quizScore() {
  var right = 0, answered = 0;
  for (var i = 0; i < state.qs.length; i++) {
    var q = state.qs[i];
    if (!q.correct || !q.ans) { continue; }
    answered++;
    if (q.ans === q.correct) { right++; }
  }
  return { right: right, answered: answered, total: quizTotal() };
}

function reportOutcome(force) {
  if (!live) { return; }
  var sc = quizScore();
  if (QUIZ_ON && sc.total) {
    var pctScore = Math.round((sc.right / sc.total) * 100);
    SCORM.setScore(pctScore, 0, 100);
    if (sc.answered >= sc.total || force) {
      SCORM.setStatus(pctScore >= MASTERY ? 'passed' : 'failed');
    }
    return;
  }
  if (!state.completed && state.total && state.seenCount >= state.total) {
    state.completed = true;
    SCORM.complete();
  }
}

/* ------------------------------------------------------------- geometry */

function stageBox() {
  return { w: dom.stage.clientWidth - GAP, h: dom.stage.clientHeight - GAP };
}

function scaleFor(base) {
  var box = stageBox();
  if (state.fit === 'width') { return box.w / base.width; }
  if (state.fit === 'page') { return Math.min(box.w / base.width, box.h / base.height); }
  return state.scale || 1;
}

function effectiveScale() { return state.pages[0] ? scaleFor(state.pages[0].base) : 1; }

function showZoom() {
  dom.zoomLevel.textContent = state.fit === 'width' ? 'Fit width'
    : state.fit === 'page' ? 'Fit page'
    : Math.round((state.scale || 1) * 100) + '%';
}

/* --------------------------------------------------------------- render */

var renderOrder = [];

function sizePage(p) {
  var s = scaleFor(p.base);
  p.wrap.style.width = Math.floor(p.base.width * s) + 'px';
  p.wrap.style.height = Math.floor(p.base.height * s) + 'px';
  return s;
}

function layout() {
  for (var i = 0; i < state.pages.length; i++) {
    var p = state.pages[i];
    sizePage(p);
    if (p.rendered) { p.stale = true; }
  }
  showZoom();
  renderVisible();
}

function evict() {
  var limit = liveLimit();
  while (renderOrder.length > limit) {
    var idx = renderOrder.shift();
    var p = state.pages[idx];
    if (!p || Math.abs(idx + 1 - state.current) <= 1) { continue; }
    if (p.task) { try { p.task.cancel(); } catch (e) { /* already done */ } p.task = null; }
    if (p.canvas) { p.canvas.width = 0; p.canvas.height = 0; }
    p.rendered = false;
    p.stale = false;
    if (p.ph) { p.ph.hidden = false; }
  }
}

function renderPage(i) {
  var p = state.pages[i];
  if (!p || p.rendering || (p.rendered && !p.stale)) { return null; }
  p.rendering = true;
  return state.doc.getPage(i + 1).then(function (page) {
    var base = page.getViewport({ scale: 1 });
    if (Math.abs(base.width - p.base.width) > 1 || Math.abs(base.height - p.base.height) > 1) {
      p.base = { width: base.width, height: base.height };
      sizePage(p);
    }
    var css = scaleFor(p.base);
    var dpr = Math.min(window.devicePixelRatio || 1, dprCap());
    var w = Math.floor(p.base.width * css * dpr);
    var h = Math.floor(p.base.height * css * dpr);
    var area = w * h;
    var capped = pixelCap();
    if (area > capped) {
      var k = Math.sqrt(capped / area);
      dpr = Math.max(0.6, dpr * k);
      w = Math.floor(p.base.width * css * dpr);
      h = Math.floor(p.base.height * css * dpr);
    }
    p.canvas.width = w;
    p.canvas.height = h;
    var ctx = p.canvas.getContext('2d', { alpha: false });
    p.task = page.render({
      canvasContext: ctx,
      viewport: page.getViewport({ scale: css * dpr }),
      intent: 'display'
    });
    return p.task.promise.then(function () {
      p.task = null;
      p.rendered = true;
      p.stale = false;
      if (p.ph) { p.ph.hidden = true; }
      renderOrder.push(i);
      evict();
    });
  })['catch'](function (e) {
    if (e && e.name === 'RenderingCancelledException') { return; }
    if (window.console) { console.error('page ' + (i + 1) + ' failed', e); }
  }).then(function () { p.rendering = false; });
}

function renderVisible() {
  if (!state.doc) { return; }
  var pad = lite() ? 200 : 500;
  var top = dom.stage.scrollTop - pad;
  var bottom = dom.stage.scrollTop + dom.stage.clientHeight + pad;
  for (var i = 0; i < state.pages.length; i++) {
    var p = state.pages[i];
    var y = p.wrap.offsetTop;
    if (y + p.wrap.offsetHeight > top && y < bottom) { renderPage(i); }
  }
}

/* ----------------------------------------------------------- navigation */

function goTo(n, smooth, fraction) {
  if (state.capped && n !== state.current) { return; }
  if (DWELL_MS && n > state.current && dwellBlock()) { return; }
  var i = clamp(n, 1, state.total || 1) - 1;
  var p = state.pages[i];
  if (!p) { return; }
  var offset = (fraction === undefined || fraction === null)
    ? -6
    : Math.max(0, p.wrap.offsetHeight * fraction - 40);
  var target = p.wrap.offsetTop + offset;
  if (smooth === false || !dom.stage.scrollTo) { dom.stage.scrollTop = target; }
  else {
    try { dom.stage.scrollTo({ top: target, behavior: 'smooth' }); }
    catch (e) { dom.stage.scrollTop = target; }
  }
  setCurrent(i + 1);
}

function setCurrent(n) {
  var changed = n !== state.current;
  var fresh = !state.seen[n];
  state.current = n;
  dom.pageInput.value = String(n);
  markSeen(n);
  dom.bookmarkBtn.classList.toggle('on', hasMark(n));
  if (changed) {
    var gap = now() - state.lastTurn;
    if (state.lastTurn && gap < 1200) { RFA_GUARD.note('fast'); }
    state.lastTurn = now();
    state.dwellFrom = now();
    RFA_GUARD.at(state.current, state.seenCount);
    markThumb();
    markChips();
    startTiming();
  }
  if (fresh || changed) { drawProgress(); save(); }
}

function drawProgress() {
  var p = state.total ? Math.round((state.seenCount / state.total) * 100) : 0;
  dom.progress.style.width = p + '%';
}

function trackScroll() {
  var top = dom.stage.scrollTop;
  var bottom = top + dom.stage.clientHeight;
  var mid = top + dom.stage.clientHeight * 0.35;
  var best = 1;
  for (var i = 0; i < state.pages.length; i++) {
    var w = state.pages[i].wrap;
    if (w.offsetTop <= mid) { best = i + 1; }
    /* anything actually on screen counts as read, so a learner who scrolls
       quickly is not punished with a stuck progress bar */
    if (w.offsetTop < bottom && w.offsetTop + w.offsetHeight > top) { markSeen(i + 1); }
  }
  setCurrent(best);
  renderVisible();
}

/* --------------------------------------------- document analysis (lazy) */

/* Group the raw text runs into visual lines. This is what makes "Q3." in its
   own styled run join up with the stem beside it, and what gives the answer
   options a box to sit under. */
function toLines(items, vh) {
  var raw = [], i, it;
  for (i = 0; i < items.length; i++) {
    it = items[i];
    if (!it.str || !it.str.replace(/\s/g, '')) { continue; }
    var h = it.height || 10;
    var x = it.transform[4];
    var y = vh - it.transform[5];        /* baseline, measured from the top */
    raw.push({ s: it.str, x: x, y: y, top: y - h, h: h, w: it.width || 0 });
  }
  raw.sort(function (a, b) { return (a.top - b.top) || (a.x - b.x); });

  var lines = [], cur = null;
  for (i = 0; i < raw.length; i++) {
    var r = raw[i];
    if (cur && Math.abs(r.top - cur.top) <= Math.max(cur.h, r.h) * 0.6) {
      cur.parts.push(r);
      cur.top = Math.min(cur.top, r.top);
      cur.h = Math.max(cur.h, r.h);
      cur.y = Math.max(cur.y, r.y);
    } else {
      if (cur) { lines.push(cur); }
      cur = { parts: [r], top: r.top, y: r.y, h: r.h };
    }
  }
  if (cur) { lines.push(cur); }

  for (i = 0; i < lines.length; i++) {
    var L = lines[i];
    L.parts.sort(function (a, b) { return a.x - b.x; });
    var text = '', x0 = 1e9, x1 = -1e9, k, part, prevEnd = null;
    for (k = 0; k < L.parts.length; k++) {
      part = L.parts[k];
      if (prevEnd !== null && part.x - prevEnd > part.h * 0.25 && !/\s$/.test(text)) { text += ' '; }
      text += part.s;
      prevEnd = part.x + part.w;
      if (part.x < x0) { x0 = part.x; }
      if (part.x + part.w > x1) { x1 = part.x + part.w; }
    }
    L.t = text.replace(/\s+/g, ' ').replace(/^\s+|\s+$/g, '');
    L.x = x0;
    L.w = Math.max(1, x1 - x0);
  }
  return lines;
}

var HEAD_RE = /^Q\s*(\d+)\s*[.):]\s*(.*)$/i;
var OPT_RE = /^\(?([A-E])\s*[.)]\s+(.+)$/;
var ANS_RE = /^Answer\s*[:\-–]?\s*\(?([A-E])\b/i;
var ANS_ANY_RE = /^Answer\s*[:\-–]/i;

var pending = null;    /* question carried across a page break */
var carryMask = false; /* an answer block ran off the foot of the last page */

function analysePage(i) {
  return state.doc.getPage(i + 1).then(function (page) {
    var vp = page.getViewport({ scale: 1 });
    return page.getTextContent().then(function (content) {
      var lines = toLines(content.items, vp.height);
      var plain = [], k;
      for (k = 0; k < lines.length; k++) { plain.push(lines[k].t); }
      state.plain[i] = plain.join(' ');
      state.lines[i] = [];
      for (k = 0; k < lines.length; k++) {
        state.lines[i].push({
          t: lines[k].t,
          x: lines[k].x / vp.width,
          y: lines[k].top / vp.height,
          w: lines[k].w / vp.width,
          h: Math.max(lines[k].h, 6) / vp.height
        });
      }

      var pageNo = i + 1;
      var heads = [];
      var FOOT = vp.height * 0.94;

      /* Pre-scan for headings so a mask can be capped at the next question,
         then walk the page once. Walking once is what keeps each mask tied to
         the question it belongs to rather than to the last one on the page. */
      for (k = 0; k < lines.length; k++) {
        if (HEAD_RE.test(lines[k].t)) { heads.push(lines[k].top); }
      }
      heads.sort(function (a, b) { return a - b; });

      /* An explanation that ran off the foot of the previous page carries on
         at the top of this one. Without this the tail of the answer sits in
         plain view on the next page while the first half is masked. */
      if (carryMask && pending) {
        var carryEnd = heads.length ? heads[0] - 2 : FOOT;
        var firstLine = lines.length ? lines[0].top : 0;
        if (carryEnd > firstLine) {
          var cm = {
            page: pageNo, top: Math.max(0, firstLine - 4) / vp.height,
            height: (carryEnd - Math.max(0, firstLine - 4)) / vp.height,
            q: pending.n
          };
          state.masks.push(cm);
          pending.masks.push(cm);
        }
      }
      carryMask = false;

      var lastY = 0;
      for (k = 0; k < lines.length; k++) {
        if (lines[k].y < FOOT && lines[k].y > lastY) { lastY = lines[k].y; }
      }

      for (k = 0; k < lines.length; k++) {
        var L = lines[k];
        var m = HEAD_RE.exec(L.t);
        if (m) {
          /* The contents list is the one place the document's own words still
             reach the DOM: a stem per heading, liftable in one line from the
             console. --short-toc trades the readable list for "Q1." alone. */
          var label = SHORT_TOC ? ('Q' + m[1] + '.')
                                : ('Q' + m[1] + '.' + (m[2] ? ' ' + m[2] : ''));
          if (label.length > 96) { label = label.slice(0, 93) + '...'; }
          heads.push(L.top);
          var q = {
            n: Number(m[1]), page: pageNo, ny: L.top / vp.height,
            label: label, opts: [], correct: '', ans: null, flag: false,
            ms: 0, t0: 0, masks: []
          };
          if (state.qByN[q.n]) {
            /* the same number seen twice (a running header, say): keep the first */
            pending = state.qByN[q.n];
            continue;
          }
          state.outline.push(q);
          state.qs.push(q);
          state.qByN[q.n] = q;
          pending = q;
          continue;
        }

        var om = OPT_RE.exec(L.t);
        if (om && pending && !pending.correct) {
          var exists = false;
          for (var z = 0; z < pending.opts.length; z++) {
            if (pending.opts[z].L === om[1]) { exists = true; break; }
          }
          if (!exists) {
            pending.opts.push({
              L: om[1], page: pageNo,
              x: MASK_L, y: (L.top - 2) / vp.height,
              w: MASK_R - MASK_L, h: Math.max(L.h + 5, 12) / vp.height
            });
          }
          continue;
        }

        if (!ANS_ANY_RE.test(L.t)) { continue; }

        var am = ANS_RE.exec(L.t);
        if (am && pending && !pending.correct) { pending.correct = am[1].toUpperCase(); }

        /* one mask per answer block: from this line down to the end of the
           block, capped at the next question heading and at the page foot */
        var top = L.top - 4;
        var limit = FOOT, hIdx;
        for (hIdx = 0; hIdx < heads.length; hIdx++) {
          if (heads[hIdx] > top + 2) { limit = Math.min(heads[hIdx], FOOT); break; }
        }
        var bottom = L.y;
        for (var j = k; j < lines.length; j++) {
          if (lines[j].top >= top && lines[j].y < limit) { bottom = Math.max(bottom, lines[j].y); }
        }
        var end = Math.min(bottom + 5, limit - 2);
        if (end > top) {
          var mask = {
            page: pageNo, top: top / vp.height, height: (end - top) / vp.height,
            q: pending ? pending.n : 0
          };
          state.masks.push(mask);
          if (pending) { pending.masks.push(mask); }
        }
        /* no heading follows and the block runs to the last line on the page:
           the explanation continues overleaf */
        if (limit >= FOOT && bottom >= lastY - 1) { carryMask = true; }
      }
      state.analysed = i + 1;
    });
  })['catch'](function (e) {
    if (window.console) { console.warn('analysis skipped page ' + (i + 1), e); }
    state.analysed = i + 1;
  });
}

/* Analysis runs page by page after the first paint, yielding between pages so
   that a slow device stays responsive and the reader is usable immediately. */
function analyseAll() {
  var i = 0;
  function step() {
    if (i >= state.total) { finishAnalysis(); return; }
    var target = i;
    analysePage(target).then(function () {
      i++;
      if (i === 1 || i % 4 === 0 || i === state.total) { drawToc(); drawNav(); }
      buildOverlaysFor(target);
      /* the page before may have been waiting on an "Answer:" line that has
         only just been read */
      if (target > 0) { buildOverlaysFor(target - 1); }
      if (i % 6 === 0) { drawThumbsMaybe(); }
      idle(step);
    });
  }
  idle(step);
}

function idle(fn) {
  if (window.requestIdleCallback) { window.requestIdleCallback(function () { fn(); }, { timeout: 300 }); }
  else { setTimeout(fn, lite() ? 24 : 0); }
}

function finishAnalysis() {
  state.done = true;
  for (var bi = 0; bi < state.pages.length; bi++) { buildOverlaysFor(bi); }
  drawToc();
  drawNav();
  applyRestoredAnswers();
  if (QUIZ_ON && quizTotal()) {
    dom.quizBtn.hidden = false;
    dom.scoreText.hidden = false;
    drawScore();
    applyAnswerVisibility();
    timerSetup();
    if (state.quiz) { startTiming(); }
  }
  if (TIMER_ON && EXAM_SECS > 0 && !state.timer.shown) { timerSetup(); }
  if (activeQuery) { runSearch(); }
  if (QUIZ_ON && !state.outline.length) { toast('No question headings found — reading tools are still available.', 2600); }
}

function applyRestoredAnswers() {
  var a = state.restoredAns || {}, f = state.restoredFlags || [], ms = state.restoredMs || {}, i;
  for (i = 0; i < state.qs.length; i++) {
    var q = state.qs[i];
    if (a[q.n]) { q.ans = a[q.n]; paintQuestion(q); }
    if (ms[q.n]) { q.ms = ms[q.n] * 1000; }
  }
  for (i = 0; i < f.length; i++) { if (state.qByN[f[i]]) { state.qByN[f[i]].flag = true; } }
  markChips();
  drawScore();
}

/* ---------------------------------------------------- overlays per page */

function layerOf(p, name) { return p[name]; }

/* Idempotent by design, and called more than once per page. A question whose
   stem sits at the foot of one page and whose "Answer:" line sits on the next
   has no known correct letter at the moment its own page is first analysed —
   so its options were skipped and the page was marked done, leaving that
   question unanswerable for the rest of the course. Every overlay is now
   keyed on its own node instead, and pages are swept again as later pages
   fill in what was missing. */
function buildOverlaysFor(i) {
  var p = state.pages[i];
  if (!p) { return; }
  var pageNo = i + 1;
  var k;

  for (k = 0; k < state.masks.length; k++) {
    var m = state.masks[k];
    if (m.page !== pageNo || m.node) { continue; }
    var b = make('button', 'mask');
    b.type = 'button';
    b.style.top = pct(m.top);
    b.style.height = pct(m.height);
    b.style.left = pct(MASK_L);
    b.style.width = pct(MASK_R - MASK_L);
    b.setAttribute('aria-label', 'Hidden answer, activate to reveal');
    b.appendChild(document.createTextNode(state.quiz && GATE
      ? 'Choose an option above to reveal'
      : 'Tap to reveal the answer'));
    m.node = b;
    (function (mask, node) {
      on(node, 'click', function () { revealMask(mask, node); });
    })(m, b);
    p.masks.appendChild(b);
  }

  for (k = 0; k < state.qs.length; k++) {
    var q = state.qs[k];
    if (!q.correct) { continue; }
    for (var z = 0; z < q.opts.length; z++) {
      var o = q.opts[z];
      if (o.page !== pageNo || o.node) { continue; }
      /* fall through: the node is created below */
      var ob = make('button', 'opt');
      ob.type = 'button';
      ob.style.top = pct(o.y);
      ob.style.height = pct(o.h);
      ob.style.left = pct(o.x);
      ob.style.width = pct(o.w);
      ob.setAttribute('aria-label', 'Choose option ' + o.L + ' for question ' + q.n);
      o.node = ob;
      (function (qq, oo) { on(ob, 'click', function () { choose(qq, oo.L); }); })(q, o);
      p.opts.appendChild(ob);
    }
    if (q.ans) { paintQuestion(q); }
  }

  applyAnswerVisibility();
}

/* ------------------------------------------------------ answer masking */

function answersHidden() { return state.quiz; }

function applyAnswerVisibility() {
  document.body.classList.toggle('hide-answers', answersHidden());
  document.body.classList.toggle('quiz', state.quiz);
  dom.quizBtn.classList.toggle('on', state.quiz);
  dom.quizBtn.setAttribute('aria-pressed', String(state.quiz));
  var qzState = el('qz-state');
  if (qzState) { qzState.textContent = state.quiz ? 'On' : 'Off'; }
  var nodes = document.querySelectorAll('.mask'), i;
  for (i = 0; i < nodes.length; i++) {
    if (!answersHidden()) { nodes[i].classList.remove('open'); }
    nodes[i].firstChild.nodeValue = state.quiz && GATE
      ? 'Choose an option above to reveal'
      : 'Tap to reveal the answer';
  }
  if (state.quiz) {
    for (i = 0; i < state.qs.length; i++) { if (state.qs[i].ans) { openMasksFor(state.qs[i]); } }
  }
}

function revealMask(mask, node) {
  if (!state.locked && state.quiz && GATE && mask.q && state.qByN[mask.q] && !state.qByN[mask.q].ans) {
    toast('Choose an answer first, then it opens.');
    return;
  }
  node.classList.add('open');
}

function openMasksFor(q) {
  for (var i = 0; i < q.masks.length; i++) {
    if (q.masks[i].node) { q.masks[i].node.classList.add('open'); }
  }
}

function toggleQuiz() {
  if (!QUIZ_ON || !quizTotal()) { toast('This document has no A–E options to answer.'); return; }
  if (state.locked) {
    toast('This attempt is closed — the answers stay open so you can review them.', 2400);
    return;
  }
  state.quiz = !state.quiz;
  if (state.quiz) { startTiming(); } else { bankTiming(); timingQ = null; }
  applyAnswerVisibility();
  toast(state.quiz ? 'Answer mode on — tap an option on the page' : 'Answer mode off');
  save();
}

/* --------------------------------------------------------- answer mode */

var timingQ = null, timingAt = 0;

/* Per-question time is what the analysis is built on, so it has to be banked
   whenever attention moves: to another question, out of answer mode, or onto
   a paused clock. Without this, time lands on whichever question happened to
   be current when the learner last chose an option. */
function bankTiming() {
  if (timingQ && timingAt) { timingQ.ms += now() - timingAt; }
  timingAt = 0;
}

function timingPaused() {
  return TIMER_ON && state.timer.shown && !state.timer.running;
}

function startTiming() {
  if (!state.quiz || timingPaused()) { bankTiming(); timingQ = null; return; }
  var q = questionAt(state.current);
  if (q === timingQ && timingAt) { return; }
  bankTiming();
  timingQ = q;
  timingAt = q ? now() : 0;
}

function questionAt(page) {
  var best = null;
  for (var i = 0; i < state.qs.length; i++) {
    if (state.qs[i].page <= page) { best = state.qs[i]; }
  }
  return best;
}

function choose(q, letter) {
  if (state.locked) { toast('Time is up — this attempt is closed. You can still read the answers.', 2400); return; }
  if (!state.quiz) { toast('Turn on Answer mode to choose.'); return; }
  var first = !q.ans;
  q.ans = letter;
  if (timingQ === q && timingAt) { q.ms += now() - timingAt; timingAt = now(); }
  paintQuestion(q);
  openMasksFor(q);
  markChips();
  drawScore();
  if (first && SEND_INTER && live) {
    SCORM.interaction('Q' + q.n, 'choice', q.correct, letter,
      letter === q.correct ? 'correct' : 'wrong', Math.round((q.ms || 0) / 1000));
  }
  toast(letter === q.correct ? 'Correct' : 'Not quite — the answer is ' + q.correct, 1400);
  save();
}

function paintQuestion(q) {
  for (var i = 0; i < q.opts.length; i++) {
    var o = q.opts[i];
    if (!o.node) { continue; }
    o.node.classList.remove('picked', 'right', 'wrong');
    clear(o.node);
    if (!q.ans) { continue; }
    if (o.L === q.correct) { o.node.classList.add('right'); addTick(o.node, '✓'); }
    else if (o.L === q.ans) { o.node.classList.add('wrong'); addTick(o.node, '✕'); }
  }
}

function addTick(node, ch) {
  var s = make('span', 'tick');
  s.textContent = ch;
  node.appendChild(s);
}

function drawScore() {
  var sc = quizScore();
  if (!sc.total) { dom.scoreText.hidden = true; return; }
  dom.scoreText.hidden = false;
  dom.scoreText.textContent = sc.right + ' / ' + sc.total;
  dom.scoreText.title = sc.answered + ' of ' + sc.total + ' answered';
}

function showResults() {
  var sc = quizScore();
  var body = el('results-body');
  clear(body);
  if (!sc.total) {
    body.innerHTML = '<p class="empty">This document has no A&ndash;E questions to score. ' +
      'Your reading progress is reported to the LMS.</p>';
    el('results-sheet').hidden = false;
    return;
  }
  var pctScore = sc.total ? Math.round((sc.right / sc.total) * 100) : 0;
  var big = make('p', 'score-big');
  big.textContent = sc.right + ' / ' + sc.total + '  (' + pctScore + '%)';
  var sub = make('p', 'score-sub');
  if (sc.answered < sc.total) {
    sub.textContent = (sc.total - sc.answered) + ' still unanswered. Pass mark is ' + MASTERY + '%.';
  } else {
    sub.className = 'score-sub ' + (pctScore >= MASTERY ? 'pass' : 'fail');
    sub.textContent = (pctScore >= MASTERY ? 'Passed' : 'Not yet passed') +
      ' — pass mark ' + MASTERY + '%. Total time ' + mmss(now() - state.started) + '.';
  }
  body.appendChild(big);
  body.appendChild(sub);
  if (state.timer.shown) {
    var el2 = timerElapsed(), tt = state.timer.total;
    var tl = make('p', 'score-sub' + (state.locked ? ' fail' : ''));
    if (state.locked) {
      tl.textContent = 'The time allowed (' + hhmmss(tt) + ') was reached and this attempt was submitted automatically.';
    } else {
      tl.textContent = 'Stopwatch: ' + hhmmss(el2) + ' of ' + hhmmss(tt) + ' allowed' +
        (el2 > tt ? ' — ' + hhmmss(el2 - tt) + ' over' : ' — ' + hhmmss(tt - el2) + ' to spare') +
        (state.timer.running ? ', running.' : ', paused.');
    }
    body.appendChild(tl);
  }

  for (var i = 0; i < state.qs.length; i++) {
    var q = state.qs[i];
    if (!q.correct) { continue; }
    var row = make('div', 'res-row' + (q.ans ? (q.ans === q.correct ? ' right' : ' wrong') : ''));
    var n = make('span', 'n'); n.textContent = 'Q' + q.n;
    var a = make('span', 'a');
    a.textContent = q.ans
      ? ('You chose ' + q.ans + ', answer ' + q.correct + (q.ms ? ' · ' + mmss(q.ms) : ''))
      : 'Not answered';
    var r = make('span', 'r');
    r.textContent = q.ans ? (q.ans === q.correct ? '✓' : '✕') : '–';
    row.appendChild(n); row.appendChild(a); row.appendChild(r);
    body.appendChild(row);
  }
  el('results-sheet').hidden = false;
}

function mmss(ms) {
  var s = Math.max(0, Math.round(ms / 1000));
  var m = Math.floor(s / 60);
  s = s % 60;
  return m + ':' + (s < 10 ? '0' : '') + s;
}

function reviewWrong() {
  for (var i = 0; i < state.qs.length; i++) {
    var q = state.qs[i];
    if (q.correct && q.ans && q.ans !== q.correct) {
      el('results-sheet').hidden = true;
      goTo(q.page, true, q.ny);
      toast('Q' + q.n + ' — you chose ' + q.ans + ', the answer is ' + q.correct, 2600);
      return;
    }
  }
  toast('Nothing missed so far.');
}

function restartAttempt() {
  if (!window.confirm('Clear your answers and start this attempt again?')) { return; }
  for (var i = 0; i < state.qs.length; i++) {
    var q = state.qs[i];
    q.ans = null; q.ms = 0; q.flag = false;
    paintQuestion(q);
    for (var k = 0; k < q.masks.length; k++) {
      if (q.masks[k].node) { q.masks[k].node.classList.remove('open'); }
    }
  }
  state.started = now();
  timerReset();
  markChips();
  drawScore();
  save();
  startTiming();
  toast(state.timer.shown ? 'Attempt cleared — the stopwatch is back to 0:00.'
                          : 'Attempt cleared.', 2200);
}

/* ------------------------------------------------------- exam stopwatch */

/* A stopwatch: it counts UP from 0:00 while the learner works. The time
   allowed for the paper (--exam-time, or questions x --per-question) is kept
   as a target: the clock turns amber at 80% of it and red once it is passed,
   and keeps running. Only with --auto-submit does reaching the target close
   the attempt.

   Wall-clock, not a count of ticks: a background tab in an LMS frame gets
   its timers throttled to once a minute, and a clock built on tick counts
   would quietly lose time. Elapsed time is banked in seconds whenever the
   clock stops, and it always comes back paused. */

var timerInt = null;

/* seconds on the stopwatch */
function timerElapsed() {
  var t = state.timer;
  if (!t.running) { return t.elapsed; }
  return t.elapsed + (now() - t.at) / 1000;
}

/* seconds left before the target (kept for the results sheet) */
function timerLeft() {
  var t = state.timer;
  return t.total ? Math.max(0, t.total - timerElapsed()) : 0;
}

/* SVG elements do not carry the HTMLElement `hidden` property, so the
   attribute has to be set by hand for the [hidden] rule to bite. */
function setHidden(node, yes) {
  if (!node) { return; }
  if (yes) { node.setAttribute('hidden', 'hidden'); }
  else { node.removeAttribute('hidden'); }
}

function hhmmss(secs) {
  var s = Math.max(0, Math.floor(secs));
  var h = Math.floor(s / 3600);
  var m = Math.floor((s % 3600) / 60);
  s = s % 60;
  var mm = (h && m < 10 ? '0' : '') + m;
  return (h ? h + ':' : '') + mm + ':' + (s < 10 ? '0' : '') + s;
}

function timerSetup() {
  if (!TIMER_ON) { return; }
  var qn = quizTotal();
  var total = EXAM_SECS > 0 ? EXAM_SECS : (qn ? qn * PER_Q_SECS : 0);
  if (!total) { return; }                       /* nothing to time */

  var t = state.timer;
  t.total = total;
  t.elapsed = 0;
  t.shown = true;

  var rt = state.restoredTimer;
  if (rt) {
    /* v3.6 and earlier banked time LEFT on a countdown; convert once. */
    var el0 = rt.sw ? rt.value : (total - rt.value);
    t.elapsed = Math.max(0, el0 || 0);
    t.expired = rt.expired;
    t.over = rt.expired || t.elapsed >= total;
    t.started = rt.started;
    if (rt.locked) { state.locked = true; }
  }

  dom.timerWrap.hidden = false;
  if (dom.timerTarget) { dom.timerTarget.textContent = '/ ' + hhmmss(total); }
  timerPaint();

  if (state.locked) { return; }
  if (TIMER_AUTO && !rt) { timerStart(); }
}

function timerStart() {
  var t = state.timer;
  if (t.running || state.locked || !t.shown) { return; }
  t.running = true;
  t.started = true;
  t.at = now();
  clearInterval(timerInt);
  timerInt = setInterval(timerTick, 250);
  startTiming();
  timerPaint();
  save();
}

function timerPause(quiet) {
  var t = state.timer;
  if (!t.running) { return; }
  t.elapsed = timerElapsed();
  t.running = false;
  t.at = 0;
  clearInterval(timerInt);
  timerInt = null;
  bankTiming();
  timingQ = null;
  timerPaint();
  if (!quiet) { toast('Stopwatch paused at ' + hhmmss(t.elapsed) + '.', 1600); }
  save();
}

function timerToggle() {
  var t = state.timer;
  if (!t.shown) { toast('This course has no stopwatch.'); return; }
  if (state.locked) { toast('This attempt has been submitted.'); return; }
  if (t.running) { timerPause(); }
  else {
    timerStart();
    toast(t.elapsed > 0 ? 'Stopwatch resumed at ' + hhmmss(t.elapsed) + '.'
                        : 'Stopwatch started — ' + hhmmss(t.total) + ' allowed.', 1600);
  }
}

function timerTick() {
  var t = state.timer;
  timerPaint();
  if (!t.over && t.total && timerElapsed() >= t.total) { timerOver(); }
}

function timerPaint() {
  var t = state.timer;
  if (!t.shown || !dom.timerWrap) { return; }
  var el1 = timerElapsed();
  dom.timerText.textContent = hhmmss(el1);

  var w = dom.timerWrap;
  w.classList.remove('run', 'warn', 'crit', 'done');
  if (state.locked) { w.classList.add('done'); }
  else if (t.total && el1 >= t.total) { w.classList.add('crit'); }
  else if (t.total && el1 >= t.total * 0.8) { w.classList.add('warn'); }
  if (t.running && !state.locked) { w.classList.add('run'); }
  w.title = hhmmss(el1) + ' elapsed of ' + hhmmss(t.total) + ' allowed' +
    (el1 > t.total ? ' (' + hhmmss(el1 - t.total) + ' over)' : '');

  var btn = dom.timerBtn;
  if (btn) {
    setHidden(btn.querySelector('.ti-play'), !!t.running);
    setHidden(btn.querySelector('.ti-pause'), !t.running);
    btn.setAttribute('aria-pressed', String(!!t.running));
    btn.setAttribute('aria-label', t.running ? 'Pause the stopwatch' : 'Start the stopwatch');
    btn.title = t.running ? 'Pause the stopwatch (T)' : 'Start the stopwatch (T)';
    btn.disabled = !!state.locked;
  }
}

/* The stopwatch has reached the time allowed. */
function timerOver() {
  var t = state.timer;
  if (t.over) { return; }
  t.over = true;
  t.expired = true;
  var msg = el('timeup-text');

  if (AUTO_SUBMIT) {
    t.elapsed = t.total;
    t.running = false;
    t.at = 0;
    clearInterval(timerInt);
    timerInt = null;
    bankTiming();
    timingQ = null;
    state.locked = true;
    if (state.quiz) { state.quiz = false; applyAnswerVisibility(); }
    if (msg) {
      msg.textContent = 'Time allowed reached. Your attempt has been submitted — ' +
        quizScore().right + '/' + quizTotal() + '. The answers are open to read.';
    }
    reportOutcome(true);
    if (ANALYSIS_ON) { setTimeout(function () { showAnalysis(); }, 900); }
  } else if (msg) {
    var sc = quizScore();
    msg.textContent = 'You have reached the ' + hhmmss(t.total) + ' allowed. The stopwatch keeps running — ' +
      (sc.total - sc.answered) + ' of ' + sc.total + ' still unanswered.';
  }
  timerPaint();
  el('timeup').hidden = false;
  save();
}

function timerReset() {
  var t = state.timer;
  clearInterval(timerInt);
  timerInt = null;
  t.elapsed = 0;
  t.running = false;
  t.at = 0;
  t.expired = false;
  t.over = false;
  t.started = false;
  state.locked = false;
  el('timeup').hidden = true;
  timerPaint();
}

/* ------------------------------------------------------------- analysis */

function analysisReport() {
  if (!window.RFA_ANALYSIS) { return null; }
  var elapsed = 0;
  if (state.timer.shown) { elapsed = Math.round(timerElapsed()); }
  else { elapsed = Math.round((now() - state.started) / 1000); }
  return window.RFA_ANALYSIS.build({
    questions: state.qs,
    modules: MODULES,
    mastery: MASTERY,
    examSeconds: state.timer.shown ? state.timer.total : 0,
    elapsedSeconds: elapsed,
    timeUp: !!state.timer.expired
  });
}

var lastReport = null;

function showAnalysis() {
  var body = el('analysis-body');
  var sheet = el('analysis-sheet');
  if (!body || !sheet) { return; }
  clear(body);

  if (!QUIZ_ON || !quizTotal()) {
    el('an-lede').textContent =
      'This document has no A–E questions, so there is nothing to analyse. Your reading progress is still reported to the LMS.';
    sheet.hidden = false;
    return;
  }

  var r = analysisReport();
  lastReport = r;
  if (!r) { return; }

  el('an-lede').textContent = r.lede;

  if (!r.answered) {
    var none = make('p', 'empty');
    none.textContent = 'Answer a few questions and open this again — the breakdown needs something to work with.';
    body.appendChild(none);
    sheet.hidden = false;
    return;
  }

  /* headline figures */
  body.appendChild(statRow([
    ['Score', r.right + '/' + r.total, r.pct + '%'],
    ['Accuracy', r.accuracy + '%', 'of ' + r.answered + ' attempted'],
    ['Pace', window.RFA_ANALYSIS.mmss(r.medianMs), 'typical question'],
    ['Unanswered', String(r.unanswered), r.unanswered ? 'scores zero' : 'nothing skipped']
  ]));

  /* module breakdown, weakest first */
  body.appendChild(section(r.hasModules ? 'By module — weakest first' : 'This paper'));
  var mods = r.ranked, i;
  for (i = 0; i < mods.length; i++) { body.appendChild(moduleRow(mods[i])); }
  if (!r.hasModules) {
    var hint = make('p', 'an-hint');
    hint.textContent = 'No modules were set for this paper, so the breakdown covers it as a whole.';
    body.appendChild(hint);
  }

  /* what it means */
  body.appendChild(section('What this says'));
  for (i = 0; i < r.findings.length; i++) {
    var f = r.findings[i];
    var card = make('div', 'an-find ' + f.level);
    var h = make('p', 'an-find-h');
    h.textContent = f.title;
    var t = make('p', 'an-find-t');
    t.textContent = f.text;
    card.appendChild(h);
    card.appendChild(t);
    body.appendChild(card);
  }

  /* what to do next */
  body.appendChild(section('What to do next'));
  var ol = make('ol', 'an-plan');
  for (i = 0; i < r.plan.length; i++) {
    var li = make('li', '');
    var b = make('b', '');
    b.textContent = r.plan[i].head;
    li.appendChild(b);
    li.appendChild(document.createTextNode(' — ' + r.plan[i].body));
    ol.appendChild(li);
  }
  body.appendChild(ol);

  var btn = el('analysis-review');
  if (btn) { btn.hidden = !(r.focus && r.focus.missedQs.length); }

  sheet.hidden = false;
}

function section(label) {
  var h = make('h3', '');
  h.textContent = label;
  return h;
}

function statRow(items) {
  var wrap = make('div', 'an-stats');
  for (var i = 0; i < items.length; i++) {
    var cell = make('div', 'an-stat');
    var k = make('span', 'k'); k.textContent = items[i][0];
    var v = make('span', 'v'); v.textContent = items[i][1];
    var s2 = make('span', 's'); s2.textContent = items[i][2];
    cell.appendChild(k); cell.appendChild(v); cell.appendChild(s2);
    wrap.appendChild(cell);
  }
  return wrap;
}

function moduleRow(m) {
  var row = make('div', 'an-mod ' + m.band);
  var top = make('div', 'an-mod-top');
  var nm = make('span', 'nm'); nm.textContent = m.name;
  var sc = make('span', 'sc');
  sc.textContent = m.answered ? (m.right + '/' + m.answered + '  ' + m.pct + '%') : 'not attempted';
  top.appendChild(nm); top.appendChild(sc);

  var track = make('div', 'an-bar');
  var fill = make('span', '');
  fill.style.width = (m.answered ? m.pct : 0) + '%';
  track.appendChild(fill);

  var note = make('p', 'an-mod-note');
  var parts = [];
  if (m.answered && m.avgMs) { parts.push(window.RFA_ANALYSIS.mmss(m.avgMs) + ' a question'); }
  if (m.unanswered) { parts.push(m.unanswered + ' unanswered'); }
  if (m.wrongQs.length) { parts.push('missed Q' + m.wrongQs.join(', Q')); }
  if (!m.answered) { parts.push('nothing attempted in this module yet'); }
  note.textContent = parts.join(' · ');

  row.appendChild(top);
  row.appendChild(track);
  if (parts.length) { row.appendChild(note); }

  (function (mod) {
    on(row, 'click', function () {
      var n = mod.missedQs.length ? mod.missedQs[0] : null;
      if (n === null) { return; }
      var q = state.qByN[n];
      if (!q) { return; }
      el('analysis-sheet').hidden = true;
      goTo(q.page, true, q.ny);
      toast('Q' + q.n + ' — ' + mod.name, 2200);
    });
  })(m);

  return row;
}

function reviewWeakest() {
  var r = lastReport || analysisReport();
  if (!r || !r.focus || !r.focus.missedQs.length) { toast('Nothing stands out to review.'); return; }
  var q = state.qByN[r.focus.missedQs[0]];
  if (!q) { toast('Nothing stands out to review.'); return; }
  el('analysis-sheet').hidden = true;
  goTo(q.page, true, q.ny);
  toast(r.focus.name + ' — starting at Q' + q.n, 2600);
}

/* -------------------------------------------------------- contents / nav */

function drawToc() {
  clear(dom.toc);
  if (!state.outline.length) {
    dom.toc.innerHTML = state.done
      ? '<p class="empty">This document has no Q1., Q2. headings to list. Search and bookmarks still work.</p>'
      : '<p class="empty">Reading the document&hellip;</p>';
    return;
  }
  for (var i = 0; i < state.outline.length; i++) {
    (function (item) {
      var b = make('button', 'toc-item');
      b.type = 'button';
      if (item.ans) { b.className += item.ans === item.correct ? ' done' : ' missed'; }
      b.appendChild(document.createTextNode(item.label));
      var w = make('span', 'where');
      w.textContent = 'Page ' + item.page + (item.flag ? ' · flagged' : '');
      b.appendChild(w);
      on(b, 'click', function () {
        goTo(item.page, true, item.ny);
        if (isNarrow()) { closePanel(); }
      });
      dom.toc.appendChild(b);
    })(state.outline[i]);
  }
  if (!state.done) {
    var p = make('p', 'empty');
    p.textContent = 'Still reading page ' + state.analysed + ' of ' + state.total + '…';
    dom.toc.appendChild(p);
  }
}

function drawNav() {
  if (!state.qs.length) { dom.navGrid.hidden = true; return; }
  dom.navGrid.hidden = false;
  clear(dom.navGrid);
  for (var i = 0; i < state.qs.length; i++) {
    (function (q) {
      var b = make('button', 'chip');
      b.type = 'button';
      b.textContent = String(q.n);
      b.title = 'Question ' + q.n + ' — page ' + q.page;
      q.chip = b;
      on(b, 'click', function () {
        goTo(q.page, true, q.ny);
        if (isNarrow()) { closePanel(); }
      });
      dom.navGrid.appendChild(b);
    })(state.qs[i]);
  }
  markChips();
}

function markChips() {
  var here = questionAt(state.current);
  for (var i = 0; i < state.qs.length; i++) {
    var q = state.qs[i];
    if (!q.chip) { continue; }
    q.chip.className = 'chip' +
      (q.ans ? (q.ans === q.correct ? ' right' : ' wrong') : '') +
      (q.flag ? ' flag' : '') +
      (q === here ? ' here' : '');
  }
}

function flagCurrent() {
  var q = questionAt(state.current);
  if (!q) { toast('No question on this page to flag.'); return; }
  q.flag = !q.flag;
  markChips();
  drawToc();
  save();
  toast(q.flag ? 'Q' + q.n + ' flagged for review' : 'Q' + q.n + ' unflagged');
}

/* --------------------------------------------------------------- search */

var activeQuery = '';
var hitList = [];
var hitAt = -1;

function runSearch() {
  var q = (dom.q.value || '').replace(/^\s+|\s+$/g, '');
  activeQuery = q;
  hitList = [];
  hitAt = -1;
  clear(dom.hits);
  clearFind();

  if (!q) {
    dom.hits.innerHTML = '<p class="empty">Type a word or phrase to search all pages.</p>';
    dom.searchNav.hidden = true;
    return;
  }

  var needle = q.toLowerCase();
  var scanned = 0;
  for (var i = 0; i < state.total; i++) {
    var text = state.plain[i];
    if (text === undefined) { continue; }
    scanned++;
    var hay = text.toLowerCase();
    var from = 0;
    while (true) {
      var at = hay.indexOf(needle, from);
      if (at === -1) { break; }
      addHit(i, text, at, q);
      from = at + q.length;
      if (hitList.length > 400) { break; }
    }
    paintFind(i, needle);
    if (hitList.length > 400) { break; }
  }

  dom.searchNav.hidden = hitList.length === 0;
  if (!hitList.length) {
    dom.hits.innerHTML = '<p class="empty">No matches for &ldquo;' + esc(q) + '&rdquo;' +
      (state.done ? '' : ' in the ' + scanned + ' pages read so far') + '.</p>';
  } else {
    if (!state.done) {
      var note = make('p', 'empty');
      note.textContent = 'Searching the pages read so far (' + scanned + ' of ' + state.total +
        '). This list grows as the rest loads.';
      dom.hits.insertBefore(note, dom.hits.firstChild);
    }
    stepTo(0);
  }
}

function addHit(i, text, at, q) {
  var start = Math.max(0, at - 40);
  var b = make('button', 'hit');
  b.type = 'button';
  b.innerHTML = (start > 0 ? '&hellip;' : '') +
    esc(text.slice(start, at)) + '<b>' + esc(text.substr(at, q.length)) + '</b>' +
    esc(text.slice(at + q.length, at + q.length + 50)) +
    '<span class="where">Page ' + (i + 1) + '</span>';
  var index = hitList.length;
  on(b, 'click', function () { stepTo(index); });
  dom.hits.appendChild(b);
  hitList.push({ page: i + 1, btn: b });
}

function stepTo(i) {
  if (!hitList.length) { return; }
  hitAt = (i + hitList.length) % hitList.length;
  var hit = hitList[hitAt];
  dom.searchCount.textContent = (hitAt + 1) + ' / ' + hitList.length;
  for (var n = 0; n < hitList.length; n++) { hitList[n].btn.classList.toggle('current', n === hitAt); }
  goTo(hit.page);
  if (isNarrow()) { closePanel(); }
  markActiveFind(hit.page);
}

function clearFind() {
  for (var i = 0; i < state.pages.length; i++) {
    if (state.pages[i].find) { clear(state.pages[i].find); }
  }
}

/* Highlights are drawn as boxes over the canvas, sized from the stored line
   geometry: there is no text in the DOM to wrap in a <mark>. */
function paintFind(i, needle) {
  var p = state.pages[i];
  var lines = state.lines[i];
  if (!p || !lines) { return; }
  clear(p.find);
  for (var k = 0; k < lines.length; k++) {
    var L = lines[k];
    var low = L.t.toLowerCase();
    var from = 0;
    while (true) {
      var at = low.indexOf(needle, from);
      if (at === -1) { break; }
      var box = make('i');
      var per = L.w / Math.max(1, L.t.length);
      box.style.left = pct(L.x + per * at);
      box.style.width = pct(Math.max(per * needle.length, 0.01));
      box.style.top = pct(L.y);
      box.style.height = pct(L.h);
      p.find.appendChild(box);
      from = at + needle.length;
    }
  }
}

function markActiveFind(page) {
  var p = state.pages[page - 1];
  if (!p || !p.find) { return; }
  var boxes = p.find.childNodes, i;
  for (i = 0; i < boxes.length; i++) { boxes[i].className = i === 0 ? 'active' : ''; }
}

/* ------------------------------------------------------------ bookmarks */

function hasMark(page) {
  for (var i = 0; i < state.marks.length; i++) { if (state.marks[i].page === page) { return true; } }
  return false;
}

function relTime(ts) {
  var mins = Math.round((now() - ts) / 60000);
  if (mins < 1) { return 'just now'; }
  if (mins < 60) { return mins + ' min ago'; }
  var hrs = Math.round(mins / 60);
  if (hrs < 24) { return hrs + ' h ago'; }
  var days = Math.round(hrs / 24);
  return days === 1 ? 'yesterday' : days + ' days ago';
}

function drawMarks() {
  clear(dom.marks);
  if (!state.marks.length) {
    dom.marks.innerHTML = '<p class="empty">No bookmarks yet. Use the flag button to mark a page.</p>';
    return;
  }
  var sorted = state.marks.slice().sort(function (a, b) { return a.page - b.page; });
  for (var i = 0; i < sorted.length; i++) {
    (function (m) {
      var b = make('button', 'mark-item');
      b.type = 'button';
      b.appendChild(document.createTextNode('Page ' + m.page));
      var w = make('span', 'when');
      w.textContent = 'Added ' + relTime(m.at);
      b.appendChild(w);
      on(b, 'click', function () { goTo(m.page); if (isNarrow()) { closePanel(); } });
      dom.marks.appendChild(b);
    })(sorted[i]);
  }
}

function toggleMark() {
  var found = -1;
  for (var i = 0; i < state.marks.length; i++) {
    if (state.marks[i].page === state.current) { found = i; break; }
  }
  if (found === -1) { state.marks.push({ page: state.current, at: now() }); }
  else { state.marks.splice(found, 1); }
  dom.bookmarkBtn.classList.toggle('on', found === -1);
  drawMarks();
  save();
  toast(found === -1 ? 'Page ' + state.current + ' bookmarked' : 'Bookmark removed');
}

/* ------------------------------------------------------------- read aloud */

var speech = window.speechSynthesis || null;

function toggleSpeak() {
  if (!SPEAK_ON || !speech || !window.SpeechSynthesisUtterance) {
    toast('This device cannot read aloud.');
    return;
  }
  if (state.speaking) { stopSpeak(); return; }
  var lines = state.lines[state.current - 1];
  if (!lines || !lines.length) { toast('This page has not finished loading yet.'); return; }
  state.speaking = true;
  markSpeak();
  var p = state.pages[state.current - 1];
  var i = 0;
  function next() {
    if (!state.speaking || i >= lines.length) { stopSpeak(); return; }
    var L = lines[i];
    clear(p.speak);
    var u = make('u');
    u.style.left = pct(Math.max(0, L.x - 0.005));
    u.style.top = pct(L.y);
    u.style.width = pct(Math.min(1, L.w + 0.01));
    u.style.height = pct(L.h);
    p.speak.appendChild(u);
    var utt = new window.SpeechSynthesisUtterance(L.t);
    utt.rate = 1;
    utt.onend = function () { i++; next(); };
    utt.onerror = function () { i++; next(); };
    speech.speak(utt);
  }
  next();
}

function markSpeak() {
  var btn = el('speak');
  if (!btn) { return; }
  btn.classList.toggle('on', state.speaking);
  btn.setAttribute('aria-pressed', String(state.speaking));
  btn.title = state.speaking ? 'Stop reading aloud' : 'Read this page aloud';
}

function stopSpeak() {
  state.speaking = false;
  markSpeak();
  if (speech) { try { speech.cancel(); } catch (e) { /* ignore */ } }
  for (var i = 0; i < state.pages.length; i++) { if (state.pages[i].speak) { clear(state.pages[i].speak); } }
}

/* ------------------------------------------------------------ thumbnails */

var thumbsDrawn = false;

function drawThumbsMaybe() {
  if (thumbsDrawn && dom.tabThumbs.hidden) { return; }
  if (!dom.tabThumbs.hidden) { drawThumbs(); }
}

function drawThumbs() {
  if (!THUMBS_ON) { return; }
  if (thumbsDrawn) { markThumb(); return; }
  thumbsDrawn = true;
  clear(dom.thumbs);
  for (var i = 0; i < state.total; i++) {
    (function (n) {
      var b = make('button', 'thumb');
      b.type = 'button';
      var c = make('canvas');
      var lab = make('span');
      lab.textContent = String(n);
      b.appendChild(c);
      b.appendChild(lab);
      on(b, 'click', function () { goTo(n); if (isNarrow()) { closePanel(); } });
      dom.thumbs.appendChild(b);
      thumbQueue.push({ n: n, canvas: c, btn: b });
    })(i + 1);
  }
  runThumbQueue();
  markThumb();
}

var thumbQueue = [];
var thumbBusy = false;

function runThumbQueue() {
  if (thumbBusy || !thumbQueue.length) { return; }
  if (dom.tabThumbs.hidden) { return; }
  thumbBusy = true;
  var job = thumbQueue.shift();
  state.doc.getPage(job.n).then(function (page) {
    var vp = page.getViewport({ scale: 1 });
    var w = lite() ? 110 : 160;
    var s = w / vp.width;
    var v = page.getViewport({ scale: s });
    job.canvas.width = Math.floor(v.width);
    job.canvas.height = Math.floor(v.height);
    return page.render({ canvasContext: job.canvas.getContext('2d', { alpha: false }), viewport: v }).promise;
  })['catch'](function () { /* skip */ }).then(function () {
    thumbBusy = false;
    setTimeout(runThumbQueue, lite() ? 60 : 10);
  });
}

function markThumb() {
  var nodes = dom.thumbs ? dom.thumbs.getElementsByClassName('thumb') : [];
  for (var i = 0; i < nodes.length; i++) {
    nodes[i].classList.toggle('here', i + 1 === state.current);
  }
}

/* ---------------------------------------------------------------- panel */

function isNarrow() { return window.innerWidth <= 900; }

function openPanel() {
  dom.panel.classList.add('open');
  if (!isNarrow()) { dom.stage.classList.add('shifted'); }
  dom.scrim.classList.toggle('on', isNarrow());
  setTimeout(function () { if (state.fit) { layout(); } }, 200);
}

function closePanel() {
  dom.panel.classList.remove('open');
  dom.stage.classList.remove('shifted');
  dom.scrim.classList.remove('on');
  setTimeout(function () { if (state.fit) { layout(); } }, 200);
}

function showTab(name) {
  var btns = dom.panel.querySelectorAll('.tabs button'), i;
  for (i = 0; i < btns.length; i++) { btns[i].classList.toggle('on', btns[i].getAttribute('data-tab') === name); }
  dom.tabToc.hidden = name !== 'toc';
  dom.tabSearch.hidden = name !== 'search';
  dom.tabMarks.hidden = name !== 'marks';
  dom.tabThumbs.hidden = name !== 'thumbs';
  if (name === 'marks') { drawMarks(); }
  if (name === 'thumbs') { drawThumbs(); runThumbQueue(); }
}

/* ----------------------------------------------------------------- zoom */

function setZoom(mode, value) {
  if (mode === 'fit') { state.fit = value; state.scale = null; }
  else { state.scale = clamp(value, MIN_SCALE, MAX_SCALE); state.fit = null; }
  layout();
  goTo(state.current, false);
  showZoom();
  save();
}

/* --------------------------------------------------------------- themes */

function applyTheme() {
  for (var i = 0; i < THEMES.length; i++) {
    document.body.classList.toggle('theme-' + THEMES[i], i === state.theme);
  }
  var name = el('theme-name');
  if (name) { name.textContent = THEME_NAMES[state.theme]; }
  var btn = el('theme');
  if (btn) { btn.title = 'Reading theme: ' + THEME_NAMES[state.theme] + ' — tap to change'; }
}

/* ----------------------------------------------------------------- load */

function fail(title, detail) {
  clear(dom.stage);
  var n = make('div', 'notice');
  n.innerHTML = '<h2>' + esc(title) + '</h2><p>' + detail + '</p>';
  dom.stage.appendChild(n);
  document.body.classList.remove('booting');
}

function bootNote(msg) { if (dom.bootNote) { dom.bootNote.textContent = msg; } }
function bootBar(frac) { if (dom.bootBar) { dom.bootBar.style.width = Math.round(frac * 100) + '%'; } }

/* XMLHttpRequest rather than fetch: it works in every browser this has to
   support and it reports download progress, which matters on a slow link. */
function loadBytes() {
  return new Promise(function (resolve, reject) {
    var xhr = new XMLHttpRequest();
    xhr.open('GET', SRC, true);
    xhr.responseType = 'arraybuffer';
    xhr.onprogress = function (e) {
      if (e.lengthComputable && e.total) {
        bootBar(e.loaded / e.total * 0.85);
        bootNote(Math.round(e.loaded / 1048576 * 10) / 10 + ' of ' +
                 Math.round(e.total / 1048576 * 10) / 10 + ' MB');
      } else {
        bootNote(Math.round(e.loaded / 1048576 * 10) / 10 + ' MB downloaded');
      }
    };
    xhr.onload = function () {
      if (xhr.status >= 200 && xhr.status < 300 && xhr.response) {
        bootBar(0.88);
        bootNote('Preparing the pages…');
        var bytes = new Uint8Array(xhr.response);
        resolve(KEY ? decode(bytes, KEY) : bytes);
      } else {
        reject(new Error('HTTP ' + xhr.status));
      }
    };
    xhr.onerror = function () { reject(new Error('network')); };
    xhr.send();
  });
}

/* Mirror of obfuscate() in build.py. Positional, so it costs one pass. */
function decode(bytes, key) {
  var k = [], i;
  for (i = 0; i < key.length; i++) { k.push(key.charCodeAt(i) & 0xFF); }
  var n = k.length;
  for (i = 0; i < bytes.length; i++) {
    bytes[i] = bytes[i] ^ k[i % n] ^ ((i * 31) & 0xFF);
  }
  return bytes;
}

function buildPages(firstBase) {
  for (var i = 0; i < state.total; i++) {
    var wrap = make('div', 'page');
    var canvas = make('canvas');
    canvas.draggable = false;
    var ph = make('div', 'placeholder');
    ph.textContent = 'Page ' + (i + 1);
    var wm = make('div', 'layer wm');
    var stamp = make('div', 'layer stamp');
    var find = make('div', 'layer find');
    var speak = make('div', 'layer speak');
    var opts = make('div', 'layer opts');
    var masks = make('div', 'layer masks');
    wrap.appendChild(canvas);
    wrap.appendChild(ph);
    wrap.appendChild(wm);
    wrap.appendChild(stamp);
    wrap.appendChild(find);
    wrap.appendChild(speak);
    wrap.appendChild(opts);
    wrap.appendChild(masks);
    dom.stage.appendChild(wrap);
    var p = {
      wrap: wrap, canvas: canvas, ph: ph, wm: wm, stamp: stamp, find: find,
      speak: speak, opts: opts, masks: masks,
      base: { width: firstBase.width, height: firstBase.height },
      rendered: false, rendering: false, stale: false, built: false, task: null
    };
    state.pages.push(p);
    sizePage(p);
    RFA_GUARD.paint(wm, i + 1, stamp);
  }
}

var bootPhase = 'download';

function start() {
  live = SCORM.init();
  state.quiz = QUIZ_ON && QUIZ_START;
  restore();
  RFA_GUARD.init({ scorm: SCORM, live: live, save: save, units: 0 });
  applyTheme();
  state.dwellFrom = now();

  if (!window.pdfjsLib || !window.Promise) {
    fail('This browser is too old to open the document',
      'The reader needs a browser released after about 2017. Please open the course in an up-to-date ' +
      'Chrome, Edge, Firefox or Safari, or on a newer device.');
    return;
  }

  pdfjsLib.GlobalWorkerOptions.workerSrc = 'lib/pdf.worker.min.js';

  loadBytes().then(function (bytes) {
    bootPhase = 'parse';
    return pdfjsLib.getDocument({
      data: bytes,
      isEvalSupported: false,
      disableAutoFetch: true,
      disableStream: true
    }).promise;
  }).then(function (doc) {
    bootPhase = 'first page';
    state.doc = doc;
    state.total = doc.numPages;
    RFA_GUARD.units(doc.numPages);
    dom.pageCount.textContent = '/ ' + state.total;
    unpackSeen(state.restoredSeen);
    return doc.getPage(1);
  }).then(function (page) {
    bootPhase = 'display';
    var base = page.getViewport({ scale: 1 });
    bootBar(1);
    document.body.classList.remove('booting');
    if (dom.loading && dom.loading.parentNode) { dom.loading.parentNode.removeChild(dom.loading); }
    buildPages({ width: base.width, height: base.height });
    layout();
    state.current = clamp(state.current, 1, state.total);
    goTo(state.current, false);
    drawMarks();
    drawProgress();
    applyAnswerVisibility();
    showZoom();
    if (state.current > 1) { toast('Back where you left off, page ' + state.current, 2200); }
    setTimeout(analyseAll, 60);
  })['catch'](function (e) {
    if (window.console) { console.error(e); }
    var detail = '';
    try {
      detail = e ? String(e.message || e) : 'unknown error';
      if (e && e.stack) {
        var top = String(e.stack).split('\n')[1];
        if (top) { detail += ' at ' + top.replace(/^\s+/, '').slice(0, 120); }
      }
    } catch (x) { detail = 'unknown error'; }
    if (bootPhase === 'download') {
      fail('The document could not be opened',
        'This course reads its file over HTTP, so it needs to run from an LMS or a web server rather ' +
        'than straight from the file system. If you are on a slow or intermittent connection, reloading ' +
        'the page will resume the download.' +
        '<br><br><small>Technical detail: ' + esc(detail) + '</small>');
    } else {
      fail('The document could not be displayed',
        'The file downloaded, but the reader hit a problem while preparing the pages. Reloading the ' +
        'page usually clears this. If it keeps happening, please send a screenshot of this message ' +
        'to support.' +
        '<br><br><small>Technical detail (' + esc(bootPhase) + '): ' + esc(detail) + '</small>');
    }
  });
}

/* The bar carries every always-on control, so its height is measured rather
   than assumed: if it wraps to a second row on a narrow screen, everything
   below it moves down to match. */
function sizeBar() {
  var bar = el('bar');
  if (!bar) { return; }
  var h = bar.offsetHeight;
  if (h > 0) { document.documentElement.style.setProperty('--bar', h + 'px'); }
}

/* --------------------------------------------------------------- events */

function bind() {
  dom = {
    stage: el('stage'), loading: el('loading'), panel: el('panel'), scrim: el('scrim'),
    bootBar: el('boot-bar'), bootNote: el('boot-note'),
    pageInput: el('page-input'), pageCount: el('page-count'), zoomLevel: el('zoom-level'),
    tabToc: el('tab-toc'), tabSearch: el('tab-search'),
    tabMarks: el('tab-marks'), tabThumbs: el('tab-thumbs'),
    toc: el('toc'), navGrid: el('nav-grid'), hits: el('hits'), marks: el('marks'),
    q: el('q'), thumbs: el('thumbs'),
    bookmarkBtn: el('bookmark'), quizBtn: el('quiz'),
    progress: el('progress'), scoreText: el('score-text'),
    searchNav: el('search-nav'), searchCount: el('search-count'),
    help: el('help-sheet'), menu: el('more-menu'),
    timerWrap: el('timer-wrap'), timerText: el('timer-text'), timerBtn: el('timer-toggle'),
    timerTarget: el('timer-target')
  };

  on(el('panel-close'), 'click', closePanel);
  on(dom.scrim, 'click', closePanel);
  on(el('search-open'), 'click', function () {
    openPanel(); showTab('search');
    setTimeout(function () { try { dom.q.focus(); } catch (e) { /* older browsers */ } }, 60);
  });
  on(el('prev'), 'click', function () { goTo(state.current - 1); });
  on(el('next'), 'click', function () { goTo(state.current + 1); });
  on(el('zoom-in'), 'click', function () { setZoom('scale', effectiveScale() * 1.25); });
  on(el('zoom-out'), 'click', function () { setZoom('scale', effectiveScale() / 1.25); });
  on(el('fit-width'), 'click', function () { setZoom('fit', 'width'); });
  on(el('fit-page'), 'click', function () { setZoom('fit', 'page'); });
  on(dom.bookmarkBtn, 'click', toggleMark);
  on(el('mark-add'), 'click', toggleMark);
  on(dom.quizBtn, 'click', function () { dom.menu.hidden = true; toggleQuiz(); });
  on(el('q-go'), 'click', runSearch);
  on(el('hit-prev'), 'click', function () { stepTo(hitAt - 1); });
  on(el('hit-next'), 'click', function () { stepTo(hitAt + 1); });
  on(el('help-close'), 'click', function () { dom.help.hidden = true; });
  on(el('results-close'), 'click', function () { el('results-sheet').hidden = true; });
  on(el('review-wrong'), 'click', reviewWrong);
  on(dom.timerBtn, 'click', timerToggle);
  on(el('timeup-dismiss'), 'click', function () { el('timeup').hidden = true; });
  on(el('analysis-close'), 'click', function () { el('analysis-sheet').hidden = true; });
  on(el('analysis-review'), 'click', reviewWeakest);
  on(el('m-analysis'), 'click', function () { dom.menu.hidden = true; showAnalysis(); });
  on(el('mm-analysis'), 'click', function () { dom.menu.hidden = true; showAnalysis(); });
  on(el('results-analyse'), 'click', function () {
    el('results-sheet').hidden = true;
    showAnalysis();
  });

  /* more menu */
  on(el('more-open'), 'click', function (e) {
    e.stopPropagation();
    dom.menu.hidden = !dom.menu.hidden;
    el('more-open').setAttribute('aria-expanded', String(!dom.menu.hidden));
  });
  on(document, 'click', function (e) {
    if (!dom.menu.hidden && !dom.menu.contains(e.target)) { dom.menu.hidden = true; }
  });
  on(el('m-toc'), 'click', function () { dom.menu.hidden = true; openPanel(); showTab('toc'); });
  on(el('m-thumbs'), 'click', function () { dom.menu.hidden = true; openPanel(); showTab('thumbs'); });
  on(el('m-marks'), 'click', function () { dom.menu.hidden = true; openPanel(); showTab('marks'); });
  on(el('speak'), 'click', function () { dom.menu.hidden = true; toggleSpeak(); });
  on(el('m-results'), 'click', function () { dom.menu.hidden = true; showResults(); });
  on(el('m-restart'), 'click', function () { dom.menu.hidden = true; restartAttempt(); });
  on(el('m-help'), 'click', function () { dom.menu.hidden = true; dom.help.hidden = false; });
  on(el('m-fullscreen'), 'click', function () {
    dom.menu.hidden = true;
    var d = document.documentElement;
    if (document.fullscreenElement || document.webkitFullscreenElement) {
      if (document.exitFullscreen) { document.exitFullscreen(); }
      else if (document.webkitExitFullscreen) { document.webkitExitFullscreen(); }
    } else if (d.requestFullscreen) { d.requestFullscreen(); }
    else if (d.webkitRequestFullscreen) { d.webkitRequestFullscreen(); }
    else { toast('This device does not allow full screen here.'); }
  });

  on(dom.q, 'keydown', function (e) { if (e.key === 'Enter' || e.keyCode === 13) { runSearch(); } });
  on(dom.pageInput, 'change', function () {
    var n = parseInt(dom.pageInput.value, 10);
    if (!isNaN(n)) { goTo(n); } else { dom.pageInput.value = String(state.current); }
  });

  var tabs = dom.panel.querySelectorAll('.tabs button');
  for (var i = 0; i < tabs.length; i++) {
    (function (b) { on(b, 'click', function () { showTab(b.getAttribute('data-tab')); }); })(tabs[i]);
  }

  if (!THUMBS_ON) { hideTab('thumbs'); el('m-thumbs').hidden = true; }
  if (!SPEAK_ON || !speech) { el('speak').hidden = true; }
  if (!QUIZ_ON) {
    el('m-results').hidden = true;
    el('m-restart').hidden = true;
    el('mh-study').hidden = true;
  }
  if (!QUIZ_ON || !ANALYSIS_ON) {
    el('m-analysis').hidden = true;
    el('mm-analysis').hidden = true;
    el('mh-study').hidden = true;
    el('results-analyse').hidden = true;
  }

  /* copy protection: the document may be read, not lifted */
  var guard = ['copy', 'cut', 'dragstart', 'contextmenu', 'selectstart'];
  for (i = 0; i < guard.length; i++) {
    on(document, guard[i], function (e) {
      var t = e.target;
      if (t && (t.tagName === 'INPUT' || t.tagName === 'TEXTAREA')) { return; }
      e.preventDefault();
    });
  }

  var scrollTimer = null;
  on(dom.stage, 'scroll', function () {
    clearTimeout(scrollTimer);
    scrollTimer = setTimeout(trackScroll, 110);
  }, { passive: true });

  var resizeTimer = null;
  on(window, 'resize', function () {
    clearTimeout(resizeTimer);
    resizeTimer = setTimeout(function () {
      sizeBar();
      if (state.fit) { layout(); goTo(state.current, false); }
    }, 220);
  });
  on(window, 'orientationchange', function () {
    setTimeout(function () { sizeBar(); if (state.fit) { layout(); goTo(state.current, false); } }, 350);
  });

  bindTouch();
  bindKeys();
  bindGuards();
  sizeBar();
}

function hideTab(name) {
  var b = dom.panel.querySelector('.tabs button[data-tab="' + name + '"]');
  if (b) { b.hidden = true; }
}

/* --------------------------------------------------- touch and pointing */

function bindTouch() {
  var lastTap = 0, lastX = 0, lastY = 0;
  var pinch = null;

  on(dom.stage, 'touchstart', function (e) {
    if (e.touches.length === 2) {
      pinch = {
        d: dist(e.touches[0], e.touches[1]),
        base: effectiveScale()
      };
      return;
    }
    var t = e.touches[0];
    var gap = now() - lastTap;
    if (gap < 320 && Math.abs(t.clientX - lastX) < 34 && Math.abs(t.clientY - lastY) < 34) {
      setZoom('fit', state.fit === 'page' ? 'width' : 'page');
      lastTap = 0;
    } else {
      lastTap = now();
      lastX = t.clientX;
      lastY = t.clientY;
    }
  }, { passive: true });

  on(dom.stage, 'touchmove', function (e) {
    if (pinch && e.touches.length === 2) {
      var d = dist(e.touches[0], e.touches[1]);
      pinch.next = clamp(pinch.base * (d / pinch.d), MIN_SCALE, MAX_SCALE);
      toast(Math.round(pinch.next * 100) + '%', 700);
      if (e.cancelable) { e.preventDefault(); }
      return;
    }
  }, { passive: false });

  on(dom.stage, 'touchend', function () {
    if (pinch) {
      if (pinch.next) { setZoom('scale', pinch.next); }
      pinch = null;
      return;
    }
  });

  on(dom.stage, 'wheel', function (e) {
    if (!e.ctrlKey) { return; }
    e.preventDefault();
    setZoom('scale', effectiveScale() * (e.deltaY < 0 ? 1.12 : 0.89));
  }, { passive: false });
}

function dist(a, b) {
  var dx = a.clientX - b.clientX, dy = a.clientY - b.clientY;
  return Math.sqrt(dx * dx + dy * dy);
}

/* -------------------------------------------------------------- keyboard */

function bindKeys() {
  on(document, 'keydown', function (e) {
    var t = e.target;
    if (t && (t.tagName === 'INPUT' || t.tagName === 'TEXTAREA')) {
      if (e.key === 'Escape') { t.blur(); }
      return;
    }
    if (BLOCK_PRNT && (e.ctrlKey || e.metaKey)) {
      var k = String(e.key || '').toLowerCase();
      if (k === 'p' || k === 's' || k === 'u') { e.preventDefault(); toast('Printing and saving are disabled for this course.'); return; }
      if (k === '+' || k === '=' ) { e.preventDefault(); setZoom('scale', effectiveScale() * 1.15); return; }
      if (k === '-') { e.preventDefault(); setZoom('scale', effectiveScale() / 1.15); return; }
    }
    switch (e.key) {
      case 'ArrowRight': case 'PageDown': goTo(state.current + 1); break;
      case 'ArrowLeft': case 'PageUp': goTo(state.current - 1); break;
      case 'Home': goTo(1); break;
      case 'End': goTo(state.total); break;
      case 'q': case 'Q': toggleQuiz(); break;
      case 'b': case 'B': toggleMark(); break;
      case 't': case 'T': if (TIMER_ON) { timerToggle(); } break;
      case 'f': case 'F': flagCurrent(); break;
      case '+': case '=': setZoom('scale', effectiveScale() * 1.15); break;
      case '-': case '_': setZoom('scale', effectiveScale() / 1.15); break;
      case '/': e.preventDefault(); openPanel(); showTab('search'); dom.q.focus(); break;
      case '?': dom.help.hidden = !dom.help.hidden; break;
      case 'Escape':
        dom.help.hidden = true;
        el('results-sheet').hidden = true;
        el('analysis-sheet').hidden = true;
        dom.menu.hidden = true;
        stopSpeak();
        closePanel();
        break;
      default: break;
    }
    if (e.key >= 'a' && e.key <= 'e' && !e.ctrlKey && !e.metaKey && state.quiz) {
      var q = questionAt(state.current);
      if (q && q.correct) { choose(q, e.key.toUpperCase()); }
    }
  });
}

/* ---------------------------------------------------------- extra guards */

function bindGuards() {
  if (BLOCK_PRNT) {
    on(window, 'beforeprint', function () { document.body.classList.add('blurred'); });
    on(window, 'afterprint', function () { document.body.classList.remove('blurred'); });
  }
  if (BLUR_BLUR) {
    on(window, 'blur', function () { el('privacy').hidden = false; });
    on(window, 'focus', function () { el('privacy').hidden = true; });
  }
  /* The stage is scrolled as well as paged, so a dwell that only refused the
     page buttons would be walked straight past with a flick. */
  if (DWELL_MS) { on(dom.stage, 'scroll', clampScroll); }
  on(document, 'visibilitychange', function () {
    if (document.hidden) { stopSpeak(); timerPause(true); flush(); }
  });
  on(window, 'pagehide', function () {
    RFA_GUARD.closing(); flush(); SCORM.close(); SCORM.terminate();
  });
  on(window, 'beforeunload', function () { RFA_GUARD.closing(); flush(); });
}

/* ----------------------------------------------------------------- boot */

if (document.readyState === 'loading') {
  document.addEventListener('DOMContentLoaded', function () { bind(); start(); });
} else {
  bind();
  start();
}

})();
