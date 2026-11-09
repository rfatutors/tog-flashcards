/* RFA Tutors guard layer.
   ------------------------------------------------------------------
   Everything the kit does ABOUT THE LEARNER rather than about the
   document: the trace code, the device code, where they are reading
   from, the watermark tile, the capture guard, the disclosure notice
   and the alerts. None of it knows what is on the page, which is why
   the same layer serves the PDF reader and the video player.

   The functions below are lifted verbatim from res/js/viewer.js so the
   two cannot drift in behaviour. If you change one, change the other -
   there is no build step that would catch it for you.

   The host page supplies four things through RFA_GUARD.init():
     scorm     the live SCORM wrapper (or null when run outside an LMS)
     save      a function the guard calls when it has changed something
     units     how long the material is, in whatever unit the capture
               threshold should be a share of - pages for the reader,
               minutes for the player
     where     an object the guard reads position from for its alerts,
               { at: <current>, seen: <covered> }
   and paints the watermark wherever it is told to. */

(function () {
'use strict';

var CFG = window.RFA_CONFIG || {};
function cfg(name, fallback) { return CFG[name] === undefined ? fallback : CFG[name]; }

var WM_ON      = cfg('watermark', true);
var WM_TEXT    = cfg('watermarkText', '');
var WM_STRONG  = cfg('strongWatermark', false);
var WM_ALPHA   = cfg('watermarkOpacity', 0);
var CAP_GUARD  = cfg('captureGuard', true);
var CAP_LOG    = cfg('captureLog', true);
var CAP_NOTICE = cfg('captureNotice', true);
var GEO_ON     = cfg('geoWatermark', true);          /* the place in the watermark */
var GEO_LOOKUP = cfg('geoLookup', GEO_ON);           /* the address lookup itself, which the session record and the sharing checks need; separable from the watermark */
var GEO_URL    = cfg('geoUrl', 'https://ipwho.is/');
var ALERT_URL  = cfg('alertUrl', '');
var ALERT_PCT  = Math.max(0, cfg('alertPercent', 0));
var SHARE_N    = Math.max(0, cfg('shareThreshold', 0));
var SHARE_H    = Math.max(1, cfg('shareWindowHours', 24));
var PATTERN_N  = Math.max(0, cfg('patternDays', 0));
var CITY_ON    = cfg('cityAlert', false);
var DEV_N      = Math.max(0, cfg('deviceAlert', 0));
var DEV_WARN   = Math.max(0, cfg('deviceWarn', 0));
var DEV_KEEP   = 30 * 24;
/* Count machines by what they are, not by how many codes they have been
   given. A private window mints a fresh code every time it opens, so one
   phone used in three private tabs was arriving as "3 devices" - the
   commonest false alarm this kit produces. Counting distinct signatures
   (platform, screen size, browser) collapses those back into one.
   --device-strict counts the codes instead, which is stricter and noisier. */
var DEV_STRICT = cfg('deviceStrict', false);
var TURNS_N    = Math.max(0, cfg('turns', 0));
var TURNS_H    = Math.max(1, cfg('turnsWindowHours', 24));
var DEV_KEY    = 'rfa.device';
/* --test-alert: fire one alert the moment the course opens, so the whole
   chain - package, network, endpoint, mailer, inbox - can be proved in one
   go instead of guessing which link is broken. Build a throwaway package
   with it, open it once, then rebuild without it. */
var TEST_ALERT = cfg('testAlert', false);
/* ---- v5: sessions, fingerprint, first-capture alert, chord heuristic ----
   sessions        POST a session-open, a heartbeat every HEARTBEAT_S seconds
                   of reading, and a session-close, to the alert endpoint. The
                   mailer turns these into a per-learner timeline and does the
                   sharing analysis server-side, across every unit at once.
   fingerprint     derive the device code from what the machine IS (screen,
                   GPU, cores, memory, time zone...) rather than a random
                   number in storage, so a browser that clears its storage
                   comes back as the same device instead of a new one.
   alertFirstCapture  the first capture attempt in a unit is reported at
                   once; later ones follow the percent rule.
   chordHeuristic  on a Mac the OS swallows Cmd+Shift+3/4/5 before the page
                   sees the digit; on Windows Win+Shift+S is swallowed the
                   same way. Both leave a tell-tale: the modifiers go down
                   and come back up with no other key in between. Counted as
                   a SUSPECTED capture and labelled as such. */
var SESSIONS_ON = cfg('sessions', true);
var HEARTBEAT_S = Math.max(30, cfg('heartbeatSeconds', 300));
var FP_ON       = cfg('fingerprint', true);
var ALERT_FIRST = cfg('alertFirstCapture', true);
var CHORD_ON    = cfg('chordHeuristic', true);
/* Reading time only counts while someone is there: a tab left open all day
   with nobody at it would otherwise read as fourteen hours of study. Any
   input, or the host reporting progress (a page turn, a playing video),
   keeps the clock running; after IDLE_S seconds without either it stops
   until the next sign of life. */
var IDLE_S      = Math.max(60, cfg('idleSeconds', 600));
var NOTICE_KEY = 'rfa.notice';
var STORE_KEY  = 'rfa.' + (cfg('id', 'COURSE'));
/* 'document' or 'video' - only the wording the learner reads changes */
var KIND       = cfg('mediaKind', 'document');
var UNIT       = (KIND === 'video') ? 'frame' : 'page';
var WHOLE      = (KIND === 'video') ? 'video' : 'document';
/* Black ink over a page, white over a picture. Drawn with difference
   blending in the player, white ink stays legible on a dark frame and on a
   bright one, which black ink does on neither. */
var WM_INK     = cfg('watermarkInk', (KIND === 'video') ? '#fff' : '#000');

/* ------------------------------------------------------------- helpers */

function el(id) { return document.getElementById(id); }
function on(node, evt, fn, opts) { if (node) { node.addEventListener(evt, fn, opts || false); } }
function now() { return (new Date()).getTime(); }
/* scrubClipboard's fallback path needs this. It went missing when the guard
   was split out of the reader, and because that path is wrapped in a
   try/catch the failure was silent - the clipboard scrub simply stopped
   happening on any browser without navigator.clipboard, which is precisely
   the older Windows machines the Print Screen scrub exists for. */
function make(tag, cls) {
  var n = document.createElement(tag);
  if (cls) { n.className = cls; }
  return n;
}
function esc(s) {
  return String(s).replace(/[&<>"]/g, function (c) {
    return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c];
  });
}

var SCORM = null;
var live = false;
var save = function () { };

var state = {
  total: 0, current: 0, seenCount: 0, locked: false,
  places: [], days: [], devs: [], visits: [], devWarn: 0,
  guard: { cap: 0, blur: 0, fast: 0, sent: 0, alert: 0, share: 0,
           streak: 0, city: 0, dev: 0, viol: 0, turns: 0 }
};

var geo = { place: '', ip: '', isp: '', lat: '', lon: '', zone: '' };   /* place is set by the lookup only; zone is the watermark's fallback */
var traceCode = null;
var devId = null;
var wmTile = null;
var stampCache = {};
var shieldTimer = null;
var lastCap = 0;
var lastArmed = 0;
var wmTargets = [];

/* How much misbehaviour earns a row in the LMS report, and how the bar
   rises so one restless learner does not file four rows a minute.
   (This constant was left behind when the guard was split out of the
   reader: noteGuard threw a ReferenceError on the FIRST capture attempt,
   which took alertCapture, armNotice and save down with it - captures were
   counted in memory and then lost. Nothing in a syntax check sees this.) */
var GUARD_TIERS = [8, 24, 60, 150];

/* One learner must not be able to empty your inbox. A capture alert fires
   every half-document, so a determined page-masher on a forty-page paper
   would otherwise post fifty times in a session - more than a consumer
   Gmail account will even send in a day. Past this many, the LMS report
   rows carry on as the record and the e-mails stop. */
var ALERT_MAX = 6;
var alertsOut = 0;

/* ---- what the machine is ------------------------------------------------

   No browser will give a page the IMEI, serial number or MAC address, and
   none ever will. What it does give is enough small facts about the machine
   - screen, pixel density, cores, memory, the GPU's own name, how a canvas
   renders text, time zone, language, touch - that hashed together they name
   one device with fair confidence. Two identical phones of the same model,
   OS and browser hash alike: that is the honest limit, and the address
   checks are what cover it. */

function fnv(str) {
  var h = 0x811c9dc5, i;
  for (i = 0; i < str.length; i++) {
    h ^= str.charCodeAt(i);
    h = (h + ((h << 1) + (h << 4) + (h << 7) + (h << 8) + (h << 24))) >>> 0;
  }
  return h;
}

var gpuName = null;
function gpu() {
  if (gpuName !== null) { return gpuName; }
  gpuName = '';
  try {
    var c = document.createElement('canvas');
    var g = c.getContext('webgl') || c.getContext('experimental-webgl');
    if (g) {
      var dbg = g.getExtension('WEBGL_debug_renderer_info');
      gpuName = String(dbg ? g.getParameter(dbg.UNMASKED_RENDERER_WEBGL) : g.getParameter(g.RENDERER) || '').slice(0, 80);
    }
  } catch (e) { gpuName = ''; }
  return gpuName;
}

function canvasHash() {
  try {
    var c = document.createElement('canvas');
    c.width = 220; c.height = 40;
    var x = c.getContext('2d');
    x.textBaseline = 'alphabetic';
    x.fillStyle = '#f60'; x.fillRect(90, 2, 60, 20);
    x.fillStyle = '#069'; x.font = '15px Arial'; x.fillText('RFA Tutors \u00a9 \u0645\u0631\u062d\u0628\u0627 1O0l', 4, 22);
    x.fillStyle = 'rgba(102,204,0,0.7)'; x.font = '17px Georgia'; x.fillText('RFA Tutors \u00a9 1O0l', 6, 36);
    return fnv(c.toDataURL()).toString(36);
  } catch (e) { return ''; }
}

function braveLike() {
  try { return !!(navigator.brave && navigator.brave.isBrave); } catch (e) { return false; }
}

/* The machine without the browser. Only traits that Chrome, Safari, Edge
   and Firefox all report the same way on the same hardware go in, so one
   computer opened in two browsers gets one key:
     device type, OS family, screen size (longer side x shorter side, so
     rotation does not matter), colour depth, touch points, CPU cores (capped
     at 8, the most Safari will admit to), and on phones and tablets the
     pixel ratio (fixed on a phone; on a desktop it moves with browser zoom).
   Left OUT on purpose: the GPU string (each browser spells it differently),
   memory (Chrome only), canvas and fonts (rendering differs), time zone and
   language (travel), and anything stored in the browser (not shared between
   browsers). Two different machines of the same model and screen share a
   key - that is the price of never splitting one machine in two. */
function osFamily() {
  var ua = String(navigator.userAgent || '');
  return /iPhone|iPad|iPod/.test(ua) ? 'iOS' : /Android/.test(ua) ? 'Android' : /Windows/.test(ua) ? 'Windows'
       : /Mac OS X/.test(ua) ? 'Mac' : /CrOS/.test(ua) ? 'ChromeOS' : /Linux/.test(ua) ? 'Linux' : 'other';
}

var hwCode = null;
function hardwareKey() {
  if (hwCode !== null) { return hwCode; }
  var bits = [], w = 0, h = 0, type = deviceType();
  try { w = screen.width || 0; h = screen.height || 0; } catch (e) { }
  try {
    bits.push(type);
    bits.push(osFamily());
    bits.push(Math.max(w, h) + 'x' + Math.min(w, h));
    bits.push(String(screen.colorDepth || 0));
    bits.push(String(navigator.maxTouchPoints || 0));
    bits.push(String(Math.min(8, navigator.hardwareConcurrency || 0)));
    bits.push((type === 'phone' || type === 'tablet') ? String(Math.round((window.devicePixelRatio || 1) * 100) / 100) : '');
  } catch (e2) { }
  var hsh = fnv(bits.join('|')).toString(36).toUpperCase();
  while (hsh.length < 6) { hsh = '0' + hsh; }
  hwCode = hsh.slice(0, 6);
  return hwCode;
}

var fpCode = null;
function fingerprint() {
  if (fpCode !== null) { return fpCode; }
  var bits = [];
  try {
    bits.push(navigator.platform || '');
    bits.push((screen.width || 0) + 'x' + (screen.height || 0) + 'x' + (screen.colorDepth || 0));
    bits.push(String(window.devicePixelRatio || 1));
    bits.push(String(navigator.hardwareConcurrency || 0));
    bits.push(String(navigator.deviceMemory || 0));
    bits.push(String(navigator.maxTouchPoints || 0));
    bits.push(gpu());
    /* zone and language are reported separately; leaving them out keeps the
       code stable when a learner travels or changes the phone's language */
    bits.push(braveLike() ? 'no-canvas' : canvasHash());   /* Brave randomises canvas: skip it */
    bits.push(deviceLabel());
  } catch (e) { /* whatever was collected */ }
  var h = fnv(bits.join('|')).toString(36).toUpperCase();
  while (h.length < 6) { h = '0' + h; }
  fpCode = h.slice(0, 8);
  return fpCode;
}

/* phone / tablet / desktop from touch and size; an iPad that calls itself a
   Mac has touch points, a real Mac has none */
function deviceType() {
  var touch = 0, w = 0, h = 0, ua = String(navigator.userAgent || '');
  try { touch = navigator.maxTouchPoints || 0; w = screen.width || 0; h = screen.height || 0; } catch (e) { }
  var small = Math.min(w, h), big = Math.max(w, h);
  if (/iPhone|iPod/.test(ua)) { return 'phone'; }
  if (/iPad/.test(ua) || (/Mac OS X/.test(ua) && touch > 1)) { return 'tablet'; }
  if (/Android/.test(ua)) { return (/Mobile/.test(ua) || small < 600) ? 'phone' : 'tablet'; }
  if (/Windows|Mac OS X|CrOS/.test(ua)) { return 'desktop'; }   /* a touch-screen laptop is still a laptop */
  if (touch > 1 && big <= 1400) { return small < 600 ? 'phone' : 'tablet'; }
  return 'desktop';
}

var modelName = '';
/* Android Chrome reports the real model (SM-S918B) only through the
   high-entropy hints; the user-agent string says "K" for every phone. */
function learnModel() {
  try {
    var d = navigator.userAgentData;
    if (!d || !d.getHighEntropyValues) { return; }
    d.getHighEntropyValues(['model', 'platformVersion', 'architecture']).then(function (v) {
      var m = String((v && v.model) || '').slice(0, 40);
      var pv = String((v && v.platformVersion) || '').slice(0, 12);
      modelName = (m ? m : '') + (pv ? (m ? ' \u00b7 ' : '') + 'v' + pv : '');
    })['catch'](function () { });
  } catch (e) { /* not this browser */ }
}

function deviceProfile() {
  var p = { fp: FP_ON ? fingerprint() : '', hw: FP_ON ? hardwareKey() : '', brave: braveLike(), code: deviceId(), label: deviceLabel(), type: deviceType(), os: osFamily(), colorDepth: 0,
            model: modelName, tz: zoneName(), lang: '', screen: '', dpr: 0, touch: 0, cores: 0, mem: 0, gpu: gpu() };
  try {
    p.lang = String(navigator.language || '').slice(0, 12);
    p.screen = (screen.width || 0) + 'x' + (screen.height || 0);
    p.dpr = Math.round((window.devicePixelRatio || 1) * 100) / 100;
    p.touch = navigator.maxTouchPoints || 0;
    p.colorDepth = screen.colorDepth || 0;
    p.cores = navigator.hardwareConcurrency || 0;
    p.mem = navigator.deviceMemory || 0;
  } catch (e) { }
  return p;
}

function deviceId() {
  if (devId !== null) { return devId; }
  devId = '';
  try {
    var store = window.localStorage;
    if (!store) { return devId; }
    var held = store.getItem(DEV_KEY);
    if (!held) {
      /* derived from the fingerprint, so cleared storage or a private window
         reproduces the same code instead of minting a fresh one */
      held = FP_ON ? fingerprint().slice(0, 4) : (Math.floor(Math.random() * 1679616)).toString(36).toUpperCase();
      while (held.length < 4) { held = '0' + held; }
      store.setItem(DEV_KEY, held);
      if (store.getItem(DEV_KEY) !== held) { return devId; }   /* wrote nothing */
    }
    devId = String(held).slice(0, 8);
  } catch (e) { devId = ''; }      /* private mode, blocked storage, partitioned iframe */
  return devId;
}

function deviceLabel() {
  var ua = String(navigator.userAgent || '');
  var os = /Windows/.test(ua) ? 'Windows'
         : /iPhone|iPad|iPod/.test(ua) ? 'iOS'
         : /Android/.test(ua) ? 'Android'
         : /Mac OS X/.test(ua) ? 'Mac'
         : /Linux/.test(ua) ? 'Linux' : 'unknown';
  var br = /EdgiOS\/|Edg\//.test(ua) ? 'Edge'
         : /CriOS\//.test(ua) ? 'Chrome'
         : /FxiOS\//.test(ua) ? 'Firefox'
         : /OPiOS\/|OPR\//.test(ua) ? 'Opera'
         : /Chrome\//.test(ua) ? 'Chrome'
         : /Firefox\//.test(ua) ? 'Firefox'
         : /Safari\//.test(ua) ? 'Safari' : 'browser';
  var size = '';
  try { size = (screen.width || 0) + '\u00d7' + (screen.height || 0); } catch (e) { size = ''; }
  return (os + ' \u00b7 ' + (size ? size + ' \u00b7 ' : '') + br).slice(0, 40);
}

/* The distinct machines behind a list of device codes, newest first. */
function deviceSignatures(list) {
  var seen = {}, out = [], i, lab;
  for (i = 0; i < list.length; i++) {
    lab = list[i][1] || 'unknown device';
    if (!seen[lab]) { seen[lab] = 1; out.push(lab); }
  }
  return out;
}

function noteDevice() {
  if (!DEV_N) { return; }
  var id = deviceId();
  if (!id) { return; }
  var hour = Math.floor(now() / 3600000), list = state.devs, i, seen = false;
  for (i = 0; i < list.length; i++) {
    if (list[i][0] === id) { list[i][1] = deviceLabel(); list[i][2] = hour; seen = true; }
  }
  if (!seen) { list.push([id, deviceLabel(), hour]); }

  var kept = [];
  for (i = 0; i < list.length; i++) {
    if (list[i][2] >= hour - DEV_KEEP) { kept.push(list[i]); }
  }
  kept.sort(function (a, b) { return b[2] - a[2]; });
  if (kept.length > 6) { kept = kept.slice(0, 6); }
  state.devs = kept;

  var sigs = deviceSignatures(kept);
  var count = DEV_STRICT ? kept.length : sigs.length;

  /* The learner is told at their own threshold, which is deliberately above
     the one that tells you: the first extra device is between you and the
     report, the next one is worth saying out loud. */
  if (DEV_WARN && count >= DEV_WARN) { state.devWarn = count; }

  if (count < DEV_N || count <= state.guard.dev) { save(); return; }
  state.guard.dev = count;

  var names = [];
  for (i = 0; i < kept.length; i++) { names.push(kept[i][0] + ' (' + kept[i][1] + ')'); }
  var detail = 'opened on ' + count + ' different device' + (count === 1 ? '' : 's') +
               ': ' + sigs.join(' / ');
  if (!DEV_STRICT && kept.length > count) {
    detail += ' \u2014 ' + kept.length + ' codes in all, so ' + (kept.length - count) +
              ' of them are repeat visits from a machine already counted ' +
              '(usually private windows or cleared site data)';
  }
  if (CAP_LOG && live && SCORM.flag) { SCORM.flag('SHARING', 'trace=' + trace() + ' ' + detail); }
  if (ALERT_URL) { sendAlert('device-sharing', detail, addressList(state.places, 6)); }
  armNotice();
  save();
}

function zoneName() {
  var z = '';
  try {
    if (window.Intl && Intl.DateTimeFormat) {
      z = Intl.DateTimeFormat().resolvedOptions().timeZone || '';
    }
  } catch (e) { z = ''; }
  if (z) { return z.replace(/_/g, ' '); }
  var off = -(new Date().getTimezoneOffset()) / 60;
  return 'UTC' + (off >= 0 ? '+' : '') + off;
}

function geoText() {
  if (!GEO_ON) { return ''; }
  var s = geo.place || geo.zone || '';
  if (geo.ip) { s = s ? s + ' \u00b7 ' + geo.ip : geo.ip; }
  return s.slice(0, 60);
}

function geoStart() {
  geo.zone = zoneName();
  if (!GEO_LOOKUP) { return; }
  if (!GEO_URL || !window.XMLHttpRequest) { return; }
  var x = new XMLHttpRequest();
  try {
    x.open('GET', GEO_URL, true);
    x.timeout = 6000;
    x.onreadystatechange = function () {
      if (x.readyState !== 4 || x.status !== 200) { return; }
      var d = null;
      try { d = JSON.parse(x.responseText); } catch (e) { return; }
      if (!d || typeof d !== 'object') { return; }
      /* ipwho.is, ipapi.co, ipinfo.io and geojs all spell these differently. */
      var city = d.city || d.region || d.region_name || '';
      var land = d.country_code || d.country_code2 || d.country || '';
      if (String(land).length > 3) { land = d.country_code || ''; }
      var place = city ? (land ? city + ', ' + land : city) : String(land || '');
      if (place) { geo.place = place; }
      if (d.ip) { geo.ip = String(d.ip).slice(0, 45); }
      /* the network owner, so the mailer need not look the address up itself */
      var c = d.connection || {};
      geo.isp = String(c.isp || c.org || d.isp || d.org || d.asn_org || '').slice(0, 60);
      /* the address's map position (the provider's area, not the house) */
      var la = parseFloat(d.latitude !== undefined ? d.latitude : d.lat), lo = parseFloat(d.longitude !== undefined ? d.longitude : d.lon);
      if (!isNaN(la) && !isNaN(lo)) { geo.lat = Math.round(la * 1000) / 1000; geo.lon = Math.round(lo * 1000) / 1000; }
      watermarkRepaint();
      noteLocation();
    };
    x.send(null);
  } catch (e2) { /* blocked outright: the time zone stands */ }
}

function ipHash(str) {
  var h = 0x811c9dc5, i;
  for (i = 0; i < str.length; i++) {
    h ^= str.charCodeAt(i);
    h = (h + ((h << 1) + (h << 4) + (h << 7) + (h << 8) + (h << 24))) >>> 0;
  }
  return h.toString(36).slice(0, 5);
}

function landOf(place) {
  var bits = String(place || '').split(', ');
  return (bits.length > 1 ? bits[bits.length - 1] : bits[0] || '').slice(0, 12);
}

function keepHours() {
  var pattern = (PATTERN_N ? 8 * 24 : 0);
  return Math.max(SHARE_H, pattern, CITY_ON ? 8 * 24 : 0, TURNS_N ? TURNS_H : 0);
}

function noteLocation() {
  /* every location check that exists has to appear here, or switching the
     others off silently switches this one off too */
  if ((!SHARE_N && !PATTERN_N && !CITY_ON && !TURNS_N) || !geo.ip) { return; }
  var key = ipHash(geo.ip);                    /* a time zone is not an address */
  var place = String(geo.place || '').slice(0, 40);
  var hour = Math.floor(now() / 3600000);
  var list = state.places, i, seen = false;
  for (i = 0; i < list.length; i++) {
    if (list[i][0] === key) { list[i][1] = place; list[i][2] = hour; seen = true; }
  }
  if (!seen) { list.push([key, place, hour, String(geo.ip).slice(0, 45)]); }

  var kept = [];
  for (i = 0; i < list.length; i++) {
    if (list[i][2] >= hour - keepHours()) { kept.push(list[i]); }
  }
  kept.sort(function (a, b) { return b[2] - a[2]; });
  if (kept.length > 12) { kept = kept.slice(0, 12); }
  state.places = kept;

  noteDay(key, hour);
  noteVisit(key, hour);
  checkSharing(kept, hour);
  checkTurns();
  checkPattern();
  checkCity(kept);
  save();
}

function noteDay(key, hour) {
  var d = Math.floor(hour / 24), days = state.days, i, rec = null;
  for (i = 0; i < days.length; i++) { if (days[i][0] === d) { rec = days[i]; } }
  if (!rec) { rec = [d]; days.push(rec); }
  if (rec.length < 4 && indexOfFrom(rec, key, 1) < 0) { rec.push(key); }
  days.sort(function (a, b) { return b[0] - a[0]; });
  if (days.length > 8) { days = days.slice(0, 8); }
  state.days = days;
}

function indexOfFrom(arr, v, from) {
  for (var i = from; i < arr.length; i++) { if (arr[i] === v) { return i; } }
  return -1;
}

function changedDays() {
  var days = state.days.slice(), seen = {}, count = 0, i, j, fresh;
  days.sort(function (a, b) { return a[0] - b[0]; });   /* oldest first */
  for (i = 0; i < days.length; i++) {
    fresh = false;
    for (j = 1; j < days[i].length; j++) {
      if (!seen[days[i][j]]) { seen[days[i][j]] = 1; fresh = true; }
    }
    if (fresh) { count++; }
  }
  return count;
}

function addressList(list, n) {
  var out = [], i;
  for (i = 0; i < list.length && i < n; i++) {
    out.push({ ip: list[i][3] || '', place: list[i][1] || '',
               day: dayStamp(list[i][2]) });
  }
  return out;
}

function dayStamp(hour) {
  return new Date(hour * 3600000).toISOString().slice(0, 10);
}

/* ---- one account, two people taking turns ------------------------------

   The checks above all ask "how many different places?". This one asks a
   better question for the case they miss: does the account keep GOING BACK?

   Two houses a street apart look identical to every place field a lookup
   returns - same city, same postal code, often the same coordinates, because
   those describe the ISP's area and not the house. What differs is the
   public address itself. So instead of measuring distance, this watches the
   order: A, then B, then A again, then B again is two people passing one
   login back and forth. A single learner who leaves home and picks up mobile
   data changes address once and stays there; they do not ping-pong.

   A "return" is a session from an address this account used before, with a
   different address in between. Three of those inside the window is the
   default, which one person's day does not usually produce and two people
   sharing one login produce almost immediately. */

function pad2(n) { return (n < 10 ? '0' : '') + n; }

function noteVisit(key, hour) {
  if (!TURNS_N) { return; }
  var v = state.visits, i;
  /* one row per session, not one per lookup */
  if (v.length && v[v.length - 1][0] === key && v[v.length - 1][1] === hour) { return; }
  v.push([key, hour]);
  var fresh = [];
  for (i = 0; i < v.length; i++) { if (v[i][1] >= hour - TURNS_H) { fresh.push(v[i]); } }
  if (fresh.length > 14) { fresh = fresh.slice(fresh.length - 14); }
  state.visits = fresh;
}

/* A return is a session from an address used before, with a different one
   in between. A-B-A is one; A-B-A-B is two; A-A-A is none. */
function countReturns(v) {
  var returns = 0, i, j, earlier;
  for (i = 1; i < v.length; i++) {
    if (v[i][0] === v[i - 1][0]) { continue; }        /* no switch at all */
    earlier = false;
    for (j = i - 2; j >= 0; j--) {
      if (v[j][0] === v[i][0]) { earlier = true; break; }
    }
    if (earlier) { returns++; }
  }
  return returns;
}

function checkTurns() {
  if (!TURNS_N) { return; }
  var v = state.visits, returns = countReturns(v), g = state.guard, i, p;
  if (returns < g.turns) { g.turns = returns; }       /* the run broke: arm it again */
  if (returns < TURNS_N || returns <= g.turns) { return; }
  g.turns = returns;

  var byKey = {}, order = [];
  for (i = 0; i < state.places.length; i++) { byKey[state.places[i][0]] = state.places[i]; }
  for (i = 0; i < v.length; i++) {
    p = byKey[v[i][0]];
    order.push(dayStamp(v[i][1]) + ' ' + pad2(v[i][1] % 24) + ':00 ' +
               (p ? (p[3] || p[0]) : v[i][0]) + (p && p[1] ? ' (' + p[1] + ')' : ''));
  }
  var detail = 'the account kept going back and forth between addresses (' + returns +
               ' returns in ' + TURNS_H + 'h): ' + order.join(' \u2192 ');
  if (CAP_LOG && live && SCORM.flag) {
    SCORM.flag('SHARING', 'trace=' + trace() + ' turn-taking, ' + returns + ' returns');
  }
  if (ALERT_URL) { sendAlert('turn-taking', detail, addressList(state.places, 8)); }
}

function checkSharing(kept, hour) {
  if (!SHARE_N) { return; }
  var fresh = [], lands = {}, nLands = 0, i;
  for (i = 0; i < kept.length; i++) {
    if (kept[i][2] >= hour - SHARE_H) { fresh.push(kept[i]); }
  }
  var land;
  for (i = 0; i < fresh.length; i++) {
    land = landOf(fresh[i][1]);
    if (land && !lands[land]) { lands[land] = 1; nLands++; }
  }
  var tripped = (fresh.length >= SHARE_N) || (nLands >= 2);
  if (!tripped || fresh.length <= state.guard.share) { return; }
  state.guard.share = fresh.length;

  var where = [];
  for (i = 0; i < fresh.length; i++) { where.push(fresh[i][0] + '@' + (landOf(fresh[i][1]) || '?')); }
  var detail = fresh.length + ' addresses in ' + SHARE_H + 'h' +
               (nLands >= 2 ? ', ' + nLands + ' countries' : '') + ' [' + where.join(' ') + ']';
  if (CAP_LOG && live && SCORM.flag) { SCORM.flag('SHARING', 'trace=' + trace() + ' ' + detail); }
  if (ALERT_URL) { sendAlert('sharing', detail, addressList(fresh, 6)); }
  armNotice();
}

function checkPattern() {
  if (!PATTERN_N) { return; }
  var n = changedDays(), g = state.guard;
  if (n < PATTERN_N || n <= g.streak) { return; }
  g.streak = n;

  var detail = 'a new address on ' + n + ' separate days';
  if (CAP_LOG && live && SCORM.flag) { SCORM.flag('SHARING', 'trace=' + trace() + ' ' + detail); }
  if (ALERT_URL) { sendAlert('daily-pattern', detail, addressList(state.places, 10)); }
  armNotice();
}

function checkCity(kept) {
  if (!CITY_ON) { return; }
  var cities = {}, order = [], n = 0, i, c;
  for (i = 0; i < kept.length; i++) {
    c = kept[i][1];
    if (!c || c.indexOf(',') < 0) { continue; }   /* country only: not a city */
    if (!cities[c]) { cities[c] = 1; order.push(c); n++; }
  }
  if (n < 2 || n <= state.guard.city) { return; }
  state.guard.city = n;

  var detail = 'opened from ' + n + ' different cities: ' + order.join(' / ');
  if (CAP_LOG && live && SCORM.flag) { SCORM.flag('SHARING', 'trace=' + trace() + ' URGENT ' + detail); }
  if (ALERT_URL) { sendAlert('city-change', detail, addressList(kept, 10)); }
  armNotice();
}

function trace() {
  if (traceCode !== null) { return traceCode; }
  var who = '';
  if (live) { who = String(SCORM.learnerId() || SCORM.learnerName() || ''); }
  var seed = (who || String(WM_TEXT || 'anon')) + '|' + String(cfg('id', 'COURSE'));
  var h = 0x811c9dc5, i;                      /* FNV-1a, 32-bit */
  for (i = 0; i < seed.length; i++) {
    h ^= seed.charCodeAt(i);
    h = (h + ((h << 1) + (h << 4) + (h << 7) + (h << 8) + (h << 24))) >>> 0;
  }
  var s = h.toString(36).toUpperCase();
  while (s.length < 6) { s = '0' + s; }
  traceCode = s.slice(0, 6);
  return traceCode;
}

function watermarkTile() {
  if (wmTile !== null) { return wmTile; }
  var name = String(WM_TEXT || (live ? SCORM.learnerName() : '') || 'RFA Tutors');
  var id = live ? String(SCORM.learnerId() || '') : '';   /* username / e-mail */
  var lines = [(name + ' \u00b7 ' + new Date().toISOString().slice(0, 10)).slice(0, 60)];
  if (id) { lines.push(id.slice(0, 60)); }
  if (WM_STRONG) {
    lines.push('TRACE ' + trace() + (deviceId() ? ' \u00b7 ' + deviceId() : ''));
  }
  if (geoText()) { lines.push(geoText()); }

  var deg = WM_STRONG ? 34 : 28;
  var size = WM_STRONG ? 16 : 15;
  var gap = WM_STRONG ? 26 : 44;              /* smaller gap = denser tiling */
  var lead = size + 7;
  var chars = 0, i;
  for (i = 0; i < lines.length; i++) { chars = Math.max(chars, lines[i].length); }
  /* Size the tile to the rotated text so nothing is clipped: the rotated
     bounding box of a W x H block at d degrees is
     W cos d + H sin d  by  W sin d + H cos d, plus the gap between repeats. */
  var textW = chars * (size * 0.57) + 20;
  var textH = lines.length * lead;
  var rad = deg * Math.PI / 180;
  var w = Math.ceil(textW * Math.cos(rad) + textH * Math.sin(rad)) + gap;
  var h = Math.ceil(textW * Math.sin(rad) + textH * Math.cos(rad)) + gap;
  var cx = w / 2, cy = h / 2;
  var top = cy - ((lines.length - 1) * lead) / 2 + size * 0.36;
  var body = '';
  for (i = 0; i < lines.length; i++) {
    body += '<text x="' + cx + '" y="' + (top + i * lead).toFixed(1) + '">' + esc(lines[i]) + '</text>';
  }
  var svg = '<svg xmlns="http://www.w3.org/2000/svg" width="' + w + '" height="' + h + '">' +
    '<g transform="rotate(-' + deg + ' ' + cx + ' ' + cy + ')" fill="' + WM_INK + '" ' +
    'font-family="Helvetica,Arial,sans-serif" font-size="' + size + '" letter-spacing="1" ' +
    'text-anchor="middle">' + body + '</g></svg>';
  wmTile = 'url("data:image/svg+xml;charset=utf-8,' + encodeURIComponent(svg) + '")';
  return wmTile;
}

function stampTile(n) {
  if (stampCache[n]) { return stampCache[n]; }
  var txt = trace() + (deviceId() ? ' \u00b7 ' + deviceId() : '') + ' \u00b7 p' + n;
  var w = txt.length * 6 + 16, h = 18;
  var svg = '<svg xmlns="http://www.w3.org/2000/svg" width="' + w + '" height="' + h + '">' +
    '<text x="' + (w - 7) + '" y="13" fill="' + WM_INK + '" font-family="Helvetica,Arial,sans-serif" ' +
    'font-size="10" letter-spacing="0.6" text-anchor="end">' + esc(txt) + '</text></svg>';
  stampCache[n] = 'url("data:image/svg+xml;charset=utf-8,' + encodeURIComponent(svg) + '")';
  return stampCache[n];
}

function wmPhase(n, salt) {
  var code = trace(), h = 0, i;
  for (i = 0; i < code.length; i++) { h = (h * 31 + code.charCodeAt(i)) >>> 0; }
  return (h + n * salt) % (salt === 17 ? 47 : 61);
}

function noticeGet(k) {
  try { return window.localStorage.getItem(k); } catch (e) { }
  try { return window.sessionStorage.getItem(k); } catch (e2) { }
  return null;
}

function noticeSet(k, v) {
  try { window.localStorage.setItem(k, v); return; } catch (e) { }
  try { window.sessionStorage.setItem(k, v); } catch (e2) { /* nothing persists */ }
}

function noticeDue() {
  if (!noticeGet(NOTICE_KEY)) { return true; }            /* never seen at all */
  var acked = parseInt(noticeGet(NOTICE_KEY + '.' + cfg('id', 'C')) || '0', 10);
  if (isNaN(acked)) { acked = 0; }
  return state.guard.viol > acked;                        /* earned another one */
}

function ackNotice() {
  noticeSet(NOTICE_KEY, '1');
  noticeSet(NOTICE_KEY + '.' + cfg('id', 'C'), String(state.guard.viol));
}

function armNotice() {
  state.guard.viol++;
  if (!CAP_NOTICE) { return; }
  if (now() - lastArmed < 60000) { return; }
  lastArmed = now();
  setTimeout(showNotice, 2600);                           /* after the shield clears */
}

function showNotice() {
  if (!CAP_NOTICE && !state.devWarn) { return; }
  var box = el('capture-notice');
  if (!box) { return; }
  var line = el('notice-text');

  /* The device warning outranks the standard notice and is shown every
     session it applies to, not once: it is the only thing here the learner
     is expected to act on. */
  if (state.devWarn) {
    if (line) {
      line.textContent = 'This login has now been opened on ' + state.devWarn +
        ' different devices. Your RFA Tutors account is for you alone. Every ' +
        UNIT + ' carries your name, a code for this device and where it is being ' +
        'viewed from, and this has been recorded against your account. If someone ' +
        'else is using your login, ask them to stop.';
    }
    box.hidden = false;
    return;
  }

  if (!CAP_NOTICE || !noticeDue()) { return; }
  var who = String(WM_TEXT || (live ? SCORM.learnerName() : '') || '');
  if (line) {
    line.textContent = 'Every ' + UNIT + ' of this ' + WHOLE + ' is watermarked' +
      (who ? ' with your name, ' + who + ',' : '') + ' and carries the code ' + trace() +
      (deviceId() ? ', a code for this device' : '') +
      (GEO_ON ? ', the date and the place you are watching from' : '') +
      '. Screenshots' + (KIND === 'video' ? ' and recordings' : ' and forwarded copies') +
      ' can be traced back to this account.';
  }
  box.hidden = false;
}

function shield(msg, ms) {
  var box = el('capture-shield');
  if (!box) { return; }
  var txt = el('shield-text');
  if (txt) { txt.textContent = msg; }
  box.hidden = false;
  clearTimeout(shieldTimer);
  if (ms) { shieldTimer = setTimeout(function () { if (!state.locked) { box.hidden = true; } }, ms); }
}

function unshield() {
  var box = el('capture-shield');
  if (box && !state.locked) { clearTimeout(shieldTimer); box.hidden = true; }
}

function scrubClipboard() {
  var note = 'Copying from this RFA Tutors course is not permitted. Ref ' + trace() + '.';
  try {
    if (navigator.clipboard && navigator.clipboard.writeText) {
      navigator.clipboard.writeText(note)['catch'](function () { /* no permission */ });
      return;
    }
  } catch (e) { /* older browsers */ }
  try {
    var ta = make('textarea', 'offscreen');
    ta.value = note;
    document.body.appendChild(ta);
    ta.select();
    document.execCommand('copy');
    document.body.removeChild(ta);
  } catch (e2) { /* nothing further to try */ }
}

function captureCombo(e) {
  var k = String(e.key || '');
  var code = String(e.code || '');
  if (k === 'PrintScreen' || e.keyCode === 44) { return 'print-screen'; }
  if (e.metaKey && e.shiftKey) {
    if (/^Digit[3456]$/.test(code)) { return 'mac-capture'; }
    if (/^[3456]$/.test(k)) { return 'mac-capture'; }
    if (!code && e.keyCode >= 51 && e.keyCode <= 54) { return 'mac-capture'; }
    if (k === 's' || k === 'S') { return 'snip'; }
  }
  if (e.ctrlKey && e.shiftKey && (k === 's' || k === 'S')) { return 'snip'; }
  return '';
}

var deferredShield = '';
function onCapture(kind, whenBack) {
  if (now() - lastCap < 700) { return; }      /* keydown and keyup are one press */
  lastCap = now();
  state.guard.cap++;
  var msg = 'Screen capture is not permitted here. Every ' + UNIT + ' carries your name and the ' +
            'code ' + trace() + ', so a copy of this screen can be traced back to your account.';
  /* raised while the window is losing focus (the snipping overlay took it):
     shown when the learner comes back, or the focus would dismiss it at once */
  if (whenBack) { deferredShield = msg; } else { shield(msg, 2000); }
  scrubClipboard();
  noteGuard('capture:' + kind);
  alertCapture('capture:' + kind);
  armNotice();
  save();
}

function guardSummary() {
  var g = state.guard;
  var row = 'trace=' + trace() + ' capture=' + g.cap + ' blur=' + g.blur + ' fastturns=' + g.fast;
  if (geoText()) { row += ' where=' + geoText(); }
  if (deviceId()) { row += ' device=' + deviceId(); }
  if (FP_ON) { row += ' fp=' + fingerprint(); }
  return row;
}

function guardScore() {
  var g = state.guard;
  return g.cap * 4 + g.fast + Math.floor(g.blur / 4);
}

function noteGuard(what) {
  if (!CAP_LOG) { return; }
  var g = state.guard;
  if (g.sent >= GUARD_TIERS.length || guardScore() < GUARD_TIERS[g.sent]) { return; }
  g.sent++;
  if (live && SCORM.flag) { SCORM.flag('CAPTURE', guardSummary() + ' last=' + what); }
}

function finalGuardReport() {
  if (!CAP_LOG || !live || !SCORM.flag) { return; }
  if (state.guard.sent || !(state.guard.cap || state.guard.fast > 6)) { return; }
  state.guard.sent++;
  SCORM.flag('CAPTURE', guardSummary() + ' last=session-end');
}

function alertPayload(event, detail, addresses) {
  var g = state.guard;
  if (!addresses || !addresses.length) { addresses = addressList(state.places, 8); }
  return JSON.stringify({
    event: String(event || 'capture'),
    detail: String(detail || ''),
    addresses: addresses || [],
    course: String(cfg('id', '')),
    title: String(cfg('title', '')),
    learner: live ? String(SCORM.learnerName() || '') : '',
    learnerId: live ? String(SCORM.learnerId() || '') : '',
    trace: trace(),
    captures: g.cap,
    blur: g.blur,
    fastTurns: g.fast,
    page: state.current,
    pagesSeen: state.seenCount,
    device: deviceId(),
    deviceLabel: deviceId() ? deviceLabel() : '',
    devices: state.devs,
    sid: sessionId,
    profile: deviceProfile(),
    active: Math.round(activeMs / 1000),
    place: geo.place || '',
    ip: geo.ip || '',
    isp: geo.isp || '',
    lat: geo.lat, lon: geo.lon,
    at: new Date().toISOString(),
    agent: String(navigator.userAgent || '').slice(0, 180)
  });
}

/* ---- sessions -----------------------------------------------------------

   One learner, one unit, one opening = one session. The endpoint hears when
   it opens, every HEARTBEAT_S seconds of visible reading, and when it closes
   (or is hidden - a phone rarely fires pagehide). The heartbeat carries the
   seconds actually spent with the page visible, so the server knows how long
   the learner read and can tell one learner's day from two people's. */

function newSessionId() {
  var s = '';
  try { s = Math.floor(Math.random() * 2176782336).toString(36).toUpperCase(); } catch (e) { s = String(now()); }
  while (s.length < 6) { s = '0' + s; }
  return s.slice(0, 8);
}
var sessionId = newSessionId();
var activeMs = 0, activeFrom = 0, sessionOpened = false, sessionClosed = false, beatTimer = null;
var lastAlive = now();

function alive() { lastAlive = now(); }

function activeTick() {
  if (!activeFrom) { return; }
  var t = now();
  /* a laptop asleep with the tab visible: the timer simply did not run, so a
     single stretch longer than two heartbeats is counted as one heartbeat */
  var end = Math.min(t, lastAlive + IDLE_S * 1000);
  if (end - activeFrom > HEARTBEAT_S * 2000) { end = activeFrom + HEARTBEAT_S * 1000; }
  if (end > activeFrom) { activeMs += end - activeFrom; }
  activeFrom = t;
}

var lastSessionBody = null;            /* the last session post, kept for a fast close */
function sessionBody(event, extra) {
  var b = JSON.parse(alertPayload(event, extra || '', []));
  b.addresses = undefined;
  b.devices = undefined;
  b.units = state.total;
  return b;
}
function sessionPost(event, extra) {
  if (!SESSIONS_ON || !ALERT_URL) { return; }
  activeTick();
  var b = sessionBody(event, extra);
  lastSessionBody = b;
  postJson(JSON.stringify(b));
}

/* The close is sent while the page is being torn down, and a beacon queued
   even a few milliseconds late can be dropped with the frame (measured: an
   iframe whose src the host replaces lost 6 closes in 10 when the payload
   was built from scratch). So the close is the last heartbeat's body with
   the few fields that changed, stringified and queued at once - no LMS
   calls, no fingerprinting, nothing that can wait. */
function sessionCloseFast(reason) {
  if (!SESSIONS_ON || !ALERT_URL) { return; }
  activeTick();
  if (!lastSessionBody) { try { lastSessionBody = sessionBody('session-close', reason); } catch (e) { return; } }
  var b = lastSessionBody, g = state.guard;
  b.event = 'session-close'; b.detail = reason; b.active = Math.round(activeMs / 1000);
  b.page = state.current; b.pagesSeen = state.seenCount; b.captures = g.cap; b.blur = g.blur; b.fastTurns = g.fast;
  b.units = state.total; b.at = new Date().toISOString();
  if (geo.ip) { b.ip = geo.ip; b.place = geo.place || ''; b.isp = geo.isp || ''; b.lat = geo.lat; b.lon = geo.lon; }
  postJson(JSON.stringify(b));
}

function sessionOpen() {
  if (sessionOpened) { return; }
  sessionOpened = true;
  sessionPost('session-open', 'opened');
}

function beat() {
  if (sessionClosed || document.hidden) { return; }
  sessionPost('heartbeat', 'reading');
}

function sessionClose(reason) {
  if (sessionClosed) { return; }
  sessionClosed = true;
  clearInterval(beatTimer);
  if (activeFrom) { activeTick(); activeFrom = 0; }
  sessionCloseFast(reason || 'closed');
}

function bindSessions() {
  if (!SESSIONS_ON || !ALERT_URL) { return; }
  activeFrom = document.hidden ? 0 : now();
  var evs = ['keydown', 'pointerdown', 'mousemove', 'touchstart', 'wheel', 'scroll'], i;
  for (i = 0; i < evs.length; i++) { on(document, evs[i], alive, { passive: true, capture: true }); }
  learnModel();
  /* a body ready from the start, so a unit closed in its first seconds still
     sends a close without building anything during teardown */
  try { lastSessionBody = sessionBody('session-open', 'opened'); } catch (e0) { }
  /* give the location lookup and the model hint a moment to land first */
  setTimeout(sessionOpen, 2500);
  beatTimer = setInterval(beat, HEARTBEAT_S * 1000);
  /* a page brought back from the back-forward cache, or a phone browser
     that fired pagehide when it went to the background, comes back as a new
     session: the old one was closed and stays closed */
  on(window, 'pageshow', function () {
    if (!sessionClosed) { return; }
    sessionClosed = false; sessionOpened = false; sessionId = newSessionId();
    activeMs = 0; activeFrom = document.hidden ? 0 : now(); lastAlive = now(); lastSessionBody = null;
    try { lastSessionBody = sessionBody('session-open', 'reopened'); } catch (e1) { }
    clearInterval(beatTimer); beatTimer = setInterval(beat, HEARTBEAT_S * 1000);
    if (!document.hidden) { sessionOpen(); }
  });
  on(document, 'visibilitychange', function () {
    if (document.hidden) {
      if (activeFrom) { activeTick(); activeFrom = 0; }
      if (sessionOpened && !sessionClosed) { sessionPost('heartbeat', 'hidden'); }   /* an unloading page goes hidden after its close */
    } else {
      activeFrom = now();
      if (!sessionOpened) { sessionOpen(); }
    }
  });
  on(window, 'pagehide', function () { if (!sessionOpened) { sessionOpened = true; } sessionClose('pagehide'); });
  on(window, 'beforeunload', function () { if (!sessionOpened) { sessionOpened = true; } sessionClose('unload'); });
}

/* fetch with keepalive first, sendBeacon second, XHR last. Measured in
   Chromium on an iframe whose src the host replaces: the close reached the
   server 30 of 30 times with fetch keepalive and 21 of 30 with sendBeacon
   (both fine when the whole page navigates or the tab closes). keepalive is
   only used where the browser says it understands it. */
var KEEPALIVE = (function () { try { return !!(window.fetch && window.Request && ('keepalive' in Request.prototype)); } catch (e) { return false; } })();
function postJson(body) {
  if (KEEPALIVE) {
    try {
      fetch(ALERT_URL, { method: 'POST', keepalive: true, body: body, headers: { 'Content-Type': 'text/plain;charset=UTF-8' } })['catch'](function () { });
      return;
    } catch (e0) { /* fall through to the beacon */ }
  }
  try {
    if (navigator.sendBeacon) {
      var blob = new Blob([body], { type: 'text/plain;charset=UTF-8' });
      if (navigator.sendBeacon(ALERT_URL, blob)) { return; }
    }
  } catch (e) { /* fall through to XHR */ }
  try {
    var x = new XMLHttpRequest();
    x.open('POST', ALERT_URL, true);
    x.setRequestHeader('Content-Type', 'text/plain;charset=UTF-8');
    x.send(body);
  } catch (e2) { /* nothing further to try */ }
}

function sendAlert(event, detail, addresses) {
  if (alertsOut >= ALERT_MAX) { return; }
  alertsOut++;
  postJson(alertPayload(event, detail, addresses));
}

function alertAt() {
  if (!ALERT_PCT || !state.total) { return 0; }
  return Math.max(3, Math.ceil(state.total * ALERT_PCT / 100));
}

function alertCapture(kind) {
  var g = state.guard, at = alertAt();
  if (!ALERT_URL) { return; }
  if (ALERT_FIRST && g.cap >= 1 && !g.alert) {
    g.alert = g.cap;
    sendAlert('capture', 'first capture attempt in this unit (' + kind + '), ' +
              (KIND === 'video' ? 'at ' + state.current + ' of ' + state.total + ' min'
                                : 'page ' + Math.max(1, Number(state.current) || 1) + ' of ' + state.total));
    return;
  }
  if (!at) { return; }
  if (g.cap < at || g.cap < g.alert + at) { return; }
  g.alert = g.cap;
  sendAlert('capture', g.cap + ' capture attempts against a ' + state.total +
            '-page document (' + Math.round(g.cap * 100 / state.total) +
            '% of its pages), last ' + kind);
}

/* ------------------------------------------------------ painting it on

   The reader tiles one of these per page; the player has a single
   overlay over the picture. Both want the same tile, and both want the
   phase moved off the obvious origin so two learners' screenshots of
   the same frame never line up. */

function paintOne(t) {
  if (!WM_ON || !t.node) { return; }
  t.node.style.backgroundImage = watermarkTile();
  t.node.style.backgroundRepeat = 'repeat';
  t.node.style.backgroundPosition = wmPhase(t.n, 17) + 'px ' + wmPhase(t.n, 29) + 'px';
  if (WM_ALPHA > 0) { t.node.style.opacity = String(WM_ALPHA); }
  else if (WM_STRONG) { t.node.style.opacity = '0.30'; }
  if (WM_STRONG && t.stamp) {
    t.stamp.style.backgroundImage = stampTile(t.n);
    t.stamp.style.backgroundRepeat = 'no-repeat';
  }
}

/* The host paints as it builds - one call per page in the reader, one for
   the whole picture in the player - and the guard keeps the list so it can
   repaint every one of them when the location lookup lands a second or two
   later. Re-painting the same node twice replaces its entry rather than
   growing the list, so a reader that rebuilds its pages on a zoom does not
   leak. */
function paint(node, n, stamp) {
  if (!node) { return; }
  var t = null, i;
  for (i = 0; i < wmTargets.length; i++) {
    if (wmTargets[i].node === node) { t = wmTargets[i]; break; }
  }
  if (!t) { t = { node: node, stamp: stamp || null, n: n || 1 }; wmTargets.push(t); }
  else { t.stamp = stamp || t.stamp; t.n = n || t.n; }
  paintOne(t);
}

function watermarkRepaint() {
  wmTile = null;
  stampCache = {};
  for (var i = 0; i < wmTargets.length; i++) { paintOne(wmTargets[i]); }
}

/* ------------------------------------------------------- capture guard */

function bindGuards() {
  if (!CAP_GUARD) { return; }
  on(window, 'blur', function () { state.guard.blur++; });
  on(document, 'keydown', function (e) {
    var kind = captureCombo(e);
    if (!kind) { return; }
    if (e.preventDefault) { e.preventDefault(); }
    onCapture(kind);
  }, true);
  on(document, 'keyup', function (e) {
    if (e.key === 'PrintScreen' || e.keyCode === 44) { onCapture('print-screen'); }
  }, true);
  on(window, 'focus', unshield);
  bindChord();
}

/* ---- the swallowed chord ------------------------------------------------

   macOS takes Cmd+Shift+3/4/5 and Windows takes Win+Shift+S before the
   browser sees the third key. What the page does see is Meta and Shift going
   down together and coming back up with nothing pressed in between - a
   combination no ordinary shortcut produces. It is a suspicion, not a
   sighting, and it is labelled that way wherever it is reported. */
var chord = { meta: 0, shift: 0, other: false };
function bindChord() {
  if (!CHORD_ON) { return; }
  var ua = String(navigator.userAgent || '');
  if (!/Mac OS X|Windows/.test(ua) || /iPhone|iPad|Android/.test(ua)) { return; }
  var isMac = /Mac OS X/.test(ua);
  /* "other" means a third key went down WHILE the chord was held; typing
     before the chord does not count, so it is cleared when the first
     modifier goes down with nothing else held */
  on(document, 'keydown', function (e) {
    var k = String(e.key || '');
    if (k === 'Meta' || k === 'OS' || k === 'Shift') {
      if (!chord.meta && !chord.shift) { chord.other = false; }
      if (k === 'Shift') { chord.shift = chord.shift || now(); } else { chord.meta = chord.meta || now(); }
      return;
    }
    if (chord.meta || chord.shift) { chord.other = true; }
  }, true);
  function judge() {
    var both = chord.meta && chord.shift;
    var held = both ? now() - Math.max(chord.meta, chord.shift) : 0;
    return both && !chord.other && held >= 60 && held < 4000;
  }
  function reset() { chord.meta = 0; chord.shift = 0; chord.other = false; }
  on(document, 'keyup', function (e) {
    var k = String(e.key || '');
    if (k !== 'Meta' && k !== 'OS' && k !== 'Shift') { return; }
    var fire = judge();
    if (k === 'Meta' || k === 'OS') { chord.meta = 0; } else { chord.shift = 0; }
    if (!chord.meta && !chord.shift) { chord.other = false; }
    if (fire) { reset(); onCapture(isMac ? 'suspected-mac-capture' : 'suspected-snip'); }
  }, true);
  /* Win+Shift+S opens the snipping overlay, which takes the focus before the
     keys come up: the chord is judged as the window loses focus, then cleared */
  on(window, 'blur', function () { var fire = judge(); reset(); if (fire) { onCapture(isMac ? 'suspected-mac-capture' : 'suspected-snip', true); } });
  on(window, 'focus', function () { if (deferredShield) { var m = deferredShield; deferredShield = ''; setTimeout(function () { shield(m, 2000); }, 30); } });
}

/* --------------------------------------------------------- the outside */

window.RFA_GUARD = {
  init: function (opts) {
    opts = opts || {};
    SCORM = opts.scorm || null;
    live = !!opts.live && !!SCORM;              /* "live" means there is an API to flag through */
    save = opts.save || function () { };
    state.total = opts.units || 0;
    geoStart();                 /* sets the time-zone line synchronously */
    noteDevice();               /* so an alert raised here is not placeless */
    if (TEST_ALERT) {
      if (ALERT_URL) {
        sendAlert('test', 'test alert fired when the course opened');
        if (CAP_LOG && live && SCORM.flag) { SCORM.flag('TEST', 'alert POSTed to ' + ALERT_URL); }
        window.RFA_TEST_SENT = true;
      } else {
        window.RFA_TEST_SENT = false;
      }
      if (window.console && console.log) {
        console.log('[RFA] test alert: ' +
          (ALERT_URL ? 'POSTed to ' + ALERT_URL : 'NO ALERT URL IN THIS PACKAGE - rebuild with --alert-url'));
      }
    }
    bindGuards();
    bindSessions();
    watermarkRepaint();
    setTimeout(showNotice, 900);
    on(el('notice-close'), 'click', function () {
      el('capture-notice').hidden = true;
      ackNotice();
    });
  },

  /* the host owns cmi.suspend_data; the guard just hands over its share */
  pack: function () {
    var out = {};
    var g = state.guard;
    if (g.viol) { out.v = g.viol; }
    if (g.cap || g.blur || g.fast) {
      out.g = [g.cap, g.blur, g.fast, g.sent, g.alert, g.share, g.streak, g.city, g.dev, g.viol];
    }
    if (state.places.length) { out.ip = state.places; }
    if (state.days.length) { out.dy = state.days; }
    if (state.devs.length) { out.dv = state.devs; }
    if (state.visits.length) { out.vs = state.visits; }
    return out;
  },

  restore: function (s) {
    if (!s) { return; }
    if (typeof s.v === 'number') { state.guard.viol = s.v; }
    if (s.g && s.g.length) {
      state.guard.cap = s.g[0] || 0;   state.guard.blur = s.g[1] || 0;
      state.guard.fast = s.g[2] || 0;  state.guard.sent = s.g[3] || 0;
      state.guard.alert = s.g[4] || 0; state.guard.share = s.g[5] || 0;
      state.guard.streak = s.g[6] || 0; state.guard.city = s.g[7] || 0;
      state.guard.dev = s.g[8] || 0;   state.guard.viol = s.g[9] || state.guard.viol;
    }
    if (s.ip && s.ip.length) { state.places = s.ip; }
    if (s.dy && s.dy.length) { state.days = s.dy; }
    if (s.dv && s.dv.length) { state.devs = s.dv; }
    if (s.vs && s.vs.length) { state.visits = s.vs; }
  },

  /* the player tells the guard where the learner is, for the alert body */
  at: function (current, seen) { state.current = current; state.seenCount = seen; alive(); },
  alive: alive,
  units: function (n) { state.total = n; },

  paint: paint,
  /* the reader puts its own messages on the same panel the capture guard
     uses - one shield, one z-index, one thing to get wrong */
  shield: function (msg, ms) { shield(msg, ms); },
  unshield: unshield,
  lock: function (on) { state.locked = !!on; },
  trace: trace,
  device: deviceId,
  where: geoText,
  summary: guardSummary,
  repaint: watermarkRepaint,
  closing: function () { sessionClose('closed'); finalGuardReport(); },   /* the beacon first: the LMS call can wait, the page cannot */
  fingerprint: fingerprint,
  profile: deviceProfile,
  /* the player counts its own kind of misbehaviour into the same tally */
  note: function (what) { state.guard.fast++; noteGuard(what); }
};

})();
