/* RFA Tutors - remote settings.
   ------------------------------------------------------------------
   The package is built with its settings baked into config.js, and a
   built package cannot be edited inside the LMS. So this file lets the
   thresholds be changed afterwards without a re-upload: it fetches a
   small JSON document from settingsUrl (the mailer's own /exec?settings=1,
   which serves the Settings tab of the log spreadsheet), stores it, and
   applies it the NEXT time the unit opens. Applying on the next open
   rather than this one keeps the fetch off the critical path: a slow or
   absent network costs nothing and the baked settings stand.

   Only the keys listed here can be overridden - never the document, the
   key, the title or the endpoint itself. */
(function () {
  'use strict';
  var C = window.RFA_CONFIG || {};
  var KEYS = ['alertPercent', 'alertFirstCapture', 'shareThreshold', 'shareWindowHours',
              'patternDays', 'cityAlert', 'deviceStrict', 'turns', 'turnsWindowHours',
              'deviceAlert', 'deviceWarn', 'captureGuard', 'captureLog', 'captureNotice',
              'chordHeuristic', 'sessions', 'heartbeatSeconds', 'idleSeconds', 'fingerprint', 'geoWatermark',
              'strongWatermark', 'watermarkOpacity', 'blurOnBlur', 'dwellSeconds', 'pageCap'];
  var STORE = 'rfa.settings';
  var held = null;
  try { held = JSON.parse(window.localStorage.getItem(STORE) || 'null'); } catch (e) { held = null; }
  if (held && held.v && typeof held.v === 'object') {
    for (var i = 0; i < KEYS.length; i++) {
      if (held.v[KEYS[i]] !== undefined && held.v[KEYS[i]] !== null && held.v[KEYS[i]] !== '') {
        C[KEYS[i]] = held.v[KEYS[i]];
      }
    }
    C.settingsFrom = held.at || '';
  }
  if (!C.settingsUrl || !window.XMLHttpRequest) { return; }
  setTimeout(function () {
    try {
      var x = new XMLHttpRequest();
      x.open('GET', C.settingsUrl + (C.settingsUrl.indexOf('?') < 0 ? '?' : '&') + 't=' + new Date().getTime(), true);
      x.timeout = 10000;
      x.onreadystatechange = function () {
        if (x.readyState !== 4 || x.status !== 200) { return; }
        var d = null;
        try { d = JSON.parse(x.responseText); } catch (e) { d = null; }
        if (!d || typeof d !== 'object' || !d.settings) { return; }
        try { window.localStorage.setItem(STORE, JSON.stringify({ at: new Date().toISOString(), v: d.settings })); } catch (e2) { }
      };
      x.send(null);
    } catch (e3) { /* the baked settings stand */ }
  }, 5000);
})();
