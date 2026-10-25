/* RFA Tutors - premium link viewer add-on (v1.0, 25 Oct 2026). Loaded right after config.js.
   1. Takes the buyer's ID from the link (?id=P7K3Q9) and remembers it on this device.
   2. Provides the small LMS interface the reader and its guard expect, with the ID as the
      student id - so every opening is reported to the premium mailer under that ID and the
      ID is printed in the page watermark.
   3. Asks the mailer how many devices this ID has been opened on and tells the reader, so
      they can log out devices that are not theirs. Nothing is refused. */
(function () {
  'use strict';
  var C = window.RFA_CONFIG || (window.RFA_CONFIG = {});
  var KEY = 'rfa.premium.id.' + String(C.id || 'DOC');
  function qs(name) { var m = new RegExp('[?&#]' + name + '=([^&#]*)').exec(String(window.location.href)); return m ? decodeURIComponent(m[1]) : ''; }
  /* Opened inside Telegram (a Mini App link posted in the group): Telegram hands the page the member's
     identity - that becomes the ID (TG<user id>) and the name. Otherwise the ID comes from ?id= in the link. */
  var tg = null, tgUser = null, tgName = '', initData = '';
  try { tg = window.Telegram && window.Telegram.WebApp; tgUser = tg && tg.initDataUnsafe && tg.initDataUnsafe.user; initData = (tg && tg.initData) || ''; if (tg && tg.ready) { tg.ready(); } if (tg && tg.expand) { tg.expand(); } } catch (eT) { tgUser = null; }
  var id = '';
  if (tgUser && tgUser.id) {
    id = 'TG' + String(tgUser.id);
    tgName = String((tgUser.first_name || '') + ' ' + (tgUser.last_name || '')).replace(/\s+/g, ' ').trim() + (tgUser.username ? ' @' + tgUser.username : '');
  } else {
    id = String(qs('id') || '').trim().toUpperCase().replace(/[^A-Z0-9_-]/g, '').slice(0, 24);
    try { if (id) { window.localStorage.setItem(KEY, id); } else { id = String(window.localStorage.getItem(KEY) || ''); } } catch (e) { }
  }
  window.RFA_PREMIUM_ID = id;
  C.watermarkText = C.watermarkText || 'RFA Tutors premium';

  var data = {}, store = 'rfa.premium.cmi.' + String(C.id || 'DOC') + '.' + id;
  try { data = JSON.parse(window.localStorage.getItem(store) || '{}') || {}; } catch (e2) { data = {}; }
  data['cmi.core.student_id'] = id || 'NO-ID'; data['cmi.core.student_name'] = tgName ? tgName.split(' @')[0] + ', ' : 'Premium, RFA';
  if (tgName) { data['cmi.core.student_name'] = tgName.split(' @')[0]; }
  data['cmi.core.lesson_mode'] = 'normal'; data['cmi.core.credit'] = 'credit';
  if (!data['cmi.core.lesson_status']) { data['cmi.core.lesson_status'] = 'not attempted'; }
  function persist() { try { window.localStorage.setItem(store, JSON.stringify(data)); } catch (e) { } }
  window.API = {
    LMSInitialize: function () { return 'true'; }, LMSFinish: function () { persist(); return 'true'; },
    LMSGetValue: function (k) { return data[k] === undefined ? (k === 'cmi.interactions._count' ? '0' : '') : String(data[k]); },
    LMSSetValue: function (k, v) { data[k] = String(v); return 'true'; }, LMSCommit: function () { persist(); return 'true'; },
    LMSGetLastError: function () { return '0'; }, LMSGetErrorString: function () { return ''; }, LMSGetDiagnostic: function () { return ''; }
  };

  function banner(text, strong) {
    var box = document.getElementById('premium-note');
    if (!box) {
      box = document.createElement('div'); box.id = 'premium-note';
      box.style.cssText = 'position:fixed;left:0;right:0;bottom:0;z-index:2147483000;font:13px/1.35 Arial,sans-serif;padding:8px 40px 8px 12px;color:#222;border-top:1px solid #999;box-shadow:0 -2px 6px rgba(0,0,0,.25)';
      var x = document.createElement('button'); x.textContent = '\u00d7'; x.setAttribute('aria-label', 'Hide');
      x.style.cssText = 'position:absolute;right:8px;top:4px;font:18px Arial;border:0;background:transparent;cursor:pointer;color:#222';
      x.onclick = function () { box.style.display = 'none'; };
      box.appendChild(document.createElement('span')); box.appendChild(x); document.body.appendChild(box);
    }
    box.style.background = strong ? '#ffe3b3' : '#e8f0fe'; box.style.display = ''; box.firstChild.textContent = text;
  }
  function askCount() {
    var url = String(C.alertUrl || ''); if (!url || !id) { return; }
    var q = url + (url.indexOf('?') < 0 ? '?' : '&') + 'count=' + encodeURIComponent(id) + '&t=' + new Date().getTime(), done = false;
    function show(r) {
      if (done || !r || typeof r.devices !== 'number') { return; } done = true;
      var n = r.devices, limit = Number(C.deviceLimit || 2);
      var who = tgName ? 'Your copy (' + tgName.split(' @')[0] + ')' : 'Your copy ' + id;
      if (n > limit) { banner(who + ' has been opened on ' + n + ' devices in the last ' + r.days + ' days. If some are not yours, log out of Telegram on the devices you do not use (Settings → Devices) and contact RFA Tutors.', true); }
      else { banner('Your copy ' + id + ' · opened on ' + n + ' device' + (n === 1 ? '' : 's') + ' in the last ' + r.days + ' days.', false); }
    }
    function jsonp() { if (done) { return; } var cb = 'rfaCount' + new Date().getTime(); window[cb] = show; var s = document.createElement('script'); s.src = q + '&callback=' + cb; document.head.appendChild(s); }
    try { var x = new XMLHttpRequest(); x.open('GET', q, true); x.timeout = 12000;
      x.onreadystatechange = function () { if (x.readyState !== 4) { return; } var r = null; try { r = JSON.parse(x.responseText); } catch (e) { } if (r) { show(r); } else { jsonp(); } };
      x.onerror = jsonp; x.ontimeout = jsonp; x.send(null); } catch (e3) { jsonp(); }
  }
  /* tell the mailer who this Telegram member is (name, @username), with Telegram's signed data so it can be verified */
  function hello() {
    var url = String(C.alertUrl || ''); if (!url || !tgUser) { return; }
    var body = JSON.stringify({ event: 'tg-hello', learnerId: id, name: tgName, tgId: String(tgUser.id), username: String(tgUser.username || ''), initData: String(initData).slice(0, 4000), course: String(C.id || ''), at: new Date().toISOString() });
    try { if (navigator.sendBeacon && navigator.sendBeacon(url, new Blob([body], { type: 'text/plain;charset=UTF-8' }))) { return; } } catch (e) { }
    try { var x = new XMLHttpRequest(); x.open('POST', url, true); x.setRequestHeader('Content-Type', 'text/plain;charset=UTF-8'); x.send(body); } catch (e2) { }
  }
  document.addEventListener('DOMContentLoaded', function () {
    hello();
    if (!id) { banner('Please open this document from the RFA Tutors link in your Telegram group.', true); return; }
    banner('Your copy ' + id + ' · every opening is recorded for RFA Tutors.', false);
    setTimeout(askCount, 2500);
  });
})();
