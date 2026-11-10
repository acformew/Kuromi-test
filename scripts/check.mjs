// Сбор ключей, реальная проверка через Xray-core, замер задержки, геопривязка, генерация подписок.
import { spawn, execFile } from 'node:child_process';
import { promisify } from 'node:util';
import nodeNet from 'node:net';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';

const run = promisify(execFile);
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const SOURCES = [
  'https://raw.githubusercontent.com/barry-far/V2ray-Config/main/All_Configs_Sub.txt',
  'https://raw.githubusercontent.com/Epodonios/v2ray-configs/main/All_Configs_Sub.txt',
  'https://raw.githubusercontent.com/MatinGhanbari/v2ray-CONFIGs/main/subscriptions/v2ray/super-sub.txt',
  'https://raw.githubusercontent.com/mahdibland/V2RayAggregator/master/sub/sub_merge.txt',
  'https://raw.githubusercontent.com/ebrasha/free-v2ray-public-list/main/V2Ray-Config-By-EbraSha.txt',
];
const REGIONS = {
  EU: 'DE NL FR GB FI SE NO PL IT ES CH AT CZ RO BG LT LV EE IE DK BE PT HU UA'.split(' '),
  US: ['US', 'CA'],
  ASIA: 'JP SG HK KR TW IN AE TH VN ID MY TR KZ'.split(' '),
  PL: ['PL'],
};
const MAX_TEST = 1500, PAR = 40, MAX_SUB = 300;
// Жёсткая проверка: узел живой только если через него реально пришёл HTTP 204 (дважды подряд).
const TEST_URL = 'https://www.gstatic.com/generate_204', TIMEOUT = 5; // секунд на один запрос
const UUID = /^[0-9a-f]{8}(-[0-9a-f]{4}){3}-[0-9a-f]{12}$/i;
const VMESS_SEC = ['auto', 'aes-128-gcm', 'chacha20-poly1305', 'none', 'zero'];
// Только AEAD-шифры Shadowsocks: старые потоковые (rc4-md5, aes-*-cfb и т.д.) современный Xray не поддерживает.
const SS_OK = new Set(['aes-128-gcm', 'aes-256-gcm', 'chacha20-poly1305', 'chacha20-ietf-poly1305', 'xchacha20-poly1305',
  'xchacha20-ietf-poly1305', '2022-blake3-aes-128-gcm', '2022-blake3-aes-256-gcm', '2022-blake3-chacha20-poly1305']);
// Адреса localhost/LAN/служебные: через них проверка «успешна» без выхода в интернет, такие узлы отбрасываются.
const badHost = (h) => {
  h = String(h || '').toLowerCase();
  if (!h || h === 'localhost' || h.endsWith('.local') || h.endsWith('.internal')) return true;
  const v4 = h.match(/^(\d+)\.(\d+)\.(\d+)\.(\d+)$/);
  if (v4) {
    const [a, b, c, d] = v4.slice(1).map(Number);
    return [a, b, c, d].some((x) => x > 255) || a === 0 || a === 10 || a === 127 || a >= 224 || (a === 169 && b === 254) ||
      (a === 172 && b >= 16 && b <= 31) || (a === 192 && b === 168) || (a === 100 && b >= 64 && b <= 127);
  }
  if (h.includes(':')) return h === '::' || h === '::1' || /^(fc|fd|fe80)/.test(h);
  return !/^[a-z0-9.-]+$/.test(h);
};
const tmp = await fs.mkdtemp(path.join(os.tmpdir(), 'x-'));

const b64d = (s) => {
  try {
    s = s.trim().replace(/-/g, '+').replace(/_/g, '/');
    while (s.length % 4) s += '=';
    return Buffer.from(s, 'base64').toString('utf8');
  } catch { return ''; }
};
const flag = (t) => {
  const m = (t || '').match(/[\u{1F1E6}-\u{1F1FF}]{2}/u);
  return m ? [...m[0]].map((c) => String.fromCharCode(c.codePointAt(0) - 0x1f1e6 + 65)).join('') : '';
};

const FPS = ['chrome', 'firefox', 'safari', 'ios', 'android', 'edge', '360', 'qq', 'random', 'randomized'];
const NETS = { tcp: 'tcp', raw: 'tcp', ws: 'ws', grpc: 'grpc', gun: 'grpc', httpupgrade: 'httpupgrade', xhttp: 'xhttp', splithttp: 'xhttp', h2: 'h2', http: 'h2', kcp: 'kcp', quic: 'quic' };
const HAPP_NETS = ['tcp', 'ws', 'grpc', 'httpupgrade', 'h2']; // транспорты, которые умеет ядро Sing-Box
const okHost = (h) => /^(?=.{1,253}$)([a-z0-9-]+\.)+[a-z][a-z0-9-]+$/i.test(h);
// Нормализует VLESS-ссылку. happ=true включает строгий режим Happ/Sing-Box.
// Возвращает null, если ключ в этом режиме использовать нельзя.
function sanitizeVlessUri(raw, happ = false) {
  let u; try { u = new URL(String(raw).trim()); } catch { return null; }
  if (u.protocol !== 'vless:') return null;
  let id; try { id = decodeURIComponent(u.username).trim().toLowerCase(); } catch { return null; }
  const host = u.hostname, port = +u.port;
  if (!/^[0-9a-f]{8}(-[0-9a-f]{4}){3}-[0-9a-f]{12}$/.test(id) || !host || !(port > 0 && port < 65536)) return null;
  const g = (k) => (u.searchParams.get(k) || '').trim();
  const net = NETS[g('type').toLowerCase()] || 'tcp';
  if (happ && !HAPP_NETS.includes(net)) return null;
  let sec = g('security').toLowerCase();
  if (sec === 'xtls') sec = 'tls';
  if (!['tls', 'reality', 'none'].includes(sec)) sec = g('pbk') ? 'reality' : 'none';
  const q = [['encryption', 'none']];
  const add = (k, v) => { if (v !== '' && v != null) q.push([k, v]); };
  const hp = g('host');
  if (sec !== 'none') {
    const pbk = g('pbk');
    if (sec === 'reality' && !/^[A-Za-z0-9_-]{43}$/.test(pbk)) return null;
    let sni = g('sni') || g('peer');
    if (!okHost(sni)) sni = '';
    if (!sni && sec === 'tls') sni = okHost(hp) ? hp : okHost(host) ? host : '';
    if (!sni && sec === 'reality' && happ) return null; // Happ требует SNI для REALITY
    let fp = g('fp').toLowerCase();
    if (happ || !FPS.includes(fp)) fp = 'chrome';
    let flow = g('flow');
    if (!(net === 'tcp' && /^xtls-rprx-vision(-udp443)?$/.test(flow))) flow = '';
    add('flow', flow); add('security', sec); add('sni', sni); add('fp', fp);
    if (sec === 'tls') add('alpn', g('alpn').split(',').map((s) => s.trim()).filter((s) => ['h2', 'http/1.1', 'h3'].includes(s)).join(','));
    if (sec === 'reality') {
      add('pbk', pbk);
      let sid = g('sid'); if (!/^[0-9a-f]{0,16}$/i.test(sid)) sid = '';
      if (happ) q.push(['sid', sid]); else add('sid', sid);
      add('spx', g('spx'));
    }
  } else add('security', 'none');
  add('type', net);
  if (net === 'tcp' && g('headerType') === 'http') { add('headerType', 'http'); add('host', hp); add('path', g('path') || '/'); }
  if (['ws', 'httpupgrade', 'xhttp', 'h2'].includes(net)) { add('host', hp); const p = g('path') || '/'; add('path', p.startsWith('/') ? p : '/' + p); }
  if (net === 'grpc') { add('serviceName', g('serviceName')); const m = g('mode'); if (['gun', 'multi'].includes(m)) add('mode', m); }
  let name; try { name = decodeURIComponent(u.hash.slice(1)); } catch { name = u.hash.slice(1); }
  name = name.replace(/[\u0000-\u001f]/g, ' ');
  if (happ) name = name.replace(/[^\p{L}\p{N}\p{Regional_Indicator}\p{Extended_Pictographic} ._|:@()\[\]-]/gu, '');
  name = (name.replace(/\s+/g, ' ').trim() || `${host}:${port}`).slice(0, 80);
  return `vless://${id}@${host}:${port}?${q.map(([k, v]) => `${k}=${encodeURIComponent(v)}`).join('&')}#${encodeURIComponent(name)}`;
}
const sanitizeVlessForHapp = (raw) => sanitizeVlessUri(raw, true);

function stream(net, sec, o) {
  if (!['tcp', 'ws', 'grpc', 'httpupgrade'].includes(net)) throw new Error('transport');
  if (!['none', 'tls', 'reality'].includes(sec)) throw new Error('security');
  if (o.insecure === '1' || o.insecure === 'true') throw new Error('allowInsecure'); // небезопасный TLS не принимаем
  if (net === 'tcp' && o.type && o.type !== 'none') throw new Error('http header');
  const s = { network: net, security: sec };
  if (sec === 'tls') s.tlsSettings = { serverName: o.sni || o.host || undefined, fingerprint: o.fp || 'chrome',
    alpn: o.alpn ? o.alpn.split(',') : undefined, allowInsecure: false };
  if (sec === 'reality') s.realitySettings = { serverName: o.sni, fingerprint: o.fp || 'chrome',
    publicKey: o.pbk, shortId: o.sid || '', spiderX: o.spx || '' };
  if (net === 'ws') s.wsSettings = { path: o.path || '/', headers: o.host ? { Host: o.host } : {} };
  if (net === 'grpc') s.grpcSettings = { serviceName: o.service || '' };
  if (net === 'httpupgrade') s.httpupgradeSettings = { path: o.path || '/', host: o.host || '' };
  return s;
}

// Разбор ссылки: валидирует структуру и сразу строит outbound для Xray. Бросает ошибку на битых ключах.
function parse(link) {
  link = link.trim();
  const p = (link.match(/^(vless|vmess|trojan|ss):\/\//) || [])[1];
  if (!p) return null;
  if (p === 'vless') { const s = sanitizeVlessUri(link); if (!s) throw new Error('vless'); link = s; }
  let host, port, name = '', out;
  const hash = link.indexOf('#');
  if (hash > -1) { try { name = decodeURIComponent(link.slice(hash + 1)); } catch { name = link.slice(hash + 1); } }
  if (p === 'vmess') {
    const j = JSON.parse(b64d(link.slice(8)));
    if (!j.add || !j.port || !j.id || !UUID.test(String(j.id).trim())) throw new Error('vmess');
    if (+j.aid) throw new Error('alterId'); // legacy VMess (MD5) в актуальном Xray не работает
    const sc = String(j.scy || 'auto').toLowerCase();
    if (!VMESS_SEC.includes(sc)) throw new Error('vmess security');
    host = String(j.add).trim(); port = +j.port; name = j.ps || name;
    out = { protocol: 'vmess', settings: { vnext: [{ address: host, port, users: [{ id: String(j.id).trim(), alterId: 0, security: sc }] }] },
      streamSettings: stream(j.net || 'tcp', j.tls === 'tls' ? 'tls' : 'none',
        { sni: j.sni, host: j.host, path: j.path, service: j.path, fp: j.fp, alpn: j.alpn, type: j.type }) };
  } else if (p === 'ss') {
    if (/[?&]plugin=/.test(link)) throw new Error('plugin');
    let b = link.slice(5, hash > -1 ? hash : undefined).split('?')[0];
    if (!b.includes('@')) b = b64d(b);
    const at = b.lastIndexOf('@');
    let ui = decodeURIComponent(b.slice(0, at));
    if (!ui.includes(':')) ui = b64d(ui);
    const [method, ...pw] = ui.split(':');
    const hp = b.slice(at + 1), i = hp.lastIndexOf(':');
    host = hp.slice(0, i).replace(/[\[\]]/g, ''); port = +hp.slice(i + 1);
    if (!method || !pw.length || !host || !port) throw new Error('ss');
    if (!SS_OK.has(method.toLowerCase())) throw new Error('ss method');
    out = { protocol: 'shadowsocks', settings: { servers: [{ address: host, port, method: method.toLowerCase(), password: pw.join(':') }] } };
  } else {
    const u = new URL(link), q = Object.fromEntries(u.searchParams);
    host = u.hostname.replace(/[\[\]]/g, ''); port = +u.port;
    if (!host || !port || !u.username) throw new Error(p);
    const o = { ...q, type: q.headerType, service: q.serviceName, insecure: q.allowInsecure || q.insecure }; // type = тип заголовка, а не транспорт
    const sec = (q.security || (p === 'trojan' ? 'tls' : 'none')).toLowerCase();
    if (p === 'trojan' && sec === 'none') throw new Error('trojan without tls');
    const st = stream((q.type || 'tcp').toLowerCase(), sec, o);
    out = p === 'vless'
      ? { protocol: 'vless', settings: { vnext: [{ address: host, port, users: [{ id: decodeURIComponent(u.username), encryption: 'none', flow: q.flow || undefined }] }] }, streamSettings: st }
      : { protocol: 'trojan', settings: { servers: [{ address: host, port, password: decodeURIComponent(u.username) }] }, streamSettings: st };
  }
  if (badHost(host) || !(port > 0 && port < 65536)) throw new Error('host');
  return { p, h: host, o: port, n: name.slice(0, 80), c: flag(name), l: link, out };
}

async function collect(prev) {
  const res = await Promise.allSettled(SOURCES.map(async (u) => {
    const r = await fetch(u, { signal: AbortSignal.timeout(20000) });
    if (!r.ok) throw new Error(r.status);
    const t = await r.text();
    return t.includes('://') ? t : b64d(t);
  }));
  const seen = new Set(), all = [];
  let bad = 0;
  for (const r of res) {
    if (r.status !== 'fulfilled') continue;
    for (const line of r.value.split(/\r?\n/)) {
      let n; try { n = parse(line); } catch { bad++; continue; }
      const k = n && `${n.h}:${n.o}`; // дубликаты отсекаются по IP:PORT
      if (n && !seen.has(k)) { seen.add(k); all.push(n); }
    }
  }
  console.log(`sources ok: ${res.filter((r) => r.status === 'fulfilled').length}/${SOURCES.length}, valid: ${all.length}, invalid: ${bad}`);
  const known = []; // узлы, уже проходившие проверку раньше, тестируются первыми
  for (const x of prev.values()) {
    if (!x.u || !x.u[1]) continue;
    try { const n = parse(x.l); const k = n && `${n.h}:${n.o}`; if (n && !seen.has(k)) { seen.add(k); known.push(n); } } catch { /* пропуск */ }
  }
  return [...known, ...all.sort(() => Math.random() - 0.5)].slice(0, MAX_TEST);
}

// Один запрос через локальный SOCKS5 Xray. Возвращает задержку в мс только при HTTP 204, иначе null.
async function viaProxy(port) {
  try {
    const { stdout } = await run('curl', ['-s', '-o', '/dev/null', '--socks5-hostname', `127.0.0.1:${port}`,
      '--connect-timeout', String(TIMEOUT), '--max-time', String(TIMEOUT), '-w', '%{http_code} %{time_total}', TEST_URL],
      { timeout: (TIMEOUT + 2) * 1000 });
    const [code, t] = stdout.trim().split(' ');
    const sec = parseFloat(String(t).replace(',', '.'));
    return code === '204' && sec > 0 ? Math.max(1, Math.round(sec * 1000)) : null;
  } catch { return null; } // ошибка сети, таймаут, RST: узел не рабочий
}
const portOpen = (port) => new Promise((res) => {
  const s = nodeNet.connect(port, '127.0.0.1');
  s.once('connect', () => { s.destroy(); res(true); });
  s.once('error', () => res(false));
});

// Реальная проверка: поднимаем Xray с этим ключом и дважды делаем HTTPS-запрос через него.
// Любой сбой (Xray не стартовал, ошибка, таймаут, код не 204) = узел сразу выбрасывается.
async function test(n, port) {
  const cfg = path.join(tmp, `${port}.json`);
  await fs.writeFile(cfg, JSON.stringify({ log: { loglevel: 'none' },
    inbounds: [{ listen: '127.0.0.1', port, protocol: 'socks', settings: { udp: false } }], outbounds: [n.out] }));
  const x = spawn('./bin/xray', ['run', '-c', cfg], { stdio: 'ignore' });
  let exited = false;
  const exitP = new Promise((r) => { x.once('exit', () => { exited = true; r(); }); x.once('error', () => { exited = true; r(); }); });
  try {
    let ready = false;
    for (let i = 0; i < 60 && !exited; i++) { if (await portOpen(port)) { ready = true; break; } await sleep(50); }
    if (!ready || exited) return null; // конфиг не принят ядром
    let best = null;
    for (let i = 0; i < 2; i++) { // 1-й запрос прогревает соединение, 2-й подтверждает стабильность
      const ms = await viaProxy(port);
      if (ms === null) return null;
      best = best === null ? ms : Math.min(best, ms);
    }
    return best;
  } finally {
    x.kill('SIGKILL');
    if (!exited) await Promise.race([exitP, sleep(500)]);
    await fs.rm(cfg, { force: true });
  }
}

async function geo(nodes) {
  const need = nodes;
  for (let i = 0; i < need.length; i += 100) {
    const part = need.slice(i, i + 100);
    try {
      const r = await fetch('http://ip-api.com/batch?fields=countryCode,city', { method: 'POST', body: JSON.stringify(part.map((x) => x.h)), signal: AbortSignal.timeout(15000) });
      (await r.json()).forEach((g, k) => { part[k].c = g.countryCode || part[k].c; part[k].city = g.city || ''; });
    } catch { /* без страны */ }
    await sleep(1500);
  }
}

const prev = new Map();
try { for (const x of JSON.parse(await fs.readFile('data/nodes.json', 'utf8')).nodes) prev.set(`${x.h}:${x.o}`, x); } catch { /* первого запуска ещё не было */ }
const hist = new Map(); // счётчики аптайма [проверок, успешных]; хранятся отдельно, в nodes.json мёртвых нет
try { for (const [k, v] of Object.entries(JSON.parse(await fs.readFile('data/history.json', 'utf8')))) hist.set(k, v); } catch { /* нет истории */ }
const list = await collect(prev);
let idx = 0;
await Promise.all(Array.from({ length: PAR }, async (_, w) => {
  while (idx < list.length) { const n = list[idx++]; n.ms = await test(n, 20000 + w); }
}));

for (const n of list) { // накопление аптайма: [проверок, успешных]
  const k = `${n.h}:${n.o}`, o = hist.get(k) || (prev.get(k) || {}).u || [0, 0];
  n.u = [o[0] + 1, o[1] + (Number.isFinite(n.ms) && n.ms > 0 ? 1 : 0)];
}
// Только узлы с реальной задержкой. Мёртвые не сохраняются нигде (KEEP_DEAD = 0).
const alive = list.filter((n) => Number.isFinite(n.ms) && n.ms > 0).sort((a, b) => a.ms - b.ms);
console.log(`tested: ${list.length}, alive: ${alive.length}`);
if (!alive.length) { console.log('no alive nodes, keeping previous data'); process.exit(0); }
await geo(alive);

const pub = ({ out, ...n }) => ({ ...n, hl: n.p === 'vless' ? sanitizeVlessForHapp(n.l) : undefined }); // hl: ссылка для Happ
await fs.mkdir('data', { recursive: true });
await fs.writeFile('data/nodes.json', JSON.stringify({ updated: new Date().toISOString(), tested: list.length,
  nodes: alive.map(pub) }));
await fs.writeFile('data/history.json', JSON.stringify(Object.fromEntries(list.map((n) => [`${n.h}:${n.o}`, n.u]))));

await fs.rm('sub', { recursive: true, force: true });
await fs.mkdir('sub', { recursive: true });
const toHapp = (x) => x.p === 'vless' ? sanitizeVlessForHapp(x.l) : x.l;
const good = alive.filter((x) => x.u[0] < 3 || x.u[1] / x.u[0] >= 0.6); // высокий аптайм или ещё мало данных
await fs.mkdir('sub/happ', { recursive: true });
const write = async (name, arr) => {
  if (!arr.length) return; // пустой файл клиенты считают невалидной подпиской
  const std = arr.slice(0, MAX_SUB).map((x) => x.l).join('\n');
  const hp = arr.map(toHapp).filter(Boolean).slice(0, MAX_SUB).join('\n');
  await fs.writeFile(`sub/${name}.txt`, Buffer.from(std).toString('base64'));
  if (hp) await fs.writeFile(`sub/happ/${name}.txt`, Buffer.from(hp).toString('base64'));
};
await write('all', good);
await write('reality', good.filter((x) => /[?&]security=reality/.test(x.l)));
for (const p of ['vless', 'vmess', 'trojan', 'ss']) await write(p, good.filter((x) => x.p === p));
for (const [r, cs] of Object.entries(REGIONS)) await write(r, good.filter((x) => cs.includes(x.c)));
for (const c of new Set(good.map((x) => x.c).filter(Boolean))) await write(c, good.filter((x) => x.c === c));
await fs.rm(tmp, { recursive: true, force: true });
