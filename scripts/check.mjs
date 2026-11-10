// Сбор ключей, реальная проверка через Xray-core, замер задержки, геопривязка, генерация подписок.
import { spawn, execFile } from 'node:child_process';
import { promisify } from 'node:util';
import nodeNet from 'node:net';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';

const run = promisify(execFile);
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
// Источники, адаптированные под Рунет (REALITY / белые списки). Недоступный источник просто пропускается.
const SOURCES = [
  'https://raw.githubusercontent.com/igareck/vpn-configs-for-russia/main/Vless-Reality-White-Lists-Rus-Mobile.txt',
  'https://raw.githubusercontent.com/igareck/vpn-configs-for-russia/main/BLACK_VLESS_RUS.txt',
  'https://raw.githubusercontent.com/igareck/vpn-configs-for-russia/main/WHITE-SNI-RU-all.txt',
  'https://raw.githubusercontent.com/AvenCores/goida-vpn-configs/main/githubmirror/1.txt',
  'https://raw.githubusercontent.com/kasesm/Free-Config/main/vless_raw.txt',
];
const REGIONS = {
  EU: 'DE NL FR GB FI SE NO PL IT ES CH AT CZ RO BG LT LV EE IE DK BE PT HU UA'.split(' '),
  US: ['US', 'CA'],
  ASIA: 'JP SG HK KR TW IN AE TH VN ID MY TR KZ'.split(' '),
  PL: ['PL'],
};
const MAX_TEST = 1500, PAR = 40, MAX_SUB = 300;
// Тест реального интернета: HTTPS-запрос к Cloudflare trace через узел (таймаут 4 с на запрос).
const TRACE_URL = 'https://www.cloudflare.com/cdn-cgi/trace', TIMEOUT = 4;
const AI_URLS = { claude: 'https://api.anthropic.com/v1/models', openai: 'https://api.openai.com/v1/models' };
const UA = 'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0 Safari/537.36';
const TLS_PORTS = [443, 8443]; // порты для TLS + ws/grpc
const BAD_PORTS = [21, 22, 23, 25, 53, 80, 110, 143, 1080, 2083, 3128, 3389, 8000, 8080, 8081, 8888, 9090]; // «мусорные» порты; также отсекаются порты > 40000
// Белый список SNI для REALITY: ТСПУ режет по домену в ClientHello, пропускаем только заведомо не заблокированные в РФ сервисы.
// Совпадение: домен целиком или его поддомен.
const SNI_WHITELIST = ['dl.google.com', 'www.google.com', 'play.google.com', 'fonts.googleapis.com', 'android.com',
  'www.apple.com', 'icloud.com', 'itunes.apple.com', 'captive.apple.com',
  'www.microsoft.com', 'azure.microsoft.com', 'live.com', 'bing.com',
  'yahoo.com', 'www.yahoo.com', 'amazon.com', 'aws.amazon.com', 'cloudflare.com', 'samsung.com', 'nvidia.com', 'oracle.com', 'cisco.com', 'speedtest.net'];
// Заблокированные в РФ домены: ключ с таким SNI выбрасывается сразу (в том числе для TLS-ключей).
const SNI_BLOCKED = ['facebook.com', 'fb.com', 'meta.com', 'instagram.com', 'whatsapp.com', 'twitter.com', 'x.com', 't.co', 'discord.com',
  'discord.gg', 'discordapp.com', 'bbc.com', 'bbc.co.uk', 'rutracker.org', 'linkedin.com', 'soundcloud.com', 'torproject.org'];
const inDom = (h, list) => list.some((d) => h === d || h.endsWith('.' + d));
const WHITELIST_TLS = false; // true: белый список SNI применяется и к TLS+ws/grpc (у них SNI = собственный домен узла, поэтому обычно выключено)
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

// Разбор ссылки под ТСПУ. В работу берутся ТОЛЬКО:
//  1) vless:// + security=reality, транспорт tcp (flow xtls-rprx-vision) или grpc, SNI из SNI_WHITELIST, валидный pbk;
//  2) vless:// и trojan:// + security=tls, транспорт ws/grpc, порт 443/8443, валидный домен в SNI (не из SNI_BLOCKED).
// ss://, vmess://, plain-tcp, trojan без TLS и всё прочее выбрасывается. Бросает ошибку на негодных ключах.
function parse(link) {
  link = link.trim();
  const p = (link.match(/^(vless|trojan):\/\//) || [])[1];
  if (!p) return null;
  let rawSni = ''; // SNI из исходной ссылки (санитайзер подставляет замену, а пустой/кривой SNI нужно отсечь)
  try { const o0 = new URL(link).searchParams; rawSni = (o0.get('sni') || o0.get('peer') || '').trim().toLowerCase(); } catch { throw new Error('url'); }
  if (rawSni && !okHost(rawSni)) throw new Error('bad sni'); // IP-адрес или мусор
  if (p === 'vless') { const s = sanitizeVlessUri(link); if (!s) throw new Error('vless'); link = s; }
  const u = new URL(link), q = Object.fromEntries(u.searchParams);
  const host = u.hostname.replace(/[\[\]]/g, ''), port = +u.port;
  if (!host || !u.username || !(port > 0 && port < 65536) || badHost(host)) throw new Error('addr');
  if (BAD_PORTS.includes(port) || port > 40000) throw new Error('port');
  const net = (q.type || 'tcp').toLowerCase();
  const sec = (q.security || (p === 'trojan' ? 'tls' : 'none')).toLowerCase();
  let sni = rawSni;
  if (sec === 'reality') {
    if (p !== 'vless' || !['tcp', 'grpc'].includes(net)) throw new Error('reality transport');
    if (!/^[A-Za-z0-9_-]{43}$/.test(q.pbk || '')) throw new Error('reality pbk');
    if (!sni) throw new Error('reality sni');
    if (net === 'tcp' && !/^xtls-rprx-vision/.test(q.flow || '')) throw new Error('reality flow'); // Vision обязателен для tcp
    if (inDom(sni, SNI_BLOCKED) || !inDom(sni, SNI_WHITELIST)) throw new Error('sni not whitelisted');
  } else if (sec === 'tls') {
    if (!['ws', 'grpc'].includes(net)) throw new Error('tls transport');
    if (!TLS_PORTS.includes(port)) throw new Error('tls port');
    sni = sni || (q.sni || '').trim().toLowerCase() || (okHost(host) ? host : '');
    if (!okHost(sni) || inDom(sni, SNI_BLOCKED)) throw new Error('sni');
    if (WHITELIST_TLS && !inDom(sni, SNI_WHITELIST)) throw new Error('sni not whitelisted');
  } else throw new Error('no tls'); // без TLS/REALITY ключи глушатся DPI
  const o = { ...q, sni, type: q.headerType, service: q.serviceName, insecure: q.allowInsecure || q.insecure }; // type = тип заголовка, не транспорт
  const st = stream(net, sec, o);
  const out = p === 'vless'
    ? { protocol: 'vless', settings: { vnext: [{ address: host, port, users: [{ id: decodeURIComponent(u.username), encryption: 'none', flow: q.flow || undefined }] }] }, streamSettings: st }
    : { protocol: 'trojan', settings: { servers: [{ address: host, port, password: decodeURIComponent(u.username) }] }, streamSettings: st };
  let name = '';
  const hash = link.indexOf('#');
  if (hash > -1) { try { name = decodeURIComponent(link.slice(hash + 1)); } catch { name = link.slice(hash + 1); } }
  return { p, h: host, o: port, n: name.slice(0, 80), c: flag(name), l: link, sni, wl: inDom(sni, SNI_WHITELIST), out };
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

// Запрос через локальный SOCKS5 Xray. Возвращает { code, body, ms } или null при любой сетевой ошибке/таймауте.
async function curlVia(port, url) {
  try {
    const { stdout } = await run('curl', ['-s', '-A', UA, '--socks5-hostname', `127.0.0.1:${port}`,
      '--connect-timeout', String(TIMEOUT), '--max-time', String(TIMEOUT), '-w', '\n__%{http_code} %{time_total}', url],
      { timeout: (TIMEOUT + 2) * 1000, maxBuffer: 1 << 20 });
    const i = stdout.lastIndexOf('\n__');
    if (i < 0) return null;
    const [code, t] = stdout.slice(i + 3).trim().split(' ');
    const sec = parseFloat(String(t).replace(',', '.'));
    return sec > 0 ? { code, body: stdout.slice(0, i), ms: Math.max(1, Math.round(sec * 1000)) } : null;
  } catch { return null; }
}
const traceOf = (body) => Object.fromEntries(String(body).split('\n').map((l) => l.split('=')).filter((a) => a.length >= 2)
  .map(([k, ...v]) => [k.trim(), v.join('=').trim()]));
const IP_RE = /^(\d{1,3}(\.\d{1,3}){3}|[0-9a-f]*:[0-9a-f:]+)$/i;
const DIRECT_IP = await (async () => { // IP самого раннера: если через узел вернулся он, трафик шёл мимо прокси
  try { const r = await fetch(TRACE_URL, { signal: AbortSignal.timeout(10000) }); return traceOf(await r.text()).ip || null; } catch { return null; }
})();
// Проверка реального интернета: HTTP 200, в теле ip= и loc=, ip выходной и не совпадает с IP раннера.
async function trace(port) {
  const r = await curlVia(port, TRACE_URL);
  if (!r || r.code !== '200' || !r.body.includes('ip=') || !r.body.includes('loc=')) return null;
  const t = traceOf(r.body);
  if (!IP_RE.test(t.ip || '') || !/^[A-Z]{2}$/.test(t.loc || '') || badHost(t.ip)) return null;
  if (t.loc === 'RU') return null; // выход в РФ = трафик остаётся внутри цензуры
  if (DIRECT_IP && t.ip === DIRECT_IP) return null;
  return { ip: t.ip, loc: t.loc, ms: r.ms };
}
// Доступность защищённого сервиса: без ключа API отдаёт 401 с JSON-ошибкой. 403/1020/503/таймаут = заблокирован Cloudflare/WAF.
async function reach(port, url) {
  const r = await curlVia(port, url);
  if (!r || !['200', '401'].includes(r.code)) return false;
  if (/cloudflare|cf-ray|Attention Required|error code: 1\d{3}/i.test(r.body)) return false;
  return r.code === '200' || /"error"/.test(r.body);
}
const portOpen = (port) => new Promise((res) => {
  const s = nodeNet.connect(port, '127.0.0.1');
  s.once('connect', () => { s.destroy(); res(true); });
  s.once('error', () => res(false));
});

// Реальная проверка: поднимаем Xray с этим ключом и делаем запросы через него.
// Любой сбой trace (ошибка, таймаут, не 200, нет ip=/loc=, IP раннера) = узел сразу выбрасывается.
// Результат: { ms, ip, loc, claude, openai } или null.
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
    const a = await trace(port); // 1-й запрос прогревает соединение
    if (!a) return null;
    const b = await trace(port); // 2-й подтверждает стабильность и даёт замер
    if (!b) return null;
    const [claude, openai] = await Promise.all([reach(port, AI_URLS.claude), reach(port, AI_URLS.openai)]);
    return { ms: Math.min(a.ms, b.ms), ip: b.ip, loc: b.loc, claude, openai };
  } finally {
    x.kill('SIGKILL');
    if (!exited) await Promise.race([exitP, sleep(500)]);
    await fs.rm(cfg, { force: true });
  }
}

const prev = new Map();
try { for (const x of JSON.parse(await fs.readFile('data/nodes.json', 'utf8')).nodes) prev.set(`${x.h}:${x.o}`, x); } catch { /* первого запуска ещё не было */ }
const hist = new Map(); // счётчики аптайма [проверок, успешных]; хранятся отдельно, в nodes.json мёртвых нет
try { for (const [k, v] of Object.entries(JSON.parse(await fs.readFile('data/history.json', 'utf8')))) hist.set(k, v); } catch { /* нет истории */ }
const list = await collect(prev);
let idx = 0;
await Promise.all(Array.from({ length: PAR }, async (_, w) => {
  while (idx < list.length) { const n = list[idx++]; const r = await test(n, 20000 + w); Object.assign(n, r || { ms: null }); }
}));

for (const n of list) { // накопление аптайма: [проверок, успешных]
  const k = `${n.h}:${n.o}`, o = hist.get(k) || (prev.get(k) || {}).u || [0, 0];
  n.u = [o[0] + 1, o[1] + (Number.isFinite(n.ms) && n.ms > 0 ? 1 : 0)];
}
// Только узлы с реальной задержкой. Мёртвые не сохраняются нигде (KEEP_DEAD = 0).
const alive = list.filter((n) => Number.isFinite(n.ms) && n.ms > 0).sort((a, b) => a.ms - b.ms);
console.log(`tested: ${list.length}, alive: ${alive.length}`);
if (!alive.length) { console.log('no alive nodes, keeping previous data'); process.exit(0); }
for (const n of alive) n.c = n.loc || n.c; // страна = страна выходного IP (из cloudflare trace)

const pub = ({ out, ms, ...n }) => ({ ...n, ping: ms, hl: n.p === 'vless' ? sanitizeVlessForHapp(n.l) : undefined }); // hl: ссылка для Happ
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
await write('claude', good.filter((x) => x.claude));
// Подписки для РФ: приоритет REALITY на 443, затем остальной REALITY, затем TLS (ws/grpc); внутри группы по пингу.
const prio = (x) => (/[?&]security=reality/.test(x.l) ? (x.o === 443 ? 0 : 1) : 2);
const ru = [...good].sort((a, b) => prio(a) - prio(b) || a.ms - b.ms);
await write('russia', ru);
await write('russia-mobile', ru.filter((x) => prio(x) === 0)); // REALITY + порт 443
for (const p of ['vless', 'trojan']) await write(p, good.filter((x) => x.p === p));
for (const [r, cs] of Object.entries(REGIONS)) await write(r, good.filter((x) => cs.includes(x.c)));
for (const c of new Set(good.map((x) => x.c).filter(Boolean))) await write(c, good.filter((x) => x.c === c));
await fs.rm(tmp, { recursive: true, force: true });
