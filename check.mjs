// Сбор ключей, реальная проверка через Xray-core, замер задержки, геопривязка, генерация подписок.
import { spawn, execFile } from 'node:child_process';
import { promisify } from 'node:util';
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
const MAX_TEST = 1500, PAR = 40, KEEP_DEAD = 100, MAX_SUB = 300;
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
const okHost = (h) => /^(?=.{1,253}$)([a-z0-9-]+\.)+[a-z][a-z0-9-]+$/i.test(h);
// Приводит VLESS-ссылку к строгому единому виду. Возвращает null, если ключ непригоден (битый UUID, нет pbk у Reality и т.п.).
function sanitizeVlessUri(raw) {
  let u; try { u = new URL(String(raw).trim()); } catch { return null; }
  if (u.protocol !== 'vless:') return null;
  let id; try { id = decodeURIComponent(u.username).toLowerCase(); } catch { return null; }
  const host = u.hostname, port = +u.port;
  if (!/^[0-9a-f]{8}(-[0-9a-f]{4}){3}-[0-9a-f]{12}$/.test(id) || !host || !(port > 0 && port < 65536)) return null;
  const g = (k) => (u.searchParams.get(k) || '').trim();
  const net = NETS[g('type').toLowerCase()] || 'tcp';
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
    let fp = g('fp').toLowerCase();
    if (!FPS.includes(fp)) fp = 'chrome';
    let flow = g('flow');
    if (!(net === 'tcp' && /^xtls-rprx-vision(-udp443)?$/.test(flow))) flow = '';
    add('flow', flow); add('security', sec); add('sni', sni); add('fp', fp);
    if (sec === 'tls') add('alpn', g('alpn').split(',').map((s) => s.trim()).filter((s) => ['h2', 'http/1.1', 'h3'].includes(s)).join(','));
    if (sec === 'reality') { add('pbk', pbk); const sid = g('sid'); add('sid', /^[0-9a-f]{0,16}$/i.test(sid) ? sid : ''); add('spx', g('spx')); }
  } else add('security', 'none');
  add('type', net);
  if (net === 'tcp' && g('headerType') === 'http') { add('headerType', 'http'); add('host', hp); add('path', g('path') || '/'); }
  if (['ws', 'httpupgrade', 'xhttp', 'h2'].includes(net)) { add('host', hp); const p = g('path') || '/'; add('path', p.startsWith('/') ? p : '/' + p); }
  if (net === 'grpc') { add('serviceName', g('serviceName')); const m = g('mode'); if (['gun', 'multi'].includes(m)) add('mode', m); }
  let name; try { name = decodeURIComponent(u.hash.slice(1)); } catch { name = u.hash.slice(1); }
  name = (name.replace(/[\u0000-\u001f]/g, '').trim() || `${host}:${port}`).slice(0, 80);
  return `vless://${id}@${host}:${port}?${q.map(([k, v]) => `${k}=${encodeURIComponent(v)}`).join('&')}#${encodeURIComponent(name)}`;
}

function stream(net, sec, o) {
  if (!['tcp', 'ws', 'grpc', 'httpupgrade'].includes(net)) throw new Error('transport');
  if (net === 'tcp' && o.type && o.type !== 'none') throw new Error('http header');
  const s = { network: net, security: sec };
  if (sec === 'tls') s.tlsSettings = { serverName: o.sni || o.host || undefined, fingerprint: o.fp || 'chrome',
    alpn: o.alpn ? o.alpn.split(',') : undefined, allowInsecure: o.insecure === '1' || o.insecure === 'true' };
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
    if (!j.add || !j.port || !j.id) throw new Error('vmess');
    host = j.add; port = +j.port; name = j.ps || name;
    out = { protocol: 'vmess', settings: { vnext: [{ address: host, port, users: [{ id: j.id, alterId: +j.aid || 0, security: j.scy || 'auto' }] }] },
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
    out = { protocol: 'shadowsocks', settings: { servers: [{ address: host, port, method, password: pw.join(':') }] } };
  } else {
    const u = new URL(link), q = Object.fromEntries(u.searchParams);
    host = u.hostname.replace(/[\[\]]/g, ''); port = +u.port;
    if (!host || !port || !u.username) throw new Error(p);
    const o = { ...q, service: q.serviceName, insecure: q.allowInsecure || q.insecure };
    const st = stream(q.type || 'tcp', q.security || (p === 'trojan' ? 'tls' : 'none'), o);
    out = p === 'vless'
      ? { protocol: 'vless', settings: { vnext: [{ address: host, port, users: [{ id: decodeURIComponent(u.username), encryption: 'none', flow: q.flow || undefined }] }] }, streamSettings: st }
      : { protocol: 'trojan', settings: { servers: [{ address: host, port, password: decodeURIComponent(u.username) }] }, streamSettings: st };
  }
  return { p, h: host, o: port, n: name.slice(0, 80), c: flag(name), l: link, out };
}

async function collect() {
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
      const k = n && `${n.p}|${n.h}|${n.o}`;
      if (n && !seen.has(k)) { seen.add(k); all.push(n); }
    }
  }
  console.log(`sources ok: ${res.filter((r) => r.status === 'fulfilled').length}/${SOURCES.length}, valid: ${all.length}, invalid: ${bad}`);
  return all.sort(() => Math.random() - 0.5).slice(0, MAX_TEST);
}

// Реальная проверка: поднимаем Xray с этим ключом и делаем HTTPS-запрос через него.
async function test(n, port) {
  const cfg = path.join(tmp, `${port}.json`);
  await fs.writeFile(cfg, JSON.stringify({ log: { loglevel: 'none' },
    inbounds: [{ listen: '127.0.0.1', port, protocol: 'socks', settings: { udp: false } }], outbounds: [n.out] }));
  const x = spawn('./bin/xray', ['run', '-c', cfg], { stdio: 'ignore' });
  let best = null;
  try {
    await sleep(700);
    for (let i = 0; i < 2; i++) { // 1-й запрос прогревает соединение, берём лучший из двух
      try {
        const { stdout } = await run('curl', ['-s', '-o', '/dev/null', '--socks5-hostname', `127.0.0.1:${port}`,
          '--max-time', '7', '-w', '%{http_code} %{time_total}', 'https://www.gstatic.com/generate_204']);
        const [code, t] = stdout.split(' ');
        if (code === '204') { const ms = Math.max(1, Math.round(+t * 1000)); best = best === null ? ms : Math.min(best, ms); }
      } catch { /* таймаут или отказ = не рабочий */ }
    }
  } finally { x.kill('SIGKILL'); await sleep(60); }
  return best;
}

async function geo(nodes) {
  const need = nodes.filter((x) => !x.c);
  for (let i = 0; i < need.length; i += 100) {
    const part = need.slice(i, i + 100);
    try {
      const r = await fetch('http://ip-api.com/batch?fields=countryCode', { method: 'POST', body: JSON.stringify(part.map((x) => x.h)) });
      (await r.json()).forEach((g, k) => { part[k].c = g.countryCode || ''; });
    } catch { /* без страны */ }
    await sleep(1500);
  }
}

const list = await collect();
let idx = 0;
await Promise.all(Array.from({ length: PAR }, async (_, w) => {
  while (idx < list.length) { const n = list[idx++]; n.ms = await test(n, 20000 + w); }
}));

const alive = list.filter((n) => n.ms !== null).sort((a, b) => a.ms - b.ms);
const dead = list.filter((n) => n.ms === null).slice(0, KEEP_DEAD);
console.log(`tested: ${list.length}, alive: ${alive.length}`);
if (!alive.length) { console.log('no alive nodes, keeping previous data'); process.exit(0); }
await geo(alive);

const pub = ({ out, ...n }) => n;
await fs.mkdir('data', { recursive: true });
await fs.writeFile('data/nodes.json', JSON.stringify({ updated: new Date().toISOString(), tested: list.length,
  nodes: [...alive, ...dead].map(pub) }));

await fs.rm('sub', { recursive: true, force: true });
await fs.mkdir('sub', { recursive: true });
const write = async (name, arr) => {
  if (!arr.length) return; // пустой файл клиенты считают невалидной подпиской
  await fs.writeFile(`sub/${name}.txt`, Buffer.from(arr.slice(0, MAX_SUB).map((x) => x.l).join('\n')).toString('base64'));
};
await write('all', alive);
for (const p of ['vless', 'vmess', 'trojan', 'ss']) await write(p, alive.filter((x) => x.p === p));
for (const [r, cs] of Object.entries(REGIONS)) await write(r, alive.filter((x) => cs.includes(x.c)));
for (const c of new Set(alive.map((x) => x.c).filter(Boolean))) await write(c, alive.filter((x) => x.c === c));
