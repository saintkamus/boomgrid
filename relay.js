#!/usr/bin/env node
'use strict';
/* =====================================================================
   BOOMGRID relay  -  zero-dependency room server (Node 16+)

   * serves the game itself at  http://HOST:PORT/   (boomgrid.html or index.html next to this file)
   * WebSocket endpoint at      /ws
   * 4-letter room codes, up to 4 players per room, plain message forwarding

   The relay never looks at gameplay: it only creates rooms, tells players
   who is in them, and forwards messages between them. Game traffic also tries
   to upgrade to direct WebRTC between players; the relay is the fallback path.

   Run:      node relay.js                (PORT=8787 by default)
   Options:  PORT=9000 HOST=0.0.0.0 GAME_FILE=/path/to/boomgrid.html node relay.js
   Health:   GET /health
   Behind a TLS proxy (Fly, Render, Cloudflare Tunnel, Caddy, nginx) the page is
   https and the game connects with wss:// automatically.
   ===================================================================== */
const http = require('http'), fs = require('fs'), path = require('path'), crypto = require('crypto'), os = require('os');

const PORT = parseInt(process.env.PORT, 10) || 8787;
const HOST = process.env.HOST || '0.0.0.0';
const MAX_PEERS = 4;                 // humans per room
const MAX_FRAME = 32 * 1024;         // bytes per websocket message
const ROOM_IDLE_MS = 60 * 60 * 1000; // empty/idle rooms are reaped
const GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';
const CODE_CHARS = 'ABCDEFGHJKMNPQRSTUVWXYZ'; // no I, L, O: hard to read out loud
const MAX_ROOMS = 500, MAX_CONN_PER_IP = 24;
const STARTED = Date.now();
const perIp = new Map();

const rooms = new Map();
let totalConns = 0, totalRooms = 0;
const log = (...a) => console.log(new Date().toISOString().slice(11, 19), ...a);

// ---------------------------------------------------------------- websocket framing
function frame(op, payload) {
  const len = payload.length; let head;
  if (len < 126) head = Buffer.from([0x80 | op, len]);
  else if (len < 65536) { head = Buffer.alloc(4); head[0] = 0x80 | op; head[1] = 126; head.writeUInt16BE(len, 2); }
  else { head = Buffer.alloc(10); head[0] = 0x80 | op; head[1] = 127; head.writeUInt32BE(0, 2); head.writeUInt32BE(len, 6); }
  return Buffer.concat([head, payload]);
}

class Conn {
  constructor(sock, ip) {
    this.sock = sock; this.ip = ip; this.alive = true; this.buf = Buffer.alloc(0); this.frag = null;
    this.id = -1; this.room = null; this.name = 'PLAYER'; this.lastSeen = Date.now();
    this.tokens = 600; this.tokT = Date.now(); this.flood = 0;
  }
  sendRaw(buf) {
    if (!this.alive) return;
    if (this.sock.writableLength > 2 * 1024 * 1024) { this.kill('slow consumer'); return; }
    try { this.sock.write(buf); } catch (e) { this.kill('write failed'); }
  }
  send(obj) { this.sendRaw(frame(0x1, Buffer.from(typeof obj === 'string' ? obj : JSON.stringify(obj)))); }
  err(code) { this.send({ t: 'err', code }); }
  kill(why) {
    if (!this.alive) return; this.alive = false;
    try { this.sock.destroy(); } catch (e) { }
    dropConn(this, why);
  }
  close(code) {
    if (!this.alive) return;
    const p = Buffer.alloc(2); p.writeUInt16BE(code || 1000, 0);
    try { this.sock.write(frame(0x8, p)); this.sock.end(); } catch (e) { }
    this.alive = false; dropConn(this, 'closed');
  }
  // token bucket: ~300 msgs/s sustained, bursts to 600
  allow() {
    const now = Date.now(); this.tokens = Math.min(600, this.tokens + (now - this.tokT) * 0.3); this.tokT = now;
    if (this.tokens < 1) { if (++this.flood > 600) this.kill('flood'); return false; }
    this.tokens -= 1; return true;
  }
  feed(chunk) {
    this.buf = this.buf.length ? Buffer.concat([this.buf, chunk]) : chunk;
    for (;;) {
      const b = this.buf; if (b.length < 2) return;
      const fin = !!(b[0] & 0x80), op = b[0] & 0x0f, masked = !!(b[1] & 0x80); let len = b[1] & 0x7f, off = 2;
      if (len === 126) { if (b.length < 4) return; len = b.readUInt16BE(2); off = 4; }
      else if (len === 127) { if (b.length < 10) return; if (b.readUInt32BE(2) !== 0) return this.kill('frame too big'); len = b.readUInt32BE(6); off = 10; }
      if (!masked) return this.kill('unmasked frame');
      if (len > MAX_FRAME) return this.kill('frame too big');
      if (b.length < off + 4 + len) return;
      const mask = b.subarray(off, off + 4), data = Buffer.from(b.subarray(off + 4, off + 4 + len));
      for (let i = 0; i < len; i++) data[i] ^= mask[i & 3];
      this.buf = b.subarray(off + 4 + len);
      if (op >= 0x8) { // control frames
        if (op === 0x8) return this.close(1000);
        if (op === 0x9) this.sendRaw(frame(0xA, data));
        this.lastSeen = Date.now(); continue;
      }
      if (op === 0x0) { // continuation
        if (!this.frag) return this.kill('bad continuation');
        this.frag.parts.push(data); this.frag.len += data.length;
        if (this.frag.len > MAX_FRAME) return this.kill('message too big');
        if (fin) { const full = Buffer.concat(this.frag.parts); const fop = this.frag.op; this.frag = null; this.message(fop, full); }
        continue;
      }
      if (!fin) { this.frag = { op, parts: [data], len: data.length }; continue; }
      this.message(op, data);
    }
  }
  message(op, data) {
    this.lastSeen = Date.now();
    if (op !== 0x1) return;               // text (JSON) only
    if (!this.allow()) return;
    let m; try { m = JSON.parse(data.toString('utf8')); } catch (e) { return; }
    if (m && typeof m === 'object') handle(this, m);
  }
}

// ---------------------------------------------------------------- rooms
const cleanName = s => String(s == null ? '' : s).toUpperCase().replace(/[^A-Z0-9 _.\-]/g, '').trim().slice(0, 8) || 'PLAYER';
function newCode() {
  for (let tries = 0; tries < 200; tries++) {
    let c = ''; for (let i = 0; i < 4; i++) c += CODE_CHARS[crypto.randomInt(CODE_CHARS.length)];
    if (!rooms.has(c)) return c;
  }
  return null;
}
function peerList(room) { return [...room.members.values()].map(m => ({ id: m.id, name: m.name })); }
function broadcast(room, obj, except) { const s = JSON.stringify(obj); for (const m of room.members.values()) if (m !== except) m.send(s); }

function handle(c, m) {
  switch (m.t) {
    case 'host': {
      if (c.room) return c.err('BUSY');
      if (rooms.size >= MAX_ROOMS) return c.err('NOROOMS');
      const code = newCode(); if (!code) return c.err('NOROOMS');
      const room = { code, host: c, members: new Map(), locked: false, created: Date.now(), active: Date.now() };
      c.id = 0; c.name = cleanName(m.name); c.room = room; room.members.set(0, c); rooms.set(code, room); totalRooms++;
      c.send({ t: 'hosted', room: code, id: 0 }); log('room', code, 'opened by', c.name, c.ip); return;
    }
    case 'join': {
      if (c.room) return c.err('BUSY');
      const code = String(m.room || '').toUpperCase().replace(/[^A-Z]/g, ''), room = rooms.get(code);
      if (!room) return c.err('NOROOM');
      if (room.locked) return c.err('LOCKED');
      if (room.members.size >= MAX_PEERS) return c.err('FULL');
      let id = 1; while (room.members.has(id)) id++;
      c.id = id; c.name = cleanName(m.name); c.room = room; room.members.set(id, c); room.active = Date.now();
      c.send({ t: 'joined', room: code, id, hostId: 0, peers: peerList(room) });
      broadcast(room, { t: 'peer', id, name: c.name }, c); log('room', code, c.name, 'joined (' + room.members.size + ')'); return;
    }
    case 'lock': { const r = c.room; if (r && r.host === c) { r.locked = !!m.v; r.active = Date.now(); } return; }
    case 'name': { const r = c.room; if (!r) return; c.name = cleanName(m.name); broadcast(r, { t: 'peer', id: c.id, name: c.name }, c); return; }
    case 'to': {
      const r = c.room; if (!r) return; r.active = Date.now();
      if (m.to === -1 || m.to === 'all') { const s = JSON.stringify({ t: 'm', from: c.id, d: m.d }); for (const p of r.members.values()) if (p !== c) p.send(s); }
      else { const p = r.members.get(m.to | 0); if (p && p !== c) p.send({ t: 'm', from: c.id, d: m.d }); }
      return;
    }
    case 'ping': return c.send({ t: 'pong', n: m.n });
    case 'leave': return c.close(1000);
  }
}
function dropConn(c, why) {
  const r = c.room; c.room = null;
  if (!r) return;
  r.members.delete(c.id);
  if (r.host === c) {          // host gone: the room is over
    broadcast(r, { t: 'closed' });
    for (const p of r.members.values()) { p.room = null; try { p.close(1000); } catch (e) { } }
    r.members.clear(); rooms.delete(r.code); log('room', r.code, 'closed (host left:', why + ')');
  } else {
    broadcast(r, { t: 'left', id: c.id }); r.active = Date.now(); log('room', r.code, c.name, 'left (' + r.members.size + ')');
  }
}

// ---------------------------------------------------------------- http
function gameFile() {
  for (const f of [process.env.GAME_FILE, path.join(__dirname, 'boomgrid.html'), path.join(__dirname, 'index.html')]) {
    if (f && fs.existsSync(f)) return f;
  }
  return null;
}
const server = http.createServer((req, res) => {
  const url = (req.url || '/').split('?')[0];
  if (url === '/' || url === '/index.html' || url === '/boomgrid.html') {
    const f = gameFile();
    if (!f) { res.writeHead(404, { 'content-type': 'text/plain' }); return res.end('boomgrid.html not found next to relay.js'); }
    res.writeHead(200, { 'content-type': 'text/html; charset=utf-8', 'cache-control': 'no-cache' });
    return fs.createReadStream(f).pipe(res);
  }
  if (url === '/favicon.ico') { res.writeHead(204); return res.end(); }
  if (url === '/health') {
    let players = 0; for (const r of rooms.values()) players += r.members.size;
    res.writeHead(200, { 'content-type': 'application/json', 'access-control-allow-origin': '*' });
    return res.end(JSON.stringify({ ok: true, rooms: rooms.size, players, conns: totalConns, uptime: Math.round((Date.now() - STARTED) / 1000) }));
  }
  res.writeHead(404, { 'content-type': 'text/plain' }); res.end('not found');
});
server.on('upgrade', (req, sock) => {
  const url = (req.url || '').split('?')[0], key = req.headers['sec-websocket-key'];
  if (url !== '/ws' || !key || String(req.headers.upgrade).toLowerCase() !== 'websocket') { sock.destroy(); return; }
  const accept = crypto.createHash('sha1').update(key + GUID).digest('base64');
  sock.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ' + accept + '\r\n\r\n');
  sock.setNoDelay(true); sock.setTimeout(0);
  const fwd = String(req.headers['x-forwarded-for'] || '').split(',')[0].trim();
  const ip = fwd || req.socket.remoteAddress || '?';
  if ((perIp.get(ip) || 0) >= MAX_CONN_PER_IP) { sock.destroy(); return; }
  perIp.set(ip, (perIp.get(ip) || 0) + 1);
  const c = new Conn(sock, ip); totalConns++;
  sock.on('close', () => { const n = (perIp.get(ip) || 1) - 1; if (n <= 0) perIp.delete(ip); else perIp.set(ip, n); });
  sock.on('data', d => { try { c.feed(d); } catch (e) { c.kill('parse error'); } });
  sock.on('close', () => { if (c.alive) { c.alive = false; dropConn(c, 'socket closed'); } });
  sock.on('error', () => { c.kill('socket error'); });
});

// keep-alive + reaping
setInterval(() => {
  const now = Date.now();
  for (const r of [...rooms.values()]) {
    for (const m of [...r.members.values()]) {
      if (now - m.lastSeen > 60000) { m.kill('timeout'); continue; }
      m.sendRaw(frame(0x9, Buffer.alloc(0)));
    }
    if (rooms.has(r.code) && now - r.active > ROOM_IDLE_MS) { for (const m of [...r.members.values()]) m.kill('idle room'); }
  }
}, 15000).unref();

server.listen(PORT, HOST, () => {
  const ips = []; for (const list of Object.values(os.networkInterfaces())) for (const i of list || []) if (i.family === 'IPv4' && !i.internal) ips.push(i.address);
  log('BOOMGRID relay listening on port', PORT);
  log('  play here:  http://localhost:' + PORT + '/' + (gameFile() ? '' : '   (no boomgrid.html found next to relay.js!)'));
  for (const ip of ips) log('  on your LAN: http://' + ip + ':' + PORT + '/');
  log('  WebSocket:  /ws    health: /health');
});
process.on('SIGINT', () => { log('bye'); process.exit(0); });
process.on('uncaughtException', e => log('uncaught', e && e.stack || e));
