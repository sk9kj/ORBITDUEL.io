'use strict';
/* Orbit Duel : serveur autoritaire. Collisions, événements, résultats et ELO sont calculés ici.
   Le client n'envoie que la position visée par le curseur. */
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const { WebSocketServer } = require('ws');

const PORT = process.env.PORT || 3000;
const DB_FILE = path.join(__dirname, 'data', 'users.json');
let INDEX_HTML;
try {
  INDEX_HTML = fs.readFileSync(path.join(__dirname, 'public', 'index.html'));
} catch (e) {
  console.error('ERREUR : public/index.html introuvable dans le dépôt. Ajoutez le dossier public/ avec index.html puis redéployez.');
  INDEX_HTML = Buffer.from('<!doctype html><meta charset="utf-8"><h1>Orbit Duel</h1><p>Fichier public/index.html manquant sur le serveur.</p>');
}

// ---------- Réglages de jeu ----------
const TICK = 1 / 30;
const ZONE_START = 500, ZONE_MIN = 130, ZONE_TIME = 150, MATCH_MAX = 240;
const R = 22, MAX_SPEED = 320, ACC = 1200, FRICTION = 1.8;
const EVENT_EVERY = 15, ELO_K = 32;
const START_COINS = 200, WIN_COINS = 60, DRAW_COINS = 30, LOSS_COINS = 20;

// ---------- Boutique (cosmétiques du curseur) ----------
const CATALOG = [
  { id: 'c_cyan', type: 'color', name: 'Cyan', price: 0, value: '#22d3ee' },
  { id: 'c_rose', type: 'color', name: 'Rose', price: 150, value: '#f43f5e' },
  { id: 'c_or', type: 'color', name: 'Or', price: 250, value: '#facc15' },
  { id: 'c_violet', type: 'color', name: 'Violet', price: 200, value: '#a855f7' },
  { id: 'c_emeraude', type: 'color', name: 'Émeraude', price: 150, value: '#10b981' },
  { id: 's_circle', type: 'shape', name: 'Cercle', price: 0, value: 'circle' },
  { id: 's_ring', type: 'shape', name: 'Anneau', price: 300, value: 'ring' },
  { id: 's_star', type: 'shape', name: 'Étoile', price: 400, value: 'star' },
  { id: 's_diamond', type: 'shape', name: 'Losange', price: 400, value: 'diamond' },
  { id: 't_none', type: 'trail', name: 'Aucune', price: 0, value: 'none' },
  { id: 't_comet', type: 'trail', name: 'Comète', price: 250, value: 'comet' },
  { id: 't_sparks', type: 'trail', name: 'Étincelles', price: 350, value: 'sparks' },
  { id: 't_rainbow', type: 'trail', name: 'Arc-en-ciel', price: 500, value: 'rainbow' },
  { id: 'p_none', type: 'particle', name: 'Aucune', price: 0, value: 'none' },
  { id: 'p_bubbles', type: 'particle', name: 'Bulles', price: 300, value: 'bubbles' },
  { id: 'p_fire', type: 'particle', name: 'Flammes', price: 450, value: 'fire' },
  { id: 'f_none', type: 'fx', name: 'Aucun', price: 0, value: 'none' },
  { id: 'f_glow', type: 'fx', name: 'Halo', price: 350, value: 'glow' },
  { id: 'f_pulse', type: 'fx', name: 'Pulsation', price: 450, value: 'pulse' },
];
const DEFAULT_OWNED = CATALOG.filter(i => i.price === 0).map(i => i.id);
const DEFAULT_EQUIP = { color: 'c_cyan', shape: 's_circle', trail: 't_none', particle: 'p_none', fx: 'f_none' };
const DEFAULT_SETTINGS = { sound: true, volume: 60, effects: 'full' };

// ---------- Base de données (fichier JSON) ----------
let db = { users: {} };
try { db = JSON.parse(fs.readFileSync(DB_FILE, 'utf8')); } catch (_) { /* première exécution */ }
let saveTimer = null;
function save() {
  clearTimeout(saveTimer);
  saveTimer = setTimeout(() => {
    fs.mkdirSync(path.dirname(DB_FILE), { recursive: true });
    fs.writeFileSync(DB_FILE + '.tmp', JSON.stringify(db, null, 2));
    fs.renameSync(DB_FILE + '.tmp', DB_FILE);
  }, 300);
}

// ---------- État en mémoire ----------
const sessions = new Map();  // token -> pseudo
const clients = new Map();   // pseudo -> socket connecté
const queues = { ranked: [], casual: [] };
const matches = new Map();
let invites = [];            // { from, to }

// ---------- Utilitaires ----------
const getUser = n => (typeof n === 'string' ? db.users[n.toLowerCase()] : undefined);
const rankOf = elo => elo < 1100 ? 'Bronze' : elo < 1300 ? 'Argent' : elo < 1500 ? 'Or' : elo < 1700 ? 'Platine' : elo < 1900 ? 'Diamant' : 'Maître';
const profile = u => ({ name: u.name, elo: u.elo, rank: rankOf(u.elo), wins: u.wins, losses: u.losses, draws: u.draws, coins: u.coins, owned: u.owned, equipped: u.equipped, settings: { ...DEFAULT_SETTINGS, ...(u.settings || {}) } });
const lookOf = u => Object.fromEntries(Object.entries(u.equipped).map(([k, id]) => [k, CATALOG.find(i => i.id === id)?.value ?? null]));
const send = (ws, msg) => { if (ws && ws.readyState === 1) ws.send(JSON.stringify(msg)); };
const err = (ws, msg) => send(ws, { type: 'notice', msg, error: true });
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
const round = v => Math.round(v * 10) / 10;
const rndPoint = rad => { const r = rad * Math.sqrt(Math.random()), a = Math.random() * Math.PI * 2; return { x: r * Math.cos(a), y: r * Math.sin(a) }; };

// ---------- Comptes ----------
const hashPw = (pw, salt) => crypto.scryptSync(pw, salt, 64).toString('hex');
function issue(u) {
  const token = crypto.randomBytes(32).toString('hex');
  sessions.set(token, u.name);
  return { token, user: profile(u) };
}
function register(username, password) {
  if (typeof username !== 'string' || !/^[A-Za-z0-9_]{3,16}$/.test(username)) return { status: 400, error: 'Pseudo : 3 à 16 caractères (lettres, chiffres, _).' };
  if (typeof password !== 'string' || password.length < 6 || password.length > 128) return { status: 400, error: 'Mot de passe : 6 caractères minimum.' };
  if (getUser(username)) return { status: 409, error: 'Ce pseudo est déjà pris.' };
  const salt = crypto.randomBytes(16).toString('hex');
  const u = { name: username, salt, hash: hashPw(password, salt), elo: 1000, wins: 0, losses: 0, draws: 0, coins: START_COINS, owned: [...DEFAULT_OWNED], equipped: { ...DEFAULT_EQUIP }, friends: [], requests: [], settings: { ...DEFAULT_SETTINGS }, created: Date.now() };
  db.users[username.toLowerCase()] = u;
  save();
  return issue(u);
}
function login(username, password) {
  const u = getUser(username);
  if (!u || typeof password !== 'string' || !crypto.timingSafeEqual(Buffer.from(hashPw(password, u.salt), 'hex'), Buffer.from(u.hash, 'hex')))
    return { status: 401, error: 'Pseudo ou mot de passe incorrect.' };
  return issue(u);
}

// ---------- HTTP (page + API de comptes) ----------
const server = http.createServer((req, res) => {
  const url = new URL(req.url, 'http://localhost');
  if (req.method === 'POST' && (url.pathname === '/api/register' || url.pathname === '/api/login')) {
    let body = '';
    req.on('data', c => { body += c; if (body.length > 4096) req.destroy(); });
    req.on('end', () => {
      let d = {};
      try { d = JSON.parse(body); } catch (_) { /* corps invalide */ }
      const r = url.pathname === '/api/register' ? register(d.username, d.password) : login(d.username, d.password);
      res.writeHead(r.status || 200, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify(r));
    });
    return;
  }
  if (url.pathname === '/' || url.pathname === '/index.html') {
    res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8' });
    return res.end(INDEX_HTML);
  }
  res.writeHead(404); res.end('404');
});

// ---------- WebSocket ----------
const wss = new WebSocketServer({ server });

function broadcastOnline() {
  const msg = JSON.stringify({ type: 'online', count: clients.size });
  wss.clients.forEach(ws => { if (ws.readyState === 1) ws.send(msg); });
}
function friendsOf(u) {
  return {
    type: 'friends',
    requests: u.requests,
    friends: u.friends.map(n => {
      const f = getUser(n), s = clients.get(f.name);
      return { name: f.name, elo: f.elo, rank: rankOf(f.elo), status: !s ? 'hors ligne' : s.match ? 'en partie' : s.queued ? 'en file' : 'en ligne' };
    }),
  };
}
const pushFriends = name => send(clients.get(name), friendsOf(getUser(name)));
const pushAllFriends = () => clients.forEach((_, n) => pushFriends(n));

function dequeue(ws) {
  if (ws.queued) { queues[ws.queued] = queues[ws.queued].filter(s => s !== ws); ws.queued = null; }
}
function unbind(ws) {
  dequeue(ws);
  if (ws.match) leaveMatch(ws);
  invites = invites.filter(i => i.from !== ws.user && i.to !== ws.user);
  if (ws.user && clients.get(ws.user) === ws) clients.delete(ws.user);
  pushAllFriends();
  broadcastOnline();
}

function auth(ws, token) {
  const u = getUser(sessions.get(token));
  if (!u) return send(ws, { type: 'authFail' });
  const old = clients.get(u.name);
  if (old && old !== ws) { // une seule session active : la nouvelle remplace l'ancienne
    if (old.match) { old.match.sockets = old.match.sockets.map(s => (s === old ? ws : s)); ws.match = old.match; }
    if (old.queued) { const mode = old.queued; queues[mode] = queues[mode].map(s => (s === old ? ws : s)); ws.queued = mode; }
    old.match = null; old.queued = null; old.user = null;
    old.terminate();
  }
  ws.user = u.name;
  clients.set(u.name, ws);
  send(ws, { type: 'profile', user: profile(u), catalog: CATALOG });
  if (ws.match) send(ws, matchInfo(ws.match, ws.match.sockets.indexOf(ws)));
  broadcastOnline();
  pushAllFriends();
}

wss.on('connection', ws => {
  ws.alive = true;
  ws.on('pong', () => { ws.alive = true; });
  ws.on('message', raw => {
    let m;
    try { m = JSON.parse(raw); } catch (_) { return; }
    try { onMessage(ws, m); } catch (e) { console.error(e); err(ws, 'Erreur serveur.'); }
  });
  ws.on('close', () => unbind(ws));
  send(ws, { type: 'online', count: clients.size });
});
setInterval(() => wss.clients.forEach(ws => { if (!ws.alive) return ws.terminate(); ws.alive = false; ws.ping(); }), 20000);

function onMessage(ws, m) {
  if (m.type === 'auth') return auth(ws, m.token);
  if (m.type === 'logout') { if (ws.user) { unbind(ws); ws.user = null; } return; }
  if (!ws.user) return send(ws, { type: 'authFail' });
  const me = getUser(ws.user);

  switch (m.type) {
    // --- File de matchmaking : JOUER (casual) et RANKED (ELO) ---
    case 'queue': {
      if (ws.match || ws.queued) return;
      const mode = m.mode === 'ranked' ? 'ranked' : 'casual';
      ws.queued = mode; ws.queuedAt = Date.now(); queues[mode].push(ws);
      send(ws, { type: 'queued', mode });
      tryPair(mode);
      return pushAllFriends();
    }
    case 'cancelQueue':
      dequeue(ws); send(ws, { type: 'queueCancelled' });
      return pushAllFriends();

    // --- Amis ---
    case 'friendRequest': {
      const t = getUser(m.to);
      if (!t) return err(ws, 'Joueur introuvable.');
      if (t.name === me.name) return err(ws, 'Tu ne peux pas t\'ajouter toi-même.');
      if (me.friends.includes(t.name)) return err(ws, 'Déjà dans tes amis.');
      if (me.requests.includes(t.name)) return err(ws, 'Ce joueur t\'a déjà envoyé une demande : accepte-la.');
      if (t.requests.includes(me.name)) return err(ws, 'Demande déjà envoyée.');
      t.requests.push(me.name); save(); pushFriends(t.name);
      return send(ws, { type: 'notice', msg: `Demande envoyée à ${t.name}.` });
    }
    case 'friendAccept': {
      const f = getUser(m.from);
      if (!f || !me.requests.includes(f.name)) return err(ws, 'Demande introuvable.');
      me.requests = me.requests.filter(n => n !== f.name);
      if (!me.friends.includes(f.name)) me.friends.push(f.name);
      if (!f.friends.includes(me.name)) f.friends.push(me.name);
      save(); pushFriends(me.name); pushFriends(f.name);
      return;
    }
    case 'friendDecline':
      me.requests = me.requests.filter(n => n !== m.from); save();
      return pushFriends(me.name);
    case 'friendRemove': {
      const f = getUser(m.name);
      me.friends = me.friends.filter(n => n !== m.name);
      if (f) f.friends = f.friends.filter(n => n !== me.name);
      save(); pushFriends(me.name); if (f) pushFriends(f.name);
      return;
    }

    // --- Invitations 1V1 privées ---
    case 'invite': {
      const t = getUser(m.to), tws = t && clients.get(t.name);
      if (!t || !me.friends.includes(t.name)) return err(ws, 'Ce joueur n\'est pas dans tes amis.');
      if (!tws) return err(ws, 'Cet ami est hors ligne.');
      if (tws.match || tws.queued || ws.match || ws.queued) return err(ws, 'Vous devez être libres pour un 1V1.');
      if (invites.some(i => i.from === me.name && i.to === t.name)) return err(ws, 'Invitation déjà envoyée.');
      const inv = { from: me.name, to: t.name };
      invites.push(inv);
      setTimeout(() => { invites = invites.filter(i => i !== inv); }, 60000);
      send(tws, { type: 'invite', from: me.name });
      return send(ws, { type: 'notice', msg: `Invitation envoyée à ${t.name}.` });
    }
    case 'inviteResponse': {
      const inv = invites.find(i => i.from === m.from && i.to === me.name);
      if (!inv) return err(ws, 'Invitation expirée.');
      invites = invites.filter(i => i !== inv);
      const host = clients.get(inv.from);
      if (!host) return err(ws, 'Ton ami s\'est déconnecté.');
      if (!m.accept) return send(host, { type: 'notice', msg: `${me.name} a refusé ton invitation.` });
      if (host.match || host.queued || ws.match || ws.queued) return err(ws, 'Un des joueurs est déjà occupé.');
      return startMatch(host, ws, 'private');
    }

    // --- Partie en cours ---
    case 'input':
      if (ws.match) ws.match.setTarget(ws, m.x, m.y);
      return;
    case 'leave':
      return leaveMatch(ws);
    case 'rematch': {
      const mt = ws.match;
      if (!mt || !mt.ended) return err(ws, 'Aucune revanche possible.');
      if (!mt.sockets.every(s => s.match === mt)) return err(ws, 'L\'adversaire a quitté la partie.');
      mt.rematch.add(me.name);
      if (mt.rematch.size < 2) return send(mt.sockets.find(s => s !== ws), { type: 'notice', msg: `${me.name} demande une revanche !` });
      mt.sockets.forEach(s => { s.match = null; });
      matches.delete(mt.id);
      return startMatch(mt.sockets[0], mt.sockets[1], mt.mode);
    }

    // --- Boutique (achat puis équipement) ---
    case 'buy': {
      const it = CATALOG.find(i => i.id === m.id);
      if (!it) return err(ws, 'Article inconnu.');
      if (!me.owned.includes(it.id)) {
        if (me.coins < it.price) return err(ws, 'Pas assez de pièces.');
        me.coins -= it.price; me.owned.push(it.id);
      }
      me.equipped[it.type] = it.id; save();
      return send(ws, { type: 'profile', user: profile(me) });
    }

    // --- Réglages propres au compte (sauvegardés côté serveur) ---
    case 'settings': {
      if (!me.settings) me.settings = { ...DEFAULT_SETTINGS };
      if (typeof m.sound === 'boolean') me.settings.sound = m.sound;
      if (Number.isFinite(m.volume)) me.settings.volume = clamp(Math.round(m.volume), 0, 100);
      if (m.effects === 'full' || m.effects === 'reduced') me.settings.effects = m.effects;
      save();
      return send(ws, { type: 'profile', user: profile(me) });
    }

    // --- Classement mondial ---
    case 'leaderboard': {
      const all = Object.values(db.users).sort((a, b) => b.elo - a.elo || b.wins - a.wins);
      return send(ws, {
        type: 'leaderboard',
        list: all.slice(0, 50).map(u => ({ name: u.name, elo: u.elo, rank: rankOf(u.elo), wins: u.wins, losses: u.losses })),
        myPos: all.indexOf(me) + 1,
      });
    }
    default:
      return;
  }
}

// ---------- Matchmaking ----------
function tryPair(mode) {
  const q = queues[mode];
  const slack = w => 250 + 25 * (Date.now() - w.queuedAt) / 1000; // la fenêtre ELO s'élargit avec l'attente
  for (let i = 0; i < q.length; i++) {
    for (let j = i + 1; j < q.length; j++) {
      const a = q[i], b = q[j];
      if (a.user === b.user) continue;
      if (mode === 'ranked' && Math.abs(getUser(a.user).elo - getUser(b.user).elo) > Math.max(slack(a), slack(b))) continue;
      q.splice(j, 1); q.splice(i, 1);
      a.queued = b.queued = null;
      startMatch(a, b, mode);
      return tryPair(mode);
    }
  }
}
setInterval(() => tryPair('ranked'), 1000);

function matchInfo(mt, side) {
  return {
    type: 'matchFound', mode: mt.mode, side,
    players: mt.sockets.map(s => { const u = getUser(s.user); return { name: u.name, elo: u.elo, rank: rankOf(u.elo), look: lookOf(u) }; }),
  };
}
function startMatch(a, b, mode) {
  const mt = new Match([a, b], mode);
  matches.set(mt.id, mt);
  a.match = b.match = mt;
  send(a, matchInfo(mt, 0));
  send(b, matchInfo(mt, 1));
  pushAllFriends();
}
function leaveMatch(ws) {
  const mt = ws.match;
  if (!mt) return;
  if (!mt.ended) { mt.ended = true; mt.phase = 'ended'; settle(mt, 1 - mt.sockets.indexOf(ws), ws); }
  ws.match = null;
  if (!mt.sockets.some(s => s.match === mt)) matches.delete(mt.id);
}

// Applique le résultat : ELO (ranked), victoires/défaites, pièces, puis prévient les joueurs.
function settle(mt, w, skip) {
  const us = mt.sockets.map(s => getUser(s.user));
  const delta = [0, 0], gained = [0, 0];
  if (mt.mode === 'ranked') {
    const e0 = 1 / (1 + 10 ** ((us[1].elo - us[0].elo) / 400)), e = [e0, 1 - e0];
    [0, 1].forEach(i => {
      const s = w === null ? 0.5 : w === i ? 1 : 0;
      delta[i] = Math.round(ELO_K * (s - e[i]));
      us[i].elo = Math.max(0, us[i].elo + delta[i]);
    });
  }
  [0, 1].forEach(i => {
    const u = us[i];
    if (w === null) { u.draws++; gained[i] = DRAW_COINS; }
    else if (w === i) { u.wins++; gained[i] = WIN_COINS; }
    else { u.losses++; gained[i] = LOSS_COINS; }
    u.coins += gained[i];
  });
  save();
  mt.sockets.forEach((s, i) => {
    if (s === skip) return;
    send(s, { type: 'matchEnd', mode: mt.mode, result: w === null ? 'draw' : w === i ? 'win' : 'lose', eloDelta: delta[i], coins: gained[i], profile: profile(us[i]) });
  });
  pushAllFriends();
}

// ---------- Simulation d'une arène ----------
class Match {
  constructor(sockets, mode) {
    this.id = crypto.randomUUID();
    this.mode = mode;
    this.sockets = sockets;
    this.phase = 'countdown';
    this.countdown = 3;
    this.t = 0;
    this.zoneR = ZONE_START;
    this.nextEvent = EVENT_EVERY;
    this.p = [-220, 220].map(x => ({ x, y: 0, vx: 0, vy: 0, tx: x, ty: 0, hp: 3, alive: true, fell: false }));
    this.obs = []; this.tnt = []; this.wind = null; this.gravity = 0; this.banner = null; this.fx = [];
    this.ended = false;
    this.rematch = new Set();
  }

  setTarget(ws, x, y) {
    const i = this.sockets.indexOf(ws);
    if (i < 0 || !Number.isFinite(x) || !Number.isFinite(y)) return;
    this.p[i].tx = clamp(x, -ZONE_START, ZONE_START);
    this.p[i].ty = clamp(y, -ZONE_START, ZONE_START);
  }

  step(dt) {
    if (this.phase === 'countdown') {
      this.countdown -= dt;
      if (this.countdown <= 0) { this.phase = 'playing'; this.banner = { name: 'GO !', ttl: 1.5 }; }
      return;
    }
    this.t += dt;
    this.zoneR = Math.max(ZONE_MIN, ZONE_START - (ZONE_START - ZONE_MIN) * Math.min(1, this.t / ZONE_TIME));
    if (this.t >= this.nextEvent) { this.nextEvent += EVENT_EVERY; this.spawnEvent(); }
    this.updateWorld(dt);
    this.physics(dt);
    this.checkEnd();
  }

  spawnEvent() {
    const kinds = ['vent', 'tnt', 'obstacles', 'gravité', 'onde de choc'];
    const k = kinds[Math.floor(Math.random() * kinds.length)];
    this.banner = { name: k.toUpperCase(), ttl: 2.5 };
    if (k === 'vent') { const a = Math.random() * Math.PI * 2; this.wind = { dx: Math.cos(a), dy: Math.sin(a), ttl: 6 }; }
    if (k === 'tnt') for (let i = 0; i < 2; i++) this.tnt.push({ ...rndPoint(this.zoneR * 0.8), fuse: 2.5 });
    if (k === 'obstacles') for (let i = 0; i < 4; i++) this.obs.push({ ...rndPoint(this.zoneR * 0.85), r: 36, ttl: 12 });
    if (k === 'gravité') this.gravity = 5;
    if (k === 'onde de choc') { const c = rndPoint(this.zoneR * 0.6); this.fx.push({ type: 'onde', x: c.x, y: c.y }); this.push(c, 240, 700); }
  }

  push(c, radius, strength) {
    this.p.forEach(p => {
      if (!p.alive) return;
      const dx = p.x - c.x, dy = p.y - c.y, d = Math.hypot(dx, dy);
      if (d >= radius) return;
      const f = (1 - d / radius) * strength;
      const nx = d > 1 ? dx / d : 1, ny = d > 1 ? dy / d : 0;
      p.vx += nx * f; p.vy += ny * f;
    });
  }

  explode(c) {
    this.fx.push({ type: 'boom', x: c.x, y: c.y });
    this.push(c, 95 + R, 650);
    this.p.forEach(p => {
      if (!p.alive || Math.hypot(p.x - c.x, p.y - c.y) > 95 + R) return;
      p.hp -= 1;
      this.fx.push({ type: 'hit', x: p.x, y: p.y });
      if (p.hp <= 0) p.alive = false;
    });
  }

  updateWorld(dt) {
    this.obs.forEach(o => { o.ttl -= dt; });
    this.obs = this.obs.filter(o => o.ttl > 0);
    this.tnt.forEach(b => { b.fuse -= dt; });
    const boom = this.tnt.filter(b => b.fuse <= 0);
    this.tnt = this.tnt.filter(b => b.fuse > 0);
    boom.forEach(b => this.explode(b));
    if (this.wind && (this.wind.ttl -= dt) <= 0) this.wind = null;
    if (this.gravity > 0) this.gravity -= dt;
    if (this.banner && (this.banner.ttl -= dt) <= 0) this.banner = null;
  }

  physics(dt) {
    const decay = Math.exp(-FRICTION * dt);
    this.p.forEach(p => {
      if (!p.alive) return;
      const dx = p.tx - p.x, dy = p.ty - p.y, d = Math.hypot(dx, dy);
      const sp = Math.min(MAX_SPEED, d * 4);
      let ax = (d > 1 ? (dx / d) * sp : 0) - p.vx;
      let ay = (d > 1 ? (dy / d) * sp : 0) - p.vy;
      const a = Math.hypot(ax, ay), lim = ACC * dt;
      if (a > lim) { ax *= lim / a; ay *= lim / a; }
      p.vx += ax; p.vy += ay;
      if (this.wind) { p.vx += this.wind.dx * 260 * dt; p.vy += this.wind.dy * 260 * dt; }
      if (this.gravity > 0) { const c = Math.hypot(p.x, p.y) || 1; p.vx -= (p.x / c) * 260 * dt; p.vy -= (p.y / c) * 260 * dt; }
      p.vx *= decay; p.vy *= decay;
      p.x += p.vx * dt; p.y += p.vy * dt;
    });

    // Collisions avec les obstacles
    this.p.forEach(p => {
      if (!p.alive) return;
      this.obs.forEach(o => {
        const dx = p.x - o.x, dy = p.y - o.y, d = Math.hypot(dx, dy) || 0.001, min = R + o.r;
        if (d >= min) return;
        const nx = dx / d, ny = dy / d;
        p.x += nx * (min - d); p.y += ny * (min - d);
        const vn = p.vx * nx + p.vy * ny;
        if (vn < 0) { p.vx -= 1.6 * vn * nx; p.vy -= 1.6 * vn * ny; }
      });
    });

    // Collision entre les deux joueurs (rebond)
    const [a, b] = this.p;
    if (a.alive && b.alive) {
      const dx = b.x - a.x, dy = b.y - a.y, d = Math.hypot(dx, dy) || 0.001;
      if (d < 2 * R) {
        const nx = dx / d, ny = dy / d, ov = 2 * R - d;
        a.x -= nx * ov / 2; a.y -= ny * ov / 2; b.x += nx * ov / 2; b.y += ny * ov / 2;
        const rv = (b.vx - a.vx) * nx + (b.vy - a.vy) * ny;
        if (rv < 0) { const k = 0.9 * rv; a.vx += nx * k; a.vy += ny * k; b.vx -= nx * k; b.vy -= ny * k; }
      }
    }

    // Chute hors de la zone
    this.p.forEach(p => {
      if (p.alive && Math.hypot(p.x, p.y) > this.zoneR + R * 0.4) {
        p.alive = false; p.fell = true;
        this.fx.push({ type: 'fall', x: p.x, y: p.y });
      }
    });
  }

  checkEnd() {
    const [a, b] = this.p;
    let w;
    if (a.alive && b.alive) {
      if (this.t < MATCH_MAX) return;
      w = a.hp === b.hp ? null : a.hp > b.hp ? 0 : 1; // temps écoulé : hp
    } else {
      w = a.alive ? 0 : b.alive ? 1 : null;
    }
    this.ended = true; this.phase = 'ended'; this.banner = null;
    settle(this, w);
  }

  snapshot(i) {
    return {
      type: 'state', phase: this.phase, countdown: Math.ceil(this.countdown), zoneR: round(this.zoneR), me: i, t: round(this.t),
      p: this.p.map(p => ({ x: round(p.x), y: round(p.y), hp: p.hp, alive: p.alive, fell: p.fell })),
      obs: this.obs.map(o => ({ x: round(o.x), y: round(o.y), r: o.r })),
      tnt: this.tnt.map(b => ({ x: round(b.x), y: round(b.y), fuse: round(b.fuse) })),
      wind: this.wind ? { dx: this.wind.dx, dy: this.wind.dy } : null,
      gravity: this.gravity > 0,
      banner: this.banner ? this.banner.name : null,
      fx: this.fx,
    };
  }
}

// ---------- Boucle de simulation (30 Hz) ----------
setInterval(() => {
  for (const mt of matches.values()) {
    if (mt.ended) {
      if (mt.sockets.every(s => s.readyState !== 1)) matches.delete(mt.id);
      continue;
    }
    mt.step(TICK);
    if (mt.ended) continue;
    mt.sockets.forEach((s, i) => send(s, mt.snapshot(i)));
    mt.fx = [];
  }
}, TICK * 1000);

server.listen(PORT, () => console.log(`Orbit Duel prêt sur http://localhost:${PORT}`));
