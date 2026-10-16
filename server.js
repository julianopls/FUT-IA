'use strict';

/*
  Servidor do Futebol de Rua.
  - Serve o jogo (index.html, style.css, script.js)
  - Salas com código de 4 números: 1 anfitrião, jogadores (Time 1 e Time 2, até 5 por time)
    e até 5 espectadores. O servidor confere nome, time e vagas.

  Como usar:  npm install   e depois   node server.js
*/

const http = require('http');
const fs = require('fs');
const path = require('path');
const os = require('os');
const { WebSocketServer } = require('ws');

const PORT = Number(process.env.PORT) || 3000;

const FILES = {
  '/index.html': 'text/html; charset=utf-8',
  '/style.css': 'text/css; charset=utf-8',
  '/script.js': 'text/javascript; charset=utf-8'
};

const server = http.createServer((req, res) => {
  let url = decodeURIComponent((req.url || '/').split('?')[0]);

  if (url === '/') url = '/index.html';

  const type = FILES[url];

  if (!type) {
    res.writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8' });
    res.end('Não encontrado');
    return;
  }

  fs.readFile(path.join(__dirname, url), (err, data) => {
    if (err) {
      res.writeHead(500, { 'Content-Type': 'text/plain; charset=utf-8' });
      res.end('Erro ao ler o arquivo');
      return;
    }

    res.writeHead(200, { 'Content-Type': type, 'Cache-Control': 'no-store' });
    res.end(data);
  });
});

/* ---------- Salas ---------- */
/* Sala: { host, hostName, hostTeam, size, guests: [], nextGid }
   Convidado (ws): gid, name, team (1|2), spec (true = espectador)
   - O anfitrião é o gid 0 e sempre joga.
   - Mensagens do anfitrião (init, s, lobby) vão para todos os convidados.
   - Controles (in) dos jogadores vão só para o anfitrião, com o número em "from".
   - A cada entrada/saída o servidor manda a lista da sala (room) para todos. */

const MAX_SPECS = 5;
const MAX_SIZE = 5;

const wss = new WebSocketServer({ server });
const rooms = new Map(); // código -> sala

function send(ws, obj) {
  if (ws && ws.readyState === 1) ws.send(JSON.stringify(obj));
}

function newCode() {
  let code;

  do {
    code = String(Math.floor(1000 + Math.random() * 9000));
  } while (rooms.has(code));

  return code;
}

function cleanName(v, fallback) {
  const s = String(v == null ? '' : v).replace(/[^\p{L}\p{N} _.\-]/gu, '').trim().slice(0, 12);

  return s || fallback;
}

function membersOf(room) {
  const list = [{ gid: 0, name: room.hostName, team: room.hostTeam, spec: false, host: true }];

  for (const g of room.guests) {
    list.push({ gid: g.gid, name: g.name, team: g.team, spec: g.spec, host: false });
  }

  return list;
}

function broadcastRoom(room) {
  const msg = { t: 'room', size: room.size, members: membersOf(room) };

  send(room.host, msg);

  for (const g of room.guests) send(g, msg);
}

function teamCount(room, team) {
  let n = room.hostTeam === team ? 1 : 0;

  for (const g of room.guests) {
    if (!g.spec && g.team === team) n++;
  }

  return n;
}

function specCount(room) {
  return room.guests.filter((g) => g.spec).length;
}

function leave(ws) {
  const room = rooms.get(ws.room);

  if (!room) return;

  if (ws.role === 'host') {
    for (const g of room.guests) {
      send(g, { t: 'left' });
      g.room = null;
      g.role = null;
    }

    rooms.delete(ws.room);
  } else {
    room.guests = room.guests.filter((g) => g !== ws);
    broadcastRoom(room);
  }

  ws.room = null;
  ws.role = null;
}

wss.on('connection', (ws) => {
  ws.room = null;
  ws.role = null;
  ws.gid = null;
  ws.name = '';
  ws.team = 1;
  ws.spec = false;

  ws.on('message', (raw) => {
    const text = raw.toString();

    if (text.length > 8192) return;

    let m;

    try { m = JSON.parse(text); } catch (err) { return; }

    if (!m || typeof m !== 'object') return;

    if (m.t === 'create') {
      leave(ws);

      const code = newCode();
      const size = Math.min(MAX_SIZE, Math.max(1, Math.floor(Number(m.size)) || MAX_SIZE));

      const room = {
        host: ws,
        hostName: cleanName(m.name, 'Anfitrião'),
        hostTeam: m.team === 2 ? 2 : 1,
        size,
        guests: [],
        nextGid: 1
      };

      rooms.set(code, room);
      ws.room = code;
      ws.role = 'host';

      send(ws, { t: 'created', code });
      broadcastRoom(room);
      console.log('Sala criada:', code, '(' + size + 'x' + size + ')');
      return;
    }

    if (m.t === 'join') {
      leave(ws);

      const code = String(m.code);
      const room = rooms.get(code);

      if (!room) return send(ws, { t: 'error', msg: 'Sala não encontrada. Confira o código.' });

      const spec = !!m.spec;
      const team = m.team === 2 ? 2 : 1;

      if (spec) {
        if (specCount(room) >= MAX_SPECS) {
          return send(ws, { t: 'error', msg: 'Essa sala já tem ' + MAX_SPECS + ' espectadores.' });
        }
      } else if (teamCount(room, team) >= room.size) {
        return send(ws, { t: 'error', msg: 'O Time ' + team + ' está cheio. Escolha o outro time ou entre como espectador.' });
      }

      ws.gid = room.nextGid++;
      ws.name = cleanName(m.name, 'Jogador ' + ws.gid);
      ws.team = team;
      ws.spec = spec;
      ws.room = code;
      ws.role = 'guest';
      room.guests.push(ws);

      send(ws, { t: 'joined', gid: ws.gid, size: room.size });
      broadcastRoom(room);
      console.log((spec ? 'Espectador ' : 'Jogador ') + ws.gid + ' (' + ws.name + ') entrou na sala:', code);
      return;
    }

    const room = rooms.get(ws.room);

    if (!room) return;

    if (ws.role === 'host') {
      /* só repassa o que o jogo usa */
      if (m.t !== 'init' && m.t !== 's' && m.t !== 'lobby') return;

      for (const g of room.guests) {
        if (g.readyState === 1) g.send(text);
      }
    } else {
      if (m.t !== 'in' || ws.spec) return;

      m.from = ws.gid;

      if (room.host.readyState === 1) room.host.send(JSON.stringify(m));
    }
  });

  ws.on('close', () => leave(ws));
  ws.on('error', () => leave(ws));
});

server.listen(PORT, '0.0.0.0', () => {
  console.log('\n⚽ Futebol de Rua rodando!\n');
  console.log('  Neste PC:        http://localhost:' + PORT);

  const nets = os.networkInterfaces();

  for (const name of Object.keys(nets)) {
    for (const n of nets[name] || []) {
      if (n.family === 'IPv4' && !n.internal) {
        console.log('  Outro PC (rede): http://' + n.address + ':' + PORT);
      }
    }
  }

  console.log('\nTodos abrem o mesmo endereço. Pare com Ctrl + C.\n');
});
