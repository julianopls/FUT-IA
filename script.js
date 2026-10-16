'use strict';

/* ---------- Constantes do jogo ---------- */

const W = 960, H = 600;
const FX = 40, FY = 92, FW = 880, FH = 488;
const CX = FX + FW / 2, CY = FY + FH / 2;
const GOAL_H = 150, GOAL_D = 26;
const GY1 = CY - GOAL_H / 2, GY2 = CY + GOAL_H / 2;
const PR = 17, BR = 10;
const KICK_REACH = 12, KICK_POWER = 800, MAX_BALL = 900;
const PLAYER_SPEED = 230, MATCH_TIME = 90, GOAL_PAUSE = 2.2;

/* Traves: quatro "postes" redondos nas pontas dos gols. A bola rebate neles. */
const POST_R = 5;
const POST_BOUNCE = 0.8;
const POSTS = [
  { x: FX, y: GY1 },
  { x: FX, y: GY2 },
  { x: FX + FW, y: GY1 },
  { x: FX + FW, y: GY2 }
];

const LEVELS = {
  easy: { name: 'Fácil', speed: 150, react: 0.5, predict: 0, err: 0.5, power: 0.75, kickCd: 0.9, align: 0.1, smart: false },
  normal: { name: 'Normal', speed: 150, react: 0.40, predict: 0.1, err: 0.3, power: 0.9, kickCd: 0.7, align: 0.45, smart: true },
  hard: { name: 'Difícil', speed: 200, react: 0.25, predict: 0.80, err: 0.1, power: 1, kickCd: 0.55, align: 0.55, smart: true }
};

/* Nível dos parceiros de time controlados pelo computador */
const MATE_LEVEL = { name: 'Parceiro', speed: 170, react: 0.35, predict: 0.3, err: 0.25, power: 0.9, kickCd: 0.7, align: 0.45, smart: true };

const STYLE_ME = { shirt: '#ffc933', trim: '#1b4fa8', hair: '#5a3418', skin: '#f2c9a0' };
const STYLE_CPU = { shirt: '#d8352a', trim: '#f4f4ee', hair: '#1d1410', skin: '#c68a5a' };

/* ---------- Personagens (para escolher no menu) ---------- */

const CHARACTERS = [
  { id: 'craque', name: 'Craque', style: STYLE_ME },
  { id: 'rosinha', name: 'Rosinha', style: { shirt: '#ff5fa2', trim: '#ffffff', hair: '#5a3418', skin: '#f2c9a0' } },
  { id: 'ciano', name: 'Ciano', style: { shirt: '#19c7c7', trim: '#0d4f6b', hair: '#111111', skin: '#a86f46' } },
  { id: 'branquinho', name: 'Branquinho', style: { shirt: '#f4f4ee', trim: '#1b4fa8', hair: '#d8b04a', skin: '#f2c9a0' } },
  { id: 'lilas', name: 'Lilás', style: { shirt: '#b388ff', trim: '#3a1d7a', hair: '#1d1410', skin: '#7a4a2c' } }
];

const HAIRS = ['#2b1a10', '#5a3418', '#d8b04a', '#111111'];
const SKINS = ['#f2c9a0', '#d9a273', '#a86f46', '#7a4a2c'];

/* ---------- Formações por tamanho de time ---------- */
const FORMATIONS = {
  1: [[0.25, 0]],
  2: [[0.28, -0.1], [0.12, 0.1]],
  3: [[0.30, 0], [0.14, -0.2], [0.14, 0.2]],
  4: [[0.30, 0], [0.14, -0.24], [0.14, 0.24], [0.24, 0.32]],
  5: [[0.30, 0], [0.14, -0.26], [0.14, 0.26], [0.24, -0.34], [0.24, 0.34]]
};

/* ---------- Adversários do campeonato ---------- */
const OPPONENTS = [
  { name: 'SENAI FUT', level: 'easy', style: { shirt: '#4CAF50', trim: '#ffffff', hair: '#2b1a10', skin: '#d9a273' } },
  { name: 'Gotis FC', level: 'normal', style: { shirt: '#2196F3', trim: '#ffffff', hair: '#111111', skin: '#f2c9a0' } },
  { name: 'Green Vale', level: 'normal', style: { shirt: '#9C27B0', trim: '#ffc933', hair: '#5a3418', skin: '#a86f46' } },
  { name: 'Modelo Fc', level: 'hard', style: { shirt: '#FF5722', trim: '#000000', hair: '#d8b04a', skin: '#c68a5a' } },
  { name: 'Real Madruga', level: 'hard', style: { shirt: '#1a1a1a', trim: '#ffc933', hair: '#1d1410', skin: '#7a4a2c' } }
];

/* ---------- Elementos da página ---------- */

const $ = (id) => document.getElementById(id);
const canvas = $('game');
const ctx = canvas.getContext('2d');

/* ---------- Estado ---------- */

let state = 'menu';
let difficulty = 'normal';
let level = LEVELS.normal;
let teamSize = 1;
let charIndex = 0;
let timeLeft = MATCH_TIME;
let goalTimer = 0;
let goalBy = 'me';
const score = { me: 0, cpu: 0 };

/* Campeonato */
let isChampionship = false;
let champRound = 0;
let champResults = [];
let activeCpuStyle = STYLE_CPU;

/* Replay */
const REPLAY_RECORD_INTERVAL = 1 / 30;
const REPLAY_MAX_FRAMES = 100;
const REPLAY_SPEED = 0.28;

let replayBuffer = [];
let replayFrames = [];
let replayIndex = 0;
let replayAccum = 0;
let replayRecordAccum = 0;
let replayFinal = null;
let replayFlash = 0;

const ball = { x: CX, y: CY, vx: 0, vy: 0, rot: 0 };

let players = [];
let me = null;
const chasers = { me: null, cpu: null };

/* ========================================================== */
/* CONEXÃO SOCKET.IO (Render + Local)                         */
/* ========================================================== */

let opened = false;
let socket = null;

try {
    const serverUrl = window.location.hostname === 'localhost' || window.location.hostname === '127.0.0.1'
        ? 'http://localhost:3000'
        : 'https://fut-ia.onrender.com';

    console.log("A tentar ligar ao servidor:", serverUrl);

    socket = io(serverUrl, {
        transports: ['websocket', 'polling'],
        reconnectionAttempts: 10,
        timeout: 20000
    });
} catch (err) {
    console.error("Erro ao inicializar Socket.io:", err);
}

const net = {
  mode: 'off', 
  ws: socket, 
  code: '', 
  peers: new Map(),
  assign: [],
  myGid: 0,
  baseSize: 1,
  ready: false,
  rp: 0, lastSent: '', lastSentAt: 0,
  size: 5,
  members: [],
  known: new Set(),
  matchOn: false,
  name: '',
  spec: false
};

if (socket) {
    socket.send = function(data) {
        socket.emit('message', data);
    };

    socket.on('connect', () => {
        console.log("✅ Conexão estabelecida com sucesso! ID:", socket.id);
        opened = true;
        if (typeof onOpen === 'function') onOpen();
    });

    socket.on('connect_error', (error) => {
        console.warn("⚠️ Erro ou demora na conexão:", error.message);
    });

    socket.on('disconnect', (reason) => {
        console.log("❌ Desconectado do servidor. Motivo:", reason);
        net.ws = null;
    });

    socket.on('atualizar-sala', (sala) => {
        console.log("Atualização de sala recebida:", sala);
        if (typeof updateLobbyUI === 'function') {
            updateLobbyUI(sala);
        }
    });
}

let netStyleMe = null;

function newPlayer(team, human, idx) {
  return {
    team, human, idx, gid: null,
    x: 0, y: 0, vx: 0, vy: 0,
    fx: team === 'me' ? 1 : -1, fy: 0,
    walk: 0, kickCd: 0, kickAnim: 0,
    role: 'chase', solo: false,
    ai: { think: 0, contact: 0, aimY: CY, seenX: CX, seenY: CY }
  };
}

function buildTeams() {
  players = [];

  for (let i = 0; i < teamSize; i++) players.push(newPlayer('me', net.mode === 'off' && i === 0, i));
  for (let i = 0; i < teamSize; i++) players.push(newPlayer('cpu', false, i));

  if (net.mode !== 'off') {
    for (const a of net.assign) {
      const q = players.find((x) => x.team === a.team && x.idx === a.idx);

      if (!q) continue;
      if (net.mode === 'host' && a.gid !== 0 && !net.peers.has(a.gid)) continue;

      q.human = true;
      q.gid = a.gid;
    }
  }

  me = (net.mode === 'host' ? players.find((x) => x.gid === 0) : null) || players[0];
  chasers.me = null;
  chasers.cpu = null;
}

const myStyle = () => netStyleMe || CHARACTERS[charIndex].style;

function styleOf(p) {
  const base = p.team === 'me' ? myStyle() : activeCpuStyle;

  if (p.idx === 0) return base;

  const k = p.idx + (p.team === 'me' ? 0 : 2);

  return { ...base, hair: HAIRS[(k + 1) % HAIRS.length], skin: SKINS[(k + 2) % SKINS.length] };
}

const clamp = (v, a, b) => Math.max(a, Math.min(b, v));

/* ---------- Entrada ---------- */

const BINDINGS = {
  up: ['KeyW', 'ArrowUp'],
  down: ['KeyS', 'ArrowDown'],
  left: ['KeyA', 'ArrowLeft'],
  right: ['KeyD', 'ArrowRight'],
  kick: ['Space']
};

const GAME_KEYS = new Set(Object.values(BINDINGS).flat());
const keys = {};
const touch = {};

const pressed = (name) => BINDINGS[name].some((code) => keys[code]) || !!touch[name];

function clearInput() {
  for (const k in keys) keys[k] = false;
  for (const k in touch) touch[k] = false;
  document.querySelectorAll('.tbtn.down').forEach((b) => b.classList.remove('down'));
}

window.addEventListener('keydown', (e) => {
  if (e.target && e.target.tagName === 'INPUT') return;

  if (e.code === 'KeyM') {
    if (!e.repeat && typeof sfx !== 'undefined' && sfx.toggleMute) sfx.toggleMute();
    return;
  }

  if (e.code === 'Escape') {
    if (!e.repeat) togglePause();
    return;
  }

  if (GAME_KEYS.has(e.code)) {
    keys[e.code] = true;
    e.preventDefault();
  }
});

window.addEventListener('keyup', (e) => {
  if (e.target && e.target.tagName === 'INPUT') return;

  if (GAME_KEYS.has(e.code)) {
    keys[e.code] = false;
    e.preventDefault();
  }
});

window.addEventListener('blur', clearInput);

document.addEventListener('visibilitychange', () => {
  if (document.hidden && state === 'playing') togglePause();
});

document.querySelectorAll('[data-touch]').forEach((btn) => {
  const name = btn.dataset.touch;

  const on = (e) => {
    e.preventDefault();
    touch[name] = true;
    btn.classList.add('down');
  };

  const off = () => {
    touch[name] = false;
    btn.classList.remove('down');
  };

  btn.addEventListener('pointerdown', on);
  ['pointerup', 'pointercancel', 'pointerleave'].forEach((ev) => btn.addEventListener(ev, off));
  btn.addEventListener('contextmenu', (e) => e.preventDefault());
});

if (window.matchMedia('(pointer: coarse)').matches) {
  document.body.classList.add('touch');
}

window.addEventListener('touchstart', () => document.body.classList.add('touch'), { once: true, passive: true });

/* ---------- Telas e botões ---------- */

function showOverlay(id) {
  document.querySelectorAll('.overlay').forEach((o) => o.classList.toggle('hidden', o.id !== id));
}

function updateLevelLabel() {
  const size = teamSize + 'x' + teamSize;
  const el = $('levelLabel');
  if (!el) return;

  if (net.mode !== 'off') {
    el.textContent = 'Online · ' + size;
  } else if (isChampionship && champRound < OPPONENTS.length) {
    el.textContent = 'vs ' + OPPONENTS[champRound].name + ' · ' + size;
  } else {
    el.textContent = 'Dificuldade: ' + level.name + ' · ' + size;
  }
}

function setState(next) {
  const prev = state;
  state = next;

  if (typeof onStateSound === 'function') onStateSound(prev, next);

  const skipRep = $('btnSkipReplay');
  if (skipRep) skipRep.classList.toggle('hidden', next !== 'replay' || net.mode === 'guest');

  document.body.dataset.state = next;
  const btnP = $('btnPause');
  if (btnP) btnP.textContent = next === 'paused' ? 'Continuar' : 'Pausar';

  updateLevelLabel();

  if (next === 'menu') showOverlay('menu');
  else if (next === 'paused') showOverlay('pause');
  else if (next === 'ended') showOverlay('end');
  else if (next === 'championship') showOverlay('championship');
  else if (next === 'champEnd') showOverlay('champEnd');
  else showOverlay(null);
}

function resetPositions() {
  const form = FORMATIONS[teamSize];

  for (const p of players) {
    const [xf, yf] = form[p.idx];

    p.x = p.team === 'me' ? FX + FW * xf : FX + FW * (1 - xf);
    p.y = CY + yf * FH;
    p.fx = p.team === 'me' ? 1 : -1;
    p.fy = 0;
    p.vx = 0;
    p.vy = 0;
    p.kickCd = 0;
    p.kickAnim = 0;

    p.ai.think = 0;
    p.ai.contact = 0;
    p.ai.seenX = CX;
    p.ai.seenY = CY;
  }

  ball.x = CX;
  ball.y = CY;
  ball.vx = 0;
  ball.vy = 0;
}

function startMatch() {
  if (!isChampionship) {
    level = LEVELS[difficulty];
    if (net.mode !== 'host') activeCpuStyle = STYLE_CPU;
  }

  if (net.mode === 'host' && typeof hostPrepare === 'function') hostPrepare();

  buildTeams();

  score.me = 0;
  score.cpu = 0;
  timeLeft = MATCH_TIME;
  goalTimer = 0;
  replayBuffer = [];
  replayRecordAccum = 0;
  replayFlash = 0;

  if (typeof clearFx === 'function') clearFx();
  clearInput();
  resetPositions();
  setState('playing');
}

function toMenu() {
  if (typeof leaveOnline === 'function') leaveOnline();
  isChampionship = false;
  score.me = 0;
  score.cpu = 0;
  timeLeft = MATCH_TIME;

  clearInput();
  resetPositions();
  setState('menu');
}

function togglePause() {
  if (net.mode !== 'off') return;

  if (state === 'playing') {
    clearInput();
    setState('paused');
  } else if (state === 'paused') {
    setState('playing');
  }
}

/* ---------- Ciclo de Jogo (Loop principal) ---------- */

function stepPlay(dt) {
  timeLeft -= dt;

  if (timeLeft <= 0) {
    timeLeft = 0;
    endMatch();
    return;
  }

  for (const p of players) {
    p.kickCd = Math.max(0, p.kickCd - dt);
    p.kickAnim = Math.max(0, p.kickAnim - dt);
  }

  updateHumans(dt);
  assignRoles();

  for (const p of players) {
    if (!p.human) updateAI(p, dt);
  }

  collidePlayers();

  const steps = 3;
  for (let i = 0; i < steps; i++) {
    stepBall(dt / steps);
    for (const p of players) {
      collidePlayerBall(p);
    }
  }

  if (checkGoal()) return;

  recordReplay(dt);
}

function stepGoal(dt) {
  goalTimer -= dt;
  if (goalTimer <= 0) {
    resetPositions();
    setState('playing');
  }
}

let lastTime = performance.now();
function loop(now) {
  const dt = Math.min(0.1, (now - lastTime) / 1000);
  lastTime = now;

  if (state === 'playing') stepPlay(dt);
  else if (state === 'goal') stepGoal(dt);
  else if (state === 'replay' && typeof stepReplay === 'function') stepReplay(dt);

  render();
  requestAnimationFrame(loop);
}

function render() {
  ctx.clearRect(0, 0, W, H);
  
  // Desenho do Campo
  ctx.fillStyle = '#2e8b57';
  ctx.fillRect(FX, FY, FW, FH);

  // Placar básico na tela
  ctx.fillStyle = '#ffffff';
  ctx.font = '20px Arial';
  ctx.fillText(`Placar: ${score.me} x ${score.cpu}`, CX - 50, FY - 20);

  // Bola
  ctx.beginPath();
  ctx.arc(ball.x, ball.y, BR, 0, Math.PI * 2);
  ctx.fillStyle = '#ffffff';
  ctx.fill();
  ctx.lineWidth = 2;
  ctx.strokeStyle = '#000000';
  ctx.stroke();

  // Jogadores
  for (const p of players) {
    ctx.beginPath();
    ctx.arc(p.x, p.y, PR, 0, Math.PI * 2);
    const st = styleOf(p);
    ctx.fillStyle = st.shirt;
    ctx.fill();
    ctx.stroke();
  }
}

requestAnimationFrame(loop);