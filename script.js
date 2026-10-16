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
/* [distância do próprio gol (fração da largura), deslocamento vertical (fração da altura)] */
/* O primeiro jogador de cada time (índice 0) é o que você controla no seu time. */

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

/* Jogadores: lista com todos (dos dois times). `me` é o jogador controlado por você. */

let players = [];
let me = null;
const chasers = { me: null, cpu: null };

/* Online: 'off' (offline), 'host' (anfitrião, roda a partida) ou 'guest' (convidado, só recebe e desenha) */
const net = {
  mode: 'off', ws: null, code: '',
  peers: new Map(),   /* anfitrião: gid do amigo -> { char, input } */
  assign: [],         /* quem controla qual vaga: { team, idx, gid } (gid 0 = anfitrião) */
  myGid: 0,           /* convidado: meu número na sala */
  baseSize: 1,        /* tamanho de time escolhido no menu */
  ready: false,       /* convidado: já recebeu a configuração da partida */
  rp: 0, lastSent: '', lastSentAt: 0,
  size: 5,            /* tamanho de time da sala (1 a 5) */
  members: [],        /* quem está na sala: { gid, name, team (1|2), spec, host } */
  known: new Set(),   /* anfitrião: membros já vistos */
  matchOn: false,     /* anfitrião: partida em andamento */
  name: '',           /* meu nome */
  spec: false         /* sou espectador */
};

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

  /* Online: marca quais vagas são de pessoas (o resto fica com o computador) */
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
    if (!e.repeat) sfx.toggleMute();
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

  if (net.mode !== 'off') {
    $('levelLabel').textContent = 'Online · ' + size;
  } else if (isChampionship && champRound < OPPONENTS.length) {
    $('levelLabel').textContent = 'vs ' + OPPONENTS[champRound].name + ' · ' + size;
  } else {
    $('levelLabel').textContent = 'Dificuldade: ' + level.name + ' · ' + size;
  }
}

function setState(next) {
  const prev = state;
  state = next;

  onStateSound(prev, next);

  $('btnSkipReplay').classList.toggle('hidden', next !== 'replay' || net.mode === 'guest');

  document.body.dataset.state = next;
  $('btnPause').textContent = next === 'paused' ? 'Continuar' : 'Pausar';

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

  if (net.mode === 'host') hostPrepare();

  buildTeams();

  score.me = 0;
  score.cpu = 0;
  timeLeft = MATCH_TIME;
  goalTimer = 0;
  replayBuffer = [];
  replayRecordAccum = 0;
  replayFlash = 0;

  clearFx();
  clearInput();
  resetPositions();
  setState('playing');
}

function toMenu() {
  leaveOnline();
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

/* ---------- Campeonato ---------- */

function startChampionship() {
  isChampionship = true;
  champRound = 0;
  champResults = [];
  showChampBracket();
}

function showChampBracket() {
  buildBracketHTML();

  if (champRound >= OPPONENTS.length) {
    showChampVictory();
    return;
  }

  $('btnChampStart').textContent = champRound === 0 ? 'COMEÇAR' : 'PRÓXIMA PARTIDA';
  setState('championship');
}

function buildBracketHTML() {
  let html = '';

  OPPONENTS.forEach((opp, i) => {
    let cls = '', icon = '⬜', scoreText = '';

    if (i < champRound && champResults[i]) {
      const r = champResults[i];
      cls = r.won ? 'won' : 'lost';
      icon = r.won ? '✅' : '❌';
      scoreText = r.myScore + ' x ' + r.cpuScore;
    } else if (i === champRound) {
      cls = 'current';
      icon = '▶️';
    }

    const diffName = LEVELS[opp.level].name;

    html += '<div class="bracket-round ' + cls + '">' +
      '<span class="r-icon">' + icon + '</span>' +
      '<span class="r-color" style="background:' + opp.style.shirt + '"></span>' +
      '<span class="r-name">' + opp.name + '</span>' +
      '<span class="r-score">' + scoreText + '</span>' +
      '<span class="r-diff">' + diffName + '</span>' +
      '</div>';
  });

  $('champBracket').innerHTML = html;
}

function startChampMatch() {
  const opp = OPPONENTS[champRound];
  level = LEVELS[opp.level];
  activeCpuStyle = opp.style;
  startMatch();
}

function showChampVictory() {
  let totalMe = 0, totalCpu = 0;

  champResults.forEach((r) => {
    totalMe += r.myScore;
    totalCpu += r.cpuScore;
  });

  $('champFinalStats').textContent = 'Placar total: Você ' + totalMe + ' x ' + totalCpu + ' Adversários';
  setState('champEnd');
}

/* ---------- Fim de partida ---------- */

function endMatch() {
  clearInput();

  let result = 'EMPATE!';
  const mine = score[myTeam()], theirs = score[myTeam() === 'me' ? 'cpu' : 'me'];

  if (mine > theirs) result = net.mode === 'host' ? 'SEU TIME VENCEU!' : 'VOCÊ VENCEU!';
  else if (mine < theirs) result = net.mode === 'host' ? 'O OUTRO TIME VENCEU' : 'O ADVERSÁRIO VENCEU';

  $('endResult').textContent = result;

  if (isChampionship) {
    const opp = OPPONENTS[champRound];
    const won = score.me > score.cpu;

    champResults[champRound] = {
      won,
      myScore: score.me,
      cpuScore: score.cpu
    };

    $('endTitle').textContent = won ? 'VITÓRIA!' : (score.me === score.cpu ? 'EMPATE!' : 'DERROTA!');
    $('endScore').textContent = 'Você ' + score.me + ' x ' + score.cpu + ' ' + opp.name;

    if (won) {
      $('endChampInfo').textContent = champRound < OPPONENTS.length - 1
        ? 'Avançando para a próxima fase...'
        : 'Você é o grande campeão!';

      $('btnChampAdvance').classList.remove('hidden');
      $('btnChampAdvance').textContent = champRound < OPPONENTS.length - 1 ? 'PRÓXIMA PARTIDA' : 'VER RESULTADO';
      $('btnChampRetry').classList.add('hidden');
    } else {
      $('endChampInfo').textContent = score.me === score.cpu
        ? 'Empate não basta! Você precisa vencer para avançar.'
        : 'Você foi eliminado. Tente novamente!';

      $('btnChampAdvance').classList.add('hidden');
      $('btnChampRetry').classList.remove('hidden');
    }

    $('endChampInfo').classList.remove('hidden');
    $('endNormalActions').classList.add('hidden');
    $('endChampActions').classList.remove('hidden');
  } else {
    $('endTitle').textContent = 'FIM DE JOGO';
    $('endScore').textContent = net.mode === 'host'
      ? 'Seu time ' + mine + ' x ' + theirs + ' Outro time'
      : 'Você ' + score.me + ' x ' + score.cpu + ' Adversário';
    $('btnAgain').classList.remove('hidden');

    $('endChampInfo').classList.add('hidden');
    $('endNormalActions').classList.remove('hidden');
    $('endChampActions').classList.add('hidden');
  }

  setState('ended');
}

/* ---------- Menu: personagem ---------- */

function buildCharPicker() {
  const box = $('charPicker');
  box.innerHTML = '';

  CHARACTERS.forEach((c, i) => {
    const b = document.createElement('button');

    b.type = 'button';
    b.className = 'char-btn' + (i === charIndex ? ' active' : '');
    b.title = c.name;
    b.setAttribute('aria-label', 'Personagem ' + c.name);

    b.innerHTML =
      '<span class="char-dot" style="--shirt:' + c.style.shirt + ';--trim:' + c.style.trim +
      ';--hair:' + c.style.hair + ';--skin:' + c.style.skin + '"></span>' +
      '<span class="char-name">' + c.name + '</span>';

    b.addEventListener('click', () => {
      charIndex = i;
      box.querySelectorAll('.char-btn').forEach((x, j) => x.classList.toggle('active', j === i));
    });

    box.appendChild(b);
  });
}

/* ---------- Botões ---------- */

document.querySelectorAll('.seg-btn[data-level]').forEach((btn) => {
  btn.addEventListener('click', () => {
    difficulty = btn.dataset.level;
    level = LEVELS[difficulty];

    document.querySelectorAll('.seg-btn[data-level]').forEach((b) => {
      b.classList.toggle('active', b === btn);
    });

    updateLevelLabel();
  });
});

document.querySelectorAll('.seg-btn[data-size]').forEach((btn) => {
  btn.addEventListener('click', () => {
    teamSize = Number(btn.dataset.size);

    document.querySelectorAll('.seg-btn[data-size]').forEach((b) => {
      b.classList.toggle('active', b === btn);
    });

    buildTeams();
    resetPositions();
    updateLevelLabel();
  });
});

$('btnPlay').addEventListener('click', () => {
  isChampionship = false;
  startMatch();
});

$('btnHow').addEventListener('click', () => showOverlay('howto'));
$('btnBack').addEventListener('click', () => showOverlay('menu'));
$('btnPause').addEventListener('click', togglePause);
$('btnRestart').addEventListener('click', startMatch);
$('btnMenu').addEventListener('click', toMenu);
$('btnResume').addEventListener('click', togglePause);
$('btnPauseRestart').addEventListener('click', startMatch);
$('btnPauseMenu').addEventListener('click', toMenu);
$('btnAgain').addEventListener('click', startMatch);
$('btnEndMenu').addEventListener('click', toMenu);

/* Botão para pular o replay */

$('btnSkipReplay').addEventListener('click', () => {
  if (state === 'replay') {
    restoreFinal();
    replayFlash = 0;
    goalTimer = GOAL_PAUSE;
    setState('goal');
  }
});

/* Campeonato */

$('btnChamp').addEventListener('click', startChampionship);
$('btnChampStart').addEventListener('click', startChampMatch);
$('btnChampMenuBack').addEventListener('click', toMenu);

$('btnChampAdvance').addEventListener('click', () => {
  champRound++;

  if (champRound >= OPPONENTS.length) showChampVictory();
  else showChampBracket();
});

$('btnChampRetry').addEventListener('click', startChampMatch);
$('btnChampEndBack').addEventListener('click', toMenu);
$('btnChampNewRun').addEventListener('click', startChampionship);
$('btnChampEndMenuBack').addEventListener('click', toMenu);

document.addEventListener('click', (e) => {
  const btn = e.target.closest('button');

  if (btn) {
    if (!btn.classList.contains('tbtn')) sfx.click();
    btn.blur();
  }
});

/* ---------- Jogadores ---------- */

function clampPlayer(p) {
  const minX = FX + PR, maxX = FX + FW - PR;
  const minY = FY + PR, maxY = FY + FH - PR;

  if (p.x < minX) {
    p.x = minX;
    p.vx = 0;
  }

  if (p.x > maxX) {
    p.x = maxX;
    p.vx = 0;
  }

  if (p.y < minY) {
    p.y = minY;
    p.vy = 0;
  }

  if (p.y > maxY) {
    p.y = maxY;
    p.vy = 0;
  }
}

function movePlayer(p, dirX, dirY, speed, dt) {
  const len = Math.hypot(dirX, dirY);
  const tx = len > 0 ? (dirX / len) * speed : 0;
  const ty = len > 0 ? (dirY / len) * speed : 0;
  const k = 1 - Math.pow(0.00001, dt);

  p.vx += (tx - p.vx) * k;
  p.vy += (ty - p.vy) * k;
  p.x += p.vx * dt;
  p.y += p.vy * dt;

  if (len > 0) {
    p.fx = dirX / len;
    p.fy = dirY / len;
  }

  p.walk += Math.hypot(p.vx, p.vy) * dt * 0.09;
  clampPlayer(p);
}

function collidePlayers() {
  const min = PR * 2;

  for (let i = 0; i < players.length; i++) {
    for (let j = i + 1; j < players.length; j++) {
      const a = players[i], b = players[j];
      let dx = b.x - a.x, dy = b.y - a.y;
      let d = Math.hypot(dx, dy);

      if (d >= min) continue;

      if (d < 0.01) {
        dx = 1;
        dy = 0;
        d = 1;
      }

      const nx = dx / d, ny = dy / d, push = (min - d) / 2;

      a.x -= nx * push;
      a.y -= ny * push;
      b.x += nx * push;
      b.y += ny * push;

      clampPlayer(a);
      clampPlayer(b);
    }
  }
}

function launch(p, dx, dy, power) {
  const len = Math.hypot(dx, dy) || 1;

  p.fx = dx / len;
  p.fy = dy / len;

  ball.vx = p.fx * power + p.vx * 0.3;
  ball.vy = p.fy * power + p.vy * 0.3;

  emitFx('kick', ball.x, ball.y, clamp(power / KICK_POWER, 0.3, 1));
}

function humanKick(p) {
  p.kickCd = 0.3;
  p.kickAnim = 0.18;

  const dx = ball.x - p.x, dy = ball.y - p.y;
  const d = Math.hypot(dx, dy);

  if (d > PR + BR + KICK_REACH || d === 0) return;

  const nx = dx / d, ny = dy / d;
  let dirX = p.fx, dirY = p.fy;

  if (dirX * nx + dirY * ny < 0.2) {
    dirX = nx;
    dirY = ny;
  }

  launch(p, dirX, dirY, KICK_POWER);
}

function localInput() {
  return {
    dx: (pressed('right') ? 1 : 0) - (pressed('left') ? 1 : 0),
    dy: (pressed('down') ? 1 : 0) - (pressed('up') ? 1 : 0),
    kick: pressed('kick')
  };
}

function updateHumans(dt) {
  for (const p of players) {
    if (!p.human) continue;

    const inp = p === me ? localInput() : ((net.peers.get(p.gid) || {}).input || ZERO_INPUT);

    movePlayer(p, inp.dx, inp.dy, PLAYER_SPEED, dt);

    if (inp.kick && p.kickCd <= 0) humanKick(p);
  }
}

/* ---------- Inteligência artificial ---------- */

const attackX = (team) => (team === 'me' ? FX + FW : FX);
const ownX = (team) => (team === 'me' ? FX : FX + FW);
const levelFor = (p) => (p.team === 'cpu' ? level : MATE_LEVEL);

/* Define quem persegue a bola e quem fica em posição em cada time (só jogadores do computador). */

function assignRoles() {
  for (const team of ['me', 'cpu']) {
    const mates = players.filter((p) => p.team === team && !p.human);

    if (!mates.length) continue;

    const humans = players.filter((p) => p.team === team && p.human);

    let chaser = null, best = Infinity;

    for (const p of mates) {
      const d = Math.hypot(ball.x - p.x, ball.y - p.y);

      if (d < best) {
        best = d;
        chaser = p;
      }
    }

    /* Evita ficar trocando de perseguidor a cada quadro */
    const prev = chasers[team];

    if (prev && mates.includes(prev) && Math.hypot(ball.x - prev.x, ball.y - prev.y) < best + 30) {
      chaser = prev;
    }

    /* Se o humano do time está bem mais perto da bola, os parceiros só apoiam */
    if (humans.some((h) => Math.hypot(ball.x - h.x, ball.y - h.y) < best - 10)) {
      chaser = null;
    }

    chasers[team] = chaser;

    const solo = team === 'cpu' && humans.length === 0 && mates.length === 1;
    let slot = 0;

    for (const p of mates) {
      p.solo = solo;
      p.role = p === chaser ? 'chase' : slot++;
    }
  }
}

function chaseTarget(p, lv) {
  const s = p.ai;
  const sx = s.seenX, sy = s.seenY;

  if (!lv.smart) return { x: sx, y: sy };

  const ballDist = Math.hypot(ball.x - p.x, ball.y - p.y);

  /* Sozinho no time do computador: volta pro gol quando a bola vem na direção dele */
  if (p.solo && ball.vx > 40 && sx > FX + FW * 0.5 && ballDist > 150) {
    return {
      x: FX + FW - 55,
      y: clamp(sy, CY - 70, CY + 70)
    };
  }

  let ax = attackX(p.team) - sx, ay = CY - sy;
  const al = Math.hypot(ax, ay) || 1;

  ax /= al;
  ay /= al;

  const off = PR + BR;
  const rx = p.x - sx, ry = p.y - sy;
  const inFront = rx * ax + ry * ay > -10;

  if (inFront && Math.hypot(rx, ry) < 170) {
    const px = -ay, py = ax;
    const side = rx * px + ry * py >= 0 ? 1 : -1;

    return {
      x: sx - ax * off * 1.8 + px * side * off * 1.6,
      y: sy - ay * off * 1.8 + py * side * off * 1.6
    };
  }

  return {
    x: sx - ax * off * 0.3,
    y: sy - ay * off * 0.3
  };
}

/* Posições de quem não está perseguindo a bola */

function supportTarget(p) {
  const dir = p.team === 'me' ? 1 : -1;
  const own = ownX(p.team);
  const bx = ball.x, by = ball.y;
  const minX = FX + PR, maxX = FX + FW - PR;
  const minY = FY + PR, maxY = FY + FH - PR;

  if (p.role === 0) {
    /* zagueiro: fica entre a bola e o próprio gol */
    const dist = clamp(Math.abs(bx - own) * 0.3, 90, FW * 0.28);

    return {
      x: own + dir * dist,
      y: clamp(CY + (by - CY) * 0.5, minY, maxY)
    };
  }

  if (p.role === 1) {
    /* atacante de apoio: se oferece à frente da bola, do lado oposto */
    return {
      x: clamp(bx + dir * 130, minX, maxX),
      y: clamp(CY + (CY - by) * 0.6, minY, maxY)
    };
  }

  /* meio-campo: acompanha a bola por trás */
  if (p.role === 2) {
    return {
      x: clamp(bx - dir * 110, minX, maxX),
      y: clamp(by + (by < CY ? 80 : -80), minY, maxY)
    };
  }

  /* quinto jogador: abre pelo lado oposto */
  return {
    x: clamp(bx - dir * 40, minX, maxX),
    y: clamp(CY - (by - CY) * 0.9, minY, maxY)
  };
}

function updateAI(p, dt) {
  const lv = levelFor(p);
  const a = p.ai;

  a.think -= dt;

  if (a.think <= 0) {
    a.think = lv.react;

    a.seenX = clamp(ball.x + ball.vx * lv.predict, FX, FX + FW);
    a.seenY = clamp(ball.y + ball.vy * lv.predict, FY, FY + FH);

    a.aimY = CY + (Math.random() * 2 - 1) * GOAL_H * 0.35;

    if (lv.smart) {
      const gx = attackX(p.team);
      let near = null, nd = Infinity;

      for (const o of players) {
        if (o.team === p.team) continue;

        const d = Math.abs(o.x - gx);

        if (d < nd) {
          nd = d;
          near = o;
        }
      }

      if (near && nd < 220) {
        a.aimY = CY + (near.y > CY ? -1 : 1) * GOAL_H * 0.3;
      }
    }
  }

  const t = p.role === 'chase' ? chaseTarget(p, lv) : supportTarget(p);
  const dx = t.x - p.x, dy = t.y - p.y;
  const d = Math.hypot(dx, dy);
  const speed = lv.speed * Math.min(1, d / 25);

  movePlayer(p, d > 3 ? dx : 0, d > 3 ? dy : 0, speed, dt);

  const bx = ball.x - p.x, by = ball.y - p.y;
  const bd = Math.hypot(bx, by);
  const reach = PR + BR + KICK_REACH;

  a.contact = bd <= reach ? a.contact + dt : 0;

  if (bd <= reach && p.kickCd <= 0) {
    const inOwnThird = p.team === 'cpu' ? ball.x > FX + FW * 0.72 : ball.x < FX + FW * 0.28;

    const aim = inOwnThird
      ? { x: CX, y: ball.y < CY ? FY + 40 : FY + FH - 40 }
      : { x: attackX(p.team), y: a.aimY };

    let ax = aim.x - p.x, ay = aim.y - p.y;
    const al = Math.hypot(ax, ay) || 1;

    ax /= al;
    ay /= al;

    const aligned = (bx * ax + by * ay) / bd > lv.align;

    if (aligned || a.contact > 0.5) {
      const angle = Math.atan2(ay, ax) + (Math.random() * 2 - 1) * lv.err;

      launch(p, Math.cos(angle), Math.sin(angle), KICK_POWER * lv.power);

      p.kickCd = lv.kickCd;
      p.kickAnim = 0.18;
      a.contact = 0;
    }
  }
}

/* ---------- Bola ---------- */

function bounceBall() {
  const e = 0.8;

  if (ball.y < FY + BR) {
    wallHit(ball.vy);
    ball.y = FY + BR;
    ball.vy = Math.abs(ball.vy) * e;
  } else if (ball.y > FY + FH - BR) {
    wallHit(ball.vy);
    ball.y = FY + FH - BR;
    ball.vy = -Math.abs(ball.vy) * e;
  }

  const inGoalMouth = ball.y > GY1 && ball.y < GY2;

  if (!inGoalMouth) {
    if (ball.x < FX + BR) {
      wallHit(ball.vx);
      ball.x = FX + BR;
      ball.vx = Math.abs(ball.vx) * e;
    } else if (ball.x > FX + FW - BR) {
      wallHit(ball.vx);
      ball.x = FX + FW - BR;
      ball.vx = -Math.abs(ball.vx) * e;
    }
  }
}

/* A bola rebate nas traves (os 4 postes dos gols) */

function collideBallPosts() {
  const min = BR + POST_R;

  for (const post of POSTS) {
    const dx = ball.x - post.x, dy = ball.y - post.y;
    const d = Math.hypot(dx, dy);

    if (d >= min) continue;

    let nx, ny;

    if (d > 0.001) {
      nx = dx / d;
      ny = dy / d;
    } else {
      nx = post.x === FX ? 1 : -1;
      ny = 0;
    }

    ball.x = post.x + nx * min;
    ball.y = post.y + ny * min;

    const vn = ball.vx * nx + ball.vy * ny;

    if (vn < 0) {
      if (-vn > 60) emitFx('post', post.x, post.y, clamp(-vn / 500, 0.3, 1));

      ball.vx -= (1 + POST_BOUNCE) * vn * nx;
      ball.vy -= (1 + POST_BOUNCE) * vn * ny;
    }
  }
}

function stepBall(s) {
  ball.x += ball.vx * s;
  ball.y += ball.vy * s;

  const friction = Math.pow(0.3, s);
  ball.vx *= friction;
  ball.vy *= friction;

  const speed = Math.hypot(ball.vx, ball.vy);

  if (speed > MAX_BALL) {
    ball.vx *= MAX_BALL / speed;
    ball.vy *= MAX_BALL / speed;
  } else if (speed < 12) {
    ball.vx = 0;
    ball.vy = 0;
  }

  ball.rot += (speed * s / BR) * (ball.vx >= 0 ? 1 : -1);

  collideBallPosts();
  bounceBall();
}

function collidePlayerBall(p) {
  const min = PR + BR;
  let d = Math.hypot(ball.x - p.x, ball.y - p.y);

  if (d >= min) return;

  let nx = p.fx, ny = p.fy;

  if (d > 0.001) {
    nx = (ball.x - p.x) / d;
    ny = (ball.y - p.y) / d;
  }

  ball.x = p.x + nx * min;
  ball.y = p.y + ny * min;

  const rel = (ball.vx - p.vx) * nx + (ball.vy - p.vy) * ny;

  if (rel < 0) {
    if (rel < -140) emitFx('touch', ball.x, ball.y, clamp(-rel / 500, 0.2, 0.8));

    ball.vx -= 1.2 * rel * nx;
    ball.vy -= 1.2 * rel * ny;
  }

  collideBallPosts();
  bounceBall();

  d = Math.hypot(ball.x - p.x, ball.y - p.y);

  if (d < min - 0.5) {
    const over = min - d;

    p.x -= nx * over;
    p.y -= ny * over;

    clampPlayer(p);

    d = Math.hypot(ball.x - p.x, ball.y - p.y);

    if (d < min - 0.5) {
      let tx = -ny, ty = nx;

      if ((CX - ball.x) * tx + (CY - ball.y) * ty < 0) {
        tx = -tx;
        ty = -ty;
      }

      ball.x += tx * (min - d);
      ball.y += ty * (min - d);

      bounceBall();
    }
  }
}

function checkGoal() {
  if (ball.y <= GY1 || ball.y >= GY2) return false;

  if (ball.x < FX) {
    scoreGoal('cpu');
    return true;
  }

  if (ball.x > FX + FW) {
    scoreGoal('me');
    return true;
  }

  return false;
}

function scoreGoal(who) {
  emitFx('net', ball.x, ball.y, 1);

  score[who]++;
  goalBy = who;

  replayFinal = {
    bx: ball.x, by: ball.y, bvx: ball.vx, bvy: ball.vy, brot: ball.rot,
    ps: players.map((p) => [p.x, p.y, p.vx, p.vy, p.fx, p.fy, p.walk, p.kickAnim])
  };

  replayFrames = replayBuffer.slice();
  replayIndex = 0;
  replayAccum = 0;

  clearInput();

  if (replayFrames.length > 10) {
    setState('replay');
  } else {
    goalTimer = GOAL_PAUSE;
    setState('goal');
  }
}

/* ---------- Replay: gravação ---------- */

function captureFrame() {
  return {
    bx: ball.x, by: ball.y, brot: ball.rot,
    ps: players.map((p) => [p.x, p.y, p.fx, p.fy, p.walk, p.kickAnim])
  };
}

function applyFrame(f) {
  ball.x = f.bx;
  ball.y = f.by;
  ball.rot = f.brot;

  f.ps.forEach((s, i) => {
    const p = players[i];

    if (!p) return;

    p.x = s[0];
    p.y = s[1];
    p.fx = s[2];
    p.fy = s[3];
    p.walk = s[4];
    p.kickAnim = s[5];
  });
}

function restoreFinal() {
  const f = replayFinal;

  ball.x = f.bx;
  ball.y = f.by;
  ball.vx = f.bvx;
  ball.vy = f.bvy;
  ball.rot = f.brot;

  f.ps.forEach((s, i) => {
    const p = players[i];

    if (!p) return;

    p.x = s[0];
    p.y = s[1];
    p.vx = s[2];
    p.vy = s[3];
    p.fx = s[4];
    p.fy = s[5];
    p.walk = s[6];
    p.kickAnim = s[7];
  });
}

function recordReplay(dt) {
  replayRecordAccum += dt;

  if (replayRecordAccum >= REPLAY_RECORD_INTERVAL) {
    replayRecordAccum -= REPLAY_RECORD_INTERVAL;
    replayBuffer.push(captureFrame());

    if (replayBuffer.length > REPLAY_MAX_FRAMES) replayBuffer.shift();
  }
}

/* ---------- Replay: reprodução ---------- */

function stepReplay(dt) {
  const frameDt = REPLAY_RECORD_INTERVAL;

  replayAccum += dt * REPLAY_SPEED;

  while (replayAccum >= frameDt && replayIndex < replayFrames.length - 1) {
    replayIndex++;
    replayAccum -= frameDt;
  }

  applyFrame(replayFrames[Math.min(replayIndex, replayFrames.length - 1)]);

  if (replayIndex >= replayFrames.length - 1) {
    restoreFinal();
    replayFlash = 1.0;
    goalTimer = GOAL_PAUSE;
    setState('goal');
  }
}

/* ---------- Atualização por quadro ---------- */

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

    for (const p of players) collidePlayerBall(p);

    if (checkGoal()) return;
  }

  recordReplay(dt);
}

function stepGoal(dt) {
  goalTimer -= dt;

  for (const p of players) {
    movePlayer(p, 0, 0, 0, dt);
    p.kickAnim = Math.max(0, p.kickAnim - dt);
  }

  ball.x += ball.vx * dt;
  ball.y += ball.vy * dt;

  const f = Math.pow(0.05, dt);

  ball.vx *= f;
  ball.vy *= f;

  ball.y = clamp(ball.y, GY1 + BR, GY2 - BR);

  if (goalBy === 'cpu') {
    if (ball.x < FX - GOAL_D + BR) {
      ball.x = FX - GOAL_D + BR;
      ball.vx = Math.abs(ball.vx) * 0.3;
    }

    if (ball.x > FX) {
      ball.x = FX;
      ball.vx = 0;
    }
  } else {
    if (ball.x > FX + FW + GOAL_D - BR) {
      ball.x = FX + FW + GOAL_D - BR;
      ball.vx = -Math.abs(ball.vx) * 0.3;
    }

    if (ball.x < FX + FW) {
      ball.x = FX + FW;
      ball.vx = 0;
    }
  }

  if (goalTimer <= 0) {
    resetPositions();
    setState('playing');
  }
}

function update(dt) {
  updateFx(dt);

  /* O convidado não simula: só desenha o que o anfitrião manda */
  if (net.mode === 'guest') return;

  if (state === 'playing') stepPlay(dt);
  else if (state === 'goal') stepGoal(dt);
  else if (state === 'replay') stepReplay(dt);

  if (replayFlash > 0) {
    replayFlash = Math.max(0, replayFlash - dt * 3);
  }
}

/* ---------- Desenho do campo ---------- */

function drawGoalShape(g, side) {
  const x0 = side === 0 ? FX - GOAL_D : FX + FW;
  const edge = side === 0 ? FX : FX + FW;
  const back = side === 0 ? x0 : x0 + GOAL_D;

  g.fillStyle = 'rgba(10, 25, 15, 0.35)';
  g.fillRect(x0, GY1, GOAL_D, GOAL_H);

  g.strokeStyle = 'rgba(255, 255, 255, 0.45)';
  g.lineWidth = 1;

  for (let x = x0; x <= x0 + GOAL_D; x += 6) {
    g.beginPath();
    g.moveTo(x, GY1);
    g.lineTo(x, GY2);
    g.stroke();
  }

  for (let y = GY1; y <= GY2; y += 6) {
    g.beginPath();
    g.moveTo(x0, y);
    g.lineTo(x0 + GOAL_D, y);
    g.stroke();
  }

  g.strokeStyle = '#ffffff';
  g.lineWidth = 4;

  g.beginPath();
  g.moveTo(edge, GY1);
  g.lineTo(back, GY1);
  g.lineTo(back, GY2);
  g.lineTo(edge, GY2);
  g.stroke();
}

function buildBackground() {
  const c = document.createElement('canvas');
  c.width = W;
  c.height = H;

  const g = c.getContext('2d');
  let seed = 11;

  const rand = () => {
    seed = (seed * 16807) % 2147483647;
    return seed / 2147483647;
  };

  g.fillStyle = '#25702f';
  g.fillRect(0, 0, W, H);

  const stripe = FW / 10;

  for (let i = 0; i < 10; i++) {
    g.fillStyle = i % 2 ? '#2f8a3c' : '#359646';
    g.fillRect(FX + i * stripe, FY, stripe, FH);
  }

  for (let i = 0; i < 1400; i++) {
    const x = rand() * W, y = 96 + rand() * (H - 96);

    g.strokeStyle = i % 2 ? 'rgba(255,255,255,0.07)' : 'rgba(0,0,0,0.10)';
    g.beginPath();
    g.moveTo(x, y);
    g.lineTo(x + 2, y - 5);
    g.stroke();
  }

  g.fillStyle = '#2a2230';
  g.fillRect(0, 0, W, 80);

  const shirts = ['#e8542b', '#2b9a4a', '#f2c230', '#3b6fd1', '#c94fa0', '#f4f4ee'];
  const skins = ['#f2c9a0', '#d9a273', '#a86f46', '#7a4a2c'];
  const hairs = ['#2b1a10', '#5a3418', '#d8b04a', '#111111'];

  for (let row = 0; row < 6; row++) {
    for (let x = (row % 2) * 7; x < W; x += 14) {
      const y = 8 + row * 11;

      g.fillStyle = shirts[Math.floor(rand() * shirts.length)];
      g.beginPath();
      g.ellipse(x + 7, y + 10, 7, 5, 0, 0, Math.PI * 2);
      g.fill();

      g.fillStyle = skins[Math.floor(rand() * skins.length)];
      g.beginPath();
      g.arc(x + 7, y + 4, 4.5, 0, Math.PI * 2);
      g.fill();

      g.fillStyle = hairs[Math.floor(rand() * hairs.length)];
      g.beginPath();
      g.arc(x + 7, y + 3, 4.7, Math.PI, 0);
      g.fill();
    }
  }

  g.fillStyle = '#8a8f94';
  g.fillRect(0, 78, W, 14);

  g.fillStyle = '#b4b9bd';
  g.fillRect(0, 78, W, 3);

  g.strokeStyle = '#f4f4ee';
  g.fillStyle = '#f4f4ee';
  g.lineWidth = 3;
  g.lineJoin = 'round';

  g.strokeRect(FX, FY, FW, FH);

  g.beginPath();
  g.moveTo(CX, FY);
  g.lineTo(CX, FY + FH);
  g.stroke();

  g.beginPath();
  g.arc(CX, CY, 70, 0, Math.PI * 2);
  g.stroke();

  g.beginPath();
  g.arc(CX, CY, 4, 0, Math.PI * 2);
  g.fill();

  for (const right of [false, true]) {
    const bigX = right ? FX + FW - 150 : FX;
    const smallX = right ? FX + FW - 55 : FX;
    const spotX = right ? FX + FW - 105 : FX + 105;

    g.strokeRect(bigX, CY - 140, 150, 280);
    g.strokeRect(smallX, CY - 95, 55, 190);

    g.beginPath();
    g.arc(spotX, CY, 3, 0, Math.PI * 2);
    g.fill();
  }

  g.beginPath();
  g.arc(FX, FY, 14, 0, Math.PI / 2);
  g.stroke();

  g.beginPath();
  g.arc(FX + FW, FY, 14, Math.PI / 2, Math.PI);
  g.stroke();

  g.beginPath();
  g.arc(FX + FW, FY + FH, 14, Math.PI, Math.PI * 1.5);
  g.stroke();

  g.beginPath();
  g.arc(FX, FY + FH, 14, Math.PI * 1.5, Math.PI * 2);
  g.stroke();

  drawGoalShape(g, 0);
  drawGoalShape(g, 1);

  return c;
}

const background = buildBackground();

/* As traves são desenhadas por cima da bola, para ela parecer bater nelas */

function drawPosts() {
  for (const post of POSTS) {
    ctx.fillStyle = '#ffffff';
    ctx.strokeStyle = '#10291a';
    ctx.lineWidth = 1.5;

    ctx.beginPath();
    ctx.arc(post.x, post.y, POST_R, 0, Math.PI * 2);
    ctx.fill();
    ctx.stroke();
  }
}

/* ---------- Desenho dos jogadores ---------- */

function drawPlayer(p, s, isMe, label = 'VOCÊ') {
  const px = -p.fy, py = p.fx;
  const swing = Math.sin(p.walk) * 5;
  const kick = p.kickAnim > 0 ? Math.sin((p.kickAnim / 0.18) * Math.PI) * 11 : 0;

  ctx.fillStyle = 'rgba(0, 0, 0, 0.28)';
  ctx.beginPath();
  ctx.ellipse(p.x + 2, p.y + 4, PR, PR * 0.85, 0, 0, Math.PI * 2);
  ctx.fill();

  if (isMe) {
    ctx.strokeStyle = '#38d6ff';
    ctx.lineWidth = 2;

    ctx.beginPath();
    ctx.ellipse(p.x, p.y + 8, PR + 5, (PR + 5) * 0.45, 0, 0, Math.PI * 2);
    ctx.stroke();
  }

  const angle = Math.atan2(p.fy, p.fx);

  [[1, swing + kick], [-1, -swing]].forEach(([side, off]) => {
    ctx.fillStyle = '#1e1e1e';
    ctx.beginPath();

    ctx.ellipse(
      p.x + px * side * 7 + p.fx * (off + 8),
      p.y + py * side * 7 + p.fy * (off + 8),
      6, 4, angle, 0, Math.PI * 2
    );

    ctx.fill();
  });

  ctx.fillStyle = s.shirt;
  ctx.beginPath();
  ctx.arc(p.x, p.y, 14, 0, Math.PI * 2);
  ctx.fill();

  ctx.strokeStyle = s.trim;
  ctx.lineWidth = 3;
  ctx.stroke();

  ctx.fillStyle = s.hair;
  ctx.beginPath();
  ctx.arc(p.x, p.y, 9, 0, Math.PI * 2);
  ctx.fill();

  ctx.fillStyle = s.skin;
  ctx.beginPath();
  ctx.arc(p.x + p.fx * 3, p.y + p.fy * 3, 6.5, 0, Math.PI * 2);
  ctx.fill();

  if (isMe) {
    const ly = p.y - PR - 12;

    ctx.fillStyle = '#38d6ff';
    ctx.beginPath();
    ctx.moveTo(p.x - 6, ly + 4);
    ctx.lineTo(p.x + 6, ly + 4);
    ctx.lineTo(p.x, ly + 11);
    ctx.closePath();
    ctx.fill();

    ctx.font = 'bold 13px "Trebuchet MS", Verdana, sans-serif';
    ctx.textAlign = 'center';
    ctx.textBaseline = 'alphabetic';
    ctx.lineWidth = 3;
    ctx.strokeStyle = '#10291a';
    ctx.strokeText(label, p.x, ly);

    ctx.fillStyle = '#ffffff';
    ctx.fillText(label, p.x, ly);
  }
}

function drawBall() {
  ctx.fillStyle = 'rgba(0, 0, 0, 0.3)';
  ctx.beginPath();
  ctx.ellipse(ball.x + 3, ball.y + 5, BR, BR * 0.7, 0, 0, Math.PI * 2);
  ctx.fill();

  ctx.save();
  ctx.translate(ball.x, ball.y);
  ctx.rotate(ball.rot);

  ctx.fillStyle = '#ffffff';
  ctx.strokeStyle = '#222222';
  ctx.lineWidth = 1.5;

  ctx.beginPath();
  ctx.arc(0, 0, BR, 0, Math.PI * 2);
  ctx.fill();
  ctx.stroke();

  ctx.fillStyle = '#111111';
  ctx.beginPath();

  for (let i = 0; i < 5; i++) {
    const a = (i / 5) * Math.PI * 2 - Math.PI / 2;
    const x = Math.cos(a) * 4, y = Math.sin(a) * 4;

    if (i === 0) ctx.moveTo(x, y);
    else ctx.lineTo(x, y);
  }

  ctx.closePath();
  ctx.fill();

  for (let i = 0; i < 5; i++) {
    const a = (i / 5) * Math.PI * 2 - Math.PI / 2;

    ctx.beginPath();
    ctx.arc(Math.cos(a) * 8, Math.sin(a) * 8, 2, 0, Math.PI * 2);
    ctx.fill();
  }

  ctx.restore();
}

function roundRectPath(x, y, w, h, r) {
  ctx.beginPath();
  ctx.moveTo(x + r, y);
  ctx.arcTo(x + w, y, x + w, y + h, r);
  ctx.arcTo(x + w, y + h, x, y + h, r);
  ctx.arcTo(x, y + h, x, y + h, r);
  ctx.arcTo(x, y, x + w, y, r);
  ctx.closePath();
}

function drawTag(x, y, text, color, align) {
  ctx.fillStyle = color;
  ctx.strokeStyle = '#10291a';
  ctx.lineWidth = 2;

  ctx.beginPath();
  ctx.arc(x, y, 8, 0, Math.PI * 2);
  ctx.fill();
  ctx.stroke();

  ctx.font = 'bold 15px "Trebuchet MS", Verdana, sans-serif';
  ctx.textAlign = align;
  ctx.textBaseline = 'middle';

  const tx = align === 'right' ? x - 14 : x + 14;

  ctx.lineWidth = 3;
  ctx.strokeText(text, tx, y);

  ctx.fillStyle = '#ffffff';
  ctx.fillText(text, tx, y);
}

function drawScoreboard() {
  const x = CX - 95, y = 6, w = 190, h = 64;

  roundRectPath(x, y, w, h, 8);

  ctx.fillStyle = '#0b0b0b';
  ctx.fill();

  ctx.lineWidth = 4;
  ctx.strokeStyle = '#4a4a4a';
  ctx.stroke();

  ctx.textAlign = 'center';
  ctx.textBaseline = 'middle';
  ctx.font = '38px Impact, "Arial Black", sans-serif';
  ctx.fillStyle = '#ffc933';

  ctx.fillText(String(score.me), CX - 62, y + h / 2 + 1);
  ctx.fillText(String(score.cpu), CX + 62, y + h / 2 + 1);

  const secs = Math.ceil(timeLeft);
  const text = Math.floor(secs / 60) + ':' + String(secs % 60).padStart(2, '0');

  ctx.font = 'bold 17px "Trebuchet MS", Verdana, sans-serif';
  ctx.fillStyle = timeLeft <= 10 ? '#ff6a5c' : '#ffd97a';
  ctx.fillText(text, CX, y + h / 2 + 1);

  let leftLabel = 'VOCÊ';
  let rightLabel = isChampionship ? OPPONENTS[champRound]?.name || 'CPU' : 'CPU';

  if (net.mode !== 'off') {
    leftLabel = 'TIME 1';
    rightLabel = 'TIME 2';
  }

  drawTag(x - 22, 38, leftLabel, myStyle().shirt, 'right');
  drawTag(x + w + 22, 38, rightLabel, activeCpuStyle.shirt, 'left');
}

function drawGoalMessage() {
  const t = GOAL_PAUSE - goalTimer;
  const pop = 1 + 0.3 * Math.max(0, 1 - t * 4);

  ctx.fillStyle = 'rgba(0, 0, 0, 0.45)';
  ctx.fillRect(0, CY - 75, W, 150);

  ctx.save();
  ctx.translate(CX, CY - 12);
  ctx.scale(pop, pop);

  ctx.textAlign = 'center';
  ctx.textBaseline = 'middle';
  ctx.font = 'italic 900 84px Impact, "Arial Black", sans-serif';
  ctx.lineWidth = 8;
  ctx.strokeStyle = '#10291a';
  ctx.strokeText('GOOOL!', 0, 0);

  ctx.fillStyle = '#ffc933';
  ctx.fillText('GOOOL!', 0, 0);
  ctx.restore();

  ctx.font = 'bold 28px "Trebuchet MS", Verdana, sans-serif';
  ctx.textAlign = 'center';
  ctx.fillStyle = '#ffffff';

  ctx.fillText(goalText(), CX, CY + 48);
}

/* ---------- Desenho do replay ---------- */

function drawReplayOverlay() {
  const progress = replayProgress();

  const vg = ctx.createRadialGradient(CX, CY, 180, CX, CY, 520);
  vg.addColorStop(0, 'transparent');
  vg.addColorStop(1, 'rgba(0,0,0,0.55)');

  ctx.fillStyle = vg;
  ctx.fillRect(0, 0, W, H);

  ctx.fillStyle = 'rgba(0,0,0,0.06)';

  for (let y = 0; y < H; y += 4) {
    ctx.fillRect(0, y, W, 2);
  }

  const badgeX = W - 155, badgeY = 14, badgeW = 140, badgeH = 34;

  roundRectPath(badgeX, badgeY, badgeW, badgeH, 6);

  ctx.fillStyle = 'rgba(200, 20, 20, 0.85)';
  ctx.fill();

  const blink = Math.sin(performance.now() * 0.008) > 0;

  if (blink) {
    ctx.fillStyle = '#ff4444';
    ctx.beginPath();
    ctx.arc(badgeX + 16, badgeY + badgeH / 2, 5, 0, Math.PI * 2);
    ctx.fill();
  }

  ctx.font = 'bold 18px "Trebuchet MS", Verdana, sans-serif';
  ctx.fillStyle = '#ffffff';
  ctx.textAlign = 'center';
  ctx.textBaseline = 'middle';
  ctx.fillText('REPLAY', badgeX + badgeW / 2 + 8, badgeY + badgeH / 2);

  ctx.font = 'bold 13px "Trebuchet MS", Verdana, sans-serif';
  ctx.fillStyle = 'rgba(255,255,255,0.6)';
  ctx.textAlign = 'right';
  ctx.fillText('CÂMERA LENTA', W - 20, badgeY + badgeH + 14);

  const barY = H - 6, barH = 4;

  ctx.fillStyle = 'rgba(255,255,255,0.15)';
  ctx.fillRect(0, barY, W, barH);

  ctx.fillStyle = 'rgba(255,80,80,0.75)';
  ctx.fillRect(0, barY, W * progress, barH);
}

function drawGameScene() {
  ctx.drawImage(background, 0, 0);

  players
    .slice()
    .sort((a, b) => a.y - b.y)
    .forEach((p) => drawPlayer(p, styleOf(p), isLocal(p) || isRemoteHuman(p), labelOf(p)));

  drawBall();
  drawPosts();
  drawFx();
  drawScoreboard();
}

function draw() {
  /* fundo por baixo, para o tremor de tela não deixar listras */
  ctx.fillStyle = '#25702f';
  ctx.fillRect(0, 0, W, H);

  ctx.save();

  if (fx.shake > 0.2) {
    ctx.translate((Math.random() * 2 - 1) * fx.shake, (Math.random() * 2 - 1) * fx.shake);
  }

  drawFrame();

  ctx.restore();
}

function drawFrame() {
  if (state === 'replay') {
    const progress = replayProgress();
    const zoomScale = 1 + progress * 0.3;
    const goalX = goalBy === 'me' ? FX + FW * 0.78 : FX + FW * 0.22;
    const focusY = clamp(ball.y, CY - 80, CY + 80);
    const panX = (goalX - CX) * progress * 0.4;
    const panY = (focusY - CY) * progress * 0.25;

    ctx.save();
    ctx.translate(CX, CY);
    ctx.scale(zoomScale, zoomScale);
    ctx.translate(-CX - panX, -CY - panY);

    drawGameScene();

    ctx.restore();
    drawReplayOverlay();
  } else {
    drawGameScene();

    if (state === 'goal') drawGoalMessage();
  }

  if (replayFlash > 0) {
    ctx.fillStyle = 'rgba(255,255,255,' + replayFlash + ')';
    ctx.fillRect(0, 0, W, H);
  }
}

/* ---------- Som (sintetizado no navegador, não usa arquivos) ---------- */

const sfx = (() => {
  let ac = null, master = null, noiseBuf = null;
  let crowdSrc = null, crowdGain = null, crowdWanted = false;
  let muted = false;

  const VOLUME = 0.8;      /* volume geral */
  const CROWD_VOL = 0.05;  /* volume da torcida de fundo */

  try { muted = localStorage.getItem('futebol-de-rua-mudo') === '1'; } catch (err) { /* ignora */ }

  function refresh() {
    const b = document.getElementById('btnSound');

    if (!b) return;

    b.textContent = muted ? '🔇' : '🔊';
    b.setAttribute('aria-pressed', muted ? 'true' : 'false');
  }

  /* Navegadores só liberam o som depois de um clique/tecla do jogador */
  function unlock() {
    if (!ac) {
      const AC = window.AudioContext || window.webkitAudioContext;

      if (!AC) return;

      try { ac = new AC(); } catch (err) { return; }

      master = ac.createGain();
      master.gain.value = muted ? 0 : VOLUME;
      master.connect(ac.destination);

      noiseBuf = ac.createBuffer(1, ac.sampleRate * 2, ac.sampleRate);

      const d = noiseBuf.getChannelData(0);

      for (let i = 0; i < d.length; i++) d[i] = Math.random() * 2 - 1;
    }

    if (ac.state === 'suspended') ac.resume();

    applyCrowd();
  }

  function setMuted(v) {
    muted = v;

    try { localStorage.setItem('futebol-de-rua-mudo', v ? '1' : '0'); } catch (err) { /* ignora */ }

    if (master) master.gain.setTargetAtTime(v ? 0 : VOLUME, ac.currentTime, 0.02);

    refresh();
  }

  function applyCrowd() {
    if (!ac) return;

    if (!crowdSrc) {
      crowdSrc = ac.createBufferSource();
      crowdSrc.buffer = noiseBuf;
      crowdSrc.loop = true;

      const f = ac.createBiquadFilter();

      f.type = 'bandpass';
      f.frequency.value = 650;
      f.Q.value = 0.5;

      crowdGain = ac.createGain();
      crowdGain.gain.value = 0;

      crowdSrc.connect(f);
      f.connect(crowdGain);
      crowdGain.connect(master);
      crowdSrc.start();
    }

    crowdGain.gain.setTargetAtTime(crowdWanted ? CROWD_VOL : 0, ac.currentTime, 0.4);
  }

  function dest(pan) {
    if (!pan || !ac.createStereoPanner) return master;

    const p = ac.createStereoPanner();

    p.pan.value = Math.max(-1, Math.min(1, pan));
    p.connect(master);

    return p;
  }

  function tone(o) {
    const t = ac.currentTime + (o.delay || 0);
    const osc = ac.createOscillator();
    const g = ac.createGain();

    osc.type = o.type || 'sine';
    osc.frequency.setValueAtTime(o.f, t);

    if (o.f2) osc.frequency.exponentialRampToValueAtTime(o.f2, t + o.dur);

    g.gain.setValueAtTime(0.0001, t);
    g.gain.exponentialRampToValueAtTime(o.vol, t + 0.006);
    g.gain.exponentialRampToValueAtTime(0.0001, t + o.dur);

    osc.connect(g);
    g.connect(dest(o.pan));
    osc.start(t);
    osc.stop(t + o.dur + 0.03);
  }

  function noise(o) {
    const t = ac.currentTime + (o.delay || 0);
    const src = ac.createBufferSource();
    const f = ac.createBiquadFilter();
    const g = ac.createGain();
    const attack = o.attack || 0.004;

    src.buffer = noiseBuf;
    src.loop = true;

    f.type = o.type || 'bandpass';
    f.frequency.setValueAtTime(o.f || 1000, t);

    if (o.f2) f.frequency.exponentialRampToValueAtTime(o.f2, t + o.dur);

    f.Q.value = o.q || 1;

    g.gain.setValueAtTime(0.0001, t);
    g.gain.exponentialRampToValueAtTime(o.vol, t + attack);
    g.gain.exponentialRampToValueAtTime(0.0001, t + o.dur);

    src.connect(f);
    f.connect(g);
    g.connect(dest(o.pan));
    src.start(t, Math.random() * 1.5);
    src.stop(t + o.dur + 0.03);
  }

  function whistle(dur, delay) {
    const t = ac.currentTime + delay;
    const osc = ac.createOscillator();
    const lfo = ac.createOscillator();
    const lg = ac.createGain();
    const g = ac.createGain();

    osc.type = 'sine';
    osc.frequency.value = 2900;
    lfo.frequency.value = 38;
    lg.gain.value = 90;

    lfo.connect(lg);
    lg.connect(osc.frequency);

    g.gain.setValueAtTime(0.0001, t);
    g.gain.exponentialRampToValueAtTime(0.22, t + 0.02);
    g.gain.setValueAtTime(0.22, t + dur - 0.04);
    g.gain.exponentialRampToValueAtTime(0.0001, t + dur);

    osc.connect(g);
    g.connect(master);
    osc.start(t);
    lfo.start(t);
    osc.stop(t + dur + 0.03);
    lfo.stop(t + dur + 0.03);

    noise({ dur, vol: 0.05, f: 3200, q: 2, delay });
  }

  return {
    unlock,
    refresh,
    toggleMute() { unlock(); setMuted(!muted); },

    crowd(on) {
      crowdWanted = on;
      applyCrowd();
    },

    kick(s, pan) {
      if (!ac) return;
      tone({ f: 190, f2: 55, dur: 0.13, vol: 0.35 + 0.3 * s, pan });
      noise({ dur: 0.05, vol: 0.12 + 0.12 * s, f: 1800, q: 0.8, pan });
    },

    touch(s, pan) {
      if (!ac) return;
      tone({ f: 150, f2: 90, dur: 0.07, vol: 0.12 + 0.12 * s, pan });
    },

    wall(s, pan) {
      if (!ac) return;
      tone({ f: 115, f2: 60, dur: 0.1, vol: 0.12 + 0.14 * s, pan });
      noise({ dur: 0.04, vol: 0.06 + 0.06 * s, f: 600, q: 0.7, pan });
    },

    post(s, pan) {
      if (!ac) return;
      /* "ding" metálico da trave */
      tone({ f: 1250, dur: 0.55, vol: 0.18 + 0.14 * s, pan });
      tone({ f: 1870, dur: 0.4, vol: 0.1 + 0.06 * s, pan });
      tone({ f: 2630, dur: 0.28, vol: 0.06, pan });
      tone({ f: 230, f2: 120, dur: 0.08, vol: 0.2, pan });
      noise({ dur: 0.03, vol: 0.14, f: 3500, q: 0.8, type: 'highpass', pan });
    },

    net(pan) {
      if (!ac) return;
      noise({ dur: 0.4, vol: 0.22, f: 900, f2: 300, q: 0.9, pan });
    },

    whoosh() {
      if (!ac) return;
      noise({ dur: 0.5, vol: 0.14, f: 250, f2: 2600, q: 1.2, attack: 0.15 });
    },

    goal() {
      if (!ac) return;

      /* torcida */
      noise({ dur: 2.2, vol: 0.5, f: 1300, f2: 900, q: 0.6, attack: 0.25 });
      noise({ dur: 2.0, vol: 0.32, f: 500, type: 'lowpass', attack: 0.2 });

      /* melodia de gol */
      [523, 659, 784, 1047].forEach((f, i) => tone({ f, dur: 0.22, type: 'triangle', vol: 0.18, delay: i * 0.11 }));
      tone({ f: 1047, dur: 0.7, type: 'triangle', vol: 0.16, delay: 0.46 });

      /* buzina */
      tone({ f: 233, dur: 0.9, type: 'sawtooth', vol: 0.06, delay: 0.1 });
      tone({ f: 349, dur: 0.9, type: 'sawtooth', vol: 0.05, delay: 0.1 });

      if (crowdGain) {
        const t = ac.currentTime;

        crowdGain.gain.setTargetAtTime(CROWD_VOL * 3, t, 0.1);
        crowdGain.gain.setTargetAtTime(crowdWanted ? CROWD_VOL : 0, t + 1.6, 0.6);
      }
    },

    whistleStart() {
      if (ac) whistle(0.45, 0);
    },

    whistleEnd() {
      if (!ac) return;
      whistle(0.25, 0);
      whistle(0.25, 0.35);
      whistle(0.65, 0.7);
    },

    click() {
      if (!ac) return;
      tone({ f: 660, f2: 880, dur: 0.05, type: 'triangle', vol: 0.07 });
    }
  };
})();

['pointerdown', 'keydown'].forEach((ev) => window.addEventListener(ev, () => sfx.unlock(), { capture: true }));

$('btnSound').addEventListener('click', () => sfx.toggleMute());
sfx.refresh();

function onStateSound(prev, next) {
  if (next === prev) return;

  sfx.crowd(next === 'playing' || next === 'goal' || next === 'replay');

  if (next === 'playing' && prev !== 'paused') sfx.whistleStart();
  else if (next === 'ended') sfx.whistleEnd();
  else if (next === 'replay') sfx.whoosh();
  else if (next === 'goal') fxGoal();
  else if (next === 'champEnd') {
    sfx.goal();
    confetti(myStyle().shirt);
  }
}

/* ---------- Efeitos visuais ---------- */

const fx = {
  particles: [],
  flashes: [],
  shake: 0,
  cool: { kick: 0, touch: 0, wall: 0, post: 0, net: 0 },
  out: []   /* eventos que o anfitrião manda para os convidados */
};

const pick = (arr) => arr[Math.floor(Math.random() * arr.length)];

function clearFx() {
  fx.particles.length = 0;
  fx.flashes.length = 0;
  fx.shake = 0;
}

function burst(x, y, n, o) {
  for (let i = 0; i < n && fx.particles.length < 450; i++) {
    const a = Math.random() * Math.PI * 2;
    const sp = o.speed * (0.3 + Math.random() * 0.7);

    fx.particles.push({
      kind: 'dot', x, y,
      vx: Math.cos(a) * sp, vy: Math.sin(a) * sp,
      g: o.g || 0, drag: o.drag || 3,
      life: 0, max: o.life * (0.6 + Math.random() * 0.8),
      size: o.size * (0.6 + Math.random() * 0.8),
      color: pick(o.colors)
    });
  }
}

function confetti(teamColor) {
  const colors = [teamColor, '#ffffff', '#ffc933', '#38d6ff', '#ff5fa2'];

  /* chuva de confete */
  for (let i = 0; i < 130 && fx.particles.length < 450; i++) {
    fx.particles.push({
      kind: 'conf',
      x: FX + Math.random() * FW, y: FY - 10 - Math.random() * 90,
      vx: (Math.random() * 2 - 1) * 50, vy: 60 + Math.random() * 160,
      g: 90, drag: 1.2,
      life: 0, max: 2.6 + Math.random() * 1.4,
      w: 5 + Math.random() * 4, h: 4 + Math.random() * 4,
      rot: Math.random() * Math.PI, vr: (Math.random() * 2 - 1) * 9,
      color: pick(colors)
    });
  }

  /* jato saindo do gol */
  const gx = goalBy === 'me' ? FX + FW : FX;
  const dir = goalBy === 'me' ? -1 : 1;

  for (let i = 0; i < 40 && fx.particles.length < 450; i++) {
    fx.particles.push({
      kind: 'conf',
      x: gx, y: CY + (Math.random() * 2 - 1) * GOAL_H / 2,
      vx: dir * (80 + Math.random() * 260), vy: -(40 + Math.random() * 240),
      g: 300, drag: 1.5,
      life: 0, max: 1.6 + Math.random() * 1.2,
      w: 5 + Math.random() * 4, h: 4 + Math.random() * 4,
      rot: Math.random() * Math.PI, vr: (Math.random() * 2 - 1) * 12,
      color: pick(colors)
    });
  }
}

function fxGoal() {
  sfx.goal();
  fx.shake = Math.max(fx.shake, 9);
  confetti(goalBy === 'me' ? myStyle().shirt : activeCpuStyle.shirt);
}

function wallHit(v) {
  const sp = Math.abs(v);

  if (sp > 140) emitFx('wall', ball.x, ball.y, clamp(sp / 700, 0.2, 1));
}

/* Quem simula a partida (offline ou anfitrião) chama isto. O convidado recebe os eventos pelo anfitrião. */

function emitFx(type, x, y, s) {
  if (net.mode === 'guest') return;
  if (fx.cool[type] > 0) return;

  fx.cool[type] = type === 'kick' ? 0.05 : 0.08;

  playFx(type, x, y, s);

  if (net.mode === 'host' && fx.out.length < 20) {
    fx.out.push([type, Math.round(x), Math.round(y), Math.round(s * 100) / 100]);
  }
}

function playFx(type, x, y, s) {
  const pan = clamp((x - CX) / (FW / 2), -1, 1) * 0.6;

  switch (type) {
    case 'kick':
      sfx.kick(s, pan);
      burst(x, y, 5, { speed: 90 + 120 * s, life: 0.35, size: 3, colors: ['#f4f4ee', '#d9e8d0', '#b7d3a8'], drag: 4 });
      break;

    case 'touch':
      sfx.touch(s, pan);
      break;

    case 'wall':
      sfx.wall(s, pan);
      burst(x, y, 3, { speed: 70, life: 0.3, size: 2.5, colors: ['#f4f4ee', '#d9e8d0'], drag: 4 });
      fx.shake = Math.max(fx.shake, 1.5 * s);
      break;

    case 'post':
      sfx.post(s, pan);
      burst(x, y, 12, { speed: 230, life: 0.45, size: 2.6, colors: ['#ffffff', '#ffe27a', '#ffc933'], drag: 3 });
      fx.flashes.push({ x, y, t: 0 });
      fx.shake = Math.max(fx.shake, 6 * s + 2);
      break;

    case 'net':
      sfx.net(pan);
      burst(x, y, 8, { speed: 120, life: 0.5, size: 2, colors: ['#ffffff', '#cfe8ff'], drag: 3 });
      break;
  }

  fx.shake = Math.min(fx.shake, 12);
}

function updateFx(dt) {
  for (const k in fx.cool) fx.cool[k] = Math.max(0, fx.cool[k] - dt);

  const ps = fx.particles;

  for (let i = ps.length - 1; i >= 0; i--) {
    const q = ps[i];

    q.life += dt;

    if (q.life >= q.max) {
      ps.splice(i, 1);
      continue;
    }

    const d = Math.exp(-q.drag * dt);

    q.vx *= d;
    q.vy = q.vy * d + q.g * dt;
    q.x += q.vx * dt;
    q.y += q.vy * dt;

    if (q.kind === 'conf') {
      q.rot += q.vr * dt;
      q.x += Math.sin(q.life * 6 + q.rot) * 0.4;
    }
  }

  for (let i = fx.flashes.length - 1; i >= 0; i--) {
    fx.flashes[i].t += dt;
    if (fx.flashes[i].t > 0.4) fx.flashes.splice(i, 1);
  }

  fx.shake = fx.shake > 0.2 ? fx.shake * Math.pow(0.002, dt) : 0;
}

function drawFx() {
  for (const f of fx.flashes) {
    const k = f.t / 0.4;

    ctx.strokeStyle = 'rgba(255, 255, 255, ' + (1 - k) + ')';
    ctx.lineWidth = 3;
    ctx.beginPath();
    ctx.arc(f.x, f.y, POST_R + k * 34, 0, Math.PI * 2);
    ctx.stroke();

    ctx.fillStyle = 'rgba(255, 240, 160, ' + 0.6 * (1 - k) + ')';
    ctx.beginPath();
    ctx.arc(f.x, f.y, POST_R + 4, 0, Math.PI * 2);
    ctx.fill();
  }

  for (const q of fx.particles) {
    const k = 1 - q.life / q.max;

    if (q.kind === 'conf') {
      ctx.save();
      ctx.translate(q.x, q.y);
      ctx.rotate(q.rot);
      ctx.globalAlpha = Math.min(1, k * 2);
      ctx.fillStyle = q.color;
      ctx.fillRect(-q.w / 2, -q.h / 2, q.w, q.h * Math.abs(Math.cos(q.rot * 2)) + 0.6);
      ctx.restore();
    } else {
      ctx.globalAlpha = Math.max(0, k);
      ctx.fillStyle = q.color;
      ctx.beginPath();
      ctx.arc(q.x, q.y, q.size * (0.5 + k * 0.5), 0, Math.PI * 2);
      ctx.fill();
    }
  }

  ctx.globalAlpha = 1;
}

/* ---------- Online (até 6 PCs na mesma rede) ---------- */
/* O anfitrião roda a partida inteira e manda o estado ~60x por segundo para todos.
   Cada convidado só manda os controles do seu jogador e desenha o que recebe.
   Vagas sem pessoa ficam com o computador. */

const ZERO_INPUT = { dx: 0, dy: 0, kick: false };

function myTeam() {
  if (net.mode === 'off') return 'me';

  const q = players.find((x) => x.gid === net.myGid);

  return q ? q.team : 'me';
}

function isSpectator() {
  return net.mode === 'guest' && net.spec;
}

function labelOf(p) {
  if (net.mode === 'off') return 'VOCÊ';

  const m = net.members.find((x) => x.gid === p.gid);

  return m ? m.name : (isLocal(p) ? 'VOCÊ' : 'J' + ((p.gid || 0) + 1));
}

function goalText() {
  if (net.mode === 'off') return iScored() ? 'Você marcou!' : 'O adversário marcou';
  if (isSpectator()) return goalBy === 'me' ? 'Time 1 marcou!' : 'Time 2 marcou!';

  return iScored() ? 'Seu time marcou!' : 'O outro time marcou';
}

function isLocal(p) {
  return net.mode === 'guest' ? p.gid === net.myGid : p === me;
}

function isRemoteHuman(p) {
  return net.mode !== 'off' && p.gid !== null && !isLocal(p);
}

function iScored() {
  return goalBy === myTeam();
}

function replayProgress() {
  if (net.mode === 'guest') return net.rp;
  return replayFrames.length > 1 ? replayIndex / (replayFrames.length - 1) : 0;
}

function setNetMode(mode) {
  net.mode = mode;
  document.body.classList.toggle('net-on', mode !== 'off');
  document.body.classList.toggle('net-guest', mode === 'guest');
  document.body.classList.toggle('net-spec', mode === 'guest' && net.spec);
}

function netSend(obj) {
  if (net.ws && net.ws.readyState === 1) net.ws.send(JSON.stringify(obj));
}

function setOnlineStatus(text) {
  $('onlineStatus').textContent = text;
}

function resetOnlineUI() {
  $('onlineChoose').classList.remove('hidden');
  $('roomView').classList.add('hidden');
  $('btnOnlineStart').classList.add('hidden');
  setOnlineStatus('');
}

function closeSocket() {
  if (!net.ws) return;

  const ws = net.ws;

  net.ws = null;
  ws.onclose = null;

  try { ws.close(); } catch (err) { /* ignora */ }
}

function leaveOnline() {
  const was = net.mode !== 'off';

  closeSocket();
  setNetMode('off');
  net.peers = new Map();
  net.assign = [];
  net.ready = false;
  net.members = [];
  net.known = new Set();
  net.matchOn = false;
  net.spec = false;
  net.myGid = 0;
  resetOnlineUI();

  if (was) {
    teamSize = net.baseSize;
    netStyleMe = null;
    activeCpuStyle = STYLE_CPU;
    buildTeams();
  }
}

function backToLobby(message) {
  clearInput();
  score.me = 0;
  score.cpu = 0;
  net.matchOn = false;
  resetPositions();
  setState('menu');
  showOverlay('online');
  setOnlineStatus(message);

  if (net.mode === 'host') netSend({ t: 'lobby' });
}

const okColor = (c, fallback) => (typeof c === 'string' && /^#[0-9a-fA-F]{6}$/.test(c) ? c : fallback);

function sanitizeStyle(st) {
  const o = st || {};

  return {
    shirt: okColor(o.shirt, '#ffc933'),
    trim: okColor(o.trim, '#1b4fa8'),
    hair: okColor(o.hair, '#5a3418'),
    skin: okColor(o.skin, '#f2c9a0')
  };
}

function cleanName(v) {
  return String(v == null ? '' : v).replace(/[^\p{L}\p{N} _.\-]/gu, '').trim().slice(0, 12);
}

function initPayload() {
  return { t: 'init', size: teamSize, styleMe: STYLE_ME, styleCpu: STYLE_CPU, assign: net.assign };
}

/* Anfitrião: monta as vagas de cada time antes de cada partida.
   Time 1 (amarelo) = 'me', ataca a direita. Time 2 (vermelho) = 'cpu', ataca a esquerda. */

function hostPrepare() {
  teamSize = net.size;
  netStyleMe = STYLE_ME;
  activeCpuStyle = STYLE_CPU;
  net.assign = [];

  [1, 2].forEach((t) => {
    net.members
      .filter((m) => !m.spec && m.team === t)
      .sort((a, b) => a.gid - b.gid)
      .slice(0, teamSize)
      .forEach((m, i) => net.assign.push({ team: t === 1 ? 'me' : 'cpu', idx: i, gid: m.gid }));
  });

  net.matchOn = true;
  netSend(initPayload());
}

function showRoomView() {
  $('onlineChoose').classList.add('hidden');
  $('roomView').classList.remove('hidden');
  $('roomCodeShow').textContent = net.code;
  renderRoom();
}

/* Lista da sala: vagas de cada time (com nomes) e espectadores */

function renderRoom() {
  const size = net.size;

  [1, 2].forEach((t) => {
    const box = $('team' + t + 'List');
    const list = net.members.filter((m) => !m.spec && m.team === t).slice(0, size);
    const title = document.createElement('div');

    box.textContent = '';
    title.className = 'team-title';
    title.textContent = 'Time ' + t + ' — ' + (t === 1 ? 'Amarelo' : 'Vermelho') + ' (' + list.length + '/' + size + ')';
    box.appendChild(title);

    for (let i = 0; i < size; i++) {
      const row = document.createElement('div');
      const m = list[i];

      row.className = m ? 'slot' : 'slot free';
      row.textContent = m ? m.name + (m.host ? ' ★' : '') + (m.gid === net.myGid ? ' (você)' : '') : 'vaga livre';
      box.appendChild(row);
    }
  });

  const specs = net.members.filter((m) => m.spec);

  $('specList').textContent = 'Espectadores (' + specs.length + '/5): ' +
    (specs.length ? specs.map((s) => s.name).join(', ') : 'ninguém ainda');

  if (net.mode === 'host') {
    $('btnOnlineStart').classList.toggle('hidden', net.peers.size < 1);

    if (state === 'menu') {
      setOnlineStatus(net.peers.size < 1
        ? 'Aguardando outro jogador entrar com o código da sala...'
        : 'Quando todos estiverem na sala, clique em COMEÇAR PARTIDA.');
    }
  }
}

/* Anfitrião: acompanha quem entrou e saiu da sala */

function hostSync() {
  const present = new Set();
  const fresh = [];

  for (const mm of net.members) {
    if (!net.known.has(mm.gid)) fresh.push(mm);

    if (!mm.spec && !mm.host) {
      present.add(mm.gid);

      if (!net.peers.has(mm.gid)) net.peers.set(mm.gid, { input: { dx: 0, dy: 0, kick: false } });
    }
  }

  net.known = new Set(net.members.map((x) => x.gid));

  /* Quem saiu é substituído pelo computador */
  let left = false;

  for (const gid of Array.from(net.peers.keys())) {
    if (present.has(gid)) continue;

    net.peers.delete(gid);
    left = true;

    const q = players.find((x) => x.gid === gid);

    if (q) {
      q.human = false;
      q.gid = null;
    }
  }

  net.assign = net.assign.filter((a) => a.gid === 0 || present.has(a.gid));

  if (!net.matchOn) return;

  /* Quem entra no meio da partida pega uma vaga livre do time escolhido (espectador só assiste) */
  for (const mm of fresh) {
    if (mm.spec || mm.host) continue;

    const team = mm.team === 1 ? 'me' : 'cpu';
    const used = new Set(net.assign.filter((a) => a.team === team).map((a) => a.idx));
    let idx = -1;

    for (let i = 0; i < teamSize; i++) {
      if (!used.has(i)) {
        idx = i;
        break;
      }
    }

    if (idx < 0) continue;

    net.assign.push({ team, idx, gid: mm.gid });

    const q = players.find((x) => x.team === team && x.idx === idx);

    if (q) {
      q.human = true;
      q.gid = mm.gid;
    }
  }

  if (fresh.length) netSend(initPayload());

  if (left && net.peers.size === 0) {
    backToLobby('Os outros jogadores saíram. Aguardando alguém entrar com o código ' + net.code + '...');
  }
}

function applyRoom(m) {
  net.size = clamp(Number(m.size) | 0, 1, 5);

  net.members = (Array.isArray(m.members) ? m.members : []).slice(0, 20).map((x) => ({
    gid: Number(x.gid) | 0,
    name: cleanName(x.name) || 'Jogador',
    team: x.team === 2 ? 2 : 1,
    spec: !!x.spec,
    host: !!x.host
  }));

  if (net.mode === 'host') hostSync();

  renderRoom();
}

function netConnect(onOpen) {
  if (location.protocol === 'file:') {
    setOnlineStatus('Para jogar online, rode "node server.js" e abra o jogo pelo endereço http://...:3000');
    return;
  }

  closeSocket();
  setOnlineStatus('Conectando...');

  let ws;
  let opened = false;

  try {
    ws = new WebSocket((location.protocol === 'https:' ? 'wss://' : 'ws://') + location.host);
  } catch (err) {
    setOnlineStatus('Não foi possível conectar ao servidor.');
    return;
  }

  net.ws = ws;

  ws.onopen = () => {
    opened = true;
    onOpen();
  };

  ws.onmessage = (ev) => {
    let m;

    try { m = JSON.parse(ev.data); } catch (err) { return; }

    handleNet(m);
  };

  ws.onclose = () => {
    if (net.ws !== ws) return;

    net.ws = null;
    leaveOnline();
    backToLobby(opened
      ? 'A conexão com o servidor caiu.'
      : 'Não foi possível conectar. Rode "node server.js" e abra o jogo por ele.');
  };
}

function handleNet(m) {
  switch (m.t) {
    case 'created':
      net.code = String(m.code);
      showRoomView();
      setOnlineStatus('Sala criada! Passe o código para seus amigos.');
      break;

    case 'joined':
      net.myGid = Number(m.gid) || 0;
      net.size = clamp(Number(m.size) | 0, 1, 5);
      setNetMode('guest');
      showRoomView();
      setOnlineStatus(net.spec
        ? 'Você entrou como espectador. Aguardando a partida...'
        : 'Conectado! Aguardando o anfitrião começar a partida...');
      break;

    case 'room':
      applyRoom(m);
      break;

    case 'in': {
      if (net.mode !== 'host') break;

      const peer = net.peers.get(m.from);

      if (!peer) break;

      peer.input.dx = clamp(Number(m.dx) || 0, -1, 1);
      peer.input.dy = clamp(Number(m.dy) || 0, -1, 1);
      peer.input.kick = !!m.k;
      break;
    }

    case 'init':
      if (net.mode !== 'guest') break;

      teamSize = clamp(Number(m.size) | 0, 1, 5);
      netStyleMe = sanitizeStyle(m.styleMe);
      activeCpuStyle = sanitizeStyle(m.styleCpu);

      net.assign = Array.isArray(m.assign)
        ? m.assign.slice(0, 10).map((a) => ({ team: a.team === 'cpu' ? 'cpu' : 'me', idx: clamp(Number(a.idx) | 0, 0, 4), gid: Number(a.gid) | 0 }))
        : [];

      buildTeams();
      net.ready = true;
      break;

    case 's':
      if (net.mode === 'guest') applySnapshot(m);
      break;

    case 'lobby':
      if (net.mode === 'guest') {
        clearInput();
        score.me = 0;
        score.cpu = 0;
        setState('menu');
        showOverlay('online');
        setOnlineStatus('Aguardando o anfitrião começar a partida...');
      }
      break;

    case 'left':
      if (net.mode === 'guest') {
        leaveOnline();
        backToLobby('O anfitrião saiu da sala.');
      }
      break;

    case 'error':
      if (net.mode === 'off') closeSocket();
      setOnlineStatus(m.msg || 'Erro de conexão.');
      break;
  }
}

/* Anfitrião: manda o estado do jogo */

function sendSnapshot() {
  const r = (v) => Math.round(v * 10) / 10;
  const r2 = (v) => Math.round(v * 100) / 100;

  netSend({
    t: 's',
    st: state,
    tl: r(timeLeft),
    sc: [score.me, score.cpu],
    gb: goalBy,
    gt: r2(goalTimer),
    rp: Math.round(replayProgress() * 1000) / 1000,
    rf: r2(replayFlash),
    ev: fx.out.splice(0),
    b: [r(ball.x), r(ball.y), r2(ball.rot)],
    ps: players.map((q) => [r(q.x), r(q.y), r2(q.fx), r2(q.fy), r2(q.walk), r2(q.kickAnim), q.gid === null ? -1 : q.gid])
  });
}

/* Convidado: aplica o estado recebido */

function applySnapshot(m) {
  if (!net.ready) return;
  if (!Array.isArray(m.b) || !Array.isArray(m.ps) || !Array.isArray(m.sc)) return;

  score.me = m.sc[0] | 0;
  score.cpu = m.sc[1] | 0;
  timeLeft = Number(m.tl) || 0;
  goalBy = m.gb === 'cpu' ? 'cpu' : 'me';
  goalTimer = Number(m.gt) || 0;
  net.rp = Number(m.rp) || 0;
  replayFlash = Number(m.rf) || 0;

  if (Array.isArray(m.ev)) {
    for (const ev of m.ev.slice(0, 8)) {
      if (Array.isArray(ev)) {
        playFx(String(ev[0]), Number(ev[1]) || CX, Number(ev[2]) || CY, clamp(Number(ev[3]) || 0.5, 0, 1));
      }
    }
  }

  ball.x = Number(m.b[0]) || 0;
  ball.y = Number(m.b[1]) || 0;
  ball.rot = Number(m.b[2]) || 0;

  m.ps.forEach((sp, i) => {
    const q = players[i];

    if (!q || !Array.isArray(sp)) return;

    q.x = Number(sp[0]) || 0;
    q.y = Number(sp[1]) || 0;
    q.fx = Number(sp[2]) || 0;
    q.fy = Number(sp[3]) || 0;
    q.walk = Number(sp[4]) || 0;
    q.kickAnim = Number(sp[5]) || 0;

    const g = Number(sp[6]);

    q.gid = Number.isFinite(g) && g >= 0 ? g : null;
    q.human = q.gid !== null;
  });

  if (m.st !== state) guestEnterState(m.st);
}

function guestEnterState(st) {
  if (st === 'ended') {
    guestShowEnd();
  } else if (st === 'playing' || st === 'goal' || st === 'replay') {
    setState(st);
  }
}

function guestShowEnd() {
  const t = myTeam();
  const mine = score[t], theirs = score[t === 'me' ? 'cpu' : 'me'];

  $('endTitle').textContent = 'FIM DE JOGO';

  if (isSpectator()) {
    $('endResult').textContent = score.me > score.cpu ? 'TIME 1 VENCEU!' : (score.me < score.cpu ? 'TIME 2 VENCEU!' : 'EMPATE!');
    $('endScore').textContent = 'Time 1 ' + score.me + ' x ' + score.cpu + ' Time 2';
  } else {
    $('endResult').textContent = mine > theirs ? 'SEU TIME VENCEU!' : (mine < theirs ? 'O OUTRO TIME VENCEU' : 'EMPATE!');
    $('endScore').textContent = 'Seu time ' + mine + ' x ' + theirs + ' Outro time';
  }

  $('endChampInfo').textContent = 'Aguardando o anfitrião...';
  $('endChampInfo').classList.remove('hidden');
  $('btnAgain').classList.add('hidden');
  $('endNormalActions').classList.remove('hidden');
  $('endChampActions').classList.add('hidden');

  setState('ended');
}

/* Chamado a cada quadro */

function netTick(now) {
  if (net.mode === 'host') {
    if (net.members.length > 1 && state !== 'menu') sendSnapshot();
    else fx.out.length = 0;
  } else if (net.mode === 'guest' && !net.spec) {
    const i = localInput();
    const key = i.dx + ',' + i.dy + ',' + (i.kick ? 1 : 0);

    if (key !== net.lastSent || now - net.lastSentAt > 200) {
      net.lastSent = key;
      net.lastSentAt = now;
      netSend({ t: 'in', dx: i.dx, dy: i.dy, k: i.kick ? 1 : 0 });
    }
  }
}

/* Botões da tela online */

const onlineUI = { mode: 'create', size: 5, team: 1 };

try { $('playerName').value = localStorage.getItem('futebol-de-rua-nome') || ''; } catch (err) { /* ignora */ }

function refreshOnlineForm() {
  $('rowCode').classList.toggle('hidden', onlineUI.mode === 'create');
  $('rowSize').classList.toggle('hidden', onlineUI.mode !== 'create');
  $('rowTeam').classList.toggle('hidden', onlineUI.mode === 'spec');

  $('btnOnlineGo').textContent = onlineUI.mode === 'create' ? 'CRIAR SALA'
    : (onlineUI.mode === 'play' ? 'ENTRAR PARA JOGAR' : 'ENTRAR COMO ESPECTADOR');
}

function bindSeg(attr, key, conv) {
  const sel = '.seg-btn[data-' + attr + ']';

  document.querySelectorAll(sel).forEach((btn) => {
    btn.addEventListener('click', () => {
      onlineUI[key] = conv(btn.dataset[attr]);
      document.querySelectorAll(sel).forEach((b) => b.classList.toggle('active', b === btn));
      refreshOnlineForm();
    });
  });
}

bindSeg('omode', 'mode', String);
bindSeg('osize', 'size', Number);
bindSeg('oteam', 'team', Number);
refreshOnlineForm();

$('btnOnline').addEventListener('click', () => {
  resetOnlineUI();
  showOverlay('online');
});

$('btnOnlineBack').addEventListener('click', () => {
  leaveOnline();
  showOverlay('menu');
});

$('btnOnlineGo').addEventListener('click', () => {
  const name = cleanName($('playerName').value);
  const code = $('roomCode').value.trim();

  if (!name) {
    setOnlineStatus('Digite seu nome.');
    return;
  }

  if (onlineUI.mode !== 'create' && !/^\d{4}$/.test(code)) {
    setOnlineStatus('Digite o código de 4 números.');
    return;
  }

  try { localStorage.setItem('futebol-de-rua-nome', name); } catch (err) { /* ignora */ }

  if (net.mode === 'off') net.baseSize = teamSize;

  net.name = name;
  net.spec = onlineUI.mode === 'spec';
  net.code = code;

  if (onlineUI.mode === 'create') {
    netConnect(() => {
      net.peers = new Map();
      net.assign = [];
      net.members = [];
      net.known = new Set();
      net.matchOn = false;
      net.spec = false;
      net.myGid = 0;
      setNetMode('host');
      netSend({ t: 'create', name, size: onlineUI.size, team: onlineUI.team });
    });
  } else {
    netConnect(() => netSend({ t: 'join', code, name, team: onlineUI.team, spec: net.spec }));
  }
});

$('btnOnlineStart').addEventListener('click', () => {
  if (net.mode !== 'host' || net.peers.size < 1) return;

  isChampionship = false;
  startMatch();
});

/* ---------- Laço principal ---------- */

let lastTime = performance.now();

function loop(now) {
  const dt = Math.min((now - lastTime) / 1000, 0.033);

  lastTime = now;

  update(dt);
  draw();
  netTick(now);

  requestAnimationFrame(loop);
}

buildTeams();
buildCharPicker();
resetPositions();
setState('menu');
requestAnimationFrame(loop);