import { VibiNet } from "./vendor/vibinet.js";
import { getMap } from "./generated/bend-api.js";

const root = document.querySelector("#app");
if (!root) {
  throw new Error("Missing #app");
}

const PHASE = {
  LOBBY: "lobby",
  PLAYING: "playing",
  STAGE_CLEAR: "stage_clear",
  CAMPAIGN_END: "campaign_end",
};

const DIR = {
  UP: 0,
  DOWN: 1,
  LEFT: 2,
  RIGHT: 3,
};

const TICK_RATE = 8;
const TOLERANCE_MS = 250;
const HEARTBEAT_MS = 2500;
const RENDER_MS = 120;
const PRESENCE_TIMEOUT_TICKS = 48;
const CHAT_LIMIT = 64;
const STORAGE = {
  user: "vibi-duopuzzle-user",
  room: "vibi-duopuzzle-room",
  uid: "vibi-duopuzzle-session-uid",
};
const COLOR_NAMES = ["Azul", "Verde", "Roxo", "Amarelo", "Marrom", "Vermelho"];
const SYSTEM_NAME = "sistema";

const U32 = { $: "UInt", size: 32 };
const U8 = { $: "UInt", size: 8 };

const POST_PACKER = {
  $: "Union",
  variants: {
    join: {
      $: "Struct",
      fields: {
        uid: U32,
        user: { $: "String" },
      },
    },
    heartbeat: {
      $: "Struct",
      fields: {
        uid: U32,
      },
    },
    leave: {
      $: "Struct",
      fields: {
        uid: U32,
      },
    },
    ready: {
      $: "Struct",
      fields: {
        uid: U32,
      },
    },
    unready: {
      $: "Struct",
      fields: {
        uid: U32,
      },
    },
    chat: {
      $: "Struct",
      fields: {
        uid: U32,
        name: { $: "String" },
        text: { $: "String" },
      },
    },
    move: {
      $: "Struct",
      fields: {
        uid: U32,
        dir: U8,
      },
    },
    victory_ready: {
      $: "Struct",
      fields: {
        uid: U32,
      },
    },
  },
};

const MAPS = Array.from({ length: 10 }, (_, index) => getMap(index + 1));

const ui = {
  userInput: window.localStorage.getItem(STORAGE.user) ?? "",
  roomInput: window.localStorage.getItem(STORAGE.room) ?? "",
  chatInput: "",
  status: "idle",
  error: "",
  uid: getOrCreateUid(),
};

const connection = {
  game: null,
  room: "",
  user: "",
  synced: false,
  renderTimer: null,
  heartbeatTimer: null,
};

let latestState = makeInitialState();

function clientApi() {
  return connection.game?.client_api ?? null;
}

function clientDebug() {
  const api = clientApi();
  if (!api || typeof api.debug_dump !== "function") {
    return null;
  }
  return api.debug_dump();
}

function socketReadyState() {
  const readyState = clientDebug()?.ws_ready_state;
  return typeof readyState === "number" ? readyState : null;
}

function socketOpen() {
  return socketReadyState() === WebSocket.OPEN;
}

function socketConnecting() {
  if (!connection.game) {
    return false;
  }
  const readyState = socketReadyState();
  return readyState === null || readyState === WebSocket.CONNECTING || readyState === WebSocket.CLOSING;
}

function socketReconnectScheduled() {
  return Boolean(clientDebug()?.reconnect_scheduled);
}

function socketSynced() {
  return Boolean(clientDebug()?.is_synced || connection.synced);
}

function syncConnectionStatus() {
  if (!connection.game) {
    ui.status = "idle";
    return;
  }
  if (socketOpen()) {
    ui.status = socketSynced() ? "live" : "syncing";
    if (ui.status === "live") {
      ui.error = "";
    }
    return;
  }
  if (socketConnecting() || socketReconnectScheduled()) {
    ui.status = "syncing";
    return;
  }
  ui.status = "offline";
}

function getOrCreateUid() {
  const existing = window.sessionStorage.getItem(STORAGE.uid);
  if (existing) {
    return Number(existing) >>> 0;
  }
  const next = Math.floor(Math.random() * 0xffffffff) >>> 0;
  window.sessionStorage.setItem(STORAGE.uid, String(next));
  return next;
}

function getLevelMap(level) {
  const index = Math.min(10, Math.max(1, level >>> 0)) - 1;
  return MAPS[index];
}

function makeSlot(slotId, colorIndex, pos) {
  return {
    occupied: false,
    occupant: 0,
    occupantName: "",
    pos: { x: pos.x >>> 0, y: pos.y >>> 0 },
    shape: slotId === 1 ? "square" : "circle",
    colorIndex: colorIndex >>> 0,
    victoryReady: false,
  };
}

function makeInitialState() {
  const map = getLevelMap(1);
  return {
    tick: 0,
    phase: PHASE.LOBBY,
    currentLevel: 1,
    people: [],
    slot1: makeSlot(1, 0, map.spawn1),
    slot2: makeSlot(2, 1, map.spawn2),
    chat: [],
    currentRunStart: 0,
    levelStart: 0,
    splitTimes: Array(10).fill(0),
    bestLevelTimes: Array(10).fill(0),
    bestTotalTime: 0,
    bestTotalDone: 0,
  };
}

function cloneState(state) {
  return JSON.parse(JSON.stringify(state));
}

function pushSystem(state, text) {
  if (!text) return;
  state.chat.push({
    kind: "system",
    name: SYSTEM_NAME,
    text,
    tick: state.tick,
  });
  trimChat(state);
}

function pushChat(state, name, text) {
  const clean = text.trim();
  if (!clean) return;
  state.chat.push({
    kind: "user",
    name,
    text: clean,
    tick: state.tick,
  });
  trimChat(state);
}

function trimChat(state) {
  if (state.chat.length > CHAT_LIMIT) {
    state.chat = state.chat.slice(-CHAT_LIMIT);
  }
}

function findPerson(state, uid) {
  return state.people.find((person) => person.uid === (uid >>> 0)) ?? null;
}

function slotNameForUid(state, uid) {
  const id = uid >>> 0;
  if (state.slot1.occupied && state.slot1.occupant === id) return "slot1";
  if (state.slot2.occupied && state.slot2.occupant === id) return "slot2";
  return null;
}

function slotRole(slotName) {
  return slotName === "slot1" ? "p1" : "p2";
}

function occupySlot(slot, person, options = {}) {
  const colorIndex = options.colorIndex ?? slot.colorIndex;
  const pos = options.pos ?? slot.pos;
  return {
    ...slot,
    occupied: true,
    occupant: person.uid >>> 0,
    occupantName: person.name,
    pos: { x: pos.x >>> 0, y: pos.y >>> 0 },
    colorIndex: colorIndex >>> 0,
    victoryReady: false,
  };
}

function clearSlot(slot) {
  return {
    ...slot,
    occupied: false,
    occupant: 0,
    occupantName: "",
    victoryReady: false,
  };
}

function nextColor(index) {
  return ((index >>> 0) + 1) % COLOR_NAMES.length;
}

function readyQueue(state) {
  return state.people.filter((person) => person.online && person.ready);
}

function readyWatchers(state) {
  const taken = new Set();
  if (state.slot1.occupied) taken.add(state.slot1.occupant);
  if (state.slot2.occupied) taken.add(state.slot2.occupant);
  return state.people.filter((person) => person.online && person.ready && !taken.has(person.uid));
}

function resetLobbySlots(state) {
  const map = getLevelMap(1);
  const ready = readyQueue(state);
  state.slot1 = ready[0] ? occupySlot(makeSlot(1, 0, map.spawn1), ready[0]) : makeSlot(1, 0, map.spawn1);
  state.slot2 = ready[1] ? occupySlot(makeSlot(2, 1, map.spawn2), ready[1]) : makeSlot(2, 1, map.spawn2);
}

function startMatch(state) {
  if (!state.slot1.occupied || !state.slot2.occupied) return;
  const map = getLevelMap(1);
  state.phase = PHASE.PLAYING;
  state.currentLevel = 1;
  state.currentRunStart = state.tick;
  state.levelStart = state.tick;
  state.splitTimes = Array(10).fill(0);
  state.slot1 = { ...state.slot1, pos: { ...map.spawn1 }, victoryReady: false };
  state.slot2 = { ...state.slot2, pos: { ...map.spawn2 }, victoryReady: false };
  pushSystem(state, `${state.slot1.occupantName} e ${state.slot2.occupantName} iniciaram o level 1.`);
}

function maybeStartLobby(state) {
  if (state.phase !== PHASE.LOBBY) return;
  resetLobbySlots(state);
  if (state.slot1.occupied && state.slot2.occupied) {
    startMatch(state);
  }
}

function returnToLobby(state, reason) {
  if (reason) {
    pushSystem(state, reason);
  }
  const map = getLevelMap(1);
  state.phase = PHASE.LOBBY;
  state.currentLevel = 1;
  state.currentRunStart = state.tick;
  state.levelStart = state.tick;
  state.splitTimes = Array(10).fill(0);
  state.people = state.people.map((person) => ({ ...person, ready: 0 }));
  state.slot1 = makeSlot(1, 0, map.spawn1);
  state.slot2 = makeSlot(2, 1, map.spawn2);
}

function refillSlots(state) {
  if (state.phase === PHASE.LOBBY) return;
  const candidates = readyWatchers(state);
  for (const slotName of ["slot1", "slot2"]) {
    if (!state[slotName].occupied) {
      const next = candidates.shift();
      if (!next) continue;
      const slot = state[slotName];
      state[slotName] = occupySlot(slot, next, {
        colorIndex: nextColor(slot.colorIndex),
        pos: slot.pos,
      });
      pushSystem(state, `${next.name} assumiu ${slotRole(slotName)} na fase atual.`);
    }
  }
  if (!state.slot1.occupied && !state.slot2.occupied) {
    returnToLobby(state, "Todos os jogadores ativos sairam. Lobby reaberto.");
  }
}

function maybeTimeoutPlayers(state) {
  let changed = false;
  for (const person of state.people) {
    if (!person.online) continue;
    if ((state.tick - person.lastSeen) <= PRESENCE_TIMEOUT_TICKS) continue;
    person.online = 0;
    person.ready = 0;
    changed = true;
    pushSystem(state, `${person.name} ficou offline por timeout.`);
    const slotName = slotNameForUid(state, person.uid);
    if (slotName) {
      state[slotName] = clearSlot(state[slotName]);
    }
  }
  if (!changed) return;
  if (state.phase === PHASE.LOBBY) {
    maybeStartLobby(state);
  } else {
    refillSlots(state);
  }
}

function recordLevelTime(state, levelTime) {
  const index = state.currentLevel - 1;
  state.splitTimes[index] = levelTime;
  const best = state.bestLevelTimes[index];
  if (best === 0 || levelTime < best) {
    state.bestLevelTimes[index] = levelTime;
  }
}

function completeLevel(state) {
  const levelTime = Math.max(0, state.tick - state.levelStart);
  recordLevelTime(state, levelTime);
  state.slot1.victoryReady = false;
  state.slot2.victoryReady = false;
  if (state.currentLevel === 10) {
    const totalTime = Math.max(0, state.tick - state.currentRunStart);
    if (state.bestTotalTime === 0 || totalTime < state.bestTotalTime) {
      state.bestTotalTime = totalTime;
      state.bestTotalDone = 1;
    }
    state.phase = PHASE.CAMPAIGN_END;
    pushSystem(state, `Campanha concluida em ${formatTicks(totalTime)}.`);
    return;
  }
  state.phase = PHASE.STAGE_CLEAR;
  pushSystem(state, `Level ${state.currentLevel} vencido em ${formatTicks(levelTime)}.`);
}

function startNextLevel(state) {
  state.currentLevel += 1;
  const map = getLevelMap(state.currentLevel);
  state.phase = PHASE.PLAYING;
  state.levelStart = state.tick;
  state.slot1 = { ...state.slot1, pos: { ...map.spawn1 }, victoryReady: false };
  state.slot2 = { ...state.slot2, pos: { ...map.spawn2 }, victoryReady: false };
  pushSystem(state, `Level ${state.currentLevel} iniciado.`);
}

function bothOnOwnExits(state) {
  if (!state.slot1.occupied || !state.slot2.occupied) return false;
  const map = getLevelMap(state.currentLevel);
  return (
    state.slot1.pos.x === map.exit1.x &&
    state.slot1.pos.y === map.exit1.y &&
    state.slot2.pos.x === map.exit2.x &&
    state.slot2.pos.y === map.exit2.y
  );
}

function bothVictoryReady(state) {
  return state.slot1.occupied && state.slot2.occupied && state.slot1.victoryReady && state.slot2.victoryReady;
}

function isWalkable(map, x, y) {
  if (x < 0 || y < 0 || y >= map.floor.length || x >= map.floor[0].length) {
    return false;
  }
  return map.floor[y][x] !== 1;
}

function applyMove(state, uid, dir) {
  if (state.phase !== PHASE.PLAYING) return;
  const slotName = slotNameForUid(state, uid);
  if (!slotName) return;
  const map = getLevelMap(state.currentLevel);
  const slot = state[slotName];
  let nx = slot.pos.x;
  let ny = slot.pos.y;
  if (dir === DIR.UP && ny > 0) ny -= 1;
  if (dir === DIR.DOWN && ny < map.floor.length - 1) ny += 1;
  if (dir === DIR.LEFT && nx > 0) nx -= 1;
  if (dir === DIR.RIGHT && nx < map.floor[0].length - 1) nx += 1;
  if (!isWalkable(map, nx, ny)) return;
  slot.pos = { x: nx >>> 0, y: ny >>> 0 };
  if (bothOnOwnExits(state)) {
    completeLevel(state);
  }
}

function handleVictoryReady(state, uid) {
  if (state.phase !== PHASE.STAGE_CLEAR && state.phase !== PHASE.CAMPAIGN_END) return;
  const slotName = slotNameForUid(state, uid);
  if (!slotName) return;
  state[slotName].victoryReady = true;
  if (!bothVictoryReady(state)) return;
  if (state.phase === PHASE.STAGE_CLEAR) {
    startNextLevel(state);
    return;
  }
  returnToLobby(state, "Campanha encerrada. Room voltou ao lobby.");
}

function handleJoin(state, post) {
  const uid = post.uid >>> 0;
  const name = post.user;
  let person = findPerson(state, uid);
  const wasOffline = !person || !person.online;
  if (!person) {
    person = {
      uid,
      name,
      online: 1,
      ready: 0,
      lastSeen: state.tick,
    };
    state.people.push(person);
  } else {
    person.name = name;
    person.online = 1;
    person.lastSeen = state.tick;
  }
  if (wasOffline) {
    pushSystem(state, `${name} entrou na room.`);
  }
  if (state.phase === PHASE.LOBBY) {
    maybeStartLobby(state);
  } else {
    refillSlots(state);
  }
}

function handleHeartbeat(state, post) {
  const person = findPerson(state, post.uid);
  if (!person) return;
  person.online = 1;
  person.lastSeen = state.tick;
}

function handleLeave(state, post) {
  const person = findPerson(state, post.uid);
  if (!person) return;
  const slotName = slotNameForUid(state, post.uid);
  const active = person.online || person.ready || slotName;
  person.online = 0;
  person.ready = 0;
  if (!active) return;
  pushSystem(state, `${person.name} saiu da room.`);
  if (slotName) {
    state[slotName] = clearSlot(state[slotName]);
  }
  if (state.phase === PHASE.LOBBY) {
    maybeStartLobby(state);
  } else {
    refillSlots(state);
  }
}

function handleReady(state, uid, readyValue) {
  const person = findPerson(state, uid);
  if (!person) return;
  person.ready = readyValue ? 1 : 0;
  pushSystem(state, readyValue ? `${person.name} ficou ready.` : `${person.name} saiu do ready.`);
  if (state.phase === PHASE.LOBBY) {
    maybeStartLobby(state);
  }
}

function onTick(previous) {
  const state = cloneState(previous);
  state.tick += 1;
  maybeTimeoutPlayers(state);
  if (state.phase === PHASE.PLAYING && bothOnOwnExits(state)) {
    completeLevel(state);
  }
  return state;
}

function onPost(post, previous) {
  const state = cloneState(previous);
  switch (post.$) {
    case "join":
      handleJoin(state, post);
      break;
    case "heartbeat":
      handleHeartbeat(state, post);
      break;
    case "leave":
      handleLeave(state, post);
      break;
    case "ready":
      handleReady(state, post.uid, true);
      break;
    case "unready":
      handleReady(state, post.uid, false);
      break;
    case "chat":
      pushChat(state, post.name, post.text);
      break;
    case "move":
      applyMove(state, post.uid, post.dir >>> 0);
      break;
    case "victory_ready":
      handleVictoryReady(state, post.uid);
      break;
    default:
      break;
  }
  return state;
}

function sanitizeUser(value) {
  return value.trim().slice(0, 24);
}

function sanitizeRoom(value) {
  return value.trim().toLowerCase().replace(/\s+/g, "-").slice(0, 48);
}

function connectRoom() {
  const room = sanitizeRoom(ui.roomInput);
  const user = sanitizeUser(ui.userInput);
  if (!room || !user) {
    ui.error = "Informe usuario e sala.";
    render();
    return;
  }
  disconnectRoom(false);
  ui.error = "";
  ui.status = "syncing";
  ui.userInput = user;
  ui.roomInput = room;
  window.localStorage.setItem(STORAGE.user, user);
  window.localStorage.setItem(STORAGE.room, room);
  latestState = makeInitialState();
  const game = new VibiNet.game({
    room,
    initial: makeInitialState(),
    on_tick: onTick,
    on_post: onPost,
    packer: POST_PACKER,
    tick_rate: TICK_RATE,
    tolerance: TOLERANCE_MS,
  });
  connection.game = game;
  connection.room = room;
  connection.user = user;
  connection.synced = false;
  connection.renderTimer = window.setInterval(render, RENDER_MS);
  game.on_sync(() => {
    if (connection.game !== game) return;
    connection.synced = true;
    ui.status = "live";
    ui.error = "";
    postNet({ $: "join", uid: ui.uid, user });
    postNet({ $: "heartbeat", uid: ui.uid });
    connection.heartbeatTimer = window.setInterval(() => {
      postNet({ $: "heartbeat", uid: ui.uid });
    }, HEARTBEAT_MS);
    render();
  });
  render();
}

function disconnectRoom(sendLeave = true) {
  const game = connection.game;
  if (!game) {
    ui.status = "idle";
    return;
  }
  if (sendLeave && connection.synced) {
    try {
      game.post({ $: "leave", uid: ui.uid });
    } catch {
    }
  }
  if (connection.renderTimer !== null) {
    window.clearInterval(connection.renderTimer);
  }
  if (connection.heartbeatTimer !== null) {
    window.clearInterval(connection.heartbeatTimer);
  }
  connection.renderTimer = null;
  connection.heartbeatTimer = null;
  connection.game = null;
  connection.synced = false;
  connection.room = "";
  connection.user = "";
  ui.status = "idle";
  ui.error = "";
  latestState = makeInitialState();
  window.setTimeout(() => {
    try {
      game.close?.();
    } catch {
    }
    try {
      game.client_api?.close?.();
    } catch {
    }
  }, sendLeave ? 120 : 0);
}

function postNet(message) {
  if (!connection.game || !connection.synced) return;
  try {
    connection.game.post(message);
  } catch (error) {
    const retrying = socketConnecting() || socketReconnectScheduled();
    ui.status = retrying ? "syncing" : "offline";
    ui.error = retrying
      ? "Conexao oscilando. O VibiNet esta tentando reconectar."
      : error instanceof Error
        ? error.message
        : "Falha ao postar no VibiNet.";
    render();
  }
}

function getCurrentState() {
  if (!connection.game) return latestState;
  try {
    latestState = connection.game.compute_current_state();
  } catch {
  }
  return latestState;
}

function currentPerson(state) {
  return findPerson(state, ui.uid);
}

function currentRole(state) {
  const slotName = slotNameForUid(state, ui.uid);
  if (!slotName) return "watching";
  const slot = state[slotName];
  return `${slotRole(slotName)} / ${COLOR_NAMES[slot.colorIndex]}`;
}

function canMoveFromKey(event) {
  const target = event.target;
  if (
    target instanceof HTMLInputElement ||
    target instanceof HTMLTextAreaElement ||
    target instanceof HTMLSelectElement
  ) {
    return false;
  }
  return true;
}

function moveFromKey(key) {
  switch (key) {
    case "w":
    case "ArrowUp":
      return DIR.UP;
    case "s":
    case "ArrowDown":
      return DIR.DOWN;
    case "a":
    case "ArrowLeft":
      return DIR.LEFT;
    case "d":
    case "ArrowRight":
      return DIR.RIGHT;
    default:
      return null;
  }
}

function formatTicks(ticks) {
  const totalSeconds = Math.floor((ticks >>> 0) / TICK_RATE);
  const minutes = Math.floor(totalSeconds / 60);
  const seconds = totalSeconds % 60;
  const tenths = Math.floor(((ticks >>> 0) % TICK_RATE) * (10 / TICK_RATE));
  return `${String(minutes).padStart(2, "0")}:${String(seconds).padStart(2, "0")}.${tenths}`;
}

function connectionLabel() {
  if (!connection.game) return "idle";
  if (socketOpen() && socketSynced()) return "live";
  if (socketConnecting() || socketReconnectScheduled() || ui.status === "syncing") return "syncing";
  return "offline";
}

function pingText() {
  if (!connection.game || !socketOpen() || !socketSynced()) return "--";
  const ping = connection.game.ping();
  if (!Number.isFinite(ping)) return "--";
  return `${Math.max(0, Math.round(ping))}ms`;
}

function roleTextForPerson(person, state) {
  if (state.slot1.occupied && state.slot1.occupant === person.uid) {
    return `p1 / ${COLOR_NAMES[state.slot1.colorIndex]}`;
  }
  if (state.slot2.occupied && state.slot2.occupant === person.uid) {
    return `p2 / ${COLOR_NAMES[state.slot2.colorIndex]}`;
  }
  return "watching";
}

function readyLabel(state) {
  return currentPerson(state)?.ready ? "Unready" : "Ready";
}

function readyList(state) {
  return state.people.filter((person) => person.ready && person.online);
}

function renderCell(map, state, x, y) {
  const classes = ["cell"];
  if (map.floor[y][x] === 1) classes.push("wall");
  if (map.exit1.x === x && map.exit1.y === y) classes.push("exit-one");
  if (map.exit2.x === x && map.exit2.y === y) classes.push("exit-two");
  const tokens = [];
  if (state.slot1.occupied && state.slot1.pos.x === x && state.slot1.pos.y === y) {
    tokens.push(`<div class="token ${state.slot1.shape} c${state.slot1.colorIndex}"></div>`);
  }
  if (state.slot2.occupied && state.slot2.pos.x === x && state.slot2.pos.y === y) {
    tokens.push(`<div class="token alt ${state.slot2.shape} c${state.slot2.colorIndex}"></div>`);
  }
  return `<div class="${classes.join(" ")}">${tokens.join("")}</div>`;
}

function renderBoard(state) {
  const map = getLevelMap(state.currentLevel);
  return `
    <div class="board-frame">
      <div class="board">
        ${map.floor
          .map(
            (row, y) => `
              <div class="board-row">
                ${row.map((_, x) => renderCell(map, state, x, y)).join("")}
              </div>
            `
          )
          .join("")}
      </div>
    </div>
  `;
}

function renderPeople(state) {
  if (state.people.length === 0) {
    return `<div class="empty">Sem pessoas conectadas.</div>`;
  }
  return `
    <div class="stack">
      ${state.people
        .map(
          (person) => `
            <div class="person-card ${person.online ? "online" : "offline"}">
              <div class="person-name">${escapeHtml(person.name)}</div>
              <div class="person-meta">${escapeHtml(roleTextForPerson(person, state))} / ${person.online ? "online" : "offline"} / ${person.ready ? "ready" : "idle"}</div>
            </div>
          `
        )
        .join("")}
    </div>
  `;
}

function renderChat(state) {
  if (state.chat.length === 0) {
    return `<div class="empty">Sem mensagens ainda.</div>`;
  }
  return `
    <div class="chat-box">
      ${state.chat
        .map(
          (entry) => `
            <div class="chat-line ${entry.kind}">
              <span class="chat-name">${escapeHtml(entry.name)}:</span>
              <span>${escapeHtml(entry.text)}</span>
            </div>
          `
        )
        .join("")}
    </div>
  `;
}

function renderSplits(state) {
  const rows = Array.from({ length: 10 }, (_, index) => {
    const current = state.splitTimes[index];
    const best = state.bestLevelTimes[index];
    return `
      <div class="split-row">
        <div>lv${String(index + 1).padStart(2, "0")}</div>
        <div>${current ? formatTicks(current) : "--"}</div>
        <div>${best ? formatTicks(best) : "--"}</div>
      </div>
    `;
  }).join("");
  return `
    <div class="split-list">
      <div class="split-row head">
        <div>fase</div>
        <div>run</div>
        <div>record</div>
      </div>
      ${rows}
    </div>
  `;
}

function renderLobbyQueue(state) {
  const ready = readyList(state);
  if (ready.length === 0) {
    return `<div class="empty">Ninguem ready ainda.</div>`;
  }
  return `
    <div class="stack">
      ${ready
        .map(
          (person, index) => `
            <div class="person-card">
              <div class="person-name">#${index + 1} ${escapeHtml(person.name)}</div>
              <div class="person-meta">${index < 2 ? "entra na partida" : "watching na fila"} / ${escapeHtml(roleTextForPerson(person, state))}</div>
            </div>
          `
        )
        .join("")}
    </div>
  `;
}

function renderOverlay(state) {
  const slotName = slotNameForUid(state, ui.uid);
  const canReady = Boolean(slotName);
  if (state.phase === PHASE.STAGE_CLEAR) {
    return `
      <div class="overlay">
        <div class="overlay-card">
          <div class="eyebrow">Fase vencida</div>
          <h2>Os dois precisam confirmar para seguir.</h2>
          <p>Quem ficou watching continua no chat. Se uma vaga abrir, o proximo watcher ready entra no lugar e na fase atual.</p>
          ${renderSplits(state)}
          <div class="button-row">
            ${canReady ? `<button class="button" data-action="victory-ready">Ready</button>` : `<div class="overlay-note">Aguardando os players ativos.</div>`}
            <button class="button-secondary" data-action="leave-room">Leave</button>
          </div>
        </div>
      </div>
    `;
  }
  if (state.phase === PHASE.CAMPAIGN_END) {
    return `
      <div class="overlay">
        <div class="overlay-card">
          <div class="eyebrow">Campanha concluida</div>
          <h2>Room fechou os 10 levels.</h2>
          <p>Total desta run: ${formatTicks(Math.max(0, state.tick - state.currentRunStart))}. Melhor total da room: ${state.bestTotalTime ? formatTicks(state.bestTotalTime) : "--"}.</p>
          ${renderSplits(state)}
          <div class="button-row">
            ${canReady ? `<button class="button" data-action="victory-ready">Voltar ao lobby</button>` : `<div class="overlay-note">Aguardando os players ativos.</div>`}
            <button class="button-secondary" data-action="leave-room">Leave</button>
          </div>
        </div>
      </div>
    `;
  }
  return "";
}

function renderSetup() {
  return `
    <div class="page">
      <section class="setup">
        <article class="hero">
          <div class="eyebrow">Online Multiplayer</div>
          <h1 class="display">Vibi DuoPuzzle</h1>
          <p class="copy">Welcome. Entra na sala, escolhe tua dupla e tenta fechar os 10 levels no menor tempo possivel.</p>
          <div class="rule">Dois jogam, o resto acompanha no lobby, conversa no chat e pode assumir vaga quando ela abrir.</div>
        </article>
        <form class="card" data-form="join">
          <div class="eyebrow">Entrar</div>
          <label class="field">
            <span>Usuario</span>
            <input class="input" name="user" value="${escapeAttr(ui.userInput)}" placeholder="Seu nome" autocomplete="off" />
          </label>
          <label class="field">
            <span>Sala</span>
            <input class="input" name="room" value="${escapeAttr(ui.roomInput)}" placeholder="Nome da room" autocomplete="off" />
          </label>
          <div class="button-row">
            <button class="button" type="submit">Entrar</button>
          </div>
          <div class="status-note">Status: ${connectionLabel()}</div>
          ${ui.error ? `<div class="error">${escapeHtml(ui.error)}</div>` : ""}
        </form>
      </section>
    </div>
  `;
}

function renderConnected(state) {
  const map = getLevelMap(state.currentLevel);
  const levelTime = Math.max(0, state.tick - state.levelStart);
  const runTime = Math.max(0, state.tick - state.currentRunStart);
  const bestLevel = state.bestLevelTimes[state.currentLevel - 1];
  return `
    <div class="page">
      <div class="status-bar">
        <div class="status-note">Sala ${escapeHtml(connection.room)} / ${escapeHtml(connection.user)} / ${escapeHtml(currentRole(state))}</div>
        <div class="chips">
          ${renderChip("Conexao", connectionLabel())}
          ${renderChip("Ping", pingText())}
          ${renderChip("Level", `lv${String(state.currentLevel).padStart(2, "0")}`)}
          ${renderChip("Run", formatTicks(runTime))}
        </div>
      </div>
      <section class="shell">
        <div class="column">
          <div class="game-panel">
            <div class="eyebrow">${escapeHtml(map.title)}</div>
            <h1>${escapeHtml(state.phase === PHASE.LOBBY ? "Lobby" : `Level ${state.currentLevel}`)}</h1>
            <div class="chips">
              ${renderChip("Tempo", formatTicks(levelTime))}
              ${renderChip("Record", bestLevel ? formatTicks(bestLevel) : "--")}
              ${renderChip("Ativos", `${state.slot1.occupied ? 1 : 0} + ${state.slot2.occupied ? 1 : 0}`)}
            </div>
            ${state.phase === PHASE.LOBBY ? renderLobbyBanner(state) : renderBoard(state)}
            <div class="legend">
              <div class="legend-item">P1 quadrado</div>
              <div class="legend-item">P2 circulo</div>
              <div class="legend-item">WASD ou setas</div>
              <div class="legend-item">Exit azul para p1</div>
              <div class="legend-item">Exit verde para p2</div>
            </div>
            ${renderOverlay(state)}
          </div>
        </div>
        <div class="column">
          <div class="panel">
            <div class="panel-title">Pessoas</div>
            ${renderPeople(state)}
          </div>
          <div class="panel">
            <div class="panel-title">Chat</div>
            ${renderChat(state)}
            <form class="chat-form" data-form="chat">
              <input class="input" name="chat" value="${escapeAttr(ui.chatInput)}" placeholder="Escreva algo..." autocomplete="off" />
              <button class="button" type="submit">Send</button>
            </form>
          </div>
          <div class="panel">
            <div class="panel-title">Room</div>
            <div class="button-row">
              <button class="button" type="button" data-action="toggle-ready">${escapeHtml(readyLabel(state))}</button>
              <button class="button-secondary" type="button" data-action="leave-room">Leave</button>
            </div>
            ${renderSplits(state)}
            <div class="footer-note">Watching pode ficar ready. Se um player sair, o primeiro watcher ready assume a vaga na fase atual.</div>
          </div>
        </div>
      </section>
    </div>
  `;
}

function renderLobbyBanner(state) {
  return `
    <div class="card">
      <div class="eyebrow">Lobby ativo</div>
      <p class="copy">O lobby mostra quem ficou ready e em que ordem a fila entra. Os dois primeiros jogam. O resto fica watching e pode assumir vaga durante o match.</p>
      <div class="chips">
        ${renderChip("Ready", String(state.people.filter((person) => person.ready).length))}
        ${renderChip("Online", String(state.people.filter((person) => person.online).length))}
        ${renderChip("Record total", state.bestTotalTime ? formatTicks(state.bestTotalTime) : "--")}
      </div>
      ${renderLobbyQueue(state)}
    </div>
  `;
}

function renderChip(label, value) {
  return `
    <div class="chip">
      <div class="chip-label">${escapeHtml(label)}</div>
      <div class="chip-value">${escapeHtml(value)}</div>
    </div>
  `;
}

function escapeHtml(value) {
  return String(value)
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;");
}

function escapeAttr(value) {
  return escapeHtml(value).replaceAll("'", "&#39;");
}

function render() {
  syncConnectionStatus();
  const state = getCurrentState();
  root.innerHTML = connection.game ? renderConnected(state) : renderSetup();
}

root.addEventListener("input", (event) => {
  const target = event.target;
  if (!(target instanceof HTMLInputElement)) return;
  if (target.name === "user") ui.userInput = target.value;
  if (target.name === "room") ui.roomInput = target.value;
  if (target.name === "chat") ui.chatInput = target.value;
});

root.addEventListener("submit", (event) => {
  const form = event.target;
  if (!(form instanceof HTMLFormElement)) return;
  event.preventDefault();
  if (form.dataset.form === "join") {
    connectRoom();
    return;
  }
  if (form.dataset.form === "chat") {
    const text = ui.chatInput.trim();
    if (!text) return;
    postNet({
      $: "chat",
      uid: ui.uid,
      name: connection.user,
      text,
    });
    ui.chatInput = "";
    render();
  }
});

root.addEventListener("click", (event) => {
  const target = event.target;
  if (!(target instanceof HTMLElement)) return;
  const action = target.closest("[data-action]");
  if (!action) return;
  const state = getCurrentState();
  switch (action.dataset.action) {
    case "toggle-ready": {
      const me = currentPerson(state);
      if (!me) return;
      postNet({ $: me.ready ? "unready" : "ready", uid: ui.uid });
      break;
    }
    case "leave-room":
      disconnectRoom(true);
      render();
      break;
    case "victory-ready":
      postNet({ $: "victory_ready", uid: ui.uid });
      break;
    default:
      break;
  }
});

window.addEventListener("keydown", (event) => {
  if (!connection.game || !connection.synced || !canMoveFromKey(event)) return;
  const dir = moveFromKey(event.key);
  if (dir === null) return;
  const state = getCurrentState();
  if (state.phase !== PHASE.PLAYING) return;
  if (!slotNameForUid(state, ui.uid)) return;
  event.preventDefault();
  postNet({ $: "move", uid: ui.uid, dir });
});

window.addEventListener("pagehide", () => {
  if (!connection.game || !connection.synced) return;
  try {
    connection.game.post({ $: "leave", uid: ui.uid });
  } catch {
  }
  try {
    connection.game.close?.();
  } catch {
  }
  try {
    connection.game.client_api?.close?.();
  } catch {
  }
});

render();
