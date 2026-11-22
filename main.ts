// Push-optimal Sokoban solver for make.fun sokoban-solver-01.
// Levels are a hallway + 1–4 rooms (3–4 boxes each). Solve rooms one by one
// with push-optimal A*, forbidding pushes into the hallway.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

const DIRS: [number, number, string][] = [
  [0, -1, 'u'],
  [0, 1, 'd'],
  [-1, 0, 'l'],
  [1, 0, 'r'],
];

type Level = {
  w: number;
  h: number;
  wall: Uint8Array;
  goals: number[];
  boxes: number[];
  player: number;
  goalSet: Set<number>;
};

function parse(text: string): Level {
  const rows = text.replace(/\r/g, '').split('\n').filter((r) => r.length > 0);
  const h = rows.length;
  const w = Math.max(...rows.map((r) => r.length));
  const wall = new Uint8Array(w * h);
  const goals: number[] = [];
  const boxes: number[] = [];
  let player = -1;
  for (let y = 0; y < h; y++) {
    const row = rows[y]!;
    for (let x = 0; x < w; x++) {
      const ch = row[x] ?? '#';
      const i = y * w + x;
      if (ch === '#') wall[i] = 1;
      if (ch === '.' || ch === '*' || ch === '+') goals.push(i);
      if (ch === '$' || ch === '*') boxes.push(i);
      if (ch === '@' || ch === '+') player = i;
    }
  }
  boxes.sort((a, b) => a - b);
  return { w, h, wall, goals, boxes, player, goalSet: new Set(goals) };
}

function idx(l: Level, x: number, y: number): number {
  return y * l.w + x;
}
function xy(l: Level, i: number): [number, number] {
  return [i % l.w, (i / l.w) | 0];
}

/** Squares from which a lone box can never reach a goal. */
function deadSquares(l: Level): Uint8Array {
  const n = l.w * l.h;
  const dead = new Uint8Array(n);
  dead.fill(1);
  const seen = new Uint8Array(n);
  const q: number[] = [];
  for (const g of l.goals) {
    dead[g] = 0;
    seen[g] = 1;
    q.push(g);
  }
  while (q.length) {
    const s = q.pop()!;
    for (const [dx, dy] of DIRS) {
      const [x, y] = xy(l, s);
      const fx = x - dx;
      const fy = y - dy;
      const pbx = x - 2 * dx;
      const pby = y - 2 * dy;
      if (fx < 0 || fy < 0 || fx >= l.w || fy >= l.h) continue;
      if (pbx < 0 || pby < 0 || pbx >= l.w || pby >= l.h) continue;
      const from = idx(l, fx, fy);
      const pb = idx(l, pbx, pby);
      if (l.wall[from] || l.wall[pb]) continue;
      if (!seen[from]) {
        seen[from] = 1;
        dead[from] = 0;
        q.push(from);
      }
    }
  }
  for (let i = 0; i < n; i++) if (l.wall[i]) dead[i] = 1;
  return dead;
}

function isDeadlock(l: Level, boxes: number[], dead: Uint8Array): boolean {
  for (const b of boxes) {
    if (l.goalSet.has(b)) continue;
    if (dead[b]) return true;
    const [x, y] = xy(l, b);
    const U = y > 0 && l.wall[idx(l, x, y - 1)] === 1;
    const D = y + 1 < l.h && l.wall[idx(l, x, y + 1)] === 1;
    const L = x > 0 && l.wall[idx(l, x - 1, y)] === 1;
    const R = x + 1 < l.w && l.wall[idx(l, x + 1, y)] === 1;
    if ((U || D) && (L || R)) return true;
  }
  return false;
}

function packBoxes(boxes: number[]): string {
  return boxes.join(',');
}

function walkPath(l: Level, from: number, to: number, boxSet: Set<number>): string | null {
  if (from === to) return '';
  const n = l.w * l.h;
  const prev = new Int32Array(n).fill(-1);
  const step = new Array<string>(n);
  const q: number[] = [from];
  prev[from] = from;
  for (let qi = 0; qi < q.length; qi++) {
    const p = q[qi]!;
    for (const [dx, dy, letter] of DIRS) {
      const [x, y] = xy(l, p);
      const nx = x + dx;
      const ny = y + dy;
      if (nx < 0 || ny < 0 || nx >= l.w || ny >= l.h) continue;
      const ni = idx(l, nx, ny);
      if (prev[ni] !== -1 || l.wall[ni] || boxSet.has(ni)) continue;
      prev[ni] = p;
      step[ni] = letter;
      if (ni === to) {
        let s = '';
        for (let t = to; t !== from; t = prev[t]!) s = step[t]! + s;
        return s;
      }
      q.push(ni);
    }
  }
  return null;
}

function heuristic(l: Level, boxes: number[]): number {
  const used = new Uint8Array(l.goals.length);
  let sum = 0;
  for (const b of boxes) {
    let best = 1e9;
    let bi = -1;
    for (let i = 0; i < l.goals.length; i++) {
      if (used[i]) continue;
      const g = l.goals[i]!;
      const d = Math.abs((g % l.w) - (b % l.w)) + Math.abs(((g / l.w) | 0) - ((b / l.w) | 0));
      if (d < best) {
        best = d;
        bi = i;
      }
    }
    if (bi >= 0) {
      used[bi] = 1;
      sum += best;
    }
  }
  return sum;
}

type PushNode = { boxes: number[]; player: number; g: number; parent: number; walk: string };

function areaKey(l: Level, player: number, boxes: number[]): number {
  const boxSet = new Set(boxes);
  const n = l.w * l.h;
  const seen = new Uint8Array(n);
  const q: number[] = [player];
  seen[player] = 1;
  let min = player;
  for (let qi = 0; qi < q.length; qi++) {
    const p = q[qi]!;
    if (p < min) min = p;
    for (const [dx, dy] of DIRS) {
      const [x, y] = xy(l, p);
      const nx = x + dx;
      const ny = y + dy;
      if (nx < 0 || ny < 0 || nx >= l.w || ny >= l.h) continue;
      const ni = idx(l, nx, ny);
      if (seen[ni] || l.wall[ni] || boxSet.has(ni)) continue;
      seen[ni] = 1;
      q.push(ni);
    }
  }
  return min;
}

/** Push-optimal A*. Optional forbid: refuse box destinations in this set. */
function solvePushOptimal(
  l: Level,
  opts: { forbid?: Set<number>; maxExpansions?: number } = {},
): string {
  const maxExpansions = opts.maxExpansions ?? 400_000;
  const forbid = opts.forbid ?? new Set<number>();
  const dead = deadSquares(l);
  for (const f of forbid) if (!l.goalSet.has(f)) dead[f] = 1;
  if (l.boxes.every((b) => l.goalSet.has(b))) return '';
  if (isDeadlock(l, l.boxes, dead)) return '';

  const nodes: PushNode[] = [{ boxes: l.boxes.slice(), player: l.player, g: 0, parent: -1, walk: '' }];
  const keyOf = (boxes: number[], player: number) => packBoxes(boxes) + '|' + areaKey(l, player, boxes);
  const best = new Map<string, number>([[keyOf(l.boxes, l.player), 0]]);
  type HeapItem = [number, number, number];
  const heap: HeapItem[] = [[heuristic(l, l.boxes), 0, 0]];
  const less = (a: HeapItem, b: HeapItem) =>
    a[0] < b[0] || (a[0] === b[0] && (a[1] < b[1] || (a[1] === b[1] && a[2] < b[2])));
  const hpush = (e: HeapItem) => {
    let i = heap.length;
    heap.push(e);
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (!less(heap[i]!, heap[p]!)) break;
      [heap[i], heap[p]] = [heap[p]!, heap[i]!];
      i = p;
    }
  };
  const hpop = (): HeapItem => {
    const top = heap[0]!;
    const last = heap.pop()!;
    if (heap.length) {
      heap[0] = last;
      for (let i = 0; ; ) {
        let c = 2 * i + 1;
        if (c >= heap.length) break;
        if (c + 1 < heap.length && less(heap[c + 1]!, heap[c]!)) c++;
        if (!less(heap[c]!, heap[i]!)) break;
        [heap[i], heap[c]] = [heap[c]!, heap[i]!];
        i = c;
      }
    }
    return top;
  };

  let expanded = 0;
  while (heap.length && expanded < maxExpansions) {
    const [, g, si] = hpop();
    const node = nodes[si]!;
    const k = keyOf(node.boxes, node.player);
    if (best.get(k) !== g) continue;
    if (node.boxes.every((b) => l.goalSet.has(b))) {
      let moves = '';
      for (let t = si; t > 0; t = nodes[t]!.parent) moves = nodes[t]!.walk + moves;
      return moves;
    }
    expanded++;
    const boxSet = new Set(node.boxes);
    const n = l.w * l.h;
    const reach = new Uint8Array(n);
    const rq: number[] = [node.player];
    reach[node.player] = 1;
    for (let qi = 0; qi < rq.length; qi++) {
      const p = rq[qi]!;
      for (const [dx, dy] of DIRS) {
        const [x, y] = xy(l, p);
        const nx = x + dx;
        const ny = y + dy;
        if (nx < 0 || ny < 0 || nx >= l.w || ny >= l.h) continue;
        const ni = idx(l, nx, ny);
        if (reach[ni] || l.wall[ni] || boxSet.has(ni)) continue;
        reach[ni] = 1;
        rq.push(ni);
      }
    }
    for (let bi = 0; bi < node.boxes.length; bi++) {
      const b = node.boxes[bi]!;
      for (const [dx, dy, letter] of DIRS) {
        const [x, y] = xy(l, b);
        const px = x - dx;
        const py = y - dy;
        const nx = x + dx;
        const ny = y + dy;
        if (px < 0 || py < 0 || px >= l.w || py >= l.h) continue;
        if (nx < 0 || ny < 0 || nx >= l.w || ny >= l.h) continue;
        const pi = idx(l, px, py);
        const dest = idx(l, nx, ny);
        if (!reach[pi] || l.wall[dest] || boxSet.has(dest)) continue;
        if (forbid.has(dest)) continue;
        const nb = node.boxes.slice();
        nb[bi] = dest;
        nb.sort((a, c) => a - c);
        if (isDeadlock(l, nb, dead)) continue;
        const ng = g + 1;
        const nk = keyOf(nb, b);
        const prevBest = best.get(nk);
        if (prevBest !== undefined && prevBest <= ng) continue;
        const path = walkPath(l, node.player, pi, boxSet);
        if (path === null) continue;
        best.set(nk, ng);
        const walk = path + letter.toUpperCase();
        nodes.push({ boxes: nb, player: b, g: ng, parent: si, walk });
        hpush([ng + heuristic(l, nb), ng, nodes.length - 1]);
      }
    }
  }
  return '';
}

function findHallwayRow(l: Level): number {
  const [, py] = xy(l, l.player);
  let open = 0;
  for (let x = 0; x < l.w; x++) if (!l.wall[idx(l, x, py)]) open++;
  if (open >= 3) return py;
  let best = py;
  let bestOpen = open;
  for (let y = 0; y < l.h; y++) {
    let o = 0;
    for (let x = 0; x < l.w; x++) if (!l.wall[idx(l, x, y)]) o++;
    if (o > bestOpen) {
      bestOpen = o;
      best = y;
    }
  }
  return best;
}

type Room = {
  cells: Set<number>;
  door: number;
  boxes: number[];
  goals: number[];
};

function findRooms(l: Level): { hallY: number; hallCells: Set<number>; rooms: Room[] } | null {
  const hallY = findHallwayRow(l);
  const hallCells = new Set<number>();
  for (let x = 0; x < l.w; x++) {
    const i = idx(l, x, hallY);
    if (!l.wall[i]) hallCells.add(i);
  }
  const rooms: Room[] = [];
  const visited = new Set<number>();
  for (let x = 1; x < l.w - 1; x++) {
    for (const dy of [-1, 1]) {
      const ry = hallY + dy;
      if (ry < 0 || ry >= l.h) continue;
      const door = idx(l, x, ry);
      const hall = idx(l, x, hallY);
      if (l.wall[door] || l.wall[hall] || visited.has(door)) continue;
      const cells = new Set<number>([door]);
      const q = [door];
      while (q.length) {
        const p = q.pop()!;
        const [px, py] = xy(l, p);
        for (const [ddx, ddy] of DIRS) {
          const nx = px + ddx;
          const ny = py + ddy;
          if (nx < 0 || ny < 0 || nx >= l.w || ny >= l.h || ny === hallY) continue;
          const ni = idx(l, nx, ny);
          if (l.wall[ni] || cells.has(ni)) continue;
          cells.add(ni);
          q.push(ni);
        }
      }
      const boxes = l.boxes.filter((b) => cells.has(b));
      const goals = l.goals.filter((g) => cells.has(g));
      if (!boxes.length && !goals.length) continue;
      for (const c of cells) visited.add(c);
      rooms.push({ cells, door, boxes, goals });
    }
  }
  if (!rooms.length) return null;
  rooms.sort((a, b) => (a.door % l.w) - (b.door % l.w));
  return { hallY, hallCells, rooms };
}

function replay(l: Level, player: number, boxesIn: number[], moves: string): { player: number; boxes: number[] } {
  const boxes = new Set(boxesIn);
  let p = player;
  for (const ch of moves) {
    if (/\s/.test(ch)) continue;
    const lower = ch.toLowerCase();
    let dx = 0;
    let dy = 0;
    if (lower === 'u') dy = -1;
    else if (lower === 'd') dy = 1;
    else if (lower === 'l') dx = -1;
    else if (lower === 'r') dx = 1;
    else continue;
    const [x, y] = xy(l, p);
    const ni = idx(l, x + dx, y + dy);
    if (boxes.has(ni)) {
      boxes.delete(ni);
      boxes.add(idx(l, x + 2 * dx, y + 2 * dy));
    }
    p = ni;
  }
  return { player: p, boxes: [...boxes].sort((a, b) => a - b) };
}

function solve(levelText: string): string {
  const l = parse(levelText);
  const split = findRooms(l);
  if (!split || split.rooms.length <= 1) {
    return solvePushOptimal(l);
  }

  let player = l.player;
  let allBoxes = l.boxes.slice();
  let allMoves = '';
  const solvedGoals = new Set<number>();

  for (const room of split.rooms) {
    // Sub-level: wall off other rooms; keep hallway for player travel.
    const wall = new Uint8Array(l.wall);
    for (let i = 0; i < wall.length; i++) {
      if (split.hallCells.has(i) || room.cells.has(i)) continue;
      // Keep other rooms' cells as walls (player shouldn't need them)
      if (!l.wall[i]) wall[i] = 1;
    }
    // Boxes not in this room become walls (solved ones sit on goals)
    for (const b of allBoxes) {
      if (!room.cells.has(b)) wall[b] = 1;
    }
    const boxes = allBoxes.filter((b) => room.cells.has(b)).sort((a, b) => a - b);
    const goals = room.goals.slice();
    const sub: Level = {
      w: l.w,
      h: l.h,
      wall,
      goals,
      boxes,
      player,
      goalSet: new Set(goals),
    };
    const moves = solvePushOptimal(sub, { forbid: split.hallCells });
    if (!moves) {
      // Fallback: whole-level search
      return solvePushOptimal(l);
    }
    allMoves += moves;
    const next = replay(l, player, allBoxes, moves);
    player = next.player;
    allBoxes = next.boxes;
    // Walk player back onto the hallway so the next room's walled-off sublevel can reach its door.
    const boxSet = new Set(allBoxes);
    let bestHall = -1;
    let bestPath: string | null = null;
    for (const h of split.hallCells) {
      if (boxSet.has(h)) continue;
      const path = walkPath(l, player, h, boxSet);
      if (path === null) continue;
      if (bestPath === null || path.length < bestPath.length) {
        bestPath = path;
        bestHall = h;
      }
    }
    if (bestHall >= 0 && bestPath !== null) {
      allMoves += bestPath;
      player = bestHall;
    }
    for (const g of goals) solvedGoals.add(g);
  }
  return allMoves;
}

for (const id of readdirSync(I).sort()) {
  const moves = solve(readFileSync(join(I, id, 'level.txt'), 'utf8'));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${moves}\n`);
}
