// sokoban-solver-01: a push-optimal Sokoban solver.
//
// The levels are a one-wide hallway with one to four rooms off it, each room
// holding 3-4 boxes and as many goals, and a box pushed into the hallway can
// never come back, so every box stays in its room and a level's push-optimum
// is the sum of its rooms' optima. This program splits a level into rooms,
// solves each room push-optimally with a layered breadth-first search over
// pushes, and joins the rooms' move strings, replaying the whole answer on
// the level before writing it.
//
// Deterministic: no clock, no randomness; the search is budgeted by work (a
// state cap), so two runs write byte-identical files. Node 22, standard
// library only, erasable TypeScript syntax.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

/** The four steps: [dx, dy, the walk's letter, the push's letter]. */
const DIRS: Array<[number, number, string, string]> = [
  [0, -1, 'u', 'U'],
  [0, 1, 'd', 'D'],
  [-1, 0, 'l', 'L'],
  [1, 0, 'r', 'R'],
];

/** The most states one room's search keeps before it gives up (work, never the clock). */
const ROOM_STATE_CAP = 500000;
/** The most states the whole-level fallback keeps. */
const WHOLE_STATE_CAP = 250000;
/** The most states the whole-level weighted fallback keeps (a smaller cap: it is a last resort). */
const WHOLE_WEIGHTED_CAP = 100000;
/** The weight on the heuristic in the weighted fallback search (a solution within about twice the optimum). */
const WEIGHT = 2;

/** A level: its width and height, walls (1 a wall), goals, boxes and player, as squares. */
interface Level {
  w: number;
  h: number;
  wall: Uint8Array;
  goals: number[];
  boxes: number[];
  player: number;
}

/** A room: its floor squares, boxes and goals. */
interface Room {
  squares: number[];
  boxes: number[];
  goals: number[];
}

/** A found answer: its push count and its moves (lower a walk, upper a push). */
interface Found {
  pushes: number;
  moves: string;
}

/**
 * A level in XSB text (# wall, space floor, . goal, $ box, * box on a goal,
 * @ player, + player on a goal), each line a row. Short rows and squares
 * outside them are walls; the outermost frame is a wall whatever it shows.
 */
function parseLevel(text: string): Level {
  const rows = text.split('\n').filter((r) => r.length > 0);
  if (rows.length === 0) return { w: 1, h: 1, wall: new Uint8Array([1]), goals: [], boxes: [], player: -1 };
  const h = rows.length;
  const w = Math.max(...rows.map((r) => r.length));
  const wall = new Uint8Array(w * h).fill(1);
  const goals: number[] = [];
  const boxes: number[] = [];
  let player = -1;
  rows.forEach((row, y) => {
    for (let x = 0; x < row.length; x++) {
      const ch = row[x];
      const i = y * w + x;
      if (ch === '#') continue;
      wall[i] = 0;
      if (ch === '.' || ch === '*' || ch === '+') goals.push(i);
      if (ch === '$' || ch === '*') boxes.push(i);
      if (ch === '@' || ch === '+') player = i;
    }
  });
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      if (x === 0 || y === 0 || x === w - 1 || y === h - 1) wall[y * w + x] = 1;
    }
  }
  boxes.sort((a, b) => a - b);
  goals.sort((a, b) => a - b);
  return { w, h, wall, goals, boxes, player };
}

/**
 * The squares from which a box alone can be pushed onto some goal: pull
 * backwards from the goals over open floor. A square a box can never leave
 * for a goal is dead, and a box on one is lost.
 */
function liveSquares(level: Level): Uint8Array {
  const { w, wall, goals } = level;
  const live = new Uint8Array(wall.length);
  const queue: number[] = [];
  for (const g of goals) {
    live[g] = 1;
    queue.push(g);
  }
  for (let qi = 0; qi < queue.length; qi++) {
    const x = queue[qi];
    for (const [dx, dy] of DIRS) {
      const d = dy * w + dx;
      const y = x - d;
      if (y < 0 || y >= wall.length) continue;
      const z = y - d;
      if (z < 0 || z >= wall.length) continue;
      if (!wall[y] && !wall[z] && !live[y]) {
        live[y] = 1;
        queue.push(y);
      }
    }
  }
  return live;
}

/**
 * The squares the player reaches from `from` with `occupied` (a box mask) in
 * the way, marked in `seen` with `stamp`; the lowest square of the region,
 * which names the region: the player can walk anywhere inside it, so its
 * exact square does not matter, only which region it stands in.
 */
function reach(level: Level, occupied: Uint8Array, from: number, seen: Int32Array, stamp: number, stack: Int32Array): number {
  const { w, wall } = level;
  let low = from;
  let n = 0;
  stack[n++] = from;
  seen[from] = stamp;
  while (n > 0) {
    const p = stack[--n];
    if (p < low) low = p;
    const q0 = p - w;
    const q1 = p + w;
    const q2 = p - 1;
    const q3 = p + 1;
    if (wall[q0] === 0 && occupied[q0] === 0 && seen[q0] !== stamp) {
      seen[q0] = stamp;
      stack[n++] = q0;
    }
    if (wall[q1] === 0 && occupied[q1] === 0 && seen[q1] !== stamp) {
      seen[q1] = stamp;
      stack[n++] = q1;
    }
    if (wall[q2] === 0 && occupied[q2] === 0 && seen[q2] !== stamp) {
      seen[q2] = stamp;
      stack[n++] = q2;
    }
    if (wall[q3] === 0 && occupied[q3] === 0 && seen[q3] !== stamp) {
      seen[q3] = stamp;
      stack[n++] = q3;
    }
  }
  return low;
}

/**
 * Whether the box just pushed to `t` sits in a frozen 2 x 2 block: four
 * squares of walls and boxes with a box among them off its goal. A box in
 * one can never be pushed out, so the state is dead.
 */
function frozenBlock(level: Level, occupied: Uint8Array, goal: Uint8Array, t: number): boolean {
  const { w, wall } = level;
  for (const a of [t, t - 1, t - w, t - w - 1]) {
    const b = a + 1;
    const c = a + w;
    const d = c + 1;
    const full =
      (wall[a] || occupied[a]) && (wall[b] || occupied[b]) && (wall[c] || occupied[c]) && (wall[d] || occupied[d]);
    if (!full) continue;
    if ((occupied[a] && !goal[a]) || (occupied[b] && !goal[b]) || (occupied[c] && !goal[c]) || (occupied[d] && !goal[d])) return true;
  }
  return false;
}

// A state's key: the region's lowest square and the boxes' squares, as digits
// in base `size`. Exact while size ** (boxes + 1) stays under 2 ** 53: a room
// of up to four boxes on any board this generator draws (size at most 255).
function keyOf(boxes: number[], low: number, size: number): number {
  let k = low;
  for (const b of boxes) k = k * size + b;
  return k;
}

/**
 * The push-optimal solution of `level`, searching at most `maxStates` states:
 * {pushes, moves}, or null when the search gives up (or the level has no
 * solution). A layered breadth-first search over pushes: states are the
 * boxes' squares and the player's reachable region, expanded in order of
 * pushes made, so the first solved state met is push-optimal. Dead squares
 * and frozen 2 x 2 blocks are pruned; neither prunes a solvable state.
 */
function searchPushes(level: Level, maxStates: number): Found | null {
  const { w, wall, goals } = level;
  const size = wall.length;
  const goal = new Uint8Array(size);
  for (const g of goals) goal[g] = 1;
  const live = liveSquares(level);
  const occupied = new Uint8Array(size);
  const seen = new Int32Array(size);
  const mark = new Int32Array(size);
  const stack = new Int32Array(size);
  let stamp = 0;
  const isSolved = (boxes: number[]): boolean => {
    for (let i = 0; i < boxes.length; i++) if (!goal[boxes[i]]) return false;
    return true;
  };
  if (level.boxes.some((b) => !live[b])) return null;
  if (isSolved(level.boxes)) return { pushes: 0, moves: '' };

  // The states in the order found: their boxes, the player's square, and the
  // push that made them from their parent.
  const statesBoxes: number[][] = [level.boxes.slice()];
  const statesPlayer: number[] = [level.player];
  const parent: number[] = [-1];
  const index = new Map<number, number>();
  for (const b of level.boxes) occupied[b] = 1;
  index.set(keyOf(level.boxes, reach(level, occupied, level.player, seen, ++stamp, stack), size), 0);
  for (const b of level.boxes) occupied[b] = 0;

  let found = -1;
  for (let head = 0; found < 0 && head < statesBoxes.length; head++) {
    const boxes = statesBoxes[head];
    for (const b of boxes) occupied[b] = 1;
    reach(level, occupied, statesPlayer[head], seen, ++stamp, stack);
    const here = stamp;
    for (let bi = 0; bi < boxes.length && found < 0; bi++) {
      const b = boxes[bi];
      for (const [dx, dy] of DIRS) {
        const d = dy * w + dx;
        const t = b + d;
        if (seen[b - d] !== here || wall[t] || occupied[t] || !live[t]) continue;
        occupied[b] = 0;
        occupied[t] = 1;
        const frozen = frozenBlock(level, occupied, goal, t);
        let key = -1;
        let next: number[] | null = null;
        if (!frozen) {
          next = boxes.slice();
          next[bi] = t;
          next.sort((x, y) => x - y);
          key = keyOf(next, reach(level, occupied, b, mark, ++stamp, stack), size);
        }
        occupied[t] = 0;
        occupied[b] = 1;
        if (frozen || index.has(key)) continue;
        if (statesBoxes.length >= maxStates) {
          for (const x of boxes) occupied[x] = 0;
          return null;
        }
        index.set(key, statesBoxes.length);
        statesBoxes.push(next as number[]);
        statesPlayer.push(b);
        parent.push(head);
        if (isSolved(next as number[])) {
          found = statesBoxes.length - 1;
          break;
        }
      }
    }
    for (const x of boxes) occupied[x] = 0;
  }
  if (found < 0) return null;

  // The path of states, then the moves: walk to each push's square, then push.
  const path: number[] = [];
  for (let s = found; s > 0; s = parent[s]) path.push(s);
  path.reverse();
  let moves = '';
  let player = level.player;
  let boxes = level.boxes;
  for (const s of path) {
    const nextBoxes = statesBoxes[s];
    const from = boxes.find((b) => !nextBoxes.includes(b)) as number;
    const to = nextBoxes.find((b) => !boxes.includes(b)) as number;
    const d = to - from;
    const dir = DIRS.find(([dx, dy]) => dy * w + dx === d) as [number, number, string, string];
    for (const b of boxes) occupied[b] = 1;
    moves += walkTo(level, occupied, player, from - d);
    for (const b of boxes) occupied[b] = 0;
    moves += dir[3];
    player = from;
    boxes = nextBoxes;
  }
  return { pushes: path.length, moves };
}

/**
 * A lower bound on the pushes still needed: the cheapest way to match every
 * box to a distinct goal by grid distance (a push moves one box one square,
 * so it changes this by at most one). Brute-force permutations while the
 * boxes are few (a room: at most four); the sum of nearest-goal distances
 * when they are many (a whole level), which is cheaper and still a bound.
 */
function matchingCost(boxes: number[], goals: number[], w: number): number {
  const n = boxes.length;
  if (n === 0) return 0;
  const dist = (b: number, g: number): number =>
    Math.abs((b % w) - (g % w)) + Math.abs(Math.floor(b / w) - Math.floor(g / w));
  if (n > 4) {
    let sum = 0;
    for (const b of boxes) {
      let best = Infinity;
      for (const g of goals) if (dist(b, g) < best) best = dist(b, g);
      sum += best;
    }
    return sum;
  }
  const m = goals.length;
  let best = Infinity;
  const used = new Array<boolean>(m).fill(false);
  const assign = (i: number, cost: number): void => {
    if (cost >= best) return;
    if (i === n) {
      best = cost;
      return;
    }
    for (let j = 0; j < m; j++) {
      if (used[j]) continue;
      used[j] = true;
      assign(i + 1, cost + dist(boxes[i], goals[j]));
      used[j] = false;
    }
  };
  assign(0, 0);
  return best;
}

/**
 * A solution of `level` by weighted A* over pushes (at most `maxStates`
 * states), or null when it gives up. The fallback when the push-optimal
 * search exceeds its cap: it trades optimality for an answer, expanding
 * states by pushes plus WEIGHT times the matching bound, so a room solved
 * this way is worth roughly half its optimum instead of nothing. The same
 * state, pruning and move-building as the optimal search; only the order of
 * expansion and the visited rule differ (a state is kept again when reached
 * in fewer pushes).
 */
function searchWeighted(level: Level, maxStates: number): Found | null {
  const { w, wall, goals } = level;
  const size = wall.length;
  const goal = new Uint8Array(size);
  for (const g of goals) goal[g] = 1;
  const live = liveSquares(level);
  const occupied = new Uint8Array(size);
  const seen = new Int32Array(size);
  const mark = new Int32Array(size);
  const stack = new Int32Array(size);
  let stamp = 0;
  const isSolved = (boxes: number[]): boolean => {
    for (let i = 0; i < boxes.length; i++) if (!goal[boxes[i]]) return false;
    return true;
  };
  if (level.boxes.some((b) => !live[b])) return null;
  if (isSolved(level.boxes)) return { pushes: 0, moves: '' };

  // The states in the order found: their boxes, the player's square, their
  // key, and the push that made them from their parent.
  const statesBoxes: number[][] = [level.boxes.slice()];
  const statesPlayer: number[] = [level.player];
  const stateKey: number[] = [];
  const parent: number[] = [-1];
  const best = new Map<number, number>();
  for (const b of level.boxes) occupied[b] = 1;
  const startKey = keyOf(level.boxes, reach(level, occupied, level.player, seen, ++stamp, stack), size);
  for (const b of level.boxes) occupied[b] = 0;
  stateKey.push(startKey);
  best.set(startKey, 0);

  // The open list, a heap on [pushes + WEIGHT * bound, pushes, state], the
  // smallest first (ties by fewer pushes, then the earlier state: fixed).
  const heap: Array<[number, number, number]> = [];
  const less = (a: [number, number, number], b: [number, number, number]): boolean =>
    a[0] < b[0] || (a[0] === b[0] && (a[1] < b[1] || (a[1] === b[1] && a[2] < b[2])));
  const heapPush = (e: [number, number, number]): void => {
    let i = heap.length;
    heap.push(e);
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (!less(heap[i], heap[p])) break;
      const t = heap[i];
      heap[i] = heap[p];
      heap[p] = t;
      i = p;
    }
  };
  const heapPop = (): [number, number, number] => {
    const top = heap[0];
    const last = heap.pop() as [number, number, number];
    if (heap.length > 0) {
      heap[0] = last;
      for (let i = 0; ; ) {
        let c = 2 * i + 1;
        if (c >= heap.length) break;
        if (c + 1 < heap.length && less(heap[c + 1], heap[c])) c++;
        if (!less(heap[c], heap[i])) break;
        const t = heap[i];
        heap[i] = heap[c];
        heap[c] = t;
        i = c;
      }
    }
    return top;
  };
  heapPush([WEIGHT * matchingCost(level.boxes, goals, w), 0, 0]);

  let found = -1;
  while (heap.length > 0 && found < 0) {
    const [, g, s] = heapPop();
    if (g > (best.get(stateKey[s]) as number)) continue;
    const boxes = statesBoxes[s];
    for (const b of boxes) occupied[b] = 1;
    reach(level, occupied, statesPlayer[s], seen, ++stamp, stack);
    const here = stamp;
    for (let bi = 0; bi < boxes.length && found < 0; bi++) {
      const b = boxes[bi];
      for (const [dx, dy] of DIRS) {
        const d = dy * w + dx;
        const t = b + d;
        if (seen[b - d] !== here || wall[t] || occupied[t] || !live[t]) continue;
        occupied[b] = 0;
        occupied[t] = 1;
        const frozen = frozenBlock(level, occupied, goal, t);
        let key = -1;
        let next: number[] | null = null;
        if (!frozen) {
          next = boxes.slice();
          next[bi] = t;
          next.sort((x, y) => x - y);
          key = keyOf(next, reach(level, occupied, b, mark, ++stamp, stack), size);
        }
        occupied[t] = 0;
        occupied[b] = 1;
        if (frozen || next === null) continue;
        const g2 = g + 1;
        const known = best.get(key);
        if (known !== undefined && known <= g2) continue;
        if (statesBoxes.length >= maxStates) {
          for (const x of boxes) occupied[x] = 0;
          return null;
        }
        best.set(key, g2);
        const id = statesBoxes.length;
        statesBoxes.push(next);
        statesPlayer.push(b);
        stateKey.push(key);
        parent.push(s);
        if (isSolved(next)) {
          found = id;
          break;
        }
        heapPush([g2 + WEIGHT * matchingCost(next, goals, w), g2, id]);
      }
    }
    for (const x of boxes) occupied[x] = 0;
  }
  if (found < 0) return null;

  // The path of states, then the moves: walk to each push's square, then push.
  const path: number[] = [];
  for (let s = found; s > 0; s = parent[s]) path.push(s);
  path.reverse();
  let moves = '';
  let player = level.player;
  let boxes = level.boxes;
  for (const s of path) {
    const nextBoxes = statesBoxes[s];
    const from = boxes.find((b) => !nextBoxes.includes(b)) as number;
    const to = nextBoxes.find((b) => !boxes.includes(b)) as number;
    const d = to - from;
    const dir = DIRS.find(([dx, dy]) => dy * w + dx === d) as [number, number, string, string];
    for (const b of boxes) occupied[b] = 1;
    moves += walkTo(level, occupied, player, from - d);
    for (const b of boxes) occupied[b] = 0;
    moves += dir[3];
    player = from;
    boxes = nextBoxes;
  }
  return { pushes: path.length, moves };
}

/** The shortest walk from `from` to `to` around walls and boxes, in lower LURD letters (the first direction first on ties). */
function walkTo(level: Level, occupied: Uint8Array, from: number, to: number): string {
  const { w, wall } = level;
  if (from === to) return '';
  const prev = new Int32Array(wall.length).fill(-1);
  const how: string[] = new Array<string>(wall.length);
  const queue: number[] = [from];
  prev[from] = from;
  for (let qi = 0; qi < queue.length; qi++) {
    const p = queue[qi];
    if (p === to) break;
    for (const [dx, dy, letter] of DIRS) {
      const q = p + dy * w + dx;
      if (wall[q] || occupied[q] || prev[q] !== -1) continue;
      prev[q] = p;
      how[q] = letter;
      queue.push(q);
    }
  }
  if (prev[to] === -1) throw new Error('walkTo: the push square is out of reach');
  let s = '';
  for (let p = to; p !== from; p = prev[p]) s = how[p] + s;
  return s;
}

/** The square the player stands on after `moves` (LURD, the case aside) from `from` on a board `w` wide. */
function endOf(w: number, from: number, moves: string): number {
  let p = from;
  for (const ch of moves.toLowerCase()) p += ch === 'u' ? -w : ch === 'd' ? w : ch === 'l' ? -1 : 1;
  return p;
}

/** The replay of `moves` on `level`: whether every step was legal, whether every box ends on a goal, and how many pushes it took. */
function replay(level: Level, moves: string): { legal: boolean; solved: boolean; pushes: number } {
  const { w, wall, goals } = level;
  const goal = new Uint8Array(wall.length);
  for (const g of goals) goal[g] = 1;
  const box = new Uint8Array(wall.length);
  for (const b of level.boxes) box[b] = 1;
  let player = level.player;
  let pushes = 0;
  for (const ch of moves) {
    const lower = ch.toLowerCase();
    if (lower !== 'u' && lower !== 'd' && lower !== 'l' && lower !== 'r') return { legal: false, solved: false, pushes };
    const d = lower === 'u' ? -w : lower === 'd' ? w : lower === 'l' ? -1 : 1;
    const next = player + d;
    if (wall[next]) return { legal: false, solved: false, pushes };
    if (box[next]) {
      const beyond = next + d;
      if (wall[beyond] || box[beyond]) return { legal: false, solved: false, pushes };
      box[next] = 0;
      box[beyond] = 1;
      pushes++;
    }
    player = next;
  }
  for (let i = 0; i < box.length; i++) {
    if (box[i] && !goal[i]) return { legal: true, solved: false, pushes };
  }
  return { legal: true, solved: true, pushes };
}

/**
 * The level's rooms: cut the dead squares of the player's row (the hallway:
 * a box there reaches no goal) out of the floor, and each part left that
 * holds a box is a room, its squares, boxes and goals. Null when some part
 * holds more or fewer boxes than goals, a goal lies in the hallway, or a box
 * starts in the hallway: then the level is no set of rooms.
 */
function roomsOf(level: Level): Room[] | null {
  const { w, wall, goals, boxes, player } = level;
  const live = liveSquares(level);
  const row = Math.floor(player / w);
  const cut = new Uint8Array(wall.length);
  for (let i = row * w; i < (row + 1) * w; i++) if (!wall[i] && !live[i]) cut[i] = 1;
  if (boxes.some((b) => cut[b])) return null;
  const part = new Int32Array(wall.length).fill(-1);
  const rooms: Room[] = [];
  for (let s = 0; s < wall.length; s++) {
    if (wall[s] || cut[s] || part[s] >= 0) continue;
    const squares: number[] = [s];
    part[s] = rooms.length;
    for (let i = 0; i < squares.length; i++) {
      for (const [dx, dy] of DIRS) {
        const q = squares[i] + dy * w + dx;
        if (!wall[q] && !cut[q] && part[q] < 0) {
          part[q] = rooms.length;
          squares.push(q);
        }
      }
    }
    rooms.push({ squares, boxes: [], goals: [] });
  }
  for (const b of boxes) rooms[part[b]].boxes.push(b);
  for (const g of goals) if (part[g] >= 0) rooms[part[g]].goals.push(g);
  if (goals.some((g) => part[g] < 0) || rooms.some((r) => r.boxes.length !== r.goals.length)) return null;
  return rooms.filter((r) => r.boxes.length > 0);
}

/** Every ordering of `items`, the given order first (lexicographic permutations). */
function permutations(items: number[]): number[][] {
  const out: number[][] = [];
  const n = items.length;
  const used = new Array<boolean>(n).fill(false);
  const cur: number[] = [];
  const build = (): void => {
    if (cur.length === n) {
      out.push(cur.slice());
      return;
    }
    for (let i = 0; i < n; i++) {
      if (used[i]) continue;
      used[i] = true;
      cur.push(items[i]);
      build();
      cur.pop();
      used[i] = false;
    }
  };
  build();
  return out;
}

/**
 * The rooms solved in the order `ord`: each room's push-optimal solution in
 * turn, the other rooms' boxes standing as walls (on their goals once their
 * room is done), the player walking on from where the last room left it.
 * Null when a room's search gives up. The joined answer must replay legal
 * and solved on the level, or the order is no good (a solved room can shut
 * the player in, so another order is tried).
 */
function solveInOrder(level: Level, rooms: Room[], ord: number[]): Found | null {
  const done = new Set<number>();
  let player = level.player;
  let pushes = 0;
  let moves = '';
  for (const ri of ord) {
    const room = rooms[ri];
    const wall = level.wall.slice();
    for (let oj = 0; oj < rooms.length; oj++) {
      if (oj === ri) continue;
      const other = rooms[oj];
      for (const b of done.has(oj) ? other.goals : other.boxes) wall[b] = 1;
    }
    const sub: Level = {
      w: level.w,
      h: level.h,
      wall,
      goals: room.goals.slice().sort((a, b) => a - b),
      boxes: room.boxes.slice().sort((a, b) => a - b),
      player,
    };
    const solved = searchPushes(sub, ROOM_STATE_CAP) ?? searchWeighted(sub, ROOM_STATE_CAP);
    if (solved === null) return null;
    pushes += solved.pushes;
    moves += solved.moves;
    player = endOf(level.w, player, solved.moves);
    done.add(ri);
  }
  const check = replay(level, moves);
  if (!check.legal || !check.solved || check.pushes !== pushes) return null;
  return { pushes, moves };
}

/**
 * The level solved room by room, trying every room order until one replays.
 * A box never leaves its room, so the rooms' optima add up to the level's.
 * Null when no order works, or the level is no set of rooms: then a search
 * over the whole level, which a small level still solves.
 */
function solveByRooms(level: Level): Found | null {
  const rooms = roomsOf(level);
  if (rooms === null) return searchPushes(level, WHOLE_STATE_CAP) ?? searchWeighted(level, WHOLE_WEIGHTED_CAP);
  const orders = permutations(rooms.map((_, i) => i));
  for (const ord of orders) {
    const attempt = solveInOrder(level, rooms, ord);
    if (attempt !== null) return attempt;
  }
  return searchPushes(level, WHOLE_STATE_CAP) ?? searchWeighted(level, WHOLE_WEIGHTED_CAP);
}

/** The moves for a level in XSB, or '' when it cannot be solved (an empty answer is valid). */
function solve(text: string): string {
  const level = parseLevel(text);
  if (level.player < 0) return '';
  if (level.boxes.length === 0) return '';
  if (level.boxes.every((b) => level.goals.includes(b))) return '';
  let found: Found | null = null;
  try {
    found = solveByRooms(level);
  } catch {
    found = null;
  }
  if (found === null) return '';
  const check = replay(level, found.moves);
  if (!check.legal || !check.solved || check.pushes !== found.pushes) return '';
  return found.moves;
}

for (const id of readdirSync(I).sort()) {
  let moves = '';
  try {
    moves = solve(readFileSync(join(I, id, 'level.txt'), 'utf8'));
  } catch {
    moves = '';
  }
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), moves + '\n');
}
