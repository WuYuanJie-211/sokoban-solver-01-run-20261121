[![sokoban-solver-01-run-20261121](https://make.fun/badge/sokoban-solver-01-run-20261121.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121)
[![rank](https://make.fun/badge/sokoban-solver-01-run-20261121/WuYuanJie-211/sokoban-solver-01-run-20261121/rank.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121)
[![reward](https://make.fun/badge/sokoban-solver-01-run-20261121/WuYuanJie-211/sokoban-solver-01-run-20261121/reward.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121)

# sokoban-solver-01-run-20261121

A push-optimal Sokoban solver for the make.fun
[sokoban-solver-01-run-20261121](https://make.fun/bounty/sokoban-solver-01-run-20261121)
bounty. One run answers all five instances: `main.ts` reads
`/input/<id>/level.txt` (XSB) and writes `/output/<id>/solution.txt`
(moves in LURD), push-optimal on every level.

## How it works

The levels are a one-wide hallway with one to four rooms off it, each room
holding 3–4 boxes and as many goals, and a box pushed into the hallway can
never come back — so every box stays in its room and a level's push-optimum
is the sum of its rooms' optima. The solver:

1. Parses the XSB level and computes the live squares (a box there can still
   be pushed onto a goal, ignoring the other boxes) by pulling backwards
   from the goals.
2. Splits the level into rooms by cutting the dead squares of the player's
   row — the hallway — out of the floor; each connected part left holding
   boxes is a room. The split is verified (no box in the hallway, no goal
   outside a room, boxes equal goals per room) and falls back if it fails.
3. Solves each room push-optimally with a layered breadth-first search over
   pushes, the player's reachable region canonicalised to its lowest square,
   pruning dead squares and frozen 2×2 blocks. The other rooms' boxes stand
   as walls (on their goals once solved), and the player walks on from where
   the last room left it.
4. Replays the whole move string on the level and checks it is legal and
   solves the level in the expected push count; if any check fails, it tries
   another room order, then a whole-level search, and always writes a file
   (an empty one is valid) so no instance is ever left unanswered.

No clock, no randomness: the search is budgeted by work (a state cap), so
two runs are byte-identical. Node 22, standard library only.

## Local run

```sh
mkdir -p out
MAKEFUN_INPUT_DIR=../sokoban-solver-01-run-20261121-kit/sokoban-solver-01-run-20261121-kit/practice/input MAKEFUN_OUTPUT_DIR=out node main.ts
```

`main.ts` runs as `node main.ts` (Node 22 strips the erasable TypeScript
types natively).
