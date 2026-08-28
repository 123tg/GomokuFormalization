# Exact 5x5 connect-five solve

`solve5x5.cpp` is a standalone exact solver for the parameterized rules

\[
\text{boardSize}=5,\qquad \text{winLength}=5,
\]

starting from the empty board with Black to move. It is separate from the
15x15 certificate generator because the current Lean theorem-facing API only
expresses forced wins, whereas this complete computation returns a draw.

## Build and run

```powershell
powershell.exe -NoProfile -ExecutionPolicy Bypass -File .\cpp\build.ps1
.\cpp\build\solve5x5.exe
```

The executable uses a 25-bit board per player, all 12 possible length-five
lines, exact three-valued negamax, alpha-beta bounds, D4 symmetry
canonicalization, and a fixed 2^27-entry flat transposition table. A table
collision replaces the old entry; lookup always compares the complete
canonical key, so replacement can only lose a cache hit and cannot reuse a
different position's result.

The only game-tree reductions are exact:

- an immediate winning move proves the current node is a win;
- when the opponent has at least two distinct immediate winning cells and the
  current player has no immediate win, one stone cannot block both;
- when the opponent has exactly one immediate winning cell and the current
  player has no immediate win, every non-blocking move loses immediately;
- D4 rotations and reflections preserve every winning line.

## Recorded local result

Run on 2026-08-28 with GCC 10.3, `-O3 -DNDEBUG`:

```text
self_check=passed
board=5x5
win_length=5
root_turn=black
result_for_black=draw
nodes=510652639
table_entries=101108996
table_capacity=134217728
table_hits=304055029
forced_blocks=13856611
symmetry_collapses=436859891
alpha_beta_cutoffs=126688189
table_replacements=101543674
max_depth=25
elapsed_s=396.07
```

The solver source used for the run had SHA-256
`7B74DEFFA90CA58392385EDC0C7C787A8F26C40A9AEDCC22978C54A7F9FC306A`.
The Windows executable hash is not recorded because the PE build embeds
non-reproducible metadata and changes across otherwise identical rebuilds.

This establishes a reproducible computational result, not yet a Lean theorem.
Formal certification of a draw needs a parameterized outcome/draw certificate
and checker; `ForceWin` alone is intentionally unable to state that neither
player can force a win.

## Parameterized 5x5--8x8 draw search

`solve_small_draws.cpp` is a separate C++20 Maker--Breaker proof searcher for
board sizes 5 through 8 with `winLength = 5`. Black is Maker and moves first;
White is Breaker. A `breaker_win` result therefore means that White has a
strategy that prevents every Black five-in-a-row, so the corresponding strong
game is a draw (White is not being claimed to have a five-in-a-row win).

The search follows the proof-preserving reductions in Hsu et al.,
[On solving the 7,7,5-game and the 8,8,5-game](https://doi.org/10.1016/j.tcs.2020.02.023):

- length-five lines are represented as 64-bit masks;
- D4 rotations/reflections canonicalize transpositions and opening orbits;
- static and middle-game pairing certificates are verified before use;
- partial pairing removes mutually dominated cells;
- vertex domination removes a move whose active-line set is contained in
  another move's active-line set;
- Breaker relevancy-zones (r-zones) skip Maker moves outside an already proven
  defense and are propagated through pairing, partial-pairing, and domination
  reductions;
- after a Maker move, the potential terminal condition is

  \[
  P=\sum_{e\text{ not blocked by Breaker}}2^{|M\cap e|}<2^5=32;
  \]

- the main transposition table is a collision-safe four-way set-associative
  flat table storing the full canonical key, game value, and canonical r-zone;
- the pairing finder uses fixed-size arrays, a small result cache, the two
  greedy rules from the paper, and at most the top `N` scored pair branches.

A hash collision can evict a cached proof but cannot turn one position into
another: every lookup compares both complete 64-bit board masks. Pair-search
branch or node limits return `node_limit`, never `impossible`, unless the
searched alternatives were exhaustive. These limits can therefore lose a
proof opportunity but cannot create a false proof.

### Reproduce the small-board results

Build and run the smoke suite:

```powershell
powershell.exe -NoProfile -ExecutionPolicy Bypass -File .\cpp\build.ps1
powershell.exe -NoProfile -ExecutionPolicy Bypass -File .\cpp\tests\small_draw_smoke.ps1
```

The short proof runs used for 5x5, 6x6, and 7x7 are:

```powershell
.\cpp\build\solve_small_draws.exe --board 5 --pair-branches 0 --static-only
.\cpp\build\solve_small_draws.exe --board 6 --pair-branches 2
.\cpp\build\solve_small_draws.exe --board 7 --pair-branches 2 --pairing-nodes 300 --reply-probes 8 --reply-probe-nodes 20 --reply-probe-min-stones 5 --skip-reply-pairing --search-depth 8 --search-nodes 100000 --table-power 20
```

Recorded outputs are kept under `cpp/results/`. The current verified results
are:

| Board | Result | Method | Local elapsed time |
|---|---|---|---:|
| 5x5 | draw | independent exact full-game solve | 396.07 s |
| 5x5 | draw | static pairing certificate | less than 1 ms |
| 6x6 | draw | one White reply plus pairing, all 6 opening orbits | about 2 ms |
| 7x7 | draw | bounded-depth AND/OR proof closed without exhausting its node budget | about 3.1 s |
| 8x8 | unknown | 20,000,000-node bounded run; budget exhausted | about 1,256 s |

`unknown` is deliberately not treated as a game result. The retained 8x8 run
is a performance/progress record, not a proof that Black wins or that the game
draws. The published result is that 8x8 is a draw, but this local search has not
yet reproduced the complete proof.

### Important options

- `--board N`: board size, from 5 through 8.
- `--pairing-nodes N`: node limit for a full pairing attempt.
- `--pair-branches N`: number of best-scored pair branches; zero is exhaustive.
- `--search-depth N`: maximum remaining AND/OR plies.
- `--search-nodes N`: global tree-node limit.
- `--table-power N`: main table capacity is `2^N` slots.
- `--reply-probes N`: try at most `N` cheap pairing replies before recursively
  searching a Breaker node; the default is zero because this helps 7x7 but
  hurts sparse 8x8 positions.
- `--reply-probe-nodes N`: pairing-node limit for each cheap reply probe.
- `--reply-probe-min-stones N`: enable reply probes only after at least `N`
  stones are on the board.
- `--opening-orbit N`: solve one D4 opening orbit independently. This is useful
  for partitioning long 8x8 runs; an orbit result alone is not the full-game
  result.
- `--skip-reply-pairing`: skip the all-replies static pairing prepass.
- `--static-only`: stop after the initial static pairing attempt.
