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
