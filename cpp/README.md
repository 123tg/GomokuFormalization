# C++ proof searcher

This directory contains an untrusted C++17 proof searcher for the existing
Lean Gomoku model. It does not change `CompactCertificate`: a successful run
emits a Lean source file containing the same `terminal`, `proverMove`, and
`opponentMoves` nodes that `Gomoku.Certificate` already checks.

## Current engine

- four-word bitboards for each player;
- incremental deterministic Zobrist hashes plus exact bitboard equality;
- iterative bounded-depth DFPN over the target-player OR nodes and opponent
  AND nodes;
- immediate-win and forced-defense ordering/pruning at target nodes only;
- complete legal-move expansion at opponent nodes;
- separate node, transposition-table, and emitted-certificate limits;
- parent-before-child Lean certificate output;
- no FFI and no change to Lean's trusted boundary.

The transposition table accelerates search, but the first exporter deliberately
materializes a tree-shaped proof. Sharing is not yet applied during certificate
emission because the current checker requires every reference to point forward.

## Build and test on Windows

```powershell
powershell.exe -NoProfile -ExecutionPolicy Bypass -File .\cpp\build.ps1 -Clean
.\cpp\build\gomoku_tests.exe
```

The local build uses the available GCC 10.3 toolchain. Build products are
written only to `cpp/build/`, which is ignored by Git.

## Position format

A position file contains the side to move, the proof target, and 15 rows from
`y = 0` through `y = 14`. Columns run from `x = 0` through `x = 14`.

```text
turn black
target black
...............
...
.....XXXX......
...
```

`X` is Black, `O` is White, and `.` is empty. The examples directory contains
an immediate-win OR position and a two-reply opponent AND position.

## Generate and check a certificate

```powershell
.\cpp\build\gomoku_solver.exe `
  --input .\cpp\examples\immediate_win.txt `
  --output .\Gomoku\Generated\CppSmoke.lean `
  --definition cppSmoke `
  --max-depth 1 `
  --max-nodes 10

lake build Gomoku.Generated.CppSmoke
```

Important options:

- `--max-depth`: iterative ply bound from 0 through the board maximum of 225;
- `--max-nodes`: expanded-node budget, with `0` meaning unlimited;
- `--max-table-entries`: exact transposition-table bound;
- `--max-certificate-nodes`: exporter bound, with `0` meaning unlimited;
- `--max-prover-moves`: optional selective target width; a positive value can
  miss a proof and therefore makes a negative result inconclusive;
- `--no-forced-pruning`: searches every ordered target move.

The generated file proves only that the existing Lean checker accepted the
data. C++ rule code, hashing, DFPN, pruning, and serialization remain outside
the trusted proof layer. A `found` result is meaningful after Lean accepts the
certificate; depth or resource exhaustion is not a proof that the position is
unwinnable.

## Known limitations

- no dedicated VCF/VCT threat-space phase yet;
- no parallel search;
- no table replacement policy after the hard entry limit;
- no proof-DAG sharing in the exporter;
- root boards are emitted as arrays of stones, so very large generated Lean
  files will eventually need a more scalable importer;
- generated checks currently use `native_decide`, matching the repository's
  executable regression style rather than reducing a huge certificate in the
  kernel.
