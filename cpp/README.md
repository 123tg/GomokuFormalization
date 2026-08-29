# C++ proof searcher

This directory contains an untrusted C++17 proof searcher for the existing
Lean Gomoku model. It does not change `CompactCertificate`: a successful run
emits a Lean source file containing the same `terminal`, `proverMove`, and
`opponentMoves` nodes that `Gomoku.Certificate` already checks.

The separate C++20 utilities under `cpp/tools/` study complete 5x5--8x8
Maker--Breaker draw proofs. Their build commands, proof-status distinction,
and recorded results are documented in `cpp/tools/README.md`.

## Current engine

- four-word bitboards for each player;
- incremental deterministic Zobrist hashes plus exact bitboard equality;
- iterative bounded-depth DFPN over the target-player OR nodes and opponent
  AND nodes;
- separately bounded VCF probing for immediate wins and continuous-four
  sequences, used only as target-move guidance for DFPN;
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
an immediate-win OR position, a two-reply opponent AND position, and a
three-ply open-four VCF position.

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
- `--max-vcf-depth`: VCF hint horizon, with `0` disabling the oracle;
- `--max-nodes`: expanded-node budget, with `0` meaning unlimited;
- `--max-vcf-nodes`: independent VCF position budget, with `0` meaning
  unlimited; exhaustion disables the hint but does not stop DFPN;
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

## Lean interface correspondence

The authoritative contract is `../SEARCHER_INTERFACE.md`.  The exporter keeps the
existing program representation and maps it directly to Lean:

- C++ `Coord {x, y}` becomes Lean `(x, y)`, with `x` as the column and `y` as
  the row; both sides use the row-major index `y * 15 + x`;
- `Certificate::target` and the three `CertificateKind` cases map directly to
  `CompactCertificate.target` and `CertificateNode`;
- nodes are emitted in depth-first preorder, so every edge satisfies
  `parent < child`;
- a prover node emits one proved move, while an opponent node emits every
  legal reply; VCF guidance never removes opponent replies;
- the exact bitboards, turn, target, and remaining depth participate in table
  equality, so the Zobrist value is only a hash accelerator.

`validateCertificate` performs an untrusted preflight before writing Lean.  It
rejects bad terminal labels, wrong turns, illegal or missing moves, duplicate
opponent replies, non-forward references, mismatched child positions, and
invalid exporter source edges.  Lean repeats the proof-relevant checks.

For an empty 15x15 board with Black to move and Black as target, generated code
uses `checkCertificate` and `compact_certificate_sound`.  All other roots use
`checkLocalCertificateAt` and `local_certificate_at_sound`; a local result must
not be presented as the global opening theorem.

The parameterized 5x5--8x8 draw programs in `cpp/tools/` do not emit this
15x15 force-win certificate.  Their current results therefore remain
reproducible computations rather than Lean-checked draw theorems.

The VCF oracle accepts only attacker moves that win immediately or create at
least one immediate winning point while leaving the defender no immediate
win. With one winning point it recursively checks the forced block; with two
or more, one defender stone cannot cover every point. This is a move-ordering
oracle, not part of the trusted proof: DFPN still builds the full opponent AND
node, and Lean checks every reply. On `examples/open_four_vcf.txt`, the oracle
reduces DFPN expansion from 13 nodes to 7; both configurations emit the same
six-node checked certificate.

## Known limitations

- no VCT/open-three threat-space search yet; the current oracle covers bounded
  continuous-four lines only;
- no parallel search;
- no table replacement policy after the hard entry limit;
- no proof-DAG sharing in the exporter;
- root boards are emitted as arrays of stones, so very large generated Lean
  files will eventually need a more scalable importer;
- generated checks currently use `native_decide`, matching the repository's
  executable regression style rather than reducing a huge certificate in the
  kernel.
