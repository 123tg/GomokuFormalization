# 无禁手五子棋的规则与必胜策略的形式化

完整的项目方案、已完成成果、当前限制和下一步实施路线见
[`PROJECT_GUIDE.md`](PROJECT_GUIDE.md)。下面保留模块和构建命令的简短概览。

This Lean 4 project formalizes a 15x15, unrestricted Gomoku game.

Current modules:

- `Gomoku.Basic`: players, cells, coordinates, boards, and board updates.
- `Gomoku.Geometry`: four board directions, bounded steps, runs, and open-line predicates.
- `Gomoku.Rules`: positions, legal moves, terminal outcomes, reachability, move monotonicity,
  stone-count/turn invariants, and strict empty-cell descent.
- `Gomoku.Game`: strategy types and the inductive `CanForceWin` game semantics.
- `Gomoku.Tactics`: immediate winning moves, strict open-three/open-four predicates, a
  proved straight open-four immediate-win theorem for Black, and separate
  multi-ply (`SafeDoubleOpenThree`) and immediate-response
  (`ImmediateSafeDoubleOpenThree`) defense-by-defense interfaces.
- `Gomoku.Certificate`: dependent strategy trees and a compact certificate-checking interface.
- `Gomoku.Search`: the untrusted searcher boundary; only checked `CompactCertificate` values
  can cross into the trusted proof layer.
- `Gomoku.Engine`: a budgeted, iterative-deepening AND/OR searcher with forced tactical
  pruning, an optional target-side width limit, a bounded hash transposition table,
  statistics, and a checked certificate boundary.
- `cpp/`: an untrusted C++17 iterative DFPN searcher using bitboards, incremental Zobrist
  hashing, a bounded VCF move oracle, resource limits, and direct export to the unchanged
  Lean `CompactCertificate`.
- `Gomoku.Generated`: C++-generated OR/AND/VCF smoke certificates that are accepted by the
  existing Lean checker and connected to `CanForceWin`.
- `Gomoku.Examples`: API-level sanity checks, horizontal/diagonal/boundary/overline examples,
  and executable board tests.
- `Gomoku.Adversarial`: executable counterexamples and regression checks from the semantic audit.

The rule layer uses the standard unrestricted semantics: a contiguous line of at least five stones wins immediately, including six or more in a row; a full board without a winner is a draw. Forbidden-move rules are intentionally outside this version.

The global 15x15 first-player theorem is not asserted without a strategy certificate. The
dependent `CertificateTree` interface is sound, and the compact checker is now connected to it:
`compact_certificate_sound` proves `CanForceWin initialPosition .black` from a passing
`checkCertificate`. The checker validates legal edges, topological references, complete opponent
coverage, and the root header. No actual 15x15 strategy certificate has been imported yet, so
`initial_black_wins` remains intentionally gated.

The game layer also proves that every non-terminal position has at least one legal move and
provides `defaultStrategy` as a legality-only baseline. It is deliberately not presented as a
winning strategy. `StrategyRealizes` separately states that a concrete position strategy wins
against every legal response. A canonical noncomputable strategy is extracted from `CanForceWin`,
and `strategyRealizes_iff_canForceWin` proves the two semantics equivalent on reachable roots.

The tactical audit includes a cross-shaped double-open-three example. It is intentionally not
treated as a proof that geometry alone forces a win: the formal safety predicate requires the
remaining game-theoretic condition after every legal defense.

`certificateTree_iff_canForceWin` records the bidirectional interface between dependent
strategy trees and `CanForceWin`; the reverse direction uses a proposition-level `Nonempty`
wrapper because Lean does not permit eliminating an arbitrary proof of a proposition directly
into data.

The audit and its open findings are recorded in [`AUDIT_REPORT.md`](AUDIT_REPORT.md). Core
proofs avoid `native_decide`; it is used only in test-oriented modules because it has a larger
trusted runtime boundary than kernel reduction by `decide`.

`Gomoku.Search` also contains an executable 225-cell candidate generator (with a
position-level-terminal-checking `candidateMovesFast` variant whose membership is proved
equivalent, plus `orderedCandidateMoves` which tries nearby cells first without dropping any
candidate, and `immediateWinningMovesFirst` which places direct wins first), a first-immediate-win
scan, and two small certificate generators. Coordinates have a proved row-major
`coordIndex`/`coordAtIndex` inverse. Threats can be cached in a fixed-size
`winningCellsMask`; its direct lookup is proved equivalent to `WinningCells`.
`immediateCertificateFor` handles a one-move win. `firstWinningMove` uses the proved local
`createsFiveFast` predicate; `firstWinningMoveReference` remains available as a full-terminal
reference implementation, and candidate legality plus terminal soundness are proved separately.
`twoPlyCertificateFor` enumerates every legal opponent reply and succeeds when the target has an
immediate winning response on every branch. Local candidates pass through
`checkLocalCertificate`; its proved soundness reuses the same node, edge, topological-order, and
opponent-coverage checks as the global checker. The global `checkCertificate` still requires an
empty-board Black root. These primitives are not yet a complete 15x15 search algorithm and do
not establish the global theorem by themselves. The module also defines a finite-depth
`CandidateTree` search and a compiler to `CompactCertificate`; a fixed five-node opponent-fork
tree is regression-tested through `checkLocalCertificateAt` and `CanForceWin`, and a two-empty-point
depth-2 search smoke test now passes after the position-level terminal-check optimization. Larger
pure-Lean searches remain too slow for routine builds because they repeatedly scan all 225 cells;
the module also exposes `tacticalCandidateMoves` for grouping immediate wins, defensive replies,
and quiet moves. The fast grouping builds one fixed-size `winningCellsMask` per position, but the
default search currently uses the cheaper immediate-win ordering. Incremental threat updates,
cache eviction, certificate DAG sharing, and incremental terminal checks remain planned before
using larger pure-Lean searches to generate certificates.

The fast path also includes `createsFiveFast`: it checks only the at most 20 five-cell windows
that contain the proposed move. `createsFiveFast_sound` and `createsFiveFast_complete` establish
its equivalence to forming a five-run when the parent board has no such run, and
`createsFiveFast_terminal_iff` connects it to the terminal winner under legal-turn hypotheses.
Executable regressions cover horizontal, vertical, both diagonals, an edge window, and an
insufficient-three-stone counterexample. These are performance and consistency checks, not a
global 15x15 strategy certificate.

For future transposition tables, `PositionKey` stores the side to move together with a lossless
225-cell vector. `boardKey_eq_iff` and `positionKey_eq_iff` prove that equal keys mean equal
boards or positions; `containsPositionKey` provides the executable table-membership primitive.
The base `SearchMemo` adapter exposes a fuel/target/position key and checked hit and miss
lemmas. `Gomoku.Engine` adds a `Std.HashMap` transposition table, carries it through recursive
AND/OR search and iterative deepening, and keeps node-limit cutoffs distinct from completed
negative searches so a cutoff is never cached as failure. `engineTacticalCandidateMoves`
uses the local at-most-20-window detector for immediate wins and forced blocks while retaining
every legal candidate. At target-player nodes, `engineProverCandidateMoves` searches only an
available immediate win or a forced one-ply defense before considering quiet moves; opponent
nodes still enumerate every legal reply. `maxProverMoves` optionally makes target-side search
selective, while `maxMemoEntries` prevents new cache entries after a hard insertion limit and
reports skipped stores. A positive width limit may miss a win, but cannot certify a false one:
`runCheckedEngine` recompiles a found tree and accepts it only after
`checkLocalCertificateAt`; `runCheckedEngine_sound` is the theorem-facing boundary.

The external `cpp/gomoku_solver` keeps the same proof boundary while moving the expensive
search state to flat bitboards and a native transposition table. Its iterative bounded-depth
DFPN treats target turns as OR nodes and opponent turns as AND nodes. Opponent nodes always
enumerate every legal move; target-only selective options may miss a proof but cannot make a
false candidate pass Lean. A separately budgeted VCF oracle recognizes immediate wins and
continuous-four lines, then moves its preferred target move to the front of DFPN without
removing any opponent reply. The exporter writes parent-before-child `CompactCertificate`
data, not a new certificate representation. `Gomoku.Generated.CppSmoke` checks a two-node
immediate win, `Gomoku.Generated.CppFork` checks a five-node opponent tree, and
`Gomoku.Generated.CppVcf` checks a six-node open-four line covering both legal defenses.
Build and CLI details are in [`cpp/README.md`](cpp/README.md).

Build with:

```text
lake build
```

Build and run the C++ regressions on Windows with:

```powershell
powershell.exe -NoProfile -ExecutionPolicy Bypass -File .\cpp\build.ps1 -Clean
.\cpp\build\gomoku_tests.exe
```
