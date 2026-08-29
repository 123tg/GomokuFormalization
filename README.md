# 无禁手五子棋的规则与必胜策略的形式化

完整的项目方案、已完成成果、当前限制和下一步实施路线见
[`PROJECT_GUIDE.md`](PROJECT_GUIDE.md)。下面保留模块和构建命令的简短概览。

搜索器与 Lean 检查器的输入输出、证书节点格式、协作约定和阶段性验收见
[`SEARCHER_INTERFACE.md`](SEARCHER_INTERFACE.md)。

队友 C++ 搜索器与当前主线的隔离构建、样例证书和兼容性实测见
[`TEAM_SEARCHER_COMPATIBILITY.md`](TEAM_SEARCHER_COMPATIBILITY.md)。

This Lean 4 project formalizes a 15x15, unrestricted Gomoku game.

Current modules:

- `Gomoku.Basic`: players, cells, coordinates, boards, and board updates.
- `Gomoku.Geometry`: four board directions, bounded steps, runs, and open-line predicates.
- `Gomoku.Rules`: positions, legal moves, terminal outcomes, reachability, move monotonicity,
  stone-count/turn invariants, and strict empty-cell descent.
- `Gomoku.Game`: strategy types and the inductive `CanForceWin` game semantics.
- `Gomoku.Tactics`: immediate winning moves, strict open-three/open-four predicates, a
  proved color-generic straight open-four immediate-win theorem (with the original
  Black-specialized wrapper retained), a theorem that both endpoints of a straight open
  four are distinct winning cells, and separate
  multi-ply (`SafeDoubleOpenThree`) and immediate-response
  (`ImmediateSafeDoubleOpenThree`) defense-by-defense interfaces.
- `Gomoku.Certificate`: dependent strategy trees and a compact certificate-checking interface.
- `Gomoku.Search`: the untrusted searcher boundary; only checked `CompactCertificate` values
  can cross into the trusted proof layer.
- `Gomoku.Engine`: a budgeted, iterative-deepening AND/OR searcher with forced tactical
  pruning, an optional target-side width limit, an incrementally updated bitboard cache key,
  a bounded hash transposition table, explicit resource statuses and a checked certificate
  boundary. Its cache key includes the complete search configuration.
- `Gomoku.Parametric`: a separate board-size/win-length-parameterized model with an
  executable two-ply searcher, a proved checker boundary, and a checked 5x5 connect-five
  double-threat example. The original 15x15 API is unchanged.
- `cpp/`: an untrusted C++17 iterative DFPN searcher using bitboards, incremental Zobrist
  hashing, a bounded VCF move oracle, resource limits, and direct export to the unchanged
  Lean `CompactCertificate`.
- `Gomoku.Generated`: C++-generated OR/AND/VCF smoke certificates that are accepted by the
  existing Lean checker and connected to `CanForceWin`.
- `terminalAfterMoveFast` in `Gomoku.Search` gives the engine one total move-to-outcome
  computation, with a proved equivalence to the ordinary terminal rule for legal moves from
  non-terminal positions.
- `Gomoku.Bounded`: an executable finite-depth game semantics with a proved soundness and
  empty-cell-depth completeness bridge to `CanForceWin`, plus monotonicity of successful depths
  for iterative deepening.
- `Gomoku.Engine`: a bounded Lean-side AND/OR candidate searcher with iterative depth, tactical
  ordering, forced-defense pruning, memoization, and explicit resource statuses.
- `EngineStats` also records terminal classifications and candidate moves generated, so search
  runs have a reproducible performance baseline in addition to their found/not-found status.
- `Gomoku.Engine` also exposes `EngineCacheLookup`, which distinguishes a cache miss from a
  cached finite-search failure and a cached candidate tree; these states are regression-tested.
- `Gomoku.Examples`: API-level sanity checks, horizontal/diagonal/boundary/overline examples,
  and executable board tests.
- `Gomoku.Adversarial`: executable counterexamples and regression checks from the semantic audit.
- `Gomoku.RuleAudit`: rule, terminal-state, reachability, and malformed-certificate regressions.
- `Gomoku.PatternAudit`: frozen v1 open-three/open-four patterns with four-direction and near-miss regressions.
- `Gomoku.SearchAudit`: normal reachable finite-depth search cases, explicit no-candidate results,
  accepted certificates, a deliberately rejected malformed candidate tree, and comparisons with
  the independent bounded semantics.
- `Gomoku.BoundedAudit`: small regressions showing that insufficient depth can return false while
  the sufficient empty-cell bound agrees with the unbounded game semantics; it also checks draw and
  opponent-immediate-win cases at more than one depth.
- `Gomoku.InteropAudit`: the fixed Lean-side adapter for an external stone-array root plus
  `CompactCertificate`, with accepted and malformed exporter-shaped fixtures. The strict adapter
  additionally rejects duplicate stone coordinates before checking the certificate.
- `Gomoku.EngineAudit`: independent engine regressions for a reachable one-move win, an
  opponent immediate win, a node-budget cutoff, complete two-reply coverage, and a rejected
  certificate that omits one legal reply.
- `Gomoku.TerminalAudit`: regressions for immediate wins, a last-move draw, illegal moves after
  a terminal position, and the fast/ordinary terminal-rule equivalence.
- `Gomoku.MutationAudit`: deliberately wrong rule variants and concrete counterexamples showing
  that six-in-a-row, non-horizontal wins, boundary endpoints, and post-terminal moves are not
  accepted by the formal semantics.
- `Gomoku.Generated.CppSmoke`, `Gomoku.Generated.CppFork`, `Gomoku.Generated.CppVcf`,
  `Gomoku.Generated.CppReachable`, and `Gomoku.Generated.CppReachableDoubleThreat`: small
  certificates emitted by the teammate's C++ searcher and rechecked by Lean. The last two are
  connected to legal histories; `CppReachableDoubleThreat` covers all 208 legal replies in a
  genuine two-threat position.

The rule layer uses the standard unrestricted semantics: a contiguous line of at least five stones wins immediately, including six or more in a row; a full board without a winner is a draw. Forbidden-move rules are intentionally outside this version.

`Gomoku.Parametric` independently packages `boardSize` and `winLength` in `GameSpec`.
Its `fiveByFiveSpec` instantiates a genuine 5x5 connect-five board. The included sparse
double-threat root has 18 legal White replies; `searchTwoPly` covers all 18, the independent
`checkTwoPlyCertificate` accepts the result, and `fiveByFive_black_forces_win` derives the
parameterized `ForceWin` conclusion. This is a local two-ply result, not a solution of the
original empty 15x15 board. The separate exact solver in `cpp/tools/solve5x5.cpp` has now
exhaustively evaluated the empty 5x5 connect-five game as a draw. That is a reproducible
native computation, not yet a Lean theorem; a formally checked draw requires an outcome
certificate interface beyond the current forced-win-only `ForceWin` type.

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
default search currently uses the cheaper immediate-win ordering. The single-move terminal
classification is now unified by `terminalAfterMoveFast`, whose result is proved equivalent to
the ordinary terminal rule under the legal non-terminal preconditions used by the searcher.
Incremental threat updates, cache eviction and certificate DAG sharing remain future work; the
finite-depth reference search already has a correctness-oriented transposition cache, while the
separate Lean engine and C++ DFPN implementation provide the optimized experimental paths.

The finite-depth search also exposes a diagnostic `CheckedDepthResult` interface. It distinguishes
`noCandidate` (no tree found under the current fuel), `rejected` (a generated certificate failed
the trusted checker), and `accepted` (the checker accepted the certificate). Only the accepted
case has a soundness theorem, so a finite search failure is never confused with a proof that a
position is unwinnable.

The fast path also includes `createsFiveFast`: it checks only the at most 20 five-cell windows
that contain the proposed move. `createsFiveFast_sound` and `createsFiveFast_complete` establish
its equivalence to forming a five-run when the parent board has no such run, and
`createsFiveFast_terminal_iff` connects it to the terminal winner under legal-turn hypotheses.
Executable regressions cover horizontal, vertical, both diagonals, an edge window, and an
insufficient-three-stone counterexample. These are performance and consistency checks, not a
global 15x15 strategy certificate.

For transposition tables, `PositionKey` stores the side to move together with a lossless
225-cell vector. `boardKey_eq_iff` and `positionKey_eq_iff` prove that equal keys mean equal
boards or positions; `containsPositionKey` provides the executable table-membership primitive.
The base `SearchMemo` adapter exposes a fuel/target/position key and checked hit and miss
lemmas. It is now used by the finite-depth reference search, whose stateful entry point returns
both the candidate tree and the updated table; cached candidates are still checked at the trusted
boundary. `Gomoku.Engine` adds a `Std.HashMap` transposition table, carries it through recursive
AND/OR search and iterative deepening, and keeps node-limit cutoffs distinct from completed
negative searches so a cutoff is never cached as failure. `engineTacticalCandidateMoves`
uses the local at-most-20-window detector for immediate wins and forced blocks while retaining
every legal candidate. At target-player nodes, `engineProverCandidateMoves` searches only an
available immediate win or a forced one-ply defense before considering quiet moves; opponent
nodes still enumerate every legal reply. `maxProverMoves` optionally makes target-side search
selective, while `maxMemoEntries` prevents new cache entries after a hard insertion limit and
reports skipped stores. A positive width limit may miss a win, but cannot certify a false one:
`runCheckedEngine` recompiles a found tree and accepts it only after
`checkLocalCertificateAt`; `runCheckedEngine_sound` is the theorem-facing boundary. Its
configuration-sensitive compact key prevents a negative result produced by a selective policy
from suppressing a search under another policy, and `EngineCacheLookup` exposes the three cache
states explicitly.

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
