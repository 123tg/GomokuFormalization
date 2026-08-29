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
classification is now unified by `terminalAfterMoveFast`; an independently proved five-window
Incremental threat updates and larger pure-Lean searches remain future work; the finite-depth reference search
already has a correctness-oriented transposition cache, but it is not a high-performance solver.

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
`SearchMemo` is now used by the finite-depth reference search: the stateful entry point returns a
candidate tree together with the updated table, while the compatibility wrapper starts from an
empty table. The key contains fuel, target, side to move, and the complete lossless board. Hit and
miss lemmas are proved, and `checkedDepthCertificateForCached` still rechecks every cached tree
with the certificate checker. This is a correctness-oriented reference cache, not yet a complete
15x15 high-performance solver.

Build with:

```text
lake build
```
