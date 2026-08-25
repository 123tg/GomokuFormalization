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
- `Gomoku.Tactics`: immediate winning moves, strict open-three/open-four predicates, and a
  proved straight open-four immediate-win theorem for Black.
- `Gomoku.Certificate`: dependent strategy trees and a compact certificate-checking interface.
- `Gomoku.Examples`: API-level sanity checks, horizontal/diagonal/boundary/overline examples,
  and executable board tests.

The rule layer uses the standard unrestricted semantics: a contiguous line of at least five stones wins immediately, including six or more in a row; a full board without a winner is a draw. Forbidden-move rules are intentionally outside this version.

The global 15x15 first-player theorem is not asserted without a strategy certificate. The
dependent `CertificateTree` interface is sound and can directly establish `CanForceWin`.
`CompactCertificate.checkCertificate` currently provides structural validation (including
legal edges, topological references, and complete opponent coverage); its header facts are
exposed by `checkCertificate_header`. A future verified DAG reifier must connect this compact
checker to `CertificateTree` before a compact certificate can prove the global theorem.

Build with:

```text
lake build
```
