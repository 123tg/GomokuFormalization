# Current baseline status

The main branch model is fixed to 7×7, five-in-a-row, Black first, standard
rules (both players win on five; draw on a full board).

| Area | Current status |
|---|---|
| Core types and rules | Migrated to 49 cells |
| Row-major coordinates | `index = y * 7 + x`, inverse theorems retained |
| Certificate checker | Uses the migrated 7×7 `Position`; safety checks retained |
| Lean/C++ local bridge | One generated `CppSmoke` certificate retained |
| Defense semantics | `CanPreventWin` / `WhiteCanPreventBlackWin` / `BlackCanPreventWhiteWin` / `StandardDraw` formalized in `Gomoku.Defense` |
| Defense certificate | `DefenseCertificate` + independent checker `checkDefenseCertificateAt` + soundness theorems (`defense_certificate_sound`, `white_defense_certificate_sound`, `black_defense_certificate_sound`) |
| Mutual defense | `standardDraw_of_mutualDefense` proved: two defense certificates imply `StandardDraw` |
| Defense audit | `Gomoku.DefenseAudit` negative tests (missing/duplicate/illegal reply, wrong/losing terminal, bad child, back edge, wrong board/turn/root) and small positive certificates |
| C++ defense mode | `--prove prevent-black-win \| prevent-white-win` with strict `found / refuted / unknown` propagation and Lean export |
| Closed loop | Small positions: C++ exports `DefenseCertificate`, Lean checker passes (`PreventWhiteFour.lean`, `PreventBlackTwoGaps.lean`) |
| Pure strategy-level proof (strategy stealing) | `Gomoku.Stealing`: determinacy lemma `not_canForceWin_implies_canPreventWin`, shadow-game simulation `ShadowSim`, and `black_can_prevent_white_initial : BlackCanPreventWhiteWin initialPosition` — the first player can force at least a draw on the empty 7×7 board, proved by pure strategy-level reasoning (no search, no certificate). Also `white_cannot_force_win_initial` |
| Pairing framework | `Gomoku.Pairing`: `Pairing`/`disjoint`/`pairProper`/`respondsTo`/`CoversWindows`/`ValidAt`/`Invariant` + `pairingStrategySound` (well-founded, works at any black-turn position) + `pairing_strategy_sound_empty`. Fix 2026-08-30: coverage now ranges over **full** windows only (`windowFull` guard) — partial boundary windows can never contain a pair, so the old definition made `ValidAt` unsatisfiable; soundness proof updated (`no_black_five_of_noBlackPair_and_valid` supplies the full-window witness from a black five) |
| 7×7 mid-game pairing theorems | `Gomoku.Generated.PreventBlackWinMidgame`: 6 machine-checked theorems `WhiteCanPreventBlackWin s` for three 4-stone positions (black (0,0), white (3,3), black m2, white r2; covering pairings found by `find_pairing --depth4`) and their 3-stone predecessors (`defenderMove` + pairing leaf). First pairing-leaf theorems on the real 7×7 board |
| 7×7 static pairing | Exhaustive backtracking (88k nodes) shows no static pairing covers all 60 five-windows of 7×7; `Gomoku.Pairing` therefore remains a conditional framework |
| Standard draw certificate (mid-game) | **`Gomoku.Generated.Draw7x7`: `draw7x7StandardDraw : StandardDraw draw7x7RootPosition` — a real draw theorem, machine-checked.** Root: 21 black + 21 white stones, black to move, 7 empties; every 5-window contains both colors, so neither side can ever win. C++ `DefenseSearcher` emits both certificates (white defense 400 nodes, black defense 158 nodes); Lean checker verifies both and `standardDraw_of_mutualDefense` combines them |
| Full 7×7 opening solve | Not completed: both empty-board defense searches return `unknown` (limits), so no empty-board theorem is claimed |
| Standard draw certificate for the empty board | Not generated (depends on the empty-board searches) |

See [`AUDIT_REPORT.md`](AUDIT_REPORT.md) for the migration audit and
[`PROJECT_GUIDE.md`](PROJECT_GUIDE.md) for the current architecture.
