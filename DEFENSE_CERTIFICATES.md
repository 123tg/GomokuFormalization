# Defense certificates: preventing the opponent's win

This document describes the defense-certificate layer added on top of the
fixed 7×7 main line.  It is the formal counterpart of the "mutual defense"
route to `StandardDraw`.

## Mathematical semantics

* `CanPreventWin defender s` (inductive Prop, `Gomoku.Defense`):
  the defender has a strategy from `s` so that the attacker (`defender.other`)
  can never win.  Terminal nodes close only for **draw** or **defender win**;
  defender nodes are existential (one move), attacker nodes are universal
  (every legal move must be answered).
* `WhiteCanPreventBlackWin s := CanPreventWin .white s`
* `BlackCanPreventWhiteWin s := CanPreventWin .black s`
* `StandardDraw s := ¬ CanForceWin s .black ∧ ¬ CanForceWin s .white`
  — the classical game-theoretic draw region: neither player can force their
  own win.  This is **not** defined as the conjunction of the two defense
  predicates; instead the real theorem
  `standardDraw_of_mutualDefense : WhiteCanPreventBlackWin s →
  BlackCanPreventWhiteWin s → StandardDraw s` is proved via
  `canPrevent_not_canForceWin` (structural recursion aligning the defense
  tree against the forcing-win tree; terminal nodes contradict by the
  uniqueness of the terminal outcome).

## Compact certificate and checker

```lean
inductive DefenseCertificateNode
  | terminal (position : Position) (outcome : Outcome)
  | defenderMove (position : Position) (move : Coord) (child : Nat)
  | attackerMoves (position : Position) (children : Array (Coord × Nat))

structure DefenseCertificate where
  defender : Player
  root : Nat
  nodes : Array DefenseCertificateNode
```

`checkDefenseCertificateAt s c` recomputes everything itself — it never trusts
the searcher:

* `terminal` node: `terminal s = some out` **and** `out = winner defender` or
  `out = .draw` (an attacker-win terminal such as `BlackWin` for
  `defender = .white` is rejected);
* `defenderMove`: `terminal s = none`, `s.turn = defender`, `legalMove s m`,
  `parent < child < nodes.size`, child position = `play s m`;
* `attackerMoves`: `terminal s = none`, `s.turn = defender.other`, every edge
  legal and in range, **move set equality** with the legal-move set
  (missing, duplicate, and illegal replies all rejected), every child
  `parent < child` with position `play s m`.

`parent < child` everywhere rules out self-loops, back edges, and cycles.

## Soundness

`defense_reify_at` rebuilds a dependent `DefenseTree` from a checked compact
certificate by well-founded recursion on `nodes.size - i`; then

```lean
theorem defense_certificate_sound (s) (c) (h : checkDefenseCertificateAt s c = true) :
    CanPreventWin c.defender s

theorem white_defense_certificate_sound ... : WhiteCanPreventBlackWin s
theorem black_defense_certificate_sound ... : BlackCanPreventWhiteWin s
```

## Trusted boundary

```
C++ search (untrusted)  →  DefenseCertificate (untrusted data)
        ↓
Lean checker (recomputes position, turn, terminal, legality, all replies)
        ↓
soundness theorem + kernel  →  WhiteCanPreventBlackWin / BlackCanPreventWhiteWin
        ↓
standardDraw_of_mutualDefense  →  StandardDraw
```

The C++ side (`--prove prevent-black-win | prevent-white-win`) runs a complete
AND/OR proof search with strict tri-state status: `found` only when every
attacker reply is answered, `refuted` only when the whole subtree was
exhausted, and `unknown` whenever any limit (node/table/certificate) was hit —
`unknown` is never cached and never exported as a certificate.

## Current results

* Small positions: C++ exports certificates that Lean checks and turns into
  real theorems (`Gomoku/Generated/PreventWhiteFour.lean`,
  `Gomoku/Generated/PreventBlackTwoGaps.lean`).
* `Gomoku/DefenseAudit.lean`: positive certificates (terminal draw, defender
  win, two-reply full coverage) and the full negative battery; all run through
  `native_decide` on the trusted Bool checker.
* Empty 7×7 board: both defense searches return `unknown` within the tried
  budgets (≈40M expanded nodes, 50M transposition entries, depth 49 reached).
  **No empty-board theorem is claimed.**  Generating `PreventBlackWin7x7.lean`,
  `PreventWhiteWin7x7.lean`, and `Draw7x7.lean` for the empty board remains
  blocked on completing the search (or on a strategy-level formal proof such
  as a pairing argument).
