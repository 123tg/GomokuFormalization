# Fixed 7×7 Migration Audit

## Scope

The current main model is fixed to:

```text
board size = 7 x 7
win length = 5
first player = Black
```

No parallel `Coord7`, `Board7`, `Position7`, or certificate type was added.
The existing types and checker interfaces were migrated directly.

## Core checks

- `Coord = Fin 7 × Fin 7`.
- `coordAtIndex : Fin 49 → Coord` and `coordIndex : Coord → Fin 49`.
- Row-major index is `y * 7 + x`; the proved inverse theorems are retained.
- `allCoords.size = 49`.
- The initial position has 49 empty/legal points, Black to move, and no outcome.
- Win length remains five in all four directions; overlines still win.
- Black win, White win, non-terminal, and full-board draw semantics are retained.
- `PositionKey` and threat masks now cover 49 cells plus the turn.
- `CompactCertificate` uses the migrated `Position` directly.
- Global/local root checks, legal edges, exact child positions, terminal labels,
  forward node ids, cycle rejection, and complete opponent coverage are retained.
- The normal C++ parser accepts exactly seven rows of seven cells.
- Lean and C++ use the same `index = y * 7 + x` convention.

## Test simplification

The former collection of duplicate tactical, performance, mutation, and
generated-certificate audit modules was removed from the main program. A small
`Gomoku.RuleAudit` suite now covers the migration acceptance criteria and the
critical positive/negative certificate boundary. `CppSmoke` is retained as the
single C++-generated Lean certificate regression.

Historical parameterized small-board tools, result files, and their duplicate
smoke script were removed. Only the fixed 7x7 solver and minimal acceptance
tests remain.

## Proof boundary

No complete 7x7 opening result is claimed. Search limits and failed searches
remain `unknown`-style operational results, not draw proofs. C++ validation is
diagnostic; only a passing Lean certificate checker yields `CanForceWin`.

## Build status

The local verification run completed successfully:

- `lake build`: passed;
- clean C++ build: passed;
- `gomoku_tests.exe`: passed;
- regenerated `CppSmoke` certificate: accepted by Lean;
- no new `sorry`, `admit`, `axiom`, or `unsafe` declaration was added.
