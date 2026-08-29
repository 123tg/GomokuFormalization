# Fixed 7x7 C++ candidate searcher

`cpp/gomoku_solver` is an untrusted C++17 DFPN searcher for the same fixed
rules as the Lean main program:

```text
board size = 7 x 7
win length = 5
first player = Black
```

It may find candidate force-win trees and export Lean source containing a
`CompactCertificate`. A search result becomes a theorem only after Lean runs
`checkCertificate` or `checkLocalCertificateAt`.

## Build and test

From the repository root:

```powershell
powershell.exe -NoProfile -ExecutionPolicy Bypass -File .\cpp\build.ps1 -Clean
.\cpp\build\gomoku_tests.exe
```

The normal build creates only the current 7x7 executables:

```text
cpp/build/gomoku_solver.exe
cpp/build/gomoku_tests.exe
```

The old parameterized 5x5--8x8 programs and result logs were removed. This
directory now contains only the fixed 7x7 main solver and its minimal tests.

## Input format

A position contains `turn`, `target`, and exactly seven rows of seven cells:

```text
turn black
target black
.......
.......
.......
.XXXX..
.......
.......
.......
```

`.` is empty, `X` is Black, and `O` is White. Rows are read in increasing
`y`; characters within a row are read in increasing `x`.

## Coordinates and storage

The fixed constants are:

```cpp
constexpr int boardSize = 7;
constexpr int winLength = 5;
constexpr int boardCells = boardSize * boardSize;
```

The Lean and C++ row-major convention is identical:

```text
index = y * boardSize + x
x = index % boardSize
y = index / boardSize
```

The existing four-word bitboard representation is intentionally retained in
this migration. Only 49 bits are used; simplifying it to one word is an
optional later optimization, not part of the board-size correctness change.

## Run and export

```powershell
.\cpp\build\gomoku_solver.exe `
  --input .\cpp\examples\immediate_win.txt `
  --output .\Gomoku\Generated\CppSmoke.lean `
  --max-depth 1 `
  --definition cppSmoke
```

Important statuses are `found`, `depthLimit`, `nodeLimit`, `tableLimit`, and
`certificateLimit`. Anything other than `found` has no certificate and must
not be reported as a draw or a proof of nonexistence.

Before writing Lean source, `validateCertificate` checks legal edges,
parent-before-child ids, child positions, target terminal labels, and complete
opponent coverage. This C++ validation is diagnostic only; Lean remains the
trusted checker.
