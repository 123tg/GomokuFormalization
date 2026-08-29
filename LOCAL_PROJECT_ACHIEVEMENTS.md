# Current project achievements

- The existing Lean model was migrated directly to fixed 7×7 coordinates.
- Five remains the winning length; Black remains the first player.
- All 49 coordinates have a proved row-major encode/decode bijection.
- The complete position key and threat mask cover all 49 cells.
- `CompactCertificate`, `checkCertificate`, and
  `checkLocalCertificateAt` now operate on the 7×7 model without weakening
  legal-move, edge, terminal-label, node-order, or opponent-coverage checks.
- The C++ solver/parser/exporter uses the same board constants and coordinate
  convention as Lean.
- A compact migration audit and a C++-generated Lean smoke certificate are
  retained in the normal build.

Not achieved: a complete empty-board 7×7 win/draw solution or a formally
checked standard-draw certificate. Resource exhaustion remains an unknown
search result, not a theorem.
