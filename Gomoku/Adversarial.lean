import Gomoku.Search

namespace Gomoku

/-!
This file contains executable counterexamples and regression checks for the
semantic audit.  These are tests, not theorems used as the trusted proof of
the 15x15 first-player result.  `native_decide` is intentionally confined to
this test-oriented module.
-/

def auditCenter : Coord := (7, 7)

def occupiedCenter : Position := Position.play initialPosition auditCenter

example : occupiedCenter.turn = .white := by
  rfl

example : ¬ legalMove occupiedCenter auditCenter := by
  native_decide

/- `play` is deliberately a raw board update.  The legality predicate must
be checked before using it as a game move. -/
example : (play occupiedCenter auditCenter).board.cell auditCenter = .stone .white := by
  rfl

def horizontalThreeWithWhiteEnd : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (5, 7) .black) (6, 7) .black)
      (7, 7) .black)
    (8, 7) .white

/- This is an intentional audit witness: the raw geometric predicate sees the
resulting pattern even though the move overwrites an occupied cell.  The
semantic wrapper must therefore carry a legality premise. -/
example : straightOpenFour
    (play ⟨horizontalThreeWithWhiteEnd, .black⟩ (8, 7)).board
    .black (5, 7) .horizontal := by
  native_decide

example : ¬ legalMove ⟨horizontalThreeWithWhiteEnd, .black⟩ (8, 7) := by
  native_decide

def horizontalThreeOpenBoard : Board :=
  Board.place
    (Board.place
      (Board.place Board.empty (5, 7) .black) (6, 7) .black)
    (7, 7) .black

def horizontalBrokenThreeBoard : Board :=
  Board.place
    (Board.place
    (Board.place Board.empty (5, 7) .black) (6, 7) .black)
    (8, 7) .black

/- Only the two horizontal endpoints and the internal gap are empty; every
   other cell is occupied so the opponent has exactly two legal replies after
   Black fills the broken-three gap. -/
def forcedBrokenThreeBoard : Board :=
  ⟨fun c =>
    if c = (4, 7) ∨ c = (7, 7) ∨ c = (9, 7) then
      .empty
    else if c = (5, 7) ∨ c = (6, 7) ∨ c = (8, 7) then
      .stone .black
    else
      if (c.1.1 + 2 * c.2.1) % 5 < 2 then .stone .black else .stone .white⟩

def forcedBrokenThreePosition : Position := ⟨forcedBrokenThreeBoard, .black⟩

def horizontalJumpFourBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (5, 7) .black) (6, 7) .black)
      (7, 7) .black)
    (9, 7) .black

def boundaryBrokenThreeBoard : Board :=
  Board.place
    (Board.place
      (Board.place Board.empty (0, 7) .black) (1, 7) .black)
    (3, 7) .black

def auditFourBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (5, 7) .black) (6, 7) .black)
      (7, 7) .black)
    (8, 7) .black

example : CanForceWin ⟨auditFourBoard, .black⟩ .black := by
  apply singleOpenFour_forces_win_minimal (s := ⟨auditFourBoard, .black⟩)
  · rfl
  · change ¬ Position.isTerminal ⟨auditFourBoard, .black⟩
    native_decide
  · native_decide

/- A positive multi-layer certificate exercises the complete prover-move path:
   the parent is non-terminal, the move is legal, the child index is strictly
   larger, and the referenced child is exactly the resulting terminal position.
   This is deliberately a local certificate; its root is not the empty board,
   so it is not a claim about the global 15x15 theorem. -/
def twoLayerRoot : Position := ⟨auditFourBoard, .black⟩

def twoLayerMove : Coord := (9, 7)

def twoLayerCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[
      .proverMove twoLayerRoot twoLayerMove 1,
      .terminal (play twoLayerRoot twoLayerMove) .blackWin
    ] }

example :
    checkNodeAt .black twoLayerCertificate.nodes 0
      (.proverMove twoLayerRoot twoLayerMove 1) = true := by
  native_decide

example :
    checkNodeAt .black twoLayerCertificate.nodes 1
      (.terminal (play twoLayerRoot twoLayerMove) .blackWin) = true := by
  native_decide

theorem twoLayerCertificate_nodes_checked :
    ∀ i (hi : i < twoLayerCertificate.nodes.size),
      checkNodeAt .black twoLayerCertificate.nodes i
        twoLayerCertificate.nodes[i] = true := by
  intro i hi
  have hi' : i = 0 ∨ i = 1 := by
    simp [twoLayerCertificate] at hi ⊢
    omega
  rcases hi' with h0 | h1
  · subst i
    have hcheck :
        checkNodeAt .black twoLayerCertificate.nodes 0
          (.proverMove twoLayerRoot twoLayerMove 1) = true := by
      native_decide
    simpa [twoLayerCertificate] using hcheck
  · subst i
    have hcheck :
        checkNodeAt .black twoLayerCertificate.nodes 1
          (.terminal (play twoLayerRoot twoLayerMove) .blackWin) = true := by
      native_decide
    simpa [twoLayerCertificate] using hcheck

example : Nonempty (CertificateTree .black twoLayerRoot) := by
  exact compact_reify_at twoLayerCertificate .black 0 (by native_decide)
    twoLayerCertificate_nodes_checked

example : CanForceWin twoLayerRoot .black := by
  exact CertificateTree.sound
    (Classical.choice (compact_reify_at twoLayerCertificate .black 0
      (by native_decide) twoLayerCertificate_nodes_checked))

example : CanForceWin twoLayerRoot .black := by
  apply immediateWinCertificate_sound (s := twoLayerRoot) (p := .black)
    (m := twoLayerMove)
  · rfl
  · native_decide
  · native_decide

/- A local opponent-node certificate exercises the universal-response path.
   The position has exactly two empty points, both endpoints of a black four;
   whichever point White fills, Black wins by filling the other endpoint. -/
def opponentForkBoard : Board :=
  ⟨fun c =>
    if c = (4, 7) ∨ c = (9, 7) then
      .empty
    else if c = (5, 7) ∨ c = (6, 7) ∨ c = (7, 7) ∨ c = (8, 7) then
      .stone .black
    else
      if (c.1.1 + 2 * c.2.1) % 5 < 2 then .stone .black else .stone .white⟩

def opponentForkPosition : Position := ⟨opponentForkBoard, .white⟩

def opponentForkCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[
      .opponentMoves opponentForkPosition #[((4, 7), 1), ((9, 7), 2)],
      .proverMove (play opponentForkPosition (4, 7)) (9, 7) 3,
      .proverMove (play opponentForkPosition (9, 7)) (4, 7) 4,
      .terminal (play (play opponentForkPosition (4, 7)) (9, 7)) .blackWin,
      .terminal (play (play opponentForkPosition (9, 7)) (4, 7)) .blackWin
    ] }

example : Board.emptyCount opponentForkBoard = 2 := by
  native_decide

example : terminal opponentForkPosition = none := by
  native_decide

/- The same two-empty-point position is also a direct executable witness for
   the semantic double-threat theorem.  Unlike `WinningMoves`,
   `WinningCells` does not require it to be the target's turn: the set records
   the two cells that Black can win on after White has replied. -/
example : (WinningCells opponentForkPosition .black).card = 2 := by
  native_decide

example : HasDoubleThreat opponentForkPosition .black := by
  native_decide

example : ∃ m, m ∈ WinningCells opponentForkPosition .black ∧ m ≠ (4, 7) := by
  apply winningCell_ne_of_hasDoubleThreat
  native_decide

example : ¬ HasImmediateWin opponentForkPosition .white := by
  native_decide

example : CanForceWin opponentForkPosition .black := by
  apply doubleThreat_forces_win (s := opponentForkPosition) (p := .black)
  · rfl
  · native_decide
  · native_decide
  · native_decide

/- A move-level witness: Black fills the centre of a cross-shaped gap.  The
   resulting position has horizontal and vertical four-lines, hence at least
   two immediate winning cells, while the move itself is not yet terminal. -/
def createdDoubleThreatBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place
          (Board.place
            (Board.place Board.empty (5, 7) .black) (6, 7) .black)
          (8, 7) .black)
        (7, 5) .black)
      (7, 6) .black)
    (7, 8) .black

def createdDoubleThreatPosition : Position :=
  ⟨createdDoubleThreatBoard, .black⟩

def createdDoubleThreatMove : Coord := (7, 7)

example : legalMove createdDoubleThreatPosition createdDoubleThreatMove := by
  native_decide

example : terminal (play createdDoubleThreatPosition createdDoubleThreatMove) = none := by
  native_decide

example : ¬ HasImmediateWin
    (play createdDoubleThreatPosition createdDoubleThreatMove) .white := by
  native_decide

example : HasDoubleThreat
    (play createdDoubleThreatPosition createdDoubleThreatMove) .black := by
  native_decide

example : CanForceWin createdDoubleThreatPosition .black := by
  apply doubleThreat_move_forces_win
    (s := createdDoubleThreatPosition) (p := .black)
    (m := createdDoubleThreatMove)
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide

example :
    checkNodeAt .black opponentForkCertificate.nodes 0
      (.opponentMoves opponentForkPosition #[((4, 7), 1), ((9, 7), 2)]) = true := by
  native_decide

example :
    checkNodeAt .black opponentForkCertificate.nodes 1
      (.proverMove (play opponentForkPosition (4, 7)) (9, 7) 3) = true := by
  native_decide

example :
    checkNodeAt .black opponentForkCertificate.nodes 2
      (.proverMove (play opponentForkPosition (9, 7)) (4, 7) 4) = true := by
  native_decide

example :
    checkNodeAt .black opponentForkCertificate.nodes 3
      (.terminal (play (play opponentForkPosition (4, 7)) (9, 7)) .blackWin) = true := by
  native_decide

example :
    checkNodeAt .black opponentForkCertificate.nodes 4
      (.terminal (play (play opponentForkPosition (9, 7)) (4, 7)) .blackWin) = true := by
  native_decide

theorem opponentForkCertificate_nodes_checked :
    ∀ i (hi : i < opponentForkCertificate.nodes.size),
      checkNodeAt .black opponentForkCertificate.nodes i
        opponentForkCertificate.nodes[i] = true := by
  intro i hi
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
    simp [opponentForkCertificate] at hi ⊢
    omega
  rcases hi' with h0 | h1 | h2 | h3 | h4
  · subst i
    have hcheck :
        checkNodeAt .black opponentForkCertificate.nodes 0
          (.opponentMoves opponentForkPosition #[((4, 7), 1), ((9, 7), 2)]) = true := by
      native_decide
    simpa [opponentForkCertificate] using hcheck
  · subst i
    have hcheck :
        checkNodeAt .black opponentForkCertificate.nodes 1
          (.proverMove (play opponentForkPosition (4, 7)) (9, 7) 3) = true := by
      native_decide
    simpa [opponentForkCertificate] using hcheck
  · subst i
    have hcheck :
        checkNodeAt .black opponentForkCertificate.nodes 2
          (.proverMove (play opponentForkPosition (9, 7)) (4, 7) 4) = true := by
      native_decide
    simpa [opponentForkCertificate] using hcheck
  · subst i
    have hcheck :
        checkNodeAt .black opponentForkCertificate.nodes 3
          (.terminal (play (play opponentForkPosition (4, 7)) (9, 7)) .blackWin) = true := by
      native_decide
    simpa [opponentForkCertificate] using hcheck
  · subst i
    have hcheck :
        checkNodeAt .black opponentForkCertificate.nodes 4
          (.terminal (play (play opponentForkPosition (9, 7)) (4, 7)) .blackWin) = true := by
      native_decide
    simpa [opponentForkCertificate] using hcheck

example : Nonempty (CertificateTree .black opponentForkPosition) := by
  have htree := compact_reify_at opponentForkCertificate .black 0 (by native_decide)
    opponentForkCertificate_nodes_checked
  have hroot : nodePosition opponentForkCertificate.nodes[0] = opponentForkPosition := by
    rfl
  simpa [hroot] using htree

example : CanForceWin opponentForkPosition .black := by
  have htree := compact_reify_at opponentForkCertificate .black 0 (by native_decide)
    opponentForkCertificate_nodes_checked
  have hroot : nodePosition opponentForkCertificate.nodes[0] = opponentForkPosition := by
    rfl
  exact CertificateTree.sound (Classical.choice (by simpa [hroot] using htree))

/- A certificate may share a child node.  Here the first opponent reply is
   listed twice and both entries reference the same prover subtree.  Duplicate
   reply entries are harmless because coverage is a membership condition; the
   checker still validates the shared node and its position once per edge. -/
def sharedSubtreeCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[
      .opponentMoves opponentForkPosition
        #[((4, 7), 1), ((4, 7), 1), ((9, 7), 2)],
      .proverMove (play opponentForkPosition (4, 7)) (9, 7) 3,
      .proverMove (play opponentForkPosition (9, 7)) (4, 7) 4,
      .terminal (play (play opponentForkPosition (4, 7)) (9, 7)) .blackWin,
      .terminal (play (play opponentForkPosition (9, 7)) (4, 7)) .blackWin
    ] }

example : checkLocalCertificateAt opponentForkPosition
    sharedSubtreeCertificate = true := by
  native_decide

example : CanForceWin opponentForkPosition .black := by
  apply local_certificate_at_sound opponentForkPosition sharedSubtreeCertificate
  native_decide

/- The generic two-ply generator accepts the same response table and feeds it
   through the local checker.  This is the first regression test for the
   reusable search-to-certificate adapter, rather than a hand-written node
   array. -/
def generatedForkCertificate : CompactCertificate :=
  twoPlyImmediateCertificate opponentForkPosition .black
    #[((4, 7), (9, 7)), ((9, 7), (4, 7))]

example : checkLocalCertificate generatedForkCertificate = true := by
  native_decide

example : CanForceWin opponentForkPosition .black := by
  exact twoPlyImmediateCertificate_sound
    (s := opponentForkPosition) (p := .black)
    (responses := #[((4, 7), (9, 7)), ((9, 7), (4, 7))]) (by
      native_decide)

example : (twoPlyCertificateFor opponentForkPosition .black).isSome := by
  native_decide

/- A fixed candidate tree exercises the general tree-to-array compiler without
   making every library build rerun the more expensive depth search. -/
def opponentForkCandidateTree : CandidateTree :=
  .opponentMoves opponentForkPosition [
    ((4, 7), .proverMove (play opponentForkPosition (4, 7)) (9, 7)
      (.terminal (play (play opponentForkPosition (4, 7)) (9, 7)))),
    ((9, 7), .proverMove (play opponentForkPosition (9, 7)) (4, 7)
      (.terminal (play (play opponentForkPosition (9, 7)) (4, 7))))
  ]

def compiledForkCertificate : CompactCertificate :=
  candidateTreeCertificate .black opponentForkCandidateTree

example : checkLocalCertificateAt opponentForkPosition compiledForkCertificate = true := by
  native_decide

example : CanForceWin opponentForkPosition .black := by
  apply local_certificate_at_sound opponentForkPosition compiledForkCertificate
  native_decide

/- After the fast candidate enumeration was introduced, this small recursive
   search is cheap enough to keep as a smoke test.  It still proves nothing by
   itself: `checkedDepthCertificateFor` accepts the result only after the same
   local certificate and root checks used above. -/
example : (checkedDepthCertificateFor 2 opponentForkPosition .black).isSome := by
  native_decide

/- The checker must reject an opponent node that omits one legal reply.  The
   root position has exactly two empty points, so listing only one child is a
   genuine coverage failure rather than an alternative strategy encoding. -/
def missingReplyCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[
      .opponentMoves opponentForkPosition #[((4, 7), 1)],
      .proverMove (play opponentForkPosition (4, 7)) (9, 7) 2,
      .terminal (play (play opponentForkPosition (4, 7)) (9, 7)) .blackWin
    ] }

example : checkLocalCertificate missingReplyCertificate = false := by
  native_decide

/- Out-of-range references and child-position mismatches are rejected even
   when the move labels themselves look plausible. -/
def badReferenceCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[
      .opponentMoves opponentForkPosition #[((4, 7), 99), ((9, 7), 2)],
      .proverMove (play opponentForkPosition (9, 7)) (4, 7) 3,
      .terminal (play (play opponentForkPosition (9, 7)) (4, 7)) .blackWin,
      .terminal (play (play opponentForkPosition (9, 7)) (4, 7)) .blackWin
    ] }

example : checkLocalCertificate badReferenceCertificate = false := by
  native_decide

def badChildPositionCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[
      .opponentMoves opponentForkPosition #[((4, 7), 1), ((9, 7), 2)],
      .proverMove opponentForkPosition (9, 7) 3,
      .proverMove (play opponentForkPosition (9, 7)) (4, 7) 4,
      .terminal (play (play opponentForkPosition (9, 7)) (4, 7)) .blackWin,
      .terminal (play (play opponentForkPosition (9, 7)) (4, 7)) .blackWin
    ] }

example : checkLocalCertificate badChildPositionCertificate = false := by
  native_decide

def badTerminalLabelCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[
      .opponentMoves opponentForkPosition #[((4, 7), 1), ((9, 7), 2)],
      .proverMove (play opponentForkPosition (4, 7)) (9, 7) 3,
      .proverMove (play opponentForkPosition (9, 7)) (4, 7) 4,
      .terminal (play (play opponentForkPosition (4, 7)) (9, 7)) .whiteWin,
      .terminal (play (play opponentForkPosition (9, 7)) (4, 7)) .blackWin
    ] }

example : checkLocalCertificate badTerminalLabelCertificate = false := by
  native_decide

/- A geometric double open three is not, by itself, the same as an
   *immediate* winning move after every defense.  The cross below creates a
   horizontal and a vertical straight open three when Black plays the center.
   White can block one endpoint; Black then has a remaining open-three
   extension, but no one-move five.  This guards the semantic boundary between
   `GeometricDoubleOpenThree` and the deliberately stronger
   `ImmediateSafeDoubleOpenThree`.
 -/
def crossForkBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (6, 7) .black) (8, 7) .black)
      (7, 6) .black)
    (7, 8) .black

def crossForkPosition : Position := ⟨crossForkBoard, .black⟩

def crossForkMove : Coord := (7, 7)

def crossForkDefense : Coord := (5, 7)

example : GeometricDoubleOpenThree crossForkPosition .black crossForkMove := by
  native_decide

/- The cross fork has several distinct one-ply four extensions, even though
   none of them is an immediate five.  This is the intended intermediate
   threat layer between geometric open threes and `WinningCells`. -/
example : HasDoubleFourThreat
    (play crossForkPosition crossForkMove) .black := by
  native_decide

example :
    ∃ m, m ∈ FourExtensionCells
      (play crossForkPosition crossForkMove).board .black := by
  exact straightOpenThree_has_fourExtension
    (by native_decide :
      straightOpenThree
        (play crossForkPosition crossForkMove).board .black (6, 7) .horizontal)

example : legalMove (play crossForkPosition crossForkMove) crossForkDefense := by
  native_decide

theorem crossFork_no_immediate_win :
    ¬ HasImmediateWin
      (play (play crossForkPosition crossForkMove) crossForkDefense) .black := by
  intro hwin
  have hcard :
      (WinningMoves
        (play (play crossForkPosition crossForkMove) crossForkDefense) .black).card = 0 := by
    native_decide
  have hpos : 0 <
      (WinningMoves
        (play (play crossForkPosition crossForkMove) crossForkDefense) .black).card :=
    Finset.card_pos.mpr hwin
  omega

example : ¬ ImmediateSafeDoubleOpenThree crossForkPosition .black crossForkMove := by
  intro hsafe
  have hafter := hsafe.2.2.2 crossForkDefense (by native_decide)
  exact crossFork_no_immediate_win hafter

/- A geometric double open three can coexist with an opponent's immediate
   win.  The white four is deliberately placed away from the black cross, so
   the example isolates the semantic condition rather than relying on an
   accidental overlap. -/
def crossWithWhiteFourBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place
          (Board.place
            (Board.place
              (Board.place
                (Board.place Board.empty (6, 7) .black) (8, 7) .black)
              (7, 6) .black)
            (7, 8) .black)
          (3, 3) .white)
        (4, 3) .white)
      (5, 3) .white)
    (6, 3) .white

def crossWithWhiteFourPosition : Position :=
  ⟨crossWithWhiteFourBoard, .black⟩

def crossWithWhiteFourMove : Coord := (7, 7)

example : GeometricDoubleOpenThree
    crossWithWhiteFourPosition .black crossWithWhiteFourMove := by
  native_decide

example : DoubleOpenThree
    crossWithWhiteFourPosition .black crossWithWhiteFourMove := by
  native_decide

example : OpponentHasImmediateWin
    (play crossWithWhiteFourPosition crossWithWhiteFourMove) .black := by
  native_decide

example : ¬ SafeDoubleOpenThree
    crossWithWhiteFourPosition .black crossWithWhiteFourMove := by
  apply not_safeDoubleOpenThree_of_opponentImmediate
  native_decide

example : ¬ ImmediateSafeDoubleOpenThree
    crossWithWhiteFourPosition .black crossWithWhiteFourMove := by
  apply not_immediateSafeDoubleOpenThree_of_opponentImmediate
  native_decide

/- A four-extension threat is not an immediate winning cell: after the cross
   move, the immediate winning-cell set is empty, while the four-threat set
   has at least two elements. -/
example : (WinningMoves
    (play crossForkPosition crossForkMove) .black).card = 0 := by
  native_decide

/- The overlap relation is executable, and the corresponding uniqueness
   theorem rejects a second start inside the same straight run. -/
example : StartShiftConflict 3 (5, 7) (6, 7) .horizontal := by
  native_decide

example :
    ¬ (straightOpenThree horizontalThreeOpenBoard .black (5, 7) .horizontal ∧
      straightOpenThree horizontalThreeOpenBoard .black (6, 7) .horizontal) := by
  intro h
  exact straightOpenThree_not_startShiftConflict h.1 h.2 (by native_decide)

example : StartShiftConflict 4 (5, 7) (6, 7) .horizontal := by
  native_decide

example :
    ¬ (straightOpenFour auditFourBoard .black (5, 7) .horizontal ∧
      straightOpenFour auditFourBoard .black (6, 7) .horizontal) := by
  intro h
  exact straightOpenFour_not_startShiftConflict h.1 h.2 (by native_decide)

example : MoveCreatesSingleOpenFour
    ⟨horizontalThreeOpenBoard, .black⟩ .black (8, 7) := by
  native_decide

example : ¬ MoveCreatesSingleOpenFour
    ⟨horizontalThreeWithWhiteEnd, .black⟩ .black (8, 7) := by
  native_decide

example : (openFourWitnesses
    (play ⟨horizontalThreeOpenBoard, .black⟩ (8, 7)).board .black).card = 1 := by
  native_decide

example : (openThreeWitnesses horizontalThreeOpenBoard .black).card = 1 := by
  native_decide

example : brokenOpenThree horizontalBrokenThreeBoard .black (5, 7) .horizontal := by
  native_decide

example : ¬ straightOpenThree horizontalBrokenThreeBoard .black (5, 7) .horizontal := by
  native_decide

example : ∃ m, m ∈ FourExtensionCells horizontalBrokenThreeBoard .black := by
  exact brokenOpenThree_has_fourExtension
    (c := (5, 7)) (d := .horizontal) (by native_decide)

example : straightOpenFour
    (horizontalBrokenThreeBoard.place (7, 7) .black)
    .black (5, 7) .horizontal := by
  native_decide

example : (7, 7) ∈ OpenFourExtensionCells
    horizontalBrokenThreeBoard .black (5, 7) .horizontal := by
  native_decide

example : ∃ w, w ∈ WinningCells
    ⟨horizontalBrokenThreeBoard.place (7, 7) .black, .white⟩ .black := by
  exact openFourExtension_has_winningCell
    (c := (5, 7)) (d := .horizontal) (m := (7, 7)) (by native_decide)

example : BrokenOpenThreeMove
    ⟨horizontalBrokenThreeBoard, .black⟩ .black (7, 7) := by
  native_decide

example : Board.emptyCount forcedBrokenThreeBoard = 3 := by
  native_decide

example : terminal forcedBrokenThreePosition = none := by
  native_decide

example : brokenOpenThree forcedBrokenThreeBoard .black (5, 7) .horizontal := by
  native_decide

example : GeometricBrokenOpenThree forcedBrokenThreePosition .black (7, 7) := by
  native_decide

example : terminal (play forcedBrokenThreePosition (7, 7)) = none := by
  native_decide

example : ¬ OpponentHasImmediateWin
    (play forcedBrokenThreePosition (7, 7)) .black := by
  native_decide

example : ImmediateSafeBrokenOpenThree
    forcedBrokenThreePosition .black (7, 7) := by
  native_decide

example : CanForceWin forcedBrokenThreePosition .black := by
  exact immediateSafeBrokenOpenThree_forces_win
    (m := (7, 7)) (by native_decide)

example : ∃ w, w ∈ WinningCells
    (play ⟨horizontalBrokenThreeBoard, .black⟩ (7, 7)) .black := by
  exact brokenOpenThreeMove_creates_winningCell (by native_decide)

example : ¬ hasAtLeastFive
    (horizontalBrokenThreeBoard.place (7, 7) .black) .black := by
  native_decide

example : jumpFour horizontalJumpFourBoard .black (5, 7) .horizontal := by
  native_decide

example : ¬ straightOpenFour horizontalJumpFourBoard .black (5, 7) .horizontal := by
  native_decide

example : CanForceWin ⟨horizontalJumpFourBoard, .black⟩ .black := by
  rcases jumpFour_black_immediate
      (s := ⟨horizontalJumpFourBoard, .black⟩) (c := (5, 7)) (d := .horizontal)
      rfl (by
        change ¬ Position.isTerminal ⟨horizontalJumpFourBoard, .black⟩
        native_decide) (by native_decide) with ⟨m, hm, hwin⟩
  exact canForceWin_immediate hm hwin rfl

example : ¬ brokenOpenThree boundaryBrokenThreeBoard .black (0, 7) .horizontal := by
  native_decide

def boundaryThreeBoard : Board :=
  Board.place
    (Board.place
      (Board.place Board.empty (0, 7) .black) (1, 7) .black)
    (2, 7) .black

example : ¬ straightOpenThree boundaryThreeBoard .black (0, 7) .horizontal := by
  native_decide

example : MaximalRun boundaryThreeBoard .black (0, 7) .horizontal 3 := by
  native_decide

example : MaximalRun horizontalThreeOpenBoard .black (5, 7) .horizontal 3 := by
  exact straightOpenThree_maximalRun (by native_decide)

example : MaximalRun auditFourBoard .black (5, 7) .horizontal 4 := by
  exact straightOpenFour_maximalRun (by native_decide)

example :
    (MaximalRun horizontalThreeOpenBoard .black (5, 7) .horizontal 3 ∧
      MaximalRun horizontalThreeOpenBoard .black (5, 7) .horizontal 3) →
      ((5, 7) : Coord) = ((5, 7) : Coord) := by
  intro h
  exact maximalRun_unique_of_comparable h.1 h.2 (by left; rfl)

def verticalFourBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (7, 3) .black) (7, 4) .black)
      (7, 5) .black)
    (7, 6) .black

def diagonalDownFourBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (3, 6) .black) (4, 5) .black)
      (5, 4) .black)
    (6, 3) .black

example : straightOpenFour verticalFourBoard .black (7, 3) .vertical := by
  native_decide

example : straightOpenFour diagonalDownFourBoard .black (3, 6) .diagonalDown := by
  native_decide

def auditOverlineBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place
          (Board.place Board.empty (4, 7) .black) (5, 7) .black)
        (6, 7) .black)
      (7, 7) .black)
    (8, 7) .black

example : hasAtLeastFive auditOverlineBoard .black := by
  native_decide

example : (openFourWitnesses auditOverlineBoard .black).card = 0 := by
  native_decide

example : ¬ legalMove ⟨auditOverlineBoard, .white⟩ auditCenter := by
  native_decide

/- A malformed compact certificate with no nodes must be rejected. -/
example : checkCertificate { target := .black, root := 0, nodes := #[] } = false := by
  rfl

/- The checker is target-specific: a white target is not an initial black-win
certificate, even before any node-level reasoning is attempted. -/
example : checkCertificate { target := .white, root := 0, nodes := #[] } = false := by
  rfl

def cycleCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[.proverMove initialPosition auditCenter 0] }

example : checkCertificate cycleCertificate = false := by
  native_decide

def wrongRootCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[.terminal ⟨auditOverlineBoard, .white⟩ .blackWin] }

example : checkCertificate wrongRootCertificate = false := by
  native_decide

example : CanForceWin ⟨auditOverlineBoard, .white⟩ .black := by
  apply CertificateTree.sound
  apply checkNode_terminal_reify (target := .black) (size := 1)
    (s := ⟨auditOverlineBoard, .white⟩) (out := .blackWin)
  native_decide

/- A compact one-node terminal certificate is accepted by the same checker
   used for larger DAG certificates, and its soundness is proved through the
   reifier rather than by a test-only shortcut. -/
def oneNodeTerminalCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[.terminal ⟨auditOverlineBoard, .white⟩ .blackWin] }

example : checkCertificate oneNodeTerminalCertificate = false := by
  native_decide

example : Nonempty (CertificateTree .black ⟨auditOverlineBoard, .white⟩) := by
  apply compact_reify_at oneNodeTerminalCertificate .black 0 (by native_decide)
  intro i hi
  have hi0 : i = 0 := by
    simpa [oneNodeTerminalCertificate] using hi
  subst i
  have hcheck :
      checkNodeAt .black oneNodeTerminalCertificate.nodes 0
        (.terminal ⟨auditOverlineBoard, .white⟩ .blackWin) = true := by
    native_decide
  simpa [oneNodeTerminalCertificate] using hcheck

example : samePosition initialPosition initialPosition = true := by
  exact samePosition_self _

example : samePosition initialPosition occupiedCenter = false := by
  native_decide

def oneMoveReference : Array (Coord × Nat) := #[(auditCenter, 1)]

example : moveInBool oneMoveReference auditCenter = true := by
  native_decide

end Gomoku
