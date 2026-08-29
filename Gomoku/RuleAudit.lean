import Gomoku.Certificate

namespace Gomoku

/-!
Executable rule and certificate regressions which do not depend on a searcher.

The named theorems in the rule/game modules form the trusted mathematical
interface.  The `native_decide` examples below are adversarial test cases: they
make boundary choices and malformed inputs concrete, but are not used by the
soundness proofs.
-/

private def boardWithStones (p : Player) (stones : List Coord) : Board :=
  stones.foldl (fun b c => b.place c p) Board.empty

def auditHorizontalFive : Board :=
  boardWithStones .black [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0)]

def auditVerticalFive : Board :=
  boardWithStones .black [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4)]

def auditDiagonalUpFive : Board :=
  boardWithStones .black [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4)]

def auditDiagonalDownFive : Board :=
  boardWithStones .black [(0, 14), (1, 13), (2, 12), (3, 11), (4, 10)]

def auditSixInRow : Board :=
  boardWithStones .black [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0)]

example : hasAtLeastFive auditHorizontalFive .black := by native_decide
example : hasAtLeastFive auditVerticalFive .black := by native_decide
example : hasAtLeastFive auditDiagonalUpFive .black := by native_decide
example : hasAtLeastFive auditDiagonalDownFive .black := by native_decide

/- This pair catches the common mutation from "at least five" to "a maximal
   run of exactly five": the six-stone run wins, but its five-stone prefix is
   not maximal. -/
example : hasAtLeastFive auditSixInRow .black := by native_decide
example : MaximalRun auditSixInRow .black (0, 0) .horizontal 6 := by native_decide
example : ¬ MaximalRun auditSixInRow .black (0, 0) .horizontal 5 := by native_decide

/- A period-four colouring chosen so that every one of the four Gomoku
   directions changes residue and no monochromatic run reaches length five. -/
private def auditCoordAtIndex (i : Fin 225) : Coord :=
  (⟨i.1 / 15, by omega⟩, ⟨i.1 % 15, by omega⟩)

private def auditAllCoords : List Coord :=
  List.ofFn auditCoordAtIndex

private def auditBlackCoords : List Coord :=
  auditAllCoords.filter (fun c => (c.1.1 + 2 * c.2.1) % 4 < 2)

private def auditWhiteCoords : List Coord :=
  auditAllCoords.filter (fun c => ¬ ((c.1.1 + 2 * c.2.1) % 4 < 2))

private def alternateAuditMoves : List Coord → List Coord → List Coord
  | [], ws => ws
  | bs, [] => bs
  | b :: bs, w :: ws => b :: w :: alternateAuditMoves bs ws

private def auditDrawMoves : List Coord :=
  alternateAuditMoves auditBlackCoords auditWhiteCoords

def auditDrawPosition : Position :=
  Position.playMoves Position.initial auditDrawMoves

def auditDrawBoard : Board := auditDrawPosition.board

theorem auditDraw_moves_length : auditDrawMoves.length = 225 := by
  native_decide

theorem auditDraw_black_count : auditBlackCoords.length = 113 := by
  native_decide

theorem auditDraw_white_count : auditWhiteCoords.length = 112 := by
  native_decide

theorem auditDraw_moves_legal :
    Position.LegalMoveSequence Position.initial auditDrawMoves := by
  native_decide

theorem auditDraw_reachable :
    Reachable auditDrawPosition := by
  exact Position.reachable_playMoves Position.Reachable.initial
    auditDrawMoves auditDraw_moves_legal

theorem auditDraw_replay_eq :
    Position.playMoves Position.initial auditDrawMoves = auditDrawPosition := by
  rfl

theorem auditDraw_reachable_position : Reachable auditDrawPosition := by
  exact auditDraw_reachable

set_option maxRecDepth 100000 in
theorem auditDraw_emptyCount_balance :
    Board.emptyCount auditDrawPosition.board + auditDrawMoves.length =
      Board.emptyCount Position.initial.board := by
  exact Position.playMoves_emptyCount_add_length auditDraw_moves_legal

example : Board.emptyCount auditDrawPosition.board = 0 := by native_decide

/- Compute the expensive full-board classification once.  The remaining
   assertions reuse this result instead of independently rescanning all 225
   cells and all four directions. -/
theorem auditDraw_terminal : terminal auditDrawPosition = some .draw := by
  native_decide

theorem auditDraw_full : Board.full auditDrawBoard := by
  exact (Position.terminal_draw_iff.mp auditDraw_terminal).2.2

theorem auditDraw_no_black_five : ¬ hasAtLeastFive auditDrawBoard .black := by
  exact (Position.terminal_draw_iff.mp auditDraw_terminal).1

theorem auditDraw_no_white_five : ¬ hasAtLeastFive auditDrawBoard .white := by
  exact (Position.terminal_draw_iff.mp auditDraw_terminal).2.1

example : Board.full auditDrawBoard := auditDraw_full
example : ¬ hasAtLeastFive auditDrawBoard .black := auditDraw_no_black_five
example : ¬ hasAtLeastFive auditDrawBoard .white := auditDraw_no_white_five
example : terminal auditDrawPosition = some .draw := auditDraw_terminal
example (c : Coord) : ¬ legalMove auditDrawPosition c := by
  exact Position.terminal_outcome_no_legal auditDraw_terminal c

example : Position.countBlack auditDrawPosition = 113 := by
  native_decide

example : Position.countWhite auditDrawPosition = 112 := by
  native_decide

example : terminal auditDrawPosition = none ↔ ¬ Position.isTerminal auditDrawPosition := by
  exact Position.terminal_none_iff

example : terminal auditDrawPosition ≠ none ↔ Position.isTerminal auditDrawPosition := by
  exact Position.terminal_ne_none_iff

example : ¬ CanForceWin auditDrawPosition .black := by
  apply not_canForceWin_of_terminal_ne (out := .draw) auditDraw_terminal
  decide

example : ¬ CanForceWin auditDrawPosition .white := by
  apply not_canForceWin_of_terminal_ne (out := .draw) auditDraw_terminal
  decide

def auditWhiteFive : Board :=
  boardWithStones .white [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0)]

def auditWhiteWinPosition : Position := ⟨auditWhiteFive, .black⟩

example : terminal auditWhiteWinPosition = some .whiteWin := by native_decide

example : ¬ CanForceWin auditWhiteWinPosition .black := by
  apply not_canForceWin_of_terminal_ne (out := .whiteWin) (by native_decide)
  decide

/- Terminal classification has an explicit precedence: a Black win is checked
   before a White win, and either win is checked before a draw.  Reachable
   games cannot produce these malformed combinations, but the rule function
   is total on arbitrary boards and this ordering is part of its contract. -/
def auditBothWinnersBoard : Board :=
  boardWithStones .black [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0)]
    |>.place (10, 0) .white
    |>.place (10, 1) .white
    |>.place (10, 2) .white
    |>.place (10, 3) .white
    |>.place (10, 4) .white

example : hasAtLeastFive auditBothWinnersBoard .black := by native_decide
example : hasAtLeastFive auditBothWinnersBoard .white := by native_decide
example : terminal ⟨auditBothWinnersBoard, .black⟩ = some .blackWin := by
  native_decide

def auditFullWinningBoard : Board :=
  auditDrawBoard.place (2, 0) .black |>.place (3, 0) .black

example : Board.full auditFullWinningBoard := by native_decide
example : hasAtLeastFive auditFullWinningBoard .black := by native_decide
example : terminal ⟨auditFullWinningBoard, .white⟩ = some .blackWin := by
  native_decide

/- Runs ending at the opposite board edges catch asymmetric boundary bugs. -/
def auditRightEdgeHorizontalFive : Board :=
  boardWithStones .black [(10, 0), (11, 0), (12, 0), (13, 0), (14, 0)]

def auditTopEdgeDiagonalFive : Board :=
  boardWithStones .black [(10, 4), (11, 3), (12, 2), (13, 1), (14, 0)]

example : hasAtLeastFive auditRightEdgeHorizontalFive .black := by native_decide
example : hasAtLeastFive auditTopEdgeDiagonalFive .black := by native_decide

def auditGappedFive : Board :=
  boardWithStones .black [(0, 0), (1, 0), (2, 0), (4, 0), (5, 0)]

example : ¬ hasAtLeastFive auditGappedFive .black := by native_decide

/- A nine-ply alternating history gives a genuinely reachable immediate win,
   unlike isolated board fixtures whose stone counts need not match a game
   history. -/
def auditReachableWinMoves : List Coord :=
  [(7, 7), (0, 0), (8, 7), (0, 1), (9, 7), (0, 2), (10, 7), (0, 3), (11, 7)]

def auditReachableWinPosition : Position :=
  Position.playMoves Position.initial auditReachableWinMoves

theorem auditReachableWin_moves_legal :
    Position.LegalMoveSequence Position.initial auditReachableWinMoves := by
  native_decide

theorem auditReachableWin_reachable : Reachable auditReachableWinPosition := by
  exact Position.reachable_playMoves Position.Reachable.initial
    auditReachableWinMoves auditReachableWin_moves_legal

theorem auditReachableWin_terminal :
    terminal auditReachableWinPosition = some .blackWin := by
  native_decide

example : Position.countBlack auditReachableWinPosition = 5 := by native_decide
example : Position.countWhite auditReachableWinPosition = 4 := by native_decide
example : auditReachableWinPosition.turn = .white := by rfl
example (c : Coord) : ¬ legalMove auditReachableWinPosition c := by
  exact Position.terminal_outcome_no_legal auditReachableWin_terminal c

/- A second alternating history gives a reachable non-terminal position in
   which White has the immediate winning move.  This catches proofs that only
   work for isolated, count-inconsistent board fixtures. -/
def auditReachableOpponentThreatMoves : List Coord :=
  [(0, 0), (3, 3), (0, 1), (4, 3), (0, 2), (5, 3), (0, 3), (6, 3), (14, 14)]

def auditReachableOpponentThreatPosition : Position :=
  Position.playMoves Position.initial auditReachableOpponentThreatMoves

def auditReachableOpponentWinningMove : Coord := (7, 3)

theorem auditReachableOpponentThreat_moves_legal :
    Position.LegalMoveSequence Position.initial auditReachableOpponentThreatMoves := by
  native_decide

theorem auditReachableOpponentThreat_reachable :
    Reachable auditReachableOpponentThreatPosition := by
  exact Position.reachable_playMoves Position.Reachable.initial
    auditReachableOpponentThreatMoves auditReachableOpponentThreat_moves_legal

theorem auditReachableOpponentThreat_nonterminal :
    terminal auditReachableOpponentThreatPosition = none := by
  native_decide

theorem auditReachableOpponentThreat_legal :
    legalMove auditReachableOpponentThreatPosition auditReachableOpponentWinningMove := by
  exact ⟨Position.not_isTerminal_of_terminal_none
    auditReachableOpponentThreat_nonterminal, by native_decide⟩

theorem auditReachableOpponentThreat_wins :
    terminal (play auditReachableOpponentThreatPosition
      auditReachableOpponentWinningMove) = some .whiteWin := by
  native_decide

example : Position.countBlack auditReachableOpponentThreatPosition = 5 := by
  native_decide

example : Position.countWhite auditReachableOpponentThreatPosition = 4 := by
  native_decide

example : ¬ CanForceWin auditReachableOpponentThreatPosition .black := by
  apply not_canForceWin_of_opponent_immediate
    (target := .black) (m := auditReachableOpponentWinningMove)
    auditReachableOpponentThreat_nonterminal rfl auditReachableOpponentThreat_legal
    auditReachableOpponentThreat_wins

/- Non-terminal immediate-threat position: White has four stones and one empty
   winning endpoint, so White can win on the next move.  The target is Black,
   but it is White's turn; the generic game theorem must reject Black's claim
   without needing a searcher. -/
def auditOpponentThreatBoard : Board :=
  boardWithStones .white [(3, 3), (4, 3), (5, 3), (6, 3)]

def auditOpponentThreatPosition : Position :=
  ⟨auditOpponentThreatBoard, .white⟩

def auditOpponentWinningMove : Coord := (7, 3)

theorem auditOpponentThreat_nonterminal :
    terminal auditOpponentThreatPosition = none := by
  native_decide

example : legalMove auditOpponentThreatPosition auditOpponentWinningMove := by
  exact ⟨Position.not_isTerminal_of_terminal_none auditOpponentThreat_nonterminal, by
    native_decide⟩

theorem auditOpponentThreat_wins :
    terminal (play auditOpponentThreatPosition auditOpponentWinningMove) = some .whiteWin := by
  native_decide

example : ¬ CanForceWin auditOpponentThreatPosition .black := by
  apply not_canForceWin_of_opponent_immediate
    auditOpponentThreat_nonterminal rfl (by
      exact ⟨Position.not_isTerminal_of_terminal_none auditOpponentThreat_nonterminal, by
        native_decide⟩)
    auditOpponentThreat_wins

/- The opponent-node equivalence exposes the universal branch directly. -/
example : CanForceWin auditOpponentThreatPosition .black ↔
    ∀ m, legalMove auditOpponentThreatPosition m →
      CanForceWin (play auditOpponentThreatPosition m) .black := by
  apply canForceWin_opponent_iff auditOpponentThreat_nonterminal rfl

/- A positive one-move game case: Black has four consecutive stones and the
   empty endpoint is legal.  The move creates a terminal Black win, after
   which every further move is rejected. -/
def auditImmediateWinBoard : Board :=
  boardWithStones .black [(3, 8), (4, 8), (5, 8), (6, 8)]

def auditImmediateWinPosition : Position :=
  ⟨auditImmediateWinBoard, .black⟩

def auditImmediateWinningMove : Coord := (7, 8)

theorem auditImmediateWin_nonterminal :
    terminal auditImmediateWinPosition = none := by
  native_decide

theorem auditImmediateWin_legal :
    legalMove auditImmediateWinPosition auditImmediateWinningMove := by
  exact ⟨Position.not_isTerminal_of_terminal_none auditImmediateWin_nonterminal, by
    native_decide⟩

theorem auditImmediateWin_terminal :
    terminal (play auditImmediateWinPosition auditImmediateWinningMove) =
      some .blackWin := by
  native_decide

/- The target-node equivalence exposes the existential branch directly. -/
example : CanForceWin auditImmediateWinPosition .black ↔
    ∃ m, legalMove auditImmediateWinPosition m ∧
      CanForceWin (play auditImmediateWinPosition m) .black := by
  apply canForceWin_target_iff auditImmediateWin_nonterminal rfl

/- A deliberately incomplete universal witness cannot be used as a proof:
   White's immediate winning move is legal, but the resulting child is not a
   Black win. -/
example : ¬ CanForceWin
    (play auditOpponentThreatPosition auditOpponentWinningMove) .black := by
  apply not_canForceWin_of_terminal_ne (out := .whiteWin)
    auditOpponentThreat_wins
  decide

example : CanForceWin auditImmediateWinPosition .black := by
  exact canForceWin_immediate auditImmediateWin_legal
    auditImmediateWin_terminal rfl

example (c : Coord) :
    ¬ legalMove (play auditImmediateWinPosition auditImmediateWinningMove) c := by
  exact Position.terminal_outcome_no_legal auditImmediateWin_terminal c

example : (play auditImmediateWinPosition auditImmediateWinningMove).turn = .white := rfl

example : Position.countBlack (play auditImmediateWinPosition auditImmediateWinningMove) = 5 := by
  native_decide

example : Position.countWhite (play auditImmediateWinPosition auditImmediateWinningMove) = 0 := by
  native_decide

/- Coordinates are bounded by their type; no run-time out-of-board coordinate
   can be supplied to the public rule interface. -/
example (c : Coord) : c.1.1 < 15 ∧ c.2.1 < 15 := ⟨c.1.2, c.2.2⟩

def auditFirstPosition : Position := play initialPosition (7, 7)

example : Reachable auditFirstPosition := by
  exact Position.Reachable.step Position.Reachable.initial (by native_decide)

example : auditFirstPosition.turn = .white := rfl
example : auditFirstPosition.board.cell (7, 7) = .stone .black := by native_decide
example : ¬ legalMove auditFirstPosition (7, 7) := by native_decide

example : auditFirstPosition.board.cell (6, 7) = .empty := by
  exact Position.play_preserves_other_cells (by native_decide) (by native_decide)

/- These two positions have impossible turn/count combinations and therefore
   cannot be produced from the empty board by legal alternating play. -/
def auditWrongInitialTurn : Position := ⟨Board.empty, .white⟩

example : ¬ Reachable auditWrongInitialTurn := by
  intro hreach
  have hinv : Position.countBlack auditWrongInitialTurn =
      Position.countWhite auditWrongInitialTurn + 1 := by
    simpa [auditWrongInitialTurn] using Position.reachable_count_invariant hreach
  have hb : Position.countBlack auditWrongInitialTurn = 0 := by native_decide
  have hw : Position.countWhite auditWrongInitialTurn = 0 := by native_decide
  omega

def auditWhiteStoneBlackTurn : Position :=
  ⟨Board.place Board.empty (7, 7) .white, .black⟩

example : ¬ Reachable auditWhiteStoneBlackTurn := by
  intro hreach
  have hinv : Position.countBlack auditWhiteStoneBlackTurn =
      Position.countWhite auditWhiteStoneBlackTurn := by
    simpa [auditWhiteStoneBlackTurn] using Position.reachable_count_invariant hreach
  have hb : Position.countBlack auditWhiteStoneBlackTurn = 0 := by native_decide
  have hw : Position.countWhite auditWhiteStoneBlackTurn = 1 := by native_decide
  omega

/- A valid local terminal certificate is accepted.  It is deliberately local:
   its root is not the empty initial board. -/
def auditWinningPosition : Position := ⟨auditHorizontalFive, .white⟩

def auditValidTerminalCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[.terminal auditWinningPosition .blackWin] }

example : checkLocalCertificateAt auditWinningPosition
    auditValidTerminalCertificate = true := by native_decide

example : CanForceWin auditWinningPosition .black := by
  exact local_certificate_at_sound auditWinningPosition
    auditValidTerminalCertificate (by native_decide)

/- A complete one-move certificate contains the non-terminal choice and its
   terminal child.  This is the smallest end-to-end certificate a searcher
   should be able to emit. -/
def auditImmediateWinCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[
      .proverMove auditImmediateWinPosition auditImmediateWinningMove 1,
      .terminal
        (play auditImmediateWinPosition auditImmediateWinningMove) .blackWin
    ] }

example : checkLocalCertificateAt auditImmediateWinPosition
    auditImmediateWinCertificate = true := by
  native_decide

example : CanForceWin auditImmediateWinPosition .black := by
  exact local_certificate_at_sound auditImmediateWinPosition
    auditImmediateWinCertificate (by native_decide)

/- This is the intended global-checker bridge.  It does not claim that such a
   full initial-board certificate exists yet; it records exactly what follows
   once a searcher supplies one which passes `checkCertificate`. -/
example (c : CompactCertificate) (h : checkCertificate c = true) :
    CanForceWin initialPosition .black :=
  compact_certificate_sound c h

/- Terminal certificate nodes may represent only a win by the certificate's
   target.  Consequently a draw leaf is necessarily rejected; a "valid
   winning certificate containing a draw branch" would contradict the
   meaning of `CanForceWin`. -/
def auditDrawLeafCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[.terminal auditDrawPosition .draw] }

example : checkLocalCertificateAt auditDrawPosition
    auditDrawLeafCertificate = false := by
  cases hcheck : checkLocalCertificateAt auditDrawPosition
      auditDrawLeafCertificate with
  | false => rfl
  | true =>
      have hparts : checkLocalCertificate auditDrawLeafCertificate = true ∧
          localRootPositionMatches auditDrawPosition auditDrawLeafCertificate = true := by
        simpa [checkLocalCertificateAt,
          Bool.and_eq_true_eq_eq_true_and_eq_true] using hcheck
      have hlocal : checkLocalCertificate auditDrawLeafCertificate = true := hparts.1
      have hnodes := checkLocalCertificate_nodes_checked
        auditDrawLeafCertificate hlocal
      have hnode := hnodes 0 (by native_decide)
      have hvalid := (checkNodeAt_terminal_iff .black
        auditDrawLeafCertificate.nodes 0 auditDrawPosition .draw).mp (by
          simpa [auditDrawLeafCertificate] using hnode)
      have : Outcome.draw = winner (.black : Player) := hvalid.2
      cases this

/- Relabelling a genuine draw as a Black win also fails: the checker recomputes
   the position outcome instead of trusting the supplied label. -/
def auditDrawAsBlackWinCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[.terminal auditDrawPosition .blackWin] }

example : checkLocalCertificateAt auditDrawPosition
    auditDrawAsBlackWinCertificate = false := by
  native_decide

def auditNonterminalLeafCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[.terminal initialPosition .blackWin] }

example : checkLocalCertificateAt initialPosition
    auditNonterminalLeafCertificate = false := by native_decide

example : checkLocalCertificate auditValidTerminalCertificate = true := by
  native_decide

/- The local checker must bind the certificate root to the supplied position;
   accepting a valid certificate at a different root would make local tactic
   results unsound. -/
example : checkLocalCertificateAt initialPosition
    auditValidTerminalCertificate = false := by
  native_decide

def auditOpponentWinLeafCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[.terminal auditWhiteWinPosition .whiteWin] }

example : checkLocalCertificateAt auditWhiteWinPosition
    auditOpponentWinLeafCertificate = false := by native_decide

/- Relabelling an opponent win as the target's win is rejected for the same
   reason: terminal outcomes are derived from the board. -/
def auditOpponentWinAsBlackCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[.terminal auditWhiteWinPosition .blackWin] }

example : checkLocalCertificateAt auditWhiteWinPosition
    auditOpponentWinAsBlackCertificate = false := by
  native_decide

/- The parent has White to move but its only listed move overwrites Black's
   occupied centre.  The child reference is in range and forward, so rejection
   specifically exercises move legality rather than index validation. -/
def auditIllegalMoveCertificate : CompactCertificate :=
  { target := .white
    root := 0
    nodes := #[
      .proverMove auditFirstPosition (7, 7) 1,
      .terminal (play auditFirstPosition (7, 7)) .whiteWin
    ] }

example : checkLocalCertificate auditIllegalMoveCertificate = false := by
  native_decide

/- A prover node is also rejected when the certificate target does not match
   the side to move. -/
def auditWrongTurnCertificate : CompactCertificate :=
  { target := .white
    root := 0
    nodes := #[
      .proverMove initialPosition (7, 7) 1,
      .terminal (play initialPosition (7, 7)) .whiteWin
    ] }

example : checkLocalCertificate auditWrongTurnCertificate = false := by
  native_decide

/- Direct node-level checks isolate the two prover preconditions.  These tests
   remain invalid even if the edge checker is changed, so a mutation of the
   legality or turn conjunct is observable. -/
example : checkNode .white 2
    (.proverMove auditFirstPosition (7, 7) 1) = false := by
  native_decide

example : checkNode .white 2
    (.proverMove initialPosition (7, 7) 1) = false := by
  native_decide

example : checkNode .black 1
    (.proverMove auditImmediateWinPosition auditImmediateWinningMove 99) = false := by
  native_decide

/- A nearly full period-four board has exactly one legal point.  Listing that
   point makes the coverage conjunct true, so the following rejection isolates
   an opponent-node turn mismatch. -/
def auditSingleEmptyBoard : Board :=
  ⟨fun c => if c = (14, 14) then .empty else auditDrawBoard.cell c⟩

def auditSingleEmptyPosition : Position :=
  ⟨auditSingleEmptyBoard, .black⟩

def auditSingleEmptyWhitePosition : Position :=
  ⟨auditSingleEmptyBoard, .white⟩

def auditSingleEmptyReplies : Array (Coord × Nat) := #[( (14, 14), 1)]

example : terminal auditSingleEmptyPosition = none := by
  native_decide

example : checkNode .black 2
    (.opponentMoves auditSingleEmptyPosition auditSingleEmptyReplies) = false := by
  native_decide

def auditOpponentEdgeMismatchNodes : Array CertificateNode := #[
  .opponentMoves auditSingleEmptyWhitePosition #[((14, 14), 1)],
  .terminal auditSingleEmptyWhitePosition .blackWin
]

example : checkNodeAt .black auditOpponentEdgeMismatchNodes 0
    (.opponentMoves auditSingleEmptyWhitePosition #[((14, 14), 1)]) = false := by
  native_decide

def auditProverEdgeMismatchNodes : Array CertificateNode := #[
  .proverMove auditImmediateWinPosition auditImmediateWinningMove 1,
  .terminal auditImmediateWinPosition .blackWin
]

example : checkNodeAt .black auditProverEdgeMismatchNodes 0
    (.proverMove auditImmediateWinPosition auditImmediateWinningMove 1) = false := by
  native_decide

/- Root indices and references are data supplied by the untrusted producer.
   Out-of-range roots, self-references and backward references are all
   rejected. -/
def auditBadRootIndexCertificate : CompactCertificate :=
  { target := .black
    root := 4
    nodes := #[.terminal auditWinningPosition .blackWin] }

example : checkLocalCertificate auditBadRootIndexCertificate = false := by
  native_decide

def auditSelfCycleCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[
      .proverMove auditImmediateWinPosition auditImmediateWinningMove 0
    ] }

example : checkLocalCertificate auditSelfCycleCertificate = false := by
  native_decide

def auditBackwardReferenceCertificate : CompactCertificate :=
  { target := .black
    root := 1
    nodes := #[
      .terminal
        (play auditImmediateWinPosition auditImmediateWinningMove) .blackWin,
      .proverMove auditImmediateWinPosition auditImmediateWinningMove 0
    ] }

example : checkLocalCertificate auditBackwardReferenceCertificate = false := by
  native_decide

/- At an opponent node the board must actually have the opponent to move;
   choosing the node tag cannot override the position's turn. -/
def auditWrongOpponentTurnCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[.opponentMoves auditImmediateWinPosition #[]] }

example : checkLocalCertificate auditWrongOpponentTurnCertificate = false := by
  native_decide

end Gomoku
