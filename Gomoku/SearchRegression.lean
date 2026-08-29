import Gomoku.Search

namespace Gomoku

/-
Executable regression checks for the untrusted candidate generator.  These
examples deliberately live outside `Gomoku.Search`: the core search API and
its theorems should compile without the large executable reductions used by
the 15x15 regression cases.  Importing this module still runs every check in
the normal `Gomoku` build.
-/

example : allCoords.size = 225 := by
  native_decide

example : allCoords[0]? = some ((0, 0) : Coord) := by
  native_decide

example : allCoords[112]? = some ((7, 7) : Coord) := by
  native_decide

example : allCoords[224]? = some ((14, 14) : Coord) := by
  native_decide

example : coordIndex ((0, 0) : Coord) = 0 := by
  native_decide

example : coordIndex ((7, 7) : Coord) = 112 := by
  native_decide

example : coordIndex ((14, 14) : Coord) = 224 := by
  native_decide

example (c : Coord) : coordAtIndex (coordIndex c) = c := by
  exact coordAtIndex_coordIndex c

example : boardKey Board.empty = boardKey Board.empty := by
  rfl

example : positionKey initialPosition = positionKey initialPosition := by
  rfl

example :
    containsPositionKey #[positionKey initialPosition] initialPosition = true := by
  native_decide

example :
    containsPositionKey #[positionKey initialPosition]
      (play initialPosition (7, 7)) = false := by
  native_decide

example : positionKey initialPosition ≠ positionKey (play initialPosition (7, 7)) := by
  intro h
  have hturn := congrArg Prod.fst h
  have hne : (Player.black : Player) ≠ Player.white := by decide
  apply hne
  simpa [positionKey, initialPosition, Position.initial, play, Position.play] using hturn

example (s : Position) (p : Player) (c : Coord) :
    (winningCellsMask s p).get (coordIndex c) = true ↔
      c ∈ WinningCells s p := by
  exact winningCellsMask_get_iff s p c

example : (candidateMoves initialPosition .black).size = 225 := by
  native_decide

example : (candidateMovesFast initialPosition .black).size = 225 := by
  native_decide

example : ((7, 7) : Coord) ∈ candidateMoves initialPosition .black := by
  native_decide

example : (candidateMoves initialPosition .white).size = 0 := by
  native_decide

example : (candidateMovesFast initialPosition .white).size = 0 := by
  native_decide

example :
    (candidateMoves (play initialPosition (7, 7)) .white).size = 224 := by
  native_decide

example :
    (candidateMovesFast (play initialPosition (7, 7)) .white).size = 224 := by
  native_decide

example :
    (orderedCandidateMoves (play initialPosition (7, 7)) .white).size = 224 := by
  native_decide

example :
    (orderedCandidateMoves (play initialPosition (7, 7)) .white)[0]? =
      some ((6, 6) : Coord) := by
  native_decide

example :
    ((0, 0) : Coord) ∈
      orderedCandidateMoves (play initialPosition (7, 7)) .white := by
  native_decide

example :
    ((7, 7) : Coord) ∉ candidateMoves (play initialPosition (7, 7)) .white := by
  native_decide

example : (candidateMoves searchTerminalPosition .white).size = 0 := by
  native_decide

example : (firstWinningMove searchImmediatePosition .black).isSome := by
  native_decide

example :
    firstWinningMoveReference searchImmediatePosition .black =
      firstWinningMove searchImmediatePosition .black := by
  native_decide

example :
    terminal (play searchImmediatePosition (4, 7)) = some .blackWin := by
  apply createsFiveFast_terminal_of_immediateCandidate
    (s := searchImmediatePosition) (p := .black) (m := (4, 7))
  · native_decide
  · native_decide

example :
    (immediateWinningMovesFirst searchImmediatePosition .black)[0]? =
      some ((4, 7) : Coord) := by
  native_decide

example :
    (immediateWinningMovesFirst searchImmediatePosition .black).size = 221 := by
  native_decide

example : (immediateCertificateFor searchImmediatePosition .black).isSome := by
  native_decide

example : immediateCertificateNodesChecked searchImmediatePosition .black = true := by
  native_decide

example : CanForceWin searchImmediatePosition .black := by
  apply immediateCertificateNodesChecked_sound
  native_decide

example : createsFiveFast searchImmediateBoard .black (4, 7) = true := by
  native_decide

example : createsFiveFast fastVerticalBoard .black (7, 7) = true := by
  native_decide

example : createsFiveFast fastDiagonalUpBoard .black (7, 7) = true := by
  native_decide

example : createsFiveFast fastDiagonalDownBoard .black (7, 2) = true := by
  native_decide

example : createsFiveFast fastBoundaryBoard .black (4, 0) = true := by
  native_decide

example : createsFiveFast fastInsufficientBoard .black (8, 7) = false := by
  native_decide

example : ¬ hasAtLeastFive fastInsufficientBoard .black := by
  native_decide

example :
    createsFiveFast searchImmediateBoard .black (4, 7) = true ↔
      hasAtLeastFive (searchImmediateBoard.place (4, 7) .black) .black := by
  exact createsFiveFast_iff (by native_decide)

example :
    createsFiveFast searchImmediateBoard .black (4, 7) = true ↔
      terminal (play ⟨searchImmediateBoard, .black⟩ (4, 7)) = some .blackWin := by
  apply createsFiveFast_terminal_iff
    (s := ⟨searchImmediateBoard, .black⟩) (p := .black) (m := (4, 7))
  · rfl
  · native_decide

end Gomoku
