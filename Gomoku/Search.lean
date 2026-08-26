import Gomoku.Certificate

namespace Gomoku

/-!
The searcher boundary is intentionally small.  A search program may use any
algorithm or heuristic, but the only object it may hand to the trusted side is
a `CompactCertificate`.  No search result is a theorem until
`checkCertificate` succeeds in Lean.
-/

structure SearchConfig where
  target : Player := .black
  maxNodes : Nat := 0
  deriving Repr

abbrev Searcher := SearchConfig → Option CompactCertificate

/- The searcher may need a complete executable move list, but this helper is
   deliberately outside the trusted certificate checker.  `Fin 225` indexes
   the 15 by 15 board in row-major order and keeps the generated coordinates
   inside the board by construction. -/
def coordAtIndex (i : Fin 225) : Coord :=
  (⟨i.1 / 15, by omega⟩, ⟨i.1 % 15, by omega⟩)

def allCoords : Array Coord :=
  Array.ofFn coordAtIndex

/- A stable row-major index for a coordinate.  Keeping this inverse to
   `coordAtIndex` lets later search code use O(1) array lookup for masks and
   cached threat information instead of linear `Array.mem` scans. -/
def coordIndex (c : Coord) : Fin 225 :=
  ⟨c.1.1 * 15 + c.2.1, by omega⟩

theorem coordAtIndex_coordIndex (c : Coord) :
    coordAtIndex (coordIndex c) = c := by
  apply Prod.ext
  · apply Fin.ext
    simp [coordAtIndex, coordIndex]
    omega
  · apply Fin.ext
    simp [coordAtIndex, coordIndex]

theorem coordIndex_coordAtIndex (i : Fin 225) :
    coordIndex (coordAtIndex i) = i := by
  apply Fin.ext
  simp [coordAtIndex, coordIndex]
  omega

/- An exact, executable row-major key for transposition tables.  The key is
   intentionally a lossless `Array Cell`, so a later cache cannot merge two
   different board positions by hash collision. -/
abbrev PositionKey := Player × Vector Cell 225

def boardKey (b : Board) : Vector Cell 225 :=
  Vector.ofFn (fun i => b.cell (coordAtIndex i))

def positionKey (s : Position) : PositionKey :=
  (s.turn, boardKey s.board)

theorem boardKey_get (b : Board) (c : Coord) :
    (boardKey b).get (coordIndex c) = b.cell c := by
  simp [boardKey, coordAtIndex_coordIndex]

theorem boardKey_eq_iff (b₁ b₂ : Board) :
    boardKey b₁ = boardKey b₂ ↔ b₁ = b₂ := by
  constructor
  · intro h
    cases b₁ with
    | mk f₁ =>
      cases b₂ with
      | mk f₂ =>
        congr
        funext c
        have hc := congrArg (fun a => a.get (coordIndex c)) h
        simpa [boardKey, coordAtIndex_coordIndex] using hc
  · intro h
    cases h
    rfl

theorem positionKey_eq_iff (s t : Position) :
    positionKey s = positionKey t ↔ s = t := by
  constructor
  · intro h
    have hturn : s.turn = t.turn := by
      simpa [positionKey] using congrArg Prod.fst h
    have hboard : s.board = t.board := by
      exact (boardKey_eq_iff s.board t.board).mp
        (by simpa [positionKey] using congrArg Prod.snd h)
    cases s with
    | mk sb ss =>
      cases t with
      | mk tb ts =>
        simp only at hturn hboard
        cases hturn
        cases hboard
        rfl
  · intro h
    cases h
    rfl

abbrev TranspositionTable := Array PositionKey

def containsPositionKey (table : TranspositionTable) (s : Position) : Bool :=
  table.any (fun k => k = positionKey s)

theorem containsPositionKey_true_iff (table : TranspositionTable) (s : Position) :
    containsPositionKey table s = true ↔
      ∃ i, ∃ (h : i < table.size), table[i] = positionKey s := by
  simp [containsPositionKey]

def candidateMoves (s : Position) (p : Player) : Array Coord :=
  if s.turn = p then
    allCoords.filter (fun c => decide (legalMove s c))
  else
    #[]

/- `candidateMoves` is the simple reference implementation.  The fast
   variant factors the position-level terminal test out of the per-cell
   filter; this matters because a search node may inspect all 225 cells. -/
def candidateMovesFast (s : Position) (p : Player) : Array Coord :=
  if s.turn = p then
    if terminal s = none then
      allCoords.filter (fun c => s.board.cell c = .empty)
    else
      #[]
  else
    #[]

theorem mem_candidateMovesFast_iff (s : Position) (p : Player) (c : Coord) :
    c ∈ candidateMovesFast s p ↔
      s.turn = p ∧ c ∈ allCoords ∧ legalMove s c := by
  by_cases hturn : s.turn = p
  · by_cases hterm : terminal s = none
    · have hnoterm : ¬ IsTerminal s :=
        Position.not_isTerminal_of_terminal_none hterm
      simp only [candidateMovesFast, if_pos hturn, if_pos hterm,
        Array.mem_filter]
      constructor
      · rintro ⟨hmem, hcell⟩
        have hcell' : s.board.cell c = .empty := of_decide_eq_true hcell
        exact ⟨hturn, hmem, ⟨hnoterm, hcell'⟩⟩
      · rintro ⟨_, hmem, hlegal⟩
        exact ⟨hmem, decide_eq_true_eq.mpr hlegal.2⟩
    · have hterm' : IsTerminal s := by
        by_contra hnoterm
        exact hterm (Position.terminal_none_of_not_isTerminal hnoterm)
      simp [candidateMovesFast, hturn, hterm, legalMove]
      intro _ hlegal
      exact hlegal.1 hterm'
  · simp [candidateMovesFast, hturn]

theorem mem_candidateMoves_iff (s : Position) (p : Player) (c : Coord) :
    c ∈ candidateMoves s p ↔
      s.turn = p ∧ c ∈ allCoords ∧ legalMove s c := by
  by_cases hturn : s.turn = p
  · simp [candidateMoves, hturn]
  · simp [candidateMoves, hturn]

theorem mem_candidateMovesFast_iff_mem_candidateMoves (s : Position) (p : Player)
    (c : Coord) :
    c ∈ candidateMovesFast s p ↔ c ∈ candidateMoves s p := by
  rw [mem_candidateMovesFast_iff, mem_candidateMoves_iff]

def neighborSteps : Array (Direction × Int) :=
  #[(.horizontal, -1), (.horizontal, 1),
    (.vertical, -1), (.vertical, 1),
    (.diagonalUp, -1), (.diagonalUp, 1),
    (.diagonalDown, -1), (.diagonalDown, 1)]

def hasOccupiedNeighbor (s : Position) (c : Coord) : Bool :=
  neighborSteps.any (fun x =>
    match step c x.1 x.2 with
    | some q => decide (s.board.cell q ≠ .empty)
    | none => false)

/- Search local moves first, but retain every legal move.  This ordering is
   used only by the untrusted searcher; the theorem below records that it does
   not change the candidate set. -/
def orderedCandidateMoves (s : Position) (p : Player) : Array Coord :=
  let moves := candidateMovesFast s p
  moves.filter (hasOccupiedNeighbor s) ++
    moves.filter (fun c => !(hasOccupiedNeighbor s c))

theorem mem_orderedCandidateMoves_iff (s : Position) (p : Player) (c : Coord) :
    c ∈ orderedCandidateMoves s p ↔ c ∈ candidateMovesFast s p := by
  simp only [orderedCandidateMoves, Array.mem_append, Array.mem_filter]
  by_cases h : hasOccupiedNeighbor s c
  · simp [h]
  · cases hvalue : hasOccupiedNeighbor s c <;> simp_all

def searchDirections : Array Direction :=
  #[.horizontal, .vertical, .diagonalUp, .diagonalDown]

def fiveBackOffsets : Array Int :=
  #[0, 1, 2, 3, 4]

def fiveWindowAt (b : Board) (p : Player) (m : Coord)
    (d : Direction) (back : Int) : Bool :=
  match step m d (-back) with
  | some start => decide (consecutive (b.place m p) p start d 5)
  | none => false

/- Only a five-cell window containing the newly placed stone can be newly
   created.  This executable predicate checks the four directions and five
   possible positions of `m` inside such a window, for at most 20 windows. -/
def createsFiveFast (b : Board) (p : Player) (m : Coord) : Bool :=
  searchDirections.any (fun d =>
    fiveBackOffsets.any (fiveWindowAt b p m d))

theorem createsFiveFast_sound {b : Board} {p : Player} {m : Coord}
    (h : createsFiveFast b p m = true) :
    hasAtLeastFive (b.place m p) p := by
  rw [createsFiveFast, Array.any_eq_true'] at h
  rcases h with ⟨d, _hd, hdir⟩
  rw [Array.any_eq_true'] at hdir
  rcases hdir with ⟨back, _hback, hwindow⟩
  unfold fiveWindowAt at hwindow
  split at hwindow
  · rename_i start hstep
    exact ⟨start, d, of_decide_eq_true hwindow⟩
  · simp at hwindow

theorem createsFiveFast_complete {b : Board} {p : Player} {m : Coord}
    (hold : ¬ hasAtLeastFive b p)
    (hnew : hasAtLeastFive (b.place m p) p) :
    createsFiveFast b p m = true := by
  rcases hnew with ⟨start, d, hcon⟩
  have hcontains : ∃ n : Fin 5, step start d (n.1 : Int) = some m := by
    by_contra hnone
    apply hold
    refine ⟨start, d, ?_⟩
    intro n
    rcases hcon n with ⟨q, hqstep, hqcell⟩
    have hqm : q ≠ m := by
      intro hqm
      subst q
      exact hnone ⟨n, hqstep⟩
    exact ⟨q, hqstep, by simpa [Board.place, hqm] using hqcell⟩
  rcases hcontains with ⟨n, hn⟩
  have hdirection : d ∈ searchDirections := by
    cases d <;> simp [searchDirections]
  have hback : (n.1 : Int) ∈ fiveBackOffsets := by
    fin_cases n <;> simp [fiveBackOffsets]
  have hwindow : fiveWindowAt b p m d (n.1 : Int) = true := by
    have hreverse : step m d (-(n.1 : Int)) = some start := step_reverse hn
    simp [fiveWindowAt, hreverse, hcon]
  rw [createsFiveFast, Array.any_eq_true']
  exact ⟨d, hdirection, (Array.any_eq_true').2
    ⟨(n.1 : Int), hback, hwindow⟩⟩

theorem createsFiveFast_iff {b : Board} {p : Player} {m : Coord}
    (hold : ¬ hasAtLeastFive b p) :
    createsFiveFast b p m = true ↔ hasAtLeastFive (b.place m p) p := by
  exact ⟨createsFiveFast_sound, createsFiveFast_complete hold⟩

theorem createsFiveFast_terminal
    {s : Position} {p : Player} {m : Coord}
    (hturn : s.turn = p) (hlegal : legalMove s m)
    (hfast : createsFiveFast s.board p m = true) :
    terminal (play s m) = some (winner p) := by
  have hfive : hasAtLeastFive (play s m).board p := by
    change hasAtLeastFive (s.board.place m s.turn) p
    rw [hturn]
    exact createsFiveFast_sound hfast
  cases p with
  | black =>
      simp [terminal, Position.terminal, winner, hfive]
  | white =>
      have hblack : ¬ hasAtLeastFive (play s m).board .black := by
        intro hchild
        have hparent : hasAtLeastFive s.board .black := by
          apply hasAtLeastFive_of_place_other (p := .black) (q := .white)
            (r := m) (by simp)
          change hasAtLeastFive (s.board.place m s.turn) .black at hchild
          simpa [hturn] using hchild
        exact hlegal.1 (Or.inl hparent)
      simp [terminal, Position.terminal, winner, hfive, hblack]

theorem createsFiveFast_terminal_iff
    {s : Position} {p : Player} {m : Coord}
    (hturn : s.turn = p) (hlegal : legalMove s m) :
    createsFiveFast s.board p m = true ↔
      terminal (play s m) = some (winner p) := by
  constructor
  · exact createsFiveFast_terminal hturn hlegal
  · intro hterminal
    apply createsFiveFast_complete
    · intro hold
      exact hlegal.1 (by
        cases p with
        | black => exact Or.inl hold
        | white => exact Or.inr (Or.inl hold))
    · have hfive := Position.terminal_winner_hasAtLeastFive hterminal
      change hasAtLeastFive (s.board.place m s.turn) p at hfive
      simpa [hturn] using hfive

def immediateWinningMovesFirst (s : Position) (p : Player) : Array Coord :=
  let moves := orderedCandidateMoves s p
  let winning := moves.filter (createsFiveFast s.board p)
  let other := moves.filter (fun m => !(createsFiveFast s.board p m))
  winning ++ other

theorem mem_immediateWinningMovesFirst_iff (s : Position) (p : Player) (c : Coord) :
    c ∈ immediateWinningMovesFirst s p ↔ c ∈ orderedCandidateMoves s p := by
  simp only [immediateWinningMovesFirst, Array.mem_append, Array.mem_filter]
  cases h : createsFiveFast s.board p c <;> simp [h]

/- Compute the opponent's winning cells once per position.  The original
   `WinningCells` is a Finset predicate and is convenient for proofs, but
   recomputing it inside a candidate filter repeats the full board scan. -/
def winningCellsArray (s : Position) (p : Player) : Array Coord :=
  allCoords.filter (fun c =>
    decide (s.board.cell c = .empty ∧
      hasAtLeastFive (s.board.place c p) p))

theorem mem_winningCellsArray_iff (s : Position) (p : Player) (c : Coord) :
    c ∈ winningCellsArray s p ↔
      c ∈ allCoords ∧ c ∈ WinningCells s p := by
  simp [winningCellsArray, mem_winningCells_iff]

/- A fixed-size threat mask keeps the one full-board scan of
   `winningCellsArray`, but replaces later linear membership searches with a
   direct row-major lookup. -/
def winningCellsMask (s : Position) (p : Player) : Vector Bool 225 :=
  Vector.ofFn (fun i =>
    decide (coordAtIndex i ∈ WinningCells s p))

theorem winningCellsMask_get_iff (s : Position) (p : Player) (c : Coord) :
    (winningCellsMask s p).get (coordIndex c) = true ↔
      c ∈ WinningCells s p := by
  simp [winningCellsMask, coordAtIndex_coordIndex]

def tacticalCandidateMovesFast (s : Position) (p : Player) : Array Coord :=
  let moves := orderedCandidateMoves s p
  let opponentWins := winningCellsMask s (Player.other p)
  let winning := moves.filter (createsFiveFast s.board p)
  let defense := moves.filter (fun m =>
    !(createsFiveFast s.board p m) &&
      opponentWins.get (coordIndex m))
  let quiet := moves.filter (fun m =>
    !(createsFiveFast s.board p m) &&
      !(opponentWins.get (coordIndex m)))
  winning ++ defense ++ quiet

theorem mem_tacticalCandidateMovesFast_iff (s : Position) (p : Player) (c : Coord) :
    c ∈ tacticalCandidateMovesFast s p ↔ c ∈ orderedCandidateMoves s p := by
  simp only [tacticalCandidateMovesFast, Array.mem_append, Array.mem_filter]
  cases hwin : createsFiveFast s.board p c with
  | true => simp [hwin]
  | false =>
    constructor
    · intro h
      rcases h with (h | h) | h
      · exact h.1
      · exact h.1
      · exact h.1
    · intro hmove
      by_cases hdef : c ∈ WinningCells s (Player.other p)
      · have hdefM :
            (winningCellsMask s (Player.other p)).get (coordIndex c) = true :=
          (winningCellsMask_get_iff s (Player.other p) c).mpr hdef
        simp [hwin, hdefM, hmove]
      · have hdefM :
            (winningCellsMask s (Player.other p)).get (coordIndex c) = false := by
          cases hmask :
              (winningCellsMask s (Player.other p)).get (coordIndex c) with
          | false => rfl
          | true =>
              exact (hdef
                ((winningCellsMask_get_iff s (Player.other p) c).mp hmask)).elim
        simp [hwin, hdefM, hmove]

def tacticalCandidateMoves (s : Position) (p : Player) : Array Coord :=
  tacticalCandidateMovesFast s p

theorem mem_tacticalCandidateMoves_iff (s : Position) (p : Player) (c : Coord) :
    c ∈ tacticalCandidateMoves s p ↔ c ∈ orderedCandidateMoves s p := by
  simpa [tacticalCandidateMoves] using mem_tacticalCandidateMovesFast_iff s p c

/- Reference implementation for regression comparisons.  It deliberately uses
   the full terminal predicate at each candidate. -/
def firstWinningMoveReference (s : Position) (p : Player) : Option Coord :=
  (immediateWinningMovesFirst s p).foldl
    (fun found m =>
      match found with
      | some _ => found
      | none =>
          if terminal (play s m) = some (winner p) then some m else none)
    none

/- The production scan uses the local five-window predicate.  Its accepted
   candidates are still checked by the certificate layer before any theorem
   consumes the generated certificate. -/
def firstWinningMove (s : Position) (p : Player) : Option Coord :=
  (immediateWinningMovesFirst s p).foldl
    (fun found m =>
      match found with
      | some _ => found
      | none =>
          if createsFiveFast s.board p m then some m else none)
    none

theorem immediateWinningMovesFirst_mem_legal
    {s : Position} {p : Player} {m : Coord}
    (hmem : m ∈ immediateWinningMovesFirst s p) :
    s.turn = p ∧ legalMove s m := by
  have hordered := (mem_immediateWinningMovesFirst_iff s p m).mp hmem
  have hcandidate := (mem_orderedCandidateMoves_iff s p m).mp hordered
  have hlegal := (mem_candidateMovesFast_iff s p m).mp hcandidate
  exact ⟨hlegal.1, hlegal.2.2⟩

theorem createsFiveFast_terminal_of_immediateCandidate
    {s : Position} {p : Player} {m : Coord}
    (hmem : m ∈ immediateWinningMovesFirst s p)
    (hfast : createsFiveFast s.board p m = true) :
    terminal (play s m) = some (winner p) := by
  have hlegal := immediateWinningMovesFirst_mem_legal hmem
  exact createsFiveFast_terminal hlegal.1 hlegal.2 hfast

def SearchResult (cfg : SearchConfig) (search : Searcher) : Prop :=
  ∃ c, search cfg = some c ∧ c.target = cfg.target

def CheckedSearchResult (cfg : SearchConfig) (search : Searcher) : Prop :=
  ∃ c, search cfg = some c ∧ checkCertificate c = true

/- A small executable certificate constructor for the easiest local case.
   It is intentionally not a global searcher: callers still have to supply a
   position, target, and candidate move, and the trusted checker must validate
   the resulting nodes. -/
def immediateWinCertificate (s : Position) (p : Player) (m : Coord) : CompactCertificate :=
  { target := p
    root := 0
    nodes := #[
      .proverMove s m 1,
      .terminal (play s m) (winner p)
    ] }

def immediateCertificateFor (s : Position) (p : Player) :
    Option CompactCertificate :=
  match firstWinningMove s p with
  | some m => some (immediateWinCertificate s p m)
  | none => none

/- A two-ply constructor for a finite response table.  The root is an
   opponent-to-move position; each pair `(r, w)` records an opponent reply
   `r` and the target player's immediate winning reply `w`.  The constructor
   is intentionally agnostic about whether the table is complete or whether
   the listed moves are legal: those obligations are checked by
   `checkLocalCertificate`.  Thus this is a certificate generator, not an
   untrusted shortcut around the checker. -/
def responseNodes (s : Position) (p : Player) : Nat → List (Coord × Coord) →
    List CertificateNode
  | _, [] => []
  | base, (reply, win) :: rest =>
      .proverMove (play s reply) win (base + 2) ::
        .terminal (play (play s reply) win) (winner p) ::
        responseNodes s p (base + 2) rest

def twoPlyImmediateCertificate (s : Position) (p : Player)
    (responses : Array (Coord × Coord)) : CompactCertificate :=
  { target := p
    root := 0
    nodes :=
      (.opponentMoves s
          (responses.mapIdx (fun i x => (x.1, 2 * i + 1))) ::
        responseNodes s p 0 responses.toList).toArray }

theorem twoPlyImmediateCertificate_root_valid (s : Position) (p : Player)
    (responses : Array (Coord × Coord)) :
    (twoPlyImmediateCertificate s p responses).root <
      (twoPlyImmediateCertificate s p responses).nodes.size := by
  simp [twoPlyImmediateCertificate]

theorem twoPlyImmediateCertificate_sound
    {s : Position} {p : Player} {responses : Array (Coord × Coord)}
    (h : checkLocalCertificate (twoPlyImmediateCertificate s p responses) = true) :
    CanForceWin s p := by
  have hroot := twoPlyImmediateCertificate_root_valid s p responses
  have hlocal := local_certificate_sound
    (twoPlyImmediateCertificate s p responses) hroot h
  change CanForceWin s p at hlocal
  exact hlocal

def collectImmediateResponses (s : Position) (p : Player) :
    List Coord → Option (List (Coord × Coord))
  | [] => some []
  | reply :: rest =>
      match firstWinningMove (play s reply) p,
          collectImmediateResponses s p rest with
      | some win, some responses => some ((reply, win) :: responses)
      | _, _ => none

/- Enumerate every legal opponent reply and keep the result only when the
   target player has an immediate win after every one of them. -/
def immediateResponseTable (s : Position) (p : Player) :
    Option (Array (Coord × Coord)) :=
  match collectImmediateResponses s p
      (candidateMovesFast s (Player.other p)).toList with
  | some responses => some responses.toArray
  | none => none

def twoPlyCertificateFor (s : Position) (p : Player) :
    Option CompactCertificate :=
  match immediateResponseTable s p with
  | some responses => some (twoPlyImmediateCertificate s p responses)
  | none => none

def checkedTwoPlyCertificateFor (s : Position) (p : Player) :
    Option CompactCertificate :=
  match twoPlyCertificateFor s p with
  | some c => if checkLocalCertificate c then some c else none
  | none => none

theorem checkedTwoPlyCertificateFor_sound
    {s : Position} {p : Player} {c : CompactCertificate}
    (h : checkedTwoPlyCertificateFor s p = some c) :
    CanForceWin s p := by
  unfold checkedTwoPlyCertificateFor at h
  split at h
  · rename_i generated hgenerated
    split at h
    · rename_i hchecked
      have hc : c = generated := by simpa using h.symm
      subst c
      unfold twoPlyCertificateFor at hgenerated
      split at hgenerated
      · rename_i responses hresponses
        have hcert : generated = twoPlyImmediateCertificate s p responses := by
          simpa using hgenerated.symm
        subst generated
        exact twoPlyImmediateCertificate_sound (by simpa using hchecked)
      · simp at hgenerated
    · simp at h
  · simp at h

inductive CandidateTree where
  | terminal (position : Position)
  | proverMove (position : Position) (move : Coord) (child : CandidateTree)
  | opponentMoves (position : Position) (children : List (Coord × CandidateTree))

/- Search results depend on both the position and the remaining depth.  The
   target player is included as well, so a table entry can never be reused for
   a different game-theoretic query. -/
structure SearchKey where
  fuel : Nat
  target : Player
  position : PositionKey
  deriving DecidableEq, Repr

structure SearchMemoEntry where
  key : SearchKey
  result : Option CandidateTree

abbrev SearchMemo := Array SearchMemoEntry

def searchKey (fuel : Nat) (s : Position) (target : Player) : SearchKey :=
  { fuel := fuel, target := target, position := positionKey s }

def memoLookup (memo : SearchMemo) (key : SearchKey) : Option (Option CandidateTree) :=
  (memo.toList.find? (fun entry => decide (entry.key = key))).map SearchMemoEntry.result

def memoInsert (entry : SearchMemoEntry) (memo : SearchMemo) : SearchMemo :=
  #[entry] ++ memo

theorem memoLookup_insert_same (entry : SearchMemoEntry) (memo : SearchMemo) :
    memoLookup (memoInsert entry memo) entry.key = some entry.result := by
  simp [memoLookup, memoInsert]

theorem memoLookup_insert_other_of_ne (entry : SearchMemoEntry) (memo : SearchMemo)
    {key : SearchKey} (hkey : entry.key ≠ key) :
    memoLookup (memoInsert entry memo) key = memoLookup memo key := by
  simp [memoLookup, memoInsert, hkey]

partial def CandidateTree.nodeCount : CandidateTree → Nat
  | .terminal _ => 1
  | .proverMove _ _ child => 1 + child.nodeCount
  | .opponentMoves _ children =>
      1 + children.foldl (fun total x => total + x.2.nodeCount) 0

mutual
  partial def candidateNodeListAt (target : Player) (base : Nat) :
      CandidateTree → List CertificateNode
    | .terminal s => [.terminal s (winner target)]
    | .proverMove s m child =>
        .proverMove s m (base + 1) ::
          candidateNodeListAt target (base + 1) child
    | .opponentMoves s children =>
        .opponentMoves s (candidateForestRefs (base + 1) children).toArray ::
          candidateForestNodes target (base + 1) children

  partial def candidateForestRefs (base : Nat) :
      List (Coord × CandidateTree) → List (Coord × Nat)
    | [] => []
    | (m, child) :: rest =>
        (m, base) :: candidateForestRefs (base + child.nodeCount) rest

  partial def candidateForestNodes (target : Player) (base : Nat) :
      List (Coord × CandidateTree) → List CertificateNode
    | [] => []
    | (_, child) :: rest =>
        candidateNodeListAt target base child ++
          candidateForestNodes target (base + child.nodeCount) rest
end

def candidateTreeCertificate (target : Player) (tree : CandidateTree) :
    CompactCertificate :=
  { target := target
    root := 0
    nodes := (candidateNodeListAt target 0 tree).toArray }

/- A stateful search result.  The recursive search returns the candidate tree
   together with every memo entry learned while exploring that tree.  The
   tree is still only a candidate: callers must pass it through the
   certificate checker before using it as a theorem. -/
structure MemoSearchResult where
  tree : Option CandidateTree
  memo : SearchMemo

instance : Nonempty MemoSearchResult :=
  ⟨{ tree := none, memo := #[] }⟩

mutual
  partial def searchCandidateTreeMemoized (memo : SearchMemo) (fuel : Nat)
      (s : Position) (target : Player) : MemoSearchResult :=
    let key := searchKey fuel s target
    match memoLookup memo key with
    | some result =>
        { tree := result
          memo := memo }
    | none =>
        let computed := searchCandidateTreeMemoMiss memo fuel s target
        { tree := computed.tree
          memo := memoInsert
            { key := key, result := computed.tree } computed.memo }

  partial def searchCandidateTreeMemoMiss (memo : SearchMemo) (fuel : Nat)
      (s : Position) (target : Player) : MemoSearchResult :=
    match terminal s with
    | some out =>
        if out = winner target then
          { tree := some (.terminal s), memo := memo }
        else
          { tree := none, memo := memo }
    | none =>
        match fuel with
        | 0 =>
            { tree := none, memo := memo }
        | depth + 1 =>
            if s.turn = target then
              searchProverChildrenMemoized memo depth s target
                (immediateWinningMovesFirst s target).toList
            else
              let forest := searchOpponentChildrenMemoized memo depth s target
                (candidateMovesFast s (Player.other target)).toList
              match forest.1 with
              | some children =>
                  { tree := some (.opponentMoves s children)
                    memo := forest.2 }
              | none =>
                  { tree := none, memo := forest.2 }

  partial def searchProverChildrenMemoized (memo : SearchMemo) (depth : Nat)
      (s : Position) (target : Player) : List Coord → MemoSearchResult
    | [] =>
        { tree := none, memo := memo }
    | m :: rest =>
        let child := searchCandidateTreeMemoized memo depth (play s m) target
        match child.tree with
        | some subtree =>
            { tree := some (.proverMove s m subtree)
              memo := child.memo }
        | none =>
            searchProverChildrenMemoized child.memo depth s target rest

  partial def searchOpponentChildrenMemoized (memo : SearchMemo) (depth : Nat)
      (s : Position) (target : Player) : List Coord →
        Option (List (Coord × CandidateTree)) × SearchMemo
    | [] => (some [], memo)
    | m :: rest =>
        let child := searchCandidateTreeMemoized memo depth (play s m) target
        match child.tree with
        | none => (none, child.memo)
        | some subtree =>
            let remaining := searchOpponentChildrenMemoized child.memo depth s target rest
            match remaining.1 with
            | some children => ((some ((m, subtree) :: children)), remaining.2)
            | none => (none, remaining.2)
end

/- The historical entry point starts with an empty memo.  Keeping this
   wrapper means existing callers and tests continue to describe the
   non-cached search while the stateful entry point is available to larger
   search drivers. -/
def searchCandidateTree (fuel : Nat) (s : Position)
    (target : Player) : Option CandidateTree :=
  (searchCandidateTreeMemoized #[] fuel s target).tree

/- Cache adapter for the finite-depth search.  A hit reuses the stored tree;
   a miss now runs the stateful recursive search, so entries discovered below
   the root are carried back to the caller.  The result is still passed to the
   certificate checker by `checkedDepthCertificateForCached`, so cached data
   is never trusted merely because it was found in the table. -/
def searchCandidateTreeCached (memo : SearchMemo) (fuel : Nat)
    (s : Position) (target : Player) : Option CandidateTree :=
  match memoLookup memo (searchKey fuel s target) with
  | some result => result
  | none => (searchCandidateTreeMemoized memo fuel s target).tree

theorem searchCandidateTreeCached_hit
    {memo : SearchMemo} {fuel : Nat} {s : Position} {target : Player}
    {result : Option CandidateTree}
    (h : memoLookup memo (searchKey fuel s target) = some result) :
    searchCandidateTreeCached memo fuel s target = result := by
  simp [searchCandidateTreeCached, h]

theorem searchCandidateTreeCached_miss
    {memo : SearchMemo} {fuel : Nat} {s : Position} {target : Player}
    (h : memoLookup memo (searchKey fuel s target) = none) :
    searchCandidateTreeCached memo fuel s target =
      (searchCandidateTreeMemoized memo fuel s target).tree := by
  simp [searchCandidateTreeCached, h]

def depthCertificateFor (fuel : Nat) (s : Position) (target : Player) :
    Option CompactCertificate :=
  (searchCandidateTree fuel s target).map (candidateTreeCertificate target)

def checkedDepthCertificateForCached (memo : SearchMemo) (fuel : Nat)
    (s : Position) (target : Player) : Option CompactCertificate :=
  match searchCandidateTreeCached memo fuel s target with
  | some tree =>
      let c := candidateTreeCertificate target tree
      if checkLocalCertificateAt s c then some c else none
  | none => none

theorem checkedDepthCertificateForCached_sound
    {memo : SearchMemo} {fuel : Nat} {s : Position} {p : Player}
    {c : CompactCertificate}
    (h : checkedDepthCertificateForCached memo fuel s p = some c) :
    CanForceWin s p := by
  unfold checkedDepthCertificateForCached at h
  split at h
  · rename_i tree htree
    change (if checkLocalCertificateAt s (candidateTreeCertificate p tree) then
      some (candidateTreeCertificate p tree) else none) = some c at h
    split at h
    · rename_i hchecked
      have hc : c = candidateTreeCertificate p tree := by
        simpa using h.symm
      subst c
      exact local_certificate_at_sound s
        (candidateTreeCertificate p tree) hchecked
    · simp at h
  · simp at h

def checkedDepthCertificateFor (fuel : Nat) (s : Position) (target : Player) :
    Option CompactCertificate :=
  match searchCandidateTree fuel s target with
  | some tree =>
      let c := candidateTreeCertificate target tree
      if checkLocalCertificateAt s c then some c else none
  | none => none

theorem checkedDepthCertificateFor_sound
    {fuel : Nat} {s : Position} {p : Player} {c : CompactCertificate}
    (h : checkedDepthCertificateFor fuel s p = some c) :
    CanForceWin s p := by
  unfold checkedDepthCertificateFor at h
  split at h
  · rename_i tree htree
    change (if checkLocalCertificateAt s (candidateTreeCertificate p tree) then
      some (candidateTreeCertificate p tree) else none) = some c at h
    split at h
    · rename_i hchecked
      have hc : c = candidateTreeCertificate p tree := by
        simpa using h.symm
      subst c
      have hsound := local_certificate_at_sound s
        (candidateTreeCertificate p tree) hchecked
      simpa [candidateTreeCertificate] using hsound
    · simp at h
  · simp at h

def immediateCertificateNodesChecked (s : Position) (p : Player) : Bool :=
  match firstWinningMove s p with
  | some m =>
      let c := immediateWinCertificate s p m
      checkNodeAt p c.nodes 0 (.proverMove s m 1) &&
        checkNodeAt p c.nodes 1
          (.terminal (play s m) (winner p))
  | none => false

/- This is the trusted local bridge for the executable primitive above.  It
   extracts the turn, legality, and terminal-win facts from the two checked
   nodes, then invokes the ordinary game theorem.  It does not use the global
   certificate checker, whose root is intentionally fixed to the initial
   position. -/
theorem immediateCertificateNodesChecked_sound
    {s : Position} {p : Player}
    (h : immediateCertificateNodesChecked s p = true) :
    CanForceWin s p := by
  unfold immediateCertificateNodesChecked at h
  split at h
  · rename_i m hfirst
    simp only [Bool.and_eq_true] at h
    have hprover :=
      (checkNodeAt_proverMove_iff p
        (immediateWinCertificate s p m).nodes 0 s m 1).mp h.1
    have hterminal :=
      (checkNodeAt_terminal_iff p
        (immediateWinCertificate s p m).nodes 1
        (play s m) (winner p)).mp h.2
    exact canForceWin_immediate hprover.2.2.1 hterminal.1 hprover.2.1
  · simp at h

theorem immediateWinCertificate_prover_checked
    {s : Position} {p : Player} {m : Coord}
    (hturn : s.turn = p) (hlegal : legalMove s m) :
    checkNodeAt p (immediateWinCertificate s p m).nodes 0
      (.proverMove s m 1) = true := by
  have hterm : terminal s = none :=
    Position.terminal_none_of_not_isTerminal hlegal.1
  simp [immediateWinCertificate, checkNodeAt, checkNode, checkEdgesAt,
    refAfter, refValid, hterm, hturn, hlegal, childPositionMatches,
    nodePosition, samePosition_self]

theorem immediateWinCertificate_terminal_checked
    {s : Position} {p : Player} {m : Coord}
    (hwin : terminal (play s m) = some (winner p)) :
    checkNodeAt p (immediateWinCertificate s p m).nodes 1
      (.terminal (play s m) (winner p)) = true := by
  simp [immediateWinCertificate, checkNodeAt, checkNode, checkEdgesAt, hwin]

theorem immediateWinCertificate_reifies
    {s : Position} {p : Player} {m : Coord}
    (hturn : s.turn = p) (hlegal : legalMove s m)
    (hwin : terminal (play s m) = some (winner p)) :
    Nonempty (CertificateTree p s) := by
  apply compact_reify_at (immediateWinCertificate s p m) p 0
  · simp [immediateWinCertificate]
  · intro i hi
    have hi' : i = 0 ∨ i = 1 := by
      simp [immediateWinCertificate] at hi ⊢
      omega
    rcases hi' with h0 | h1
    · subst i
      simpa [immediateWinCertificate] using
        immediateWinCertificate_prover_checked hturn hlegal
    · subst i
      simpa [immediateWinCertificate] using
        immediateWinCertificate_terminal_checked hwin

theorem immediateWinCertificate_sound
    {s : Position} {p : Player} {m : Coord}
    (hturn : s.turn = p) (hlegal : legalMove s m)
    (hwin : terminal (play s m) = some (winner p)) :
    CanForceWin s p :=
  CertificateTree.sound
    (Classical.choice (immediateWinCertificate_reifies hturn hlegal hwin))

theorem checkedSearchResult_sound {cfg : SearchConfig} {search : Searcher}
    (h : CheckedSearchResult cfg search) :
    CanForceWin initialPosition .black := by
  rcases h with ⟨c, _hresult, hcheck⟩
  exact compact_certificate_sound c hcheck

def acceptCertificate (c : CompactCertificate) : Option CompactCertificate :=
  if checkCertificate c then some c else none

theorem acceptCertificate_some_iff (c : CompactCertificate) :
    acceptCertificate c = some c ↔ checkCertificate c = true := by
  simp [acceptCertificate]

theorem acceptCertificate_sound {c : CompactCertificate}
    (h : acceptCertificate c = some c) :
    CanForceWin initialPosition .black := by
  exact compact_certificate_sound c ((acceptCertificate_some_iff c).mp h)

/- Executable regression checks for the untrusted candidate generator.  These
   examples check coverage and filtering only; they do not contribute to the
   certificate soundness theorem. -/
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

def searchTerminalBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place
          (Board.place Board.empty (5, 7) .black) (6, 7) .black)
        (7, 7) .black)
      (8, 7) .black)
    (9, 7) .black

def searchTerminalPosition : Position :=
  ⟨searchTerminalBoard, .white⟩

example : (candidateMoves searchTerminalPosition .white).size = 0 := by
  native_decide

def searchImmediateBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (5, 7) .black) (6, 7) .black)
      (7, 7) .black)
    (8, 7) .black

def searchImmediatePosition : Position :=
  ⟨searchImmediateBoard, .black⟩

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

/- Fast five detection regression suite.  Each board has four stones and the
   tested move fills the fifth point; the boundary case exercises a window
   whose first cell is on the edge of the board. -/
def fastVerticalBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (7, 3) .black) (7, 4) .black)
      (7, 5) .black)
    (7, 6) .black

def fastDiagonalUpBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (3, 3) .black) (4, 4) .black)
      (5, 5) .black)
    (6, 6) .black

def fastDiagonalDownBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (3, 6) .black) (4, 5) .black)
      (5, 4) .black)
    (6, 3) .black

def fastBoundaryBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (0, 0) .black) (1, 0) .black)
      (2, 0) .black)
    (3, 0) .black

def fastInsufficientBoard : Board :=
  Board.place
    (Board.place
      (Board.place Board.empty (5, 7) .black) (6, 7) .black)
    (7, 7) .black

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
