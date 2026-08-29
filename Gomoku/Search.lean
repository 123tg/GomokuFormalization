import Gomoku.Certificate

/-!
搜索层：枚举并排序候选落子，进行快速五连检测、两层与有限深度 AND/OR 搜索，
再把未受信候选树编译为 `CompactCertificate`。任何搜索结果都必须通过 Lean 检查器后才能成为定理。
-/

namespace Gomoku

structure SearchConfig where
  target : Player := .black
  maxNodes : Nat := 0
  deriving Repr
-- 配置搜索目标玩家与节点预算；`maxNodes = 0` 约定为由具体搜索器自行解释的默认预算。

abbrev Searcher := SearchConfig → Option CompactCertificate
-- 把搜索器抽象为从配置到可选紧凑证书的函数，失败时返回 `none`。

/- The searcher may need a complete executable move list, but this helper is
   deliberately outside the trusted certificate checker.  `Fin 49` indexes
   the 7 by 7 board in row-major order and keeps the generated coordinates
   inside the board by construction. -/
def coordAtIndex (i : Fin 49) : Coord :=
  (⟨i.1 % 7, by omega⟩, ⟨i.1 / 7, by omega⟩)
-- 按行优先顺序把 `0 ≤ i < 49` 的索引还原为合法的 7×7 棋盘坐标。

def allCoords : Array Coord :=
  Array.ofFn coordAtIndex
-- 依次枚举棋盘上的全部 49 个坐标。

/- A stable row-major index for a coordinate.  Keeping this inverse to
   `coordAtIndex` lets later search code use O(1) array lookup for masks and
   cached threat information instead of linear `Array.mem` scans. -/
def coordIndex (c : Coord) : Fin 49 :=
  ⟨c.2.1 * 7 + c.1.1, by omega⟩
-- 按 `index = y * 7 + x` 把棋盘坐标编码为 `Fin 49` 索引。

theorem coordAtIndex_coordIndex (c : Coord) :
    coordAtIndex (coordIndex c) = c := by
  apply Prod.ext
  · apply Fin.ext
    simp [coordAtIndex, coordIndex]
  · apply Fin.ext
    simp [coordAtIndex, coordIndex]
    omega
-- 证明坐标先编码再解码仍得到原坐标，即 `coordAtIndex` 是 `coordIndex` 的左逆。

theorem coordIndex_coordAtIndex (i : Fin 49) :
    coordIndex (coordAtIndex i) = i := by
  apply Fin.ext
  simp [coordAtIndex, coordIndex]
  omega
-- 证明索引先解码再编码仍得到原索引，即两个行优先转换互为逆映射。

theorem mem_allCoords (c : Coord) : c ∈ allCoords := by
  change c ∈ Array.ofFn coordAtIndex
  rw [Array.mem_ofFn]
  exact ⟨coordIndex c, coordAtIndex_coordIndex c⟩

/- An exact, executable row-major key for transposition tables.  The key is
   intentionally a lossless `Array Cell`, so a later cache cannot merge two
   different board positions by hash collision. -/
abbrev PositionKey := Player × Vector Cell 49
-- 用当前行棋方和无损的 49 格棋盘向量共同表示局面键，避免哈希碰撞影响正确性。

def boardKey (b : Board) : Vector Cell 49 :=
  Vector.ofFn (fun i => b.cell (coordAtIndex i))
-- 把函数式棋盘按行优先顺序展开为固定长度向量。

def positionKey (s : Position) : PositionKey :=
  (s.turn, boardKey s.board)
-- 提取局面的完整缓存键，同时保留棋盘与轮到哪一方的信息。

theorem boardKey_get (b : Board) (c : Coord) :
    (boardKey b).get (coordIndex c) = b.cell c := by
  simp [boardKey, coordAtIndex_coordIndex]
-- 说明通过坐标对应索引读取棋盘键，得到的格子与原棋盘在该坐标的内容一致。

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
-- 证明两个棋盘键相等当且仅当两个函数式棋盘相等，因此 `boardKey` 不丢失信息。

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
-- 证明两个局面键相等当且仅当两个局面相等，为换位表的精确复用提供依据。

abbrev TranspositionTable := Array PositionKey
-- 用局面键数组表示最简单的换位表。

def containsPositionKey (table : TranspositionTable) (s : Position) : Bool :=
  table.any (fun k => k = positionKey s)
-- 可执行地判断换位表中是否已经记录给定局面。

theorem containsPositionKey_true_iff (table : TranspositionTable) (s : Position) :
    containsPositionKey table s = true ↔
      ∃ i, ∃ (h : i < table.size), table[i] = positionKey s := by
  simp [containsPositionKey]
-- 把布尔查表成功刻画为：数组中存在一个合法下标，其元素等于该局面键。

def candidateMoves (s : Position) (p : Player) : Array Coord :=
  if s.turn = p then
    allCoords.filter (fun c => decide (legalMove s c))
  else
    #[]
-- 参考版候选生成器：仅当轮到 `p` 时枚举全部合法落子。

/- `candidateMoves` is the simple reference implementation.  The fast
   variant factors the position-level terminal test out of the per-cell
   filter; this matters because a search node may inspect all 49 cells. -/
def candidateMovesFast (s : Position) (p : Player) : Array Coord :=
  if s.turn = p then
    if terminal s = none then
      allCoords.filter (fun c => s.board.cell c = .empty)
    else
      #[]
  else
    #[]
-- 优化版候选生成器：先统一排除终局，再只按空格过滤，从而避免对每个坐标重复检查终局。

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
-- 精确刻画快速候选数组的成员条件：轮到 `p`、坐标在全盘枚举中且该步合法。

theorem mem_candidateMoves_iff (s : Position) (p : Player) (c : Coord) :
    c ∈ candidateMoves s p ↔
      s.turn = p ∧ c ∈ allCoords ∧ legalMove s c := by
  by_cases hturn : s.turn = p
  · simp [candidateMoves, hturn]
  · simp [candidateMoves, hturn]
-- 精确刻画参考候选数组的成员条件。

theorem mem_candidateMovesFast_iff_mem_candidateMoves (s : Position) (p : Player)
    (c : Coord) :
    c ∈ candidateMovesFast s p ↔ c ∈ candidateMoves s p := by
  rw [mem_candidateMovesFast_iff, mem_candidateMoves_iff]
-- 证明快速实现与参考实现生成完全相同的候选集合，优化只改变计算方式。

def neighborSteps : Array (Direction × Int) :=
  #[(.horizontal, -1), (.horizontal, 1),
    (.vertical, -1), (.vertical, 1),
    (.diagonalUp, -1), (.diagonalUp, 1),
    (.diagonalDown, -1), (.diagonalDown, 1)]
-- 列出某坐标沿四条棋线向正反两侧移动一步的八种邻接方式。

def hasOccupiedNeighbor (s : Position) (c : Coord) : Bool :=
  neighborSteps.any (fun x =>
    match step c x.1 x.2 with
    | some q => decide (s.board.cell q ≠ .empty)
    | none => false)
-- 判断坐标 `c` 的八邻域内是否至少有一个已落子坐标。

/- Search local moves first, but retain every legal move.  This ordering is
   used only by the untrusted searcher; the theorem below records that it does
   not change the candidate set. -/
def orderedCandidateMoves (s : Position) (p : Player) : Array Coord :=
  let moves := candidateMovesFast s p
  moves.filter (hasOccupiedNeighbor s) ++
    moves.filter (fun c => !(hasOccupiedNeighbor s c))
-- 在不删减合法步的前提下，把邻近已有棋子的候选排在孤立候选之前。

theorem mem_orderedCandidateMoves_iff (s : Position) (p : Player) (c : Coord) :
    c ∈ orderedCandidateMoves s p ↔ c ∈ candidateMovesFast s p := by
  simp only [orderedCandidateMoves, Array.mem_append, Array.mem_filter]
  by_cases h : hasOccupiedNeighbor s c
  · simp [h]
  · cases hvalue : hasOccupiedNeighbor s c <;> simp_all
-- 证明候选排序保持成员集合不变，因此该启发式不影响搜索完备性。

def searchDirections : Array Direction :=
  #[.horizontal, .vertical, .diagonalUp, .diagonalDown]
-- 枚举五子连线可能采用的四个无向方向。

def fiveBackOffsets : Array Int :=
  #[0, 1, 2, 3, 4]
-- 枚举新落子在长度为五的窗口中可能占据的五个位置。

def fiveWindowAt (b : Board) (p : Player) (m : Coord)
    (d : Direction) (back : Int) : Bool :=
  match step m d (-back) with
  | some start => decide (consecutive (b.place m p) p start d 5)
  | none => false
-- 检查以 `m` 向方向 `d` 回退 `back` 格为起点的五格窗口，落子后是否全属于 `p`。

/- Only a five-cell window containing the newly placed stone can be newly
   created.  This executable predicate checks the four directions and five
   possible positions of `m` inside such a window, for at most 20 windows. -/
def createsFiveFast (b : Board) (p : Player) (m : Coord) : Bool :=
  searchDirections.any (fun d =>
    fiveBackOffsets.any (fiveWindowAt b p m d))
-- 至多检查 4×5 个包含新落子 `m` 的窗口，快速判断该步是否新形成五连。

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
-- 证明快速判定为真时，落子后的棋盘确实存在玩家 `p` 的至少五连。

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
-- 在落子前不存在旧五连的前提下，证明落子后出现五连一定会被快速窗口检查发现。

theorem createsFiveFast_iff {b : Board} {p : Player} {m : Coord}
    (hold : ¬ hasAtLeastFive b p) :
    createsFiveFast b p m = true ↔ hasAtLeastFive (b.place m p) p := by
  exact ⟨createsFiveFast_sound, createsFiveFast_complete hold⟩
-- 合并可靠性与完备性：没有旧五连时，快速判定与落子后存在五连等价。

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
-- 证明合法且通过快速五连检查的当前玩家落子，会使子局面终局结果等于该玩家获胜。

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
-- 对合法当前落子证明：快速五连判定为真，当且仅当落子后终局结果是 `p` 获胜。

/- A single executable boundary for the result of a candidate move.  The
   function deliberately returns `none` for an illegal move, because it is
   used by the untrusted search engine as a total computation.  The theorem
   below is the trusted interpretation: on a non-terminal position and a
   legal move, this fast classification is exactly the ordinary game rule. -/
def terminalAfterMoveFast (s : Position) (m : Coord) : Option Outcome :=
  if hlegal : legalMove s m then
    if createsFiveFast s.board s.turn m then
      some (winner s.turn)
    else if Board.full (play s m).board then
      some .draw
    else
      none
  else
    none

theorem terminalAfterMoveFast_eq_terminal
    {s : Position} {m : Coord}
    (hterm : terminal s = none) (hlegal : legalMove s m) :
    terminalAfterMoveFast s m = terminal (play s m) := by
  have hsnoterm : ¬ Position.isTerminal s :=
    Position.not_isTerminal_of_terminal_none hterm
  have hnotold : ¬ hasAtLeastFive s.board s.turn := by
    intro h
    apply hsnoterm
    cases hturn : s.turn with
    | black => exact Or.inl (by simpa [hturn] using h)
    | white => exact Or.inr (Or.inl (by simpa [hturn] using h))
  have hnotother :
      ¬ hasAtLeastFive (play s m).board (Player.other s.turn) := by
    intro hchild
    change hasAtLeastFive (s.board.place m s.turn) (Player.other s.turn) at hchild
    apply hlegal.1
    cases hturn : s.turn with
    | black =>
        have hprev : hasAtLeastFive s.board .white := by
          apply hasAtLeastFive_of_place_other
            (p := .white) (q := .black) (r := m) (by decide)
          simpa [hturn] using hchild
        exact Or.inr (Or.inl hprev)
    | white =>
        have hprev : hasAtLeastFive s.board .black := by
          apply hasAtLeastFive_of_place_other
            (p := .black) (q := .white) (r := m) (by decide)
          simpa [hturn] using hchild
        exact Or.inl hprev
  by_cases hfast : createsFiveFast s.board s.turn m = true
  · have hwin := createsFiveFast_terminal
      (s := s) (p := s.turn) (m := m) rfl hlegal hfast
    simp [terminalAfterMoveFast, hlegal, hfast, hwin]
  · have hnotnew : ¬ hasAtLeastFive (play s m).board s.turn := by
      intro hchild
      change hasAtLeastFive (s.board.place m s.turn) s.turn at hchild
      have hplaced := hchild
      exact hfast ((createsFiveFast_iff hnotold).mpr hplaced)
    cases hturn : s.turn with
    | black =>
        have hnotblack : ¬ hasAtLeastFive (play s m).board .black := by
          simpa [hturn] using hnotnew
        have hnotwhite : ¬ hasAtLeastFive (play s m).board .white := by
          simpa [hturn] using hnotother
        by_cases hfull : Board.full (play s m).board
        · simp [terminalAfterMoveFast, hlegal, hfast, hfull, terminal,
            Position.terminal, hnotblack, hnotwhite]
        · simp [terminalAfterMoveFast, hlegal, hfast, hfull, terminal,
            Position.terminal, hnotblack, hnotwhite]
    | white =>
        have hnotblack : ¬ hasAtLeastFive (play s m).board .black := by
          simpa [hturn] using hnotother
        have hnotwhite : ¬ hasAtLeastFive (play s m).board .white := by
          simpa [hturn] using hnotnew
        by_cases hfull : Board.full (play s m).board
        · simp [terminalAfterMoveFast, hlegal, hfast, hfull, terminal,
            Position.terminal, hnotblack, hnotwhite]
        · simp [terminalAfterMoveFast, hlegal, hfast, hfull, terminal,
            Position.terminal, hnotblack, hnotwhite]

theorem terminalAfterMoveFast_of_not_legal
    {s : Position} {m : Coord} (hlegal : ¬ legalMove s m) :
    terminalAfterMoveFast s m = none := by
  simp [terminalAfterMoveFast, hlegal]

theorem terminalAfterMoveFast_none_iff
    {s : Position} {m : Coord}
    (hterm : terminal s = none) (hlegal : legalMove s m) :
    terminalAfterMoveFast s m = none ↔ terminal (play s m) = none := by
  rw [terminalAfterMoveFast_eq_terminal hterm hlegal]

theorem terminalAfterMoveFast_win_iff
    {s : Position} {m : Coord}
    (hterm : terminal s = none) (hlegal : legalMove s m) :
    terminalAfterMoveFast s m = some (winner s.turn) ↔
      terminal (play s m) = some (winner s.turn) := by
  rw [terminalAfterMoveFast_eq_terminal hterm hlegal]

theorem terminalAfterMoveFast_draw_iff
    {s : Position} {m : Coord}
    (hterm : terminal s = none) (hlegal : legalMove s m) :
    terminalAfterMoveFast s m = some .draw ↔
      terminal (play s m) = some .draw := by
  rw [terminalAfterMoveFast_eq_terminal hterm hlegal]

def immediateWinningMovesFirst (s : Position) (p : Player) : Array Coord :=
  let moves := orderedCandidateMoves s p
  let winning := moves.filter (createsFiveFast s.board p)
  let other := moves.filter (fun m => !(createsFiveFast s.board p m))
  winning ++ other
-- 将立即获胜步移到候选数组前部，同时保留其余候选及各组内部原有顺序。

theorem mem_immediateWinningMovesFirst_iff (s : Position) (p : Player) (c : Coord) :
    c ∈ immediateWinningMovesFirst s p ↔ c ∈ orderedCandidateMoves s p := by
  simp only [immediateWinningMovesFirst, Array.mem_append, Array.mem_filter]
  cases h : createsFiveFast s.board p c <;> simp [h]
-- 证明“立即胜着优先”只重排候选，不增加或删除任何落子。

/- Compute the opponent's winning cells once per position.  The original
   `WinningCells` is a Finset predicate and is convenient for proofs, but
   recomputing it inside a candidate filter repeats the full board scan. -/
def winningCellsArray (s : Position) (p : Player) : Array Coord :=
  allCoords.filter (fun c =>
    decide (s.board.cell c = .empty ∧
      hasAtLeastFive (s.board.place c p) p))
-- 枚举玩家 `p` 落下后能形成至少五连的所有空格。

theorem mem_winningCellsArray_iff (s : Position) (p : Player) (c : Coord) :
    c ∈ winningCellsArray s p ↔
      c ∈ allCoords ∧ c ∈ WinningCells s p := by
  simp [winningCellsArray, mem_winningCells_iff]
-- 证明数组成员关系等价于坐标属于形式化定义 `WinningCells s p`。

/- A fixed-size threat mask keeps the one full-board scan of
   `winningCellsArray`, but replaces later linear membership searches with a
   direct row-major lookup. -/
def winningCellsMask (s : Position) (p : Player) : Vector Bool 49 :=
  Vector.ofFn (fun i =>
    decide (coordAtIndex i ∈ WinningCells s p))
-- 把全部制胜点预计算为 49 位布尔向量，以便按坐标常数时间查询。

theorem winningCellsMask_get_iff (s : Position) (p : Player) (c : Coord) :
    (winningCellsMask s p).get (coordIndex c) = true ↔
      c ∈ WinningCells s p := by
  simp [winningCellsMask, coordAtIndex_coordIndex]
-- 证明在制胜点掩码中读取坐标 `c`，结果为真当且仅当 `c` 属于 `WinningCells s p`。

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
-- 按“己方立即胜着、阻挡对方制胜点、普通步”的优先级排列全部候选。

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
-- 证明战术分组后的快速候选数组与排序前的数组具有相同成员集合。

def tacticalCandidateMoves (s : Position) (p : Player) : Array Coord :=
  tacticalCandidateMovesFast s p
-- 暴露稳定的战术候选接口，当前实现采用预计算制胜点掩码的快速版本。

theorem mem_tacticalCandidateMoves_iff (s : Position) (p : Player) (c : Coord) :
    c ∈ tacticalCandidateMoves s p ↔ c ∈ orderedCandidateMoves s p := by
  simpa [tacticalCandidateMoves] using mem_tacticalCandidateMovesFast_iff s p c
-- 证明公开战术候选接口仍只改变顺序，不改变合法候选集合。

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
-- 参考实现逐个计算完整终局谓词，返回候选顺序中的第一个立即获胜步。

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
-- 生产实现使用局部快速五连检查，返回候选顺序中的第一个立即获胜步。

theorem immediateWinningMovesFirst_mem_legal
    {s : Position} {p : Player} {m : Coord}
    (hmem : m ∈ immediateWinningMovesFirst s p) :
    s.turn = p ∧ legalMove s m := by
  have hordered := (mem_immediateWinningMovesFirst_iff s p m).mp hmem
  have hcandidate := (mem_orderedCandidateMoves_iff s p m).mp hordered
  have hlegal := (mem_candidateMovesFast_iff s p m).mp hcandidate
  exact ⟨hlegal.1, hlegal.2.2⟩
-- 从立即胜着优先数组的成员关系恢复轮次条件与该落子的合法性。

theorem createsFiveFast_terminal_of_immediateCandidate
    {s : Position} {p : Player} {m : Coord}
    (hmem : m ∈ immediateWinningMovesFirst s p)
    (hfast : createsFiveFast s.board p m = true) :
    terminal (play s m) = some (winner p) := by
  have hlegal := immediateWinningMovesFirst_mem_legal hmem
  exact createsFiveFast_terminal hlegal.1 hlegal.2 hfast
-- 证明候选数组中通过快速五连检查的落子，执行后必得到目标玩家获胜的终局。

def SearchResult (cfg : SearchConfig) (search : Searcher) : Prop :=
  ∃ c, search cfg = some c ∧ c.target = cfg.target
-- 描述搜索器返回了一张目标玩家与配置一致的证书，但尚未要求证书通过检查。

def CheckedSearchResult (cfg : SearchConfig) (search : Searcher) : Prop :=
  ∃ c, search cfg = some c ∧ checkCertificate c = true
-- 描述搜索器返回的证书已经通过全局可信检查器。

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
-- 构造只有“证明方落一步”和“该子局面获胜终结”两个节点的最小紧凑证书。

def immediateCertificateFor (s : Position) (p : Player) :
    Option CompactCertificate :=
  match firstWinningMove s p with
  | some m => some (immediateWinCertificate s p m)
  | none => none
-- 若能找到立即获胜步，就为它生成两节点证书；否则报告没有此类证书。

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
-- 把每个“对手应手—我方胜着”对展开为连续的证明方节点与终局节点，并递推计算索引。

def twoPlyImmediateCertificate (s : Position) (p : Player)
    (responses : Array (Coord × Coord)) : CompactCertificate :=
  { target := p
    root := 0
    nodes :=
      (.opponentMoves s
          (responses.mapIdx (fun i x => (x.1, 2 * i + 1))) ::
        responseNodes s p 0 responses.toList).toArray }
-- 将完整应手表编码为两层证书：根列举对方所有合法应手，每条分支以我方立即获胜结束。

theorem twoPlyImmediateCertificate_root_valid (s : Position) (p : Player)
    (responses : Array (Coord × Coord)) :
    (twoPlyImmediateCertificate s p responses).root <
      (twoPlyImmediateCertificate s p responses).nodes.size := by
  simp [twoPlyImmediateCertificate]
-- 证明两层证书的根索引 0 始终落在非空节点数组内。

theorem twoPlyImmediateCertificate_sound
    {s : Position} {p : Player} {responses : Array (Coord × Coord)}
    (h : checkLocalCertificate (twoPlyImmediateCertificate s p responses) = true) :
    CanForceWin s p := by
  have hroot := twoPlyImmediateCertificate_root_valid s p responses
  have hlocal := local_certificate_sound
    (twoPlyImmediateCertificate s p responses) hroot h
  change CanForceWin s p at hlocal
  exact hlocal
-- 证明两层生成证书一旦通过局部检查，就可推出玩家 `p` 从局面 `s` 能强制获胜。

def collectImmediateResponses (s : Position) (p : Player) :
    List Coord → Option (List (Coord × Coord))
  | [] => some []
  | reply :: rest =>
      match firstWinningMove (play s reply) p,
          collectImmediateResponses s p rest with
      | some win, some responses => some ((reply, win) :: responses)
      | _, _ => none
-- 递归检查给定的每个对手应手；只有每个子局面都存在我方立即胜着时才返回完整对应表。

/- Enumerate every legal opponent reply and keep the result only when the
   target player has an immediate win after every one of them. -/
def immediateResponseTable (s : Position) (p : Player) :
    Option (Array (Coord × Coord)) :=
  match collectImmediateResponses s p
      (candidateMovesFast s (Player.other p)).toList with
  | some responses => some responses.toArray
  | none => none
-- 枚举对手的全部合法应手，并尝试为每个应手收集玩家 `p` 的立即获胜回复。

def twoPlyCertificateFor (s : Position) (p : Player) :
    Option CompactCertificate :=
  match immediateResponseTable s p with
  | some responses => some (twoPlyImmediateCertificate s p responses)
  | none => none
-- 若完整两层应手表存在，则将它转换为候选紧凑证书。

def checkedTwoPlyCertificateFor (s : Position) (p : Player) :
    Option CompactCertificate :=
  match twoPlyCertificateFor s p with
  | some c => if checkLocalCertificate c then some c else none
  | none => none
-- 只返回通过局部可信检查器的两层证书，拒绝生成器产生的无效候选。

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
-- 证明成功返回的已检查两层证书蕴含 `CanForceWin s p`。

inductive CandidateTree where
  | terminal (position : Position)
  | proverMove (position : Position) (move : Coord) (child : CandidateTree)
  | opponentMoves (position : Position) (children : List (Coord × CandidateTree))
-- 表示搜索器构造的未受信证明树：胜利叶、我方选一步、以及对方全部应手分支。

/- Search results depend on both the position and the remaining depth.  The
   target player is included as well, so a table entry can never be reused for
   a different game-theoretic query. -/
structure SearchKey where
  fuel : Nat
  target : Player
  position : PositionKey
  deriving DecidableEq, Repr
-- 用剩余深度、目标玩家和完整局面共同标识一次有限深度搜索查询。

structure SearchMemoEntry where
  key : SearchKey
  result : Option CandidateTree
-- 保存某搜索键的成功候选树或已确认的失败结果。

abbrev SearchMemo := Array SearchMemoEntry
-- 用条目数组表示搜索记忆表，后插入的条目置于数组前端。

def searchKey (fuel : Nat) (s : Position) (target : Player) : SearchKey :=
  { fuel := fuel, target := target, position := positionKey s }
-- 从搜索参数构造精确的记忆化查询键。

/- The cache key is exact: two queries have the same key only when their
   remaining depth, target player, and complete position are all equal.  This
   is the small correctness fact that prevents a result proved at one depth
   (or for the other player) from being silently reused for another query. -/
theorem searchKey_eq_iff (fuel₁ fuel₂ : Nat) (s t : Position)
    (p q : Player) :
    searchKey fuel₁ s p = searchKey fuel₂ t q ↔
      fuel₁ = fuel₂ ∧ p = q ∧ s = t := by
  constructor
  · intro h
    have hfuel : fuel₁ = fuel₂ := congrArg SearchKey.fuel h
    have htarget : p = q := congrArg SearchKey.target h
    have hpositionKey : positionKey s = positionKey t :=
      congrArg SearchKey.position h
    have hposition : s = t := (positionKey_eq_iff s t).mp hpositionKey
    exact ⟨hfuel, htarget, hposition⟩
  · rintro ⟨hfuel, htarget, hposition⟩
    cases hfuel
    cases htarget
    cases hposition
    rfl

def memoLookup (memo : SearchMemo) (key : SearchKey) : Option (Option CandidateTree) :=
  (memo.toList.find? (fun entry => decide (entry.key = key))).map SearchMemoEntry.result
-- 在线性记忆表中查找首个匹配键，并区分“未缓存”和“缓存的失败 `none`”。

def memoInsert (entry : SearchMemoEntry) (memo : SearchMemo) : SearchMemo :=
  #[entry] ++ memo
-- 把新搜索结果插入记忆表前端，使最新条目优先命中。

theorem memoLookup_insert_same (entry : SearchMemoEntry) (memo : SearchMemo) :
    memoLookup (memoInsert entry memo) entry.key = some entry.result := by
  simp [memoLookup, memoInsert]
-- 证明刚插入的条目按自身键查询时必然立即命中其结果。

theorem memoLookup_insert_other_of_ne (entry : SearchMemoEntry) (memo : SearchMemo)
    {key : SearchKey} (hkey : entry.key ≠ key) :
    memoLookup (memoInsert entry memo) key = memoLookup memo key := by
  simp [memoLookup, memoInsert, hkey]
-- 证明插入不同键的条目不会改变原键的查询结果。

partial def CandidateTree.nodeCount : CandidateTree → Nat
  | .terminal _ => 1
  | .proverMove _ _ child => 1 + child.nodeCount
  | .opponentMoves _ children =>
      1 + children.foldl (fun total x => total + x.2.nodeCount) 0
-- 递归统计候选树包含的节点总数，用于把树展平时计算后续子树根索引。

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
  -- 从索引 `base` 开始把一棵候选树以前序方式展平为紧凑证书节点列表。

  partial def candidateForestRefs (base : Nat) :
      List (Coord × CandidateTree) → List (Coord × Nat)
    | [] => []
    | (m, child) :: rest =>
        (m, base) :: candidateForestRefs (base + child.nodeCount) rest
  -- 为对手分支森林计算每个落子对应的展平子树根索引。

  partial def candidateForestNodes (target : Player) (base : Nat) :
      List (Coord × CandidateTree) → List CertificateNode
    | [] => []
    | (_, child) :: rest =>
        candidateNodeListAt target base child ++
          candidateForestNodes target (base + child.nodeCount) rest
  -- 按顺序展平分支森林，并利用各子树节点数推进下一棵子树的起始索引。
end

def candidateTreeCertificate (target : Player) (tree : CandidateTree) :
    CompactCertificate :=
  { target := target
    root := 0
    nodes := (candidateNodeListAt target 0 tree).toArray }
-- 把未受信候选树封装成根索引为 0 的紧凑证书，供可信检查器重新验证。

/- A stateful search result.  The recursive search returns the candidate tree
   together with every memo entry learned while exploring that tree.  The
   tree is still only a candidate: callers must pass it through the
   certificate checker before using it as a theorem. -/
structure MemoSearchResult where
  tree : Option CandidateTree
  memo : SearchMemo
-- 同时返回本次搜索得到的可选候选树和递归过程中积累的记忆表。

instance : Nonempty MemoSearchResult :=
  ⟨{ tree := none, memo := #[] }⟩
-- 给记忆化搜索结果提供一个“无候选树、空缓存”的默认非空见证。

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
  -- 记忆化搜索入口：命中时复用结果，未命中时递归计算并把根查询结果写回缓存。

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
  -- 处理缓存未命中的搜索节点：胜利终局生成叶，深度耗尽失败，否则按轮次采用存在或全称分支。

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
  -- 搜索证明方分支；只需找到一个能递归获胜的落子，并保留探索中更新的缓存。

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
  -- 搜索对手分支；必须为每个合法应手找到获胜子树，否则整个全称分支失败。
end

/- The historical entry point starts with an empty memo.  Keeping this
   wrapper means existing callers and tests continue to describe the
   non-cached search while the stateful entry point is available to larger
   search drivers. -/
def searchCandidateTree (fuel : Nat) (s : Position)
    (target : Player) : Option CandidateTree :=
  (searchCandidateTreeMemoized #[] fuel s target).tree
-- 从空记忆表启动有限深度候选树搜索，并仅暴露候选树结果。

/- Cache adapter for the finite-depth search.  A hit reuses the stored tree;
   a miss runs the stateful search and returns its candidate tree.  The result
   is still passed to the certificate checker by
   `checkedDepthCertificateForCached`, so cached data is never trusted merely
   because it was found in the table. -/
def searchCandidateTreeCached (memo : SearchMemo) (fuel : Nat)
    (s : Position) (target : Player) : Option CandidateTree :=
  match memoLookup memo (searchKey fuel s target) with
  | some result => result
  | none => (searchCandidateTreeMemoized memo fuel s target).tree
-- 使用调用者提供的缓存查询搜索结果；根未命中时运行完整记忆化递归。

theorem searchCandidateTreeCached_hit
    {memo : SearchMemo} {fuel : Nat} {s : Position} {target : Player}
    {result : Option CandidateTree}
    (h : memoLookup memo (searchKey fuel s target) = some result) :
    searchCandidateTreeCached memo fuel s target = result := by
  simp [searchCandidateTreeCached, h]
-- 证明根查询命中时，缓存适配器原样返回已存结果。

theorem searchCandidateTreeCached_miss
    {memo : SearchMemo} {fuel : Nat} {s : Position} {target : Player}
    (h : memoLookup memo (searchKey fuel s target) = none) :
    searchCandidateTreeCached memo fuel s target =
      (searchCandidateTreeMemoized memo fuel s target).tree := by
  simp [searchCandidateTreeCached, h]
-- 证明根查询未命中时，缓存适配器等于记忆化递归计算出的树结果。

def depthCertificateFor (fuel : Nat) (s : Position) (target : Player) :
    Option CompactCertificate :=
  (searchCandidateTree fuel s target).map (candidateTreeCertificate target)
-- 把有限深度搜索成功得到的候选树展平为尚未检查的紧凑证书。

def checkedDepthCertificateForCached (memo : SearchMemo) (fuel : Nat)
    (s : Position) (target : Player) : Option CompactCertificate :=
  match searchCandidateTreeCached memo fuel s target with
  | some tree =>
      let c := candidateTreeCertificate target tree
      if checkLocalCertificateAt s c then some c else none
  | none => none
-- 对缓存搜索产生的证书执行以 `s` 为根的局部检查，只返回通过检查的结果。

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
-- 证明缓存版深度搜索成功返回证书时，目标玩家从根局面确实能强制获胜。

theorem checkedDepthCertificateForCached_isSome_sound
    {memo : SearchMemo} {fuel : Nat} {s : Position} {p : Player}
    (h : (checkedDepthCertificateForCached memo fuel s p).isSome) :
    CanForceWin s p := by
  cases hresult : checkedDepthCertificateForCached memo fuel s p with
  | none =>
      simp [hresult] at h
  | some c =>
      apply checkedDepthCertificateForCached_sound
      simpa [hresult]

def checkedDepthCertificateFor (fuel : Nat) (s : Position) (target : Player) :
    Option CompactCertificate :=
  match searchCandidateTree fuel s target with
  | some tree =>
      let c := candidateTreeCertificate target tree
      if checkLocalCertificateAt s c then some c else none
  | none => none
-- 运行无外部缓存的有限深度搜索，并仅保留通过局部检查的证书。

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
-- 证明普通深度搜索一旦返回已检查证书，就可推出 `CanForceWin s p`。

theorem checkedDepthCertificateFor_isSome_sound
    {fuel : Nat} {s : Position} {p : Player}
    (h : (checkedDepthCertificateFor fuel s p).isSome) :
    CanForceWin s p := by
  cases hresult : checkedDepthCertificateFor fuel s p with
  | none =>
      simp [hresult] at h
  | some c =>
      apply checkedDepthCertificateFor_sound
      simpa [hresult]

/- A diagnostic form of the checked finite-depth search.  `checkedDepthCertificateFor`
   intentionally collapses every unsuccessful run to `none`, which is convenient
   for a small API but hides whether the candidate generator found a tree that the
   trusted checker rejected.  This three-way result is still untrusted data; only
   the `accepted` case has a soundness theorem below. -/
inductive CheckedDepthResult where
  | noCandidate
  | rejected (certificate : CompactCertificate)
  | accepted (certificate : CompactCertificate)

def CheckedDepthResult.isAccepted : CheckedDepthResult → Bool
  | .accepted _ => true
  | _ => false

def CheckedDepthResult.isRejected : CheckedDepthResult → Bool
  | .rejected _ => true
  | _ => false

def CheckedDepthResult.isNoCandidate : CheckedDepthResult → Bool
  | .noCandidate => true
  | _ => false

def checkedCandidateTreeResult (s : Position) (target : Player)
    (tree : CandidateTree) : CheckedDepthResult :=
  let c := candidateTreeCertificate target tree
  if checkLocalCertificateAt s c then .accepted c else .rejected c

def checkedDepthResultFor (fuel : Nat) (s : Position) (target : Player) :
    CheckedDepthResult :=
  match searchCandidateTree fuel s target with
  | none => .noCandidate
  | some tree => checkedCandidateTreeResult s target tree

theorem checkedDepthResultFor_accepted_iff
    {fuel : Nat} {s : Position} {p : Player} {c : CompactCertificate} :
    checkedDepthResultFor fuel s p = .accepted c ↔
      checkedDepthCertificateFor fuel s p = some c := by
  unfold checkedDepthResultFor checkedDepthCertificateFor checkedCandidateTreeResult
  cases htree : searchCandidateTree fuel s p with
  | none => simp [htree]
  | some tree =>
      by_cases hcheck : checkLocalCertificateAt s
          (candidateTreeCertificate p tree) = true
      · simp [htree, hcheck, checkedCandidateTreeResult]
      · simp [htree, hcheck, checkedCandidateTreeResult]

theorem checkedDepthResultFor_noCandidate_iff
    {fuel : Nat} {s : Position} {p : Player} :
    checkedDepthResultFor fuel s p = .noCandidate ↔
      searchCandidateTree fuel s p = none := by
  unfold checkedDepthResultFor
  cases htree : searchCandidateTree fuel s p with
  | none => simp [htree]
  | some tree =>
      by_cases hcheck : checkLocalCertificateAt s
          (candidateTreeCertificate p tree) = true
      · simp [htree, hcheck, checkedCandidateTreeResult]
      · simp [htree, hcheck, checkedCandidateTreeResult]

theorem checkedDepthResultFor_rejected_iff
    {fuel : Nat} {s : Position} {p : Player} {c : CompactCertificate} :
    checkedDepthResultFor fuel s p = .rejected c ↔
      ∃ tree, searchCandidateTree fuel s p = some tree ∧
        checkLocalCertificateAt s (candidateTreeCertificate p tree) = false ∧
        c = candidateTreeCertificate p tree := by
  unfold checkedDepthResultFor checkedCandidateTreeResult
  cases htree : searchCandidateTree fuel s p with
  | none => simp [htree]
  | some tree =>
      cases hcheck : checkLocalCertificateAt s
          (candidateTreeCertificate p tree) with
      | false =>
          simp [hcheck]
          exact eq_comm
      | true => simp [htree, hcheck]

theorem checkedDepthResultFor_sound
    {fuel : Nat} {s : Position} {p : Player} {c : CompactCertificate}
    (h : checkedDepthResultFor fuel s p = .accepted c) :
    CanForceWin s p := by
  exact checkedDepthCertificateFor_sound
    ((checkedDepthResultFor_accepted_iff).mp h)

def immediateCertificateNodesChecked (s : Position) (p : Player) : Bool :=
  match firstWinningMove s p with
  | some m =>
      let c := immediateWinCertificate s p m
      checkNodeAt p c.nodes 0 (.proverMove s m 1) &&
        checkNodeAt p c.nodes 1
          (.terminal (play s m) (winner p))
  | none => false
-- 单独检查立即胜证书的两个节点，作为不依赖全局初始根的局部可执行判据。

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
-- 从两个节点的检查结果提取合法性、轮次与获胜终局，推出局部强制获胜。

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
-- 证明合法且轮到 `p` 的落子会使立即胜证书的根“证明方落子”节点通过检查。

theorem immediateWinCertificate_terminal_checked
    {s : Position} {p : Player} {m : Coord}
    (hwin : terminal (play s m) = some (winner p)) :
    checkNodeAt p (immediateWinCertificate s p m).nodes 1
      (.terminal (play s m) (winner p)) = true := by
  simp [immediateWinCertificate, checkNodeAt, checkNode, checkEdgesAt, hwin]
-- 证明落子后确实为目标玩家获胜时，立即胜证书的终局节点通过检查。

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
-- 把两个已验证节点重构为依赖类型的 `CertificateTree p s` 见证。

theorem immediateWinCertificate_sound
    {s : Position} {p : Player} {m : Coord}
    (hturn : s.turn = p) (hlegal : legalMove s m)
    (hwin : terminal (play s m) = some (winner p)) :
    CanForceWin s p :=
  CertificateTree.sound
    (Classical.choice (immediateWinCertificate_reifies hturn hlegal hwin))
-- 由重构后的证书树可靠性证明，立即获胜证书蕴含 `CanForceWin s p`。

theorem checkedSearchResult_sound {cfg : SearchConfig} {search : Searcher}
    (h : CheckedSearchResult cfg search) :
    CanForceWin initialPosition .black := by
  rcases h with ⟨c, _hresult, hcheck⟩
  exact compact_certificate_sound c hcheck
-- 证明任何搜索算法只要返回通过全局检查的证书，就能证明初始局面黑方强制获胜。

def acceptCertificate (c : CompactCertificate) : Option CompactCertificate :=
  if checkCertificate c then some c else none
-- 将全局证书检查器包装为过滤器：有效证书原样接收，无效证书返回 `none`。

theorem acceptCertificate_some_iff (c : CompactCertificate) :
    acceptCertificate c = some c ↔ checkCertificate c = true := by
  simp [acceptCertificate]
-- 刻画证书被接收的充要条件正是全局检查结果为真。

theorem acceptCertificate_sound {c : CompactCertificate}
    (h : acceptCertificate c = some c) :
    CanForceWin initialPosition .black := by
  exact compact_certificate_sound c ((acceptCertificate_some_iff c).mp h)
-- 证明任何被 `acceptCertificate` 接收的证书都给出初始局面黑方强制获胜定理。

/- Executable regression checks for the untrusted candidate generator.  These
   examples check coverage and filtering only; they do not contribute to the
   certificate soundness theorem. -/
example : allCoords.size = 49 := by
  native_decide
-- 回归检查：全坐标数组恰好包含 49 个元素。

example : allCoords[0]? = some ((0, 0) : Coord) := by
  native_decide
-- 回归检查：行优先数组的首元素是左上角坐标 `(0, 0)`。

example : allCoords[24]? = some ((3, 3) : Coord) := by
  native_decide
-- 回归检查：行优先数组的中心索引 24 对应坐标 `(3, 3)`。

example : allCoords[48]? = some ((6, 6) : Coord) := by
  native_decide
-- 回归检查：行优先数组的末元素是右下角坐标 `(6, 6)`。

example : coordIndex ((0, 0) : Coord) = 0 := by
  native_decide
-- 回归检查：左上角的行优先索引为 0。

example : coordIndex ((3, 3) : Coord) = 24 := by
  native_decide
-- 回归检查：中心点的行优先索引为 24。

example : coordIndex ((6, 6) : Coord) = 48 := by
  native_decide
-- 回归检查：右下角的行优先索引为 48。

example (c : Coord) : coordAtIndex (coordIndex c) = c := by
  exact coordAtIndex_coordIndex c
-- 对任意坐标复用逆映射定理，检查编码再解码保持坐标不变。

example : boardKey Board.empty = boardKey Board.empty := by
  rfl
-- 最小自反测试：空棋盘的完整键与自身相等。

example : positionKey initialPosition = positionKey initialPosition := by
  rfl
-- 最小自反测试：初始局面的完整键与自身相等。

example :
    containsPositionKey #[positionKey initialPosition] initialPosition = true := by
  native_decide
-- 回归检查：只含初始局面键的换位表能够命中初始局面。

example :
    containsPositionKey #[positionKey initialPosition]
      (play initialPosition (3, 3)) = false := by
  native_decide
-- 回归检查：初始局面键不会误命中已经在中心落子后的局面。

example : positionKey initialPosition ≠ positionKey (play initialPosition (3, 3)) := by
  intro h
  have hturn := congrArg Prod.fst h
  have hne : (Player.black : Player) ≠ Player.white := by decide
  apply hne
  simpa [positionKey, initialPosition, Position.initial, play, Position.play] using hturn
-- 证明初始局面与首步后的局面具有不同的无损位置键。

example (s : Position) (p : Player) (c : Coord) :
    (winningCellsMask s p).get (coordIndex c) = true ↔
      c ∈ WinningCells s p := by
  exact winningCellsMask_get_iff s p c
-- 回归检查：制胜点掩码的读取规范可直接用于任意局面、玩家与坐标。

example : (candidateMoves initialPosition .black).size = 49 := by
  native_decide
-- 回归检查：初始局面轮到黑方，参考生成器列出全部 49 个落子。

example : (candidateMovesFast initialPosition .black).size = 49 := by
  native_decide
-- 回归检查：快速生成器在初始局面同样列出 49 个落子。

example : ((3, 3) : Coord) ∈ candidateMoves initialPosition .black := by
  native_decide
-- 回归检查：初始局面的中心点属于黑方候选集合。

example : (candidateMoves initialPosition .white).size = 0 := by
  native_decide
-- 回归检查：初始局面尚未轮到白方，参考生成器返回空数组。

example : (candidateMovesFast initialPosition .white).size = 0 := by
  native_decide
-- 回归检查：快速生成器也会拒绝非当前玩家的候选查询。

example :
    (candidateMoves (play initialPosition (3, 3)) .white).size = 48 := by
  native_decide
-- 回归检查：黑方首步后，参考生成器为白方列出剩余 48 个空点。

example :
    (candidateMovesFast (play initialPosition (3, 3)) .white).size = 48 := by
  native_decide
-- 回归检查：黑方首步后，快速生成器与参考实现具有相同候选数。

example :
    (orderedCandidateMoves (play initialPosition (3, 3)) .white).size = 48 := by
  native_decide
-- 回归检查：邻近优先排序不改变首步后候选数组的大小。

example :
    (orderedCandidateMoves (play initialPosition (3, 3)) .white)[0]? =
      some ((2, 2) : Coord) := by
  native_decide
-- 回归检查：中心有棋子时，排序会把相邻的 `(2, 2)` 放到首位。

example :
    ((0, 0) : Coord) ∈
      orderedCandidateMoves (play initialPosition (3, 3)) .white := by
  native_decide
-- 回归检查：即使远离已有棋子，角点仍保留在排序后的完整候选集中。

example :
    ((3, 3) : Coord) ∉ candidateMoves (play initialPosition (3, 3)) .white := by
  native_decide
-- 回归检查：已经被黑棋占据的中心点不会成为白方合法候选。

def searchTerminalBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place
          (Board.place Board.empty (1, 3) .black) (2, 3) .black)
        (3, 3) .black)
      (4, 3) .black)
    (5, 3) .black
-- 构造含有一条黑方横向五连的测试棋盘。

def searchTerminalPosition : Position :=
  ⟨searchTerminalBoard, .white⟩
-- 将五连测试棋盘包装为轮到白方、但实际上已经终局的测试局面。

example : (candidateMoves searchTerminalPosition .white).size = 0 := by
  native_decide
-- 回归检查：即使轮到指定玩家，终局位置也不再产生候选落子。

def searchImmediateBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (1, 3) .black) (2, 3) .black)
      (3, 3) .black)
    (4, 3) .black
-- 构造已有连续四颗黑棋、两端可补成五连的立即获胜测试棋盘。

def searchImmediatePosition : Position :=
  ⟨searchImmediateBoard, .black⟩
-- 将连续四子测试棋盘包装为轮到黑方的局面。

example : (firstWinningMove searchImmediatePosition .black).isSome := by
  native_decide
-- 回归检查：快速扫描能在连续四子局面找到至少一个立即获胜步。

example :
    firstWinningMoveReference searchImmediatePosition .black =
      firstWinningMove searchImmediatePosition .black := by
  native_decide
-- 回归检查：在该测试局面中，完整终局参考扫描与快速扫描返回相同首个胜着。

example :
    terminal (play searchImmediatePosition (0, 3)) = some .blackWin := by
  apply createsFiveFast_terminal_of_immediateCandidate
    (s := searchImmediatePosition) (p := .black) (m := (0, 3))
  · native_decide
  · native_decide
-- 通过快速检测的可靠性桥证明在 `(0, 3)` 落子后终局结果为黑胜。

example :
    (immediateWinningMovesFirst searchImmediatePosition .black)[0]? =
      some ((0, 3) : Coord) := by
  native_decide
-- 回归检查：立即获胜排序把 `(0, 3)` 放在候选数组首位。

example :
    (immediateWinningMovesFirst searchImmediatePosition .black).size = 45 := by
  native_decide
-- 回归检查：四个已占据坐标被排除后，重排数组仍含全部 45 个合法空点。

example : (immediateCertificateFor searchImmediatePosition .black).isSome := by
  native_decide
-- 回归检查：立即胜着存在时能够生成对应的两节点候选证书。

example : immediateCertificateNodesChecked searchImmediatePosition .black = true := by
  native_decide
-- 回归检查：生成的立即胜证书两个节点都通过可信局部检查。

example : CanForceWin searchImmediatePosition .black := by
  apply immediateCertificateNodesChecked_sound
  native_decide
-- 由节点检查可靠性正式证明黑方从该测试局面能够强制获胜。

/- Fast five detection regression suite.  Each board has four stones and the
   tested move fills the fifth point; the boundary case exercises a window
   whose first cell is on the edge of the board. -/
def fastVerticalBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (3, 1) .black) (3, 2) .black)
      (3, 3) .black)
    (3, 4) .black
-- 构造缺少第五子的纵向连续四子测试棋盘。

def fastDiagonalUpBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (1, 1) .black) (2, 2) .black)
      (3, 3) .black)
    (4, 4) .black
-- 构造缺少第五子的上升对角线连续四子测试棋盘。

def fastDiagonalDownBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (1, 5) .black) (2, 4) .black)
      (3, 3) .black)
    (4, 2) .black
-- 构造缺少第五子的下降对角线连续四子测试棋盘。

def fastBoundaryBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (0, 0) .black) (1, 0) .black)
      (2, 0) .black)
    (3, 0) .black
-- 构造贴近棋盘边界、缺少第五子的横向连续四子测试棋盘。

def fastInsufficientBoard : Board :=
  Board.place
    (Board.place
      (Board.place Board.empty (1, 3) .black) (2, 3) .black)
    (3, 3) .black
-- 构造只有三颗连续黑棋、无法一步组成五连的反例棋盘。

example : createsFiveFast searchImmediateBoard .black (0, 3) = true := by
  native_decide
-- 回归检查：快速检测能识别补齐横向五连的落子。

example : createsFiveFast fastVerticalBoard .black (3, 0) = true := by
  native_decide
-- 回归检查：快速检测能识别补齐纵向五连的落子。

example : createsFiveFast fastDiagonalUpBoard .black (0, 0) = true := by
  native_decide
-- 回归检查：快速检测能识别补齐上升对角线五连的落子。

example : createsFiveFast fastDiagonalDownBoard .black (0, 6) = true := by
  native_decide
-- 回归检查：快速检测能识别补齐下降对角线五连的落子。

example : createsFiveFast fastBoundaryBoard .black (4, 0) = true := by
  native_decide
-- 回归检查：快速检测能正确处理从棋盘边界开始的五连窗口。

example : createsFiveFast fastInsufficientBoard .black (4, 3) = false := by
  native_decide
-- 回归检查：仅把三连扩为四连不会被误判为五连。

example : ¬ hasAtLeastFive fastInsufficientBoard .black := by
  native_decide
-- 回归检查：三子反例棋盘本身确实不存在黑方至少五连。

example :
    createsFiveFast searchImmediateBoard .black (0, 3) = true ↔
      hasAtLeastFive (searchImmediateBoard.place (0, 3) .black) .black := by
  exact createsFiveFast_iff (by native_decide)
-- 在具体测试棋盘上实例化快速五连判定与形式化五连谓词的等价定理。

example :
    createsFiveFast searchImmediateBoard .black (0, 3) = true ↔
      terminal (play ⟨searchImmediateBoard, .black⟩ (0, 3)) = some .blackWin := by
  apply createsFiveFast_terminal_iff
    (s := ⟨searchImmediateBoard, .black⟩) (p := .black) (m := (0, 3))
  · rfl
  · native_decide
-- 在合法测试局面上实例化快速五连判定与落子后黑胜终局的等价定理。

end Gomoku
