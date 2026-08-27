import Gomoku.Geometry

namespace Gomoku

inductive Outcome where
  | blackWin
  | whiteWin
  | draw
  deriving DecidableEq, Repr
-- 表示终局结果：黑胜、白胜或和棋。

def winner : Player → Outcome
  | .black => .blackWin
  | .white => .whiteWin
-- 把获胜玩家转换为对应的终局结果。

structure Position where
  board : Board
  turn : Player
-- 一个局面由当前棋盘和下一手应行动的玩家组成。

namespace Position

def initial : Position := ⟨Board.empty, .black⟩
-- 定义空棋盘且轮到黑方行动的初始局面。

def isTerminal (s : Position) : Prop :=
  hasAtLeastFive s.board .black ∨ hasAtLeastFive s.board .white ∨ Board.full s.board
-- 表示局面已经结束：任一方形成五连，或棋盘已满。

instance isTerminalDecidable (s : Position) : Decidable (isTerminal s) := by
  unfold isTerminal
  infer_instance
-- 说明局面的终止性可通过有限棋盘检查判定。

def terminal (s : Position) : Option Outcome :=
  if hasAtLeastFive s.board .black then some .blackWin
  else if hasAtLeastFive s.board .white then some .whiteWin
  else if Board.full s.board then some .draw
  else none
-- 计算局面的终局结果；按黑胜、白胜、满盘和棋的顺序检查，未结束时返回 none。

def legalMove (s : Position) (c : Coord) : Prop :=
  ¬ isTerminal s ∧ s.board.cell c = .empty
-- 定义合法落子：当前局面未结束且目标坐标为空。

instance legalMoveDecidable (s : Position) (c : Coord) : Decidable (legalMove s c) := by
  unfold legalMove
  infer_instance
-- 说明指定坐标在给定局面中是否合法可以判定。

def play (s : Position) (c : Coord) : Position :=
  ⟨s.board.place c s.turn, s.turn.other⟩
-- 执行一次落子：在 c 放置当前玩家棋子，并把行动权交给对手。

inductive Reachable : Position → Prop where
  | initial : Reachable Position.initial
  | step {s : Position} {c : Coord} :
      Reachable s → legalMove s c → Reachable (play s c)
-- 归纳定义可达局面：从初始局面出发，仅经过合法落子得到的局面。

def countBlack (s : Position) : Nat := s.board.count .black
-- 统计局面中的黑棋数量。
def countWhite (s : Position) : Nat := s.board.count .white
-- 统计局面中的白棋数量。

theorem legalMove_empty {s : Position} {c : Coord} (h : legalMove s c) :
    s.board.cell c = .empty := h.2
-- 从合法落子条件中提取目标坐标为空这一事实。

theorem play_turn (s : Position) (c : Coord) : (play s c).turn = s.turn.other := rfl
-- 说明执行落子后轮次必定切换到当前玩家的对手。

theorem play_legal_cell {s : Position} {c : Coord} (h : legalMove s c) :
    (play s c).board.cell c = .stone s.turn := by
  exact Board.place_same _ _ _
-- 说明合法落子后目标坐标由落子前的当前玩家占据。

theorem terminal_no_legal {s : Position} (hs : isTerminal s) (c : Coord) :
    ¬ legalMove s c := by
  intro h
  exact h.1 hs
-- 说明任何终局都不存在合法落子。

theorem terminal_outcome_isTerminal {s : Position} {o : Outcome}
    (h : terminal s = some o) : isTerminal s := by
  unfold terminal at h
  split at h
  · exact Or.inl ‹hasAtLeastFive s.board .black›
  · split at h
    · exact Or.inr (Or.inl ‹hasAtLeastFive s.board .white›)
    · split at h
      · exact Or.inr (Or.inr ‹Board.full s.board›)
      · simp at h
-- 说明 terminal 返回具体结果时，命题形式的 isTerminal 必然成立。

theorem terminal_winner_hasAtLeastFive {s : Position} {p : Player}
    (h : terminal s = some (winner p)) :
    hasAtLeastFive s.board p := by
  cases p with
  | black =>
      simp only [winner] at h
      unfold terminal at h
      split at h
      · assumption
      · split at h
        · simp at h
        · split at h <;> simp at h
  | white =>
      simp only [winner] at h
      unfold terminal at h
      split at h
      · simp at h
      · split at h
        · assumption
        · split at h <;> simp at h
-- 说明若 terminal 宣告玩家 p 获胜，则 p 的棋盘上确实存在五连。

theorem terminal_outcome_no_legal {s : Position} {o : Outcome}
    (h : terminal s = some o) (c : Coord) : ¬ legalMove s c := by
  exact terminal_no_legal (terminal_outcome_isTerminal h) c
-- 把计算出的终局结果转换为“任意坐标都不能合法落子”的结论。

theorem full_no_legal {s : Position} (hfull : Board.full s.board) (c : Coord) :
    ¬ legalMove s c := by
  intro h
  exact (hfull c) h.2
-- 说明满盘时不存在空坐标，因此不存在合法落子。

theorem terminal_none_of_not_isTerminal {s : Position} (h : ¬ isTerminal s) :
    terminal s = none := by
  unfold terminal
  split <;> simp_all [isTerminal]
-- 说明非终局的可执行终局检测结果必为 none。

theorem not_isTerminal_of_terminal_none {s : Position}
    (h : terminal s = none) : ¬ isTerminal s := by
  intro hs
  rcases hs with hb | hw | hf
  · by_cases hb' : hasAtLeastFive s.board .black
    · simp [terminal, hb'] at h
    · exact (hb' hb).elim
  · by_cases hb' : hasAtLeastFive s.board .black
    · simp [terminal, hb'] at h
    · simp [terminal, hb', hw] at h
  · by_cases hb' : hasAtLeastFive s.board .black
    · simp [terminal, hb'] at h
    · by_cases hw' : hasAtLeastFive s.board .white
      · simp [terminal, hb', hw'] at h
      · simp [terminal, hb', hw', hf] at h
-- 说明 terminal 返回 none 时，局面既无胜者也未满，因此不是终局。

theorem exists_legalMove_of_terminal_none {s : Position}
    (h : terminal s = none) : ∃ c, legalMove s c := by
  have hnotfull : ¬ Board.full s.board := by
    intro hfull
    exact (not_isTerminal_of_terminal_none h)
      (Or.inr (Or.inr hfull))
  have hempty : ∃ c, s.board.cell c = .empty := by
    by_contra hne
    apply hnotfull
    intro c
    by_contra hc
    exact hne ⟨c, hc⟩
  rcases hempty with ⟨c, hc⟩
  exact ⟨c, ⟨not_isTerminal_of_terminal_none h, hc⟩⟩
-- 说明未终局局面必有至少一个空点，从而存在合法落子。

theorem initial_not_terminal : ¬ isTerminal initial := by
  intro h
  rcases h with h | h | h
  · rcases h with ⟨c, d, hc⟩
    have hstone : (Position.initial.board).cell c = .stone .black := by
      rcases hc ⟨0, by omega⟩ with ⟨q, hq, hcell⟩
      simpa [initial, Board.empty] using hcell
    simp [initial, Board.empty] at hstone
  · rcases h with ⟨c, d, hc⟩
    have hstone : (Position.initial.board).cell c = .stone .white := by
      rcases hc ⟨0, by omega⟩ with ⟨q, hq, hcell⟩
      simpa [initial, Board.empty] using hcell
    simp [initial, Board.empty] at hstone
  · have hempty : Position.initial.board.cell (0, 0) = .empty := by
      rfl
    exact h (0, 0) hempty
-- 说明空棋盘初始局面没有五连且未满，因此不是终局。

theorem play_preserves_other_cells {s : Position} {c d : Coord}
    (hlegal : legalMove s c) (hne : d ≠ c) :
    (play s c).board.cell d = s.board.cell d := by
  change (s.board.place c s.turn).cell d = s.board.cell d
  exact Board.place_other s.board hne s.turn
-- 说明一次合法落子只改变目标坐标，其他棋盘格保持不变。

theorem play_target_cell {s : Position} {c : Coord} (hlegal : legalMove s c) :
    (play s c).board.cell c = .stone s.turn :=
  Board.place_same _ _ _
-- 再次以全局 play 接口记录落子后目标格的精确内容。

theorem play_emptyCount_succ {s : Position} {c : Coord} (hlegal : legalMove s c) :
    Board.emptyCount (play s c).board + 1 = Board.emptyCount s.board := by
  simpa [play] using Board.emptyCount_place_of_empty s.board c s.turn hlegal.2
-- 说明合法落子恰好消耗一个空点。

theorem play_emptyCount_lt {s : Position} {c : Coord} (hlegal : legalMove s c) :
    Board.emptyCount (play s c).board < Board.emptyCount s.board := by
  have h := play_emptyCount_succ hlegal
  omega
-- 说明每次合法落子都会严格减少空点数，为后续良基递归提供度量。

/- A legal move starts from a position with no winner.  The newly placed
   stone may create a line only for the mover, so the child cannot contain
   winning lines for both players. -/
theorem play_not_both_winners {s : Position} {c : Coord}
    (hlegal : legalMove s c) :
    ¬ (hasAtLeastFive (play s c).board .black ∧
      hasAtLeastFive (play s c).board .white) := by
  intro hboth
  cases hturn : s.turn with
  | black =>
      have hwhite : hasAtLeastFive s.board .white := by
        apply hasAtLeastFive_of_place_other (p := .white) (q := .black)
          (r := c) (by simp)
        simpa [play, hturn] using hboth.2
      exact hlegal.1 (Or.inr (Or.inl hwhite))
  | white =>
      have hblack : hasAtLeastFive s.board .black := by
        apply hasAtLeastFive_of_place_other (p := .black) (q := .white)
          (r := c) (by simp)
        simpa [play, hturn] using hboth.1
      exact hlegal.1 (Or.inl hblack)
-- 说明从非终局执行合法落子后，不可能同时出现黑白双方五连。

theorem reachable_count_invariant {s : Position} (h : Reachable s) :
    (match s.turn with
    | .black => countBlack s = countWhite s
    | .white => countBlack s = countWhite s + 1) := by
  induction h with
  | initial => rfl
  | @step s c hs hlegal ih =>
      cases hturn : s.turn with
      | black =>
          have hblack :
              (play s c).board.count .black = s.board.count .black + 1 := by
            simpa [play, hturn] using Board.count_place_same_of_empty s.board c .black hlegal.2
          have hwhite :
              (play s c).board.count .white = s.board.count .white := by
            simpa [play, hturn] using Board.count_place_other_of_empty s.board c .black .white hlegal.2 (by simp)
          have hchildturn : (play s c).turn = .white := by
            simp [play_turn, hturn]
          rw [hchildturn]
          simp [countBlack, countWhite, hblack, hwhite]
          have ih' : s.board.count .black = s.board.count .white := by
            simpa [countBlack, countWhite, hturn] using ih
          rw [ih']
      | white =>
          have hblack :
              (play s c).board.count .black = s.board.count .black := by
            simpa [play, hturn] using Board.count_place_other_of_empty s.board c .white .black hlegal.2 (by simp)
          have hwhite :
              (play s c).board.count .white = s.board.count .white + 1 := by
            simpa [play, hturn] using Board.count_place_same_of_empty s.board c .white hlegal.2
          have hchildturn : (play s c).turn = .black := by
            simp [play_turn, hturn]
          rw [hchildturn]
          simp [countBlack, countWhite, hblack, hwhite]
          have ih' : s.board.count .black = s.board.count .white + 1 := by
            simpa [countBlack, countWhite, hturn] using ih
          exact ih'
-- 证明可达局面的棋子数与轮次一致：黑方回合两方等量，白方回合黑方多一子。

theorem reachable_not_both_winners {s : Position} (h : Reachable s) :
    ¬ (hasAtLeastFive s.board .black ∧ hasAtLeastFive s.board .white) := by
  cases h with
  | initial =>
      intro hboth
      exact initial_not_terminal (Or.inl hboth.1)
  | step _ hlegal =>
      exact play_not_both_winners hlegal
-- 由可达性的最后一步归纳证明任一可达局面都不会同时有两个胜者。

end Position

def IsTerminal (s : Position) : Prop := Position.isTerminal s
-- 在 Gomoku 命名空间暴露局面终止性的统一别名。
def legalMove (s : Position) (c : Coord) : Prop := Position.legalMove s c
-- 在全局命名空间暴露合法落子谓词。
def play (s : Position) (c : Coord) : Position := Position.play s c
-- 在全局命名空间暴露执行落子的状态转移函数。
def terminal (s : Position) : Option Outcome := Position.terminal s
-- 在全局命名空间暴露可执行终局检测函数。
def initialPosition : Position := Position.initial
-- 在全局命名空间暴露标准初始局面。
def Reachable (s : Position) : Prop := Position.Reachable s
-- 在全局命名空间暴露从初始局面可达的谓词。

instance legalMoveDecidableGlobal (s : Position) (c : Coord) : Decidable (legalMove s c) := by
  exact Position.legalMoveDecidable s c
-- 为全局 legalMove 别名提供对应的可判定实例。

end Gomoku
