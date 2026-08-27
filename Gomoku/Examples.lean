import Gomoku.Certificate

/-!
本文件用小型可计算局面串联基础棋盘、规则、几何模式、游戏语义与证书可靠性，
作为各层定义的正向示例和边界回归测试。
-/

namespace Gomoku

def center : Coord := (7, 7)
-- 定义 15×15 棋盘的中心坐标，供后续落子示例复用。

def horizontalFourBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (5, 7) .black) (6, 7) .black)
      (7, 7) .black)
    (8, 7) .black
-- 构造横向连续四颗黑棋且左右仍为空的测试棋盘。

def diagonalFourBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (3, 3) .black) (4, 4) .black)
      (5, 5) .black)
    (6, 6) .black
-- 构造上升对角线方向连续四颗黑棋的测试棋盘。

def boundaryFourBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (0, 7) .black) (1, 7) .black)
      (2, 7) .black)
    (3, 7) .black
-- 构造从左边界开始的横向四子，用于说明边界一侧不算开放端。

def overlineBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place
          (Board.place
            (Board.place Board.empty (4, 7) .black) (5, 7) .black)
          (6, 7) .black)
        (7, 7) .black)
      (8, 7) .black)
    (9, 7) .black
-- 构造六颗连续黑棋，测试自由五子棋规则中长连同样满足“至少五连”。

example : initialPosition.turn = .black := rfl
-- 检查初始局面按定义轮到黑方。

example : initialPosition.board.cell center = .empty := by
  rfl
-- 检查初始棋盘的中心点为空。

example : legalMove initialPosition center := by
  constructor
  · exact Position.initial_not_terminal
  · rfl
-- 由初始局面非终局和中心为空证明黑方可以合法下在中心。

example : ∃ c, legalMove initialPosition c := by
  exact Position.exists_legalMove_of_terminal_none (by
    exact Position.terminal_none_of_not_isTerminal Position.initial_not_terminal)
-- 由非终局局面存在合法步的定理得到初始局面至少有一个可下坐标。

example : legalMove initialPosition
    ((defaultStrategy .black initialPosition Position.Reachable.initial rfl (by
      exact Position.terminal_none_of_not_isTerminal Position.initial_not_terminal)).1) := by
  exact defaultStrategy_legal .black initialPosition Position.Reachable.initial rfl
    (Position.terminal_none_of_not_isTerminal Position.initial_not_terminal)
-- 实例化默认策略的合法性，说明它在可达、非终局且轮到黑方时总会选合法步。

example : (play initialPosition center).turn = .white := by
  rfl
-- 检查黑方首步后行棋方切换为白方。

example : (play initialPosition center).board.cell center = .stone .black := by
  exact Board.place_same _ _ _
-- 检查首步后中心点确实保存黑棋。

example : straightOpenFour horizontalFourBoard .black (5, 7) .horizontal := by
  native_decide
-- 计算验证横向测试棋盘包含一条两端开放的直四。

example : straightOpenFour diagonalFourBoard .black (3, 3) .diagonalUp := by
  native_decide
-- 计算验证对角测试棋盘包含一条上升方向的直四。

example : ¬ straightOpenFour boundaryFourBoard .black (0, 7) .horizontal := by
  native_decide
-- 计算验证贴边四子因左端越界而不是“两端开放”的直四。

example : hasAtLeastFive overlineBoard .black := by
  native_decide
-- 计算验证六连棋盘满足黑方至少五连谓词。

example : terminal ⟨overlineBoard, .white⟩ = some .blackWin := by
  native_decide
-- 计算验证含黑方长连的局面被判为黑胜终局。

example : ¬ legalMove ⟨overlineBoard, .white⟩ center := by
  native_decide
-- 检查终局之后即使存在空点也不允许继续落子。

example : ¬ legalMove (play initialPosition center) center := by
  native_decide
-- 检查已经占据的中心点不能再次落子。

example : Board.emptyCount (Board.place Board.empty center .black) + 1 =
    Board.emptyCount Board.empty := by
  exact Board.emptyCount_place_of_empty _ _ _ rfl
-- 实例化空格计数定理：在空点落一子会使空格数恰好减少一。

example : Position.countBlack (Position.play initialPosition center) = 1 := by
  native_decide
-- 计算验证初始局面黑方首步后黑棋计数为一。

example {s : Position} (h : Reachable s) :
    ¬ (hasAtLeastFive s.board .black ∧ hasAtLeastFive s.board .white) := by
  exact Position.reachable_not_both_winners h
-- 说明任一按合法落子到达的局面不可能同时存在黑白双方五连。

example {s : Position} {p : Player} (hs : Reachable s) :
    (∃ σ : Strategy p, StrategyRealizes σ s hs) ↔ CanForceWin s p := by
  exact strategyRealizes_iff_canForceWin hs
-- 在任意可达局面上展示“存在实现策略”与归纳强制胜谓词的等价关系。

example {s : Position} {p : Player}
    (h : terminal s = some (winner p)) : CanForceWin s p :=
  canForceWin_terminal h
-- 展示目标玩家已获胜的终局可直接构成 `CanForceWin` 证明。

example {s : Position} {p : Player} {m : Coord}
    (hm : legalMove s m)
    (hwin : terminal (play s m) = some (winner p))
    (hturn : s.turn = p) : CanForceWin s p :=
  canForceWin_immediate hm hwin hturn
-- 展示合法的一步立即胜着如何提升为当前局面的强制胜证明。

example :
    CanForceWin ⟨overlineBoard, .white⟩ .black := by
  exact certificate_sound
    { target := .black
      root := ⟨overlineBoard, .white⟩
      proof := .terminal (by native_decide) }
-- 构造依赖类型终局证书并用 `certificate_sound` 得到长连测试局面的黑方强制胜。

example :
    checkCertificate { target := .black, root := 0, nodes := #[] } = false := by
  rfl
-- 检查空节点数组且根索引为零的紧凑证书会被全局检查器拒绝。

end Gomoku
