import Gomoku.Rules

/-!
参数化小棋盘实验层。

该模块不改动现有 `Gomoku.Coord`、`Gomoku.Board` 或 `Gomoku.Position`，而是在
`Gomoku.Parametric` 中把棋盘边长与获胜连珠长度放入 `GameSpec`。这样原有
15×15 证明保持不变，同时可以独立实例化并搜索真正的 5×5 棋盘。
-/

namespace Gomoku.Parametric

structure GameSpec where
  boardSize : Nat
  winLength : Nat
  deriving DecidableEq, Repr
-- 同时记录方形棋盘边长与获胜所需的连续棋子数。

abbrev Coord (spec : GameSpec) := Fin spec.boardSize × Fin spec.boardSize
-- 根据 `spec.boardSize` 在类型层限制参数化棋盘坐标。

structure Board (spec : GameSpec) where
  cell : Coord spec → Cell
-- 保存参数化棋盘上每个合法坐标的格子状态。

namespace Board

def empty (spec : GameSpec) : Board spec := ⟨fun _ => .empty⟩
-- 构造指定规格的空棋盘。

def place {spec : GameSpec} (b : Board spec) (c : Coord spec)
    (p : Player) : Board spec :=
  ⟨fun d => if d = c then .stone p else b.cell d⟩
-- 在指定坐标放置棋子，并保留其他格子的原状态。

def emptyCount {spec : GameSpec} (b : Board spec) : Nat :=
  ((Finset.univ : Finset (Coord spec)).filter
    (fun c => b.cell c = .empty)).card
-- 统计参数化棋盘的空格数量。

end Board

structure Position (spec : GameSpec) where
  board : Board spec
  turn : Player
-- 把参数化棋盘与下一手玩家组合为局面。

private def toFin {spec : GameSpec} (x : Int)
    (h : 0 ≤ x ∧ x < spec.boardSize) : Fin spec.boardSize :=
  ⟨x.toNat, by omega⟩
-- 在边界证明成立时，把整数坐标安全转换为参数化有限坐标。

def step {spec : GameSpec} (c : Coord spec) (d : Direction)
    (offset : Int) : Option (Coord spec) :=
  let x := (c.1 : Int) + offset * Direction.dx d
  let y := (c.2 : Int) + offset * Direction.dy d
  if h : 0 ≤ x ∧ x < spec.boardSize ∧
      0 ≤ y ∧ y < spec.boardSize then
    some (toFin x ⟨h.1, h.2.1⟩,
      toFin y ⟨h.2.2.1, h.2.2.2⟩)
  else
    none
-- 沿四种直线方向移动；越出参数化棋盘时返回 `none`。

def allCoords (spec : GameSpec) : Array (Coord spec) :=
  (Array.ofFn fun x : Fin spec.boardSize =>
    Array.ofFn fun y : Fin spec.boardSize => (x, y)).flatten
-- 枚举指定棋盘的全部坐标。

def searchDirections : Array Direction :=
  #[.horizontal, .vertical, .diagonalUp, .diagonalDown]
-- 列出判定连珠时需要检查的四个无向方向。

def consecutive (spec : GameSpec) (b : Board spec) (p : Player)
    (start : Coord spec) (d : Direction) : Bool :=
  (List.range spec.winLength).all (fun offset =>
    match step start d (Int.ofNat offset) with
    | some c => decide (b.cell c = .stone p)
    | none => false)
-- 判断从起点沿给定方向的 `spec.winLength` 个格子是否均为玩家棋子。

def hasRun (spec : GameSpec) (b : Board spec) (p : Player) : Bool :=
  (allCoords spec).any (fun start =>
    searchDirections.any (consecutive spec b p start))
-- 穷举起点与方向，检查玩家是否已经形成规定长度的连珠。

def terminal (spec : GameSpec) (s : Position spec) : Option Outcome :=
  if hasRun spec s.board .black then some .blackWin
  else if hasRun spec s.board .white then some .whiteWin
  else if Board.emptyCount s.board = 0 then some .draw
  else none
-- 按黑胜、白胜、满盘和棋的顺序计算参数化局面的终局结果。

def legalMove (spec : GameSpec) (s : Position spec) (c : Coord spec) : Bool :=
  decide (terminal spec s = none) && decide (s.board.cell c = .empty)
-- 检查局面尚未终结且目标坐标为空。

def play {spec : GameSpec} (s : Position spec) (c : Coord spec) : Position spec :=
  ⟨s.board.place c s.turn, s.turn.other⟩
-- 执行落子并把行动权交给对手。

def legalMoves (spec : GameSpec) (s : Position spec) : Array (Coord spec) :=
  (allCoords spec).filter (legalMove spec s)
-- 枚举局面上的全部合法落子。

theorem mem_allCoords (spec : GameSpec) (c : Coord spec) :
    c ∈ allCoords spec := by
  rcases c with ⟨x, y⟩
  rw [allCoords, Array.mem_flatten]
  refine ⟨Array.ofFn (fun y : Fin spec.boardSize => (x, y)), ?_, ?_⟩
  · rw [Array.mem_ofFn]
    exact ⟨x, rfl⟩
  · rw [Array.mem_ofFn]
    exact ⟨y, rfl⟩
-- 证明参数化坐标枚举不会遗漏任何合法坐标。

theorem mem_legalMoves_iff (spec : GameSpec) (s : Position spec)
    (c : Coord spec) :
    c ∈ legalMoves spec s ↔ legalMove spec s c = true := by
  simp [legalMoves, mem_allCoords]
-- 把合法着法数组成员关系等价为可执行合法性检查成功。

theorem legalMove_eq_true_iff (spec : GameSpec) (s : Position spec)
    (c : Coord spec) :
    legalMove spec s c = true ↔
      terminal spec s = none ∧ s.board.cell c = .empty := by
  simp [legalMove]
-- 展开布尔合法性检查，得到非终局与空格两个事实。

inductive ForceWin (spec : GameSpec) (target : Player) :
    Position spec → Prop where
  | terminal {s : Position spec}
      (h : terminal spec s = some (winner target)) : ForceWin spec target s
  | choose {s : Position spec}
      (hterm : terminal spec s = none)
      (hturn : s.turn = target)
      (m : Coord spec)
      (hm : legalMove spec s m = true)
      (child : ForceWin spec target (play s m)) : ForceWin spec target s
  | respond {s : Position spec}
      (hterm : terminal spec s = none)
      (hturn : s.turn = Player.other target)
      (children : ∀ m, legalMove spec s m = true →
        ForceWin spec target (play s m)) : ForceWin spec target s
-- 表达目标方终局获胜、选择一个获胜着法以及覆盖对手全部合法应手。

structure TwoPlyCertificate (spec : GameSpec) (root : Position spec)
    (target : Player) where
  responses : Array (Coord spec × Coord spec)
-- 以根局面和目标玩家为类型索引，为每个对手应手记录目标方的一步获胜回复。

def firstWinningMove (spec : GameSpec) (s : Position spec)
    (target : Player) : Option (Coord spec) :=
  (legalMoves spec s).find? (fun m =>
    decide (terminal spec (play s m) = some (winner target)))
-- 在全部合法落子中寻找第一个能立即形成目标方胜局的着法。

def collectTwoPlyResponses (spec : GameSpec) (root : Position spec)
    (target : Player) : List (Coord spec) →
      Option (List (Coord spec × Coord spec))
  | [] => some []
  | reply :: rest =>
      match firstWinningMove spec (play root reply) target,
          collectTwoPlyResponses spec root target rest with
      | some winningMove, some responses =>
          some ((reply, winningMove) :: responses)
      | _, _ => none
-- 逐一处理对手合法应手；任一分支没有立即胜着就拒绝整张两层证书。

def searchTwoPly (spec : GameSpec) (root : Position spec)
    (target : Player) : Option (TwoPlyCertificate spec root target) :=
  if terminal spec root = none ∧ root.turn = Player.other target then
    match collectTwoPlyResponses spec root target
        (legalMoves spec root).toList with
    | some responses =>
        some {
          responses := responses.toArray }
    | none => none
  else
    none
-- 在对手节点执行完整两层搜索，并把所有应手及其立即胜着打包为候选证书。

def checkTwoPlyCertificate {spec : GameSpec} {root : Position spec}
    {target : Player}
    (certificate : TwoPlyCertificate spec root target) : Bool :=
  decide (terminal spec root = none) &&
    decide (root.turn = Player.other target) &&
    (legalMoves spec root).all (fun reply =>
      certificate.responses.any (fun response =>
        decide (response.1 = reply) &&
          legalMove spec (play root reply) response.2 &&
          decide (terminal spec
            (play (play root reply) response.2) =
              some (winner target))))
-- 独立检查根信息，并确认每个对手合法应手都有合法且立即获胜的回复。

theorem checkTwoPlyCertificate_sound {spec : GameSpec} {root : Position spec}
    {target : Player}
    (certificate : TwoPlyCertificate spec root target)
    (h : checkTwoPlyCertificate certificate = true) :
    ForceWin spec target root := by
  simp only [checkTwoPlyCertificate,
    Bool.and_eq_true_eq_eq_true_and_eq_true] at h
  have htermB : decide (terminal spec root = none) = true := by
    aesop
  have hturnB :
      decide (root.turn = Player.other target) = true := by
    aesop
  have hcovered :
      (legalMoves spec root).all (fun reply =>
        certificate.responses.any (fun response =>
          decide (response.1 = reply) &&
            legalMove spec (play root reply) response.2 &&
            decide (terminal spec
              (play (play root reply) response.2) =
                some (winner target)))) = true := by
    aesop
  have hterm := of_decide_eq_true htermB
  have hturn := of_decide_eq_true hturnB
  apply ForceWin.respond hterm hturn
  intro reply hreplyLegal
  have hreplyMem : reply ∈ legalMoves spec root :=
    (mem_legalMoves_iff spec root reply).2 hreplyLegal
  rw [Array.all_eq_true'] at hcovered
  have hresponse := hcovered reply hreplyMem
  rw [Array.any_eq_true'] at hresponse
  rcases hresponse with ⟨response, _hresponseMem, hresponseChecked⟩
  rcases response with ⟨responseReply, winningMove⟩
  simp only [Bool.and_eq_true_eq_eq_true_and_eq_true] at hresponseChecked
  have hresponseMove : responseReply = reply :=
    of_decide_eq_true hresponseChecked.1.1
  subst responseReply
  have hwinningLegal :
      legalMove spec (play root reply) winningMove = true :=
    hresponseChecked.1.2
  have hwinningTerminal :
      terminal spec (play (play root reply) winningMove) =
        some (winner target) := by
    exact of_decide_eq_true hresponseChecked.2
  have hchildTerm : terminal spec (play root reply) = none :=
    (legalMove_eq_true_iff spec (play root reply) winningMove).1
      hwinningLegal |>.1
  have hchildTurn : (play root reply).turn = target := by
    simp [play, hturn]
  exact ForceWin.choose hchildTerm hchildTurn winningMove hwinningLegal
    (ForceWin.terminal hwinningTerminal)
-- 证明两层检查器通过后，证书确实覆盖所有对手应手并给出目标方强制胜。

def fiveByFiveSpec : GameSpec :=
  { boardSize := 5, winLength := 5 }
-- 实例化真正的 5×5 棋盘，并保持五子连珠获胜规则。

def fiveByFiveForkBoard : Board fiveByFiveSpec :=
  ⟨fun c =>
    if (c.2.1 = 0 ∧ c.1.1 < 4) ∨ (c.1.1 = 0 ∧ c.2.1 < 4) then
      .stone .black
    else
      .empty⟩
-- 构造首行与首列各有四枚黑子的交叉双威胁棋盘。

def fiveByFiveForkPosition : Position fiveByFiveSpec :=
  ⟨fiveByFiveForkBoard, .white⟩
-- 令白方在双威胁形成后行动，以测试对手全应手搜索。

def fiveByFiveForkSearch : Option
    (TwoPlyCertificate fiveByFiveSpec fiveByFiveForkPosition .black) :=
  searchTwoPly fiveByFiveSpec fiveByFiveForkPosition .black
-- 在 5×5 双威胁局面执行完整的两层搜索。

set_option linter.style.nativeDecide false in
def fiveByFiveForkCertificate :
    TwoPlyCertificate fiveByFiveSpec fiveByFiveForkPosition .black :=
  fiveByFiveForkSearch.get (by native_decide)
-- 从已计算成功的搜索结果中取得候选证书。

set_option linter.style.nativeDecide false in
example : Board.emptyCount fiveByFiveForkBoard = 18 := by
  native_decide
-- 确认根棋盘有七枚黑子与十八个白方合法应手。

set_option linter.style.nativeDecide false in
example : fiveByFiveForkCertificate.responses.size = 18 := by
  native_decide
-- 确认搜索证书为白方全部十八种合法落子都生成了黑方回复。

set_option linter.style.nativeDecide false in
theorem fiveByFiveForkCertificate_checked :
    checkTwoPlyCertificate fiveByFiveForkCertificate = true := by
  native_decide
-- 由参数化检查器重新验证搜索器生成的 5×5 两层证书。

theorem fiveByFive_black_forces_win :
    ForceWin fiveByFiveSpec .black fiveByFiveForkPosition := by
  exact checkTwoPlyCertificate_sound fiveByFiveForkCertificate
    fiveByFiveForkCertificate_checked
-- 得到正式结论：黑方在该 5×5 双威胁局面中能够强制获胜。

end Gomoku.Parametric
