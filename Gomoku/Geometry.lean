import Gomoku.Basic

namespace Gomoku

inductive Direction where
  | horizontal
  | vertical
  | diagonalUp
  | diagonalDown
  deriving DecidableEq, Repr
-- 枚举棋盘上判断连续棋形所需的横、竖和两条对角线方向。

namespace Direction

def dx : Direction → Int
  | .horizontal => 1
  | .vertical => 0
  | .diagonalUp => 1
  | .diagonalDown => 1
-- 给出沿指定方向前进一步时横坐标的整数增量。

def dy : Direction → Int
  | .horizontal => 0
  | .vertical => 1
  | .diagonalUp => 1
  | .diagonalDown => -1
-- 给出沿指定方向前进一步时纵坐标的整数增量。

end Direction

def directions : Finset Direction :=
  {.horizontal, .vertical, .diagonalUp, .diagonalDown}
-- 收集全部四种需要检查的无向直线方向。

instance : Fintype Direction :=
  ⟨directions, by
    intro d
    cases d <;> simp [directions]⟩
-- 证明 Direction 是有限类型，使程序可以穷举所有四个方向。

private def toFin15 (x : Int) (h : 0 ≤ x ∧ x < 15) : Fin 15 :=
  ⟨x.toNat, by omega⟩
-- 在已有边界证明 h 的前提下，把整数 x 安全转换为 Fin 15。

def step (c : Coord) (d : Direction) (n : Int) : Option Coord :=
  let x := (c.1 : Int) + n * Direction.dx d
  let y := (c.2 : Int) + n * Direction.dy d
  if h : 0 ≤ x ∧ x < 15 ∧ 0 ≤ y ∧ y < 15 then
    some (toFin15 x ⟨h.1, h.2.1⟩, toFin15 y ⟨h.2.2.1, h.2.2.2⟩)
  else
    none
-- 从坐标 c 沿方向 d 移动 n 步；结果越出 15×15 棋盘时返回 none。

theorem step_reverse {c q : Coord} {d : Direction} {n : Int}
    (h : step c d n = some q) : step q d (-n) = some c := by
  rcases c with ⟨⟨cx, hcx⟩, ⟨cy, hcy⟩⟩
  rcases q with ⟨⟨qx, hqx⟩, ⟨qy, hqy⟩⟩
  cases d <;>
    simp [step, Direction.dx, Direction.dy, toFin15] at h ⊢ <;>
    omega
-- 说明有效步进可以用相反步数撤销：从 c 到 q 后再走 -n 步会回到 c。

def lineCells (c : Coord) (d : Direction) (length : Nat) : List Coord :=
  (List.range length).filterMap (fun n => step c d n)
-- 列出从 c 开始沿 d 的前 length 个仍位于棋盘内的坐标。

def occupiedAt (b : Board) (p : Player) (c : Coord) (d : Direction) (n : Int) : Prop :=
  ∃ q, step c d n = some q ∧ b.cell q = .stone p
-- 表示从 c 沿 d 偏移 n 的有效坐标上放有玩家 p 的棋子。

instance occupiedAtDecidable (b : Board) (p : Player) (c : Coord) (d : Direction) (n : Int) :
    Decidable (occupiedAt b p c d n) := by
  unfold occupiedAt
  infer_instance
-- 说明有限步进位置是否由玩家 p 占据可以直接判定。

def consecutive (b : Board) (p : Player) (c : Coord) (d : Direction) (length : Nat) : Prop :=
  ∀ n : Fin length, occupiedAt b p c d n.1
-- 表示从 c 开始沿 d 的 length 个位置全部连续放有玩家 p 的棋子。

instance consecutiveDecidable (b : Board) (p : Player) (c : Coord) (d : Direction)
    (length : Nat) : Decidable (consecutive b p c d length) := by
  unfold consecutive
  infer_instance
-- 说明固定起点、方向和长度的连续棋形可以通过有限检查判定。

def hasRun (b : Board) (p : Player) (length : Nat) : Prop :=
  ∃ c d, consecutive b p c d length
-- 表示棋盘上存在某个起点和方向形成玩家 p 的指定长度连子。

instance hasRunDecidable (b : Board) (p : Player) (length : Nat) :
    Decidable (hasRun b p length) := by
  exact Fintype.decidableExistsFintype
-- 通过穷举有限起点和方向，判定棋盘上是否存在指定长度连子。

def hasAtLeastFive (b : Board) (p : Player) : Prop := hasRun b p 5
-- 表示玩家 p 在棋盘 b 上已经形成至少五个连续棋子的获胜线。

instance hasAtLeastFiveDecidable (b : Board) (p : Player) :
    Decidable (hasAtLeastFive b p) := by
  exact hasRunDecidable b p 5
-- 复用五连存在性的有限判定，得到 hasAtLeastFive 的可判定实例。

/- Placing the other player's stone cannot create a run for `p`.  No
   emptiness assumption is needed: even an overwrite at `r` cannot turn that
   cell into a stone owned by `p`. -/
theorem hasAtLeastFive_of_place_other
    {b : Board} {p q : Player} {r : Coord}
    (hq : q ≠ p) (h : hasAtLeastFive (b.place r q) p) :
    hasAtLeastFive b p := by
  rcases h with ⟨start, d, hcon⟩
  refine ⟨start, d, ?_⟩
  intro n
  rcases hcon n with ⟨x, hxstep, hxcell⟩
  have hxr : x ≠ r := by
    intro hxr
    subst x
    simp [Board.place, hq] at hxcell
  refine ⟨x, hxstep, ?_⟩
  simpa [Board.place, hxr] using hxcell
-- 说明放置另一玩家 q 的棋子不可能为 p 新建五连；落子后的 p 五连在原棋盘中已存在。

def openEnd (b : Board) (c : Coord) (d : Direction) (n : Int) : Prop :=
  ∃ q, step c d n = some q ∧ b.cell q = .empty
-- 表示从 c 沿 d 偏移 n 的位置有效且为空，可作为棋形的开放端点。

instance openEndDecidable (b : Board) (c : Coord) (d : Direction) (n : Int) :
    Decidable (openEnd b c d n) := by
  unfold openEnd
  infer_instance
-- 说明指定偏移位置是否为开放空点可以直接判定。

/- These predicates are deliberately separate from the straight patterns
   above.  Each disjunct is one frozen finite pattern; adding another
   Gomoku convention later must add another named disjunct or predicate. -/
def brokenOpenThree (b : Board) (p : Player) (c : Coord) (d : Direction) : Prop :=
  (occupiedAt b p c d 0 ∧ occupiedAt b p c d 1 ∧ occupiedAt b p c d 3 ∧
      openEnd b c d (-1) ∧ openEnd b c d 2 ∧ openEnd b c d 4) ∨
    (occupiedAt b p c d 0 ∧ occupiedAt b p c d 2 ∧ occupiedAt b p c d 3 ∧
      openEnd b c d (-1) ∧ openEnd b c d 1 ∧ openEnd b c d 4)
-- 描述两种冻结的断三模式：三枚同色棋子中间缺一子，且相关缺口和两端均为空。

instance brokenOpenThreeDecidable (b : Board) (p : Player) (c : Coord) (d : Direction) :
    Decidable (brokenOpenThree b p c d) := by
  unfold brokenOpenThree
  infer_instance
-- 说明给定起点和方向是否满足断三模式可以通过有限条件判定。

def jumpFour (b : Board) (p : Player) (c : Coord) (d : Direction) : Prop :=
  (occupiedAt b p c d 0 ∧ occupiedAt b p c d 1 ∧ occupiedAt b p c d 2 ∧
      occupiedAt b p c d 4 ∧ openEnd b c d (-1) ∧ openEnd b c d 3 ∧
      openEnd b c d 5) ∨
    (occupiedAt b p c d 0 ∧ occupiedAt b p c d 1 ∧ occupiedAt b p c d 3 ∧
      occupiedAt b p c d 4 ∧ openEnd b c d (-1) ∧ openEnd b c d 2 ∧
      openEnd b c d 5) ∨
    (occupiedAt b p c d 0 ∧ occupiedAt b p c d 2 ∧ occupiedAt b p c d 3 ∧
      occupiedAt b p c d 4 ∧ openEnd b c d (-1) ∧ openEnd b c d 1 ∧
      openEnd b c d 5)
-- 描述五格窗口中恰有一个内部缺口的三种跳四模式，并要求窗口两端为空。

instance jumpFourDecidable (b : Board) (p : Player) (c : Coord) (d : Direction) :
    Decidable (jumpFour b p c d) := by
  unfold jumpFour
  infer_instance
-- 说明给定起点和方向是否满足任一跳四模式可以判定。

def straightOpenThree (b : Board) (p : Player) (c : Coord) (d : Direction) : Prop :=
  consecutive b p c d 3 ∧ openEnd b c d (-1) ∧ openEnd b c d 3
-- 描述从 c 开始的直线活三：连续三子且前后两个端点都为空。

instance straightOpenThreeDecidable (b : Board) (p : Player) (c : Coord) (d : Direction) :
    Decidable (straightOpenThree b p c d) := by
  unfold straightOpenThree
  infer_instance
-- 说明固定起点和方向上的直线活三条件可以判定。

def straightOpenFour (b : Board) (p : Player) (c : Coord) (d : Direction) : Prop :=
  consecutive b p c d 4 ∧ openEnd b c d (-1) ∧ openEnd b c d 4
-- 描述从 c 开始的直线活四：连续四子且前后两个端点都为空。

instance straightOpenFourDecidable (b : Board) (p : Player) (c : Coord) (d : Direction) :
    Decidable (straightOpenFour b p c d) := by
  unfold straightOpenFour
  infer_instance
-- 说明固定起点和方向上的直线活四条件可以判定。

def canonicalRunStart (b : Board) (p : Player) (c : Coord) (d : Direction) : Prop :=
  ¬ occupiedAt b p c d (-1)
-- 要求起点 c 的前一格不是玩家 p 的棋子，用作连子起点的规范化条件。

def normalizedStraightOpenThree (b : Board) (p : Player) (c : Coord) (d : Direction) : Prop :=
  straightOpenThree b p c d ∧ canonicalRunStart b p c d
-- 将直线活三与规范起点条件组合，得到规范化的活三表示。

def normalizedStraightOpenFour (b : Board) (p : Player) (c : Coord) (d : Direction) : Prop :=
  straightOpenFour b p c d ∧ canonicalRunStart b p c d
-- 将直线活四与规范起点条件组合，得到规范化的活四表示。

instance canonicalRunStartDecidable (b : Board) (p : Player) (c : Coord) (d : Direction) :
    Decidable (canonicalRunStart b p c d) := by
  unfold canonicalRunStart
  infer_instance
-- 说明某个坐标是否满足规范连子起点条件可以判定。

instance normalizedStraightOpenThreeDecidable (b : Board) (p : Player) (c : Coord) (d : Direction) :
    Decidable (normalizedStraightOpenThree b p c d) := by
  unfold normalizedStraightOpenThree
  infer_instance
-- 说明规范化直线活三条件可以判定。

instance normalizedStraightOpenFourDecidable (b : Board) (p : Player) (c : Coord) (d : Direction) :
    Decidable (normalizedStraightOpenFour b p c d) := by
  unfold normalizedStraightOpenFour
  infer_instance
-- 说明规范化直线活四条件可以判定。

theorem straightOpenThree_canonical {b : Board} {p : Player} {c : Coord} {d : Direction}
    (h : straightOpenThree b p c d) : canonicalRunStart b p c d := by
  intro hstone
  rcases h.2.1 with ⟨q, hq, hempty⟩
  rcases hstone with ⟨q', hq', hstone⟩
  have hqq : q = q' := by
    exact Option.some.inj (hq.symm.trans hq')
  subst q'
  rw [hempty] at hstone
  cases hstone
-- 说明直线活三的左端为空，因此其给定起点自动满足规范起点条件。

theorem straightOpenFour_canonical {b : Board} {p : Player} {c : Coord} {d : Direction}
    (h : straightOpenFour b p c d) : canonicalRunStart b p c d := by
  intro hstone
  rcases h.2.1 with ⟨q, hq, hempty⟩
  rcases hstone with ⟨q', hq', hstone⟩
  have hqq : q = q' := by
    exact Option.some.inj (hq.symm.trans hq')
  subst q'
  rw [hempty] at hstone
  cases hstone
-- 说明直线活四的左端为空，因此其给定起点自动满足规范起点条件。

theorem normalizedStraightOpenThree_iff {b : Board} {p : Player} {c : Coord} {d : Direction} :
    normalizedStraightOpenThree b p c d ↔ straightOpenThree b p c d := by
  constructor
  · exact And.left
  · intro h
    exact ⟨h, straightOpenThree_canonical h⟩
-- 说明规范起点条件对直线活三是自动成立的，规范化前后的命题等价。

theorem normalizedStraightOpenFour_iff {b : Board} {p : Player} {c : Coord} {d : Direction} :
    normalizedStraightOpenFour b p c d ↔ straightOpenFour b p c d := by
  constructor
  · exact And.left
  · intro h
    exact ⟨h, straightOpenFour_canonical h⟩
-- 说明规范起点条件对直线活四是自动成立的，规范化前后的命题等价。

/- A maximal run is a finite consecutive segment that cannot be extended by
   another stone of the same player at either endpoint.  Boundary cells are
   handled by `occupiedAt`: an out-of-board step simply has no witness. -/
def MaximalRun (b : Board) (p : Player) (c : Coord) (d : Direction)
    (length : Nat) : Prop :=
  consecutive b p c d length ∧
    ¬ occupiedAt b p c d (-1) ∧
    ¬ occupiedAt b p c d (length : Int)
-- 描述不能在任一端继续接上同色棋子的极大连续段，棋盘边界也视为不可延伸。

instance maximalRunDecidable (b : Board) (p : Player) (c : Coord) (d : Direction)
    (length : Nat) : Decidable (MaximalRun b p c d length) := by
  unfold MaximalRun
  infer_instance
-- 说明固定参数下的极大连续段条件可以判定。

theorem not_occupiedAt_of_openEnd {b : Board} {p : Player} {c : Coord} {d : Direction}
    {n : Int} (hopen : openEnd b c d n) : ¬ occupiedAt b p c d n := by
  intro hocc
  rcases hopen with ⟨q, hstep, hempty⟩
  rcases hocc with ⟨q', hstep', hstone⟩
  have hqq : q = q' := Option.some.inj (hstep.symm.trans hstep')
  subst q'
  rw [hempty] at hstone
  cases hstone
-- 说明同一偏移位置若为空，就不可能同时被任意玩家 p 的棋子占据。

theorem straightOpenThree_maximalRun {b : Board} {p : Player} {c : Coord} {d : Direction}
    (h : straightOpenThree b p c d) : MaximalRun b p c d 3 := by
  refine ⟨h.1, ?_, ?_⟩
  · exact not_occupiedAt_of_openEnd h.2.1
  · exact not_occupiedAt_of_openEnd h.2.2
-- 说明两端均为空的直线活三必然构成长度为 3 的极大连续段。

theorem straightOpenFour_maximalRun {b : Board} {p : Player} {c : Coord} {d : Direction}
    (h : straightOpenFour b p c d) : MaximalRun b p c d 4 := by
  refine ⟨h.1, ?_, ?_⟩
  · exact not_occupiedAt_of_openEnd h.2.1
  · exact not_occupiedAt_of_openEnd h.2.2
-- 说明两端均为空的直线活四必然构成长度为 4 的极大连续段。

/- `StartShiftConflict` is the precise overlap condition needed for a
   uniqueness statement.  It says that `c'` is a positive-offset cell of the
   run starting at `c`, and that the cell immediately before `c'` is the
   previous cell of that same run.  Separate runs in the same direction do
   not satisfy this relation, so no false global uniqueness claim is made. -/
def StartShiftConflict (length : Nat) (c c' : Coord) (d : Direction) : Prop :=
  ∃ i : Fin length, 0 < i.1 ∧ ∃ q,
    step c d (i.1 : Int) = some c' ∧
      step c d ((i.1 : Int) - 1) = some q ∧
        step c' d (-1) = some q
-- 表示 c' 是从 c 开始的连段内部正偏移起点，且两种方式计算出的前一格相同。

instance startShiftConflictDecidable (length : Nat) (c c' : Coord) (d : Direction) :
    Decidable (StartShiftConflict length c c' d) := by
  unfold StartShiftConflict
  infer_instance
-- 说明两个起点之间是否存在指定长度内的偏移冲突可以判定。

theorem consecutive_not_startShiftConflict
    {b : Board} {p : Player} {length : Nat}
    {c c' : Coord} {d : Direction}
    (hcon : consecutive b p c d length)
    (hleft : openEnd b c' d (-1))
    (hconf : StartShiftConflict length c c' d) : False := by
  rcases hconf with ⟨i, hi, q, hstart, hprev, hback⟩
  have hprevBound : i.1 - 1 < length := by omega
  rcases hcon ⟨i.1 - 1, hprevBound⟩ with ⟨q', hq', hstone⟩
  have hq'coord : step c d ((i.1 : Int) - 1) = some q' := by
    have hiNat : 1 ≤ i.1 := by omega
    have hcast : ((i.1 - 1 : Nat) : Int) = (i.1 : Int) - 1 := by
      rw [Nat.cast_sub hiNat]
      norm_num
    simpa [hcast] using hq'
  have hqq : q' = q := by
    exact Option.some.inj (hq'coord.symm.trans hprev)
  subst q'
  rcases hleft with ⟨q'', hleftStep, hempty⟩
  have hqq' : q'' = q := by
    exact Option.some.inj (hleftStep.symm.trans hback)
  subst q''
  rw [hempty] at hstone
  cases hstone
-- 说明连续段内部的偏移起点，其前一格已有同色棋子，因而不可能同时是开放左端。

theorem consecutive_not_startShiftConflict_of_not_occupied
    {b : Board} {p : Player} {length : Nat}
    {c c' : Coord} {d : Direction}
    (hcon : consecutive b p c d length)
    (hleft : ¬ occupiedAt b p c' d (-1))
    (hconf : StartShiftConflict length c c' d) : False := by
  rcases hconf with ⟨i, hi, q, hstart, hprev, hback⟩
  have hprevBound : i.1 - 1 < length := by omega
  rcases hcon ⟨i.1 - 1, hprevBound⟩ with ⟨q', hq', hstone⟩
  have hq'coord : step c d ((i.1 : Int) - 1) = some q' := by
    have hiNat : 1 ≤ i.1 := by omega
    have hcast : ((i.1 - 1 : Nat) : Int) = (i.1 : Int) - 1 := by
      rw [Nat.cast_sub hiNat]
      norm_num
    simpa [hcast] using hq'
  have hqq : q' = q := Option.some.inj (hq'coord.symm.trans hprev)
  subst q'
  exact hleft ⟨q, hback, hstone⟩
-- 将上一冲突结论推广为：只要偏移起点前一格不是同色棋子，就不可能发生起点偏移冲突。

theorem straightOpenThree_not_startShiftConflict
    {b : Board} {p : Player} {c c' : Coord} {d : Direction}
    (h : straightOpenThree b p c d)
    (h' : straightOpenThree b p c' d)
    (hconf : StartShiftConflict 3 c c' d) : False := by
  exact consecutive_not_startShiftConflict h.1 h'.2.1 hconf
-- 说明同方向的两个直线活三起点不能以长度 3 的内部正偏移方式互相重叠。

theorem straightOpenFour_not_startShiftConflict
    {b : Board} {p : Player} {c c' : Coord} {d : Direction}
    (h : straightOpenFour b p c d)
    (h' : straightOpenFour b p c' d)
    (hconf : StartShiftConflict 4 c c' d) : False := by
  exact consecutive_not_startShiftConflict h.1 h'.2.1 hconf
-- 说明同方向的两个直线活四起点不能以长度 4 的内部正偏移方式互相重叠。

def ComparableRunStarts (length : Nat) (c c' : Coord) (d : Direction) : Prop :=
  c = c' ∨ StartShiftConflict length c c' d ∨ StartShiftConflict length c' c d
-- 表示两个连段起点相同，或其中一个是另一个连段内部可比较的偏移起点。

theorem normalizedStraightOpenThree_unique_of_comparable
    {b : Board} {p : Player} {c c' : Coord} {d : Direction}
    (h : normalizedStraightOpenThree b p c d)
    (h' : normalizedStraightOpenThree b p c' d)
    (hcompare : ComparableRunStarts 3 c c' d) : c = c' := by
  rcases hcompare with hsame | hconf | hconf
  · exact hsame
  · exact False.elim (straightOpenThree_not_startShiftConflict h.1 h'.1 hconf)
  · exact False.elim (straightOpenThree_not_startShiftConflict h'.1 h.1 hconf)
-- 说明两个可比较的规范化直线活三只能拥有同一个起点。

theorem normalizedStraightOpenFour_unique_of_comparable
    {b : Board} {p : Player} {c c' : Coord} {d : Direction}
    (h : normalizedStraightOpenFour b p c d)
    (h' : normalizedStraightOpenFour b p c' d)
    (hcompare : ComparableRunStarts 4 c c' d) : c = c' := by
  rcases hcompare with hsame | hconf | hconf
  · exact hsame
  · exact False.elim (straightOpenFour_not_startShiftConflict h.1 h'.1 hconf)
  · exact False.elim (straightOpenFour_not_startShiftConflict h'.1 h.1 hconf)
-- 说明两个可比较的规范化直线活四只能拥有同一个起点。

theorem maximalRun_unique_of_comparable
    {b : Board} {p : Player} {length : Nat}
    {c c' : Coord} {d : Direction}
    (h : MaximalRun b p c d length)
    (h' : MaximalRun b p c' d length)
    (hcompare : ComparableRunStarts length c c' d) : c = c' := by
  rcases hcompare with hsame | hconf | hconf
  · exact hsame
  · exact False.elim
      (consecutive_not_startShiftConflict_of_not_occupied h.1 h'.2.1 hconf)
  · exact False.elim
      (consecutive_not_startShiftConflict_of_not_occupied h'.1 h.2.1 hconf)
-- 说明同方向、同长度且起点可比较的两个极大连续段必有相同起点。

def StraightOpenThree (b : Board) (p : Player) : Prop :=
  ∃ c d, straightOpenThree b p c d
-- 表示棋盘上至少存在一个起点和方向构成玩家 p 的直线活三。

def StraightOpenFour (b : Board) (p : Player) : Prop :=
  ∃ c d, straightOpenFour b p c d
-- 表示棋盘上至少存在一个起点和方向构成玩家 p 的直线活四。

@[simp] theorem directions_horizontal : Direction.dx .horizontal = 1 := rfl
-- 记录横向单位步的横坐标增量为 1，供化简器直接使用。

end Gomoku
