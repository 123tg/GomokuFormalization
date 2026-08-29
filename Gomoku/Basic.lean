import Mathlib

/-!
基础数据层：定义玩家、棋盘格、7×7 坐标与函数式棋盘，并证明落子对棋子数和空格数的影响。
-/

namespace Gomoku

inductive Player where
  | black
  | white
  deriving DecidableEq, Repr
-- 表示五子棋的两名玩家，并提供可判定相等性和可打印表示。

namespace Player

def other : Player → Player
  | .black => .white
  | .white => .black
-- 返回给定玩家的对手：黑方对应白方，白方对应黑方。

@[simp] theorem other_black : other .black = .white := rfl
-- 说明黑方的对手按定义就是白方。
@[simp] theorem other_white : other .white = .black := rfl
-- 说明白方的对手按定义就是黑方。

@[simp] theorem other_other (p : Player) : other (other p) = p := by
  cases p <;> rfl
-- 说明连续交换两次玩家会回到原玩家。

@[simp] theorem other_ne_self (p : Player) : other p ≠ p := by
  cases p <;> simp
-- 说明任意玩家的对手都不等于该玩家自身。

@[simp] theorem self_ne_other (p : Player) : p ≠ other p := by
  cases p <;> simp
-- 给出上一结论的反向不等式形式：任意玩家都不等于自己的对手。

end Player

inductive Cell where
  | empty
  | stone (player : Player)
  deriving DecidableEq, Repr
-- 表示棋盘格的状态：空点或由某一玩家占据的棋子。

namespace Cell

def owner : Cell → Option Player
  | .empty => none
  | .stone p => some p
-- 查询棋盘格的占有者；空点返回 none，棋子返回对应玩家。

@[simp] theorem owner_empty : owner .empty = none := rfl
-- 说明空棋盘格没有占有者。
@[simp] theorem owner_stone (p : Player) : owner (.stone p) = some p := rfl
-- 说明玩家 p 的棋子所占棋盘格的占有者正是 p。

end Cell

abbrev Coord := Fin 7 × Fin 7
-- 用两个范围为 0 至 6 的有限自然数表示 7×7 棋盘坐标。

structure Board where
  cell : Coord → Cell
-- 棋盘由从每个合法坐标到其棋盘格状态的函数表示。

namespace Board

def empty : Board := ⟨fun _ => .empty⟩
-- 构造所有坐标均为空点的棋盘。

instance : Inhabited Board := ⟨empty⟩
-- 以空棋盘作为 Board 类型的默认值。

def place (b : Board) (c : Coord) (p : Player) : Board :=
  ⟨fun d => if d = c then .stone p else b.cell d⟩
-- 在坐标 c 放置玩家 p 的棋子，并保持其余坐标的状态不变。

@[simp] theorem empty_cell (c : Coord) : empty.cell c = .empty := rfl
-- 说明空棋盘上的任意坐标都是空点。

theorem place_same (b : Board) (c : Coord) (p : Player) :
    (place b c p).cell c = .stone p := by
  simp [place]
-- 说明在坐标 c 落子后，该坐标保存的正是玩家 p 的棋子。

theorem place_other (b : Board) {c d : Coord} (h : d ≠ c) (p : Player) :
    (place b c p).cell d = b.cell d := by
  simp [place, h]
-- 说明在坐标 c 落子不会改变任何不同坐标 d 的状态。

theorem place_commute_of_ne (b : Board) {c d : Coord} {p q : Player}
    (h : c ≠ d) :
    (place (place b c p) d q) = place (place b d q) c p := by
  cases b with
  | mk f =>
    apply congrArg (fun g : Coord → Cell => Board.mk g)
    funext x
    by_cases hxc : x = c
    · subst x
      simp [place, h]
    · by_cases hxd : x = d
      · subst x
        have hdc : d ≠ c := hxc
        simp [place, h, hdc]
      · simp [place, hxc, hxd]
-- 说明在两个不同坐标落子时，交换两次落子的先后顺序不会改变最终棋盘。

def count (b : Board) (p : Player) : Nat :=
  ((Finset.univ : Finset Coord).filter (fun c => b.cell c = .stone p)).card
-- 统计棋盘 b 上属于玩家 p 的棋子数量。

def emptyCount (b : Board) : Nat :=
  ((Finset.univ : Finset Coord).filter (fun c => b.cell c = .empty)).card
-- 统计棋盘 b 上空坐标的数量。

def full (b : Board) : Prop := ∀ c, b.cell c ≠ .empty
-- 表示棋盘 b 已满，即每个合法坐标都不是空点。

private theorem filter_place_eq_insert (b : Board) (c : Coord) (p : Player)
    (P : Cell → Prop) [DecidablePred P]
    (hnew : P (.stone p)) (hold : ¬ P (b.cell c)) :
    (Finset.univ : Finset Coord).filter (fun d => P ((place b c p).cell d)) =
      insert c (((Finset.univ : Finset Coord).erase c).filter (fun d => P (b.cell d))) := by
  ext d
  by_cases hd : d = c
  · subst d
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_univ, true_and]
    simpa [place] using hnew
  · simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase,
      Finset.mem_univ, true_and, and_true]
    simp [place, hd]
-- 把落子后满足性质 P 的坐标集合分解为新坐标 c 与其余原有坐标，供计数证明复用。

private theorem filter_erase_of_not (P : Coord → Prop) [DecidablePred P]
    (c : Coord) (h : ¬ P c) :
    (Finset.univ : Finset Coord).filter P =
      ((Finset.univ : Finset Coord).erase c).filter P := by
  rw [← Finset.insert_erase (by simp : c ∈ (Finset.univ : Finset Coord))]
  rw [Finset.filter_insert]
  simp [h]
-- 当坐标 c 不满足 P 时，先删除 c 再筛选不会改变最终的筛选集合。

theorem count_place_same_of_empty (b : Board) (c : Coord) (p : Player)
    (h : b.cell c = .empty) :
    (place b c p).count p = b.count p + 1 := by
  classical
  let P : Coord → Prop := fun d => b.cell d = .stone p
  have hnew : (fun x : Cell => x = .stone p) (.stone p) := rfl
  have hold : ¬ (fun x : Cell => x = .stone p) (b.cell c) := by simp [h]
  have heq := filter_place_eq_insert b c p (fun x : Cell => x = .stone p) hnew hold
  have herase := filter_erase_of_not P c (by simp [P, h])
  unfold count
  change (Finset.univ.filter (fun d => (place b c p).cell d = .stone p)).card = _
  rw [heq]
  rw [← herase]
  simp [P, h, Nat.add_comm]
-- 说明在空坐标放置玩家 p 的棋子后，p 的棋子总数恰好增加一。

theorem count_place_other_of_empty (b : Board) (c : Coord) (p q : Player)
    (h : b.cell c = .empty) (hq : q ≠ p) :
    (place b c p).count q = b.count q := by
  classical
  let P : Coord → Prop := fun d => b.cell d = .stone q
  have hpq : p ≠ q := by intro hpq; exact hq hpq.symm
  have hnew : ¬ ((fun x : Cell => x = .stone q) (.stone p)) := by simp [hpq]
  have hold : ¬ (fun x : Cell => x = .stone q) (b.cell c) := by simp [h]
  have heq :
      (Finset.univ : Finset Coord).filter (fun d => (place b c p).cell d = .stone q) =
        ((Finset.univ : Finset Coord).erase c).filter P := by
    rw [← Finset.insert_erase (by simp : c ∈ (Finset.univ : Finset Coord))]
    rw [Finset.filter_insert]
    have hcnew : ¬ ((fun d => (place b c p).cell d = .stone q) c) := by
      simpa [place] using hnew
    rw [if_neg hcnew]
    rw [Finset.erase_insert (by simp : c ∉ (Finset.univ : Finset Coord).erase c)]
    apply Finset.filter_congr
    intro d hd
    have hdc : d ≠ c := (Finset.mem_erase.mp hd).1
    simp [place, hdc, P]
  unfold count
  rw [heq]
  exact (congrArg Finset.card (filter_erase_of_not P c (by simp [P, h]))).symm
-- 说明在空坐标放置 p 的棋子不会改变另一玩家 q 的棋子总数。

theorem emptyCount_place_of_empty (b : Board) (c : Coord) (p : Player)
    (h : b.cell c = .empty) :
    (place b c p).emptyCount + 1 = b.emptyCount := by
  classical
  let P : Coord → Prop := fun d => b.cell d = .empty
  have heq :
      (Finset.univ : Finset Coord).filter (fun d => (place b c p).cell d = .empty) =
        ((Finset.univ : Finset Coord).erase c).filter P := by
    rw [← Finset.insert_erase (by simp : c ∈ (Finset.univ : Finset Coord))]
    rw [Finset.filter_insert]
    have hcnew : ¬ ((fun d => (place b c p).cell d = .empty) c) := by
      simpa [place] using h
    rw [if_neg hcnew]
    rw [Finset.erase_insert (by simp : c ∉ (Finset.univ : Finset Coord).erase c)]
    apply Finset.filter_congr
    intro d hd
    have hdc : d ≠ c := (Finset.mem_erase.mp hd).1
    simp [place, hdc, P]
  unfold emptyCount
  rw [heq]
  rw [Finset.filter_erase]
  exact Finset.card_erase_add_one (by simp [P, h])
-- 说明在一个空坐标落子后，空点数量恰好减少一。

instance fullDecidable (b : Board) : Decidable (full b) := by
  exact Fintype.decidableForallFintype
-- 说明有限棋盘是否已满可以通过检查全部 49 个坐标来判定。

end Board

end Gomoku
