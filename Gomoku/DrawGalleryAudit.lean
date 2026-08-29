import Gomoku.Pairing
import Gomoku.Generated.Draw7x7
import Gomoku.Generated.Draw7x7s2
import Gomoku.Generated.Draw7x7s3
import Gomoku.Generated.Draw7x7s4
import Gomoku.Generated.Draw7x7s5
import Gomoku.Generated.Draw7x7s6
import Gomoku.Generated.Draw7x7s7
import Gomoku.Generated.Draw7x7s8
import Gomoku.Generated.Draw7x7s9

/-!
汇总审计:9 个 7×7 和棋局面,每个都独立验证
  1) 两侧防守证书通过 Lean 检查器 (checkDefenseCertificateAt);
  2) 根局面为 21 黑 + 21 白、7 空、轮到黑方;
  3) 每个长度 5 窗口同时含黑子和白子 (双方永远无法成五);
  4) 由两张防守证书组合出 `StandardDraw`。

全部断言均为机器可判定 (native_decide),不依赖任何 C++ 结果。
-/

namespace Gomoku.DrawGalleryAudit

open Gomoku.Generated

/-- 每个完整窗口都含至少一黑一白。 -/
def BothColorsInEveryWindow (s : Position) : Prop :=
  ∀ c d, Pairing.windowFull c d = true →
    (∃ q ∈ Pairing.fiveWindow c d, s.board.cell q = .stone .black) ∧
    (∃ q ∈ Pairing.fiveWindow c d, s.board.cell q = .stone .white)

instance bothColorsDecidable (s : Position) : Decidable (BothColorsInEveryWindow s) := by
  unfold BothColorsInEveryWindow
  infer_instance

/-- 局面形状断言:21 黑 + 21 白 + 7 空 + 轮到黑方。 -/
def ShapeOk (s : Position) : Prop :=
  Board.count s.board .black = 21 ∧ Board.count s.board .white = 21 ∧
    Board.emptyCount s.board = 7 ∧ s.turn = .black

instance shapeOkDecidable (s : Position) : Decidable (ShapeOk s) := by
  unfold ShapeOk
  infer_instance

/-! ## 局面 1: Draw7x7 -/

set_option linter.style.nativeDecide false in
theorem case1_white_checked :
    checkDefenseCertificateAt draw7x7RootPosition draw7x7WhiteDefenseCertificate = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case1_black_checked :
    checkDefenseCertificateAt draw7x7RootPosition draw7x7BlackDefenseCertificate = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case1_shape : ShapeOk draw7x7RootPosition := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case1_both_colors : BothColorsInEveryWindow draw7x7RootPosition := by
  native_decide

theorem case1_draw : StandardDraw draw7x7RootPosition := draw7x7StandardDraw

/-! ## 局面 2: Draw7x7s2 -/

set_option linter.style.nativeDecide false in
theorem case2_white_checked :
    checkDefenseCertificateAt draw7x7s2RootPosition draw7x7s2WhiteDefenseCertificate = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case2_black_checked :
    checkDefenseCertificateAt draw7x7s2RootPosition draw7x7s2BlackDefenseCertificate = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case2_shape : ShapeOk draw7x7s2RootPosition := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case2_both_colors : BothColorsInEveryWindow draw7x7s2RootPosition := by
  native_decide

theorem case2_draw : StandardDraw draw7x7s2RootPosition := draw7x7s2StandardDraw

/-! ## 局面 3: Draw7x7s3 -/

set_option linter.style.nativeDecide false in
theorem case3_white_checked :
    checkDefenseCertificateAt draw7x7s3RootPosition draw7x7s3WhiteDefenseCertificate = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case3_black_checked :
    checkDefenseCertificateAt draw7x7s3RootPosition draw7x7s3BlackDefenseCertificate = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case3_shape : ShapeOk draw7x7s3RootPosition := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case3_both_colors : BothColorsInEveryWindow draw7x7s3RootPosition := by
  native_decide

theorem case3_draw : StandardDraw draw7x7s3RootPosition := draw7x7s3StandardDraw

/-! ## 局面 4: Draw7x7s4 -/

set_option linter.style.nativeDecide false in
theorem case4_white_checked :
    checkDefenseCertificateAt draw7x7s4RootPosition draw7x7s4WhiteDefenseCertificate = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case4_black_checked :
    checkDefenseCertificateAt draw7x7s4RootPosition draw7x7s4BlackDefenseCertificate = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case4_shape : ShapeOk draw7x7s4RootPosition := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case4_both_colors : BothColorsInEveryWindow draw7x7s4RootPosition := by
  native_decide

theorem case4_draw : StandardDraw draw7x7s4RootPosition := draw7x7s4StandardDraw

/-! ## 局面 5: Draw7x7s5 -/

set_option linter.style.nativeDecide false in
theorem case5_white_checked :
    checkDefenseCertificateAt draw7x7s5RootPosition draw7x7s5WhiteDefenseCertificate = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case5_black_checked :
    checkDefenseCertificateAt draw7x7s5RootPosition draw7x7s5BlackDefenseCertificate = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case5_shape : ShapeOk draw7x7s5RootPosition := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case5_both_colors : BothColorsInEveryWindow draw7x7s5RootPosition := by
  native_decide

theorem case5_draw : StandardDraw draw7x7s5RootPosition := draw7x7s5StandardDraw

/-! ## 局面 6: Draw7x7s6 -/

set_option linter.style.nativeDecide false in
theorem case6_white_checked :
    checkDefenseCertificateAt draw7x7s6RootPosition draw7x7s6WhiteDefenseCertificate = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case6_black_checked :
    checkDefenseCertificateAt draw7x7s6RootPosition draw7x7s6BlackDefenseCertificate = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case6_shape : ShapeOk draw7x7s6RootPosition := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case6_both_colors : BothColorsInEveryWindow draw7x7s6RootPosition := by
  native_decide

theorem case6_draw : StandardDraw draw7x7s6RootPosition := draw7x7s6StandardDraw

/-! ## 局面 7: Draw7x7s7 -/

set_option linter.style.nativeDecide false in
theorem case7_white_checked :
    checkDefenseCertificateAt draw7x7s7RootPosition draw7x7s7WhiteDefenseCertificate = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case7_black_checked :
    checkDefenseCertificateAt draw7x7s7RootPosition draw7x7s7BlackDefenseCertificate = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case7_shape : ShapeOk draw7x7s7RootPosition := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case7_both_colors : BothColorsInEveryWindow draw7x7s7RootPosition := by
  native_decide

theorem case7_draw : StandardDraw draw7x7s7RootPosition := draw7x7s7StandardDraw

/-! ## 局面 8: Draw7x7s8 -/

set_option linter.style.nativeDecide false in
theorem case8_white_checked :
    checkDefenseCertificateAt draw7x7s8RootPosition draw7x7s8WhiteDefenseCertificate = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case8_black_checked :
    checkDefenseCertificateAt draw7x7s8RootPosition draw7x7s8BlackDefenseCertificate = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case8_shape : ShapeOk draw7x7s8RootPosition := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case8_both_colors : BothColorsInEveryWindow draw7x7s8RootPosition := by
  native_decide

theorem case8_draw : StandardDraw draw7x7s8RootPosition := draw7x7s8StandardDraw

/-! ## 局面 9: Draw7x7s9 -/

set_option linter.style.nativeDecide false in
theorem case9_white_checked :
    checkDefenseCertificateAt draw7x7s9RootPosition draw7x7s9WhiteDefenseCertificate = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case9_black_checked :
    checkDefenseCertificateAt draw7x7s9RootPosition draw7x7s9BlackDefenseCertificate = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case9_shape : ShapeOk draw7x7s9RootPosition := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case9_both_colors : BothColorsInEveryWindow draw7x7s9RootPosition := by
  native_decide

theorem case9_draw : StandardDraw draw7x7s9RootPosition := draw7x7s9StandardDraw

/-! ## 汇总:9 个局面全部和棋 -/

theorem draw7x7_all_nine :
    StandardDraw draw7x7RootPosition ∧
    StandardDraw draw7x7s2RootPosition ∧
    StandardDraw draw7x7s3RootPosition ∧
    StandardDraw draw7x7s4RootPosition ∧
    StandardDraw draw7x7s5RootPosition ∧
    StandardDraw draw7x7s6RootPosition ∧
    StandardDraw draw7x7s7RootPosition ∧
    StandardDraw draw7x7s8RootPosition ∧
    StandardDraw draw7x7s9RootPosition := by
  constructor
  · exact draw7x7StandardDraw
  · constructor
    · exact draw7x7s2StandardDraw
    · constructor
      · exact draw7x7s3StandardDraw
      · constructor
        · exact draw7x7s4StandardDraw
        · constructor
          · exact draw7x7s5StandardDraw
          · constructor
            · exact draw7x7s6StandardDraw
            · constructor
              · exact draw7x7s7StandardDraw
              · constructor
                · exact draw7x7s8StandardDraw
                · exact draw7x7s9StandardDraw

theorem all_nine_white_certificates_checked :
    (checkDefenseCertificateAt draw7x7RootPosition draw7x7WhiteDefenseCertificate = true) ∧
    (checkDefenseCertificateAt draw7x7s2RootPosition draw7x7s2WhiteDefenseCertificate = true) ∧
    (checkDefenseCertificateAt draw7x7s3RootPosition draw7x7s3WhiteDefenseCertificate = true) ∧
    (checkDefenseCertificateAt draw7x7s4RootPosition draw7x7s4WhiteDefenseCertificate = true) ∧
    (checkDefenseCertificateAt draw7x7s5RootPosition draw7x7s5WhiteDefenseCertificate = true) ∧
    (checkDefenseCertificateAt draw7x7s6RootPosition draw7x7s6WhiteDefenseCertificate = true) ∧
    (checkDefenseCertificateAt draw7x7s7RootPosition draw7x7s7WhiteDefenseCertificate = true) ∧
    (checkDefenseCertificateAt draw7x7s8RootPosition draw7x7s8WhiteDefenseCertificate = true) ∧
    (checkDefenseCertificateAt draw7x7s9RootPosition draw7x7s9WhiteDefenseCertificate = true) := by
  constructor
  · exact case1_white_checked
  · constructor
    · exact case2_white_checked
    · constructor
      · exact case3_white_checked
      · constructor
        · exact case4_white_checked
        · constructor
          · exact case5_white_checked
          · constructor
            · exact case6_white_checked
            · constructor
              · exact case7_white_checked
              · constructor
                · exact case8_white_checked
                · exact case9_white_checked

theorem all_nine_black_certificates_checked :
    (checkDefenseCertificateAt draw7x7RootPosition draw7x7BlackDefenseCertificate = true) ∧
    (checkDefenseCertificateAt draw7x7s2RootPosition draw7x7s2BlackDefenseCertificate = true) ∧
    (checkDefenseCertificateAt draw7x7s3RootPosition draw7x7s3BlackDefenseCertificate = true) ∧
    (checkDefenseCertificateAt draw7x7s4RootPosition draw7x7s4BlackDefenseCertificate = true) ∧
    (checkDefenseCertificateAt draw7x7s5RootPosition draw7x7s5BlackDefenseCertificate = true) ∧
    (checkDefenseCertificateAt draw7x7s6RootPosition draw7x7s6BlackDefenseCertificate = true) ∧
    (checkDefenseCertificateAt draw7x7s7RootPosition draw7x7s7BlackDefenseCertificate = true) ∧
    (checkDefenseCertificateAt draw7x7s8RootPosition draw7x7s8BlackDefenseCertificate = true) ∧
    (checkDefenseCertificateAt draw7x7s9RootPosition draw7x7s9BlackDefenseCertificate = true) := by
  constructor
  · exact case1_black_checked
  · constructor
    · exact case2_black_checked
    · constructor
      · exact case3_black_checked
      · constructor
        · exact case4_black_checked
        · constructor
          · exact case5_black_checked
          · constructor
            · exact case6_black_checked
            · constructor
              · exact case7_black_checked
              · constructor
                · exact case8_black_checked
                · exact case9_black_checked

theorem all_nine_shapes_ok :
    ShapeOk draw7x7RootPosition ∧ ShapeOk draw7x7s2RootPosition ∧
    ShapeOk draw7x7s3RootPosition ∧ ShapeOk draw7x7s4RootPosition ∧
    ShapeOk draw7x7s5RootPosition ∧ ShapeOk draw7x7s6RootPosition ∧
    ShapeOk draw7x7s7RootPosition ∧ ShapeOk draw7x7s8RootPosition ∧
    ShapeOk draw7x7s9RootPosition := by
  constructor
  · exact case1_shape
  · constructor
    · exact case2_shape
    · constructor
      · exact case3_shape
      · constructor
        · exact case4_shape
        · constructor
          · exact case5_shape
          · constructor
            · exact case6_shape
            · constructor
              · exact case7_shape
              · constructor
                · exact case8_shape
                · exact case9_shape

theorem all_nine_both_colors :
    BothColorsInEveryWindow draw7x7RootPosition ∧
    BothColorsInEveryWindow draw7x7s2RootPosition ∧
    BothColorsInEveryWindow draw7x7s3RootPosition ∧
    BothColorsInEveryWindow draw7x7s4RootPosition ∧
    BothColorsInEveryWindow draw7x7s5RootPosition ∧
    BothColorsInEveryWindow draw7x7s6RootPosition ∧
    BothColorsInEveryWindow draw7x7s7RootPosition ∧
    BothColorsInEveryWindow draw7x7s8RootPosition ∧
    BothColorsInEveryWindow draw7x7s9RootPosition := by
  constructor
  · exact case1_both_colors
  · constructor
    · exact case2_both_colors
    · constructor
      · exact case3_both_colors
      · constructor
        · exact case4_both_colors
        · constructor
          · exact case5_both_colors
          · constructor
            · exact case6_both_colors
            · constructor
              · exact case7_both_colors
              · constructor
                · exact case8_both_colors
                · exact case9_both_colors

end Gomoku.DrawGalleryAudit
