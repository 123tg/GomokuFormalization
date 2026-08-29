import Gomoku.Generated.Draw7x7s5WhiteDefense
import Gomoku.Generated.Draw7x7s5BlackDefense

namespace Gomoku.Generated

/-! 7x7 标准和棋 (seed 5): 21 黑 + 21 白, 轮到黑方, 7 个空格。
每个长度 5 窗口都同时含黑子和白子, 任何一方都无法成五;
两侧防守证书由 C++ DefenseSearcher 独立生成, Lean 检查器验证后
用 standardDraw_of_mutualDefense 组合出和棋。 -/

def draw7x7s5RootPosition : Position := draw7x7s5WhiteDefenseRootPosition

set_option linter.style.nativeDecide false in
theorem draw7x7s5WhiteChecked :
    checkDefenseCertificateAt draw7x7s5RootPosition draw7x7s5WhiteDefenseCertificate = true := by
  native_decide

theorem draw7x7s5WhitePrevents : WhiteCanPreventBlackWin draw7x7s5RootPosition :=
  white_defense_certificate_sound draw7x7s5RootPosition draw7x7s5WhiteDefenseCertificate rfl draw7x7s5WhiteChecked

set_option linter.style.nativeDecide false in
theorem draw7x7s5BlackChecked :
    checkDefenseCertificateAt draw7x7s5RootPosition draw7x7s5BlackDefenseCertificate = true := by
  native_decide

theorem draw7x7s5BlackPrevents : BlackCanPreventWhiteWin draw7x7s5RootPosition :=
  black_defense_certificate_sound draw7x7s5RootPosition draw7x7s5BlackDefenseCertificate rfl draw7x7s5BlackChecked

theorem draw7x7s5StandardDraw : StandardDraw draw7x7s5RootPosition :=
  standardDraw_of_mutualDefense draw7x7s5WhitePrevents draw7x7s5BlackPrevents

end Gomoku.Generated