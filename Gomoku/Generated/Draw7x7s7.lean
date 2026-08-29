import Gomoku.Generated.Draw7x7s7WhiteDefense
import Gomoku.Generated.Draw7x7s7BlackDefense

namespace Gomoku.Generated

/-! 7x7 标准和棋 (seed 7): 21 黑 + 21 白, 轮到黑方, 7 个空格。
每个长度 5 窗口都同时含黑子和白子, 任何一方都无法成五;
两侧防守证书由 C++ DefenseSearcher 独立生成, Lean 检查器验证后
用 standardDraw_of_mutualDefense 组合出和棋。 -/

def draw7x7s7RootPosition : Position := draw7x7s7WhiteDefenseRootPosition

set_option linter.style.nativeDecide false in
theorem draw7x7s7WhiteChecked :
    checkDefenseCertificateAt draw7x7s7RootPosition draw7x7s7WhiteDefenseCertificate = true := by
  native_decide

theorem draw7x7s7WhitePrevents : WhiteCanPreventBlackWin draw7x7s7RootPosition :=
  white_defense_certificate_sound draw7x7s7RootPosition draw7x7s7WhiteDefenseCertificate rfl draw7x7s7WhiteChecked

set_option linter.style.nativeDecide false in
theorem draw7x7s7BlackChecked :
    checkDefenseCertificateAt draw7x7s7RootPosition draw7x7s7BlackDefenseCertificate = true := by
  native_decide

theorem draw7x7s7BlackPrevents : BlackCanPreventWhiteWin draw7x7s7RootPosition :=
  black_defense_certificate_sound draw7x7s7RootPosition draw7x7s7BlackDefenseCertificate rfl draw7x7s7BlackChecked

theorem draw7x7s7StandardDraw : StandardDraw draw7x7s7RootPosition :=
  standardDraw_of_mutualDefense draw7x7s7WhitePrevents draw7x7s7BlackPrevents

end Gomoku.Generated