import Gomoku.Generated.Draw7x7s2WhiteDefense
import Gomoku.Generated.Draw7x7s2BlackDefense

namespace Gomoku.Generated

/-! 7x7 标准和棋 (seed 2): 21 黑 + 21 白, 轮到黑方, 7 个空格。
每个长度 5 窗口都同时含黑子和白子, 任何一方都无法成五;
两侧防守证书由 C++ DefenseSearcher 独立生成, Lean 检查器验证后
用 standardDraw_of_mutualDefense 组合出和棋。 -/

def draw7x7s2RootPosition : Position := draw7x7s2WhiteDefenseRootPosition

set_option linter.style.nativeDecide false in
theorem draw7x7s2WhiteChecked :
    checkDefenseCertificateAt draw7x7s2RootPosition draw7x7s2WhiteDefenseCertificate = true := by
  native_decide

theorem draw7x7s2WhitePrevents : WhiteCanPreventBlackWin draw7x7s2RootPosition :=
  white_defense_certificate_sound draw7x7s2RootPosition draw7x7s2WhiteDefenseCertificate rfl draw7x7s2WhiteChecked

set_option linter.style.nativeDecide false in
theorem draw7x7s2BlackChecked :
    checkDefenseCertificateAt draw7x7s2RootPosition draw7x7s2BlackDefenseCertificate = true := by
  native_decide

theorem draw7x7s2BlackPrevents : BlackCanPreventWhiteWin draw7x7s2RootPosition :=
  black_defense_certificate_sound draw7x7s2RootPosition draw7x7s2BlackDefenseCertificate rfl draw7x7s2BlackChecked

theorem draw7x7s2StandardDraw : StandardDraw draw7x7s2RootPosition :=
  standardDraw_of_mutualDefense draw7x7s2WhitePrevents draw7x7s2BlackPrevents

end Gomoku.Generated