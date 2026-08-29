import Gomoku.Generated.Draw7x7s6WhiteDefense
import Gomoku.Generated.Draw7x7s6BlackDefense

namespace Gomoku.Generated

/-! 7x7 标准和棋 (seed 6): 21 黑 + 21 白, 轮到黑方, 7 个空格。
每个长度 5 窗口都同时含黑子和白子, 任何一方都无法成五;
两侧防守证书由 C++ DefenseSearcher 独立生成, Lean 检查器验证后
用 standardDraw_of_mutualDefense 组合出和棋。 -/

def draw7x7s6RootPosition : Position := draw7x7s6WhiteDefenseRootPosition

set_option linter.style.nativeDecide false in
theorem draw7x7s6WhiteChecked :
    checkDefenseCertificateAt draw7x7s6RootPosition draw7x7s6WhiteDefenseCertificate = true := by
  native_decide

theorem draw7x7s6WhitePrevents : WhiteCanPreventBlackWin draw7x7s6RootPosition :=
  white_defense_certificate_sound draw7x7s6RootPosition draw7x7s6WhiteDefenseCertificate rfl draw7x7s6WhiteChecked

set_option linter.style.nativeDecide false in
theorem draw7x7s6BlackChecked :
    checkDefenseCertificateAt draw7x7s6RootPosition draw7x7s6BlackDefenseCertificate = true := by
  native_decide

theorem draw7x7s6BlackPrevents : BlackCanPreventWhiteWin draw7x7s6RootPosition :=
  black_defense_certificate_sound draw7x7s6RootPosition draw7x7s6BlackDefenseCertificate rfl draw7x7s6BlackChecked

theorem draw7x7s6StandardDraw : StandardDraw draw7x7s6RootPosition :=
  standardDraw_of_mutualDefense draw7x7s6WhitePrevents draw7x7s6BlackPrevents

end Gomoku.Generated