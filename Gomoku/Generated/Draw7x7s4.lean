import Gomoku.Generated.Draw7x7s4WhiteDefense
import Gomoku.Generated.Draw7x7s4BlackDefense

namespace Gomoku.Generated

/-! 7x7 标准和棋 (seed 4): 21 黑 + 21 白, 轮到黑方, 7 个空格。
每个长度 5 窗口都同时含黑子和白子, 任何一方都无法成五;
两侧防守证书由 C++ DefenseSearcher 独立生成, Lean 检查器验证后
用 standardDraw_of_mutualDefense 组合出和棋。 -/

def draw7x7s4RootPosition : Position := draw7x7s4WhiteDefenseRootPosition

set_option linter.style.nativeDecide false in
theorem draw7x7s4WhiteChecked :
    checkDefenseCertificateAt draw7x7s4RootPosition draw7x7s4WhiteDefenseCertificate = true := by
  native_decide

theorem draw7x7s4WhitePrevents : WhiteCanPreventBlackWin draw7x7s4RootPosition :=
  white_defense_certificate_sound draw7x7s4RootPosition draw7x7s4WhiteDefenseCertificate rfl draw7x7s4WhiteChecked

set_option linter.style.nativeDecide false in
theorem draw7x7s4BlackChecked :
    checkDefenseCertificateAt draw7x7s4RootPosition draw7x7s4BlackDefenseCertificate = true := by
  native_decide

theorem draw7x7s4BlackPrevents : BlackCanPreventWhiteWin draw7x7s4RootPosition :=
  black_defense_certificate_sound draw7x7s4RootPosition draw7x7s4BlackDefenseCertificate rfl draw7x7s4BlackChecked

theorem draw7x7s4StandardDraw : StandardDraw draw7x7s4RootPosition :=
  standardDraw_of_mutualDefense draw7x7s4WhitePrevents draw7x7s4BlackPrevents

end Gomoku.Generated