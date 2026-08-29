import Gomoku.Generated.Draw7x7s9WhiteDefense
import Gomoku.Generated.Draw7x7s9BlackDefense

namespace Gomoku.Generated

/-! 7x7 标准和棋 (seed 9): 21 黑 + 21 白, 轮到黑方, 7 个空格。
每个长度 5 窗口都同时含黑子和白子, 任何一方都无法成五;
两侧防守证书由 C++ DefenseSearcher 独立生成, Lean 检查器验证后
用 standardDraw_of_mutualDefense 组合出和棋。 -/

def draw7x7s9RootPosition : Position := draw7x7s9WhiteDefenseRootPosition

set_option linter.style.nativeDecide false in
theorem draw7x7s9WhiteChecked :
    checkDefenseCertificateAt draw7x7s9RootPosition draw7x7s9WhiteDefenseCertificate = true := by
  native_decide

theorem draw7x7s9WhitePrevents : WhiteCanPreventBlackWin draw7x7s9RootPosition :=
  white_defense_certificate_sound draw7x7s9RootPosition draw7x7s9WhiteDefenseCertificate rfl draw7x7s9WhiteChecked

set_option linter.style.nativeDecide false in
theorem draw7x7s9BlackChecked :
    checkDefenseCertificateAt draw7x7s9RootPosition draw7x7s9BlackDefenseCertificate = true := by
  native_decide

theorem draw7x7s9BlackPrevents : BlackCanPreventWhiteWin draw7x7s9RootPosition :=
  black_defense_certificate_sound draw7x7s9RootPosition draw7x7s9BlackDefenseCertificate rfl draw7x7s9BlackChecked

theorem draw7x7s9StandardDraw : StandardDraw draw7x7s9RootPosition :=
  standardDraw_of_mutualDefense draw7x7s9WhitePrevents draw7x7s9BlackPrevents

end Gomoku.Generated