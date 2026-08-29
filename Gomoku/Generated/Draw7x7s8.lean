import Gomoku.Generated.Draw7x7s8WhiteDefense
import Gomoku.Generated.Draw7x7s8BlackDefense

namespace Gomoku.Generated

/-! 7x7 标准和棋 (seed 8): 21 黑 + 21 白, 轮到黑方, 7 个空格。
每个长度 5 窗口都同时含黑子和白子, 任何一方都无法成五;
两侧防守证书由 C++ DefenseSearcher 独立生成, Lean 检查器验证后
用 standardDraw_of_mutualDefense 组合出和棋。 -/

def draw7x7s8RootPosition : Position := draw7x7s8WhiteDefenseRootPosition

set_option linter.style.nativeDecide false in
theorem draw7x7s8WhiteChecked :
    checkDefenseCertificateAt draw7x7s8RootPosition draw7x7s8WhiteDefenseCertificate = true := by
  native_decide

theorem draw7x7s8WhitePrevents : WhiteCanPreventBlackWin draw7x7s8RootPosition :=
  white_defense_certificate_sound draw7x7s8RootPosition draw7x7s8WhiteDefenseCertificate rfl draw7x7s8WhiteChecked

set_option linter.style.nativeDecide false in
theorem draw7x7s8BlackChecked :
    checkDefenseCertificateAt draw7x7s8RootPosition draw7x7s8BlackDefenseCertificate = true := by
  native_decide

theorem draw7x7s8BlackPrevents : BlackCanPreventWhiteWin draw7x7s8RootPosition :=
  black_defense_certificate_sound draw7x7s8RootPosition draw7x7s8BlackDefenseCertificate rfl draw7x7s8BlackChecked

theorem draw7x7s8StandardDraw : StandardDraw draw7x7s8RootPosition :=
  standardDraw_of_mutualDefense draw7x7s8WhitePrevents draw7x7s8BlackPrevents

end Gomoku.Generated