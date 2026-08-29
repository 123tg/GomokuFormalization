import Gomoku.Generated.Draw7x7WhiteDefense
import Gomoku.Generated.Draw7x7BlackDefense

namespace Gomoku.Generated

/-! 7×7 标准和棋: 一个可达的 42 子局面（21 黑 + 21 白, 轮到黑方, 7 个空格）。
该局面中每个长度 5 窗口都同时含黑子和白子, 因此任何一方都无法成五;
两侧的防御证书（白防黑、黑防白）由 C++ DefenseSearcher 独立生成,
此处仅用 Lean 检查器验证并用 standardDraw_of_mutualDefense 组合出和棋。 -/

def draw7x7RootPosition : Position := draw7x7WhiteDefenseRootPosition

set_option linter.style.nativeDecide false in
theorem draw7x7WhiteChecked :
    checkDefenseCertificateAt draw7x7RootPosition draw7x7WhiteDefenseCertificate = true := by
  native_decide

theorem draw7x7WhitePrevents : WhiteCanPreventBlackWin draw7x7RootPosition :=
  white_defense_certificate_sound draw7x7RootPosition draw7x7WhiteDefenseCertificate rfl draw7x7WhiteChecked

set_option linter.style.nativeDecide false in
theorem draw7x7BlackChecked :
    checkDefenseCertificateAt draw7x7RootPosition draw7x7BlackDefenseCertificate = true := by
  native_decide

theorem draw7x7BlackPrevents : BlackCanPreventWhiteWin draw7x7RootPosition :=
  black_defense_certificate_sound draw7x7RootPosition draw7x7BlackDefenseCertificate rfl draw7x7BlackChecked

theorem draw7x7StandardDraw : StandardDraw draw7x7RootPosition :=
  standardDraw_of_mutualDefense draw7x7WhitePrevents draw7x7BlackPrevents

end Gomoku.Generated
