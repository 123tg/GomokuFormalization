import Gomoku.Generated.Draw7x7s3WhiteDefense
import Gomoku.Generated.Draw7x7s3BlackDefense

namespace Gomoku.Generated

/-! 7x7 标准和棋 (seed 3): 21 黑 + 21 白, 轮到黑方, 7 个空格。
每个长度 5 窗口都同时含黑子和白子, 任何一方都无法成五;
两侧防守证书由 C++ DefenseSearcher 独立生成, Lean 检查器验证后
用 standardDraw_of_mutualDefense 组合出和棋。 -/

def draw7x7s3RootPosition : Position := draw7x7s3WhiteDefenseRootPosition

set_option linter.style.nativeDecide false in
theorem draw7x7s3WhiteChecked :
    checkDefenseCertificateAt draw7x7s3RootPosition draw7x7s3WhiteDefenseCertificate = true := by
  native_decide

theorem draw7x7s3WhitePrevents : WhiteCanPreventBlackWin draw7x7s3RootPosition :=
  white_defense_certificate_sound draw7x7s3RootPosition draw7x7s3WhiteDefenseCertificate rfl draw7x7s3WhiteChecked

set_option linter.style.nativeDecide false in
theorem draw7x7s3BlackChecked :
    checkDefenseCertificateAt draw7x7s3RootPosition draw7x7s3BlackDefenseCertificate = true := by
  native_decide

theorem draw7x7s3BlackPrevents : BlackCanPreventWhiteWin draw7x7s3RootPosition :=
  black_defense_certificate_sound draw7x7s3RootPosition draw7x7s3BlackDefenseCertificate rfl draw7x7s3BlackChecked

theorem draw7x7s3StandardDraw : StandardDraw draw7x7s3RootPosition :=
  standardDraw_of_mutualDefense draw7x7s3WhitePrevents draw7x7s3BlackPrevents

end Gomoku.Generated