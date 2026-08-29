import Gomoku.Defense

/-!
防御证书审计：对 `checkDefenseCertificateAt` 做恶意证书负测试与小型正测试。

负测试覆盖：缺失攻击方应手、重复应手、非法应手、错误终局标签、输局终局
（defender=White 却以 BlackWin 闭合）、越界子引用、回边/自环、子局面不匹配、
错误轮次。正测试覆盖：终局和棋闭合、防守方一步获胜闭合、攻击方两应手全覆盖，
并通过 soundness theorem 把检查结果提升为真正的数学命题。

注意：本文件中的 `native_decide` 只用于对已经证明可靠的 Bool 检查器做具体计算；
soundness theorem 本身（`Defense.lean` 中的 `defense_certificate_sound` 等）
是真正的定理，不依赖任何外部搜索器结果。
-/

namespace Gomoku

set_option linter.style.nativeDecide false

private def boardWithStones (p : Player) (stones : List Coord) : Board :=
  stones.foldl (fun b c => b.place c p) Board.empty

/-
无五连满盘：黑棋当且仅当 (x + 2y) mod 4 ∈ {0, 1}，任何方向最长连续 4 子。
-/
private def noFiveFill : Board :=
  ⟨fun c =>
    if (c.1.1 + 2 * c.2.1) % 4 == 0 || (c.1.1 + 2 * c.2.1) % 4 == 1 then
      .stone .black
    else .stone .white⟩

example : noFiveFill.full := by native_decide
example : ¬ hasAtLeastFive noFiveFill .black := by native_decide
example : ¬ hasAtLeastFive noFiveFill .white := by native_decide
example : terminal ⟨noFiveFill, .white⟩ = some .draw := by native_decide

/- 白方四连 (1,3)-(4,3)，(0,3)、(5,3) 为空；fourPlayer 指定四连的归属。 -/
private def carvedBoard (fourPlayer : Player) : Board :=
  ⟨fun c =>
    if (c.1.1 == 0 && c.2.1 == 3) || (c.1.1 == 5 && c.2.1 == 3) then .empty
    else if c.2.1 == 3 && (c.1.1 == 1 || c.1.1 == 2 || c.1.1 == 3 || c.1.1 == 4) then
      .stone fourPlayer
    else if (c.1.1 + 2 * c.2.1) % 4 == 0 || (c.1.1 + 2 * c.2.1) % 4 == 1 then
      .stone .black
    else .stone .white⟩

private def whiteFourGap : Position := ⟨carvedBoard .white, .white⟩
private def blackTwoGap : Position := ⟨carvedBoard .white, .black⟩
private def blackFourGap : Position := ⟨carvedBoard .black, .black⟩

example : terminal whiteFourGap = none := by native_decide
example : terminal blackTwoGap = none := by native_decide
example : terminal blackFourGap = none := by native_decide
example : terminal (play whiteFourGap (0, 3)) = some .whiteWin := by native_decide
example : terminal (play (play blackTwoGap (0, 3)) (5, 3)) = some .whiteWin := by
  native_decide

private def blackWinRoot : Position :=
  ⟨boardWithStones .black [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0)], .white⟩

example : terminal blackWinRoot = some .blackWin := by native_decide

/-! ## 正测试：完整证书必须通过 -/

/- 终局和棋：单个终局节点闭合，defender = White。 -/
private def drawCertificate : DefenseCertificate :=
  { defender := .white
    root := 0
    nodes := #[.terminal ⟨noFiveFill, .white⟩ .draw] }

example : checkDefenseCertificateAt ⟨noFiveFill, .white⟩ drawCertificate = true := by
  native_decide

example : WhiteCanPreventBlackWin ⟨noFiveFill, .white⟩ :=
  white_defense_certificate_sound ⟨noFiveFill, .white⟩ drawCertificate rfl
    (by native_decide)

/- 终局和棋：同一个满盘局面下 defender = Black 同样闭合。 -/
private def blackDrawCertificate : DefenseCertificate :=
  { defender := .black
    root := 0
    nodes := #[.terminal ⟨noFiveFill, .white⟩ .draw] }

example : checkDefenseCertificateAt ⟨noFiveFill, .white⟩ blackDrawCertificate = true := by
  native_decide

example : BlackCanPreventWhiteWin ⟨noFiveFill, .white⟩ :=
  black_defense_certificate_sound ⟨noFiveFill, .white⟩ blackDrawCertificate rfl
    (by native_decide)

/- 互守组合：同一满盘和棋局面推出 StandardDraw（真实 theorem，非计算假设）。 -/
example : StandardDraw ⟨noFiveFill, .white⟩ :=
  standardDraw_of_mutualDefense
    (white_defense_certificate_sound ⟨noFiveFill, .white⟩ drawCertificate rfl
      (by native_decide))
    (black_defense_certificate_sound ⟨noFiveFill, .white⟩ blackDrawCertificate rfl
      (by native_decide))

/- 防守方一步获胜：白棋回合在 (0,3) 落子即白胜。 -/
private def whiteFourCertificate : DefenseCertificate :=
  { defender := .white
    root := 0
    nodes := #[
      .defenderMove whiteFourGap (0, 3) 1,
      .terminal (play whiteFourGap (0, 3)) .whiteWin ] }

example : checkDefenseCertificateAt whiteFourGap whiteFourCertificate = true := by
  native_decide

example : WhiteCanPreventBlackWin whiteFourGap :=
  white_defense_certificate_sound whiteFourGap whiteFourCertificate rfl
    (by native_decide)

/- 攻击方两应手全覆盖：黑棋无论走 (0,3) 还是 (5,3)，白棋都在另一端成五。 -/
private def twoReplyCertificate : DefenseCertificate :=
  { defender := .white
    root := 0
    nodes := #[
      .attackerMoves blackTwoGap #[((0, 3), 1), ((5, 3), 3)],
      .defenderMove (play blackTwoGap (0, 3)) (5, 3) 2,
      .terminal (play (play blackTwoGap (0, 3)) (5, 3)) .whiteWin,
      .defenderMove (play blackTwoGap (5, 3)) (0, 3) 4,
      .terminal (play (play blackTwoGap (5, 3)) (0, 3)) .whiteWin ] }

example : checkDefenseCertificateAt blackTwoGap twoReplyCertificate = true := by
  native_decide

example : WhiteCanPreventBlackWin blackTwoGap :=
  white_defense_certificate_sound blackTwoGap twoReplyCertificate rfl
    (by native_decide)

/- defender = Black 的终局黑胜闭合。 -/
private def blackWinCertificate : DefenseCertificate :=
  { defender := .black
    root := 0
    nodes := #[.terminal blackWinRoot .blackWin] }

example : checkDefenseCertificateAt blackWinRoot blackWinCertificate = true := by
  native_decide

example : BlackCanPreventWhiteWin blackWinRoot :=
  black_defense_certificate_sound blackWinRoot blackWinCertificate rfl
    (by native_decide)

/-! ## 负测试：恶意证书必须被拒绝 -/

/- 缺失应手：攻击方节点只列出 (0,3)，漏掉合法应手 (5,3)。 -/
private def missingReplyCertificate : DefenseCertificate :=
  { defender := .white
    root := 0
    nodes := #[
      .attackerMoves blackTwoGap #[((0, 3), 1)],
      .defenderMove (play blackTwoGap (0, 3)) (5, 3) 2,
      .terminal (play (play blackTwoGap (0, 3)) (5, 3)) .whiteWin,
      .defenderMove (play blackTwoGap (5, 3)) (0, 3) 4,
      .terminal (play (play blackTwoGap (5, 3)) (0, 3)) .whiteWin ] }

example : checkDefenseCertificateAt blackTwoGap missingReplyCertificate = false := by
  native_decide

/- 重复应手：攻击方节点把 (0, 3) 列出两次（覆盖仍然完整）。 -/
private def duplicateReplyCertificate : DefenseCertificate :=
  { defender := .white
    root := 0
    nodes := #[
      .attackerMoves blackTwoGap #[((0, 3), 1), ((5, 3), 3), ((0, 3), 1)],
      .defenderMove (play blackTwoGap (0, 3)) (5, 3) 2,
      .terminal (play (play blackTwoGap (0, 3)) (5, 3)) .whiteWin,
      .defenderMove (play blackTwoGap (5, 3)) (0, 3) 4,
      .terminal (play (play blackTwoGap (5, 3)) (0, 3)) .whiteWin ] }

example : checkDefenseCertificateAt blackTwoGap duplicateReplyCertificate = false := by
  native_decide

/- 非法应手：攻击方节点把已被白棋占据的 (1, 3) 列为应手。 -/
private def illegalReplyCertificate : DefenseCertificate :=
  { defender := .white
    root := 0
    nodes := #[
      .attackerMoves blackTwoGap #[((0, 3), 1), ((1, 3), 3), ((5, 3), 3)],
      .defenderMove (play blackTwoGap (0, 3)) (5, 3) 2,
      .terminal (play (play blackTwoGap (0, 3)) (5, 3)) .whiteWin,
      .defenderMove (play blackTwoGap (5, 3)) (0, 3) 4,
      .terminal (play (play blackTwoGap (5, 3)) (0, 3)) .whiteWin ] }

example : checkDefenseCertificateAt blackTwoGap illegalReplyCertificate = false := by
  native_decide

/- 错误终局：非终局局面写成终局标签。 -/
private def wrongTerminalCertificate : DefenseCertificate :=
  { defender := .white
    root := 0
    nodes := #[.terminal blackTwoGap .draw] }

example : checkDefenseCertificateAt blackTwoGap wrongTerminalCertificate = false := by
  native_decide

/- 输局终局：defender = White 却以 BlackWin 闭合。 -/
private def losingTerminalCertificate : DefenseCertificate :=
  { defender := .white
    root := 0
    nodes := #[.terminal blackWinRoot .blackWin] }

example : checkDefenseCertificateAt blackWinRoot losingTerminalCertificate = false := by
  native_decide

/- 非法防守方着法：defenderMove 落在已被占据的格 (1, 3)。 -/
private def illegalDefenderMoveCertificate : DefenseCertificate :=
  { defender := .white
    root := 0
    nodes := #[
      .defenderMove whiteFourGap (1, 3) 1,
      .terminal (play whiteFourGap (0, 3)) .whiteWin ] }

example : checkDefenseCertificateAt whiteFourGap illegalDefenderMoveCertificate = false := by
  native_decide

/- 越界子引用：child = 5 超出两节点数组。 -/
private def invalidChildCertificate : DefenseCertificate :=
  { defender := .white
    root := 0
    nodes := #[
      .defenderMove whiteFourGap (0, 3) 5,
      .terminal (play whiteFourGap (0, 3)) .whiteWin ] }

example : checkDefenseCertificateAt whiteFourGap invalidChildCertificate = false := by
  native_decide

/- 回边/自环：child = parent。 -/
private def backEdgeCertificate : DefenseCertificate :=
  { defender := .white
    root := 0
    nodes := #[
      .defenderMove whiteFourGap (0, 3) 0,
      .terminal (play whiteFourGap (0, 3)) .whiteWin ] }

example : checkDefenseCertificateAt whiteFourGap backEdgeCertificate = false := by
  native_decide

/- 子局面不匹配：child 记录的局面不是 play parent move。 -/
private def wrongChildPositionCertificate : DefenseCertificate :=
  { defender := .white
    root := 0
    nodes := #[
      .defenderMove whiteFourGap (0, 3) 1,
      .terminal whiteFourGap .draw ] }

example : checkDefenseCertificateAt whiteFourGap wrongChildPositionCertificate = false := by
  native_decide

/- 错误轮次 1：defenderMove 节点轮到攻击方（黑棋）。 -/
private def wrongTurnDefenderMoveCertificate : DefenseCertificate :=
  { defender := .white
    root := 0
    nodes := #[
      .defenderMove blackTwoGap (0, 3) 1,
      .terminal (play blackTwoGap (0, 3)) .whiteWin ] }

example : checkDefenseCertificateAt blackTwoGap wrongTurnDefenderMoveCertificate = false := by
  native_decide

/- 错误轮次 2：attackerMoves 节点轮到防守方（白棋）。 -/
private def wrongTurnAttackerMovesCertificate : DefenseCertificate :=
  { defender := .white
    root := 0
    nodes := #[
      .attackerMoves whiteFourGap #[((0, 3), 1)],
      .terminal (play whiteFourGap (0, 3)) .whiteWin ] }

example : checkDefenseCertificateAt whiteFourGap wrongTurnAttackerMovesCertificate = false := by
  native_decide

/- 根引用越界：root 指向不存在的节点。 -/
private def badRootCertificate : DefenseCertificate :=
  { defender := .white
    root := 1
    nodes := #[.terminal ⟨noFiveFill, .white⟩ .draw] }

example : checkDefenseCertificateAt ⟨noFiveFill, .white⟩ badRootCertificate = false := by
  native_decide

/- 根局面不匹配：证书根局面不是调用方指定的局面。 -/
private def wrongRootCertificate : DefenseCertificate :=
  { defender := .white
    root := 0
    nodes := #[.terminal ⟨noFiveFill, .white⟩ .draw] }

example : checkDefenseCertificateAt blackTwoGap wrongRootCertificate = false := by
  native_decide

end Gomoku
