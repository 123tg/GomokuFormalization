import Gomoku.Search

/-!
本文件集中进行语义审计：既验证合法局面和证书的正例，也构造覆盖缺失、错误引用、
错误根局面等反例，明确几何形状、可执行搜索结果与可信强制胜证明之间的边界。
-/

namespace Gomoku

/-!
This file contains executable counterexamples and regression checks for the
semantic audit.  These are tests, not theorems used as the trusted proof of
the 15x15 first-player result.  `native_decide` is intentionally confined to
this test-oriented module.
-/

def auditCenter : Coord := (7, 7)
-- 定义审计样例反复使用的棋盘中心坐标。

def occupiedCenter : Position := Position.play initialPosition auditCenter
-- 构造黑方已经在中心落子、轮到白方的局面。

example : occupiedCenter.turn = .white := by
  rfl
-- 检查黑方中心首步后行棋方已切换为白方。

example : ¬ legalMove occupiedCenter auditCenter := by
  native_decide
-- 检查白方不能在已经被黑棋占据的中心重复落子。

/- `play` is deliberately a raw board update.  The legality predicate must
be checked before using it as a game move. -/
example : (play occupiedCenter auditCenter).board.cell auditCenter = .stone .white := by
  rfl
-- 展示原始 `play` 会覆盖棋子，因此游戏语义使用它之前必须另行证明 `legalMove`。

def horizontalThreeWithWhiteEnd : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (5, 7) .black) (6, 7) .black)
      (7, 7) .black)
    (8, 7) .white
-- 构造三颗横向黑棋右端被白棋占据的非法覆盖审计棋盘。

/- This is an intentional audit witness: the raw geometric predicate sees the
resulting pattern even though the move overwrites an occupied cell.  The
semantic wrapper must therefore carry a legality premise. -/
example : straightOpenFour
    (play ⟨horizontalThreeWithWhiteEnd, .black⟩ (8, 7)).board
    .black (5, 7) .horizontal := by
  native_decide
-- 展示若无合法性前提，原始落子覆盖白棋后会让几何谓词观察到并不存在于合法对局中的直四。

example : ¬ legalMove ⟨horizontalThreeWithWhiteEnd, .black⟩ (8, 7) := by
  native_decide
-- 确认上述制造直四的覆盖落子确实非法，从而隔离几何层与规则层。

def horizontalThreeOpenBoard : Board :=
  Board.place
    (Board.place
      (Board.place Board.empty (5, 7) .black) (6, 7) .black)
    (7, 7) .black
-- 构造两端开放的横向连续三子测试棋盘。

def horizontalBrokenThreeBoard : Board :=
  Board.place
    (Board.place
    (Board.place Board.empty (5, 7) .black) (6, 7) .black)
    (8, 7) .black
-- 构造中间 `(7, 7)` 留空的横向断三测试棋盘。

/- Only the two horizontal endpoints and the internal gap are empty; every
   other cell is occupied so the opponent has exactly two legal replies after
   Black fills the broken-three gap. -/
def forcedBrokenThreeBoard : Board :=
  ⟨fun c =>
    if c = (4, 7) ∨ c = (7, 7) ∨ c = (9, 7) then
      .empty
    else if c = (5, 7) ∨ c = (6, 7) ∨ c = (8, 7) then
      .stone .black
    else
      if (c.1.1 + 2 * c.2.1) % 5 < 2 then .stone .black else .stone .white⟩
-- 构造仅三个关键空点的稠密断三局面，使补缺口后对手恰有两个合法应手。

def forcedBrokenThreePosition : Position := ⟨forcedBrokenThreeBoard, .black⟩
-- 将稠密断三棋盘包装为轮到黑方的强制攻击局面。

def horizontalJumpFourBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (5, 7) .black) (6, 7) .black)
      (7, 7) .black)
    (9, 7) .black
-- 构造内部 `(8, 7)` 留空的横向跳四测试棋盘。

def boundaryBrokenThreeBoard : Board :=
  Board.place
    (Board.place
      (Board.place Board.empty (0, 7) .black) (1, 7) .black)
    (3, 7) .black
-- 构造贴左边界的断三，用于验证越界端不能满足开放模式。

def auditFourBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (5, 7) .black) (6, 7) .black)
      (7, 7) .black)
    (8, 7) .black
-- 构造两端开放的横向黑方直四，作为立即胜和证书正例的根棋盘。

example : CanForceWin ⟨auditFourBoard, .black⟩ .black := by
  apply singleOpenFour_forces_win_minimal (s := ⟨auditFourBoard, .black⟩)
  · rfl
  · change ¬ Position.isTerminal ⟨auditFourBoard, .black⟩
    native_decide
  · native_decide
-- 通过单直四战术定理证明黑方从审计直四局面能够强制获胜。

/- A positive multi-layer certificate exercises the complete prover-move path:
   the parent is non-terminal, the move is legal, the child index is strictly
   larger, and the referenced child is exactly the resulting terminal position.
   This is deliberately a local certificate; its root is not the empty board,
   so it is not a claim about the global 15x15 theorem. -/
def twoLayerRoot : Position := ⟨auditFourBoard, .black⟩
-- 将审计直四棋盘设为两节点局部证书的根局面。

def twoLayerMove : Coord := (9, 7)
-- 选择直四右端 `(9, 7)` 作为两节点证书中的黑方立即胜着。

def twoLayerCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[
      .proverMove twoLayerRoot twoLayerMove 1,
      .terminal (play twoLayerRoot twoLayerMove) .blackWin
    ] }
-- 构造“证明方落子—黑胜终局”的两节点紧凑局部证书。

example :
    checkNodeAt .black twoLayerCertificate.nodes 0
      (.proverMove twoLayerRoot twoLayerMove 1) = true := by
  native_decide
-- 单独验证两节点证书的根落子节点满足非终局、轮次、合法性、索引和子局面条件。

example :
    checkNodeAt .black twoLayerCertificate.nodes 1
      (.terminal (play twoLayerRoot twoLayerMove) .blackWin) = true := by
  native_decide
-- 单独验证两节点证书的叶节点确实标记黑胜终局。

theorem twoLayerCertificate_nodes_checked :
    ∀ i (hi : i < twoLayerCertificate.nodes.size),
      checkNodeAt .black twoLayerCertificate.nodes i
        twoLayerCertificate.nodes[i] = true := by
  intro i hi
  have hi' : i = 0 ∨ i = 1 := by
    simp [twoLayerCertificate] at hi ⊢
    omega
  rcases hi' with h0 | h1
  · subst i
    have hcheck :
        checkNodeAt .black twoLayerCertificate.nodes 0
          (.proverMove twoLayerRoot twoLayerMove 1) = true := by
      native_decide
    simpa [twoLayerCertificate] using hcheck
  · subst i
    have hcheck :
        checkNodeAt .black twoLayerCertificate.nodes 1
          (.terminal (play twoLayerRoot twoLayerMove) .blackWin) = true := by
      native_decide
    simpa [twoLayerCertificate] using hcheck
-- 枚举唯二的合法节点索引，证明两节点证书中的每个节点都通过带边检查。

example : Nonempty (CertificateTree .black twoLayerRoot) := by
  exact compact_reify_at twoLayerCertificate .black 0 (by native_decide)
    twoLayerCertificate_nodes_checked
-- 使用通用重构器把已检查的紧凑节点数组还原为依赖类型证书树。

example : CanForceWin twoLayerRoot .black := by
  exact CertificateTree.sound
    (Classical.choice (compact_reify_at twoLayerCertificate .black 0
      (by native_decide) twoLayerCertificate_nodes_checked))
-- 对重构的证书树应用可靠性定理，得到两层根局面的黑方强制胜。

example : CanForceWin twoLayerRoot .black := by
  apply immediateWinCertificate_sound (s := twoLayerRoot) (p := .black)
    (m := twoLayerMove)
  · rfl
  · native_decide
  · native_decide
-- 用专门的立即胜证书定理再次证明同一结论，交叉核对两条证明路径。

/- A local opponent-node certificate exercises the universal-response path.
   The position has exactly two empty points, both endpoints of a black four;
   whichever point White fills, Black wins by filling the other endpoint. -/
def opponentForkBoard : Board :=
  ⟨fun c =>
    if c = (4, 7) ∨ c = (9, 7) then
      .empty
    else if c = (5, 7) ∨ c = (6, 7) ∨ c = (7, 7) ∨ c = (8, 7) then
      .stone .black
    else
      if (c.1.1 + 2 * c.2.1) % 5 < 2 then .stone .black else .stone .white⟩
-- 构造仅有直四两端为空的稠密棋盘，使白方正好有两种应手且黑方随后可补另一端获胜。

def opponentForkPosition : Position := ⟨opponentForkBoard, .white⟩
-- 将两空点棋盘包装为轮到白方的全称应手分叉局面。

def opponentForkCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[
      .opponentMoves opponentForkPosition #[((4, 7), 1), ((9, 7), 2)],
      .proverMove (play opponentForkPosition (4, 7)) (9, 7) 3,
      .proverMove (play opponentForkPosition (9, 7)) (4, 7) 4,
      .terminal (play (play opponentForkPosition (4, 7)) (9, 7)) .blackWin,
      .terminal (play (play opponentForkPosition (9, 7)) (4, 7)) .blackWin
    ] }
-- 手写五节点证书，覆盖白方两个合法应手并为每条分支给出黑方立即胜着。

example : Board.emptyCount opponentForkBoard = 2 := by
  native_decide
-- 计算确认分叉根棋盘恰有两个空点，保证全称应手集合可明确审计。

example : terminal opponentForkPosition = none := by
  native_decide
-- 计算确认白方应手前的分叉根局面尚未终局。

/- The same two-empty-point position is also a direct executable witness for
   the semantic double-threat theorem.  Unlike `WinningMoves`,
   `WinningCells` does not require it to be the target's turn: the set records
   the two cells that Black can win on after White has replied. -/
example : (WinningCells opponentForkPosition .black).card = 2 := by
  native_decide
-- 检查不依赖当前轮次的黑方制胜点集合正好包含两个端点。

example : HasDoubleThreat opponentForkPosition .black := by
  native_decide
-- 由两个不同制胜点计算验证黑方在该局面具有双威胁。

example : ∃ m, m ∈ WinningCells opponentForkPosition .black ∧ m ≠ (4, 7) := by
  apply winningCell_ne_of_hasDoubleThreat
  native_decide
-- 从双威胁定理提取一个不同于指定端点 `(4, 7)` 的黑方制胜点。

example : ¬ HasImmediateWin opponentForkPosition .white := by
  native_decide
-- 检查当前行棋的白方自身没有一步获胜手段。

example : CanForceWin opponentForkPosition .black := by
  apply doubleThreat_forces_win (s := opponentForkPosition) (p := .black)
  · rfl
  · native_decide
  · native_decide
  · native_decide
-- 用双威胁强制胜定理证明：无论白方占哪一端，黑方都可占另一端获胜。

/- A move-level witness: Black fills the centre of a cross-shaped gap.  The
   resulting position has horizontal and vertical four-lines, hence at least
   two immediate winning cells, while the move itself is not yet terminal. -/
def createdDoubleThreatBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place
          (Board.place
            (Board.place Board.empty (5, 7) .black) (6, 7) .black)
          (8, 7) .black)
        (7, 5) .black)
      (7, 6) .black)
    (7, 8) .black
-- 构造横纵两条棋线都缺中心的六子交叉局面，中心落子后会产生两个方向的四线威胁。

def createdDoubleThreatPosition : Position :=
  ⟨createdDoubleThreatBoard, .black⟩
-- 将交叉缺口棋盘包装为轮到黑方的局面。

def createdDoubleThreatMove : Coord := (7, 7)
-- 指定同时连接横纵两条攻击线的中心落子。

example : legalMove createdDoubleThreatPosition createdDoubleThreatMove := by
  native_decide
-- 计算验证中心点在非终局交叉局面上是合法落子。

example : terminal (play createdDoubleThreatPosition createdDoubleThreatMove) = none := by
  native_decide
-- 检查中心落子只建立双威胁，并未立即形成五连终局。

example : ¬ HasImmediateWin
    (play createdDoubleThreatPosition createdDoubleThreatMove) .white := by
  native_decide
-- 检查黑方中心落子后，轮到的白方没有一步获胜反击。

example : HasDoubleThreat
    (play createdDoubleThreatPosition createdDoubleThreatMove) .black := by
  native_decide
-- 计算验证中心落子后的局面具有至少两个不同的黑方制胜点。

example : CanForceWin createdDoubleThreatPosition .black := by
  apply doubleThreat_move_forces_win
    (s := createdDoubleThreatPosition) (p := .black)
    (m := createdDoubleThreatMove)
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
-- 应用“落子制造安全双威胁”定理，证明黑方从交叉缺口根局面强制获胜。

example :
    checkNodeAt .black opponentForkCertificate.nodes 0
      (.opponentMoves opponentForkPosition #[((4, 7), 1), ((9, 7), 2)]) = true := by
  native_decide
-- 验证手写分叉证书的根节点完整覆盖白方两个合法应手。

example :
    checkNodeAt .black opponentForkCertificate.nodes 1
      (.proverMove (play opponentForkPosition (4, 7)) (9, 7) 3) = true := by
  native_decide
-- 验证白方先下 `(4, 7)` 后黑方补 `(9, 7)` 的证明方节点。

example :
    checkNodeAt .black opponentForkCertificate.nodes 2
      (.proverMove (play opponentForkPosition (9, 7)) (4, 7) 4) = true := by
  native_decide
-- 验证白方先下 `(9, 7)` 后黑方补 `(4, 7)` 的证明方节点。

example :
    checkNodeAt .black opponentForkCertificate.nodes 3
      (.terminal (play (play opponentForkPosition (4, 7)) (9, 7)) .blackWin) = true := by
  native_decide
-- 验证第一条白方应手分支的叶局面确实为黑胜。

example :
    checkNodeAt .black opponentForkCertificate.nodes 4
      (.terminal (play (play opponentForkPosition (9, 7)) (4, 7)) .blackWin) = true := by
  native_decide
-- 验证第二条白方应手分支的叶局面确实为黑胜。

theorem opponentForkCertificate_nodes_checked :
    ∀ i (hi : i < opponentForkCertificate.nodes.size),
      checkNodeAt .black opponentForkCertificate.nodes i
        opponentForkCertificate.nodes[i] = true := by
  intro i hi
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
    simp [opponentForkCertificate] at hi ⊢
    omega
  rcases hi' with h0 | h1 | h2 | h3 | h4
  · subst i
    have hcheck :
        checkNodeAt .black opponentForkCertificate.nodes 0
          (.opponentMoves opponentForkPosition #[((4, 7), 1), ((9, 7), 2)]) = true := by
      native_decide
    simpa [opponentForkCertificate] using hcheck
  · subst i
    have hcheck :
        checkNodeAt .black opponentForkCertificate.nodes 1
          (.proverMove (play opponentForkPosition (4, 7)) (9, 7) 3) = true := by
      native_decide
    simpa [opponentForkCertificate] using hcheck
  · subst i
    have hcheck :
        checkNodeAt .black opponentForkCertificate.nodes 2
          (.proverMove (play opponentForkPosition (9, 7)) (4, 7) 4) = true := by
      native_decide
    simpa [opponentForkCertificate] using hcheck
  · subst i
    have hcheck :
        checkNodeAt .black opponentForkCertificate.nodes 3
          (.terminal (play (play opponentForkPosition (4, 7)) (9, 7)) .blackWin) = true := by
      native_decide
    simpa [opponentForkCertificate] using hcheck
  · subst i
    have hcheck :
        checkNodeAt .black opponentForkCertificate.nodes 4
          (.terminal (play (play opponentForkPosition (9, 7)) (4, 7)) .blackWin) = true := by
      native_decide
    simpa [opponentForkCertificate] using hcheck
-- 穷举索引 0 至 4，证明手写分叉证书的全部节点均通过语义与有向边检查。

example : Nonempty (CertificateTree .black opponentForkPosition) := by
  have htree := compact_reify_at opponentForkCertificate .black 0 (by native_decide)
    opponentForkCertificate_nodes_checked
  have hroot : nodePosition opponentForkCertificate.nodes[0] = opponentForkPosition := by
    rfl
  simpa [hroot] using htree
-- 将全部已检查的分叉节点重构为根在 `opponentForkPosition` 的依赖类型证书树。

example : CanForceWin opponentForkPosition .black := by
  have htree := compact_reify_at opponentForkCertificate .black 0 (by native_decide)
    opponentForkCertificate_nodes_checked
  have hroot : nodePosition opponentForkCertificate.nodes[0] = opponentForkPosition := by
    rfl
  exact CertificateTree.sound (Classical.choice (by simpa [hroot] using htree))
-- 对重构的分叉证书树应用可靠性，得到黑方强制胜结论。

/- A certificate may share a child node.  Here the first opponent reply is
   listed twice and both entries reference the same prover subtree.  Duplicate
   reply entries are harmless because coverage is a membership condition; the
   checker still validates the shared node and its position once per edge. -/
def sharedSubtreeCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[
      .opponentMoves opponentForkPosition
        #[((4, 7), 1), ((4, 7), 1), ((9, 7), 2)],
      .proverMove (play opponentForkPosition (4, 7)) (9, 7) 3,
      .proverMove (play opponentForkPosition (9, 7)) (4, 7) 4,
      .terminal (play (play opponentForkPosition (4, 7)) (9, 7)) .blackWin,
      .terminal (play (play opponentForkPosition (9, 7)) (4, 7)) .blackWin
    ] }

example : checkLocalCertificateAt opponentForkPosition
    sharedSubtreeCertificate = true := by
  native_decide

example : CanForceWin opponentForkPosition .black := by
  apply local_certificate_at_sound opponentForkPosition sharedSubtreeCertificate
  native_decide

/- The generic two-ply generator accepts the same response table and feeds it
   through the local checker.  This is the first regression test for the
   reusable search-to-certificate adapter, rather than a hand-written node
   array. -/
def generatedForkCertificate : CompactCertificate :=
  twoPlyImmediateCertificate opponentForkPosition .black
    #[((4, 7), (9, 7)), ((9, 7), (4, 7))]
-- 用通用两层证书生成器从同一“应手—胜着”表自动生成分叉证书。

example : checkLocalCertificate generatedForkCertificate = true := by
  native_decide
-- 计算验证通用生成器产出的分叉证书通过局部检查器。

example : CanForceWin opponentForkPosition .black := by
  exact twoPlyImmediateCertificate_sound
    (s := opponentForkPosition) (p := .black)
    (responses := #[((4, 7), (9, 7)), ((9, 7), (4, 7))]) (by
      native_decide)
-- 直接使用两层证书生成器的可靠性定理，再次推出分叉局面黑方强制胜。

example : (twoPlyCertificateFor opponentForkPosition .black).isSome := by
  native_decide
-- 检查自动枚举全部白方应手的两层搜索确实能产生候选证书。

/- A fixed candidate tree exercises the general tree-to-array compiler without
   making every library build rerun the more expensive depth search. -/
def opponentForkCandidateTree : CandidateTree :=
  .opponentMoves opponentForkPosition [
    ((4, 7), .proverMove (play opponentForkPosition (4, 7)) (9, 7)
      (.terminal (play (play opponentForkPosition (4, 7)) (9, 7)))),
    ((9, 7), .proverMove (play opponentForkPosition (9, 7)) (4, 7)
      (.terminal (play (play opponentForkPosition (9, 7)) (4, 7))))
  ]
-- 用树形结构表达同一全称分叉证明，供通用树到数组编译器测试。

def compiledForkCertificate : CompactCertificate :=
  candidateTreeCertificate .black opponentForkCandidateTree
-- 将固定分叉候选树以前序布局编译为紧凑证书。

example : checkLocalCertificateAt opponentForkPosition compiledForkCertificate = true := by
  native_decide
-- 验证编译后的证书同时通过节点检查和指定根局面匹配检查。

example : CanForceWin opponentForkPosition .black := by
  apply local_certificate_at_sound opponentForkPosition compiledForkCertificate
  native_decide
-- 由编译证书的局部可靠性再次得到分叉根局面的黑方强制胜。

/- After the fast candidate enumeration was introduced, this small recursive
   search is cheap enough to keep as a smoke test.  It still proves nothing by
   itself: `checkedDepthCertificateFor` accepts the result only after the same
   local certificate and root checks used above. -/
example : (checkedDepthCertificateFor 2 opponentForkPosition .black).isSome := by
  native_decide
-- 冒烟检查：通用深度二搜索能找到并通过检查这张分叉证书。

/- The checker must reject an opponent node that omits one legal reply.  The
   root position has exactly two empty points, so listing only one child is a
   genuine coverage failure rather than an alternative strategy encoding. -/
def missingReplyCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[
      .opponentMoves opponentForkPosition #[((4, 7), 1)],
      .proverMove (play opponentForkPosition (4, 7)) (9, 7) 2,
      .terminal (play (play opponentForkPosition (4, 7)) (9, 7)) .blackWin
    ] }
-- 构造故意遗漏白方 `(9, 7)` 应手的错误证书，测试全称分支覆盖检查。

example : checkLocalCertificate missingReplyCertificate = false := by
  native_decide
-- 确认检查器拒绝没有覆盖全部合法对手应手的证书。

/- Out-of-range references and child-position mismatches are rejected even
   when the move labels themselves look plausible. -/
def badReferenceCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[
      .opponentMoves opponentForkPosition #[((4, 7), 99), ((9, 7), 2)],
      .proverMove (play opponentForkPosition (9, 7)) (4, 7) 3,
      .terminal (play (play opponentForkPosition (9, 7)) (4, 7)) .blackWin,
      .terminal (play (play opponentForkPosition (9, 7)) (4, 7)) .blackWin
    ] }
-- 构造含越界子节点引用 99 的错误证书。

example : checkLocalCertificate badReferenceCertificate = false := by
  native_decide
-- 确认检查器拒绝任何指向节点数组之外的边引用。

def badChildPositionCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[
      .opponentMoves opponentForkPosition #[((4, 7), 1), ((9, 7), 2)],
      .proverMove opponentForkPosition (9, 7) 3,
      .proverMove (play opponentForkPosition (9, 7)) (4, 7) 4,
      .terminal (play (play opponentForkPosition (9, 7)) (4, 7)) .blackWin,
      .terminal (play (play opponentForkPosition (9, 7)) (4, 7)) .blackWin
    ] }
-- 构造首个子节点局面未等于执行父边落子结果的错误证书。

example : checkLocalCertificate badChildPositionCertificate = false := by
  native_decide
-- 确认检查器会比较父边落子后的实际局面与被引用子节点局面。

def badTerminalLabelCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[
      .opponentMoves opponentForkPosition #[((4, 7), 1), ((9, 7), 2)],
      .proverMove (play opponentForkPosition (4, 7)) (9, 7) 3,
      .proverMove (play opponentForkPosition (9, 7)) (4, 7) 4,
      .terminal (play (play opponentForkPosition (4, 7)) (9, 7)) .whiteWin,
      .terminal (play (play opponentForkPosition (9, 7)) (4, 7)) .blackWin
    ] }
-- 构造把实际黑胜叶错误标记为白胜的证书。

example : checkLocalCertificate badTerminalLabelCertificate = false := by
  native_decide
-- 确认检查器重新计算终局结果，不信任证书中伪造的胜者标签。

/- A geometric double open three is not, by itself, the same as an
   *immediate* winning move after every defense.  The cross below creates a
   horizontal and a vertical straight open three when Black plays the center.
   White can block one endpoint; Black then has a remaining open-three
   extension, but no one-move five.  This guards the semantic boundary between
   `GeometricDoubleOpenThree` and the deliberately stronger
   `ImmediateSafeDoubleOpenThree`.
 -/
def crossForkBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (6, 7) .black) (8, 7) .black)
      (7, 6) .black)
    (7, 8) .black
-- 构造中心为空、横纵各有两颗分离黑棋的开放三交叉棋盘。

def crossForkPosition : Position := ⟨crossForkBoard, .black⟩
-- 将开放三交叉棋盘包装为轮到黑方的局面。

def crossForkMove : Coord := (7, 7)
-- 指定在中心连接横纵棋线、同时产生两个几何开放三的落子。

def crossForkDefense : Coord := (5, 7)
-- 指定白方封堵横向一端的合法防守，用于否定“一步后必有立即胜”的过强语义。

example : GeometricDoubleOpenThree crossForkPosition .black crossForkMove := by
  native_decide
-- 计算验证中心落子满足纯几何双开放三定义。

/- The cross fork has several distinct one-ply four extensions, even though
   none of them is an immediate five.  This is the intended intermediate
   threat layer between geometric open threes and `WinningCells`. -/
example : HasDoubleFourThreat
    (play crossForkPosition crossForkMove) .black := by
  native_decide
-- 验证中心落子后虽无立即五连，却存在至少两个不同的一步成四扩展点。

example :
    ∃ m, m ∈ FourExtensionCells
      (play crossForkPosition crossForkMove).board .black := by
  exact straightOpenThree_has_fourExtension
    (by native_decide :
      straightOpenThree
        (play crossForkPosition crossForkMove).board .black (6, 7) .horizontal)
-- 从横向直开放三定理提取一个能把该棋形扩展为四威胁的落子。

example : legalMove (play crossForkPosition crossForkMove) crossForkDefense := by
  native_decide
-- 计算确认白方在 `(5, 7)` 的封堵是中心落子后的合法应手。

theorem crossFork_no_immediate_win :
    ¬ HasImmediateWin
      (play (play crossForkPosition crossForkMove) crossForkDefense) .black := by
  intro hwin
  have hcard :
      (WinningMoves
        (play (play crossForkPosition crossForkMove) crossForkDefense) .black).card = 0 := by
    native_decide
  have hpos : 0 <
      (WinningMoves
        (play (play crossForkPosition crossForkMove) crossForkDefense) .black).card :=
    Finset.card_pos.mpr hwin
  omega
-- 通过制胜步集合基数为零，证明白方上述防守后黑方没有一步立即胜着。

example : ¬ ImmediateSafeDoubleOpenThree crossForkPosition .black crossForkMove := by
  intro hsafe
  have hafter := hsafe.2.2.2 crossForkDefense (by native_decide)
  exact crossFork_no_immediate_win hafter
-- 用具体防守反例否定该几何双开放三满足更强的“每个应手后都有立即胜”条件。

/- A geometric double open three can coexist with an opponent's immediate
   win.  The white four is deliberately placed away from the black cross, so
   the example isolates the semantic condition rather than relying on an
   accidental overlap. -/
def crossWithWhiteFourBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place
          (Board.place
            (Board.place
              (Board.place
                (Board.place Board.empty (6, 7) .black) (8, 7) .black)
              (7, 6) .black)
            (7, 8) .black)
          (3, 3) .white)
        (4, 3) .white)
      (5, 3) .white)
    (6, 3) .white
-- 在黑方开放三交叉之外另放一条白方直四，构造对手已有立即胜着的危险局面。

def crossWithWhiteFourPosition : Position :=
  ⟨crossWithWhiteFourBoard, .black⟩
-- 将带白方直四的交叉棋盘包装为轮到黑方的局面。

def crossWithWhiteFourMove : Coord := (7, 7)
-- 指定仍可在几何上形成黑方双开放三的中心落子。

example : GeometricDoubleOpenThree
    crossWithWhiteFourPosition .black crossWithWhiteFourMove := by
  native_decide
-- 检查即使白方另有直四，黑方中心落子仍满足纯几何双开放三。

example : DoubleOpenThree
    crossWithWhiteFourPosition .black crossWithWhiteFourMove := by
  native_decide
-- 检查中心落子也满足带轮次与合法性包装的 `DoubleOpenThree`。

example : OpponentHasImmediateWin
    (play crossWithWhiteFourPosition crossWithWhiteFourMove) .black := by
  native_decide
-- 计算确认黑方中心落子后白方仍保有一步获胜点。

example : ¬ SafeDoubleOpenThree
    crossWithWhiteFourPosition .black crossWithWhiteFourMove := by
  apply not_safeDoubleOpenThree_of_opponentImmediate
  native_decide
-- 由对手存在立即胜着否定该落子满足语义安全的双开放三条件。

example : ¬ ImmediateSafeDoubleOpenThree
    crossWithWhiteFourPosition .black crossWithWhiteFourMove := by
  apply not_immediateSafeDoubleOpenThree_of_opponentImmediate
  native_decide
-- 同样否定更强的立即安全双开放三条件。

/- A four-extension threat is not an immediate winning cell: after the cross
   move, the immediate winning-cell set is empty, while the four-threat set
   has at least two elements. -/
example : (WinningMoves
    (play crossForkPosition crossForkMove) .black).card = 0 := by
  native_decide
-- 计算确认普通交叉中心落子后的黑方立即制胜步集合为空，区分四威胁与立即五连。

/- The overlap relation is executable, and the corresponding uniqueness
   theorem rejects a second start inside the same straight run. -/
example : StartShiftConflict 3 (5, 7) (6, 7) .horizontal := by
  native_decide
-- 检查长度三、同方向且起点相邻的两个窗口发生起点平移冲突。

example :
    ¬ (straightOpenThree horizontalThreeOpenBoard .black (5, 7) .horizontal ∧
      straightOpenThree horizontalThreeOpenBoard .black (6, 7) .horizontal) := by
  intro h
  exact straightOpenThree_not_startShiftConflict h.1 h.2 (by native_decide)
-- 应用唯一性定理否定同一条三子直线能以两个冲突起点重复计为开放三。

example : StartShiftConflict 4 (5, 7) (6, 7) .horizontal := by
  native_decide
-- 检查长度四的相邻同向窗口同样发生起点平移冲突。

example :
    ¬ (straightOpenFour auditFourBoard .black (5, 7) .horizontal ∧
      straightOpenFour auditFourBoard .black (6, 7) .horizontal) := by
  intro h
  exact straightOpenFour_not_startShiftConflict h.1 h.2 (by native_decide)
-- 应用直四唯一性定理排除同一连续四子被相邻起点重复计数。

example : MoveCreatesSingleOpenFour
    ⟨horizontalThreeOpenBoard, .black⟩ .black (8, 7) := by
  native_decide
-- 计算验证在合法开放三右端落子会恰好创建一条直开放四。

example : ¬ MoveCreatesSingleOpenFour
    ⟨horizontalThreeWithWhiteEnd, .black⟩ .black (8, 7) := by
  native_decide
-- 确认覆盖白棋的非法几何更新不满足带合法性约束的“创建单开放四”。

example : (openFourWitnesses
    (play ⟨horizontalThreeOpenBoard, .black⟩ (8, 7)).board .black).card = 1 := by
  native_decide
-- 计算验证合法扩展后的开放四见证集合恰有一个元素。

example : (openThreeWitnesses horizontalThreeOpenBoard .black).card = 1 := by
  native_decide
-- 计算验证横向开放三不会因起点平移被重复计数。

example : brokenOpenThree horizontalBrokenThreeBoard .black (5, 7) .horizontal := by
  native_decide
-- 计算验证带一个内部空缺的三颗黑棋满足断三几何谓词。

example : ¬ straightOpenThree horizontalBrokenThreeBoard .black (5, 7) .horizontal := by
  native_decide
-- 确认同一断三棋盘不满足连续直开放三谓词。

example : ∃ m, m ∈ FourExtensionCells horizontalBrokenThreeBoard .black := by
  exact brokenOpenThree_has_fourExtension
    (c := (5, 7)) (d := .horizontal) (by native_decide)
-- 由断三定理得到至少一个能把棋形扩展成四威胁的空点。

example : straightOpenFour
    (horizontalBrokenThreeBoard.place (7, 7) .black)
    .black (5, 7) .horizontal := by
  native_decide
-- 计算验证在断三内部缺口 `(7, 7)` 补子后形成直开放四。

example : (7, 7) ∈ OpenFourExtensionCells
    horizontalBrokenThreeBoard .black (5, 7) .horizontal := by
  native_decide
-- 检查内部缺口属于该具体断三棋线的开放四扩展点集合。

example : ∃ w, w ∈ WinningCells
    ⟨horizontalBrokenThreeBoard.place (7, 7) .black, .white⟩ .black := by
  exact openFourExtension_has_winningCell
    (c := (5, 7)) (d := .horizontal) (m := (7, 7)) (by native_decide)
-- 从开放四扩展定理推出补缺口后的局面至少存在一个黑方制胜点。

example : BrokenOpenThreeMove
    ⟨horizontalBrokenThreeBoard, .black⟩ .black (7, 7) := by
  native_decide
-- 计算验证在断三缺口落子满足包含轮次、合法性与几何结果的落子级谓词。

example : Board.emptyCount forcedBrokenThreeBoard = 3 := by
  native_decide
-- 确认稠密强制断三棋盘只有左端、内部缺口和右端三个空点。

example : terminal forcedBrokenThreePosition = none := by
  native_decide
-- 确认强制断三根局面尚未出现终局结果。

example : brokenOpenThree forcedBrokenThreeBoard .black (5, 7) .horizontal := by
  native_decide
-- 计算验证稠密填充没有破坏关键横向断三棋形。

example : GeometricBrokenOpenThree forcedBrokenThreePosition .black (7, 7) := by
  native_decide
-- 检查在内部缺口落子会从几何上把断三扩展为开放四。

example : terminal (play forcedBrokenThreePosition (7, 7)) = none := by
  native_decide
-- 确认补断三缺口后仍未立即终局，强制性来自后续分支而非当步五连。

example : ¬ OpponentHasImmediateWin
    (play forcedBrokenThreePosition (7, 7)) .black := by
  native_decide
-- 确认黑方补缺口后白方没有一步获胜反击。

example : ImmediateSafeBrokenOpenThree
    forcedBrokenThreePosition .black (7, 7) := by
  native_decide
-- 综合验证补缺口落子安全，且白方每个合法应手后黑方都有立即胜着。

example : CanForceWin forcedBrokenThreePosition .black := by
  exact immediateSafeBrokenOpenThree_forces_win
    (m := (7, 7)) (by native_decide)
-- 由立即安全断三定理推出黑方从稠密强制断三根局面能够强制获胜。

example : ∃ w, w ∈ WinningCells
    (play ⟨horizontalBrokenThreeBoard, .black⟩ (7, 7)) .black := by
  exact brokenOpenThreeMove_creates_winningCell (by native_decide)
-- 从一般断三落子定理推出补缺口后的局面至少产生一个黑方制胜点。

example : ¬ hasAtLeastFive
    (horizontalBrokenThreeBoard.place (7, 7) .black) .black := by
  native_decide
-- 确认补断三缺口只形成开放四而非已经完成五连。

example : jumpFour horizontalJumpFourBoard .black (5, 7) .horizontal := by
  native_decide
-- 计算验证四颗带单个内部空缺的黑棋满足跳四模式。

example : ¬ straightOpenFour horizontalJumpFourBoard .black (5, 7) .horizontal := by
  native_decide
-- 确认跳四因内部有空缺而不属于连续直开放四。

example : CanForceWin ⟨horizontalJumpFourBoard, .black⟩ .black := by
  rcases jumpFour_black_immediate
      (s := ⟨horizontalJumpFourBoard, .black⟩) (c := (5, 7)) (d := .horizontal)
      rfl (by
        change ¬ Position.isTerminal ⟨horizontalJumpFourBoard, .black⟩
        native_decide) (by native_decide) with ⟨m, hm, hwin⟩
  exact canForceWin_immediate hm hwin rfl
-- 用跳四补缺口定理提取立即胜着，并提升为黑方强制胜证明。

example : ¬ brokenOpenThree boundaryBrokenThreeBoard .black (0, 7) .horizontal := by
  native_decide
-- 检查贴边断三因左侧不存在开放端而不满足断三定义。

def boundaryThreeBoard : Board :=
  Board.place
    (Board.place
      (Board.place Board.empty (0, 7) .black) (1, 7) .black)
    (2, 7) .black
-- 构造从左边界开始的连续三颗黑棋。

example : ¬ straightOpenThree boundaryThreeBoard .black (0, 7) .horizontal := by
  native_decide
-- 确认边界连续三子只有右端开放，因此不是两端开放的直三。

example : MaximalRun boundaryThreeBoard .black (0, 7) .horizontal 3 := by
  native_decide
-- 验证尽管不是开放三，它仍是从边界开始、长度恰为三的极大连续段。

example : MaximalRun horizontalThreeOpenBoard .black (5, 7) .horizontal 3 := by
  exact straightOpenThree_maximalRun (by native_decide)
-- 从直开放三性质推出其三子核心构成长度三的极大连续段。

example : MaximalRun auditFourBoard .black (5, 7) .horizontal 4 := by
  exact straightOpenFour_maximalRun (by native_decide)
-- 从直开放四性质推出其四子核心构成长度四的极大连续段。

example :
    (MaximalRun horizontalThreeOpenBoard .black (5, 7) .horizontal 3 ∧
      MaximalRun horizontalThreeOpenBoard .black (5, 7) .horizontal 3) →
      ((5, 7) : Coord) = ((5, 7) : Coord) := by
  intro h
  exact maximalRun_unique_of_comparable h.1 h.2 (by left; rfl)
-- 在自反可比的简单情形实例化极大连续段起点唯一性定理。

def verticalFourBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (7, 3) .black) (7, 4) .black)
      (7, 5) .black)
    (7, 6) .black
-- 构造纵向连续四颗黑棋的方向测试棋盘。

def diagonalDownFourBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (3, 6) .black) (4, 5) .black)
      (5, 4) .black)
    (6, 3) .black
-- 构造下降对角线方向连续四颗黑棋的方向测试棋盘。

example : straightOpenFour verticalFourBoard .black (7, 3) .vertical := by
  native_decide
-- 计算验证开放四检测适用于纵向棋线。

example : straightOpenFour diagonalDownFourBoard .black (3, 6) .diagonalDown := by
  native_decide
-- 计算验证开放四检测适用于下降对角线棋线。

def auditOverlineBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place
          (Board.place Board.empty (4, 7) .black) (5, 7) .black)
        (6, 7) .black)
      (7, 7) .black)
    (8, 7) .black
-- 构造恰好五颗连续黑棋的终局审计棋盘。

example : hasAtLeastFive auditOverlineBoard .black := by
  native_decide
-- 计算验证审计终局棋盘满足黑方至少五连。

example : (openFourWitnesses auditOverlineBoard .black).card = 0 := by
  native_decide
-- 确认已形成五连的棋盘不会被误计为仍有一条两端开放的直四。

example : ¬ legalMove ⟨auditOverlineBoard, .white⟩ auditCenter := by
  native_decide
-- 检查黑方已经五连后白方不能继续落子。

/- A malformed compact certificate with no nodes must be rejected. -/
example : checkCertificate { target := .black, root := 0, nodes := #[] } = false := by
  rfl
-- 确认没有任何节点的全局紧凑证书因根索引越界而被拒绝。

/- The checker is target-specific: a white target is not an initial black-win
certificate, even before any node-level reasoning is attempted. -/
example : checkCertificate { target := .white, root := 0, nodes := #[] } = false := by
  rfl
-- 确认全局检查器不会接受目标为白方的所谓初始黑胜证书。

def cycleCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[.proverMove initialPosition auditCenter 0] }
-- 构造根节点反向引用自身的循环证书，测试严格前向边约束。

example : checkCertificate cycleCertificate = false := by
  native_decide
-- 确认全局检查器拒绝自引用循环，从而保证重构递归良基。

def wrongRootCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[.terminal ⟨auditOverlineBoard, .white⟩ .blackWin] }
-- 构造节点语义有效但根局面不是空棋盘初始位置的全局证书。

example : checkCertificate wrongRootCertificate = false := by
  native_decide
-- 确认全局检查器除节点正确性外还强制根局面等于 `initialPosition`。

example : CanForceWin ⟨auditOverlineBoard, .white⟩ .black := by
  apply CertificateTree.sound
  apply checkNode_terminal_reify (target := .black) (size := 1)
    (s := ⟨auditOverlineBoard, .white⟩) (out := .blackWin)
  native_decide
-- 单独重构有效终局节点，说明错误根证书被拒绝不等于其局部黑胜事实为假。

/- A compact one-node terminal certificate is accepted by the same checker
   used for larger DAG certificates, and its soundness is proved through the
   reifier rather than by a test-only shortcut. -/
def oneNodeTerminalCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[.terminal ⟨auditOverlineBoard, .white⟩ .blackWin] }
-- 构造根在审计终局的单节点局部证书，与全局初始根要求形成对照。

example : checkCertificate oneNodeTerminalCertificate = false := by
  native_decide
-- 确认单节点局部证书虽然节点有效，作为全局初始局面证书仍因根不匹配而失败。

example : Nonempty (CertificateTree .black ⟨auditOverlineBoard, .white⟩) := by
  apply compact_reify_at oneNodeTerminalCertificate .black 0 (by native_decide)
  intro i hi
  have hi0 : i = 0 := by
    simpa [oneNodeTerminalCertificate] using hi
  subst i
  have hcheck :
      checkNodeAt .black oneNodeTerminalCertificate.nodes 0
        (.terminal ⟨auditOverlineBoard, .white⟩ .blackWin) = true := by
    native_decide
  simpa [oneNodeTerminalCertificate] using hcheck
-- 通过逐节点检查和重构器证明同一单节点证书在其真实局部根上可形成证书树。

example : samePosition initialPosition initialPosition = true := by
  exact samePosition_self _
-- 检查局面可执行相等测试对自身返回真。

example : samePosition initialPosition occupiedCenter = false := by
  native_decide
-- 检查初始局面与中心落子后的局面被可执行比较正确地区分。

def oneMoveReference : Array (Coord × Nat) := #[(auditCenter, 1)]
-- 构造只含“中心落子指向节点 1”的最小应手引用数组。

example : moveInBool oneMoveReference auditCenter = true := by
  native_decide
-- 计算验证布尔成员检查能在引用数组中找到中心落子。

end Gomoku
