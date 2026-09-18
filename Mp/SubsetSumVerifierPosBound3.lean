import Mp.SubsetSumVerifierPosBound2
import Mp.SubsetSumVerifierReverse3
import Mp.SubsetSumVerifierReverse9

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.constructorNameAsVariable false
set_option linter.unusedVariables false
set_option linter.style.nativeDecide false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.style.multiGoal false
set_option linter.style.whitespace false

namespace Mp

-- ============================================================================
-- q10 ①线 A-2 模块化实现(2026-09-09 用户裁决方案 2):
--   L3''(encS++gS 输入上接受路径中间 cfg 头 < |wS|)=
--     格式段(现成任意 input 件:backchain_to_first4/prefix_states 系)+ 三链域(新写)。
--   核心事实(用户教导 + 逐态核对):主循环活动被 encS 结构约束在 #₁(含)左侧:
--     21 清完读 #₁ → 22、13 读 #₁ → 84 L、87 停 #₀'(51 置,< #₁)、
--     81 遇 consumed 即变 13(扫程止于处理中元素 consumed 边界,到不了 #₁)、
--     格式段(0/1/2/3/24/26/27/29/38/28)扫 encS 到 #₀/#₁ 停。
--   gS 区不被读 → 头 ≤ |encS|-1 < |wS|。
-- ============================================================================

-- ============================================================================
-- 模块 1:布局 —— wS = encS ++ gS 的 encS 前缀内容(位置/kind)
-- ============================================================================

/-- wS 的 encS 前缀在位置 j(< |encS|)的取值 = encS 的。 -/
lemma a2p_getD_prefix_left {a b : List Sym} {j : ℕ} (hj : j < a.length) :
    (a ++ b).getD j Sym.blank = a.getD j Sym.blank := by
  exact List.getD_append a b Sym.blank j hj

/-- enc 串长公式的 wS 版前缀界:0 < |encS|(结构非空)。 -/
lemma a2p_enc_pos (inst : SubsetSumInstance) : 0 < (encodeInstanceSym inst).length := by
  rw [r7_enc_len]
  omega

/-- wS@0 = #ₗ(左边界符)。 -/
lemma a2p_pos0_boundary (inst : SubsetSumInstance) (gS : List Sym) :
    (encodeInstanceSym inst ++ gS).getD 0 Sym.blank = Sym.boundary := by
  rw [a2p_getD_prefix_left (a := encodeInstanceSym inst) (b := gS) (by
    exact a2p_enc_pos inst)]
  exact r7_enc_getD_0 inst

/-- wS@(|bits|+1) = #₀(中边界符)。 -/
lemma a2p_pos_mid_boundary (inst : SubsetSumInstance) (gS : List Sym) :
    (encodeInstanceSym inst ++ gS).getD
      ((encodeBitsSym inst.target).length + 1) Sym.blank = Sym.boundary := by
  rw [a2p_getD_prefix_left (a := encodeInstanceSym inst) (b := gS)]
  · exact r7_enc_getD_mid inst
  · rw [r7_enc_len]
    omega

/-- wS@(|encS|-1) = #₁(右边界符,初始 m=false)。 -/
lemma a2p_pos_last_boundary (inst : SubsetSumInstance) (gS : List Sym) :
    (encodeInstanceSym inst ++ gS).getD
      ((encodeInstanceSym inst).length - 1) Sym.blank = Sym.boundary := by
  rw [a2p_getD_prefix_left (a := encodeInstanceSym inst) (b := gS)]
  · exact r7_enc_getD_last inst
  · exact Nat.sub_lt (a2p_enc_pos inst) (by norm_num)

/-- encS 的 target 区(位置 1..|bits|)每格 kind ∈ {data0, data1}。 -/
lemma a2p_bits_region_kind (inst : SubsetSumInstance) {j : ℕ}
    (hj : j < (encodeBitsSym inst.target).length) :
    ((encodeInstanceSym inst).getD (1 + j) Sym.blank).1 = SymKind.data0 ∨
    ((encodeInstanceSym inst).getD (1 + j) Sym.blank).1 = SymKind.data1 := by
  unfold encodeInstanceSym
  let X₂ : List Sym := [Sym.boundary] ++ encodeBitsSym inst.target
  let X₁ : List Sym := X₂ ++ [Sym.boundary]
  let X₀ : List Sym := X₁ ++ encodeElementsSym inst.elements
  change ((X₀ ++ [Sym.boundary]).getD (1 + j) Sym.blank).1 = SymKind.data0 ∨
    ((X₀ ++ [Sym.boundary]).getD (1 + j) Sym.blank).1 = SymKind.data1
  have hL₀ : 1 + j < X₀.length := by
    dsimp [X₀, X₁, X₂]
    simp [List.length_append]
    omega
  have hL₁ : 1 + j < X₁.length := by
    dsimp [X₁, X₂]
    simp [List.length_append]
    omega
  have hL₂ : 1 + j < X₂.length := by
    dsimp [X₂]
    simp [List.length_append]
    omega
  have hR : [Sym.boundary].length ≤ 1 + j := by
    simp
  have hcell : (X₀ ++ [Sym.boundary]).getD (1 + j) Sym.blank =
      (encodeBitsSym inst.target).getD j Sym.blank := by
    calc
      (X₀ ++ [Sym.boundary]).getD (1 + j) Sym.blank
          = X₀.getD (1 + j) Sym.blank := by
              exact r7_getD_append_left X₀ [Sym.boundary] Sym.blank (1 + j) hL₀
      _ = X₁.getD (1 + j) Sym.blank := by
              exact r7_getD_append_left X₁ (encodeElementsSym inst.elements) Sym.blank (1 + j) hL₁
      _ = X₂.getD (1 + j) Sym.blank := by
              exact r7_getD_append_left X₂ [Sym.boundary] Sym.blank (1 + j) hL₂
      _ = (encodeBitsSym inst.target).getD ((1 + j) - [Sym.boundary].length) Sym.blank := by
              exact List.getD_append_right [Sym.boundary] (encodeBitsSym inst.target)
                Sym.blank (1 + j) hR
      _ = (encodeBitsSym inst.target).getD j Sym.blank := by
              congr 1 <;> simp
  rw [hcell]
  rw [List.getD_eq_getElem (encodeBitsSym inst.target) Sym.blank hj]
  exact encodeBitsSym_nonboundary inst.target ((encodeBitsSym inst.target)[j]'hj)
    (List.getElem_mem hj)

/-- wS 的 target 区每格 kind ∈ {data0, data1}。 -/
lemma a2p_bits_kind_wS (inst : SubsetSumInstance) (gS : List Sym) {j : ℕ}
    (hj : j < (encodeBitsSym inst.target).length) :
    ((encodeInstanceSym inst ++ gS).getD (1 + j) Sym.blank).1 = SymKind.data0 ∨
    ((encodeInstanceSym inst ++ gS).getD (1 + j) Sym.blank).1 = SymKind.data1 := by
  have hpre : 1 + j < (encodeInstanceSym inst).length := by
    rw [r7_enc_len]
    omega
  rw [a2p_getD_prefix_left (a := encodeInstanceSym inst) (b := gS) hpre]
  exact a2p_bits_region_kind inst hj

/-- encS 的元素区每格非 boundary(α/data 类;无 #₀'/#₁ 干扰)。 -/
lemma a2p_elems_region_nonboundary (inst : SubsetSumInstance) {j : ℕ}
    (hj : j < (encodeElementsSym inst.elements).length) :
    ((encodeInstanceSym inst).getD
      ((encodeBitsSym inst.target).length + 2 + j) Sym.blank).1 ≠ SymKind.boundary := by
  unfold encodeInstanceSym
  let X₂ : List Sym := [Sym.boundary] ++ encodeBitsSym inst.target
  let X₁ : List Sym := X₂ ++ [Sym.boundary]
  let X₀ : List Sym := X₁ ++ encodeElementsSym inst.elements
  change ((X₀ ++ [Sym.boundary]).getD ((encodeBitsSym inst.target).length + 2 + j)
    Sym.blank).1 ≠ SymKind.boundary
  have hL₀ : (encodeBitsSym inst.target).length + 2 + j < X₀.length := by
    dsimp [X₀, X₁, X₂]
    simp [List.length_append]
    omega
  have hR₁ : X₁.length ≤ (encodeBitsSym inst.target).length + 2 + j := by
    dsimp [X₁, X₂]
    simp [List.length_append]
  have hcell : (X₀ ++ [Sym.boundary]).getD ((encodeBitsSym inst.target).length + 2 + j)
      Sym.blank = (encodeElementsSym inst.elements).getD j Sym.blank := by
    calc
      (X₀ ++ [Sym.boundary]).getD ((encodeBitsSym inst.target).length + 2 + j) Sym.blank
          = X₀.getD ((encodeBitsSym inst.target).length + 2 + j) Sym.blank := by
              exact r7_getD_append_left X₀ [Sym.boundary] Sym.blank
                ((encodeBitsSym inst.target).length + 2 + j) hL₀
      _ = (encodeElementsSym inst.elements).getD
          ((encodeBitsSym inst.target).length + 2 + j - X₁.length) Sym.blank := by
              exact List.getD_append_right X₁ (encodeElementsSym inst.elements) Sym.blank
                ((encodeBitsSym inst.target).length + 2 + j) hR₁
      _ = (encodeElementsSym inst.elements).getD j Sym.blank := by
              congr 1 <;> dsimp [X₁, X₂] <;> simp [List.length_append]
  rw [hcell]
  rw [List.getD_eq_getElem (encodeElementsSym inst.elements) Sym.blank hj]
  exact encodeElementsSym_nonboundary 0 inst.elements
    ((encodeElementsSym inst.elements)[j]'hj) (List.getElem_mem hj)

/-- wS 的元素区每格非 boundary。 -/
lemma a2p_elems_kind_wS (inst : SubsetSumInstance) (gS : List Sym) {j : ℕ}
    (hj : j < (encodeElementsSym inst.elements).length) :
    ((encodeInstanceSym inst ++ gS).getD
      ((encodeBitsSym inst.target).length + 2 + j) Sym.blank).1 ≠ SymKind.boundary := by
  have hpre : (encodeBitsSym inst.target).length + 2 + j < (encodeInstanceSym inst).length := by
    rw [r7_enc_len]
    omega
  rw [a2p_getD_prefix_left (a := encodeInstanceSym inst) (b := gS) hpre]
  exact a2p_elems_region_nonboundary inst hj


-- ============================================================================
-- 模块 2:格式段(fmt)态集与转移分类
-- ============================================================================

/-- 格式段态集(首达 4 之前的态:0→1→2→3→24→29/26→27→38→28)。 -/
def a2p_fmtSet : Finset ℕ := {0, 1, 2, 3, 24, 26, 27, 29, 38, 28}

/-- fmt 入边封闭:next ∈ fmt ⟹ 源 ∈ fmt(0 无入边;100/101 吸收不产生 fmt 态)。 -/
lemma a2p_fmt_into_class (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hnext : r.nextState ∈ a2p_fmtSet) :
    (q : ℕ) ∈ a2p_fmtSet := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ∈ a2p_fmtSet →
        (q : ℕ) ∈ a2p_fmtSet := by
    native_decide
  exact hbb q s r hr hnext

/-- fmt 转移的 next(非 101):fmt ∪ {4}(防御 101 由可延拓排除;4 = 28 读 #₀)。 -/
lemma a2p_fmt_next_class (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hq : (q : ℕ) ∈ a2p_fmtSet)
    (hne : r.nextState ≠ 101) :
    r.nextState ∈ a2p_fmtSet ∨ r.nextState = 4 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) ∈ a2p_fmtSet →
      r.nextState ≠ 101 → r.nextState ∈ a2p_fmtSet ∨ r.nextState = 4 := by
    native_decide
  exact hbb q s r hr hq hne

/-- 1 态入边(步前态与读):0 读 boundary R,或 1 读 data R(写回)。 -/
lemma a2p_into_1 (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h1 : r.nextState = 1) :
    (q = 0 ∧ s.1 = SymKind.boundary ∧ r.moveDir = Dir.R) ∨
    (q = 1 ∧ (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ r.moveDir = Dir.R ∧
      r.writeSym.1 = s.1) := by
  exact sym_into_1_class q hq s r hr h1

/-- 2 态入边:1 读 boundary R,或 2 读 data/α R(写 sel/nosel 或回写)。 -/
lemma a2p_into_2 (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h2 : r.nextState = 2) :
    (q = 1 ∧ s.1 = SymKind.boundary ∧ r.moveDir = Dir.R) ∨
    (q = 2 ∧ (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.alpha) ∧
      r.moveDir = Dir.R) := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 2 →
        ((q : ℕ) = 1 ∧ s.1 = SymKind.boundary ∧ r.moveDir = Dir.R) ∨
        ((q : ℕ) = 2 ∧ (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.alpha) ∧
          r.moveDir = Dir.R) := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr h2

/-- 3 态入边:2 读 boundary S(#₁ 上停)。 -/
lemma a2p_into_3 (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h3 : r.nextState = 3) :
    q = 2 ∧ s.1 = SymKind.boundary ∧ r.moveDir = Dir.S := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 3 →
        (q : ℕ) = 2 ∧ s.1 = SymKind.boundary ∧ r.moveDir = Dir.S := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr h3

/-- 28 态入边:38 读 boundary-false(#ₗ@0)R。 -/
lemma a2p_into_28 (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h28 : r.nextState = 28) :
    (q = 38 ∧ s.1 = SymKind.boundary ∧ r.moveDir = Dir.R) ∨
    (q = 28 ∧ (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ r.moveDir = Dir.R) := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 28 →
        ((q : ℕ) = 38 ∧ s.1 = SymKind.boundary ∧ r.moveDir = Dir.R) ∨
        ((q : ℕ) = 28 ∧ (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ r.moveDir = Dir.R) := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr h28

/-- fmt 左扫态 {24,26,27,29,38} 的入边源仍在 fmt 左扫 ∪ {3,28 的源}。 -/
lemma a2p_into_fmtL (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s))
    (hnext : r.nextState ∈ ({24, 26, 27, 29, 38} : Finset ℕ)) :
    q ∈ a2p_fmtSet := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) →
      r.nextState ∈ ({24, 26, 27, 29, 38} : Finset ℕ) →
        (q : ℕ) ∈ a2p_fmtSet := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr hnext

/-- 左扫态读任意符号的移动方向:L(38 读 #ₗ → 28 R 除外;24/29/26/27/38 读 data 均 L)。 -/
lemma a2p_fmtL_move (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s))
    (hqL : q ∈ ({24, 26, 27, 29, 38} : Finset ℕ)) (hne : r.nextState ≠ 101) :
    r.nextState ∈ a2p_fmtSet ∨ r.nextState = 4 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) →
      (q : ℕ) ∈ ({24, 26, 27, 29, 38} : Finset ℕ) → r.nextState ≠ 101 →
        r.nextState ∈ a2p_fmtSet ∨ r.nextState = 4 := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr hqL hne


-- ============================================================================
-- 模块 2b:元素区精确内容(初始:每元素 = α 首 + data0/1 值位)——格式段 2/左扫态读格分类用
-- ============================================================================

/-- wS 元素区每格 kind ∈ {α, data0, data1}。 -/
lemma a2p_elems_exact_kind_wS (inst : SubsetSumInstance) (gS : List Sym)
    (hpos : ∀ v ∈ inst.elements, 0 < v) {j : ℕ}
    (hj : j < (encodeElementsSym inst.elements).length) :
    ((encodeInstanceSym inst ++ gS).getD
      ((encodeBitsSym inst.target).length + 2 + j) Sym.blank).1 = SymKind.alpha ∨
    ((encodeInstanceSym inst ++ gS).getD
      ((encodeBitsSym inst.target).length + 2 + j) Sym.blank).1 = SymKind.data0 ∨
    ((encodeInstanceSym inst ++ gS).getD
      ((encodeBitsSym inst.target).length + 2 + j) Sym.blank).1 = SymKind.data1 := by
  have hpre : (encodeBitsSym inst.target).length + 2 + j < (encodeInstanceSym inst).length := by
    rw [r7_enc_len]
    omega
  rw [a2p_getD_prefix_left (a := encodeInstanceSym inst) (b := gS) hpre]
  unfold encodeInstanceSym
  let X₂ : List Sym := [Sym.boundary] ++ encodeBitsSym inst.target
  let X₁ : List Sym := X₂ ++ [Sym.boundary]
  let X₀ : List Sym := X₁ ++ encodeElementsSym inst.elements
  change ((X₀ ++ [Sym.boundary]).getD ((encodeBitsSym inst.target).length + 2 + j)
    Sym.blank).1 = SymKind.alpha ∨
    ((X₀ ++ [Sym.boundary]).getD ((encodeBitsSym inst.target).length + 2 + j)
      Sym.blank).1 = SymKind.data0 ∨
    ((X₀ ++ [Sym.boundary]).getD ((encodeBitsSym inst.target).length + 2 + j)
      Sym.blank).1 = SymKind.data1
  have hL₀ : (encodeBitsSym inst.target).length + 2 + j < X₀.length := by
    dsimp [X₀, X₁, X₂]
    simp [List.length_append]
    omega
  have hR₁ : X₁.length ≤ (encodeBitsSym inst.target).length + 2 + j := by
    dsimp [X₁, X₂]
    simp [List.length_append]
  have hcell : (X₀ ++ [Sym.boundary]).getD ((encodeBitsSym inst.target).length + 2 + j)
      Sym.blank = (encodeElementsSym inst.elements).getD j Sym.blank := by
    calc
      (X₀ ++ [Sym.boundary]).getD ((encodeBitsSym inst.target).length + 2 + j) Sym.blank
          = X₀.getD ((encodeBitsSym inst.target).length + 2 + j) Sym.blank := by
              exact r7_getD_append_left X₀ [Sym.boundary] Sym.blank
                ((encodeBitsSym inst.target).length + 2 + j) hL₀
      _ = (encodeElementsSym inst.elements).getD
          ((encodeBitsSym inst.target).length + 2 + j - X₁.length) Sym.blank := by
              exact List.getD_append_right X₁ (encodeElementsSym inst.elements) Sym.blank
                ((encodeBitsSym inst.target).length + 2 + j) hR₁
      _ = (encodeElementsSym inst.elements).getD j Sym.blank := by
              congr 1 <;> dsimp [X₁, X₂] <;> simp [List.length_append]
  rw [hcell]
  exact q10h_elems_kind inst.elements j hj


-- ============================================================================
-- 模块 2c-1:fmt 段 tape kind 保持(读格 kind = 初始布局 kind 的论证基础)
-- ============================================================================

/-- fmt 态写 kind:回写同 kind,或(唯一例外)2 读 α 分支写 sel/nosel。 -/
lemma a2p_fmt_write_kind (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hq : (q : ℕ) ∈ a2p_fmtSet) :
    r.writeSym.1 = s.1 ∨
      (s.1 = SymKind.alpha ∧
        (r.writeSym.1 = SymKind.sel ∨ r.writeSym.1 = SymKind.nosel)) := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) ∈ a2p_fmtSet →
        r.writeSym.1 = s.1 ∨
          (s.1 = SymKind.alpha ∧
            (r.writeSym.1 = SymKind.sel ∨ r.writeSym.1 = SymKind.nosel)) := by
    native_decide
  exact hbb q s r hr hq

/-- fmt 路径上任意 cfg(态 ∈ fmt):每格 kind = 初始 kind,或该格是 2 分支写出的
    sel/nosel(初始 α 位)。 -/
lemma a2p_fmt_kind_stable (inst : SubsetSumInstance) (gS : List Sym)
    {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π cfg) :
    cfg.state ∈ a2p_fmtSet →
      ∀ j : ℤ,
        (cfg.tape j).1 = ((symInitialConfig (encodeInstanceSym inst ++ gS)).tape j).1 ∨
        ((cfg.tape j).1 = SymKind.sel ∨ (cfg.tape j).1 = SymKind.nosel) := by
  induction h with
  | nil =>
      intro hf j
      exact Or.inl rfl
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro hf' j
      have hf₁ : cfg₁.state ∈ a2p_fmtSet := by
        have hsrc := a2p_fmt_into_class ⟨cfg₁.state, q12_path_state_lt102
          (encodeInstanceSym inst ++ gS) π₀ cfg₁ hprev⟩ step.readSym step.result
          (by simpa [hread] using htrans)
        exact hsrc (by
          simpa [symStepConfig] using hf')
      have hkind := ih hf₁
      by_cases hw : cfg₁.headPos = j
      · have hwq := a2p_fmt_write_kind ⟨cfg₁.state,
            q12_path_state_lt102 (encodeInstanceSym inst ++ gS) π₀ cfg₁ hprev⟩
            step.readSym step.result (by simpa [hread] using htrans) hf₁
        rw [symStepConfig]
        simp [hw]
        rcases hwq with hsame | hbr
        · rw [hsame]
          rw [hread, ← hw]
          rcases hkind cfg₁.headPos with hk | hsel
          · exact Or.inl hk
          · exact Or.inr hsel
        · exact Or.inr hbr.2
      · rw [symStepConfig]
        simp [if_neg (Ne.symm hw)]
        exact hkind j

-- ============================================================================
-- 模块 2c-2:格式段头域(联合归纳,蓝图轮次 9)
-- 分量:1∈[1,n+1];2∈[n+2,L-1];3=L-1;24=L-2;29/26∈[n+1,L-3];
--       27=n;38∈[0,n-1];28∈[1,n+1]
-- ============================================================================

/-- πfmt 段态集(3 标 #₁ 之后:24→29/26→27→38→28)。 -/
def a2p_fmtPostSet : Finset ℕ := {24, 26, 27, 29, 38, 28}

/-- πfmt 段各态入边与方向(表级)。 -/
lemma a2p_into_24' (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (h24 : r.nextState = 24) :
    (q : ℕ) = 3 ∧ r.moveDir = Dir.L := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 24 →
        (q : ℕ) = 3 ∧ r.moveDir = Dir.L := by
    native_decide
  exact hbb q s r hr h24

lemma a2p_into_29' (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (h29 : r.nextState = 29) :
    (q : ℕ) = 24 ∨ (q : ℕ) = 26 ∨ (q : ℕ) = 29 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 29 →
        (q : ℕ) = 24 ∨ (q : ℕ) = 26 ∨ (q : ℕ) = 29 := by
    native_decide
  exact hbb q s r hr h29

lemma a2p_into_26' (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (h26 : r.nextState = 26) :
    (q : ℕ) = 29 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 26 → (q : ℕ) = 29 := by
    native_decide
  exact hbb q s r hr h26

lemma a2p_into_27' (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (h27 : r.nextState = 27) :
    (q : ℕ) = 26 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 27 → (q : ℕ) = 26 := by
    native_decide
  exact hbb q s r hr h27

lemma a2p_into_38' (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (h38 : r.nextState = 38) :
    (q : ℕ) = 27 ∨ (q : ℕ) = 38 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 38 →
        (q : ℕ) = 27 ∨ (q : ℕ) = 38 := by
    native_decide
  exact hbb q s r hr h38

/-- 步后 28:源 38(读 boundary,R)或 28(读 data,R);38/28 的 R 步反推读 kind。 -/
lemma a2p_into_28' (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (h28 : r.nextState = 28) :
    ((q : ℕ) = 38 ∨ (q : ℕ) = 28) ∧ r.moveDir = Dir.R := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 28 →
        ((q : ℕ) = 38 ∨ (q : ℕ) = 28) ∧ r.moveDir = Dir.R := by
    native_decide
  exact hbb q s r hr h28

lemma a2p_28_read_kind (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (28, s)) (h28 : r.nextState = 28) :
    s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
  have hbb : ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (28, s) → r.nextState = 28 →
        s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
    native_decide
  exact hbb s r hr h28

lemma a2p_38_to_28_read_boundary (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (38, s)) (h28 : r.nextState = 28) :
    s.1 = SymKind.boundary := by
  have hbb : ∀ s : Sym, ∀ r ∈ VerifierSym.transition (38, s),
      r.nextState = 28 → s.1 = SymKind.boundary := by
    intro s
    rcases s with ⟨ks, ms⟩ <;> cases ks <;> cases ms <;> decide
  exact hbb s r hr h28

/-- L 步类:24/29/26/27/38 读非 boundary(next 仍在该集)的 dir = L。 -/
lemma a2p_fmtPost_L_dir (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s))
    (hq : (q : ℕ) ∈ a2p_fmtPostSet) (hnext : r.nextState ∈ a2p_fmtPostSet) :
    r.moveDir = Dir.L ∨ (q : ℕ) = 38 ∨ (q : ℕ) = 28 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) ∈ a2p_fmtPostSet →
      r.nextState ∈ a2p_fmtPostSet →
        r.moveDir = Dir.L ∨ (q : ℕ) = 38 ∨ (q : ℕ) = 28 := by
    native_decide
  exact hbb q s r hr hq hnext

/-- 读 boundary 的 fmtPost 态(表级,带 m):24/27/29 → 101;26/38 读 false 转
    27/28(true → 101);28 → 4。 -/
lemma a2p_fmtPost_boundary_read (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hq : (q : ℕ) ∈ a2p_fmtPostSet)
    (hb : s.1 = SymKind.boundary) :
    (q : ℕ) = 26 ∨ (q : ℕ) = 38 ∨ (q : ℕ) = 28 ∨ r.nextState = 101 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) ∈ a2p_fmtPostSet →
      s.1 = SymKind.boundary →
        (q : ℕ) = 26 ∨ (q : ℕ) = 38 ∨ (q : ℕ) = 28 ∨ r.nextState = 101 := by
    native_decide
  exact hbb q s r hr hq hb

/-- 26 读 boundary-false → 27 L;boundary-true → 101。 -/
lemma a2p_26_boundary_read (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (26, s)) (hb : s.1 = SymKind.boundary) :
    (s.2 = false ∧ r.nextState = 27 ∧ r.moveDir = Dir.L) ∨
    (s.2 = true ∧ r.nextState = 101) := by
  have hbb : ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (26, s) → s.1 = SymKind.boundary →
        (s.2 = false ∧ r.nextState = 27 ∧ r.moveDir = Dir.L) ∨
        (s.2 = true ∧ r.nextState = 101) := by
    native_decide
  exact hbb s r hr hb

/-- 38 读 boundary-false → 28 R;boundary-true → 101。 -/
lemma a2p_38_boundary_read (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (38, s)) (hb : s.1 = SymKind.boundary) :
    (s.2 = false ∧ r.nextState = 28 ∧ r.moveDir = Dir.R) ∨
    (s.2 = true ∧ r.nextState = 101) := by
  have hbb : ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (38, s) → s.1 = SymKind.boundary →
        (s.2 = false ∧ r.nextState = 28 ∧ r.moveDir = Dir.R) ∨
        (s.2 = true ∧ r.nextState = 101) := by
    native_decide
  exact hbb s r hr hb


/-- bits 串非空(target > 0 → 位数 ≥ 1)。 -/
lemma a2p_bits_len_pos (inst : SubsetSumInstance) (ht : 0 < inst.target) :
    1 ≤ (encodeBitsSym inst.target).length := by
  have h := r7_bits_len_pos inst.target ht
  simpa [encodeBitsSym, encodeBitsSymNative] using h

-- 模块 2c-2 辅助簇:初始 tape 的位置分类(ℤ 版桥)+ fmt 态读 sel → 101
-- ============================================================================

/-- fmt 态读 sel/nosel → 101,除 2(读 sel 行)与 29(读 sel → 26)。 -/
lemma a2p_fmt_read_sel101 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hq : (q : ℕ) ∈ a2p_fmtSet)
    (hne29 : (q : ℕ) ≠ 29) (hne2 : (q : ℕ) ≠ 2)
    (hsel : s.1 = SymKind.sel ∨ s.1 = SymKind.nosel) :
    r.nextState = 101 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) ∈ a2p_fmtSet →
      (q : ℕ) ≠ 29 → (q : ℕ) ≠ 2 →
      (s.1 = SymKind.sel ∨ s.1 = SymKind.nosel) → r.nextState = 101 := by
    native_decide
  exact hbb q s r hr hq hne29 hne2 hsel

/-- 2 读 sel/nosel → 101(表级)。 -/
lemma a2p_2_read_sel101 (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (2, s))
    (hsel : s.1 = SymKind.sel ∨ s.1 = SymKind.nosel) :
    r.nextState = 101 := by
  have hbb : ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (2, s) →
      (s.1 = SymKind.sel ∨ s.1 = SymKind.nosel) → r.nextState = 101 := by
    native_decide
  exact hbb s r hr hsel

/-- 初始 tape 在带内位置 j 的取值 = 输入串格。 -/
lemma a2p_tape_init_eq_input (input : List Sym) {j : ℤ}
    (hj0 : 0 ≤ j) (hj1 : j.toNat < input.length) :
    (symInitialConfig input).tape j = input[j.toNat] := by
  simp [symInitialConfig, hj0, hj1]

/-- 桥:带内 ℤ 位置 = getD。 -/
lemma a2p_tape_at_getD (input : List Sym) {j : ℤ}
    (hj0 : 0 ≤ j) (hj1 : j.toNat < input.length) :
    (symInitialConfig input).tape j = input.getD j.toNat Sym.blank := by
  rw [a2p_tape_init_eq_input input hj0 hj1]
  exact (List.getD_eq_getElem input Sym.blank hj1).symm

/-- wS@0(#ₗ)的 tape 版。 -/
lemma a2p_tape0_wS (inst : SubsetSumInstance) (gS : List Sym) :
    (symInitialConfig (encodeInstanceSym inst ++ gS)).tape 0 = Sym.boundary := by
  rw [a2p_tape_at_getD (encodeInstanceSym inst ++ gS) (by norm_num) (by
    norm_num
    exact Or.inl (a2p_enc_pos inst))]
  simpa using a2p_pos0_boundary inst gS

/-- wS@(|bits|+1)(#₀)的 tape 版。 -/
lemma a2p_tape_mid_wS (inst : SubsetSumInstance) (gS : List Sym) :
    (symInitialConfig (encodeInstanceSym inst ++ gS)).tape
      (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) = Sym.boundary := by
  rw [a2p_tape_at_getD (encodeInstanceSym inst ++ gS) (by omega) (by
    simp
    rw [r7_enc_len]
    omega)]
  simpa using a2p_pos_mid_boundary inst gS

/-- wS@(|encS|-1)(#₁)的 tape 版。 -/
lemma a2p_tape_last_wS (inst : SubsetSumInstance) (gS : List Sym) :
    (symInitialConfig (encodeInstanceSym inst ++ gS)).tape
      (((encodeInstanceSym inst).length - 1 : ℕ) : ℤ) = Sym.boundary := by
  rw [a2p_tape_at_getD (encodeInstanceSym inst ++ gS) (by
    exact Int.natCast_nonneg _) (by
    simp
    have hL := a2p_enc_pos inst
    omega)]
  simpa using a2p_pos_last_boundary inst gS

/-- wS@(|encS|-1)(#₁)的 tape 版(ℤ 减形式:↑L - 1)。 -/
lemma a2p_tape_last_wS' (inst : SubsetSumInstance) (gS : List Sym) :
    (symInitialConfig (encodeInstanceSym inst ++ gS)).tape
      ((((encodeInstanceSym inst).length : ℕ) : ℤ) - 1) = Sym.boundary := by
  have hcast : (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 =
      (((encodeInstanceSym inst).length - 1 : ℕ) : ℤ) := by
    have hL0 := a2p_enc_pos inst
    omega
  rw [hcast]
  exact a2p_tape_last_wS inst gS

/-- target 区(1..n)每格 kind ∈ {data0, data1}(tape 版,ℕ 偏移)。 -/
lemma a2p_tape_bits_data_wS (inst : SubsetSumInstance) (gS : List Sym) {j : ℕ}
    (hj : j < (encodeBitsSym inst.target).length) :
    ((symInitialConfig (encodeInstanceSym inst ++ gS)).tape (1 + (j : ℤ))).1 =
        SymKind.data0 ∨
    ((symInitialConfig (encodeInstanceSym inst ++ gS)).tape (1 + (j : ℤ))).1 =
        SymKind.data1 := by
  rw [a2p_tape_at_getD (encodeInstanceSym inst ++ gS) (by omega) (by
    simp
    rw [r7_enc_len]
    omega)]
  have hj' : (1 + (j : ℤ)).toNat = 1 + j := by omega
  rw [hj']
  exact a2p_bits_kind_wS inst gS hj

/-- 元素区(n+2..)每格非 boundary(tape 版,ℕ 偏移)。 -/
lemma a2p_tape_elems_nonboundary_wS (inst : SubsetSumInstance) (gS : List Sym) {j : ℕ}
    (hj : j < (encodeElementsSym inst.elements).length) :
    ((symInitialConfig (encodeInstanceSym inst ++ gS)).tape
      (((encodeBitsSym inst.target).length + 2 + j : ℕ) : ℤ)).1 ≠ SymKind.boundary := by
  rw [a2p_tape_at_getD (encodeInstanceSym inst ++ gS) (by omega) (by
    simp
    rw [r7_enc_len]
    omega)]
  have hj' : ((((encodeBitsSym inst.target).length + 2 + j : ℕ) : ℤ).toNat) =
      (encodeBitsSym inst.target).length + 2 + j := by omega
  rw [hj']
  exact a2p_elems_kind_wS inst gS hj

-- ============================================================================
/-- 位置 ∈ [1, n] 的初始格 kind ∈ {data0, data1}(ℤ 版)。 -/
lemma a2p_init_bits_tape (inst : SubsetSumInstance) (gS : List Sym) {j : ℤ}
    (hj1 : (1 : ℤ) ≤ j) (hj2 : j ≤ (((encodeBitsSym inst.target).length : ℕ) : ℤ)) :
    ((symInitialConfig (encodeInstanceSym inst ++ gS)).tape j).1 = SymKind.data0 ∨
    ((symInitialConfig (encodeInstanceSym inst ++ gS)).tape j).1 = SymKind.data1 := by
  have hj0 : 0 ≤ j := by omega
  rcases Int.eq_ofNat_of_zero_le hj0 with ⟨t, rfl⟩
  have hjt : 1 ≤ t ∧ t ≤ (encodeBitsSym inst.target).length := by omega
  have hj' : t = 1 + (t - 1) := by omega
  rw [hj']
  exact a2p_tape_bits_data_wS inst gS (by omega)

-- 模块 2c-2(fmt 域,特征位置不等式版):独立小定理 + 专门区
--   T0:0 态头 = 0;T1:1 ≤ 头 ≤ n+1;T2:n+2 ≤ 头 ≤ L-1;
--   A3:sel/nosel 格位 ≥ n+2(fmt 路径);T3:3 头 ∈ [n+2, L-1];
--   T4:24 头 ∈ [n+1, L-2];T56:{29,26}(26 ≥ n+1;29 ≥ 0;≤ L-2);
--   T7:27 ∈ [n, L-3];T8:38 ∈ [0, L-2];T9:28 ∈ [0, L-1];主装配。
-- ============================================================================

/-- T0:0 态 cfg 头 = 0(0 无入边;nil 头 0)。 -/
lemma a2p_s0_head (inst : SubsetSumInstance) (gS : List Sym)
    {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π cfg) :
    cfg.state = 0 → cfg.headPos = 0 := by
  induction h with
  | nil =>
      intro hq
      simp [symInitialConfig]
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro hq
      dsimp [symStepConfig] at hq
      have hq1lt : cfg₁.state < 102 :=
        q12_path_state_lt102 (encodeInstanceSym inst ++ gS) π₀ cfg₁ hprev
      have hdec : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
          r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 0 := by
        native_decide
      exact (hdec ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
        (by simpa [hread] using htrans) hq).elim

/-- T1:1 态 cfg 头 ∈ [1, n+1](1 读 #₀@n+1 转 2;头从 1 起递增)。
    n = |bits|。 -/
lemma a2p_s1_head (inst : SubsetSumInstance) (ht : 0 < inst.target) (gS : List Sym)
    {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π cfg)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101) :
    cfg.state = 1 →
      (1 : ℤ) ≤ cfg.headPos ∧
      cfg.headPos ≤ (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) := by
  induction h with
  | nil =>
      intro hq
      dsimp [symInitialConfig] at hq
      norm_num at hq
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro hq
      dsimp [symStepConfig] at hq
      have hq1lt : cfg₁.state < 102 :=
        q12_path_state_lt102 (encodeInstanceSym inst ++ gS) π₀ cfg₁ hprev
      have hno101s : step.result.nextState ≠ 101 :=
        hno101 step (by simp)
      have hno101₀ : ∀ step₀ ∈ π₀, step₀.result.nextState ≠ 101 := by
        intro step₀ hs0
        exact hno101 step₀ (by simp [hs0])
      have hsrc := a2p_into_1 cfg₁.state hq1lt step.readSym step.result
        (by simpa [hread] using htrans) hq
      rcases hsrc with h01 | h11
      · -- 源 0:0 读 boundary → 1 R:头 = 1
        rcases h01 with ⟨hq0, hb, hdir⟩
        have hh0 : cfg₁.headPos = 0 := by
          -- 0 态 cfg 的头 = 0(T0;步前 cfg₁ 可达)
          exact a2p_s0_head inst gS hprev hq0
        rw [symStepConfig]
        simp [hh0, hdir, Dir.toInt]
      · -- 源 1:1 读 data → 1 R:头₀ = h₁+1;排除 h₁ = n+1
        rcases h11 with ⟨hq1, hdata, hdir⟩
        have hP1' : (1 : ℤ) ≤ cfg₁.headPos ∧
            cfg₁.headPos ≤ (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) := by
          exact ih hno101₀ hq1
        have hne : cfg₁.headPos ≠ (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) := by
          intro hc
          have hf₁ : cfg₁.state ∈ a2p_fmtSet := by
            rw [hq1]
            decide
          have hkind := a2p_fmt_kind_stable inst gS hprev hf₁ cfg₁.headPos
          rw [hread] at hdata
          rw [hc] at hdata hkind
          rcases hkind with hk | hs
          · -- 初始:位置 n+1 = #₀(boundary)≠ data
            have hk' : (cfg₁.tape (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ)).1 =
                SymKind.boundary := by
              rw [hk]
              rw [a2p_tape_mid_wS]
              rfl
            rcases hdata with hd0 | hd1
            · rw [hk'] at hd0; cases hd0
            · rw [hk'] at hd1; cases hd1
          · -- sel:1 读 sel → 101
            have hsel : step.readSym.1 = SymKind.sel ∨ step.readSym.1 = SymKind.nosel := by
              rw [← hc] at hs
              simpa [hread] using hs
            have hne29 : cfg₁.state ≠ 29 := by rw [hq1]; norm_num
            have hne2 : cfg₁.state ≠ 2 := by rw [hq1]; norm_num
            have h101 := a2p_fmt_read_sel101 ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
              (by simpa [hread] using htrans) hf₁ hne29 hne2 hsel
            exact hno101s h101
        rw [symStepConfig]
        simp [hdir, Dir.toInt]
        omega

/-- T2:2 态 cfg 头 ∈ [n+2, L-1](2 从 1@n+1 读 #₀ 进 n+2;自环 R 在 #₁ 停)。
    n = |bits|,L = |encS|。 -/
lemma a2p_s2_head (inst : SubsetSumInstance) (hm : 0 < (encodeElementsSym inst.elements).length)
    (ht : 0 < inst.target) (gS : List Sym)
    {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π cfg)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101) :
    cfg.state = 2 →
      (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ cfg.headPos ∧
      cfg.headPos < (((encodeInstanceSym inst).length : ℕ) : ℤ) := by
  induction h with
  | nil =>
      intro hq
      dsimp [symInitialConfig] at hq
      norm_num at hq
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro hq
      dsimp [symStepConfig] at hq
      have hq1lt : cfg₁.state < 102 :=
        q12_path_state_lt102 (encodeInstanceSym inst ++ gS) π₀ cfg₁ hprev
      have hno101s : step.result.nextState ≠ 101 :=
        hno101 step (by simp)
      have hno101₀ : ∀ step₀ ∈ π₀, step₀.result.nextState ≠ 101 := by
        intro step₀ hs0
        exact hno101 step₀ (by simp [hs0])
      have hsrc := a2p_into_2 cfg₁.state hq1lt step.readSym step.result
        (by simpa [hread] using htrans) hq
      rcases hsrc with h12 | h22
      · -- 源 1:1 读 boundary → 2 R:1 的头 = n+1(#₀)⟹ 头₀ = n+2
        rcases h12 with ⟨hq1, hb, hdir⟩
        have hP1' : (1 : ℤ) ≤ cfg₁.headPos ∧
            cfg₁.headPos ≤ (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) := by
          exact a2p_s1_head inst ht gS hprev hno101₀ hq1
        have hhc : cfg₁.headPos = (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) := by
          by_contra hnc
          have hlt : cfg₁.headPos < (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) := by
            omega
          have hf₁ : cfg₁.state ∈ a2p_fmtSet := by
            rw [hq1]
            decide
          have hkind := a2p_fmt_kind_stable inst gS hprev hf₁ cfg₁.headPos
          rw [hread] at hb
          rcases hkind with hk | hs
          · -- 初始:位置 ∈ [1, n] → data(与读 boundary 矛盾)
            have hge1 : (1 : ℤ) ≤ cfg₁.headPos := hP1'.1
            have hlen : (1 : ℤ) ≤ cfg₁.headPos ∧
                cfg₁.headPos ≤ (((encodeBitsSym inst.target).length : ℕ) : ℤ) := by
              omega
            have hb' := a2p_init_bits_tape inst gS (j := cfg₁.headPos) hlen.1 hlen.2
            have hkk : ((symInitialConfig (encodeInstanceSym inst ++ gS)).tape
                cfg₁.headPos).1 = SymKind.boundary := by
              rw [← hk]
              exact hb
            rcases hb' with hd0 | hd1
            · rw [hkk] at hd0; cases hd0
            · rw [hkk] at hd1; cases hd1
          · -- sel:1 读 sel → 101
            have hsel : step.readSym.1 = SymKind.sel ∨ step.readSym.1 = SymKind.nosel := by
              simpa [hread] using hs
            have hne29 : cfg₁.state ≠ 29 := by rw [hq1]; norm_num
            have hne2 : cfg₁.state ≠ 2 := by rw [hq1]; norm_num
            have h101 := a2p_fmt_read_sel101 ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
              (by simpa [hread] using htrans) hf₁ hne29 hne2 hsel
            exact hno101s h101
        rw [symStepConfig]
        simp [hhc, hdir, Dir.toInt]
        rw [r7_enc_len]
        omega
      · -- 源 2:2 读 data/α → 2 R:ih 双界 + 排除 h₁ = L-1(#₁ → 3)
        rcases h22 with ⟨hq2, hd, hdir⟩
        have hP2' : (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ cfg₁.headPos ∧
            cfg₁.headPos < (((encodeInstanceSym inst).length : ℕ) : ℤ) := by
          exact ih hno101₀ hq2
        have hne : cfg₁.headPos ≠ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 := by
          intro hc
          have hf₁ : cfg₁.state ∈ a2p_fmtSet := by
            rw [hq2]
            decide
          have hkind := a2p_fmt_kind_stable inst gS hprev hf₁ cfg₁.headPos
          rw [hread] at hd
          rw [hc] at hd hkind
          rcases hkind with hk | hs
          · -- 初始:位置 L-1 = #₁(boundary)≠ data/α
            have hk' : (cfg₁.tape ((((encodeInstanceSym inst).length : ℕ) : ℤ) - 1)).1 =
                SymKind.boundary := by
              rw [hk]
              rw [a2p_tape_last_wS']
              rfl
            rcases hd with hd0 | hd1 | ha
            · rw [hk'] at hd0; cases hd0
            · rw [hk'] at hd1; cases hd1
            · rw [hk'] at ha; cases ha
          · -- sel:2 读 sel → 101
            rw [← hc] at hs
            have hsel : step.readSym.1 = SymKind.sel ∨ step.readSym.1 = SymKind.nosel := by
              simpa [hread] using hs
            have h101 := a2p_2_read_sel101 step.readSym step.result
              (by simpa [hread, hq2] using htrans) hsel
            exact hno101s h101
        rw [symStepConfig]
        simp [hdir, Dir.toInt]
        omega

/-- A3:fmt 路径上 sel/nosel 格的位置 ≥ n+2(写 sel 的 fmt 步源 = 2 读 α,
    T2 给 2 头 ≥ n+2;初始带 < n+2 区无 sel)。 -/
lemma a2p_sel_ge_n2 (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (ht : 0 < inst.target) (gS : List Sym)
    {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π cfg)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101) :
    cfg.state ∈ a2p_fmtSet →
      ∀ j : ℤ,
        (cfg.tape j).1 = SymKind.sel ∨ (cfg.tape j).1 = SymKind.nosel →
          (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ j := by
  induction h with
  | nil =>
      intro hf j hj
      -- 初始带:j < n+2 的格 kind ∈ {boundary, data0, data1}(无 sel);带外 blank
      by_contra hlt
      have hjl : j < (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) := by omega
      have hj0 : 0 ≤ j := by
        by_contra hneg
        have hjneg : j < 0 := by omega
        have hcell : (symInitialConfig (encodeInstanceSym inst ++ gS)).tape j = Sym.blank := by
          simp [symInitialConfig, hjneg]
        rw [hcell] at hj
        rcases hj with hjs | hjn
        · cases hjs <;> simp [Sym.blank]
        · cases hjn <;> simp [Sym.blank]
      have hto : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj0
      have htn : j.toNat < (encodeBitsSym inst.target).length + 2 := by
        apply Int.ofNat_lt.mp
        rw [hto]
        exact hjl
      have hlen2 : (encodeBitsSym inst.target).length + 2 ≤
          (encodeInstanceSym inst ++ gS).length := by
        rw [List.length_append, r7_enc_len]
        omega
      have hc : (symInitialConfig (encodeInstanceSym inst ++ gS)).tape j =
          (encodeInstanceSym inst ++ gS).getD j.toNat Sym.blank :=
        a2p_tape_at_getD (encodeInstanceSym inst ++ gS) hj0 (lt_of_lt_of_le htn hlen2)
      -- 位置 t = j.toNat ∈ [0, n+1]:0 → boundary;1..n → data;n+1 → boundary
      have hkind : ((encodeInstanceSym inst ++ gS).getD j.toNat Sym.blank).1 =
            SymKind.boundary ∨
          ((encodeInstanceSym inst ++ gS).getD j.toNat Sym.blank).1 = SymKind.data0 ∨
          ((encodeInstanceSym inst ++ gS).getD j.toNat Sym.blank).1 = SymKind.data1 := by
        by_cases hz : j.toNat = 0
        · left
          have hb := a2p_pos0_boundary inst gS
          rw [hz, hb]
          rfl
        · have hzt : 1 ≤ j.toNat := by omega
          by_cases hmid : j.toNat = (encodeBitsSym inst.target).length + 1
          · left
            have hb := a2p_pos_mid_boundary inst gS
            rw [hmid, hb]
            rfl
          · right
            have hbn : j.toNat ≤ (encodeBitsSym inst.target).length := by omega
            have harg : j.toNat = 1 + (j.toNat - 1) := by omega
            rw [harg]
            exact a2p_bits_kind_wS inst gS (by omega)
      rw [hc] at hj
      rcases hkind with hb0 | hdata
      · rw [hb0] at hj
        rcases hj with hjs | hjn
        · cases hjs
        · cases hjn
      · rcases hdata with hd0 | hd1
        · rw [hd0] at hj
          rcases hj with hjs | hjn
          · cases hjs
          · cases hjn
        · rw [hd1] at hj
          rcases hj with hjs | hjn
          · cases hjs
          · cases hjn
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro hf j hj
      have hf₁ : cfg₁.state ∈ a2p_fmtSet := by
        have hsrc := a2p_fmt_into_class ⟨cfg₁.state, q12_path_state_lt102
          (encodeInstanceSym inst ++ gS) π₀ cfg₁ hprev⟩ step.readSym step.result
          (by simpa [hread] using htrans)
        exact hsrc (by simpa [symStepConfig] using hf)
      have hno101₀ : ∀ step₀ ∈ π₀, step₀.result.nextState ≠ 101 := by
        intro step₀ hs0
        exact hno101 step₀ (by simp [hs0])
      by_cases hw : cfg₁.headPos = j
      · -- 写位:写 sel/nosel ⟹ 写回同 kind(读 sel,ih)或 2 读 α(T2)
        have hwj : (step.result.writeSym).1 = SymKind.sel ∨ (step.result.writeSym).1 = SymKind.nosel := by
          dsimp [symStepConfig] at hj
          simpa [hw] using hj
        have hwq := a2p_fmt_write_kind ⟨cfg₁.state, q12_path_state_lt102
          (encodeInstanceSym inst ++ gS) π₀ cfg₁ hprev⟩ step.readSym step.result
          (by simpa [hread] using htrans) hf₁
        rcases hwq with hsame | hbr
        · -- 写回同 kind:写 sel ⟹ 读格 sel ⟹ ih(cfg₁ 的 sel 位 ≥ n+2)
          have hread_sel : (cfg₁.tape j).1 = SymKind.sel ∨ (cfg₁.tape j).1 = SymKind.nosel := by
            rw [← hw]
            rw [← hread]
            rw [hsame] at hwj
            exact hwj
          exact ih hno101₀ hf₁ j hread_sel
        · -- 写 sel/nosel 分支:源 = 2 读 α(表级)——T2 给 2 头 ≥ n+2
          have hq2 : cfg₁.state = 2 := by
            have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) →
                (q : ℕ) ∈ a2p_fmtSet →
                (r.writeSym.1 = SymKind.sel ∨ r.writeSym.1 = SymKind.nosel) →
                s.1 = SymKind.alpha →
                (q : ℕ) = 2 := by
              native_decide
            exact hbb ⟨cfg₁.state, q12_path_state_lt102
              (encodeInstanceSym inst ++ gS) π₀ cfg₁ hprev⟩ step.readSym step.result
              (by simpa [hread] using htrans) hf₁ hwj hbr.1
          have hge := a2p_s2_head inst hm ht gS hprev hno101₀ hq2
          rw [← hw]
          exact hge.1
      · -- 非写位:ih
        have hj' : (cfg₁.tape j).1 = SymKind.sel ∨ (cfg₁.tape j).1 = SymKind.nosel := by
          dsimp [symStepConfig] at hj
          simpa [if_neg (Ne.symm hw)] using hj
        exact ih hno101₀ hf₁ j hj'

-- ============================================================================
-- 模块 2c-2 续:T3-T9(fmtPost 各态特征位不等式;ℤ 减界,避免 natCast 减)
--   T3:3 头 ∈ [n+2, L);T4:24 头 ∈ [n+1, L);T56:{29,26} ≤ L-2 且 26 ≥ n+1;
--   T7:27 头 ∈ [1, L-2];T8:38 头 ∈ [0, L-3];T9:28 头 ∈ [1, L-1]
-- ============================================================================
/-- T3:3 态 cfg 头 ∈ [n+2, L)(3 = 2 头,2 读 boundary@<L 内唯一 = #₁@L-1)。 -/
lemma a2p_s3_head (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (ht : 0 < inst.target) (gS : List Sym)
    {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π cfg)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101) :
    cfg.state = 3 →
      (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ cfg.headPos ∧
      cfg.headPos < (((encodeInstanceSym inst).length : ℕ) : ℤ) := by
  intro hq
  induction h with
  | nil =>
      dsimp [symInitialConfig] at hq
      norm_num at hq
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      dsimp [symStepConfig] at hq
      have hq1lt : cfg₁.state < 102 :=
        q12_path_state_lt102 (encodeInstanceSym inst ++ gS) π₀ cfg₁ hprev
      have hno101₀ : ∀ step₀ ∈ π₀, step₀.result.nextState ≠ 101 := by
        intro step₀ hs0
        exact hno101 step₀ (by simp [hs0])
      rcases a2p_into_3 cfg₁.state hq1lt step.readSym step.result
        (by simpa [hread] using htrans) hq with ⟨hq2, hb, hdir⟩
      have hT2 := a2p_s2_head inst hm ht gS hprev hno101₀ hq2
      rw [symStepConfig]
      simp [hdir, Dir.toInt]
      exact hT2

/-- T4:24 态 cfg 头 ∈ [n+1, L)(24 = 3头-1,3 读 #₁ 标后 L)。 -/
lemma a2p_s24_head (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (ht : 0 < inst.target) (gS : List Sym)
    {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π cfg)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101) :
    cfg.state = 24 →
      (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) ≤ cfg.headPos ∧
      cfg.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 2 := by
  intro hq
  induction h with
  | nil =>
      dsimp [symInitialConfig] at hq
      norm_num at hq
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      dsimp [symStepConfig] at hq
      have hq1lt : cfg₁.state < 102 :=
        q12_path_state_lt102 (encodeInstanceSym inst ++ gS) π₀ cfg₁ hprev
      have hno101₀ : ∀ step₀ ∈ π₀, step₀.result.nextState ≠ 101 := by
        intro step₀ hs0
        exact hno101 step₀ (by simp [hs0])
      rcases a2p_into_24' ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
        (by simpa [hread] using htrans) hq with ⟨hq3, hdir⟩
      have hT3 := a2p_s3_head inst hm ht gS hprev hno101₀ hq3
      rw [symStepConfig]
      simp [hdir, Dir.toInt]
      omega


/-- T56(联合):态 ∈ {29, 26} → 头 ≤ L-2 且 0 ≤ 头 且(26 → 头 ≥ n+1)
    (29 从 24 读 data1 L 进或 26/29 自环 L;26 从 29 读 sel(位 ≥ n+2,A3)L 进;
    29@0 读 #ₗ → 101 故 29 头 ≥ 1)。 -/
lemma a2p_s56_head (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (ht : 0 < inst.target) (gS : List Sym)
    {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π cfg)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101) :
    cfg.state = 29 ∨ cfg.state = 26 →
      cfg.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 2 ∧
      (0 : ℤ) ≤ cfg.headPos ∧
      (cfg.state = 26 → (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) ≤ cfg.headPos) := by
  intro hq
  induction h with
  | nil =>
      rcases hq with hq29 | hq26
      · dsimp [symInitialConfig] at hq29
        norm_num at hq29
      · dsimp [symInitialConfig] at hq26
        norm_num at hq26
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      dsimp [symStepConfig] at hq
      have hq1lt : cfg₁.state < 102 :=
        q12_path_state_lt102 (encodeInstanceSym inst ++ gS) π₀ cfg₁ hprev
      have hno101₀ : ∀ step₀ ∈ π₀, step₀.result.nextState ≠ 101 := by
        intro step₀ hs0
        exact hno101 step₀ (by simp [hs0])
      rcases hq with hq29 | hq26
      · -- 步后 29:源 ∈ {24, 26, 29}(表级);dir = L
        have hsrc := a2p_into_29' ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
          (by simpa [hread] using htrans) hq29
        have hdir : step.result.moveDir = Dir.L := by
          have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
              r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 29 →
                r.moveDir = Dir.L := by
            native_decide
          exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
            (by simpa [hread] using htrans) hq29
        have hb1 : cfg₁.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 2 ∧
            (1 : ℤ) ≤ cfg₁.headPos ∧
            (cfg₁.state = 26 → (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) ≤
              cfg₁.headPos) := by
          rcases hsrc with h24 | h26 | h29
          · -- 源 24:T4 给 [n+1, L-2]
            have h24e : cfg₁.state = 24 := by simpa using h24
            have hT4 := a2p_s24_head inst hm ht gS hprev hno101₀ h24e
            have hnz : (0 : ℤ) < (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) := by
              exact Int.ofNat_lt.mpr (by omega : (0 : ℕ) < (encodeBitsSym inst.target).length + 1)
            constructor
            · exact hT4.2
            · constructor
              · omega
              · intro hq26e
                rw [h24e] at hq26e
                norm_num at hq26e
          · -- 源 26:T56(26 分量)
            have h26e : cfg₁.state = 26 := by simpa using h26
            have hT56 := ih hno101₀ (Or.inr h26e)
            have hnz : (0 : ℤ) < (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) := by
              exact Int.ofNat_lt.mpr (by omega : (0 : ℕ) < (encodeBitsSym inst.target).length + 1)
            constructor
            · exact hT56.1
            · constructor
              · omega
              · intro hq26e
                exact hT56.2.2 h26e
          · -- 源 29 自环:ih 的 29 分量 + 排除 29@0(读 #ₗ → 101 或读 sel → 26)
            have h29e : cfg₁.state = 29 := by simpa using h29
            have hT56 := ih hno101₀ (Or.inl h29e)
            have hone : (1 : ℤ) ≤ cfg₁.headPos := by
              by_contra hz
              have hz' : cfg₁.headPos = 0 := by omega
              have hf₁ : cfg₁.state ∈ a2p_fmtSet := by
                rw [h29e]
                decide
              have hkind := a2p_fmt_kind_stable inst gS hprev hf₁ cfg₁.headPos
              rw [hz'] at hkind
              have htr : step.result ∈ VerifierSym.transition (29, cfg₁.tape cfg₁.headPos) := by
                rw [h29e] at htrans
                exact htrans
              rcases hkind with hk | hs
              · -- 初始 #ₗ:29 读 boundary → 101(矛盾 hno101)
                have hk' : (cfg₁.tape 0).1 = SymKind.boundary := by
                  rw [hk]
                  rw [a2p_tape0_wS]
                  rfl
                have hbb : ∀ s : Sym, ∀ r : SymTransResult,
                    r ∈ VerifierSym.transition (29, s) → s.1 = SymKind.boundary →
                      r.nextState = 101 := by
                  native_decide
                have hbnd : (cfg₁.tape cfg₁.headPos).1 = SymKind.boundary := by
                  simpa [hz'] using hk'
                exact hno101 step (by simp) (hbb (cfg₁.tape cfg₁.headPos) step.result htr hbnd)
              · -- sel@0:A3(sel 位 ≥ n+2)矛盾
                have hA3 := a2p_sel_ge_n2 inst hm ht gS hprev hno101₀ hf₁ 0 hs
                have hnz : (0 : ℤ) < (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) := by
                  exact Int.ofNat_lt.mpr (by omega : (0 : ℕ) < (encodeBitsSym inst.target).length + 2)
                omega
            constructor
            · exact hT56.1
            · constructor
              · exact hone
              · intro hq26e
                rw [h29e] at hq26e
                norm_num at hq26e
        rw [symStepConfig]
        simp [hdir, Dir.toInt]
        constructor
        · omega
        · constructor
          · omega
          · intro hq26'
            rw [hq29] at hq26'
            norm_num at hq26'
      · -- 步后 26:源 = 29 读 sel/nosel(位 ≥ n+2 由 A3)L 进
        have hq1' : cfg₁.state = 29 := by
          simpa using (a2p_into_26' ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
            (by simpa [hread] using htrans) hq26)
        have hdir : step.result.moveDir = Dir.L := by
          have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
              r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 26 →
                r.moveDir = Dir.L := by
            native_decide
          exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
            (by simpa [hread] using htrans) hq26
        -- 29 读 sel/nosel(表级反推)
        have hsel : (cfg₁.tape cfg₁.headPos).1 = SymKind.sel ∨
            (cfg₁.tape cfg₁.headPos).1 = SymKind.nosel := by
          have hbb : ∀ s : Sym, ∀ r : SymTransResult,
              r ∈ VerifierSym.transition (29, s) → r.nextState = 26 →
                s.1 = SymKind.sel ∨ s.1 = SymKind.nosel := by
            native_decide
          have htr : step.result ∈ VerifierSym.transition (29, cfg₁.tape cfg₁.headPos) := by
            rw [hq1'] at htrans
            exact htrans
          exact hbb (cfg₁.tape cfg₁.headPos) step.result htr hq26
        have hf₁ : cfg₁.state ∈ a2p_fmtSet := by
          rw [hq1']
          decide
        have hge := a2p_sel_ge_n2 inst hm ht gS hprev hno101₀ hf₁ cfg₁.headPos hsel
        have hT56 := ih hno101₀ (Or.inl hq1')
        rw [symStepConfig]
        simp [hdir, Dir.toInt]
        constructor
        · omega
        · constructor
          · omega
          · intro hq26'
            omega

/-- T7:27 态 cfg 头 ∈ [1, L-2](27 = 26 读 boundary-false@≥n+1 L 进)。 -/
lemma a2p_s27_head (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (ht : 0 < inst.target) (gS : List Sym)
    {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π cfg)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101) :
    cfg.state = 27 →
      (1 : ℤ) ≤ cfg.headPos ∧
      cfg.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 2 := by
  intro hq
  induction h with
  | nil =>
      dsimp [symInitialConfig] at hq
      norm_num at hq
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      dsimp [symStepConfig] at hq
      have hq1lt : cfg₁.state < 102 :=
        q12_path_state_lt102 (encodeInstanceSym inst ++ gS) π₀ cfg₁ hprev
      have hno101₀ : ∀ step₀ ∈ π₀, step₀.result.nextState ≠ 101 := by
        intro step₀ hs0
        exact hno101 step₀ (by simp [hs0])
      have hq1' : cfg₁.state = 26 :=
        (a2p_into_27' ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
          (by simpa [hread] using htrans) hq)
      have hdir : step.result.moveDir = Dir.L := by
        have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
            r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 27 →
              r.moveDir = Dir.L := by
          native_decide
        exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
          (by simpa [hread] using htrans) hq
      have hT56 := a2p_s56_head inst hm ht gS hprev hno101₀ (Or.inr hq1')
      have hn1 : 1 ≤ (encodeBitsSym inst.target).length := a2p_bits_len_pos inst ht
      rw [symStepConfig]
      simp [hdir, Dir.toInt]
      omega

/-- T8:38 态 cfg 头 ∈ [0, L-3](38 从 27 读 data1 L 进或自环 L)。 -/
lemma a2p_s38_head (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (ht : 0 < inst.target) (gS : List Sym)
    {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π cfg)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101) :
    cfg.state = 38 →
      (0 : ℤ) ≤ cfg.headPos ∧
      cfg.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 3 := by
  intro hq
  induction h with
  | nil =>
      dsimp [symInitialConfig] at hq
      norm_num at hq
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      dsimp [symStepConfig] at hq
      have hq1lt : cfg₁.state < 102 :=
        q12_path_state_lt102 (encodeInstanceSym inst ++ gS) π₀ cfg₁ hprev
      have hno101₀ : ∀ step₀ ∈ π₀, step₀.result.nextState ≠ 101 := by
        intro step₀ hs0
        exact hno101 step₀ (by simp [hs0])
      rcases a2p_into_38' ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
        (by simpa [hread] using htrans) hq with h27 | h38
      · -- 源 27:27 读 data1 → 38 L;T7 给 27 ∈ [1, L-2]
        have h27e : cfg₁.state = 27 := by simpa using h27
        have hT7 := a2p_s27_head inst hm ht gS hprev hno101₀ h27e
        have hdir : step.result.moveDir = Dir.L := by
          have hbb : ∀ s : Sym, ∀ r : SymTransResult,
              r ∈ VerifierSym.transition (27, s) → r.nextState = 38 →
                r.moveDir = Dir.L := by
            native_decide
          have htr : step.result ∈ VerifierSym.transition (27, cfg₁.tape cfg₁.headPos) := by
            rw [h27e] at htrans
            exact htrans
          exact hbb (cfg₁.tape cfg₁.headPos) step.result htr hq
        rw [symStepConfig]
        simp [hdir, Dir.toInt]
        omega
      · -- 源 38 自环(读 data L):38@0 读 #ₗ → 28(非 38)
        have h38e : cfg₁.state = 38 := by simpa using h38
        have hT38 := ih hno101₀ h38e
        have hdir : step.result.moveDir = Dir.L := by
          have hbb : ∀ s : Sym, ∀ r : SymTransResult,
              r ∈ VerifierSym.transition (38, s) → r.nextState = 38 →
                r.moveDir = Dir.L := by
            native_decide
          have htr : step.result ∈ VerifierSym.transition (38, cfg₁.tape cfg₁.headPos) := by
            rw [h38e] at htrans
            exact htrans
          exact hbb (cfg₁.tape cfg₁.headPos) step.result htr hq
        -- 38@0 的读格 = #ₗ(boundary)→ 步后 28 ≠ 38:故步前头 ≠ 0
        have hne0 : cfg₁.headPos ≠ 0 := by
          intro hc
          have hf₁ : cfg₁.state ∈ a2p_fmtSet := by
            rw [h38e]
            decide
          have hkind := a2p_fmt_kind_stable inst gS hprev hf₁ cfg₁.headPos
          rw [hc] at hkind
          have htr : step.result ∈ VerifierSym.transition (38, cfg₁.tape cfg₁.headPos) := by
            rw [h38e] at htrans
            exact htrans
          rcases hkind with hk | hs
          · -- 初始 #ₗ:38 读 boundary → 28(≠ 38,矛盾)
            have hk' : (cfg₁.tape 0).1 = SymKind.boundary := by
              rw [hk]
              rw [a2p_tape0_wS]
              rfl
            have hreadb : step.readSym.1 = SymKind.boundary := by
              simpa [hread, hc] using hk'
            have hbb : ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition (38, s) → s.1 = SymKind.boundary →
                  r.nextState = 28 ∨ r.nextState = 101 := by
              native_decide
            have hbnd : (cfg₁.tape cfg₁.headPos).1 = SymKind.boundary := by
              simpa [hc] using hk'
            have hbad := hbb (cfg₁.tape cfg₁.headPos) step.result htr hbnd
            rcases hbad with hb28 | hb101
            · exfalso
              rw [hq] at hb28
              norm_num at hb28
            · exact hno101 step (by simp) hb101
          · -- sel:38 读 sel → 101(矛盾)
            have hbb : ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition (38, s) →
                (s.1 = SymKind.sel ∨ s.1 = SymKind.nosel) → r.nextState = 101 := by
              native_decide
            rw [← hc] at hs
            exact hno101 step (by simp) (hbb (cfg₁.tape cfg₁.headPos) step.result htr hs)
        rw [symStepConfig]
        simp [hdir, Dir.toInt]
        omega

/-- T9:28 态 cfg 头 ∈ [1, L-1)(28 从 38 读 #ₗ R 进或自环 R;@L-1 读 #₁ → 4)。 -/
lemma a2p_s28_head (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (ht : 0 < inst.target) (gS : List Sym)
    {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π cfg)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101) :
    cfg.state = 28 →
      (1 : ℤ) ≤ cfg.headPos ∧
      cfg.headPos < (((encodeInstanceSym inst).length : ℕ) : ℤ) := by
  intro hq
  induction h with
  | nil =>
      dsimp [symInitialConfig] at hq
      norm_num at hq
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      dsimp [symStepConfig] at hq
      have hq1lt : cfg₁.state < 102 :=
        q12_path_state_lt102 (encodeInstanceSym inst ++ gS) π₀ cfg₁ hprev
      have hno101₀ : ∀ step₀ ∈ π₀, step₀.result.nextState ≠ 101 := by
        intro step₀ hs0
        exact hno101 step₀ (by simp [hs0])
      rcases a2p_into_28' ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
        (by simpa [hread] using htrans) hq with ⟨hsrc, hdir⟩
      rcases hsrc with h38 | h28
      · -- 源 38 读 boundary → 28 R:T8 给 38 ∈ [0, L-3]
        have h38e : cfg₁.state = 38 := by simpa using h38
        have hT8 := a2p_s38_head inst hm ht gS hprev hno101₀ h38e
        rw [symStepConfig]
        simp [hdir, Dir.toInt]
        omega
      · -- 源 28 自环(读 data R):28@L-1 读 #₁(boundary/sel)→ 4/101(≠ 28)
        have h28e : cfg₁.state = 28 := by simpa using h28
        have hT28 := ih hno101₀ h28e
        have hne : cfg₁.headPos ≠ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 := by
          intro hc
          have hf₁ : cfg₁.state ∈ a2p_fmtSet := by
            rw [h28e]
            decide
          have hkind := a2p_fmt_kind_stable inst gS hprev hf₁ cfg₁.headPos
          rw [hc] at hkind
          have htr : step.result ∈ VerifierSym.transition (28, cfg₁.tape cfg₁.headPos) := by
            rw [h28e] at htrans
            exact htrans
          rcases hkind with hk | hs
          · -- 初始 #₁(boundary):28 读 boundary → 4(≠ 28,矛盾)
            have hk' : (cfg₁.tape ((((encodeInstanceSym inst).length : ℕ) : ℤ) - 1)).1 =
                SymKind.boundary := by
              rw [hk]
              rw [a2p_tape_last_wS']
              rfl
            have hbb : ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition (28, s) → s.1 = SymKind.boundary →
                  r.nextState = 4 := by
              native_decide
            have hbnd : (cfg₁.tape cfg₁.headPos).1 = SymKind.boundary := by
              simpa [hc] using hk'
            have hbad := hbb (cfg₁.tape cfg₁.headPos) step.result htr hbnd
            exfalso
            rw [hq] at hbad
            norm_num at hbad
          · -- sel:28 读 sel → 101(矛盾)
            have hbb : ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition (28, s) →
                (s.1 = SymKind.sel ∨ s.1 = SymKind.nosel) → r.nextState = 101 := by
              native_decide
            rw [← hc] at hs
            exact hno101 step (by simp) (hbb (cfg₁.tape cfg₁.headPos) step.result htr hs)
        rw [symStepConfig]
        simp [hdir, Dir.toInt]
        omega

/-- 主装配:fmt 态 cfg 头 ∈ [0, L)(0 ≤ 头 < L = |encS|);按态引用 T0-T9。 -/
lemma a2p_fmt_head_domain (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (ht : 0 < inst.target) (gS : List Sym)
    {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π cfg)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101) :
    cfg.state ∈ a2p_fmtSet →
      (0 : ℤ) ≤ cfg.headPos ∧
      cfg.headPos < (((encodeInstanceSym inst).length : ℕ) : ℤ) := by
  intro hf
  have hq1lt : cfg.state < 102 := q12_path_state_lt102
    (encodeInstanceSym inst ++ gS) π cfg h
  have hdec : ∀ q : Fin 102,
      (q : ℕ) ∈ a2p_fmtSet →
        (q : ℕ) = 0 ∨ (q : ℕ) = 1 ∨ (q : ℕ) = 2 ∨ (q : ℕ) = 3 ∨ (q : ℕ) = 24 ∨
        (q : ℕ) = 29 ∨ (q : ℕ) = 26 ∨ (q : ℕ) = 27 ∨ (q : ℕ) = 38 ∨ (q : ℕ) = 28 := by
    native_decide
  have hlt1 : (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) <
      (((encodeInstanceSym inst).length : ℕ) : ℤ) := by
    apply Int.ofNat_lt.mpr
    rw [r7_enc_len]
    omega
  have hLposz : (0 : ℤ) < (((encodeInstanceSym inst).length : ℕ) : ℤ) := by
    apply Int.ofNat_lt.mpr
    exact a2p_enc_pos inst
  rcases hdec ⟨cfg.state, hq1lt⟩ hf with h0 | h1 | h2 | h3 | h24 | h29 | h26 | h27 | h38 | h28
  · -- 0:头 = 0(T0)
    have hh := a2p_s0_head inst gS h h0
    constructor
    · omega
    · simpa [hh] using hLposz
  · -- 1:T1(1 ≤ 头 ≤ n+1 < L)
    have hT1 := a2p_s1_head inst ht gS h hno101 h1
    constructor
    · omega
    · exact lt_of_le_of_lt hT1.2 hlt1
  · -- 2:T2(n+2 ≤ 头 < L)
    have hT2 := a2p_s2_head inst hm ht gS h hno101 h2
    rw [r7_enc_len] at hT2 ⊢
    constructor
    · exact le_trans (Int.natCast_nonneg _) hT2.1
    · omega
  · -- 3:T3
    have hT3 := a2p_s3_head inst hm ht gS h hno101 h3
    rw [r7_enc_len] at hT3 ⊢
    constructor
    · exact le_trans (Int.natCast_nonneg _) hT3.1
    · omega
  · -- 24:T4
    have hT4 := a2p_s24_head inst hm ht gS h hno101 h24
    rw [r7_enc_len] at hT4 ⊢
    constructor
    · exact le_trans (Int.natCast_nonneg _) hT4.1
    · omega
  · -- 29:T56
    have hT56 := a2p_s56_head inst hm ht gS h hno101 (Or.inl h29)
    rw [r7_enc_len] at hT56 ⊢
    constructor
    · exact hT56.2.1
    · omega
  · -- 26:T56
    have hT56 := a2p_s56_head inst hm ht gS h hno101 (Or.inr h26)
    rw [r7_enc_len] at hT56 ⊢
    constructor
    · exact hT56.2.1
    · omega
  · -- 27:T7
    have hT7 := a2p_s27_head inst hm ht gS h hno101 h27
    rw [r7_enc_len] at hT7 ⊢
    constructor
    · omega
    · omega
  · -- 38:T8
    have hT8 := a2p_s38_head inst hm ht gS h hno101 h38
    rw [r7_enc_len] at hT8 ⊢
    constructor
    · exact hT8.1
    · omega
  · -- 28:T9
    have hT9 := a2p_s28_head inst hm ht gS h hno101 h28
    rw [r7_enc_len] at hT9 ⊢
    constructor
    · omega
    · omega






end Mp
