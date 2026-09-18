/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/



/-
真实子集和编码与 F4 语言下界。

本文件实现论文（measure.C.0.7.tex 第 5 节）所要求的「带固定虚部的 F4 编码」：
  - 语言输入 = encodeInstanceF4 inst（Sym 编译编码，flat4F4 ∘ encodeInstanceSym）；
  - α/β 是独立于元素值位的分支标记符号（元素 = α/β 标记 + k 位值位 + sep），
    其 4F4 末格虚部 = kindBits 的 i1 = 1，即 NTM2 分叉位置；
  - 验证时 q=2 读 α/β 分支，该格被改写为 sel/nosel（sel/nosel 的 i1 = 0，
    写回后该格不再触发分支）；元素值与目标值的二进制数据在实部（虚部 false）。

信息论下界的关键：编码中虚部 = 1 的符号数恰为元素个数，每条接受路径
逐符号消费整个输入，故分支次数 ≥ 元素个数（branchCount = imTrueCount）。
-/

import Mp.Basic
import Mp.CBTM
import Mp.IVM
import Mp.EssentialDimension
import Mp.LowerBound
import Mp.SubsetSumVerifierCBTM

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

open CBTM
open IVM
open SymToF4

-- ============================================================================
-- 真实编码
-- ============================================================================

/-- 自然数的二进制编码（最低位在前，虚部 false）。 -/
def natToBinaryF4Real (n : ℕ) : List F4 :=
  (Nat.digits 2 n).map boolToF4

/-- 每个元素 = alpha 分支标记（虚部 true）+ 元素二进制；后接 target 二进制。 -/
def encodeSubsetSumF4Real (inst : SubsetSumInstance) : List F4 :=
  inst.elements.flatMap (fun s => F4.alpha :: natToBinaryF4Real s) ++ natToBinaryF4Real inst.target

-- 二进制编码的虚部全 false
lemma natToBinaryF4Real_im_false (n : ℕ) :
    ∀ s ∈ natToBinaryF4Real n, F4.im s = false := by
  intro s hs
  rcases List.mem_map.mp hs with ⟨b, hb, rfl⟩
  simp [boolToF4]

lemma imTrueCount_natToBinaryF4Real (n : ℕ) :
    imTrueCount (natToBinaryF4Real n) = 0 := by
  unfold imTrueCount
  have hfilter : (natToBinaryF4Real n).filter (fun s => F4.im s) = [] := by
    rw [List.filter_eq_nil_iff]
    intro s hs
    have him : F4.im s = false := natToBinaryF4Real_im_false n s hs
    simp [him]
  rw [hfilter]
  rfl

lemma imTrueCount_cons_alpha_binary (s : ℕ) :
    imTrueCount (F4.alpha :: natToBinaryF4Real s) = 1 := by
  unfold imTrueCount
  rw [List.filter_cons_of_pos (by simp [F4.alpha])]
  have hfilter : (natToBinaryF4Real s).filter (fun x => F4.im x) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    have him : F4.im x = false := natToBinaryF4Real_im_false s x hx
    simp [him]
  rw [hfilter]
  rfl

lemma imTrueCount_flatMap_alpha_binary (l : List ℕ) :
    imTrueCount (l.flatMap (fun s => F4.alpha :: natToBinaryF4Real s)) = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rw [show (x :: xs).flatMap (fun s => F4.alpha :: natToBinaryF4Real s) =
        (F4.alpha :: natToBinaryF4Real x) ++
        xs.flatMap (fun s => F4.alpha :: natToBinaryF4Real s) from rfl]
      rw [imTrueCount_append, imTrueCount_cons_alpha_binary, ih]
      simp only [List.length_cons]
      omega

-- 编码中虚部 true 的符号数 = 元素个数
lemma imTrueCount_encodeSubsetSumF4Real (inst : SubsetSumInstance) :
    imTrueCount (encodeSubsetSumF4Real inst) = inst.elements.length := by
  unfold encodeSubsetSumF4Real
  rw [imTrueCount_append, imTrueCount_natToBinaryF4Real]
  simp [imTrueCount_flatMap_alpha_binary]

-- ============================================================================
-- F4 语言（带固定虚部的输入）
-- ============================================================================

/-- 带虚部的语言：F4 串的集合。虚部是输入的一部分，验证器不可选择。 -/
abbrev FLanguage : Type := Set (List F4)

/-- 子集和语言（F4 版本，Sym 编译编码）：输入 = encodeInstanceF4 inst 的前缀闭包
    （w = encodeInstanceF4 inst ++ g，g 为「boundary（#₁）以外的信息」——判定只关心
    到 #₁ 为止的编码前缀，之后的内容不予考虑，与机器行为一致：判定完成于 #₁，
    100 吸收不读后续格）。
    虚部标记 = NTM2 分叉位置（α/β 元素选择点），实部 = 元素与目标值数据。
    合法实例约束（与验证器格式检查一致）：
    · elements ≠ []（空实例非法，验证器状态 24 直接拒绝）；
    · 每个元素值 > 0（元素 0 的编码块全 0，格式检查拒绝）；
    · target > 0（target 区无前导 0，格式检查要求最高位 data1）。 -/
def subsetSumLanguageF4Real : FLanguage := fun w =>
  ∃ inst, ∃ gS : List Sym, w = encodeInstanceF4 inst ++ flat4F4 gS ∧ inst.elements ≠ [] ∧
    (∀ v ∈ inst.elements, 0 < v) ∧ 0 < inst.target ∧ subsetSumHolds inst

-- ============================================================================
-- 编译编码的虚部计数：imTrueCount (encodeInstanceF4 inst) = 元素个数
-- ============================================================================

/-- symTo4F4 的虚部 true 数：分支符号（α/β）记 1，否则 0。 -/
lemma imTrueCount_symTo4F4 (s : Sym) :
    imTrueCount (symTo4F4 s) = if Sym.isBranch s then 1 else 0 := by
  rcases s with ⟨k, mark⟩
  unfold symTo4F4 Sym.kindBits imTrueCount Sym.isBranch SymKind.isBranch
  cases k <;> simp [F4.zero, F4.one, F4.alpha, F4.beta]

/-- 展平后虚部 true 数 = 分支符号的个数。 -/
lemma imTrueCount_flatMap_symTo4F4 (l : List Sym) :
    imTrueCount (l.flatMap symTo4F4) = (l.filter Sym.isBranch).length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rw [show (x :: xs).flatMap symTo4F4 = symTo4F4 x ++ xs.flatMap symTo4F4 from rfl]
      rw [imTrueCount_append, ih, imTrueCount_symTo4F4]
      rcases x with ⟨k, mark⟩
      by_cases h : SymKind.isBranch k <;>
        simp [h, List.filter_cons, List.length_cons] <;> omega

/-- 实例编译编码展平后的虚部 true 符号数 = 元素个数。 -/
lemma imTrueCount_encodeInstanceF4 (inst : SubsetSumInstance) :
    imTrueCount (encodeInstanceF4 inst) = inst.elements.length := by
  unfold encodeInstanceF4 flat4F4
  rw [imTrueCount_flatMap_symTo4F4]
  unfold encodeInstanceSym
  simp [List.filter_append, List.filter_singleton, List.length_append, List.length_singleton,
    filter_branch_encodeBitsSym, filter_branch_encodeElementsSym_length,
    Sym.boundary, Sym.mk, Sym.isBranch]

-- ============================================================================
-- F4 版本的验证器集合与本质维度
-- ============================================================================

/-- F4 语言的验证器集合（直接接受 F4 串，虚部固定；磁带语义）。 -/
def FVerifiers (L : FLanguage) : Set CBTM :=
  { M | CBTM.isPolynomialTime M ∧ (∀ w : List F4, M.tapeAccepts w ↔ L w) }

/-- F4 语言在长度 n 上的本质维度。 -/
noncomputable def FessentialDimension (L : FLanguage) (n : ℕ) : ℕ := by
  classical
  by_cases h : ∃ M, M ∈ FVerifiers L
  · have h_ex : ∃ (k : ℕ), ∃ M, M ∈ FVerifiers L ∧ worstCaseDimension M n = k := by
      rcases h with ⟨M, hM⟩
      exact ⟨worstCaseDimension M n, M, hM, rfl⟩
    exact Nat.find h_ex
  · exact 0

theorem FessentialDimension_spec (L : FLanguage) (n : ℕ)
    (h_nonempty : ∃ M, M ∈ FVerifiers L) :
    ∃ M, M ∈ FVerifiers L ∧ worstCaseDimension M n = FessentialDimension L n := by
  classical
  have h_ex : ∃ (k : ℕ), ∃ M, M ∈ FVerifiers L ∧ worstCaseDimension M n = k := by
    rcases h_nonempty with ⟨M, hM⟩
    exact ⟨worstCaseDimension M n, M, hM, rfl⟩
  have h_ess_eq : FessentialDimension L n = Nat.find h_ex := by
    unfold FessentialDimension
    simp only [h_nonempty, dite_true]
  rw [h_ess_eq]
  exact Nat.find_spec h_ex

-- ============================================================================
-- 下界核心（磁带语义）：正确机器必须读取每个虚部 true 的激活位。
-- 磁带语义下接受路径不必消费整个输入，故「读序列 = 输入」不再免费；
-- 必读性由「翻转未读激活位的实部 → 编码失效 → 语言值改变」推出。
-- ============================================================================

/-- 符号对齐（合法块串）：flat4F4 的像（每个 8bit 符号块完整且 padding 位固定；
    输入带 2bit 符号经符号对应编译的合法输入域）。 -/
def IsSymbolAligned (w : List F4) : Prop :=
  ∃ wS : List Sym, w = flat4F4 wS

/-- CBTM 在符号对齐输入上的多项式时间（输入语义 = 计算纸带 4F4，spec 约定 25）：
    验证器（witness）是 4 带机，输入符号在物理实现上映射为计算带 4F4 符号串
    （flat4F4 像）；非 flat4F4 像的 F4 串不是这台机器的输入（4 带机无半符号，
    缺项输入语义已失、不接受——数计一体，2026-09-09 用户裁决），机器性质不在
    其上断言。界按输入格长（多项式对 4 倍缩放封闭，与按符号计数等价）。 -/
def CBTM.isPolynomialTimeAligned (M : CBTM) : Prop :=
  ∃ p : ℕ → ℕ, IsPolynomialBound p ∧
    ∀ (x : List F4), IsSymbolAligned x →
      ∀ (π : ComputationPath) (cfg : CBTMConfig M x),
        TapeReachablePath M x π cfg → cfg.state ∈ M.acceptStates →
        (∀ step ∈ π, step.fromState ∉ M.acceptStates) →
        π.length ≤ p x.length

/-- 两版多项式时间语义的关系（评审建议 2026-09-11）：全输入版 `isPolynomialTime`
    蕴含对齐版 `isPolynomialTimeAligned`（后者只在输入域 IsSymbolAligned 内断言，
    故是前者的弱化）。反向不成立：对齐版对非对齐输入不作约束。 -/
theorem isPolynomialTimeAligned_of_isPolynomialTime (M : CBTM)
    (h : CBTM.isPolynomialTime M) : CBTM.isPolynomialTimeAligned M := by
  rcases h with ⟨p, hp, hbound⟩
  exact ⟨p, hp, fun x _ π cfg hr ha hno => hbound x π cfg hr ha hno⟩

/-- 翻转第 i 格（0-based）的实部为 true。 -/
def flipReAt (w : List F4) (i : ℕ) : List F4 :=
  match w with
  | [] => []
  | s :: rest => if i = 0 then (true, s.2) :: rest else s :: flipReAt rest (i - 1)

/-- take 与 append 的分布（l₁.length ≤ n）。 -/
lemma take_append_of_ge {α : Type} (l₁ l₂ : List α) (n : ℕ) (h : l₁.length ≤ n) :
    (l₁ ++ l₂).take n = l₁ ++ l₂.take (n - l₁.length) := by
  induction l₁ generalizing n with
  | nil => simp
  | cons a rest ih =>
      have h' : rest.length + 1 ≤ n := by simpa using h
      have hn0 : 0 < n := by omega
      rw [List.cons_append]
      rw [List.take_cons hn0]
      congr 1
      have hrest : rest.length ≤ n - 1 := by omega
      rw [show (a :: rest).length = rest.length + 1 by simp]
      rw [show n - (rest.length + 1) = n - 1 - rest.length by omega]
      exact ih (n := n - 1) hrest

/-- flat4F4 与 take 交换（每 Sym 恰 4 格）。 -/
lemma flat4F4_take (l : List Sym) (k : ℕ) :
    flat4F4 (l.take k) = (flat4F4 l).take (4 * k) := by
  induction l generalizing k with
  | nil => cases k with
    | zero => simp [flat4F4]
    | succ n' => rfl
  | cons s rest ih =>
      cases k with
      | zero => simp [flat4F4]
      | succ k' =>
          rw [List.take_cons (by omega : 0 < k' + 1)]
          rw [show k' + 1 - 1 = k' by omega]
          rw [flat4F4, flat4F4]
          rw [List.flatMap_cons, List.flatMap_cons]
          rw [← flat4F4]
          rw [ih k']
          rw [take_append_of_ge (symTo4F4 s) (List.flatMap symTo4F4 rest) (4 * (k' + 1))
            (by simp [symTo4F4_length])]
          rw [show 4 * (k' + 1) - (symTo4F4 s).length = 4 * k' by
            simp [symTo4F4_length, Nat.mul_add, Nat.add_comm, Nat.mul_one]]
          rfl

/-- flat4F4 与 drop 交换（块对齐）。 -/
lemma flat4F4_drop (wS : List Sym) (j : ℕ) :
    flat4F4 (wS.drop j) = (flat4F4 wS).drop (4 * j) := by
  induction j generalizing wS with
  | zero => simp [flat4F4]
  | succ j ih =>
      cases wS with
      | nil => simp [flat4F4]
      | cons s rest =>
          simp [flat4F4]
          rw [List.drop_append]
          rw [show (symTo4F4 s).drop (4 * (j + 1)) = [] by
            rw [List.drop_eq_nil_of_le (by simp [symTo4F4_length] : 4 ≤ 4 * (j + 1))]]
          simp
          rw [show 4 * (j + 1) - 4 = 4 * j by omega]
          dsimp [flat4F4] at ih
          rw [ih rest]

/-- flipReAt 于 symTo4F4 的第 4 格 = mark 置 true 的编码。 -/
lemma flipReAt_symTo4F4_3 (s : Sym) :
    flipReAt (symTo4F4 s) 3 = symTo4F4 (Sym.mk s.1 true) := by
  rcases s with ⟨k, m⟩
  dsimp [flipReAt, symTo4F4]

/-- flat4F4 的长度 = 4 × 符号数。 -/
lemma flat4F4_length (wS : List Sym) : (flat4F4 wS).length = 4 * wS.length := by
  dsimp [flat4F4]
  induction wS with
  | nil => rfl
  | cons s rest ih =>
      simp [symTo4F4_length, ih]
      ring

/-- flat4F4 的块格分解：第 j 块第 k 格 = symTo4F4 (第 j 符号) 的第 k 格。 -/
lemma flat4F4_getD_block {wS : List Sym} {j k : ℕ} (hj : j < wS.length) (hk : k < 4) :
    (flat4F4 wS).getD (4 * j + k) F4.zero = (symTo4F4 (wS.getD j Sym.blank)).getD k F4.zero := by
  induction wS generalizing j k with
  | nil => simp at hj
  | cons s rest ih =>
      cases j with
      | zero =>
          dsimp [flat4F4, List.flatMap]
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left (by simpa [symTo4F4_length] using hk)]
          simp
      | succ j =>
          dsimp [flat4F4, List.flatMap]
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by simp [symTo4F4_length]; omega)]
          simp [symTo4F4_length]
          rw [show 4 * (j + 1) + k - 4 = 4 * j + k by omega]
          exact (by simpa [flat4F4, List.flatMap] using ih (Nat.lt_of_succ_lt_succ hj) hk)

/-- 实部翻转于 append 左段。 -/
lemma flipReAt_append_of_lt {w₁ w₂ : List F4} {i : ℕ} (hi : i < w₁.length) :
    flipReAt (w₁ ++ w₂) i = flipReAt w₁ i ++ w₂ := by
  induction w₁ generalizing i with
  | nil => simp at hi
  | cons s rest ih =>
      cases i with
      | zero => rfl
      | succ i =>
          dsimp [flipReAt]
          exact congrArg (fun l => s :: l) (ih (Nat.lt_of_succ_lt_succ hi))

/-- 实部翻转于 append 右段。 -/
lemma flipReAt_append_of_ge {w₁ w₂ : List F4} {i : ℕ} (hi : w₁.length ≤ i) :
    flipReAt (w₁ ++ w₂) i = w₁ ++ flipReAt w₂ (i - w₁.length) := by
  induction w₁ generalizing i with
  | nil => simp
  | cons s rest ih =>
      cases i with
      | zero => simp at hi
      | succ i =>
          simp [flipReAt]
          have hi' : rest.length + 1 ≤ i + 1 := by simpa using hi
          exact ih (Nat.le_of_succ_le_succ hi')

/-- flat4F4 的三段分解：第 j 块单独拆出。 -/
lemma flat4F4_split {wS : List Sym} {j : ℕ} (hj : j < wS.length) :
    flat4F4 wS = flat4F4 (wS.take j) ++ symTo4F4 (wS.getD j Sym.blank) ++
      flat4F4 (wS.drop (j + 1)) := by
  have h1 : wS = wS.take j ++ [wS.getD j Sym.blank] ++ wS.drop (j + 1) := by
    induction j generalizing wS with
    | zero =>
        cases wS with
        | nil => simp at hj
        | cons s rest => simp
    | succ j ih =>
        cases wS with
        | nil => simp at hj
        | cons s rest =>
            have := ih (Nat.lt_of_succ_lt_succ hj)
            simpa [List.getD_eq_getElem?_getD] using this
  calc
    flat4F4 wS = flat4F4 (wS.take j ++ [wS.getD j Sym.blank] ++ wS.drop (j + 1)) := by
      exact congrArg flat4F4 h1
    _ = flat4F4 (wS.take j) ++ symTo4F4 (wS.getD j Sym.blank) ++ flat4F4 (wS.drop (j + 1)) := by
      dsimp [flat4F4]
      rw [List.flatMap_append]
      rw [List.flatMap_append]
      simp

/-- 翻转 flat4F4 第 j 块的第 4 格 = 该块 mark 置 true 的编码。 -/
lemma flipReAt_flat4F4_block4 {wS : List Sym} {j : ℕ} (hj : j < wS.length) :
    flipReAt (flat4F4 wS) (4 * j + 3) =
      flat4F4 (wS.take j ++ [Sym.mk (wS.getD j Sym.blank).1 true] ++ wS.drop (j + 1)) := by
  rw [flat4F4_split hj]
  rw [flipReAt_append_of_lt (w₁ := flat4F4 (wS.take j) ++ symTo4F4 (wS.getD j Sym.blank))
    (w₂ := flat4F4 (wS.drop (j + 1)))
    (i := 4 * j + 3) (by
      rw [List.length_append]
      rw [flat4F4_length]
      simp [List.length_take, symTo4F4_length, Nat.min_eq_left (Nat.le_of_lt hj)])]
  rw [flipReAt_append_of_ge (w₁ := flat4F4 (wS.take j))
    (w₂ := symTo4F4 (wS.getD j Sym.blank)) (i := 4 * j + 3) (by
      rw [flat4F4_length]
      simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)])]
  rw [show 4 * j + 3 - (flat4F4 (wS.take j)).length = 3 by
    rw [flat4F4_length]
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]]
  rw [flipReAt_symTo4F4_3]
  dsimp [flat4F4]
  rw [List.flatMap_append]
  rw [List.flatMap_append]
  simp

/-- flat4F4 串中 im=true 的格必是某块的第 4 格。 -/
lemma im_true_is_block4_of_flat4F4 {wS : List Sym} {i : ℕ}
    (hi : i < (flat4F4 wS).length)
    (him : F4.im ((flat4F4 wS).getD i F4.zero) = true) :
    i % 4 = 3 := by
  have hid : i = 4 * (i / 4) + i % 4 := by omega
  have hlt : i % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hblock : i / 4 < wS.length := by
    rw [flat4F4_length] at hi
    omega
  have hget := flat4F4_getD_block (wS := wS) (j := i / 4) (k := i % 4) hblock hlt
  rw [hid] at him
  rw [hget] at him
  by_contra hne
  have hlt3 : i % 4 < 3 := by omega
  have himF : F4.im ((symTo4F4 (wS.getD (i / 4) Sym.blank)).getD (i % 4) F4.zero) = false := by
    rcases wS.getD (i / 4) Sym.blank with ⟨kind, m⟩
    dsimp [symTo4F4]
    have hk : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 := by omega
    rcases hk with hk0 | hk1 | hk2
    · rw [hk0]; rfl
    · rw [hk1]; rfl
    · rw [hk2]; rfl
  rw [himF] at him
  cases him

/-- 翻转实例编码内激活位（im=true 格）的实部后仍是符号对齐串（该块 mark 置 true）。 -/
lemma flipReAt_activated_aligned (inst : SubsetSumInstance) (gS : List Sym) (i : ℕ)
    (hi : i < (encodeInstanceF4 inst).length)
    (him : F4.im ((encodeInstanceF4 inst).getD i F4.zero) = true) :
    IsSymbolAligned (flipReAt (encodeInstanceF4 inst ++ flat4F4 gS) i) := by
  dsimp [IsSymbolAligned, encodeInstanceF4]
  have hblock4 : i % 4 = 3 := by
    apply im_true_is_block4_of_flat4F4
    · simpa [encodeInstanceF4] using hi
    · simpa [encodeInstanceF4] using him
  let j := i / 4
  have hij : i = 4 * j + 3 := by
    dsimp [j]
    have := hblock4
    omega
  have hj : j < (encodeInstanceSym inst).length := by
    dsimp [j, encodeInstanceF4] at hi
    rw [flat4F4_length] at hi
    omega
  refine ⟨(encodeInstanceSym inst).take j ++
      [Sym.mk ((encodeInstanceSym inst).getD j Sym.blank).1 true] ++
      (encodeInstanceSym inst).drop (j + 1) ++ gS, ?_⟩
  rw [hij]
  rw [flipReAt_append_of_lt (w₁ := flat4F4 (encodeInstanceSym inst))
    (w₂ := flat4F4 gS) (i := 4 * j + 3) (by
      rw [flat4F4_length]
      dsimp [encodeInstanceF4] at hi
      rw [flat4F4_length] at hi
      omega)]
  rw [flipReAt_flat4F4_block4 hj]
  dsimp [flat4F4]
  rw [List.flatMap_append]
  rw [List.flatMap_append]
  rw [List.flatMap_append]
  simp

lemma flipReAt_length (w : List F4) (i : ℕ) : (flipReAt w i).length = w.length := by
  induction w generalizing i with
  | nil => simp [flipReAt]
  | cons s rest ih =>
      simp [flipReAt]
      by_cases h : i = 0 <;> simp [h, ih]

/-- 翻转后第 i 格的实部为 true、虚部保持（i < w.length）。 -/
lemma flipReAt_getD_self (w : List F4) (i : ℕ) (hi : i < w.length) :
    (flipReAt w i).getD i F4.zero = (true, (w.getD i F4.zero).2) := by
  induction w generalizing i with
  | nil => simp at hi
  | cons s rest ih =>
      cases i with
      | zero => rfl
      | succ k =>
          have hk : k < rest.length := by simp at hi; exact hi
          simp [flipReAt, List.getD_cons_succ]
          exact ih k hk

/-- 翻转后其他格的符号不变（j < w.length）。 -/
lemma flipReAt_getD_ne (w : List F4) (i j : ℕ) (hij : j ≠ i) (hj : j < w.length) :
    (flipReAt w i).getD j F4.zero = w.getD j F4.zero := by
  induction w generalizing i j with
  | nil => simp at hj
  | cons s rest ih =>
      cases i with
      | zero =>
          cases j with
          | zero => exfalso; exact hij rfl
          | succ j' => simp [flipReAt]
      | succ i' =>
          cases j with
          | zero => simp [flipReAt]
          | succ j' =>
              have hj' : j' < rest.length := by simp at hj; exact hj
              simp [flipReAt]
              exact ih i' j' (by omega) hj'

/-- stepConfig 后带头位置的格被写入。 -/
lemma stepConfig_tapeAt_head {M : CBTM} {input : List F4} (cfg : CBTMConfig M input)
    (r : CBTMTransResult) :
    (stepConfig cfg r).tapeAt cfg.headPos = r.writeSym := by
  unfold stepConfig CBTMConfig.tapeAt
  simp [if_pos rfl]

/-- stepConfig 后其他格不变。 -/
lemma stepConfig_tapeAt_ne {M : CBTM} {input : List F4} (cfg : CBTMConfig M input)
    (r : CBTMTransResult) {j : ℤ} (hj : j ≠ cfg.headPos) :
    (stepConfig cfg r).tapeAt j = cfg.tapeAt j := by
  unfold stepConfig CBTMConfig.tapeAt
  simp [hj]

/-- configAtGo 的一步归约方程。 -/
lemma configAtGo_succ (M : CBTM) (input : List F4) (step : TransitionStep)
    (rest : ComputationPath) (state : ℕ) (tape : ℤ → F4) (pos : ℤ) (t : ℕ) :
    configAtGo M input (step :: rest) state tape pos (t + 1) =
      configAtGo M input rest step.result.nextState
        (fun i => if i = pos then step.result.writeSym else tape i)
        (pos + step.result.moveDir.toInt) t := rfl

/-- configAtGo 的零步方程。 -/
lemma configAtGo_zero (M : CBTM) (input : List F4) (steps : ComputationPath)
    (state : ℕ) (tape : ℤ → F4) (pos : ℤ) :
    configAtGo M input steps state tape pos 0 =
      { state := state, tape := tape,
        headPos := pos } := by
  cases steps <;> rfl

/-- configAtGo 只看前 t 步：前缀相同的路径在 t 处格局相同（任意起点）。 -/
lemma configAtGo_eq_of_take_eq (M : CBTM) (input : List F4) (π₁ π₂ : ComputationPath)
    (state : ℕ) (tape : ℤ → F4) (pos : ℤ) (t : ℕ) (h : π₁.take t = π₂.take t) :
    configAtGo M input π₁ state tape pos t = configAtGo M input π₂ state tape pos t := by
  induction t generalizing π₁ π₂ state tape pos with
  | zero => cases π₁ <;> cases π₂ <;> rfl
  | succ t ih =>
      cases π₁ with
      | nil =>
          cases π₂ with
          | nil => rfl
          | cons s₂ r₂ => simp at h
      | cons s₁ r₁ =>
          cases π₂ with
          | nil => simp at h
          | cons s₂ r₂ =>
              have hs : s₁ = s₂ := by
                have := congrArg (fun l : ComputationPath => l.getD 0 s₁) h
                simpa [List.getD_cons_zero] using this
              subst s₂
              have ht : r₁.take t = r₂.take t := by
                simpa using congrArg List.tail h
              rw [configAtGo_succ, configAtGo_succ]
              exact ih r₁ r₂ (state := s₁.result.nextState)
                (tape := fun i => if i = pos then s₁.result.writeSym else tape i)
                (pos := pos + s₁.result.moveDir.toInt) ht

/-- configAt 只看前 t 步：前缀相同的路径在 t 处格局相同。 -/
lemma configAt_eq_of_take_eq {M : CBTM} {input : List F4} {π₁ π₂ : ComputationPath}
    {t : ℕ} (h : π₁.take t = π₂.take t) :
    CBTM.configAt M input π₁ t = CBTM.configAt M input π₂ t := by
  unfold CBTM.configAt
  exact configAtGo_eq_of_take_eq M input π₁ π₂ M.startState (initialTapeOf input M.blankSym) 0 t h

/-- configAt 的前缀闭合：t ≤ π₀.length 时追加一步不影响前 t 步格局。 -/
lemma configAt_append_left {M : CBTM} {input : List F4} (π₀ : ComputationPath)
    (step : TransitionStep) {t : ℕ} (ht : t ≤ π₀.length) :
    CBTM.configAt M input (π₀ ++ [step]) t = CBTM.configAt M input π₀ t := by
  apply configAt_eq_of_take_eq
  rw [List.take_append_of_le_length (by omega)]

/-- configAtGo 的步进：第 (t+1) 步格局 = 第 t 步格局应用第 t 步转移（任意起点）。 -/
lemma configAtGo_succ_stepConfig (M : CBTM) (input : List F4) (π : ComputationPath)
    (state : ℕ) (tape : ℤ → F4) (pos : ℤ) (t : ℕ) (ht : t < π.length) :
    configAtGo M input π state tape pos (t + 1) =
      stepConfig (configAtGo M input π state tape pos t) (π.get ⟨t, ht⟩).result := by
  induction t generalizing π state tape pos with
  | zero =>
      cases π with
      | nil => simp at ht
      | cons s rest =>
          rw [Nat.zero_add, configAtGo_succ]
          unfold stepConfig
          simp only [configAtGo_zero]
          congr
  | succ t ih =>
      cases π with
      | nil => simp at ht
      | cons s rest =>
          have ht' : t < rest.length := by
            simp at ht
            exact ht
          have := ih (π := rest) (state := s.result.nextState)
            (tape := fun i => if i = pos then s.result.writeSym else tape i)
            (pos := pos + s.result.moveDir.toInt) ht'
          rw [configAtGo_succ, configAtGo_succ]
          simpa using this

/-- configAt 的步进：第 (t+1) 步格局 = 第 t 步格局应用第 t 步转移。 -/
lemma configAt_succ_stepConfig (M : CBTM) (input : List F4) (π : ComputationPath)
    (t : ℕ) (ht : t < π.length) :
    CBTM.configAt M input π (t + 1) =
      stepConfig (CBTM.configAt M input π t) (π.get ⟨t, ht⟩).result := by
  unfold CBTM.configAt
  exact configAtGo_succ_stepConfig M input π M.startState (initialTapeOf input M.blankSym) 0 t ht

/-- 磁带路径桥：TapeSteps 末端格局的头位置与状态 = configAt 链（headPos/state 与磁带无关）。 -/
lemma tapeSteps_state_head_eq_configAt {M : CBTM} {input : List F4} {π : ComputationPath}
    {cfg : CBTMConfig M input}
    (h : TapeSteps M input (initialConfig M input) π cfg) :
    cfg.state = (CBTM.configAt M input π π.length).state ∧
      cfg.headPos = (CBTM.configAt M input π π.length).headPos := by
  let P (π' : ComputationPath) (cfg' : CBTMConfig M input) : Prop :=
    cfg'.state = (CBTM.configAt M input π' π'.length).state ∧
    cfg'.headPos = (CBTM.configAt M input π' π'.length).headPos
  change P π cfg
  induction h with
  | nil => constructor <;> rfl
  | cons π₀ step cfg' h_ind h_from h_read h_trans ih =>
      have hget : ((π₀ ++ [step]).get ⟨π₀.length, by simp⟩) = step := by
        simp [List.getElem_append_right, List.getElem_cons_zero]
      rcases ih with ⟨hst₀, hhp₀⟩
      constructor
      · rw [show List.length (π₀ ++ [step]) = π₀.length + 1 by simp]
        rw [configAt_succ_stepConfig M input (π₀ ++ [step]) π₀.length (by simp)]
        rw [configAt_append_left π₀ step (by omega)]
        rw [hget]
        rfl
      · rw [show List.length (π₀ ++ [step]) = π₀.length + 1 by simp]
        rw [configAt_succ_stepConfig M input (π₀ ++ [step]) π₀.length (by simp)]
        rw [configAt_append_left π₀ step (by omega)]
        rw [hget]
        unfold stepConfig
        rw [hhp₀]

/-- 核心：未读格 i 的翻转不影响路径（磁带语义，任意机器）。 -/
lemma tapeSteps_sim_under_unread_update {M : CBTM} {w w' : List F4} {π : ComputationPath}
    {i : ℤ} {cfg : CBTMConfig M w}
    (h : TapeSteps M w (initialConfig M w) π cfg)
    (hinit : ∀ j : ℤ, j ≠ i → (initialConfig M w).tapeAt j = (initialConfig M w').tapeAt j)
    (hskip : ∀ t, t < π.length → (CBTM.configAt M w π t).headPos ≠ i) :
    ∃ cfg' : CBTMConfig M w', TapeSteps M w' (initialConfig M w') π cfg' ∧
      cfg.state = cfg'.state ∧ cfg.headPos = cfg'.headPos ∧
      ∀ j : ℤ, j ≠ i → cfg.tapeAt j = cfg'.tapeAt j := by
  let P (π' : ComputationPath) (cfg' : CBTMConfig M w)
      (hsk : ∀ t, t < π'.length → (CBTM.configAt M w π' t).headPos ≠ i) : Prop :=
    ∃ cfg'' : CBTMConfig M w', TapeSteps M w' (initialConfig M w') π' cfg'' ∧
      cfg'.state = cfg''.state ∧ cfg'.headPos = cfg''.headPos ∧
      ∀ j : ℤ, j ≠ i → cfg'.tapeAt j = cfg''.tapeAt j
  have hP : P π cfg hskip := by
    induction h with
    | nil =>
        exact ⟨initialConfig M w', TapeSteps.nil, rfl, rfl, hinit⟩
    | cons π₀ step cfg₀ h_ind h_from h_read h_trans ih =>
        have hskip₀' : ∀ t, t < π₀.length → (CBTM.configAt M w π₀ t).headPos ≠ i := by
          intro t ht
          rw [← configAt_append_left (M := M) (input := w) π₀ step (by omega)]
          exact hskip t (by rw [List.length_append]; omega)
        rcases ih hskip₀' with ⟨cfg₀', hπ₀', hst₀, hhp₀, htp₀⟩
        have hcfg₀_head_ne : cfg₀.headPos ≠ i := by
          rcases tapeSteps_state_head_eq_configAt h_ind with ⟨_, hhp⟩
          have hhp' : (CBTM.configAt M w π₀ π₀.length).headPos ≠ i := by
            have hh : (CBTM.configAt M w (π₀ ++ [step]) π₀.length).headPos ≠ i :=
              hskip π₀.length (by simp [List.length_append])
            rwa [configAt_append_left π₀ step (by omega)] at hh
          rwa [← hhp] at hhp'
        have hread' : step.readSym = cfg₀'.tapeAt cfg₀'.headPos := by
          rw [h_read]
          rw [← hhp₀]
          rw [← htp₀ cfg₀.headPos hcfg₀_head_ne]
        have htrans' : step.result ∈ M.transition (cfg₀'.state, cfg₀'.tapeAt cfg₀'.headPos, cfg₀'.headPos) := by
          have hst' : cfg₀'.state = step.fromState := by rw [← hst₀, ← h_from]
          rw [hst']
          rw [h_from]
          rw [← hhp₀]
          rw [← htp₀ cfg₀.headPos hcfg₀_head_ne]
          exact h_trans
        refine ⟨stepConfig cfg₀' step.result,
          TapeSteps.cons π₀ step cfg₀' hπ₀' (by rw [h_from, hst₀]) hread' htrans', ?_⟩
        constructor
        · rfl
        constructor
        · unfold stepConfig
          rw [hhp₀]
        · intro j hj
          by_cases hh : j = cfg₀.headPos
          · subst j
            rw [stepConfig_tapeAt_head (cfg := cfg₀) (r := step.result)]
            rw [hhp₀]
            rw [stepConfig_tapeAt_head (cfg := cfg₀') (r := step.result)]
          · rw [stepConfig_tapeAt_ne (cfg := cfg₀) (r := step.result) (by exact hh)]
            have hh' : j ≠ cfg₀'.headPos := by
              rw [← hhp₀]
              exact hh
            rw [stepConfig_tapeAt_ne (cfg := cfg₀') (r := step.result) hh']
            exact htp₀ j hj
  change P π cfg hskip at hP
  exact hP

/-- 未读格翻转不改变接受性。 -/
lemma tapeAccepts_insensitive_to_unread_update {M : CBTM} {w w' : List F4} {i : ℤ}
    {π : ComputationPath} {cfg : CBTMConfig M w}
    (hr : TapeReachablePath M w π cfg) (ha : cfg.state ∈ M.acceptStates)
    (hinit : ∀ j : ℤ, j ≠ i → (initialConfig M w).tapeAt j = (initialConfig M w').tapeAt j)
    (hskip : ∀ t, t < π.length → (CBTM.configAt M w π t).headPos ≠ i) :
    M.tapeAccepts w' := by
  have hsteps : TapeSteps M w (initialConfig M w) π cfg :=
    (tapeSteps_initial_iff M w π cfg).2 hr
  rcases tapeSteps_sim_under_unread_update hsteps hinit hskip with
    ⟨cfg', hsteps', hst, hhp, _⟩
  refine ⟨π, cfg', (tapeSteps_initial_iff M w' π cfg').1 hsteps', ?_⟩
  rwa [← hst]

/-- getD 在界内恰为 get（core 环境无 get? 界内引理，归纳直证）。 -/
lemma getD_eq_get {α : Type} (l : List α) (i : ℕ) (d : α) (hi : i < l.length) :
    l.getD i d = l.get ⟨i, hi⟩ := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a rest ih =>
      cases i with
      | zero => rfl
      | succ k =>
          rw [List.getD_cons_succ]
          have hk : k < rest.length := by simp at hi; exact hi
          rw [ih k hk]
          change (a :: rest)[k + 1]'hi = rest[k]'hk
          rw [List.getElem_cons (i := k + 1)]
          simp

/-- 翻转后其他格的符号不变（get 版，归纳直证）。 -/
lemma flipReAt_get_ne (w : List F4) (i j : ℕ) (hij : j ≠ i) (hj : j < w.length) :
    (flipReAt w i).get ⟨j, by simpa [flipReAt_length] using hj⟩ = w.get ⟨j, hj⟩ := by
  induction w generalizing i j with
  | nil => simp at hj
  | cons s rest ih =>
      cases i with
      | zero =>
          cases j with
          | zero => exfalso; exact hij rfl
          | succ k =>
              have hk : k < rest.length := by simp at hj; exact hj
              simp [flipReAt]
              first | done | exact ih 0 k (by omega) hk
      | succ i' =>
          cases j with
          | zero => simp [flipReAt]
          | succ k =>
              have hk : k < rest.length := by simp at hj; exact hj
              simp [flipReAt]
              first | done | exact ih i' k (by omega) hk

/-- getD 越过前缀：l₁.length ≤ i 时 (l₁ ++ l₂).getD i = l₂.getD (i - l₁.length)。 -/
lemma getD_append_drop (l₁ l₂ : List F4) (i : ℕ) (d : F4)
    (hi : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  induction l₁ generalizing i with
  | nil => simp
  | cons a rest ih =>
      cases i with
      | zero => simp at hi
      | succ k =>
          rw [List.cons_append]
          rw [List.getD_cons_succ]
          have hk : rest.length ≤ k := by simp at hi; exact hi
          rw [show (a :: rest).length = rest.length + 1 by rfl]
          rw [Nat.add_sub_add_right]
          exact ih k hk

/-- flat4F4 的虚部 true 格实部必为 false（激活位恒为 (false, true)：α/β 末格，i1=true ⟹ mark=false）。 -/
lemma flat4F4_im_true_re_false (syms : List Sym)
    (hmark : ∀ s ∈ syms, (Sym.kindBits s.1).2.1 = true → s.2 = false) :
    ∀ i, i < (flat4F4 syms).length →
      F4.im ((flat4F4 syms).getD i F4.zero) = true →
      ((flat4F4 syms).getD i F4.zero).1 = false := by
  intro i hi him
  induction syms generalizing i with
  | nil => unfold flat4F4 at hi; simp at hi
  | cons s rest ih =>
      unfold flat4F4 at hi him ⊢
      rw [List.flatMap_cons] at hi him ⊢
      by_cases hi4 : i < 4
      · have hget : ((symTo4F4 s) ++ (List.flatMap symTo4F4 rest)).getD i F4.zero =
            (symTo4F4 s).getD i F4.zero := by
          rw [List.getD_append]
          simp [hi4, symTo4F4_length]
        rw [hget] at him ⊢
        have hi3 : i = 3 := by
          rcases symTo4F4_im_false_012 s with ⟨h0, h1, h2⟩
          interval_cases i <;> simp [symTo4F4, Sym.kindBits, List.getD] at him ⊢
        subst i
        have h4 : F4.im ((symTo4F4 s).getD 3 F4.zero) = (Sym.kindBits s.1).2.1 := by
          rcases s with ⟨k, m⟩
          cases k <;> rfl
        have hi1 : (Sym.kindBits s.1).2.1 = true := by
          rw [h4] at him
          exact him
        have hm : s.2 = false := hmark s (by simp) hi1
        simp [symTo4F4, hm]
      · have hirest : i - 4 < (flat4F4 rest).length := by
          rw [List.length_append, symTo4F4_length, List.length_flatMap] at hi
          unfold flat4F4
          rw [List.length_flatMap]
          omega
        have hget : ((symTo4F4 s) ++ (List.flatMap symTo4F4 rest)).getD i F4.zero =
            (flat4F4 rest).getD (i - 4) F4.zero := by
          unfold flat4F4
          rw [getD_append_drop (symTo4F4 s) (List.flatMap symTo4F4 rest) i F4.zero
            (by simpa [symTo4F4_length] using (Nat.le_of_not_gt hi4))]
          rw [symTo4F4_length]
        rw [hget] at him ⊢
        exact ih (by intro s' hs'; exact hmark s' (List.mem_cons_of_mem s hs')) (i - 4) hirest him

/-- encodeBitsSym 的元素 kind 恒为 data0/data1。 -/
lemma mem_encodeBitsSym_kind (n : ℕ) {s : Sym} (hs : s ∈ encodeBitsSym n) :
    s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
  unfold encodeBitsSym at hs
  rcases List.mem_map.mp hs with ⟨d, hd, rfl⟩
  by_cases hd0 : d = 0 <;> simp [hd0, Sym.data0, Sym.data1, Sym.mk]

/-- encodeBitsSymNative 的元素 kind 恒为 data0/data1。 -/
lemma mem_encodeBitsSymNative_kind (n : ℕ) {s : Sym} (hs : s ∈ encodeBitsSymNative n) :
    s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
  unfold encodeBitsSymNative at hs
  rcases List.mem_map.mp hs with ⟨d, hd, rfl⟩
  by_cases hd0 : d = 0 <;> simp [hd0, Sym.data0, Sym.data1, Sym.mk]

/-- encodeElementsSym 中 kind=alpha 的符号 mark 必为 false。 -/
lemma mem_encodeElementsSym_alpha_mark (elems : List ℕ) {s : Sym}
    (hs : s ∈ encodeElementsSym elems) (hk : s.1 = SymKind.alpha) : s.2 = false := by
  induction elems generalizing s with
  | nil => simp [encodeElementsSym] at hs
  | cons v rest ih =>
      by_cases hrest : rest = []
      · subst rest
        dsimp [encodeElementsSym] at hs
        rw [List.mem_cons] at hs
        rcases hs with h | h
        · subst s
          rfl
        · rcases mem_encodeBitsSymNative_kind v h with hd | hd <;> rw [hd] at hk <;> simp at hk
      · cases rest with
        | nil => exfalso; exact hrest rfl
        | cons v₂ rest₂ =>
            dsimp [encodeElementsSym] at hs
            rw [List.mem_cons] at hs
            rcases hs with h | h
            · subst s
              rfl
            · simp only [List.mem_append] at h
              cases h with
              | inl h₁ => rcases mem_encodeBitsSymNative_kind v h₁ with hd | hd <;> rw [hd] at hk <;> simp at hk
              | inr h₂ => exact ih h₂ hk

/-- encodeElementsSym 中 kind=beta 的符号 mark 必为 false。 -/
lemma mem_encodeElementsSym_beta_mark (elems : List ℕ) {s : Sym}
    (hs : s ∈ encodeElementsSym elems) (hk : s.1 = SymKind.beta) : s.2 = false := by
  induction elems generalizing s with
  | nil => simp [encodeElementsSym] at hs
  | cons v rest ih =>
      by_cases hrest : rest = []
      · subst rest
        dsimp [encodeElementsSym] at hs
        rw [List.mem_cons] at hs
        rcases hs with h | h
        · subst s
          rfl
        · rcases mem_encodeBitsSymNative_kind v h with hd | hd <;> rw [hd] at hk <;> simp at hk
      · cases rest with
        | nil => exfalso; exact hrest rfl
        | cons v₂ rest₂ =>
            dsimp [encodeElementsSym] at hs
            rw [List.mem_cons] at hs
            rcases hs with h | h
            · subst s
              cases hk
            · simp only [List.mem_append] at h
              cases h with
              | inl h₁ => rcases mem_encodeBitsSymNative_kind v h₁ with hd | hd <;> rw [hd] at hk <;> simp at hk
              | inr h₂ => exact ih h₂ hk

/-- 实例编码中 kind=beta 的符号 mark 必为 false。 -/
lemma mem_encodeInstanceSym_beta_mark (inst : SubsetSumInstance) {s : Sym}
    (hs : s ∈ encodeInstanceSym inst) (hk : s.1 = SymKind.beta) : s.2 = false := by
  unfold encodeInstanceSym at hs
  simp only [List.mem_append, List.mem_singleton] at hs
  rcases hs with h | h₅
  · rcases h with h | h₄
    · rcases h with h | h₃
      · rcases h with h₁ | h₂
        · rcases h₁ with rfl
          cases hk
        · rcases mem_encodeBitsSym_kind inst.target h₂ with hd | hd <;>
            rw [hd] at hk <;> simp at hk
      · rcases h₃ with rfl
        cases hk
    · exact mem_encodeElementsSym_beta_mark inst.elements h₄ hk
  · rcases h₅ with rfl
    cases hk

/-- 实例编码中 kind=alpha 的符号 mark 必为 false。 -/
lemma mem_encodeInstanceSym_alpha_mark (inst : SubsetSumInstance) {s : Sym}
    (hs : s ∈ encodeInstanceSym inst) (hk : s.1 = SymKind.alpha) : s.2 = false := by
  unfold encodeInstanceSym at hs
  simp only [List.mem_append, List.mem_singleton] at hs
  rcases hs with h | h₅
  · rcases h with h | h₄
    · rcases h with h | h₃
      · rcases h with h₁ | h₂
        · rcases h₁ with rfl
          cases hk
        · rcases mem_encodeBitsSym_kind inst.target h₂ with hd | hd <;>
            rw [hd] at hk <;> simp at hk
      · rcases h₃ with rfl
        cases hk
    · exact mem_encodeElementsSym_alpha_mark inst.elements h₄ hk
  · rcases h₅ with rfl
    cases hk

/-- encodeElementsSym 中符号的 kind 恒为 data0/data1/alpha/beta 之一。 -/
lemma mem_encodeElementsSym_kind_mem (elems : List ℕ) {s : Sym}
    (hs : s ∈ encodeElementsSym elems) :
    s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.alpha ∨
      s.1 = SymKind.beta := by
  induction elems generalizing s with
  | nil => simp [encodeElementsSym] at hs
  | cons v rest ih =>
      by_cases hrest : rest = []
      · subst rest
        dsimp [encodeElementsSym] at hs
        rw [List.mem_cons] at hs
        rcases hs with h | h
        · subst s
          right; right; left; rfl
        · rcases mem_encodeBitsSymNative_kind v h with hd | hd
          · left; exact hd
          · right; left; exact hd
      · cases rest with
        | nil => exfalso; exact hrest rfl
        | cons v₂ rest₂ =>
            dsimp [encodeElementsSym] at hs
            rw [List.mem_cons] at hs
            rcases hs with h | h
            · subst s
              right; right; left; rfl
            · simp only [List.mem_append] at h
              cases h with
              | inl h₁ =>
                  rcases mem_encodeBitsSymNative_kind v h₁ with hd | hd
                  · left; exact hd
                  · right; left; exact hd
              | inr h₂ => exact ih h₂

/-- 实例编码中符号的 kind 恒为 5 种合法 kind 之一。 -/
lemma mem_encodeInstanceSym_kind_mem (inst : SubsetSumInstance) {s : Sym}
    (hs : s ∈ encodeInstanceSym inst) :
    s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.alpha ∨
      s.1 = SymKind.beta ∨ s.1 = SymKind.boundary := by
  unfold encodeInstanceSym at hs
  simp only [List.mem_append, List.mem_singleton] at hs
  rcases hs with h | h₅
  · rcases h with h | h₄
    · rcases h with h | h₃
      · rcases h with h₁ | h₂
        · subst s
          right; right; right; right; rfl
        · rcases mem_encodeBitsSym_kind inst.target h₂ with hd | hd
          · left; exact hd
          · right; left; exact hd
      · subst s
        right; right; right; right; rfl
    · rcases mem_encodeElementsSym_kind_mem inst.elements h₄ with
        hd | hd | hd | hd
      · left; exact hd
      · right; left; exact hd
      · right; right; left; exact hd
      · right; right; right; left; exact hd
  · subst s
    right; right; right; right; rfl

/-- 编码中 kind=boundary 的符号恰为 Sym.boundary。 -/
lemma mem_encodeInstanceSym_boundary_eq (inst : SubsetSumInstance) {s : Sym}
    (hs : s ∈ encodeInstanceSym inst) (hk : s.1 = SymKind.boundary) : s = Sym.boundary := by
  unfold encodeInstanceSym at hs
  simp only [List.mem_append, List.mem_singleton] at hs
  rcases hs with h | h₅
  · rcases h with h | h₄
    · rcases h with h | h₃
      · rcases h with h₁ | h₂
        · exact h₁
        · rcases mem_encodeBitsSym_kind inst.target h₂ with hd | hd <;>
            rw [hd] at hk <;> simp at hk
      · exact h₃
    · rcases mem_encodeElementsSym_kind_mem inst.elements h₄ with
        hd | hd | hd | hd <;> rw [hd] at hk <;> simp at hk
  · exact h₅

/-- 编码实例的元素中 mark=true 者必为 data0/data1（其余符号 mark 恒 false）。 -/
theorem encodeInstanceSym_input_valid (inst : SubsetSumInstance) :
    ∀ s ∈ encodeInstanceSym inst, s.2 = true → s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
  intro s hs hm
  cases s with
  | mk k m =>
      cases k with
      | data0 => left; rfl
      | data1 => right; rfl
      | alpha =>
          have hf := mem_encodeInstanceSym_alpha_mark inst hs rfl
          exfalso
          change m = false at hf
          rw [hf] at hm
          cases hm
      | beta =>
          have hf := mem_encodeInstanceSym_beta_mark inst hs rfl
          exfalso
          change m = false at hf
          rw [hf] at hm
          cases hm
      | boundary =>
          have he : (Sym.mk SymKind.boundary m) = Sym.boundary :=
            mem_encodeInstanceSym_boundary_eq inst hs rfl
          exfalso
          have hmf : m = false := by
            simpa [Sym.boundary, Sym.mk] using (congrArg Prod.snd he)
          rw [hmf] at hm
          cases hm
      | sel =>
          exfalso
          have hk : (SymKind.sel, m).1 = SymKind.sel := rfl
          rcases mem_encodeInstanceSym_kind_mem inst hs with hd | hd | hd | hd | hd <;>
            rw [hd] at hk <;> cases hk
      | nosel =>
          exfalso
          have hk : (SymKind.nosel, m).1 = SymKind.nosel := rfl
          rcases mem_encodeInstanceSym_kind_mem inst hs with hd | hd | hd | hd | hd <;>
            rw [hd] at hk <;> cases hk
      | consumed =>
          exfalso
          have hk : (SymKind.consumed, m).1 = SymKind.consumed := rfl
          rcases mem_encodeInstanceSym_kind_mem inst hs with hd | hd | hd | hd | hd <;>
            rw [hd] at hk <;> cases hk

/-- 实例编码中 i1=true 的符号 mark 必为 false（α/β 的 mark=false，data 位 i1=false）。 -/
lemma encodeInstanceSym_i1_mark (inst : SubsetSumInstance) :
    ∀ s ∈ encodeInstanceSym inst, (Sym.kindBits s.1).2.1 = true → s.2 = false := by
  intro s hs hi1
  rcases s with ⟨k, m⟩
  cases k <;> simp [Sym.kindBits] at hi1 ⊢
  · exact mem_encodeInstanceSym_alpha_mark inst hs rfl
  · exact mem_encodeInstanceSym_beta_mark inst hs rfl

/-- 编码的虚部 true 格实部必为 false（激活位恒为 (false, true)，α/β 末格）。 -/
lemma encodeInstanceF4_im_true_re_false (inst : SubsetSumInstance) :
    ∀ i, i < (encodeInstanceF4 inst).length →
      F4.im ((encodeInstanceF4 inst).getD i F4.zero) = true →
      ((encodeInstanceF4 inst).getD i F4.zero).1 = false := by
  unfold encodeInstanceF4
  exact flat4F4_im_true_re_false (encodeInstanceSym inst) (encodeInstanceSym_i1_mark inst)

/-- symTo4F4 单射（4 格编码两两不同）。 -/
lemma symTo4F4_injective : Function.Injective symTo4F4 := by
  intro a b h
  rcases a with ⟨ka, ma⟩; rcases b with ⟨kb, mb⟩
  cases ka <;> cases ma <;> cases kb <;> cases mb <;> simp [symTo4F4, Sym.kindBits] at h ⊢
  all_goals cases h

/-- flat4F4 单射（块长 4 的编码单射）。 -/
lemma flat4F4_injective : Function.Injective (flat4F4 : List Sym → List F4) := by
  intro l₁ l₂ h
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => rfl
      | cons s rest => simp [flat4F4, symTo4F4] at h
  | cons a as ih =>
      cases l₂ with
      | nil => simp [flat4F4, symTo4F4] at h
      | cons b bs =>
          unfold flat4F4 at h
          have h4 : (symTo4F4 a ++ flat4F4 as).take 4 = (symTo4F4 b ++ flat4F4 bs).take 4 := by
            change (List.flatMap symTo4F4 (a :: as)).take 4 = (List.flatMap symTo4F4 (b :: bs)).take 4
            rw [h]
          rw [List.take_left' (l₁ := symTo4F4 a) (by simp [symTo4F4_length] : (symTo4F4 a).length = 4),
            List.take_left' (l₁ := symTo4F4 b) (by simp [symTo4F4_length] : (symTo4F4 b).length = 4)] at h4
          have hab : a = b := symTo4F4_injective (by simpa [symTo4F4_length] using h4)
          subst b
          have htail : flat4F4 as = flat4F4 bs := by
            have hd : (symTo4F4 a ++ flat4F4 as).drop 4 = (symTo4F4 a ++ flat4F4 bs).drop 4 := by
              change (List.flatMap symTo4F4 (a :: as)).drop 4 = (List.flatMap symTo4F4 (a :: bs)).drop 4
              rw [h]
            rw [List.drop_append_of_le_length (by simp [symTo4F4_length]),
              List.drop_append_of_le_length (by simp [symTo4F4_length])] at hd
            simpa [symTo4F4_length] using hd
          rw [ih htail]

/-- take 与 flipReAt 交换（n ≤ i 时翻转位不在前缀内）。 -/
lemma take_flipReAt_eq_of_le (w : List F4) (i n : ℕ) (hn : n ≤ i) :
    (flipReAt w i).take n = w.take n := by
  induction w generalizing i n with
  | nil =>
      cases n with
      | zero => simp
      | succ k => simp [flipReAt]
  | cons s rest ih =>
      cases n with
      | zero => simp
      | succ k =>
          have hi0 : i ≠ 0 := by omega
          rw [flipReAt]
          simp only [hi0, ite_false]
          rw [List.take_cons (by omega : 0 < k + 1), List.take_cons (by omega : 0 < k + 1)]
          change s :: List.take k (flipReAt rest (i - 1)) = s :: List.take k rest
          rw [ih (i := i - 1) (n := k) (by omega : k ≤ i - 1)]

/-- take n (l₁ ++ l₂) = take n l₁，当 n ≤ l₁.length。 -/
lemma take_append_of_le {α : Type} (l₁ l₂ : List α) (n : ℕ) (h : n ≤ l₁.length) :
    (l₁ ++ l₂).take n = l₁.take n := by
  induction l₁ generalizing n with
  | nil => simp at h; subst h; simp
  | cons a rest ih =>
      cases n with
      | zero => simp
      | succ k =>
          rw [List.cons_append]
          rw [List.take_cons (by omega : 0 < k + 1)]
          rw [List.take_cons (by omega : 0 < k + 1)]
          congr 1
          exact ih k (by simp at h; omega)

/-- encodeBitsSym 不产生 boundary 符号。 -/
lemma encodeBitsSym_no_boundary (n : ℕ) : ∀ s ∈ encodeBitsSym n, s.1 ≠ SymKind.boundary := by
  intro s hs
  rw [encodeBitsSym] at hs
  rcases List.mem_map.mp hs with ⟨d, hd, hsd⟩
  rw [← hsd]
  by_cases h0 : d = 0 <;> simp [h0, Sym.data0, Sym.data1]

/-- encodeBitsSymNative 不产生 boundary 符号。 -/
lemma encodeBitsSymNative_no_boundary (n : ℕ) :
    ∀ s ∈ encodeBitsSymNative n, s.1 ≠ SymKind.boundary := by
  intro s hs
  rw [encodeBitsSymNative] at hs
  rcases List.mem_map.mp hs with ⟨d, hd, hsd⟩
  rw [← hsd]
  by_cases h0 : d = 0 <;> simp [h0, Sym.data0, Sym.data1]

/-- encodeElementsSym 不产生 boundary 符号。 -/
lemma encodeElementsSym_no_boundary (elems : List ℕ) :
    ∀ s ∈ encodeElementsSym elems, s.1 ≠ SymKind.boundary := by
  intro s hs
  induction elems generalizing s with
  | nil => simp only [encodeElementsSym] at hs; cases hs
  | cons v rest ih =>
      cases rest with
      | nil =>
          unfold encodeElementsSym at hs
          simp only [List.mem_append, List.mem_singleton] at hs
          rcases hs with h | h
          · rw [h]
            simp [Sym.alpha]
          · exact encodeBitsSymNative_no_boundary v s h
      | cons v₂ rest₂ =>
          unfold encodeElementsSym at hs
          simp only [List.mem_append] at hs
          rcases hs with h | h
          · simp only [List.mem_append, List.mem_singleton] at h
            rcases h with hα | hb
            · rw [hα]
              simp [Sym.alpha]
            · exact encodeBitsSymNative_no_boundary v s hb
          · exact ih s h

lemma filter_boundary_eq_nil (l : List Sym) (hnb : ∀ s ∈ l, s.1 ≠ SymKind.boundary) :
    l.filter (fun s => decide (s.1 = SymKind.boundary)) = [] := by
  induction l with
  | nil => rfl
  | cons s rest ih =>
      rw [List.filter_cons]
      by_cases hb : s.1 = SymKind.boundary
      · exfalso
        exact hnb s (by simp) hb
      · rw [if_neg (by simpa using hb)]
        apply ih
        intro t ht
        exact hnb t (List.mem_cons.mpr (Or.inr ht))

/-- encodeInstanceSym 的 boundary 符号恰 3 个。 -/
lemma boundary_count_encodeInstanceSym (inst : SubsetSumInstance) :
    ((encodeInstanceSym inst).filter (fun s => decide (s.1 = SymKind.boundary))).length = 3 := by
  rw [encodeInstanceSym]
  rw [List.filter_append, List.filter_append, List.filter_append, List.filter_append]
  rw [filter_boundary_eq_nil (encodeBitsSym inst.target) (encodeBitsSym_no_boundary inst.target)]
  rw [filter_boundary_eq_nil (encodeElementsSym inst.elements) (encodeElementsSym_no_boundary inst.elements)]
  simp [Sym.boundary]

/-- encodeInstanceSym 的真前缀的 boundary 数 ≤ 2。 -/
lemma boundary_count_take_lt (inst : SubsetSumInstance) (n : ℕ)
    (hn : n < (encodeInstanceSym inst).length) :
    (((encodeInstanceSym inst).take n).filter (fun s => decide (s.1 = SymKind.boundary))).length ≤ 2 := by
  have hsubs : List.Sublist ((encodeInstanceSym inst).take n) ((encodeInstanceSym inst).take ((encodeInstanceSym inst).length - 1)) := by
    rw [show (encodeInstanceSym inst).take n = List.take n ((encodeInstanceSym inst).take ((encodeInstanceSym inst).length - 1)) by
      rw [List.take_take]
      rw [min_eq_left (by omega : n ≤ (encodeInstanceSym inst).length - 1)]]
    exact List.take_sublist n ((encodeInstanceSym inst).take ((encodeInstanceSym inst).length - 1))
  have hle := List.Sublist.length_le
    (hsubs.filter (fun s => decide (s.1 = SymKind.boundary)))
  have htake_last : (encodeInstanceSym inst).take ((encodeInstanceSym inst).length - 1) =
      [Sym.boundary] ++ encodeBitsSym inst.target ++ [Sym.boundary] ++ encodeElementsSym inst.elements := by
    rw [encodeInstanceSym]
    rw [List.take_left' (l₁ := [Sym.boundary] ++ encodeBitsSym inst.target ++
        [Sym.boundary] ++ encodeElementsSym inst.elements) (by simp; omega)]
  rw [htake_last] at hle
  have htwo : (([Sym.boundary] ++ encodeBitsSym inst.target ++ [Sym.boundary] ++ encodeElementsSym inst.elements).filter
      (fun s => decide (s.1 = SymKind.boundary))).length = 2 := by
    rw [List.filter_append, List.filter_append, List.filter_append]
    rw [filter_boundary_eq_nil (encodeBitsSym inst.target) (encodeBitsSym_no_boundary inst.target)]
    rw [filter_boundary_eq_nil (encodeElementsSym inst.elements) (encodeElementsSym_no_boundary inst.elements)]
    simp [Sym.boundary]
  rw [htwo] at hle
  exact hle

/-- 翻转任一激活位的实部 → 不是任何实例编码 → 语言值改变为 false。 -/
lemma flipReAt_activated_not_in_L (inst : SubsetSumInstance) (gS : List Sym) (i : ℕ)
    (hi : i < (encodeInstanceF4 inst).length)
    (him : F4.im ((encodeInstanceF4 inst).getD i F4.zero) = true) :
    ¬ subsetSumLanguageF4Real (flipReAt (encodeInstanceF4 inst ++ flat4F4 gS) i) := by
  intro hL
  rcases hL with ⟨inst', g', henc, _, _, _, _⟩
  by_cases hi' : i < (encodeInstanceF4 inst').length
  · -- 情形 1：翻转格落在 enc' 内
    have h_i : (flipReAt (encodeInstanceF4 inst ++ flat4F4 gS) i).getD i F4.zero = (true, true) := by
      rw [flipReAt_getD_self (encodeInstanceF4 inst ++ flat4F4 gS) i (by
        simp only [List.length_append]
        omega)]
      refine Prod.ext rfl ?_
      rw [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega : i < (encodeInstanceF4 inst).length)]
      rw [← List.getD_eq_getElem?_getD]
      simpa [F4.im] using him
    rw [henc] at h_i
    rw [List.getD_eq_getElem?_getD] at h_i
    rw [List.getElem?_append_left (by omega : i < (encodeInstanceF4 inst').length)] at h_i
    rw [← List.getD_eq_getElem?_getD] at h_i
    have h_i_re : ((encodeInstanceF4 inst').getD i F4.zero).1 = true := by
      simpa using congrArg Prod.fst h_i
    have h_i_im : F4.im ((encodeInstanceF4 inst').getD i F4.zero) = true := by
      simpa [F4.im] using congrArg Prod.snd h_i
    have hre' : ((encodeInstanceF4 inst').getD i F4.zero).1 = false :=
      encodeInstanceF4_im_true_re_false inst' i hi' h_i_im
    rw [hre'] at h_i_re
    cases h_i_re
  · -- 情形 2：enc' 是 enc(inst) 的对齐真前缀 → 非编码
    have hlen_le : (encodeInstanceF4 inst').length ≤ i := by omega
    have hpre : (encodeInstanceF4 inst).take (encodeInstanceF4 inst').length = encodeInstanceF4 inst' := by
      have ht1 : (flipReAt (encodeInstanceF4 inst ++ flat4F4 gS) i).take (encodeInstanceF4 inst').length =
          (encodeInstanceF4 inst' ++ flat4F4 g').take (encodeInstanceF4 inst').length := by rw [henc]
      rw [List.take_left] at ht1
      have ht2 : (flipReAt (encodeInstanceF4 inst ++ flat4F4 gS) i).take (encodeInstanceF4 inst').length =
          (encodeInstanceF4 inst ++ flat4F4 gS).take (encodeInstanceF4 inst').length := by
        rw [take_flipReAt_eq_of_le (encodeInstanceF4 inst ++ flat4F4 gS) i (encodeInstanceF4 inst').length hlen_le]
      rw [ht2] at ht1
      have ht3 : (encodeInstanceF4 inst ++ flat4F4 gS).take (encodeInstanceF4 inst').length =
          (encodeInstanceF4 inst).take (encodeInstanceF4 inst').length :=
        take_append_of_le (encodeInstanceF4 inst) (flat4F4 gS) (encodeInstanceF4 inst').length (by omega)
      rw [ht3] at ht1
      exact ht1
    -- 对齐：|enc'| = 4·k'，k' = Sym 编码长度
    have hlen4 : (encodeInstanceF4 inst').length = 4 * (encodeInstanceSym inst').length := by
      unfold encodeInstanceF4 flat4F4
      rw [List.length_flatMap]
      simp [symTo4F4_length, Nat.mul_comm]
    have htake_sym : (encodeInstanceF4 inst).take (encodeInstanceF4 inst').length =
        flat4F4 ((encodeInstanceSym inst).take (encodeInstanceSym inst').length) := by
      rw [hlen4]
      unfold encodeInstanceF4
      rw [flat4F4_take]
    rw [htake_sym] at hpre
    have hsym_eq : encodeInstanceSym inst' = (encodeInstanceSym inst).take (encodeInstanceSym inst').length := by
      apply flat4F4_injective
      rw [hpre]
      unfold encodeInstanceF4
      rfl
    have hk'lt : (encodeInstanceSym inst').length < (encodeInstanceSym inst).length := by
      have hsymlen : (encodeInstanceF4 inst).length = 4 * (encodeInstanceSym inst).length := by
        unfold encodeInstanceF4 flat4F4
        rw [List.length_flatMap]
        simp [symTo4F4_length, Nat.mul_comm]
      have hlt : (encodeInstanceF4 inst').length < (encodeInstanceF4 inst).length := by
        exact Nat.lt_of_le_of_lt hlen_le hi
      rw [hlen4, hsymlen] at hlt
      nlinarith
    have hb1 := boundary_count_encodeInstanceSym inst'
    have hb2 := boundary_count_take_lt inst (encodeInstanceSym inst').length hk'lt
    rw [← hsym_eq] at hb2
    omega

/-- 正确机器的每条接受路径必须读取每个激活位（反证：翻转未读激活位 → 语言值变 → 矛盾）。 -/
lemma tapeSteps_tapeAt_eq_of_head_ne {M : CBTM} {input : List F4} {π : ComputationPath}
    {cfg : CBTMConfig M input} {i : ℤ} {t₀ : ℕ}
    (h : TapeSteps M input (initialConfig M input) π cfg)
    (hne : ∀ t, t < t₀ → (CBTM.configAt M input π t).headPos ≠ i) :
    (CBTM.configAt M input π (min t₀ π.length)).tapeAt i = (initialConfig M input).tapeAt i := by
  induction t₀ generalizing π with
  | zero => simp [CBTM.configAt, configAtGo_zero, CBTMConfig.tapeAt, initialConfig]
  | succ t₀ ih =>
      by_cases ht : t₀ < π.length
      · have hm : min (t₀ + 1) π.length = min t₀ π.length + 1 := by omega
        rw [hm]
        have hstepm : (CBTM.configAt M input π (min t₀ π.length + 1)) =
            stepConfig (CBTM.configAt M input π (min t₀ π.length))
              (π.get ⟨min t₀ π.length, by omega⟩).result :=
          configAt_succ_stepConfig M input π (min t₀ π.length) (by omega)
        rw [hstepm]
        have hpos_ne : (CBTM.configAt M input π (min t₀ π.length)).headPos ≠ i :=
          hne (min t₀ π.length) (by omega)
        rw [stepConfig_tapeAt_ne (cfg := (CBTM.configAt M input π (min t₀ π.length)))
          (r := (π.get ⟨min t₀ π.length, by omega⟩).result) hpos_ne.symm]
        have hne' : ∀ t, t < t₀ → (CBTM.configAt M input π t).headPos ≠ i := by
          intro t ht'
          exact hne t (by omega)
        exact ih h hne'
      · -- min (t₀+1) π.length = π.length = min t₀ π.length（t₀ ≥ π.length）
        have hm' : min (t₀ + 1) π.length = min t₀ π.length := by omega
        rw [hm']
        have hne' : ∀ t, t < t₀ → (CBTM.configAt M input π t).headPos ≠ i := by
          intro t ht'
          exact hne t (by omega)
        exact ih h hne'

/-- TapeSteps 的末端格局恰为 configAt 的末端格局（初始磁带修复后两者一致）。 -/
lemma tapeSteps_cfg_eq_configAt {M : CBTM} {input : List F4} {π : ComputationPath}
    {cfg : CBTMConfig M input}
    (h : TapeSteps M input (initialConfig M input) π cfg) :
    cfg = CBTM.configAt M input π π.length := by
  let P (π' : ComputationPath) (cfg' : CBTMConfig M input) : Prop :=
    cfg' = CBTM.configAt M input π' π'.length
  change P π cfg
  induction h with
  | nil => rfl
  | cons π₀ step cfg₀ h_ind h_from h_read h_trans ih =>
      rw [ih]
      change stepConfig (CBTM.configAt M input π₀ π₀.length) step.result =
        CBTM.configAt M input (π₀ ++ [step]) (List.length (π₀ ++ [step]))
      rw [show List.length (π₀ ++ [step]) = π₀.length + 1 by simp]
      rw [configAt_succ_stepConfig M input (π₀ ++ [step]) π₀.length (by simp)]
      rw [configAt_append_left π₀ step (by omega)]
      rw [show (π₀ ++ [step]).get ⟨π₀.length, by simp⟩ = step by
        simp [List.getElem_append_right, List.getElem_cons_zero]]

/-- 第 t 步读的符号 = 第 t 步格局带头处的符号。 -/
lemma tapeSteps_readSym_at {M : CBTM} {input : List F4} {π : ComputationPath}
    {cfg : CBTMConfig M input}
    (h : TapeSteps M input (initialConfig M input) π cfg)
    (t : ℕ) (ht : t < π.length) :
    (π.get ⟨t, ht⟩).readSym =
      (CBTM.configAt M input π t).tapeAt (CBTM.configAt M input π t).headPos := by
  let P (π' : ComputationPath) (cfg' : CBTMConfig M input) : Prop :=
    ∀ t (ht : t < π'.length), (π'.get ⟨t, ht⟩).readSym =
      (CBTM.configAt M input π' t).tapeAt (CBTM.configAt M input π' t).headPos
  revert t ht
  change P π cfg
  induction h with
  | nil => intro t ht; simp at ht
  | cons π₀ step cfg₀ h_ind h_from h_read h_trans ih =>
      intro t ht
      by_cases hte : t = π₀.length
      · subst t
        have hget : ((π₀ ++ [step]).get ⟨π₀.length, by simp⟩) = step := by
          simp [List.getElem_append_right, List.getElem_cons_zero]
        rw [hget, h_read]
        have hcfg : cfg₀ = CBTM.configAt M input (π₀ ++ [step]) π₀.length := by
          have h1 : cfg₀ = CBTM.configAt M input π₀ π₀.length := tapeSteps_cfg_eq_configAt h_ind
          rw [h1]
          rw [configAt_append_left π₀ step (by omega)]
        rw [hcfg]
      · have ht₀ : t < π₀.length := by
          simp [List.length_append] at ht
          omega
        have hget : ((π₀ ++ [step]).get ⟨t, by simp; omega⟩) = π₀.get ⟨t, ht₀⟩ := by
          exact List.getElem_append_left (α := TransitionStep) (as := π₀) (bs := [step])
            (i := t) ht₀
        rw [hget]
        rw [ih t ht₀]
        have hpre : (π₀ ++ [step]).take t = π₀.take t := by
          rw [List.take_append_of_le_length (by exact Nat.le_of_lt ht₀)]
        simpa only [configAt_eq_of_take_eq (M := M) (input := input) (t := t) hpre]

/-- 激活索引列表的元素都 ≥ start（1-based 起点的单调性）。 -/
lemma not_mem_activatedGenIndicesOnPathAux_lt (π : ComputationPath) (start idx : ℕ)
    (hlt : idx < start) : idx ∉ activatedGenIndicesOnPathAux π start := by
  induction π generalizing start idx with
  | nil => simp [activatedGenIndicesOnPathAux]
  | cons step rest ih =>
      unfold activatedGenIndicesOnPathAux
      by_cases him : step.readSym.im = true
      · rw [if_pos him]
        rw [List.mem_cons]
        intro h
        rcases h with h | h
        · subst h
          omega
        · exact (ih (start + 1) idx (Nat.lt_trans hlt (Nat.lt_succ_self start))) h
      · rw [if_neg him]
        exact ih (start + 1) idx (Nat.lt_trans hlt (Nat.lt_succ_self start))

/-- 激活索引列表（1-based）的成员：start + idx ∈ 列表 ⟺ 第 idx 步读符号虚部为 true。 -/
lemma mem_activatedGenIndicesOnPathAux (π : ComputationPath) (start idx : ℕ)
    (hidx : idx < π.length) :
    start + idx ∈ activatedGenIndicesOnPathAux π start ↔
      F4.im ((π.getD idx Inhabited.default).readSym) = true := by
  induction π generalizing start idx with
  | nil => simp at hidx
  | cons step rest ih =>
      by_cases hidx0 : idx = 0
      · subst idx
        unfold activatedGenIndicesOnPathAux
        by_cases him : step.readSym.im = true
        · simp [him, List.getD_cons_zero]
        · rw [if_neg him, List.getD_cons_zero]
          have hnot : step.readSym.im = true ↔ False := by
            constructor
            · intro h; exact him h
            · intro h; cases h
          rw [hnot, iff_false]
          intro h
          apply (not_mem_activatedGenIndicesOnPathAux_lt rest (start + 1) start
            (Nat.lt_succ_self start))
          simpa using h
      · rcases idx with _ | k
        · contradiction
        · have hk : k < rest.length := by simp at hidx; exact hidx
          have := ih (start := start + 1) (idx := k) hk
          unfold activatedGenIndicesOnPathAux
          by_cases him : step.readSym.im = true
          · simp [him, hidx0, List.getD_cons_succ]
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
          · simp [him, hidx0, List.getD_cons_succ]
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

-- range 的 cons 分解（尾元素版 range_succ 与 w 的 cons 结构不对齐，需此形式）
lemma range_cons_succ (n : ℕ) : List.range (n + 1) = 0 :: (List.range n).map (fun i => i + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ]
      conv_lhs => rw [ih]
      rw [List.cons_append]
      rw [List.range_succ, List.map_append, List.map_singleton]
      first | done | rfl

/-- range 索引 filter 计数 = 列表 filter 计数（core 无 List.enum 的替代）。 -/
lemma length_filter_map_add (l : List ℕ) (p : ℕ → Bool) :
    ((l.map (fun i => i + 1)).filter p).length = (l.filter (fun i => p (i + 1))).length := by
  rw [List.filter_map, List.length_map]
  rfl

lemma length_filter_range_getD (w : List F4) :
    ((List.range w.length).filter (fun i => F4.im (w.getD i F4.zero) = true)).length =
      (w.filter (fun s : F4 => F4.im s)).length := by
  induction w with
  | nil => simp
  | cons s rest ih =>
      rw [List.length_cons, range_cons_succ]
      rw [List.filter_cons, List.getD_cons_zero]
      by_cases him : F4.im s
      · rw [if_pos (by simpa using him)]
        simp only [him, List.filter_cons]
        simp only [List.length_cons]
        rw [length_filter_map_add]
        simp only [List.getD_cons_succ]
        rw [ih]
        first | done | rfl
      · rw [if_neg (by intro h; exact him (of_decide_eq_true h))]
        simp only [him, List.filter_cons]
        rw [length_filter_map_add]
        simp only [List.getD_cons_succ]
        rw [ih]
        first | done | rfl

/-- 正确机器的接受路径必读每个激活位（enc 内）：反证翻转未读位的实部 → 编码失效 → 语言改变 → 矛盾。 -/
lemma accepting_path_reads_all_activated (M : CBTM) (inst : SubsetSumInstance) (gS : List Sym)
    (hcorrect : ∀ w', IsSymbolAligned w' → (M.tapeAccepts w' ↔ subsetSumLanguageF4Real w'))
    {π : ComputationPath} {cfg : CBTMConfig M (encodeInstanceF4 inst ++ flat4F4 gS)}
    (hπ : TapeReachablePath M (encodeInstanceF4 inst ++ flat4F4 gS) π cfg) (hacc : cfg.state ∈ M.acceptStates) :
    ∀ i, i < (encodeInstanceF4 inst).length → F4.im ((encodeInstanceF4 inst).getD i F4.zero) = true →
      ∃ t, t < π.length ∧ (CBTM.configAt M (encodeInstanceF4 inst ++ flat4F4 gS) π t).headPos = (i : ℤ) := by
  intro i hi him
  by_contra hnot
  have hskip : ∀ t, t < π.length →
      (CBTM.configAt M (encodeInstanceF4 inst ++ flat4F4 gS) π t).headPos ≠ (i : ℤ) := by
    intro t ht hpos
    exact hnot ⟨t, ht, hpos⟩
  let w' : List F4 := flipReAt (encodeInstanceF4 inst ++ flat4F4 gS) i
  have hinit : ∀ j : ℤ, j ≠ (i : ℤ) →
      (initialConfig M (encodeInstanceF4 inst ++ flat4F4 gS)).tapeAt j = (initialConfig M w').tapeAt j := by
    intro j hj
    have hF4 : initialTapeOf (encodeInstanceF4 inst ++ flat4F4 gS) M.blankSym j =
        initialTapeOf w' M.blankSym j := by
      unfold initialTapeOf
      by_cases hj' : 0 ≤ j ∧ j.toNat < (encodeInstanceF4 inst ++ flat4F4 gS).length
      · rw [dif_pos hj']
        have hj'' : 0 ≤ j ∧ j.toNat < w'.length := by
          rcases hj' with ⟨h0, hlt⟩
          exact ⟨h0, by rw [flipReAt_length]; exact hlt⟩
        rw [dif_pos hj'']
        have hne : j.toNat ≠ i := by
          intro h
          exact hj (by
            cases j with
            | ofNat n => subst h; rfl
            | negSucc n => omega)
        rw [flipReAt_get_ne (encodeInstanceF4 inst ++ flat4F4 gS) i j.toNat hne hj'.2]
      · rw [dif_neg hj']
        rw [dif_neg (by
          intro h
          apply hj'
          exact ⟨h.1, by rw [← flipReAt_length]; exact h.2⟩)]
    simp [CBTMConfig.tapeAt]
    exact hF4
  have hacc'' : M.tapeAccepts w' := by
    exact tapeAccepts_insensitive_to_unread_update hπ hacc hinit hskip
  have hL' : subsetSumLanguageF4Real w' := by
    have ha : IsSymbolAligned w' := by
      simpa [w'] using flipReAt_activated_aligned inst gS i hi him
    have hcorr : M.tapeAccepts w' ↔ subsetSumLanguageF4Real w' := hcorrect w' ha
    exact hcorr.1 hacc''
  exact flipReAt_activated_not_in_L inst gS i hi him hL'

set_option maxHeartbeats 4000000 in
lemma activated_ge_imTrueCount_of_reads_all {M : CBTM} {w : List F4} {inst : SubsetSumInstance}
    (gS : List Sym) {π : ComputationPath} {cfg : CBTMConfig M w}
    (henc : w = encodeInstanceF4 inst ++ flat4F4 gS)
    (hreach : TapeReachablePath M w π cfg)
    (hreads : ∀ i, i < (encodeInstanceF4 inst).length → F4.im ((encodeInstanceF4 inst).getD i F4.zero) = true →
      ∃ t, t < π.length ∧ (CBTM.configAt M w π t).headPos = (i : ℤ)) :
    (activatedGenSetOnPath π).card ≥ imTrueCount (encodeInstanceF4 inst) := by
  classical
  have hsteps : TapeSteps M w (initialConfig M w) π cfg :=
    (tapeSteps_initial_iff M w π cfg).2 hreach
  -- 激活位索引列表（i < |enc| 且 im=true），按 range 排列（core 无 List.enum）
  let wf : List (ℕ × F4) := ((List.range (encodeInstanceF4 inst).length).filter
    (fun i => F4.im ((encodeInstanceF4 inst).getD i F4.zero) = true)).map
    (fun i => (i, (encodeInstanceF4 inst).getD i F4.zero))
  have hmain : ∀ p, p ∈ wf → p.1 < (encodeInstanceF4 inst).length ∧
      p.2 = (encodeInstanceF4 inst).getD p.1 F4.zero ∧
      F4.im ((encodeInstanceF4 inst).getD p.1 F4.zero) = true := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨i, hif, hpi⟩
    rw [← hpi]
    exact ⟨List.mem_range.mp (List.mem_filter.mp hif).1, rfl,
      of_decide_eq_true (List.mem_filter.mp hif).2⟩
  let ts : List ℕ := wf.attach.map (fun ⟨p, hp⟩ => Nat.find
    (hreads p.1 (hmain p hp).1 (hmain p hp).2.2))
  have hlen : ts.length = imTrueCount (encodeInstanceF4 inst) := by
    unfold ts wf imTrueCount
    rw [List.length_map, List.length_attach, List.length_map]
    exact length_filter_range_getD (encodeInstanceF4 inst)
  -- 每个 t_i 是激活步（0-based t < π.length 且 readSym.im = true）
  have ht_active : ∀ t ∈ ts, t < π.length ∧
      F4.im ((π.getD t Inhabited.default).readSym) = true := by
    intro t ht
    rcases List.mem_map.mp ht with ⟨⟨p, hp⟩, _hpe, rfl⟩
    let P : ℕ → Prop := fun t => t < π.length ∧ (CBTM.configAt M w π t).headPos = (p.1 : ℤ)
    let t₀ : ℕ := Nat.find (p := P) (hreads p.1 (hmain p hp).1 (hmain p hp).2.2)
    have hP : P t₀ := by
      exact Nat.find_spec _
    have htlt : t₀ < π.length := hP.1
    have hpos : (CBTM.configAt M w π t₀).headPos = (p.1 : ℤ) := hP.2
    constructor
    · exact htlt
    · have hfirst : ∀ t, t < t₀ → (CBTM.configAt M w π t).headPos ≠ (p.1 : ℤ) := by
        intro u hu hpos'
        exact (Nat.find_min (H := hreads p.1 (hmain p hp).1 (hmain p hp).2.2) (m := u) hu)
          (And.intro (by omega) hpos')
      have htape : (CBTM.configAt M w π (min t₀ π.length)).tapeAt (p.1 : ℤ) =
          (initialConfig M w).tapeAt (p.1 : ℤ) :=
        tapeSteps_tapeAt_eq_of_head_ne (h := hsteps) (i := (p.1 : ℤ)) (t₀ := t₀) hfirst
      have hm : min t₀ π.length = t₀ := by omega
      have hread : ((π.getD t₀ Inhabited.default).readSym) =
          (CBTM.configAt M w π t₀).tapeAt (p.1 : ℤ) := by
        have hread' := tapeSteps_readSym_at (M := M) (input := w) (h := hsteps) (t := t₀) htlt
        rw [hpos] at hread'
        rw [getD_eq_get π t₀ Inhabited.default htlt]
        exact hread'
      have hw_lt : p.1 < w.length := by
        rw [henc]
        simp only [List.length_append]
        exact Nat.lt_of_lt_of_le (hmain p hp).1 (Nat.le_add_right _ _)
      have htape' : (CBTM.configAt M w π t₀).tapeAt (p.1 : ℤ) =
          w.getD p.1 F4.zero := by
        rw [hm] at htape
        rw [htape]
        have htapeInit : (initialConfig M w).tapeAt (p.1 : ℤ) = w.get ⟨p.1, hw_lt⟩ := by
          change ((initialConfig M w).tape (p.1 : ℤ) : F4) = w.get ⟨p.1, hw_lt⟩
          have hget : initialTapeOf w M.blankSym (p.1 : ℤ) = w.get ⟨p.1, hw_lt⟩ := by
            unfold initialTapeOf
            have hpp : 0 ≤ (p.1 : ℤ) ∧ ((p.1 : ℤ).toNat) < w.length := ⟨by omega, hw_lt⟩
            rw [dif_pos hpp]
            simpa
          congr
        rw [htapeInit]
        simpa using (getD_eq_get w p.1 F4.zero hw_lt).symm
      rw [hread, htape']
      change F4.im (w.getD p.1 F4.zero) = true
      rw [henc]
      rw [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (hmain p hp).1]
      rw [← List.getD_eq_getElem?_getD]
      simpa [F4.im] using (hmain p hp).2.2
  -- ts 无重复（t_p 两两不同：一步只读一格）
  have hwfNodup : wf.Nodup := by
    unfold wf
    exact List.Nodup.map (l := (List.range (encodeInstanceF4 inst).length).filter
        (fun i => F4.im ((encodeInstanceF4 inst).getD i F4.zero) = true))
      (f := fun i => (i, (encodeInstanceF4 inst).getD i F4.zero))
      (by intro a b heq; exact congrArg Prod.fst heq)
      (List.Nodup.filter (fun i => F4.im ((encodeInstanceF4 inst).getD i F4.zero) = true) (by
        have hrange : (List.range (encodeInstanceF4 inst).length).Nodup := by
          induction (encodeInstanceF4 inst).length with
          | zero => simp
          | succ n ih =>
              rw [List.range_succ, List.nodup_append]
              constructor
              · exact ih
              constructor
              · exact (List.nodup_singleton n)
              · intro a ha b hb
                rw [List.mem_singleton] at hb
                have : a < n := List.mem_range.mp ha
                omega
        exact hrange))
  have hinj : Function.Injective (fun x : {x : ℕ × F4 // x ∈ wf} =>
      (Nat.find (hreads x.1.1 (hmain x.1 x.2).1 (hmain x.1 x.2).2.2) : ℕ)) := by
    intro a₁ a₂ heq
    apply Subtype.ext
    have hposP : (CBTM.configAt M w π (Nat.find _)).headPos = (a₁.1.1 : ℤ) :=
      (Nat.find_spec (hreads a₁.1.1 (hmain a₁.1 a₁.2).1 (hmain a₁.1 a₁.2).2.2)).2
    have hposQ : (CBTM.configAt M w π
        (Nat.find (hreads a₂.1.1 (hmain a₂.1 a₂.2).1 (hmain a₂.1 a₂.2).2.2))).headPos =
        (a₂.1.1 : ℤ) :=
      (Nat.find_spec (hreads a₂.1.1 (hmain a₂.1 a₂.2).1 (hmain a₂.1 a₂.2).2.2)).2
    have hp1 : a₁.1.1 = a₂.1.1 := by
      have hhp : (CBTM.configAt M w π
          (Nat.find (hreads a₁.1.1 (hmain a₁.1 a₁.2).1 (hmain a₁.1 a₁.2).2.2))).headPos =
        (CBTM.configAt M w π
          (Nat.find (hreads a₂.1.1 (hmain a₂.1 a₂.2).1 (hmain a₂.1 a₂.2).2.2))).headPos :=
        congrArg (fun t => (CBTM.configAt M w π t).headPos) heq
      apply Int.ofNat_inj.mp
      rw [← hposP, ← hposQ]
      exact hhp
    apply Prod.ext
    · exact hp1
    · have hp2 := (hmain a₁.1 a₁.2).2.1
      have hq2 := (hmain a₂.1 a₂.2).2.1
      rw [hp2, hq2, hp1]
  have hnodup : ts.Nodup := by
    unfold ts
    exact List.Nodup.map (l := wf.attach)
      (f := fun ⟨p, hp⟩ => (Nat.find (hreads p.1 (hmain p hp).1 (hmain p hp).2.2) : ℕ))
      hinj ((List.nodup_attach).2 hwfNodup)
  -- 每个激活步 t（0-based）→ 1-based t+1 ∈ 激活索引列表
  have hto : ∀ t ∈ ts, t + 1 ∈ activatedGenIndicesOnPath π := by
    intro t ht
    rcases ht_active t ht with ⟨htlt, him⟩
    rw [activatedGenIndicesOnPath]
    simpa [Nat.add_comm] using (mem_activatedGenIndicesOnPathAux π 1 t htlt).2 him
  have hcard_ts : ts.length ≤ (activatedGenSetOnPath π).card := by
    have hnd : (ts.map (fun t => t + 1)).Nodup := by
      rw [List.nodup_map_iff_inj_on (l := ts) (f := fun t => t + 1)]
      · intro a _ha b _hb heq
        omega
      · exact hnodup
    have htof : (ts.map (fun t => t + 1)).toFinset ⊆ (activatedGenIndicesOnPath π).toFinset := by
      intro x hx
      rw [List.mem_toFinset] at hx ⊢
      rcases List.mem_map.mp hx with ⟨t, ht, rfl⟩
      exact hto t ht
    have hcardle : (ts.map (fun t => t + 1)).toFinset.card ≤
        (activatedGenIndicesOnPath π).toFinset.card :=
      Finset.card_le_card htof
    have hcard1 : (ts.map (fun t => t + 1)).toFinset.card =
        (ts.map (fun t => t + 1)).length := by
      rw [List.toFinset_card_of_nodup hnd]
    rw [activatedGenSetOnPath]
    rw [hcard1, List.length_map] at hcardle
    exact hcardle
  rw [← hlen]
  exact hcard_ts


/-- kappa_M 下界（磁带语义）：正确机器的 κ ≥ 虚部 true 符号数。 -/
lemma kappa_M_ge_imTrueCount (M : CBTM) (inst : SubsetSumInstance) (w : List F4)
    (hw : ∃ gS, w = encodeInstanceF4 inst ++ flat4F4 gS)
    (hholds : subsetSumHolds inst) (hne : inst.elements ≠ [])
    (hpos : ∀ v ∈ inst.elements, 0 < v) (htgt : 0 < inst.target)
    (hcorrect : ∀ w', IsSymbolAligned w' → (M.tapeAccepts w' ↔ subsetSumLanguageF4Real w')) :
    kappa_M M w ≥ imTrueCount (encodeInstanceF4 inst) := by
  rcases hw with ⟨gS, henc⟩
  subst w
  by_cases h_exists : ∃ π, ∃ cfg : CBTMConfig M (encodeInstanceF4 inst ++ flat4F4 gS),
      TapeReachablePath M (encodeInstanceF4 inst ++ flat4F4 gS) π cfg ∧ cfg.state ∈ M.acceptStates
  · rcases kappa_M_spec M (encodeInstanceF4 inst ++ flat4F4 gS) h_exists with ⟨π, cfg, hr, ha, hcard⟩
    rw [← hcard]
    exact activated_ge_imTrueCount_of_reads_all gS rfl hr
      (accepting_path_reads_all_activated M inst gS hcorrect hr ha)
  · exfalso
    have hacc : M.tapeAccepts (encodeInstanceF4 inst ++ flat4F4 gS) :=
      have haligned : IsSymbolAligned (encodeInstanceF4 inst ++ flat4F4 gS) := by
        refine ⟨encodeInstanceSym inst ++ gS, ?_⟩
        dsimp [encodeInstanceF4, flat4F4]
        rw [List.flatMap_append]
      have hcorr : M.tapeAccepts (encodeInstanceF4 inst ++ flat4F4 gS) ↔
          subsetSumLanguageF4Real (encodeInstanceF4 inst ++ flat4F4 gS) :=
        hcorrect (encodeInstanceF4 inst ++ flat4F4 gS) haligned
      hcorr.2 ⟨inst, gS, rfl, hne, hpos, htgt, hholds⟩
    rcases hacc with ⟨π, cfg, hr, ha⟩
    exact h_exists ⟨π, cfg, hr, ha⟩

-- ============================================================================
-- 点态下界（论文 thm:subset-sum-lower 的核心）：对任意正确验证器 M 与任意
-- YES 实例 inst，kappa_M M (encode inst) ≥ 元素个数。
-- ============================================================================

theorem subsetSum_kappa_lower_bound (M : CBTM) (inst : SubsetSumInstance)
    (hholds : subsetSumHolds inst) (hne : inst.elements ≠ [])
    (hpos : ∀ v ∈ inst.elements, 0 < v) (htgt : 0 < inst.target)
    (hM : ∀ w, IsSymbolAligned w → (M.tapeAccepts w ↔ subsetSumLanguageF4Real w)) :
    kappa_M M (encodeInstanceF4 inst) ≥ inst.elements.length := by
  have hge := kappa_M_ge_imTrueCount M inst (encodeInstanceF4 inst) ⟨[], by simp [flat4F4]⟩
    hholds hne hpos htgt hM
  rw [imTrueCount_encodeInstanceF4 inst] at hge
  exact hge

-- ============================================================================
-- 子集和 ∉ P（F4 版本）：restricted 验证器 κ 恒 0，但点态下界 κ ≥ 1。
-- ============================================================================

theorem subsetSum_not_in_P_F :
    ¬ (∃ M, CBTM.IsRestricted M ∧ CBTM.isPolynomialTimeAligned M ∧
      (∀ w : List F4, IsSymbolAligned w → (M.tapeAccepts w ↔ subsetSumLanguageF4Real w))) := by
  intro h
  rcases h with ⟨M, hrest, _hpoly, hcorrect⟩
  let inst : SubsetSumInstance := { elements := [1], target := 1 }
  have h_lower : kappa_M M (encodeInstanceF4 inst) ≥ 1 := by
    have hk := subsetSum_kappa_lower_bound M inst
      (⟨[true], by simp [inst], by simp [inst, selectedSum]⟩ : subsetSumHolds inst)
      (by simp [inst]) (by intro v hv; simp [inst] at hv; omega)
      (by norm_num [inst]) (fun w hw => hcorrect w hw)
    simpa [inst] using hk
  have h_zero : kappa_M M (encodeInstanceF4 inst) = 0 :=
    kappa_zero_of_restricted_total M (encodeInstanceF4 inst) hrest
  rw [h_zero] at h_lower
  omega

-- ============================================================================
-- F4 版本的复杂度类 P_F / NP_F
-- ============================================================================

/-- F4 语言的多项式时间确定性类（restricted CBTM 判定，磁带语义；
    判定域 = 符号对齐串（4F4 计算符号串），半块/非法 padding 串不是输入（不在语言定义域内）；
    多项式界同样只在输入域内要求（isPolynomialTimeAligned，2026-09-09 用户裁决）。 -/
def IsP_F (L : FLanguage) : Prop :=
  ∃ M, CBTM.IsRestricted M ∧ CBTM.isPolynomialTimeAligned M ∧
    (∀ w, IsSymbolAligned w → (M.tapeAccepts w ↔ L w))

/-- F4 语言的多项式时间非确定性类（磁带语义；判定域 = 符号对齐串）。 -/
def IsNP_F (L : FLanguage) : Prop :=
  ∃ M, CBTM.isPolynomialTimeAligned M ∧ (∀ w, IsSymbolAligned w → (M.tapeAccepts w ↔ L w))

def P_F : Set FLanguage := { L | IsP_F L }
def NP_F : Set FLanguage := { L | IsNP_F L }

-- 子集和 ∉ P_F
theorem subsetSum_not_in_P_F' : ¬ IsP_F subsetSumLanguageF4Real :=
  subsetSum_not_in_P_F

-- 注：subsetSum_in_NP_F 已由 Mp.SubsetSumInNP 定理化（见证 = subsetSumCBTM，
-- NTM2 ≅ CBTM 同构的编译像）；P_F_neq_NP_F 相应移至 Mp.FinalProof。

end Mp
