/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import Mp.ATMBasic

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

/-!
# Mp.ATMBridge —— 符号层 ↔ bit 层转换与桥

- **bit 转换**：直读位对即 2bit 码——`codeBits s = [F4.re s, F4.im s]`；
  0↦00、1↦10、sep↦01、#↦11；`toBits`/`ofBits` 互逆，长度 ×2。
- **确定性（DTM）单卡事实**：DTM 转移结果唯一 ⇒ 对应 CBTM 结果集恒单元素（card = 1）——
  为 DTM≅CBTM0 桥与 κ 传递备料（接口见 design 纸面件 §6；带外写 alpha、blank=alpha 已裁）。
- **DTM 侧 F4 口径（用户裁决）**：F4 按 `Bool × Bool` 理解——机器只读一对 bit，不带虚部语义。
- **CBTM 侧口径（用户裁决）**：F4 = bool（数据）＋虚部；就输入数据而言只占 1 个 bit。
- **DTM≅CBTM0 同构条件（用户裁决）**：取实部（数据）+虚部全 0 —— 同构在「虚部=0 层」上。
- 时间计量 = 格子移动数（`dtmMoveCount`/`ntm2MoveCount`，见 ATMBasic）。
-/

namespace Mp

-- ============================================================================
-- §1 bit 转换（直读位对 = 2bit 码；长度 ×2）
-- ============================================================================

/-- 2bit 码：直读位对 (re, im)。0↦00、1↦10、sep↦01、#↦11。 -/
def codeBits (s : F4) : List Bool := [F4.re s, F4.im s]

/-- 码长恒 2。 -/
theorem codeBits_length (s : F4) : (codeBits s).length = 2 := rfl

/-- 符号串 → bit 串（逐符号 2bit）。 -/
def toBits : List F4 → List Bool
  | [] => []
  | s :: t => codeBits s ++ toBits t

/-- cons 展开。 -/
theorem toBits_cons (s : F4) (t : List F4) : toBits (s :: t) = codeBits s ++ toBits t := rfl

/-- bit 串 → 符号串（2bit 配对；奇尾补一位 false——偶长为主定理域，奇长按此约定）。 -/
def ofBits : List Bool → List F4
  | [] => []
  | b :: [] => [(b, false)]
  | b₁ :: b₂ :: rest => (b₁, b₂) :: ofBits rest

/-- 编码长度 ×2。 -/
theorem toBits_length (x : List F4) : (toBits x).length = 2 * x.length := by
  induction x with
  | nil => rfl
  | cons s t ih =>
    rw [toBits_cons, List.length_append, ih, codeBits_length, List.length_cons]
    ring

/-- 互逆（符号 → bit → 符号）。 -/
theorem ofBits_toBits (x : List F4) : ofBits (toBits x) = x := by
  induction x with
  | nil => rfl
  | cons s t ih =>
    obtain ⟨r, i⟩ := s
    cases r <;> cases i <;> simp [toBits_cons, codeBits, ofBits, ih]

-- ============================================================================
-- §2 DTM 确定性单卡（为 DTM≅CBTM0 桥备料）
-- ============================================================================

/-- DTM 转移结果 → CBTM 转移结果（同名翻译）。 -/
def dtmResultToCBTM (r : ClassicDTMTransitionResult) : CBTMTransResult :=
  { nextState := r.nextState, writeSym := r.writeSym, moveDir := r.move }

/-- DTM 的转移集（单元素；确定性 ⇒ 无分支）。 -/
def dtmTransitionSet (M : ClassicDTM) (q : ℕ) (s : F4) : Finset CBTMTransResult :=
  {dtmResultToCBTM (M.transition (q, s))}

/-- 单卡：DTM 的转移集基数恒 1。 -/
theorem dtmTransitionSet_card_one (M : ClassicDTM) (q : ℕ) (s : F4) :
    (dtmTransitionSet M q s).card = 1 :=
  Finset.card_singleton _

/-- DTM 一步记录 → CBTM 一步（结果翻译）。 -/
def dtmStepToCBTM (st : DTMTransitionStep) : TransitionStep :=
  { fromState := st.fromState, readSym := st.readSym, result := dtmResultToCBTM st.result }

-- ============================================================================
-- §3 DTM ≅ CBTM0 语法同构（移植自旧工程 PvsNP/CBTM.lean:209-420，适配 mp 形状）
-- ============================================================================

/-- DTM 转移函数的 CBTM0 投影：在 {zero, one} 上单元素像，其余为空
（分支规则相容：像字母表 = {zero, one}）。 -/
def ClassicDTM.toCBTMTrans (M : ClassicDTM) : ℕ × F4 × ℤ → Finset CBTMTransResult :=
  fun (q, s, _) =>
    if s ∈ ({F4.zero, F4.one} : Finset F4) then
      {dtmResultToCBTM (M.transition (q, s))}
    else
      ∅

@[simp] theorem ClassicDTM.toCBTMTrans_zero (M : ClassicDTM) (q : ℕ) (i : ℤ) :
    M.toCBTMTrans (q, F4.zero, i) = {dtmResultToCBTM (M.transition (q, F4.zero))} := by
  simp only [ClassicDTM.toCBTMTrans]
  rw [if_pos (by simp)]

@[simp] theorem ClassicDTM.toCBTMTrans_one (M : ClassicDTM) (q : ℕ) (i : ℤ) :
    M.toCBTMTrans (q, F4.one, i) = {dtmResultToCBTM (M.transition (q, F4.one))} := by
  simp only [ClassicDTM.toCBTMTrans]
  rw [if_pos (by simp)]

/-- DTM → CBTM0。 数据闭合前提（写符号虚部恒 false）供投影约束用；
    空白取 F4.zero（像侧字母表 = {zero, one}，虚部＝0 层）。 -/
def ClassicDTM.toCBTM (M : ClassicDTM)
    (hwrite : ∀ q s, F4.im (M.transition (q, s)).writeSym = false) : CBTM :=
  { states := M.states
    startState := M.startState
    acceptStates := M.acceptStates
    rejectStates := M.rejectStates
    alphabet := {F4.zero, F4.one}
    transition := M.toCBTMTrans
    blankSym := F4.zero
    h_blank_in_alphabet := by simp
    h_start_in_states := M.h_start_in_states
    h_accept_subset := M.h_accept_subset
    h_reject_subset := M.h_reject_subset
    h_accept_reject_disjoint := M.h_accept_reject_disjoint
    h_branch_rule := by
      intro q s i hs
      have hcases : s = F4.zero ∨ s = F4.one := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hs
      rcases hcases with rfl | rfl <;>
        · simp [ClassicDTM.toCBTMTrans, F4.im, F4.zero, F4.one]
    h_projection_constraint := by
      intro q s i hs him
      have hcases : s = F4.zero ∨ s = F4.one := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hs
      rcases hcases with rfl | rfl
      · constructor
        · rw [ClassicDTM.toCBTMTrans_zero]
          exact Finset.card_singleton _
        · intro r hr
          rw [ClassicDTM.toCBTMTrans_zero] at hr
          rw [Finset.mem_singleton] at hr
          subst hr
          simpa [dtmResultToCBTM] using hwrite q F4.zero
      · constructor
        · rw [ClassicDTM.toCBTMTrans_one]
          exact Finset.card_singleton _
        · intro r hr
          rw [ClassicDTM.toCBTMTrans_one] at hr
          rw [Finset.mem_singleton] at hr
          subst hr
          simpa [dtmResultToCBTM] using hwrite q F4.one
    isValid := by
      intro q s i hs r hr
      have hcases : s = F4.zero ∨ s = F4.one := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hs
      rcases hcases with rfl | rfl
      · rw [ClassicDTM.toCBTMTrans_zero] at hr
        rw [Finset.mem_singleton] at hr
        subst hr
        simpa [dtmResultToCBTM] using M.isValid q F4.zero
      · rw [ClassicDTM.toCBTMTrans_one] at hr
        rw [Finset.mem_singleton] at hr
        subst hr
        simpa [dtmResultToCBTM] using M.isValid q F4.one
    h_transition_outside := by
      intro q s i hs
      simp only [ClassicDTM.toCBTMTrans]
      exact if_neg hs }

/-- 语法结构同构（DTM ↔ CBTM0）：状态集一致、转移在 {zero, one} 层逐点单元素对应。 -/
structure StructIsoClassicDTM (M : ClassicDTM) (N : CBTM) : Type where
  h_restricted : CBTM.IsRestricted N
  h_states_eq : M.states = N.states
  h_start : M.startState = N.startState
  h_accept : N.acceptStates = M.acceptStates
  h_reject : N.rejectStates = M.rejectStates
  h_transition : ∀ (q : ℕ) (s : F4), s ∈ ({F4.zero, F4.one} : Finset F4) → ∀ i : ℤ,
    N.transition (q, s, i) = {dtmResultToCBTM (M.transition (q, s))}

/-- 存在性：每个数据闭合 DTM 都同构于某个受限 CBTM。 -/
theorem exists_CBTM0_iso_DTM (M : ClassicDTM)
    (hwrite : ∀ q s, F4.im (M.transition (q, s)).writeSym = false) :
    ∃ (N : CBTM), Nonempty (StructIsoClassicDTM M N) := by
  let N := M.toCBTM hwrite
  have hmem {s : F4} (hs : s ∈ ({F4.zero, F4.one} : Finset F4)) :
      s = F4.zero ∨ s = F4.one := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hs
  have hcard : ∀ q s i, s ∈ N.alphabet → (N.transition (q, s, i)).card = 1 := by
    intro q s i hs
    rcases hmem (by simpa [N, ClassicDTM.toCBTM] using hs) with rfl | rfl
    · rw [show N.transition (q, F4.zero, i) = {dtmResultToCBTM (M.transition (q, F4.zero))} from by
          simp [N, ClassicDTM.toCBTM]]
      exact Finset.card_singleton _
    · rw [show N.transition (q, F4.one, i) = {dtmResultToCBTM (M.transition (q, F4.one))} from by
          simp [N, ClassicDTM.toCBTM]]
      exact Finset.card_singleton _
  have hrest : CBTM.IsRestricted N := by
    refine ⟨?_, ?_, hcard, ?_⟩
    · intro s hs
      rcases hmem (by simpa [N, ClassicDTM.toCBTM] using hs) with rfl | rfl <;> simp
    · intro s hs
      rcases hmem (by simpa [N, ClassicDTM.toCBTM] using hs) with rfl | rfl <;> simp [F4.im, F4.zero, F4.one]
    · simp [N, ClassicDTM.toCBTM]
  exact ⟨N, ⟨{
    h_restricted := hrest
    h_states_eq := rfl
    h_start := rfl
    h_accept := rfl
    h_reject := rfl
    h_transition := by
      intro q s hs i
      rcases hmem hs with rfl | rfl
      · simp [N, ClassicDTM.toCBTM]
      · simp [N, ClassicDTM.toCBTM]
  }⟩⟩

-- ============================================================================
-- §4 CBTM0 类与逆方向：受限 CBTM → DTM（移植自 PvsNP/CBTM.lean:180-191,286-378,420-470）
-- ============================================================================

/-- CBTM 结果 → DTM 结果（逆翻译）。 -/
def cbtmResultToDTM (r : CBTMTransResult) : ClassicDTMTransitionResult :=
  { nextState := r.nextState, writeSym := r.writeSym, move := r.moveDir }

/-- 结果层往返：dtm → cbtm → dtm 为恒等。 -/
@[simp] theorem cbtmResultToDTM_dtmResultToCBTM (r : ClassicDTMTransitionResult) :
    cbtmResultToDTM (dtmResultToCBTM r) = r := rfl

/-- 基数 1 的有限集等于其唯一元素（choose 所取）的单元素集。
    （`card_eq_one_unique_mem` 已于 `Mp/CBTM.lean:159` 存在，直接复用。） -/
lemma eq_singleton_choose_of_card_eq_one {α : Type*} (s : Finset α) (h : s.card = 1) :
    s = {(card_eq_one_unique_mem s h).choose} := by
  classical
  rcases Finset.card_eq_one.mp h with ⟨a, ha⟩
  subst ha
  have hmem : a ∈ ({a} : Finset α) := by simp
  have hchoose : (card_eq_one_unique_mem ({a} : Finset α) h).choose = a :=
    (card_eq_one_unique_mem ({a} : Finset α) h).choose_spec.2 a hmem |>.symm
  rw [hchoose]

/-- CBTM0（受限形）：字母表 = {zero, one}，转移卡恒 1，且位置无关。 -/
structure CBTM.IsCBTM0 (M : CBTM) : Prop where
  alphabet_eq : M.alphabet = {F4.zero, F4.one}
  card_one : ∀ q s i, s ∈ M.alphabet → (M.transition (q, s, i)).card = 1
  pos_indep : ∀ q s i j, s ∈ M.alphabet → M.transition (q, s, i) = M.transition (q, s, j)

/-- CBTM0 的转移投影回 DTM（位置无关，取唯一元素；
    字母表外给固定占位，不影响 {zero, one} 层对应）。 -/
noncomputable def CBTM.toClassicDTMTrans (N : CBTM) (h : CBTM.IsCBTM0 N) :
    ℕ × F4 → ClassicDTMTransitionResult :=
  fun (q, s) =>
    if hs : s ∈ N.alphabet then
      cbtmResultToDTM ((card_eq_one_unique_mem (N.transition (q, s, 0))
        (h.card_one q s 0 hs)).choose)
    else
      { nextState := N.startState, writeSym := s, move := Dir.S }

/-- CBTM0 → DTM（取 i=0 截面；pos_indep 保证对 \(i\) 一致）。 -/
noncomputable def CBTM.toClassicDTM (N : CBTM) (h : CBTM.IsCBTM0 N) : ClassicDTM :=
  { states := N.states
    startState := N.startState
    acceptStates := N.acceptStates
    rejectStates := N.rejectStates
    alphabet := {F4.zero, F4.one, F4.alpha, F4.beta}
    transition := N.toClassicDTMTrans h
    blankSym := N.blankSym
    h_start_in_states := N.h_start_in_states
    h_accept_subset := N.h_accept_subset
    h_reject_subset := N.h_reject_subset
    h_accept_reject_disjoint := N.h_accept_reject_disjoint
    isValid := by
      intro q s
      by_cases hs : s ∈ N.alphabet
      · have hspec := (card_eq_one_unique_mem (N.transition (q, s, 0))
          (h.card_one q s 0 hs)).choose_spec
        have hmem : (card_eq_one_unique_mem (N.transition (q, s, 0))
            (h.card_one q s 0 hs)).choose ∈ N.transition (q, s, 0) := hspec.1
        simpa [CBTM.toClassicDTMTrans, dif_pos hs, cbtmResultToDTM]
          using N.isValid q s 0 hs _ hmem
      · simpa [CBTM.toClassicDTMTrans, dif_neg hs] using N.h_start_in_states
    h_alphabet_all := rfl }

/-- 逆方向存在性：每个 CBTM0（+ 空白在字母表内）同构于某个 DTM。 -/
theorem exists_ClassicDTM_iso_restrictedCBTM (N : CBTM) (h : CBTM.IsCBTM0 N)
    (hblank : N.blankSym ∈ ({F4.zero, F4.one} : Finset F4)) :
    ∃ (M : ClassicDTM), Nonempty (StructIsoClassicDTM M N) := by
  have hmem {s : F4} (hs : s ∈ ({F4.zero, F4.one} : Finset F4)) :
      s = F4.zero ∨ s = F4.one := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hs
  let M := N.toClassicDTM h
  have hrest : CBTM.IsRestricted N := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s hs
      rw [h.alphabet_eq] at hs
      exact hs
    · intro s hs
      rw [h.alphabet_eq] at hs
      rcases hmem hs with rfl | rfl <;> simp [F4.im, F4.zero, F4.one]
    · intro q s i hs
      exact h.card_one q s i hs
    · simpa [h.alphabet_eq] using hblank
  refine ⟨M, ⟨{
    h_restricted := hrest
    h_states_eq := rfl
    h_start := rfl
    h_accept := rfl
    h_reject := rfl
    h_transition := by
      intro q s hs i
      rcases hmem hs with rfl | rfl
      · have hz : F4.zero ∈ N.alphabet := by
          rw [h.alphabet_eq]; simp
        have hcard := h.card_one q F4.zero 0 hz
        have hM : M.transition (q, F4.zero) =
            cbtmResultToDTM (card_eq_one_unique_mem (N.transition (q, F4.zero, 0)) hcard).choose := by
          simp only [M, CBTM.toClassicDTM, CBTM.toClassicDTMTrans, dif_pos hz]
        rw [h.pos_indep q F4.zero i 0 hz, eq_singleton_choose_of_card_eq_one _ hcard, hM]
        congr 1
      · have ho : F4.one ∈ N.alphabet := by
          rw [h.alphabet_eq]; simp
        have hcard := h.card_one q F4.one 0 ho
        have hM : M.transition (q, F4.one) =
            cbtmResultToDTM (card_eq_one_unique_mem (N.transition (q, F4.one, 0)) hcard).choose := by
          simp only [M, CBTM.toClassicDTM, CBTM.toClassicDTMTrans, dif_pos ho]
        rw [h.pos_indep q F4.one i 0 ho, eq_singleton_choose_of_card_eq_one _ hcard, hM]
        congr 1
  }⟩⟩

end Mp
