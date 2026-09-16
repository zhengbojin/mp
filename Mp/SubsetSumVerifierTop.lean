/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import Mp.SubsetSumVerifierCore2
import Mp.SubsetSumVerifierCoreA

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
# 子集和验证器顶层组装（Sym 层完整接受路径）

把 Core/Core1/CoreA/Core2 的部件组装为完整正确性：

- `sym_accept_of_holds`：合法 YES 实例（元素 > 0、target > 0、subsetSumHolds）
  的编码被 Sym 验证器接受（0 → 1 → 2(分支) → 3 → 24(格式) → 4 → 主循环 → 22 → 23 → 100）。
- 前驱引理（`prev_of_nextState_*`）：接受路径的反演基础（→ 方向）。

状态表约定（2026-08-29 定稿）：
- 最高位恒为 data1：24/26/27 读 data0 → 101（状态 25 已删除）；
- 语言约束：元素 > 0、target > 0（SubsetSumReal.subsetSumLanguageF4Real）。
-/

namespace Mp

open VerifierSym

-- ============================================================================
-- §1 判定段小引理（状态 23）
-- ============================================================================

-- ============================================================================
-- §2 SymSteps 最后一步分解（反演基础）
-- ============================================================================

/-- SymSteps 路径的最后一步分解：π = π₀ ++ [step]，step 从 cfg₁ 到 cfg。 -/
lemma last_step_of_SymSteps {M : ℕ × Sym → Finset SymTransResult} {cfg₀ : SymConfig}
    {π : List SymStep} {cfg : SymConfig} (h : SymSteps M cfg₀ π cfg) (hπ : π ≠ []) :
    ∃ (π₀ : List SymStep) (step : SymStep) (cfg₁ : SymConfig),
      π = π₀ ++ [step] ∧ SymSteps M cfg₀ π₀ cfg₁ ∧
      step.fromState = cfg₁.state ∧
      step.readSym = cfg₁.tape cfg₁.headPos ∧
      step.result ∈ M (cfg₁.state, cfg₁.tape cfg₁.headPos) ∧
      symStepConfig cfg₁ step.result = cfg := by
  induction h with
  | nil =>
      exfalso
      exact hπ rfl
  | cons π₀ step cfg' h_ind h_from h_read h_trans ih =>
      refine ⟨π₀, step, cfg', rfl, h_ind, h_from, h_read, h_trans, rfl⟩

-- ============================================================================
-- §3 前驱唯一性（反演基础）
-- ============================================================================

/-- legalStates 的状态都不超过 101。 -/
lemma legalStates_le_101 (q : ℕ) (hq : q ∈ VerifierSym.legalStates) : q ≤ 101 := by
  have hdec : ∀ q ∈ VerifierSym.legalStates, q ≤ 101 := by
    native_decide
  exact hdec q hq

/-- 转移结果 nextState = 22 的唯一前驱：21 读 boundary 写回自身停（S）。 -/
lemma prev_of_nextState_22 (q : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (hrs : r.nextState = 22) :
    q = 21 ∧ s.1 = SymKind.boundary ∧
      r.writeSym = s ∧ r.moveDir = Dir.S := by
  have hqle : q ≤ 101 := by
    by_cases hqin : q ∈ VerifierSym.legalStates
    · exact legalStates_le_101 q hqin
    · have htr : VerifierSym.transition (q, s) = {SymTransResult.mk 101 s Dir.S} := by
        unfold VerifierSym.transition
        dsimp
        rw [if_neg hqin]
      have hr' : r = SymTransResult.mk 101 s Dir.S := by
        simpa [htr] using hr
      rw [hr'] at hrs
      simp at hrs
  have hdec : ∀ q : ℕ, q ≤ 101 → ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (q, s) → r.nextState = 22 →
        q = 21 ∧ s.1 = SymKind.boundary ∧
          r.writeSym = s ∧ r.moveDir = Dir.S := by
    native_decide
  exact hdec q hqle s r hr hrs

/-- 转移结果 nextState = 23 的前驱：22 读 #₁（m=1）左移，或 23 读 data0 自环左扫。 -/
lemma prev_of_nextState_23 (q : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (hrs : r.nextState = 23) :
    (q = 22 ∧ s.1 = SymKind.boundary ∧ s.2 = true ∧
      r.writeSym = s ∧ r.moveDir = Dir.L) ∨
    (q = 23 ∧ s.1 = SymKind.data0 ∧
      r.writeSym = s ∧ r.moveDir = Dir.L) := by
  have hqin : q ∈ VerifierSym.legalStates := by
    by_contra hq
    have htr : VerifierSym.transition (q, s) = {SymTransResult.mk 101 s Dir.S} := by
      unfold VerifierSym.transition
      dsimp
      rw [if_neg hq]
    have hr' : r = SymTransResult.mk 101 s Dir.S := by
      simpa [htr] using hr
    rw [hr'] at hrs
    simp at hrs
  have hdec : ∀ q ∈ VerifierSym.legalStates, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (q, s) → r.nextState = 23 →
        (q = 22 ∧ s.1 = SymKind.boundary ∧ s.2 = true ∧
          r.writeSym = s ∧ r.moveDir = Dir.L) ∨
        (q = 23 ∧ s.1 = SymKind.data0 ∧
          r.writeSym = s ∧ r.moveDir = Dir.L) := by
    native_decide
  exact hdec q hqin s r hr hrs

/-- 转移结果 nextState = 100 的前驱：23 读 boundary 右移，或 100 吸收自环。 -/
lemma prev_of_nextState_100 (q : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (hrs : r.nextState = 100) :
    (q = 23 ∧ s.1 = SymKind.boundary ∧ r.writeSym = s ∧ r.moveDir = Dir.R) ∨
    (q = 100 ∧ r.writeSym = s ∧ r.moveDir = Dir.S) := by
  have hqin : q ∈ VerifierSym.legalStates := by
    by_contra hq
    have htr : VerifierSym.transition (q, s) = {SymTransResult.mk 101 s Dir.S} := by
      unfold VerifierSym.transition
      dsimp
      rw [if_neg hq]
    have hr' : r = SymTransResult.mk 101 s Dir.S := by
      simpa [htr] using hr
    rw [hr'] at hrs
    simp at hrs
  have hdec : ∀ q ∈ VerifierSym.legalStates, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (q, s) → r.nextState = 100 →
        (q = 23 ∧ s.1 = SymKind.boundary ∧ r.writeSym = s ∧ r.moveDir = Dir.R) ∨
        (q = 100 ∧ r.writeSym = s ∧ r.moveDir = Dir.S) := by
    native_decide
  exact hdec q hqin s r hr hrs

-- ============================================================================
-- §4 #₁ 保持（主循环不改变已标记的 #₁）
-- ============================================================================

/-- 转移读已标记 boundary（m=1）时必写回自身（#₁ 保持）。 -/
lemma transition_at_hash1_writes_self (q : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (hs : s.1 = SymKind.boundary)
    (hs2 : s.2 = true) (hq20 : q ≠ 20) :
    r.writeSym = s := by
  by_cases hqin : q ∈ VerifierSym.legalStates
  · have hdec : ∀ q ∈ VerifierSym.legalStates, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (q, s) → s.1 = SymKind.boundary → s.2 = true →
          q ≠ 20 → r.writeSym = s := by
      native_decide
    exact hdec q hqin s r hr hs hs2 hq20
  · have htr : VerifierSym.transition (q, s) = {SymTransResult.mk 101 s Dir.S} := by
      unfold VerifierSym.transition
      dsimp
      rw [if_neg hqin]
    have hr' : r = SymTransResult.mk 101 s Dir.S := by
      simpa [htr] using hr
    subst r
    rfl

/-- SymSteps 路径保持 #₁（boundary 且 mark=true）的值：marked boundary 位置的写必写回自身；
路径上状态 20 的步读的不是已标记符号（实际上 20 读的是未标记的 #₀）。 -/
lemma SymSteps_keep_hash1 {cfg₀ : SymConfig} {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition cfg₀ π cfg) (i : ℤ)
    (hinit : cfg₀.tape i = Sym.mk SymKind.boundary true)
    (hno20 : ∀ step ∈ π, step.fromState ≠ 20 ∨ step.readSym.2 = false) :
    cfg.tape i = Sym.mk SymKind.boundary true := by
  induction h with
  | nil => exact hinit
  | cons π₀ step cfg' h_ind h_from h_read h_trans ih =>
      by_cases hi : i = cfg'.headPos
      · -- 当前步写在 i（marked boundary 位置）：写回自身
        have hs : cfg'.tape cfg'.headPos = Sym.mk SymKind.boundary true := by
          rw [← hi]
          exact ih (by intro step hmem; exact hno20 step (by simp [hmem]))
        by_cases hq20 : cfg'.state = 20
        · -- 20 读 marked boundary：与前提 hno20 矛盾（路径上 20 读的不是已标记符号）
          have hread_marked : step.readSym.2 = true := by
            rw [h_read]
            rw [hs]
            rfl
          have hno := hno20 step (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
          rcases hno with hneq | hreadf
          · exfalso
            exact hneq (by rw [h_from]; exact hq20)
          · exfalso
            simp [hread_marked] at hreadf
        · -- 非 20：写回自身
          have hw : step.result.writeSym = cfg'.tape cfg'.headPos := by
            exact transition_at_hash1_writes_self cfg'.state (cfg'.tape cfg'.headPos) step.result
              (by simpa [h_read] using h_trans) (by simpa [hs]) (by simpa [hs])
              (by intro hq; exact hq20 hq)
          change (symStepConfig cfg' step.result).tape i = Sym.mk SymKind.boundary true
          dsimp [symStepConfig]
          rw [if_pos hi]
          rw [hw, ← hi]
          exact ih (by intro step hmem; exact hno20 step (by simp [hmem]))
      · -- 当前步不写 i
        change (symStepConfig cfg' step.result).tape i = Sym.mk SymKind.boundary true
        dsimp [symStepConfig]
        rw [if_neg hi]
        exact ih (by intro step hmem; exact hno20 step (by simp [hmem]))

-- ============================================================================
-- §5 23 判定扫描 + 组装辅助
-- ============================================================================

/-- 状态 23 读 data0（m=0）：保持 23 左扫。 -/
lemma trans23_data0 (s : Sym) (hk : s.1 = SymKind.data0) :
    { nextState := 23, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (23, s) := by
  rcases s with ⟨k, m⟩
  have hk' : k = SymKind.data0 := by simpa using hk
  subst k
  cases m <;> decide

/-- 状态 23 读 #ₗ（boundary）：右移到接受态 100。 -/
lemma trans23_hash :
    { nextState := 100, writeSym := Sym.boundary, moveDir := Dir.R } ∈
      VerifierSym.transition (23, Sym.boundary) := by
  decide

/-- 同一磁带同一位置的两个等长一致列表相等。 -/
lemma tapeAgrees_inj {tape : ℤ → Sym} {p : ℤ} {l₁ l₂ : List Sym}
    (hlen : l₁.length = l₂.length)
    (h₁ : tapeAgrees tape p l₁) (h₂ : tapeAgrees tape p l₂) : l₁ = l₂ := by
  induction l₁ generalizing p l₂ with
  | nil =>
      cases l₂ with
      | nil => rfl
      | cons b bs => exfalso; have h := hlen; simp at h
  | cons a as ih =>
      cases l₂ with
      | nil => exfalso; have h := hlen; simp at h
      | cons b bs =>
          have ha : a = b := by
            have h₁' := h₁ 0 (by simp)
            have h₂' := h₂ 0 (by simp)
            exact h₁'.symm.trans h₂'
          have h₁' : tapeAgrees tape (p + 1) as := by
            intro i hi
            have h₁i := h₁ (i + 1) (by simp [hi])
            simpa [show p + (↑i + 1) = p + 1 + ↑i from by omega] using h₁i
          have h₂' : tapeAgrees tape (p + 1) bs := by
            intro i hi
            have h₂i := h₂ (i + 1) (by simp [hi])
            simpa [show p + (↑i + 1) = p + 1 + ↑i from by omega] using h₂i
          have hlen' : as.length = bs.length := by
            have h := hlen
            simp at h
            exact h
          have has : as = bs := ih hlen' h₁' h₂'
          simp [ha, has]

/-- `encodeElementsSymWithSel` 对选择串是单射（块首 sel/nosel 区分）。 -/
lemma encodeElementsSymWithSel_inj {elems : List ℕ} {sel₁ sel₂ : List Bool}
    (h₁ : sel₁.length = elems.length) (h₂ : sel₂.length = elems.length)
    (h : encodeElementsSymWithSel elems sel₁ = encodeElementsSymWithSel elems sel₂) :
    sel₁ = sel₂ := by
  induction elems generalizing sel₁ sel₂ with
  | nil =>
      have h₁nil : sel₁ = [] := List.eq_nil_of_length_eq_zero (by simpa using h₁)
      have h₂nil : sel₂ = [] := List.eq_nil_of_length_eq_zero (by simpa using h₂)
      simp [h₁nil, h₂nil]
  | cons v rest ih =>
      cases sel₁ with
      | nil => exfalso; have h := h₁; simp at h
      | cons b₁ sel₁' =>
          cases sel₂ with
          | nil => exfalso; have h := h₂; simp at h
          | cons b₂ sel₂' =>
              have hh : [if b₁ then Sym.sel else Sym.nosel] ++ encodeBitsSymNative v ++
                    encodeElementsSymWithSel rest sel₁' =
                  [if b₂ then Sym.sel else Sym.nosel] ++ encodeBitsSymNative v ++
                    encodeElementsSymWithSel rest sel₂' := by
                simpa [encodeElementsSymWithSel, joinLists] using h
              have hb : (if b₁ then Sym.sel else Sym.nosel) = (if b₂ then Sym.sel else Sym.nosel) := by
                have hh' := congrArg List.head? hh
                simpa using hh'
              have hbb : b₁ = b₂ := by
                by_cases hb₁ : b₁ <;> by_cases hb₂ : b₂
                · simp [hb₁, hb₂]
                · exfalso
                  simpa [Sym.sel, Sym.nosel, Sym.mk, hb₁, hb₂] using hb
                · exfalso
                  simpa [Sym.sel, Sym.nosel, Sym.mk, hb₁, hb₂] using hb
                · simp [hb₁, hb₂]
              have hrest : encodeElementsSymWithSel rest sel₁' = encodeElementsSymWithSel rest sel₂' := by
                have hh' : [if b₁ then Sym.sel else Sym.nosel] ++ encodeBitsSymNative v ++
                      encodeElementsSymWithSel rest sel₁' =
                    [if b₁ then Sym.sel else Sym.nosel] ++ encodeBitsSymNative v ++
                      encodeElementsSymWithSel rest sel₂' := by
                  simpa [hbb] using hh
                have htail : encodeBitsSymNative v ++ encodeElementsSymWithSel rest sel₁' =
                    encodeBitsSymNative v ++ encodeElementsSymWithSel rest sel₂' := by
                  simpa using (congrArg List.tail hh')
                exact (List.append_right_injective (encodeBitsSymNative v)) htail
              have hs₁ : sel₁'.length = rest.length := by simpa using h₁
              have hs₂ : sel₂'.length = rest.length := by simpa using h₂
              have hsel' : sel₁' = sel₂' := ih hs₁ hs₂ hrest
              simp [hbb, hsel']

/-- 状态 23 左扫 n 格全 data0 后读 boundary → 100。 -/
lemma scan23_check (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hkeep : ∀ i : ℤ, p - (n : ℤ) < i ∧ i ≤ p → (tape i).1 = SymKind.data0)
    (hbound : tape (p - (n : ℤ)) = Sym.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 23 tape p) π cfg' ∧
      cfg'.state = 100 ∧ cfg'.headPos = p - (n : ℤ) + 1 ∧ cfg'.tape = tape := by
  refine scanLeftKeepPos 23 100 Sym.boundary Dir.R n p tape ?_ ?_ hbound
  · intro i hi
    exact trans23_data0 (tape i) (hkeep i hi)
  · exact trans23_hash


-- ============================================================================
-- §5 holds ⟹ Sym 层接受（完整组装 0 → 100）
-- ============================================================================

/-- bitsToSym 全 false ⟹ 全 data0。 -/
lemma bitsToSym_all_data0 {bits : List Bool} (h : ∀ b ∈ bits, b = false) :
    ∀ i (hi : i < (bitsToSym bits).length), (bitsToSym bits)[i] = Sym.data0 := by
  induction bits with
  | nil => intro i hi; simp [bitsToSym] at hi
  | cons b bs ih =>
      have hb : b = false := h b (by simp)
      intro i hi
      cases i with
      | zero =>
          simp [bitsToSym, hb]
      | succ i =>
          have hi' : i < (bitsToSym bs).length := by simpa [bitsToSym] using hi
          have hb' : ∀ b' ∈ bs, b' = false := by intro b' hb'; exact h b' (by simp [hb'])
          have hd := ih hb' i hi'
          simpa [bitsToSym, hb] using hd

/-- holds ⟹ Sym 层接受（0 → 100 完整路径）。 -/
theorem sym_accept_of_holds (inst : SubsetSumInstance) (hne : inst.elements ≠ [])
    (hpos : ∀ v ∈ inst.elements, 0 < v) (htgt : 0 < inst.target)
    (hholds : subsetSumHolds inst) :
    symAccepts VerifierSym.transition VerifierSym.acceptStates (encodeInstanceSym inst) := by
  rcases hholds with ⟨sel₀, hsel_len₀, hsum₀⟩
  let tbits := bitsOf inst.target
  let p₀ : ℤ := 1 + (tbits.length : ℤ)
  let pE : ℤ := p₀ + 1
  have hlen : (encodeBitsSym inst.target).length = (bitsOf inst.target).length := by
    rw [encodeBitsSym_eq_bitsToSym_bitsOf]
    simp [bitsToSym]
  have hpE : pE = 2 + ((encodeBitsSym inst.target).length : ℤ) := by
    dsimp [pE, p₀, tbits]
    rw [hlen]
    omega
  -- 阶段 A：0 → 4（branch_phase + scanRight2_chosen sel₀）
  rcases branch_phase inst hne hpos htgt sel₀ hsel_len₀
      (fun tape helems hbound => by
        rw [← hpE] at helems
        rw [← hpE] at hbound
        rcases scanRight2_chosen inst.elements sel₀ pE tape hsel_len₀ helems hbound with
          ⟨π₂, cfg₂, hπ₂, hs₂, hhead₂, htape_sel₂, _hne₂, hleft₂, hbnd₂⟩
        exact ⟨π₂, cfg₂, by simpa [hpE] using hπ₂, hs₂, by simpa [hpE] using hhead₂,
          by simpa [hpE] using hbnd₂, by simpa [hpE] using hleft₂,
          sel₀, hsel_len₀, by simpa [hpE] using htape_sel₂, rfl⟩)
    with ⟨πA, cfgA, hπA, hsA, hheadA, htargetA, hhashL_A, hhash0_A,
      ⟨selA, hselA_len, hWithSel_A, hselA_eq⟩, hhash1_A⟩
  -- 阶段 B：4 → 22（main_loop_correct）
  have hle_total : selectedSum inst.elements selA ≤ bitsValue tbits := by
    rw [hselA_eq, hsum₀, bitsValue_bitsOf]
  rcases main_loop_correct inst.elements selA tbits 1 p₀ cfgA.tape hne hpos hselA_len
      (by dsimp [p₀]; omega)
      (by simpa [targetTape, tbits, encodeBitsSym_eq_bitsToSym_bitsOf] using htargetA)
      (by simpa [p₀, tbits, bitsOf, symToBits, encodeBitsSym] using hhash0_A)
      (by simpa [p₀] using hhashL_A)
      (by intro i hi; omega)
      (by
        have hpos_e : 1 + ↑tbits.length + 1 = 2 + ((encodeBitsSym inst.target).length : ℤ) := by
          dsimp [tbits]
          rw [hlen]
          omega
        rw [hpos_e]
        exact hWithSel_A)
      (by
        have hh1 : cfgA.tape (pE + ((encodeElementsSym inst.elements).length : ℤ)) = Sym.mk SymKind.boundary true := by
          simpa [hpE] using hhash1_A
        have hwsl : (encodeElementsSymWithSel inst.elements selA).length = (encodeElementsSym inst.elements).length :=
          WithSel_length inst.elements selA hselA_len
        have hpos_eq : p₀ + 1 + ((encodeElementsSymWithSel inst.elements selA).length : ℤ) =
            pE + ((encodeElementsSym inst.elements).length : ℤ) := by
          dsimp [pE, p₀]
          rw [hwsl]
        rw [hpos_eq]
        exact congrArg Prod.fst hh1)
      hle_total
    with ⟨πB, cfgB, hπB, hsB, htargetB, hheadB, hclearB, hhashL_B, hpadB, hrightB, hkeepB⟩
  -- 阶段 C：22 → 23（单步，22 读 #₁ marked 左移）
  have hmarked : cfgB.tape cfgB.headPos = Sym.mk SymKind.boundary true := by
    rw [hkeepB]
    have hpos1 : cfgB.headPos = pE + ((encodeElementsSym inst.elements).length : ℤ) := by
      rw [hheadB]
      have hwsl : (encodeElementsSymWithSel inst.elements selA).length = (encodeElementsSym inst.elements).length :=
        WithSel_length inst.elements selA hselA_len
      dsimp [pE, p₀]
      rw [hwsl]
      omega
    rw [hpos1]
    simpa [hpE] using hhash1_A
  let stepC : SymStep := { fromState := 22, readSym := Sym.mk SymKind.boundary true, result := { nextState := 23, writeSym := Sym.mk SymKind.boundary true, moveDir := Dir.L } }
  have hstepC : SymSteps VerifierSym.transition cfgB [stepC] (symStepConfig cfgB stepC.result) := by
    refine SymSteps.cons [] stepC cfgB SymSteps.nil ?_ ?_ ?_
    · exact hsB.symm
    · exact hmarked.symm
    · rw [hsB]
      change stepC.result ∈ VerifierSym.transition (22, cfgB.tape cfgB.headPos)
      rw [hmarked]
      decide
  let cfgC' : SymConfig := symStepConfig cfgB stepC.result
  have hcfgC' : cfgC' = SymConfig.mk 23 cfgB.tape (cfgB.headPos - 1) := by
    dsimp [cfgC', stepC]
    simp [symStepConfig, Dir.toInt]
    constructor
    · funext i
      by_cases hi : i = cfgB.headPos
      · rw [hi]
        simp [hmarked]
      · simp [hi]
    · rfl
  -- 阶段 D：23 判定扫描（从 headPos-1 向左到 #ₗ）
  have hsubAll_false : ∀ b ∈ subAllSelected 0 tbits inst.elements selA, b = false := by
    have hbv : bitsValue (subAllSelected 0 tbits inst.elements selA) = 0 := by
      rw [subAllSelected_value 0 tbits inst.elements selA hle_total]
      rw [hselA_eq, hsum₀, bitsValue_bitsOf]
      omega
    exact (bitsValue_eq_zero_iff_all_false (subAllSelected 0 tbits inst.elements selA)).mp hbv
  have hdata23 : ∀ i : ℤ, 0 < i ∧ i ≤ cfgB.headPos - 1 →
      (cfgB.tape i).1 = SymKind.data0 := by
    intro i hi
    by_cases hlt : i < p₀
    · -- target 区 [1, p₀)：htargetB（subAllSelected 全 false → 全 data0）
      let k : ℕ := Int.toNat (i - 1)
      have hk : (k : ℤ) = i - 1 := by
        dsimp [k]
        exact Int.toNat_of_nonneg (by omega)
      have hk_lt : k < (targetTape 0 (subAllSelected 0 tbits inst.elements selA)).length := by
        rw [targetTape_zero]
        simp [bitsToSym, subAllSelected_length]
        have hk' : (k : ℤ) < (tbits.length : ℤ) := by
          rw [hk]
          omega
        exact_mod_cast hk'
      have hta := htargetB k hk_lt
      have hpos' : 1 + (k : ℤ) = i := by
        rw [hk]
        omega
      rw [hpos'] at hta
      have hd : (targetTape 0 (subAllSelected 0 tbits inst.elements selA))[k]'(hk_lt) = Sym.data0 := by
        simpa [targetTape_zero] using (bitsToSym_all_data0 hsubAll_false k (by simpa using hk_lt))
      rw [hta, hd]
      rfl
    · -- [p₀, headPos)：hclearB
      have hd := hclearB i (by constructor <;> omega)
      rw [hd]
      rfl
  have hbound0 : cfgB.tape 0 = Sym.boundary := by
    simpa using hhashL_B
  let n23 : ℕ := Int.toNat (cfgB.headPos - 1)
  have hn23 : (n23 : ℤ) = cfgB.headPos - 1 := by
    dsimp [n23]
    have hge : 0 ≤ cfgB.headPos - 1 := by
      rw [hheadB]
      dsimp [p₀]
      omega
    exact Int.toNat_of_nonneg hge
  rcases scan23_check n23 (cfgB.headPos - 1) cfgB.tape
      (by
        intro i hi
        have hi' : 0 < i ∧ i ≤ cfgB.headPos - 1 := by
          rw [hn23] at hi
          omega
        exact hdata23 i hi')
      (by
        simpa [hn23] using hbound0)
    with ⟨πD, cfgD, hπD, hsD, hheadD, htapeD⟩
  -- 拼接 0 → 100
  have hcfgA : cfgA = SymConfig.mk 4 cfgA.tape pE := by
    cases cfgA with
    | mk s t hp =>
        change s = 4 at hsA
        subst s
        change hp = 2 + ((encodeBitsSym inst.target).length : ℤ) at hheadA
        subst hp
        simp [SymConfig.mk, hpE]
  have hπAB : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) (πA ++ πB) cfgB := by
    have hπB' : SymSteps VerifierSym.transition cfgA πB cfgB := by
      rw [hcfgA]
      exact hπB
    exact SymSteps_trans VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) cfgA cfgB πA πB hπA hπB'
  have hπABC : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) (πA ++ πB ++ [stepC]) cfgC' := by
    have hπBC : SymSteps VerifierSym.transition cfgA (πB ++ [stepC]) cfgC' := by
      have hπB2 : SymSteps VerifierSym.transition cfgA πB cfgB := by
        rw [hcfgA]
        exact hπB
      exact SymSteps_trans VerifierSym.transition cfgA cfgB cfgC' πB [stepC] hπB2 hstepC
    simpa [List.append_assoc] using
      (SymSteps_trans VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) cfgA cfgC' πA (πB ++ [stepC]) hπA hπBC)
  have hπD' : SymSteps VerifierSym.transition cfgC' πD cfgD := by
    rw [hcfgC']
    exact hπD
  have hπ_all : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) (πA ++ πB ++ [stepC] ++ πD) cfgD := by
    simpa [List.append_assoc] using
      (SymSteps_trans VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) cfgC' cfgD (πA ++ πB ++ [stepC]) πD hπABC hπD')
  refine ⟨πA ++ πB ++ [stepC] ++ πD, cfgD, ?_, ?_⟩
  · simpa [List.append_assoc] using
      ((symSteps_initial_iff VerifierSym.transition (encodeInstanceSym inst)
        (πA ++ πB ++ [stepC] ++ πD) cfgD).mp hπ_all)
  · rw [hsD]
    simp [VerifierSym.acceptStates, qAccept]

end Mp
