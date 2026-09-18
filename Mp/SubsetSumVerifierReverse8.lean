/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import Mp.SubsetSumVerifierReverse4
import Mp.SubsetSumVerifierReverse5

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
set_option linter.style.emptyLine false
set_option linter.style.setOption false



/-!
# Reverse8:条款 4(接受 ⟹ 合法编码)组装

A1 条款 4(hrel)的定理化:把 `no_trap_path_decodes_prefix`(Reverse5,q11b)
与 `symAccepts_implies_encodeInstanceSym`(Reverse4)组装为

    ∀ M : CBTM, Nonempty (StructIsoNTM2CBTM subsetSumNTM2 M) →
      ∀ w : List F4, M.tapeAccepts w →
        ∃ inst g, w = encodeInstanceF4 inst ++ g ∧ …

结构:

1. 转移层桥:`toCBTMTrans_subsetSumNTM2_eq` / `iso_transition_eq` /
   `iso_acceptStates_eq` / `iso_startState_eq` / `iso_blankSym_eq` ——
   把同构机器 M 的接受性归约到 `subsetSumCBTM.tapeAccepts`。
2. `iso_tapeSteps` / `iso_tapeAccepts_forward`:M.tapeAccepts w →
   subsetSumCBTM.tapeAccepts w(TapeSteps 逐字段重放,转移函数经 iso_transition_eq 相等)。
3. 主定理 `iso_accepts_implies_encoding`:q11b 解码 → symAccepts →
   Reverse4 编码前缀 → 长度组装。
-/

namespace Mp.SymToF4
open Classical

-- ============================================================================
-- §1. 转移层桥:同构机器的转移函数 = subsetSumCBTM.transition
-- ============================================================================

/-- toCBTM subsetSumNTM2 的转移函数就是 subsetSumCBTM.transition。 -/
lemma toCBTMTrans_subsetSumNTM2_eq :
    NTM2.toCBTMTrans subsetSumNTM2 = subsetSumCBTM.transition := by
  have h := congrArg CBTM.transition toCBTM_subsetSumNTM2_eq
  simpa [NTM2.toCBTM] using h

/-- 字母表全集的成员判定(结构同构桥的 h_transition 前提)。 -/
lemma mem_subsetSumNTM2_alphabet (s : F4) : s ∈ subsetSumNTM2.alphabet := by
  dsimp [subsetSumNTM2, subsetSumCBTM]
  rcases s with ⟨r, im⟩ <;> cases r <;> cases im <;>
    simp [F4.zero, F4.one, F4.alpha, F4.beta]

/-- StructIso 桥:M.transition = subsetSumCBTM.transition(点态)。 -/
lemma iso_transition_eq (M : CBTM) (iso : StructIsoNTM2CBTM subsetSumNTM2 M) :
    ∀ q s i, M.transition (q, s, i) = subsetSumCBTM.transition (q, s, i) := by
  intro q s i
  have h1 := iso.h_transition q s i (mem_subsetSumNTM2_alphabet s)
  have h2 := iso.h_φ_id s
  rw [h2] at h1
  have h3 : (subsetSumNTM2.transition (q, s, i)).image ntm2ResultToCBTM =
      subsetSumCBTM.transition (q, s, i) := by
    rw [← toCBTMTrans_eq subsetSumNTM2 q s i (mem_subsetSumNTM2_alphabet s)]
    rw [toCBTMTrans_subsetSumNTM2_eq]
  rw [h3] at h1
  exact h1

/-- StructIso 桥:M.acceptStates = subsetSumCBTM.acceptStates。 -/
lemma iso_acceptStates_eq (M : CBTM) (iso : StructIsoNTM2CBTM subsetSumNTM2 M) :
    M.acceptStates = subsetSumCBTM.acceptStates := by
  rw [iso.h_accept]
  have h := congrArg CBTM.acceptStates toCBTM_subsetSumNTM2_eq
  simpa [NTM2.toCBTM] using h

/-- StructIso 桥:M.startState = subsetSumCBTM.startState。 -/
lemma iso_startState_eq (M : CBTM) (iso : StructIsoNTM2CBTM subsetSumNTM2 M) :
    M.startState = subsetSumCBTM.startState := by
  rw [iso.h_start]
  have h := congrArg CBTM.startState toCBTM_subsetSumNTM2_eq
  simpa [NTM2.toCBTM] using h

/-- StructIso 桥:M.blankSym = subsetSumCBTM.blankSym。 -/
lemma iso_blankSym_eq (M : CBTM) (iso : StructIsoNTM2CBTM subsetSumNTM2 M) :
    M.blankSym = subsetSumCBTM.blankSym := by
  rw [iso.h_blank]
  rfl

-- ============================================================================
-- §2. 接受性桥:M.tapeAccepts → subsetSumCBTM.tapeAccepts
-- ============================================================================

/-- 同构机器的 TapeSteps 在 subsetSumCBTM 上重放(逐字段)。 -/
lemma iso_tapeSteps (M : CBTM) (iso : StructIsoNTM2CBTM subsetSumNTM2 M) (w : List F4)
    {π : ComputationPath} {cfg : CBTMConfig M w}
    (h : TapeSteps M w (initialConfig M w) π cfg) :
    TapeSteps subsetSumCBTM w (initialConfig subsetSumCBTM w) π
      ⟨cfg.state, cfg.tape, cfg.headPos⟩ := by
  induction h with
  | nil =>
      have hcfg : (⟨(initialConfig M w).state, (initialConfig M w).tape,
          (initialConfig M w).headPos⟩ : CBTMConfig subsetSumCBTM w) =
          initialConfig subsetSumCBTM w := by
        dsimp [initialConfig]
        rw [iso_startState_eq M iso]
        rw [iso_blankSym_eq M iso]
      rw [hcfg]
      exact TapeSteps.nil
  | cons πs₀ step cfg' hprev hfrom hread htrans ih =>
      refine TapeSteps.cons (π := πs₀) (step := step)
        (cfg' := ⟨cfg'.state, cfg'.tape, cfg'.headPos⟩) ih hfrom hread ?_
      rw [iso_transition_eq M iso cfg'.state (cfg'.tapeAt cfg'.headPos) cfg'.headPos] at htrans
      simpa [CBTMConfig.tapeAt] using htrans

/-- 同构机器的接受路径在 subsetSumCBTM 上重放。 -/
lemma iso_tapeAccepts_forward (M : CBTM) (iso : StructIsoNTM2CBTM subsetSumNTM2 M)
    (w : List F4) :
    M.tapeAccepts w → subsetSumCBTM.tapeAccepts w := by
  rintro ⟨π, cfg, hpath, hacc⟩
  refine ⟨π, ⟨cfg.state, cfg.tape, cfg.headPos⟩, ?_, ?_⟩
  · have hsteps := (tapeSteps_initial_iff M w π cfg).mpr hpath
    exact (tapeSteps_initial_iff subsetSumCBTM w π ⟨cfg.state, cfg.tape, cfg.headPos⟩).mp
      (iso_tapeSteps M iso w hsteps)
  · rw [iso_acceptStates_eq M iso] at hacc
    exact hacc

-- ============================================================================
-- §3. flat4F4 的 append 分解与条款 4 主定理
-- ============================================================================

/-- flat4F4 保 append(flatMap 分解)。 -/
lemma flat4F4_append (w₁ w₂ : List Sym) :
    flat4F4 (w₁ ++ w₂) = flat4F4 w₁ ++ flat4F4 w₂ := by
  dsimp [flat4F4]
  rw [List.flatMap_append]

/-- 条款 4(hrel 于 A := subsetSumNTM2):同构机器对合法符号输入(完整 8bit 块串)
    接受 ⟹ 输入是某非空正实例编码 ++ 垃圾后缀。
    输入带 = 2bit 符号串经符号对应(1 符号 ↔ 4F4,含 padding)编译——合法输入
    即 flat4F4 的像;块内 padding 位固定,不存在「半块截断」的合法输入。 -/
theorem iso_accepts_implies_encoding (M : CBTM)
    (iso : StructIsoNTM2CBTM subsetSumNTM2 M) :
    ∀ w : List F4, (∃ wS₀ : List Sym, w = flat4F4 wS₀) →
      M.tapeAccepts w →
      ∃ inst : SubsetSumInstance, ∃ gS : List Sym,
        w = encodeInstanceF4 inst ++ flat4F4 gS ∧
        inst.elements ≠ [] ∧ (∀ v ∈ inst.elements, 0 < v) ∧ 0 < inst.target := by
  intro w hwf hacc
  rcases hwf with ⟨wS₀, hf⟩
  have haccC : subsetSumCBTM.tapeAccepts w := iso_tapeAccepts_forward M iso w hacc
  have hsym : symAccepts VerifierSym.transition VerifierSym.acceptStates wS₀ :=
    (subsetSumCBTM_accepts_iff_symAccepts wS₀).1 (by rw [← hf]; exact haccC)
  rcases symAccepts_implies_encodeInstanceSym wS₀ hsym with ⟨inst, gS, hwS, hne, hpos, htarget⟩
  refine ⟨inst, gS, ?_, hne, hpos, htarget⟩
  calc
    w = flat4F4 wS₀ := hf
    _ = flat4F4 (encodeInstanceSym inst ++ gS) := by rw [hwS]
    _ = flat4F4 (encodeInstanceSym inst) ++ flat4F4 gS := flat4F4_append _ _
    _ = encodeInstanceF4 inst ++ flat4F4 gS := rfl

end SymToF4
