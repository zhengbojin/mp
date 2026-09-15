/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import Mp.IVM
import Mp.PrimeSqrtLinearIndep
import Mp.A2Bridge
import Mp.SubsetSumInNP

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
# Mp.ATMTransfer —— κ 传递层（T1 位置桥 / T2 代数分开 / T3 装配）

形状定形（2026-09-14 用户裁决）：
- **T2（本文件）**：路径值 `pathValue`（**不分号模式版**）= Σ_{i ∈ 激活索引集} √p_i，
  素数族取 mathlib `Nat.nth Nat.Prime`；
  **分开定理**：两条路径的激活模式不同 ⇒ 值不同（由素数平方根 ℚ-线性独立）。
- T1（位置桥）：`iso_path_forward_forkCount`（路径计数对应：`ntm2ForkCount π = branchCount π'`）+ `iso_vbAt_iff_card_two`（点态：vb=1 ⟷ CBTM 读空白处卡恰 2）——已落本文件 §4/§5。
- T3（装配预告）：`subsetSum_kappa_lower_bound` + T1 + T2 ⇒ 传统 P vs NP 推进。
-/

namespace Mp

-- ============================================================================
-- §1 素数族（Nat.nth Nat.Prime）
-- ============================================================================

/-- 第 k 个素数。 -/
noncomputable def nthPrime (k : ℕ) : ℕ := Nat.nth Nat.Prime k

/-- 第 k 个素数是素数。 -/
lemma nthPrime_prime (k : ℕ) : Nat.Prime (nthPrime k) := by
  unfold nthPrime
  exact Nat.prime_nth_prime k

/-- 素数族严格单增（⇒ 单射）。 -/
lemma nthPrime_strictMono : StrictMono nthPrime := by
  unfold nthPrime
  exact Nat.nth_strictMono Nat.infinite_setOf_prime

lemma nthPrime_injective : Function.Injective nthPrime :=
  nthPrime_strictMono.injective

-- ============================================================================
-- §2 路径值（不分号模式版）
-- ============================================================================

/-- 路径值：激活索引集 Σ √(第 i 个素数)。不分号——只记录激活模式。 -/
noncomputable def pathValue (π : ComputationPath) : ℝ :=
  ∑ i ∈ activatedGenSetOnPath π, Real.sqrt ((nthPrime i : ℕ) : ℝ)

/-- 无激活（受限机器路径/无分支路径）⇒ 值 0。 -/
@[simp] lemma pathValue_of_no_activation (π : ComputationPath)
    (h : activatedGenSetOnPath π = ∅) : pathValue π = 0 := by
  unfold pathValue
  simp [h]

-- ============================================================================
-- §3 分开定理：激活模式不同 ⇒ 值不同
-- ============================================================================

/-- **T2 分开定理（不分号模式版）**：两条路径的激活模式（激活索引集）不同，
    则路径值不同——差为 Σ ±√p_i（±1 系数）非零，由素数平方根 ℚ-线性独立。 -/
theorem pathValue_separated (π₁ π₂ : ComputationPath)
    (h : activatedGenSetOnPath π₁ ≠ activatedGenSetOnPath π₂) :
    pathValue π₁ ≠ pathValue π₂ := by
  intro heq
  set S₁ : Finset ℕ := activatedGenSetOnPath π₁
  set S₂ : Finset ℕ := activatedGenSetOnPath π₂
  let T : Finset ℕ := S₁ ∪ S₂
  have hzero₁ : ∀ i ∈ T, i ∉ S₁ →
      (if i ∈ S₁ then (1 : ℚ) else 0) • Real.sqrt ((nthPrime i : ℕ) : ℝ) = 0 := by
    intro i _ hi
    simp [hi]
  have hzero₂ : ∀ i ∈ T, i ∉ S₂ →
      (if i ∈ S₂ then (1 : ℚ) else 0) • Real.sqrt ((nthPrime i : ℕ) : ℝ) = 0 := by
    intro i _ hi
    simp [hi]
  have hT₁ : ∑ i ∈ T, (if i ∈ S₁ then (1 : ℚ) else 0) • Real.sqrt ((nthPrime i : ℕ) : ℝ)
      = ∑ i ∈ S₁, Real.sqrt ((nthPrime i : ℕ) : ℝ) := by
    rw [(Finset.sum_subset (Finset.subset_union_left) hzero₁).symm]
    exact Finset.sum_congr rfl (fun i hi => by simp [hi])
  have hT₂ : ∑ i ∈ T, (if i ∈ S₂ then (1 : ℚ) else 0) • Real.sqrt ((nthPrime i : ℕ) : ℝ)
      = ∑ i ∈ S₂, Real.sqrt ((nthPrime i : ℕ) : ℝ) := by
    rw [(Finset.sum_subset (Finset.subset_union_right) hzero₂).symm]
    exact Finset.sum_congr rfl (fun i hi => by simp [hi])
  have hΔ : ∑ i ∈ T, (if i ∈ S₁ then (1 : ℚ) else 0) • Real.sqrt ((nthPrime i : ℕ) : ℝ)
      = ∑ i ∈ T, (if i ∈ S₂ then (1 : ℚ) else 0) • Real.sqrt ((nthPrime i : ℕ) : ℝ) := by
    rw [hT₁, hT₂]
    simpa [S₁, S₂, pathValue] using heq
  have hcomb : ∑ i ∈ T,
      ((if i ∈ S₁ then (1 : ℚ) else 0) - (if i ∈ S₂ then (1 : ℚ) else 0))
        • Real.sqrt ((nthPrime i : ℕ) : ℝ) = 0 := by
    calc ∑ i ∈ T, ((if i ∈ S₁ then (1 : ℚ) else 0) - (if i ∈ S₂ then (1 : ℚ) else 0))
            • Real.sqrt ((nthPrime i : ℕ) : ℝ)
        = ∑ i ∈ T, ((if i ∈ S₁ then (1 : ℚ) else 0) • Real.sqrt ((nthPrime i : ℕ) : ℝ)
            - (if i ∈ S₂ then (1 : ℚ) else 0) • Real.sqrt ((nthPrime i : ℕ) : ℝ)) :=
          Finset.sum_congr rfl (fun i _ => sub_smul _ _ _)
      _ = ∑ i ∈ T, (if i ∈ S₁ then (1 : ℚ) else 0) • Real.sqrt ((nthPrime i : ℕ) : ℝ)
            - ∑ i ∈ T, (if i ∈ S₂ then (1 : ℚ) else 0) • Real.sqrt ((nthPrime i : ℕ) : ℝ) := by
          rw [Finset.sum_sub_distrib]
      _ = 0 := by rw [hΔ, sub_self]
  have hg : ∑ i : ↥T,
      ((if i.1 ∈ S₁ then (1 : ℚ) else 0) - (if i.1 ∈ S₂ then (1 : ℚ) else 0))
        • Real.sqrt ((nthPrime i.1 : ℕ) : ℝ) = 0 := by
    rw [show (Finset.univ : Finset ↥T) = T.attach from Finset.univ_eq_attach T]
    rw [Finset.sum_attach T (fun i => ((if i ∈ S₁ then (1 : ℚ) else 0)
      - (if i ∈ S₂ then (1 : ℚ) else 0)) • Real.sqrt ((nthPrime i : ℕ) : ℝ))]
    exact hcomb
  have hli := primeSqrt_Q_linearIndependent_finite
    (fun i : ↥T => nthPrime i.1)
    (fun i => nthPrime_prime i.1)
    (fun i j hij => Subtype.ext (nthPrime_injective hij))
  have hc0 := (Fintype.linearIndependent_iff.mp hli)
    (fun i : ↥T => (if i.1 ∈ S₁ then (1 : ℚ) else 0)
      - (if i.1 ∈ S₂ then (1 : ℚ) else 0)) hg
  have hne : ∃ i, (i ∈ S₁ ∧ i ∉ S₂) ∨ (i ∈ S₂ ∧ i ∉ S₁) := by
    by_contra h3
    push Not at h3
    apply h
    ext i
    rcases h3 i with ⟨h1, h2⟩
    constructor
    · intro hi
      exact h1 hi
    · intro hi
      exact h2 hi
  rcases hne with ⟨i, hi | hi⟩
  · have hmem : i ∈ T := Finset.mem_union.mpr (Or.inl hi.1)
    have hz := hc0 ⟨i, hmem⟩
    have hc : (if i ∈ S₁ then (1 : ℚ) else 0) - (if i ∈ S₂ then (1 : ℚ) else 0) = 1 := by
      rw [if_pos hi.1, if_neg hi.2]
      norm_num
    rw [hc] at hz
    exact (by norm_num : (1 : ℚ) ≠ 0) hz
  · have hmem : i ∈ T := Finset.mem_union.mpr (Or.inr hi.1)
    have hz := hc0 ⟨i, hmem⟩
    have hc : (if i ∈ S₁ then (1 : ℚ) else 0) - (if i ∈ S₂ then (1 : ℚ) else 0) = -1 := by
      rw [if_neg hi.2, if_pos hi.1]
      norm_num
    rw [hc] at hz
    exact (by norm_num : (-1 : ℚ) ≠ 0) hz

-- ============================================================================
-- §4 T1 位置桥（路径计数对应；用户裁决形状 2026-09-14）
-- ============================================================================

/-- NTM2 分叉计数的单步加法（对应 `branchCount_append`）。 -/
lemma ntm2ForkCount_append_singleton (A : NTM2) (π : NTM2ComputationPath)
    (step : NTM2TransitionStep) :
    ntm2ForkCount A (π ++ [step]) =
      ntm2ForkCount A π + (if F4.im step.readSym = true then 1 else 0) := by
  dsimp [ntm2ForkCount]
  rw [List.filter_append, List.length_append]
  cases h : F4.im step.readSym <;> simp [h]

/-- **T1 前向位置桥**：iso 路径对应下，NTM2 分叉计数 = CBTM 分支计数。
    机制：读符号恒等翻译（iso_path_forward 中 `readSym := step.readSym`）
    ⇒ 虚部标记一致 ⇒ 过滤计数一致。归纳加强（同 iso_path_forward + 计数合取）。 -/
theorem iso_path_forward_forkCount (A : NTM2) (M : CBTM) (iso : StructIsoNTM2CBTM A M)
    (x : List F4) (hcan : NTM2.Canonical A) :
    ∀ π, ∀ cfg : NTM2Config A x, TapeReachablePathNTM2 A x π cfg →
      ∃ π' : ComputationPath, ∃ cfg' : CBTMConfig M x,
        TapeReachablePath M x π' cfg' ∧
        cfg' = ntm2CfgToCBTM A M iso cfg ∧
        ntm2ForkCount A π = branchCount π' := by
  intro π cfg hr
  induction hr with
  | nil =>
      refine ⟨[], initialConfig M x, TapeReachablePath.nil, ?_, ?_⟩
      · exact (iso_initial_corresp A M iso x).symm
      · dsimp [ntm2ForkCount, branchCount]
  | cons π₀ step cfg₀ hrc hfrom hread hpos htrans ih =>
      rcases ih with ⟨π', cfg', hrc', hcfg', hcnt⟩
      have hs_in : step.readSym ∈ A.alphabet := by
        by_contra hsnot
        have hout := A.h_transition_outside cfg₀.state step.readSym cfg₀.headPos hsnot
        rw [← hread] at htrans
        rw [hout] at htrans
        simpa using htrans
      let step' : TransitionStep :=
        { fromState := step.fromState,
          readSym := step.readSym,
          result := ntm2ResultToCBTM step.result }
      refine ⟨π' ++ [step'], stepConfig cfg' step'.result,
        TapeReachablePath.cons π' step' cfg' hrc' ?_ ?_ ?_, ?_, ?_⟩
      · rw [hcfg']
        dsimp [ntm2CfgToCBTM]
        dsimp [step']
        rw [← hfrom]
      · rw [hcfg']
        dsimp [ntm2CfgToCBTM, CBTMConfig.tapeAt]
        dsimp [step']
        rw [hread]
      · rw [hcfg']
        dsimp [ntm2CfgToCBTM, CBTMConfig.tapeAt]
        dsimp [step']
        rw [← hread, ← hpos] at htrans ⊢
        have hstepfwd := iso_step_forward A M iso cfg₀.state step.readSym step.pos step.result hs_in htrans
        rw [iso.h_φ_id step.readSym] at hstepfwd
        exact hstepfwd
      · rw [hcfg']
        dsimp [ntm2CfgToCBTM]
        dsimp [step']
        exact (iso_step_config A M iso cfg₀ step.result).symm
      · rw [ntm2ForkCount_append_singleton, branchCount_append, hcnt]

-- ============================================================================
-- §5 T1 点态桥：vb ↔ 卡恰 2（经 iso 搬运）
-- ============================================================================

/-- **T1 点态桥**：读空白处的分支声明经 iso 搬运到 CBTM 侧：
    vb=1（A 侧转移卡=2）⟷ M 侧转移卡=2。 -/
theorem iso_vbAt_iff_card_two (A : NTM2) (M : CBTM) (iso : StructIsoNTM2CBTM A M)
    (i : ℤ) :
    NTM2.vbAt A i = true ↔ (M.transition (M.startState, M.blankSym, i)).card = 2 := by
  have hcard : (M.transition (M.startState, M.blankSym, i)).card =
      (A.transition (A.startState, A.blankSym, i)).card := by
    have hM : M.transition (M.startState, M.blankSym, i) =
        (A.transition (A.startState, A.blankSym, i)).image ntm2ResultToCBTM := by
      rw [iso.h_start, iso.h_blank]
      have hthis := iso.h_transition A.startState A.blankSym i A.h_blank_in_alphabet
      rwa [iso.h_φ_id A.blankSym] at hthis
    rw [hM, Finset.card_image_of_injective _ ntm2ResultToCBTM_injective]
  unfold NTM2.vbAt
  rw [hcard]
  simp

end Mp
