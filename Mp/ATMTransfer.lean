/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import Mp.IVM
import Mp.PrimeSqrtLinearIndep

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
- T1（位置桥）：`ntm2ForkCount π = branchCount π'`（iso 路径对应）+ 点态 vb ⟷ cellV1——后续落此文件。
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
    push_neg at h3
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

end Mp
