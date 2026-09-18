/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import Mp.SubsetSumVerifierReverse

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.constructorNameAsVariable false
set_option linter.unusedVariables false
set_option linter.style.nativeDecide false
set_option maxHeartbeats 8000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.style.multiGoal false
set_option linter.style.whitespace false

namespace Mp

open CBTM
open IVM
open F4

/-- 分支选择后的磁带：位置 元素开始位置 处按 sel 写 sel/nosel，其余同 tape₀。 -/
lemma trans1_next1_or_2 (s : Sym) (r : SymTransResult) (hr : r ∈ VerifierSym.transition (1, s)) :
    r.nextState = 1 ∨ r.nextState = 2 ∨ r.nextState = 101 := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (1, Sym.mk k m) →
        r.nextState = 1 ∨ r.nextState = 2 ∨ r.nextState = 101 := by
    native_decide
  rcases s with ⟨k, m⟩
  exact hdec k m r hr

/-- 状态 1 的 101 分支：读符号 kind ∈ {consumed, alpha, sel, nosel, beta}。 -/
lemma trans1_next101_read_kind (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (1, s)) (hnext : r.nextState = 101) :
    s.1 = SymKind.consumed ∨ s.1 = SymKind.alpha ∨ s.1 = SymKind.sel ∨
      s.1 = SymKind.nosel ∨ s.1 = SymKind.beta := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (1, Sym.mk k m) → r.nextState = 101 →
        k = SymKind.consumed ∨ k = SymKind.alpha ∨ k = SymKind.sel ∨
          k = SymKind.nosel ∨ k = SymKind.beta := by
    native_decide
  rcases s with ⟨k, m⟩
  exact hdec k m r hr hnext

/-- 状态 3 的下一步 ∈ {24, 101}（读 #₁ 判定进入格式检查）。 -/
lemma trans3_next3_or_4 (s : Sym) (r : SymTransResult) (hr : r ∈ VerifierSym.transition (3, s)) :
    r.nextState = 24 ∨ r.nextState = 101 := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (3, Sym.mk k m) → r.nextState = 24 ∨ r.nextState = 101 := by
    native_decide
  rcases s with ⟨k, m⟩
  exact hdec k m r hr
/-- 转移保 legalStates：q ∈ detset 组 1（[4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22]）。 -/
lemma transition_nextState_in_legal_det1 (q : ℕ) (s : Sym) (r : SymTransResult)
    (hq : q = 4 ∨ q = 5 ∨ q = 8 ∨ q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 12 ∨ q = 13 ∨ q = 14 ∨ q = 20 ∨ q = 21 ∨ q = 22)
    (hr : r ∈ VerifierSym.transition (q, s)) :
    r.nextState ∈ VerifierSym.legalStates := by
  have hdec : ∀ q ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22} : Finset ℕ),
      ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (q, Sym.mk k m) → r.nextState ∈ VerifierSym.legalStates := by
    native_decide
  rcases s with ⟨k, m⟩
  have hqin : q ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22} : Finset ℕ) := by
    rcases hq with h4 | h5 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h20 | h21 | h22 <;> subst q <;> simp
  exact hdec q hqin k m r hr
/-- 转移保 legalStates：q ∈ detset 组 2（[76, 77, 81, 84, 85, 86, 87, 38]）。 -/
lemma transition_nextState_in_legal_det2 (q : ℕ) (s : Sym) (r : SymTransResult)
    (hq : q = 76 ∨ q = 77 ∨ q = 81 ∨ q = 84 ∨ q = 85 ∨ q = 86 ∨ q = 87 ∨ q = 38)
    (hr : r ∈ VerifierSym.transition (q, s)) :
    r.nextState ∈ VerifierSym.legalStates := by
  have hdec : ∀ q ∈ ({76, 77, 81, 84, 85, 86, 87, 38} : Finset ℕ),
      ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (q, Sym.mk k m) → r.nextState ∈ VerifierSym.legalStates := by
    native_decide
  rcases s with ⟨k, m⟩
  have hqin : q ∈ ({76, 77, 81, 84, 85, 86, 87, 38} : Finset ℕ) := by
    rcases hq with h76 | h77 | h81 | h84 | h85 | h86 | h87 | h38 <;> subst q <;> simp
  exact hdec q hqin k m r hr
/-- 转移保 legalStates：q ∈ detset 组 3（[23]）。 -/
lemma transition_nextState_in_legal_det3 (q : ℕ) (s : Sym) (r : SymTransResult)
    (hq : q = 23)
    (hr : r ∈ VerifierSym.transition (q, s)) :
    r.nextState ∈ VerifierSym.legalStates := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (23, Sym.mk k m) → r.nextState ∈ VerifierSym.legalStates := by
    native_decide
  subst q
  rcases s with ⟨k, m⟩
  exact hdec k m r hr
/-- 转移保 legalStates：q ∈ detset 时 nextState ∈ legalStates。 -/
lemma transition_nextState_in_legal_det (q : ℕ) (s : Sym) (r : SymTransResult)
    (hq : q ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 76, 77, 81, 84, 85, 86, 87, 38, 51, 23} : Finset ℕ))
    (hr : r ∈ VerifierSym.transition (q, s)) :
    r.nextState ∈ VerifierSym.legalStates := by
  by_cases hq51 : q = 51
  · subst q
    have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (51, Sym.mk k m) → r.nextState ∈ VerifierSym.legalStates := by
      native_decide
    rcases s with ⟨k, m⟩
    exact hdec k m r hr
  · have hq_cases : q = 4 ∨ q = 5 ∨ q = 8 ∨ q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 12 ∨ q = 13 ∨ q = 14 ∨ q = 20 ∨ q = 21 ∨ q = 22 ∨ q = 76 ∨ q = 77 ∨ q = 81 ∨ q = 84 ∨ q = 85 ∨ q = 86 ∨ q = 87 ∨ q = 38 ∨ q = 23 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq ⊢
      omega
    rcases hq_cases with h4 | h5 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h20 | h21 | h22 | h76 | h77 | h81 | h84 | h85 | h86 | h87 | h38 | h23
    · exact transition_nextState_in_legal_det1 q s r (by subst q; tauto) hr
    · exact transition_nextState_in_legal_det1 q s r (by subst q; tauto) hr
    · exact transition_nextState_in_legal_det1 q s r (by subst q; tauto) hr
    · exact transition_nextState_in_legal_det1 q s r (by subst q; tauto) hr
    · exact transition_nextState_in_legal_det1 q s r (by subst q; tauto) hr
    · exact transition_nextState_in_legal_det1 q s r (by subst q; tauto) hr
    · exact transition_nextState_in_legal_det1 q s r (by subst q; tauto) hr
    · exact transition_nextState_in_legal_det1 q s r (by subst q; tauto) hr
    · exact transition_nextState_in_legal_det1 q s r (by subst q; tauto) hr
    · exact transition_nextState_in_legal_det1 q s r (by subst q; tauto) hr
    · exact transition_nextState_in_legal_det1 q s r (by subst q; tauto) hr
    · exact transition_nextState_in_legal_det1 q s r (by subst q; tauto) hr
    · exact transition_nextState_in_legal_det2 q s r (by subst q; tauto) hr
    · exact transition_nextState_in_legal_det2 q s r (by subst q; tauto) hr
    · exact transition_nextState_in_legal_det2 q s r (by subst q; tauto) hr
    · exact transition_nextState_in_legal_det2 q s r (by subst q; tauto) hr
    · exact transition_nextState_in_legal_det2 q s r (by subst q; tauto) hr
    · exact transition_nextState_in_legal_det2 q s r (by subst q; tauto) hr
    · exact transition_nextState_in_legal_det2 q s r (by subst q; tauto) hr
    · exact transition_nextState_in_legal_det2 q s r (by subst q; tauto) hr
    · exact transition_nextState_in_legal_det3 q s r (by subst q; tauto) hr

/-- 转移保 legalStates：q < 4 时 nextState ∈ legalStates。 -/
lemma transition_nextState_in_legal_lt4 (q : ℕ) (s : Sym) (r : SymTransResult)
    (hq : q < 4) (hr : r ∈ VerifierSym.transition (q, s)) :
    r.nextState ∈ VerifierSym.legalStates := by
  interval_cases q
  · have hdec0 : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (0, Sym.mk k m) → r.nextState ∈ VerifierSym.legalStates := by
      native_decide
    rcases s with ⟨k, m⟩
    exact hdec0 k m r hr
  · rcases trans1_next1_or_2 s r hr with h1 | h2 | h101
    · simp [h1, VerifierSym.legalStates]
    · simp [h2, VerifierSym.legalStates]
    · simp [h101, VerifierSym.legalStates]
  · rcases trans2_next2_or_3 s r hr with h2 | h3 | h101
    · simp [h2, VerifierSym.legalStates]
    · simp [h3, VerifierSym.legalStates]
    · simp [h101, VerifierSym.legalStates]
  · rcases trans3_next3_or_4 s r hr with h24 | h101
    · simp [h24, VerifierSym.legalStates]
    · simp [h101, VerifierSym.legalStates]


open CBTM
open IVM
open F4

/-- 转移保 legalStates：q ∈ {24,26,27,28,29,100,101} 时 nextState ∈ legalStates。 -/
lemma transition_nextState_in_legal_rest (q : ℕ) (s : Sym) (r : SymTransResult)
    (hq : q = 24 ∨ q = 26 ∨ q = 27 ∨ q = 28 ∨ q = 29 ∨ q = 100 ∨ q = 101)
    (hr : r ∈ VerifierSym.transition (q, s)) :
    r.nextState ∈ VerifierSym.legalStates := by
  have hdec : ∀ q ∈ ({24, 26, 27, 28, 29, 100, 101} : Finset ℕ),
      ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (q, Sym.mk k m) → r.nextState ∈ VerifierSym.legalStates := by
    native_decide
  rcases s with ⟨k, m⟩
  have hqin : q ∈ ({24, 26, 27, 28, 29, 100, 101} : Finset ℕ) := by
    rcases hq with h24 | h26 | h27 | h28 | h29 | h100 | h101 <;> subst q <;> simp
  exact hdec q hqin k m r hr
/-- 转移保 legalStates：q ∈ legalStates → nextState ∈ legalStates。 -/
lemma transition_nextState_in_legal (q : ℕ) (s : Sym) (r : SymTransResult)
    (hq : q ∈ VerifierSym.legalStates) (hr : r ∈ VerifierSym.transition (q, s)) :
    r.nextState ∈ VerifierSym.legalStates := by
  by_cases hq4 : q < 4
  · exact transition_nextState_in_legal_lt4 q s r hq4 hr
  · by_cases hdet : q ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 76, 77, 81, 84, 85, 86, 87, 38, 51, 23} : Finset ℕ)
    · exact transition_nextState_in_legal_det q s r hdet hr
    · have hrest : q = 24 ∨ q = 26 ∨ q = 27 ∨ q = 28 ∨ q = 29 ∨ q = 100 ∨ q = 101 := by
        simp [VerifierSym.legalStates, Finset.mem_insert, Finset.mem_singleton] at hq hdet
        omega
      exact transition_nextState_in_legal_rest q s r hrest hr

/-- SymSteps 路径上的配置状态恒在合法状态集。 -/
lemma reachable_state_in_range {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition (symInitialConfig input) π cfg) :
    cfg.state ∈ VerifierSym.legalStates := by
  induction h with
  | nil => simp [symInitialConfig, VerifierSym.legalStates]
  | cons π₀ step cfg₀ h_ind h_from h_read h_trans ih =>
      have hnext : step.result.nextState ∈ VerifierSym.legalStates :=
        transition_nextState_in_legal cfg₀.state (cfg₀.tape cfg₀.headPos) step.result ih h_trans
      simpa [symStepConfig] using hnext


open CBTM
open IVM
open F4

/-- detset 内 nextState = 4 检查（[4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22]）。 -/
lemma transition_nextState_4_of_det1 (q : ℕ) (s : Sym) (r : SymTransResult)
    (hq : q = 4 ∨ q = 5 ∨ q = 8 ∨ q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 12 ∨ q = 13 ∨ q = 14 ∨ q = 20 ∨ q = 21 ∨ q = 22)
    (hr : r ∈ VerifierSym.transition (q, s)) (hnext : r.nextState = 4) :
    q = 28 ∨ q = 51 := by
  have hdec : ∀ q ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22} : Finset ℕ),
      ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (q, Sym.mk k m) → r.nextState = 4 → q = 28 ∨ q = 51 := by
    native_decide
  rcases s with ⟨k, m⟩
  have hqin : q ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22} : Finset ℕ) := by
    rcases hq with h4 | h5 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h20 | h21 | h22 <;> subst q <;> simp
  exact hdec q hqin k m r hr hnext
/-- detset 内 nextState = 4 检查（[76, 77, 81, 84, 85, 86, 87, 38]）。 -/
lemma transition_nextState_4_of_det2 (q : ℕ) (s : Sym) (r : SymTransResult)
    (hq : q = 76 ∨ q = 77 ∨ q = 81 ∨ q = 84 ∨ q = 85 ∨ q = 86 ∨ q = 87 ∨ q = 38)
    (hr : r ∈ VerifierSym.transition (q, s)) (hnext : r.nextState = 4) :
    q = 28 ∨ q = 51 := by
  have hdec : ∀ q ∈ ({76, 77, 81, 84, 85, 86, 87, 38} : Finset ℕ),
      ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (q, Sym.mk k m) → r.nextState = 4 → q = 28 ∨ q = 51 := by
    native_decide
  rcases s with ⟨k, m⟩
  have hqin : q ∈ ({76, 77, 81, 84, 85, 86, 87, 38} : Finset ℕ) := by
    rcases hq with h76 | h77 | h81 | h84 | h85 | h86 | h87 | h38 <;> subst q <;> simp
  exact hdec q hqin k m r hr hnext
/-- detset 内 nextState = 4 检查（[23]）。 -/
lemma transition_nextState_4_of_det3 (q : ℕ) (s : Sym) (r : SymTransResult)
    (hq : q = 23)
    (hr : r ∈ VerifierSym.transition (q, s)) (hnext : r.nextState = 4) :
    q = 28 ∨ q = 51 := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (23, Sym.mk k m) → r.nextState = 4 → 23 = 28 ∨ 23 = 51 := by
    native_decide
  subst q
  rcases s with ⟨k, m⟩
  exact hdec k m r hr hnext
/-- detset 内 nextState = 4 → q = 28 ∨ q = 51（21 态枚举）。 -/
lemma transition_nextState_4_of_det (q : ℕ) (s : Sym) (r : SymTransResult)
    (hq : q ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 76, 77, 81, 84, 85, 86, 87, 38, 51, 23} : Finset ℕ))
    (hr : r ∈ VerifierSym.transition (q, s)) (hnext : r.nextState = 4) :
    q = 28 ∨ q = 51 := by
  by_cases hq51 : q = 51
  · right
    exact hq51
  · have hq_cases : q = 4 ∨ q = 5 ∨ q = 8 ∨ q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 12 ∨ q = 13 ∨ q = 14 ∨ q = 20 ∨ q = 21 ∨ q = 22 ∨ q = 76 ∨ q = 77 ∨ q = 81 ∨ q = 84 ∨ q = 85 ∨ q = 86 ∨ q = 87 ∨ q = 38 ∨ q = 23 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq ⊢
      omega
    rcases hq_cases with h4 | h5 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h20 | h21 | h22 | h76 | h77 | h81 | h84 | h85 | h86 | h87 | h38 | h23
    · exact transition_nextState_4_of_det1 q s r (by subst q; tauto) hr hnext
    · exact transition_nextState_4_of_det1 q s r (by subst q; tauto) hr hnext
    · exact transition_nextState_4_of_det1 q s r (by subst q; tauto) hr hnext
    · exact transition_nextState_4_of_det1 q s r (by subst q; tauto) hr hnext
    · exact transition_nextState_4_of_det1 q s r (by subst q; tauto) hr hnext
    · exact transition_nextState_4_of_det1 q s r (by subst q; tauto) hr hnext
    · exact transition_nextState_4_of_det1 q s r (by subst q; tauto) hr hnext
    · exact transition_nextState_4_of_det1 q s r (by subst q; tauto) hr hnext
    · exact transition_nextState_4_of_det1 q s r (by subst q; tauto) hr hnext
    · exact transition_nextState_4_of_det1 q s r (by subst q; tauto) hr hnext
    · exact transition_nextState_4_of_det1 q s r (by subst q; tauto) hr hnext
    · exact transition_nextState_4_of_det1 q s r (by subst q; tauto) hr hnext
    · exact transition_nextState_4_of_det2 q s r (by subst q; tauto) hr hnext
    · exact transition_nextState_4_of_det2 q s r (by subst q; tauto) hr hnext
    · exact transition_nextState_4_of_det2 q s r (by subst q; tauto) hr hnext
    · exact transition_nextState_4_of_det2 q s r (by subst q; tauto) hr hnext
    · exact transition_nextState_4_of_det2 q s r (by subst q; tauto) hr hnext
    · exact transition_nextState_4_of_det2 q s r (by subst q; tauto) hr hnext
    · exact transition_nextState_4_of_det2 q s r (by subst q; tauto) hr hnext
    · exact transition_nextState_4_of_det2 q s r (by subst q; tauto) hr hnext
    · exact transition_nextState_4_of_det3 q s r (by subst q; tauto) hr hnext
/-- nextState = 4 的唯一来源：28（格式检查完）或 51（减法末位）。 -/
lemma transition_nextState_4_of (q : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (hnext : r.nextState = 4) :
    q = 28 ∨ q = 51 := by
  by_cases hqin : q ∈ VerifierSym.legalStates
  · by_cases hq4 : q < 4
    · -- 0-3 态：nextState ≠ 4
      exfalso
      interval_cases q
      · have hdec0 : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
            r ∈ VerifierSym.transition (0, Sym.mk k m) → r.nextState ≠ 4 := by
          native_decide
        rcases s with ⟨k, m⟩
        exact (hdec0 k m r hr) hnext
      · rcases trans1_next1_or_2 s r hr with h1 | h2 | h101
        · rw [h1] at hnext; norm_num at hnext
        · rw [h2] at hnext; norm_num at hnext
        · rw [h101] at hnext; norm_num at hnext
      · rcases trans2_next2_or_3 s r hr with h2 | h3 | h101
        · rw [h2] at hnext; norm_num at hnext
        · rw [h3] at hnext; norm_num at hnext
        · rw [h101] at hnext; norm_num at hnext
      · rcases trans3_next3_or_4 s r hr with h24 | h101
        · rw [h24] at hnext; norm_num at hnext
        · rw [h101] at hnext; norm_num at hnext
    · by_cases hdet : q ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 76, 77, 81, 84, 85, 86, 87, 38, 51, 23} : Finset ℕ)
      · exact transition_nextState_4_of_det q s r hdet hr hnext
      · have hrest : q = 24 ∨ q = 26 ∨ q = 27 ∨ q = 28 ∨ q = 29 ∨ q = 100 ∨ q = 101 := by
          simp [VerifierSym.legalStates, Finset.mem_insert, Finset.mem_singleton] at hqin hdet
          omega
        have hdec' : ∀ q ∈ ({24, 26, 27, 28, 29, 100, 101} : Finset ℕ),
            ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
              r ∈ VerifierSym.transition (q, Sym.mk k m) → r.nextState = 4 → q = 28 ∨ q = 51 := by
          native_decide
        rcases s with ⟨k, m⟩
        have hqin' : q ∈ ({24, 26, 27, 28, 29, 100, 101} : Finset ℕ) := by
          rcases hrest with h24 | h26 | h27 | h28 | h29 | h100 | h101 <;> subst q <;> simp
        exact hdec' q hqin' k m r hr hnext
  · simp only [VerifierSym.transition, if_neg hqin, Finset.mem_singleton] at hr
    subst r
    exfalso
    norm_num at hnext

/-- 从初始配置出发、以状态 4 结束的路径：最后一步必为 28→4 或 51→4。 -/
lemma split_at_state4 {input : List Sym} (π : List SymStep) (cfg : SymConfig)
    (hstart : (symInitialConfig input).tape 0 = Sym.boundary) :
    SymSteps VerifierSym.transition (symInitialConfig input) π cfg →
    cfg.state = 4 →
    ∃ π₀₃ step₃ cfg₃ π₂,
      π = (π₀₃ ++ [step₃]) ++ π₂ ∧
      SymSteps VerifierSym.transition (symInitialConfig input) π₀₃ cfg₃ ∧
      (cfg₃.state = 28 ∨ cfg₃.state = 51) ∧
      cfg = symStepConfig cfg₃ step₃.result ∧
      SymSteps VerifierSym.transition cfg π₂ cfg := by
  intro h h4
  induction h with
  | nil =>
      exfalso
      change (symInitialConfig input).state = 4 at h4
      simp [symInitialConfig] at h4
  | cons π₀ step cfg₀ h_ind h_from h_read h_trans ih =>
      have hnext4 : step.result.nextState = 4 := by
        simpa [symStepConfig] using h4
      rcases transition_nextState_4_of cfg₀.state (cfg₀.tape cfg₀.headPos) step.result h_trans hnext4 with h28 | h51
      · refine ⟨π₀, step, cfg₀, [], by simp, h_ind, Or.inl h28, rfl, SymSteps.nil⟩
      · refine ⟨π₀, step, cfg₀, [], by simp, h_ind, Or.inr h51, rfl, SymSteps.nil⟩


end Mp
