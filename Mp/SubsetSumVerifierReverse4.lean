/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import Mp.SubsetSumVerifierReverse3

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
set_option maxHeartbeats 8000000

namespace Mp
open CBTM

-- q11a:格式检查段分解(π₁ = π₀₂ ++ [2→3] ++ [3→24] ++ fmt 步)
-- ===================================================

/-- π₁ 的段分解:2→3 步前状态 ∈ {0,1,2};2→3 后状态 3;3→24 后 fmt 步直至 4。 -/
lemma pi1_fmt_split (input : List Sym) (π₁ : List SymStep) (cfg₄ : SymConfig)
    (hπ₁ : SymSteps VerifierSym.transition (symInitialConfig input) π₁ cfg₄)
    (hno4 : ∀ {π₀ : List SymStep} {cfg₀ : SymConfig},
      SymSteps VerifierSym.transition (symInitialConfig input) π₀ cfg₀ →
      (∃ ρ, π₁ = π₀ ++ ρ) → π₀.length < π₁.length → cfg₀.state ≠ 4)
    (hno101 : ∀ step ∈ π₁, step.result.nextState ≠ 101)
    (hs4 : cfg₄.state = 4) :
    ∃ π₀₂ πfmt : List SymStep, ∃ step₂₃ step₃₂₄ : SymStep, ∃ cfg₂ cfg₃ : SymConfig,
      π₁ = π₀₂ ++ [step₂₃] ++ [step₃₂₄] ++ πfmt ∧
      SymSteps VerifierSym.transition (symInitialConfig input) π₀₂ cfg₂ ∧
      cfg₂.state = 2 ∧
      (∃ n₁ i : ℕ, cfg₂.headPos = 2 + (n₁ : ℤ) + (i : ℤ) ∧
        ((symInitialConfig input).tape (1 + (n₁ : ℤ))).1 = SymKind.boundary ∧
        (∀ j : ℕ, j < i → ((symInitialConfig input).tape (2 + (n₁ : ℤ) + (j : ℤ))).1 = SymKind.alpha ∨
          ((symInitialConfig input).tape (2 + (n₁ : ℤ) + (j : ℤ))).1 = SymKind.data0 ∨
          ((symInitialConfig input).tape (2 + (n₁ : ℤ) + (j : ℤ))).1 = SymKind.data1) ∧
        (∀ j : ℕ, j < n₁ → ((symInitialConfig input).tape (1 + (j : ℤ))).1 = SymKind.data0 ∨
          ((symInitialConfig input).tape (1 + (j : ℤ))).1 = SymKind.data1)) ∧
      step₂₃.fromState = 2 ∧ step₂₃.result.nextState = 3 ∧
      step₂₃.readSym = cfg₂.tape cfg₂.headPos ∧
      step₂₃.result ∈ VerifierSym.transition (2, cfg₂.tape cfg₂.headPos) ∧
      cfg₂.tape cfg₂.headPos = (symInitialConfig input).tape cfg₂.headPos ∧
      cfg₃ = symStepConfig cfg₂ step₂₃.result ∧
      step₃₂₄.fromState = 3 ∧ step₃₂₄.result.nextState = 24 ∧
      step₃₂₄.readSym = cfg₃.tape cfg₃.headPos ∧
      step₃₂₄.result ∈ VerifierSym.transition (3, cfg₃.tape cfg₃.headPos) ∧
      SymSteps VerifierSym.transition (symStepConfig cfg₃ step₃₂₄.result) πfmt cfg₄ ∧
      (∀ step ∈ πfmt, step.fromState ∈ fmtStates) := by
  let P : List SymStep → SymConfig → Prop := fun π₀ cfg₁ =>
    (((cfg₁.state = 0 ∧ cfg₁.headPos = 0) ∨
      (∃ n₁ : ℕ, cfg₁.state = 1 ∧ cfg₁.headPos = 1 + (n₁ : ℤ) ∧
        (∀ j : ℕ, j < n₁ → ((symInitialConfig input).tape (1 + (j : ℤ))).1 = SymKind.data0 ∨
          ((symInitialConfig input).tape (1 + (j : ℤ))).1 = SymKind.data1)) ∨
      (∃ n₁ i : ℕ, cfg₁.state = 2 ∧ cfg₁.headPos = 2 + (n₁ : ℤ) + (i : ℤ) ∧
        ((symInitialConfig input).tape (1 + (n₁ : ℤ))).1 = SymKind.boundary ∧
        (∀ j : ℕ, j < i → ((symInitialConfig input).tape (2 + (n₁ : ℤ) + (j : ℤ))).1 = SymKind.alpha ∨
          ((symInitialConfig input).tape (2 + (n₁ : ℤ) + (j : ℤ))).1 = SymKind.data0 ∨
          ((symInitialConfig input).tape (2 + (n₁ : ℤ) + (j : ℤ))).1 = SymKind.data1) ∧
        (∀ j : ℕ, j < n₁ → ((symInitialConfig input).tape (1 + (j : ℤ))).1 = SymKind.data0 ∨
          ((symInitialConfig input).tape (1 + (j : ℤ))).1 = SymKind.data1))) ∧
      ∀ j : ℤ, cfg₁.headPos ≤ j → cfg₁.tape j = (symInitialConfig input).tape j) ∨
    (∃ π₀₂ : List SymStep, ∃ step₂₃ : SymStep, ∃ cfg₂ : SymConfig,
      π₀ = π₀₂ ++ [step₂₃] ∧
      SymSteps VerifierSym.transition (symInitialConfig input) π₀₂ cfg₂ ∧
      cfg₂.state = 2 ∧
      (∃ n₁ i : ℕ, cfg₂.headPos = 2 + (n₁ : ℤ) + (i : ℤ) ∧
        ((symInitialConfig input).tape (1 + (n₁ : ℤ))).1 = SymKind.boundary ∧
        (∀ j : ℕ, j < i → ((symInitialConfig input).tape (2 + (n₁ : ℤ) + (j : ℤ))).1 = SymKind.alpha ∨
          ((symInitialConfig input).tape (2 + (n₁ : ℤ) + (j : ℤ))).1 = SymKind.data0 ∨
          ((symInitialConfig input).tape (2 + (n₁ : ℤ) + (j : ℤ))).1 = SymKind.data1) ∧
        (∀ j : ℕ, j < n₁ → ((symInitialConfig input).tape (1 + (j : ℤ))).1 = SymKind.data0 ∨
          ((symInitialConfig input).tape (1 + (j : ℤ))).1 = SymKind.data1)) ∧
      step₂₃.fromState = 2 ∧ step₂₃.result.nextState = 3 ∧
      step₂₃.readSym = cfg₂.tape cfg₂.headPos ∧
      step₂₃.result ∈ VerifierSym.transition (2, cfg₂.tape cfg₂.headPos) ∧
      cfg₂.tape cfg₂.headPos = (symInitialConfig input).tape cfg₂.headPos ∧
      cfg₁ = symStepConfig cfg₂ step₂₃.result) ∨
    (∃ π₀₂ πfmt₀ : List SymStep, ∃ step₂₃ step₃₂₄ : SymStep, ∃ cfg₂ cfg₃ : SymConfig,
      π₀ = π₀₂ ++ [step₂₃] ++ [step₃₂₄] ++ πfmt₀ ∧
      SymSteps VerifierSym.transition (symInitialConfig input) π₀₂ cfg₂ ∧
      cfg₂.state = 2 ∧
      (∃ n₁ i : ℕ, cfg₂.headPos = 2 + (n₁ : ℤ) + (i : ℤ) ∧
        ((symInitialConfig input).tape (1 + (n₁ : ℤ))).1 = SymKind.boundary ∧
        (∀ j : ℕ, j < i → ((symInitialConfig input).tape (2 + (n₁ : ℤ) + (j : ℤ))).1 = SymKind.alpha ∨
          ((symInitialConfig input).tape (2 + (n₁ : ℤ) + (j : ℤ))).1 = SymKind.data0 ∨
          ((symInitialConfig input).tape (2 + (n₁ : ℤ) + (j : ℤ))).1 = SymKind.data1) ∧
        (∀ j : ℕ, j < n₁ → ((symInitialConfig input).tape (1 + (j : ℤ))).1 = SymKind.data0 ∨
          ((symInitialConfig input).tape (1 + (j : ℤ))).1 = SymKind.data1)) ∧
      step₂₃.fromState = 2 ∧ step₂₃.result.nextState = 3 ∧
      step₂₃.readSym = cfg₂.tape cfg₂.headPos ∧
      step₂₃.result ∈ VerifierSym.transition (2, cfg₂.tape cfg₂.headPos) ∧
      cfg₂.tape cfg₂.headPos = (symInitialConfig input).tape cfg₂.headPos ∧
      cfg₃ = symStepConfig cfg₂ step₂₃.result ∧
      step₃₂₄.fromState = 3 ∧ step₃₂₄.result.nextState = 24 ∧
      step₃₂₄.readSym = cfg₃.tape cfg₃.headPos ∧
      step₃₂₄.result ∈ VerifierSym.transition (3, cfg₃.tape cfg₃.headPos) ∧
      SymSteps VerifierSym.transition (symStepConfig cfg₃ step₃₂₄.result) πfmt₀ cfg₁ ∧
      (∀ step ∈ πfmt₀, step.fromState ∈ fmtStates) ∧
      (cfg₁.state ∈ fmtStates ∨ cfg₁.state = 4))
  have hd0 : ∀ k m r, r ∈ VerifierSym.transition (0, (k, m)) → r.nextState ≠ 101 →
      r.nextState = 1 := by
    native_decide
  have hd1 : ∀ k m r, r ∈ VerifierSym.transition (1, (k, m)) → r.nextState ≠ 101 →
      r.nextState = 1 ∨ r.nextState = 2 := by
    native_decide
  have hd2 : ∀ k m r, r ∈ VerifierSym.transition (2, (k, m)) → r.nextState ≠ 101 →
      r.nextState = 2 ∨ r.nextState = 3 := by
    native_decide
  have hd3 : ∀ k m r, r ∈ VerifierSym.transition (3, (k, m)) → r.nextState ≠ 101 →
      r.nextState = 24 := by
    native_decide
  have hP : P π₁ cfg₄ := by
    clear hs4
    induction hπ₁ with
    | nil =>
        left
        constructor
        · left
          exact ⟨rfl, rfl⟩
        · intro j hj
          rfl
    | cons π₀ step cfg₀ h_ind h_from h_read h_trans ih =>
        have hno4₀ : ∀ {π₀' : List SymStep} {cfg₀' : SymConfig},
            SymSteps VerifierSym.transition (symInitialConfig input) π₀' cfg₀' →
            (∃ ρ, π₀ = π₀' ++ ρ) → π₀'.length < π₀.length → cfg₀'.state ≠ 4 := by
          intro π₀' cfg₀' h₀' hpre' hlen'
          exact hno4 h₀' (by
            rcases hpre' with ⟨ρ', hρ'⟩
            refine ⟨ρ' ++ [step], ?_⟩
            change (π₀ ++ [step]) = π₀' ++ (ρ' ++ [step])
            rw [hρ']
            simp [List.append_assoc]) (by
            simpa [List.length_append] using Nat.le_of_lt hlen')
        have hno101step : step.result.nextState ≠ 101 := hno101 step (by simp)
        have hno101₀ : ∀ step ∈ π₀, step.result.nextState ≠ 101 :=
          fun step h => hno101 step (by rw [List.mem_append]; left; exact h)
        rcases ih hno4₀ hno101₀ with hA | hB | hC
        · -- 状态 ∈ {0,1,2}
          rcases hA with ⟨hAform, hAagr⟩
          have hstate3 : cfg₀.state = 0 ∨ cfg₀.state = 1 ∨ cfg₀.state = 2 := by
            rcases hAform with h0 | h1 | h2
            · exact Or.inl h0.1
            · rcases h1 with ⟨_, hst1, _, _⟩
              exact Or.inr (Or.inl hst1)
            · rcases h2 with ⟨_, _, hst2, _, _, _⟩
              exact Or.inr (Or.inr hst2)
          have hqmem : cfg₀.state ∈ ({0, 1, 2} : Finset ℕ) := by
            rcases hstate3 with h | h | h <;> rw [h] <;> decide
          have htr0 : step.result ∈ VerifierSym.transition (cfg₀.state, step.readSym) := by
            rw [← h_read] at h_trans
            exact h_trans
          have hnext : step.result.nextState ∈ ({0, 1, 2} : Finset ℕ) ∨ step.result.nextState = 3 := by
            have hdec : ∀ q ∈ ({0, 1, 2} : Finset ℕ), ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition (q, (k, m)) → r.nextState ≠ 101 →
                r.nextState ∈ ({0, 1, 2} : Finset ℕ) ∨ r.nextState = 3 := by
              native_decide
            exact hdec cfg₀.state hqmem step.readSym.1 step.readSym.2 step.result htr0 hno101step
          rcases hnext with hnextA | hnext3
          · -- 留在 {0,1,2}
            have hdR : step.result.moveDir = Dir.R := by
              have hdec : ∀ q ∈ ({0, 1, 2} : Finset ℕ), ∀ k : SymKind, ∀ m : Bool,
                  ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition (q, (k, m)) →
                  r.nextState ∈ ({0, 1, 2} : Finset ℕ) → r.moveDir = Dir.R := by
                native_decide
              exact hdec cfg₀.state hqmem step.readSym.1 step.readSym.2 step.result htr0 hnextA
            have hright' : ∀ j : ℤ, (symStepConfig cfg₀ step.result).headPos ≤ j →
                (symStepConfig cfg₀ step.result).tape j = (symInitialConfig input).tape j := by
              intro j hj
              dsimp [symStepConfig]
              have hj' : j ≠ cfg₀.headPos := by
                intro heq
                rw [heq] at hj
                simp [symStepConfig, hdR, Dir.toInt] at hj
              rw [if_neg hj']
              have hjagr : cfg₀.headPos ≤ j := by
                dsimp [symStepConfig] at hj
                rw [hdR] at hj
                dsimp [Dir.toInt] at hj
                omega
              exact hAagr j hjagr
            rcases hAform with hA0 | hA1 | hA2
            · -- 0 → 1
              rcases hA0 with ⟨_hst0, hhead0⟩
              have hnext1 : step.result.nextState = 1 := by
                have hdec : ∀ k m r, r ∈ VerifierSym.transition (0, (k, m)) → r.nextState ≠ 101 →
                    r.nextState = 1 := by
                  native_decide
                exact hdec _ _ _ (by simpa [_hst0] using htr0) hno101step
              left
              constructor
              · right; left
                refine ⟨0, by simpa [symStepConfig] using hnext1, ?_, ?_⟩
                · dsimp [symStepConfig]
                  rw [hhead0, hdR]
                  simp [Dir.toInt, Int.add_assoc, Int.add_comm, Int.add_left_comm]
                · intro j hj
                  omega
              · exact hright'
            · -- 1 → 1 / 1 → 2
              rcases hA1 with ⟨n₁, hst1, hhead₁, hd₁⟩
              have hkind3 : step.readSym.1 = SymKind.data0 ∨ step.readSym.1 = SymKind.data1 ∨
                  step.readSym.1 = SymKind.boundary := by
                have hdec : ∀ k m r, r ∈ VerifierSym.transition (1, (k, m)) → r.nextState ≠ 101 →
                    k = SymKind.data0 ∨ k = SymKind.data1 ∨ k = SymKind.boundary := by
                  native_decide
                exact hdec _ _ _ (by simpa [hst1] using htr0) hno101step
              rcases hkind3 with hd0' | hd1' | hb'
              · -- data0 → 1
                have hnext1 : step.result.nextState = 1 := by
                  have hdec : ∀ k m r, r ∈ VerifierSym.transition (1, (k, m)) → k = SymKind.data0 →
                      r.nextState = 1 := by
                    native_decide
                  exact hdec _ _ _ (by simpa [hst1] using htr0) hd0'
                left
                constructor
                · right; left
                  refine ⟨n₁ + 1, by simpa [symStepConfig] using hnext1, ?_, ?_⟩
                  · dsimp [symStepConfig]
                    rw [hhead₁, hdR]
                    simp [Dir.toInt, Int.add_assoc, Int.add_comm, Int.add_left_comm]
                  · intro j hj
                    have hjl : j < n₁ ∨ j = n₁ := by omega
                    rcases hjl with hjlt | hjeq
                    · exact hd₁ j hjlt
                    · subst j
                      have hreadcell : (symInitialConfig input).tape (1 + (n₁ : ℤ)) = step.readSym := by
                        calc
                          (symInitialConfig input).tape (1 + (n₁ : ℤ))
                              = (symInitialConfig input).tape cfg₀.headPos := by rw [hhead₁]
                          _ = cfg₀.tape cfg₀.headPos := (hAagr cfg₀.headPos (le_rfl)).symm
                          _ = step.readSym := h_read.symm
                      rw [hreadcell]
                      exact Or.inl hd0'
                · exact hright'
              · -- data1 → 1
                have hnext1 : step.result.nextState = 1 := by
                  have hdec : ∀ k m r, r ∈ VerifierSym.transition (1, (k, m)) → k = SymKind.data1 →
                      r.nextState = 1 := by
                    native_decide
                  exact hdec _ _ _ (by simpa [hst1] using htr0) hd1'
                left
                constructor
                · right; left
                  refine ⟨n₁ + 1, by simpa [symStepConfig] using hnext1, ?_, ?_⟩
                  · dsimp [symStepConfig]
                    rw [hhead₁, hdR]
                    simp [Dir.toInt, Int.add_assoc, Int.add_comm, Int.add_left_comm]
                  · intro j hj
                    have hjl : j < n₁ ∨ j = n₁ := by omega
                    rcases hjl with hjlt | hjeq
                    · exact hd₁ j hjlt
                    · subst j
                      have hreadcell : (symInitialConfig input).tape (1 + (n₁ : ℤ)) = step.readSym := by
                        calc
                          (symInitialConfig input).tape (1 + (n₁ : ℤ))
                              = (symInitialConfig input).tape cfg₀.headPos := by rw [hhead₁]
                          _ = cfg₀.tape cfg₀.headPos := (hAagr cfg₀.headPos (le_rfl)).symm
                          _ = step.readSym := h_read.symm
                      rw [hreadcell]
                      exact Or.inr hd1'
                · exact hright'
              · -- boundary → 2
                have hnext2 : step.result.nextState = 2 := by
                  have hdec : ∀ k m r, r ∈ VerifierSym.transition (1, (k, m)) → k = SymKind.boundary →
                      r.nextState = 2 := by
                    native_decide
                  exact hdec _ _ _ (by simpa [hst1] using htr0) hb'
                left
                constructor
                · right; right
                  refine ⟨n₁, 0, by simpa [symStepConfig] using hnext2, ?_, ?_, ?_, hd₁⟩
                  · dsimp [symStepConfig]
                    rw [hhead₁, hdR]
                    simp [Dir.toInt, Int.add_assoc, Int.add_comm, Int.add_left_comm]
                  · -- 1→2 读格 = 边界(1+n₁)
                    have hreadcell : (symInitialConfig input).tape (1 + (n₁ : ℤ)) = step.readSym := by
                      calc
                        (symInitialConfig input).tape (1 + (n₁ : ℤ))
                            = (symInitialConfig input).tape cfg₀.headPos := by rw [hhead₁]
                        _ = cfg₀.tape cfg₀.headPos := (hAagr cfg₀.headPos (le_rfl)).symm
                        _ = step.readSym := h_read.symm
                    rw [hreadcell]
                    exact hb'
                  · intro j hj
                    omega
                · exact hright'
            · -- 2 → 2
              rcases hA2 with ⟨n₁, i, hst2, hhead₂, hbnd₁, helems, hd₁⟩
              have hkind : step.readSym.1 = SymKind.alpha ∨ step.readSym.1 = SymKind.data0 ∨
                  step.readSym.1 = SymKind.data1 := by
                have hdec : ∀ k m r, r ∈ VerifierSym.transition (2, (k, m)) →
                    r.nextState ∈ ({0, 1, 2} : Finset ℕ) →
                    k = SymKind.alpha ∨ k = SymKind.data0 ∨ k = SymKind.data1 := by
                  native_decide
                exact hdec _ _ _ (by simpa [hst2] using htr0) hnextA
              have hnext2 : step.result.nextState = 2 := by
                have hdec : ∀ k m r, r ∈ VerifierSym.transition (2, (k, m)) →
                    r.nextState ∈ ({0, 1, 2} : Finset ℕ) → r.nextState = 2 := by
                  native_decide
                exact hdec _ _ _ (by simpa [hst2] using htr0) hnextA
              left
              constructor
              · right; right
                refine ⟨n₁, i + 1, by simpa [symStepConfig] using hnext2, ?_, hbnd₁, ?_, hd₁⟩
                · dsimp [symStepConfig]
                  rw [hhead₂, hdR]
                  simp [Dir.toInt, Int.add_assoc, Int.add_comm, Int.add_left_comm]
                · intro j hj
                  have hjl : j < i ∨ j = i := by omega
                  rcases hjl with hjlt | hjeq
                  · exact helems j hjlt
                  · subst j
                    have hreadcell : (symInitialConfig input).tape (2 + (n₁ : ℤ) + (i : ℤ)) = step.readSym := by
                      calc
                        (symInitialConfig input).tape (2 + (n₁ : ℤ) + (i : ℤ))
                            = (symInitialConfig input).tape cfg₀.headPos := by rw [hhead₂]
                        _ = cfg₀.tape cfg₀.headPos := (hAagr cfg₀.headPos (le_rfl)).symm
                        _ = step.readSym := h_read.symm
                    rw [hreadcell]
                    exact hkind
              · exact hright'
          · -- 2 → 3:进入状态 3 段
            have hst2' : cfg₀.state = 2 := by
              have hdec : ∀ q ∈ ({0, 1, 2} : Finset ℕ), ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition (q, (k, m)) → r.nextState = 3 → q = 2 := by
                native_decide
              exact hdec cfg₀.state hqmem step.readSym.1 step.readSym.2 step.result htr0 hnext3
            rcases hAform with hA0 | hA1 | hA2
            · rw [hA0.1] at hst2'
              norm_num at hst2'
            · rcases hA1 with ⟨_, hst1', _, _⟩
              rw [hst1'] at hst2'
              norm_num at hst2'
            · rcases hA2 with ⟨n₁, i, _hst2'', hhead₂, hbnd₁, helems, hd₁⟩
              right; left
              refine ⟨π₀, step, cfg₀, rfl, h_ind, hst2', ⟨n₁, i, hhead₂, hbnd₁, helems, hd₁⟩,
                by simpa [hst2'] using h_from, hnext3, h_read,
                by simpa [hst2', h_read] using htr0, ?_, rfl⟩
              · exact hAagr cfg₀.headPos (le_rfl)
        · -- 状态 3:当前步 = 3→24
          rcases hB with ⟨π₀₂, step₂₃, cfg₂, hπeq, hSym, hst2, hexp, hf23, hn23, hr23, ht23, hbr, hcfg₃⟩
          have hst3 : cfg₀.state = 3 := by
            rw [hcfg₃]
            dsimp [symStepConfig]
            simpa using hn23
          have htr : step.result ∈ VerifierSym.transition (3, step.readSym) := by
            rw [hst3] at h_trans
            rw [← h_read] at h_trans
            exact h_trans
          have hnext24 : step.result.nextState = 24 := hd3 _ _ _ htr hno101step
          right; right
          refine ⟨π₀₂, [], step₂₃, step, cfg₂, cfg₀, ?_, hSym, hst2, hexp, hf23, hn23, hr23, ht23,
            hbr, hcfg₃, by simpa [hst3] using h_from, hnext24, h_read,
            by simpa [hst3, h_read] using h_trans,
            SymSteps.nil, ?_, ?_⟩
          · rw [hπeq]
            simp
          · intro s hs
            simp at hs
          · left
            dsimp [symStepConfig]
            rw [hnext24]
            decide
        · -- fmt 段:当前步的 fromState ∈ fmtStates 或 4
          rcases hC with ⟨π₀₂, πfmt₀, step₂₃, step₃₂₄, cfg₂, cfg₃, hπeq, hSym, hst2, hexp,
            hf23, hn23, hr23, ht23, hbr, hcfg₃, hf324, hn324, hr324, ht324, hSymf, hfm₀, hstfin⟩
          rcases hstfin with hF | h4₀
          · have hwsame := pre4_fmt_write_same_next cfg₀.state (cfg₀.tape cfg₀.headPos) step.result
              hF h_trans hno101step
            have hnext := hwsame.2
            right; right
            refine ⟨π₀₂, πfmt₀ ++ [step], step₂₃, step₃₂₄, cfg₂, cfg₃, ?_, hSym, hst2, hexp,
              hf23, hn23, hr23, ht23, hbr, hcfg₃, hf324, hn324, hr324, ht324,
              ?_, ?_, hnext⟩
            · rw [hπeq]
              rw [List.append_assoc, List.append_assoc]
            · exact SymSteps.cons πfmt₀ step cfg₀ hSymf h_from h_read h_trans
            · intro s hs
              rw [List.mem_append] at hs
              rcases hs with h | h
              · exact hfm₀ s h
              · simp at h
                rw [h]
                exact h_from ▸ hF
          · exfalso
            exact (hno4 h_ind ⟨[step], rfl⟩ (by simp)) h4₀
  rcases hP with hA' | hB' | hC'
  · exfalso
    rcases hA'.1 with h0 | h1 | h2
    · rcases h0 with ⟨hst0, _⟩
      rw [hst0] at hs4
      norm_num at hs4
    · rcases h1 with ⟨_, hst1, _, _⟩
      rw [hst1] at hs4
      norm_num at hs4
    · rcases h2 with ⟨_, _, hst2, _, _, _⟩
      rw [hst2] at hs4
      norm_num at hs4
  · rcases hB' with ⟨_, step₂₃, _, _, _, _, _, _, hn23, _, _, _, hcfg₃⟩
    exfalso
    have hst : cfg₄.state = 3 := by
      rw [hcfg₃]
      simpa [symStepConfig] using hn23
    rw [hst] at hs4
    norm_num at hs4
  · rcases hC' with ⟨π₀₂, πfmt, step₂₃, step₃₂₄, cfg₂, cfg₃, hπeq, hSym, hst2, hexp,
      hf23, hn23, hr23, ht23, hbr, hcfg₃, hf324, hn324, hr324, ht324, hSymf, hfm, _⟩
    refine ⟨π₀₂, πfmt, step₂₃, step₃₂₄, cfg₂, cfg₃, hπeq, hSym, hst2, hexp, hf23, hn23, hr23, ht23,
      hbr, hcfg₃, hf324, hn324, hr324, ht324, hSymf, hfm⟩

-- ===================================================
-- q11a:格式检查行走(format_check_precise)
-- ===================================================

/-- fmt 段的各步写回读格(磁带不变)。 -/
lemma fmt_tape_unchanged (cfg₂₄ cfg₄ : SymConfig) (πfmt : List SymStep)
    (hSymf : SymSteps VerifierSym.transition cfg₂₄ πfmt cfg₄)
    (hfm : ∀ step ∈ πfmt, step.fromState ∈ fmtStates)
    (hno101 : ∀ step ∈ πfmt, step.result.nextState ≠ 101) :
    cfg₄.tape = cfg₂₄.tape := by
  funext j
  induction hSymf with
  | nil => rfl
  | cons π₀ step cfg₁ h_ind h_from h_read h_trans ih =>
      have hwsame := pre4_fmt_write_same_next cfg₁.state (cfg₁.tape cfg₁.headPos) step.result
        (by simpa [← h_from] using hfm step (by simp)) h_trans (hno101 step (by simp))
      rw [show (symStepConfig cfg₁ step.result).tape j = cfg₁.tape j from by
        dsimp [symStepConfig]
        by_cases hj : j = cfg₁.headPos
        · rw [hj, hwsame.1]
          simp
        · rw [if_neg hj]]
      exact ih (fun step h => hfm step (by simp [h])) (fun step h => hno101 step (by simp [h]))

-- fmt 行走的读格桥接辅助引理

/-- 29 支 data 读(→29):读格输入值 = (data0|data1, false)。 -/
lemma step29_data_cell (input : List Sym) (n len j : ℕ) (cfg₄ cfg₁ : SymConfig) (step : SymStep)
    (hhead : cfg₁.headPos = (n : ℤ) + 2 + (j : ℤ))
    (htapep : cfg₁.tape cfg₁.headPos = cfg₄.tape cfg₁.headPos)
    (htrans : step.result ∈ VerifierSym.transition (29, cfg₁.tape cfg₁.headPos))
    (hnext29 : step.result.nextState = 29)
    (hws : cfg₄.tape ((n : ℤ) + 2 + (j : ℤ)) = Sym.sel ∨
        cfg₄.tape ((n : ℤ) + 2 + (j : ℤ)) = Sym.nosel ∨
        cfg₄.tape ((n : ℤ) + 2 + (j : ℤ)) = (symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ))) :
    ((symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ))).2 = false := by
  have hdec : ∀ k m r, r ∈ VerifierSym.transition (29, (k, m)) → r.nextState = 29 →
      m = false ∧ (k = SymKind.data0 ∨ k = SymKind.data1) := by
    native_decide
  have hread' := hdec (cfg₁.tape cfg₁.headPos).1 (cfg₁.tape cfg₁.headPos).2 step.result htrans hnext29
  rcases hws with hsel | hnosel | horig
  · exfalso
    rw [← hhead] at hsel
    have hk : (cfg₁.tape cfg₁.headPos).1 = SymKind.sel := by
      rw [htapep]
      exact congrArg (fun s : Sym => s.1) hsel
    rcases hread'.2 with hd0 | hd1
    · rw [hd0] at hk
      cases hk
    · rw [hd1] at hk
      cases hk
  · exfalso
    rw [← hhead] at hnosel
    have hk : (cfg₁.tape cfg₁.headPos).1 = SymKind.nosel := by
      rw [htapep]
      exact congrArg (fun s : Sym => s.1) hnosel
    rcases hread'.2 with hd0 | hd1
    · rw [hd0] at hk
      cases hk
    · rw [hd1] at hk
      cases hk
  · rw [← hhead] at horig
    have hfull : (symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ)) = (SymKind.data0, false) ∨
        (symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ)) = (SymKind.data1, false) := by
      have hk := hread'.2
      have hm := hread'.1
      rcases hk with hk0 | hk1
      · left
        rw [← hhead, ← horig, ← htapep]
        rw [show cfg₁.tape cfg₁.headPos = ((cfg₁.tape cfg₁.headPos).1, (cfg₁.tape cfg₁.headPos).2) from rfl]
        rw [hk0, hm]
      · right
        rw [← hhead, ← horig, ← htapep]
        rw [show cfg₁.tape cfg₁.headPos = ((cfg₁.tape cfg₁.headPos).1, (cfg₁.tape cfg₁.headPos).2) from rfl]
        rw [hk1, hm]
    rcases hfull with hf | hf <;> exact congrArg (fun s : Sym => s.2) hf

/-- 元素格的 sel/nosel 写入仅源于状态 2 的 α 读。 -/
lemma elem_cell_sel_implies_input_alpha (input : List Sym) (π₁ : List SymStep) (cfg₄ : SymConfig)
    (hπ₁ : SymSteps VerifierSym.transition (symInitialConfig input) π₁ cfg₄)
    (hno4 : ∀ {π₀ : List SymStep} {cfg₀ : SymConfig},
      SymSteps VerifierSym.transition (symInitialConfig input) π₀ cfg₀ →
      (∃ ρ : List SymStep, π₁ = π₀ ++ ρ) → π₀.length < π₁.length → cfg₀.state ≠ 4)
    (hno101 : ∀ step ∈ π₁, step.result.nextState ≠ 101)
    (n len j : ℕ) (hj : j < len)
    (hkind₃ : ((symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.alpha ∨
        ((symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.data0 ∨
        ((symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.data1) :
    cfg₄.tape ((n : ℤ) + 2 + (j : ℤ)) = Sym.sel ∨
      cfg₄.tape ((n : ℤ) + 2 + (j : ℤ)) = Sym.nosel →
    ((symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.alpha := by
  let S : ℕ → Prop := fun q => q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 24 ∨ q = 29 ∨ q = 26 ∨
    q = 27 ∨ q = 38 ∨ q = 28
  let Q : SymConfig → Prop := fun cfg =>
    (S cfg.state ∨ cfg.state = 4) ∧
    (cfg.tape ((n : ℤ) + 2 + (j : ℤ)) = (symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ)) ∨
     ((cfg.tape ((n : ℤ) + 2 + (j : ℤ)) = Sym.sel ∨
       cfg.tape ((n : ℤ) + 2 + (j : ℤ)) = Sym.nosel) ∧
       ((symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.alpha))
  have hQ₀ : Q (symInitialConfig input) := by
    constructor
    · left; left; rfl
    · left; rfl
  have hQfin : Q cfg₄ := by
    induction hπ₁ with
    | nil => exact hQ₀
    | cons π₀ step cfg₁ h_ind h_from h_read h_trans ih =>
        have hno101₀ : ∀ step ∈ π₀, step.result.nextState ≠ 101 :=
          fun step h => hno101 step (by simp [h])
        have hno4₀ : ∀ {π₀' : List SymStep} {cfg₀ : SymConfig},
            SymSteps VerifierSym.transition (symInitialConfig input) π₀' cfg₀ →
            (∃ ρ : List SymStep, π₀ = π₀' ++ ρ) → π₀'.length < π₀.length → cfg₀.state ≠ 4 := by
          intro π₀' cfg₀ h₀ hρ hlt
          rcases hρ with ⟨ρ, hρ'⟩
          refine hno4 h₀ ⟨ρ ++ [step], ?_⟩ ?_
          · -- π₁ = π₀' ++ ρ ++ [step](π₁ = π₀ ++ [step])
            rw [hρ']
            simp [List.append_assoc]
          · -- π₀'.length < π₁.length(π₁ = π₀ ++ [step])
            exact Nat.lt_trans hlt (by simp)
        rcases ih hno4₀ hno101₀ with ⟨hS₁, hcell₁⟩
        have htr : step.result ∈ VerifierSym.transition (cfg₁.state, cfg₁.tape cfg₁.headPos) := by
          simpa [h_from, h_read] using h_trans
        have hno101step : step.result.nextState ≠ 101 := hno101 step (by simp)
        rcases hS₁ with hS₁ | hS4₀
        · have hdecS : ∀ q, S q → ∀ k m r, r ∈ VerifierSym.transition (q, (k, m)) →
              r.nextState ≠ 101 → S r.nextState ∨ r.nextState = 4 := by
            intro q hq
            rcases hq with hq | hq | hq | hq | hq | hq | hq | hq | hq | hq <;> subst q <;>
              native_decide
          have hS' : S (symStepConfig cfg₁ step.result).state ∨
              (symStepConfig cfg₁ step.result).state = 4 := by
            dsimp [symStepConfig]
            exact hdecS cfg₁.state hS₁ (cfg₁.tape cfg₁.headPos).1 (cfg₁.tape cfg₁.headPos).2
              step.result htr hno101step
          by_cases hj' : cfg₁.headPos = (n : ℤ) + 2 + (j : ℤ)
          · rcases hcell₁ with horig | hselα
            · constructor
              · exact hS'
              · have hdecW : ∀ q, S q → ∀ k m r, r ∈ VerifierSym.transition (q, (k, m)) →
                  r.nextState ≠ 101 →
                  (r.writeSym = (k, m) ∨
                   (q = 2 ∧ k = SymKind.alpha ∧ m = false ∧
                     (r.writeSym = Sym.sel ∨ r.writeSym = Sym.nosel)) ∨
                   (q = 3 ∧ k = SymKind.boundary ∧ m = false ∧
                     r.writeSym = Sym.mk SymKind.boundary true)) := by
                  intro q hq
                  rcases hq with hq | hq | hq | hq | hq | hq | hq | hq | hq | hq <;> subst q <;>
                    decide
                have hwr := hdecW cfg₁.state hS₁ (cfg₁.tape cfg₁.headPos).1
                  (cfg₁.tape cfg₁.headPos).2 step.result htr hno101step
                rcases hwr with hwb | hselw | h3w
                · left
                  dsimp [symStepConfig]
                  simp [hj', hwb]
                  exact horig
                · right
                  constructor
                  · rcases hselw.2.2.2 with hsel | hnosel
                    · left
                      dsimp [symStepConfig]
                      simp [hj', hsel]
                    · right
                      dsimp [symStepConfig]
                      simp [hj', hnosel]
                  · rw [← horig, ← hj']
                    exact hselw.2.1
                · exfalso
                  have hk : ((symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ))).1 =
                      SymKind.boundary := by
                    rw [← horig, ← hj']
                    exact h3w.2.1
                  rcases hkind₃ with hα | hd0 | hd1
                  · rw [hα] at hk
                    cases hk
                  · rw [hd0] at hk
                    cases hk
                  · rw [hd1] at hk
                    cases hk
            · constructor
              · exact hS'
              · have hdec29 : ∀ q, S q → ∀ k m r, r ∈ VerifierSym.transition (q, (k, m)) →
                  r.nextState ≠ 101 → (k = SymKind.sel ∨ k = SymKind.nosel) → q = 29 := by
                  intro q hq
                  rcases hq with hq | hq | hq | hq | hq | hq | hq | hq | hq | hq <;> subst q <;>
                    native_decide
                have hreadselk : (cfg₁.tape cfg₁.headPos).1 = SymKind.sel ∨
                    (cfg₁.tape cfg₁.headPos).1 = SymKind.nosel := by
                  rw [hj']
                  rcases hselα.1 with hsel1 | hnosel1
                  · exact Or.inl (congrArg (fun s : Sym => s.1) hsel1)
                  · exact Or.inr (congrArg (fun s : Sym => s.1) hnosel1)
                have hq29 := hdec29 cfg₁.state hS₁ (cfg₁.tape cfg₁.headPos).1
                  (cfg₁.tape cfg₁.headPos).2 step.result htr hno101step hreadselk
                have hwb : step.result.writeSym = cfg₁.tape cfg₁.headPos := by
                  have hd : ∀ k m r, r ∈ VerifierSym.transition (29, (k, m)) → r.nextState ≠ 101 →
                      (k = SymKind.sel ∨ k = SymKind.nosel) → r.writeSym = (k, m) := by
                    native_decide
                  exact hd (cfg₁.tape cfg₁.headPos).1 (cfg₁.tape cfg₁.headPos).2 step.result
                    (by simpa [hq29] using htr) hno101step hreadselk
                rcases hselα.1 with hselα1 | hselα1'
                · right
                  constructor
                  · left
                    dsimp [symStepConfig]
                    simp [hj']
                    rw [hwb]
                    rw [← hj'] at hselα1
                    exact hselα1
                  · exact hselα.2
                · right
                  constructor
                  · right
                    dsimp [symStepConfig]
                    simp [hj']
                    rw [hwb]
                    rw [← hj'] at hselα1'
                    exact hselα1'
                  · exact hselα.2
          · constructor
            · exact hS'
            · rcases hcell₁ with horig | hselα
              · left
                dsimp [symStepConfig]
                rw [if_neg (by intro h; exact hj' h.symm)]
                exact horig
              · right
                constructor
                · dsimp [symStepConfig]
                  rw [if_neg (by intro h; exact hj' h.symm)]
                  exact hselα.1
                · exact hselα.2
        · exfalso
          exact hno4 h_ind ⟨[step], by simp⟩ (by simp) hS4₀
  intro hsel
  rcases hQfin with ⟨_hS, hcell⟩
  rcases hcell with horig | hselα
  · exfalso
    rcases hsel with hsel' | hnosel'
    · have hk := congrArg (fun s : Sym => s.1) (hsel' ▸ horig.symm)
      rcases hkind₃ with hα | hd0 | hd1
      · rw [hα] at hk
        cases hk
      · rw [hd0] at hk
        cases hk
      · rw [hd1] at hk
        cases hk
    · have hk := congrArg (fun s : Sym => s.1) (hnosel' ▸ horig.symm)
      rcases hkind₃ with hα | hd0 | hd1
      · rw [hα] at hk
        cases hk
      · rw [hd0] at hk
        cases hk
      · rw [hd1] at hk
        cases hk
  · exact hselα.2

lemma step26_data1_cell (input : List Sym) (n len j : ℕ) (cfg₄ cfg₁ : SymConfig) (step : SymStep)
    (hhead : cfg₁.headPos = (n : ℤ) + 2 + (j : ℤ))
    (htapep : cfg₁.tape cfg₁.headPos = cfg₄.tape cfg₁.headPos)
    (htrans : step.result ∈ VerifierSym.transition (26, cfg₁.tape cfg₁.headPos))
    (hnext29 : step.result.nextState = 29)
    (hws : cfg₄.tape ((n : ℤ) + 2 + (j : ℤ)) = Sym.sel ∨
        cfg₄.tape ((n : ℤ) + 2 + (j : ℤ)) = Sym.nosel ∨
        cfg₄.tape ((n : ℤ) + 2 + (j : ℤ)) = (symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ))) :
    ((symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ))).2 = false ∧
    ((symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.data1 := by
  have hdec : ∀ k m r, r ∈ VerifierSym.transition (26, (k, m)) → r.nextState = 29 →
      k = SymKind.data1 ∧ m = false := by
    native_decide
  have hread' := hdec (cfg₁.tape cfg₁.headPos).1 (cfg₁.tape cfg₁.headPos).2 step.result htrans hnext29
  rcases hws with hsel | hnosel | horig
  · exfalso
    rw [← hhead] at hsel
    have hk : (cfg₁.tape cfg₁.headPos).1 = SymKind.sel := by
      rw [htapep]
      exact congrArg (fun s : Sym => s.1) hsel
    rw [hread'.1] at hk
    cases hk
  · exfalso
    rw [← hhead] at hnosel
    have hk : (cfg₁.tape cfg₁.headPos).1 = SymKind.nosel := by
      rw [htapep]
      exact congrArg (fun s : Sym => s.1) hnosel
    rw [hread'.1] at hk
    cases hk
  · have hfull : (symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ)) = (SymKind.data1, false) := by
      rw [← horig, ← hhead, ← htapep]
      rcases h : cfg₁.tape cfg₁.headPos with ⟨k, m⟩
      rw [h] at hread'
      simpa using hread'
    constructor
    · exact congrArg (fun s : Sym => s.2) hfull
    · exact congrArg (fun s : Sym => s.1) hfull

/-- 27 支读(→38):读格输入值 = (data1, false),且 0 < n。 -/
lemma step27_cell (input : List Sym) (n : ℕ) (cfg₄ cfg₁ : SymConfig) (step : SymStep)
    (hhead : cfg₁.headPos = (n : ℤ))
    (htapep : cfg₁.tape cfg₁.headPos = cfg₄.tape cfg₁.headPos)
    (hlown : cfg₄.tape ((n : ℤ)) = (symInitialConfig input).tape ((n : ℤ)))
    (hb0 : ((symInitialConfig input).tape 0).1 = SymKind.boundary)
    (htrans : step.result ∈ VerifierSym.transition (27, cfg₁.tape cfg₁.headPos))
    (hnext38 : step.result.nextState = 38) :
    0 < n ∧
    ((symInitialConfig input).tape ((n : ℤ))).1 = SymKind.data1 ∧
    ((symInitialConfig input).tape ((n : ℤ))).2 = false := by
  have hdec : ∀ k m r, r ∈ VerifierSym.transition (27, (k, m)) → r.nextState = 38 →
      (k, m) = (SymKind.data1, false) := by
    native_decide
  have hread' := hdec (cfg₁.tape cfg₁.headPos).1 (cfg₁.tape cfg₁.headPos).2 step.result htrans hnext38
  have hcell : (symInitialConfig input).tape ((n : ℤ)) = (SymKind.data1, false) := by
    rw [← hlown, ← hhead, ← htapep]
    rcases h : cfg₁.tape cfg₁.headPos with ⟨k, m⟩
    rw [h] at hread'
    simpa using hread'
  have hpos : 0 < n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    rw [hn0] at hcell
    have hk : ((symInitialConfig input).tape 0).1 = SymKind.data1 := congrArg (fun s : Sym => s.1) hcell
    rw [hb0] at hk
    cases hk
  exact ⟨hpos, congrArg (fun s : Sym => s.1) hcell, congrArg (fun s : Sym => s.2) hcell⟩

/-- 38 支 data 读(→38):读格输入标记 false。 -/
lemma step38_data_cell (input : List Sym) (n j : ℕ) (cfg₄ cfg₁ : SymConfig) (step : SymStep)
    (hhead : cfg₁.headPos = 1 + (j : ℤ))
    (htapep : cfg₁.tape cfg₁.headPos = cfg₄.tape cfg₁.headPos)
    (hlowj : cfg₄.tape (1 + (j : ℤ)) = (symInitialConfig input).tape (1 + (j : ℤ)))
    (htrans : step.result ∈ VerifierSym.transition (38, cfg₁.tape cfg₁.headPos))
    (hnext38 : step.result.nextState = 38) :
    ((symInitialConfig input).tape (1 + (j : ℤ))).2 = false := by
  have hdec : ∀ k m r, r ∈ VerifierSym.transition (38, (k, m)) → r.nextState = 38 →
      m = false ∧ (k = SymKind.data0 ∨ k = SymKind.data1) := by
    native_decide
  have hread' := hdec (cfg₁.tape cfg₁.headPos).1 (cfg₁.tape cfg₁.headPos).2 step.result htrans hnext38
  rcases hcell0 : cfg₁.tape cfg₁.headPos with ⟨k, m⟩
  rw [hcell0] at hread'
  have hfull : (symInitialConfig input).tape (1 + (j : ℤ)) = (k, m) := by
    rw [← hlowj, ← hhead, ← htapep]
    exact hcell0
  rw [hfull]
  simpa using hread'.1

/-- 38 支 boundary 读(→28):读格输入 = (boundary, false)。 -/
lemma step38_boundary_cell (input : List Sym) (cfg₄ cfg₁ : SymConfig) (step : SymStep)
    (hhead : cfg₁.headPos = 0)
    (htapep : cfg₁.tape cfg₁.headPos = cfg₄.tape cfg₁.headPos)
    (hlow0 : cfg₄.tape 0 = (symInitialConfig input).tape 0)
    (htrans : step.result ∈ VerifierSym.transition (38, cfg₁.tape cfg₁.headPos))
    (hnext28 : step.result.nextState = 28) :
    ((symInitialConfig input).tape 0).2 = false := by
  have hdec : ∀ k m r, r ∈ VerifierSym.transition (38, (k, m)) → r.nextState = 28 →
      (k, m) = (SymKind.boundary, false) := by
    native_decide
  have hread' := hdec (cfg₁.tape cfg₁.headPos).1 (cfg₁.tape cfg₁.headPos).2 step.result htrans hnext28
  rcases hcell0 : cfg₁.tape cfg₁.headPos with ⟨k, m⟩
  rw [hcell0] at hread'
  have hfull : (symInitialConfig input).tape 0 = (k, m) := by
    rw [← hlow0, ← hhead, ← htapep]
    exact hcell0
  rw [hfull]
  rw [hread']

/-- 26 支 boundary 读(→27):读格输入 = (boundary, false)(#₀)。 -/
lemma step26_boundary_cell (input : List Sym) (n : ℕ) (cfg₄ cfg₁ : SymConfig) (step : SymStep)
    (hhead : cfg₁.headPos = (n : ℤ) + 1)
    (htapep : cfg₁.tape cfg₁.headPos = cfg₄.tape cfg₁.headPos)
    (hmid : cfg₄.tape ((n : ℤ) + 1) = (symInitialConfig input).tape ((n : ℤ) + 1))
    (htrans : step.result ∈ VerifierSym.transition (26, cfg₁.tape cfg₁.headPos))
    (hnext27 : step.result.nextState = 27) :
    ((symInitialConfig input).tape ((n : ℤ) + 1)).2 = false := by
  have hdec : ∀ k m r, r ∈ VerifierSym.transition (26, (k, m)) → r.nextState = 27 →
      (k, m) = (SymKind.boundary, false) := by
    native_decide
  have hread' := hdec (cfg₁.tape cfg₁.headPos).1 (cfg₁.tape cfg₁.headPos).2 step.result htrans hnext27
  rcases hcell0 : cfg₁.tape cfg₁.headPos with ⟨k, m⟩
  rw [hcell0] at hread'
  have hfull : (symInitialConfig input).tape ((n : ℤ) + 1) = (k, m) := by
    rw [← hmid, ← hhead, ← htapep]
    exact hcell0
  rw [hfull]
  rw [hread']


-- ============================================================
-- q11a-2b:fmt 行走独立引理(standalone,吸收面受控)
-- 结论 Q cfg₄:四区不变式(24 / 29∨26 / 27∨38 / 28∨4),cfg-only(无磁带字段,
-- 常数性按需导出)。归纳于 hSymf;上下文只含可前缀限制假设。
-- ============================================================
/-- 24 支读(→29):读格输入值 = (data1, false)。 -/
lemma step24_last_cell (input : List Sym) (n len j : Nat) (cfg₁ : SymConfig) (step : SymStep)
    (hhead : cfg₁.headPos = (n : Int) + 2 + (j : Int))
    (htrans : step.result ∈ VerifierSym.transition (24, cfg₁.tape cfg₁.headPos))
    (hnext : step.result.nextState ≠ 101)
    (hws : (cfg₁.tape ((n : Int) + 2 + (j : Int))).1 = SymKind.sel ∨
        (cfg₁.tape ((n : Int) + 2 + (j : Int))).1 = SymKind.nosel ∨
        cfg₁.tape ((n : Int) + 2 + (j : Int)) = (symInitialConfig input).tape ((n : Int) + 2 + (j : Int))) :
    ((symInitialConfig input).tape ((n : Int) + 2 + (j : Int))).2 = false ∧
    ((symInitialConfig input).tape ((n : Int) + 2 + (j : Int))).1 = SymKind.data1 := by
  have hdec := pre4_step_24 (cfg₁.tape cfg₁.headPos) step htrans hnext
  have hs : cfg₁.tape cfg₁.headPos = (SymKind.data1, false) := hdec.1
  rcases hws with hsel | hnosel | horig
  · exfalso
    rw [← hhead] at hsel
    have hk : (cfg₁.tape cfg₁.headPos).1 = SymKind.sel := hsel
    rw [hs] at hk
    cases hk
  · exfalso
    rw [← hhead] at hnosel
    have hk : (cfg₁.tape cfg₁.headPos).1 = SymKind.nosel := hnosel
    rw [hs] at hk
    cases hk
  · have hfull : (symInitialConfig input).tape ((n : Int) + 2 + (j : Int)) = (SymKind.data1, false) := by
      rw [hhead] at hs
      rw [← horig]
      exact hs
    exact ⟨congrArg (fun s : Sym => s.2) hfull, congrArg (fun s : Sym => s.1) hfull⟩

lemma fmt_walk_regions (input : List Sym) (n len : Nat) (cfg24 cfg4 : SymConfig)
    (πfmt : List SymStep)
    (hSymf : SymSteps VerifierSym.transition cfg24 πfmt cfg4)
    (hfm : ∀ step ∈ πfmt, step.fromState ∈ fmtStates)
    (hno101 : ∀ step ∈ πfmt, step.result.nextState ≠ 101)
    (hst24 : cfg24.state = 24)
    (hhead24 : cfg24.headPos = (n : Int) + 2 + (len : Int) - 1)
    (htap24 : cfg24.tape = cfg4.tape)
    (hmid : cfg4.tape ((n : Int) + 1) = (symInitialConfig input).tape ((n : Int) + 1))
    (hlow : ∀ j : Int, j < (n : Int) + 1 → cfg4.tape j = (symInitialConfig input).tape j)
    (hbn1 : (cfg4.tape ((n : Int) + 1)).1 = SymKind.boundary)
    (hb0 : (cfg4.tape 0).1 = SymKind.boundary)
    (hws : ∀ j : Nat, j < len →
      (cfg4.tape ((n : Int) + 2 + (j : Int))).1 = SymKind.sel ∨
      (cfg4.tape ((n : Int) + 2 + (j : Int))).1 = SymKind.nosel ∨
      cfg4.tape ((n : Int) + 2 + (j : Int)) = (symInitialConfig input).tape ((n : Int) + 2 + (j : Int)))
    (hαm : ∀ j : Nat, j < len →
      ((symInitialConfig input).tape ((n : Int) + 2 + (j : Int))).1 = SymKind.alpha →
      ((symInitialConfig input).tape ((n : Int) + 2 + (j : Int))).2 = false)
    (hbnd0in : ((symInitialConfig input).tape ((n : Int) + 1)).1 = SymKind.boundary)
    (hdata : ∀ j : Nat, j < n →
      ((symInitialConfig input).tape (1 + (j : Int))).1 = SymKind.data0 ∨
      ((symInitialConfig input).tape (1 + (j : Int))).1 = SymKind.data1)
    (hkind₃ : ∀ j : Nat, j < len →
      ((symInitialConfig input).tape ((n : Int) + 2 + (j : Int))).1 = SymKind.alpha ∨
      ((symInitialConfig input).tape ((n : Int) + 2 + (j : Int))).1 = SymKind.data0 ∨
      ((symInitialConfig input).tape ((n : Int) + 2 + (j : Int))).1 = SymKind.data1)
    (hselα : ∀ j : Nat, j < len →
      cfg4.tape ((n : Int) + 2 + (j : Int)) = Sym.sel ∨
      cfg4.tape ((n : Int) + 2 + (j : Int)) = Sym.nosel →
      ((symInitialConfig input).tape ((n : Int) + 2 + (j : Int))).1 = SymKind.alpha) :
    let tape0 : Int → Sym := (symInitialConfig input).tape
    (cfg4.state = 24 ∧ cfg4.headPos = (n : Int) + 2 + (len : Int) - 1) ∨
    ((cfg4.state = 29 ∨ cfg4.state = 26) ∧
      1 + (n : Int) ≤ cfg4.headPos ∧ cfg4.headPos ≤ (n : Int) + 2 + (len : Int) - 2 ∧
      (∀ j : Nat, j < len → cfg4.headPos < (n : Int) + 2 + (j : Int) →
        ((symInitialConfig input).tape ((n : Int) + 2 + (j : Int))).2 = false) ∧
      (∀ j : Nat, j < len → cfg4.headPos + 1 < (n : Int) + 2 + (j : Int) →
        ((symInitialConfig input).tape ((n : Int) + 2 + (j : Int))).1 = SymKind.alpha →
        0 < j → ((symInitialConfig input).tape ((n : Int) + 2 + ((j - 1 : Nat) : Int))).1 = SymKind.data1) ∧
      (cfg4.headPos < (n : Int) + 2 + (len : Int) - 1 →
        ((symInitialConfig input).tape ((n : Int) + 2 + (len : Int) - 1)).1 = SymKind.data1) ∧
      (cfg4.headPos ≤ 1 + (n : Int) →
        0 < len ∧ (cfg4.state = 26 → ((symInitialConfig input).tape ((n : Int) + 2)).1 = SymKind.alpha)) ∧
      (cfg4.state = 29 → ((symInitialConfig input).tape (cfg4.headPos + 1)).1 ≠ SymKind.alpha)) ∨
    (cfg4.state = 27 ∧ cfg4.headPos = (n : Int) ∧
      (∀ j : Nat, j < len → ((symInitialConfig input).tape ((n : Int) + 2 + (j : Int))).2 = false) ∧
      (∀ j : Nat, j < len →
        ((symInitialConfig input).tape ((n : Int) + 2 + (j : Int))).1 = SymKind.alpha →
        0 < j → ((symInitialConfig input).tape ((n : Int) + 2 + ((j - 1 : Nat) : Int))).1 = SymKind.data1) ∧
      ((symInitialConfig input).tape ((n : Int) + 2 + (len : Int) - 1)).1 = SymKind.data1 ∧
      0 < len ∧ ((symInitialConfig input).tape ((n : Int) + 2)).1 = SymKind.alpha ∧
      ((symInitialConfig input).tape ((n : Int) + 1)).2 = false) ∨
    (cfg4.state = 38 ∧
      0 ≤ cfg4.headPos ∧ cfg4.headPos ≤ (n : Int) - 1 ∧
      (∀ j : Nat, j < n → cfg4.headPos < 1 + (j : Int) →
        ((symInitialConfig input).tape (1 + (j : Int))).2 = false) ∧
      0 < n ∧ ((symInitialConfig input).tape ((n : Int))).1 = SymKind.data1 ∧
      (∀ j : Nat, j < len → ((symInitialConfig input).tape ((n : Int) + 2 + (j : Int))).2 = false) ∧
      (∀ j : Nat, j < len →
        ((symInitialConfig input).tape ((n : Int) + 2 + (j : Int))).1 = SymKind.alpha →
        0 < j → ((symInitialConfig input).tape ((n : Int) + 2 + ((j - 1 : Nat) : Int))).1 = SymKind.data1) ∧
      ((symInitialConfig input).tape ((n : Int) + 2 + (len : Int) - 1)).1 = SymKind.data1 ∧
      0 < len ∧ ((symInitialConfig input).tape ((n : Int) + 2)).1 = SymKind.alpha ∧
      ((symInitialConfig input).tape ((n : Int) + 1)).2 = false) ∨
    ((cfg4.state = 28 ∨ cfg4.state = 4) ∧
      1 ≤ cfg4.headPos ∧ cfg4.headPos ≤ 2 + (n : Int) ∧
      (∀ j : Nat, j < len → ((symInitialConfig input).tape ((n : Int) + 2 + (j : Int))).2 = false) ∧
      (∀ j : Nat, j < len →
        ((symInitialConfig input).tape ((n : Int) + 2 + (j : Int))).1 = SymKind.alpha →
        0 < j → ((symInitialConfig input).tape ((n : Int) + 2 + ((j - 1 : Nat) : Int))).1 = SymKind.data1) ∧
      ((symInitialConfig input).tape ((n : Int) + 2 + (len : Int) - 1)).1 = SymKind.data1 ∧
      (∀ j : Nat, j < n → ((symInitialConfig input).tape (1 + (j : Int))).2 = false) ∧
      ((symInitialConfig input).tape 0).2 = false ∧
      0 < n ∧ ((symInitialConfig input).tape ((n : Int))).1 = SymKind.data1 ∧
      0 < len ∧ ((symInitialConfig input).tape ((n : Int) + 2)).1 = SymKind.alpha ∧
      ((symInitialConfig input).tape ((n : Int) + 1)).2 = false) := by
  induction hSymf with
  | nil =>
      left
      exact ⟨hst24, hhead24⟩
  | cons π₀ step cfg₁ h_ind h_from h_read h_trans ih =>
      have hfm₀ : ∀ step ∈ π₀, step.fromState ∈ fmtStates :=
        fun step h => hfm step (by simp [h])
      have hno101₀ : ∀ step ∈ π₀, step.result.nextState ≠ 101 :=
        fun step h => hno101 step (by simp [h])
      have htap24₀ : cfg24.tape = cfg₁.tape :=
        (fmt_tape_unchanged cfg24 cfg₁ π₀ h_ind hfm₀ hno101₀).symm
      -- 分支端磁带 = 前缀端磁带(写回);被吸收假设在分支内已 cfg4 ↦ symStepConfig cfg₁ step.result
      have htape14 : cfg₁.tape = (symStepConfig cfg₁ step.result).tape := by
        exact Eq.trans htap24₀.symm htap24
      have hmid₀ : cfg₁.tape ((n : Int) + 1) = (symInitialConfig input).tape ((n : Int) + 1) := by
        rw [htape14]
        exact hmid
      have hlow₀ : ∀ j : Int, j < (n : Int) + 1 →
          cfg₁.tape j = (symInitialConfig input).tape j := by
        intro j hj
        rw [htape14]
        exact hlow j hj
      have hbn1₀ : (cfg₁.tape ((n : Int) + 1)).1 = SymKind.boundary := by
        rw [htape14]
        exact hbn1
      have hb0₀ : (cfg₁.tape 0).1 = SymKind.boundary := by
        rw [htape14]
        exact hb0
      have hws₀ : ∀ j : Nat, j < len →
          (cfg₁.tape ((n : Int) + 2 + (j : Int))).1 = SymKind.sel ∨
          (cfg₁.tape ((n : Int) + 2 + (j : Int))).1 = SymKind.nosel ∨
          cfg₁.tape ((n : Int) + 2 + (j : Int)) = (symInitialConfig input).tape ((n : Int) + 2 + (j : Int)) := by
        intro j hj
        rw [htape14]
        exact hws j hj
      have hselα₀ : ∀ j : Nat, j < len →
          cfg₁.tape ((n : Int) + 2 + (j : Int)) = Sym.sel ∨
          cfg₁.tape ((n : Int) + 2 + (j : Int)) = Sym.nosel →
          ((symInitialConfig input).tape ((n : Int) + 2 + (j : Int))).1 = SymKind.alpha := by
        intro j hj h
        rw [htape14] at h
        exact hselα j hj h
      -- ih 参数 = 被吸收假设(hfm hno101 htap24 hmid hlow hbn1 hws hselα)的前缀/前缀端形
      rcases (ih hfm₀ hno101₀ htap24₀ hmid₀ hlow₀ hbn1₀ hb0₀ hws₀ hselα₀) with
        hq24 | hq2926 | hq27 | hq38 | hq284
      · -- 放电体 1:24 → 29(区域 A → B,读末元素 data1)
        rcases hq24 with ⟨hst24', hheadp⟩
        have htr : step.result ∈ VerifierSym.transition (24, cfg₁.tape cfg₁.headPos) := by
          simpa [hst24', h_from, h_read] using h_trans
        have hno101step : step.result.nextState ≠ 101 := hno101 step (by simp)
        have h24 := pre4_step_24 (cfg₁.tape cfg₁.headPos) step htr hno101step
        have hs : cfg₁.tape cfg₁.headPos = (SymKind.data1, false) := h24.1
        have hres : step.result = SymTransResult.mk 29 (cfg₁.tape cfg₁.headPos) Dir.L := h24.2
        -- len = 0 排除(读 data1 vs #₀ boundary)
        have hlenpos : 0 < len := by
          by_contra hlen0
          have hlen0' : len = 0 := by omega
          subst hlen0'
          have hk : (cfg₁.tape ((n : Int) + 1)).1 = SymKind.data1 := by
            have hs' : cfg₁.tape ((n : Int) + 1) = (SymKind.data1, false) := by
              rw [show cfg₁.headPos = (n : Int) + 1 by
                rw [hheadp]
                omega] at hs
              exact hs
            exact congrArg (fun s : Sym => s.1) hs'
          rw [hbn1₀] at hk
          cases hk
        have hj_last : len - 1 < len := by omega
        have hhead_last : cfg₁.headPos = (n : Int) + 2 + ((len - 1 : Nat) : Int) := by
          rw [hheadp]
          congr 1
          omega
        have hlast := step24_last_cell input n len (len - 1) cfg₁ step hhead_last htr hno101step
          (hws₀ (len - 1) hj_last)
        have hafter_head : (symStepConfig cfg₁ step.result).headPos =
            (n : Int) + 2 + (len : Int) - 2 := by
          dsimp [symStepConfig]
          rw [hres]
          rw [hheadp]
          simp [Dir.toInt]
          omega
        right
        left
        constructor
        · left
          dsimp [symStepConfig]
          rw [hres]
        constructor
        · rw [hafter_head]
          omega
        constructor
        · rw [hafter_head]
        constructor
        · intro j hj hlt
          have hj_eq : j = len - 1 := by
            rw [hafter_head] at hlt
            omega
          subst j
          exact hlast.1
        constructor
        · intro j hj hlt hα hpos
          exfalso
          rw [hafter_head] at hlt
          omega
        constructor
        · intro hlt
          rw [show (n : Int) + 2 + (len : Int) - 1 = (n : Int) + 2 + ((len - 1 : Nat) : Int) by omega]
          exact hlast.2
        constructor
        · intro hle
          constructor
          · exact hlenpos
          · intro hst26'
            exfalso
            dsimp [symStepConfig] at hst26'
            rw [hres] at hst26'
            norm_num at hst26'
        · intro hst29 hα'
          rw [hafter_head] at hα'
          rw [show (n : Int) + 2 + (len : Int) - 2 + 1 = (n : Int) + 2 + ((len - 1 : Nat) : Int) by omega] at hα'
          rw [hlast.2] at hα'
          cases hα'
      · -- 放电体 2:区域 B(29∨26)元素区步进 + 26-boundary→27 入区域 C
        rcases hq2926 with ⟨hst, hbndl, hbndu, hmark, hstruct, hmsb, hfirstα, hnotα⟩
        have htr : step.result ∈ VerifierSym.transition (cfg₁.state, cfg₁.tape cfg₁.headPos) := by
          simpa [h_from, h_read] using h_trans
        have hno101step : step.result.nextState ≠ 101 := hno101 step (by simp)
        rcases hst with hst29 | hst26
        · -- 状态 29
          have htr29 : step.result ∈ VerifierSym.transition (29, cfg₁.tape cfg₁.headPos) := by
            simpa [hst29] using htr
          have h29 := pre4_step_29 (cfg₁.tape cfg₁.headPos) step htr29 hno101step
          have hs29 : (cfg₁.tape cfg₁.headPos).2 = false := by
            have hdec : ∀ k m r, r ∈ VerifierSym.transition (29, (k, m)) → r.nextState ≠ 101 →
                m = false := by
              native_decide
            exact hdec (cfg₁.tape cfg₁.headPos).1 (cfg₁.tape cfg₁.headPos).2 step.result htr29 hno101step
          -- head ≠ n+1(29 读 boundary 必 101)
          have hhead_ge : (n : Int) + 2 ≤ cfg₁.headPos := by
            by_contra hlt
            have heq : cfg₁.headPos = (n : Int) + 1 := by omega
            have hk : (cfg₁.tape cfg₁.headPos).1 = SymKind.boundary := by
              rw [heq]
              exact hbn1₀
            rcases h29.1 with hd0 | hd1 | hsel' | hnosel'
            · rw [hd0] at hk
              cases hk
            · rw [hd1] at hk
              cases hk
            · rw [hsel'] at hk
              cases hk
            · rw [hnosel'] at hk
              cases hk
          let j : Nat := (cfg₁.headPos - (n : Int) - 2).toNat
          have hjint : (j : Int) = cfg₁.headPos - (n : Int) - 2 := by
            dsimp [j]
            exact Int.toNat_of_nonneg (by omega : 0 ≤ cfg₁.headPos - (n : Int) - 2)
          have hjhead : cfg₁.headPos = (n : Int) + 2 + (j : Int) := by
            rw [hjint]
            omega
          have hjlen : j < len := by
            have h1 : (j : Int) ≤ (len : Int) - 2 := by
              rw [hjint]
              omega
            omega
          rcases h29.1 with hd0 | hd1 | hsel' | hnosel'
          · -- data0 读 → 29
            have hres29 : step.result = SymTransResult.mk 29 (cfg₁.tape cfg₁.headPos) Dir.L := by
              have hdec : ∀ k m r, r ∈ VerifierSym.transition (29, (k, m)) → r.nextState ≠ 101 →
                  k = SymKind.data0 → r = SymTransResult.mk 29 (k, m) Dir.L := by
                native_decide
              exact hdec (cfg₁.tape cfg₁.headPos).1 (cfg₁.tape cfg₁.headPos).2 step.result htr29
                hno101step hd0
            have hfull : (symInitialConfig input).tape cfg₁.headPos = (SymKind.data0, false) := by
              rcases hws₀ j hjlen with hsel'' | hnosel'' | horig
              · exfalso
                rw [← hjhead] at hsel''
                have hk : (cfg₁.tape cfg₁.headPos).1 = SymKind.sel := hsel''
                rw [hd0] at hk
                cases hk
              · exfalso
                rw [← hjhead] at hnosel''
                have hk : (cfg₁.tape cfg₁.headPos).1 = SymKind.nosel := hnosel''
                rw [hd0] at hk
                cases hk
              · rw [← hjhead] at horig
                exact horig.symm.trans (by
                  rw [show cfg₁.tape cfg₁.headPos = ((cfg₁.tape cfg₁.headPos).1, (cfg₁.tape cfg₁.headPos).2) from rfl]
                  rw [hd0, hs29])
            have hmarkhead : ((symInitialConfig input).tape cfg₁.headPos).2 = false :=
              congrArg (fun s : Sym => s.2) hfull
            have hdata0head : ((symInitialConfig input).tape cfg₁.headPos).1 = SymKind.data0 :=
              congrArg (fun s : Sym => s.1) hfull
            have hafter_head : (symStepConfig cfg₁ step.result).headPos = cfg₁.headPos - 1 := by
              dsimp [symStepConfig]
              rw [hres29]
              simp [Dir.toInt]
              omega
            right
            left
            constructor
            · left
              dsimp [symStepConfig]
              rw [hres29]
            constructor
            · rw [hafter_head]
              omega
            constructor
            · rw [hafter_head]
              omega
            constructor
            · intro j' hj' hlt
              rw [hafter_head] at hlt
              by_cases hjeq : j' = j
              · subst j'
                rw [hjhead.symm]
                exact hmarkhead
              · exact hmark j' hj' (by omega)
            constructor
            · intro j' hj' hlt hα' hpos
              rw [hafter_head] at hlt
              by_cases hjeq : j' = j + 1
              · subst j'
                exfalso
                have hα'' : ((symInitialConfig input).tape (cfg₁.headPos + 1)).1 = SymKind.alpha := by
                  rw [show cfg₁.headPos + 1 = (n : Int) + 2 + ((j + 1 : Nat) : Int) by omega]
                  exact hα'
                exact (hnotα hst29 hα'').elim
              · exact hstruct j' hj' (by omega) hα' hpos
            constructor
            · intro hlt
              exact hmsb (by omega)
            constructor
            · intro hle
              rw [hafter_head] at hle
              constructor
              · omega
              · intro hst26'
                exfalso
                dsimp [symStepConfig] at hst26'
                rw [hres29] at hst26'
                norm_num at hst26'
            · intro hst29' hα'
              rw [hafter_head] at hα'
              rw [show cfg₁.headPos - 1 + 1 = cfg₁.headPos by omega] at hα'
              rw [hdata0head] at hα'
              cases hα'
          · -- data1 读 → 29
            have hres29 : step.result = SymTransResult.mk 29 (cfg₁.tape cfg₁.headPos) Dir.L := by
              have hdec : ∀ k m r, r ∈ VerifierSym.transition (29, (k, m)) → r.nextState ≠ 101 →
                  k = SymKind.data1 → r = SymTransResult.mk 29 (k, m) Dir.L := by
                native_decide
              exact hdec (cfg₁.tape cfg₁.headPos).1 (cfg₁.tape cfg₁.headPos).2 step.result htr29
                hno101step hd1
            have hfull : (symInitialConfig input).tape cfg₁.headPos = (SymKind.data1, false) := by
              rcases hws₀ j hjlen with hsel'' | hnosel'' | horig
              · exfalso
                rw [← hjhead] at hsel''
                have hk : (cfg₁.tape cfg₁.headPos).1 = SymKind.sel := hsel''
                rw [hd1] at hk
                cases hk
              · exfalso
                rw [← hjhead] at hnosel''
                have hk : (cfg₁.tape cfg₁.headPos).1 = SymKind.nosel := hnosel''
                rw [hd1] at hk
                cases hk
              · rw [← hjhead] at horig
                exact horig.symm.trans (by
                  rw [show cfg₁.tape cfg₁.headPos = ((cfg₁.tape cfg₁.headPos).1, (cfg₁.tape cfg₁.headPos).2) from rfl]
                  rw [hd1, hs29])
            have hmarkhead : ((symInitialConfig input).tape cfg₁.headPos).2 = false :=
              congrArg (fun s : Sym => s.2) hfull
            have hdata1head : ((symInitialConfig input).tape cfg₁.headPos).1 = SymKind.data1 :=
              congrArg (fun s : Sym => s.1) hfull
            have hafter_head : (symStepConfig cfg₁ step.result).headPos = cfg₁.headPos - 1 := by
              dsimp [symStepConfig]
              rw [hres29]
              simp [Dir.toInt]
              omega
            right
            left
            constructor
            · left
              dsimp [symStepConfig]
              rw [hres29]
            constructor
            · rw [hafter_head]
              omega
            constructor
            · rw [hafter_head]
              omega
            constructor
            · intro j' hj' hlt
              rw [hafter_head] at hlt
              by_cases hjeq : j' = j
              · subst j'
                rw [hjhead.symm]
                exact hmarkhead
              · exact hmark j' hj' (by omega)
            constructor
            · intro j' hj' hlt hα' hpos
              rw [hafter_head] at hlt
              by_cases hjeq : j' = j + 1
              · subst j'
                rw [show (n : Int) + 2 + ((j + 1 - 1 : Nat) : Int) = cfg₁.headPos by omega]
                exact hdata1head
              · exact hstruct j' hj' (by omega) hα' hpos
            constructor
            · intro hlt
              exact hmsb (by omega)
            constructor
            · intro hle
              rw [hafter_head] at hle
              constructor
              · omega
              · intro hst26'
                exfalso
                dsimp [symStepConfig] at hst26'
                rw [hres29] at hst26'
                norm_num at hst26'
            · intro hst29' hα'
              rw [hafter_head] at hα'
              rw [show cfg₁.headPos - 1 + 1 = cfg₁.headPos by omega] at hα'
              rw [hdata1head] at hα'
              cases hα'
          · -- sel 读 → 26
            have hres26 : step.result = SymTransResult.mk 26 (cfg₁.tape cfg₁.headPos) Dir.L := by
              have hdec : ∀ k m r, r ∈ VerifierSym.transition (29, (k, m)) → r.nextState ≠ 101 →
                  k = SymKind.sel → r = SymTransResult.mk 26 (k, m) Dir.L := by
                native_decide
              exact hdec (cfg₁.tape cfg₁.headPos).1 (cfg₁.tape cfg₁.headPos).2 step.result htr29
                hno101step hsel'
            have hs_full : cfg₁.tape ((n : Int) + 2 + (j : Int)) = Sym.sel := by
              rw [← hjhead]
              rw [show cfg₁.tape cfg₁.headPos = ((cfg₁.tape cfg₁.headPos).1, (cfg₁.tape cfg₁.headPos).2) from rfl]
              rw [hsel', hs29]
              rfl
            have hαhead : ((symInitialConfig input).tape ((n : Int) + 2 + (j : Int))).1 = SymKind.alpha :=
              hselα₀ j hjlen (Or.inl hs_full)
            have hmarkheadj : ((symInitialConfig input).tape ((n : Int) + 2 + (j : Int))).2 = false :=
              hαm j hjlen hαhead
            have hafter_head : (symStepConfig cfg₁ step.result).headPos = cfg₁.headPos - 1 := by
              dsimp [symStepConfig]
              rw [hres26]
              simp [Dir.toInt]
              omega
            right
            left
            constructor
            · right
              dsimp [symStepConfig]
              rw [hres26]
            constructor
            · rw [hafter_head]
              omega
            constructor
            · rw [hafter_head]
              omega
            constructor
            · intro j' hj' hlt
              rw [hafter_head] at hlt
              by_cases hjeq : j' = j
              · subst j'
                exact hmarkheadj
              · exact hmark j' hj' (by omega)
            constructor
            · intro j' hj' hlt hα' hpos
              rw [hafter_head] at hlt
              by_cases hjeq : j' = j + 1
              · subst j'
                exfalso
                have hα'' : ((symInitialConfig input).tape (cfg₁.headPos + 1)).1 = SymKind.alpha := by
                  rw [show cfg₁.headPos + 1 = (n : Int) + 2 + ((j + 1 : Nat) : Int) by omega]
                  exact hα'
                exact (hnotα hst29 hα'').elim
              · exact hstruct j' hj' (by omega) hα' hpos
            constructor
            · intro hlt
              exact hmsb (by omega)
            constructor
            · intro hle
              rw [hafter_head] at hle
              constructor
              · omega
              · intro hst26'
                have hj0 : j = 0 := by omega
                rw [show (n : Int) + 2 + (j : Int) = (n : Int) + 2 by omega] at hαhead
                exact hαhead
            · intro hst29' hα'
              exfalso
              dsimp [symStepConfig] at hst29'
              rw [hres26] at hst29'
              norm_num at hst29'
          · -- nosel 读 → 26
            have hres26 : step.result = SymTransResult.mk 26 (cfg₁.tape cfg₁.headPos) Dir.L := by
              have hdec : ∀ k m r, r ∈ VerifierSym.transition (29, (k, m)) → r.nextState ≠ 101 →
                  k = SymKind.nosel → r = SymTransResult.mk 26 (k, m) Dir.L := by
                native_decide
              exact hdec (cfg₁.tape cfg₁.headPos).1 (cfg₁.tape cfg₁.headPos).2 step.result htr29
                hno101step hnosel'
            have hs_full : cfg₁.tape ((n : Int) + 2 + (j : Int)) = Sym.nosel := by
              rw [← hjhead]
              rw [show cfg₁.tape cfg₁.headPos = ((cfg₁.tape cfg₁.headPos).1, (cfg₁.tape cfg₁.headPos).2) from rfl]
              rw [hnosel', hs29]
              rfl
            have hαhead : ((symInitialConfig input).tape ((n : Int) + 2 + (j : Int))).1 = SymKind.alpha :=
              hselα₀ j hjlen (Or.inr hs_full)
            have hmarkheadj : ((symInitialConfig input).tape ((n : Int) + 2 + (j : Int))).2 = false :=
              hαm j hjlen hαhead
            have hafter_head : (symStepConfig cfg₁ step.result).headPos = cfg₁.headPos - 1 := by
              dsimp [symStepConfig]
              rw [hres26]
              simp [Dir.toInt]
              omega
            right
            left
            constructor
            · right
              dsimp [symStepConfig]
              rw [hres26]
            constructor
            · rw [hafter_head]
              omega
            constructor
            · rw [hafter_head]
              omega
            constructor
            · intro j' hj' hlt
              rw [hafter_head] at hlt
              by_cases hjeq : j' = j
              · subst j'
                exact hmarkheadj
              · exact hmark j' hj' (by omega)
            constructor
            · intro j' hj' hlt hα' hpos
              rw [hafter_head] at hlt
              by_cases hjeq : j' = j + 1
              · subst j'
                exfalso
                have hα'' : ((symInitialConfig input).tape (cfg₁.headPos + 1)).1 = SymKind.alpha := by
                  rw [show cfg₁.headPos + 1 = (n : Int) + 2 + ((j + 1 : Nat) : Int) by omega]
                  exact hα'
                exact (hnotα hst29 hα'').elim
              · exact hstruct j' hj' (by omega) hα' hpos
            constructor
            · intro hlt
              exact hmsb (by omega)
            constructor
            · intro hle
              rw [hafter_head] at hle
              constructor
              · omega
              · intro hst26'
                have hj0 : j = 0 := by omega
                rw [show (n : Int) + 2 + (j : Int) = (n : Int) + 2 by omega] at hαhead
                exact hαhead
            · intro hst29' hα'
              exfalso
              dsimp [symStepConfig] at hst29'
              rw [hres26] at hst29'
              norm_num at hst29'
        · -- 状态 26
          have htr26 : step.result ∈ VerifierSym.transition (26, cfg₁.tape cfg₁.headPos) := by
            simpa [hst26] using htr
          have h26 := pre4_step_26 (cfg₁.tape cfg₁.headPos) step htr26 hno101step
          have hs26 : (cfg₁.tape cfg₁.headPos).2 = false := by
            have hdec : ∀ k m r, r ∈ VerifierSym.transition (26, (k, m)) → r.nextState ≠ 101 →
                m = false := by
              native_decide
            exact hdec (cfg₁.tape cfg₁.headPos).1 (cfg₁.tape cfg₁.headPos).2 step.result htr26 hno101step
          rcases h26.1 with hd1' | hbnd26
          · -- data1 读 → 29
            have hhead_ge : (n : Int) + 2 ≤ cfg₁.headPos := by
              by_contra hlt
              have heq : cfg₁.headPos = (n : Int) + 1 := by omega
              have hk : (cfg₁.tape cfg₁.headPos).1 = SymKind.boundary := by
                rw [heq]
                exact hbn1₀
              rw [hd1'] at hk
              cases hk
            let j : Nat := (cfg₁.headPos - (n : Int) - 2).toNat
            have hjint : (j : Int) = cfg₁.headPos - (n : Int) - 2 := by
              dsimp [j]
              exact Int.toNat_of_nonneg (by omega : 0 ≤ cfg₁.headPos - (n : Int) - 2)
            have hjhead : cfg₁.headPos = (n : Int) + 2 + (j : Int) := by
              rw [hjint]
              omega
            have hjlen : j < len := by
              have h1 : (j : Int) ≤ (len : Int) - 2 := by
                rw [hjint]
                omega
              omega
            have hres29 : step.result = SymTransResult.mk 29 (cfg₁.tape cfg₁.headPos) Dir.L := by
              have hdec : ∀ k m r, r ∈ VerifierSym.transition (26, (k, m)) → r.nextState ≠ 101 →
                  k = SymKind.data1 → r = SymTransResult.mk 29 (k, m) Dir.L := by
                native_decide
              exact hdec (cfg₁.tape cfg₁.headPos).1 (cfg₁.tape cfg₁.headPos).2 step.result htr26
                hno101step hd1'
            have hfull : (symInitialConfig input).tape cfg₁.headPos = (SymKind.data1, false) := by
              rcases hws₀ j hjlen with hsel'' | hnosel'' | horig
              · exfalso
                rw [← hjhead] at hsel''
                have hk : (cfg₁.tape cfg₁.headPos).1 = SymKind.sel := hsel''
                rw [hd1'] at hk
                cases hk
              · exfalso
                rw [← hjhead] at hnosel''
                have hk : (cfg₁.tape cfg₁.headPos).1 = SymKind.nosel := hnosel''
                rw [hd1'] at hk
                cases hk
              · rw [← hjhead] at horig
                exact horig.symm.trans (by
                  rw [show cfg₁.tape cfg₁.headPos = ((cfg₁.tape cfg₁.headPos).1, (cfg₁.tape cfg₁.headPos).2) from rfl]
                  rw [hd1', hs26])
            have hmarkhead : ((symInitialConfig input).tape cfg₁.headPos).2 = false :=
              congrArg (fun s : Sym => s.2) hfull
            have hdata1head : ((symInitialConfig input).tape cfg₁.headPos).1 = SymKind.data1 :=
              congrArg (fun s : Sym => s.1) hfull
            have hafter_head : (symStepConfig cfg₁ step.result).headPos = cfg₁.headPos - 1 := by
              dsimp [symStepConfig]
              rw [hres29]
              simp [Dir.toInt]
              omega
            right
            left
            constructor
            · left
              dsimp [symStepConfig]
              rw [hres29]
            constructor
            · rw [hafter_head]
              omega
            constructor
            · rw [hafter_head]
              omega
            constructor
            · intro j' hj' hlt
              rw [hafter_head] at hlt
              by_cases hjeq : j' = j
              · subst j'
                rw [hjhead.symm]
                exact hmarkhead
              · exact hmark j' hj' (by omega)
            constructor
            · intro j' hj' hlt hα' hpos
              rw [hafter_head] at hlt
              by_cases hjeq : j' = j + 1
              · subst j'
                rw [show (n : Int) + 2 + ((j + 1 - 1 : Nat) : Int) = cfg₁.headPos by omega]
                exact hdata1head
              · exact hstruct j' hj' (by omega) hα' hpos
            constructor
            · intro hlt
              exact hmsb (by omega)
            constructor
            · intro hle
              rw [hafter_head] at hle
              constructor
              · omega
              · intro hst26'
                exfalso
                dsimp [symStepConfig] at hst26'
                rw [hres29] at hst26'
                norm_num at hst26'
            · intro hst29' hα'
              rw [hafter_head] at hα'
              rw [show cfg₁.headPos - 1 + 1 = cfg₁.headPos by omega] at hα'
              rw [hdata1head] at hα'
              cases hα'
          · -- boundary 读 → 27(入区域 C)
            have hhead_n1 : cfg₁.headPos = (n : Int) + 1 := by
              by_contra hne
              have hge : (n : Int) + 2 ≤ cfg₁.headPos := by omega
              let j : Nat := (cfg₁.headPos - (n : Int) - 2).toNat
              have hjint : (j : Int) = cfg₁.headPos - (n : Int) - 2 := by
                dsimp [j]
                exact Int.toNat_of_nonneg (by omega : 0 ≤ cfg₁.headPos - (n : Int) - 2)
              have hjhead : cfg₁.headPos = (n : Int) + 2 + (j : Int) := by
                rw [hjint]
                omega
              have hjlen : j < len := by
                have h1 : (j : Int) ≤ (len : Int) - 2 := by
                  rw [hjint]
                  omega
                omega
              rcases hws₀ j hjlen with hsel' | hnosel' | horig
              · exfalso
                rw [← hjhead] at hsel'
                have hk : (cfg₁.tape cfg₁.headPos).1 = SymKind.sel := hsel'
                rw [hbnd26] at hk
                cases hk
              · exfalso
                rw [← hjhead] at hnosel'
                have hk : (cfg₁.tape cfg₁.headPos).1 = SymKind.nosel := hnosel'
                rw [hbnd26] at hk
                cases hk
              · exfalso
                rw [← hjhead] at horig
                have hkin : ((symInitialConfig input).tape cfg₁.headPos).1 = SymKind.boundary := by
                  rw [← horig]
                  exact hbnd26
                rw [hjhead] at hkin
                rcases hkind₃ j hjlen with hα | hd0 | hd1
                · rw [hα] at hkin
                  cases hkin
                · rw [hd0] at hkin
                  cases hkin
                · rw [hd1] at hkin
                  cases hkin
            have hread_n1 : cfg₁.tape cfg₁.headPos = Sym.boundary := by
              have hdec : ∀ k m r, r ∈ VerifierSym.transition (26, (k, m)) → r.nextState ≠ 101 →
                  k = SymKind.boundary → (k, m) = Sym.boundary := by
                native_decide
              exact hdec (cfg₁.tape cfg₁.headPos).1 (cfg₁.tape cfg₁.headPos).2 step.result htr26
                hno101step hbnd26
            have hres27 : step.result = SymTransResult.mk 27 (cfg₁.tape cfg₁.headPos) Dir.L := by
              have hdec : ∀ k m r, r ∈ VerifierSym.transition (26, (k, m)) → r.nextState ≠ 101 →
                  k = SymKind.boundary → r = SymTransResult.mk 27 (k, m) Dir.L := by
                native_decide
              exact hdec (cfg₁.tape cfg₁.headPos).1 (cfg₁.tape cfg₁.headPos).2 step.result htr26
                hno101step hbnd26
            have hn1full : (symInitialConfig input).tape ((n : Int) + 1) = Sym.boundary := by
              rw [← hmid₀]
              rw [← hhead_n1]
              exact hread_n1
            have hafter_head : (symStepConfig cfg₁ step.result).headPos = (n : Int) := by
              dsimp [symStepConfig]
              rw [hres27]
              rw [hhead_n1]
              simp [Dir.toInt]
            have hfirstαfired := hfirstα (by omega)
            right
            right
            left
            constructor
            · dsimp [symStepConfig]
              rw [hres27]
            constructor
            · rw [hafter_head]
            constructor
            · intro j hj
              exact hmark j hj (by omega)
            constructor
            · intro j hj hα hpos
              by_cases hj0 : j = 0
              · subst j
                exfalso
                omega
              · exact hstruct j hj (by omega) hα hpos
            constructor
            · exact hmsb (by omega)
            constructor
            · exact hfirstαfired.1
            constructor
            · exact hfirstαfired.2 hst26
            · exact congrArg (fun s : Sym => s.2) hn1full
      · -- 放电体 3a:27 案(格 n = target 最高位,读 (data1,false) → 38 于 n−1)
        rcases hq27 with ⟨hst27, hheadn, helemM, helemS, hmsbE, hlenposC, hαfirstC, hmarkn1⟩
        have htr27 : step.result ∈ VerifierSym.transition (27, cfg₁.tape cfg₁.headPos) := by
          simpa [hst27, h_from, h_read] using h_trans
        have hno101step : step.result.nextState ≠ 101 := hno101 step (by simp)
        have h27 := pre4_step_27 (cfg₁.tape cfg₁.headPos) step htr27 hno101step
        have hs27 : cfg₁.tape cfg₁.headPos = (SymKind.data1, false) := h27.1
        have hres38 : step.result = SymTransResult.mk 38 (cfg₁.tape cfg₁.headPos) Dir.L := h27.2
        -- 输入事实:格 n = (data1, false)
        have hlow_n := hlow₀ (n : Int) (by omega : (n : Int) < (n : Int) + 1)
        have hnfull : (symInitialConfig input).tape ((n : Int)) = (SymKind.data1, false) := by
          rw [← hlow_n]
          rw [← hheadn]
          exact hs27
        have hd1n : ((symInitialConfig input).tape ((n : Int))).1 = SymKind.data1 :=
          congrArg (fun s : Sym => s.1) hnfull
        have hmn : ((symInitialConfig input).tape ((n : Int))).2 = false :=
          congrArg (fun s : Sym => s.2) hnfull
        -- 0 < n(n = 0 时 27 读格 0 = #ₗ)
        have hnpos : 0 < n := by
          by_contra hn0
          have hn0' : n = 0 := by omega
          subst hn0'
          have hk : ((symInitialConfig input).tape 0).1 = SymKind.data1 := by
            simpa using hd1n
          have hlow0 := hlow₀ 0 (by omega : (0 : Int) < (0 : Int) + 1)
          have hkb : ((symInitialConfig input).tape 0).1 = SymKind.boundary := by
            rw [← hlow0]
            exact hb0₀
          rw [hkb] at hk
          cases hk
        have hafter_head : (symStepConfig cfg₁ step.result).headPos = (n : Int) - 1 := by
          dsimp [symStepConfig]
          rw [hres38]
          rw [hheadn]
          simp [Dir.toInt]
          omega
        right
        right
        right
        left
        constructor
        · dsimp [symStepConfig]
          rw [hres38]
        constructor
        · rw [hafter_head]
          omega
        constructor
        · rw [hafter_head]
        constructor
        · intro j hj hlt
          rw [hafter_head] at hlt
          have hj_eq : j = n - 1 := by omega
          subst j
          rw [show (1 + (n - 1 : Nat) : Int) = (n : Int) by omega]
          exact hmn
        constructor
        · exact hnpos
        constructor
        · exact hd1n
        constructor
        · intro j hj
          exact helemM j hj
        constructor
        · intro j hj hα hpos
          exact helemS j hj hα hpos
        constructor
        · exact hmsbE
        constructor
        · exact hlenposC
        constructor
        · exact hαfirstC
        · exact hmarkn1
      · -- 放电体 3b:38 案(data 读 → 38 左移;boundary 读(格 0)→ 28 右转入区域 D)
        rcases hq38 with ⟨hst38, hheadlo, hheadhi, hmarkT, hnposC, hd1n, helemM, helemS,
          hmsbE, hlenposC, hαfirstC, hmarkn1⟩
        have htr38 : step.result ∈ VerifierSym.transition (38, cfg₁.tape cfg₁.headPos) := by
          simpa [hst38, h_from, h_read] using h_trans
        have hno101step : step.result.nextState ≠ 101 := hno101 step (by simp)
        have h38 := pre4_step_38 (cfg₁.tape cfg₁.headPos) step htr38 hno101step
        have hs38 : (cfg₁.tape cfg₁.headPos).2 = false := by
          have hdec : ∀ k m r, r ∈ VerifierSym.transition (38, (k, m)) → r.nextState ≠ 101 →
              m = false := by
            native_decide
          exact hdec (cfg₁.tape cfg₁.headPos).1 (cfg₁.tape cfg₁.headPos).2 step.result htr38
            hno101step
        rcases h38.1 with hd0 | hd1 | hb38
        · -- data0 读 → 38
          have hheadge1 : 1 ≤ cfg₁.headPos := by
            by_contra hlt
            have heq : cfg₁.headPos = 0 := by omega
            have hk : (cfg₁.tape cfg₁.headPos).1 = SymKind.boundary := by
              rw [heq]
              exact hb0₀
            rw [hd0] at hk
            cases hk
          have hres38s : step.result = SymTransResult.mk 38 (cfg₁.tape cfg₁.headPos) Dir.L := by
            have hdec : ∀ k m r, r ∈ VerifierSym.transition (38, (k, m)) → r.nextState ≠ 101 →
                k = SymKind.data0 → r = SymTransResult.mk 38 (k, m) Dir.L := by
              native_decide
            exact hdec (cfg₁.tape cfg₁.headPos).1 (cfg₁.tape cfg₁.headPos).2 step.result htr38
              hno101step hd0
          have hlowh := hlow₀ cfg₁.headPos (by omega : cfg₁.headPos < (n : Int) + 1)
          have hfull : (symInitialConfig input).tape cfg₁.headPos = (SymKind.data0, false) := by
            rw [← hlowh]
            rw [show cfg₁.tape cfg₁.headPos = ((cfg₁.tape cfg₁.headPos).1, (cfg₁.tape cfg₁.headPos).2) from rfl]
            rw [hd0, hs38]
          have hmarkhead : ((symInitialConfig input).tape cfg₁.headPos).2 = false :=
            congrArg (fun s : Sym => s.2) hfull
          have hafter_head : (symStepConfig cfg₁ step.result).headPos = cfg₁.headPos - 1 := by
            dsimp [symStepConfig]
            rw [hres38s]
            simp [Dir.toInt]
            omega
          right
          right
          right
          left
          constructor
          · dsimp [symStepConfig]
            rw [hres38s]
          constructor
          · rw [hafter_head]
            omega
          constructor
          · rw [hafter_head]
            omega
          constructor
          · intro j hj hlt
            rw [hafter_head] at hlt
            by_cases hjeq : (j : Int) = cfg₁.headPos - 1
            · rw [show 1 + (j : Int) = cfg₁.headPos by omega]
              exact hmarkhead
            · exact hmarkT j hj (by omega)
          constructor
          · exact hnposC
          constructor
          · exact hd1n
          constructor
          · intro j hj
            exact helemM j hj
          constructor
          · intro j hj hα hpos
            exact helemS j hj hα hpos
          constructor
          · exact hmsbE
          constructor
          · exact hlenposC
          constructor
          · exact hαfirstC
          · exact hmarkn1
        · -- data1 读 → 38
          have hheadge1 : 1 ≤ cfg₁.headPos := by
            by_contra hlt
            have heq : cfg₁.headPos = 0 := by omega
            have hk : (cfg₁.tape cfg₁.headPos).1 = SymKind.boundary := by
              rw [heq]
              exact hb0₀
            rw [hd1] at hk
            cases hk
          have hres38s : step.result = SymTransResult.mk 38 (cfg₁.tape cfg₁.headPos) Dir.L := by
            have hdec : ∀ k m r, r ∈ VerifierSym.transition (38, (k, m)) → r.nextState ≠ 101 →
                k = SymKind.data1 → r = SymTransResult.mk 38 (k, m) Dir.L := by
              native_decide
            exact hdec (cfg₁.tape cfg₁.headPos).1 (cfg₁.tape cfg₁.headPos).2 step.result htr38
              hno101step hd1
          have hlowh := hlow₀ cfg₁.headPos (by omega : cfg₁.headPos < (n : Int) + 1)
          have hfull : (symInitialConfig input).tape cfg₁.headPos = (SymKind.data1, false) := by
            rw [← hlowh]
            rw [show cfg₁.tape cfg₁.headPos = ((cfg₁.tape cfg₁.headPos).1, (cfg₁.tape cfg₁.headPos).2) from rfl]
            rw [hd1, hs38]
          have hmarkhead : ((symInitialConfig input).tape cfg₁.headPos).2 = false :=
            congrArg (fun s : Sym => s.2) hfull
          have hafter_head : (symStepConfig cfg₁ step.result).headPos = cfg₁.headPos - 1 := by
            dsimp [symStepConfig]
            rw [hres38s]
            simp [Dir.toInt]
            omega
          right
          right
          right
          left
          constructor
          · dsimp [symStepConfig]
            rw [hres38s]
          constructor
          · rw [hafter_head]
            omega
          constructor
          · rw [hafter_head]
            omega
          constructor
          · intro j hj hlt
            rw [hafter_head] at hlt
            by_cases hjeq : (j : Int) = cfg₁.headPos - 1
            · rw [show 1 + (j : Int) = cfg₁.headPos by omega]
              exact hmarkhead
            · exact hmarkT j hj (by omega)
          constructor
          · exact hnposC
          constructor
          · exact hd1n
          constructor
          · intro j hj
            exact helemM j hj
          constructor
          · intro j hj hα hpos
            exact helemS j hj hα hpos
          constructor
          · exact hmsbE
          constructor
          · exact hlenposC
          constructor
          · exact hαfirstC
          · exact hmarkn1
        · -- boundary 读(格 0)→ 28 右转(区域 D)
          have hhead0 : cfg₁.headPos = 0 := by
            by_contra hne
            have hge1 : 1 ≤ cfg₁.headPos := by omega
            let j : Nat := (cfg₁.headPos - 1).toNat
            have hjint : (j : Int) = cfg₁.headPos - 1 := by
              dsimp [j]
              exact Int.toNat_of_nonneg (by omega : 0 ≤ cfg₁.headPos - 1)
            have hjlt : j < n := by
              have h1 : (j : Int) ≤ (n : Int) - 2 := by
                rw [hjint]
                omega
              omega
            have hlj := hlow₀ cfg₁.headPos (by omega : cfg₁.headPos < (n : Int) + 1)
            have hkin : ((symInitialConfig input).tape cfg₁.headPos).1 = SymKind.boundary := by
              rw [← hlj]
              exact hb38
            have hdj := hdata j hjlt
            rw [show 1 + (j : Int) = cfg₁.headPos by rw [hjint]; omega] at hdj
            rcases hdj with hd0 | hd1
            · rw [hd0] at hkin
              cases hkin
            · rw [hd1] at hkin
              cases hkin
          have hres28 : step.result = SymTransResult.mk 28 (cfg₁.tape cfg₁.headPos) Dir.R := by
            have hdec : ∀ k m r, r ∈ VerifierSym.transition (38, (k, m)) → r.nextState ≠ 101 →
                k = SymKind.boundary → r = SymTransResult.mk 28 (k, m) Dir.R := by
              native_decide
            exact hdec (cfg₁.tape cfg₁.headPos).1 (cfg₁.tape cfg₁.headPos).2 step.result htr38
              hno101step hb38
          have hlow0 := hlow₀ 0 (by omega)
          have h0full : (symInitialConfig input).tape 0 = Sym.boundary := by
            rw [← hlow0]
            rw [← hhead0]
            rw [show cfg₁.tape cfg₁.headPos = ((cfg₁.tape cfg₁.headPos).1, (cfg₁.tape cfg₁.headPos).2) from rfl]
            rw [hb38, hs38]
            rfl
          have hafter_head : (symStepConfig cfg₁ step.result).headPos = 1 := by
            dsimp [symStepConfig]
            rw [hres28]
            rw [hhead0]
            simp [Dir.toInt]
          right
          right
          right
          right
          constructor
          · left
            dsimp [symStepConfig]
            rw [hres28]
          constructor
          · rw [hafter_head]
          constructor
          · rw [hafter_head]
            omega
          constructor
          · intro j hj
            exact helemM j hj
          constructor
          · intro j hj hα hpos
            exact helemS j hj hα hpos
          constructor
          · exact hmsbE
          constructor
          · intro j hj
            exact hmarkT j hj (by omega)
          constructor
          · exact congrArg (fun s : Sym => s.2) h0full
          constructor
          · exact hnposC
          constructor
          · exact hd1n
          constructor
          · exact hlenposC
          constructor
          · exact hαfirstC
          · exact hmarkn1
      · -- 放电体 4:区域 D(28 右扫 data→28、boundary(#₀)→4;4 态不能有后继步)
        rcases hq284 with ⟨hstD, hheadlo, hheadhi, helemM, helemS, hmsbE, hmarkT, h0m,
          hnposC, hd1n, hlenposC, hαfirstC, hmarkn1⟩
        rcases hstD with hst28 | hst4
        · -- 28 态
          have htr28 : step.result ∈ VerifierSym.transition (28, cfg₁.tape cfg₁.headPos) := by
            simpa [hst28, h_from, h_read] using h_trans
          have hno101step : step.result.nextState ≠ 101 := hno101 step (by simp)
          have h28 := pre4_step_28 (cfg₁.tape cfg₁.headPos) step htr28 hno101step
          rcases h28.1 with hd0 | hd1 | hb28
          · -- data0 读 → 28 R(head ≤ n:#₀ 在 n+1 不能读 data)
            have hheadle : cfg₁.headPos ≤ (n : Int) := by
              by_contra hgt
              have hge : (n : Int) + 1 ≤ cfg₁.headPos := by omega
              by_cases heq : cfg₁.headPos = (n : Int) + 1
              · have hb : (cfg₁.tape ((n : Int) + 1)).1 = SymKind.boundary := by
                  rw [hmid₀]
                  exact hbnd0in
                have hk : (cfg₁.tape cfg₁.headPos).1 = SymKind.boundary := by
                  rw [heq]
                  exact hb
                rw [hd0] at hk
                cases hk
              · have heq2 : cfg₁.headPos = (n : Int) + 2 := by omega
                exfalso
                rw [heq2] at hd0
                rcases hws₀ 0 hlenposC with hsel | hnosel | horig
                · rw [show (n : Int) + 2 + ((0 : Nat) : Int) = (n : Int) + 2 by omega] at hsel
                  rw [hsel] at hd0
                  cases hd0
                · rw [show (n : Int) + 2 + ((0 : Nat) : Int) = (n : Int) + 2 by omega] at hnosel
                  rw [hnosel] at hd0
                  cases hd0
                · rw [show (n : Int) + 2 + ((0 : Nat) : Int) = (n : Int) + 2 by omega] at horig
                  rw [horig] at hd0
                  have hk : ((symInitialConfig input).tape ((n : Int) + 2)).1 = SymKind.alpha := hαfirstC
                  rw [hd0] at hk
                  cases hk
            have hres28s : step.result = SymTransResult.mk 28 (cfg₁.tape cfg₁.headPos) Dir.R := by
              have hdec : ∀ k m r, r ∈ VerifierSym.transition (28, (k, m)) → r.nextState ≠ 101 →
                  k = SymKind.data0 → r = SymTransResult.mk 28 (k, m) Dir.R := by
                native_decide
              exact hdec (cfg₁.tape cfg₁.headPos).1 (cfg₁.tape cfg₁.headPos).2 step.result htr28
                hno101step hd0
            have hafter_head : (symStepConfig cfg₁ step.result).headPos = cfg₁.headPos + 1 := by
              dsimp [symStepConfig]
              rw [hres28s]
              simp [Dir.toInt]
            right
            right
            right
            right
            constructor
            · left
              dsimp [symStepConfig]
              rw [hres28s]
            constructor
            · rw [hafter_head]
              omega
            constructor
            · rw [hafter_head]
              omega
            constructor
            · intro j hj
              exact helemM j hj
            constructor
            · intro j hj hα hpos
              exact helemS j hj hα hpos
            constructor
            · exact hmsbE
            constructor
            · intro j hj
              exact hmarkT j hj
            constructor
            · exact h0m
            constructor
            · exact hnposC
            constructor
            · exact hd1n
            constructor
            · exact hlenposC
            constructor
            · exact hαfirstC
            · exact hmarkn1
          · -- data1 读 → 28 R
            have hheadle : cfg₁.headPos ≤ (n : Int) := by
              by_contra hgt
              have hge : (n : Int) + 1 ≤ cfg₁.headPos := by omega
              by_cases heq : cfg₁.headPos = (n : Int) + 1
              · have hb : (cfg₁.tape ((n : Int) + 1)).1 = SymKind.boundary := by
                  rw [hmid₀]
                  exact hbnd0in
                have hk : (cfg₁.tape cfg₁.headPos).1 = SymKind.boundary := by
                  rw [heq]
                  exact hb
                rw [hd1] at hk
                cases hk
              · have heq2 : cfg₁.headPos = (n : Int) + 2 := by omega
                exfalso
                rw [heq2] at hd1
                rcases hws₀ 0 hlenposC with hsel | hnosel | horig
                · rw [show (n : Int) + 2 + ((0 : Nat) : Int) = (n : Int) + 2 by omega] at hsel
                  rw [hsel] at hd1
                  cases hd1
                · rw [show (n : Int) + 2 + ((0 : Nat) : Int) = (n : Int) + 2 by omega] at hnosel
                  rw [hnosel] at hd1
                  cases hd1
                · rw [show (n : Int) + 2 + ((0 : Nat) : Int) = (n : Int) + 2 by omega] at horig
                  rw [horig] at hd1
                  have hk : ((symInitialConfig input).tape ((n : Int) + 2)).1 = SymKind.alpha := hαfirstC
                  rw [hd1] at hk
                  cases hk
            have hres28s : step.result = SymTransResult.mk 28 (cfg₁.tape cfg₁.headPos) Dir.R := by
              have hdec : ∀ k m r, r ∈ VerifierSym.transition (28, (k, m)) → r.nextState ≠ 101 →
                  k = SymKind.data1 → r = SymTransResult.mk 28 (k, m) Dir.R := by
                native_decide
              exact hdec (cfg₁.tape cfg₁.headPos).1 (cfg₁.tape cfg₁.headPos).2 step.result htr28
                hno101step hd1
            have hafter_head : (symStepConfig cfg₁ step.result).headPos = cfg₁.headPos + 1 := by
              dsimp [symStepConfig]
              rw [hres28s]
              simp [Dir.toInt]
            right
            right
            right
            right
            constructor
            · left
              dsimp [symStepConfig]
              rw [hres28s]
            constructor
            · rw [hafter_head]
              omega
            constructor
            · rw [hafter_head]
              omega
            constructor
            · intro j hj
              exact helemM j hj
            constructor
            · intro j hj hα hpos
              exact helemS j hj hα hpos
            constructor
            · exact hmsbE
            constructor
            · intro j hj
              exact hmarkT j hj
            constructor
            · exact h0m
            constructor
            · exact hnposC
            constructor
            · exact hd1n
            constructor
            · exact hlenposC
            constructor
            · exact hαfirstC
            · exact hmarkn1
          · -- boundary 读(#₀ 于 n+1)→ 4 R
            have hheadn1 : cfg₁.headPos = (n : Int) + 1 := by
              by_contra hne
              by_cases hle : cfg₁.headPos ≤ (n : Int)
              · have hge1 : 1 ≤ cfg₁.headPos := hheadlo
                let j : Nat := (cfg₁.headPos - 1).toNat
                have hjint : (j : Int) = cfg₁.headPos - 1 := by
                  dsimp [j]
                  exact Int.toNat_of_nonneg (by omega : 0 ≤ cfg₁.headPos - 1)
                have hjlt : j < n := by
                  have h1 : (j : Int) ≤ (n : Int) - 1 := by
                    rw [hjint]
                    omega
                  omega
                have hlj := hlow₀ cfg₁.headPos (by omega : cfg₁.headPos < (n : Int) + 1)
                have hkin : ((symInitialConfig input).tape cfg₁.headPos).1 = SymKind.boundary := by
                  rw [← hlj]
                  exact hb28
                have hdj := hdata j hjlt
                rw [show 1 + (j : Int) = cfg₁.headPos by rw [hjint]; omega] at hdj
                rcases hdj with hd0 | hd1
                · rw [hd0] at hkin
                  cases hkin
                · rw [hd1] at hkin
                  cases hkin
              · have heq2 : cfg₁.headPos = (n : Int) + 2 := by omega
                exfalso
                rw [heq2] at hb28
                rcases hws₀ 0 hlenposC with hsel | hnosel | horig
                · rw [show (n : Int) + 2 + ((0 : Nat) : Int) = (n : Int) + 2 by omega] at hsel
                  rw [hsel] at hb28
                  cases hb28
                · rw [show (n : Int) + 2 + ((0 : Nat) : Int) = (n : Int) + 2 by omega] at hnosel
                  rw [hnosel] at hb28
                  cases hb28
                · rw [show (n : Int) + 2 + ((0 : Nat) : Int) = (n : Int) + 2 by omega] at horig
                  rw [horig] at hb28
                  have hk : ((symInitialConfig input).tape ((n : Int) + 2)).1 = SymKind.alpha := hαfirstC
                  rw [hb28] at hk
                  cases hk
            have hres4 : step.result = SymTransResult.mk 4 (cfg₁.tape cfg₁.headPos) Dir.R := by
              have hdec : ∀ k m r, r ∈ VerifierSym.transition (28, (k, m)) → r.nextState ≠ 101 →
                  k = SymKind.boundary → r = SymTransResult.mk 4 (k, m) Dir.R := by
                native_decide
              exact hdec (cfg₁.tape cfg₁.headPos).1 (cfg₁.tape cfg₁.headPos).2 step.result htr28
                hno101step hb28
            have hafter_head : (symStepConfig cfg₁ step.result).headPos = (n : Int) + 2 := by
              dsimp [symStepConfig]
              rw [hres4]
              rw [hheadn1]
              simp [Dir.toInt]
              omega
            right
            right
            right
            right
            constructor
            · right
              dsimp [symStepConfig]
              rw [hres4]
            constructor
            · rw [hafter_head]
              omega
            constructor
            · rw [hafter_head]
              omega
            constructor
            · intro j hj
              exact helemM j hj
            constructor
            · intro j hj hα hpos
              exact helemS j hj hα hpos
            constructor
            · exact hmsbE
            constructor
            · intro j hj
              exact hmarkT j hj
            constructor
            · exact h0m
            constructor
            · exact hnposC
            constructor
            · exact hd1n
            constructor
            · exact hlenposC
            constructor
            · exact hαfirstC
            · exact hmarkn1
        · -- 4 态(行走终点;4 的后继步违 hfm)
          exfalso
          have hfmstep : step.fromState ∈ fmtStates := hfm step (by simp)
          rw [h_from] at hfmstep
          rw [hst4] at hfmstep
          norm_num [fmtStates] at hfmstep


theorem format_check_precise (input : List Sym) (π₁ : List SymStep) (cfg₄ : SymConfig)
    (hπ₁ : SymSteps VerifierSym.transition (symInitialConfig input) π₁ cfg₄)
    (hno4 : ∀ {π₀ : List SymStep} {cfg₀ : SymConfig},
      SymSteps VerifierSym.transition (symInitialConfig input) π₀ cfg₀ →
      (∃ ρ, π₁ = π₀ ++ ρ) → π₀.length < π₁.length → cfg₀.state ≠ 4)
    (hno101 : ∀ step ∈ π₁, step.result.nextState ≠ 101)
    (hs4 : cfg₄.state = 4) :
    ∃ n len : ℕ,
      (∀ j : ℕ, j < n → ((symInitialConfig input).tape (1 + (j : ℤ))).2 = false) ∧
      (∀ j : ℕ, j < len → ((symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ))).2 = false) ∧
      ((symInitialConfig input).tape 0).2 = false ∧
      ((symInitialConfig input).tape ((n : ℤ) + 1)).2 = false ∧
      ((symInitialConfig input).tape ((n : ℤ) + 2 + (len : ℤ))).2 = false ∧
      0 < n ∧
      ((symInitialConfig input).tape ((n : ℤ))).1 = SymKind.data1 ∧
      0 < len ∧
      ((symInitialConfig input).tape ((n : ℤ) + 2)).1 = SymKind.alpha ∧
      (∀ j : ℕ, j < len → ((symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.alpha →
        0 < j → ((symInitialConfig input).tape ((n : ℤ) + 2 + ((j - 1 : ℕ) : ℤ))).1 = SymKind.data1) ∧
      ((symInitialConfig input).tape ((n : ℤ) + 2 + ((len - 1 : ℕ) : ℤ))).1 = SymKind.data1 ∧
      (∀ j : ℕ, j < n → ((symInitialConfig input).tape (1 + (j : ℤ))).1 = SymKind.data0 ∨
        ((symInitialConfig input).tape (1 + (j : ℤ))).1 = SymKind.data1) ∧
      (∀ j : ℕ, j < len → ((symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.alpha ∨
        ((symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.data0 ∨
        ((symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.data1) ∧
      ((symInitialConfig input).tape 0).1 = SymKind.boundary ∧
      ((symInitialConfig input).tape ((n : ℤ) + 1)).1 = SymKind.boundary ∧
      ((symInitialConfig input).tape ((n : ℤ) + 2 + (len : ℤ))).1 = SymKind.boundary := by
  let tape₀ : ℤ → Sym := (symInitialConfig input).tape
  rcases branch_phase_inv_general input π₁ cfg₄ hπ₁ hno4 hno101 hs4 with
    ⟨n, len, hhead, hb0, hlow, hdata, hbnd, hmido, hbnd0, hbnd1, hws, hkind₀, hkind₃, hαm, hhigh, hmark⟩
  rcases pi1_fmt_split input π₁ cfg₄ hπ₁ hno4 hno101 hs4 with
    ⟨π₀₂, πfmt, step₂₃, step₃₂₄, cfg₂, cfg₃, hπeq, hSym, hst2, hexp, hf23, hn23, hr23, ht23,
      hbr, hcfg₃, hf324, hn324, hr324, ht324, hSymf, hfm⟩
  rcases hexp with ⟨n₁, i, hhead₂, hbnd₁, helems₂, hd₂⟩
  -- 校准:n₁ = n
  have hn₁n : n₁ = n := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h₁ | h₂
    · have hd := hdata n₁ h₁
      rcases hd with hd0 | hd1
      · rw [hd0] at hbnd₁
        cases hbnd₁
      · rw [hd1] at hbnd₁
        cases hbnd₁
    · have hd := hd₂ n h₂
      rcases hd with hd0 | hd1
      · rw [show ((symInitialConfig input).tape (1 + (n : ℤ))).1 = SymKind.boundary from
          by simpa [add_comm] using hbnd0] at hd0
        cases hd0
      · rw [show ((symInitialConfig input).tape (1 + (n : ℤ))).1 = SymKind.boundary from
          by simpa [add_comm] using hbnd0] at hd1
        cases hd1
  subst n₁
  -- 校准:i = len
  have hilen : i = len := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h₁ | h₂
    · have hk := hkind₃ i h₁
      have hb23 : ((symInitialConfig input).tape ((n : ℤ) + 2 + (i : ℤ))).1 = SymKind.boundary := by
        have hread := (pre4_step_2_to_3 cfg₂ n i step₂₃ ht23 hn23).1
        rw [hhead₂] at hread
        rw [hhead₂] at hbr
        rw [hbr] at hread
        simpa [add_comm, add_left_comm, add_assoc] using hread
      rcases hk with hα | hd0 | hd1
      · rw [hb23] at hα
        cases hα
      · rw [hb23] at hd0
        cases hd0
      · rw [hb23] at hd1
        cases hd1
    · have he := helems₂ len h₂
      have hb : ((symInitialConfig input).tape (2 + (n : ℤ) + (len : ℤ))).1 = SymKind.boundary :=
        by simpa [add_comm, add_left_comm, add_assoc] using hbnd1
      rcases he with hα | hd0 | hd1
      · rw [hb] at hα
        cases hα
      · rw [hb] at hd0
        cases hd0
      · rw [hb] at hd1
        cases hd1
  subst i
  -- 基配置头:cfg₂₄.headPos = (n:ℤ)+2+(len:ℤ)-1
  let cfg₂₄ : SymConfig := symStepConfig cfg₃ step₃₂₄.result
  have hhead₂₄ : cfg₂₄.headPos = (n : ℤ) + 2 + (len : ℤ) - 1 := by
    dsimp [cfg₂₄]
    have hh := (pre4_step_3_to_24 cfg₃ n len step₃₂₄ ht324 hn324).2.2
    rw [hh]
    have hhead₃' : cfg₃.headPos = (n : ℤ) + 2 + (len : ℤ) := by
      rw [hcfg₃]
      dsimp [symStepConfig]
      rw [hhead₂]
      have hmv : step₂₃.result.moveDir = Dir.S := by
        have hdec : ∀ k m r, r ∈ VerifierSym.transition (2, (k, m)) → r.nextState = 3 →
            r.moveDir = Dir.S := by
          native_decide
        exact hdec _ _ _ ht23 hn23
      rw [hmv]
      simp [Dir.toInt]
      omega
    rw [hhead₃']
  -- #₁ 标记位(3→24 读 = (boundary,false))
  have hb1m : (tape₀ ((n : ℤ) + 2 + (len : ℤ))).2 = false := by
    have hread3 : cfg₃.tape cfg₃.headPos = Sym.boundary :=
      (pre4_step_3_to_24 cfg₃ n len step₃₂₄ ht324 hn324).1
    have hbrg : cfg₃.tape (2 + (n : ℤ) + (len : ℤ)) = tape₀ ((n : ℤ) + 2 + (len : ℤ)) := by
      have hw := (pre4_step_2_to_3 cfg₂ n len step₂₃ ht23 hn23).2
      rw [← hcfg₃] at hw
      rw [hw]
      dsimp [SymConfig.mk]
      have hb := hbr
      rw [hhead₂] at hb
      rw [hb]
      congr 1
      omega
    have hhead₃ : cfg₃.headPos = 2 + (n : ℤ) + (len : ℤ) := by
      rw [hcfg₃]
      dsimp [symStepConfig]
      have hmm : step₂₃.result.moveDir = Dir.S := by
        have hdec : ∀ k m r, r ∈ VerifierSym.transition (2, (k, m)) → r.nextState = 3 →
            r.moveDir = Dir.S := by
          native_decide
        exact hdec _ _ _ ht23 hn23
      rw [hmm]
      simp [Dir.toInt]
      simpa using hhead₂
    rw [hhead₃] at hread3
    rw [hbrg] at hread3
    exact congrArg (fun s : Sym => s.2) hread3
  -- 磁带不变性(基)
  have hno101f : ∀ step ∈ πfmt, step.result.nextState ≠ 101 :=
    fun step h => hno101 step (by
      rw [hπeq]
      simp only [List.mem_append]
      right
      exact h)
  have htapeInv₀ : cfg₂₄.tape = cfg₄.tape := by
    dsimp [cfg₂₄]
    exact (fmt_tape_unchanged (symStepConfig cfg₃ step₃₂₄.result) cfg₄ πfmt hSymf hfm hno101f).symm
  -- 调用独立行走引理(cfg-only 不变式;与 cfg₄ 索引无关,避免归纳泛化吸收)
  have hselα : ∀ j : Nat, j < len →
      cfg₄.tape ((n : ℤ) + 2 + (j : ℤ)) = Sym.sel ∨
      cfg₄.tape ((n : ℤ) + 2 + (j : ℤ)) = Sym.nosel →
      ((symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.alpha := by
    intro j hj hsel
    exact elem_cell_sel_implies_input_alpha input π₁ cfg₄ hπ₁ hno4 hno101 n len j hj
      (hkind₃ j hj) hsel
  have hQ4 := fmt_walk_regions input n len cfg₂₄ cfg₄ πfmt hSymf hfm hno101f
    (by
      dsimp [cfg₂₄, symStepConfig]
      exact hn324)
    hhead₂₄ htapeInv₀ hmido
    hlow hbnd hb0 hws hαm hbnd0 hdata hkind₃ hselα
  -- cfg₄.state = 4:Q 只落在区域 D(28∨4)
  rcases hQ4 with hQA | hQB | hQC27 | hQC38 | hQD
  · exfalso
    rcases hQA with ⟨hstA, hheadA⟩
    rw [hstA] at hs4
    norm_num at hs4
  · exfalso
    rcases hQB with ⟨hstB, _⟩
    rcases hstB with hst29 | hst26
    · rw [hst29] at hs4
      norm_num at hs4
    · rw [hst26] at hs4
      norm_num at hs4
  · exfalso
    rcases hQC27 with ⟨hst27, _⟩
    rw [hst27] at hs4
    norm_num at hs4
  · exfalso
    rcases hQC38 with ⟨hst38, _⟩
    rw [hst38] at hs4
    norm_num at hs4
  · rcases hQD with ⟨hstD4, hheadlo4, hheadhi4, hmark4, hstruct4, hmsb4, htgt4, h04m,
      hn4pos, hd14n, hlen4pos, hα4first, h14m⟩
    -- 区域 D 事实 → 定理结论(msb 格形态 ↑(len-1) 对齐 ↑len-1)
    have hb0kind : ((symInitialConfig input).tape 0).1 = SymKind.boundary := by
      rw [hlow 0 (by omega)] at hb0
      exact hb0
    have hbnkind : ((symInitialConfig input).tape ((n : ℤ) + 1)).1 = SymKind.boundary := hbnd0
    have hb2kind : ((symInitialConfig input).tape ((n : ℤ) + 2 + (len : ℤ))).1 = SymKind.boundary := hbnd1
    refine ⟨n, len, htgt4, hmark4, h04m, h14m, hb1m, hn4pos, hd14n, hlen4pos, hα4first,
      hstruct4, ?_, hdata, hkind₃, hb0kind, hbnkind, hb2kind⟩
    rw [show (n : ℤ) + 2 + ((len - 1 : ℕ) : ℤ) = (n : ℤ) + 2 + (len : ℤ) - 1 by omega]
    exact hmsb4

-- ============================================================================
-- q11a-3:解析层(往返引理,纯 list)——见 _Q11a3Probe 移植
-- ============================================================================
-- q11a-3 解析层(纯 list,core-only):往返引理开发探针
-- ============================================================================

abbrev isDataSym (s : Sym) : Prop := s.1 = SymKind.data0 ∨ s.1 = SymKind.data1

@[simp] lemma isDataSym_data0 : isDataSym Sym.data0 := by decide
@[simp] lemma isDataSym_data1 : isDataSym Sym.data1 := by decide
@[simp] lemma isDataSym_alpha : ¬ isDataSym Sym.alpha := by decide
@[simp] lemma isDataSym_boundary : ¬ isDataSym Sym.boundary := by decide

/-- data 运行收集:返回 (最大 data 前缀, 余段)。 -/
def collectDataRun : List Sym → List Sym × List Sym
  | [] => ([], [])
  | s :: rest =>
      if h : isDataSym s then
        let (r, t) := collectDataRun rest
        (s :: r, t)
      else ([], s :: rest)

/-- 一步展开:data 头的收集。 -/
lemma collectDataRun_cons_data (s : Sym) (rest : List Sym) (hd : isDataSym s) :
    collectDataRun (s :: rest) = (s :: (collectDataRun rest).1, (collectDataRun rest).2) := by
  have hdef : collectDataRun (s :: rest) =
      (if h : isDataSym s then let (r, t) := collectDataRun rest; (s :: r, t) else ([], s :: rest)) := by
    rfl
  rw [hdef]
  simp [hd]

/-- 一步展开:非 data 头的收集。 -/
lemma collectDataRun_cons_nondata (s : Sym) (rest : List Sym) (hnd : ¬ isDataSym s) :
    collectDataRun (s :: rest) = ([], s :: rest) := by
  have hdef : collectDataRun (s :: rest) =
      (if h : isDataSym s then let (r, t) := collectDataRun rest; (s :: r, t) else ([], s :: rest)) := by
    rfl
  rw [hdef]
  simp [hnd]

/-- collectDataRun 规范:l = r ++ t ∧ r 全 data ∧ t 空或头非 data。 -/
lemma collectDataRun_spec (l : List Sym) :
    l = (collectDataRun l).1 ++ (collectDataRun l).2 ∧
    (∀ s ∈ (collectDataRun l).1, isDataSym s) ∧
    ((collectDataRun l).2 = [] ∨ (∃ u ts, (collectDataRun l).2 = u :: ts ∧ ¬ isDataSym u)) := by
  induction l with
  | nil => simp [collectDataRun]
  | cons s rest ih =>
      by_cases hd : isDataSym s
      · rw [collectDataRun_cons_data s rest hd]
        rcases ih with ⟨h1, h2, h3⟩
        constructor
        · change s :: rest = s :: ((collectDataRun rest).1 ++ (collectDataRun rest).2)
          rw [← h1]
        constructor
        · intro u hu
          rw [List.mem_cons] at hu
          rcases hu with rfl | hu'
          · exact hd
          · exact h2 u hu'
        · exact h3
      · rw [collectDataRun_cons_nondata s rest hd]
        constructor
        · rfl
        constructor
        · intro u hu
          simp at hu
        · right
          refine ⟨s, rest, rfl, hd⟩

/-- 若 l = r ++ t、r 全 data、t 空或头非 data,则 collectDataRun l = (r, t)(分解唯一)。 -/
lemma collectDataRun_eq {l r t : List Sym} (h1 : l = r ++ t)
    (h2 : ∀ s ∈ r, isDataSym s) (h3 : t = [] ∨ (∃ u ts, t = u :: ts ∧ ¬ isDataSym u)) :
    collectDataRun l = (r, t) := by
  induction r generalizing l with
  | nil =>
      subst l
      cases h3 with
      | inl ht => rw [ht]; rfl
      | inr ht =>
          rcases ht with ⟨u, ts, htu, hu⟩
          simpa [htu, collectDataRun_cons_nondata u ts hu]
  | cons s r' ih =>
      rw [h1]
      have hs : isDataSym s := h2 s (by simp)
      have h2' : ∀ s ∈ r', isDataSym s := fun u hu => h2 u (by simp [hu])
      have hih := ih rfl h2'
      have hs' : isDataSym s := hs
      simpa [collectDataRun, hs, hih]

/-- data 前缀 ++ (空或 α 头)的收集 = (前缀, 后缀)。 -/
lemma collectDataRun_append_of_data {a b : List Sym}
    (ha : ∀ s ∈ a, isDataSym s)
    (hb : b = [] ∨ (∃ t ts, b = t :: ts ∧ ¬ isDataSym t)) :
    collectDataRun (a ++ b) = (a, b) := by
  exact collectDataRun_eq rfl ha hb

/-- encodeBitsSymNative 的成员全是 data0/data1。 -/
lemma mem_encodeBitsSymNative_data (n : ℕ) {s : Sym} (hs : s ∈ encodeBitsSymNative n) :
    s = Sym.data0 ∨ s = Sym.data1 := by
  unfold encodeBitsSymNative at hs
  rcases List.mem_map.mp hs with ⟨d, hd, rfl⟩
  have hdlt : d < 2 := Nat.digits_lt_base (by decide : 1 < 2) hd
  by_cases h0 : d = 0
  · left; simp [h0]
  · right
    have h1 : d = 1 := by omega
    subst h1
    simp

/-- encodeElementsSym 非空时以 α 开头。 -/
lemma encodeElementsSym_head_alpha (v : ℕ) (rest : List ℕ) :
    encodeElementsSym (v :: rest) = Sym.alpha :: (encodeBitsSymNative v ++ encodeElementsSym rest) := by
  cases rest with
  | nil => simp [encodeElementsSym]
  | cons w ws => rfl

/-- encodeElementsSym 的尾段:空或 α 头。 -/
lemma encodeElementsSym_alpha_or_nil (rest : List ℕ) :
    encodeElementsSym rest = [] ∨
      ∃ v rest', rest = v :: rest' ∧ encodeElementsSym rest = Sym.alpha :: (encodeBitsSymNative v ++ encodeElementsSym rest') := by
  cases rest with
  | nil => left; rfl
  | cons v rest' => right; exact ⟨v, rest', rfl, encodeElementsSym_head_alpha v rest'⟩

-- ============================================================================
-- 往返 2:encodeBitsSym ∘ decodeBitsSym = id(data 串,空或末 data1)
-- ============================================================================

lemma encodeBitsSym_decode_eq_self {l : List Sym}
    (hd : ∀ s ∈ l, s = Sym.data0 ∨ s = Sym.data1)
    (hl : l = [] ∨ (∃ t s, l = t ++ [s] ∧ s.1 = SymKind.data1)) :
    encodeBitsSym (decodeBitsSym l) = l := by
  unfold decodeBitsSym
  unfold encodeBitsSym
  have hdsmap : (l.map bitVal).map (fun d => if d = 0 then Sym.data0 else Sym.data1) = l := by
    rw [List.map_map]
    apply map_eq_self_of_forall
    intro s hs
    rcases hd s hs with hs0 | hs1
    · rw [hs0]
      simp [bitVal]
    · rw [hs1]
      simp [bitVal]
  have hdo : Nat.digits 2 (Nat.ofDigits 2 (l.map bitVal)) = l.map bitVal := by
    apply Nat.digits_ofDigits
    · norm_num
    · intro d hd'
      rcases List.mem_map.mp hd' with ⟨s, hs, rfl⟩
      rcases hd s hs with hs0 | hs1
      · rw [hs0]; norm_num
      · rw [hs1]; norm_num
    · intro hne
      have hlne : l ≠ [] := by
        intro hl'
        apply hne
        rw [hl']
        rfl
      cases hl with
      | inl hl' => exact (hlne hl').elim
      | inr hlast =>
          rcases hlast with ⟨t, s, hls, hs1⟩
          have hmem : s ∈ l := by
            rw [hls]
            simp
          rcases hd s hmem with hs0 | hs1'
          · exfalso
            rw [hs0] at hs1
            simp at hs1
          · simp [hls, hs1', List.getLast_append_singleton]
  rw [hdo]
  exact hdsmap

-- ============================================================================
-- 元素区解析:α 起段 + decodeBitsSym
-- ============================================================================

/-- 元素区解析:每段 `α ++ data 位串`,段值 = decodeBitsSym。 -/
def parseElementsSym : List Sym → List ℕ
  | [] => []
  | s :: rest =>
      if s.1 = SymKind.alpha then
        decodeBitsSym (collectDataRun rest).1 :: parseElementsSym (collectDataRun rest).2
      else parseElementsSym rest
termination_by l => l.length
decreasing_by
  · -- α 分支:(cdr rest).2 是 rest 的后缀
    have hsp := collectDataRun_spec rest
    have hlen : rest.length = (collectDataRun rest).1.length + (collectDataRun rest).2.length := by
      have hl := congrArg List.length hsp.1
      rw [List.length_append] at hl
      exact hl
    have hle : (collectDataRun rest).2.length ≤ rest.length := by
      rw [hlen]
      omega
    simp_wf
    omega
  · simp_wf

/-- parse ∘ encodeElementsSym = id。 -/
lemma parseElementsSym_encodeElementsSym (elems : List ℕ) :
    parseElementsSym (encodeElementsSym elems) = elems := by
  induction elems with
  | nil => simp [encodeElementsSym, parseElementsSym]
  | cons v rest ih =>
      rw [encodeElementsSym_head_alpha]
      have ha : ∀ s ∈ encodeBitsSymNative v, isDataSym s := by
        intro s hs
        rcases mem_encodeBitsSymNative_data v hs with h0 | h1
        · simp [h0, isDataSym]
        · simp [h1, isDataSym]
      have hb : encodeElementsSym rest = [] ∨
          (∃ t ts, encodeElementsSym rest = t :: ts ∧ ¬ isDataSym t) := by
        rcases encodeElementsSym_alpha_or_nil rest with h | ⟨v', rest', hre, henc⟩
        · left; exact h
        · right
          refine ⟨Sym.alpha, encodeBitsSymNative v' ++ encodeElementsSym rest', ?_, ?_⟩
          · rw [henc]
          · simp [isDataSym]
      have hcdr := collectDataRun_append_of_data (a := encodeBitsSymNative v)
        (b := encodeElementsSym rest) ha hb
      -- 目标:parse (α :: (bits v ++ enc rest)) = v :: rest
      have hpar : parseElementsSym (Sym.alpha :: (encodeBitsSymNative v ++ encodeElementsSym rest)) =
          decodeBitsSym (collectDataRun (encodeBitsSymNative v ++ encodeElementsSym rest)).1 ::
            parseElementsSym (collectDataRun (encodeBitsSymNative v ++ encodeElementsSym rest)).2 := by
        simp [parseElementsSym, Sym.alpha]
      rw [hpar, hcdr]
      have hd : decodeBitsSym (encodeBitsSymNative v) = v := by
        simpa [encodeBitsSymNative, encodeBitsSym] using (decodeBitsSym_encodeBitsSym v)
      rw [hd, ih]

-- q11a-3b:decode 正性 + WellFormedElems + encode∘parse = id
-- ============================================================================

/-- ofDigits 2 正性:位串含 1 则值 > 0。 -/
lemma ofDigits_two_pos_of_mem_one (ds : List ℕ) (h : 1 ∈ ds) :
    0 < Nat.ofDigits 2 ds := by
  induction ds with
  | nil => simp at h
  | cons d rest ih =>
      simp at h
      rcases h with hd | hrest
      · rw [← hd]
        simp [Nat.ofDigits]
      · have hrest' : 0 < Nat.ofDigits 2 rest := ih hrest
        have h2 : 0 < 2 * Nat.ofDigits 2 rest := Nat.mul_pos (by decide) hrest'
        simp [Nat.ofDigits]
        omega

/-- decodeBitsSym 正性:含 data1 的串解码 > 0。 -/
lemma decodeBitsSym_pos_of_data1 {l : List Sym} (h : Sym.data1 ∈ l) :
    0 < decodeBitsSym l := by
  unfold decodeBitsSym
  have h1 : 1 ∈ l.map bitVal := by
    exact List.mem_map.mpr ⟨Sym.data1, h, by simp [bitVal]⟩
  exact ofDigits_two_pos_of_mem_one (l.map bitVal) h1

lemma sym_eq_alpha_of_kind_of_mark {s : Sym} (hk : s.1 = SymKind.alpha) (hm : s.2 = false) :
    s = Sym.alpha := by
  rcases s with ⟨k, m⟩
  simp at hk hm
  rw [hk, hm]
  rfl

lemma sym_eq_data0_of_kind_of_mark {s : Sym} (hk : s.1 = SymKind.data0) (hm : s.2 = false) :
    s = Sym.data0 := by
  rcases s with ⟨k, m⟩
  simp at hk hm
  rw [hk, hm]
  rfl

lemma sym_eq_boundary_of_kind_of_mark {s : Sym} (hk : s.1 = SymKind.boundary) (hm : s.2 = false) :
    s = Sym.boundary := by
  rcases s with ⟨k, m⟩
  simp at hk hm
  rw [hk, hm]
  rfl

lemma sym_eq_data1_of_kind_of_mark {s : Sym} (hk : s.1 = SymKind.data1) (hm : s.2 = false) :
    s = Sym.data1 := by
  rcases s with ⟨k, m⟩
  simp at hk hm
  rw [hk, hm]
  rfl

/-- 元素区结构良好(递归):每段 α ++ data 位串,位串空或末 data1。 -/
inductive WellFormedElems : List Sym → Prop
  | nil : WellFormedElems []
  | cons (s : Sym) (rest r t : List Sym) :
      s = Sym.alpha →
      collectDataRun rest = (r, t) →
      (∀ u ∈ r, u = Sym.data0 ∨ u = Sym.data1) →
      (r = [] ∨ ∃ r' u, r = r' ++ [u] ∧ u.1 = SymKind.data1) →
      WellFormedElems t →
      WellFormedElems (s :: rest)



lemma encodeElementsSym_parse_of_wellformed {es : List Sym} (hw : WellFormedElems es) :
    encodeElementsSym (parseElementsSym es) = es := by
  induction hw with
  | nil => simp [encodeElementsSym, parseElementsSym]
  | cons s rest r t hα hcdr hr hrend hwt ih =>
      -- es = s :: rest
      have hspec := collectDataRun_spec rest
      rw [hcdr] at hspec
      rcases hspec with ⟨hrest, hrestdata, htail⟩
      have hparse : parseElementsSym (s :: rest) =
          decodeBitsSym (collectDataRun rest).1 :: parseElementsSym (collectDataRun rest).2 := by
        rw [hα]
        simp [parseElementsSym, Sym.alpha]
      rw [hparse]
      simp [hcdr]
      -- 目标:encode (decode r :: parse t) = s :: rest
      rw [encodeElementsSym_head_alpha]
      -- 目标:α :: (bits (decode r) ++ encode (parse t)) = s :: rest
      have hbits : encodeBitsSymNative (decodeBitsSym r) = r := by
        apply encodeBitsSym_decode_eq_self
        · intro u hu
          exact hr u hu
        · rcases hrend with h0 | ⟨r', u, hru, hu1⟩
          · left; rw [h0]
          · right
            refine ⟨r', u, hru, hu1⟩
      have htail' : encodeElementsSym (parseElementsSym t) = t := ih
      rw [hbits, htail']
      -- 目标:α :: (r ++ t) = s :: rest
      rw [hα]
      -- 目标:α :: (r ++ t) = α :: rest
      congr 1
      -- 目标:r ++ t = rest
      exact hrest.symm


/-- list 等式下的 getElem 转换。 -/
lemma getElem_congr {α : Type} {l l' : List α} {i : ℕ} (h : l = l')
    (hi : i < l.length) (hi' : i < l'.length) :
    l[i]'(hi) = l'[i]'(hi') := by
  subst l'
  rfl

/-- getElem 的界无关性。 -/
lemma getElem_irrel {α : Type} {l : List α} {i : ℕ} (h h' : i < l.length) :
    l[i]'(h) = l[i]'(h') := by
  rw [Subsingleton.elim h h']

/-- take 1 l = [l[0]]。 -/
lemma take_one_eq_singleton {α : Type} (l : List α) (hpos : 0 < l.length) :
    l.take 1 = [l[0]'(hpos)] := by
  apply List.ext_getElem
  · have hmin : min 1 l.length = 1 := by
      omega
    rw [List.length_take, hmin]
    rfl
  · intro i h1 h2
    have hi0 : i = 0 := by
      have hmin : min 1 l.length = 1 := by
        omega
      have : (l.take 1).length = 1 := by
        rw [List.length_take, hmin]
      rw [this] at h1
      omega
    subst i
    simpa using (List.getElem_take (xs := l) (j := 1) (i := 0) (h := h1))


/-- list 等式下的 getLast 一致。 -/
lemma getLast_congr {α : Type} {l l' : List α} (h : l = l')
    (hl : l ≠ []) (hl' : l' ≠ []) :
    l.getLast hl = l'.getLast hl' := by
  subst l'
  rfl

/-- getLast 的界无关性。 -/
lemma getLast_irrel {α : Type} {l : List α} (h h' : l ≠ []) :
    l.getLast h = l.getLast h' := by
  rw [Subsingleton.elim h h']

/-- getLast (s :: xs) = getLast xs(xs 非空)。 -/
lemma getLast_cons {α : Type} {x : α} {xs : List α} (h : xs ≠ []) :
    (x :: xs).getLast (by intro h0; exact h (by simpa using h0)) = xs.getLast h := by
  cases xs with
  | nil => simp at h
  | cons y ys => rfl

/-- length = 0 → list = []。 -/
lemma length_eq_zero_of_eq_zero {α : Type} {l : List α} (h : l.length = 0) : l = [] := by
  cases l with
  | nil => rfl
  | cons x xs => simp at h

/-- 索引相等 → getElem 相等(界显式)。 -/
lemma getElem_of_index_eq {α : Type} {l : List α} {i j : ℕ} (hij : i = j)
    (hi : i < l.length) (hj : j < l.length) :
    l[i]'(hi) = l[j]'(hj) := by
  subst j
  rfl

/-- a ++ t 的末元素 = t 的末元素(t 非空)。 -/
lemma getLast_append_of_ne_nil {α : Type} {a t : List α} (ht : t ≠ []) :
    (a ++ t).getLast (by
      intro h
      apply ht
      have hlen : (a ++ t).length = 0 := congrArg List.length h
      have htlen : t.length = 0 := by
        rw [List.length_append] at hlen
        omega
      cases t with
      | nil => rfl
      | cons y ys => simp at htlen) = t.getLast ht := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
      have hxs : xs ++ t ≠ [] := by
        intro h0
        apply ht
        have hlen : (xs ++ t).length = 0 := congrArg List.length h0
        have htlen : t.length = 0 := by
          rw [List.length_append] at hlen
          omega
        cases t with
        | nil => rfl
        | cons y ys => simp at htlen
      have h1 : (x :: (xs ++ t)).getLast (by intro h0; exact hxs (by simpa using h0)) =
          (xs ++ t).getLast hxs := by
        exact getLast_cons (x := x) (xs := xs ++ t) hxs
      calc
        (x :: (xs ++ t)).getLast (by intro h0; exact hxs (by simpa using h0))
            = (xs ++ t).getLast hxs := h1
        _ = t.getLast ht := ih

/-- (r ++ t) 中偏移 r.length 的索引 = t 的索引 j。 -/
lemma getElem_append_shift {α : Type} (r t : List α) (j : ℕ) (hj : j < t.length) :
    (r ++ t)[r.length + j]'(by
      simp [List.length_append]
      omega) = t[j]'(hj) := by
  have h1 : r.length + j < (r ++ t).length := by
    simp [List.length_append]
    omega
  have h2 : (r.length + j) - r.length < t.length := by
    have : (r.length + j) - r.length = j := Nat.add_sub_cancel_left r.length j
    rw [this]
    exact hj
  have h : (r ++ t)[r.length + j]'(h1) = t[(r.length + j) - r.length]'(h2) := by
    exact @List.getElem_append_right α r t (r.length + j)
      (by omega : r.length ≤ r.length + j)
      (by exact h1)
  simpa [Nat.add_sub_cancel_left] using h

/-- r 非空:(s :: (r ++ t))[r.length] = r 的末元素。 -/
lemma getElem_cons_append_last {α : Type} (s : α) (r t : List α) (hr : r ≠ []) :
    (s :: (r ++ t))[r.length]'(by
      simp [List.length_append]) = r.getLast hr := by
  have hlast : r.getLast hr = r[r.length - 1]'(by
      cases r with
      | nil => simp at hr
      | cons x xs => simp) := List.getLast_eq_getElem hr
  have hpos : 0 < r.length := by
    cases r with
    | nil => simp at hr
    | cons x xs => simp
  have hgt : (s :: (r ++ t))[r.length]'(by
      simp [List.length_append]) = (r ++ t)[r.length - 1]'(by
      simp [List.length_append]
      omega) := by
    have hcs := List.getElem_cons_succ s (r ++ t) (r.length - 1) (by
      simp [List.length_append]
      omega)
    simpa [show (r.length - 1) + 1 = r.length by omega] using hcs
  have hgt2 : (r ++ t)[r.length - 1]'(by
      simp [List.length_append]
      omega) = r[r.length - 1]'(by omega) := by
    exact @List.getElem_append_left α (r.length - 1) r t
      (by omega : r.length - 1 < r.length)
      (by simp [List.length_append]
          omega : r.length - 1 < (r ++ t).length)
  rw [hgt, hgt2]
  rw [← hlast]

/-- (s :: (r ++ t))[1 + r.length + j] = t[j]。 -/
lemma getElem_cons_append_shift {α : Type} (s : α) (r t : List α) (j : ℕ) (hj : j < t.length) :
    (s :: (r ++ t))[1 + r.length + j]'(by
      simp [List.length_append]
      omega) = t[j]'(hj) := by
  have hgt : (s :: (r ++ t))[1 + r.length + j]'(by
      simp [List.length_append]
      omega) = (r ++ t)[r.length + j]'(by
      simp [List.length_append]
      omega) := by
    have hcs := List.getElem_cons_succ s (r ++ t) (r.length + j) (by
      simp [List.length_append]
      omega)
    simpa [show (r.length + j) + 1 = 1 + r.length + j by omega] using hcs
  rw [hgt]
  exact getElem_append_shift r t j hj

/-- es = s :: rest(rest = r ++ t)的 α-左邻逐点事实在 t 段上的平移。 -/
lemma struct_tail {s : Sym} {rest r t : List Sym} (hrt : rest = r ++ t)
    (hstruct : ∀ j : ℕ, (hj : j < (s :: rest).length) →
      ((s :: rest)[j]'(hj)).1 = SymKind.alpha →
      0 < j → ((s :: rest)[j - 1]'(by omega)).1 = SymKind.data1) :
    ∀ j' : ℕ, (hj' : j' < t.length) → (t[j']'(hj')).1 = SymKind.alpha →
      0 < j' → (t[j' - 1]'(by omega)).1 = SymKind.data1 := by
  have hstruct' : ∀ j : ℕ, (hj : j < (s :: (r ++ t)).length) →
      ((s :: (r ++ t))[j]'(hj)).1 = SymKind.alpha →
      0 < j → ((s :: (r ++ t))[j - 1]'(by omega)).1 = SymKind.data1 := by
    intro j hj hαj hposj
    have hj' : j < (s :: rest).length := by
      rw [hrt]
      exact hj
    have hαrest : ((s :: rest)[j]'(hj')).1 = SymKind.alpha := by
      have hc := getElem_congr (l := s :: (r ++ t)) (l' := s :: rest) (i := j)
        (by rw [hrt]) hj hj'
      rw [← hc]
      exact hαj
    have hres := hstruct j hj' hαrest hposj
    have hlt : j - 1 < j := Nat.sub_lt (by omega : 0 < j) (by decide)
    have hc2 := getElem_congr (l := s :: (r ++ t)) (l' := s :: rest) (i := j - 1)
      (by rw [hrt]) (by omega) (by omega)
    rw [hc2]
    exact hres
  intro j' hj' hα' hpos'
  have hj1 : 1 + r.length + j' < (s :: (r ++ t)).length := by
    have hlen : (s :: (r ++ t)).length = 1 + r.length + t.length := by
      simp [List.length_append]
      omega
    rw [hlen]
    omega
  have hg := getElem_cons_append_shift s r t j' hj'
  have hαes : ((s :: (r ++ t))[1 + r.length + j']'(hj1)).1 = SymKind.alpha := by
    rw [hg]
    exact hα'
  have hstr := hstruct' (1 + r.length + j') hj1 hαes (by omega)
  have hleft : t[j' - 1]'(by omega) = (s :: (r ++ t))[1 + r.length + (j' - 1)]'(by
      simp [List.length_append]
      omega) := by
    have hj'1 : j' - 1 < t.length := by omega
    exact (getElem_cons_append_shift s r t (j' - 1) hj'1).symm
  calc
    (t[j' - 1]'(by omega)).1 = ((s :: (r ++ t))[1 + r.length + (j' - 1)]'(by
        simp [List.length_append]
        omega)).1 := by
      exact congrArg (fun x : Sym => x.1) hleft
    _ = SymKind.data1 := by
      have hidx : 1 + r.length + (j' - 1) = (1 + r.length + j') - 1 := by omega
      have hgb := getElem_of_index_eq (l := s :: (r ++ t))
        (i := 1 + r.length + (j' - 1)) (j := (1 + r.length + j') - 1) hidx
        (by simp [List.length_append]
            omega)
        (by simp [List.length_append]
            omega)
      rw [hgb]
      exact hstr
/-- 切片 getElem:((l.drop a).take b)[j] = l[a + j](界参数化)。 -/
lemma getElem_drop_take {α : Type} (l : List α) (a b j : ℕ) (hj : j < b)
    (hb : a + j < l.length) (hbt : j < ((l.drop a).take b).length) :
    ((l.drop a).take b)[j]'(hbt) = l[a + j]'(hb) := by
  have hb2 : j < (l.drop a).length := by
    simp [List.length_drop]
    exact @Nat.lt_sub_of_add_lt j a l.length (by omega)
  have h1 : ((l.drop a).take b)[j]'(hbt) = (l.drop a)[j]'(hb2) := by
    exact List.getElem_take (xs := l.drop a) (j := b) (i := j) (h := hbt)
  rw [h1]
  exact List.getElem_drop (xs := l) (i := a) (j := j) (h := hb2)

lemma length_drop_take {α : Type} (l : List α) (a b : ℕ) :
    ((l.drop a).take b).length = min b (l.length - a) := by
  simp [List.length_take, List.length_drop]

/-- 格式事实 → 结构良好(强归纳)。 -/
lemma WellFormedElems_of (es : List Sym)
    (hfirst : es = [] ∨ (∃ s rest, es = s :: rest ∧ s = Sym.alpha))
    (hdata : ∀ s ∈ es, s = Sym.data0 ∨ s = Sym.data1 ∨ s = Sym.alpha)
    (hstruct : ∀ j : ℕ, (hj : j < es.length) → (es[j]'(hj)).1 = SymKind.alpha →
      0 < j → (es[j - 1]'(by omega)).1 = SymKind.data1)
    (hlast : es = [] ∨ ∃ es' u, es = es' ++ [u] ∧ u.1 = SymKind.data1) :
    WellFormedElems es := by
  have hmain : ∀ (n : ℕ), ∀ (es : List Sym), es.length = n →
      (es = [] ∨ (∃ s rest, es = s :: rest ∧ s = Sym.alpha)) →
      (∀ s ∈ es, s = Sym.data0 ∨ s = Sym.data1 ∨ s = Sym.alpha) →
      (∀ j : ℕ, (hj : j < es.length) → (es[j]'(hj)).1 = SymKind.alpha →
        0 < j → (es[j - 1]'(by omega)).1 = SymKind.data1) →
      (es = [] ∨ ∃ es' u, es = es' ++ [u] ∧ u.1 = SymKind.data1) →
      WellFormedElems es := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro es hlen hfirst hdata hstruct hlast
        cases es with
        | nil =>
            exact WellFormedElems.nil
        | cons s rest =>
            rcases hfirst with h0 | ⟨s', rest', heq, hα'⟩
            · simp at h0
            · injection heq with hseq hresteq
              have hs_alpha : s = Sym.alpha := by
                rw [← hseq] at hα'
                exact hα'
              subst s'
              subst rest'
              have hspec := collectDataRun_spec rest
              let r : List Sym := (collectDataRun rest).1
              let t : List Sym := (collectDataRun rest).2
              have hrt : rest = r ++ t := by
                dsimp [r, t]
                exact hspec.1
              refine WellFormedElems.cons s rest r t hs_alpha ?_ ?_ ?_ ?_
              · rfl
              · intro u hu
                have hu_data : isDataSym u := hspec.2.1 u (by simpa [r, t] using hu)
                have hu_rest : u ∈ rest := by
                  rw [hrt]
                  exact List.mem_append_left t (by simpa [r, t] using hu)
                have hu_es : u ∈ s :: rest := List.mem_cons_of_mem s hu_rest
                rcases hdata u hu_es with hd0 | hd1 | hαu
                · exact Or.inl hd0
                · exact Or.inr hd1
                · exfalso
                  rw [hαu] at hu_data
                  simp [isDataSym] at hu_data
              · by_cases hr0 : r = []
                · left; exact hr0
                · right
                  -- 目标:∃ r' u0, r = r' ++ [u0] ∧ u0.1 = data1
                  rcases hspec.2.2 with ht0 | ⟨u0, ts, hteq, hu0nd⟩
                  · -- t = []:r = rest;es 末 data1(hlast)
                    have ht0' : t = [] := by simpa [t] using ht0
                    have hrest_r : rest = r := by
                      rw [hrt, ht0']
                      simp
                    -- r = rest;rest 非空(hr0)
                    rcases hlast with hle | ⟨es', u, hesu, hu1⟩
                    · simp at hle
                    · -- es = s::rest(数据上 = s::r);es = es'++[u]
                      -- 比较两分解:若 es' = []:es = [u] → rest = [] → 矛盾;否则 es' = x::es'' → rest = es''++[u]
                      cases es' with
                      | nil =>
                          exfalso
                          apply hr0
                          have htail_eq : rest = [] := by
                            have he2 : s :: rest = [u] := by simpa using hesu
                            simpa using congrArg List.tail he2
                          rw [← hrest_r]
                          exact htail_eq
                      | cons x es'' =>
                          have he2 : s :: rest = x :: (es'' ++ [u]) := by
                            simpa using hesu
                          have htail_eq : rest = es'' ++ [u] := by
                            simpa using congrArg List.tail he2
                          refine ⟨es'', u, ?_, ?_⟩
                          · -- r = es'' ++ [u]
                            rw [← hrest_r]
                            exact htail_eq
                          · exact hu1
                  · -- t 非空:t = u0::ts;u0 非 data → hdata → u0 = α;r 末 = u0 左邻
                    have ht0' : t = u0 :: ts := by simpa [t] using hteq
                    have htpos : 0 < t.length := by
                      rw [ht0']
                      simp
                    -- u0 ∈ es → hdata → u0 = α
                    have hu0_rest : u0 ∈ rest := by
                      rw [hrt]
                      apply List.mem_append_right
                      rw [ht0']
                      simp
                    have hu0_es : u0 ∈ s :: rest := List.mem_cons_of_mem s hu0_rest
                    rcases hdata u0 hu0_es with hd0 | hd1 | hαu0
                    · exfalso; exact hu0nd (by simp [hd0, isDataSym])
                    · exfalso; exact hu0nd (by simp [hd1, isDataSym])
                    · -- u0 = α:r 末 = u0(es 位置 1+r.length)的左邻(hstruct)
                      have hlen2 : (s :: (r ++ t)).length = 1 + r.length + t.length := by
                        simp [List.length_append]
                        omega
                      have hlen2r : (s :: rest).length = 1 + r.length + t.length := by
                        rw [hrt]
                        simp [List.length_append]
                        omega
                      have bj : 1 + r.length < (s :: (r ++ t)).length := by
                        rw [hlen2]
                        omega
                      have bj0 : 1 + r.length + 0 < (s :: (r ++ t)).length := by
                        rw [hlen2]
                        omega
                      have brm : r.length < (s :: (r ++ t)).length := by
                        simp [List.length_append]
                      -- es 中 u0(t 头)处 = α:es[1+r.length] = t[0](shift + 索引归一),t[0] = u0 = α
                      have hg0 := getElem_cons_append_shift s r t 0 htpos
                      -- hg0 : (s::(r++t))[1+r.length+0]'(bA) = t[0]'(htpos)
                      have hα0 : (t[0]'(htpos)).1 = SymKind.alpha := by
                        have hg0t := getElem_congr (l := t) (l' := u0 :: ts) (i := 0)
                          ht0' htpos (by simp)
                        calc
                          (t[0]'(htpos)).1 = ((u0 :: ts)[0]'(by simp)).1 := by
                            rw [hg0t]
                          _ = u0.1 := by rfl
                          _ = SymKind.alpha := by
                            simp [hαu0, Sym.alpha]
                      -- 归一 1+r.length+0 → 1+r.length(在 s::(r++t) 上):
                      have hidx0 : 1 + r.length + 0 = 1 + r.length := by omega
                      have hgbA := getElem_of_index_eq (l := s :: (r ++ t))
                        (i := 1 + r.length + 0) (j := 1 + r.length) hidx0 bj0 bj
                      have hαu0atA : ((s :: (r ++ t))[1 + r.length]'(bj)).1 = SymKind.alpha := by
                        calc
                          ((s :: (r ++ t))[1 + r.length]'(bj)).1
                              = ((s :: (r ++ t))[1 + r.length + 0]'(bj0)).1 := by
                                rw [← hgbA]
                          _ = (t[0]'(htpos)).1 := by
                                rw [hg0]
                          _ = SymKind.alpha := hα0
                      -- hstruct 在 s::rest 上:先桥 α 事实到 s::rest:
                      have hlenr : (s :: rest).length = (s :: (r ++ t)).length := by
                        rw [hrt]
                      have hbj' : 1 + r.length < (s :: rest).length := by
                        rw [hlenr]
                        exact bj
                      have hαu0at : ((s :: rest)[1 + r.length]'(hbj')).1 = SymKind.alpha := by
                        have hc0 := getElem_congr (l := s :: (r ++ t)) (l' := s :: rest)
                          (i := 1 + r.length) (by rw [hrt]) bj hbj'
                        calc
                          ((s :: rest)[1 + r.length]'(hbj')).1
                              = ((s :: (r ++ t))[1 + r.length]'(bj)).1 := by
                                exact congrArg (fun x : Sym => x.1) hc0.symm
                          _ = SymKind.alpha := hαu0atA
                      -- hstruct 应用(es = s::rest):
                      have hstr := hstruct (1 + r.length) hbj' hαu0at (by omega)
                      -- hstr : ((s::rest)[(1+r.length)-1]'(界)).1 = data1——索引归一 (1+r.length)-1 = r.length:
                      have hbrm' : r.length < (s :: rest).length := by
                        rw [hlenr]
                        exact brm
                      have hidx1 : (1 + r.length) - 1 = r.length := by omega
                      have hgbB := getElem_of_index_eq (l := s :: rest)
                        (i := (1 + r.length) - 1) (j := r.length) hidx1 (by omega) hbrm'
                      have hstr' : ((s :: rest)[r.length]'(hbrm')).1 = SymKind.data1 := by
                        calc
                          ((s :: rest)[r.length]'(hbrm')).1
                              = ((s :: rest)[(1 + r.length) - 1]'(by omega)).1 := by
                                exact congrArg (fun x : Sym => x.1) hgbB.symm
                          _ = SymKind.data1 := hstr
                      -- r 末 = es[r.length](cons_append_last,桥到 s::rest):
                      have hgl := getElem_cons_append_last s r t hr0
                      -- hgl : (s::(r++t))[r.length]'(brm) = r.getLast hr0
                      have hglr : (s :: rest)[r.length]'(hbrm') = r.getLast hr0 := by
                        have hc1 := getElem_congr (l := s :: (r ++ t)) (l' := s :: rest)
                          (i := r.length) (by rw [hrt]) brm hbrm'
                        calc
                          (s :: rest)[r.length]'(hbrm') = (s :: (r ++ t))[r.length]'(brm) := by
                                exact hc1.symm
                          _ = r.getLast hr0 := hgl
                      refine ⟨r.dropLast, r.getLast hr0, ?_, ?_⟩
                      · exact (List.dropLast_append_getLast hr0).symm
                      · -- (r.getLast hr0).1 = data1:r.getLast = es[r.length](hglr.symm)+hstr'
                        calc
                          (r.getLast hr0).1 = ((s :: rest)[r.length]'(hbrm')).1 := by
                                exact congrArg (fun x : Sym => x.1) hglr.symm
                          _ = SymKind.data1 := hstr'
              · -- hwt:WellFormedElems t——递归:ih t.length … t rfl + t 的四前提
                have hlt : t.length < (s :: rest).length := by
                  have hlen_s : (s :: rest).length = 1 + rest.length := by
                    simp
                    omega
                  rw [hlen_s]
                  have hrest_len : rest.length = r.length + t.length := by
                    rw [hrt]
                    simp [List.length_append]
                  rw [hrest_len]
                  omega
                have htfirst : t = [] ∨ (∃ s0 rest0, t = s0 :: rest0 ∧ s0 = Sym.alpha) := by
                  by_cases ht0 : t = []
                  · left; exact ht0
                  · right
                    rcases hspec.2.2 with hz | ⟨u0, ts, hteq, hu0nd⟩
                    · exfalso; apply ht0; simpa [t] using hz
                    · -- u0 = t 头 ∈ es → hdata → α(排除 data 由 hu0nd)
                      have ht0' : t = u0 :: ts := by simpa [t] using hteq
                      have hu0_rest : u0 ∈ rest := by
                        rw [hrt]
                        apply List.mem_append_right
                        rw [ht0']
                        simp
                      have hu0_es : u0 ∈ s :: rest := List.mem_cons_of_mem s hu0_rest
                      rcases hdata u0 hu0_es with hd0 | hd1 | hαu0
                      · exfalso; exact hu0nd (by simp [hd0, isDataSym])
                      · exfalso; exact hu0nd (by simp [hd1, isDataSym])
                      · exact ⟨u0, ts, ht0', hαu0⟩
                have htdata : ∀ s0 ∈ t, s0 = Sym.data0 ∨ s0 = Sym.data1 ∨ s0 = Sym.alpha := by
                  intro s0 hs0
                  have hs0_rest : s0 ∈ rest := by
                    rw [hrt]
                    exact List.mem_append_right _ hs0
                  have hs0_es : s0 ∈ s :: rest := List.mem_cons_of_mem s hs0_rest
                  exact hdata s0 hs0_es
                have htstruct : ∀ j : ℕ, (hj : j < t.length) → (t[j]'(hj)).1 = SymKind.alpha →
                    0 < j → (t[j - 1]'(by omega)).1 = SymKind.data1 := by
                  exact struct_tail (s := s) (rest := rest) (r := r) (t := t) hrt hstruct
                have htlast : t = [] ∨ ∃ t' u, t = t' ++ [u] ∧ u.1 = SymKind.data1 := by
                  by_cases ht0 : t = []
                  · left; exact ht0
                  · right
                    -- t 非空:t 末 = es 末(hlast)→ data1
                    rcases hlast with hle | ⟨es', u, hesu, hu1⟩
                    · simp at hle
                    · -- es = es'++[u];es = s::(r++t) → t 末 = u
                      -- 若 es' = []:es = [u] → rest = [] → t = [] 矛盾(ht0);否则 rest = es''++[u] → r++t = es''++[u] → t 末 = u
                      cases es' with
                      | nil =>
                          exfalso
                          apply ht0
                          have he2 : s :: (r ++ t) = [u] := by simpa [hrt] using hesu
                          have htail0 : r ++ t = [] := by
                            simpa using congrArg List.tail he2
                          have hlen3 : (r ++ t).length = 0 := congrArg List.length htail0
                          rw [List.length_append] at hlen3
                          have htlen : t.length = 0 := by omega
                          exact length_eq_zero_of_eq_zero htlen
                      | cons x es'' =>
                          have he2 : s :: (r ++ t) = x :: (es'' ++ [u]) := by
                            simpa [hrt] using hesu
                          have htail_eq : r ++ t = es'' ++ [u] := by
                            simpa using congrArg List.tail he2
                          -- t 末 = u:用 getLast 两侧:t 非空——(r++t).getLast = t.getLast(getLast_append_of_ne_nil)——(es''++[u]).getLast = u
                          refine ⟨t.dropLast, t.getLast ht0, ?_, ?_⟩
                          · exact (List.dropLast_append_getLast ht0).symm
                          · -- (t.getLast ht0).1 = data1
                            have hg1 := getLast_append_of_ne_nil (a := r) (t := t) ht0
                            -- hg1 : (r++t).getLast(…) = t.getLast ht0
                            -- 从 htail_eq:(r++t) = es''++[u]——getLast 相等:
                            have hg2 : (r ++ t).getLast (by
                                intro h0
                                apply ht0
                                -- (r++t) = [] → t = []
                                have hlen4 : (r ++ t).length = 0 := congrArg List.length h0
                                rw [List.length_append] at hlen4
                                have htlen : t.length = 0 := by omega
                                exact length_eq_zero_of_eq_zero htlen) = u := by
                              -- es''++[u] 的末 = u;list 相等 htail_eq.symm:
                              have hg2' : (es'' ++ [u]).getLast (by
                                  intro h0
                                  apply ht0
                                  have hlen5 : (es'' ++ [u]).length = 0 := congrArg List.length h0
                                  simp at hlen5) = u := List.getLast_append_singleton es''
                              -- rw [htail_eq] 于目标——list 重写依赖?——subst 法不行(表达式)——用 calc + congr:
                              -- (r++t).getLast h = (es''++[u]).getLast h'——由 htail_eq:getElem_congr 类……getLast 无索引——**直接 subst 式:htail_eq : r ++ t = es'' ++ [u]——两边 getLast——rw [htail_eq] at 目标(目标 LHS (r++t).getLast ——rw 依赖(界证明 h 类型含 (r++t))——h 由 by 块(文本依赖 (r++t))——rw 替换后 h 的类型变——motive 错?——试 exact:
                              -- 目标 (r++t).getLast h = u——(es''++[u]).getLast h' = u(hg2')——经 htail_eq:
                              -- congrArg (fun l => l.getLast …) 不行(界依赖 l)
                              -- **用 getElem_congr 同法:getLast 的界不是索引——getLast h 的 h : l ≠ [] 依赖 l——与 getElem_congr 同样用 subst:htail_eq 两侧非变量……
                              -- 换:用 dropLast 分解一致性:es''++[u] = r++t——es'' 长度……u = (r++t) 的末——**绕过:不用 getLast,tail 分解**:t 的分解 t = t'++[u] 由 htail_eq + t 是 (r++t) 的后缀……——直接看 t:htail_eq : r ++ t = es'' ++ [u]——**从该等式推出 t 末 u 的引理**:
                              -- 分解比较:r++t = es''++[u] 且 t ≠ []——t = es''.drop r.length ++ [u]?——u 必在 t 内(它是末元素,r 的长度截断):t 末 = u:
                              -- **simpa [htail_eq] using hg2'?**——hg2' 的目标换 (es''++[u]) → (r++t)??——simpa [htail_eq] 用 htail_eq(方向 r++t = es''++[u]——rw 把 (r++t) 换 (es''++[u])?——simpa [← htail_eq] using hg2'?——hg2' : (es''++[u]).getLast(…) = u——simpa [← htail_eq] :目标 (es''++[u]) 的 getLast 换 (r++t)?——simpa [← htail_eq] using hg2' 的目标变成 (r++t).getLast(…) = u——界 h 类型……simpa 处理
                              simpa [← htail_eq] using hg2'
                            -- 最后 (t.getLast ht0).1 = u.1:
                            have hgl : t.getLast ht0 = u := by
                              rw [← hg1]
                              exact hg2
                            rw [hgl]
                            exact hu1
                have hlt_n : t.length < n := by
                  rw [← hlen]
                  exact hlt
                have hwt : WellFormedElems t :=
                  ih t.length hlt_n t rfl htfirst htdata htstruct htlast
                exact hwt
  exact hmain es.length es rfl hfirst hdata hstruct hlast

-- ============================================================================
-- q11a-4 主定理辅助:解析结果非空/正性
-- ============================================================================

/-- 良好 es 非空 → parse 非空。 -/
lemma parse_ne_of_wf (es : List Sym) (hw : WellFormedElems es) (hne : es ≠ []) :
    parseElementsSym es ≠ [] := by
  cases hw with
  | nil => exact (hne rfl).elim
  | cons s rest r t hα hcdr hr hrend hwt =>
      intro hp
      have hparse : parseElementsSym (s :: rest) = decodeBitsSym r :: parseElementsSym t := by
        rw [hα]
        simp [parseElementsSym, Sym.alpha, hcdr]
      rw [hparse] at hp
      simp at hp


/-- 良好 es(段末 data1、α 左邻 data1、全符号、mark false)→ 每元素正。 -/
lemma parse_pos_of_wf (es : List Sym) (hw : WellFormedElems es)
    (hdata : ∀ s ∈ es, s = Sym.data0 ∨ s = Sym.data1 ∨ s = Sym.alpha)
    (hmk : ∀ s ∈ es, s.2 = false)
    (hleft : ∀ j : ℕ, (hj : j < es.length) → (es[j]'(hj)).1 = SymKind.alpha → 0 < j →
      (es[j - 1]'(by omega)).1 = SymKind.data1)
    (hlast : es = [] ∨ ∃ es' u, es = es' ++ [u] ∧ u.1 = SymKind.data1) :
    ∀ v ∈ parseElementsSym es, 0 < v := by
  induction hw with
  | nil =>
      intro v hv
      simp [parseElementsSym] at hv
  | cons s rest r t hα hcdr hr hrend hwt ih =>
      have hspec := collectDataRun_spec rest
      have hrt : rest = r ++ t := by
        rw [hspec.1]
        simp [hcdr]
      intro v hv
      have hparse : parseElementsSym (s :: rest) = decodeBitsSym r :: parseElementsSym t := by
        rw [hα]
        simp [parseElementsSym, Sym.alpha, hcdr]
      rw [hparse] at hv
      simp at hv
      rcases hv with hv1 | hv2
      · -- v = decodeBitsSym r:r 非空且末 data1 全符号 → 正
        rw [hv1]
        have hrne : r ≠ [] := by
          intro hr0
          rcases hrend with hrl | ⟨r', u, hrr, hu1⟩
          · -- r = []:空段情形(连续 α 或单 α)排除
            rcases hspec.2.2 with ht0 | ⟨u0, ts, hteq, hu0nd⟩
            · exfalso
              have ht0' : t = [] := by simpa [hcdr] using ht0
              rcases hlast with hle | ⟨es', u, hes, hu1⟩
              · simp at hle
              · have hrest0 : rest = [] := by
                  rw [hrt, hr0, ht0']
                  simp
                have hu_s : u = s := by
                  cases es' with
                  | nil =>
                      have hes' : [s] = [u] := by simpa [hrest0] using hes
                      injection hes' with hsu
                      exact hsu.symm
                  | cons x es'' =>
                      exfalso
                      have hes'' : s :: rest = x :: (es'' ++ [u]) := by simpa using hes
                      have htail' : rest = es'' ++ [u] := by
                        simpa using congrArg List.tail hes''
                      rw [hrest0] at htail'
                      exact (by simp : es'' ++ [u] ≠ []) htail'.symm
                rw [hu_s, hα] at hu1
                simp [Sym.alpha] at hu1
            · exfalso
              have hteq' : t = u0 :: ts := by simpa [hcdr] using hteq
              have hu0_es : u0 ∈ s :: rest := by
                simp [hrt, hr0, hteq']
              rcases hdata u0 hu0_es with hd0 | hd1 | hαu0
              · exfalso; exact hu0nd (by simp [hd0, isDataSym])
              · exfalso; exact hu0nd (by simp [hd1, isDataSym])
              · have hb1 : 1 < (s :: rest).length := by
                  have hlen : (s :: rest).length = 2 + ts.length := by
                    calc
                      (s :: rest).length = (s :: u0 :: ts).length := by
                        exact congrArg List.length (by simp [hrt, hr0, hteq'])
                      _ = 2 + ts.length := by
                        simp only [List.length_cons]
                        omega
                  rw [hlen]
                  omega
                have hα1 : ((s :: rest)[1]'(hb1)).1 = SymKind.alpha := by
                  calc
                    ((s :: rest)[1]'(hb1)).1 = ((s :: u0 :: ts)[1]'(by
                        simp [hrt, hr0, hteq'])).1 := by
                          have hseq : s :: rest = s :: u0 :: ts := by simp [hrt, hr0, hteq']
                          have hge := getElem_congr (l := s :: rest) (l' := s :: u0 :: ts)
                            (i := 1) hseq hb1 (by
                              simp [hrt, hr0, hteq'])
                          exact congrArg (fun x : Sym => x.1) hge
                    _ = u0.1 := by rfl
                    _ = SymKind.alpha := by
                      rw [hαu0]
                      rfl
                have hleft1 := hleft 1 hb1 hα1 (by omega)
                simp [hrt, hr0, hteq', hα, Sym.alpha] at hleft1
          · -- hrend inr:r = r'++[u] 非空 → 与 r = [] 矛盾
            rw [hrr] at hr0
            simp at hr0
        rcases hrend with hrl | ⟨r', u, hrr, hu1⟩
        · exfalso
          exact hrne hrl
        · have hu_r : u ∈ r := by
            rw [hrr]
            simp
          have hu_mark : u.2 = false := hmk u (by
            have hu_rest : u ∈ rest := by
              rw [hrt]
              exact List.mem_append_left t hu_r
            exact List.mem_cons_of_mem s hu_rest)
          have hu_sym : u = Sym.data1 := sym_eq_data1_of_kind_of_mark hu1 hu_mark
          have hd1 : Sym.data1 ∈ r := by
            rw [hu_sym] at hu_r
            exact hu_r
          exact decodeBitsSym_pos_of_data1 hd1
      · -- v ∈ parse t:递归(ih)——喂 t 版前提
        have htdata : ∀ s0 ∈ t, s0 = Sym.data0 ∨ s0 = Sym.data1 ∨ s0 = Sym.alpha := by
          intro s0 hs0
          have hs0_rest : s0 ∈ rest := by
            rw [hrt]
            exact List.mem_append_right _ hs0
          exact hdata s0 (List.mem_cons_of_mem s hs0_rest)
        have hmkt : ∀ s0 ∈ t, s0.2 = false := by
          intro s0 hs0
          have hs0_rest : s0 ∈ rest := by
            rw [hrt]
            exact List.mem_append_right _ hs0
          exact hmk s0 (List.mem_cons_of_mem s hs0_rest)
        have hleftt : ∀ j : ℕ, (hj : j < t.length) → (t[j]'(hj)).1 = SymKind.alpha → 0 < j →
            (t[j - 1]'(by omega)).1 = SymKind.data1 := by
          exact struct_tail (s := s) (rest := rest) (r := r) (t := t) hrt hleft
        have hlastt : t = [] ∨ ∃ t' u, t = t' ++ [u] ∧ u.1 = SymKind.data1 := by
          by_cases ht0 : t = []
          · left; exact ht0
          · right
            rcases hlast with hle | ⟨es', u, hes, hu1⟩
            · simp at hle
            · -- t 非空:t 末 = es 末 = u(es = es'++[u])
              have htne : t ≠ [] := ht0
              have hene_sr : (s :: r) ++ t ≠ [] := by
                intro h0
                apply htne
                simpa using h0
              have hene_es : s :: rest ≠ [] := by
                intro h0
                apply htne
                have htail : rest = [] := by simpa using congrArg List.tail h0
                have hr0 : r ++ t = [] := by
                  rw [← hrt]
                  exact htail
                have hlen : (r ++ t).length = 0 := congrArg List.length hr0
                rw [List.length_append] at hlen
                have htlen : t.length = 0 := by omega
                exact length_eq_zero_of_eq_zero htlen
              have hg2 : (s :: rest).getLast hene_es = u := by
                have hg2' : (es' ++ [u]).getLast (by intro h0; simp at h0) = u :=
                  List.getLast_append_singleton es'
                exact (getLast_congr (l := es' ++ [u]) (l' := s :: rest) hes.symm
                  (by intro h0; simp at h0) hene_es).symm.trans hg2'
              refine ⟨t.dropLast, t.getLast htne, ?_, ?_⟩
              · exact (List.dropLast_append_getLast htne).symm
              · calc
                  (t.getLast htne).1 = ((s :: rest).getLast hene_es).1 := by
                    have hg1' : t.getLast htne = ((s :: r) ++ t).getLast hene_sr :=
                      (getLast_append_of_ne_nil (a := s :: r) htne).symm
                    have heq_sr : (s :: r) ++ t = s :: rest := by simp [hrt]
                    have hg3 : ((s :: r) ++ t).getLast hene_sr = (s :: rest).getLast hene_es :=
                      getLast_congr (l := (s :: r) ++ t) (l' := s :: rest) heq_sr hene_sr hene_es
                    rw [hg1']
                    rw [hg3]
                  _ = u.1 := by rw [hg2]
                  _ = SymKind.data1 := hu1
        have ih' := ih htdata hmkt hleftt hlastt
        exact ih' v hv2


-- ============================================================================
-- q11a-4 主定理:symAccepts → 精确前缀分解(w = encodeInstanceSym inst ++ g)
-- ============================================================================

theorem symAccepts_implies_encodeInstanceSym (w : List Sym) :
    symAccepts VerifierSym.transition VerifierSym.acceptStates w →
    ∃ inst : SubsetSumInstance, ∃ g : List Sym,
      w = encodeInstanceSym inst ++ g ∧
      inst.elements ≠ [] ∧ (∀ v ∈ inst.elements, 0 < v) ∧ 0 < inst.target := by
  intro h
  rcases h with ⟨π, cfg, hpath, hacc⟩
  have hπ : SymSteps VerifierSym.transition (symInitialConfig w) π cfg :=
    reachablePath_to_steps hpath
  have hs100 : cfg.state = 100 := by
    simpa [VerifierSym.acceptStates, VerifierSym.qAccept] using hacc
  have hno101 : ∀ step ∈ π, step.result.nextState ≠ 101 :=
    symAccepts_no_101 hπ hs100
  rcases backchain_to_first4 hπ (by rw [hs100]; native_decide) with
    ⟨π₁, π₂, cfg₄, hsplit, hπ₁, hs4, hno4₁, hrest⟩
  have hno101₁ : ∀ step ∈ π₁, step.result.nextState ≠ 101 := by
    intro step hstep
    exact hno101 step (by rw [hsplit]; exact List.mem_append_left _ hstep)
  rcases format_check_precise w π₁ cfg₄ hπ₁ hno4₁ hno101₁ hs4 with
    ⟨n, len, htmark, hmark, hb0m, hb1m, hb2m, hnpos, hd1n, hlenpos, hαf, hstruct, hmsb,
     hdata, hkind₃, hb0k, hbnk, hb2k⟩
  let tape₀ : ℤ → Sym := (symInitialConfig w).tape
  -- 长度界:n + 2 + len + 1 ≤ w.length
  have hlb : n + 2 + len + 1 ≤ w.length := by
    by_contra hlen
    by_cases hlen0 : len = 0
    · have hto2 : ((n : ℤ) + 2).toNat = n + 2 := by
        have hu : ↑(((n : ℤ) + 2).toNat) = (n : ℤ) + 2 := Int.toNat_of_nonneg (by omega)
        rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) from by rw [Int.natCast_add]; rfl] at hu
        omega
      have hcell2 : (symInitialConfig w).tape ((n : ℤ) + 2) = Sym.blank := by
        dsimp [symInitialConfig, SymConfig.mk]
        by_cases hcond : 0 ≤ (n : ℤ) + 2 ∧ ((n : ℤ) + 2).toNat < w.length
        · exfalso
          rcases hcond with ⟨_, hlt⟩
          rw [hto2] at hlt
          apply hlen
          rw [hlen0]
          omega
        · exact dif_neg hcond
      have hb1k' : ((symInitialConfig w).tape ((n : ℤ) + 2)).1 = SymKind.boundary := by
        simpa [hlen0, add_comm, add_left_comm, add_assoc] using hb2k
      rw [hcell2] at hb1k'
      dsimp [Sym.blank] at hb1k'
      cases hb1k'
    · have hto3 : ((n : ℤ) + 2 + (len : ℤ)).toNat = n + 2 + len := by
        have hu : ↑(((n : ℤ) + 2 + (len : ℤ)).toNat) = (n : ℤ) + 2 + (len : ℤ) :=
          Int.toNat_of_nonneg (by omega)
        rw [show (n : ℤ) + 2 + (len : ℤ) = ((n + 2 + len : ℕ) : ℤ) from by
          rw [Int.natCast_add, Int.natCast_add]; rfl] at hu
        omega
      have hcell3 : (symInitialConfig w).tape ((n : ℤ) + 2 + (len : ℤ)) = Sym.blank := by
        dsimp [symInitialConfig, SymConfig.mk]
        by_cases hcond : 0 ≤ (n : ℤ) + 2 + (len : ℤ) ∧ ((n : ℤ) + 2 + (len : ℤ)).toNat < w.length
        · exfalso
          rcases hcond with ⟨_, hlt⟩
          rw [hto3] at hlt
          apply hlen
          omega
        · exact dif_neg hcond
      have hb1k'' : ((symInitialConfig w).tape ((n : ℤ) + 2 + (len : ℤ))).1 = SymKind.boundary := hb2k
      rw [hcell3] at hb1k''
      dsimp [Sym.blank] at hb1k''
      cases hb1k''
  -- 切片定义
  let ts : List Sym := (w.drop 1).take n
  let es : List Sym := (w.drop (n + 2)).take len
  let g : List Sym := w.drop (n + 2 + len + 1)
  have hts_len : ts.length = n := by
    dsimp [ts]
    rw [length_drop_take]
    rw [Nat.min_eq_left (by omega)]
  have hes_len : es.length = len := by
    dsimp [es]
    rw [length_drop_take]
    rw [Nat.min_eq_left (by omega)]
  have hg_len : g.length = w.length - (n + 2 + len + 1) := by
    dsimp [g]
    simp [List.length_drop]
  -- w 分解:w = (w.take (n+2)) ++ es ++ (w.take? …)——先取基础分解:
  -- w = w.take (n + 2) ++ (w.drop (n + 2)).take len ++ w.drop (n + 2 + len)
  have hw_split : w = w.take (n + 2) ++ es ++ w.drop (n + 2 + len) := by
    calc
      w = w.take (n + 2) ++ w.drop (n + 2) := (List.take_append_drop (n + 2) w).symm
      _ = w.take (n + 2) ++ ((w.drop (n + 2)).take len ++ (w.drop (n + 2)).drop len) := by
        rw [List.take_append_drop len (w.drop (n + 2))]
      _ = w.take (n + 2) ++ es ++ w.drop (n + 2 + len) := by
        simp [es, List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  -- tape₀ 与 w:tapeAgrees
  have hta : tapeAgrees tape₀ 0 w := symInitialConfig_tapeAgrees w
  -- w[j] 与 tape₀ j 的桥(hlb 保证位置在界内):
  have hw_get : ∀ j : ℕ, (hj : j < w.length) → w[j]'(hj) = tape₀ (j : ℤ) := by
    intro j hj
    simpa using (hta j hj).symm
  -- 界分配:
  have hts_bd : ∀ j : ℕ, (hj : j < n) → j < ts.length := by
    intro j hj
    rw [hts_len]
    exact hj
  have hes_bd : ∀ j : ℕ, (hj : j < len) → j < es.length := by
    intro j hj
    rw [hes_len]
    exact hj
  -- ts 元素 = tape₀(1+j):
  have hts_get : ∀ j : ℕ, (hj : j < n) → ts[j]'(hts_bd j hj) = tape₀ ((1 + j : ℕ) : ℤ) := by
    intro j hj
    have hb : 1 + j < w.length := by omega
    calc
      ts[j]'(hts_bd j hj) = w[1 + j]'(hb) := by
        dsimp [ts]
        exact getElem_drop_take w 1 n j hj hb (hts_bd j hj)
      _ = tape₀ ((1 + j : ℕ) : ℤ) := hw_get (1 + j) hb
  -- es 元素 = tape₀(n+2+j):
  have hes_get : ∀ j : ℕ, (hj : j < len) → es[j]'(hes_bd j hj) = tape₀ (((n + 2 + j) : ℕ) : ℤ) := by
    intro j hj
    have hb : n + 2 + j < w.length := by omega
    calc
      es[j]'(hes_bd j hj) = w[n + 2 + j]'(hb) := by
        dsimp [es]
        exact getElem_drop_take w (n + 2) len j hj hb (hes_bd j hj)
      _ = tape₀ (((n + 2 + j) : ℕ) : ℤ) := hw_get (n + 2 + j) hb
  -- w[n+2+len] = tape₀(n+2+len)(用于 g 段的分界):
  have hw_blast : w[n + 2 + len]'(by omega) = tape₀ ((n + 2 + len : ℕ) : ℤ) := by
    exact hw_get (n + 2 + len) (by omega)

  -- ts 全 data(符号级):
  have hts_data : ∀ s ∈ ts, s = Sym.data0 ∨ s = Sym.data1 := by
    intro s hs
    rcases List.getElem_of_mem hs with ⟨j, hj, hjs⟩
    have hj_n : j < n := by
      rw [hts_len] at hj
      exact hj
    have hjs' : ts[j]'(hts_bd j hj_n) = s := by
      calc
        ts[j]'(hts_bd j hj_n) = ts[j]'(hj) := getElem_irrel (hts_bd j hj_n) hj
        _ = s := hjs
    have hs_tape : s = tape₀ ((1 + j : ℕ) : ℤ) := by
      rw [← hjs']
      exact hts_get j hj_n
    have hs_kind : s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
      rw [hs_tape]
      exact hdata j hj_n
    have hs_mark : s.2 = false := by
      rw [hs_tape]
      exact htmark j hj_n
    rcases hs_kind with hk0 | hk1
    · left; exact sym_eq_data0_of_kind_of_mark hk0 hs_mark
    · right; exact sym_eq_data1_of_kind_of_mark hk1 hs_mark
  -- ts 末 = data1(符号级):
  have hts_last : ts[n - 1]'(hts_bd (n - 1) (by omega)) = Sym.data1 := by
    have hkindn : (tape₀ (n : ℤ)).1 = SymKind.data1 := hd1n
    have hmarkn : (tape₀ (n : ℤ)).2 = false := by
      simpa [tape₀, show (1 + ((n - 1 : ℕ) : ℤ)) = (n : ℤ) by omega] using htmark (n - 1) (by omega)
    have htape : tape₀ (n : ℤ) = Sym.data1 := sym_eq_data1_of_kind_of_mark hkindn hmarkn
    calc
      ts[n - 1]'(hts_bd (n - 1) (by omega)) = tape₀ ((1 + (n - 1) : ℕ) : ℤ) :=
        hts_get (n - 1) (by omega)
      _ = tape₀ (n : ℤ) := by
        simpa [show (1 + (n - 1) : ℕ) = n by omega]
      _ = Sym.data1 := htape
  -- 往返 2:encodeBitsSym (decodeBitsSym ts) = ts
  have henc_ts : encodeBitsSym (decodeBitsSym ts) = ts := by
    apply encodeBitsSym_decode_eq_self
    · exact hts_data
    · right
      have htsne : ts ≠ [] := by
        intro hts0
        have : ts.length = 0 := congrArg List.length hts0
        rw [hts_len] at this
        omega
      refine ⟨ts.dropLast, Sym.data1, ?_, ?_⟩
      · have hget : ts.getLast htsne = Sym.data1 := by
          calc
            ts.getLast htsne = ts[ts.length - 1]'(by
              have hpos : 0 < ts.length := by rw [hts_len]; exact hnpos
              omega) := List.getLast_eq_getElem htsne
            _ = ts[n - 1]'(hts_bd (n - 1) (by omega)) := by
              have hidx : ts.length - 1 = n - 1 := by
                rw [hts_len]
              exact getElem_of_index_eq (l := ts) (i := ts.length - 1) (j := n - 1) hidx
                (by
                  have hpos : 0 < ts.length := by rw [hts_len]; exact hnpos
                  omega)
                (hts_bd (n - 1) (by omega))
            _ = Sym.data1 := hts_last
        calc
          ts = ts.dropLast ++ [ts.getLast htsne] := (List.dropLast_append_getLast htsne).symm
          _ = ts.dropLast ++ [Sym.data1] := by rw [hget]
      · rfl
  -- es 头 = α(符号级):
  have hes0_alpha : es[0]'(hes_bd 0 hlenpos) = Sym.alpha := by
    have hkind0 : (tape₀ ((n + 2 : ℕ) : ℤ)).1 = SymKind.alpha := by
      simpa [tape₀] using hαf
    have hmark0 : (tape₀ ((n + 2 : ℕ) : ℤ)).2 = false := hmark 0 hlenpos
    have htape : tape₀ ((n + 2 : ℕ) : ℤ) = Sym.alpha := sym_eq_alpha_of_kind_of_mark hkind0 hmark0
    calc
      es[0]'(hes_bd 0 hlenpos) = tape₀ (((n + 2 + 0) : ℕ) : ℤ) := hes_get 0 hlenpos
      _ = tape₀ ((n + 2 : ℕ) : ℤ) := by
        simpa [show (n + 2 + 0 : ℕ) = n + 2 by omega]
      _ = Sym.alpha := htape
  -- es 非空与头分解:
  have hes_ne : es ≠ [] := by
    intro hes0
    have : es.length = 0 := congrArg List.length hes0
    rw [hes_len] at this
    omega
  have hfirst_es : es = [] ∨ (∃ s rest, es = s :: rest ∧ s = Sym.alpha) := by
    right
    rcases List.exists_cons_of_ne_nil hes_ne with ⟨s0, rest0, hes_cons⟩
    have hs0 : s0 = Sym.alpha := by
      have h0 : es[0]'(hes_bd 0 hlenpos) = s0 := by
        simp [hes_cons]
      exact h0.symm.trans hes0_alpha
    refine ⟨s0, rest0, hes_cons, hs0⟩
  -- es 全符号:
  have hdata_es : ∀ s ∈ es, s = Sym.data0 ∨ s = Sym.data1 ∨ s = Sym.alpha := by
    intro s hs
    rcases List.getElem_of_mem hs with ⟨j, hj, hjs⟩
    have hj_len : j < len := by
      rw [hes_len] at hj
      exact hj
    have hjs' : es[j]'(hes_bd j hj_len) = s := by
      calc
        es[j]'(hes_bd j hj_len) = es[j]'(hj) := getElem_irrel (hes_bd j hj_len) hj
        _ = s := hjs
    have hs_tape : s = tape₀ (((n + 2 + j) : ℕ) : ℤ) := by
      rw [← hjs']
      exact hes_get j hj_len
    have hs_kind : s.1 = SymKind.alpha ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
      rw [hs_tape]
      exact hkind₃ j hj_len
    have hs_mark : s.2 = false := by
      rw [hs_tape]
      exact hmark j hj_len
    rcases hs_kind with hα | hd0 | hd1
    · exact Or.inr (Or.inr (sym_eq_alpha_of_kind_of_mark hα hs_mark))
    · exact Or.inl (sym_eq_data0_of_kind_of_mark hd0 hs_mark)
    · exact Or.inr (Or.inl (sym_eq_data1_of_kind_of_mark hd1 hs_mark))
  -- es 的 α-左邻 data1(es 形):
  have hstruct_es : ∀ j : ℕ, (hj : j < es.length) → (es[j]'(hj)).1 = SymKind.alpha → 0 < j →
      (es[j - 1]'(by omega)).1 = SymKind.data1 := by
    intro j hj hαj hposj
    have hj_len : j < len := by
      rw [hes_len] at hj
      exact hj
    have hαtape : ((symInitialConfig w).tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.alpha := by
      have hgj : es[j]'(hes_bd j hj_len) = tape₀ (((n + 2 + j) : ℕ) : ℤ) := hes_get j hj_len
      have hαj' : (es[j]'(hes_bd j hj_len)).1 = SymKind.alpha := by
        rw [getElem_irrel hj (hes_bd j hj_len)] at hαj
        exact hαj
      rw [hgj] at hαj'
      simpa [tape₀] using hαj'
    have hstr := hstruct j hj_len hαtape (by omega)
    calc
      (es[j - 1]'(by omega)).1
          = (es[j - 1]'(hes_bd (j - 1) (by omega : j - 1 < len))).1 := by
            rw [getElem_irrel (by omega : j - 1 < es.length) (hes_bd (j - 1) (by omega : j - 1 < len))]
      _ = ((symInitialConfig w).tape ((n : ℤ) + 2 + ((j - 1 : ℕ) : ℤ))).1 := by
        rw [hes_get (j - 1) (by omega : j - 1 < len)]
        simpa [tape₀]
      _ = SymKind.data1 := hstr
  -- es 末 data1(分解形):
  have hlast_es : es = [] ∨ ∃ es' u, es = es' ++ [u] ∧ u.1 = SymKind.data1 := by
    right
    refine ⟨es.dropLast, Sym.data1, ?_, ?_⟩
    · have hlast1 : es[len - 1]'(hes_bd (len - 1) (by omega)) = Sym.data1 := by
        have hkindl : ((symInitialConfig w).tape ((n : ℤ) + 2 + ((len - 1 : ℕ) : ℤ))).1 = SymKind.data1 := hmsb
        have hmarkl : ((symInitialConfig w).tape ((n : ℤ) + 2 + ((len - 1 : ℕ) : ℤ))).2 = false := hmark (len - 1) (by omega)
        have htape : ((symInitialConfig w).tape ((n : ℤ) + 2 + ((len - 1 : ℕ) : ℤ))) = Sym.data1 :=
          sym_eq_data1_of_kind_of_mark hkindl hmarkl
        calc
          es[len - 1]'(hes_bd (len - 1) (by omega)) = tape₀ (((n + 2 + (len - 1) : ℕ) : ℤ)) :=
            hes_get (len - 1) (by omega)
          _ = Sym.data1 := by
            simpa [tape₀] using htape
      have hget : es.getLast hes_ne = Sym.data1 := by
        calc
          es.getLast hes_ne = es[es.length - 1]'(by
            have hpos : 0 < es.length := by rw [hes_len]; exact hlenpos
            omega) := List.getLast_eq_getElem hes_ne
          _ = es[len - 1]'(hes_bd (len - 1) (by omega)) := by
            have hidx : es.length - 1 = len - 1 := by rw [hes_len]
            exact getElem_of_index_eq (l := es) (i := es.length - 1) (j := len - 1) hidx
              (by
                have hpos : 0 < es.length := by rw [hes_len]; exact hlenpos
                omega)
              (hes_bd (len - 1) (by omega))
          _ = Sym.data1 := hlast1
      calc
        es = es.dropLast ++ [es.getLast hes_ne] := (List.dropLast_append_getLast hes_ne).symm
        _ = es.dropLast ++ [Sym.data1] := by rw [hget]
    · rfl
  -- 结构良好 + P2:
  have hw_es : WellFormedElems es :=
    WellFormedElems_of es hfirst_es hdata_es hstruct_es hlast_es
  have henc_es : encodeElementsSym (parseElementsSym es) = es :=
    encodeElementsSym_parse_of_wellformed hw_es

  -- 段 A+B:w.take (n+2) = [b] ++ ts ++ [b]
  have hw_take : w.take (n + 2) = [Sym.boundary] ++ ts ++ [Sym.boundary] := by
    calc
      w.take (n + 2) = w.take 1 ++ (w.drop 1).take (n + 1) := by
        rw [show n + 2 = 1 + (n + 1) by omega]
        exact List.take_add
      _ = [w[0]'(by omega)] ++ (w.drop 1).take (n + 1) := by
        have ht1 := take_one_eq_singleton w (by omega : 0 < w.length)
        rw [ht1]
      _ = [Sym.boundary] ++ (w.drop 1).take (n + 1) := by
        have hw0 : w[0]'(by omega) = Sym.boundary := by
          calc
            w[0]'(by omega) = tape₀ (0 : ℤ) := hw_get 0 (by omega)
            _ = Sym.boundary := sym_eq_boundary_of_kind_of_mark hb0k hb0m
        rw [hw0]
      _ = [Sym.boundary] ++ ts ++ [w[n + 1]'(by omega)] := by
        have hseg : (w.drop 1).take (n + 1) = ts ++ (w.drop (n + 1)).take 1 := by
          calc
            (w.drop 1).take (n + 1) = (w.drop 1).take n ++ (List.drop n (w.drop 1)).take 1 := by
              exact @List.take_add _ (w.drop 1) n 1
            _ = ts ++ (w.drop (n + 1)).take 1 := by
              dsimp [ts]
              rw [show List.drop n (w.drop 1) = w.drop (n + 1) by
                rw [List.drop_drop]
                rw [show 1 + n = n + 1 by omega]]
        have ht1 := take_one_eq_singleton (w.drop (n + 1)) (by
          simp [List.length_drop]
          omega)
        have hg0 := List.getElem_drop (xs := w) (i := n + 1) (j := 0) (h := by
          simp [List.length_drop]
          omega)
        have hg0' : (w.drop (n + 1))[0]'(by
            simp [List.length_drop]
            omega) = w[n + 1]'(by omega) := by
          simpa [show n + 1 + 0 = n + 1 by omega] using hg0
        rw [hseg, ht1, hg0']
        simp [List.append_assoc]
      _ = [Sym.boundary] ++ ts ++ [Sym.boundary] := by
        have hw_n1 : w[n + 1]'(by omega) = Sym.boundary := by
          calc
            w[n + 1]'(by omega) = tape₀ ((n + 1 : ℕ) : ℤ) := hw_get (n + 1) (by omega)
            _ = Sym.boundary := sym_eq_boundary_of_kind_of_mark hbnk hb1m
        rw [hw_n1]
  -- 段 C:w.drop (n+2+len) = [b] ++ g
  have hw_drop : w.drop (n + 2 + len) = [Sym.boundary] ++ g := by
    calc
      w.drop (n + 2 + len) = (w.drop (n + 2 + len)).take 1 ++ (w.drop (n + 2 + len)).drop 1 := by
        exact (List.take_append_drop 1 (w.drop (n + 2 + len))).symm
      _ = [w[n + 2 + len]'(by omega)] ++ g := by
        have ht1 := take_one_eq_singleton (w.drop (n + 2 + len)) (by
          simp [List.length_drop]
          omega)
        have hg0 := List.getElem_drop (xs := w) (i := n + 2 + len) (j := 0) (h := by
          simp [List.length_drop]
          omega)
        have hg0' : (w.drop (n + 2 + len))[0]'(by
            simp [List.length_drop]
            omega) = w[n + 2 + len]'(by omega) := by
          simpa [show n + 2 + len + 0 = n + 2 + len by omega] using hg0
        rw [ht1, hg0']
        dsimp [g]
        rw [List.drop_drop]
      _ = [Sym.boundary] ++ g := by
        have hwb : w[n + 2 + len]'(by omega) = Sym.boundary := by
          calc
            w[n + 2 + len]'(by omega) = tape₀ ((n + 2 + len : ℕ) : ℤ) := hw_get (n + 2 + len) (by omega)
            _ = Sym.boundary := sym_eq_boundary_of_kind_of_mark hb2k hb2m
        rw [hwb]
  -- inst 构造:
  let elems : List ℕ := parseElementsSym es
  let target : ℕ := decodeBitsSym ts
  let inst : SubsetSumInstance := { elements := elems, target := target }
  have henc_inst : encodeInstanceSym inst = [Sym.boundary] ++ ts ++ [Sym.boundary] ++ es ++ [Sym.boundary] := by
    dsimp [inst, target, elems, encodeInstanceSym]
    rw [henc_ts, henc_es]
  -- 正性:
  have hmark_es : ∀ s ∈ es, s.2 = false := by
    intro s hs
    rcases List.getElem_of_mem hs with ⟨j, hj, hjs⟩
    have hj_len : j < len := by
      rw [hes_len] at hj
      exact hj
    have hjs' : es[j]'(hes_bd j hj_len) = s := by
      calc
        es[j]'(hes_bd j hj_len) = es[j]'(hj) := getElem_irrel (hes_bd j hj_len) hj
        _ = s := hjs
    have hs_tape : s = tape₀ (((n + 2 + j) : ℕ) : ℤ) := by
      rw [← hjs']
      exact hes_get j hj_len
    rw [hs_tape]
    exact hmark j hj_len
  have hpos_v : ∀ v ∈ parseElementsSym es, 0 < v :=
    parse_pos_of_wf es hw_es hdata_es hmark_es hstruct_es hlast_es
  have helems_ne : parseElementsSym es ≠ [] := parse_ne_of_wf es hw_es hes_ne
  have htarget_pos : 0 < decodeBitsSym ts := by
    have hmem : Sym.data1 ∈ ts := by
      exact List.mem_iff_getElem.mpr ⟨n - 1, hts_bd (n - 1) (by omega), hts_last⟩
    exact decodeBitsSym_pos_of_data1 hmem
  -- 组装:
  refine ⟨inst, g, ?_, ?_, ?_, ?_⟩
  · calc
      w = w.take (n + 2) ++ es ++ w.drop (n + 2 + len) := hw_split
      _ = ([Sym.boundary] ++ ts ++ [Sym.boundary]) ++ es ++ ([Sym.boundary] ++ g) := by
        rw [hw_take, hw_drop]
      _ = encodeInstanceSym inst ++ g := by
        rw [henc_inst]
        simp [List.append_assoc]
  · dsimp [inst]
    exact helems_ne
  · intro v hv
    dsimp [inst] at hv
    exact hpos_v v hv
  · dsimp [inst]
    exact htarget_pos



end Mp
