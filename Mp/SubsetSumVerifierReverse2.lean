/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/


import Mp.SubsetSumVerifierState

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

/-- q ∈ [4,101] 时 nextState ≥ 4 或 = 101。 -/
lemma transition_nextState_ge4_of_ge4 (q : ℕ) (s : Sym) (r : SymTransResult)
    (hq : 4 ≤ q) (hqle : q ≤ 101) (hr : r ∈ VerifierSym.transition (q, s)) :
    4 ≤ r.nextState ∨ r.nextState = 101 := by
  by_cases hqin : q ∈ VerifierSym.legalStates
  · have hq_cases : q ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 76, 77, 81, 84, 85, 86, 87, 38, 51, 23} : Finset ℕ) ∨
        q = 24 ∨ q = 26 ∨ q = 27 ∨ q = 28 ∨ q = 29 ∨ q = 100 ∨ q = 101 := by
      simp [VerifierSym.legalStates] at hqin
      simp only [Finset.mem_insert, Finset.mem_singleton] at ⊢
      omega
    have hdec24 : ∀ q ∈ ({24, 26, 27, 28, 29, 100, 101} : Finset ℕ),
        ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
          r ∈ VerifierSym.transition (q, Sym.mk k m) →
            4 ≤ r.nextState ∨ r.nextState = 101 := by
      native_decide
    rcases hq_cases with hdet | h24 | h26 | h27 | h28 | h29 | h100 | h101
    · have hin := transition_nextState_in_det q s r hdet hr
      rcases hin with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14
      all_goals (left <;> omega)
    · subst q
      rcases s with ⟨k, m⟩
      exact hdec24 24 (by simp) k m r hr
    · subst q
      rcases s with ⟨k, m⟩
      exact hdec24 26 (by simp) k m r hr
    · subst q
      rcases s with ⟨k, m⟩
      exact hdec24 27 (by simp) k m r hr
    · subst q
      rcases s with ⟨k, m⟩
      exact hdec24 28 (by simp) k m r hr
    · subst q
      rcases s with ⟨k, m⟩
      exact hdec24 29 (by simp) k m r hr
    · subst q
      rcases s with ⟨k, m⟩
      exact hdec24 100 (by simp) k m r hr
    · subst q
      rcases s with ⟨k, m⟩
      exact hdec24 101 (by simp) k m r hr
  · dsimp [VerifierSym.transition] at hr
    split at hr
    · exfalso
      rename_i hqin2
      exact hqin hqin2
    · simp only [Finset.mem_singleton] at hr
      subst r
      right
      rfl

/-- 转移表中任何结果行的 nextState ≥ 1。 -/
lemma transition_nextState_ge1 (q : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) : 1 ≤ r.nextState := by
  by_cases hqin : q ∈ VerifierSym.legalStates
  · by_cases hq4 : q < 4
    · -- q ∈ {0,1,2,3}：转移 nextState ∈ {1,2,3,24,101} ≥ 1
      interval_cases q
      · have hdec0 : ∀ k : SymKind, ∀ m : Bool, ∀ r ∈ VerifierSym.transition (0, Sym.mk k m),
            1 ≤ r.nextState := by
          decide
        rcases s with ⟨k, m⟩
        exact hdec0 k m r hr
      · have hdec1 : ∀ k : SymKind, ∀ m : Bool, ∀ r ∈ VerifierSym.transition (1, Sym.mk k m),
            1 ≤ r.nextState := by
          decide
        rcases s with ⟨k, m⟩
        exact hdec1 k m r hr
      · have hdec2 : ∀ k : SymKind, ∀ m : Bool, ∀ r ∈ VerifierSym.transition (2, Sym.mk k m),
            1 ≤ r.nextState := by
          decide
        rcases s with ⟨k, m⟩
        exact hdec2 k m r hr
      · have hdec3 : ∀ k : SymKind, ∀ m : Bool, ∀ r ∈ VerifierSym.transition (3, Sym.mk k m),
            1 ≤ r.nextState := by
          decide
        rcases s with ⟨k, m⟩
        exact hdec3 k m r hr
    · -- q ≥ 4：nextState ≥ 4 或 101（ge4 引理）
      rcases transition_nextState_ge4_of_ge4 q s r (by omega) (by simp [VerifierSym.legalStates] at hqin; omega) hr with h4 | h101
      · omega
      · simp [h101]
  · dsimp [VerifierSym.transition] at hr
    split at hr
    · exfalso
      rename_i hqin2
      exact hqin hqin2
    · simp only [Finset.mem_singleton] at hr
      subst r
      simp
/-- 可达域内 no-retreat 的逆否：后继 < 4 则前驱 < 4。 -/
lemma transition_nextState_lt4_of_lt4 (q : ℕ) (s : Sym) (r : SymTransResult)
    (hq : q ≤ 101)
    (hr : r ∈ VerifierSym.transition (q, s)) (hnext : r.nextState < 4) :
    q < 4 := by
  by_cases hqin : q ∈ VerifierSym.legalStates
  · by_contra hq4
    rcases transition_nextState_ge4_of_ge4 q s r (by omega) hq hr with h4 | h101
    · omega
    · simp [h101] at hnext
  · dsimp [VerifierSym.transition] at hr
    split at hr
    · exfalso
      rename_i hqin2
      exact hqin hqin2
    · simp only [Finset.mem_singleton] at hr
      subst r
      norm_num at hnext
/-- 状态 0 读 #ₗ → 1 R（唯一转移）。 -/
lemma trans0_step (r : SymTransResult) (hr : r ∈ VerifierSym.transition (0, Sym.boundary)) :
    r = SymTransResult.mk 1 Sym.boundary Dir.R := by
  have hdec : ∀ r ∈ VerifierSym.transition (0, Sym.boundary),
      r = SymTransResult.mk 1 Sym.boundary Dir.R := by
    decide
  exact hdec r hr

/-- 状态 2 的下一步 ∈ {2, 3, 101}。 -/
lemma trans2_next_state (s : Sym) (r : SymTransResult) (hr : r ∈ VerifierSym.transition (2, s)) :
    r.nextState = 2 ∨ r.nextState = 3 ∨ r.nextState = 101 := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (2, Sym.mk k m) →
        r.nextState = 2 ∨ r.nextState = 3 ∨ r.nextState = 101 := by
    native_decide
  rcases s with ⟨k, m⟩
  exact hdec k m r hr

/-- 状态 2 读 data 位：写回原符号、右移、停留 2。 -/
lemma trans2_data (s : Sym) (r : SymTransResult) (hs : s.1 = SymKind.data0 ∨ s.1 = SymKind.data1)
    (hr : r ∈ VerifierSym.transition (2, s)) :
    r = SymTransResult.mk 2 s Dir.R := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (2, Sym.mk k m) → (k = SymKind.data0 ∨ k = SymKind.data1) →
        r = SymTransResult.mk 2 (Sym.mk k m) Dir.R := by
    native_decide
  rcases s with ⟨k, m⟩
  exact hdec k m r hr hs

/-- 状态 2 读无标记 α：双分支写 sel/nosel、右移、停留 2（带标记 α 与 β 读到即陷阱）。 -/
lemma trans2_branch (s : Sym) (r : SymTransResult) (hs : s.1 = SymKind.alpha ∧ s.2 = false)
    (hr : r ∈ VerifierSym.transition (2, s)) :
    r = SymTransResult.mk 2 Sym.sel Dir.R ∨ r = SymTransResult.mk 2 Sym.nosel Dir.R := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (2, Sym.mk k m) → k = SymKind.alpha → m = false →
        r = SymTransResult.mk 2 Sym.sel Dir.R ∨ r = SymTransResult.mk 2 Sym.nosel Dir.R := by
    native_decide
  rcases s with ⟨k, m⟩
  have hm : m = false := by simpa using hs.2
  exact hdec k m r hr hs.1 hm

/-- 状态 2 读 #₁：写回、停留、转 3。 -/
lemma trans2_boundary (r : SymTransResult) (hr : r ∈ VerifierSym.transition (2, Sym.boundary)) :
    r = SymTransResult.mk 3 Sym.boundary Dir.S := by
  have hdec : ∀ r ∈ VerifierSym.transition (2, Sym.boundary),
      r = SymTransResult.mk 3 Sym.boundary Dir.S := by
    decide
  exact hdec r hr

/-- 状态 3 读未标 #₁：写 (boundary,true)、左移、转 24。 -/
lemma trans3_hash1 (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (3, Sym.mk SymKind.boundary false)) :
    r = SymTransResult.mk 24 (Sym.mk SymKind.boundary true) Dir.L := by
  have hdec : ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (3, Sym.mk SymKind.boundary false) →
        r = SymTransResult.mk 24 (Sym.mk SymKind.boundary true) Dir.L := by
    native_decide
  exact hdec r hr

/-- 状态 3 读已标 #₁：转 101。 -/
lemma trans3_hash1_marked (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (3, Sym.mk SymKind.boundary true)) :
    r.nextState = 101 := by
  have hdec : ∀ r ∈ VerifierSym.transition (3, Sym.mk SymKind.boundary true),
      r.nextState = 101 := by
    decide
  exact hdec r hr

/-- fmt 段（24/29/26/27/38/28）全部写回原符号。 -/
lemma fmt_write_s (q : ℕ) (s : Sym) (r : SymTransResult)
    (hq : q ∈ ({24, 29, 26, 27, 38, 28} : Finset ℕ))
    (hr : r ∈ VerifierSym.transition (q, s)) :
    r.writeSym = s := by
  have hdec : ∀ q ∈ ({24, 29, 26, 27, 38, 28} : Finset ℕ),
      ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (q, Sym.mk k m) → r.writeSym = Sym.mk k m := by
    native_decide
  rcases s with ⟨k, m⟩
  exact hdec q hq k m r hr

/-- 状态 24：读 (data1,false) → 29 L；否则 101。 -/
lemma trans24_step (s : Sym) (r : SymTransResult) (hr : r ∈ VerifierSym.transition (24, s)) :
    (s.1 = SymKind.data1 ∧ s.2 = false ∧ r = SymTransResult.mk 29 s Dir.L) ∨ r.nextState = 101 := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (24, Sym.mk k m) →
        (k = SymKind.data1 ∧ m = false ∧ r = SymTransResult.mk 29 (Sym.mk k m) Dir.L) ∨ r.nextState = 101 := by
    native_decide
  rcases s with ⟨k, m⟩
  exact hdec k m r hr

/-- 状态 29：读 data → 29 L；读 sel/nosel → 26 L；否则 101。 -/
lemma trans29_step (s : Sym) (r : SymTransResult) (hr : r ∈ VerifierSym.transition (29, s)) :
    ((s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ r = SymTransResult.mk 29 s Dir.L) ∨
    ((s.1 = SymKind.sel ∨ s.1 = SymKind.nosel) ∧ r = SymTransResult.mk 26 s Dir.L) ∨
    r.nextState = 101 := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (29, Sym.mk k m) →
        ((k = SymKind.data0 ∨ k = SymKind.data1) ∧ r = SymTransResult.mk 29 (Sym.mk k m) Dir.L) ∨
        ((k = SymKind.sel ∨ k = SymKind.nosel) ∧ r = SymTransResult.mk 26 (Sym.mk k m) Dir.L) ∨
        r.nextState = 101 := by
    native_decide
  rcases s with ⟨k, m⟩
  exact hdec k m r hr

/-- 状态 26：读 (data1,false) → 29 L；读 boundary → 27 L；否则 101。 -/
lemma trans26_step (s : Sym) (r : SymTransResult) (hr : r ∈ VerifierSym.transition (26, s)) :
    (s.1 = SymKind.data1 ∧ s.2 = false ∧ r = SymTransResult.mk 29 s Dir.L) ∨
    (s.1 = SymKind.boundary ∧ r = SymTransResult.mk 27 s Dir.L) ∨
    r.nextState = 101 := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (26, Sym.mk k m) →
        (k = SymKind.data1 ∧ m = false ∧ r = SymTransResult.mk 29 (Sym.mk k m) Dir.L) ∨
        (k = SymKind.boundary ∧ r = SymTransResult.mk 27 (Sym.mk k m) Dir.L) ∨
        r.nextState = 101 := by
    native_decide
  rcases s with ⟨k, m⟩
  exact hdec k m r hr

/-- 状态 27：读 (data1,false) → 38 L；否则 101。 -/
lemma trans27_step (s : Sym) (r : SymTransResult) (hr : r ∈ VerifierSym.transition (27, s)) :
    (s.1 = SymKind.data1 ∧ s.2 = false ∧ r = SymTransResult.mk 38 s Dir.L) ∨ r.nextState = 101 := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (27, Sym.mk k m) →
        (k = SymKind.data1 ∧ m = false ∧ r = SymTransResult.mk 38 (Sym.mk k m) Dir.L) ∨ r.nextState = 101 := by
    native_decide
  rcases s with ⟨k, m⟩
  exact hdec k m r hr

/-- 状态 38：读 data → 38 L；读 boundary → 28 R；否则 101。 -/
lemma trans38_step (s : Sym) (r : SymTransResult) (hr : r ∈ VerifierSym.transition (38, s)) :
    ((s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ r = SymTransResult.mk 38 s Dir.L) ∨
    (s.1 = SymKind.boundary ∧ r = SymTransResult.mk 28 s Dir.R) ∨
    r.nextState = 101 := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (38, Sym.mk k m) →
        ((k = SymKind.data0 ∨ k = SymKind.data1) ∧ r = SymTransResult.mk 38 (Sym.mk k m) Dir.L) ∨
        (k = SymKind.boundary ∧ r = SymTransResult.mk 28 (Sym.mk k m) Dir.R) ∨
        r.nextState = 101 := by
    native_decide
  rcases s with ⟨k, m⟩
  exact hdec k m r hr

/-- 状态 28：读 data → 28 R；读 boundary → 4 R；否则 101。 -/
lemma trans28_step (s : Sym) (r : SymTransResult) (hr : r ∈ VerifierSym.transition (28, s)) :
    ((s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ r = SymTransResult.mk 28 s Dir.R) ∨
    (s.1 = SymKind.boundary ∧ r = SymTransResult.mk 4 s Dir.R) ∨
    r.nextState = 101 := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (28, Sym.mk k m) →
        ((k = SymKind.data0 ∨ k = SymKind.data1) ∧ r = SymTransResult.mk 28 (Sym.mk k m) Dir.R) ∨
        (k = SymKind.boundary ∧ r = SymTransResult.mk 4 (Sym.mk k m) Dir.R) ∨
        r.nextState = 101 := by
    native_decide
  rcases s with ⟨k, m⟩
  exact hdec k m r hr

/-- 状态 101 吸收：读任意符号、恒 101。 -/
lemma trans101_step (s : Sym) (r : SymTransResult) (hr : r ∈ VerifierSym.transition (101, s)) :
    r.nextState = 101 := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r ∈ VerifierSym.transition (101, Sym.mk k m),
      r.nextState = 101 := by
    decide
  rcases s with ⟨k, m⟩
  exact hdec k m r hr

/-- WithSel 的符号都是 sel/nosel/data0/data1（非 boundary、非 α/β）。 -/
lemma encodeElementsSymWithSel_kind (elems : List ℕ) (sel : List Bool) :
    ∀ s ∈ encodeElementsSymWithSel elems sel,
      s.1 = SymKind.sel ∨ s.1 = SymKind.nosel ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
  intro s hs
  induction elems generalizing sel s with
  | nil =>
      cases sel <;> simp [encodeElementsSymWithSel, joinLists] at hs
  | cons v rest ih =>
      cases sel with
      | nil => simp [encodeElementsSymWithSel, joinLists] at hs
      | cons b sel' =>
          rw [encodeElementsSymWithSel] at hs
          simp only [List.zip_cons_cons, List.map_cons, joinLists_cons] at hs
          rw [List.mem_append] at hs
          rcases hs with h | h
          · rw [List.mem_append] at h
            rcases h with hh | hbits
            · rw [List.mem_singleton] at hh
              rw [hh]
              by_cases hb : b <;> simp [hb, Sym.sel, Sym.nosel]
            · have hk := encodeBitsSymNative_kind v s hbits
              rcases hk with hd0 | hd1
              · simp [hd0]
              · simp [hd1]
          · exact ih sel' s h

lemma SymSteps_nil_eq {M : ℕ × Sym → Finset SymTransResult} {cfg₀ cfg₁ : SymConfig} :
    SymSteps M cfg₀ [] cfg₁ → cfg₁ = cfg₀ := by
  intro h
  generalize hπ : [] = π at h
  induction h with
  | nil => rfl
  | cons π₀ step cfg₁' h_ind h_from h_read h_trans ih =>
      exfalso
      have hlen : ([] : List SymStep).length = (π₀ ++ [step]).length := by
        simpa using congrArg List.length hπ
      simp [List.length_append] at hlen
/-- 同路径列表 → 同终点配置。 -/
lemma SymSteps_cfg_eq {M : ℕ × Sym → Finset SymTransResult} {input : List Sym}
    {π : List SymStep} {cfg cfg' : SymConfig}
    (h : SymSteps M (symInitialConfig input) π cfg)
    (h' : SymSteps M (symInitialConfig input) π cfg') : cfg = cfg' := by
  induction h generalizing cfg' with
  | nil => exact (SymSteps_nil_eq h').symm
  | cons π₀ step cfg₀ h_ind h_from h_read h_trans ih =>
      generalize hπ : π₀ ++ [step] = πfull at h'
      cases h' with
      | nil =>
          exfalso
          have hlen : π₀.length + 1 = 0 := by
            simpa [List.length_append] using congrArg List.length hπ
          omega
      | cons π₀' step' cfg₀' h_ind' h_from' h_read' h_trans' =>
          have htail : π₀ = π₀' ∧ step = step' := by
            have hrev := congrArg List.reverse hπ
            rw [List.reverse_append, List.reverse_append] at hrev
            simp at hrev
            exact ⟨hrev.2, hrev.1⟩
          rcases htail with ⟨hπ₀, hstep⟩
          subst hπ₀
          subst hstep
          have hcfg₀ := ih h_ind'
          subst hcfg₀
          rfl
/-- 列表尾唯一性：a ++ [x] = b ++ [y] → a = b ∧ x = y。 -/
lemma append_right_cancel {α : Type} {a b : List α} {x y : α}
    (h : a ++ [x] = b ++ [y]) : a = b ∧ x = y := by
  have hrev := congrArg List.reverse h
  rw [List.reverse_append, List.reverse_append] at hrev
  simp at hrev
  exact ⟨hrev.2, hrev.1⟩
lemma SymSteps_states_in {M : ℕ × Sym → Finset SymTransResult} (P : ℕ → Prop) (cfg₀ : SymConfig)
    (hclose : ∀ ⦃q : ℕ⦄ ⦃s : Sym⦄ ⦃r : SymTransResult⦄, P q → r ∈ M (q, s) → P r.nextState)
    (hP₀ : P cfg₀.state) {π : List SymStep} {cfg : SymConfig} :
    SymSteps M cfg₀ π cfg → P cfg.state := by
  intro h
  induction h with
  | nil => exact hP₀
  | cons π₀ step cfg₁ h_ind h_from h_read h_trans ih =>
      exact hclose ih (by simpa [h_from] using h_trans)
/-- 确定性（在谓词 P 内）机器的路径前缀唯一：同一配置出发的两条路径，短的是长的前缀。 -/
lemma SymSteps_prefix_unique_det {M : ℕ × Sym → Finset SymTransResult} (P : ℕ → Prop)
    (cfg₀ : SymConfig)
    (hdet : ∀ ⦃q : ℕ⦄ ⦃s : Sym⦄ ⦃r r' : SymTransResult⦄, P q → r ∈ M (q, s) → r' ∈ M (q, s) → r = r')
    (hclose : ∀ ⦃q : ℕ⦄ ⦃s : Sym⦄ ⦃r : SymTransResult⦄, P q → r ∈ M (q, s) → P r.nextState)
    (hP₀ : P cfg₀.state) :
    ∀ {π₁ π₂ : List SymStep} {cfg₁ cfg₂ : SymConfig},
      SymSteps M cfg₀ π₁ cfg₁ → SymSteps M cfg₀ π₂ cfg₂ →
      (∃ ρ, π₂ = π₁ ++ ρ ∧ SymSteps M cfg₁ ρ cfg₂) ∨
      (∃ ρ, π₁ = π₂ ++ ρ ∧ SymSteps M cfg₂ ρ cfg₁) := by
  have hmain : ∀ (n : ℕ) (cfg₀ : SymConfig) (π₁ π₂ : List SymStep), π₁.length + π₂.length = n →
      P cfg₀.state →
      ∀ (cfg₁ cfg₂ : SymConfig), SymSteps M cfg₀ π₁ cfg₁ → SymSteps M cfg₀ π₂ cfg₂ →
      (∃ ρ, π₂ = π₁ ++ ρ ∧ SymSteps M cfg₁ ρ cfg₂) ∨
      (∃ ρ, π₁ = π₂ ++ ρ ∧ SymSteps M cfg₂ ρ cfg₁) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro cfg₀ π₁ π₂ hlen hPcfg cfg₁ cfg₂ h₁ h₂
        cases h₁ with
        | nil =>
            left
            refine ⟨π₂, by rfl, ?_⟩
            simpa using h₂
        | cons π₁' step₁ cfg₁' h₁' hfrom₁ hread₁ htrans₁ =>
            cases h₂ with
            | nil =>
                right
                refine ⟨π₁' ++ [step₁], by rfl, ?_⟩
                exact SymSteps.cons π₁' step₁ cfg₁' h₁' hfrom₁ hread₁ htrans₁
            | cons π₂' step₂ cfg₂' h₂' hfrom₂ hread₂ htrans₂ =>
                have hlen' : π₁'.length + π₂'.length < n := by
                  have h₁len : (π₁' ++ [step₁]).length = π₁'.length + 1 := by
                    simp [List.length_append]
                  have h₂len : (π₂' ++ [step₂]).length = π₂'.length + 1 := by
                    simp [List.length_append]
                  rw [h₁len, h₂len] at hlen
                  omega
                rcases ih (π₁'.length + π₂'.length) hlen' cfg₀ π₁' π₂' rfl hPcfg cfg₁' cfg₂' h₁' h₂' with hl | hr
                · -- π₂' = π₁' ++ ρ₀，SymSteps cfg₁' ρ₀ cfg₂'
                  rcases hl with ⟨ρ₀, hρ₀_eq, hρ₀⟩
                  subst π₂'
                  have hP₁' : P cfg₁'.state := SymSteps_states_in P cfg₀ hclose hPcfg h₁'
                  have hP₂' : P cfg₂'.state := SymSteps_states_in P cfg₀ hclose hPcfg h₂'
                  have hstep₁ : SymSteps M cfg₁' [step₁] (symStepConfig cfg₁' step₁.result) :=
                    SymSteps.cons [] step₁ cfg₁' SymSteps.nil hfrom₁ hread₁ htrans₁
                  have hlen'' : 1 + ρ₀.length < n := by
                    have h₁len : (π₁' ++ [step₁]).length = π₁'.length + 1 := by
                      simp [List.length_append]
                    have h₂len : ((π₁' ++ ρ₀) ++ [step₂]).length = π₁'.length + ρ₀.length + 1 := by
                      simp [List.length_append]
                      omega
                    rw [h₁len, h₂len] at hlen
                    omega
                  rcases ih (1 + ρ₀.length) hlen'' cfg₁' [step₁] ρ₀ rfl hP₁' (symStepConfig cfg₁' step₁.result) cfg₂' hstep₁ hρ₀ with hsl | hsr
                  · -- ρ₀ = [step₁] ++ ρ'' ∧ SymSteps cfg₁ ρ'' cfg₂'
                    rcases hsl with ⟨ρ'', hρ₀_eq', hrest⟩
                    left
                    refine ⟨ρ'' ++ [step₂], ?_, ?_⟩
                    · rw [hρ₀_eq']
                      ac_rfl
                    · exact SymSteps.cons ρ'' step₂ cfg₂' hrest hfrom₂ hread₂ htrans₂
                  · -- [step₁] = ρ₀ ++ ρ'' ∧ SymSteps cfg₂' ρ'' cfg₁
                    rcases hsr with ⟨ρ'', hstep_eq, hrest⟩
                    cases ρ₀ with
                    | nil =>
                        have hcfg₂' : cfg₂' = cfg₁' := SymSteps_nil_eq hρ₀
                        have hsteps : step₁ = step₂ := by
                          cases step₁ with
                          | mk f₁ r₁ res₁ =>
                            cases step₂ with
                            | mk f₂ r₂ res₂ =>
                                congr
                                · exact hfrom₁.trans (show cfg₁'.state = f₂ from by simpa [hcfg₂'] using hfrom₂.symm)
                                · exact hread₁.trans (show cfg₁'.tape cfg₁'.headPos = r₂ from by simpa [hcfg₂'] using hread₂.symm)
                                · exact hdet hP₁' htrans₁ (by simpa [hcfg₂'] using htrans₂)
                        left
                        refine ⟨[], ?_, ?_⟩
                        · rw [hsteps]
                          simp
                        · rw [show symStepConfig cfg₂' step₂.result = symStepConfig cfg₁' step₁.result from by
                            rw [hcfg₂', hsteps]]
                          exact SymSteps.nil
                    | cons s₀ ρ₁ =>
                        have hs₀ : s₀ = step₁ := by
                          have hfull : s₀ = step₁ ∧ ρ₁ = [] ∧ ρ'' = [] := by
                            simpa using hstep_eq.symm
                          exact hfull.1
                        have hρ''_nil : ρ₁ = [] ∧ ρ'' = [] := by
                          have hfull : s₀ = step₁ ∧ ρ₁ = [] ∧ ρ'' = [] := by
                            simpa using hstep_eq.symm
                          exact ⟨hfull.2.1, hfull.2.2⟩
                        rcases hρ''_nil with ⟨hρ₁, hρ''⟩
                        subst s₀
                        subst ρ₁
                        subst ρ''
                        have hcfg₂' : cfg₂' = symStepConfig cfg₁' step₁.result := by
                          have hrest' : SymSteps M cfg₂' [] (symStepConfig cfg₁' step₁.result) := hrest
                          exact (SymSteps_nil_eq hrest').symm
                        left
                        refine ⟨[step₂], ?_, ?_⟩
                        · rfl
                        · simpa [hcfg₂'] using (SymSteps.cons [] step₂ cfg₂' SymSteps.nil hfrom₂ hread₂ htrans₂)
                · -- π₁' = π₂' ++ ρ₀，SymSteps cfg₂' ρ₀ cfg₁'
                  rcases hr with ⟨ρ₀, hρ₀_eq, hρ₀⟩
                  subst π₁'
                  have hP₁' : P cfg₁'.state := SymSteps_states_in P cfg₀ hclose hPcfg h₁'
                  have hP₂' : P cfg₂'.state := SymSteps_states_in P cfg₀ hclose hPcfg h₂'
                  have hstep₂ : SymSteps M cfg₂' [step₂] (symStepConfig cfg₂' step₂.result) :=
                    SymSteps.cons [] step₂ cfg₂' SymSteps.nil hfrom₂ hread₂ htrans₂
                  have hlen'' : 1 + ρ₀.length < n := by
                    have h₂len : (π₂' ++ [step₂]).length = π₂'.length + 1 := by
                      simp [List.length_append]
                    have h₁len : ((π₂' ++ ρ₀) ++ [step₁]).length = π₂'.length + ρ₀.length + 1 := by
                      simp [List.length_append]
                      omega
                    rw [h₁len, h₂len] at hlen
                    omega
                  rcases ih (1 + ρ₀.length) hlen'' cfg₂' [step₂] ρ₀ rfl hP₂' (symStepConfig cfg₂' step₂.result) cfg₁' hstep₂ hρ₀ with hsl | hsr
                  · -- ρ₀ = [step₂] ++ ρ'' ∧ SymSteps cfg₂ ρ'' cfg₁'
                    rcases hsl with ⟨ρ'', hρ₀_eq', hrest⟩
                    right
                    refine ⟨ρ'' ++ [step₁], ?_, ?_⟩
                    · rw [hρ₀_eq']
                      ac_rfl
                    · exact SymSteps.cons ρ'' step₁ cfg₁' hrest hfrom₁ hread₁ htrans₁
                  · -- [step₂] = ρ₀ ++ ρ'' ∧ SymSteps cfg₁' ρ'' cfg₂
                    rcases hsr with ⟨ρ'', hstep_eq, hrest⟩
                    cases ρ₀ with
                    | nil =>
                        have hcfg₁' : cfg₁' = cfg₂' := SymSteps_nil_eq hρ₀
                        have hsteps : step₂ = step₁ := by
                          cases step₁ with
                          | mk f₁ r₁ res₁ =>
                            cases step₂ with
                            | mk f₂ r₂ res₂ =>
                                congr
                                · exact (show f₂ = cfg₁'.state from by simpa [hcfg₁'] using hfrom₂).trans hfrom₁.symm
                                · exact (show r₂ = cfg₁'.tape cfg₁'.headPos from by simpa [hcfg₁'] using hread₂).trans hread₁.symm
                                · exact hdet hP₂' (by simpa [hcfg₁'] using htrans₂) (by simpa [hcfg₁'] using htrans₁)
                        right
                        refine ⟨[], ?_, ?_⟩
                        · rw [hsteps]
                          simp
                        · rw [show symStepConfig cfg₁' step₁.result = symStepConfig cfg₂' step₂.result from by
                            rw [hcfg₁', hsteps]]
                          exact SymSteps.nil
                    | cons s₀ ρ₁ =>
                        have hs₀ : s₀ = step₂ := by
                          have hfull : s₀ = step₂ ∧ ρ₁ = [] ∧ ρ'' = [] := by
                            simpa using hstep_eq.symm
                          exact hfull.1
                        have hρ''_nil : ρ₁ = [] ∧ ρ'' = [] := by
                          have hfull : s₀ = step₂ ∧ ρ₁ = [] ∧ ρ'' = [] := by
                            simpa using hstep_eq.symm
                          exact ⟨hfull.2.1, hfull.2.2⟩
                        rcases hρ''_nil with ⟨hρ₁, hρ''⟩
                        subst s₀
                        subst ρ₁
                        subst ρ''
                        have hcfg₁' : cfg₁' = symStepConfig cfg₂' step₂.result := by
                          have hrest' : SymSteps M cfg₁' [] (symStepConfig cfg₂' step₂.result) := hrest
                          exact (SymSteps_nil_eq hrest').symm
                        right
                        refine ⟨[step₁], ?_, ?_⟩
                        · rfl
                        · simpa [hcfg₁'] using (SymSteps.cons [] step₁ cfg₁' SymSteps.nil hfrom₁ hread₁ htrans₁)
  intro π₁ π₂ cfg₁ cfg₂ h₁ h₂
  exact hmain (π₁.length + π₂.length) cfg₀ π₁ π₂ rfl hP₀ cfg₁ cfg₂ h₁ h₂
/-- SymReachablePath 转 SymSteps。 -/
lemma reachablePath_to_steps {M : ℕ × Sym → Finset SymTransResult} {input : List Sym}
    {π : List SymStep} {cfg : SymConfig} :
    SymReachablePath M input π cfg → SymSteps M (symInitialConfig input) π cfg := by
  intro h
  induction h with
  | nil => exact SymSteps.nil
  | cons π₀ step cfg h_ind h_from h_read h_trans ih =>
      exact SymSteps.cons π₀ step cfg ih h_from h_read h_trans
end Mp