/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/


import Mp.SubsetSumVerifierCore

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

set_option maxHeartbeats 4000000

set_option maxErrors 2000

/-!
# 子集和 CBTM 验证器（第二部分：减法/清理/主循环构造）
从 `Mp.SubsetSumVerifierCore` 的转移表与基础引理出发，构造减法循环、
清理与主循环的正确性证明。
-/

namespace Mp

/-- kind ∈ {data0, data1} 则 kind ≠ boundary。 -/
lemma kind_ne_boundary_of_data_or (s : Sym) (hs : s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) :
    s.1 ≠ SymKind.boundary := by
  intro h
  rcases hs with hk | hk <;> rw [hk] at h <;> cases h
lemma trans12_marked (s : Sym) (hs : s.2 = true) (hk : s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) :
    { nextState := 12, writeSym := s, moveDir := Dir.R } ∈ VerifierSym.transition (12, s) := by
  rcases s with ⟨k, m⟩
  have hm : m = true := by simpa using hs
  have hk' : k = SymKind.data0 ∨ k = SymKind.data1 := by simpa using hk
  subst m
  cases hk' <;> subst k <;> decide

/-- 状态 12 右移 n 格 m=1 的 data 符号（写回自身），保持 12。 -/
lemma scanRight12 (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hk : ∀ i : ℤ, p ≤ i ∧ i < p + (n : ℤ) →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hcons : ∀ i : ℤ, p ≤ i ∧ i < p + (n : ℤ) → (tape i).2 = true) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 12 tape p) π cfg' ∧
      cfg'.state = 12 ∧ cfg'.headPos = p + (n : ℤ) ∧ cfg'.tape = tape := by
  exact scanRightKeep 12 n p tape (by
    intro i hi
    exact trans12_marked (tape i) (hcons i hi) (hk i hi))

/-- 通用左移引理（谓词 P 版本）：状态 q 左移 n 格（读符号满足 P，写回自身），
    读 boundary 转 q'（写 w，方向 d）。 -/
lemma scanLeftKeepP (q q' : ℕ) (w : Sym) (d : Dir) (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (P : Sym → Prop)
    (hnb : ∀ i : ℤ, p - (n : ℤ) < i ∧ i ≤ p → P (tape i))
    (hbound : tape (p - (n : ℤ)) = Sym.boundary)
    (hkeep : ∀ s : Sym, P s → { nextState := q, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (q, s))
    (hend : { nextState := q', writeSym := w, moveDir := d } ∈ VerifierSym.transition (q, Sym.boundary))
    (hw : w = Sym.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk q tape p) π cfg' ∧
      cfg'.state = q' ∧ cfg'.headPos = p - (n : ℤ) + d.toInt ∧ cfg'.tape = tape := by
  induction n generalizing p tape with
  | zero =>
      let r : SymTransResult := { nextState := q', writeSym := w, moveDir := d }
      let step : SymStep := { fromState := q, readSym := Sym.boundary, result := r }
      have hbound' : tape p = Sym.boundary := by simpa using hbound
      refine ⟨[step], symStepConfig (SymConfig.mk q tape p) step.result, ?_, rfl, ?_, ?_⟩
      · refine SymSteps.cons [] step (SymConfig.mk q tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · change Sym.boundary = tape p
          rw [hbound']
        · change step.result ∈ VerifierSym.transition (q, tape p)
          rw [hbound']
          exact hend
      · simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
      · simp [symStepConfig, SymConfig.mk, step, r]
        funext i
        by_cases h : i = p <;> simp [h, hw, hbound']
  | succ n ih =>
      let r : SymTransResult := { nextState := q, writeSym := tape p, moveDir := Dir.L }
      let step : SymStep := { fromState := q, readSym := tape p, result := r }
      have htrans : step.result ∈ VerifierSym.transition (q, tape p) := by
        exact hkeep (tape p) (hnb p (by constructor <;> omega))
      have hstep : SymSteps VerifierSym.transition (SymConfig.mk q tape p) [step]
          (symStepConfig (SymConfig.mk q tape p) step.result) := by
        refine SymSteps.cons [] step (SymConfig.mk q tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans
      have hcfg : symStepConfig (SymConfig.mk q tape p) step.result = SymConfig.mk q tape (p - 1) := by
        simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
        constructor
        · funext i
          by_cases h : i = p <;> simp [h]
        · omega
      have hnb₁ : ∀ i : ℤ, p - 1 - (n : ℤ) < i ∧ i ≤ p - 1 → P (tape i) := by
        intro i h
        exact hnb i (by constructor <;> omega)
      have hbound₁ : tape (p - 1 - (n : ℤ)) = Sym.boundary := by
        have h' : p - 1 - (n : ℤ) = p - ((n + 1 : ℕ) : ℤ) := by omega
        rw [h']
        exact hbound
      rcases ih (p - 1) tape hnb₁ hbound₁ with ⟨π', cfg', hπ', hs', hhead', htape'⟩
      refine ⟨[step] ++ π', cfg', ?_, hs', ?_, htape'⟩
      · exact SymSteps_trans VerifierSym.transition (SymConfig.mk q tape p) (SymConfig.mk q tape (p - 1)) cfg'
          [step] π' (hcfg ▸ hstep) hπ'
      · rw [hhead']
        omega

/-- targetTape 产生符号都是 data 类（data0/data1）。 -/
lemma markFirst_data (l : List Bool) : ∀ s ∈ markFirst l, s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
  intro s hs
  cases l with
  | nil => simp [markFirst] at hs
  | cons b rest =>
      simp [markFirst] at hs
      rcases hs with rfl | hs
      · by_cases hb : b <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]
      · rcases List.mem_map.mp hs with ⟨x, hx, rfl⟩
        by_cases hx' : x <;> simp [hx', Sym.data1, Sym.data0, Sym.mk]

/-- 状态 81 读 data/boundary：写回自身右移。 -/
lemma trans81_keep (s : Sym) (hs : s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary) :
    { nextState := 81, writeSym := s, moveDir := Dir.R } ∈ VerifierSym.transition (81, s) := by
  rcases s with ⟨k, m⟩
  rcases hs with hk | hk | hk
  · have hk' : k = SymKind.data0 := by simpa using hk
    subst hk'
    cases m <;> decide
  · have hk' : k = SymKind.data1 := by simpa using hk
    subst hk'
    cases m <;> decide
  · have hk' : k = SymKind.boundary := by simpa using hk
    subst hk'
    cases m <;> decide

/-- 状态 81 右移 n 格（data/boundary，写回自身）到第一个 consumed，转状态 13。 -/
lemma scanRight81 (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hnc : ∀ i : ℤ, p ≤ i ∧ i < p + (n : ℤ) → (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1 ∨ (tape i).1 = SymKind.boundary)
    (hcons : tape (p + (n : ℤ)) = Sym.consumed) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 81 tape p) π cfg' ∧
      cfg'.state = 13 ∧ cfg'.headPos = p + (n : ℤ) + 1 ∧ cfg'.tape = tape := by
  induction n generalizing p tape with
  | zero =>
      let r : SymTransResult := { nextState := 13, writeSym := Sym.consumed, moveDir := Dir.R }
      let step : SymStep := { fromState := 81, readSym := Sym.consumed, result := r }
      have hcons' : tape p = Sym.consumed := by simpa using hcons
      refine ⟨[step], symStepConfig (SymConfig.mk 81 tape p) step.result, ?_, rfl, ?_, ?_⟩
      · refine SymSteps.cons [] step (SymConfig.mk 81 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · change Sym.consumed = tape p
          rw [hcons']
        · change step.result ∈ VerifierSym.transition (81, tape p)
          rw [hcons']
          decide
      · simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
      · simp [symStepConfig, SymConfig.mk, step, r]
        funext i
        by_cases h : i = p <;> simp [h, hcons']
  | succ n ih =>
      let r : SymTransResult := { nextState := 81, writeSym := tape p, moveDir := Dir.R }
      let step : SymStep := { fromState := 81, readSym := tape p, result := r }
      have htrans : step.result ∈ VerifierSym.transition (81, tape p) := by
        exact trans81_keep (tape p) (hnc p (by constructor <;> omega))
      have hstep : SymSteps VerifierSym.transition (SymConfig.mk 81 tape p) [step]
          (symStepConfig (SymConfig.mk 81 tape p) step.result) := by
        refine SymSteps.cons [] step (SymConfig.mk 81 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans
      have hcfg₁ : symStepConfig (SymConfig.mk 81 tape p) step.result = SymConfig.mk 81 tape (p + 1) := by
        simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
        funext i
        by_cases h : i = p <;> simp [h]
      have hnc₁ : ∀ i : ℤ, p + 1 ≤ i ∧ i < p + 1 + (n : ℤ) → (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1 ∨ (tape i).1 = SymKind.boundary := by
        intro i h
        exact hnc i (by constructor <;> omega)
      have hcons₁ : tape (p + 1 + (n : ℤ)) = Sym.consumed := by
        have h' : p + 1 + (n : ℤ) = p + ((n + 1 : ℕ) : ℤ) := by omega
        rw [h']
        exact hcons
      rcases ih (p + 1) tape hnc₁ hcons₁ with ⟨π', cfg', hπ', hs', hhead', htape'⟩
      refine ⟨[step] ++ π', cfg', ?_, hs', ?_, htape'⟩
      · exact SymSteps_trans VerifierSym.transition (SymConfig.mk 81 tape p) (SymConfig.mk 81 tape (p + 1)) cfg'
          [step] π' (hcfg₁ ▸ hstep) hπ'
      · rw [hhead']
        omega

/-- 状态 13 右移 n 格 consumed 到 v_{j+1}：读 data0/data1 → 5 S；读 #₁ → 84 L。
    （sel/nosel 标记在减法执行前已被清除为 data0，故 13 不会读标记。）
    输出带读符号标签，供调用方判定 j+1 与 k 的关系。 -/
lemma scanRight13 (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hcons : ∀ i : ℤ, p ≤ i ∧ i < p + (n : ℤ) → tape i = Sym.consumed)
    (hv : tape (p + (n : ℤ)) = Sym.data0 ∨ tape (p + (n : ℤ)) = Sym.data1 ∨
      tape (p + (n : ℤ)) = Sym.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 13 tape p) π cfg' ∧
      (cfg'.state = 5 ∧ cfg'.headPos = p + (n : ℤ) ∧
          (tape (p + (n : ℤ)) = Sym.data0 ∨ tape (p + (n : ℤ)) = Sym.data1)
       ∨ cfg'.state = 84 ∧ cfg'.headPos = p + (n : ℤ) - 1 ∧
          tape (p + (n : ℤ)) = Sym.boundary) ∧
      cfg'.tape = tape := by
  induction n generalizing p tape with
  | zero =>
      rcases hv with h | h | hb
      · let r : SymTransResult := { nextState := 5, writeSym := Sym.data0, moveDir := Dir.S }
        let step : SymStep := { fromState := 13, readSym := Sym.data0, result := r }
        have ht : tape p = Sym.data0 := by simpa using h
        refine ⟨[step], symStepConfig (SymConfig.mk 13 tape p) step.result, ?_, ?_, ?_⟩
        · refine SymSteps.cons [] step (SymConfig.mk 13 tape p) SymSteps.nil ?_ ?_ ?_
          · rfl
          · change Sym.data0 = tape p
            rw [ht]
          · change step.result ∈ VerifierSym.transition (13, tape p)
            rw [ht]
            decide
        · left
          refine ⟨rfl, ?_, ?_⟩
          · simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
          · left
            simpa using ht
        · simp [symStepConfig, SymConfig.mk, step, r]
          funext i
          by_cases h' : i = p <;> simp [h', ht]
      · let r : SymTransResult := { nextState := 5, writeSym := Sym.data1, moveDir := Dir.S }
        let step : SymStep := { fromState := 13, readSym := Sym.data1, result := r }
        have ht : tape p = Sym.data1 := by simpa using h
        refine ⟨[step], symStepConfig (SymConfig.mk 13 tape p) step.result, ?_, ?_, ?_⟩
        · refine SymSteps.cons [] step (SymConfig.mk 13 tape p) SymSteps.nil ?_ ?_ ?_
          · rfl
          · change Sym.data1 = tape p
            rw [ht]
          · change step.result ∈ VerifierSym.transition (13, tape p)
            rw [ht]
            decide
        · left
          refine ⟨rfl, ?_, ?_⟩
          · simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
          · right
            simpa using ht
        · simp [symStepConfig, SymConfig.mk, step, r]
          funext i
          by_cases h' : i = p <;> simp [h', ht]
      · let r : SymTransResult := { nextState := 84, writeSym := Sym.boundary, moveDir := Dir.L }
        let step : SymStep := { fromState := 13, readSym := Sym.boundary, result := r }
        have ht : tape p = Sym.boundary := by simpa using hb
        refine ⟨[step], symStepConfig (SymConfig.mk 13 tape p) step.result, ?_, ?_, ?_⟩
        · refine SymSteps.cons [] step (SymConfig.mk 13 tape p) SymSteps.nil ?_ ?_ ?_
          · rfl
          · change Sym.boundary = tape p
            rw [ht]
          · change step.result ∈ VerifierSym.transition (13, tape p)
            rw [ht]
            decide
        · right
          refine ⟨rfl, ?_, ?_⟩
          · simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
            omega
          · simpa using ht
        · simp [symStepConfig, SymConfig.mk, step, r]
          funext i
          by_cases h' : i = p <;> simp [h', ht]
  | succ n ih =>
      let r : SymTransResult := { nextState := 13, writeSym := Sym.consumed, moveDir := Dir.R }
      let step : SymStep := { fromState := 13, readSym := tape p, result := r }
      have htrans : step.result ∈ VerifierSym.transition (13, tape p) := by
        have hs : (tape p).1 = SymKind.consumed := by
          have h := hcons p (by constructor <;> omega)
          simp [h, Sym.consumed, Sym.mk]
        exact trans13_cons (tape p) hs
      have hstep : SymSteps VerifierSym.transition (SymConfig.mk 13 tape p) [step]
          (symStepConfig (SymConfig.mk 13 tape p) step.result) := by
        refine SymSteps.cons [] step (SymConfig.mk 13 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans
      have hcfg₁ : symStepConfig (SymConfig.mk 13 tape p) step.result = SymConfig.mk 13 tape (p + 1) := by
        simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
        funext i
        by_cases h : i = p
        · subst i
          simpa using (hcons p (by constructor <;> omega)).symm
        · simp [h]
      have hcons₁ : ∀ i : ℤ, p + 1 ≤ i ∧ i < p + 1 + (n : ℤ) → tape i = Sym.consumed := by
        intro i h
        exact hcons i (by constructor <;> omega)
      have hv₁ : tape (p + 1 + (n : ℤ)) = Sym.data0 ∨ tape (p + 1 + (n : ℤ)) = Sym.data1 ∨
          tape (p + 1 + (n : ℤ)) = Sym.boundary := by
        have h' : p + 1 + (n : ℤ) = p + ((n + 1 : ℕ) : ℤ) := by omega
        rw [h']
        exact hv
      rcases ih (p + 1) tape hcons₁ hv₁ with ⟨π', cfg', hπ', hs', htape'⟩
      refine ⟨[step] ++ π', cfg', ?_, ?_, htape'⟩
      · exact SymSteps_trans VerifierSym.transition (SymConfig.mk 13 tape p) (SymConfig.mk 13 tape (p + 1)) cfg'
          [step] π' (hcfg₁ ▸ hstep) hπ'
      · rcases hs' with hs5 | hs84
        · left
          refine ⟨hs5.1, ?_, ?_⟩
          · rw [hs5.2.1]
            omega
          · have h' : p + 1 + (n : ℤ) = p + ((n + 1 : ℕ) : ℤ) := by omega
            simpa [h'] using hs5.2.2
        · right
          refine ⟨hs84.1, ?_, ?_⟩
          · rw [hs84.2.1]
            omega
          · have h' : p + 1 + (n : ℤ) = p + ((n + 1 : ℕ) : ℤ) := by omega
            simpa [h'] using hs84.2.2

/-- 状态 14 借位传播（带头 p 起、借位进行中）：扫 d0→d1 右移（m 保留），
    遇 d1→d0 转 81（终止，m 保留）。 -/
lemma borrow_matches_subOne (bits : List Sym) (b' : List Bool) (p : ℤ)
    (tape : ℤ → Sym) (hsub : subOne (symToBits bits) = some b')
    (hdata : ∀ s ∈ bits, s.1 = SymKind.data0 ∨ s.1 = SymKind.data1)
    (hmarks : ∀ s ∈ bits, s.2 = false)
    (htape : tapeAgrees tape p bits) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 14 tape p) π cfg' ∧
      cfg'.state = 81 ∧
      cfg'.headPos = p + (firstTrueIdx (symToBits bits) : ℤ) + 1 ∧
      tapeAgrees cfg'.tape p (bitsToSym b') ∧
      (∀ i : ℤ, i < p → cfg'.tape i = tape i) ∧
      (∀ i : ℤ, p + (bits.length : ℤ) ≤ i → cfg'.tape i = tape i) := by
  induction bits generalizing b' p tape with
  | nil => simp [symToBits, subOne] at hsub
  | cons s rest ih =>
      rcases s with ⟨k, m⟩
      have hk : k = SymKind.data0 ∨ k = SymKind.data1 := hdata (k, m) (by simp)
      have hm : m = false := hmarks (k, m) (by simp)
      subst m
      have htp : tape p = (k, false) :=
        ((tapeAgrees_cons tape p (k, false) rest).mp htape).1
      have hrest_tape : tapeAgrees tape (p + 1) rest :=
        ((tapeAgrees_cons tape p (k, false) rest).mp htape).2
      cases hk with
      | inl hk =>
          subst k
          simp [symToBits, subOne] at hsub
          rcases hsub with ⟨b'', hsub'', hb'⟩
          subst b'
          -- 14 读 d0,m=0 → 写 d1,m=0 → R 14（借位传播，m 保留）
          let tape₁ : ℤ → Sym := fun i => if i = p then Sym.data1 false else tape i
          let r : SymTransResult := { nextState := 14, writeSym := Sym.data1 false, moveDir := Dir.R }
          let step : SymStep := { fromState := 14, readSym := Sym.mk SymKind.data0 false, result := r }
          have htrans : step.result ∈ VerifierSym.transition (14, (SymKind.data0, false)) := by
            decide
          have hstep : SymSteps VerifierSym.transition (SymConfig.mk 14 tape p) [step]
              (symStepConfig (SymConfig.mk 14 tape p) step.result) := by
            refine SymSteps.cons [] step (SymConfig.mk 14 tape p) SymSteps.nil ?_ ?_ ?_
            · rfl
            · change step.readSym = tape p
              rw [htp]
              rfl
            · change step.result ∈ VerifierSym.transition (14, tape p)
              rw [htp]
              exact htrans
          have hcfg : symStepConfig (SymConfig.mk 14 tape p) step.result = SymConfig.mk 14 tape₁ (p + 1) := by
            simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt, tape₁]
          have htape₁ : tapeAgrees tape₁ (p + 1) rest := by
            intro i hi
            have hrest := hrest_tape i hi
            by_cases heq : (p + 1) + (i : ℤ) = p
            · have hnonneg : (0 : ℤ) ≤ (i : ℤ) := by exact_mod_cast Nat.zero_le i
              omega
            · simpa [tape₁, heq] using hrest
          rcases ih b'' (p + 1) tape₁ hsub''
            (by intro s hs; exact hdata s (by simp [hs]))
            (by intro s hs; exact hmarks s (by simp [hs])) htape₁
            with ⟨π', cfg', hπ', hs', hhead', htape', hleft', hright'⟩
          refine ⟨[step] ++ π', cfg', ?_, hs', ?_, ?_, ?_, ?_⟩
          · exact SymSteps_trans VerifierSym.transition (SymConfig.mk 14 tape p)
              (SymConfig.mk 14 tape₁ (p + 1)) cfg' [step] π' (hcfg ▸ hstep) hπ'
          · rw [hhead']
            simp [symToBits, firstTrueIdx]
            omega
          · intro i hi
            cases i with
            | zero =>
                have hp : cfg'.tape p = tape₁ p := by
                  exact hleft' p (by omega)
                simpa [tape₁, bitsToSym, hp] using (hleft' p (by omega)).symm
            | succ i =>
                have hi' : i < (bitsToSym b'').length := by
                  simpa [bitsToSym] using hi
                have h' := htape' i hi'
                simpa [bitsToSym, add_assoc, add_comm, add_left_comm] using h'
          · intro i hlt
            have hi₁ : i < p + 1 := by omega
            have h' := hleft' i hi₁
            have htape₁_i : tape₁ i = tape i := by
              simp [tape₁]
              intro h
              omega
            rw [h', htape₁_i]
          · intro i hle
            have hi₁ : p + 1 + (rest.length : ℤ) ≤ i := by
              have hlen : (((SymKind.data0, false) :: rest).length : ℤ) = (rest.length : ℤ) + 1 := by simp
              omega
            have h' := hright' i hi₁
            have htape₁_i : tape₁ i = tape i := by
              simp [tape₁]
              intro h
              omega
            rw [h', htape₁_i]
      | inr hk =>
          subst k
          simp [symToBits, subOne] at hsub
          subst b'
          -- 14 读 d1,m=0 → 写 d0,m=0 → R 81（终止，m 保留）
          let tape₁ : ℤ → Sym := fun i => if i = p then Sym.data0 false else tape i
          let r : SymTransResult := { nextState := 81, writeSym := Sym.data0 false, moveDir := Dir.R }
          let step : SymStep := { fromState := 14, readSym := Sym.mk SymKind.data1 false, result := r }
          have htrans : step.result ∈ VerifierSym.transition (14, (SymKind.data1, false)) := by
            decide
          have hstep : SymSteps VerifierSym.transition (SymConfig.mk 14 tape p) [step]
              (symStepConfig (SymConfig.mk 14 tape p) step.result) := by
            refine SymSteps.cons [] step (SymConfig.mk 14 tape p) SymSteps.nil ?_ ?_ ?_
            · rfl
            · change step.readSym = tape p
              rw [htp]
              rfl
            · change step.result ∈ VerifierSym.transition (14, tape p)
              rw [htp]
              exact htrans
          have hcfg : symStepConfig (SymConfig.mk 14 tape p) step.result = SymConfig.mk 81 tape₁ (p + 1) := by
            simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt, tape₁]
          refine ⟨[step], SymConfig.mk 81 tape₁ (p + 1), ?_, rfl, ?_, ?_, ?_, ?_⟩
          · exact SymSteps_trans VerifierSym.transition (SymConfig.mk 14 tape p)
              (SymConfig.mk 81 tape₁ (p + 1)) (SymConfig.mk 81 tape₁ (p + 1)) [step] []
              (hcfg ▸ hstep) SymSteps.nil
          · simp [symToBits, firstTrueIdx]
          · change tapeAgrees (SymConfig.mk 81 tape₁ (p + 1)).tape p (bitsToSym (false :: symToBits rest))
            rw [show bitsToSym (false :: symToBits rest) = (Sym.data0 false) :: rest from by
              rw [show bitsToSym (false :: symToBits rest) = (Sym.data0 false) :: bitsToSym (symToBits rest) from rfl]
              rw [show bitsToSym (symToBits rest) = rest from
                bitsToSym_symToBits_of_data rest
                  (by intro s hs; exact hdata s (by simp [hs]))
                  (by intro s hs; exact hmarks s (by simp [hs]))]]
            intro i hi
            cases i with
            | zero => simp [tape₁]
            | succ i =>
                have hi_rest : i < rest.length := by
                  simpa [List.length_cons] using hi
                have h' := hrest_tape i hi_rest
                simp only [List.getElem_cons_succ]
                dsimp [tape₁]
                rw [if_neg (by omega : p + ((i : ℤ) + 1) ≠ p)]
                simpa [add_assoc, add_comm, add_left_comm] using h'
          · intro i hlt
            simp [tape₁]
            intro h
            omega
          · intro i hle
            have hne : i ≠ p := by
              have hlen : (1 : ℤ) ≤ (((SymKind.data1, false) :: rest).length : ℤ) := by simp
              omega
            simp [tape₁, hne]

/-- 状态 11 读 (data0/data1, false)：置 4F4.4=true 转状态 12。 -/
lemma subtract_one_matches_subOne (bits : List Sym) (b' : List Bool) (p : ℤ)
    (tape : ℤ → Sym) (hsub : subOne (symToBits bits) = some b')
    (hdata : ∀ s ∈ bits, s.1 = SymKind.data0 ∨ s.1 = SymKind.data1)
    (hmarks : ∀ s ∈ bits, s.2 = false)
    (htape : tapeAgrees tape p bits) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 10 tape p) π cfg' ∧
      cfg'.state = 81 ∧
      cfg'.headPos = p + (firstTrueIdx (symToBits bits) : ℤ) + 1 ∧
      tapeAgrees cfg'.tape p (markFirst b') ∧
      (∀ i : ℤ, i < p → cfg'.tape i = tape i) ∧
      (∀ i : ℤ, p + (bits.length : ℤ) ≤ i → cfg'.tape i = tape i) := by
  induction bits generalizing b' p tape with
  | nil => simp [symToBits, subOne] at hsub
  | cons s rest ih =>
      rcases s with ⟨k, m⟩
      have hk : k = SymKind.data0 ∨ k = SymKind.data1 := hdata (k, m) (by simp)
      have hm : m = false := hmarks (k, m) (by simp)
      subst m
      have htp : tape p = (k, false) :=
        ((tapeAgrees_cons tape p (k, false) rest).mp htape).1
      have hrest_tape : tapeAgrees tape (p + 1) rest :=
        ((tapeAgrees_cons tape p (k, false) rest).mp htape).2
      cases hk with
      | inl hk =>
          subst k
          simp [symToBits, subOne] at hsub
          rcases hsub with ⟨b'', hsub'', hb'⟩
          subst b'
          -- 10 读 d0 → 写 d0,m=1 → S 11；11 读 (d0,true) → d1,m=1 → R 14（借位）
          let tapeA : ℤ → Sym := fun i => if i = p then Mp.Sym.data0 true else tape i
          let tape₁ : ℤ → Sym := fun i => if i = p then Mp.Sym.data1 true else tape i
          let rA : SymTransResult := { nextState := 11, writeSym := Sym.data0 true, moveDir := Dir.S }
          let stepA : SymStep := { fromState := 10, readSym := Sym.mk SymKind.data0 false, result := rA }
          let rB : SymTransResult := { nextState := 14, writeSym := Sym.data1 true, moveDir := Dir.R }
          let stepB : SymStep := { fromState := 11, readSym := Sym.data0 true, result := rB }
          have htransA : stepA.result ∈ VerifierSym.transition (10, (SymKind.data0, false)) := by
            decide
          have htransB : stepB.result ∈ VerifierSym.transition (11, Sym.data0 true) := by
            decide
          have hstepA : SymSteps VerifierSym.transition (SymConfig.mk 10 tape p) [stepA]
              (symStepConfig (SymConfig.mk 10 tape p) stepA.result) := by
            refine SymSteps.cons [] stepA (SymConfig.mk 10 tape p) SymSteps.nil ?_ ?_ ?_
            · rfl
            · change stepA.readSym = tape p
              rw [htp]
              rfl
            · change stepA.result ∈ VerifierSym.transition (10, tape p)
              rw [htp]
              exact htransA
          have hcfgA : symStepConfig (SymConfig.mk 10 tape p) stepA.result = SymConfig.mk 11 tapeA p := by
            simp [symStepConfig, SymConfig.mk, stepA, rA, Dir.toInt, tapeA]
          have hstepB : SymSteps VerifierSym.transition (SymConfig.mk 11 tapeA p) [stepB]
              (symStepConfig (SymConfig.mk 11 tapeA p) stepB.result) := by
            refine SymSteps.cons [] stepB (SymConfig.mk 11 tapeA p) SymSteps.nil ?_ ?_ ?_
            · rfl
            · simp [stepB, tapeA]
            · simpa [stepB, tapeA] using htransB
          have hcfgB : symStepConfig (SymConfig.mk 11 tapeA p) stepB.result = SymConfig.mk 14 tape₁ (p + 1) := by
            simp [symStepConfig, SymConfig.mk, stepB, rB, Dir.toInt, tapeA, tape₁]
            funext i
            by_cases h : i = p <;> simp [h, tapeA, tape₁]
          have htape₁ : tapeAgrees tape₁ (p + 1) rest := by
            intro i hi
            have hrest := hrest_tape i hi
            by_cases heq : (p + 1) + (i : ℤ) = p
            · have hnonneg : (0 : ℤ) ≤ (i : ℤ) := by exact_mod_cast Nat.zero_le i
              omega
            · simpa [tape₁, heq] using hrest
          rcases borrow_matches_subOne rest b'' (p + 1) tape₁ hsub''
            (by intro s hs; exact hdata s (by simp [hs]))
            (by intro s hs; exact hmarks s (by simp [hs])) htape₁
            with ⟨π', cfg', hπ', hs', hhead', htape', hleft', hright'⟩
          refine ⟨[stepA, stepB] ++ π', cfg', ?_, hs', ?_, ?_, ?_, ?_⟩
          · have hAB : SymSteps VerifierSym.transition (SymConfig.mk 10 tape p)
                ([stepA] ++ [stepB]) (SymConfig.mk 14 tape₁ (p + 1)) := by
              exact SymSteps_trans VerifierSym.transition (SymConfig.mk 10 tape p)
                (SymConfig.mk 11 tapeA p) (SymConfig.mk 14 tape₁ (p + 1)) [stepA] [stepB]
                (hcfgA ▸ hstepA) (hcfgB ▸ hstepB)
            exact SymSteps_trans VerifierSym.transition (SymConfig.mk 10 tape p)
              (SymConfig.mk 14 tape₁ (p + 1)) cfg' ([stepA] ++ [stepB]) π' hAB hπ'
          · rw [hhead']
            simp [symToBits, firstTrueIdx]
            omega
          · intro i hi
            cases i with
            | zero =>
                have hp : cfg'.tape p = tape₁ p := by
                  exact hleft' p (by omega)
                simpa [tape₁, markFirst, bitsToSym, hp] using (hleft' p (by omega)).symm
            | succ i =>
                have hi' : i < (bitsToSym b'').length := by
                  simp [markFirst, bitsToSym] at hi ⊢
                  omega
                have h' := htape' i hi'
                simp [markFirst, bitsToSym] at h' ⊢
                convert h' using 2
                ring
          · intro i hlt
            have hi₁ : i < p + 1 := by omega
            have h' := hleft' i hi₁
            have htape₁_i : tape₁ i = tape i := by
              simp [tape₁]
              intro h
              omega
            rw [h', htape₁_i]
          · intro i hle
            have hi₁ : p + 1 + (rest.length : ℤ) ≤ i := by
              have hlen : (((SymKind.data0, false) :: rest).length : ℤ) = (rest.length : ℤ) + 1 := by simp
              omega
            have h' := hright' i hi₁
            have htape₁_i : tape₁ i = tape i := by
              simp [tape₁]
              intro h
              omega
            rw [h', htape₁_i]
      | inr hk =>
          subst k
          simp [symToBits, subOne] at hsub
          subst b'
          -- 10 读 d1 → 写 d1,m=1 → S 11；11 读 (d1,true) → d0,m=1 → R 81（1-1=0 完成）
          let tapeA : ℤ → Sym := fun i => if i = p then Mp.Sym.data1 true else tape i
          let tape₁ : ℤ → Sym := fun i => if i = p then Mp.Sym.data0 true else tape i
          let rA : SymTransResult := { nextState := 11, writeSym := Sym.data1 true, moveDir := Dir.S }
          let stepA : SymStep := { fromState := 10, readSym := Sym.mk SymKind.data1 false, result := rA }
          let rB : SymTransResult := { nextState := 81, writeSym := Sym.data0 true, moveDir := Dir.R }
          let stepB : SymStep := { fromState := 11, readSym := Sym.data1 true, result := rB }
          have htransA : stepA.result ∈ VerifierSym.transition (10, (SymKind.data1, false)) := by
            decide
          have htransB : stepB.result ∈ VerifierSym.transition (11, Sym.data1 true) := by
            decide
          have hstepA : SymSteps VerifierSym.transition (SymConfig.mk 10 tape p) [stepA]
              (symStepConfig (SymConfig.mk 10 tape p) stepA.result) := by
            refine SymSteps.cons [] stepA (SymConfig.mk 10 tape p) SymSteps.nil ?_ ?_ ?_
            · rfl
            · change stepA.readSym = tape p
              rw [htp]
              rfl
            · change stepA.result ∈ VerifierSym.transition (10, tape p)
              rw [htp]
              exact htransA
          have hcfgA : symStepConfig (SymConfig.mk 10 tape p) stepA.result = SymConfig.mk 11 tapeA p := by
            simp [symStepConfig, SymConfig.mk, stepA, rA, Dir.toInt, tapeA]
          have hstepB : SymSteps VerifierSym.transition (SymConfig.mk 11 tapeA p) [stepB]
              (symStepConfig (SymConfig.mk 11 tapeA p) stepB.result) := by
            refine SymSteps.cons [] stepB (SymConfig.mk 11 tapeA p) SymSteps.nil ?_ ?_ ?_
            · rfl
            · simp [stepB, tapeA]
            · simpa [stepB, tapeA] using htransB
          have hcfgB : symStepConfig (SymConfig.mk 11 tapeA p) stepB.result = SymConfig.mk 81 tape₁ (p + 1) := by
            simp [symStepConfig, SymConfig.mk, stepB, rB, Dir.toInt, tapeA, tape₁]
            funext i
            by_cases h : i = p <;> simp [h, tapeA, tape₁]
          let cfg' : SymConfig := SymConfig.mk 81 tape₁ (p + 1)
          refine ⟨[stepA, stepB], SymConfig.mk 81 tape₁ (p + 1), ?_, rfl, ?_, ?_, ?_, ?_⟩
          · exact SymSteps_trans VerifierSym.transition (SymConfig.mk 10 tape p)
              (SymConfig.mk 11 tapeA p) (SymConfig.mk 81 tape₁ (p + 1)) [stepA] [stepB]
              (hcfgA ▸ hstepA) (hcfgB ▸ hstepB)
          · simp [symToBits, firstTrueIdx]
          · intro i hi
            cases i with
            | zero => simp [tape₁, markFirst, bitsToSym]
            | succ i =>
                have hi' : i < rest.length := by
                  simp [markFirst, bitsToSym] at hi
                  omega
                have hsym : bitsToSym (symToBits rest) = rest :=
                  bitsToSym_symToBits_of_data rest
                    (by intro s hs; exact hdata s (by simp [hs]))
                    (by intro s hs; exact hmarks s (by simp [hs]))
                have h' : tape (p + 1 + (i : ℤ)) = rest[i] := hrest_tape i hi'
                have hne : p + 1 + (i : ℤ) ≠ p := by omega
                have hp : p + ((i + 1 : ℕ) : ℤ) = p + 1 + (i : ℤ) := by omega
                have hlen_mf : (markFirst (false :: symToBits rest)).length = rest.length + 1 := by
                  simp [markFirst, bitsToSym, symToBits, List.length_map]
                have hi1 : (i : ℕ) + 1 < (markFirst (false :: symToBits rest)).length := by
                  rw [hlen_mf]
                  omega
                have hrhs : (markFirst (false :: symToBits rest))[(i : ℕ) + 1]'hi1 = rest[i]'hi' := by
                  change ((Sym.data0 true) :: bitsToSym (symToBits rest))[(i : ℕ) + 1]'hi1 = rest[i]'hi'
                  rw [List.getElem_cons_succ]
                  simp only [show bitsToSym (symToBits rest) = rest from hsym]
                rw [hp]
                change (SymConfig.mk 81 tape₁ (p + 1)).tape (p + 1 + (i : ℤ)) =
                  (markFirst (false :: symToBits rest))[(i : ℕ) + 1]'hi1
                rw [hrhs]
                simp [tape₁, hne]
                exact h'
          · intro i hlt
            simp [tape₁]
            intro h
            omega
          · intro i hle
            have hne : i ≠ p := by
              have hlen : (1 : ℤ) ≤ (((SymKind.data1, false) :: rest).length : ℤ) := by simp
              omega
            simp [tape₁, hne]

/-- 借位传播（状态 14）：[p, p+n) 全 data0 且 p+n 处 #₀ → 状态 14 右移把 data0 全写 data1，
    到 #₀ 转 101。用于 target 不足（借位越界）的拒绝路径。 -/
lemma underflow_scan_to_boundary (p : ℤ) (n : ℕ) (tape : ℤ → Sym)
    (htape : ∀ i : ℕ, i < n → tape (p + (i : ℤ)) = Sym.data0)
    (hbound : tape (p + (n : ℤ)) = Sym.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 14 tape p) π cfg' ∧
      cfg'.state = 101 ∧
      cfg'.headPos = p + (n : ℤ) + 1 ∧
      (∀ i : ℕ, i < n → cfg'.tape (p + (i : ℤ)) = Sym.data1) ∧
      cfg'.tape (p + (n : ℤ)) = Sym.boundary ∧
      (∀ i : ℤ, i < p → cfg'.tape i = tape i) ∧
      (∀ i : ℤ, p + (n : ℤ) < i → cfg'.tape i = tape i) := by
  induction n generalizing p tape with
  | zero =>
      -- 状态 14 读 p 处 #₀ → 101（写原样，右移）
      have hstep : { nextState := 101, writeSym := Sym.boundary, moveDir := Dir.R } ∈
          VerifierSym.transition (14, Sym.boundary) := by native_decide
      let tape' : ℤ → Sym := fun i => if i = p then Sym.boundary else tape i
      have hπ : SymSteps VerifierSym.transition (SymConfig.mk 14 tape p)
          [SymStep.mk 14 Sym.boundary { nextState := 101, writeSym := Sym.boundary, moveDir := Dir.R }]
          (SymConfig.mk 101 tape' (p + 1)) := by
        exact SymSteps.cons [] (SymStep.mk 14 Sym.boundary { nextState := 101, writeSym := Sym.boundary, moveDir := Dir.R })
          (SymConfig.mk 14 tape p) SymSteps.nil
          (by rfl)
          (by
            have hb : tape p = Sym.boundary := by simpa using hbound
            simp [SymStep.mk]
            rw [hb])
          (by
            have hb : tape p = Sym.boundary := by simpa using hbound
            simp [SymStep.mk]
            rw [hb]
            exact hstep)
      refine ⟨[SymStep.mk 14 Sym.boundary { nextState := 101, writeSym := Sym.boundary, moveDir := Dir.R }], SymConfig.mk 101 tape' (p + 1), hπ, rfl, by simp, ?_, ?_, ?_, ?_⟩
      · intro i hi
        omega
      · simpa [tape'] using hbound
      · intro i h
        simp [tape', show i ≠ p from by omega]
      · intro i h
        simp [tape', show i ≠ p from by omega]
  | succ n ih =>
      -- 状态 14 读 p 处（data0）→ 写 data1 右移（借位传播一格）
      have hk0' : tape p = Sym.data0 := by simpa using htape 0 (Nat.succ_pos n)
      have hstep : { nextState := 14, writeSym := Sym.data1, moveDir := Dir.R } ∈
          VerifierSym.transition (14, tape p) := by
        rw [hk0']
        exact trans14_borrow false
      let tape' : ℤ → Sym := fun i => if i = p then Sym.data1 else tape i
      have hπ1 : SymSteps VerifierSym.transition (SymConfig.mk 14 tape p)
          [SymStep.mk 14 Sym.data0 { nextState := 14, writeSym := Sym.data1, moveDir := Dir.R }]
          (SymConfig.mk 14 tape' (p + 1)) := by
        exact SymSteps.cons [] (SymStep.mk 14 Sym.data0 { nextState := 14, writeSym := Sym.data1, moveDir := Dir.R })
          (SymConfig.mk 14 tape p) SymSteps.nil
          (by rfl) (by simp [SymStep.mk]; exact hk0'.symm) (by simp [SymStep.mk]; exact hstep)
      have htape' : ∀ i : ℕ, i < n → tape' (p + 1 + (i : ℤ)) = Sym.data0 := by
        intro i hi
        have h' := htape (i + 1) (Nat.succ_lt_succ hi)
        have hsimp : tape' (p + 1 + (i : ℤ)) = tape (p + 1 + (i : ℤ)) := by
          simp [tape', show p + 1 + (i : ℤ) ≠ p from by omega]
        rw [hsimp]
        have hcast : p + 1 + (i : ℤ) = p + ((i + 1 : ℕ) : ℤ) := by
          rw [Nat.cast_add]
          simp [add_assoc, add_comm, add_left_comm]
        rw [hcast]
        exact h'
      have hbound' : tape' (p + 1 + (n : ℤ)) = Sym.boundary := by
        have hsimp : tape' (p + 1 + (n : ℤ)) = tape (p + 1 + (n : ℤ)) := by
          simp [tape', show p + 1 + (n : ℤ) ≠ p from by omega]
        rw [hsimp]
        have hcast : p + 1 + (n : ℤ) = p + ((n + 1 : ℕ) : ℤ) := by
          rw [Nat.cast_add]
          simp [add_assoc, add_comm, add_left_comm]
        rw [hcast]
        exact hbound
      rcases ih (p + 1) tape' htape' hbound' with ⟨π', cfg', hπ', hs', hhead', hdata1', hbound'', hleft', hright'⟩
      refine ⟨[SymStep.mk 14 Sym.data0 { nextState := 14, writeSym := Sym.data1, moveDir := Dir.R }] ++ π', cfg', ?_, hs', ?_, ?_, ?_, ?_, ?_⟩
      · exact SymSteps_trans VerifierSym.transition (SymConfig.mk 14 tape p)
          (SymConfig.mk 14 tape' (p + 1)) cfg' [SymStep.mk 14 Sym.data0 { nextState := 14, writeSym := Sym.data1, moveDir := Dir.R }] π' hπ1 hπ'
      · rw [hhead']
        omega
      · intro i hi
        cases i with
        | zero =>
            have hl : cfg'.tape p = tape' p := hleft' p (by omega)
            have hz : cfg'.tape (p + (0 : ℕ) : ℤ) = Sym.data1 := by
              simpa [tape', hl]
            rw [hz]
        | succ i =>
            have h' := hdata1' i (by omega)
            have hsimp : cfg'.tape (p + ((i + 1 : ℕ) : ℤ)) = cfg'.tape (p + 1 + (i : ℤ)) := by
              congr 1
              rw [Nat.cast_add]
              simp [add_assoc, add_comm, add_left_comm]
            rw [hsimp]
            exact h'
      · have hsimp : cfg'.tape (p + ((n + 1 : ℕ) : ℤ)) = cfg'.tape (p + 1 + (n : ℤ)) := by
          congr 1
          rw [Nat.cast_add]
          simp [add_assoc, add_comm, add_left_comm]
        rw [hsimp]
        exact hbound''
      · intro i h
        have h' := hleft' i (by omega)
        simpa [tape', show i ≠ p from by omega] using h'
      · intro i h
        have h' := hright' i (by omega)
        simpa [tape', show i ≠ p from by omega] using h'

/-- targetTape j bits 的符号 kind ∈ {data0, data1}。 -/
lemma targetTape_data (j : ℕ) (bits : List Bool) :
    ∀ s ∈ targetTape j bits, s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
  intro s hs
  rw [targetTape, List.mem_append] at hs
  rcases hs with hm | hd
  · rcases List.mem_map.mp hm with ⟨b, hb, rfl⟩
    by_cases hb' : b <;> simp [hb', Sym.data1, Sym.data0, Sym.mk]
  · rcases List.mem_map.mp hd with ⟨b, hb, rfl⟩
    by_cases hb' : b <;> simp [hb', Sym.data1, Sym.data0, Sym.mk]

lemma process_one_bit (k j : ℕ) (v_j : Bool) (tbits ebits : List Bool)
    (p_t p_e : ℤ) (tape : ℤ → Sym)
    (htlen : tbits.length = k) (helen : ebits.length = k)
    (hj : j < k)
    (hp_t_le : p_t + (k : ℤ) ≤ p_e)
    (hbound : tape (p_e - 1) = Sym.boundary)
    (hpad : ∀ i : ℤ, p_t + (k : ℤ) ≤ i ∧ i < p_e - 1 → tape i = Sym.data0)
    (htarget : tapeAgrees tape p_t (targetTape j tbits))
    (hhashL : tape (p_t - 1) = Sym.boundary)
    (hsel : (tape p_e).1 = SymKind.data0 ∨ (tape p_e).1 = SymKind.data1)
    (helem_pre : ∀ i : ℕ, i < j → tape (p_e + 1 + (i : ℤ)) = Sym.consumed)
    (hvj : tape (p_e + 1 + (j : ℤ)) = if v_j then Sym.data1 else Sym.data0)
    (helem_rest : tapeAgrees tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) (bitsToSym (ebits.drop (j + 1))))
    (hv_succ : tape (p_e + 1 + (k : ℤ)) = Sym.boundary ∨
      tape (p_e + 1 + (k : ℤ)) = Sym.data0)
    (hsub : (if v_j then 2^j else 0) ≤ bitsValue tbits) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) π cfg' ∧
      ((cfg'.state = 84 ∧ cfg'.headPos = p_e + 1 + ((j + 1 : ℕ) : ℤ) - 1 ∧
          cfg'.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = Sym.boundary)
       ∨ (cfg'.state = 5 ∧ cfg'.headPos = p_e + 1 + ((j + 1 : ℕ) : ℤ) ∧
          (cfg'.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = Sym.data0 ∨
           cfg'.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = Sym.data1))) ∧
      tapeAgrees cfg'.tape p_t (targetTape (j + 1)
        (if v_j then (subOneAt j tbits).getD tbits else tbits)) ∧
      (∀ i : ℕ, i ≤ j → cfg'.tape (p_e + 1 + (i : ℤ)) = Sym.consumed) ∧
      tapeAgrees cfg'.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) (bitsToSym (ebits.drop (j + 1))) ∧
      ((cfg'.tape p_e).1 = SymKind.data0 ∨ (cfg'.tape p_e).1 = SymKind.data1) ∧
      cfg'.tape (p_t - 1) = Sym.boundary ∧
      cfg'.tape (p_e - 1) = Sym.boundary ∧
      cfg'.tape (p_e + 1 + (k : ℤ)) = tape (p_e + 1 + (k : ℤ)) ∧
      cfg'.tape p_e = tape p_e ∧
      (∀ i : ℤ, p_t + (k : ℤ) ≤ i ∧ i < p_e - 1 → cfg'.tape i = Sym.data0) ∧
      (∀ i : ℤ, p_e + 1 + (k : ℤ) < i → cfg'.tape i = tape i) := by
  by_cases hvj_bool : v_j
  · -- 减路径（v_j = true）：状态 5→6→7→10→减2^j→12→13→5
    have hvj' : tape (p_e + 1 + (j : ℤ)) = Sym.data1 := by simpa [hvj_bool] using hvj
    have hp_t_lt : p_t + (k : ℤ) < p_e := boundary_after_target k j p_t p_e tape tbits (le_of_eq htlen.symm) hj hp_t_le htarget hbound
    have hne_pe : p_e ≠ p_t + (j : ℤ) := by omega
    have hne_pe1 : p_e - 1 ≠ p_t + (j : ℤ) := by omega
    let r5 : SymTransResult := { nextState := 76, writeSym := Sym.consumed, moveDir := Dir.L }
    let step5 : SymStep := { fromState := 5, readSym := Sym.data1, result := r5 }
    have htrans5 : step5.result ∈ VerifierSym.transition (5, tape (p_e + 1 + (j : ℤ))) := by
      unfold step5 r5
      rw [hvj']
      decide
    let tape1 : ℤ → Sym := fun i => if i = p_e + 1 + (j : ℤ) then Sym.consumed else tape i
    have hstep5 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) [step5]
        (symStepConfig (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) step5.result) := by
      refine SymSteps.cons [] step5 (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) SymSteps.nil ?_ ?_ ?_
      · rfl
      · change Sym.data1 = tape (p_e + 1 + (j : ℤ))
        rw [hvj']
      · change step5.result ∈ VerifierSym.transition (5, tape (p_e + 1 + (j : ℤ)))
        unfold step5 r5
        rw [hvj']
        decide
    have hcfg5 : symStepConfig (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) step5.result =
        SymConfig.mk 76 tape1 (p_e + (j : ℤ)) := by
      simp [symStepConfig, SymConfig.mk, step5, r5, tape1, Dir.toInt]
      omega
    -- 2. 状态 76 左移 j+1 格到 #₀
    have hnb6 : ∀ i : ℤ, p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ) < i ∧ i ≤ p_e + (j : ℤ) →
        (tape1 i).1 = SymKind.consumed ∨ (tape1 i).1 = SymKind.data0 ∨ (tape1 i).1 = SymKind.data1 := by
      intro i h
      have hi : p_e ≤ i ∧ i ≤ p_e + (j : ℤ) := by constructor <;> omega
      by_cases heq : i = p_e
      · subst i
        rw [show tape1 p_e = tape p_e from by simp [tape1]; intro h; omega]
        rcases hsel with hd0 | hd1
        · right; left; exact hd0
        · right; right; exact hd1
      · have ioff : ∃ io : ℕ, (io : ℤ) = i - (p_e + 1) := by
          refine ⟨(i - (p_e + 1)).toNat, ?_⟩
          exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p_e + 1))
        rcases ioff with ⟨io, hio⟩
        have hio_le : io ≤ j := by omega
        by_cases heqio : io = j
        · subst io
          have hidx : i = p_e + 1 + (j : ℤ) := by omega
          rw [hidx]
          simp [tape1, Sym.consumed]
        · have hio_lt : io < j := by omega
          have ht := helem_pre io hio_lt
          have hidx : p_e + 1 + (io : ℤ) = i := by omega
          have ht' : tape i = Sym.consumed := by
            rw [hidx] at ht
            exact ht
          rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
          rw [ht']
          simp [Sym.consumed, Sym.mk]
    have hbound6 : tape1 (p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ)) = Sym.boundary := by
      have hpos : p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ) = p_e - 1 := by omega
      rw [hpos]
      rw [show tape1 (p_e - 1) = tape (p_e - 1) from by simp [tape1]; intro h; omega]
      exact hbound
    have hend6 : { nextState := 77, writeSym := Sym.boundary, moveDir := Dir.L } ∈ VerifierSym.transition (76, Sym.boundary) := by decide
    have hkeep6 : ∀ s : Sym, s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 → { nextState := 76, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (76, s) := trans76_keep
    rcases scanLeftKeepP 76 77 Sym.boundary Dir.L (j + 1) (p_e + (j : ℤ)) tape1
        (fun s : Sym => s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1)
        hnb6 hbound6 hkeep6 hend6 rfl
      with ⟨π6, cfg6, hπ6, hs6, hhead6, htape6⟩
    -- 3. 状态 77 左移 (p_e - p_t - 1) 格到 #ₗ
    let n7 : ℕ := (p_e - p_t - 1).toNat
    have hn7 : (n7 : ℤ) = p_e - p_t - 1 := by
      change ((p_e - p_t - 1).toNat : ℤ) = p_e - p_t - 1
      exact Int.toNat_of_nonneg (by omega : 0 ≤ p_e - p_t - 1)
    have hnb7 : ∀ i : ℤ, (p_e - 2) - (n7 : ℤ) < i ∧ i ≤ p_e - 2 →
        (tape1 i).1 = SymKind.data0 ∨ (tape1 i).1 = SymKind.data1 := by
      intro i h
      rw [hn7] at h
      have hi : p_t ≤ i ∧ i < p_e - 1 := by constructor <;> omega
      by_cases hlt_target : i < p_t + (k : ℤ)
      · -- target 位
        have ioff : ∃ io : ℕ, (io : ℤ) = i - p_t := by
          refine ⟨(i - p_t).toNat, ?_⟩
          exact Int.toNat_of_nonneg (by linarith only [hi.1])
        rcases ioff with ⟨io, hio⟩
        have hio_lt : io < (targetTape j tbits).length := by
          have hlen : (targetTape j tbits).length = tbits.length := by
            simp [targetTape_length]
          rw [hlen]
          omega
        have ht := htarget io hio_lt
        have hnb_io : ((targetTape j tbits)[io]).1 = SymKind.data0 ∨ ((targetTape j tbits)[io]).1 = SymKind.data1 := by
          have hmem : (targetTape j tbits)[io] ∈ targetTape j tbits := List.getElem_mem hio_lt
          exact targetTape_data j tbits ((targetTape j tbits)[io]) hmem
        have hidx : p_t + (io : ℤ) = i := by omega
        rw [hidx] at ht
        rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
        rw [ht]
        exact hnb_io
      · -- data0 填充
        have hpad_i := hpad i (by constructor <;> omega)
        rw [show tape1 i = tape i from by simp [tape1]; intro h'; omega]
        rw [hpad_i]
        left
        rfl
    have hbound7 : tape1 ((p_e - 2) - (n7 : ℤ)) = Sym.boundary := by
      have hpos : (p_e - 2) - (n7 : ℤ) = p_t - 1 := by rw [hn7]; omega
      rw [hpos]
      rw [show tape1 (p_t - 1) = tape (p_t - 1) from by simp [tape1]; intro h; omega]
      exact hhashL
    have hend7 : { nextState := 10, writeSym := Sym.boundary, moveDir := Dir.R } ∈ VerifierSym.transition (77, Sym.boundary) := by decide
    have hkeep7 : ∀ s : Sym, s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 → { nextState := 77, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (77, s) := trans77_keep
    rcases scanLeftKeepP 77 10 Sym.boundary Dir.R n7 (p_e - 2) tape1
        (fun s : Sym => s.1 = SymKind.data0 ∨ s.1 = SymKind.data1)
        hnb7 hbound7 hkeep7 hend7 rfl
      with ⟨π7, cfg7, hπ7, hs7, hhead7, htape7⟩
    -- 4. 状态 10 右移 j 格（4F4.4 前缀）
    have hkeep10 : ∀ i : ℤ, p_t ≤ i ∧ i < p_t + (j : ℤ) → { nextState := 10, writeSym := tape1 i, moveDir := Dir.R } ∈ VerifierSym.transition (10, tape1 i) := by
      intro i h
      have hi : p_t ≤ i ∧ i < p_t + (k : ℤ) := by constructor <;> omega
      have ioff : ∃ io : ℕ, (io : ℤ) = i - p_t := by
        refine ⟨(i - p_t).toNat, ?_⟩
        exact Int.toNat_of_nonneg (by linarith only [hi.1])
      rcases ioff with ⟨io, hio⟩
      have hio_lt : io < (targetTape j tbits).length := by
        have hlen : (targetTape j tbits).length = k := by
          simp [targetTape, bitsToSym, htlen, List.length_drop, Nat.min_eq_left (Nat.le_of_lt hj)]
          omega
        rw [hlen]
        omega
      have ht := htarget io hio_lt
      have hio_j : io < j := by omega
      have hio_tbits : io < tbits.length := by omega
      have hsym : (targetTape j tbits)[io] = (if tbits[io] then Sym.data1 true else Sym.data0 true) := by
        simp [targetTape, bitsToSym, hio_j, hio_tbits]
      have hidx : p_t + (io : ℤ) = i := by omega
      rw [hidx] at ht
      rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
      rw [ht, hsym]
      have hk : ((if tbits[io] then Sym.data1 true else Sym.data0 true).1 = SymKind.data0 ∨
          (if tbits[io] then Sym.data1 true else Sym.data0 true).1 = SymKind.data1) := by
        by_cases hb : tbits[io] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]
      exact trans10_marked (if tbits[io] then Sym.data1 true else Sym.data0 true) (by by_cases hb : tbits[io] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]) hk
    rcases scanRightKeep 10 j p_t tape1 hkeep10 with ⟨π10, cfg10, hπ10, hs10, hhead10, htape10⟩
    -- 5. 减 2^j：状态 10 读 t_j 减一
    have hsub2 : 2 ^ j ≤ bitsValue tbits := by simpa [hvj_bool] using hsub
    rcases subOne_drop_some_of_ge_pow tbits j hsub2 with ⟨b', hsub_drop⟩
    have hsub' : subOne (symToBits (bitsToSym (tbits.drop j))) = some b' := by
      simpa [symToBits_bitsToSym] using hsub_drop
    have htape_drop : tapeAgrees tape1 (p_t + (j : ℤ)) (bitsToSym (tbits.drop j)) := by
      have htarget_drop : tapeAgrees tape (p_t + (j : ℤ)) (bitsToSym (tbits.drop j)) := by
        have hsplit := (tapeAgrees_append tape p_t ((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true)) (bitsToSym (tbits.drop j))).mp (by simpa [targetTape] using htarget)
        have hoffset : p_t + (min j tbits.length : ℤ) = p_t + (j : ℤ) := by omega
        simpa [hoffset] using hsplit.2
      intro i hi
      have h := htarget_drop i hi
      rw [show tape1 (p_t + (j : ℤ) + (i : ℤ)) = tape (p_t + (j : ℤ) + (i : ℤ)) from by
        simp [tape1]
        intro h'
        have hlen_drop : (bitsToSym (tbits.drop j)).length = k - j := by simp [bitsToSym, htlen, List.length_drop]
        have hi_lt : (i : ℤ) < (k - j : ℤ) := by
          have : (i : ℕ) < (bitsToSym (tbits.drop j)).length := hi
          rw [hlen_drop] at this
          omega
        have hlt : p_t + (j : ℤ) + (i : ℤ) < p_t + (k : ℤ) := by omega
        omega]
      exact h
    rcases subtract_one_matches_subOne (bitsToSym (tbits.drop j)) b' (p_t + (j : ℤ)) tape1 hsub'
      (bitsToSym_data (tbits.drop j)) (bitsToSym_marks (tbits.drop j)) htape_drop
      with ⟨πsub, cfgsub, hπsub, hs_sub, hhead_sub, htape_sub, hleft_sub, hright_sub⟩
    -- 6. 状态 81 右移回元素区（穿 target 剩余 + #₀ + sel 到 v_0）
    let m := firstTrueIdx (tbits.drop j)
    let n : ℕ := (p_e - p_t - (j : ℤ) - (m : ℤ)).toNat
    let p' : ℤ := p_t + ((j + m + 1 : ℕ) : ℤ)
    have hm_lt : m < k - j := by
      have htrue : true ∈ tbits.drop j := (subOne_some_iff_mem_true (tbits.drop j)).mp ⟨b', hsub_drop⟩
      have hlt := firstTrueIdx_lt_length_of_mem (tbits.drop j) htrue
      simpa [m, List.length_drop, htlen] using hlt
    have hn_n : (n : ℤ) = p_e - p_t - (j : ℤ) - (m : ℤ) := by
      change ((p_e - p_t - (j : ℤ) - (m : ℤ)).toNat : ℤ) = p_e - p_t - (j : ℤ) - (m : ℤ)
      exact Int.toNat_of_nonneg (by omega : 0 ≤ p_e - p_t - (j : ℤ) - (m : ℤ))
    have hhead_sub' : cfgsub.headPos = p' := by
      rw [hhead_sub]
      rw [symToBits_bitsToSym]
      simp only [p', m]
      push_cast
      ring
    have hp_n : p' + (n : ℤ) = p_e + 1 := by
      rw [hn_n]
      simp only [p']
      omega
    have hnc12 : ∀ i : ℤ, p' ≤ i ∧ i < p' + (n : ℤ) → (cfgsub.tape i).1 = SymKind.data0 ∨ (cfgsub.tape i).1 = SymKind.data1 ∨ (cfgsub.tape i).1 = SymKind.boundary := by
      intro i hi
      have hi_lt_pe : i < p_e + 1 := by
        have := hi.2
        rw [hp_n] at this
        exact this
      by_cases hlt_target : i < p_t + (k : ℤ)
      · -- target 剩余位（markFirst b' 部分）
        have ioff : ∃ io : ℕ, (io : ℤ) = i - (p_t + (j : ℤ)) := by
          refine ⟨(i - (p_t + (j : ℤ))).toNat, ?_⟩
          exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p_t + (j : ℤ)))
        rcases ioff with ⟨io, hio⟩
        have hio_lt : io < (markFirst b').length := by
          rw [markFirst_length]
          have hb'_len : b'.length = (tbits.drop j).length := subOne_length (tbits.drop j) b' hsub_drop
          rw [hb'_len, List.length_drop]
          omega
        have ht := htape_sub io hio_lt
        have hidx : p_t + (j : ℤ) + (io : ℤ) = i := by omega
        rw [hidx] at ht
        have hd := markFirst_data b' ((markFirst b')[io]) (List.getElem_mem hio_lt)
        rw [ht]
        rcases hd with hd0 | hd1
        · left
          exact hd0
        · right; left
          exact hd1
      · -- data0 填充 / #₀ / sel
        have hright_i : cfgsub.tape i = tape1 i := hright_sub i (by
          have hlen_drop : (bitsToSym (tbits.drop j)).length = k - j := by simp [bitsToSym, htlen, List.length_drop]
          omega)
        rw [hright_i]
        by_cases hpad_i : i < p_e - 1
        · have h := hpad i (by constructor <;> omega)
          rw [show tape1 i = tape i from by simp [tape1]; intro h'; omega]
          rw [h]
          left; rfl
        · by_cases hh0 : i = p_e - 1
          · rw [hh0]
            rw [show tape1 (p_e - 1) = tape (p_e - 1) from by simp [tape1]; intro h'; omega]
            rw [hbound]
            right; right; rfl
          · have hi_pe : i = p_e := by omega
            rw [hi_pe]
            rw [show tape1 p_e = tape p_e from by simp [tape1]; intro h'; omega]
            rcases hsel with hd0 | hd1
            · left; exact hd0
            · right; left; exact hd1
    have hcons12 : cfgsub.tape (p' + (n : ℤ)) = Sym.consumed := by
      rw [hp_n]
      have hright_v0 : cfgsub.tape (p_e + 1) = tape1 (p_e + 1) := hright_sub (p_e + 1) (by
        have hlen_drop : (bitsToSym (tbits.drop j)).length = k - j := by simp [bitsToSym, htlen, List.length_drop]
        rw [hlen_drop]
        omega)
      rw [hright_v0]
      by_cases hj0 : j = 0
      · subst j
        simp [tape1]
      · have h0lt : 0 < j := by omega
        have h := helem_pre 0 h0lt
        rw [show tape1 (p_e + 1) = tape (p_e + 1) from by simp [tape1]; intro h'; omega]
        simpa using h
    rcases scanRight81 n p' cfgsub.tape hnc12 hcons12 with ⟨π12, cfg12, hπ12, hs12, hhead12, htape12⟩
    -- 7. 状态 13 右移扫 consumed 到 v_{j+1}
    have hcons13 : ∀ i : ℤ, p_e + 2 ≤ i ∧ i < p_e + 2 + (j : ℤ) → cfgsub.tape i = Sym.consumed := by
      intro i hi
      have hright_i : cfgsub.tape i = tape1 i := hright_sub i (by
        have hlen_drop : (bitsToSym (tbits.drop j)).length = k - j := by simp [bitsToSym, htlen, List.length_drop]
        rw [hlen_drop]
        omega)
      rw [hright_i]
      have ioff : ∃ io : ℕ, (io : ℤ) = i - (p_e + 2) := by
        refine ⟨(i - (p_e + 2)).toNat, ?_⟩
        exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p_e + 2))
      rcases ioff with ⟨io, hio⟩
      have hio_lt : io < j := by omega
      have hidx : i = p_e + 1 + ((io + 1 : ℕ) : ℤ) := by omega
      rw [hidx]
      have hio1_le : io + 1 ≤ j := by omega
      by_cases hio1_eq : io + 1 = j
      · rw [hio1_eq]
        simp [tape1]
      · have hio1_lt : io + 1 < j := by omega
        have h := helem_pre (io + 1) hio1_lt
        rw [show tape1 (p_e + 1 + ((io + 1 : ℕ) : ℤ)) = tape (p_e + 1 + ((io + 1 : ℕ) : ℤ)) from by simp [tape1]; intro h'; omega]
        exact h
    have hv13_tag : (j + 1 < k ∧ (cfgsub.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = Sym.data0 ∨
          cfgsub.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = Sym.data1))
        ∨ (j + 1 = k ∧ (cfgsub.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = Sym.boundary ∨
            cfgsub.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = Sym.data0)) := by
      by_cases hj_last : j + 1 < k
      · -- j+1 < k：v_{j+1} 是 data 位
        left
        refine ⟨hj_last, ?_⟩
        have hright_v : cfgsub.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = tape1 (p_e + 1 + ((j + 1 : ℕ) : ℤ)) := hright_sub (p_e + 1 + ((j + 1 : ℕ) : ℤ)) (by
          have hlen_drop : (bitsToSym (tbits.drop j)).length = k - j := by simp [bitsToSym, htlen, List.length_drop]
          rw [hlen_drop]
          omega)
        rw [hright_v]
        have hneq : p_e + 1 + ((j + 1 : ℕ) : ℤ) ≠ p_e + 1 + (j : ℤ) := by omega
        rw [show tape1 (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) from by
          simp [tape1, hneq]]
        have hlen_pos : 0 < (bitsToSym (ebits.drop (j + 1))).length := by
          simp [bitsToSym, helen, List.length_drop]
          omega
        have h := helem_rest 0 hlen_pos
        have h' : tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = (bitsToSym (ebits.drop (j + 1)))[0] := by
          simpa using h
        have hmem : (bitsToSym (ebits.drop (j + 1)))[0] ∈ bitsToSym (ebits.drop (j + 1)) := List.getElem_mem hlen_pos
        have hdata := bitsToSym_data (ebits.drop (j + 1)) ((bitsToSym (ebits.drop (j + 1)))[0]) hmem
        have hmarks := bitsToSym_marks (ebits.drop (j + 1)) ((bitsToSym (ebits.drop (j + 1)))[0]) hmem
        rw [h']
        cases hdata with
        | inl hd =>
            left
            have hsym : (bitsToSym (ebits.drop (j + 1)))[0] = Sym.data0 := by
              ext <;> simp [hd, hmarks, Sym.data0, Sym.mk]
            exact hsym
        | inr hd =>
            right
            have hsym : (bitsToSym (ebits.drop (j + 1)))[0] = Sym.data1 := by
              ext <;> simp [hd, hmarks, Sym.data1, Sym.mk]
            exact hsym
      · -- j+1 = k：读 #₁ 或下一元素标记
        right
        have hj_eq : j + 1 = k := by omega
        refine ⟨hj_eq, ?_⟩
        have hright_v : cfgsub.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = tape1 (p_e + 1 + ((j + 1 : ℕ) : ℤ)) := hright_sub (p_e + 1 + ((j + 1 : ℕ) : ℤ)) (by
          have hlen_drop : (bitsToSym (tbits.drop j)).length = k - j := by simp [bitsToSym, htlen, List.length_drop]
          omega)
        rw [hright_v]
        have hneq : p_e + 1 + ((j + 1 : ℕ) : ℤ) ≠ p_e + 1 + (j : ℤ) := by omega
        rw [show tape1 (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) from by
          simp [tape1, hneq]]
        simpa [hj_eq] using hv_succ
    rcases scanRight13 j (p_e + 2) cfgsub.tape hcons13 (by
        rcases hv13_tag with hd | hb
        · rcases hd.2 with hd0 | hd1
          · left
            simpa [add_assoc, add_comm, add_left_comm] using hd0
          · right; left
            simpa [add_assoc, add_comm, add_left_comm] using hd1
        · rcases hb.2 with hbnd | hd0b
          · right; right
            simpa [add_assoc, add_comm, add_left_comm] using hbnd
          · left
            simpa [add_assoc, add_comm, add_left_comm] using hd0b)
      with ⟨π13, cfg13, hπ13, hfin13, htape13⟩
    -- 组装：target 区不变量
    have htarget_pre : tapeAgrees tape p_t ((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true)) := by
      have hsplit := (tapeAgrees_append tape p_t ((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true)) (bitsToSym (tbits.drop j))).mp (by simpa [targetTape] using htarget)
      exact hsplit.1
    have hcfgsub_pre : tapeAgrees cfgsub.tape p_t ((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true)) := by
      intro i hi
      have h := htarget_pre i hi
      have hlen : ((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true)).length = j := by
        simp [htlen, Nat.min_eq_left (Nat.le_of_lt hj)]
      rw [show cfgsub.tape (p_t + (i : ℤ)) = tape1 (p_t + (i : ℤ)) from hleft_sub (p_t + (i : ℤ)) (by omega)]
      rw [show tape1 (p_t + (i : ℤ)) = tape (p_t + (i : ℤ)) from by
        simp [tape1]
        intro h'
        have hi_lt : (i : ℤ) < (k : ℤ) := by omega
        omega]
      exact h
    have htarget_next_eq : targetTape (j + 1) ((subOneAt j tbits).getD tbits) =
        (tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true) ++ markFirst b' := by
      have hsubAt : subOneAt j tbits = some ((tbits.take j) ++ b') := by
        rw [subOneAt_eq_drop, hsub_drop]
        rfl
      have hgetD : (subOneAt j tbits).getD tbits = (tbits.take j) ++ b' := by
        rw [hsubAt]
        rfl
      rw [hgetD]
      exact targetTape_succ_append tbits j b' hsub_drop
    have hcfgsub_target : tapeAgrees cfgsub.tape p_t (targetTape (j + 1) ((subOneAt j tbits).getD tbits)) := by
      rw [htarget_next_eq]
      have hlen : ((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true)).length = j := by
        simp [htlen, Nat.min_eq_left (Nat.le_of_lt hj)]
      have hsub'' : tapeAgrees cfgsub.tape (p_t + (((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true)).length : ℤ)) (markFirst b') := by
        rw [hlen]
        exact htape_sub
      exact (tapeAgrees_append cfgsub.tape p_t ((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true)) (markFirst b')).mpr ⟨hcfgsub_pre, hsub''⟩
    have hcfgsub_cons : ∀ i : ℕ, i ≤ j → cfgsub.tape (p_e + 1 + (i : ℤ)) = Sym.consumed := by
      intro i hi
      have hright_i : cfgsub.tape (p_e + 1 + (i : ℤ)) = tape1 (p_e + 1 + (i : ℤ)) := hright_sub (p_e + 1 + (i : ℤ)) (by
        have hlen_drop : (bitsToSym (tbits.drop j)).length = k - j := by simp [bitsToSym, htlen, List.length_drop]
        rw [hlen_drop]
        omega)
      rw [hright_i]
      by_cases hij : i = j
      · subst i
        simp [tape1]
      · have hi_lt : i < j := by omega
        have h := helem_pre i hi_lt
        rw [show tape1 (p_e + 1 + (i : ℤ)) = tape (p_e + 1 + (i : ℤ)) from by simp [tape1]; intro h'; omega]
        exact h
    have hcfgsub_rest : tapeAgrees cfgsub.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) (bitsToSym (ebits.drop (j + 1))) := by
      intro i hi
      have h := helem_rest i hi
      have hright_i : cfgsub.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ)) = tape1 (p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ)) := hright_sub (p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ)) (by
        have hlen_drop : (bitsToSym (tbits.drop j)).length = k - j := by simp [bitsToSym, htlen, List.length_drop]
        rw [hlen_drop]
        omega)
      rw [hright_i]
      rw [show tape1 (p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ)) = tape (p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ)) from by
        simp [tape1]; intro h'; omega]
      exact h
    -- 组装路径
    have hstep5' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) [step5] (SymConfig.mk 76 tape1 (p_e + (j : ℤ))) := hcfg5 ▸ hstep5
    have h567 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6) cfg6 := SymSteps_trans _ _ _ _ [step5] π6 hstep5' hπ6
    have hhead6' : cfg6.headPos = p_e - 2 := by
      rw [hhead6]
      simp [Dir.toInt]
      omega
    have hcfg6_eq : cfg6 = SymConfig.mk 77 tape1 (p_e - 2) := by
      rw [← hs6, ← htape6, ← hhead6']
    have hπ7' : SymSteps VerifierSym.transition cfg6 π7 cfg7 := by
      rw [hcfg6_eq]; exact hπ7
    have h567' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6 ++ π7) cfg7 := SymSteps_trans _ _ _ _ ([step5] ++ π6) π7 h567 hπ7'
    have hhead7' : cfg7.headPos = p_t := by
      rw [hhead7]
      simp [Dir.toInt]
      omega
    have hcfg7_eq : cfg7 = SymConfig.mk 10 tape1 p_t := by
      rw [← hs7, ← htape7, ← hhead7']
    have hπ10' : SymSteps VerifierSym.transition cfg7 π10 cfg10 := by
      rw [hcfg7_eq]; exact hπ10
    have h567'' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6 ++ π7 ++ π10) cfg10 := SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7) π10 h567' hπ10'
    have hcfg10_eq : cfg10 = SymConfig.mk 10 tape1 (p_t + (j : ℤ)) := by
      rw [← hs10, ← htape10, ← hhead10]
    have hsub' : SymSteps VerifierSym.transition cfg10 πsub cfgsub := by
      rw [hcfg10_eq]; exact hπsub
    have h567''' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6 ++ π7 ++ π10 ++ πsub) cfgsub := SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7 ++ π10) πsub h567'' hsub'
    have hcfgsub_eq : cfgsub = SymConfig.mk 81 cfgsub.tape p' := by
      rw [← hs_sub, ← hhead_sub']
    have h12' : SymSteps VerifierSym.transition cfgsub π12 cfg12 := by
      rw [hcfgsub_eq]; exact hπ12
    have h567'''' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6 ++ π7 ++ π10 ++ πsub ++ π12) cfg12 := SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7 ++ π10 ++ πsub) π12 h567''' h12'
    have hhead12' : cfg12.headPos = p_e + 2 := by
      rw [hhead12]
      rw [hp_n]
      omega
    have hcfg12_eq : cfg12 = SymConfig.mk 13 cfgsub.tape (p_e + 2) := by
      rw [← hs12, ← htape12, ← hhead12']
    have h13' : SymSteps VerifierSym.transition cfg12 π13 cfg13 := by
      rw [hcfg12_eq]; exact hπ13
    have htotal : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6 ++ π7 ++ π10 ++ πsub ++ π12 ++ π13) cfg13 := SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7 ++ π10 ++ πsub ++ π12) π13 h567'''' h13'
    refine ⟨[step5] ++ π6 ++ π7 ++ π10 ++ πsub ++ π12 ++ π13, cfg13, htotal, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

    · -- state/headPos 析取（带读符号标签）
      rcases hfin13 with h5 | h84
      · right
        refine ⟨h5.1, ?_, ?_⟩
        · simpa [add_assoc, add_comm, add_left_comm] using h5.2.1
        · rw [htape13]
          simpa [add_assoc, add_comm, add_left_comm] using h5.2.2
      · left
        refine ⟨h84.1, ?_, ?_⟩
        · simpa [add_assoc, add_comm, add_left_comm] using h84.2.1
        · rw [htape13]
          simpa [add_assoc, add_comm, add_left_comm] using h84.2.2
    · rw [htape13, hvj_bool]
      exact hcfgsub_target
    · intro i hi
      rw [htape13]
      exact hcfgsub_cons i hi
    · rw [htape13]
      exact hcfgsub_rest
    · rw [htape13]
      rw [hright_sub p_e (by
        have hlen : (bitsToSym (tbits.drop j)).length = k - j := by simp [bitsToSym, htlen]
        omega)]
      rw [show tape1 p_e = tape p_e from by simp [tape1]; intro h; omega]
      exact hsel
    · rw [htape13]
      rw [hleft_sub (p_t - 1) (by omega)]
      rw [show tape1 (p_t - 1) = tape (p_t - 1) from by simp [tape1]; intro h; omega]
      exact hhashL
    · rw [htape13]
      rw [hright_sub (p_e - 1) (by
        have hlen : (bitsToSym (tbits.drop j)).length = k - j := by simp [bitsToSym, htlen]
        omega)]
      rw [show tape1 (p_e - 1) = tape (p_e - 1) from by simp [tape1]; intro h; omega]
      exact hbound
    · rw [htape13]
      rw [hright_sub (p_e + 1 + (k : ℤ)) (by
        have hlen : (bitsToSym (tbits.drop j)).length = k - j := by simp [bitsToSym, htlen]
        omega)]
      rw [show tape1 (p_e + 1 + (k : ℤ)) = tape (p_e + 1 + (k : ℤ)) from by simp [tape1]; intro h; omega]
    · rw [htape13]
      rw [hright_sub p_e (by
        have hlen : (bitsToSym (tbits.drop j)).length = k - j := by simp [bitsToSym, htlen]
        omega)]
      rw [show tape1 p_e = tape p_e from by simp [tape1]; intro h; omega]
    · -- gap
      intro i hi
      rw [htape13]
      rw [hright_sub i (by
        have hlen : (bitsToSym (tbits.drop j)).length = k - j := by simp [bitsToSym, htlen]
        omega)]
      rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
      exact hpad i hi
    · -- 右不变
      intro i hi
      rw [htape13]
      rw [hright_sub i (by
        have hlen : (bitsToSym (tbits.drop j)).length = k - j := by simp [bitsToSym, htlen]
        omega)]
      rw [show tape1 i = tape i from by
        dsimp [tape1]
        rw [if_neg (by omega : i ≠ p_e + 1 + (j : ℤ))]]

  · -- 标记路径（v_j = false）：状态 5→8→9→12→81→13→5
    have hvj' : tape (p_e + 1 + (j : ℤ)) = Sym.data0 := by simpa [hvj_bool] using hvj
    have hp_t_lt : p_t + (k : ℤ) < p_e := boundary_after_target k j p_t p_e tape tbits (le_of_eq htlen.symm) hj hp_t_le htarget hbound
    have hne_pe : p_e ≠ p_t + (j : ℤ) := by omega
    have hne_pe1 : p_e - 1 ≠ p_t + (j : ℤ) := by omega
    let r5 : SymTransResult := { nextState := 8, writeSym := Sym.consumed, moveDir := Dir.L }
    let step5 : SymStep := { fromState := 5, readSym := Sym.data0, result := r5 }
    have htrans5 : step5.result ∈ VerifierSym.transition (5, tape (p_e + 1 + (j : ℤ))) := by
      unfold step5 r5
      rw [hvj']
      decide
    let tape1 : ℤ → Sym := fun i => if i = p_e + 1 + (j : ℤ) then Sym.consumed else tape i
    have hstep5 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) [step5]
        (symStepConfig (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) step5.result) := by
      refine SymSteps.cons [] step5 (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) SymSteps.nil ?_ ?_ ?_
      · rfl
      · change Sym.data0 = tape (p_e + 1 + (j : ℤ))
        rw [hvj']
      · change step5.result ∈ VerifierSym.transition (5, tape (p_e + 1 + (j : ℤ)))
        unfold step5 r5
        rw [hvj']
        decide
    have hcfg5 : symStepConfig (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) step5.result =
        SymConfig.mk 8 tape1 (p_e + (j : ℤ)) := by
      simp [symStepConfig, SymConfig.mk, step5, r5, tape1, Dir.toInt]
      omega
    -- 状态 8 左移 j+1 格到 #₀
    have hnb8 : ∀ i : ℤ, p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ) < i ∧ i ≤ p_e + (j : ℤ) →
        (tape1 i).1 = SymKind.consumed ∨ (tape1 i).1 = SymKind.data0 ∨ (tape1 i).1 = SymKind.data1 := by
      intro i h
      have hi : p_e ≤ i ∧ i ≤ p_e + (j : ℤ) := by constructor <;> omega
      by_cases heq : i = p_e
      · subst i
        rw [show tape1 p_e = tape p_e from by simp [tape1]; intro h; omega]
        rcases hsel with hk | hk
        · right; left; exact hk
        · right; right; exact hk
      · have ioff : ∃ io : ℕ, (io : ℤ) = i - (p_e + 1) := by
          refine ⟨(i - (p_e + 1)).toNat, ?_⟩
          exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p_e + 1))
        rcases ioff with ⟨io, hio⟩
        have hio_le : io ≤ j := by omega
        by_cases heqio : io = j
        · subst io
          have hidx : i = p_e + 1 + (j : ℤ) := by omega
          rw [hidx]
          simp [tape1]
          left; rfl
        · have hio_lt : io < j := by omega
          have ht := helem_pre io hio_lt
          have hidx : p_e + 1 + (io : ℤ) = i := by omega
          have ht' : tape i = Sym.consumed := by
            rw [hidx] at ht
            exact ht
          rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
          rw [ht']
          left; rfl
    have hbound8 : tape1 (p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ)) = Sym.boundary := by
      have hpos : p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ) = p_e - 1 := by omega
      rw [hpos]
      rw [show tape1 (p_e - 1) = tape (p_e - 1) from by simp [tape1]; intro h; omega]
      exact hbound
    have hend8 : { nextState := 9, writeSym := Sym.boundary, moveDir := Dir.L } ∈ VerifierSym.transition (8, Sym.boundary) := by decide
    have hkeep8 : ∀ s : Sym, s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 →
        { nextState := 8, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (8, s) := trans8_keep
    rcases scanLeftKeepP 8 9 Sym.boundary Dir.L (j + 1) (p_e + (j : ℤ)) tape1
        (fun s => s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1)
        hnb8 hbound8 hkeep8 hend8 rfl
      with ⟨π8, cfg8, hπ8, hs8, hhead8, htape8⟩
    -- 状态 9 左移 (p_e - p_t - 1) 格到 #ₗ
    let n9 : ℕ := (p_e - p_t - 1).toNat
    have hn9 : (n9 : ℤ) = p_e - p_t - 1 := by
      change ((p_e - p_t - 1).toNat : ℤ) = p_e - p_t - 1
      exact Int.toNat_of_nonneg (by omega : 0 ≤ p_e - p_t - 1)
    have hnb9 : ∀ i : ℤ, (p_e - 2) - (n9 : ℤ) < i ∧ i ≤ p_e - 2 → (tape1 i).1 = SymKind.data0 ∨ (tape1 i).1 = SymKind.data1 := by
      intro i h
      rw [hn9] at h
      have hi : p_t ≤ i ∧ i < p_e - 1 := by constructor <;> omega
      by_cases hlt_target : i < p_t + (k : ℤ)
      · -- target 位
        have ioff : ∃ io : ℕ, (io : ℤ) = i - p_t := by
          refine ⟨(i - p_t).toNat, ?_⟩
          exact Int.toNat_of_nonneg (by linarith only [hi.1])
        rcases ioff with ⟨io, hio⟩
        have hio_lt : io < (targetTape j tbits).length := by
          have hlen : (targetTape j tbits).length = tbits.length := by
            simp [targetTape_length]
          rw [hlen]
          omega
        have ht := htarget io hio_lt
        have hnb_io : ((targetTape j tbits)[io]).1 = SymKind.data0 ∨ ((targetTape j tbits)[io]).1 = SymKind.data1 := by
          have hmem : (targetTape j tbits)[io] ∈ targetTape j tbits := List.getElem_mem hio_lt
          exact targetTape_data j tbits ((targetTape j tbits)[io]) hmem
        have hidx : p_t + (io : ℤ) = i := by omega
        rw [hidx] at ht
        rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
        rw [ht]
        exact hnb_io
      · -- data0 填充
        have hpad_i := hpad i (by constructor <;> omega)
        rw [show tape1 i = tape i from by simp [tape1]; intro h'; omega]
        rw [hpad_i]
        left; rfl
    -- 3b. 状态 8 左扫（data/consumed 到 #₀ → 9）
    let n8 : ℕ := j + 1
    have hstep5' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) [step5] (SymConfig.mk 8 tape1 (p_e + (j : ℤ))) :=
      hcfg5 ▸ hstep5
    have hbound8 : tape1 (p_e + (j : ℤ) - (n8 : ℤ)) = Sym.boundary := by
      have hpos : p_e + (j : ℤ) - (n8 : ℤ) = p_e - 1 := by
        dsimp [n8]
        omega
      rw [hpos]
      rw [show tape1 (p_e - 1) = tape (p_e - 1) from by simp [tape1]; intro h; omega]
      exact hbound
    have hend8 : { nextState := 9, writeSym := Sym.boundary, moveDir := Dir.L } ∈ VerifierSym.transition (8, Sym.boundary) := by decide
    have hkeep8 : ∀ i : ℤ, p_e + (j : ℤ) - (n8 : ℤ) < i ∧ i ≤ p_e + (j : ℤ) →
        { nextState := 8, writeSym := tape1 i, moveDir := Dir.L } ∈ VerifierSym.transition (8, tape1 i) := by
      intro i hi
      by_cases hcons : (tape1 i).1 = SymKind.consumed
      · exact trans8_keep (tape1 i) (Or.inl hcons)
      · have hdata : (tape1 i).1 = SymKind.data0 ∨ (tape1 i).1 = SymKind.data1 := by
          have hi_eq : i = p_e := by
            by_contra hne
            have hi_gt : p_e < i := by omega
            have ioff : ∃ io : ℕ, (io : ℤ) = i - (p_e + 1) := by
              refine ⟨(i - (p_e + 1)).toNat, ?_⟩
              exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p_e + 1))
            rcases ioff with ⟨io, hio⟩
            have hio_lt : io < j := by omega
            have hpre := helem_pre io hio_lt
            have hcons_i : (tape1 i).1 = SymKind.consumed := by
              rw [show i = p_e + 1 + (io : ℤ) from by omega]
              rw [show tape1 (p_e + 1 + (io : ℤ)) = tape (p_e + 1 + (io : ℤ)) from by simp [tape1]; intro h; omega]
              exact congrArg (fun s : Sym => s.1) hpre
            exact hcons hcons_i
          rw [hi_eq]
          have hsel0 : (tape1 p_e).1 = SymKind.data0 ∨ (tape1 p_e).1 = SymKind.data1 := by
            rw [show tape1 p_e = tape p_e from by simp [tape1]; intro h; omega]
            exact hsel
          rcases hsel0 with hd0 | hd1
          · left; exact hd0
          · right; exact hd1
        exact trans8_keep (tape1 i) (Or.inr hdata)
    rcases scanLeftKeepPos 8 9 Sym.boundary Dir.L n8 (p_e + (j : ℤ)) tape1 hkeep8 hend8 hbound8
      with ⟨π8, cfg8, hπ8, hs8, hhead8, htape8⟩
    have hcfg8_eq : cfg8 = SymConfig.mk 9 tape1 (p_e + (j : ℤ) - (n8 : ℤ) + (-1)) := by
      cases cfg8 with
      | mk s t hp =>
          have hs8' : s = 9 := by simpa [SymConfig.mk] using hs8
          have htape8' : t = tape1 := by simpa [SymConfig.mk] using htape8
          subst s
          subst t
          simp [Dir.toInt] at hhead8
          rw [hhead8]
    have hbound9 : tape1 ((p_e - 2) - (n9 : ℤ)) = Sym.boundary := by
      have hpos : (p_e - 2) - (n9 : ℤ) = p_t - 1 := by rw [hn9]; omega
      rw [hpos]
      rw [show tape1 (p_t - 1) = tape (p_t - 1) from by simp [tape1]; intro h; omega]
      exact hhashL
    have hend9 : { nextState := 12, writeSym := Sym.boundary, moveDir := Dir.R } ∈ VerifierSym.transition (9, Sym.boundary) := by decide
    have hkeep9 : ∀ s : Sym, s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 →
        { nextState := 9, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (9, s) := trans9_keep
    rcases scanLeftKeepP 9 12 Sym.boundary Dir.R n9 (p_e - 2) tape1
        (fun s => s.1 = SymKind.data0 ∨ s.1 = SymKind.data1)
        hnb9 hbound9 hkeep9 hend9 rfl
      with ⟨π9, cfg9, hπ9, hs9, hhead9, htape9⟩
    -- 4. 状态 12 右移 j 格（4F4.4 前缀）
    have hkeep12b : ∀ i : ℤ, p_t ≤ i ∧ i < p_t + (j : ℤ) → { nextState := 12, writeSym := tape1 i, moveDir := Dir.R } ∈ VerifierSym.transition (12, tape1 i) := by
      intro i h
      have hi : p_t ≤ i ∧ i < p_t + (k : ℤ) := by constructor <;> omega
      have ioff : ∃ io : ℕ, (io : ℤ) = i - p_t := by
        refine ⟨(i - p_t).toNat, ?_⟩
        exact Int.toNat_of_nonneg (by linarith only [hi.1])
      rcases ioff with ⟨io, hio⟩
      have hio_lt : io < (targetTape j tbits).length := by
        have hlen : (targetTape j tbits).length = k := by
          simp [targetTape, bitsToSym, htlen, List.length_drop, Nat.min_eq_left (Nat.le_of_lt hj)]
          omega
        rw [hlen]
        omega
      have ht := htarget io hio_lt
      have hio_j : io < j := by omega
      have hio_tbits : io < tbits.length := by omega
      have hsym : (targetTape j tbits)[io] = (if tbits[io] then Sym.data1 true else Sym.data0 true) := by
        simp [targetTape, bitsToSym, hio_j, hio_tbits]
      have hidx : p_t + (io : ℤ) = i := by omega
      rw [hidx] at ht
      rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
      rw [ht, hsym]
      have hk : ((if tbits[io] then Sym.data1 true else Sym.data0 true).1 = SymKind.data0 ∨
          (if tbits[io] then Sym.data1 true else Sym.data0 true).1 = SymKind.data1) := by
        by_cases hb : tbits[io] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]
      exact trans12_marked (if tbits[io] then Sym.data1 true else Sym.data0 true) (by by_cases hb : tbits[io] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]) hk
    rcases scanRightKeep 12 j p_t tape1 hkeep12b with ⟨π12b, cfg12b, hπ12b, hs12b, hhead12b, htape12b⟩
    -- 5. 状态 12 读 t_j（m=0）→ 81 标 m=1 右移
    have htape_tj : tape1 (p_t + (j : ℤ)) = (if tbits[j] then Sym.data1 else Sym.data0) := by
      rw [show tape1 (p_t + (j : ℤ)) = tape (p_t + (j : ℤ)) from by simp [tape1]; intro h'; omega]
      have hj' : j < tbits.length := by omega
      have h := htarget j (by
        have hlen : (targetTape j tbits).length = tbits.length := by
          simp [targetTape_length]
        rw [hlen]
        omega)
      simpa [targetTape_getElem_j j tbits hj'] using h
    let tape2 : ℤ → Sym := fun i => if i = p_t + (j : ℤ) then (if tbits[j] then Sym.data1 true else Sym.data0 true) else tape1 i
    let r_tj : SymTransResult := { nextState := 81, writeSym := (if tbits[j] then Sym.data1 true else Sym.data0 true), moveDir := Dir.R }
    let step_tj : SymStep := { fromState := 12, readSym := (if tbits[j] then Sym.data1 else Sym.data0), result := r_tj }
    have htrans_tj : step_tj.result ∈ VerifierSym.transition (12, (if tbits[j] then Sym.data1 else Sym.data0)) := by
      by_cases hb : tbits[j]
      · simp [step_tj, r_tj, hb]
        decide
      · simp [step_tj, r_tj, hb]
        decide
    have hstep_tj : SymSteps VerifierSym.transition (SymConfig.mk 12 tape1 (p_t + (j : ℤ))) [step_tj]
        (symStepConfig (SymConfig.mk 12 tape1 (p_t + (j : ℤ))) step_tj.result) := by
      refine SymSteps.cons [] step_tj (SymConfig.mk 12 tape1 (p_t + (j : ℤ))) SymSteps.nil ?_ ?_ ?_
      · rfl
      · change step_tj.readSym = tape1 (p_t + (j : ℤ))
        simp [step_tj]
        rw [htape_tj]
      · change step_tj.result ∈ VerifierSym.transition (12, tape1 (p_t + (j : ℤ)))
        rw [htape_tj]
        exact htrans_tj
    have hcfg_tj : symStepConfig (SymConfig.mk 12 tape1 (p_t + (j : ℤ))) step_tj.result =
        SymConfig.mk 81 tape2 (p_t + (j : ℤ) + 1) := by
      simp [symStepConfig, SymConfig.mk, step_tj, r_tj, tape2, Dir.toInt]
    -- 6. 状态 81 右移回元素区（穿 target 剩余 + #₀ + sel 到 consumed）→ 13
    have hnc81 : ∀ i : ℤ, p_t + (j : ℤ) + 1 ≤ i ∧ i < p_e + 1 →
        (tape2 i).1 = SymKind.data0 ∨ (tape2 i).1 = SymKind.data1 ∨ (tape2 i).1 = SymKind.boundary := by
      intro i hi
      by_cases hile : i ≤ p_t + (j : ℤ)
      · exfalso
        omega
      · by_cases hik : i < p_t + (k : ℤ)
        · -- target 区（data0/data1）
          have hi_lt_k : i < p_t + (k : ℤ) := hik
          have hd : (tape2 i).1 = SymKind.data0 ∨ (tape2 i).1 = SymKind.data1 := by
            rw [show tape2 i = tape i from by
              dsimp [tape2]
              rw [if_neg (show i ≠ p_t + (j : ℤ) from by
                intro h
                have hbad : p_t + (j : ℤ) + 1 ≤ p_t + (j : ℤ) := h.symm ▸ hi.1
                linarith only [hbad])]
              rw [show tape1 i = tape i from by
                dsimp [tape1]
                rw [if_neg (show i ≠ p_e + 1 + (j : ℤ) from by
                  intro h
                  have hp' : p_t + (k : ℤ) ≤ p_e := by simpa [htlen] using hp_t_le
                  linarith only [hik, h, hp'])]]]
            have ioff : ∃ io : ℕ, (io : ℤ) = i - p_t := by
              refine ⟨(i - p_t).toNat, ?_⟩
              exact Int.toNat_of_nonneg (by linarith only [hi.1])
            rcases ioff with ⟨io, hio⟩
            have hio_lt : io < (targetTape j tbits).length := by
              rw [targetTape_length, htlen]
              have hlt : (io : ℤ) < (k : ℤ) := by
                rw [hio]
                linarith only [hi_lt_k]
              exact Int.ofNat_lt.mp hlt
            have h := htarget io hio_lt
            rw [show p_t + (io : ℤ) = i from by rw [hio]; ring] at h
            rw [h]
            have hmem : (targetTape j tbits)[io] ∈ targetTape j tbits := List.getElem_mem hio_lt
            exact targetTape_data j tbits ((targetTape j tbits)[io]) hmem
          rcases hd with hd0 | hd1
          · left; exact hd0
          · right; left; exact hd1
        · -- i ≥ p_t+k：gap / #₀ / sel 区
          by_cases hlt_pe : i < p_e - 1
          · -- gap data0
            have hd0 : tape2 i = Sym.data0 := by
              have hpad_i := hpad i (by
                constructor
                · have hge : p_t + (k : ℤ) ≤ i := le_of_not_gt (by intro hgt; exact hik hgt)
                  exact hge
                · exact hlt_pe)
              rw [show tape2 i = tape i from by
                dsimp [tape2]
                rw [if_neg (show i ≠ p_t + (j : ℤ) from by
                  intro h
                  have hbad : p_t + (j : ℤ) + 1 ≤ p_t + (j : ℤ) := h.symm ▸ hi.1
                  linarith only [hbad])]
                rw [show tape1 i = tape i from by
                  dsimp [tape1]
                  rw [if_neg (show i ≠ p_e + 1 + (j : ℤ) from by
                    intro h
                    have hbad : p_e + 1 + (j : ℤ) < p_e - 1 := by
                      exact h ▸ hlt_pe
                    linarith only [hbad])]]]
              exact hpad_i
            left
            have hk : (Sym.data0).1 = SymKind.data0 := rfl
            rw [hd0]
            exact hk
          · -- i = p_e-1（#₀）或 p_e（sel）
            by_cases hie : i = p_e - 1
            · right; right
              rw [hie]
              rw [show tape2 (p_e - 1) = tape (p_e - 1) from by
                dsimp [tape2]
                rw [if_neg (show p_e - 1 ≠ p_t + (j : ℤ) from by
                  intro h
                  have hbad : p_t + (j : ℤ) < p_e - 1 := by
                    have hj1 : (j : ℤ) + 1 ≤ (k : ℤ) := by exact_mod_cast (by omega : j + 1 ≤ k)
                    linarith only [hp_t_lt, hj1]
                  linarith only [hbad, h])]
                rw [show tape1 (p_e - 1) = tape (p_e - 1) from by
                  dsimp [tape1]
                  rw [if_neg (show p_e - 1 ≠ p_e + 1 + (j : ℤ) from by
                    intro h
                    linarith only [hj, h])]]]
              exact congrArg (fun s : Sym => s.1) hbound
            · have hi_eq : i = p_e := by omega
              rw [hi_eq]
              have hsel0 : (tape2 p_e).1 = SymKind.data0 ∨ (tape2 p_e).1 = SymKind.data1 := by
                rw [show tape2 p_e = tape p_e from by
                  dsimp [tape2]
                  rw [if_neg (show p_e ≠ p_t + (j : ℤ) from by
                    intro h
                    have hbad : p_t + (j : ℤ) < p_e := by
                      have hj1 : (j : ℤ) + 1 ≤ (k : ℤ) := by exact_mod_cast (by omega : j + 1 ≤ k)
                      linarith only [hp_t_lt, hj1]
                    linarith only [hbad, h])]
                  rw [show tape1 p_e = tape p_e from by
                    dsimp [tape1]
                    rw [if_neg (show p_e ≠ p_e + 1 + (j : ℤ) from by
                      intro h
                      linarith only [hj, h])]]]
                exact hsel
              rcases hsel0 with hd0 | hd1
              · left; exact hd0
              · right; left; exact hd1
    have hn81 : (((p_e + 1 - (p_t + (j : ℤ) + 1)).toNat) : ℤ) = p_e + 1 - (p_t + (j : ℤ) + 1) := by
      exact Int.toNat_of_nonneg (by
        have hp' : p_t + (k : ℤ) ≤ p_e := by simpa [htlen] using hp_t_le
        linarith only [hp', hj])
    rcases scanRightKeep 81 ((p_e + 1 - (p_t + (j : ℤ) + 1)).toNat) (p_t + (j : ℤ) + 1) tape2
        (by
          intro i hi
          have hk := trans81_keep (tape2 i) (hnc81 i (by
            constructor
            · exact hi.1
            · have hlt : i < p_e + 1 := by
                rw [hn81] at hi
                linarith only [hi.2]
              exact hlt))
          exact hk)
      with ⟨π81, cfg81, hπ81, hs81, hhead81, htape81⟩
    have hhead81' : cfg81.headPos = p_e + 1 := by
      rw [hhead81]
      rw [hn81]
      omega
    -- 7. 状态 13 读 v_{j+1}（data0/data1 → 5 S）或 #₁/标记 → 84 L
    have hv13_tag : (j + 1 < k ∧ (cfg81.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = Sym.data0 ∨
          cfg81.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = Sym.data1))
        ∨ (j + 1 = k ∧ (cfg81.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = Sym.boundary ∨
            cfg81.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = Sym.data0)) := by
      by_cases hj_last : j + 1 < k
      · left
        refine ⟨hj_last, ?_⟩
        have hkeep : cfg81.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = tape2 (p_e + 1 + ((j + 1 : ℕ) : ℤ)) := htape81.symm ▸ (by rfl)
        rw [hkeep]
        have hneq1 : p_e + 1 + ((j + 1 : ℕ) : ℤ) ≠ p_t + (j : ℤ) := by omega
        have hneq2 : p_e + 1 + ((j + 1 : ℕ) : ℤ) ≠ p_e + 1 + (j : ℤ) := by omega
        rw [show tape2 (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) from by
          dsimp [tape2]
          rw [if_neg (by simpa [add_assoc, add_comm, add_left_comm] using hneq1)]
          dsimp [tape1]
          rw [if_neg (by simpa [add_assoc, add_comm, add_left_comm] using hneq2)]]
        have hlen_pos : 0 < (bitsToSym (ebits.drop (j + 1))).length := by
          simp [bitsToSym, helen, List.length_drop]
          omega
        have h := helem_rest 0 hlen_pos
        have h' : tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = (bitsToSym (ebits.drop (j + 1)))[0] := by
          simpa using h
        have hmem : (bitsToSym (ebits.drop (j + 1)))[0] ∈ bitsToSym (ebits.drop (j + 1)) := List.getElem_mem hlen_pos
        have hdata := bitsToSym_data (ebits.drop (j + 1)) ((bitsToSym (ebits.drop (j + 1)))[0]) hmem
        have hmarks := bitsToSym_marks (ebits.drop (j + 1)) ((bitsToSym (ebits.drop (j + 1)))[0]) hmem
        rw [h']
        cases hdata with
        | inl hd =>
            left
            have hsym : (bitsToSym (ebits.drop (j + 1)))[0] = Sym.data0 := by
              ext <;> simp [hd, hmarks, Sym.data0, Sym.mk]
            exact hsym
        | inr hd =>
            right
            have hsym : (bitsToSym (ebits.drop (j + 1)))[0] = Sym.data1 := by
              ext <;> simp [hd, hmarks, Sym.data1, Sym.mk]
            exact hsym
      · right
        have hj_eq : j + 1 = k := by omega
        refine ⟨hj_eq, ?_⟩
        have hkeep : cfg81.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = tape2 (p_e + 1 + ((j + 1 : ℕ) : ℤ)) := htape81.symm ▸ (by rfl)
        rw [hkeep]
        have hneq1 : p_e + 1 + ((j + 1 : ℕ) : ℤ) ≠ p_t + (j : ℤ) := by omega
        have hneq2 : p_e + 1 + ((j + 1 : ℕ) : ℤ) ≠ p_e + 1 + (j : ℤ) := by omega
        rw [show tape2 (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) from by
          dsimp [tape2]
          rw [if_neg (by simpa [add_assoc, add_comm, add_left_comm] using hneq1)]
          dsimp [tape1]
          rw [if_neg (by simpa [add_assoc, add_comm, add_left_comm] using hneq2)]]
        simpa [hj_eq] using hv_succ
    have hcons13 : ∀ i : ℤ, p_e + 2 ≤ i ∧ i < p_e + 2 + (j : ℤ) → cfg81.tape i = Sym.consumed := by
      intro i hi
      rw [htape81]
      have hi' : p_t + (j : ℤ) + 1 ≤ i := by omega
      have hcons : tape2 i = Sym.consumed := by
        have ioff : ∃ io : ℕ, (io : ℤ) = i - (p_e + 1) := by
          refine ⟨(i - (p_e + 1)).toNat, ?_⟩
          exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p_e + 1))
        rcases ioff with ⟨io, hio⟩
        have hio_le : io ≤ j := by omega
        by_cases hio_eq : io = j
        · rw [show i = p_e + 1 + (io : ℤ) from by omega]
          rw [hio_eq]
          rw [show tape2 (p_e + 1 + (j : ℤ)) = Sym.consumed from by
            rw [show tape2 (p_e + 1 + (j : ℤ)) = tape1 (p_e + 1 + (j : ℤ)) from by
              dsimp [tape2]
              rw [if_neg (by omega : p_e + 1 + (j : ℤ) ≠ p_t + (j : ℤ))]]
            simp [tape1]]
        · have hio_lt : io < j := by omega
          have hpre := helem_pre io hio_lt
          rw [show i = p_e + 1 + (io : ℤ) from by omega]
          rw [show tape2 (p_e + 1 + (io : ℤ)) = tape (p_e + 1 + (io : ℤ)) from by
            dsimp [tape2]
            rw [if_neg (by omega : p_e + 1 + (io : ℤ) ≠ p_t + (j : ℤ))]
            dsimp [tape1]
            rw [if_neg (by omega : p_e + 1 + (io : ℤ) ≠ p_e + 1 + (j : ℤ))]]
          exact hpre
      exact hcons
    rcases scanRight13 j (p_e + 2) cfg81.tape hcons13 (by
        rcases hv13_tag with hd | hb
        · rcases hd.2 with hd0 | hd1
          · left
            simpa [add_assoc, add_comm, add_left_comm] using hd0
          · right; left
            simpa [add_assoc, add_comm, add_left_comm] using hd1
        · rcases hb.2 with hbnd | hd0b
          · right; right
            simpa [add_assoc, add_comm, add_left_comm] using hbnd
          · left
            simpa [add_assoc, add_comm, add_left_comm] using hd0b)
      with ⟨π13, cfg13, hπ13, hfin13, htape13⟩
    -- 8. 组装
    have hπ81' : SymSteps VerifierSym.transition (SymConfig.mk 81 tape2 (p_t + (j : ℤ) + 1)) π81 cfg81 := hπ81
    have hcfg81_eq : cfg81 = SymConfig.mk 81 tape2 (p_e + 1) := by
      rw [← hs81, ← htape81, ← hhead81']
    -- 8.5 状态 81 读 consumed → 13 R
    let r13i : SymTransResult := { nextState := 13, writeSym := Sym.consumed, moveDir := Dir.R }
    let step13i : SymStep := { fromState := 81, readSym := Sym.consumed, result := r13i }
    have htrans13i : step13i.result ∈ VerifierSym.transition (81, Sym.consumed) := by
      decide
    have hstep13i : SymSteps VerifierSym.transition (SymConfig.mk 81 tape2 (p_e + 1)) [step13i]
        (SymConfig.mk 13 tape2 (p_e + 2)) := by
      have hcons_pe1 : tape2 (p_e + 1) = Sym.consumed := by
        rw [show tape2 (p_e + 1) = tape1 (p_e + 1) from by
          dsimp [tape2]
          rw [if_neg (by omega : p_e + 1 ≠ p_t + (j : ℤ))]]
        by_cases hj0 : j = 0
        · simp [tape1, hj0]
        · have h0 := helem_pre 0 (by omega : 0 < j)
          rw [show tape1 (p_e + 1) = tape (p_e + 1) from by
            dsimp [tape1]
            rw [if_neg (show p_e + 1 ≠ p_e + 1 + (j : ℤ) from by
              intro h
              have hbad : j = 0 := by exact_mod_cast (by linarith only [h] : (j : ℤ) = 0)
              exact hj0 hbad)]]
          simpa [show p_e + 1 + (0 : ℤ) = p_e + 1 from by ring] using h0
      have hcfg13i : symStepConfig (SymConfig.mk 81 tape2 (p_e + 1)) step13i.result =
          SymConfig.mk 13 tape2 (p_e + 2) := by
        unfold step13i r13i
        simp [symStepConfig, SymConfig.mk, Dir.toInt]
        constructor
        · funext i
          by_cases hi : i = p_e + 1
          · rw [hi]
            simp
            exact hcons_pe1.symm
          · simp [hi]
        · ring
      simpa [hcfg13i] using (SymSteps.cons [] step13i (SymConfig.mk 81 tape2 (p_e + 1)) SymSteps.nil
        (by rfl)
        (by
          simp [SymConfig.mk]
          rw [hcons_pe1])
        (by
          change step13i.result ∈ VerifierSym.transition (81, tape2 (p_e + 1))
          rw [hcons_pe1]
          exact htrans13i))
    have hπ13' : SymSteps VerifierSym.transition cfg81 ([step13i] ++ π13) cfg13 := by
      have h13i : SymSteps VerifierSym.transition cfg81 [step13i] (SymConfig.mk 13 tape2 (p_e + 2)) := by
        rw [hcfg81_eq]
        exact hstep13i
      have hπ13'' : SymSteps VerifierSym.transition (SymConfig.mk 13 tape2 (p_e + 2)) π13 cfg13 := by
        have htape81' : cfg81.tape = tape2 := htape81
        simpa [htape81'] using hπ13
      exact SymSteps_trans _ _ _ _ [step13i] π13 h13i hπ13''
    have htotal : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) (([step5] ++ π8 ++ π9 ++ π12b ++ [step_tj] ++ π81) ++ ([step13i] ++ π13)) cfg13 := by
      have h1 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π8) cfg8 :=
        SymSteps_trans _ _ _ _ [step5] π8 hstep5' hπ8
      have h2 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π8 ++ π9) cfg9 := by
        have hcfg8 : cfg8 = SymConfig.mk 9 tape1 (p_e - 2) := by
          rw [hcfg8_eq]
          dsimp [n8]
          ring
        have hπ9' : SymSteps VerifierSym.transition cfg8 π9 cfg9 := by rw [hcfg8]; exact hπ9
        exact SymSteps_trans _ _ _ _ ([step5] ++ π8) π9 h1 hπ9'
      have h3 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π8 ++ π9 ++ π12b) cfg12b := by
        have hhead9' : cfg9.headPos = p_t := by
          rw [hhead9, hn9]
          simp [Dir.toInt]
          ring
        have hcfg9 : cfg9 = SymConfig.mk 12 tape1 p_t := by rw [← hs9, ← htape9, ← hhead9']
        have hπ12b' : SymSteps VerifierSym.transition cfg9 π12b cfg12b := by rw [hcfg9]; exact hπ12b
        exact SymSteps_trans _ _ _ _ ([step5] ++ π8 ++ π9) π12b h2 hπ12b'
      have h4 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π8 ++ π9 ++ π12b ++ [step_tj]) (SymConfig.mk 81 tape2 (p_t + (j : ℤ) + 1)) := by
        have hhead12b' : cfg12b.headPos = p_t + (j : ℤ) := by rw [hhead12b]
        have hcfg12b : cfg12b = SymConfig.mk 12 tape1 (p_t + (j : ℤ)) := by rw [← hs12b, ← htape12b, ← hhead12b']
        have hstep_tj' : SymSteps VerifierSym.transition cfg12b [step_tj] (SymConfig.mk 81 tape2 (p_t + (j : ℤ) + 1)) := by
          rw [hcfg12b]
          exact hcfg_tj ▸ hstep_tj
        exact SymSteps_trans _ _ _ _ ([step5] ++ π8 ++ π9 ++ π12b) [step_tj] h3 hstep_tj'
      have h5 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π8 ++ π9 ++ π12b ++ [step_tj] ++ π81) cfg81 :=
        SymSteps_trans _ _ _ _ ([step5] ++ π8 ++ π9 ++ π12b ++ [step_tj]) π81 h4 hπ81'
      exact SymSteps_trans _ _ _ _ ([step5] ++ π8 ++ π9 ++ π12b ++ [step_tj] ++ π81) ([step13i] ++ π13) h5 hπ13'
    refine ⟨([step5] ++ π8 ++ π9 ++ π12b ++ [step_tj] ++ π81) ++ ([step13i] ++ π13), cfg13, htotal, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- state/headPos 析取（带读符号标签）
      rcases hfin13 with h5f | h84
      · right
        refine ⟨h5f.1, ?_, ?_⟩
        · simpa [add_assoc, add_comm, add_left_comm] using h5f.2.1
        · rw [htape13]
          simpa [add_assoc, add_comm, add_left_comm] using h5f.2.2
      · left
        refine ⟨h84.1, ?_, ?_⟩
        · simpa [add_assoc, add_comm, add_left_comm] using h84.2.1
        · rw [htape13]
          simpa [add_assoc, add_comm, add_left_comm] using h84.2.2
    · -- target 保持（标记路径不减）
      intro i hi
      have hlen : (targetTape (j + 1) tbits).length = k := by
        simp [targetTape, bitsToSym, htlen]
        omega
      have hik : i < k := by simpa [hlen, hvj_bool] using hi
      have hi1 : i < (targetTape j tbits).length := by
        have hlen0 : (targetTape j tbits).length = k := by
          simp [targetTape, bitsToSym, htlen, List.length_drop, Nat.min_eq_left (Nat.le_of_lt hj)]
          omega
        rw [hlen0]
        exact hik
      have htj : j < tbits.length := by rw [htlen]; exact hj
      have hkeep : cfg13.tape (p_t + (i : ℤ)) = tape2 (p_t + (i : ℤ)) := by
        rw [htape13, htape81]
      rw [hkeep]
      by_cases hij : i = j
      · subst i
        dsimp [tape2]
        rw [if_pos rfl]
        rw [show (targetTape (j + 1) (if v_j = true then (subOneAt j tbits).getD tbits else tbits))[j] =
            (targetTape (j + 1) tbits)[j] from by
          simp [hvj_bool]]
        unfold targetTape
        rw [List.getElem_append_left (by
          simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt htj)]
          omega)]
        rw [List.getElem_map _ (i := j)]
        simp [List.getElem_take]
      · rw [show tape2 (p_t + (i : ℤ)) = tape (p_t + (i : ℤ)) from by
          dsimp [tape2]
          rw [if_neg (show p_t + (i : ℤ) ≠ p_t + (j : ℤ) from by
            intro h
            exact hij (by exact_mod_cast (by linarith only [h] : (i : ℤ) = (j : ℤ))))]
          dsimp [tape1]
          rw [if_neg (by omega : p_t + (i : ℤ) ≠ p_e + 1 + (j : ℤ))]]
        rw [show (targetTape (j + 1) (if v_j = true then (subOneAt j tbits).getD tbits else tbits))[i] =
            (targetTape (j + 1) tbits)[i] from by
          simp [hvj_bool]]
        have hta := htarget i hi1
        have hta' : tape (p_t + (i : ℤ)) = (targetTape (j + 1) tbits)[i] := by
          have h := htarget i hi1
          change tape (p_t + (i : ℤ)) = (targetTape j tbits)[i] at h
          by_cases hil : i < j
          · have hL := targetTape_getElem_lt j i tbits (by rw [htlen]; exact hik) hil
            have hR := targetTape_getElem_lt (j + 1) i tbits (by rw [htlen]; exact hik) (by omega : i < j + 1)
            rw [hL] at h
            rw [hR]
            exact h
          · have hig : j < i := by omega
            have hL := targetTape_getElem_ge j i tbits (by rw [htlen]; exact hik) (Nat.le_of_lt hig)
            have hR := targetTape_getElem_ge (j + 1) i tbits (by rw [htlen]; exact hik) (by omega : j + 1 ≤ i)
            rw [hL] at h
            rw [hR]
            exact h
        exact hta'
    · -- consumed：p_e+1..p_e+1+j
      intro i hi
      rw [htape13, htape81]
      by_cases hij : i = j
      · subst i
        dsimp [tape2]
        rw [if_neg (by omega : p_e + 1 + (j : ℤ) ≠ p_t + (j : ℤ))]
        dsimp [tape1]
        rw [if_pos rfl]
      · have hpre := helem_pre i (by omega : i < j)
        dsimp [tape2]
        rw [if_neg (by omega : p_e + 1 + (i : ℤ) ≠ p_t + (j : ℤ))]
        dsimp [tape1]
        rw [if_neg (by omega : p_e + 1 + (i : ℤ) ≠ p_e + 1 + (j : ℤ))]
        exact hpre
    · -- rest：v_{j+1} 起
      intro i hi
      rw [htape13]
      rw [htape81]
      have h := helem_rest i hi
      rw [show tape2 (p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ)) = tape (p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ)) from by
        dsimp [tape2]; rw [if_neg (by omega)]; dsimp [tape1]; rw [if_neg (by omega)]]
      simpa [add_assoc, add_comm, add_left_comm] using h
    · -- p_e 格保持
      rw [htape13]
      rw [htape81]
      rw [show tape2 p_e = tape p_e from by dsimp [tape2]; rw [if_neg (by omega)]; dsimp [tape1]; rw [if_neg (by omega)]]
      exact hsel
    · -- #ₗ 保持
      rw [htape13]
      rw [htape81]
      rw [show tape2 (p_t - 1) = tape (p_t - 1) from by dsimp [tape2]; rw [if_neg (by omega)]; dsimp [tape1]; rw [if_neg (by omega)]]
      exact hhashL
    · -- #₀ 保持
      rw [htape13]
      rw [htape81]
      rw [show tape2 (p_e - 1) = tape (p_e - 1) from by dsimp [tape2]; rw [if_neg (by omega)]; dsimp [tape1]; rw [if_neg (by omega)]]
      exact hbound
    · -- sep 保持（p_e+1+k 格）
      rw [htape13]
      rw [htape81]
      rw [show tape2 (p_e + 1 + (k : ℤ)) = tape (p_e + 1 + (k : ℤ)) from by dsimp [tape2]; rw [if_neg (by omega)]; dsimp [tape1]; rw [if_neg (by omega)]]
    · -- p_e 格等式保持
      rw [htape13]
      rw [htape81]
      rw [show tape2 p_e = tape p_e from by dsimp [tape2]; rw [if_neg (by omega)]; dsimp [tape1]; rw [if_neg (by omega)]]
    · -- gap data0
      intro i hi
      rw [htape13]
      rw [htape81]
      rw [show tape2 i = tape i from by dsimp [tape2]; rw [if_neg (by omega)]; dsimp [tape1]; rw [if_neg (by omega)]]
      exact hpad i hi
    · -- 右不变
      intro i hi
      rw [htape13]
      rw [htape81]
      rw [show tape2 i = tape i from by dsimp [tape2]; rw [if_neg (by omega)]; dsimp [tape1]; rw [if_neg (by omega)]]
lemma scanRight13_scan (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hcons : ∀ i : ℤ, p ≤ i ∧ i < p + (n : ℤ) → tape i = Sym.consumed) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 13 tape p) π cfg' ∧
      cfg'.state = 13 ∧ cfg'.headPos = p + (n : ℤ) ∧ cfg'.tape = tape := by
  induction n generalizing p tape with
  | zero =>
      refine ⟨[], SymConfig.mk 13 tape p, SymSteps.nil, rfl, ?_, rfl⟩
      simp
  | succ n ih =>
      let r : SymTransResult := { nextState := 13, writeSym := Sym.consumed, moveDir := Dir.R }
      let step : SymStep := { fromState := 13, readSym := tape p, result := r }
      have htrans : step.result ∈ VerifierSym.transition (13, tape p) := by
        have hs : (tape p).1 = SymKind.consumed := by
          have h := hcons p (by constructor <;> omega)
          simp [h, Sym.consumed, Sym.mk]
        exact trans13_cons (tape p) hs
      have hstep : SymSteps VerifierSym.transition (SymConfig.mk 13 tape p) [step]
          (symStepConfig (SymConfig.mk 13 tape p) step.result) := by
        refine SymSteps.cons [] step (SymConfig.mk 13 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans
      have hcfg₁ : symStepConfig (SymConfig.mk 13 tape p) step.result = SymConfig.mk 13 tape (p + 1) := by
        have hp : tape p = Sym.consumed := hcons p (by constructor <;> omega)
        simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt, hp]
        funext i
        by_cases hi : i = p
        · rw [hi]
          simp [hp]
        · simp [hi]
      have hcons₁ : ∀ i : ℤ, p + 1 ≤ i ∧ i < p + 1 + (n : ℤ) → tape i = Sym.consumed := by
        intro i h
        exact hcons i (by constructor <;> omega)
      rcases ih (p + 1) tape hcons₁ with ⟨π', cfg', hπ', hs', hhead', htape'⟩
      refine ⟨[step] ++ π', cfg', ?_, hs', ?_, htape'⟩
      · exact SymSteps_trans VerifierSym.transition (SymConfig.mk 13 tape p) (SymConfig.mk 13 tape (p + 1)) cfg'
          [step] π' (hcfg₁ ▸ hstep) hπ'
      · rw [hhead']
        omega

/-- 减一位循环（最后元素变体）：逐位减 2^j，最后一位后读 #₁（boundary）而非 sep。 -/

lemma process_one_bit_last (j : ℕ) (v_j : Bool) (tbits ebits : List Bool)
    (p_t p_e : ℤ) (tape : ℤ → Sym)
    (hlen_le : ebits.length ≤ tbits.length)
    (hj : j < ebits.length)
    (hp_t_le : p_t + (tbits.length : ℤ) ≤ p_e)
    (hbound : tape (p_e - 1) = Sym.boundary)
    (hpad : ∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p_e - 1 → tape i = Sym.data0)
    (htarget : tapeAgrees tape p_t (targetTape j tbits))
    (hhashL : tape (p_t - 1) = Sym.boundary)
    (hsel : (tape p_e).1 = SymKind.data0 ∨ (tape p_e).1 = SymKind.data1)
    (helem_pre : ∀ i : ℕ, i < j → tape (p_e + 1 + (i : ℤ)) = Sym.consumed)
    (hvj : tape (p_e + 1 + (j : ℤ)) = if v_j then Sym.data1 else Sym.data0)
    (helem_rest : tapeAgrees tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) (bitsToSym (ebits.drop (j + 1)))) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) π cfg' ∧
      ((cfg'.state = 13 ∧
      cfg'.headPos = p_e + 1 + ((j + 1 : ℕ) : ℤ) ∧
      tapeAgrees cfg'.tape p_t (targetTape (j + 1)
        (if v_j then (subOneAt j tbits).getD tbits else tbits)) ∧
      (∀ i : ℕ, i ≤ j → cfg'.tape (p_e + 1 + (i : ℤ)) = Sym.consumed) ∧
      tapeAgrees cfg'.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) (bitsToSym (ebits.drop (j + 1))) ∧
      ((cfg'.tape p_e).1 = SymKind.data0 ∨ (cfg'.tape p_e).1 = SymKind.data1) ∧
      cfg'.tape (p_t - 1) = Sym.boundary ∧
      cfg'.tape (p_e - 1) = Sym.boundary ∧
      cfg'.tape (p_e + 1 + (ebits.length : ℤ)) = tape (p_e + 1 + (ebits.length : ℤ)) ∧
      cfg'.tape p_e = tape p_e ∧
      (∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p_e - 1 → cfg'.tape i = Sym.data0) ∧
      (∀ i : ℤ, p_e + 1 + (ebits.length : ℤ) < i → cfg'.tape i = tape i)) ∨
      (cfg'.state = 101 ∧
      cfg'.headPos = p_e ∧
      v_j = true ∧
      bitsValue tbits < 2 ^ j ∧
      (∀ i : ℤ, p_t + (j : ℤ) ≤ i ∧ i < p_e - 1 → (cfg'.tape i).1 = SymKind.data1) ∧
      cfg'.tape (p_e - 1) = Sym.boundary ∧
      (∀ i : ℕ, i ≤ j → cfg'.tape (p_e + 1 + (i : ℤ)) = Sym.consumed) ∧
      cfg'.tape (p_t - 1) = Sym.boundary ∧
      cfg'.tape p_e = tape p_e ∧
      (∀ i : ℤ, p_e + 1 + (j : ℤ) < i → cfg'.tape i = tape i))) := by
  by_cases hvj_bool : v_j
  · -- 减路径（v_j = true）：状态 5→6→7→10→减2^j→12→13→5
    have hvj' : tape (p_e + 1 + (j : ℤ)) = Sym.data1 := by simpa [hvj_bool] using hvj
    have hp_t_lt : p_t + (ebits.length : ℤ) < p_e := boundary_after_target ebits.length j p_t p_e tape tbits hlen_le hj (by omega) htarget hbound
    have hne_pe : p_e ≠ p_t + (j : ℤ) := by omega
    have hne_pe1 : p_e - 1 ≠ p_t + (j : ℤ) := by omega
    let r5 : SymTransResult := { nextState := 76, writeSym := Sym.consumed, moveDir := Dir.L }
    let step5 : SymStep := { fromState := 5, readSym := Sym.data1, result := r5 }
    have htrans5 : step5.result ∈ VerifierSym.transition (5, tape (p_e + 1 + (j : ℤ))) := by
      rw [hvj']
      decide
    let tape1 : ℤ → Sym := fun i => if i = p_e + 1 + (j : ℤ) then Sym.consumed else tape i
    have hstep5 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) [step5]
        (symStepConfig (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) step5.result) := by
      refine SymSteps.cons [] step5 (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) SymSteps.nil ?_ ?_ ?_
      · rfl
      · change Sym.data1 = tape (p_e + 1 + (j : ℤ))
        rw [hvj']
      · change step5.result ∈ VerifierSym.transition (5, tape (p_e + 1 + (j : ℤ)))
        rw [hvj']
        decide
    have hcfg5 : symStepConfig (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) step5.result =
        SymConfig.mk 76 tape1 (p_e + (j : ℤ)) := by
      simp [symStepConfig, SymConfig.mk, step5, r5, tape1, Dir.toInt]
      omega
    -- 2. 状态 76 左移 j+1 格到 #₀
    have hnb6 : ∀ i : ℤ, p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ) < i ∧ i ≤ p_e + (j : ℤ) →
        (tape1 i).1 = SymKind.consumed ∨ (tape1 i).1 = SymKind.data0 ∨ (tape1 i).1 = SymKind.data1 := by
      intro i h
      have hi : p_e ≤ i ∧ i ≤ p_e + (j : ℤ) := by constructor <;> omega
      by_cases heq : i = p_e
      · subst i
        rw [show tape1 p_e = tape p_e from by simp [tape1]; intro h; omega]
        rcases hsel with hd | hd
        · right; left; simpa using hd
        · right; right; simpa using hd
      · have ioff : ∃ io : ℕ, (io : ℤ) = i - (p_e + 1) := by
          refine ⟨(i - (p_e + 1)).toNat, ?_⟩
          exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p_e + 1))
        rcases ioff with ⟨io, hio⟩
        have hio_le : io ≤ j := by omega
        by_cases heqio : io = j
        · subst io
          have hidx : i = p_e + 1 + (j : ℤ) := by omega
          rw [hidx]
          simp [tape1]
          left
          rfl
        · have hio_lt : io < j := by omega
          have ht := helem_pre io hio_lt
          have hidx : p_e + 1 + (io : ℤ) = i := by omega
          have ht' : tape i = Sym.consumed := by
            rw [hidx] at ht
            exact ht
          rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
          rw [ht']
          decide
    have hbound6 : tape1 (p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ)) = Sym.boundary := by
      have hpos : p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ) = p_e - 1 := by omega
      rw [hpos]
      rw [show tape1 (p_e - 1) = tape (p_e - 1) from by simp [tape1]; intro h; omega]
      exact hbound
    have hend6 : { nextState := 77, writeSym := Sym.boundary, moveDir := Dir.L } ∈ VerifierSym.transition (76, Sym.boundary) := by decide
    have hkeep6 : ∀ s : Sym, s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 →
        { nextState := 76, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (76, s) := trans76_keep
    rcases scanLeftKeepP 76 77 Sym.boundary Dir.L (j + 1) (p_e + (j : ℤ)) tape1
        (fun s => s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) hnb6 hbound6 hkeep6 hend6 rfl
      with ⟨π6, cfg6, hπ6, hs6, hhead6, htape6⟩
    -- 3. 状态 7 左移 (p_e - p_t - 1) 格到 #ₗ
    let n7 : ℕ := (p_e - p_t - 1).toNat
    have hn7 : (n7 : ℤ) = p_e - p_t - 1 := by
      change ((p_e - p_t - 1).toNat : ℤ) = p_e - p_t - 1
      exact Int.toNat_of_nonneg (by omega : 0 ≤ p_e - p_t - 1)
    have hnb7 : ∀ i : ℤ, (p_e - 2) - (n7 : ℤ) < i ∧ i ≤ p_e - 2 → (tape1 i).1 = SymKind.data0 ∨ (tape1 i).1 = SymKind.data1 := by
      intro i h
      rw [hn7] at h
      have hi : p_t ≤ i ∧ i < p_e - 1 := by constructor <;> omega
      by_cases hlt_target : i < p_t + (tbits.length : ℤ)
      · -- target 位
        have ioff : ∃ io : ℕ, (io : ℤ) = i - p_t := by
          refine ⟨(i - p_t).toNat, ?_⟩
          exact Int.toNat_of_nonneg (by omega : 0 ≤ i - p_t)
        rcases ioff with ⟨io, hio⟩
        have hio_lt : io < (targetTape j tbits).length := by
          have hlen : (targetTape j tbits).length = tbits.length := by
            simp [targetTape_length]
          rw [hlen]
          omega
        have ht := htarget io hio_lt
        have hmem : (targetTape j tbits)[io] ∈ targetTape j tbits := List.getElem_mem hio_lt
        have hdata_io := targetTape_data j tbits ((targetTape j tbits)[io]) hmem
        have hidx : p_t + (io : ℤ) = i := by omega
        rw [hidx] at ht
        rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
        rw [ht]
        exact hdata_io
      · -- data0 填充
        have hpad_i := hpad i (by constructor <;> omega)
        rw [show tape1 i = tape i from by simp [tape1]; intro h'; omega]
        rw [hpad_i]
        decide
    have hbound7 : tape1 ((p_e - 2) - (n7 : ℤ)) = Sym.boundary := by
      have hpos : (p_e - 2) - (n7 : ℤ) = p_t - 1 := by rw [hn7]; omega
      rw [hpos]
      rw [show tape1 (p_t - 1) = tape (p_t - 1) from by simp [tape1]; intro h; omega]
      exact hhashL
    have hend7 : { nextState := 10, writeSym := Sym.boundary, moveDir := Dir.R } ∈ VerifierSym.transition (77, Sym.boundary) := by decide
    have hkeep7 : ∀ s : Sym, s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 →
        { nextState := 77, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (77, s) := trans77_keep
    rcases scanLeftKeepP 77 10 Sym.boundary Dir.R n7 (p_e - 2) tape1
        (fun s => s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) hnb7 hbound7 hkeep7 hend7 rfl
      with ⟨π7, cfg7, hπ7, hs7, hhead7, htape7⟩
    -- 4. 状态 10 右移 j 格（4F4.4 前缀）
    have hkeep10 : ∀ i : ℤ, p_t ≤ i ∧ i < p_t + (j : ℤ) → { nextState := 10, writeSym := tape1 i, moveDir := Dir.R } ∈ VerifierSym.transition (10, tape1 i) := by
      intro i h
      have hi : p_t ≤ i ∧ i < p_t + (ebits.length : ℤ) := by constructor <;> omega
      have ioff : ∃ io : ℕ, (io : ℤ) = i - p_t := by
        refine ⟨(i - p_t).toNat, ?_⟩
        exact Int.toNat_of_nonneg (by omega : 0 ≤ i - p_t)
      rcases ioff with ⟨io, hio⟩
      have hio_lt : io < (targetTape j tbits).length := by
        have hlen : (targetTape j tbits).length = tbits.length := by
          simp [targetTape_length]
        rw [hlen]
        omega
      have ht := htarget io hio_lt
      have hio_j : io < j := by omega
      have hio_tbits : io < tbits.length := by omega
      have hsym : (targetTape j tbits)[io] = (if tbits[io] then Sym.data1 true else Sym.data0 true) := by
        simp [targetTape, bitsToSym, hio_j, hio_tbits]
      have hidx : p_t + (io : ℤ) = i := by omega
      rw [hidx] at ht
      rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
      rw [ht, hsym]
      have hk : ((if tbits[io] then Sym.data1 true else Sym.data0 true).1 = SymKind.data0 ∨
          (if tbits[io] then Sym.data1 true else Sym.data0 true).1 = SymKind.data1) := by
        by_cases hb : tbits[io] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]
      exact trans10_marked (if tbits[io] then Sym.data1 true else Sym.data0 true) (by by_cases hb : tbits[io] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]) hk
    rcases scanRightKeep 10 j p_t tape1 hkeep10 with ⟨π10, cfg10, hπ10, hs10, hhead10, htape10⟩
    -- 5. 减 2^j：状态 10 读 t_j 减一
    by_cases hsub2 : 2 ^ j ≤ bitsValue tbits
    · -- 正常减法：target 足够（2^j ≤ T），借位不越界
      rcases subOne_drop_some_of_ge_pow tbits j hsub2 with ⟨b', hsub_drop⟩
      have hsub' : subOne (symToBits (bitsToSym (tbits.drop j))) = some b' := by
        simpa [symToBits_bitsToSym] using hsub_drop
      have htape_drop : tapeAgrees tape1 (p_t + (j : ℤ)) (bitsToSym (tbits.drop j)) := by
        have htarget_drop : tapeAgrees tape (p_t + (j : ℤ)) (bitsToSym (tbits.drop j)) := by
          have hsplit := (tapeAgrees_append tape p_t ((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true)) (bitsToSym (tbits.drop j))).mp (by simpa [targetTape] using htarget)
          have hoffset : p_t + (min j tbits.length : ℤ) = p_t + (j : ℤ) := by omega
          simpa [hoffset] using hsplit.2
        intro i hi
        have h := htarget_drop i hi
        rw [show tape1 (p_t + (j : ℤ) + (i : ℤ)) = tape (p_t + (j : ℤ) + (i : ℤ)) from by
          simp [tape1]
          intro h'
          have htbits_le : p_t + (tbits.length : ℤ) ≤ p_e - 1 := target_ends_before_pe ebits.length j p_t p_e tape tbits hlen_le hj (by omega) htarget hbound
          have hlen_drop : (bitsToSym (tbits.drop j)).length = tbits.length - j := by simp [bitsToSym, List.length_drop]
          have hlt_pe : p_t + (j : ℤ) + (i : ℤ) < p_e + 1 := by
            have : (i : ℕ) < tbits.length - j := by
              rw [hlen_drop] at hi
              exact hi
            omega
          omega]
        exact h
      rcases subtract_one_matches_subOne (bitsToSym (tbits.drop j)) b' (p_t + (j : ℤ)) tape1 hsub'
        (bitsToSym_data (tbits.drop j)) (bitsToSym_marks (tbits.drop j)) htape_drop
        with ⟨πsub, cfgsub, hπsub, hs_sub, hhead_sub, htape_sub, hleft_sub, hright_sub⟩
    -- 6. 状态 12 右移回元素区（穿 target 剩余 + #₀ + sel 到 v_0）
      let m := firstTrueIdx (tbits.drop j)
      let n : ℕ := (p_e - p_t - (j : ℤ) - (m : ℤ)).toNat
      let p' : ℤ := p_t + ((j + m + 1 : ℕ) : ℤ)
      have htbits_le : p_t + (tbits.length : ℤ) ≤ p_e - 1 := target_ends_before_pe ebits.length j p_t p_e tape tbits hlen_le hj (by omega) htarget hbound
      have hm_lt : m < tbits.length - j := by
        have htrue : true ∈ tbits.drop j := (subOne_some_iff_mem_true (tbits.drop j)).mp ⟨b', hsub_drop⟩
        have hlt := firstTrueIdx_lt_length_of_mem (tbits.drop j) htrue
        simpa [m, List.length_drop] using hlt
      have hn_n : (n : ℤ) = p_e - p_t - (j : ℤ) - (m : ℤ) := by
        change ((p_e - p_t - (j : ℤ) - (m : ℤ)).toNat : ℤ) = p_e - p_t - (j : ℤ) - (m : ℤ)
        exact Int.toNat_of_nonneg (by omega : 0 ≤ p_e - p_t - (j : ℤ) - (m : ℤ))
      have hhead_sub' : cfgsub.headPos = p' := by
        rw [hhead_sub]
        rw [symToBits_bitsToSym]
        simp only [p', m]
        push_cast
        ring
      have hp_n : p' + (n : ℤ) = p_e + 1 := by
        rw [hn_n]
        simp only [p']
        omega
      have hnc12 : ∀ i : ℤ, p' ≤ i ∧ i < p' + (n : ℤ) →
          (cfgsub.tape i).1 = SymKind.data0 ∨ (cfgsub.tape i).1 = SymKind.data1 ∨ (cfgsub.tape i).1 = SymKind.boundary := by
        intro i hi
        have hi_lt_pe : i < p_e + 1 := by
          have := hi.2
          rw [hp_n] at this
          exact this
        by_cases hlt_target : i < p_t + (tbits.length : ℤ)
        · -- target 剩余位（markFirst b' 部分）
          have ioff : ∃ io : ℕ, (io : ℤ) = i - (p_t + (j : ℤ)) := by
            refine ⟨(i - (p_t + (j : ℤ))).toNat, ?_⟩
            exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p_t + (j : ℤ)))
          rcases ioff with ⟨io, hio⟩
          have hio_lt : io < (markFirst b').length := by
            rw [markFirst_length]
            have hb'_len : b'.length = (tbits.drop j).length := subOne_length (tbits.drop j) b' hsub_drop
            rw [hb'_len, List.length_drop]
            omega
          have ht := htape_sub io hio_lt
          have hidx : p_t + (j : ℤ) + (io : ℤ) = i := by omega
          rw [hidx] at ht
          rw [ht]
          rcases markFirst_data b' ((markFirst b')[io]) (List.getElem_mem hio_lt) with hd0 | hd1
          · left
            exact hd0
          · right; left
            exact hd1
        · -- data0 填充 / #₀ / sel
          have hright_i : cfgsub.tape i = tape1 i := hright_sub i (by
            have hlen_drop : (bitsToSym (tbits.drop j)).length = tbits.length - j := by simp [bitsToSym, List.length_drop]
            omega)
          rw [hright_i]
          by_cases hpad_i : i < p_e - 1
          · -- data0 填充
            have h := hpad i (by constructor <;> omega)
            rw [show tape1 i = tape i from by simp [tape1]; intro h'; omega]
            rw [h]
            decide
          · -- i ∈ {p_e-1, p_e}
            by_cases hh0 : i = p_e - 1
            · rw [hh0]
              rw [show tape1 (p_e - 1) = tape (p_e - 1) from by simp [tape1]; intro h'; omega]
              rw [hbound]
              decide
            · have hi_pe : i = p_e := by omega
              rw [hi_pe]
              rw [show tape1 p_e = tape p_e from by simp [tape1]; intro h'; omega]
              rcases hsel with hd | hd
              · left; simpa using hd
              · right; left; simpa using hd
      have hcons12 : cfgsub.tape (p' + (n : ℤ)) = Sym.consumed := by
        rw [hp_n]
        have hright_v0 : cfgsub.tape (p_e + 1) = tape1 (p_e + 1) := hright_sub (p_e + 1) (by
          have hlen_drop : (bitsToSym (tbits.drop j)).length = tbits.length - j := by simp [bitsToSym, List.length_drop]
          rw [hlen_drop]
          omega)
        rw [hright_v0]
        by_cases hj0 : j = 0
        · subst j
          simp [tape1]
        · have h0lt : 0 < j := by omega
          have h := helem_pre 0 h0lt
          rw [show tape1 (p_e + 1) = tape (p_e + 1) from by simp [tape1]; intro h'; omega]
          simpa using h
      rcases scanRight81 n p' cfgsub.tape hnc12 hcons12 with ⟨π12, cfg12, hπ12, hs12, hhead12, htape12⟩
    -- 7. 状态 13 右移扫 consumed 到 v_{j+1}
      have hcons13 : ∀ i : ℤ, p_e + 2 ≤ i ∧ i < p_e + 2 + (j : ℤ) → cfgsub.tape i = Sym.consumed := by
        intro i hi
        have hright_i : cfgsub.tape i = tape1 i := hright_sub i (by
          have hlen_drop : (bitsToSym (tbits.drop j)).length = tbits.length - j := by simp [bitsToSym, List.length_drop]
          rw [hlen_drop]
          omega)
        rw [hright_i]
        have ioff : ∃ io : ℕ, (io : ℤ) = i - (p_e + 2) := by
          refine ⟨(i - (p_e + 2)).toNat, ?_⟩
          exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p_e + 2))
        rcases ioff with ⟨io, hio⟩
        have hio_lt : io < j := by omega
        have hidx : i = p_e + 1 + ((io + 1 : ℕ) : ℤ) := by omega
        rw [hidx]
        have hio1_le : io + 1 ≤ j := by omega
        by_cases hio1_eq : io + 1 = j
        · rw [hio1_eq]
          simp [tape1]
        · have hio1_lt : io + 1 < j := by omega
          have h := helem_pre (io + 1) hio1_lt
          rw [show tape1 (p_e + 1 + ((io + 1 : ℕ) : ℤ)) = tape (p_e + 1 + ((io + 1 : ℕ) : ℤ)) from by simp [tape1]; intro h'; omega]
          exact h
      rcases scanRight13_scan j (p_e + 2) cfgsub.tape hcons13 with ⟨π13, cfg13, hπ13, hs13, hhead13, htape13⟩
    -- 组装：target 区不变量
      have htarget_pre : tapeAgrees tape p_t ((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true)) := by
        have hsplit := (tapeAgrees_append tape p_t ((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true)) (bitsToSym (tbits.drop j))).mp (by simpa [targetTape] using htarget)
        exact hsplit.1
      have hcfgsub_pre : tapeAgrees cfgsub.tape p_t ((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true)) := by
        intro i hi
        have h := htarget_pre i hi
        have hlen : ((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true)).length = j := by
          simp [List.length_map, List.length_take, min_eq_left (by omega : j ≤ tbits.length)]
        rw [show cfgsub.tape (p_t + (i : ℤ)) = tape1 (p_t + (i : ℤ)) from hleft_sub (p_t + (i : ℤ)) (by omega)]
        rw [show tape1 (p_t + (i : ℤ)) = tape (p_t + (i : ℤ)) from by
          simp [tape1]
          intro h'
          have hi_lt : (i : ℤ) < (ebits.length : ℤ) := by omega
          omega]
        exact h
      have htarget_next_eq : targetTape (j + 1) ((subOneAt j tbits).getD tbits) =
          (tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true) ++ markFirst b' := by
        have hsubAt : subOneAt j tbits = some ((tbits.take j) ++ b') := by
          rw [subOneAt_eq_drop, hsub_drop]
          rfl
        have hgetD : (subOneAt j tbits).getD tbits = (tbits.take j) ++ b' := by
          rw [hsubAt]
          rfl
        rw [hgetD]
        exact targetTape_succ_append tbits j b' hsub_drop
      have hcfgsub_target : tapeAgrees cfgsub.tape p_t (targetTape (j + 1) ((subOneAt j tbits).getD tbits)) := by
        rw [htarget_next_eq]
        have hlen : ((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true)).length = j := by
          simp [List.length_map, List.length_take, min_eq_left (by omega : j ≤ tbits.length)]
        have hsub'' : tapeAgrees cfgsub.tape (p_t + (((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true)).length : ℤ)) (markFirst b') := by
          rw [hlen]
          exact htape_sub
        exact (tapeAgrees_append cfgsub.tape p_t ((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true)) (markFirst b')).mpr ⟨hcfgsub_pre, hsub''⟩
      have hcfgsub_cons : ∀ i : ℕ, i ≤ j → cfgsub.tape (p_e + 1 + (i : ℤ)) = Sym.consumed := by
        intro i hi
        have hright_i : cfgsub.tape (p_e + 1 + (i : ℤ)) = tape1 (p_e + 1 + (i : ℤ)) := hright_sub (p_e + 1 + (i : ℤ)) (by
          have hlen_drop : (bitsToSym (tbits.drop j)).length = tbits.length - j := by simp [bitsToSym, List.length_drop]
          rw [hlen_drop]
          omega)
        rw [hright_i]
        by_cases hij : i = j
        · subst i
          simp [tape1]
        · have hi_lt : i < j := by omega
          have h := helem_pre i hi_lt
          rw [show tape1 (p_e + 1 + (i : ℤ)) = tape (p_e + 1 + (i : ℤ)) from by simp [tape1]; intro h'; omega]
          exact h
      have hcfgsub_rest : tapeAgrees cfgsub.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) (bitsToSym (ebits.drop (j + 1))) := by
        intro i hi
        have h := helem_rest i hi
        have hright_i : cfgsub.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ)) = tape1 (p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ)) := hright_sub (p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ)) (by
          have hlen_drop : (bitsToSym (tbits.drop j)).length = tbits.length - j := by simp [bitsToSym, List.length_drop]
          rw [hlen_drop]
          omega)
        rw [hright_i]
        rw [show tape1 (p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ)) = tape (p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ)) from by
          simp [tape1]; intro h'; omega]
        exact h
    -- 组装路径
      have hstep5' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) [step5] (SymConfig.mk 76 tape1 (p_e + (j : ℤ))) := hcfg5 ▸ hstep5
      have h567 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6) cfg6 := SymSteps_trans _ _ _ _ [step5] π6 hstep5' hπ6
      have hhead6' : cfg6.headPos = p_e - 2 := by
        rw [hhead6]
        simp [Dir.toInt]
        omega
      have hcfg6_eq : cfg6 = SymConfig.mk 77 tape1 (p_e - 2) := by
        rw [← hs6, ← htape6, ← hhead6']
      have hπ7' : SymSteps VerifierSym.transition cfg6 π7 cfg7 := by
        rw [hcfg6_eq]; exact hπ7
      have h567' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6 ++ π7) cfg7 := SymSteps_trans _ _ _ _ ([step5] ++ π6) π7 h567 hπ7'
      have hhead7' : cfg7.headPos = p_t := by
        rw [hhead7]
        simp [Dir.toInt]
        omega
      have hcfg7_eq : cfg7 = SymConfig.mk 10 tape1 p_t := by
        rw [← hs7, ← htape7, ← hhead7']
      have hπ10' : SymSteps VerifierSym.transition cfg7 π10 cfg10 := by
        rw [hcfg7_eq]; exact hπ10
      have h567'' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6 ++ π7 ++ π10) cfg10 := SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7) π10 h567' hπ10'
      have hcfg10_eq : cfg10 = SymConfig.mk 10 tape1 (p_t + (j : ℤ)) := by
        rw [← hs10, ← htape10, ← hhead10]
      have hsub' : SymSteps VerifierSym.transition cfg10 πsub cfgsub := by
        rw [hcfg10_eq]; exact hπsub
      have h567''' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6 ++ π7 ++ π10 ++ πsub) cfgsub := SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7 ++ π10) πsub h567'' hsub'
      have hcfgsub_eq : cfgsub = SymConfig.mk 81 cfgsub.tape p' := by
        rw [← hs_sub, ← hhead_sub']
      have h12' : SymSteps VerifierSym.transition cfgsub π12 cfg12 := by
        rw [hcfgsub_eq]; exact hπ12
      have h567'''' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6 ++ π7 ++ π10 ++ πsub ++ π12) cfg12 := SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7 ++ π10 ++ πsub) π12 h567''' h12'
      have hhead12' : cfg12.headPos = p_e + 2 := by
        rw [hhead12]
        rw [hp_n]
        omega
      have hcfg12_eq : cfg12 = SymConfig.mk 13 cfgsub.tape (p_e + 2) := by
        rw [← hs12, ← htape12, ← hhead12']
      have h13' : SymSteps VerifierSym.transition cfg12 π13 cfg13 := by
        rw [hcfg12_eq]; exact hπ13
      have htotal : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6 ++ π7 ++ π10 ++ πsub ++ π12 ++ π13) cfg13 := SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7 ++ π10 ++ πsub ++ π12) π13 h567'''' h13'
      refine ⟨[step5] ++ π6 ++ π7 ++ π10 ++ πsub ++ π12 ++ π13, cfg13, htotal, Or.inl ⟨hs13, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · simpa [add_assoc, add_comm, add_left_comm] using hhead13
      · rw [htape13, hvj_bool]
        exact hcfgsub_target
      · intro i hi
        rw [htape13]
        exact hcfgsub_cons i hi
      · rw [htape13]
        exact hcfgsub_rest
      · rw [htape13]
        rw [hright_sub p_e (by
          have hlen : (bitsToSym (tbits.drop j)).length = tbits.length - j := by simp [bitsToSym, List.length_drop]
          rw [hlen]
          omega)]
        rw [show tape1 p_e = tape p_e from by simp [tape1]; intro h; omega]
        exact hsel
      · rw [htape13]
        rw [hleft_sub (p_t - 1) (by omega)]
        rw [show tape1 (p_t - 1) = tape (p_t - 1) from by simp [tape1]; intro h; omega]
        exact hhashL
      · rw [htape13]
        rw [hright_sub (p_e - 1) (by
          have hlen : (bitsToSym (tbits.drop j)).length = tbits.length - j := by simp [bitsToSym, List.length_drop]
          rw [hlen]
          omega)]
        rw [show tape1 (p_e - 1) = tape (p_e - 1) from by simp [tape1]; intro h; omega]
        exact hbound
      · rw [htape13]
        rw [hright_sub (p_e + 1 + (ebits.length : ℤ)) (by
          have hlen : (bitsToSym (tbits.drop j)).length = tbits.length - j := by simp [bitsToSym, List.length_drop]
          rw [hlen]
          omega)]
        rw [show tape1 (p_e + 1 + (ebits.length : ℤ)) = tape (p_e + 1 + (ebits.length : ℤ)) from by
          simp [tape1]; intro h; omega]
      · rw [htape13]
        rw [hright_sub p_e (by
          have hlen : (bitsToSym (tbits.drop j)).length = tbits.length - j := by simp [bitsToSym, List.length_drop]
          rw [hlen]
          omega)]
        rw [show tape1 p_e = tape p_e from by simp [tape1]; intro h; omega]
      · intro i hi
        rw [htape13]
        rw [hright_sub i (by
          have hjle : j ≤ tbits.length := le_trans (Nat.le_of_lt hj) hlen_le
          have hsum : j + (tbits.length - j) = tbits.length := Nat.add_sub_of_le hjle
          have hz : (p_t : ℤ) + (j : ℤ) + ((tbits.length - j : ℕ) : ℤ) ≤ (p_t : ℤ) + (tbits.length : ℤ) := by
            rw [add_assoc]
            rw [← Nat.cast_add]
            rw [hsum]
          have hlen : (bitsToSym (tbits.drop j)).length = tbits.length - j := by
            simp [bitsToSym, List.length_drop]
          rw [hlen]
          omega)]
        rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
        exact hpad i (by omega)
      · intro i hi
        rw [htape13]
        rw [hright_sub i (by
          have hjle : j ≤ tbits.length := le_trans (Nat.le_of_lt hj) hlen_le
          have hsum : j + (tbits.length - j) = tbits.length := Nat.add_sub_of_le hjle
          have hz : (p_t : ℤ) + (j : ℤ) + ((tbits.length - j : ℕ) : ℤ) ≤ (p_t : ℤ) + (tbits.length : ℤ) := by
            rw [add_assoc]
            rw [← Nat.cast_add]
            rw [hsum]
          have hlen : (bitsToSym (tbits.drop j)).length = tbits.length - j := by simp [bitsToSym, List.length_drop]
          rw [hlen]
          omega)]
        rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
    · -- 借位越界（2^j > T）：target 不足——状态 5→76→77→10→11→14→…→101（拒绝路径）
      have hlt2 : bitsValue tbits < 2 ^ j := lt_of_not_ge hsub2
      -- [j, L) 段全 false（否则 2^j ≤ T）
      have hall_false : ∀ io : ℕ, j ≤ io → (hlt : io < tbits.length) → tbits[io]'(hlt) = false := by
        intro io hge hlt
        by_contra h
        have htrue : tbits[io] = true := by
          cases hb : tbits[io] <;> simp [hb] at h ⊢
        have hpow : 2 ^ io ≤ bitsValue tbits := bitsValue_ge_pow_of_getElem_true tbits io hlt htrue
        have hge2 : 2 ^ j ≤ 2 ^ io := pow_le_pow_right₀ (by norm_num) hge
        omega
      have hj' : j < tbits.length := by omega
      have htbits_j : tbits[j] = false := hall_false j (by omega) hj'
      -- t_j 处带 = data0（m=0）
      have htape_tj : tape1 (p_t + (j : ℤ)) = Sym.data0 := by
        rw [show tape1 (p_t + (j : ℤ)) = tape (p_t + (j : ℤ)) from by simp [tape1]; intro h'; omega]
        have h := htarget j (by simpa [targetTape_length] using hj')
        have hget : (targetTape j tbits)[j]'(by simpa [targetTape_length] using hj') = Sym.data0 := by
          rw [targetTape_getElem_ge j j tbits hj' le_rfl]
          simp [htbits_j]
        rw [hget] at h
        exact h
      -- 状态 10 读 t_j（data0 m=0）→ 11（写 data0 m=1 标 m）
      let r10tj : SymTransResult := { nextState := 11, writeSym := Sym.data0 true, moveDir := Dir.S }
      let step10tj : SymStep := { fromState := 10, readSym := Sym.data0, result := r10tj }
      have htrans10tj : step10tj.result ∈ VerifierSym.transition (10, tape1 (p_t + (j : ℤ))) := by
        rw [htape_tj]
        simp [step10tj, r10tj]
        decide
      have hstep10tj : SymSteps VerifierSym.transition (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) [step10tj]
          (symStepConfig (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) step10tj.result) := by
        refine SymSteps.cons [] step10tj (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) SymSteps.nil ?_ ?_ ?_
        · rfl
        · dsimp [step10tj]
          rw [htape_tj]
        · change step10tj.result ∈ VerifierSym.transition (10, tape1 (p_t + (j : ℤ)))
          exact htrans10tj
      let tape2 : ℤ → Sym := fun i => if i = p_t + (j : ℤ) then Sym.data0 true else tape1 i
      have hcfg10tj : symStepConfig (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) step10tj.result =
          SymConfig.mk 11 tape2 (p_t + (j : ℤ)) := by
        simp [symStepConfig, SymConfig.mk, step10tj, r10tj, tape2, Dir.toInt]
      -- 状态 11 读（data0 m=1）→ 14（借位写 data1 m=1）
      let r11 : SymTransResult := { nextState := 14, writeSym := Sym.data1 true, moveDir := Dir.R }
      let step11 : SymStep := { fromState := 11, readSym := Sym.data0 true, result := r11 }
      have htrans11 : step11.result ∈ VerifierSym.transition (11, Sym.data0 true) := by
        simp [step11, r11]
        decide
      have hstep11 : SymSteps VerifierSym.transition (SymConfig.mk 11 tape2 (p_t + (j : ℤ))) [step11]
          (symStepConfig (SymConfig.mk 11 tape2 (p_t + (j : ℤ))) step11.result) := by
        refine SymSteps.cons [] step11 (SymConfig.mk 11 tape2 (p_t + (j : ℤ))) SymSteps.nil ?_ ?_ ?_
        · rfl
        · dsimp [step11, tape2]
          simp
        · change step11.result ∈ VerifierSym.transition (11, tape2 (p_t + (j : ℤ)))
          simp [tape2]
          exact htrans11
      let tape3 : ℤ → Sym := fun i => if i = p_t + (j : ℤ) then Sym.data1 true else tape2 i
      have hcfg11 : symStepConfig (SymConfig.mk 11 tape2 (p_t + (j : ℤ))) step11.result =
          SymConfig.mk 14 tape3 (p_t + (j : ℤ) + 1) := by
        simp [symStepConfig, SymConfig.mk, step11, r11, tape3, Dir.toInt]
      -- 状态 14 借位传播：从 p_t + j + 1 到 #₀（p_e - 1）全 data0 → 101
      let n : ℕ := (p_e - 1 - (p_t + (j : ℤ) + 1)).toNat
      have hn_n : (n : ℤ) = p_e - 1 - (p_t + (j : ℤ) + 1) := by
        change ((p_e - 1 - (p_t + (j : ℤ) + 1)).toNat : ℤ) = p_e - 1 - (p_t + (j : ℤ) + 1)
        exact Int.toNat_of_nonneg (by omega : 0 ≤ p_e - 1 - (p_t + (j : ℤ) + 1))
      have huf_tape : ∀ i : ℕ, i < n → tape3 (p_t + (j : ℤ) + 1 + (i : ℤ)) = Sym.data0 := by
        intro i hi
        have hx_lt : p_t + (j : ℤ) + 1 + (i : ℤ) < p_e - 1 := by
          have hz : (i : ℤ) < (n : ℤ) := by exact_mod_cast hi
          rw [hn_n] at hz
          omega
        have hne1 : p_t + (j : ℤ) + 1 + (i : ℤ) ≠ p_t + (j : ℤ) := by omega
        simp [tape3, tape2, hne1]
        rw [show tape1 (p_t + (j : ℤ) + 1 + (i : ℤ)) = tape (p_t + (j : ℤ) + 1 + (i : ℤ)) from by
          simp [tape1]; intro h'; omega]
        by_cases hlt : p_t + (j : ℤ) + 1 + (i : ℤ) < p_t + (tbits.length : ℤ)
        · -- target 高位段（[j+1, L) 全 false → data0）
          have ioff : ∃ io : ℕ, (io : ℤ) = p_t + (j : ℤ) + 1 + (i : ℤ) - p_t := by
            refine ⟨(p_t + (j : ℤ) + 1 + (i : ℤ) - p_t).toNat, ?_⟩
            change ((p_t + (j : ℤ) + 1 + (i : ℤ) - p_t).toNat : ℤ) = p_t + (j : ℤ) + 1 + (i : ℤ) - p_t
            exact Int.toNat_of_nonneg (by omega)
          rcases ioff with ⟨io, hio⟩
          have hio_lt : io < (targetTape j tbits).length := by
            have hlen : (targetTape j tbits).length = tbits.length := by simp [targetTape_length]
            rw [hlen]
            omega
          have ht := htarget io hio_lt
          have hio_ge : j < io := by omega
          have hio_lt_L : io < tbits.length := by omega
          have hbits_false : tbits[io] = false := hall_false io (Nat.le_of_lt hio_ge) hio_lt_L
          have hsym : (targetTape j tbits)[io] = Sym.data0 := by
            rw [targetTape_getElem_ge j io tbits hio_lt_L (Nat.le_of_lt hio_ge)]
            simp [hbits_false]
          have hidx : p_t + (io : ℤ) = p_t + (j : ℤ) + 1 + (i : ℤ) := by omega
          rw [hidx] at ht
          rw [ht, hsym]
        · -- 填充区（hpad）
          have hpad_i := hpad (p_t + (j : ℤ) + 1 + (i : ℤ)) (by constructor <;> omega)
          rw [hpad_i]
      have huf_bound : tape3 (p_t + (j : ℤ) + 1 + (n : ℤ)) = Sym.boundary := by
        rw [hn_n]
        have hpos : p_t + (j : ℤ) + 1 + (p_e - 1 - (p_t + (j : ℤ) + 1)) = p_e - 1 := by omega
        rw [hpos]
        simp [tape3, tape2, show p_e - 1 ≠ p_t + (j : ℤ) from by omega]
        rw [show tape1 (p_e - 1) = tape (p_e - 1) from by simp [tape1]; intro h; omega]
        exact hbound
      rcases underflow_scan_to_boundary (p_t + (j : ℤ) + 1) n tape3 huf_tape huf_bound
        with ⟨πuf, cfguf, hπuf, hsuf, hheaduf, hdata1uf, hbounduf, hleftuf, hrightuf⟩
      -- 拼链：5 → 76 → 77 → 10 → 11 → 14 → … → 101
      have hstep5' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) [step5] (SymConfig.mk 76 tape1 (p_e + (j : ℤ))) := hcfg5 ▸ hstep5
      have h567 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6) cfg6 := SymSteps_trans _ _ _ _ [step5] π6 hstep5' hπ6
      have hcfg6_eq : cfg6 = SymConfig.mk 77 tape1 (p_e - 2) := by
        cases cfg6 with
        | mk state tape headPos =>
            change state = 77 at hs6
            change tape = tape1 at htape6
            rw [hs6, htape6]
            congr 1
            change headPos = (p_e + (j : ℤ)) - ((j + 1 : ℕ) : ℤ) + Dir.L.toInt at hhead6
            rw [hhead6]
            simp [Dir.toInt]
            omega
      have hπ7' : SymSteps VerifierSym.transition cfg6 π7 cfg7 := by
        rw [hcfg6_eq]; exact hπ7
      have h567' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6 ++ π7) cfg7 := SymSteps_trans _ _ _ _ ([step5] ++ π6) π7 h567 hπ7'
      have hcfg7_eq : cfg7 = SymConfig.mk 10 tape1 p_t := by
        cases cfg7 with
        | mk state tape headPos =>
            change state = 10 at hs7
            change tape = tape1 at htape7
            rw [hs7, htape7]
            congr 1
            change headPos = (p_e - 2) - (n7 : ℤ) + Dir.R.toInt at hhead7
            rw [hhead7]
            simp [hn7, Dir.toInt]
            omega
      have hπ10' : SymSteps VerifierSym.transition cfg7 π10 cfg10 := by
        rw [hcfg7_eq]; exact hπ10
      have h567'' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6 ++ π7 ++ π10) cfg10 := SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7) π10 h567' hπ10'
      have hcfg10_eq : cfg10 = SymConfig.mk 10 tape1 (p_t + (j : ℤ)) := by
        cases cfg10 with
        | mk state tape headPos =>
            change state = 10 at hs10
            change tape = tape1 at htape10
            change headPos = p_t + (j : ℤ) at hhead10
            rw [hs10, htape10, hhead10]
      have h10tj' : SymSteps VerifierSym.transition cfg10 [step10tj]
          (symStepConfig (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) step10tj.result) := by
        rw [hcfg10_eq]
        exact hstep10tj
      have h567''' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ)))
          ([step5] ++ π6 ++ π7 ++ π10 ++ [step10tj])
          (symStepConfig (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) step10tj.result) :=
        SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7 ++ π10) [step10tj] h567'' h10tj'
      have h11' : SymSteps VerifierSym.transition (symStepConfig (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) step10tj.result) [step11]
          (symStepConfig (SymConfig.mk 11 tape2 (p_t + (j : ℤ))) step11.result) := by
        rw [hcfg10tj]
        exact hstep11
      have h567'''' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ)))
          ([step5] ++ π6 ++ π7 ++ π10 ++ [step10tj] ++ [step11])
          (symStepConfig (SymConfig.mk 11 tape2 (p_t + (j : ℤ))) step11.result) :=
        SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7 ++ π10 ++ [step10tj]) [step11] h567''' h11'
      have h14' : SymSteps VerifierSym.transition (symStepConfig (SymConfig.mk 11 tape2 (p_t + (j : ℤ))) step11.result) πuf cfguf := by
        rw [hcfg11]
        exact hπuf
      have htotal : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ)))
          ([step5] ++ π6 ++ π7 ++ π10 ++ [step10tj] ++ [step11] ++ πuf) cfguf :=
        SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7 ++ π10 ++ [step10tj] ++ [step11]) πuf h567'''' h14'
      -- 结论（101 分支）
      have hhead_uf : cfguf.headPos = p_e := by
        rw [hheaduf]
        rw [hn_n]
        omega
      have hdata1' : ∀ i : ℤ, p_t + (j : ℤ) ≤ i ∧ i < p_e - 1 → (cfguf.tape i).1 = SymKind.data1 := by
        intro i hi
        by_cases heq : i = p_t + (j : ℤ)
        · subst i
          have hl := hleftuf (p_t + (j : ℤ)) (by omega)
          rw [hl]
          simp [tape3, Sym.data1]
        · have hio : ∃ io : ℕ, (io : ℤ) = i - (p_t + (j : ℤ) + 1) := by
            refine ⟨(i - (p_t + (j : ℤ) + 1)).toNat, ?_⟩
            change ((i - (p_t + (j : ℤ) + 1)).toNat : ℤ) = i - (p_t + (j : ℤ) + 1)
            exact Int.toNat_of_nonneg (by omega)
          rcases hio with ⟨io, hio⟩
          have hio_lt : io < n := by
            have hz : (io : ℤ) < (n : ℤ) := by
              rw [hio]
              rw [hn_n]
              omega
            exact_mod_cast hz
          have hd := hdata1uf io hio_lt
          have hidx : i = p_t + (j : ℤ) + 1 + (io : ℤ) := by omega
          rw [hidx, hd]
          simp
      have hcons' : ∀ i : ℕ, i ≤ j → cfguf.tape (p_e + 1 + (i : ℤ)) = Sym.consumed := by
        intro i hi
        have hr := hrightuf (p_e + 1 + (i : ℤ)) (by omega)
        rw [hr]
        simp [tape3, tape2, show p_e + 1 + (i : ℤ) ≠ p_t + (j : ℤ) from by omega]
        by_cases heq : i = j
        · subst i
          simp [tape1]
        · have hpre := helem_pre i (by omega)
          rw [show tape1 (p_e + 1 + (i : ℤ)) = tape (p_e + 1 + (i : ℤ)) from by simp [tape1]; intro h'; omega]
          exact hpre
      have hhashL' : cfguf.tape (p_t - 1) = Sym.boundary := by
        have hl := hleftuf (p_t - 1) (by omega)
        rw [hl]
        simp [tape3, tape2, show p_t - 1 ≠ p_t + (j : ℤ) from by omega]
        rw [show tape1 (p_t - 1) = tape (p_t - 1) from by simp [tape1]; intro h; omega]
        exact hhashL
      have hkeep_pe : cfguf.tape p_e = tape p_e := by
        have hr := hrightuf p_e (by omega)
        rw [hr]
        simp [tape3, tape2, show p_e ≠ p_t + (j : ℤ) from by omega]
        rw [show tape1 p_e = tape p_e from by simp [tape1]; intro h; omega]
      have hbound_pe : cfguf.tape (p_e - 1) = Sym.boundary := by
        rw [show p_e - 1 = p_t + (j : ℤ) + 1 + (n : ℤ) from by rw [hn_n]; omega]
        exact hbounduf
      have hright' : ∀ i : ℤ, p_e + 1 + (j : ℤ) < i → cfguf.tape i = tape i := by
        intro i hi
        have hr := hrightuf i (by omega)
        rw [hr]
        have hne : i ≠ p_t + (j : ℤ) := by omega
        simp [tape3, tape2, hne]
        rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
      refine ⟨[step5] ++ π6 ++ π7 ++ π10 ++ [step10tj] ++ [step11] ++ πuf, cfguf, htotal,
        Or.inr ⟨hsuf, hhead_uf, hvj_bool, hlt2, hdata1', hbound_pe, hcons', hhashL', hkeep_pe, hright'⟩⟩
  · -- 标记路径（v_j = false）：状态 5→8→9→11→12→13→5
    have hvj' : tape (p_e + 1 + (j : ℤ)) = Sym.data0 := by simpa [hvj_bool] using hvj
    have hp_t_lt : p_t + (ebits.length : ℤ) < p_e := boundary_after_target ebits.length j p_t p_e tape tbits hlen_le hj (by omega) htarget hbound
    have hne_pe : p_e ≠ p_t + (j : ℤ) := by omega
    have hne_pe1 : p_e - 1 ≠ p_t + (j : ℤ) := by omega
    let r5 : SymTransResult := { nextState := 8, writeSym := Sym.consumed, moveDir := Dir.L }
    let step5 : SymStep := { fromState := 5, readSym := Sym.data0, result := r5 }
    have htrans5 : step5.result ∈ VerifierSym.transition (5, tape (p_e + 1 + (j : ℤ))) := by
      rw [hvj']
      decide
    let tape1 : ℤ → Sym := fun i => if i = p_e + 1 + (j : ℤ) then Sym.consumed else tape i
    have hstep5 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) [step5]
        (symStepConfig (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) step5.result) := by
      refine SymSteps.cons [] step5 (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) SymSteps.nil ?_ ?_ ?_
      · rfl
      · change Sym.data0 = tape (p_e + 1 + (j : ℤ))
        rw [hvj']
      · change step5.result ∈ VerifierSym.transition (5, tape (p_e + 1 + (j : ℤ)))
        rw [hvj']
        decide
    have hcfg5 : symStepConfig (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) step5.result =
        SymConfig.mk 8 tape1 (p_e + (j : ℤ)) := by
      simp [symStepConfig, SymConfig.mk, step5, r5, tape1, Dir.toInt]
      omega
    -- 状态 8 左移 j+1 格到 #₀
    have hnb8 : ∀ i : ℤ, p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ) < i ∧ i ≤ p_e + (j : ℤ) →
        (tape1 i).1 = SymKind.consumed ∨ (tape1 i).1 = SymKind.data0 ∨ (tape1 i).1 = SymKind.data1 := by
      intro i h
      have hi : p_e ≤ i ∧ i ≤ p_e + (j : ℤ) := by constructor <;> omega
      by_cases heq : i = p_e
      · subst i
        rw [show tape1 p_e = tape p_e from by simp [tape1]; intro h; omega]
        rcases hsel with hd | hd
        · right; left; simpa using hd
        · right; right; simpa using hd
      · have ioff : ∃ io : ℕ, (io : ℤ) = i - (p_e + 1) := by
          refine ⟨(i - (p_e + 1)).toNat, ?_⟩
          exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p_e + 1))
        rcases ioff with ⟨io, hio⟩
        have hio_le : io ≤ j := by omega
        by_cases heqio : io = j
        · subst io
          have hidx : i = p_e + 1 + (j : ℤ) := by omega
          rw [hidx]
          simp [tape1]
          left
          rfl
        · have hio_lt : io < j := by omega
          have ht := helem_pre io hio_lt
          have hidx : p_e + 1 + (io : ℤ) = i := by omega
          have ht' : tape i = Sym.consumed := by
            rw [hidx] at ht
            exact ht
          rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
          rw [ht']
          decide
    have hbound8 : tape1 (p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ)) = Sym.boundary := by
      have hpos : p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ) = p_e - 1 := by omega
      rw [hpos]
      rw [show tape1 (p_e - 1) = tape (p_e - 1) from by simp [tape1]; intro h; omega]
      exact hbound
    have hend8 : { nextState := 9, writeSym := Sym.boundary, moveDir := Dir.L } ∈ VerifierSym.transition (8, Sym.boundary) := by decide
    have hkeep8 : ∀ s : Sym, s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 →
        { nextState := 8, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (8, s) := trans8_keep
    rcases scanLeftKeepP 8 9 Sym.boundary Dir.L (j + 1) (p_e + (j : ℤ)) tape1
        (fun s => s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) hnb8 hbound8 hkeep8 hend8 rfl
      with ⟨π8, cfg8, hπ8, hs8, hhead8, htape8⟩
    -- 状态 9 左移 (p_e - p_t - 1) 格到 #ₗ
    let n9 : ℕ := (p_e - p_t - 1).toNat
    have hn9 : (n9 : ℤ) = p_e - p_t - 1 := by
      change ((p_e - p_t - 1).toNat : ℤ) = p_e - p_t - 1
      exact Int.toNat_of_nonneg (by omega : 0 ≤ p_e - p_t - 1)
    have hnb9 : ∀ i : ℤ, (p_e - 2) - (n9 : ℤ) < i ∧ i ≤ p_e - 2 → (tape1 i).1 = SymKind.data0 ∨ (tape1 i).1 = SymKind.data1 := by
      intro i h
      rw [hn9] at h
      have hi : p_t ≤ i ∧ i < p_e - 1 := by constructor <;> omega
      by_cases hlt_target : i < p_t + (ebits.length : ℤ)
      · -- target 位
        have ioff : ∃ io : ℕ, (io : ℤ) = i - p_t := by
          refine ⟨(i - p_t).toNat, ?_⟩
          exact Int.toNat_of_nonneg (by omega : 0 ≤ i - p_t)
        rcases ioff with ⟨io, hio⟩
        have hio_lt : io < (targetTape j tbits).length := by
          have hlen : (targetTape j tbits).length = tbits.length := by
            simp [targetTape_length]
          rw [hlen]
          omega
        have ht := htarget io hio_lt
        have hmem : (targetTape j tbits)[io] ∈ targetTape j tbits := List.getElem_mem hio_lt
        have hdata_io := targetTape_data j tbits ((targetTape j tbits)[io]) hmem
        have hidx : p_t + (io : ℤ) = i := by omega
        rw [hidx] at ht
        rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
        rw [ht]
        exact hdata_io
      · -- target 高位（t_k 到 t_{L-1}）或 data0 填充
        by_cases hlt_L : i < p_t + (tbits.length : ℤ)
        · -- target 高位：data0/1
          have ioff : ∃ io : ℕ, (io : ℤ) = i - p_t := by
            refine ⟨(i - p_t).toNat, ?_⟩
            exact Int.toNat_of_nonneg (by omega : 0 ≤ i - p_t)
          rcases ioff with ⟨io, hio⟩
          have hio_gt : j < io := by omega
          have hio_lt : io < (targetTape j tbits).length := by
            have hlen : (targetTape j tbits).length = tbits.length := by
              simp [targetTape_length]
            rw [hlen]
            omega
          have ht := htarget io hio_lt
          have hio_tbits : io < tbits.length := by omega
          have hsym : (targetTape j tbits)[io]'(by simpa using hio_tbits) = (if tbits[io] then Sym.data1 else Sym.data0) := by
            exact targetTape_getElem_ge j io tbits hio_tbits (Nat.le_of_lt hio_gt)
          have hnb : ((if tbits[io] then Sym.data1 else Sym.data0).1 = SymKind.data0 ∨
              (if tbits[io] then Sym.data1 else Sym.data0).1 = SymKind.data1) := by
            by_cases hb : tbits[io] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]
          have hidx : p_t + (io : ℤ) = i := by omega
          rw [hidx] at ht
          rw [show tape1 i = tape i from by simp [tape1]; intro h'; omega]
          rw [ht, hsym]
          rcases hnb with hd | hd
          · left; simpa using hd
          · right; simpa using hd
        · -- data0 填充
          have hpad_i := hpad i (by constructor <;> omega)
          rw [show tape1 i = tape i from by simp [tape1]; intro h'; omega]
          rw [hpad_i]
          decide
    have hbound9 : tape1 ((p_e - 2) - (n9 : ℤ)) = Sym.boundary := by
      have hpos : (p_e - 2) - (n9 : ℤ) = p_t - 1 := by rw [hn9]; omega
      rw [hpos]
      rw [show tape1 (p_t - 1) = tape (p_t - 1) from by simp [tape1]; intro h; omega]
      exact hhashL
    have hend9 : { nextState := 12, writeSym := Sym.boundary, moveDir := Dir.R } ∈ VerifierSym.transition (9, Sym.boundary) := by decide
    have hkeep9 : ∀ s : Sym, s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 →
        { nextState := 9, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (9, s) := trans9_keep
    rcases scanLeftKeepP 9 12 Sym.boundary Dir.R n9 (p_e - 2) tape1
        (fun s => s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) hnb9 hbound9 hkeep9 hend9 rfl
      with ⟨π9, cfg9, hπ9, hs9, hhead9, htape9⟩
    -- 状态 12 右移 j 格扫 4F4.4 前缀
    have hkeep11 : ∀ i : ℤ, p_t ≤ i ∧ i < p_t + (j : ℤ) → { nextState := 12, writeSym := tape1 i, moveDir := Dir.R } ∈ VerifierSym.transition (12, tape1 i) := by
      intro i h
      have hi : p_t ≤ i ∧ i < p_t + (ebits.length : ℤ) := by constructor <;> omega
      have ioff : ∃ io : ℕ, (io : ℤ) = i - p_t := by
        refine ⟨(i - p_t).toNat, ?_⟩
        exact Int.toNat_of_nonneg (by omega : 0 ≤ i - p_t)
      rcases ioff with ⟨io, hio⟩
      have hio_lt : io < (targetTape j tbits).length := by
        have hlen : (targetTape j tbits).length = tbits.length := by
          simp [targetTape_length]
        rw [hlen]
        omega
      have ht := htarget io hio_lt
      have hio_j : io < j := by omega
      have hio_tbits : io < tbits.length := by omega
      have hsym : (targetTape j tbits)[io] = (if tbits[io] then Sym.data1 true else Sym.data0 true) := by
        simp [targetTape, bitsToSym, hio_j, hio_tbits]
      have hidx : p_t + (io : ℤ) = i := by omega
      rw [hidx] at ht
      rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
      rw [ht, hsym]
      have hk : ((if tbits[io] then Sym.data1 true else Sym.data0 true).1 = SymKind.data0 ∨
          (if tbits[io] then Sym.data1 true else Sym.data0 true).1 = SymKind.data1) := by
        by_cases hb : tbits[io] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]
      exact trans12_marked (if tbits[io] then Sym.data1 true else Sym.data0 true) (by by_cases hb : tbits[io] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]) hk
    rcases scanRightKeep 12 j p_t tape1 hkeep11 with ⟨π11, cfg11, hπ11, hs11, hhead11, htape11⟩
    -- 状态 12 读 t_j（m=0），置 m=1 转 81
    have htape_tj : tape1 (p_t + (j : ℤ)) = (if tbits[j] then Sym.data1 else Sym.data0) := by
      rw [show tape1 (p_t + (j : ℤ)) = tape (p_t + (j : ℤ)) from by simp [tape1]; intro h'; omega]
      have hj' : j < tbits.length := by omega
      have h := htarget j (by
        have hlen : (targetTape j tbits).length = tbits.length := by
          simp [targetTape_length]
        rw [hlen]
        omega)
      simpa [targetTape_getElem_j j tbits hj'] using h
    let tape2 : ℤ → Sym := fun i => if i = p_t + (j : ℤ) then (if tbits[j] then Sym.data1 true else Sym.data0 true) else tape1 i
    let r_tj : SymTransResult := { nextState := 81, writeSym := (if tbits[j] then Sym.data1 true else Sym.data0 true), moveDir := Dir.R }
    let step_tj : SymStep := { fromState := 12, readSym := (if tbits[j] then Sym.data1 else Sym.data0), result := r_tj }
    have htj_mark : ((if tbits[j] then Sym.data1 else Sym.data0).2 = false) := by
      by_cases hb : tbits[j] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]
    have htj_kind : ((if tbits[j] then Sym.data1 else Sym.data0).1 = SymKind.data0 ∨
        (if tbits[j] then Sym.data1 else Sym.data0).1 = SymKind.data1) := by
      by_cases hb : tbits[j] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]
    have htrans_tj : step_tj.result ∈ VerifierSym.transition (12, (if tbits[j] then Sym.data1 else Sym.data0)) := by
      by_cases hb : tbits[j]
      · simp [step_tj, r_tj, hb]
        decide
      · simp [step_tj, r_tj, hb]
        decide
    have hstep_tj : SymSteps VerifierSym.transition (SymConfig.mk 12 tape1 (p_t + (j : ℤ))) [step_tj]
        (symStepConfig (SymConfig.mk 12 tape1 (p_t + (j : ℤ))) step_tj.result) := by
      refine SymSteps.cons [] step_tj (SymConfig.mk 12 tape1 (p_t + (j : ℤ))) SymSteps.nil ?_ ?_ ?_
      · rfl
      · change step_tj.readSym = tape1 (p_t + (j : ℤ))
        simp [step_tj]
        rw [htape_tj]
      · change step_tj.result ∈ VerifierSym.transition (12, tape1 (p_t + (j : ℤ)))
        rw [htape_tj]
        exact htrans_tj
    have hcfg_tj : symStepConfig (SymConfig.mk 12 tape1 (p_t + (j : ℤ))) step_tj.result =
        SymConfig.mk 81 tape2 (p_t + (j : ℤ) + 1) := by
      simp [symStepConfig, SymConfig.mk, step_tj, r_tj, tape2, Dir.toInt]
    -- 状态 12 右移回元素区
    let n : ℕ := (p_e - p_t - (j : ℤ)).toNat
    have hn_n : (n : ℤ) = p_e - p_t - (j : ℤ) := by
      change ((p_e - p_t - (j : ℤ)).toNat : ℤ) = p_e - p_t - (j : ℤ)
      exact Int.toNat_of_nonneg (by omega : 0 ≤ p_e - p_t - (j : ℤ))
    have hnc12 : ∀ i : ℤ, p_t + (j : ℤ) + 1 ≤ i ∧ i < p_t + (j : ℤ) + 1 + (n : ℤ) →
        (tape2 i).1 = SymKind.data0 ∨ (tape2 i).1 = SymKind.data1 ∨ (tape2 i).1 = SymKind.boundary := by
      intro i hi
      have hi_lt_pe : i < p_e + 1 := by
        have := hi.2
        rw [hn_n] at this
        omega
      by_cases hlt_target : i < p_t + (ebits.length : ℤ)
      · -- target 剩余位（t_j+1 到 t_{k-1}）
        have hne_tj : i ≠ p_t + (j : ℤ) := by omega
        have ioff : ∃ io : ℕ, (io : ℤ) = i - p_t := by
          refine ⟨(i - p_t).toNat, ?_⟩
          exact Int.toNat_of_nonneg (by omega : 0 ≤ i - p_t)
        rcases ioff with ⟨io, hio⟩
        have hio_gt : j < io := by omega
        have hio_lt : io < (targetTape j tbits).length := by
          have hlen : (targetTape j tbits).length = tbits.length := by
            simp [targetTape_length]
          rw [hlen]
          omega
        have ht := htarget io hio_lt
        have hio_tbits : io < tbits.length := by omega
        have hsym : (targetTape j tbits)[io]'(by simpa using hio_tbits) = (if tbits[io] then Sym.data1 else Sym.data0) := by
          exact targetTape_getElem_ge j io tbits hio_tbits (Nat.le_of_lt hio_gt)
        have hnb : ((if tbits[io] then Sym.data1 else Sym.data0).1 = SymKind.data0 ∨
            (if tbits[io] then Sym.data1 else Sym.data0).1 = SymKind.data1) := by
          by_cases hb : tbits[io] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]
        have hidx : p_t + (io : ℤ) = i := by omega
        rw [hidx] at ht
        rw [show tape2 i = tape1 i from by simp [tape2]; intro h; omega]
        rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
        rw [ht, hsym]
        rcases hnb with hd | hd
        · left; simpa using hd
        · right; left; simpa using hd
      · -- target 高位（t_k 到 t_{L-1}）或 data0 填充 / #₀ / sel
        by_cases hlt_L : i < p_t + (tbits.length : ℤ)
        · -- target 高位：data0/1
          have ioff : ∃ io : ℕ, (io : ℤ) = i - p_t := by
            refine ⟨(i - p_t).toNat, ?_⟩
            exact Int.toNat_of_nonneg (by omega : 0 ≤ i - p_t)
          rcases ioff with ⟨io, hio⟩
          have hio_gt : j < io := by omega
          have hio_lt : io < (targetTape j tbits).length := by
            have hlen : (targetTape j tbits).length = tbits.length := by
              simp [targetTape_length]
            rw [hlen]
            omega
          have ht := htarget io hio_lt
          have hio_tbits : io < tbits.length := by omega
          have hsym : (targetTape j tbits)[io]'(by simpa using hio_tbits) = (if tbits[io] then Sym.data1 else Sym.data0) := by
            exact targetTape_getElem_ge j io tbits hio_tbits (Nat.le_of_lt hio_gt)
          have hnb : ((if tbits[io] then Sym.data1 else Sym.data0).1 = SymKind.data0 ∨
              (if tbits[io] then Sym.data1 else Sym.data0).1 = SymKind.data1 ∨
              (if tbits[io] then Sym.data1 else Sym.data0).1 = SymKind.boundary) := by
            by_cases hb : tbits[io] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]
          have hidx : p_t + (io : ℤ) = i := by omega
          rw [hidx] at ht
          rw [show tape2 i = tape1 i from by simp [tape2]; intro h'; omega]
          rw [show tape1 i = tape i from by simp [tape1]; intro h'; omega]
          rw [ht, hsym]
          rcases hnb with hd | hd | hd
          · left; simpa using hd
          · right; left; simpa using hd
          · right; right; simpa using hd
        · -- data0 填充 / #₀ / sel
          by_cases hpad_i : i < p_e - 1
          · -- data0 填充
            have h := hpad i (by constructor <;> omega)
            rw [show tape2 i = tape1 i from by simp [tape2]; intro h'; omega]
            rw [show tape1 i = tape i from by simp [tape1]; intro h'; omega]
            rw [h]
            decide
          · -- i ∈ {p_e-1, p_e}
            by_cases hh0 : i = p_e - 1
            · rw [hh0]
              rw [show tape2 (p_e - 1) = tape1 (p_e - 1) from by simp [tape2]; intro h'; omega]
              rw [show tape1 (p_e - 1) = tape (p_e - 1) from by simp [tape1]; intro h'; omega]
              rw [hbound]
              decide
            · have hi_pe : i = p_e := by omega
              rw [hi_pe]
              rw [show tape2 p_e = tape1 p_e from by simp [tape2]; intro h'; omega]
              rw [show tape1 p_e = tape p_e from by simp [tape1]; intro h'; omega]
              rcases hsel with hd | hd
              · left; simpa using hd
              · right; left; simpa using hd
    have hcons12 : tape2 (p_t + (j : ℤ) + 1 + (n : ℤ)) = Sym.consumed := by
      have hpos : p_t + (j : ℤ) + 1 + (n : ℤ) = p_e + 1 := by rw [hn_n]; omega
      rw [hpos]
      rw [show tape2 (p_e + 1) = tape1 (p_e + 1) from by simp [tape2]; intro h; omega]
      by_cases hj0 : j = 0
      · subst j
        simp [tape1]
      · have h0lt : 0 < j := by omega
        have h := helem_pre 0 h0lt
        rw [show tape1 (p_e + 1) = tape (p_e + 1) from by simp [tape1]; intro h'; omega]
        simpa using h
    rcases scanRight81 n (p_t + (j : ℤ) + 1) tape2 hnc12 hcons12 with ⟨π12, cfg12, hπ12, hs12, hhead12, htape12⟩
    -- 状态 13 右移扫 consumed 到 v_{j+1}
    have hcons13 : ∀ i : ℤ, p_e + 2 ≤ i ∧ i < p_e + 2 + (j : ℤ) → tape2 i = Sym.consumed := by
      intro i hi
      have ioff : ∃ io : ℕ, (io : ℤ) = i - (p_e + 2) := by
        refine ⟨(i - (p_e + 2)).toNat, ?_⟩
        exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p_e + 2))
      rcases ioff with ⟨io, hio⟩
      have hio_lt : io < j := by omega
      have hidx : i = p_e + 1 + ((io + 1 : ℕ) : ℤ) := by omega
      rw [hidx]
      rw [show tape2 (p_e + 1 + ((io + 1 : ℕ) : ℤ)) = tape1 (p_e + 1 + ((io + 1 : ℕ) : ℤ)) from by simp [tape2]; intro h; omega]
      have hio1_le : io + 1 ≤ j := by omega
      by_cases hio1_eq : io + 1 = j
      · rw [hio1_eq]
        simp [tape1]
      · have hio1_lt : io + 1 < j := by omega
        have h := helem_pre (io + 1) hio1_lt
        rw [show tape1 (p_e + 1 + ((io + 1 : ℕ) : ℤ)) = tape (p_e + 1 + ((io + 1 : ℕ) : ℤ)) from by simp [tape1]; intro h'; omega]
        exact h
    rcases scanRight13_scan j (p_e + 2) tape2 hcons13 with ⟨π13, cfg13, hπ13, hs13, hhead13, htape13⟩
    -- 组装
    have htarget_next : tapeAgrees tape2 p_t (targetTape (j + 1) tbits) := by
      exact tape_agrees_targetTape_succ_mark ebits.length j tbits p_t tape tape2 hlen_le hj htarget
        (by simp [tape2])
        (by intro i hi hne
            have htbits_le : p_t + (tbits.length : ℤ) ≤ p_e - 1 := target_ends_before_pe ebits.length j p_t p_e tape tbits hlen_le hj (by omega) htarget hbound
            rw [show tape2 i = tape1 i from by simp [tape2, hne]]
            rw [show tape1 i = tape i from by simp [tape1]; intro h'; omega])
    have hcfg13_cons : ∀ i : ℕ, i ≤ j → tape2 (p_e + 1 + (i : ℤ)) = Sym.consumed := by
      intro i hi
      by_cases hij : i = j
      · subst i
        have hneq : p_e + 1 + (j : ℤ) ≠ p_t + (j : ℤ) := by omega
        rw [show tape2 (p_e + 1 + (j : ℤ)) = tape1 (p_e + 1 + (j : ℤ)) from by
          simp only [tape2]
          rw [if_neg hneq]]
        simp [tape1]
      · have hi_lt : i < j := by omega
        have h := helem_pre i hi_lt
        rw [show tape2 (p_e + 1 + (i : ℤ)) = tape1 (p_e + 1 + (i : ℤ)) from by simp [tape2]; intro h'; omega]
        rw [show tape1 (p_e + 1 + (i : ℤ)) = tape (p_e + 1 + (i : ℤ)) from by simp [tape1]; intro h'; omega]
        exact h
    have hcfg13_rest : tapeAgrees tape2 (p_e + 1 + ((j + 1 : ℕ) : ℤ)) (bitsToSym (ebits.drop (j + 1))) := by
      intro i hi
      have h := helem_rest i hi
      have hneq : p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ) ≠ p_e + 1 + (j : ℤ) := by omega
      rw [show tape2 (p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ)) = tape1 (p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ)) from by simp [tape2]; intro h'; omega]
      rw [show tape1 (p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ)) = tape (p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ)) from by
        simp [tape1]; intro h'; omega]
      exact h
    -- 组装路径
    have hstep5' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) [step5] (SymConfig.mk 8 tape1 (p_e + (j : ℤ))) := hcfg5 ▸ hstep5
    have h58 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π8) cfg8 := SymSteps_trans _ _ _ _ [step5] π8 hstep5' hπ8
    have hhead8' : cfg8.headPos = p_e - 2 := by
      rw [hhead8]
      simp [Dir.toInt]
      omega
    have hcfg8_eq : cfg8 = SymConfig.mk 9 tape1 (p_e - 2) := by
      rw [← hs8, ← htape8, ← hhead8']
    have hπ9' : SymSteps VerifierSym.transition cfg8 π9 cfg9 := by
      rw [hcfg8_eq]; exact hπ9
    have h589 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π8 ++ π9) cfg9 := SymSteps_trans _ _ _ _ ([step5] ++ π8) π9 h58 hπ9'
    have hhead9' : cfg9.headPos = p_t := by
      rw [hhead9]
      simp [Dir.toInt]
      omega
    have hcfg9_eq : cfg9 = SymConfig.mk 12 tape1 p_t := by
      rw [← hs9, ← htape9, ← hhead9']
    have hπ11' : SymSteps VerifierSym.transition cfg9 π11 cfg11 := by
      rw [hcfg9_eq]; exact hπ11
    have h58911 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π8 ++ π9 ++ π11) cfg11 := SymSteps_trans _ _ _ _ ([step5] ++ π8 ++ π9) π11 h589 hπ11'
    have hcfg11_eq : cfg11 = SymConfig.mk 12 tape1 (p_t + (j : ℤ)) := by
      rw [← hs11, ← htape11, ← hhead11]
    have hstep_tj' : SymSteps VerifierSym.transition cfg11 [step_tj] (SymConfig.mk 81 tape2 (p_t + (j : ℤ) + 1)) := by
      rw [hcfg11_eq]
      exact hcfg_tj ▸ hstep_tj
    have h58911tj : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π8 ++ π9 ++ π11 ++ [step_tj]) (SymConfig.mk 81 tape2 (p_t + (j : ℤ) + 1)) := SymSteps_trans _ _ _ _ ([step5] ++ π8 ++ π9 ++ π11) [step_tj] h58911 hstep_tj'
    have h12' : SymSteps VerifierSym.transition (SymConfig.mk 81 tape2 (p_t + (j : ℤ) + 1)) π12 cfg12 := hπ12
    have h58911tj12 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π8 ++ π9 ++ π11 ++ [step_tj] ++ π12) cfg12 := SymSteps_trans _ _ _ _ ([step5] ++ π8 ++ π9 ++ π11 ++ [step_tj]) π12 h58911tj h12'
    have hhead12' : cfg12.headPos = p_e + 2 := by
      rw [hhead12]
      rw [hn_n]
      omega
    have hcfg12_eq : cfg12 = SymConfig.mk 13 tape2 (p_e + 2) := by
      rw [← hs12, ← htape12, ← hhead12']
    have h13' : SymSteps VerifierSym.transition cfg12 π13 cfg13 := by
      rw [hcfg12_eq]; exact hπ13
    have htotal : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π8 ++ π9 ++ π11 ++ [step_tj] ++ π12 ++ π13) cfg13 := SymSteps_trans _ _ _ _ ([step5] ++ π8 ++ π9 ++ π11 ++ [step_tj] ++ π12) π13 h58911tj12 h13'
    refine ⟨[step5] ++ π8 ++ π9 ++ π11 ++ [step_tj] ++ π12 ++ π13, cfg13, htotal,
      Or.inl ⟨hs13, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simpa [add_assoc, add_comm, add_left_comm] using hhead13
    · rw [htape13]
      simp [hvj_bool]
      exact htarget_next
    · intro i hi
      rw [htape13]
      exact hcfg13_cons i hi
    · rw [htape13]
      exact hcfg13_rest
    · rw [htape13]
      rw [show tape2 p_e = tape1 p_e from by dsimp [tape2]; rw [if_neg (by omega)]]
      rw [show tape1 p_e = tape p_e from by simp [tape1]; intro h; omega]
      exact hsel
    · rw [htape13]
      rw [show tape2 (p_t - 1) = tape1 (p_t - 1) from by simp [tape2]; intro h; omega]
      rw [show tape1 (p_t - 1) = tape (p_t - 1) from by simp [tape1]; intro h; omega]
      exact hhashL
    · rw [htape13]
      rw [show tape2 (p_e - 1) = tape1 (p_e - 1) from by dsimp [tape2]; rw [if_neg (by omega)]]
      rw [show tape1 (p_e - 1) = tape (p_e - 1) from by simp [tape1]; intro h; omega]
      exact hbound
    · rw [htape13]
      rw [show tape2 (p_e + 1 + (ebits.length : ℤ)) = tape1 (p_e + 1 + (ebits.length : ℤ)) from by
        simp [tape2]; intro h; omega]
      rw [show tape1 (p_e + 1 + (ebits.length : ℤ)) = tape (p_e + 1 + (ebits.length : ℤ)) from by
        simp [tape1]; intro h; omega]
    · rw [htape13]
      rw [show tape2 p_e = tape1 p_e from by dsimp [tape2]; rw [if_neg (by omega)]]
      rw [show tape1 p_e = tape p_e from by simp [tape1]; intro h; omega]
    · intro i hi
      rw [htape13]
      rw [show tape2 i = tape1 i from by simp [tape2]; intro h; omega]
      rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
      exact hpad i (by omega)
    · intro i hi
      rw [htape13]
      rw [show tape2 i = tape1 i from by simp [tape2]; intro h; omega]
      rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]


lemma subtract_loop (tbits ebits : List Bool) (j : ℕ) (p_t p_e : ℤ) (tape : ℤ → Sym)
    (hj_lt : j < tbits.length)
    (htlen : tbits.length = j + ebits.length)
    (hle : 2 ^ j * bitsValue ebits ≤ bitsValue tbits)
    (hp_t_le : p_t + (tbits.length : ℤ) ≤ p_e)
    (htarget : tapeAgrees tape p_t (targetTape j tbits))
    (hbound : tape (p_e - 1) = Sym.boundary)
    (hhashL : tape (p_t - 1) = Sym.boundary)
    (hpad : ∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p_e - 1 → tape i = Sym.data0)
    (hsel : (tape p_e).1 = SymKind.data0 ∨ (tape p_e).1 = SymKind.data1)
    (helem_pre : ∀ i : ℕ, i < j → tape (p_e + 1 + (i : ℤ)) = Sym.consumed)
    (helem_rest : tapeAgrees tape (p_e + 1 + (j : ℤ)) (bitsToSym ebits))
    (hsep : tape (p_e + 1 + ((j + ebits.length : ℕ) : ℤ)) = Sym.sel ∨
        tape (p_e + 1 + ((j + ebits.length : ℕ) : ℤ)) = Sym.nosel ∨
        tape (p_e + 1 + ((j + ebits.length : ℕ) : ℤ)) = Sym.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) π cfg' ∧
      cfg'.state = 84 ∧
      tapeAgrees cfg'.tape p_t (targetTape (j + ebits.length) (subAllBitsAt tbits ebits j)) ∧
      (∀ i : ℕ, i < j + ebits.length → cfg'.tape (p_e + 1 + (i : ℤ)) = Sym.consumed) ∧
      cfg'.headPos = p_e + ((j + ebits.length : ℕ) : ℤ) ∧
      cfg'.tape p_e = tape p_e ∧
      cfg'.tape (p_t - 1) = Sym.boundary ∧
      cfg'.tape (p_e + 1 + ((j + ebits.length : ℕ) : ℤ)) = tape (p_e + 1 + ((j + ebits.length : ℕ) : ℤ)) ∧
      (∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p_e - 1 → cfg'.tape i = Sym.data0) ∧
      cfg'.tape (p_e - 1) = Sym.boundary ∧
      (∀ i : ℤ, p_e + 1 + ((j + ebits.length : ℕ) : ℤ) < i → cfg'.tape i = tape i) := by
  induction ebits generalizing tbits j p_t p_e tape with
  | nil =>
      -- ebits = []：tbits.length = j，与 hj_lt 矛盾（最后位后直接 84，不会回到 5）
      exfalso
      have hj' : j < j := by simpa [htlen] using hj_lt
      omega
  | cons b rest ih =>
      -- 处理第 j 位 b
      have hvj : tape (p_e + 1 + (j : ℤ)) = if b then Sym.data1 else Sym.data0 := by
        have h0 := helem_rest 0 (by simp [bitsToSym])
        simpa [bitsToSym_cons] using h0
      let ebits_full : List Bool := List.replicate j false ++ (b :: rest)
      have helen_full : ebits_full.length = tbits.length := by
        simp [ebits_full, htlen]
      have hj : j < tbits.length := by
        rw [htlen]
        simp
      have helem_rest_full : tapeAgrees tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) (bitsToSym (ebits_full.drop (j + 1))) := by
        have hdrop : ebits_full.drop (j + 1) = rest := by
          dsimp [ebits_full]
          simp [List.drop_append, List.length_replicate]
        rw [hdrop]
        intro i hi
        have h := helem_rest (i + 1) (by
          simp [bitsToSym] at hi ⊢
          omega)
        simpa [bitsToSym_cons, add_assoc, add_comm, add_left_comm] using h
      have hsub : (if b then 2 ^ j else 0) ≤ bitsValue tbits := by
        by_cases hb : b
        · simp [hb]
          have hbval : 1 ≤ bitsValue (b :: rest) := by simp [hb]
          have hmul : 2 ^ j ≤ 2 ^ j * bitsValue (b :: rest) := by
            have : 2 ^ j * 1 ≤ 2 ^ j * bitsValue (b :: rest) := Nat.mul_le_mul_left (2 ^ j) hbval
            simpa using this
          exact le_trans hmul hle
        · simp [hb]
      have hres := process_one_bit_last j b tbits ebits_full p_t p_e tape (by rw [helen_full]) (by rw [← helen_full] at hj; exact hj) hp_t_le
          hbound hpad htarget hhashL hsel helem_pre hvj helem_rest_full
      rcases hres with ⟨π₁, cfg₁, hπ₁, hres1⟩
      match hres1 with
      | Or.inl ⟨hstate₁, hhead₁, hta₁, hcons₁, hrest₁, hsel₁, hhashL₁, hbound₁, hsep₁, hpe_eq₁, hpad_keep₁, hright₁⟩ =>
          let tbits' : List Bool := if b then (subOneAt j tbits).getD tbits else tbits
          have htbits'_eq : tbits' = subAllBitsAt tbits [b] j := by
            simp [tbits', subAllBitsAt]
          have htlen' : tbits'.length = (j + 1) + rest.length := by
            have hlen_t : tbits'.length = tbits.length := by
              rw [htbits'_eq]
              exact subAllBitsAt_length tbits [b] j
            rw [hlen_t, htlen]
            rw [show (b :: rest).length = rest.length + 1 from rfl]
            omega
          have hle' : 2 ^ (j + 1) * bitsValue rest ≤ bitsValue tbits' := by
            have hval : bitsValue tbits' = bitsValue tbits - (if b then 2 ^ j else 0) := by
              by_cases hb : b
              · have hval' := subAllBitsAt_value tbits [b] j (by simpa [hb, bitsValue] using hsub)
                rw [← htbits'_eq] at hval'
                have hb_val : bitsValue [b] = 1 := by simp [hb]
                simpa [hb, hb_val] using hval'
              · have hval' := subAllBitsAt_value tbits [b] j (by simp [hb])
                rw [← htbits'_eq] at hval'
                have hb_val : bitsValue [b] = 0 := by simp [hb]
                simpa [hb, hb_val] using hval'
            by_cases hb : b
            · -- b = true
              have hbval : bitsValue (b :: rest) = 1 + 2 * bitsValue rest := by simp [hb]
              have hle0 : 2 ^ j * (1 + 2 * bitsValue rest) ≤ bitsValue tbits := by simpa [hbval] using hle
              have hle1 : 2 ^ j + 2 ^ j * (2 * bitsValue rest) ≤ bitsValue tbits := by
                have : 2 ^ j + 2 ^ j * (2 * bitsValue rest) = 2 ^ j * (1 + 2 * bitsValue rest) := by ring
                rw [this]
                exact hle0
              have hpow : 2 ^ j * (2 * bitsValue rest) = 2 ^ (j + 1) * bitsValue rest := by
                rw [pow_succ]
                ring
              rw [hval]
              simp [hb]
              rw [← hpow]
              omega
            · -- b = false
              have hbval : bitsValue (b :: rest) = 2 * bitsValue rest := by simp [hb]
              have hle0 : 2 ^ j * (2 * bitsValue rest) ≤ bitsValue tbits := by simpa [hbval] using hle
              have hpow : 2 ^ j * (2 * bitsValue rest) = 2 ^ (j + 1) * bitsValue rest := by
                rw [pow_succ]
                ring
              rw [hval]
              simp [hb]
              simpa [hpow] using hle0
          have htarget' : tapeAgrees cfg₁.tape p_t (targetTape (j + 1) tbits') := by
            simpa [tbits'] using hta₁
          have helem_pre' : ∀ i : ℕ, i < j + 1 → cfg₁.tape (p_e + 1 + (i : ℤ)) = Sym.consumed := by
            intro i hi
            exact hcons₁ i (by omega)
          have hsep' : cfg₁.tape (p_e + 1 + ((j + 1 + rest.length : ℕ) : ℤ)) = Sym.sel ∨
              cfg₁.tape (p_e + 1 + ((j + 1 + rest.length : ℕ) : ℤ)) = Sym.nosel ∨
              cfg₁.tape (p_e + 1 + ((j + 1 + rest.length : ℕ) : ℤ)) = Sym.boundary := by
            have hlen_eq : ((j + 1 + rest.length : ℕ) : ℤ) = (ebits_full.length : ℤ) := by
              rw [helen_full]
              rw [htlen, List.length_cons]
              omega
            rcases hsep with hsel | hnosel | hbnd
            · left
              rw [hlen_eq, hsep₁]
              simpa [helen_full, htlen, List.length_cons, ebits_full] using hsel
            · right; left
              rw [hlen_eq, hsep₁]
              simpa [helen_full, htlen, List.length_cons, ebits_full] using hnosel
            · right; right
              rw [hlen_eq, hsep₁]
              simpa [helen_full, htlen, List.length_cons, ebits_full] using hbnd
          have hp_t_le' : p_t + (tbits'.length : ℤ) ≤ p_e := by
            have hlen : tbits'.length = tbits.length := by
              rw [htbits'_eq]
              exact subAllBitsAt_length tbits [b] j
            rw [hlen]
            exact hp_t_le
          have hbound' : cfg₁.tape (p_e - 1) = Sym.boundary := hbound₁
          have hpad' : ∀ i : ℤ, p_t + (tbits'.length : ℤ) ≤ i ∧ i < p_e - 1 → cfg₁.tape i = Sym.data0 := by
            intro i hi
            have hlen : tbits'.length = tbits.length := by
              rw [htbits'_eq]
              exact subAllBitsAt_length tbits [b] j
            rw [hlen] at hi
            exact hpad_keep₁ i hi
          have hhashL' : cfg₁.tape (p_t - 1) = Sym.boundary := hhashL₁
          cases rest with
          | nil =>
              -- 最后位：13 读下一元素标记/#₁ → 84 L
              have hsbnd : cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = Sym.sel ∨
                  cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = Sym.nosel ∨
                  cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = Sym.boundary := by
                have hk : ((j + 1 : ℕ) : ℤ) = (ebits_full.length : ℤ) := by
                  rw [helen_full]
                  rw [htlen, List.length_cons]
                  norm_num
                rcases hsep with hsel | hnosel | hbnd
                · left
                  rw [hk, hsep₁]
                  simpa [helen_full, htlen, List.length_cons, ebits_full] using hsel
                · right; left
                  rw [hk, hsep₁]
                  simpa [helen_full, htlen, List.length_cons, ebits_full] using hnosel
                · right; right
                  rw [hk, hsep₁]
                  simpa [helen_full, htlen, List.length_cons, ebits_full] using hbnd
              let r84 : SymTransResult := { nextState := 84, writeSym := cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)), moveDir := Dir.L }
              let step84 : SymStep := { fromState := 13, readSym := cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)), result := r84 }
              have hcfg₁_eq : cfg₁ = SymConfig.mk 13 cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) := by
                cases cfg₁ with
                | mk s t hp =>
                    have hs' : s = 13 := by simpa [SymConfig.mk] using hstate₁
                    have hp' : hp = p_e + 1 + ((j + 1 : ℕ) : ℤ) := by simpa [SymConfig.mk] using hhead₁
                    subst s
                    rw [hp']
              have htrans84 : step84.result ∈ VerifierSym.transition (cfg₁.state, cfg₁.tape cfg₁.headPos) := by
                rw [hcfg₁_eq]
                rcases hsbnd with hs | hs | hs
                · unfold step84 r84
                  rw [hs]
                  simp [SymConfig.mk]
                  decide
                · unfold step84 r84
                  rw [hs]
                  simp [SymConfig.mk]
                  decide
                · unfold step84 r84
                  rw [hs]
                  simp [SymConfig.mk]
                  decide
              have hstep84 : SymSteps VerifierSym.transition cfg₁ [step84] (symStepConfig cfg₁ step84.result) := by
                refine SymSteps.cons [] step84 cfg₁ SymSteps.nil ?_ ?_ ?_
                · simpa [step84] using hstate₁.symm
                · rw [hhead₁]
                · exact htrans84
              let cfg84 : SymConfig := symStepConfig cfg₁ step84.result
              have htape84 : cfg84.tape = cfg₁.tape := by
                dsimp [cfg84]
                simp only [symStepConfig, SymConfig.mk, step84, r84]
                funext i
                by_cases h : i = p_e + 1 + ((j + 1 : ℕ) : ℤ)
                · rw [hcfg₁_eq]
                  rw [h]
                  simp
                · rw [hcfg₁_eq]
                  rw [if_neg h]
              have htotal : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) (π₁ ++ [step84]) cfg84 :=
                SymSteps_trans _ _ _ _ π₁ [step84] hπ₁ hstep84
              refine ⟨π₁ ++ [step84], cfg84, htotal, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · -- target：subAllBitsAt tbits [b] j
                simp only [show cfg84.tape = cfg₁.tape from htape84]
                simpa [tbits', subAllBitsAt] using hta₁
              · -- consumed：i < j + 1
                intro i hi
                simp only [show cfg84.tape = cfg₁.tape from htape84]
                simp [List.length_cons] at hi
                exact hcons₁ i (by omega)
              · -- headPos = p_e + (j+1)
                dsimp [cfg84]
                simp only [symStepConfig, SymConfig.mk, step84, r84, Dir.toInt]
                exact (by
                  simp [hhead₁]
                  ring_nf)
              · -- p_e 保持
                simp only [show cfg84.tape = cfg₁.tape from htape84]
                exact hpe_eq₁
              · simp only [show cfg84.tape = cfg₁.tape from htape84]
                exact hhashL₁
              · -- #₁ 保持
                simp only [show cfg84.tape = cfg₁.tape from htape84]
                rw [show ((j + [b].length : ℕ) : ℤ) = (ebits_full.length : ℤ) from by
                  rw [helen_full]
                  rw [htlen, List.length_cons]]
                exact hsep₁
              · -- gap
                intro i hi
                simp only [show cfg84.tape = cfg₁.tape from htape84]
                exact hpad_keep₁ i hi
              · simp only [show cfg84.tape = cfg₁.tape from htape84]
                exact hbound₁
              · intro i hi
                simp only [show cfg84.tape = cfg₁.tape from htape84]
                have hi' : p_e + 1 + (ebits_full.length : ℤ) < i := by
                  rw [helen_full]
                  rw [← htlen] at hi
                  exact hi
                exact hright₁ i hi'
          | cons b2 rest2 =>
              -- 非最后位：13 读 v_{j+1}（data）→ 5 S
              have hd : cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = (if b2 then Sym.data1 else Sym.data0) := by
                have hdrop : ebits_full.drop (j + 1) = b2 :: rest2 := by
                  dsimp [ebits_full]
                  simp [List.drop_append, List.length_replicate, List.drop]
                have h0 := hrest₁ 0 (by simp [bitsToSym, hdrop])
                simpa [bitsToSym, hdrop] using h0
              let r5b : SymTransResult := { nextState := 5, writeSym := cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)), moveDir := Dir.S }
              let step5b : SymStep := { fromState := 13, readSym := cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)), result := r5b }
              have hcfg₁_eq : cfg₁ = SymConfig.mk 13 cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) := by
                cases cfg₁ with
                | mk s t hp =>
                    have hs' : s = 13 := by simpa [SymConfig.mk] using hstate₁
                    have hp' : hp = p_e + 1 + ((j + 1 : ℕ) : ℤ) := by simpa [SymConfig.mk] using hhead₁
                    subst s
                    rw [hp']
              have htrans5b : step5b.result ∈ VerifierSym.transition (cfg₁.state, cfg₁.tape cfg₁.headPos) := by
                rw [hcfg₁_eq]
                by_cases hb2 : b2
                · unfold step5b r5b
                  rw [show cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = Sym.data1 from by simpa [if_pos hb2] using hd]
                  simp [SymConfig.mk]
                  decide
                · unfold step5b r5b
                  rw [show cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = Sym.data0 from by simpa [if_neg hb2] using hd]
                  simp [SymConfig.mk]
                  decide
              have hstep5b : SymSteps VerifierSym.transition cfg₁ [step5b] (symStepConfig cfg₁ step5b.result) := by
                refine SymSteps.cons [] step5b cfg₁ SymSteps.nil ?_ ?_ ?_
                · simpa [step5b] using hstate₁.symm
                · rw [hhead₁]
                · exact htrans5b
              let cfg5b : SymConfig := symStepConfig cfg₁ step5b.result
              have htape5b : cfg5b.tape = cfg₁.tape := by
                dsimp [cfg5b]
                dsimp only [symStepConfig, SymConfig.mk, step5b, r5b]
                funext i
                by_cases h : i = p_e + 1 + ((j + 1 : ℕ) : ℤ)
                · rw [hcfg₁_eq]
                  rw [h]
                  simp
                · rw [hcfg₁_eq]
                  rw [if_neg h]
              have hhead5b : cfg5b.headPos = p_e + 1 + ((j + 1 : ℕ) : ℤ) := by
                dsimp [cfg5b]
                simp only [symStepConfig, SymConfig.mk, step5b, r5b, Dir.toInt]
                rw [hcfg₁_eq]
                simp
              have hstate5b : cfg5b.state = 5 := by
                dsimp [cfg5b]
                simp only [symStepConfig, SymConfig.mk, step5b, r5b]
              have htotal_pre : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) (π₁ ++ [step5b]) cfg5b :=
                SymSteps_trans _ _ _ _ π₁ [step5b] hπ₁ hstep5b
              have hbound'' : cfg5b.tape (p_e - 1) = Sym.boundary := by simp only [show cfg5b.tape = cfg₁.tape from htape5b]; exact hbound₁
              have hhashL'' : cfg5b.tape (p_t - 1) = Sym.boundary := by simp only [show cfg5b.tape = cfg₁.tape from htape5b]; exact hhashL₁
              have hpad'' : ∀ i : ℤ, p_t + (tbits'.length : ℤ) ≤ i ∧ i < p_e - 1 → cfg5b.tape i = Sym.data0 := by
                intro i hi
                simp only [show cfg5b.tape = cfg₁.tape from htape5b]
                exact hpad' i hi
              have hsel'' : (cfg5b.tape p_e).1 = SymKind.data0 ∨ (cfg5b.tape p_e).1 = SymKind.data1 := by
                simp only [show cfg5b.tape = cfg₁.tape from htape5b]
                exact hsel₁
              have helem_pre'' : ∀ i : ℕ, i < j + 1 → cfg5b.tape (p_e + 1 + (i : ℤ)) = Sym.consumed := by
                intro i hi
                simp only [show cfg5b.tape = cfg₁.tape from htape5b]
                exact hcons₁ i (Nat.le_of_lt_succ hi)
              have helem_rest'' : tapeAgrees cfg5b.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) (bitsToSym (b2 :: rest2)) := by
                simp only [show cfg5b.tape = cfg₁.tape from htape5b]
                have hdrop2 : ebits_full.drop (j + 1) = b2 :: rest2 := by
                  dsimp [ebits_full]
                  simp [List.drop_append, List.length_replicate, List.drop]
                rw [hdrop2] at hrest₁
                exact hrest₁
              have hsep'' : cfg5b.tape (p_e + 1 + ((j + 1 + (b2 :: rest2).length : ℕ) : ℤ)) = Sym.sel ∨
                  cfg5b.tape (p_e + 1 + ((j + 1 + (b2 :: rest2).length : ℕ) : ℤ)) = Sym.nosel ∨
                  cfg5b.tape (p_e + 1 + ((j + 1 + (b2 :: rest2).length : ℕ) : ℤ)) = Sym.boundary := by
                simp only [show cfg5b.tape = cfg₁.tape from htape5b]
                rw [show (j + 1 + (b2 :: rest2).length : ℕ) = (ebits_full.length : ℕ) from by
                  rw [helen_full]
                  rw [htlen]
                  simp [List.length_cons]
                  omega]
                rw [hsep₁]
                rw [helen_full]
                rw [htlen]
                exact hsep
              have hj_lt2 : j + 1 < tbits'.length := by
                rw [htlen']
                simp
              have hcfg5b_eq : cfg5b = SymConfig.mk 5 cfg5b.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) := by
                rw [← hstate5b, ← hhead5b]
              rw [← htape5b] at htarget'
              have hih := ih tbits' (j + 1) p_t p_e cfg5b.tape hj_lt2 htlen' hle' hp_t_le' htarget'
                  hbound'' hhashL'' hpad'' hsel'' helem_pre'' helem_rest'' hsep''
              rcases hih with ⟨π₂, cfg₂, hπ₂, hs₂, hta₂, hcons₂, hhead₂, hpe_eq₂, hhashL₂, hsep₂, hpad₂, hbound₂, hright₂⟩
              have hπ₂' : SymSteps VerifierSym.transition cfg5b π₂ cfg₂ := by
                rw [hcfg5b_eq]
                exact hπ₂
              have htotal : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) (π₁ ++ [step5b] ++ π₂) cfg₂ :=
                SymSteps_trans _ _ _ _ (π₁ ++ [step5b]) π₂ htotal_pre hπ₂'
              refine ⟨π₁ ++ [step5b] ++ π₂, cfg₂, htotal, hs₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · -- tapeAgrees
                have hta₂' : tapeAgrees cfg₂.tape p_t (targetTape (j + 1 + (b2 :: rest2).length) (subAllBitsAt tbits' (b2 :: rest2) (j + 1))) := hta₂
                have hsubAll : subAllBitsAt tbits (b :: b2 :: rest2) j = subAllBitsAt tbits' (b2 :: rest2) (j + 1) := by
                  simp [subAllBitsAt, tbits']
                have hlen_eq : j + 1 + (b2 :: rest2).length = j + (b :: b2 :: rest2).length := by simp [List.length_cons]; omega
                rw [← hsubAll] at hta₂'
                rw [hlen_eq] at hta₂'
                exact hta₂'
              · -- consumed
                intro i hi
                have h := hcons₂ i (by rw [List.length_cons] at hi; omega)
                exact h
              · -- headPos
                rw [hhead₂]
                congr 1
                simp only [List.length_cons]
                omega
              · -- p_e 保持
                exact hpe_eq₂ ▸ (show cfg5b.tape p_e = tape p_e from by
                  simp only [show cfg5b.tape = cfg₁.tape from htape5b]
                  exact hpe_eq₁)
              · -- hhashL 保持
                exact hhashL₂
              · -- #₁ 保持
                have hlen_eq : ((j + (b :: b2 :: rest2).length : ℕ) : ℤ) = (ebits_full.length : ℤ) := by
                  rw [helen_full]
                  rw [htlen]
                rw [hlen_eq]
                have hlen_eq2 : ((j + 1 + (b2 :: rest2).length : ℕ) : ℤ) = (ebits_full.length : ℤ) := by
                  rw [helen_full]
                  rw [htlen]
                  simp [List.length_cons]
                  omega
                rw [hlen_eq2] at hsep₂
                rw [hsep₂]
                simp only [show cfg5b.tape = cfg₁.tape from htape5b]
                exact hsep₁
              · -- data0 填充保持
                intro i hi
                have hlen : tbits'.length = tbits.length := by
                  rw [htbits'_eq]
                  exact subAllBitsAt_length tbits [b] j
                rw [← hlen] at hi
                exact hpad₂ i hi
              · -- boundary 保持
                exact hbound₂
              · -- #₁ 右边不变
                intro i hi
                rw [show p_e + 1 + ((j + (b :: b2 :: rest2).length : ℕ) : ℤ) = p_e + 1 + ((j + 1 + (b2 :: rest2).length : ℕ) : ℤ) from by rw [List.length_cons]; omega] at hi
                rw [hright₂ i hi]
                have hi' : p_e + 1 + (ebits_full.length : ℤ) < i := by
                  rw [helen_full]
                  rw [htlen, List.length_cons]
                  omega
                simp only [show cfg5b.tape = cfg₁.tape from htape5b]
                rw [hright₁ i hi']

      | Or.inr ⟨hs101, hhead101, hb101, hlt2_101, hdata1_101, hbound101, hcons101, hhashL101, hkeep_pe101, hright101⟩ =>
          exfalso
          have hb' : b = true := by simpa using hb101
          subst b
          have h2 : 2 ^ j ≤ bitsValue tbits := by simpa using hsub
          omega
lemma subtract_element_correct (tbits ebits : List Bool) (p_t p_e : ℤ) (tape : ℤ → Sym)
    (hebits_pos : 0 < ebits.length)
    (htlen : tbits.length = ebits.length)
    (hle : bitsValue ebits ≤ bitsValue tbits)
    (hp_t_le : p_t + (tbits.length : ℤ) ≤ p_e)

    (htarget : tapeAgrees tape p_t (targetTape 0 tbits))
    (hbound : tape (p_e - 1) = Sym.boundary)
    (hhashL : tape (p_t - 1) = Sym.boundary)
    (hpad : ∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p_e - 1 → tape i = Sym.data0)
    (hsel : tape p_e = Sym.sel)
    (helem : tapeAgrees tape (p_e + 1) (bitsToSym ebits))
    (hsep : tape (p_e + 1 + (ebits.length : ℤ)) = Sym.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) π cfg' ∧
      ((cfg'.state = 84 ∧ cfg'.headPos = p_e + (ebits.length : ℤ))
       ∨ (cfg'.state = 5 ∧ cfg'.headPos = p_e + 1 + (ebits.length : ℤ))) ∧
      tapeAgrees cfg'.tape p_t (targetTape ebits.length (subAllBits tbits ebits)) ∧
      (∀ i : ℕ, i < ebits.length → cfg'.tape (p_e + 1 + (i : ℤ)) = Sym.consumed) ∧
      cfg'.tape p_e = Sym.data0 ∧
      cfg'.tape (p_t - 1) = Sym.boundary ∧
      cfg'.tape (p_e + 1 + (ebits.length : ℤ)) = tape (p_e + 1 + (ebits.length : ℤ)) ∧
      (∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p_e - 1 → cfg'.tape i = Sym.data0) ∧
      cfg'.tape (p_e - 1) = Sym.boundary ∧
      (∀ i : ℤ, p_e + 1 + (ebits.length : ℤ) < i → cfg'.tape i = tape i) := by
  let r : SymTransResult := { nextState := 5, writeSym := Sym.data0, moveDir := Dir.R }
  let step : SymStep := { fromState := 4, readSym := Sym.sel, result := r }
  let tape1 : ℤ → Sym := fun i => if i = p_e then Sym.data0 else tape i
  have hstep : SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) [step]
      (symStepConfig (SymConfig.mk 4 tape p_e) step.result) := by
    refine SymSteps.cons [] step (SymConfig.mk 4 tape p_e) SymSteps.nil ?_ ?_ ?_
    · rfl
    · change Sym.sel = tape p_e
      rw [hsel]
    · change step.result ∈ VerifierSym.transition (4, tape p_e)
      rw [hsel]
      decide
  have hcfg : symStepConfig (SymConfig.mk 4 tape p_e) step.result =
      SymConfig.mk 5 tape1 (p_e + 1) := by
    simp [symStepConfig, SymConfig.mk, step, r, tape1, Dir.toInt]
  have htarget0 : tapeAgrees tape1 p_t (targetTape 0 tbits) := by
    intro i hi
    have hi_t : i < tbits.length := by simpa [targetTape_length] using hi
    have hneq : p_t + (i : ℤ) ≠ p_e := by omega
    rw [show tape1 (p_t + (i : ℤ)) = tape (p_t + (i : ℤ)) from by
      simp only [tape1]
      rw [if_neg hneq]]
    exact htarget i hi
  have hbound0 : tape1 (p_e - 1) = Sym.boundary := by
    rw [show tape1 (p_e - 1) = tape (p_e - 1) from by
      simp only [tape1]
      rw [if_neg (by omega : p_e - 1 ≠ p_e)]]
    exact hbound
  have hhashL0 : tape1 (p_t - 1) = Sym.boundary := by
    have hneq : p_t - 1 ≠ p_e := by omega
    rw [show tape1 (p_t - 1) = tape (p_t - 1) from by
      simp only [tape1]
      rw [if_neg hneq]]
    exact hhashL
  have hsel0 : (tape1 p_e).1 = SymKind.data0 ∨ (tape1 p_e).1 = SymKind.data1 := by
    left
    simp [tape1]
  have helem0 : tapeAgrees tape1 (p_e + 1) (bitsToSym ebits) := by
    intro i hi
    have hneq : p_e + 1 + (i : ℤ) ≠ p_e := by omega
    rw [show tape1 (p_e + 1 + (i : ℤ)) = tape (p_e + 1 + (i : ℤ)) from by
      simp only [tape1]
      rw [if_neg hneq]]
    exact helem i hi
  have hsep0 : tape1 (p_e + 1 + (ebits.length : ℤ)) = Sym.boundary := by
    have hneq : p_e + 1 + (ebits.length : ℤ) ≠ p_e := by omega
    rw [show tape1 (p_e + 1 + (ebits.length : ℤ)) = tape (p_e + 1 + (ebits.length : ℤ)) from by
      simp only [tape1]
      rw [if_neg hneq]]
    exact hsep
  have hle0 : 2 ^ 0 * bitsValue ebits ≤ bitsValue tbits := by simpa using hle
  have hpad0 : ∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p_e - 1 → tape1 i = Sym.data0 := by
    intro i hi
    rw [show tape1 i = tape i from by
      simp only [tape1]
      rw [if_neg (by omega : i ≠ p_e)]]
    exact hpad i hi
  have hsl := subtract_loop tbits ebits 0 p_t p_e tape1 (by rw [htlen]; exact hebits_pos) (by rw [zero_add]; exact htlen) hle0 hp_t_le htarget0 hbound0 hhashL0 hpad0 hsel0
      (by intro i hi; omega) (by simpa using helem0) (Or.inr (Or.inr (by simpa [zero_add] using hsep0)))
  rcases hsl with ⟨π, cfg', hπ, hrest⟩
  rcases hrest with ⟨hfin, hta, hcons, hhead, hpe_eq, hhashL_out, hsep_keep, hpad_keep, hbound_keep, hright_keep⟩
  refine ⟨[step] ++ π, cfg', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hstep' : SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) [step]
        (SymConfig.mk 5 tape1 (p_e + 1)) := by
      simpa [hcfg] using hstep
    have hπ' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape1 (p_e + 1)) π cfg' := by
      simpa using hπ
    exact SymSteps_trans VerifierSym.transition (SymConfig.mk 4 tape p_e) (SymConfig.mk 5 tape1 (p_e + 1)) cfg' [step] π hstep' hπ'
  · left
    refine ⟨hfin, ?_⟩
    rw [hhead]
    rw [show p_e + ((0 + ebits.length : ℕ) : ℤ) = p_e + (ebits.length : ℤ) from by simp]
  · simpa [subAllBits] using hta
  · intro i hi
    exact hcons i (by omega)
  · rw [hpe_eq]
    simp [tape1]
  · exact hhashL_out
  · -- sep 保持
    have hsep_keep' : cfg'.tape (p_e + 1 + (ebits.length : ℤ)) = tape1 (p_e + 1 + (ebits.length : ℤ)) := by
      simpa [Nat.zero_add] using hsep_keep
    rw [hsep_keep']
    rw [show tape1 (p_e + 1 + (ebits.length : ℤ)) = tape (p_e + 1 + (ebits.length : ℤ)) from by
      simp only [tape1]
      rw [if_neg (by omega : p_e + 1 + (ebits.length : ℤ) ≠ p_e)]]
  · -- data0 填充保持
    exact hpad_keep
  · -- boundary 保持
    exact hbound_keep
  · intro i hi
    rw [hright_keep i (by simpa [Nat.zero_add] using hi)]
    rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]

/-- 状态 84 读 consumed/data0/data1：写回自身左移。 -/
lemma trans84_keep (s : Sym)
    (hs : s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) :
    { nextState := 84, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (84, s) := by
  rcases s with ⟨k, m⟩
  rcases hs with hk | hk | hk
  · have hk' : k = SymKind.consumed := by simpa using hk
    subst hk'
    cases m <;> decide
  · have hk' : k = SymKind.data0 := by simpa using hk
    subst hk'
    cases m <;> decide
  · have hk' : k = SymKind.data1 := by simpa using hk
    subst hk'
    cases m <;> decide

/-- 状态 85 读 data0/data1：写回自身左移。 -/
lemma trans85_keep (s : Sym)
    (hs : s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) :
    { nextState := 85, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (85, s) := by
  rcases s with ⟨k, m⟩
  rcases hs with hk | hk
  · have hk' : k = SymKind.data0 := by simpa using hk
    subst hk'
    cases m <;> decide
  · have hk' : k = SymKind.data1 := by simpa using hk
    subst hk'
    cases m <;> decide

/-- targetTape bits.length bits 的所有格 4F4.4 = true（全标记）。 -/
lemma targetTape_full_marks (bits : List Bool) :
    ∀ s ∈ targetTape bits.length bits, s.2 = true := by
  intro s hs
  rw [targetTape, List.mem_append] at hs
  rcases hs with hm | hd
  · rcases List.mem_map.mp hm with ⟨b, hb, rfl⟩
    by_cases hb' : b <;> simp [hb', Sym.data1, Sym.data0, Sym.mk]
  · rw [List.drop_of_length_le (Nat.le_refl bits.length)] at hd
    simpa [bitsToSym] using hd

/-- 清除 targetTape n bits（全标记）第 j 位的 4F4.4 位，得到 targetTape 0 bits 第 j 位。 -/
lemma targetTape_clearMark_nth (n j : ℕ) (bits : List Bool) (hj : j < n) (hlen : n ≤ bits.length) :
    Sym.mk (((targetTape n bits)[j]'(by simpa [targetTape_length] using lt_of_lt_of_le hj hlen)).1) false =
      (targetTape 0 bits)[j]'(by simpa [targetTape_length] using lt_of_lt_of_le hj hlen) := by
  have hj_n : j < n := hj
  rw [targetTape_getElem_lt n j bits (by simpa [targetTape_length] using lt_of_lt_of_le hj hlen) hj_n]
  rw [show (targetTape 0 bits)[j]'(by simpa [targetTape_length] using lt_of_lt_of_le hj hlen) = (if bits[j] then Sym.data1 else Sym.data0) from by
    simp [targetTape, bitsToSym]]
  by_cases hb : bits[j] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk, bitsToSym]

/-- 同一列表、索引相等的 getElem 相等（proof irrelevance）。 -/
lemma getElem_of_eq {α : Type} (l : List α) {i j : ℕ} (h : i = j) (hi : i < l.length) (hj : j < l.length) :
    l[i]'hi = l[j]'hj := by
  subst j
  rfl

/-- targetTape n bits 的第 n 格 = if bits[n]（第一个未标记格，m=false）。 -/
lemma targetTape_nth_eq_if (n : ℕ) (bits : List Bool) (hn : n < bits.length) :
    (targetTape n bits)[n]'(by simpa [targetTape_length] using hn) =
      (if bits[n]'(hn) then Sym.data1 else Sym.data0) := by
  have hlen_take : ((bits.take n).map (fun b => if b then Sym.data1 true else Sym.data0 true)).length = n := by
    rw [List.length_map, List.length_take, min_eq_left (le_of_lt hn)]
  have hg : ((bits.take n).map (fun b => if b then Sym.data1 true else Sym.data0 true) ++ bitsToSym (bits.drop n))[n]'(by
        simp [bitsToSym, List.length_drop, List.length_append, hlen_take]
        omega) = (bitsToSym (bits.drop n))[n - ((bits.take n).map (fun b => if b then Sym.data1 true else Sym.data0 true)).length]'(by
        simp [bitsToSym, List.length_drop, hlen_take]
        omega) := by
    exact List.getElem_append_right (by rw [hlen_take])
  unfold targetTape
  simpa [hg, min_eq_left (le_of_lt hn), bitsToSym]

/-- targetTape n bits 在 i ≥ n 处与 targetTape 0 bits 相同（高位不标，与 j 无关）。 -/
lemma targetTape_high_nth (n i : ℕ) (bits : List Bool) (hn : n ≤ i) (hi : i < bits.length) :
    (targetTape n bits)[i]'(by simpa [targetTape_length] using hi) = (targetTape 0 bits)[i]'(by simpa [targetTape_length] using hi) := by
  have hlen_take : ((bits.take n).map (fun b => if b then Sym.data1 true else Sym.data0 true)).length = n := by
    rw [List.length_map, List.length_take, min_eq_left (by omega : n ≤ bits.length)]
  unfold targetTape
  rw [List.getElem_append_right (by rw [hlen_take]; exact hn)]
  rw [List.getElem_append_right (by omega : 0 ≤ i)]
  simp [bitsToSym, List.getElem_drop, min_eq_left (by omega : n ≤ bits.length)]
  change (if bits[n + (i - n)]'(show n + (i - n) < bits.length by omega) = true then Sym.data1 else Sym.data0) =
    if bits[i]'(show i < bits.length by omega) = true then Sym.data1 else Sym.data0
  have hx : bits[n + (i - n)]'(show n + (i - n) < bits.length by omega) =
      bits[i]'(show i < bits.length by omega) := by
    exact getElem_of_eq bits (by omega : n + (i - n) = i) _ _
  rw [hx]

/-- 状态 86 右移清 k 格 4F4.4 标记（m=1 → m=0），读第 k+1 格（m=0）→ 87 停。 -/
lemma clearMark86 (k : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hmarked : ∀ i : ℕ, i < k → (tape (p + (i : ℤ))).2 = true)
    (hstop : (tape (p + (k : ℤ))).2 = false)
    (hdata : ∀ i : ℤ, p ≤ i ∧ i < p + (k : ℤ) → (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hdata_stop : (tape (p + (k : ℤ))).1 = SymKind.data0 ∨ (tape (p + (k : ℤ))).1 = SymKind.data1 ∨
      (tape (p + (k : ℤ))).1 = SymKind.boundary)
:
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 86 tape p) π cfg' ∧
      cfg'.state = 87 ∧ cfg'.headPos = p + (k : ℤ) ∧
      (∀ i : ℕ, i < k → cfg'.tape (p + (i : ℤ)) = Sym.mk (tape (p + (i : ℤ))).1 false) ∧
      cfg'.tape (p + (k : ℤ)) = tape (p + (k : ℤ)) ∧
      (∀ i : ℤ, i < p → cfg'.tape i = tape i) ∧
      (∀ i : ℤ, p + (k : ℤ) < i → cfg'.tape i = tape i) := by
  induction k generalizing p tape with
  | zero =>
      let r : SymTransResult := { nextState := 87, writeSym := tape p, moveDir := Dir.S }
      let step : SymStep := { fromState := 86, readSym := tape p, result := r }
      have htrans : step.result ∈ VerifierSym.transition (86, tape p) := by
        rcases htp : tape p with ⟨ks, ms⟩
        simp only [step, r] at *
        rw [htp]
        have hms : ms = false := by simpa [Sym.mk, htp] using hstop
        subst ms
        have hks : ks = SymKind.data0 ∨ ks = SymKind.data1 ∨ ks = SymKind.boundary := by
          simpa [Sym.mk, htp] using hdata_stop
        rcases hks with hk | hk | hk <;> subst ks <;> decide
      refine ⟨[step], symStepConfig (SymConfig.mk 86 tape p) step.result, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · refine SymSteps.cons [] step (SymConfig.mk 86 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans
      · simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
      · intro i hi; omega
      · rw [show (p + ↑(0 : ℕ) : ℤ) = p from by omega]
        simp [symStepConfig, SymConfig.mk, step, r]
      · intro i hi
        have hne : i ≠ p := by omega
        simp [symStepConfig, SymConfig.mk, step, r, hne]
      · intro i hi
        have hne : i ≠ p := by omega
        simp [symStepConfig, SymConfig.mk, step, r, hne]
  | succ k ih =>
      have h0 : (tape p).2 = true := by simpa using hmarked 0 (by omega)
      let tape₁ : ℤ → Sym := fun i => if i = p then Sym.mk (tape p).1 false else tape i
      let r : SymTransResult := { nextState := 86, writeSym := Sym.mk (tape p).1 false, moveDir := Dir.R }
      let step : SymStep := { fromState := 86, readSym := tape p, result := r }
      have htrans : step.result ∈ VerifierSym.transition (86, tape p) := by
        rcases htp : tape p with ⟨ks, ms⟩
        simp only [step, r] at *
        rw [htp]
        have hms : ms = true := by simpa [Sym.mk, htp] using h0
        subst ms
        have hks : ks = SymKind.data0 ∨ ks = SymKind.data1 := by
          simpa [Sym.mk, htp] using hdata p (by constructor; rfl; omega)
        rcases hks with hk | hk <;> subst ks <;> decide
      have hstep : SymSteps VerifierSym.transition (SymConfig.mk 86 tape p) [step]
          (symStepConfig (SymConfig.mk 86 tape p) step.result) := by
        refine SymSteps.cons [] step (SymConfig.mk 86 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans
      have hcfg : symStepConfig (SymConfig.mk 86 tape p) step.result = SymConfig.mk 86 tape₁ (p + 1) := by
          simp [symStepConfig, SymConfig.mk, step, r, tape₁, Dir.toInt]
      have hmarked₁ : ∀ i : ℕ, i < k → (tape₁ (p + 1 + (i : ℤ))).2 = true := by
        intro i hi
        have h := hmarked (i + 1) (by omega)
        have htape : tape₁ (p + 1 + (i : ℤ)) = tape (p + ((i + 1 : ℕ) : ℤ)) := by
          simp only [tape₁]
          rw [if_neg (by omega : p + 1 + (i : ℤ) ≠ p)]
          exact congrArg tape (by omega)
        rw [htape]
        exact h
      have hstop₁ : (tape₁ (p + 1 + (k : ℤ))).2 = false := by
        have htape : tape₁ (p + 1 + (k : ℤ)) = tape (p + ((k + 1 : ℕ) : ℤ)) := by
          simp only [tape₁]
          rw [if_neg (by omega : p + 1 + (k : ℤ) ≠ p)]
          exact congrArg tape (by omega)
        rw [htape]
        exact hstop
      have hdata₁ : ∀ i : ℤ, p + 1 ≤ i ∧ i < p + 1 + (k : ℤ) → (tape₁ i).1 = SymKind.data0 ∨ (tape₁ i).1 = SymKind.data1 := by
        intro i hi
        have hd := hdata i (by constructor <;> omega)
        have htape₁_i : tape₁ i = tape i := by
          simp only [tape₁]
          rw [if_neg (by omega : i ≠ p)]
        simpa [htape₁_i] using hd
      have hdata_stop₁ : (tape₁ (p + 1 + (k : ℤ))).1 = SymKind.data0 ∨ (tape₁ (p + 1 + (k : ℤ))).1 = SymKind.data1 ∨
          (tape₁ (p + 1 + (k : ℤ))).1 = SymKind.boundary := by
        have htape : tape₁ (p + 1 + (k : ℤ)) = tape (p + ((k + 1 : ℕ) : ℤ)) := by
          simp only [tape₁]
          rw [if_neg (by omega : p + 1 + (k : ℤ) ≠ p)]
          exact congrArg tape (by omega)
        rw [htape]
        exact hdata_stop
      rcases ih (p + 1) tape₁ hmarked₁ hstop₁ hdata₁ hdata_stop₁ with ⟨π', cfg', hπ', hs', hhead', hclear', hstop', hleft', hright'⟩
      refine ⟨[step] ++ π', cfg', ?_, hs', ?_, ?_, ?_, ?_, ?_⟩
      · exact SymSteps_trans VerifierSym.transition (SymConfig.mk 86 tape p)
          (SymConfig.mk 86 tape₁ (p + 1)) cfg' [step] π' (by simpa [hcfg] using hstep) hπ'
      · rw [hhead']
        omega
      · intro i hi
        cases i with
        | zero =>
            have hkeep : cfg'.tape p = (SymConfig.mk 86 tape₁ (p + 1)).tape p := by
              exact hleft' p (by omega)
            simpa [SymConfig.mk, tape₁] using hkeep
        | succ i =>
            have h := hclear' i (by omega)
            have hshift : p + ((i + 1 : ℕ) : ℤ) = (p + 1) + (i : ℤ) := by omega
            have htape₁ : tape₁ ((p + 1) + (i : ℤ)) = tape ((p + 1) + (i : ℤ)) := by
              simp only [tape₁]
              rw [if_neg (by omega : (p + 1) + (i : ℤ) ≠ p)]
            rw [hshift, ← htape₁]
            exact h
      · rw [show (p + ((k + 1 : ℕ) : ℤ)) = (p + 1) + (k : ℤ) from by omega]
        rw [hstop']
        simp only [tape₁]
        rw [if_neg (by omega : (p + 1) + (k : ℤ) ≠ p)]
      · intro i hi
        have hi₁ : i < p + 1 := by omega
        have h' := hleft' i hi₁
        have htape₁_i : tape₁ i = tape i := by
          simp only [tape₁]
          rw [if_neg (by omega : i ≠ p)]
        rw [h', htape₁_i]
      · intro i hi
        have hi₁ : p + 1 + (k : ℤ) < i := by omega
        have h' := hright' i hi₁
        have htape₁_i : tape₁ i = tape i := by
          simp only [tape₁]
          rw [if_neg (by omega : i ≠ p)]
        rw [h', htape₁_i]

/-- 状态 87 右移扫 n 格（data0/data1，写回自身）到 #₀（boundary）→ 20。 -/
lemma scanRight87 (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hdata : ∀ i : ℤ, p ≤ i ∧ i < p + (n : ℤ) → (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hbound : tape (p + (n : ℤ)) = Sym.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 87 tape p) π cfg' ∧
      cfg'.state = 20 ∧ cfg'.headPos = p + (n : ℤ) ∧ cfg'.tape = tape := by
  induction n generalizing p tape with
  | zero =>
      let r : SymTransResult := { nextState := 20, writeSym := Sym.boundary, moveDir := Dir.S }
      let step : SymStep := { fromState := 87, readSym := Sym.boundary, result := r }
      have hbound' : tape p = Sym.boundary := by simpa using hbound
      refine ⟨[step], symStepConfig (SymConfig.mk 87 tape p) step.result, ?_, rfl, ?_, ?_⟩
      · refine SymSteps.cons [] step (SymConfig.mk 87 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · change Sym.boundary = tape p
          rw [hbound']
        · change step.result ∈ VerifierSym.transition (87, tape p)
          rw [hbound']
          decide
      · simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
      · simp [symStepConfig, SymConfig.mk, step, r]
        funext i
        by_cases h : i = p <;> simp [h, hbound']
  | succ n ih =>
      have h0 : (tape p).1 = SymKind.data0 ∨ (tape p).1 = SymKind.data1 :=
        hdata p (by constructor <;> omega)
      let r : SymTransResult := { nextState := 87, writeSym := tape p, moveDir := Dir.R }
      let step : SymStep := { fromState := 87, readSym := tape p, result := r }
      have htrans : step.result ∈ VerifierSym.transition (87, tape p) := by
        rcases htp : tape p with ⟨ks, ms⟩
        simp only [step, r] at *
        rw [htp]
        have hks : ks = SymKind.data0 ∨ ks = SymKind.data1 := by simpa [Sym.mk, htp] using h0
        rcases hks with hk | hk <;> subst ks <;> cases ms <;> decide
      have hstep : SymSteps VerifierSym.transition (SymConfig.mk 87 tape p) [step]
          (symStepConfig (SymConfig.mk 87 tape p) step.result) := by
        refine SymSteps.cons [] step (SymConfig.mk 87 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans
      have hcfg : symStepConfig (SymConfig.mk 87 tape p) step.result = SymConfig.mk 87 tape (p + 1) := by
        simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
        funext i
        by_cases h : i = p <;> simp [h]
      have hdata₁ : ∀ i : ℤ, p + 1 ≤ i ∧ i < p + 1 + (n : ℤ) → (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1 := by
        intro i h
        exact hdata i (by constructor <;> omega)
      have hbound₁ : tape (p + 1 + (n : ℤ)) = Sym.boundary := by
        have h' : p + 1 + (n : ℤ) = p + ((n + 1 : ℕ) : ℤ) := by omega
        rw [h']
        exact hbound
      rcases ih (p + 1) tape hdata₁ hbound₁ with ⟨π', cfg', hπ', hs', hhead', htape'⟩
      refine ⟨[step] ++ π', cfg', ?_, hs', ?_, ?_⟩
      · exact SymSteps_trans VerifierSym.transition (SymConfig.mk 87 tape p)
          (SymConfig.mk 87 tape (p + 1)) cfg' [step] π' (hcfg ▸ hstep) hπ'
      · rw [hhead']
        omega
      · exact htape'



/-- foldl (max ∘ bitWidth) 从 x 起的值 ≥ x。 -/
lemma foldl_max_ge (l : List ℕ) (x : ℕ) :
    x ≤ l.foldl (fun m w => max m (bitWidth w)) x := by
  induction l generalizing x with
  | nil => simp
  | cons a rest ih =>
      simp only [List.foldl_cons]
      exact le_trans (Nat.le_max_left x (bitWidth a)) (ih (max x (bitWidth a)))

/-- foldl (max ∘ bitWidth) 关于初值单调。 -/
lemma foldl_max_mono (l : List ℕ) (x y : ℕ) (hxy : x ≤ y) :
    l.foldl (fun m w => max m (bitWidth w)) x ≤ l.foldl (fun m w => max m (bitWidth w)) y := by
  induction l generalizing x y with
  | nil => simpa using hxy
  | cons a rest ih =>
      simp only [List.foldl_cons]
      exact ih (max x (bitWidth a)) (max y (bitWidth a)) (max_le_max hxy (le_refl _))

/-- foldl (max ∘ bitWidth) 1 l ≥ 第 i 个元素的 bitWidth。 -/
lemma foldl_max_ge_elem (l : List ℕ) (i : ℕ) (hi : i < l.length) :
    bitWidth l[i] ≤ l.foldl (fun m w => max m (bitWidth w)) 1 := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a rest ih =>
      cases i with
      | zero =>
          simp only [List.foldl_cons]
          exact le_trans (Nat.le_max_right 1 (bitWidth a)) (foldl_max_ge rest (max 1 (bitWidth a)))
      | succ i =>
          simp only [List.foldl_cons]
          have hi' : i < rest.length := by simp at hi; exact hi
          exact le_trans (ih i hi') (foldl_max_mono rest 1 (max 1 (bitWidth a))
          (Nat.le_max_left 1 (bitWidth a)))



/-- 状态 84→20：清 target 区 4F4.4 标记（减完一个 sel 元素后复位计数器）。
    新协议：84 左扫到 #₀ → 85 左扫到 #ₗ → 86 右移清 m → 87 右扫到 #₀ → 20。 -/
lemma trans21_clear (s : Sym) (hs : s.1 = SymKind.data0 ∨ s.1 =
SymKind.data1 ∨ s.1 = SymKind.consumed) :
    { nextState := 21, writeSym := Sym.data0, moveDir := Dir.R } ∈
    VerifierSym.transition (21, s) := by
  rcases s with ⟨k, m⟩
  change k = SymKind.data0 ∨ k = SymKind.data1 ∨ k = SymKind.consumed at hs
  rcases hs with h | h | h <;> subst k <;> cases m <;> decide

/-- 状态 21 右移清 n 格（data0/data1/consumed → data0），遇 sel/nosel → 51 左移，遇 #₁ → 22。 -/
lemma expand_scan_headPos (n : ℕ) (p₀ : ℤ) (tape : ℤ → Sym)
    (hdata : ∀ i : ℕ, i < n → (tape (p₀ + (i : ℤ))).1 =
    SymKind.data0 ∨ (tape (p₀ + (i : ℤ))).1 = SymKind.consumed) :
    ∀ (π₁ : List SymStep) (cfg₁ : SymConfig),
      SymSteps VerifierSym.transition (SymConfig.mk 21 tape p₀) π₁ cfg₁ →
      π₁.length ≤ n → cfg₁.headPos = p₀ + (π₁.length : ℤ) ∧ cfg₁.state = 21 := by
  intro π₁ cfg₁ hπ₁ hlen
  refine Nat.strong_induction_on (p := fun m => ∀ (π₁ : List SymStep) (cfg₁ : SymConfig),
      π₁.length = m → SymSteps VerifierSym.transition (SymConfig.mk 21 tape p₀) π₁ cfg₁ →
      π₁.length ≤ n → cfg₁.headPos =
      p₀ + (m : ℤ) ∧ cfg₁.state = 21) π₁.length ?_ π₁ cfg₁ rfl hπ₁ hlen
  intro m ih π₁ cfg₁ hlen_m hπ₁ hlen
  cases hπ₁ with
  | nil => simp [SymConfig.mk, ← hlen_m]
  | cons π₀ step₀ cfg_before hπ₀ h_from h_read h_trans =>
      have hlen_m' : π₀.length + 1 = m := by simpa using hlen_m
      simp at hlen
      have hlen₀ : π₀.length ≤ n := by omega
      have hlt : π₀.length < m := by omega
      have hih₀ := ih π₀.length hlt π₀ cfg_before rfl hπ₀ hlen₀
      have hhead₀ : cfg_before.headPos = p₀ + (π₀.length : ℤ) := hih₀.1
      have hstate₀ : cfg_before.state = 21 := hih₀.2
      have hltn : π₀.length < n := by omega
      have hsym : (step₀.readSym).1 = SymKind.data0 ∨ (step₀.readSym).1 = SymKind.consumed := by
        rw [h_read]
        have htape_eq : cfg_before.tape (p₀ + (π₀.length : ℤ)) = tape (p₀ + (π₀.length : ℤ)) := by
          apply SymSteps_tape_of_headPos_le VerifierSym.transition (SymConfig.mk 21 tape p₀) cfg_before π₀ (p₀ + (π₀.length : ℤ) - 1) hπ₀
          · intro π₀₁ step₀₁ π₀₂ cfg₀₁ hπ₀_eq hπ₀₁
            have hπ₀₁_lt : π₀₁.length < π₀.length := by
              rw [hπ₀_eq]
              simp
            have hlen₀₁ : π₀₁.length ≤ n := by omega
            have hlt₁ : π₀₁.length < m := by omega
            have hih₁ := ih π₀₁.length hlt₁ π₀₁ cfg₀₁ rfl hπ₀₁ hlen₀₁
            have hhead₀₁ : cfg₀₁.headPos = p₀ + (π₀₁.length : ℤ) := hih₁.1
            omega
          · omega
        have htape_eq' : cfg_before.tape cfg_before.headPos = tape (p₀ + (π₀.length : ℤ)) := by
          rw [hhead₀]
          exact htape_eq
        rw [htape_eq']
        exact hdata (π₀.length) hltn
      have hsym' : (cfg_before.tape cfg_before.headPos).1 = SymKind.data0 ∨ (cfg_before.tape cfg_before.headPos).1 = SymKind.consumed := by
        simpa [h_read] using hsym
      have hres : step₀.result = { nextState := 21, writeSym := Sym.data0, moveDir := Dir.R } := by
        rw [hstate₀] at h_trans
        cases hcfg : cfg_before.tape cfg_before.headPos with
        | mk k m =>
            rw [hcfg] at hsym' h_trans
            simp [Sym.mk] at hsym' h_trans
            rcases hsym' with hd | hd
            · have hk : k = SymKind.data0 := by simpa using hd
              subst k
              have hsgl : VerifierSym.transition (21, (SymKind.data0, m)) =
                  ({ { nextState := 21, writeSym := Sym.data0, moveDir := Dir.R } } : Finset SymTransResult) := by
                cases m <;> decide
              rw [hsgl] at h_trans
              simpa using h_trans
            · have hk : k = SymKind.consumed := by simpa using hd
              subst k
              have hsgl : VerifierSym.transition (21, (SymKind.consumed, m)) =
                  ({ { nextState := 21, writeSym := Sym.data0, moveDir := Dir.R } } : Finset SymTransResult) := by
                cases m <;> decide
              rw [hsgl] at h_trans
              simpa using h_trans
      simp [SymConfig.mk, symStepConfig, hres, Dir.toInt, hhead₀]
      omega

/-- 状态 21 右移清 n 格（data0/consumed → data0），扫到 sel/nosel → 51 写回 L
    boundary → 22 写回 S。 -/
lemma expand_scan (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hdata : ∀ i : ℕ, i < n → (tape (p + (i : ℤ))).1 = SymKind.data0 ∨ (tape (p + (i : ℤ))).1 = SymKind.consumed)
    (hend : (tape (p + (n : ℤ))).1 = SymKind.sel ∨ (tape (p + (n : ℤ))).1 = SymKind.nosel ∨
      (tape (p + (n : ℤ))).1 = SymKind.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 21 tape p) π cfg' ∧
      tapeAgrees cfg'.tape p (List.replicate n Sym.data0) ∧
      (cfg'.state = 51 ∧ cfg'.tape (p + (n : ℤ)) = tape (p + (n : ℤ)) ∧ cfg'.headPos = p + (n : ℤ) - 1
       ∨ cfg'.state = 22 ∧ (cfg'.tape (p + (n : ℤ))).1 = SymKind.boundary ∧ cfg'.headPos = p + (n : ℤ) ∧
          cfg'.tape (p + (n : ℤ)) = tape (p + (n : ℤ))) ∧
      π.length = n + 1 ∧
      (∀ i : ℤ, i < p → cfg'.tape i = tape i) ∧
      (∀ i : ℤ, p + (n : ℤ) < i → cfg'.tape i = tape i) ∧
      ((tape (p + (n : ℤ))).1 = SymKind.sel ∨ (tape (p + (n : ℤ))).1 = SymKind.nosel → cfg'.state = 51) ∧
      ((tape (p + (n : ℤ))).1 = SymKind.boundary → cfg'.state = 22) := by
  induction n generalizing p tape with
  | zero =>
      rcases hend with hsel | hnosel | hbound
      · let r : SymTransResult := { nextState := 51, writeSym := tape p, moveDir := Dir.L }
        let step : SymStep := { fromState := 21, readSym := tape p, result := r }
        have hstep : SymSteps VerifierSym.transition (SymConfig.mk 21 tape p) [step]
            (symStepConfig (SymConfig.mk 21 tape p) step.result) := by
          refine SymSteps.cons [] step (SymConfig.mk 21 tape p) SymSteps.nil ?_ ?_ ?_
          · rfl
          · rfl
          · change step.result ∈ VerifierSym.transition (21, tape p)
            cases htape : tape p with
            | mk k m =>
                have hk : k = SymKind.sel := by simpa [htape] using hsel
                subst k
                change { nextState := 51, writeSym := tape p, moveDir := Dir.L } ∈
                  VerifierSym.transition (21, (SymKind.sel, m))
                rw [show tape p = (SymKind.sel, m) from htape]
                cases m <;> decide
        refine ⟨[step], symStepConfig (SymConfig.mk 21 tape p) step.result, hstep, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro i hi; simp at hi
        · left
          refine ⟨rfl, ?_, ?_⟩
          · simp [add_zero, symStepConfig, SymConfig.mk, step, r]
          · simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
            omega
        · simp
        · -- hleft：i < p 未动
          intro i hi
          simp [symStepConfig, SymConfig.mk, step, r, show i ≠ p from by omega]
        · -- hright：p < i 未动
          intro i hi
          simp [symStepConfig, SymConfig.mk, step, r, show i ≠ p from by omega]
        · intro hs; rfl
        · intro hb
          exfalso
          have hsel' : (tape p).1 = SymKind.sel := by simpa using hsel
          have hb' : (tape p).1 = SymKind.boundary := by simpa using hb
          rw [hb'] at hsel'
          cases hsel'
      · let r : SymTransResult := { nextState := 51, writeSym := tape p, moveDir := Dir.L }
        let step : SymStep := { fromState := 21, readSym := tape p, result := r }
        have hstep : SymSteps VerifierSym.transition (SymConfig.mk 21 tape p) [step]
            (symStepConfig (SymConfig.mk 21 tape p) step.result) := by
          refine SymSteps.cons [] step (SymConfig.mk 21 tape p) SymSteps.nil ?_ ?_ ?_
          · rfl
          · rfl
          · change step.result ∈ VerifierSym.transition (21, tape p)
            cases htape : tape p with
            | mk k m =>
                have hk : k = SymKind.nosel := by simpa [htape] using hnosel
                subst k
                change { nextState := 51, writeSym := tape p, moveDir := Dir.L } ∈
                  VerifierSym.transition (21, (SymKind.nosel, m))
                rw [show tape p = (SymKind.nosel, m) from htape]
                cases m <;> decide
        refine ⟨[step], symStepConfig (SymConfig.mk 21 tape p) step.result, hstep, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro i hi; simp at hi
        · left
          refine ⟨rfl, ?_, ?_⟩
          · simp [add_zero, symStepConfig, SymConfig.mk, step, r]
          · simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
            omega
        · simp
        · -- hleft：i < p 未动
          intro i hi
          simp [symStepConfig, SymConfig.mk, step, r, show i ≠ p from by omega]
        · -- hright：p < i 未动
          intro i hi
          simp [symStepConfig, SymConfig.mk, step, r, show i ≠ p from by omega]
        · intro hs; rfl
        · intro hb
          exfalso
          have hnosel' : (tape p).1 = SymKind.nosel := by simpa using hnosel
          have hb' : (tape p).1 = SymKind.boundary := by simpa using hb
          rw [hb'] at hnosel'
          cases hnosel'
      · let r : SymTransResult := { nextState := 22, writeSym := tape p, moveDir := Dir.S }
        let step : SymStep := { fromState := 21, readSym := tape p, result := r }
        have hstep : SymSteps VerifierSym.transition (SymConfig.mk 21 tape p) [step]
            (symStepConfig (SymConfig.mk 21 tape p) step.result) := by
          refine SymSteps.cons [] step (SymConfig.mk 21 tape p) SymSteps.nil ?_ ?_ ?_
          · rfl
          · rfl
          · change step.result ∈ VerifierSym.transition (21, tape p)
            rcases htape : tape p with ⟨k, m⟩
            have hk : k = SymKind.boundary := by simpa [htape] using hbound
            subst k
            have hstep' : step.result = { nextState := 22, writeSym := (SymKind.boundary, m), moveDir := Dir.S } := by
              dsimp [step, r]
              rw [htape]
            rw [hstep']
            cases m <;> decide
        refine ⟨[step], symStepConfig (SymConfig.mk 21 tape p) step.result, hstep, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro i hi; simp at hi
        · right
          refine ⟨rfl, ?_, ?_, ?_⟩
          · simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
            simpa using hbound
          · simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
          · -- cfg'.tape p = tape p（! 写回读值）
            simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
        · simp
        · -- hleft：i < p 未动
          intro i hi
          simp [symStepConfig, SymConfig.mk, step, r, show i ≠ p from by omega]
        · -- hright：p < i 未动
          intro i hi
          simp [symStepConfig, SymConfig.mk, step, r, show i ≠ p from by omega]
        · intro hs
          exfalso
          have hb1 : (tape p).1 = SymKind.boundary := by simpa using hbound
          rcases hs with hk | hk
          · have hk' : (tape p).1 = SymKind.sel := by simpa using hk
            rw [hk'] at hb1
            cases hb1
          · have hk' : (tape p).1 = SymKind.nosel := by simpa using hk
            rw [hk'] at hb1
            cases hb1
        · intro hb; rfl
  | succ n ih =>
      have h0 := hdata 0 (by omega)
      let r : SymTransResult := { nextState := 21, writeSym := Sym.data0, moveDir := Dir.R }
      let step : SymStep := { fromState := 21, readSym := tape p, result := r }
      have htrans : step.result ∈ VerifierSym.transition (21, tape p) := by
        have h0' : (tape p).1 = SymKind.data0 ∨ (tape p).1 = SymKind.consumed := by
          simpa using h0
        have h0'' : (tape p).1 = SymKind.data0 ∨ (tape p).1 = SymKind.data1 ∨ (tape p).1 = SymKind.consumed := by
          rcases h0' with h | h
          · left; exact h
          · right; right; exact h
        exact trans21_clear (tape p) h0''
      let tape1 : ℤ → Sym := fun i => if i = p then Sym.data0 else tape i
      have hstep : SymSteps VerifierSym.transition (SymConfig.mk 21 tape p) [step]
          (symStepConfig (SymConfig.mk 21 tape p) step.result) := by
        refine SymSteps.cons [] step (SymConfig.mk 21 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans
      have hcfg : symStepConfig (SymConfig.mk 21 tape p) step.result = SymConfig.mk 21 tape1 (p + 1) := by
        simp [symStepConfig, SymConfig.mk, step, r, tape1, Dir.toInt]
      have hdata1 : ∀ i : ℕ, i < n → (tape1 (p + 1 + (i : ℤ))).1 = SymKind.data0 ∨
          (tape1 (p + 1 + (i : ℤ))).1 = SymKind.consumed := by
        intro i hi
        have h := hdata (i + 1) (by omega)
        have htape : tape1 (p + 1 + (i : ℤ)) = tape (p + ((i + 1 : ℕ) : ℤ)) := by
          simp only [tape1]
          rw [if_neg (by omega : p + 1 + (i : ℤ) ≠ p)]
          exact congrArg tape (by omega)
        rw [htape]
        exact h
      have hend1 : (tape1 (p + 1 + (n : ℤ))).1 = SymKind.sel ∨ (tape1 (p + 1 + (n : ℤ))).1 = SymKind.nosel ∨
          (tape1 (p + 1 + (n : ℤ))).1 = SymKind.boundary := by
        have htape : tape1 (p + 1 + (n : ℤ)) = tape (p + ((n + 1 : ℕ) : ℤ)) := by
          simp only [tape1]
          rw [if_neg (by omega : p + 1 + (n : ℤ) ≠ p)]
          exact congrArg tape (by omega)
        rcases hend with hsel | hnosel | hbound
        · left
          rw [htape]
          simpa using hsel
        · right; left
          rw [htape]
          simpa using hnosel
        · right; right
          rw [htape]
          simpa using hbound
      rcases ih (p + 1) tape1 hdata1 hend1 with ⟨π, cfg', hπ, hta, hend', hπlen, hleft_ih, hright_ih, hsep_imp_ih, hboundary_imp_ih⟩
      refine ⟨[step] ++ π, cfg', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact SymSteps_trans VerifierSym.transition (SymConfig.mk 21 tape p)
          (SymConfig.mk 21 tape1 (p + 1)) cfg' [step] π (by simpa [hcfg] using hstep) hπ
      · intro i hi
        cases i with
        | zero =>
            have hkeep : cfg'.tape p = (SymConfig.mk 21 tape1 (p + 1)).tape p := by
              apply SymSteps_tape_of_headPos_ge VerifierSym.transition (SymConfig.mk 21 tape1 (p + 1)) cfg' π (p + 1) hπ
              · intro π₁ step₁ π₂ cfg₁ hπ_eq hπ₁
                have hπlen₁ : π₁.length ≤ n := by
                  have hlt : π₁.length < π.length := by
                    rw [hπ_eq]
                    simp
                  rw [hπlen] at hlt
                  omega
                have hhead₁ : cfg₁.headPos = p + 1 + (π₁.length : ℤ) :=
                  (expand_scan_headPos n (p + 1) tape1 hdata1 π₁ cfg₁ hπ₁ hπlen₁).1
                omega
              · omega
            simpa [SymConfig.mk, tape1] using hkeep
        | succ i =>
            have h := hta i (by simpa using hi)
            rw [show (p + ((i + 1 : ℕ) : ℤ)) = (p + 1 + (i : ℤ)) from by omega]
            exact h
      · rcases hend' with h4 | h22
        · left
          rcases h4 with ⟨hs4, hb, hhead⟩
          refine ⟨hs4, ?_, ?_⟩
          · rw [show (p + ((n + 1 : ℕ) : ℤ)) = (p + 1) + (n : ℤ) from by omega]
            rw [show tape1 (p + 1 + (n : ℤ)) = tape (p + 1 + (n : ℤ)) from by
              simp only [tape1]
              rw [if_neg (by omega : p + 1 + (n : ℤ) ≠ p)]] at hb
            exact hb
          · rw [hhead]
            omega
        · right
          rcases h22 with ⟨hs22, hb, hhead, hkeep⟩
          refine ⟨hs22, ?_, ?_, ?_⟩
          · rw [show (p + ((n + 1 : ℕ) : ℤ)) = (p + 1) + (n : ℤ) from by omega]
            exact hb
          · rw [hhead]
            omega
          · -- cfg'.tape (p + (n+1)) = tape (p + (n+1))（ih 值保持）
            have hk' : cfg'.tape (p + ((n + 1 : ℕ) : ℤ)) = tape1 (p + ((n + 1 : ℕ) : ℤ)) := by
              rw [show p + ((n + 1 : ℕ) : ℤ) = (p + 1) + (n : ℤ) from by omega]
              exact hkeep
            have ht1 : tape1 (p + ((n + 1 : ℕ) : ℤ)) = tape (p + ((n + 1 : ℕ) : ℤ)) := by
              simp only [tape1]
              rw [if_neg (by omega : p + ((n + 1 : ℕ) : ℤ) ≠ p)]
            rw [hk', ht1]
      · simp [hπlen]
      · -- hleft：i < p 未动（ih 从 p+1 起）
        intro i hi
        have h := hleft_ih i (by omega)
        rw [h]
        simp [tape1, show i ≠ p from by omega]
      · -- hright：p + (n+1) < i（ih 从 p+1+n 起）
        intro i hi
        have h := hright_ih i (by omega)
        rw [h]
        simp [tape1, show i ≠ p from by omega]
      · intro hs
        have hs1 : (tape1 (p + 1 + (n : ℤ))).1 =
        SymKind.sel ∨ (tape1 (p + 1 + (n : ℤ))).1 = SymKind.nosel := by
          rcases hs with hsel | hnosel
          · left
            simp only [tape1]
            rw [if_neg (by omega : p + 1 + (n : ℤ) ≠ p)]
            simpa [show p + (↑n + 1) = p + 1 + (n : ℤ) from by omega] using hsel
          · right
            simp only [tape1]
            rw [if_neg (by omega : p + 1 + (n : ℤ) ≠ p)]
            simpa [show p + (↑n + 1) = p + 1 + (n : ℤ) from by omega] using hnosel
        exact hsep_imp_ih hs1
      · intro hb
        have hb1 : (tape1 (p + 1 + (n : ℤ))).1 = SymKind.boundary := by
          simp only [tape1]
          rw [if_neg (by omega : p + 1 + (n : ℤ) ≠ p)]
          simpa [show p + (↑n + 1) = p + 1 + (n : ℤ) from by omega] using hb
        exact hboundary_imp_ih hb1

/-- 状态 16→20：清 target 区 4F4.4 标记（减完一个 sel 元素后复位计数器）。 -/
lemma blocksJoin_last_data (blocks : List (Sym × List Sym))
    (hblocks : ∀ b ∈ blocks, (b.1 = Sym.sel ∨ b.1 = Sym.nosel) ∧ b.2 ≠ [] ∧
      (∀ s ∈ b.2, (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false))
    (hne : blocks ≠ []) :
    let els := joinLists (List.map (fun b => [b.1] ++ b.2) blocks)
    let s := els[els.length - 1]'(Nat.pred_lt (ne_of_gt ((List.length_pos_iff_ne_nil).mpr
      (blocksJoin_ne_nil blocks hne (by intro b hb; exact (hblocks b hb).2.1)))))
    (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false := by
  intro els s
  have hfin : els.length - 1 < els.length := Nat.pred_lt (ne_of_gt ((List.length_pos_iff_ne_nil).mpr
    (blocksJoin_ne_nil blocks hne (by intro b hb; exact (hblocks b hb).2.1))))
  have hs : s = els[els.length - 1]'hfin := rfl
  induction blocks using List.reverseRecOn with
  | nil => exfalso; exact hne rfl
  | append_singleton bs b ih =>
      have hb_mem : b ∈ bs ++ [b] := by simp
      have hbb := hblocks b hb_mem
      have hb2ne : b.2 ≠ [] := hbb.2.1
      have hb2pos : 0 < b.2.length := (List.length_pos_iff_ne_nil).mpr hb2ne
      have hb2idx : b.2.length - 1 < b.2.length := Nat.pred_lt (ne_of_gt hb2pos)
      have hels_eq : els = joinLists (bs.map (fun b => [b.1] ++ b.2)) ++ ([b.1] ++ b.2) := by
        simp [els, List.map_append, joinLists_append, joinLists_cons, joinLists_nil]
      have hcell : els[els.length - 1]'hfin = b.2[b.2.length - 1]'hb2idx := by
        simp only [hels_eq]
        have hlen : (joinLists (bs.map (fun b => [b.1] ++ b.2)) ++ ([b.1] ++ b.2)).length =
            (joinLists (bs.map (fun b => [b.1] ++ b.2))).length + 1 + b.2.length := by
          rw [List.length_append, List.length_append, List.length_singleton]
          omega
        rw [List.getElem_append_right (by
          rw [hlen]
          omega)]
        rw [List.getElem_append_right (by
          rw [List.length_singleton, hlen]
          omega)]
        have hidx : (joinLists (bs.map (fun b => [b.1] ++ b.2))).length + 1 + b.2.length - 1 -
            (joinLists (bs.map (fun b => [b.1] ++ b.2))).length - 1 = b.2.length - 1 := by
          omega
        simp only [hlen, List.length_singleton, hidx]
      have hmem : b.2[b.2.length - 1]'hb2idx ∈ b.2 := by
        exact List.getElem_mem hb2idx
      have hdata := hbb.2.2 (b.2[b.2.length - 1]'hb2idx) hmem
      constructor
      · rw [hs, hcell]
        exact hdata.1
      · rw [hs, hcell]
        exact hdata.2

/-- joinLists 的长度与 encodeElementsSym 相同。 -/
lemma joinLists_map_sel_len (elems : List ℕ) :
    (joinLists (elems.map (fun v => [Sym.sel] ++ encodeBitsSymNative v))).length =
      (encodeElementsSym elems).length := by
  induction elems with
  | nil => rfl
  | cons v rest ih =>
      rw [List.map_cons, joinLists_cons, List.length_append, List.length_append]
      cases rest with
      | nil => simp [encodeElementsSym, ih, joinLists]; omega
      | cons w rest' =>
          rw [ih]
          simp [encodeElementsSym, joinLists, List.length_append]
          omega

/-- 块的最高位（最右格，LSB 左布局）是 data1：元素值 > 0 / 无前导 0（格式检查 24/26/27 要求）。 -/
def blockTopIs1 (b : Sym × List Sym) : Prop :=
  ∀ hne : b.2 ≠ [], (b.2[b.2.length - 1]'(Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hne) (by norm_num))).1 = SymKind.data1

/-- 从右往左第一个 data1 的偏移 k：l[len-1-k] = data1，其右（偏移 < k）全 data0。 -/
lemma first_data1_from_right (l : List Sym)
    (hdata : ∀ s ∈ l, (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false)
    (hne : l ≠ [])
    (hpos : ∃ s ∈ l, s.1 = SymKind.data1) :
    ∃ k : ℕ, k < l.length ∧ l[l.length - 1 - k]'(by
        by_cases hklt : k < l.length
        · omega
        · have h0 : l.length - 1 - k = 0 := by
            rw [Nat.sub_eq_zero_of_le (by omega : l.length - 1 ≤ k)]
          rw [h0]
          exact List.length_pos_iff_ne_nil.mpr hne) = Sym.data1 ∧
      ∀ j : ℕ, j < k → l[l.length - 1 - j]'(by
        by_cases hjlt : j < l.length
        · omega
        · have h0 : l.length - 1 - j = 0 := by
            rw [Nat.sub_eq_zero_of_le (by omega : l.length - 1 ≤ j)]
          rw [h0]
          exact List.length_pos_iff_ne_nil.mpr hne) = Sym.data0 := by
  induction l using List.reverseRecOn with
  | nil =>
      rcases hpos with ⟨s, hs, _⟩
      simp at hs
  | append_singleton l' d ih =>
      by_cases hd1 : d.1 = SymKind.data1
      · have hd : d = Sym.data1 := by
          rcases (hdata d (by simp)) with ⟨hk, hm⟩
          rcases d with ⟨k0, m⟩
          dsimp at hd1 hm hk ⊢
          subst k0
          subst m
          rfl
        refine ⟨0, by simp, ?_, ?_⟩
        · simp [List.length_append, hd]
        · intro j hj
          simp at hj
      · have hd0 : d.1 = SymKind.data0 := by
          rcases (hdata d (by simp)) with ⟨hk, hm⟩
          rcases hk with hk | hk
          · exact hk
          · exact False.elim (hd1 hk)
        have hpos' : ∃ s ∈ l', s.1 = SymKind.data1 := by
          rcases hpos with ⟨s, hs, hk⟩
          have hs' : s ∈ l' := by
            simp at hs
            rcases hs with hs | hd_eq
            · exact hs
            · subst s
              exact False.elim (hd1 hk)
          exact ⟨s, hs', hk⟩
        have hne' : l' ≠ [] := by
          intro h'
          rcases hpos' with ⟨s, hs, _⟩
          simp [h'] at hs
        rcases ih (by intro s hs; exact hdata s (by simp [hs])) hne' hpos' with ⟨k, hk_lt, hk1, hk0s⟩
        refine ⟨k + 1, ?_, ?_, ?_⟩
        · simp [List.length_append]
          omega
        · have hlen : (l' ++ [d]).length = l'.length + 1 := by simp
          have hg : (l' ++ [d])[(l' ++ [d]).length - 1 - (k + 1)]'(by omega) =
              (l' ++ [d])[l'.length - 1 - k]'(by omega) := by
            congr 1
            rw [hlen]
            omega
          rw [hg]
          rw [List.getElem_append_left (by omega : l'.length - 1 - k < l'.length)]
          exact hk1
        · intro j hj
          cases j with
          | zero =>
              have hlen : (l' ++ [d]).length = l'.length + 1 := by simp
              have hd0' : d = Sym.data0 := by
                rcases (hdata d (by simp)) with ⟨hk, hm⟩
                rcases d with ⟨k0, m⟩
                dsimp at hd0 hm ⊢
                subst k0
                subst m
                rfl
              have hg : (l' ++ [d])[(l' ++ [d]).length - 1 - 0]'(by omega) =
                  (l' ++ [d])[l'.length]'(by omega) := by
                congr 1
                rw [hlen]
                omega
              rw [hg]
              rw [List.getElem_append_right (by omega : l'.length ≤ l'.length)]
              simpa [hd0']
          | succ j' =>
              have hj' : j' < k := by omega
              have hlen : (l' ++ [d]).length = l'.length + 1 := by simp
              have hg : (l' ++ [d])[(l' ++ [d]).length - 1 - (j' + 1)]'(by omega) =
                  (l' ++ [d])[l'.length - 1 - j']'(by omega) := by
                congr 1
                rw [hlen]
                omega
              rw [hg]
              rw [List.getElem_append_left (by omega : l'.length - 1 - j' < l'.length)]
              exact hk0s j' hj'

/-- α/β 换 sel 的逐格替换。 -/
lemma format_sweep_rec_from26 (blocks : List (Sym × List Sym)) (tgt : List Sym) (p₀ : ℤ) (tape : ℤ → Sym)
    (hblocks : ∀ b ∈ blocks, (b.1 = Sym.sel ∨ b.1 = Sym.nosel) ∧ b.2 ≠ [] ∧
      (∀ s ∈ b.2, (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false))
    (hpos : ∀ b ∈ blocks, blockTopIs1 b)
    (hels : tapeAgrees tape p₀ (joinLists (blocks.map (fun b => [b.1] ++ b.2))))
    (htgt : tapeAgrees tape (p₀ - (tgt.length : ℤ) - 1) tgt)
    (htgt_data : ∀ s ∈ tgt, (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false)
    (hne_tgt : tgt ≠ [])
    (hmid : tape (p₀ - 1) = Sym.boundary)
    (hleft : tape (p₀ - (tgt.length : ℤ) - 2) = Sym.boundary)
    (hne_blocks : blocks ≠ []) :
    ∃ π cfg', SymSteps VerifierSym.transition
      (SymConfig.mk 26 tape (p₀ + ((joinLists (blocks.map (fun b => [b.1] ++ b.2))).length : ℤ) - 1)) π cfg' ∧
      cfg'.state = 27 ∧ cfg'.headPos = p₀ - 2 ∧ cfg'.tape = tape := by
  let f : Sym × List Sym → List Sym := fun b => [b.1] ++ b.2
  induction blocks using List.reverseRecOn generalizing p₀ tape with
  | nil => exfalso; exact hne_blocks rfl
  | append_singleton bs b ih =>
      let els' : List Sym := joinLists (bs.map f)
      let els : List Sym := els' ++ f b
      have hels_eq : els = joinLists ((bs ++ [b]).map f) := by
        simp [els, els', f, List.map_append, joinLists_append, joinLists_cons, joinLists_nil]
      have hb_mem : b ∈ bs ++ [b] := by simp
      have hbb := hblocks b hb_mem
      have hb1 : b.1 = Sym.sel ∨ b.1 = Sym.nosel := hbb.1
      have hb2ne : b.2 ≠ [] := hbb.2.1
      have hb2_data : ∀ s ∈ b.2, (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false := hbb.2.2
      have hb1m : b.1.2 = false := by rcases hb1 with h | h <;> simp [h, Sym.sel, Sym.nosel, Sym.mk]
      have helen : (els.length : ℤ) = (els'.length : ℤ) + 1 + (b.2.length : ℤ) := by
        simp [els, els', f]
        omega
      have htape_els : tapeAgrees tape p₀ els := by
        intro i hi
        rw [hels_eq] at hi
        have h := hels i hi
        simp only [hels_eq]
        exact h
      -- 定位 b.2 从右往左第一个 data1（最右位 d1 → 29 直接；d0 → 拒绝）
      have hb2_pos : ∃ s ∈ b.2, s.1 = SymKind.data1 := by
        refine ⟨b.2[b.2.length - 1]'(Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hb2ne) (by norm_num)), ?_, ?_⟩
        · exact List.getElem_mem _
        · exact hpos b hb_mem hb2ne
      rcases first_data1_from_right b.2 hb2_data hb2ne hb2_pos with ⟨k, hk_lt, hk1, hk0s⟩
      have hk_le : k ≤ b.2.length - 1 := by omega
      have hk1_le : k + 1 ≤ b.2.length := by omega
      have hcast_k : ((b.2.length - 1 - k : ℕ) : ℤ) = (b.2.length : ℤ) - 1 - (k : ℤ) := by
        rw [show b.2.length - 1 - k = b.2.length - (k + 1) from by omega]
        rw [Nat.cast_sub hk1_le]
        rw [Nat.cast_add]
        norm_num
        omega
      -- 24 读最右位（els 最后一位 = b.2 的 last）
      have hlast_tape24 : tape (p₀ + (els.length : ℤ) - 1) = els[els.length - 1]'(by omega) := by
        have hne' : els ≠ [] := by
          simpa [f, els, els', hels_eq] using (blocksJoin_ne_nil (bs ++ [b]) hne_blocks (by intro b' hb'; exact (hblocks b' hb').2.1))
        have hidx : els.length - 1 < els.length := Nat.pred_lt (ne_of_gt ((List.length_pos_iff_ne_nil).mpr hne'))
        have h := htape_els (els.length - 1) hidx
        have hcast : p₀ + ↑(els.length - 1) = p₀ + ↑els.length - 1 := by
          rw [Nat.cast_pred (by exact (List.length_pos_iff_ne_nil).mpr hne')]
          omega
        rw [congrArg tape hcast] at h
        exact h
      have hlen_nat : els.length = els'.length + 1 + b.2.length := by
        simp [els, els', f]
        omega
      have hlast_cell : els[els.length - 1]'(by omega) = b.2[b.2.length - 1]'(by omega) := by
        have hidx0 : els.length - 1 < (els' ++ ([b.1] ++ b.2)).length := by
          rw [List.length_append, List.length_append, List.length_singleton]
          omega
        change (els' ++ ([b.1] ++ b.2))[els.length - 1]'hidx0 = b.2[b.2.length - 1]'(by omega)
        rw [List.getElem_append_right (by
          rw [hlen_nat]
          omega)]
        rw [List.getElem_append_right (by
          rw [List.length_singleton]
          omega)]
        have hidx' : els.length - 1 - els'.length - [b.1].length = b.2.length - 1 := by
          rw [List.length_singleton]
          rw [hlen_nat]
          omega
        simp only [hidx']
      have hlast_m : (tape (p₀ + (els.length : ℤ) - 1)).2 = false := by
        rw [hlast_tape24, hlast_cell]
        rcases (hb2_data (b.2[b.2.length - 1]'(by omega)) (List.getElem_mem (by omega))) with ⟨_, hm⟩
        exact hm
      have hb1k : b.1.1 = SymKind.sel ∨ b.1.1 = SymKind.nosel := by
        rcases hb1 with h | h
        · left; rw [h]; rfl
        · right; rw [h]; rfl
      -- 段 2（29 扫剩余数据 → 选择符 → 26）；起点 p29 = 偏移 k+1 位置
      let p29 : ℤ := p₀ + (els.length : ℤ) - (k : ℤ) - 2
      have hkeep29 : ∀ i : ℤ, p29 - ((b.2.length - 1 - k : ℕ) : ℤ) < i ∧ i ≤ p29 →
          { nextState := 29, writeSym := tape i, moveDir := Dir.L } ∈ VerifierSym.transition (29, tape i) := by
        intro i h
        have hi' : p₀ + (els'.length : ℤ) < i := by
          have hk' := h.1
          rw [show p29 - ((b.2.length - 1 - k : ℕ) : ℤ) = p₀ + (els'.length : ℤ) from by
            dsimp [p29]
            rw [hcast_k]
            rw [helen]
            omega] at hk'
          exact hk'
        have hio : ∃ io : ℕ, (io : ℤ) = i - p₀ := by
          refine ⟨(i - p₀).toNat, ?_⟩
          exact Int.toNat_of_nonneg (by omega : 0 ≤ i - p₀)
        rcases hio with ⟨io, hio_eq⟩
        have hio_lt : io < els.length := by omega
        have hidx : p₀ + (io : ℤ) = i := by omega
        have hcell : tape i = els[io] := by
          rw [← hidx]
          exact htape_els io hio_lt
        have hio_ge : els'.length + 1 ≤ io := by omega
        have hio_lt2 : io < els'.length + 1 + b.2.length := by omega
        have hcell' : els[io] = b.2[io - (els'.length + 1)]'(by omega) := by
          have hio_ltX : io < (els' ++ ([b.1] ++ b.2)).length := by
            rw [List.length_append, List.length_append, List.length_singleton]
            omega
          change (els' ++ ([b.1] ++ b.2))[io]'hio_ltX = b.2[io - (els'.length + 1)]'(by omega)
          rw [List.getElem_append_right (by omega)]
          rw [List.getElem_append_right (by
            rw [List.length_singleton]
            omega)]
          have hidx' : io - els'.length - [b.1].length = io - (els'.length + 1) := by
            rw [List.length_singleton]
            omega
          simp only [hidx']
        have hmem : b.2[io - (els'.length + 1)] ∈ b.2 := List.getElem_mem (by omega)
        have hdata := hb2_data (b.2[io - (els'.length + 1)]) hmem
        have hk : (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1 := by
          rw [hcell, hcell']
          exact hdata.1
        have hm : (tape i).2 = false := by
          rw [hcell, hcell']
          exact hdata.2
        exact trans29_data (tape i) hk hm
      have hb29_end : tape (p29 - ((b.2.length - 1 - k : ℕ) : ℤ)) = b.1 := by
        have heq : p29 - ((b.2.length - 1 - k : ℕ) : ℤ) = p₀ + (els'.length : ℤ) := by
          dsimp [p29]
          rw [hcast_k]
          rw [helen]
          omega
        rw [heq]
        have hcell : tape (p₀ + (els'.length : ℤ)) = els[els'.length]'(by omega) :=
          htape_els els'.length (by omega)
        rw [hcell]
        rw [show els[els'.length] = b.1 from by
          have hidx0 : els'.length < (els' ++ ([b.1] ++ b.2)).length := by
            rw [List.length_append, List.length_append, List.length_singleton]
            omega
          change (els' ++ ([b.1] ++ b.2))[els'.length]'hidx0 = b.1
          rw [List.getElem_append_right (by omega)]
          have hidx1 : els'.length - els'.length = 0 := by omega
          simp only [hidx1]
          rfl]
      -- 入口：24 读最右位 → 25/29 找 1 → 29 态（段 2 起点 p29）
      have hentry : ∃ π0 cfg0, SymSteps VerifierSym.transition (SymConfig.mk 26 tape (p₀ + (els.length : ℤ) - 1)) π0 cfg0 ∧
          cfg0 = SymConfig.mk 29 tape p29 := by
        by_cases hk0 : k = 0
        · -- k=0：最右位是 data1：24 d1 → 29
          have hlast1 : tape (p₀ + (els.length : ℤ) - 1) = Sym.data1 := by
            rw [hlast_tape24, hlast_cell]
            simpa [hk0] using hk1
          let r24 : SymTransResult := { nextState := 29, writeSym := tape (p₀ + (els.length : ℤ) - 1), moveDir := Dir.L }
          let step24 : SymStep := { fromState := 26, readSym := tape (p₀ + (els.length : ℤ) - 1), result := r24 }
          have htrans24 : step24.result ∈ VerifierSym.transition (26, tape (p₀ + (els.length : ℤ) - 1)) := by
            exact trans26_data1 (tape (p₀ + (els.length : ℤ) - 1)) (congrArg (fun s : Sym => s.1) hlast1) hlast_m
          have hstep24 : SymSteps VerifierSym.transition (SymConfig.mk 26 tape (p₀ + (els.length : ℤ) - 1)) [step24]
              (symStepConfig (SymConfig.mk 26 tape (p₀ + (els.length : ℤ) - 1)) step24.result) := by
            refine SymSteps.cons [] step24 (SymConfig.mk 26 tape (p₀ + (els.length : ℤ) - 1)) SymSteps.nil ?_ ?_ ?_
            · rfl
            · rfl
            · exact htrans24
          have hcfg24 : symStepConfig (SymConfig.mk 26 tape (p₀ + (els.length : ℤ) - 1)) step24.result =
              SymConfig.mk 29 tape (p₀ + (els.length : ℤ) - 2) := by
            simp [symStepConfig, SymConfig.mk, step24, r24, Dir.toInt]
            constructor
            · funext i
              by_cases h : i = p₀ + (els.length : ℤ) - 1 <;> simp [h]
            · omega
          refine ⟨[step24], symStepConfig (SymConfig.mk 26 tape (p₀ + (els.length : ℤ) - 1)) step24.result, hstep24, ?_⟩
          rw [hcfg24]
          simp [p29, hk0]
        · -- k ≥ 1：最右位 data0，与 hpos（最高位 = data1）矛盾
          have hk0pos : 0 < k := by omega
          have hlast0 : tape (p₀ + (els.length : ℤ) - 1) = Sym.data0 := by
            rw [hlast_tape24, hlast_cell]
            simpa using hk0s 0 hk0pos
          have hcell0 : (b.2[b.2.length - 1]'(by omega)).1 = SymKind.data0 := by
            have hc : tape (p₀ + (els.length : ℤ) - 1) = b.2[b.2.length - 1]'(by omega) := by
              rw [hlast_tape24, hlast_cell]
            rw [hc] at hlast0
            simpa using congrArg (fun s : Sym => s.1) hlast0
          have hcell1 : (b.2[b.2.length - 1]'(by omega)).1 = SymKind.data1 := hpos b hb_mem hb2ne
          have : SymKind.data0 = SymKind.data1 := hcell0.symm.trans hcell1
          cases this
      rcases hentry with ⟨π0, cfg0, hπ0, hcfg0⟩
      rcases scanLeftKeepPos 29 26 b.1 Dir.L (b.2.length - 1 - k) p29 tape
        hkeep29 (trans29_sel b.1 hb1k hb1m) hb29_end with ⟨πb, cfgb, hπb, hsb, hheadb, htapeb⟩
      have hπb' : SymSteps VerifierSym.transition cfg0 πb cfgb := by
        simpa [hcfg0] using hπb
      have hcfgb : cfgb = SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1) := by
        rcases cfgb with ⟨s, t, hp⟩
        have ht : t = tape := by simpa using htapeb
        have hs : s = 26 := by simpa using hsb
        have hhp : hp = p₀ + (els.length : ℤ) - (k : ℤ) - 2 - ((b.2.length - 1 - k : ℕ) : ℤ) + (-1 : ℤ) := by
          simpa [Dir.toInt, p29] using hheadb
        subst t; subst s; subst hp
        simp [SymConfig.mk]
        rw [show p₀ + (els.length : ℤ) - (k : ℤ) - 2 - ((b.2.length - 1 - k : ℕ) : ℤ) + (-1 : ℤ) =
            p₀ + (els'.length : ℤ) - 1 from by
          have hk1_le : k + 1 ≤ b.2.length := by omega
          have hcast_k : ((b.2.length - 1 - k : ℕ) : ℤ) = (b.2.length : ℤ) - 1 - (k : ℤ) := by
            rw [show b.2.length - 1 - k = b.2.length - (k + 1) from by omega]
            rw [Nat.cast_sub hk1_le]
            rw [Nat.cast_add]
            norm_num
            omega
          rw [helen]
          rw [hcast_k]
          omega]
      by_cases hbs : bs = []
      · -- 26 读 #₀ → 27
        have hpos : p₀ + (els'.length : ℤ) - 1 = p₀ - 1 := by
          simp [els', hbs]
        have hmid' : tape (p₀ + (els'.length : ℤ) - 1) = Sym.boundary := by
          rw [hpos]
          exact hmid
        let r26 : SymTransResult := { nextState := 27, writeSym := Sym.boundary, moveDir := Dir.L }
        let step26 : SymStep := { fromState := 26, readSym := Sym.boundary, result := r26 }
        have htrans26 : step26.result ∈ VerifierSym.transition (26, Sym.boundary) := trans26_hash
        have hstep26 : SymSteps VerifierSym.transition (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) [step26]
            (symStepConfig (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) step26.result) := by
          refine SymSteps.cons [] step26 (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) SymSteps.nil ?_ ?_ ?_
          · rfl
          · change Sym.boundary = tape (p₀ + (els'.length : ℤ) - 1)
            rw [hmid']
          · change step26.result ∈ VerifierSym.transition (26, tape (p₀ + (els'.length : ℤ) - 1))
            rw [hmid']
            exact htrans26
        refine ⟨π0 ++ πb ++ [step26], symStepConfig (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) step26.result, ?_, ?_, ?_, ?_⟩
        · have hπ0' : SymSteps VerifierSym.transition (SymConfig.mk 26 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1)) π0 cfg0 := by
            convert hπ0 using 1
            rw [hels_eq]
          have h0b : SymSteps VerifierSym.transition (SymConfig.mk 26 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1)) (π0 ++ πb)
              (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) := by
            exact SymSteps_trans VerifierSym.transition (SymConfig.mk 26 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1)) cfg0
              (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) π0 πb hπ0' (hcfgb ▸ hπb')
          exact SymSteps_trans VerifierSym.transition (SymConfig.mk 26 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1))
            (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1))
            (symStepConfig (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) step26.result)
            (π0 ++ πb) [step26] h0b hstep26
        · rfl
        · change (symStepConfig (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) step26.result).headPos = p₀ - 2
          simp [symStepConfig, SymConfig.mk, step26, r26, Dir.toInt]
          omega
        · change (symStepConfig (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) step26.result).tape = tape
          simp [symStepConfig, SymConfig.mk, step26, r26]
          funext i
          by_cases h : i = p₀ + (els'.length : ℤ) - 1 <;> simp [h, hmid']
      · -- 26 读 els'.last（data）→ 25，接 ih
        have hbs' : bs ≠ [] := hbs
        have hblocks_bs : ∀ b' ∈ bs, (b'.1 = Sym.sel ∨ b'.1 = Sym.nosel) ∧ b'.2 ≠ [] ∧
            (∀ s ∈ b'.2, (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false) := by
          intro b' hb'
          exact hblocks b' (by simp [hb'])
        have hels_bs : tapeAgrees tape p₀ els' := by
          intro i hi
          have helen' := htape_els i (by
            rw [show els = els' ++ ([b.1] ++ b.2) from by simp [els, els', f]]
            rw [List.length_append, List.length_append, List.length_singleton]
            omega)
          have hcelli : els[i]'(by omega) = els'[i]'(by omega) := by
            change (els' ++ ([b.1] ++ b.2))[i]'(by
              rw [List.length_append, List.length_append, List.length_singleton]
              omega) = els'[i]'(by omega)
            rw [List.getElem_append_left (by omega)]
          rw [hcelli] at helen'
          exact helen'
        have hpos_bs : ∀ b' ∈ bs, blockTopIs1 b' := by
          intro b' hb'
          exact hpos b' (by simp [hb'])
        rcases ih p₀ tape hblocks_bs hpos_bs hels_bs htgt hmid hleft hbs' with ⟨π', cfg', hπ', hs', hhead', htape'⟩
        refine ⟨π0 ++ πb ++ π', cfg', ?_, hs', ?_, ?_⟩
        · have hπ0' : SymSteps VerifierSym.transition (SymConfig.mk 26 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1)) π0 cfg0 := by
            convert hπ0 using 1
            rw [hels_eq]
          have h0b : SymSteps VerifierSym.transition (SymConfig.mk 26 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1)) (π0 ++ πb)
              (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) := by
            exact SymSteps_trans VerifierSym.transition (SymConfig.mk 26 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1)) cfg0
              (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) π0 πb hπ0' (hcfgb ▸ hπb')
          have hπ'' : SymSteps VerifierSym.transition (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) π' cfg' := by
            simpa [f, els'] using hπ'
          exact SymSteps_trans VerifierSym.transition (SymConfig.mk 26 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1))
            (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) cfg' (π0 ++ πb) π' h0b hπ''
        · rw [hhead']
        · simpa using htape'

lemma format_sweep_rec (blocks : List (Sym × List Sym)) (tgt : List Sym) (p₀ : ℤ) (tape : ℤ → Sym)
    (hblocks : ∀ b ∈ blocks, (b.1 = Sym.sel ∨ b.1 = Sym.nosel) ∧ b.2 ≠ [] ∧
      (∀ s ∈ b.2, (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false))
    (hpos : ∀ b ∈ blocks, blockTopIs1 b)
    (hels : tapeAgrees tape p₀ (joinLists (blocks.map (fun b => [b.1] ++ b.2))))
    (htgt : tapeAgrees tape (p₀ - (tgt.length : ℤ) - 1) tgt)
    (htgt_data : ∀ s ∈ tgt, (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false)
    (hne_tgt : tgt ≠ [])
    (hmid : tape (p₀ - 1) = Sym.boundary)
    (hleft : tape (p₀ - (tgt.length : ℤ) - 2) = Sym.boundary)
    (hne_blocks : blocks ≠ []) :
    ∃ π cfg', SymSteps VerifierSym.transition
      (SymConfig.mk 24 tape (p₀ + ((joinLists (blocks.map (fun b => [b.1] ++ b.2))).length : ℤ) - 1)) π cfg' ∧
      cfg'.state = 27 ∧ cfg'.headPos = p₀ - 2 ∧ cfg'.tape = tape := by
  let f : Sym × List Sym → List Sym := fun b => [b.1] ++ b.2
  induction blocks using List.reverseRecOn generalizing p₀ tape with
  | nil => exfalso; exact hne_blocks rfl
  | append_singleton bs b ih =>
      let els' : List Sym := joinLists (bs.map f)
      let els : List Sym := els' ++ f b
      have hels_eq : els = joinLists ((bs ++ [b]).map f) := by
        simp [els, els', f, List.map_append, joinLists_append, joinLists_cons, joinLists_nil]
      have hb_mem : b ∈ bs ++ [b] := by simp
      have hbb := hblocks b hb_mem
      have hb1 : b.1 = Sym.sel ∨ b.1 = Sym.nosel := hbb.1
      have hb2ne : b.2 ≠ [] := hbb.2.1
      have hb2_data : ∀ s ∈ b.2, (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false := hbb.2.2
      have hb1m : b.1.2 = false := by rcases hb1 with h | h <;> simp [h, Sym.sel, Sym.nosel, Sym.mk]
      have helen : (els.length : ℤ) = (els'.length : ℤ) + 1 + (b.2.length : ℤ) := by
        simp [els, els', f]
        omega
      have htape_els : tapeAgrees tape p₀ els := by
        intro i hi
        rw [hels_eq] at hi
        have h := hels i hi
        simp only [hels_eq]
        exact h
      -- 定位 b.2 从右往左第一个 data1（最右位 d1 → 29 直接；d0 → 拒绝）
      have hb2_pos : ∃ s ∈ b.2, s.1 = SymKind.data1 := by
        refine ⟨b.2[b.2.length - 1]'(Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hb2ne) (by norm_num)), ?_, ?_⟩
        · exact List.getElem_mem _
        · exact hpos b hb_mem hb2ne
      rcases first_data1_from_right b.2 hb2_data hb2ne hb2_pos with ⟨k, hk_lt, hk1, hk0s⟩
      have hk_le : k ≤ b.2.length - 1 := by omega
      have hk1_le : k + 1 ≤ b.2.length := by omega
      have hcast_k : ((b.2.length - 1 - k : ℕ) : ℤ) = (b.2.length : ℤ) - 1 - (k : ℤ) := by
        rw [show b.2.length - 1 - k = b.2.length - (k + 1) from by omega]
        rw [Nat.cast_sub hk1_le]
        rw [Nat.cast_add]
        norm_num
        omega
      -- 24 读最右位（els 最后一位 = b.2 的 last）
      have hlast_tape24 : tape (p₀ + (els.length : ℤ) - 1) = els[els.length - 1]'(by omega) := by
        have hne' : els ≠ [] := by
          simpa [f, els, els', hels_eq] using (blocksJoin_ne_nil (bs ++ [b]) hne_blocks (by intro b' hb'; exact (hblocks b' hb').2.1))
        have hidx : els.length - 1 < els.length := Nat.pred_lt (ne_of_gt ((List.length_pos_iff_ne_nil).mpr hne'))
        have h := htape_els (els.length - 1) hidx
        have hcast : p₀ + ↑(els.length - 1) = p₀ + ↑els.length - 1 := by
          rw [Nat.cast_pred (by exact (List.length_pos_iff_ne_nil).mpr hne')]
          omega
        rw [congrArg tape hcast] at h
        exact h
      have hlen_nat : els.length = els'.length + 1 + b.2.length := by
        simp [els, els', f]
        omega
      have hlast_cell : els[els.length - 1]'(by omega) = b.2[b.2.length - 1]'(by omega) := by
        have hidx0 : els.length - 1 < (els' ++ ([b.1] ++ b.2)).length := by
          rw [List.length_append, List.length_append, List.length_singleton]
          omega
        change (els' ++ ([b.1] ++ b.2))[els.length - 1]'hidx0 = b.2[b.2.length - 1]'(by omega)
        rw [List.getElem_append_right (by
          rw [hlen_nat]
          omega)]
        rw [List.getElem_append_right (by
          rw [List.length_singleton]
          omega)]
        have hidx' : els.length - 1 - els'.length - [b.1].length = b.2.length - 1 := by
          rw [List.length_singleton]
          rw [hlen_nat]
          omega
        simp only [hidx']
      have hlast_m : (tape (p₀ + (els.length : ℤ) - 1)).2 = false := by
        rw [hlast_tape24, hlast_cell]
        rcases (hb2_data (b.2[b.2.length - 1]'(by omega)) (List.getElem_mem (by omega))) with ⟨_, hm⟩
        exact hm
      have hb1k : b.1.1 = SymKind.sel ∨ b.1.1 = SymKind.nosel := by
        rcases hb1 with h | h
        · left; rw [h]; rfl
        · right; rw [h]; rfl
      -- 段 2（29 扫剩余数据 → 选择符 → 26）；起点 p29 = 偏移 k+1 位置
      let p29 : ℤ := p₀ + (els.length : ℤ) - (k : ℤ) - 2
      have hkeep29 : ∀ i : ℤ, p29 - ((b.2.length - 1 - k : ℕ) : ℤ) < i ∧ i ≤ p29 →
          { nextState := 29, writeSym := tape i, moveDir := Dir.L } ∈ VerifierSym.transition (29, tape i) := by
        intro i h
        have hi' : p₀ + (els'.length : ℤ) < i := by
          have hk' := h.1
          rw [show p29 - ((b.2.length - 1 - k : ℕ) : ℤ) = p₀ + (els'.length : ℤ) from by
            dsimp [p29]
            rw [hcast_k]
            rw [helen]
            omega] at hk'
          exact hk'
        have hio : ∃ io : ℕ, (io : ℤ) = i - p₀ := by
          refine ⟨(i - p₀).toNat, ?_⟩
          exact Int.toNat_of_nonneg (by omega : 0 ≤ i - p₀)
        rcases hio with ⟨io, hio_eq⟩
        have hio_lt : io < els.length := by omega
        have hidx : p₀ + (io : ℤ) = i := by omega
        have hcell : tape i = els[io] := by
          rw [← hidx]
          exact htape_els io hio_lt
        have hio_ge : els'.length + 1 ≤ io := by omega
        have hio_lt2 : io < els'.length + 1 + b.2.length := by omega
        have hcell' : els[io] = b.2[io - (els'.length + 1)]'(by omega) := by
          have hio_ltX : io < (els' ++ ([b.1] ++ b.2)).length := by
            rw [List.length_append, List.length_append, List.length_singleton]
            omega
          change (els' ++ ([b.1] ++ b.2))[io]'hio_ltX = b.2[io - (els'.length + 1)]'(by omega)
          rw [List.getElem_append_right (by omega)]
          rw [List.getElem_append_right (by
            rw [List.length_singleton]
            omega)]
          have hidx' : io - els'.length - [b.1].length = io - (els'.length + 1) := by
            rw [List.length_singleton]
            omega
          simp only [hidx']
        have hmem : b.2[io - (els'.length + 1)] ∈ b.2 := List.getElem_mem (by omega)
        have hdata := hb2_data (b.2[io - (els'.length + 1)]) hmem
        have hk : (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1 := by
          rw [hcell, hcell']
          exact hdata.1
        have hm : (tape i).2 = false := by
          rw [hcell, hcell']
          exact hdata.2
        exact trans29_data (tape i) hk hm
      have hb29_end : tape (p29 - ((b.2.length - 1 - k : ℕ) : ℤ)) = b.1 := by
        have heq : p29 - ((b.2.length - 1 - k : ℕ) : ℤ) = p₀ + (els'.length : ℤ) := by
          dsimp [p29]
          rw [hcast_k]
          rw [helen]
          omega
        rw [heq]
        have hcell : tape (p₀ + (els'.length : ℤ)) = els[els'.length]'(by omega) :=
          htape_els els'.length (by omega)
        rw [hcell]
        rw [show els[els'.length] = b.1 from by
          have hidx0 : els'.length < (els' ++ ([b.1] ++ b.2)).length := by
            rw [List.length_append, List.length_append, List.length_singleton]
            omega
          change (els' ++ ([b.1] ++ b.2))[els'.length]'hidx0 = b.1
          rw [List.getElem_append_right (by omega)]
          have hidx1 : els'.length - els'.length = 0 := by omega
          simp only [hidx1]
          rfl]
      -- 入口：24 读最右位 → 25/29 找 1 → 29 态（段 2 起点 p29）
      have hentry : ∃ π0 cfg0, SymSteps VerifierSym.transition (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1)) π0 cfg0 ∧
          cfg0 = SymConfig.mk 29 tape p29 := by
        by_cases hk0 : k = 0
        · -- k=0：最右位是 data1：24 d1 → 29
          have hlast1 : tape (p₀ + (els.length : ℤ) - 1) = Sym.data1 := by
            rw [hlast_tape24, hlast_cell]
            simpa [hk0] using hk1
          let r24 : SymTransResult := { nextState := 29, writeSym := tape (p₀ + (els.length : ℤ) - 1), moveDir := Dir.L }
          let step24 : SymStep := { fromState := 24, readSym := tape (p₀ + (els.length : ℤ) - 1), result := r24 }
          have htrans24 : step24.result ∈ VerifierSym.transition (24, tape (p₀ + (els.length : ℤ) - 1)) := by
            exact trans24_data1 (tape (p₀ + (els.length : ℤ) - 1)) (congrArg (fun s : Sym => s.1) hlast1) hlast_m
          have hstep24 : SymSteps VerifierSym.transition (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1)) [step24]
              (symStepConfig (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1)) step24.result) := by
            refine SymSteps.cons [] step24 (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1)) SymSteps.nil ?_ ?_ ?_
            · rfl
            · rfl
            · exact htrans24
          have hcfg24 : symStepConfig (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1)) step24.result =
              SymConfig.mk 29 tape (p₀ + (els.length : ℤ) - 2) := by
            simp [symStepConfig, SymConfig.mk, step24, r24, Dir.toInt]
            constructor
            · funext i
              by_cases h : i = p₀ + (els.length : ℤ) - 1 <;> simp [h]
            · omega
          refine ⟨[step24], symStepConfig (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1)) step24.result, hstep24, ?_⟩
          rw [hcfg24]
          simp [p29, hk0]
        · -- k ≥ 1：最右位 data0，与 hpos（最高位 = data1）矛盾
          have hk0pos : 0 < k := by omega
          have hlast0 : tape (p₀ + (els.length : ℤ) - 1) = Sym.data0 := by
            rw [hlast_tape24, hlast_cell]
            simpa using hk0s 0 hk0pos
          have hcell0 : (b.2[b.2.length - 1]'(by omega)).1 = SymKind.data0 := by
            have hc : tape (p₀ + (els.length : ℤ) - 1) = b.2[b.2.length - 1]'(by omega) := by
              rw [hlast_tape24, hlast_cell]
            rw [hc] at hlast0
            simpa using congrArg (fun s : Sym => s.1) hlast0
          have hcell1 : (b.2[b.2.length - 1]'(by omega)).1 = SymKind.data1 := hpos b hb_mem hb2ne
          have : SymKind.data0 = SymKind.data1 := hcell0.symm.trans hcell1
          cases this
      rcases hentry with ⟨π0, cfg0, hπ0, hcfg0⟩
      rcases scanLeftKeepPos 29 26 b.1 Dir.L (b.2.length - 1 - k) p29 tape
        hkeep29 (trans29_sel b.1 hb1k hb1m) hb29_end with ⟨πb, cfgb, hπb, hsb, hheadb, htapeb⟩
      have hπb' : SymSteps VerifierSym.transition cfg0 πb cfgb := by
        simpa [hcfg0] using hπb
      have hcfgb : cfgb = SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1) := by
        rcases cfgb with ⟨s, t, hp⟩
        have ht : t = tape := by simpa using htapeb
        have hs : s = 26 := by simpa using hsb
        have hhp : hp = p₀ + (els.length : ℤ) - (k : ℤ) - 2 - ((b.2.length - 1 - k : ℕ) : ℤ) + (-1 : ℤ) := by
          simpa [Dir.toInt, p29] using hheadb
        subst t; subst s; subst hp
        simp [SymConfig.mk]
        rw [show p₀ + (els.length : ℤ) - (k : ℤ) - 2 - ((b.2.length - 1 - k : ℕ) : ℤ) + (-1 : ℤ) =
            p₀ + (els'.length : ℤ) - 1 from by
          have hk1_le : k + 1 ≤ b.2.length := by omega
          have hcast_k : ((b.2.length - 1 - k : ℕ) : ℤ) = (b.2.length : ℤ) - 1 - (k : ℤ) := by
            rw [show b.2.length - 1 - k = b.2.length - (k + 1) from by omega]
            rw [Nat.cast_sub hk1_le]
            rw [Nat.cast_add]
            norm_num
            omega
          rw [helen]
          rw [hcast_k]
          omega]
      by_cases hbs : bs = []
      · -- 26 读 #₀ → 27
        have hpos : p₀ + (els'.length : ℤ) - 1 = p₀ - 1 := by
          simp [els', hbs]
        have hmid' : tape (p₀ + (els'.length : ℤ) - 1) = Sym.boundary := by
          rw [hpos]
          exact hmid
        let r26 : SymTransResult := { nextState := 27, writeSym := Sym.boundary, moveDir := Dir.L }
        let step26 : SymStep := { fromState := 26, readSym := Sym.boundary, result := r26 }
        have htrans26 : step26.result ∈ VerifierSym.transition (26, Sym.boundary) := trans26_hash
        have hstep26 : SymSteps VerifierSym.transition (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) [step26]
            (symStepConfig (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) step26.result) := by
          refine SymSteps.cons [] step26 (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) SymSteps.nil ?_ ?_ ?_
          · rfl
          · change Sym.boundary = tape (p₀ + (els'.length : ℤ) - 1)
            rw [hmid']
          · change step26.result ∈ VerifierSym.transition (26, tape (p₀ + (els'.length : ℤ) - 1))
            rw [hmid']
            exact htrans26
        refine ⟨π0 ++ πb ++ [step26], symStepConfig (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) step26.result, ?_, ?_, ?_, ?_⟩
        · have hπ0' : SymSteps VerifierSym.transition (SymConfig.mk 24 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1)) π0 cfg0 := by
            convert hπ0 using 1
            rw [hels_eq]
          have h0b : SymSteps VerifierSym.transition (SymConfig.mk 24 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1)) (π0 ++ πb)
              (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) := by
            exact SymSteps_trans VerifierSym.transition (SymConfig.mk 24 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1)) cfg0
              (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) π0 πb hπ0' (hcfgb ▸ hπb')
          exact SymSteps_trans VerifierSym.transition (SymConfig.mk 24 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1))
            (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1))
            (symStepConfig (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) step26.result)
            (π0 ++ πb) [step26] h0b hstep26
        · rfl
        · change (symStepConfig (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) step26.result).headPos = p₀ - 2
          simp [symStepConfig, SymConfig.mk, step26, r26, Dir.toInt]
          omega
        · change (symStepConfig (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) step26.result).tape = tape
          simp [symStepConfig, SymConfig.mk, step26, r26]
          funext i
          by_cases h : i = p₀ + (els'.length : ℤ) - 1 <;> simp [h, hmid']
      · -- 26 读 els'.last（data）→ 25，接 ih
        have hbs' : bs ≠ [] := hbs
        have hblocks_bs : ∀ b' ∈ bs, (b'.1 = Sym.sel ∨ b'.1 = Sym.nosel) ∧ b'.2 ≠ [] ∧
            (∀ s ∈ b'.2, (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false) := by
          intro b' hb'
          exact hblocks b' (by simp [hb'])
        have hels_bs : tapeAgrees tape p₀ els' := by
          intro i hi
          have helen' := htape_els i (by
            rw [show els = els' ++ ([b.1] ++ b.2) from by simp [els, els', f]]
            rw [List.length_append, List.length_append, List.length_singleton]
            omega)
          have hcelli : els[i]'(by omega) = els'[i]'(by omega) := by
            change (els' ++ ([b.1] ++ b.2))[i]'(by
              rw [List.length_append, List.length_append, List.length_singleton]
              omega) = els'[i]'(by omega)
            rw [List.getElem_append_left (by omega)]
          rw [hcelli] at helen'
          exact helen'
        have hpos_bs : ∀ b' ∈ bs, blockTopIs1 b' := by
          intro b' hb'
          exact hpos b' (by simp [hb'])
        rcases format_sweep_rec_from26 bs tgt p₀ tape hblocks_bs hpos_bs hels_bs htgt htgt_data hne_tgt hmid hleft hbs' with ⟨π', cfg', hπ', hs', hhead', htape'⟩
        refine ⟨π0 ++ πb ++ π', cfg', ?_, hs', ?_, ?_⟩
        · have hπ0' : SymSteps VerifierSym.transition (SymConfig.mk 24 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1)) π0 cfg0 := by
            convert hπ0 using 1
            rw [hels_eq]
          have h0b : SymSteps VerifierSym.transition (SymConfig.mk 24 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1)) (π0 ++ πb)
              (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) := by
            exact SymSteps_trans VerifierSym.transition (SymConfig.mk 24 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1)) cfg0
              (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) π0 πb hπ0' (hcfgb ▸ hπb')
          have hπ'' : SymSteps VerifierSym.transition (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) π' cfg' := by
            simpa [f, els'] using hπ'
          exact SymSteps_trans VerifierSym.transition (SymConfig.mk 24 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1))
            (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) cfg' (π0 ++ πb) π' h0b hπ''
        · rw [hhead']
        · simpa using htape'

/-- 格式检查左扫（从状态 24、带头在元素区右端数值位出发）：
    24 读 data → 25，接 format_sweep_rec 扫完元素区（27 在 tgt 右端），
    38 扫 target 到 #ₗ → 28 右移回 #₀ → 状态 4，磁头在第一个元素选择符，磁带不变。 -/
lemma format_sweep_correct (blocks : List (Sym × List Sym)) (tgt : List Sym) (p₀ : ℤ) (tape : ℤ → Sym)
    (hblocks : ∀ b ∈ blocks, (b.1 = Sym.sel ∨ b.1 = Sym.nosel) ∧ b.2 ≠ [] ∧
      (∀ s ∈ b.2, (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false))
    (hpos : ∀ b ∈ blocks, blockTopIs1 b)
    (hels : tapeAgrees tape p₀ (joinLists (blocks.map (fun b => [b.1] ++ b.2))))
    (htgt : tapeAgrees tape (p₀ - (tgt.length : ℤ) - 1) tgt)
    (htgt_data : ∀ s ∈ tgt, (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false)
    (hne_tgt : tgt ≠ [])
    (htgt_top : (tgt[tgt.length - 1]'(Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hne_tgt) (by norm_num))).1 = SymKind.data1)
    (hmid : tape (p₀ - 1) = Sym.boundary)
    (hleft : tape (p₀ - (tgt.length : ℤ) - 2) = Sym.boundary)
    (hne_blocks : blocks ≠ []) :
    ∃ π cfg', SymSteps VerifierSym.transition
      (SymConfig.mk 24 tape (p₀ + ((joinLists (blocks.map (fun b => [b.1] ++ b.2))).length : ℤ) - 1)) π cfg' ∧
      cfg'.state = 4 ∧ cfg'.headPos = p₀ ∧ cfg'.tape = tape := by
  let els : List Sym := joinLists (blocks.map (fun b => [b.1] ++ b.2))
  -- 24 读 els.last（data）→ L 25
  have hlastdata := blocksJoin_last_data blocks hblocks hne_blocks
  rcases format_sweep_rec blocks tgt p₀ tape hblocks hpos hels htgt htgt_data hne_tgt hmid hleft hne_blocks
    with ⟨πs, cfgs, hπs, hss, hheads, htapes⟩
  have hcfgs : cfgs = SymConfig.mk 27 tape (p₀ - 2) := by
    rcases cfgs with ⟨s, t, hp⟩
    have ht : t = tape := by simpa using htapes
    have hs : s = 27 := by simpa using hss
    have hhp : hp = p₀ - 2 := by simpa using hheads
    subst t; subst s; subst hp
    simp [SymConfig.mk]
  -- 27 读 tgt.last → L 38
  have h_tgt_idx : tgt.length - 1 < tgt.length :=
    Nat.pred_lt (ne_of_gt ((List.length_pos_iff_ne_nil).mpr hne_tgt))
  have htgt_last : tape (p₀ - 2) = tgt[tgt.length - 1]'h_tgt_idx := by
    have h := htgt (tgt.length - 1) (by
      exact Nat.pred_lt (ne_of_gt ((List.length_pos_iff_ne_nil).mpr hne_tgt)))
    have hcast : p₀ - ↑tgt.length - 1 + ↑(tgt.length - 1) = p₀ - ↑tgt.length - 1 + (↑tgt.length - 1) := by
      rw [Nat.cast_pred (by exact (List.length_pos_iff_ne_nil).mpr hne_tgt)]
    rw [hcast] at h
    have hidx : p₀ - (tgt.length : ℤ) - 1 + ((tgt.length : ℤ) - 1) = p₀ - 2 := by omega
    rw [hidx] at h
    exact h
  have htgt_last_data : ((tgt[tgt.length - 1]'h_tgt_idx).1 = SymKind.data0 ∨ (tgt[tgt.length - 1]'h_tgt_idx).1 = SymKind.data1) ∧
      (tgt[tgt.length - 1]'h_tgt_idx).2 = false := by
    exact htgt_data (tgt[tgt.length - 1]'h_tgt_idx) (List.getElem_mem h_tgt_idx)
  let r27 : SymTransResult := { nextState := 38, writeSym := tape (p₀ - 2), moveDir := Dir.L }
  let step27 : SymStep := { fromState := 27, readSym := tape (p₀ - 2), result := r27 }
  have htrans27 : step27.result ∈ VerifierSym.transition (27, tape (p₀ - 2)) := by
    simpa [step27, r27, htgt_last] using trans27_data1 (tgt[tgt.length - 1]'h_tgt_idx)
      htgt_top htgt_last_data.2
  have hstep27 : SymSteps VerifierSym.transition (SymConfig.mk 27 tape (p₀ - 2)) [step27]
      (symStepConfig (SymConfig.mk 27 tape (p₀ - 2)) step27.result) := by
    refine SymSteps.cons [] step27 (SymConfig.mk 27 tape (p₀ - 2)) SymSteps.nil ?_ ?_ ?_
    · rfl
    · rfl
    · exact htrans27
  have hcfg27 : symStepConfig (SymConfig.mk 27 tape (p₀ - 2)) step27.result =
      SymConfig.mk 38 tape (p₀ - 3) := by
    simp [symStepConfig, SymConfig.mk, step27, r27, Dir.toInt]
    constructor
    · funext i
      by_cases h : i = p₀ - 2 <;> simp [h]
    · omega
  -- 38 扫 tgt（|tgt|-1 格）→ #ₗ → 28
  have hkeep38 : ∀ i : ℤ, p₀ - 3 - ((tgt.length - 1 : ℕ) : ℤ) < i ∧ i ≤ p₀ - 3 →
      { nextState := 38, writeSym := tape i, moveDir := Dir.L } ∈ VerifierSym.transition (38, tape i) := by
    intro i h
    have hio : ∃ io : ℕ, (io : ℤ) = i - (p₀ - (tgt.length : ℤ) - 1) := by
      refine ⟨(i - (p₀ - (tgt.length : ℤ) - 1)).toNat, ?_⟩
      exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p₀ - (tgt.length : ℤ) - 1))
    rcases hio with ⟨io, hio_eq⟩
    have hio_lt : io < tgt.length := by omega
    have hidx : p₀ - (tgt.length : ℤ) - 1 + (io : ℤ) = i := by omega
    have hcell : tape i = tgt[io] := by
      rw [← hidx]
      exact htgt io hio_lt
    have hdata := htgt_data (tgt[io]) (List.getElem_mem hio_lt)
    exact trans38_data (tape i) (by rw [hcell]; exact hdata.1) (by rw [hcell]; exact hdata.2)
  have hbound38 : tape (p₀ - 3 - ((tgt.length - 1 : ℕ) : ℤ)) = Sym.boundary := by
    have hidx : p₀ - 3 - ((tgt.length - 1 : ℕ) : ℤ) = p₀ - (tgt.length : ℤ) - 2 := by omega
    rw [hidx]
    exact hleft
  rcases scanLeftKeepPos 38 28 Sym.boundary Dir.R (tgt.length - 1) (p₀ - 3) tape
    hkeep38 trans38_hash hbound38 with ⟨π38, cfg38, hπ38, hs38, hhead38, htape38⟩
  have hcfg38 : cfg38 = SymConfig.mk 28 tape (p₀ - (tgt.length : ℤ) - 1) := by
    rcases cfg38 with ⟨s, t, hp⟩
    have ht : t = tape := by simpa using htape38
    have hs : s = 28 := by simpa using hs38
    have hhp : hp = p₀ - 3 - ((tgt.length - 1 : ℕ) : ℤ) + 1 := by
      simpa [Dir.toInt] using hhead38
    subst t; subst s; subst hp
    simp [SymConfig.mk]
    omega
  -- 28 右扫 tgt → #₀ → 4
  have hkeep28 : ∀ i : ℤ, p₀ - (tgt.length : ℤ) - 1 ≤ i ∧ i < p₀ - (tgt.length : ℤ) - 1 + (tgt.length : ℤ) →
      { nextState := 28, writeSym := tape i, moveDir := Dir.R } ∈ VerifierSym.transition (28, tape i) := by
    intro i h
    have hio : ∃ io : ℕ, (io : ℤ) = i - (p₀ - (tgt.length : ℤ) - 1) := by
      refine ⟨(i - (p₀ - (tgt.length : ℤ) - 1)).toNat, ?_⟩
      exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p₀ - (tgt.length : ℤ) - 1))
    rcases hio with ⟨io, hio_eq⟩
    have hio_lt : io < tgt.length := by omega
    have hidx : p₀ - (tgt.length : ℤ) - 1 + (io : ℤ) = i := by omega
    have hcell : tape i = tgt[io] := by
      rw [← hidx]
      exact htgt io hio_lt
    have hdata := htgt_data (tgt[io]) (List.getElem_mem hio_lt)
    exact trans28_data (tape i) (by rw [hcell]; exact hdata.1)
  rcases scanRightKeep 28 tgt.length (p₀ - (tgt.length : ℤ) - 1) tape hkeep28
    with ⟨π28, cfg28, hπ28, hs28, hhead28, htape28⟩
  have hcfg28 : cfg28 = SymConfig.mk 28 tape (p₀ - 1) := by
    rcases cfg28 with ⟨s, t, hp⟩
    have ht : t = tape := by simpa using htape28
    have hs : s = 28 := by simpa using hs28
    have hhp : hp = p₀ - (tgt.length : ℤ) - 1 + (tgt.length : ℤ) := by simpa using hhead28
    subst t; subst s; subst hp
    simp [SymConfig.mk]
    omega
  -- 28 读 #₀ → R 4
  let r28 : SymTransResult := { nextState := 4, writeSym := Sym.boundary, moveDir := Dir.R }
  let step28 : SymStep := { fromState := 28, readSym := Sym.boundary, result := r28 }
  have htrans28 : step28.result ∈ VerifierSym.transition (28, Sym.boundary) := trans28_hash
  have hstep28 : SymSteps VerifierSym.transition (SymConfig.mk 28 tape (p₀ - 1)) [step28]
      (symStepConfig (SymConfig.mk 28 tape (p₀ - 1)) step28.result) := by
    refine SymSteps.cons [] step28 (SymConfig.mk 28 tape (p₀ - 1)) SymSteps.nil ?_ ?_ ?_
    · rfl
    · change Sym.boundary = tape (p₀ - 1)
      exact hmid.symm
    · change step28.result ∈ VerifierSym.transition (28, tape (p₀ - 1))
      rw [hmid]
      exact htrans28
  have hcfg28' : symStepConfig (SymConfig.mk 28 tape (p₀ - 1)) step28.result =
      SymConfig.mk 4 tape p₀ := by
    simp [symStepConfig, SymConfig.mk, step28, r28, Dir.toInt]
    funext i
    by_cases h : i = p₀ - 1 <;> simp [h, hmid]
  refine ⟨πs ++ [step27] ++ π38 ++ π28 ++ [step28], symStepConfig (SymConfig.mk 28 tape (p₀ - 1)) step28.result, ?_, ?_, ?_, ?_⟩
  · have h1 : SymSteps VerifierSym.transition (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1))
        πs (SymConfig.mk 27 tape (p₀ - 2)) := by
      exact hcfgs ▸ hπs
    have h2 : SymSteps VerifierSym.transition (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1))
        (πs ++ [step27]) (SymConfig.mk 38 tape (p₀ - 3)) := by
      exact SymSteps_trans VerifierSym.transition (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1))
        (SymConfig.mk 27 tape (p₀ - 2)) (SymConfig.mk 38 tape (p₀ - 3))
        πs [step27] h1 (hcfg27 ▸ hstep27)
    have h3 : SymSteps VerifierSym.transition (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1))
        (πs ++ [step27] ++ π38) (SymConfig.mk 28 tape (p₀ - (tgt.length : ℤ) - 1)) := by
      exact SymSteps_trans VerifierSym.transition (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1))
        (SymConfig.mk 38 tape (p₀ - 3)) (SymConfig.mk 28 tape (p₀ - (tgt.length : ℤ) - 1))
        (πs ++ [step27]) π38 h2 (hcfg38 ▸ hπ38)
    have h4 : SymSteps VerifierSym.transition (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1))
        (πs ++ [step27] ++ π38 ++ π28) (SymConfig.mk 28 tape (p₀ - 1)) := by
      exact SymSteps_trans VerifierSym.transition (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1))
        (SymConfig.mk 28 tape (p₀ - (tgt.length : ℤ) - 1)) (SymConfig.mk 28 tape (p₀ - 1))
        (πs ++ [step27] ++ π38) π28 h3 (hcfg28 ▸ hπ28)
    exact SymSteps_trans VerifierSym.transition (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1))
      (SymConfig.mk 28 tape (p₀ - 1)) (symStepConfig (SymConfig.mk 28 tape (p₀ - 1)) step28.result)
      (πs ++ [step27] ++ π38 ++ π28) [step28] h4 (hcfg28' ▸ hstep28)
  · rfl
  · change (symStepConfig (SymConfig.mk 28 tape (p₀ - 1)) step28.result).headPos = p₀
    simp [symStepConfig, SymConfig.mk, step28, r28, Dir.toInt]
  · change (symStepConfig (SymConfig.mk 28 tape (p₀ - 1)) step28.result).tape = tape
    simp [symStepConfig, SymConfig.mk, step28, r28]
    funext i
    by_cases h : i = p₀ - 1 <;> simp [h, hmid]
/-- 状态 0 读 #ₗ → 1（初始配置的第一个单步：磁头 0 → 1，磁带不变）。 -/
lemma step0_initial (tape : ℤ → Sym) (h0 : tape 0 = Sym.boundary) :
    ∃ step : SymStep, SymSteps VerifierSym.transition (SymConfig.mk 0 tape 0) [step]
      (SymConfig.mk 1 tape 1) := by
  let r0 : SymTransResult := { nextState := 1, writeSym := Sym.boundary, moveDir := Dir.R }
  let step0 : SymStep := { fromState := 0, readSym := Sym.boundary, result := r0 }
  refine ⟨step0, ?_⟩
  have htrans0 : step0.result ∈ VerifierSym.transition (0, tape 0) := by
    rw [h0]
    decide
  have hstep0 : SymSteps VerifierSym.transition (SymConfig.mk 0 tape 0) [step0]
      (symStepConfig (SymConfig.mk 0 tape 0) step0.result) := by
    refine SymSteps.cons [] step0 (SymConfig.mk 0 tape 0) SymSteps.nil ?_ ?_ ?_
    · rfl
    · dsimp [SymConfig.mk, step0]
      rw [h0]
    · exact htrans0
  have hcfg0 : symStepConfig (SymConfig.mk 0 tape 0) step0.result = SymConfig.mk 1 tape 1 := by
    simp [symStepConfig, SymConfig.mk, step0, r0, Dir.toInt]
    funext i
    by_cases h : i = 0 <;> simp [h, h0]
  exact hcfg0 ▸ hstep0

end Mp
