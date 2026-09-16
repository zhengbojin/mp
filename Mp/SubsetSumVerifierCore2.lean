/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import Mp.SubsetSumVerifierCore1
import Mp.SubsetSumVerifierCoreA

set_option maxHeartbeats 1000000

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


set_option maxErrors 2000

/-!
# 子集和 CBTM 验证器（第三部分：清理/扩展/主循环）
清理计数器、占位扩展与主循环（状态 4 → 22）的正确性证明。
-/

namespace Mp
/-- bitsValue 上界：值 < 2^位宽。 -/
lemma bitsValue_lt_two_pow_length (bits : List Bool) : bitsValue bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [bitsValue]
  | cons b rest ih =>
      rw [List.length_cons]
      rw [show 2 ^ (rest.length + 1) = 2 * 2 ^ rest.length from by rw [pow_succ]; ring]
      by_cases hb : b
      · simp [hb, bitsValue_cons]
        have hbv_le : bitsValue rest ≤ 2 ^ rest.length - 1 := Nat.le_sub_one_of_lt ih
        have hpow : 0 < 2 ^ rest.length := pow_pos (by norm_num) rest.length
        have hle1 : 1 + 2 * bitsValue rest ≤ 1 + 2 * (2 ^ rest.length - 1) := by omega
        have hle2 : 1 + 2 * (2 ^ rest.length - 1) < 2 * 2 ^ rest.length := by
          have h2 : 2 * (2 ^ rest.length - 1) = 2 * 2 ^ rest.length - 2 := by omega
          omega
        exact lt_of_le_of_lt hle1 hle2
      · simp [hb, bitsValue_cons]
        exact ih

/-- 值 ≤ bitsValue tbits → 位数 ≤ tbits 的位数（v > 0）。 -/
lemma bitsOf_length_le_of_value_le (v : ℕ) (tbits : List Bool) (hv : 0 < v) (hle : v ≤ bitsValue tbits) :
    (bitsOf v).length ≤ tbits.length := by
  have hvlt : v < 2 ^ tbits.length := lt_of_le_of_lt hle (bitsValue_lt_two_pow_length tbits)
  have hlog : Nat.log 2 v < tbits.length := Nat.log_lt_of_lt_pow (by omega : v ≠ 0) hvlt
  have hdigits : (Nat.digits 2 v).length = Nat.log 2 v + 1 := Nat.length_digits 2 v (by norm_num : 1 < 2) (by omega : v ≠ 0)
  rw [bitsOf_length]
  rw [hdigits]
  omega

/-- 状态 3 读 #₁（m=0）：标 m=1，转 24（格式检查入口）。 -/
lemma scanLeft3_check (p : ℤ) (tape : ℤ → Sym)
    (hbound : tape p = Sym.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 3 tape p) π cfg' ∧
      cfg'.state = 24 ∧ cfg'.headPos = p - 1 ∧
      cfg'.tape p = Sym.mk SymKind.boundary true ∧
      (∀ i : ℤ, i ≠ p → cfg'.tape i = tape i) := by
  let r : SymTransResult := { nextState := 24, writeSym := Sym.mk SymKind.boundary true, moveDir := Dir.L }
  let step : SymStep := { fromState := 3, readSym := Sym.boundary, result := r }
  refine ⟨[step], symStepConfig (SymConfig.mk 3 tape p) step.result, ?_, ?_, ?_, ?_, ?_⟩
  · refine SymSteps.cons [] step (SymConfig.mk 3 tape p) SymSteps.nil ?_ ?_ ?_
    · rfl
    · change Sym.boundary = tape p
      rw [hbound]
    · change step.result ∈ VerifierSym.transition (3, tape p)
      rw [hbound]
      decide
  · simp [symStepConfig, SymConfig.mk, step, r]
  · simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
    omega
  · dsimp [symStepConfig, SymConfig.mk, step, r]
    rw [if_pos rfl]
  · intro i hi
    dsimp [symStepConfig, SymConfig.mk, step, r]
    rw [if_neg hi]

/-- `encodeBitsSym` 产生的符号 4F4.4 位都是 false。 -/
lemma encodeBitsSym_marks (n : ℕ) : ∀ s ∈ encodeBitsSym n, s.2 = false := by
  intro s hs
  unfold encodeBitsSym at hs
  rcases List.mem_map.mp hs with ⟨b, hb, hbs⟩
  rw [← hbs]
  by_cases h : b = 0 <;> simp [h, Sym.data0, Sym.data1, Sym.mk]

/-- `encodeBitsSym n = bitsToSym (bitsOf n)`。 -/
lemma encodeBitsSym_eq_bitsToSym_bitsOf (n : ℕ) :
    encodeBitsSym n = bitsToSym (bitsOf n) := by
  rw [bitsOf]
  symm
  exact bitsToSym_symToBits_of_data (encodeBitsSym n) (encodeBitsSym_nonboundary n) (encodeBitsSym_marks n)

/-- 状态 21 右扫 n 格（data0/consumed → data0），读第 n+1 格：sel/nosel → 51 停（L），boundary → 22 停（S）。 -/
lemma expand_place_correct_ext (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hn_pos : 1 ≤ n)
    (hbound : tape p = Sym.boundary)
    (hdata : ∀ i : ℕ, i < n → (tape (p + 1 + (i : ℤ))).1 = SymKind.data0 ∨ (tape (p + 1 + (i : ℤ))).1 = SymKind.consumed)
    (hend : (tape (p + 1 + (n : ℤ))).1 = SymKind.sel ∨ (tape (p + 1 + (n : ℤ))).1 = SymKind.nosel ∨
      (tape (p + 1 + (n : ℤ))).1 = SymKind.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 20 tape p) π cfg' ∧
      cfg'.tape p = Sym.data0 ∧
      (cfg'.state = 4 ∧ cfg'.tape (p + (n : ℤ)) = Sym.boundary ∧ cfg'.headPos = p + (n : ℤ) + 1 ∧
          cfg'.tape (p + 1 + (n : ℤ)) = tape (p + 1 + (n : ℤ)) ∧
          (∀ i : ℕ, i + 1 < n → cfg'.tape (p + 1 + (i : ℤ)) = Sym.data0)
       ∨ cfg'.state = 22 ∧ cfg'.tape (p + (n : ℤ)) = Sym.data0 ∧
          (cfg'.tape (p + 1 + (n : ℤ))).1 = SymKind.boundary ∧ cfg'.headPos = p + 1 + (n : ℤ) ∧
          cfg'.tape (p + 1 + (n : ℤ)) = tape (p + 1 + (n : ℤ)) ∧
          (∀ i : ℕ, i < n → cfg'.tape (p + 1 + (i : ℤ)) = Sym.data0)) ∧
      (∀ i : ℤ, i < p → cfg'.tape i = tape i) ∧
      (∀ i : ℤ, p + 1 + (n : ℤ) < i → cfg'.tape i = tape i) ∧
      ((tape (p + 1 + (n : ℤ))).1 = SymKind.sel ∨ (tape (p + 1 + (n : ℤ))).1 = SymKind.nosel → cfg'.state = 4) ∧
      ((tape (p + 1 + (n : ℤ))).1 = SymKind.boundary → cfg'.state = 22) := by
  let r : SymTransResult := { nextState := 21, writeSym := Sym.data0, moveDir := Dir.R }
  let step : SymStep := { fromState := 20, readSym := Sym.boundary, result := r }
  have hstep : SymSteps VerifierSym.transition (SymConfig.mk 20 tape p) [step]
      (symStepConfig (SymConfig.mk 20 tape p) step.result) := by
    refine SymSteps.cons [] step (SymConfig.mk 20 tape p) SymSteps.nil ?_ ?_ ?_
    · rfl
    · change Sym.boundary = tape p
      rw [hbound]
    · change step.result ∈ VerifierSym.transition (20, tape p)
      rw [hbound]
      decide
  let tape1 : ℤ → Sym := fun i => if i = p then Sym.data0 else tape i
  have hcfg : symStepConfig (SymConfig.mk 20 tape p) step.result = SymConfig.mk 21 tape1 (p + 1) := by
    simp [symStepConfig, SymConfig.mk, step, r, tape1, Dir.toInt]
  have hdata1 : ∀ i : ℕ, i < n → (tape1 (p + 1 + (i : ℤ))).1 = SymKind.data0 ∨ (tape1 (p + 1 + (i : ℤ))).1 = SymKind.consumed := by
    intro i hi
    have h := hdata i hi
    have htape : tape1 (p + 1 + (i : ℤ)) = tape (p + 1 + (i : ℤ)) := by
      simp only [tape1]
      rw [if_neg (by omega : p + 1 + (i : ℤ) ≠ p)]
    rw [htape]
    exact h
  have hend1 : (tape1 (p + 1 + (n : ℤ))).1 = SymKind.sel ∨ (tape1 (p + 1 + (n : ℤ))).1 = SymKind.nosel ∨
      (tape1 (p + 1 + (n : ℤ))).1 = SymKind.boundary := by
    rcases hend with hsel | hnosel | hbound'
    · left
      rw [show tape1 (p + 1 + (n : ℤ)) = tape (p + 1 + (n : ℤ)) from by
        simp only [tape1]
        rw [if_neg (by omega : p + 1 + (n : ℤ) ≠ p)]]
      exact hsel
    · right; left
      rw [show tape1 (p + 1 + (n : ℤ)) = tape (p + 1 + (n : ℤ)) from by
        simp only [tape1]
        rw [if_neg (by omega : p + 1 + (n : ℤ) ≠ p)]]
      exact hnosel
    · right; right
      rw [show tape1 (p + 1 + (n : ℤ)) = tape (p + 1 + (n : ℤ)) from by
        simp only [tape1]
        rw [if_neg (by omega : p + 1 + (n : ℤ) ≠ p)]]
      exact hbound'
  rcases expand_scan n (p + 1) tape1 hdata1 hend1 with ⟨π, cfg', hπ, hta, hdisj, hπlen, hleft_scan, hright_scan, hsep_imp_scan, hboundary_imp_scan⟩
  have hstep' : SymSteps VerifierSym.transition (SymConfig.mk 20 tape p) [step] (SymConfig.mk 21 tape1 (p + 1)) := by
    simpa [hcfg] using hstep
  rcases hdisj with h51 | h22
  · -- 51 分支：读 data0 写 boundary → 4
    let r4 : SymTransResult := { nextState := 4, writeSym := Sym.boundary, moveDir := Dir.R }
    let step4 : SymStep := { fromState := 51, readSym := Sym.data0, result := r4 }
    rcases h51 with ⟨hs51, hb51, hhead51⟩
    have hhead51' : cfg'.headPos = p + 1 + (n : ℤ) - 1 := hhead51
    have hread4 : cfg'.tape cfg'.headPos = Sym.data0 := by
      rw [hhead51']
      have hn1 : n - 1 < n := by omega
      have h := hta (n - 1) (by simpa using hn1)
      have hidx : (p + 1) + ((n - 1 : ℕ) : ℤ) = p + 1 + (n : ℤ) - 1 := by omega
      rw [hidx] at h
      have hrep : (List.replicate n Sym.data0)[n - 1]'(by simpa using hn1) = Sym.data0 := by
        have hmem : (List.replicate n Sym.data0)[n - 1]'(by simpa using hn1) ∈ List.replicate n Sym.data0 := List.getElem_mem (by simpa using hn1)
        exact (List.mem_replicate.mp hmem).2
      rw [h, hrep]
    have htrans4 : step4.result ∈ VerifierSym.transition (51, cfg'.tape cfg'.headPos) := by
      rw [hread4]
      decide
    have hstep4 : SymSteps VerifierSym.transition cfg' [step4] (symStepConfig cfg' step4.result) := by
      refine SymSteps.cons [] step4 cfg' SymSteps.nil ?_ ?_ ?_
      · simpa [step4] using hs51.symm
      · change Sym.data0 = cfg'.tape cfg'.headPos
        rw [hread4]
      · simpa [hs51] using htrans4
    let cfg4 : SymConfig := symStepConfig cfg' step4.result
    have htotal4 : SymSteps VerifierSym.transition (SymConfig.mk 20 tape p) ([step] ++ π ++ [step4]) cfg4 := by
      have hstepπ : SymSteps VerifierSym.transition (SymConfig.mk 20 tape p) ([step] ++ π) cfg' :=
        SymSteps_trans _ _ _ _ [step] π hstep' hπ
      exact SymSteps_trans _ _ _ _ ([step] ++ π) [step4] hstepπ hstep4
    have hkeep_p : cfg'.tape p = (SymConfig.mk 21 tape1 (p + 1)).tape p := by
      simp only [SymConfig.mk]
      exact hleft_scan p (by omega)
    have hkeep_left : ∀ i : ℤ, i < p → cfg'.tape i = (SymConfig.mk 21 tape1 (p + 1)).tape i := by
      intro i hi
      have h := hleft_scan i (by omega)
      simp [tape1, show i ≠ p from by omega, h]
    have hkeep_right : ∀ i : ℤ, p + 1 + (n : ℤ) < i → cfg'.tape i = (SymConfig.mk 21 tape1 (p + 1)).tape i := by
      intro i hi
      have h := hright_scan i (by omega)
      simp [tape1, show i ≠ p from by omega, h]
    refine ⟨[step] ++ π ++ [step4], cfg4, htotal4, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- cfg4.tape p = Sym.data0
      have hp_ne : p ≠ cfg'.headPos := by rw [hhead51']; omega
      have hw : cfg4.tape p = cfg'.tape p := by
        dsimp [cfg4]
        simp only [symStepConfig, SymConfig.mk, step4, r4]
        rw [if_neg hp_ne]
      rw [hw, hkeep_p]
      simpa [SymConfig.mk, tape1] using hkeep_p
    · -- 4 析取分支
      left
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩
      · -- cfg4.tape (p + n) = Sym.boundary
        dsimp [cfg4]
        simp only [symStepConfig, SymConfig.mk, step4, r4]
        rw [if_pos (by rw [hhead51']; omega)]
      · -- headPos = p + n + 1
        dsimp [cfg4]
        simp only [symStepConfig, SymConfig.mk, step4, r4, Dir.toInt]
        rw [hhead51']
        omega
      · -- cfg4.tape (p + 1 + n) = tape (p + 1 + n)
        have hne : p + 1 + (n : ℤ) ≠ cfg'.headPos := by rw [hhead51']; omega
        have hw : cfg4.tape (p + 1 + (n : ℤ)) = cfg'.tape (p + 1 + (n : ℤ)) := by
          dsimp [cfg4]
          simp only [symStepConfig, SymConfig.mk, step4, r4]
          rw [if_neg hne]
        rw [hw]
        have hb51' : cfg'.tape (p + 1 + (n : ℤ)) = tape1 (p + 1 + (n : ℤ)) := by
          simpa [show p + 1 + (n : ℤ) = (p + 1) + (n : ℤ) from by omega] using hb51
        rw [hb51']
        simp only [tape1]
        rw [if_neg (by omega : p + 1 + (n : ℤ) ≠ p)]
      · -- i + 1 < n → data0
        intro i hi
        have hne : p + 1 + (i : ℤ) ≠ cfg'.headPos := by
          rw [hhead51']
          omega
        have hw : cfg4.tape (p + 1 + (i : ℤ)) = cfg'.tape (p + 1 + (i : ℤ)) := by
          dsimp [cfg4]
          simp only [symStepConfig, SymConfig.mk, step4, r4]
          rw [if_neg hne]
        rw [hw]
        have hi' : i < (List.replicate n Sym.data0).length := by simpa using (by omega : i < n)
        have h := hta i hi'
        have hmem : (List.replicate n Sym.data0)[i]'hi' ∈ List.replicate n Sym.data0 := List.getElem_mem hi'
        have hrep : (List.replicate n Sym.data0)[i]'hi' = Sym.data0 := (List.mem_replicate.mp hmem).2
        rw [show (p + 1 + (i : ℤ)) = (p + 1) + (i : ℤ) from by omega]
        rw [h, hrep]
    · -- 左不变：i < p
      intro i hi
      have hne : i ≠ cfg'.headPos := by rw [hhead51']; omega
      have hw : cfg4.tape i = cfg'.tape i := by
        dsimp [cfg4]
        simp only [symStepConfig, SymConfig.mk, step4, r4]
        rw [if_neg hne]
      rw [hw, hkeep_left i hi]
      simp only [SymConfig.mk, tape1]
      rw [if_neg (by omega : i ≠ p)]
    · -- 右不变：i > p+1+n
      intro i hi
      have hne : i ≠ cfg'.headPos := by rw [hhead51']; omega
      have hw : cfg4.tape i = cfg'.tape i := by
        dsimp [cfg4]
        simp only [symStepConfig, SymConfig.mk, step4, r4]
        rw [if_neg hne]
      rw [hw, hkeep_right i hi]
      simp only [SymConfig.mk, tape1]
      rw [if_neg (by omega : i ≠ p)]
    · -- sel/nosel → 4
      intro hs
      have hs1 : (tape1 ((p + 1) + (n : ℤ))).1 = SymKind.sel ∨ (tape1 ((p + 1) + (n : ℤ))).1 = SymKind.nosel := by
        rcases hs with h | h
        · left
          have hh : tape1 ((p + 1) + (n : ℤ)) = tape ((p + 1) + (n : ℤ)) := by
            simp [tape1, show (p + 1) + (n : ℤ) ≠ p from by omega]
          rw [hh]
          exact h
        · right
          have hh : tape1 ((p + 1) + (n : ℤ)) = tape ((p + 1) + (n : ℤ)) := by
            simp [tape1, show (p + 1) + (n : ℤ) ≠ p from by omega]
          rw [hh]
          exact h
      have hs51' : cfg'.state = 51 := hsep_imp_scan hs1
      dsimp [cfg4, step4, r4]
      rfl
    · -- boundary → 22（与 51 分支矛盾：hend 决定分支）
      intro hb
      have hb1 : (tape1 ((p + 1) + (n : ℤ))).1 = SymKind.boundary := by
        simp only [tape1]
        rw [if_neg (by omega : (p + 1) + (n : ℤ) ≠ p)]
        simpa [show p + 1 + (n : ℤ) = (p + 1) + (n : ℤ) from by omega] using hb
      have hs22' : cfg'.state = 22 := hboundary_imp_scan hb1
      exfalso
      have hcontra : (51 : ℕ) = 22 := hs51.symm.trans hs22'
      cases hcontra
  · -- 22 分支
    rcases h22 with ⟨hs22, hb22, hhead22, hkeep22⟩
    refine ⟨[step] ++ π, cfg', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact SymSteps_trans VerifierSym.transition (SymConfig.mk 20 tape p) (SymConfig.mk 21 tape1 (p + 1)) cfg' [step] π hstep' hπ
    · -- cfg'.tape p = Sym.data0
      have hkeep : cfg'.tape p = (SymConfig.mk 21 tape1 (p + 1)).tape p := by
        simp only [SymConfig.mk]
        exact hleft_scan p (by omega)
      simpa [SymConfig.mk, tape1] using hkeep
    · -- 22 析取分支
      right
      refine ⟨hs22, ?_, hb22, ?_, ?_, ?_⟩
      · -- cfg'.tape (p + n) = Sym.data0
        have hn1 : n - 1 < n := by omega
        have h := hta (n - 1) (by simpa using hn1)
        have hidx : (p + 1) + ((n - 1 : ℕ) : ℤ) = p + (n : ℤ) := by omega
        rw [hidx] at h
        have hrep : (List.replicate n Sym.data0)[n - 1]'(by simpa using hn1) = Sym.data0 := by
          have hmem : (List.replicate n Sym.data0)[n - 1]'(by simpa using hn1) ∈ List.replicate n Sym.data0 := List.getElem_mem (by simpa using hn1)
          exact (List.mem_replicate.mp hmem).2
        rw [h, hrep]
      · -- headPos = p + 1 + n
        exact hhead22
      · -- cfg'.tape (p+1+n) = tape (p+1+n)（! 写回读值）
        have hk' : cfg'.tape (p + 1 + (n : ℤ)) = tape1 (p + 1 + (n : ℤ)) := by
          simpa [show p + 1 + (n : ℤ) = (p + 1) + (n : ℤ) from by omega] using hkeep22
        have ht1 : tape1 (p + 1 + (n : ℤ)) = tape (p + 1 + (n : ℤ)) := by
          simp only [tape1]
          rw [if_neg (by omega : p + 1 + (n : ℤ) ≠ p)]
        rw [hk', ht1]
      · -- i < n → data0
        intro i hi
        have hi' : i < (List.replicate n Sym.data0).length := by simpa using hi
        have h := hta i hi'
        have hmem : (List.replicate n Sym.data0)[i]'hi' ∈ List.replicate n Sym.data0 := List.getElem_mem hi'
        have hrep : (List.replicate n Sym.data0)[i]'hi' = Sym.data0 := (List.mem_replicate.mp hmem).2
        rw [show (p + 1 + (i : ℤ)) = (p + 1) + (i : ℤ) from by omega]
        rw [h, hrep]
    · -- 左不变：i < p
      intro i hi
      have hkeep : cfg'.tape i = (SymConfig.mk 21 tape1 (p + 1)).tape i := by
        have h := hleft_scan i (by omega)
        simp [tape1, show i ≠ p from by omega, h]
      rw [hkeep]
      simp only [SymConfig.mk, tape1]
      rw [if_neg (by omega : i ≠ p)]
    · -- 右不变：i > p+1+n
      intro i hi
      have hkeep : cfg'.tape i = (SymConfig.mk 21 tape1 (p + 1)).tape i := by
        have h := hright_scan i (by omega)
        simp [tape1, show i ≠ p from by omega, h]
      rw [hkeep]
      simp only [SymConfig.mk, tape1]
      rw [if_neg (by omega : i ≠ p)]
    · -- sel/nosel → 4（与 22 分支矛盾：hend 决定分支）
      intro hs
      have hs1 : (tape1 ((p + 1) + (n : ℤ))).1 = SymKind.sel ∨ (tape1 ((p + 1) + (n : ℤ))).1 = SymKind.nosel := by
        rcases hs with h | h
        · left
          have hh : tape1 ((p + 1) + (n : ℤ)) = tape ((p + 1) + (n : ℤ)) := by
            simp [tape1, show (p + 1) + (n : ℤ) ≠ p from by omega]
          rw [hh]
          exact h
        · right
          have hh : tape1 ((p + 1) + (n : ℤ)) = tape ((p + 1) + (n : ℤ)) := by
            simp [tape1, show (p + 1) + (n : ℤ) ≠ p from by omega]
          rw [hh]
          exact h
      have hs51 : cfg'.state = 51 := hsep_imp_scan hs1
      exfalso
      have hcontra : (22 : ℕ) = 51 := hs22.symm.trans hs51
      cases hcontra
    · intro hb
      have hb1 : (tape1 ((p + 1) + (n : ℤ))).1 = SymKind.boundary := by
        simp only [tape1]
        rw [if_neg (by omega : (p + 1) + (n : ℤ) ≠ p)]
        simpa [show p + 1 + (n : ℤ) = (p + 1) + (n : ℤ) from by omega] using hb
      exact hboundary_imp_scan hb1

/-- 逐位减 ebits 的所有 true 位（最后元素变体：扫到 #₁ 终止）。 -/
lemma subtract_loop_last (tbits ebits : List Bool) (j : ℕ) (p_t p_e : ℤ) (tape : ℤ → Sym)
    (hj_lt : j < tbits.length)
    (hebits_pos : 1 ≤ ebits.length)
    (htlen : j + ebits.length ≤ tbits.length)
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
        (tape (p_e + 1 + ((j + ebits.length : ℕ) : ℤ))).1 = SymKind.boundary) :
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
      -- ebits = []：由 hebits_pos 矛盾（调用方保证元素位串非空）
      exfalso
      simp at hebits_pos
  | cons b rest ih =>
      -- 处理第 j 位 b
      have hvj : tape (p_e + 1 + (j : ℤ)) = if b then Sym.data1 else Sym.data0 := by
        have h0 := helem_rest 0 (by simp [bitsToSym])
        simpa [bitsToSym_cons] using h0
      let ebits_full : List Bool := List.replicate j false ++ (b :: rest)
      have helen_full : ebits_full.length = j + 1 + rest.length := by
        simp [ebits_full]
        omega
      have hj : j < tbits.length := hj_lt
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
      have hres := process_one_bit_last j b tbits ebits_full p_t p_e tape
          (by
            rw [helen_full]
            simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htlen) (by simp [ebits_full]) hp_t_le
          hbound hpad htarget hhashL hsel helem_pre hvj helem_rest_full
      rcases hres with ⟨π₁, cfg₁, hπ₁, hres1⟩
      match hres1 with
      | Or.inl ⟨hstate₁, hhead₁, hta₁, hcons₁, hrest₁, hsel₁, hhashL₁, hbound₁, hsep₁, hpe_eq₁, hpad_keep₁, hright₁⟩ =>
          let tbits' : List Bool := if b then (subOneAt j tbits).getD tbits else tbits
          have htbits'_eq : tbits' = subAllBitsAt tbits [b] j := by
            simp [tbits', subAllBitsAt]
          have htlen' : (j + 1) + rest.length ≤ tbits'.length := by
            have hlen_t : tbits'.length = tbits.length := by
              rw [htbits'_eq]
              exact subAllBitsAt_length tbits [b] j
            rw [hlen_t]
            have htlen_l := htlen
            simp [List.length_cons] at htlen_l
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
              (cfg₁.tape (p_e + 1 + ((j + 1 + rest.length : ℕ) : ℤ))).1 = SymKind.boundary := by
            rcases hsep with hsel | hnosel | hbnd
            · left
              rw [show p_e + 1 + ((j + 1 + rest.length : ℕ) : ℤ) = p_e + 1 + ((ebits_full.length : ℕ) : ℤ) from by
                simp [ebits_full]
                omega]
              rw [hsep₁]
              simpa [ebits_full, List.length_cons] using hsel
            · right; left
              rw [show p_e + 1 + ((j + 1 + rest.length : ℕ) : ℤ) = p_e + 1 + ((ebits_full.length : ℕ) : ℤ) from by
                simp [ebits_full]
                omega]
              rw [hsep₁]
              simpa [ebits_full, List.length_cons] using hnosel
            · right; right
              rw [show p_e + 1 + ((j + 1 + rest.length : ℕ) : ℤ) = p_e + 1 + ((ebits_full.length : ℕ) : ℤ) from by
                simp [ebits_full]
                omega]
              rw [hsep₁]
              simpa [ebits_full, List.length_cons] using hbnd
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
                  (cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ))).1 = SymKind.boundary := by
                rcases hsep with hsel | hnosel | hbnd
                · left
                  rw [show p_e + 1 + ((j + 1 : ℕ) : ℤ) = p_e + 1 + ((ebits_full.length : ℕ) : ℤ) from by
                    simp [ebits_full]]
                  rw [hsep₁]
                  simpa [ebits_full, List.length_cons] using hsel
                · right; left
                  rw [show p_e + 1 + ((j + 1 : ℕ) : ℤ) = p_e + 1 + ((ebits_full.length : ℕ) : ℤ) from by
                    simp [ebits_full]]
                  rw [hsep₁]
                  simpa [ebits_full, List.length_cons] using hnosel
                · right; right
                  rw [show p_e + 1 + ((j + 1 : ℕ) : ℤ) = p_e + 1 + ((ebits_full.length : ℕ) : ℤ) from by
                    simp [ebits_full]]
                  rw [hsep₁]
                  simpa [ebits_full, List.length_cons] using hbnd
              let r84 : SymTransResult := { nextState := 84, writeSym := cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)), moveDir := Dir.L }
              let step84 : SymStep := { fromState := 13, readSym := cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)), result := r84 }
              have hcfg₁_eq : cfg₁ = SymConfig.mk 13 cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) := by
                cases cfg₁ with
                | mk s t hp =>
                    dsimp [SymConfig.mk]
                    rw [show s = 13 from hstate₁]
                    rw [show hp = p_e + 1 + ((j + 1 : ℕ) : ℤ) from hhead₁]
                    norm_num
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
                  have hdec : ∀ s : Sym, s.1 = SymKind.boundary →
                      { nextState := 84, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (13, s) := by
                    intro s hs
                    rcases s with ⟨k, m⟩
                    have hk' : k = SymKind.boundary := by simpa using hs
                    subst k
                    cases m <;> decide
                  exact hdec (cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ))) hs
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
                rw [show p_e + 1 + ((j + [b].length : ℕ) : ℤ) = p_e + 1 + ((ebits_full.length : ℕ) : ℤ) from by
                  simp [ebits_full]]
                rw [hsep₁]
              · -- gap
                intro i hi
                simp only [show cfg84.tape = cfg₁.tape from htape84]
                exact hpad_keep₁ i hi
              · simp only [show cfg84.tape = cfg₁.tape from htape84]
                exact hbound₁
              · intro i hi
                simp only [show cfg84.tape = cfg₁.tape from htape84]
                have hi' : p_e + 1 + (ebits_full.length : ℤ) < i := by
                  simpa [ebits_full, List.length_cons] using hi
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
                    dsimp [SymConfig.mk]
                    rw [show s = 13 from hstate₁]
                    rw [show hp = p_e + 1 + ((j + 1 : ℕ) : ℤ) from hhead₁]
                    norm_num
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
                simp only [symStepConfig, SymConfig.mk, step5b, r5b]
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
              have hbound'' : cfg5b.tape (p_e - 1) = Sym.boundary := by rw [htape5b]; exact hbound₁
              have hhashL'' : cfg5b.tape (p_t - 1) = Sym.boundary := by rw [htape5b]; exact hhashL₁
              have hpad'' : ∀ i : ℤ, p_t + (tbits'.length : ℤ) ≤ i ∧ i < p_e - 1 → cfg5b.tape i = Sym.data0 := by
                intro i hi
                rw [htape5b]
                exact hpad' i hi
              have hsel'' : (cfg5b.tape p_e).1 = SymKind.data0 ∨ (cfg5b.tape p_e).1 = SymKind.data1 := by
                rw [htape5b]
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
                  (cfg5b.tape (p_e + 1 + ((j + 1 + (b2 :: rest2).length : ℕ) : ℤ))).1 = SymKind.boundary := by
                simp only [show cfg5b.tape = cfg₁.tape from htape5b]
                rw [show p_e + 1 + ((j + 1 + (b2 :: rest2).length : ℕ) : ℤ) = p_e + 1 + ((ebits_full.length : ℕ) : ℤ) from by
                  simp [ebits_full]
                  omega]
                rw [hsep₁]
                simpa [ebits_full, List.length_cons] using hsep
              have hj_lt2 : j + 1 < tbits'.length := by
                have hrest_pos : 0 < (b2 :: rest2).length := by
                  simp [List.length_cons]
                omega
              have hcfg5b_eq : cfg5b = SymConfig.mk 5 cfg5b.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) := by
                rw [← hstate5b, ← hhead5b]
              rw [← htape5b] at htarget'
              rcases ih tbits' (j + 1) p_t p_e cfg5b.tape hj_lt2 (by simp : 1 ≤ (b2 :: rest2).length) htlen' hle' hp_t_le' htarget'
                  hbound'' hhashL'' hpad'' hsel'' helem_pre'' helem_rest'' hsep''
                  with ⟨π₂, cfg₂, hπ₂, hs₂, hta₂, hcons₂, hhead₂, hpe_eq₂, hhashL₂, hsep₂, hpad₂, hbound₂, hright₂⟩
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
                have hlen_eq : j + 1 + (b2 :: rest2).length = j + (b :: b2 :: rest2).length := by
                  simp [List.length_cons]
                  omega
                rw [hsubAll]
                rw [← hlen_eq]
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
                rw [show p_e + 1 + ((j + (b :: b2 :: rest2).length : ℕ) : ℤ) = p_e + 1 + ((j + 1 + (b2 :: rest2).length : ℕ) : ℤ) from by
                  simp [List.length_cons]
                  omega]
                rw [hsep₂]
                rw [htape5b]
                rw [show p_e + 1 + ((j + 1 + (b2 :: rest2).length : ℕ) : ℤ) = p_e + 1 + ((ebits_full.length : ℕ) : ℤ) from by
                  simp [ebits_full]
                  omega]
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
                  have htlen_l := htlen
                  simp [List.length_cons, ebits_full] at hi htlen_l ⊢
                  omega
                simp only [show cfg5b.tape = cfg₁.tape from htape5b]
                rw [hright₁ i hi']
      | Or.inr ⟨hs101, hhead101, hb101, hlt2_101, hdata1_101, hbound101, hcons101, hhashL101, hkeep_pe101, hright101⟩ =>
          exfalso
          have hb' : b = true := by simpa using hb101
          subst b
          have h2 : 2 ^ j ≤ bitsValue tbits := by simpa using hsub
          omega


lemma subtract_element_last_correct (tbits ebits : List Bool) (p_t p_e : ℤ) (tape : ℤ → Sym)
    (hebits_pos : 1 ≤ ebits.length)
    (htlen : ebits.length ≤ tbits.length)
    (hle : bitsValue ebits ≤ bitsValue tbits)
    (hp_t_le : p_t + (tbits.length : ℤ) ≤ p_e)
    (htarget : tapeAgrees tape p_t (targetTape 0 tbits))
    (hbound : tape (p_e - 1) = Sym.boundary)
    (hhashL : tape (p_t - 1) = Sym.boundary)
    (hpad : ∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p_e - 1 → tape i = Sym.data0)
    (hsel : tape p_e = Sym.sel)
    (helem : tapeAgrees tape (p_e + 1) (bitsToSym ebits))
    (hsep : tape (p_e + 1 + (ebits.length : ℤ)) = Sym.sel ∨
        tape (p_e + 1 + (ebits.length : ℤ)) = Sym.nosel ∨
        (tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) π cfg' ∧
      cfg'.state = 84 ∧
      tapeAgrees cfg'.tape p_t (targetTape ebits.length (subAllBits tbits ebits)) ∧
      (∀ i : ℕ, i < ebits.length → cfg'.tape (p_e + 1 + (i : ℤ)) = Sym.consumed) ∧
      cfg'.headPos = p_e + (ebits.length : ℤ) ∧
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
  have hsep0 : tape1 (p_e + 1 + (ebits.length : ℤ)) = Sym.sel ∨
      tape1 (p_e + 1 + (ebits.length : ℤ)) = Sym.nosel ∨
      (tape1 (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.boundary := by
    have hneq : p_e + 1 + (ebits.length : ℤ) ≠ p_e := by omega
    rcases hsep with hsel | hnosel | hbnd
    · left
      rw [show tape1 (p_e + 1 + (ebits.length : ℤ)) = tape (p_e + 1 + (ebits.length : ℤ)) from by
        simp only [tape1]
        rw [if_neg hneq]]
      exact hsel
    · right; left
      rw [show tape1 (p_e + 1 + (ebits.length : ℤ)) = tape (p_e + 1 + (ebits.length : ℤ)) from by
        simp only [tape1]
        rw [if_neg hneq]]
      exact hnosel
    · right; right
      rw [show tape1 (p_e + 1 + (ebits.length : ℤ)) = tape (p_e + 1 + (ebits.length : ℤ)) from by
        simp only [tape1]
        rw [if_neg hneq]]
      exact hbnd
  have hle0 : 2 ^ 0 * bitsValue ebits ≤ bitsValue tbits := by simpa using hle
  have hpad0 : ∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p_e - 1 → tape1 i = Sym.data0 := by
    intro i hi
    rw [show tape1 i = tape i from by
      simp only [tape1]
      rw [if_neg (by omega : i ≠ p_e)]]
    exact hpad i hi
  rcases subtract_loop_last tbits ebits 0 p_t p_e tape1 (by omega) hebits_pos (by omega) hle0 hp_t_le htarget0 hbound0 hhashL0 hpad0 hsel0
      (by intro i hi; omega) (by simpa using helem0) (by simpa using hsep0)
      with ⟨π, cfg', hπ, hs, hta, hcons, hhead, hpe_eq, hhashL_out, hsep_keep, hpad_keep, hbound_keep, hright_keep⟩
  refine ⟨[step] ++ π, cfg', ?_, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hstep' : SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) [step]
        (SymConfig.mk 5 tape1 (p_e + 1)) := by
      simpa [hcfg] using hstep
    have hπ' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape1 (p_e + 1)) π cfg' := by
      simpa using hπ
    exact SymSteps_trans VerifierSym.transition (SymConfig.mk 4 tape p_e) (SymConfig.mk 5 tape1 (p_e + 1)) cfg' [step] π hstep' hπ'
  · simpa [subAllBits] using hta
  · intro i hi
    exact hcons i (by omega)
  · rw [hhead]
    simp
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

/-- 物理编码非空（每个元素块至少 1 个符号）。 -/
lemma encodeElementsSymWithSel_length_pos (elems : List ℕ) (sel : List Bool)
    (helems : elems ≠ []) (hsel : sel.length = elems.length) :
    0 < (encodeElementsSymWithSel elems sel).length := by
  rcases elems with _ | ⟨v, rest⟩
  · contradiction
  · rcases sel with _ | ⟨b, sel'⟩
    · simp at hsel
    · have hx : 0 < ([if b then Sym.sel else Sym.nosel] ++ encodeBitsSymNative v).length := by simp
      dsimp [encodeElementsSymWithSel]
      simp [joinLists]

/-- 主循环（状态 4 → 22）：对元素/选择同步归纳，逐元素 subtract/clear + clear_counter/退回 + expand_place，
    把 target 区从 tbits 累积减到 subAllSelected；22 停在 #₁ 上（headPos = p + chosen 长度 + 1）。 -/
lemma main_loop_correct (elems : List ℕ) (sel : List Bool) (tbits : List Bool)
    (p_t p : ℤ) (tape : ℤ → Sym)
    (hne : elems ≠ [])
    (hpos : ∀ v ∈ elems, 0 < v)
    (hsel_len : sel.length = elems.length)
    (hp_t_le : p_t + (tbits.length : ℤ) ≤ p)
    (htarget : tapeAgrees tape p_t (targetTape 0 tbits))
    (hbound : tape p = Sym.boundary)
    (hhashL : tape (p_t - 1) = Sym.boundary)
    (hpad : ∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p → tape i = Sym.data0)
    (helems : tapeAgrees tape (p + 1) (encodeElementsSymWithSel elems sel))
    (hend : (tape (p + 1 + (encodeElementsSymWithSel elems sel).length)).1 = SymKind.boundary)
    (hle_total : selectedSum elems sel ≤ bitsValue tbits) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) π cfg' ∧
      cfg'.state = 22 ∧
      tapeAgrees cfg'.tape p_t (targetTape 0 (subAllSelected 0 tbits elems sel)) ∧
      cfg'.headPos = p + (encodeElementsSymWithSel elems sel).length + 1 ∧
      (∀ i : ℤ, p ≤ i ∧ i < cfg'.headPos → cfg'.tape i = Sym.data0) ∧
      cfg'.tape (p_t - 1) = Sym.boundary ∧
      (∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p → cfg'.tape i = Sym.data0) ∧
      (∀ i : ℤ, p + 1 + (encodeElementsSymWithSel elems sel).length < i → cfg'.tape i = tape i) ∧
      cfg'.tape cfg'.headPos = tape cfg'.headPos := by
  induction elems generalizing sel p tape tbits with
  | nil =>
      exfalso
      exact hne rfl
  | cons v rest ih =>
      cases sel with
      | nil => exfalso; have h := hsel_len; simp at h
      | cons b sel' =>
          cases rest with
          | nil =>
              have hsel'_nil : sel' = [] := by
                have h : sel'.length = 0 := by
                  have hlen' : sel'.length + 1 = 1 := by
                    simpa [List.length_cons] using hsel_len
                  omega
                exact List.eq_nil_of_length_eq_zero h
              subst sel'
              have hv : v ∈ v :: [] := by simp
              have hv_len : (bitsOf v).length = (Nat.digits 2 v).length := bitsOf_length v
              have henc_len : (encodeBitsSymNative v).length = (bitsOf v).length := by
                simp [encodeBitsSymNative, hv_len]
              have hmark : tape (p + 1) = (if b then Sym.sel else Sym.nosel) := by
                have h := (tapeAgrees_cons tape (p + 1) (if b then Sym.sel else Sym.nosel) (encodeBitsSym v)).mp (by
                  simpa [encodeElementsSymWithSel, joinLists, show encodeBitsSym v = encodeBitsSymNative v from rfl] using helems)
                exact h.1
              have hvals : tapeAgrees tape (p + 2) (encodeBitsSym v) := by
                have h := (tapeAgrees_cons tape (p + 1) (if b then Sym.sel else Sym.nosel) (encodeBitsSym v)).mp (by
                  simpa [encodeElementsSymWithSel, joinLists, show encodeBitsSym v = encodeBitsSymNative v from rfl] using helems)
                simpa [show p + 2 = p + 1 + 1 from by omega] using h.2
              have hvals_bits : tapeAgrees tape (p + 2) (bitsToSym (bitsOf v)) := by
                simpa [encodeBitsSym_eq_bitsToSym_bitsOf] using hvals
              have hbnd : (tape (p + 2 + ((bitsOf v).length : ℤ))).1 = SymKind.boundary := by
                have hend' : (tape (p + 1 + (encodeElementsSymWithSel [v] [b]).length)).1 = SymKind.boundary := hend
                simpa [encodeElementsSymWithSel, joinLists, encodeBitsSymNative, hv_len, show p + 1 + (↑(Nat.digits 2 v).length + 1) = p + 2 + ↑(Nat.digits 2 v).length from by omega] using hend'
              by_cases hb : b
              · -- sel，最后元素
                have hmark_sel : tape (p + 1) = Sym.sel := by simpa [hb] using hmark
                have hle_v : v ≤ bitsValue tbits := selected_ge_of_le v [] [] tbits (by simpa [hb] using hle_total)
                have hle_bits : bitsValue (bitsOf v) ≤ bitsValue tbits := by simpa [bitsValue_bitsOf] using hle_v
                have hlen_le_sub : (bitsOf v).length ≤ tbits.length := bitsOf_length_le_of_value_le v tbits (hpos v hv) hle_v
                have hebits_pos_sub : 1 ≤ (bitsOf v).length := by
                  rw [bitsOf_length]
                  exact List.length_pos_iff_ne_nil.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr (ne_of_gt (hpos v hv)))
                have hp_t_le_sub : p_t + (tbits.length : ℤ) ≤ p + 1 := by omega
                have hpad_sub : ∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < (p + 1) - 1 → tape i = Sym.data0 := by
                  intro i hi
                  exact hpad i ⟨hi.1, by omega⟩
                rcases subtract_element_last_correct tbits (bitsOf v) p_t (p + 1) tape hebits_pos_sub hlen_le_sub hle_bits hp_t_le_sub htarget
                    (by simpa using hbound) hhashL hpad_sub hmark_sel (by simpa [show p + 2 = p + 1 + 1 from by omega] using hvals_bits) (by right; right; rw [← show p + 2 + ((bitsOf v).length : ℤ) = p + 1 + 1 + ((bitsOf v).length : ℤ) from by omega]; simpa using hbnd)
                    with ⟨πsub, cfgsub, hπsub, hssub, htasub, hconssub, hpe_sub, hpe0_sub, hhashL_sub, hsep_out, hpad_out, hbound_out, hright_sub⟩
                rcases clear_counter_correct tbits (bitsOf v) p_t (p + 1) cfgsub.tape hebits_pos_sub hlen_le_sub hp_t_le_sub htasub
                    hbound_out hhashL_sub hpad_out hpe0_sub hconssub
                    with ⟨πcc, cfgcc, hπcc, hscc, hheadcc, htacc, hbound_cc, hhashL_cc, hmark_cc, hcons_cc, hkeep_cc, hgap_cc⟩
                have hbound_cc0 : cfgcc.tape p = Sym.boundary := by simpa using hbound_cc
                have hdata_cc : ∀ i : ℕ, i < (bitsOf v).length + 1 → (cfgcc.tape (p + 1 + (i : ℤ))).1 = SymKind.data0 ∨ (cfgcc.tape (p + 1 + (i : ℤ))).1 = SymKind.consumed := by
                  intro i hi
                  cases i with
                  | zero => left; simpa using congrArg (fun s : Sym => s.1) hmark_cc
                  | succ j =>
                      right
                      have hj : j < (bitsOf v).length := by simpa [hv_len] using hi
                      have h := hcons_cc j hj
                      simpa [Sym.consumed, hv_len, show p + 1 + (↑j + 1) = p + 1 + 1 + ↑j from by omega] using congrArg (fun s : Sym => s.1) h
                have hb_cc : (cfgcc.tape (p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ))).1 = SymKind.boundary := by
                  have hkeep : cfgcc.tape (p + 2 + ((bitsOf v).length : ℤ)) = tape (p + 2 + ((bitsOf v).length : ℤ)) := by
                    rw [hkeep_cc (p + 2 + ((bitsOf v).length : ℤ)) (by omega)]
                    rw [← show p + 1 + 1 + ((bitsOf v).length : ℤ) = p + 2 + ((bitsOf v).length : ℤ) from by omega]
                    exact hsep_out
                  simpa [show p + 1 + (↑(bitsOf v).length + 1) = p + 2 + ↑(bitsOf v).length from by omega] using (by
                    rw [hkeep]
                    exact hbnd)
                have hend_cc : (cfgcc.tape (p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ))).1 = SymKind.sel ∨
                    (cfgcc.tape (p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ))).1 = SymKind.nosel ∨
                    (cfgcc.tape (p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ))).1 = SymKind.boundary := by
                  right; right
                  exact hb_cc
                rcases expand_place_correct_ext ((bitsOf v).length + 1) p cfgcc.tape (by omega) hbound_cc0 hdata_cc hend_cc with
                  ⟨πe, cfge, hπe, he0, he_disj, hleft_e, hright_e, hsep_imp_e, hboundary_imp_e⟩
                have htotal : SymSteps VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) (πsub ++ πcc ++ πe) cfge := by
                  have hsub : SymSteps VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) πsub cfgsub := by simpa using hπsub
                  have hcc : SymSteps VerifierSym.transition cfgsub πcc cfgcc := by
                    have hcfg : cfgsub = SymConfig.mk 84 cfgsub.tape (p + 1 + ((bitsOf v).length : ℤ)) := by
                      cases cfgsub with
                      | mk s t hp =>
                          dsimp [SymConfig.mk]
                          rw [show s = 84 from hssub]
                          rw [show hp = p + 1 + ((bitsOf v).length : ℤ) from hpe_sub]
                    rw [hcfg]
                    exact hπcc
                  have he : SymSteps VerifierSym.transition cfgcc πe cfge := by
                    have hcfg : cfgcc = SymConfig.mk 20 cfgcc.tape p := by
                      cases cfgcc with
                      | mk s t hp =>
                          dsimp [SymConfig.mk]
                          rw [show s = 20 from hscc]
                          rw [show hp = p from by simpa using hheadcc]
                    rw [hcfg]
                    exact hπe
                  have h1 : SymSteps VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) (πsub ++ πcc) cfgcc :=
                    SymSteps_trans VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) cfgsub cfgcc πsub πcc hsub hcc
                  exact SymSteps_trans VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) cfgcc cfge (πsub ++ πcc) πe h1 he
                refine ⟨πsub ++ πcc ++ πe, cfge, htotal, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · exact hboundary_imp_e hb_cc
                · -- target 区 = subAllSelected tbits [v] [b]
                  have htarget' : tapeAgrees cfge.tape p_t (targetTape 0 (subAllBits tbits (bitsOf v))) := by
                    intro i hi
                    have hlen : (targetTape 0 (subAllBits tbits (bitsOf v))).length = tbits.length := by
                      simp [targetTape_length, subAllBits_length]
                    have hik : i < tbits.length := by simpa [hlen] using hi
                    have hi_lt : p_t + (i : ℤ) < p := by omega
                    rw [hleft_e (p_t + (i : ℤ)) hi_lt]
                    exact htacc i hi
                  simpa [subAllSelected, hb] using htarget'
                · -- headPos
                  rcases he_disj with h4 | h22
                  · exfalso
                    have hs : cfge.state = 22 := hboundary_imp_e hb_cc
                    have hcontra : (4 : ℕ) = 22 := h4.1.symm.trans hs
                    cases hcontra
                  · rw [show (encodeElementsSymWithSel [v] [b]).length = (bitsOf v).length + 1 from by simp +arith [encodeElementsSymWithSel, joinLists, henc_len]]
                    rw [← show p + 1 + ↑((bitsOf v).length + 1) = p + ↑((bitsOf v).length + 1) + 1 from by omega]
                    exact h22.2.2.2.1
                · -- 清空 [p, p+(bitsOf v).length+1]
                  intro i hi
                  have hhead : cfge.headPos = p + (((bitsOf v).length + 1 : ℕ) : ℤ) + 1 := by
                    rcases he_disj with h4 | h22
                    · exfalso
                      have hs : cfge.state = 22 := hboundary_imp_e hb_cc
                      cases (h4.1.symm.trans hs)
                    · simpa [show p + 1 + (↑(bitsOf v).length + 1) = p + (↑(bitsOf v).length + 1) + 1 from by omega] using h22.2.2.2.1
                  by_cases heq : i = p
                  · subst i
                    exact he0
                  · have : ∃ j : ℕ, j < (bitsOf v).length + 1 ∧ i = p + 1 + (j : ℤ) := by
                      have hgt : p < i := by omega
                      let j : ℕ := (i - (p + 1)).toNat
                      refine ⟨j, ?_, ?_⟩
                      · have hj : (j : ℤ) = i - (p + 1) := by
                          dsimp [j]
                          exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p + 1))
                        rw [hhead] at hi
                        omega
                      · have hj : (j : ℤ) = i - (p + 1) := by
                          dsimp [j]
                          exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p + 1))
                        rw [hj]
                        omega
                    rcases this with ⟨j, hj, hjpos⟩
                    rw [hjpos]
                    have he_data22 : ∀ j : ℕ, j < (bitsOf v).length + 1 → cfge.tape (p + 1 + (j : ℤ)) = Sym.data0 := by
                      rcases he_disj with h4 | h22
                      · exfalso
                        exact (by decide : (4 : ℕ) ≠ 22) (h4.1.symm.trans (hboundary_imp_e hb_cc))
                      · intro j hj
                        exact h22.2.2.2.2.2 j hj
                    exact he_data22 j hj
                · -- #ₗ 保持
                  rw [hleft_e (p_t - 1) (by omega)]
                  exact hhashL_cc
                · -- gap data0
                  intro i hi
                  rw [hleft_e i hi.2]
                  have hgap : cfgcc.tape i = cfgsub.tape i := hgap_cc i (by
                    constructor
                    · exact hi.1
                    · omega)
                  rw [hgap]
                  exact hpad_out i (by
                    constructor
                    · exact hi.1
                    · omega)
                · -- 右不变：i > p+1+chosen.len
                  intro i hi
                  have hlen : (encodeElementsSymWithSel [v] [b]).length = (bitsOf v).length + 1 := by simp +arith [encodeElementsSymWithSel, joinLists, henc_len]
                  have h := hright_e i (by omega)
                  rw [h]
                  rw [hkeep_cc i (by omega)]
                  exact hright_sub i (by
                    have hlen' : (encodeElementsSymWithSel [v] [b]).length = (bitsOf v).length + 1 := by simp +arith [encodeElementsSymWithSel, joinLists, henc_len]
                    omega)
                · -- cfge.tape cfge.headPos = tape cfge.headPos（#₁ 值保持）
                  have hke : cfge.tape (p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ)) =
                      cfgcc.tape (p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ)) := by
                    rcases he_disj with h4 | h22
                    · exfalso
                      exact (by decide : (4 : ℕ) ≠ 22) (h4.1.symm.trans (hboundary_imp_e hb_cc))
                    · exact h22.2.2.2.2.1
                  have hhead' : cfge.headPos = p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ) := by
                    rcases he_disj with h4 | h22
                    · exfalso
                      exact (by decide : (4 : ℕ) ≠ 22) (h4.1.symm.trans (hboundary_imp_e hb_cc))
                    · exact h22.2.2.2.1
                  have hkc : cfgcc.tape (p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ)) =
                      tape (p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ)) := by
                    have h1 : cfgcc.tape (p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ)) =
                        cfgsub.tape (p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ)) := by
                      exact hkeep_cc (p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ)) (by omega)
                    have h2 : cfgsub.tape (p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ)) =
                        tape (p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ)) := by
                      have hpos' : p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ) =
                          p + 1 + 1 + ((bitsOf v).length : ℤ) := by omega
                      rw [hpos']
                      exact hsep_out
                    exact h1.trans h2
                  rw [hhead']
                  exact hke.trans hkc
              · -- nosel，最后元素
                have hmark_nosel : tape (p + 1) = Sym.nosel := by simpa [hb] using hmark
                rcases clear_element_correct (bitsOf v) (p + 1) tape hmark_nosel (by simpa [show (p + 1) - 1 = p from by omega] using hbound) (by simpa [show p + 2 = p + 1 + 1 from by omega] using hvals_bits) (by
                    right; right
                    rw [← show p + 2 + ↑(bitsOf v).length = p + 1 + 1 + ↑(bitsOf v).length from by omega]; simpa using hbnd)
                    with ⟨πcl, cfgcl, hπcl, hscl, hheadcl, hbnd22_cl, hsel51_cl, htacl, hbound_cl, hpem1_cl, hmark_cl, hleft_cl, hkeep_sep_cl, hright_cl⟩
                have hbnd' : (tape (p + 1 + 1 + ↑(bitsOf v).length)).1 = SymKind.boundary := by
                  simpa [show p + 1 + 1 + ↑(bitsOf v).length = p + 2 + ↑(bitsOf v).length from by omega] using hbnd
                have hcl22 : cfgcl.state = 22 := (hbnd22_cl hbnd').1
                have hhead22 : cfgcl.headPos = p + 2 + ↑(bitsOf v).length := by
                  simpa [show p + 1 + 1 + ↑(bitsOf v).length = p + 2 + ↑(bitsOf v).length from by omega] using (hbnd22_cl hbnd').2
                have hclear : ∀ i : ℤ, p ≤ i ∧ i < p + 2 + ↑(bitsOf v).length → cfgcl.tape i = Sym.data0 := by
                  intro i hi
                  by_cases heq : i = p
                  · subst i
                    simpa [show (p + 1) - 1 = p from by omega] using hpem1_cl
                  · by_cases heq1 : i = p + 1
                    · subst i
                      exact hmark_cl
                    · have hgt : p + 2 ≤ i := by omega
                      have hlt : i < p + 1 + 1 + ↑(bitsOf v).length := by omega
                      let j : ℕ := (i - (p + 2)).toNat
                      have hj : (j : ℤ) = i - (p + 2) := by
                        dsimp [j]
                        exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p + 2))
                      have hj_lt : j < (bitsOf v).length := by
                        have hj' : (j : ℤ) < (bitsOf v).length := by
                          rw [hj]
                          omega
                        exact_mod_cast hj'
                      have h := htacl j (by simpa using hj_lt)
                      have hpos : p + 2 + (j : ℤ) = i := by
                        rw [hj]
                        omega
                      rw [← hpos]
                      simpa [show p + 1 + 1 + (j : ℤ) = p + 2 + (j : ℤ) from by omega] using h
                refine ⟨πcl, cfgcl, ?_, hcl22, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · -- 步骤链
                  simpa using hπcl
                · -- target 区 = tbits（nosel 不减）
                  have htarget' : tapeAgrees cfgcl.tape p_t (targetTape 0 tbits) := by
                    intro i hi
                    have hlen : (targetTape 0 tbits).length = tbits.length := by
                      simp [targetTape_length]
                    have hik : i < tbits.length := by simpa [hlen] using hi
                    rw [hleft_cl (p_t + (i : ℤ)) (by omega)]
                    exact htarget i hi
                  simpa [subAllSelected, hb] using htarget'
                · -- headPos
                  rw [hhead22]
                  rw [show (encodeElementsSymWithSel [v] [b]).length = (bitsOf v).length + 1 from by simp +arith [encodeElementsSymWithSel, joinLists, henc_len]]
                  omega
                · -- 清空 [p, p+2+ebits.length)
                  rw [hhead22]
                  exact hclear
                · -- #ₗ 保持
                  rw [hleft_cl (p_t - 1) (by omega)]
                  exact hhashL
                · -- gap data0
                  intro i hi
                  rw [hleft_cl i (by omega)]
                  exact hpad i hi
                · -- 右不变：i > p+1+chosen.len
                  intro i hi
                  exact hright_cl i (by
                    have hlen : (encodeElementsSymWithSel [v] [b]).length = (bitsOf v).length + 1 := by simp +arith [encodeElementsSymWithSel, joinLists, henc_len]
                    omega)
                · -- cfgcl.tape cfgcl.headPos = tape cfgcl.headPos（#₁ 值保持）
                  rw [hhead22]
                  have hpos'' : p + 2 + ((bitsOf v).length : ℤ) = p + 1 + 1 + ((bitsOf v).length : ℤ) := by omega
                  rw [hpos'']
                  exact hkeep_sep_cl
          | cons w rest' =>
              have hv : v ∈ v :: w :: rest' := by simp
              have hv_len : (bitsOf v).length = (Nat.digits 2 v).length := bitsOf_length v
              have henc_len : (encodeBitsSym v).length = (bitsOf v).length := by
                rw [encodeBitsSym_eq_bitsToSym_bitsOf]
                simp [bitsToSym]
              have hsel'_len : sel'.length = (w :: rest').length := by
                have h : (b :: sel').length = (v :: w :: rest').length := hsel_len
                simpa using h
              let mark := if b then Sym.sel else Sym.nosel
              let enc := encodeElementsSymWithSel (w :: rest') sel'
              have hhelems : tapeAgrees tape (p + 1) (mark :: (encodeBitsSym v ++ enc)) := by
                simpa [encodeElementsSymWithSel, joinLists, mark, enc, show encodeBitsSym v = encodeBitsSymNative v from rfl] using helems
              have hmark : tape (p + 1) = mark :=
                (tapeAgrees_cons tape (p + 1) mark (encodeBitsSym v ++ enc)).mp hhelems |>.1
              have htail : tapeAgrees tape (p + 2) (encodeBitsSym v ++ enc) := by
                have h := (tapeAgrees_cons tape (p + 1) mark (encodeBitsSym v ++ enc)).mp hhelems |>.2
                simpa [show p + 2 = p + 1 + 1 from by omega] using h
              have htail_split := (tapeAgrees_append tape (p + 2) (encodeBitsSym v) enc).mp htail
              have hvals : tapeAgrees tape (p + 2) (encodeBitsSym v) := htail_split.1
              have hrest : tapeAgrees tape (p + 2 + ((bitsOf v).length : ℤ)) enc := by
                simpa [henc_len] using htail_split.2
              have hvals_bits : tapeAgrees tape (p + 2) (bitsToSym (bitsOf v)) := by
                simpa [encodeBitsSym_eq_bitsToSym_bitsOf] using hvals
              let p' : ℤ := p + ((bitsOf v).length : ℤ) + 1
              have hsep_sub : tape (p + 2 + ((bitsOf v).length : ℤ)) = Sym.sel ∨ tape (p + 2 + ((bitsOf v).length : ℤ)) = Sym.nosel := by
                  have hsel'_cons : ∃ b' sel'', sel' = b' :: sel'' := by
                    cases sel' with
                    | nil => exfalso; have h := hsel'_len; simp at h
                    | cons b' sel'' => exact ⟨b', sel'', rfl⟩
                  rcases hsel'_cons with ⟨b', sel'', hsel'_eq⟩
                  have hlen_pos : 0 < (encodeElementsSymWithSel (w :: rest') sel').length :=
                    encodeElementsSymWithSel_length_pos (w :: rest') sel' (by simp) hsel'_len
                  subst sel'
                  have h0 := hrest 0 (by simpa [enc] using hlen_pos)
                  by_cases hb' : b'
                  · left
                    simpa [enc, encodeElementsSymWithSel, joinLists, hb', List.getElem_cons_zero] using h0
                  · right
                    simpa [enc, encodeElementsSymWithSel, joinLists, hb', List.getElem_cons_zero] using h0
              by_cases hb : b
              · -- sel，非最后元素
                have hmark_sel : tape (p + 1) = Sym.sel := by simpa [hb, mark] using hmark
                have hle_v : v ≤ bitsValue tbits := selected_ge_of_le v (w :: rest') sel' tbits (by simpa [hb] using hle_total)
                have hle_bits : bitsValue (bitsOf v) ≤ bitsValue tbits := by simpa [bitsValue_bitsOf] using hle_v
                have hlen_le_sub : (bitsOf v).length ≤ tbits.length := bitsOf_length_le_of_value_le v tbits (hpos v hv) hle_v
                have hebits_pos_sub : 1 ≤ (bitsOf v).length := by
                  rw [bitsOf_length]
                  exact List.length_pos_iff_ne_nil.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr (ne_of_gt (hpos v hv)))
                have hp_t_le_sub : p_t + (tbits.length : ℤ) ≤ p + 1 := by omega
                have hpad_sub : ∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < (p + 1) - 1 → tape i = Sym.data0 := by
                  intro i hi
                  exact hpad i ⟨hi.1, by omega⟩
                rcases subtract_element_last_correct tbits (bitsOf v) p_t (p + 1) tape hebits_pos_sub hlen_le_sub hle_bits hp_t_le_sub htarget
                    (by simpa using hbound) hhashL hpad_sub hmark_sel (by simpa [show p + 2 = p + 1 + 1 from by omega] using hvals_bits)
                    (by rcases hsep_sub with hsel_s | hnosel_s
                        · left
                          rw [← show p + 2 + ((bitsOf v).length : ℤ) = p + 1 + 1 + ((bitsOf v).length : ℤ) from by omega]
                          simpa using hsel_s
                        · right; left
                          rw [← show p + 2 + ((bitsOf v).length : ℤ) = p + 1 + 1 + ((bitsOf v).length : ℤ) from by omega]
                          simpa using hnosel_s)
                    with ⟨πsub, cfgsub, hπsub, hssub, htasub, hconssub, hpe_sub, hpe0_sub, hhashL_sub, hsep_out, hpad_out, hbound_out, hright_sub⟩
                rcases clear_counter_correct tbits (bitsOf v) p_t (p + 1) cfgsub.tape hebits_pos_sub hlen_le_sub hp_t_le_sub htasub
                    hbound_out hhashL_sub hpad_out hpe0_sub hconssub
                    with ⟨πcc, cfgcc, hπcc, hscc, hheadcc, htacc, hbound_cc, hhashL_cc, hmark_cc, hcons_cc, hkeep_cc, hgap_cc⟩
                have hbound_cc0 : cfgcc.tape p = Sym.boundary := by simpa using hbound_cc
                have hdata_cc : ∀ i : ℕ, i < (bitsOf v).length + 1 → (cfgcc.tape (p + 1 + (i : ℤ))).1 = SymKind.data0 ∨ (cfgcc.tape (p + 1 + (i : ℤ))).1 = SymKind.consumed := by
                  intro i hi
                  cases i with
                  | zero => left; simpa using congrArg (fun s : Sym => s.1) hmark_cc
                  | succ j =>
                      right
                      have hj : j < (bitsOf v).length := by simpa [hv_len] using hi
                      have h := hcons_cc j hj
                      simpa [Sym.consumed, hv_len, show p + 1 + (↑j + 1) = p + 1 + 1 + ↑j from by omega] using congrArg (fun s : Sym => s.1) h
                have hsep_cc : (cfgcc.tape (p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ))).1 = SymKind.sel ∨
                    (cfgcc.tape (p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ))).1 = SymKind.nosel := by
                  have hkeep : cfgcc.tape (p + 2 + ((bitsOf v).length : ℤ)) = tape (p + 2 + ((bitsOf v).length : ℤ)) := by
                    rw [hkeep_cc (p + 2 + ((bitsOf v).length : ℤ)) (by omega)]
                    rw [← show p + 1 + 1 + ((bitsOf v).length : ℤ) = p + 2 + ((bitsOf v).length : ℤ) from by omega]
                    exact hsep_out
                  rcases hsep_sub with hsel_s | hnosel_s
                  · left
                    simpa [show p + 1 + (↑(bitsOf v).length + 1) = p + 2 + ↑(bitsOf v).length from by omega] using (by
                      rw [hkeep]
                      exact congrArg (fun s : Sym => s.1) hsel_s)
                  · right
                    simpa [show p + 1 + (↑(bitsOf v).length + 1) = p + 2 + ↑(bitsOf v).length from by omega] using (by
                      rw [hkeep]
                      exact congrArg (fun s : Sym => s.1) hnosel_s)
                have hend_cc : (cfgcc.tape (p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ))).1 = SymKind.sel ∨
                    (cfgcc.tape (p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ))).1 = SymKind.nosel ∨
                    (cfgcc.tape (p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ))).1 = SymKind.boundary := by
                  rcases hsep_cc with hsel_cc | hnosel_cc
                  · left
                    exact hsel_cc
                  · right; left
                    exact hnosel_cc
                rcases expand_place_correct_ext ((bitsOf v).length + 1) p cfgcc.tape (by omega) hbound_cc0 hdata_cc hend_cc with
                  ⟨πe, cfge, hπe, he0, he_disj, hleft_e, hright_e, hsep_imp_e, hboundary_imp_e⟩
                -- 递归
                let tbits' : List Bool := subAllBits tbits (bitsOf v)
                have hle_total' : selectedSum (w :: rest') sel' ≤ bitsValue tbits' := by
                  dsimp [tbits']
                  have h := selected_rest_le_of_le 0 v (w :: rest') sel' tbits (by simpa [hb] using hle_total)
                  simpa [selectedSum] using h
                have hp_t_le' : p_t + (tbits'.length : ℤ) ≤ p' := by
                  dsimp [p', tbits']
                  rw [subAllBits_length]
                  omega
                have hbound' : cfge.tape p' = Sym.boundary := by
                  rcases he_disj with h4 | h22
                  · have hb : cfge.tape (p + (((bitsOf v).length + 1 : ℕ) : ℤ)) = Sym.boundary := h4.2.1
                    convert hb using 1
                    dsimp [p']
                    ring
                  · exfalso
                    have hs4 : cfge.state = 4 := hsep_imp_e hsep_cc
                    have hcontra : (22 : ℕ) = 4 := h22.1.symm.trans hs4
                    cases hcontra
                have hhashL' : cfge.tape (p_t - 1) = Sym.boundary := by
                  rw [hleft_e (p_t - 1) (by omega)]
                  exact hhashL_cc
                have htlen_eq : tbits'.length = tbits.length := by
                  dsimp [tbits']
                  rw [subAllBits_length]
                have hpad' : ∀ i : ℤ, p_t + (tbits'.length : ℤ) ≤ i ∧ i < p' → cfge.tape i = Sym.data0 := by
                  intro i hi
                  by_cases hlt_p : i < p
                  · rw [hleft_e i hlt_p]
                    have hkeep : cfgcc.tape i = cfgsub.tape i := hgap_cc i (by constructor <;> omega)
                    rw [hkeep]
                    exact hpad_out i (by constructor <;> omega)
                  · by_cases heq_p : i = p
                    · subst i
                      exact he0
                    · have : ∃ j : ℕ, j < (bitsOf v).length ∧ i = p + 1 + (j : ℤ) := by
                        have hgt : p < i := by omega
                        let j : ℕ := (i - (p + 1)).toNat
                        refine ⟨j, ?_, ?_⟩
                        · have hj : (j : ℤ) = i - (p + 1) := by
                            dsimp [j]
                            exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p + 1))
                          dsimp [p'] at hi
                          omega
                        · have hj : (j : ℤ) = i - (p + 1) := by
                            dsimp [j]
                            exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p + 1))
                          rw [hj]
                          omega
                      rcases this with ⟨j, hj, hjpos⟩
                      rw [hjpos]
                      have he_data4 : ∀ j : ℕ, j < (bitsOf v).length → cfge.tape (p + 1 + (j : ℤ)) = Sym.data0 := by
                        rcases he_disj with h4 | h22
                        · intro j hj
                          exact h4.2.2.2.2 j (by omega)
                        · exfalso
                          have hs4 : cfge.state = 4 := hsep_imp_e hsep_cc
                          have hcontra : (22 : ℕ) = 4 := h22.1.symm.trans hs4
                          cases hcontra
                      exact he_data4 j (by omega)
                have helems' : tapeAgrees cfge.tape (p' + 1) enc := by
                  intro i hi
                  by_cases h0 : i = 0
                  · subst i
                    have hkeep0 : cfge.tape (p' + 1) = tape (p' + 1) := by
                      rcases he_disj with h4 | h22
                      · have hmark' : cfge.tape (p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ)) = cfgcc.tape (p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ)) := by
                          rw [h4.2.2.2.1]
                        dsimp [p']
                        rw [show p + ((bitsOf v).length : ℤ) + 1 + 1 = p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ) from by simp only [Int.natCast_add]; omega]
                        rw [hmark']
                        rw [show p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ) = p + 1 + 1 + ((bitsOf v).length : ℤ) from by simp only [Int.natCast_add]; omega]
                        rw [hkeep_cc (p + 1 + 1 + ((bitsOf v).length : ℤ)) (by omega)]
                        rw [← hsep_out]
                      · exfalso
                        have hs4 : cfge.state = 4 := hsep_imp_e hsep_cc
                        have hcontra : (22 : ℕ) = 4 := h22.1.symm.trans hs4
                        cases hcontra
                    norm_num
                    rw [hkeep0]
                    rw [show p' + 1 = p + 2 + ((bitsOf v).length : ℤ) from by dsimp [p']; omega]
                    simpa using hrest 0 (encodeElementsSymWithSel_length_pos (w :: rest') sel' (by simp) hsel'_len)
                  · have hkeep : cfge.tape (p' + 1 + (i : ℤ)) = tape (p' + 1 + (i : ℤ)) := by
                      rw [hright_e (p' + 1 + (i : ℤ)) (by dsimp [p']; (have hi_pos : 0 < (i : ℤ) := by exact_mod_cast (Nat.pos_of_ne_zero h0)); omega)]
                      rw [hkeep_cc (p' + 1 + (i : ℤ)) (by omega)]
                      exact hright_sub (p' + 1 + (i : ℤ)) (by omega)
                    rw [hkeep]
                    rw [show p' + 1 + (i : ℤ) = p + 2 + ((bitsOf v).length : ℤ) + (i : ℤ) from by dsimp [p']; omega]
                    exact hrest i hi
                have henc_pos : 0 < enc.length :=
                  encodeElementsSymWithSel_length_pos (w :: rest') sel' (by simp) hsel'_len
                have hend' : (cfge.tape (p' + 1 + (enc.length : ℤ))).1 = SymKind.boundary := by
                  have hpos : p + 1 + (encodeElementsSymWithSel (v :: w :: rest') (b :: sel')).length = p' + 1 + (enc.length : ℤ) := by
                    have hlen_full : (encodeElementsSymWithSel (v :: w :: rest') (b :: sel')).length = (1 + (bitsOf v).length) + enc.length := by
                      calc
                        (encodeElementsSymWithSel (v :: w :: rest') (b :: sel')).length
                            = (1 + (encodeBitsSymNative v).length) + (encodeElementsSymWithSel (w :: rest') sel').length := by
                              simp [encodeElementsSymWithSel, joinLists, enc]
                              rw [show (encodeBitsSymNative v).length = (bitsOf v).length from by
                                simpa [show encodeBitsSym v = encodeBitsSymNative v from rfl] using henc_len]
                              ac_rfl
                        _ = (1 + (bitsOf v).length) + enc.length := by
                              rw [show (encodeBitsSymNative v).length = (bitsOf v).length from by
                                simpa [show encodeBitsSym v = encodeBitsSymNative v from rfl] using henc_len]
                              try
                                change (1 + (bitsOf v).length) + (encodeElementsSymWithSel (w :: rest') sel').length =
                                  (1 + (bitsOf v).length) + (encodeElementsSymWithSel (w :: rest') sel').length
                                rfl
                    rw [hlen_full]
                    dsimp [p']
                    repeat rw [Int.natCast_add]
                    omega
                  have hkeep : cfge.tape (p' + 1 + (enc.length : ℤ)) = tape (p' + 1 + (enc.length : ℤ)) := by
                    rw [hright_e (p' + 1 + (enc.length : ℤ)) (by dsimp [p']; (have henc_pos' : 0 < (enc.length : ℤ) := by exact_mod_cast henc_pos); omega)]
                    rw [hkeep_cc (p' + 1 + (enc.length : ℤ)) (by omega)]
                    exact hright_sub (p' + 1 + (enc.length : ℤ)) (by omega)
                  rw [hkeep, ← hpos]
                  exact hend
                have htarget' : tapeAgrees cfge.tape p_t (targetTape 0 tbits') := by
                  intro i hi
                  have hlen : (targetTape 0 tbits').length = tbits'.length := by
                    simp [targetTape_length, subAllBits_length]
                  have hik : i < tbits'.length := by simpa [hlen] using hi
                  have hi_lt : p_t + (i : ℤ) < p := by omega
                  rw [hleft_e (p_t + (i : ℤ)) hi_lt]
                  simpa [tbits'] using htacc i hi
                have hpos' : ∀ v' ∈ w :: rest', 0 < v' := by
                  intro v' hv'
                  exact hpos v' (by simp [hv'])
                rcases ih sel' tbits' p' cfge.tape (by simp) hpos' hsel'_len hp_t_le' htarget' hbound' hhashL' hpad' helems' hend' hle_total'
                    with ⟨πrec, cfgrec, hπrec, hsrec, htarec, hheadrec, hclearrec, hhashLrec, hgaprec, hrightrec, hkeeprec⟩
                have htotal : SymSteps VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) (πsub ++ πcc ++ πe ++ πrec) cfgrec := by
                  have hsub : SymSteps VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) πsub cfgsub := by simpa using hπsub
                  have hcc : SymSteps VerifierSym.transition cfgsub πcc cfgcc := by
                    have hcfg : cfgsub = SymConfig.mk 84 cfgsub.tape (p + 1 + ((bitsOf v).length : ℤ)) := by
                      cases cfgsub with
                      | mk s t hp =>
                          dsimp [SymConfig.mk]
                          rw [show s = 84 from hssub]
                          rw [show hp = p + 1 + ((bitsOf v).length : ℤ) from hpe_sub]
                    rw [hcfg]
                    exact hπcc
                  have he : SymSteps VerifierSym.transition cfgcc πe cfge := by
                    have hcfg : cfgcc = SymConfig.mk 20 cfgcc.tape p := by
                      cases cfgcc with
                      | mk s t hp =>
                          dsimp [SymConfig.mk]
                          rw [show s = 20 from hscc]
                          rw [show hp = p from by simpa using hheadcc]
                    rw [hcfg]
                    exact hπe
                  have hrec : SymSteps VerifierSym.transition cfge πrec cfgrec := by
                    have hcfg : cfge = SymConfig.mk 4 cfge.tape (p' + 1) := by
                      cases cfge with
                      | mk s t hp =>
                          dsimp [SymConfig.mk]
                          have hs4 : s = 4 := by
                            simpa using hsep_imp_e hsep_cc
                          rw [hs4]
                          have hhead : hp = p' + 1 := by
                            rcases he_disj with h4 | h22
                            · simpa [show p + (↑(bitsOf v).length + 1) + 1 = p' + 1 from by dsimp [p']; omega] using h4.2.2.1
                            · exfalso
                              have hcontra : (4 : ℕ) = 22 := (hsep_imp_e hsep_cc).symm.trans h22.1
                              cases hcontra
                          rw [hhead]
                    rw [hcfg]
                    exact hπrec
                  have h1 : SymSteps VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) (πsub ++ πcc) cfgcc :=
                    SymSteps_trans VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) cfgsub cfgcc πsub πcc hsub hcc
                  have h2 : SymSteps VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) (πsub ++ πcc ++ πe) cfge :=
                    SymSteps_trans VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) cfgcc cfge (πsub ++ πcc) πe h1 he
                  exact SymSteps_trans VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) cfge cfgrec (πsub ++ πcc ++ πe) πrec h2 hrec
                refine ⟨πsub ++ πcc ++ πe ++ πrec, cfgrec, htotal, hsrec, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · have htarec' : tapeAgrees cfgrec.tape p_t (targetTape 0 (subAllSelected 0 tbits' (w :: rest') sel')) := htarec
                  simpa [subAllSelected, hb, tbits'] using htarec'
                · -- headPos
                  have hlen_full : (encodeElementsSymWithSel (v :: w :: rest') (b :: sel')).length = ((bitsOf v).length + 1) + enc.length := by
                    calc
                      (encodeElementsSymWithSel (v :: w :: rest') (b :: sel')).length
                          = (1 + (encodeBitsSymNative v).length) + (encodeElementsSymWithSel (w :: rest') sel').length := by
                            simp [encodeElementsSymWithSel, joinLists, enc]
                            rw [show (encodeBitsSymNative v).length = (bitsOf v).length from by
                              simpa [show encodeBitsSym v = encodeBitsSymNative v from rfl] using henc_len]
                            ac_rfl
                      _ = ((bitsOf v).length + 1) + enc.length := by
                            rw [show (encodeBitsSymNative v).length = (bitsOf v).length from by
                              simpa [show encodeBitsSym v = encodeBitsSymNative v from rfl] using henc_len]
                            try
                              change (1 + (bitsOf v).length) + (encodeElementsSymWithSel (w :: rest') sel').length =
                                ((bitsOf v).length + 1) + (encodeElementsSymWithSel (w :: rest') sel').length
                              omega
                  rw [hlen_full]
                  dsimp [p'] at hheadrec
                  have harith : p + ((((bitsOf v).length + 1) + enc.length : ℕ) : ℤ) + 1 = p + ((bitsOf v).length : ℤ) + 1 + (enc.length : ℤ) + 1 := by
                    rw [Int.natCast_add]
                    norm_num
                    ring
                  rw [harith]
                  ring_nf at hheadrec ⊢
                  exact hheadrec
                · -- 清空
                  intro i hi
                  by_cases hilt : i < p'
                  · exact hgaprec i (by constructor <;> omega)
                  · exact hclearrec i (by omega)
                · -- #ₗ 保持
                  exact hhashLrec
                · -- gap data0
                  intro i hi
                  exact hgaprec i (by constructor <;> omega)
                · -- 右不变：i > p+1+chosen.len
                  intro i hi
                  have hlen_full : (encodeElementsSymWithSel (v :: w :: rest') (b :: sel')).length = ((bitsOf v).length + 1) + enc.length := by
                    calc
                      (encodeElementsSymWithSel (v :: w :: rest') (b :: sel')).length
                          = (1 + (encodeBitsSymNative v).length) + (encodeElementsSymWithSel (w :: rest') sel').length := by
                            simp [encodeElementsSymWithSel, joinLists, enc]
                            rw [show (encodeBitsSymNative v).length = (bitsOf v).length from by
                              simpa [show encodeBitsSym v = encodeBitsSymNative v from rfl] using henc_len]
                            ac_rfl
                      _ = ((bitsOf v).length + 1) + enc.length := by
                            rw [show (encodeBitsSymNative v).length = (bitsOf v).length from by
                              simpa [show encodeBitsSym v = encodeBitsSymNative v from rfl] using henc_len]
                            try
                              change (1 + (bitsOf v).length) + (encodeElementsSymWithSel (w :: rest') sel').length =
                                ((bitsOf v).length + 1) + (encodeElementsSymWithSel (w :: rest') sel').length
                              omega
                  have hrec := hrightrec i (by
                    have hlen_full_z : p + 1 + ((encodeElementsSymWithSel (v :: w :: rest') (b :: sel')).length : ℤ) = p' + 1 + (enc.length : ℤ) := by
                      rw [hlen_full]
                      repeat rw [Nat.cast_add]
                      norm_num
                      dsimp [p']
                      ring
                    rw [hlen_full_z] at hi
                    exact hi)
                  rw [hrec]
                  rw [hright_e i (by
                    rw [hlen_full] at hi
                    repeat rw [Nat.cast_add] at hi
                    have henc_pos' : 0 ≤ (enc.length : ℤ) := by exact_mod_cast Nat.zero_le enc.length
                    omega)]
                  rw [hkeep_cc i (by omega)]
                  exact hright_sub i (by omega)
                · -- cfgrec.tape cfgrec.headPos = tape cfgrec.headPos（#₁ 值保持）
                  rw [hkeeprec]
                  have hhead' : cfgrec.headPos = p + ((((bitsOf v).length + 1) + enc.length : ℕ) : ℤ) + 1 := by
                    dsimp [p'] at hheadrec
                    have harith : p + ((((bitsOf v).length + 1) + enc.length : ℕ) : ℤ) + 1 = p + ((bitsOf v).length : ℤ) + 1 + (enc.length : ℤ) + 1 := by
                      rw [Int.natCast_add]
                      norm_num
                      ring
                    rw [harith]
                    ring_nf at hheadrec ⊢
                    exact hheadrec
                  have hre : cfge.tape (p + ((((bitsOf v).length + 1) + enc.length : ℕ) : ℤ) + 1) =
                      cfgcc.tape (p + ((((bitsOf v).length + 1) + enc.length : ℕ) : ℤ) + 1) := by
                    exact hright_e (p + ((((bitsOf v).length + 1) + enc.length : ℕ) : ℤ) + 1) (by
                      have hnp : (1 : ℤ) ≤ (enc.length : ℤ) := by exact_mod_cast (Nat.succ_le_of_lt henc_pos)
                      omega)
                  have hkc : cfgcc.tape (p + ((((bitsOf v).length + 1) + enc.length : ℕ) : ℤ) + 1) =
                      tape (p + ((((bitsOf v).length + 1) + enc.length : ℕ) : ℤ) + 1) := by
                    have h1 : cfgcc.tape (p + ((((bitsOf v).length + 1) + enc.length : ℕ) : ℤ) + 1) =
                        cfgsub.tape (p + ((((bitsOf v).length + 1) + enc.length : ℕ) : ℤ) + 1) := by
                      exact hkeep_cc (p + ((((bitsOf v).length + 1) + enc.length : ℕ) : ℤ) + 1) (by
                        have hnp : (1 : ℤ) ≤ (enc.length : ℤ) := by exact_mod_cast (Nat.succ_le_of_lt henc_pos)
                        omega)
                    have h2 : cfgsub.tape (p + ((((bitsOf v).length + 1) + enc.length : ℕ) : ℤ) + 1) =
                        tape (p + ((((bitsOf v).length + 1) + enc.length : ℕ) : ℤ) + 1) := by
                      exact hright_sub (p + ((((bitsOf v).length + 1) + enc.length : ℕ) : ℤ) + 1) (by
                        have hnp : (1 : ℤ) ≤ (enc.length : ℤ) := by exact_mod_cast (Nat.succ_le_of_lt henc_pos)
                        omega)
                    exact h1.trans h2
                  rw [hhead']
                  exact hre.trans hkc
              · -- nosel，非最后元素
                have hmark_nosel : tape (p + 1) = Sym.nosel := by simpa [hb, mark] using hmark
                rcases clear_element_correct (bitsOf v) (p + 1) tape hmark_nosel (by simpa [show (p + 1) - 1 = p from by omega] using hbound) (by simpa [show p + 2 = p + 1 + 1 from by omega] using hvals_bits) (by
                    rcases hsep_sub with hsel_s | hnosel_s
                    · left
                      simpa [← hv_len, show p + 2 + ↑(bitsOf v).length = p + 1 + 1 + ↑(bitsOf v).length from by omega] using hsel_s
                    · right; left
                      simpa [← hv_len, show p + 2 + ↑(bitsOf v).length = p + 1 + 1 + ↑(bitsOf v).length from by omega] using hnosel_s)
                    with ⟨πcl, cfgcl, hπcl, hscl, hheadcl, hbnd22_cl, hsel51_cl, htacl, hbound_cl, hpem1_cl, hmark_cl, hleft_cl, hkeep_sep_cl, hright_cl⟩
                -- 右端是 sel/nosel → 51 停（不在 #₁ 判定）
                have hcl51 : cfgcl.state = 51 ∧ cfgcl.headPos = p + 1 + ↑(bitsOf v).length := by
                  have hsel51' : (tape (p + 1 + 1 + ↑(bitsOf v).length)).1 = SymKind.sel ∨
                      (tape (p + 1 + 1 + ↑(bitsOf v).length)).1 = SymKind.nosel := by
                    rcases hsep_sub with hsel_s | hnosel_s
                    · left
                      simpa [Sym.sel, Sym.nosel, ← hv_len, show p + 2 + ↑(bitsOf v).length = p + 1 + 1 + ↑(bitsOf v).length from by omega] using congrArg (fun s : Sym => s.1) hsel_s
                    · right
                      simpa [Sym.sel, Sym.nosel, ← hv_len, show p + 2 + ↑(bitsOf v).length = p + 1 + 1 + ↑(bitsOf v).length from by omega] using congrArg (fun s : Sym => s.1) hnosel_s
                  have h := hsel51_cl hsel51'
                  exact ⟨h.1, by simpa [show p + 1 + 1 + ↑(bitsOf v).length = p + 1 + ↑(bitsOf v).length + 1 from by omega] using h.2⟩
                -- 51 读数据区末位（被清成 data0）→ 写 #₀ 回 4 右移
                have hebits_pos : 1 ≤ (bitsOf v).length := by
                  rw [bitsOf_length]
                  exact List.length_pos_iff_ne_nil.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr (ne_of_gt (hpos v hv)))
                have hdata51 : cfgcl.tape (p + 1 + ↑(bitsOf v).length) = Sym.data0 := by
                  have hlt : (bitsOf v).length - 1 < (bitsOf v).length := by omega
                  have h := htacl ((bitsOf v).length - 1) (by simpa using hlt)
                  simpa [show p + 1 + 1 + ↑((bitsOf v).length - 1) = p + 1 + ↑(bitsOf v).length from by omega] using h
                let r51 : SymTransResult := { nextState := 4, writeSym := Sym.boundary, moveDir := Dir.R }
                let step51 : SymStep := { fromState := 51, readSym := Sym.data0, result := r51 }
                let cfg51 : SymConfig := symStepConfig cfgcl step51.result
                have hstep51 : SymSteps VerifierSym.transition cfgcl [step51] cfg51 := by
                  refine SymSteps.cons [] step51 cfgcl SymSteps.nil ?_ ?_ ?_
                  · rw [hcl51.1]
                  · change Sym.data0 = cfgcl.tape cfgcl.headPos
                    rw [hcl51.2]
                    exact hdata51.symm
                  · rw [hcl51.1, hcl51.2, hdata51]
                    decide
                -- 递归（tbits 不变）
                have hle_total' : selectedSum (w :: rest') sel' ≤ bitsValue tbits := by
                  have h := selected_rest_le_of_not v (w :: rest') sel' tbits (by simpa [hb] using hle_total)
                  simpa [selectedSum] using h
                have hp_t_le' : p_t + (tbits.length : ℤ) ≤ p' := by dsimp [p']; omega
                have htarget' : tapeAgrees cfg51.tape p_t (targetTape 0 tbits) := by
                  intro i hi
                  have hlen : (targetTape 0 tbits).length = tbits.length := by simp [targetTape_length]
                  have hik : i < tbits.length := by simpa [hlen] using hi
                  have htape51 : cfg51.tape (p_t + (i : ℤ)) = cfgcl.tape (p_t + (i : ℤ)) := by
                    dsimp [cfg51, symStepConfig, step51, r51, p']
                    rw [hcl51.2]
                    by_cases heq : p_t + (i : ℤ) = p + 1 + ↑(bitsOf v).length
                    · exfalso
                      omega
                    · rw [if_neg heq]
                  rw [htape51]
                  rw [hleft_cl (p_t + (i : ℤ)) (by omega)]
                  exact htarget i (by simpa [hlen] using hik)
                have hbound' : cfg51.tape p' = Sym.boundary := by
                  dsimp [cfg51, symStepConfig, step51, r51, p']
                  rw [hcl51.2]
                  rw [if_pos (by omega : p + ↑(bitsOf v).length + 1 = p + 1 + ↑(bitsOf v).length)]
                have hhashL' : cfg51.tape (p_t - 1) = Sym.boundary := by
                  dsimp [cfg51, symStepConfig, step51, r51, p']
                  rw [hcl51.2]
                  by_cases heq : p_t - 1 = p + 1 + ↑(bitsOf v).length
                  · exfalso
                    omega
                  · rw [if_neg heq]
                    rw [hleft_cl (p_t - 1) (by omega)]
                    exact hhashL
                have hpad' : ∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p' → cfg51.tape i = Sym.data0 := by
                  intro i hi
                  have htape51 : cfg51.tape i = cfgcl.tape i := by
                    dsimp [cfg51, symStepConfig, step51, r51, p']
                    rw [hcl51.2]
                    by_cases heq : i = p + 1 + ↑(bitsOf v).length
                    · exfalso
                      omega
                    · rw [if_neg heq]
                  rw [htape51]
                  by_cases hlt_p : i < p
                  · rw [hleft_cl i (by omega)]
                    exact hpad i ⟨hi.1, hlt_p⟩
                  · by_cases heq_p : i = p
                    · subst i
                      simpa [show (p + 1) - 1 = p from by omega] using hpem1_cl
                    · have : ∃ j : ℕ, j < (bitsOf v).length ∧ i = p + 1 + (j : ℤ) := by
                        have hgt : p < i := by omega
                        let j : ℕ := (i - (p + 1)).toNat
                        refine ⟨j, ?_, ?_⟩
                        · have hj : (j : ℤ) = i - (p + 1) := by
                            dsimp [j]
                            exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p + 1))
                          dsimp [p'] at hi
                          omega
                        · have hj : (j : ℤ) = i - (p + 1) := by
                            dsimp [j]
                            exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p + 1))
                          rw [hj]
                          omega
                      rcases this with ⟨j, hj, hjpos⟩
                      rw [hjpos]
                      by_cases hj0 : j = 0
                      · subst j
                        norm_num
                        exact hmark_cl
                      · have hj1 : 1 ≤ j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj0)
                        let j' : ℕ := j - 1
                        have hj'_lt : j' < (bitsOf v).length := by
                          dsimp [j']
                          omega
                        have h := htacl j' (by simpa using hj'_lt)
                        simpa [show p + 1 + 1 + ↑j' = p + 1 + ↑j from by dsimp [j']; omega] using h
                have henc_pos : 0 < enc.length :=
                  encodeElementsSymWithSel_length_pos (w :: rest') sel' (by simp) hsel'_len
                have helems' : tapeAgrees cfg51.tape (p' + 1) enc := by
                  intro i hi
                  have htape51 : cfg51.tape (p' + 1 + (i : ℤ)) = cfgcl.tape (p' + 1 + (i : ℤ)) := by
                    dsimp [cfg51, symStepConfig, step51, r51, p']
                    rw [hcl51.2]
                    by_cases heq : p' + 1 + (i : ℤ) = p + 1 + ↑(bitsOf v).length
                    · exfalso
                      omega
                    · rw [if_neg heq]
                  rw [htape51]
                  by_cases hi0 : i = 0
                  · subst i
                    norm_num
                    rw [show p' + 1 = p + 2 + ↑(bitsOf v).length from by dsimp [p']; omega]
                    rw [show p + 2 + ↑(bitsOf v).length = p + 1 + 1 + ↑(bitsOf v).length from by omega]
                    rw [hkeep_sep_cl]
                    simpa [show p + 1 + 1 + ↑(bitsOf v).length = p + 2 + ↑(bitsOf v).length from by omega] using hrest 0 (by simpa [enc] using henc_pos)
                  · have hi_gt : 0 < i := Nat.pos_of_ne_zero hi0
                    rw [hright_cl (p' + 1 + (i : ℤ)) (by omega)]
                    simpa [show p' + 1 + (i : ℤ) = p + 2 + ↑(bitsOf v).length + (i : ℤ) from by dsimp [p']; omega] using hrest i hi
                have hend' : (cfg51.tape (p' + 1 + (enc.length : ℤ))).1 = SymKind.boundary := by
                  have hkeep : cfg51.tape (p' + 1 + (enc.length : ℤ)) = tape (p' + 1 + (enc.length : ℤ)) := by
                    dsimp [cfg51, symStepConfig, step51, r51, p']
                    rw [hcl51.2]
                    by_cases heq : p' + 1 + (enc.length : ℤ) = p + 1 + ↑(bitsOf v).length
                    · exfalso
                      omega
                    · rw [if_neg heq]
                      rw [hright_cl (p' + 1 + (enc.length : ℤ)) (by dsimp [p']; (have henc_pos' : 0 < (enc.length : ℤ) := by exact_mod_cast henc_pos); omega)]
                  rw [hkeep]
                  have hpos : p + 1 + (encodeElementsSymWithSel (v :: w :: rest') (b :: sel')).length = p' + 1 + (enc.length : ℤ) := by
                    have hlen_full : (encodeElementsSymWithSel (v :: w :: rest') (b :: sel')).length = (1 + (bitsOf v).length) + enc.length := by
                      calc
                        (encodeElementsSymWithSel (v :: w :: rest') (b :: sel')).length
                            = (1 + (encodeBitsSymNative v).length) + (encodeElementsSymWithSel (w :: rest') sel').length := by
                              simp [encodeElementsSymWithSel, joinLists, enc]
                              rw [show (encodeBitsSymNative v).length = (bitsOf v).length from by
                                simpa [show encodeBitsSym v = encodeBitsSymNative v from rfl] using henc_len]
                              ac_rfl
                        _ = (1 + (bitsOf v).length) + enc.length := by
                              rw [show (encodeBitsSymNative v).length = (bitsOf v).length from by
                                simpa [show encodeBitsSym v = encodeBitsSymNative v from rfl] using henc_len]
                              try
                                change (1 + (bitsOf v).length) + (encodeElementsSymWithSel (w :: rest') sel').length =
                                  (1 + (bitsOf v).length) + (encodeElementsSymWithSel (w :: rest') sel').length
                                rfl
                    rw [hlen_full]
                    dsimp [p']
                    repeat rw [Int.natCast_add]
                    omega
                  rw [← hpos]
                  exact hend
                have hpos' : ∀ v' ∈ w :: rest', 0 < v' := by
                  intro v' hv'
                  exact hpos v' (by simp [hv'])
                rcases ih sel' tbits p' cfg51.tape (by simp) hpos' hsel'_len hp_t_le' htarget' hbound' hhashL' hpad' helems' hend' hle_total'
                    with ⟨πrec, cfgrec, hπrec, hsrec, htarec, hheadrec, hclearrec, hhashLrec, hgaprec, hrightrec, hkeeprec⟩
                have htotal : SymSteps VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) (πcl ++ [step51] ++ πrec) cfgrec := by
                  have hcl : SymSteps VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) πcl cfgcl := by simpa using hπcl
                  have hrec : SymSteps VerifierSym.transition cfg51 πrec cfgrec := by
                    have hcfg : cfg51 = SymConfig.mk 4 cfg51.tape (p' + 1) := by
                      cases cfgcl with
                      | mk s t hp =>
                          have hhp : hp = p + 1 + ↑(bitsOf v).length := by
                            simpa using hcl51.2
                          dsimp [cfg51, symStepConfig, step51, r51, SymConfig.mk, Dir.toInt]
                          rw [hhp]
                          simp [p', show p + 1 + ↑(bitsOf v).length + 1 = p' + 1 from by dsimp [p']; omega]
                    rw [hcfg]
                    exact hπrec
                  have h1 : SymSteps VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) (πcl ++ [step51]) cfg51 :=
                    SymSteps_trans VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) cfgcl cfg51 πcl [step51] hcl hstep51
                  exact SymSteps_trans VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) cfg51 cfgrec (πcl ++ [step51]) πrec h1 hrec
                refine ⟨πcl ++ [step51] ++ πrec, cfgrec, htotal, hsrec, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · have htarec' : tapeAgrees cfgrec.tape p_t (targetTape 0 (subAllSelected 0 tbits (w :: rest') sel')) := htarec
                  simpa [subAllSelected, hb] using htarec'
                · -- headPos
                  have hlen_full : (encodeElementsSymWithSel (v :: w :: rest') (b :: sel')).length = ((bitsOf v).length + 1) + enc.length := by
                    calc
                      (encodeElementsSymWithSel (v :: w :: rest') (b :: sel')).length
                          = (1 + (encodeBitsSymNative v).length) + (encodeElementsSymWithSel (w :: rest') sel').length := by
                            simp [encodeElementsSymWithSel, joinLists, enc]
                            rw [show (encodeBitsSymNative v).length = (bitsOf v).length from by
                              simpa [show encodeBitsSym v = encodeBitsSymNative v from rfl] using henc_len]
                            ac_rfl
                      _ = ((bitsOf v).length + 1) + enc.length := by
                            rw [show (encodeBitsSymNative v).length = (bitsOf v).length from by
                              simpa [show encodeBitsSym v = encodeBitsSymNative v from rfl] using henc_len]
                            try
                              change (1 + (bitsOf v).length) + (encodeElementsSymWithSel (w :: rest') sel').length =
                                ((bitsOf v).length + 1) + (encodeElementsSymWithSel (w :: rest') sel').length
                              omega
                  rw [hlen_full]
                  dsimp [p'] at hheadrec
                  have harith : p + ((((bitsOf v).length + 1) + enc.length : ℕ) : ℤ) + 1 = p + ((bitsOf v).length : ℤ) + 1 + (enc.length : ℤ) + 1 := by
                    rw [Int.natCast_add]
                    norm_num
                    ring
                  rw [harith]
                  ring_nf at hheadrec ⊢
                  exact hheadrec
                · -- 清空
                  intro i hi
                  by_cases hilt : i < p'
                  · exact hgaprec i (by constructor <;> omega)
                  · exact hclearrec i (by omega)
                · -- #ₗ 保持
                  exact hhashLrec
                · -- gap data0
                  intro i hi
                  exact hgaprec i (by constructor <;> omega)
                · -- 右不变：i > p+1+chosen.len
                  intro i hi
                  have hlen_full : (encodeElementsSymWithSel (v :: w :: rest') (b :: sel')).length = ((bitsOf v).length + 1) + enc.length := by
                    calc
                      (encodeElementsSymWithSel (v :: w :: rest') (b :: sel')).length
                          = (1 + (encodeBitsSymNative v).length) + (encodeElementsSymWithSel (w :: rest') sel').length := by
                            simp [encodeElementsSymWithSel, joinLists, enc]
                            rw [show (encodeBitsSymNative v).length = (bitsOf v).length from by
                              simpa [show encodeBitsSym v = encodeBitsSymNative v from rfl] using henc_len]
                            ac_rfl
                      _ = ((bitsOf v).length + 1) + enc.length := by
                            rw [show (encodeBitsSymNative v).length = (bitsOf v).length from by
                              simpa [show encodeBitsSym v = encodeBitsSymNative v from rfl] using henc_len]
                            try
                              change (1 + (bitsOf v).length) + (encodeElementsSymWithSel (w :: rest') sel').length =
                                ((bitsOf v).length + 1) + (encodeElementsSymWithSel (w :: rest') sel').length
                              omega
                  have hrec := hrightrec i (by
                    have hlen_full_z : p + 1 + ((encodeElementsSymWithSel (v :: w :: rest') (b :: sel')).length : ℤ) = p' + 1 + (enc.length : ℤ) := by
                      rw [hlen_full]
                      repeat rw [Nat.cast_add]
                      norm_num
                      dsimp [p']
                      ring
                    rw [hlen_full_z] at hi
                    exact hi)
                  rw [hrec]
                  have htape51 : cfg51.tape i = cfgcl.tape i := by
                    dsimp [cfg51, symStepConfig, step51, r51, p']
                    rw [hcl51.2]
                    by_cases heq : i = p + 1 + ↑(bitsOf v).length
                    · exfalso
                      omega
                    · rw [if_neg heq]
                  rw [htape51]
                  exact hright_cl i (by omega)
                · -- cfgrec.tape cfgrec.headPos = tape cfgrec.headPos（#₁ 值保持）
                  rw [hkeeprec]
                  have hhead' : cfgrec.headPos = p + ((((bitsOf v).length + 1) + enc.length : ℕ) : ℤ) + 1 := by
                    dsimp [p'] at hheadrec
                    have harith : p + ((((bitsOf v).length + 1) + enc.length : ℕ) : ℤ) + 1 = p + ((bitsOf v).length : ℤ) + 1 + (enc.length : ℤ) + 1 := by
                      rw [Int.natCast_add]
                      norm_num
                      ring
                    rw [harith]
                    ring_nf at hheadrec ⊢
                    exact hheadrec
                  have h51k : cfg51.tape (p + ((((bitsOf v).length + 1) + enc.length : ℕ) : ℤ) + 1) =
                      cfgcl.tape (p + ((((bitsOf v).length + 1) + enc.length : ℕ) : ℤ) + 1) := by
                    dsimp [cfg51]
                    simp only [symStepConfig, SymConfig.mk, step51, r51]
                    rw [if_neg (by
                      have hhp : cfgcl.headPos = p + 1 + ((bitsOf v).length : ℤ) := hcl51.2
                      rw [hhp]
                      omega)]
                  have hclk : cfgcl.tape (p + ((((bitsOf v).length + 1) + enc.length : ℕ) : ℤ) + 1) =
                      tape (p + ((((bitsOf v).length + 1) + enc.length : ℕ) : ℤ) + 1) := by
                    exact hright_cl (p + ((((bitsOf v).length + 1) + enc.length : ℕ) : ℤ) + 1) (by
                      have hnp : (1 : ℤ) ≤ (enc.length : ℤ) := by exact_mod_cast (Nat.succ_le_of_lt henc_pos)
                      omega)
                  rw [hhead']
                  exact h51k.trans hclk
-- ============================================================================
-- symVerifier_correct 的辅助引理
-- ============================================================================

/-- `targetTape 0` 就是 `bitsToSym`（无已处理前缀）。 -/
@[simp] lemma targetTape_zero (bits : List Bool) :
    targetTape 0 bits = bitsToSym bits := by
  simp [targetTape]


/-- 全 false 的位列表经 `bitsToSym` 得到全 Sym.data0 符号。 -/
lemma bitsToSym_all_false_data0 (bits : List Bool) (h : ∀ b ∈ bits, b = false) :
    ∀ s ∈ bitsToSym bits, s = Sym.data0 := by
  intro s hs
  rcases List.mem_map.mp hs with ⟨b, hb, rfl⟩
  have hb' : b = false := h b hb
  simp [bitsToSym, hb']

/-- 状态 22 读 #₁（boundary, m=1）→ 23 L（进判定阶段，与转移表 22 行一致）。
    判定链（23 全 0 左扫 → 100 接受）由判定引理给出。 -/
lemma check_accept_left (headPos : ℤ) (tape : ℤ → Sym)
    (hbound : tape headPos = Sym.mk SymKind.boundary true) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 22 tape headPos) π cfg' ∧
      cfg'.state = 23 := by
  let r : SymTransResult := { nextState := 23, writeSym := Sym.mk SymKind.boundary true, moveDir := Dir.L }
  let step : SymStep := { fromState := 22, readSym := Sym.mk SymKind.boundary true, result := r }
  refine ⟨[step], symStepConfig (SymConfig.mk 22 tape headPos) step.result, ?_, ?_⟩
  · refine SymSteps.cons [] step (SymConfig.mk 22 tape headPos) SymSteps.nil ?_ ?_ ?_
    · rfl
    · change Sym.mk SymKind.boundary true = tape headPos
      rw [hbound]
    · change step.result ∈ VerifierSym.transition (22, tape headPos)
      rw [hbound]
      decide
  · rfl

/-- 单值转移：q 在流程状态集中时 transition (q, s) 是单例。 -/
lemma transition_singleton_ge4 (q : ℕ) (s : Sym)
    (hq : q ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 76, 77, 81, 84, 85, 86, 87, 38, 51, 23} : Finset ℕ)) :
    (VerifierSym.transition (q, s)).card = 1 := by
  fin_cases hq <;> rcases s with ⟨k, mk⟩ <;> cases k <;> cases mk <;> decide

/-- 单值转移的成员唯一性。 -/
lemma transition_unique_ge4 (q : ℕ) (s : Sym)
    (hq : q ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 76, 77, 81, 84, 85, 86, 87, 38, 51, 23} : Finset ℕ))
    {r r' : SymTransResult} (hr : r ∈ VerifierSym.transition (q, s)) (hr' : r' ∈ VerifierSym.transition (q, s)) :
    r = r' := by
  have hcard := transition_singleton_ge4 q s hq
  rcases Finset.card_eq_one.mp hcard with ⟨r₀, hr₀⟩
  have : r = r₀ := by
    have : r ∈ ({r₀} : Finset SymTransResult) := by simpa [hr₀] using hr
    simpa using this
  rw [this]
  have : r' = r₀ := by
    have : r' ∈ ({r₀} : Finset SymTransResult) := by simpa [hr₀] using hr'
    simpa using this
  rw [this]

/-- 转移保 detset（q ∈ 合法状态集时 nextState 仍在其中；23/100/101 是判定/吸收态，
    76/77/81/84/85/86/87/38/51 是流程中间态）。 -/
lemma transition_nextState_in_det (q : ℕ) (s : Sym) (r : SymTransResult)
    (hq : q ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 76, 77, 81, 84, 85, 86, 87, 38, 51, 23} : Finset ℕ))
    (hr : r ∈ VerifierSym.transition (q, s)) :
    (4 ≤ r.nextState ∧ r.nextState ≤ 22) ∨ r.nextState = 51 ∨ r.nextState = 81 ∨ r.nextState = 84 ∨
      r.nextState = 23 ∨ r.nextState = 100 ∨ r.nextState = 101 ∨ r.nextState = 76 ∨ r.nextState = 77 ∨
      r.nextState = 85 ∨ r.nextState = 86 ∨ r.nextState = 87 ∨ r.nextState = 38 ∨ r.nextState = 28 := by
  by_cases hq_legal : q ∈ VerifierSym.legalStates
  · have hq_cases : q = 4 ∨ q = 5 ∨ q = 8 ∨ q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 12 ∨ q = 13 ∨ q = 14 ∨ q = 20 ∨ q = 21 ∨ q = 22 ∨ q = 76 ∨ q = 77 ∨ q = 81 ∨ q = 84 ∨ q = 85 ∨ q = 86 ∨ q = 87 ∨ q = 38 ∨ q = 51 ∨ q = 23 := by
      fin_cases hq <;> simp
    rcases hq_cases with hq4 | hq5 | hq8 | hq9 | hq10 | hq11 | hq12 | hq13 | hq14 | hq20 | hq21 | hq22 | hq76 | hq77 | hq81 | hq84 | hq85 | hq86 | hq87 | hq38 | hq51 | hq23
    · -- q = 4
      subst q
      rcases s with ⟨k, b⟩
      cases k
      · -- data0
        cases b
        · -- 4 data0 false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data0 false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data0 false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 4 data0 true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data0 true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data0 true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- data1
        cases b
        · -- 4 data1 false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data1 false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data1 false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 4 data1 true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data1 true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data1 true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- consumed
        cases b
        · -- 4 consumed false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 4 consumed true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- alpha
        cases b
        · -- 4 alpha false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 4 alpha true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- sel
        cases b
        · -- 4 sel false → 5 (Sym.data0) R
          have hr' : r ∈ ({SymTransResult.mk 5 (Sym.data0) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 5 (Sym.data0) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 4 sel true → 5 (Sym.data0) R
          have hr' : r ∈ ({SymTransResult.mk 5 (Sym.data0) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 5 (Sym.data0) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- nosel
        cases b
        · -- 4 nosel false → 20 (Sym.data0) L
          have hr' : r ∈ ({SymTransResult.mk 20 (Sym.data0) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 20 (Sym.data0) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 4 nosel true → 20 (Sym.data0) L
          have hr' : r ∈ ({SymTransResult.mk 20 (Sym.data0) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 20 (Sym.data0) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- beta
        cases b
        · -- 4 beta false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 4 beta true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- boundary
        cases b
        · -- 4 boundary false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 4 boundary true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide

    · -- q = 5
      subst q
      rcases s with ⟨k, b⟩
      cases k
      · -- data0
        cases b
        · -- 5 data0 false → 8 (Sym.consumed) L
          have hr' : r ∈ ({SymTransResult.mk 8 (Sym.consumed) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 8 (Sym.consumed) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 5 data0 true → 8 (Sym.consumed) L
          have hr' : r ∈ ({SymTransResult.mk 8 (Sym.consumed) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 8 (Sym.consumed) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- data1
        cases b
        · -- 5 data1 false → 76 (Sym.consumed) L
          have hr' : r ∈ ({SymTransResult.mk 76 (Sym.consumed) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 76 (Sym.consumed) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 5 data1 true → 76 (Sym.consumed) L
          have hr' : r ∈ ({SymTransResult.mk 76 (Sym.consumed) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 76 (Sym.consumed) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- consumed
        cases b
        · -- 5 consumed false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 5 consumed true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- alpha
        cases b
        · -- 5 alpha false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 5 alpha true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- sel
        cases b
        · -- 5 sel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 5 sel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- nosel
        cases b
        · -- 5 nosel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 5 nosel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- beta
        cases b
        · -- 5 beta false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 5 beta true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- boundary
        cases b
        · -- 5 boundary false → 101 s L
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 5 boundary true → 101 s L
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide

    · -- q = 8
      subst q
      rcases s with ⟨k, b⟩
      cases k
      · -- data0
        cases b
        · -- 8 data0 false → 8 s L
          have hr' : r ∈ ({SymTransResult.mk 8 (Sym.mk SymKind.data0 false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 8 (Sym.mk SymKind.data0 false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 8 data0 true → 8 s L
          have hr' : r ∈ ({SymTransResult.mk 8 (Sym.mk SymKind.data0 true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 8 (Sym.mk SymKind.data0 true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- data1
        cases b
        · -- 8 data1 false → 8 s L
          have hr' : r ∈ ({SymTransResult.mk 8 (Sym.mk SymKind.data1 false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 8 (Sym.mk SymKind.data1 false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 8 data1 true → 8 s L
          have hr' : r ∈ ({SymTransResult.mk 8 (Sym.mk SymKind.data1 true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 8 (Sym.mk SymKind.data1 true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- consumed
        cases b
        · -- 8 consumed false → 8 s L
          have hr' : r ∈ ({SymTransResult.mk 8 (Sym.mk SymKind.consumed false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 8 (Sym.mk SymKind.consumed false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 8 consumed true → 8 s L
          have hr' : r ∈ ({SymTransResult.mk 8 (Sym.mk SymKind.consumed true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 8 (Sym.mk SymKind.consumed true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- alpha
        cases b
        · -- 8 alpha false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 8 alpha true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- sel
        cases b
        · -- 8 sel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 8 sel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- nosel
        cases b
        · -- 8 nosel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 8 nosel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- beta
        cases b
        · -- 8 beta false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 8 beta true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- boundary
        cases b
        · -- 8 boundary false → 9 s L
          have hr' : r ∈ ({SymTransResult.mk 9 (Sym.mk SymKind.boundary false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 9 (Sym.mk SymKind.boundary false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 8 boundary true → 9 s L
          have hr' : r ∈ ({SymTransResult.mk 9 (Sym.mk SymKind.boundary true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 9 (Sym.mk SymKind.boundary true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide

    · -- q = 9
      subst q
      rcases s with ⟨k, b⟩
      cases k
      · -- data0
        cases b
        · -- 9 data0 false → 9 s L
          have hr' : r ∈ ({SymTransResult.mk 9 (Sym.mk SymKind.data0 false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 9 (Sym.mk SymKind.data0 false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 9 data0 true → 9 s L
          have hr' : r ∈ ({SymTransResult.mk 9 (Sym.mk SymKind.data0 true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 9 (Sym.mk SymKind.data0 true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- data1
        cases b
        · -- 9 data1 false → 9 s L
          have hr' : r ∈ ({SymTransResult.mk 9 (Sym.mk SymKind.data1 false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 9 (Sym.mk SymKind.data1 false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 9 data1 true → 9 s L
          have hr' : r ∈ ({SymTransResult.mk 9 (Sym.mk SymKind.data1 true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 9 (Sym.mk SymKind.data1 true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- consumed
        cases b
        · -- 9 consumed false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 9 consumed true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- alpha
        cases b
        · -- 9 alpha false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 9 alpha true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- sel
        cases b
        · -- 9 sel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 9 sel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- nosel
        cases b
        · -- 9 nosel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 9 nosel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- beta
        cases b
        · -- 9 beta false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 9 beta true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- boundary
        cases b
        · -- 9 boundary false → 12 s R
          have hr' : r ∈ ({SymTransResult.mk 12 (Sym.mk SymKind.boundary false) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 12 (Sym.mk SymKind.boundary false) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 9 boundary true → 12 s R
          have hr' : r ∈ ({SymTransResult.mk 12 (Sym.mk SymKind.boundary true) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 12 (Sym.mk SymKind.boundary true) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide

    · -- q = 10
      subst q
      rcases s with ⟨k, b⟩
      cases k
      · -- data0
        cases b
        · -- 10 data0 false → 11 (Sym.data0 true) S
          have hr' : r ∈ ({SymTransResult.mk 11 (Sym.data0 true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 11 (Sym.data0 true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 10 data0 true → 10 (Sym.data0 true) R
          have hr' : r ∈ ({SymTransResult.mk 10 (Sym.data0 true) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 10 (Sym.data0 true) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- data1
        cases b
        · -- 10 data1 false → 11 (Sym.data1 true) S
          have hr' : r ∈ ({SymTransResult.mk 11 (Sym.data1 true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 11 (Sym.data1 true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 10 data1 true → 10 (Sym.data1 true) R
          have hr' : r ∈ ({SymTransResult.mk 10 (Sym.data1 true) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 10 (Sym.data1 true) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- consumed
        cases b
        · -- 10 consumed false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 10 consumed true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- alpha
        cases b
        · -- 10 alpha false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 10 alpha true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- sel
        cases b
        · -- 10 sel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 10 sel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- nosel
        cases b
        · -- 10 nosel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 10 nosel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- beta
        cases b
        · -- 10 beta false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 10 beta true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- boundary
        cases b
        · -- 10 boundary false → 101 s L
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 10 boundary true → 101 s L
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide

    · -- q = 11
      subst q
      rcases s with ⟨k, b⟩
      cases k
      · -- data0
        cases b
        · -- 11 data0 false → 14 (Sym.data1 m) R
          have hr' : r ∈ ({SymTransResult.mk 14 (Sym.data1 false) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 14 (Sym.data1 false) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 11 data0 true → 14 (Sym.data1 m) R
          have hr' : r ∈ ({SymTransResult.mk 14 (Sym.data1 true) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 14 (Sym.data1 true) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- data1
        cases b
        · -- 11 data1 false → 81 (Sym.data0 m) R
          have hr' : r ∈ ({SymTransResult.mk 81 (Sym.data0 false) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 81 (Sym.data0 false) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 11 data1 true → 81 (Sym.data0 m) R
          have hr' : r ∈ ({SymTransResult.mk 81 (Sym.data0 true) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 81 (Sym.data0 true) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- consumed
        cases b
        · -- 11 consumed false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 11 consumed true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- alpha
        cases b
        · -- 11 alpha false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 11 alpha true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- sel
        cases b
        · -- 11 sel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 11 sel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- nosel
        cases b
        · -- 11 nosel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 11 nosel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- beta
        cases b
        · -- 11 beta false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 11 beta true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- boundary
        cases b
        · -- 11 boundary false → 101 s R
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary false) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary false) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 11 boundary true → 101 s R
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary true) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary true) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide

    · -- q = 12
      subst q
      rcases s with ⟨k, b⟩
      cases k
      · -- data0
        cases b
        · -- 12 data0 false → 81 (Sym.data0 true) R
          have hr' : r ∈ ({SymTransResult.mk 81 (Sym.data0 true) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 81 (Sym.data0 true) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 12 data0 true → 12 (Sym.data0 true) R
          have hr' : r ∈ ({SymTransResult.mk 12 (Sym.data0 true) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 12 (Sym.data0 true) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- data1
        cases b
        · -- 12 data1 false → 81 (Sym.data1 true) R
          have hr' : r ∈ ({SymTransResult.mk 81 (Sym.data1 true) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 81 (Sym.data1 true) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 12 data1 true → 12 (Sym.data1 true) R
          have hr' : r ∈ ({SymTransResult.mk 12 (Sym.data1 true) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 12 (Sym.data1 true) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- consumed
        cases b
        · -- 12 consumed false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 12 consumed true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- alpha
        cases b
        · -- 12 alpha false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 12 alpha true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- sel
        cases b
        · -- 12 sel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 12 sel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- nosel
        cases b
        · -- 12 nosel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 12 nosel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- beta
        cases b
        · -- 12 beta false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 12 beta true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- boundary
        cases b
        · -- 12 boundary false → 101 s R
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary false) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary false) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 12 boundary true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide

    · -- q = 13
      subst q
      rcases s with ⟨k, b⟩
      cases k
      · -- data0
        cases b
        · -- 13 data0 false → 5 s S
          have hr' : r ∈ ({SymTransResult.mk 5 (Sym.mk SymKind.data0 false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 5 (Sym.mk SymKind.data0 false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 13 data0 true → 5 s S
          have hr' : r ∈ ({SymTransResult.mk 5 (Sym.mk SymKind.data0 true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 5 (Sym.mk SymKind.data0 true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- data1
        cases b
        · -- 13 data1 false → 5 s S
          have hr' : r ∈ ({SymTransResult.mk 5 (Sym.mk SymKind.data1 false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 5 (Sym.mk SymKind.data1 false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 13 data1 true → 5 s S
          have hr' : r ∈ ({SymTransResult.mk 5 (Sym.mk SymKind.data1 true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 5 (Sym.mk SymKind.data1 true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- consumed
        cases b
        · -- 13 consumed false → 13 (Sym.consumed) R
          have hr' : r ∈ ({SymTransResult.mk 13 (Sym.consumed) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 13 (Sym.consumed) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 13 consumed true → 13 (Sym.consumed) R
          have hr' : r ∈ ({SymTransResult.mk 13 (Sym.consumed) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 13 (Sym.consumed) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- alpha
        cases b
        · -- 13 alpha false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 13 alpha true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- sel
        cases b
        · -- 13 sel false → 84 s L
          have hr' : r ∈ ({SymTransResult.mk 84 (Sym.mk SymKind.sel false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 84 (Sym.mk SymKind.sel false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 13 sel true → 84 s L
          have hr' : r ∈ ({SymTransResult.mk 84 (Sym.mk SymKind.sel true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 84 (Sym.mk SymKind.sel true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- nosel
        cases b
        · -- 13 nosel false → 84 s L
          have hr' : r ∈ ({SymTransResult.mk 84 (Sym.mk SymKind.nosel false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 84 (Sym.mk SymKind.nosel false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 13 nosel true → 84 s L
          have hr' : r ∈ ({SymTransResult.mk 84 (Sym.mk SymKind.nosel true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 84 (Sym.mk SymKind.nosel true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- beta
        cases b
        · -- 13 beta false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 13 beta true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- boundary
        cases b
        · -- 13 boundary false → 84 s L
          have hr' : r ∈ ({SymTransResult.mk 84 (Sym.mk SymKind.boundary false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 84 (Sym.mk SymKind.boundary false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 13 boundary true → 84 s L
          have hr' : r ∈ ({SymTransResult.mk 84 (Sym.mk SymKind.boundary true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 84 (Sym.mk SymKind.boundary true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide

    · -- q = 14
      subst q
      rcases s with ⟨k, b⟩
      cases k
      · -- data0
        cases b
        · -- 14 data0 false → 14 (Sym.data1 m) R
          have hr' : r ∈ ({SymTransResult.mk 14 (Sym.data1 false) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 14 (Sym.data1 false) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 14 data0 true → 14 (Sym.data1 m) R
          have hr' : r ∈ ({SymTransResult.mk 14 (Sym.data1 true) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 14 (Sym.data1 true) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- data1
        cases b
        · -- 14 data1 false → 81 (Sym.data0 m) R
          have hr' : r ∈ ({SymTransResult.mk 81 (Sym.data0 false) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 81 (Sym.data0 false) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 14 data1 true → 81 (Sym.data0 m) R
          have hr' : r ∈ ({SymTransResult.mk 81 (Sym.data0 true) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 81 (Sym.data0 true) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- consumed
        cases b
        · -- 14 consumed false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 14 consumed true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- alpha
        cases b
        · -- 14 alpha false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 14 alpha true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- sel
        cases b
        · -- 14 sel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 14 sel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- nosel
        cases b
        · -- 14 nosel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 14 nosel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- beta
        cases b
        · -- 14 beta false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 14 beta true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- boundary
        cases b
        · -- 14 boundary false → 101 s R
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary false) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary false) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 14 boundary true → 101 s R
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary true) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary true) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide

    · -- q = 20
      subst q
      rcases s with ⟨k, b⟩
      cases k
      · -- data0
        cases b
        · -- 20 data0 false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data0 false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data0 false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 20 data0 true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data0 true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data0 true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- data1
        cases b
        · -- 20 data1 false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data1 false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data1 false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 20 data1 true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data1 true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data1 true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- consumed
        cases b
        · -- 20 consumed false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 20 consumed true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- alpha
        cases b
        · -- 20 alpha false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 20 alpha true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- sel
        cases b
        · -- 20 sel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 20 sel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- nosel
        cases b
        · -- 20 nosel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 20 nosel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- beta
        cases b
        · -- 20 beta false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 20 beta true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- boundary
        cases b
        · -- 20 boundary false → 21 (Sym.data0) R
          have hr' : r ∈ ({SymTransResult.mk 21 (Sym.data0) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 21 (Sym.data0) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 20 boundary true → 21 (Sym.data0) R
          have hr' : r ∈ ({SymTransResult.mk 21 (Sym.data0) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 21 (Sym.data0) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide

    · -- q = 21
      subst q
      rcases s with ⟨k, b⟩
      cases k
      · -- data0
        cases b
        · -- 21 data0 false → 21 (Sym.data0) R
          have hr' : r ∈ ({SymTransResult.mk 21 (Sym.data0) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 21 (Sym.data0) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 21 data0 true → 21 (Sym.data0) R
          have hr' : r ∈ ({SymTransResult.mk 21 (Sym.data0) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 21 (Sym.data0) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- data1
        cases b
        · -- 21 data1 false → 21 (Sym.data0) R
          have hr' : r ∈ ({SymTransResult.mk 21 (Sym.data0) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 21 (Sym.data0) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 21 data1 true → 21 (Sym.data0) R
          have hr' : r ∈ ({SymTransResult.mk 21 (Sym.data0) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 21 (Sym.data0) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- consumed
        cases b
        · -- 21 consumed false → 21 (Sym.data0) R
          have hr' : r ∈ ({SymTransResult.mk 21 (Sym.data0) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 21 (Sym.data0) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 21 consumed true → 21 (Sym.data0) R
          have hr' : r ∈ ({SymTransResult.mk 21 (Sym.data0) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 21 (Sym.data0) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- alpha
        cases b
        · -- 21 alpha false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 21 alpha true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- sel
        cases b
        · -- 21 sel false → 51 s L
          have hr' : r ∈ ({SymTransResult.mk 51 (Sym.mk SymKind.sel false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 51 (Sym.mk SymKind.sel false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 21 sel true → 51 s L
          have hr' : r ∈ ({SymTransResult.mk 51 (Sym.mk SymKind.sel true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 51 (Sym.mk SymKind.sel true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- nosel
        cases b
        · -- 21 nosel false → 51 s L
          have hr' : r ∈ ({SymTransResult.mk 51 (Sym.mk SymKind.nosel false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 51 (Sym.mk SymKind.nosel false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 21 nosel true → 51 s L
          have hr' : r ∈ ({SymTransResult.mk 51 (Sym.mk SymKind.nosel true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 51 (Sym.mk SymKind.nosel true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- beta
        cases b
        · -- 21 beta false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 21 beta true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- boundary
        cases b
        · -- 21 boundary false → 22 s S
          have hr' : r ∈ ({SymTransResult.mk 22 (Sym.mk SymKind.boundary false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 22 (Sym.mk SymKind.boundary false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 21 boundary true → 22 s S
          have hr' : r ∈ ({SymTransResult.mk 22 (Sym.mk SymKind.boundary true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 22 (Sym.mk SymKind.boundary true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide

    · -- q = 22
      subst q
      rcases s with ⟨k, b⟩
      cases k
      · -- data0
        cases b
        · -- 22 data0 false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data0 false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data0 false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 22 data0 true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data0 true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data0 true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- data1
        cases b
        · -- 22 data1 false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data1 false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data1 false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 22 data1 true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data1 true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data1 true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- consumed
        cases b
        · -- 22 consumed false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 22 consumed true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- alpha
        cases b
        · -- 22 alpha false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 22 alpha true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- sel
        cases b
        · -- 22 sel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 22 sel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- nosel
        cases b
        · -- 22 nosel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 22 nosel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- beta
        cases b
        · -- 22 beta false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 22 beta true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- boundary
        cases b
        · -- 22 boundary false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 22 boundary true → 23 s L
          have hr' : r ∈ ({SymTransResult.mk 23 (Sym.mk SymKind.boundary true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 23 (Sym.mk SymKind.boundary true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide

    · -- q = 76
      subst q
      rcases s with ⟨k, b⟩
      cases k
      · -- data0
        cases b
        · -- 76 data0 false → 76 s L
          have hr' : r ∈ ({SymTransResult.mk 76 (Sym.mk SymKind.data0 false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 76 (Sym.mk SymKind.data0 false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 76 data0 true → 76 s L
          have hr' : r ∈ ({SymTransResult.mk 76 (Sym.mk SymKind.data0 true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 76 (Sym.mk SymKind.data0 true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- data1
        cases b
        · -- 76 data1 false → 76 s L
          have hr' : r ∈ ({SymTransResult.mk 76 (Sym.mk SymKind.data1 false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 76 (Sym.mk SymKind.data1 false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 76 data1 true → 76 s L
          have hr' : r ∈ ({SymTransResult.mk 76 (Sym.mk SymKind.data1 true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 76 (Sym.mk SymKind.data1 true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- consumed
        cases b
        · -- 76 consumed false → 76 s L
          have hr' : r ∈ ({SymTransResult.mk 76 (Sym.mk SymKind.consumed false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 76 (Sym.mk SymKind.consumed false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 76 consumed true → 76 s L
          have hr' : r ∈ ({SymTransResult.mk 76 (Sym.mk SymKind.consumed true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 76 (Sym.mk SymKind.consumed true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- alpha
        cases b
        · -- 76 alpha false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 76 alpha true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- sel
        cases b
        · -- 76 sel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 76 sel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- nosel
        cases b
        · -- 76 nosel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 76 nosel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- beta
        cases b
        · -- 76 beta false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 76 beta true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- boundary
        cases b
        · -- 76 boundary false → 77 s L
          have hr' : r ∈ ({SymTransResult.mk 77 (Sym.mk SymKind.boundary false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 77 (Sym.mk SymKind.boundary false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 76 boundary true → 77 s L
          have hr' : r ∈ ({SymTransResult.mk 77 (Sym.mk SymKind.boundary true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 77 (Sym.mk SymKind.boundary true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide

    · -- q = 77
      subst q
      rcases s with ⟨k, b⟩
      cases k
      · -- data0
        cases b
        · -- 77 data0 false → 77 s L
          have hr' : r ∈ ({SymTransResult.mk 77 (Sym.mk SymKind.data0 false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 77 (Sym.mk SymKind.data0 false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 77 data0 true → 77 s L
          have hr' : r ∈ ({SymTransResult.mk 77 (Sym.mk SymKind.data0 true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 77 (Sym.mk SymKind.data0 true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- data1
        cases b
        · -- 77 data1 false → 77 s L
          have hr' : r ∈ ({SymTransResult.mk 77 (Sym.mk SymKind.data1 false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 77 (Sym.mk SymKind.data1 false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 77 data1 true → 77 s L
          have hr' : r ∈ ({SymTransResult.mk 77 (Sym.mk SymKind.data1 true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 77 (Sym.mk SymKind.data1 true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- consumed
        cases b
        · -- 77 consumed false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 77 consumed true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- alpha
        cases b
        · -- 77 alpha false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 77 alpha true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- sel
        cases b
        · -- 77 sel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 77 sel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- nosel
        cases b
        · -- 77 nosel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 77 nosel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- beta
        cases b
        · -- 77 beta false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 77 beta true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- boundary
        cases b
        · -- 77 boundary false → 10 s R
          have hr' : r ∈ ({SymTransResult.mk 10 (Sym.mk SymKind.boundary false) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 10 (Sym.mk SymKind.boundary false) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 77 boundary true → 10 s R
          have hr' : r ∈ ({SymTransResult.mk 10 (Sym.mk SymKind.boundary true) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 10 (Sym.mk SymKind.boundary true) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide

    · -- q = 81
      subst q
      rcases s with ⟨k, b⟩
      cases k
      · -- data0
        cases b
        · -- 81 data0 false → 81 s R
          have hr' : r ∈ ({SymTransResult.mk 81 (Sym.mk SymKind.data0 false) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 81 (Sym.mk SymKind.data0 false) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 81 data0 true → 81 s R
          have hr' : r ∈ ({SymTransResult.mk 81 (Sym.mk SymKind.data0 true) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 81 (Sym.mk SymKind.data0 true) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- data1
        cases b
        · -- 81 data1 false → 81 s R
          have hr' : r ∈ ({SymTransResult.mk 81 (Sym.mk SymKind.data1 false) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 81 (Sym.mk SymKind.data1 false) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 81 data1 true → 81 s R
          have hr' : r ∈ ({SymTransResult.mk 81 (Sym.mk SymKind.data1 true) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 81 (Sym.mk SymKind.data1 true) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- consumed
        cases b
        · -- 81 consumed false → 13 (Sym.consumed) R
          have hr' : r ∈ ({SymTransResult.mk 13 (Sym.consumed) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 13 (Sym.consumed) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 81 consumed true → 13 (Sym.consumed) R
          have hr' : r ∈ ({SymTransResult.mk 13 (Sym.consumed) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 13 (Sym.consumed) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- alpha
        cases b
        · -- 81 alpha false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 81 alpha true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- sel
        cases b
        · -- 81 sel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 81 sel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- nosel
        cases b
        · -- 81 nosel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 81 nosel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- beta
        cases b
        · -- 81 beta false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 81 beta true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- boundary
        cases b
        · -- 81 boundary false → 81 s R
          have hr' : r ∈ ({SymTransResult.mk 81 (Sym.mk SymKind.boundary false) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 81 (Sym.mk SymKind.boundary false) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 81 boundary true → 81 s R
          have hr' : r ∈ ({SymTransResult.mk 81 (Sym.mk SymKind.boundary true) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 81 (Sym.mk SymKind.boundary true) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide

    · -- q = 84
      subst q
      rcases s with ⟨k, b⟩
      cases k
      · -- data0
        cases b
        · -- 84 data0 false → 84 s L
          have hr' : r ∈ ({SymTransResult.mk 84 (Sym.mk SymKind.data0 false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 84 (Sym.mk SymKind.data0 false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 84 data0 true → 84 s L
          have hr' : r ∈ ({SymTransResult.mk 84 (Sym.mk SymKind.data0 true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 84 (Sym.mk SymKind.data0 true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- data1
        cases b
        · -- 84 data1 false → 84 s L
          have hr' : r ∈ ({SymTransResult.mk 84 (Sym.mk SymKind.data1 false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 84 (Sym.mk SymKind.data1 false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 84 data1 true → 84 s L
          have hr' : r ∈ ({SymTransResult.mk 84 (Sym.mk SymKind.data1 true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 84 (Sym.mk SymKind.data1 true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- consumed
        cases b
        · -- 84 consumed false → 84 s L
          have hr' : r ∈ ({SymTransResult.mk 84 (Sym.mk SymKind.consumed false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 84 (Sym.mk SymKind.consumed false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 84 consumed true → 84 s L
          have hr' : r ∈ ({SymTransResult.mk 84 (Sym.mk SymKind.consumed true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 84 (Sym.mk SymKind.consumed true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- alpha
        cases b
        · -- 84 alpha false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 84 alpha true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- sel
        cases b
        · -- 84 sel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 84 sel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- nosel
        cases b
        · -- 84 nosel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 84 nosel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- beta
        cases b
        · -- 84 beta false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 84 beta true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- boundary
        cases b
        · -- 84 boundary false → 85 s L
          have hr' : r ∈ ({SymTransResult.mk 85 (Sym.mk SymKind.boundary false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 85 (Sym.mk SymKind.boundary false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 84 boundary true → 85 s L
          have hr' : r ∈ ({SymTransResult.mk 85 (Sym.mk SymKind.boundary true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 85 (Sym.mk SymKind.boundary true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide

    · -- q = 85
      subst q
      rcases s with ⟨k, b⟩
      cases k
      · -- data0
        cases b
        · -- 85 data0 false → 85 s L
          have hr' : r ∈ ({SymTransResult.mk 85 (Sym.mk SymKind.data0 false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 85 (Sym.mk SymKind.data0 false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 85 data0 true → 85 s L
          have hr' : r ∈ ({SymTransResult.mk 85 (Sym.mk SymKind.data0 true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 85 (Sym.mk SymKind.data0 true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- data1
        cases b
        · -- 85 data1 false → 85 s L
          have hr' : r ∈ ({SymTransResult.mk 85 (Sym.mk SymKind.data1 false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 85 (Sym.mk SymKind.data1 false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 85 data1 true → 85 s L
          have hr' : r ∈ ({SymTransResult.mk 85 (Sym.mk SymKind.data1 true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 85 (Sym.mk SymKind.data1 true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- consumed
        cases b
        · -- 85 consumed false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 85 consumed true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- alpha
        cases b
        · -- 85 alpha false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 85 alpha true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- sel
        cases b
        · -- 85 sel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 85 sel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- nosel
        cases b
        · -- 85 nosel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 85 nosel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- beta
        cases b
        · -- 85 beta false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 85 beta true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- boundary
        cases b
        · -- 85 boundary false → 86 s R
          have hr' : r ∈ ({SymTransResult.mk 86 (Sym.mk SymKind.boundary false) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 86 (Sym.mk SymKind.boundary false) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 85 boundary true → 86 s R
          have hr' : r ∈ ({SymTransResult.mk 86 (Sym.mk SymKind.boundary true) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 86 (Sym.mk SymKind.boundary true) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide

    · -- q = 86
      subst q
      rcases s with ⟨k, b⟩
      cases k
      · -- data0
        cases b
        · -- 86 data0 false → 87 s S
          have hr' : r ∈ ({SymTransResult.mk 87 (Sym.mk SymKind.data0 false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 87 (Sym.mk SymKind.data0 false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 86 data0 true → 86 (Sym.mk SymKind.data0 false) R
          have hr' : r ∈ ({SymTransResult.mk 86 (Sym.mk SymKind.data0 false) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 86 (Sym.mk SymKind.data0 false) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- data1
        cases b
        · -- 86 data1 false → 87 s S
          have hr' : r ∈ ({SymTransResult.mk 87 (Sym.mk SymKind.data1 false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 87 (Sym.mk SymKind.data1 false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 86 data1 true → 86 (Sym.mk SymKind.data1 false) R
          have hr' : r ∈ ({SymTransResult.mk 86 (Sym.mk SymKind.data1 false) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 86 (Sym.mk SymKind.data1 false) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- consumed
        cases b
        · -- 86 consumed false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 86 consumed true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- alpha
        cases b
        · -- 86 alpha false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 86 alpha true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- sel
        cases b
        · -- 86 sel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 86 sel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- nosel
        cases b
        · -- 86 nosel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 86 nosel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- beta
        cases b
        · -- 86 beta false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 86 beta true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- boundary
        cases b
        · -- 86 boundary false → 87 s S
          have hr' : r ∈ ({SymTransResult.mk 87 (Sym.mk SymKind.boundary false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 87 (Sym.mk SymKind.boundary false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 86 boundary true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide

    · -- q = 87
      subst q
      rcases s with ⟨k, b⟩
      cases k
      · -- data0
        cases b
        · -- 87 data0 false → 87 s R
          have hr' : r ∈ ({SymTransResult.mk 87 (Sym.mk SymKind.data0 false) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 87 (Sym.mk SymKind.data0 false) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 87 data0 true → 87 s R
          have hr' : r ∈ ({SymTransResult.mk 87 (Sym.mk SymKind.data0 true) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 87 (Sym.mk SymKind.data0 true) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- data1
        cases b
        · -- 87 data1 false → 87 s R
          have hr' : r ∈ ({SymTransResult.mk 87 (Sym.mk SymKind.data1 false) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 87 (Sym.mk SymKind.data1 false) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 87 data1 true → 87 s R
          have hr' : r ∈ ({SymTransResult.mk 87 (Sym.mk SymKind.data1 true) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 87 (Sym.mk SymKind.data1 true) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- consumed
        cases b
        · -- 87 consumed false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 87 consumed true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- alpha
        cases b
        · -- 87 alpha false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 87 alpha true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- sel
        cases b
        · -- 87 sel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 87 sel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- nosel
        cases b
        · -- 87 nosel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 87 nosel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- beta
        cases b
        · -- 87 beta false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 87 beta true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- boundary
        cases b
        · -- 87 boundary false → 20 s S
          have hr' : r ∈ ({SymTransResult.mk 20 (Sym.mk SymKind.boundary false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 20 (Sym.mk SymKind.boundary false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 87 boundary true → 20 s S
          have hr' : r ∈ ({SymTransResult.mk 20 (Sym.mk SymKind.boundary true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 20 (Sym.mk SymKind.boundary true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide

    · -- q = 38
      subst q
      rcases s with ⟨k, b⟩
      cases k
      · -- data0
        cases b
        · -- 38 data0 false → 38 s L
          have hr' : r ∈ ({SymTransResult.mk 38 (Sym.mk SymKind.data0 false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 38 (Sym.mk SymKind.data0 false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 38 data0 true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data0 true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data0 true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- data1
        cases b
        · -- 38 data1 false → 38 s L
          have hr' : r ∈ ({SymTransResult.mk 38 (Sym.mk SymKind.data1 false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 38 (Sym.mk SymKind.data1 false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 38 data1 true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data1 true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data1 true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- consumed
        cases b
        · -- 38 consumed false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 38 consumed true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- alpha
        cases b
        · -- 38 alpha false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 38 alpha true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- sel
        cases b
        · -- 38 sel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 38 sel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- nosel
        cases b
        · -- 38 nosel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 38 nosel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- beta
        cases b
        · -- 38 beta false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 38 beta true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- boundary
        cases b
        · -- 38 boundary false → 28 s R
          have hr' : r ∈ ({SymTransResult.mk 28 (Sym.mk SymKind.boundary false) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 28 (Sym.mk SymKind.boundary false) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 38 boundary true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide

    · -- q = 51
      subst q
      rcases s with ⟨k, b⟩
      cases k
      · -- data0
        cases b
        · -- 51 data0 false → 4 (Sym.boundary) R
          have hr' : r ∈ ({SymTransResult.mk 4 (Sym.boundary) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 4 (Sym.boundary) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 51 data0 true → 4 (Sym.boundary) R
          have hr' : r ∈ ({SymTransResult.mk 4 (Sym.boundary) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 4 (Sym.boundary) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- data1
        cases b
        · -- 51 data1 false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data1 false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data1 false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 51 data1 true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data1 true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data1 true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- consumed
        cases b
        · -- 51 consumed false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 51 consumed true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- alpha
        cases b
        · -- 51 alpha false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 51 alpha true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- sel
        cases b
        · -- 51 sel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 51 sel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- nosel
        cases b
        · -- 51 nosel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 51 nosel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- beta
        cases b
        · -- 51 beta false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 51 beta true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- boundary
        cases b
        · -- 51 boundary false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 51 boundary true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.boundary true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide

    · -- q = 23
      subst q
      rcases s with ⟨k, b⟩
      cases k
      · -- data0
        cases b
        · -- 23 data0 false → 23 s L
          have hr' : r ∈ ({SymTransResult.mk 23 (Sym.mk SymKind.data0 false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 23 (Sym.mk SymKind.data0 false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 23 data0 true → 23 s L
          have hr' : r ∈ ({SymTransResult.mk 23 (Sym.mk SymKind.data0 true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 23 (Sym.mk SymKind.data0 true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- data1
        cases b
        · -- 23 data1 false → 101 s L
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data1 false) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data1 false) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 23 data1 true → 101 s L
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data1 true) Dir.L} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.data1 true) Dir.L} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- consumed
        cases b
        · -- 23 consumed false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 23 consumed true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.consumed true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- alpha
        cases b
        · -- 23 alpha false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 23 alpha true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.alpha true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- sel
        cases b
        · -- 23 sel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 23 sel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.sel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- nosel
        cases b
        · -- 23 nosel false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 23 nosel true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.nosel true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- beta
        cases b
        · -- 23 beta false → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta false) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 23 beta true → 101 s S
          have hr' : r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 101 (Sym.mk SymKind.beta true) Dir.S} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
      · -- boundary
        cases b
        · -- 23 boundary false → 100 s R
          have hr' : r ∈ ({SymTransResult.mk 100 (Sym.mk SymKind.boundary false) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 100 (Sym.mk SymKind.boundary false) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
        · -- 23 boundary true → 100 s R
          have hr' : r ∈ ({SymTransResult.mk 100 (Sym.mk SymKind.boundary true) Dir.R} : Finset SymTransResult) := by
            change r ∈ ({SymTransResult.mk 100 (Sym.mk SymKind.boundary true) Dir.R} : Finset SymTransResult)
            exact hr
          simp at hr'
          subst r
          decide
  · exfalso
    have hq_legal' : q ∈ VerifierSym.legalStates := by
      fin_cases hq <;> simp [VerifierSym.legalStates]
    exact hq_legal hq_legal'

lemma steps_from_100 (tape : ℤ → Sym) (p : ℤ) {π cfg} :
    SymSteps VerifierSym.transition (SymConfig.mk 100 tape p) π cfg → cfg.state = 100 := by
  intro h
  induction h with
  | nil => rfl
  | cons π₀ step cfg₁ h_ind h_from h_read h_trans ih =>
      change step.result.nextState = 100
      have hs₀ : cfg₁.state = 100 := ih
      have hmem : step.result ∈ VerifierSym.transition (100, cfg₁.tape cfg₁.headPos) := by
        simpa [hs₀] using h_trans
      cases hsym : cfg₁.tape cfg₁.headPos with
      | mk k mk' =>
          rw [hsym] at hmem
          have hres : step.result = SymTransResult.mk 100 (k, mk') Dir.S := by
            rw [VerifierSym.transition, if_pos (by decide : 100 ∈ VerifierSym.legalStates)] at hmem
            simp at hmem
            exact hmem
          rw [hres]

/-- 状态 101 吸收。 -/
lemma steps_from_101 (tape : ℤ → Sym) (p : ℤ) {π cfg} :
    SymSteps VerifierSym.transition (SymConfig.mk 101 tape p) π cfg → cfg.state = 101 := by
  intro h
  induction h with
  | nil => rfl
  | cons π₀ step cfg₁ h_ind h_from h_read h_trans ih =>
      change step.result.nextState = 101
      have hs₀ : cfg₁.state = 101 := ih
      have hmem : step.result ∈ VerifierSym.transition (101, cfg₁.tape cfg₁.headPos) := by
        simpa [hs₀] using h_trans
      cases hsym : cfg₁.tape cfg₁.headPos with
      | mk k mk' =>
          rw [hsym] at hmem
          have hres : step.result = SymTransResult.mk 101 (k, mk') Dir.S := by
            rw [VerifierSym.transition, if_pos (by decide : 101 ∈ VerifierSym.legalStates)] at hmem
            simp at hmem
            exact hmem
          rw [hres]

/-- 2^j > bitsValue bits → bits 的第 j 位起全为 false。 -/
lemma drop_all_false_of_lt_pow (bits : List Bool) (j : ℕ) (h : bitsValue bits < 2 ^ j) :
    ∀ b ∈ bits.drop j, b = false := by
  have hv : bitsValue (bits.drop j) = 0 := by
    by_contra hz
    have hge1 : 1 ≤ bitsValue (bits.drop j) := by omega
    have hle := bitsValue_drop_le bits j
    have hle2 : 2 ^ j ≤ 2 ^ j * bitsValue (bits.drop j) := by
      have hmul := Nat.mul_le_mul_left (2 ^ j) hge1
      simpa using hmul
    omega
  exact (bitsValue_eq_zero_iff_all_false (bits.drop j)).mp hv

end Mp
