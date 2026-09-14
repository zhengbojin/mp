-- ============================================================================
-- 模块 3:主循环态头域联合归纳(左右边界符之间,负区准备)
--   自含:辅助引理 + 表级件 + 主定理(a2p_EProp 顶层 17 个合取分量)
-- ============================================================================
import Mp.SubsetSumVerifierPosBound3

set_option maxHeartbeats 20000000
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

namespace Mp

/-- 可达路径终态 ≠ 101:路径内无 101 步。 -/
lemma a2p_reach_no_101 {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg) (hs : cfg.state ≠ 101) :
    ∀ step ∈ π, step.result.nextState ≠ 101 := by
  induction h with
  | nil => intro step hs0; simp at hs0
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro step₀ hs0
      simp at hs0
      cases hs0 with
      | inl hmem =>
          have hc₁ : cfg₁.state ≠ 101 := by
            intro h101s
            have hnext : step.result.nextState = 101 := by
              have ht : step.result ∈ VerifierSym.transition (101, step.readSym) := by
                rw [h101s] at htrans
                rw [← hread] at htrans
                exact htrans
              exact state101_absorb step.readSym step.result ht
            change step.result.nextState ≠ 101 at hs
            exact hs hnext
          exact ih hc₁ step₀ hmem
      | inr hst =>
          cases hst
          change step.result.nextState ≠ 101 at hs
          exact hs

/-- 表级:写 sel/nosel ⟸ 读 sel/nosel ∨ 读 α(源 = 2)。 -/
lemma a2p_write_sel_class (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s))
    (hw : r.writeSym.1 = SymKind.sel ∨ r.writeSym.1 = SymKind.nosel) :
    (s.1 = SymKind.sel ∨ s.1 = SymKind.nosel) ∨
      (s.1 = SymKind.alpha ∧ (q : ℕ) = 2) := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) →
      (r.writeSym.1 = SymKind.sel ∨ r.writeSym.1 = SymKind.nosel) →
        (s.1 = SymKind.sel ∨ s.1 = SymKind.nosel) ∨
          (s.1 = SymKind.alpha ∧ (q : ℕ) = 2) := by
    native_decide
  exact hbb q s r hr hw

/-- A3 任意路径版:sel/nosel 格位 ≥ n+2。 -/
lemma a2p_sel_ge_n2_all (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (ht : 0 < inst.target) (gS : List Sym)
    {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π cfg)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101) :
    ∀ j : ℤ,
      (cfg.tape j).1 = SymKind.sel ∨ (cfg.tape j).1 = SymKind.nosel →
        (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ j := by
  induction h with
  | nil =>
      intro j hj
      by_contra hlt
      have hjl : j < (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) := by omega
      have hj0 : 0 ≤ j := by
        by_contra hneg
        have hjneg : j < 0 := by omega
        have hcell : (symInitialConfig (encodeInstanceSym inst ++ gS)).tape j = Sym.blank := by
          simp [symInitialConfig, hjneg]
        rw [hcell] at hj
        rcases hj with hjs | hjn
        · cases hjs <;> simp [Sym.blank]
        · cases hjn <;> simp [Sym.blank]
      have hto : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj0
      have htn : j.toNat < (encodeBitsSym inst.target).length + 2 := by
        apply Int.ofNat_lt.mp
        rw [hto]
        exact hjl
      have hlen2 : (encodeBitsSym inst.target).length + 2 ≤
          (encodeInstanceSym inst ++ gS).length := by
        rw [List.length_append, r7_enc_len]
        omega
      have hc : (symInitialConfig (encodeInstanceSym inst ++ gS)).tape j =
          (encodeInstanceSym inst ++ gS).getD j.toNat Sym.blank :=
        a2p_tape_at_getD (encodeInstanceSym inst ++ gS) hj0 (lt_of_lt_of_le htn hlen2)
      have hkind : ((encodeInstanceSym inst ++ gS).getD j.toNat Sym.blank).1 =
            SymKind.boundary ∨
          ((encodeInstanceSym inst ++ gS).getD j.toNat Sym.blank).1 = SymKind.data0 ∨
          ((encodeInstanceSym inst ++ gS).getD j.toNat Sym.blank).1 = SymKind.data1 := by
        by_cases hz : j.toNat = 0
        · left
          have hb := a2p_pos0_boundary inst gS
          rw [hz, hb]
          rfl
        · have hzt : 1 ≤ j.toNat := by omega
          by_cases hmid : j.toNat = (encodeBitsSym inst.target).length + 1
          · left
            have hb := a2p_pos_mid_boundary inst gS
            rw [hmid, hb]
            rfl
          · right
            have hbn : j.toNat ≤ (encodeBitsSym inst.target).length := by omega
            have harg : j.toNat = 1 + (j.toNat - 1) := by omega
            rw [harg]
            exact a2p_bits_kind_wS inst gS (by omega)
      rw [hc] at hj
      rcases hkind with hb0 | hdata
      · rw [hb0] at hj
        rcases hj with hjs | hjn
        · cases hjs
        · cases hjn
      · rcases hdata with hd0 | hd1
        · rw [hd0] at hj
          rcases hj with hjs | hjn
          · cases hjs
          · cases hjn
        · rw [hd1] at hj
          rcases hj with hjs | hjn
          · cases hjs
          · cases hjn
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro j hj
      have hno101₀ : ∀ step₀ ∈ π₀, step₀.result.nextState ≠ 101 := by
        intro step₀ hs0
        exact hno101 step₀ (by simp [hs0])
      by_cases hw : cfg₁.headPos = j
      · have hwj : (step.result.writeSym).1 = SymKind.sel ∨
            (step.result.writeSym).1 = SymKind.nosel := by
          dsimp [symStepConfig] at hj
          simpa [hw] using hj
        have hwq := a2p_write_sel_class ⟨cfg₁.state, q12_path_state_lt102
          (encodeInstanceSym inst ++ gS) π₀ cfg₁ hprev⟩ step.readSym step.result
          (by simpa [hread] using htrans) hwj
        rcases hwq with hsame | halpha
        · have hread_sel : (cfg₁.tape j).1 = SymKind.sel ∨ (cfg₁.tape j).1 = SymKind.nosel := by
            rw [← hw]
            rw [← hread]
            exact hsame
          exact ih hno101₀ j hread_sel
        · have hq2 : cfg₁.state = 2 := halpha.2
          have hge := a2p_s2_head inst hm ht gS hprev hno101₀ hq2
          rw [← hw]
          exact hge.1
      · have hj' : (cfg₁.tape j).1 = SymKind.sel ∨ (cfg₁.tape j).1 = SymKind.nosel := by
          dsimp [symStepConfig] at hj
          simpa [if_neg (Ne.symm hw)] using hj
        exact ih hno101₀ j hj'

-- 声明(每态:源 → 本态的 dir;含自环源)
lemma a2p_mainloop_dir (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) :
    (r.nextState = 4 → ((q : ℕ) = 51 ∧ r.moveDir = Dir.R) ∨ ((q : ℕ) = 28 ∧ r.moveDir = Dir.R)) ∧
    (r.nextState = 5 → ((q : ℕ) = 4 ∧ r.moveDir = Dir.R) ∨ ((q : ℕ) = 13 ∧ r.moveDir = Dir.S)) ∧
    ((r.nextState = 76 ∨ r.nextState = 8) → ((q : ℕ) = 5 ∧ r.moveDir = Dir.L) ∨
        ((q : ℕ) = 76 ∧ r.moveDir = Dir.L) ∨ ((q : ℕ) = 8 ∧ r.moveDir = Dir.L)) ∧
    ((r.nextState = 77 ∨ r.nextState = 9) → ((q : ℕ) = 76 ∧ r.moveDir = Dir.L) ∨
        ((q : ℕ) = 8 ∧ r.moveDir = Dir.L) ∨ ((q : ℕ) = 77 ∧ r.moveDir = Dir.L) ∨
        ((q : ℕ) = 9 ∧ r.moveDir = Dir.L)) ∧
    (r.nextState = 10 → ((q : ℕ) = 77 ∧ r.moveDir = Dir.R) ∨ ((q : ℕ) = 10 ∧ r.moveDir = Dir.R)) ∧
    (r.nextState = 12 → ((q : ℕ) = 9 ∧ r.moveDir = Dir.R) ∨ ((q : ℕ) = 12 ∧ r.moveDir = Dir.R)) ∧
    (r.nextState = 11 → (q : ℕ) = 10 ∧ r.moveDir = Dir.S) ∧
    (r.nextState = 14 → ((q : ℕ) = 11 ∧ r.moveDir = Dir.R) ∨ ((q : ℕ) = 14 ∧ r.moveDir = Dir.R)) ∧
    (r.nextState = 81 → ((q : ℕ) = 11 ∨ (q : ℕ) = 12 ∨ (q : ℕ) = 14 ∨ (q : ℕ) = 81) ∧
        r.moveDir = Dir.R) ∧
    (r.nextState = 13 → ((q : ℕ) = 81 ∧ r.moveDir = Dir.R) ∨ ((q : ℕ) = 13 ∧ r.moveDir = Dir.R)) ∧
    (r.nextState = 84 → ((q : ℕ) = 13 ∧ r.moveDir = Dir.L) ∨ ((q : ℕ) = 84 ∧ r.moveDir = Dir.L)) ∧
    (r.nextState = 85 → ((q : ℕ) = 84 ∧ r.moveDir = Dir.L) ∨ ((q : ℕ) = 85 ∧ r.moveDir = Dir.L)) ∧
    (r.nextState = 86 → ((q : ℕ) = 85 ∧ r.moveDir = Dir.R) ∨ ((q : ℕ) = 86 ∧ r.moveDir = Dir.R)) ∧
    (r.nextState = 87 → ((q : ℕ) = 86 ∧ r.moveDir = Dir.S) ∨ ((q : ℕ) = 87 ∧ r.moveDir = Dir.R)) ∧
    (r.nextState = 20 → ((q : ℕ) = 87 ∧ r.moveDir = Dir.S) ∨ ((q : ℕ) = 4 ∧ r.moveDir = Dir.L)) ∧
    (r.nextState = 21 → ((q : ℕ) = 20 ∧ r.moveDir = Dir.R) ∨ ((q : ℕ) = 21 ∧ r.moveDir = Dir.R)) ∧
    (r.nextState = 51 → (q : ℕ) = 21 ∧ r.moveDir = Dir.L) ∧
    (r.nextState = 22 → (q : ℕ) = 21 ∧ r.moveDir = Dir.S) ∧
    (r.nextState = 23 → ((q : ℕ) = 22 ∧ r.moveDir = Dir.L) ∨ ((q : ℕ) = 23 ∧ r.moveDir = Dir.L)) := by

  repeat' constructor
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 4 → (q : ℕ) = 51 ∧ r.moveDir = Dir.R ∨ (q : ℕ) = 28 ∧ r.moveDir = Dir.R := by
      native_decide
    exact hbb q s r hr hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 5 → (q : ℕ) = 4 ∧ r.moveDir = Dir.R ∨ (q : ℕ) = 13 ∧ r.moveDir = Dir.S := by
      native_decide
    exact hbb q s r hr hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 76 ∨ r.nextState = 8 → (q : ℕ) = 5 ∧ r.moveDir = Dir.L ∨ (q : ℕ) = 76 ∧ r.moveDir = Dir.L ∨ (q : ℕ) = 8 ∧ r.moveDir = Dir.L := by
      native_decide
    exact hbb q s r hr hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 77 ∨ r.nextState = 9 → (q : ℕ) = 76 ∧ r.moveDir = Dir.L ∨ (q : ℕ) = 8 ∧ r.moveDir = Dir.L ∨ (q : ℕ) = 77 ∧ r.moveDir = Dir.L ∨ (q : ℕ) = 9 ∧ r.moveDir = Dir.L := by
      native_decide
    exact hbb q s r hr hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 10 → (q : ℕ) = 77 ∧ r.moveDir = Dir.R ∨ (q : ℕ) = 10 ∧ r.moveDir = Dir.R := by
      native_decide
    exact hbb q s r hr hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 12 → (q : ℕ) = 9 ∧ r.moveDir = Dir.R ∨ (q : ℕ) = 12 ∧ r.moveDir = Dir.R := by
      native_decide
    exact hbb q s r hr hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 11 → (q : ℕ) = 10 ∧ r.moveDir = Dir.S := by
      native_decide
    exact hbb q s r hr hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 14 → (q : ℕ) = 11 ∧ r.moveDir = Dir.R ∨ (q : ℕ) = 14 ∧ r.moveDir = Dir.R := by
      native_decide
    exact hbb q s r hr hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 81 → ((q : ℕ) = 11 ∨ (q : ℕ) = 12 ∨ (q : ℕ) = 14 ∨ (q : ℕ) = 81) ∧ r.moveDir = Dir.R := by
      native_decide
    exact hbb q s r hr hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 13 → (q : ℕ) = 81 ∧ r.moveDir = Dir.R ∨ (q : ℕ) = 13 ∧ r.moveDir = Dir.R := by
      native_decide
    exact hbb q s r hr hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 84 → (q : ℕ) = 13 ∧ r.moveDir = Dir.L ∨ (q : ℕ) = 84 ∧ r.moveDir = Dir.L := by
      native_decide
    exact hbb q s r hr hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 85 → (q : ℕ) = 84 ∧ r.moveDir = Dir.L ∨ (q : ℕ) = 85 ∧ r.moveDir = Dir.L := by
      native_decide
    exact hbb q s r hr hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 86 → (q : ℕ) = 85 ∧ r.moveDir = Dir.R ∨ (q : ℕ) = 86 ∧ r.moveDir = Dir.R := by
      native_decide
    exact hbb q s r hr hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 87 → (q : ℕ) = 86 ∧ r.moveDir = Dir.S ∨ (q : ℕ) = 87 ∧ r.moveDir = Dir.R := by
      native_decide
    exact hbb q s r hr hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 20 → (q : ℕ) = 87 ∧ r.moveDir = Dir.S ∨ (q : ℕ) = 4 ∧ r.moveDir = Dir.L := by
      native_decide
    exact hbb q s r hr hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 21 → (q : ℕ) = 20 ∧ r.moveDir = Dir.R ∨ (q : ℕ) = 21 ∧ r.moveDir = Dir.R := by
      native_decide
    exact hbb q s r hr hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 51 → (q : ℕ) = 21 ∧ r.moveDir = Dir.L := by
      native_decide
    exact hbb q s r hr hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 22 → (q : ℕ) = 21 ∧ r.moveDir = Dir.S := by
      native_decide
    exact hbb q s r hr hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 23 → (q : ℕ) = 22 ∧ r.moveDir = Dir.L ∨ (q : ℕ) = 23 ∧ r.moveDir = Dir.L := by
      native_decide
    exact hbb q s r hr hx

/-- 表级:非 101 步读格 kind 约束。 -/
lemma a2p_chain_read (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101) :
    ((q : ℕ) = 4 → s.1 = SymKind.sel ∨ s.1 = SymKind.nosel) ∧
    ((q : ℕ) = 5 → s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧
    (((q : ℕ) = 76 ∨ (q : ℕ) = 8) → s.1 = SymKind.boundary ∨ s.1 = SymKind.consumed ∨
        s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧
    (((q : ℕ) = 77 ∨ (q : ℕ) = 9) → s.1 = SymKind.boundary ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧
    (((q : ℕ) = 10 ∨ (q : ℕ) = 11 ∨ (q : ℕ) = 12 ∨ (q : ℕ) = 14) → s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧
    ((q : ℕ) = 81 → s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨
        s.1 = SymKind.boundary) ∧
    ((q : ℕ) = 13 → s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨
        s.1 = SymKind.sel ∨ s.1 = SymKind.nosel ∨ s.1 = SymKind.boundary) ∧
    ((q : ℕ) = 84 → s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.consumed ∨
        s.1 = SymKind.boundary) ∧
    ((q : ℕ) = 85 → s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary) ∧
    ((q : ℕ) = 86 → s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary) ∧
    ((q : ℕ) = 87 → s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary) ∧
    ((q : ℕ) = 20 → s.1 = SymKind.boundary) ∧
    ((q : ℕ) = 21 → s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.consumed ∨
        s.1 = SymKind.sel ∨ s.1 = SymKind.nosel ∨ s.1 = SymKind.boundary) ∧
    ((q : ℕ) = 22 → s.1 = SymKind.boundary) ∧
    ((q : ℕ) = 23 → s.1 = SymKind.data0 ∨ s.1 = SymKind.boundary) ∧
    ((q : ℕ) = 51 → s.1 = SymKind.data0) := by
  repeat' constructor
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 4 →
          s.1 = SymKind.sel ∨ s.1 = SymKind.nosel := by
      native_decide
    exact hbb q s r hr hne hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 5 →
          s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
      native_decide
    exact hbb q s r hr hne hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 76 ∨ (q : ℕ) = 8 →
          s.1 = SymKind.boundary ∨ s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
      native_decide
    exact hbb q s r hr hne hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 77 ∨ (q : ℕ) = 9 →
          s.1 = SymKind.boundary ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
      native_decide
    exact hbb q s r hr hne hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 10 ∨ (q : ℕ) = 11 ∨ (q : ℕ) = 12 ∨ (q : ℕ) = 14 →
          s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
      native_decide
    exact hbb q s r hr hne hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 81 →
          s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary := by
      native_decide
    exact hbb q s r hr hne hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 13 →
          s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.sel ∨ s.1 = SymKind.nosel ∨ s.1 = SymKind.boundary := by
      native_decide
    exact hbb q s r hr hne hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 84 →
          s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.consumed ∨ s.1 = SymKind.boundary := by
      native_decide
    exact hbb q s r hr hne hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 85 →
          s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary := by
      native_decide
    exact hbb q s r hr hne hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 86 →
          s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary := by
      native_decide
    exact hbb q s r hr hne hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 87 →
          s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary := by
      native_decide
    exact hbb q s r hr hne hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 20 →
          s.1 = SymKind.boundary := by
      native_decide
    exact hbb q s r hr hne hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 21 →
          s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.consumed ∨ s.1 = SymKind.sel ∨ s.1 = SymKind.nosel ∨ s.1 = SymKind.boundary := by
      native_decide
    exact hbb q s r hr hne hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 22 →
          s.1 = SymKind.boundary := by
      native_decide
    exact hbb q s r hr hne hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 23 →
          s.1 = SymKind.data0 ∨ s.1 = SymKind.boundary := by
      native_decide
    exact hbb q s r hr hne hx
  · intro hx
    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 51 →
          s.1 = SymKind.data0 := by
      native_decide
    exact hbb q s r hr hne hx

/-- 表级:a2p_read_4 读集约束。 -/
lemma a2p_read_4 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 4) :
    s.1 = SymKind.sel ∨ s.1 = SymKind.nosel := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 4 →
        s.1 = SymKind.sel ∨ s.1 = SymKind.nosel := by
    native_decide
  exact hbb q s r hr hne hq

/-- 表级:a2p_read_5 读集约束。 -/
lemma a2p_read_5 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 5) :
    s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 5 →
        s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
    native_decide
  exact hbb q s r hr hne hq

/-- 表级:a2p_read_768 读集约束。 -/
lemma a2p_read_768 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 76 ∨ (q : ℕ) = 8) :
    s.1 = SymKind.boundary ∨ s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 76 ∨ (q : ℕ) = 8 →
        s.1 = SymKind.boundary ∨ s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
    native_decide
  exact hbb q s r hr hne hq

/-- 表级:a2p_read_779 读集约束。 -/
lemma a2p_read_779 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 77 ∨ (q : ℕ) = 9) :
    s.1 = SymKind.boundary ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 77 ∨ (q : ℕ) = 9 →
        s.1 = SymKind.boundary ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
    native_decide
  exact hbb q s r hr hne hq

/-- 表级:a2p_read_10fam 读集约束。 -/
lemma a2p_read_10fam (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 10 ∨ (q : ℕ) = 11 ∨ (q : ℕ) = 12 ∨ (q : ℕ) = 14) :
    s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 10 ∨ (q : ℕ) = 11 ∨ (q : ℕ) = 12 ∨ (q : ℕ) = 14 →
        s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
    native_decide
  exact hbb q s r hr hne hq

/-- 表级:a2p_read_81 读集约束。 -/
lemma a2p_read_81 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 81) :
    s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 81 →
        s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary := by
    native_decide
  exact hbb q s r hr hne hq

/-- 表级:a2p_read_13 读集约束。 -/
lemma a2p_read_13 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 13) :
    s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.sel ∨ s.1 = SymKind.nosel ∨ s.1 = SymKind.boundary := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 13 →
        s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.sel ∨ s.1 = SymKind.nosel ∨ s.1 = SymKind.boundary := by
    native_decide
  exact hbb q s r hr hne hq

/-- 表级:a2p_read_84 读集约束。 -/
lemma a2p_read_84 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 84) :
    s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.consumed ∨ s.1 = SymKind.boundary := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 84 →
        s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.consumed ∨ s.1 = SymKind.boundary := by
    native_decide
  exact hbb q s r hr hne hq

/-- 表级:a2p_read_85 读集约束。 -/
lemma a2p_read_85 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 85) :
    s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 85 →
        s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary := by
    native_decide
  exact hbb q s r hr hne hq

/-- 表级:a2p_read_86 读集约束。 -/
lemma a2p_read_86 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 86) :
    s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 86 →
        s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary := by
    native_decide
  exact hbb q s r hr hne hq

/-- 表级:a2p_read_87 读集约束。 -/
lemma a2p_read_87 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 87) :
    s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 87 →
        s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary := by
    native_decide
  exact hbb q s r hr hne hq

/-- 表级:a2p_read_20 读集约束。 -/
lemma a2p_read_20 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 20) :
    s.1 = SymKind.boundary := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 20 →
        s.1 = SymKind.boundary := by
    native_decide
  exact hbb q s r hr hne hq

/-- 表级:a2p_read_21 读集约束。 -/
lemma a2p_read_21 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 21) :
    s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.consumed ∨ s.1 = SymKind.sel ∨ s.1 = SymKind.nosel ∨ s.1 = SymKind.boundary := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 21 →
        s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.consumed ∨ s.1 = SymKind.sel ∨ s.1 = SymKind.nosel ∨ s.1 = SymKind.boundary := by
    native_decide
  exact hbb q s r hr hne hq

/-- 表级:a2p_read_22 读集约束。 -/
lemma a2p_read_22 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 22) :
    s.1 = SymKind.boundary := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 22 →
        s.1 = SymKind.boundary := by
    native_decide
  exact hbb q s r hr hne hq

/-- 表级:a2p_read_23 读集约束。 -/
lemma a2p_read_23 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 23) :
    s.1 = SymKind.data0 ∨ s.1 = SymKind.boundary := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 23 →
        s.1 = SymKind.data0 ∨ s.1 = SymKind.boundary := by
    native_decide
  exact hbb q s r hr hne hq

/-- 表级:a2p_read_51 读集约束。 -/
lemma a2p_read_51 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 51) :
    s.1 = SymKind.data0 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 51 →
        s.1 = SymKind.data0 := by
    native_decide
  exact hbb q s r hr hne hq

/-- 表级:自环步读格非 boundary。 -/
lemma a2p_selfloop_read (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hself : r.nextState = (q : ℕ))
    (hL : r.moveDir = Dir.L) :
    s.1 ≠ SymKind.boundary := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = (q : ℕ) →
        r.moveDir = Dir.L → s.1 ≠ SymKind.boundary := by
    native_decide
  exact hb q s r hr hself hL

/-- 表级:读 boundary 且 moveDir = L 的转移源态 ∈ {76, 8, 13, 84, 26}(其余 → 101)。 -/
lemma a2p_state0_head {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg) :
    cfg.state = 0 → cfg.headPos = (0 : ℤ) := by
  induction h with
  | nil => intro hq; simp [symInitialConfig]
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro hq
      have hq1lt : cfg₁.state < 102 := q12_path_state_lt102 input π₀ cfg₁ hprev
      have hb : (step.result.nextState = 0 → False) := by
        have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
            r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 0 → False := by
          native_decide
        intro hn
        exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
          (by rw [hread]; exact htrans) hn
      exact (hb (by simpa [symStepConfig] using hq)).elim

lemma a2p_state1_head {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg) :
    cfg.state = 1 → (1 : ℤ) ≤ cfg.headPos := by
  induction h with
  | nil => intro hq; simp [symInitialConfig] at hq
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro hq
      have hq1lt : cfg₁.state < 102 := q12_path_state_lt102 input π₀ cfg₁ hprev
      have hsrc : (cfg₁.state : ℕ) = 0 ∨ (cfg₁.state : ℕ) = 1 := by
        have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
            r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 1 →
              (q : ℕ) = 0 ∨ (q : ℕ) = 1 := by
          native_decide
        exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
          (by rw [hread]; exact htrans) (by simpa [symStepConfig] using hq)
      rcases hsrc with h0s | h1s
      · have h0h : cfg₁.headPos = (0 : ℤ) := a2p_state0_head hprev (by exact_mod_cast h0s)
        have hd : step.result.moveDir = Dir.R := by
          have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
              r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 0 →
                r.nextState = 1 → r.moveDir = Dir.R := by
            native_decide
          exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
            (by rw [hread]; exact htrans) h0s (by simpa [symStepConfig] using hq)
        dsimp [symStepConfig]
        rw [hd, h0h]
        dsimp [Dir.toInt]
        omega
      · have h1l := ih (by exact_mod_cast h1s)
        have hd : step.result.moveDir = Dir.R := by
          have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
              r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 1 →
                r.nextState = 1 → r.moveDir = Dir.R := by
            native_decide
          exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
            (by rw [hread]; exact htrans) h1s (by simpa [symStepConfig] using hq)
        dsimp [symStepConfig]
        rw [hd]
        dsimp [Dir.toInt]
        omega

lemma a2p_boundary_L_next (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hL : r.moveDir = Dir.L)
    (hb : s.1 = SymKind.boundary) :
    (q : ℕ) = 76 ∨ (q : ℕ) = 8 ∨ (q : ℕ) = 13 ∨ (q : ℕ) = 84 ∨ (q : ℕ) = 26 ∨
      (q : ℕ) = 22 ∨ (q : ℕ) = 3 ∨ r.nextState = 101 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.moveDir = Dir.L →
        s.1 = SymKind.boundary →
          (q : ℕ) = 76 ∨ (q : ℕ) = 8 ∨ (q : ℕ) = 13 ∨ (q : ℕ) = 84 ∨ (q : ℕ) = 26 ∨
            (q : ℕ) = 22 ∨ (q : ℕ) = 3 ∨ r.nextState = 101 := by
    native_decide
  exact hbb q s r hr hL hb

/-- 表级:读 boundary 的非 101 步,要么写回 boundary,要么源 = 20(占位扩展消除)。 -/
lemma a2p_bnd_write_n101 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s))
    (hb : s.1 = SymKind.boundary) :
    r.writeSym.1 = SymKind.boundary ∨ (q : ℕ) = 20 ∨ r.nextState = 101 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → s.1 = SymKind.boundary →
        r.writeSym.1 = SymKind.boundary ∨ (q : ℕ) = 20 ∨ r.nextState = 101 := by
    native_decide
  exact hbb q s r hr hb

/-- 表级:写 boundary 的步,要么源 = 51(重建分隔符),要么读格就是 boundary(写回)。 -/
lemma a2p_write_bnd_src (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s))
    (hw : r.writeSym.1 = SymKind.boundary) :
    (q : ℕ) = 51 ∨ s.1 = SymKind.boundary := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.writeSym.1 = SymKind.boundary →
        (q : ℕ) = 51 ∨ s.1 = SymKind.boundary := by
    native_decide
  exact hbb q s r hr hw

/-- 表级:写 consumed 的步,要么源 = 5(消耗新位),要么读格就是 consumed(写回)。 -/
lemma a2p_write_cons_src (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hw : r.writeSym.1 = SymKind.consumed) :
    (q : ℕ) = 5 ∨ s.1 = SymKind.consumed := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 →
        r.writeSym.1 = SymKind.consumed →
          (q : ℕ) = 5 ∨ s.1 = SymKind.consumed := by
    native_decide
  exact hbb q s r hr hne hw

/-- 表级:28 态读集。 -/
lemma a2p_read_28 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 28) :
    s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 28 →
        s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary := by
    native_decide
  exact hbb q s r hr hne hq

/-- 表级:1 态读集。 -/
lemma a2p_read_1 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 1) :
    s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 1 →
        s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary := by
    native_decide
  exact hbb q s r hr hne hq

/-- 表级:2 态读集。 -/
lemma a2p_read_2 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 2) :
    s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary ∨
      s.1 = SymKind.alpha := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 2 →
        s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary ∨
          s.1 = SymKind.alpha := by
    native_decide
  exact hbb q s r hr hne hq

/-- 表级:3 态读集。 -/
lemma a2p_read_3 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 3) :
    s.1 = SymKind.boundary := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 3 →
        s.1 = SymKind.boundary := by
    native_decide
  exact hbb q s r hr hne hq

/-- 表级:24 态读集。 -/
lemma a2p_read_24 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 24) :
    s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 24 →
        s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
    native_decide
  exact hbb q s r hr hne hq

/-- 表级:26 态读集。 -/
lemma a2p_read_26 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 26) :
    s.1 = SymKind.boundary ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨
      s.1 = SymKind.sel ∨ s.1 = SymKind.nosel := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 26 →
        s.1 = SymKind.boundary ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨
          s.1 = SymKind.sel ∨ s.1 = SymKind.nosel := by
    native_decide
  exact hbb q s r hr hne hq

/-- 表级:29 态读集。 -/
lemma a2p_read_29 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 29) :
    s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.sel ∨ s.1 = SymKind.nosel := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 29 →
        s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.sel ∨ s.1 = SymKind.nosel := by
    native_decide
  exact hbb q s r hr hne hq

/-- 表级:27 态读集。 -/
lemma a2p_read_27 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 27) :
    s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 27 →
        s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
    native_decide
  exact hbb q s r hr hne hq

/-- 表级:38 态读集。 -/
lemma a2p_read_38 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 38) :
    s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 38 →
        s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary := by
    native_decide
  exact hbb q s r hr hne hq

/-- 表级:21 读 sel/nosel → 51 L(占位重建的触发)。 -/
lemma a2p_read_21_sel (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 21) :
    r.nextState = 51 ∨ s.1 ≠ SymKind.sel ∧ s.1 ≠ SymKind.nosel := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 21 →
        r.nextState = 51 ∨ s.1 ≠ SymKind.sel ∧ s.1 ≠ SymKind.nosel := by
    native_decide
  exact hbb q s r hr hne hq


/-- 原生位串每格 kind ∈ {data0, data1}。 -/
lemma a2p_bits_native_kind (n : ℕ) {j : ℕ} (hj : j < (encodeBitsSymNative n).length) :
    ((encodeBitsSymNative n).getD j Sym.blank).1 = SymKind.data0 ∨
    ((encodeBitsSymNative n).getD j Sym.blank).1 = SymKind.data1 := by
  unfold encodeBitsSymNative
  rw [List.getD_eq_getElem ((Nat.digits 2 n).map (fun d => if d = 0 then Sym.data0 else Sym.data1))
    Sym.blank hj]
  rw [List.getElem_map (fun d => if d = 0 then Sym.data0 else Sym.data1)]
  have hj' : j < (Nat.digits 2 n).length := by
    simpa [encodeBitsSymNative, List.length_map] using hj
  by_cases hd : (Nat.digits 2 n)[j] = 0 <;> simp [hd]

/-- 元素表编码每格 kind ∈ {alpha, data0, data1}。 -/
lemma a2p_elems_rec_kind (elems : List ℕ) {j : ℕ}
    (hj : j < (encodeElementsSym elems).length) :
    ((encodeElementsSym elems).getD j Sym.blank).1 = SymKind.alpha ∨
    ((encodeElementsSym elems).getD j Sym.blank).1 = SymKind.data0 ∨
    ((encodeElementsSym elems).getD j Sym.blank).1 = SymKind.data1 := by
  induction elems generalizing j with
  | nil => simp [encodeElementsSym] at hj
  | cons v rest ih =>
      cases rest with
      | nil =>
          cases j with
          | zero => simp [encodeElementsSym, Sym.alpha]
          | succ k =>
              simp only [encodeElementsSym]
              change ((encodeBitsSymNative v).getD k Sym.blank).1 = SymKind.alpha ∨
                ((encodeBitsSymNative v).getD k Sym.blank).1 = SymKind.data0 ∨
                ((encodeBitsSymNative v).getD k Sym.blank).1 = SymKind.data1
              have hkb : k < (encodeBitsSymNative v).length := by
                simp [encodeElementsSym, List.length_append] at hj
                omega
              exact Or.inr (a2p_bits_native_kind v hkb)
      | cons w rest' =>
          cases j with
          | zero => simp [encodeElementsSym, Sym.alpha]
          | succ k =>
              simp only [encodeElementsSym]
              change ((encodeBitsSymNative v ++ encodeElementsSym (w :: rest')).getD k Sym.blank).1 =
                  SymKind.alpha ∨
                ((encodeBitsSymNative v ++ encodeElementsSym (w :: rest')).getD k Sym.blank).1 =
                  SymKind.data0 ∨
                ((encodeBitsSymNative v ++ encodeElementsSym (w :: rest')).getD k Sym.blank).1 =
                  SymKind.data1
              simp [encodeElementsSym, List.length_append] at hj
              by_cases hkb : k < (encodeBitsSymNative v).length
              · have hg : (encodeBitsSymNative v ++ encodeElementsSym (w :: rest')).getD k Sym.blank =
                    (encodeBitsSymNative v).getD k Sym.blank :=
                  List.getD_append (encodeBitsSymNative v) (encodeElementsSym (w :: rest'))
                    Sym.blank k hkb
                rcases a2p_bits_native_kind v hkb with hk0 | hk1
                · right; left
                  rw [hg]
                  exact hk0
                · right; right
                  rw [hg]
                  exact hk1
              · have hk'' : k - (encodeBitsSymNative v).length < (encodeElementsSym (w :: rest')).length := by
                  omega
                have hg : (encodeBitsSymNative v ++ encodeElementsSym (w :: rest')).getD k Sym.blank =
                    (encodeElementsSym (w :: rest')).getD (k - (encodeBitsSymNative v).length) Sym.blank := by
                  have h := List.getD_append_right (encodeBitsSymNative v)
                    (encodeElementsSym (w :: rest')) Sym.blank k (by omega)
                  simpa using h
                rcases ih hk'' with ha | hd0 | hd1
                · left
                  rw [hg]
                  exact ha
                · right; left
                  rw [hg]
                  exact hd0
                · right; right
                  rw [hg]
                  exact hd1

/-- encS 元素区 getD 位移:n+2+j 位 = 元素表 j 位。 -/
lemma a2p_enc_elems_getD (inst : SubsetSumInstance) {j : ℕ}
    (hj : j < (encodeElementsSym inst.elements).length) :
    (encodeInstanceSym inst).getD ((encodeBitsSym inst.target).length + 2 + j) Sym.blank =
      (encodeElementsSym inst.elements).getD j Sym.blank := by
  unfold encodeInstanceSym
  calc
    ([Sym.boundary] ++ encodeBitsSym inst.target ++ [Sym.boundary] ++
        encodeElementsSym inst.elements ++ [Sym.boundary]).getD
        ((encodeBitsSym inst.target).length + 2 + j) Sym.blank
        = (encodeElementsSym inst.elements ++ [Sym.boundary]).getD j Sym.blank := by
            have h := List.getD_append_right ([Sym.boundary] ++ encodeBitsSym inst.target ++ [Sym.boundary])
              (encodeElementsSym inst.elements ++ [Sym.boundary]) Sym.blank
              ((encodeBitsSym inst.target).length + 2 + j) (by simp)
            simpa using h
    _ = (encodeElementsSym inst.elements).getD j Sym.blank :=
            List.getD_append (encodeElementsSym inst.elements) [Sym.boundary] Sym.blank j hj

/-- encS 元素区每格 kind ∈ {alpha, data0, data1}(初始无 sel/nosel/consumed)。 -/
lemma a2p_elems_init_kind (inst : SubsetSumInstance) {j : ℕ}
    (hj : j < (encodeElementsSym inst.elements).length) :
    ((encodeInstanceSym inst).getD
      ((encodeBitsSym inst.target).length + 2 + j) Sym.blank).1 = SymKind.alpha ∨
    ((encodeInstanceSym inst).getD
      ((encodeBitsSym inst.target).length + 2 + j) Sym.blank).1 = SymKind.data0 ∨
    ((encodeInstanceSym inst).getD
      ((encodeBitsSym inst.target).length + 2 + j) Sym.blank).1 = SymKind.data1 := by
  rw [a2p_enc_elems_getD inst hj]
  exact a2p_elems_rec_kind inst.elements hj

/-- hc81k 的行走不变量:S-链源状态(76/8/77/9/10/11/12/14/81)存在停点 c,
    头 ≤ c ≤ L-2 且 tape c = consumed(即链上尚未走过、已写 consumed 的格)。 
    封装为 irreducible def,避免 ∃-型假设干扰同一声明内其它 omega 精化。 -/
@[irreducible] def a2p_walk81 (inst : SubsetSumInstance) (s : ℤ) (cfg : SymConfig) : Prop :=
  (cfg.state = 76 ∨ cfg.state = 8 ∨ cfg.state = 77 ∨ cfg.state = 9 ∨ cfg.state = 10 ∨
      cfg.state = 11 ∨ cfg.state = 12 ∨ cfg.state = 14 ∨ cfg.state = 81) →
    ∃ c : ℤ, cfg.headPos ≤ c ∧ c ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 2 ∧ (cfg.tape c).1 = SymKind.consumed

/-- E 右支:活动分隔符 s 的存在与相对位置约束。 -/
def a2p_EProp (inst : SubsetSumInstance) (cfg : SymConfig) : Prop :=
  ∃ s : ℤ, (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) ≤ s ∧
    s ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 3 ∧
    (cfg.tape s).1 = SymKind.boundary ∧
    (∀ j : ℤ, j < (((encodeInstanceSym inst).length : ℕ) : ℤ) →
        (cfg.tape j).1 = SymKind.boundary →
        j = 0 ∨ j = (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 ∨ j = s) ∧
    ((cfg.state = 76 ∨ cfg.state = 8 ∨ cfg.state = 84 ∨ cfg.state = 26 ∨
        cfg.state = 29 ∨ cfg.state = 24) → s ≤ cfg.headPos) ∧
    ((cfg.state = 13 ∨ cfg.state = 5 ∨ cfg.state = 4 ∨ cfg.state = 2 ∨
        cfg.state = 3) →
        s + 1 ≤ cfg.headPos) ∧
    ((cfg.state = 85 ∨ cfg.state = 77 ∨ cfg.state = 9 ∨ cfg.state = 27 ∨
        cfg.state = 38) → cfg.headPos ≤ s - 1) ∧
    ((cfg.state = 86 ∨ cfg.state = 87 ∨ cfg.state = 28 ∨ cfg.state = 1) →
        cfg.headPos ≤ s) ∧
    ((cfg.state = 4) → cfg.headPos ≤ s + 1) ∧
    ((cfg.state = 28) → (1 : ℤ) ≤ cfg.headPos) ∧
    ((cfg.state = 10 ∨ cfg.state = 11 ∨ cfg.state = 12) → cfg.headPos ≤ s) ∧
    ((cfg.state = 14) → cfg.headPos ≤ s) ∧
    ((cfg.state = 81) → cfg.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 2) ∧
    a2p_walk81 inst s cfg ∧
    (∀ j : ℤ, j < (((encodeInstanceSym inst).length : ℕ) : ℤ) →
        (cfg.tape j).1 = SymKind.consumed →
        s + 1 ≤ j ∧ j ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 2) ∧
    ((cfg.state = 76 ∨ cfg.state = 8 ∨ cfg.state = 84 ∨ cfg.state = 26 ∨
        cfg.state = 29) → cfg.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 2) ∧
    ((cfg.state = 2 ∨ cfg.state = 3 ∨ cfg.state = 24) →
        cfg.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1)

/-- G 分量(占位扩展后 #₀ 右移,tape(n+1) 只在非豁免态保持 boundary)。 -/
def a2p_G (inst : SubsetSumInstance) (cfg : SymConfig) : Prop :=
  (cfg.tape (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ)).1 = SymKind.boundary ∨
    (cfg.tape (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ)).1 = SymKind.data0 ∨
    (cfg.tape (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ)).1 = SymKind.data1

-- ============================================================================
-- 主定理(负区版):主循环每态不进入负区(0 ≤ 头)+ 下界分量 + consumed 位 ≥ n+2
-- ============================================================================
theorem a2p_mainloop_no_neg (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (ht : 0 < inst.target) (gS : List Sym)
    {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π cfg) :
    (∃ step : SymStep, ∃ π₃ : List SymStep, ∃ cfg₃ : SymConfig,
      step.fromState = cfg.state ∧ step.readSym = cfg.tape cfg.headPos ∧
      step.result ∈ VerifierSym.transition (cfg.state, cfg.tape cfg.headPos) ∧
      SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS)
        (π ++ step :: π₃) cfg₃ ∧ cfg₃.state = 100) →
    (∀ step ∈ π, step.result.nextState ≠ 101) →
    ((0 : ℤ) ≤ cfg.headPos) ∧
    (cfg.state = 4 → (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ cfg.headPos) ∧
    (cfg.state = 5 → (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ cfg.headPos) ∧
    ((cfg.state = 76 ∨ cfg.state = 8) →
        (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) ≤ cfg.headPos) ∧
    (cfg.state = 13 → (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ cfg.headPos) ∧
    (cfg.state = 84 → (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) ≤ cfg.headPos) ∧
    (cfg.state = 20 → (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) ≤ cfg.headPos ∧
        cfg.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 2) ∧
    (cfg.state = 86 → (1 : ℤ) ≤ cfg.headPos) ∧
    (cfg.state = 87 → (1 : ℤ) ≤ cfg.headPos) ∧
    (cfg.state = 21 → (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ cfg.headPos ∧
        cfg.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1) ∧
    (cfg.state = 51 → (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) ≤ cfg.headPos ∧
        cfg.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 3) ∧
    (cfg.state = 5 → cfg.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1) ∧
    (cfg.state = 13 → cfg.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1) ∧
    (∀ j : ℤ, (cfg.tape j).1 = SymKind.consumed →
        (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ j) ∧
    (cfg.tape 0).1 = SymKind.boundary ∧
    (cfg.tape ((((encodeInstanceSym inst).length : ℕ) : ℤ) - 1)).1 = SymKind.boundary ∧
    (((cfg.state = 21 ∨ cfg.state = 51 ∨ cfg.state = 22 ∨
          cfg.state = 23 ∨ cfg.state = 100 ∨ cfg.state = 101) ∨ a2p_EProp inst cfg)) ∧
    (((cfg.state = 21 ∨ cfg.state = 51) →
        ∀ j : ℤ, j < (((encodeInstanceSym inst).length : ℕ) : ℤ) →
          (cfg.tape j).1 = SymKind.boundary →
          j = 0 ∨ j = (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1) ∧
     ((cfg.state = 20 ∨ cfg.state = 21 ∨ cfg.state = 22 ∨ cfg.state = 23 ∨
          cfg.state = 51) →
        ∀ j : ℤ, j < (((encodeInstanceSym inst).length : ℕ) : ℤ) →
          (cfg.tape j).1 = SymKind.consumed → cfg.headPos ≤ j)) ∧
    (cfg.state = 22 → cfg.headPos = (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1) ∧
    a2p_G inst cfg := by
  induction h with
  | nil =>
      intro hext hno101
      constructor
      · simp [symInitialConfig]
      constructor
      · intro h4; simp [symInitialConfig] at h4
      constructor
      · intro h5; simp [symInitialConfig] at h5
      constructor
      · intro h76; rcases h76 with h | h <;> simp [symInitialConfig] at h
      constructor
      · intro h13; simp [symInitialConfig] at h13
      constructor
      · intro h84; simp [symInitialConfig] at h84
      constructor
      · intro h20; simp [symInitialConfig] at h20
      constructor
      · intro h86; simp [symInitialConfig] at h86
      constructor
      · intro h87; simp [symInitialConfig] at h87
      constructor
      · intro h21; simp [symInitialConfig] at h21
      constructor
      · intro h51; simp [symInitialConfig] at h51
      constructor
      · intro h5; simp [symInitialConfig] at h5
      constructor
      · intro h13; simp [symInitialConfig] at h13
      constructor
      · intro j hj -- consumed 位 ≥ n+2(初始无 consumed)
        by_contra hlt
        have hjl : j < (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) := by omega
        have hj0 : 0 ≤ j := by
          by_contra hneg
          have hcell : (symInitialConfig (encodeInstanceSym inst ++ gS)).tape j = Sym.blank := by
            simp [symInitialConfig, hneg]
          rw [hcell] at hj
          cases hj
        have hto : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj0
        have htn : j.toNat < (encodeBitsSym inst.target).length + 2 := by
          apply Int.ofNat_lt.mp
          rw [hto]
          exact hjl
        have hlen2 : (encodeBitsSym inst.target).length + 2 ≤
            (encodeInstanceSym inst ++ gS).length := by
          rw [List.length_append, r7_enc_len]
          omega
        have hc : (symInitialConfig (encodeInstanceSym inst ++ gS)).tape j =
            (encodeInstanceSym inst ++ gS).getD j.toNat Sym.blank :=
          a2p_tape_at_getD (encodeInstanceSym inst ++ gS) hj0 (lt_of_lt_of_le htn hlen2)
        rw [hc] at hj
        -- j ∈ [0, n+1]:boundary/data0/data1,无 consumed
        have hkind : ((encodeInstanceSym inst ++ gS).getD j.toNat Sym.blank).1 =
              SymKind.boundary ∨
            ((encodeInstanceSym inst ++ gS).getD j.toNat Sym.blank).1 = SymKind.data0 ∨
            ((encodeInstanceSym inst ++ gS).getD j.toNat Sym.blank).1 = SymKind.data1 := by
          by_cases hz : j.toNat = 0
          · left
            have hb := a2p_pos0_boundary inst gS
            rw [hz, hb]
            rfl
          · have hzt : 1 ≤ j.toNat := by omega
            by_cases hmid : j.toNat = (encodeBitsSym inst.target).length + 1
            · left
              have hb := a2p_pos_mid_boundary inst gS
              rw [hmid, hb]
              rfl
            · right
              have hbn : j.toNat ≤ (encodeBitsSym inst.target).length := by omega
              have harg : j.toNat = 1 + (j.toNat - 1) := by omega
              rw [harg]
              exact a2p_bits_kind_wS inst gS (by omega)
        rcases hkind with hb0' | hdata
        · rw [hb0'] at hj
          cases hj
        · rcases hdata with hd0 | hd1
          · rw [hd0] at hj
            cases hj
          · rw [hd1] at hj
            cases hj
      constructor
      · rw [a2p_tape0_wS inst gS]; rfl
      constructor
      · -- tape(L-1) = boundary
        have hLg : 0 ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 := by
          rw [r7_enc_len]
          omega
        have hc := a2p_tape_at_getD (encodeInstanceSym inst ++ gS)
          (j := (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1) hLg (by
            simp
            rw [r7_enc_len]
            omega)
        rw [hc]
        have hto : ((((encodeInstanceSym inst).length : ℕ) : ℤ) - 1).toNat =
            (encodeInstanceSym inst).length - 1 := by omega
        rw [hto]
        exact ((a2p_pos_last_boundary inst gS) ▸ rfl)
      constructor
      · -- E:s = n+1(初始中分隔符)
        right
        refine ⟨(((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rfl
        · rw [r7_enc_len]
          omega
        · have hst := a2p_tape_at_getD (encodeInstanceSym inst ++ gS)
            (j := (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ)) (by omega) (by
              simp
              rw [r7_enc_len]
              omega)
          rw [hst]
          exact ((a2p_pos_mid_boundary inst gS) ▸ rfl)
        · -- 唯一性:j < L 且 boundary → j ∈ {0, L-1, n+1}
          intro j hjl hjb
          have hj0 : 0 ≤ j := by
            by_contra hneg
            have hcell : (symInitialConfig (encodeInstanceSym inst ++ gS)).tape j = Sym.blank := by
              simp [symInitialConfig, hneg]
            rw [hcell] at hjb
            cases hjb
          have hjt : j.toNat < (encodeInstanceSym inst).length := by
            apply Int.ofNat_lt.mp
            rw [Int.toNat_of_nonneg hj0]
            exact hjl
          have hc : (symInitialConfig (encodeInstanceSym inst ++ gS)).tape j =
              (encodeInstanceSym inst ++ gS).getD j.toNat Sym.blank :=
            a2p_tape_at_getD (encodeInstanceSym inst ++ gS) hj0
              (lt_of_lt_of_le hjt (by rw [List.length_append]; omega))
          rw [hc] at hjb
          rw [a2p_getD_prefix_left (a := encodeInstanceSym inst) (b := gS) hjt] at hjb
          by_cases hz : j.toNat = 0
          · left
            omega
          · have hzt : 1 ≤ j.toNat := by omega
            by_cases hmid : j.toNat = (encodeBitsSym inst.target).length + 1
            · right; right
              omega
            · by_cases hlast : j.toNat = (encodeInstanceSym inst).length - 1
              · right; left
                omega
              · by_cases hle : j.toNat ≤ (encodeBitsSym inst.target).length
                · have harg : j.toNat = 1 + (j.toNat - 1) := by omega
                  rw [harg] at hjb
                  have hk := a2p_bits_region_kind inst (j := j.toNat - 1) (by omega)
                  rcases hk with hk0 | hk1
                  · rw [hk0] at hjb; cases hjb
                  · rw [hk1] at hjb; cases hjb
                · have harg : j.toNat = (encodeBitsSym inst.target).length + 2 +
                        (j.toNat - (encodeBitsSym inst.target).length - 2) := by omega
                  rw [harg] at hjb
                  have hk := a2p_elems_region_nonboundary inst
                    (j := j.toNat - (encodeBitsSym inst.target).length - 2) (by
                      rw [r7_enc_len] at hjt hlast
                      omega)
                  exact (hk hjb).elim
        · -- 76/8/84/26/29/24 → s ≤ 头(初始态 = 0:vacuous)
          intro hq
          rcases hq with h | h | h | h | h | h <;> simp [symInitialConfig] at h
        · -- 13/5/4/2 → s+1 ≤ 头
          intro hq
          rcases hq with h | h | h | h <;> simp [symInitialConfig] at h
        · -- 85/77/9/27/38 → 头 ≤ s-1
          intro hq
          rcases hq with h | h | h | h | h <;> simp [symInitialConfig] at h
        · -- 86/87/28/1 → 头 ≤ s
          intro hq
          rcases hq with h | h | h | h <;> simp [symInitialConfig] at h
        · -- 4 → 头 ≤ s+1(初始态 = 0:vacuous)
          intro hq
          simp [symInitialConfig] at hq
        · -- 28 → 1 ≤ 头(初始态 = 0:vacuous)
          intro hq
          simp [symInitialConfig] at hq
        · -- 10/11/12 → 头 ≤ s-1(初始态 = 0:vacuous)
          intro hq
          rcases hq with h | h | h <;> simp [symInitialConfig] at h
        · -- 14 → 头 ≤ s(初始态 = 0:vacuous)
          intro hq
          simp [symInitialConfig] at hq
        · -- 81 → 头 ≤ s+1(初始态 = 0:vacuous)
          intro hq
          have h0 : (symInitialConfig (encodeInstanceSym inst ++ gS)).state = (0 : Fin 102) := rfl
          rw [h0] at hq
          cases hq
        · -- a2p_walk81(初始:0 ∉ S:vacuous)
          rw [a2p_walk81]
          intro hq
          have h0 : (symInitialConfig (encodeInstanceSym inst ++ gS)).state = (0 : Fin 102) := rfl
          rw [h0] at hq
          exact absurd hq (by decide)
        · -- consumed:j < L ∧ consumed → s+1 ≤ j ∧ j ≤ L-2(初始无 consumed)
          intro j hjl hjc
          have hj0 : 0 ≤ j := by
            by_contra hneg
            have hcell : (symInitialConfig (encodeInstanceSym inst ++ gS)).tape j = Sym.blank := by
              simp [symInitialConfig, hneg]
            rw [hcell] at hjc
            cases hjc
          have hjt : j.toNat < (encodeInstanceSym inst).length := by
            apply Int.ofNat_lt.mp
            rw [Int.toNat_of_nonneg hj0]
            exact hjl
          have hc : (symInitialConfig (encodeInstanceSym inst ++ gS)).tape j =
              (encodeInstanceSym inst ++ gS).getD j.toNat Sym.blank :=
            a2p_tape_at_getD (encodeInstanceSym inst ++ gS) hj0
              (lt_of_lt_of_le hjt (by rw [List.length_append]; omega))
          rw [hc] at hjc
          rw [a2p_getD_prefix_left (a := encodeInstanceSym inst) (b := gS) hjt] at hjc
          by_cases hz : j.toNat = 0
          · have hb := r7_enc_getD_0 inst
            rw [hz, hb] at hjc
            cases hjc
          · have hzt : 1 ≤ j.toNat := by omega
            by_cases hmid : j.toNat = (encodeBitsSym inst.target).length + 1
            · have hb := r7_enc_getD_mid inst
              rw [hmid, hb] at hjc
              cases hjc
            · by_cases hlast : j.toNat = (encodeInstanceSym inst).length - 1
              · have hb := r7_enc_getD_last inst
                rw [hlast, hb] at hjc
                cases hjc
              · by_cases hle : j.toNat ≤ (encodeBitsSym inst.target).length
                · have harg : j.toNat = 1 + (j.toNat - 1) := by omega
                  rw [harg] at hjc
                  have hk := a2p_bits_region_kind inst (j := j.toNat - 1) (by omega)
                  rcases hk with hk0 | hk1
                  · rw [hk0] at hjc; cases hjc
                  · rw [hk1] at hjc; cases hjc
                · have harg : j.toNat = (encodeBitsSym inst.target).length + 2 +
                        (j.toNat - (encodeBitsSym inst.target).length - 2) := by omega
                  rw [harg] at hjc
                  have hk := a2p_elems_init_kind inst
                    (j := j.toNat - (encodeBitsSym inst.target).length - 2) (by
                      rw [r7_enc_len] at hjt hlast
                      omega)
                  rcases hk with ha | hd0 | hd1
                  · rw [ha] at hjc; cases hjc
                  · rw [hd0] at hjc; cases hjc
                  · rw [hd1] at hjc; cases hjc
        · -- hc1u:(76/8/84/26/29 → 头 ≤ L-2) ∧ (2/3/24 → 头 ≤ L-1)(初始态 = 0:vacuous)
          refine ⟨?_, ?_⟩
          · intro hq
            rcases hq with h | h | h | h | h
            · dsimp [symInitialConfig] at h; exfalso; exact absurd h (by decide)
            · dsimp [symInitialConfig] at h; exfalso; exact absurd h (by decide)
            · dsimp [symInitialConfig] at h; exfalso; exact absurd h (by decide)
            · dsimp [symInitialConfig] at h; exfalso; exact absurd h (by decide)
            · dsimp [symInitialConfig] at h; exfalso; exact absurd h (by decide)
          · intro hq
            rcases hq with h | h | h
            · dsimp [symInitialConfig] at h; exfalso; exact absurd h (by decide)
            · dsimp [symInitialConfig] at h; exfalso; exact absurd h (by decide)
            · dsimp [symInitialConfig] at h; exfalso; exact absurd h (by decide)
      constructor
      · -- F:21/51 → boundary 格 ⊆ {0, L-1} ∧ 清扫集合 {20,21,22,23,51}(初始态 = 0:vacuous)
        constructor
        · intro h21or51
          rcases h21or51 with h | h <;> simp [symInitialConfig] at h
        · intro hq j hjl hjc
          rcases hq with h | h | h | h | h <;> simp [symInitialConfig] at h
      constructor
      · -- 22 态头 = L-1(初始态 = 0:vacuous)
        intro h22n
        simp [symInitialConfig] at h22n
      -- G(第 19 分量)
      unfold a2p_G
      left
      have hst := a2p_tape_at_getD (encodeInstanceSym inst ++ gS)
        (j := (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ)) (by omega) (by
          simp
          rw [r7_enc_len]
          omega)
      rw [hst]
      have hmid1 : ((encodeInstanceSym inst ++ gS).getD
          ((encodeBitsSym inst.target).length + 1) Sym.blank).1 = SymKind.boundary := by
        exact ((a2p_pos_mid_boundary inst gS) ▸ rfl)
      exact hmid1
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro hext hno101
      have hq1lt : cfg₁.state < 102 :=
        q12_path_state_lt102 (encodeInstanceSym inst ++ gS) π₀ cfg₁ hprev
      have hno101₀ : ∀ step₀ ∈ π₀, step₀.result.nextState ≠ 101 := by
        intro step₀ hs0
        exact hno101 step₀ (by simp [hs0])
      have hne : step.result.nextState ≠ 101 :=
        hno101 step (by simp)
      have hdir := a2p_mainloop_dir ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
        (by simpa [hread] using htrans)
      rcases hdir with ⟨hd4, hd5, hd768, hd779, hd10, hd12, hd11, hd14, hd81, hd13,
        hd84, hd85, hd86, hd87, hd20, hd21, hd51, hd22, hd23⟩
      rcases ih (by
        rcases hext with ⟨stepₑ, π₃, cfg₃, hfₑ, hrₑ, htₑ, hₑ, hₑs⟩
        exact ⟨step, stepₑ :: π₃, cfg₃, hfrom, hread, htrans,
          (by simpa [List.cons_append] using hₑ), hₑs⟩) hno101₀ with
        ⟨hge0, hi4, hi5, hi768, hi13, hi84, hi20, hi86, hi87, hi21, hi51, hi5u, hi13u,
          hic, hb0, hbL, hE, hF, hi22, hG⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- 全局 0 ≤ 头
        rw [symStepConfig]
        by_cases hL : step.result.moveDir = Dir.L
        · have hge1 : (1 : ℤ) ≤ cfg₁.headPos := by
            by_cases hb_step : step.readSym.1 = SymKind.boundary
            · have hsrc := a2p_boundary_L_next ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                (by simpa [hread] using htrans) hL hb_step
              rcases hsrc with h76 | h8 | h13 | h84 | h26 | h22src | h3src | h101
              · have hlb := hi768 (by left; exact_mod_cast h76)
                omega
              · have hlb := hi768 (by right; exact_mod_cast h8)
                omega
              · have hlb := hi13 (by exact_mod_cast h13)
                omega
              · have hlb := hi84 (by exact_mod_cast h84)
                omega
              · have hq26 : cfg₁.state = 26 := by exact_mod_cast h26
                have hlb : (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) ≤ cfg₁.headPos :=
                  (a2p_s56_head inst hm ht gS hprev hno101₀ (by right; exact hq26)).2.2 hq26
                omega
              · have hq22 : cfg₁.state = 22 := by exact_mod_cast h22src
                have h22e : cfg₁.headPos = (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 :=
                  hi22 hq22
                rw [r7_enc_len] at h22e
                omega
              · have hq3 : cfg₁.state = 3 := by exact_mod_cast h3src
                have hlb := (a2p_s3_head inst hm ht gS hprev hno101₀ hq3).1
                omega
              · exact (hne h101).elim
            · by_contra hnot
              have hh : cfg₁.headPos = 0 := by omega
              have hb_s : step.readSym.1 = SymKind.boundary := by
                simpa [hread, hh] using hb0
              exact hb_step hb_s
          change (0 : ℤ) ≤ cfg₁.headPos + step.result.moveDir.toInt
          rw [hL]
          dsimp [Dir.toInt]
          change (0 : ℤ) ≤ cfg₁.headPos - 1
          have hle : (0 : ℤ) ≤ cfg₁.headPos - 1 := by
            have := sub_le_sub_right hge1 (1 : ℤ)
            norm_num at this ⊢
            exact this
          exact hle
        · by_cases hR : step.result.moveDir = Dir.R
          · rw [hR]
            dsimp [Dir.toInt]
            omega
          · have hS : step.result.moveDir = Dir.S := by
              have hcases : step.result.moveDir = Dir.L ∨ step.result.moveDir = Dir.R ∨
                  step.result.moveDir = Dir.S := by
                cases step.result.moveDir <;> simp
              rcases hcases with h1 | h2 | h3
              · exact (hL h1).elim
              · exact (hR h2).elim
              · exact h3
            rw [hS]
            dsimp [Dir.toInt]
            simpa using hge0
      · intro h4s -- 4 ≥ n+2
        dsimp [symStepConfig] at h4s
        have hfull : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS)
            (π₀ ++ [step]) (symStepConfig cfg₁ step.result) :=
          SymReachablePath.cons (π₀ := π₀) (step := step) (cfg := cfg₁)
            hprev hfrom hread htrans
        have hhno : ∀ step₀ ∈ π₀ ++ [step], step₀.result.nextState ≠ 101 := by
          intro step₀ hs0
          exact hno101 step₀ (by simpa using hs0)
        rcases hext with ⟨stepₑ, π₃, cfg₃, hfₑ, hrₑ, htₑ, hₑ, hₑs⟩
        have hfₑ4 : stepₑ.fromState = 4 := by
          dsimp [symStepConfig] at hfₑ
          exact hfₑ.trans h4s
        have hneₑ : stepₑ.result.nextState ≠ 101 := by
          have hno := a2p_reach_no_101 hₑ (by rw [hₑs]; decide)
          exact hno stepₑ (by simp)
        have hk : stepₑ.readSym.1 = SymKind.sel ∨ stepₑ.readSym.1 = SymKind.nosel :=
          a2p_read_4 ⟨4, by decide⟩ stepₑ.readSym stepₑ.result
            (by
              have ht : stepₑ.result ∈ VerifierSym.transition (4, stepₑ.readSym) := by
                have ht' : stepₑ.result ∈ VerifierSym.transition (stepₑ.fromState, stepₑ.readSym) := by
                  rw [← hfₑ] at htₑ
                  rw [← hrₑ] at htₑ
                  exact htₑ
                simpa [hfₑ4] using ht'
              exact ht) hneₑ rfl
        have hge := a2p_sel_ge_n2_all inst hm ht gS hfull hhno
          (symStepConfig cfg₁ step.result).headPos (by
            have hr : (symStepConfig cfg₁ step.result).tape
                (symStepConfig cfg₁ step.result).headPos = stepₑ.readSym := hrₑ.symm
            simpa [hr] using hk)
        exact hge
      · intro h5s -- 5 ≥ n+2
        dsimp [symStepConfig] at h5s
        rcases hd5 h5s with h4src | h13src
        · rcases h4src with ⟨hq, hd⟩
          have h4l : (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ cfg₁.headPos :=
            hi4 (by exact_mod_cast hq)
          dsimp [symStepConfig]
          rw [hd]
          dsimp [Dir.toInt]
          omega
        · rcases h13src with ⟨hq, hd⟩
          have h13l : (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ cfg₁.headPos :=
            hi13 (by exact_mod_cast hq)
          dsimp [symStepConfig]
          rw [hd]
          dsimp [Dir.toInt]
          omega
      · intro h768s -- 76/8 ≥ n+1
        dsimp [symStepConfig] at h768s
        rcases hd768 h768s with h5src | h76src | h8src
        · rcases h5src with ⟨hq, hd⟩
          have h5l : (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ cfg₁.headPos :=
            hi5 (by exact_mod_cast hq)
          dsimp [symStepConfig]
          rw [hd]
          dsimp [Dir.toInt]
          omega
        · rcases h76src with ⟨hq, hd⟩
          have hq76 : cfg₁.state = 76 := by exact_mod_cast hq
          have h76l : (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) ≤ cfg₁.headPos :=
            hi768 (by left; exact hq76)
          have hge2 : (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ cfg₁.headPos := by
            have h768s76 : step.result.nextState = 76 := by
              rcases h768s with h | h
              · simpa [symStepConfig, hq76] using h
              · have hsrc : (cfg₁.state : ℕ) = 5 ∨ (cfg₁.state : ℕ) = 8 := by
                  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 8 →
                        (q : ℕ) = 5 ∨ (q : ℕ) = 8 := by
                    native_decide
                  exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                    (by simpa [hread] using htrans) h
                rcases hsrc with h5s | h8s
                · have hv : (76 : ℕ) = 5 := by simpa [hq76] using h5s
                  omega
                · have hv : (76 : ℕ) = 8 := by simpa [hq76] using h8s
                  omega
            have hnb : step.readSym.1 ≠ SymKind.boundary := by
              exact a2p_selfloop_read ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                (by simpa [hread] using htrans) (by simpa [hq76] using h768s76) (by simpa [hd])
            have hnex : ¬ (cfg₁.state = 21 ∨ cfg₁.state = 51 ∨
                cfg₁.state = 22 ∨ cfg₁.state = 23 ∨ cfg₁.state = 100 ∨ cfg₁.state = 101) := by
              intro hx
              rcases hx with a | b | c | d | e | f <;> omega
            have hsE76 : a2p_EProp inst cfg₁ := hE.resolve_left hnex
            rcases hsE76 with ⟨s, hs1, hs2, hst, huniq, hc1, hc2, hc3, hc4, hc4u, hc28, hc10, hc14, hc81, hc81k, hcons, hc1u⟩
            have h76ge : s ≤ cfg₁.headPos := hc1 (by left; exact hq76)
            have hne_s : cfg₁.headPos ≠ s := by
              intro he
              have hb : step.readSym.1 = SymKind.boundary := by
                simpa [hread, he] using hst
              exact hnb hb
            omega
          dsimp [symStepConfig]
          rw [hd]
          dsimp [Dir.toInt]
          omega
        · rcases h8src with ⟨hq, hd⟩
          have hq8 : cfg₁.state = 8 := by exact_mod_cast hq
          have h8l : (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) ≤ cfg₁.headPos :=
            hi768 (by right; exact hq8)
          have hge2 : (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ cfg₁.headPos := by
            have h768s8 : step.result.nextState = 8 := by
              rcases h768s with h | h
              · have hsrc : (cfg₁.state : ℕ) = 5 ∨ (cfg₁.state : ℕ) = 76 := by
                  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 76 →
                        (q : ℕ) = 5 ∨ (q : ℕ) = 76 := by
                    native_decide
                  exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                    (by simpa [hread] using htrans) h
                rcases hsrc with h5s | h76s
                · have hv : (8 : ℕ) = 5 := by simpa [hq8] using h5s
                  omega
                · have hv : (8 : ℕ) = 76 := by simpa [hq8] using h76s
                  omega
              · simpa [symStepConfig, hq8] using h
            have hnb : step.readSym.1 ≠ SymKind.boundary := by
              exact a2p_selfloop_read ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                (by simpa [hread] using htrans) (by simpa [hq8] using h768s8) (by simpa [hd])
            have hnex : ¬ (cfg₁.state = 21 ∨ cfg₁.state = 51 ∨
                cfg₁.state = 22 ∨ cfg₁.state = 23 ∨ cfg₁.state = 100 ∨ cfg₁.state = 101) := by
              intro hx
              rcases hx with a | b | c | d | e | f <;> omega
            have hsE8 : a2p_EProp inst cfg₁ := hE.resolve_left hnex
            rcases hsE8 with ⟨s, hs1, hs2, hst, huniq, hc1, hc2, hc3, hc4, hc4u, hc28, hc10, hc14, hc81, hc81k, hcons, hc1u⟩
            have h8ge : s ≤ cfg₁.headPos := hc1 (by right; left; exact hq8)
            have hne_s : cfg₁.headPos ≠ s := by
              intro he
              have hb : step.readSym.1 = SymKind.boundary := by
                simpa [hread, he] using hst
              exact hnb hb
            omega
          dsimp [symStepConfig]
          rw [hd]
          dsimp [Dir.toInt]
          omega
      · intro h13s -- 13 ≥ n+2
        dsimp [symStepConfig] at h13s
        rcases hd13 h13s with h81src | h13src
        · rcases h81src with ⟨hq, hd⟩
          have hq81 : cfg₁.state = 81 := by exact_mod_cast hq
          have hc : (step.readSym.1 = SymKind.consumed) := by
            have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 81 →
                  r.nextState = 13 → s.1 = SymKind.consumed := by
              native_decide
            exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
              (by simpa [hread] using htrans) hq81 (by simpa [symStepConfig] using h13s)
          have hcpos : (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ cfg₁.headPos :=
            hic cfg₁.headPos (by simpa [hread] using hc)
          dsimp [symStepConfig]
          rw [hd]
          dsimp [Dir.toInt]
          omega
        · rcases h13src with ⟨hq, hd⟩
          have h13l : (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ cfg₁.headPos :=
            hi13 (by exact_mod_cast hq)
          dsimp [symStepConfig]
          rw [hd]
          dsimp [Dir.toInt]
          omega
      · intro h84s -- 84 ≥ n+1
        dsimp [symStepConfig] at h84s
        rcases hd84 h84s with h13src | h84src
        · rcases h13src with ⟨hq, hd⟩
          have hq13 : cfg₁.state = 13 := by exact_mod_cast hq
          have hnex : ¬ (cfg₁.state = 21 ∨ cfg₁.state = 51 ∨
              cfg₁.state = 22 ∨ cfg₁.state = 23 ∨ cfg₁.state = 100 ∨ cfg₁.state = 101) := by
            intro hex
            rcases hex with h21' | h51' | h22 | h23 | h100 | h101 <;> omega
          have hsE : a2p_EProp inst cfg₁ := hE.resolve_left hnex
          rcases hsE with ⟨s, hs1, hs2, hst, huniq, hc1, hc2, hc3, hc4, hc4u, hc28, hc10, hc14, hc81, hc81k, hcons, hc1u⟩
          have h13l : s + 1 ≤ cfg₁.headPos := hc2 (by left; exact hq13)
          dsimp [symStepConfig]
          rw [hd]
          dsimp [Dir.toInt]
          omega
        · rcases h84src with ⟨hq, hd⟩
          have hq84 : cfg₁.state = 84 := by exact_mod_cast hq
          have hnex : ¬ (cfg₁.state = 21 ∨ cfg₁.state = 51 ∨
              cfg₁.state = 22 ∨ cfg₁.state = 23 ∨ cfg₁.state = 100 ∨ cfg₁.state = 101) := by
            intro hex
            rcases hex with h21' | h51' | h22 | h23 | h100 | h101 <;> omega
          have hsE : a2p_EProp inst cfg₁ := hE.resolve_left hnex
          rcases hsE with ⟨s, hs1, hs2, hst, huniq, hc1, hc2, hc3, hc4, hc4u, hc28, hc10, hc14, hc81, hc81k, hcons, hc1u⟩
          have h84ge : s ≤ cfg₁.headPos := hc1 (by right; right; left; exact hq84)
          have hnb : step.readSym.1 ≠ SymKind.boundary := by
            exact a2p_selfloop_read ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
              (by simpa [hread] using htrans) (by simpa [symStepConfig, hq84] using h84s) (by simpa [hd])
          have hne_s : cfg₁.headPos ≠ s := by
            intro he
            have hb : step.readSym.1 = SymKind.boundary := by
              simpa [hread, he] using hst
            exact hnb hb
          dsimp [symStepConfig]
          rw [hd]
          dsimp [Dir.toInt]
          omega
      · intro h20l -- 20:n+1 ≤ 头 ∧ 头 ≤ L-2
        dsimp [symStepConfig] at h20l
        rcases hd20 h20l with h87src | h4src
        · rcases h87src with ⟨hq, hd⟩
          have hq87 : cfg₁.state = 87 := by exact_mod_cast hq
          have hb87 : step.readSym.1 = SymKind.boundary := by
            have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 87 →
                  r.nextState = 20 → s.1 = SymKind.boundary := by
              native_decide
            exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
              (by simpa [hread] using htrans) hq87 (by simpa [symStepConfig] using h20l)
          have hnex : ¬ (cfg₁.state = 21 ∨ cfg₁.state = 51 ∨
              cfg₁.state = 22 ∨ cfg₁.state = 23 ∨ cfg₁.state = 100 ∨ cfg₁.state = 101) := by
            intro hex
            rcases hex with h21' | h51' | h22 | h23 | h100 | h101 <;> omega
          have hsE : a2p_EProp inst cfg₁ := hE.resolve_left hnex
          rcases hsE with ⟨s, hs1, hs2, hst, huniq, hc1, hc2, hc3, hc4, hc4u, hc28, hc10, hc14, hc81, hc81k, hcons, hc1u⟩
          have h87u : cfg₁.headPos ≤ s := hc4 (by right; left; exact hq87)
          have h87l1 : (1 : ℤ) ≤ cfg₁.headPos := hi87 hq87
          have h87u2 : cfg₁.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 3 :=
            le_trans h87u hs2
          have h87s : cfg₁.headPos = s := by
            have hb := huniq cfg₁.headPos (by
              rw [r7_enc_len] at hs2 h87u2 ⊢
              omega) (by simpa [hread] using hb87)
            rcases hb with h0 | hL | hs
            · have hz : (1 : ℤ) ≤ (0 : ℤ) := by simpa [h0] using h87l1
              exfalso
              omega
            · have hz : cfg₁.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 3 :=
                le_trans h87u hs2
              rw [hL] at hz
              rw [r7_enc_len] at hz
              exfalso
              omega
            · exact hs
          constructor
          · dsimp [symStepConfig]
            rw [hd, h87s]
            dsimp [Dir.toInt]
            simpa using hs1
          · dsimp [symStepConfig]
            rw [hd, h87s]
            dsimp [Dir.toInt]
            have hsL : s ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 2 :=
              le_trans hs2 (by rw [r7_enc_len]; omega)
            simpa using hsL
        · rcases h4src with ⟨hq, hd⟩
          have hq4 : cfg₁.state = 4 := by exact_mod_cast hq
          have h4l := hi4 hq4
          have hnex : ¬ (cfg₁.state = 21 ∨ cfg₁.state = 51 ∨
              cfg₁.state = 22 ∨ cfg₁.state = 23 ∨ cfg₁.state = 100 ∨ cfg₁.state = 101) := by
            intro hex
            rcases hex with h21' | h51' | h22 | h23 | h100 | h101 <;> omega
          have hsE : a2p_EProp inst cfg₁ := hE.resolve_left hnex
          rcases hsE with ⟨s, hs1, hs2, hst, huniq, hc1, hc2, hc3, hc4, hc4u, hc28, hc10, hc14, hc81, hc81k, hcons, hc1u⟩
          have h4u : cfg₁.headPos ≤ s + 1 := hc4u hq4
          constructor
          · dsimp [symStepConfig]
            rw [hd]
            dsimp [Dir.toInt]
            change (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) ≤ cfg₁.headPos - 1
            have := sub_le_sub_right h4l (1 : ℤ)
            norm_num at this ⊢
            exact this
          · dsimp [symStepConfig]
            rw [hd]
            dsimp [Dir.toInt]
            change cfg₁.headPos - 1 ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 2
            have hh : cfg₁.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 2 := by omega
            omega
      · intro h86l -- 86 ≥ 1
        dsimp [symStepConfig] at h86l
        rcases hd86 h86l with h85src | h86src
        · rcases h85src with ⟨hq, hd⟩
          have h85g : (0 : ℤ) ≤ cfg₁.headPos := hge0
          dsimp [symStepConfig]
          rw [hd]
          dsimp [Dir.toInt]
          omega
        · rcases h86src with ⟨hq, hd⟩
          have h86g : (1 : ℤ) ≤ cfg₁.headPos := hi86 (by exact_mod_cast hq)
          dsimp [symStepConfig]
          rw [hd]
          dsimp [Dir.toInt]
          omega
      · intro h87l -- 87 ≥ 1
        dsimp [symStepConfig] at h87l
        rcases hd87 h87l with h86src | h87src
        · rcases h86src with ⟨hq, hd⟩
          have h86g : (1 : ℤ) ≤ cfg₁.headPos := hi86 (by exact_mod_cast hq)
          dsimp [symStepConfig]
          rw [hd]
          dsimp [Dir.toInt]
          simpa using h86g
        · rcases h87src with ⟨hq, hd⟩
          have h87g : (1 : ℤ) ≤ cfg₁.headPos := hi87 (by exact_mod_cast hq)
          dsimp [symStepConfig]
          rw [hd]
          dsimp [Dir.toInt]
          omega
      · -- 21 界:n+2 ≤ 头 ∧ 头 ≤ L-1
        intro h21s
        dsimp [symStepConfig] at h21s
        rcases hd21 h21s with h20src | h21src
        · rcases h20src with ⟨hq, hd⟩
          have h20l := (hi20 (by exact_mod_cast hq)).1
          have h20u := (hi20 (by exact_mod_cast hq)).2
          constructor
          · dsimp [symStepConfig]
            rw [hd]
            dsimp [Dir.toInt]
            omega
          · dsimp [symStepConfig]
            rw [hd]
            dsimp [Dir.toInt]
            omega
        · rcases h21src with ⟨hq, hd⟩
          have h21l := (hi21 (by exact_mod_cast hq)).1
          have h21u := (hi21 (by exact_mod_cast hq)).2
          have hnb : step.readSym.1 ≠ SymKind.boundary := by
            intro hb
            have hnext : step.result.nextState = 22 := by
              have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 21 →
                    s.1 = SymKind.boundary → r.nextState = 22 := by
                native_decide
              exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                (by simpa [hread] using htrans) (by exact_mod_cast hq) hb
            rw [hnext] at h21s
            cases h21s
          have hneL : cfg₁.headPos ≠ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 := by
            intro heL
            have hb : step.readSym.1 = SymKind.boundary := by
              simpa [hread, heL] using hbL
            exact hnb hb
          constructor
          · dsimp [symStepConfig]
            rw [hd]
            dsimp [Dir.toInt]
            omega
          · dsimp [symStepConfig]
            rw [hd]
            dsimp [Dir.toInt]
            omega
      · -- 51 界:n+1 ≤ 头 ∧ 头 ≤ L-3
        intro h51s
        dsimp [symStepConfig] at h51s
        rcases hd51 h51s with ⟨hq, hd⟩
        have h21l := (hi21 (by exact_mod_cast hq)).1
        have h21u := (hi21 (by exact_mod_cast hq)).2
        have hnb : step.readSym.1 ≠ SymKind.boundary := by
          intro hb
          have hnext : step.result.nextState = 22 := by
            have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 21 →
                  s.1 = SymKind.boundary → r.nextState = 22 := by
              native_decide
            exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
              (by simpa [hread] using htrans) (by exact_mod_cast hq) hb
          rw [hnext] at h51s
          cases h51s
        have hneL : cfg₁.headPos ≠ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 := by
          intro heL
          have hb : step.readSym.1 = SymKind.boundary := by
            simpa [hread, heL] using hbL
          exact hnb hb
        constructor
        · dsimp [symStepConfig]
          rw [hd]
          dsimp [Dir.toInt]
          omega
        · dsimp [symStepConfig]
          rw [hd]
          dsimp [Dir.toInt]
          omega
      · -- 5 上界 ≤ L-1
        intro h5s
        dsimp [symStepConfig] at h5s
        rcases hd5 h5s with h4src | h13src
        · rcases h4src with ⟨hq, hd⟩
          have hq4 : cfg₁.state = 4 := by exact_mod_cast hq
          have hnex : ¬ (cfg₁.state = 21 ∨ cfg₁.state = 51 ∨
              cfg₁.state = 22 ∨ cfg₁.state = 23 ∨ cfg₁.state = 100 ∨ cfg₁.state = 101) := by
            intro hex
            rcases hex with h21' | h51' | h22 | h23 | h100 | h101 <;> omega
          have hsE : a2p_EProp inst cfg₁ := by
            exact (hE.resolve_left hnex)
          rcases hsE with ⟨s, hs1, hs2, hst, huniq, hc1, hc2, hc3, hc4, hc4u, hc28, hc10, hc14, hc81, hc81k, hcons, hc1u⟩
          have h4u : cfg₁.headPos ≤ s + 1 := hc4u hq4
          dsimp [symStepConfig]
          rw [hd]
          dsimp [Dir.toInt]
          omega
        · rcases h13src with ⟨hq, hd⟩
          have h13u := hi13u (by exact_mod_cast hq)
          dsimp [symStepConfig]
          rw [hd]
          dsimp [Dir.toInt]
          omega
      · -- 13 上界 ≤ L-1
        intro h13s
        dsimp [symStepConfig] at h13s
        rcases hd13 h13s with h81src | h13src
        · rcases h81src with ⟨hq, hd⟩
          have hq81 : cfg₁.state = 81 := by exact_mod_cast hq
          have hc : step.readSym.1 = SymKind.consumed := by
            have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 81 →
                  r.nextState = 13 → s.1 = SymKind.consumed := by
              native_decide
            exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
              (by simpa [hread] using htrans) hq81 (by simpa [symStepConfig] using h13s)
          have hnex : ¬ (cfg₁.state = 21 ∨ cfg₁.state = 51 ∨
              cfg₁.state = 22 ∨ cfg₁.state = 23 ∨ cfg₁.state = 100 ∨ cfg₁.state = 101) := by
            intro hex
            rcases hex with h21' | h51' | h22 | h23 | h100 | h101 <;> omega
          have hsE : a2p_EProp inst cfg₁ := by
            exact (hE.resolve_left hnex)
          rcases hsE with ⟨s, hs1, hs2, hst, huniq, hc1, hc2, hc3, hc4, hc4u, hc28, hc10, hc14, hc81, hc81k, hcons, hc1u⟩
          have h81u : cfg₁.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 2 := hc81 hq81
          dsimp [symStepConfig]
          rw [hd]
          dsimp [Dir.toInt]
          omega
        · rcases h13src with ⟨hq, hd⟩
          have hq13 : cfg₁.state = 13 := by exact_mod_cast hq
          have hc : step.readSym.1 = SymKind.consumed := by
            have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 13 →
                  r.nextState = 13 → s.1 = SymKind.consumed := by
              native_decide
            exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
              (by simpa [hread] using htrans) hq13 (by simpa [symStepConfig] using h13s)
          have hnex : ¬ (cfg₁.state = 21 ∨ cfg₁.state = 51 ∨
              cfg₁.state = 22 ∨ cfg₁.state = 23 ∨ cfg₁.state = 100 ∨ cfg₁.state = 101) := by
            intro hex
            rcases hex with h21' | h51' | h22 | h23 | h100 | h101 <;> omega
          have hsE : a2p_EProp inst cfg₁ := by
            exact (hE.resolve_left hnex)
          rcases hsE with ⟨s, hs1, hs2, hst, huniq, hc1, hc2, hc3, hc4, hc4u, hc28, hc10, hc14, hc81, hc81k, hcons, hc1u⟩
          have h13u' := hi13u hq13
          have hneL : cfg₁.headPos ≠ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 := by
            intro he
            have hb : step.readSym.1 = SymKind.boundary := by
              simpa [hread, he] using hbL
            rw [hb] at hc
            cases hc
          dsimp [symStepConfig]
          rw [hd]
          dsimp [Dir.toInt]
          omega
      · intro j hj -- consumed 位 ≥ n+2
        by_cases hw : cfg₁.headPos = j
        · have hwj : (step.result.writeSym).1 = SymKind.consumed := by
            dsimp [symStepConfig] at hj
            simpa [hw] using hj
          have hsrcq : cfg₁.state = 5 ∨
              (step.readSym.1 = SymKind.consumed ∧
                (cfg₁.state = 76 ∨ cfg₁.state = 8 ∨ cfg₁.state = 81 ∨
                  cfg₁.state = 13 ∨ cfg₁.state = 84 ∨ cfg₁.state = 100)) := by
            have hb5 : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 →
                  r.writeSym.1 = SymKind.consumed → (q : ℕ) ≠ 5 →
                    s.1 = SymKind.consumed := by
              native_decide
            have hbq : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 →
                  r.writeSym.1 = SymKind.consumed → (q : ℕ) ≠ 5 →
                    (q : ℕ) = 76 ∨ (q : ℕ) = 8 ∨ (q : ℕ) = 81 ∨
                      (q : ℕ) = 13 ∨ (q : ℕ) = 84 ∨ (q : ℕ) = 100 := by
              native_decide
            by_cases hq5 : cfg₁.state = 5
            · exact Or.inl hq5
            · right
              exact ⟨hb5 ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                  (by simpa [hread] using htrans) hne hwj hq5,
                hbq ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                  (by simpa [hread] using htrans) hne hwj hq5⟩
          rcases hsrcq with hq5 | hcons
          · have h5l : (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ cfg₁.headPos :=
              hi5 hq5
            rw [← hw]
            exact h5l
          · have hjc : (cfg₁.tape cfg₁.headPos).1 = SymKind.consumed := by
              simpa [hread] using hcons.1
            have hcl : (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ cfg₁.headPos :=
              hic cfg₁.headPos hjc
            rw [← hw]
            exact hcl
        · have hj' : (cfg₁.tape j).1 = SymKind.consumed := by
            dsimp [symStepConfig] at hj
            simpa [if_neg (Ne.symm hw)] using hj
          exact hic j hj'
      · -- tape 0 保持
        dsimp [symStepConfig]
        by_cases hw : cfg₁.headPos = 0
        · have hb1 : step.readSym.1 = SymKind.boundary := by
            simpa [hread, hw] using hb0
          have hkeep : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
              r ∈ VerifierSym.transition ((q : ℕ), s) → s.1 = SymKind.boundary →
                (q : ℕ) ≠ 20 → r.writeSym.1 = SymKind.boundary := by
            native_decide
          have hne20 : cfg₁.state ≠ 20 := by
            intro h20s
            have h20g : (1 : ℤ) ≤ cfg₁.headPos := by
              have := (hi20 h20s).1
              omega
            rw [hw] at h20g
            omega
          rw [hw]
          simp
          exact hkeep ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
            (by simpa [← hread] using htrans) hb1 hne20
        · rw [if_neg (Ne.symm hw)]
          exact hb0
      · -- tape(L-1) 保持
        dsimp [symStepConfig]
        by_cases hw : cfg₁.headPos = (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1
        · have hb1 : step.readSym.1 = SymKind.boundary := by
            simpa [hread, hw] using hbL
          have hw1 := a2p_bnd_write_n101 ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
            (by simpa [hread] using htrans) hb1
          rcases hw1 with hwb | hq20 | h101
          · simpa [hw, hwb]
          · have h20u := (hi20 (by exact_mod_cast hq20)).2
            rw [hw] at h20u
            omega
          · exact (hne h101).elim
        · rw [if_neg (Ne.symm hw)]
          exact hbL
      · -- E:活动分隔符(豁免 ∨ a2p_EProp)
        by_cases hnew : (symStepConfig cfg₁ step.result).state = 21 ∨
            (symStepConfig cfg₁ step.result).state = 51 ∨
            (symStepConfig cfg₁ step.result).state = 22 ∨
            (symStepConfig cfg₁ step.result).state = 23 ∨
            (symStepConfig cfg₁ step.result).state = 100 ∨
            (symStepConfig cfg₁ step.result).state = 101
        · exact Or.inl hnew
        · exact Or.inr (by
            have hnew' : ¬ ((symStepConfig cfg₁ step.result).state = 21 ∨
                (symStepConfig cfg₁ step.result).state = 51 ∨
                (symStepConfig cfg₁ step.result).state = 22 ∨
                (symStepConfig cfg₁ step.result).state = 23 ∨
                (symStepConfig cfg₁ step.result).state = 100 ∨
                (symStepConfig cfg₁ step.result).state = 101) := hnew
            dsimp [symStepConfig] at hnew'
            rcases hE with hex | hsE
            · -- 旧豁免:唯一非豁免出边 51 → 4
              rcases hex with h21 | h51 | h22 | h23 | h100 | h101
              · -- 21 → {51,22,21,101}
                have hnext : step.result.nextState = 51 ∨ step.result.nextState = 22 ∨
                    step.result.nextState = 21 ∨ step.result.nextState = 101 := by
                  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                      r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 21 →
                        r.nextState = 51 ∨ r.nextState = 22 ∨ r.nextState = 21 ∨
                        r.nextState = 101 := by
                    native_decide
                  exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                    (by simpa [hread] using htrans) (by exact_mod_cast h21)
                rcases hnext with hn | hn | hn | hn
                · exact (hnew' (by right; left; exact hn)).elim
                · exact (hnew' (by right; right; left; exact hn)).elim
                · exact (hnew' (by left; exact hn)).elim
                · exact (hnew' (by right; right; right; right; right; exact hn)).elim
              · -- 51 → 4 ∨ 101
                have hnext : step.result.nextState = 4 ∨ step.result.nextState = 101 := by
                  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                      r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 51 →
                        r.nextState = 4 ∨ r.nextState = 101 := by
                    native_decide
                  exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                    (by simpa [hread] using htrans) (by exact_mod_cast h51)
                rcases hnext with hn4 | hn101
                · -- 51 → 4:s' = 51头
                  refine ⟨cfg₁.headPos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · exact (hi51 h51).1
                  · exact (hi51 h51).2
                  · -- tape(s') = boundary(51 写 boundary@头 = s')
                    have hw : step.result.writeSym.1 = SymKind.boundary := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 51 →
                            r.nextState = 4 → r.writeSym.1 = SymKind.boundary := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by simpa [hread] using htrans) (by exact_mod_cast h51) hn4
                    dsimp [symStepConfig]
                    simp [hw]
                  · -- 唯一性:旧 51 态 boundary ⊆ {0, L-1}(hF)
                    intro j hjl hjb
                    by_cases hj : j = cfg₁.headPos
                    · right; right
                      exact hj
                    · have hjb' : (cfg₁.tape j).1 = SymKind.boundary := by
                        dsimp [symStepConfig] at hjb
                        rw [if_neg hj] at hjb
                        exact hjb
                      have hF51 := hF.1 (by right; exact h51)
                      have hb' := hF51 j hjl hjb'
                      rcases hb' with h0 | hL
                      · left
                        exact h0
                      · right; left
                        exact hL
                  · -- 76/8/84/26/29/24 → s' ≤ 新头:新态 = 4 ∉
                    intro hq
                    dsimp [symStepConfig] at hq
                    rcases hq with h | h | h | h | h | h
                    · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                    · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                    · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                    · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                    · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                    · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                  · -- 13/5/4/2 → s'+1 ≤ 新头:新态 = 4:新头 = 51头+1 = s'+1
                    intro hq
                    dsimp [symStepConfig] at hq
                    rcases hq with h | h | h | h | h
                    · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                    · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                    · have hR : step.result.moveDir = Dir.R := by
                        have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                            r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 51 →
                              r.nextState = 4 → r.moveDir = Dir.R := by
                          native_decide
                        exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                          (by simpa [hread] using htrans) (by exact_mod_cast h51) hn4
                      dsimp [symStepConfig]
                      rw [hR]
                      dsimp [Dir.toInt]
                      norm_num
                    · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                    · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                  · -- 85/77/9/27/38 → 新头 ≤ s'-1:新态 = 4 ∉
                    intro hq
                    dsimp [symStepConfig] at hq
                    rcases hq with h | h | h | h | h
                    · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                    · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                    · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                    · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                    · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                  · -- 86/87/28/1 → 新头 ≤ s':新态 = 4 ∉
                    intro hq
                    dsimp [symStepConfig] at hq
                    rcases hq with h | h | h | h
                    · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                    · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                    · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                    · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                  · -- 4 → 新头 ≤ s'+1:新头 = s'+1
                    intro hq
                    have hR : step.result.moveDir = Dir.R := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 51 →
                            r.nextState = 4 → r.moveDir = Dir.R := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by simpa [hread] using htrans) (by exact_mod_cast h51) hn4
                    dsimp [symStepConfig]
                    rw [hR]
                    dsimp [Dir.toInt]
                    norm_num
                  · -- 28 → 1 ≤ 新头:新态 = 4 ∉
                    intro hq
                    dsimp [symStepConfig] at hq
                    exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using hq)) (by decide)
                  · -- 10/11/12 → 新头 ≤ s'-1:新态 = 4 ∉
                    intro hq
                    dsimp [symStepConfig] at hq
                    rcases hq with h | h | h
                    · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                    · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                    · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                  · -- 14 → 新头 ≤ s':新态 = 4 ∉
                    intro hq
                    dsimp [symStepConfig] at hq
                    exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using hq)) (by decide)
                  · -- 81 → 新头 ≤ s'+1:新态 = 4 ∉
                    intro hq
                    exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using hq)) (by decide)
                  · -- a2p_walk81:新态 = 4 ∉ S
                    rw [a2p_walk81]
                    intro hq
                    dsimp [symStepConfig] at hq
                    rw [hn4] at hq
                    exact absurd hq (by decide)
                  · -- consumed:51 态无 consumed;写格 = s' 写 boundary
                    intro j hjl hjc
                    by_cases hj : j = cfg₁.headPos
                    · have hw : step.result.writeSym.1 = SymKind.boundary := by
                        have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                            r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 51 →
                              r.nextState = 4 → r.writeSym.1 = SymKind.boundary := by
                          native_decide
                        exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                          (by simpa [hread] using htrans) (by exact_mod_cast h51) hn4
                      dsimp [symStepConfig] at hjc
                      rw [hj] at hjc
                      simp at hjc
                      rw [hw] at hjc
                      cases hjc
                    · -- j ≠ 51头:用 51 的松式实例 + 51头 处是 boundary(行 515 写的就是它)
                      have hjc₁ : (cfg₁.tape j).1 = SymKind.consumed := by
                        first
                          | rw [if_neg hj] at hjc
                          | (simp only [symStepConfig] at hjc; rw [if_neg hj] at hjc)
                        exact hjc
                      have hc51 := hF.2 (by right; right; right; right; exact h51) j hjl hjc₁
                      have hneq : j ≠ cfg₁.headPos := by
                        intro hje
                        have hb : ((symStepConfig cfg₁ step.result).tape cfg₁.headPos).1 = SymKind.boundary := by
                          simp only [symStepConfig]
                          rw [if_pos trivial]
                          have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                              r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 51 →
                                r.nextState = 4 → r.writeSym.1 = SymKind.boundary := by native_decide
                          exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                            (by simpa [hread] using htrans) (by exact_mod_cast h51) hn4
                        rw [hje] at hjc
                        rw [hb] at hjc
                        exact absurd hjc (by decide)
                      have hbLs : ((symStepConfig cfg₁ step.result).tape ((((encodeInstanceSym inst).length : ℕ) : ℤ) - 1)).1 =
                          SymKind.boundary := by
                        simp only [symStepConfig]
                        rw [if_neg (by have := (hi51 h51).2; omega)]
                        exact hbL
                      have hneL : j ≠ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 := by
                        intro hje
                        rw [hje] at hjc
                        rw [hbLs] at hjc
                        exact absurd hjc (by decide)
                      rw [r7_enc_len] at hjl hneL ⊢
                      refine ⟨?_, ?_⟩ <;> omega
                  · -- hc1u:(76/8/84/26/29 → 头 ≤ L-2) ∧ (2/3/24 → 头 ≤ L-1):新态 = 4 → vacuous
                    refine ⟨?_, ?_⟩
                    · intro hq
                      rcases hq with h | h | h | h | h
                      · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                      · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                      · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                      · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                      · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                    · intro hq
                      rcases hq with h | h | h
                      · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                      · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                      · exfalso; exact absurd (hn4.symm.trans (by simpa only [symStepConfig] using h)) (by decide)
                · exact (hnew' (by right; right; right; right; right; exact hn101)).elim
              · -- 22 → 23 ∨ 101
                have hnext : step.result.nextState = 23 ∨ step.result.nextState = 101 := by
                  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                      r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 22 →
                        r.nextState = 23 ∨ r.nextState = 101 := by
                    native_decide
                  exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                    (by simpa [hread] using htrans) (by exact_mod_cast h22)
                rcases hnext with hn | hn
                · exact (hnew' (by right; right; right; left; exact hn)).elim
                · exact (hnew' (by right; right; right; right; right; exact hn)).elim
              · -- 23 → {23,100,101}
                have hnext : step.result.nextState = 23 ∨ step.result.nextState = 100 ∨
                    step.result.nextState = 101 := by
                  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                      r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 23 →
                        r.nextState = 23 ∨ r.nextState = 100 ∨ r.nextState = 101 := by
                    native_decide
                  exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                    (by simpa [hread] using htrans) (by exact_mod_cast h23)
                rcases hnext with hn | hn | hn
                · exact (hnew' (by right; right; right; left; exact hn)).elim
                · exact (hnew' (by right; right; right; right; left; exact hn)).elim
                · exact (hnew' (by right; right; right; right; right; exact hn)).elim
              · -- 100 → 100
                have hnext : step.result.nextState = 100 := by
                  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                      r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 100 →
                        r.nextState = 100 := by
                    native_decide
                  exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                    (by simpa [hread] using htrans) (by exact_mod_cast h100)
                exact (hnew' (by right; right; right; right; left; exact hnext)).elim
              · -- 101 → 101
                have hnext : step.result.nextState = 101 := by
                  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                      r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 101 →
                        r.nextState = 101 := by
                    native_decide
                  exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                    (by simpa [hread] using htrans) (by exact_mod_cast h101)
                exact (hnew' (by right; right; right; right; right; exact hnext)).elim
            · -- 旧态非豁免:s' = s 通用保持
              rcases hsE with ⟨s, hs1, hs2, hst, huniq, hc1, hc2, hc3, hc4, hc4u, hc28, hc10, hc14, hc81, hc81k, hcons, hc1u⟩
              refine ⟨s, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · -- hs1:n+1 ≤ s
                exact hs1
              · -- hs2:s ≤ L-3
                exact hs2
              · -- tape(s) = boundary
                by_cases hw : cfg₁.headPos = s
                · have hb : step.readSym.1 = SymKind.boundary := by
                    simpa [hread, hw] using hst
                  have hw1 := a2p_bnd_write_n101 ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                    (by rw [hread]; exact htrans) hb
                  rcases hw1 with hwb | hq20 | h101
                  · dsimp [symStepConfig]
                    simpa [hw, hwb]
                  · have hnext : step.result.nextState = 21 := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 20 →
                            s.1 = SymKind.boundary → r.nextState = 21 := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) (by exact_mod_cast hq20) hb
                    exact (hnew' (by left; exact hnext)).elim
                  · exact (hne h101).elim
                · dsimp [symStepConfig]
                  rw [if_neg (Ne.symm hw)]
                  exact hst
              · -- 唯一性
                intro j hjl hjb
                by_cases hj : j = cfg₁.headPos
                · have hwj : step.result.writeSym.1 = SymKind.boundary := by
                    dsimp [symStepConfig] at hjb
                    rw [hj] at hjb
                    simp at hjb
                    exact hjb
                  have hw1 := a2p_write_bnd_src ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                    (by rw [hread]; exact htrans) hwj
                  rcases hw1 with hq51 | hb
                  · have hnot51E : ¬ a2p_EProp inst cfg₁ := by
                      intro he
                      rcases he with ⟨s2, hs21, hs22, hst2, huniq2, _⟩
                      have hq51' : cfg₁.state = 51 := by exact_mod_cast hq51
                      have hF51 := hF.1 (by right; exact hq51')
                      have hb' := hF51 s2 (by rw [r7_enc_len] at hs22 ⊢; omega) hst2
                      rcases hb' with h0 | hL
                      · have hz : (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) ≤ 0 := by
                          simpa [h0] using hs21
                        have hpos : (1 : ℤ) ≤ (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) := by
                          exact_mod_cast (Nat.succ_pos (encodeBitsSym inst.target).length)
                        exact (not_le_of_gt hpos hz)
                      · have hz : s2 ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 := by
                          simpa [hL] using hs22
                        rw [r7_enc_len] at hz
                        exfalso
                        omega
                    exact (hnot51E ⟨s, hs1, hs2, hst, huniq, hc1, hc2, hc3, hc4, hc4u, hc28, hc10, hc14, hc81, hc81k, hcons, hc1u⟩).elim
                  · have hb' := huniq cfg₁.headPos (by simpa [hj] using hjl) (by simpa [hread] using hb)
                    rcases hb' with h0 | hL | hs
                    · left
                      simpa [hj] using h0
                    · right; left
                      simpa [hj] using hL
                    · right; right
                      simpa [hj] using hs
                · have hjb' : (cfg₁.tape j).1 = SymKind.boundary := by
                    dsimp [symStepConfig] at hjb
                    rw [if_neg hj] at hjb
                    exact hjb
                  exact huniq j hjl hjb'
              · -- hc1:76/8/84/26/29/24 → s ≤ 新头
                intro hq
                dsimp [symStepConfig] at hq
                rcases hq with h | h | h | h | h | h
                · rcases (hd768 (Or.inl h)) with h5' | h76' | h8'
                  · have h5ge : s + 1 ≤ cfg₁.headPos := hc2 (by right; left; exact_mod_cast h5'.1)
                    dsimp [symStepConfig]
                    rw [h5'.2]
                    dsimp [Dir.toInt]
                    omega
                  · have hnb : step.readSym.1 ≠ SymKind.boundary := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 76 →
                            r.nextState = 76 → s.1 ≠ SymKind.boundary := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h76'.1 (by simpa [symStepConfig] using h)
                    have h76ge : s ≤ cfg₁.headPos := hc1 (by left; exact_mod_cast h76'.1)
                    have hne : cfg₁.headPos ≠ s := by
                      intro he
                      have hb : step.readSym.1 = SymKind.boundary := by simpa [hread, he] using hst
                      exact hnb hb
                    dsimp [symStepConfig]
                    rw [h76'.2]
                    dsimp [Dir.toInt]
                    omega
                  · have h8or : step.result.nextState = 8 ∨ step.result.nextState = 9 := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 8 →
                            r.moveDir = Dir.L → r.nextState = 8 ∨ r.nextState = 9 := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h8'.1 h8'.2
                    rcases h8or with h8c | h9c
                    · rw [h8c] at h
                      cases h
                    · rw [h9c] at h
                      cases h
                · rcases (hd768 (Or.inr h)) with h5' | h76' | h8'
                  · have h5ge : s + 1 ≤ cfg₁.headPos := hc2 (by right; left; exact_mod_cast h5'.1)
                    dsimp [symStepConfig]
                    rw [h5'.2]
                    dsimp [Dir.toInt]
                    omega
                  · have h76or : step.result.nextState = 76 ∨ step.result.nextState = 77 := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 76 →
                            r.moveDir = Dir.L → r.nextState = 76 ∨ r.nextState = 77 := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h76'.1 h76'.2
                    rcases h76or with h76c | h77c
                    · rw [h76c] at h
                      cases h
                    · rw [h77c] at h
                      cases h
                  · have h8ge : s ≤ cfg₁.headPos := hc1 (by right; left; exact_mod_cast h8'.1)
                    have hnb : step.readSym.1 ≠ SymKind.boundary := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 8 →
                            r.nextState = 8 → s.1 ≠ SymKind.boundary := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h8'.1 (by simpa [symStepConfig] using h)
                    have hne : cfg₁.headPos ≠ s := by
                      intro he
                      have hb : step.readSym.1 = SymKind.boundary := by simpa [hread, he] using hst
                      exact hnb hb
                    dsimp [symStepConfig]
                    rw [h8'.2]
                    dsimp [Dir.toInt]
                    omega
                · rcases (hd84 h) with h13' | h84'
                  · have h13ge : s + 1 ≤ cfg₁.headPos := hc2 (by left; exact_mod_cast h13'.1)
                    dsimp [symStepConfig]
                    rw [h13'.2]
                    dsimp [Dir.toInt]
                    omega
                  · have hnb : step.readSym.1 ≠ SymKind.boundary := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 84 →
                            r.nextState = 84 → s.1 ≠ SymKind.boundary := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h84'.1 (by simpa [symStepConfig] using h)
                    have h84ge : s ≤ cfg₁.headPos := hc1 (by right; right; left; exact_mod_cast h84'.1)
                    have hne : cfg₁.headPos ≠ s := by
                      intro he
                      have hb : step.readSym.1 = SymKind.boundary := by simpa [hread, he] using hst
                      exact hnb hb
                    dsimp [symStepConfig]
                    rw [h84'.2]
                    dsimp [Dir.toInt]
                    omega
                · -- 26:源 = 29
                  have hsrc : (cfg₁.state : ℕ) = 29 := by
                    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 26 →
                          (q : ℕ) = 29 := by
                      native_decide
                    exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                      (by rw [hread]; exact htrans) (by simpa [symStepConfig] using h)
                  have hq29 : cfg₁.state = 29 := by exact_mod_cast hsrc
                  have h29ge : s ≤ cfg₁.headPos := hc1 (by right; right; right; right; left; exact hq29)
                  have hnb : step.readSym.1 ≠ SymKind.boundary := by
                    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                        r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 29 →
                          r.nextState = 26 → s.1 ≠ SymKind.boundary := by
                      native_decide
                    exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                      (by rw [hread]; exact htrans) hsrc (by simpa [symStepConfig] using h)
                  have hne : cfg₁.headPos ≠ s := by
                    intro he
                    have hb : step.readSym.1 = SymKind.boundary := by simpa [hread, he] using hst
                    exact hnb hb
                  have hd : step.result.moveDir = Dir.L := by
                    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                        r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 29 →
                          r.nextState = 26 → r.moveDir = Dir.L := by
                      native_decide
                    exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                      (by rw [hread]; exact htrans) hsrc (by simpa [symStepConfig] using h)
                  dsimp [symStepConfig]
                  rw [hd]
                  dsimp [Dir.toInt]
                  omega
                · -- 29:源 = 24 ∨ 26 ∨ 29
                  have hsrc : (cfg₁.state : ℕ) = 24 ∨ (cfg₁.state : ℕ) = 26 ∨
                      (cfg₁.state : ℕ) = 29 := by
                    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 29 →
                          (q : ℕ) = 24 ∨ (q : ℕ) = 26 ∨ (q : ℕ) = 29 := by
                      native_decide
                    exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                      (by rw [hread]; exact htrans) (by simpa [symStepConfig] using h)
                  rcases hsrc with h24s | h26s | h29s
                  · have hq24 : cfg₁.state = 24 := by exact_mod_cast h24s
                    have h24ge : s ≤ cfg₁.headPos := hc1 (by right; right; right; right; right; exact hq24)
                    have hnb : step.readSym.1 ≠ SymKind.boundary := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 24 →
                            r.nextState = 29 → s.1 ≠ SymKind.boundary := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h24s (by simpa [symStepConfig] using h)
                    have hne : cfg₁.headPos ≠ s := by
                      intro he
                      have hb : step.readSym.1 = SymKind.boundary := by simpa [hread, he] using hst
                      exact hnb hb
                    have hd : step.result.moveDir = Dir.L := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 24 →
                            r.nextState = 29 → r.moveDir = Dir.L := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h24s (by simpa [symStepConfig] using h)
                    dsimp [symStepConfig]
                    rw [hd]
                    dsimp [Dir.toInt]
                    omega
                  · have hq26 : cfg₁.state = 26 := by exact_mod_cast h26s
                    have h26ge : s ≤ cfg₁.headPos := hc1 (by right; right; right; left; exact hq26)
                    have hnb : step.readSym.1 ≠ SymKind.boundary := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 26 →
                            r.nextState = 29 → s.1 ≠ SymKind.boundary := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h26s (by simpa [symStepConfig] using h)
                    have hne : cfg₁.headPos ≠ s := by
                      intro he
                      have hb : step.readSym.1 = SymKind.boundary := by simpa [hread, he] using hst
                      exact hnb hb
                    have hd : step.result.moveDir = Dir.L := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 26 →
                            r.nextState = 29 → r.moveDir = Dir.L := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h26s (by simpa [symStepConfig] using h)
                    dsimp [symStepConfig]
                    rw [hd]
                    dsimp [Dir.toInt]
                    omega
                  · have hq29 : cfg₁.state = 29 := by exact_mod_cast h29s
                    have h29ge : s ≤ cfg₁.headPos := hc1 (by right; right; right; right; left; exact hq29)
                    have hnb : step.readSym.1 ≠ SymKind.boundary := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 29 →
                            r.nextState = 29 → s.1 ≠ SymKind.boundary := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h29s (by simpa [symStepConfig] using h)
                    have hne : cfg₁.headPos ≠ s := by
                      intro he
                      have hb : step.readSym.1 = SymKind.boundary := by simpa [hread, he] using hst
                      exact hnb hb
                    have hd : step.result.moveDir = Dir.L := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 29 →
                            r.nextState = 29 → r.moveDir = Dir.L := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h29s (by simpa [symStepConfig] using h)
                    dsimp [symStepConfig]
                    rw [hd]
                    dsimp [Dir.toInt]
                    omega
                · -- 24:源 = 3:3 头 ≥ s+1 ⇒ 24 头 = 3 头 - 1 ≥ s
                  have hd24g : ∀ q : Fin 102, ∀ sy : Sym, ∀ r : SymTransResult,
                      r ∈ VerifierSym.transition ((q : ℕ), sy) → r.nextState = 24 →
                        (q = 3 ∧ r.moveDir = Dir.L) := by
                    native_decide
                  rcases (hd24g ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                    (by rw [hread]; exact htrans) (by simpa [symStepConfig] using h)) with ⟨h3f, h3d⟩
                  have h3ge : s + 1 ≤ cfg₁.headPos :=
                    hc2 (by right; right; right; right; simpa using congrArg Fin.val h3f)
                  dsimp [symStepConfig]
                  rw [h3d]
                  dsimp [Dir.toInt]
                  omega
              · -- hc2:13/5/4/2/3 → s+1 ≤ 新头
                intro hq
                dsimp [symStepConfig] at hq
                rcases hq with h | h | h | h | h
                · rcases (hd13 h) with h81' | h13'
                  · have hjl : cfg₁.headPos < (((encodeInstanceSym inst).length : ℕ) : ℤ) := by
                      have h81u : cfg₁.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 2 := hc81 (by exact_mod_cast h81'.1)
                      rw [r7_enc_len] at hs2 h81u ⊢
                      omega
                    have hc' : (cfg₁.tape cfg₁.headPos).1 = SymKind.consumed := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 81 →
                            r.nextState = 13 → s.1 = SymKind.consumed := by
                        native_decide
                      simpa [hread] using (hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h81'.1 (by simpa [symStepConfig] using h))
                    have hc1' := hcons cfg₁.headPos hjl hc'
                    dsimp [symStepConfig]
                    rw [h81'.2]
                    dsimp [Dir.toInt]
                    omega
                  · have h13ge : s + 1 ≤ cfg₁.headPos := hc2 (by left; exact_mod_cast h13'.1)
                    dsimp [symStepConfig]
                    rw [h13'.2]
                    dsimp [Dir.toInt]
                    omega
                · rcases (hd5 h) with h4' | h13'
                  · have h4ge : s + 1 ≤ cfg₁.headPos := hc2 (by right; right; left; exact_mod_cast h4'.1)
                    dsimp [symStepConfig]
                    rw [h4'.2]
                    dsimp [Dir.toInt]
                    omega
                  · have h13ge : s + 1 ≤ cfg₁.headPos := hc2 (by left; exact_mod_cast h13'.1)
                    dsimp [symStepConfig]
                    rw [h13'.2]
                    dsimp [Dir.toInt]
                    omega
                · rcases (hd4 h) with h51' | h28'
                  · have hnot51E : ¬ a2p_EProp inst cfg₁ := by
                      intro he
                      rcases he with ⟨s2, hs21, hs22, hst2, huniq2, _⟩
                      have hq51' : cfg₁.state = 51 := by exact_mod_cast h51'.1
                      have hF51 := hF.1 (by right; exact hq51')
                      have hb' := hF51 s2 (by rw [r7_enc_len] at hs22 ⊢; omega) hst2
                      rcases hb' with h0 | hL
                      · have hz : (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) ≤ 0 := by
                          simpa [h0] using hs21
                        have hpos : (1 : ℤ) ≤ (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) := by
                          exact_mod_cast (Nat.succ_pos (encodeBitsSym inst.target).length)
                        exact (not_le_of_gt hpos hz)
                      · have hz : s2 ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 := by
                          simpa [hL] using hs22
                        rw [r7_enc_len] at hz
                        exfalso
                        omega
                    exact (hnot51E ⟨s, hs1, hs2, hst, huniq, hc1, hc2, hc3, hc4, hc4u, hc28, hc10, hc14, hc81, hc81k, hcons, hc1u⟩).elim
                  · have h28u : cfg₁.headPos ≤ s := hc4 (by right; right; left; exact_mod_cast h28'.1)
                    have h28l : (1 : ℤ) ≤ cfg₁.headPos := hc28 (by exact_mod_cast h28'.1)
                    have h28s : cfg₁.headPos = s := by
                      have hb : step.readSym.1 = SymKind.boundary := by
                        have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                            r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 28 →
                              r.nextState = 4 → s.1 = SymKind.boundary := by
                          native_decide
                        exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                          (by rw [hread]; exact htrans) (by exact_mod_cast h28'.1) (by simpa [symStepConfig] using h)
                      have hb' := huniq cfg₁.headPos (by rw [r7_enc_len] at hs2 ⊢; omega) (by simpa [hread] using hb)
                      rcases hb' with h0 | hL | hs
                      · have hz : (1 : ℤ) ≤ (0 : ℤ) := by simpa [h0] using h28l
                        omega
                      · have hz : cfg₁.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 3 :=
                          le_trans h28u hs2
                        rw [hL] at hz
                        rw [r7_enc_len] at hz
                        exfalso
                        omega
                      · exact hs
                    dsimp [symStepConfig]
                    rw [h28'.2]
                    dsimp [Dir.toInt]
                    rw [h28s]
                · have hsrc2 : (cfg₁.state : ℕ) = 1 ∨ (cfg₁.state : ℕ) = 2 := by
                    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 2 →
                          (q : ℕ) = 1 ∨ (q : ℕ) = 2 := by
                      native_decide
                    exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                      (by rw [hread]; exact htrans) (by simpa [symStepConfig] using h)
                  rcases hsrc2 with h1' | h2'
                  · have h1u : cfg₁.headPos ≤ s := hc4 (by right; right; right; exact_mod_cast h1')
                    have h1s : cfg₁.headPos = s := by
                      have hb : step.readSym.1 = SymKind.boundary := by
                        have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                            r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 1 →
                              r.nextState = 2 → s.1 = SymKind.boundary := by
                          native_decide
                        exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                          (by rw [hread]; exact htrans) h1' (by simpa [symStepConfig] using h)
                      have hb' := huniq cfg₁.headPos (by rw [r7_enc_len] at hs2 ⊢; omega) (by simpa [hread] using hb)
                      rcases hb' with h0 | hL | hs
                      · have h1l : (1 : ℤ) ≤ cfg₁.headPos :=
                          a2p_state1_head hprev (by exact_mod_cast h1')
                        rw [h0] at h1l
                        omega
                      · rw [hL] at h1u
                        rw [r7_enc_len] at h1u
                        omega
                      · exact hs
                    have hd : step.result.moveDir = Dir.R := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 1 →
                            r.nextState = 2 → r.moveDir = Dir.R := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h1' (by simpa [symStepConfig] using h)
                    dsimp [symStepConfig]
                    rw [hd]
                    dsimp [Dir.toInt]
                    rw [h1s]
                  · have h2ge : s + 1 ≤ cfg₁.headPos := hc2 (by right; right; right; left; exact_mod_cast h2')
                    have hd : step.result.moveDir = Dir.R := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 2 →
                            r.nextState = 2 → r.moveDir = Dir.R := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h2' (by simpa [symStepConfig] using h)
                    dsimp [symStepConfig]
                    rw [hd]
                    dsimp [Dir.toInt]
                    omega
                · -- 3:源 = 2 原地 S(下界继承:3 头 = 2 头 ≥ s+1)
                  have hd3g : ∀ q : Fin 102, ∀ sy : Sym, ∀ r : SymTransResult,
                      r ∈ VerifierSym.transition ((q : ℕ), sy) → r.nextState = 3 →
                        (q = 2 ∧ r.moveDir = Dir.S) := by
                    native_decide
                  rcases (hd3g ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                    (by rw [hread]; exact htrans) (by simpa [symStepConfig] using h)) with ⟨h2f, h2d⟩
                  have h2ge : s + 1 ≤ cfg₁.headPos :=
                    hc2 (by right; right; right; left; simpa using congrArg Fin.val h2f)
                  dsimp [symStepConfig]
                  rw [h2d]
                  dsimp [Dir.toInt]
                  omega
              · -- hc3:85/77/9/27/38 → 新头 ≤ s-1
                intro hq
                dsimp [symStepConfig] at hq
                rcases hq with h | h | h | h | h
                · rcases (hd85 h) with h84' | h85'
                  · have h84ge : s ≤ cfg₁.headPos := hc1 (by right; right; left; exact_mod_cast h84'.1)
                    have hb : step.readSym.1 = SymKind.boundary := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 84 →
                            r.nextState = 85 → s.1 = SymKind.boundary := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) (by exact_mod_cast h84'.1) (by simpa [symStepConfig] using h)
                    have h84s : cfg₁.headPos = s := by
                      have h84u : cfg₁.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 2 :=
                        hc1u.1 (by right; right; left; exact_mod_cast h84'.1)
                      have hb' := huniq cfg₁.headPos (by omega) (by simpa [hread] using hb)
                      rcases hb' with h0 | hL | hs
                      · omega
                      · omega
                      · exact hs
                    dsimp [symStepConfig]
                    rw [h84'.2]
                    dsimp [Dir.toInt]
                    rw [h84s]
                    omega
                  · have h85u : cfg₁.headPos ≤ s - 1 := hc3 (by left; exact_mod_cast h85'.1)
                    have hnb : step.readSym.1 ≠ SymKind.boundary := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 85 →
                            r.nextState = 85 → s.1 ≠ SymKind.boundary := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h85'.1 (by simpa [symStepConfig] using h)
                    dsimp [symStepConfig]
                    rw [h85'.2]
                    dsimp [Dir.toInt]
                    omega
                · rcases (hd779 (Or.inl h)) with h76' | h8' | h77' | h9'
                  · have h76ge : s ≤ cfg₁.headPos := hc1 (by left; exact_mod_cast h76'.1)
                    have hb : step.readSym.1 = SymKind.boundary := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 76 →
                            r.nextState = 77 → s.1 = SymKind.boundary := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) (by exact_mod_cast h76'.1) (by simpa [symStepConfig] using h)
                    have h76s : cfg₁.headPos = s := by
                      have h76u : cfg₁.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 2 :=
                        hc1u.1 (by left; exact_mod_cast h76'.1)
                      have hb' := huniq cfg₁.headPos (by omega) (by simpa [hread] using hb)
                      rcases hb' with h0 | hL | hs
                      · omega
                      · omega
                      · exact hs
                    dsimp [symStepConfig]
                    rw [h76'.2]
                    dsimp [Dir.toInt]
                    rw [h76s]
                    omega
                  · have h8or : step.result.nextState = 8 ∨ step.result.nextState = 9 := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 8 →
                            r.moveDir = Dir.L → r.nextState = 8 ∨ r.nextState = 9 := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h8'.1 h8'.2
                    rcases h8or with h8c | h9c2
                    · rw [h8c] at h
                      cases h
                    · rw [h9c2] at h
                      cases h
                  · have h77u : cfg₁.headPos ≤ s - 1 := hc3 (by right; left; exact_mod_cast h77'.1)
                    have hnb : step.readSym.1 ≠ SymKind.boundary := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 77 →
                            r.nextState = 77 → s.1 ≠ SymKind.boundary := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h77'.1 (by simpa [symStepConfig] using h)
                    dsimp [symStepConfig]
                    rw [h77'.2]
                    dsimp [Dir.toInt]
                    omega
                  · have h9or : step.result.nextState = 9 ∨ step.result.nextState = 12 := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 9 →
                            r.moveDir = Dir.L → r.nextState = 9 ∨ r.nextState = 12 := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h9'.1 h9'.2
                    rcases h9or with h9c | h12c
                    · rw [h9c] at h
                      cases h
                    · rw [h12c] at h
                      cases h
                · rcases (hd779 (Or.inr h)) with h76' | h8' | h77' | h9'
                  · have h76or : step.result.nextState = 76 ∨ step.result.nextState = 77 := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 76 →
                            r.moveDir = Dir.L → r.nextState = 76 ∨ r.nextState = 77 := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h76'.1 h76'.2
                    rcases h76or with h77c | h76c
                    · rw [h77c] at h
                      cases h
                    · rw [h76c] at h
                      cases h
                  · have h8ge : s ≤ cfg₁.headPos := hc1 (by right; left; exact_mod_cast h8'.1)
                    have hb : step.readSym.1 = SymKind.boundary := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 8 →
                            r.nextState = 9 → s.1 = SymKind.boundary := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) (by exact_mod_cast h8'.1) (by simpa [symStepConfig] using h)
                    have h8s : cfg₁.headPos = s := by
                      have h8u : cfg₁.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 2 :=
                        hc1u.1 (by right; left; exact_mod_cast h8'.1)
                      have hb' := huniq cfg₁.headPos (by omega) (by simpa [hread] using hb)
                      rcases hb' with h0 | hL | hs
                      · omega
                      · omega
                      · exact hs
                    dsimp [symStepConfig]
                    rw [h8'.2]
                    dsimp [Dir.toInt]
                    rw [h8s]
                    omega
                  · have h77or : step.result.nextState = 77 ∨ step.result.nextState = 10 := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 77 →
                            r.moveDir = Dir.L → r.nextState = 77 ∨ r.nextState = 10 := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h77'.1 h77'.2
                    rcases h77or with h77c | h10c
                    · rw [h77c] at h
                      cases h
                    · rw [h10c] at h
                      cases h
                  · have h9u : cfg₁.headPos ≤ s - 1 := hc3 (by right; right; left; exact_mod_cast h9'.1)
                    have hnb : step.readSym.1 ≠ SymKind.boundary := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 9 →
                            r.nextState = 9 → s.1 ≠ SymKind.boundary := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h9'.1 (by simpa [symStepConfig] using h)
                    dsimp [symStepConfig]
                    rw [h9'.2]
                    dsimp [Dir.toInt]
                    omega
                · -- 27:源 = 26
                  have hsrc : (cfg₁.state : ℕ) = 26 := by
                    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 27 →
                          (q : ℕ) = 26 := by
                      native_decide
                    exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                      (by rw [hread]; exact htrans) (by simpa [symStepConfig] using h)
                  have hq26 : cfg₁.state = 26 := by exact_mod_cast hsrc
                  have h26ge : s ≤ cfg₁.headPos := hc1 (by right; right; right; left; exact hq26)
                  have hb : step.readSym.1 = SymKind.boundary := by
                    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                        r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 26 →
                          r.nextState = 27 → s.1 = SymKind.boundary := by
                      native_decide
                    exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                      (by rw [hread]; exact htrans) hsrc (by simpa [symStepConfig] using h)
                  have h26s : cfg₁.headPos = s := by
                    have h26u : cfg₁.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 2 :=
                      hc1u.1 (by right; right; right; left; exact hq26)
                    have hb' := huniq cfg₁.headPos (by omega) (by simpa [hread] using hb)
                    rcases hb' with h0 | hL | hs
                    · omega
                    · omega
                    · exact hs
                  have hd : step.result.moveDir = Dir.L := by
                    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                        r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 26 →
                          r.nextState = 27 → r.moveDir = Dir.L := by
                      native_decide
                    exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                      (by rw [hread]; exact htrans) hsrc (by simpa [symStepConfig] using h)
                  dsimp [symStepConfig]
                  rw [hd]
                  dsimp [Dir.toInt]
                  rw [h26s]
                  omega
                · -- 38:源 = 27 ∨ 38
                  have hsrc : (cfg₁.state : ℕ) = 27 ∨ (cfg₁.state : ℕ) = 38 := by
                    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 38 →
                          (q : ℕ) = 27 ∨ (q : ℕ) = 38 := by
                      native_decide
                    exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                      (by rw [hread]; exact htrans) (by simpa [symStepConfig] using h)
                  rcases hsrc with h27s | h38s
                  · have hq27 : cfg₁.state = 27 := by exact_mod_cast h27s
                    have h27u : cfg₁.headPos ≤ s - 1 := hc3 (by right; right; right; left; exact hq27)
                    have hd : step.result.moveDir = Dir.L := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 27 →
                            r.nextState = 38 → r.moveDir = Dir.L := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h27s (by simpa [symStepConfig] using h)
                    dsimp [symStepConfig]
                    rw [hd]
                    dsimp [Dir.toInt]
                    omega
                  · have hq38 : cfg₁.state = 38 := by exact_mod_cast h38s
                    have h38u : cfg₁.headPos ≤ s - 1 := hc3 (by right; right; right; right; exact hq38)
                    have hnb : step.readSym.1 ≠ SymKind.boundary := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 38 →
                            r.nextState = 38 → s.1 ≠ SymKind.boundary := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h38s (by simpa [symStepConfig] using h)
                    have hd : step.result.moveDir = Dir.L := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 38 →
                            r.nextState = 38 → r.moveDir = Dir.L := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h38s (by simpa [symStepConfig] using h)
                    dsimp [symStepConfig]
                    rw [hd]
                    dsimp [Dir.toInt]
                    omega
              · -- hc4:86/87/28/1 → 新头 ≤ s
                intro hq
                dsimp [symStepConfig] at hq
                rcases hq with h | h | h | h
                · rcases (hd86 h) with h85' | h86'
                  · have h85u : cfg₁.headPos ≤ s - 1 := hc3 (by left; exact_mod_cast h85'.1)
                    have hd : step.result.moveDir = Dir.R := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 85 →
                            r.nextState = 86 → r.moveDir = Dir.R := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) (by exact_mod_cast h85'.1) (by simpa [symStepConfig] using h)
                    dsimp [symStepConfig]
                    rw [hd]
                    dsimp [Dir.toInt]
                    omega
                  · have h86u : cfg₁.headPos ≤ s := hc4 (by left; exact_mod_cast h86'.1)
                    have hnb : step.readSym.1 ≠ SymKind.boundary := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 86 →
                            r.nextState = 86 → s.1 ≠ SymKind.boundary := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h86'.1 (by simpa [symStepConfig] using h)
                    have hne : cfg₁.headPos ≠ s := by
                      intro he
                      have hb : step.readSym.1 = SymKind.boundary := by simpa [hread, he] using hst
                      exact hnb hb
                    dsimp [symStepConfig]
                    rw [h86'.2]
                    dsimp [Dir.toInt]
                    omega
                · rcases (hd87 h) with h86' | h87'
                  · have h86u : cfg₁.headPos ≤ s := hc4 (by left; exact_mod_cast h86'.1)
                    have hd : step.result.moveDir = Dir.S := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 86 →
                            r.nextState = 87 → r.moveDir = Dir.S := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) (by exact_mod_cast h86'.1) (by simpa [symStepConfig] using h)
                    dsimp [symStepConfig]
                    rw [hd]
                    dsimp [Dir.toInt]
                    omega
                  · have h87u : cfg₁.headPos ≤ s := hc4 (by right; left; exact_mod_cast h87'.1)
                    have hnb : step.readSym.1 ≠ SymKind.boundary := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 87 →
                            r.nextState = 87 → s.1 ≠ SymKind.boundary := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h87'.1 (by simpa [symStepConfig] using h)
                    have hne : cfg₁.headPos ≠ s := by
                      intro he
                      have hb : step.readSym.1 = SymKind.boundary := by simpa [hread, he] using hst
                      exact hnb hb
                    dsimp [symStepConfig]
                    rw [h87'.2]
                    dsimp [Dir.toInt]
                    omega
                · have hsrc28 : (cfg₁.state : ℕ) = 38 ∨ (cfg₁.state : ℕ) = 28 := by
                    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 28 →
                          (q : ℕ) = 38 ∨ (q : ℕ) = 28 := by
                      native_decide
                    exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                      (by rw [hread]; exact htrans) (by simpa [symStepConfig] using h)
                  rcases hsrc28 with h38' | h28'
                  · have h38u : cfg₁.headPos ≤ s - 1 := hc3 (by right; right; right; right; exact_mod_cast h38')
                    have hd : step.result.moveDir = Dir.R := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 38 →
                            r.nextState = 28 → r.moveDir = Dir.R := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h38' (by simpa [symStepConfig] using h)
                    dsimp [symStepConfig]
                    rw [hd]
                    dsimp [Dir.toInt]
                    omega
                  · have h28u : cfg₁.headPos ≤ s := hc4 (by right; right; left; exact_mod_cast h28')
                    have hnb : step.readSym.1 ≠ SymKind.boundary := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 28 →
                            r.nextState = 28 → s.1 ≠ SymKind.boundary := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h28' (by simpa [symStepConfig] using h)
                    have hd : step.result.moveDir = Dir.R := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 28 →
                            r.nextState = 28 → r.moveDir = Dir.R := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h28' (by simpa [symStepConfig] using h)
                    have hne : cfg₁.headPos ≠ s := by
                      intro he
                      have hb : step.readSym.1 = SymKind.boundary := by simpa [hread, he] using hst
                      exact hnb hb
                    dsimp [symStepConfig]
                    rw [hd]
                    dsimp [Dir.toInt]
                    omega
                · have hsrc1 : (cfg₁.state : ℕ) = 0 ∨ (cfg₁.state : ℕ) = 1 := by
                    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 1 →
                          (q : ℕ) = 0 ∨ (q : ℕ) = 1 := by
                      native_decide
                    exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                      (by rw [hread]; exact htrans) (by simpa [symStepConfig] using h)
                  rcases hsrc1 with h0' | h1'
                  · have hd : step.result.moveDir = Dir.R := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 0 →
                            r.nextState = 1 → r.moveDir = Dir.R := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h0' (by simpa [symStepConfig] using h)
                    have h0head : cfg₁.headPos = (0 : ℤ) :=
                      a2p_state0_head hprev (by exact_mod_cast h0')
                    dsimp [symStepConfig]
                    rw [hd, h0head]
                    dsimp [Dir.toInt]
                    have hs1z : (1 : ℤ) ≤ s := le_trans (by
                      omega : (1 : ℤ) ≤ (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ)) hs1
                    omega
                  · have h1u : cfg₁.headPos ≤ s := hc4 (by right; right; right; exact_mod_cast h1')
                    have hnb : step.readSym.1 ≠ SymKind.boundary := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 1 →
                            r.nextState = 1 → s.1 ≠ SymKind.boundary := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h1' (by simpa [symStepConfig] using h)
                    have hd : step.result.moveDir = Dir.R := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 1 →
                            r.nextState = 1 → r.moveDir = Dir.R := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h1' (by simpa [symStepConfig] using h)
                    have hne : cfg₁.headPos ≠ s := by
                      intro he
                      have hb : step.readSym.1 = SymKind.boundary := by simpa [hread, he] using hst
                      exact hnb hb
                    dsimp [symStepConfig]
                    rw [hd]
                    dsimp [Dir.toInt]
                    omega
              · -- hc4u:4 → 新头 ≤ s+1
                intro hq
                dsimp [symStepConfig] at hq
                rcases (hd4 hq) with h51' | h28'
                · have hnot51E : ¬ a2p_EProp inst cfg₁ := by
                    intro he
                    rcases he with ⟨s2, hs21, hs22, hst2, huniq2, _⟩
                    have hq51' : cfg₁.state = 51 := by exact_mod_cast h51'.1
                    have hF51 := hF.1 (by right; exact hq51')
                    have hb' := hF51 s2 (by rw [r7_enc_len] at hs22 ⊢; omega) hst2
                    rcases hb' with h0 | hL
                    · have hz : (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) ≤ 0 := by
                        simpa [h0] using hs21
                      have hpos : (1 : ℤ) ≤ (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) := by
                        exact_mod_cast (Nat.succ_pos (encodeBitsSym inst.target).length)
                      exact (not_le_of_gt hpos hz)
                    · have hz : s2 ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 := by
                        simpa [hL] using hs22
                      rw [r7_enc_len] at hz
                      exfalso
                      omega
                  exact (hnot51E ⟨s, hs1, hs2, hst, huniq, hc1, hc2, hc3, hc4, hc4u, hc28, hc10, hc14, hc81, hc81k, hcons, hc1u⟩).elim
                · have h28u : cfg₁.headPos ≤ s := hc4 (by right; right; left; exact_mod_cast h28'.1)
                  have h28l : (1 : ℤ) ≤ cfg₁.headPos := hc28 (by exact_mod_cast h28'.1)
                  have h28s : cfg₁.headPos = s := by
                    have hb : step.readSym.1 = SymKind.boundary := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 28 →
                            r.nextState = 4 → s.1 = SymKind.boundary := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) (by exact_mod_cast h28'.1) (by simpa [symStepConfig] using hq)
                    have hb' := huniq cfg₁.headPos (by rw [r7_enc_len] at hs2 ⊢; omega) (by simpa [hread] using hb)
                    rcases hb' with h0 | hL | hs
                    · have hz : (1 : ℤ) ≤ (0 : ℤ) := by simpa [h0] using h28l
                      omega
                    · have hz : cfg₁.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 3 :=
                        le_trans h28u hs2
                      rw [hL] at hz
                      rw [r7_enc_len] at hz
                      exfalso
                      omega
                    · exact hs
                  dsimp [symStepConfig]
                  rw [h28'.2]
                  dsimp [Dir.toInt]
                  rw [h28s]
              · -- hc28:28 → 1 ≤ 新头
                intro hq
                dsimp [symStepConfig] at hq
                have hsrc28 : (cfg₁.state : ℕ) = 38 ∨ (cfg₁.state : ℕ) = 28 := by
                  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 28 →
                        (q : ℕ) = 38 ∨ (q : ℕ) = 28 := by
                    native_decide
                  exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                    (by rw [hread]; exact htrans) (by simpa [symStepConfig] using hq)
                rcases hsrc28 with h38' | h28'
                · have hd : step.result.moveDir = Dir.R := by
                    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                        r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 38 →
                          r.nextState = 28 → r.moveDir = Dir.R := by
                      native_decide
                    exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                      (by rw [hread]; exact htrans) h38' (by simpa [symStepConfig] using hq)
                  dsimp [symStepConfig]
                  rw [hd]
                  dsimp [Dir.toInt]
                  omega
                · have h28l : (1 : ℤ) ≤ cfg₁.headPos := hc28 (by exact_mod_cast h28')
                  have hd : step.result.moveDir = Dir.R := by
                    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                        r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 28 →
                          r.nextState = 28 → r.moveDir = Dir.R := by
                      native_decide
                    exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                      (by rw [hread]; exact htrans) h28' (by simpa [symStepConfig] using hq)
                  dsimp [symStepConfig]
                  rw [hd]
                  dsimp [Dir.toInt]
                  omega
              · -- hc10:10/11/12 → 新头 ≤ s
                intro hq
                dsimp [symStepConfig] at hq
                rcases hq with h | h | h
                · rcases (hd10 h) with h77' | h10'
                  · have hd : step.result.moveDir = Dir.R := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 77 →
                            r.nextState = 10 → r.moveDir = Dir.R := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) (by exact_mod_cast h77'.1) (by simpa [symStepConfig] using h)
                    have h77u : cfg₁.headPos ≤ s - 1 := hc3 (by right; left; exact_mod_cast h77'.1)
                    dsimp [symStepConfig]
                    rw [hd]
                    dsimp [Dir.toInt]
                    omega
                  · have h10u : cfg₁.headPos ≤ s := hc10 (by left; exact_mod_cast h10'.1)
                    have hnb : step.readSym.1 ≠ SymKind.boundary := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 10 →
                            r.nextState = 10 → s.1 ≠ SymKind.boundary := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h10'.1 (by simpa [symStepConfig] using h)
                    have hne : cfg₁.headPos ≠ s := by
                      intro he
                      have hb : step.readSym.1 = SymKind.boundary := by simpa [hread, he] using hst
                      exact hnb hb
                    dsimp [symStepConfig]
                    rw [h10'.2]
                    dsimp [Dir.toInt]
                    omega
                · have ⟨h10', hS11⟩ := hd11 h
                  have h10u : cfg₁.headPos ≤ s := hc10 (by left; exact_mod_cast h10')
                  dsimp [symStepConfig]
                  rw [hS11]
                  dsimp [Dir.toInt]
                  omega
                · rcases (hd12 h) with h9' | h12'
                  · have hd : step.result.moveDir = Dir.R := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 9 →
                            r.nextState = 12 → r.moveDir = Dir.R := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) (by exact_mod_cast h9'.1) (by simpa [symStepConfig] using h)
                    have h9u : cfg₁.headPos ≤ s - 1 := hc3 (by right; right; left; exact_mod_cast h9'.1)
                    dsimp [symStepConfig]
                    rw [hd]
                    dsimp [Dir.toInt]
                    omega
                  · have h12u : cfg₁.headPos ≤ s := hc10 (by right; right; exact_mod_cast h12'.1)
                    have hnb : step.readSym.1 ≠ SymKind.boundary := by
                      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 12 →
                            r.nextState = 12 → s.1 ≠ SymKind.boundary := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) h12'.1 (by simpa [symStepConfig] using h)
                    have hne : cfg₁.headPos ≠ s := by
                      intro he
                      have hb : step.readSym.1 = SymKind.boundary := by simpa [hread, he] using hst
                      exact hnb hb
                    dsimp [symStepConfig]
                    rw [h12'.2]
                    dsimp [Dir.toInt]
                    omega
              · -- hc14:14 → 新头 ≤ s
                intro hq
                dsimp [symStepConfig] at hq
                rcases (hd14 hq) with h11' | h14'
                · have h11u : cfg₁.headPos ≤ s := hc10 (by right; left; exact_mod_cast h11'.1)
                  have hnb : step.readSym.1 ≠ SymKind.boundary := by
                    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                        r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 11 →
                          r.nextState = 14 → s.1 ≠ SymKind.boundary := by
                      native_decide
                    exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                      (by rw [hread]; exact htrans) (by exact_mod_cast h11'.1) (by simpa [symStepConfig] using hq)
                  have h11s : cfg₁.headPos ≤ s - 1 := by
                    by_contra hgt
                    have hh : cfg₁.headPos = s := by omega
                    have hb : step.readSym.1 = SymKind.boundary := by simpa [hread, hh] using hst
                    exact hnb hb
                  dsimp [symStepConfig]
                  rw [h11'.2]
                  dsimp [Dir.toInt]
                  omega
                · have h14u : cfg₁.headPos ≤ s := hc14 (by exact_mod_cast h14'.1)
                  have hnb : step.readSym.1 ≠ SymKind.boundary := by
                    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                        r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 14 →
                          r.nextState = 14 → s.1 ≠ SymKind.boundary := by
                      native_decide
                    exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                      (by rw [hread]; exact htrans) h14'.1 (by simpa [symStepConfig] using hq)
                  have hne : cfg₁.headPos ≠ s := by
                    intro he
                    have hb : step.readSym.1 = SymKind.boundary := by simpa [hread, he] using hst
                    exact hnb hb
                  dsimp [symStepConfig]
                  rw [h14'.2]
                  dsimp [Dir.toInt]
                  omega
              · -- hc81:81 → 新头 ≤ L-2
                intro hq
                dsimp [symStepConfig] at hq
                rcases (hd81 hq) with ⟨hsrc, hR81⟩
                rcases hsrc with h11s | h12s | h14s | h81s
                · have h11u : cfg₁.headPos ≤ s := hc10 (by right; left; exact_mod_cast h11s)
                  dsimp [symStepConfig]
                  rw [hR81]
                  dsimp [Dir.toInt]
                  omega
                · have h12u : cfg₁.headPos ≤ s := hc10 (by right; right; exact_mod_cast h12s)
                  dsimp [symStepConfig]
                  rw [hR81]
                  dsimp [Dir.toInt]
                  omega
                · have h14u : cfg₁.headPos ≤ s := hc14 (by exact_mod_cast h14s)
                  dsimp [symStepConfig]
                  rw [hR81]
                  dsimp [Dir.toInt]
                  omega
                · have hw := hc81k
                  rw [a2p_walk81] at hw
                  obtain ⟨c, hc_le, hc_leL, hc_cons⟩ := hw (by right; right; right; right; right; right; right; right; exact_mod_cast h81s)
                  have hrd : step.readSym.1 ≠ SymKind.consumed := by
                    have hbb : ∀ q : Fin 102, ∀ sy : Sym, ∀ r : SymTransResult,
                        r ∈ VerifierSym.transition ((q : ℕ), sy) → r.nextState = (81 : Fin 102) →
                          sy.1 ≠ SymKind.consumed := by
                      native_decide
                    exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                      (by rw [hread]; exact htrans) (by simpa [symStepConfig] using hq)
                  have hne : cfg₁.headPos ≠ c := by
                    intro he
                    exact hrd (by rw [hread, he]; exact hc_cons)
                  dsimp [symStepConfig]
                  rw [hR81]
                  dsimp [Dir.toInt]
                  omega
              · -- a2p_walk81:S-链传递(基例:源 5 写 consumed 于 5头,取 c := 5头;其余继承 IH 停点)
                rw [a2p_walk81]
                intro hq
                dsimp [symStepConfig] at hq
                have hbbSrc : ∀ q : Fin 102, ∀ sy : Sym, ∀ r : SymTransResult,
                    r ∈ VerifierSym.transition ((q : ℕ), sy) →
                      ((r.nextState : ℕ) = 76 ∨ (r.nextState : ℕ) = 8 ∨ (r.nextState : ℕ) = 77 ∨
                        (r.nextState : ℕ) = 9 ∨ (r.nextState : ℕ) = 10 ∨ (r.nextState : ℕ) = 11 ∨
                        (r.nextState : ℕ) = 12 ∨ (r.nextState : ℕ) = 14 ∨ (r.nextState : ℕ) = 81) →
                        ((q : ℕ) = 5 ∧ r.moveDir = Dir.L ∧
                            ((r.nextState : ℕ) = 76 ∨ (r.nextState : ℕ) = 8)) ∨
                          ((q : ℕ) = 76 ∨ (q : ℕ) = 8 ∨ (q : ℕ) = 77 ∨ (q : ℕ) = 9 ∨ (q : ℕ) = 10 ∨
                            (q : ℕ) = 11 ∨ (q : ℕ) = 12 ∨ (q : ℕ) = 14 ∨ (q : ℕ) = 81) := by
                  native_decide
                have hsrc := hbbSrc ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                  (by rw [hread]; exact htrans) hq
                rcases hsrc with ⟨h5, hdir5, _⟩ | hS
                · -- 基例:5 → 76/8,写 consumed 于 5头
                  have h5n : cfg₁.state = 5 := by simpa using h5
                  refine ⟨cfg₁.headPos, ?_, ?_, ?_⟩
                  · dsimp [symStepConfig]
                    rw [hdir5]
                    dsimp [Dir.toInt]
                    omega
                  · have h1 : cfg₁.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 :=
                      hi5u (by simpa using h5n)
                    have hnb : step.readSym.1 ≠ SymKind.boundary := by
                      have hbb : ∀ q : Fin 102, ∀ sy : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), sy) → (q : ℕ) = 5 →
                            r.nextState ≠ 101 → sy.1 ≠ SymKind.boundary := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by simpa [hread] using htrans) (by simpa using h5n) hne
                    have hneL : cfg₁.headPos ≠ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 := by
                      intro he
                      exact hnb (by simpa [hread, he] using hbL)
                    omega
                  · have hw5 : step.result.writeSym.1 = SymKind.consumed := by
                      have hbb : ∀ q : Fin 102, ∀ sy : Sym, ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition ((q : ℕ), sy) → (q : ℕ) = 5 →
                            r.nextState ≠ 101 → r.writeSym.1 = SymKind.consumed := by
                        native_decide
                      exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by simpa [hread] using htrans) (by simpa using h5n) hne
                    simpa [symStepConfig] using hw5
                · -- 传递:源 ∈ S,继承 IH 停点 c
                  have hSn : cfg₁.state = 76 ∨ cfg₁.state = 8 ∨ cfg₁.state = 77 ∨ cfg₁.state = 9 ∨
                      cfg₁.state = 10 ∨ cfg₁.state = 11 ∨ cfg₁.state = 12 ∨ cfg₁.state = 14 ∨
                      cfg₁.state = 81 := by
                    simpa using hS
                  have hwS := hc81k
                  rw [a2p_walk81] at hwS
                  obtain ⟨c, hle, hleL, hc_cons⟩ := hwS hSn
                  have hbb : ∀ q : Fin 102, ∀ sy : Sym, ∀ r : SymTransResult,
                      r ∈ VerifierSym.transition ((q : ℕ), sy) →
                        ((q : ℕ) = 76 ∨ (q : ℕ) = 8 ∨ (q : ℕ) = 77 ∨ (q : ℕ) = 9 ∨ (q : ℕ) = 10 ∨
                          (q : ℕ) = 11 ∨ (q : ℕ) = 12 ∨ (q : ℕ) = 14 ∨ (q : ℕ) = 81) →
                          sy.1 = SymKind.consumed → r.nextState ≠ 13 → r.nextState ≠ 101 →
                            ((q : ℕ) = 76 ∨ (q : ℕ) = 8) ∧ r.moveDir = Dir.L ∧ r.writeSym.1 = sy.1 := by
                    native_decide
                  have h13 : step.result.nextState ≠ 13 := by
                    intro hc13
                    rw [hc13] at hq
                    exact absurd hq (by decide)
                  refine ⟨c, ?_, hleL, ?_⟩
                  · by_cases hrc : step.readSym.1 = SymKind.consumed
                    · obtain ⟨_, hdir, _⟩ := hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) (by simpa using hSn) hrc h13 hne
                      dsimp [symStepConfig]
                      rw [hdir]
                      dsimp [Dir.toInt]
                      omega
                    · have hce : cfg₁.headPos ≠ c := fun he => hrc (by rw [hread, he]; exact hc_cons)
                      dsimp [symStepConfig]
                      cases step.result.moveDir <;> dsimp [Dir.toInt] <;> omega
                  · by_cases hrc : step.readSym.1 = SymKind.consumed
                    · obtain ⟨_, _, hws⟩ := hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                        (by rw [hread]; exact htrans) (by simpa using hSn) hrc h13 hne
                      by_cases hce : c = cfg₁.headPos
                      · simpa [symStepConfig, hce] using hws.trans hrc
                      · simpa [symStepConfig, hce] using hc_cons
                    · have hne' : cfg₁.headPos ≠ c := fun he => hrc (by rw [hread, he]; exact hc_cons)
                      have hce : ¬ (c = cfg₁.headPos) := fun h => hne' h.symm
                      simpa [symStepConfig, hce] using hc_cons
              · -- hcons:consumed 位 ∈ [s+1, L-2]
                intro j hjl hjc
                by_cases hw : cfg₁.headPos = j
                · have hwj : (step.result.writeSym).1 = SymKind.consumed := by
                    dsimp [symStepConfig] at hjc
                    simpa [hw] using hjc
                  rcases a2p_write_cons_src ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                      (by simpa [hread] using htrans) hne hwj with hq5 | hrc
                  · have h5ge : s + 1 ≤ cfg₁.headPos :=
                      hc2 (by right; left; simpa using hq5)
                    have h5le : cfg₁.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 2 := by
                      have h1 : cfg₁.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 := hi5u (by simpa using hq5)
                      have hnb : step.readSym.1 ≠ SymKind.boundary := by
                        have hbb : ∀ q : Fin 102, ∀ sy : Sym, ∀ r : SymTransResult,
                            r ∈ VerifierSym.transition ((q : ℕ), sy) → (q : ℕ) = 5 →
                              r.nextState ≠ 101 → sy.1 ≠ SymKind.boundary := by
                          native_decide
                        exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                          (by simpa [hread] using htrans) (by simpa using hq5) hne
                      have hneL : cfg₁.headPos ≠ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 := by
                        intro he
                        exact hnb (by simpa [hread, he] using hbL)
                      omega
                    rw [← hw]
                    exact ⟨h5ge, h5le⟩
                  · have hrc' : (cfg₁.tape cfg₁.headPos).1 = SymKind.consumed := by
                      simpa [hread] using hrc
                    have hih := hcons cfg₁.headPos (by rw [hw]; exact hjl) hrc'
                    rw [← hw]
                    exact hih
                · have hjc₁ : (cfg₁.tape j).1 = SymKind.consumed := by
                    dsimp [symStepConfig] at hjc
                    simpa [if_neg (Ne.symm hw)] using hjc
                  exact hcons j hjl hjc₁
              · -- hc1u:(76/8/84/26/29 → 头 ≤ L-2) ∧ (2/3/24 → 头 ≤ L-1)(上界:恒在中分界符右侧)
                have hd768ug : ∀ q : Fin 102, ∀ sy : Sym, ∀ r : SymTransResult,
                    r ∈ VerifierSym.transition ((q : ℕ), sy) →
                      (r.nextState = 76 ∨ r.nextState = 8) →
                        (q = 5 ∧ r.moveDir = Dir.L) ∨ (q = 76 ∧ r.moveDir = Dir.L) ∨
                          (q = 8 ∧ r.moveDir = Dir.L) := by
                  native_decide
                have hd84ug : ∀ q : Fin 102, ∀ sy : Sym, ∀ r : SymTransResult,
                    r ∈ VerifierSym.transition ((q : ℕ), sy) → r.nextState = 84 →
                      (q = 13 ∧ r.moveDir = Dir.L) ∨ (q = 84 ∧ r.moveDir = Dir.L) := by
                  native_decide
                have hd26g : ∀ q : Fin 102, ∀ sy : Sym, ∀ r : SymTransResult,
                    r ∈ VerifierSym.transition ((q : ℕ), sy) → r.nextState = 26 →
                      (q = 29 ∧ r.moveDir = Dir.L) ∨ (q = 26 ∧ r.moveDir = Dir.L) := by
                  native_decide
                have hd29g : ∀ q : Fin 102, ∀ sy : Sym, ∀ r : SymTransResult,
                    r ∈ VerifierSym.transition ((q : ℕ), sy) → r.nextState = 29 →
                      (q = 24 ∧ r.moveDir = Dir.L) ∨ (q = 26 ∧ r.moveDir = Dir.L) ∨
                        (q = 29 ∧ r.moveDir = Dir.L) := by
                  native_decide
                refine ⟨?_, ?_⟩
                · intro hq
                  dsimp [symStepConfig] at hq
                  rcases hq with h | h | h | h | h
                  · rcases (hd768ug ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                      (by rw [hread]; exact htrans) (Or.inl h)) with h5' | h76' | h8'
                    · have h5u := hi5u (by simpa using congrArg Fin.val h5'.1)
                      dsimp [symStepConfig]
                      rw [h5'.2]
                      dsimp [Dir.toInt]
                      omega
                    · have h76u := hc1u.1 (by left; simpa using congrArg Fin.val h76'.1)
                      dsimp [symStepConfig]
                      rw [h76'.2]
                      dsimp [Dir.toInt]
                      omega
                    · have h8or : step.result.nextState = 8 ∨ step.result.nextState = 9 := by
                        have hbb : ∀ q : Fin 102, ∀ sy : Sym, ∀ r : SymTransResult,
                            r ∈ VerifierSym.transition ((q : ℕ), sy) → (q : ℕ) = 8 →
                              r.moveDir = Dir.L → r.nextState = 8 ∨ r.nextState = 9 := by
                          native_decide
                        exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                          (by rw [hread]; exact htrans) (by simpa using congrArg Fin.val h8'.1) h8'.2
                      rcases h8or with h8c | h9c
                      · rw [h8c] at h
                        cases h
                      · rw [h9c] at h
                        cases h
                  · rcases (hd768ug ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                      (by rw [hread]; exact htrans) (Or.inr h)) with h5' | h76' | h8'
                    · have h5u := hi5u (by simpa using congrArg Fin.val h5'.1)
                      dsimp [symStepConfig]
                      rw [h5'.2]
                      dsimp [Dir.toInt]
                      omega
                    · have h76or : step.result.nextState = 76 ∨ step.result.nextState = 77 := by
                        have hbb : ∀ q : Fin 102, ∀ sy : Sym, ∀ r : SymTransResult,
                            r ∈ VerifierSym.transition ((q : ℕ), sy) → (q : ℕ) = 76 →
                              r.moveDir = Dir.L → r.nextState = 76 ∨ r.nextState = 77 := by
                          native_decide
                        exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                          (by rw [hread]; exact htrans) (by simpa using congrArg Fin.val h76'.1) h76'.2
                      rcases h76or with h76c | h77c
                      · rw [h76c] at h
                        cases h
                      · rw [h77c] at h
                        cases h
                    · have h8u := hc1u.1 (by right; left; simpa using congrArg Fin.val h8'.1)
                      dsimp [symStepConfig]
                      rw [h8'.2]
                      dsimp [Dir.toInt]
                      omega
                  · rcases (hd84ug ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                      (by rw [hread]; exact htrans) h) with h13' | h84'
                    · have h13u := hi13u (by simpa using congrArg Fin.val h13'.1)
                      dsimp [symStepConfig]
                      rw [h13'.2]
                      dsimp [Dir.toInt]
                      omega
                    · have h84u := hc1u.1 (by right; right; left; simpa using congrArg Fin.val h84'.1)
                      dsimp [symStepConfig]
                      rw [h84'.2]
                      dsimp [Dir.toInt]
                      omega
                  · rcases (hd26g ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                      (by rw [hread]; exact htrans) h) with h29' | h26'
                    · have h29u := hc1u.1 (by right; right; right; right; simpa using congrArg Fin.val h29'.1)
                      dsimp [symStepConfig]
                      rw [h29'.2]
                      dsimp [Dir.toInt]
                      omega
                    · have h26u := hc1u.1 (by right; right; right; left; simpa using congrArg Fin.val h26'.1)
                      dsimp [symStepConfig]
                      rw [h26'.2]
                      dsimp [Dir.toInt]
                      omega
                  · rcases (hd29g ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                      (by rw [hread]; exact htrans) h) with h24' | h26' | h29'
                    · have h24u := hc1u.2 (by right; right; simpa using congrArg Fin.val h24'.1)
                      dsimp [symStepConfig]
                      rw [h24'.2]
                      dsimp [Dir.toInt]
                      omega
                    · have h26u := hc1u.1 (by right; right; right; left; simpa using congrArg Fin.val h26'.1)
                      dsimp [symStepConfig]
                      rw [h26'.2]
                      dsimp [Dir.toInt]
                      omega
                    · have h29u := hc1u.1 (by right; right; right; right; simpa using congrArg Fin.val h29'.1)
                      dsimp [symStepConfig]
                      rw [h29'.2]
                      dsimp [Dir.toInt]
                      omega
                · -- 2/3/24 → 头 ≤ L-1(扫入态:读 data 者不落在 L-1)
                  have hd2g : ∀ q : Fin 102, ∀ sy : Sym, ∀ r : SymTransResult,
                      r ∈ VerifierSym.transition ((q : ℕ), sy) → r.nextState = 2 →
                        (q = 1 ∧ r.moveDir = Dir.R) ∨ (q = 2 ∧ r.moveDir = Dir.R) := by
                    native_decide
                  have hd2nb : ∀ q : Fin 102, ∀ sy : Sym, ∀ r : SymTransResult,
                      r ∈ VerifierSym.transition ((q : ℕ), sy) → r.nextState = 2 →
                        (q : ℕ) = 2 → sy.1 ≠ SymKind.boundary := by
                    native_decide
                  have hd3g : ∀ q : Fin 102, ∀ sy : Sym, ∀ r : SymTransResult,
                      r ∈ VerifierSym.transition ((q : ℕ), sy) → r.nextState = 3 →
                        (q = 2 ∧ r.moveDir = Dir.S) := by
                    native_decide
                  have hd24g : ∀ q : Fin 102, ∀ sy : Sym, ∀ r : SymTransResult,
                      r ∈ VerifierSym.transition ((q : ℕ), sy) → r.nextState = 24 →
                        (q = 3 ∧ r.moveDir = Dir.L) := by
                    native_decide
                  intro hq2
                  dsimp [symStepConfig] at hq2
                  rcases hq2 with h2 | h3 | h24
                  · -- 2 ← 1(R):1 头 ≤ s ≤ L-3;2 ← 2(R):读 data ⇒ 头 ≠ L-1
                    rcases (hd2g ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                      (by rw [hread]; exact htrans) (by simpa [symStepConfig] using h2))
                      with ⟨hqf, hqd⟩ | ⟨hqf, hqd⟩
                    · have h1le : cfg₁.headPos ≤ s :=
                        hc4 (by right; right; right; simpa using congrArg Fin.val hqf)
                      dsimp [symStepConfig]
                      rw [hqd]
                      dsimp [Dir.toInt]
                      omega
                    · have h2le : cfg₁.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 :=
                        hc1u.2 (by left; simpa using congrArg Fin.val hqf)
                      have hd2nbl : step.readSym.1 ≠ SymKind.boundary :=
                        hd2nb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                          (by rw [hread]; exact htrans) (by simpa [symStepConfig] using h2)
                          (by simpa using congrArg Fin.val hqf)
                      have hneL : cfg₁.headPos ≠ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 := by
                        intro heL
                        exact hd2nbl (by simpa [hread, heL] using hbL)
                      dsimp [symStepConfig]
                      rw [hqd]
                      dsimp [Dir.toInt]
                      omega
                  · -- 3 ← 2(S):头不变
                    rcases (hd3g ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                      (by rw [hread]; exact htrans) (by simpa [symStepConfig] using h3))
                      with ⟨hqf, hqd⟩
                    have h2le : cfg₁.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 :=
                      hc1u.2 (by left; simpa using congrArg Fin.val hqf)
                    dsimp [symStepConfig]
                    rw [hqd]
                    dsimp [Dir.toInt]
                    omega
                  · -- 24 ← 3(L):3 头 ≤ L-1 ⇒ 新头 ≤ L-2
                    rcases (hd24g ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                      (by rw [hread]; exact htrans) (by simpa [symStepConfig] using h24))
                      with ⟨hqf, hqd⟩
                    have h3le : cfg₁.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 :=
                      hc1u.2 (by right; left; simpa using congrArg Fin.val hqf)
                    dsimp [symStepConfig]
                    rw [hqd]
                    dsimp [Dir.toInt]
                    omega
                )

      · -- F:21/51 → boundary 格 ⊆ {0, L-1}
        refine ⟨?_, ?_⟩
        · -- (1) 21/51:boundary 格 ⊆ {0, L-1}(原块)
          intro hFnew
          dsimp [symStepConfig] at hFnew
          rcases hFnew with h21n | h51n
          · -- 新态 21:旧 20(读 #₀)或 21 自环(扫 data)
            have hsrc : (cfg₁.state : ℕ) = 20 ∨ (cfg₁.state : ℕ) = 21 := by
              have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 21 →
                    (q : ℕ) = 20 ∨ (q : ℕ) = 21 := by
                native_decide
              exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                (by simpa [hread] using htrans) h21n
            cases hsrc with
            | inl hsrc20 =>
              -- 旧 20:20 态 boundary ⊆ {0, L-1, s}(ih huniq)
              have hq20 : cfg₁.state = 20 := by exact_mod_cast hsrc20
              have hnex20 : ¬ (cfg₁.state = 21 ∨ cfg₁.state = 51 ∨
                  cfg₁.state = 22 ∨ cfg₁.state = 23 ∨ cfg₁.state = 100 ∨ cfg₁.state = 101) := by
                intro hx
                rcases hx with a | b | c | d | e | f <;> omega
              have hsE20 : a2p_EProp inst cfg₁ := hE.resolve_left hnex20
              rcases hsE20 with ⟨s, hs1, hs2, hst, huniq, hc1, hc2, hc3, hc4, hc4u, hc28, hc10, hc14, hc81, hc81k, hcons, hc1u⟩
              intro j hjl hjb
              by_cases hj : j = cfg₁.headPos
              · -- 写格 = 20头 = s:20 写 data0:boundary 不成立
                have hw : step.result.writeSym.1 = SymKind.data0 := by
                  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                      r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 20 →
                        r.nextState = 21 → r.writeSym.1 = SymKind.data0 := by
                    native_decide
                  exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                    (by simpa [hread] using htrans) hsrc20 h21n
                dsimp [symStepConfig] at hjb
                rw [hj] at hjb
                simp at hjb
                rw [hw] at hjb
                cases hjb
              · have hjb' : (cfg₁.tape j).1 = SymKind.boundary := by
                  dsimp [symStepConfig] at hjb
                  rw [if_neg hj] at hjb
                  exact hjb
                have hb' := huniq j hjl hjb'
                rcases hb' with h0 | hL | hs
                · left
                  exact h0
                · right
                  exact hL
                · have hb20 : step.readSym.1 = SymKind.boundary := by
                    have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                        r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 20 →
                          r.nextState = 21 → s.1 = SymKind.boundary := by
                      native_decide
                    exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                      (by simpa [hread] using htrans) hsrc20 h21n
                  have h20s : cfg₁.headPos = s := by
                    have h20u := (hi20 hq20).2
                    have hb := huniq cfg₁.headPos (by
                      rw [r7_enc_len] at h20u ⊢
                      omega) (by simpa [hread] using hb20)
                    rcases hb with h0 | hL | hhs
                    · have h20l := (hi20 hq20).1
                      rw [h0] at h20l
                      omega
                    · rw [hL] at h20u
                      omega
                    · exact hhs
                  rw [h20s] at hj
                  exact (hj hs).elim
            | inr hsrc21 =>
              -- 旧 21(自环):21 写 data0@头,ih hF 给旧 21 态
              have hq21 : cfg₁.state = 21 := by exact_mod_cast hsrc21
              have hF21 := hF.1 (by left; exact hq21)
              intro j hjl hjb
              by_cases hj : j = cfg₁.headPos
              · have hw : step.result.writeSym.1 = SymKind.data0 := by
                  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                      r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 21 →
                        r.nextState = 21 → r.writeSym.1 = SymKind.data0 := by
                    native_decide
                  exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                    (by simpa [hread] using htrans) hsrc21 h21n
                dsimp [symStepConfig] at hjb
                rw [hj] at hjb
                simp at hjb
                rw [hw] at hjb
                cases hjb
              · have hjb' : (cfg₁.tape j).1 = SymKind.boundary := by
                  dsimp [symStepConfig] at hjb
                  rw [if_neg hj] at hjb
                  exact hjb
                exact hF21 j hjl hjb'
          · -- 新态 51:旧 21:21 态 boundary ⊆ {0, L-1}(ih hF)
            have hsrc : (cfg₁.state : ℕ) = 21 := by
              have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 51 → (q : ℕ) = 21 := by
                native_decide
              exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                (by simpa [hread] using htrans) h51n
            have hq21 : cfg₁.state = 21 := by exact_mod_cast hsrc
            have hF21 := hF.1 (by left; exact hq21)
            intro j hjl hjb
            have hjb' : (cfg₁.tape j).1 = SymKind.boundary := by
              dsimp [symStepConfig] at hjb
              by_cases hj : j = cfg₁.headPos
              · have hw : step.result.writeSym.1 = SymKind.sel ∨
                    step.result.writeSym.1 = SymKind.nosel := by
                  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                      r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 21 →
                        r.nextState = 51 → r.writeSym.1 = SymKind.sel ∨ r.writeSym.1 = SymKind.nosel := by
                    native_decide
                  exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                    (by simpa [hread] using htrans) hsrc h51n
                rw [hj] at hjb
                simp at hjb
                rcases hw with hw | hw
                · rw [hw] at hjb
                  cases hjb
                · rw [hw] at hjb
                  cases hjb
              · rw [if_neg hj] at hjb
                exact hjb
            exact hF21 j hjl hjb'

        · -- (2) 清扫集合 {20,21,22,23,51}:consumed j ⇒ 头 ≤ j(松式)
          intro hq j hjl hjc
          have hqT : step.result.nextState = 20 ∨ step.result.nextState = 21 ∨
              step.result.nextState = 22 ∨ step.result.nextState = 23 ∨
              step.result.nextState = 51 := hq
          have hsrc : (cfg₁.state : ℕ) = 20 ∨ (cfg₁.state : ℕ) = 21 ∨
              (cfg₁.state : ℕ) = 22 ∨ (cfg₁.state : ℕ) = 23 ∨
              (cfg₁.state : ℕ) = 4 ∨ (cfg₁.state : ℕ) = 87 := by
            have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) →
                  (r.nextState = 20 ∨ r.nextState = 21 ∨ r.nextState = 22 ∨
                    r.nextState = 23 ∨ r.nextState = 51) →
                  ((q : ℕ) = 20 ∨ (q : ℕ) = 21 ∨ (q : ℕ) = 22 ∨ (q : ℕ) = 23 ∨
                    (q : ℕ) = 4 ∨ (q : ℕ) = 87) := by native_decide
            exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
              (by simpa [hread] using htrans) hqT
          have hwne : step.result.writeSym.1 ≠ SymKind.consumed := by
            have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) →
                  (r.nextState = 20 ∨ r.nextState = 21 ∨ r.nextState = 22 ∨
                    r.nextState = 23 ∨ r.nextState = 51) →
                  r.writeSym.1 ≠ SymKind.consumed := by native_decide
            exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
              (by simpa [hread] using htrans) hqT
          have hjne : j ≠ cfg₁.headPos := by
            intro hje
            have hc : step.result.writeSym.1 = SymKind.consumed := by
              simp only [symStepConfig] at hjc
              rw [hje] at hjc
              simpa using hjc
            exact hwne hc
          have hjc₁ : (cfg₁.tape j).1 = SymKind.consumed := by
            simp only [symStepConfig] at hjc
            rw [if_neg hjne] at hjc
            exact hjc
          have hmv1 : step.result.moveDir.toInt ≤ 1 := by
            have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) → r.moveDir.toInt ≤ 1 := by native_decide
            exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
              (by simpa [hread] using htrans)
          rw [symStepConfig]
          show cfg₁.headPos + step.result.moveDir.toInt ≤ j
          rcases hsrc with h20 | h21 | h22 | h23 | h4 | h87
          · have hz := hF.2 (by left; exact_mod_cast h20) j hjl hjc₁
            have hlt : cfg₁.headPos < j := lt_of_le_of_ne hz (Ne.symm hjne)
            omega
          · have hz := hF.2 (by right; left; exact_mod_cast h21) j hjl hjc₁
            have hlt : cfg₁.headPos < j := lt_of_le_of_ne hz (Ne.symm hjne)
            omega
          · have hz := hF.2 (by right; right; left; exact_mod_cast h22) j hjl hjc₁
            have hlt : cfg₁.headPos < j := lt_of_le_of_ne hz (Ne.symm hjne)
            omega
          · have hz := hF.2 (by right; right; right; left; exact_mod_cast h23) j hjl hjc₁
            have hlt : cfg₁.headPos < j := lt_of_le_of_ne hz (Ne.symm hjne)
            omega
          · -- 源 4(行 441:4,nosel → 20 data0 L):头_20 = 4头-1,4头 = s+1
            have hnex : ¬ (cfg₁.state = 21 ∨ cfg₁.state = 51 ∨ cfg₁.state = 22 ∨
                cfg₁.state = 23 ∨ cfg₁.state = 100 ∨ cfg₁.state = 101) := by
              intro hx
              rcases hx with a | b | c | d | e | f <;> omega
            rcases hE.resolve_left hnex with
              ⟨s, hs1, hs2, hst, huniq, hc1, hc2, hc3, hc4, hc4u, hc28, hc10, hc14,
                hc81, hc81k, hcons, hc1u⟩
            have h4h : cfg₁.headPos = s + 1 :=
              le_antisymm (hc4u h4) (hc2 (by right; right; left; exact h4))
            have hz := hcons j hjl hjc₁
            have hnext : step.result.nextState = 20 := by
              have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 4 →
                (r.nextState = 20 ∨ r.nextState = 21 ∨ r.nextState = 22 ∨
                  r.nextState = 23 ∨ r.nextState = 51) → r.nextState = 20 := by native_decide
              exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                (by simpa [hread] using htrans) h4 hqT
            have hmv4 : step.result.moveDir.toInt = -1 := by
              have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 4 →
                    r.nextState = 20 → r.moveDir.toInt = -1 := by native_decide
              exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                (by simpa [hread] using htrans) h4 hnext
            omega
          · -- 源 87(行 506:87,boundary → 20 s S):87头 = s(934-935 + huniq + 1 ≤ 头)
            have hnex : ¬ (cfg₁.state = 21 ∨ cfg₁.state = 51 ∨ cfg₁.state = 22 ∨
                cfg₁.state = 23 ∨ cfg₁.state = 100 ∨ cfg₁.state = 101) := by
              intro hx
              rcases hx with a | b | c | d | e | f <;> omega
            rcases hE.resolve_left hnex with
              ⟨s, hs1, hs2, hst, huniq, hc1, hc2, hc3, hc4, hc4u, hc28, hc10, hc14,
                hc81, hc81k, hcons, hc1u⟩
            have hnext : step.result.nextState = 20 := by
              have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 87 →
                (r.nextState = 20 ∨ r.nextState = 21 ∨ r.nextState = 22 ∨
                  r.nextState = 23 ∨ r.nextState = 51) → r.nextState = 20 := by native_decide
              exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                (by simpa [hread] using htrans) h87 hqT
            have h87b : step.readSym.1 = SymKind.boundary := by
              have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 87 →
                    r.nextState = 20 → s.1 = SymKind.boundary := by native_decide
              exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
                (by simpa [hread] using htrans) h87 hnext
            have h87h : cfg₁.headPos = s := by
              have hle := hc4 (by right; left; exact h87)
              have hb := huniq cfg₁.headPos (by omega) (by simpa [hread] using h87b)
              rcases hb with h0 | hL | hs
              · have h1 := hi87 (by exact_mod_cast h87)
                omega
              · omega
              · exact hs
            have hz := hcons j hjl hjc₁
            omega
      · -- 22 态头 = L-1:新态 = 22 → 旧 21 读 #₁@L-1
        intro h22n
        dsimp [symStepConfig] at h22n
        have hsrc : (cfg₁.state : ℕ) = 21 := by
          have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
              r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 22 →
                (q : ℕ) = 21 := by
            native_decide
          exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
            (by rw [hread]; exact htrans) (by simpa [symStepConfig] using h22n)
        have hq21 : cfg₁.state = 21 := by exact_mod_cast hsrc
        have h21l := (hi21 hq21).1
        have h21u := (hi21 hq21).2
        have hF21 := hF.1 (by left; exact hq21)
        have hb : step.readSym.1 = SymKind.boundary := by
          have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
              r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 21 →
                r.nextState = 22 → s.1 = SymKind.boundary := by
            native_decide
          exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
            (by rw [hread]; exact htrans) hsrc (by simpa [symStepConfig] using h22n)
        have h21h : cfg₁.headPos = (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 := by
          have hb' := hF21 cfg₁.headPos (by
            rw [r7_enc_len] at h21u ⊢
            omega) (by simpa [hread] using hb)
          rcases hb' with h0 | hL
          · rw [h0] at h21l
            exfalso
            omega
          · exact hL
        have hd : step.result.moveDir = Dir.S := by
          have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
              r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 21 →
                r.nextState = 22 → r.moveDir = Dir.S := by
            native_decide
          exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
            (by rw [hread]; exact htrans) hsrc (by simpa [symStepConfig] using h22n)
        dsimp [symStepConfig]
        rw [hd, h21h]
        dsimp [Dir.toInt]
        omega
      · -- G:tape(n+1) ∈ {boundary, data0, data1}
        unfold a2p_G
        by_cases hw : cfg₁.headPos = (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ)
        · -- 写格 = n+1:q ≠ 5(5 头 ≥ n+2);读格 ∈ {b,d0,d1}(ih hG);写 ∈ {读格, b, d0, d1}(表级)
          have hq5n : (cfg₁.state : ℕ) ≠ 5 := by
            intro h5s
            have h5l := hi5 (by exact_mod_cast h5s)
            rw [hw] at h5l
            omega
          have hg : (cfg₁.tape (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ)).1 =
              SymKind.boundary ∨
              (cfg₁.tape (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ)).1 =
              SymKind.data0 ∨
              (cfg₁.tape (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ)).1 =
              SymKind.data1 := hG
          have hw1 : step.result.writeSym.1 = step.readSym.1 ∨
              step.result.writeSym.1 = SymKind.boundary ∨
              step.result.writeSym.1 = SymKind.data0 ∨
              step.result.writeSym.1 = SymKind.data1 := by
            have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) ≠ 5 →
                  s.1 = SymKind.boundary ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 →
                  r.writeSym.1 = s.1 ∨ r.writeSym.1 = SymKind.boundary ∨
                    r.writeSym.1 = SymKind.data0 ∨ r.writeSym.1 = SymKind.data1 := by
              native_decide
            exact hbb ⟨cfg₁.state, hq1lt⟩ step.readSym step.result
              (by simpa [hread] using htrans) hq5n (by
                rw [hread]
                rw [hw]
                exact hg)
          have hpos : ((symStepConfig cfg₁ step.result).tape
              (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ)) = step.result.writeSym := by
            dsimp [symStepConfig]
            exact if_pos hw.symm
          rw [hpos]
          rcases hw1 with hw1 | hw1 | hw1 | hw1
          · -- 写 = 读格:读格 = 旧 tape(n+1) ∈ {b,d0,d1}(ih hG)
            rw [hread] at hw1
            rw [hw] at hw1
            rw [hw1]
            exact hg
          · left
            exact hw1
          · right; left
            exact hw1
          · right; right
            exact hw1
        · -- 写格 ≠ n+1:旧 tape(n+1) ∈ {b,d0,d1}(ih hG)
          have hg : (cfg₁.tape (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ)).1 =
              SymKind.boundary ∨
              (cfg₁.tape (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ)).1 =
              SymKind.data0 ∨
              (cfg₁.tape (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ)).1 =
              SymKind.data1 := hG
          have hneg : ((symStepConfig cfg₁ step.result).tape
              (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ)) =
              cfg₁.tape (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) := by
            dsimp [symStepConfig]
            exact if_neg (Ne.symm hw)
          rw [hneg]
          exact hg





/-- 用户规格落点:81 行走的停点 `c` 落在中分隔符 `s` 右侧 ——
即 "c 在数据区,一定大于 s"、"81 的行走不会站到中分隔符 s 那一格"。
依赖 EProp 的 `hcons`(consumed 格 ⇒ `s + 1 ≤ j`)与 `(tape s).1 = boundary`。 -/
lemma a2p_walk81_stop_gt_s (inst : SubsetSumInstance) (s : ℤ) (cfg : SymConfig)
    (hw : a2p_walk81 inst s cfg) (h81 : cfg.state = 81)
    (hbnd : (cfg.tape s).1 = SymKind.boundary)
    (hcons : ∀ j : ℤ, j < (((encodeInstanceSym inst).length : ℕ) : ℤ) →
        (cfg.tape j).1 = SymKind.consumed → s + 1 ≤ j) :
    ∃ c : ℤ, cfg.headPos ≤ c ∧ s + 1 ≤ c ∧
      c ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 2 ∧
      (cfg.tape c).1 = SymKind.consumed ∧ c ≠ s := by
  rw [a2p_walk81] at hw
  obtain ⟨c, hc_le, hc_leL, hc_cons⟩ :=
    hw (by right; right; right; right; right; right; right; right; exact h81)
  have hcLt : c < (((encodeInstanceSym inst).length : ℕ) : ℤ) := by omega
  refine ⟨c, hc_le, hcons c hcLt hc_cons, hc_leL, hc_cons, ?_⟩
  intro hcs
  rw [hcs, hbnd] at hc_cons
  exact absurd hc_cons (by decide)
/- ============================================================================
   §81 行走相内容保真 —— 规格落点:「81 起始头和 c 之间,只有 data0 data1 和中分隔符」

   表级事实:81 态「相内步」(后继仍为 81,即非停点、非 101)读到的一定是
   data0/data1/boundary;81 态步一律右移且原样写回 ⇒ 相内区间
   [起始头, 终点头) 全为 data0/data1/boundary,而停点格(终点头处,读 consumed)即 c。
   ============================================================================ -/

/-- 表级:81 态「停留在 81」的步只读 data0/data1/boundary。 -/
lemma a2p_read_81_cont (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hq : (q : ℕ) = 81)
    (hnext : r.nextState = 81) :
    s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 81 → r.nextState = 81 →
        s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary := by
    native_decide
  exact hbb q s r hr hq hnext

/-- 表级:81 态步一律右移。 -/
lemma a2p_dir_81 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 81) : r.moveDir = Dir.R := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 81 →
        r.moveDir = Dir.R := by
    native_decide
  exact hbb q s r hr hne hq

/-- 表级:81 态步把读到的符号原样写回。 -/
lemma a2p_write_81 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 81) : r.writeSym.1 = s.1 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → (q : ℕ) = 81 →
        r.writeSym.1 = s.1 := by
    native_decide
  exact hbb q s r hr hne hq

/-- **81 行走相内容**:从状态 81 出发、每步都停留在 81(后继状态 = 81,非 101)的行程,
    起始头到终点头之间(相内走过的全部格子)只可能是 data0 / data1 / boundary。
    停点步读到 consumed 才转 13,故停点格 c 正是终点头 ⇒
    「81 起始头和 c 之间,只有 data0 data1 和中分隔符」。 -/
lemma a2p_walk81_phase (cfg₀ : SymConfig) (π : List SymStep) (cfg : SymConfig)
    (h : SymSteps VerifierSym.transition cfg₀ π cfg) :
    cfg₀.state = 81 →
    (∀ st ∈ π, st.fromState = 81 ∧ st.result.nextState = 81 ∧ st.fromState < 102) →
    ∀ j : ℤ, cfg₀.headPos ≤ j → j < cfg.headPos →
      (cfg.tape j).1 = SymKind.data0 ∨ (cfg.tape j).1 = SymKind.data1 ∨
        (cfg.tape j).1 = SymKind.boundary := by
  induction h with
  | nil =>
      intro _h81 _hphase j hj hjlt
      omega
  | cons π' step cfg' hπ hfrom hread htrans ih =>
      intro h81 hphase j hj hjlt
      have hphase' : ∀ st ∈ π', st.fromState = 81 ∧ st.result.nextState = 81 ∧
          st.fromState < 102 := by
        intro st hst
        exact hphase st (by rw [List.mem_append]; exact Or.inl hst)
      have hstep : step.fromState = 81 ∧ step.result.nextState = 81 ∧
          step.fromState < 102 := hphase step (by simp)
      have hstt : cfg'.state = 81 := by rw [← hfrom]; exact hstep.1
      have hlt : cfg'.state < 102 := by rw [← hfrom]; exact hstep.2.2
      have hne : step.result.nextState ≠ 101 := by rw [hstep.2.1]; decide
      have htrans' : step.result ∈
          VerifierSym.transition ((cfg'.state : ℕ), step.readSym) := by
        have hh := htrans
        rw [← hread] at hh
        exact hh
      have hdir : step.result.moveDir = Dir.R :=
        a2p_dir_81 ⟨cfg'.state, hlt⟩ step.readSym step.result htrans' hne
          (by simpa using hstt)
      have hw : step.result.writeSym.1 = step.readSym.1 :=
        a2p_write_81 ⟨cfg'.state, hlt⟩ step.readSym step.result htrans' hne
          (by simpa using hstt)
      have hkind : step.readSym.1 = SymKind.data0 ∨ step.readSym.1 = SymKind.data1 ∨
          step.readSym.1 = SymKind.boundary :=
        a2p_read_81_cont ⟨cfg'.state, hlt⟩ step.readSym step.result htrans'
          (by simpa using hstt) hstep.2.1
      have hhead : (symStepConfig cfg' step.result).headPos = cfg'.headPos + 1 := by
        simp [symStepConfig, hdir, Dir.toInt]
      rw [hhead] at hjlt
      by_cases hjpos : j = cfg'.headPos
      · rw [hjpos]
        simp only [symStepConfig]
        split_ifs with hoch
        · rw [hw]; exact hkind
        · exact absurd trivial hoch
      · have hjlt' : j < cfg'.headPos := by omega
        simp only [symStepConfig]
        rw [if_neg hjpos]
        exact ih h81 hphase' j hj hjlt'

-- ============================================================================
-- §8_76_单调递减:状态 8 / 76 期间读写头位置单调递减(用户规格落点)
--   规格:「状态8 和76 状态期间,其读写头的位置是单调递减的。」
--   依据:表级探针(∃-反例 + native_decide)证 8 / 76 态的非 101 回落步**一律左移**;
--   相级:整段行程每步都处于 8 或 76 ⇒ 头位置 = 起点 − 步数,严格单调递减。
-- ============================================================================

/-- 表级:8 / 76 态的非 101 回落步一律左移。 -/
lemma a2p_dir_8_76 (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) (hne : r.nextState ≠ 101)
    (hq : (q : ℕ) = 8 ∨ (q : ℕ) = 76) : r.moveDir = Dir.L := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 →
        ((q : ℕ) = 8 ∨ (q : ℕ) = 76) → r.moveDir = Dir.L := by
    native_decide
  exact hbb q s r hr hne hq

/-- **8 / 76 相头单调递减**:行程中每一步都处于状态 8 或 76(且非 101 回落)时,
    读写头位置单调不增 —— 精确地,终点头 = 起始头 − 步数。 -/
lemma a2p_walk8_76_dec (cfg₀ : SymConfig) (π : List SymStep) (cfg : SymConfig)
    (h : SymSteps VerifierSym.transition cfg₀ π cfg)
    (hphase : ∀ st ∈ π, (st.fromState = 8 ∨ st.fromState = 76) ∧
      st.result.nextState ≠ 101 ∧ st.fromState < 102) :
    cfg.headPos = cfg₀.headPos - (π.length : ℤ) := by
  induction h with
  | nil => simp
  | cons π' step cfg' hπ hfrom hread htrans ih =>
      have hphase' : ∀ st ∈ π', (st.fromState = 8 ∨ st.fromState = 76) ∧
          st.result.nextState ≠ 101 ∧ st.fromState < 102 := by
        intro st hst
        exact hphase st (by rw [List.mem_append]; exact Or.inl hst)
      have hstep : (step.fromState = 8 ∨ step.fromState = 76) ∧
          step.result.nextState ≠ 101 ∧ step.fromState < 102 := hphase step (by simp)
      have hstt : cfg'.state = 8 ∨ cfg'.state = 76 := by rw [← hfrom]; exact hstep.1
      have hlt : cfg'.state < 102 := by rw [← hfrom]; exact hstep.2.2
      have hne : step.result.nextState ≠ 101 := hstep.2.1
      have htrans' : step.result ∈
          VerifierSym.transition ((cfg'.state : ℕ), step.readSym) := by
        have hh := htrans
        rw [← hread] at hh
        exact hh
      have hdir : step.result.moveDir = Dir.L :=
        a2p_dir_8_76 ⟨cfg'.state, hlt⟩ step.readSym step.result htrans' hne
          (by simpa using hstt)
      have hhead : (symStepConfig cfg' step.result).headPos = cfg'.headPos + (-1) := by
        simp [symStepConfig, hdir, Dir.toInt]
      rw [hhead, ih hphase']
      simp
      omega

end Mp
