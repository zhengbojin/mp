import Mp.SubsetSumVerifierReverse7
import Mp.SubsetSumVerifierReverse6

open Mp
open VerifierSym

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


namespace Mp

-- ============================================================================
-- L3'' 主体:接受路径每真前缀 headPos < |encS| ∨ state = 100
-- 联合归纳束(12 分量):
--   P0' : state = 100 ∨ state = 101 ∨ headPos < (encodeInstanceSym inst).length
--   P1  : state = 1 → headPos ≤ (encodeInstanceSym inst).length-3     P28 : state = 28 → headPos ≤ (encodeInstanceSym inst).length-3
--   P87 : state = 87 → headPos ≤ (encodeInstanceSym inst).length-2    P20 : state = 20 → headPos ≤ (encodeInstanceSym inst).length-3
--   P23 : state = 23 → headPos ≤ (encodeInstanceSym inst).length-2    P81 : state = 81 → headPos ≤ (encodeInstanceSym inst).length-2
--   P9A : state ∈ {9,38,77,85} → headPos ≤ (encodeInstanceSym inst).length-4
--   P12c: state ∈ {12,11,14} → headPos ≤ (encodeInstanceSym inst).length-3
--   P10 : state = 10 → headPos ≤ (encodeBitsSym inst.target).length
--   P6l : (tape 0).1 = boundary          P6r : (tape ((encodeInstanceSym inst).length-1)).1 = boundary
--   P9  : ∀ p, (tape p).1 = boundary → p = 0 ∨ p = (encodeInstanceSym inst).length-1 ∨ ((encodeBitsSym inst.target).length+1 ≤ p ∧ p ≤ (encodeInstanceSym inst).length-3)
-- ============================================================================

/-- E 族：相位 0-1 态（0/1/2/3/24/29/26/27/38/28）——入边封闭（表级），族内无 51。 -/
abbrev r7_E (q : ℕ) : Prop :=
  q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 24 ∨ q = 29 ∨
  q = 26 ∨ q = 27 ∨ q = 38 ∨ q = 28


/-- E 路径（全部步源 ∈ E 族）上元素区段 [n+2, L-3] 无 boundary 格。 -/
lemma r7_E_no_segment_boundary (inst : SubsetSumInstance) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg)
    (hE : ∀ step ∈ π, r7_E step.fromState) :
    ∀ p : ℤ, (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ p →
      p ≤ (((encodeInstanceSym inst).length : ℕ) - 3 : ℤ) →
      (cfg.tape p).1 ≠ SymKind.boundary := by
  induction h with
  | nil =>
      intro p hp1 hp2
      dsimp [symInitialConfig]
      split
      · rename_i hc
        -- 格 = getD (p.toNat) blank，位置 = n+2+j（j < 元素长）——非 boundary（r7_enc_getD_elems_kind）
        have hge : (encodeInstanceSym inst).getD p.toNat Sym.blank =
            (encodeInstanceSym inst)[p.toNat] :=
          List.getD_eq_getElem (encodeInstanceSym inst) Sym.blank hc.2
        -- p.toNat = n + 2 + j；j = p.toNat - (n+2) < 元素长
        have hmid : p.toNat - ((encodeBitsSym inst.target).length + 2) <
            (encodeElementsSym inst.elements).length := by
          rw [r7_enc_len] at hp2
          have hq : p.toNat ≤ (encodeBitsSym inst.target).length + 1 + (encodeElementsSym inst.elements).length := by
            omega
          omega
        have hnb := r7_enc_getD_elems_kind inst (j := p.toNat - ((encodeBitsSym inst.target).length + 2)) hmid
        have hpos_eq : p.toNat = (encodeBitsSym inst.target).length + 2 + (p.toNat - ((encodeBitsSym inst.target).length + 2)) := by
          omega
        have hcell : ((encodeInstanceSym inst).getD p.toNat Sym.blank).1 ≠ SymKind.boundary := by
          rw [hpos_eq]
          exact hnb
        -- 目标：格值 .1 ≠ boundary（同一格）
        intro hb
        have hb' : ((encodeInstanceSym inst)[p.toNat]).1 = SymKind.boundary := hb
        exact hcell (by simpa [← hge] using hb')
      · rename_i hnc
        exfalso
        omega
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      have hE₀ : ∀ step ∈ π₀, r7_E step.fromState := by
        intro s hs
        exact hE s (by simp [hs])
      intro p hp1 hp2
      rw [symStepConfig]
      by_cases hw : cfg'.headPos = p
      · -- 写 p：分类（回写 → ih；51 → hE 矛盾；3 → ih）
        have hq' : cfg'.state < 102 := q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev
        dsimp [symStepConfig]
        rw [hw]
        by_cases hbw : (step.result.writeSym).1 = SymKind.boundary
        · exfalso
          by_cases hsame : step.result.writeSym = cfg'.tape p
          · -- 回写：读时已 boundary，ih 矛盾
            have hcell : (cfg'.tape p).1 = SymKind.boundary := by
              rwa [← hsame]
            exact ih hE₀ p hp1 hp2 hcell
          · -- 非回写：q = 51 ∨ q = 3
            rcases q12suffix_write_boundary_class cfg'.state hq' (cfg'.tape p) step.result
                (by simpa [hread, hw] using htrans) hbw hsame with h51 | h3
            · -- 51 ∉ E
              have hbad : r7_E step.fromState := hE step (by simp)
              rcases hbad with hb0 | hb1 | hb2 | hb3 | hb4 | hb5 | hb6 | hb7 | hb8 | hb9 <;> omega
            · -- 3：读 boundary（读位 = p）——ih 矛盾
              have hcell : (cfg'.tape cfg'.headPos).1 = SymKind.boundary := by
                have hbb : ∀ s : Sym, ∀ r : SymTransResult,
                    r ∈ VerifierSym.transition (3, s) → (r.writeSym).1 = SymKind.boundary →
                      s.1 = SymKind.boundary := by
                  native_decide
                exact hbb (cfg'.tape cfg'.headPos) step.result
                  (by simpa [hread, symStepConfig, h3] using htrans) hbw
              have hb3 : (cfg'.tape p).1 = SymKind.boundary := by
                simpa [hw] using hcell
              exact ih hE₀ p hp1 hp2 hb3
        · simpa using hbw
      · -- 不写 p：ih 保持
        dsimp [symStepConfig]
        rw [if_neg]
        · exact ih hE₀ p hp1 hp2
        · exact Ne.symm hw


/-- List append 左消去。 -/
lemma list_append_left_cancel {α : Type} {as bs cs : List α}
    (h : as ++ bs = as ++ cs) : bs = cs := by
  induction as with
  | nil => simpa using h
  | cons a as ih =>
      simp at h
      exact h

/-- List append 右消去。 -/
lemma list_append_right_cancel {α : Type} {as bs cs : List α}
    (h : as ++ bs = cs ++ bs) : as = cs := by
  induction bs generalizing as cs with
  | nil => simpa using h
  | cons b bs ih =>
      simp at h
      exact h

/-- List append = [] 的分解。 -/
lemma list_append_eq_nil {α : Type} {as bs : List α} (h : as ++ bs = []) : as = [] ∧ bs = [] := by
  induction as with
  | nil =>
      simp at h
      exact ⟨rfl, h⟩
  | cons a as ih =>
      simp at h

/-- snoc 注入：两 snoc 相等 → init 相等 ∧ last 相等。 -/
lemma list_snoc_inj {α : Type} {as bs : List α} {a b : α}
    (h : as ++ [a] = bs ++ [b]) : as = bs ∧ a = b := by
  induction as generalizing bs with
  | nil =>
      cases bs with
      | nil =>
          simp at h
          exact ⟨rfl, h⟩
      | cons c cs =>
          simp at h
  | cons c as ih =>
      cases bs with
      | nil =>
          simp at h
      | cons d ds =>
          simp at h
          have hc : c = d := h.left
          have hrest : as = ds := h.right.1
          exact ⟨by rw [hc, hrest], h.right.2⟩

/-- List 右端分解：非空列表 = init ++ [last]。 -/
lemma list_snoc_decomp {α : Type} {l : List α} (hl : l ≠ []) :
    ∃ l₀ : List α, ∃ a : α, l = l₀ ++ [a] := by
  induction l with
  | nil => exfalso; exact hl rfl
  | cons a l ih =>
      by_cases hl' : l = []
      · exact ⟨[], a, by simp [hl']⟩
      · rcases ih hl' with ⟨l₀, a₀, hs⟩
        exact ⟨a :: l₀, a₀, by simp [hs, List.append_assoc]⟩

/-- SymSteps 拼接分解（逆 of SymSteps_trans）：(\u03c0₁ ++ \u03c0₂) 路径 → \u03c0₁ 终点 + \u03c0₂ 从该终点走。 -/
lemma symSteps_append_decomp {M : ℕ × Sym → Finset SymTransResult} {cfg₀ cfg₂ : SymConfig}
    (π₁ π₂ : List SymStep)
    (h : SymSteps M cfg₀ (π₁ ++ π₂) cfg₂) :
    ∃ cfg₁ : SymConfig, SymSteps M cfg₀ π₁ cfg₁ ∧ SymSteps M cfg₁ π₂ cfg₂ := by
  -- 对 π₂.length 归纳（辅助 main）
  have main : ∀ (n : ℕ), ∀ (π₂ : List SymStep), π₂.length = n →
      ∀ {cfg₂ : SymConfig}, SymSteps M cfg₀ (π₁ ++ π₂) cfg₂ →
        ∃ cfg₁ : SymConfig, SymSteps M cfg₀ π₁ cfg₁ ∧ SymSteps M cfg₁ π₂ cfg₂ := by
    intro n
    induction n with
    | zero =>
        intro π₂ hlen cfg₂ hsteps
        have hπ₂ : π₂ = [] := by simpa using hlen
        subst π₂
        exact ⟨cfg₂, by simpa using hsteps, SymSteps.nil⟩
    | succ n ih =>
        intro π₂ hlen cfg₂ hsteps
        by_cases hπ : π₂ = []
        · subst π₂
          exact ⟨cfg₂, by simpa using hsteps, SymSteps.nil⟩
        · -- π₂ 非空：右端剝最后步
          rcases list_snoc_decomp hπ with ⟨π₂₀, last₂, hπeq⟩
          have hne : π₁ ++ π₂ ≠ [] := by
            intro hc
            exact hπ (list_append_eq_nil hc).2
          have hsplit := Mp.SymToF4.symSteps_split_last hsteps hne
          rcases hsplit with ⟨step₂, πₜ, cfg₁₂, hs, hprev₂, hfrom₂, hread₂, htrans₂, hcfg₂⟩
          have hpi : πₜ = π₁ ++ π₂₀ := by
            have hfull : (π₁ ++ π₂₀) ++ [last₂] = πₜ ++ [step₂] := by
              simpa [List.append_assoc, hπeq] using hs
            exact (list_snoc_inj hfull).1.symm
          have hlen2 : π₂₀.length = n := by
            rw [hπeq] at hlen
            simp at hlen
            omega
          have hprev' : SymSteps M cfg₀ (π₁ ++ π₂₀) cfg₁₂ := by
            simpa [hpi] using hprev₂
          rcases ih π₂₀ hlen2 hprev' with ⟨cfg₁, hseg₁, hseg₂⟩
          refine ⟨cfg₁, hseg₁, ?_⟩
          have hlast' : last₂ = step₂ := by
            have hfull : (π₁ ++ π₂₀) ++ [last₂] = (π₁ ++ π₂₀) ++ [step₂] := by
              simpa [List.append_assoc, hπeq, hpi] using hs
            have hsing := list_append_left_cancel hfull
            injection hsing
          have hπ₂eq : π₂ = π₂₀ ++ [step₂] := by
            simpa [hlast'] using hπeq
          rw [hπ₂eq, hcfg₂]
          exact SymSteps.cons π₂₀ step₂ cfg₁₂ hseg₂ hfrom₂ hread₂ htrans₂
  exact main π₂.length π₂ rfl h


/-- 21 漂移表级（读 IsOutside → 态保持）。 -/
lemma sym_21_drift_state : ∀ (s : Sym) (r : SymTransResult),
    r ∈ VerifierSym.transition (21, s) →
    s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.consumed →
    r.nextState = 21 := by
  native_decide

/-- 21 漂移表级（头向右）。 -/
lemma sym_21_drift_dir : ∀ (s : Sym) (r : SymTransResult),
    r ∈ VerifierSym.transition (21, s) →
    s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.consumed →
    r.moveDir = Dir.R := by
  native_decide

/-- 21 漂移表级（写保 IsOutside）。 -/
lemma sym_21_drift_write : ∀ (s : Sym) (r : SymTransResult),
    r ∈ VerifierSym.transition (21, s) →
    s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.consumed →
    r.writeSym.1 = SymKind.data0 ∨ r.writeSym.1 = SymKind.data1 ∨ r.writeSym.1 = SymKind.consumed := by
  native_decide

/-- 漂移态不变量：SymSteps 链中每 cfg 保持（态 = q ∧ 头 ≥ |w| ∧ 带外 IsOutside）。 -/
lemma sym_drift_steps (q : ℕ) (input : List Sym) (cfg : SymConfig)
    (hq : cfg.state = q) (hge : (input.length : ℤ) ≤ cfg.headPos)
    (hout : ∀ j : ℤ, (input.length : ℤ) ≤ j → IsOutside (cfg.tape j))
    (hdrift : ∀ s : Sym, IsOutside s → ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (q, s) → r.nextState = q ∧ r.moveDir = Dir.R ∧ IsOutside r.writeSym) :
    ∀ {π₂ : List SymStep} {cfg₂ : SymConfig},
      SymSteps VerifierSym.transition cfg π₂ cfg₂ →
        cfg₂.state = q ∧ (input.length : ℤ) ≤ cfg₂.headPos ∧
          (∀ j : ℤ, (input.length : ℤ) ≤ j → IsOutside (cfg₂.tape j)) := by
  intro π₂ cfg₂ hsteps
  induction hsteps with
  | nil =>
      exact ⟨hq, hge, hout⟩
  | cons π₂₀ step₂ cfg₁₂ hprev₂ hfrom₂ hread₂ htrans₂ ih =>
      have hcell : IsOutside step₂.readSym := by
        simpa [hread₂] using ih.2.2 cfg₁₂.headPos ih.2.1
      have hd := hdrift step₂.readSym hcell step₂.result
        (by simpa [ih.1, ← hread₂] using htrans₂)
      constructor
      · simp [symStepConfig, hd.1]
      · constructor
        · simp [symStepConfig, hd.2.1, Dir.toInt]
          omega
        · intro j hj
          rw [symStepConfig]
          by_cases hw : cfg₁₂.headPos = j
          · simpa [hw] using hd.2.2
          · simpa [Ne.symm hw] using ih.2.2 j hj

/-- 带外右漂态无延拓到 100（q 读 IsOutside → q R 自环且写保 IsOutside）。 -/
lemma sym_drift_no_accept (q : ℕ) (input : List Sym) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg)
    (hq : cfg.state = q) (hge : (input.length : ℤ) ≤ cfg.headPos)
    (hq100 : q ≠ 100)
    (hdrift : ∀ s : Sym, IsOutside s → ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (q, s) → r.nextState = q ∧ r.moveDir = Dir.R ∧ IsOutside r.writeSym) :
    ¬ (∃ π₂ cfg₂, SymReachablePath VerifierSym.transition input (π ++ π₂) cfg₂ ∧ cfg₂.state = 100) := by
  intro hext
  rcases hext with ⟨π₂, cfg₂, hpath₂, hacc₂⟩
  have hsteps₂ : SymSteps VerifierSym.transition (symInitialConfig input) (π ++ π₂) cfg₂ :=
    (symSteps_initial_iff VerifierSym.transition input (π ++ π₂) cfg₂).mpr hpath₂
  have hsteps₁ : SymSteps VerifierSym.transition (symInitialConfig input) π cfg :=
    (symSteps_initial_iff VerifierSym.transition input π cfg).mpr h
  rcases symSteps_append_decomp π π₂ hsteps₂ with ⟨cfg₁, hseg₁, hseg₂⟩
  have hcfg₁ : cfg₁ = cfg := Mp.SymToF4.symSteps_end_unique hseg₁ hsteps₁
  have hseg₂' : SymSteps VerifierSym.transition cfg π₂ cfg₂ := by
    simpa [hcfg₁] using hseg₂
  have hmain := sym_drift_steps q input cfg hq hge
    (q12_outside_closed_and_51_bound input π cfg h).1 hdrift hseg₂'
  exact (hq100 (by simpa [hmain.1] using hacc₂))

/-- 带外右漂态无延拓到 100（blank 版：带外 = blank，q 读 blank → q R 自环写回 blank）。
    Pblank 的束分量提供带外 = blank；81 的带外漂移反驳用此版（IsOutside 版对 81 假：
    81 读 consumed → 13 非自环）。 -/
lemma sym_drift_blank_steps (q : ℕ) (input : List Sym) (cfg : SymConfig)
    (hq : cfg.state = q) (hge : (input.length : ℤ) ≤ cfg.headPos)
    (hblank : ∀ j : ℤ, (input.length : ℤ) ≤ j → cfg.tape j = Sym.blank)
    (hdrift : ∀ r : SymTransResult, r ∈ VerifierSym.transition (q, Sym.blank) →
      r.nextState = q ∧ r.moveDir = Dir.R ∧ r.writeSym = Sym.blank) :
    ∀ {π₂ : List SymStep} {cfg₂ : SymConfig},
      SymSteps VerifierSym.transition cfg π₂ cfg₂ →
        cfg₂.state = q ∧ (input.length : ℤ) ≤ cfg₂.headPos ∧
          (∀ j : ℤ, (input.length : ℤ) ≤ j → cfg₂.tape j = Sym.blank) := by
  intro π₂ cfg₂ hsteps
  induction hsteps with
  | nil =>
      exact ⟨hq, hge, hblank⟩
  | cons π₂₀ step₂ cfg₁₂ hprev₂ hfrom₂ hread₂ htrans₂ ih =>
      have hcell : step₂.readSym = Sym.blank := by
        simpa [hread₂] using ih.2.2 cfg₁₂.headPos ih.2.1
      have hd := hdrift step₂.result (by
        have hc2 : cfg₁₂.tape cfg₁₂.headPos = Sym.blank := by simpa [hread₂] using hcell
        simpa [ih.1, hc2] using htrans₂)
      constructor
      · simp [symStepConfig, hd.1]
      · constructor
        · simp [symStepConfig, hd.2.1, Dir.toInt]
          omega
        · intro j hj
          rw [symStepConfig]
          by_cases hw : cfg₁₂.headPos = j
          · simpa [hw] using hd.2.2
          · simpa [Ne.symm hw] using ih.2.2 j hj

lemma sym_drift_blank_no_accept (q : ℕ) (input : List Sym) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg)
    (hq : cfg.state = q) (hge : (input.length : ℤ) ≤ cfg.headPos)
    (hq100 : q ≠ 100)
    (hblank : ∀ j : ℤ, (input.length : ℤ) ≤ j → cfg.tape j = Sym.blank)
    (hdrift : ∀ r : SymTransResult, r ∈ VerifierSym.transition (q, Sym.blank) →
      r.nextState = q ∧ r.moveDir = Dir.R ∧ r.writeSym = Sym.blank) :
    ¬ (∃ π₂ cfg₂, SymReachablePath VerifierSym.transition input (π ++ π₂) cfg₂ ∧ cfg₂.state = 100) := by
  intro hext
  rcases hext with ⟨π₂, cfg₂, hpath₂, hacc₂⟩
  have hsteps₂ : SymSteps VerifierSym.transition (symInitialConfig input) (π ++ π₂) cfg₂ :=
    (symSteps_initial_iff VerifierSym.transition input (π ++ π₂) cfg₂).mpr hpath₂
  have hsteps₁ : SymSteps VerifierSym.transition (symInitialConfig input) π cfg :=
    (symSteps_initial_iff VerifierSym.transition input π cfg).mpr h
  rcases symSteps_append_decomp π π₂ hsteps₂ with ⟨cfg₁, hseg₁, hseg₂⟩
  have hcfg₁ : cfg₁ = cfg := Mp.SymToF4.symSteps_end_unique hseg₁ hsteps₁
  have hseg₂' : SymSteps VerifierSym.transition cfg π₂ cfg₂ := by
    simpa [hcfg₁] using hseg₂
  have hmain := sym_drift_blank_steps q input cfg hq hge hblank hdrift hseg₂'
  exact (hq100 (by simpa [hmain.1] using hacc₂))

/-- SymSteps（从任意 cfg 起）拼接可达路径：cfg 可达 + SymSteps cfg π₂ cfg₂ → cfg₂ 可达。 -/
lemma symSteps_after_path (M : ℕ × Sym → Finset SymTransResult) (input : List Sym)
    {πc : List SymStep} {cfg : SymConfig} {π₂ : List SymStep} {cfg₂ : SymConfig}
    (h : SymReachablePath M input πc cfg)
    (hseg : SymSteps M cfg π₂ cfg₂) :
    SymReachablePath M input (πc ++ π₂) cfg₂ := by
  induction hseg with
  | nil =>
      simpa using h
  | cons π₂₀ step cfg₁ hprev hfrom hread htrans ih =>
      simpa [List.append_assoc] using
        (SymReachablePath.cons (πc ++ π₂₀) step cfg₁ ih hfrom hread htrans)

/-- 81 读 boundary-kind 或 blank → 81 R 写回原值（表级；含 m=true 的 boundary）。 -/
lemma sym_81_boundary_blank_write (s : Sym) (hs : s.1 = SymKind.boundary ∨ s = Sym.blank)
    (r : SymTransResult) (hr : r ∈ VerifierSym.transition (81, s)) :
    r.nextState = 81 ∧ r.moveDir = Dir.R ∧ r.writeSym = s := by
  have hb : ∀ s : Sym, (s.1 = SymKind.boundary ∨ s = Sym.blank) →
      ∀ r : SymTransResult, r ∈ VerifierSym.transition (81, s) →
        r.nextState = 81 ∧ r.moveDir = Dir.R ∧ r.writeSym = s := by
    native_decide
  exact hb s hs r hr

/-- 带头 ≥ L-1 的 81 漂移链：读 #₁@L-1 → R，读带外 blank → R，写回原值（保持 tape 形状）。 -/
lemma sym_drift_81_steps (input : List Sym) (cfg : SymConfig)
    (hq : cfg.state = 81) (hge : (input.length : ℤ) - 1 ≤ cfg.headPos)
    (hbdry : (cfg.tape ((input.length : ℤ) - 1)).1 = SymKind.boundary)
    (hblank : ∀ j : ℤ, (input.length : ℤ) ≤ j → cfg.tape j = Sym.blank) :
    ∀ {π₂ : List SymStep} {cfg₂ : SymConfig},
      SymSteps VerifierSym.transition cfg π₂ cfg₂ →
        cfg₂.state = 81 ∧ (input.length : ℤ) - 1 ≤ cfg₂.headPos ∧
          (cfg₂.tape ((input.length : ℤ) - 1)).1 = SymKind.boundary ∧
            (∀ j : ℤ, (input.length : ℤ) ≤ j → cfg₂.tape j = Sym.blank) := by
  intro π₂ cfg₂ hsteps
  induction hsteps with
  | nil =>
      exact ⟨hq, hge, hbdry, hblank⟩
  | cons π₂₀ step₂ cfg₁₂ hprev₂ hfrom₂ hread₂ htrans₂ ih =>
      have hcell : step₂.readSym.1 = SymKind.boundary ∨ step₂.readSym = Sym.blank := by
        by_cases hL1 : cfg₁₂.headPos = (input.length : ℤ) - 1
        · left
          simpa [hread₂, hL1] using ih.2.2.1
        · right
          have hge₂' : (input.length : ℤ) ≤ cfg₁₂.headPos := by omega
          simpa [hread₂] using ih.2.2.2 cfg₁₂.headPos hge₂'
      have hd := sym_81_boundary_blank_write step₂.readSym hcell step₂.result
        (by simpa [ih.1, ← hread₂] using htrans₂)
      constructor
      · simp [symStepConfig, hd.1]
      · constructor
        · simp [symStepConfig, hd.2.1, Dir.toInt]
          omega
        · constructor
          · rw [symStepConfig]
            by_cases hw : cfg₁₂.headPos = (input.length : ℤ) - 1
            · have hwv : step₂.result.writeSym.1 = SymKind.boundary := by
                have htmp : step₂.result.writeSym = cfg₁₂.tape cfg₁₂.headPos := by
                  simpa [hread₂] using hd.2.2
                rw [htmp]
                simpa [hw] using ih.2.2.1
              simpa [symStepConfig, hw] using hwv
            · simp [symStepConfig, Ne.symm hw]
              exact ih.2.2.1
          · intro j hj
            rw [symStepConfig]
            by_cases hw : cfg₁₂.headPos = j
            · have hb2 : cfg₁₂.tape cfg₁₂.headPos = Sym.blank := by
                have hj' : (input.length : ℤ) ≤ cfg₁₂.headPos := by omega
                exact ih.2.2.2 cfg₁₂.headPos hj'
              have hwv : step₂.result.writeSym = Sym.blank := by
                calc
                  step₂.result.writeSym = cfg₁₂.tape cfg₁₂.headPos := by simpa [hread₂] using hd.2.2
                  _ = Sym.blank := hb2
              simpa [symStepConfig, hw] using hwv
            · simpa [symStepConfig, Ne.symm hw] using ih.2.2.2 j hj

lemma sym_drift_81_no_accept (input : List Sym) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg)
    (hq : cfg.state = 81) (hge : (input.length : ℤ) - 1 ≤ cfg.headPos)
    (hbdry : (cfg.tape ((input.length : ℤ) - 1)).1 = SymKind.boundary)
    (hblank : ∀ j : ℤ, (input.length : ℤ) ≤ j → cfg.tape j = Sym.blank) :
    ¬ (∃ π₂ cfg₂, SymReachablePath VerifierSym.transition input (π ++ π₂) cfg₂ ∧ cfg₂.state = 100) := by
  intro hext
  rcases hext with ⟨π₂, cfg₂, hpath₂, hacc₂⟩
  have hsteps₂ : SymSteps VerifierSym.transition (symInitialConfig input) (π ++ π₂) cfg₂ :=
    (symSteps_initial_iff VerifierSym.transition input (π ++ π₂) cfg₂).mpr hpath₂
  have hsteps₁ : SymSteps VerifierSym.transition (symInitialConfig input) π cfg :=
    (symSteps_initial_iff VerifierSym.transition input π cfg).mpr h
  rcases symSteps_append_decomp π π₂ hsteps₂ with ⟨cfg₁, hseg₁, hseg₂⟩
  have hcfg₁ : cfg₁ = cfg := Mp.SymToF4.symSteps_end_unique hseg₁ hsteps₁
  have hseg₂' : SymSteps VerifierSym.transition cfg π₂ cfg₂ := by
    simpa [hcfg₁] using hseg₂
  have hmain := sym_drift_81_steps input cfg hq hge hbdry hblank hseg₂'
  have h81n : 81 ≠ 100 := by norm_num
  exact (h81n (by simpa [hmain.1] using hacc₂))

/-- 101 的 S 吸收（带外 blank 版）：101@头 ≥ L 读 blank → 101 S 写回 blank（头不动），
    延拓终点恒 101 ≠ 100。P12c 各支的"@L-1 读 #₁ → 101 R@L"排除用。 -/
lemma sym_drift_101S_steps (input : List Sym) (cfg : SymConfig)
    (hq : cfg.state = 101) (hge : (input.length : ℤ) ≤ cfg.headPos)
    (hblank : ∀ j : ℤ, (input.length : ℤ) ≤ j → cfg.tape j = Sym.blank) :
    ∀ {π₂ : List SymStep} {cfg₂ : SymConfig},
      SymSteps VerifierSym.transition cfg π₂ cfg₂ →
        cfg₂.state = 101 ∧ (input.length : ℤ) ≤ cfg₂.headPos ∧
          (∀ j : ℤ, (input.length : ℤ) ≤ j → cfg₂.tape j = Sym.blank) := by
  intro π₂ cfg₂ hsteps
  induction hsteps with
  | nil => exact ⟨hq, hge, hblank⟩
  | cons π₂₀ step₂ cfg₁₂ hprev₂ hfrom₂ hread₂ htrans₂ ih =>
      have hcell : step₂.readSym = Sym.blank := by
        simpa [hread₂] using ih.2.2 cfg₁₂.headPos ih.2.1
      have hd : step₂.result.nextState = 101 ∧ step₂.result.moveDir = Dir.S ∧
          step₂.result.writeSym = Sym.blank := by
        have hb : ∀ r : SymTransResult, r ∈ VerifierSym.transition (101, Sym.blank) →
            r.nextState = 101 ∧ r.moveDir = Dir.S ∧ r.writeSym = Sym.blank := by
          native_decide
        have hc2 : cfg₁₂.tape cfg₁₂.headPos = Sym.blank := by simpa [hread₂] using hcell
        exact hb step₂.result (by simpa [ih.1, hc2] using htrans₂)
      constructor
      · simp [symStepConfig, hd.1]
      · constructor
        · simp [symStepConfig, hd.2.1, Dir.toInt]
          exact ih.2.1
        · intro j hj
          rw [symStepConfig]
          by_cases hw : cfg₁₂.headPos = j
          · simpa [hw] using hd.2.2
          · simpa [Ne.symm hw] using ih.2.2 j hj

lemma sym_drift_101S_no_accept (input : List Sym) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg)
    (hq : cfg.state = 101) (hge : (input.length : ℤ) ≤ cfg.headPos)
    (hblank : ∀ j : ℤ, (input.length : ℤ) ≤ j → cfg.tape j = Sym.blank) :
    ¬ (∃ π₂ cfg₂, SymReachablePath VerifierSym.transition input (π ++ π₂) cfg₂ ∧ cfg₂.state = 100) := by
  intro hext
  rcases hext with ⟨π₂, cfg₂, hpath₂, hacc₂⟩
  have hsteps₂ : SymSteps VerifierSym.transition (symInitialConfig input) (π ++ π₂) cfg₂ :=
    (symSteps_initial_iff VerifierSym.transition input (π ++ π₂) cfg₂).mpr hpath₂
  have hsteps₁ : SymSteps VerifierSym.transition (symInitialConfig input) π cfg :=
    (symSteps_initial_iff VerifierSym.transition input π cfg).mpr h
  rcases symSteps_append_decomp π π₂ hsteps₂ with ⟨cfg₁, hseg₁, hseg₂⟩
  have hcfg₁ : cfg₁ = cfg := Mp.SymToF4.symSteps_end_unique hseg₁ hsteps₁
  have hseg₂' : SymSteps VerifierSym.transition cfg π₂ cfg₂ := by
    simpa [hcfg₁] using hseg₂
  have hmain := sym_drift_101S_steps input cfg hq hge hblank hseg₂'
  have h101n : 101 ≠ 100 := by norm_num
  exact (h101n (by simpa [hmain.1] using hacc₂))

/-- q@L-1（q 读 boundary → 101 类）的可延拓 cfg：任意延拓的中间/终点状态
    ∈ {cfg, 101}（cfg 读 #₁ → 101，101 读任意 → 101 S 吸收；头 ≥ L-1 无 q 自环）。 -/
lemma sym_qL1_states (input : List Sym) (q : ℕ) (cfg : SymConfig)
    (hq : cfg.state = q) (hL1 : cfg.headPos = (input.length : ℤ) - 1)
    (hbdry : (cfg.tape ((input.length : ℤ) - 1)).1 = SymKind.boundary)
    (hbq : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (q, s) → s.1 = SymKind.boundary → r.nextState = 101) :
    ∀ {π₂ : List SymStep} {cfg₂ : SymConfig},
      SymSteps VerifierSym.transition cfg π₂ cfg₂ →
        cfg₂ = cfg ∨ cfg₂.state = 101 := by
  intro π₂ cfg₂ hsteps
  induction hsteps with
  | nil => left; rfl
  | cons π₂₀ step₂ cfg₁₂ hprev₂ hfrom₂ hread₂ htrans₂ ih =>
      right
      rcases ih with hc | h101₂
      · -- cfg₁₂ = cfg（q@L-1）：读 #₁ → 101
        have hcbd : step₂.readSym.1 = SymKind.boundary := by
          rw [hread₂, hc, hL1]
          exact hbdry
        have hq₁₂ : cfg₁₂.state = q := by simpa [hc] using hq
        have hbad := hbq step₂.readSym step₂.result (by simpa [hq₁₂, ← hread₂] using htrans₂) hcbd
        simpa [symStepConfig] using hbad
      · -- cfg₁₂ 态 101：S 吸收
        have hb101 : ∀ s : Sym, ∀ r : SymTransResult,
            r ∈ VerifierSym.transition (101, s) → r.nextState = 101 := by
          native_decide
        have hbad := hb101 step₂.readSym step₂.result (by simpa [h101₂, ← hread₂] using htrans₂)
        simpa [symStepConfig] using hbad

/-- q@L-1 读 #₁ → 101 的态（q ∈ {12,11,14} 类）：q@L-1 的可延拓 cfg 无延拓到 100。 -/
lemma sym_qL1_101_no_accept (input : List Sym) (q : ℕ) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg)
    (hq : cfg.state = q) (hL1 : cfg.headPos = (input.length : ℤ) - 1)
    (hbdry : (cfg.tape ((input.length : ℤ) - 1)).1 = SymKind.boundary)
    (hbq : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (q, s) → s.1 = SymKind.boundary → r.nextState = 101)
    (hq100 : q ≠ 100) :
    ¬ (∃ π₂ cfg₂, SymReachablePath VerifierSym.transition input (π ++ π₂) cfg₂ ∧ cfg₂.state = 100) := by
  intro hext
  rcases hext with ⟨π₂, cfg₂, hpath₂, hacc₂⟩
  have hsteps₂ : SymSteps VerifierSym.transition (symInitialConfig input) (π ++ π₂) cfg₂ :=
    (symSteps_initial_iff VerifierSym.transition input (π ++ π₂) cfg₂).mpr hpath₂
  have hsteps₁ : SymSteps VerifierSym.transition (symInitialConfig input) π cfg :=
    (symSteps_initial_iff VerifierSym.transition input π cfg).mpr h
  rcases symSteps_append_decomp π π₂ hsteps₂ with ⟨cfg₁, hseg₁, hseg₂⟩
  have hcfg₁ : cfg₁ = cfg := Mp.SymToF4.symSteps_end_unique hseg₁ hsteps₁
  have hseg₂' : SymSteps VerifierSym.transition cfg π₂ cfg₂ := by
    simpa [hcfg₁] using hseg₂
  have hst₂ := sym_qL1_states input q cfg hq hL1 hbdry hbq hseg₂'
  have h101n : 101 ≠ 100 := by norm_num
  rcases hst₂ with hc | h101₂
  · -- cfg₂ = cfg：态 q ≠ 100
    exact hq100 (by simpa [hq, hc] using hacc₂)
  · -- cfg₂ 态 101 ≠ 100
    exact h101n (by simpa [h101₂] using hacc₂)

/-- 值 ≥ 1 的位串非空（digits 2 v 长 ≥ 1）。 -/
lemma r7_bits_len_pos (v : ℕ) (hv : 0 < v) : 1 ≤ (encodeBitsSymNative v).length := by
  unfold encodeBitsSymNative
  rw [List.length_map]
  have hne : v ≠ 0 := by omega
  have hl : (Nat.digits 2 v).length = Nat.log 2 v + 1 := by
    exact Nat.length_digits 2 v (by norm_num : 1 < 2) hne
  rw [hl]
  omega

/-- 非空 + 全正值 → 元素区总长 ≥ 2（每元素 = 分隔符 + ≥1 位）。 -/
lemma r7_elems_len_ge2 (l : List ℕ) (hl : 0 < (encodeElementsSym l).length)
    (hpos : ∀ v ∈ l, 0 < v) :
    2 ≤ (encodeElementsSym l).length := by
  cases l with
  | nil => simp [encodeElementsSym] at hl
  | cons v rest =>
      have hvp : 0 < v := hpos v (by simp)
      cases rest with
      | nil =>
          simp [encodeElementsSym]
          have hd := r7_bits_len_pos v hvp
          omega
      | cons v2 rest2 =>
          simp [encodeElementsSym]
          have hd := r7_bits_len_pos v hvp
          omega



/-- bits 首格(值位首)kind ∈ {data0, data1}(v > 0 → digits 非空,首 digit ∈ {0,1})。 -/
lemma r7l3_bits_getD0_kind (v : ℕ) (hv : 0 < v) :
    ((encodeBitsSymNative v).getD 0 Sym.blank).1 = SymKind.data0 ∨
    ((encodeBitsSymNative v).getD 0 Sym.blank).1 = SymKind.data1 := by
  have hv0 : 0 < (encodeBitsSymNative v).length := by
    have hle := r7_bits_len_pos v hv
    omega
  have hdv : 0 < (Nat.digits 2 v).length := by
    simpa [encodeBitsSymNative] using hv0
  have he0 : (encodeBitsSymNative v).getD 0 Sym.blank = (encodeBitsSymNative v)[0]'hv0 :=
    List.getD_eq_getElem (encodeBitsSymNative v) Sym.blank hv0
  rw [he0]
  unfold encodeBitsSymNative
  rw [List.getElem_map]
  by_cases hd : (Nat.digits 2 v)[0]'hdv = 0
  · left
    simp [hd]
  · right
    simp [hd]

/-- 元素区 getD 1(首元素 α 后首格 = 值位首)kind ∈ {data0, data1}。 -/
lemma r7l3_elems_getD1_kind {elems : List ℕ} (hm : 0 < (encodeElementsSym elems).length)
    (hpos : ∀ v ∈ elems, 0 < v) :
    ((encodeElementsSym elems).getD 1 Sym.blank).1 = SymKind.data0 ∨
    ((encodeElementsSym elems).getD 1 Sym.blank).1 = SymKind.data1 := by
  cases elems with
  | nil => simp [encodeElementsSym] at hm
  | cons v rest =>
      have hv : 0 < v := hpos v List.mem_cons_self
      have hval : (encodeElementsSym (v :: rest)).getD 1 Sym.blank =
          (encodeBitsSymNative v).getD 0 Sym.blank := by
        cases rest with
        | nil =>
            change ([Sym.alpha] ++ encodeBitsSymNative v).getD 1 Sym.blank =
              (encodeBitsSymNative v).getD 0 Sym.blank
            rfl
        | cons v2 rest2 =>
            change ([Sym.alpha] ++ encodeBitsSymNative v ++ encodeElementsSym (v2 :: rest2)).getD 1
                Sym.blank = (encodeBitsSymNative v).getD 0 Sym.blank
            rw [List.append_assoc]
            rw [List.getD_append_right [Sym.alpha]
              (encodeBitsSymNative v ++ encodeElementsSym (v2 :: rest2)) Sym.blank 1 (by simp)]
            change (encodeBitsSymNative v ++ encodeElementsSym (v2 :: rest2)).getD 0 Sym.blank =
              (encodeBitsSymNative v).getD 0 Sym.blank
            rw [r7_getD_append_left (encodeBitsSymNative v) (encodeElementsSym (v2 :: rest2))
              Sym.blank 0 (by have hle := r7_bits_len_pos v hv; omega)]
      rw [hval]
      exact r7l3_bits_getD0_kind v hv

/-- 标记位位置（定理级，可达版）：alpha/sel/nosel 格只出现在元素标记位
    α_k ∈ [n+2, L-2]（元素段）——新写 sel/nosel 者只 2（读 alpha 格，r7_sel_nosel_writer_only_2），
    21/51/100/101 只写回同值；alpha 无新写者。 -/
lemma r7l3_marker_pos (inst : SubsetSumInstance) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg) :
    ∀ p : ℤ, (cfg.tape p).1 = SymKind.alpha ∨ (cfg.tape p).1 = SymKind.sel ∨
      (cfg.tape p).1 = SymKind.nosel →
      (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ p ∧
      p ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := by
  induction h with
  | nil =>
      intro p hp
      constructor
      · -- 下界 n+2 ≤ p：反证 p ≤ n+1 → 格 ∈ {#ₗ, bits data, #₀}
        by_contra hlt
        have hp_le : p ≤ (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) := by omega
        rw [symInitialConfig] at hp
        dsimp [symInitialConfig] at hp
        by_cases hvalid : 0 ≤ p ∧ p.toNat < (encodeInstanceSym inst).length
        · have hcases : p = 0 ∨ (1 ≤ p ∧ p ≤ ((encodeBitsSym inst.target).length : ℤ)) ∨
              p = (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) := by omega
          rcases hcases with hp0 | hbits | hmid
          · subst hp0
            simp at hvalid
            simp [hvalid] at hp
            have hz0 : (encodeInstanceSym inst)[0] = Sym.boundary := by
              rw [← List.getD_eq_getElem (encodeInstanceSym inst) Sym.blank (by
                rw [r7_enc_len]
                omega)]
              rw [r7_enc_getD_0 inst]
            rw [hz0] at hp
            rcases hp with hα | hsel | hnosel
            · cases hα
            · cases hsel
            · cases hnosel
          · -- bits 区：getD p.toNat = bits.getD (p.toNat-1) ∈ {data0, data1}
            have hk : p.toNat - 1 < (encodeBitsSym inst.target).length := by
              have hge : 1 ≤ p.toNat := by omega
              omega
            have hfinal : ((encodeInstanceSym inst).getD p.toNat Sym.blank) =
                (encodeBitsSym inst.target).getD (p.toNat - 1) Sym.blank := by
              unfold encodeInstanceSym
              let X₂ : List Sym := [Sym.boundary] ++ encodeBitsSym inst.target
              let X₁ : List Sym := X₂ ++ [Sym.boundary]
              let X₀ : List Sym := X₁ ++ encodeElementsSym inst.elements
              change (X₀ ++ [Sym.boundary]).getD p.toNat Sym.blank =
                (encodeBitsSym inst.target).getD (p.toNat - 1) Sym.blank
              have hpn : p.toNat ≤ (encodeBitsSym inst.target).length := by omega
              have hL₀ : p.toNat < X₀.length := by
                dsimp [X₀, X₁, X₂]; simp [List.length_append]; omega
              have hL₁ : p.toNat < X₁.length := by
                dsimp [X₁, X₂]; simp [List.length_append]; omega
              have hL₂ : p.toNat < X₂.length := by
                dsimp [X₂]; simp [List.length_append]; omega
              have hR : [Sym.boundary].length ≤ p.toNat := by
                simp; omega
              calc
                (X₀ ++ [Sym.boundary]).getD p.toNat Sym.blank
                    = X₀.getD p.toNat Sym.blank := r7_getD_append_left X₀ [Sym.boundary] Sym.blank p.toNat hL₀
                _ = X₁.getD p.toNat Sym.blank := r7_getD_append_left X₁ (encodeElementsSym inst.elements) Sym.blank p.toNat hL₁
                _ = X₂.getD p.toNat Sym.blank := r7_getD_append_left X₂ [Sym.boundary] Sym.blank p.toNat hL₂
                _ = (encodeBitsSym inst.target).getD (p.toNat - [Sym.boundary].length) Sym.blank :=
                    List.getD_append_right [Sym.boundary] (encodeBitsSym inst.target) Sym.blank p.toNat hR
                _ = (encodeBitsSym inst.target).getD (p.toNat - 1) Sym.blank := by
                    congr 1 <;> simp
            simp [hvalid] at hp
            rw [← List.getD_eq_getElem (encodeInstanceSym inst) Sym.blank hvalid.2] at hp
            rw [hfinal] at hp
            have hd := encodeBitsSym_data inst.target (p.toNat - 1) hk
            rcases hp with hα | hsel | hnosel
            · rcases hd with hd0 | hd1
              · rw [hα] at hd0; cases hd0
              · rw [hα] at hd1; cases hd1
            · rcases hd with hd0 | hd1
              · rw [hsel] at hd0; cases hd0
              · rw [hsel] at hd1; cases hd1
            · rcases hd with hd0 | hd1
              · rw [hnosel] at hd0; cases hd0
              · rw [hnosel] at hd1; cases hd1
          · subst hmid
            simp at hvalid
            simp [hvalid] at hp
            rw [← List.getD_eq_getElem (encodeInstanceSym inst) Sym.blank hvalid.2] at hp
            rw [r7_enc_getD_mid inst] at hp
            rcases hp with hα | hsel | hnosel
            · cases hα
            · cases hsel
            · cases hnosel
        · simp [hvalid] at hp
          rcases hp with hα | hsel | hnosel
          · cases hα
          · cases hsel
          · cases hnosel
      · -- 上界 p ≤ L-2：反证 p ≥ L-1 → 格 ∈ {#₁, blank}
        by_contra hgt
        have hp_ge : (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) ≤ p := by omega
        rw [symInitialConfig] at hp
        dsimp [symInitialConfig] at hp
        by_cases hvalid : 0 ≤ p ∧ p.toNat < (encodeInstanceSym inst).length
        · have hlast : p.toNat = (encodeInstanceSym inst).length - 1 := by omega
          simp [hvalid] at hp
          have hz : (encodeInstanceSym inst)[p.toNat] = Sym.boundary := by
            rw [← List.getD_eq_getElem (encodeInstanceSym inst) Sym.blank hvalid.2]
            rw [hlast]
            rw [r7_enc_getD_last inst]
          rw [hz] at hp
          rcases hp with hα | hsel | hnosel
          · cases hα
          · cases hsel
          · cases hnosel
        · simp [hvalid] at hp
          rcases hp with hα | hsel | hnosel
          · exfalso; exact (by native_decide : Sym.blank.1 ≠ SymKind.alpha) hα
          · exfalso; exact (by native_decide : Sym.blank.1 ≠ SymKind.sel) hsel
          · exfalso; exact (by native_decide : Sym.blank.1 ≠ SymKind.nosel) hnosel
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      intro p hp
      rw [symStepConfig] at hp
      by_cases hpw : p = cfg'.headPos
      · -- 写位：cfg.tape p = writeSym
        have hq' : cfg'.state < 102 := q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev
        -- 读的 = cfg'.tape p（hread + hpw）
        have hrd : (cfg'.tape p).1 = SymKind.alpha ∨ (cfg'.tape p).1 = SymKind.sel ∨
            (cfg'.tape p).1 = SymKind.nosel := by
          rw [hpw, ← hread]
          -- 写 alpha/sel/nosel 者读同值（表级：新写 sel/nosel 者 2 读 alpha 也在集内）
          have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
              r ∈ VerifierSym.transition ((q : ℕ), s) →
                r.writeSym.1 = SymKind.alpha ∨ r.writeSym.1 = SymKind.sel ∨ r.writeSym.1 = SymKind.nosel →
                  s.1 = SymKind.alpha ∨ s.1 = SymKind.sel ∨ s.1 = SymKind.nosel := by
            native_decide
          exact hb ⟨cfg'.state, hq'⟩ step.readSym step.result
            (by simpa [hread] using htrans) (by simpa [hpw, ← hread] using hp)
        exact ih p hrd
      · -- 未写该格
        have hp' : (cfg'.tape p).1 = SymKind.alpha ∨ (cfg'.tape p).1 = SymKind.sel ∨
            (cfg'.tape p).1 = SymKind.nosel := by
          simpa [symStepConfig, hpw] using hp
        exact ih p hp'


/-- 读 boundary 的写值:恒 boundary 或 q = 20(20 读 boundary 写 data0——消除 #₀)。 -/
lemma r7l3_boundary_write (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hs : s.1 = SymKind.boundary) (hr : r ∈ VerifierSym.transition (q, s)) :
    (r.writeSym).1 = SymKind.boundary ∨ q = 20 := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → s.1 = SymKind.boundary →
      (r.writeSym).1 = SymKind.boundary ∨ (q : ℕ) = 20 := by native_decide
  exact hb ⟨q, hq⟩ s r hr hs
/-- n+3 位(首元素 α 后的值位首格)永非 α/sel/nosel:初始 = 首元素值位(data0/1);
    写 sel/nosel 者只 2(读 α——ih 排);α 无写者。用途:P10' 排除 51@n+2(51 头 = n+2 ⟸ 21 读 sel@n+3)。 -/
lemma r7l3_marker_not_n3 (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (hpos : ∀ v ∈ inst.elements, 0 < v) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg) :
    (cfg.tape (((encodeBitsSym inst.target).length + 3 : ℕ) : ℤ)).1 ≠ SymKind.alpha ∧
    (cfg.tape (((encodeBitsSym inst.target).length + 3 : ℕ) : ℤ)).1 ≠ SymKind.sel ∧
    (cfg.tape (((encodeBitsSym inst.target).length + 3 : ℕ) : ℤ)).1 ≠ SymKind.nosel := by
  induction h with
  | nil =>
      -- 初始:n+3 格 = 首元素值位首(data0/1——hm+hpos:首元素 v0 > 0,bits 非空)
      -- n+3 在编码内:elems 长 ≥ 2(r7_elems_len_ge2)——n+3 = n+2+1 < n+2+len
      have hlenge : 2 ≤ (encodeElementsSym inst.elements).length := r7_elems_len_ge2 inst.elements hm hpos
      refine ⟨?_, ?_, ?_⟩
      · intro hnb
        dsimp [symInitialConfig] at hnb
        split at hnb
        · rename_i hc
          -- 界内格 = (input)[n+3]——getD 链到 elems.getD 1 = 首元素 bits 首(data0/1)
          have hge : (encodeInstanceSym inst).getD (((encodeBitsSym inst.target).length + 3 : ℕ)) Sym.blank =
              (encodeElementsSym inst.elements).getD 1 Sym.blank := by
            unfold encodeInstanceSym
            let X₁ : List Sym := [Sym.boundary] ++ encodeBitsSym inst.target ++ [Sym.boundary]
            let X₀ : List Sym := X₁ ++ encodeElementsSym inst.elements
            change (X₀ ++ [Sym.boundary]).getD (((encodeBitsSym inst.target).length + 3 : ℕ)) Sym.blank =
              (encodeElementsSym inst.elements).getD 1 Sym.blank
            have hL₀ : (encodeBitsSym inst.target).length + 3 < X₀.length := by
              dsimp [X₀, X₁]; simp [List.length_append]
              omega
            have hR : X₁.length ≤ (encodeBitsSym inst.target).length + 3 := by
              dsimp [X₁]; simp [List.length_append]
            calc
              (X₀ ++ [Sym.boundary]).getD (((encodeBitsSym inst.target).length + 3 : ℕ)) Sym.blank
                  = X₀.getD (((encodeBitsSym inst.target).length + 3 : ℕ)) Sym.blank := r7_getD_append_left X₀ [Sym.boundary] Sym.blank (((encodeBitsSym inst.target).length + 3 : ℕ)) hL₀
              _ = (encodeElementsSym inst.elements).getD (((encodeBitsSym inst.target).length + 3) - X₁.length) Sym.blank :=
                    List.getD_append_right X₁ (encodeElementsSym inst.elements) Sym.blank (((encodeBitsSym inst.target).length + 3 : ℕ)) hR
              _ = (encodeElementsSym inst.elements).getD 1 Sym.blank := by
                    congr 1 <;> dsimp [X₁] <;> simp [List.length_append]
          have hn3to : ((((encodeBitsSym inst.target).length + 3 : ℕ) : ℤ).toNat) = (encodeBitsSym inst.target).length + 3 := by omega
          rw [← List.getD_eq_getElem (encodeInstanceSym inst) Sym.blank hc.2] at hnb
          have hidx : ((((encodeBitsSym inst.target).length : ℤ) + 3).toNat) =
              (encodeBitsSym inst.target).length + 3 := by omega
          rw [hidx] at hnb
          rw [hge] at hnb
          -- elems.getD 1 = 首元素 bits 首
          rcases r7l3_elems_getD1_kind hm hpos with hd0 | hd1
          · rw [hnb] at hd0
            exact (by native_decide : SymKind.alpha ≠ SymKind.data0) hd0
          · rw [hnb] at hd1
            exact (by native_decide : SymKind.alpha ≠ SymKind.data1) hd1
        · rename_i hnc
          have hnb' : Sym.blank.1 ≠ SymKind.alpha := by native_decide
          exact hnb' hnb
      · intro hnb
        dsimp [symInitialConfig] at hnb
        split at hnb
        · rename_i hc
          have hge : (encodeInstanceSym inst).getD (((encodeBitsSym inst.target).length + 3 : ℕ)) Sym.blank =
              (encodeElementsSym inst.elements).getD 1 Sym.blank := by
            unfold encodeInstanceSym
            let X₁ : List Sym := [Sym.boundary] ++ encodeBitsSym inst.target ++ [Sym.boundary]
            let X₀ : List Sym := X₁ ++ encodeElementsSym inst.elements
            change (X₀ ++ [Sym.boundary]).getD (((encodeBitsSym inst.target).length + 3 : ℕ)) Sym.blank =
              (encodeElementsSym inst.elements).getD 1 Sym.blank
            have hL₀ : (encodeBitsSym inst.target).length + 3 < X₀.length := by
              dsimp [X₀, X₁]; simp [List.length_append]
              omega
            have hR : X₁.length ≤ (encodeBitsSym inst.target).length + 3 := by
              dsimp [X₁]; simp [List.length_append]
            calc
              (X₀ ++ [Sym.boundary]).getD (((encodeBitsSym inst.target).length + 3 : ℕ)) Sym.blank
                  = X₀.getD (((encodeBitsSym inst.target).length + 3 : ℕ)) Sym.blank := r7_getD_append_left X₀ [Sym.boundary] Sym.blank (((encodeBitsSym inst.target).length + 3 : ℕ)) hL₀
              _ = (encodeElementsSym inst.elements).getD (((encodeBitsSym inst.target).length + 3) - X₁.length) Sym.blank :=
                    List.getD_append_right X₁ (encodeElementsSym inst.elements) Sym.blank (((encodeBitsSym inst.target).length + 3 : ℕ)) hR
              _ = (encodeElementsSym inst.elements).getD 1 Sym.blank := by
                    congr 1 <;> dsimp [X₁] <;> simp [List.length_append]
          have hn3to : ((((encodeBitsSym inst.target).length + 3 : ℕ) : ℤ).toNat) = (encodeBitsSym inst.target).length + 3 := by omega
          rw [← List.getD_eq_getElem (encodeInstanceSym inst) Sym.blank hc.2] at hnb
          have hidx : ((((encodeBitsSym inst.target).length : ℤ) + 3).toNat) =
              (encodeBitsSym inst.target).length + 3 := by omega
          rw [hidx] at hnb
          rw [hge] at hnb
          rcases r7l3_elems_getD1_kind hm hpos with hd0 | hd1
          · rw [hnb] at hd0
            exact (by native_decide : SymKind.sel ≠ SymKind.data0) hd0
          · rw [hnb] at hd1
            exact (by native_decide : SymKind.sel ≠ SymKind.data1) hd1
        · rename_i hnc
          have hnb' : Sym.blank.1 ≠ SymKind.sel := by native_decide
          exact hnb' hnb
      · intro hnb
        dsimp [symInitialConfig] at hnb
        split at hnb
        · rename_i hc
          have hge : (encodeInstanceSym inst).getD (((encodeBitsSym inst.target).length + 3 : ℕ)) Sym.blank =
              (encodeElementsSym inst.elements).getD 1 Sym.blank := by
            unfold encodeInstanceSym
            let X₁ : List Sym := [Sym.boundary] ++ encodeBitsSym inst.target ++ [Sym.boundary]
            let X₀ : List Sym := X₁ ++ encodeElementsSym inst.elements
            change (X₀ ++ [Sym.boundary]).getD (((encodeBitsSym inst.target).length + 3 : ℕ)) Sym.blank =
              (encodeElementsSym inst.elements).getD 1 Sym.blank
            have hL₀ : (encodeBitsSym inst.target).length + 3 < X₀.length := by
              dsimp [X₀, X₁]; simp [List.length_append]
              omega
            have hR : X₁.length ≤ (encodeBitsSym inst.target).length + 3 := by
              dsimp [X₁]; simp [List.length_append]
            calc
              (X₀ ++ [Sym.boundary]).getD (((encodeBitsSym inst.target).length + 3 : ℕ)) Sym.blank
                  = X₀.getD (((encodeBitsSym inst.target).length + 3 : ℕ)) Sym.blank := r7_getD_append_left X₀ [Sym.boundary] Sym.blank (((encodeBitsSym inst.target).length + 3 : ℕ)) hL₀
              _ = (encodeElementsSym inst.elements).getD (((encodeBitsSym inst.target).length + 3) - X₁.length) Sym.blank :=
                    List.getD_append_right X₁ (encodeElementsSym inst.elements) Sym.blank (((encodeBitsSym inst.target).length + 3 : ℕ)) hR
              _ = (encodeElementsSym inst.elements).getD 1 Sym.blank := by
                    congr 1 <;> dsimp [X₁] <;> simp [List.length_append]
          have hn3to : ((((encodeBitsSym inst.target).length + 3 : ℕ) : ℤ).toNat) = (encodeBitsSym inst.target).length + 3 := by omega
          rw [← List.getD_eq_getElem (encodeInstanceSym inst) Sym.blank hc.2] at hnb
          have hidx : ((((encodeBitsSym inst.target).length : ℤ) + 3).toNat) =
              (encodeBitsSym inst.target).length + 3 := by omega
          rw [hidx] at hnb
          rw [hge] at hnb
          rcases r7l3_elems_getD1_kind hm hpos with hd0 | hd1
          · rw [hnb] at hd0
            exact (by native_decide : SymKind.nosel ≠ SymKind.data0) hd0
          · rw [hnb] at hd1
            exact (by native_decide : SymKind.nosel ≠ SymKind.data1) hd1
        · rename_i hnc
          have hnb' : Sym.blank.1 ≠ SymKind.nosel := by native_decide
          exact hnb' hnb
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      rcases ih with ⟨hna, hns, hnn⟩
      refine ⟨?_, ?_, ?_⟩
      · intro hnb
        rw [symStepConfig] at hnb
        by_cases hw : ((encodeBitsSym inst.target).length : ℤ) + 3 = cfg'.headPos
        · have hwc : step.result.writeSym.1 = SymKind.alpha := by simpa [hw] using hnb
          have hrd : step.readSym.1 = SymKind.alpha := by
            have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) → r.writeSym.1 = SymKind.alpha →
                  s.1 = SymKind.alpha := by native_decide
            exact hb ⟨cfg'.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev⟩
              step.readSym step.result (by simpa [← hread] using htrans) hwc
          exact hna (by simpa [hw, hread] using hrd)
        · exact hna (by simpa [symStepConfig, hw] using hnb)
      · intro hnb
        rw [symStepConfig] at hnb
        by_cases hw : ((encodeBitsSym inst.target).length : ℤ) + 3 = cfg'.headPos
        · have hwc : step.result.writeSym.1 = SymKind.sel := by simpa [hw] using hnb
          have hrd : step.readSym.1 = SymKind.alpha ∨
              step.readSym.1 = SymKind.sel := by
            have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) → r.writeSym.1 = SymKind.sel →
                  s.1 = SymKind.alpha ∨ s.1 = SymKind.sel := by native_decide
            exact hb ⟨cfg'.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev⟩
              step.readSym step.result (by simpa [← hread] using htrans) hwc
          rcases hrd with hα | hsel
          · exact hna (by simpa [hw, hread] using hα)
          · exact hns (by simpa [hw, hread] using hsel)
        · exact hns (by simpa [symStepConfig, hw] using hnb)
      · intro hnb
        rw [symStepConfig] at hnb
        by_cases hw : ((encodeBitsSym inst.target).length : ℤ) + 3 = cfg'.headPos
        · have hwc : step.result.writeSym.1 = SymKind.nosel := by simpa [hw] using hnb
          have hrd : step.readSym.1 = SymKind.alpha ∨
              step.readSym.1 = SymKind.nosel := by
            have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) → r.writeSym.1 = SymKind.nosel →
                  s.1 = SymKind.alpha ∨ s.1 = SymKind.nosel := by native_decide
            exact hb ⟨cfg'.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev⟩
              step.readSym step.result (by simpa [← hread] using htrans) hwc
          rcases hrd with hα | hnos
          · exact hna (by simpa [hw, hread] using hα)
          · exact hnn (by simpa [hw, hread] using hnos)
        · exact hnn (by simpa [symStepConfig, hw] using hnb)

/-- 51 头域:51 头 ∈ [n+1, L-3](#₀' 域——51 入边唯 21 读 sel/nosel L,marker_pos 限位)。 -/
lemma r7l3_51_domain (inst : SubsetSumInstance) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg)
    (h51 : cfg.state = 51) :
    (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) ≤ cfg.headPos ∧
    cfg.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 3 : ℤ) := by
  induction h with
  | nil => simp [symInitialConfig] at h51
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      have hsrc := q12_into_51 cfg'.state
        (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
        step.readSym step.result (by simpa [hread] using htrans) (by simpa [symStepConfig] using h51)
      rcases hsrc with ⟨hq21, hrd, hdL⟩
      have hmp := r7l3_marker_pos inst hprev cfg'.headPos (by
        rcases hrd with hsel | hnosel
        · rw [← hread]
          exact Or.inr (Or.inl hsel)
        · rw [← hread]
          exact Or.inr (Or.inr hnosel))
      constructor
      · simp [symStepConfig, hdL, Dir.toInt]
        rw [r7_enc_len] at hmp
        omega
      · simp [symStepConfig, hdL, Dir.toInt]
        rw [r7_enc_len] at hmp ⊢
        omega

/-- 可达 cfg 的负头格(j < 0)恒非 boundary(写 boundary 者读 boundary(负位无)或 51(头域 ≥ n+1))。 -/
lemma r7l3_neg_no_boundary (inst : SubsetSumInstance) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg) :
    ∀ j : ℤ, j < 0 → (cfg.tape j).1 ≠ SymKind.boundary := by
  induction h with
  | nil =>
      intro j hj
      dsimp [symInitialConfig]
      split
      · rename_i hc
        exfalso
        omega
      · native_decide
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      intro j hj
      dsimp [symStepConfig]
      by_cases hw : j = cfg'.headPos
      · by_cases hb : (step.result.writeSym).1 = SymKind.boundary
        · have hcls := r7_write_boundary_class cfg'.state
            (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
            step.readSym step.result (by simpa [hread] using htrans) hb
          rcases hcls with hrdb | h51
          · exfalso
            have hnb := ih cfg'.headPos (by omega)
            have hrd' : (cfg'.tape cfg'.headPos).1 = SymKind.boundary := by
              rw [← hread]
              exact hrdb
            exact hnb hrd'
          · have hd51 := r7l3_51_domain inst hprev (by simpa [symStepConfig] using h51)
            omega
        · simpa [hw] using hb
      · have hp' : (cfg'.tape j).1 ≠ SymKind.boundary := ih j hj
        simpa [hw] using hp'

/-- 86 入边:85 读 boundary R(清 m 起点)或 86 自环 R(清 m 中)。 -/
lemma r7l3_into_86 (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h86 : r.nextState = 86) :
    (q = 85 ∧ s.1 = SymKind.boundary ∧ r.moveDir = Dir.R) ∨
      (q = 86 ∧ r.moveDir = Dir.R) := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 86 →
      ((q : ℕ) = 85 ∧ s.1 = SymKind.boundary ∧ r.moveDir = Dir.R) ∨
        ((q : ℕ) = 86 ∧ r.moveDir = Dir.R) := by native_decide
  exact hb ⟨q, hq⟩ s r hr h86

/-- 86 头 ≥ 1(86 从 85 读 boundary R(85 头 ≥ 0——负头格非 boundary)或 86 自环 R 保持)。 -/
lemma r7l3_86_head (inst : SubsetSumInstance) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg) :
    cfg.state = 86 → (1 : ℤ) ≤ cfg.headPos := by
  intro h86
  induction h with
  | nil => simp [symInitialConfig] at h86
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      have hsrc := r7l3_into_86 cfg'.state
        (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
        step.readSym step.result (by simpa [hread] using htrans) (by simpa [symStepConfig] using h86)
      rcases hsrc with h85 | h86s
      · rcases h85 with ⟨hq85, hrdb, hdR⟩
        have hge0 : (0 : ℤ) ≤ cfg'.headPos := by
          by_contra hlt
          have hnb := r7l3_neg_no_boundary inst hprev cfg'.headPos (by omega)
          have hrd' : (cfg'.tape cfg'.headPos).1 = SymKind.boundary := by
            rw [← hread]
            exact hrdb
          exact hnb hrd'
        simp [symStepConfig, hdR, Dir.toInt]
        omega
      · rcases h86s with ⟨hq86s, hdR⟩
        have hge1 := ih hq86s
        simp [symStepConfig, hdR, Dir.toInt]
        omega

/-- 87 入边:86 m=false → 87 S 或 87 自环 R(读 data)。 -/
lemma r7l3_into_87 (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h87 : r.nextState = 87) :
    (q = 86 ∧ r.moveDir = Dir.S) ∨ (q = 87 ∧ r.moveDir = Dir.R) := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 87 →
      ((q : ℕ) = 86 ∧ r.moveDir = Dir.S) ∨ ((q : ℕ) = 87 ∧ r.moveDir = Dir.R) := by
    native_decide
  exact hb ⟨q, hq⟩ s r hr h87

/-- 87 头 ≥ 1(87 从 86 S(86 头 ≥ 1)或 87 自环 R(读 data——0 格 #ₗ 非 data)保持)。 -/
lemma r7l3_87_head (inst : SubsetSumInstance) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg) :
    cfg.state = 87 → (1 : ℤ) ≤ cfg.headPos := by
  intro h87
  induction h with
  | nil => simp [symInitialConfig] at h87
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      have hsrc := r7l3_into_87 cfg'.state
        (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
        step.readSym step.result (by simpa [hread] using htrans) (by simpa [symStepConfig] using h87)
      rcases hsrc with h86s | h87s
      · rcases h86s with ⟨hq86, hdS⟩
        have hge1 := r7l3_86_head inst hprev (by simpa [symStepConfig] using hq86)
        simp [symStepConfig, hdS, Dir.toInt]
        omega
      · rcases h87s with ⟨hq87s, hdR⟩
        have hge1 := ih hq87s
        simp [symStepConfig, hdR, Dir.toInt]
        omega

/-- 20 头 ≥ 1(20 入边 87 S(87 头 ≥ 1)或 4 L(4 读 nosel——marker_pos 限元素区))。 -/
lemma r7l3_20_head (inst : SubsetSumInstance) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg) :
    cfg.state = 20 → (1 : ℤ) ≤ cfg.headPos := by
  intro h20
  induction h with
  | nil => simp [symInitialConfig] at h20
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      have hsrc := r7_into_20_class cfg'.state
        (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
        step.readSym step.result (by simpa [hread] using htrans) (by simpa [symStepConfig] using h20)
      rcases hsrc with h87s | h4l
      · rcases h87s with ⟨hq87, hdS⟩
        have hge1 := r7l3_87_head inst hprev (by simpa [symStepConfig] using hq87)
        simp [symStepConfig, hdS, Dir.toInt]
        omega
      · rcases h4l with ⟨hq4, hdL⟩
        have hnos : step.readSym.1 = SymKind.nosel := by
          have hb : ∀ s : Sym, ∀ r : SymTransResult,
              r ∈ VerifierSym.transition (4, s) → r.nextState = 20 → s.1 = SymKind.nosel := by
            native_decide
          exact hb step.readSym step.result (by simpa [← hread, hq4] using htrans) (by simpa [symStepConfig] using h20)
        have hmp := r7l3_marker_pos inst hprev cfg'.headPos (by
          rw [← hread]
          exact Or.inr (Or.inr hnos))
        simp [symStepConfig, hdL, Dir.toInt]
        rw [r7_enc_len] at hmp
        omega


theorem r7_path_bundle (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (hpos : ∀ v ∈ inst.elements, 0 < v)
    (htarget : 0 < inst.target) :
    ∀ (π : List SymStep) (cfg : SymConfig),
      SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg →
      (∃ (π₂ : List SymStep) (cfg₂ : SymConfig),
          SymReachablePath VerifierSym.transition (encodeInstanceSym inst) (π ++ π₂) cfg₂ ∧
          cfg₂.state = 100) →
      (cfg.state = 100 ∨ cfg.state = 101 ∨
        cfg.headPos < ((encodeInstanceSym inst).length : ℤ)) ∧
      (∀ j : ℤ, (((encodeInstanceSym inst).length : ℕ) : ℤ) ≤ j →
        cfg.tape j = Sym.blank) ∧
      (r7_E cfg.state → ∀ step ∈ π, r7_E step.fromState) ∧
      (cfg.state = 1 → cfg.headPos ≤ (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ)) ∧
      (cfg.state = 28 → cfg.headPos ≤ (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ)) ∧
      (cfg.state = 87 → cfg.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ)) ∧
      (cfg.state = 20 → cfg.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ)) ∧
      (cfg.state = 23 → cfg.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ)) ∧
      (cfg.state = 81 → cfg.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ)) ∧
      ((cfg.state = 9 ∨ cfg.state = 38 ∨ cfg.state = 77 ∨ cfg.state = 85) →
        cfg.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ)) ∧
      ((cfg.state = 12 ∨ cfg.state = 11 ∨ cfg.state = 14) →
        cfg.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ)) ∧
      (cfg.state = 10 → cfg.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ)) ∧
      (r7_E cfg.state →
        (cfg.tape (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ)).1 = SymKind.boundary) ∧
      ((cfg.state = 1) → cfg.headPos ≤ (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ)) ∧
      ((cfg.state = 1) → (1 : ℤ) ≤ cfg.headPos) ∧
      ((cfg.state = 1) →
        (cfg.tape (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ)).1 = SymKind.alpha) ∧
      ((cfg.state = 2) →
        (((cfg.tape (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ)).1 = SymKind.alpha ∨
          (cfg.tape (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ)).1 = SymKind.sel ∨
          (cfg.tape (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ)).1 = SymKind.nosel) ∧
        ((((encodeBitsSym inst.target).length : ℤ) + 3 ≤ cfg.headPos) →
          (cfg.tape (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ)).1 = SymKind.sel ∨
          (cfg.tape (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ)).1 = SymKind.nosel) ∧
        (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ cfg.headPos)) ∧
      ((cfg.state = 3 ∨ cfg.state = 24 ∨ cfg.state = 29 ∨ cfg.state = 26 ∨
          cfg.state = 27 ∨ cfg.state = 38 ∨ cfg.state = 28) →
        (cfg.tape (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ)).1 = SymKind.sel ∨
        (cfg.tape (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ)).1 = SymKind.nosel) ∧
      ((cfg.tape (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ)).1 = SymKind.boundary ∨
        cfg.tape (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) = Sym.mk SymKind.data0 false ∨
        (cfg.tape (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ)).1 = SymKind.data1 ∨
        cfg.tape (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) = Sym.mk SymKind.data0 true ∨
        (cfg.tape (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ)).1 = SymKind.consumed) ∧
      ((cfg.tape 0).1 = SymKind.boundary) ∧
      ((cfg.tape (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ)).1 = SymKind.boundary) ∧
      (∀ p : ℤ, (cfg.tape p).1 = SymKind.boundary →
        p = 0 ∨ p = (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) ∨
        (((encodeBitsSym inst.target).length + 1 : ℤ) ≤ p ∧
          p ≤ (((encodeInstanceSym inst).length : ℕ) - 3 : ℤ))) := by
  intro π cfg h hext
  induction h with
  | nil =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · right; right
        dsimp [symInitialConfig]
        have hlen : 0 < (encodeInstanceSym inst).length := by
          rw [r7_enc_len]
          omega
        omega
      · -- Pblank（nil: 初始 cfg 的带外（≥ L）恒 blank——输入有限）
        intro j hj
        have hj0 : (0 : ℤ) ≤ j := by omega
        have hnot : ¬ j.toNat < (encodeInstanceSym inst).length := by
          intro h
          have hz : (j.toNat : ℤ) < ((encodeInstanceSym inst).length : ℤ) := by exact_mod_cast h
          have hnat : ((encodeInstanceSym inst).length : ℤ) ≤ (j.toNat : ℤ) := by
            rw [Int.toNat_of_nonneg hj0]
            omega
          omega
        dsimp [symInitialConfig]
        simp [hj0, hnot]
      · -- P0e: E 族封闭（nil: 路径空——空真）
        intro hE
        intro step hmem
        simp at hmem
      · intro h1; simp [symInitialConfig] at h1
      · intro h28; simp [symInitialConfig] at h28
      · intro h87; simp [symInitialConfig] at h87
      · intro h20; simp [symInitialConfig] at h20
      · intro h23; simp [symInitialConfig] at h23
      · intro h81; simp [symInitialConfig] at h81
      · intro h9A; simp [symInitialConfig] at h9A
      · intro h12c; simp [symInitialConfig] at h12c
      · intro h10; simp [symInitialConfig] at h10
      · -- P10'0（E 态 → #₀ .1 = boundary）：初始态 0 ∈ E——#₀ 位 = boundary
        intro hE
        have hpos : (0 : ℤ) ≤ ((encodeBitsSym inst.target).length + 1 : ℕ) ∧
            (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ).toNat < (encodeInstanceSym inst).length := by
          constructor
          · omega
          · rw [r7_enc_len]
            have hE' : 1 ≤ (encodeElementsSym inst.elements).length := hm
            omega
        dsimp [symInitialConfig]
        split
        · rename_i hc
          have hge : (encodeInstanceSym inst).getD (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ).toNat Sym.blank =
              (encodeInstanceSym inst)[(((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ).toNat] :=
            List.getD_eq_getElem (encodeInstanceSym inst) Sym.blank hc.2
          have hmid : (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ).toNat =
              (encodeBitsSym inst.target).length + 1 := by omega
          have hmidb := r7_enc_getD_mid inst
          have heq : (encodeInstanceSym inst).getD (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ).toNat Sym.blank =
              (encodeInstanceSym inst).getD ((encodeBitsSym inst.target).length + 1) Sym.blank := by
            rw [hmid]
          have hfull : (encodeInstanceSym inst)[(((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ).toNat] =
              Sym.boundary := by
            calc
              (encodeInstanceSym inst)[(((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ).toNat]
                  = (encodeInstanceSym inst).getD (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ).toNat Sym.blank := hge.symm
              _ = (encodeInstanceSym inst).getD ((encodeBitsSym inst.target).length + 1) Sym.blank := heq
              _ = Sym.boundary := hmidb
          exact congrArg (fun x : Sym => x.1) hfull
        · rename_i hnc
          exfalso
          exact hnc hpos
      · -- P10'1a（1 态 → 头 ≤ n+1）：初始态 0——前件假
        intro h1
        simp [symInitialConfig] at h1
      · -- P10'-1b（1 态 → 头 ≥ 1）：初始态 0——前件假
        intro h1
        simp [symInitialConfig] at h1
      · -- P10'-1c（1 态 → 首格 α）：初始态 0——前件假
        intro h1
        simp [symInitialConfig] at h1
      · -- P10'-2（2 态）：初始态 0——前件假
        intro h2
        simp [symInitialConfig] at h2
      · -- P10'-3（格式段态）：初始态 0——前件假
        intro hF
        rcases hF with h3 | h24 | h29 | h26 | h27 | h38 | h28
        · simp [symInitialConfig] at h3
        · simp [symInitialConfig] at h24
        · simp [symInitialConfig] at h29
        · simp [symInitialConfig] at h26
        · simp [symInitialConfig] at h27
        · simp [symInitialConfig] at h38
        · simp [symInitialConfig] at h28
      · -- P11（#₀ 位）：位置 n+1 = boundary
        left
        have hpos : (0 : ℤ) ≤ ((encodeBitsSym inst.target).length + 1 : ℕ) ∧
            (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ).toNat < (encodeInstanceSym inst).length := by
          constructor
          · omega
          · rw [r7_enc_len]
            have hE : 1 ≤ (encodeElementsSym inst.elements).length := hm
            omega
        dsimp [symInitialConfig]
        split
        · rename_i hc
          have hge : (encodeInstanceSym inst).getD (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ).toNat Sym.blank =
              (encodeInstanceSym inst)[(((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ).toNat] :=
            List.getD_eq_getElem (encodeInstanceSym inst) Sym.blank hc.2
          have hmid : (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ).toNat =
              (encodeBitsSym inst.target).length + 1 := by omega
          have hmidb := r7_enc_getD_mid inst
          have heq : (encodeInstanceSym inst).getD (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ).toNat Sym.blank =
              (encodeInstanceSym inst).getD ((encodeBitsSym inst.target).length + 1) Sym.blank := by
            rw [hmid]
          have hfull : (encodeInstanceSym inst)[(((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ).toNat] =
              Sym.boundary := by
            calc
              (encodeInstanceSym inst)[(((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ).toNat]
                  = (encodeInstanceSym inst).getD (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ).toNat Sym.blank := hge.symm
              _ = (encodeInstanceSym inst).getD ((encodeBitsSym inst.target).length + 1) Sym.blank := heq
              _ = Sym.boundary := hmidb
          exact congrArg (fun x : Sym => x.1) hfull
        · rename_i hnc
          exfalso
          exact hnc hpos
      · -- P6l: tape 0 = #ₗ
        have hlen : 0 < (encodeInstanceSym inst).length := by
          rw [r7_enc_len]
          omega
        dsimp [symInitialConfig]
        split
        · rename_i hc
          have hge : (encodeInstanceSym inst).getD 0 Sym.blank = (encodeInstanceSym inst)[0] :=
            List.getD_eq_getElem (encodeInstanceSym inst) Sym.blank (by simpa using hlen)
          exact (congrArg (fun x : Sym => x.1) hge.symm).trans
            (congrArg (fun x : Sym => x.1) (r7_enc_getD_0 inst))
        · rename_i hnc
          exfalso
          have hlt : ((0 : ℤ).toNat) < (encodeInstanceSym inst).length := by simpa using hlen
          exact hnc ⟨by omega, hlt⟩
      · -- P6r: tape (L-1) = #₁
        have hlen : 0 < (encodeInstanceSym inst).length := by
          rw [r7_enc_len]
          omega
        have hcast : (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ).toNat =
            (encodeInstanceSym inst).length - 1 := by
          rw [show (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) =
              (((encodeInstanceSym inst).length - 1 : ℕ) : ℤ) from by omega]
          rfl
        dsimp [symInitialConfig]
        split
        · rename_i hc
          have hge : (encodeInstanceSym inst).getD (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ).toNat Sym.blank =
              (encodeInstanceSym inst)[(((encodeInstanceSym inst).length : ℕ) - 1 : ℤ).toNat] :=
            List.getD_eq_getElem (encodeInstanceSym inst) Sym.blank hc.2
          have heq : (encodeInstanceSym inst).getD (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ).toNat Sym.blank =
              (encodeInstanceSym inst).getD ((encodeInstanceSym inst).length - 1) Sym.blank := by
            rw [hcast]
          calc
            ((encodeInstanceSym inst)[(((encodeInstanceSym inst).length : ℕ) - 1 : ℤ).toNat]).1
                = ((encodeInstanceSym inst).getD (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ).toNat Sym.blank).1 :=
                  congrArg (fun s : Sym => s.1) hge.symm
            _ = ((encodeInstanceSym inst).getD ((encodeInstanceSym inst).length - 1) Sym.blank).1 :=
                  congrArg (fun s : Sym => s.1) heq
            _ = SymKind.boundary := congrArg (fun s : Sym => s.1) (r7_enc_getD_last inst)
        · rename_i hnc
          exfalso
          have hge : (0 : ℤ) ≤ (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by
            rw [r7_enc_len]
            omega
          have hlt : (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ).toNat <
              (encodeInstanceSym inst).length := by
            rw [hcast]
            rw [r7_enc_len]
            omega
          exact hnc ⟨hge, hlt⟩
      · -- P9: 带上 boundary 只在 0 / L-1 / [|bits|+1, L-3]
        intro p hp
        dsimp [symInitialConfig] at hp
        by_cases hpos : 0 ≤ p ∧ p.toNat < (encodeInstanceSym inst).length
        · -- 带内：从 hp 的 if 真支提取 get 格
          have hval : (if h : 0 ≤ p ∧ p.toNat < (encodeInstanceSym inst).length
              then (encodeInstanceSym inst).get ⟨p.toNat, h.2⟩ else Sym.blank) =
              (encodeInstanceSym inst).get ⟨p.toNat, hpos.2⟩ := by
            split
            · rename_i hc
              congr 1
            · rename_i hnc
              exfalso
              exact hnc hpos
          have hget : ((encodeInstanceSym inst).get ⟨p.toNat, hpos.2⟩).1 = SymKind.boundary := by
            exact (congrArg (fun x : Sym => x.1) hval).symm.trans hp
          have hk : ((encodeInstanceSym inst).getD p.toNat Sym.blank).1 = SymKind.boundary := by
            rw [List.getD_eq_getElem (encodeInstanceSym inst) Sym.blank hpos.2]
            exact hget
          rw [show p = (p.toNat : ℤ) from by omega]
          by_cases h0 : p.toNat = 0
          · left
            omega
          by_cases hlast : p.toNat = (encodeInstanceSym inst).length - 1
          · right; left
            omega
          right; right
          by_cases hmid : p.toNat = (encodeBitsSym inst.target).length + 1
          · have hmidle : (encodeBitsSym inst.target).length + 1 ≤
                (encodeInstanceSym inst).length - 3 := by
              rw [r7_enc_len]
              have hE : 1 ≤ (encodeElementsSym inst.elements).length := hm
              omega
            constructor <;> omega
          have hlt : p.toNat < (encodeInstanceSym inst).length := hpos.2
          have hsplit : p.toNat ≤ (encodeBitsSym inst.target).length ∨
              (encodeBitsSym inst.target).length + 2 ≤ p.toNat := by
            rw [r7_enc_len] at hlt
            omega
          rcases hsplit with hle | hge
          · -- p 在 target 区（非 boundary——r7_enc_getD_bits_kind 排除）
            exfalso
            have hj : p.toNat - 1 < (encodeBitsSym inst.target).length := by omega
            have hnb := r7_enc_getD_bits_kind inst (j := p.toNat - 1) hj
            have heq : p.toNat = 1 + (p.toNat - 1) := by omega
            rw [heq] at hk
            exact hnb hk
          · -- p 在元素区（非 boundary——r7_enc_getD_elems_kind 排除）
            exfalso
            have hj : p.toNat - ((encodeBitsSym inst.target).length + 2) <
                (encodeElementsSym inst.elements).length := by
              rw [r7_enc_len] at hlt
              rw [r7_enc_len] at hlast
              omega
            have hnb := r7_enc_getD_elems_kind inst
              (j := p.toNat - ((encodeBitsSym inst.target).length + 2)) hj
            have heq : p.toNat = (encodeBitsSym inst.target).length + 2 +
                (p.toNat - ((encodeBitsSym inst.target).length + 2)) := by omega
            rw [heq] at hk
            exact hnb hk
        · -- 带外：tape p = blank——kind 非 boundary 矛盾
          exfalso
          have hval : (if h : 0 ≤ p ∧ p.toNat < (encodeInstanceSym inst).length
              then (encodeInstanceSym inst).get ⟨p.toNat, h.2⟩ else Sym.blank) = Sym.blank := by
            split
            · rename_i hc
              exfalso
              exact hpos hc
            · rfl
          have hb : Sym.blank.1 = SymKind.boundary := by
            exact (congrArg (fun x : Sym => x.1) hval).symm.trans hp
          have hnb : Sym.blank.1 ≠ SymKind.boundary := by native_decide
          exact hnb hb
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      rcases hext with ⟨π₂, cfg₂, hpath₂, hacc₂⟩
      have hext₀ : ∃ (π₀₂ : List SymStep) (cfg₀₂ : SymConfig),
          SymReachablePath VerifierSym.transition (encodeInstanceSym inst) (π₀ ++ π₀₂) cfg₀₂ ∧
          cfg₀₂.state = 100 := by
        refine ⟨[step] ++ π₂, cfg₂, ?_, hacc₂⟩
        simpa [List.append_assoc] using hpath₂
      rcases ih hext₀ with ⟨hP0, hPblank, hP0e, h1, h28, h87, h20, h23, h81, h9A, h12c, h10,
        hP10'0, hP10'1, hP10'1b, hP10'1c, hP10'2, hP10'F, hP11, hP6l, hP6r, hP9⟩
      have htrans' : step.result ∈ VerifierSym.transition (cfg'.state, step.readSym) := by
        simpa [hread] using htrans
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- P0'
        by_cases h100 : cfg'.state = 100
        · left
          have ha := r7_100_absorb cfg'.state (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
            step.readSym step.result htrans' h100
          simpa [symStepConfig] using ha.1
        by_cases h101 : cfg'.state = 101
        · right; left
          have ha := r7_101_absorb_move cfg'.state (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
            step.readSym step.result htrans' h101
          simpa [symStepConfig] using ha.1
        · -- 目标保持 P0' 整析取；各分支按需 right; right
          have hpos0 : cfg'.headPos < ((encodeInstanceSym inst).length : ℤ) := by
            rcases hP0 with h100' | h101' | hlt
            · exfalso; exact h100 h100'
            · exfalso; exact h101 h101'
            · exact hlt
          have hq0 : cfg'.state < 102 := q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev
          have hleg' : cfg'.state ∈ legalStates := r7_path_state_legal (encodeInstanceSym inst) π₀ cfg' hprev
          have hleg : r7_legalState cfg'.state := r7_all_legal cfg'.state hleg'
          rcases hleg with hA | hB | h100'' | h101''
          · -- A 支
            rcases hd : step.result.moveDir with hL | hR | hS
            · simp [symStepConfig, hd, Dir.toInt]
              right; right
              omega
            · -- R:A@pos₀ R
              by_cases hlast : cfg'.headPos = (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ)
              · -- @(encodeInstanceSym inst).length-1 读 #₁:r7_A_boundary_R_class
                have hreadb : step.readSym.1 = SymKind.boundary := by
                  rw [hread]
                  simpa [hlast] using hP6r
                have hcls := r7_A_boundary_R_class cfg'.state hq0 step.readSym step.result htrans'
                  hA hreadb hd
                rcases hcls with hqset | h100''' | h101'''
                · -- q ∈ AboundSet:排除
                  have hqset' : cfg'.state = 0 ∨ cfg'.state = 1 ∨ cfg'.state = 9 ∨ cfg'.state = 38 ∨
                      cfg'.state = 77 ∨ cfg'.state = 85 ∨ cfg'.state = 28 ∨ cfg'.state = 12 ∨
                      cfg'.state = 11 ∨ cfg'.state = 14 := by
                    simpa [r7_AboundSet] using hqset
                  have hn2 : ((encodeBitsSym inst.target).length + 2 : ℤ) <
                      ((encodeInstanceSym inst).length : ℤ) - 1 := by
                    rw [r7_enc_len]
                    have hE : 1 ≤ (encodeElementsSym inst.elements).length := hm
                    omega
                  rcases hqset' with hq0' | hq1 | hq9 | hq38 | hq77 | hq85 | hq28 | hq12 | hq11 | hq14
                  · -- q = 0:头 = 0
                    cases hprev with
                    | nil =>
                        exfalso
                        dsimp [symInitialConfig] at hlast
                        have hL : (0 : ℤ) < (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by
                          rw [r7_enc_len]
                          have hE : 1 ≤ (encodeElementsSym inst.elements).length := hm
                          omega
                        omega
                    | cons π₀₀ step₀ cfg₀ hprev₀ hfrom₀ hread₀ htrans₀ =>
                        exfalso
                        have hbad : step₀.result.nextState = 0 := by
                          simpa [symStepConfig] using hq0'
                        exact (by
                          have hb0 : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                              r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 0 → False := by
                            native_decide
                          exact hb0 ⟨cfg₀.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀₀ cfg₀ hprev₀⟩
                            step₀.readSym step₀.result (by simpa [hread₀] using htrans₀) hbad)
                  · have hle : cfg'.headPos ≤ (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) := h1 hq1
                    right; right
                    omega
                  · have hle : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h9A (Or.inl hq9)
                    right; right
                    omega
                  · have hle : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h9A (Or.inr (Or.inl hq38))
                    right; right
                    omega
                  · have hle : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h9A (Or.inr (Or.inr (Or.inl hq77)))
                    right; right
                    omega
                  · have hle : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h9A (Or.inr (Or.inr (Or.inr hq85)))
                    right; right
                    omega
                  · have hle : cfg'.headPos ≤ (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) := h28 hq28
                    right; right
                    omega
                  · have hle : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h12c (Or.inl hq12)
                    right; right
                    omega
                  · have hle : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h12c (Or.inr (Or.inl hq11))
                    right; right
                    omega
                  · have hle : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h12c (Or.inr (Or.inr hq14))
                    right; right
                    omega
                · left
                  simpa [symStepConfig] using h100'''
                · right; left
                  simpa [symStepConfig] using h101'''
              · -- pos₀ ≤ (encodeInstanceSym inst).length-2:pos ≤ (encodeInstanceSym inst).length-1 < (encodeInstanceSym inst).length
                simp [symStepConfig, hd, Dir.toInt]
                right; right
                omega
            · simp [symStepConfig, hd, Dir.toInt]
              right; right
              omega
          · -- B 支
            rcases hd : step.result.moveDir with hL | hR | hS
            · simp [symStepConfig, hd, Dir.toInt]
              right; right
              omega
            · -- R:B@pos₀ R
              by_cases hlast : cfg'.headPos = (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ)
              · -- @(encodeInstanceSym inst).length-1 读 #₁:Rset 分类
                have hreadb : step.readSym.1 = SymKind.boundary := by
                  rw [hread]
                  simpa [hlast] using hP6r
                rcases hmark : step.readSym.2 with hmf | hmt
                · have hcls := r7_boundary_false_R_class cfg'.state step.readSym step.result
                    hq0 hreadb hmark htrans' hd
                  rcases hcls with hq0' | hq1 | hq38 | hq28 | hq77 | hq9 | hq12 | hq11 | hq14 | hq81 | hq85 | hq20 | hq23 | h100''' | h101'''
                  · cases hprev with
                    | nil =>
                        exfalso
                        dsimp [symInitialConfig] at hlast
                        have hL : (0 : ℤ) < (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by
                          rw [r7_enc_len]
                          have hE : 1 ≤ (encodeElementsSym inst.elements).length := hm
                          omega
                        omega
                    | cons π₀₀ step₀ cfg₀ hprev₀ hfrom₀ hread₀ htrans₀ =>
                        exfalso
                        have hbad : step₀.result.nextState = 0 := by
                          simpa [symStepConfig] using hq0'
                        exact (by
                          have hb0 : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                              r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 0 → False := by
                            native_decide
                          exact hb0 ⟨cfg₀.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀₀ cfg₀ hprev₀⟩
                            step₀.readSym step₀.result (by simpa [hread₀] using htrans₀) hbad)
                  · have hle : cfg'.headPos ≤ (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) := h1 hq1
                    right; right
                    omega
                  · have hle : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h9A (Or.inr (Or.inl hq38))
                    right; right
                    omega
                  · have hle : cfg'.headPos ≤ (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) := h28 hq28
                    right; right
                    omega
                  · have hle : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h9A (Or.inr (Or.inr (Or.inl hq77)))
                    right; right
                    omega
                  · have hle : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h9A (Or.inl hq9)
                    right; right
                    omega
                  · have hle : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h12c (Or.inl hq12)
                    right; right
                    omega
                  · have hle : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h12c (Or.inr (Or.inl hq11))
                    right; right
                    omega
                  · have hle : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h12c (Or.inr (Or.inr hq14))
                    right; right
                    omega
                  · have hle : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h81 hq81
                    right; right
                    omega
                  · have hle : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h9A (Or.inr (Or.inr (Or.inr hq85)))
                    right; right
                    omega
                  · have hle : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := h20 hq20
                    right; right
                    by_cases hL1 : cfg'.headPos = (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ)
                    · -- 20@L-1 读 boundary R → 步后 21@L：带外漂——sym_drift_no_accept q=21 与 hext 矛盾
                      exfalso
                      have hq21 : (symStepConfig cfg' step.result).state = 21 := by
                        have hb : ∀ s : Sym, ∀ r : SymTransResult,
                            r ∈ VerifierSym.transition (20, s) → s.1 = SymKind.boundary → r.moveDir = Dir.R →
                              r.nextState = 21 := by
                          native_decide
                        have hns := hb step.readSym step.result (by simpa [hq20] using htrans')
                          hreadb hd
                        simpa [symStepConfig] using hns
                      have hge21 : (((encodeInstanceSym inst).length : ℕ) : ℤ) ≤ (symStepConfig cfg' step.result).headPos := by
                        have hh : (symStepConfig cfg' step.result).headPos = (((encodeInstanceSym inst).length : ℕ) : ℤ) := by
                          simp [symStepConfig, hd, Dir.toInt, hL1]
                        rw [hh]
                      have hpathc : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) (π₀ ++ [step]) (symStepConfig cfg' step.result) := by
                        exact SymReachablePath.cons π₀ step cfg' hprev hfrom hread htrans
                      have hdr21 : ∀ s : Sym, IsOutside s → ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition (21, s) → r.nextState = 21 ∧ r.moveDir = Dir.R ∧ IsOutside r.writeSym := by
                        intro s hs r hr
                        unfold IsOutside at hs
                        exact ⟨sym_21_drift_state s r hr hs, sym_21_drift_dir s r hr hs,
                          by unfold IsOutside; exact sym_21_drift_write s r hr hs⟩
                      exact sym_drift_no_accept 21 (encodeInstanceSym inst) hpathc hq21 hge21 (by norm_num) hdr21
                        ⟨π₂, cfg₂, hpath₂, hacc₂⟩
                    · omega
                  · have hle : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h23 hq23
                    right; right
                    omega
                  · left
                    simpa [symStepConfig] using h100'''
                  · right; left
                    simpa [symStepConfig] using h101'''
                · have hcls := r7_boundary_true_R_class cfg'.state step.readSym step.result
                    hq0 hreadb hmark htrans' hd
                  rcases hcls with hq0' | hq1 | hq28 | hq77 | hq9 | hq11 | hq14 | hq81 | hq85 | hq20 | hq23 | h100''' | h101'''
                  · cases hprev with
                    | nil =>
                        exfalso
                        dsimp [symInitialConfig] at hlast
                        have hL : (0 : ℤ) < (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by
                          rw [r7_enc_len]
                          have hE : 1 ≤ (encodeElementsSym inst.elements).length := hm
                          omega
                        omega
                    | cons π₀₀ step₀ cfg₀ hprev₀ hfrom₀ hread₀ htrans₀ =>
                        exfalso
                        have hbad : step₀.result.nextState = 0 := by
                          simpa [symStepConfig] using hq0'
                        exact (by
                          have hb0 : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                              r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 0 → False := by
                            native_decide
                          exact hb0 ⟨cfg₀.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀₀ cfg₀ hprev₀⟩
                            step₀.readSym step₀.result (by simpa [hread₀] using htrans₀) hbad)
                  · have hle : cfg'.headPos ≤ (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) := h1 hq1
                    right; right
                    omega
                  · have hle : cfg'.headPos ≤ (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) := h28 hq28
                    right; right
                    omega
                  · have hle : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h9A (Or.inr (Or.inr (Or.inl hq77)))
                    right; right
                    omega
                  · have hle : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h9A (Or.inl hq9)
                    right; right
                    omega
                  · have hle : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h12c (Or.inr (Or.inl hq11))
                    right; right
                    omega
                  · have hle : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h12c (Or.inr (Or.inr hq14))
                    right; right
                    omega
                  · have hle : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h81 hq81
                    right; right
                    omega
                  · have hle : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h9A (Or.inr (Or.inr (Or.inr hq85)))
                    right; right
                    omega
                  · have hle : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := h20 hq20
                    right; right
                    by_cases hL1 : cfg'.headPos = (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ)
                    · -- 20@L-1 读 boundary R → 步后 21@L：带外漂——sym_drift_no_accept q=21 与 hext 矛盾
                      exfalso
                      have hq21 : (symStepConfig cfg' step.result).state = 21 := by
                        have hb : ∀ s : Sym, ∀ r : SymTransResult,
                            r ∈ VerifierSym.transition (20, s) → s.1 = SymKind.boundary → r.moveDir = Dir.R →
                              r.nextState = 21 := by
                          native_decide
                        have hns := hb step.readSym step.result (by simpa [hq20] using htrans')
                          hreadb hd
                        simpa [symStepConfig] using hns
                      have hge21 : (((encodeInstanceSym inst).length : ℕ) : ℤ) ≤ (symStepConfig cfg' step.result).headPos := by
                        have hh : (symStepConfig cfg' step.result).headPos = (((encodeInstanceSym inst).length : ℕ) : ℤ) := by
                          simp [symStepConfig, hd, Dir.toInt, hL1]
                        rw [hh]
                      have hpathc : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) (π₀ ++ [step]) (symStepConfig cfg' step.result) := by
                        exact SymReachablePath.cons π₀ step cfg' hprev hfrom hread htrans
                      have hdr21 : ∀ s : Sym, IsOutside s → ∀ r : SymTransResult,
                          r ∈ VerifierSym.transition (21, s) → r.nextState = 21 ∧ r.moveDir = Dir.R ∧ IsOutside r.writeSym := by
                        intro s hs r hr
                        unfold IsOutside at hs
                        exact ⟨sym_21_drift_state s r hr hs, sym_21_drift_dir s r hr hs,
                          by unfold IsOutside; exact sym_21_drift_write s r hr hs⟩
                      exact sym_drift_no_accept 21 (encodeInstanceSym inst) hpathc hq21 hge21 (by norm_num) hdr21
                        ⟨π₂, cfg₂, hpath₂, hacc₂⟩
                    · omega
                  · have hle : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h23 hq23
                    right; right
                    omega
                  · left
                    simpa [symStepConfig] using h100'''
                  · right; left
                    simpa [symStepConfig] using h101'''
              · -- pos₀ ≤ (encodeInstanceSym inst).length-2
                simp [symStepConfig, hd, Dir.toInt]
                right; right
                omega
            · simp [symStepConfig, hd, Dir.toInt]
              right; right
              omega
          · exfalso
            exact h100 h100''
          · exfalso
            exact h101 h101''
      · -- Pblank（cons: cfg 带外 = cfg' 带外（写位 < L，P0' hlt）；100/101 写回 = 读 = 带外 blank）
        intro j hj
        by_cases hw : j = cfg'.headPos
        · rcases hP0 with h100' | h101' | hlt
          · have hwreq : ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition (100, s) → r.writeSym = s := by native_decide
            have hwv : step.result.writeSym = step.readSym :=
              hwreq step.readSym step.result (by simpa [h100'] using htrans')
            simp [symStepConfig, hw]
            rw [hwv, hread, ← hw]
            exact hPblank j hj
          · have hwreq : ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition (101, s) → r.writeSym = s := by native_decide
            have hwv : step.result.writeSym = step.readSym :=
              hwreq step.readSym step.result (by simpa [h101'] using htrans')
            simp [symStepConfig, hw]
            rw [hwv, hread, ← hw]
            exact hPblank j hj
          · exfalso
            omega
        · simp [symStepConfig, hw]
          exact hPblank j hj
      · -- P0e: E 族封闭——步后 ∈ E → 源 ∈ E（表级）+ ih 覆盖 π₀
        intro hEc
        have hq' : cfg'.state < 102 := q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev
        have hsrc : r7_E cfg'.state := by
          have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
              r ∈ VerifierSym.transition ((q : ℕ), s) → r7_E r.nextState → r7_E (q : ℕ) := by
            native_decide
          exact hb ⟨cfg'.state, hq'⟩ step.readSym step.result htrans' hEc
        have hih := hP0e hsrc
        intro step' hmem'
        rw [List.mem_append] at hmem'
        rcases hmem' with hmemπ | hmemlast
        · exact hih step' hmemπ
        · have hstep' : step' = step := by
            simpa using hmemlast
          rw [hstep']
          simpa [hfrom.symm] using hsrc
      · -- P1: state = 1 → headPos ≤ n+2（自环读 data 而非首格——P10' 强化挡 data0-串入）
        intro hst
        have hcls := r7_into_1_class cfg'.state (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
          step.readSym step.result htrans' (by simpa [symStepConfig] using hst)
        rcases hcls with hq0 | hq1
        · -- 源 0:0 只在初始（无 nextState=0）——nil 支头 0 → 1@1 ≤ n+2；cons 支矛盾
          cases hprev with
          | nil =>
              have hdm : step.result.moveDir.toInt ≤ 1 := by
                cases step.result.moveDir <;> simp [Dir.toInt]
              simp [symStepConfig, symInitialConfig]
              omega
          | cons π₀₀ step₀ cfg₀ hprev₀ hfrom₀ hread₀ htrans₀ =>
              exfalso
              have hbad : step₀.result.nextState = 0 := by
                simpa [symStepConfig] using hq0
              exact (by
                have hb0 : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                    r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 0 → False := by
                  native_decide
                exact hb0 ⟨cfg₀.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀₀ cfg₀ hprev₀⟩
                  step₀.readSym step₀.result (by simpa [hread₀] using htrans₀) hbad)
        · -- 自环（源 1）：头 ≤ n+2（ih）且读位 ≠ n+2（P10' 强化）
          have hle0 : cfg'.headPos ≤ (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) := h1 hq1
          rcases hd : step.result.moveDir with hL | hR | hS
          · simp [symStepConfig, hd, Dir.toInt]
            omega
          · -- R:读符 ∈ {data0, data1}（表级：1 的 nextState=1 行）且读位 ≠ n+2
            have hd01 : step.readSym.1 = SymKind.data0 ∨ step.readSym.1 = SymKind.data1 := by
              have hb : ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition (1, s) → r.nextState = 1 →
                    s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
                native_decide
              exact hb step.readSym step.result (by simpa [hq1] using htrans') (by simpa [symStepConfig] using hst)
            have hne : cfg'.headPos ≠ (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) := by
              intro hpos
              -- 1 态头 ≤ n+1（P10'1a）——与头 = n+2 矛盾
              have hle' : cfg'.headPos ≤ (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) := hP10'1 hq1
              omega
            have hle1 : cfg'.headPos ≤ (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) := by
              omega
            simp [symStepConfig, hd, Dir.toInt]
            omega
          · simp [symStepConfig, hd, Dir.toInt]
            omega
      · -- P28: state = 28 → headPos ≤ n+2
        intro hst
        have hcls := r7_into_28_class cfg'.state (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
          step.readSym step.result htrans' (by simpa [symStepConfig] using hst)
        rcases hcls with hq38 | hq28
        · -- 源 38：38 读 boundary R（表级）——读位 ∈ {0, n+1}（P9 分类 + E 路径无段 boundary + h9A 排 L-1）→ 步后 ≤ n+2
          have hle38 : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h9A (Or.inr (Or.inl hq38))
          have hpathE : ∀ step ∈ π₀, r7_E step.fromState := hP0e (by simpa [r7_E, hq38])
          have hreadb : step.readSym.1 = SymKind.boundary := by
            have hb : ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition (38, s) → r.nextState = 28 → s.1 = SymKind.boundary := by
              native_decide
            exact hb step.readSym step.result (by simpa [hq38] using htrans') (by simpa [symStepConfig] using hst)
          have hdR : step.result.moveDir = Dir.R := by
            have hb : ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition (38, s) → r.nextState = 28 → r.moveDir = Dir.R := by
              native_decide
            exact hb step.readSym step.result (by simpa [hq38] using htrans') (by simpa [symStepConfig] using hst)
          have hp9 := hP9 cfg'.headPos (by rw [← hread]; exact hreadb)
          rcases hp9 with hp0 | hpL | hpr
          · -- 头 = 0（#ₗ）→ 步后 1 ≤ n+2
            simp [symStepConfig, hdR, Dir.toInt, hp0]
            omega
          · -- 头 = L-1（#₁）：与 h9A（≤ L-4）矛盾
            exfalso
            omega
          · -- 头 ∈ [n+1, L-3]：头 = n+1（#₀）→ 步后 n+2；头 ≥ n+2 → E 路径无段 boundary 矛盾
            rcases hpr with ⟨hpge, hple⟩
            by_cases hn1 : cfg'.headPos = (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ)
            · simp [symStepConfig, hdR, Dir.toInt, hn1]
            · exfalso
              have hsegb := r7_E_no_segment_boundary inst hprev hpathE cfg'.headPos
              -- 需要 n+2 ≤ 头 且 头 ≤ L-3
              have hn2le : (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ cfg'.headPos := by
                omega
              have hnb := hsegb hn2le hple
              -- tape@头 ≠ boundary（hnb）与读 boundary（hreadb）矛盾
              exact hnb (by simpa [hread] using hreadb)
        · -- 自环（源 28）：同 P1——P10' 强化档首格
          have hle0 : cfg'.headPos ≤ (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) := h28 hq28
          rcases hd : step.result.moveDir with hL | hR | hS
          · simp [symStepConfig, hd, Dir.toInt]
            omega
          · -- R
            have hd01 : step.readSym.1 = SymKind.data0 ∨ step.readSym.1 = SymKind.data1 := by
              have hb : ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition (28, s) → r.nextState = 28 →
                    s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
                native_decide
              exact hb step.readSym step.result (by simpa [hq28] using htrans') (by simpa [symStepConfig] using hst)
            have hne : cfg'.headPos ≠ (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) := by
              intro hpos
              -- 28 态时首格 ∈ {sel, nosel}（P10' 第三条）——28 读 sel/nosel → nextState ≠ 28 与自环矛盾
              rcases hP10'F (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hq28)))))) with hsel | hnosel
              · have hb : ∀ s : Sym, ∀ r : SymTransResult,
                    r ∈ VerifierSym.transition (28, s) → s.1 = SymKind.sel → r.nextState ≠ 28 := by
                  native_decide
                have hbad := hb step.readSym step.result (by simpa [hq28] using htrans') (by simpa [hread, hpos] using hsel)
                exact hbad (by simpa [symStepConfig] using hst)
              · have hb : ∀ s : Sym, ∀ r : SymTransResult,
                    r ∈ VerifierSym.transition (28, s) → s.1 = SymKind.nosel → r.nextState ≠ 28 := by
                  native_decide
                have hbad := hb step.readSym step.result (by simpa [hq28] using htrans') (by simpa [hread, hpos] using hnosel)
                exact hbad (by simpa [symStepConfig] using hst)
            have hle1 : cfg'.headPos ≤ (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) := by
              omega
            simp [symStepConfig, hd, Dir.toInt]
            omega
          · simp [symStepConfig, hd, Dir.toInt]
            omega
      · -- P87: state = 87 → headPos ≤ L-1
        intro hst
        have hcls := r7_into_87_class cfg'.state (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
          step.readSym step.result htrans' (by simpa [symStepConfig] using hst)
        rcases hcls with h86 | h87self
        · -- 86 读 → 87 S：87 头 = 86 头 < L（hP0，86 非 100/101）
          rcases h86 with ⟨hq86, hdS⟩
          have hlt86 : cfg'.headPos < ((encodeInstanceSym inst).length : ℤ) := by
            rcases hP0 with h100' | h101' | hlt
            · exfalso
              rw [hq86] at h100'
              norm_num at h100'
            · exfalso
              rw [hq86] at h101'
              norm_num at h101'
            · exact hlt
          simp [symStepConfig, hdS, Dir.toInt]
          omega
        · -- 87 自环（读 data R）：ih ≤ L-1；读位 ≠ L-1（#₁ boundary 非 data）→ 步后 ≤ L-1
          rcases h87self with ⟨hq87, hdR⟩
          have hle0 : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := h87 hq87
          have hd01 : step.readSym.1 = SymKind.data0 ∨ step.readSym.1 = SymKind.data1 := by
            have hb : ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition (87, s) → r.nextState = 87 →
                  s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
              native_decide
            exact hb step.readSym step.result (by simpa [hq87] using htrans') (by simpa [symStepConfig] using hst)
          have hne : cfg'.headPos ≠ (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by
            intro hlast
            have hcell : (cfg'.tape cfg'.headPos).1 = SymKind.boundary := by
              simpa [hlast] using hP6r
            have hcell' : step.readSym.1 = SymKind.boundary := by
              simpa [hread] using hcell
            rcases hd01 with hd0 | hd1
            · have hne0 : SymKind.data0 ≠ SymKind.boundary := by native_decide
              exact hne0 (hd0.symm.trans hcell')
            · have hne1 : SymKind.data1 ≠ SymKind.boundary := by native_decide
              exact hne1 (hd1.symm.trans hcell')
          have hle1 : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := by
            omega
          simp [symStepConfig, hdR, Dir.toInt]
          omega
      · -- P20: state = 20 → headPos ≤ L-1
        intro hst
        have hcls := r7_into_20_class cfg'.state (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
          step.readSym step.result htrans' (by simpa [symStepConfig] using hst)
        rcases hcls with h87s | h4l
        · -- 87 读 boundary → 20 S：20 头 = 87 头 ≤ L-1（ih P87）
          rcases h87s with ⟨hq87, hdS⟩
          have hle0 : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := h87 hq87
          simp [symStepConfig, hdS, Dir.toInt]
          omega
        · -- 4 读 → 20 L：20 头 = 4 头 - 1 < L（hP0，4 非 100/101）
          rcases h4l with ⟨hq4, hdL⟩
          have hlt4 : cfg'.headPos < ((encodeInstanceSym inst).length : ℤ) := by
            rcases hP0 with h100' | h101' | hlt
            · exfalso
              rw [hq4] at h100'
              norm_num at h100'
            · exfalso
              rw [hq4] at h101'
              norm_num at h101'
            · exact hlt
          simp [symStepConfig, hdL, Dir.toInt]
          omega
      · -- P23: state = 23 → headPos ≤ L-2
        intro hst
        have hcls := r7_into_23_class cfg'.state (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
          step.readSym step.result htrans' (by simpa [symStepConfig] using hst)
        rcases hcls with hq22 | hq23
        · -- 22 读 boundary → 23 L：23 头 = 22 头 - 1，22 头 < L（hP0）
          have hlt22 : cfg'.headPos < ((encodeInstanceSym inst).length : ℤ) := by
            rcases hP0 with h100' | h101' | hlt
            · exfalso
              rw [hq22] at h100'
              norm_num at h100'
            · exfalso
              rw [hq22] at h101'
              norm_num at h101'
            · exact hlt
          have hdL : step.result.moveDir = Dir.L := by
            have hb : ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition (22, s) → r.nextState = 23 → r.moveDir = Dir.L := by
              native_decide
            exact hb step.readSym step.result (by simpa [hq22] using htrans') (by simpa [symStepConfig] using hst)
          simp [symStepConfig, hdL, Dir.toInt]
          omega
        · -- 23 自环（读 data0 L）：头减——ih ≤ L-2 保持
          have hle0 : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h23 hq23
          have hdL : step.result.moveDir = Dir.L := by
            have hb : ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition (23, s) → r.nextState = 23 → r.moveDir = Dir.L := by
              native_decide
            exact hb step.readSym step.result (by simpa [hq23] using htrans') (by simpa [symStepConfig] using hst)
          simp [symStepConfig, hdL, Dir.toInt]
          omega
      · -- P81: state = 81 → headPos ≤ L-1
        intro hst
        have hcls := r7_into_81_class cfg'.state (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
          step.readSym step.result htrans' (by simpa [symStepConfig] using hst)
        rcases hcls with hq11 | hq12 | hq14 | hq81
        · -- 11/12/14 读 data → 81 R：81 头 = 源头 + 1 ≤ n+3 ≤ L-1（hm）
          have hle0 : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h12c (Or.inr (Or.inl hq11))
          have hdR : step.result.moveDir = Dir.R := by
            have hb' : ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition (11, s) → r.nextState = 81 → r.moveDir = Dir.R := by
              native_decide
            exact hb' step.readSym step.result (by simpa [hq11] using htrans') (by simpa [symStepConfig] using hst)
          by_cases hL2 : cfg'.headPos = (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ)
          · exfalso
            -- cfg'@L-2 读 data → 81 R@L-1：81@L-1 的漂移链（读 #₁/blank 均 81 R 写回）恒 81，与 hext 矛盾
            have hL1c : (symStepConfig cfg' step.result).headPos =
                (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by
              simp [symStepConfig, hdR, Dir.toInt, hL2]
              omega
            have hq81c : (symStepConfig cfg' step.result).state = 81 := by
              simpa [symStepConfig] using hst
            have hge81c : (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 ≤
                (symStepConfig cfg' step.result).headPos := by
              rw [hL1c]
            have hpathc : SymReachablePath VerifierSym.transition (encodeInstanceSym inst)
                (π₀ ++ [step]) (symStepConfig cfg' step.result) := by
              exact SymReachablePath.cons π₀ step cfg' hprev hfrom hread htrans
            have hbdryc : ((symStepConfig cfg' step.result).tape
                (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ)).1 = SymKind.boundary := by
              have hw : cfg'.headPos ≠ (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by omega
              simp [symStepConfig, Ne.symm hw]
              exact hP6r
            have hblankc : ∀ j : ℤ, (((encodeInstanceSym inst).length : ℕ) : ℤ) ≤ j →
                (symStepConfig cfg' step.result).tape j = Sym.blank := by
              intro j hj
              have hw1 : j ≠ (symStepConfig cfg' step.result).headPos := by omega
              have hw2 : j ≠ cfg'.headPos := by omega
              simp [symStepConfig, hw1, hw2]
              exact hPblank j hj
            exact sym_drift_81_no_accept (encodeInstanceSym inst) hpathc hq81c hge81c
              hbdryc hblankc ⟨π₂, cfg₂, hpath₂, hacc₂⟩
          · simp [symStepConfig, hdR, Dir.toInt]
            omega
        · have hle0 : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h12c (Or.inl hq12)
          have hdR : step.result.moveDir = Dir.R := by
            have hb' : ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition (12, s) → r.nextState = 81 → r.moveDir = Dir.R := by
              native_decide
            exact hb' step.readSym step.result (by simpa [hq12] using htrans') (by simpa [symStepConfig] using hst)
          by_cases hL2 : cfg'.headPos = (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ)
          · exfalso
            -- cfg'@L-2 读 data → 81 R@L-1：81@L-1 的漂移链（读 #₁/blank 均 81 R 写回）恒 81，与 hext 矛盾
            have hL1c : (symStepConfig cfg' step.result).headPos =
                (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by
              simp [symStepConfig, hdR, Dir.toInt, hL2]
              omega
            have hq81c : (symStepConfig cfg' step.result).state = 81 := by
              simpa [symStepConfig] using hst
            have hge81c : (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 ≤
                (symStepConfig cfg' step.result).headPos := by
              rw [hL1c]
            have hpathc : SymReachablePath VerifierSym.transition (encodeInstanceSym inst)
                (π₀ ++ [step]) (symStepConfig cfg' step.result) := by
              exact SymReachablePath.cons π₀ step cfg' hprev hfrom hread htrans
            have hbdryc : ((symStepConfig cfg' step.result).tape
                (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ)).1 = SymKind.boundary := by
              have hw : cfg'.headPos ≠ (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by omega
              simp [symStepConfig, Ne.symm hw]
              exact hP6r
            have hblankc : ∀ j : ℤ, (((encodeInstanceSym inst).length : ℕ) : ℤ) ≤ j →
                (symStepConfig cfg' step.result).tape j = Sym.blank := by
              intro j hj
              have hw1 : j ≠ (symStepConfig cfg' step.result).headPos := by omega
              have hw2 : j ≠ cfg'.headPos := by omega
              simp [symStepConfig, hw1, hw2]
              exact hPblank j hj
            exact sym_drift_81_no_accept (encodeInstanceSym inst) hpathc hq81c hge81c
              hbdryc hblankc ⟨π₂, cfg₂, hpath₂, hacc₂⟩
          · simp [symStepConfig, hdR, Dir.toInt]
            omega
        · have hle0 : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h12c (Or.inr (Or.inr hq14))
          have hdR : step.result.moveDir = Dir.R := by
            have hb' : ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition (14, s) → r.nextState = 81 → r.moveDir = Dir.R := by
              native_decide
            exact hb' step.readSym step.result (by simpa [hq14] using htrans') (by simpa [symStepConfig] using hst)
          by_cases hL2 : cfg'.headPos = (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ)
          · exfalso
            -- cfg'@L-2 读 data → 81 R@L-1：81@L-1 的漂移链（读 #₁/blank 均 81 R 写回）恒 81，与 hext 矛盾
            have hL1c : (symStepConfig cfg' step.result).headPos =
                (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by
              simp [symStepConfig, hdR, Dir.toInt, hL2]
              omega
            have hq81c : (symStepConfig cfg' step.result).state = 81 := by
              simpa [symStepConfig] using hst
            have hge81c : (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 ≤
                (symStepConfig cfg' step.result).headPos := by
              rw [hL1c]
            have hpathc : SymReachablePath VerifierSym.transition (encodeInstanceSym inst)
                (π₀ ++ [step]) (symStepConfig cfg' step.result) := by
              exact SymReachablePath.cons π₀ step cfg' hprev hfrom hread htrans
            have hbdryc : ((symStepConfig cfg' step.result).tape
                (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ)).1 = SymKind.boundary := by
              have hw : cfg'.headPos ≠ (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by omega
              simp [symStepConfig, Ne.symm hw]
              exact hP6r
            have hblankc : ∀ j : ℤ, (((encodeInstanceSym inst).length : ℕ) : ℤ) ≤ j →
                (symStepConfig cfg' step.result).tape j = Sym.blank := by
              intro j hj
              have hw1 : j ≠ (symStepConfig cfg' step.result).headPos := by omega
              have hw2 : j ≠ cfg'.headPos := by omega
              simp [symStepConfig, hw1, hw2]
              exact hPblank j hj
            exact sym_drift_81_no_accept (encodeInstanceSym inst) hpathc hq81c hge81c
              hbdryc hblankc ⟨π₂, cfg₂, hpath₂, hacc₂⟩
          · simp [symStepConfig, hdR, Dir.toInt]
            omega
        · -- 81 自环 R（读 data/boundary）
          -- cfg' 头 ≤ L-2（h81）。cfg'@L-2 读 data/boundary → cfg = 81@L-1：
          -- 其延拓第一步读 #₁@L-1 → 81 R@L → 带外漂（blank 版）与 hext 矛盾。
          have hle0 : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h81 hq81
          have hdR : step.result.moveDir = Dir.R := by
            have hb' : ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition (81, s) → r.nextState = 81 → r.moveDir = Dir.R := by
              native_decide
            exact hb' step.readSym step.result (by simpa [hq81] using htrans') (by simpa [symStepConfig] using hst)
          by_cases hL2 : cfg'.headPos = (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ)
          · exfalso
            -- cfg = 81@L-1（头 = L-1）：其延拓第一步读 #₁@L-1 → 81 R@L
            -- → 头 ≥ L-1 的 81 漂移链（读 boundary/blank 均 81 R 写回）恒 81，与 hext 矛盾
            have hL1c : (symStepConfig cfg' step.result).headPos =
                (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by
              simp [symStepConfig, hdR, Dir.toInt, hL2]
              omega
            have hq81c : (symStepConfig cfg' step.result).state = 81 := by
              simpa [symStepConfig] using hst
            have hge81c : (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 ≤
                (symStepConfig cfg' step.result).headPos := by
              rw [hL1c]
            have hpathc : SymReachablePath VerifierSym.transition (encodeInstanceSym inst)
                (π₀ ++ [step]) (symStepConfig cfg' step.result) := by
              exact SymReachablePath.cons π₀ step cfg' hprev hfrom hread htrans
            have hbdryc : ((symStepConfig cfg' step.result).tape
                (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ)).1 = SymKind.boundary := by
              have hw : cfg'.headPos ≠ (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by omega
              simp [symStepConfig, Ne.symm hw]
              exact hP6r
            have hblankc : ∀ j : ℤ, (((encodeInstanceSym inst).length : ℕ) : ℤ) ≤ j →
                (symStepConfig cfg' step.result).tape j = Sym.blank := by
              intro j hj
              have hw1 : j ≠ (symStepConfig cfg' step.result).headPos := by omega
              have hw2 : j ≠ cfg'.headPos := by omega
              simp [symStepConfig, hw1, hw2]
              exact hPblank j hj
            exact sym_drift_81_no_accept (encodeInstanceSym inst) hpathc hq81c hge81c
              hbdryc hblankc ⟨π₂, cfg₂, hpath₂, hacc₂⟩
          · simp [symStepConfig, hdR, Dir.toInt]
            omega
      · -- P9A：cfg.state ∈ {9,38,77,85} → cfg 头 ≤ L-2
        -- （界放宽裁决：9@L-2 真实可达（8@L-1 读 #₁ → 9 L）；≤ L-2 够 P0' 用）
        -- 各支：入边分类 → cfg' 分量（h9A）或 cfg' 头 < L（P0' hlt）→ 步后头 ≤ L-2
        intro hst
        rcases hst with hq9 | hq38 | hq77 | hq85
        · -- 9：入边 {8（读 boundary → 9 L）, 9（自环 L）}
          have hst9 : step.result.nextState = 9 := by simpa [symStepConfig] using hq9
          have hsrc9 : cfg'.state = 8 ∨ cfg'.state = 9 := by
            have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 9 →
                  (q : ℕ) = 8 ∨ (q : ℕ) = 9 := by native_decide
            exact hb ⟨cfg'.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev⟩
              step.readSym step.result (by simpa [hq9] using htrans') hst9
          rcases hsrc9 with hq8 | hq9'
          · -- 8 读 → 9 L：cfg' 头 < L（P0' hlt）→ 9 头 = cfg' 头 - 1 ≤ L-2
            have hd8L : step.result.moveDir = Dir.L := by
              have hb : ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition (8, s) → r.nextState = 9 → r.moveDir = Dir.L := by native_decide
              exact hb step.readSym step.result (by simpa [hq8] using htrans')
                hst9
            have hlt8 : cfg'.headPos < ((encodeInstanceSym inst).length : ℤ) := by
              rcases hP0 with h100' | h101' | hlt
              · have : (8 : ℕ) ≠ 100 := by norm_num
                exact False.elim (this (hq8.symm.trans h100'))
              · have : (8 : ℕ) ≠ 101 := by norm_num
                exact False.elim (this (hq8.symm.trans h101'))
              · exact hlt
            simp [symStepConfig, hd8L, Dir.toInt]
            omega
          · -- 9 自环 L：h9A（≤ L-2）→ 9 头 ≤ L-3
            have hle9' : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h9A (Or.inl hq9')
            have hd9L : step.result.moveDir = Dir.L := by
              have hb : ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition (9, s) → r.nextState = 9 → r.moveDir = Dir.L := by native_decide
              exact hb step.readSym step.result (by simpa [hq9'] using htrans')
                hst9
            simp [symStepConfig, hd9L, Dir.toInt]
            omega
        · -- 38：入边 {27（读 data1-false → 38 L）, 38（自环 L）}
          have hst38 : step.result.nextState = 38 := by simpa [symStepConfig] using hq38
          have hsrc38 : cfg'.state = 27 ∨ cfg'.state = 38 := by
            have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 38 →
                  (q : ℕ) = 27 ∨ (q : ℕ) = 38 := by native_decide
            exact hb ⟨cfg'.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev⟩
              step.readSym step.result (by simpa [hq38] using htrans') hst38
          rcases hsrc38 with hq27 | hq38'
          · -- 27 读 data1-false → 38 L：cfg' 头 < L（P0' hlt）→ 38 头 = cfg' 头 - 1 ≤ L-2
            have hd27L : step.result.moveDir = Dir.L := by
              have hb : ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition (27, s) → r.nextState = 38 → r.moveDir = Dir.L := by native_decide
              exact hb step.readSym step.result (by simpa [hq27] using htrans')
                hst38
            have hlt27 : cfg'.headPos < ((encodeInstanceSym inst).length : ℤ) := by
              rcases hP0 with h100' | h101' | hlt
              · have : (27 : ℕ) ≠ 100 := by norm_num
                exact False.elim (this (hq27.symm.trans h100'))
              · have : (27 : ℕ) ≠ 101 := by norm_num
                exact False.elim (this (hq27.symm.trans h101'))
              · exact hlt
            simp [symStepConfig, hd27L, Dir.toInt]
            omega
          · -- 38 自环 L：h9A（≤ L-2）→ 38 头 ≤ L-3
            have hle38' : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h9A (Or.inr (Or.inl hq38'))
            have hd38L : step.result.moveDir = Dir.L := by
              have hb : ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition (38, s) → r.nextState = 38 → r.moveDir = Dir.L := by native_decide
              exact hb step.readSym step.result (by simpa [hq38'] using htrans')
                hst38
            simp [symStepConfig, hd38L, Dir.toInt]
            omega
        · -- 77：入边 {76（读 boundary → 77 L）, 77（自环 L）}
          have hst77 : step.result.nextState = 77 := by simpa [symStepConfig] using hq77
          have hsrc77 : cfg'.state = 76 ∨ cfg'.state = 77 := by
            have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 77 →
                  (q : ℕ) = 76 ∨ (q : ℕ) = 77 := by native_decide
            exact hb ⟨cfg'.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev⟩
              step.readSym step.result (by simpa [hq77] using htrans') hst77
          rcases hsrc77 with hq76 | hq77'
          · -- 76 读 → 77 L：cfg' 头 < L（P0' hlt）→ 77 头 = cfg' 头 - 1 ≤ L-2
            have hd76L : step.result.moveDir = Dir.L := by
              have hb : ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition (76, s) → r.nextState = 77 → r.moveDir = Dir.L := by native_decide
              exact hb step.readSym step.result (by simpa [hq76] using htrans')
                hst77
            have hlt76 : cfg'.headPos < ((encodeInstanceSym inst).length : ℤ) := by
              rcases hP0 with h100' | h101' | hlt
              · have : (76 : ℕ) ≠ 100 := by norm_num
                exact False.elim (this (hq76.symm.trans h100'))
              · have : (76 : ℕ) ≠ 101 := by norm_num
                exact False.elim (this (hq76.symm.trans h101'))
              · exact hlt
            simp [symStepConfig, hd76L, Dir.toInt]
            omega
          · -- 77 自环 L：h9A（≤ L-2）→ 77 头 ≤ L-3
            have hle77' : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h9A (Or.inr (Or.inr (Or.inl hq77')))
            have hd77L : step.result.moveDir = Dir.L := by
              have hb : ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition (77, s) → r.nextState = 77 → r.moveDir = Dir.L := by native_decide
              exact hb step.readSym step.result (by simpa [hq77'] using htrans')
                hst77
            simp [symStepConfig, hd77L, Dir.toInt]
            omega
        · -- 85：入边 {84（读 boundary → 85 L）, 85（自环 L）}
          have hst85 : step.result.nextState = 85 := by simpa [symStepConfig] using hq85
          have hsrc85 : cfg'.state = 84 ∨ cfg'.state = 85 := by
            have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 85 →
                  (q : ℕ) = 84 ∨ (q : ℕ) = 85 := by native_decide
            exact hb ⟨cfg'.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev⟩
              step.readSym step.result (by simpa [hq85] using htrans') hst85
          rcases hsrc85 with hq84 | hq85'
          · -- 84 读 → 85 L：cfg' 头 < L（P0' hlt）→ 85 头 = cfg' 头 - 1 ≤ L-2
            have hd84L : step.result.moveDir = Dir.L := by
              have hb : ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition (84, s) → r.nextState = 85 → r.moveDir = Dir.L := by native_decide
              exact hb step.readSym step.result (by simpa [hq84] using htrans')
                hst85
            have hlt84 : cfg'.headPos < ((encodeInstanceSym inst).length : ℤ) := by
              rcases hP0 with h100' | h101' | hlt
              · have : (84 : ℕ) ≠ 100 := by norm_num
                exact False.elim (this (hq84.symm.trans h100'))
              · have : (84 : ℕ) ≠ 101 := by norm_num
                exact False.elim (this (hq84.symm.trans h101'))
              · exact hlt
            simp [symStepConfig, hd84L, Dir.toInt]
            omega
          · -- 85 自环 L：h9A（≤ L-2）→ 85 头 ≤ L-3
            have hle85' : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h9A (Or.inr (Or.inr (Or.inr hq85')))
            have hd85L : step.result.moveDir = Dir.L := by
              have hb : ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition (85, s) → r.nextState = 85 → r.moveDir = Dir.L := by native_decide
              exact hb step.readSym step.result (by simpa [hq85'] using htrans')
                hst85
            simp [symStepConfig, hd85L, Dir.toInt]
            omega
      · -- P12c: state ∈ {12,11,14} → 头 ≤ L-2
        -- （界放宽裁决（P9A 先例）：9 读 #₀/#₀' → 12@[n+2, L-2] 由 P9 析取直接过；
        --   @L-2 的 12/11/14 读 data → R@L-1 读 #₁ → 101 R@L（101 带外 S 吸收）不可延拓，
        --   用 sym_qL1_101_no_accept 排除——"右行态归约到左行态/终止"判据的实例）
        intro hst
        rcases hst with hq12 | hq11 | hq14
        · -- 12：入边 {9（读 boundary → 12 R）, 12（自环 R 读 data-true）}
          have hst12 : step.result.nextState = 12 := by simpa [symStepConfig] using hq12
          have hsrc12 : cfg'.state = 9 ∨ cfg'.state = 12 := by
            have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 12 →
                  (q : ℕ) = 9 ∨ (q : ℕ) = 12 := by native_decide
            exact hb ⟨cfg'.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev⟩
              step.readSym step.result (by simpa [hq12] using htrans') hst12
          rcases hsrc12 with hq9 | hq12'
          · -- 9 读 boundary → 12 R：h9A（≤ L-2）；9@L-2 → 12@L-1 读 #₁ → 101 排除
            have hle9 : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h9A (Or.inl hq9)
            have hdR : step.result.moveDir = Dir.R := by
              have hb : ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition (9, s) → r.nextState = 12 → r.moveDir = Dir.R := by
                native_decide
              exact hb step.readSym step.result (by simpa [hq9] using htrans') hst12
            by_cases hL2 : cfg'.headPos = (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ)
            · exfalso
              -- 9@L-2 → 12@L-1：12 读 #₁ → 101 R@L；101 带外 S 吸收——与 hext 矛盾
              have hL1c : (symStepConfig cfg' step.result).headPos =
                  (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by
                simp [symStepConfig, hdR, Dir.toInt, hL2]
                omega
              have hq12c : (symStepConfig cfg' step.result).state = 12 := by
                simpa [symStepConfig] using hq12
              have hpathc : SymReachablePath VerifierSym.transition (encodeInstanceSym inst)
                  (π₀ ++ [step]) (symStepConfig cfg' step.result) := by
                exact SymReachablePath.cons π₀ step cfg' hprev hfrom hread htrans
              have hbdryc : ((symStepConfig cfg' step.result).tape
                  (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ)).1 = SymKind.boundary := by
                have hw : cfg'.headPos ≠ (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by omega
                simp [symStepConfig, Ne.symm hw]
                exact hP6r
              have hblankc : ∀ j : ℤ, (((encodeInstanceSym inst).length : ℕ) : ℤ) ≤ j →
                  (symStepConfig cfg' step.result).tape j = Sym.blank := by
                intro j hj
                have hw1 : j ≠ (symStepConfig cfg' step.result).headPos := by omega
                have hw2 : j ≠ cfg'.headPos := by omega
                simp [symStepConfig, hw1, hw2]
                exact hPblank j hj
              have hb12b : ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition (12, s) → s.1 = SymKind.boundary → r.nextState = 101 := by
                native_decide
              exact sym_qL1_101_no_accept (encodeInstanceSym inst) 12 hpathc hq12c hL1c
                hbdryc hb12b (by norm_num) ⟨π₂, cfg₂, hpath₂, hacc₂⟩
            · simp [symStepConfig, hdR, Dir.toInt]
              omega
          · -- 12 自环 R（读 data-true）：h12c（≤ L-2）；12@L-2 → 12@L-1 读 #₁ → 101 排除
            have hle12 : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h12c (Or.inl hq12')
            have hdR : step.result.moveDir = Dir.R := by
              have hb : ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition (12, s) → r.nextState = 12 → r.moveDir = Dir.R := by
                native_decide
              exact hb step.readSym step.result (by simpa [hq12'] using htrans') hst12
            by_cases hL2 : cfg'.headPos = (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ)
            · exfalso
              -- 12@L-2 读 data-true → 12 R@L-1：12@L-1 读 #₁ → 101 R@L（带外 S 吸收）——与 hext 矛盾
              have hL1c : (symStepConfig cfg' step.result).headPos =
                  (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by
                simp [symStepConfig, hdR, Dir.toInt, hL2]
                omega
              have hq12c : (symStepConfig cfg' step.result).state = 12 := by
                simpa [symStepConfig] using hq12
              have hpathc : SymReachablePath VerifierSym.transition (encodeInstanceSym inst)
                  (π₀ ++ [step]) (symStepConfig cfg' step.result) := by
                exact SymReachablePath.cons π₀ step cfg' hprev hfrom hread htrans
              have hbdryc : ((symStepConfig cfg' step.result).tape
                  (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ)).1 = SymKind.boundary := by
                have hw : cfg'.headPos ≠ (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by omega
                simp [symStepConfig, Ne.symm hw]
                exact hP6r
              have hblankc : ∀ j : ℤ, (((encodeInstanceSym inst).length : ℕ) : ℤ) ≤ j →
                  (symStepConfig cfg' step.result).tape j = Sym.blank := by
                intro j hj
                have hw1 : j ≠ (symStepConfig cfg' step.result).headPos := by omega
                have hw2 : j ≠ cfg'.headPos := by omega
                simp [symStepConfig, hw1, hw2]
                exact hPblank j hj
              have hb12b : ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition (12, s) → s.1 = SymKind.boundary → r.nextState = 101 := by
                native_decide
              exact sym_qL1_101_no_accept (encodeInstanceSym inst) 12 hpathc hq12c hL1c
                hbdryc hb12b (by norm_num) ⟨π₂, cfg₂, hpath₂, hacc₂⟩
            · simp [symStepConfig, hdR, Dir.toInt]
              omega
        · -- 11：入边 {10（读 data-false → 11 S）}
          have hst11 : step.result.nextState = 11 := by simpa [symStepConfig] using hq11
          have hsrc11 : cfg'.state = 10 ∨ cfg'.state = 11 := by
            have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 11 →
                  (q : ℕ) = 10 ∨ (q : ℕ) = 11 := by native_decide
            exact hb ⟨cfg'.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev⟩
              step.readSym step.result (by simpa [hq11] using htrans') hst11
          rcases hsrc11 with hq10 | hq11'
          · -- 10 读 data-false → 11 S：头不变 ≤ L-2（h10，S 步）
            have hle10 : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h10 hq10
            have hdS : step.result.moveDir = Dir.S := by
              have hb : ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition (10, s) → r.nextState = 11 → r.moveDir = Dir.S := by
                native_decide
              exact hb step.readSym step.result (by simpa [hq10] using htrans') hst11
            simp [symStepConfig, hdS, Dir.toInt]
            omega
          · -- 11 自环：11 的转移无 nextState = 11（表级：data1 → 81、data0 → 14、boundary → 101）
            exfalso
            have hb : ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition (11, s) → r.nextState ≠ 11 := by
              native_decide
            exact hb step.readSym step.result (by simpa [hq11'] using htrans') hst11
        · -- 14：入边 {11（读 data0-false → 14 R）, 14（自环 R 读 data0——借位传播）}
          have hst14 : step.result.nextState = 14 := by simpa [symStepConfig] using hq14
          have hsrc14 : cfg'.state = 11 ∨ cfg'.state = 14 := by
            have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 14 →
                  (q : ℕ) = 11 ∨ (q : ℕ) = 14 := by native_decide
            exact hb ⟨cfg'.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev⟩
              step.readSym step.result (by simpa [hq14] using htrans') hst14
          rcases hsrc14 with hq11 | hq14'
          · -- 11 读 data0-false → 14 R：h12c（≤ L-2）；11@L-2 → 14@L-1 读 #₁ → 101 排除
            have hle11 : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h12c (Or.inr (Or.inl hq11))
            have hdR : step.result.moveDir = Dir.R := by
              have hb : ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition (11, s) → r.nextState = 14 → r.moveDir = Dir.R := by
                native_decide
              exact hb step.readSym step.result (by simpa [hq11] using htrans') hst14
            by_cases hL2 : cfg'.headPos = (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ)
            · exfalso
              -- 11@L-2 读 data0-false → 14 R@L-1：14@L-1 读 #₁ → 101 R@L（带外 S 吸收）——与 hext 矛盾
              have hL1c : (symStepConfig cfg' step.result).headPos =
                  (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by
                simp [symStepConfig, hdR, Dir.toInt, hL2]
                omega
              have hq14c : (symStepConfig cfg' step.result).state = 14 := by
                simpa [symStepConfig] using hq14
              have hpathc : SymReachablePath VerifierSym.transition (encodeInstanceSym inst)
                  (π₀ ++ [step]) (symStepConfig cfg' step.result) := by
                exact SymReachablePath.cons π₀ step cfg' hprev hfrom hread htrans
              have hbdryc : ((symStepConfig cfg' step.result).tape
                  (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ)).1 = SymKind.boundary := by
                have hw : cfg'.headPos ≠ (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by omega
                simp [symStepConfig, Ne.symm hw]
                exact hP6r
              have hblankc : ∀ j : ℤ, (((encodeInstanceSym inst).length : ℕ) : ℤ) ≤ j →
                  (symStepConfig cfg' step.result).tape j = Sym.blank := by
                intro j hj
                have hw1 : j ≠ (symStepConfig cfg' step.result).headPos := by omega
                have hw2 : j ≠ cfg'.headPos := by omega
                simp [symStepConfig, hw1, hw2]
                exact hPblank j hj
              have hb14b : ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition (14, s) → s.1 = SymKind.boundary → r.nextState = 101 := by
                native_decide
              exact sym_qL1_101_no_accept (encodeInstanceSym inst) 14 hpathc hq14c hL1c
                hbdryc hb14b (by norm_num) ⟨π₂, cfg₂, hpath₂, hacc₂⟩
            · simp [symStepConfig, hdR, Dir.toInt]
              omega
          · -- 14 自环 R（读 data0）：h12c（≤ L-2）；14@L-2 → 14@L-1 读 #₁ → 101 排除
            have hle14 : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h12c (Or.inr (Or.inr hq14'))
            have hdR : step.result.moveDir = Dir.R := by
              have hb : ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition (14, s) → r.nextState = 14 → r.moveDir = Dir.R := by
                native_decide
              exact hb step.readSym step.result (by simpa [hq14'] using htrans') hst14
            by_cases hL2 : cfg'.headPos = (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ)
            · exfalso
              -- 14@L-2 读 data0 → 14 R@L-1：14@L-1 读 #₁ → 101 R@L（带外 S 吸收）——与 hext 矛盾
              have hL1c : (symStepConfig cfg' step.result).headPos =
                  (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by
                simp [symStepConfig, hdR, Dir.toInt, hL2]
                omega
              have hq14c : (symStepConfig cfg' step.result).state = 14 := by
                simpa [symStepConfig] using hq14
              have hpathc : SymReachablePath VerifierSym.transition (encodeInstanceSym inst)
                  (π₀ ++ [step]) (symStepConfig cfg' step.result) := by
                exact SymReachablePath.cons π₀ step cfg' hprev hfrom hread htrans
              have hbdryc : ((symStepConfig cfg' step.result).tape
                  (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ)).1 = SymKind.boundary := by
                have hw : cfg'.headPos ≠ (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by omega
                simp [symStepConfig, Ne.symm hw]
                exact hP6r
              have hblankc : ∀ j : ℤ, (((encodeInstanceSym inst).length : ℕ) : ℤ) ≤ j →
                  (symStepConfig cfg' step.result).tape j = Sym.blank := by
                intro j hj
                have hw1 : j ≠ (symStepConfig cfg' step.result).headPos := by omega
                have hw2 : j ≠ cfg'.headPos := by omega
                simp [symStepConfig, hw1, hw2]
                exact hPblank j hj
              have hb14b : ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition (14, s) → s.1 = SymKind.boundary → r.nextState = 101 := by
                native_decide
              exact sym_qL1_101_no_accept (encodeInstanceSym inst) 14 hpathc hq14c hL1c
                hbdryc hb14b (by norm_num) ⟨π₂, cfg₂, hpath₂, hacc₂⟩
            · simp [symStepConfig, hdR, Dir.toInt]
              omega
      · -- P10: state = 10 → 头 ≤ L-2
        -- （界放宽：10 的 R 扫（读 data-true 穿、data-false → 11 定位）被 consumed 区拦截归约到
        --   左行态；77 读 #₀/#₀' → 10@[n+2, L-2]；@L-2 → 10 R@L-1 读 #₁ → 101 R@L
        --   （101 S 吸收）——sym_qL1_101_no_accept 排除）
        intro hst
        have hst10 : step.result.nextState = 10 := by simpa [symStepConfig] using hst
        have hsrc10 : cfg'.state = 77 ∨ cfg'.state = 10 := by
          have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
              r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 10 →
                (q : ℕ) = 77 ∨ (q : ℕ) = 10 := by native_decide
          exact hb ⟨cfg'.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev⟩
            step.readSym step.result htrans' hst10
        rcases hsrc10 with hq77 | hq10'
        · -- 77 读 boundary → 10 R：h9A（≤ L-2）；77@L-2 → 10@L-1 读 #₁ → 101 排除
          have hle77 : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h9A (Or.inr (Or.inr (Or.inl hq77)))
          have hdR : step.result.moveDir = Dir.R := by
            have hb : ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition (77, s) → r.nextState = 10 → r.moveDir = Dir.R := by
              native_decide
            exact hb step.readSym step.result (by simpa [hq77] using htrans') hst10
          by_cases hL2 : cfg'.headPos = (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ)
          · exfalso
            -- 77@L-2 读 boundary → 10 R@L-1：10@L-1 读 #₁ → 101 R@L；101 带外 S 吸收——与 hext 矛盾
            have hL1c : (symStepConfig cfg' step.result).headPos =
                (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by
              simp [symStepConfig, hdR, Dir.toInt, hL2]
              omega
            have hq10c : (symStepConfig cfg' step.result).state = 10 := by
              simpa [symStepConfig] using hst
            have hpathc : SymReachablePath VerifierSym.transition (encodeInstanceSym inst)
                (π₀ ++ [step]) (symStepConfig cfg' step.result) := by
              exact SymReachablePath.cons π₀ step cfg' hprev hfrom hread htrans
            have hbdryc : ((symStepConfig cfg' step.result).tape
                (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ)).1 = SymKind.boundary := by
              have hw : cfg'.headPos ≠ (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by omega
              simp [symStepConfig, Ne.symm hw]
              exact hP6r
            have hb10b : ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition (10, s) → s.1 = SymKind.boundary → r.nextState = 101 := by
              native_decide
            exact sym_qL1_101_no_accept (encodeInstanceSym inst) 10 hpathc hq10c hL1c
              hbdryc hb10b (by norm_num) ⟨π₂, cfg₂, hpath₂, hacc₂⟩
          · simp [symStepConfig, hdR, Dir.toInt]
            omega
        · -- 10 自环 R（读 data-true）：h10（≤ L-2）；10@L-2 → 10@L-1 读 #₁ → 101 排除
          have hle10 : cfg'.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := h10 hq10'
          have hdR : step.result.moveDir = Dir.R := by
            have hb : ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition (10, s) → r.nextState = 10 → r.moveDir = Dir.R := by
              native_decide
            exact hb step.readSym step.result (by simpa [hq10'] using htrans') hst10
          by_cases hL2 : cfg'.headPos = (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ)
          · exfalso
            -- 10@L-2 读 data-true → 10 R@L-1：10@L-1 读 #₁ → 101 R@L（带外 S 吸收）——与 hext 矛盾
            have hL1c : (symStepConfig cfg' step.result).headPos =
                (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by
              simp [symStepConfig, hdR, Dir.toInt, hL2]
              omega
            have hq10c : (symStepConfig cfg' step.result).state = 10 := by
              simpa [symStepConfig] using hst
            have hpathc : SymReachablePath VerifierSym.transition (encodeInstanceSym inst)
                (π₀ ++ [step]) (symStepConfig cfg' step.result) := by
              exact SymReachablePath.cons π₀ step cfg' hprev hfrom hread htrans
            have hbdryc : ((symStepConfig cfg' step.result).tape
                (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ)).1 = SymKind.boundary := by
              have hw : cfg'.headPos ≠ (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by omega
              simp [symStepConfig, Ne.symm hw]
              exact hP6r
            have hb10b : ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition (10, s) → s.1 = SymKind.boundary → r.nextState = 101 := by
              native_decide
            exact sym_qL1_101_no_accept (encodeInstanceSym inst) 10 hpathc hq10c hL1c
              hbdryc hb10b (by norm_num) ⟨π₂, cfg₂, hpath₂, hacc₂⟩
          · simp [symStepConfig, hdR, Dir.toInt]
            omega
      · -- P10'0 cons:r7_E（格式段）→ #₀ 位(n+1).1 = boundary
        intro hEc
        have hEc' : r7_E cfg'.state := by
          have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
              r ∈ VerifierSym.transition ((q : ℕ), s) → r7_E r.nextState → r7_E (q : ℕ) := by
            native_decide
          exact hb ⟨cfg'.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev⟩
            step.readSym step.result htrans' hEc
        rw [symStepConfig]
        by_cases hw : ((encodeBitsSym inst.target).length : ℤ) + 1 = cfg'.headPos
        · -- 写位 n+1：读格 = 旧 #₀（ih）——E 态读 boundary 写 .1 = boundary
          have hbd : (cfg'.tape cfg'.headPos).1 = SymKind.boundary := by
            simpa [hw, hread] using (hP10'0 hEc')
          have hwb : (step.result.writeSym).1 = SymKind.boundary := by
            have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) → r7_E (q : ℕ) → s.1 = SymKind.boundary →
                  r.writeSym.1 = SymKind.boundary := by
              native_decide
            exact hb ⟨cfg'.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev⟩
              step.readSym step.result htrans' hEc' (by simpa [hread] using hbd)
          simp [hw]
          exact hwb
        · -- 未写位：继承 ih
          simpa [symStepConfig, hw] using (hP10'0 hEc')
      · -- P10'1a cons:1 态 → 头 ≤ n+1
        intro h1c
        have hsrc : cfg'.state = 0 ∨ cfg'.state = 1 := by
          have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
              r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 1 → (q : ℕ) = 0 ∨ (q : ℕ) = 1 := by
            native_decide
          exact hb ⟨cfg'.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev⟩
            step.readSym step.result htrans' (by simpa [symStepConfig] using h1c)
        rcases hsrc with hq0 | hq1
        · -- 源 0:0 无入边(头 = 0)→ 步后头 1 ≤ n+1
          have hhp0 : cfg'.headPos = 0 := by
            cases hprev with
            | nil => simp [symInitialConfig]
            | cons π₁ step₁ cfg₁ hprev₁ hfrom₁ hread₁ htrans₁ =>
                exfalso
                have hb0 : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                    r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 0 → False := by native_decide
                exact hb0 ⟨cfg₁.state, q12_path_state_lt102 (encodeInstanceSym inst) π₁ cfg₁ hprev₁⟩
                  step₁.readSym step₁.result (by simpa [hread₁] using htrans₁)
                  (by simpa [symStepConfig] using hq0)
          have hdR : step.result.moveDir = Dir.R := by
            have hb : ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition (0, s) → r.nextState = 1 → r.moveDir = Dir.R := by native_decide
            exact hb step.readSym step.result (by simpa [hq0] using htrans') (by simpa [symStepConfig] using h1c)
          simp [symStepConfig, hdR, Dir.toInt, hhp0]
        · -- 源 1:自环 R——ih(头 ≤ n+1);源头 = n+1 时读 #₀(boundary)→ next = 2 ≠ 1
          have hle0 := hP10'1 hq1
          by_cases hpn : cfg'.headPos = (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ)
          · exfalso
            have hbd : (cfg'.tape cfg'.headPos).1 = SymKind.boundary := by
              have hE1 : r7_E cfg'.state := by
                simpa [r7_E] using (Or.inr (Or.inl hq1))
              rw [hpn]
              exact hP10'0 hE1
            have hnext2 : step.result.nextState = 2 := by
              have hb : ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition (1, s) → s.1 = SymKind.boundary → r.nextState = 2 := by native_decide
              exact hb step.readSym step.result (by simpa [hq1] using htrans') (by simpa [hread] using hbd)
            have h1' : step.result.nextState = 1 := by
              simpa [symStepConfig] using h1c
            exact (by native_decide : (2 : ℕ) ≠ 1) (hnext2.symm.trans h1')
          · -- 源头 ≠ n+1(≤ n)→ 步后头 ≤ n+1
            have hdR : step.result.moveDir = Dir.R := by
              have hb : ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition (1, s) → r.nextState = 1 → r.moveDir = Dir.R := by native_decide
              exact hb step.readSym step.result (by simpa [hq1] using htrans') (by simpa [symStepConfig] using h1c)
            simp [symStepConfig, hdR, Dir.toInt]
            omega
      · -- P10'-1b cons:1 态 → 头 ≥ 1
        intro h1c
        have hsrc : cfg'.state = 0 ∨ cfg'.state = 1 := by
          have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
              r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 1 → (q : ℕ) = 0 ∨ (q : ℕ) = 1 := by
            native_decide
          exact hb ⟨cfg'.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev⟩
            step.readSym step.result htrans' (by simpa [symStepConfig] using h1c)
        rcases hsrc with hq0 | hq1
        · -- 源 0:0 无入边(头 = 0)→ 步后 1(0 读 #ₗ → 1 R)
          have hhp0 : cfg'.headPos = 0 := by
            cases hprev with
            | nil => simp [symInitialConfig]
            | cons π₁ step₁ cfg₁ hprev₁ hfrom₁ hread₁ htrans₁ =>
                exfalso
                have hb0 : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                    r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 0 → False := by
                  native_decide
                exact hb0 ⟨cfg₁.state, q12_path_state_lt102 (encodeInstanceSym inst) π₁ cfg₁ hprev₁⟩
                  step₁.readSym step₁.result (by simpa [hread₁] using htrans₁)
                  (by simpa [symStepConfig] using hq0)
          have hdR : step.result.moveDir = Dir.R := by
            have hb : ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition (0, s) → r.nextState = 1 → r.moveDir = Dir.R := by native_decide
            exact hb step.readSym step.result (by simpa [hq0] using htrans') (by simpa [symStepConfig] using h1c)
          simp [symStepConfig, hdR, Dir.toInt, hhp0]
        · -- 源 1:自环 R——ih(1 → 头 ≥ 1)
          have hdR : step.result.moveDir = Dir.R := by
            have hb : ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition (1, s) → r.nextState = 1 → r.moveDir = Dir.R := by native_decide
            exact hb step.readSym step.result (by simpa [hq1] using htrans') (by simpa [symStepConfig] using h1c)
          have hge1 := hP10'1b hq1
          simp [symStepConfig, hdR, Dir.toInt]
          omega
      · -- P10'-1c cons:1 态 → 首格 α
        intro h1c
        have hsrc : cfg'.state = 0 ∨ cfg'.state = 1 := by
          have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
              r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 1 → (q : ℕ) = 0 ∨ (q : ℕ) = 1 := by
            native_decide
          exact hb ⟨cfg'.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev⟩
            step.readSym step.result htrans' (by simpa [symStepConfig] using h1c)
        by_cases hw : ((encodeBitsSym inst.target).length : ℤ) + 2 = cfg'.headPos
        · -- 写位 = 首格:源 0 不可能(0 头 = 0);源 1 读首格 = α(ih)→ 1 读 α → next ≠ 1 矛盾
          rcases hsrc with hq0 | hq1
          · exfalso
            cases hprev with
            | nil =>
                have hh0 : (symInitialConfig (encodeInstanceSym inst)).headPos = 0 := rfl
                omega
            | cons π₁ step₁ cfg₁ hprev₁ hfrom₁ hread₁ htrans₁ =>
                exfalso
                have hb0 : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                    r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 0 → False := by
                  native_decide
                exact hb0 ⟨cfg₁.state, q12_path_state_lt102 (encodeInstanceSym inst) π₁ cfg₁ hprev₁⟩
                  step₁.readSym step₁.result (by simpa [hread₁] using htrans₁)
                  (by simpa [symStepConfig] using hq0)
          · exfalso
            have hα := hP10'1c hq1
            have hb : ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition (1, s) → s.1 = SymKind.alpha → r.nextState ≠ 1 := by
              native_decide
            have hbad := hb step.readSym step.result (by simpa [hq1] using htrans')
              (by simpa [hw, hread] using hα)
            exact hbad (by simpa [symStepConfig] using h1c)
        · -- 未写位
          rcases hsrc with hq0 | hq1
          · -- 源 0:cfg' = 初始——首格 = α
            cases hprev with
            | nil =>
                have hα0 : (symInitialConfig (encodeInstanceSym inst)).tape
                    (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) = Sym.alpha := by
                  dsimp [symInitialConfig]
                  have hpos' : (0 : ℤ) ≤ ((encodeBitsSym inst.target).length + 2 : ℕ) ∧
                      (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ).toNat < (encodeInstanceSym inst).length := by
                    constructor
                    · omega
                    · rw [r7_enc_len]
                      have hE : 1 ≤ (encodeElementsSym inst.elements).length := hm
                      omega
                  split
                  · rename_i hc
                    have hge : (encodeInstanceSym inst).getD
                        (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ).toNat Sym.blank =
                        (encodeInstanceSym inst)[(((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ).toNat] :=
                      List.getD_eq_getElem (encodeInstanceSym inst) Sym.blank hc.2
                    have hmid : (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ).toNat =
                        (encodeBitsSym inst.target).length + 2 := by omega
                    calc
                      (encodeInstanceSym inst)[(((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ).toNat]
                          = (encodeInstanceSym inst).getD (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ).toNat Sym.blank := hge.symm
                      _ = (encodeInstanceSym inst).getD ((encodeBitsSym inst.target).length + 2) Sym.blank := by
                            rw [hmid]
                      _ = Sym.alpha := r7_enc_getD_elem_first inst hm
                  · rename_i hnc
                    exfalso
                    exact hnc hpos'
                have hα0k : ((symInitialConfig (encodeInstanceSym inst)).tape
                    (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ)).1 = SymKind.alpha := by
                  simpa [Sym.alpha] using (congrArg (fun x : Sym => x.1) hα0)
                have hne0 : ↑(((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≠
                    (symInitialConfig (encodeInstanceSym inst)).headPos := by
                  intro h
                  simp [symInitialConfig] at h
                  omega
                change (if ↑(((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) =
                    (symInitialConfig (encodeInstanceSym inst)).headPos then
                    (step.result.writeSym).1 else
                    ((symInitialConfig (encodeInstanceSym inst)).tape
                      (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ)).1) = SymKind.alpha
                rw [if_neg hne0]
                exact hα0k
            | cons π₁ step₁ cfg₁ hprev₁ hfrom₁ hread₁ htrans₁ =>
                exfalso
                have hb0 : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                    r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 0 → False := by
                  native_decide
                exact hb0 ⟨cfg₁.state, q12_path_state_lt102 (encodeInstanceSym inst) π₁ cfg₁ hprev₁⟩
                  step₁.readSym step₁.result (by simpa [hread₁] using htrans₁)
                  (by simpa [symStepConfig] using hq0)
          · simpa [symStepConfig, hw] using (hP10'1c hq1)
      · -- P10'-2 cons:2 态 → (首格 ∈ {α,sel,nosel} ∧ (头 ≥ n+3 → sel/nosel) ∧ n+2 ≤ 头)
        intro h2c
        have hsrc : cfg'.state = 1 ∨ cfg'.state = 2 := by
          have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
              r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 2 → (q : ℕ) = 1 ∨ (q : ℕ) = 2 := by
            native_decide
          exact hb ⟨cfg'.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev⟩
            step.readSym step.result htrans' (by simpa [symStepConfig] using h2c)
        refine ⟨?_, ?_, ?_⟩
        · -- 首格 ∈ {α,sel,nosel}
          rw [symStepConfig]
          by_cases hw : ((encodeBitsSym inst.target).length : ℤ) + 2 = cfg'.headPos
          · -- 写位 = 首格:源 1 读 boundary 与首格 α 矛盾;源 2 读 α 写 sel/nosel
            rcases hsrc with hq1 | hq2
            · exfalso
              have hα := hP10'1c hq1
              have hrdb : step.readSym.1 = SymKind.boundary := by
                have hb : ∀ s : Sym, ∀ r : SymTransResult,
                    r ∈ VerifierSym.transition (1, s) → r.nextState = 2 → s.1 = SymKind.boundary := by
                  native_decide
                exact hb step.readSym step.result (by simpa [hq1] using htrans') (by simpa [symStepConfig] using h2c)
              have hαr : step.readSym.1 = SymKind.alpha := by
                simpa [hw, hread] using hα
              exact (by native_decide : SymKind.alpha ≠ SymKind.boundary) (hαr.symm.trans hrdb)
            · have hα2 : (cfg'.tape cfg'.headPos).1 = SymKind.alpha := by
                rcases (hP10'2 hq2).1 with ha | hs | hn
                · simpa [hw] using ha
                · exfalso
                  have hb1 : ∀ s : Sym, ∀ r : SymTransResult,
                      r ∈ VerifierSym.transition (2, s) → s.1 = SymKind.sel → r.nextState = 2 → False := by
                    native_decide
                  exact hb1 step.readSym step.result (by simpa [hq2] using htrans')
                    (by simpa [hw, hread] using hs) (by simpa [symStepConfig] using h2c)
                · exfalso
                  have hb1 : ∀ s : Sym, ∀ r : SymTransResult,
                      r ∈ VerifierSym.transition (2, s) → s.1 = SymKind.nosel → r.nextState = 2 → False := by
                    native_decide
                  exact hb1 step.readSym step.result (by simpa [hq2] using htrans')
                    (by simpa [hw, hread] using hn) (by simpa [symStepConfig] using h2c)
              have hwsel : step.result.writeSym.1 = SymKind.sel ∨ step.result.writeSym.1 = SymKind.nosel := by
                have hb : ∀ s : Sym, ∀ r : SymTransResult,
                    r ∈ VerifierSym.transition (2, s) → s.1 = SymKind.alpha → r.nextState = 2 →
                      r.writeSym.1 = SymKind.sel ∨ r.writeSym.1 = SymKind.nosel := by native_decide
                exact hb step.readSym step.result (by simpa [hq2] using htrans') (by simpa [hread] using hα2) (by simpa [symStepConfig] using h2c)
              rcases hwsel with hw1 | hw2
              · simpa [symStepConfig, hw] using (Or.inr (Or.inl hw1))
              · simpa [symStepConfig, hw] using (Or.inr (Or.inr hw2))
          · -- 未写位
            rcases hsrc with hq1 | hq2
            · simpa [symStepConfig, hw] using (Or.inl (hP10'1c hq1))
            · rcases (hP10'2 hq2).1 with ha | hs | hn
              · simpa [symStepConfig, hw] using (Or.inl ha)
              · simpa [symStepConfig, hw] using (Or.inr (Or.inl hs))
              · simpa [symStepConfig, hw] using (Or.inr (Or.inr hn))
        · -- 头 ≥ n+3 → sel/nosel
          intro hge
          rw [symStepConfig] at hge
          by_cases hw : ((encodeBitsSym inst.target).length : ℤ) + 2 = cfg'.headPos
          · -- 写位 = 首格:源 2 写 sel/nosel
            rcases hsrc with hq1 | hq2
            · exfalso
              have hα := hP10'1c hq1
              have hrdb : step.readSym.1 = SymKind.boundary := by
                have hb : ∀ s : Sym, ∀ r : SymTransResult,
                    r ∈ VerifierSym.transition (1, s) → r.nextState = 2 → s.1 = SymKind.boundary := by
                  native_decide
                exact hb step.readSym step.result (by simpa [hq1] using htrans') (by simpa [symStepConfig] using h2c)
              have hαr : step.readSym.1 = SymKind.alpha := by
                simpa [hw, hread] using hα
              exact (by native_decide : SymKind.alpha ≠ SymKind.boundary) (hαr.symm.trans hrdb)
            · have hwsel : step.result.writeSym.1 = SymKind.sel ∨ step.result.writeSym.1 = SymKind.nosel := by
                have hb : ∀ s : Sym, ∀ r : SymTransResult,
                    r ∈ VerifierSym.transition (2, s) → s.1 = SymKind.alpha → r.nextState = 2 →
                      r.writeSym.1 = SymKind.sel ∨ r.writeSym.1 = SymKind.nosel := by native_decide
                have hα2 : (cfg'.tape cfg'.headPos).1 = SymKind.alpha := by
                  rcases (hP10'2 hq2).1 with ha | hs | hn
                  · simpa [hw] using ha
                  · exfalso
                    have hb1 : ∀ s : Sym, ∀ r : SymTransResult,
                        r ∈ VerifierSym.transition (2, s) → s.1 = SymKind.sel → r.nextState = 2 → False := by
                      native_decide
                    exact hb1 step.readSym step.result (by simpa [hq2] using htrans')
                      (by simpa [hw, hread] using hs) (by simpa [symStepConfig] using h2c)
                  · exfalso
                    have hb1 : ∀ s : Sym, ∀ r : SymTransResult,
                        r ∈ VerifierSym.transition (2, s) → s.1 = SymKind.nosel → r.nextState = 2 → False := by
                      native_decide
                    exact hb1 step.readSym step.result (by simpa [hq2] using htrans')
                      (by simpa [hw, hread] using hn) (by simpa [symStepConfig] using h2c)
                exact hb step.readSym step.result (by simpa [hq2] using htrans') (by simpa [hread] using hα2) (by simpa [symStepConfig] using h2c)
              rcases hwsel with hw1 | hw2
              · simpa [symStepConfig, hw] using (Or.inl hw1)
              · simpa [symStepConfig, hw] using (Or.inr hw2)
          · -- 未写位:源 2 自环(源 1 步后头 = n+2 与 hge 矛盾)——源头 ≥ n+3 → ih 后半
            rcases hsrc with hq1 | hq2
            · exfalso
              have hdR : step.result.moveDir = Dir.R := by
                have hb : ∀ s : Sym, ∀ r : SymTransResult,
                    r ∈ VerifierSym.transition (1, s) → r.nextState = 2 → r.moveDir = Dir.R := by native_decide
                exact hb step.readSym step.result (by simpa [hq1] using htrans') (by simpa [symStepConfig] using h2c)
              simp [symStepConfig, hdR, Dir.toInt] at hge
              omega
            · have hdR : step.result.moveDir = Dir.R := by
                have hb : ∀ s : Sym, ∀ r : SymTransResult,
                    r ∈ VerifierSym.transition (2, s) → r.nextState = 2 → r.moveDir = Dir.R := by native_decide
                exact hb step.readSym step.result (by simpa [hq2] using htrans') (by simpa [symStepConfig] using h2c)
              have hsrcge : (((encodeBitsSym inst.target).length : ℤ) + 3) ≤ cfg'.headPos := by
                have hne : cfg'.headPos ≠ ((encodeBitsSym inst.target).length : ℤ) + 2 := by
                  intro h
                  exact hw h.symm
                simp [symStepConfig, hdR, Dir.toInt] at hge
                omega
              simpa [symStepConfig, hw] using ((hP10'2 hq2).2.1 hsrcge)
        · -- 2 态 → n+2 ≤ 头
          have hsrc : cfg'.state = 1 ∨ cfg'.state = 2 := by
            have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 2 → (q : ℕ) = 1 ∨ (q : ℕ) = 2 := by
              native_decide
            exact hb ⟨cfg'.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev⟩
              step.readSym step.result htrans' (by simpa [symStepConfig] using h2c)
          rcases hsrc with hq1 | hq2
          · -- 源 1:1 读 #₀@n+1 → 2 R@n+2(读位经 hP9 分类 + h1 上界 + 1 头下界)
            have hrdb : step.readSym.1 = SymKind.boundary := by
              have hb : ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition (1, s) → r.nextState = 2 → s.1 = SymKind.boundary := by native_decide
              exact hb step.readSym step.result (by simpa [hq1] using htrans') (by simpa [symStepConfig] using h2c)
            have hdR : step.result.moveDir = Dir.R := by
              have hb : ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition (1, s) → r.nextState = 2 → r.moveDir = Dir.R := by native_decide
              exact hb step.readSym step.result (by simpa [hq1] using htrans') (by simpa [symStepConfig] using h2c)
            have hp9 := hP9 cfg'.headPos (by rw [← hread]; exact hrdb)
            rcases hp9 with hp0 | hpL | hpr
            · -- 1@0 与 1 头 ≥ 1 矛盾
              have hge1 := hP10'1b hq1
              omega
            · -- 1@L-1 与 h1(1 头 ≤ n+2)矛盾
              have hle1 := h1 hq1
              have hlen2 := r7_elems_len_ge2 inst.elements hm hpos
              rw [r7_enc_len] at hpL
              omega
            · -- 头 ∈ [n+1, L-3] → 步后头 = 头 + 1 ≥ n+2
              simp [symStepConfig, hdR, Dir.toInt]
              omega
          · -- 源 2:自环 R——ih(n+2 ≤ 头)
            have hdR : step.result.moveDir = Dir.R := by
              have hb : ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition (2, s) → r.nextState = 2 → r.moveDir = Dir.R := by native_decide
              exact hb step.readSym step.result (by simpa [hq2] using htrans') (by simpa [symStepConfig] using h2c)
            have hge2 := (hP10'2 hq2).2.2
            simp [symStepConfig, hdR, Dir.toInt]
            omega
      · -- P10'-3 cons:{3,24,29,26,27,38,28} → 首格 sel/nosel
        intro hFc
        have hsrc : (cfg'.state = 3 ∨ cfg'.state = 24 ∨ cfg'.state = 29 ∨ cfg'.state = 26 ∨
            cfg'.state = 27 ∨ cfg'.state = 38 ∨ cfg'.state = 28) ∨ cfg'.state = 2 := by
          have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
              r ∈ VerifierSym.transition ((q : ℕ), s) →
                (r.nextState = 3 ∨ r.nextState = 24 ∨ r.nextState = 29 ∨ r.nextState = 26 ∨
                  r.nextState = 27 ∨ r.nextState = 38 ∨ r.nextState = 28) →
                ((q : ℕ) = 3 ∨ (q : ℕ) = 24 ∨ (q : ℕ) = 29 ∨ (q : ℕ) = 26 ∨ (q : ℕ) = 27 ∨
                  (q : ℕ) = 38 ∨ (q : ℕ) = 28) ∨ (q : ℕ) = 2 := by native_decide
          exact hb ⟨cfg'.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev⟩
            step.readSym step.result htrans' (by simpa [symStepConfig] using hFc)
        rw [symStepConfig]
        by_cases hw : ((encodeBitsSym inst.target).length : ℤ) + 2 = cfg'.headPos
        · -- 写位 = 首格:源格式段读首格 = sel/nosel(ih)→ 读 sel/nosel → next = 101 矛盾;源 2 → 读 boundary 与首格矛盾
          rcases hsrc with hF | hq2
          · -- 源格式段:读格 = 首格 ∈ {sel,nosel}(ih)——写回同值 → 落支
            rcases hP10'F hF with hs | hn
            · have hwsel : step.result.writeSym.1 = SymKind.sel := by
                have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                    r ∈ VerifierSym.transition ((q : ℕ), s) →
                      ((q : ℕ) = 3 ∨ (q : ℕ) = 24 ∨ (q : ℕ) = 29 ∨ (q : ℕ) = 26 ∨ (q : ℕ) = 27 ∨
                        (q : ℕ) = 38 ∨ (q : ℕ) = 28) → s.1 = SymKind.sel → r.writeSym.1 = SymKind.sel := by
                  native_decide
                exact hb ⟨cfg'.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev⟩
                  step.readSym step.result htrans' hF (by simpa [hw, hread] using hs)
              simpa [symStepConfig, hw] using (Or.inl hwsel)
            · have hwn : step.result.writeSym.1 = SymKind.nosel := by
                have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                    r ∈ VerifierSym.transition ((q : ℕ), s) →
                      ((q : ℕ) = 3 ∨ (q : ℕ) = 24 ∨ (q : ℕ) = 29 ∨ (q : ℕ) = 26 ∨ (q : ℕ) = 27 ∨
                        (q : ℕ) = 38 ∨ (q : ℕ) = 28) → s.1 = SymKind.nosel → r.writeSym.1 = SymKind.nosel := by
                  native_decide
                exact hb ⟨cfg'.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev⟩
                  step.readSym step.result htrans' hF (by simpa [hw, hread] using hn)
              simpa [symStepConfig, hw] using (Or.inr hwn)
          · exfalso
            have hrdb : step.readSym.1 = SymKind.boundary := by
              have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 2 →
                    (r.nextState = 3 ∨ r.nextState = 24 ∨ r.nextState = 29 ∨ r.nextState = 26 ∨
                      r.nextState = 27 ∨ r.nextState = 38 ∨ r.nextState = 28) → s.1 = SymKind.boundary := by
                native_decide
              exact hb ⟨cfg'.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev⟩
                step.readSym step.result htrans' hq2 (by simpa [symStepConfig] using hFc)
            rcases (hP10'2 hq2).1 with ha | hs | hn
            · have hαr : step.readSym.1 = SymKind.alpha := by
                simpa [hw, hread] using ha
              exact (by native_decide : SymKind.alpha ≠ SymKind.boundary) (hαr.symm.trans hrdb)
            · have hsr : step.readSym.1 = SymKind.sel := by
                simpa [hw, hread] using hs
              exact (by native_decide : SymKind.sel ≠ SymKind.boundary) (hsr.symm.trans hrdb)
            · have hnr : step.readSym.1 = SymKind.nosel := by
                simpa [hw, hread] using hn
              exact (by native_decide : SymKind.nosel ≠ SymKind.boundary) (hnr.symm.trans hrdb)
        · -- 未写位
          rcases hsrc with hF | hq2
          · rcases hP10'F hF with hs | hn
            · simpa [symStepConfig, hw] using (Or.inl hs)
            · simpa [symStepConfig, hw] using (Or.inr hn)
          · -- 源 2 → next = 3:2 读 #₁——头 ≥ n+3 → 首格 sel/nosel(2 断言后半)
            have hge : (((encodeBitsSym inst.target).length : ℤ) + 3) ≤ cfg'.headPos := by
              have hrdb : step.readSym.1 = SymKind.boundary := by
                have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                    r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 2 →
                      (r.nextState = 3 ∨ r.nextState = 24 ∨ r.nextState = 29 ∨ r.nextState = 26 ∨
                        r.nextState = 27 ∨ r.nextState = 38 ∨ r.nextState = 28) → s.1 = SymKind.boundary := by
                  native_decide
                exact hb ⟨cfg'.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev⟩
                  step.readSym step.result htrans' hq2 (by simpa [symStepConfig] using hFc)
              have hp9 := hP9 cfg'.headPos (by simpa [hread] using hrdb)
              rcases hp9 with hp0 | hpL | hpr
              · -- 2@0 与 2 头 ≥ n+2 矛盾
                have hge2 := (hP10'2 hq2).2.2
                omega
              · have hlen2 := r7_elems_len_ge2 inst.elements hm hpos
                rw [r7_enc_len] at hpL
                omega
              · -- 头 ∈ [n+1, L-3] 且 ≥ n+2 → [n+2, L-3] 无 boundary(r7_E_no_segment_boundary)矛盾
                have hge2 := (hP10'2 hq2).2.2
                have hpathE : ∀ step' ∈ π₀, r7_E step'.fromState :=
                  hP0e (by simpa [r7_E] using (Or.inr (Or.inr (Or.inl hq2))))
                have hsegb := r7_E_no_segment_boundary inst hprev hpathE cfg'.headPos hge2 hpr.2
                exfalso
                exact hsegb (by simpa [hread] using hrdb)
            simpa [symStepConfig, hw] using ((hP10'2 hq2).2.1 hge)
      · -- P11 cons:#₀ 位(n+1)∈ {boundary(种), data0}
        rw [symStepConfig]
        by_cases hw : ((encodeBitsSym inst.target).length : ℤ) + 1 = cfg'.headPos
        · -- 写位 n+1:读格 ∈ {boundary, data0}(ih)→ 写.1 = boundary ∨ 写 = data0(表级)
          have hwb : step.result.writeSym.1 = SymKind.boundary ∨
              step.result.writeSym = Sym.mk SymKind.data0 false ∨
              step.result.writeSym.1 = SymKind.data1 ∨
              step.result.writeSym = Sym.mk SymKind.data0 true ∨
              step.result.writeSym.1 = SymKind.consumed := by
            have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) →
                  (s.1 = SymKind.boundary ∨ s = Sym.mk SymKind.data0 false ∨
                    s.1 = SymKind.data1 ∨ s = Sym.mk SymKind.data0 true ∨ s.1 = SymKind.consumed) →
                    r.writeSym.1 = SymKind.boundary ∨ r.writeSym = Sym.mk SymKind.data0 false ∨
                      r.writeSym.1 = SymKind.data1 ∨ r.writeSym = Sym.mk SymKind.data0 true ∨
                        r.writeSym.1 = SymKind.consumed := by
              native_decide
            exact hb ⟨cfg'.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev⟩
              step.readSym step.result htrans' (by simpa [hw, hread] using hP11)
          rcases hwb with hb1 | hb2 | hb3 | hb4 | hb5
          · simpa [symStepConfig, hw] using (Or.inl hb1)
          · simpa [symStepConfig, hw] using (Or.inr (Or.inl hb2))
          · simpa [symStepConfig, hw] using (Or.inr (Or.inr (Or.inl hb3)))
          · simpa [symStepConfig, hw] using (Or.inr (Or.inr (Or.inr (Or.inl hb4))))
          · simpa [symStepConfig, hw] using (Or.inr (Or.inr (Or.inr (Or.inr hb5))))
        · -- 未写位
          simpa [symStepConfig, hw] using hP11
      · -- P6l:写位 0 时写回 boundary(写者读 #ₗ 保 kind;q = 20 读 boundary 写 data0——20 头 ≥ 1 排除)
        by_cases hw : cfg'.headPos = 0
        · rw [symStepConfig]
          simp [hw]
          have hwrite : (step.result.writeSym).1 = SymKind.boundary := by
            have hrd : step.readSym.1 = SymKind.boundary := by
              rw [hread]
              simpa [hw] using hP6l
            have hbw := r7l3_boundary_write cfg'.state
              (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
              step.readSym step.result hrd htrans'
            rcases hbw with hbd | h20
            · exact hbd
            · exfalso
              have hge1 := r7l3_20_head inst hprev h20
              omega
          simpa [symStepConfig, hw] using hwrite
        · -- neg:继承 ih
          simpa [symStepConfig, Ne.symm hw] using hP6l
      · -- P6r:写位 L-1 时写回 boundary(写者读 #₁ 保 kind;q = 20 读 #₁ → 21 R@L——带外 blank
        --   漂移(21 读 blank 写回 blank)恒 21 ≠ 100,hext 矛盾)
        by_cases hw : cfg'.headPos = (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ)
        · rw [symStepConfig]
          simp [hw]
          have hwrite : (step.result.writeSym).1 = SymKind.boundary := by
            have hrd : step.readSym.1 = SymKind.boundary := by
              rw [hread]
              simpa [hw] using hP6r
            have hbw := r7l3_boundary_write cfg'.state
              (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
              step.readSym step.result hrd htrans'
            rcases hbw with hbd | h20
            · exact hbd
            · exfalso
              have hns : step.result.nextState = 21 := by
                have hb : ∀ s : Sym, ∀ r : SymTransResult,
                    r ∈ VerifierSym.transition (20, s) → s.1 = SymKind.boundary → r.nextState = 21 := by
                  native_decide
                exact hb step.readSym step.result (by simpa [h20] using htrans') hrd
              have hdR : step.result.moveDir = Dir.R := by
                have hb : ∀ s : Sym, ∀ r : SymTransResult,
                    r ∈ VerifierSym.transition (20, s) → s.1 = SymKind.boundary → r.moveDir = Dir.R := by
                  native_decide
                exact hb step.readSym step.result (by simpa [h20] using htrans') hrd
              have h21c : (symStepConfig cfg' step.result).state = 21 := by
                simpa [symStepConfig] using hns
              have hLc : ((encodeInstanceSym inst).length : ℤ) ≤
                  (symStepConfig cfg' step.result).headPos := by
                simp [symStepConfig, hdR, Dir.toInt]
                omega
              have hpathc : SymReachablePath VerifierSym.transition (encodeInstanceSym inst)
                  (π₀ ++ [step]) (symStepConfig cfg' step.result) := by
                exact SymReachablePath.cons π₀ step cfg' hprev hfrom hread htrans
              have hblankc : ∀ j : ℤ, ((encodeInstanceSym inst).length : ℤ) ≤ j →
                  (symStepConfig cfg' step.result).tape j = Sym.blank := by
                intro j hj
                have hw2 : j ≠ cfg'.headPos := by omega
                simp [symStepConfig, hw2]
                exact hPblank j hj
              have hdrift21 : ∀ r : SymTransResult, r ∈ VerifierSym.transition (21, Sym.blank) →
                  r.nextState = 21 ∧ r.moveDir = Dir.R ∧ r.writeSym = Sym.blank := by
                native_decide
              exact sym_drift_blank_no_accept 21 (encodeInstanceSym inst) hpathc h21c hLc
                (by norm_num) hblankc hdrift21 ⟨π₂, cfg₂, hpath₂, hacc₂⟩
          exact hwrite
        · -- neg:继承 ih
          simpa [symStepConfig, Ne.symm hw] using hP6r
      · -- P9
        intro p hp
        rw [symStepConfig] at hp
        by_cases hw : p = cfg'.headPos
        · -- 写位:写者读 boundary(保)或 51
          have hwrite : (step.result.writeSym).1 = SymKind.boundary := by
            simpa [hw] using hp
          have hcls := r7_write_boundary_class cfg'.state
            (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
            step.readSym step.result htrans' hwrite
          rcases hcls with hrd | h51
          · -- 读格 = boundary → 读位分类(ih P9)
            have hreadp : (cfg'.tape cfg'.headPos).1 = SymKind.boundary := by
              rw [← hread]
              exact hrd
            have hp9' := hP9 cfg'.headPos hreadp
            rw [hw]
            exact hp9'
          · -- 51:写位 = 51 头 ∈ [n+1, L-3](r7l3_51_domain——#₀' 域,束外引理)
            have hd51 := r7l3_51_domain inst hprev (by simpa [symStepConfig] using h51)
            rw [hw]
            right; right
            exact hd51
        · -- 未写位:ih P9
          have hp' : (cfg'.tape p).1 = SymKind.boundary := by
            simpa [symStepConfig, hw] using hp
          exact hP9 p hp'

-- ===================================================
-- q10 ① Sym 层 H1(roadmap §10.1b:r7_accept_no_101 + r7_accept_path_prefix_inside)

/-- q10 ① Sym 层 H1a:接受路径(终点 100)上每步后继 ≠ 101
    (101 吸收:101 出现则后续恒 101,终点必 101——适配 Reverse3 symAccepts_no_101)。 -/
lemma r7_accept_no_101 (inst : SubsetSumInstance) :
    ∀ π cfg, SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg →
      cfg.state = 100 → ∀ step ∈ π, step.result.nextState ≠ 101 := by
  intro π cfg h hq step hstep
  have hsteps : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π cfg :=
    (symSteps_initial_iff VerifierSym.transition (encodeInstanceSym inst) π cfg).mpr h
  exact symAccepts_no_101 hsteps hq step hstep

/-- q10 ① Sym 层 H1:非吸收态(≠ 100/101)带头 < |enc|——束 P0' 环直推(带可延拓前提)。 -/
lemma r7_nonabsorb_head_inside (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (hpos : ∀ v ∈ inst.elements, 0 < v)
    (htarget : 0 < inst.target) :
    ∀ π cfg, SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg →
      (∃ π₂ cfg₂, SymReachablePath VerifierSym.transition (encodeInstanceSym inst) (π ++ π₂) cfg₂ ∧
        cfg₂.state = 100) →
      cfg.state ≠ 100 → cfg.state ≠ 101 →
        cfg.headPos < ((encodeInstanceSym inst).length : ℤ) := by
  intro π cfg h hext hq100 hq101
  have hb := r7_path_bundle inst hm hpos htarget π cfg h
  have hP0 : cfg.state = 100 ∨ cfg.state = 101 ∨
      cfg.headPos < ((encodeInstanceSym inst).length : ℤ) := (hb hext).1
  rcases hP0 with h100 | h101 | hlt
  · exfalso
    exact hq100 h100
  · exfalso
    exact hq101 h101
  · exact hlt

/-- q10 ① Sym 层:接受路径每前缀 cfg₀:100 ∨ 头 < |enc|(P0' + 101 吸收排除)。
    §8.4 目标形态。 -/
lemma r7_accept_path_prefix_inside (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (hpos : ∀ v ∈ inst.elements, 0 < v)
    (htarget : 0 < inst.target) :
    ∀ π cfg, SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg →
      cfg.state = 100 →
      ∀ π₀ cfg₀, SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π₀ cfg₀ →
        List.IsPrefix π₀ π →
          cfg₀.state = 100 ∨ cfg₀.headPos < ((encodeInstanceSym inst).length : ℤ) := by
  intro π cfg h hq π₀ cfg₀ h₀ hpfix
  rcases hpfix with ⟨πrest, hπ⟩
  have hext₀ : ∃ π₂ cfg₂, SymReachablePath VerifierSym.transition (encodeInstanceSym inst) (π₀ ++ π₂) cfg₂ ∧
      cfg₂.state = 100 := by
    refine ⟨πrest, cfg, ?_, hq⟩
    simpa [hπ] using h
  have hb := r7_path_bundle inst hm hpos htarget π₀ cfg₀ h₀
  have hP0 : cfg₀.state = 100 ∨ cfg₀.state = 101 ∨
      cfg₀.headPos < ((encodeInstanceSym inst).length : ℤ) := (hb hext₀).1
  rcases hP0 with h100 | h101 | hlt
  · exact Or.inl h100
  · exfalso
    have hsteps : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π cfg :=
      (symSteps_initial_iff VerifierSym.transition (encodeInstanceSym inst) π cfg).mpr h
    have hsteps₀ : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π₀ cfg₀ :=
      (symSteps_initial_iff VerifierSym.transition (encodeInstanceSym inst) π₀ cfg₀).mpr h₀
    have hsteps' : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) (π₀ ++ πrest) cfg := by
      simpa [hπ] using hsteps
    rcases symSteps_append_decomp π₀ πrest hsteps' with ⟨cfg₁, hseg₁, hseg₂⟩
    have hcfg₁ : cfg₁ = cfg₀ := Mp.SymToF4.symSteps_end_unique hseg₁ hsteps₀
    have hseg₂' : SymSteps VerifierSym.transition cfg₀ πrest cfg := by
      simpa [hcfg₁] using hseg₂
    have h101end : cfg.state = 101 := symSteps_from_101_stays_101 h101 hseg₂'
    exact (by norm_num : (101 : ℕ) ≠ 100) (h101end.symm.trans hq)
  · exact Or.inr hlt

-- ===================================================
-- L3a(1b fork 装配)Sym 层桥:写 sel/nosel 步数 = 读分支步数(用户方向:数 sel/nosel)

/-- 路径每步的转移与源态 < 102(归纳提取)。 -/
lemma r7_path_step_trans (input : List Sym) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg) :
    (∀ step ∈ π, step.result ∈ VerifierSym.transition (step.fromState, step.readSym)) ∧
      (∀ step ∈ π, step.fromState < 102) := by
  induction h with
  | nil =>
      constructor <;> intro step hmem <;> simp at hmem
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      constructor
      · intro t ht
        rcases List.mem_append.mp ht with ht0 | ht1
        · exact ih.1 t ht0
        · have ht_eq : t = step := List.mem_singleton.mp ht1
          subst t
          have htrans' : step.result ∈ VerifierSym.transition (step.fromState, step.readSym) := by
            simpa [hfrom, hread] using htrans
          exact htrans'
      · intro t ht
        rcases List.mem_append.mp ht with ht0 | ht1
        · exact ih.2 t ht0
        · have ht_eq : t = step := List.mem_singleton.mp ht1
          subst t
          simpa [hfrom] using (q12_path_state_lt102 input π₀ cfg' hprev)

-- 表级:预选写谓词 = 读分支谓词(Bool 版;2 态读 α 是唯一产生 sel/nosel 的转移;
--   21 的写回(读 sel 写 sel,next 51)与 100/101 的写回被 next ∉ {100,101} 前提排除)。
lemma r7_selnosel_write_eq_branch (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s))
    (hno100 : r.nextState ≠ 100) (hno101 : r.nextState ≠ 101) :
    ((decide (r.writeSym.1 = SymKind.sel) || decide (r.writeSym.1 = SymKind.nosel)) &&
        decide (r.nextState = 2)) = Sym.isBranch s := by
  have hdec : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 100 → r.nextState ≠ 101 →
        ((decide (r.writeSym.1 = SymKind.sel) || decide (r.writeSym.1 = SymKind.nosel)) &&
          decide (r.nextState = 2)) = Sym.isBranch s := by
    native_decide
  exact hdec ⟨q, hq⟩ s r hr hno100 hno101

-- 接受路径(截断:每步 next ∉ {100,101})上:预选写步数 = 读分支步数
--   (2 预选每元素恰一步;21/100/101 的写回不计数)。
lemma r7_accept_write_selnosel_eq_fork (input : List Sym) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg) (hacc : cfg.state = 100)
    (hno100 : ∀ step ∈ π, step.result.nextState ≠ 100) :
    (π.filter (fun step =>
        (decide (step.result.writeSym.1 = SymKind.sel) ||
            decide (step.result.writeSym.1 = SymKind.nosel)) &&
          decide (step.result.nextState = 2))).length =
      (π.filter (fun step => Sym.isBranch step.readSym)).length := by
  have hsteps : SymSteps VerifierSym.transition (symInitialConfig input) π cfg :=
    (symSteps_initial_iff VerifierSym.transition input π cfg).mpr h
  have hno101 : ∀ step ∈ π, step.result.nextState ≠ 101 := symAccepts_no_101 hsteps hacc
  have htr := r7_path_step_trans input h
  have hpred : ∀ step ∈ π,
      ((decide (step.result.writeSym.1 = SymKind.sel) ||
          decide (step.result.writeSym.1 = SymKind.nosel)) &&
        decide (step.result.nextState = 2)) = Sym.isBranch step.readSym := by
    intro step hmem
    exact r7_selnosel_write_eq_branch step.fromState (htr.2 step hmem) step.readSym
      step.result (htr.1 step hmem) (hno100 step hmem) (hno101 step hmem)
  have hf : π.filter (fun step =>
      (decide (step.result.writeSym.1 = SymKind.sel) ||
          decide (step.result.writeSym.1 = SymKind.nosel)) &&
        decide (step.result.nextState = 2)) =
      π.filter (fun step => Sym.isBranch step.readSym) := by
    apply List.filter_congr
    intro step hmem
    exact hpred step hmem
  simpa [hf]

end Mp
