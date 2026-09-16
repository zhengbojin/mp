/- 编译正确性（阶段 1）：Sym 层验证器 → CBTM 层（subsetSumCBTM）的完备性提升，
   与 CBTM 层 → Sym 层的投影组装（可靠性方向见后续阶段；htrap 需要
   transition4 陷阱逃逸分析，见文件尾注释）。 -/
import Mp.Basic
import Mp.CBTM
import Mp.IVM
import Mp.SubsetSumVerifierCore
import Mp.SubsetSumVerifierCBTM
import Mp.SubsetSumVerifierCBTM3
import Mp.SubsetSumVerifierCBTM4
import Mp.SubsetSumVerifierCBTM6
import Mp.SubsetSumVerifierReverse2
import Mp.SubsetSumReal
import Mp.LowerBound


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
open CBTM
open SymToF4

-- ===========================================================================
-- §1. Sym 转移表全局引理（Finset.all + decide，规避无界 SymTransResult 枚举）
-- ===========================================================================

/-- 表外状态的转移 = 101 陷阱单例（防御性默认分支，避免展开大转移表）。 -/
lemma transition_of_not_legal (q : ℕ) (s : Sym) (hq : q ∉ VerifierSym.legalStates) :
    VerifierSym.transition (q, s) = {SymTransResult.mk 101 s Dir.S} := by
  unfold VerifierSym.transition
  simp [hq]

/-- 任意状态读任意符号的转移，nextState ≤ 101（表外状态归 101 陷阱）。 -/
lemma symTransition_nextState_le101 (q : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) : r.nextState ≤ 101 := by
  by_cases hqin : q ∈ VerifierSym.legalStates
  · have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≤ 101 := by
      native_decide
    have hqlt : q < 102 := by
      simp [VerifierSym.legalStates] at hqin
      omega
    exact hb ⟨q, hqlt⟩ s r hr
  · rw [transition_of_not_legal q s hqin] at hr
    simp at hr
    subst r
    norm_num

/-- 表内转移的 nextState 仍在表内。 -/
lemma symTransition_nextState_mem_legal (q : ℕ) (s : Sym) (r : SymTransResult)
    (hq : q ∈ VerifierSym.legalStates) (hr : r ∈ VerifierSym.transition (q, s)) :
    r.nextState ∈ VerifierSym.legalStates := by
  have hb : ∀ q : Fin 102, ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), Sym.mk k m) → r.nextState ∈ VerifierSym.legalStates := by
    native_decide
  have hqlt : q < 102 := by
    simp [VerifierSym.legalStates] at hq
    omega
  rcases s with ⟨k, m⟩
  exact hb ⟨q, hqlt⟩ k m r hr

/-- 可达路径的状态恒在 legalStates 内（初始态 0 合法）。 -/
lemma symReachable_state_mem_legal {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg) :
    cfg.state ∈ VerifierSym.legalStates ∧ ∀ step ∈ π, step.fromState ∈ VerifierSym.legalStates := by
  induction h with
  | nil =>
      constructor
      · dsimp [symInitialConfig]
        decide
      · intro st hst
        simp at hst
  | cons π₀ step cfg₀ hprev hfrom hread htrans ih =>
      rcases ih with ⟨hst₀, hall⟩
      constructor
      · dsimp [symStepConfig]
        exact symTransition_nextState_mem_legal cfg₀.state (cfg₀.tape cfg₀.headPos)
          step.result hst₀ htrans
      · intro st hstm
        rw [List.mem_append] at hstm
        rcases hstm with hpre | hlast
        · exact hall st hpre
        · rw [List.mem_singleton] at hlast
          rw [hlast]
          rw [hfrom]
          exact hst₀

/-- 分支符号（α/β）的读若不出 101 陷阱则必在状态 2（100 态除外：吸收写回原符号）。 -/
lemma symTransition_branch_q2 (q : ℕ) (s : Sym) (r : SymTransResult)
    (hbr : Sym.isBranch s) (hr : r ∈ VerifierSym.transition (q, s))
    (hrs : r.nextState ≠ 101) (hqne : q ≠ 100) : q = 2 := by
  by_cases hq2 : q = 2
  · exact hq2
  · exfalso
    by_cases hqlt : q < 102
    · have hb : ∀ q : Fin 102, (q : ℕ) ≠ 100 → ∀ s : Sym, Sym.isBranch s → ∀ r : SymTransResult,
          r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) ≠ 2 → r.nextState = 101 := by
        native_decide
      exact hrs (hb ⟨q, hqlt⟩ hqne s hbr r hr hq2)
    · have hout : q ∉ VerifierSym.legalStates := by
        intro hqin
        simp [VerifierSym.legalStates] at hqin
        omega
      rw [transition_of_not_legal q s hout] at hr
      simp at hr
      subst r
      exact hrs rfl

/-- 陷阱态 101 吸收（Sym 层）：读任意符号的转移 nextState 恒 101。 -/
lemma symTransition_trap101_absorb (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (101, s)) : r.nextState = 101 := by
  have hb : ∀ s : Sym, ∀ r ∈ VerifierSym.transition (101, s),
      r.nextState = 101 := by
    intro s
    rcases s with ⟨ks, ms⟩ <;> cases ks <;> cases ms <;> decide
  exact hb s r hr

/-- Sym 路径不变量：终态与每步 fromState 都 ≤ 101。 -/
lemma symSteps_state_le101 {cfg₀ : SymConfig} {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition cfg₀ π cfg) (h0 : cfg₀.state ≤ 101) :
    cfg.state ≤ 101 ∧ ∀ step ∈ π, step.fromState ≤ 101 := by
  induction h with
  | nil =>
      exact ⟨h0, by intro step hstep; simp at hstep⟩
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      rcases ih with ⟨hst₁, hall⟩
      constructor
      · dsimp [symStepConfig]
        rw [← hread] at htrans
        exact symTransition_nextState_le101 cfg₁.state step.readSym step.result htrans
      · intro st hstm
        rw [List.mem_append] at hstm
        rcases hstm with hpre | hlast
        · exact hall st hpre
        · rw [List.mem_singleton] at hlast
          subst hlast
          rw [hfrom]
          exact hst₁

/-- 100 态吸收：读任意符号 nextState 恒 100。 -/
lemma symTransition_100_absorb (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (100, s)) : r.nextState = 100 := by
  have hb : ∀ s : Sym, ∀ r ∈ VerifierSym.transition (100, s),
      r.nextState = 100 := by
    intro s
    rcases s with ⟨ks, ms⟩ <;> cases ks <;> cases ms <;> decide
  exact hb s r hr

/-- 路径二分：要么每步 nextState ≠ 100，要么终点状态 = 100。 -/
lemma symSteps_no_100_or_end {cfg₀ : SymConfig} {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition cfg₀ π cfg) :
    (∀ step ∈ π, step.result.nextState ≠ 100) ∨ cfg.state = 100 := by
  induction h with
  | nil =>
      left
      intro step hstep
      simp at hstep
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      cases ih with
      | inl h₁ =>
          by_cases h100 : step.result.nextState = 100
          · right
            simpa [symStepConfig, h100]
          · left
            intro st hstm
            rw [List.mem_append] at hstm
            rcases hstm with hpre | hlast
            · exact h₁ st hpre
            · rw [List.mem_singleton] at hlast
              subst st
              exact h100
      | inr h₁ =>
          right
          have htr' : step.result ∈ VerifierSym.transition (100, step.readSym) := by
            rw [h₁, ← hread] at htrans
            exact htrans
          simpa [symStepConfig] using (symTransition_100_absorb step.readSym step.result htr')

/-- 每步 nextState ≠ 100 ⟹ 每步 fromState ≠ 100（初始态 0 ≠ 100）。 -/
lemma symSteps_fromState_ne100_of_next_ne100 {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition (symInitialConfig input) π cfg) :
    (∀ step ∈ π, step.result.nextState ≠ 100) → ∀ step ∈ π, step.fromState ≠ 100 := by
  intro hno
  induction h with
  | nil =>
      intro st hst
      simp at hst
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro st hstm
      rw [List.mem_append] at hstm
      rcases hstm with hpre | hlast
      · exact ih (fun st' hst' => hno st' (by rw [List.mem_append]; left; exact hst')) st hpre
      · rw [List.mem_singleton] at hlast
        subst st
        intro hf
        rw [← hread, ← hfrom, hf] at htrans
        have hnext := symTransition_100_absorb step.readSym step.result htrans
        exact hno step (by simp) hnext

/-- 接受路径可截断为无 100 态步（fromState ≠ 100）的路径。 -/
lemma symSteps_accept_exists_no_100 {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition (symInitialConfig input) π cfg)
    (hacc : cfg.state = VerifierSym.qAccept) :
    ∃ π' : List SymStep, ∃ cfg' : SymConfig,
      SymSteps VerifierSym.transition (symInitialConfig input) π' cfg' ∧
      cfg'.state = VerifierSym.qAccept ∧
      ∀ step ∈ π', step.fromState ≠ 100 := by
  induction h with
  | nil =>
      exfalso
      dsimp [symInitialConfig, SymConfig.mk, VerifierSym.qAccept] at hacc
      norm_num at hacc
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      by_cases h1 : cfg₁.state = 100
      · rcases ih h1 with ⟨π', cfg', h', hacc', hn'⟩
        exact ⟨π', cfg', h', hacc', hn'⟩
      · have hnone₀ : ∀ step' ∈ π₀, step'.result.nextState ≠ 100 := by
          rcases symSteps_no_100_or_end hprev with hnone | hend
          · exact hnone
          · exfalso
            exact h1 hend
        have hfrom₀ : ∀ step' ∈ π₀, step'.fromState ≠ 100 :=
          symSteps_fromState_ne100_of_next_ne100 hprev hnone₀
        refine ⟨π₀ ++ [step], symStepConfig cfg₁ step.result,
          SymSteps.cons π₀ step cfg₁ hprev hfrom hread htrans, hacc, ?_⟩
        intro st hstm
        rw [List.mem_append] at hstm
        rcases hstm with hpre | hlast
        · exact hfrom₀ st hpre
        · rw [List.mem_singleton] at hlast
          subst st
          rw [hfrom]
          exact h1

/-- Sym 路径不变量：分支读只出现在状态 2（无 101 步的前提：101 步吸收到不了接受态）。 -/
lemma symSteps_branch_only_q2 {cfg₀ : SymConfig} {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition cfg₀ π cfg)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101)
    (hno100 : ∀ step ∈ π, step.fromState ≠ 100) :
    ∀ step ∈ π, Sym.isBranch step.readSym → step.fromState = 2 := by
  induction h with
  | nil =>
      intro step hstep
      simp at hstep
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro st hstm
      rw [List.mem_append] at hstm
      rcases hstm with hpre | hlast
      · exact ih (fun step' hst' => hno101 step' (by rw [List.mem_append]; left; exact hst'))
          (fun step' hst' => hno100 step' (by rw [List.mem_append]; left; exact hst')) st hpre
      · rw [List.mem_singleton] at hlast
        rw [hlast]
        intro hbr
        rw [← hread] at htrans
        have hfne : step.fromState ≠ 101 := by
          intro hf
          rw [← hfrom, hf] at htrans
          have hnext := symTransition_trap101_absorb step.readSym step.result htrans
          exact hno101 step (by simp) hnext
        have hfne100 : step.fromState ≠ 100 :=
          hno100 step (by simp)
        have hrs' : step.result.nextState ≠ 101 :=
          hno101 step (by simp)
        have hqne100' : cfg₁.state ≠ 100 := by
          intro hq100
          exact hfne100 (by rw [hfrom, hq100])
        have hq := symTransition_branch_q2 cfg₁.state step.readSym step.result hbr htrans hrs' hqne100'
        rw [hfrom]
        exact hq

-- ===========================================================================
-- §2. 完备性提升：Sym 接受 ⟹ CBTM 接受
-- ===========================================================================

/-- GoodBlockPath 的块级 TapeSteps 拼接为整体 TapeSteps。 -/
lemma goodBlockPath_to_tapeSteps (w : List F4) (cfgc : CBTMConfig subsetSumCBTM w)
    (π : ComputationPath) (cfgc' : CBTMConfig subsetSumCBTM w)
    (hbp : GoodBlockPath w cfgc π cfgc') :
    TapeSteps subsetSumCBTM w cfgc π cfgc' := by
  induction hbp with
  | nil cfgc => exact TapeSteps.nil
  | cons cfgc cfgm cfgc' πm π cfgs p q sym r hblock htail ih =>
      rcases hblock with ⟨hpath, hlen, _⟩
      exact TapeSteps_trans subsetSumCBTM w cfgc cfgm cfgc' πm π hpath ih

/-- acceptStates4 含 (qAccept, 0, 0) 编码。 -/
lemma acceptStates4_mem_qAccept : encodeState VerifierSym.qAccept 0 0 ∈ acceptStates4 := by
  dsimp [acceptStates4]
  apply Finset.mem_image.mpr
  refine ⟨0, ?_, rfl⟩
  rw [Finset.mem_range]
  dsimp [regBound]
  norm_num

/-- SymReachablePath → symAccepts（状态对应）。 -/
lemma symReachable_accepts {input : List Sym} {πs : List SymStep} {cfgs : SymConfig}
    (h : SymReachablePath VerifierSym.transition input πs cfgs) :
    cfgs.state = VerifierSym.qAccept →
    symAccepts VerifierSym.transition VerifierSym.acceptStates input := by
  intro hacc
  refine ⟨πs, cfgs, ?_, ?_⟩
  · exact h
  · rw [VerifierSym.acceptStates]
    rw [hacc]
    exact Finset.mem_singleton.mpr rfl

/-- 完备性：Sym 接受 ⟹ CBTM 接受（对 Sym 编码串 w）。 -/
theorem symAccepts_implies_tapeAccepts (w : List Sym) :
    symAccepts VerifierSym.transition VerifierSym.acceptStates w →
    subsetSumCBTM.tapeAccepts (flat4F4 w) := by
  intro hs
  rcases hs with ⟨πs, cfgs, hpath, hacc⟩
  rcases reachablePath_to_steps hpath with hsteps
  have h0 : (symInitialConfig w).state ≤ 101 := by
    dsimp [symInitialConfig]
    norm_num
  have hsteps_ok : ∀ step ∈ πs, step.fromState ≤ 101 := by
    intro step hst
    have hm := (symReachable_state_mem_legal hpath).2 step hst
    have hdec : ∀ q ∈ VerifierSym.legalStates, q ≤ 101 := by
      native_decide
    exact hdec step.fromState hm
  have haccEq : cfgs.state = VerifierSym.qAccept := by
    simpa [VerifierSym.acceptStates] using hacc
  rcases symSteps_accept_exists_no_100 hsteps haccEq with ⟨πs', cfgs', hsteps', hacc', hn100'⟩
  have hno101' : ∀ step ∈ πs', step.result.nextState ≠ 101 :=
    symSteps_accept_no_101 hsteps' hacc'
  have hpath' : SymReachablePath VerifierSym.transition w πs' cfgs' :=
    (symSteps_initial_iff VerifierSym.transition w πs' cfgs').1 hsteps'
  have hsteps_ok' : ∀ step ∈ πs', step.fromState ≤ 101 := by
    intro step hst
    have hm := (symReachable_state_mem_legal hpath').2 step hst
    have hdec : ∀ q ∈ VerifierSym.legalStates, q ≤ 101 := by
      native_decide
    exact hdec step.fromState hm
  have hbranch : ∀ step ∈ πs', Sym.isBranch step.readSym → step.fromState = 2 :=
    symSteps_branch_only_q2 hsteps' hno101' hn100'
  rcases symPath_to_blockPath w hsteps' hacc' hsteps_ok' hbranch with ⟨πc, cfgc, hbp, _hcorr, hst⟩
  refine ⟨πc, cfgc, ?_, ?_⟩
  · exact (tapeSteps_initial_iff subsetSumCBTM (flat4F4 w) πc cfgc).1
      (goodBlockPath_to_tapeSteps (flat4F4 w) (initialConfig subsetSumCBTM (flat4F4 w)) πc cfgc hbp)
  · rw [hst]
    exact acceptStates4_mem_qAccept

-- ===========================================================================
-- §4. witness NTM2：subsetSumCBTM 的 NTM2 化（符号驱动、转移恒等翻译）
-- ===========================================================================

/-- 结果翻译：CBTMTransResult → ℕ × F4 × Dir（单射）。 -/
def cbtmResultToTriple (r : CBTMTransResult) : ℕ × F4 × Dir :=
  (r.nextState, r.writeSym, r.moveDir)

lemma cbtmResultToTriple_injective : Function.Injective cbtmResultToTriple := by
  intro r1 r2 h
  rcases r1 with ⟨n1, w1, d1⟩
  rcases r2 with ⟨n2, w2, d2⟩
  have hn : n1 = n2 := congrArg Prod.fst h
  have hw : w1 = w2 := congrArg (fun x : ℕ × F4 × Dir => x.2.1) h
  have hd : d1 = d2 := congrArg (fun x : ℕ × F4 × Dir => x.2.2) h
  subst n1
  subst w1
  subst d1
  rfl

/-- 复合翻译 = 恒等：ntm2ResultToCBTM ∘ cbtmResultToTriple = id。 -/
lemma ntm2ResultToCBTM_comp_cbtmResultToTriple (r : CBTMTransResult) :
    ntm2ResultToCBTM (cbtmResultToTriple r) = r := by
  rcases r with ⟨n, w, d⟩
  rfl

/-- witness NTM2：subsetSumCBTM 的 NTM2 化（同一状态/字母表/空白符，转移经三重翻译）。 -/
def subsetSumNTM2 : NTM2 := {
  states := subsetSumCBTM.states
  startState := subsetSumCBTM.startState
  acceptStates := subsetSumCBTM.acceptStates
  rejectStates := subsetSumCBTM.rejectStates
  alphabet := subsetSumCBTM.alphabet
  transition := fun (q, s, _i) => (subsetSumCBTM.transition (q, s, 0)).image cbtmResultToTriple
  blankSym := subsetSumCBTM.blankSym
  h_blank_in_alphabet := subsetSumCBTM.h_blank_in_alphabet
  h_start_in_states := subsetSumCBTM.h_start_in_states
  h_accept_subset := subsetSumCBTM.h_accept_subset
  h_reject_subset := subsetSumCBTM.h_reject_subset
  h_accept_reject_disjoint := subsetSumCBTM.h_accept_reject_disjoint
  h_branch_rule := by
    intro q s i hs
    change if F4.im s then
        ((subsetSumCBTM.transition (q, s, 0)).image cbtmResultToTriple).card = 2 else
        ((subsetSumCBTM.transition (q, s, 0)).image cbtmResultToTriple).card = 1
    have hcard : ((subsetSumCBTM.transition (q, s, 0)).image cbtmResultToTriple).card =
        (subsetSumCBTM.transition (q, s, 0)).card := by
      rw [Finset.card_image_of_injective (subsetSumCBTM.transition (q, s, 0)) cbtmResultToTriple_injective]
    have hb := subsetSumCBTM.h_branch_rule q s 0 hs
    by_cases him : F4.im s
    · rw [if_pos him, hcard]
      exact (by simpa [him] using hb)
    · rw [if_neg him, hcard]
      exact (by simpa [him] using hb)
  h_write_projection := by
    intro q s i hs him r hr
    change r ∈ (subsetSumCBTM.transition (q, s, 0)).image cbtmResultToTriple at hr
    rcases Finset.mem_image.mp hr with ⟨r0, hr0, hf⟩
    rw [← hf]
    change F4.im r0.writeSym = false
    exact (subsetSumCBTM.h_projection_constraint q s 0 hs him).2 r0 hr0
  h_alphabet_all := by
    rfl
  h_transition_state_mem := by
    intro q s i hs r hr
    change r ∈ (subsetSumCBTM.transition (q, s, 0)).image cbtmResultToTriple at hr
    rcases Finset.mem_image.mp hr with ⟨r0, hr0, hf⟩
    rw [← hf]
    change r0.nextState ∈ subsetSumCBTM.states
    exact subsetSumCBTM.isValid q s 0 hs r0 hr0
  h_transition_outside := by
    intro q s i hsnot
    have hout : subsetSumCBTM.transition (q, s, 0) = ∅ :=
      subsetSumCBTM.h_transition_outside q s 0 hsnot
    change (subsetSumCBTM.transition (q, s, 0)).image cbtmResultToTriple = ∅
    rw [hout]
    rfl
}

/-- CBTM 结构相等：7 个数据字段相等即整体相等（Prop 字段证明无关自动）。 -/
theorem cbtm_eq_of_fields {M₁ M₂ : CBTM}
    (h1 : M₁.states = M₂.states) (h2 : M₁.startState = M₂.startState)
    (h3 : M₁.acceptStates = M₂.acceptStates) (h4 : M₁.rejectStates = M₂.rejectStates)
    (h5 : M₁.alphabet = M₂.alphabet) (h6 : M₁.transition = M₂.transition)
    (h7 : M₁.blankSym = M₂.blankSym) : M₁ = M₂ := by
  rcases M₁ with ⟨a1, a2, a3, a4, a5, a6, a7, p1, p2, p3, p4, p5, p6, p7, p8, p9⟩
  rcases M₂ with ⟨b1, b2, b3, b4, b5, b6, b7, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩
  cases h1
  cases h2
  cases h3
  cases h4
  cases h5
  cases h6
  cases h7
  congr
  all_goals exact Subsingleton.elim _ _

/-- toCBTM（恒等翻译）保持：NTM2.toCBTM subsetSumNTM2 = subsetSumCBTM。 -/
theorem toCBTM_subsetSumNTM2_eq : NTM2.toCBTM subsetSumNTM2 = subsetSumCBTM := by
  -- 结构逐字段：states/startState/acceptStates/rejectStates/alphabet/blankSym 定义级相等
  -- transition 字段：函数外延 + image 复合 + 复合 = id + 位置无关
  have htrans : NTM2.toCBTMTrans subsetSumNTM2 = subsetSumCBTM.transition := by
    funext p
    rcases p with ⟨q, s, i⟩
    by_cases hs : s ∈ subsetSumNTM2.alphabet
    · dsimp [NTM2.toCBTMTrans, subsetSumNTM2] at hs ⊢
      have htrans_i : (subsetSumCBTM.transition (q, s, i)) = (subsetSumCBTM.transition (q, s, 0)) := by
        rfl
      rw [htrans_i]
      simp [hs]
      apply Finset.ext
      intro r
      constructor
      · intro hr
        rcases Finset.mem_image.mp hr with ⟨r0, hr0, hf⟩
        rw [← hf]
        rcases Finset.mem_image.mp hr0 with ⟨r1, hr1, hf1⟩
        rw [← hf1]
        rw [ntm2ResultToCBTM_comp_cbtmResultToTriple r1]
        exact hr1
      · intro hr0
        exact Finset.mem_image.mpr ⟨cbtmResultToTriple r, Finset.mem_image.mpr ⟨r, hr0, rfl⟩,
          ntm2ResultToCBTM_comp_cbtmResultToTriple r⟩
    · have hsnotM : s ∉ subsetSumCBTM.alphabet := by
        simpa [subsetSumNTM2] using hs
      simp [NTM2.toCBTMTrans, hs]
      rw [subsetSumCBTM.h_transition_outside q s i hsnotM]
  dsimp [NTM2.toCBTM, subsetSumNTM2, subsetSumCBTM]
  apply cbtm_eq_of_fields
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact htrans
  · rfl

-- ===========================================================================
-- §3. CBTM 层陷阱吸收与接受路径无陷阱（transition4 已修复：q=101 全局吸收）
-- ===========================================================================

-- 注：transition4_trap_q101 在修复 101 泄漏后（相位 11 好路径对 q=101 给 (101,0,0)）为真命题。
--   旧版本（假命题）保留于 git 历史。
/-- encodeState q ph reg 的 decodeState q 分量 = q（总偏移 < stepsPerSym*regBound）。 -/
lemma decodeState_encodeState_q_eq (q ph reg : ℕ) (hoff : ph * regBound + reg < stepsPerSym * regBound) :
    (decodeState (encodeState q ph reg)).1 = q := by
  dsimp [decodeState, encodeState, stepsPerSym, regBound]
  ring_nf
  rw [Nat.div_eq_of_lt_le (k := q) (n := 98304) (m := q * 98304 + ph * 8192 + reg)
    (by omega : q * 98304 ≤ q * 98304 + ph * 8192 + reg)
    (by nlinarith [hoff] : q * 98304 + ph * 8192 + reg < (q + 1) * 98304)]

/-- 陷阱 nphase 的偏移界（ph < 12）。 -/
lemma trap_off_nphase_lt (ph : ℕ) (hph : ph < 12) :
    (if ph = 11 then 0 else ph + 1) * regBound + 0 < stepsPerSym * regBound := by
  dsimp [stepsPerSym, regBound]
  by_cases h11 : ph = 11
  · simp [h11]
  · have hlt : ph + 1 < 12 := by omega
    rw [if_neg h11]
    have hlt' : (ph + 1) * 8192 < 12 * 8192 := (Nat.mul_lt_mul_right (by decide : 0 < 8192)).2 hlt
    simpa using hlt'

/-- 读阶段（ph<3）单结果的偏移界。 -/
lemma trap_off_read_lt (ph reg buf : ℕ) (hph : ph < 3) (hreg : reg < 8192) (hbuf : buf ≤ 48) :
    (ph + 1) * regBound + (reg + buf) < stepsPerSym * regBound := by
  dsimp [stepsPerSym, regBound]
  have h1 : (ph + 1) * 8192 ≤ 3 * 8192 := Nat.mul_le_mul_right 8192 (by omega : ph + 1 ≤ 3)
  nlinarith [h1, hreg, hbuf]

/-- 移动阶段（ph<12 且 ph≠11）好路径的偏移界。 -/
lemma trap_off_mid_lt (ph reg : ℕ) (hph : ph < 12) (hne : ph ≠ 11) (hreg : reg < 8192) :
    (ph + 1) * regBound + reg < stepsPerSym * regBound := by
  dsimp [stepsPerSym, regBound]
  have h1 : (ph + 1) * 8192 ≤ 11 * 8192 := Nat.mul_le_mul_right 8192 (by omega : ph + 1 ≤ 11)
  nlinarith [h1, hreg]

/-- 写回阶段（c ≤ 11 常量）的偏移界。 -/
lemma trap_off_const_lt (c reg : ℕ) (hc : c ≤ 11) (hreg : reg < 8192) :
    c * regBound + reg < stepsPerSym * regBound := by
  dsimp [stepsPerSym, regBound]
  have h1 : c * 8192 ≤ 11 * 8192 := Nat.mul_le_mul_right 8192 hc
  nlinarith [h1, hreg]

/-- transition4：起点状态 q = 101 → 所有结果的 nextState 解码 q = 101（陷阱吸收）。 -/
lemma transition4_trap_q101 (st : ℕ) (s : F4) (r : CBTMTransResult)
    (hq : (decodeState st).1 = 101) (hr : r ∈ transition4 st s) :
    (decodeState r.nextState).1 = 101 := by
  dsimp [transition4] at hr
  have hph : (decodeState st).2.1 < 12 := by
    dsimp [decodeState, stepsPerSym, regBound]
    exact Nat.mod_lt _ (by decide : 0 < 12)
  have hreg : (decodeState st).2.2 < 8192 := by
    dsimp [decodeState, regBound]
    exact Nat.mod_lt _ (by decide : 0 < regBound)
  have hqs : min (decodeState st).1 101 = 101 := by rw [hq]; rfl
  by_cases hph3 : (decodeState st).2.1 < 3
  · -- 读阶段 0-2
    rw [if_pos hph3] at hr
    by_cases him : F4.im s
    · rw [if_pos him] at hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl <;>
        rw [decodeState_encodeState_q_eq 101 (if (decodeState st).2.1 = 11 then 0 else (decodeState st).2.1 + 1) 0
          (trap_off_nphase_lt (decodeState st).2.1 hph)]
    · rw [if_neg him] at hr
      simp only [Finset.mem_singleton] at hr
      subst r
      rw [hqs]
      have hpow : 4 ^ (decodeState st).2.1 ≤ 16 := by
        exact pow_le_pow_right₀ (by norm_num : 0 < 4) (by omega : (decodeState st).2.1 ≤ 2)
      have hbuf : bufOf3s (decodeState st).2.1 s (decodeState st).2.2 ≤ 48 := by
        dsimp [bufOf3s]
        split_ifs <;> nlinarith
      rw [decodeState_encodeState_q_eq 101 ((decodeState st).2.1 + 1)
        ((decodeState st).2.2 + bufOf3s (decodeState st).2.1 s (decodeState st).2.2)
        (trap_off_read_lt (decodeState st).2.1 (decodeState st).2.2
          (bufOf3s (decodeState st).2.1 s (decodeState st).2.2) hph3 hreg hbuf)]
  · by_cases hphE : (decodeState st).2.1 = 3
    · -- 合成查表（phase 3）
      rw [if_neg hph3, if_pos hphE] at hr
      rcases hnone2 : symOf4F4 (f4ofBuf (decodeState st).2.2).1 (f4ofBuf (decodeState st).2.2).2.1
          (f4ofBuf (decodeState st).2.2).2.2 s with _ | sym
      · -- none 支：im → trap 双结果；¬im → trap1 单结果
        simp [hnone2] at hr
        by_cases him : F4.im s
        · rw [if_pos him] at hr
          simp only [Finset.mem_insert, Finset.mem_singleton] at hr
          rcases hr with rfl | rfl <;>
            rw [decodeState_encodeState_q_eq 101 (if (decodeState st).2.1 = 11 then 0 else (decodeState st).2.1 + 1) 0
              (trap_off_nphase_lt (decodeState st).2.1 hph)]
        · rw [if_neg him] at hr
          simp only [Finset.mem_singleton] at hr
          subst r
          rw [decodeState_encodeState_q_eq 101 (if (decodeState st).2.1 = 11 then 0 else (decodeState st).2.1 + 1) 0
            (trap_off_nphase_lt (decodeState st).2.1 hph)]
      · -- some sym 支
        simp [hnone2] at hr
        by_cases him : F4.im s
        · rw [if_pos him] at hr
          have hnq2 : ¬ (min (decodeState st).1 101 = 2 ∧ (f4ofBuf (decodeState st).2.2).1 = F4.zero ∧ F4.re s = false) := by
            intro h
            exact (by rw [hqs]; norm_num : min (decodeState st).1 101 ≠ 2) h.1
          rw [if_neg hnq2] at hr
          simp only [Finset.mem_insert, Finset.mem_singleton] at hr
          rcases hr with rfl | rfl <;>
            rw [decodeState_encodeState_q_eq 101 (if (decodeState st).2.1 = 11 then 0 else (decodeState st).2.1 + 1) 0
              (trap_off_nphase_lt (decodeState st).2.1 hph)]
        · rw [if_neg him] at hr
          rcases Finset.mem_image.mp hr with ⟨r0, hr0, hf⟩
          rw [← hf]
          have hq0 : r0.nextState = 101 := by
            have hr0' : r0 ∈ VerifierSym.transition (101, sym) := by
              rw [hqs] at hr0
              exact hr0
            exact symTransition_trap101_absorb sym r0 hr0'
          rw [hq0]
          have henc : encodeResult r0 < 8192 := by
            dsimp [encodeResult, skOf, dirOf]
            rw [hq0]
            rcases r0.writeSym with ⟨k, m⟩
            cases k <;> cases m <;> cases r0.moveDir <;> norm_num
          rw [decodeState_encodeState_q_eq 101 4 (encodeResult r0)
            (trap_off_const_lt 4 (encodeResult r0) (by norm_num) henc)]
    · by_cases hph8 : (decodeState st).2.1 < 8
      · -- 写回阶段 4-7
        rw [if_neg hph3, if_neg hphE, if_pos hph8] at hr
        by_cases him : F4.im s
        · rw [if_pos him] at hr
          simp only [Finset.mem_insert, Finset.mem_singleton] at hr
          rcases hr with rfl | rfl <;>
            rw [decodeState_encodeState_q_eq 101 (if (decodeState st).2.1 = 11 then 0 else (decodeState st).2.1 + 1) 0
              (trap_off_nphase_lt (decodeState st).2.1 hph)]
        · rw [if_neg him] at hr
          by_cases hp4 : (decodeState st).2.1 = 4
          · rw [if_pos hp4] at hr
            simp only [Finset.mem_singleton] at hr
            subst r
            rw [hqs]
            rw [decodeState_encodeState_q_eq 101 5 (decodeState st).2.2
              (trap_off_const_lt 5 (decodeState st).2.2 (by norm_num) hreg)]
          · rw [if_neg hp4] at hr
            by_cases hp5 : (decodeState st).2.1 = 5
            · rw [if_pos hp5] at hr
              simp only [Finset.mem_singleton] at hr
              subst r
              rw [hqs]
              rw [decodeState_encodeState_q_eq 101 6 (decodeState st).2.2
                (trap_off_const_lt 6 (decodeState st).2.2 (by norm_num) hreg)]
            · rw [if_neg hp5] at hr
              by_cases hp6 : (decodeState st).2.1 = 6
              · rw [if_pos hp6] at hr
                simp only [Finset.mem_singleton] at hr
                subst r
                rw [hqs]
                rw [decodeState_encodeState_q_eq 101 7 (decodeState st).2.2
                  (trap_off_const_lt 7 (decodeState st).2.2 (by norm_num) hreg)]
              · rw [if_neg hp6] at hr
                simp only [Finset.mem_singleton] at hr
                subst r
                rw [hqs]
                rw [decodeState_encodeState_q_eq 101 8 (decodeState st).2.2
                  (trap_off_const_lt 8 (decodeState st).2.2 (by norm_num) hreg)]
      · by_cases hph12 : (decodeState st).2.1 < 12
        · -- 移动阶段 8-11
          rw [if_neg hph3, if_neg hphE, if_neg hph8, if_pos hph12] at hr
          by_cases him : F4.im s
          · rw [if_pos him] at hr
            simp only [Finset.mem_insert, Finset.mem_singleton] at hr
            by_cases h11 : (decodeState st).2.1 = 11
            · rcases hr with rfl | rfl
              · -- 好路径：q=101 → (101,0,0) 吸收
                rw [show (if (decodeState st).1 = 101 then 101 else min (decodeResult (decodeState st).2.2).nextState 101) = 101 by simp [hq]]
                simp [h11]
                rw [decodeState_encodeState 101 0 0 (by norm_num) (by norm_num)]
              · simp [h11]
                rw [decodeState_encodeState 101 0 0 (by norm_num) (by norm_num)]
            · rcases hr with rfl | rfl
              · rw [hqs]
                simp only [h11, if_false] at ⊢
                rw [decodeState_encodeState_q_eq 101 ((decodeState st).2.1 + 1) (decodeState st).2.2
                  (trap_off_mid_lt (decodeState st).2.1 (decodeState st).2.2 hph12 h11 hreg)]
              · simp only [h11, if_false] at ⊢
                rw [decodeState_encodeState_q_eq 101 ((decodeState st).2.1 + 1) 0
                  (trap_off_mid_lt (decodeState st).2.1 0 hph12 h11 (by norm_num))]
          · rw [if_neg him] at hr
            by_cases hq101 : (decodeState st).1 = 101
            · rw [if_pos hq101] at hr
              simp only [Finset.mem_singleton] at hr
              subst r
              rw [decodeState_encodeState_q_eq 101 (if (decodeState st).2.1 = 11 then 0 else (decodeState st).2.1 + 1) 0
                (trap_off_nphase_lt (decodeState st).2.1 hph)]
            · exfalso
              exact hq101 hq
        · -- phase ≥ 12
          rw [if_neg hph3, if_neg hphE, if_neg hph8, if_neg hph12] at hr
          by_cases him : F4.im s
          · rw [if_pos him] at hr
            simp only [Finset.mem_insert, Finset.mem_singleton] at hr
            rcases hr with rfl | rfl <;>
              rw [decodeState_encodeState_q_eq 101 (if (decodeState st).2.1 = 11 then 0 else (decodeState st).2.1 + 1) 0
                (trap_off_nphase_lt (decodeState st).2.1 hph)]
          · rw [if_neg him] at hr
            simp only [Finset.mem_singleton] at hr
            subst r
            rw [decodeState_encodeState_q_eq 101 (if (decodeState st).2.1 = 11 then 0 else (decodeState st).2.1 + 1) 0
              (trap_off_nphase_lt (decodeState st).2.1 hph)]

/-- 第 t 步的 fromState = configAt t 的 state（TapeSteps 与 configAt 一致）。 -/
lemma tapeSteps_fromState_eq_configAt_state {w : List F4} {π : ComputationPath}
    {cfg : CBTMConfig subsetSumCBTM w}
    (h : TapeSteps subsetSumCBTM w (initialConfig subsetSumCBTM w) π cfg)
    (t : ℕ) (ht : t < π.length) :
    (π.get ⟨t, ht⟩).fromState = (CBTM.configAt subsetSumCBTM w π t).state := by
  induction h generalizing t with
  | nil =>
      simp at ht
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      by_cases ht' : t < π₀.length
      · have hg : (π₀ ++ [step]).get ⟨t, ht⟩ = π₀.get ⟨t, ht'⟩ := by
          simpa [List.get] using (List.getElem_append_left ht')
        rw [hg]
        rw [configAt_append_left π₀ step (by omega)]
        exact ih t ht'
      · have ht_eq : t = π₀.length := by
          have hlen : (π₀ ++ [step]).length = π₀.length + 1 := by simp
          rw [hlen] at ht
          omega
        subst t
        have hg : (π₀ ++ [step]).get ⟨π₀.length, ht⟩ = step := by
          simp [List.getElem_append_right, List.getElem_cons_zero]
        rw [hg]
        rw [configAt_append_left π₀ step (by omega)]
        rcases tapeSteps_state_head_eq_configAt hprev with ⟨hst, _⟩
        rw [← hst]
        rw [hfrom]

-- 注：accept_path_no_trap 依赖 transition4_trap_q101（原注已作废：该引理在修复 101 泄漏后为**真命题**，见本文件 :495 注；
--   已被 ① 线 A-1 装配使用：SubsetSumVerifierPosBound:383/389）。
/-- 接受路径无陷阱：任何步的 nextState 解码 q ≠ 101（101 全局吸收 + 终态 ≠ 101）。 -/
lemma accept_path_no_trap {w : List F4} {π : ComputationPath} {cfg : CBTMConfig subsetSumCBTM w}
    (h : TapeSteps subsetSumCBTM w (initialConfig subsetSumCBTM w) π cfg)
    (hacc : cfg.state ∈ acceptStates4) :
    ∀ k (hk : k < π.length), (decodeState (π.get ⟨k, hk⟩).result.nextState).1 ≠ 101 := by
  intro k hk h101
  -- configAt (k+1) 的 state = 第 k 步 nextState → q = 101
  have hstate_after : (CBTM.configAt subsetSumCBTM w π (k + 1)).state =
      (π.get ⟨k, hk⟩).result.nextState := by
    rw [configAt_succ_stepConfig subsetSumCBTM w π k hk]
    rfl
  have hq_after : (decodeState (CBTM.configAt subsetSumCBTM w π (k + 1)).state).1 = 101 := by
    rw [hstate_after]
    exact h101
  -- 陷阱吸收：t ≥ k+1 恒 q = 101（对 m 归纳）
  have hq_all : ∀ t, k + 1 ≤ t → t ≤ π.length →
      (decodeState (CBTM.configAt subsetSumCBTM w π t).state).1 = 101 := by
    intro t hkle htl
    rcases Nat.exists_eq_add_of_le hkle with ⟨m, rfl⟩
    induction m with
    | zero => exact hq_after
    | succ m ih =>
        have ht' : (k + 1) + m < π.length := by omega
        have hprev_q : (decodeState (CBTM.configAt subsetSumCBTM w π ((k + 1) + m)).state).1 = 101 :=
          ih (by omega : k + 1 ≤ (k + 1) + m) (by omega : (k + 1) + m ≤ π.length)
        change (decodeState (CBTM.configAt subsetSumCBTM w π ((k + 1) + m + 1)).state).1 = 101
        rw [configAt_succ_stepConfig subsetSumCBTM w π ((k + 1) + m) ht']
        dsimp [stepConfig]
        have hst_prev : (CBTM.configAt subsetSumCBTM w π ((k + 1) + m)).state =
            (π.get ⟨(k + 1) + m, ht'⟩).fromState := by
          exact (tapeSteps_fromState_eq_configAt_state h ((k + 1) + m) ht').symm
        rw [hst_prev] at hprev_q
        have htr : (π.get ⟨(k + 1) + m, ht'⟩).result ∈
            transition4 (π.get ⟨(k + 1) + m, ht'⟩).fromState (π.get ⟨(k + 1) + m, ht'⟩).readSym := by
          have htran := tapeSteps_step_trans h ((k + 1) + m) ht'
          rcases htran with ⟨pos, hp⟩
          simpa [subsetSumCBTM] using hp
        exact transition4_trap_q101 (π.get ⟨(k + 1) + m, ht'⟩).fromState
          (π.get ⟨(k + 1) + m, ht'⟩).readSym (π.get ⟨(k + 1) + m, ht'⟩).result hprev_q htr
  -- 终态 q = 101 与 hacc（q = 100）矛盾
  have hq_end : (decodeState (CBTM.configAt subsetSumCBTM w π π.length).state).1 = 101 :=
    hq_all π.length (by omega) (by omega)
  rcases tapeSteps_state_head_eq_configAt h with ⟨hst, _⟩
  rw [← hst] at hq_end
  rcases Finset.mem_image.mp hacc with ⟨reg, hreg, hacc'⟩
  rw [← hacc'] at hq_end
  have hdec : decodeState (encodeState VerifierSym.qAccept 0 reg) = (VerifierSym.qAccept, 0, reg) := by
    exact decodeState_encodeState VerifierSym.qAccept 0 reg (by norm_num)
      (by simpa [regBound] using Finset.mem_range.mp hreg)
  rw [hdec] at hq_end
  norm_num [VerifierSym.qAccept] at hq_end

-- 注：tapeAccepts_implies_symAccepts 与 subsetSumCBTM_accepts_iff_symAccepts 依赖 accept_path_no_trap
--   （链上的 transition4_trap_q101 修复 101 泄漏后为真命题，原注已作废）。symAccepts_implies_tapeAccepts（完备性方向）已独立保留。
/-- 可靠性：CBTM 接受 ⟹ Sym 接受（对 Sym 编码串 w）。 -/
theorem tapeAccepts_implies_symAccepts (w : List Sym) :
    subsetSumCBTM.tapeAccepts (flat4F4 w) →
    symAccepts VerifierSym.transition VerifierSym.acceptStates w := by
  intro haccT
  rcases haccT with ⟨π, cfg, hr, hacc⟩
  rcases (tapeSteps_initial_iff subsetSumCBTM (flat4F4 w) π cfg).mpr hr with hsteps
  have htrap : ∀ k (hk : k < π.length), (decodeState (π.get ⟨k, hk⟩).result.nextState).1 ≠ 101 :=
    accept_path_no_trap hsteps hacc
  have hbp : GoodBlockPath (flat4F4 w) (initialConfig subsetSumCBTM (flat4F4 w)) π cfg :=
    accept_path_is_good_block_path hsteps (by simpa [subsetSumCBTM] using hacc) htrap
      (initialBlockCorrespond w) (by dsimp [symInitialConfig, SymConfig.mk]; norm_num)
  rcases project_path w π cfg hbp htrap with ⟨πs, cfgs', hreach, hcorr', _hlen⟩
  have haccS : cfgs'.state = VerifierSym.qAccept := by
    -- blockCorrespond 的状态分量：cfgc'.state = encodeState cfgs'.state 0 0
    -- 而 hacc : cfg.state ∈ acceptStates4 = encodeState 100 0 reg
    rcases Finset.mem_image.mp hacc with ⟨reg, hreg, hacc'⟩
    have hst : cfg.state = encodeState cfgs'.state 0 0 := hcorr'.1
    have hdec := decodeState_encodeState VerifierSym.qAccept 0 reg (by norm_num)
      (by simpa [regBound] using Finset.mem_range.mp hreg)
    have hdec2 := decodeState_encodeState cfgs'.state 0 0 (by norm_num) (by norm_num)
    have hcong := congrArg decodeState (show cfg.state = encodeState VerifierSym.qAccept 0 reg by
      rw [← hacc'])
    rw [hst] at hcong
    rw [hdec, hdec2] at hcong
    exact congrArg Prod.fst hcong
  exact symReachable_accepts hreach haccS

/-- 编译正确性：CBTM 接受 ⟺ Sym 接受（w 为 Sym 编码串）。 -/
theorem subsetSumCBTM_accepts_iff_symAccepts (w : List Sym) :
    subsetSumCBTM.tapeAccepts (flat4F4 w) ↔
      symAccepts VerifierSym.transition VerifierSym.acceptStates w := by
  constructor
  · exact tapeAccepts_implies_symAccepts w
  · exact symAccepts_implies_tapeAccepts w

-- ===========================================================================
-- §5. 分叉计数：分支步数 = 初始分支格数（α/β 只减不增，每格至多读一次分支）
-- ===========================================================================

/-- 合法状态下写出的符号恒非分支（α/β 只减不增；101 陷阱除外——写回原符号）。 -/
lemma symTransition_write_not_branch (q : ℕ) (s : Sym) (r : SymTransResult)
    (hq : q ∈ VerifierSym.legalStates) (hr : r ∈ VerifierSym.transition (q, s))
    (hrs : r.nextState ≠ 101) (hqne : q ≠ 100) :
    ¬ Sym.isBranch r.writeSym := by
  by_cases hqlt : q < 102
  · have hb : ∀ q : Fin 102, (q : ℕ) ≠ 100 → ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), Sym.mk k m) → r.nextState ≠ 101 →
          (q : ℕ) ∈ VerifierSym.legalStates → ¬ Sym.isBranch r.writeSym := by
      native_decide
    rcases s with ⟨k, m⟩
    exact hb ⟨q, hqlt⟩ hqne k m r hr hrs hq
  · exfalso
    have hout : q ∉ VerifierSym.legalStates := by
      intro hqin
      simp [VerifierSym.legalStates] at hqin
      omega
    exact hout hq

/-- 101 陷阱步写回原符号。 -/
lemma symTransition_write_101_no_issue (q : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h101 : r.nextState = 101) :
    r.writeSym = s := by
  by_cases hqlt : q < 102
  · have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 101 → r.writeSym = s := by
      native_decide
    exact hb ⟨q, hqlt⟩ s r hr h101
  · have hout : q ∉ VerifierSym.legalStates := by
      intro hqin
      simp [VerifierSym.legalStates] at hqin
      omega
    rw [transition_of_not_legal q s hout] at hr
    simp at hr
    subst r
    rfl

def tapeBranchCount (input : List Sym) (tape : ℤ → Sym) : ℕ :=
  ((List.range input.length).filter (fun i => Sym.isBranch (tape (Int.ofNat i)))).length

/-- 初始磁带：输入区内分支格数 = 输入的分支符号数。 -/
lemma tapeBranchCount_initial (input : List Sym) :
    tapeBranchCount input (symInitialConfig input).tape = (input.filter Sym.isBranch).length := by
  induction input with
  | nil => rfl
  | cons x xs ih =>
      rw [tapeBranchCount]
      rw [List.length_cons]
      rw [List.range_succ_eq_map]
      rw [List.filter_cons]
      rw [List.filter_map]
      have hcg : (List.range xs.length).filter ((fun i => Sym.isBranch (
          (symInitialConfig (x :: xs)).tape (Int.ofNat i))) ∘ Nat.succ) =
          (List.range xs.length).filter (fun i => Sym.isBranch (
            (symInitialConfig xs).tape (Int.ofNat i))) := by
        apply List.filter_congr
        intro i hi
        simp only [Function.comp_apply]
        have hilt : i < xs.length := List.mem_range.mp hi
        have hlt : Nat.succ i < (x :: xs).length := by
          simpa using (Nat.succ_lt_succ hilt)
        have hcons : (x :: xs)[Nat.succ i]'hlt = xs[i] := by
          rw [List.getElem_cons]
          simp [Nat.succ_ne_zero]
        have hL : (symInitialConfig (x :: xs)).tape (Int.ofNat (Nat.succ i)) = xs[i] := by
          have hbase : (symInitialConfig (x :: xs)).tape (Int.ofNat (Nat.succ i)) =
              (x :: xs)[Nat.succ i]'hlt := by
            have hguard : 0 ≤ (Int.ofNat (Nat.succ i) : ℤ) ∧
                (Int.ofNat (Nat.succ i) : ℤ).toNat < (x :: xs).length := by
              constructor
              · exact Int.natCast_nonneg (Nat.succ i)
              · simpa using hlt
            dsimp [symInitialConfig, SymConfig.mk]
            apply dif_pos hguard
          rw [hbase, hcons]
        have hR : (symInitialConfig xs).tape (Int.ofNat i) = xs[i] := by
          simp [symInitialConfig, SymConfig.mk, hilt]
        rw [hL, hR]
      rw [hcg]
      have h0 : (symInitialConfig (x :: xs)).tape (Int.ofNat 0) = x := by
        simp [symInitialConfig, SymConfig.mk]
      rw [h0]
      have hih : ((List.range xs.length).filter (fun i => Sym.isBranch (
          (symInitialConfig xs).tape (Int.ofNat i)))).length = (xs.filter Sym.isBranch).length := by
        simpa [tapeBranchCount] using ih
      by_cases hx : Sym.isBranch x <;>
        simp [hx, List.length_cons] at *
      all_goals rw [hih] <;> rfl

/-- 分支步（非 100/101 态）写 sel/nosel。 -/
lemma symTransition_branch_write_sel_nosel (q : ℕ) (s : Sym) (r : SymTransResult)
    (hbr : Sym.isBranch s) (hr : r ∈ VerifierSym.transition (q, s))
    (hrs : r.nextState ≠ 101) (hqne : q ≠ 100) :
    r.writeSym = Sym.sel ∨ r.writeSym = Sym.nosel := by
  have hq2 := symTransition_branch_q2 q s r hbr hr hrs hqne
  by_cases hqlt : q < 102
  · have hb : ∀ q : Fin 102, ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), (k, m)) →
          (q : ℕ) = 2 → SymKind.isBranch k → r.nextState ≠ 101 →
            r.writeSym = Sym.sel ∨ r.writeSym = Sym.nosel := by
      native_decide
    rcases s with ⟨k, m⟩
    exact hb ⟨q, hqlt⟩ k m r hr hq2 hbr hrs
  · exfalso
    have hout : q ∉ VerifierSym.legalStates := by
      intro hqin
      simp [VerifierSym.legalStates] at hqin
      omega
    have hmem : r ∈ ({SymTransResult.mk 101 s Dir.S} : Finset SymTransResult) := by
      simpa [VerifierSym.transition, hout] using hr
    rw [Finset.mem_singleton] at hmem
    exact hrs (by simpa [hmem])

/-- 两个谓词仅在 g（∈ range n）处不同（P g = true、P' g = false）时 filter 长度差 1。 -/
lemma filter_length_diff_single {n g : ℕ} (hg : g < n) {P P' : ℕ → Bool}
    (hcongr : ∀ i < n, i ≠ g → P i = P' i) (hgP : P g = true) (hgP' : P' g = false) :
    ((List.range n).filter P).length = ((List.range n).filter P').length + 1 := by
  induction n generalizing g with
  | zero => cases hg
  | succ n ih =>
      rw [List.range_succ, List.filter_append, List.filter_singleton, List.length_append]
      by_cases hgn : g = n
      · subst g
        have hcongr' : (List.range n).filter P = (List.range n).filter P' := by
          apply List.filter_congr
          intro i hi
          have hilt : i < n := by simpa using (List.mem_range.mp hi)
          exact hcongr i (Nat.lt_trans hilt (Nat.lt_succ_self n)) (by omega)
        rw [hcongr']
        simp [List.length_singleton, hgP, hgP']
      · have ih' := ih (by omega : g < n) (fun i hilt hine => hcongr i (by omega) (by omega))
          hgP hgP'
        have hn : P n = P' n := hcongr n (by omega) (by omega)
        rw [ih', hn]
        rw [List.filter_append, List.length_append, List.filter_singleton]
        omega

lemma symReachable_tape_outside_nonbranch {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101)
    (hno100 : ∀ step ∈ π, step.fromState ≠ 100) :
    ∀ i : ℤ, i < 0 ∨ (input.length : ℤ) ≤ i → ¬ Sym.isBranch (cfg.tape i) := by
  induction h with
  | nil =>
      intro i hi
      dsimp [symInitialConfig, SymConfig.mk]
      by_cases h0 : 0 ≤ i ∧ i.toNat < input.length
      · exfalso
        omega
      · simp [h0, Sym.blank, Sym.isBranch, SymKind.isBranch]
  | cons π₀ step cfg₀ hprev hfrom hread htrans ih =>
      intro i hi
      have hst := (symReachable_state_mem_legal hprev).1
      dsimp [symStepConfig]
      by_cases hi' : i = cfg₀.headPos
      · rw [if_pos hi']
        by_cases h101 : step.result.nextState = 101
        · have hw := symTransition_write_101_no_issue cfg₀.state (cfg₀.tape cfg₀.headPos)
            step.result htrans h101
          rw [hw]
          rw [← hi']
          exact ih (fun st hst => hno101 st (by simpa [List.mem_append] using Or.inl hst))
            (fun st hst => hno100 st (by simpa [List.mem_append] using Or.inl hst)) i hi
        · have hqne100' : cfg₀.state ≠ 100 := by
            intro hq
            have h100' : step.fromState ≠ 100 := hno100 step (by simp)
            exact h100' (by rw [hfrom, hq])
          exact symTransition_write_not_branch cfg₀.state (cfg₀.tape cfg₀.headPos)
            step.result hst htrans h101 hqne100'
      · rw [if_neg hi']
        exact ih (fun st hst => hno101 st (by simpa [List.mem_append] using Or.inl hst))
          (fun st hst => hno100 st (by simpa [List.mem_append] using Or.inl hst)) i hi

/-- 核心不变量：分支步数 + 当前磁带分支格数 = 初始分支格数（对路径归纳，无 101 步）。 -/
lemma symReachable_branchCount_eq_initial {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101)
    (hno100 : ∀ step ∈ π, step.fromState ≠ 100) :
    (π.filter (fun st => Sym.isBranch st.readSym)).length +
      tapeBranchCount input cfg.tape = (input.filter Sym.isBranch).length := by
  induction h with
  | nil =>
      simpa using tapeBranchCount_initial input
  | cons π₀ step cfg₀ hprev hfrom hread htrans ih =>
      have hno₀ : ∀ st ∈ π₀, st.result.nextState ≠ 101 :=
        fun st hst => hno101 st (by rw [List.mem_append]; left; exact hst)
      have hno100₀ : ∀ st ∈ π₀, st.fromState ≠ 100 :=
        fun st hst => hno100 st (by rw [List.mem_append]; left; exact hst)
      have h101 : step.result.nextState ≠ 101 :=
        hno101 step (by simp)
      have h100 : step.fromState ≠ 100 :=
        hno100 step (by simp)
      have hqne100 : cfg₀.state ≠ 100 := by
        intro hq
        exact h100 (by rw [hfrom, hq])
      have hst₀ := (symReachable_state_mem_legal hprev).1
      have hnb := symTransition_write_not_branch cfg₀.state (cfg₀.tape cfg₀.headPos)
        step.result hst₀ htrans h101 hqne100
      by_cases hb : Sym.isBranch step.readSym
      · -- 分支步：写 sel/nosel（非分支），读格（= cfg₀.headPos）区内且原为分支
        rw [hread] at hb
        have hwsel : step.result.writeSym = Sym.sel ∨ step.result.writeSym = Sym.nosel :=
          symTransition_branch_write_sel_nosel cfg₀.state (cfg₀.tape cfg₀.headPos)
            step.result hb htrans h101 hqne100
        -- 读格区内
        have hg_in : 0 ≤ cfg₀.headPos ∧ cfg₀.headPos.toNat < input.length := by
          by_contra hg
          have hout : cfg₀.headPos < 0 ∨ (input.length : ℤ) ≤ cfg₀.headPos := by omega
          have hnb' := symReachable_tape_outside_nonbranch hprev hno₀ hno100₀ cfg₀.headPos hout
          exact hnb' (by simpa [hread] using hb)
        -- 差分：写格分支 → 非分支，其它不变
        have htape_diff : tapeBranchCount input cfg₀.tape =
            tapeBranchCount input (symStepConfig cfg₀ step.result).tape + 1 := by
          dsimp [tapeBranchCount, symStepConfig, SymConfig.mk]
          have hcongr : ∀ i < input.length, i ≠ cfg₀.headPos.toNat →
              Sym.isBranch (cfg₀.tape (i : ℤ)) = Sym.isBranch (
                (fun j : ℤ => if j = cfg₀.headPos then step.result.writeSym else cfg₀.tape j) (i : ℤ)) := by
            intro i hi hi'
            have hine : (i : ℤ) ≠ cfg₀.headPos := by
              intro h
              exact hi' (by omega)
            simp [hine]
          have hself : Sym.isBranch (cfg₀.tape (cfg₀.headPos.toNat : ℤ)) = true := by
            rw [show (cfg₀.headPos.toNat : ℤ) = cfg₀.headPos by omega]
            simpa [← hread] using hb
          have hself' : Sym.isBranch ((fun j : ℤ => if j = cfg₀.headPos then step.result.writeSym else cfg₀.tape j) (cfg₀.headPos.toNat : ℤ)) = false := by
            simp only [show (cfg₀.headPos.toNat : ℤ) = cfg₀.headPos by omega]
            have hns : Sym.isBranch step.result.writeSym = false := by
              rcases hwsel with h | h <;> rw [h] <;> dsimp [Sym.isBranch, SymKind.isBranch] <;> rfl
            exact hns
          exact filter_length_diff_single hg_in.2 hcongr hself hself'
        -- 路径差分：分支步 +1
        rw [List.filter_append]
        have hP : (decide (step.readSym.1 = SymKind.alpha) ||
            decide (step.readSym.1 = SymKind.beta)) = true := by
          rw [← Bool.decide_or]
          simpa [hread, Sym.isBranch, SymKind.isBranch] using hb
        simp [hP, Bool.decide_or, List.length_append, List.length_singleton]
        have hmain := ih hno₀ hno100₀
        have hmain' : (List.filter (fun st => decide (st.readSym.1 = SymKind.alpha) ||
            decide (st.readSym.1 = SymKind.beta)) π₀).length + tapeBranchCount input cfg₀.tape =
            (List.filter Sym.isBranch input).length := by
          simpa [Sym.isBranch, SymKind.isBranch] using hmain
        rw [← hmain']
        rw [htape_diff]
        ac_rfl
      · -- 非分支步：磁带分支格数不变（写非 branch：write_not_branch）
        have htape_same : tapeBranchCount input cfg₀.tape =
            tapeBranchCount input (symStepConfig cfg₀ step.result).tape := by
          dsimp [tapeBranchCount, symStepConfig, SymConfig.mk]
          apply congrArg List.length
          apply List.filter_congr
          intro i hi
          by_cases hi' : (i : ℤ) = cfg₀.headPos
          · rw [if_pos hi']
            rw [show Sym.isBranch step.result.writeSym = false by
              by_cases hw : Sym.isBranch step.result.writeSym
              · exfalso
                simp [hw] at hnb
              · simpa [hw]]
            rw [hi']
            rw [show Sym.isBranch (cfg₀.tape cfg₀.headPos) = false by
              by_cases hc : Sym.isBranch (cfg₀.tape cfg₀.headPos)
              · exfalso
                simp [hread, hc] at hb
              · simpa [hc]]
          · rw [if_neg hi']
        rw [List.filter_append]
        have hP : (decide (step.readSym.1 = SymKind.alpha) ||
            decide (step.readSym.1 = SymKind.beta)) = false := by
          rw [← Bool.decide_or]
          simpa [Sym.isBranch, SymKind.isBranch] using hb
        simp [hP, Bool.decide_or, List.length_append, List.length_singleton]
        rw [← htape_same]
        simpa [Nat.add_zero] using ih hno₀ hno100₀

/-- 可达路径（无 101 步）的分支步数 ≤ 初始分支格数。 -/
lemma symReachable_branchCount_le_initial {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101)
    (hno100 : ∀ step ∈ π, step.fromState ≠ 100) :
    (π.filter (fun st => Sym.isBranch st.readSym)).length ≤ (input.filter Sym.isBranch).length := by
  have hmain := symReachable_branchCount_eq_initial h hno101 hno100
  omega

-- ============================================================================
-- §6. Canonical 支撑（SymSteps 版）：状态合法 / 写非分支 / 分支格单调 / 分支读步位置互异
-- ============================================================================

/-- SymSteps 版：起始配置状态合法 ⟹ 终点状态合法且每步 fromState 合法。 -/
lemma symSteps_state_mem_legal {cfg₀ cfg : SymConfig} {π : List SymStep}
    (h : SymSteps VerifierSym.transition cfg₀ π cfg)
    (h₀ : cfg₀.state ∈ VerifierSym.legalStates) :
    cfg.state ∈ VerifierSym.legalStates ∧ ∀ step ∈ π, step.fromState ∈ VerifierSym.legalStates := by
  induction h with
  | nil =>
      constructor
      · exact h₀
      · intro st hst
        simp at hst
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      rcases ih with ⟨hst₀, hall⟩
      constructor
      · dsimp [symStepConfig]
        exact symTransition_nextState_mem_legal cfg'.state (cfg'.tape cfg'.headPos)
          step.result hst₀ htrans
      · intro st hstm
        rw [List.mem_append] at hstm
        rcases hstm with hpre | hlast
        · exact hall st hpre
        · rw [List.mem_singleton] at hlast
          rw [hlast]
          rw [hfrom]
          exact hst₀

/-- SymSteps 版：无 101 步、无 100 步的路径中，每步写出的符号非分支。 -/
lemma symSteps_writeSym_nonbranch {cfg₀ cfg : SymConfig} {π : List SymStep}
    (h : SymSteps VerifierSym.transition cfg₀ π cfg)
    (h₀ : cfg₀.state ∈ VerifierSym.legalStates)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101)
    (hno100 : ∀ step ∈ π, step.fromState ≠ 100) :
    ∀ step ∈ π, ¬ Sym.isBranch step.result.writeSym := by
  induction h with
  | nil =>
      intro st hst
      simp at hst
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      intro t ht
      have hno₀ : ∀ st ∈ π₀, st.result.nextState ≠ 101 :=
        fun st hst => hno101 st (by rw [List.mem_append]; left; exact hst)
      have hno100₀ : ∀ st ∈ π₀, st.fromState ≠ 100 :=
        fun st hst => hno100 st (by rw [List.mem_append]; left; exact hst)
      rw [List.mem_append] at ht
      rcases ht with hpre | hlast
      · exact ih hno₀ hno100₀ t hpre
      · rw [List.mem_singleton] at hlast
        rw [hlast]
        have hq : step.fromState ∈ VerifierSym.legalStates := by
          rw [hfrom]
          exact (symSteps_state_mem_legal hprev h₀).1
        have h101 : step.result.nextState ≠ 101 := hno101 step (by simp)
        have h100 : step.fromState ≠ 100 := hno100 step (by simp)
        exact symTransition_write_not_branch step.fromState step.readSym step.result
          hq (by rw [← hfrom, ← hread] at htrans; exact htrans) h101 h100

/-- SymSteps 版：格值分支单调——初始（cfg₀）非分支的格恒非分支。 -/
lemma symSteps_tape_branch_mono {cfg₀ cfg : SymConfig} {π : List SymStep}
    (h : SymSteps VerifierSym.transition cfg₀ π cfg)
    (h₀ : cfg₀.state ∈ VerifierSym.legalStates)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101)
    (hno100 : ∀ step ∈ π, step.fromState ≠ 100) :
    ∀ x : ℤ, ¬ Sym.isBranch (cfg₀.tape x) → ¬ Sym.isBranch (cfg.tape x) := by
  induction h with
  | nil =>
      intro x hx
      exact hx
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      have hno₀ : ∀ st ∈ π₀, st.result.nextState ≠ 101 :=
        fun st hst => hno101 st (by rw [List.mem_append]; left; exact hst)
      have hno100₀ : ∀ st ∈ π₀, st.fromState ≠ 100 :=
        fun st hst => hno100 st (by rw [List.mem_append]; left; exact hst)
      intro x hx0
      have hxmid : ¬ Sym.isBranch (cfg'.tape x) := ih hno₀ hno100₀ x hx0
      dsimp [symStepConfig]
      by_cases hx' : x = cfg'.headPos
      · rw [if_pos hx']
        have hq : step.fromState ∈ VerifierSym.legalStates := by
          rw [hfrom]
          exact (symSteps_state_mem_legal hprev h₀).1
        have h101 : step.result.nextState ≠ 101 := hno101 step (by simp)
        have h100 : step.fromState ≠ 100 := hno100 step (by simp)
        exact symTransition_write_not_branch step.fromState step.readSym step.result
          hq (by rw [← hfrom, ← hread] at htrans; exact htrans) h101 h100
      · rw [if_neg hx']
        exact hxmid


end Mp
