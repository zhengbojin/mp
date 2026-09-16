-- ============================================================================
-- T16:条款⑤(尾缀无关)—— subsetSumNTM2_hrel2
--   .1:原 ⟹ 尾缀版(消费 SubsetSumInNP:443);.2:尾缀版 ⟹ 原(消费 :420)
--   环1:CBTM↔Sym 桥(Compile:452/816,恒等式 rfl/flatMap_append)
--   环2:symAccepts_tail_iff(尾缀模拟引理 symReachablePath_agree_below——唯一新数学)
--   环3:组装(rw 桥 + 两向 iff)
-- ============================================================================
import Mp.SubsetSumVerifierPosBound5
import Mp.SubsetSumCompile

/-! # T16:条款⑤(尾缀无关)— `subsetSumNTM2_hrel2`

`.1` = 原 ⟹ 尾缀版(消费 `SubsetSumInNP:443`);`.2` = 尾缀版 ⟹ 原(消费 `:420`)。
链:CBTM↔Sym 桥(Compile:452/816)→ `symAccepts_tail_iff`(尾缀模拟,唯一新数学)
→ 组装。0 缺口;0 新增公理(全结构归纳 + 既有件继承账)。 -/

set_option maxRecDepth 200000
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

open SymToF4

-- ============================================================
-- 环 2a:尾缀模拟(input₁ 上跑且真前缀头 ∈ [0,N) ⇒ input₂ 上同跑同 π)
-- ============================================================

lemma symReachablePath_agree_below {M : ℕ × Sym → Finset SymTransResult}
    {input₁ input₂ : List Sym} {N : ℤ}
    (hagree₀ : ∀ z, 0 ≤ z → z < N →
      (symInitialConfig input₁).tape z = (symInitialConfig input₂).tape z)
    {π : List SymStep} {cfg : SymConfig} (h : SymReachablePath M input₁ π cfg)
    (hb : ∀ (π₀ : List SymStep) (cfg₀ : SymConfig), SymReachablePath M input₁ π₀ cfg₀ →
      List.IsPrefix π₀ π → π₀ ≠ π → 0 ≤ cfg₀.headPos ∧ cfg₀.headPos < N) :
    ∃ cfg' : SymConfig, SymReachablePath M input₂ π cfg' ∧ cfg'.state = cfg.state ∧
      cfg'.headPos = cfg.headPos ∧
      (∀ z, 0 ≤ z → z < N → cfg'.tape z = cfg.tape z) := by
  revert hb
  induction h with
  | nil =>
      intro _hb
      exact ⟨symInitialConfig input₂, SymReachablePath.nil, rfl, rfl,
        fun z hz0 hzN => (hagree₀ z hz0 hzN).symm⟩
  | cons π₀ step cfg₀ hprev hfrom hread htrans ih =>
      intro hb
      have hne₀ : π₀ ≠ π₀ ++ [step] := by
        intro he
        have hlen := congrArg List.length he
        simp at hlen
      have hbd := hb π₀ cfg₀ hprev ⟨[step], rfl⟩ hne₀
      have hb₀ : ∀ (π₁ : List SymStep) (cfg₁ : SymConfig),
          SymReachablePath M input₁ π₁ cfg₁ → List.IsPrefix π₁ π₀ → π₁ ≠ π₀ →
          0 ≤ cfg₁.headPos ∧ cfg₁.headPos < N := by
        intro π₁ cfg₁ h₁ hpfx₁ hne₁
        exact hb π₁ cfg₁ h₁ (hpfx₁.trans ⟨[step], rfl⟩) (by
          intro he
          rcases hpfx₁ with ⟨s, hs⟩
          have hlen1 := congrArg List.length he
          have hlen2 := congrArg List.length hs
          simp at hlen1 hlen2
          omega)
      rcases ih hb₀ with ⟨cfg₁', hpath₁, hst₁, hhd₁, hag₁⟩
      have hread₁ : cfg₁'.tape cfg₁'.headPos = cfg₀.tape cfg₀.headPos := by
        rw [hhd₁]
        exact hag₁ cfg₀.headPos hbd.1 hbd.2
      have hmem₁ : step.result ∈ M (cfg₁'.state, cfg₁'.tape cfg₁'.headPos) := by
        rw [hst₁, hread₁]
        exact htrans
      -- 原 step 于 input₂ 上的一步三事实
      have hfrom' : step.fromState = cfg₁'.state := hfrom.trans hst₁.symm
      have hread' : step.readSym = cfg₁'.tape cfg₁'.headPos := by
        calc step.readSym = cfg₀.tape cfg₀.headPos := hread
          _ = cfg₁'.tape cfg₀.headPos := (hag₁ cfg₀.headPos hbd.1 hbd.2).symm
          _ = cfg₁'.tape cfg₁'.headPos := by rw [hhd₁]
      refine ⟨symStepConfig cfg₁' step.result,
        SymReachablePath.cons π₀ step cfg₁' hpath₁ hfrom' hread' hmem₁, ?_, ?_, ?_⟩
      · rfl
      · dsimp [symStepConfig]
        rw [hhd₁]
      · intro z hz0 hzN
        dsimp [symStepConfig]
        by_cases hzh : z = cfg₀.headPos
        · rw [hzh, hhd₁]
          simp
        · have hz1 : ¬ (z = cfg₁'.headPos) := by
            intro he
            exact hzh (he.trans hhd₁)
          rw [if_neg hz1, if_neg hzh]
          exact hag₁ z hz0 hzN

-- ============================================================
-- 环 2b:尾缀无关:symAccepts encS ⟺ symAccepts (encS ++ gS)
-- ============================================================

theorem symAccepts_tail_iff (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length) (ht : 0 < inst.target)
    (gS : List Sym) :
    symAccepts VerifierSym.transition VerifierSym.acceptStates (encodeInstanceSym inst) ↔
      symAccepts VerifierSym.transition VerifierSym.acceptStates (encodeInstanceSym inst ++ gS) := by
  have hagree₀ : ∀ z, 0 ≤ z → z < (((encodeInstanceSym inst).length : ℕ) : ℤ) →
      (symInitialConfig (encodeInstanceSym inst)).tape z =
        (symInitialConfig (encodeInstanceSym inst ++ gS)).tape z := by
    intro z hz0 hzN
    simp only [symInitialConfig]
    have hz1 : z.toNat < (encodeInstanceSym inst).length := by omega
    have hz2 : z.toNat < (encodeInstanceSym inst ++ gS).length := by
      rw [List.length_append]
      omega
    rw [dif_pos (show 0 ≤ z ∧ z.toNat < (encodeInstanceSym inst).length from ⟨hz0, hz1⟩),
      dif_pos (show 0 ≤ z ∧ z.toNat < (encodeInstanceSym inst ++ gS).length from ⟨hz0, hz2⟩)]
    exact (List.getElem_append_left hz1).symm
  constructor
  · intro hacc
    rcases hacc with ⟨π, cfg, h, hmem⟩
    have h100 : cfg.state = 100 := by
      simpa [VerifierSym.acceptStates, VerifierSym.qAccept] using hmem
    have h₁ : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ []) π cfg := by
      simpa [List.append_nil] using h
    have hagree₀₁ : ∀ z, 0 ≤ z → z < (((encodeInstanceSym inst).length : ℕ) : ℤ) →
        (symInitialConfig (encodeInstanceSym inst ++ [])).tape z =
          (symInitialConfig (encodeInstanceSym inst ++ gS)).tape z := by
      intro z hz0 hzN
      simpa [List.append_nil] using hagree₀ z hz0 hzN
    have hb : ∀ (π₀ : List SymStep) (cfg₀ : SymConfig),
        SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ []) π₀ cfg₀ →
        List.IsPrefix π₀ π → π₀ ≠ π →
        0 ≤ cfg₀.headPos ∧ cfg₀.headPos < (((encodeInstanceSym inst).length : ℕ) : ℤ) := by
      intro π₀ cfg₀ h₀ hpfx hne
      exact ⟨a2_sym_head_nonneg inst hm ht [] h₁ h100 π₀ cfg₀ h₀ hpfx,
        a2_accept_path_read_inside inst hm ht [] h₁ h100 π₀ cfg₀ h₀ hpfx hne⟩
    rcases symReachablePath_agree_below (M := VerifierSym.transition) hagree₀₁ h₁ hb with
      ⟨cfg', hpath', hst', _hhd', _hag'⟩
    refine ⟨π, cfg', hpath', ?_⟩
    rw [hst']
    simpa [VerifierSym.acceptStates, VerifierSym.qAccept] using h100
  · intro hacc
    rcases hacc with ⟨π, cfg, h, hmem⟩
    have h100 : cfg.state = 100 := by
      simpa [VerifierSym.acceptStates, VerifierSym.qAccept] using hmem
    have hb : ∀ (π₀ : List SymStep) (cfg₀ : SymConfig),
        SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π₀ cfg₀ →
        List.IsPrefix π₀ π → π₀ ≠ π →
        0 ≤ cfg₀.headPos ∧ cfg₀.headPos < (((encodeInstanceSym inst).length : ℕ) : ℤ) := by
      intro π₀ cfg₀ h₀ hpfx hne
      exact ⟨a2_sym_head_nonneg inst hm ht gS h h100 π₀ cfg₀ h₀ hpfx,
        a2_accept_path_read_inside inst hm ht gS h h100 π₀ cfg₀ h₀ hpfx hne⟩
    rcases symReachablePath_agree_below (M := VerifierSym.transition)
      (input₁ := encodeInstanceSym inst ++ gS) (input₂ := encodeInstanceSym inst)
      (fun z hz0 hzN => (hagree₀ z hz0 hzN).symm) h hb with
      ⟨cfg', hpath', hst', _hhd', _hag'⟩
    refine ⟨π, cfg', hpath', ?_⟩
    rw [hst']
    simpa [VerifierSym.acceptStates, VerifierSym.qAccept] using h100

-- ============================================================
-- 环 3:组装(条款⑤ hrel2)
-- ============================================================

/-- 条款⑤(尾缀无关):CBTM 对 encS 与 encS++gS 接受性一致。
    .1:原 ⟹ 尾缀版(消费 :443);.2:尾缀版 ⟹ 原(消费 :420)。 -/
theorem subsetSumNTM2_hrel2 (inst : SubsetSumInstance) (hne : inst.elements ≠ [])
    (hm : 0 < (encodeElementsSym inst.elements).length) (ht : 0 < inst.target)
    (gS : List Sym) :
    (NTM2.toCBTM subsetSumNTM2).tapeAccepts (encodeInstanceF4 inst) ↔
      (NTM2.toCBTM subsetSumNTM2).tapeAccepts (encodeInstanceF4 inst ++ flat4F4 gS) := by
  have hflat : encodeInstanceF4 inst ++ flat4F4 gS = flat4F4 (encodeInstanceSym inst ++ gS) := by
    simp [encodeInstanceF4, flat4F4, List.flatMap_append]
  rw [toCBTM_subsetSumNTM2_eq]
  constructor
  · intro hacc
    have hsym : symAccepts VerifierSym.transition VerifierSym.acceptStates
        (encodeInstanceSym inst) :=
      (subsetSumCBTM_accepts_iff_symAccepts (encodeInstanceSym inst)).1 hacc
    have hsym2 := (symAccepts_tail_iff inst hm ht gS).1 hsym
    rw [hflat]
    exact (subsetSumCBTM_accepts_iff_symAccepts (encodeInstanceSym inst ++ gS)).2 hsym2
  · intro hacc
    rw [hflat] at hacc
    have hsym2 : symAccepts VerifierSym.transition VerifierSym.acceptStates
        (encodeInstanceSym inst ++ gS) :=
      (subsetSumCBTM_accepts_iff_symAccepts (encodeInstanceSym inst ++ gS)).1 hacc
    have hsym := (symAccepts_tail_iff inst hm ht gS).2 hsym2
    exact (subsetSumCBTM_accepts_iff_symAccepts (encodeInstanceSym inst)).2 hsym

end Mp
