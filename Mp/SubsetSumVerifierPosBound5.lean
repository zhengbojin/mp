-- ============================================================================
-- 模块 5:A-2 成品层(L3″-gS)— W2 线
--   §1 可达态归类(33 态)                    §2 gS 版无101 + 101 排除件
--   §3 Extendable 谓词 + 首步事实 + 前缀供给
--   §4 锚定界(23 态 ≤ L−2;中途 100 态 ≤ L−1)
--   §5 其余 20 态分类(Finset 级 kernel decide)
--   §6 workhorse:逐态界 → head < |encS|
--   §7 成品:#1 a2_accept_path_prefix_inside(L3″-gS;终末位析取 state=100)
--          可延拓封装 a2_extendable_prefix_inside
--          #3 a2_accept_path_read_inside / a2_accept_path_write_inside(读写分列)
--          兼容件 a2_accept_path_prefix_inside_nil(gS=[])
--   口径:接受路径真前缀 head < |encS|(#3);全程 ≤ 显式界(#1)
--   依赖(只读):PosBound4 主循环定理 / Reverse6 q12suffix / Reverse5 分解原语 / Reverse3 no101
-- ============================================================================
import Mp.SubsetSumVerifierPosBound4

/-! # 模块 5:A-2 成品层(L3″-gS + F4 层)— W2 线

【Sym 层（提交① 6c9a34a）】
成品:#1 `a2_accept_path_prefix_inside`(L3″-gS) / 可延拓封装 `a2_extendable_prefix_inside`
/ #3 读写分列 `a2_accept_path_read_inside`·`a2_accept_path_write_inside`(T16 直接消费)
/ 兼容件 `a2_accept_path_prefix_inside_nil`(gS=[])。
口径:接受路径真前缀 head < |encS|;全程显式界;终末位由析取项 state=100 容纳。

【F4 层（提交② 230ee80）】x = encodeInstanceF4 inst ++ flat4F4 gS(恒 4 对齐)。成品:
M1-gS `a2_accept_path_prefix_head_le`(每前缀头 ≤ |x|) / M2-gS `a2_accept_path_prefix_head_nonneg`(≥ 0)
/ #2 `a2_cbtm_accept_path_prefix_bound`(每前缀头 ∈ [0, |x|])
/ 可延拓封装 `a2_cbtm_extendable_path_prefix_bound`(供 Q10-(a) 消费)
/ gS=[] 对照件 `a2_cbtm_accept_path_prefix_bound_nil` + 恒等件 `a2p_flat4F4_nil`。
方法:桥/块机械参数化复用;仅替换两处 enc 专用 Sym 界(r7→#1、ext_path_state100_head_le_enc→
a2_state100_head_le);M2 下界新路 = mainloop #1(任意态 ≥ 0) + 末态「100 自环+主循环」。 -/

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

-- ============================================================
-- §1 33 态归类
-- ============================================================

def a2p_stateSet : Finset ℕ :=
  {0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 24, 26, 27, 28, 29, 38,
   51, 76, 77, 81, 84, 85, 86, 87, 100, 101}

lemma a2p_stateSet_closure (q : Fin 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition ((q : ℕ), s)) :
    r.nextState ∈ a2p_stateSet := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym,
      (VerifierSym.transition ((q : ℕ), s)).image SymTransResult.nextState ⊆ a2p_stateSet := by
    decide
  exact hbb q s (Finset.mem_image.mpr ⟨r, hr, rfl⟩)

lemma a2p_stateSet_cases : ∀ q : Fin 102, (q : ℕ) ∈ a2p_stateSet →
    (q : ℕ) = 0 ∨ (q : ℕ) = 1 ∨ (q : ℕ) = 2 ∨ (q : ℕ) = 3 ∨ (q : ℕ) = 4 ∨
    (q : ℕ) = 5 ∨ (q : ℕ) = 8 ∨ (q : ℕ) = 9 ∨ (q : ℕ) = 10 ∨ (q : ℕ) = 11 ∨
    (q : ℕ) = 12 ∨ (q : ℕ) = 13 ∨ (q : ℕ) = 14 ∨ (q : ℕ) = 20 ∨ (q : ℕ) = 21 ∨
    (q : ℕ) = 22 ∨ (q : ℕ) = 23 ∨ (q : ℕ) = 24 ∨ (q : ℕ) = 26 ∨ (q : ℕ) = 27 ∨
    (q : ℕ) = 28 ∨ (q : ℕ) = 29 ∨ (q : ℕ) = 38 ∨ (q : ℕ) = 51 ∨ (q : ℕ) = 76 ∨
    (q : ℕ) = 77 ∨ (q : ℕ) = 81 ∨ (q : ℕ) = 84 ∨ (q : ℕ) = 85 ∨ (q : ℕ) = 86 ∨
    (q : ℕ) = 87 ∨ (q : ℕ) = 100 ∨ (q : ℕ) = 101 := by
  decide

lemma a2p_reach_state_mem (input : List Sym) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg) :
    cfg.state ∈ a2p_stateSet := by
  have hsteps : SymSteps VerifierSym.transition (symInitialConfig input) π cfg :=
    (symSteps_initial_iff VerifierSym.transition input π cfg).mpr h
  induction hsteps with
  | nil => change (0 : ℕ) ∈ a2p_stateSet; decide
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      have hpath₁ : SymReachablePath VerifierSym.transition input π₀ cfg₁ :=
        (symSteps_initial_iff VerifierSym.transition input π₀ cfg₁).1 hprev
      have hq₁ : cfg₁.state < 102 := q12_path_state_lt102 input π₀ cfg₁ hpath₁
      have hcl := a2p_stateSet_closure ⟨cfg₁.state, hq₁⟩ (cfg₁.tape cfg₁.headPos)
        step.result htrans
      simpa [symStepConfig] using hcl

-- ============================================================
-- §2 无101
-- ============================================================

lemma a2p_no101_of_accept {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg) (hacc : cfg.state = 100) :
    ∀ step ∈ π, step.result.nextState ≠ 101 := by
  have hsteps : SymSteps VerifierSym.transition (symInitialConfig input) π cfg :=
    (symSteps_initial_iff VerifierSym.transition input π cfg).mpr h
  exact symAccepts_no_101 hsteps hacc

lemma a2p_reach_ne_101 {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101) : cfg.state ≠ 101 := by
  intro h101
  have hsteps : SymSteps VerifierSym.transition (symInitialConfig input) π cfg :=
    (symSteps_initial_iff VerifierSym.transition input π cfg).mpr h
  cases hπ : π with
  | nil =>
      rw [hπ] at hsteps
      have he := Mp.SymToF4.symSteps_empty hsteps rfl
      rw [he] at h101
      simp [symInitialConfig] at h101
  | cons s rest =>
      rw [hπ] at hsteps
      have hne : s :: rest ≠ [] := by simp
      rcases Mp.SymToF4.symSteps_split_last hsteps hne with
        ⟨step₂, πs₀, cfg₁, hs, _hprev, _hfrom, _hread, _htrans, hcfg⟩
      have hmem : step₂ ∈ s :: rest := by
        rw [hs]
        exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
      have hthis := hno101 step₂ (by rw [hπ]; exact hmem)
      apply hthis
      rw [hcfg] at h101
      exact h101

-- ============================================================
-- §3 Extendable + 首步事实 + 前缀供给
-- ============================================================

def a2p_Extendable (input : List Sym) (π : List SymStep) (cfg : SymConfig) : Prop :=
  ∃ step : SymStep, ∃ π₃ : List SymStep, ∃ cfg₃ : SymConfig,
    step.fromState = cfg.state ∧ step.readSym = cfg.tape cfg.headPos ∧
    step.result ∈ VerifierSym.transition (cfg.state, cfg.tape cfg.headPos) ∧
    SymReachablePath VerifierSym.transition input (π ++ step :: π₃) cfg₃ ∧
    cfg₃.state = 100

lemma a2p_extendable_cons {input : List Sym} {π₀ : List SymStep} {step : SymStep}
    {cfg cfg' : SymConfig}
    (hfrom : step.fromState = cfg.state) (hread : step.readSym = cfg.tape cfg.headPos)
    (htrans : step.result ∈ VerifierSym.transition (cfg.state, cfg.tape cfg.headPos))
    (hext' : a2p_Extendable input (π₀ ++ [step]) cfg') :
    a2p_Extendable input π₀ cfg := by
  rcases hext' with ⟨step₂, π₃, cfg₃, _hfrom₂, _hread₂, _hmem₂, hpath₂, hacc₂⟩
  refine ⟨step, step₂ :: π₃, cfg₃, hfrom, hread, htrans, ?_, hacc₂⟩
  simpa [List.append_assoc, List.singleton_append] using hpath₂

lemma a2p_hno101_restrict {π₀ : List SymStep} {step : SymStep}
    (hno101 : ∀ s ∈ π₀ ++ [step], s.result.nextState ≠ 101) :
    ∀ s ∈ π₀, s.result.nextState ≠ 101 :=
  fun s hs => hno101 s (List.mem_append.mpr (Or.inl hs))

lemma a2p_symSteps_first_facts {M : ℕ × Sym → Finset SymTransResult} (step : SymStep)
    (cfg₀ : SymConfig) :
    ∀ (L : List SymStep) {cfg : SymConfig}, (∃ rest, L = step :: rest) →
      SymSteps M cfg₀ L cfg →
      step.fromState = cfg₀.state ∧ step.readSym = cfg₀.tape cfg₀.headPos ∧
        step.result ∈ M (cfg₀.state, cfg₀.tape cfg₀.headPos) := by
  have main : ∀ (n : ℕ) (L : List SymStep) {cfg : SymConfig}, L.length = n →
      (∃ rest, L = step :: rest) → SymSteps M cfg₀ L cfg →
      step.fromState = cfg₀.state ∧ step.readSym = cfg₀.tape cfg₀.headPos ∧
        step.result ∈ M (cfg₀.state, cfg₀.tape cfg₀.headPos) := by
    intro n
    induction n with
    | zero =>
        intro L cfg hlen hshape _h
        rcases hshape with ⟨rest, rfl⟩
        simp at hlen
    | succ n ih =>
        intro L cfg hlen hshape h
        rcases hshape with ⟨rest, rfl⟩
        cases rest with
        | nil =>
            have hne : step :: [] ≠ [] := by simp
            rcases Mp.SymToF4.symSteps_split_last h hne with
              ⟨step₂, πs₀, cfg₁, hs, hprev, hfrom, hread, htrans, _hcfg⟩
            cases πs₀ with
            | nil =>
                simp only [List.nil_append] at hs
                have h1 : step = step₂ := (List.cons.inj hs).1
                have he : cfg₁ = cfg₀ := Mp.SymToF4.symSteps_empty hprev rfl
                rw [← h1] at hfrom hread htrans
                rw [he] at hfrom hread htrans
                exact ⟨hfrom, hread, htrans⟩
            | cons x πs₀' =>
                simp at hs
        | cons r rest' =>
            have hne : step :: r :: rest' ≠ [] := by simp
            rcases Mp.SymToF4.symSteps_split_last h hne with
              ⟨step₂, πs₀, cfg₁, hs, hprev, _hfrom, _hread, _htrans, _hcfg⟩
            cases πs₀ with
            | nil => simp at hs
            | cons x πs₀' =>
                simp only [List.cons_append] at hs
                have hx : x = step := (List.cons.inj hs).1.symm
                have htail : πs₀' ++ [step₂] = r :: rest' := (List.cons.inj hs).2.symm
                subst x
                have hlen' : (step :: πs₀').length = n := by
                  have h2 := congrArg List.length htail
                  simp only [List.length_append, List.length_cons, List.length_nil] at h2 hlen
                  simp only [List.length_cons]
                  omega
                exact ih (step :: πs₀') hlen' ⟨πs₀', rfl⟩ hprev
  intro L cfg hshape h
  exact main L.length L rfl hshape h

lemma a2p_prefix_supply (inst : SubsetSumInstance)
    (gS : List Sym) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π cfg)
    {π₀ : List SymStep} {cfg₀ : SymConfig}
    (h₀ : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π₀ cfg₀)
    (hpfx : List.IsPrefix π₀ π) (hne : π₀ ≠ π) (hacc : cfg.state = 100)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101) :
    a2p_Extendable (encodeInstanceSym inst ++ gS) π₀ cfg₀ ∧
      (∀ step ∈ π₀, step.result.nextState ≠ 101) := by
  rcases hpfx with ⟨πrest, hπ⟩
  have hrest : πrest ≠ [] := by
    intro he
    apply hne
    rw [he, List.append_nil] at hπ
    exact hπ
  cases πrest with
  | nil => exact absurd rfl hrest
  | cons step rest =>
      have h' : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS)
          (π₀ ++ step :: rest) cfg := by
        simpa [hπ] using h
      have hsteps : SymSteps VerifierSym.transition
          (symInitialConfig (encodeInstanceSym inst ++ gS))
          (π₀ ++ step :: rest) cfg :=
        (symSteps_initial_iff VerifierSym.transition (encodeInstanceSym inst ++ gS)
          (π₀ ++ step :: rest) cfg).mpr h'
      have hsteps₀ : SymSteps VerifierSym.transition
          (symInitialConfig (encodeInstanceSym inst ++ gS))
          π₀ cfg₀ :=
        (symSteps_initial_iff VerifierSym.transition (encodeInstanceSym inst ++ gS)
          π₀ cfg₀).mpr h₀
      rcases symSteps_append_decomp π₀ (step :: rest) hsteps with ⟨cfg₁, hseg₁, hseg₂⟩
      have heq : cfg₁ = cfg₀ := Mp.SymToF4.symSteps_end_unique hseg₁ hsteps₀
      subst cfg₁
      have hfacts := a2p_symSteps_first_facts step cfg₀ (step :: rest) ⟨rest, rfl⟩ hseg₂
      rcases hfacts with ⟨hf1, hf2, hf3⟩
      have hno101' : ∀ s ∈ π₀ ++ step :: rest, s.result.nextState ≠ 101 := by
        intro s hs
        exact hno101 s (by simpa [hπ] using hs)
      refine ⟨⟨step, rest, cfg, hf1, hf2, hf3, h', hacc⟩, ?_⟩
      intro s hs
      exact hno101' s (List.mem_append.mpr (Or.inl hs))

-- ============================================================
-- §4 锚定界：23 ≤ L−2；100（中途）≤ L−1
-- ============================================================

lemma a2_state23_head_le (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length) (ht : 0 < inst.target)
    (gS : List Sym) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π cfg)
    (hext : a2p_Extendable (encodeInstanceSym inst ++ gS) π cfg)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101)
    (h23 : cfg.state = 23) :
    cfg.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 2 := by
  revert hext hno101 h23
  induction h with
  | nil =>
      intro _ _ h23
      exact absurd h23 (by simp [symInitialConfig])
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro hext hno101 h23
      have hq₁ : cfg₁.state < 102 :=
        q12_path_state_lt102 (encodeInstanceSym inst ++ gS) π₀ cfg₁ hprev
      have hnext : step.result.nextState = 23 := by simpa [symStepConfig] using h23
      have hinto := q12suffix_into_23 cfg₁.state hq₁ step.readSym step.result
        (by simpa [hread] using htrans) hnext
      have hext₀ : a2p_Extendable (encodeInstanceSym inst ++ gS) π₀ cfg₁ :=
        a2p_extendable_cons hfrom hread htrans hext
      have hno101₀ : ∀ s ∈ π₀, s.result.nextState ≠ 101 := a2p_hno101_restrict hno101
      rcases hinto with ⟨hcase, hL⟩
      rcases hcase with h22src | h23src
      · rcases h22src with ⟨hq22, _⟩
        have hml := a2p_mainloop_no_neg inst hm ht gS hprev hext₀ hno101₀
        rcases hml with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          h22eq, _⟩
        have hhead : cfg₁.headPos = (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 :=
          h22eq hq22
        dsimp [symStepConfig]
        rw [hhead, hL]
        have : (Dir.L).toInt = -1 := by simp [Dir.toInt]
        rw [this]
        omega
      · rcases h23src with ⟨hq23, _⟩
        have hih : cfg₁.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 2 :=
          ih hext₀ hno101₀ hq23
        dsimp [symStepConfig]
        rw [hL]
        have : (Dir.L).toInt = -1 := by simp [Dir.toInt]
        rw [this]
        omega

lemma a2_state100_head_le (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length) (ht : 0 < inst.target)
    (gS : List Sym) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π cfg)
    (hext : a2p_Extendable (encodeInstanceSym inst ++ gS) π cfg)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101)
    (h100 : cfg.state = 100) :
    cfg.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 := by
  revert hext hno101 h100
  induction h with
  | nil =>
      intro _ _ h100
      exact absurd h100 (by simp [symInitialConfig])
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro hext hno101 h100
      have hq₁ : cfg₁.state < 102 :=
        q12_path_state_lt102 (encodeInstanceSym inst ++ gS) π₀ cfg₁ hprev
      have hnext : step.result.nextState = 100 := by simpa [symStepConfig] using h100
      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
          r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 100 →
          ((q : ℕ) = 23 ∧ s.1 = SymKind.boundary ∧ r.moveDir = Dir.R) ∨
            ((q : ℕ) = 100 ∧ r.moveDir = Dir.S) := by
        decide
      have hcls := hbb ⟨cfg₁.state, hq₁⟩ step.readSym step.result
        (by simpa [hread] using htrans) hnext
      have hext₀ : a2p_Extendable (encodeInstanceSym inst ++ gS) π₀ cfg₁ :=
        a2p_extendable_cons hfrom hread htrans hext
      have hno101₀ : ∀ s ∈ π₀, s.result.nextState ≠ 101 := a2p_hno101_restrict hno101
      rcases hcls with h23src | h100self
      · rcases h23src with ⟨hq23, _hb, hdR⟩
        have h23le : cfg₁.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 2 :=
          a2_state23_head_le inst hm ht gS hprev hext₀ hno101₀ hq23
        dsimp [symStepConfig]
        rw [hdR]
        have : (Dir.R).toInt = 1 := by simp [Dir.toInt]
        rw [this]
        omega
      · rcases h100self with ⟨hq100, hdS⟩
        have hih : cfg₁.headPos ≤ (((encodeInstanceSym inst).length : ℕ) : ℤ) - 1 :=
          ih hext₀ hno101₀ hq100
        dsimp [symStepConfig]
        rw [hdS]
        have : (Dir.S).toInt = 0 := by simp [Dir.toInt]
        rw [this]
        omega

-- ============================================================
-- §5 其余 20 态分类
-- ============================================================

lemma a2p_state_remain_cases : ∀ q : Fin 102, (q : ℕ) ∈ a2p_stateSet →
    (q : ℕ) ∉ a2p_fmtSet → (q : ℕ) ≠ 100 → (q : ℕ) ≠ 101 → (q : ℕ) ≠ 23 →
    (q : ℕ) = 4 ∨ (q : ℕ) = 5 ∨ (q : ℕ) = 8 ∨ (q : ℕ) = 9 ∨ (q : ℕ) = 10 ∨
    (q : ℕ) = 11 ∨ (q : ℕ) = 12 ∨ (q : ℕ) = 13 ∨ (q : ℕ) = 14 ∨ (q : ℕ) = 20 ∨
    (q : ℕ) = 21 ∨ (q : ℕ) = 22 ∨ (q : ℕ) = 51 ∨ (q : ℕ) = 76 ∨ (q : ℕ) = 77 ∨
    (q : ℕ) = 81 ∨ (q : ℕ) = 84 ∨ (q : ℕ) = 85 ∨ (q : ℕ) = 86 ∨ (q : ℕ) = 87 := by
  decide

-- ============================================================
-- §6 workhorse：逐态界 → head < |encS|
-- ============================================================

lemma a2_prefix_head_lt (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length) (ht : 0 < inst.target)
    (gS : List Sym) {π₀ : List SymStep} {cfg₀ : SymConfig}
    (h₀ : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π₀ cfg₀)
    (hext₀ : a2p_Extendable (encodeInstanceSym inst ++ gS) π₀ cfg₀)
    (hno101₀ : ∀ step ∈ π₀, step.result.nextState ≠ 101) :
    cfg₀.headPos < (((encodeInstanceSym inst).length : ℕ) : ℤ) := by
  have hmem : cfg₀.state ∈ a2p_stateSet :=
    a2p_reach_state_mem (encodeInstanceSym inst ++ gS) h₀
  have hq₀ : cfg₀.state < 102 :=
    q12_path_state_lt102 (encodeInstanceSym inst ++ gS) π₀ cfg₀ h₀
  by_cases hfmt : cfg₀.state ∈ a2p_fmtSet
  · exact (a2p_fmt_head_domain inst hm ht gS h₀ hno101₀ hfmt).2
  · by_cases h100 : cfg₀.state = 100
    · have hb := a2_state100_head_le inst hm ht gS h₀ hext₀ hno101₀ h100
      omega
    · by_cases h101 : cfg₀.state = 101
      · exact absurd h101 (a2p_reach_ne_101 h₀ hno101₀)
      · by_cases h23 : cfg₀.state = 23
        · have hb := a2_state23_head_le inst hm ht gS h₀ hext₀ hno101₀ h23
          omega
        · have hrem := a2p_state_remain_cases ⟨cfg₀.state, hq₀⟩ hmem hfmt h100 h101 h23
          have hml := a2p_mainloop_no_neg inst hm ht gS h₀ hext₀ hno101₀
          rcases hml with ⟨_, h4lo, h5lo, h768lo, h13lo, h84lo, h20b, h86lo, h87lo,
            h21b, h51b, h5up, h13up, _, _, _, hdisj, _, h22eq, _⟩
          rcases hdisj with hh | hE
          · rcases hh with h21d | h51d | h22d | h23d | h100d | h101d
            · have := (h21b h21d).2; omega
            · have := (h51b h51d).2; omega
            · have := h22eq h22d; omega
            · exact absurd h23d h23
            · exact absurd h100d h100
            · exact absurd h101d h101
          · obtain ⟨s, _, hs2, _, _, _, _, hE7, hE8, hE4, _, hE1112, hE14, hE81, _,
                _, hE7684, _⟩ := hE
            rcases hrem with h4 | h5 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h20 |
              h21 | h22 | h51 | h76 | h77 | h81 | h84 | h85 | h86 | h87
            · have hc : cfg₀.state = 4 := h4
              have := hE4 hc; omega
            · have hc : cfg₀.state = 5 := h5
              have := h5up hc; omega
            · have hc : cfg₀.state = 8 := h8
              have := hE7684 (Or.inr (Or.inl hc)); omega
            · have hc : cfg₀.state = 9 := h9
              have := hE7 (Or.inr (Or.inr (Or.inl hc))); omega
            · have hc : cfg₀.state = 10 := h10
              have := hE1112 (Or.inl hc); omega
            · have hc : cfg₀.state = 11 := h11
              have := hE1112 (Or.inr (Or.inl hc)); omega
            · have hc : cfg₀.state = 12 := h12
              have := hE1112 (Or.inr (Or.inr hc)); omega
            · have hc : cfg₀.state = 13 := h13
              have := h13up hc; omega
            · have hc : cfg₀.state = 14 := h14
              have := hE14 hc; omega
            · have hc : cfg₀.state = 20 := h20
              have := (h20b hc).2; omega
            · have hc : cfg₀.state = 21 := h21
              have := (h21b hc).2; omega
            · have hc : cfg₀.state = 22 := h22
              have := h22eq hc; omega
            · have hc : cfg₀.state = 51 := h51
              have := (h51b hc).2; omega
            · have hc : cfg₀.state = 76 := h76
              have := hE7684 (Or.inl hc); omega
            · have hc : cfg₀.state = 77 := h77
              have := hE7 (Or.inr (Or.inl hc)); omega
            · have hc : cfg₀.state = 81 := h81
              have := hE81 hc; omega
            · have hc : cfg₀.state = 84 := h84
              have := hE7684 (Or.inr (Or.inr (Or.inl hc))); omega
            · have hc : cfg₀.state = 85 := h85
              have := hE7 (Or.inl hc); omega
            · have hc : cfg₀.state = 86 := h86
              have := hE8 (Or.inl hc); omega
            · have hc : cfg₀.state = 87 := h87
              have := hE8 (Or.inr (Or.inl hc)); omega

-- ============================================================
-- §7 成品
-- ============================================================

/-- #1（L3″-gS）：接受路径任意前缀：state = 100 ∨ 头 < |wS|。 -/
theorem a2_accept_path_prefix_inside (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length) (ht : 0 < inst.target)
    (gS : List Sym) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π cfg)
    (hacc : cfg.state = 100) :
    ∀ (π₀ : List SymStep) (cfg₀ : SymConfig),
      SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π₀ cfg₀ →
      List.IsPrefix π₀ π →
      cfg₀.state = 100 ∨
        cfg₀.headPos < (((encodeInstanceSym inst ++ gS).length : ℕ) : ℤ) := by
  intro π₀ cfg₀ h₀ hpfx
  by_cases hterm : π₀ = π
  · left
    have hsteps : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst ++ gS))
        π cfg₀ := by
      rw [← hterm]
      exact (symSteps_initial_iff VerifierSym.transition (encodeInstanceSym inst ++ gS)
        π₀ cfg₀).mpr h₀
    have hsteps2 : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst ++ gS))
        π cfg :=
      (symSteps_initial_iff VerifierSym.transition (encodeInstanceSym inst ++ gS) π cfg).mpr h
    have he : cfg₀ = cfg := Mp.SymToF4.symSteps_end_unique hsteps hsteps2
    rw [he]
    exact hacc
  · right
    have hno101 := a2p_no101_of_accept h hacc
    obtain ⟨hext₀, hno101₀⟩ := a2p_prefix_supply inst gS h h₀ hpfx hterm hacc hno101
    have hlt := a2_prefix_head_lt inst hm ht gS h₀ hext₀ hno101₀
    have hLe : (((encodeInstanceSym inst).length : ℕ) : ℤ) ≤
        (((encodeInstanceSym inst ++ gS).length : ℕ) : ℤ) := by
      rw [List.length_append]
      push_cast
      omega
    omega

/-- #1 可延拓封装（非接受路径版）：可续行到 100 ⇒ 前缀全界。 -/
theorem a2_extendable_prefix_inside (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length) (ht : 0 < inst.target)
    (gS : List Sym) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π cfg)
    (hext : ∃ π₂ : List SymStep, ∃ cfg₂ : SymConfig,
      SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) (π ++ π₂) cfg₂ ∧
        cfg₂.state = 100) :
    ∀ (π₀ : List SymStep) (cfg₀ : SymConfig),
      SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π₀ cfg₀ →
      List.IsPrefix π₀ π →
      cfg₀.state = 100 ∨
        cfg₀.headPos < (((encodeInstanceSym inst ++ gS).length : ℕ) : ℤ) := by
  obtain ⟨π₂, cfg₂, h₂, hacc₂⟩ := hext
  have hmain := a2_accept_path_prefix_inside inst hm ht gS h₂ hacc₂
  intro π₀ cfg₀ h₀ hpfx
  have hpfx₂ : List.IsPrefix π₀ (π ++ π₂) :=
    hpfx.trans ⟨π₂, rfl⟩
  exact hmain π₀ cfg₀ h₀ hpfx₂

/-- #3 读位分列：接受路径真前缀的步前头（= 读位置）< |encS|。 -/
theorem a2_accept_path_read_inside (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length) (ht : 0 < inst.target)
    (gS : List Sym) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π cfg)
    (hacc : cfg.state = 100) :
    ∀ (π₀ : List SymStep) (cfg₀ : SymConfig),
      SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π₀ cfg₀ →
      List.IsPrefix π₀ π → π₀ ≠ π →
      cfg₀.headPos < (((encodeInstanceSym inst).length : ℕ) : ℤ) := by
  intro π₀ cfg₀ h₀ hpfx hne
  have hno101 := a2p_no101_of_accept h hacc
  obtain ⟨hext₀, hno101₀⟩ := a2p_prefix_supply inst gS h h₀ hpfx hne hacc hno101
  exact a2_prefix_head_lt inst hm ht gS h₀ hext₀ hno101₀

/-- #3 写位分列：就地写语义下写位置 = 步前头，故与读位同界。 -/
theorem a2_accept_path_write_inside (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length) (ht : 0 < inst.target)
    (gS : List Sym) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π cfg)
    (hacc : cfg.state = 100) :
    ∀ (π₀ : List SymStep) (cfg₀ : SymConfig),
      SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π₀ cfg₀ →
      List.IsPrefix π₀ π → π₀ ≠ π →
      cfg₀.headPos < (((encodeInstanceSym inst).length : ℕ) : ℤ) := by
  intro π₀ cfg₀ h₀ hpfx hne
  exact a2_accept_path_read_inside inst hm ht gS h hacc π₀ cfg₀ h₀ hpfx hne

/-- #1 与 A-1 enc 版形状兼容（gS = [] 特化）。 -/
theorem a2_accept_path_prefix_inside_nil (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length) (ht : 0 < inst.target)
    {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ []) π cfg)
    (hacc : cfg.state = 100) :
    ∀ (π₀ : List SymStep) (cfg₀ : SymConfig),
      SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ []) π₀ cfg₀ →
      List.IsPrefix π₀ π →
      cfg₀.state = 100 ∨
        cfg₀.headPos < (((encodeInstanceSym inst).length : ℕ) : ℤ) := by
  intro π₀ cfg₀ h₀ hpfx
  have hres := a2_accept_path_prefix_inside inst hm ht [] h hacc π₀ cfg₀ h₀ hpfx
  rcases hres with h100 | hlt
  · exact Or.inl h100
  · right
    simpa using hlt


-- ============================================================================
-- S3（W2 线）：F4 层成品 —— x = encodeInstanceF4 inst ++ flat4F4 gS
--   M1-gS 每前缀头 ≤ |x|；M2-gS 每前缀头 ≥ 0；
--   #2 a2_cbtm_accept_path_prefix_bound + 可延拓封装 + gS=[] 对照件。
-- ============================================================================

open SymToF4

set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

-- ============================================================
-- 组合件：TapeSteps 拼接
-- ============================================================

lemma a2_tapeSteps_comp {M : CBTM} {input : List F4} {cfg₀ cfg₁ cfg₂ : CBTMConfig M input}
    {π₁ π₂ : ComputationPath}
    (h₁ : TapeSteps M input cfg₀ π₁ cfg₁) (h₂ : TapeSteps M input cfg₁ π₂ cfg₂) :
    TapeSteps M input cfg₀ (π₁ ++ π₂) cfg₂ := by
  induction h₂ with
  | nil => simpa using h₁
  | cons π step cfg' hprev hfrom hread htrans ih =>
      rw [← List.append_assoc]
      exact TapeSteps.cons (π₁ ++ π) step cfg' ih hfrom hread htrans

-- ============================================================
-- Sym 层下界链（探针 5 件，随 PosBound5 提交）
-- ============================================================

lemma a2_state100_head_ge0 (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length) (ht : 0 < inst.target)
    (gS : List Sym) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π cfg)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101)
    (h100 : cfg.state = 100) :
    (0 : ℤ) ≤ cfg.headPos := by
  let r : SymTransResult := { nextState := 100, writeSym := cfg.tape cfg.headPos, moveDir := Dir.S }
  have hmem : r ∈ VerifierSym.transition (100, cfg.tape cfg.headPos) := by
    have hb : ∀ s : Sym,
        ({ nextState := 100, writeSym := s, moveDir := Dir.S } : SymTransResult) ∈
          VerifierSym.transition (100, s) := by decide
    simpa [r] using hb (cfg.tape cfg.headPos)
  let step : SymStep := { fromState := 100, readSym := cfg.tape cfg.headPos, result := r }
  have hfrom : step.fromState = cfg.state := by dsimp [step]; rw [h100]
  have hread : step.readSym = cfg.tape cfg.headPos := rfl
  have htrans : step.result ∈ VerifierSym.transition (cfg.state, cfg.tape cfg.headPos) := by
    dsimp [step]; rw [h100]; exact hmem
  have hpath : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS)
      (π ++ step :: []) (symStepConfig cfg step.result) :=
    SymReachablePath.cons π step cfg h hfrom hread htrans
  have hacc' : (symStepConfig cfg step.result).state = 100 := rfl
  exact (a2p_mainloop_no_neg inst hm ht gS h
    ⟨step, [], symStepConfig cfg step.result, hfrom, hread, htrans, hpath, hacc'⟩ hno101).1

lemma a2_sym_head_nonneg (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length) (ht : 0 < inst.target)
    (gS : List Sym) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π cfg)
    (hacc : cfg.state = 100) :
    ∀ (π₀ : List SymStep) (cfg₀ : SymConfig),
      SymReachablePath VerifierSym.transition (encodeInstanceSym inst ++ gS) π₀ cfg₀ →
      List.IsPrefix π₀ π → (0 : ℤ) ≤ cfg₀.headPos := by
  intro π₀ cfg₀ h₀ hpfx
  have hno101 := a2p_no101_of_accept h hacc
  by_cases hterm : π₀ = π
  · have hsteps : SymSteps VerifierSym.transition
        (symInitialConfig (encodeInstanceSym inst ++ gS)) π cfg₀ := by
      rw [← hterm]
      exact (symSteps_initial_iff VerifierSym.transition (encodeInstanceSym inst ++ gS)
        π₀ cfg₀).mpr h₀
    have hsteps2 : SymSteps VerifierSym.transition
        (symInitialConfig (encodeInstanceSym inst ++ gS)) π cfg :=
      (symSteps_initial_iff VerifierSym.transition (encodeInstanceSym inst ++ gS) π cfg).mpr h
    have he : cfg₀ = cfg := Mp.SymToF4.symSteps_end_unique hsteps hsteps2
    rw [he]
    exact a2_state100_head_ge0 inst hm ht gS h hno101 hacc
  · obtain ⟨hext₀, hno101₀⟩ := a2p_prefix_supply inst gS h h₀ hpfx hterm hacc hno101
    exact (a2p_mainloop_no_neg inst hm ht gS h₀ hext₀ hno101₀).1

-- ============================================================
-- M1-gS：每前缀头 ≤ |x|
-- ============================================================

lemma a2_accept_path_prefix_head_le (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length) (ht : 0 < inst.target)
    (gS : List Sym) :
    ∀ {π : ComputationPath} {cfg : CBTMConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)},
      TapeSteps subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)
        (initialConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)) π cfg →
      cfg.state ∈ acceptStates4 →
      ∀ π₀ cfg₀,
        TapeSteps subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)
          (initialConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)) π₀ cfg₀ →
        List.IsPrefix π₀ π →
        cfg₀.headPos ≤ ((encodeInstanceF4 inst ++ flat4F4 gS).length : ℤ) := by
  let wS := encodeInstanceSym inst ++ gS
  have hx : encodeInstanceF4 inst ++ flat4F4 gS = flat4F4 wS := by
    simp [wS, encodeInstanceF4, flat4F4, List.flatMap_append]
  intro π cfg h hacc π₀ cfg₀ h₀ hp
  have htrap : ∀ k (hk : k < π.length),
      (decodeState (π.get ⟨k, hk⟩).result.nextState).1 ≠ 101 := accept_path_no_trap h hacc
  have hcorr0 : blockCorrespond (initialConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS))
      (symInitialConfig wS) := by
    rw [hx]
    exact initialBlockCorrespond wS
  have hq0 : (symInitialConfig wS).state ≤ 101 := by
    dsimp [symInitialConfig, SymConfig.mk, VerifierSym.qStart]
    norm_num
  have hbp : GoodBlockPath (encodeInstanceF4 inst ++ flat4F4 gS)
      (initialConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)) π cfg :=
    accept_path_is_good_block_path h hacc htrap hcorr0 hq0
  have hbridge := good_block_path_head_corresp (encodeInstanceF4 inst ++ flat4F4 gS) wS
    (initialConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)) (symInitialConfig wS)
    π cfg hcorr0 hbp htrap
  rcases hbridge with ⟨πs, cfgs', hsSym, hcorr', hlen12, hhead⟩
  have hreach : SymReachablePath VerifierSym.transition wS πs cfgs' :=
    (symSteps_initial_iff VerifierSym.transition wS πs cfgs').1 hsSym
  have haccS : cfgs'.state = VerifierSym.qAccept := by
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
  have hendSym : cfgs'.headPos ≤ (wS.length : ℤ) :=
    q12_weak wS πs cfgs' hreach haccS
  by_cases hfull : π₀ = π
  · subst π₀
    have hdet : cfg₀ = cfg := (tapeSteps_det π h h₀).symm
    subst cfg₀
    rw [hcorr'.2.1]
    have hlenx : (encodeInstanceF4 inst ++ flat4F4 gS).length = 4 * wS.length := by
      rw [hx]
      simp [flat4F4_length]
    rw [hlenx]
    have h4 : (0 : ℤ) ≤ 4 := by norm_num
    exact mul_le_mul_of_nonneg_left hendSym h4
  · let n₀ := π₀.length
    let k := n₀ / 12
    have htake₀ : π₀ = π.take n₀ := by simpa [n₀] using (prefix_eq_take hp)
    have hn₀_le : n₀ ≤ π.length := by
      dsimp [n₀]
      rw [htake₀]
      simp [List.length_take]
    have hn₀_lt : n₀ < π.length := by
      by_contra hge
      have htake_all : π.take n₀ = π := by
        exact (List.take_eq_self_iff π).2 (Nat.le_of_not_gt hge)
      apply hfull
      rw [htake₀, htake_all]
    have hlen12' : π.length = 12 * πs.length := by
      rw [← hlen12]
      simp [Nat.mul_comm]
    have hn₀_lt12 : n₀ < 12 * πs.length := by
      rw [← hlen12']
      exact hn₀_lt
    have hk_lt : k < πs.length := by
      have hd := (Nat.div_lt_iff_lt_mul (k := 12) (y := πs.length) (by norm_num : 0 < 12)).2 (by
        simpa [Nat.mul_comm] using hn₀_lt12)
      simpa [k] using hd
    have hk1 : k + 1 ≤ πs.length := by omega
    rcases hhead k (by omega) with ⟨cfgsm, cfgcm, hSym_k, hTap_k, hpk, hstk⟩
    rcases hhead (k + 1) hk1 with ⟨cfgsm1, cfgcm1, hSym_k1, hTap_k1, hpk1, hstk1⟩
    have hreach_k : SymReachablePath VerifierSym.transition wS (πs.take k) cfgsm :=
      (symSteps_initial_iff VerifierSym.transition wS (πs.take k) cfgsm).1 hSym_k
    have hp_le : cfgsm.headPos ≤ ((wS.length : ℕ) - 1 : ℤ) := by
      have hr7 := a2_accept_path_prefix_inside inst hm ht gS hreach haccS (πs.take k) cfgsm hreach_k
        (by
          refine ⟨πs.drop k, ?_⟩
          simp [List.take_append_drop])
      rcases hr7 with h100 | hlt
      · have hne_take : πs.take k ≠ πs := by
          intro he
          have hlen := congrArg List.length he
          rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk_lt)] at hlen
          omega
        have hno101πs : ∀ step ∈ πs, step.result.nextState ≠ 101 :=
          a2p_no101_of_accept hreach haccS
        obtain ⟨hextm, hno101m⟩ := a2p_prefix_supply inst gS hreach hreach_k
          (by
            refine ⟨πs.drop k, ?_⟩
            simp [List.take_append_drop])
          hne_take haccS hno101πs
        have hle := a2_state100_head_le inst hm ht gS hreach_k hextm hno101m h100
        have hLle : (((encodeInstanceSym inst).length : ℕ) : ℤ) ≤ (wS.length : ℤ) := by
          dsimp [wS]
          rw [List.length_append]
          push_cast
          omega
        have hw : 1 ≤ wS.length := by
          have hLpos : 0 < (encodeInstanceSym inst).length := by
            rw [r7_enc_len]
            omega
          have hle' : 1 ≤ (encodeInstanceSym inst).length := by omega
          dsimp [wS]
          rw [List.length_append]
          omega
        have hcast : ((wS.length : ℕ) - 1 : ℤ) = (wS.length : ℤ) - 1 := by
          simpa using (Int.ofNat_sub (m := 1) (n := wS.length) hw)
        rw [hcast]
        omega
      · have hltw : cfgsm.headPos < (wS.length : ℤ) := hlt
        have hw : 1 ≤ wS.length := by
          have hLpos : 0 < (encodeInstanceSym inst).length := by
            rw [r7_enc_len]
            omega
          have hle' : 1 ≤ (encodeInstanceSym inst).length := by omega
          dsimp [wS]
          rw [List.length_append]
          omega
        have hcast : ((wS.length : ℕ) - 1 : ℤ) = (wS.length : ℤ) - 1 := by
          simpa using (Int.ofNat_sub (m := 1) (n := wS.length) hw)
        rw [hcast]
        omega
    have h12k_le : 12 * k ≤ n₀ := by
      have hd := Nat.div_mul_le_self n₀ 12
      simpa [k, Nat.mul_comm] using hd
    have htake_eq : π₀.take (12 * k) = π.take (12 * k) := by
      rw [htake₀, List.take_take]
      rw [Nat.min_eq_left h12k_le]
    have hdec₀ := tapeSteps_append_decomp (π₁ := π₀.take (12 * k))
      (π₂ := π₀.drop (12 * k))
      (by simpa [List.take_append_drop] using h₀)
    rcases hdec₀ with ⟨cfg₁, h₁, h₂⟩
    have hdet₁ : cfg₁ = cfgcm := by
      exact tapeSteps_det (π.take (12 * k)) (by simpa [htake_eq] using h₁) hTap_k
    have h₂' : TapeSteps subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS) cfgcm
        (π₀.drop (12 * k)) cfg₀ := by
      simpa [hdet₁] using h₂
    have htt : (π.take (12 * (k + 1))).take (12 * k) = π.take (12 * k) := by
      rw [List.take_take]
      rw [Nat.min_eq_left (by omega : 12 * k ≤ 12 * (k + 1))]
    have hdec₁ := tapeSteps_append_decomp (π₁ := π.take (12 * k))
      (π₂ := (π.take (12 * (k + 1))).drop (12 * k))
      (by
        rw [← htt]
        simpa [List.take_append_drop] using hTap_k1)
    rcases hdec₁ with ⟨cfg₂, h₂a, h₂b⟩
    have hdet₂ : cfg₂ = cfgcm := tapeSteps_det (π.take (12 * k)) h₂a hTap_k
    have hb12 : TapeSteps subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS) cfgcm
        ((π.take (12 * (k + 1))).drop (12 * k)) cfgcm1 := by
      rw [← hdet₂]
      exact h₂b
    have hblen : ((π.take (12 * (k + 1))).drop (12 * k)).length = 12 := by
      have hle : 12 * (k + 1) ≤ π.length := by
        have hle' : 12 * (k + 1) ≤ 12 * πs.length := Nat.mul_le_mul_left 12 hk1
        simpa [hlen12', Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hle'
      exact block_drop_length hle
    have htr12 : ∀ m (hm : m < ((π.take (12 * (k + 1))).drop (12 * k)).length),
        (decodeState (((π.take (12 * (k + 1))).drop (12 * k)).get ⟨m, hm⟩).result.nextState).1 ≠ 101 := by
      intro m hm
      have hmem : ∀ step ∈ (π.take (12 * (k + 1))).drop (12 * k),
          (decodeState step.result.nextState).1 ≠ 101 := by
        intro step hs
        exact (trap_mem_of_get htrap) step (block_step_mem (π := π) (k := k) step hs)
      exact trap_get_of_mem hmem m hm
    have hblk := block12_prefix_pos_inside (p := cfgsm.headPos) hb12 hblen hstk hpk htr12
    have hmidlen : (π₀.drop (12 * k)).length ≤ 12 := by
      rw [List.length_drop]
      have hjk : 12 * k + n₀ % 12 = n₀ := by
        simpa [k, Nat.mul_comm] using (Nat.div_add_mod n₀ 12)
      have hnmod : n₀ % 12 < 12 := Nat.mod_lt n₀ (by norm_num)
      omega
    rcases hblk (π₀.drop (12 * k)).length hmidlen with ⟨cfgj, hpfxj, hIcc⟩
    have hmid_eq : π₀.drop (12 * k) =
        ((π.take (12 * (k + 1))).drop (12 * k)).take (π₀.drop (12 * k)).length := by
      rw [htake₀]
      have hlen' : ((π.take n₀).drop (12 * k)).length = n₀ - 12 * k := by
        rw [List.length_drop, List.length_take]
        rw [Nat.min_eq_left hn₀_le]
      rw [hlen']
      have hA : 12 * (k + 1) - 12 * k = 12 := by omega
      have hx' : n₀ - 12 * k ≤ 12 := by
        have hjk : 12 * k + n₀ % 12 = n₀ := by
          simpa [k, Nat.mul_comm] using (Nat.div_add_mod n₀ 12)
        have hnmod : n₀ % 12 < 12 := Nat.mod_lt n₀ (by norm_num)
        omega
      calc
        (π.take n₀).drop (12 * k)
            = (π.drop (12 * k)).take (n₀ - 12 * k) := by
                rw [List.drop_take]
        _ = ((π.take (12 * (k + 1))).drop (12 * k)).take (n₀ - 12 * k) := by
                rw [List.drop_take]
                rw [List.take_take]
                rw [hA]
                rw [Nat.min_eq_left hx']
    have hdet₀ : cfg₀ = cfgj := by
      have hsame : TapeSteps subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS) cfgcm
          (π₀.drop (12 * k)) cfgj := by
        rw [hmid_eq]
        exact hpfxj
      exact tapeSteps_det (π₀.drop (12 * k)) h₂' hsame
    rw [hdet₀]
    rcases hIcc with ⟨hlo, hhi⟩
    have hlenx : (encodeInstanceF4 inst ++ flat4F4 gS).length = 4 * wS.length := by
      rw [hx]
      simp [flat4F4_length]
    rw [hlenx]
    simp [Nat.cast_mul]
    have h4p : 4 * cfgsm.headPos + 4 ≤ 4 * (wS.length : ℤ) := by
      have hpz : cfgsm.headPos ≤ ((wS.length : ℕ) : ℤ) - 1 := hp_le
      have hwpos : (0 : ℤ) ≤ (wS.length : ℕ) := by simp
      nlinarith
    nlinarith

-- ============================================================
-- M2-gS：每前缀头 ≥ 0
-- ============================================================

lemma a2_accept_path_prefix_head_nonneg (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length) (ht : 0 < inst.target)
    (gS : List Sym) :
    ∀ {π : ComputationPath} {cfg : CBTMConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)},
      TapeSteps subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)
        (initialConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)) π cfg →
      cfg.state ∈ acceptStates4 →
      ∀ π₀ cfg₀,
        TapeSteps subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)
          (initialConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)) π₀ cfg₀ →
        List.IsPrefix π₀ π →
        (0 : ℤ) ≤ cfg₀.headPos := by
  let wS := encodeInstanceSym inst ++ gS
  have hx : encodeInstanceF4 inst ++ flat4F4 gS = flat4F4 wS := by
    simp [wS, encodeInstanceF4, flat4F4, List.flatMap_append]
  intro π cfg h hacc π₀ cfg₀ h₀ hp
  have htrap : ∀ k (hk : k < π.length),
      (decodeState (π.get ⟨k, hk⟩).result.nextState).1 ≠ 101 := accept_path_no_trap h hacc
  have hcorr0 : blockCorrespond (initialConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS))
      (symInitialConfig wS) := by
    rw [hx]
    exact initialBlockCorrespond wS
  have hq0 : (symInitialConfig wS).state ≤ 101 := by
    dsimp [symInitialConfig, SymConfig.mk, VerifierSym.qStart]
    norm_num
  have hbp : GoodBlockPath (encodeInstanceF4 inst ++ flat4F4 gS)
      (initialConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)) π cfg :=
    accept_path_is_good_block_path h hacc htrap hcorr0 hq0
  have hbridge := good_block_path_head_corresp (encodeInstanceF4 inst ++ flat4F4 gS) wS
    (initialConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)) (symInitialConfig wS)
    π cfg hcorr0 hbp htrap
  rcases hbridge with ⟨πs, cfgs', hsSym, hcorr', hlen12, hhead⟩
  have hreach : SymReachablePath VerifierSym.transition wS πs cfgs' :=
    (symSteps_initial_iff VerifierSym.transition wS πs cfgs').1 hsSym
  have haccS : cfgs'.state = VerifierSym.qAccept := by
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
  by_cases hfull : π₀ = π
  · subst π₀
    have hdet : cfg₀ = cfg := (tapeSteps_det π h h₀).symm
    subst cfg₀
    rw [hcorr'.2.1]
    have hgeS' : (0 : ℤ) ≤ cfgs'.headPos :=
      a2_sym_head_nonneg inst hm ht gS hreach haccS πs cfgs' hreach
        (by refine ⟨[], ?_⟩; simp)
    exact mul_nonneg (by norm_num) hgeS'
  · let n₀ := π₀.length
    let k := n₀ / 12
    have htake₀ : π₀ = π.take n₀ := by simpa [n₀] using (prefix_eq_take hp)
    have hn₀_le : n₀ ≤ π.length := by
      dsimp [n₀]
      rw [htake₀]
      simp [List.length_take]
    have hn₀_lt : n₀ < π.length := by
      by_contra hge
      have htake_all : π.take n₀ = π := by
        exact (List.take_eq_self_iff π).2 (Nat.le_of_not_gt hge)
      apply hfull
      rw [htake₀, htake_all]
    have hlen12' : π.length = 12 * πs.length := by
      rw [← hlen12]
      simp [Nat.mul_comm]
    have hn₀_lt12 : n₀ < 12 * πs.length := by
      rw [← hlen12']
      exact hn₀_lt
    have hk_lt : k < πs.length := by
      have hd := (Nat.div_lt_iff_lt_mul (k := 12) (y := πs.length) (by norm_num : 0 < 12)).2 (by
        simpa [Nat.mul_comm] using hn₀_lt12)
      simpa [k] using hd
    have hk1 : k + 1 ≤ πs.length := by omega
    rcases hhead k (by omega) with ⟨cfgsm, cfgcm, hSym_k, hTap_k, hpk, hstk⟩
    rcases hhead (k + 1) hk1 with ⟨cfgsm1, cfgcm1, hSym_k1, hTap_k1, hpk1, hstk1⟩
    have hreach_k : SymReachablePath VerifierSym.transition wS (πs.take k) cfgsm :=
      (symSteps_initial_iff VerifierSym.transition wS (πs.take k) cfgsm).1 hSym_k
    have h12k_le : 12 * k ≤ n₀ := by
      have hd := Nat.div_mul_le_self n₀ 12
      simpa [k, Nat.mul_comm] using hd
    have htake_eq : π₀.take (12 * k) = π.take (12 * k) := by
      rw [htake₀, List.take_take]
      rw [Nat.min_eq_left h12k_le]
    have hdec₀ := tapeSteps_append_decomp (π₁ := π₀.take (12 * k))
      (π₂ := π₀.drop (12 * k))
      (by simpa [List.take_append_drop] using h₀)
    rcases hdec₀ with ⟨cfg₁, h₁, h₂⟩
    have hdet₁ : cfg₁ = cfgcm := by
      exact tapeSteps_det (π.take (12 * k)) (by simpa [htake_eq] using h₁) hTap_k
    have h₂' : TapeSteps subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS) cfgcm
        (π₀.drop (12 * k)) cfg₀ := by
      simpa [hdet₁] using h₂
    have htt : (π.take (12 * (k + 1))).take (12 * k) = π.take (12 * k) := by
      rw [List.take_take]
      rw [Nat.min_eq_left (by omega : 12 * k ≤ 12 * (k + 1))]
    have hdec₁ := tapeSteps_append_decomp (π₁ := π.take (12 * k))
      (π₂ := (π.take (12 * (k + 1))).drop (12 * k))
      (by
        rw [← htt]
        simpa [List.take_append_drop] using hTap_k1)
    rcases hdec₁ with ⟨cfg₂, h₂a, h₂b⟩
    have hdet₂ : cfg₂ = cfgcm := tapeSteps_det (π.take (12 * k)) h₂a hTap_k
    have hb12 : TapeSteps subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS) cfgcm
        ((π.take (12 * (k + 1))).drop (12 * k)) cfgcm1 := by
      rw [← hdet₂]
      exact h₂b
    have hblen : ((π.take (12 * (k + 1))).drop (12 * k)).length = 12 := by
      have hle : 12 * (k + 1) ≤ π.length := by
        have hle' : 12 * (k + 1) ≤ 12 * πs.length := Nat.mul_le_mul_left 12 hk1
        simpa [hlen12', Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hle'
      exact block_drop_length hle
    have htr12 : ∀ m (hm : m < ((π.take (12 * (k + 1))).drop (12 * k)).length),
        (decodeState (((π.take (12 * (k + 1))).drop (12 * k)).get ⟨m, hm⟩).result.nextState).1 ≠ 101 := by
      intro m hm
      have hmem : ∀ step ∈ (π.take (12 * (k + 1))).drop (12 * k),
          (decodeState step.result.nextState).1 ≠ 101 := by
        intro step hs
        exact (trap_mem_of_get htrap) step (block_step_mem (π := π) (k := k) step hs)
      exact trap_get_of_mem hmem m hm
    have hmidlen : (π₀.drop (12 * k)).length ≤ 12 := by
      rw [List.length_drop]
      have hjk : 12 * k + n₀ % 12 = n₀ := by
        simpa [k, Nat.mul_comm] using (Nat.div_add_mod n₀ 12)
      have hnmod : n₀ % 12 < 12 := Nat.mod_lt n₀ (by norm_num)
      omega
    have hgeS : (0 : ℤ) ≤ cfgsm.headPos :=
      a2_sym_head_nonneg inst hm ht gS hreach haccS (πs.take k) cfgsm hreach_k
        (by refine ⟨πs.drop k, ?_⟩; simp [List.take_append_drop])
    by_cases hp0s : cfgsm.headPos = 0
    · have htail0 : (0 : ℤ) ≤ cfgcm1.headPos := by
        have hgeS1 : (0 : ℤ) ≤ cfgsm1.headPos := by
          have hreach_k1 : SymReachablePath VerifierSym.transition wS (πs.take (k + 1)) cfgsm1 :=
            (symSteps_initial_iff VerifierSym.transition wS (πs.take (k + 1)) cfgsm1).1 hSym_k1
          exact a2_sym_head_nonneg inst hm ht gS hreach haccS
            (πs.take (k + 1)) cfgsm1 hreach_k1 (by
              refine ⟨πs.drop (k + 1), ?_⟩
              simp [List.take_append_drop])
        rw [hpk1]
        exact mul_nonneg (by norm_num) hgeS1
      have hpp0 : cfgcm.headPos = 0 := by
        rw [hpk, hp0s]
        norm_num
      rcases (p0_block_prefix_nonneg hb12 hblen hstk hpp0 htr12 htail0)
        (π₀.drop (12 * k)).length hmidlen with ⟨cfgj, hpfxj, hge0⟩
      have hmid_eq : π₀.drop (12 * k) =
          ((π.take (12 * (k + 1))).drop (12 * k)).take (π₀.drop (12 * k)).length := by
        rw [htake₀]
        have hlen' : ((π.take n₀).drop (12 * k)).length = n₀ - 12 * k := by
          rw [List.length_drop, List.length_take]
          rw [Nat.min_eq_left hn₀_le]
        rw [hlen']
        have hA : 12 * (k + 1) - 12 * k = 12 := by omega
        have hx' : n₀ - 12 * k ≤ 12 := by
          have hjk : 12 * k + n₀ % 12 = n₀ := by
            simpa [k, Nat.mul_comm] using (Nat.div_add_mod n₀ 12)
          have hnmod : n₀ % 12 < 12 := Nat.mod_lt n₀ (by norm_num)
          omega
        calc
          (π.take n₀).drop (12 * k)
              = (π.drop (12 * k)).take (n₀ - 12 * k) := by
                  rw [List.drop_take]
          _ = ((π.take (12 * (k + 1))).drop (12 * k)).take (n₀ - 12 * k) := by
                  rw [List.drop_take]
                  rw [List.take_take]
                  rw [hA]
                  rw [Nat.min_eq_left hx']
      have hdet₀ : cfg₀ = cfgj := by
        have hsame : TapeSteps subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS) cfgcm
            (π₀.drop (12 * k)) cfgj := by
          rw [hmid_eq]
          exact hpfxj
        exact tapeSteps_det (π₀.drop (12 * k)) h₂' hsame
      rw [hdet₀]
      exact hge0
    · have hpge1 : 1 ≤ cfgsm.headPos := by omega
      rcases (a1_block_prefix_nonneg hb12 hblen hstk hpk htr12 hpge1)
        (π₀.drop (12 * k)).length hmidlen with ⟨cfgj, hpfxj, hge0, hhi⟩
      have hmid_eq : π₀.drop (12 * k) =
          ((π.take (12 * (k + 1))).drop (12 * k)).take (π₀.drop (12 * k)).length := by
        rw [htake₀]
        have hlen' : ((π.take n₀).drop (12 * k)).length = n₀ - 12 * k := by
          rw [List.length_drop, List.length_take]
          rw [Nat.min_eq_left hn₀_le]
        rw [hlen']
        have hA : 12 * (k + 1) - 12 * k = 12 := by omega
        have hx' : n₀ - 12 * k ≤ 12 := by
          have hjk : 12 * k + n₀ % 12 = n₀ := by
            simpa [k, Nat.mul_comm] using (Nat.div_add_mod n₀ 12)
          have hnmod : n₀ % 12 < 12 := Nat.mod_lt n₀ (by norm_num)
          omega
        calc
          (π.take n₀).drop (12 * k)
              = (π.drop (12 * k)).take (n₀ - 12 * k) := by
                  rw [List.drop_take]
          _ = ((π.take (12 * (k + 1))).drop (12 * k)).take (n₀ - 12 * k) := by
                  rw [List.drop_take]
                  rw [List.take_take]
                  rw [hA]
                  rw [Nat.min_eq_left hx']
      have hdet₀ : cfg₀ = cfgj := by
        have hsame : TapeSteps subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS) cfgcm
            (π₀.drop (12 * k)) cfgj := by
          rw [hmid_eq]
          exact hpfxj
        exact tapeSteps_det (π₀.drop (12 * k)) h₂' hsame
      rw [hdet₀]
      exact hge0

-- ============================================================
-- 主装配：#2 成品
-- ============================================================

/-- #2（F4 层）：x = encodeInstanceF4 inst ++ flat4F4 gS 上接受路径每前缀头 ∈ [0, |x|]。 -/
theorem a2_cbtm_accept_path_prefix_bound (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length) (ht : 0 < inst.target)
    (gS : List Sym) :
    ∀ {π : ComputationPath} {cfg : CBTMConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)},
      TapeSteps subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)
        (initialConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)) π cfg →
      cfg.state ∈ acceptStates4 →
      ∀ m (hm' : m ≤ π.length),
        ∃ cfgm : CBTMConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS),
          TapeSteps subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)
            (initialConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)) (π.take m) cfgm ∧
          (0 : ℤ) ≤ cfgm.headPos ∧
          cfgm.headPos ≤ ((encodeInstanceF4 inst ++ flat4F4 gS).length : ℤ) := by
  intro π cfg h hacc m hm'
  rcases tapeSteps_prefix_end h m hm' with ⟨cfgm, hpfx⟩
  refine ⟨cfgm, hpfx, ?_, ?_⟩
  · exact a2_accept_path_prefix_head_nonneg inst hm ht gS h hacc (π.take m) cfgm hpfx
      (by refine ⟨π.drop m, ?_⟩; simp [List.take_append_drop])
  · have hle := a2_accept_path_prefix_head_le inst hm ht gS h hacc (π.take m) cfgm hpfx
      (by refine ⟨π.drop m, ?_⟩; simp [List.take_append_drop])
    exact hle

/-- #2 可延拓封装（非接受路径消费形态）：可续行到接受 ⇒ 每前缀头 ∈ [0, |x|]。 -/
theorem a2_cbtm_extendable_path_prefix_bound (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length) (ht : 0 < inst.target)
    (gS : List Sym) :
    ∀ {π : ComputationPath} {cfg : CBTMConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)},
      TapeSteps subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)
        (initialConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)) π cfg →
      (∃ π₂ : ComputationPath, ∃ cfg₂ : CBTMConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS),
        TapeSteps subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS) cfg π₂ cfg₂ ∧
          cfg₂.state ∈ acceptStates4) →
      ∀ m (hm' : m ≤ π.length),
        ∃ cfgm : CBTMConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS),
          TapeSteps subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)
            (initialConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)) (π.take m) cfgm ∧
          (0 : ℤ) ≤ cfgm.headPos ∧
          cfgm.headPos ≤ ((encodeInstanceF4 inst ++ flat4F4 gS).length : ℤ) := by
  intro π cfg h hext m hm'
  rcases hext with ⟨π₂, cfg₂, h₂, hacc₂⟩
  have hfull : TapeSteps subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)
      (initialConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)) (π ++ π₂) cfg₂ :=
    a2_tapeSteps_comp h h₂
  have hmain := a2_cbtm_accept_path_prefix_bound inst hm ht gS hfull hacc₂ m
    (by rw [List.length_append]; omega)
  rcases hmain with ⟨cfgm, hpfx, hlo, hhi⟩
  refine ⟨cfgm, ?_, hlo, hhi⟩
  have heq : (π ++ π₂).take m = π.take m := List.take_append_of_le_length hm'
  simpa [heq] using hpfx

/-- flat4F4 [] = []（gS = [] 时 x = encodeInstanceF4 inst ++ flat4F4 [] 与 encodeInstanceF4 inst 恒等）。 -/
lemma a2p_flat4F4_nil : flat4F4 ([] : List Sym) = [] := rfl

/-- gS = [] 对照件：主定理的 gS = [] 实例。
    x = encodeInstanceF4 inst ++ flat4F4 ([] : List Sym)，由 `a2p_flat4F4_nil` 恒等于 A-1 的
    encodeInstanceF4 inst（界 ≤ |x| = 4·|encS|，与 a1_cbtm_accept_path_prefix_bound 形状一致）。 -/
theorem a2_cbtm_accept_path_prefix_bound_nil (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length) (ht : 0 < inst.target) :
    ∀ {π : ComputationPath}
      {cfg : CBTMConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 ([] : List Sym))},
      TapeSteps subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 ([] : List Sym))
        (initialConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 ([] : List Sym))) π cfg →
      cfg.state ∈ acceptStates4 →
      ∀ m (hm' : m ≤ π.length),
        ∃ cfgm : CBTMConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 ([] : List Sym)),
          TapeSteps subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 ([] : List Sym))
            (initialConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 ([] : List Sym)))
            (π.take m) cfgm ∧
          (0 : ℤ) ≤ cfgm.headPos ∧
          cfgm.headPos ≤ ((encodeInstanceF4 inst ++ flat4F4 ([] : List Sym)).length : ℤ) :=
  a2_cbtm_accept_path_prefix_bound inst hm ht ([] : List Sym)

end Mp
