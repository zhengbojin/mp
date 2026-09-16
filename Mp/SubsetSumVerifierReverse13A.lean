import Mp.SubsetSumVerifierReverse13

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

open Mp
open Mp.SymToF4

namespace Mp

/-! ========== P3 · 单调性（局部对照） ========== -/

/-- [P3 · 位级] 同位轮长差恰 +1：位1轮 `2k+2p_e+3` = 位0轮 `2k+2p_e+2` + 1。 -/
lemma len_d1_eq_len_d0_plus_one (k : ℕ) (p_e : ℤ) :
    2 * (k : ℤ) + 2 * p_e + 3 = 2 * (k : ℤ) + 2 * p_e + 2 + 1 := by
  ring

/-- [P3 · 位级 ≤ 形] 位0轮长 ≤ 位1轮长（消费形）。 -/
lemma len_d0_le_len_d1 (k : ℕ) (p_e : ℤ) :
    2 * (k : ℤ) + 2 * p_e + 2 ≤ 2 * (k : ℤ) + 2 * p_e + 3 := by
  omega

/-- [P3 · 元素级对照] 单元素 nosel 段界（`b+5`，R12 `segSrNosel`）≤ sel 段界（`el(b,p)`，R13 `segSrSel_gen`）。
    口径：sel vs nosel 只对比 1 个元素。 -/
lemma nosel_le_sel (b : ℕ) (p : ℤ) (hp : 0 ≤ p) :
    (b : ℤ) + 5 ≤ (b : ℤ) * (2 * (b : ℤ) + 2 * p + 3) + (4 * p + 4 * (b : ℤ) + 13) := by
  have hb : (0 : ℤ) ≤ (b : ℤ) := by positivity
  have h25 : (0 : ℤ) ≤ 2 * (b : ℤ) + 2 * p + 3 := by omega
  have hmul : 0 ≤ (b : ℤ) * (2 * (b : ℤ) + 2 * p + 3) := mul_nonneg hb h25
  omega

/-- [P2 桥 · 编码] 全1位段 → 全 data1 符号（worst 族元素位段编码小桥）。 -/
lemma bitsToSym_replicate_true (n : ℕ) :
    bitsToSym (List.replicate n true) = List.replicate n Sym.data1 := by
  induction n with
  | zero => simp [bitsToSym]
  | succ n ih => simp [bitsToSym, ih]

/-! ========== P1 · 确定性（段拼接前置） ========== -/

/-- [表级 · 单后继] 非 2 态转移表单后继（表基数 ≤ 1）——`(2,A-)` 是全表唯一双后继行。 -/
lemma symTransition_card_le_one (s : Sym) :
    ∀ (q : Fin 102), (q : ℕ) ≠ 2 → (VerifierSym.transition ((q : ℕ), s)).card ≤ 1 := by
  obtain ⟨k, m⟩ := s
  cases m <;> cases k <;> decide

/-- [表级 · 单后继] 非 2 态的两后继结果相等（段内确定性）。 -/
lemma symTransition_single_of_ne_two (s : Sym) (q : Fin 102) (hq : (q : ℕ) ≠ 2)
    {r₁ r₂ : SymTransResult}
    (h₁ : r₁ ∈ VerifierSym.transition ((q : ℕ), s))
    (h₂ : r₂ ∈ VerifierSym.transition ((q : ℕ), s)) : r₁ = r₂ :=
  (Finset.card_le_one.mp (symTransition_card_le_one s q hq)) r₁ h₁ r₂ h₂

/-- [P1 · 拼接] 单步运行（从 cfg 沿 step 到步后配置）。 -/
lemma symSteps_single (cfg : SymConfig) (step : SymStep)
    (hfrom : step.fromState = cfg.state) (hread : step.readSym = cfg.tape cfg.headPos)
    (hmem : step.result ∈ VerifierSym.transition (cfg.state, cfg.tape cfg.headPos)) :
    SymSteps VerifierSym.transition cfg [step] (symStepConfig cfg step.result) :=
  SymSteps.cons (M := VerifierSym.transition) (cfg₀ := cfg) [] step
    cfg SymSteps.nil hfrom hread hmem

/-- [P1 · 确定性] 单步重合：同配置、非 2 态，两单步运行的步相等。 -/
lemma symSteps_single_eq {cfg cfg₁ cfg₂ : SymConfig} {s₁ s₂ : SymStep}
    (h₁ : SymSteps VerifierSym.transition cfg [s₁] cfg₁)
    (h₂ : SymSteps VerifierSym.transition cfg [s₂] cfg₂)
    (hle : cfg.state < 102) (hne : cfg.state ≠ 2) : s₁ = s₂ := by
  obtain ⟨hf₁, hr₁, hm₁, _⟩ := symSteps_singleton_facts h₁
  obtain ⟨hf₂, hr₂, hm₂, _⟩ := symSteps_singleton_facts h₂
  have hq : ((⟨cfg.state, hle⟩ : Fin 102) : ℕ) ≠ 2 := by
    simpa using hne
  have hres : s₁.result = s₂.result :=
    symTransition_single_of_ne_two (cfg.tape cfg.headPos) ⟨cfg.state, hle⟩ hq hm₁ hm₂
  have hf : s₁.fromState = s₂.fromState := hf₁.trans hf₂.symm
  have hr : s₁.readSym = s₂.readSym := hr₁.trans hr₂.symm
  cases s₁ with
  | mk f₁ r₁ res₁ =>
    cases s₂ with
    | mk f₂ r₂ res₂ =>
      simp only [SymStep.mk.injEq]
      exact ⟨hf, hr, hres⟩

/-- [P1 · 确定性] 前缀相容：同起点两运行，第一条沿途非 2 态 ⟹ 一为另一的前缀（且余段是运行）。 -/
lemma symSteps_prefix_comp {cfg₀ cfg₁ cfg₂ : SymConfig} {σ π : List SymStep}
    (hσ : SymSteps VerifierSym.transition cfg₀ σ cfg₁)
    (hπ : SymSteps VerifierSym.transition cfg₀ π cfg₂)
    (h0 : cfg₀.state ≤ 101)
    (hno2 : ∀ step ∈ σ, step.fromState ≠ 2) :
    (∃ r, π = σ ++ r ∧ SymSteps VerifierSym.transition cfg₁ r cfg₂) ∨
    (∃ r, σ = π ++ r ∧ SymSteps VerifierSym.transition cfg₂ r cfg₁) := by
  revert hπ hno2
  induction hσ generalizing π cfg₂ with
  | nil =>
      intro hπ _
      exact Or.inl ⟨π, by simp, hπ⟩
  | cons σ₀ step cfg₁' hprev hfrom hread htrans ih =>
      intro hπ hno2
      have hno2' : ∀ st ∈ σ₀, st.fromState ≠ 2 := by
        intro st hst
        exact hno2 st (by rw [List.mem_append]; left; exact hst)
      have hle : cfg₁'.state < 102 := by
        have hb := symSteps_state_le101 hprev h0
        omega
      have hne2 : cfg₁'.state ≠ 2 := by
        have hs := hno2 step (by rw [List.mem_append]; right; simp)
        rwa [hfrom] at hs
      have hsingle : SymSteps VerifierSym.transition cfg₁' [step]
          (symStepConfig cfg₁' step.result) :=
        symSteps_single cfg₁' step hfrom hread htrans
      rcases ih hπ hno2' with ⟨r, hr, hrun⟩ | ⟨r, hr, hrun⟩
      · -- π = σ₀ ++ r：先看 r 是否空
        rcases r with _ | ⟨r₁, r'⟩
        · -- r = []：π = σ₀，σ = π ++ [step]
          right
          have hcfg₂ : cfg₂ = cfg₁' := symSteps_nil_cfg hrun
          refine ⟨[step], ?_, ?_⟩
          · rw [hr, List.append_nil]
          · rw [hcfg₂]
            exact hsingle
        · -- r = r₁ :: r'：拆出首步 r₁，与 step 重合
          rcases symSteps_append_split (M := VerifierSym.transition) (π₀ := [r₁]) (rest := r')
            (by simpa using hrun) with ⟨mid, hsingle₁, hrest⟩
          have hstepeq : step = r₁ := symSteps_single_eq hsingle hsingle₁ hle hne2
          have hmideq : mid = symStepConfig cfg₁' r₁.result :=
            (symSteps_singleton_fromState hsingle₁).2
          left
          refine ⟨r', ?_, ?_⟩
          · rw [hr, hstepeq]
            simp only [List.singleton_append, List.append_assoc]
          · rw [hstepeq, ← hmideq]
            exact hrest
      · -- σ₀ = π ++ r：σ = π ++ (r ++ [step])
        right
        refine ⟨r ++ [step], ?_, ?_⟩
        · rw [hr, List.append_assoc]
        · exact SymSteps_trans VerifierSym.transition cfg₂ cfg₁'
            (symStepConfig cfg₁' step.result) r [step] hrun hsingle

/-- [P1 · 首达分割] 任意步谓词的首达拆分：路径上要么无满足 p 的步，要么在首个处拆为
    `π₀ ++ step :: π₁`（π₀ 内全不满足 p，π₀ 终点配置状态 = step.fromState）。 -/
lemma symSteps_first_split (p : SymStep → Prop) :
    ∀ {cfg₀ cfg : SymConfig} {π : List SymStep},
      SymSteps VerifierSym.transition cfg₀ π cfg →
      (∀ s ∈ π, ¬ p s) ∨
      ∃ π₀ step π₁ cfgmid, π = π₀ ++ step :: π₁ ∧ p step ∧
        (∀ s ∈ π₀, ¬ p s) ∧
        SymSteps VerifierSym.transition cfg₀ π₀ cfgmid ∧ cfgmid.state = step.fromState := by
  intro cfg₀ cfg π h
  induction h with
  | nil =>
      left
      intro s hs
      simp at hs
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      rcases ih with hclean | ⟨π₀', st, π₁', cmid, hsplit, hp_st, hclean', hcmid, hstate'⟩
      · by_cases hp_step : p step
        · right
          refine ⟨π₀, step, [], cfg₁, ?_, hp_step, hclean, hprev, ?_⟩
          · simp
          · exact hfrom.symm
        · left
          intro s hs
          rcases List.mem_append.mp hs with hm | hm'
          · exact hclean s hm
          · have hsing : s = step := by
              simpa using hm'
            rw [hsing]
            exact hp_step
      · right
        refine ⟨π₀', st, π₁' ++ [step], cmid, ?_, hp_st, hclean', hcmid, hstate'⟩
        rw [hsplit]
        simp [List.append_assoc]

/-- [P1 · 阶段] α 之后可达状态集（3 = α 出口；格式/轮/清尾/判定诸态 + 100）。 -/
def postAlpha : List ℕ :=
  [3, 24, 29, 26, 27, 38, 28, 4, 5, 76, 77, 10, 11, 14, 81, 8, 9, 12, 13, 84, 85, 86, 87,
    20, 21, 51, 22, 23, 100]

/-- [P1 · 阶段] 表级封口：进入 α 后状态集的步，其来态 ∈ 后状态集 ∪ {2}（且来态 = 2 时目标恰为 3）。 -/
lemma transition_postAlpha_entry (s : Sym) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), s),
      r.nextState ∈ postAlpha → (q : ℕ) ∈ postAlpha ∨ ((q : ℕ) = 2 ∧ r.nextState = 3) := by
  obtain ⟨k, m⟩ := s
  cases m <;> cases k <;> decide

/-- [P1 · 阶段] 阶段不变量：自初始运行要么历过 3，要么从未进入 α 后状态集（且终态不在其中）。 -/
lemma symSteps_from_initial_stage_inv {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition (symInitialConfig input) π cfg) :
    (∃ s ∈ π, s.result.nextState = 3) ∨
    (cfg.state ∉ postAlpha ∧ ∀ s ∈ π, s.result.nextState ∉ postAlpha) := by
  have h0 : (symInitialConfig input).state ≤ 101 := by simp [symInitialConfig]
  induction h with
  | nil =>
      right
      constructor
      · simp [symInitialConfig, postAlpha]
      · intro s hs
        simp at hs
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      rcases ih with ⟨s, hs, h3⟩ | ⟨hc₁, hnp₀⟩
      · left
        exact ⟨s, by rw [List.mem_append]; left; exact hs, h3⟩
      · by_cases hp : step.result.nextState ∈ postAlpha
        · have hlt : cfg₁.state < 102 := by
            have := (symSteps_state_le101 hprev h0).1
            omega
          have hmem : step.result ∈ VerifierSym.transition
              (((⟨cfg₁.state, hlt⟩ : Fin 102) : ℕ), step.readSym) := by
            have h2 := htrans
            rw [← hread] at h2
            exact h2
          rcases transition_postAlpha_entry step.readSym ⟨cfg₁.state, hlt⟩ step.result hmem hp with
            hinP | ⟨_, hnext3⟩
          · exact absurd (by simpa using hinP) hc₁
          · left
            exact ⟨step, by rw [List.mem_append]; right; simp, hnext3⟩
        · right
          constructor
          · simpa [symStepConfig] using hp
          · intro s hs
            rw [List.mem_append] at hs
            rcases hs with hmem' | hlast
            · exact hnp₀ s hmem'
            · rw [List.mem_singleton] at hlast
              subst hlast
              exact hp

/-- [P1 · 阶段] 接受运行必过 3：从初始配置到达 100 的运行中，存在一步其 nextState = 3。 -/
lemma symSteps_accept_hits_three {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition (symInitialConfig input) π cfg)
    (hacc : cfg.state = 100) :
    ∃ s ∈ π, s.result.nextState = 3 := by
  rcases symSteps_from_initial_stage_inv h with ⟨s, hs, h3⟩ | ⟨hc, _⟩
  · exact ⟨s, hs, h3⟩
  · exact absurd (by rw [hacc]; decide) hc

/-! ========== P1 · ①α 段表件（给定运行扫掠分析） ========== -/

/-- [P1 · ①表] state 0 读 #ₗ：唯一后继 `{1, #, R}`（写回 #）。 -/
lemma transition_zero_boundary :
    ∀ (r : SymTransResult), r ∈ VerifierSym.transition ((0 : ℕ), Sym.boundary) →
      r.nextState = 1 ∧ r.moveDir = Dir.R ∧ r.writeSym = Sym.boundary := by
  decide

/-- [P1 · ①表] state 1 读数据位：保持原符号、右移、留 1。 -/
lemma transition_one_keep (s : Sym) (hs : s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) :
    ∀ r ∈ VerifierSym.transition ((1 : ℕ), s),
      r.nextState = 1 ∧ r.moveDir = Dir.R ∧ r.writeSym = s := by
  obtain ⟨k, m⟩ := s
  rcases hs with h | h
  · cases h
    cases m <;> decide
  · cases h
    cases m <;> decide

/-- [P1 · ①表] state 1 读 #₀：`{2, #, R}`。 -/
lemma transition_one_boundary :
    ∀ (r : SymTransResult), r ∈ VerifierSym.transition ((1 : ℕ), Sym.boundary) →
      r.nextState = 2 ∧ r.moveDir = Dir.R ∧ r.writeSym = Sym.boundary := by
  decide

/-- [P1 · ①表] state 2 读数据位：保持原符号、右移、留 2。 -/
lemma transition_two_keep (s : Sym) (hs : s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) :
    ∀ r ∈ VerifierSym.transition ((2 : ℕ), s),
      r.nextState = 2 ∧ r.moveDir = Dir.R ∧ r.writeSym = s := by
  obtain ⟨k, m⟩ := s
  rcases hs with h | h
  · cases h
    cases m <;> decide
  · cases h
    cases m <;> decide

/-- [P1 · ①表] state 2 读 α（`Sym.alpha`，mark false）：双后继均 `{2, ·, R}`，写 ∈ {sel, nosel}（选择无关长度）。 -/
lemma transition_two_alpha (s : Sym) (hs : s = Sym.alpha) :
    ∀ r ∈ VerifierSym.transition ((2 : ℕ), s),
      r.nextState = 2 ∧ r.moveDir = Dir.R ∧ (r.writeSym = Sym.sel ∨ r.writeSym = Sym.nosel) := by
  subst hs
  decide

/-- [P1 · ①表] state 2 读 #₁：`{3, #, S}`（停）。 -/
lemma transition_two_boundary :
    ∀ (r : SymTransResult), r ∈ VerifierSym.transition ((2 : ℕ), Sym.boundary) →
      r.nextState = 3 ∧ r.moveDir = Dir.S ∧ r.writeSym = Sym.boundary := by
  decide

/-- [P1 · ①表] state 2 读 β：落 101（拒绝）。 -/
lemma transition_two_beta (s : Sym) (hs : s.1 = SymKind.beta) :
    ∀ r ∈ VerifierSym.transition ((2 : ℕ), s), r.nextState = 101 := by
  obtain ⟨k, m⟩ := s
  cases hs
  cases m <;> decide

/-- [P1 · ①表] 3 的进入：只从 state 2 读 #₁（plain boundary）。 -/
lemma transition_three_entry :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), Sym.boundary),
      r.nextState = 3 → (q : ℕ) = 2 := by
  decide

/-- [P1 · ①工具] 终态非 101 ⟹ 途中无 101 步（101 吸收）。 -/
lemma symSteps_no_101_of_end_ne :
    ∀ {cfg₀ cfg : SymConfig} {π : List SymStep},
      SymSteps VerifierSym.transition cfg₀ π cfg → cfg.state ≠ 101 →
      ∀ s ∈ π, s.result.nextState ≠ 101 := by
  intro cfg₀ cfg π h
  induction h with
  | nil =>
      intro _ s hs
      simp at hs
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro hne
      have hne' : step.result.nextState ≠ 101 := by
        intro h101
        exact hne (by simpa [symStepConfig] using h101)
      have hne₁ : cfg₁.state ≠ 101 := by
        intro hc
        have h2 : step.result ∈ VerifierSym.transition (101, cfg₁.tape cfg₁.headPos) := by
          have h3 := htrans
          rw [hc] at h3
          exact h3
        exact hne' (symTransition_trap101_absorb (cfg₁.tape cfg₁.headPos) step.result h2)
      intro s hs
      rcases List.mem_append.mp hs with h | h
      · exact ih hne₁ s h
      · rw [List.mem_singleton] at h
        subst h
        exact hne'

/-- [P1 · ①工具] 接受运行（终态 100）途中无 101 步。 -/
lemma symSteps_accept_no_101 {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition (symInitialConfig input) π cfg)
    (hacc : cfg.state = 100) :
    ∀ s ∈ π, s.result.nextState ≠ 101 :=
  symSteps_no_101_of_end_ne h (by rw [hacc]; norm_num)

/-- [P1 · ①工具] 全 R 运行：终头位 = 起头位 + 步数。 -/
lemma head_eq_of_all_right (M : ℕ × Sym → Finset SymTransResult) :
    ∀ {cfg₀ cfg : SymConfig} {π : List SymStep},
      SymSteps M cfg₀ π cfg → (∀ s ∈ π, s.result.moveDir = Dir.R) →
      cfg.headPos = cfg₀.headPos + (π.length : ℤ) := by
  intro cfg₀ cfg π h
  induction h with
  | nil =>
      intro _
      simp
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro hR
      have hRstep : step.result.moveDir = Dir.R := hR step (by simp)
      have hR₀ : ∀ s ∈ π₀, s.result.moveDir = Dir.R :=
        fun s hs => hR s (by rw [List.mem_append]; left; exact hs)
      have ih' := ih hR₀
      rw [List.length_append]
      simp only [List.length_cons, List.length_nil]
      push_cast
      have hhead : (symStepConfig cfg₁ step.result).headPos = cfg₁.headPos + 1 := by
        simp [symStepConfig, hRstep, Dir.toInt]
      rw [hhead]
      rw [ih']
      omega

/-- [P1 · ①工具] 全 S 运行：终头位 = 起头位。 -/
lemma head_eq_of_all_stay (M : ℕ × Sym → Finset SymTransResult) :
    ∀ {cfg₀ cfg : SymConfig} {π : List SymStep},
      SymSteps M cfg₀ π cfg → (∀ s ∈ π, s.result.moveDir = Dir.S) →
      cfg.headPos = cfg₀.headPos := by
  intro cfg₀ cfg π h
  induction h with
  | nil =>
      intro _
      simp
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro hS
      have hSstep : step.result.moveDir = Dir.S := hS step (by simp)
      have hS₀ : ∀ s ∈ π₀, s.result.moveDir = Dir.S :=
        fun s hs => hS s (by rw [List.mem_append]; left; exact hs)
      have ih' := ih hS₀
      have hhead : (symStepConfig cfg₁ step.result).headPos = cfg₁.headPos := by
        simp [symStepConfig, hSstep, Dir.toInt]
      rw [hhead]
      rw [ih']

/-- [P1 · ①表] state 0 出发的后继 ∈ {1, 2, 101}。 -/
lemma transition_zero_nexts (s : Sym) :
    ∀ r ∈ VerifierSym.transition ((0 : ℕ), s), r.nextState ∈ [1, 2, 101] := by
  obtain ⟨k, m⟩ := s
  cases m <;> cases k <;> decide

/-- [P1 · ①表] state 1 出发的后继 ∈ {1, 2, 101}。 -/
lemma transition_one_nexts (s : Sym) :
    ∀ r ∈ VerifierSym.transition ((1 : ℕ), s), r.nextState ∈ [1, 2, 101] := by
  obtain ⟨k, m⟩ := s
  cases m <;> cases k <;> decide

/-- [P1 · ①表] state 2 出发的后继 ∈ {2, 3, 101}。 -/
lemma transition_two_nexts (s : Sym) :
    ∀ r ∈ VerifierSym.transition ((2 : ℕ), s), r.nextState ∈ [2, 3, 101] := by
  obtain ⟨k, m⟩ := s
  cases m <;> cases k <;> decide

/-- [P1 · ①表] state 2 的自环步（next = 2）必右移（选择无关）。 -/
lemma transition_two_selfstep (s : Sym) :
    ∀ r ∈ VerifierSym.transition ((2 : ℕ), s), r.nextState = 2 → r.moveDir = Dir.R := by
  obtain ⟨k, m⟩ := s
  cases m <;> cases k <;> decide

/-- [P1 · ①表] state 2 不会回到 state 1。 -/
lemma transition_two_not_one (s : Sym) :
    ∀ r ∈ VerifierSym.transition ((2 : ℕ), s), r.nextState ≠ 1 := by
  obtain ⟨k, m⟩ := s
  cases m <;> cases k <;> decide

/-- [P1 · 阶段] 3 前收窄：未历 3 的运行，其步后继 ∈ {1, 2, 101}。 -/
lemma symSteps_stage_inv2 {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition (symInitialConfig input) π cfg) :
    (∃ s ∈ π, s.result.nextState = 3) ∨ (∀ s ∈ π, s.result.nextState ∈ [1, 2, 101]) := by
  induction h with
  | nil =>
      right
      intro s hs
      simp at hs
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      rcases ih with ⟨s, hs, h3⟩ | hall₀
      · left
        exact ⟨s, by rw [List.mem_append]; left; exact hs, h3⟩
      · by_cases h3 : step.result.nextState = 3
        · left
          exact ⟨step, by rw [List.mem_append]; right; simp, h3⟩
        · right
          have hstepmem : step.result.nextState ∈ [1, 2, 101] := by
            have hq : cfg₁.state ∈ [0, 1, 2, 101] := by
              by_cases hemp : π₀ = []
              · subst hemp
                rw [symSteps_nil_cfg hprev]
                simp [symInitialConfig]
              · -- π₀ 非空：末步后继 = cfg₁.state
                have hsplit : π₀.dropLast ++ [π₀.getLast hemp] = π₀ :=
                  List.dropLast_append_getLast hemp
                rw [← hsplit] at hprev
                rcases symSteps_append_split (M := VerifierSym.transition)
                  (cfg₀ := symInitialConfig input) (cfg' := cfg₁) (π₀ := π₀.dropLast)
                  (rest := [π₀.getLast hemp]) hprev with ⟨mid, _, hlast⟩
                obtain ⟨_, hcfgLast⟩ := symSteps_singleton_fromState hlast
                have hmemLast : π₀.getLast hemp ∈ π₀ := List.getLast_mem hemp
                have h1 := hall₀ (π₀.getLast hemp) hmemLast
                rw [hcfgLast]
                have h2 : (π₀.getLast hemp).result.nextState ∈ [0, 1, 2, 101] :=
                  List.mem_cons_of_mem 0 h1
                simpa [symStepConfig] using h2
            have hmem : step.result ∈ VerifierSym.transition (cfg₁.state, step.readSym) := by
              have h2 := htrans
              rw [← hread] at h2
              exact h2
            rcases List.mem_cons.mp hq with h0 | hq'
            · rw [h0] at hmem
              exact transition_zero_nexts step.readSym step.result hmem
            rcases List.mem_cons.mp hq' with h1 | hq''
            · rw [h1] at hmem
              exact transition_one_nexts step.readSym step.result hmem
            rcases List.mem_cons.mp hq'' with h2 | hq'''
            · rw [h2] at hmem
              have htw := transition_two_nexts step.readSym step.result hmem
              rcases List.mem_cons.mp htw with h2a | htw'
              · rw [h2a]
                decide
              rcases List.mem_cons.mp htw' with h3a | htw''
              · exact absurd h3a h3
              · rw [List.mem_singleton.mp htw'']
                decide
            · rw [List.mem_singleton.mp hq'''] at hmem
              have hnext := symTransition_trap101_absorb step.readSym step.result hmem
              rw [hnext]
              simp
          intro s hs
          rcases List.mem_append.mp hs with h | h
          · exact hall₀ s h
          · rw [List.mem_singleton] at h
            subst h
            exact hstepmem

/-- [P1 · ①工具] 运行终态刻画：终态 = 起点态或某步后继。 -/
lemma symSteps_state_char {M : ℕ × Sym → Finset SymTransResult} :
    ∀ {cfg₀ cfg : SymConfig} {π : List SymStep}, SymSteps M cfg₀ π cfg →
      (cfg.state = cfg₀.state ∨ ∃ s ∈ π, s.result.nextState = cfg.state) := by
  intro cfg₀ cfg π h
  induction h with
  | nil => exact Or.inl rfl
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      exact Or.inr ⟨step, by simp, rfl⟩

/-- [P1 · ①工具] 步来态刻画：每步 fromState = 起点态或某步后继。 -/
lemma symSteps_fromState_char {M : ℕ × Sym → Finset SymTransResult} :
    ∀ {cfg₀ cfg : SymConfig} {π : List SymStep}, SymSteps M cfg₀ π cfg →
      ∀ s ∈ π, s.fromState = cfg₀.state ∨ ∃ s' ∈ π, s'.result.nextState = s.fromState := by
  intro cfg₀ cfg π h
  induction h with
  | nil =>
      intro s hs
      simp at hs
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro s hs
      rcases List.mem_append.mp hs with hh | hh
      · rcases ih s hh with heq | ⟨s', hs', hnext⟩
        · exact Or.inl heq
        · exact Or.inr ⟨s', by rw [List.mem_append]; left; exact hs', hnext⟩
      · rw [List.mem_singleton] at hh
        subst hh
        rcases symSteps_state_char hprev with heq | ⟨s', hs', hnext⟩
        · left
          rw [hfrom, heq]
        · right
          refine ⟨s', by rw [List.mem_append]; left; exact hs', ?_⟩
          rw [hfrom]
          exact hnext

/-- [P1 · ①工具] 逐步隶属：运行中每步的 result 属该步 (fromState, readSym) 的转移表。 -/
lemma symSteps_step_mem {M : ℕ × Sym → Finset SymTransResult} :
    ∀ {cfg₀ cfg : SymConfig} {π : List SymStep}, SymSteps M cfg₀ π cfg →
      ∀ s ∈ π, s.result ∈ M (s.fromState, s.readSym) := by
  intro cfg₀ cfg π h
  induction h with
  | nil =>
      intro s hs
      simp at hs
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro s hs
      rcases List.mem_append.mp hs with hh | hh
      · exact ih s hh
      · rw [List.mem_singleton] at hh
        subst hh
        rw [← hfrom, ← hread] at htrans
        exact htrans

/-- [P1 · ①表] 中段（来态 ∈{0,1,2}）后继 ∈{1,2} 的步必右移。 -/
lemma transition_mid_moves (q : ℕ) (hq : q ∈ [0, 1, 2]) (s : Sym) :
    ∀ r ∈ VerifierSym.transition (q, s), r.nextState ∈ [1, 2] → r.moveDir = Dir.R := by
  rcases List.mem_cons.mp hq with h0 | hq'
  · cases h0
    obtain ⟨k, m⟩ := s
    cases m <;> cases k <;> decide
  rcases List.mem_cons.mp hq' with h1 | hq''
  · cases h1
    obtain ⟨k, m⟩ := s
    cases m <;> cases k <;> decide
  · cases List.mem_singleton.mp hq''
    obtain ⟨k, m⟩ := s
    cases m <;> cases k <;> decide

/-- [P1 · ①表] 3 的进入（kind 级）：只从 state 2 读 #（任意标）。 -/
lemma transition_three_entry_kind (s : Sym) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), s),
      r.nextState = 3 → ((q : ℕ) = 2 ∧ s.1 = SymKind.boundary) := by
  obtain ⟨k, m⟩ := s
  cases m <;> cases k <;> decide

/-- [P1 · ①裁切] 接受运行在首个 3 处切分：π = π₀ ++ step₃ :: π₁；π₀ 无 3 命中、
    全 R、后继 ∈{1,2}、来态 ∈{0,1,2}；step₃ 从 2 读 # 进入 3；π₀ 终点头位 = |π₀|。 -/
lemma run_carve {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition (symInitialConfig input) π cfg)
    (hacc : cfg.state = 100) :
    ∃ (π₀ : List SymStep) (step₃ : SymStep) (π₁ : List SymStep) (cfgm : SymConfig),
      π = π₀ ++ step₃ :: π₁ ∧
      step₃.result.nextState = 3 ∧
      step₃.fromState = 2 ∧
      cfgm.state = 2 ∧
      step₃.readSym.1 = SymKind.boundary ∧
      (∀ s ∈ π₀, s.result.nextState ≠ 3) ∧
      SymSteps VerifierSym.transition (symInitialConfig input) π₀ cfgm ∧
      (∀ s ∈ π₀, s.result.nextState ∈ [1, 2]) ∧
      (∀ s ∈ π₀, s.result.moveDir = Dir.R) ∧
      (∀ s ∈ π₀, s.fromState ∈ [0, 1, 2]) ∧
      cfgm.headPos = (π₀.length : ℤ) := by
  rcases symSteps_first_split (fun s => s.result.nextState = 3) h with
    hnone | ⟨π₀, step₃, π₁, cfgm, hsplit, hp3, hclean, hrun, hstate⟩
  · exfalso
    rcases symSteps_accept_hits_three h hacc with ⟨s, hs, h3⟩
    exact hnone s hs h3
  · have hn101 : ∀ s ∈ π₀, s.result.nextState ≠ 101 := by
      intro s hs
      exact symSteps_accept_no_101 h hacc s (by rw [hsplit]; exact List.mem_append.mpr (Or.inl hs))
    have hnexts : ∀ s ∈ π₀, s.result.nextState ∈ [1, 2] := by
      intro s hs
      rcases symSteps_stage_inv2 hrun with h3seen | hall
      · rcases h3seen with ⟨s', hs', h3'⟩
        exact absurd h3' (hclean s' hs')
      · rcases List.mem_cons.mp (hall s hs) with he1 | h1'
        · rw [he1]; decide
        · rcases List.mem_cons.mp h1' with he2 | h1''
          · rw [he2]; decide
          · exact absurd (List.mem_singleton.mp h1'') (hn101 s hs)
    have hfroms : ∀ s ∈ π₀, s.fromState ∈ [0, 1, 2] := by
      intro s hs
      rcases symSteps_fromState_char hrun s hs with heq | ⟨s', hs', hnext⟩
      · rw [heq]
        simp [symInitialConfig]
      · rw [← hnext]
        exact List.mem_cons_of_mem 0 (hnexts s' hs')
    have hR : ∀ s ∈ π₀, s.result.moveDir = Dir.R := by
      intro s hs
      exact transition_mid_moves s.fromState (hfroms s hs) s.readSym s.result
        (symSteps_step_mem hrun s hs) (hnexts s hs)
    have hhead : cfgm.headPos = (π₀.length : ℤ) := by
      have h := head_eq_of_all_right VerifierSym.transition hrun hR
      simpa [symInitialConfig, SymConfig.mk] using h
    have hlt : cfgm.state < 102 := by
      have := (symSteps_state_le101 hrun (by simp [symInitialConfig])).1
      omega
    have hmem3 : step₃.result ∈ VerifierSym.transition (cfgm.state, step₃.readSym) := by
      have h2 := symSteps_step_mem h step₃ (by rw [hsplit]; exact List.mem_append.mpr (Or.inr (by simp)))
      rwa [← hstate] at h2
    obtain ⟨hq2, hkind⟩ :=
      transition_three_entry_kind step₃.readSym ⟨cfgm.state, hlt⟩ step₃.result hmem3 hp3
    have hfrom3 : step₃.fromState = 2 := by
      rw [← hstate]
      simpa using hq2
    have hq2v : cfgm.state = 2 := by
      simpa using hq2
    exact ⟨π₀, step₃, π₁, cfgm, hsplit, hp3, hfrom3, hq2v, hkind, hclean, hrun, hnexts, hR, hfroms, hhead⟩

/-- [P1 · ①读追踪] 全 R 运行：头位以上区域与初始带一致（写只发生在已过的头位）。 -/
lemma run_tape_high_agree {M : ℕ × Sym → Finset SymTransResult} :
    ∀ {cfg₀ cfg : SymConfig} {π : List SymStep}, SymSteps M cfg₀ π cfg →
      (∀ s ∈ π, s.result.moveDir = Dir.R) →
      ∀ j : ℤ, cfg.headPos ≤ j → cfg.tape j = cfg₀.tape j := by
  intro cfg₀ cfg π h
  induction h with
  | nil =>
      intro _ j _
      rfl
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro hR j hj
      have hRstep : step.result.moveDir = Dir.R := hR step (by simp)
      have hR₀ : ∀ s ∈ π₀, s.result.moveDir = Dir.R :=
        fun s hs => hR s (by rw [List.mem_append]; left; exact hs)
      have ih' := ih hR₀
      have h2 : cfg₁.headPos + 1 ≤ j := by
        simpa [symStepConfig, hRstep, Dir.toInt] using hj
      have hj' : cfg₁.headPos ≤ j := by omega
      have hne : j ≠ cfg₁.headPos := by omega
      simp only [symStepConfig]
      rw [if_neg hne]
      exact ih' j hj'

/-- [P1 · ①读追踪] 全 R 运行：第 i 步之读 = 初始带在 `head₀ + i` 处的值（头单调 ⟹ 每格首访）。 -/
lemma run_reads_index {M : ℕ × Sym → Finset SymTransResult} :
    ∀ {cfg₀ cfg : SymConfig} {π : List SymStep}, SymSteps M cfg₀ π cfg →
      (∀ s ∈ π, s.result.moveDir = Dir.R) →
      ∀ (i : ℕ) (hi : i < π.length),
        (π.get ⟨i, hi⟩).readSym = cfg₀.tape (cfg₀.headPos + (i : ℤ)) := by
  intro cfg₀ cfg π h
  induction h with
  | nil =>
      intro _ i hi
      simp at hi
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro hR i hi
      -- 先看 i < |π₀| 还是 i = |π₀|
      by_cases hlt : i < π₀.length
      · -- 前缀内：用 ih
        have hR₀ : ∀ s ∈ π₀, s.result.moveDir = Dir.R :=
          fun s hs => hR s (by rw [List.mem_append]; left; exact hs)
        have hget : (π₀ ++ [step]).get ⟨i, hi⟩ = π₀.get ⟨i, hlt⟩ :=
          List.getElem_append_left hlt
        rw [hget]
        exact ih hR₀ i hlt
      · -- i = |π₀|：末步
        have hie : i = π₀.length := by
          have h2 : (π₀ ++ [step]).length = π₀.length + 1 := by simp
          omega
        subst hie
        have hget : (π₀ ++ [step]).get ⟨π₀.length, hi⟩ = step := by
          have h1 := List.getLast_eq_getElem (l := π₀ ++ [step]) (h := by simp)
          have h2 : (π₀ ++ [step]).get ⟨π₀.length, hi⟩ =
              (π₀ ++ [step]).getLast (by simp) := by
            rw [h1]
            congr 1
            apply Fin.ext
            simp
          rw [h2]
          simpa only [List.concat_eq_append] using List.getLast_concat' π₀
        rw [hget]
        -- step.readSym = cfg₁.tape cfg₁.headPos（结构）——从 hread；再证 cfg₁ 头处带值 = 初始值
        have hR₀ : ∀ s ∈ π₀, s.result.moveDir = Dir.R :=
          fun s hs => hR s (by rw [List.mem_append]; left; exact hs)
        have hhead₁ : cfg₁.headPos = cfg₀.headPos + (π₀.length : ℤ) :=
          head_eq_of_all_right M hprev hR₀
        have htape₁ : cfg₁.tape cfg₁.headPos = cfg₀.tape cfg₁.headPos :=
          run_tape_high_agree hprev hR₀ cfg₁.headPos le_rfl
        rw [hread, htape₁, hhead₁]

/-- [P1 · ①表] (1, s) 自环步（next = 1）读数据位。 -/
lemma transition_one_nexteq1_kind (s : Sym) :
    ∀ r ∈ VerifierSym.transition ((1 : ℕ), s), r.nextState = 1 →
      (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) := by
  obtain ⟨k, m⟩ := s
  cases m <;> cases k <;> decide

/-- [P1 · ①表] (2, s) 自环步（next = 2）读非 #。 -/
lemma transition_two_nexteq2_kind (s : Sym) :
    ∀ r ∈ VerifierSym.transition ((2 : ℕ), s), r.nextState = 2 → s.1 ≠ SymKind.boundary := by
  obtain ⟨k, m⟩ := s
  cases m <;> cases k <;> decide

/-- [P1 · ①表] 2 的进入：从 1 读 #，或 2 自环。 -/
lemma transition_two_entry (s : Sym) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), s),
      r.nextState = 2 → (((q : ℕ) = 1 ∧ s.1 = SymKind.boundary) ∨ (q : ℕ) = 2) := by
  obtain ⟨k, m⟩ := s
  cases m <;> cases k <;> decide

/-- [P1 · ①输入] 元素编码的符号型：α 或数据位。 -/
lemma encodeElementsSym_kinds (elems : List ℕ) :
    ∀ s ∈ encodeElementsSym elems,
      s = Sym.alpha ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
  induction elems with
  | nil =>
      intro s hs
      simp [encodeElementsSym] at hs
  | cons v rest ih =>
      intro s hs
      cases hrest : rest with
      | nil =>
          simp [hrest, encodeElementsSym] at hs
          rcases hs with h | h
          · left
            exact h
          · rcases encodeBitsSymNative_nonboundary v s h with h0 | h1
            · exact Or.inr (Or.inl h0)
            · exact Or.inr (Or.inr h1)
      | cons w rest' =>
          simp [hrest, encodeElementsSym] at hs
          rcases hs with h | h | h
          · left
            exact h
          · rcases encodeBitsSymNative_nonboundary v s h with h0 | h1
            · exact Or.inr (Or.inl h0)
            · exact Or.inr (Or.inr h1)
          · rw [← hrest] at h
            exact ih s h

/-- [P1 · ①表] (1, s) 读数据位 ⟹ next = 1。 -/
lemma transition_one_data_next (s : Sym) (hs : s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) :
    ∀ r ∈ VerifierSym.transition ((1 : ℕ), s), r.nextState = 1 := by
  obtain ⟨k, m⟩ := s
  rcases hs with h | h
  · cases h
    cases m <;> decide
  · cases h
    cases m <;> decide

/-- [P1 · ①表] (1, s) 读 #（kind）⟹ next = 2。 -/
lemma transition_one_hash_next (s : Sym) (hs : s.1 = SymKind.boundary) :
    ∀ r ∈ VerifierSym.transition ((1 : ℕ), s), r.nextState = 2 := by
  obtain ⟨k, m⟩ := s
  cases hs
  cases m <;> decide

/-- [P1 · ①表] (2, s) 读安全型（数据位 kind / 纯 α）⟹ next = 2。 -/
lemma transition_two_safe_next (s : Sym)
    (hs : s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s = Sym.alpha) :
    ∀ r ∈ VerifierSym.transition ((2 : ℕ), s), r.nextState = 2 := by
  obtain ⟨k, m⟩ := s
  rcases hs with h | h | h
  · cases h
    cases m <;> decide
  · cases h
    cases m <;> decide
  · cases h
    decide

/-- [P1 · ①输入] 初始带六段结构：0=#；[1,1+tb) 数据；#@1+tb；[2+tb,2+tb+eb) α/数据；#@2+tb+eb；其后 blank。 -/
lemma inst_tape_struct (inst : SubsetSumInstance) :
    let tape := (symInitialConfig (encodeInstanceSym inst)).tape
    tape 0 = Sym.boundary ∧
    (∀ j : ℤ, 1 ≤ j → j < 1 + ((encodeBitsSym inst.target).length : ℤ) →
      (tape j).1 = SymKind.data0 ∨ (tape j).1 = SymKind.data1) ∧
    tape (1 + ((encodeBitsSym inst.target).length : ℤ)) = Sym.boundary ∧
    (∀ j : ℤ, 2 + ((encodeBitsSym inst.target).length : ℤ) ≤ j →
      j < 2 + ((encodeBitsSym inst.target).length : ℤ) +
        ((encodeElementsSym inst.elements).length : ℤ) →
      tape j = Sym.alpha ∨ (tape j).1 = SymKind.data0 ∨ (tape j).1 = SymKind.data1) ∧
    tape (2 + ((encodeBitsSym inst.target).length : ℤ) +
      ((encodeElementsSym inst.elements).length : ℤ)) = Sym.boundary ∧
    (∀ j : ℤ, 2 + ((encodeBitsSym inst.target).length : ℤ) +
      ((encodeElementsSym inst.elements).length : ℤ) < j →
      (tape j).1 = SymKind.data0 ∨ (tape j).1 = SymKind.data1) := by
  let tb := encodeBitsSym inst.target
  let eb := encodeElementsSym inst.elements
  let tape := (symInitialConfig (encodeInstanceSym inst)).tape
  have htape0 : tapeAgrees tape 0 (encodeInstanceSym inst) :=
    symInitialConfig_tapeAgrees (encodeInstanceSym inst)
  have htapeA : tapeAgrees tape 0
      ([Sym.boundary] ++ (tb ++ ([Sym.boundary] ++ (eb ++ [Sym.boundary])))) := by
    simpa [encodeInstanceSym, tb, eb] using htape0
  have hsplit1 := (tapeAgrees_append tape 0 [Sym.boundary]
    (tb ++ ([Sym.boundary] ++ (eb ++ [Sym.boundary])))).mp htapeA
  have hb_l : tape 0 = Sym.boundary := ((tapeAgrees_cons tape 0 Sym.boundary []).mp hsplit1.1).1
  have htape1 : tapeAgrees tape 1 (tb ++ ([Sym.boundary] ++ (eb ++ [Sym.boundary]))) := by
    simpa using hsplit1.2
  have hsplit2 := (tapeAgrees_append tape 1 tb ([Sym.boundary] ++ (eb ++ [Sym.boundary]))).mp htape1
  have ht_tb : tapeAgrees tape 1 tb := hsplit2.1
  have hsplit3 := (tapeAgrees_cons tape (1 + (tb.length : ℤ)) Sym.boundary (eb ++ [Sym.boundary])).mp hsplit2.2
  have hb_0 : tape (1 + (tb.length : ℤ)) = Sym.boundary := hsplit3.1
  have hsplit4 := (tapeAgrees_append tape ((1 + (tb.length : ℤ)) + 1) eb [Sym.boundary]).mp hsplit3.2
  have hoff : (1 + (tb.length : ℤ)) + 1 = 2 + (tb.length : ℤ) := by ring
  have hoff2 : ((1 + (tb.length : ℤ)) + 1) + (eb.length : ℤ) =
      (2 + (tb.length : ℤ)) + (eb.length : ℤ) := by ring
  have helems0 : tapeAgrees tape (2 + (tb.length : ℤ)) eb := by
    rw [← hoff]
    exact hsplit4.1
  have hb1 : tape (2 + (tb.length : ℤ) + (eb.length : ℤ)) = Sym.boundary := by
    rw [← hoff2]
    exact ((tapeAgrees_cons tape (((1 + (tb.length : ℤ)) + 1) + (eb.length : ℤ))
      Sym.boundary []).mp hsplit4.2).1
  refine ⟨hb_l, ?_, hb_0, ?_, hb1, ?_⟩
  · intro j hj1 hj2
    change j < 1 + (tb.length : ℤ) at hj2
    change (tape j).1 = SymKind.data0 ∨ (tape j).1 = SymKind.data1
    have hio : ∃ io : ℕ, (io : ℤ) = j - 1 := ⟨(j - 1).toNat, Int.toNat_of_nonneg (by omega)⟩
    rcases hio with ⟨io, hio⟩
    have hio_lt : io < tb.length := by
      have h2 : (io : ℤ) < (tb.length : ℤ) := by omega
      exact_mod_cast h2
    have ht : tape (1 + (io : ℤ)) = tb[io] := ht_tb io hio_lt
    have hidx : 1 + (io : ℤ) = j := by omega
    have heq : tape j = tb[io] := by
      rw [← hidx]
      exact ht
    rw [heq]
    exact encodeBitsSym_nonboundary inst.target tb[io] (List.getElem_mem hio_lt)
  · intro j hj1 hj2
    change 2 + (tb.length : ℤ) ≤ j at hj1
    change j < 2 + (tb.length : ℤ) + (eb.length : ℤ) at hj2
    change tape j = Sym.alpha ∨ (tape j).1 = SymKind.data0 ∨ (tape j).1 = SymKind.data1
    have hio : ∃ io : ℕ, (io : ℤ) = j - (2 + (tb.length : ℤ)) :=
      ⟨_, Int.toNat_of_nonneg (by omega)⟩
    rcases hio with ⟨io, hio⟩
    have hio_lt : io < eb.length := by
      have h2 : (io : ℤ) < (eb.length : ℤ) := by omega
      exact_mod_cast h2
    have ht : tape ((2 + (tb.length : ℤ)) + (io : ℤ)) = eb[io] := helems0 io hio_lt
    have hidx : (2 + (tb.length : ℤ)) + (io : ℤ) = j := by omega
    have heq : tape j = eb[io] := by
      rw [← hidx]
      exact ht
    rw [heq]
    exact encodeElementsSym_kinds inst.elements eb[io] (List.getElem_mem hio_lt)
  · intro j hj
    change 2 + (tb.length : ℤ) + (eb.length : ℤ) < j at hj
    change (tape j).1 = SymKind.data0 ∨ (tape j).1 = SymKind.data1
    have hlen : (encodeInstanceSym inst).length = 2 + tb.length + eb.length + 1 := by
      simp [encodeInstanceSym, tb, eb]
      ring
    have hge : (encodeInstanceSym inst).length ≤ j.toNat := by
      rw [hlen]
      exact (Int.le_toNat (by omega : (0 : ℤ) ≤ j)).mpr (by
        have hj' : 2 + (tb.length : ℤ) + (eb.length : ℤ) + 1 ≤ j := by omega
        push_cast
        exact hj')
    have hout : tape j = Sym.blank := by
      show (symInitialConfig (encodeInstanceSym inst)).tape j = Sym.blank
      simp only [symInitialConfig]
      rw [dif_neg]
      intro hcon
      exact absurd hcon.2 (by omega)
    rw [hout]
    exact Or.inl rfl


/-! ========== P1 · ①带模式不变量（T-P1.5d） ========== -/

/-- [P1 · ①带模式] 自 (0, tape, 0) 的全 R、后继∈{1,2} 运行：头位 = 步数，且状态按步数分段
    （0 / 1 …1 / 2 …2；三段由输入带六段结构决定）。 -/
lemma run_alpha_inv {tb eb : ℕ} {tape : ℤ → Sym}
    (h0 : tape 0 = Sym.boundary)
    (hb : ∀ j : ℤ, 1 ≤ j → j < 1 + (tb : ℤ) →
      (tape j).1 = SymKind.data0 ∨ (tape j).1 = SymKind.data1)
    (h10 : tape (1 + (tb : ℤ)) = Sym.boundary)
    (he : ∀ j : ℤ, 2 + (tb : ℤ) ≤ j → j < 2 + (tb : ℤ) + (eb : ℤ) →
      tape j = Sym.alpha ∨ (tape j).1 = SymKind.data0 ∨ (tape j).1 = SymKind.data1)
    (h11 : tape (2 + (tb : ℤ) + (eb : ℤ)) = Sym.boundary)
    (hbe : ∀ j : ℤ, 2 + (tb : ℤ) + (eb : ℤ) < j →
      (tape j).1 = SymKind.data0 ∨ (tape j).1 = SymKind.data1) :
    ∀ {π : List SymStep} {cfg : SymConfig},
      SymSteps VerifierSym.transition (SymConfig.mk 0 tape 0) π cfg →
      (∀ s ∈ π, s.result.moveDir = Dir.R) →
      (∀ s ∈ π, s.result.nextState ∈ [1, 2]) →
      cfg.headPos = (π.length : ℤ) ∧
      ((π.length = 0 → cfg.state = 0) ∧
       (1 ≤ π.length ∧ π.length ≤ tb + 1 → cfg.state = 1) ∧
       (tb + 2 ≤ π.length → cfg.state = 2)) := by
  intro π cfg h
  induction h with
  | nil =>
      intro _ _
      refine ⟨by simp, ?_, ?_, ?_⟩
      · intro _
        rfl
      · intro ⟨h1, _⟩
        exact absurd h1 (by simp)
      · intro h3
        exact absurd h3 (by simp)
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro hR hnext
      have hR₀ : ∀ s ∈ π₀, s.result.moveDir = Dir.R :=
        fun s hs => hR s (by rw [List.mem_append]; left; exact hs)
      have hnext₀ : ∀ s ∈ π₀, s.result.nextState ∈ [1, 2] :=
        fun s hs => hnext s (by rw [List.mem_append]; left; exact hs)
      obtain ⟨ihhead, ihs0, ihs1, ihs2⟩ := ih hR₀ hnext₀
      have hRstep : step.result.moveDir = Dir.R := hR step (by simp)
      have hmemr : step.result ∈ VerifierSym.transition (cfg₁.state, step.readSym) := by
        rw [hread]
        exact htrans
      have hread0 : step.readSym = tape (π₀.length : ℤ) := by
        have h1 := run_tape_high_agree hprev hR₀ cfg₁.headPos le_rfl
        rw [hread, h1, ihhead]
      have hlen1 : (π₀ ++ [step]).length = π₀.length + 1 := by simp
      have hlenZ : ((π₀ ++ [step]).length : ℤ) = (π₀.length : ℤ) + 1 := by
        rw [hlen1]; push_cast; ring
      -- 步后继分类
      have hcases : (π₀.length = 0 ∧ step.result.nextState = 1) ∨
          (1 ≤ π₀.length ∧ π₀.length + 1 ≤ tb + 1 ∧ step.result.nextState = 1) ∨
          (π₀.length = tb + 1 ∧ step.result.nextState = 2) ∨
          (tb + 2 ≤ π₀.length ∧ step.result.nextState = 2) := by
        by_cases hz : π₀.length = 0
        · left
          refine ⟨hz, ?_⟩
          have hst : cfg₁.state = 0 := ihs0 hz
          have hreadB : step.readSym = Sym.boundary := by
            rw [hread0, hz]
            exact h0
          have hm : step.result ∈ VerifierSym.transition (0, Sym.boundary) := by
            rw [hst, hreadB] at hmemr
            exact hmemr
          exact (transition_zero_boundary step.result hm).1
        · by_cases hle : π₀.length ≤ tb
          · right; left
            refine ⟨by omega, by omega, ?_⟩
            have hst : cfg₁.state = 1 := ihs1 ⟨by omega, by omega⟩
            have hk := hb (π₀.length : ℤ) (by omega) (by omega)
            have hkind : step.readSym.1 = SymKind.data0 ∨ step.readSym.1 = SymKind.data1 := by
              rw [hread0]
              exact hk
            have hm : step.result ∈ VerifierSym.transition (1, step.readSym) := by
              rw [hst] at hmemr
              exact hmemr
            exact transition_one_data_next step.readSym hkind step.result hm
          · by_cases he1 : π₀.length = tb + 1
            · right; right; left
              refine ⟨he1, ?_⟩
              have hst : cfg₁.state = 1 := ihs1 ⟨by omega, by omega⟩
              have hreadB : step.readSym = Sym.boundary := by
                rw [hread0, show (π₀.length : ℤ) = 1 + (tb : ℤ) from by omega]
                exact h10
              have hm : step.result ∈ VerifierSym.transition (1, step.readSym) := by
                rw [hst] at hmemr
                exact hmemr
              exact transition_one_hash_next step.readSym (by rw [hreadB]; rfl) step.result hm
            · right; right; right
              have hge : tb + 2 ≤ π₀.length := by omega
              refine ⟨hge, ?_⟩
              have hst : cfg₁.state = 2 := ihs2 hge
              by_cases himp : π₀.length = 2 + tb + eb
              · exfalso
                have hreadB : step.readSym = Sym.boundary := by
                  rw [hread0, show (π₀.length : ℤ) = 2 + (tb : ℤ) + (eb : ℤ) from by omega]
                  exact h11
                have hm : step.result ∈ VerifierSym.transition (2, Sym.boundary) := by
                  rw [hst, hreadB] at hmemr
                  exact hmemr
                have h3 := (transition_two_boundary step.result hm).1
                have h12 := hnext step (by simp)
                rw [h3] at h12
                exact absurd h12 (by decide)
              · rcases lt_or_gt_of_ne himp with hlt | hgt
                · have hk := he (π₀.length : ℤ) (by omega) (by omega)
                  have hkind : step.readSym.1 = SymKind.data0 ∨ step.readSym.1 = SymKind.data1 ∨
                      step.readSym = Sym.alpha := by
                    rw [hread0]
                    rcases hk with h | h | h
                    · right; right
                      exact h
                    · left; exact h
                    · right; left; exact h
                  have hm : step.result ∈ VerifierSym.transition (2, step.readSym) := by
                    rw [hst] at hmemr
                    exact hmemr
                  exact transition_two_safe_next step.readSym hkind step.result hm
                · have hk := hbe (π₀.length : ℤ) (by omega)
                  have hkind : step.readSym.1 = SymKind.data0 ∨ step.readSym.1 = SymKind.data1 ∨
                      step.readSym = Sym.alpha := by
                    rw [hread0]
                    rcases hk with h | h
                    · left; exact h
                    · right; left; exact h
                  have hm : step.result ∈ VerifierSym.transition (2, step.readSym) := by
                    rw [hst] at hmemr
                    exact hmemr
                  exact transition_two_safe_next step.readSym hkind step.result hm
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- 头位 = 步数
        rw [show (symStepConfig cfg₁ step.result).headPos = cfg₁.headPos + 1 from by
          simp [symStepConfig, hRstep, Dir.toInt]]
        rw [ihhead]
        rw [hlenZ]
      · -- 步数 = 0 → 状态 0
        intro hcon
        exact absurd hcon (by omega)
      · -- 1 ≤ 步数 ≤ tb+1 → 状态 1
        intro ⟨h1', h2'⟩
        rcases hcases with ⟨_, hn⟩ | ⟨_, _, hn⟩ | ⟨he1', _⟩ | ⟨hge', _⟩
        · simpa [symStepConfig] using hn
        · simpa [symStepConfig] using hn
        · omega
        · omega
      · -- tb+2 ≤ 步数 → 状态 2
        intro h3'
        rcases hcases with ⟨hz', _⟩ | ⟨_, _, _⟩ | ⟨_, hn⟩ | ⟨_, hn⟩
        · omega
        · omega
        · simpa [symStepConfig] using hn
        · simpa [symStepConfig] using hn

/-! ========== P1 · ①长界（T-P1.5d 收官） ========== -/

/-- [P1 · ①长界] 接受运行首段（α 段）刻画：切点定长 `|π₀| = 2+|tb|+|eb|`（= |tb|+|eb|+2），
    切点读值 = 初始带在该处之值，头位以上区域带面不动（写只发生在已过头位）。 -/
lemma run_alpha_len {inst : SubsetSumInstance} {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π cfg)
    (hacc : cfg.state = 100) :
    ∃ (π₀ : List SymStep) (step₃ : SymStep) (π₁ : List SymStep) (cfgm : SymConfig),
      π = π₀ ++ step₃ :: π₁ ∧
      (π₀.length : ℤ) = 2 + ((encodeBitsSym inst.target).length : ℤ) +
        ((encodeElementsSym inst.elements).length : ℤ) ∧
      cfgm.headPos = (π₀.length : ℤ) ∧
      step₃.fromState = 2 ∧ step₃.result.nextState = 3 ∧
      step₃.readSym = (symInitialConfig (encodeInstanceSym inst)).tape (π₀.length : ℤ) ∧
      (∀ j : ℤ, (π₀.length : ℤ) ≤ j →
        cfgm.tape j = (symInitialConfig (encodeInstanceSym inst)).tape j) ∧
      (∀ s ∈ π₀, s.result.moveDir = Dir.R) ∧
      (∀ s ∈ π₀, s.result.nextState ∈ [1, 2]) ∧
      SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π₀ cfgm := by
  obtain ⟨π₀, step₃, π₁, cfgm, hsplit, hp3, hfrom3, hq2v, hkind3, hclean, hrun, hnexts, hR, hfroms, hhead⟩ :=
    run_carve h hacc
  obtain ⟨h0, hb, h10, he, h11, hbe⟩ := inst_tape_struct inst
  obtain ⟨hinvhead, hinv0, hinv1, hinv2⟩ := run_alpha_inv h0 hb h10 he h11 hbe hrun hR hnexts
  -- 读链：拆 h 取 π₀ 终点运行 c 与 step₃ 单步事实
  have h' : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst))
      (π₀ ++ ([step₃] ++ π₁)) cfg := by
    rw [hsplit] at h
    simpa [List.cons_append] using h
  obtain ⟨c, hmid, htail⟩ := symSteps_append_split (π₀ := π₀) (rest := [step₃] ++ π₁) h'
  obtain ⟨c', hs₁, _hr⟩ := symSteps_append_split (π₀ := [step₃]) (rest := π₁) htail
  obtain ⟨_hsfrom, hsread, _hsmem, _⟩ := symSteps_singleton_facts hs₁
  have hchead : c.headPos = (π₀.length : ℤ) := by
    have := head_eq_of_all_right VerifierSym.transition hmid hR
    simpa [symInitialConfig, SymConfig.mk] using this
  have hcread : step₃.readSym = (symInitialConfig (encodeInstanceSym inst)).tape
      (π₀.length : ℤ) := by
    have hag := run_tape_high_agree hmid hR c.headPos le_rfl
    rw [hsread, hag, hchead]
  -- 边界型位置刻画：tape₀ 的 # 位恰为 {0, 1+|tb|, 2+|tb|+|eb|}
  have hbound : ∀ j : ℤ, 0 ≤ j →
      ((symInitialConfig (encodeInstanceSym inst)).tape j).1 = SymKind.boundary →
      j = 0 ∨ j = 1 + ((encodeBitsSym inst.target).length : ℤ) ∨
      j = 2 + ((encodeBitsSym inst.target).length : ℤ) +
        ((encodeElementsSym inst.elements).length : ℤ) := by
    intro j hj0 hkj
    by_cases hj1 : j = 0
    · exact Or.inl hj1
    · right
      have hj1' : 1 ≤ j := by omega
      by_cases hb1 : j < 1 + ((encodeBitsSym inst.target).length : ℤ)
      · exfalso
        rcases hb j hj1' hb1 with hd | hd <;> (rw [hkj] at hd; exact absurd hd (by decide))
      · by_cases hb2 : j = 1 + ((encodeBitsSym inst.target).length : ℤ)
        · exact Or.inl hb2
        · right
          have hj2 : 2 + ((encodeBitsSym inst.target).length : ℤ) ≤ j := by omega
          by_cases hb3 : j < 2 + ((encodeBitsSym inst.target).length : ℤ) +
              ((encodeElementsSym inst.elements).length : ℤ)
          · exfalso
            rcases he j hj2 hb3 with hd | hd | hd
            · rw [hd] at hkj
              exact absurd hkj (by decide)
            · rw [hkj] at hd
              exact absurd hd (by decide)
            · rw [hkj] at hd
              exact absurd hd (by decide)
          · by_cases hb4 : j = 2 + ((encodeBitsSym inst.target).length : ℤ) +
                ((encodeElementsSym inst.elements).length : ℤ)
            · exact hb4
            · exfalso
              rcases hbe j (by omega) with hd | hd <;> (rw [hkj] at hd; exact absurd hd (by decide))
  -- π₀ 非空（终态 = 2 ≠ 0）
  have hne : π₀ ≠ [] := by
    intro hnil
    have hc : cfgm = symInitialConfig (encodeInstanceSym inst) :=
      symSteps_nil_cfg (by rwa [hnil] at hrun)
    rw [hc] at hq2v
    simp [symInitialConfig] at hq2v
  have hlenPos : 1 ≤ π₀.length := by
    rcases π₀ with _ | ⟨s, rest⟩
    · exact absurd rfl hne
    · simp
  -- |π₀| ≠ 1+|tb|（否则状态 = 1，与终态 2 矛盾）
  have hneTb : (π₀.length : ℤ) ≠ 1 + ((encodeBitsSym inst.target).length : ℤ) := by
    intro hcon
    have hst1 : cfgm.state = 1 := hinv1 ⟨by omega, by omega⟩
    omega
  have hkindT : ((symInitialConfig (encodeInstanceSym inst)).tape (π₀.length : ℤ)).1 =
      SymKind.boundary := by
    rw [← hcread]
    exact hkind3
  have hpos := hbound (π₀.length : ℤ) (by omega) hkindT
  have hlenEq : (π₀.length : ℤ) = 2 + ((encodeBitsSym inst.target).length : ℤ) +
      ((encodeElementsSym inst.elements).length : ℤ) := by
    rcases hpos with h0' | h1tb | heq2
    · omega
    · exact absurd h1tb hneTb
    · exact heq2
  have hface : ∀ j : ℤ, (π₀.length : ℤ) ≤ j →
      cfgm.tape j = (symInitialConfig (encodeInstanceSym inst)).tape j := by
    intro j hj
    exact run_tape_high_agree hrun hR j (by rw [hhead]; exact hj)
  exact ⟨π₀, step₃, π₁, cfgm, hsplit, hlenEq, hhead, hfrom3, hp3, hcread, hface, hR, hnexts, hrun⟩

/-! ========== P1 · ①面提取（T-P1.6 基础） ========== -/

/-- [P1 · ①面提取] 全 R 运行：第 i 步所过之格（初始头 + i）的值 = 第 i 步的写入符号。 -/
lemma run_tape_written {M : ℕ × Sym → Finset SymTransResult} :
    ∀ {cfg₀ cfg : SymConfig} {π : List SymStep}, SymSteps M cfg₀ π cfg →
      (∀ s ∈ π, s.result.moveDir = Dir.R) →
      ∀ (i : ℕ) (hi : i < π.length),
        cfg.tape (cfg₀.headPos + (i : ℤ)) = (π.get ⟨i, hi⟩).result.writeSym := by
  intro cfg₀ cfg π h
  induction h with
  | nil =>
      intro _ i hi
      simp at hi
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro hR i hi
      have hRstep : step.result.moveDir = Dir.R := hR step (by simp)
      have hR₀ : ∀ s ∈ π₀, s.result.moveDir = Dir.R :=
        fun s hs => hR s (by rw [List.mem_append]; left; exact hs)
      have hhead₁ : cfg₁.headPos = cfg₀.headPos + (π₀.length : ℤ) :=
        head_eq_of_all_right M hprev hR₀
      by_cases hlt : i < π₀.length
      · have ih' := ih hR₀ i hlt
        have hget : (π₀ ++ [step]).get ⟨i, hi⟩ = π₀.get ⟨i, hlt⟩ :=
          List.getElem_append_left hlt
        rw [hget, ← ih']
        simp only [symStepConfig]
        rw [if_neg (by omega : ¬(cfg₀.headPos + (i : ℤ) = cfg₁.headPos))]
      · have hie : i = π₀.length := by
          have h2 : (π₀ ++ [step]).length = π₀.length + 1 := by simp
          omega
        subst hie
        have hget : (π₀ ++ [step]).get ⟨π₀.length, hi⟩ = step := by
          have h1 := List.getLast_eq_getElem (l := π₀ ++ [step]) (h := by simp)
          have h2 : (π₀ ++ [step]).get ⟨π₀.length, hi⟩ =
              (π₀ ++ [step]).getLast (by simp) := by
            rw [h1]
            congr 1
            apply Fin.ext
            simp
          rw [h2]
          simpa only [List.concat_eq_append] using List.getLast_concat' π₀
        rw [hget]
        simp only [symStepConfig]
        rw [if_pos (by omega : cfg₀.headPos + (π₀.length : ℤ) = cfg₁.headPos)]

/-- [P1 · ①写分类] (0/1/2) 态读边界/数据位/α 位：除 (2, α) 分支外写 = 读。 -/
lemma transition_alpha_write (q : ℕ) (hq : q = 0 ∨ q = 1 ∨ q = 2) (s : Sym)
    (hs : s = Sym.boundary ∨ s = Sym.data0 ∨ s = Sym.data1 ∨ s = Sym.alpha)
    (r : SymTransResult) (hm : r ∈ VerifierSym.transition (q, s)) :
    r.writeSym = s ∨ (q = 2 ∧ s = Sym.alpha ∧ (r.writeSym = Sym.sel ∨ r.writeSym = Sym.nosel)) := by
  rcases hq with rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl | rfl <;>
    (first
      | (left; revert r; decide)
      | (right; refine ⟨rfl, rfl, ?_⟩; revert r; decide))


/-! ========== T-P1.7 移植（线2 探针，15:50 吸收包；逐字复制） ========== -/

/-- [草案命名] 逐元素段界：`el(b,p) = b(2b+2p+3) + (4p+4b+13)`（= `foldLenB` 单元素项）。 -/
def el (b : ℕ) (p : ℤ) : ℤ :=
  (b : ℤ) * (2 * (b : ℤ) + 2 * p + 3) + (4 * p + 4 * (b : ℤ) + 13)

/-- [缝 · 命名对齐] `el` 与 `foldLenB [b]` 逐字一致。 -/
lemma el_eq_foldLenB_single (b : ℕ) (p : ℤ) : el b p = foldLenB [b] p := by
  simp [el, foldLenB_single]

/-- [缝 · 统一 cons 递归] `foldLenB (b :: rest) p = el b p + foldLenB rest (p + b + 1)`
    （库中仅有 `_nil/_single/_cons_cons` 三条 simp 引理；此件为 fold 归纳主件，
    `rest` 空/非空统一，无需在递归里手工分派 cons_cons）。 -/
lemma foldLenB_cons (b : ℕ) (rest : List ℕ) (p : ℤ) :
    foldLenB (b :: rest) p = el b p + foldLenB rest (p + (b : ℤ) + 1) := by
  cases rest with
  | nil => simp [el]
  | cons c t => simp [el, foldLenB_cons_cons]

/-- [T-P3.3 · nosel 半] nosel 段界 `b+5` ≤ `el(b,p)`（`0 ≤ p`）。 -/
lemma nosel_bound_le_el (b : ℕ) (p : ℤ) (hp : 0 ≤ p) :
    (b : ℤ) + 5 ≤ el b p := by
  have hb : (0 : ℤ) ≤ (b : ℤ) := Int.natCast_nonneg b
  have h25 : (0 : ℤ) ≤ 2 * (b : ℤ) + 2 * p + 3 := by omega
  have hmul : 0 ≤ (b : ℤ) * (2 * (b : ℤ) + 2 * p + 3) := mul_nonneg hb h25
  simp only [el]
  omega

/-- [T-P3.3 草案] 任一路线段 ≤ `el`：sel 支 = `el` 本身；nosel 支 = `b+5 ≤ el`。
    Bool 索引形对应 fold 内「按标记 by_cases 分派」的消费形。 -/
lemma route_le_el (b : ℕ) (p : ℤ) (hp : 0 ≤ p) (sel : Bool) :
    (if sel then el b p else (b : ℤ) + 5) ≤ el b p := by
  by_cases h : sel
  · simp [h]
  · simp [h]
    exact nosel_bound_le_el b p hp

/-- [P2 · 放宽口径备用] `el` 关于 p 单调（系数 `2b+4 ≥ 0`）。 -/
lemma el_mono_p (b : ℕ) {p p' : ℤ} (h : p ≤ p') : el b p ≤ el b p' := by
  have hb : (0 : ℤ) ≤ (b : ℤ) := Int.natCast_nonneg b
  simp only [el]
  nlinarith [hb, h, sq_nonneg ((b : ℤ) + 2)]

/-! ========== P1 · ①面提取：步访问器（T-P1.6） ========== -/

/-- [P1 · ①面提取] 步 i 的来态 = 前 i 步运行（`take`）终点状态。 -/
lemma run_fromState_at {M : ℕ × Sym → Finset SymTransResult} :
    ∀ {cfg₀ cfg : SymConfig} {π : List SymStep}, SymSteps M cfg₀ π cfg →
      ∀ (i : ℕ) (hi : i < π.length),
        ∃ (cfgᵢ : SymConfig), SymSteps M cfg₀ (π.take i) cfgᵢ ∧
          (π.get ⟨i, hi⟩).fromState = cfgᵢ.state := by
  intro cfg₀ cfg π h
  induction h with
  | nil =>
      intro i hi
      simp at hi
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro i hi
      by_cases hlt : i < π₀.length
      · obtain ⟨cfgᵢ, hrunᵢ, hfromᵢ⟩ := ih i hlt
        refine ⟨cfgᵢ, ?_, ?_⟩
        · rw [List.take_append_of_le_length (by omega : i ≤ π₀.length)]
          exact hrunᵢ
        · have hget : (π₀ ++ [step]).get ⟨i, hi⟩ = π₀.get ⟨i, hlt⟩ :=
            List.getElem_append_left hlt
          rw [hget]
          exact hfromᵢ
      · have hie : i = π₀.length := by
          have h2 : (π₀ ++ [step]).length = π₀.length + 1 := by simp
          omega
        subst hie
        refine ⟨cfg₁, ?_, ?_⟩
        · rw [List.take_append_of_le_length (Nat.le_refl π₀.length), List.take_length]
          exact hprev
        · have hget : (π₀ ++ [step]).get ⟨π₀.length, hi⟩ = step := by
            have h1 := List.getLast_eq_getElem (l := π₀ ++ [step]) (h := by simp)
            have h2 : (π₀ ++ [step]).get ⟨π₀.length, hi⟩ =
                (π₀ ++ [step]).getLast (by simp) := by
              rw [h1]
              congr 1
              apply Fin.ext
              simp
            rw [h2]
            simpa only [List.concat_eq_append] using List.getLast_concat' π₀
          rw [hget]
          exact hfrom

/-- [P1 · ①面提取] 元素区（步号 ≥ tb+2）每步来态 = 2。 -/
lemma run_alpha_state2 {tb eb : ℕ} {tape : ℤ → Sym}
    (h0 : tape 0 = Sym.boundary)
    (hb : ∀ j : ℤ, 1 ≤ j → j < 1 + (tb : ℤ) →
      (tape j).1 = SymKind.data0 ∨ (tape j).1 = SymKind.data1)
    (h10 : tape (1 + (tb : ℤ)) = Sym.boundary)
    (he : ∀ j : ℤ, 2 + (tb : ℤ) ≤ j → j < 2 + (tb : ℤ) + (eb : ℤ) →
      tape j = Sym.alpha ∨ (tape j).1 = SymKind.data0 ∨ (tape j).1 = SymKind.data1)
    (h11 : tape (2 + (tb : ℤ) + (eb : ℤ)) = Sym.boundary)
    (hbe : ∀ j : ℤ, 2 + (tb : ℤ) + (eb : ℤ) < j →
      (tape j).1 = SymKind.data0 ∨ (tape j).1 = SymKind.data1) :
    ∀ {π : List SymStep} {cfg : SymConfig},
      SymSteps VerifierSym.transition (SymConfig.mk 0 tape 0) π cfg →
      (∀ s ∈ π, s.result.moveDir = Dir.R) →
      (∀ s ∈ π, s.result.nextState ∈ [1, 2]) →
      ∀ (i : ℕ) (hi : i < π.length), tb + 2 ≤ i →
        (π.get ⟨i, hi⟩).fromState = 2 := by
  intro π cfg hrun hR hnexts i hi hge
  obtain ⟨cfgᵢ, hrunᵢ, hfromᵢ⟩ := run_fromState_at hrun i hi
  have hRᵢ : ∀ s ∈ π.take i, s.result.moveDir = Dir.R :=
    fun s hs => hR s (List.mem_of_mem_take hs)
  have hnextᵢ : ∀ s ∈ π.take i, s.result.nextState ∈ [1, 2] :=
    fun s hs => hnexts s (List.mem_of_mem_take hs)
  obtain ⟨_, _, _, hinv2⟩ := run_alpha_inv h0 hb h10 he h11 hbe hrunᵢ hRᵢ hnextᵢ
  have htake : (π.take i).length = i := by
    rw [List.length_take]
    omega
  rw [hfromᵢ]
  exact hinv2 (by omega)

/-- [P1 · ①面提取] 每步来态 ∈ {0, 1, 2}。 -/
lemma run_alpha_state_le2 {tb eb : ℕ} {tape : ℤ → Sym}
    (h0 : tape 0 = Sym.boundary)
    (hb : ∀ j : ℤ, 1 ≤ j → j < 1 + (tb : ℤ) →
      (tape j).1 = SymKind.data0 ∨ (tape j).1 = SymKind.data1)
    (h10 : tape (1 + (tb : ℤ)) = Sym.boundary)
    (he : ∀ j : ℤ, 2 + (tb : ℤ) ≤ j → j < 2 + (tb : ℤ) + (eb : ℤ) →
      tape j = Sym.alpha ∨ (tape j).1 = SymKind.data0 ∨ (tape j).1 = SymKind.data1)
    (h11 : tape (2 + (tb : ℤ) + (eb : ℤ)) = Sym.boundary)
    (hbe : ∀ j : ℤ, 2 + (tb : ℤ) + (eb : ℤ) < j →
      (tape j).1 = SymKind.data0 ∨ (tape j).1 = SymKind.data1) :
    ∀ {π : List SymStep} {cfg : SymConfig},
      SymSteps VerifierSym.transition (SymConfig.mk 0 tape 0) π cfg →
      (∀ s ∈ π, s.result.moveDir = Dir.R) →
      (∀ s ∈ π, s.result.nextState ∈ [1, 2]) →
      ∀ (i : ℕ) (hi : i < π.length),
        (π.get ⟨i, hi⟩).fromState = 0 ∨ (π.get ⟨i, hi⟩).fromState = 1 ∨
          (π.get ⟨i, hi⟩).fromState = 2 := by
  intro π cfg hrun hR hnexts i hi
  obtain ⟨cfgᵢ, hrunᵢ, hfromᵢ⟩ := run_fromState_at hrun i hi
  have hRᵢ : ∀ s ∈ π.take i, s.result.moveDir = Dir.R :=
    fun s hs => hR s (List.mem_of_mem_take hs)
  have hnextᵢ : ∀ s ∈ π.take i, s.result.nextState ∈ [1, 2] :=
    fun s hs => hnexts s (List.mem_of_mem_take hs)
  obtain ⟨_, hinv0, hinv1, hinv2⟩ := run_alpha_inv h0 hb h10 he h11 hbe hrunᵢ hRᵢ hnextᵢ
  have htake : (π.take i).length = i := by
    rw [List.length_take]
    omega
  rw [hfromᵢ]
  by_cases hz : i = 0
  · subst hz
    have hnil : cfgᵢ = SymConfig.mk 0 tape 0 := symSteps_nil_cfg (by simpa using hrunᵢ)
    rw [hnil]
    simp
  · by_cases hle : i ≤ tb + 1
    · have h1 : cfgᵢ.state = 1 := hinv1 ⟨by omega, by omega⟩
      rw [h1]
      simp
    · have h2 : cfgᵢ.state = 2 := hinv2 (by omega)
      rw [h2]
      simp

/-! ========== P1 · ①面提取：编码条目与带面本体（T-P1.6） ========== -/

/-- [P1 · ①面提取] `encodeBitsSym` 条目恰为 data0/data1（精确符号）。 -/
lemma encodeBitsSym_entries (n : ℕ) : ∀ s ∈ encodeBitsSym n, s = Sym.data0 ∨ s = Sym.data1 := by
  intro s hs
  simp [encodeBitsSym] at hs
  rcases hs with ⟨d, -, hs⟩
  rw [← hs]
  by_cases h : d = 0 <;> simp [h]

/-- [P1 · ①面提取] `encodeBitsSymNative` 条目恰为 data0/data1（精确符号）。 -/
lemma encodeBitsSymNative_entries (v : ℕ) :
    ∀ s ∈ encodeBitsSymNative v, s = Sym.data0 ∨ s = Sym.data1 := by
  intro s hs
  simp [encodeBitsSymNative] at hs
  rcases hs with ⟨d, -, hs⟩
  rw [← hs]
  by_cases h : d = 0 <;> simp [h]

/-- [P1 · ①面提取] 元素编码条目恰为 α/data0/data1（精确符号）。 -/
lemma encodeElementsSym_entries (elems : List ℕ) :
    ∀ s ∈ encodeElementsSym elems, s = Sym.alpha ∨ s = Sym.data0 ∨ s = Sym.data1 := by
  induction elems with
  | nil =>
      intro s hs
      simp [encodeElementsSym] at hs
  | cons v rest ih =>
      intro s hs
      cases hrest : rest with
      | nil =>
          simp [hrest, encodeElementsSym] at hs
          rcases hs with h | h
          · left
            exact h
          · rcases encodeBitsSymNative_entries v s h with h0 | h1
            · exact Or.inr (Or.inl h0)
            · exact Or.inr (Or.inr h1)
      | cons w rest' =>
          simp [hrest, encodeElementsSym] at hs
          rcases hs with h | h | h
          · left
            exact h
          · rcases encodeBitsSymNative_entries v s h with h0 | h1
            · exact Or.inr (Or.inl h0)
            · exact Or.inr (Or.inr h1)
          · rw [← hrest] at h
            exact ih s h

/-- [P1 · ①面提取] 元素编码 cons 长度（库版 `encodeElementsSym_cons_eq` 配套）。 -/
lemma encodeElementsSym_cons_len (v : ℕ) (rest : List ℕ) :
    (encodeElementsSym (v :: rest)).length =
      1 + (encodeBitsSymNative v).length + (encodeElementsSym rest).length := by
  rw [encodeElementsSym_cons_eq]
  simp [List.length_append]
  omega

/-- [P1 · ①面提取] ①段输出带面：目标区/边界保持不动；元素区 = `WithSel` 编码
    （sel 从 σ₁ 的分支写读出）；#₁ 在位。 -/
lemma run_alpha_face {inst : SubsetSumInstance} {π₀ : List SymStep} {cfgm : SymConfig}
    (hrun : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π₀ cfgm)
    (hR : ∀ s ∈ π₀, s.result.moveDir = Dir.R)
    (hnexts : ∀ s ∈ π₀, s.result.nextState ∈ [1, 2])
    (hhead : cfgm.headPos = (π₀.length : ℤ))
    (hlen : (π₀.length : ℤ) = 2 + ((encodeBitsSym inst.target).length : ℤ) +
      ((encodeElementsSym inst.elements).length : ℤ)) :
    ∃ sel : List Bool, sel.length = inst.elements.length ∧
      cfgm.tape 0 = Sym.boundary ∧
      tapeAgrees cfgm.tape 1 (encodeBitsSym inst.target) ∧
      cfgm.tape (1 + ((encodeBitsSym inst.target).length : ℤ)) = Sym.boundary ∧
      tapeAgrees cfgm.tape (2 + ((encodeBitsSym inst.target).length : ℤ))
        (encodeElementsSymWithSel inst.elements sel) ∧
      cfgm.tape (2 + ((encodeBitsSym inst.target).length : ℤ) +
        ((encodeElementsSym inst.elements).length : ℤ)) = Sym.boundary := by
  set tbl := encodeBitsSym inst.target with htbl_def
  set ebl := encodeElementsSym inst.elements with hebl_def
  obtain ⟨h0, hb, h10, he, h11, hbe⟩ := inst_tape_struct inst
  have hlenN : π₀.length = 2 + tbl.length + ebl.length := by omega
  -- 步访问器
  have hwrite : ∀ (i : ℕ) (hi : i < π₀.length),
      cfgm.tape (i : ℤ) = (π₀.get ⟨i, hi⟩).result.writeSym := by
    intro i hi
    have := run_tape_written hrun hR i hi
    simpa [symInitialConfig, SymConfig.mk] using this
  have hread : ∀ (i : ℕ) (hi : i < π₀.length),
      (π₀.get ⟨i, hi⟩).readSym = (symInitialConfig (encodeInstanceSym inst)).tape (i : ℤ) := by
    intro i hi
    have := run_reads_index hrun hR i hi
    simpa [symInitialConfig, SymConfig.mk] using this
  have hfrom2 : ∀ (i : ℕ) (hi : i < π₀.length), tbl.length + 2 ≤ i →
      (π₀.get ⟨i, hi⟩).fromState = 2 :=
    run_alpha_state2 h0 hb h10 he h11 hbe hrun hR hnexts
  have hfromle : ∀ (i : ℕ) (hi : i < π₀.length),
      (π₀.get ⟨i, hi⟩).fromState = 0 ∨ (π₀.get ⟨i, hi⟩).fromState = 1 ∨
        (π₀.get ⟨i, hi⟩).fromState = 2 :=
    run_alpha_state_le2 h0 hb h10 he h11 hbe hrun hR hnexts
  have hmem : ∀ (i : ℕ) (hi : i < π₀.length),
      (π₀.get ⟨i, hi⟩).result ∈ VerifierSym.transition
        ((π₀.get ⟨i, hi⟩).fromState, (π₀.get ⟨i, hi⟩).readSym) :=
    fun i hi => symSteps_step_mem hrun _ (List.getElem_mem hi)
  -- 保留格：读 ≠ α ⟹ 写 = 读
  have hkeep : ∀ (i : ℕ) (hi : i < π₀.length) (s₀ : Sym),
      (π₀.get ⟨i, hi⟩).readSym = s₀ →
      (s₀ = Sym.boundary ∨ s₀ = Sym.data0 ∨ s₀ = Sym.data1) →
      cfgm.tape (i : ℤ) = s₀ := by
    intro i hi s₀ hr0 hs
    rw [hwrite i hi]
    have hs4 : s₀ = Sym.boundary ∨ s₀ = Sym.data0 ∨ s₀ = Sym.data1 ∨
        s₀ = Sym.alpha := by
      rcases hs with h | h | h
      · left; exact h
      · right; left; exact h
      · right; right; left; exact h
    have hm0 : (π₀.get ⟨i, hi⟩).result ∈
        VerifierSym.transition ((π₀.get ⟨i, hi⟩).fromState, s₀) := by
      rw [← hr0]
      exact hmem i hi
    rcases transition_alpha_write (π₀.get ⟨i, hi⟩).fromState (hfromle i hi) s₀ hs4
      (π₀.get ⟨i, hi⟩).result hm0 with h | ⟨-, hα, -⟩
    · exact h
    · rcases hs with h | h | h <;> (rw [hα] at h; exact absurd h (by decide))
  -- 输入分解（segS0 模式）
  have htape0 : tapeAgrees (symInitialConfig (encodeInstanceSym inst)).tape 0 (encodeInstanceSym inst) :=
    symInitialConfig_tapeAgrees (encodeInstanceSym inst)
  have htapeA : tapeAgrees (symInitialConfig (encodeInstanceSym inst)).tape 0
      ([Sym.boundary] ++ (tbl ++ ([Sym.boundary] ++ (ebl ++ [Sym.boundary])))) := by
    simpa [encodeInstanceSym, htbl_def, hebl_def] using htape0
  have hsplit1 := (tapeAgrees_append _ 0 [Sym.boundary]
    (tbl ++ ([Sym.boundary] ++ (ebl ++ [Sym.boundary])))).mp htapeA
  have hb_l : (symInitialConfig (encodeInstanceSym inst)).tape 0 = Sym.boundary :=
    ((tapeAgrees_cons _ 0 Sym.boundary []).mp hsplit1.1).1
  have htape1 : tapeAgrees (symInitialConfig (encodeInstanceSym inst)).tape 1
      (tbl ++ ([Sym.boundary] ++ (ebl ++ [Sym.boundary]))) := by
    simpa using hsplit1.2
  have hsplit2 := (tapeAgrees_append _ 1 tbl ([Sym.boundary] ++ (ebl ++ [Sym.boundary]))).mp htape1
  have ht_tb : tapeAgrees (symInitialConfig (encodeInstanceSym inst)).tape 1 tbl := hsplit2.1
  have hsplit3 := (tapeAgrees_cons _ (1 + (tbl.length : ℤ)) Sym.boundary (ebl ++ [Sym.boundary])).mp hsplit2.2
  have hb_0 : (symInitialConfig (encodeInstanceSym inst)).tape (1 + (tbl.length : ℤ)) = Sym.boundary :=
    hsplit3.1
  have hsplit4 := (tapeAgrees_append _ ((1 + (tbl.length : ℤ)) + 1) ebl [Sym.boundary]).mp hsplit3.2
  have helems0 : tapeAgrees (symInitialConfig (encodeInstanceSym inst)).tape (2 + (tbl.length : ℤ)) ebl := by
    have hoff : (1 + (tbl.length : ℤ)) + 1 = 2 + (tbl.length : ℤ) := by ring
    rw [← hoff]
    exact hsplit4.1
  have hb_1 : (symInitialConfig (encodeInstanceSym inst)).tape
      (2 + (tbl.length : ℤ) + (ebl.length : ℤ)) = Sym.boundary := by
    have hoff2 : ((1 + (tbl.length : ℤ)) + 1) + (ebl.length : ℤ) =
        2 + (tbl.length : ℤ) + (ebl.length : ℤ) := by ring
    rw [← hoff2]
    exact ((tapeAgrees_cons _ (((1 + (tbl.length : ℤ)) + 1) + (ebl.length : ℤ)) Sym.boundary []).mp
      hsplit4.2).1
  -- 目标区
  have htarget : tapeAgrees cfgm.tape 1 tbl := by
    intro i hi
    have hi' : 1 + i < π₀.length := by omega
    have hri : (π₀.get ⟨1 + i, hi'⟩).readSym = tbl[i] := by
      rw [hread]
      have := ht_tb i hi
      simpa [Nat.cast_add, Nat.cast_one] using this
    have := hkeep (1 + i) hi' (tbl[i]) hri
      (Or.inr (encodeBitsSym_entries inst.target tbl[i] (List.getElem_mem hi)))
    simpa [Nat.cast_add, Nat.cast_one] using this
  -- #₀
  have hbnd0 : cfgm.tape (1 + (tbl.length : ℤ)) = Sym.boundary := by
    have hi : 1 + tbl.length < π₀.length := by omega
    have hri : (π₀.get ⟨1 + tbl.length, hi⟩).readSym = Sym.boundary := by
      rw [hread]
      have := hb_0
      simpa [Nat.cast_add, Nat.cast_one] using this
    have := hkeep (1 + tbl.length) hi Sym.boundary hri (Or.inl rfl)
    simpa [Nat.cast_add, Nat.cast_one] using this
  -- 位置 0
  have hb_l' : cfgm.tape 0 = Sym.boundary := by
    have hi : 0 < π₀.length := by omega
    have hri : (π₀.get ⟨0, hi⟩).readSym = Sym.boundary := by
      rw [hread]
      simpa using hb_l
    have := hkeep 0 hi Sym.boundary hri (Or.inl rfl)
    simpa using this
  -- #₁
  have hbnd1 : cfgm.tape (2 + (tbl.length : ℤ) + (ebl.length : ℤ)) = Sym.boundary := by
    have hh := run_tape_high_agree hrun hR cfgm.headPos le_rfl
    rw [hhead, hlen] at hh
    exact hh.trans hb_1
  -- 元素区块归纳
  have faceElem : tapeAgrees cfgm.tape (2 + (tbl.length : ℤ))
      (encodeElementsSymWithSel inst.elements (scanSelPrefix inst.elements cfgm.tape (2 + (tbl.length : ℤ)))) := by
    have hgen : ∀ (elems : List ℕ) (p : ℕ),
        2 + tbl.length ≤ p →
        p + (encodeElementsSym elems).length ≤ π₀.length →
        tapeAgrees (symInitialConfig (encodeInstanceSym inst)).tape (p : ℤ) (encodeElementsSym elems) →
        tapeAgrees cfgm.tape (p : ℤ)
          (encodeElementsSymWithSel elems (scanSelPrefix elems cfgm.tape (p : ℤ))) := by
      intro elems
      induction elems with
      | nil =>
          intro p _ _ _
          exact tapeAgrees_nil cfgm.tape (p : ℤ)
      | cons v rest ih =>
          intro p hp2 hbound htape
          have hlenee : (encodeElementsSym (v :: rest)).length =
              1 + (encodeBitsSymNative v).length + (encodeElementsSym rest).length :=
            encodeElementsSym_cons_len v rest
          have htape' : tapeAgrees (symInitialConfig (encodeInstanceSym inst)).tape (p : ℤ)
              ([Sym.alpha] ++ (encodeBitsSymNative v ++ encodeElementsSym rest)) := by
            rw [← List.append_assoc, ← encodeElementsSym_cons_eq v rest]
            exact htape
          have hs1 := (tapeAgrees_append _ (p : ℤ) [Sym.alpha]
            (encodeBitsSymNative v ++ encodeElementsSym rest)).mp htape'
          have hα₀ : (symInitialConfig (encodeInstanceSym inst)).tape (p : ℤ) = Sym.alpha :=
            ((tapeAgrees_cons _ (p : ℤ) Sym.alpha _).mp hs1.1).1
          have hs2 := (tapeAgrees_append _ ((p : ℤ) + 1) (encodeBitsSymNative v)
            (encodeElementsSym rest)).mp hs1.2
          have hbits₀ : tapeAgrees (symInitialConfig (encodeInstanceSym inst)).tape ((p : ℤ) + 1)
              (encodeBitsSymNative v) := hs2.1
          have hrest₀ : tapeAgrees (symInitialConfig (encodeInstanceSym inst)).tape
              ((p : ℤ) + 1 + ((encodeBitsSymNative v).length : ℤ)) (encodeElementsSym rest) := hs2.2
          -- WithSel 分解
          have hWsel : encodeElementsSymWithSel (v :: rest)
              (scanSelPrefix (v :: rest) cfgm.tape (p : ℤ)) =
              ([if decide (cfgm.tape (p : ℤ) = Sym.sel) then Sym.sel else Sym.nosel]) ++
              (encodeBitsSymNative v ++ encodeElementsSymWithSel rest
                (scanSelPrefix rest cfgm.tape ((p : ℤ) + 1 + ((encodeBitsSymNative v).length : ℤ)))) := by
            simp [encodeElementsSymWithSel, scanSelPrefix, List.zip_cons_cons, joinLists_cons,
              List.append_assoc]
          -- 头部标记格
          have hp_lt : p < π₀.length := by omega
          have hs₀ : (π₀.get ⟨p, hp_lt⟩).readSym = Sym.alpha := by
            rw [hread]
            exact hα₀
          have hfromp : (π₀.get ⟨p, hp_lt⟩).fromState = 2 := hfrom2 p hp_lt (by omega)
          have hmark : cfgm.tape (p : ℤ) =
              (if decide (cfgm.tape (p : ℤ) = Sym.sel) then Sym.sel else Sym.nosel) := by
            have hw0 : cfgm.tape (p : ℤ) = (π₀.get ⟨p, hp_lt⟩).result.writeSym := hwrite p hp_lt
            have hb0 : (π₀.get ⟨p, hp_lt⟩).result.writeSym = Sym.sel ∨
                (π₀.get ⟨p, hp_lt⟩).result.writeSym = Sym.nosel := by
              have hm0 := hmem p hp_lt
              rw [hfromp, hs₀] at hm0
              exact (transition_two_alpha Sym.alpha rfl _ hm0).2.2
            rcases hb0 with h | h
            · rw [hw0, h]
              simp
            · rw [hw0, h]
              have hne : ¬(Sym.nosel = Sym.sel) := by decide
              rw [if_neg (by rw [decide_eq_true_eq]; exact hne)]
          -- 位格
          have hbitsf : tapeAgrees cfgm.tape ((p : ℤ) + 1) (encodeBitsSymNative v) := by
            intro j hj
            have hjlt : p + 1 + j < π₀.length := by omega
            have hrj : (π₀.get ⟨p + 1 + j, hjlt⟩).readSym = (encodeBitsSymNative v)[j] := by
              rw [hread]
              have := hbits₀ j hj
              simpa [Nat.cast_add, Nat.cast_one] using this
            have := hkeep (p + 1 + j) hjlt ((encodeBitsSymNative v)[j]) hrj
              (Or.inr (encodeBitsSymNative_entries v _ (List.getElem_mem hj)))
            simpa [Nat.cast_add, Nat.cast_one] using this
          -- 尾块
          have hrestf : tapeAgrees cfgm.tape ((p : ℤ) + 1 + ((encodeBitsSymNative v).length : ℤ))
              (encodeElementsSymWithSel rest
                (scanSelPrefix rest cfgm.tape ((p : ℤ) + 1 + ((encodeBitsSymNative v).length : ℤ)))) := by
            have hb' : p + 1 + (encodeBitsSymNative v).length + (encodeElementsSym rest).length ≤
                π₀.length := by omega
            have hr' : tapeAgrees (symInitialConfig (encodeInstanceSym inst)).tape
                ((p + 1 + (encodeBitsSymNative v).length : ℕ) : ℤ) (encodeElementsSym rest) := by
              simpa [Nat.cast_add, Nat.cast_one] using hrest₀
            have := ih (p + 1 + (encodeBitsSymNative v).length) (by omega) hb' hr'
            simpa [Nat.cast_add, Nat.cast_one] using this
          -- 组装
          rw [hWsel]
          refine (tapeAgrees_append cfgm.tape (p : ℤ)
            ([if decide (cfgm.tape (p : ℤ) = Sym.sel) then Sym.sel else Sym.nosel])
            (encodeBitsSymNative v ++ encodeElementsSymWithSel rest
              (scanSelPrefix rest cfgm.tape ((p : ℤ) + 1 + ((encodeBitsSymNative v).length : ℤ))))).mpr ?_
          refine ⟨?_, ?_⟩
          · exact (tapeAgrees_cons cfgm.tape (p : ℤ)
              (if decide (cfgm.tape (p : ℤ) = Sym.sel) then Sym.sel else Sym.nosel) []).mpr
              ⟨hmark, tapeAgrees_nil _ _⟩
          · refine (tapeAgrees_append cfgm.tape ((p : ℤ) + 1) (encodeBitsSymNative v)
              (encodeElementsSymWithSel rest
                (scanSelPrefix rest cfgm.tape ((p : ℤ) + 1 + ((encodeBitsSymNative v).length : ℤ))))).mpr ?_
            exact ⟨hbitsf, hrestf⟩
    have hb0e : 2 + tbl.length + (encodeElementsSym inst.elements).length ≤ π₀.length := by
      rw [← hebl_def]
      omega
    have := hgen inst.elements (2 + tbl.length) (by omega) hb0e helems0
    simpa using this
  exact ⟨scanSelPrefix inst.elements cfgm.tape (2 + (tbl.length : ℤ)),
    scanSelPrefix_length inst.elements cfgm.tape (2 + (tbl.length : ℤ)),
    hb_l', htarget, hbnd0, faceElem, hbnd1⟩

/-! ========== P1 · ②拼接基础（T-P1.6） ========== -/

/-- [P1 · ②表] ≥3 封闭：q ≥ 3 的任意 (q,s) 转移后继仍 ≥ 3（表事实，逐值判定）。 -/
lemma transition_ge3_closed : ∀ (q : ℕ) (hq : q < 102) (k : SymKind) (m : Bool),
    3 ≤ q → ∀ r ∈ VerifierSym.transition (q, Sym.mk k m), 3 ≤ r.nextState := by
  intro q hq k m h3
  cases k <;> cases m <;> interval_cases q <;> decide

/-- [P1 · ②表] 100 吸收：任何 (100, s) 转移后继 = 100（表事实）。 -/
lemma transition_100_absorb : ∀ (k : SymKind) (m : Bool),
    ∀ r ∈ VerifierSym.transition (100, Sym.mk k m), r.nextState = 100 := by
  intro k m
  cases k <;> cases m <;> decide

/-- [P1 · ②拼接] 运行唯一性：同起点同一列表的两次运行终点配置相同。 -/
lemma symSteps_det {M : ℕ × Sym → Finset SymTransResult} :
    ∀ {c₀ c₁ c₂ : SymConfig} {π : List SymStep},
      SymSteps M c₀ π c₁ → SymSteps M c₀ π c₂ → c₁ = c₂ := by
  intro c₀ c₁ c₂ π h₁
  revert c₂
  induction h₁ with
  | nil =>
      intro c₂ h₂
      generalize hL : ([] : List SymStep) = L at h₂
      induction h₂ with
      | nil => rfl
      | cons πs step' c₂' hprev' hfrom' hread' htrans' ih2 => simp at hL
  | cons π₀ step c₁' hprev hfrom hread htrans ih =>
      intro c₂ h₂
      generalize hL : π₀ ++ [step] = L at h₂
      induction h₂ with
      | nil => simp at hL
      | cons πs step' c₂' hprev' hfrom' hread' htrans' ih2 =>
          obtain ⟨hπs, hstep⟩ := snoc_eq_snoc (by simpa using hL)
          subst hπs
          subst hstep
          have hcc := ih hprev'
          subst hcc
          rfl

/-- [P1 · ②拼接] 非空运行：存在步其（后继 = 终点状态）——实为末步。 -/
lemma symSteps_last_next {M : ℕ × Sym → Finset SymTransResult} :
    ∀ {c₀ cfg : SymConfig} {π : List SymStep}, π ≠ [] → SymSteps M c₀ π cfg →
      ∃ s ∈ π, s.result.nextState = cfg.state := by
  intro c₀ cfg π hne h
  revert hne
  induction h with
  | nil =>
      intro hne
      exact absurd rfl hne
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro _
      exact ⟨step, by simp, rfl⟩

/-- [P1 · ②拼接] 100 吸收 ⟹ 终态 ≠ 100 的运行不经过 100（步后继均 ≠ 100）。 -/
lemma symSteps_no_100_of_end_ne :
    ∀ {c₀ cfg : SymConfig} {π : List SymStep},
      SymSteps VerifierSym.transition c₀ π cfg → cfg.state ≠ 100 →
      ∀ s ∈ π, s.result.nextState ≠ 100 := by
  intro c₀ cfg π h
  induction h with
  | nil =>
      intro _ s hs
      simp at hs
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro hend s hs
      rcases List.mem_append.mp hs with hs' | hs'
      · have hc₁ : cfg₁.state ≠ 100 := by
          intro hc
          have hm100 : step.result ∈ VerifierSym.transition (100, step.readSym) := by
            rw [← hread, hc] at htrans
            exact htrans
          cases hrd : step.readSym with
          | mk k m =>
              rw [hrd] at hm100
              have hnext := transition_100_absorb k m step.result hm100
              exact hend hnext
        exact ih hc₁ s hs'
      · rw [List.mem_singleton] at hs'
        subst hs'
        exact hend

/-- [P1 · ②拼接] 自 (3, ·, ·) 的 VerifierSym 运行：终态 ≥ 3 且全部来态/后继 ≥ 3。 -/
lemma symSteps_ge3 :
    ∀ {t : ℤ → Sym} {p : ℤ} {π : List SymStep} {cfg : SymConfig},
      SymSteps VerifierSym.transition (SymConfig.mk 3 t p) π cfg →
      3 ≤ cfg.state ∧ ∀ s ∈ π, 3 ≤ s.fromState ∧ 3 ≤ s.result.nextState := by
  intro t p π cfg h
  induction h with
  | nil =>
      refine ⟨?_, ?_⟩
      · show 3 ≤ 3
        omega
      · intro s hs
        simp at hs
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      obtain ⟨ihst, ihsteps⟩ := ih
      have hq101 : cfg₁.state ≤ 101 :=
        (symSteps_state_le101 hprev (by simp)).1
      have hnext3 : 3 ≤ step.result.nextState := by
        have hm3 : step.result ∈ VerifierSym.transition (cfg₁.state, step.readSym) := by
          rw [hread]
          exact htrans
        cases hrd : step.readSym with
        | mk k m =>
            rw [hrd] at hm3
            exact transition_ge3_closed cfg₁.state (by omega) k m ihst step.result hm3
      refine ⟨?_, ?_⟩
      · rw [show (symStepConfig cfg₁ step.result).state = step.result.nextState from rfl]
        exact hnext3
      · intro s hs
        rcases List.mem_append.mp hs with hs' | hs'
        · exact ihsteps s hs'
        · rw [List.mem_singleton] at hs'
          subst hs'
          exact ⟨by rw [hfrom]; exact ihst, hnext3⟩

/-! ========== T-P1.7 段面分解移植（线2 探针 16:41 全绿；逐字复制） ========== -/

/-- 桥：`encodeBitsSymNative v = bitsToSym (bitsOf v)`（native 与 bitsToSym∘bitsOf 逐字同构）。 -/
lemma encNative_eq_bitsToSym_bitsOf (v : ℕ) :
    encodeBitsSymNative v = bitsToSym (bitsOf v) := by
  rw [show encodeBitsSymNative v = encodeBitsSym v from rfl]
  exact encodeBitsSym_eq_bitsToSym_bitsOf v

/-- 局部：`getD false` = 索引取值（越界前提）。 -/
lemma getD_false_eq_getElem (l : List Bool) (k : ℕ) (hk : k < l.length) :
    l.getD k false = l[k] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

/-- cons 形（关键：`++` 左结合，cons 化后各 getElem 归约走 `getElem_cons_succ`/`getElem_cons_zero`）。 -/
lemma WithSel_cons'' (v : ℕ) (rest : List ℕ) (b : Bool) (sel' : List Bool) :
    encodeElementsSymWithSel (v :: rest) (b :: sel') =
      (if b then Sym.sel else Sym.nosel) ::
        (encodeBitsSymNative v ++ encodeElementsSymWithSel rest sel') := by
  rw [WithSel_cons v rest b sel']
  rfl

/-- [分解 · 标记格] 段面下首格 = `sel`/`nosel`（按选择位 `b`）。 -/
lemma face_mark (v : ℕ) (rest : List ℕ) (b : Bool) (sel' : List Bool)
    (tape : ℤ → Sym) (base : ℤ)
    (h : tapeAgrees tape base (encodeElementsSymWithSel (v :: rest) (b :: sel'))) :
    tape base = (if b then Sym.sel else Sym.nosel) := by
  have hc := WithSel_cons'' v rest b sel'
  have hh := h 0 (by
    rw [hc]
    simp only [List.length_cons, List.length_append, List.length_nil]
    omega)
  simp only [hc] at hh
  simp only [List.getElem_cons_zero] at hh
  simpa using hh

/-- [分解 · 位格 Sym 面] 位格逐格 = `bitsToSym (bitsOf v)`（nosel 支 `helem` 形）。 -/
lemma face_bits_sym (v : ℕ) (rest : List ℕ) (b : Bool) (sel' : List Bool)
    (tape : ℤ → Sym) (base : ℤ)
    (h : tapeAgrees tape base (encodeElementsSymWithSel (v :: rest) (b :: sel'))) :
    tapeAgrees tape (base + 1) (bitsToSym (bitsOf v)) := by
  have hc := WithSel_cons'' v rest b sel'
  intro j hj
  have hjN : j < (encodeBitsSymNative v).length := by
    rw [encNative_eq_bitsToSym_bitsOf v]
    simpa using hj
  have hh := h (j + 1) (by
    rw [hc]
    simp only [List.length_cons, List.length_append, List.length_nil]
    omega)
  simp only [hc] at hh
  simp only [List.getElem_cons_succ] at hh
  simp only [List.getElem_append_left (bs := encodeElementsSymWithSel rest sel') hjN] at hh
  simp only [encNative_eq_bitsToSym_bitsOf v] at hh
  have hpos : base + ((j + 1 : ℕ) : ℤ) = (base + 1) + (j : ℤ) := by
    push_cast
    ring
  rw [hpos] at hh
  exact hh

/-- [分解 · 位格 kind 面] getD 形（sel 支 `hbits` 形；`ebits := bitsOf v`）。 -/
lemma face_bits_kind (v : ℕ) (rest : List ℕ) (b : Bool) (sel' : List Bool)
    (tape : ℤ → Sym) (base : ℤ)
    (h : tapeAgrees tape base (encodeElementsSymWithSel (v :: rest) (b :: sel'))) :
    ∀ i : ℕ, 1 ≤ i → i < (bitsOf v).length + 1 →
      (tape (base + (i : ℤ))).1 =
        (if (bitsOf v).getD (i - 1) false = true then SymKind.data1 else SymKind.data0) := by
  intro i hi1 hi2
  have hsym := face_bits_sym v rest b sel' tape base h
  have hiL : i - 1 < (bitsOf v).length := by omega
  have hcell := hsym (i - 1) (by
    simpa [bitsToSym] using hiL)
  have hval : (bitsToSym (bitsOf v))[i - 1]'(by
      simpa [bitsToSym] using hiL) =
      (if (bitsOf v)[i - 1] then Sym.data1 else Sym.data0) := by
    simp only [bitsToSym, List.getElem_map]
  rw [hval] at hcell
  have hpos : base + (i : ℤ) = (base + 1) + ((i - 1 : ℕ) : ℤ) := by
    have hi : i = (i - 1) + 1 := by omega
    rw [hi]
    push_cast
    ring
  rw [hpos]
  rw [hcell]
  rw [getD_false_eq_getElem (bitsOf v) (i - 1) hiL]
  by_cases hb : (bitsOf v)[i - 1]
  · simp [hb, Sym.data1_fst]
  · simp [hb, Sym.data0_fst]

/-- [分解 · 余段带面] 推进 `base ← base + 1 + |native v|`。 -/
lemma face_tail (v : ℕ) (rest : List ℕ) (b : Bool) (sel' : List Bool)
    (tape : ℤ → Sym) (base : ℤ)
    (h : tapeAgrees tape base (encodeElementsSymWithSel (v :: rest) (b :: sel'))) :
    tapeAgrees tape (base + 1 + ((encodeBitsSymNative v).length : ℤ))
      (encodeElementsSymWithSel rest sel') := by
  have hc := WithSel_cons'' v rest b sel'
  intro j hj
  have hh := h (1 + (encodeBitsSymNative v).length + j) (by
    rw [hc]
    simp only [List.length_cons, List.length_append, List.length_nil]
    omega)
  simp only [hc] at hh
  simp only [show 1 + (encodeBitsSymNative v).length + j =
      ((encodeBitsSymNative v).length + j) + 1 from by omega] at hh
  simp only [List.getElem_cons_succ] at hh
  rw [List.getElem_append_right (by omega)] at hh
  simp only [show (encodeBitsSymNative v).length + j -
      (encodeBitsSymNative v).length = j from by omega] at hh
  have hpos : base + (((encodeBitsSymNative v).length + j + 1 : ℕ) : ℤ) =
      (base + 1 + ((encodeBitsSymNative v).length : ℤ)) + (j : ℤ) := by
    push_cast
    ring
  rw [hpos] at hh
  exact hh

/-- [段面分解 · 合并件] 首元素全套面 + 余段带面（`run_fold_gen` 递归步直接消费）。 -/
lemma face_decomp_cons (v : ℕ) (rest : List ℕ) (b : Bool) (sel' : List Bool)
    (tape : ℤ → Sym) (base : ℤ)
    (h : tapeAgrees tape base (encodeElementsSymWithSel (v :: rest) (b :: sel'))) :
    tape base = (if b then Sym.sel else Sym.nosel) ∧
    tapeAgrees tape (base + 1) (bitsToSym (bitsOf v)) ∧
    (∀ i : ℕ, 1 ≤ i → i < (bitsOf v).length + 1 →
      (tape (base + (i : ℤ))).1 =
        (if (bitsOf v).getD (i - 1) false = true then SymKind.data1 else SymKind.data0)) ∧
    tapeAgrees tape (base + 1 + ((encodeBitsSymNative v).length : ℤ))
      (encodeElementsSymWithSel rest sel') :=
  ⟨face_mark v rest b sel' tape base h,
   face_bits_sym v rest b sel' tape base h,
   face_bits_kind v rest b sel' tape base h,
   face_tail v rest b sel' tape base h⟩

/-! ========== P1 · ②拼接总装（T-P1.6 收官） ========== -/

/-- [P1 · ②总装] ②格式段：给定接受运行自 ①出口展开 = `ρ`（`segS1` 包件，界 `2(3+|tb|+|eb|)`）+ 余段运行。 -/
lemma run_format_split {inst : SubsetSumInstance} {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π cfg)
    (hacc : cfg.state = 100)
    (hne : inst.elements ≠ []) (hpos : ∀ v ∈ inst.elements, 0 < v) (htarget : 0 < inst.target) :
    ∃ (sel : List Bool) (π₀ ρ π₁ : List SymStep) (step₃ : SymStep) (cfgm cf₁ : SymConfig),
      sel.length = inst.elements.length ∧
      π = π₀ ++ step₃ :: (ρ ++ π₁) ∧
      SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π₀ cfgm ∧
      (π₀.length : ℤ) = 2 + ((encodeBitsSym inst.target).length : ℤ) +
        ((encodeElementsSym inst.elements).length : ℤ) ∧
      cfgm.headPos = (π₀.length : ℤ) ∧
      step₃.fromState = 2 ∧ step₃.result.nextState = 3 ∧
      SymSteps VerifierSym.transition
        (SymConfig.mk 3 cfgm.tape (2 + ((encodeBitsSym inst.target).length : ℤ) +
          ((encodeElementsSym inst.elements).length : ℤ))) ρ cf₁ ∧
      cf₁.state = 4 ∧ cf₁.headPos = 2 + ((encodeBitsSym inst.target).length : ℤ) ∧
      ρ.length ≤ 2 * (3 + (encodeBitsSym inst.target).length +
        (encodeElementsSym inst.elements).length) ∧
      tapeAgrees cf₁.tape (2 + ((encodeBitsSym inst.target).length : ℤ))
        (encodeElementsSymWithSel inst.elements sel) ∧
      cf₁.tape (1 + ((encodeBitsSym inst.target).length : ℤ)) = Sym.boundary ∧
      cf₁.tape 0 = Sym.boundary ∧
      (∀ i : ℤ, 1 ≤ i → i ≤ ((encodeBitsSym inst.target).length : ℤ) →
        (cf₁.tape i).1 = SymKind.data0 ∨ (cf₁.tape i).1 = SymKind.data1) ∧
      (∀ i : ℤ, 1 ≤ i → i ≤ ((encodeBitsSym inst.target).length : ℤ) →
        (cf₁.tape i).2 = false) ∧
      cf₁.tape (2 + ((encodeBitsSym inst.target).length : ℤ) +
        ((encodeElementsSym inst.elements).length : ℤ)) = Sym.mk SymKind.boundary true ∧
      SymSteps VerifierSym.transition cf₁ π₁ cfg := by
  obtain ⟨π₀, step₃, π₁, cfgm, hsplit, hlenEq, hhead, hfrom3, hp3, hcread, hface, hR, hnexts, hrun⟩ :=
    run_alpha_len h hacc
  obtain ⟨sel, hsel_len, h0', htgt, hbnd0', hels, hbnd1'⟩ :=
    run_alpha_face hrun hR hnexts hhead hlenEq
  -- 尾段拆分：π₀ 之后 = step₃ :: π₁
  have h' : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst))
      (π₀ ++ (step₃ :: π₁)) cfg := by
    have := h
    rw [hsplit] at this
    exact this
  obtain ⟨c, hpre, htail⟩ := symSteps_append_split h'
  have hc : c = cfgm := symSteps_det hpre hrun
  rw [hc] at htail
  obtain ⟨c', hs₃, hπ₁⟩ := symSteps_append_split (π₀ := [step₃]) (rest := π₁)
    (by simpa [List.cons_append] using htail)
  obtain ⟨_hf, _hr, _hm, hc'⟩ := symSteps_singleton_facts hs₃
  rw [hc'] at hπ₁
  -- step₃ 写入/移动（(2, #) 行）：写 = boundary，动 = S
  have hw3 : step₃.result.writeSym = Sym.boundary ∧ step₃.result.moveDir = Dir.S := by
    have hm : step₃.result ∈ VerifierSym.transition (step₃.fromState, step₃.readSym) :=
      symSteps_step_mem h step₃ (by rw [hsplit]; exact List.mem_append.mpr (Or.inr (by simp)))
    rw [hfrom3] at hm
    have hread3 : step₃.readSym = Sym.boundary := by
      rw [hcread, hlenEq]
      obtain ⟨-, -, -, -, h11', -⟩ := inst_tape_struct inst
      exact h11'
    rw [hread3] at hm
    have := transition_two_boundary step₃.result hm
    exact ⟨this.2.2, this.2.1⟩
  -- cfg₃ 形：symStepConfig cfgm step₃.result = mk 3 cfgm.tape (2+|tb|+|eb|)
  have hmark1 : cfgm.tape cfgm.headPos = Sym.boundary := by
    rw [hhead, hface (π₀.length : ℤ) le_rfl]
    obtain ⟨-, -, -, -, h11', -⟩ := inst_tape_struct inst
    rw [hlenEq]
    exact h11'
  have hcfg3 : symStepConfig cfgm step₃.result =
      SymConfig.mk 3 cfgm.tape (2 + ((encodeBitsSym inst.target).length : ℤ) +
        ((encodeElementsSym inst.elements).length : ℤ)) := by
    have htapeeq : (fun i => if i = cfgm.headPos then step₃.result.writeSym else cfgm.tape i) =
        cfgm.tape := by
      funext i
      by_cases hi : i = cfgm.headPos
      · rw [if_pos hi, hw3.1, hi]
        exact hmark1.symm
      · rw [if_neg hi]
    have hhead' : cfgm.headPos + step₃.result.moveDir.toInt = 2 +
        ((encodeBitsSym inst.target).length : ℤ) +
        ((encodeElementsSym inst.elements).length : ℤ) := by
      rw [hw3.2]
      simp [Dir.toInt]
      rw [hhead]
      exact hlenEq
    simp only [symStepConfig]
    rw [hp3, htapeeq, hhead']
  rw [hcfg3] at hπ₁
  -- segS1 包件（前件全由 ① 面供给）
  obtain ⟨ρ, cf₁, hρrun, hcf₁st, hcf₁hd, hρlen, hcf₁tape⟩ :=
    segS1 inst sel hsel_len hne hpos htarget cfgm.tape h0' htgt hbnd0' hels hbnd1'
  -- 前缀相容：给定余段 vs 包件
  have hno2 : ∀ step ∈ π₁, step.fromState ≠ 2 := by
    have hge := (symSteps_ge3 hπ₁).2
    intro s hs
    have := hge s hs
    omega
  have h0le : (SymConfig.mk 3 cfgm.tape (2 + ((encodeBitsSym inst.target).length : ℤ) +
      ((encodeElementsSym inst.elements).length : ℤ))).state ≤ 101 := by simp
  rcases symSteps_prefix_comp hπ₁ hρrun h0le hno2 with ⟨r, hρeq, -⟩ | ⟨r, hsplit2, hrem⟩
  · -- 排除：ρ = π₁ ++ r 时 π₁ 末步后继 = 100 ∈ ρ，与 100 吸收（终态 = 4）矛盾
    exfalso
    have hne₁ : π₁ ≠ [] := by
      intro hnil
      have hc := symSteps_nil_cfg (by rwa [hnil] at hπ₁)
      rw [hc] at hacc
      simp at hacc
    obtain ⟨s₀, hs₀, hnext₀⟩ := symSteps_last_next hne₁ hπ₁
    have h100 : s₀.result.nextState = 100 := by rw [hnext₀, hacc]
    have hs₀ρ : s₀ ∈ ρ := by rw [hρeq]; exact List.mem_append.mpr (Or.inl hs₀)
    exact (symSteps_no_100_of_end_ne hρrun (by rw [hcf₁st]; decide) s₀ hs₀ρ) h100
  · -- cf₁ 带面六件（折叠 ③ 入口前提）
    have hface₁ : tapeAgrees cf₁.tape (2 + ((encodeBitsSym inst.target).length : ℤ))
        (encodeElementsSymWithSel inst.elements sel) := by
      intro j hj
      have hneq : ¬ (2 + ((encodeBitsSym inst.target).length : ℤ) + (j : ℤ) =
          2 + ((encodeBitsSym inst.target).length : ℤ) +
            ((encodeElementsSym inst.elements).length : ℤ)) := by
        have h2 := hj
        rw [WithSel_length inst.elements sel hsel_len] at h2
        omega
      have hcell : cf₁.tape (2 + ((encodeBitsSym inst.target).length : ℤ) + (j : ℤ)) =
          cfgm.tape (2 + ((encodeBitsSym inst.target).length : ℤ) + (j : ℤ)) := by
        rw [hcf₁tape]
        exact if_neg hneq
      rw [hcell]
      exact hels j hj
    have hbnd0₁ : cf₁.tape (1 + ((encodeBitsSym inst.target).length : ℤ)) = Sym.boundary := by
      have hneq : ¬ (1 + ((encodeBitsSym inst.target).length : ℤ) =
          2 + ((encodeBitsSym inst.target).length : ℤ) +
            ((encodeElementsSym inst.elements).length : ℤ)) := by omega
      have hcell : cf₁.tape (1 + ((encodeBitsSym inst.target).length : ℤ)) =
          cfgm.tape (1 + ((encodeBitsSym inst.target).length : ℤ)) := by
        rw [hcf₁tape]
        exact if_neg hneq
      rw [hcell]
      exact hbnd0'
    have hbndL₁ : cf₁.tape 0 = Sym.boundary := by
      have hneq : ¬ ((0 : ℤ) = 2 + ((encodeBitsSym inst.target).length : ℤ) +
          ((encodeElementsSym inst.elements).length : ℤ)) := by omega
      have hcell : cf₁.tape 0 = cfgm.tape 0 := by
        rw [hcf₁tape]
        exact if_neg hneq
      rw [hcell]
      exact h0'
    have hkd₁ : ∀ i : ℤ, 1 ≤ i → i ≤ ((encodeBitsSym inst.target).length : ℤ) →
        (cf₁.tape i).1 = SymKind.data0 ∨ (cf₁.tape i).1 = SymKind.data1 := by
      intro i hi1 hi2
      have hneq : ¬ (i = 2 + ((encodeBitsSym inst.target).length : ℤ) +
          ((encodeElementsSym inst.elements).length : ℤ)) := by omega
      have hcell : cf₁.tape i = cfgm.tape i := by
        rw [hcf₁tape]
        exact if_neg hneq
      rw [hcell]
      have h2 : i.toNat ≤ (encodeBitsSym inst.target).length := (Int.toNat_le).mpr hi2
      have h1 : 1 ≤ i.toNat := (Int.le_toNat (by omega : (0 : ℤ) ≤ i)).mpr hi1
      have htn : ((i.toNat : ℕ) : ℤ) = i := Int.toNat_of_nonneg (by omega)
      have hbnd2 : i.toNat - 1 < (encodeBitsSym inst.target).length := by omega
      have hmem := htgt (i.toNat - 1) hbnd2
      have hcell2 : 1 + ((i.toNat - 1 : ℕ) : ℤ) = i := by omega
      rw [hcell2] at hmem
      rw [hmem]
      rcases encodeBitsSym_entries inst.target _ (List.getElem_mem hbnd2) with h | h <;>
        rw [h] <;> [exact Or.inl rfl; exact Or.inr rfl]
    have hfl₁ : ∀ i : ℤ, 1 ≤ i → i ≤ ((encodeBitsSym inst.target).length : ℤ) →
        (cf₁.tape i).2 = false := by
      intro i hi1 hi2
      have hneq : ¬ (i = 2 + ((encodeBitsSym inst.target).length : ℤ) +
          ((encodeElementsSym inst.elements).length : ℤ)) := by omega
      have hcell : cf₁.tape i = cfgm.tape i := by
        rw [hcf₁tape]
        exact if_neg hneq
      rw [hcell]
      have h2 : i.toNat ≤ (encodeBitsSym inst.target).length := (Int.toNat_le).mpr hi2
      have h1 : 1 ≤ i.toNat := (Int.le_toNat (by omega : (0 : ℤ) ≤ i)).mpr hi1
      have htn : ((i.toNat : ℕ) : ℤ) = i := Int.toNat_of_nonneg (by omega)
      have hbnd2 : i.toNat - 1 < (encodeBitsSym inst.target).length := by omega
      have hmem := htgt (i.toNat - 1) hbnd2
      have hcell2 : 1 + ((i.toNat - 1 : ℕ) : ℤ) = i := by omega
      rw [hcell2] at hmem
      rw [hmem]
      rcases encodeBitsSym_entries inst.target _ (List.getElem_mem hbnd2) with h | h <;>
        rw [h] <;> rfl
    have hhend1₁ : cf₁.tape (2 + ((encodeBitsSym inst.target).length : ℤ) +
        ((encodeElementsSym inst.elements).length : ℤ)) = Sym.mk SymKind.boundary true := by
      rw [hcf₁tape]
      exact if_pos rfl
    exact ⟨sel, π₀, ρ, r, step₃, cfgm, cf₁, hsel_len, by rw [hsplit, hsplit2], hrun, hlenEq,
      hhead, hfrom3, hp3, hρrun, hcf₁st, hcf₁hd, hρlen, hface₁, hbnd0₁, hbndL₁, hkd₁, hfl₁,
      hhend1₁, hrem⟩

/-! ========== T-P1.7 · run_fold_gen 辅助与末元素件（T-P1.7 总装） ========== -/

/-- [T-P1.7] 选中元素值之和（结构性寄存器上界：`regVal ≥ chosenVal` 随递归下降）。 -/
def chosenVal (elems : List ℕ) (sels : List Bool) : ℤ :=
  ((elems.zip sels).filterMap (fun q => if q.2 then some (valFrom (bitsOf q.1) 1) else none)).sum

/-- [T-P1.7] 选中和 cons（true）。 -/
lemma chosenVal_cons_true (v : ℕ) (rest : List ℕ) (sel' : List Bool) :
    chosenVal (v :: rest) (true :: sel') = valFrom (bitsOf v) 1 + chosenVal rest sel' := by
  simp [chosenVal, List.zip_cons_cons, List.filterMap_cons]

/-- [T-P1.7] 选中和 cons（false）。 -/
lemma chosenVal_cons_false (v : ℕ) (rest : List ℕ) (sel' : List Bool) :
    chosenVal (v :: rest) (false :: sel') = chosenVal rest sel' := by
  simp [chosenVal, List.zip_cons_cons, List.filterMap_cons]

/-- [T-P1.7] 选中和 ≥ 0。 -/
lemma chosenVal_nonneg (elems : List ℕ) (sels : List Bool) : 0 ≤ chosenVal elems sels := by
  have hsum : ∀ l : List ℤ, (∀ x ∈ l, 0 ≤ x) → 0 ≤ l.sum := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons a t ih2 =>
        intro h
        rw [List.sum_cons]
        exact add_nonneg (h a (by simp)) (ih2 (fun x hx => h x (by simp [hx])))
  unfold chosenVal
  apply hsum
  intro x hx
  rcases List.mem_filterMap.mp hx with ⟨q, -, hq⟩
  by_cases hb : q.2 = true
  · rw [if_pos hb] at hq
    have hx' : valFrom (bitsOf q.1) 1 = x := Option.some.inj hq
    rw [← hx']
    exact valFrom_nonneg (bitsOf q.1) 1 (by norm_num)
  · rw [if_neg hb] at hq
    exact absurd hq (by simp)

/-- [T-P1.7] `bitsOf` 与 native 长度一致。 -/
lemma bitsOf_length_native (v : ℕ) : (bitsOf v).length = (encodeBitsSymNative v).length := by
  rw [encNative_eq_bitsToSym_bitsOf v]
  simp [bitsToSym]

/-- [T-P1.7] `segSrSel_gen` 界项 = `el`（逐字）。 -/
lemma sel_bound_eq_el (b : ℕ) (p : ℤ) :
    (b : ℤ) * (2 * (b : ℤ) + 2 * p + 3) + (4 * p + 4 * (b : ℤ) + 13) = el b p := rfl

/-- [T-P1.7 · 末元素 sel] 末元素（sel 标记，其后 #₁）：单段运行至 22。 -/
lemma run_fold_gen_last_sel (v : ℕ) (p_e : ℤ) (tape : ℤ → Sym)
    (hn1 : 1 ≤ (bitsOf v).length)
    (hnpe : ((bitsOf v).length : ℤ) ≤ p_e - 2)
    (hsel : tape p_e = Sym.sel)
    (hbound0 : tape (p_e - 1) = Sym.boundary)
    (hboundL : tape 0 = Sym.boundary)
    (hbwd0 : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hflag0 : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 → (tape i).2 = false)
    (hbits : ∀ i : ℕ, 1 ≤ i → i < (bitsOf v).length + 1 →
      (tape (p_e + (i : ℤ))).1 =
        (if (bitsOf v).getD (i - 1) false then SymKind.data1 else SymKind.data0))
    (hR0 : valFrom (bitsOf v) 1 ≤ regVal tape ((p_e - 2).toNat))
    (hende : (tape (p_e + 1 + ((bitsOf v).length : ℤ))).1 = SymKind.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) π cfg' ∧
      cfg'.state = 22 ∧
      cfg'.headPos = p_e + ((bitsOf v).length : ℤ) + 1 ∧
      (π.length : ℤ) ≤ el (bitsOf v).length p_e ∧
      tapeAgrees cfg'.tape (p_e - 1) (List.replicate ((bitsOf v).length + 2) Sym.data0) ∧
      (cfg'.tape 0 = tape 0) ∧
      (regVal cfg'.tape ((p_e - 2).toNat) =
        regVal tape ((p_e - 2).toNat) - valFrom (bitsOf v) 1) ∧
      (∀ i : ℤ, 1 ≤ i → i ≤ p_e + ((bitsOf v).length : ℤ) - 1 → (cfg'.tape i).2 = false) ∧
      (∀ i : ℤ, 1 ≤ i → i ≤ p_e + ((bitsOf v).length : ℤ) - 1 →
        (cfg'.tape i).1 = SymKind.data0 ∨ (cfg'.tape i).1 = SymKind.data1) ∧
      (cfg'.tape (p_e + ((bitsOf v).length : ℤ) + 1) =
        tape (p_e + ((bitsOf v).length : ℤ) + 1)) ∧
      (∀ i : ℤ, p_e + ((bitsOf v).length : ℤ) + 1 < i → cfg'.tape i = tape i) := by
  have hend : tape (p_e + 1 + ((bitsOf v).length : ℤ)) = Sym.sel ∨
      tape (p_e + 1 + ((bitsOf v).length : ℤ)) = Sym.nosel ∨
      (tape (p_e + 1 + ((bitsOf v).length : ℤ))).1 = SymKind.boundary :=
    Or.inr (Or.inr hende)
  rcases segSrSel_gen (bitsOf v) p_e tape hn1 hnpe hsel hbound0 hboundL hbwd0 hflag0 hbits hR0 hend
    with ⟨π, cfg', hrun, hcase, hC1, _, hex⟩
  have hendeB : (tape (p_e + ((bitsOf v).length : ℤ) + 1)).1 = SymKind.boundary := by
    rw [show p_e + ((bitsOf v).length : ℤ) + 1 = p_e + 1 + ((bitsOf v).length : ℤ)
      by ring]
    exact hende
  have hst22 : cfg'.state = 22 := hC1 hendeB
  rcases hcase with h4 | h22
  · exfalso
    rw [h4.1] at hst22
    exact absurd hst22 (by decide)
  · obtain ⟨_, hhd, hlen, hagr, hbl, hfl, hkd, htk, hhk⟩ := h22
    exact ⟨π, cfg', hrun, hst22, hhd, by simpa only [el] using hlen, hagr, hbl, hex,
      hfl, hkd, htk, hhk⟩

/-- [T-P1.7 · 末元素 nosel] 末元素（nosel 标记，其后 #₁）：单段运行至 22。 -/
lemma run_fold_gen_last_nosel (v : ℕ) (p_e : ℤ) (tape : ℤ → Sym)
    (hp0 : (0 : ℤ) ≤ p_e)
    (hsel : tape p_e = Sym.nosel)
    (hbound0 : tape (p_e - 1) = Sym.boundary)
    (helem : tapeAgrees tape (p_e + 1) (bitsToSym (bitsOf v)))
    (hende : (tape (p_e + 1 + ((bitsOf v).length : ℤ))).1 = SymKind.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) π cfg' ∧
      cfg'.state = 22 ∧
      cfg'.headPos = p_e + 1 + ((bitsOf v).length : ℤ) ∧
      (π.length : ℤ) ≤ el (bitsOf v).length p_e ∧
      tapeAgrees cfg'.tape (p_e - 1) (List.replicate ((bitsOf v).length + 1) Sym.data0) ∧
      (∀ i : ℤ, i < p_e - 1 → cfg'.tape i = tape i) ∧
      (∀ i : ℤ, p_e + 1 + ((bitsOf v).length : ℤ) < i → cfg'.tape i = tape i) ∧
      (cfg'.tape (p_e + 1 + ((bitsOf v).length : ℤ)) =
        tape (p_e + 1 + ((bitsOf v).length : ℤ))) ∧
      (cfg'.tape (p_e + ((bitsOf v).length : ℤ)) = Sym.data0) := by
  have hend : tape (p_e + 1 + ((bitsOf v).length : ℤ)) = Sym.sel ∨
      tape (p_e + 1 + ((bitsOf v).length : ℤ)) = Sym.nosel ∨
      (tape (p_e + 1 + ((bitsOf v).length : ℤ))).1 = SymKind.boundary :=
    Or.inr (Or.inr hende)
  rcases segSrNosel (bitsOf v) p_e tape hsel hbound0 helem hend with
    ⟨π, cfg', hrun, hlen, _, hC2, hagr, hlow, hhigh, htk, hzcell⟩
  obtain ⟨hst22, hhd⟩ := hC2 hende
  have hel : ((bitsOf v).length : ℤ) + 5 ≤ el (bitsOf v).length p_e :=
    nosel_bound_le_el (bitsOf v).length p_e hp0
  have hlen' : (π.length : ℤ) ≤ ((bitsOf v).length : ℤ) + 5 := by
    have := hlen
    omega
  exact ⟨π, cfg', hrun, hst22, hhd, by linarith, hagr, hlow, hhigh, htk, hzcell hende⟩

/-! ========== T-P1.7 · run_fold_gen 递归架构（FoldSpec） ========== -/

/-- [T-P1.7] WithSel 长度 cons 展开。 -/
lemma encSel_length_cons (e : ℕ) (rest : List ℕ) (b : Bool) (sel' : List Bool) :
    (encodeElementsSymWithSel (e :: rest) (b :: sel')).length =
      1 + (bitsOf e).length + (encodeElementsSymWithSel rest sel').length := by
  rw [WithSel_cons'']
  simp only [List.length_cons, List.length_append]
  rw [encNative_eq_bitsToSym_bitsOf]
  simp only [bitsToSym, List.length_map]
  omega

/-- [T-P1.7] WithSel 长度单元素。 -/
lemma encSel_length_single (e : ℕ) (b : Bool) :
    (encodeElementsSymWithSel [e] [b]).length = (bitsOf e).length + 1 := by
  have h := WithSel_cons'' e [] b []
  rw [h]
  simp only [List.length_cons, List.length_append]
  rw [encNative_eq_bitsToSym_bitsOf]
  simp only [bitsToSym, List.length_map]
  have h0 : (encodeElementsSymWithSel ([] : List ℕ) ([] : List Bool)).length = 0 := rfl
  omega

/-- [T-P1.7] native 编码长度 = bitsOf 长度。 -/
lemma encNative_length (e : ℕ) :
    (encodeBitsSymNative e).length = (bitsOf e).length := by
  rw [encNative_eq_bitsToSym_bitsOf]
  simp [bitsToSym]

/-- [T-P1.7] 段面首格（cons 形 · Or 版）：`tape base = sel ∨ tape base = nosel`。 -/
lemma tail_mark_iff (v : ℕ) (rest : List ℕ) (b : Bool) (sel' : List Bool)
    (tape : ℤ → Sym) (base : ℤ)
    (h : tapeAgrees tape base (encodeElementsSymWithSel (v :: rest) (b :: sel'))) :
    tape base = Sym.sel ∨ tape base = Sym.nosel := by
  have hc := WithSel_cons'' v rest b sel'
  have h0 := h 0 (by rw [hc]; simp only [List.length_cons]; omega)
  simp only [hc] at h0
  simp only [List.getElem_cons_zero] at h0
  cases b with
  | true => exact Or.inl (by simpa using h0)
  | false => exact Or.inr (by simpa using h0)

/-- [T-P1.7] fold 结论谓词（供递归引用；出口 = 22 + 定长头 + 二次界 + 全零区）。 -/
def FoldSpec (elems : List ℕ) (sels : List Bool) : Prop :=
  elems.length = sels.length →
  ∀ (p_e : ℤ) (tape : ℤ → Sym),
    (hne : elems ≠ []) → (0 : ℤ) ≤ p_e → (2 : ℤ) ≤ p_e →
    (∀ v ∈ elems, 1 ≤ v) →
    (∀ p ∈ elems.zip sels, p.2 = true → ((bitsOf p.1).length : ℤ) ≤ p_e - 2) →
    tapeAgrees tape p_e (encodeElementsSymWithSel elems sels) →
    tape (p_e - 1) = Sym.boundary →
    tape 0 = Sym.boundary →
    (∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1) →
    (∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 → (tape i).2 = false) →
    tape (p_e + ((encodeElementsSymWithSel elems sels).length : ℤ)) =
      Sym.mk SymKind.boundary true →
    chosenVal elems sels ≤ regVal tape ((p_e - 2).toNat) →
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) π cfg' ∧
      cfg'.state = 22 ∧
      cfg'.headPos = p_e + ((encodeElementsSymWithSel elems sels).length : ℤ) ∧
      (π.length : ℤ) ≤ foldLenB (elems.map (fun v => (bitsOf v).length)) p_e ∧
      (regVal cfg'.tape ((p_e + ((encodeElementsSymWithSel elems sels).length : ℤ) -
        ((bitsOf (elems.getLast hne)).length : ℤ) - 3).toNat) =
        regVal tape ((p_e - 2).toNat) - chosenVal elems sels) ∧
      (cfg'.tape 0 = Sym.boundary) ∧
      (∀ i : ℤ, 1 ≤ i → i ≤ p_e + ((encodeElementsSymWithSel elems sels).length : ℤ) -
          ((bitsOf (elems.getLast hne)).length : ℤ) - 3 →
        (cfg'.tape i).1 = SymKind.data0 ∨ (cfg'.tape i).1 = SymKind.data1) ∧
      (∀ i : ℤ, 1 ≤ i → i ≤ p_e + ((encodeElementsSymWithSel elems sels).length : ℤ) -
          ((bitsOf (elems.getLast hne)).length : ℤ) - 3 → (cfg'.tape i).2 = false) ∧
      (cfg'.tape (p_e + ((encodeElementsSymWithSel elems sels).length : ℤ)) =
        Sym.mk SymKind.boundary true) ∧
      (∀ i : ℤ, p_e + ((encodeElementsSymWithSel elems sels).length : ℤ) -
          ((bitsOf (elems.getLast hne)).length : ℤ) - 2 ≤ i →
        i ≤ p_e + ((encodeElementsSymWithSel elems sels).length : ℤ) - 1 →
        cfg'.tape i = Sym.data0)

/-- [T-P1.7] Bool-条件桥：`if g = true then A else B` = `if g then A else B`。 -/
lemma if_true_bridge (g : Bool) (A B : SymKind) :
    (if g = true then A else B) = (if g then A else B) := by
  cases g <;> simp

/-- [T-P1.7] `bitsOf` 长度正性。 -/
lemma bitsOf_length_pos {v : ℕ} (hv : 1 ≤ v) : 1 ≤ (bitsOf v).length := by
  rw [bitsOf_length]
  by_contra h
  have hnil : Nat.digits 2 v = [] := List.eq_nil_of_length_eq_zero (by omega)
  have hval := Nat.ofDigits_digits 2 v
  rw [hnil] at hval
  simp [Nat.ofDigits] at hval
  omega

/-- [T-P1.7 · 单元素 true] 单元素（sel）：`FoldSpec [v] [true]`。 -/
lemma fold_single_true (v : ℕ) : FoldSpec [v] [true] := by
  unfold FoldSpec
  intro hlen p_e tape hne hp0 hp2 hpos1 hposlen hface hbound0 hboundL hbwd0 hflag0 hend1 hR0
  have hv1 : 1 ≤ v := hpos1 v (by simp)
  have hmark := face_mark v [] true [] tape p_e hface
  simp only [if_true] at hmark
  have hbitsI := face_bits_kind v [] true [] tape p_e hface
  have hbits : ∀ i : ℕ, 1 ≤ i → i < (bitsOf v).length + 1 →
      (tape (p_e + (i : ℤ))).1 =
        (if (bitsOf v).getD (i - 1) false then SymKind.data1 else SymKind.data0) := by
    intro i hi1 hi2
    have h := hbitsI i hi1 hi2
    rw [if_true_bridge] at h
    exact h
  have hcv : chosenVal [v] [true] = valFrom (bitsOf v) 1 := by
    rw [chosenVal_cons_true]
    simp [chosenVal]
  have hR0' : valFrom (bitsOf v) 1 ≤ regVal tape ((p_e - 2).toNat) := by
    rw [← hcv]
    exact hR0
  have hWlen : (encodeElementsSymWithSel [v] [true]).length = (bitsOf v).length + 1 := by
    rw [WithSel_length [v] [true] (by simp)]
    rw [encodeElementsSym_cons_eq]
    simp only [encodeElementsSym, List.length_append, List.length_cons, List.length_nil,
      encodeBitsSymNative, List.length_map, zero_add, add_zero]
    rw [bitsOf_length]
    omega
  have hW : ((encodeElementsSymWithSel [v] [true]).length : ℤ) =
      ((bitsOf v).length : ℤ) + 1 := by
    exact_mod_cast hWlen
  have hende : (tape (p_e + 1 + ((bitsOf v).length : ℤ))).1 = SymKind.boundary := by
    have hpos : p_e + 1 + ((bitsOf v).length : ℤ) =
        p_e + ((encodeElementsSymWithSel [v] [true]).length : ℤ) := by omega
    rw [hpos, hend1]
    rfl
  have hn1 : 1 ≤ (bitsOf v).length := bitsOf_length_pos hv1
  have hnpe : ((bitsOf v).length : ℤ) ≤ p_e - 2 := hposlen (v, true) (by simp) rfl
  rcases run_fold_gen_last_sel v p_e tape hn1 hnpe hmark hbound0 hboundL
    hbwd0 hflag0 hbits hR0' hende with
    ⟨π, cfg', hrun, hst22, hhd, hlenB, hagr, hbl, hex, hfl, hkd, htk, hhk⟩
  have hend1' : tape (p_e + ((bitsOf v).length : ℤ) + 1) =
      Sym.mk SymKind.boundary true := by
    rw [show p_e + ((bitsOf v).length : ℤ) + 1 =
      p_e + ((encodeElementsSymWithSel [v] [true]).length : ℤ) by rw [hW]; ring]
    exact hend1
  have hgl : ([v] : List ℕ).getLast hne = v := List.getLast_singleton hne
  have hidx3 : p_e + ((encodeElementsSymWithSel [v] [true]).length : ℤ) -
      ((bitsOf (([v] : List ℕ).getLast hne)).length : ℤ) - 3 = p_e - 2 := by
    rw [hW, hgl]
    ring
  have hidx2 : p_e + ((encodeElementsSymWithSel [v] [true]).length : ℤ) -
      ((bitsOf (([v] : List ℕ).getLast hne)).length : ℤ) - 2 = p_e - 1 := by
    rw [hW, hgl]
    ring
  refine ⟨π, cfg', hrun, hst22, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hW, ← add_assoc]
    exact hhd
  · rw [show ([v].map (fun w => (bitsOf w).length)) = [((bitsOf v).length)] from rfl,
      ← el_eq_foldLenB_single]
    exact hlenB
  · rw [hidx3, hcv]
    exact hex
  · rw [hbl, hboundL]
  · intro i hi1 hi2
    exact hkd i hi1 (by omega)
  · intro i hi1 hi2
    exact hfl i hi1 (by omega)
  · rw [hW, ← add_assoc]
    exact htk.trans hend1'
  · intro i hi1 hi2
    have hi1' : p_e - 1 ≤ i := by
      rw [hidx2] at hi1
      exact hi1
    have hj : (i - (p_e - 1)).toNat < (bitsOf v).length + 2 := by omega
    have hcell : p_e - 1 + ((i - (p_e - 1)).toNat : ℤ) = i := by omega
    have h := hagr ((i - (p_e - 1)).toNat) (by simpa using hj)
    rw [hcell] at h
    rwa [List.getElem_replicate] at h

/-- [T-P1.7 · 单元素 false] 单元素（nosel）：`FoldSpec [v] [false]`。 -/
lemma fold_single_false (v : ℕ) : FoldSpec [v] [false] := by
  unfold FoldSpec
  intro hlen p_e tape hne hp0 hp2 hpos1 hposlen hface hbound0 hboundL hbwd0 hflag0 hend1 hR0
  have hv1 : 1 ≤ v := hpos1 v (by simp)
  have hn1 : 1 ≤ (bitsOf v).length := bitsOf_length_pos hv1
  have hmark0 := face_mark v [] false [] tape p_e hface
  have hmark : tape p_e = Sym.nosel := by simpa using hmark0
  have helem := face_bits_sym v [] false [] tape p_e hface
  have hWlen : (encodeElementsSymWithSel [v] [false]).length = (bitsOf v).length + 1 := by
    rw [WithSel_length [v] [false] (by simp)]
    rw [encodeElementsSym_cons_eq]
    simp only [encodeElementsSym, List.length_append, List.length_cons, List.length_nil,
      encodeBitsSymNative, List.length_map, zero_add, add_zero]
    rw [bitsOf_length]
    omega
  have hW : ((encodeElementsSymWithSel [v] [false]).length : ℤ) =
      ((bitsOf v).length : ℤ) + 1 := by
    exact_mod_cast hWlen
  have hende : (tape (p_e + 1 + ((bitsOf v).length : ℤ))).1 = SymKind.boundary := by
    have hpos : p_e + 1 + ((bitsOf v).length : ℤ) =
        p_e + ((encodeElementsSymWithSel [v] [false]).length : ℤ) := by omega
    rw [hpos, hend1]
    rfl
  have hend1' : tape (p_e + ((bitsOf v).length : ℤ) + 1) =
      Sym.mk SymKind.boundary true := by
    rw [show p_e + ((bitsOf v).length : ℤ) + 1 =
      p_e + ((encodeElementsSymWithSel [v] [false]).length : ℤ) by rw [hW]; ring]
    exact hend1
  have hend1F : tape (p_e + 1 + ((bitsOf v).length : ℤ)) =
      Sym.mk SymKind.boundary true := by
    rw [show p_e + 1 + ((bitsOf v).length : ℤ) =
      p_e + ((encodeElementsSymWithSel [v] [false]).length : ℤ) by rw [hW]; ring]
    exact hend1
  rcases run_fold_gen_last_nosel v p_e tape hp0 hmark hbound0 helem hende with
    ⟨π, cfg', hrun, hst22, hhd, hlenB, hagr, hlow, hhigh, htk, hcellEnd⟩
  have hcv : chosenVal [v] [false] = 0 := by
    rw [chosenVal_cons_false]
    simp [chosenVal]
  have hreg : regVal cfg'.tape ((p_e - 2).toNat) = regVal tape ((p_e - 2).toNat) := by
    have h1 : (1 : ℤ) ≤ ((bitsOf v).length : ℤ) := by exact_mod_cast hn1
    have hpe0 : (0 : ℤ) ≤ p_e - 2 := by omega
    have htl : (((p_e - 2).toNat : ℤ)) ≤ p_e - 2 := (Int.le_toNat hpe0).mp le_rfl
    unfold regVal
    refine regValA_congr_below tape cfg'.tape 1 ((p_e - 2).toNat) 0 (fun j hj => ?_)
    exact hlow (1 + (j : ℤ)) (by omega)
  have hgl : ([v] : List ℕ).getLast hne = v := List.getLast_singleton hne
  have hidx3 : p_e + ((encodeElementsSymWithSel [v] [false]).length : ℤ) -
      ((bitsOf (([v] : List ℕ).getLast hne)).length : ℤ) - 3 = p_e - 2 := by
    rw [hW, hgl]
    ring
  have hidx2 : p_e + ((encodeElementsSymWithSel [v] [false]).length : ℤ) -
      ((bitsOf (([v] : List ℕ).getLast hne)).length : ℤ) - 2 = p_e - 1 := by
    rw [hW, hgl]
    ring
  refine ⟨π, cfg', hrun, hst22, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show p_e + ((encodeElementsSymWithSel [v] [false]).length : ℤ) =
        p_e + 1 + ((bitsOf v).length : ℤ) by rw [hW]; ring]
    exact hhd
  · rw [show ([v].map (fun w => (bitsOf w).length)) = [((bitsOf v).length)] from rfl,
      ← el_eq_foldLenB_single]
    exact hlenB
  · rw [hidx3, hcv, sub_zero]
    exact hreg
  · rw [hlow 0 (by omega), hboundL]
  · intro i hi1 hi2
    rw [hlow i (by omega)]
    exact hbwd0 i hi1 (by omega)
  · intro i hi1 hi2
    rw [hlow i (by omega)]
    exact hflag0 i hi1 (by omega)
  · rw [show p_e + ((encodeElementsSymWithSel [v] [false]).length : ℤ) =
        p_e + 1 + ((bitsOf v).length : ℤ) by rw [hW]; ring]
    exact htk.trans hend1F
  · intro i hi1 hi2
    have hi1' : p_e - 1 ≤ i := by
      rw [hidx2] at hi1
      exact hi1
    by_cases hlt : i ≤ p_e + ((bitsOf v).length : ℤ) - 1
    · have hj : (i - (p_e - 1)).toNat < (bitsOf v).length + 1 := by omega
      have hcell : p_e - 1 + ((i - (p_e - 1)).toNat : ℤ) = i := by omega
      have h := hagr ((i - (p_e - 1)).toNat) (by simpa using hj)
      rw [hcell] at h
      rwa [List.getElem_replicate] at h
    · have hieq : i = p_e + ((bitsOf v).length : ℤ) := by
        have hWn := hW
        omega
      rw [hieq]
      exact hcellEnd

/-- [T-P1.7 · cons true] 归纳步（sel 首元素 + 递归尾）：`FoldSpec rest → FoldSpec (v :: rest) (true :: sel')` 之 cons 情形的展开形。 -/
lemma fold_cons_true (v : ℕ) (rest : List ℕ) (sel' : List Bool)
    (ih : ∀ (sels : List Bool), FoldSpec rest sels)
    (hlen : (v :: rest).length = (true :: sel').length)
    (hne : rest ≠ [])
    (hneCG : (v :: rest) ≠ [])
    (p_e : ℤ) (tape : ℤ → Sym)
    (hp0 : (0 : ℤ) ≤ p_e)
    (hp2 : (2 : ℤ) ≤ p_e)
    (hpos1 : ∀ w ∈ v :: rest, 1 ≤ w)
    (hposlen : ∀ p ∈ (v :: rest).zip (true :: sel'), p.2 = true → ((bitsOf p.1).length : ℤ) ≤ p_e - 2)
    (hface : tapeAgrees tape p_e (encodeElementsSymWithSel (v :: rest) (true :: sel')))
    (hbound0 : tape (p_e - 1) = Sym.boundary)
    (hboundL : tape 0 = Sym.boundary)
    (hbwd0 : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hflag0 : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 → (tape i).2 = false)
    (hend1 : tape (p_e + ((encodeElementsSymWithSel (v :: rest) (true :: sel')).length : ℤ)) =
      Sym.mk SymKind.boundary true)
    (hR0 : chosenVal (v :: rest) (true :: sel') ≤ regVal tape ((p_e - 2).toNat)) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) π cfg' ∧
      cfg'.state = 22 ∧
      cfg'.headPos = p_e + ((encodeElementsSymWithSel (v :: rest) (true :: sel')).length : ℤ) ∧
      (π.length : ℤ) ≤ foldLenB ((v :: rest).map (fun v => (bitsOf v).length)) p_e ∧
      (regVal cfg'.tape ((p_e + ((encodeElementsSymWithSel (v :: rest) (true :: sel')).length : ℤ) -
        ((bitsOf ((v :: rest).getLast hneCG)).length : ℤ) - 3).toNat) =
        regVal tape ((p_e - 2).toNat) - chosenVal (v :: rest) (true :: sel')) ∧
      (cfg'.tape 0 = Sym.boundary) ∧
      (∀ i : ℤ, 1 ≤ i → i ≤ p_e + ((encodeElementsSymWithSel (v :: rest) (true :: sel')).length : ℤ) -
          ((bitsOf ((v :: rest).getLast hneCG)).length : ℤ) - 3 →
        (cfg'.tape i).1 = SymKind.data0 ∨ (cfg'.tape i).1 = SymKind.data1) ∧
      (∀ i : ℤ, 1 ≤ i → i ≤ p_e + ((encodeElementsSymWithSel (v :: rest) (true :: sel')).length : ℤ) -
          ((bitsOf ((v :: rest).getLast hneCG)).length : ℤ) - 3 → (cfg'.tape i).2 = false) ∧
      (cfg'.tape (p_e + ((encodeElementsSymWithSel (v :: rest) (true :: sel')).length : ℤ)) =
        Sym.mk SymKind.boundary true) ∧
      (∀ i : ℤ, p_e + ((encodeElementsSymWithSel (v :: rest) (true :: sel')).length : ℤ) -
          ((bitsOf ((v :: rest).getLast hneCG)).length : ℤ) - 2 ≤ i →
        i ≤ p_e + ((encodeElementsSymWithSel (v :: rest) (true :: sel')).length : ℤ) - 1 →
        cfg'.tape i = Sym.data0) := by
  cases rest with
  | nil => exact absurd rfl hne
  | cons w ws =>
    cases sel' with
    | nil =>
      have h0 : (w :: ws).length = 0 := by
        simp only [List.length_cons, List.length_nil] at hlen
        omega
      exact absurd (List.eq_nil_of_length_eq_zero h0) hne
    | cons b' sel'' =>
      have hlen' : (w :: ws).length = (b' :: sel'').length := by
        simp only [List.length_cons] at hlen ⊢
        omega
      rw [chosenVal_cons_true] at hR0
      have hR01 : valFrom (bitsOf v) 1 ≤ regVal tape ((p_e - 2).toNat) := by
        linarith [hR0, chosenVal_nonneg (w :: ws) (b' :: sel'')]
      obtain ⟨hmark1, _hbits_sym1, hbits_kind1, htail1⟩ :=
        face_decomp_cons v (w :: ws) true (b' :: sel'') tape p_e hface
      have hsel1 : tape p_e = Sym.sel := by simpa using hmark1
      have hWcons : (((encodeElementsSymWithSel (v :: (w :: ws)) (true :: b' :: sel'')).length : ℕ) : ℤ) =
          1 + ((bitsOf v).length : ℤ) + ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ) := by
        rw [encSel_length_cons]
        push_cast
        ring
      have htb : p_e + 1 + ((encodeBitsSymNative v).length : ℤ) =
          p_e + ((bitsOf v).length : ℤ) + 1 := by
        rw [encNative_length v]
        ring
      have hm2 : tape (p_e + ((bitsOf v).length : ℤ) + 1) = Sym.sel ∨
          tape (p_e + ((bitsOf v).length : ℤ) + 1) = Sym.nosel := by
        have h := tail_mark_iff w ws b' sel'' tape
          (p_e + 1 + ((encodeBitsSymNative v).length : ℤ)) htail1
        rwa [htb] at h
      have hend1s : tape (p_e + 1 + ((bitsOf v).length : ℤ)) = Sym.sel ∨
          tape (p_e + 1 + ((bitsOf v).length : ℤ)) = Sym.nosel ∨
          (tape (p_e + 1 + ((bitsOf v).length : ℤ))).1 = SymKind.boundary := by
        rw [show p_e + 1 + ((bitsOf v).length : ℤ) =
          p_e + ((bitsOf v).length : ℤ) + 1 from by ring]
        rcases hm2 with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      have hn1 : 1 ≤ (bitsOf v).length := bitsOf_length_pos (hpos1 v (by simp))
      have hnpe : ((bitsOf v).length : ℤ) ≤ p_e - 2 := hposlen (v, true) (by simp) rfl
      rcases segSrSel_gen (bitsOf v) p_e tape hn1 hnpe hsel1 hbound0 hboundL hbwd0
        hflag0 hbits_kind1 hR01 hend1s with ⟨π₁, cfg₁, hs₁, hcase₁, hC1₁, hC2₁, hex₁⟩
      have hkind2 : (tape (p_e + ((bitsOf v).length : ℤ) + 1)).1 = SymKind.sel ∨
          (tape (p_e + ((bitsOf v).length : ℤ) + 1)).1 = SymKind.nosel := by
        rcases hm2 with h | h
        · exact Or.inl (by rw [h]; rfl)
        · exact Or.inr (by rw [h]; rfl)
      have hst4 : cfg₁.state = 4 := hC2₁ hkind2
      rcases hcase₁ with h4₁ | h22₁
      · rcases h4₁ with ⟨hst, hhd, hlen₁, hstamp, hagr, hbl, _hnet, hfl, hkd, htk, hhk⟩
        -- ===== 尾前提线程 =====
        have hbound0₂ : cfg₁.tape (p_e + ((bitsOf v).length : ℤ) + 1 - 1) = Sym.boundary := by
          rw [show p_e + ((bitsOf v).length : ℤ) + 1 - 1 =
            p_e + ((bitsOf v).length : ℤ) from by ring]
          exact hstamp
        have hboundL₂ : cfg₁.tape 0 = Sym.boundary := hbl.trans hboundL
        have hbwd0₂ : ∀ i : ℤ, 1 ≤ i → i ≤ (p_e + ((bitsOf v).length : ℤ) + 1) - 2 →
            (cfg₁.tape i).1 = SymKind.data0 ∨ (cfg₁.tape i).1 = SymKind.data1 := by
          intro i hi1 hi2
          exact hkd i hi1 (by omega)
        have hflag0₂ : ∀ i : ℤ, 1 ≤ i → i ≤ (p_e + ((bitsOf v).length : ℤ) + 1) - 2 →
            (cfg₁.tape i).2 = false := by
          intro i hi1 hi2
          exact hfl i hi1 (by omega)
        have hface₂ : tapeAgrees cfg₁.tape (p_e + ((bitsOf v).length : ℤ) + 1)
            (encodeElementsSymWithSel (w :: ws) (b' :: sel'')) := by
          intro j hj
          cases j with
          | zero =>
              show cfg₁.tape (p_e + ((bitsOf v).length : ℤ) + 1 + ((0 : ℕ) : ℤ)) =
                (encodeElementsSymWithSel (w :: ws) (b' :: sel''))[0]
              have hjm : (0 : ℕ) < (encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length := by
                rw [WithSel_cons'']; simp only [List.length_cons]; omega
              have h0 := htail1 0 hjm
              rw [show p_e + ((bitsOf v).length : ℤ) + 1 + ((0 : ℕ) : ℤ) =
                p_e + ((bitsOf v).length : ℤ) + 1 from by simp]
              rw [htk]
              have h0' : tape (p_e + ((bitsOf v).length : ℤ) + 1) =
                  (encodeElementsSymWithSel (w :: ws) (b' :: sel''))[0] := by
                have h := h0
                rw [show (p_e + 1 + ((encodeBitsSymNative v).length : ℤ)) + ((0 : ℕ) : ℤ) =
                  p_e + ((bitsOf v).length : ℤ) + 1 from by rw [htb]; simp] at h
                exact h
              exact h0'
          | succ j' =>
              rw [hhk _ (by
                show p_e + ((bitsOf v).length : ℤ) + 1 <
                  p_e + ((bitsOf v).length : ℤ) + 1 + (((j' + 1 : ℕ)) : ℤ)
                push_cast
                omega)]
              have hcell := htail1 (j' + 1) hj
              rw [show (p_e + 1 + ((encodeBitsSymNative v).length : ℤ)) + (((j' + 1 : ℕ)) : ℤ) =
                p_e + ((bitsOf v).length : ℤ) + 1 + (((j' + 1 : ℕ)) : ℤ) from by rw [htb]] at hcell
              exact hcell
        have hterm₂ : cfg₁.tape (p_e + ((bitsOf v).length : ℤ) + 1 +
            ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ)) = Sym.mk SymKind.boundary true := by
          have hgt : p_e + ((bitsOf v).length : ℤ) + 1 <
              p_e + ((bitsOf v).length : ℤ) + 1 +
                ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ) := by
            have h1 : 1 ≤ ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ) := by
              rw [WithSel_cons'']; simp only [List.length_cons]; omega
            omega
          rw [hhk _ hgt]
          have hterm_conv : tape (p_e + ((bitsOf v).length : ℤ) + 1 +
              ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ)) = Sym.mk SymKind.boundary true := by
            have h := hend1
            rw [hWcons] at h
            rwa [show p_e + (1 + ((bitsOf v).length : ℤ) +
                ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ)) =
              p_e + ((bitsOf v).length : ℤ) + 1 +
                ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ) from by ring] at h
          exact hterm_conv
        have hpos1₂ : ∀ w_ ∈ w :: ws, 1 ≤ w_ := by
          intro w_ hw_
          exact hpos1 w_ (by simp [hw_])
        have hposlen₂ : ∀ p ∈ (w :: ws).zip (b' :: sel''), p.2 = true →
            ((bitsOf p.1).length : ℤ) ≤ (p_e + ((bitsOf v).length : ℤ) + 1) - 2 := by
          intro p hp hpt
          have hp' : p ∈ (v :: (w :: ws)).zip (true :: b' :: sel'') :=
            List.mem_cons_of_mem (v, true) hp
          have := hposlen p hp' hpt
          omega
        have hp2₂ : (2 : ℤ) ≤ p_e + ((bitsOf v).length : ℤ) + 1 := by omega
        have hm' : ((p_e + ((bitsOf v).length : ℤ) + 1 - 2).toNat) =
            ((p_e - 2).toNat) + ((bitsOf v).length + 1) := by
          have hc1 := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
          have hc2 := Int.toNat_of_nonneg
            (show (0 : ℤ) ≤ p_e + ((bitsOf v).length : ℤ) + 1 - 2 by omega)
          omega
        have hagr' : tapeAgrees cfg₁.tape (1 + (((p_e - 2).toNat) : ℤ))
            (List.replicate ((bitsOf v).length + 1) Sym.data0) := by
          have heq : (1 : ℤ) + (((p_e - 2).toNat) : ℤ) = p_e - 1 := by
            have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
            omega
          rw [heq]
          exact hagr
        have hext : regVal cfg₁.tape (((p_e - 2).toNat) + ((bitsOf v).length + 1)) =
            regVal cfg₁.tape ((p_e - 2).toNat) :=
          regVal_zero_ext cfg₁.tape 1 ((p_e - 2).toNat) ((bitsOf v).length + 1) hagr'
        have hR0₂ : chosenVal (w :: ws) (b' :: sel'') ≤
            regVal cfg₁.tape ((p_e + ((bitsOf v).length : ℤ) + 1 - 2).toNat) := by
          rw [hm', hext, hex₁]
          linarith [hR0]
        -- ===== 尾递归（ih）=====
        rcases ih (b' :: sel'') hlen' (p_e + ((bitsOf v).length : ℤ) + 1) cfg₁.tape hne (by omega) hp2₂
          hpos1₂ hposlen₂ hface₂ hbound0₂ hboundL₂ hbwd0₂ hflag0₂ hterm₂ hR0₂ with
          ⟨π₂, cfg₂, hs₂, hst₂, hhd₂, hlen₂, hreg₂, htape0₂, hkd₂, hfl₂, htk₂, hz₂⟩
        -- ===== 拼接与出口装配 =====
        have e₀ : cfg₁ = SymConfig.mk 4 cfg₁.tape (p_e + ((bitsOf v).length : ℤ) + 1) := by
          rw [show cfg₁ = SymConfig.mk cfg₁.state cfg₁.tape cfg₁.headPos from rfl]
          rw [hst, hhd]
        have hcat : SymSteps VerifierSym.transition cfg₁ π₂ cfg₂ := by
          rw [e₀]
          exact hs₂
        have hlen'₂ : (π₁.length : ℤ) ≤ el (bitsOf v).length p_e := by
          simpa [el] using hlen₁
        have hLlast : ((bitsOf ((v :: (w :: ws)).getLast hneCG)).length : ℤ) =
            ((bitsOf ((w :: ws).getLast hne)).length : ℤ) := by
          rw [List.getLast_cons hne]
        have hidx : p_e + ((encodeElementsSymWithSel (v :: (w :: ws)) (true :: b' :: sel'')).length : ℤ) -
            ((bitsOf ((v :: (w :: ws)).getLast hneCG)).length : ℤ) - 3 =
            (p_e + ((bitsOf v).length : ℤ) + 1) +
              ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ) -
              ((bitsOf ((w :: ws).getLast hne)).length : ℤ) - 3 := by
          rw [hWcons, hLlast]
          ring
        have hidxK : p_e + ((encodeElementsSymWithSel (v :: (w :: ws)) (true :: b' :: sel'')).length : ℤ) -
            ((bitsOf ((v :: (w :: ws)).getLast hneCG)).length : ℤ) - 3 =
            (p_e + ((bitsOf v).length : ℤ) + 1) +
              ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ) -
              ((bitsOf ((w :: ws).getLast hne)).length : ℤ) - 3 := by
          rw [hWcons, hLlast]
          ring
        refine ⟨π₁ ++ π₂, cfg₂, symSteps_append_concat π₁ π₂ hs₁ hcat, hst₂, ?_, ?_, ?_,
          htape0₂, ?_, ?_, ?_, ?_⟩
        · rw [hWcons]
          rw [show p_e + (1 + ((bitsOf v).length : ℤ) +
              ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ)) =
            p_e + ((bitsOf v).length : ℤ) + 1 +
              ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ) from by ring]
          exact hhd₂
        · rw [List.length_append]
          push_cast
          have hf : foldLenB ((v :: (w :: ws)).map (fun v => (bitsOf v).length)) p_e =
              el (bitsOf v).length p_e +
                foldLenB ((w :: ws).map (fun w => (bitsOf w).length))
                  (p_e + ((bitsOf v).length : ℤ) + 1) := by
            rw [List.map_cons, foldLenB_cons]
          rw [hf]
          linarith [hlen'₂, hlen₂]
        · rw [hidx]
          have hchain : regVal cfg₁.tape ((p_e + ((bitsOf v).length : ℤ) + 1 - 2).toNat) =
              regVal tape ((p_e - 2).toNat) - valFrom (bitsOf v) 1 := by
            rw [hm', hext, hex₁]
          rw [hchain] at hreg₂
          rw [chosenVal_cons_true]
          linarith [hreg₂]
        · intro i hi1 hi2
          have hi2' : i ≤ (p_e + ((bitsOf v).length : ℤ) + 1) +
              ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ) -
              ((bitsOf ((w :: ws).getLast hne)).length : ℤ) - 3 := by
            have h := hi2
            rw [hWcons, hLlast] at h
            omega
          exact hkd₂ i hi1 hi2'
        · intro i hi1 hi2
          have hi2' : i ≤ (p_e + ((bitsOf v).length : ℤ) + 1) +
              ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ) -
              ((bitsOf ((w :: ws).getLast hne)).length : ℤ) - 3 := by
            have h := hi2
            rw [hWcons, hLlast] at h
            omega
          exact hfl₂ i hi1 hi2'
        · rw [hWcons]
          rw [show p_e + (1 + ((bitsOf v).length : ℤ) +
              ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ)) =
            p_e + ((bitsOf v).length : ℤ) + 1 +
              ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ) from by ring]
          exact htk₂
        · intro i hi1 hi2
          have hidx2 : p_e + ((encodeElementsSymWithSel (v :: (w :: ws)) (true :: b' :: sel'')).length : ℤ) -
              ((bitsOf ((v :: (w :: ws)).getLast hneCG)).length : ℤ) - 2 =
              (p_e + ((bitsOf v).length : ℤ) + 1) +
                ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ) -
                ((bitsOf ((w :: ws).getLast hne)).length : ℤ) - 2 := by
            rw [hWcons, hLlast]
            ring
          have hidx3 : p_e + ((encodeElementsSymWithSel (v :: (w :: ws)) (true :: b' :: sel'')).length : ℤ) - 1 =
              (p_e + ((bitsOf v).length : ℤ) + 1) +
                ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ) - 1 := by
            rw [hWcons]
            ring
          rw [hidx2] at hi1
          rw [hidx3] at hi2
          exact hz₂ i hi1 hi2
      · exfalso
        rw [h22₁.1] at hst4
        exact absurd hst4 (by decide)

/-- [T-P1.7 · cons false] 归纳步（nosel 首元素 + 递归尾）：`FoldSpec rest → FoldSpec (v :: rest) (false :: sel')` 之 cons 情形的展开形。 -/
lemma fold_cons_false (v : ℕ) (rest : List ℕ) (sel' : List Bool)
    (ih : ∀ (sels : List Bool), FoldSpec rest sels)
    (hlen : (v :: rest).length = (false :: sel').length)
    (hne : rest ≠ [])
    (hneCG : (v :: rest) ≠ [])
    (p_e : ℤ) (tape : ℤ → Sym)
    (hp0 : (0 : ℤ) ≤ p_e)
    (hp2 : (2 : ℤ) ≤ p_e)
    (hpos1 : ∀ w ∈ v :: rest, 1 ≤ w)
    (hposlen : ∀ p ∈ (v :: rest).zip (false :: sel'), p.2 = true → ((bitsOf p.1).length : ℤ) ≤ p_e - 2)
    (hface : tapeAgrees tape p_e (encodeElementsSymWithSel (v :: rest) (false :: sel')))
    (hbound0 : tape (p_e - 1) = Sym.boundary)
    (hboundL : tape 0 = Sym.boundary)
    (hbwd0 : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hflag0 : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 → (tape i).2 = false)
    (hend1 : tape (p_e + ((encodeElementsSymWithSel (v :: rest) (false :: sel')).length : ℤ)) =
      Sym.mk SymKind.boundary true)
    (hR0 : chosenVal (v :: rest) (false :: sel') ≤ regVal tape ((p_e - 2).toNat)) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) π cfg' ∧
      cfg'.state = 22 ∧
      cfg'.headPos = p_e + ((encodeElementsSymWithSel (v :: rest) (false :: sel')).length : ℤ) ∧
      (π.length : ℤ) ≤ foldLenB ((v :: rest).map (fun v => (bitsOf v).length)) p_e ∧
      (regVal cfg'.tape ((p_e + ((encodeElementsSymWithSel (v :: rest) (false :: sel')).length : ℤ) -
        ((bitsOf ((v :: rest).getLast hneCG)).length : ℤ) - 3).toNat) =
        regVal tape ((p_e - 2).toNat) - chosenVal (v :: rest) (false :: sel')) ∧
      (cfg'.tape 0 = Sym.boundary) ∧
      (∀ i : ℤ, 1 ≤ i → i ≤ p_e + ((encodeElementsSymWithSel (v :: rest) (false :: sel')).length : ℤ) -
          ((bitsOf ((v :: rest).getLast hneCG)).length : ℤ) - 3 →
        (cfg'.tape i).1 = SymKind.data0 ∨ (cfg'.tape i).1 = SymKind.data1) ∧
      (∀ i : ℤ, 1 ≤ i → i ≤ p_e + ((encodeElementsSymWithSel (v :: rest) (false :: sel')).length : ℤ) -
          ((bitsOf ((v :: rest).getLast hneCG)).length : ℤ) - 3 → (cfg'.tape i).2 = false) ∧
      (cfg'.tape (p_e + ((encodeElementsSymWithSel (v :: rest) (false :: sel')).length : ℤ)) =
        Sym.mk SymKind.boundary true) ∧
      (∀ i : ℤ, p_e + ((encodeElementsSymWithSel (v :: rest) (false :: sel')).length : ℤ) -
          ((bitsOf ((v :: rest).getLast hneCG)).length : ℤ) - 2 ≤ i →
        i ≤ p_e + ((encodeElementsSymWithSel (v :: rest) (false :: sel')).length : ℤ) - 1 →
        cfg'.tape i = Sym.data0) := by
  cases rest with
  | nil => exact absurd rfl hne
  | cons w ws =>
    cases sel' with
    | nil =>
      have h0 : (w :: ws).length = 0 := by
        simp only [List.length_cons, List.length_nil] at hlen
        omega
      exact absurd (List.eq_nil_of_length_eq_zero h0) hne
    | cons b' sel'' =>
      have hlen' : (w :: ws).length = (b' :: sel'').length := by
        simp only [List.length_cons] at hlen ⊢
        omega
      rw [chosenVal_cons_false] at hR0
      obtain ⟨hmark1, _hbits_sym1, hbits_kind1, htail1⟩ :=
        face_decomp_cons v (w :: ws) false (b' :: sel'') tape p_e hface
      have hnosel1 : tape p_e = Sym.nosel := by simpa using hmark1
      have hbits_sym1v : tapeAgrees tape (p_e + 1) (bitsToSym (bitsOf v)) :=
        face_bits_sym v (w :: ws) false (b' :: sel'') tape p_e hface
      have hn1v : 1 ≤ (bitsOf v).length := bitsOf_length_pos (hpos1 v (by simp))
      have hp2v : (2 : ℤ) ≤ p_e := by omega
      have hWcons : (((encodeElementsSymWithSel (v :: (w :: ws)) (false :: b' :: sel'')).length : ℕ) : ℤ) =
          1 + ((bitsOf v).length : ℤ) + ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ) := by
        rw [encSel_length_cons]
        push_cast
        ring
      have htb : p_e + 1 + ((encodeBitsSymNative v).length : ℤ) =
          p_e + ((bitsOf v).length : ℤ) + 1 := by
        rw [encNative_length v]
        ring
      have hm2 : tape (p_e + ((bitsOf v).length : ℤ) + 1) = Sym.sel ∨
          tape (p_e + ((bitsOf v).length : ℤ) + 1) = Sym.nosel := by
        have h := tail_mark_iff w ws b' sel'' tape
          (p_e + 1 + ((encodeBitsSymNative v).length : ℤ)) htail1
        rwa [htb] at h
      have hend1s : tape (p_e + 1 + ((bitsOf v).length : ℤ)) = Sym.sel ∨
          tape (p_e + 1 + ((bitsOf v).length : ℤ)) = Sym.nosel ∨
          (tape (p_e + 1 + ((bitsOf v).length : ℤ))).1 = SymKind.boundary := by
        rw [show p_e + 1 + ((bitsOf v).length : ℤ) =
          p_e + ((bitsOf v).length : ℤ) + 1 from by ring]
        rcases hm2 with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      rcases segSrNosel (bitsOf v) p_e tape hnosel1 hbound0 hbits_sym1v hend1s with
        ⟨π₁, cfg₁, hs₁, hlen₅, hC1n, _hC2n, hagr, hleftn, hrightn, htk, _hzcell⟩
      have hkind2 : tape (p_e + ((bitsOf v).length : ℤ) + 1) = Sym.sel ∨
          tape (p_e + ((bitsOf v).length : ℤ) + 1) = Sym.nosel := hm2
      have hkind2A : tape (p_e + 1 + ((bitsOf v).length : ℤ)) = Sym.sel ∨
          tape (p_e + 1 + ((bitsOf v).length : ℤ)) = Sym.nosel := by
        rw [show p_e + 1 + ((bitsOf v).length : ℤ) =
          p_e + ((bitsOf v).length : ℤ) + 1 from by ring]
        exact hkind2
      obtain ⟨hst, hhd, hstamp, _htkN⟩ := hC1n hkind2A
      -- ===== 尾前提线程 =====
      have hbound0₂ : cfg₁.tape (p_e + ((bitsOf v).length : ℤ) + 1 - 1) = Sym.boundary := by
        rw [show p_e + ((bitsOf v).length : ℤ) + 1 - 1 =
          p_e + ((bitsOf v).length : ℤ) from by ring]
        exact hstamp
      have hboundL₂ : cfg₁.tape 0 = Sym.boundary := (hleftn 0 (by omega)).trans hboundL
      have hbwd0₂ : ∀ i : ℤ, 1 ≤ i → i ≤ (p_e + ((bitsOf v).length : ℤ) + 1) - 2 →
          (cfg₁.tape i).1 = SymKind.data0 ∨ (cfg₁.tape i).1 = SymKind.data1 := by
        intro i hi1 hi2
        by_cases hle : i ≤ p_e - 2
        · rw [hleftn i (by omega)]
          exact hbwd0 i hi1 hle
        · have hcell := hagr (i - (p_e - 1)).toNat (by
            rw [List.length_replicate]
            have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - (p_e - 1) by omega)
            omega)
          have hsub : i = (p_e - 1) + (((i - (p_e - 1)).toNat : ℕ) : ℤ) := by
            have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - (p_e - 1) by omega)
            omega
          rw [hsub, hcell]
          simp only [List.getElem_replicate]
          exact Or.inl rfl
      have hflag0₂ : ∀ i : ℤ, 1 ≤ i → i ≤ (p_e + ((bitsOf v).length : ℤ) + 1) - 2 →
          (cfg₁.tape i).2 = false := by
        intro i hi1 hi2
        by_cases hle : i ≤ p_e - 2
        · rw [hleftn i (by omega)]
          exact hflag0 i hi1 hle
        · have hcell := hagr (i - (p_e - 1)).toNat (by
            rw [List.length_replicate]
            have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - (p_e - 1) by omega)
            omega)
          have hsub : i = (p_e - 1) + (((i - (p_e - 1)).toNat : ℕ) : ℤ) := by
            have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - (p_e - 1) by omega)
            omega
          rw [hsub, hcell]
          simp only [List.getElem_replicate]
          rfl
      have hface₂ : tapeAgrees cfg₁.tape (p_e + ((bitsOf v).length : ℤ) + 1)
          (encodeElementsSymWithSel (w :: ws) (b' :: sel'')) := by
        intro j hj
        cases j with
        | zero =>
            show cfg₁.tape (p_e + ((bitsOf v).length : ℤ) + 1 + ((0 : ℕ) : ℤ)) =
              (encodeElementsSymWithSel (w :: ws) (b' :: sel''))[0]
            have hjm : (0 : ℕ) < (encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length := by
              rw [WithSel_cons'']; simp only [List.length_cons]; omega
            have h0 := htail1 0 hjm
            rw [show p_e + ((bitsOf v).length : ℤ) + 1 + ((0 : ℕ) : ℤ) =
              p_e + 1 + ((bitsOf v).length : ℤ) from by push_cast; ring]
            rw [htk]
            have h0' : tape (p_e + 1 + ((bitsOf v).length : ℤ)) =
                (encodeElementsSymWithSel (w :: ws) (b' :: sel''))[0] := by
              have h := h0
              rw [show (p_e + 1 + ((encodeBitsSymNative v).length : ℤ)) + ((0 : ℕ) : ℤ) =
                p_e + 1 + ((bitsOf v).length : ℤ) from by rw [htb]; push_cast; ring] at h
              exact h
            exact h0'
        | succ j' =>
            rw [hrightn _ (by
              show p_e + 1 + ((bitsOf v).length : ℤ) <
                p_e + ((bitsOf v).length : ℤ) + 1 + (((j' + 1 : ℕ)) : ℤ)
              push_cast
              omega)]
            have hcell := htail1 (j' + 1) hj
            rw [show (p_e + 1 + ((encodeBitsSymNative v).length : ℤ)) + (((j' + 1 : ℕ)) : ℤ) =
              p_e + ((bitsOf v).length : ℤ) + 1 + (((j' + 1 : ℕ)) : ℤ) from by rw [htb]] at hcell
            exact hcell
      have hterm₂ : cfg₁.tape (p_e + ((bitsOf v).length : ℤ) + 1 +
          ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ)) = Sym.mk SymKind.boundary true := by
        have hgt : p_e + 1 + ((bitsOf v).length : ℤ) <
            p_e + ((bitsOf v).length : ℤ) + 1 +
              ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ) := by
          have h1 : 1 ≤ ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ) := by
            rw [WithSel_cons'']; simp only [List.length_cons]; omega
          omega
        rw [hrightn _ hgt]
        have hterm_conv : tape (p_e + ((bitsOf v).length : ℤ) + 1 +
            ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ)) = Sym.mk SymKind.boundary true := by
          have h := hend1
          rw [hWcons] at h
          rwa [show p_e + (1 + ((bitsOf v).length : ℤ) +
              ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ)) =
            p_e + ((bitsOf v).length : ℤ) + 1 +
              ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ) from by ring] at h
        exact hterm_conv
      have hpos1₂ : ∀ w_ ∈ w :: ws, 1 ≤ w_ := by
        intro w_ hw_
        exact hpos1 w_ (by simp [hw_])
      have hposlen₂ : ∀ p ∈ (w :: ws).zip (b' :: sel''), p.2 = true →
          ((bitsOf p.1).length : ℤ) ≤ (p_e + ((bitsOf v).length : ℤ) + 1) - 2 := by
        intro p hp hpt
        have hp' : p ∈ (v :: (w :: ws)).zip (false :: b' :: sel'') :=
          List.mem_cons_of_mem (v, false) hp
        have := hposlen p hp' hpt
        omega
      have hp2₂ : (2 : ℤ) ≤ p_e + ((bitsOf v).length : ℤ) + 1 := by omega
      have hm' : ((p_e + ((bitsOf v).length : ℤ) + 1 - 2).toNat) =
          ((p_e - 2).toNat) + ((bitsOf v).length + 1) := by
        have hc1 := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
        have hc2 := Int.toNat_of_nonneg
          (show (0 : ℤ) ≤ p_e + ((bitsOf v).length : ℤ) + 1 - 2 by omega)
        omega
      have hagr' : tapeAgrees cfg₁.tape (1 + (((p_e - 2).toNat) : ℤ))
          (List.replicate ((bitsOf v).length + 1) Sym.data0) := by
        have heq : (1 : ℤ) + (((p_e - 2).toNat) : ℤ) = p_e - 1 := by
          have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
          omega
        rw [heq]
        exact hagr
      have hR0₂ : chosenVal (w :: ws) (b' :: sel'') ≤
          regVal cfg₁.tape ((p_e + ((bitsOf v).length : ℤ) + 1 - 2).toNat) := by
        rw [hm']
        have hext : regVal cfg₁.tape (((p_e - 2).toNat) + ((bitsOf v).length + 1)) =
            regVal cfg₁.tape ((p_e - 2).toNat) :=
          regVal_zero_ext cfg₁.tape 1 ((p_e - 2).toNat) ((bitsOf v).length + 1) hagr'
        rw [hext]
        have hcongr : regVal cfg₁.tape ((p_e - 2).toNat) = regVal tape ((p_e - 2).toNat) := by
          unfold regVal
          exact regValA_congr_below tape cfg₁.tape 1 ((p_e - 2).toNat) 0
            (fun j _ => hleftn (1 + (j : ℤ)) (by omega))
        rw [hcongr]
        exact hR0
      -- ===== 尾递归（ih）=====
      rcases ih (b' :: sel'') hlen' (p_e + ((bitsOf v).length : ℤ) + 1) cfg₁.tape hne (by omega) hp2₂
        hpos1₂ hposlen₂ hface₂ hbound0₂ hboundL₂ hbwd0₂ hflag0₂ hterm₂ hR0₂ with
        ⟨π₂, cfg₂, hs₂, hst₂, hhd₂, hlen₂, hreg₂, htape0₂, hkd₂, hfl₂, htk₂, hz₂⟩
      -- ===== 拼接与出口装配 =====
      have e₀ : cfg₁ = SymConfig.mk 4 cfg₁.tape (p_e + ((bitsOf v).length : ℤ) + 1) := by
        rw [show cfg₁ = SymConfig.mk cfg₁.state cfg₁.tape cfg₁.headPos from rfl]
        rw [hst, hhd]
      have hcat : SymSteps VerifierSym.transition cfg₁ π₂ cfg₂ := by
        rw [e₀]
        exact hs₂
      have hlen'₂ : (π₁.length : ℤ) ≤ el (bitsOf v).length p_e := by
        have h5 : (π₁.length : ℤ) ≤ ((bitsOf v).length : ℤ) + 5 := by
          have hcast : (((bitsOf v).length + 5 : ℕ) : ℤ) = ((bitsOf v).length : ℤ) + 5 := by
            push_cast
            ring
          rw [← hcast]
          exact_mod_cast hlen₅
        have hel : ((bitsOf v).length : ℤ) + 5 ≤ el (bitsOf v).length p_e :=
          nosel_bound_le_el (bitsOf v).length p_e hp0
        linarith
      have hLlast : ((bitsOf ((v :: (w :: ws)).getLast hneCG)).length : ℤ) =
          ((bitsOf ((w :: ws).getLast hne)).length : ℤ) := by
        rw [List.getLast_cons hne]
      have hidx : p_e + ((encodeElementsSymWithSel (v :: (w :: ws)) (false :: b' :: sel'')).length : ℤ) -
          ((bitsOf ((v :: (w :: ws)).getLast hneCG)).length : ℤ) - 3 =
          (p_e + ((bitsOf v).length : ℤ) + 1) +
            ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ) -
            ((bitsOf ((w :: ws).getLast hne)).length : ℤ) - 3 := by
        rw [hWcons, hLlast]
        ring
      have hidxK : p_e + ((encodeElementsSymWithSel (v :: (w :: ws)) (false :: b' :: sel'')).length : ℤ) -
          ((bitsOf ((v :: (w :: ws)).getLast hneCG)).length : ℤ) - 3 =
          (p_e + ((bitsOf v).length : ℤ) + 1) +
            ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ) -
            ((bitsOf ((w :: ws).getLast hne)).length : ℤ) - 3 := by
        rw [hWcons, hLlast]
        ring
      refine ⟨π₁ ++ π₂, cfg₂, symSteps_append_concat π₁ π₂ hs₁ hcat, hst₂, ?_, ?_, ?_,
        htape0₂, ?_, ?_, ?_, ?_⟩
      · rw [hWcons]
        rw [show p_e + (1 + ((bitsOf v).length : ℤ) +
            ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ)) =
          p_e + ((bitsOf v).length : ℤ) + 1 +
            ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ) from by ring]
        exact hhd₂
      · rw [List.length_append]
        push_cast
        have hf : foldLenB ((v :: (w :: ws)).map (fun v => (bitsOf v).length)) p_e =
            el (bitsOf v).length p_e +
              foldLenB ((w :: ws).map (fun w => (bitsOf w).length))
                (p_e + ((bitsOf v).length : ℤ) + 1) := by
          rw [List.map_cons, foldLenB_cons]
        rw [hf]
        linarith [hlen'₂, hlen₂]
      · rw [hidx]
        have hchain : regVal cfg₁.tape ((p_e + ((bitsOf v).length : ℤ) + 1 - 2).toNat) =
            regVal tape ((p_e - 2).toNat) := by
          rw [hm']
          have hext : regVal cfg₁.tape (((p_e - 2).toNat) + ((bitsOf v).length + 1)) =
              regVal cfg₁.tape ((p_e - 2).toNat) :=
            regVal_zero_ext cfg₁.tape 1 ((p_e - 2).toNat) ((bitsOf v).length + 1) hagr'
          rw [hext]
          unfold regVal
          exact regValA_congr_below tape cfg₁.tape 1 ((p_e - 2).toNat) 0
            (fun j _ => hleftn (1 + (j : ℤ)) (by omega))
        rw [hchain] at hreg₂
        rw [chosenVal_cons_false]
        linarith [hreg₂]
      · intro i hi1 hi2
        have hi2' : i ≤ (p_e + ((bitsOf v).length : ℤ) + 1) +
            ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ) -
            ((bitsOf ((w :: ws).getLast hne)).length : ℤ) - 3 := by
          have h := hi2
          rw [hWcons, hLlast] at h
          omega
        exact hkd₂ i hi1 hi2'
      · intro i hi1 hi2
        have hi2' : i ≤ (p_e + ((bitsOf v).length : ℤ) + 1) +
            ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ) -
            ((bitsOf ((w :: ws).getLast hne)).length : ℤ) - 3 := by
          have h := hi2
          rw [hWcons, hLlast] at h
          omega
        exact hfl₂ i hi1 hi2'
      · rw [hWcons]
        rw [show p_e + (1 + ((bitsOf v).length : ℤ) +
            ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ)) =
          p_e + ((bitsOf v).length : ℤ) + 1 +
            ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ) from by ring]
        exact htk₂
      · intro i hi1 hi2
        have hidx2 : p_e + ((encodeElementsSymWithSel (v :: (w :: ws)) (false :: b' :: sel'')).length : ℤ) -
            ((bitsOf ((v :: (w :: ws)).getLast hneCG)).length : ℤ) - 2 =
            (p_e + ((bitsOf v).length : ℤ) + 1) +
              ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ) -
              ((bitsOf ((w :: ws).getLast hne)).length : ℤ) - 2 := by
          rw [hWcons, hLlast]
          ring
        have hidx3 : p_e + ((encodeElementsSymWithSel (v :: (w :: ws)) (false :: b' :: sel'')).length : ℤ) - 1 =
            (p_e + ((bitsOf v).length : ℤ) + 1) +
              ((encodeElementsSymWithSel (w :: ws) (b' :: sel'')).length : ℤ) - 1 := by
          rw [hWcons]
          ring
        rw [hidx2] at hi1
        rw [hidx3] at hi2
        exact hz₂ i hi1 hi2

/-- [T-P1.7 · 总装] 通用 fold：任意元素表/选择表（非空）自 (4, tape, p_e) 逐元素消费至 22。 -/
theorem run_fold_gen (elems : List ℕ) (sels : List Bool) : FoldSpec elems sels := by
  induction elems generalizing sels with
  | nil =>
      unfold FoldSpec
      intro hlen p_e tape hne
      exact absurd rfl hne
  | cons v rest ih =>
      unfold FoldSpec
      intro hlen p_e tape hneCG hp0 hp2 hpos1 hposlen hface hbound0 hboundL hbwd0 hflag0 hend1 hR0
      cases sels with
      | nil =>
          have h0 : (v :: rest).length = 0 := by simpa using hlen
          exact absurd (List.eq_nil_of_length_eq_zero h0) (by simp)
      | cons b sel' =>
          cases b with
          | true =>
              cases rest with
              | nil =>
                  have hsel0 : sel' = [] := by
                    have h := hlen
                    simp only [List.length_cons, List.length_nil] at h
                    exact List.eq_nil_of_length_eq_zero (by omega)
                  subst hsel0
                  exact fold_single_true v hlen p_e tape hneCG hp0 hp2 hpos1 hposlen hface
                    hbound0 hboundL hbwd0 hflag0 hend1 hR0
              | cons w ws =>
                  have hne : (w :: ws) ≠ [] := by simp
                  exact fold_cons_true v (w :: ws) sel' ih hlen hne hneCG p_e tape hp0 hp2
                    hpos1 hposlen hface hbound0 hboundL hbwd0 hflag0 hend1 hR0
          | false =>
              cases rest with
              | nil =>
                  have hsel0 : sel' = [] := by
                    have h := hlen
                    simp only [List.length_cons, List.length_nil] at h
                    exact List.eq_nil_of_length_eq_zero (by omega)
                  subst hsel0
                  exact fold_single_false v hlen p_e tape hneCG hp0 hp2 hpos1 hposlen hface
                    hbound0 hboundL hbwd0 hflag0 hend1 hR0
              | cons w ws =>
                  have hne : (w :: ws) ≠ [] := by simp
                  exact fold_cons_false v (w :: ws) sel' ih hlen hne hneCG p_e tape hp0 hp2
                    hpos1 hposlen hface hbound0 hboundL hbwd0 hflag0 hend1 hR0

/-! ========== T-P1.8 · ④判定段接件 ========== -/

/-- [T-P1.8 · ④判定] 判扫（强前件形）：自 (22, tape, p_e+W) 沿整带零区 [1, p_e+W−1] 扫回至 100。
    前件 = 线2 第五批前提族（标记/边界/全带零）；供 F1/F2 扩展后的 fold 出口对接。 -/
lemma run_judge_split (p_e : ℤ) (W : ℕ) (tape : ℤ → Sym)
    (hp0 : (0 : ℤ) ≤ p_e)
    (hp1 : (1 : ℤ) ≤ p_e + (W : ℤ))
    (hmark : tape (p_e + (W : ℤ)) = Sym.mk SymKind.boundary true)
    (hstrip : ∀ i : ℤ, 1 ≤ i → i ≤ p_e + (W : ℤ) - 1 → tape i = Sym.data0)
    (hbnd0 : tape 0 = Sym.boundary) :
    ∃ π cfg₂, SymSteps VerifierSym.transition
        (SymConfig.mk 22 tape (p_e + (W : ℤ))) π cfg₂ ∧
      π.length ≤ ((p_e + (W : ℤ)).toNat) + 2 ∧
      cfg₂.state = 100 ∧
      cfg₂.headPos = 1 ∧
      cfg₂.tape = tape := by
  have hTnn : 0 ≤ p_e + (W : ℤ) := by omega
  have hncast : (((p_e + (W : ℤ)).toNat : ℕ) : ℤ) = p_e + (W : ℤ) :=
    Int.toNat_of_nonneg hTnn
  have hcellr : ((((p_e + (W : ℤ)).toNat - 1 : ℕ) : ℤ)) + 1 = p_e + (W : ℤ) := by
    have h1 : 1 ≤ (p_e + (W : ℤ)).toNat := (Int.le_toNat hTnn).mpr hp1
    have h2 : ((p_e + (W : ℤ)).toNat - 1 + 1 : ℕ) = (p_e + (W : ℤ)).toNat :=
      Nat.sub_add_cancel h1
    calc (((p_e + (W : ℤ)).toNat - 1 : ℕ) : ℤ) + 1
        = (((p_e + (W : ℤ)).toNat - 1 + 1 : ℕ) : ℤ) := by push_cast; ring
      _ = (((p_e + (W : ℤ)).toNat : ℕ) : ℤ) := by rw [h2]
      _ = p_e + (W : ℤ) := hncast
  rcases segS3 (((p_e + (W : ℤ)).toNat) - 1) 0 tape
    (by
      rw [zero_add]
      rw [hcellr]
      exact hmark)
    (by
      intro i hi1 hi2
      rw [zero_add] at hi2
      have hi2' : i ≤ p_e + (W : ℤ) - 1 := by
        have h2 : (i : ℤ) ≤ (((p_e + (W : ℤ)).toNat : ℕ) : ℤ) - 1 := by
          have := hi2
          omega
        rw [hncast] at h2
        omega
      exact hstrip i hi1 hi2')
    hbnd0
    with ⟨π, cfg₂, hs, hlen, hst₂, hhd₂, htape⟩
  refine ⟨π, cfg₂, ?_, ?_, hst₂, ?_, htape⟩
  · have he : SymConfig.mk 22 tape (p_e + (W : ℤ)) =
        SymConfig.mk 22 tape (0 + ((((p_e + (W : ℤ)).toNat) - 1 : ℕ) : ℤ) + 1) := by
      congr 1
      rw [zero_add]
      exact hcellr.symm
    rw [he]
    exact hs
  · have h2 : (((p_e + (W : ℤ)).toNat) - 1 + 2) ≤ ((p_e + (W : ℤ)).toNat) + 2 := by omega
    linarith [hlen]
  · rw [hhd₂]
    norm_num

/-- [T-P1.8 · 判零转换] 末窗口区 kinds/flags + 值零（末窗口索引）+ 末自清区（+1 格）
    ⇒ 整带 `[0<i≤p_e+W−1]` 全 `data0`（线2 第五批路线：A 区零被 `all_d0_of_regVal_zero` 一并转换）。 -/
lemma judge_zero_region (tape : ℤ → Sym) (p_e W Llast : ℤ)
    (hL1 : 1 ≤ Llast)
    (hpos3 : 0 ≤ p_e + W - Llast - 3)
    (hkind : ∀ i : ℤ, 1 ≤ i → i ≤ p_e + W - Llast - 3 →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hflag : ∀ i : ℤ, 1 ≤ i → i ≤ p_e + W - Llast - 3 → (tape i).2 = false)
    (hreg0 : regVal tape ((p_e + W - Llast - 3).toNat) = 0)
    (hzone : ∀ i : ℤ, p_e + W - Llast - 2 ≤ i → i ≤ p_e + W - 1 → tape i = Sym.data0) :
    ∀ i : ℤ, 0 < i → i ≤ p_e + W - 1 → tape i = Sym.data0 := by
  intro i hi1 hi2
  by_cases hc : i ≤ p_e + W - Llast - 3
  · have hcast : (((p_e + W - Llast - 3).toNat : ℕ) : ℤ) = p_e + W - Llast - 3 :=
      Int.toNat_of_nonneg hpos3
    refine all_d0_of_regVal_zero tape ((p_e + W - Llast - 3).toNat) ?_ ?_ hreg0 i (by omega) ?_
    · intro j hj1 hj2
      rw [hcast] at hj2
      exact hkind j hj1 hj2
    · intro j hj1 hj2
      rw [hcast] at hj2
      exact hflag j hj1 hj2
    · rw [hcast]
      exact hc
  · push Not at hc
    exact hzone i (by omega) hi2

/-- [T-P1.8 · ③④合流] fold（③）+ 判扫（④）总装：出口整带零经 `judge_zero_region` 转换 ⇒ 100。
    语义前提 `hreg0eq`（族路径结构性可得；一般路径 = 语义层）供梯子全零。 -/
lemma run_fold_judge (elems : List ℕ) (sels : List Bool) (hlen : elems.length = sels.length)
    (hne : elems ≠ [])
    (p_e : ℤ) (tape : ℤ → Sym)
    (hp0 : (0 : ℤ) ≤ p_e)
    (hp2 : (2 : ℤ) ≤ p_e)
    (hp1 : (1 : ℤ) ≤ p_e + ((encodeElementsSymWithSel elems sels).length : ℤ))
    (hp3 : (0 : ℤ) ≤ p_e + ((encodeElementsSymWithSel elems sels).length : ℤ) -
      ((bitsOf (elems.getLast hne)).length : ℤ) - 3)
    (hL1 : 1 ≤ ((bitsOf (elems.getLast hne)).length : ℤ))
    (hpos1 : ∀ v ∈ elems, 1 ≤ v)
    (hposlen : ∀ p ∈ elems.zip sels, p.2 = true → ((bitsOf p.1).length : ℤ) ≤ p_e - 2)
    (hface : tapeAgrees tape p_e (encodeElementsSymWithSel elems sels))
    (hbound0 : tape (p_e - 1) = Sym.boundary)
    (hboundL : tape 0 = Sym.boundary)
    (hbwd0 : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hflag0 : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 → (tape i).2 = false)
    (hend1 : tape (p_e + ((encodeElementsSymWithSel elems sels).length : ℤ)) =
      Sym.mk SymKind.boundary true)
    (hR0 : chosenVal elems sels ≤ regVal tape ((p_e - 2).toNat))
    (hreg0eq : regVal tape ((p_e - 2).toNat) = chosenVal elems sels) :
    ∃ π cfg₂, SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) π cfg₂ ∧
      cfg₂.state = 100 ∧
      cfg₂.headPos = 1 ∧
      (π.length : ℤ) ≤ foldLenB (elems.map (fun v => (bitsOf v).length)) p_e +
        (((p_e + ((encodeElementsSymWithSel elems sels).length : ℤ)).toNat) + 2) := by
  obtain ⟨π₁, cfg_f, hrun_f, hst22, hhd, hlen_f, hreg_f, hbl_f, hkd_f, hfl_f,
    hmark_f, hzone_f⟩ :=
    run_fold_gen elems sels hlen p_e tape hne hp0 hp2 hpos1 hposlen hface hbound0 hboundL
      hbwd0 hflag0 hend1 hR0
  have hzfull := judge_zero_region cfg_f.tape p_e
    ((encodeElementsSymWithSel elems sels).length : ℤ)
    ((bitsOf (elems.getLast hne)).length : ℤ) hL1 hp3 hkd_f hfl_f
    (by rw [hreg_f, hreg0eq, sub_self]) hzone_f
  rcases run_judge_split p_e ((encodeElementsSymWithSel elems sels).length) cfg_f.tape
    hp0 hp1 hmark_f (fun i hi1 hi2 => hzfull i (by omega) hi2) hbl_f with
    ⟨π₂, cfg₂, hrun_j, hlen_j, hst₂, hhd₂, _htape⟩
  have e₀ : cfg_f = SymConfig.mk 22 cfg_f.tape
      (p_e + ((encodeElementsSymWithSel elems sels).length : ℤ)) := by
    rw [show cfg_f = SymConfig.mk cfg_f.state cfg_f.tape cfg_f.headPos from rfl]
    rw [hst22, hhd]
  have hcat : SymSteps VerifierSym.transition cfg_f π₂ cfg₂ := by
    rw [e₀]
    exact hrun_j
  refine ⟨π₁ ++ π₂, cfg₂, symSteps_append_concat π₁ π₂ hrun_f hcat, hst₂, hhd₂, ?_⟩
  rw [List.length_append]
  push_cast
  linarith [hlen_f, hlen_j]


-- ============================================================================
-- [P1 · 判段直长] 「100 路径」免费前提的直接榨取：判扫长度被状态流锁死
-- （22/23 行引理 + 101 锁定 + 洁净；不需任何带值/零区/语义前提）
-- ============================================================================

/-- 22 段：非陷阱 ⇒ next = 23。 -/
theorem state22_nexts (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 22 → r.nextState ≠ 101 → r.nextState = 23 := by
  cases m <;> cases k <;> decide

/-- 22 段：22→23 行 ⇒ L。 -/
theorem state22_L (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 22 → r.nextState = 23 → r.moveDir = Dir.L := by
  cases m <;> cases k <;> decide

/-- 23 段：非陷阱 ⇒ next ∈ {23, 100}。 -/
theorem state23_nexts (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 23 → r.nextState ≠ 101 → r.nextState = 23 ∨ r.nextState = 100 := by
  cases m <;> cases k <;> decide

/-- 23 段：23→23 行 ⇒ 读 data0 且 L。 -/
theorem state23_cont (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 23 → r.nextState = 23 → k = SymKind.data0 ∧ r.moveDir = Dir.L := by
  cases m <;> cases k <;> decide

/-- [P1·洁净空跑] 从状态 q 出发、无 q-出发步的运行必为空。 -/
lemma symSteps_eq_nil_of_clean {M : ℕ × Sym → Finset SymTransResult} {cfg₀ cfg : SymConfig}
    {π : List SymStep} (h : SymSteps M cfg₀ π cfg) (q : ℕ) (hq : cfg₀.state = q)
    (hclean : ∀ s ∈ π, s.fromState ≠ q) : π = [] := by
  cases π with
  | nil => rfl
  | cons step rest =>
      obtain ⟨cfg₁, h1, _⟩ := symSteps_append_split (M := M) (π₀ := [step]) (rest := rest)
        (by simpa using h)
      obtain ⟨hf, _, _, _⟩ := symSteps_singleton_facts h1
      exact absurd (hf.trans hq) (hclean step (by simp))

/-- [P1·判扫直长] 自 (23, h) 出发、终态 100 的判扫运行：长度 ≤ h + 1。
    格 0 为 boundary（判刀墙：0 以下不可续走）；洁净（无 100-出发步）。 -/
lemma scan23_len_le {c c' : SymConfig} {π : List SymStep}
    (h : SymSteps VerifierSym.transition c π c') (hst : c.state = 23)
    (h'st : c'.state = 100) (hhp : 0 ≤ c.headPos)
    (hz : (c.tape 0).1 = SymKind.boundary)
    (hclean : ∀ s ∈ π, s.fromState ≠ 100) :
    (π.length : ℤ) ≤ c.headPos + 1 := by
  have key : ∀ n, ∀ (c : SymConfig) (π : List SymStep) (c' : SymConfig),
      π.length = n →
      SymSteps VerifierSym.transition c π c' → c.state = 23 → c'.state = 100 →
      0 ≤ c.headPos → (c.tape 0).1 = SymKind.boundary →
      (∀ s ∈ π, s.fromState ≠ 100) → (π.length : ℤ) ≤ c.headPos + 1 := by
    intro n
    induction n with
    | zero =>
        intro c π c' hlen h hst h'st hhp hz hclean
        cases π with
        | nil => simp; omega
        | cons a t => simp at hlen
    | succ n ih =>
        intro c π c' hlen h hst h'st hhp hz hclean
        have hlock := symSteps_next_ne101_of_end_ne101 h (by rw [h'st]; decide)
        obtain ⟨step, rest, rfl⟩ : ∃ s t, π = s :: t := by
          cases π with
          | nil => simp at hlen
          | cons a t => exact ⟨a, t, rfl⟩
        have hlen' : rest.length = n := by have := hlen; simp [List.length_cons] at this; omega
        obtain ⟨cfg₁, h1, hrst⟩ := symSteps_append_split (M := VerifierSym.transition)
          (π₀ := [step]) (rest := rest) (by simpa using h)
        obtain ⟨hf, hr, hmem, hcfg⟩ := symSteps_singleton_facts h1
        have hlt : step.fromState < 102 :=
          legalStates_lt_102 step.fromState (by rw [hf, hst]; decide)
        rcases hrk : c.tape c.headPos with ⟨k, b⟩
        have hm : step.result ∈ VerifierSym.transition ((step.fromState : ℕ), (k, b)) := by
          have h1m : step.result ∈ VerifierSym.transition
              ((step.fromState : ℕ), c.tape c.headPos) := by
            simpa [← hf] using hmem
          simpa [hrk] using h1m
        have hno101 : step.result.nextState ≠ 101 := hlock step (by simp)
        have hnexts := state23_nexts k b ⟨step.fromState, hlt⟩ step.result hm
          (by simp [hf, hst]) hno101
        rcases hnexts with h23 | h100
        · -- 续扫一格
          have hcont := state23_cont k b ⟨step.fromState, hlt⟩ step.result hm
            (by simp [hf, hst]) h23
          have hk0 : k = SymKind.data0 := hcont.1
          have hmd : step.result.moveDir = Dir.L := hcont.2
          have hcfg1s : cfg₁.state = 23 := by simp [hcfg, symStepConfig, h23]
          have hcfg1h : cfg₁.headPos = c.headPos + (-1) := by
            simp [hcfg, symStepConfig, hmd, Dir.toInt]
          have hhead_ne : c.headPos ≠ 0 := by
            intro h0
            have hc0 : c.tape 0 = (k, b) := by rw [← h0]; exact hrk
            have hs1 : (c.tape 0).1 = SymKind.data0 := by rw [hc0]; exact hk0
            have h2 : (SymKind.data0 : SymKind) = SymKind.boundary := by
              rw [← hs1]; exact hz
            nomatch h2
          have hhp' : 0 ≤ cfg₁.headPos := by rw [hcfg1h]; omega
          have hz' : (cfg₁.tape 0).1 = SymKind.boundary := by
            have h0v : (symStepConfig c step.result).tape 0 = c.tape 0 := by
              show (if (0 : ℤ) = c.headPos then step.result.writeSym else c.tape 0) = c.tape 0
              rw [if_neg (fun hh => hhead_ne hh.symm)]
            rw [hcfg, h0v]; exact hz
          have hclean' : ∀ s ∈ rest, s.fromState ≠ 100 :=
            fun s hs => hclean s (List.mem_cons_of_mem step hs)
          have ih' := ih cfg₁ rest c' hlen' hrst hcfg1s h'st hhp' hz' hclean'
          rw [hcfg1h] at ih'
          have hlenc : ((step :: rest).length : ℤ) = (rest.length : ℤ) + 1 := by simp
          omega
        · -- 到 #ₗ：接受
          have hcfg1s : cfg₁.state = 100 := by simp [hcfg, symStepConfig, h100]
          have hnil : rest = [] := symSteps_eq_nil_of_clean hrst 100 hcfg1s
            (fun s hs => hclean s (List.mem_cons_of_mem step hs))
          have hlenc : ((step :: rest).length : ℤ) = 1 := by rw [hnil]; rfl
          rw [hlenc]; omega
  exact key π.length c π c' rfl h hst h'st hhp hz hclean

/-- [P1·判段直长] 自 (22, h) 出发、终态 100 的判扫段（折叠出口 ⇒ 接受）：长度 ≤ h + 1。
    h100 免费（终态 100）+ 洁净；h ≥ 1（22 行唯一合法读为 (boundary, true)）。 -/
lemma judge_len_le {c c' : SymConfig} {π : List SymStep}
    (h : SymSteps VerifierSym.transition c π c') (hst : c.state = 22)
    (h'st : c'.state = 100) (hhp : 1 ≤ c.headPos)
    (hz : (c.tape 0).1 = SymKind.boundary)
    (hclean : ∀ s ∈ π, s.fromState ≠ 100) :
    (π.length : ℤ) ≤ c.headPos + 1 := by
  have hlock := symSteps_next_ne101_of_end_ne101 h (by rw [h'st]; decide)
  cases π with
  | nil => simp; omega
  | cons step rest =>
      obtain ⟨cfg₁, h1, hrst⟩ := symSteps_append_split (M := VerifierSym.transition)
        (π₀ := [step]) (rest := rest) (by simpa using h)
      obtain ⟨hf, hr, hmem, hcfg⟩ := symSteps_singleton_facts h1
      have hlt : step.fromState < 102 :=
        legalStates_lt_102 step.fromState (by rw [hf, hst]; decide)
      rcases hrk : c.tape c.headPos with ⟨k, b⟩
      have hm : step.result ∈ VerifierSym.transition ((step.fromState : ℕ), (k, b)) := by
        have h1m : step.result ∈ VerifierSym.transition
            ((step.fromState : ℕ), c.tape c.headPos) := by
          simpa [← hf] using hmem
        simpa [hrk] using h1m
      have hno101 : step.result.nextState ≠ 101 := hlock step (by simp)
      have hj23 := state22_nexts k b ⟨step.fromState, hlt⟩ step.result hm
        (by simp [hf, hst]) hno101
      have hmd : step.result.moveDir = Dir.L := state22_L k b ⟨step.fromState, hlt⟩
        step.result hm (by simp [hf, hst]) hj23
      have hcfg1s : cfg₁.state = 23 := by simp [hcfg, symStepConfig, hj23]
      have hcfg1h : cfg₁.headPos = c.headPos + (-1) := by
        simp [hcfg, symStepConfig, hmd, Dir.toInt]
      have hhead_ne : c.headPos ≠ 0 := by omega
      have hhp' : 0 ≤ cfg₁.headPos := by rw [hcfg1h]; omega
      have hz' : (cfg₁.tape 0).1 = SymKind.boundary := by
        have h0v : (symStepConfig c step.result).tape 0 = c.tape 0 := by
          show (if (0 : ℤ) = c.headPos then step.result.writeSym else c.tape 0) = c.tape 0
          rw [if_neg (fun hh => hhead_ne hh.symm)]
        rw [hcfg, h0v]; exact hz
      have hclean' : ∀ s ∈ rest, s.fromState ≠ 100 :=
        fun s hs => hclean s (List.mem_cons_of_mem step hs)
      have ih' := scan23_len_le hrst hcfg1s h'st hhp' hz' hclean'
      rw [hcfg1h] at ih'
      have hlenc : ((step :: rest).length : ℤ) = (rest.length : ℤ) + 1 := by simp
      omega


-- ============================================================================
-- [CBTM·Sym 表级] β 行：任意非吸收态读 β 唯一结果 = (101, β, S)
-- （用户交底：「bβ 在 CBTM Symbol 版中被设置为 101」；锦标对应 CBTM4:179-183 / Core:415 / Core2:2091,2224）
-- ============================================================================

/-- β 行（Fin 102 框架）：q ≠ 100 时，读 β 的唯一结果为 101。 -/
theorem beta_row_101 (m : Bool) :
    ∀ (q : Fin 102), (q : ℕ) ≠ 100 →
      ∀ r ∈ VerifierSym.transition ((q : ℕ), Sym.mk SymKind.beta m),
        r.nextState = 101 := by
  cases m <;> decide

/-- β 行（任意 ℕ 态）：q ≠ 100 时，读 β 的唯一结果为 101。
    （表外态走 else 支 ⇒ {101, β, S}；表内态 q ≠ 100 由 β 行/默认臂/101 吸收行 均归 101。） -/
theorem beta_row_101_nat (m : Bool) (q : ℕ) (hq : q ≠ 100) :
    ∀ r ∈ VerifierSym.transition (q, Sym.mk SymKind.beta m), r.nextState = 101 := by
  by_cases hmem : q ∈ VerifierSym.legalStates
  · exact beta_row_101 m ⟨q, legalStates_lt_102 q hmem⟩ hq
  · intro r hr
    simp [VerifierSym.transition, hmem] at hr
    rw [hr]

-- 逐步转移成员：见前文 `symSteps_step_mem`（R13A:513，勿重复定义）。


-- ============================================================================
-- [P1 · 尾段分解与界（A1/A2）] 自 cf₁（4 态、元素区 WithSel 面）至 100 的尾段：
-- 规范折叠段（`run_fold_gen`）+ 判扫段（`judge_len_le`）合成界。
-- 前提注：`hR0`/`hfit`/`hne` 属「免费域操作化」（A5）供给位。
-- ============================================================================

/-- [P1·尾段工具] 自任意 q₀（3 ≤ q₀ ≤ 101）起的运行全态 ≥ 3（含末态）。
    （`symSteps_ge3` 的起始态泛化版；`transition_ge3_closed` 直接消化。） -/
lemma symSteps_ge3_of {t : ℤ → Sym} {p : ℤ} {q₀ : ℕ} {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition (SymConfig.mk q₀ t p) π cfg)
    (hq3 : 3 ≤ q₀) (hq101 : q₀ ≤ 101) :
    3 ≤ cfg.state ∧ ∀ s ∈ π, 3 ≤ s.fromState ∧ 3 ≤ s.result.nextState := by
  induction h with
  | nil =>
      refine ⟨?_, ?_⟩
      · show 3 ≤ q₀
        exact hq3
      · intro s hs
        simp at hs
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      obtain ⟨ihst, ihsteps⟩ := ih
      have hq101' : cfg₁.state ≤ 101 := (symSteps_state_le101 hprev hq101).1
      have hnext3 : 3 ≤ step.result.nextState := by
        have hm3 : step.result ∈ VerifierSym.transition (cfg₁.state, step.readSym) := by
          rw [hread]
          exact htrans
        cases hrd : step.readSym with
        | mk k m =>
            rw [hrd] at hm3
            exact transition_ge3_closed cfg₁.state (by omega) k m ihst step.result hm3
      refine ⟨?_, ?_⟩
      · rw [show (symStepConfig cfg₁ step.result).state = step.result.nextState from rfl]
        exact hnext3
      · intro s hs
        rcases List.mem_append.mp hs with hs' | hs'
        · exact ihsteps s hs'
        · rw [List.mem_singleton] at hs'
          subst hs'
          exact ⟨by rw [hfrom]; exact ihst, hnext3⟩

/-- [P1·尾段工具] 自 q₀ = 4 起的运行：全程无 2-态步（hno2；`symSteps_prefix_comp` 侧条件）。 -/
lemma symSteps_no2_of_four {t : ℤ → Sym} {p : ℤ} {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition (SymConfig.mk 4 t p) π cfg) :
    ∀ s ∈ π, s.fromState ≠ 2 := by
  have h3 := symSteps_ge3_of h (by norm_num) (by norm_num)
  intro s hs h2
  have := (h3.2 s hs).1
  omega

/-- [P1·尾段分解与界 A1/A2] 自 cf₁（4 态、元素区 WithSel 面、p_e = 2+|tb|）至 100 的洁净运行 π₁：
    `|π₁| ≤ foldLenB bs p_e + (p_e + |W| + 1)`。
    手法：`run_fold_gen` 构造规范折叠 σf（自 cf₁）+ `symSteps_prefix_comp` 双支：
    前缀支直结；延伸支尾段用 `judge_len_le` 直结（零语义前提）。 -/
lemma run_tail_len_le {inst : SubsetSumInstance} {sel : List Bool} {cf₁ cfg : SymConfig}
    {π₁ : List SymStep}
    (hne : inst.elements ≠ [])
    (hsel_len : sel.length = inst.elements.length)
    (hpos : ∀ v ∈ inst.elements, 1 ≤ v)
    (hfit : ∀ p ∈ inst.elements.zip sel, p.2 = true →
      ((bitsOf p.1).length : ℤ) ≤ ((encodeBitsSym inst.target).length : ℤ))
    (hst : cf₁.state = 4)
    (hhp : cf₁.headPos = 2 + ((encodeBitsSym inst.target).length : ℤ))
    (hface : tapeAgrees cf₁.tape (2 + ((encodeBitsSym inst.target).length : ℤ))
      (encodeElementsSymWithSel inst.elements sel))
    (hbnd0 : cf₁.tape (1 + ((encodeBitsSym inst.target).length : ℤ)) = Sym.boundary)
    (hbndL : cf₁.tape 0 = Sym.boundary)
    (hkinds : ∀ i : ℤ, 1 ≤ i → i ≤ ((encodeBitsSym inst.target).length : ℤ) →
      (cf₁.tape i).1 = SymKind.data0 ∨ (cf₁.tape i).1 = SymKind.data1)
    (hmarks : ∀ i : ℤ, 1 ≤ i → i ≤ ((encodeBitsSym inst.target).length : ℤ) →
      (cf₁.tape i).2 = false)
    (hterm : cf₁.tape (2 + ((encodeBitsSym inst.target).length : ℤ) +
      ((encodeElementsSym inst.elements).length : ℤ)) = Sym.mk SymKind.boundary true)
    (hR0 : chosenVal inst.elements sel ≤
      regVal cf₁.tape (((2 + ((encodeBitsSym inst.target).length : ℤ)) - 2).toNat))
    (hrun : SymSteps VerifierSym.transition cf₁ π₁ cfg)
    (h100 : cfg.state = 100)
    (hclean : ∀ s ∈ π₁, s.fromState ≠ 100) :
    (π₁.length : ℤ) ≤
      foldLenB (inst.elements.map (fun v => (bitsOf v).length))
          (2 + ((encodeBitsSym inst.target).length : ℤ)) +
        (2 + ((encodeBitsSym inst.target).length : ℤ) +
          ((encodeElementsSymWithSel inst.elements sel).length : ℤ) + 1) := by
  -- 规范折叠段 σf：run_fold_gen（前提族逐一消解）
  obtain ⟨σf, cfgf, hσf, hcfgfs, hcfgfh, hσflen, _hregv, hcfgf0, _hkf, _hmf, _htf, _hzf⟩ :=
    run_fold_gen inst.elements sel hsel_len.symm
      (2 + ((encodeBitsSym inst.target).length : ℤ)) cf₁.tape
      hne (by omega) (by omega) hpos
      (by
        intro p hp hpt
        have := hfit p hp hpt
        omega)
      hface
      (by
        have h1 : (2 : ℤ) + ((encodeBitsSym inst.target).length : ℤ) - 1 =
            1 + ((encodeBitsSym inst.target).length : ℤ) := by ring
        rw [h1]
        exact hbnd0)
      hbndL
      (by
        intro i h1 h2
        exact hkinds i h1 (by omega))
      (by
        intro i h1 h2
        exact hmarks i h1 (by omega))
      (by
        rw [WithSel_length inst.elements sel hsel_len]
        exact hterm)
      hR0
  -- 起始配置对齐（σf 与 π₁ 同起点）
  have hcf₁eq : cf₁ =
      SymConfig.mk 4 cf₁.tape (2 + ((encodeBitsSym inst.target).length : ℤ)) := by
    rw [← hst, ← hhp]
  rw [hcf₁eq] at hrun
  -- hno2：σf 无 2-态步
  have hno2 : ∀ s ∈ σf, s.fromState ≠ 2 := symSteps_no2_of_four hσf
  -- 前缀相容双支
  rcases symSteps_prefix_comp hσf hrun (by norm_num) hno2 with
    ⟨r, hEq, hrest⟩ | ⟨r, hEq, hrest⟩
  · -- A 支：π₁ = σf ++ r，r 判扫（自 22 至 100）
    have hjl : (r.length : ℤ) ≤ cfgf.headPos + 1 :=
      judge_len_le hrest hcfgfs h100
        (by omega)
        (by simpa [Sym.boundary, Sym.mk] using congrArg Prod.fst hcfgf0)
        (by
          intro s hs
          exact hclean s (by rw [hEq]; exact List.mem_append.mpr (Or.inr hs)))
    have hlenA : (π₁.length : ℤ) = (σf.length : ℤ) + (r.length : ℤ) := by
      have := congrArg List.length hEq
      simp [List.length_append] at this
      omega
    rw [hlenA]
    have hbr : cfgf.headPos + 1 ≤
        2 + ((encodeBitsSym inst.target).length : ℤ) +
          ((encodeElementsSymWithSel inst.elements sel).length : ℤ) + 1 := by
      omega
    omega
  · -- B 支：σf = π₁ ++ r（前缀直结）
    have hlenB : (π₁.length : ℤ) ≤ (σf.length : ℤ) := by
      have := congrArg List.length hEq
      simp [List.length_append] at this
      omega
    have : (π₁.length : ℤ) ≤ foldLenB (inst.elements.map (fun v => (bitsOf v).length))
        (2 + ((encodeBitsSym inst.target).length : ℤ)) := le_trans hlenB hσflen
    omega


/-- [P1·A4 全段界合成] 四段界算术合成：`π = π₀ ++ step₃ :: (ρ ++ π₁)`
    的三段界（①定长 / ②ρ 界 / ③④ 合成界）⇙ 全段界。
    （下游：C1 供给实例化时由 `run_format_split` + `run_tail_len_le` 供各段界。） -/
lemma phases_len_le {inst : SubsetSumInstance} {π π₀ ρ π₁ : List SymStep}
    {step₃ : SymStep} {sel : List Bool}
    (hsplit : π = π₀ ++ step₃ :: (ρ ++ π₁))
    (h₀ : (π₀.length : ℤ) = 2 + ((encodeBitsSym inst.target).length : ℤ) +
        ((encodeElementsSym inst.elements).length : ℤ))
    (hρ : (ρ.length : ℤ) ≤ 2 * (3 + (encodeBitsSym inst.target).length +
        (encodeElementsSym inst.elements).length))
    (h₁ : (π₁.length : ℤ) ≤
      foldLenB (inst.elements.map (fun v => (bitsOf v).length))
          (2 + ((encodeBitsSym inst.target).length : ℤ)) +
        (2 + ((encodeBitsSym inst.target).length : ℤ) +
          ((encodeElementsSymWithSel inst.elements sel).length : ℤ) + 1)) :
    (π.length : ℤ) ≤
      (2 + ((encodeBitsSym inst.target).length : ℤ) +
        ((encodeElementsSym inst.elements).length : ℤ)) + 1 +
      (2 * (3 + (encodeBitsSym inst.target).length +
        (encodeElementsSym inst.elements).length)) +
      (foldLenB (inst.elements.map (fun v => (bitsOf v).length))
          (2 + ((encodeBitsSym inst.target).length : ℤ)) +
        (2 + ((encodeBitsSym inst.target).length : ℤ) +
          ((encodeElementsSymWithSel inst.elements sel).length : ℤ) + 1)) := by
  have hlen : (π.length : ℤ) =
      (π₀.length : ℤ) + 1 + ((ρ.length : ℤ) + (π₁.length : ℤ)) := by
    have := congrArg List.length hsplit
    simp [List.length_append, List.length_cons] at this
    omega
  rw [hlen]
  omega

-- ============================================================================
-- [C1 · 工具] 输入前缀归约：自 `encS inst ++ gS` 起、全头 < |encS inst| 的运行
-- 也是自 `encS inst` 的合法运行（初始带在 {i < |encS|} 上一致 + 写入局限）。
-- ============================================================================

/-- [C1·工具] 前接合流：`[step]` 跑到 `c₁`、`rest` 从 `c₁` 续跑 ⇒ `step :: rest` 整跑。 -/
lemma symSteps_front_cons {c c₁ : SymConfig} {step : SymStep}
    {rest : List SymStep} {cfg : SymConfig}
    (h₁ : SymSteps VerifierSym.transition c [step] c₁)
    (h₂ : SymSteps VerifierSym.transition c₁ rest cfg) :
    SymSteps VerifierSym.transition c (step :: rest) cfg := by
  induction h₂ with
  | nil => simpa using h₁
  | cons πs st cfg' hprev hf hr hm ih =>
      exact SymSteps.cons (step :: πs) st cfg' ih hf hr hm

/-- [C1·工具·主件] 两配置带在 `{i | i < |encS inst|}` 上一致、态/头相同、运行全头落在该域内
    ⇒ 运行从左侧配置合法，且末配置在该域上与右侧末配置一致。 -/
lemma symSteps_of_agree_left {inst : SubsetSumInstance} {c₁ c₂ cfg : SymConfig} {π : List SymStep}
    (hstate : c₁.state = c₂.state) (hhead : c₁.headPos = c₂.headPos)
    (htape : ∀ i : ℤ, i < ((encodeInstanceSym inst).length : ℤ) → c₁.tape i = c₂.tape i)
    (h : SymSteps VerifierSym.transition c₂ π cfg)
    (hconf : ∀ k, k < π.length →
      ((π.take k).map (fun st => st.result.moveDir.toInt)).sum + c₂.headPos <
        ((encodeInstanceSym inst).length : ℤ)) :
    ∃ cfg', SymSteps VerifierSym.transition c₁ π cfg' ∧
      cfg'.state = cfg.state ∧ cfg'.headPos = cfg.headPos ∧
      ∀ i : ℤ, i < ((encodeInstanceSym inst).length : ℤ) → cfg'.tape i = cfg.tape i := by
  have key : ∀ n, ∀ (c₁ c₂ cfg : SymConfig) (π : List SymStep), π.length = n →
      c₁.state = c₂.state → c₁.headPos = c₂.headPos →
      (∀ i : ℤ, i < ((encodeInstanceSym inst).length : ℤ) → c₁.tape i = c₂.tape i) →
      SymSteps VerifierSym.transition c₂ π cfg →
      (∀ k, k < π.length →
        ((π.take k).map (fun st => st.result.moveDir.toInt)).sum + c₂.headPos <
          ((encodeInstanceSym inst).length : ℤ)) →
      ∃ cfg', SymSteps VerifierSym.transition c₁ π cfg' ∧
        cfg'.state = cfg.state ∧ cfg'.headPos = cfg.headPos ∧
        ∀ i : ℤ, i < ((encodeInstanceSym inst).length : ℤ) → cfg'.tape i = cfg.tape i := by
    intro n
    induction n with
    | zero =>
        intro c₁ c₂ cfg π hlen hstate hhead htape h hconf
        cases π with
        | nil =>
            rw [symSteps_nil_cfg h]
            exact ⟨c₁, SymSteps.nil, hstate, hhead, htape⟩
        | cons a t =>
            simp only [List.length_cons] at hlen
            omega
    | succ n ih =>
        intro c₁ c₂ cfg π hlen hstate hhead htape h hconf
        cases π with
        | nil => simp at hlen
        | cons step rest =>
            obtain ⟨c₂', hstep, hrest⟩ := symSteps_append_split (π₀ := [step]) (rest := rest)
              (by simpa using h)
            obtain ⟨hf, hr, hmem, hcfg₂'⟩ := symSteps_singleton_facts hstep
            have hlen_rest : rest.length = n := by
              simp only [List.length_cons] at hlen
              omega
            have hhead0 : c₂.headPos < ((encodeInstanceSym inst).length : ℤ) := by
              have := hconf 0 (by simp)
              simpa using this
            have hread : c₁.tape c₁.headPos = c₂.tape c₂.headPos := by
              rw [hhead]
              exact htape c₂.headPos hhead0
            have hmem₁ : step.result ∈
                VerifierSym.transition (c₁.state, c₁.tape c₁.headPos) := by
              have hm := hmem
              rw [← hf, ← hr] at hm
              rw [hstate, ← hf, hread, ← hr]
              exact hm
            have hf₁ : step.fromState = c₁.state := hf.trans hstate.symm
            have hr₁ : step.readSym = c₁.tape c₁.headPos := hr.trans hread.symm
            have hstep₁ : SymSteps VerifierSym.transition c₁ [step]
                (symStepConfig c₁ step.result) :=
              SymSteps.cons [] step c₁ SymSteps.nil hf₁ hr₁ hmem₁
            have hstate' : (symStepConfig c₁ step.result).state =
                (symStepConfig c₂ step.result).state := rfl
            have hhead' : (symStepConfig c₁ step.result).headPos =
                (symStepConfig c₂ step.result).headPos := by
              simp only [symStepConfig]
              rw [hhead]
            have htape' : ∀ i : ℤ, i < ((encodeInstanceSym inst).length : ℤ) →
                (symStepConfig c₁ step.result).tape i =
                  (symStepConfig c₂ step.result).tape i := by
              intro i hi
              simp only [symStepConfig]
              by_cases hih : i = c₂.headPos
              · rw [if_pos (by rw [hhead]; exact hih), if_pos hih]
              · rw [if_neg (by rw [hhead]; exact hih), if_neg hih]
                exact htape i hi
            have hconf' : ∀ k, k < rest.length →
                ((rest.take k).map (fun st => st.result.moveDir.toInt)).sum +
                  (symStepConfig c₂ step.result).headPos <
                  ((encodeInstanceSym inst).length : ℤ) := by
              intro k hk
              have hk1 : k + 1 < (step :: rest).length := by
                simp only [List.length_cons]
                omega
              have hfull := hconf (k + 1) hk1
              simp only [List.take_succ_cons, List.map_cons, List.sum_cons, symStepConfig] at hfull
              simp only [symStepConfig]
              linarith [hfull]
            obtain ⟨cfg', hleft, hst', hhd', htp'⟩ :=
              ih (symStepConfig c₁ step.result) (symStepConfig c₂ step.result) cfg rest
                hlen_rest hstate' hhead' htape' (hcfg₂' ▸ hrest) hconf'
            exact ⟨cfg', symSteps_front_cons hstep₁ hleft, hst', hhd', htp'⟩
  exact key π.length c₁ c₂ cfg π rfl hstate hhead htape h hconf

/-- [C1·工具·实例] 输入 `encS inst ++ gS` 的运行（全头 < |encS inst|）也是自 `encS inst` 的运行。 -/
lemma symSteps_input_append_left {inst : SubsetSumInstance} {gS : List Sym}
    {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition
      (symInitialConfig (encodeInstanceSym inst ++ gS)) π cfg)
    (hconf : ∀ k, k < π.length →
      ((π.take k).map (fun st => st.result.moveDir.toInt)).sum <
        ((encodeInstanceSym inst).length : ℤ)) :
    ∃ cfg', SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π cfg' ∧
      cfg'.state = cfg.state ∧ cfg'.headPos = cfg.headPos ∧
      ∀ i : ℤ, i < ((encodeInstanceSym inst).length : ℤ) → cfg'.tape i = cfg.tape i := by
  have htape₀ : ∀ i : ℤ, i < ((encodeInstanceSym inst).length : ℤ) →
      (symInitialConfig (encodeInstanceSym inst)).tape i =
        (symInitialConfig (encodeInstanceSym inst ++ gS)).tape i := by
    intro i hi
    simp only [symInitialConfig]
    by_cases h0 : 0 ≤ i
    · have hi_nat : i.toNat < (encodeInstanceSym inst).length := by
        have : (i.toNat : ℤ) = i := Int.toNat_of_nonneg h0
        omega
      have hi_nat₂ : i.toNat < (encodeInstanceSym inst ++ gS).length := by
        rw [List.length_append]
        omega
      have hc₁ : (0 ≤ i ∧ i.toNat < (encodeInstanceSym inst).length) := ⟨h0, hi_nat⟩
      have hc₂ : (0 ≤ i ∧ i.toNat < (encodeInstanceSym inst ++ gS).length) := ⟨h0, hi_nat₂⟩
      simp only [dif_pos hc₁, dif_pos hc₂]
      exact (List.getElem_append_left hi_nat).symm
    · have hlt : ¬ (0 ≤ i ∧ i.toNat < (encodeInstanceSym inst).length) := fun h => h0 h.1
      have hlt₂ : ¬ (0 ≤ i ∧ i.toNat < (encodeInstanceSym inst ++ gS).length) := fun h => h0 h.1
      simp only [dif_neg hlt, dif_neg hlt₂]
  have hconf₀ : ∀ k, k < π.length →
      ((π.take k).map (fun st => st.result.moveDir.toInt)).sum +
        (symInitialConfig (encodeInstanceSym inst ++ gS)).headPos <
        ((encodeInstanceSym inst).length : ℤ) := by
    intro k hk
    simpa [symInitialConfig] using hconf k hk
  obtain ⟨cfg', hleft, hst', hhd', htp'⟩ := symSteps_of_agree_left (inst := inst)
    (c₁ := symInitialConfig (encodeInstanceSym inst))
    (c₂ := symInitialConfig (encodeInstanceSym inst ++ gS))
    (cfg := cfg) (π := π) rfl rfl htape₀ h hconf₀
  exact ⟨cfg', hleft, hst', hhd', htp'⟩


end Mp
