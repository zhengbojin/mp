/- A2 桥（A2 公理消去的核心定理）：F4 符号版 + 直铺输入 + 符号驱动分支。
   输入 = F4 串（2bit 符号，空白符在符号集内自带编码）；NTM2 与 CBTM 同字母表、
   同格局（state, tape, headPos）、转移恒等翻译 → 同构桥恒等。
   规范 NTM2（NTM2.Canonical）保证任意可达路径的磁头只在输入区内活动。 -/
import Mp.Basic
import Mp.CBTM
import Mp.IVM
import Mp.SubsetSumVerifierCBTM


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
open IVM

-- ======================================================================
-- 结构同构保持接受语言（A2 公理消去的核心定理；规范 NTM2 版）
-- ======================================================================

/-- NTM2 输入 → CBTM 输入：恒等（同字母表 F4，输入直铺）。 -/
def ntm2InputToCBTM (A : NTM2) (x : List F4) : List F4 := x

/-- NTM2 配置 → CBTM 配置：恒等（格局同型：state, tape, headPos）。 -/
def ntm2CfgToCBTM (A : NTM2) (M : CBTM) (iso : StructIsoNTM2CBTM A M)
    {x : List F4} (cfg : NTM2Config A x) : CBTMConfig M x :=
  { state := cfg.state, tape := cfg.tape, headPos := cfg.headPos }

/-- 初始配置的对应（恒等；空白符经 iso.h_blank 对应）。 -/
lemma iso_initial_corresp (A : NTM2) (M : CBTM) (iso : StructIsoNTM2CBTM A M) (x : List F4) :
    ntm2CfgToCBTM A M iso (NTM2InitialConfig A x) = initialConfig M x := by
  unfold ntm2CfgToCBTM NTM2InitialConfig initialConfig NTM2InitialTape initialTapeOf
  rw [iso.h_start]
  congr
  funext i
  by_cases h : 0 ≤ i ∧ i.toNat < x.length <;> simp [h, iso.h_blank]

/-- 非负整数：ℤ 界 < ↑n 蕴含 toNat 界 < n。 -/
lemma int_toNat_lt_of_lt (i : ℤ) (n : ℕ) (h0 : 0 ≤ i) (hlt : i < (n : ℤ)) :
    i.toNat < n := by
  exact (Int.toNat_lt (n := n) h0).mpr hlt

/-- Int.toNat 在非负整数上单射。 -/
lemma int_toNat_inj_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a.toNat = b.toNat → a = b := by
  intro h
  have hz : (a.toNat : ℤ) = (b.toNat : ℤ) := congrArg (fun n : ℕ => (n : ℤ)) h
  rw [Int.toNat_of_nonneg ha] at hz
  rw [Int.toNat_of_nonneg hb] at hz
  exact hz

/-- 互异的自然数列表，元素都 < n → 长度 ≤ n（鸽巢：n 个候选位置，互异元素至多 n 个）。 -/
lemma nat_nodup_lt_length_le (l : List ℕ) (n : ℕ)
    (hnodup : l.Nodup) (hlt : ∀ q ∈ l, q < n) : l.length ≤ n := by
  have hcard : l.toFinset.card = l.length := List.toFinset_card_of_nodup hnodup
  rw [← hcard]
  have hle : l.toFinset.card ≤ (Finset.range n).card := Finset.card_le_card (by
    intro q hq
    rw [Finset.mem_range]
    exact hlt q (List.mem_toFinset.mp hq))
  rwa [Finset.card_range] at hle

/-- 互异的非负整数列表，元素都 < n → 长度 ≤ n。 -/
lemma int_nodup_bounded_length (l : List ℤ) (n : ℕ)
    (hnodup : l.Nodup) (h0 : ∀ p ∈ l, 0 ≤ p) (hlt : ∀ p ∈ l, p < n) :
    l.length ≤ n := by
  have hmap_nodup : (l.map Int.toNat).Nodup := by
    apply List.Nodup.map_on
    · intro a ha b hb h
      exact int_toNat_inj_nonneg (h0 a ha) (h0 b hb) h
    · exact hnodup
  have hmap_lt : ∀ q ∈ l.map Int.toNat, q < n := by
    intro q hq
    rcases List.mem_map.mp hq with ⟨p, hp, rfl⟩
    exact (Int.toNat_lt (n := n) (h0 p hp)).mpr (hlt p hp)
  have hlen : (l.map Int.toNat).length = l.length := by simp
  rw [← hlen]
  exact nat_nodup_lt_length_le (l.map Int.toNat) n hmap_nodup hmap_lt

/-- 空路径的可达配置唯一：nil 路径的终配置 = 初始配置。 -/
lemma reach_cfg_of_len_zero (A : NTM2) (x : List F4) :
    ∀ (π : NTM2ComputationPath) (cfg : NTM2Config A x),
      TapeReachablePathNTM2 A x π cfg → π = [] → cfg = NTM2InitialConfig A x := by
  intro π cfg h
  induction h with
  | nil =>
      intro hπ
      rfl
  | cons π₀ step cfg₀ hrc hfrom hread hpos htrans ih =>
      intro hπ
      exfalso
      have hlen : (π₀ ++ [step]).length ≠ 0 := by simp
      exact hlen (by rw [hπ]; rfl)

lemma reach_nil_cfg (A : NTM2) (x : List F4) (cfg : NTM2Config A x) :
    TapeReachablePathNTM2 A x [] cfg → cfg = NTM2InitialConfig A x := by
  intro h
  exact reach_cfg_of_len_zero A x [] cfg h rfl

/-- 单步转移对应（NTM2 → CBTM，字母表内恒等翻译）。 -/
lemma iso_step_forward (A : NTM2) (M : CBTM) (iso : StructIsoNTM2CBTM A M)
    (q : ℕ) (s : F4) (i : ℤ) (r : ℕ × F4 × Dir) (hs : s ∈ A.alphabet) :
    r ∈ A.transition (q, s, i) →
    ntm2ResultToCBTM r ∈ M.transition (q, (iso.φ_symbol s).val, i) := by
  intro hr
  rw [iso.h_transition q s i hs]
  exact Finset.mem_image.mpr ⟨r, hr, rfl⟩

/-- 单步配置步进的对应（恒等）。 -/
lemma iso_step_config (A : NTM2) (M : CBTM) (iso : StructIsoNTM2CBTM A M)
    {x : List F4} (cfg : NTM2Config A x) (r : ℕ × F4 × Dir) :
    ntm2CfgToCBTM A M iso (NTM2StepConfig cfg r) =
      stepConfig (ntm2CfgToCBTM A M iso cfg) (ntm2ResultToCBTM r) := by
  dsimp [ntm2CfgToCBTM, NTM2StepConfig, stepConfig, ntm2ResultToCBTM]

/-- 路径上某步的读符号必在字母表内（读符号有转移 → 不落字母表外；h_transition_outside）。 -/
lemma path_step_readSym_mem_alphabet (A : NTM2) {x : List F4} {π : NTM2ComputationPath}
    {cfg : NTM2Config A x} (hr : TapeReachablePathNTM2 A x π cfg)
    (step : NTM2TransitionStep) (hstep : step ∈ π) :
    step.readSym ∈ A.alphabet := by
  induction hr with
  | nil =>
      simp at hstep
  | cons π₀ st cfg₀ hrc hfrom hread hpos htrans ih =>
      rw [List.mem_append] at hstep
      rcases hstep with hlast | htail
      · exact ih hlast
      · rw [List.mem_singleton] at htail
        subst htail
        by_contra hsnot
        have hout := A.h_transition_outside cfg₀.state step.readSym cfg₀.headPos hsnot
        rw [← hread] at htrans
        rw [hout] at htrans
        simpa using htrans

/-- 可达路径的对应（NTM2 → CBTM，路径与配置逐步保持；恒等翻译）。 -/
lemma iso_path_forward (A : NTM2) (M : CBTM) (iso : StructIsoNTM2CBTM A M) (x : List F4)
    (hcan : NTM2.Canonical A) :
    ∀ π, ∀ cfg : NTM2Config A x, TapeReachablePathNTM2 A x π cfg →
      ∃ π' : ComputationPath, ∃ cfg' : CBTMConfig M x,
        TapeReachablePath M x π' cfg' ∧
        cfg' = ntm2CfgToCBTM A M iso cfg := by
  intro π cfg hr
  induction hr with
  | nil =>
      refine ⟨[], initialConfig M x, TapeReachablePath.nil, ?_⟩
      exact (iso_initial_corresp A M iso x).symm
  | cons π₀ step cfg₀ hrc hfrom hread hpos htrans ih =>
      rcases ih with ⟨π', cfg', hrc', hcfg'⟩
      have hs_in : step.readSym ∈ A.alphabet := by
        by_contra hsnot
        have hout := A.h_transition_outside cfg₀.state step.readSym cfg₀.headPos hsnot
        rw [← hread] at htrans
        rw [hout] at htrans
        simpa using htrans
      let step' : TransitionStep :=
        { fromState := step.fromState,
          readSym := step.readSym,
          result := ntm2ResultToCBTM step.result }
      refine ⟨π' ++ [step'], stepConfig cfg' step'.result,
        TapeReachablePath.cons π' step' cfg' hrc' ?_ ?_ ?_, ?_⟩
      · rw [hcfg']
        dsimp [ntm2CfgToCBTM]
        dsimp [step']
        rw [← hfrom]
      · rw [hcfg']
        dsimp [ntm2CfgToCBTM, CBTMConfig.tapeAt]
        dsimp [step']
        rw [hread]
      · rw [hcfg']
        dsimp [ntm2CfgToCBTM, CBTMConfig.tapeAt]
        dsimp [step']
        rw [← hread, ← hpos] at htrans ⊢
        have hstepfwd := iso_step_forward A M iso cfg₀.state step.readSym step.pos step.result hs_in htrans
        rw [iso.h_φ_id step.readSym] at hstepfwd
        exact hstepfwd
      · rw [hcfg']
        dsimp [ntm2CfgToCBTM]
        dsimp [step']
        exact (iso_step_config A M iso cfg₀ step.result).symm

/-- 可达路径的对应（CBTM → NTM2；规范 NTM2 时）。
    归纳加强：镜像路径与 CBTM 路径同长，且终配置在输入区内（或路径为空）且非负。 -/
inductive NTM2TapeSteps (A : NTM2) (input : List F4) (cfg₀ : NTM2Config A input) :
    NTM2ComputationPath → NTM2Config A input → Prop
  | nil : NTM2TapeSteps A input cfg₀ [] cfg₀
  | cons : ∀ (π : NTM2ComputationPath) (step : NTM2TransitionStep) (cfg' : NTM2Config A input),
      NTM2TapeSteps A input cfg₀ π cfg' →
      step.fromState = cfg'.state →
      step.readSym = cfg'.tape cfg'.headPos →
      step.pos = cfg'.headPos →
      step.result ∈ A.transition (cfg'.state, cfg'.tape cfg'.headPos, cfg'.headPos) →
      NTM2TapeSteps A input cfg₀ (π ++ [step]) (NTM2StepConfig cfg' step.result)

/-- SymToF4.TapeSteps 拼接：h₁ 的终点接 h₂。 -/
lemma tapeSteps_append {M : CBTM} {input : List F4} {cfg₀ cfg₁ cfg₂ : CBTMConfig M input}
    {π₁ π₂ : ComputationPath}
    (h₁ : SymToF4.TapeSteps M input cfg₀ π₁ cfg₁) (h₂ : SymToF4.TapeSteps M input cfg₁ π₂ cfg₂) :
    SymToF4.TapeSteps M input cfg₀ (π₁ ++ π₂) cfg₂ := by
  induction h₂ with
  | nil => simpa using h₁
  | cons π₂₀ st cfg₂₀ hprev hfrom hread htrans ih =>
      have hcomb : SymToF4.TapeSteps M input cfg₀ (π₁ ++ π₂₀) cfg₂₀ := ih
      rw [← List.append_assoc]
      exact SymToF4.TapeSteps.cons (π₁ ++ π₂₀) st cfg₂₀ hcomb hfrom hread htrans

/-- NTM2TapeSteps 拼接（同上）。 -/
lemma ntm2TapeSteps_append {A : NTM2} {input : List F4} {cfg₀ cfg₁ cfg₂ : NTM2Config A input}
    {π₁ π₂ : NTM2ComputationPath}
    (h₁ : NTM2TapeSteps A input cfg₀ π₁ cfg₁) (h₂ : NTM2TapeSteps A input cfg₁ π₂ cfg₂) :
    NTM2TapeSteps A input cfg₀ (π₁ ++ π₂) cfg₂ := by
  induction h₂ with
  | nil => simpa using h₁
  | cons π₂₀ st cfg₂₀ hprev hfrom hread hpos htrans ih =>
      have hcomb : NTM2TapeSteps A input cfg₀ (π₁ ++ π₂₀) cfg₂₀ := ih
      rw [← List.append_assoc]
      exact NTM2TapeSteps.cons (π₁ ++ π₂₀) st cfg₂₀ hcomb hfrom hread hpos htrans

/-- NTM2TapeSteps 与 TapeReachablePathNTM2 一致（从初始配置出发）。 -/
lemma ntm2TapeSteps_initial_iff (A : NTM2) (input : List F4) (π : NTM2ComputationPath)
    (cfg : NTM2Config A input) :
    NTM2TapeSteps A input (NTM2InitialConfig A input) π cfg ↔ TapeReachablePathNTM2 A input π cfg := by
  constructor <;> intro h
  · induction h with
    | nil => exact TapeReachablePathNTM2.nil
    | cons π₀ st cfg₁ hprev hfrom hread hpos htrans ih =>
        exact TapeReachablePathNTM2.cons π₀ st cfg₁ ih hfrom hread hpos htrans
  · induction h with
    | nil => exact NTM2TapeSteps.nil
    | cons π₀ st cfg₁ hprev hfrom hread hpos htrans ih =>
        exact NTM2TapeSteps.cons π₀ st cfg₁ ih hfrom hread hpos htrans



/-- 继续路径镜像：M 层 SymToF4.TapeSteps（从 cfg₀）→ A 层镜像（从 cfg₀ 的 A 镜像 cfg'）。
    A 的转移不依赖位置、F4 全在字母表 ⟹ 镜像总可构造（不需位置界）。 -/
lemma iso_continue_mirror (A : NTM2) (M : CBTM) (iso : StructIsoNTM2CBTM A M) (x : List F4)
    {cfg' : NTM2Config A x} {cfg₀ : CBTMConfig M x}
    (hcfg : cfg₀ = ntm2CfgToCBTM A M iso cfg')
    {π₂ : ComputationPath} {cfg₂ : CBTMConfig M x}
    (h₂ : SymToF4.TapeSteps M x cfg₀ π₂ cfg₂) :
    ∃ π₂' : NTM2ComputationPath, ∃ cfg₂' : NTM2Config A x,
      cfg₂ = ntm2CfgToCBTM A M iso cfg₂' ∧
      π₂.length = π₂'.length ∧
      (π₂'.map (fun s => s.readSym) = π₂.map (fun s => s.readSym)) ∧
      NTM2TapeSteps A x cfg' π₂' cfg₂' := by
  induction h₂ with
  | nil =>
      refine ⟨[], cfg', ?_, ?_, ?_, NTM2TapeSteps.nil⟩
      · rw [hcfg]
      · rfl
      · rfl
  | cons π₀₂ step cfg₁ hprev hfrom hread htrans ih =>
      rcases ih with ⟨π₀₂', cfg₁', hcfg₁, hlen, hmap, hsteps'⟩
      let s₀ : F4 := cfg₁.tapeAt cfg₁.headPos
      have hs₀_in : s₀ ∈ A.alphabet := by
        by_contra hsnot
        rw [A.h_alphabet_all] at hsnot
        have hsnotM : s₀ ∉ M.alphabet := by
          rcases s₀ with ⟨r, im⟩ <;> cases r <;> cases im <;>
            simp [F4.zero, F4.one, F4.alpha, F4.beta] at hsnot
        have hout := M.h_transition_outside cfg₁.state s₀ cfg₁.headPos hsnotM
        have htrans' : step.result ∈ M.transition (cfg₁.state, s₀, cfg₁.headPos) := by
          simpa [s₀, CBTMConfig.tapeAt] using htrans
        rw [hout] at htrans'
        simpa using htrans'
      have himage : step.result ∈ (A.transition (cfg₁.state, s₀, cfg₁.headPos)).image
          ntm2ResultToCBTM := by
        rw [← iso.h_transition cfg₁.state s₀ cfg₁.headPos hs₀_in]
        rw [iso.h_φ_id s₀]
        exact htrans
      rcases Finset.mem_image.mp himage with ⟨r₀, hr₀, hres⟩
      let step₀ : NTM2TransitionStep :=
        { fromState := cfg₁.state, readSym := s₀, pos := cfg₁.headPos, result := r₀ }
      have hhead_eq : cfg₁.headPos = cfg₁'.headPos := by
        rw [hcfg₁]
        rfl
      have hfrom₀ : step₀.fromState = cfg₁'.state := by
        dsimp [step₀]
        rw [hcfg₁]
        rfl
      have hread₀ : step₀.readSym = cfg₁'.tape cfg₁'.headPos := by
        dsimp [step₀, s₀, CBTMConfig.tapeAt]
        rw [hcfg₁]
        rfl
      have hpos₀ : step₀.pos = cfg₁'.headPos := by
        dsimp [step₀]
        rw [hcfg₁]
        rfl
      have htrans₀ : step₀.result ∈ A.transition (cfg₁'.state, cfg₁'.tape cfg₁'.headPos, cfg₁'.headPos) := by
        dsimp [step₀]
        dsimp [s₀, CBTMConfig.tapeAt] at hr₀
        rw [hcfg₁] at hr₀
        exact hr₀
      refine ⟨π₀₂' ++ [step₀], NTM2StepConfig cfg₁' r₀, ?_, ?_, ?_, ?_⟩
      · rw [hcfg₁]
        rw [← hres]
        exact (iso_step_config A M iso cfg₁' r₀).symm
      · simp [hlen]
      · rw [List.map_append, List.map_append, hmap]
        simp [step₀, s₀, hread.symm]
      · exact NTM2TapeSteps.cons π₀₂' step₀ cfg₁' hsteps' hfrom₀ hread₀ hpos₀ htrans₀

lemma iso_path_backward (A : NTM2) (M : CBTM) (iso : StructIsoNTM2CBTM A M) (x : List F4)
    (hcan : NTM2.Canonical A)
    (hwf : ∃ inst : SubsetSumInstance, ∃ gS : List Sym,
      x = SymToF4.encodeInstanceF4 inst ++ SymToF4.flat4F4 gS) :
    ∀ π, ∀ cfg : CBTMConfig M x,
      (∀ step ∈ π, step.fromState ∉ A.acceptStates) →
      TapeReachablePath M x π cfg →
      (∃ π₂ : ComputationPath, ∃ cfg₂ : CBTMConfig M x,
          SymToF4.TapeSteps M x cfg π₂ cfg₂ ∧ cfg₂.state ∈ M.acceptStates) →
      ∃ π' : NTM2ComputationPath, ∃ cfg' : NTM2Config A x,
        TapeReachablePathNTM2 A x π' cfg' ∧ cfg = ntm2CfgToCBTM A M iso cfg' ∧
        π.length = π'.length ∧
        (cfg'.headPos ≤ (x.length : ℤ) ∨ π'.length = 0) ∧ 0 ≤ cfg'.headPos ∧
        (∀ step ∈ π', step.fromState ∉ A.acceptStates) ∧
        (π'.map (fun s => s.readSym) = π.map (fun s => s.readSym)) := by
  intro π cfg hnoTerm hr hext
  rcases hcan with ⟨K, hK⟩
  induction hr with
  | nil =>
      refine ⟨[], NTM2InitialConfig A x, TapeReachablePathNTM2.nil, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact (iso_initial_corresp A M iso x).symm
      · rfl
      · exact Or.inr rfl
      · dsimp [NTM2InitialConfig]
        omega
      · intro s hs
        simp at hs
      · rfl
  | cons π₀ step cfg₀ hrc hfrom hread htrans ih =>
      have hnoπ₀ : ∀ s ∈ π₀, s.fromState ∉ A.acceptStates := by
        intro s hs
        have hmem : s ∈ π₀ ++ [step] := List.mem_append.mpr (Or.inl hs)
        exact hnoTerm s hmem
      rcases hext with ⟨π₂, cfg₂, hsteps₂, hacc₂⟩
      -- π₀ 可延拓:cfg₀ --step--> cfg(hr 终点)再 π₂(hsteps₂ 从 cfg 出发)
      have hext₀ : ∃ (π₀₂ : ComputationPath) (cfg₀₂ : CBTMConfig M x),
          SymToF4.TapeSteps M x cfg₀ π₀₂ cfg₀₂ ∧ cfg₀₂.state ∈ M.acceptStates := by
        refine ⟨step :: π₂, cfg₂, ?_, hacc₂⟩
        have hsingle : SymToF4.TapeSteps M x cfg₀ [step] (stepConfig cfg₀ step.result) := by
          exact SymToF4.TapeSteps.cons [] step cfg₀ SymToF4.TapeSteps.nil hfrom hread htrans
        simpa using (tapeSteps_append hsingle hsteps₂)
      rcases ih hnoπ₀ hext₀ with ⟨π', cfg', hrc', hcfg', hlen, hlt, hnonneg, hnoπ', hmap⟩
      let s₀ : F4 := cfg₀.tapeAt cfg₀.headPos
      have hhead_eq : cfg₀.headPos = cfg'.headPos := by
        rw [hcfg']
        rfl
      have hs₀_in : s₀ ∈ A.alphabet := by
        by_contra hsnot
        rw [A.h_alphabet_all] at hsnot
        have hsnotM : s₀ ∉ M.alphabet := by
          rcases s₀ with ⟨r, im⟩ <;> cases r <;> cases im <;>
            simp [F4.zero, F4.one, F4.alpha, F4.beta] at hsnot
        have hout := M.h_transition_outside cfg₀.state s₀ cfg₀.headPos hsnotM
        have htrans' : step.result ∈ M.transition (cfg₀.state, s₀, cfg₀.headPos) := by
          simpa [s₀, CBTMConfig.tapeAt] using htrans
        rw [hout] at htrans'
        simpa using htrans'
      have himage : step.result ∈ (A.transition (cfg₀.state, s₀, cfg₀.headPos)).image
          ntm2ResultToCBTM := by
        rw [← iso.h_transition cfg₀.state s₀ cfg₀.headPos hs₀_in]
        rw [iso.h_φ_id s₀]
        exact htrans
      rcases Finset.mem_image.mp himage with ⟨r₀, hr₀, hres⟩
      let step₀ : NTM2TransitionStep :=
        { fromState := cfg₀.state, readSym := s₀, pos := cfg₀.headPos, result := r₀ }
      have hfrom₀ : step₀.fromState = cfg'.state := by
        dsimp [step₀]
        rw [hcfg']
        dsimp [ntm2CfgToCBTM]
      have hread₀ : step₀.readSym = cfg'.tape cfg'.headPos := by
        dsimp [step₀, s₀, CBTMConfig.tapeAt]
        rw [hcfg']
        dsimp [ntm2CfgToCBTM]
      have hpos₀ : step₀.pos = cfg'.headPos := by
        dsimp [step₀]
        rw [hcfg']
        dsimp [ntm2CfgToCBTM]
      have htrans₀ : step₀.result ∈ A.transition (cfg'.state, cfg'.tape cfg'.headPos, cfg'.headPos) := by
        dsimp [step₀]
        dsimp [s₀, CBTMConfig.tapeAt] at hr₀
        rw [hcfg'] at hr₀
        dsimp [ntm2CfgToCBTM] at hr₀
        exact hr₀
      have hnoπ'₀ : ∀ s ∈ π' ++ [step₀], s.fromState ∉ A.acceptStates := by
        intro s hs
        rcases List.mem_append.mp hs with hml | hmr
        · exact hnoπ' s hml
        · have hsing : s = step₀ := by
            simpa using hmr
          rw [hsing]
          dsimp [step₀]
          have h1 := hnoTerm step (by
            exact List.mem_append.mpr (Or.inr (List.mem_singleton_self step)))
          simpa [hfrom] using h1
      -- π'++[step₀] 的可延拓:hr 终点 cfg 的 A 镜像 = NTM2StepConfig cfg' r₀;
      -- π₂ 从 cfg 出发(hsteps₂)→ iso_continue_mirror 给 A 层镜像(到 cfg₂' accept)
      have hext_new : ∃ (π₂' : NTM2ComputationPath) (cfg₂' : NTM2Config A x),
          TapeReachablePathNTM2 A x (π' ++ [step₀] ++ π₂') cfg₂' ∧
            cfg₂'.state ∈ A.acceptStates := by
        have hcfgM : stepConfig cfg₀ step.result = ntm2CfgToCBTM A M iso (NTM2StepConfig cfg' r₀) := by
          calc stepConfig cfg₀ step.result
              = stepConfig (ntm2CfgToCBTM A M iso cfg') step.result := by rw [hcfg']
              _ = stepConfig (ntm2CfgToCBTM A M iso cfg') (ntm2ResultToCBTM r₀) := by rw [hres]
              _ = ntm2CfgToCBTM A M iso (NTM2StepConfig cfg' r₀) := (iso_step_config A M iso cfg' r₀).symm
        rcases iso_continue_mirror A M iso x hcfgM hsteps₂ with
          ⟨π₂', cfg₂', hcfg₂, _hlen₂, _hmap₂, hsteps₂'⟩
        have hacc₂' : cfg₂'.state ∈ A.acceptStates := by
          have h1 : cfg₂'.state ∈ M.acceptStates := by
            rw [hcfg₂] at hacc₂
            simpa [ntm2CfgToCBTM] using hacc₂
          simpa [iso.h_accept] using h1
        have hrc'' : TapeReachablePathNTM2 A x (π' ++ [step₀]) (NTM2StepConfig cfg' r₀) := by
          exact TapeReachablePathNTM2.cons π' step₀ cfg' hrc' hfrom₀ hread₀ hpos₀ htrans₀
        have hfull : TapeReachablePathNTM2 A x (π' ++ [step₀] ++ π₂') cfg₂' := by
          have h1' : NTM2TapeSteps A x (NTM2InitialConfig A x) (π' ++ [step₀])
              (NTM2StepConfig cfg' r₀) :=
            (ntm2TapeSteps_initial_iff A x (π' ++ [step₀]) (NTM2StepConfig cfg' r₀)).mpr hrc''
          have h2' : NTM2TapeSteps A x (NTM2InitialConfig A x) ((π' ++ [step₀]) ++ π₂') cfg₂' :=
            ntm2TapeSteps_append h1' hsteps₂'
          exact (ntm2TapeSteps_initial_iff A x (π' ++ [step₀] ++ π₂') cfg₂').mp
            (by simpa [List.append_assoc] using h2')
        exact ⟨π₂', cfg₂', hfull, hacc₂'⟩
      have hcan_new := hK x (π' ++ [step₀]) (NTM2StepConfig cfg' r₀) hwf hnoπ'₀
        (TapeReachablePathNTM2.cons π' step₀ cfg' hrc' hfrom₀ hread₀ hpos₀ htrans₀) hext_new
      have hstep₀_mem : step₀ ∈ π' ++ [step₀] := by simp
      have hstep0_after : 0 ≤ step₀.pos + step₀.result.2.2.toInt :=
        (hcan_new.1 step₀ hstep₀_mem).2.2.1
      have hstep0_after_le : step₀.pos + step₀.result.2.2.toInt ≤ (x.length : ℤ) :=
        (hcan_new.1 step₀ hstep₀_mem).2.2.2
      have hcfg''head : (NTM2StepConfig cfg' r₀).headPos = step₀.pos + step₀.result.2.2.toInt := by
        dsimp [NTM2StepConfig, step₀]
        rw [hhead_eq]
      have hnew_le : (NTM2StepConfig cfg' r₀).headPos ≤ (x.length : ℤ) := by
        rw [hcfg''head]
        exact hstep0_after_le
      have hnew_ge : 0 ≤ (NTM2StepConfig cfg' r₀).headPos := by
        rw [hcfg''head]
        exact hstep0_after
      refine ⟨π' ++ [step₀], NTM2StepConfig cfg' r₀,
        TapeReachablePathNTM2.cons π' step₀ cfg' hrc' hfrom₀ hread₀ hpos₀ htrans₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hcfg']
        dsimp [ntm2CfgToCBTM]
        rw [← hres]
        exact (iso_step_config A M iso cfg' r₀).symm
      · -- π.length = (π' ++ [step₀]).length（cons 分支：π = π₀ ++ [step]，ih 同长）
        simp [hlen]
      · exact Or.inl hnew_le
      · exact hnew_ge
      · exact hnoπ'₀
      · -- 镜像步 readSym = 原步 readSym（构造 step₀.readSym = s₀ = 原读符）
        rw [List.map_append, List.map_append, hmap]
        simp [step₀, s₀, hread.symm]

/-- 首达接受步拆分：路径上要么没有从接受态出发的步，要么在首个这样的步处拆分为
    π₀ ++ step :: π₁（π₀ 的所有步都不从接受态出发，且 π₀ 的终点配置状态 = step.fromState ∈ accept）。 -/
lemma first_accept_step_split (M : CBTM) (x : List F4) :
    ∀ {π : ComputationPath} {cfg : CBTMConfig M x}, TapeReachablePath M x π cfg →
      (∀ step ∈ π, step.fromState ∉ M.acceptStates) ∨
      ∃ π₀ step π₁, π = π₀ ++ step :: π₁ ∧ step.fromState ∈ M.acceptStates ∧
        (∀ s ∈ π₀, s.fromState ∉ M.acceptStates) ∧
        ∃ c₀ : CBTMConfig M x, TapeReachablePath M x π₀ c₀ ∧ c₀.state = step.fromState := by
  intro π cfg h
  induction h with
  | nil =>
      left
      intro s hs
      simp at hs
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      rcases ih with hclean | ⟨π₀', st, π₁', hsplit, hacc_st, hclean', c₀', hc₀', hstate'⟩
      · by_cases hacc_step : step.fromState ∈ M.acceptStates
        · right
          refine ⟨π₀, step, [], ?_, hacc_step, hclean, cfg₁, hprev, ?_⟩
          · simp
          · exact hfrom.symm
        · left
          intro s hs
          rcases List.mem_append.mp hs with hm | hm'
          · exact hclean s hm
          · have hsing : s = step := by
              simpa using hm'
            rw [hsing]
            exact hacc_step
      · right
        refine ⟨π₀', st, π₁' ++ [step], ?_, hacc_st, hclean', c₀', hc₀', hstate'⟩
        rw [hsplit]
        simp [List.append_assoc]

/-- CBTM 接受路径可截断为首达接受态路径：首达接受态前的步均不从接受态出发
    （无需接受态吸收性）。 -/
lemma tapeAccepts_truncate (M : CBTM) (x : List F4) (π : ComputationPath) (cfg : CBTMConfig M x)
    (h : TapeReachablePath M x π cfg) (hacc : cfg.state ∈ M.acceptStates) :
    ∃ π' : ComputationPath, ∃ cfg' : CBTMConfig M x,
      TapeReachablePath M x π' cfg' ∧ cfg'.state ∈ M.acceptStates ∧
      (∀ step ∈ π', step.fromState ∉ M.acceptStates) := by
  rcases first_accept_step_split M x h with hclean | ⟨π₀, step, π₁, hsplit, hacc_st, hclean₀, c₀, hc₀, hstate⟩
  · exact ⟨π, cfg, h, hacc, hclean⟩
  · refine ⟨π₀, c₀, hc₀, ?_, hclean₀⟩
    simpa [hstate] using hacc_st

/-- 结构同构保持接受语言（NTM2 磁带语义 ↔ CBTM 磁带语义；规范 NTM2 时）。
    输入 = F4 串（直铺恒等）；接受路径经首达截断后满足 hnoTerm。 -/
theorem StructIso_preserves_accepts (A : NTM2) (M : CBTM) (iso : StructIsoNTM2CBTM A M)
    (hcan : NTM2.Canonical A) (x : List F4)
    (hwf : ∃ inst : SubsetSumInstance, ∃ gS : List Sym,
      x = SymToF4.encodeInstanceF4 inst ++ SymToF4.flat4F4 gS) :
    (A.acceptsTape x ↔ M.tapeAccepts x) := by
  constructor
  · intro ⟨π, cfg, hr, hacc⟩
    rcases (iso_path_forward A M iso x hcan π cfg hr) with ⟨π', cfg', hrc', hcfg'⟩
    refine ⟨π', cfg', hrc', ?_⟩
    rw [hcfg']
    rw [iso.h_accept]
    exact hacc
  · intro ⟨π, cfg, hr, hacc⟩
    rcases tapeAccepts_truncate M x π cfg hr hacc with ⟨πt, cfgt, hrt, hacct, hnoT⟩
    rcases (iso_path_backward A M iso x hcan hwf πt cfgt (by
      intro step hmem h
      exact hnoT step hmem (by simpa [iso.h_accept] using h)) hrt
      ⟨[], cfgt, SymToF4.TapeSteps.nil, hacct⟩) with
      ⟨π', cfg', hrc', hcfg', _hlen, _hlt, _hnonneg, _hnoπ', _hmap⟩
    refine ⟨π', cfg', hrc', ?_⟩
    rw [iso.h_accept] at hacct
    rw [hcfg'] at hacct
    exact hacct

end Mp
