import Mp.SubsetSumVerifierPosBound1
import Mp.SubsetSumVerifierReverse7L3
import Mp.SubsetSumVerifierStepBound

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

-- ============================================================================
-- q10 ①线 A-2(g' ≠ [] 推广):带后缀输入 x = encodeInstanceF4 inst ++ g' 上的位置界
-- 2026-09-09 开工。目标(2026-09-09 修正):Canonical ① 原文(CBTM.lean:977)——x 上
--   可延拓接受路径每步 pos ∈ [0, |x|] 闭区间("不越输入";非 ≤ 4L'——机器可在 gS 区
--   活动,越 |x| 读带外 = 与 enc 输入同值 → 束漂移族排除)。
--   §K0'(b0f81c9)= 用户裁决(2026-09-09):"20 必然是在中分隔符上"——可达路径上
--     cfg.state = 20 ⟹ 头格是 boundary(任意输入,纯转移结构,联合归纳;通用件)。
--   §K0(431a12b)= enc 输入上 20 的头 ∈ [n+1, L-3](可延拓路径):P9(boundary 位置三支)
--     + r7l3_20_head(≥1,排 0)+ 20@L-1 排除(唯一转移 20 读 #₁ → 21 R@L,
--     21 读带外 blank 自环漂移,sym_drift_blank_no_accept 与 hext 矛盾)——独立有效
--     引理(enc 特例,不再阻塞 A-2;K0' 的 enc 版界化)。
-- 设计文档:_q10-a2-design.md(第二版);padding = 逻辑层映射(机器 {0,1,sep,#} →
--   {data0,data1,alpha,boundary})。带外 = boundary 语义推进(Lean 迁移延后单列)。
-- ============================================================================

/-- 4 的入边分类(带读写细节):28 读 boundary R 写回,或 51 读 data R 写 boundary。 -/
lemma a2_into_4 (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h4 : r.nextState = 4) :
    (q = 28 ∧ s.1 = SymKind.boundary ∧ r.moveDir = Dir.R ∧ r.writeSym = s) ∨
    (q = 51 ∧ s.1 = SymKind.data0 ∧ r.moveDir = Dir.R ∧ r.writeSym = Sym.boundary) := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 4 →
      ((q : ℕ) = 28 ∧ s.1 = SymKind.boundary ∧ r.moveDir = Dir.R ∧ r.writeSym = s) ∨
        ((q : ℕ) = 51 ∧ s.1 = SymKind.data0 ∧ r.moveDir = Dir.R ∧ r.writeSym = Sym.boundary) := by
    native_decide
  exact hb ⟨q, hq⟩ s r hr h4

/-- 87 → 20:读 boundary S 写回(20 停在 87 读的 boundary 格上)。 -/
lemma a2_87_to_20 (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (87, s)) (h20 : r.nextState = 20) :
    s.1 = SymKind.boundary ∧ r.moveDir = Dir.S ∧ r.writeSym = s := by
  have hb : ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (87, s) → r.nextState = 20 →
      s.1 = SymKind.boundary ∧ r.moveDir = Dir.S ∧ r.writeSym = s := by
    native_decide
  exact hb s r hr h20

/-- K0':20 态必在中分隔符上(头格符号是 boundary)。任意输入成立。 -/
lemma a2_cfg20_on_boundary {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg) :
    cfg.state = 20 → (cfg.tape cfg.headPos).1 = SymKind.boundary := by
  -- 联合归纳:P cfg = (20 分量:头格 boundary)∧ (4 分量:头-1 格 boundary)
  --   20 的 4 L 入边分支用 ih 的 4 分量;4 分量由入边一步(28/51)闭合。
  have hmain : ∀ {π : List SymStep} {cfg : SymConfig},
      SymReachablePath VerifierSym.transition input π cfg →
        (cfg.state = 20 → (cfg.tape cfg.headPos).1 = SymKind.boundary) ∧
          (cfg.state = 4 → (cfg.tape (cfg.headPos - 1)).1 = SymKind.boundary) := by
    intro π cfg h
    induction h with
    | nil =>
        constructor
        · intro h20
          simp [symInitialConfig] at h20
        · intro h4
          simp [symInitialConfig] at h4
    | cons π₀ step cfg' hprev hfrom hread htrans ih =>
        constructor
        · intro h20
          have hsrc := r7_into_20_class cfg'.state
            (q12_path_state_lt102 input π₀ cfg' hprev)
            step.readSym step.result (by simpa [hread] using htrans) (by simpa [symStepConfig] using h20)
          rcases hsrc with h87s | h4l
          · rcases h87s with ⟨hq87, hdS⟩
            have hb := a2_87_to_20 step.readSym step.result
              (by simpa [hread, hq87] using htrans) (by simpa [symStepConfig] using h20)
            rcases hb with ⟨hrdb, _hdS', hws⟩
            dsimp [symStepConfig]
            rw [hdS]
            simp [Dir.toInt]
            rw [hws]
            exact hrdb
          · rcases h4l with ⟨hq4, hdL⟩
            dsimp [symStepConfig]
            rw [hdL]
            simp [Dir.toInt]
            rw [show cfg'.headPos + -1 = cfg'.headPos - 1 by omega]
            exact ih.2 hq4
        · intro h4
          have hsrc := a2_into_4 cfg'.state
            (q12_path_state_lt102 input π₀ cfg' hprev)
            step.readSym step.result (by simpa [hread] using htrans) (by simpa [symStepConfig] using h4)
          rcases hsrc with h28 | h51
          · rcases h28 with ⟨hq28, hrdb, hdR, hws⟩
            dsimp [symStepConfig]
            rw [hdR]
            simp [Dir.toInt]
            rw [hws]
            exact hrdb
          · rcases h51 with ⟨hq51, hdata, hdR, hws⟩
            dsimp [symStepConfig]
            rw [hdR]
            simp [Dir.toInt]
            rw [hws]
            simp [Sym.boundary]
  intro h20
  exact (hmain h).1 h20

/-- 表级:20 读 boundary-kind 符号 → 唯一转移 21 R 写 data0(#₁ 亦然——越界通道)。 -/
lemma a2_20_read_boundary_to_21 (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (20, s)) (hb : s.1 = SymKind.boundary) :
    r.nextState = 21 ∧ r.moveDir = Dir.R ∧ r.writeSym = Sym.data0 := by
  have hbb : ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (20, s) → s.1 = SymKind.boundary →
      r.nextState = 21 ∧ r.moveDir = Dir.R ∧ r.writeSym = Sym.data0 := by
    native_decide
  exact hbb s r hr hb

/-- 表级:21 读 blank(= data0-false)→ 自环 R 写回 blank(带外漂移)。 -/
lemma a2_21_read_blank_drift (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (21, Sym.blank)) :
    r.nextState = 21 ∧ r.moveDir = Dir.R ∧ r.writeSym = Sym.blank := by
  have hb : ∀ r : SymTransResult, r ∈ VerifierSym.transition (21, Sym.blank) →
      r.nextState = 21 ∧ r.moveDir = Dir.R ∧ r.writeSym = Sym.blank := by
    native_decide
  exact hb r hr

/-- 单步 SymSteps 的成员提取(仿 symSteps_singleton_fromState 的 generalize-归纳)。 -/
lemma a2_singleton_hmem {M : ℕ × Sym → Finset SymTransResult} {cfg cfg' : SymConfig}
    {step : SymStep} (h : SymSteps M cfg [step] cfg') :
    step.fromState = cfg.state ∧ step.readSym = cfg.tape cfg.headPos ∧
      step.result ∈ M (cfg.state, cfg.tape cfg.headPos) := by
  generalize hL : [step] = L at h
  induction h with
  | nil => simp at hL
  | cons πs step' cfg₁ hprev hfrom hread htrans _ =>
      have hsnoc := snoc_eq_snoc (α := SymStep) (π₁ := []) (π₂ := πs) (a := step) (b := step')
        (by simpa [List.append_assoc] using hL)
      rcases hsnoc with ⟨hπs, hstep'⟩
      subst hstep'
      have hcfg₁ : cfg₁ = cfg := by
        exact (Mp.SymToF4.symSteps_end_unique (M := M)
          (by simpa [hπs] using hprev) SymSteps.nil)
      subst hcfg₁
      exact ⟨hfrom, hread, htrans⟩

/-- K0:enc 输入上可延拓路径的 20 态头 ∈ [n+1, L-3](n = |target bits|)。 -/
lemma a2_cfg20_head_in_range (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (hpos : ∀ v ∈ inst.elements, 0 < v) (htarget : 0 < inst.target)
    {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg)
    (hext : ∃ (π₂ : List SymStep) (cfg₂ : SymConfig),
      SymReachablePath VerifierSym.transition (encodeInstanceSym inst) (π ++ π₂) cfg₂ ∧
      cfg₂.state = 100) :
    cfg.state = 20 →
    (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) ≤ cfg.headPos ∧
    cfg.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 3 : ℤ) := by
  intro h20
  have hbnd : (cfg.tape cfg.headPos).1 = SymKind.boundary := a2_cfg20_on_boundary h h20
  rcases r7_path_bundle inst hm hpos htarget π cfg h hext with
    ⟨_hP0, hPblank, _hP0e, _h1, _h28, _h87, _h20b, _h23, _h81, _h9A, _h12c, _h10,
      _hP10'0, _hP10'1, _hP10'1b, _hP10'1c, _hP10'2, _hP10'F, _hP11, _hP6l, _hP6r, hP9⟩
  rcases hP9 cfg.headPos hbnd with h0 | hL1 | hmid
  · exfalso
    have hge1 : (1 : ℤ) ≤ cfg.headPos := r7l3_20_head inst h h20
    omega
  · exfalso
    -- 20@L-1(读 #₁):唯一转移 20 → 21 R;21@L 读带外 blank 自环漂移 →
    -- sym_drift_blank_no_accept 与 hext 矛盾
    have hlenL : ((encodeInstanceSym inst).length : ℤ) - 1 = cfg.headPos := by omega
    rcases hext with ⟨π₂, cfg₂, hpath₂, hacc₂⟩
    have hsteps₂ : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst))
        (π ++ π₂) cfg₂ :=
      (symSteps_initial_iff VerifierSym.transition (encodeInstanceSym inst) (π ++ π₂) cfg₂).mpr hpath₂
    have hsteps₁ : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst))
        π cfg :=
      (symSteps_initial_iff VerifierSym.transition (encodeInstanceSym inst) π cfg).mpr h
    rcases symSteps_append_decomp π π₂ hsteps₂ with ⟨cfg₁, hseg₁, hseg₂⟩
    have hcfg₁ : cfg₁ = cfg := Mp.SymToF4.symSteps_end_unique hseg₁ hsteps₁
    have hseg₂' : SymSteps VerifierSym.transition cfg π₂ cfg₂ := by
      simpa [hcfg₁] using hseg₂
    cases π₂ with
    | nil =>
        exfalso
        have hc : cfg₂ = cfg := by
          simpa using (Mp.SymToF4.symSteps_end_unique (M := VerifierSym.transition) hseg₂' SymSteps.nil)
        have h20' : cfg₂.state = 20 := by simpa [hc] using h20
        omega
    | cons step₂ π₂' =>
        -- 第一步:step₂ from cfg(态 20)读 boundary(#₁)→ 21 R@L
        have hseg₂'' : SymSteps VerifierSym.transition cfg ([step₂] ++ π₂') cfg₂ := by
          simpa using hseg₂'
        rcases symSteps_append_split (M := VerifierSym.transition) (cfg₀ := cfg)
          (π₀ := [step₂]) (rest := π₂') hseg₂'' with ⟨cfg₁', h₁, h₂⟩
        have hsing : step₂.fromState = cfg.state ∧
            cfg₁' = symStepConfig cfg step₂.result := symSteps_singleton_fromState h₁
        rcases hsing with ⟨hfrom, hcfg₁'⟩
        have hmem₁ : step₂.fromState = cfg.state ∧ step₂.readSym = cfg.tape cfg.headPos ∧
            step₂.result ∈ VerifierSym.transition (cfg.state, cfg.tape cfg.headPos) :=
          a2_singleton_hmem h₁
        have hbnd₂ : (step₂.readSym).1 = SymKind.boundary := by
          simpa [hmem₁.2.1, hbnd]
        have h20b := a2_20_read_boundary_to_21 step₂.readSym step₂.result
          (by simpa [h20, hmem₁.2.1] using hmem₁.2.2)
          hbnd₂
        have hq21' : cfg₁'.state = 21 := by
          rw [hcfg₁']
          exact h20b.1
        have hdR : step₂.result.moveDir = Dir.R := h20b.2.1
        have hgeL : ((encodeInstanceSym inst).length : ℤ) ≤ cfg₁'.headPos := by
          rw [hcfg₁']
          simp [symStepConfig, hdR, Dir.toInt, hlenL]
          omega
        have hblank1 : ∀ j : ℤ, ((encodeInstanceSym inst).length : ℤ) ≤ j →
            cfg₁'.tape j = Sym.blank := by
          intro j hj
          rw [hcfg₁']
          simp [symStepConfig]
          rw [if_neg (by omega : j ≠ cfg.headPos)]
          exact hPblank j hj
        -- cfg₁' 可达 + 延拓(π ++ [step₂] ++ π₂' → cfg₂ 态 100)
        have hreach1 : SymReachablePath VerifierSym.transition (encodeInstanceSym inst)
            (π ++ [step₂]) cfg₁' := by
          refine symSteps_after_path VerifierSym.transition (encodeInstanceSym inst) h ?_
          simpa [hcfg₁'] using h₁
        have hext1 : ∃ (π₂'' : List SymStep) (cfg₂' : SymConfig),
            SymReachablePath VerifierSym.transition (encodeInstanceSym inst)
              ((π ++ [step₂]) ++ π₂'') cfg₂' ∧ cfg₂'.state = 100 := by
          refine ⟨π₂', cfg₂, ?_, hacc₂⟩
          have htail : SymSteps VerifierSym.transition cfg₁' π₂' cfg₂ := by
            simpa [hcfg₁'] using h₂
          have hpath : SymReachablePath VerifierSym.transition (encodeInstanceSym inst)
              (π ++ [step₂] ++ π₂') cfg₂ :=
            symSteps_after_path VerifierSym.transition (encodeInstanceSym inst) hreach1 htail
          simpa [List.append_assoc] using hpath
        have hdrift := a2_21_read_blank_drift
        exact sym_drift_blank_no_accept 21 (encodeInstanceSym inst) hreach1 hq21' hgeL
          (by norm_num) hblank1 hdrift hext1
  · rcases hmid with ⟨hge, hle⟩
    exact ⟨hge, hle⟩

-- ============================================================================
-- A-2 K1-Sym(B 右端版 q12):虚拟输入 wS 上从真输入界 B(= ceil(|x|/4))起为
--   data0-false 尾(no_trap 的 zeroTail)——"尾区活动 = 带外类"的 Q∧R 联合归纳
--   (q12_outside_closed_and_51_bound 的模板,|input| → B,初始条件用 getD 零尾)。
--   用途:虚拟接受路径每前缀头 ≤ B ⟹ F4 块首 4p ≤ 4B-4(≈ |x|)⟹ A-2 上界。
-- ============================================================================

/-- K1-Sym Q∧R:B 右端版带外封闭(位置 ≥ B 的格值 ∈ IsOutside {data0,data1,consumed})
    + 51 态头 ≤ B-1。前提:输入在 ≥ B 处全 data0-false(getD 形式,带外自动 blank 同值)。
    q12_outside_closed_and_51_bound(Reverse6:187)的逐字重放,右端 |input| → B。 -/
lemma a2_outside_closed_from (input : List Sym) (B : ℕ) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg)
    (hB : ∀ j : ℕ, B ≤ j → input.getD j Sym.blank = Sym.data0 false) :
    (∀ j : ℤ, (B : ℤ) ≤ j → IsOutside (cfg.tape j)) ∧
    (cfg.state = 51 → cfg.headPos ≤ (B : ℤ) - 1) := by
  induction h with
  | nil =>
      constructor
      · intro j hj
        left
        change (if h : 0 ≤ j ∧ j.toNat < input.length then
            input.get ⟨j.toNat, h.2⟩ else Sym.blank).1 = SymKind.data0
        by_cases hc : 0 ≤ j ∧ j.toNat < input.length
        · have hb' : input.getD j.toNat Sym.blank = Sym.data0 false := hB j.toNat (by omega)
          have hget : input.get ⟨j.toNat, hc.2⟩ = Sym.data0 false := by
            have hg' : (input[j.toNat]?).getD Sym.blank = input.get ⟨j.toNat, hc.2⟩ := by
              simp [hc.2]
            rw [← hg']
            rw [← List.getD_eq_getElem?_getD]
            exact hb'
          rw [dif_pos hc]
          simpa using congrArg (fun s : Sym => s.1) hget
        · rw [dif_neg hc]
          rfl
      · intro h51
        simp [symInitialConfig] at h51
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      constructor
      · intro j hj
        rw [symStepConfig]
        by_cases hw : cfg'.headPos = j
        · have hcell : IsOutside (cfg'.tape j) := ih.1 j hj
          have hq' : cfg'.state < 102 := q12_path_state_lt102 input π₀ cfg' hprev
          have hne51 : cfg'.state ≠ 51 := by
            intro h51
            have hle := ih.2 h51
            omega
          have hw' : IsOutside step.result.writeSym :=
            q12_outside_write_closed cfg'.state hq' hne51 (cfg'.tape j) hcell step.result
              (by simpa [hread, hw] using htrans)
          simpa [hw] using hw'
        · dsimp [symStepConfig]
          rw [if_neg]
          · exact ih.1 j hj
          · exact Ne.symm hw
      · intro h51
        have hq' : cfg'.state < 102 := q12_path_state_lt102 input π₀ cfg' hprev
        have hinto := q12_into_51 cfg'.state hq' step.readSym step.result
          (by simpa [hread] using htrans) (by simpa [symStepConfig] using h51)
        rcases hinto with ⟨hq21, hsel, hL⟩
        have hpos : cfg'.headPos < (B : ℤ) := by
          by_contra hge
          have hcell := ih.1 cfg'.headPos (le_of_not_gt hge)
          rcases hsel with hsel' | hnosel'
          · rcases hcell with hd0 | hd1 | hc0
            · have hbad : SymKind.sel = SymKind.data0 := by
                rw [← hsel']
                rw [hread]
                exact hd0
              have hne : SymKind.sel ≠ SymKind.data0 := by decide
              exact hne hbad
            · have hbad : SymKind.sel = SymKind.data1 := by
                rw [← hsel']
                rw [hread]
                exact hd1
              have hne : SymKind.sel ≠ SymKind.data1 := by decide
              exact hne hbad
            · have hbad : SymKind.sel = SymKind.consumed := by
                rw [← hsel']
                rw [hread]
                exact hc0
              have hne : SymKind.sel ≠ SymKind.consumed := by decide
              exact hne hbad
          · rcases hcell with hd0 | hd1 | hc0
            · have hbad : SymKind.nosel = SymKind.data0 := by
                rw [← hnosel']
                rw [hread]
                exact hd0
              have hne : SymKind.nosel ≠ SymKind.data0 := by decide
              exact hne hbad
            · have hbad : SymKind.nosel = SymKind.data1 := by
                rw [← hnosel']
                rw [hread]
                exact hd1
              have hne : SymKind.nosel ≠ SymKind.data1 := by decide
              exact hne hbad
            · have hbad : SymKind.nosel = SymKind.consumed := by
                rw [← hnosel']
                rw [hread]
                exact hc0
              have hne : SymKind.nosel ≠ SymKind.consumed := by decide
              exact hne hbad
        change cfg'.headPos + step.result.moveDir.toInt ≤ (B : ℤ) - 1
        rw [hL, Dir.toInt]
        exact Int.sub_le_sub_right (le_of_lt hpos) (1 : ℤ)

/-- K1-Sym 头不变量(B 版):任意路径上,头 ≤ B ∨ 态 ≠ 100。
    q12_head_invariant(Reverse6:280)的逐字重放,右端 |input| → B。 -/
lemma a2_head_invariant_from (input : List Sym) (B : ℕ) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg)
    (hB : ∀ j : ℕ, B ≤ j → input.getD j Sym.blank = Sym.data0 false) :
    cfg.headPos ≤ (B : ℤ) ∨ cfg.state ≠ 100 := by
  induction h with
  | nil =>
      left
      simp [symInitialConfig]
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      by_cases hp : (symStepConfig cfg' step.result).headPos ≤ (B : ℤ)
      · left
        exact hp
      · right
        have hpre : (B : ℤ) ≤ cfg'.headPos := by
          have hm : step.result.moveDir.toInt ≤ 1 := by
            cases step.result.moveDir <;> norm_num [Dir.toInt]
          dsimp [symStepConfig] at hp
          omega
        have hQR := a2_outside_closed_from input B hprev hB
        have hcell : IsOutside (cfg'.tape cfg'.headPos) := hQR.1 cfg'.headPos hpre
        have hq' : cfg'.state < 102 := q12_path_state_lt102 input π₀ cfg' hprev
        have hcls := q12_outside_ne_100 cfg'.state hq' (cfg'.tape cfg'.headPos) hcell
          step.result (by simpa [hread] using htrans)
        intro hacc
        have hnext : step.result.nextState = 100 := by
          simpa [symStepConfig] using hacc
        rcases hcls with hne | h100S
        · exact hne hnext
        · rcases h100S with ⟨hq100, hS⟩
          rcases ih with hi1 | hi2
          · exfalso
            have hS' : step.result.moveDir.toInt = 0 := by
              rw [hS]
              rfl
            dsimp [symStepConfig] at hp
            omega
          · exact hi2 hq100

/-- K1-Sym 主件(终点版,逻辑正确):输入在 ≥ B 处全 data0-false 时,接受路径
    (终点 100)的终点头 ≤ B。每前缀版需 R' 链态域扩展(5/8/13/76/84 头 ≤ B-1 +
    尾区无 consumed 种子)——见 _q10-a2-design.md §5,下阶段。 -/
lemma a2_sym_accept_head_from (input : List Sym) (B : ℕ) {π : List SymStep}
    {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg) (hacc : cfg.state = 100)
    (hB : ∀ j : ℕ, B ≤ j → input.getD j Sym.blank = Sym.data0 false) :
    cfg.headPos ≤ (B : ℤ) := by
  rcases a2_head_invariant_from input B h hB with hp | hne
  · exact hp
  · exfalso
    exact hne hacc

/-- 辅助:可达 100 态的头 ≤ B(入边 23 读 boundary R——≥ B 处无 boundary(Q 类排除);
    100 S 自环保持)。 -/
lemma a2_sym100_head_from (input : List Sym) (B : ℕ) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg) (h100 : cfg.state = 100)
    (hB : ∀ j : ℕ, B ≤ j → input.getD j Sym.blank = Sym.data0 false) :
    cfg.headPos ≤ (B : ℤ) := by
  induction h with
  | nil => simp [symInitialConfig] at h100
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      have hq' : cfg'.state < 102 := q12_path_state_lt102 input π₀ cfg' hprev
      have hnext : step.result.nextState = 100 := by
        simpa [symStepConfig] using h100
      have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
          r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 100 →
          ((q : ℕ) = 23 ∧ s.1 = SymKind.boundary ∧ r.moveDir = Dir.R) ∨
            ((q : ℕ) = 100 ∧ r.moveDir = Dir.S) := by
        native_decide
      have hcls := hbb ⟨cfg'.state, hq'⟩ step.readSym step.result
        (by simpa [hread] using htrans) hnext
      rcases hcls with h23 | h100s
      · rcases h23 with ⟨hq23, hb, hdR⟩
        have h23f : step.fromState = 23 := by simpa [hfrom] using hq23
        -- 23 读 boundary @头:≥ B 处无 boundary(Q 类排除)
        have hQR := a2_outside_closed_from input B hprev hB
        have hlt : cfg'.headPos < (B : ℤ) := by
          by_contra hge
          have hcell := hQR.1 cfg'.headPos (le_of_not_gt hge)
          have hrd : step.readSym.1 = SymKind.boundary := hb
          have hbnd : (cfg'.tape cfg'.headPos).1 = SymKind.boundary := by
            simpa [← hread] using hrd
          rcases hcell with hd0 | hd1 | hc0
          · have hbad : SymKind.boundary = SymKind.data0 := by
              rw [← hbnd]
              exact hd0
            have hne : SymKind.boundary ≠ SymKind.data0 := by decide
            exact hne hbad
          · have hbad : SymKind.boundary = SymKind.data1 := by
              rw [← hbnd]
              exact hd1
            have hne : SymKind.boundary ≠ SymKind.data1 := by decide
            exact hne hbad
          · have hbad : SymKind.boundary = SymKind.consumed := by
              rw [← hbnd]
              exact hc0
            have hne : SymKind.boundary ≠ SymKind.consumed := by decide
            exact hne hbad
        simp [symStepConfig, hdR, Dir.toInt]
        omega
      · rcases h100s with ⟨hq100s, hS⟩
        have h100f : cfg'.state = 100 := by simpa [hfrom] using hq100s
        have hle := ih h100f
        simp [symStepConfig, hS, Dir.toInt]
        exact hle

end Mp
