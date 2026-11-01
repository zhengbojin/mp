import Mp.ATMDom
import Mp.ProjectionP

/-!
# `P_A = P_cb` 的机器层：`DTM ⇄ CBTM|0` 的配置对应

三条例外都已进定义：字母表 `{0,1}`、转移位置无关、空白 `0`。
本文件给出把两边计算逐步对应起来的基本块。
-/

set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false

namespace Mp

open F4

variable {M : ClassicDTM} {N : CBTM}

/-- 虚部为假 ⇒ 符号是 `0` 或 `1`。 -/
lemma im_false_zero_or_one {s : F4} (h : F4.im s = false) : s = F4.zero ∨ s = F4.one := by
  obtain ⟨re, im⟩ := s
  cases re <;> cases im <;> simp_all [F4.im, F4.zero, F4.one]

/-- `M.toCBTM hwrite` 是 **CBTM|0**（字母表 `{0,1}`、转移单值、位置无关）。

    2026-11-01：此定理曾被误判为 Lean C 后端崩溃源（实为 360 安全卫士拦截 lean 写 olean）。 -/
theorem isCBTM0_toCBTM (M : ClassicDTM)
    (hwrite : ∀ q s, F4.im (M.transition (q, s)).writeSym = false) :
    CBTM.IsCBTM0 (M.toCBTM hwrite) where
  alphabet_eq := rfl
  card_one := by
    intro q s i hs
    have hmem : s ∈ ({F4.zero, F4.one} : Finset F4) := by
      simpa [ClassicDTM.toCBTM] using hs
    rcases Finset.mem_insert.mp hmem with rfl | h1
    · have h := ClassicDTM.toCBTMTrans_zero M q i
      show (M.toCBTMTrans (q, F4.zero, i)).card = 1
      rw [h]; exact Finset.card_singleton _
    · rw [Finset.mem_singleton.mp h1]
      have h := ClassicDTM.toCBTMTrans_one M q i
      show (M.toCBTMTrans (q, F4.one, i)).card = 1
      rw [h]; exact Finset.card_singleton _
  pos_indep := by
    intro q s i j hs
    rfl

/-- 配置对应：状态、带头位置相同，纸带逐格相同。 -/
def CfgRel {x : List F4} (c : DTMConfig M) (c' : CBTMConfig N x) : Prop :=
  c.state = c'.state ∧ c.headPos = c'.headPos ∧ ∀ i : ℤ, c.tape.read i = c'.tape i

/-- 初始配置对应（需要同构给出起始态相等、且空白符相同）。 -/
lemma cfgRel_init (iso : StructIsoClassicDTM M N) (x : List F4)
    (hblank : N.blankSym = M.blankSym) :
    CfgRel (M := M) (N := N) (DTMInitialConfig M x) (initialConfig N x) := by
  refine ⟨?_, ?_, ?_⟩
  · show M.startState = N.startState
    exact iso.h_start
  · rfl
  · intro i
    simp only [DTMInitialConfig, initialConfig, DTMInitialTape, initialTapeOf, Tape.read, hblank]

/-- 一步对应：配置对应 + 所读符号在 `{0,1}` 内 ⇒ 一步之后仍对应。 -/
lemma cfgRel_step {x : List F4} (iso : StructIsoClassicDTM M N)
    {c : DTMConfig M} {c' : CBTMConfig N x} (hr : CfgRel c c')
    (hsym : c'.tape c'.headPos ∈ ({F4.zero, F4.one} : Finset F4))
    (hread : c.tape.read c.headPos = c'.tape c'.headPos) :
    CfgRel (M := M) (N := N)
      (DTMStepConfig c (M.transition (c.state, c.tape.read c.headPos)))
      (stepConfig c' (dtmResultToCBTM (M.transition (c.state, c.tape.read c.headPos)))) := by
  obtain ⟨hst, hpos, htape⟩ := hr
  have htr : N.transition (c'.state, c'.tape c'.headPos, c'.headPos)
      = {dtmResultToCBTM (M.transition (c.state, c.tape.read c.headPos))} := by
    have h0 := iso.h_transition c.state (c'.tape c'.headPos) hsym c'.headPos
    simpa [hst, hread] using h0
  refine ⟨rfl, ?_, ?_⟩
  · have hmv : (M.transition (c.state, c.tape.read c'.headPos)).move.toInt
        = (dtmResultToCBTM (M.transition (c.state, c.tape.read c'.headPos))).moveDir.toInt := rfl
    simp only [DTMStepConfig, stepConfig]
    rw [hpos, hmv]
  · intro i
    simp only [DTMStepConfig, stepConfig, Tape.read]
    rw [hpos]
    by_cases hi : i = c'.headPos
    · simp [hi, dtmResultToCBTM]
    · simp only [hi, if_false]
      exact htape i

-- ============================================================================
-- §2 纸带的 0/1 不变量与路径对应
-- ============================================================================

/-- 纸带每格都是 `0` 或 `1`。 -/
def AllZeroOne (t : Tape F4) : Prop := ∀ i, t.read i = F4.zero ∨ t.read i = F4.one

/-- 初始纸带满足 0/1 不变量（输入无标记、空白为 0）。 -/
lemma allZeroOne_init (x : List F4) (hnm : ∀ c ∈ x, F4.im c = false)
    (hb : M.blankSym = F4.zero) : AllZeroOne (DTMInitialConfig M x).tape := by
  intro i
  simp only [DTMInitialConfig, DTMInitialTape, Tape.read]
  by_cases hin : 0 ≤ i ∧ i.toNat < x.length
  · rw [dif_pos hin]
    exact im_false_zero_or_one (hnm _ (List.get_mem _ _))
  · rw [dif_neg hin, hb]
    exact Or.inl rfl

/-- 一步保持 0/1 不变量（机器不写标记）。 -/
lemma allZeroOne_step (hwrite : ∀ q s, F4.im (M.transition (q, s)).writeSym = false)
    {c : DTMConfig M} (h : AllZeroOne c.tape) (q : ℕ) (s : F4) :
    AllZeroOne (DTMStepConfig c (M.transition (q, s))).tape := by
  intro i
  by_cases hi : i = c.headPos
  · simp only [DTMStepConfig, Tape.read, hi, if_true]
    exact im_false_zero_or_one (hwrite q s)
  · simp only [DTMStepConfig, Tape.read, hi, if_false]
    exact h i

/-- 可达配置满足 0/1 不变量。 -/
lemma allZeroOne_of_path (hwrite : ∀ q s, F4.im (M.transition (q, s)).writeSym = false)
    (x : List F4) (hnm : ∀ c ∈ x, F4.im c = false) (hb : M.blankSym = F4.zero) :
    ∀ (π : List DTMTransitionStep) (cfg : DTMConfig M),
      DTMTapeReachablePath M x π cfg → AllZeroOne cfg.tape := by
  intro π cfg hpath
  induction hpath with
  | nil => exact allZeroOne_init x hnm hb
  | cons π₀ step cfg₀ hpath h_from h_read h_pos h_res ih =>
      rw [h_res]
      exact allZeroOne_step hwrite ih cfg₀.state (cfg₀.tape.read cfg₀.headPos)

/-- DTM 可达路径 ⇒ CBTM 可达路径（从各自初始配置出发）：配置逐步对应、路径长度相同。 -/
lemma path_fwd (iso : StructIsoClassicDTM M N)
    (hwrite : ∀ q s, F4.im (M.transition (q, s)).writeSym = false)
    (x : List F4) (hnm : ∀ c ∈ x, F4.im c = false)
    (hbM : M.blankSym = F4.zero) (hbN : N.blankSym = M.blankSym) :
    ∀ (π : List DTMTransitionStep) (cfg : DTMConfig M),
      DTMTapeReachablePath M x π cfg →
      ∃ (π' : ComputationPath) (cfg'' : CBTMConfig N x),
        TapeReachablePath N x π' cfg'' ∧ CfgRel cfg cfg'' ∧ π'.length = π.length := by
  intro π cfg hpath
  induction hpath with
  | nil =>
      exact ⟨[], initialConfig N x, TapeReachablePath.nil, cfgRel_init iso x hbN, rfl⟩
  | cons π₀ step cfg₀ hpath h_from h_read h_pos h_res ih =>
      obtain ⟨π', cfg'', hpath', hrel', hlen'⟩ := ih
      have hhd : cfg₀.headPos = cfg''.headPos := hrel'.2.1
      have hsym : cfg₀.tape.read cfg₀.headPos = cfg''.tape cfg''.headPos := by
        simpa [hhd] using hrel'.2.2 cfg₀.headPos
      have hz : cfg''.tape cfg''.headPos ∈ ({F4.zero, F4.one} : Finset F4) := by
        have h01 := allZeroOne_of_path hwrite x hnm hbM π₀ cfg₀ hpath cfg₀.headPos
        rw [← hsym]
        rcases h01 with h | h <;> simp [h]
      let st : TransitionStep :=
        { fromState := cfg''.state, readSym := cfg''.tape cfg''.headPos,
          result := dtmResultToCBTM step.result }
      have hmem : st.result ∈ N.transition (cfg''.state, cfg''.tape cfg''.headPos, cfg''.headPos) := by
        have h0 := iso.h_transition cfg''.state (cfg''.tape cfg''.headPos) hz cfg''.headPos
        rw [h0, Finset.mem_singleton]
        show dtmResultToCBTM step.result = dtmResultToCBTM (M.transition (cfg''.state, cfg''.tape cfg''.headPos))
        rw [h_res]
        rw [hrel'.1, hsym]
      refine ⟨π' ++ [st], stepConfig cfg'' (dtmResultToCBTM step.result), ?_, ?_, ?_⟩
      · exact TapeReachablePath.cons π' st cfg'' hpath' rfl rfl hmem
      · rw [h_res]
        exact cfgRel_step iso hrel' hz hsym
      · simp [hlen']

/-- 接受性（DTM ⇒ CBTM）：同构把 DTM 的接受路径搬到 CBTM。 -/
lemma accepts_of_dtm (iso : StructIsoClassicDTM M N)
    (hwrite : ∀ q s, F4.im (M.transition (q, s)).writeSym = false)
    (x : List F4) (hnm : ∀ c ∈ x, F4.im c = false)
    (hbM : M.blankSym = F4.zero) (hbN : N.blankSym = M.blankSym) :
    M.acceptsTape x → N.tapeAccepts x := by
  rintro ⟨π, cfg, hr, ha⟩
  obtain ⟨π', cfg', hr', hrel', _⟩ := path_fwd iso hwrite x hnm hbM hbN π cfg hr
  refine ⟨π', cfg', hr', ?_⟩
  rw [← hrel'.1, iso.h_accept]
  exact ha

/-- `dtmResultToCBTM` 单射。 -/
lemma dtmResultToCBTM_inj {r₁ r₂ : ClassicDTMTransitionResult}
    (h : dtmResultToCBTM r₁ = dtmResultToCBTM r₂) : r₁ = r₂ := by
  obtain ⟨a1, b1, c1⟩ := r₁
  obtain ⟨a2, b2, c2⟩ := r₂
  simp only [dtmResultToCBTM, CBTMTransResult.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [h1, h2, h3]

/-- `dtmMoveCount` 追加单步。 -/
private lemma dtmMoveCount_append_single (l : List DTMTransitionStep) (s : DTMTransitionStep) :
    dtmMoveCount (l ++ [s]) = dtmMoveCount l + (if isMovingDir s.result.move then 1 else 0) := by
  unfold dtmMoveCount
  rw [List.filter_append]
  simp [List.length_append]
  by_cases h : isMovingDir s.result.move <;> simp [h]

/-- `cbtmMoveCount` 追加单步。 -/
private lemma cbtmMoveCount_append_single (l : ComputationPath) (s : TransitionStep) :
    cbtmMoveCount (l ++ [s]) =
      cbtmMoveCount l + (if isMovingDir s.result.moveDir then 1 else 0) := by
  unfold cbtmMoveCount
  rw [List.filter_append]
  simp [List.length_append]
  by_cases h : isMovingDir s.result.moveDir <;> simp [h]

/-- CBTM 可达路径 ⇒ DTM 可达路径：配置逐步对应、路径长度相同、**移动数相同**。 -/
lemma path_bwd (iso : StructIsoClassicDTM M N) (x : List F4)
    (hbN : N.blankSym = M.blankSym) :
    ∀ (π' : ComputationPath) (cfg' : CBTMConfig N x),
      TapeReachablePath N x π' cfg' →
      ∃ (π : List DTMTransitionStep) (cfg : DTMConfig M),
        DTMTapeReachablePath M x π cfg ∧ CfgRel cfg cfg' ∧ π.length = π'.length ∧
        dtmMoveCount π = cbtmMoveCount π' ∧
        π.map (fun s => s.fromState) = π'.map (fun s => s.fromState) := by
  intro π' cfg' hpath
  induction hpath with
  | nil =>
      refine ⟨[], DTMInitialConfig M x, DTMTapeReachablePath.nil, ?_, rfl, rfl, rfl⟩
      refine ⟨?_, rfl, ?_⟩
      · show M.startState = N.startState
        exact iso.h_start
      · intro i
        simp only [DTMInitialConfig, initialConfig, DTMInitialTape, initialTapeOf, Tape.read, hbN]
  | cons π₀ step cfg₀ hpath h_from h_read hmem ih =>
      obtain ⟨π, cfg, hdtm, hrel', hlen, hmove, hstates⟩ := ih
      have hinAlph : step.readSym ∈ N.alphabet := by
        by_contra hnot
        have hempty : N.transition (cfg₀.state, cfg₀.tapeAt cfg₀.headPos, cfg₀.headPos) = ∅ :=
          N.h_transition_outside cfg₀.state (cfg₀.tapeAt cfg₀.headPos) cfg₀.headPos
            (by rwa [← h_read])
        rw [hempty] at hmem
        simpa using hmem
      have hz : step.readSym ∈ ({F4.zero, F4.one} : Finset F4) :=
        iso.h_restricted.h_alphabet_subset hinAlph
      have h0 := iso.h_transition cfg₀.state step.readSym hz cfg₀.headPos
      have hres : step.result = dtmResultToCBTM (M.transition (cfg₀.state, step.readSym)) := by
        have hm := hmem
        rw [← h_read] at hm
        rw [h0] at hm
        exact Finset.mem_singleton.mp hm
      have hsymEq : cfg.tape.read cfg.headPos = step.readSym := by
        rw [hrel'.2.2 cfg.headPos, hrel'.2.1]
        exact h_read.symm
      let st : DTMTransitionStep :=
        { fromState := cfg.state, readSym := cfg.tape.read cfg.headPos,
          pos := cfg.headPos, result := M.transition (cfg₀.state, step.readSym) }
      refine ⟨π ++ [st], DTMStepConfig cfg st.result, ?_, ?_, ?_, ?_, ?_⟩
      · refine DTMTapeReachablePath.cons π st cfg hdtm rfl ?_ rfl ?_
        · show st.readSym = cfg.tape.read cfg.headPos
          simp only [st]
        · show st.result = M.transition (cfg.state, cfg.tape.read cfg.headPos)
          simp only [st]
          rw [← hrel'.1, ← hsymEq]
      · refine ⟨?_, ?_, ?_⟩
        · simp only [DTMStepConfig, stepConfig, hres, dtmResultToCBTM, st]
        · simp only [DTMStepConfig, stepConfig, st, hres, dtmResultToCBTM]
          rw [hrel'.2.1]
        · intro i
          simp only [DTMStepConfig, stepConfig, Tape.read, st, hres, dtmResultToCBTM]
          rw [hrel'.2.1]
          by_cases hi : i = cfg₀.headPos
          · simp [hi]
          · simp only [hi, if_false]
            exact hrel'.2.2 i
      · simp [hlen]
      · -- 移动数相同
        have hstepmove : isMovingDir step.result.moveDir = isMovingDir st.result.move := by
          rw [hres]
          rfl
        calc
          dtmMoveCount (π ++ [st]) = dtmMoveCount π + (if isMovingDir st.result.move then 1 else 0) :=
            dtmMoveCount_append_single _ _
          _ = cbtmMoveCount π₀ + (if isMovingDir step.result.moveDir then 1 else 0) := by
            rw [hmove, hstepmove]
          _ = cbtmMoveCount (π₀ ++ [step]) := (cbtmMoveCount_append_single _ _).symm
      · -- fromState 序列相同（首达性搬运用）
        simp only [List.map_append, List.map_cons, List.map_nil]
        rw [hstates]
        simp
        show cfg.state = step.fromState
        rw [hrel'.1, h_from]

/-- 接受性（CBTM ⇒ DTM）。 -/
lemma accepts_of_cbtm (iso : StructIsoClassicDTM M N) (x : List F4)
    (hbN : N.blankSym = M.blankSym) :
    N.tapeAccepts x → M.acceptsTape x := by
  rintro ⟨π', cfg', hr, ha⟩
  obtain ⟨π, cfg, hdtm, hrel', _, _, _⟩ := path_bwd iso x hbN π' cfg' hr
  refine ⟨π, cfg, hdtm, ?_⟩
  rw [hrel'.1, ← iso.h_accept]
  exact ha

/-- **接受性等价**（同构 + 输入无标记 + 不写标记 + 空白一致）。 -/
theorem accepts_iff_p (iso : StructIsoClassicDTM M N)
    (hwrite : ∀ q s, F4.im (M.transition (q, s)).writeSym = false)
    (x : List F4) (hnm : ∀ c ∈ x, F4.im c = false)
    (hbM : M.blankSym = F4.zero) (hbN : N.blankSym = M.blankSym) :
    M.acceptsTape x ↔ N.tapeAccepts x :=
  ⟨accepts_of_dtm iso hwrite x hnm hbM hbN, accepts_of_cbtm iso x hbN⟩

/-- 停机性（DTM ⇒ CBTM）：到判态的路径被搬到 CBTM。 -/
lemma halts_of_dtm (iso : StructIsoClassicDTM M N)
    (hwrite : ∀ q s, F4.im (M.transition (q, s)).writeSym = false)
    (hbM : M.blankSym = F4.zero) (hbN : N.blankSym = M.blankSym) :
    ClassicDTM.IsAlgorithmOn M noMarkDomain → CBTM.IsAlgorithmOn N noMarkDomain := by
  rintro h x ⟨hal, hnm⟩
  obtain ⟨π, cfg, hr, ha⟩ := h x ⟨hal, hnm⟩
  obtain ⟨π', cfg', hr', hrel', _⟩ := path_fwd iso hwrite x hnm hbM hbN π cfg hr
  refine ⟨π', cfg', hr', ?_⟩
  rw [← hrel'.1, iso.h_accept, iso.h_reject]
  exact ha

/-- 停机性（CBTM ⇒ DTM）。 -/
lemma halts_of_cbtm (iso : StructIsoClassicDTM M N) (hbN : N.blankSym = M.blankSym) :
    CBTM.IsAlgorithmOn N noMarkDomain → ClassicDTM.IsAlgorithmOn M noMarkDomain := by
  rintro h x ⟨hal, hnm⟩
  obtain ⟨π', cfg', hr, ha⟩ := h x ⟨hal, hnm⟩
  obtain ⟨π, cfg, hdtm, hrel', _, _, _⟩ := path_bwd iso x hbN π' cfg' hr
  refine ⟨π, cfg, hdtm, ?_⟩
  rw [hrel'.1, ← iso.h_accept, ← iso.h_reject]
  exact ha

-- ============================================================================
-- §3 计时口径：两侧都用「移动数」（与项目口径「成本 = 位移」一致）
-- ============================================================================

-- 注：`cbtmMoveCount` 已在 `Mp/ATMDom.lean` 定义（本文件 import 之），此处不再重复定义。

/-- `dtmStepToCBTM` 保持移动方向，故移动数不变。 -/
lemma dtmMoveCount_map (π : List DTMTransitionStep) :
    cbtmMoveCount (π.map dtmStepToCBTM) = dtmMoveCount π := by
  unfold cbtmMoveCount dtmMoveCount
  induction π with
  | nil => rfl
  | cons st rest ih =>
      simp only [List.map_cons, List.filter_cons]
      cases h : isMovingDir st.result.move <;>
        simp [h, dtmStepToCBTM, dtmResultToCBTM, ih]

-- ============================================================================
-- §4 第二层：`P_A ⊆ P_cb` 与 `P_A ≠ NP_A`
-- ============================================================================
-- 见 `Mp/SecondLayer.lean`（避免与 ATMDom/ATMAssembly 的层序耦合）。

end Mp











