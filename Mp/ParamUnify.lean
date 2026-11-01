import Mp.ATMBasic

/-!
# 参数化统一：CBTM|0 = DTM（纸带 = 2F4，虚位是参数）

用户裁决（2026-10-31）：「布尔图灵机与复布尔图灵机可以用参数化的方式统一用复布尔图灵机
来描述，即得到 CBTM|0 与 FULL CBTM。所以有 CBTM|0 = DTM。」

形式内容（本文件）：

* 纸带格 = `PCell := CBTMCell2 = F4 × F4`（`Mp/ATMBasic.lean` §7 的多带视图）。
  **逻辑符号 = `cellData c = (c.1.1, c.2.1)`（4 值：0/1/sep/#）**，与虚位无关；
  **虚位参数 = `pVirt c = c.1.2 || c.2.2`**。
* `PCBTM`：纸带为 `PCell` 的参数化机；虚位 ≡ 0 的档 = **CBTM|0**；虚位自由的档 = **FULL CBTM**。
* `ClassicDT(dtmToPC M)`：把 DTM 的参数档固定为「虚位关」——每个格都写成 `liftInput ·`（虚位全 false），
  逻辑符号逐点保持（`cellData (liftInput s) = s`）。
* **`toPC_accepts_iff`**：`(dtmToPC M)` 接受 `x.map liftInput` ⟺ `M` 接受 `x`，且**路径步数一一对应**。

这就把「CBTM|0 = DTM」落成机器级等同：同状态、同转移图（在虚位关上）、输入经 `liftInput` 嵌入。
-/

namespace Mp
namespace ParamUnify

-- ============================================================================
-- §1 参数化纸带格：逻辑符号 vs 虚位
-- ============================================================================

/-- 参数化纸带格（2F4）。 -/
abbrev PCell : Type := CBTMCell2

/-- 逻辑符号（4 值：0/1/sep/#）——虚位关时仍可读。 -/
def pData (c : PCell) : F4 := cellData c

/-- 虚位参数：两个虚部标志的或。 -/
def pVirt (c : PCell) : Bool := c.1.2 || c.2.2

/-- 虚位关 ⟺ 两个虚部全假。 -/
lemma pVirt_eq_false_iff (c : PCell) : pVirt c = false ↔ cellZeroVirt c := by
  rcases c with ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩
  simp [pVirt, cellZeroVirt, Bool.or_eq_false_iff]

/-- 虚位关时，`liftInput` 与 `cellData` 互逆。 -/
lemma liftInput_cellData {c : PCell} (h : cellZeroVirt c) : liftInput (cellData c) = c := by
  rcases c with ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩
  simp [cellZeroVirt] at h
  obtain ⟨h1, h2⟩ := h
  subst h1; subst h2
  rfl

/-- `liftInput` 的像虚位恒关。 -/
lemma pVirt_liftInput (s : F4) : pVirt (liftInput s) = false := by
  rw [pVirt_eq_false_iff]
  exact cellZeroVirt_liftInput s

/-- 逻辑符号在 `liftInput` 下保持不变。 -/
lemma cellData_liftInput' (s : F4) : cellData (liftInput s) = s := cellData_liftInput s

-- ============================================================================
-- §2 参数化机与磁带语义
-- ============================================================================

/-- 参数化 CBTM：纸带 = `PCell`，转移结果 = `(后继状态, 写格, 方向)`。 -/
structure PCBTM where
  states : Finset ℕ
  startState : ℕ
  acceptStates : Finset ℕ
  rejectStates : Finset ℕ
  alphabet : Finset PCell
  transition : ℕ × PCell × ℤ → Finset (ℕ × PCell × Dir)
  blankCell : PCell
  h_start_in_states : startState ∈ states
  h_accept_subset : acceptStates ⊆ states
  h_reject_subset : rejectStates ⊆ states
  isValid : ∀ q c i, c ∈ alphabet → ∀ r ∈ transition (q, c, i), r.1 ∈ states

/-- 格局。 -/
structure PCConfig (P : PCBTM) (x : List PCell) where
  state : ℕ
  tape : ℤ → PCell
  headPos : ℤ

/-- 初始格局：输入直铺 [0, n)，其余为空白格。 -/
def pcInitial (P : PCBTM) (x : List PCell) : PCConfig P x :=
  { state := P.startState,
    tape := fun i => if h : 0 ≤ i ∧ i.toNat < x.length then x.get ⟨i.toNat, h.2⟩ else P.blankCell,
    headPos := 0 }

/-- 一步格局。 -/
def pcStep {P : PCBTM} {x : List PCell} (cfg : PCConfig P x) (r : ℕ × PCell × Dir) :
    PCConfig P x :=
  { state := r.1,
    tape := fun i => if i = cfg.headPos then r.2.1 else cfg.tape i,
    headPos := cfg.headPos + r.2.2.toInt }

/-- 磁带语义可达路径（步列表）。 -/
inductive PCTapeReach (P : PCBTM) (x : List PCell) :
    List (ℕ × PCell × Dir) → PCConfig P x → Prop
  | nil : PCTapeReach P x [] (pcInitial P x)
  | cons : ∀ (π : List (ℕ × PCell × Dir)) (cfg : PCConfig P x) (r : ℕ × PCell × Dir),
      PCTapeReach P x π cfg →
      r ∈ P.transition (cfg.state, cfg.tape cfg.headPos, cfg.headPos) →
      PCTapeReach P x (π ++ [r]) (pcStep cfg r)

/-- 接受：存在一条末端在接受态的可达路径。 -/
def PCBTM.pcAccepts (P : PCBTM) (x : List PCell) : Prop :=
  ∃ (π : List (ℕ × PCell × Dir)) (cfg : PCConfig P x),
    PCTapeReach P x π cfg ∧ cfg.state ∈ P.acceptStates

-- ============================================================================
-- §3 DTM → 参数化机（虚位关档）
-- ============================================================================

/-- DTM 的参数化转移：读格虚位关时走 DTM 的转移（写 `liftInput`，逻辑符号保存）。 -/
noncomputable def pcTransOf (M : ClassicDTM) : ℕ × PCell × ℤ → Finset (ℕ × PCell × Dir) :=
  fun (q, c, _) =>
    if h : pVirt c = true then ∅
    else
      let r := M.transition (q, cellData c)
      {(r.nextState, liftInput r.writeSym, r.move)}

/-- **DTM 的参数档：虚位恒关**。 -/
noncomputable def dtmToPC (M : ClassicDTM) : PCBTM :=
  { states := M.states
    startState := M.startState
    acceptStates := M.acceptStates
    rejectStates := M.rejectStates
    alphabet := {liftInput F4.zero, liftInput F4.one, liftInput F4.alpha, liftInput F4.beta}
    transition := pcTransOf M
    blankCell := liftInput M.blankSym
    h_start_in_states := M.h_start_in_states
    h_accept_subset := M.h_accept_subset
    h_reject_subset := M.h_reject_subset
    isValid := by
      intro q c i _ r hr
      by_cases hv : pVirt c = true
      · simp only [pcTransOf, dif_pos hv] at hr
        simp at hr
      · simp only [pcTransOf, dif_neg hv] at hr
        rw [Finset.mem_singleton] at hr
        subst hr
        exact M.isValid q (cellData c) }

/-- 虚位关时的转移展开。 -/
lemma toPC_trans {M : ClassicDTM} {q : ℕ} {c : PCell} {i : ℤ} (hv : pVirt c = false) :
    (dtmToPC M).transition (q, c, i) =
      {((M.transition (q, cellData c)).nextState,
        liftInput (M.transition (q, cellData c)).writeSym,
        (M.transition (q, cellData c)).move)} := by
  have hv' : ¬ (pVirt c = true) := by rw [hv]; simp
  simp only [dtmToPC, pcTransOf, dif_neg hv']

-- ============================================================================
-- §4 模拟不变量与两个方向
-- ============================================================================

/-- PC 格局与 DTM 格局的模拟关系（含「所有格虚位关」不变式）。 -/
def SimPC (M : ClassicDTM) {x : List F4}
    (cfg : PCConfig (dtmToPC M) (x.map liftInput)) (dcfg : DTMConfig M) : Prop :=
  cfg.state = dcfg.state ∧ cfg.headPos = dcfg.headPos ∧
  ∀ i : ℤ, cellData (cfg.tape i) = dcfg.tape.read i ∧ pVirt (cfg.tape i) = false

/-- 初始格局满足模拟关系。 -/
lemma simPC_init (M : ClassicDTM) (x : List F4) :
    SimPC M (pcInitial (dtmToPC M) (x.map liftInput)) (DTMInitialConfig M x) := by
  refine ⟨rfl, rfl, ?_⟩
  intro i
  have hlen : (List.map liftInput x).length = x.length := List.length_map ..
  by_cases hi : 0 ≤ i ∧ i.toNat < x.length
  · have hi' : 0 ≤ i ∧ i.toNat < (List.map liftInput x).length := by rw [hlen]; exact hi
    have hpc : (pcInitial (dtmToPC M) (List.map liftInput x)).tape i
        = liftInput (x.get ⟨i.toNat, hi.2⟩) := by
      simp only [pcInitial]
      rw [dif_pos hi']
      simp
    have hdtm : (DTMInitialConfig M x).tape.read i = x.get ⟨i.toNat, hi.2⟩ := by
      simp only [DTMInitialConfig, Tape.read, DTMInitialTape]
      rw [dif_pos hi]
    rw [hpc, hdtm]
    exact ⟨cellData_liftInput' _, pVirt_liftInput _⟩
  · have hi' : ¬ (0 ≤ i ∧ i.toNat < (List.map liftInput x).length) := by rw [hlen]; exact hi
    have hpc : (pcInitial (dtmToPC M) (List.map liftInput x)).tape i
        = liftInput M.blankSym := by
      simp only [pcInitial, dtmToPC]
      rw [dif_neg hi']
    have hdtm : (DTMInitialConfig M x).tape.read i = M.blankSym := by
      simp only [DTMInitialConfig, Tape.read, DTMInitialTape]
      rw [dif_neg hi]
    rw [hpc, hdtm]
    exact ⟨cellData_liftInput' _, pVirt_liftInput _⟩

/-- 一步对应（前向）：PC 一步 ⇒ DTM 一步，保持不变量。 -/
lemma sim_pc_step {M : ClassicDTM} {x : List F4}
    {cfg : PCConfig (dtmToPC M) (x.map liftInput)} {dcfg : DTMConfig M}
    (hsim : SimPC M cfg dcfg) (r : ℕ × PCell × Dir)
    (hmem : r ∈ (dtmToPC M).transition (cfg.state, cfg.tape cfg.headPos, cfg.headPos)) :
    SimPC M (pcStep cfg r)
      (DTMStepConfig dcfg { nextState := r.1, writeSym := cellData r.2.1, move := r.2.2 }) := by
  obtain ⟨hs1, hs2, hs3⟩ := hsim
  have hv : pVirt (cfg.tape cfg.headPos) = false := (hs3 cfg.headPos).2
  rw [toPC_trans hv] at hmem
  rw [Finset.mem_singleton] at hmem
  subst hmem
  refine ⟨?_, ?_, ?_⟩
  · simp [pcStep, DTMStepConfig, hs1]
  · simp only [pcStep, DTMStepConfig]
    rw [hs2]
  · intro i
    simp only [pcStep, DTMStepConfig, Tape.read]
    rw [hs2]
    by_cases hi : i = dcfg.headPos
    · rw [if_pos hi, if_pos hi]
      exact ⟨cellData_liftInput' _, pVirt_liftInput _⟩
    · rw [if_neg hi, if_neg hi]
      exact hs3 i

/-- 一步对应（后向）：DTM 一步 ⇒ PC 一步，保持不变量。 -/
lemma sim_dtm_step {M : ClassicDTM} {x : List F4}
    {cfg : PCConfig (dtmToPC M) (x.map liftInput)} {dcfg : DTMConfig M}
    (hsim : SimPC M cfg dcfg) (r : ClassicDTMTransitionResult)
    (hmem : (r.nextState, liftInput r.writeSym, r.move) ∈
      (dtmToPC M).transition (cfg.state, cfg.tape cfg.headPos, cfg.headPos)) :
    SimPC M (pcStep cfg (r.nextState, liftInput r.writeSym, r.move)) (DTMStepConfig dcfg r) := by
  obtain ⟨hs1, hs2, hs3⟩ := hsim
  refine ⟨?_, ?_, ?_⟩
  · simp [pcStep, DTMStepConfig, hs1]
  · simp only [pcStep, DTMStepConfig]
    rw [hs2]
  · intro i
    simp only [pcStep, DTMStepConfig, Tape.read]
    rw [hs2]
    by_cases hi : i = dcfg.headPos
    · rw [if_pos hi, if_pos hi]
      exact ⟨cellData_liftInput' _, pVirt_liftInput _⟩
    · rw [if_neg hi, if_neg hi]
      exact hs3 i


-- ============================================================================
-- §5 路径级对应与主定理（接受一致 + 步数一致）
-- ============================================================================

/-- 前向：PC 可达路径 ⇒ 同步数的 DTM 可达路径。 -/
lemma path_forward (M : ClassicDTM) (x : List F4) :
    ∀ (π : List (ℕ × PCell × Dir)) (cfg : PCConfig (dtmToPC M) (x.map liftInput)),
      PCTapeReach (dtmToPC M) (x.map liftInput) π cfg →
      ∃ (π' : List DTMTransitionStep) (dcfg : DTMConfig M),
        DTMTapeReachablePath M x π' dcfg ∧ π'.length = π.length ∧ SimPC M cfg dcfg := by
  intro π cfg hp
  induction hp with
  | nil => exact ⟨[], _, DTMTapeReachablePath.nil, rfl, simPC_init M x⟩
  | cons π₀ cfg r hpath hmem ih =>
      obtain ⟨π', dcfg, hdtm, hlen, hsim⟩ := ih
      have hsimK := hsim
      obtain ⟨hs1, hs2, hs3⟩ := hsim
      have hv : pVirt (cfg.tape cfg.headPos) = false := (hs3 cfg.headPos).2
      have hsingle := toPC_trans (M := M) (q := cfg.state) (c := cfg.tape cfg.headPos)
        (i := cfg.headPos) hv
      rw [hsingle] at hmem
      rw [Finset.mem_singleton] at hmem
      subst hmem
      let dstep : DTMTransitionStep :=
        { fromState := cfg.state, readSym := cellData (cfg.tape cfg.headPos), pos := cfg.headPos,
          result := { nextState := (M.transition (cfg.state, cellData (cfg.tape cfg.headPos))).nextState,
                      writeSym := cellData (liftInput (M.transition (cfg.state, cellData (cfg.tape cfg.headPos))).writeSym),
                      move := (M.transition (cfg.state, cellData (cfg.tape cfg.headPos))).move } }
      have hmem' : ((M.transition (cfg.state, cellData (cfg.tape cfg.headPos))).nextState,
          liftInput (M.transition (cfg.state, cellData (cfg.tape cfg.headPos))).writeSym,
          (M.transition (cfg.state, cellData (cfg.tape cfg.headPos))).move)
          ∈ (dtmToPC M).transition (cfg.state, cfg.tape cfg.headPos, cfg.headPos) := by
        rw [hsingle]
        exact Finset.mem_singleton.mpr rfl
      refine ⟨π' ++ [dstep], DTMStepConfig dcfg dstep.result, ?_, ?_,
        sim_pc_step hsimK _ hmem'⟩
      · refine DTMTapeReachablePath.cons π' dstep dcfg hdtm ?_ ?_ ?_ ?_
        · show cfg.state = dcfg.state
          exact hs1
        · show cellData (cfg.tape cfg.headPos) = dcfg.tape.read dcfg.headPos
          rw [← hs2]
          exact (hs3 _).1
        · show cfg.headPos = dcfg.headPos
          exact hs2
        · show dstep.result = M.transition (dcfg.state, dcfg.tape.read dcfg.headPos)
          show ({ nextState := (M.transition (cfg.state, cellData (cfg.tape cfg.headPos))).nextState,
                  writeSym := cellData (liftInput (M.transition (cfg.state, cellData (cfg.tape cfg.headPos))).writeSym),
                  move := (M.transition (cfg.state, cellData (cfg.tape cfg.headPos))).move } : ClassicDTMTransitionResult)
              = M.transition (dcfg.state, dcfg.tape.read dcfg.headPos)
          rw [show cellData (liftInput (M.transition (cfg.state, cellData (cfg.tape cfg.headPos))).writeSym)
              = (M.transition (cfg.state, cellData (cfg.tape cfg.headPos))).writeSym from
            cellData_liftInput' _]
          rw [hs1, hs2, (hs3 dcfg.headPos).1]
      · simp [hlen]

/-- 后向：DTM 可达路径 ⇒ 同步数的 PC 可达路径。 -/
lemma path_backward (M : ClassicDTM) (x : List F4) :
    ∀ (π : List DTMTransitionStep) (dcfg : DTMConfig M),
      DTMTapeReachablePath M x π dcfg →
      ∃ (π' : List (ℕ × PCell × Dir)) (cfg : PCConfig (dtmToPC M) (x.map liftInput)),
        PCTapeReach (dtmToPC M) (x.map liftInput) π' cfg ∧ π'.length = π.length ∧
        SimPC M cfg dcfg := by
  intro π dcfg hp
  induction hp with
  | nil => exact ⟨[], _, PCTapeReach.nil, rfl, simPC_init M x⟩
  | cons π₀ step cfg hpath hfrom hread hpos hres ih =>
      obtain ⟨π', cfgc, hpc, hlen, hsim⟩ := ih
      have hsimK := hsim
      obtain ⟨hs1, hs2, hs3⟩ := hsim
      have hv : pVirt (cfgc.tape cfgc.headPos) = false := (hs3 cfgc.headPos).2
      have hmatch : M.transition (cfg.state, cfg.tape.read cfg.headPos)
          = M.transition (cfgc.state, cellData (cfgc.tape cfgc.headPos)) := by
        rw [← hs1, ← hs2, ← (hs3 _).1]
      have hmem : (step.result.nextState, liftInput step.result.writeSym, step.result.move)
          ∈ (dtmToPC M).transition (cfgc.state, cfgc.tape cfgc.headPos, cfgc.headPos) := by
        rw [toPC_trans (M := M) (q := cfgc.state) (c := cfgc.tape cfgc.headPos)
          (i := cfgc.headPos) hv, Finset.mem_singleton, hres, hmatch]
      refine ⟨π' ++ [(step.result.nextState, liftInput step.result.writeSym, step.result.move)],
        pcStep cfgc (step.result.nextState, liftInput step.result.writeSym, step.result.move),
        ?_, ?_, sim_dtm_step hsimK step.result hmem⟩
      · refine PCTapeReach.cons π' cfgc _ hpc hmem
      · simp [hlen]

/-- **主定理（参数化统一）**：`dtmToPC M` 在「虚位关」档上接受
    `x.map liftInput` ⟺ `M` 接受 `x`。即 **CBTM|0 = DTM**。 -/
theorem toPC_accepts_iff (M : ClassicDTM) (x : List F4) :
    (dtmToPC M).pcAccepts (x.map liftInput) ↔ M.acceptsTape x := by
  constructor
  · rintro ⟨π, cfg, hpc, hacc⟩
    obtain ⟨π', dcfg, hdtm, hlen, hsim⟩ := path_forward M x π cfg hpc
    exact ⟨π', dcfg, hdtm, by rw [← hsim.1]; exact hacc⟩
  · rintro ⟨π, dcfg, hdtm, hacc⟩
    obtain ⟨π', cfg, hpc, hlen, hsim⟩ := path_backward M x π dcfg hdtm
    exact ⟨π', cfg, hpc, by rw [hsim.1]; exact hacc⟩

end ParamUnify
end Mp
