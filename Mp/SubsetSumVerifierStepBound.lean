/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/


import Mp.SubsetSumVerifierCore
import Mp.SubsetSumVerifierReverse10
import Mp.SubsetSumVerifierCBTM3
import Mp.SubsetSumVerifierPosBound

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

/-!
# StepBound：Canonical ③（路径长度多项式界）的 Sym 层素材

计划（见 A1Progress.md §5.3）：
- C1：可延拓 ⟹ 无陷阱（101 吸收锁定；本文件首件）
- C2：块分解长度换算（accept_path_is_good_block_path → π.length = 12·块数）
- C3（核心）：Sym 层全局步数界 π.length ≤ (m+1)·(|x|+1)²
  语义依据：验证器全流程 = 每元素每数据位一轮（减法循环）、每轮全距穿越 O(|x|)、
  每轮必读 ≥1 标记 → 轮数 ≤ m+1；轮内步数上界可粗（常数被 K 吸收）。
- C4：③ 形状组装（对可延拓路径，拒绝-S 停滞尾部支恒假——qReject=101 见 Core:359）。

只读依赖：Mp.SubsetSumVerifierCore（SymSteps/VerifierSym/symSteps_initial_iff）、
Mp.SubsetSumVerifierReverse10（sym_absorb_101/symSteps_absorb101_locked）。
本文件为③线独占，不修改任何其它文件。
-/



namespace Mp

-- ==============================================================================
-- C1：可延拓 ⟹ 无陷阱（101 吸收锁定）
-- ==============================================================================

/-- 从任意配置出发的 SymSteps：终点态 ≠ 101 ⟹ 全程每步 nextState ≠ 101
    （反证：一旦某步进入 101，其后的步全部被 101 吸收锁定，终点必为 101）。 -/
lemma symSteps_next_ne101_of_end_ne101 {cfg₀ cfg : SymConfig} {π : List SymStep}
    (h : SymSteps VerifierSym.transition cfg₀ π cfg) (hne : cfg.state ≠ 101) :
    ∀ step ∈ π, step.result.nextState ≠ 101 := by
  induction h with
  | nil => intro step hs; simp at hs
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      have hne_step : step.result.nextState ≠ 101 := by
        intro h101
        apply hne
        dsimp [symStepConfig]
        exact h101
      have hne₁ : cfg₁.state ≠ 101 := by
        intro h₁₀₁
        have habs := sym_absorb_101 (cfg₁.tape cfg₁.headPos) step.result
          (by simpa [h₁₀₁] using htrans)
        apply hne
        dsimp [symStepConfig]
        exact habs.1
      intro s hs
      rw [List.mem_append] at hs
      rcases hs with (hs | hs)
      · exact ih hne₁ s hs
      · rcases (List.mem_singleton.mp hs) with rfl
        exact hne_step

/-- C1 主件：可延拓到接受态的 Sym 层路径全程无 101 步
    （101 = qReject 吸收态，任何进入 101 的路径都被锁定在 101，不可到达 100）。 -/
lemma symPath_next_ne101_of_extendable (input : List Sym) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg)
    (hext : ∃ π₂ cfg₂, SymReachablePath VerifierSym.transition input (π ++ π₂) cfg₂ ∧
        cfg₂.state ∈ VerifierSym.acceptStates) :
    ∀ step ∈ π, step.result.nextState ≠ 101 := by
  rcases hext with ⟨π₂, cfg₂, hfull, hacc⟩
  have hne : cfg₂.state ≠ 101 := by
    intro h₁₀₁
    have : 101 ∈ VerifierSym.acceptStates := by
      simpa [h₁₀₁] using hacc
    simp [VerifierSym.acceptStates, VerifierSym.qAccept] at this
  have hS := (symSteps_initial_iff VerifierSym.transition input (π ++ π₂) cfg₂).mpr hfull
  have hall := symSteps_next_ne101_of_end_ne101 hS hne
  intro step hs
  exact hall step (List.mem_append.mpr (Or.inl hs))


-- ==============================================================================
-- C3 位置域依赖方案（2026-09-09 修订）：
--   Canonical ③ 的 π 是 NTM2 层路径 = F4 层路径（同层！）——每步位置界 [0,|x|]
--   直接由 ①线 A-1（装配主定理，PosBound 侧）交付，③ 无需重证 q12 加强版；
--   Sym 层段分析需要「Sym 步位置 ∈ [0, 4L']」——由 A-1 的 F4 层界 +
--   good_block_path_head_corresp/块级包络（Reverse10 tapeSteps12_headPos_inside）合成，
--   与 ① 装配链同源。左界已就绪（A-3 sym_accept_prefix_head_nonneg）。
-- 表级事实（探针 _chkC3d 2026-09-09 确认，右界/域论证素材）：
--   读 (boundary,true)(#₁) 且 R 的态 = {0,1,9,11,14,20,23,28,77,81,85}（写 B 或 101/100/4/…）；
--   读 (boundary,false)(#ₗ/#₀) 且 L 的态 = {3,5,8,10,13,26,76,84}（26 写 B L——左越界候选需域排除）；
--   读 blank(= data0 false) 非漂移态 → 101 吸收（S/L）；漂移态 {9,77,84,85} 读 blank 自环 L（A 件）。
-- C3 段分析依赖就绪清单：分解（本文件）、单步形态（本文件）、A-1 位置域（①线）、
--   A-3 左界（PosBound:1878）、C1 无 101（本文件）。
-- ==============================================================================

/-- SymSteps 前缀分解：全长 cfg₀ -π₀++rest→ cfg' ⟹ 存在中间 cfg₁（前缀终点/后缀起点）。 -/
lemma symSteps_append_split {M : ℕ × Sym → Finset SymTransResult} {cfg₀ cfg' : SymConfig}
    {π₀ rest : List SymStep} (h : SymSteps M cfg₀ (π₀ ++ rest) cfg') :
    ∃ cfg₁ : SymConfig, SymSteps M cfg₀ π₀ cfg₁ ∧ SymSteps M cfg₁ rest cfg' := by
  revert h
  revert cfg'
  induction rest using List.reverseRecOn with
  | nil =>
      intro cfg' h
      refine ⟨cfg', ?_, ?_⟩
      · simpa using h
      · exact SymSteps.nil
  | append_singleton rest' step ih =>
      intro cfg' h
      rw [← List.append_assoc] at h
      generalize hL : (π₀ ++ rest') ++ [step] = L at h
      induction h with
      | nil => simp at hL
      | cons πs step' cfg₁ hprev hfrom hread htrans _ =>
          -- (π₀ ++ rest') ++ [step] = πs ++ [step'] ⟹ πs = π₀ ++ rest' ∧ step' = step
          have hsnoc := snoc_eq_snoc (α := SymStep) (π₁ := π₀ ++ rest') (π₂ := πs)
            (a := step) (b := step') (by simpa [List.append_assoc] using hL)
          rcases hsnoc with ⟨hπs, hstep'⟩
          subst hstep'
          have hprev' : SymSteps M cfg₀ (π₀ ++ rest') cfg₁ := by simpa [hπs] using hprev
          rcases ih hprev' with ⟨cfg₂, h₁, h₂⟩
          refine ⟨cfg₂, h₁, ?_⟩
          have hlast : SymSteps M cfg₁ [step] (symStepConfig cfg₁ step.result) := by
            exact SymSteps.cons (M := M) (cfg₀ := cfg₁) [] step cfg₁
              SymSteps.nil hfrom hread htrans
          simpa [List.append_assoc] using
            (symSteps_append_concat (π₁ := rest') ([step]) h₂ hlast)

/-- 单步路径的形态：Steps cfg₀ [step] cfg' ⟹ fromState 一致且 cfg' 是步后配置。 -/
lemma symSteps_singleton_fromState {M : ℕ × Sym → Finset SymTransResult} {cfg₀ cfg' : SymConfig}
    {step : SymStep} (h : SymSteps M cfg₀ [step] cfg') :
    step.fromState = cfg₀.state ∧ cfg' = symStepConfig cfg₀ step.result := by
  generalize hL : [step] = L at h
  induction h with
  | nil => simp at hL
  | cons πs step' cfg₁ hprev hfrom hread htrans _ =>
      have hsnoc := snoc_eq_snoc (α := SymStep) (π₁ := []) (π₂ := πs)
        (a := step) (b := step') (by simpa using hL)
      rcases hsnoc with ⟨hπs, hstep'⟩
      subst hstep'
      have hcfg₁ : cfg₁ = cfg₀ := symSteps_nil_cfg (by simpa [hπs] using hprev)
      constructor
      · rw [hfrom, hcfg₁]
      · dsimp [symStepConfig]
        rw [hcfg₁]
namespace SymToF4

/-- C2：GoodBlockPath 的路径长度 = 12·块数（每 GoodBlock 恰 12 步）。
     （③ 的 F4 微步数 = 12·Sym 符号步数的块级半边；另一半边（块数 = Sym 步数）
     由 project_path/symPath_to_blockPath 在合龙时接。） -/
lemma goodBlockPath_length_eq {w : List F4} {cfgc cfgc' : CBTMConfig subsetSumCBTM w}
    {π : ComputationPath} (h : GoodBlockPath w cfgc π cfgc') :
    ∃ n : ℕ, π.length = 12 * n := by
  induction h with
  | nil => exact ⟨0, by simp⟩
  | cons cfgc cfgm cfgc' πm π cfgs p q sym r hb hrest ih =>
      rcases ih with ⟨n, hn⟩
      rcases hb with ⟨hpath, hlen, hrest_fields⟩
      refine ⟨n + 1, ?_⟩
      simp [List.length_append]
      rw [hlen, hn]
      ring

end SymToF4


-- ==============================================================================
-- C3 段分析（M2 结构件，2026-09-10 主控）：
--   按「事件谓词」把路径切成若干段，每段 =（非事件元素)* ++ [事件元素]（末段可纯非事件）。
--   ③ 的路径长界 = 段数（≤ 事件数 + 1）× 段长界。两种事件都用本件切分：
--     · 事件 =「dir = S 停驻步」（_q10-stepcount-design.md 的 M2：非吸收 S 步全为状态改变、
--       无自环 ⟹ S 步是流程停驻点，段内每步 L/R 推进）；
--     · 事件 =「im-true 读步」（= ntm2ForkCount 的 filter 谓词，SubsetSumInNP.lean:46）——
--       与 ② 的 m 同一定义（A1Progress §3 口径对齐要求）。
--   段长界（M4 段方向单调 + 位置域 [0,|x|]）在合龙时由 ①（PosBound1 a9ec5ed 的
--   a1_cbtm_accept_path_prefix_bound）经块级包络提供；本件只负责组合。
-- ==============================================================================

/-- 按事件谓词 P 切段：事件元素开启新段，非事件元素并入其后首个段（若其后无段则自成一段）。
    结果中每段形如（非事件)* ++ [事件]（末段可为纯非事件）。 -/
def segsByEvent {α : Type} (P : α → Bool) : List α → List (List α)
  | [] => []
  | a :: l =>
      match P a with
      | true => [a] :: segsByEvent P l
      | false =>
          match segsByEvent P l with
          | [] => [[a]]
          | s :: rest => (a :: s) :: rest

/-- 单步展开（true 支）。 -/
lemma segsByEvent_cons_true {α : Type} (P : α → Bool) (a : α) (l : List α)
    (h : P a = true) : segsByEvent P (a :: l) = [a] :: segsByEvent P l := by
  simp only [segsByEvent, h]

/-- 单步展开（false 支，后段为空）。 -/
lemma segsByEvent_cons_false_nil {α : Type} (P : α → Bool) (a : α) (l : List α)
    (h : P a = false) (hseg : segsByEvent P l = []) :
    segsByEvent P (a :: l) = [[a]] := by
  simp only [segsByEvent, h, hseg]

/-- 单步展开（false 支，后段非空）。 -/
lemma segsByEvent_cons_false_cons {α : Type} (P : α → Bool) (a : α) (l : List α)
    (s : List α) (rest : List (List α)) (h : P a = false)
    (hseg : segsByEvent P l = s :: rest) :
    segsByEvent P (a :: l) = (a :: s) :: rest := by
  simp only [segsByEvent, h, hseg]

/-- 切段不丢元素：拍平 = 原表。 -/
lemma segsByEvent_flatten {α : Type} (P : α → Bool) (l : List α) :
    (segsByEvent P l).flatten = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      cases hP : P a with
      | true =>
          rw [segsByEvent_cons_true P a l hP, List.flatten_cons, ih]
          rfl
      | false =>
          cases hseg : segsByEvent P l with
          | nil =>
              have hl : l = [] := by
                have hfl := ih
                rw [hseg] at hfl
                simpa using hfl.symm
              subst hl
              rw [segsByEvent_cons_false_nil P a [] hP rfl]
              rfl
          | cons s rest =>
              have hflat : ((s :: rest) : List (List α)).flatten = l := by
                have h' := ih
                rw [hseg] at h'
                exact h'
              rw [segsByEvent_cons_false_cons P a l s rest hP hseg, List.flatten_cons,
                List.cons_append, ← List.flatten_cons, hflat]

/-- 段数 ≤ 事件数 + 1（事件数 = filter 长度）。 -/
lemma segsByEvent_length_le {α : Type} (P : α → Bool) (l : List α) :
    (segsByEvent P l).length ≤ (l.filter P).length + 1 := by
  induction l with
  | nil => simp [segsByEvent]
  | cons a l ih =>
      cases hP : P a with
      | true =>
          rw [segsByEvent_cons_true P a l hP, List.length_cons]
          have hfilter : ((a :: l).filter P).length = (l.filter P).length + 1 := by
            simp [hP]
          rw [hfilter]
          omega
      | false =>
          have hfilter : ((a :: l).filter P).length = (l.filter P).length := by
            simp [hP]
          cases hseg : segsByEvent P l with
          | nil =>
              have hl : l = [] := by
                have hfl := segsByEvent_flatten P l
                rw [hseg] at hfl
                simpa using hfl.symm
              subst hl
              rw [segsByEvent_cons_false_nil P a [] hP rfl, List.length_cons, List.length_nil,
                hfilter]
              simp
          | cons s rest =>
              have ih' : rest.length + 1 ≤ (l.filter P).length + 1 := by
                have h' := ih
                rw [hseg, List.length_cons] at h'
                exact h'
              rw [segsByEvent_cons_false_cons P a l s rest hP hseg, List.length_cons, hfilter]
              omega

/-- 逐项界 ⟹ 和的界（ℕ 版）。 -/
lemma sum_le_length_mul {L : List ℕ} {c : ℕ} (h : ∀ x ∈ L, x ≤ c) :
    L.sum ≤ L.length * c := by
  induction L with
  | nil => simp
  | cons a rest ih =>
      have ha : a ≤ c := h a (by simp)
      have hr : rest.sum ≤ rest.length * c := ih (fun x hx => h x (by simp [hx]))
      rw [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- **C3 通用组装件**：若切出的每段长 ≤ c，则原路径长 ≤（事件数 + 1）· c。
    （③ 的目标形态：事件 = im-true 读步时，(事件数 + 1) 即 (m + 1)。） -/
theorem length_le_filter_mul_of_segs {α : Type} (P : α → Bool) (c : ℕ) (l : List α)
    (hseg : ∀ s ∈ segsByEvent P l, s.length ≤ c) :
    l.length ≤ ((l.filter P).length + 1) * c := by
  have h1 : l.length = (segsByEvent P l).flatten.length := by
    rw [segsByEvent_flatten]
  rw [h1, List.length_flatten]
  have h2 : ((segsByEvent P l).map List.length).sum ≤ (segsByEvent P l).length * c := by
    calc ((segsByEvent P l).map List.length).sum
        ≤ ((segsByEvent P l).map List.length).length * c := by
          apply sum_le_length_mul
          intro x hx
          rcases List.mem_map.mp hx with ⟨s, hs, rfl⟩
          exact hseg s hs
      _ = (segsByEvent P l).length * c := by rw [List.length_map]
  exact le_trans h2 (Nat.mul_le_mul_right c (segsByEvent_length_le P l))


-- ==============================================================================
-- C3 接口（钉死 ③ 的组装形状）：两种事件谓词的轮级组装。
--   · symRoundHead    ：主循环轮首（fromState = 4）—— 轮段 = 一次主循环迭代；
--   · symIsMarkedRead ：标记读步（readSym 的标记位 = true）—— 与 ② 的 filter 谓词
--                       同源（SubsetSumInNP.lean:46 ntm2ForkCount）。
--   配合 M3（轮首数/标记读数 ≤ K·(m+1)·(|x|+1)）与 M4（轮段 ≤ |x|+1），
--   即得 ③ 的路径长界 π.length ≤ K·(m+1)·(|x|+1)²（K 吸收常数）。
-- ==============================================================================

/-- 事件谓词：主循环轮首（fromState = 4 的步）。Core 表中状态 4 = 减法阶段入口，
    每轮恰有一个 fromState = 4 的步。 -/
def symRoundHead (step : SymStep) : Bool := decide (step.fromState = 4)

/-- 事件谓词：标记读步（readSym 标记位 = true）。 -/
def symIsMarkedRead (step : SymStep) : Bool := step.readSym.2

/-- ③ 轮级组装（轮首切分）：若每个轮段步数 ≤ C，则 π.length ≤ (轮首数 + 1) · C。 -/
theorem symSteps_length_le_of_rounds {π : List SymStep} {C : ℕ}
    (h : ∀ s ∈ segsByEvent symRoundHead π, s.length ≤ C) :
    π.length ≤ ((π.filter symRoundHead).length + 1) * C :=
  length_le_filter_mul_of_segs symRoundHead C π h

/-- ③ 轮级组装（标记读切分）：若相邻标记读之间的步数 ≤ C，
    则 π.length ≤ (标记读数 + 1) · C（标记读数 = ② 的 m）。 -/
theorem symSteps_length_le_of_markedReads {π : List SymStep} {C : ℕ}
    (h : ∀ s ∈ segsByEvent symIsMarkedRead π, s.length ≤ C) :
    π.length ≤ ((π.filter symIsMarkedRead).length + 1) * C :=
  length_le_filter_mul_of_segs symIsMarkedRead C π h

-- ==============================================================================
-- C3/M4 相表事实（路线 (b) 原型，2026-09-10）：表级「方向唯一」事实。
--   · 全部由 `cases SymKind/Bool` + `simp_all [VerifierSym.transition]` 展开获得 ⟹ **不引新公理**
--     （区别于 native_decide/decide 路线）。
--   · 形式：`r ∈ VerifierSym.transition (q, (k, im)) → r.nextState ≠ 101 → r.moveDir = d`；
--     前提 `nextState ≠ 101` 由 C1（可延拓路径无陷阱）在路径层提供。
--   · 待补全族：相态 4/5/76/8/9/77/10/12/11/14/81/13/84/85/86/87/20/21/51/22/23 的方向表
--     （相内方向单调 ⟹ 相长 ≤ 位置振幅 + O(1)，位置振幅用 ① A-1 的域）。
-- ==============================================================================

/-- 状态 81（回程相）：已列举读符号下方向恒 R。 -/
theorem transition_81_dir (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (81, (k, im))) (hne : r.nextState ≠ 101) : r.moveDir = Dir.R := by
  have hmem : (81 : ℕ) ∈ VerifierSym.legalStates := by decide
  cases k <;> cases im <;> simp_all [VerifierSym.transition, hmem]

/-- 状态 87（清理相右扫）：数据位/已清位自环 R；跨 #₀ 停驻（S，转 20）。
    —— 证据修正：方向事实必须按 (态, 读符号) 记录；「相结束步」是 S 步，
    这正是 M4 的切段点（段内方向由 (态,读符号) 表决定，段末必 S）。 -/
theorem transition_87_dir (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (87, (k, im))) (hne : r.nextState ≠ 101) :
    r.moveDir = Dir.R ∨ (r.moveDir = Dir.S ∧ r.nextState = 20) := by
  have hmem : (87 : ℕ) ∈ VerifierSym.legalStates := by decide
  cases k <;> cases im <;> simp_all [VerifierSym.transition, hmem]

-- >>> M4A-BLOCK-BEGIN（自动生成：逐格行等式 + 每状态方向表；内核判定，不引公理）

/-- [M4a] 状态 0 的方向表：非陷阱步方向 ∈ {R}。 -/
theorem transition_0_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (0, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.R) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (0, (SymKind.data0, true)) =
            ({⟨101, (SymKind.data0, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (0, (SymKind.data0, false)) =
            ({⟨101, (SymKind.data0, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (0, (SymKind.data1, true)) =
            ({⟨101, (SymKind.data1, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (0, (SymKind.data1, false)) =
            ({⟨101, (SymKind.data1, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (0, (SymKind.consumed, true)) =
            ({⟨101, (SymKind.consumed, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (0, (SymKind.consumed, false)) =
            ({⟨101, (SymKind.consumed, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (0, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (0, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (0, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (0, (SymKind.sel, false)) =
            ({⟨101, (SymKind.sel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (0, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (0, (SymKind.nosel, false)) =
            ({⟨101, (SymKind.nosel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (0, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (0, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (0, (SymKind.boundary, true)) =
            ({⟨1, (SymKind.boundary, true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (0, (SymKind.boundary, false)) =
            ({⟨1, (SymKind.boundary, false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)


/-- [M4a] 状态 1 的方向表：非陷阱步方向 ∈ {R}。 -/
theorem transition_1_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (1, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.R) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (1, (SymKind.data0, true)) =
            ({⟨1, (SymKind.data0, true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (1, (SymKind.data0, false)) =
            ({⟨1, (SymKind.data0, false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (1, (SymKind.data1, true)) =
            ({⟨1, (SymKind.data1, true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (1, (SymKind.data1, false)) =
            ({⟨1, (SymKind.data1, false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (1, (SymKind.consumed, true)) =
            ({⟨101, (SymKind.consumed, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (1, (SymKind.consumed, false)) =
            ({⟨101, (SymKind.consumed, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (1, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (1, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (1, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (1, (SymKind.sel, false)) =
            ({⟨101, (SymKind.sel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (1, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (1, (SymKind.nosel, false)) =
            ({⟨101, (SymKind.nosel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (1, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (1, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (1, (SymKind.boundary, true)) =
            ({⟨2, (SymKind.boundary, true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (1, (SymKind.boundary, false)) =
            ({⟨2, (SymKind.boundary, false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)


/-- [M4a] 状态 2 的方向表：非陷阱步方向 ∈ {R, S}；S 后继 ∈ {3}。 -/
theorem transition_2_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (2, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.R ∨ r.moveDir = Dir.S) ∧ (r.moveDir = Dir.S → r.nextState ∈ ({3} : Finset ℕ)) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (2, (SymKind.data0, true)) =
            ({⟨2, (SymKind.data0, true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inl rfl, fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (2, (SymKind.data0, false)) =
            ({⟨2, (SymKind.data0, false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inl rfl, fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (2, (SymKind.data1, true)) =
            ({⟨2, (SymKind.data1, true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inl rfl, fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (2, (SymKind.data1, false)) =
            ({⟨2, (SymKind.data1, false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inl rfl, fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (2, (SymKind.consumed, true)) =
            ({⟨101, (SymKind.consumed, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (2, (SymKind.consumed, false)) =
            ({⟨101, (SymKind.consumed, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (2, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (2, (SymKind.alpha, false)) =
            ({⟨2, Sym.sel, Dir.R⟩, ⟨2, Sym.nosel, Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         rcases hr with hr | hr
         · subst hr
           exact ⟨Or.inl rfl, fun hd => by cases hd⟩
         · subst hr
           exact ⟨Or.inl rfl, fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (2, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (2, (SymKind.sel, false)) =
            ({⟨101, (SymKind.sel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (2, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (2, (SymKind.nosel, false)) =
            ({⟨101, (SymKind.nosel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (2, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (2, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (2, (SymKind.boundary, true)) =
            ({⟨3, (SymKind.boundary, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inr (rfl), fun hd => by decide⟩)
      | (have h : VerifierSym.transition (2, (SymKind.boundary, false)) =
            ({⟨3, (SymKind.boundary, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inr (rfl), fun hd => by decide⟩)


/-- [M4a] 状态 3 的方向表：非陷阱步方向 ∈ {L}。 -/
theorem transition_3_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (3, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.L) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (3, (SymKind.data0, true)) =
            ({⟨101, (SymKind.data0, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (3, (SymKind.data0, false)) =
            ({⟨101, (SymKind.data0, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (3, (SymKind.data1, true)) =
            ({⟨101, (SymKind.data1, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (3, (SymKind.data1, false)) =
            ({⟨101, (SymKind.data1, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (3, (SymKind.consumed, true)) =
            ({⟨101, (SymKind.consumed, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (3, (SymKind.consumed, false)) =
            ({⟨101, (SymKind.consumed, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (3, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (3, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (3, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (3, (SymKind.sel, false)) =
            ({⟨101, (SymKind.sel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (3, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (3, (SymKind.nosel, false)) =
            ({⟨101, (SymKind.nosel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (3, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (3, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (3, (SymKind.boundary, true)) =
            ({⟨101, (SymKind.boundary, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (3, (SymKind.boundary, false)) =
            ({⟨24, (Sym.mk SymKind.boundary true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)


/-- [M4a] 状态 4 的方向表：非陷阱步方向 ∈ {L, R}。 -/
theorem transition_4_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (4, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.L ∨ r.moveDir = Dir.R) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (4, (SymKind.data0, true)) =
            ({⟨101, (SymKind.data0, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (4, (SymKind.data0, false)) =
            ({⟨101, (SymKind.data0, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (4, (SymKind.data1, true)) =
            ({⟨101, (SymKind.data1, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (4, (SymKind.data1, false)) =
            ({⟨101, (SymKind.data1, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (4, (SymKind.consumed, true)) =
            ({⟨101, (SymKind.consumed, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (4, (SymKind.consumed, false)) =
            ({⟨101, (SymKind.consumed, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (4, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (4, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (4, (SymKind.sel, true)) =
            ({⟨5, Sym.data0, Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inr (rfl))
      | (have h : VerifierSym.transition (4, (SymKind.sel, false)) =
            ({⟨5, Sym.data0, Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inr (rfl))
      | (have h : VerifierSym.transition (4, (SymKind.nosel, true)) =
            ({⟨20, Sym.data0, Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inl rfl)
      | (have h : VerifierSym.transition (4, (SymKind.nosel, false)) =
            ({⟨20, Sym.data0, Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inl rfl)
      | (have h : VerifierSym.transition (4, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (4, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (4, (SymKind.boundary, true)) =
            ({⟨101, (SymKind.boundary, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (4, (SymKind.boundary, false)) =
            ({⟨101, (SymKind.boundary, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)


/-- [M4a] 状态 5 的方向表：非陷阱步方向 ∈ {L}。 -/
theorem transition_5_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (5, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.L) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (5, (SymKind.data0, true)) =
            ({⟨8, Sym.consumed, Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (5, (SymKind.data0, false)) =
            ({⟨8, Sym.consumed, Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (5, (SymKind.data1, true)) =
            ({⟨76, Sym.consumed, Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (5, (SymKind.data1, false)) =
            ({⟨76, Sym.consumed, Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (5, (SymKind.consumed, true)) =
            ({⟨101, (SymKind.consumed, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (5, (SymKind.consumed, false)) =
            ({⟨101, (SymKind.consumed, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (5, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (5, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (5, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (5, (SymKind.sel, false)) =
            ({⟨101, (SymKind.sel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (5, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (5, (SymKind.nosel, false)) =
            ({⟨101, (SymKind.nosel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (5, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (5, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (5, (SymKind.boundary, true)) =
            ({⟨101, (SymKind.boundary, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (5, (SymKind.boundary, false)) =
            ({⟨101, (SymKind.boundary, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)


/-- [M4a] 状态 8 的方向表：非陷阱步方向 ∈ {L}。 -/
theorem transition_8_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (8, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.L) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (8, (SymKind.data0, true)) =
            ({⟨8, (SymKind.data0, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (8, (SymKind.data0, false)) =
            ({⟨8, (SymKind.data0, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (8, (SymKind.data1, true)) =
            ({⟨8, (SymKind.data1, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (8, (SymKind.data1, false)) =
            ({⟨8, (SymKind.data1, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (8, (SymKind.consumed, true)) =
            ({⟨8, (SymKind.consumed, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (8, (SymKind.consumed, false)) =
            ({⟨8, (SymKind.consumed, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (8, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (8, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (8, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (8, (SymKind.sel, false)) =
            ({⟨101, (SymKind.sel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (8, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (8, (SymKind.nosel, false)) =
            ({⟨101, (SymKind.nosel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (8, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (8, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (8, (SymKind.boundary, true)) =
            ({⟨9, (SymKind.boundary, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (8, (SymKind.boundary, false)) =
            ({⟨9, (SymKind.boundary, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)


/-- [M4a] 状态 9 的方向表：非陷阱步方向 ∈ {L, R}。 -/
theorem transition_9_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (9, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.L ∨ r.moveDir = Dir.R) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (9, (SymKind.data0, true)) =
            ({⟨9, (SymKind.data0, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inl rfl)
      | (have h : VerifierSym.transition (9, (SymKind.data0, false)) =
            ({⟨9, (SymKind.data0, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inl rfl)
      | (have h : VerifierSym.transition (9, (SymKind.data1, true)) =
            ({⟨9, (SymKind.data1, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inl rfl)
      | (have h : VerifierSym.transition (9, (SymKind.data1, false)) =
            ({⟨9, (SymKind.data1, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inl rfl)
      | (have h : VerifierSym.transition (9, (SymKind.consumed, true)) =
            ({⟨101, (SymKind.consumed, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (9, (SymKind.consumed, false)) =
            ({⟨101, (SymKind.consumed, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (9, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (9, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (9, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (9, (SymKind.sel, false)) =
            ({⟨101, (SymKind.sel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (9, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (9, (SymKind.nosel, false)) =
            ({⟨101, (SymKind.nosel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (9, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (9, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (9, (SymKind.boundary, true)) =
            ({⟨12, (SymKind.boundary, true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inr (rfl))
      | (have h : VerifierSym.transition (9, (SymKind.boundary, false)) =
            ({⟨12, (SymKind.boundary, false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inr (rfl))


/-- [M4a] 状态 10 的方向表：非陷阱步方向 ∈ {R, S}；S 后继 ∈ {11}。 -/
theorem transition_10_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (10, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.R ∨ r.moveDir = Dir.S) ∧ (r.moveDir = Dir.S → r.nextState ∈ ({11} : Finset ℕ)) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (10, (SymKind.data0, true)) =
            ({⟨10, (Sym.data0 true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inl rfl, fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (10, (SymKind.data0, false)) =
            ({⟨11, (Sym.data0 true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inr (rfl), fun hd => by decide⟩)
      | (have h : VerifierSym.transition (10, (SymKind.data1, true)) =
            ({⟨10, (Sym.data1 true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inl rfl, fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (10, (SymKind.data1, false)) =
            ({⟨11, (Sym.data1 true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inr (rfl), fun hd => by decide⟩)
      | (have h : VerifierSym.transition (10, (SymKind.consumed, true)) =
            ({⟨101, (SymKind.consumed, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (10, (SymKind.consumed, false)) =
            ({⟨101, (SymKind.consumed, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (10, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (10, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (10, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (10, (SymKind.sel, false)) =
            ({⟨101, (SymKind.sel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (10, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (10, (SymKind.nosel, false)) =
            ({⟨101, (SymKind.nosel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (10, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (10, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (10, (SymKind.boundary, true)) =
            ({⟨101, (SymKind.boundary, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (10, (SymKind.boundary, false)) =
            ({⟨101, (SymKind.boundary, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)


/-- [M4a] 状态 11 的方向表：非陷阱步方向 ∈ {R}。 -/
theorem transition_11_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (11, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.R) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (11, (SymKind.data0, true)) =
            ({⟨14, (Sym.data1 true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (11, (SymKind.data0, false)) =
            ({⟨14, (Sym.data1 false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (11, (SymKind.data1, true)) =
            ({⟨81, (Sym.data0 true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (11, (SymKind.data1, false)) =
            ({⟨81, (Sym.data0 false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (11, (SymKind.consumed, true)) =
            ({⟨101, (SymKind.consumed, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (11, (SymKind.consumed, false)) =
            ({⟨101, (SymKind.consumed, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (11, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (11, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (11, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (11, (SymKind.sel, false)) =
            ({⟨101, (SymKind.sel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (11, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (11, (SymKind.nosel, false)) =
            ({⟨101, (SymKind.nosel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (11, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (11, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (11, (SymKind.boundary, true)) =
            ({⟨101, (SymKind.boundary, true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (11, (SymKind.boundary, false)) =
            ({⟨101, (SymKind.boundary, false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)


/-- [M4a] 状态 12 的方向表：非陷阱步方向 ∈ {R}。 -/
theorem transition_12_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (12, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.R) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (12, (SymKind.data0, true)) =
            ({⟨12, (Sym.data0 true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (12, (SymKind.data0, false)) =
            ({⟨81, (Sym.data0 true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (12, (SymKind.data1, true)) =
            ({⟨12, (Sym.data1 true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (12, (SymKind.data1, false)) =
            ({⟨81, (Sym.data1 true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (12, (SymKind.consumed, true)) =
            ({⟨101, (SymKind.consumed, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (12, (SymKind.consumed, false)) =
            ({⟨101, (SymKind.consumed, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (12, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (12, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (12, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (12, (SymKind.sel, false)) =
            ({⟨101, (SymKind.sel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (12, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (12, (SymKind.nosel, false)) =
            ({⟨101, (SymKind.nosel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (12, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (12, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (12, (SymKind.boundary, true)) =
            ({⟨101, (SymKind.boundary, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (12, (SymKind.boundary, false)) =
            ({⟨101, (SymKind.boundary, false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)


/-- [M4a] 状态 13 的方向表：非陷阱步方向 ∈ {L, R, S}；S 后继 ∈ {5}。 -/
theorem transition_13_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (13, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.L ∨ r.moveDir = Dir.R ∨ r.moveDir = Dir.S) ∧ (r.moveDir = Dir.S → r.nextState ∈ ({5} : Finset ℕ)) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (13, (SymKind.data0, true)) =
            ({⟨5, (SymKind.data0, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inr (Or.inr (rfl)), fun hd => by decide⟩)
      | (have h : VerifierSym.transition (13, (SymKind.data0, false)) =
            ({⟨5, (SymKind.data0, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inr (Or.inr (rfl)), fun hd => by decide⟩)
      | (have h : VerifierSym.transition (13, (SymKind.data1, true)) =
            ({⟨5, (SymKind.data1, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inr (Or.inr (rfl)), fun hd => by decide⟩)
      | (have h : VerifierSym.transition (13, (SymKind.data1, false)) =
            ({⟨5, (SymKind.data1, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inr (Or.inr (rfl)), fun hd => by decide⟩)
      | (have h : VerifierSym.transition (13, (SymKind.consumed, true)) =
            ({⟨13, Sym.consumed, Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inr (Or.inl rfl), fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (13, (SymKind.consumed, false)) =
            ({⟨13, Sym.consumed, Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inr (Or.inl rfl), fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (13, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (13, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (13, (SymKind.sel, true)) =
            ({⟨84, (SymKind.sel, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inl rfl, fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (13, (SymKind.sel, false)) =
            ({⟨84, (SymKind.sel, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inl rfl, fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (13, (SymKind.nosel, true)) =
            ({⟨84, (SymKind.nosel, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inl rfl, fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (13, (SymKind.nosel, false)) =
            ({⟨84, (SymKind.nosel, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inl rfl, fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (13, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (13, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (13, (SymKind.boundary, true)) =
            ({⟨84, (SymKind.boundary, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inl rfl, fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (13, (SymKind.boundary, false)) =
            ({⟨84, (SymKind.boundary, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inl rfl, fun hd => by cases hd⟩)


/-- [M4a] 状态 14 的方向表：非陷阱步方向 ∈ {R}。 -/
theorem transition_14_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (14, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.R) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (14, (SymKind.data0, true)) =
            ({⟨14, (Sym.data1 true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (14, (SymKind.data0, false)) =
            ({⟨14, (Sym.data1 false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (14, (SymKind.data1, true)) =
            ({⟨81, (Sym.data0 true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (14, (SymKind.data1, false)) =
            ({⟨81, (Sym.data0 false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (14, (SymKind.consumed, true)) =
            ({⟨101, (SymKind.consumed, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (14, (SymKind.consumed, false)) =
            ({⟨101, (SymKind.consumed, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (14, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (14, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (14, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (14, (SymKind.sel, false)) =
            ({⟨101, (SymKind.sel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (14, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (14, (SymKind.nosel, false)) =
            ({⟨101, (SymKind.nosel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (14, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (14, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (14, (SymKind.boundary, true)) =
            ({⟨101, (SymKind.boundary, true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (14, (SymKind.boundary, false)) =
            ({⟨101, (SymKind.boundary, false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)


/-- [M4a] 状态 20 的方向表：非陷阱步方向 ∈ {R}。 -/
theorem transition_20_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (20, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.R) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (20, (SymKind.data0, true)) =
            ({⟨101, (SymKind.data0, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (20, (SymKind.data0, false)) =
            ({⟨101, (SymKind.data0, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (20, (SymKind.data1, true)) =
            ({⟨101, (SymKind.data1, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (20, (SymKind.data1, false)) =
            ({⟨101, (SymKind.data1, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (20, (SymKind.consumed, true)) =
            ({⟨101, (SymKind.consumed, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (20, (SymKind.consumed, false)) =
            ({⟨101, (SymKind.consumed, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (20, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (20, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (20, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (20, (SymKind.sel, false)) =
            ({⟨101, (SymKind.sel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (20, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (20, (SymKind.nosel, false)) =
            ({⟨101, (SymKind.nosel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (20, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (20, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (20, (SymKind.boundary, true)) =
            ({⟨21, Sym.data0, Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (20, (SymKind.boundary, false)) =
            ({⟨21, Sym.data0, Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)


/-- [M4a] 状态 21 的方向表：非陷阱步方向 ∈ {L, R, S}；S 后继 ∈ {22}。 -/
theorem transition_21_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (21, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.L ∨ r.moveDir = Dir.R ∨ r.moveDir = Dir.S) ∧ (r.moveDir = Dir.S → r.nextState ∈ ({22} : Finset ℕ)) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (21, (SymKind.data0, true)) =
            ({⟨21, Sym.data0, Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inr (Or.inl rfl), fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (21, (SymKind.data0, false)) =
            ({⟨21, Sym.data0, Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inr (Or.inl rfl), fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (21, (SymKind.data1, true)) =
            ({⟨21, Sym.data0, Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inr (Or.inl rfl), fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (21, (SymKind.data1, false)) =
            ({⟨21, Sym.data0, Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inr (Or.inl rfl), fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (21, (SymKind.consumed, true)) =
            ({⟨21, Sym.data0, Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inr (Or.inl rfl), fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (21, (SymKind.consumed, false)) =
            ({⟨21, Sym.data0, Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inr (Or.inl rfl), fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (21, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (21, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (21, (SymKind.sel, true)) =
            ({⟨51, (SymKind.sel, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inl rfl, fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (21, (SymKind.sel, false)) =
            ({⟨51, (SymKind.sel, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inl rfl, fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (21, (SymKind.nosel, true)) =
            ({⟨51, (SymKind.nosel, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inl rfl, fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (21, (SymKind.nosel, false)) =
            ({⟨51, (SymKind.nosel, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inl rfl, fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (21, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (21, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (21, (SymKind.boundary, true)) =
            ({⟨22, (SymKind.boundary, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inr (Or.inr (rfl)), fun hd => by decide⟩)
      | (have h : VerifierSym.transition (21, (SymKind.boundary, false)) =
            ({⟨22, (SymKind.boundary, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inr (Or.inr (rfl)), fun hd => by decide⟩)


/-- [M4a] 状态 22 的方向表：非陷阱步方向 ∈ {L}。 -/
theorem transition_22_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (22, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.L) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (22, (SymKind.data0, true)) =
            ({⟨101, (SymKind.data0, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (22, (SymKind.data0, false)) =
            ({⟨101, (SymKind.data0, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (22, (SymKind.data1, true)) =
            ({⟨101, (SymKind.data1, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (22, (SymKind.data1, false)) =
            ({⟨101, (SymKind.data1, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (22, (SymKind.consumed, true)) =
            ({⟨101, (SymKind.consumed, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (22, (SymKind.consumed, false)) =
            ({⟨101, (SymKind.consumed, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (22, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (22, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (22, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (22, (SymKind.sel, false)) =
            ({⟨101, (SymKind.sel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (22, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (22, (SymKind.nosel, false)) =
            ({⟨101, (SymKind.nosel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (22, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (22, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (22, (SymKind.boundary, true)) =
            ({⟨23, (SymKind.boundary, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (22, (SymKind.boundary, false)) =
            ({⟨101, (SymKind.boundary, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)


/-- [M4a] 状态 23 的方向表：非陷阱步方向 ∈ {L, R}。 -/
theorem transition_23_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (23, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.L ∨ r.moveDir = Dir.R) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (23, (SymKind.data0, true)) =
            ({⟨23, (SymKind.data0, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inl rfl)
      | (have h : VerifierSym.transition (23, (SymKind.data0, false)) =
            ({⟨23, (SymKind.data0, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inl rfl)
      | (have h : VerifierSym.transition (23, (SymKind.data1, true)) =
            ({⟨101, (SymKind.data1, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (23, (SymKind.data1, false)) =
            ({⟨101, (SymKind.data1, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (23, (SymKind.consumed, true)) =
            ({⟨101, (SymKind.consumed, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (23, (SymKind.consumed, false)) =
            ({⟨101, (SymKind.consumed, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (23, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (23, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (23, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (23, (SymKind.sel, false)) =
            ({⟨101, (SymKind.sel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (23, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (23, (SymKind.nosel, false)) =
            ({⟨101, (SymKind.nosel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (23, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (23, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (23, (SymKind.boundary, true)) =
            ({⟨100, (SymKind.boundary, true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inr (rfl))
      | (have h : VerifierSym.transition (23, (SymKind.boundary, false)) =
            ({⟨100, (SymKind.boundary, false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inr (rfl))


/-- [M4a] 状态 24 的方向表：非陷阱步方向 ∈ {L}。 -/
theorem transition_24_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (24, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.L) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (24, (SymKind.data0, true)) =
            ({⟨101, (SymKind.data0, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (24, (SymKind.data0, false)) =
            ({⟨101, (SymKind.data0, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (24, (SymKind.data1, true)) =
            ({⟨101, (SymKind.data1, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (24, (SymKind.data1, false)) =
            ({⟨29, (SymKind.data1, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (24, (SymKind.consumed, true)) =
            ({⟨101, (SymKind.consumed, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (24, (SymKind.consumed, false)) =
            ({⟨101, (SymKind.consumed, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (24, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (24, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (24, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (24, (SymKind.sel, false)) =
            ({⟨101, (SymKind.sel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (24, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (24, (SymKind.nosel, false)) =
            ({⟨101, (SymKind.nosel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (24, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (24, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (24, (SymKind.boundary, true)) =
            ({⟨101, (SymKind.boundary, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (24, (SymKind.boundary, false)) =
            ({⟨101, (SymKind.boundary, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)


/-- [M4a] 状态 26 的方向表：非陷阱步方向 ∈ {L}。 -/
theorem transition_26_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (26, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.L) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (26, (SymKind.data0, true)) =
            ({⟨101, (SymKind.data0, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (26, (SymKind.data0, false)) =
            ({⟨101, (SymKind.data0, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (26, (SymKind.data1, true)) =
            ({⟨101, (SymKind.data1, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (26, (SymKind.data1, false)) =
            ({⟨29, (SymKind.data1, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (26, (SymKind.consumed, true)) =
            ({⟨101, (SymKind.consumed, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (26, (SymKind.consumed, false)) =
            ({⟨101, (SymKind.consumed, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (26, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (26, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (26, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (26, (SymKind.sel, false)) =
            ({⟨101, (SymKind.sel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (26, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (26, (SymKind.nosel, false)) =
            ({⟨101, (SymKind.nosel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (26, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (26, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (26, (SymKind.boundary, true)) =
            ({⟨101, (SymKind.boundary, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (26, (SymKind.boundary, false)) =
            ({⟨27, (SymKind.boundary, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)


/-- [M4a] 状态 27 的方向表：非陷阱步方向 ∈ {L}。 -/
theorem transition_27_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (27, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.L) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (27, (SymKind.data0, true)) =
            ({⟨101, (SymKind.data0, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (27, (SymKind.data0, false)) =
            ({⟨101, (SymKind.data0, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (27, (SymKind.data1, true)) =
            ({⟨101, (SymKind.data1, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (27, (SymKind.data1, false)) =
            ({⟨38, (SymKind.data1, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (27, (SymKind.consumed, true)) =
            ({⟨101, (SymKind.consumed, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (27, (SymKind.consumed, false)) =
            ({⟨101, (SymKind.consumed, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (27, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (27, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (27, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (27, (SymKind.sel, false)) =
            ({⟨101, (SymKind.sel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (27, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (27, (SymKind.nosel, false)) =
            ({⟨101, (SymKind.nosel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (27, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (27, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (27, (SymKind.boundary, true)) =
            ({⟨101, (SymKind.boundary, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (27, (SymKind.boundary, false)) =
            ({⟨101, (SymKind.boundary, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)


/-- [M4a] 状态 28 的方向表：非陷阱步方向 ∈ {R}。 -/
theorem transition_28_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (28, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.R) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (28, (SymKind.data0, true)) =
            ({⟨28, (SymKind.data0, true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (28, (SymKind.data0, false)) =
            ({⟨28, (SymKind.data0, false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (28, (SymKind.data1, true)) =
            ({⟨28, (SymKind.data1, true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (28, (SymKind.data1, false)) =
            ({⟨28, (SymKind.data1, false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (28, (SymKind.consumed, true)) =
            ({⟨101, (SymKind.consumed, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (28, (SymKind.consumed, false)) =
            ({⟨101, (SymKind.consumed, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (28, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (28, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (28, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (28, (SymKind.sel, false)) =
            ({⟨101, (SymKind.sel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (28, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (28, (SymKind.nosel, false)) =
            ({⟨101, (SymKind.nosel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (28, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (28, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (28, (SymKind.boundary, true)) =
            ({⟨4, (SymKind.boundary, true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (28, (SymKind.boundary, false)) =
            ({⟨4, (SymKind.boundary, false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)


/-- [M4a] 状态 29 的方向表：非陷阱步方向 ∈ {L}。 -/
theorem transition_29_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (29, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.L) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (29, (SymKind.data0, true)) =
            ({⟨101, (SymKind.data0, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (29, (SymKind.data0, false)) =
            ({⟨29, (SymKind.data0, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (29, (SymKind.data1, true)) =
            ({⟨101, (SymKind.data1, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (29, (SymKind.data1, false)) =
            ({⟨29, (SymKind.data1, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (29, (SymKind.consumed, true)) =
            ({⟨101, (SymKind.consumed, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (29, (SymKind.consumed, false)) =
            ({⟨101, (SymKind.consumed, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (29, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (29, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (29, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (29, (SymKind.sel, false)) =
            ({⟨26, (SymKind.sel, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (29, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (29, (SymKind.nosel, false)) =
            ({⟨26, (SymKind.nosel, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (29, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (29, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (29, (SymKind.boundary, true)) =
            ({⟨101, (SymKind.boundary, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (29, (SymKind.boundary, false)) =
            ({⟨101, (SymKind.boundary, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)


/-- [M4a] 状态 38 的方向表：非陷阱步方向 ∈ {L, R}。 -/
theorem transition_38_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (38, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.L ∨ r.moveDir = Dir.R) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (38, (SymKind.data0, true)) =
            ({⟨101, (SymKind.data0, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (38, (SymKind.data0, false)) =
            ({⟨38, (SymKind.data0, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inl rfl)
      | (have h : VerifierSym.transition (38, (SymKind.data1, true)) =
            ({⟨101, (SymKind.data1, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (38, (SymKind.data1, false)) =
            ({⟨38, (SymKind.data1, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inl rfl)
      | (have h : VerifierSym.transition (38, (SymKind.consumed, true)) =
            ({⟨101, (SymKind.consumed, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (38, (SymKind.consumed, false)) =
            ({⟨101, (SymKind.consumed, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (38, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (38, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (38, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (38, (SymKind.sel, false)) =
            ({⟨101, (SymKind.sel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (38, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (38, (SymKind.nosel, false)) =
            ({⟨101, (SymKind.nosel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (38, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (38, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (38, (SymKind.boundary, true)) =
            ({⟨101, (SymKind.boundary, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (38, (SymKind.boundary, false)) =
            ({⟨28, (SymKind.boundary, false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inr (rfl))


/-- [M4a] 状态 51 的方向表：非陷阱步方向 ∈ {R}。 -/
theorem transition_51_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (51, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.R) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (51, (SymKind.data0, true)) =
            ({⟨4, Sym.boundary, Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (51, (SymKind.data0, false)) =
            ({⟨4, Sym.boundary, Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (51, (SymKind.data1, true)) =
            ({⟨101, (SymKind.data1, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (51, (SymKind.data1, false)) =
            ({⟨101, (SymKind.data1, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (51, (SymKind.consumed, true)) =
            ({⟨101, (SymKind.consumed, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (51, (SymKind.consumed, false)) =
            ({⟨101, (SymKind.consumed, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (51, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (51, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (51, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (51, (SymKind.sel, false)) =
            ({⟨101, (SymKind.sel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (51, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (51, (SymKind.nosel, false)) =
            ({⟨101, (SymKind.nosel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (51, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (51, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (51, (SymKind.boundary, true)) =
            ({⟨101, (SymKind.boundary, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (51, (SymKind.boundary, false)) =
            ({⟨101, (SymKind.boundary, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)


/-- [M4a] 状态 76 的方向表：非陷阱步方向 ∈ {L}。 -/
theorem transition_76_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (76, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.L) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (76, (SymKind.data0, true)) =
            ({⟨76, (SymKind.data0, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (76, (SymKind.data0, false)) =
            ({⟨76, (SymKind.data0, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (76, (SymKind.data1, true)) =
            ({⟨76, (SymKind.data1, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (76, (SymKind.data1, false)) =
            ({⟨76, (SymKind.data1, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (76, (SymKind.consumed, true)) =
            ({⟨76, (SymKind.consumed, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (76, (SymKind.consumed, false)) =
            ({⟨76, (SymKind.consumed, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (76, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (76, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (76, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (76, (SymKind.sel, false)) =
            ({⟨101, (SymKind.sel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (76, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (76, (SymKind.nosel, false)) =
            ({⟨101, (SymKind.nosel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (76, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (76, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (76, (SymKind.boundary, true)) =
            ({⟨77, (SymKind.boundary, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (76, (SymKind.boundary, false)) =
            ({⟨77, (SymKind.boundary, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)


/-- [M4a] 状态 77 的方向表：非陷阱步方向 ∈ {L, R}。 -/
theorem transition_77_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (77, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.L ∨ r.moveDir = Dir.R) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (77, (SymKind.data0, true)) =
            ({⟨77, (SymKind.data0, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inl rfl)
      | (have h : VerifierSym.transition (77, (SymKind.data0, false)) =
            ({⟨77, (SymKind.data0, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inl rfl)
      | (have h : VerifierSym.transition (77, (SymKind.data1, true)) =
            ({⟨77, (SymKind.data1, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inl rfl)
      | (have h : VerifierSym.transition (77, (SymKind.data1, false)) =
            ({⟨77, (SymKind.data1, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inl rfl)
      | (have h : VerifierSym.transition (77, (SymKind.consumed, true)) =
            ({⟨101, (SymKind.consumed, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (77, (SymKind.consumed, false)) =
            ({⟨101, (SymKind.consumed, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (77, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (77, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (77, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (77, (SymKind.sel, false)) =
            ({⟨101, (SymKind.sel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (77, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (77, (SymKind.nosel, false)) =
            ({⟨101, (SymKind.nosel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (77, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (77, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (77, (SymKind.boundary, true)) =
            ({⟨10, (SymKind.boundary, true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inr (rfl))
      | (have h : VerifierSym.transition (77, (SymKind.boundary, false)) =
            ({⟨10, (SymKind.boundary, false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inr (rfl))


/-- [M4a] 状态 81 的方向表：非陷阱步方向 ∈ {R}。 -/
theorem transition_81_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (81, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.R) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (81, (SymKind.data0, true)) =
            ({⟨81, (SymKind.data0, true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (81, (SymKind.data0, false)) =
            ({⟨81, (SymKind.data0, false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (81, (SymKind.data1, true)) =
            ({⟨81, (SymKind.data1, true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (81, (SymKind.data1, false)) =
            ({⟨81, (SymKind.data1, false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (81, (SymKind.consumed, true)) =
            ({⟨13, Sym.consumed, Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (81, (SymKind.consumed, false)) =
            ({⟨13, Sym.consumed, Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (81, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (81, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (81, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (81, (SymKind.sel, false)) =
            ({⟨101, (SymKind.sel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (81, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (81, (SymKind.nosel, false)) =
            ({⟨101, (SymKind.nosel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (81, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (81, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (81, (SymKind.boundary, true)) =
            ({⟨81, (SymKind.boundary, true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (81, (SymKind.boundary, false)) =
            ({⟨81, (SymKind.boundary, false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)


/-- [M4a] 状态 84 的方向表：非陷阱步方向 ∈ {L}。 -/
theorem transition_84_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (84, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.L) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (84, (SymKind.data0, true)) =
            ({⟨84, (SymKind.data0, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (84, (SymKind.data0, false)) =
            ({⟨84, (SymKind.data0, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (84, (SymKind.data1, true)) =
            ({⟨84, (SymKind.data1, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (84, (SymKind.data1, false)) =
            ({⟨84, (SymKind.data1, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (84, (SymKind.consumed, true)) =
            ({⟨84, (SymKind.consumed, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (84, (SymKind.consumed, false)) =
            ({⟨84, (SymKind.consumed, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (84, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (84, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (84, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (84, (SymKind.sel, false)) =
            ({⟨101, (SymKind.sel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (84, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (84, (SymKind.nosel, false)) =
            ({⟨101, (SymKind.nosel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (84, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (84, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (84, (SymKind.boundary, true)) =
            ({⟨85, (SymKind.boundary, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)
      | (have h : VerifierSym.transition (84, (SymKind.boundary, false)) =
            ({⟨85, (SymKind.boundary, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact rfl)


/-- [M4a] 状态 85 的方向表：非陷阱步方向 ∈ {L, R}。 -/
theorem transition_85_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (85, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.L ∨ r.moveDir = Dir.R) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (85, (SymKind.data0, true)) =
            ({⟨85, (SymKind.data0, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inl rfl)
      | (have h : VerifierSym.transition (85, (SymKind.data0, false)) =
            ({⟨85, (SymKind.data0, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inl rfl)
      | (have h : VerifierSym.transition (85, (SymKind.data1, true)) =
            ({⟨85, (SymKind.data1, true), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inl rfl)
      | (have h : VerifierSym.transition (85, (SymKind.data1, false)) =
            ({⟨85, (SymKind.data1, false), Dir.L⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inl rfl)
      | (have h : VerifierSym.transition (85, (SymKind.consumed, true)) =
            ({⟨101, (SymKind.consumed, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (85, (SymKind.consumed, false)) =
            ({⟨101, (SymKind.consumed, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (85, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (85, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (85, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (85, (SymKind.sel, false)) =
            ({⟨101, (SymKind.sel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (85, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (85, (SymKind.nosel, false)) =
            ({⟨101, (SymKind.nosel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (85, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (85, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (85, (SymKind.boundary, true)) =
            ({⟨86, (SymKind.boundary, true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inr (rfl))
      | (have h : VerifierSym.transition (85, (SymKind.boundary, false)) =
            ({⟨86, (SymKind.boundary, false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact Or.inr (rfl))


/-- [M4a] 状态 86 的方向表：非陷阱步方向 ∈ {R, S}；S 后继 ∈ {87}。 -/
theorem transition_86_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (86, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.R ∨ r.moveDir = Dir.S) ∧ (r.moveDir = Dir.S → r.nextState ∈ ({87} : Finset ℕ)) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (86, (SymKind.data0, true)) =
            ({⟨86, (Sym.mk SymKind.data0 false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inl rfl, fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (86, (SymKind.data0, false)) =
            ({⟨87, (SymKind.data0, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inr (rfl), fun hd => by decide⟩)
      | (have h : VerifierSym.transition (86, (SymKind.data1, true)) =
            ({⟨86, (Sym.mk SymKind.data1 false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inl rfl, fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (86, (SymKind.data1, false)) =
            ({⟨87, (SymKind.data1, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inr (rfl), fun hd => by decide⟩)
      | (have h : VerifierSym.transition (86, (SymKind.consumed, true)) =
            ({⟨101, (SymKind.consumed, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (86, (SymKind.consumed, false)) =
            ({⟨101, (SymKind.consumed, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (86, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (86, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (86, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (86, (SymKind.sel, false)) =
            ({⟨101, (SymKind.sel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (86, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (86, (SymKind.nosel, false)) =
            ({⟨101, (SymKind.nosel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (86, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (86, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (86, (SymKind.boundary, true)) =
            ({⟨101, (SymKind.boundary, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (86, (SymKind.boundary, false)) =
            ({⟨87, (SymKind.boundary, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inr (rfl), fun hd => by decide⟩)


/-- [M4a] 状态 87 的方向表：非陷阱步方向 ∈ {R, S}；S 后继 ∈ {20}。 -/
theorem transition_87_dirTab (k : SymKind) (im : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (87, (k, im))) (hne : r.nextState ≠ 101) :
    (r.moveDir = Dir.R ∨ r.moveDir = Dir.S) ∧ (r.moveDir = Dir.S → r.nextState ∈ ({20} : Finset ℕ)) := by
  cases k <;> cases im <;>
    first
      | (have h : VerifierSym.transition (87, (SymKind.data0, true)) =
            ({⟨87, (SymKind.data0, true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inl rfl, fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (87, (SymKind.data0, false)) =
            ({⟨87, (SymKind.data0, false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inl rfl, fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (87, (SymKind.data1, true)) =
            ({⟨87, (SymKind.data1, true), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inl rfl, fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (87, (SymKind.data1, false)) =
            ({⟨87, (SymKind.data1, false), Dir.R⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inl rfl, fun hd => by cases hd⟩)
      | (have h : VerifierSym.transition (87, (SymKind.consumed, true)) =
            ({⟨101, (SymKind.consumed, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (87, (SymKind.consumed, false)) =
            ({⟨101, (SymKind.consumed, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (87, (SymKind.alpha, true)) =
            ({⟨101, (SymKind.alpha, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (87, (SymKind.alpha, false)) =
            ({⟨101, (SymKind.alpha, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (87, (SymKind.sel, true)) =
            ({⟨101, (SymKind.sel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (87, (SymKind.sel, false)) =
            ({⟨101, (SymKind.sel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (87, (SymKind.nosel, true)) =
            ({⟨101, (SymKind.nosel, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (87, (SymKind.nosel, false)) =
            ({⟨101, (SymKind.nosel, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (87, (SymKind.beta, true)) =
            ({⟨101, (SymKind.beta, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (87, (SymKind.beta, false)) =
            ({⟨101, (SymKind.beta, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact absurd rfl hne)
      | (have h : VerifierSym.transition (87, (SymKind.boundary, true)) =
            ({⟨20, (SymKind.boundary, true), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inr (rfl), fun hd => by decide⟩)
      | (have h : VerifierSym.transition (87, (SymKind.boundary, false)) =
            ({⟨20, (SymKind.boundary, false), Dir.S⟩} : Finset SymTransResult) := by decide
         rw [h] at hr
         simp at hr
         subst hr
         exact ⟨Or.inr (rfl), fun hd => by decide⟩)

-- <<< M4A-BLOCK-END

-- >>> M4B1-BEGIN
-- ==============================================================================
-- M4b-1 位置桥 / 扫掠装配件（2026-09-10,内核判定,0 新增公理）
--   ① 单步位置律:symStepConfig 头 = 头 + moveDir.toInt（定义即得）
--   ② 路径位置律:终点头 = 起始头 + Σ 步位移
--   ③ 单向扫掠长界:L 向/R 向单调步行进 ⇒ 步数 ≤ 头跨距
--   ④ 两段装配:一 L 段 + 一 R 段 ⇒ 总步数 ≤ 两段跨距之和
--   用途:与「段内扫掠数 ≤ C」的表事实合成 ⇒ 段长 ≤ (C+1)·(位置域宽+1)。
-- ==============================================================================

lemma symStepConfig_headPos (cfg : SymConfig) (r : SymTransResult) :
    (symStepConfig cfg r).headPos = cfg.headPos + r.moveDir.toInt := rfl

lemma symSteps_headPos_eq (M : ℕ × Sym → Finset SymTransResult) {cfg₀ cfg : SymConfig}
    {π : List SymStep} (h : SymSteps M cfg₀ π cfg) :
    cfg.headPos = cfg₀.headPos + (π.map (fun st => st.result.moveDir.toInt)).sum := by
  induction h with
  | nil => simp
  | cons π step cfg' hπ hfrom hread hmem ih =>
      simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
        List.sum_nil, List.append_eq, symStepConfig] at *
      omega

lemma symSteps_length_le_of_all_dirL (M : ℕ × Sym → Finset SymTransResult) {cfg₀ cfg : SymConfig}
    {π : List SymStep} (h : SymSteps M cfg₀ π cfg)
    (hd : ∀ st ∈ π, st.result.moveDir = Dir.L) :
    (π.length : ℤ) ≤ cfg₀.headPos - cfg.headPos := by
  induction h with
  | nil => simp
  | cons π step cfg' hπ hfrom hread hmem ih =>
      have hdπ : ∀ st ∈ π, st.result.moveDir = Dir.L := fun st hst => hd st (by simp [hst])
      have ih' := ih hdπ
      have hlast : step.result.moveDir = Dir.L := hd step (by simp)
      have hlen : ((π ++ [step]).length : ℤ) = (π.length : ℤ) + 1 := by simp
      have hcfg : (symStepConfig cfg' step.result).headPos = cfg'.headPos - 1 := by
        simp [symStepConfig, hlast, Dir.toInt] <;> omega
      rw [hlen, hcfg]
      omega

lemma symSteps_length_le_of_all_dirR (M : ℕ × Sym → Finset SymTransResult) {cfg₀ cfg : SymConfig}
    {π : List SymStep} (h : SymSteps M cfg₀ π cfg)
    (hd : ∀ st ∈ π, st.result.moveDir = Dir.R) :
    (π.length : ℤ) ≤ cfg.headPos - cfg₀.headPos := by
  induction h with
  | nil => simp
  | cons π step cfg' hπ hfrom hread hmem ih =>
      have hdπ : ∀ st ∈ π, st.result.moveDir = Dir.R := fun st hst => hd st (by simp [hst])
      have ih' := ih hdπ
      have hlast : step.result.moveDir = Dir.R := hd step (by simp)
      have hlen : ((π ++ [step]).length : ℤ) = (π.length : ℤ) + 1 := by simp
      have hcfg : (symStepConfig cfg' step.result).headPos = cfg'.headPos + 1 := by
        simp [symStepConfig, hlast, Dir.toInt] <;> omega
      rw [hlen, hcfg]
      omega

lemma symSteps_length_le_of_two_runs (M : ℕ × Sym → Finset SymTransResult) {cfg₀ cfg₁ cfg : SymConfig}
    {π₁ π₂ : List SymStep} (h₁ : SymSteps M cfg₀ π₁ cfg₁) (h₂ : SymSteps M cfg₁ π₂ cfg)
    (hL : ∀ st ∈ π₁, st.result.moveDir = Dir.L) (hR : ∀ st ∈ π₂, st.result.moveDir = Dir.R) :
    (π₁.length + π₂.length : ℤ) ≤ (cfg₀.headPos - cfg₁.headPos) + (cfg.headPos - cfg₁.headPos) := by
  have h1 := symSteps_length_le_of_all_dirL M h₁ hL
  have h2 := symSteps_length_le_of_all_dirR M h₂ hR
  omega
-- <<< M4B1-END


-- >>> M4B2-BEGIN
-- ==============================================================================
-- M4b-2 抽象扫掠装配件（纯组合，0 公理；2026-09-10）
--   段 = 若干「单向扫掠」顺序拼接：每段是 Sym 路径且步全 L 或全 R；
--   每段端点位置 ∈ [lo,hi] ⟹ 段长 ≤ 端点跨距（M4b-1 ③/④）
--   ⟹ 总步数 ≤ 扫掠数 × (hi-lo)。
--   用途：与 M4b-3「段内扫掠数 ≤ 2(k+1)」合成 ⟹ 段长 ≤ 2(k+1)(L+1)。
-- ==============================================================================
inductive SymSweeps (M : ℕ × Sym → Finset SymTransResult) (lo hi : ℤ) :
    SymConfig → List (List SymStep) → SymConfig → Prop
  | nil (cfg : SymConfig) : lo ≤ cfg.headPos → cfg.headPos ≤ hi →
      SymSweeps M lo hi cfg [] cfg
  | cons (cfg₀ cfg₁ cfg : SymConfig) (run : List SymStep) (rest : List (List SymStep))
      (hrun : SymSteps M cfg₀ run cfg₁)
      (hdir : (∀ st ∈ run, st.result.moveDir = Dir.L) ∨ (∀ st ∈ run, st.result.moveDir = Dir.R))
      (h₀ : lo ≤ cfg₀.headPos ∧ cfg₀.headPos ≤ hi)
      (h₁ : lo ≤ cfg₁.headPos ∧ cfg₁.headPos ≤ hi)
      (hrest : SymSweeps M lo hi cfg₁ rest cfg) :
      SymSweeps M lo hi cfg₀ (run :: rest) cfg

theorem SymSweeps_flatten_length_le {M : ℕ × Sym → Finset SymTransResult} {lo hi : ℤ}
    {cfg₀ cfg : SymConfig} {runs : List (List SymStep)}
    (hs : SymSweeps M lo hi cfg₀ runs cfg) :
    runs.flatten.length ≤ runs.length * (hi - lo).toNat := by
  induction hs with
  | nil cfg h0 h1 => simp
  | cons cfg₀ cfg₁ cfg run rest hrun hdir h₀ h₁ hrest ih =>
      have hrun_le : (run.length : ℤ) ≤ hi - lo := by
        rcases hdir with hL | hR
        · have h1 := symSteps_length_le_of_all_dirL M hrun hL
          omega
        · have h2 := symSteps_length_le_of_all_dirR M hrun hR
          omega
      have hrun_nat : run.length ≤ (hi - lo).toNat := by omega
      have hflat : (run :: rest).flatten.length = run.length + rest.flatten.length := by
        simp [List.flatten_cons]
      have hlen : (run :: rest).length = rest.length + 1 := by simp
      rw [hflat, hlen, Nat.add_mul, Nat.one_mul]
      omega
-- <<< M4B2-END




-- >>> M4B3A-BEGIN
-- ==============================================================================
-- M4b-3a 方向运行计数（纯组合，0 公理；2026-09-10）
--   扫掠数 = 方向序列的极大同向运行数 ≤ 转向数 + 1。
--   用途：把「段内扫掠数 ≤ 2(k+1)」的义务归约为「段内转向数 ≤ 2(k+1)」。
-- ==============================================================================
def symDirRuns : List Dir → ℕ
  | [] => 0
  | [_] => 1
  | d :: e :: rest => (if d = e then 0 else 1) + symDirRuns (e :: rest)

def symTurnCount : List Dir → ℕ
  | [] => 0
  | [_] => 0
  | d :: e :: rest => (if d = e then 0 else 1) + symTurnCount (e :: rest)

theorem symDirRuns_le_turnCount_add_one (ds : List Dir) :
    symDirRuns ds ≤ symTurnCount ds + 1 := by
  induction ds with
  | nil => simp [symDirRuns, symTurnCount]
  | cons d rest ih =>
      cases rest with
      | nil => simp [symDirRuns, symTurnCount]
      | cons e rest2 =>
          by_cases h : d = e
          · simp [symDirRuns, symTurnCount, h]
            exact ih
          · simp [symDirRuns, symTurnCount, h]
            omega
-- <<< M4B3A-END
-- ============================================================================
-- [M4b-3b-㋓] 相位计数底座(0 公理,纯组合)
--   C3 段界最后一块 ③b(段内转向数 ≤ 2·左穿 + C₀)的计数底座:
--   头位每步 ±1/0 且必连续 ⇒ 跨中分隔符 s 的上下穿成对。
--   注意分层:①线 `a2p_*`(PosBound2/3/4)在 ③线**下游**,本文件不可导入,
--   故 ③b 的相位论证只能用 Core 表事实 + M4a 方向表(31 态/496 格)在本文件内自证。
-- ============================================================================

/-- [M4b-3b-㋓] 段末头位 = 起点 + Σ 方向。 -/
def symHeadEnd : ℤ → List SymStep → ℤ
  | h, [] => h
  | h, st :: rest => symHeadEnd (h + st.result.moveDir.toInt) rest

/-- [M4b-3b-㋓] 左穿数:步起点头位 = s+1 且方向 L(头由中分隔符右侧跨到 s)。 -/
def symLeftCrossCount (s : ℤ) : ℤ → List SymStep → ℕ
  | _, [] => 0
  | h, st :: rest =>
      (if h = s + 1 ∧ st.result.moveDir = Dir.L then 1 else 0)
        + symLeftCrossCount s (h + st.result.moveDir.toInt) rest

/-- [M4b-3b-㋓] 右穿数:步起点头位 = s 且方向 R。 -/
def symRightCrossCount (s : ℤ) : ℤ → List SymStep → ℕ
  | _, [] => 0
  | h, st :: rest =>
      (if h = s ∧ st.result.moveDir = Dir.R then 1 else 0)
        + symRightCrossCount s (h + st.result.moveDir.toInt) rest

/-- [M4b-3b-㋓] 侧标记:h ≥ s+1 记 1(在中分隔符右侧),否则 0。 -/
def symSideR (s h : ℤ) : ℕ := if h ≥ s + 1 then 1 else 0

/-- [M4b-3b-㋓] 单步局部恒等式:侧标记的变化恰由左右穿的指示量给出。 -/
private lemma symCross_local (s h : ℤ) (d : Dir) :
    (if h = s ∧ d = Dir.R then 1 else 0) + symSideR s h
      = (if h = s + 1 ∧ d = Dir.L then 1 else 0) + symSideR s (h + d.toInt) := by
  have hLR : ¬ (Dir.R = Dir.L) := by decide
  cases d with
  | L =>
      have hne : ¬ (Dir.L = Dir.R) := by decide
      simp only [hne, and_false, if_false, and_true, Dir.toInt, symSideR]
      split_ifs <;> omega
  | R =>
      simp only [hLR, and_false, if_false, and_true, Dir.toInt, symSideR]
      split_ifs <;> omega
  | S =>
      have hne : ¬ (Dir.S = Dir.R) := by decide
      have hne2 : ¬ (Dir.S = Dir.L) := by decide
      simp only [hne, hne2, and_false, if_false, Dir.toInt, symSideR]
      split_ifs <;> omega

/-- [M4b-3b-㋓] 穿越平衡:右穿数 + [起点在右] = 左穿数 + [终点在右]。
    推论:段首尾都在右侧(≥ s+1)时,段内左穿数 = 右穿数。 -/
theorem symCross_balance (s h : ℤ) (steps : List SymStep) :
    symRightCrossCount s h steps + symSideR s h
      = symLeftCrossCount s h steps + symSideR s (symHeadEnd h steps) := by
  induction steps generalizing h with
  | nil => simp [symRightCrossCount, symLeftCrossCount, symHeadEnd]
  | cons st rest ih =>
      have hl := ih (h + st.result.moveDir.toInt)
      have hloc := symCross_local s h st.result.moveDir
      simp only [symRightCrossCount, symLeftCrossCount, symHeadEnd]
      omega

/-- [M4b-3b-㋓] 推论:段首尾头位都 ≥ s+1 ⇒ 段内左穿数 = 右穿数。 -/
theorem symLeftCrossCount_eq_rightCrossCount (s h : ℤ) (steps : List SymStep)
    (hstart : h ≥ s + 1) (hend : symHeadEnd h steps ≥ s + 1) :
    symLeftCrossCount s h steps = symRightCrossCount s h steps := by
  have hb := symCross_balance s h steps
  simp only [symSideR, if_pos hstart, if_pos hend] at hb
  omega

-- ============================================================================
-- [M4b-3b-㋑-①] 相位切分:穿越事件交替
--   相位 = 相邻跨 s 事件之间的一段 ⇒ 每次左穿必配一个后续右穿(一趟来回)。
--   侧假设:期望左穿时头必在右侧(h ≥ s+1),期望右穿时头必在左侧(h ≤ s)。
-- ============================================================================

/-- [㋑-①] 交替谓词:`expectL = true` 表示期望下一个穿越事件是左穿。 -/
def SymAlt : Bool → List Dir → Prop
  | _, [] => True
  | expectL, x :: rest => x = (if expectL then Dir.L else Dir.R) ∧ SymAlt (!expectL) rest

/-- [㋑-①] 穿越事件序列(按步序):`h` = 该步起点头位;只记左穿/右穿。 -/
def symCrossList (s : ℤ) : ℤ → List SymStep → List Dir
  | _, [] => []
  | h, st :: rest =>
      (if h = s + 1 ∧ st.result.moveDir = Dir.L then [Dir.L]
        else if h = s ∧ st.result.moveDir = Dir.R then [Dir.R] else [])
        ++ symCrossList s (h + st.result.moveDir.toInt) rest

/-- [㋑-①] 主引理:起点在右侧(期望左穿)时,段内穿越事件必交替,且首个必是左穿。 -/
theorem symCrossList_alt (s : ℤ) :
    ∀ (steps : List SymStep) (h : ℤ) (expectL : Bool),
      (expectL = true → h ≥ s + 1) → (expectL = false → h ≤ s) →
      SymAlt expectL (symCrossList s h steps) := by
  intro steps
  induction steps with
  | nil => intro h expectL _ _; exact trivial
  | cons st rest ih =>
      intro h expectL hL hR
      cases hdir : st.result.moveDir with
      | L =>
        by_cases hc : h = s + 1
        · -- 左穿:期望方向必为 L,新头 h-1 = s
          have hl : expectL = true := by
            cases expectL with
            | true => rfl
            | false => exact absurd (hR rfl) (by omega)
          subst hl
          have hnew : h + st.result.moveDir.toInt ≤ s := by
            simp only [hdir, Dir.toInt]; omega
          have hstep : symCrossList s h (st :: rest)
              = Dir.L :: symCrossList s (h + st.result.moveDir.toInt) rest := by
            simp [symCrossList, hdir, hc]
          rw [hstep]
          exact ⟨rfl, ih (h + st.result.moveDir.toInt) false (by simp) (fun _ => hnew)⟩
        · -- 非穿越(仍向左):侧假设保持
          have hstep : symCrossList s h (st :: rest)
              = symCrossList s (h + st.result.moveDir.toInt) rest := by
            simp [symCrossList, hdir, hc]
          rw [hstep]
          exact ih (h + st.result.moveDir.toInt) expectL
            (fun he => by have hge := hL he; simp only [hdir, Dir.toInt] at *; omega)
            (fun he => by have hle := hR he; simp only [hdir, Dir.toInt] at *; omega)
      | R =>
        by_cases hc : h = s
        · -- 右穿:期望方向必为 R,新头 h+1 = s+1
          have hl : expectL = false := by
            cases expectL with
            | false => rfl
            | true => exact absurd (hL rfl) (by omega)
          subst hl
          have hnew : h + st.result.moveDir.toInt ≥ s + 1 := by
            simp only [hdir, Dir.toInt]; omega
          have hstep : symCrossList s h (st :: rest)
              = Dir.R :: symCrossList s (h + st.result.moveDir.toInt) rest := by
            simp [symCrossList, hdir, hc]
          rw [hstep]
          exact ⟨rfl, ih (h + st.result.moveDir.toInt) true (fun _ => hnew) (by simp)⟩
        · -- 非穿越(仍向右):侧假设保持
          have hstep : symCrossList s h (st :: rest)
              = symCrossList s (h + st.result.moveDir.toInt) rest := by
            simp [symCrossList, hdir, hc]
          rw [hstep]
          exact ih (h + st.result.moveDir.toInt) expectL
            (fun he => by have hge := hL he; simp only [hdir, Dir.toInt] at *; omega)
            (fun he => by have hle := hR he; simp only [hdir, Dir.toInt] at *; omega)
      | S =>
        -- 不动:永不穿越,侧假设原样保持
        have hstep : symCrossList s h (st :: rest)
            = symCrossList s h rest := by
          simp [symCrossList, hdir, Dir.toInt]
        rw [hstep]
        exact ih h expectL hL hR

-- ============================================================================
-- [M4b-3b-㋑-②-α] 相位内头位不越侧:段内无穿越事件 ⟹ 全程停在 s 的一侧
-- ============================================================================

/-- [㋑-②-α] 段内最小头位(含起点与每步落点)。 -/
def symMinHead : ℤ → List SymStep → ℤ
  | h, [] => h
  | h, st :: rest => min h (symMinHead (h + st.result.moveDir.toInt) rest)

/-- [㋑-②-α] 段内最大头位。 -/
def symMaxHead : ℤ → List SymStep → ℤ
  | h, [] => h
  | h, st :: rest => max h (symMaxHead (h + st.result.moveDir.toInt) rest)

/-- [㋑-②-α] 右侧相位:段内无穿越且起点在右侧 ⟹ 整段头位 ≥ s+1。 -/
theorem symMinHead_ge_of_noCross (s : ℤ) :
    ∀ (steps : List SymStep) (h : ℤ),
      symCrossList s h steps = [] → h ≥ s + 1 → symMinHead h steps ≥ s + 1 := by
  intro steps
  induction steps with
  | nil => intro h _ hge; simpa [symMinHead] using hge
  | cons st rest ih =>
      intro h hempty hge
      by_cases hc : h = s + 1 ∧ st.result.moveDir = Dir.L
      · simp [symCrossList, hc] at hempty
      · by_cases hc2 : h = s ∧ st.result.moveDir = Dir.R
        · simp [symCrossList, hc, hc2] at hempty
        · have h0 : symCrossList s h (st :: rest)
              = symCrossList s (h + st.result.moveDir.toInt) rest := by
            simp [symCrossList, hc, hc2]
          rw [h0] at hempty
          have hge' : h + st.result.moveDir.toInt ≥ s + 1 := by
            cases hdir : st.result.moveDir with
            | L =>
                have hne : h ≠ s + 1 := fun he => hc ⟨he, hdir⟩
                simp only [hdir, Dir.toInt]; omega
            | R => simp only [hdir, Dir.toInt]; omega
            | S => simp only [hdir, Dir.toInt]; omega
          have ih' := ih (h + st.result.moveDir.toInt) hempty hge'
          simp only [symMinHead]
          exact le_min hge ih'

/-- [㋑-②-α] 左侧相位:段内无穿越且起点在左侧 ⟹ 整段头位 ≤ s。 -/
theorem symMaxHead_le_of_noCross (s : ℤ) :
    ∀ (steps : List SymStep) (h : ℤ),
      symCrossList s h steps = [] → h ≤ s → symMaxHead h steps ≤ s := by
  intro steps
  induction steps with
  | nil => intro h _ hle; simpa [symMaxHead] using hle
  | cons st rest ih =>
      intro h hempty hle
      by_cases hc : h = s + 1 ∧ st.result.moveDir = Dir.L
      · simp [symCrossList, hc] at hempty
      · by_cases hc2 : h = s ∧ st.result.moveDir = Dir.R
        · simp [symCrossList, hc, hc2] at hempty
        · have h0 : symCrossList s h (st :: rest)
              = symCrossList s (h + st.result.moveDir.toInt) rest := by
            simp [symCrossList, hc, hc2]
          rw [h0] at hempty
          have hle' : h + st.result.moveDir.toInt ≤ s := by
            cases hdir : st.result.moveDir with
            | L => simp only [hdir, Dir.toInt]; omega
            | R =>
                have hne : h ≠ s := fun he => hc2 ⟨he, hdir⟩
                simp only [hdir, Dir.toInt]; omega
            | S => simp only [hdir, Dir.toInt]; omega
          have ih' := ih (h + st.result.moveDir.toInt) hempty hle'
          simp only [symMaxHead]
          exact max_le hle ih'

-- >>> M4B3BG-BEGIN
-- ==============================================================================
-- [M4b-3b-γ] 三次方口径（2026-09-10 用户裁决：左穿按 L 计 + 整体放宽到三次方）
--   ① 格方向唯一性（表事实，decide 生成）：同一格 (q,k,im) 的所有活转移方向相同
--      ⇒ 一次「转向」完整由 (位置, 状态) 决定（与量测 3「多方向格 = 0」同口径）。
--   ② 转向步配对 symTurnPairs：步 i 与步 i+1 方向不同时记 (起点头位, 起点状态)；
--      symTurnPairs_length_eq：配对长度 = symTurnCount（与 M4b-3a 同口径）。
--   ③ 鸽笼 symTurnPairs_length_le：配对互不重复 + 头位 ∈ [0,L) + 状态 < 102
--      ⟹ 转向数 ≤ L×102。
--   链：段长 ≤ #扫掠·(L+1)〔M4b-2〕+ #扫掠 ≤ 转向+1〔M4b-3a〕
--       ⟹ 段长 ≤ (102L+103)(L+1) ⟹ 总步数 ≤ 103(L+1)^3。
-- ==============================================================================
/-- [M4b-3b-γ①] 格方向唯一性（状态 0）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_0 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (0, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 1）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_1 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (1, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 2）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_2 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (2, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 3）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_3 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (3, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 4）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_4 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (4, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 5）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_5 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (5, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 8）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_8 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (8, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 9）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_9 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (9, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 10）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_10 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (10, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 11）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_11 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (11, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 12）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_12 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (12, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 13）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_13 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (13, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 14）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_14 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (14, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 20）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_20 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (20, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 21）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_21 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (21, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 22）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_22 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (22, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 23）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_23 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (23, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 24）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_24 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (24, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 26）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_26 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (26, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 27）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_27 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (27, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 28）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_28 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (28, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 29）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_29 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (29, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 38）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_38 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (38, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 51）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_51 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (51, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 76）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_76 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (76, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 77）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_77 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (77, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 81）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_81 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (81, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 84）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_84 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (84, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 85）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_85 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (85, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 86）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_86 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (86, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide

/-- [M4b-3b-γ①] 格方向唯一性（状态 87）：该态 16 个格 (k,im) 的活转移方向均唯一。 -/
theorem transition_dirUnique_87 (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (87, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  cases k <;> cases im <;> decide
/-- [M4b-3b-γ①] 31 个相态的格方向唯一性汇总。
    用途：一个「转向步」把 (位置, 状态) 配对后，同一配对不可能对应两个不同方向。 -/
theorem transition_dirUnique_allStates (q : ℕ)
    (hq : q ∈ ({0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 24, 26, 27, 28, 29, 38, 51, 76, 77, 81, 84, 85, 86, 87} : Finset ℕ)) (k : SymKind) (im : Bool) :
    (((VerifierSym.transition (q, (k, im))).filter (fun r => r.nextState ≠ 101)).image
      (fun r => r.moveDir)).card ≤ 1 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact transition_dirUnique_0 k im
  · exact transition_dirUnique_1 k im
  · exact transition_dirUnique_2 k im
  · exact transition_dirUnique_3 k im
  · exact transition_dirUnique_4 k im
  · exact transition_dirUnique_5 k im
  · exact transition_dirUnique_8 k im
  · exact transition_dirUnique_9 k im
  · exact transition_dirUnique_10 k im
  · exact transition_dirUnique_11 k im
  · exact transition_dirUnique_12 k im
  · exact transition_dirUnique_13 k im
  · exact transition_dirUnique_14 k im
  · exact transition_dirUnique_20 k im
  · exact transition_dirUnique_21 k im
  · exact transition_dirUnique_22 k im
  · exact transition_dirUnique_23 k im
  · exact transition_dirUnique_24 k im
  · exact transition_dirUnique_26 k im
  · exact transition_dirUnique_27 k im
  · exact transition_dirUnique_28 k im
  · exact transition_dirUnique_29 k im
  · exact transition_dirUnique_38 k im
  · exact transition_dirUnique_51 k im
  · exact transition_dirUnique_76 k im
  · exact transition_dirUnique_77 k im
  · exact transition_dirUnique_81 k im
  · exact transition_dirUnique_84 k im
  · exact transition_dirUnique_85 k im
  · exact transition_dirUnique_86 k im
  · exact transition_dirUnique_87 k im
/-- [M4b-3b-γ②] 转向步配对序列：当前步与其后一步方向不同（含 S）时，
    记下该步的 (起点头位, 起点状态)，然后沿轨迹前进。 -/
def symTurnPairs : ℤ → ℕ → List SymStep → List (ℤ × ℕ)
  | _, _, [] => []
  | _, _, [_] => []
  | h, q, st₁ :: st₂ :: rest =>
      (if st₁.result.moveDir = st₂.result.moveDir then [] else [(h, q)])
        ++ symTurnPairs (h + st₁.result.moveDir.toInt) st₁.result.nextState (st₂ :: rest)

/-- [M4b-3b-γ②] 配对序列长度 = 转向数（与 M4b-3a 的 symTurnCount 同口径）。 -/
theorem symTurnPairs_length_eq (h : ℤ) (q : ℕ) (π : List SymStep) :
    (symTurnPairs h q π).length = symTurnCount (π.map (fun st => st.result.moveDir)) := by
  induction π generalizing h q with
  | nil => rfl
  | cons st₁ rest ih =>
      cases rest with
      | nil => rfl
      | cons st₂ rest2 =>
          simp only [List.map_cons, symTurnPairs, symTurnCount, List.length_cons,
            List.length_append, List.length_nil, ih]
          by_cases hd : st₁.result.moveDir = st₂.result.moveDir <;> simp [hd]

/-- [M4b-3b-γ③-引] 互不重复的 ℕ×ℕ 序列，若第一坐标 < L、第二坐标 < 102，则长度 ≤ L×102（鸽笼）。 -/
theorem natPairs_length_le_of_nodup {l : List (ℕ × ℕ)} {L : ℕ} (hnd : l.Nodup)
    (h1 : ∀ p ∈ l, p.1 < L) (h2 : ∀ p ∈ l, p.2 < 102) : l.length ≤ L * 102 := by
  have hsub : l.toFinset ⊆ Finset.range L ×ˢ Finset.range 102 := by
    intro p hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨h1 p (List.mem_toFinset.mp hp), h2 p (List.mem_toFinset.mp hp)⟩
  calc l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ (Finset.range L ×ˢ Finset.range 102).card := Finset.card_le_card hsub
    _ = L * 102 := by rw [Finset.card_product, Finset.card_range, Finset.card_range]

/-- [M4b-3b-γ③-引] 非负 ℤ 坐标序列经 toNat 投影后仍互不重复。 -/
theorem nodup_map_toNat {l : List (ℤ × ℕ)} (hnd : l.Nodup)
    (hpos : ∀ p ∈ l, 0 ≤ p.1) :
    (l.map (fun p : ℤ × ℕ => (p.1.toNat, p.2))).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.nodup_cons] at hnd
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih hnd.2 (fun p hp => hpos p (List.mem_cons_of_mem x hp))⟩
      intro hmem
      obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hmem
      have hy0 : 0 ≤ y.1 := hpos y (List.mem_cons_of_mem x hy)
      have hx0 : 0 ≤ x.1 := hpos x (by simp)
      have hyx' : y = x := by
        obtain ⟨ha, hb⟩ := Prod.ext_iff.mp hyx
        have ha' : y.1.toNat = x.1.toNat := ha
        have hb' : y.2 = x.2 := hb
        refine Prod.ext ?_ hb'
        have hcast : ((y.1.toNat : ℕ) : ℤ) = ((x.1.toNat : ℕ) : ℤ) := by rw [ha']
        simpa [Int.toNat_of_nonneg hy0, Int.toNat_of_nonneg hx0] using hcast
      exact hnd.1 (hyx' ▸ hy)

/-- [M4b-3b-γ③] 鸽笼主引理：转向步的 (起点头位, 起点状态) 对互不重复，
    且头位落在 [0,L)、状态 < 102，则转向数 ≤ L×102。 -/
theorem symTurnPairs_length_le {h₀ : ℤ} {q₀ : ℕ} {π : List SymStep} {L : ℕ}
    (hnd : (symTurnPairs h₀ q₀ π).Nodup)
    (hpos : ∀ p ∈ symTurnPairs h₀ q₀ π, 0 ≤ p.1 ∧ p.1 < (L : ℤ))
    (hst : ∀ p ∈ symTurnPairs h₀ q₀ π, p.2 < 102) :
    (symTurnPairs h₀ q₀ π).length ≤ L * 102 := by
  have hnd' := nodup_map_toNat hnd (fun p hp => (hpos p hp).1)
  have h1 : ∀ p ∈ (symTurnPairs h₀ q₀ π).map (fun p : ℤ × ℕ => (p.1.toNat, p.2)), p.1 < L := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    exact (Int.toNat_lt (hpos x hx).1).mpr (hpos x hx).2
  have h2 : ∀ p ∈ (symTurnPairs h₀ q₀ π).map (fun p : ℤ × ℕ => (p.1.toNat, p.2)), p.2 < 102 := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    exact hst x hx
  simpa using natPairs_length_le_of_nodup hnd' h1 h2
-- <<< M4B3BG-END


-- >>> M4B3BD-BEGIN
-- ==============================================================================
-- [M4b-3b-δ] 段长装配（三次方链第 2 环）—— 第 1 段：头位轨迹 + 单向扫掠长度界
--   段长链：段长 ≤ (#极大同向扫掠)·(位置窗口)〔本件〕+ #扫掠 = 转向数+1（切点即转向点）
--           + 转向数 ≤ L×102（M4b-3b-γ③）⟹ 段长 ≤ (102L+1)(L+1)
--   本件不依赖 SymSteps（子步列表无独立 SymSteps 推导），只用纯步列 + 位置窗口。
-- ==============================================================================

/-- [M4b-3b-δ] 头位轨迹：每步起点头位（不含终止位；长度 = π.length）。 -/
def symPositions (h₀ : ℤ) : List SymStep → List ℤ
  | [] => []
  | st :: rest => h₀ :: symPositions (h₀ + st.result.moveDir.toInt) rest

/-- [M4b-3b-δ] 终止头位：走完 π 后的头位。 -/
def symEnd (h₀ : ℤ) : List SymStep → ℤ
  | [] => h₀
  | st :: rest => symEnd (h₀ + st.result.moveDir.toInt) rest

/-- [M4b-3b-δ] 轨迹对拼接可加。 -/
theorem symPositions_append (h₀ : ℤ) (π₁ π₂ : List SymStep) :
    symPositions h₀ (π₁ ++ π₂) = symPositions h₀ π₁ ++ symPositions (symEnd h₀ π₁) π₂ := by
  induction π₁ generalizing h₀ with
  | nil => simp [symPositions, symEnd]
  | cons st rest ih => simp [symPositions, symEnd, ih]

/-- [M4b-3b-δ] 终止头位对拼接可加。 -/
theorem symEnd_append (h₀ : ℤ) (π₁ π₂ : List SymStep) :
    symEnd h₀ (π₁ ++ π₂) = symEnd (symEnd h₀ π₁) π₂ := by
  induction π₁ generalizing h₀ with
  | nil => simp [symEnd]
  | cons st rest ih => simp [symEnd, ih]

/-- [M4b-3b-δ] 全 R 步列：长度 = 终止位 − 起位。 -/
theorem symSingleDirR_length_le (h₀ : ℤ) (π : List SymStep)
    (hd : ∀ st ∈ π, st.result.moveDir = Dir.R) :
    (π.length : ℤ) ≤ symEnd h₀ π - h₀ := by
  induction π generalizing h₀ with
  | nil => simp [symEnd]
  | cons st rest ih =>
      have hd0 : st.result.moveDir = Dir.R := hd st (by simp)
      have hdR : ∀ s ∈ rest, s.result.moveDir = Dir.R := fun s hs => hd s (by simp [hs])
      have ih' := ih (h₀ + st.result.moveDir.toInt) hdR
      have he : symEnd h₀ (st :: rest) = symEnd (h₀ + 1) rest := by
        simp [symEnd, hd0, Dir.toInt]
      have hh : h₀ + st.result.moveDir.toInt = h₀ + 1 := by simp [hd0, Dir.toInt]
      have hcast : ((rest.length + 1 : ℕ) : ℤ) = (rest.length : ℤ) + 1 := by omega
      rw [List.length_cons, hcast, he]
      rw [hh] at ih'
      linarith

/-- [M4b-3b-δ] 全 L 步列：长度 = 起位 − 终止位。 -/
theorem symSingleDirL_length_le (h₀ : ℤ) (π : List SymStep)
    (hd : ∀ st ∈ π, st.result.moveDir = Dir.L) :
    (π.length : ℤ) ≤ h₀ - symEnd h₀ π := by
  induction π generalizing h₀ with
  | nil => simp [symEnd]
  | cons st rest ih =>
      have hd0 : st.result.moveDir = Dir.L := hd st (by simp)
      have hdL : ∀ s ∈ rest, s.result.moveDir = Dir.L := fun s hs => hd s (by simp [hs])
      have ih' := ih (h₀ + st.result.moveDir.toInt) hdL
      have he : symEnd h₀ (st :: rest) = symEnd (h₀ + (-1)) rest := by
        simp [symEnd, hd0, Dir.toInt]
      have hh : h₀ + st.result.moveDir.toInt = h₀ + (-1) := by simp [hd0, Dir.toInt]
      have hcast : ((rest.length + 1 : ℕ) : ℤ) = (rest.length : ℤ) + 1 := by omega
      rw [List.length_cons, hcast, he]
      rw [hh] at ih'
      linarith

/-- [M4b-3b-δ] **单向扫掠长度 ≤ 位置窗口**：步列方向单一、起点与终点均落在 [lo,hi] 内
    ⟹ 步数 ≤ (hi−lo).toNat。段长装配时对每个极大同向扫掠使用。 -/
theorem symSingleDir_length_le_of_window (h₀ : ℤ) (π : List SymStep) (lo hi : ℤ)
    (hd : (∀ st ∈ π, st.result.moveDir = Dir.R) ∨ (∀ st ∈ π, st.result.moveDir = Dir.L))
    (hstart : lo ≤ h₀ ∧ h₀ ≤ hi)
    (hend : lo ≤ symEnd h₀ π ∧ symEnd h₀ π ≤ hi) :
    (π.length : ℤ) ≤ (hi - lo).toNat := by
  have h4 : (0 : ℤ) ≤ hi - lo := by linarith [hstart.1, hend.2]
  have hkey : (π.length : ℤ) ≤ hi - lo := by
    rcases hd with hdR | hdL
    · have h := symSingleDirR_length_le h₀ π hdR
      linarith
    · have h := symSingleDirL_length_le h₀ π hdL
      linarith
  calc (π.length : ℤ) ≤ hi - lo := hkey
    _ ≤ (↑((hi - lo).toNat) : ℤ) := by
        rw [Int.toNat_of_nonneg h4]
-- <<< M4B3BD-END


-- >>> M4B3BD2-BEGIN
-- ==============================================================================
-- M4b-3b-δ-2 段长装配第 2 环：极大同向扫掠切分 + 扫掠数 ≤ 转向数+1（2026-09-10）
--   symTakeDir/symDropDir：方向 d 的极大同向前缀 / 其余；
--   symRunsOf：按方向变化切分（WF 递归，measure = 长度；eq_1/eq_2 无条件等式）；
--   symRunsOf_flatten：切分拼接回原步列；symRunsOf_singleDir/ne_nil：每段同向非空；
--   symRunsOf_length_le_turnCount_add_one：#扫掠 ≤ 转向数 + 1。
-- ==============================================================================


/-- [M4b-3b-δ-2] 取方向 d 的极大同向前缀。 -/
def symTakeDir (d : Dir) : List SymStep → List SymStep
  | [] => []
  | st :: rest => if st.result.moveDir = d then st :: symTakeDir d rest else []

/-- [M4b-3b-δ-2] 去掉方向 d 的极大同向前缀后的剩余。 -/
def symDropDir (d : Dir) : List SymStep → List SymStep
  | [] => []
  | st :: rest => if st.result.moveDir = d then symDropDir d rest else st :: rest

theorem symDropDir_length_le (d : Dir) (π : List SymStep) :
    (symDropDir d π).length ≤ π.length := by
  induction π with
  | nil => simp [symDropDir]
  | cons st rest ih =>
      by_cases h : st.result.moveDir = d
      · simp [symDropDir, h]
        exact Nat.le_succ_of_le ih
      · simp [symDropDir, h]

theorem symTakeDir_append_symDropDir (d : Dir) (π : List SymStep) :
    symTakeDir d π ++ symDropDir d π = π := by
  induction π with
  | nil => rfl
  | cons st rest ih =>
      by_cases h : st.result.moveDir = d
      · simp [symTakeDir, symDropDir, h, ih]
      · simp [symTakeDir, symDropDir, h]

theorem symTakeDir_all (d : Dir) (π : List SymStep) :
    ∀ st ∈ symTakeDir d π, st.result.moveDir = d := by
  induction π with
  | nil => intro st hst; simp [symTakeDir] at hst
  | cons st rest ih =>
      intro s hs
      by_cases h : st.result.moveDir = d
      · have hs' : s = st ∨ s ∈ symTakeDir d rest := by
          simpa [symTakeDir, h] using hs
        rcases hs' with rfl | hs'
        · exact h
        · exact ih s hs'
      · have hs' : s ∈ ([] : List SymStep) := by
          simpa [symTakeDir, h] using hs
        exact absurd hs' (by simp)

theorem symDropDir_head_ne (d : Dir) (π : List SymStep) (st : SymStep) (rest : List SymStep)
    (h : symDropDir d π = st :: rest) : st.result.moveDir ≠ d := by
  induction π with
  | nil => simp [symDropDir] at h
  | cons st' rest' ih =>
      by_cases h' : st'.result.moveDir = d
      · simp only [symDropDir, h', ↓reduceIte] at h
        exact ih h
      · simp only [symDropDir, h', ↓reduceIte] at h
        have hst : st' = st := (List.cons.injEq _ _ _ _).mp h |>.1
        rw [← hst]
        exact h'

/-- [M4b-3b-δ-2] 极大同向扫掠切分。 -/
def symRunsOf : List SymStep → List (List SymStep)
  | [] => []
  | st :: rest =>
      (st :: symTakeDir st.result.moveDir rest) :: symRunsOf (symDropDir st.result.moveDir rest)
termination_by π => π.length
decreasing_by
  simp_wf
  exact symDropDir_length_le _ _

theorem symRunsOf_flatten (π : List SymStep) : (symRunsOf π).flatten = π := by
  induction π using symRunsOf.induct with
  | case1 => rw [symRunsOf.eq_1]; rfl
  | case2 st rest ih =>
      rw [symRunsOf.eq_2, List.flatten_cons, List.cons_append, ih,
        symTakeDir_append_symDropDir]

theorem symRunsOf_singleDir (π : List SymStep) :
    ∀ r ∈ symRunsOf π, ∃ d : Dir, ∀ st ∈ r, st.result.moveDir = d := by
  induction π using symRunsOf.induct with
  | case1 => intro r hr; rw [symRunsOf.eq_1] at hr; simp at hr
  | case2 st rest ih =>
      intro r hr
      rw [symRunsOf.eq_2] at hr
      rcases List.mem_cons.mp hr with rfl | hr
      · refine ⟨st.result.moveDir, fun s hs => ?_⟩
        rcases List.mem_cons.mp hs with rfl | hs
        · rfl
        · exact symTakeDir_all _ _ s hs
      · exact ih r hr

theorem symRunsOf_ne_nil (π : List SymStep) : ∀ r ∈ symRunsOf π, r ≠ [] := by
  induction π using symRunsOf.induct with
  | case1 => intro r hr; rw [symRunsOf.eq_1] at hr; simp at hr
  | case2 st rest ih =>
      intro r hr
      rw [symRunsOf.eq_2] at hr
      rcases List.mem_cons.mp hr with rfl | hr
      · simp
      · exact ih r hr

theorem symTurnCount_cons_cons_self (d : Dir) (rest : List Dir) :
    symTurnCount (d :: d :: rest) = symTurnCount (d :: rest) := by
  simp [symTurnCount]

theorem symTurnCount_cons_cons_ne {d e : Dir} (h : d ≠ e) (rest : List Dir) :
    symTurnCount (d :: e :: rest) = 1 + symTurnCount (e :: rest) := by
  cases rest with
  | nil => simp [symTurnCount, h]
  | cons a b => simp [symTurnCount, h]

theorem symRunsOf_length_le_turnCount_add_one_aux (d : Dir) (rest : List SymStep) :
    (symRunsOf (symDropDir d rest)).length + 1
      ≤ symTurnCount (d :: rest.map (fun st => st.result.moveDir)) + 1 := by
  induction rest generalizing d with
  | nil => rw [symDropDir, symRunsOf.eq_1]; simp [symTurnCount]
  | cons st rest' ih =>
      by_cases h : st.result.moveDir = d
      · have hdrop : symDropDir d (st :: rest') = symDropDir d rest' := by
          simp [symDropDir, h]
        have htc : symTurnCount (d :: (st :: rest').map (fun x => x.result.moveDir))
            = symTurnCount (d :: rest'.map (fun x => x.result.moveDir)) := by
          simp only [List.map_cons]
          rw [h]
          exact symTurnCount_cons_cons_self d (rest'.map (fun x => x.result.moveDir))
        rw [hdrop, htc]
        exact ih d
      · have hdrop : symDropDir d (st :: rest') = st :: rest' := by
          simp [symDropDir, h]
        have htc : symTurnCount (d :: (st :: rest').map (fun x => x.result.moveDir))
            = 1 + symTurnCount (st.result.moveDir :: rest'.map (fun x => x.result.moveDir)) := by
          simp only [List.map_cons]
          exact symTurnCount_cons_cons_ne (fun hh => h hh.symm)
            (rest'.map (fun x => x.result.moveDir))
        rw [hdrop, symRunsOf.eq_2, List.length_cons, htc]
        have hih := ih st.result.moveDir
        omega

theorem symRunsOf_length_le_turnCount_add_one (π : List SymStep) :
    (symRunsOf π).length ≤ symTurnCount (π.map (fun st => st.result.moveDir)) + 1 := by
  cases π with
  | nil => rw [symRunsOf.eq_1]; simp [symTurnCount]
  | cons st rest =>
      have h := symRunsOf_length_le_turnCount_add_one_aux st.result.moveDir rest
      rw [symRunsOf.eq_2]
      simp only [List.map_cons, List.length_cons]
      omega




/-- [M4b-3b-δ-3] 终止状态：走完 π 后的状态。 -/
def symEndState (q : ℕ) : List SymStep → ℕ
  | [] => q
  | st :: rest => symEndState st.result.nextState rest

/-- [M4b-3b-δ-3] 各步 (起点头位, 起点状态) 对。 -/
def symStepPairs : ℤ → ℕ → List SymStep → List (ℤ × ℕ)
  | _, _, [] => []
  | h, q, st :: rest => (h, q) :: symStepPairs (h + st.result.moveDir.toInt) st.result.nextState rest

theorem symStepPairs_append (h : ℤ) (q : ℕ) (π₁ π₂ : List SymStep) :
    symStepPairs h q (π₁ ++ π₂)
      = symStepPairs h q π₁ ++ symStepPairs (symEnd h π₁) (symEndState q π₁) π₂ := by
  induction π₁ generalizing h q with
  | nil => rfl
  | cons st rest ih => simp [symStepPairs, symEnd, symEndState, ih]

theorem symStepPairs_length (h : ℤ) (q : ℕ) (π : List SymStep) :
    (symStepPairs h q π).length = π.length := by
  induction π generalizing h q with
  | nil => rfl
  | cons st rest ih => simp [symStepPairs, ih]

/-- [M4b-3b-δ-3] 互不相同且都 < 102 的自然数 ⇒ 个数 ≤ 102。 -/
theorem nodup_nat_length_le (l : List ℕ) (hnd : l.Nodup) (hlt : ∀ x ∈ l, x < 102) :
    l.length ≤ 102 := by
  have hsub : l.toFinset ⊆ Finset.range 102 := by
    intro x hx
    rw [Finset.mem_range]
    exact hlt x (List.mem_toFinset.mp hx)
  calc l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ (Finset.range 102).card := Finset.card_le_card hsub
    _ = 102 := Finset.card_range 102

/-- [M4b-3b-δ-3] 首分量恒为 x 的配对互不相同 ⇒ 次分量互不相同。 -/
theorem nodup_snd_of_const_fst {l : List (ℤ × ℕ)} (hnd : l.Nodup) {x : ℤ}
    (hfst : ∀ p ∈ l, p.1 = x) : (l.map (fun p => p.2)).Nodup := by
  induction l with
  | nil => simp
  | cons p rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd ⊢
      refine ⟨?_, ih hnd.2 (fun p' hp' => hfst p' (List.mem_cons_of_mem p hp'))⟩
      intro hmem
      obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hmem
      have hy1 : y.1 = x := hfst y (List.mem_cons_of_mem p hy)
      have hp1 : p.1 = x := hfst p (by simp)
      have hyx' : y = p := Prod.ext (by rw [hy1, hp1]) hyx
      exact hnd.1 (hyx' ▸ hy)

/-- [M4b-3b-δ-3] 全 S 步 ⇒ 配对首分量恒为起点（头位不动）。 -/
theorem symStepPairs_fst_of_allS (h₀ : ℤ) (q₀ : ℕ) (run : List SymStep)
    (hd : ∀ st ∈ run, st.result.moveDir = Dir.S) :
    ∀ p ∈ symStepPairs h₀ q₀ run, p.1 = h₀ := by
  induction run generalizing h₀ q₀ with
  | nil => intro p hp; simp [symStepPairs] at hp
  | cons st rest ih =>
      intro p hp
      have hd0 : st.result.moveDir = Dir.S := hd st (by simp)
      have hdR : ∀ s ∈ rest, s.result.moveDir = Dir.S := fun s hs => hd s (by simp [hs])
      have hpos : h₀ + st.result.moveDir.toInt = h₀ := by rw [hd0]; simp [Dir.toInt]
      simp only [symStepPairs, List.mem_cons] at hp
      rcases hp with rfl | hp'
      · rfl
      · rw [hpos] at hp'
        exact ih h₀ st.result.nextState hdR p hp'

/-- [M4b-3b-δ-3] **全 S 段：长度 ≤ 102**（头位不动 ⟹ 配对互不重复即状态互不相同）。 -/
theorem symAllS_length_le (h₀ : ℤ) (q₀ : ℕ) (run : List SymStep)
    (hd : ∀ st ∈ run, st.result.moveDir = Dir.S)
    (hnd : (symStepPairs h₀ q₀ run).Nodup)
    (hlt : ∀ p ∈ symStepPairs h₀ q₀ run, p.2 < 102) :
    run.length ≤ 102 := by
  have hfst := symStepPairs_fst_of_allS h₀ q₀ run hd
  have hndS := nodup_snd_of_const_fst hnd hfst
  have hltS : ∀ x ∈ (symStepPairs h₀ q₀ run).map (fun p => p.2), x < 102 := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact hlt p hp
  have hb := nodup_nat_length_le _ hndS hltS
  simpa [List.length_map, symStepPairs_length] using hb

/-- [M4b-3b-δ-3] **逐段界**：方向单一的一段，长度 ≤ 窗口 + 102
    （L/R 走窗口推论；S 走状态计数 —— S 步不动头，窗口管不到）。 -/
theorem symRun_length_le (h₀ : ℤ) (q₀ : ℕ) (run : List SymStep) (d : Dir) (lo hi : ℤ)
    (hall : ∀ s ∈ run, s.result.moveDir = d)
    (hstart : lo ≤ h₀ ∧ h₀ ≤ hi)
    (hend : lo ≤ symEnd h₀ run ∧ symEnd h₀ run ≤ hi)
    (hnd : (symStepPairs h₀ q₀ run).Nodup)
    (hlt : ∀ p ∈ symStepPairs h₀ q₀ run, p.2 < 102) :
    (run.length : ℤ) ≤ ((hi - lo).toNat : ℤ) + 102 := by
  rcases d with _ | _ | _
  · have hb := symSingleDir_length_le_of_window h₀ run lo hi (Or.inr hall) hstart hend
    omega
  · have hb := symSingleDir_length_le_of_window h₀ run lo hi (Or.inl hall) hstart hend
    omega
  · have hb := symAllS_length_le h₀ q₀ run hall hnd hlt
    omega

/-- [M4b-3b-δ-3] **段长装配**：段长 ≤ 扫掠数 · (窗口 + 102)。 -/
theorem symSteps_length_le_of_runs (lo hi : ℤ) (π : List SymStep) :
    ∀ (h : ℤ) (q : ℕ),
      (∀ p ∈ symPositions h π, lo ≤ p ∧ p ≤ hi) →
      (lo ≤ symEnd h π ∧ symEnd h π ≤ hi) →
      (∀ p ∈ symStepPairs h q π, p.2 < 102) →
      (symStepPairs h q π).Nodup →
      (π.length : ℤ) ≤ ((symRunsOf π).length : ℤ) * (((hi - lo).toNat : ℤ) + 102) := by
  induction π using symRunsOf.induct with
  | case1 =>
      intro h q _ _ _ _
      rw [symRunsOf.eq_1]
      simp
  | case2 st rest ih =>
      intro h q hpos hend hlt hnd
      have hsplit : (st :: rest)
          = (st :: symTakeDir st.result.moveDir rest) ++ symDropDir st.result.moveDir rest := by
        rw [List.cons_append, symTakeDir_append_symDropDir]
      have hpairs : symStepPairs h q (st :: rest)
          = symStepPairs h q (st :: symTakeDir st.result.moveDir rest)
            ++ symStepPairs (symEnd h (st :: symTakeDir st.result.moveDir rest))
                 (symEndState q (st :: symTakeDir st.result.moveDir rest))
                 (symDropDir st.result.moveDir rest) := by
        rw [hsplit, symStepPairs_append]
      have hpos_split : symPositions h (st :: rest)
          = symPositions h (st :: symTakeDir st.result.moveDir rest)
            ++ symPositions (symEnd h (st :: symTakeDir st.result.moveDir rest))
                 (symDropDir st.result.moveDir rest) := by
        rw [hsplit, symPositions_append]
      have hpos_run : ∀ p ∈ symPositions h (st :: symTakeDir st.result.moveDir rest),
          lo ≤ p ∧ p ≤ hi := by
        intro p hp
        exact hpos p (by rw [hpos_split]; exact List.mem_append.mpr (Or.inl hp))
      have hpos_rst : ∀ p ∈ symPositions (symEnd h (st :: symTakeDir st.result.moveDir rest))
          (symDropDir st.result.moveDir rest), lo ≤ p ∧ p ≤ hi := by
        intro p hp
        exact hpos p (by rw [hpos_split]; exact List.mem_append.mpr (Or.inr hp))
      have hstart : lo ≤ h ∧ h ≤ hi := by
        have : h ∈ symPositions h (st :: symTakeDir st.result.moveDir rest) := by simp [symPositions]
        exact hpos_run h this
      have hend_run : lo ≤ symEnd h (st :: symTakeDir st.result.moveDir rest)
          ∧ symEnd h (st :: symTakeDir st.result.moveDir rest) ≤ hi := by
        by_cases hnil : symDropDir st.result.moveDir rest = []
        · have he : symEnd h (st :: symTakeDir st.result.moveDir rest) = symEnd h (st :: rest) := by
            rw [hsplit, hnil, List.append_nil]
          rw [he]; exact hend
        · have hmem : symEnd h (st :: symTakeDir st.result.moveDir rest)
              ∈ symPositions (symEnd h (st :: symTakeDir st.result.moveDir rest))
                  (symDropDir st.result.moveDir rest) := by
            cases hd : symDropDir st.result.moveDir rest with
            | nil => exact absurd hd hnil
            | cons a b => simp [symPositions]
          exact hpos_rst _ hmem
      have hend_rst : lo ≤ symEnd (symEnd h (st :: symTakeDir st.result.moveDir rest))
            (symDropDir st.result.moveDir rest)
          ∧ symEnd (symEnd h (st :: symTakeDir st.result.moveDir rest))
            (symDropDir st.result.moveDir rest) ≤ hi := by
        have he : symEnd (symEnd h (st :: symTakeDir st.result.moveDir rest))
              (symDropDir st.result.moveDir rest) = symEnd h (st :: rest) := by
          rw [← symEnd_append, ← hsplit]
        rw [he]; exact hend
      have hnd_run : (symStepPairs h q (st :: symTakeDir st.result.moveDir rest)).Nodup := by
        have h2 := hnd; rw [hpairs] at h2; exact (List.nodup_append.mp h2).1
      have hnd_rst : (symStepPairs (symEnd h (st :: symTakeDir st.result.moveDir rest))
            (symEndState q (st :: symTakeDir st.result.moveDir rest))
            (symDropDir st.result.moveDir rest)).Nodup := by
        have h2 := hnd; rw [hpairs] at h2; exact (List.nodup_append.mp h2).2.1
      have hlt_run : ∀ p ∈ symStepPairs h q (st :: symTakeDir st.result.moveDir rest),
          p.2 < 102 := by
        intro p hp
        exact hlt p (by rw [hpairs]; exact List.mem_append.mpr (Or.inl hp))
      have hlt_rst : ∀ p ∈ symStepPairs (symEnd h (st :: symTakeDir st.result.moveDir rest))
            (symEndState q (st :: symTakeDir st.result.moveDir rest))
            (symDropDir st.result.moveDir rest), p.2 < 102 := by
        intro p hp
        exact hlt p (by rw [hpairs]; exact List.mem_append.mpr (Or.inr hp))
      have hall : ∀ s ∈ st :: symTakeDir st.result.moveDir rest,
          s.result.moveDir = st.result.moveDir := by
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs'
        · rfl
        · exact symTakeDir_all st.result.moveDir rest s hs'
      have hrun_bound := symRun_length_le h q (st :: symTakeDir st.result.moveDir rest)
        st.result.moveDir lo hi hall hstart hend_run hnd_run hlt_run
      have hih := ih (symEnd h (st :: symTakeDir st.result.moveDir rest))
        (symEndState q (st :: symTakeDir st.result.moveDir rest))
        hpos_rst hend_rst hlt_rst hnd_rst
      have hlen : ((st :: rest).length : ℤ)
          = ((st :: symTakeDir st.result.moveDir rest).length : ℤ)
            + ((symDropDir st.result.moveDir rest).length : ℤ) := by
        rw [hsplit, List.length_append]; push_cast; ring
      have hruns : ((symRunsOf (st :: rest)).length : ℤ)
          = 1 + ((symRunsOf (symDropDir st.result.moveDir rest)).length : ℤ) := by
        rw [symRunsOf.eq_2, List.length_cons]; push_cast; ring
      have hW : (0 : ℤ) ≤ ((hi - lo).toNat : ℤ) + 102 := by
        have : (0 : ℤ) ≤ ((hi - lo).toNat : ℤ) := Int.natCast_nonneg _
        omega
      rw [hlen, hruns]
      nlinarith [hrun_bound, hih, hW]

/-- [M4b-3b-δ-3] **段长 ≤ (转向数 + 1) · (窗口 + 102)**。 -/
theorem symSteps_length_le_of_turnCount (lo hi : ℤ) (π : List SymStep) (h : ℤ) (q : ℕ)
    (hpos : ∀ p ∈ symPositions h π, lo ≤ p ∧ p ≤ hi)
    (hend : lo ≤ symEnd h π ∧ symEnd h π ≤ hi)
    (hlt : ∀ p ∈ symStepPairs h q π, p.2 < 102)
    (hnd : (symStepPairs h q π).Nodup) :
    (π.length : ℤ) ≤ ((symTurnCount (π.map (fun st => st.result.moveDir)) : ℤ) + 1)
      * (((hi - lo).toNat : ℤ) + 102) := by
  have h1 := symSteps_length_le_of_runs lo hi π h q hpos hend hlt hnd
  have h2 : ((symRunsOf π).length : ℤ)
      ≤ (symTurnCount (π.map (fun st => st.result.moveDir)) : ℤ) + 1 := by
    exact_mod_cast symRunsOf_length_le_turnCount_add_one π
  have hW : (0 : ℤ) ≤ ((hi - lo).toNat : ℤ) + 102 := by
    have : (0 : ℤ) ≤ ((hi - lo).toNat : ℤ) := Int.natCast_nonneg _
    omega
  exact le_trans h1 (mul_le_mul_of_nonneg_right h2 hW)

-- ===== δ-4（H_triple 三元组路线）已肃清（2026-09-13，用户令：作废方案残余不留存；原块见 git 史）=====
-- ===== δ-5② BEGIN =====
open Mp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- [δ-5②] `q` 读 `k` 时的 S 后继状态集(排除 101 ⇒ 结果仍可延拓)。 -/
def symSOut (q : ℕ) (k : Sym) : Finset ℕ :=
  (((VerifierSym.transition (q, k)).filter (fun r => r.moveDir = Dir.S ∧ r.nextState ≠ 101)).image
    (fun r => r.nextState))

/-- [δ-5②] 三层 S 链的终点集(起点非 100)。 -/
def symS2Paths : Finset ℕ :=
  ((Finset.range 102).filter (fun a => a ≠ 100)).biUnion (fun a =>
    (Finset.univ : Finset Sym).biUnion (fun k1 =>
      (symSOut a k1).biUnion (fun b =>
        (Finset.univ : Finset Sym).biUnion (fun k2 =>
          (symSOut b k2).biUnion (fun c =>
            (Finset.univ : Finset Sym).biUnion (fun k3 => symSOut c k3))))))

/-- [δ-5②] **表事实**:非 100 起点上不存在三层 S 链。 -/
theorem symS2Paths_eq_empty : symS2Paths = ∅ := by decide

/-- [δ-5②] 可用形式:S 段长 ≤ 2(不存在连续三步 S)。 -/
theorem symS_no_three {a b c d : ℕ} {k1 k2 k3 : Sym} (ha : a < 102) (hne : a ≠ 100)
    (hb : b ∈ symSOut a k1) (hc : c ∈ symSOut b k2) (hd : d ∈ symSOut c k3) : False := by
  have h0 : d ∈ symS2Paths := by
    simp only [symS2Paths, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range,
      Finset.mem_univ, true_and, and_true]
    exact ⟨a, ⟨ha, hne⟩, k1, b, hb, k2, c, hc, k3, hd⟩
  have h1 : d ∉ symS2Paths := by rw [symS2Paths_eq_empty]; simp
  exact h1 h0


-- ===== δ-5② END =====
-- ===== δ-5④ BEGIN =====
open Mp
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- [δ-5④-1] 表事实的可用后果:不存在三层 S 转移链(非 100 起点、结果可延拓)。 -/
theorem symS_no_three_tab {a : ℕ} (ha : a < 102) (hne : a ≠ 100) {k1 k2 k3 : Sym}
    {r1 r2 r3 : SymTransResult}
    (h1 : r1 ∈ VerifierSym.transition (a, k1)) (hd1 : r1.moveDir = Dir.S) (hn1 : r1.nextState ≠ 101)
    (h2 : r2 ∈ VerifierSym.transition (r1.nextState, k2)) (hd2 : r2.moveDir = Dir.S)
    (hn2 : r2.nextState ≠ 101)
    (h3 : r3 ∈ VerifierSym.transition (r2.nextState, k3)) (hd3 : r3.moveDir = Dir.S)
    (hn3 : r3.nextState ≠ 101) :
    False := by
  have m1 : r1.nextState ∈ Mp.symSOut a k1 := by
    simp only [Mp.symSOut, Finset.mem_image, Finset.mem_filter]
    exact ⟨r1, ⟨h1, hd1, hn1⟩, rfl⟩
  have m2 : r2.nextState ∈ Mp.symSOut r1.nextState k2 := by
    simp only [Mp.symSOut, Finset.mem_image, Finset.mem_filter]
    exact ⟨r2, ⟨h2, hd2, hn2⟩, rfl⟩
  have m3 : r3.nextState ∈ Mp.symSOut r2.nextState k3 := by
    simp only [Mp.symSOut, Finset.mem_image, Finset.mem_filter]
    exact ⟨r3, ⟨h3, hd3, hn3⟩, rfl⟩
  exact Mp.symS_no_three ha hne m1 m2 m3

/-- [δ-5④-2] 合法 S 步列:预态条件 + 逐位相接 + 转移表成员(装配变体用)。 -/
def SymSOk : ℕ → List SymStep → Prop
  | _, [] => True
  | q, st :: rest =>
      q < 102 ∧ q ≠ 100 ∧ st.fromState = q ∧ st.result.moveDir = Dir.S ∧
        st.result.nextState ≠ 101 ∧ st.result ∈ VerifierSym.transition (q, st.readSym) ∧
        SymSOk st.result.nextState rest

/-- [δ-5④-2] **S 段 ≤ 2**(免 nodup,由 ② 的后果给出)。 -/
theorem symS_run_le_two : ∀ (q : ℕ) (run : List SymStep), SymSOk q run → run.length ≤ 2 := by
  intro q run
  induction run generalizing q with
  | nil => intro _; simp
  | cons st rest ih =>
      intro h
      obtain ⟨hq102, hq100, hf, hd, hn, htr, hrest⟩ := h
      rcases rest with _ | ⟨st₂, rest₂⟩
      · simp
      · obtain ⟨_, _, hf₂, hd₂, hn₂, htr₂, hrest₂⟩ := hrest
        rcases rest₂ with _ | ⟨st₃, rest₃⟩
        · simp
        · obtain ⟨_, _, _, hd₃, hn₃, htr₃, _⟩ := hrest₂
          exact absurd
            (symS_no_three_tab hq102 hq100 (k1 := st.readSym) (k2 := st₂.readSym) (k3 := st₃.readSym)
              htr hd hn htr₂ hd₂ hn₂ htr₃ hd₃ hn₃) (by simp)

-- ===== δ-5④ END =====
-- ===== δ-5④b BEGIN =====
open Mp
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- [δ-5④-3a] L/R 段段长界(**免 nodup**,纯位置窗口)。 -/
theorem symRun_LR_le (h₀ : ℤ) (run : List SymStep) (d : Dir) (lo hi : ℤ)
    (hd : d = Dir.L ∨ d = Dir.R)
    (hall : ∀ s ∈ run, s.result.moveDir = d)
    (hstart : lo ≤ h₀ ∧ h₀ ≤ hi)
    (hend : lo ≤ symEnd h₀ run ∧ symEnd h₀ run ≤ hi) :
    (run.length : ℤ) ≤ ((hi - lo).toNat : ℤ) + 102 := by
  rcases hd with h | h
  · subst h
    have hh := symSingleDir_length_le_of_window h₀ run lo hi (Or.inr hall) hstart hend
    omega
  · subst h
    have hh := symSingleDir_length_le_of_window h₀ run lo hi (Or.inl hall) hstart hend
    omega

/-- [δ-5④-3b] S 段段长界(**免 nodup**,由 S 段 ≤ 2)。 -/
theorem symRun_S_le (h₀ : ℤ) (q₀ : ℕ) (run : List SymStep) (lo hi : ℤ)
    (hsok : SymSOk q₀ run) :
    (run.length : ℤ) ≤ ((hi - lo).toNat : ℤ) + 102 := by
  have h2 : run.length ≤ 2 := symS_run_le_two q₀ run hsok
  have h3 : (run.length : ℤ) ≤ 2 := by exact_mod_cast h2
  have h0 : (0 : ℤ) ≤ ((hi - lo).toNat : ℤ) := Int.natCast_nonneg _
  omega

-- ===== δ-5④b END =====
-- ===== δ-5④-4 BEGIN =====
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- [δ-5④-4] 装配变体:逐段求和,**不需要全局 Nodup**;只需
(窗口,含终点) + ①步前非接受 + (每个 S 段)合法 S 步列。 -/
theorem symSteps_length_le_of_runs_free (lo hi : ℤ) (π : List SymStep) :
    ∀ (h : ℤ) (q : ℕ),
      (∀ p ∈ symPositions h π ++ [symEnd h π], lo ≤ p ∧ p ≤ hi) →
      (∀ p ∈ symStepPairs h q π, p.2 < 102 ∧ p.2 ≠ 100) →
      (∀ seg ∈ symRunsOf π, (∀ st ∈ seg, st.result.moveDir = Dir.S) →
        ∃ q' : ℕ, SymSOk q' seg) →
      (π.length : ℤ) ≤ ((symRunsOf π).length : ℤ) * (((hi - lo).toNat : ℤ) + 102) := by
  induction π using symRunsOf.induct with
  | case1 =>
      intro h q _ _ _
      rw [symRunsOf.eq_1]
      simp
  | case2 st rest ih =>
      intro h q hwin h102 hsokS
      have hun : symRunsOf (st :: rest) =
          (st :: symTakeDir st.result.moveDir rest)
            :: symRunsOf (symDropDir st.result.moveDir rest) := by
        rw [symRunsOf.eq_2]
      have hsplit : (st :: symTakeDir st.result.moveDir rest)
          ++ symDropDir st.result.moveDir rest = st :: rest := by
        rw [List.cons_append, symTakeDir_append_symDropDir]
      have hsp : symPositions h (st :: rest) ++ [symEnd h (st :: rest)] =
          symPositions h (st :: symTakeDir st.result.moveDir rest)
            ++ (symPositions (symEnd h (st :: symTakeDir st.result.moveDir rest))
                  (symDropDir st.result.moveDir rest)
                ++ [symEnd (symEnd h (st :: symTakeDir st.result.moveDir rest))
                      (symDropDir st.result.moveDir rest)]) := by
        conv_lhs => rw [← hsplit]
        rw [symPositions_append, symEnd_append, List.append_assoc]
      have hsp2 : symStepPairs h q (st :: rest) =
          symStepPairs h q (st :: symTakeDir st.result.moveDir rest)
            ++ symStepPairs (symEnd h (st :: symTakeDir st.result.moveDir rest))
                (symEndState q (st :: symTakeDir st.result.moveDir rest))
                (symDropDir st.result.moveDir rest) := by
        conv_lhs => rw [← hsplit]
        rw [symStepPairs_append]
      -- 首段方向恒定
      have hd_all : ∀ s ∈ (st :: symTakeDir st.result.moveDir rest),
          s.result.moveDir = st.result.moveDir := by
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs'
        · rfl
        · exact symTakeDir_all _ _ s hs'
      -- 首段起点/终点落在窗口内
      have hstart : lo ≤ h ∧ h ≤ hi := by
        have hm : h ∈ symPositions h (st :: rest) ++ [symEnd h (st :: rest)] :=
          List.mem_append.mpr (Or.inl (by simp [symPositions]))
        exact hwin h hm
      have hend : lo ≤ symEnd h (st :: symTakeDir st.result.moveDir rest)
          ∧ symEnd h (st :: symTakeDir st.result.moveDir rest) ≤ hi := by
        rcases hs : symDropDir st.result.moveDir rest with _ | ⟨st₂, rest₂⟩
        · have he : symEnd h (st :: symTakeDir st.result.moveDir rest) = symEnd h (st :: rest) := by
            rw [← hsplit]
            simp [hs, symEnd_append]
          have hm : symEnd h (st :: rest)
              ∈ symPositions h (st :: rest) ++ [symEnd h (st :: rest)] :=
            List.mem_append.mpr (Or.inr (List.mem_singleton_self _))
          rw [he]
          exact hwin _ hm
        · have hm1 : symEnd h (st :: symTakeDir st.result.moveDir rest)
              ∈ symPositions (symEnd h (st :: symTakeDir st.result.moveDir rest))
                  (st₂ :: rest₂) := by
            simp [symPositions]
          have hm : symEnd h (st :: symTakeDir st.result.moveDir rest)
              ∈ symPositions h (st :: rest) ++ [symEnd h (st :: rest)] := by
            rw [hsp]
            exact List.mem_append.mpr
              (Or.inr (List.mem_append.mpr (Or.inl (by rw [hs]; exact hm1))))
          exact hwin _ hm
      -- 首段长度界:S 走 ≤2 / L·R 走窗口
      have hseg_le : ((st :: symTakeDir st.result.moveDir rest).length : ℤ)
          ≤ ((hi - lo).toNat : ℤ) + 102 := by
        have hmem_seg : (st :: symTakeDir st.result.moveDir rest) ∈ symRunsOf (st :: rest) := by
          rw [hun]; exact List.mem_cons_self
        by_cases hS : st.result.moveDir = Dir.S
        · have hsegS : ∀ s ∈ (st :: symTakeDir st.result.moveDir rest),
              s.result.moveDir = Dir.S := by
            intro s hs; rw [hd_all s hs, hS]
          obtain ⟨q', hq'⟩ := hsokS _ hmem_seg hsegS
          exact symRun_S_le h q' _ lo hi hq'
        · have hLR : st.result.moveDir = Dir.L ∨ st.result.moveDir = Dir.R := by
            cases hmv : st.result.moveDir with
            | L => exact Or.inl rfl
            | R => exact Or.inr rfl
            | S =>
                rw [hmv] at hS
                exact absurd rfl hS
          exact symRun_LR_le h _ _ lo hi hLR hd_all hstart hend
      -- 尾段:归纳假设
      have hsok_tail : ∀ seg' ∈ symRunsOf (symDropDir st.result.moveDir rest),
          (∀ s ∈ seg', s.result.moveDir = Dir.S) → ∃ q', SymSOk q' seg' := by
        intro seg' hmem hs
        exact hsokS seg' (by rw [hun]; exact List.mem_cons_of_mem _ hmem) hs
      have hwin_tail : ∀ p ∈ symPositions (symEnd h (st :: symTakeDir st.result.moveDir rest))
            (symDropDir st.result.moveDir rest)
          ++ [symEnd (symEnd h (st :: symTakeDir st.result.moveDir rest))
                (symDropDir st.result.moveDir rest)], lo ≤ p ∧ p ≤ hi := by
        intro p hp
        refine hwin p ?_
        rw [hsp]
        exact List.mem_append.mpr (Or.inr hp)
      have h102_tail : ∀ p ∈ symStepPairs (symEnd h (st :: symTakeDir st.result.moveDir rest))
            (symEndState q (st :: symTakeDir st.result.moveDir rest))
            (symDropDir st.result.moveDir rest), p.2 < 102 ∧ p.2 ≠ 100 := by
        intro p hp
        refine h102 p ?_
        rw [hsp2]
        exact List.mem_append.mpr (Or.inr hp)
      have htail := ih (symEnd h (st :: symTakeDir st.result.moveDir rest))
        (symEndState q (st :: symTakeDir st.result.moveDir rest))
        hwin_tail h102_tail hsok_tail
      -- 算术合拢
      have hlen : (st :: rest).length = (st :: symTakeDir st.result.moveDir rest).length
          + (symDropDir st.result.moveDir rest).length := by
        rw [← hsplit]
        simp only [List.length_append, List.length_cons]
      have hW : (0 : ℤ) < ((hi - lo).toNat : ℤ) + 102 := by
        have h0 : (0 : ℤ) ≤ ((hi - lo).toNat : ℤ) := Int.natCast_nonneg _
        omega
      rw [hun, hlen]
      simp only [List.length_cons] at hseg_le ⊢
      push_cast at hseg_le ⊢
      nlinarith [hseg_le, htail, hW]

-- ===== δ-5④-4 END =====
-- ===== δ-6 BEGIN =====
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- [⑤a] 自由版转向计数装配:段长 ≤ (转向数+1)·W(**免全局 Nodup**)。 -/
theorem symSteps_length_le_of_turnCount_free (lo hi : ℤ) (π : List SymStep) (h : ℤ) (q : ℕ)
    (hwin : ∀ p ∈ symPositions h π ++ [symEnd h π], lo ≤ p ∧ p ≤ hi)
    (h102 : ∀ p ∈ symStepPairs h q π, p.2 < 102 ∧ p.2 ≠ 100)
    (hsokS : ∀ seg ∈ symRunsOf π, (∀ st ∈ seg, st.result.moveDir = Dir.S) →
      ∃ q', SymSOk q' seg) :
    (π.length : ℤ) ≤ ((symTurnCount (π.map (fun st => st.result.moveDir)) : ℤ) + 1)
      * (((hi - lo).toNat : ℤ) + 102) := by
  have h1 := symSteps_length_le_of_runs_free lo hi π h q hwin h102 hsokS
  have h2 : ((symRunsOf π).length : ℤ)
      ≤ (symTurnCount (π.map (fun st => st.result.moveDir)) : ℤ) + 1 := by
    exact_mod_cast symRunsOf_length_le_turnCount_add_one π
  have hW : (0 : ℤ) ≤ ((hi - lo).toNat : ℤ) + 102 := by
    have : (0 : ℤ) ≤ ((hi - lo).toNat : ℤ) := Int.natCast_nonneg _
    omega
  exact le_trans h1 (mul_le_mul_of_nonneg_right h2 hW)

-- ===== δ-6 END =====
-- ===== δ-7 BEGIN =====
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- [δ-7a] 装配变体(纯长度版):逐段求和,**不需要全局 Nodup**,S 段长度界由前提交付。 -/
theorem symSteps_length_le_of_runs_freeS (lo hi : ℤ) (π : List SymStep) :
    ∀ (h : ℤ) (q : ℕ),
      (∀ p ∈ symPositions h π ++ [symEnd h π], lo ≤ p ∧ p ≤ hi) →
      (∀ p ∈ symStepPairs h q π, p.2 < 102 ∧ p.2 ≠ 100) →
      (∀ seg ∈ symRunsOf π, (∀ st ∈ seg, st.result.moveDir = Dir.S) → seg.length ≤ 2) →
      (π.length : ℤ) ≤ ((symRunsOf π).length : ℤ) * (((hi - lo).toNat : ℤ) + 102) := by
  induction π using symRunsOf.induct with
  | case1 =>
      intro h q _ _ _
      rw [symRunsOf.eq_1]
      simp
  | case2 st rest ih =>
      intro h q hwin h102 hSlen
      have hun : symRunsOf (st :: rest) =
          (st :: symTakeDir st.result.moveDir rest)
            :: symRunsOf (symDropDir st.result.moveDir rest) := by
        rw [symRunsOf.eq_2]
      have hsplit : (st :: symTakeDir st.result.moveDir rest)
          ++ symDropDir st.result.moveDir rest = st :: rest := by
        rw [List.cons_append, symTakeDir_append_symDropDir]
      have hsp : symPositions h (st :: rest) ++ [symEnd h (st :: rest)] =
          symPositions h (st :: symTakeDir st.result.moveDir rest)
            ++ (symPositions (symEnd h (st :: symTakeDir st.result.moveDir rest))
                  (symDropDir st.result.moveDir rest)
                ++ [symEnd (symEnd h (st :: symTakeDir st.result.moveDir rest))
                      (symDropDir st.result.moveDir rest)]) := by
        conv_lhs => rw [← hsplit]
        rw [symPositions_append, symEnd_append, List.append_assoc]
      have hsp2 : symStepPairs h q (st :: rest) =
          symStepPairs h q (st :: symTakeDir st.result.moveDir rest)
            ++ symStepPairs (symEnd h (st :: symTakeDir st.result.moveDir rest))
                (symEndState q (st :: symTakeDir st.result.moveDir rest))
                (symDropDir st.result.moveDir rest) := by
        conv_lhs => rw [← hsplit]
        rw [symStepPairs_append]
      have hd_all : ∀ s ∈ (st :: symTakeDir st.result.moveDir rest),
          s.result.moveDir = st.result.moveDir := by
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs'
        · rfl
        · exact symTakeDir_all _ _ s hs'
      have hstart : lo ≤ h ∧ h ≤ hi := by
        have hm : h ∈ symPositions h (st :: rest) ++ [symEnd h (st :: rest)] :=
          List.mem_append.mpr (Or.inl (by simp [symPositions]))
        exact hwin h hm
      have hend : lo ≤ symEnd h (st :: symTakeDir st.result.moveDir rest)
          ∧ symEnd h (st :: symTakeDir st.result.moveDir rest) ≤ hi := by
        rcases hs : symDropDir st.result.moveDir rest with _ | ⟨st₂, rest₂⟩
        · have he : symEnd h (st :: symTakeDir st.result.moveDir rest) = symEnd h (st :: rest) := by
            rw [← hsplit]
            simp [hs, symEnd_append]
          have hm : symEnd h (st :: rest)
              ∈ symPositions h (st :: rest) ++ [symEnd h (st :: rest)] :=
            List.mem_append.mpr (Or.inr (List.mem_singleton_self _))
          rw [he]
          exact hwin _ hm
        · have hm1 : symEnd h (st :: symTakeDir st.result.moveDir rest)
              ∈ symPositions (symEnd h (st :: symTakeDir st.result.moveDir rest))
                  (st₂ :: rest₂) := by
            simp [symPositions]
          have hm : symEnd h (st :: symTakeDir st.result.moveDir rest)
              ∈ symPositions h (st :: rest) ++ [symEnd h (st :: rest)] := by
            rw [hsp]
            exact List.mem_append.mpr
              (Or.inr (List.mem_append.mpr (Or.inl (by rw [hs]; exact hm1))))
          exact hwin _ hm
      have hseg_le : ((st :: symTakeDir st.result.moveDir rest).length : ℤ)
          ≤ ((hi - lo).toNat : ℤ) + 102 := by
        have hmem_seg : (st :: symTakeDir st.result.moveDir rest) ∈ symRunsOf (st :: rest) := by
          rw [hun]; exact List.mem_cons_self
        by_cases hS : st.result.moveDir = Dir.S
        · have hsegS : ∀ s ∈ (st :: symTakeDir st.result.moveDir rest),
              s.result.moveDir = Dir.S := by
            intro s hs; rw [hd_all s hs, hS]
          have h2 : (st :: symTakeDir st.result.moveDir rest).length ≤ 2 :=
            hSlen _ hmem_seg hsegS
          have h2z : ((st :: symTakeDir st.result.moveDir rest).length : ℤ) ≤ 2 := by
            exact_mod_cast h2
          have h0 : (0 : ℤ) ≤ ((hi - lo).toNat : ℤ) := Int.natCast_nonneg _
          omega
        · have hLR : st.result.moveDir = Dir.L ∨ st.result.moveDir = Dir.R := by
            cases hmv : st.result.moveDir with
            | L => exact Or.inl rfl
            | R => exact Or.inr rfl
            | S =>
                rw [hmv] at hS
                exact absurd rfl hS
          exact symRun_LR_le h _ _ lo hi hLR hd_all hstart hend
      have hSlen_tail : ∀ seg' ∈ symRunsOf (symDropDir st.result.moveDir rest),
          (∀ s ∈ seg', s.result.moveDir = Dir.S) → seg'.length ≤ 2 := by
        intro seg' hmem hs
        exact hSlen seg' (by rw [hun]; exact List.mem_cons_of_mem _ hmem) hs
      have hwin_tail : ∀ p ∈ symPositions (symEnd h (st :: symTakeDir st.result.moveDir rest))
            (symDropDir st.result.moveDir rest)
          ++ [symEnd (symEnd h (st :: symTakeDir st.result.moveDir rest))
                (symDropDir st.result.moveDir rest)], lo ≤ p ∧ p ≤ hi := by
        intro p hp
        refine hwin p ?_
        rw [hsp]
        exact List.mem_append.mpr (Or.inr hp)
      have h102_tail : ∀ p ∈ symStepPairs (symEnd h (st :: symTakeDir st.result.moveDir rest))
            (symEndState q (st :: symTakeDir st.result.moveDir rest))
            (symDropDir st.result.moveDir rest), p.2 < 102 ∧ p.2 ≠ 100 := by
        intro p hp
        refine h102 p ?_
        rw [hsp2]
        exact List.mem_append.mpr (Or.inr hp)
      have htail := ih (symEnd h (st :: symTakeDir st.result.moveDir rest))
        (symEndState q (st :: symTakeDir st.result.moveDir rest))
        hwin_tail h102_tail hSlen_tail
      have hlen : (st :: rest).length = (st :: symTakeDir st.result.moveDir rest).length
          + (symDropDir st.result.moveDir rest).length := by
        rw [← hsplit]
        simp only [List.length_append, List.length_cons]
      have hW : (0 : ℤ) < ((hi - lo).toNat : ℤ) + 102 := by
        have h0 : (0 : ℤ) ≤ ((hi - lo).toNat : ℤ) := Int.natCast_nonneg _
        omega
      rw [hun, hlen]
      simp only [List.length_cons] at hseg_le ⊢
      push_cast at hseg_le ⊢
      nlinarith [hseg_le, htail, hW]

/-- [δ-7b] 纯长度版转向计数装配:段长 ≤ (转向数+1)·W(**免全局 Nodup**)。 -/
theorem symSteps_length_le_of_turnCount_freeS (lo hi : ℤ) (π : List SymStep) (h : ℤ) (q : ℕ)
    (hwin : ∀ p ∈ symPositions h π ++ [symEnd h π], lo ≤ p ∧ p ≤ hi)
    (h102 : ∀ p ∈ symStepPairs h q π, p.2 < 102 ∧ p.2 ≠ 100)
    (hSlen : ∀ seg ∈ symRunsOf π, (∀ st ∈ seg, st.result.moveDir = Dir.S) → seg.length ≤ 2) :
    (π.length : ℤ) ≤ ((symTurnCount (π.map (fun st => st.result.moveDir)) : ℤ) + 1)
      * (((hi - lo).toNat : ℤ) + 102) := by
  have h1 := symSteps_length_le_of_runs_freeS lo hi π h q hwin h102 hSlen
  have h2 : ((symRunsOf π).length : ℤ)
      ≤ (symTurnCount (π.map (fun st => st.result.moveDir)) : ℤ) + 1 := by
    exact_mod_cast symRunsOf_length_le_turnCount_add_one π
  have hW : (0 : ℤ) ≤ ((hi - lo).toNat : ℤ) + 102 := by
    have : (0 : ℤ) ≤ ((hi - lo).toNat : ℤ) := Int.natCast_nonneg _
    omega
  exact le_trans h1 (mul_le_mul_of_nonneg_right h2 hW)

-- ===== δ-7 END =====
-- ===== δ-8 BEGIN =====
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- 步列链：相邻两步相接(`st'` 起点态 = `st` 终点态)。 -/
def SymChained : List SymStep → Prop
  | [] => True
  | [_] => True
  | st :: st' :: rest => st'.fromState = st.result.nextState ∧ SymChained (st' :: rest)

/-- [δ-8a] 逐步事实 + 链 ⇒ `SymSOk`(起点 = 首步 `fromState`)。 -/
theorem SymSOk_of_chained_cons (st : SymStep) (rest : List SymStep)
    (hch : SymChained (st :: rest))
    (hp : ∀ s ∈ st :: rest, s.fromState < 102 ∧ s.fromState ≠ 100)
    (hd : ∀ s ∈ st :: rest, s.result.moveDir = Dir.S)
    (hn : ∀ s ∈ st :: rest, s.result.nextState ≠ 101)
    (ht : ∀ s ∈ st :: rest, s.result ∈ VerifierSym.transition (s.fromState, s.readSym)) :
    SymSOk st.fromState (st :: rest) := by
  rcases rest with _ | ⟨st', rest'⟩
  · refine ⟨(hp st (by simp)).1, (hp st (by simp)).2, rfl, hd st (by simp),
      hn st (by simp), ht st (by simp), trivial⟩
  · simp only [SymChained] at hch
    have hlink : st'.fromState = st.result.nextState := hch.1
    have hchrest : SymChained (st' :: rest') := hch.2
    have hih : SymSOk st'.fromState (st' :: rest') :=
      SymSOk_of_chained_cons st' rest' hchrest
        (by intro s hs; exact hp s (List.mem_cons_of_mem _ hs))
        (by intro s hs; exact hd s (List.mem_cons_of_mem _ hs))
        (by intro s hs; exact hn s (List.mem_cons_of_mem _ hs))
        (by intro s hs; exact ht s (List.mem_cons_of_mem _ hs))
    refine ⟨(hp st (by simp)).1, (hp st (by simp)).2, rfl, hd st (by simp),
      hn st (by simp), ht st (by simp), by rw [← hlink]; exact hih⟩

/-- [δ-8b] **S 段 ≤ 2(逐步可派生版)**。 -/
theorem S_run_le_two_of_step_facts (seg : List SymStep)
    (hch : SymChained seg)
    (hp : ∀ s ∈ seg, s.fromState < 102 ∧ s.fromState ≠ 100)
    (hd : ∀ s ∈ seg, s.result.moveDir = Dir.S)
    (hn : ∀ s ∈ seg, s.result.nextState ≠ 101)
    (ht : ∀ s ∈ seg, s.result ∈ VerifierSym.transition (s.fromState, s.readSym)) :
    seg.length ≤ 2 := by
  rcases seg with _ | ⟨st, rest⟩
  · simp
  · exact symS_run_le_two _ _ (SymSOk_of_chained_cons st rest hch hp hd hn ht)

-- ===== δ-8 END =====
-- ===== δ-9 BEGIN =====
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- [δ-9a] 右侧因子继承链。 -/
theorem SymChained_append_right : ∀ (l r : List SymStep), SymChained (l ++ r) → SymChained r := by
  intro l
  induction l with
  | nil => intro r h; exact h
  | cons x t ih =>
      intro r h
      cases t with
      | nil =>
          cases r with
          | nil => exact trivial
          | cons y t' =>
              simp only [List.cons_append] at h
              exact h.2
      | cons y t' =>
          have h2 : SymChained ((y :: t') ++ r) := by
            simp only [SymChained, List.cons_append] at h
            exact h.2
          exact ih r h2

/-- [δ-9b] 左侧因子继承链。 -/
theorem SymChained_append_left : ∀ (l r : List SymStep), SymChained (l ++ r) → SymChained l := by
  intro l
  induction l with
  | nil => intro r _; exact trivial
  | cons x t ih =>
      intro r h
      cases t with
      | nil => exact trivial
      | cons y t' =>
          simp only [SymChained, List.cons_append] at h
          exact ⟨h.1, ih r h.2⟩

-- ===== δ-9 END =====
-- ===== δ-10 BEGIN =====
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- [δ-10a] 成员即连续块。 -/
theorem exists_append_of_mem_flatten : ∀ (L : List (List SymStep)) (s : List SymStep),
    s ∈ L → ∃ a b, L.flatten = a ++ s ++ b
  | [], s, h => by simp at h
  | l :: t, s, h => by
      rcases List.mem_cons.mp h with rfl | hmem
      · exact ⟨[], t.flatten, by simp⟩
      · obtain ⟨a, b, hab⟩ := exists_append_of_mem_flatten t s hmem
        exact ⟨l ++ a, b, by rw [List.flatten_cons, hab]; ac_rfl⟩

/-- [δ-10b] `symRunsOf` 的每个段都继承全局链。 -/
theorem SymChained_of_mem_symRunsOf (π : List SymStep) (hπ : SymChained π) :
    ∀ seg ∈ symRunsOf π, SymChained seg := by
  intro seg hmem
  obtain ⟨a, b, hab⟩ := exists_append_of_mem_flatten (symRunsOf π) seg hmem
  rw [symRunsOf_flatten] at hab
  have h' : SymChained (a ++ (seg ++ b)) := by
    rw [← List.append_assoc]
    exact hab ▸ hπ
  exact SymChained_append_left seg b (SymChained_append_right a (seg ++ b) h')

/-- [δ-10c] **hSlen 派生**：全 S 段 ≤ 2(前提 = 全局链 + 逐步事实)。 -/
theorem symAllS_seg_le_two (π : List SymStep)
    (hch : SymChained π)
    (hp : ∀ s ∈ π, s.fromState < 102 ∧ s.fromState ≠ 100)
    (hn : ∀ s ∈ π, s.result.nextState ≠ 101)
    (ht : ∀ s ∈ π, s.result ∈ VerifierSym.transition (s.fromState, s.readSym)) :
    ∀ seg ∈ symRunsOf π, (∀ s ∈ seg, s.result.moveDir = Dir.S) → seg.length ≤ 2 := by
  intro seg hmem hS
  have hsub : ∀ s ∈ seg, s ∈ π := by
    intro s hs
    have : s ∈ (symRunsOf π).flatten := List.mem_flatten.mpr ⟨seg, hmem, hs⟩
    rwa [symRunsOf_flatten] at this
  exact S_run_le_two_of_step_facts seg (SymChained_of_mem_symRunsOf π hch seg hmem)
    (by intro s hs; exact hp s (hsub s hs))
    hS
    (by intro s hs; exact hn s (hsub s hs))
    (by intro s hs; exact ht s (hsub s hs))

-- ===== δ-10 END =====
-- ===== δ-11 BEGIN =====
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- [δ-19-15] **免 `Nodup` 的转向预算版**（③ 长度界口径重述）。
    原 `hnd`/`htpos`/`htst` 中 `Nodup` 已实测为假 ⇒ 换成单一可满足前提
    「总转向数 ≤ 1632L」（实测：转向数 ≈ 2·标记读数，远小于 1632L）。结论形状不变。 -/
theorem symSteps_length_le_of_turnBudget_freeS (lo hi : ℤ) (π : List SymStep) (h : ℤ) (q : ℕ)
    (L : ℕ)
    (hturn : symTurnCount (π.map (fun st => st.result.moveDir)) ≤ 1632 * L)
    (hwin : ∀ p ∈ symPositions h π ++ [symEnd h π], lo ≤ p ∧ p ≤ hi)
    (h102 : ∀ p ∈ symStepPairs h q π, p.2 < 102 ∧ p.2 ≠ 100)
    (hSlen : ∀ seg ∈ symRunsOf π, (∀ st ∈ seg, st.result.moveDir = Dir.S) → seg.length ≤ 2) :
    (π.length : ℤ) ≤ ((L : ℤ) * 1632 + 1) * (((hi - lo).toNat : ℤ) + 102) := by
  have h1 := symSteps_length_le_of_turnCount_freeS lo hi π h q hwin h102 hSlen
  have hcast : ((1632 * L : ℕ) : ℤ) = (L : ℤ) * 1632 := by push_cast; ring
  have h2 : (symTurnCount (π.map (fun st => st.result.moveDir)) : ℤ) + 1
      ≤ (L : ℤ) * 1632 + 1 := by
    have htn : ((symTurnCount (π.map (fun st => st.result.moveDir)) : ℕ) : ℤ)
        ≤ ((1632 * L : ℕ) : ℤ) := by exact_mod_cast hturn
    rw [hcast] at htn
    omega
  have hW : (0 : ℤ) ≤ ((hi - lo).toNat : ℤ) + 102 := by
    have : (0 : ℤ) ≤ ((hi - lo).toNat : ℤ) := Int.natCast_nonneg _
    omega
  exact le_trans h1 (mul_le_mul_of_nonneg_right h2 hW)

/-- [δ-19-15] 转向预算版的运行事实包装（S 段长度前提自动放电，与 δ-11 同形）。 -/
theorem symSteps_length_le_of_run_facts_turnBudget (lo hi : ℤ) (π : List SymStep) (h : ℤ) (q : ℕ)
    (L : ℕ)
    (hturn : symTurnCount (π.map (fun st => st.result.moveDir)) ≤ 1632 * L)
    (hwin : ∀ p ∈ symPositions h π ++ [symEnd h π], lo ≤ p ∧ p ≤ hi)
    (h102 : ∀ p ∈ symStepPairs h q π, p.2 < 102 ∧ p.2 ≠ 100)
    (hch : SymChained π)
    (hp : ∀ s ∈ π, s.fromState < 102 ∧ s.fromState ≠ 100)
    (hn : ∀ s ∈ π, s.result.nextState ≠ 101)
    (ht : ∀ s ∈ π, s.result ∈ VerifierSym.transition (s.fromState, s.readSym)) :
    (π.length : ℤ) ≤ ((L : ℤ) * 1632 + 1) * (((hi - lo).toNat : ℤ) + 102) :=
  symSteps_length_le_of_turnBudget_freeS lo hi π h q L hturn hwin h102
    (symAllS_seg_le_two π hch hp hn ht)

-- ===== δ-19-15b BEGIN：转向数分段记账（把「每段转向 ≤ C」折算成「总量 ≤ (C+1)·#段」）=====

/-- [δ-19-15b] 转向数计入拼接：`symTurnCount (a ++ b) ≤ symTurnCount a + symTurnCount b + 1`。 -/
theorem symTurnCount_append_le (a b : List Dir) :
    symTurnCount (a ++ b) ≤ symTurnCount a + symTurnCount b + 1 := by
  induction a with
  | nil => simp [symTurnCount]
  | cons d rest ih =>
    cases rest with
    | nil =>
      cases b with
      | nil => simp [symTurnCount]
      | cons e es =>
        rw [List.singleton_append]
        by_cases h : d = e
        · subst h; rw [symTurnCount_cons_cons_self]; simp [symTurnCount]
        · rw [symTurnCount_cons_cons_ne h]; simp only [symTurnCount]; omega
    | cons e rest2 =>
      rw [List.cons_append, List.cons_append]
      have ih' : symTurnCount (e :: (rest2 ++ b)) ≤ symTurnCount (e :: rest2) + symTurnCount b + 1 := by
        rw [← List.cons_append]; exact ih
      by_cases h : d = e
      · subst h
        rw [symTurnCount_cons_cons_self d (rest2 ++ b), symTurnCount_cons_cons_self d rest2]
        omega
      · rw [symTurnCount_cons_cons_ne h (rest2 ++ b), symTurnCount_cons_cons_ne h rest2]
        omega

/-- [δ-19-15b] 转向数计入拍平。 -/
theorem symTurnCount_flatten_le (l : List (List Dir)) :
    symTurnCount l.flatten ≤ (l.map symTurnCount).sum + l.length := by
  induction l with
  | nil => simp [symTurnCount]
  | cons a rest ih =>
    rw [List.flatten_cons, List.map_cons, List.sum_cons, List.length_cons]
    have h1 := symTurnCount_append_le a rest.flatten
    omega

/-- [δ-19-15b] **分段记账**：总转向 ≤ Σ(段内转向) + #段。 -/
theorem symTurnCount_le_sum_segs (P : SymStep → Bool) (π : List SymStep) :
    symTurnCount (π.map (fun st => st.result.moveDir))
      ≤ ((segsByEvent P π).map (fun seg => symTurnCount (seg.map (fun st => st.result.moveDir)))).sum
        + (segsByEvent P π).length := by
  have hflat : (segsByEvent P π).flatten = π := segsByEvent_flatten P π
  have hmap : π.map (fun st => st.result.moveDir)
      = ((segsByEvent P π).map (fun seg => seg.map (fun st => st.result.moveDir))).flatten := by
    conv_lhs => rw [← hflat]
    rw [List.map_flatten]
  rw [hmap]
  have h2 := symTurnCount_flatten_le
    ((segsByEvent P π).map (fun seg => seg.map (fun st => st.result.moveDir)))
  rw [List.length_map] at h2
  rw [List.map_map] at h2
  exact h2

/-- [δ-19-15b] **每段 ≤ C ⇒ 总转向 ≤ (C+1)·#段**。 -/
theorem symTurnCount_le_mul_segs (P : SymStep → Bool) (C : ℕ) (π : List SymStep)
    (hseg : ∀ seg ∈ segsByEvent P π, symTurnCount (seg.map (fun st => st.result.moveDir)) ≤ C) :
    symTurnCount (π.map (fun st => st.result.moveDir)) ≤ (C + 1) * (segsByEvent P π).length := by
  have h1 := symTurnCount_le_sum_segs P π
  have h2 : ((segsByEvent P π).map
      (fun seg => symTurnCount (seg.map (fun st => st.result.moveDir)))).sum
      ≤ (segsByEvent P π).length * C := by
    have h3 := sum_le_length_mul (c := C)
      (fun x hx => by
        obtain ⟨seg, hseg_mem, rfl⟩ := List.mem_map.mp hx
        exact hseg seg hseg_mem)
    rw [List.length_map] at h3
    exact h3
  calc symTurnCount (π.map (fun st => st.result.moveDir))
      ≤ ((segsByEvent P π).map
          (fun seg => symTurnCount (seg.map (fun st => st.result.moveDir)))).sum
        + (segsByEvent P π).length := h1
    _ ≤ (segsByEvent P π).length * C + (segsByEvent P π).length := by omega
    _ = (C + 1) * (segsByEvent P π).length := by ring

/-- [δ-19-15b] **③ 转向轴·轮级组装**：每轮（`fromState = 4` 切分）转向 ≤ C
    ⇒ 总转向 ≤ (C+1)·(轮首数 + 1)。（与 `symSteps_length_le_of_rounds` 对称。） -/
theorem symTurnCount_le_of_rounds {π : List SymStep} {C : ℕ}
    (h : ∀ s ∈ segsByEvent symRoundHead π,
      symTurnCount (s.map (fun st => st.result.moveDir)) ≤ C) :
    symTurnCount (π.map (fun st => st.result.moveDir))
      ≤ (C + 1) * ((π.filter symRoundHead).length + 1) := by
  calc symTurnCount (π.map (fun st => st.result.moveDir))
      ≤ (C + 1) * (segsByEvent symRoundHead π).length :=
        symTurnCount_le_mul_segs symRoundHead C π h
    _ ≤ (C + 1) * ((π.filter symRoundHead).length + 1) :=
        Nat.mul_le_mul_left _ (segsByEvent_length_le symRoundHead π)

/-- [δ-19-15b] **③ 转向轴·标记读级组装**：相邻标记读之间转向 ≤ C
    ⇒ 总转向 ≤ (C+1)·(标记读数 + 1)。（与 `symSteps_length_le_of_markedReads` 对称。） -/
theorem symTurnCount_le_of_markedReads {π : List SymStep} {C : ℕ}
    (h : ∀ s ∈ segsByEvent symIsMarkedRead π,
      symTurnCount (s.map (fun st => st.result.moveDir)) ≤ C) :
    symTurnCount (π.map (fun st => st.result.moveDir))
      ≤ (C + 1) * ((π.filter symIsMarkedRead).length + 1) := by
  calc symTurnCount (π.map (fun st => st.result.moveDir))
      ≤ (C + 1) * (segsByEvent symIsMarkedRead π).length :=
        symTurnCount_le_mul_segs symIsMarkedRead C π h
    _ ≤ (C + 1) * ((π.filter symIsMarkedRead).length + 1) :=
        Nat.mul_le_mul_left _ (segsByEvent_length_le symIsMarkedRead π)

-- ===== δ-19-15b END =====
-- ===== δ-11 END =====
/-
  ==============================================================================
  [M4b-3b-δ-12] 位置表 ↔ 真实运行头位（T15 的 hwin 交付件）
  ------------------------------------------------------------------------------
  既有 `symSteps_headPos_eq`(sum 口径) 只给「终位 = 初位 + Σ方向」;
  本节把**位置表** `symPositions`/`symEnd` 接到真实 `SymSteps` 运行:
    · A-0 `symEnd_eq_headPos_sum`      : symEnd 与 sum 口径同一
    · A-1 `symPositions_length`        : 位置表长度 = 步数
    · A-2 `symEnd_take_eq_getD`        : 第 k 步前头位 = 位置表第 k 项
    · A-3 `exists_take_of_mem_symPositions` : 表中元素 = 某前缀头位
  用途: 由 ① A-1 的逐前缀头对应 `cfgcm.headPos = 4 * cfgsm.headPos`(÷4) 交付 T15 的 `hwin`。
  ==============================================================================
-/

/-- [M4b-3b-δ-12 A-0] `symEnd` = 初位 + 方向累加（与 `symSteps_headPos_eq` 同口径）。 -/
theorem symEnd_eq_headPos_sum (h0 : ℤ) (p : List SymStep) :
    symEnd h0 p = h0 + (p.map (fun st => st.result.moveDir.toInt)).sum := by
  induction p generalizing h0 with
  | nil => simp [symEnd]
  | cons st rest ih => simp [symEnd, ih]; ring

/-- [M4b-3b-δ-12 A-1] 位置表长度 = 步数。 -/
theorem symPositions_length (h0 : ℤ) (p : List SymStep) :
    (symPositions h0 p).length = p.length := by
  induction p generalizing h0 with
  | nil => simp [symPositions]
  | cons st rest ih => simp [symPositions, ih]

/-- [M4b-3b-δ-12 A-2] 第 k 步前头位 = 位置表第 k 项（`getD`）。 -/
theorem symEnd_take_eq_getD (h0 : ℤ) : ∀ (p : List SymStep) (k : ℕ), k ≤ p.length →
    symEnd h0 (p.take k) = (symPositions h0 p ++ [symEnd h0 p]).getD k 0
  | [], k, hk => by
      have hk0 : k = 0 := by simpa using hk
      subst hk0
      simp [symPositions, symEnd]
  | st :: rest, k, hk => by
      have hd : symEnd h0 (st :: rest) = symEnd (h0 + st.result.moveDir.toInt) rest := by
        simp [symEnd]
      cases k with
      | zero => simp [symPositions, symEnd]
      | succ k' =>
          have hk' : k' ≤ rest.length := by simpa using hk
          have hL : symEnd h0 ((st :: rest).take (k' + 1))
              = symEnd (h0 + st.result.moveDir.toInt) (rest.take k') := by
            simp [symEnd]
          rw [hL]
          simp only [symPositions, hd]
          exact symEnd_take_eq_getD (h0 + st.result.moveDir.toInt) rest k' hk'

/-- [M4b-3b-δ-12 A-3a] 列表成员都可由 `getD` 取到（带下标上界）。 -/
theorem exists_getD_eq_of_mem : ∀ (l : List ℤ) {q : ℤ}, q ∈ l →
    ∃ k, k < l.length ∧ l.getD k 0 = q
  | [], q, hq => by simp at hq
  | a :: l, q, hq => by
      rcases List.mem_cons.mp hq with hq | hq
      · exact ⟨ 0, by simp [hq]⟩
      · obtain ⟨ k, hk, hqk⟩ := exists_getD_eq_of_mem l hq
        exact ⟨ k + 1, by simpa using hk, by simpa using hqk⟩

/-- [M4b-3b-δ-12 A-3] 位置表中每个元素都是某个前缀运行的头位。 -/
theorem exists_take_of_mem_symPositions (h0 : ℤ) (p : List SymStep) {q : ℤ}
    (hq : q ∈ symPositions h0 p ++ [symEnd h0 p]) :
    ∃ k, k ≤ p.length ∧ q = symEnd h0 (p.take k) := by
  obtain ⟨ k, hk, hqk⟩ := exists_getD_eq_of_mem _ hq
  have hlen : (symPositions h0 p ++ [symEnd h0 p]).length = p.length + 1 := by
    simp [symPositions_length]
  have hk' : k ≤ p.length := by omega
  refine ⟨ k, hk', ?_⟩
  rw [← hqk, symEnd_take_eq_getD h0 p k hk']
/-
  ==============================================================================
  [M4b-3b-δ-13] hwin 交付层：逐前缀头位界 ⇒ 位置表窗口界
  ------------------------------------------------------------------------------
  T15 的 `hwin` 以位置表为口径，而 ① A-1 (`a1_cbtm_accept_path_prefix_bound`)
  只给「逐前缀的 **CBTM/Sym 头位对应**」。本节把两者接上:
    · δ-12 A-3 把表元素化为某前缀头位 `symEnd 0 (p.take k)`;
    · 既有 `symSteps_headPos_eq`(Σ口径) + δ-12 A-0 把「任一前缀运行的头位」与 `symEnd` 对齐
      ⇒ 只需逐前缀有一个运行头位落在 `[0, bound]` 即可。
  用途: 由 ① A-1 的 `cfgcm.headPos = 4 * cfgsm.headPos` 与 `0 ≤ cfgcm.headPos ≤ 4 · |wS|`
  给出 `bound = (encodeInstanceSym inst).length`（÷4）。
  ==============================================================================
-/

/-- [M4b-3b-δ-13] 若每个前缀运行的头位落在 `[0, bound]`，
则位置表全部元素（含终位）落在 `[0, bound]`。 -/
theorem hwin_of_prefix_head_facts (input : List Sym) {p : List SymStep} {bound : ℤ}
    (h : ∀ k ≤ p.length, ∃ cfgm : SymConfig,
        SymSteps VerifierSym.transition (symInitialConfig input) (p.take k) cfgm ∧
        0 ≤ cfgm.headPos ∧ cfgm.headPos ≤ bound) :
    ∀ q ∈ symPositions 0 p ++ [symEnd 0 p], 0 ≤ q ∧ q ≤ bound := by
  intro q hq
  obtain ⟨ k, hk, hqk⟩ := exists_take_of_mem_symPositions 0 p hq
  obtain ⟨ cfgm, hrun, hlo, hhi⟩ := h k hk
  have hsum := symSteps_headPos_eq VerifierSym.transition hrun
  have h0 : (symInitialConfig input).headPos = 0 := by simp [symInitialConfig]
  have hcfg : cfgm.headPos = symEnd 0 (p.take k) := by
    rw [hsum, h0]
    exact (symEnd_eq_headPos_sum 0 (p.take k)).symm
  rw [hqk, ← hcfg]
  exact ⟨ hlo, hhi⟩

end Mp


-- ===== δ-19-15c BEGIN =====
-- 轮头轴结构件（量测口径：每轮转向 ≤ 2.2·(该元素位长) + 11；#轮 = #元素）
-- 状态 4（轮头）只对 s / n（`SymKind.sel` / `SymKind.nosel`）有非陷阱转移。
namespace Mp

/-- δ-19-15c：状态 4 上非陷阱的合法转移，其读符号的种类必为 `sel` 或 `nosel`。 -/
theorem transition_four_read_isSelOrNosel (s : Sym) (r : SymTransResult)
    (h : r ∈ VerifierSym.transition (4, s)) (h101 : r.nextState ≠ 101) :
    s.1 = SymKind.sel ∨ s.1 = SymKind.nosel := by
  have h4mem : 4 ∈ VerifierSym.legalStates := by decide
  obtain ⟨k, b⟩ := s
  cases k <;> cases b <;>
    simp [VerifierSym.transition, h4mem] at h h101 ⊢ <;>
    (rw [h] at h101; simp at h101)

/-- δ-19-15c：非陷阱的轮头步读 `sel` 或 `nosel`。 -/
theorem symStep_read_isSelOrNosel_of_roundHead {step : SymStep}
    (h : step.result ∈ VerifierSym.transition (step.fromState, step.readSym))
    (h4 : step.fromState = 4) (h101 : step.result.nextState ≠ 101) :
    step.readSym.1 = SymKind.sel ∨ step.readSym.1 = SymKind.nosel :=
  transition_four_read_isSelOrNosel step.readSym step.result
    (by rw [h4] at h; exact h) h101

/-- δ-19-15c：`symRoundHead` 判定为真且非陷阱 ⇒ 该步读 `sel` / `nosel`。 -/
theorem symRoundHead_read_isSelOrNosel {step : SymStep}
    (h : step.result ∈ VerifierSym.transition (step.fromState, step.readSym))
    (hr : symRoundHead step = true) (h101 : step.result.nextState ≠ 101) :
    step.readSym.1 = SymKind.sel ∨ step.readSym.1 = SymKind.nosel :=
  symStep_read_isSelOrNosel_of_roundHead h (by simpa [symRoundHead] using hr) h101

end Mp
-- ===== δ-19-15c END =====

-- ===== δ-19-15c-2 BEGIN =====
-- (S3′) 元素区位长记账：Σ(bitWidth v + 1) = |元素区| ≤ L（初等）
namespace Mp

/-- δ-19-15c-2：原生位串长度 = 位宽。 -/
lemma encodeBitsSymNative_length (v : ℕ) : (encodeBitsSymNative v).length = bitWidth v := by
  simp [encodeBitsSymNative, bitWidth]

/-- δ-19-15c-2：元素区长度 = Σ(位宽) + #元素（每元素一个 α 加一段原生位串）。 -/
lemma encodeElementsSym_length (elems : List ℕ) :
    (encodeElementsSym elems).length = (elems.map bitWidth).sum + elems.length := by
  induction elems with
  | nil => simp [encodeElementsSym]
  | cons v rest ih =>
    cases rest with
    | nil => simp [encodeElementsSym, encodeBitsSymNative_length]
    | cons w rest' => simp [encodeElementsSym, encodeBitsSymNative_length, ih]; omega

/-- δ-19-15c-2（(S3′)）：位宽总和 + 元素数 ≤ 实例编码长度 L。 -/
lemma sum_bitWidth_add_length_le_encodeInstanceSym_length (inst : SubsetSumInstance) :
    (inst.elements.map bitWidth).sum + inst.elements.length
      ≤ (encodeInstanceSym inst).length := by
  rw [← encodeElementsSym_length]
  simp [encodeInstanceSym]
  omega

end Mp
-- ===== δ-19-15c-2 END =====

-- ===== δ-19-15c-3 BEGIN =====
-- (S2′) 步骤 2：全表唯一写 s/n 的站点 = 状态 2 读「未被标记的 α」（α 双分支），
-- 故「写 s/n 的合法步」所读必为 (alpha, false) —— 即该格是元素标记格。
namespace Mp

set_option maxRecDepth 200000

/-- δ-19-15c-3（表级）：写出 `Sym.sel`/`Sym.nosel`（未标记选择位）的合法转移，
    其读符号必为 `(SymKind.alpha, false)`。 -/
theorem writeSelOrNosel_read_alpha (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      r.nextState ≠ 101 → (r.writeSym = Sym.sel ∨ r.writeSym = Sym.nosel) →
      r.writeSym ≠ (k, m) →
      k = SymKind.alpha ∧ m = false := by
  cases m <;> cases k <;> decide

end Mp
-- ===== δ-19-15c-3 END =====
