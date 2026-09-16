/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import Mp.SubsetSumVerifierCore
import Mp.SubsetSumVerifierReverse4
import Mp.SubsetSumCompile
import Mp.SubsetSumVerifierReverse3

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
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

namespace Mp

/-!
# q12：验证器接受路径带头不超越右边界符（完整弱版）

在现行定义下证明：若符号验证器（Sym 层，转移表 `VerifierSym.transition`）存在一条
从初始配置出发的接受路径（终点状态 100），则终点带头满足 `headPos ≤ |input|`
——接受路径的带头不超越输入右端。

方法（canonical_unsat 先例）：先证表级事实（探针 1-2），再构造最小反例判定强版
（探针 3：任意路径不读 boundary 右侧——现定义为假，`Sym.blank` 残留使带外读可构造），
最后完成弱版引理链（Tstate/T1/T1w/T51 + 联合归纳 TQR + L3 带头不变量 + L4 主定理）。

核心结构决策：
- ① Q∧R 联合归纳一次证——Q（带外格值 ∈ 封闭集 {data0, data1, consumed}）与
  R（51 态带头 ≤ |w|−1）互相依赖（Q 的写步排除 51 写 boundary 需 R；R 的入边
  21 读 sel/nosel 的读位带内需 Q），两个独立定理循环引用被 Lean 拒绝，必须单归纳证 Q ∧ R；
- ② 带外封闭集迭代——decide 判定为假 = 真实表行反例（12 读 blank 写 data0 true、
  5 读 data 写 consumed），集从 {blank, data1} 扩为三类；51 写 boundary 由 R 排除；
- ③ 状态-位置链只需两个锚点（21→51 L、22→23 L），不需 33 态逐态界。
-/

/-- 探针 1（表级）：23 读 boundary → 100 R。 -/
theorem q12_state23_boundary_R :
    SymTransResult.mk 100 (Sym.mk SymKind.boundary false) Dir.R ∈
      VerifierSym.transition (23, Sym.mk SymKind.boundary false) := by
  decide

/-- 探针 2（表级）：100 是吸收自环。 -/
theorem q12_state100_absorb (k : SymKind) (m : Bool) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (100, Sym.mk k m)) :
    r.nextState = 100 ∧ r.moveDir = Dir.S := by
  have hb : ∀ k : SymKind, ∀ m : Bool, ∀ r ∈ VerifierSym.transition (100, Sym.mk k m),
      r.nextState = 100 ∧ r.moveDir = Dir.S := by
    decide
  exact hb k m r hr

/-- 探针 3（反例）：blank 残留使带外读可构造——强版（任意路径不读 boundary 右侧）为假。 -/
theorem q12_reads_outside_counterexample :
    ∃ (input : List Sym) (π : List SymStep) (cfg : SymConfig),
      SymReachablePath VerifierSym.transition input π cfg ∧
      cfg.headPos = ((input.length : ℤ) + 1) := by
  let input : List Sym := [Sym.boundary]
  let step0 : SymStep := SymStep.mk 0 Sym.boundary (SymTransResult.mk 1 Sym.boundary Dir.R)
  let step1 : SymStep := SymStep.mk 1 Sym.blank (SymTransResult.mk 1 Sym.blank Dir.R)
  let cfg1 : SymConfig := symStepConfig (symInitialConfig input) step0.result
  refine ⟨input, [step0, step1], symStepConfig cfg1 step1.result, ?_, ?_⟩
  · refine SymReachablePath.cons [step0] step1 cfg1 ?_ ?_ ?_ ?_
    · refine SymReachablePath.cons [] step0 (symInitialConfig input) ?_ ?_ ?_ ?_
      · exact SymReachablePath.nil
      · rfl
      · rfl
      · have h : SymTransResult.mk 1 Sym.boundary Dir.R ∈ VerifierSym.transition (0, Sym.boundary) := by
          decide
        simpa [input, symInitialConfig] using h
    · rfl
    · rfl
    · have h : SymTransResult.mk 1 Sym.blank Dir.R ∈ VerifierSym.transition (1, Sym.blank) := by
        decide
      simpa [input, symInitialConfig, symStepConfig, step0, step1, cfg1, Dir.toInt] using h
  · norm_num [symInitialConfig, symStepConfig, input, step0, step1, cfg1, Dir.toInt]

-- ============================================================================
-- 完整弱版 q12：接受路径带头 ≤ |input|（不超越右边界符）
-- ============================================================================

/-- 带外值判定：符号的 kind 是 data0/data1/consumed（带外封闭集）。 -/
def IsOutside (s : Sym) : Prop :=
  s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.consumed

/-- Tstate（状态界）：表内转移的 nextState < 102。 -/
theorem q12_nextState_lt102 (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) : r.nextState < 102 := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState < 102 := by
    native_decide
  exact hb ⟨q, hq⟩ s r hr

/-- 路径状态恒 < 102。 -/
theorem q12_path_state_lt102 (input : List Sym) (π : List SymStep) (cfg : SymConfig)
    (h : SymReachablePath VerifierSym.transition input π cfg) : cfg.state < 102 := by
  induction h with
  | nil => simp [symInitialConfig]
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      exact q12_nextState_lt102 cfg'.state ih step.readSym step.result
        (by simpa [hread] using htrans)

/-- T1（带外读不达 100）：读带外类符号的转移 nextState ≠ 100，
    唯一例外是 q = 100 自环（moveDir = S）。 -/
theorem q12_outside_ne_100 (q : ℕ) (hq : q < 102) (s : Sym)
    (hs : IsOutside s) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) :
    r.nextState ≠ 100 ∨ (q = 100 ∧ r.moveDir = Dir.S) := by
  rcases s with ⟨k, m⟩
  rcases hs with hk0 | hk1 | hk2
  · have hk0' : k = SymKind.data0 := hk0
    subst k
    have hb : ∀ q : Fin 102, ∀ m : Bool, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), Sym.mk SymKind.data0 m) →
          r.nextState ≠ 100 ∨ ((q : ℕ) = 100 ∧ r.moveDir = Dir.S) := by
      native_decide
    exact hb ⟨q, hq⟩ m r hr
  · have hk1' : k = SymKind.data1 := hk1
    subst k
    have hb : ∀ q : Fin 102, ∀ m : Bool, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), Sym.mk SymKind.data1 m) →
          r.nextState ≠ 100 ∨ ((q : ℕ) = 100 ∧ r.moveDir = Dir.S) := by
      native_decide
    exact hb ⟨q, hq⟩ m r hr
  · have hk2' : k = SymKind.consumed := hk2
    subst k
    have hb : ∀ q : Fin 102, ∀ m : Bool, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), Sym.mk SymKind.consumed m) →
          r.nextState ≠ 100 ∨ ((q : ℕ) = 100 ∧ r.moveDir = Dir.S) := by
      native_decide
    exact hb ⟨q, hq⟩ m r hr

/-- T1w（非 51 态带外写值封闭）：q ≠ 51 读带外类符号的转移写值仍在带外封闭集。 -/
theorem q12_outside_write_closed (q : ℕ) (hq : q < 102) (hq51 : q ≠ 51) (s : Sym)
    (hs : IsOutside s) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) : IsOutside r.writeSym := by
  rcases s with ⟨k, m⟩
  rcases hs with hk0 | hk1 | hk2
  · have hk0' : k = SymKind.data0 := hk0
    subst k
    have hb : ∀ q : Fin 102, (q : ℕ) ≠ 51 → ∀ m : Bool, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), Sym.mk SymKind.data0 m) →
          (r.writeSym).1 = SymKind.data0 ∨ (r.writeSym).1 = SymKind.data1 ∨
            (r.writeSym).1 = SymKind.consumed := by
      native_decide
    exact hb ⟨q, hq⟩ hq51 m r hr
  · have hk1' : k = SymKind.data1 := hk1
    subst k
    have hb : ∀ q : Fin 102, (q : ℕ) ≠ 51 → ∀ m : Bool, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), Sym.mk SymKind.data1 m) →
          (r.writeSym).1 = SymKind.data0 ∨ (r.writeSym).1 = SymKind.data1 ∨
            (r.writeSym).1 = SymKind.consumed := by
      native_decide
    exact hb ⟨q, hq⟩ hq51 m r hr
  · have hk2' : k = SymKind.consumed := hk2
    subst k
    have hb : ∀ q : Fin 102, (q : ℕ) ≠ 51 → ∀ m : Bool, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), Sym.mk SymKind.consumed m) →
          (r.writeSym).1 = SymKind.data0 ∨ (r.writeSym).1 = SymKind.data1 ∨
            (r.writeSym).1 = SymKind.consumed := by
      native_decide
    exact hb ⟨q, hq⟩ hq51 m r hr

/-- T51（51 的入边）：nextState = 51 的转移必为 21 读 sel/nosel 类且 moveDir = L。 -/
theorem q12_into_51 (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h51 : r.nextState = 51) :
    q = 21 ∧ (s.1 = SymKind.sel ∨ s.1 = SymKind.nosel) ∧ r.moveDir = Dir.L := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 51 →
        (q : ℕ) = 21 ∧ (s.1 = SymKind.sel ∨ s.1 = SymKind.nosel) ∧ r.moveDir = Dir.L := by
    native_decide
  exact hb ⟨q, hq⟩ s r hr h51

/-- TQR（联合归纳）：任意路径上
    Q：位置 ≥ |input| 的格子值恒为带外类（带外封闭）；
    R：状态 = 51 → 带头 ≤ |input| - 1（51 态带头恒在串内）。 -/
theorem q12_outside_closed_and_51_bound (input : List Sym) (π : List SymStep) (cfg : SymConfig)
    (h : SymReachablePath VerifierSym.transition input π cfg) :
    (∀ j : ℤ, (input.length : ℤ) ≤ j → IsOutside (cfg.tape j)) ∧
    (cfg.state = 51 → cfg.headPos ≤ (input.length : ℤ) - 1) := by
  induction h with
  | nil =>
      constructor
      · intro j hj
        left
        rw [symInitialConfig]
        by_cases hc : 0 ≤ j ∧ j.toNat < input.length
        · exfalso
          omega
        · simp [hc, Sym.blank]
      · intro h51
        simp [symInitialConfig] at h51
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      constructor
      · -- Q 步
        intro j hj
        rw [symStepConfig]
        by_cases hw : cfg'.headPos = j
        · -- 写该格（写位 = j ≥ |w|——带外写）
          have hcell : IsOutside (cfg'.tape j) := ih.1 j hj
          have hq' : cfg'.state < 102 := q12_path_state_lt102 input π₀ cfg' hprev
          have hne51 : cfg'.state ≠ 51 := by
            intro h51
            have hle := ih.2 h51
            omega
          have hw' : IsOutside step.result.writeSym :=
            q12_outside_write_closed cfg'.state hq' hne51 (cfg'.tape j) hcell step.result
              (by simpa [hread, hw] using htrans)
          simpa [hw] using hw'
        · -- 未写该格：ih 保持
          dsimp [symStepConfig]
          rw [if_neg]
          · exact ih.1 j hj
          · exact Ne.symm hw
      · -- R 步
        intro h51
        have hq' : cfg'.state < 102 := q12_path_state_lt102 input π₀ cfg' hprev
        have hinto := q12_into_51 cfg'.state hq' step.readSym step.result
          (by simpa [hread] using htrans) (by simpa [symStepConfig] using h51)
        rcases hinto with ⟨hq21, hsel, hL⟩
        -- 21 读 sel/nosel：读位带内（Q：sel/nosel 非带外类）
        have hpos : cfg'.headPos < (input.length : ℤ) := by
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
        -- 51 带头 = 21 带头 - 1 ≤ |w| - 2 ≤ |w| - 1
        change cfg'.headPos + step.result.moveDir.toInt ≤ (input.length : ℤ) - 1
        rw [hL, Dir.toInt]
        exact Int.sub_le_sub_right (le_of_lt hpos) (1 : ℤ)

/-- L3（带头不变量）：任意路径上，带头 ≤ |input| ∨ 状态 ≠ 100。 -/
theorem q12_head_invariant (input : List Sym) (π : List SymStep) (cfg : SymConfig)
    (h : SymReachablePath VerifierSym.transition input π cfg) :
    cfg.headPos ≤ (input.length : ℤ) ∨ cfg.state ≠ 100 := by
  induction h with
  | nil =>
      left
      simp [symInitialConfig]
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      by_cases hp : (symStepConfig cfg' step.result).headPos ≤ (input.length : ℤ)
      · left
        exact hp
      · right
        -- 步后带头 > |w|：步前带头 ≥ |w|（moveDir ≤ +1）
        have hpre : (input.length : ℤ) ≤ cfg'.headPos := by
          have hm : step.result.moveDir.toInt ≤ 1 := by
            cases step.result.moveDir <;> norm_num [Dir.toInt]
          dsimp [symStepConfig] at hp
          omega
        -- 步前读带外类（Q），读带外不达 100（T1），q=100 自环被 ih 排除
        have hQR := q12_outside_closed_and_51_bound input π₀ cfg' hprev
        have hcell : IsOutside (cfg'.tape cfg'.headPos) := hQR.1 cfg'.headPos hpre
        have hq' : cfg'.state < 102 := q12_path_state_lt102 input π₀ cfg' hprev
        have hcls := q12_outside_ne_100 cfg'.state hq' (cfg'.tape cfg'.headPos) hcell
          step.result (by simpa [hread] using htrans)
        intro hacc
        have hnext : step.result.nextState = 100 := by
          simpa [symStepConfig] using hacc
        rcases hcls with hne | h100S
        · exact hne hnext
        · -- q = 100 自环（S）：ih 左支给步前 ≤ |w|，hpre 给 ≥，故步前 = |w|，S 步后 = |w| 与 hp 矛盾
          rcases h100S with ⟨hq100, hS⟩
          rcases ih with hi1 | hi2
          · exfalso
            have hS' : step.result.moveDir.toInt = 0 := by
              rw [hS]
              rfl
            dsimp [symStepConfig] at hp
            omega
          · exact hi2 hq100

/-- L4（q12 完整弱版主定理）：接受路径（终点状态 100）的带头 ≤ |input|——不超越右边界符。 -/
theorem q12_weak (input : List Sym) (π : List SymStep) (cfg : SymConfig)
    (h : SymReachablePath VerifierSym.transition input π cfg) (hacc : cfg.state = 100) :
    cfg.headPos ≤ (input.length : ℤ) := by
  rcases q12_head_invariant input π cfg h with hp | hne
  · exact hp
  · exfalso
    exact hne hacc



/-! # q12 延伸：条款 5（后缀不变）Sym 层内核

A1 条款 5（hrel2）的 Sym 层支撑：`symAccepts (encodeInstanceSym inst ++ g) ↔
symAccepts (encodeInstanceSym inst)` 的内核——接受路径的"语义活动"全部在 w 内，
g 区只可能被 100 吸收自环读到（无条件自环，不影响接受性）。

链：write_boundary_class / into_23（表级）→ boundary_inside（Q_b：boundary 格恒在串内，
归纳用 q12 的 R 排除 51 带外写）→ state23_inside（Q23：23 态带头 < |input|，
入边 22@#₁ L / 自环 23@data0 L）→ accept_step_inside（接受步读位 < |input|）
→ init_tape_prefix（w 与 w++g 前缀 tape 一致，重放组件）。

剩余（下一轮）：L3''（接受路径每步步前带头 < |w| ∨ 状态 = 100）+
Q23 强化（23 带头 < |w|，依赖 3 写位链状态-位置界）+ 双向重放定理。 -/



/-- 表级：写 boundary 且写值 ≠ 读值的转移必为 q=51（读 data0）或 q=3（读 boundary-false）。 -/
theorem q12suffix_write_boundary_class (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (hb : (r.writeSym).1 = SymKind.boundary)
    (hne : r.writeSym ≠ s) :
    q = 51 ∨ q = 3 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → (r.writeSym).1 = SymKind.boundary →
        r.writeSym ≠ s → (q : ℕ) = 51 ∨ (q : ℕ) = 3 := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr hb hne

/-- 表级：nextState = 23 的转移必为 22 读 boundary-true 或 23 读 data0，且 moveDir = L。 -/
theorem q12suffix_into_23 (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h23 : r.nextState = 23) :
    ((q = 22 ∧ s = Sym.mk SymKind.boundary true) ∨ (q = 23 ∧ s.1 = SymKind.data0)) ∧
      r.moveDir = Dir.L := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 23 →
        (((q : ℕ) = 22 ∧ s = Sym.mk SymKind.boundary true) ∨
          ((q : ℕ) = 23 ∧ s.1 = SymKind.data0)) ∧ r.moveDir = Dir.L := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr h23

/-- Q_b（boundary 格恒在串内）：位置 ≥ |input| 的格子不是 boundary。 -/
theorem q12suffix_boundary_inside (input : List Sym) (π : List SymStep) (cfg : SymConfig)
    (h : SymReachablePath VerifierSym.transition input π cfg) :
    ∀ j : ℤ, (input.length : ℤ) ≤ j → (cfg.tape j).1 ≠ SymKind.boundary := by
  induction h with
  | nil =>
      intro j hj
      rw [symInitialConfig]
      by_cases hc : 0 ≤ j ∧ j.toNat < input.length
      · exfalso
        omega
      · simp [hc, Sym.blank]
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      intro j hj
      rw [symStepConfig]
      by_cases hw : cfg'.headPos = j
      · -- 写该格（写位 = j ≥ |w|——带外写）
        have hQR := q12_outside_closed_and_51_bound input π₀ cfg' hprev
        have hq' : cfg'.state < 102 := q12_path_state_lt102 input π₀ cfg' hprev
        dsimp [symStepConfig]
        rw [hw]
        -- 目标：(step.result.writeSym).1 ≠ SymKind.boundary
        by_cases hbw : (step.result.writeSym).1 = SymKind.boundary
        · exfalso
          by_cases hsame : step.result.writeSym = cfg'.tape j
          · -- 写回读符：写后该格仍是 boundary 则读时已是 boundary，ih 矛盾
            have hcell : (cfg'.tape j).1 = SymKind.boundary := by
              rwa [← hsame]
            exact ih j hj hcell
          · -- 新写 boundary：q = 51 ∨ q = 3
            rcases q12suffix_write_boundary_class cfg'.state hq' (cfg'.tape j) step.result
                (by simpa [hread, hw] using htrans) hbw hsame with h51 | h3
            · -- 51 写 boundary：R（q12）给 51 带头 ≤ |w|-1，与写位 ≥ |w| 矛盾
              have hle := hQR.2 h51
              omega
            · -- 3 写 boundary-true：3 的读位是 boundary 格，ih 给读位 < |w|，与写位 ≥ |w| 矛盾
              have hcell : (cfg'.tape cfg'.headPos).1 = SymKind.boundary := by
                have hbb : ∀ s : Sym, ∀ r : SymTransResult,
                    r ∈ VerifierSym.transition (3, s) → (r.writeSym).1 = SymKind.boundary →
                      s.1 = SymKind.boundary := by
                  native_decide
                exact hbb (cfg'.tape cfg'.headPos) step.result
                  (by simpa [hread, symStepConfig, h3] using htrans) hbw
              have hlt : cfg'.headPos < (input.length : ℤ) := by
                by_contra hge
                exact ih cfg'.headPos (le_of_not_gt hge) hcell
              omega
        · simpa using hbw
      · -- 未写该格：ih 保持
        dsimp [symStepConfig]
        rw [if_neg]
        · exact ih j hj
        · exact Ne.symm hw

/-- Q23（23 态带头恒在串内）：状态 = 23 → 带头 < |input|。 -/
theorem q12suffix_state23_inside (input : List Sym) (π : List SymStep) (cfg : SymConfig)
    (h : SymReachablePath VerifierSym.transition input π cfg) :
    cfg.state = 23 → cfg.headPos < (input.length : ℤ) := by
  induction h with
  | nil =>
      intro h23
      simp [symInitialConfig] at h23
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      intro h23
      have hq' : cfg'.state < 102 := q12_path_state_lt102 input π₀ cfg' hprev
      have hinto := q12suffix_into_23 cfg'.state hq' step.readSym step.result
        (by simpa [hread] using htrans) (by simpa [symStepConfig] using h23)
      rcases hinto with ⟨hcase, hL⟩
      rcases hcase with h22 | h23self
      · -- 22 读 boundary-true：读位是 boundary 格，Q_b 给读位 < |w|
        rcases h22 with ⟨hq22, hs⟩
        have hcell : (cfg'.tape cfg'.headPos).1 = SymKind.boundary := by
          rw [← hread]
          rw [hs]
          rfl
        have hQb := q12suffix_boundary_inside input π₀ cfg' hprev
        have hlt : cfg'.headPos < (input.length : ℤ) := by
          by_contra hge
          exact hQb cfg'.headPos (le_of_not_gt hge) hcell
        -- 23 带头 = 22 带头 - 1 < |w|
        change cfg'.headPos + step.result.moveDir.toInt < (input.length : ℤ)
        rw [hL, Dir.toInt]
        omega
      · -- 23 自环（读 data0 → L）：ih 给步前带头 < |w|
        rcases h23self with ⟨hq23, _hd⟩
        have hlt := ih hq23
        change cfg'.headPos + step.result.moveDir.toInt < (input.length : ℤ)
        rw [hL, Dir.toInt]
        omega

/-- 接受步存在性：接受路径上存在进 100 的步（23 读 boundary），其步前带头 < |input|。 -/
theorem q12suffix_accept_step_inside (input : List Sym) (π : List SymStep) (cfg : SymConfig)
    (h : SymReachablePath VerifierSym.transition input π cfg) :
    cfg.state = 100 → ∃ π₀ step π₁, π = π₀ ++ step :: π₁ ∧
      step.result.nextState = 100 ∧ step.fromState = 23 ∧ step.readSym.1 = SymKind.boundary ∧
      ∃ cfg', SymReachablePath VerifierSym.transition input π₀ cfg' ∧
        cfg'.headPos < (input.length : ℤ) := by
  intro hacc
  induction h with
  | nil =>
      simp [symInitialConfig] at hacc
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      have hq' : cfg'.state < 102 := q12_path_state_lt102 input π₀ cfg' hprev
      by_cases hprev100 : cfg'.state = 100
      · -- 前一步已是 100：ih 给更早的接受步
        rcases ih hprev100 with ⟨π₁, st, π₂, hsplit, hs100, h23, hb, c, hc, hlt⟩
        refine ⟨π₁, st, π₂ ++ [step], ?_, hs100, h23, hb, c, hc, hlt⟩
        rw [hsplit]
        simp [List.append_assoc]
      · -- 本步进 100：表级——进 100 的转移必为 23 读 boundary R
        have hstep100 : step.result.nextState = 100 := by
          simpa [symStepConfig] using hacc
        have hinto : step.fromState = 23 ∧ step.readSym.1 = SymKind.boundary := by
          have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
              r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 100 →
                (q : ℕ) = 23 ∧ s.1 = SymKind.boundary ∨ (q : ℕ) = 100 := by
            native_decide
          have hcls := hbb ⟨cfg'.state, hq'⟩ step.readSym step.result
            (by simpa [hread] using htrans) hstep100
          rcases hcls with hres | h100
          · exact ⟨by simpa [hfrom] using hres.1, hres.2⟩
          · exact False.elim (hprev100 h100)
        rcases hinto with ⟨h23, hb⟩
        -- 23 步读位 < |w|（Q23）
        have hlt : cfg'.headPos < (input.length : ℤ) :=
          q12suffix_state23_inside input π₀ cfg' hprev (by rwa [hfrom] at h23)
        refine ⟨π₀, step, [], rfl, hstep100, h23, hb, cfg', hprev, hlt⟩

/-- getD 在左段内的桥。 -/
lemma getD_of_append_left {α : Type} (l m : List α) (d : α) (j : ℕ) (h : j < l.length) :
    (l ++ m).getD j d = l.getD j d := by
  rw [List.getD_eq_get (l ++ m) d ⟨j, by
    exact Nat.lt_of_lt_of_le h (by simpa using (Nat.le_add_right l.length m.length))⟩]
  rw [List.getD_eq_get l d ⟨j, h⟩]
  exact List.getElem_append_left (as := l) (bs := m) h

/-- map 单射性（f 单射）。 -/
lemma map_injective {α β : Type} {f : α → β} (hf : ∀ {a b : α}, f a = f b → a = b)
    {l m : List α} (h : l.map f = m.map f) : l = m := by
  induction l generalizing m with
  | nil =>
      cases m with
      | nil => rfl
      | cons b mb => simp at h
  | cons a l ih =>
      cases m with
      | nil => simp at h
      | cons b mb =>
          injection h with hf' hrest
          have hab : a = b := hf hf'
          subst b
          rw [ih (by exact hrest)]

/-- digits 非空：0 < n → Nat.digits 2 n ≠ []。 -/
lemma digits_ne_nil {n : ℕ} (hpos : 0 < n) : Nat.digits 2 n ≠ [] := by
  unfold Nat.digits
  rcases n with _ | n'
  · omega
  · change Nat.digitsAux 2 (by decide) (n' + 1) ≠ []
    rw [Nat.digitsAux.eq_2]
    intro h
    simp at h

/-- digits 元素 < 基数（core 定理特化）。 -/
lemma digitsAux_lt {n d : ℕ} (hd : d ∈ Nat.digits 2 n) : d < 2 :=
  Nat.digits_lt_base (by decide : 1 < 2) hd

/-- digits 头部：n > 0 时 (Nat.digits 2 n).getD 0 0 = n % 2。 -/
lemma digits2_head (n : ℕ) (hpos : 0 < n) :
    (Nat.digits 2 n).getD 0 0 = n % 2 := by
  rcases n with _ | n'
  · omega
  · unfold Nat.digits
    change (Nat.digitsAux 2 (by decide) (n' + 1)).getD 0 0 = (n' + 1) % 2
    rw [Nat.digitsAux.eq_2]
    simp

/-- digits 尾部：n > 0 时 (Nat.digits 2 n).tail = Nat.digits 2 (n / 2)。 -/
lemma digits2_tail (n : ℕ) (hpos : 0 < n) :
    (Nat.digits 2 n).tail = Nat.digits 2 (n / 2) := by
  rcases n with _ | n'
  · omega
  · unfold Nat.digits
    change (Nat.digitsAux 2 (by decide) (n' + 1)).tail = Nat.digitsAux 2 (by decide) ((n' + 1) / 2)
    rw [Nat.digitsAux.eq_2]
    rfl

/-- Nat.digits 2 单射（ofDigits 往返）。 -/
lemma digits2_injective {n m : ℕ} (h : Nat.digits 2 n = Nat.digits 2 m) : n = m := by
  have := congrArg (Nat.ofDigits 2) h
  rwa [Nat.ofDigits_digits, Nat.ofDigits_digits] at this

/-- f 在 {0,1} 上单射。 -/
lemma digit_f_injective {a b : ℕ} (ha : a < 2) (hb : b < 2)
    (h : (if a = 0 then Sym.data0 else Sym.data1) = (if b = 0 then Sym.data0 else Sym.data1)) :
    a = b := by
  by_cases ha0 : a = 0
  · subst a
    by_cases hb0 : b = 0
    · subst b
      rfl
    · have hb1 : b = 1 := by omega
      subst b
      have hne : Sym.data0 ≠ Sym.data1 := by
        intro h
        injection h with hk hm
        cases hk
      simp at h
      exact (hne h).elim
  · have ha1 : a = 1 := by omega
    subst a
    by_cases hb0 : b = 0
    · subst b
      have hne : Sym.data1 ≠ Sym.data0 := by
        intro h
        injection h with hk hm
        cases hk
      simp at h
      exact (hne h).elim
    · have hb1 : b = 1 := by omega
      subst b
      rfl

/-- bits 编码全 data 类（界内）。 -/
lemma encodeBitsSym_data (n : ℕ) (k : ℕ) (_hk : k < (encodeBitsSym n).length) :
    ((encodeBitsSym n).getD k Sym.blank).1 = SymKind.data0 ∨
    ((encodeBitsSym n).getD k Sym.blank).1 = SymKind.data1 := by
  unfold encodeBitsSym
  rw [show ((Nat.digits 2 n).map (fun d => if d = 0 then Sym.data0 else Sym.data1)).getD k Sym.blank =
      (if (Nat.digits 2 n).getD k 0 = 0 then Sym.data0 else Sym.data1) from by
    change ((Nat.digits 2 n).map (fun d => if d = 0 then Sym.data0 else Sym.data1)).getD k
      (if 0 = 0 then Sym.data0 else Sym.data1) = (if (Nat.digits 2 n).getD k 0 = 0 then Sym.data0 else Sym.data1)
    rw [@List.getD_map ℕ Sym (Nat.digits 2 n) 0 k (fun d => if d = 0 then Sym.data0 else Sym.data1)]]
  by_cases h : (Nat.digits 2 n).getD k 0 = 0
  · rw [if_pos h]
    exact Or.inl rfl
  · rw [if_neg h]
    exact Or.inr rfl

/-- bits 编码单射：encodeBitsSym n = encodeBitsSym m → n = m。 -/
lemma encodeBitsSym_injective {n m : ℕ} (h : encodeBitsSym n = encodeBitsSym m) : n = m := by
  unfold encodeBitsSym at h
  have hdig : Nat.digits 2 n = Nat.digits 2 m := by
    -- 逐格 getD 相等 + 元素 < 2 + f 单射
    apply List.ext_get
    · have hlen := congrArg (fun l : List Sym => l.length) h
      simp at hlen
      exact hlen
    · intro j h1 h2
      have hget := congrArg (fun l : List Sym => l.getD j (if 0 = 0 then Sym.data0 else Sym.data1)) h
      have hgm := (List.getD_map (l := Nat.digits 2 n) (d := 0) (n := j)
        (f := fun d => if d = 0 then Sym.data0 else Sym.data1))
      have hgm' := (List.getD_map (l := Nat.digits 2 m) (d := 0) (n := j)
        (f := fun d => if d = 0 then Sym.data0 else Sym.data1))
      rw [hgm] at hget
      rw [hgm'] at hget
      have hltn : (Nat.digits 2 n).getD j 0 < 2 := by
        rw [List.getD_eq_get (Nat.digits 2 n) 0 ⟨j, h1⟩]
        exact digitsAux_lt (List.get_mem (Nat.digits 2 n) ⟨j, h1⟩)
      have hltm : (Nat.digits 2 m).getD j 0 < 2 := by
        rw [List.getD_eq_get (Nat.digits 2 m) 0 ⟨j, h2⟩]
        exact digitsAux_lt (List.get_mem (Nat.digits 2 m) ⟨j, h2⟩)
      have hij : (Nat.digits 2 n).getD j 0 = (Nat.digits 2 m).getD j 0 :=
        @digit_f_injective ((Nat.digits 2 n).getD j 0) ((Nat.digits 2 m).getD j 0) hltn hltm hget
      rw [List.getD_eq_get (Nat.digits 2 n) 0 ⟨j, h1⟩,
          List.getD_eq_get (Nat.digits 2 m) 0 ⟨j, h2⟩] at hij
      exact hij
  exact digits2_injective hdig

/-- 元素区编码不含 boundary 符号。 -/
lemma enc_elements_no_boundary {elems : List ℕ} {s : Sym} (hs : s ∈ encodeElementsSym elems) :
    s.1 ≠ SymKind.boundary := by
  induction elems generalizing s with
  | nil => simp [encodeElementsSym] at hs
  | cons v rest ih =>
      rw [encodeElementsSym_head_alpha v rest] at hs
      simp only [List.mem_cons] at hs
      rcases hs with hsα | hsrest
      · rw [hsα]
        intro h
        exact (by decide : SymKind.alpha ≠ SymKind.boundary) h
      · rw [List.mem_append] at hsrest
        rcases hsrest with hbits | hrest
        · rcases mem_encodeBitsSymNative_data v hbits with h0 | h1
          · rw [h0]
            intro h
            exact (by decide : SymKind.data0 ≠ SymKind.boundary) h
          · rw [h1]
            intro h
            exact (by decide : SymKind.data1 ≠ SymKind.boundary) h
        · exact ih hrest

/-- 结构：bits 区（1 ≤ j ≤ |A|）的格是 data 类。 -/
lemma enc_bits_data (inst : SubsetSumInstance) (j : ℕ)
    (hj : 1 ≤ j) (hj2 : j ≤ (encodeBitsSym inst.target).length) :
    ((encodeInstanceSym inst).getD j Sym.blank).1 = SymKind.data0 ∨
    ((encodeInstanceSym inst).getD j Sym.blank).1 = SymKind.data1 := by
  unfold encodeInstanceSym
  change (([Sym.boundary] ++ (encodeBitsSym inst.target ++ [Sym.boundary] ++
    encodeElementsSym inst.elements ++ [Sym.boundary])).getD j Sym.blank).1 = SymKind.data0 ∨
    (([Sym.boundary] ++ (encodeBitsSym inst.target ++ [Sym.boundary] ++
    encodeElementsSym inst.elements ++ [Sym.boundary])).getD j Sym.blank).1 = SymKind.data1
  rw [@List.getD_append_right Sym [Sym.boundary]
    (encodeBitsSym inst.target ++ [Sym.boundary] ++ encodeElementsSym inst.elements ++ [Sym.boundary])
    Sym.blank j (by omega)]
  rw [show j - [Sym.boundary].length = j - 1 from by simp]
  have hlt : j - 1 < (encodeBitsSym inst.target).length := by omega
  rw [show encodeBitsSym inst.target ++ [Sym.boundary] ++ encodeElementsSym inst.elements ++ [Sym.boundary] =
      encodeBitsSym inst.target ++ (([Sym.boundary] ++ encodeElementsSym inst.elements) ++ [Sym.boundary]) from by
    simp only [List.append_assoc]]
  have hg := getD_of_append_left (encodeBitsSym inst.target)
    ([Sym.boundary] ++ encodeElementsSym inst.elements ++ [Sym.boundary]) Sym.blank (j - 1) hlt
  rw [hg]
  exact encodeBitsSym_data inst.target (j - 1) hlt

/-- 结构：第二个 boundary（#₀）在位置 t = 1 + |target 位|（getD 版）。 -/
lemma enc_getD_boundary_mid (inst : SubsetSumInstance) :
    (encodeInstanceSym inst).getD (1 + (encodeBitsSym inst.target).length) Sym.blank
      = Sym.boundary := by
  unfold encodeInstanceSym
  change ([Sym.boundary] ++ (encodeBitsSym inst.target ++ [Sym.boundary] ++
    encodeElementsSym inst.elements ++ [Sym.boundary])).getD
    (1 + (encodeBitsSym inst.target).length) Sym.blank = Sym.boundary
  rw [@List.getD_append_right Sym [Sym.boundary]
    (encodeBitsSym inst.target ++ [Sym.boundary] ++ encodeElementsSym inst.elements ++ [Sym.boundary])
    Sym.blank (1 + (encodeBitsSym inst.target).length) (by simp)]
  rw [show 1 + (encodeBitsSym inst.target).length - [Sym.boundary].length =
      (encodeBitsSym inst.target).length from by simp]
  rw [show encodeBitsSym inst.target ++ [Sym.boundary] ++ encodeElementsSym inst.elements ++ [Sym.boundary] =
      encodeBitsSym inst.target ++ (([Sym.boundary] ++ encodeElementsSym inst.elements) ++ [Sym.boundary]) from by
    simp only [List.append_assoc]]
  rw [@List.getD_append_right Sym (encodeBitsSym inst.target)
    ([Sym.boundary] ++ encodeElementsSym inst.elements ++ [Sym.boundary])
    Sym.blank (encodeBitsSym inst.target).length (by rfl)]
  simp

/-- take 前缀自证：take |l| (l ++ m) = l。 -/
lemma take_prefix_of_len {α : Type} (l m : List α) : (l ++ m).take l.length = l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      simp [List.take_cons, ih]

/-- 编码前缀唯一：encodeInstanceSym inst ++ g = encodeInstanceSym inst' ++ g' → inst = inst'。 -/
lemma enc_prefix_unique {inst inst' : SubsetSumInstance} {g g' : List Sym}
    (h : encodeInstanceSym inst ++ g = encodeInstanceSym inst' ++ g') :
    inst = inst' := by
  -- 1. |A| = |A'|（mid 位置左侧 B、右侧 data 的矛盾）
  have hlenA : (encodeBitsSym inst.target).length = (encodeBitsSym inst'.target).length := by
    by_contra hne
    by_cases hlt : (encodeBitsSym inst.target).length < (encodeBitsSym inst'.target).length
    · have hcong := congrArg (fun l : List Sym => l.getD (1 + (encodeBitsSym inst.target).length) Sym.blank) h
      have hmid : (encodeInstanceSym inst ++ g).getD (1 + (encodeBitsSym inst.target).length) Sym.blank
          = Sym.boundary := by
        have hltw : 1 + (encodeBitsSym inst.target).length < (encodeInstanceSym inst).length := by
          unfold encodeInstanceSym
          simp [List.length_append]
          omega
        rw [getD_of_append_left (encodeInstanceSym inst) g Sym.blank
          (1 + (encodeBitsSym inst.target).length) hltw]
        exact enc_getD_boundary_mid inst
      rw [hmid] at hcong
      have hdata : ((encodeInstanceSym inst' ++ g').getD (1 + (encodeBitsSym inst.target).length) Sym.blank).1 =
          SymKind.data0 ∨ ((encodeInstanceSym inst' ++ g').getD (1 + (encodeBitsSym inst.target).length) Sym.blank).1 =
          SymKind.data1 := by
        have hltw : 1 + (encodeBitsSym inst.target).length < (encodeInstanceSym inst').length := by
          unfold encodeInstanceSym
          simp [List.length_append]
          omega
        rw [getD_of_append_left (encodeInstanceSym inst') g' Sym.blank
          (1 + (encodeBitsSym inst.target).length) hltw]
        change (([Sym.boundary] ++ (encodeBitsSym inst'.target ++ [Sym.boundary] ++
          encodeElementsSym inst'.elements ++ [Sym.boundary])).getD
          (1 + (encodeBitsSym inst.target).length) Sym.blank).1 = SymKind.data0 ∨
          (([Sym.boundary] ++ (encodeBitsSym inst'.target ++ [Sym.boundary] ++
          encodeElementsSym inst'.elements ++ [Sym.boundary])).getD
          (1 + (encodeBitsSym inst.target).length) Sym.blank).1 = SymKind.data1
        rw [@List.getD_append_right Sym [Sym.boundary]
          (encodeBitsSym inst'.target ++ [Sym.boundary] ++ encodeElementsSym inst'.elements ++ [Sym.boundary])
          Sym.blank (1 + (encodeBitsSym inst.target).length) (by simp)]
        rw [show 1 + (encodeBitsSym inst.target).length - [Sym.boundary].length =
            (encodeBitsSym inst.target).length from by simp]
        rw [show encodeBitsSym inst'.target ++ [Sym.boundary] ++ encodeElementsSym inst'.elements ++ [Sym.boundary] =
            encodeBitsSym inst'.target ++ (([Sym.boundary] ++ encodeElementsSym inst'.elements) ++ [Sym.boundary]) from by
          simp only [List.append_assoc]]
        rw [getD_of_append_left (encodeBitsSym inst'.target)
          (([Sym.boundary] ++ encodeElementsSym inst'.elements) ++ [Sym.boundary]) Sym.blank
          (encodeBitsSym inst.target).length hlt]
        exact encodeBitsSym_data inst'.target (encodeBitsSym inst.target).length hlt
      rcases hdata with hd0 | hd1
      · have : Sym.boundary.1 = SymKind.data0 := by rwa [hcong]
        exact (by decide : SymKind.boundary ≠ SymKind.data0) this
      · have : Sym.boundary.1 = SymKind.data1 := by rwa [hcong]
        exact (by decide : SymKind.boundary ≠ SymKind.data1) this
    · have hlt' : (encodeBitsSym inst'.target).length < (encodeBitsSym inst.target).length := by omega
      have hcong := congrArg (fun l : List Sym => l.getD (1 + (encodeBitsSym inst'.target).length) Sym.blank) h.symm
      have hmid : (encodeInstanceSym inst' ++ g').getD (1 + (encodeBitsSym inst'.target).length) Sym.blank
          = Sym.boundary := by
        have hltw : 1 + (encodeBitsSym inst'.target).length < (encodeInstanceSym inst').length := by
          unfold encodeInstanceSym
          simp [List.length_append]
          omega
        rw [getD_of_append_left (encodeInstanceSym inst') g' Sym.blank
          (1 + (encodeBitsSym inst'.target).length) hltw]
        exact enc_getD_boundary_mid inst'
      rw [hmid] at hcong
      have hdata : ((encodeInstanceSym inst ++ g).getD (1 + (encodeBitsSym inst'.target).length) Sym.blank).1 =
          SymKind.data0 ∨ ((encodeInstanceSym inst ++ g).getD (1 + (encodeBitsSym inst'.target).length) Sym.blank).1 =
          SymKind.data1 := by
        have hltw : 1 + (encodeBitsSym inst'.target).length < (encodeInstanceSym inst).length := by
          unfold encodeInstanceSym
          simp [List.length_append]
          omega
        rw [getD_of_append_left (encodeInstanceSym inst) g Sym.blank
          (1 + (encodeBitsSym inst'.target).length) hltw]
        change (([Sym.boundary] ++ (encodeBitsSym inst.target ++ [Sym.boundary] ++
          encodeElementsSym inst.elements ++ [Sym.boundary])).getD
          (1 + (encodeBitsSym inst'.target).length) Sym.blank).1 = SymKind.data0 ∨
          (([Sym.boundary] ++ (encodeBitsSym inst.target ++ [Sym.boundary] ++
          encodeElementsSym inst.elements ++ [Sym.boundary])).getD
          (1 + (encodeBitsSym inst'.target).length) Sym.blank).1 = SymKind.data1
        rw [@List.getD_append_right Sym [Sym.boundary]
          (encodeBitsSym inst.target ++ [Sym.boundary] ++ encodeElementsSym inst.elements ++ [Sym.boundary])
          Sym.blank (1 + (encodeBitsSym inst'.target).length) (by simp)]
        rw [show 1 + (encodeBitsSym inst'.target).length - [Sym.boundary].length =
            (encodeBitsSym inst'.target).length from by simp]
        rw [show encodeBitsSym inst.target ++ [Sym.boundary] ++ encodeElementsSym inst.elements ++ [Sym.boundary] =
            encodeBitsSym inst.target ++ (([Sym.boundary] ++ encodeElementsSym inst.elements) ++ [Sym.boundary]) from by
          simp only [List.append_assoc]]
        rw [getD_of_append_left (encodeBitsSym inst.target)
          (([Sym.boundary] ++ encodeElementsSym inst.elements) ++ [Sym.boundary]) Sym.blank
          (encodeBitsSym inst'.target).length hlt']
        exact encodeBitsSym_data inst.target (encodeBitsSym inst'.target).length hlt'
      rcases hdata with hd0 | hd1
      · have : Sym.boundary.1 = SymKind.data0 := by rwa [hcong]
        exact (by decide : SymKind.boundary ≠ SymKind.data0) this
      · have : Sym.boundary.1 = SymKind.data1 := by rwa [hcong]
        exact (by decide : SymKind.boundary ≠ SymKind.data1) this
  -- 2. A = A'
  have hA : encodeBitsSym inst.target = encodeBitsSym inst'.target := by
    have hall : ∀ j : ℕ, j < (encodeBitsSym inst.target).length →
        (encodeBitsSym inst.target).getD j Sym.blank = (encodeBitsSym inst'.target).getD j Sym.blank := by
      intro j hjlt
      have hcong := congrArg (fun l : List Sym => l.getD (j + 1) Sym.blank) h
      have hl : (encodeInstanceSym inst ++ g).getD (j + 1) Sym.blank =
          (encodeBitsSym inst.target).getD j Sym.blank := by
        have hltw : j + 1 < (encodeInstanceSym inst).length := by
          unfold encodeInstanceSym
          simp [List.length_append]
          omega
        rw [getD_of_append_left (encodeInstanceSym inst) g Sym.blank (j + 1) hltw]
        unfold encodeInstanceSym
        change ([Sym.boundary] ++ (encodeBitsSym inst.target ++ [Sym.boundary] ++
          encodeElementsSym inst.elements ++ [Sym.boundary])).getD (j + 1) Sym.blank =
          (encodeBitsSym inst.target).getD j Sym.blank
        rw [@List.getD_append_right Sym [Sym.boundary]
          (encodeBitsSym inst.target ++ [Sym.boundary] ++ encodeElementsSym inst.elements ++ [Sym.boundary])
          Sym.blank (j + 1) (by simp)]
        rw [show j + 1 - [Sym.boundary].length = j from by simp]
        rw [show encodeBitsSym inst.target ++ [Sym.boundary] ++ encodeElementsSym inst.elements ++ [Sym.boundary] =
            encodeBitsSym inst.target ++ (([Sym.boundary] ++ encodeElementsSym inst.elements) ++ [Sym.boundary]) from by
          simp only [List.append_assoc]]
        rw [getD_of_append_left (encodeBitsSym inst.target)
          (([Sym.boundary] ++ encodeElementsSym inst.elements) ++ [Sym.boundary]) Sym.blank j hjlt]
      have hr : (encodeInstanceSym inst' ++ g').getD (j + 1) Sym.blank =
          (encodeBitsSym inst'.target).getD j Sym.blank := by
        have hltw : j + 1 < (encodeInstanceSym inst').length := by
          unfold encodeInstanceSym
          simp [List.length_append]
          rw [← hlenA]
          omega
        rw [getD_of_append_left (encodeInstanceSym inst') g' Sym.blank (j + 1) hltw]
        unfold encodeInstanceSym
        change ([Sym.boundary] ++ (encodeBitsSym inst'.target ++ [Sym.boundary] ++
          encodeElementsSym inst'.elements ++ [Sym.boundary])).getD (j + 1) Sym.blank =
          (encodeBitsSym inst'.target).getD j Sym.blank
        rw [@List.getD_append_right Sym [Sym.boundary]
          (encodeBitsSym inst'.target ++ [Sym.boundary] ++ encodeElementsSym inst'.elements ++ [Sym.boundary])
          Sym.blank (j + 1) (by simp)]
        rw [show j + 1 - [Sym.boundary].length = j from by simp]
        rw [show encodeBitsSym inst'.target ++ [Sym.boundary] ++ encodeElementsSym inst'.elements ++ [Sym.boundary] =
            encodeBitsSym inst'.target ++ (([Sym.boundary] ++ encodeElementsSym inst'.elements) ++ [Sym.boundary]) from by
          simp only [List.append_assoc]]
        rw [getD_of_append_left (encodeBitsSym inst'.target)
          (([Sym.boundary] ++ encodeElementsSym inst'.elements) ++ [Sym.boundary]) Sym.blank j
          (by rw [← hlenA]; exact hjlt)]
      rwa [hl, hr] at hcong
    -- 逐格 getD 相等 → 列表相等（长度同 + ext_get）
    apply List.ext_get
    · simp [hlenA]
    · intro j h1 h2
      have hhall : (encodeBitsSym inst.target).getD j Sym.blank =
          (encodeBitsSym inst'.target).getD j Sym.blank := hall j h1
      rw [List.getD_eq_get (encodeBitsSym inst.target) Sym.blank ⟨j, h1⟩,
          List.getD_eq_get (encodeBitsSym inst'.target) Sym.blank ⟨j, h2⟩] at hhall
      exact hhall
  -- 3. target 相等
  have htarget : inst.target = inst'.target := encodeBitsSym_injective hA
  -- 4. 元素区相等
  have hE : encodeElementsSym inst.elements = encodeElementsSym inst'.elements := by
    have hdrop := congrArg (fun l : List Sym => l.drop (1 + (encodeBitsSym inst.target).length + 1)) h
    have hl : (encodeInstanceSym inst ++ g).drop (1 + (encodeBitsSym inst.target).length + 1) =
        encodeElementsSym inst.elements ++ [Sym.boundary] ++ g := by
      unfold encodeInstanceSym
      simp [List.length_append, List.drop_append]
    have hr : (encodeInstanceSym inst' ++ g').drop (1 + (encodeBitsSym inst.target).length + 1) =
        encodeElementsSym inst'.elements ++ [Sym.boundary] ++ g' := by
      unfold encodeInstanceSym
      rw [hlenA]
      simp [List.length_append, List.drop_append]
    rw [hl, hr] at hdrop
    have hElen : (encodeElementsSym inst.elements).length = (encodeElementsSym inst'.elements).length := by
      apply le_antisymm
      · by_contra hlt
        have hgt' : (encodeElementsSym inst'.elements).length < (encodeElementsSym inst.elements).length := by omega
        have hget := congrArg (fun l : List Sym => l.getD (encodeElementsSym inst'.elements).length Sym.blank) hdrop
        have hright : ((encodeElementsSym inst'.elements ++ [Sym.boundary] ++ g').getD
            (encodeElementsSym inst'.elements).length Sym.blank).1 = SymKind.boundary := by
          rw [show encodeElementsSym inst'.elements ++ [Sym.boundary] ++ g' =
              encodeElementsSym inst'.elements ++ ([Sym.boundary] ++ g') from by
            rw [List.append_assoc]]
          rw [@List.getD_append_right Sym (encodeElementsSym inst'.elements)
            ([Sym.boundary] ++ g') Sym.blank (encodeElementsSym inst'.elements).length (by omega)]
          simp
          rfl
        have hleft : ((encodeElementsSym inst.elements ++ [Sym.boundary] ++ g).getD
            (encodeElementsSym inst'.elements).length Sym.blank).1 = SymKind.boundary := by
          rw [hget]
          exact hright
        have hleft' : ((encodeElementsSym inst.elements).getD
            (encodeElementsSym inst'.elements).length Sym.blank).1 = SymKind.boundary := by
          rw [show encodeElementsSym inst.elements ++ [Sym.boundary] ++ g =
              encodeElementsSym inst.elements ++ ([Sym.boundary] ++ g) from by
            rw [List.append_assoc]] at hleft
          rw [getD_of_append_left (encodeElementsSym inst.elements)
            ([Sym.boundary] ++ g) Sym.blank (encodeElementsSym inst'.elements).length hgt'] at hleft
          exact hleft
        have hval : ((encodeElementsSym inst.elements).get
            ⟨(encodeElementsSym inst'.elements).length, hgt'⟩).1 = SymKind.boundary := by
          rw [List.getD_eq_get (encodeElementsSym inst.elements) Sym.blank
            ⟨(encodeElementsSym inst'.elements).length, hgt'⟩] at hleft'
          exact hleft'
        have hno := enc_elements_no_boundary
          (List.get_mem (encodeElementsSym inst.elements)
            ⟨(encodeElementsSym inst'.elements).length, hgt'⟩)
        exact hno hval
      · by_contra hlt
        have hgt' : (encodeElementsSym inst.elements).length < (encodeElementsSym inst'.elements).length := by omega
        have hget := congrArg (fun l : List Sym => l.getD (encodeElementsSym inst.elements).length Sym.blank) hdrop.symm
        have hright : ((encodeElementsSym inst.elements ++ [Sym.boundary] ++ g).getD
            (encodeElementsSym inst.elements).length Sym.blank).1 = SymKind.boundary := by
          rw [show encodeElementsSym inst.elements ++ [Sym.boundary] ++ g =
              encodeElementsSym inst.elements ++ ([Sym.boundary] ++ g) from by
            rw [List.append_assoc]]
          rw [@List.getD_append_right Sym (encodeElementsSym inst.elements)
            ([Sym.boundary] ++ g) Sym.blank (encodeElementsSym inst.elements).length (by omega)]
          simp
          rfl
        have hleft : ((encodeElementsSym inst'.elements ++ [Sym.boundary] ++ g').getD
            (encodeElementsSym inst.elements).length Sym.blank).1 = SymKind.boundary := by
          rw [hget]
          exact hright
        have hleft' : ((encodeElementsSym inst'.elements).getD
            (encodeElementsSym inst.elements).length Sym.blank).1 = SymKind.boundary := by
          rw [show encodeElementsSym inst'.elements ++ [Sym.boundary] ++ g' =
              encodeElementsSym inst'.elements ++ ([Sym.boundary] ++ g') from by
            rw [List.append_assoc]] at hleft
          rw [getD_of_append_left (encodeElementsSym inst'.elements)
            ([Sym.boundary] ++ g') Sym.blank (encodeElementsSym inst.elements).length hgt'] at hleft
          exact hleft
        have hval : ((encodeElementsSym inst'.elements).get
            ⟨(encodeElementsSym inst.elements).length, hgt'⟩).1 = SymKind.boundary := by
          rw [List.getD_eq_get (encodeElementsSym inst'.elements) Sym.blank
            ⟨(encodeElementsSym inst.elements).length, hgt'⟩] at hleft'
          exact hleft'
        have hno := enc_elements_no_boundary
          (List.get_mem (encodeElementsSym inst'.elements)
            ⟨(encodeElementsSym inst.elements).length, hgt'⟩)
        exact hno hval
    have htake := congrArg (fun l : List Sym => l.take (encodeElementsSym inst.elements).length) hdrop
    rw [show (encodeElementsSym inst.elements ++ [Sym.boundary] ++ g).take
        (encodeElementsSym inst.elements).length = encodeElementsSym inst.elements from by
      rw [List.take_append_of_le_length
        (by simp [List.length_append] : (encodeElementsSym inst.elements).length ≤ (encodeElementsSym inst.elements ++ [Sym.boundary]).length)]
      exact take_prefix_of_len (encodeElementsSym inst.elements) [Sym.boundary]] at htake
    rw [show (encodeElementsSym inst'.elements ++ [Sym.boundary] ++ g').take
        (encodeElementsSym inst.elements).length = encodeElementsSym inst'.elements from by
      rw [hElen]
      rw [List.take_append_of_le_length
        (by simp [List.length_append] : (encodeElementsSym inst'.elements).length ≤ (encodeElementsSym inst'.elements ++ [Sym.boundary]).length)]
      exact take_prefix_of_len (encodeElementsSym inst'.elements) [Sym.boundary]] at htake
    exact htake
  -- 5. elements 相等（parse 往返）
  have helems : inst.elements = inst'.elements := by
    rw [← parseElementsSym_encodeElementsSym inst.elements,
      ← parseElementsSym_encodeElementsSym inst'.elements]
    rw [hE]
  -- 6. inst = inst'
  rcases inst with ⟨tgt, elems⟩
  rcases inst' with ⟨tgt', elems'⟩
  have ht : elems = elems' := htarget
  have he : tgt = tgt' := helems
  subst elems
  subst tgt
  rfl

/-- 编码层：元素区编码的分支符号数 = 元素数。 -/
lemma enc_alpha_count_eq_elems (elems : List ℕ) :
    ((encodeElementsSym elems).filter Sym.isBranch).length = elems.length := by
  induction elems with
  | nil => rfl
  | cons v rest ih =>
      rw [show encodeElementsSym (v :: rest) = [Sym.alpha] ++ encodeBitsSymNative v ++
          encodeElementsSym rest from by
        cases rest <;> simp [encodeElementsSym]]
      rw [List.filter_append, List.filter_append]
      rw [show ([Sym.alpha] : List Sym).filter Sym.isBranch = [Sym.alpha] from by
        decide]
      rw [filter_branch_encodeBitsSymNative v]
      simp [ih]

/-- 读分支符号的转移写值非分支或写回原值（α 读即覆盖，位置不再分叉）。 -/
lemma branch_read_writes_nonbranch : (List.range 102).all (fun q =>
    ∀ k : SymKind, SymKind.isBranch k → ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (q, (k, m)) → ¬ Sym.isBranch r.writeSym ∨ r.writeSym = (k, m)) := by
  native_decide

/-- 写 β 符号的转移必读 β：β 永不新写，只写回读值（α 读恒写 sel/nosel；
    全量「写分支 → 读 β」对 100/101 自环写回 α 不成立，故结论收窄为 β 专属形式）。 -/
lemma branch_write_reads_beta : (List.range 102).all (fun q =>
    ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (q, (k, m)) → r.writeSym.1 = SymKind.beta →
      k = SymKind.beta) := by
  native_decide

/-- 元素位编码符号非 β。 -/
lemma encodeBitsSymNative_no_beta (n : ℕ) : ∀ s ∈ encodeBitsSymNative n, s.1 ≠ SymKind.beta := by
  intro s hs
  unfold encodeBitsSymNative at hs
  rw [List.mem_map] at hs
  rcases hs with ⟨d, hd, hds⟩
  rw [← hds]
  by_cases h : d = 0
  · rw [if_pos h]
    native_decide
  · rw [if_neg h]
    decide

/-- 元素区编码符号非 β（α/数据位均非 β）。 -/
lemma encodeElementsSym_no_beta (elems : List ℕ) : ∀ s ∈ encodeElementsSym elems, s.1 ≠ SymKind.beta := by
  induction elems with
  | nil => intro s hs; simp [encodeElementsSym] at hs
  | cons v vs ih =>
      intro s hs
      rw [show encodeElementsSym (v :: vs) = [Sym.alpha] ++ encodeBitsSymNative v ++
          encodeElementsSym vs from by
        cases vs <;> simp [encodeElementsSym]] at hs
      rw [List.mem_append] at hs
      rcases hs with hs | hs
      · rw [List.mem_append] at hs
        rcases hs with hs | hs
        · rw [List.mem_singleton] at hs
          rw [hs]
          decide
        · exact encodeBitsSymNative_no_beta v s hs
      · exact ih s hs

/-- 输入编码无 β 符号。 -/
lemma enc_no_beta (inst : SubsetSumInstance) : ∀ s ∈ encodeInstanceSym inst, s.1 ≠ SymKind.beta := by
  unfold encodeInstanceSym
  intro s hs
  rw [List.mem_append] at hs
  rcases hs with hs | hs
  · rw [List.mem_append] at hs
    rcases hs with hs | hs
    · rw [List.mem_append] at hs
      rcases hs with hs | hs
      · rw [List.mem_append] at hs
        rcases hs with hs | hs
        · rw [List.mem_singleton] at hs
          rw [hs]
          decide
        · rcases encodeBitsSym_nonboundary inst.target s hs with h | h <;> rw [h] <;> decide
      · rw [List.mem_singleton] at hs
        rw [hs]
        decide
    · have hno := encodeElementsSym_no_beta inst.elements s hs
      exact hno
  · rw [List.mem_singleton] at hs
    rw [hs]
    decide

-- ============================================================================
-- §1 表级分类引理的应用形态（q ∈ legalStates 版本）
-- ============================================================================

/-- branch_read_writes_nonbranch 的应用形态。 -/
lemma branch_read_writes_nonbranch_of (q : ℕ) (hq : q ∈ VerifierSym.legalStates) (s : Sym)
    (hb : Sym.isBranch s = true) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) :
    ¬ Sym.isBranch r.writeSym = true ∨ r.writeSym = s := by
  have hqlt : q < 102 := by
    simp [VerifierSym.legalStates] at hq
    omega
  rcases s with ⟨k, m⟩
  have hk : SymKind.isBranch k = true := by
    simpa [Sym.isBranch] using hb
  have hd := of_decide_eq_true
    ((List.all_eq_true.mp branch_read_writes_nonbranch) q (List.mem_range.mpr hqlt))
  exact hd k hk m r hr

/-- branch_write_reads_beta 的应用形态。 -/
lemma branch_write_reads_beta_of (q : ℕ) (hq : q ∈ VerifierSym.legalStates) (s : Sym)
    (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (hb : r.writeSym.1 = SymKind.beta) :
    s.1 = SymKind.beta := by
  have hqlt : q < 102 := by
    simp [VerifierSym.legalStates] at hq
    omega
  rcases s with ⟨k, m⟩
  have hd := of_decide_eq_true
    ((List.all_eq_true.mp branch_write_reads_beta) q (List.mem_range.mpr hqlt))
  exact hd k m r hr hb

/-- 写分支符号必写回读值（α/β 永不新写；对 100/101 自环与陷阱行成立）。 -/
lemma branch_write_eq_read : (List.range 102).all (fun q =>
    ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (q, (k, m)) → Sym.isBranch r.writeSym →
      r.writeSym = (k, m)) := by
  native_decide

/-- branch_write_eq_read 的应用形态。 -/
lemma branch_write_eq_read_of (q : ℕ) (hq : q ∈ VerifierSym.legalStates) (s : Sym)
    (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (hb : Sym.isBranch r.writeSym = true) :
    r.writeSym = s := by
  have hqlt : q < 102 := by
    simp [VerifierSym.legalStates] at hq
    omega
  rcases s with ⟨k, m⟩
  have hd := of_decide_eq_true
    ((List.all_eq_true.mp branch_write_eq_read) q (List.mem_range.mpr hqlt))
  exact hd k m r hr hb

-- ============================================================================
-- §2 目标 1：no_beta_invariant（可达配置带面恒无 β，无条件）
-- ============================================================================

/-- 无 β 不变量：从 enc inst 可达的任意配置，带面上无 β 符号（含带外 blank）。 -/
lemma no_beta_invariant (inst : SubsetSumInstance) (π : List SymStep) (cfg : SymConfig)
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg) :
    ∀ p : ℤ, (cfg.tape p).1 ≠ SymKind.beta := by
  induction h with
  | nil =>
      intro p
      dsimp [symInitialConfig, SymConfig.mk]
      by_cases h : 0 ≤ p ∧ p.toNat < (encodeInstanceSym inst).length
      · rw [dif_pos h]
        have hmem : (encodeInstanceSym inst).get ⟨p.toNat, h.2⟩ ∈ encodeInstanceSym inst :=
          List.get_mem (encodeInstanceSym inst) ⟨p.toNat, h.2⟩
        exact enc_no_beta inst _ hmem
      · rw [dif_neg h]
        decide
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro p
      dsimp [symStepConfig, SymConfig.mk]
      by_cases hp : p = cfg₁.headPos
      · rw [if_pos hp]
        intro hwβ
        have hq := (symReachable_state_mem_legal hprev).1
        have hβ := branch_write_reads_beta_of cfg₁.state hq (cfg₁.tape cfg₁.headPos)
          step.result htrans hwβ
        exact ih cfg₁.headPos hβ
      · rw [if_neg hp]
        exact ih p

/-- 分支格必在编码区内：带外为 blank 且永不写分支 → 读分支符号的格必在 [0, |enc|)。 -/
lemma branch_cells_in_bounds (inst : SubsetSumInstance) (π : List SymStep) (cfg : SymConfig)
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg) :
    ∀ p : ℤ, Sym.isBranch (cfg.tape p) = true →
      0 ≤ p ∧ p.toNat < (encodeInstanceSym inst).length := by
  induction h with
  | nil =>
      intro p hp
      dsimp [symInitialConfig, SymConfig.mk] at hp
      by_cases h : 0 ≤ p ∧ p.toNat < (encodeInstanceSym inst).length
      · exact h
      · rw [dif_neg h] at hp
        exfalso
        simpa [Sym.blank, Sym.isBranch, SymKind.isBranch] using hp
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro p hp
      dsimp [symStepConfig, SymConfig.mk] at hp
      by_cases hpw : p = cfg₁.headPos
      · rw [if_pos hpw] at hp
        have hq := (symReachable_state_mem_legal hprev).1
        have hwr := branch_write_eq_read_of cfg₁.state hq (cfg₁.tape cfg₁.headPos)
          step.result htrans hp
        rw [hwr] at hp
        have hbnd := ih cfg₁.headPos hp
        omega
      · rw [if_neg hpw] at hp
        exact ih p hp

-- ============================================================================
-- §3 目标 2：fork_steps_write_nonbranch（读分支步写非分支）
-- ============================================================================

/-- 读分支符号的步（非陷阱、非吸收态）写值非分支：
    分支读若不出 101 陷阱则必在状态 2（symTransition_branch_q2），其 (α,false) 行
    写 sel/nosel（symTransition_branch_write_sel_nosel）。
    注：表级「无条件读分支写非分支」不成立——2 读 (α,true)/β 与 100/101 自环、
    catch-all 均写回分支符号；故需排除陷阱与吸收态（即接受路径截断后自然满足的条件）。 -/
lemma fork_steps_write_nonbranch (q : ℕ) (s : Sym)
    (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (hb : Sym.isBranch s = true)
    (hrs : r.nextState ≠ 101) (hqne : q ≠ 100) :
    ¬ Sym.isBranch r.writeSym = true := by
  have hf : Sym.isBranch r.writeSym = false := by
    have hsel := symTransition_branch_write_sel_nosel q s r hb hr hrs hqne
    rcases hsel with h | h <;> rw [h] <;> dsimp [Sym.isBranch, SymKind.isBranch] <;> rfl
  intro hw
  rw [hf] at hw
  cases hw

-- ============================================================================
-- §4 目标 3：fork_conservation（读分支步数 + tape 分支格数 = 元素数）
-- ============================================================================

/-- digits→Sym 映射列表无分支符号（filter 版本）。 -/
lemma map_digits_filter_nil (l : List ℕ) :
    (l.map (fun d => if d = 0 then Sym.data0 else Sym.data1)).filter Sym.isBranch = [] := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
      rw [List.map_cons, List.filter_cons]
      by_cases hb : Sym.isBranch (if d = 0 then Sym.data0 else Sym.data1) = true
      · exfalso
        by_cases hd : d = 0 <;> simp [hd, Sym.isBranch, SymKind.isBranch] at hb
      · rw [if_neg hb, ih]

/-- 目标位编码无分支符号。 -/
lemma encodeBitsSym_filter_nil (n : ℕ) : (encodeBitsSym n).filter Sym.isBranch = [] := by
  unfold encodeBitsSym
  exact map_digits_filter_nil (Nat.digits 2 n)

/-- 目标位编码符号均非分支。 -/
lemma encodeBitsSym_no_branch (n : ℕ) : ∀ s ∈ encodeBitsSym n, Sym.isBranch s = false := by
  intro s hs
  cases hb : Sym.isBranch s with
  | true =>
      have hmem : s ∈ (encodeBitsSym n).filter Sym.isBranch := List.mem_filter.mpr ⟨hs, hb⟩
      rw [encodeBitsSym_filter_nil n] at hmem
      simp at hmem
  | false => rfl

/-- 目标位编码无分支符号（filter 版本）。 -/
lemma encodeBitsSymNative_filter_nil (n : ℕ) : (encodeBitsSymNative n).filter Sym.isBranch = [] := by
  unfold encodeBitsSymNative
  exact map_digits_filter_nil (Nat.digits 2 n)

/-- 元素位编码符号均非分支。 -/
lemma encodeBitsSymNative_no_branch (n : ℕ) : ∀ s ∈ encodeBitsSymNative n, Sym.isBranch s = false := by
  intro s hs
  cases hb : Sym.isBranch s with
  | true =>
      have hmem : s ∈ (encodeBitsSymNative n).filter Sym.isBranch := List.mem_filter.mpr ⟨hs, hb⟩
      rw [encodeBitsSymNative_filter_nil n] at hmem
      simp at hmem
  | false => rfl

/-- WithSel 编码（sel/nosel + 原生位）无分支符号。 -/
lemma encodeElementsSymWithSel_no_branch (elems : List ℕ) (sel : List Bool) :
    ∀ s ∈ encodeElementsSymWithSel elems sel, Sym.isBranch s = false := by
  induction elems generalizing sel with
  | nil =>
      intro s hs
      simp [encodeElementsSymWithSel, joinLists] at hs
  | cons v vs ih =>
      cases sel with
      | nil =>
          intro s hs
          simp [encodeElementsSymWithSel, joinLists] at hs
      | cons b bs =>
          intro s hs
          rw [show encodeElementsSymWithSel (v :: vs) (b :: bs) =
              ([if b then Sym.sel else Sym.nosel] ++ encodeBitsSymNative v) ++
                encodeElementsSymWithSel vs bs from by
            rfl] at hs
          rw [List.mem_append] at hs
          rcases hs with hs | hs
          · rw [List.mem_append] at hs
            rcases hs with hs | hs
            · rw [List.mem_singleton] at hs
              rw [hs]
              cases b <;> decide
            · exact encodeBitsSymNative_no_branch v s hs
          · exact ih bs s hs

/-- 元素区编码的长度展开（cons 情形）。 -/
lemma encodeElementsSym_cons_length (v : ℕ) (vs : List ℕ) :
    (encodeElementsSym (v :: vs)).length = 1 + (encodeBitsSymNative v).length +
      (encodeElementsSym vs).length := by
  cases vs with
  | nil => simp [encodeElementsSym]; omega
  | cons w ws => simp [encodeElementsSym]; omega

/-- WithSel 长度 = 元素区编码长度（sel 满长时）。 -/
lemma encodeElementsSymWithSel_length_eq (elems : List ℕ) (sel : List Bool)
    (hsel : sel.length = elems.length) :
    (encodeElementsSymWithSel elems sel).length = (encodeElementsSym elems).length := by
  induction elems generalizing sel with
  | nil =>
      cases sel with
      | nil => rfl
      | cons b bs => exfalso; simpa [List.length_cons] using hsel
  | cons v vs ih =>
      cases sel with
      | nil => exfalso; simpa [List.length_cons] using hsel
      | cons b bs =>
          rw [show encodeElementsSymWithSel (v :: vs) (b :: bs) =
              ([if b then Sym.sel else Sym.nosel] ++ encodeBitsSymNative v) ++
                encodeElementsSymWithSel vs bs from by
            rfl]
          rw [List.length_append, List.length_append, List.length_singleton]
          rw [encodeElementsSym_cons_length v vs]
          rw [ih bs (by simpa using hsel)]

/-- 实例编码的分支符号数 = 元素数。 -/
lemma enc_filter_branch_eq_elems (inst : SubsetSumInstance) :
    ((encodeInstanceSym inst).filter Sym.isBranch).length = inst.elements.length := by
  unfold encodeInstanceSym
  rw [List.filter_append, List.filter_append, List.filter_append, List.filter_append]
  rw [show ([Sym.boundary] : List Sym).filter Sym.isBranch = [] by decide,
      encodeBitsSym_filter_nil inst.target]
  simp [enc_alpha_count_eq_elems inst.elements]

/-- 保守性不变量：读分支步数 + tape 分支格数（[0, |enc|) 计数）= 元素数。
    前提：路径无 101 陷阱步（no 101）、无 100 吸收步（no 100）——分支读步的写非分支
    需要排除陷阱行（2 读 (α,true)/β 写回分支符号）与 100 自环。 -/
lemma fork_conservation (inst : SubsetSumInstance) (π : List SymStep) (cfg : SymConfig)
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101)
    (hno100 : ∀ step ∈ π, step.fromState ≠ 100) :
    (π.filter (fun step => Sym.isBranch step.readSym)).length +
      tapeBranchCount (encodeInstanceSym inst) cfg.tape = inst.elements.length := by
  induction h with
  | nil =>
      rw [tapeBranchCount_initial (encodeInstanceSym inst)]
      rw [enc_filter_branch_eq_elems inst]
      simp
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      by_cases hb : Sym.isBranch step.readSym
      · -- 分支读步：fork +1，写非分支（读格被覆盖），tape 分支格数 -1
        have hb' : Sym.isBranch (cfg₁.tape cfg₁.headPos) = true := by
          simpa [hread] using hb
        have hq := (symReachable_state_mem_legal hprev).1
        have h101 : step.result.nextState ≠ 101 := hno101 step (by simp)
        have h100 : step.fromState ≠ 100 := hno100 step (by simp)
        have hqne : cfg₁.state ≠ 100 := by
          intro hq'
          exact h100 (by rw [hfrom, hq'])
        have hwne : ¬ Sym.isBranch step.result.writeSym = true :=
          fork_steps_write_nonbranch cfg₁.state (cfg₁.tape cfg₁.headPos) step.result htrans
            hb' h101 hqne
        have hg_in : 0 ≤ cfg₁.headPos ∧ cfg₁.headPos.toNat < (encodeInstanceSym inst).length :=
          branch_cells_in_bounds inst π₀ cfg₁ hprev cfg₁.headPos hb'
        have htape_diff : tapeBranchCount (encodeInstanceSym inst) cfg₁.tape =
            tapeBranchCount (encodeInstanceSym inst) (symStepConfig cfg₁ step.result).tape + 1 := by
          dsimp [tapeBranchCount, symStepConfig, SymConfig.mk]
          have hcongr : ∀ i < (encodeInstanceSym inst).length, i ≠ cfg₁.headPos.toNat →
              Sym.isBranch (cfg₁.tape (i : ℤ)) = Sym.isBranch (
                (fun j : ℤ => if j = cfg₁.headPos then step.result.writeSym else cfg₁.tape j) (i : ℤ)) := by
            intro i hi hi'
            have hine : (i : ℤ) ≠ cfg₁.headPos := by
              intro h
              exact hi' (by omega)
            simp [hine]
          have hself : Sym.isBranch (cfg₁.tape (cfg₁.headPos.toNat : ℤ)) = true := by
            rw [show (cfg₁.headPos.toNat : ℤ) = cfg₁.headPos by omega]
            simpa [hread] using hb
          have hself' : Sym.isBranch ((fun j : ℤ => if j = cfg₁.headPos then step.result.writeSym
              else cfg₁.tape j) (cfg₁.headPos.toNat : ℤ)) = false := by
            simp only [show (cfg₁.headPos.toNat : ℤ) = cfg₁.headPos by omega]
            have hns : Sym.isBranch step.result.writeSym = false := by
              simpa using hwne
            exact hns
          exact filter_length_diff_single hg_in.2 hcongr hself hself'
        rw [List.filter_append]
        have hP : (decide (step.readSym.1 = SymKind.alpha) ||
            decide (step.readSym.1 = SymKind.beta)) = true := by
          rw [← Bool.decide_or]
          simpa [Sym.isBranch, SymKind.isBranch] using hb
        simp [hP, Bool.decide_or, List.length_append]
        have ih' : (List.filter (fun step => decide (step.readSym.1 = SymKind.alpha) ||
            decide (step.readSym.1 = SymKind.beta)) π₀).length +
            tapeBranchCount (encodeInstanceSym inst) cfg₁.tape = inst.elements.length := by
          simpa [Sym.isBranch, SymKind.isBranch] using (ih
            (fun st hst => hno101 st (by rw [List.mem_append]; left; exact hst))
            (fun st hst => hno100 st (by rw [List.mem_append]; left; exact hst)))
        rw [← ih']
        rw [htape_diff]
        ac_rfl
      · -- 非分支读步：fork 不变，写非分支（写分支必写回读值，读值非分支），tape 分支格数不变
        have htape_same : tapeBranchCount (encodeInstanceSym inst) cfg₁.tape =
            tapeBranchCount (encodeInstanceSym inst) (symStepConfig cfg₁ step.result).tape := by
          dsimp [tapeBranchCount, symStepConfig, SymConfig.mk]
          apply congrArg List.length
          apply List.filter_congr
          intro i hi
          by_cases hi' : (i : ℤ) = cfg₁.headPos
          · rw [if_pos hi']
            have hleft : Sym.isBranch (cfg₁.tape (i : ℤ)) = false := by
              rw [hi', ← hread]
              simpa using hb
            have hright : Sym.isBranch step.result.writeSym = false := by
              have hq' := (symReachable_state_mem_legal hprev).1
              have hwne : ¬ Sym.isBranch step.result.writeSym = true := by
                intro hwbr
                have hwr := branch_write_eq_read_of cfg₁.state hq' (cfg₁.tape cfg₁.headPos)
                  step.result htrans hwbr
                rw [hwr, ← hread] at hwbr
                exact hb hwbr
              simpa using hwne
            rw [hleft, hright]
          · rw [if_neg hi']
        rw [List.filter_append]
        have hP : (decide (step.readSym.1 = SymKind.alpha) ||
            decide (step.readSym.1 = SymKind.beta)) = false := by
          rw [← Bool.decide_or]
          simpa [Sym.isBranch, SymKind.isBranch] using hb
        simp [hP, Bool.decide_or]
        have ih' : (List.filter (fun step => decide (step.readSym.1 = SymKind.alpha) ||
            decide (step.readSym.1 = SymKind.beta)) π₀).length +
            tapeBranchCount (encodeInstanceSym inst) cfg₁.tape = inst.elements.length := by
          simpa [Sym.isBranch, SymKind.isBranch] using (ih
            (fun st hst => hno101 st (by rw [List.mem_append]; left; exact hst))
            (fun st hst => hno100 st (by rw [List.mem_append]; left; exact hst)))
        rw [← ih']
        rw [htape_same]

-- ============================================================================
-- §5 目标 4 的辅助：首达 4 时残基 = 0，且残基单调不增
-- ============================================================================

/-- filter 长度单调（逐点蕴含）。 -/
lemma filter_length_mono {n : ℕ} {P P' : ℕ → Bool} (h : ∀ i, P' i = true → P i = true) :
    ((List.range n).filter P').length ≤ ((List.range n).filter P).length := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.filter_append, List.filter_append,
        List.length_append, List.length_append]
      rw [List.filter_singleton]
      by_cases hP'n : P' n = true
      · have hPn : P n = true := h n hP'n
        simp [hP'n, hPn]
        omega
      · by_cases hPn : P n = true
        · simp [hP'n, hPn]
          omega
        · simp [hP'n, hPn]
          omega

/-- SymSteps（从合法态出发、无 101/100 步）上状态合法性保持 + tape 分支格数单调不增。 -/
lemma symSteps_tapeBranchCount_mono {input : List Sym} {cfg₀ : SymConfig}
    {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition cfg₀ π cfg)
    (h0 : cfg₀.state ∈ VerifierSym.legalStates)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101)
    (hno100 : ∀ step ∈ π, step.fromState ≠ 100) :
    cfg.state ∈ VerifierSym.legalStates ∧
      tapeBranchCount input cfg.tape ≤ tapeBranchCount input cfg₀.tape := by
  induction h with
  | nil => exact ⟨h0, by simp⟩
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      rcases ih (fun st hst => hno101 st (by rw [List.mem_append]; left; exact hst))
          (fun st hst => hno100 st (by rw [List.mem_append]; left; exact hst)) with
        ⟨hq₁, hmono₁⟩
      have h101 : step.result.nextState ≠ 101 := hno101 step (by simp)
      have h100 : step.fromState ≠ 100 := hno100 step (by simp)
      have hqne : cfg₁.state ≠ 100 := by
        intro hq
        exact h100 (by rw [hfrom, hq])
      have hwne : ¬ Sym.isBranch step.result.writeSym = true :=
        symTransition_write_not_branch cfg₁.state (cfg₁.tape cfg₁.headPos) step.result hq₁
          htrans h101 hqne
      constructor
      · dsimp [symStepConfig]
        exact symTransition_nextState_mem_legal cfg₁.state (cfg₁.tape cfg₁.headPos)
          step.result hq₁ htrans
      · have hstep : tapeBranchCount input (symStepConfig cfg₁ step.result).tape ≤
            tapeBranchCount input cfg₁.tape := by
          dsimp [tapeBranchCount, symStepConfig, SymConfig.mk]
          have hpt : ∀ i : ℕ, Sym.isBranch ((fun j : ℤ => if j = cfg₁.headPos then
                step.result.writeSym else cfg₁.tape j) (i : ℤ)) = true →
              Sym.isBranch (cfg₁.tape (i : ℤ)) = true := by
            intro i hb
            dsimp at hb
            by_cases hi : (i : ℤ) = cfg₁.headPos
            · rw [if_pos hi] at hb
              exfalso
              exact hwne hb
            · rw [if_neg hi] at hb
              exact hb
          exact filter_length_mono hpt
        exact le_trans hstep hmono₁

-- ============================================================================
-- §6 目标 4：sym_accept_fork_eq_elems
-- ============================================================================

/-- 主定理（A1 条款 1b 的 Sym 层机器部分）：接受路径读分支符号步数 = 元素数。 -/
theorem sym_accept_fork_eq_elems (inst : SubsetSumInstance) (hne : inst.elements ≠ [])
    (hpos : ∀ v ∈ inst.elements, 0 < v) (htarget : 0 < inst.target)
    (hholds : subsetSumHolds inst) :
    ∃ π : List SymStep, ∃ cfg : SymConfig,
      SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg ∧
      cfg.state = VerifierSym.qAccept ∧
      (π.filter (fun step => Sym.isBranch step.readSym)).length = inst.elements.length := by
  have hacc : symAccepts VerifierSym.verifierSymTransition VerifierSym.acceptStates
      (encodeInstanceSym inst) := (symVerifier_correct inst hne hpos htarget).2 hholds
  rcases hacc with ⟨π, cfg, hpath, hmem⟩
  have hs100 : cfg.state = 100 := by
    simpa [VerifierSym.acceptStates, VerifierSym.qAccept] using hmem
  have hsteps : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π cfg :=
    reachablePath_to_steps hpath
  -- 截断为首达 100 的路径（无 100 步）
  rcases symSteps_accept_exists_no_100 hsteps (by simpa [VerifierSym.qAccept] using hs100) with
    ⟨π', cfg', hsteps', hacc', hno100'⟩
  have hs100' : cfg'.state = 100 := by simpa [VerifierSym.qAccept] using hacc'
  -- 接受路径（截断后仍接受）无 101 步
  have hno101' : ∀ step ∈ π', step.result.nextState ≠ 101 := by
    intro step hmem'
    exact symAccepts_no_101 hsteps' hs100' step hmem'
  -- 首达状态 4 的子路径：元素区已全部覆盖（branch_phase_inv），残基 = 0
  have hset : cfg'.state ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 51, 76, 77, 81,
      84, 85, 86, 87, 100} : Finset ℕ) := by
    rw [hs100']
    native_decide
  rcases backchain_to_first4 hsteps' hset with ⟨π₁, π₂, cfg₄, hsplit, hπ₁, hs4, hno4₁, hrest⟩
  rcases branch_phase_inv inst π₁ cfg₄ hπ₁ hno4₁ hs4 with ⟨sel, hsel_len, hbody⟩
  have hbits : tapeAgrees cfg₄.tape 1 (encodeBitsSym inst.target) := hbody.2.1
  have hb0 : cfg₄.tape 0 = Sym.boundary := hbody.2.2.1
  have hb1 : cfg₄.tape (1 + (encodeBitsSym inst.target).length) = Sym.boundary := hbody.2.2.2.1
  have helems : tapeAgrees cfg₄.tape (2 + (encodeBitsSym inst.target).length)
      (encodeElementsSymWithSel inst.elements sel) := hbody.2.2.2.2.1
  have hhash : cfg₄.tape (2 + (encodeBitsSym inst.target).length +
      (encodeElementsSymWithSel inst.elements sel).length) = Sym.mk SymKind.boundary true :=
    hbody.2.2.2.2.2
  have hres4 : tapeBranchCount (encodeInstanceSym inst) cfg₄.tape = 0 := by
    dsimp [tapeBranchCount]
    have hnonb : ∀ i : ℕ, i < (encodeInstanceSym inst).length →
        Sym.isBranch (cfg₄.tape (i : ℤ)) = false := by
      intro i hi
      have hge0 : 0 ≤ (i : ℤ) := by exact_mod_cast (Nat.zero_le i)
      by_cases h1 : i = 0
      · rw [h1]
        change (cfg₄.tape 0).isBranch = false
        rw [hb0]
        native_decide
      · have hge1 : (1 : ℤ) ≤ (i : ℤ) := by omega
        by_cases h2 : (i : ℤ) < 1 + (encodeBitsSym inst.target).length
        · have hj : i - 1 < (encodeBitsSym inst.target).length := by
            have hjz : ((i - 1 : ℕ) : ℤ) < (encodeBitsSym inst.target).length := by
              have hi1 : ((i - 1 : ℕ) : ℤ) = (i : ℤ) - 1 := by omega
              omega
            exact_mod_cast hjz
          have htape' : cfg₄.tape (i : ℤ) = (encodeBitsSym inst.target)[i - 1] := by
            simpa [show (1 : ℤ) + ((i - 1 : ℕ) : ℤ) = (i : ℤ) by omega] using
              hbits (i - 1) hj
          rw [htape']
          exact encodeBitsSym_no_branch inst.target _
            (List.get_mem (encodeBitsSym inst.target) ⟨i - 1, hj⟩)
        · by_cases h3 : (i : ℤ) = 1 + (encodeBitsSym inst.target).length
          · rw [h3]
            rw [hb1]
            decide
          · by_cases h4 : (i : ℤ) < 2 + (encodeBitsSym inst.target).length +
                (encodeElementsSymWithSel inst.elements sel).length
            · have hge : (2 : ℤ) + (encodeBitsSym inst.target).length ≤ (i : ℤ) := by omega
              have hj : i - (2 + (encodeBitsSym inst.target).length) <
                  (encodeElementsSymWithSel inst.elements sel).length := by
                have hjz : ((i - (2 + (encodeBitsSym inst.target).length) : ℕ) : ℤ) <
                    (encodeElementsSymWithSel inst.elements sel).length := by
                  have hi1 : ((i - (2 + (encodeBitsSym inst.target).length) : ℕ) : ℤ) =
                      (i : ℤ) - (2 + (encodeBitsSym inst.target).length) := by omega
                  omega
                exact_mod_cast hjz
              have htape' : cfg₄.tape (i : ℤ) =
                  (encodeElementsSymWithSel inst.elements sel)[i - (2 + (encodeBitsSym inst.target).length)] := by
                simpa [show (2 : ℤ) + (encodeBitsSym inst.target).length +
                      ((i - (2 + (encodeBitsSym inst.target).length) : ℕ) : ℤ) = (i : ℤ) by omega] using
                  helems (i - (2 + (encodeBitsSym inst.target).length)) hj
              rw [htape']
              exact encodeElementsSymWithSel_no_branch inst.elements sel _
                (List.get_mem (encodeElementsSymWithSel inst.elements sel)
                  ⟨i - (2 + (encodeBitsSym inst.target).length), hj⟩)
            · have h5 : (i : ℤ) = 2 + (encodeBitsSym inst.target).length +
                  (encodeElementsSymWithSel inst.elements sel).length := by
                have henc : (encodeInstanceSym inst).length =
                    2 + (encodeBitsSym inst.target).length +
                      (encodeElementsSymWithSel inst.elements sel).length + 1 := by
                  simp [encodeInstanceSym,
                    encodeElementsSymWithSel_length_eq inst.elements sel hsel_len]
                  omega
                have hi' : (i : ℤ) < 2 + (encodeBitsSym inst.target).length +
                    (encodeElementsSymWithSel inst.elements sel).length + 1 := by
                  have hi₀ : (i : ℤ) < (encodeInstanceSym inst).length := by exact_mod_cast hi
                  simpa [henc] using hi₀
                omega
              rw [h5]
              rw [hhash]
              decide
    have hflt : (List.range (encodeInstanceSym inst).length).filter
        (fun i : ℕ => Sym.isBranch (cfg₄.tape (i : ℤ))) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro x hx
      have hxr : x ∈ List.range (encodeInstanceSym inst).length := (List.mem_filter.mp hx).1
      have hxb : Sym.isBranch (cfg₄.tape (x : ℤ)) = true := (List.mem_filter.mp hx).2
      have hlt : x < (encodeInstanceSym inst).length := List.mem_range.mp hxr
      have hf : Sym.isBranch (cfg₄.tape (x : ℤ)) = false := hnonb x hlt
      rw [hf] at hxb
      cases hxb
    have hlen : ((List.range (encodeInstanceSym inst).length).filter
        (fun i : ℕ => Sym.isBranch (cfg₄.tape (i : ℤ)))).length = 0 := by
      rw [hflt]
      rfl
    exact hlen
  -- 残基从 cfg₄ 到 cfg' 单调不增 → 终点残基 = 0
  have hmono : tapeBranchCount (encodeInstanceSym inst) cfg'.tape ≤
      tapeBranchCount (encodeInstanceSym inst) cfg₄.tape := by
    have hno101₂ : ∀ step ∈ π₂, step.result.nextState ≠ 101 := fun step hmem₂ =>
      hno101' step (by rw [hsplit]; rw [List.mem_append]; right; exact hmem₂)
    have hno100₂ : ∀ step ∈ π₂, step.fromState ≠ 100 := fun step hmem₂ =>
      hno100' step (by rw [hsplit]; rw [List.mem_append]; right; exact hmem₂)
    rcases symSteps_tapeBranchCount_mono hrest (by rw [hs4]; native_decide) hno101₂ hno100₂ with
      ⟨_, hmono⟩
    exact hmono
  have hres' : tapeBranchCount (encodeInstanceSym inst) cfg'.tape = 0 := by omega
  -- 截断路径的守恒：分支步数 + 残基 = 元素数
  have hpath' : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π' cfg' :=
    (symSteps_initial_iff VerifierSym.verifierSymTransition (encodeInstanceSym inst) π' cfg').mp hsteps'
  have hcons := fork_conservation inst π' cfg' hpath' hno101' hno100'
  have hfork : (π'.filter (fun step => Sym.isBranch step.readSym)).length = inst.elements.length := by
    rw [hres'] at hcons
    simpa using hcons
  exact ⟨π', cfg', hpath', hacc', hfork⟩

-- ============================================================================
-- §7 目标 4 补：1b 层间桥表级引理（Sym 层 → 4F4/NTM2 层读分隔符 (0,1) 的 1:1 映射基础）
-- 形态前提（hnoTerm 接受路径）：q ≠ 100（无吸收出发步）、nextState ≠ 101（无 trap 步）。
-- ============================================================================

lemma forkBridge_no_write_branch (q : ℕ) (hq : q < 102) (hq100 : q ≠ 100) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (hne : r.nextState ≠ 101) :
    r.writeSym.1 ≠ SymKind.alpha ∧ r.writeSym.1 ≠ SymKind.beta := by
  have hb : ∀ q : Fin 102, (q : ℕ) ≠ 100 → ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 →
      r.writeSym.1 ≠ SymKind.alpha ∧ r.writeSym.1 ≠ SymKind.beta := by
    native_decide
  exact hb ⟨q, hq⟩ hq100 s r hr hne

lemma forkBridge_read_alpha_q2_or_100 (q : ℕ) (hq : q < 102) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, Sym.mk SymKind.alpha false)) (hne : r.nextState ≠ 101) :
    q = 2 ∨ q = 100 := by
  have hb : ∀ q : Fin 102, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), Sym.mk SymKind.alpha false) → r.nextState ≠ 101 →
      (q : ℕ) = 2 ∨ (q : ℕ) = 100 := by
    native_decide
  exact hb ⟨q, hq⟩ r hr hne

lemma forkBridge_read_alpha_marked_q100 (q : ℕ) (hq : q < 102) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, Sym.mk SymKind.alpha true)) (hne : r.nextState ≠ 101) :
    q = 100 := by
  have hb : ∀ q : Fin 102, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), Sym.mk SymKind.alpha true) → r.nextState ≠ 101 →
      (q : ℕ) = 100 := by
    native_decide
  exact hb ⟨q, hq⟩ r hr hne

lemma forkBridge_L_not_phase0 (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (hne : r.nextState ≠ 101) (hd : r.moveDir = Dir.L) :
    q ≠ 0 ∧ q ≠ 1 ∧ q ≠ 2 := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 → r.moveDir = Dir.L →
      (q : ℕ) ≠ 0 ∧ (q : ℕ) ≠ 1 ∧ (q : ℕ) ≠ 2 := by
    native_decide
  exact hb ⟨q, hq⟩ s r hr hne hd

lemma forkBridge_alpha_branch_R (q : ℕ) (hq : q < 102) (hq100 : q ≠ 100) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, Sym.mk SymKind.alpha false)) (hne : r.nextState ≠ 101) :
    r.moveDir = Dir.R := by
  have hb : ∀ q : Fin 102, (q : ℕ) ≠ 100 → ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), Sym.mk SymKind.alpha false) → r.nextState ≠ 101 →
      r.moveDir = Dir.R := by
    native_decide
  exact hb ⟨q, hq⟩ hq100 r hr hne

lemma forkBridge_alpha_branch_write_sel (q : ℕ) (hq : q < 102) (hq100 : q ≠ 100) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, Sym.mk SymKind.alpha false)) (hne : r.nextState ≠ 101) :
    r.writeSym = Sym.sel ∨ r.writeSym = Sym.nosel := by
  have hb : ∀ q : Fin 102, (q : ℕ) ≠ 100 → ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), Sym.mk SymKind.alpha false) → r.nextState ≠ 101 →
      r.writeSym = Sym.sel ∨ r.writeSym = Sym.nosel := by
    native_decide
  exact hb ⟨q, hq⟩ hq100 r hr hne
end Mp
