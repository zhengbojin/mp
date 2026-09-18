/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/


import Mp.SubsetSumVerifierCBTM3

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
set_option linter.style.emptyLine false
set_option linter.style.setOption false

set_option maxRecDepth 200000

/-!
# 任务6：接受路径 ⟹ 全好块（投影的反方向）

把 CBTM3 的投影（好块路径 → Sym 路径）反方向闭合：任何从初始格局出发、
进入接受态 `acceptStates4` 的磁带路径，必可分解为 `GoodBlockPath`
（每 12 步一块、每块都是好块）。

证明路线：

1. §5 Sym 层转移表引理：状态集 `{0..22} ∪ {100,101}` 封闭；写符号从不
   产生分支符号（α/β 只减不增）；写符号的 4F4.4 标记只落在 data0/data1 上。
2. §6 Sym 层路径结构：Sym 机器从初始格局出发的运行——前缀
   `0 →(读#ₗ) 1 →(扫目标) 2 →(走元素区,α/β→sel/nosel) 3 →(左扫) 4`，
   此后 α/β 已全部转换，主循环只读非分支符号。推论：分支读只发生在
   状态 2；写符号恒非分支；读入符号的标记合法性恒成立。
3. §7 CBTM 相位纪律：每步 phase +1 (mod 12)；接受路径长度 ≡ 0 (mod 12)。
4. §8 逐块分析：陷阱支（q=101 结果）在任何接受路径上不可达
   （相位 3 合成读 im=true ⟺ 该格为 α/β ⟹ 对应 Sym 状态 = 2 ⟹ 只有
   sel/nosel 好支；相位 0-2/4-11 读的 re 格与写回格 im 恒 false）。
   由此每块 12 步的结果形态被强制，块末状态/带头回到 Sym 步形式。
5. §9 分解定理：接受路径 ⟹ `GoodBlockPath`（逐块归纳，配合 CBTM3 的
   `project_block` 维持逐块对应）。

当前状态：
- §5 四引理已证（受控枚举骨架：cases kind 前置 + interval_cases/split）。
- §6/§7 证明体已填充（待编译修正）。
- §8/§9 声明依赖 CBTM3 类型，TODO 块给出计划声明，待任务5 完成后启用。
- 已踩坑：first 的 alternative 中 `rcases … with h | h` 引入的名字在后续
  tactic 中不可见（Lean 4.32 scoping 坑，报 Unknown identifier）——一律用
  cases kind 前置 + interval_cases q 的受控枚举替代。
-/
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.constructorNameAsVariable false
set_option linter.unusedVariables false
set_option linter.style.nativeDecide false
set_option maxHeartbeats 8000000
namespace Mp
open CBTM
namespace SymToF4

-- ======================================================================
-- §5 Sym 层转移表引理
-- ======================================================================

set_option maxHeartbeats 8000000 in
/-- Sym 转移表的全部结果状态 ≤ 101。 -/
lemma symTransition_nextState_mem (q : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) :
    r.nextState ≤ 101 := by
  by_cases hqin : q ∈ VerifierSym.legalStates
  · have hdec : ∀ q ∈ VerifierSym.legalStates, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (q, s) → r.nextState ≤ 101 := by
      native_decide
    exact hdec q hqin s r hr
  · dsimp [VerifierSym.transition] at hr
    split at hr
    · exfalso
      rename_i hqin2
      exact hqin hqin2
    · simp only [Finset.mem_singleton] at hr
      subst r
      simp

/-- Sym 转移表：读非分支符号时，写符号也非分支。 -/
lemma symTransition_write_not_branch_of_not_branch_read (q : ℕ) (s : Sym) (hs : ¬ Sym.isBranch s)
    (r : SymTransResult) (hr : r ∈ VerifierSym.transition (q, s)) :
    ¬ Sym.isBranch r.writeSym := by
  by_cases hqin : q ∈ VerifierSym.legalStates
  · have hb : ∀ q ∈ VerifierSym.legalStates, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (q, s) → ¬ Sym.isBranch s → ¬ Sym.isBranch r.writeSym := by
      native_decide
    exact hb q hqin s r hr hs
  · dsimp [VerifierSym.transition] at hr
    split at hr
    · exfalso
      rename_i hqin2
      exact hqin hqin2
    · simp only [Finset.mem_singleton] at hr
      subst r
      exact hs

/-- Sym 转移表：分支行（q=2 读无标记 α）的结果恰是 sel/nosel 双分支（带标记 α 与 β 读到即陷阱）。 -/
lemma symTransition_branch_row (q : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (hα : s.1 = SymKind.alpha) (hs : s.2 = false)
    (hq2 : q = 2) :
    r = SymTransResult.mk 2 Sym.sel Dir.R ∨ r = SymTransResult.mk 2 Sym.nosel Dir.R := by
  rcases s with ⟨k, m⟩
  have hk : k = SymKind.alpha := by simpa using hα
  subst k
  subst q
  have hm : m = false := by simpa using hs
  subst m
  have hdec : ∀ r : SymTransResult, r ∈ VerifierSym.transition (2, Sym.mk SymKind.alpha false) →
      r = SymTransResult.mk 2 Sym.sel Dir.R ∨ r = SymTransResult.mk 2 Sym.nosel Dir.R := by
    native_decide
  exact hdec r hr


/-- 分支读且 q≠2 时结果行写回 s（或 sel/nosel）。 -/
lemma transition_branch_not_q2_write (q : ℕ) (s : Sym) (hbr : Sym.isBranch s) (hq2 : q ≠ 2)
    (r : SymTransResult) (hr : r ∈ VerifierSym.transition (q, s)) :
    r.writeSym = s ∨ r.writeSym = Sym.sel ∨ r.writeSym = Sym.nosel := by
  by_cases hqin : q ∈ VerifierSym.legalStates
  · have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → Sym.isBranch s → (q : ℕ) ≠ 2 →
        r.writeSym = s ∨ r.writeSym = Sym.sel ∨ r.writeSym = Sym.nosel := by
      native_decide
    have hqlt : q < 102 := by
      have hdec : ∀ q ∈ VerifierSym.legalStates, q < 102 := by
        decide
      exact hdec q hqin
    exact hb ⟨q, hqlt⟩ s r hr hbr hq2
  · dsimp [VerifierSym.transition] at hr
    split at hr
    · exfalso
      rename_i hqin2
      exact hqin hqin2
    · simp only [Finset.mem_singleton] at hr
      subst r
      left; rfl


/-- Sym 转移表（分支读 α/β）：写符号标记合法或为 sel/nosel。 -/
lemma symTransition_write_mark_valid_br (q : ℕ) (s : Sym) (r : SymTransResult)
    (hbr : Sym.isBranch s)
    (hr : r ∈ VerifierSym.transition (q, s))
    (hread : s.2 = true → s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary) :
    r.writeSym.2 = true → r.writeSym.1 = SymKind.data0 ∨ r.writeSym.1 = SymKind.data1 ∨
      r.writeSym.1 = SymKind.sel ∨ r.writeSym.1 = SymKind.nosel ∨
      r.writeSym.1 = SymKind.boundary := by
  by_cases hq2 : q = 2
  · subst q
    rcases s with ⟨k, m⟩
    cases k with
    | alpha =>
        by_cases hm : m
        · exfalso
          have hc := hread (by simpa [hm] using rfl : (Sym.mk SymKind.alpha m).2 = true)
          rcases hc with h | h | h <;> cases h
        · have hm' : m = false := by
            cases h : m <;> simp [h] at hm ⊢
          subst m
          have hdec : ∀ r : SymTransResult, r ∈ VerifierSym.transition (2, Sym.mk SymKind.alpha false) →
              r.writeSym.2 = true → r.writeSym.1 = SymKind.data0 ∨ r.writeSym.1 = SymKind.data1 ∨
                r.writeSym.1 = SymKind.sel ∨ r.writeSym.1 = SymKind.nosel ∨
                r.writeSym.1 = SymKind.boundary := by
            native_decide
          exact hdec r hr
    | beta =>
        have htr : ∀ m : Bool, ∀ r : SymTransResult, r ∈ VerifierSym.transition (2, Sym.mk SymKind.beta m) →
            r = SymTransResult.mk 101 (Sym.mk SymKind.beta m) Dir.S := by
          native_decide
        rw [htr m r hr]
        by_cases hm : m
        · exfalso
          have hc := hread (by simp [hm])
          rcases hc with h | h | h <;> cases h
        · intro hw
          exfalso
          exact hm hw
    | _ => cases hbr
  · have hwself := transition_branch_not_q2_write q s hbr hq2 r hr
    rcases hwself with h | h | h
    · rw [h]
      intro hw
      rcases s with ⟨k, m⟩
      cases k with
      | alpha | beta =>
          cases m
          · simp at hw
          · exfalso
            have hc := hread hw
            exact False.elim (Or.elim hc (fun h' => SymKind.noConfusion h')
              (fun h'' => Or.elim h'' (fun h' => SymKind.noConfusion h')
                (fun h' => SymKind.noConfusion h')))
      | _ => cases hbr
    · rw [h]; intro hw; right; right; left; rfl
    · rw [h]; intro hw; right; right; right; left; rfl


/-- Sym 转移表（非分支读）：写符号标记合法。 -/
lemma symTransition_write_mark_valid_nb (q : ℕ) (s : Sym) (r : SymTransResult)
    (hnb : ¬ Sym.isBranch s)
    (hr : r ∈ VerifierSym.transition (q, s))
    (hread : s.2 = true → s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary) :
    r.writeSym.2 = true → r.writeSym.1 = SymKind.data0 ∨ r.writeSym.1 = SymKind.data1 ∨
      r.writeSym.1 = SymKind.sel ∨ r.writeSym.1 = SymKind.nosel ∨
      r.writeSym.1 = SymKind.boundary := by
  by_cases hqin : q ∈ VerifierSym.legalStates
  · have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → ¬ Sym.isBranch s →
        (s.2 = true → s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary) →
        r.writeSym.2 = true → r.writeSym.1 = SymKind.data0 ∨ r.writeSym.1 = SymKind.data1 ∨
          r.writeSym.1 = SymKind.sel ∨ r.writeSym.1 = SymKind.nosel ∨
          r.writeSym.1 = SymKind.boundary := by
      native_decide
    have hqlt : q < 102 := by
      have hdec : ∀ q ∈ VerifierSym.legalStates, q < 102 := by
        decide
      exact hdec q hqin
    exact hb ⟨q, hqlt⟩ s r hr hnb hread
  · dsimp [VerifierSym.transition] at hr
    split at hr
    · exfalso
      rename_i hqin2
      exact hqin hqin2
    · simp only [Finset.mem_singleton] at hr
      subst r
      dsimp
      intro hw
      rcases hread hw with hd | hd | hd <;> rw [hd]
      · left; rfl
      · right; left; rfl
      · right; right; right; right; rfl

/-- Sym 转移表：读符号标记合法时，写符号的标记也落在 data0/data1/sel/nosel 上。 -/
lemma symTransition_write_mark_valid (q : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s))
    (hread : s.2 = true → s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary) :
    r.writeSym.2 = true → r.writeSym.1 = SymKind.data0 ∨ r.writeSym.1 = SymKind.data1 ∨
      r.writeSym.1 = SymKind.sel ∨ r.writeSym.1 = SymKind.nosel ∨
      r.writeSym.1 = SymKind.boundary := by
  by_cases hb : Sym.isBranch s
  · exact symTransition_write_mark_valid_br q s r hb hr hread
  · exact symTransition_write_mark_valid_nb q s r hb hr hread

/-- 转移表写出的 sel 若 ≠ 读符号，则恒为常量 `Sym.sel`（标记位 false）。 -/
lemma symTransition_write_sel_const (q : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h : r.writeSym.1 = SymKind.sel)
    (hne : r.writeSym ≠ s) :
    r.writeSym = Sym.sel := by
  by_cases hqin : q ∈ VerifierSym.legalStates
  · have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.writeSym.1 = SymKind.sel → r.writeSym ≠ s →
        r.writeSym = Sym.sel := by
      native_decide
    have hqlt : q < 102 := by
      have hdec : ∀ q ∈ VerifierSym.legalStates, q < 102 := by
        decide
      exact hdec q hqin
    exact hb ⟨q, hqlt⟩ s r hr h hne
  · dsimp [VerifierSym.transition] at hr
    split at hr
    · exfalso
      rename_i hqin2
      exact hqin hqin2
    · simp only [Finset.mem_singleton] at hr
      subst r
      exfalso
      exact hne rfl

/-- 转移表写出的 nosel 若 ≠ 读符号，则恒为常量 `Sym.nosel`（标记位 false）。 -/
lemma symTransition_write_nosel_const (q : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h : r.writeSym.1 = SymKind.nosel)
    (hne : r.writeSym ≠ s) :
    r.writeSym = Sym.nosel := by
  by_cases hqin : q ∈ VerifierSym.legalStates
  · have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.writeSym.1 = SymKind.nosel → r.writeSym ≠ s →
        r.writeSym = Sym.nosel := by
      native_decide
    have hqlt : q < 102 := by
      have hdec : ∀ q ∈ VerifierSym.legalStates, q < 102 := by
        decide
      exact hdec q hqin
    exact hb ⟨q, hqlt⟩ s r hr h hne
  · dsimp [VerifierSym.transition] at hr
    split at hr
    · exfalso
      rename_i hqin2
      exact hqin hqin2
    · simp only [Finset.mem_singleton] at hr
      subst r
      exfalso
      exact hne rfl

-- ======================================================================
-- §6 Sym 层路径结构（不变式归纳）
-- ======================================================================

/-- 初始配置的磁带符号标记合法（输入符号合法 + blank 合法）。 -/
lemma symInitialConfig_read_mark_valid (input : List Sym) (p : ℤ)
    (hinput : ∀ s ∈ input, s.2 = true → s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) :
    ((symInitialConfig input).tape p).2 = true → ((symInitialConfig input).tape p).1 = SymKind.data0 ∨
      ((symInitialConfig input).tape p).1 = SymKind.data1 := by
  dsimp [symInitialConfig]
  by_cases h : 0 ≤ p ∧ p.toNat < input.length
  · rw [dif_pos h]
    exact hinput (input.get ⟨p.toNat, h.2⟩) (by simp)
  · rw [dif_neg h]
    intro hw
    exfalso
    simp [Sym.blank, Sym.data0] at hw

/-- Sym 路径标记合法不变式：初始标记合法 ⟹ 全程保持——任意格子的标记位为 true 时，
其 kind 必 ∈ {data0, data1}，或该符号恰为常量 `Sym.sel`/`Sym.nosel`（两者标记位 false，
故不可能出现在标记为 true 的格中；写符号由 §5 的 symTransition_write_mark_valid
与 sel/nosel 常量引理保证）。 -/
lemma symSteps_invariant (cfg₀ : SymConfig) (π : List SymStep) (cfg : SymConfig)
    (h : SymSteps VerifierSym.transition cfg₀ π cfg)
    (h0 : ∀ p : ℤ, (cfg₀.tape p).2 = true → (cfg₀.tape p).1 = SymKind.data0 ∨ (cfg₀.tape p).1 = SymKind.data1) :
    ∀ p : ℤ, (cfg.tape p).2 = true → (cfg.tape p).1 = SymKind.data0 ∨ (cfg.tape p).1 = SymKind.data1 ∨
      (cfg.tape p) = Sym.sel ∨ (cfg.tape p) = Sym.nosel ∨
      (cfg.tape p).1 = SymKind.boundary := by
  induction h with
  | nil =>
      intro p hp
      rcases h0 p hp with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      have hmark_step2 : (step.readSym).2 = true → (step.readSym).1 = SymKind.data0 ∨
          (step.readSym).1 = SymKind.data1 ∨ (step.readSym).1 = SymKind.boundary := by
        intro hw
        rcases ih cfg₁.headPos (by simpa [hread] using hw) with h | h | h | h | h
        · exact Or.inl (by simpa [hread] using h)
        · exact Or.inr (Or.inl (by simpa [hread] using h))
        · exfalso
          rw [hread] at hw
          rw [h] at hw
          change false = true at hw
          cases hw
        · exfalso
          rw [hread] at hw
          rw [h] at hw
          change false = true at hw
          cases hw
        · exact Or.inr (Or.inr (by simpa [hread] using h))
      have htrans' : step.result ∈ VerifierSym.transition (cfg₁.state, cfg₁.tape cfg₁.headPos) := by
        simpa [hfrom, hread] using htrans
      intro p hp
      dsimp [symStepConfig] at hp ⊢
      by_cases hp0 : p = cfg₁.headPos
      · rw [if_pos hp0] at hp ⊢
        rcases symTransition_write_mark_valid cfg₁.state (cfg₁.tape cfg₁.headPos) step.result
            htrans' (by simpa [hread] using hmark_step2) hp with h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · by_cases hws : step.result.writeSym = step.readSym
          · exfalso
            have hk : step.readSym.1 = SymKind.sel := by rw [← hws]; exact h
            have hm : step.readSym.2 = true := by rw [← hws]; exact hp
            rcases hmark_step2 hm with hd | hd | hd <;> (rw [hd] at hk; cases hk)
          · exact Or.inr (Or.inr (Or.inl (symTransition_write_sel_const cfg₁.state
              (cfg₁.tape cfg₁.headPos) step.result htrans' h (by simpa [hread] using hws))))
        · by_cases hws : step.result.writeSym = step.readSym
          · exfalso
            have hk : step.readSym.1 = SymKind.nosel := by rw [← hws]; exact h
            have hm : step.readSym.2 = true := by rw [← hws]; exact hp
            rcases hmark_step2 hm with hd | hd | hd <;> (rw [hd] at hk; cases hk)
          · exact Or.inr (Or.inr (Or.inr (Or.inl (symTransition_write_nosel_const cfg₁.state
              (cfg₁.tape cfg₁.headPos) step.result htrans' h (by simpa [hread] using hws)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · rw [if_neg hp0] at hp ⊢
        exact ih p hp

/-- 从初始配置出发的 Sym 路径不变式（初始标记合法由输入提供）。 -/
lemma symSteps_initial_invariant (input : List Sym) (π : List SymStep) (cfg : SymConfig)
    (hinput : ∀ s ∈ input, s.2 = true → s.1 = SymKind.data0 ∨ s.1 = SymKind.data1)
    (h : SymSteps VerifierSym.transition (symInitialConfig input) π cfg) :
    ∀ p : ℤ, (cfg.tape p).2 = true → (cfg.tape p).1 = SymKind.data0 ∨ (cfg.tape p).1 = SymKind.data1 ∨
      (cfg.tape p) = Sym.sel ∨ (cfg.tape p) = Sym.nosel ∨
      (cfg.tape p).1 = SymKind.boundary := by
  exact symSteps_invariant (symInitialConfig input) π cfg h
    (fun p => symInitialConfig_read_mark_valid input p hinput)

-- ======================================================================
-- §7 CBTM 相位纪律
-- ======================================================================

/-- 相位纪律：每步的相位 +1 (mod 12)（对全部转移结果成立，含陷阱支）。 -/
lemma transition4_phase_succ (st : ℕ) (s : F4) (r : CBTMTransResult)
    (hr : r ∈ transition4 st s) (hph : (decodeState st).2.1 < 12)
    (hbufOK : (st / regBound) % stepsPerSym < 3 →
      st % regBound + bufOf3s ((st / regBound) % stepsPerSym) s (st % regBound) < regBound) :
    (decodeState r.nextState).2.1 = ((decodeState st).2.1 + 1) % 12 := by
  dsimp [transition4] at hr
  dsimp [decodeState] at hr
  have hph12 : st / regBound % stepsPerSym < 12 := by
    dsimp [decodeState, stepsPerSym, regBound] at hph
    exact hph
  by_cases h3 : (st / regBound) % stepsPerSym < 3
  · by_cases him : F4.im s
    · simp [hph12, h3, him] at hr
      rcases hr with h | h <;> rw [h]
      · -- trap S 支：nextState = encodeState 101 nphase 0
        dsimp [decodeState, encodeState, qBound, stepsPerSym, regBound]
        by_cases h11 : (st / regBound) % stepsPerSym = 11
        · simp [h11]
        · simp [h11]
          omega
      · -- trap R 支
        dsimp [decodeState, encodeState, qBound, stepsPerSym, regBound]
        by_cases h11 : (st / regBound) % stepsPerSym = 11
        · simp [h11]
        · simp [h11]
          omega
    · simp [hph12, h3, him] at hr
      rw [hr]
      rw [decodeState_encodeState (min (st / (stepsPerSym * regBound)) 101)
        ((st / regBound) % stepsPerSym + 1)
        (st % regBound + bufOf3s ((st / regBound) % stepsPerSym) s (st % regBound))
        (by dsimp [stepsPerSym] at h3 hph12 ⊢; omega)
        (by dsimp [regBound] at hbufOK; exact hbufOK (by dsimp [stepsPerSym] at h3; exact h3))]
      simp
      change (st / regBound) % stepsPerSym + 1 =
        ((st / regBound) % stepsPerSym + 1) % 12
      rw [Nat.mod_eq_of_lt (show ((st / regBound) % stepsPerSym + 1) < 12 by
        dsimp [stepsPerSym, regBound] at h3 ⊢
        omega)]
  · by_cases h33 : (st / regBound) % stepsPerSym = 3
    · by_cases him : F4.im s
      · -- phase 3 读 im=true：q=2 分支双结果或 trap
        rcases hsym : symOf4F4 ((f4ofBuf (st % regBound)).1) ((f4ofBuf (st % regBound)).2.1)
            ((f4ofBuf (st % regBound)).2.2) s with _ | sym
        · simp [hph12, h3, h33, him, hsym] at hr
          rcases hr with h | h <;> rw [h]
          · rw [decodeState_encodeState 101 4 0 (by norm_num) (by norm_num)]
            dsimp [decodeState, stepsPerSym, regBound] at h33 ⊢
            rw [h33]
          · rw [decodeState_encodeState 101 4 0 (by norm_num) (by norm_num)]
            dsimp [decodeState, stepsPerSym, regBound] at h33 ⊢
            rw [h33]
        · simp [hph12, h3, h33, him, hsym] at hr
          by_cases hq2 : min (st / (stepsPerSym * regBound)) 101 = 2 ∧ (f4ofBuf (st % regBound)).1 = F4.zero ∧ F4.re s = false
          · simp [hq2] at hr
            rcases hr with h | h <;> rw [h]
            · rw [decodeState_encodeState 2 4 (encodeResult (SymTransResult.mk 2 Sym.sel Dir.R))
                (by norm_num) (by decide)]
              dsimp [decodeState, stepsPerSym, regBound] at h33 ⊢
              rw [h33]
            · rw [decodeState_encodeState 2 4 (encodeResult (SymTransResult.mk 2 Sym.nosel Dir.R))
                (by norm_num) (by decide)]
              dsimp [decodeState, stepsPerSym, regBound] at h33 ⊢
              rw [h33]
          · simp [hq2] at hr
            rcases hr with h | h <;> rw [h]
            · rw [decodeState_encodeState 101 4 0 (by norm_num) (by norm_num)]
              dsimp [decodeState, stepsPerSym, regBound] at h33 ⊢
              rw [h33]
            · rw [decodeState_encodeState 101 4 0 (by norm_num) (by norm_num)]
              dsimp [decodeState, stepsPerSym, regBound] at h33 ⊢
              rw [h33]
      · -- phase 3 读 im=false：rs.image 或 trap1
        rcases hsym : symOf4F4 ((f4ofBuf (st % regBound)).1) ((f4ofBuf (st % regBound)).2.1)
            ((f4ofBuf (st % regBound)).2.2) s with _ | sym
        · simp [hph12, h3, h33, him, hsym] at hr
          rw [hr]
          rw [decodeState_encodeState 101 4 0 (by norm_num) (by norm_num)]
          dsimp [decodeState, stepsPerSym, regBound] at h33 ⊢
          rw [h33]
        · simp [hph12, h3, h33, him, hsym] at hr
          rcases hr with ⟨r₀, hr₀, h⟩
          rw [← h]
          rw [decodeState_encodeState r₀.nextState 4 (encodeResult r₀)
            (by norm_num)
            (by
              have hnext := transition_nextState_le101 _ sym (Nat.min_le_right _ _) r₀ hr₀
              dsimp [encodeResult, skOf, dirOf, regBound, encodeState, stepsPerSym]
              rcases r₀ with ⟨n0, w0, d0⟩
              rcases w0 with ⟨k0, m0⟩
              cases k0 <;> cases m0 <;> cases d0
              all_goals
                have hnextL : n0 ≤ 101 := by simpa using hnext
                dsimp [skOf, dirOf]
                omega)]
          simp
          dsimp [decodeState, stepsPerSym, regBound] at h33 ⊢
          rw [h33]
          first | done | norm_num
    · by_cases h8 : (st / regBound) % stepsPerSym < 8
      · have hge3 : 3 ≤ (st / regBound) % stepsPerSym := by omega
        have hlt8 : (st / regBound) % stepsPerSym < 8 := h8
        have hx4 : (st / regBound) % stepsPerSym = 4 ∨ (st / regBound) % stepsPerSym = 5 ∨
            (st / regBound) % stepsPerSym = 6 ∨ (st / regBound) % stepsPerSym = 7 := by omega
        rcases hx4 with hx4 | hx4 | hx4 | hx4
        · -- hx4 : (st / regBound) % stepsPerSym = 4
          by_cases him : F4.im s
          · simp [transition4, him, hx4] at hr
            rcases hr with h | h <;> rw [h]
            · dsimp
              dsimp [decodeState] at hx4 ⊢
              dsimp [stepsPerSym, regBound] at hx4 ⊢
              rw [hx4]
              dsimp [encodeState]
              norm_num
            · dsimp
              dsimp [decodeState] at hx4 ⊢
              dsimp [stepsPerSym, regBound] at hx4 ⊢
              rw [hx4]
              dsimp [encodeState]
              norm_num
          · simp [transition4, him, hx4] at hr
            rw [hr]
            by_cases hmin : st / 98304 ≤ 101
            · dsimp [stepsPerSym, regBound]
              rw [Nat.min_eq_left hmin]
              rw [decodeState_encodeState (st / 98304) 5 (st % regBound)
                (by norm_num) (by exact Nat.mod_lt _ (by decide : 0 < regBound))]
              dsimp [decodeState, stepsPerSym, regBound] at hx4 ⊢
              rw [hx4]
              first | done | norm_num
            · have hminr : 101 ≤ st / 98304 := by
                omega
              dsimp [stepsPerSym, regBound]
              rw [Nat.min_eq_right hminr]
              rw [decodeState_encodeState 101 5 (st % regBound)
                (by norm_num) (by exact Nat.mod_lt _ (by decide : 0 < regBound))]
              dsimp [decodeState, stepsPerSym, regBound] at hx4 ⊢
              rw [hx4]
              first | done | norm_num
        · -- hx4 : (st / regBound) % stepsPerSym = 5
          by_cases him : F4.im s
          · simp [transition4, him, hx4] at hr
            rcases hr with h | h <;> rw [h]
            · dsimp
              dsimp [decodeState] at hx4 ⊢
              dsimp [stepsPerSym, regBound] at hx4 ⊢
              rw [hx4]
              dsimp [encodeState]
              norm_num
            · dsimp
              dsimp [decodeState] at hx4 ⊢
              dsimp [stepsPerSym, regBound] at hx4 ⊢
              rw [hx4]
              dsimp [encodeState]
              norm_num
          · simp [transition4, him, hx4] at hr
            rw [hr]
            by_cases hmin : st / 98304 ≤ 101
            · dsimp [stepsPerSym, regBound]
              rw [Nat.min_eq_left hmin]
              rw [decodeState_encodeState (st / 98304) 6 (st % regBound)
                (by norm_num) (by exact Nat.mod_lt _ (by decide : 0 < regBound))]
              dsimp [decodeState, stepsPerSym, regBound] at hx4 ⊢
              rw [hx4]
              first | done | norm_num
            · have hminr : 101 ≤ st / 98304 := by
                omega
              dsimp [stepsPerSym, regBound]
              rw [Nat.min_eq_right hminr]
              rw [decodeState_encodeState 101 6 (st % regBound)
                (by norm_num) (by exact Nat.mod_lt _ (by decide : 0 < regBound))]
              dsimp [decodeState, stepsPerSym, regBound] at hx4 ⊢
              rw [hx4]
              first | done | norm_num
        · -- hx4 : (st / regBound) % stepsPerSym = 6
          by_cases him : F4.im s
          · simp [transition4, him, hx4] at hr
            rcases hr with h | h <;> rw [h]
            · dsimp
              dsimp [decodeState] at hx4 ⊢
              dsimp [stepsPerSym, regBound] at hx4 ⊢
              rw [hx4]
              dsimp [encodeState]
              norm_num
            · dsimp
              dsimp [decodeState] at hx4 ⊢
              dsimp [stepsPerSym, regBound] at hx4 ⊢
              rw [hx4]
              dsimp [encodeState]
              norm_num
          · simp [transition4, him, hx4] at hr
            rw [hr]
            by_cases hmin : st / 98304 ≤ 101
            · dsimp [stepsPerSym, regBound]
              rw [Nat.min_eq_left hmin]
              rw [decodeState_encodeState (st / 98304) 7 (st % regBound)
                (by norm_num) (by exact Nat.mod_lt _ (by decide : 0 < regBound))]
              dsimp [decodeState, stepsPerSym, regBound] at hx4 ⊢
              rw [hx4]
              first | done | norm_num
            · have hminr : 101 ≤ st / 98304 := by
                omega
              dsimp [stepsPerSym, regBound]
              rw [Nat.min_eq_right hminr]
              rw [decodeState_encodeState 101 7 (st % regBound)
                (by norm_num) (by exact Nat.mod_lt _ (by decide : 0 < regBound))]
              dsimp [decodeState, stepsPerSym, regBound] at hx4 ⊢
              rw [hx4]
              first | done | norm_num
        · -- hx4 : (st / regBound) % stepsPerSym = 7
          by_cases him : F4.im s
          · simp [transition4, him, hx4] at hr
            rcases hr with h | h <;> rw [h]
            · dsimp
              dsimp [decodeState] at hx4 ⊢
              dsimp [stepsPerSym, regBound] at hx4 ⊢
              rw [hx4]
              dsimp [encodeState]
              norm_num
            · dsimp
              dsimp [decodeState] at hx4 ⊢
              dsimp [stepsPerSym, regBound] at hx4 ⊢
              rw [hx4]
              dsimp [encodeState]
              norm_num
          · simp [transition4, him, hx4] at hr
            rw [hr]
            by_cases hmin : st / 98304 ≤ 101
            · dsimp [stepsPerSym, regBound]
              rw [Nat.min_eq_left hmin]
              rw [decodeState_encodeState (st / 98304) 8 (st % regBound)
                (by norm_num) (by exact Nat.mod_lt _ (by decide : 0 < regBound))]
              dsimp [decodeState, stepsPerSym, regBound] at hx4 ⊢
              rw [hx4]
              first | done | norm_num
            · have hminr : 101 ≤ st / 98304 := by
                omega
              dsimp [stepsPerSym, regBound]
              rw [Nat.min_eq_right hminr]
              rw [decodeState_encodeState 101 8 (st % regBound)
                (by norm_num) (by exact Nat.mod_lt _ (by decide : 0 < regBound))]
              dsimp [decodeState, stepsPerSym, regBound] at hx4 ⊢
              rw [hx4]
              first | done | norm_num
      · -- 移动阶段 8-11
        have hge8 : 8 ≤ (st / regBound) % stepsPerSym := by omega
        by_cases him : F4.im s
        · simp [hph12, h3, h33, h8, him] at hr
          by_cases h11 : (st / regBound) % stepsPerSym = 11
          · simp [hph12, h11] at hr
            rcases hr with h | h <;> rw [h]
            · by_cases hq101 : st / (stepsPerSym * regBound) = 101
              · have hq101n : st / 98304 = 101 := by simpa [stepsPerSym, regBound] using hq101
                norm_num at hq101
                simp [decodeState, encodeState, qBound, stepsPerSym, regBound, hq101] at h11 ⊢
                norm_num at *
                rw [Nat.add_mod]
                rw [h11]
              · have hq101n : st / 98304 ≠ 101 := by
                  intro h
                  apply hq101
                  simpa [stepsPerSym, regBound] using h
                norm_num at hq101
                simp [decodeState, encodeState, qBound, stepsPerSym, regBound, hq101] at h11 ⊢
                rw [Nat.add_mod]
                rw [h11]
            · rw [decodeState_encodeState 101 0 0 (by decide) (by decide)]
              simp
              dsimp [decodeState, stepsPerSym, regBound] at h11 ⊢
              rw [h11]
          · simp [hph12, h11] at hr
            rcases hr with h1 | h2
            · rw [h1]
              rw [decodeState_encodeState (min (st / (stepsPerSym * regBound)) 101)
                ((st / regBound) % stepsPerSym + 1) (st % regBound)
                (by dsimp [stepsPerSym] at h11 hph12 ⊢; omega)
                (by dsimp [regBound]; exact Nat.mod_lt _ (by norm_num))]
              simp
              dsimp [decodeState, stepsPerSym, regBound] at h11 h8 hph12 ⊢
              omega
            · rw [h2]
              rw [decodeState_encodeState 101 ((st / regBound) % stepsPerSym + 1) 0
                (by dsimp [stepsPerSym] at h11 hph12 ⊢; omega) (by decide)]
              simp
              dsimp [decodeState, stepsPerSym, regBound] at h11 h8 hph12 ⊢
              omega
        · simp [hph12, h3, h33, h8, him] at hr
          by_cases h11 : (st / regBound) % stepsPerSym = 11
          · simp [hph12, h11] at hr
            by_cases hq101 : st / (stepsPerSym * regBound) = 101
            · simp [hq101] at hr
              rw [hr]
              rw [decodeState_encodeState 101 0 0 (by decide) (by decide)]
              dsimp
              dsimp [decodeState, stepsPerSym, regBound] at hph ⊢
              rw [Nat.add_mod]
              have h11' : st / 8192 % 12 = 11 := by simpa [stepsPerSym, regBound] using h11
              simp [h11']
            · simp [hq101] at hr
              rw [hr]
              rw [decodeState_encodeState (min (decodeResult (st % regBound)).nextState 101) 0 0
                (by decide) (by decide)]
              dsimp
              dsimp [decodeState, stepsPerSym, regBound] at hph ⊢
              rw [Nat.add_mod]
              have h11' : st / 8192 % 12 = 11 := by simpa [stepsPerSym, regBound] using h11
              simp [h11']
          · simp [hph12, h11] at hr
            by_cases hq101 : st / (stepsPerSym * regBound) = 101
            · simp [hq101] at hr
              rw [hr]
              rw [decodeState_encodeState 101 ((st / regBound) % stepsPerSym + 1) 0
                (by dsimp [stepsPerSym] at h11 hph12 ⊢; omega) (by decide)]
              dsimp
              dsimp [decodeState, stepsPerSym, regBound] at hph ⊢
              rw [Nat.add_mod]
              have h11' : st / 8192 % 12 ≠ 11 := by simpa [stepsPerSym, regBound] using h11
              have hlt : st / 8192 % 12 + 1 < 12 := by
                have hle : st / 8192 % 12 ≤ 10 := by omega
                omega
              simp [Nat.mod_eq_of_lt hlt]
            · simp [hq101] at hr
              rw [hr]
              rw [decodeState_encodeState (min (st / (stepsPerSym * regBound)) 101)
                ((st / regBound) % stepsPerSym + 1) (st % regBound)
                (by dsimp [stepsPerSym] at h11 hph12 ⊢; omega)
                (by dsimp [regBound]; exact Nat.mod_lt _ (by norm_num))]
              simp
              dsimp [decodeState, stepsPerSym, regBound] at h11 h8 hph12 ⊢
              omega

/-- 模 12 小于 3 的余数只能是 0/1/2。 -/
lemma mod12_lt3_eq (n : ℕ) (h : n % 12 < 3) : n % 12 = 0 ∨ n % 12 = 1 ∨ n % 12 = 2 := by
  omega

/-- 读阶段（相位 < 3）：新 reg = 旧 reg + e·4^相位 < 4^(相位+1) = 4^新相位（含陷阱支，reg 归 0）。 -/
lemma transition4_read_phase_reg_lt (st : ℕ) (s : F4) (r : CBTMTransResult)
    (hr : r ∈ transition4 st s)
    (hph : (decodeState st).2.1 < 3)
    (hreg : (decodeState st).2.2 < 4 ^ (decodeState st).2.1) :
    (decodeState r.nextState).2.2 < 4 ^ (decodeState r.nextState).2.1 := by
  dsimp [transition4] at hr
  have hph' : (st / regBound) % stepsPerSym < 3 := by
    dsimp [decodeState, stepsPerSym, regBound] at hph
    exact hph
  have hreg' : st % regBound < 4 ^ ((st / regBound) % stepsPerSym) := by
    dsimp [decodeState, stepsPerSym, regBound] at hreg
    exact hreg
  have hph12 : (st / regBound) % stepsPerSym + 1 < stepsPerSym := by
    dsimp [stepsPerSym] at hph' ⊢
    omega
  have hle : (if s = F4.zero then 0 else if s = F4.one then 1 else if s = F4.alpha then 2 else 3) ≤ 3 := by
    rcases s with ⟨rs, is⟩
    cases rs <;> cases is <;> simp [F4.zero, F4.one, F4.alpha, F4.beta]
  have hne11 : (st / regBound) % stepsPerSym ≠ 11 := by omega
  simp [decodeState, hph', hne11] at hr
  by_cases him : F4.im s
  · simp [him] at hr
    rcases hr with hr1 | hr2
    · rw [hr1]
      rw [decodeState_encodeState 101 ((st / regBound) % stepsPerSym + 1) 0 hph12 (by norm_num)]
      dsimp [stepsPerSym, regBound]
      norm_num
    · rw [hr2]
      rw [decodeState_encodeState 101 ((st / regBound) % stepsPerSym + 1) 0 hph12 (by norm_num)]
      dsimp [stepsPerSym, regBound]
      norm_num
  · simp [him] at hr
    rw [hr]
    have hreg8192 : st % regBound + bufOf3s ((st / regBound) % stepsPerSym) s (st % regBound) < regBound := by
      have hle2 : (st / regBound) % stepsPerSym ≤ 2 := by
        dsimp [stepsPerSym] at hph'
        exact Nat.le_of_lt_succ hph'
      have hp012 : (st / regBound) % stepsPerSym = 0 ∨
          (st / regBound) % stepsPerSym = 1 ∨
          (st / regBound) % stepsPerSym = 2 := by
        have hlt' : (st / 8192) % 12 < 3 := by
          dsimp [stepsPerSym, regBound] at hle2
          exact Nat.lt_of_le_of_lt hle2 (by norm_num)
        simpa [stepsPerSym, regBound] using mod12_lt3_eq (st / 8192) hlt'
      have hpow : 4 ^ ((st / regBound) % stepsPerSym) ≤ 16 := by
        rcases hp012 with h2 | h1 | h0
        · rw [h2]; norm_num
        · rw [h1]; norm_num
        · rw [h0]; norm_num
      have hbuf : bufOf3s ((st / regBound) % stepsPerSym) s (st % regBound) ≤ 48 := by
        unfold bufOf3s
        have hleif : (if s = F4.zero then 0 else if s = F4.one then 1 else if s = F4.alpha then 2 else 3) ≤ 3 := by
          omega
        exact Nat.mul_le_mul hleif hpow
      dsimp [regBound, stepsPerSym] at hreg' hpow hbuf ⊢
      omega
    rw [decodeState_encodeState (min (st / (stepsPerSym * regBound)) 101)
      ((st / regBound) % stepsPerSym + 1)
      (st % regBound + bufOf3s ((st / regBound) % stepsPerSym) s (st % regBound))
      hph12 hreg8192]
    dsimp [bufOf3s, stepsPerSym, regBound] at hreg' ⊢
    rw [pow_succ]
    have hleif : (if s = F4.zero then 0 else if s = F4.one then 1 else if s = F4.alpha then 2 else 3) ≤ 3 := by
      omega
    nlinarith [hreg', hleif, Nat.mul_le_mul_right (4 ^ (st / 8192 % 12)) hleif]

/-- 相位 11（块末移动/重启）：下一状态相位与 reg 分量都归 0。 -/
lemma transition4_phase11_reg_eq_zero (st : ℕ) (s : F4) (r : CBTMTransResult)
    (hr : r ∈ transition4 st s)
    (hph : (decodeState st).2.1 = 11) :
    (decodeState r.nextState).2.1 = 0 ∧ (decodeState r.nextState).2.2 = 0 := by
  dsimp [transition4] at hr
  have hph' : (st / regBound) % stepsPerSym = 11 := by
    dsimp [decodeState, stepsPerSym, regBound] at hph
    exact hph
  have hnotlt3 : ¬ (st / regBound) % stepsPerSym < 3 := by omega
  have hnot3 : ¬ (st / regBound) % stepsPerSym = 3 := by
    dsimp [stepsPerSym] at hph' ⊢
    omega
  have hnot8 : ¬ (st / regBound) % stepsPerSym < 8 := by
    dsimp [stepsPerSym] at hph' ⊢
    omega
  have hlt12 : (st / regBound) % stepsPerSym < 12 := by
    dsimp [stepsPerSym] at hph' ⊢
    omega
  have h113 : ((11 : ℕ) < 3) = False := by decide
  have h113e : ((11 : ℕ) = 3) = False := by decide
  simp only [decodeState, stepsPerSym, regBound, hph', hnotlt3, hnot3, hnot8, hlt12, h113, h113e,
    if_false, if_true] at hr
  by_cases him : F4.im s
  · simp [him, decodeResult] at hr
    rcases hr with hr1 | hr2
    · rw [hr1]
      by_cases hq101 : st / (stepsPerSym * regBound) = 101
      · have hq101n : st / 98304 = 101 := by simpa [stepsPerSym, regBound] using hq101
        simp [hq101n] at *
        rw [decodeState_encodeState 101 0 0 (by decide) (by norm_num)]
        dsimp [stepsPerSym, regBound]
        norm_num
      · have hq101n : st / 98304 ≠ 101 := by
          intro h
          apply hq101
          simpa [stepsPerSym, regBound] using h
        simp [hq101n] at *
        rw [decodeState_encodeState (min (st % regBound / 54) 101) 0 0
          (by decide) (by norm_num)]
        dsimp [stepsPerSym, regBound]
        norm_num
    · rw [hr2]
      rw [decodeState_encodeState 101 0 0 (by decide) (by norm_num)]
      dsimp [stepsPerSym, regBound]
      norm_num
  · simp [him, decodeResult] at hr
    by_cases hq101 : st / 98304 = 101
    · rw [if_pos hq101] at hr
      simp at hr
      rw [hr]
      rw [decodeState_encodeState 101 0 0 (by decide) (by norm_num)]
      dsimp [stepsPerSym, regBound]
      norm_num
    · rw [if_neg hq101] at hr
      simp at hr
      rw [hr]
      have hq101n : st / 98304 ≠ 101 := by intro h; exact hq101 (by simpa [stepsPerSym, regBound] using h)
      simp [hq101n]
      rw [decodeState_encodeState (min (st % regBound / 54) 101) 0 0
        (by decide) (by norm_num)]
      dsimp [stepsPerSym, regBound]
      norm_num

/-- 相位 ∈ [3,10]：下一相位 = 相位+1 ≥ 4 ≥ 3。 -/
lemma transition4_phase_ge3_ne11_next_ge3 (st : ℕ) (s : F4) (r : CBTMTransResult)
    (hr : r ∈ transition4 st s)
    (hph12 : (decodeState st).2.1 < 12)
    (hge3 : 3 ≤ (decodeState st).2.1)
    (hne11 : (decodeState st).2.1 ≠ 11) :
    3 ≤ (decodeState r.nextState).2.1 := by
  have hsucc := transition4_phase_succ st s r hr hph12
    (by intro h; dsimp [decodeState, stepsPerSym, regBound] at h hge3; omega)
  rw [hsucc]
  have hlt : (decodeState st).2.1 + 1 < 12 := by omega
  rw [Nat.mod_eq_of_lt hlt]
  omega

/-- 接受路径长度 ≡ 0 (mod 12)：起点相位 0、接受态相位 0、每步相位 +1 (mod 12)。 -/
lemma accept_path_length_mod12 {w : List F4} {π : ComputationPath}
    {cfg : CBTMConfig subsetSumCBTM w}
    (h : TapeSteps subsetSumCBTM w (initialConfig subsetSumCBTM w) π cfg)
    (hacc : cfg.state ∈ acceptStates4) :
    π.length % 12 = 0 := by
  have hph : (decodeState cfg.state).2.1 = π.length % 12 ∧
      (decodeState cfg.state).2.2 < regBound ∧
      ((decodeState cfg.state).2.1 < 3 →
        (decodeState cfg.state).2.2 < 4 ^ (decodeState cfg.state).2.1) := by
    clear hacc
    induction h with
    | nil =>
        simp [initialConfig, subsetSumCBTM, decodeState, encodeState, qBound, stepsPerSym, regBound]
    | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
        rcases ih with ⟨ihph, ihreg, ih64⟩
        have htrans' : step.result ∈ transition4 cfg₁.state step.readSym := by
          rw [hread]
          exact htrans
        have hbufOK : (cfg₁.state / regBound) % stepsPerSym < 3 →
            cfg₁.state % regBound +
              bufOf3s ((cfg₁.state / regBound) % stepsPerSym) step.readSym (cfg₁.state % regBound) < regBound := by
          intro hlt3
          dsimp [decodeState, stepsPerSym, regBound] at ih64
          have h64 : cfg₁.state % regBound < 4 ^ ((cfg₁.state / regBound) % stepsPerSym) :=
            ih64 hlt3
          have hp012 : (cfg₁.state / regBound) % stepsPerSym = 0 ∨
              (cfg₁.state / regBound) % stepsPerSym = 1 ∨
              (cfg₁.state / regBound) % stepsPerSym = 2 := by
            have hlt' : (cfg₁.state / 8192) % 12 < 3 := by
              dsimp [stepsPerSym, regBound] at hlt3
              exact Nat.lt_of_le_of_lt (Nat.le_of_lt_succ hlt3) (by norm_num)
            simpa [stepsPerSym, regBound] using mod12_lt3_eq (cfg₁.state / 8192) hlt'
          have hpow : 4 ^ ((cfg₁.state / regBound) % stepsPerSym) ≤ 16 := by
            rcases hp012 with h2 | h1 | h0
            · rw [h2]; norm_num
            · rw [h1]; norm_num
            · rw [h0]; norm_num
          have hbuf : bufOf3s ((cfg₁.state / regBound) % stepsPerSym) step.readSym
                (cfg₁.state % regBound) ≤ 48 := by
            unfold bufOf3s
            have hle2 : (cfg₁.state / regBound) % stepsPerSym ≤ 2 := by
              dsimp [stepsPerSym] at hlt3
              omega
            rcases step.readSym with ⟨rs, is⟩
            cases rs <;> cases is <;> simp [F4.zero, F4.one, F4.alpha, F4.beta]
            all_goals first | done | nlinarith [hpow]
          dsimp [regBound, stepsPerSym] at h64 hpow hbuf ⊢
          omega
        have hstep := transition4_phase_succ cfg₁.state step.readSym step.result htrans'
          (by rw [ihph]; exact Nat.mod_lt _ (by decide : 0 < 12)) hbufOK
        dsimp [stepConfig]
        rw [hstep]
        rw [ihph]
        constructor
        · -- 第一分量：相位等式
          simp [Nat.add_mod]
        · constructor
          · -- reg 分量 < regBound：decodeState 的第三分量恒 < regBound
            dsimp [decodeState, stepsPerSym, regBound]
            exact Nat.mod_lt _ (by decide : 0 < regBound)
          · -- 相位 < 3 ⟹ reg < 4^相位（新状态维持）
            intro hlt3'
            rw [Nat.add_mod] at hlt3'
            by_cases hlt3 : (decodeState cfg₁.state).2.1 < 3
            · have h64 : (decodeState cfg₁.state).2.2 < 4 ^ (decodeState cfg₁.state).2.1 :=
                ih64 hlt3
              have hreg := transition4_read_phase_reg_lt cfg₁.state step.readSym step.result
                htrans' hlt3 h64
              rw [← ihph, ← hstep]
              exact hreg
            · have hlt12 : (decodeState cfg₁.state).2.1 < 12 := by
                rw [ihph]
                exact Nat.mod_lt _ (by decide : 0 < 12)
              by_cases h11 : (decodeState cfg₁.state).2.1 = 11
              · have hz := transition4_phase11_reg_eq_zero cfg₁.state step.readSym step.result
                  htrans' h11
                rw [← ihph, ← hstep]
                rw [hz.1, hz.2]
                norm_num
              · have hge := transition4_phase_ge3_ne11_next_ge3 cfg₁.state step.readSym step.result
                  htrans' hlt12 (by omega) h11
                rw [← ihph, ← hstep]
                first | done | omega
  -- hacc：接受态 phase = 0
  have hacc' : (decodeState cfg.state).2.1 = 0 := by
    rcases Finset.mem_image.mp hacc with ⟨reg, hreg, h⟩
    rw [← h]
    dsimp [decodeState, encodeState, qBound, stepsPerSym, regBound, VerifierSym.qAccept]
    simp [Finset.mem_range] at hreg
    dsimp [regBound] at hreg
    omega
  omega

-- ======================================================================
-- §8 接受路径的逐块结构
-- ======================================================================

/-- 路径相位纪律（含中途）：终点三元组 + 每一步起点的三元组。 -/
lemma path_phase_at {w : List F4} {π : ComputationPath}
    {cfg : CBTMConfig subsetSumCBTM w}
    (h : TapeSteps subsetSumCBTM w (initialConfig subsetSumCBTM w) π cfg) :
    ((decodeState cfg.state).2.1 = π.length % 12 ∧
     (decodeState cfg.state).2.2 < regBound ∧
     ((decodeState cfg.state).2.1 < 3 →
      (decodeState cfg.state).2.2 < 4 ^ (decodeState cfg.state).2.1)) ∧
    (∀ m (hm : m < π.length),
      (decodeState (π.get ⟨m, hm⟩).fromState).2.1 = m % 12 ∧
      (decodeState (π.get ⟨m, hm⟩).fromState).2.2 < regBound ∧
      ((decodeState (π.get ⟨m, hm⟩).fromState).2.1 < 3 →
       (decodeState (π.get ⟨m, hm⟩).fromState).2.2 <
         4 ^ (decodeState (π.get ⟨m, hm⟩).fromState).2.1)) := by
  induction h with
  | nil =>
      constructor
      · simp [initialConfig, subsetSumCBTM, decodeState, encodeState, qBound, stepsPerSym, regBound]
      · intro m hm
        have hm' : m < 0 := by simpa using hm
        linarith
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      rcases ih with ⟨ihEnd, ihMid⟩
      have htrans' : step.result ∈ transition4 cfg₁.state step.readSym := by
        rw [hread]
        exact htrans
      have hbufOK : (cfg₁.state / regBound) % stepsPerSym < 3 →
          cfg₁.state % regBound +
            bufOf3s ((cfg₁.state / regBound) % stepsPerSym) step.readSym (cfg₁.state % regBound) < regBound := by
        intro hlt3
        dsimp [decodeState, stepsPerSym, regBound] at ihEnd
        have h64 : cfg₁.state % regBound < 4 ^ ((cfg₁.state / regBound) % stepsPerSym) :=
          ihEnd.2.2 hlt3
        have hp012 : (cfg₁.state / regBound) % stepsPerSym = 0 ∨
            (cfg₁.state / regBound) % stepsPerSym = 1 ∨
            (cfg₁.state / regBound) % stepsPerSym = 2 := by
          have hlt' : (cfg₁.state / 8192) % 12 < 3 := by
            dsimp [stepsPerSym, regBound] at hlt3
            exact Nat.lt_of_le_of_lt (Nat.le_of_lt_succ hlt3) (by norm_num)
          simpa [stepsPerSym, regBound] using mod12_lt3_eq (cfg₁.state / 8192) hlt'
        have hpow : 4 ^ ((cfg₁.state / regBound) % stepsPerSym) ≤ 16 := by
          rcases hp012 with h2 | h1 | h0
          · rw [h2]; norm_num
          · rw [h1]; norm_num
          · rw [h0]; norm_num
        have hbuf : bufOf3s ((cfg₁.state / regBound) % stepsPerSym) step.readSym
              (cfg₁.state % regBound) ≤ 48 := by
          unfold bufOf3s
          have hle2 : (cfg₁.state / regBound) % stepsPerSym ≤ 2 := by
            dsimp [stepsPerSym] at hlt3
            omega
          rcases step.readSym with ⟨rs, is⟩
          cases rs <;> cases is <;> simp [F4.zero, F4.one, F4.alpha, F4.beta]
          all_goals first | done | nlinarith [hpow]
        dsimp [regBound, stepsPerSym] at h64 hpow hbuf ⊢
        omega
      have hstep := transition4_phase_succ cfg₁.state step.readSym step.result htrans'
        (by rw [ihEnd.1]; exact Nat.mod_lt _ (by decide : 0 < 12)) hbufOK
      have hend : (decodeState (stepConfig cfg₁ step.result).state).2.1 = (π₀ ++ [step]).length % 12 ∧
          (decodeState (stepConfig cfg₁ step.result).state).2.2 < regBound ∧
          ((decodeState (stepConfig cfg₁ step.result).state).2.1 < 3 →
           (decodeState (stepConfig cfg₁ step.result).state).2.2 <
             4 ^ (decodeState (stepConfig cfg₁ step.result).state).2.1) := by
        dsimp [stepConfig]
        rw [hstep]
        rw [ihEnd.1]
        constructor
        · -- 第一分量：相位等式
          simp [Nat.add_mod]
        · constructor
          · -- reg 分量 < regBound：恒真
            dsimp [decodeState, stepsPerSym, regBound]
            exact Nat.mod_lt _ (by decide : 0 < regBound)
          · -- 相位 < 3 ⟹ reg < 4^相位（新状态维持）
            intro hlt3'
            rw [Nat.add_mod] at hlt3'
            by_cases hlt3 : (decodeState cfg₁.state).2.1 < 3
            · have h64 : (decodeState cfg₁.state).2.2 < 4 ^ (decodeState cfg₁.state).2.1 :=
                ihEnd.2.2 hlt3
              have hreg := transition4_read_phase_reg_lt cfg₁.state step.readSym step.result
                htrans' hlt3 h64
              rw [← ihEnd.1, ← hstep]
              exact hreg
            · have hlt12 : (decodeState cfg₁.state).2.1 < 12 := by
                rw [ihEnd.1]
                exact Nat.mod_lt _ (by decide : 0 < 12)
              by_cases h11 : (decodeState cfg₁.state).2.1 = 11
              · have hz := transition4_phase11_reg_eq_zero cfg₁.state step.readSym step.result
                  htrans' h11
                rw [← ihEnd.1, ← hstep]
                rw [hz.1, hz.2]
                norm_num
              · have hge := transition4_phase_ge3_ne11_next_ge3 cfg₁.state step.readSym step.result
                  htrans' hlt12 (by omega) h11
                rw [← ihEnd.1, ← hstep]
                first | done | omega
      constructor
      · exact hend
      · intro m hm
        have hm' : m < (π₀ ++ [step]).length := by simpa using hm
        have hlt_or : m < π₀.length ∨ m = π₀.length := by
          simp at hm'
          omega
        rcases hlt_or with hlt | heq
        · have hg : (π₀ ++ [step]).get ⟨m, hm⟩ = π₀.get ⟨m, hlt⟩ := by
            exact List.getElem_append_left hlt
          rw [hg]
          exact ihMid m hlt
        · subst m
          have hg : (π₀ ++ [step]).get ⟨π₀.length, hm⟩ = step := by
            simpa using (List.getElem_append_right (α := TransitionStep) (as := π₀)
              (bs := [step]) (i := π₀.length) (Nat.le_refl π₀.length))
          simpa [hg, hfrom] using ihEnd

/-- 接受路径第 m 步起点的相位 = m % 12（中途相位纪律的相位分量）。 -/
lemma path_phase_at_phase {w : List F4} {π : ComputationPath}
    {cfg : CBTMConfig subsetSumCBTM w}
    (h : TapeSteps subsetSumCBTM w (initialConfig subsetSumCBTM w) π cfg)
    (m : ℕ) (hm : m < π.length) :
    (decodeState (π.get ⟨m, hm⟩).fromState).2.1 = m % 12 :=
  ((path_phase_at h).2 m hm).1

/-- 第 k 块（步 k*12 .. k*12+11）起点的相位 = 0。 -/
lemma block_start_phase_zero {w : List F4} {π : ComputationPath}
    {cfg : CBTMConfig subsetSumCBTM w}
    (h : TapeSteps subsetSumCBTM w (initialConfig subsetSumCBTM w) π cfg)
    (k : ℕ) (hk : k * 12 < π.length) :
    (decodeState (π.get ⟨k * 12, hk⟩).fromState).2.1 = 0 := by
  have hph := path_phase_at_phase h (k * 12) hk
  rw [hph]
  rw [Nat.mul_comm]
  exact Nat.mul_mod_right 12 k

-- ======================================================================
-- §8' 块级映射（从 CBTM5 搬入）：4F4 字符 ↔ 4×F4 集合体；Sym 路径 → 块路径
-- ======================================================================

-- ======================================================================
-- §1 块级移动：字符层 ±1 ↔ 格层 ±4
-- ======================================================================

/-- 块级移动：Sym 步的移动方向对应的 4 格净移动（4 个 F4 一起动）。 -/
def blockMove (d : Dir) : ℤ :=
  match d with
  | Dir.R => 4
  | Dir.L => -4
  | Dir.S => 0

/-- blockMove 恰是 4 倍的字符移动。 -/
lemma blockMove_eq_four_toInt (d : Dir) : blockMove d = 4 * d.toInt := by
  cases d <;> rfl

-- ======================================================================
-- §2 块级移动对应：expand 12 步的净移动 = blockMove（头 4 格一起动）
-- ======================================================================

/-- 一个 Sym 步展开后，12 步的净效果：带头按 blockMove 移动（4 格对齐保持）。 -/
theorem expand_headPos_blockMove (q : ℕ) (sym : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, sym)) (hqle : q ≤ 101)
    (hbranch : Sym.isBranch sym → q = 2) (hrs : r.nextState < 101)
    (w : List F4) (cfgc : CBTMConfig subsetSumCBTM w) (cfgs : SymConfig) (p : ℤ)
    (hcorr : blockCorrespond cfgc cfgs)
    (hst : cfgc.state = encodeState q 0 0)
    (hp : cfgc.headPos = 4 * p)
    (hread : cfgs.tape p = sym) :
    ∃ πb : ComputationPath, ∃ cfgc' : CBTMConfig subsetSumCBTM w,
      TapeSteps subsetSumCBTM w cfgc πb cfgc' ∧
      πb.length = 12 ∧
      cfgc'.headPos = cfgc.headPos + blockMove r.moveDir := by
  rcases expand_sym_step q sym r hr hqle hbranch hrs w cfgc cfgs p hcorr hst hp hread
    with ⟨πb, cfgc', hsteps, hlen, hcorr', _hg3⟩
  refine ⟨πb, cfgc', hsteps, hlen, ?_⟩
  -- blockCorrespond 的 headPos 分量（4 格对齐）：
  have hh' := hcorr'.2.1
  dsimp [symStepConfig] at hh'
  have hh0 := hcorr.2.1
  -- 目标：4 * (cfgs.headPos + r.moveDir.toInt) = 4 * cfgs.headPos + 4 * r.moveDir.toInt
  rw [hh']
  rw [Int.mul_add]
  rw [← hh0]
  rw [blockMove_eq_four_toInt]

-- ======================================================================
-- §3 块级读写对应：当前块 4 格 = symTo4F4 r.writeSym（4 格一起写）
-- ======================================================================

/-- 12 步结束后，块 p 的 4 格恰为 writeSym 的编码（集合体整体写回）。 -/
theorem expand_block_write_eq (q : ℕ) (sym : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, sym)) (hqle : q ≤ 101)
    (hbranch : Sym.isBranch sym → q = 2) (hrs : r.nextState < 101)
    (w : List F4) (cfgc : CBTMConfig subsetSumCBTM w) (cfgs : SymConfig) (p : ℤ)
    (hcorr : blockCorrespond cfgc cfgs)
    (hst : cfgc.state = encodeState q 0 0)
    (hp : cfgc.headPos = 4 * p)
    (hread : cfgs.tape p = sym) :
    ∃ πb : ComputationPath, ∃ cfgc' : CBTMConfig subsetSumCBTM w,
      TapeSteps subsetSumCBTM w cfgc πb cfgc' ∧
      πb.length = 12 ∧
      ∀ (j : ℕ) (_ : j < 4), cfgc'.tapeAt (4 * p + j) = (symTo4F4 r.writeSym).getD j F4.zero := by
  rcases expand_sym_step q sym r hr hqle hbranch hrs w cfgc cfgs p hcorr hst hp hread
    with ⟨πb, cfgc', hsteps, hlen, hcorr', _hg3⟩
  refine ⟨πb, cfgc', hsteps, hlen, ?_⟩
  intro j hj
  -- blockCorrespond 的磁带分量（块 p 的 4 格 = symStepConfig 写后 tape p 的编码）：
  have ht := hcorr'.2.2 p j hj
  -- 带头确实在 p（由 hcorr 的 headPos 分量 + hp）：
  have hp_sym : cfgs.headPos = p := by
    have hh0 := hcorr.2.1
    rw [hh0] at hp
    omega
  dsimp [symStepConfig] at ht
  rw [if_pos hp_sym.symm] at ht
  exact ht

-- ======================================================================
-- §4 块级单步等价：expand 的净效果 = symStepConfig（状态/头/块三位一体）
-- ======================================================================

/-- 块级单步：12 步块的净效果与 Sym 层单步完全一致。 -/
theorem expand_net_effect (q : ℕ) (sym : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, sym)) (hqle : q ≤ 101)
    (hbranch : Sym.isBranch sym → q = 2) (hrs : r.nextState < 101)
    (w : List F4) (cfgc : CBTMConfig subsetSumCBTM w) (cfgs : SymConfig) (p : ℤ)
    (hcorr : blockCorrespond cfgc cfgs)
    (hst : cfgc.state = encodeState q 0 0)
    (hp : cfgc.headPos = 4 * p)
    (hread : cfgs.tape p = sym) :
    ∃ πb : ComputationPath, ∃ cfgc' : CBTMConfig subsetSumCBTM w,
      TapeSteps subsetSumCBTM w cfgc πb cfgc' ∧
      πb.length = 12 ∧
      blockCorrespond cfgc' (symStepConfig cfgs r) := by
  -- 计划：直接由 expand_sym_step（CBTM2）给出——这就是"块级单步"的完整陈述（单向：Sym 步 → 12 步块）。
  rcases expand_sym_step q sym r hr hqle hbranch hrs w cfgc cfgs p hcorr hst hp hread
    with ⟨πb, cfgc', hsteps, hlen, hcorr', hg3⟩
  exact ⟨πb, cfgc', hsteps, hlen, hcorr'⟩

-- ======================================================================
-- §5 分支对应：块内唯一分叉点 ↔ Sym 层 α/β 双分支（sel/nosel 集合体）
-- ======================================================================

/-- 合成步（im=true 读、q=2）的双结果恰为 sel/nosel 两块集合体，与 α/β 一一对应。 -/
theorem branch_step_is_sel_nosel (st : ℕ) (s : F4)
    (hphase3 : (st / regBound) % stepsPerSym = 3) (him : F4.im s)
    (hq2 : min (st / (stepsPerSym * regBound)) 101 = 2)
    (hsym : ∃ sym : Sym, symOf4F4 ((f4ofBuf (st % regBound)).1) ((f4ofBuf (st % regBound)).2.1)
        ((f4ofBuf (st % regBound)).2.2) s = some sym ∧ Sym.isBranch sym ∧
        (f4ofBuf (st % regBound)).1 = F4.zero)
    (hsre : F4.re s = false) :
    transition4 st s =
      {CBTMTransResult.mk (encodeState 2 4 (encodeResult (SymTransResult.mk 2 Sym.sel Dir.R)))
         ((symTo4F4 Sym.sel).getLastD F4.zero) Dir.L,
       CBTMTransResult.mk (encodeState 2 4 (encodeResult (SymTransResult.mk 2 Sym.nosel Dir.R)))
         ((symTo4F4 Sym.nosel).getLastD F4.zero) Dir.L} := by
  rcases hsym with ⟨sym, hso, _hbr, hc0⟩
  dsimp [transition4, decodeState, stepsPerSym, regBound] at hq2 ⊢
  rw [hc0] at hso
  simp [hphase3, him, hq2, hso, hc0, hsre]

/-- 块内其余 11 步确定性（im=false 读 → card=1）：验证过程无分叉。 -/
theorem block_deterministic_except_branch (st : ℕ) (s : F4) (him : F4.im s = false) :
    (transition4 st s).card = 1 := by
  -- 计划：transition4_card_one_of_im_false（CBTM.lean 已证）——块内非分支步确定性。
  exact transition4_card_one_of_im_false st s him

-- ======================================================================
-- §6 路径层单向提升：字符版 Sym 路径 → F4 版块路径
-- ======================================================================

/-- GoodBlockPath 的传递性（块路径拼接：后加）。 -/
lemma GoodBlockPath_append (w : List F4) (cfgc cfgm cfgc' : CBTMConfig subsetSumCBTM w)
    (π₁ π₂ : ComputationPath) :
    GoodBlockPath w cfgc π₁ cfgm → GoodBlockPath w cfgm π₂ cfgc' →
    GoodBlockPath w cfgc (π₁ ++ π₂) cfgc' := by
  intro h₁
  induction h₁ with
  | nil =>
      intro h₂
      simpa using h₂
  | cons cfgc₀ cfgm₀ cfgc₀' πm₀ π₀ cfgs₀ p₀ q₀ sym₀ r₀ hblock₀ hrest₀ ih =>
      intro h₂
      -- (πm₀ ++ π₀) ++ π₂ = πm₀ ++ (π₀ ++ π₂)
      rw [List.append_assoc]
      exact GoodBlockPath.cons cfgc₀ cfgm₀ cfgc' πm₀ (π₀ ++ π₂) cfgs₀ p₀ q₀ sym₀ r₀ hblock₀ (ih h₂)

/-- 单向提升：Sym 层一条合法接受路径 ⟹ F4 层一条 GoodBlockPath。
（每步 Sym 转移用 expand_sym_step 展开成 12 步块，逐块拼接。）
前提（Sym 路径的良构性，对应 CBTM4 §6 不变式的分量）：
- 每步 fromState ≤ 101（expand 需要）；
- 分支读只出现在 q = 2（v2：删除读/写标记值位前提，往返引理对任意符号成立）。 -/
theorem symPath_to_blockPath (input : List Sym)
    {πs : List SymStep} {cfgs : SymConfig}
    (hs : SymSteps VerifierSym.transition (symInitialConfig input) πs cfgs)
    (hacc : cfgs.state = VerifierSym.qAccept)
    (hsteps_ok : ∀ step ∈ πs, step.fromState ≤ 101)
    (hbranch : ∀ step ∈ πs, Sym.isBranch step.readSym → step.fromState = 2) :
    ∃ πc : ComputationPath, ∃ cfgc : CBTMConfig subsetSumCBTM (flat4F4 input),
      GoodBlockPath (flat4F4 input) (initialConfig subsetSumCBTM (flat4F4 input)) πc cfgc ∧
      blockCorrespond cfgc cfgs ∧
      cfgc.state = encodeState VerifierSym.qAccept 0 0 := by
  -- 先证不带 hacc 的通用版（归纳维护 GoodBlockPath + blockCorrespond + 状态相位 0 对应）
  -- 接受路径上无 101 步：终点 qAccept=100 且 101 吸收 → 每步 nextState ≠ 101（在 clear hacc 前取出）。
  have hno101 : ∀ step ∈ πs, step.result.nextState ≠ 101 :=
    symSteps_accept_no_101 hs hacc
  have hgen : ∃ πc : ComputationPath, ∃ cfgc : CBTMConfig subsetSumCBTM (flat4F4 input),
      GoodBlockPath (flat4F4 input) (initialConfig subsetSumCBTM (flat4F4 input)) πc cfgc ∧
      blockCorrespond cfgc cfgs ∧ cfgc.state = encodeState cfgs.state 0 0 := by
    clear hacc
    induction hs with
    | nil =>
        refine ⟨[], initialConfig subsetSumCBTM (flat4F4 input), GoodBlockPath.nil _,
          initialBlockCorrespond input, ?_⟩
        rfl
    | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
        have hok0 : ∀ step' ∈ π₀, step'.fromState ≤ 101 := by
          intro st hst
          exact hsteps_ok st (by simp [hst])
        have hbr0 : ∀ step' ∈ π₀, Sym.isBranch step'.readSym → step'.fromState = 2 := by
          intro st hst
          exact hbranch st (by simp [hst])
        have hno101₀ : ∀ step ∈ π₀, step.result.nextState ≠ 101 := by
          intro st hst
          exact hno101 st (by simp [hst])
        rcases ih hok0 hbr0 hno101₀ with ⟨πc, cfgc₁, hbp, hcorr₁, hst₁⟩
        have hok := hsteps_ok step (by simp)
        have hbr := hbranch step (by simp)
        have hqle : cfg₁.state ≤ 101 := by
          simpa [hfrom] using hok
        have hbr' : Sym.isBranch (cfg₁.tape cfg₁.headPos) → cfg₁.state = 2 := by
          intro hb
          rw [← hread] at hb
          simpa [hfrom] using hbr hb
        have hvalid_sym' : (cfg₁.tape cfg₁.headPos).2 = true →
            (cfg₁.tape cfg₁.headPos).1 = SymKind.data0 ∨ (cfg₁.tape cfg₁.headPos).1 = SymKind.data1 ∨
            (cfg₁.tape cfg₁.headPos).1 = SymKind.alpha ∨ (cfg₁.tape cfg₁.headPos).1 = SymKind.consumed ∨
            (cfg₁.tape cfg₁.headPos).1 = SymKind.boundary ∨ (cfg₁.tape cfg₁.headPos).1 = SymKind.sel ∨
            (cfg₁.tape cfg₁.headPos).1 = SymKind.nosel ∨ (cfg₁.tape cfg₁.headPos).1 = SymKind.beta := by
          intro hm
          rcases (cfg₁.tape cfg₁.headPos).1 with k <;> cases k <;> simp at hm ⊢
        have hvalid_r' : step.result.writeSym.2 = true →
            step.result.writeSym.1 = SymKind.data0 ∨ step.result.writeSym.1 = SymKind.data1 ∨
            step.result.writeSym.1 = SymKind.alpha ∨ step.result.writeSym.1 = SymKind.consumed ∨
            step.result.writeSym.1 = SymKind.boundary ∨ step.result.writeSym.1 = SymKind.sel ∨
            step.result.writeSym.1 = SymKind.nosel ∨ step.result.writeSym.1 = SymKind.beta := by
          intro hm
          rcases step.result.writeSym.1 with k <;> cases k <;> simp at hm ⊢
        have htrans' : step.result ∈ VerifierSym.transition (cfg₁.state, cfg₁.tape cfg₁.headPos) := by
          simpa [hfrom, hread] using htrans
        -- 接受路径上无 101 步（hno101）+ nextState ≤ 101 → nextState < 101（expand_sym_step v3 前提）。
        have hrs : step.result.nextState < 101 := by
          have hne : step.result.nextState ≠ 101 :=
            hno101 step (by simp)
          have hle : step.result.nextState ≤ 101 :=
            transition_nextState_le101 cfg₁.state (cfg₁.tape cfg₁.headPos) hqle step.result htrans'
          omega
        rcases expand_sym_step cfg₁.state (cfg₁.tape cfg₁.headPos) step.result htrans' hqle hbr' hrs
          (flat4F4 input) cfgc₁ cfg₁ cfg₁.headPos hcorr₁ (by simpa [hfrom] using hst₁) hcorr₁.2.1 rfl
          with ⟨πm, cfgm, hsteps_m, hlen_m, hcorr_m, hg3⟩
        have hg3' : (πm.get ⟨3, by omega⟩).result = CBTMTransResult.mk
            (encodeState step.result.nextState 4 (encodeResult step.result))
            ((symTo4F4 step.result.writeSym).getLastD F4.zero) Dir.L := by
          have hg : πm.getD 3 (TransitionStep.mk (encodeState step.result.nextState 4 (encodeResult step.result))
              ((symTo4F4 step.result.writeSym).getLastD F4.zero)
              (CBTMTransResult.mk (encodeState step.result.nextState 4 (encodeResult step.result))
                ((symTo4F4 step.result.writeSym).getLastD F4.zero) Dir.L)) =
              πm.get ⟨3, by omega⟩ :=
            List.getD_eq_get πm (TransitionStep.mk (encodeState step.result.nextState 4 (encodeResult step.result))
              ((symTo4F4 step.result.writeSym).getLastD F4.zero)
              (CBTMTransResult.mk (encodeState step.result.nextState 4 (encodeResult step.result))
                ((symTo4F4 step.result.writeSym).getLastD F4.zero) Dir.L)) ⟨3, by omega⟩
          rw [hg] at hg3
          exact hg3
        have hh14 : cfgm.headPos = 4 * cfg₁.headPos + 4 * (step.result.moveDir).toInt := by
          dsimp [symStepConfig] at hcorr_m
          rw [hcorr_m.2.1]
          rw [Int.mul_add]
        have hblock : GoodBlock (flat4F4 input) cfgc₁ πm cfgm cfg₁ cfg₁.headPos cfg₁.state
            (cfg₁.tape cfg₁.headPos) step.result :=
          ⟨hsteps_m, hlen_m, ⟨
          by simpa [hfrom] using hst₁,
          hcorr₁.2.1,
          hcorr₁,
          rfl,
          by simpa [hfrom] using hok,
          hbr',
          hvalid_sym',
          hg3',
          hvalid_r',
          htrans',
          by simpa [symStepConfig] using hcorr_m.1,
          hh14⟩⟩
        have hsingle : GoodBlockPath (flat4F4 input) cfgc₁ πm cfgm := by
          simpa using (GoodBlockPath.cons cfgc₁ cfgm cfgm πm [] cfg₁ cfg₁.headPos cfg₁.state
            (cfg₁.tape cfg₁.headPos) step.result hblock (GoodBlockPath.nil cfgm))
        refine ⟨πc ++ πm, cfgm, GoodBlockPath_append (flat4F4 input)
          (initialConfig subsetSumCBTM (flat4F4 input)) cfgc₁ cfgm πc πm hbp hsingle, hcorr_m, ?_⟩
        · -- 归纳末态：cfgm.state = encodeState cfgs.state 0 0（cfgs = symStepConfig cfg₁ step.result）
          simpa [symStepConfig] using hcorr_m.1
  -- 收尾：hacc 给接受态
  rcases hgen with ⟨πc, cfgc, hbp, hcorr, hst⟩
  refine ⟨πc, cfgc, hbp, hcorr, ?_⟩
  rw [hst, ← hacc]

-- ======================================================================
-- §9 分解定理：接受路径 ⟹ GoodBlockPath（条件版：无陷阱）
-- ======================================================================

/-- 列表尾唯一性：a ++ [x] = b ++ [y] → a = b ∧ x = y。
    （Reverse2 的 Mp.append_right_cancel 的 SymToF4 版，供本模块使用。） -/
lemma append_right_cancel {α : Type} {a b : List α} {x y : α}
    (h : a ++ [x] = b ++ [y]) : a = b ∧ x = y := by
  have hrev := congrArg List.reverse h
  rw [List.reverse_append, List.reverse_append] at hrev
  simp at hrev
  exact ⟨hrev.2, hrev.1⟩

/-- 路径第 k 步的转移合法（按步自身字段表述）。 -/
lemma tapeSteps_step_trans {M : CBTM} {input : List F4} {cfg₀ : CBTMConfig M input}
    {π : ComputationPath} {cfg : CBTMConfig M input}
    (h : TapeSteps M input cfg₀ π cfg) (k : ℕ) (hk : k < π.length) :
    ∃ pos : ℤ, (π.get ⟨k, hk⟩).result ∈ M.transition ((π.get ⟨k, hk⟩).fromState, (π.get ⟨k, hk⟩).readSym, pos) := by
  induction h generalizing k with
  | nil =>
      simp at hk
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      have hlt_or : k < π₀.length ∨ k = π₀.length := by
        have hk' : k < (π₀ ++ [step]).length := by simpa using hk
        simp at hk'
        omega
      rcases hlt_or with hlt | heq
      · have hg : (π₀ ++ [step]).get ⟨k, hk⟩ = π₀.get ⟨k, hlt⟩ := by
          simpa [List.get] using (List.getElem_append_left hlt)
        rw [hg]
        exact ih k hlt
      · subst k
        have hg : (π₀ ++ [step]).get ⟨π₀.length, hk⟩ = step := by
          simpa [List.get, Nat.sub_add_cancel] using
            (List.getElem_append_right (Nat.le_refl _) (by simpa [Nat.sub_add_cancel] using hk))
        rw [hg, hread, hfrom]
        exact ⟨cfg₁.headPos, htrans⟩

/-- 非空路径末步结果的 nextState = 终点状态。 -/
lemma tapeSteps_last_result_nextState {M : CBTM} {input : List F4} {cfg₀ : CBTMConfig M input}
    {π : ComputationPath} {cfg : CBTMConfig M input}
    (h : TapeSteps M input cfg₀ π cfg) (hπ : π ≠ []) :
    (π.getLast (by simpa using hπ)).result.nextState = cfg.state := by
  cases h with
  | nil => exact (hπ rfl).elim
  | cons π₀ step cfg₁ hprev hfrom hread htrans =>
      rw [List.getLast_append_singleton]
      rfl

/-- 同一路径的终点唯一（TapeSteps 的函数性）。 -/
lemma tapeSteps_unique {M : CBTM} {input : List F4} {cfg₀ : CBTMConfig M input}
    {π : ComputationPath} {cfg cfg' : CBTMConfig M input}
    (h : TapeSteps M input cfg₀ π cfg) (h' : TapeSteps M input cfg₀ π cfg') : cfg = cfg' := by
  induction h generalizing cfg' with
  | nil =>
      have hcfg' : cfg' = cfg₀ := tapeSteps_empty h' rfl
      rw [hcfg']
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      have hne : π₀ ++ [step] ≠ [] := by
        intro h
        have := congrArg List.length h
        simp at this
      rcases tapeSteps_split_last h' hne with
        ⟨step', π₀', cfg₁', hπeq, hprev', hfrom', hread', htrans', hcfg'⟩
      have hc := append_right_cancel hπeq
      rcases hc with ⟨hπ₀, hstep⟩
      subst π₀'
      subst step'
      have hcfg₁ : cfg₁ = cfg₁' := ih hprev'
      subst cfg₁'
      exact hcfg'.symm

/-- 路径第 k+1 步的 fromState = 第 k 步结果的 nextState。 -/
lemma tapeSteps_fromState_succ {M : CBTM} {input : List F4} {cfg₀ : CBTMConfig M input}
    {π : ComputationPath} {cfg : CBTMConfig M input}
    (h : TapeSteps M input cfg₀ π cfg) (k : ℕ) (hk : k + 1 < π.length) :
    (π.get ⟨k + 1, hk⟩).fromState = ((π.get ⟨k, by omega⟩).result).nextState := by
  induction h generalizing k with
  | nil =>
      simp at hk
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      have hk' : k + 1 < (π₀ ++ [step]).length := by simpa using hk
      simp at hk'
      have hlt_or : k + 1 < π₀.length ∨ k + 1 = π₀.length := by omega
      rcases hlt_or with hlt | heq
      · have hg1 : (π₀ ++ [step]).get ⟨k + 1, hk⟩ = π₀.get ⟨k + 1, hlt⟩ := by
          simpa [List.get] using (List.getElem_append_left hlt)
        have hg2 : (π₀ ++ [step]).get ⟨k, by omega⟩ = π₀.get ⟨k, by omega⟩ := by
          simpa [List.get] using (List.getElem_append_left (by omega))
        rw [hg1, hg2]
        exact ih k hlt
      · have hg1 : (π₀ ++ [step]).get ⟨k + 1, hk⟩ = step := by
          simpa [List.get, heq] using
            (List.getElem_append_right (by omega : π₀.length ≤ k + 1) (by simpa using hk))
        have hne : π₀ ≠ [] := by
          intro hπe
          rw [hπe] at heq
          simp at heq
        have hlast := tapeSteps_last_result_nextState hprev hne
        have hg2 : (π₀ ++ [step]).get ⟨k, by omega⟩ = π₀.get ⟨k, by omega⟩ := by
          simpa [List.get] using (List.getElem_append_left (by omega : k < π₀.length))
        have hgetlast : π₀.get ⟨k, by omega⟩ = π₀.getLast hne := by
          rw [List.getLast_eq_getElem]
          congr
          omega
        rw [hg1, hg2, hgetlast, hlast]
        exact hfrom

/-- symTo4F4 前 3 格（kindBits 编码）的虚部恒 false。 -/
lemma symTo4F4_getD_im_false_of_lt3 (s : Sym) (j : ℕ) (hj : j < 3) :
    F4.im ((symTo4F4 s).getD j F4.zero) = false := by
  rcases s with ⟨k, mk⟩
  cases k <;> interval_cases j <;> simp [symTo4F4, Sym.kindBits, F4.im, List.getD]

/-- symTo4F4 第 4 格（末格）的实部 = 标记位。 -/
lemma symTo4F4_getD3_re_eq_mk (s : Sym) :
    F4.re ((symTo4F4 s).getD 3 F4.zero) = s.2 := by
  rcases s with ⟨k, mk⟩
  cases k <;> cases mk <;> simp [symTo4F4, Sym.kindBits, F4.re, F4.im, List.getD]

/-- symTo4F4 第 4 格（末格）的虚部 = 分支位（isBranch）。 -/
lemma symTo4F4_getD3_im_eq_isBranch (s : Sym) :
    F4.im ((symTo4F4 s).getD 3 F4.zero) = SymKind.isBranch s.1 := by
  rcases s with ⟨k, mk⟩
  cases k <;> cases mk <;> simp [symTo4F4, Sym.kindBits, SymKind.isBranch, F4.re, F4.im, List.getD]

end SymToF4
end Mp
