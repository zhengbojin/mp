/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import Mp.SubsetSumVerifierReverse7L3
import Mp.SubsetSumVerifierCBTM3
import Mp.SubsetSumVerifierReverse6
import Mp.A2Bridge
import Mp.IVM
import Mp.SubsetSumVerifierReverse10

set_option linter.auxLemma false

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
# L3a:块级 fork 计数(1b 装配的最后一块)

分工边界:不动 Reverse7L3(束里程碑)/Reverse10(q10 ① 组合,兄弟热区)/Reverse9。

## 目标链(1b):NTM2 接受路径的 ntm2ForkCount(读 im=true 微步数)= elements.length

素材(全部已绿):
- Reverse7L3 `r7_accept_write_selnosel_eq_fork`(550e3ac,预选写步 = 读分支步;交叉验证用)
- SubsetSumCompile `symReachable_branchCount_eq_initial`(:1000,守恒)/`symTransition_branch_write_sel_nosel`(:916)/`symTransition_write_not_branch`(:827)
- Reverse6 `sym_accept_fork_eq_elems`(:1479,Sym 层成品:∃ 接受路径 filter isBranch = elements.length)
- CBTM3 `GoodBlock`/`GoodBlockPath`/`project_path`(块 ↔ Sym 步,块 sym = 投影步读符号)
- IVM `branchCount`(:356,CBTM 路径 im 读计数;`branchCount_append` 递归)
- Core `imTrueCount_symToF4s`(:231,字符 4F4 的 im-true 数 = 分支 ? 1 : 0)

## 路线(用户裁决 2):以 sym_accept_fork_eq_elems 结论(读分支 = elements)为 Sym 基准,
块级桥直接接;550e3ac 预选写桥留交叉验证。

## 块级桥结构(GoodBlock 单块 im 读计数;12 步读格 im 分类已由 expand_sym_step 步定义确认)

关键修正(expand_sym_step 定义确认,CBTM2:99-200):块内 im-true 读**不只 st3**:
st9(L 块)读 tprev.getD 3(前字符第 4 格 = 前字符分支性);
st11(R 块)读 w3(写符号第 4 格 = 写符号分支性)。R 块 st11 由表级挡(写 α/β 者仅 100/101,
截断路径排除 → 写非分支 → im false)。L 块 st9 需 α 区间论证。

素材优势:symPath_to_blockPath(CBTM4:1270 全绿)= Sym 接受路径 → GoodBlockPath +
blockCorrespond 正向构造已存在(SubsetSumCompile:317 symAccepts_implies_tapeAccepts 用过);
好块无需重拆 12 步样板。

## α 区间论证(用户裁决:选项 1,完整精确 fork;新不变量)

目标引理:接受截断路径上,任何 L 移动 Sym 步的左邻字符非 α(⇒ 块 st9 无 im 读)。

论证结构(时间性三段):
1. **2 段连续**:进入 2 唯一(非 2 态 next=2 ⟹ 源 1:1 读 #₀→2)、2 段内自环 R(2 读 α/data → 2
   写 sel/nosel R;读其它 → 101 死或 #₁ boundary → 3 S 离开)、离开后不回 2(表级:无态转 2 除
   1@#₀ 与 2 自环)⇒ 2 段 = 从 n+2 单调 R 扫到 #₁@L-1,全覆盖元素区
2. **2 段前无 L 步**:0/1 态表级全 R(1 态头 ≤ n+1,束 P10'1a 已给)
3. **2 全覆盖后带无 α**:2 写 sel/nosel(非 α);后续步源态 ∉ {100,101}(截断)→ 表级写非分支
   (symTransition_write_not_branch:827)⇒ 无 α 再生 ⇒ 任何 L 步(都在 2 段后活动)左邻非 α

轮 A-D 更新:
1. 轮 A:2 段连续 + 2 段前无 L(时间性;素材:表级转移 + 束 P10'1a)
2. 轮 B:2 全覆盖后带无 α 不变量(symTransition_write_not_branch 归纳)
3. 轮 C:L 步左邻非 α → 单块 im 读 = 分支?1:0(st3/st9/st11 分类)
4. 轮 D:GoodBlockPath 整体(经 symPath_to_blockPath)→ IVM branchCount → 1b 装配
-/

namespace Mp
namespace SymToF4

-- ============================================================
-- 轮 A:2 段连续性(α 区间论证 1)——表级进入/离开唯一性
-- ============================================================

/-- 进入 2 的唯一转移(非自环):q ≠ 2 ∧ nextState = 2 ⟹ 源态 = 1(1 读 boundary #₀ → 2)。
    (2 读 α/data 的自环 next=2 由 q≠2 排除。) -/
lemma l3a_next2_src1 (q : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) :
    q ≠ 2 → r.nextState = 2 → q = 1 := by
  intro hqne hn
  by_cases hqin : q ∈ VerifierSym.legalStates
  · have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) →
          (q : ℕ) ≠ 2 → r.nextState = 2 → (q : ℕ) = 1 := by
      native_decide
    have hqlt : q < 102 := by
      simp [VerifierSym.legalStates] at hqin
      omega
    exact hb ⟨q, hqlt⟩ s r hr hqne hn
  · rw [transition_of_not_legal q s hqin] at hr
    simp at hr
    subst r
    simp at hn

/-- 2 态步的 next 分类:自环 2(读 α/data)或 3(读 boundary #₁,停)或 101(读其它,死)。
    (接受截断路径排除 101 后 ⇒ 2 段内恒 2,直到 #₁ 转 3。) -/
lemma l3a_q2_next_class (q : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) :
    q = 2 → r.nextState = 2 ∨ r.nextState = 3 ∨ r.nextState = 101 := by
  intro hq
  by_cases hqin : q ∈ VerifierSym.legalStates
  · have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) →
          (q : ℕ) = 2 → r.nextState = 2 ∨ r.nextState = 3 ∨ r.nextState = 101 := by
      native_decide
    have hqlt : q < 102 := by
      simp [VerifierSym.legalStates] at hqin
      omega
    exact hb ⟨q, hqlt⟩ s r hr hq
  · rw [transition_of_not_legal q s hqin] at hr
    simp at hr
    subst r
    simp

/-- 1 态步的 next 分类:自环 1(读 data,target 区扫描)或 2(读 boundary #₀ 转 2)或 101(死)。
    (段前路径 = 0/1 态步的线性流:0 读 #ₗ → 1 后,1 自环直到 #₀ 转 2。) -/
lemma l3a_q1_next_class (q : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) :
    q = 1 → r.nextState = 1 ∨ r.nextState = 2 ∨ r.nextState = 101 := by
  intro hq
  by_cases hqin : q ∈ VerifierSym.legalStates
  · have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) →
          (q : ℕ) = 1 → r.nextState = 1 ∨ r.nextState = 2 ∨ r.nextState = 101 := by
      native_decide
    have hqlt : q < 102 := by
      simp [VerifierSym.legalStates] at hqin
      omega
    exact hb ⟨q, hqlt⟩ s r hr hq
  · rw [transition_of_not_legal q s hqin] at hr
    simp at hr
    subst r
    simp

/-- 2 态步的移动:R(覆盖步单调右扫;离开步 2 读 boundary → 3 移动 S 不在此列,
    101 死步亦不在此列)。(2 段全覆盖论证的移动性素材。) -/
lemma l3a_q2_move_R (q : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) :
    q = 2 → r.nextState = 2 → r.moveDir = Dir.R := by
  intro hq hn
  by_cases hqin : q ∈ VerifierSym.legalStates
  · have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) →
          (q : ℕ) = 2 → r.nextState = 2 → r.moveDir = Dir.R := by
      native_decide
    have hqlt : q < 102 := by
      simp [VerifierSym.legalStates] at hqin
      omega
    exact hb ⟨q, hqlt⟩ s r hr hq hn
  · rw [transition_of_not_legal q s hqin] at hr
    simp at hr
    subst r
    simp at hn

/-- 0/1 态步的移动:R(段前路径无 L 步——2 段前不会向左踏入元素区;101 死步排除)。 -/
lemma l3a_le1_move_R (q : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) :
    q ≤ 1 → r.nextState ≠ 101 → r.moveDir = Dir.R := by
  intro hq hne
  by_cases hqin : q ∈ VerifierSym.legalStates
  · have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) →
          (q : ℕ) ≤ 1 → r.nextState ≠ 101 → r.moveDir = Dir.R := by
      native_decide
    have hqlt : q < 102 := by
      simp [VerifierSym.legalStates] at hqin
      omega
    exact hb ⟨q, hqlt⟩ s r hr hq hne
  · rw [transition_of_not_legal q s hqin] at hr
    simp at hr
    subst r
    simp at hne

/-- 路径级:任何落 2 的步其源态 ∈ {1, 2}(1 转 2 进入或 2 自环)。
    (2 段连续的半成品:段内无他态插入——非 {1,2} 源不落 2。) -/
lemma l3a_q2_step_src {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg) :
    ∀ step ∈ π, step.result.nextState = 2 →
      step.fromState = 1 ∨ step.fromState = 2 := by
  intro step hst hn
  rcases r7_path_step_trans input h with ⟨htrans, _hlt⟩
  by_cases hsrc2 : step.fromState = 2
  · exact Or.inr hsrc2
  · exact Or.inl (l3a_next2_src1 step.fromState step.readSym step.result
      (htrans step hst) hsrc2 hn)

/-- 落 1 的转移源态 ∈ {0, 1}(0 读 #ₗ → 1 进入;1 读 data 自环;1 段前无他态落 1)。 -/
lemma l3a_next1_src_le1 (q : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) :
    r.nextState = 1 → q = 0 ∨ q = 1 := by
  intro hn
  by_cases hqin : q ∈ VerifierSym.legalStates
  · have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) →
          r.nextState = 1 → (q : ℕ) = 0 ∨ (q : ℕ) = 1 := by
      native_decide
    have hqlt : q < 102 := by
      simp [VerifierSym.legalStates] at hqin
      omega
    exact hb ⟨q, hqlt⟩ s r hr hn
  · rw [transition_of_not_legal q s hqin] at hr
    simp at hr
    subst r
    simp at hn

/-- 无转移落 0(0 只出现于初始 cfg;1 段/2 段后不再回 0)。 -/
lemma l3a_no_next0 (q : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) :
    r.nextState ≠ 0 := by
  intro hn
  by_cases hqin : q ∈ VerifierSym.legalStates
  · have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 0 := by
      native_decide
    have hqlt : q < 102 := by
      simp [VerifierSym.legalStates] at hqin
      omega
    exact hb ⟨q, hqlt⟩ s r hr hn
  · rw [transition_of_not_legal q s hqin] at hr
    simp at hr
    subst r
    simp at hn

/-- 路径级:任何落 1 的步其源态 ∈ {0, 1}(1 段线性:0 进入或 1 自环)。
    (配合 l3a_q2_step_src:0→1→2 的状态串行链。) -/
lemma l3a_q1_step_src {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg) :
    ∀ step ∈ π, step.result.nextState = 1 →
      step.fromState = 0 ∨ step.fromState = 1 := by
  intro step hst hn
  rcases r7_path_step_trans input h with ⟨htrans, _hlt⟩
  exact l3a_next1_src_le1 step.fromState step.readSym step.result
    (htrans step hst) hn

/-- 落 3 的转移源态 = 2(2 读 boundary #₁ → 3 是唯一入 3 口——2 段结束步)。 -/
lemma l3a_next3_src2 (q : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) :
    r.nextState = 3 → q = 2 := by
  intro hn
  by_cases hqin : q ∈ VerifierSym.legalStates
  · have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 3 → (q : ℕ) = 2 := by
      native_decide
    have hqlt : q < 102 := by
      simp [VerifierSym.legalStates] at hqin
      omega
    exact hb ⟨q, hqlt⟩ s r hr hn
  · rw [transition_of_not_legal q s hqin] at hr
    simp at hr
    subst r
    simp at hn

/-- 落 ≥3(非 101)的转移源态 ∉ {0, 1}(0/1 只落 1/2/101;101 陷阱行排除后
    0/1 不落 ≥3 ⇒ ≥3 态域的进入只经 2 段结束步)。 -/
lemma l3a_ge3_next_src_not_le1 (q : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) :
    r.nextState ≥ 3 → r.nextState ≠ 101 → q ≠ 0 ∧ q ≠ 1 := by
  intro hn hne
  by_cases hqin : q ∈ VerifierSym.legalStates
  · have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) →
          r.nextState ≥ 3 → r.nextState ≠ 101 → (q : ℕ) ≠ 0 ∧ (q : ℕ) ≠ 1 := by
      native_decide
    have hqlt : q < 102 := by
      simp [VerifierSym.legalStates] at hqin
      omega
    exact hb ⟨q, hqlt⟩ s r hr hn hne
  · rw [transition_of_not_legal q s hqin] at hr
    simp at hr
    subst r
    simp at hne

/-- 路径级:落 ≥3(非 101)步的源态 ∉ {0, 1}。 -/
lemma l3a_ge3_step_src_not_le1 {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg) :
    ∀ step ∈ π, step.result.nextState ≥ 3 → step.result.nextState ≠ 101 →
      step.fromState ≠ 0 ∧ step.fromState ≠ 1 := by
  intro step hst hn hne
  rcases r7_path_step_trans input h with ⟨htrans, _hlt⟩
  exact l3a_ge3_next_src_not_le1 step.fromState step.readSym step.result
    (htrans step hst) hn hne

/-- α 格不迁移:带上的 α 位置 ⊆ 初始带的 α 位置(写 α 只写回读 α 处——
    branch_write_eq_read_of)。未被读的 α 格恒为 α(反证:终点带分支格 > 0 的材料)。
    (仿 no_beta_invariant,Reverse6:1119 模板;cons 支:写位写 α ⟹ 读 α ⟹ ih。) -/
lemma l3a_alpha_pos_in_initial (inst : SubsetSumInstance) (π : List SymStep) (cfg : SymConfig)
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg) :
    ∀ p : ℤ, (cfg.tape p).1 = SymKind.alpha →
      ((symInitialConfig (encodeInstanceSym inst)).tape p).1 = SymKind.alpha := by
  induction h with
  | nil =>
      intro p hp
      simpa using hp
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro p hp
      dsimp [symStepConfig, SymConfig.mk] at hp
      by_cases hpw : p = cfg₁.headPos
      · rw [if_pos hpw] at hp
        have hq : cfg₁.state ∈ VerifierSym.legalStates := (symReachable_state_mem_legal hprev).1
        have hbr : Sym.isBranch step.result.writeSym = true := by
          simp [Sym.isBranch, SymKind.isBranch, hp]
        have hwr := branch_write_eq_read_of cfg₁.state hq (cfg₁.tape cfg₁.headPos)
          step.result htrans hbr
        have hsα : (cfg₁.tape cfg₁.headPos).1 = SymKind.alpha := by
          rw [← hwr]
          exact hp
        rw [hpw]
        exact ih cfg₁.headPos hsα
      · rw [if_neg hpw] at hp
        exact ih p hp

/-- symTo4F4 第 4 格(c3)的 im = 符号分支性(第 4 格 = (s.2, i1),i1 = kindBits 第 2 位 =
    α/β 标记)。S4(分支块 st3 读 im-true)的表级件。 -/
lemma l3a_symTo4F4_getD3_im (s : Sym) :
    F4.im ((symTo4F4 s).getD 3 F4.zero) = Sym.isBranch s := by
  rcases s with ⟨k, m⟩
  cases k <;> simp [symTo4F4, Sym.kindBits, Sym.isBranch, SymKind.isBranch]

/-- S4b 设计存档(2026-09-08 会话尾,下轮执行):
    目标:分支块(读 α)第 4 微步(st3)读 im-true → fork ≥ 分支块数 = elements。
    1. GoodBlock 拆 12 层(project_block 同款 tapeSteps_split_last 模式,CBTM3:451+)
       拿 step0-3/cfg0-3。
    2. 相位 0-2 步移动 R(表级 l3a_phase_lt3_step:transition4 定义直证(CBTM:215-218,
       相位<3 且读 im=false → 写回原符号 R),无需 decide)→ cfg3.headPos = 4p+3。
    3. 前 3 步写位 = 自己的头(stepConfig 写位=步前头)→ cfg3.tapeAt(4p+3) 未被写
       = cfgc.tapeAt(4p+3)。
    4. blockCorrespond → (symTo4F4 sym).getD 3 → l3a_symTo4F4_getD3_im(S4a)
       → im = isBranch sym = true(分支块)。
    5. ⇒ 分支块第 4 步读 im-true。路径级:每分支块贡献 1 个 im-true 读微步(块互不相交)
       → fork ≥ 分支块数 = Sym 读分支步数 = elements(sym_accept_fork_eq_elems)。
    查证:无现成结论级引理(CBTM2 expand 证明体内 hp3/hread3 局部:480/535 行);
    表级件 CBTM:85(前3格im=false)/89(非分支末格false)/727(getD3=getLastD)已有。
    模板行号(CBTM3 project_block,裁剪照抄):拆解 12 层 451-536(tapeSteps_split_last
    逐层,hπe/hf/hr/ht/hc 命名);hπn/cfgc0=cfgc 536-546;hc0v-3v/him0-2 560-575;
    b01/b12/b3 ≤63 与 decodeState_encodeState 581-610;前 3 步 hmem/hres/hp 620-735;
    第 4 步读链(hrd3'+hp3+逐步回退未写格)735-745(stepConfig_tapeAt_eq_of_ne)。
    裁剪片:片1 拆解+格值+解码(编译);片2 step0-2 推导+hp3(编译);片3 组合(编译)。 -/
lemma l3a_phase_lt3_step (q phase reg : ℕ) (s : F4) (r : CBTMTransResult)
    (hr : r ∈ transition4 (encodeState q phase reg) s)
    (hph : phase < 3) (him : F4.im s = false) (hreg : reg < regBound) :
    r.moveDir = Dir.R ∧ r.writeSym = s := by
  simp [transition4, decodeState_encodeState q phase reg (by dsimp [stepsPerSym]; omega) hreg, hph, him] at hr
  subst r
  simp


/-- S4b-2:分支块(读 α)的第 4 微步(0-index 3)读 im-true。
    拆解样板照抄 project_block(CBTM3:451-745);裁剪到 hrd3 + im 组合。 -/
lemma l3a_goodblock_step3_read_im {w : List F4} {cfgc : CBTMConfig subsetSumCBTM w}
    {π : ComputationPath} {cfgc' : CBTMConfig subsetSumCBTM w} {cfgs : SymConfig}
    {p : ℤ} {q : ℕ} {sym : Sym} {r : SymTransResult}
    (hblock : GoodBlock w cfgc π cfgc' cfgs p q sym r)
    (hbranch : Sym.isBranch sym = true) :
    F4.im (π.get ⟨3, by
      rcases hblock with ⟨_hpath, hlen, _⟩
      omega⟩).readSym = true := by
  rcases hblock with ⟨hpath, hlen, hst, hp, hcorr, hread, hq, hbranchq, hvalid_sym, hstep4, hmk, hr, hst', hhead'⟩
  -- 本地 let(与 expand_sym_step/project_block 内部一致)
  let cells := symTo4F4 sym
  let c0 := cells.getD 0 F4.zero
  let c1 := cells.getD 1 F4.zero
  let c2 := cells.getD 2 F4.zero
  let c3 := cells.getD 3 F4.zero
  let nrs := symTo4F4 r.writeSym
  let b01 := bufOf3 c0 F4.zero F4.zero
  let b12 := bufOf3 c0 c1 F4.zero
  let b3 := bufOf3 c0 c1 c2
  let regr := encodeResult r
  -- 1. 拆出 12 步(project_block 451-536 同款)
  rcases tapeSteps_split_last hpath (by intro h; simp [h] at hlen) with
    ⟨step11, π10, cfg11, hπe11, h10, hf11, hr11, ht11, hc11⟩
  rcases tapeSteps_split_last h10 (by
      intro h
      have : (π10 ++ [step11]).length = 12 := by simpa [hπe11] using hlen
      simp [h] at this) with
    ⟨step10, π9, cfg10, hπe10, h9, hf10, hr10, ht10, hc10⟩
  rcases tapeSteps_split_last h9 (by
      intro h
      have : (π9 ++ [step10, step11]).length = 12 := by simpa [hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step9, π8, cfg9, hπe9, h8, hf9, hr9, ht9, hc9⟩
  rcases tapeSteps_split_last h8 (by
      intro h
      have : (π8 ++ [step9, step10, step11]).length = 12 := by simpa [hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step8, π7, cfg8, hπe8, h7, hf8, hr8, ht8, hc8⟩
  rcases tapeSteps_split_last h7 (by
      intro h
      have : (π7 ++ [step8, step9, step10, step11]).length = 12 := by simpa [hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step7, π6, cfg7, hπe7, h6, hf7, hr7, ht7, hc7⟩
  rcases tapeSteps_split_last h6 (by
      intro h
      have : (π6 ++ [step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step6, π5, cfg6, hπe6, h5, hf6, hr6, ht6, hc6⟩
  rcases tapeSteps_split_last h5 (by
      intro h
      have : (π5 ++ [step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step5, π4, cfg5, hπe5, h4, hf5, hr5, ht5, hc5⟩
  rcases tapeSteps_split_last h4 (by
      intro h
      have : (π4 ++ [step5, step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step4, π3, cfg4, hπe4, h3, hf4, hr4, ht4, hc4⟩
  rcases tapeSteps_split_last h3 (by
      intro h
      have : (π3 ++ [step4, step5, step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step3, π2, cfg3, hπe3, h2, hf3, hr3, ht3, hc3⟩
  rcases tapeSteps_split_last h2 (by
      intro h
      have : (π2 ++ [step3, step4, step5, step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe3, hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step2, π1, cfg2, hπe2, h1, hf2, hr2, ht2, hc2⟩
  rcases tapeSteps_split_last h1 (by
      intro h
      have : (π1 ++ [step2, step3, step4, step5, step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe2, hπe3, hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step1, π0, cfg1, hπe1, h0, hf1, hr1, ht1, hc1⟩
  rcases tapeSteps_split_last h0 (by
      intro h
      have : (π0 ++ [step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe1, hπe2, hπe3, hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step0, πn, cfgc0, hπen, hn, hf0, hr0, ht0, hc0⟩
  -- 2. πn = []、cfgc0 = cfgc
  have hπn : πn = [] := by
    have hsum : (πn ++ [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11]).length = 12 := by
      simpa [hπen, hπe1, hπe2, hπe3, hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
    have hsum' : πn.length + 12 = 12 := by simpa using hsum
    have hlen0 : πn.length = 0 := by omega
    cases πn with
    | nil => rfl
    | cons x xs => simp at hlen0
  have hcfg0 : cfgc0 = cfgc := by
    exact tapeSteps_empty hn hπn
  subst πn
  subst cfgc0
  -- 3. 前 4 格取值
  have hc0v : cfgc.tapeAt (4 * p) = c0 := by
    have hc := hcorr.2.2 p 0 (by norm_num)
    simpa [hread, c0, cells] using hc
  have hc1v : cfgc.tapeAt (4 * p + 1) = c1 := by
    have hc := hcorr.2.2 p 1 (by norm_num)
    simpa [hread, c1, cells] using hc
  have hc2v : cfgc.tapeAt (4 * p + 2) = c2 := by
    have hc := hcorr.2.2 p 2 (by norm_num)
    simpa [hread, c2, cells] using hc
  have hc3v : cfgc.tapeAt (4 * p + 3) = c3 := by
    have hc := hcorr.2.2 p 3 (by norm_num)
    simpa [hread, c3, cells] using hc
  have him0 : F4.im c0 = false := by simpa [c0, cells] using (symTo4F4_im_false_012 sym).1
  have him1 : F4.im c1 = false := by simpa [c1, cells] using (symTo4F4_im_false_012 sym).2.1
  have him2 : F4.im c2 = false := by simpa [c2, cells] using (symTo4F4_im_false_012 sym).2.2
  -- 4. 解码辅助
  have hb01 : b01 = bufOf3s 0 c0 0 := by
    dsimp [b01, bufOf3, bufOf3s]
    rcases c0 with ⟨r0, i0⟩
    cases r0 <;> cases i0 <;> simp [F4.zero, F4.one, F4.alpha, F4.beta]
  have hb12 : b12 = b01 + bufOf3s 1 c1 b01 := by
    dsimp [b12, b01, bufOf3, bufOf3s]
    rcases c0 with ⟨r0, i0⟩ <;> rcases c1 with ⟨r1, i1⟩
    cases r0 <;> cases i0 <;> cases r1 <;> cases i1 <;> simp [F4.zero, F4.one, F4.alpha, F4.beta]
  have hb3 : b3 = b12 + bufOf3s 2 c2 b12 := by
    dsimp [b3, b12, b01, bufOf3, bufOf3s]
    rcases c0 with ⟨r0, i0⟩ <;> rcases c1 with ⟨r1, i1⟩ <;> rcases c2 with ⟨r2, i2⟩
    cases r0 <;> cases i0 <;> cases r1 <;> cases i1 <;> cases r2 <;> cases i2 <;>
      simp [F4.zero, F4.one, F4.alpha, F4.beta]
  have hdec1' : decodeState (encodeState (min q 101) 1 b01) = (min q 101, 1, b01) := by
    apply decodeState_encodeState
    · norm_num
    · have hb : b01 ≤ 63 := by
        dsimp [b01, bufOf3]
        rcases c0 with ⟨r0, i0⟩
        cases r0 <;> cases i0 <;> simp [F4.zero, F4.one, F4.alpha, F4.beta]
      exact lt_of_le_of_lt hb (by norm_num)
  have hdec2' : decodeState (encodeState (min q 101) 2 b12) = (min q 101, 2, b12) := by
    apply decodeState_encodeState
    · norm_num
    · have hb : b12 ≤ 63 := by
        dsimp [b12, bufOf3]
        rcases c0 with ⟨r0, i0⟩ <;> rcases c1 with ⟨r1, i1⟩
        cases r0 <;> cases i0 <;> cases r1 <;> cases i1 <;> simp [F4.zero, F4.one, F4.alpha, F4.beta]
      exact lt_of_le_of_lt hb (by norm_num)
  -- 5. 第 0 步:读 c0(im=false)→ 唯一结果 R
  have hst0 : step0.fromState = encodeState q 0 0 := by simpa [hst] using hf0
  have hrd0 : step0.readSym = c0 := by
    simpa [hc0v, hp, c0] using hr0
  have hmem0 : step0.result ∈ transition4 (encodeState q 0 0) c0 := by
    have ht0' : step0.result ∈ subsetSumCBTM.transition (cfgc.state, cfgc.tapeAt cfgc.headPos, cfgc.headPos) := ht0
    rw [hst, hp, hc0v] at ht0'
    simpa [subsetSumCBTM] using ht0'
  have hres0 : step0.result = CBTMTransResult.mk (encodeState (min q 101) 1 b01) c0 Dir.R := by
    dsimp [transition4] at hmem0
    rw [decodeState_encodeState q 0 0 (by norm_num) (by norm_num)] at hmem0
    simp [him0] at hmem0
    simpa [hb01] using hmem0
  have hp1 : cfg1.headPos = 4 * p + 1 := by
    rw [hc0]
    dsimp [stepConfig]
    rw [hres0]
    dsimp
    rw [hp]
    simp [Dir.toInt]
  -- 6. 第 1 步:读 c1
  have hst1 : step1.fromState = encodeState (min q 101) 1 b01 := by
    have hst1' : step1.fromState = cfg1.state := by simpa using hf1
    rw [hst1']
    rw [hc0]
    dsimp [stepConfig]
    rw [hres0]
  have hrd1 : step1.readSym = c1 := by
    have hrd1' : step1.readSym = cfg1.tapeAt cfg1.headPos := by simpa using hr1
    rw [hrd1', hp1]
    rw [hc0]
    rw [stepConfig_tapeAt_eq_of_ne cfgc step0.result (4 * p + 1) (by rw [hp]; omega)]
    rw [hc1v]
  have hmem1 : step1.result ∈ transition4 (encodeState (min q 101) 1 b01) c1 := by
    have ht1' : step1.result ∈ subsetSumCBTM.transition (cfg1.state, cfg1.tapeAt cfg1.headPos, cfg1.headPos) := ht1
    rw [show cfg1.state = encodeState (min q 101) 1 b01 from by simpa [hf1] using hst1] at ht1'
    rw [hp1] at ht1'
    rw [show cfg1.tapeAt (4 * p + 1) = c1 from by simpa [hr1, hp1] using hrd1] at ht1'
    simpa [subsetSumCBTM] using ht1'
  have hres1 : step1.result = CBTMTransResult.mk (encodeState (min q 101) 2 (b01 + bufOf3s 1 c1 b01)) c1 Dir.R := by
    dsimp [transition4] at hmem1
    rw [hdec1'] at hmem1
    simp [him1] at hmem1
    simpa using hmem1
  have hp2 : cfg2.headPos = 4 * p + 2 := by
    rw [hc1]
    dsimp [stepConfig]
    rw [hres1]
    dsimp
    rw [hp1]
    simp [Dir.toInt]
    omega
  -- 7. 第 2 步:读 c2
  have hst2 : step2.fromState = encodeState (min q 101) 2 b12 := by
    have hst2' : step2.fromState = cfg2.state := by simpa using hf2
    rw [hst2']
    rw [hc1]
    dsimp [stepConfig]
    rw [hres1]
    dsimp
    rw [← hb12]
  have hrd2 : step2.readSym = c2 := by
    have hrd2' : step2.readSym = cfg2.tapeAt cfg2.headPos := by simpa using hr2
    rw [hrd2', hp2]
    rw [hc1]
    rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * p + 2) (by rw [hp1]; omega)]
    rw [hc0]
    rw [stepConfig_tapeAt_eq_of_ne cfgc step0.result (4 * p + 2) (by rw [hp]; omega)]
    rw [hc2v]
  have hmem2 : step2.result ∈ transition4 (encodeState (min q 101) 2 b12) c2 := by
    have ht2' : step2.result ∈ subsetSumCBTM.transition (cfg2.state, cfg2.tapeAt cfg2.headPos, cfg2.headPos) := ht2
    rw [show cfg2.state = encodeState (min q 101) 2 b12 from by simpa [hf2] using hst2] at ht2'
    rw [hp2] at ht2'
    rw [show cfg2.tapeAt (4 * p + 2) = c2 from by simpa [hr2, hp2] using hrd2] at ht2'
    simpa [subsetSumCBTM] using ht2'
  have hres2 : step2.result = CBTMTransResult.mk (encodeState (min q 101) 3 (b12 + bufOf3s 2 c2 b12)) c2 Dir.R := by
    dsimp [transition4] at hmem2
    rw [hdec2'] at hmem2
    simp [him2] at hmem2
    simpa using hmem2
  have hp3 : cfg3.headPos = 4 * p + 3 := by
    rw [hc2]
    dsimp [stepConfig]
    rw [hres2]
    dsimp
    rw [hp2]
    simp [Dir.toInt]
    omega
  -- 8. 第 3 步(合成步):读格 = 4p+3 未被前 3 步写 → c3 → im = 分支性
  have hrd3 : step3.readSym = c3 := by
    have hrd3' : step3.readSym = cfg3.tapeAt cfg3.headPos := by simpa using hr3
    rw [hrd3', hp3]
    rw [hc2]
    rw [stepConfig_tapeAt_eq_of_ne cfg2 step2.result (4 * p + 3) (by rw [hp2]; omega)]
    rw [hc1]
    rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * p + 3) (by rw [hp1]; omega)]
    rw [hc0]
    rw [stepConfig_tapeAt_eq_of_ne cfgc step0.result (4 * p + 3) (by rw [hp]; omega)]
    rw [hc3v]
  -- 9. π.get 3 = step3 → 组合
  have hπ' : π = [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11] := by
    rw [hπe11, hπe10, hπe9, hπe8, hπe7, hπe6, hπe5, hπe4, hπe3, hπe2, hπe1, hπen]
    rfl
  have hg : π.get ⟨3, by omega⟩ = step3 := by
    simpa [hπ']
  rw [hg]
  rw [hrd3]
  dsimp [c3, cells]
  rw [l3a_symTo4F4_getD3_im]
  exact hbranch

-- S4b-3 设计存档(2026-09-08):fork ≥ elements 的路径级组装。
-- 难点:GoodBlockPath 是 Prop(不能递归计数 def)。
-- 方案:对 SymSteps(πs)归纳(仿 symPath_to_blockPath 骨架,带计数结论):
--   lemma l3a_symPath_fork_ge : SymSteps 接受路径(截断)前提 →
--     ∃ πc cfgc, GoodBlockPath … πc cfgc ∧ blockCorrespond cfgc cfgs ∧
--       (πc.filter (fun st => F4.im st.readSym)).length ≥
--         (πs.filter Sym.isBranch …).length
--   cons 支:πc = πc₀ ++ block(expand 12 步);fork 分解(filter_append);
--   每分支步的块贡献 ≥ 1(块内 st3 = l3a_goodblock_step3_read_im(5100553),
--   需 πm.get ⟨3⟩ ∈ πm(filter 计数 ≥ 1 用 List.length_pos_of_mem + mem_filter)。
--   然后组合:sym_accept_fork_eq_elems(πs filter = elements)→ fork ≥ elements。
-- 依赖:l3a_goodblock_step3_read_im 需要 hblock(块的 sym 分支(每块参数由
--   expand_sym_step 的 ∃ 给出(与 symPath_to_blockPath 相同的构造语境。
-- 预估 ~200 行(仿 CBTM4:1270 归纳骨架)。


/-- 单例 filter 长度 ≤ 1(filter 是子表)。 -/
lemma l3a_filter_singleton_len_le1 (step : SymStep) :
    ([step].filter (fun st => Sym.isBranch st.readSym)).length ≤ 1 := by
  simpa using (List.length_filter_le (fun st => Sym.isBranch st.readSym) [step])

/-- 单例 filter 长度 = 0(谓词在 step 上假;成员反证,不依赖 filter 化简)。 -/
lemma l3a_filter_singleton_len0 (step : SymStep)
    (hb : Sym.isBranch step.readSym = false) :
    ([step].filter (fun st => Sym.isBranch st.readSym)).length = 0 := by
  rw [List.filter_cons]
  rw [hb]
  simp

/-- 表级:非分支符号的 symTo4F4 分量不含 alpha/beta(F4 值)。
    (S5-A:块路径无写 im-true 值的关键——块写符号 = Sym 步写符号的 4F4。) -/
lemma l3a_symTo4F4_component_im_false (s : Sym) (hnb : ¬ Sym.isBranch s) :
    ∀ (j : ℕ) (hj : j < 4), F4.im ((symTo4F4 s).getD j F4.zero) = false := by
  rcases s with ⟨k, m⟩
  intro j hj
  interval_cases j <;> cases k <;> cases m <;>
    simp [symTo4F4, Sym.kindBits, Sym.isBranch, SymKind.isBranch] at hnb ⊢

/-- q2_scan 链基:0 态 cfg 的头 = 0(0 无入边(l3a_no_next0)→ 0 只初始配置)。 -/
lemma l3a_q0_head_zero (inst : SubsetSumInstance) {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π cfg) :
    cfg.state = 0 → cfg.headPos = 0 := by
  induction h with
  | nil =>
      intro hq
      simp [symInitialConfig] at hq ⊢
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro hq
      have hq' : step.result.nextState = 0 := by
        simpa [symStepConfig] using hq
      exact False.elim (l3a_no_next0 cfg₁.state (cfg₁.tape cfg₁.headPos) step.result htrans hq')


/-- 表级:2 态自环步(next = 2)的写符号非 α(2 读 α/data 写 sel/nosel/写回,
    catch-all 101 写回除外——自环排除)。(q2_scan 自环支:写位不产生新 α 格。) -/
lemma l3a_q2_write_not_alpha (q : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (hq : q = 2) (hq2 : r.nextState = 2) :
    r.writeSym.1 ≠ SymKind.alpha := by
  by_cases hqin : q ∈ VerifierSym.legalStates
  · have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) →
          (q : ℕ) = 2 → r.nextState = 2 → r.writeSym.1 ≠ SymKind.alpha := by
      native_decide
    have hqlt : q < 102 := by
      simp [VerifierSym.legalStates] at hqin
      omega
    exact hb ⟨q, hqlt⟩ s r hr hq hq2
  · rw [transition_of_not_legal q s hqin] at hr
    simp at hr
    subst r
    simp at hq2

/-- q2_scan 自环支:2 态 cfg₁(扫过区无 α)执行 2 自环步(移动 R + 写非 α)
    ⟹ 步后 cfg 的扫过区仍无 α。 -/
lemma l3a_q2_scan_selfloop (inst : SubsetSumInstance) {cfg₁ : SymConfig}
    (step : SymStep)
    (hfrom : step.fromState = cfg₁.state)
    (hread : step.readSym = cfg₁.tape cfg₁.headPos)
    (htrans : step.result ∈ VerifierSym.transition (cfg₁.state, cfg₁.tape cfg₁.headPos))
    (hq1 : cfg₁.state = 2) (hq2 : step.result.nextState = 2)
    (hscan : ∀ p : ℤ, (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ p →
      p < cfg₁.headPos → (cfg₁.tape p).1 ≠ SymKind.alpha) :
    ∀ p : ℤ, (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ p →
      p < (symStepConfig cfg₁ step.result).headPos →
      ((symStepConfig cfg₁ step.result).tape p).1 ≠ SymKind.alpha := by
  intro p hp1 hp2
  have hR : step.result.moveDir = Dir.R :=
    l3a_q2_move_R cfg₁.state (cfg₁.tape cfg₁.headPos) step.result htrans hq1 hq2
  have hwα : step.result.writeSym.1 ≠ SymKind.alpha :=
    l3a_q2_write_not_alpha cfg₁.state (cfg₁.tape cfg₁.headPos) step.result htrans hq1 hq2
  dsimp [symStepConfig]
  by_cases hpeq : p = cfg₁.headPos
  · rw [if_pos hpeq]
    exact hwα
  · rw [if_neg hpeq]
    apply hscan p hp1
    have hp2' : p < cfg₁.headPos + (1 : ℤ) := by
      dsimp [symStepConfig] at hp2
      simpa [hR, Dir.toInt] using hp2
    omega


/-- 表级:1 态转 2 的步读 boundary(1 读 data 自环,读 boundary 才转 2)。 -/
lemma l3a_q1_to2_reads_boundary (q : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (hq : q = 1) (hq2 : r.nextState = 2) :
    s.1 = SymKind.boundary := by
  by_cases hqin : q ∈ VerifierSym.legalStates
  · have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) →
          (q : ℕ) = 1 → r.nextState = 2 → s.1 = SymKind.boundary := by
      native_decide
    have hqlt : q < 102 := by
      simp [VerifierSym.legalStates] at hqin
      omega
    exact hb ⟨q, hqlt⟩ s r hr hq hq2
  · rw [transition_of_not_legal q s hqin] at hr
    simp at hr
    subst r
    simp at hq2

/-- 1 态 cfg 的头 ≥ 1(0 读 #ₗ@0 → 1 后头 = 1;1 自环 R 头递增)。
    (q2_scan 进入支:排除 headPos = 0 的 boundary。) -/
lemma l3a_q1_head_ge1 (inst : SubsetSumInstance) {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π cfg) :
    cfg.state = 1 → (1 : ℤ) ≤ cfg.headPos := by
  induction h with
  | nil =>
      intro hq
      simp [symInitialConfig] at hq
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro hq
      have hq' : step.result.nextState = 1 := by
        simpa [symStepConfig] using hq
      have hsrc : cfg₁.state = 0 ∨ cfg₁.state = 1 :=
        l3a_next1_src_le1 cfg₁.state (cfg₁.tape cfg₁.headPos) step.result htrans hq'
      rcases hsrc with h0 | h1
      · have hpos0 : cfg₁.headPos = 0 := l3a_q0_head_zero inst hprev h0
        have hR : step.result.moveDir = Dir.R := by
          have hne : step.result.nextState ≠ 101 := by omega
          exact l3a_le1_move_R cfg₁.state (cfg₁.tape cfg₁.headPos) step.result htrans
            (by omega) hne
        rw [symStepConfig]
        simp [hR, hpos0, Dir.toInt]
      · have hge : (1 : ℤ) ≤ cfg₁.headPos := ih h1
        have hR : step.result.moveDir = Dir.R := by
          have hne : step.result.nextState ≠ 101 := by omega
          exact l3a_le1_move_R cfg₁.state (cfg₁.tape cfg₁.headPos) step.result htrans
            (by omega) hne
        rw [symStepConfig]
        simp [hR, Dir.toInt]
        omega


/-- q2_scan(2 全覆盖):2 态 cfg 的头部扫过区([n+2, headPos))无 α 格。
    自环支:l3a_q2_scan_selfloop(83fcc20);进入支:sym_domain_state1(兄弟,
    1 态头 ≤ bits+1)→ 步后头 ≤ bits+2 → 扫过区空。 -/
lemma l3a_q2_scan (inst : SubsetSumInstance) {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π cfg)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101)
    (hno100 : ∀ step ∈ π, step.fromState ≠ 100) :
    cfg.state = 2 →
    ∀ p : ℤ, (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ p → p < cfg.headPos →
      (cfg.tape p).1 ≠ SymKind.alpha := by
  induction h with
  | nil =>
      intro hq p hp1 hp2
      simp [symInitialConfig] at hq
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro hq2 p hp1 hp2
      have hq2' : step.result.nextState = 2 := by
        simpa [symStepConfig] using hq2
      by_cases hq1 : cfg₁.state = 2
      · -- 自环支:步保持引理
        have hno101₀ : ∀ step ∈ π₀, step.result.nextState ≠ 101 := by
          intro st hst
          exact hno101 st (by rw [List.mem_append]; left; exact hst)
        have hno100₀ : ∀ step ∈ π₀, step.fromState ≠ 100 := by
          intro st hst
          exact hno100 st (by rw [List.mem_append]; left; exact hst)
        have hscan₁ : ∀ p : ℤ, (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ p →
            p < cfg₁.headPos → (cfg₁.tape p).1 ≠ SymKind.alpha := ih hno101₀ hno100₀ hq1
        exact l3a_q2_scan_selfloop inst step hfrom hread htrans hq1 hq2' hscan₁ p hp1 hp2
      · -- 进入支:cfg₁ 态 1(表级 next2_src1)→ sym_domain_state1 → 步后头 ≤ bits+2 → 扫过区空
        have hsrc1 : cfg₁.state = 1 :=
          l3a_next2_src1 cfg₁.state (cfg₁.tape cfg₁.headPos) step.result htrans hq1 hq2'
        have hpath₁ : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π₀ cfg₁ :=
          (symSteps_initial_iff VerifierSym.transition (encodeInstanceSym inst) π₀ cfg₁).1 hprev
        have hdom := sym_domain_state1 inst hpath₁ hsrc1
        have hR : step.result.moveDir = Dir.R := by
          have hne : step.result.nextState ≠ 101 := hno101 step (by simp)
          exact l3a_le1_move_R cfg₁.state (cfg₁.tape cfg₁.headPos) step.result htrans
            (by simpa [hsrc1]) hne
        have hbnd : (symStepConfig cfg₁ step.result).headPos ≤
            (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) := by
          dsimp [symStepConfig]
          simp [hR, Dir.toInt]
          omega
        exfalso
        dsimp [symStepConfig] at hp2
        simp [hR, Dir.toInt] at hp2 hbnd
        omega


/-- 低态域前缀封闭:cfg 态 ≤ 2 时,路径前缀的步源 ≤ 2(⊆ E 族)。
    (全覆盖论证:r7_E_no_segment_boundary 需要 E 路径前提。)
    源分类:落 0 无(l3a_no_next0)、落 1 源 ≤ 1、落 2 源 ≤ 2。 -/
lemma l3a_lowstate_prefix_le2 {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg) :
    cfg.state ≤ 2 → ∀ step ∈ π, step.fromState ≤ 2 := by
  induction h with
  | nil => intro hle step hmem; simp at hmem
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro hle st hst
      have hsrc_le : cfg₁.state ≤ 2 := by
        have hq' : step.result.nextState ≤ 2 := by
          simpa [symStepConfig] using hle
        by_cases h0 : step.result.nextState = 0
        · exfalso
          exact l3a_no_next0 cfg₁.state (cfg₁.tape cfg₁.headPos) step.result htrans h0
        · by_cases h1 : step.result.nextState = 1
          · have hsrc := l3a_next1_src_le1 cfg₁.state (cfg₁.tape cfg₁.headPos) step.result htrans h1
            rcases hsrc with h0s | h1s <;> omega
          · have h2 : step.result.nextState = 2 := by omega
            by_cases hsrc2 : cfg₁.state = 2
            · omega
            · have h1' : cfg₁.state = 1 :=
                l3a_next2_src1 cfg₁.state (cfg₁.tape cfg₁.headPos) step.result htrans hsrc2 h2
              omega
      rw [List.mem_append] at hst
      rcases hst with hpre | hlast
      · exact ih hsrc_le st hpre
      · rw [List.mem_singleton] at hlast
        rw [hlast]
        simpa [hfrom] using hsrc_le


/-- S5a:2 态 cfg 读 boundary ⟹ 头 = L-1(#₁)。
    束 P10'2(n+2 ≤ 头)+ P9(boundary 位置 ∈ {0, L-1} ∪ [n+1, L-3])+
    prefix_E → r7_E_no_segment_boundary(排除 [n+2, L-3])。 -/
lemma l3a_q2_read_boundary_at_L1 (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (hpos : ∀ v ∈ inst.elements, 0 < v) (htarget : 0 < inst.target)
    {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg)
    (hext : ∃ (π₂ : List SymStep) (cfg₂ : SymConfig),
      SymReachablePath VerifierSym.transition (encodeInstanceSym inst) (π ++ π₂) cfg₂ ∧
      cfg₂.state = 100)
    (hq : cfg.state = 2)
    (hbnd : (cfg.tape cfg.headPos).1 = SymKind.boundary) :
    cfg.headPos = (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by
  rcases r7_path_bundle inst hm hpos htarget π cfg h hext with
    ⟨_hP0, _hPblank, _hP0e, _h1, _h28, _h87, _h20, _h23, _h81, _h9A, _h12c, _h10,
      _hP10'0, _hP10'1, _hP10'1b, _hP10'1c, hP10'2, _hP10'F, _hP11, _hP6l, _hP6r, hP9⟩
  rcases hP10'2 hq with ⟨_hfirst, _hgt, hge⟩
  have hE : ∀ step ∈ π, r7_E step.fromState := by
    intro step hst
    have hle : step.fromState ≤ 2 := l3a_lowstate_prefix_le2 h (by omega) step hst
    interval_cases step.fromState <;> simp [r7_E]
  have hnoE : ∀ p : ℤ, (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ p →
      p ≤ (((encodeInstanceSym inst).length : ℕ) - 3 : ℤ) →
      (cfg.tape p).1 ≠ SymKind.boundary := r7_E_no_segment_boundary inst h hE
  rcases hP9 cfg.headPos hbnd with h0 | hL1 | hmid
  · exfalso
    omega
  · exact hL1
  · exfalso
    rcases hmid with ⟨hge1, hle3⟩
    have hnb := hnoE cfg.headPos hge hle3
    exact hnb hbnd


/-- 布局:初始带的 α 位置 ∈ [n+2, L-2](元素区)。
    (S5b 2 支:α 不迁移(l3a_alpha_pos_in_initial)⟹ cfg 带 α 位置 ⊆ 初始位置 ⊆
    扫过区 [n+2, L-1),与 q2_scan 矛盾。) -/
lemma l3a_initial_alpha_in_elem_zone (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length) {j : ℕ}
    (hj : j < (encodeInstanceSym inst).length)
    (hα : ((encodeInstanceSym inst)[j]).1 = SymKind.alpha) :
    ((encodeBitsSym inst.target).length + 2 : ℕ) ≤ j ∧
      j ≤ ((encodeInstanceSym inst).length - 2) := by
  have hlen : (encodeInstanceSym inst).length =
      (encodeBitsSym inst.target).length + 2 + (encodeElementsSym inst.elements).length + 1 := by
    rw [r7_enc_len]
    omega
  by_cases hlo : j < (encodeBitsSym inst.target).length + 2
  · exfalso
    have hval : ((encodeInstanceSym inst)[j]).1 ≠ SymKind.alpha := by
      by_cases hz : j = 0
      · have hconv : (encodeInstanceSym inst)[j] = (encodeInstanceSym inst).getD j Sym.blank :=
          (List.getD_eq_getElem (encodeInstanceSym inst) Sym.blank hj).symm
        rw [hconv, hz]
        rw [r7_enc_getD_0 inst]
        decide
      · by_cases hm1 : j = (encodeBitsSym inst.target).length + 1
        · have hconv : (encodeInstanceSym inst)[j] = (encodeInstanceSym inst).getD j Sym.blank :=
            (List.getD_eq_getElem (encodeInstanceSym inst) Sym.blank hj).symm
          rw [hconv, hm1]
          rw [r7_enc_getD_mid inst]
          decide
        · have hj1 : j - 1 < (encodeBitsSym inst.target).length := by
            rw [r7_enc_len] at hj
            omega
          have hcell : (encodeInstanceSym inst).getD j Sym.blank =
              (encodeBitsSym inst.target).getD (j - 1) Sym.blank := by
            unfold encodeInstanceSym
            let X₂ : List Sym := [Sym.boundary] ++ encodeBitsSym inst.target
            let X₁ : List Sym := X₂ ++ [Sym.boundary]
            let X₀ : List Sym := X₁ ++ encodeElementsSym inst.elements
            have hL₀ : j < X₀.length := by
              dsimp [X₀, X₁, X₂]
              simp [List.length_append]
              rw [r7_enc_len] at hj
              omega
            have hL₁ : j < X₁.length := by
              dsimp [X₁, X₂]
              simp [List.length_append]
              rw [r7_enc_len] at hj
              omega
            have hL₂ : j < X₂.length := by
              dsimp [X₂]
              simp [List.length_append]
              omega
            have hR : [Sym.boundary].length ≤ j := by
              simp
              omega
            calc
              (X₀ ++ [Sym.boundary]).getD j Sym.blank
                  = X₀.getD j Sym.blank := by
                      exact r7_getD_append_left X₀ [Sym.boundary] Sym.blank j hL₀
              _ = X₁.getD j Sym.blank := by
                      exact r7_getD_append_left X₁ (encodeElementsSym inst.elements) Sym.blank j hL₁
              _ = X₂.getD j Sym.blank := by
                      exact r7_getD_append_left X₂ [Sym.boundary] Sym.blank j hL₂
              _ = (encodeBitsSym inst.target).getD (j - [Sym.boundary].length) Sym.blank := by
                      exact List.getD_append_right [Sym.boundary] (encodeBitsSym inst.target)
                        Sym.blank j hR
              _ = (encodeBitsSym inst.target).getD (j - 1) Sym.blank := by
                      congr 1 <;> simp
          have hconv : (encodeInstanceSym inst)[j] = (encodeInstanceSym inst).getD j Sym.blank :=
            (List.getD_eq_getElem (encodeInstanceSym inst) Sym.blank hj).symm
          rw [hconv, hcell]
          rw [List.getD_eq_getElem (encodeBitsSym inst.target) Sym.blank hj1]
          have hk := encodeBitsSym_nonboundary inst.target
            (GetElem.getElem (encodeBitsSym inst.target) (j - 1) hj1)
            (List.getElem_mem hj1)
          rcases hk with hk | hk <;> simp [hk]
    exact hval hα
  · have hge : (encodeBitsSym inst.target).length + 2 ≤ j := by omega
    by_cases hhi : j ≤ (encodeInstanceSym inst).length - 2
    · exact ⟨hge, hhi⟩
    · exfalso
      have hval : ((encodeInstanceSym inst)[j]).1 ≠ SymKind.alpha := by
        have hconv : (encodeInstanceSym inst)[j] = (encodeInstanceSym inst).getD j Sym.blank :=
          (List.getD_eq_getElem (encodeInstanceSym inst) Sym.blank hj).symm
        rw [hconv]
        have hjL1 : j = (encodeInstanceSym inst).length - 1 := by
          rw [hlen] at hhi hj ⊢
          omega
        rw [hjL1]
        rw [r7_enc_getD_last inst]
        decide
      exact hval hα


/-- S5b:态 ≥3 且 ≠101 ⟹ 带无 α(全覆盖后件)。
    2 支:源 2 转 3(S5a 头=L-1 + q2_scan 全覆盖 + S3 α 不迁移 + 布局);3+ 支:ih + 写非 α。 -/
lemma l3a_no_alpha_ge3 (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (hpos : ∀ v ∈ inst.elements, 0 < v) (htarget : 0 < inst.target)
    {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg)
    (hext : ∃ (π₂ : List SymStep) (cfg₂ : SymConfig),
      SymReachablePath VerifierSym.transition (encodeInstanceSym inst) (π ++ π₂) cfg₂ ∧
      cfg₂.state = 100)
    (hno100 : ∀ step ∈ π, step.fromState ≠ 100)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101) :
    cfg.state ≥ 3 → cfg.state ≠ 101 →
    ∀ p : ℤ, (cfg.tape p).1 ≠ SymKind.alpha := by
  induction h with
  | nil =>
      intro hge hne p
      simp [symInitialConfig] at hge
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro hge hne p
      have hq' : step.result.nextState ≥ 3 := by
        simpa [symStepConfig] using hge
      have hne' : step.result.nextState ≠ 101 := by
        simpa [symStepConfig] using hne
      have hno100₀ : ∀ step₀ ∈ π₀, step₀.fromState ≠ 100 := by
        intro step₀ hmem
        exact hno100 step₀ (by simp [hmem])
      have hno101₀ : ∀ step₀ ∈ π₀, step₀.result.nextState ≠ 101 := by
        intro step₀ hmem
        exact hno101 step₀ (by simp [hmem])
      have hext₀ : ∃ (π₂ : List SymStep) (cfg₂ : SymConfig),
          SymReachablePath VerifierSym.transition (encodeInstanceSym inst) (π₀ ++ π₂) cfg₂ ∧
          cfg₂.state = 100 := by
        rcases hext with ⟨π₂, cfg₂, hpath₂, hacc₂⟩
        refine ⟨[step] ++ π₂, cfg₂, ?_, hacc₂⟩
        simpa [List.append_assoc] using hpath₂
      by_cases hq1 : cfg₁.state = 2
      · -- 2 支:next = 3
        have h3 : step.result.nextState = 3 := by
          have hcls := l3a_q2_next_class cfg₁.state (cfg₁.tape cfg₁.headPos) step.result htrans hq1
          rcases hcls with h2 | h3 | h101
          · omega
          · exact h3
          · exfalso; exact hne' h101
        have htrans₂ : step.result ∈ VerifierSym.transition (2, cfg₁.tape cfg₁.headPos) := by
          simpa [hq1] using htrans
        have hbnd := trans2_next3 (cfg₁.tape cfg₁.headPos) step.result htrans₂ h3
        rcases hbnd with ⟨hbndr, hres⟩
        have hL1 : cfg₁.headPos = (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) :=
          l3a_q2_read_boundary_at_L1 inst hm hpos htarget hprev hext₀ hq1 hbndr
        -- cfg₁ 带无 α(态 2:q2_scan + S3 + 布局)
        have hnoα₁ : ∀ p : ℤ, (cfg₁.tape p).1 ≠ SymKind.alpha := by
          intro p hpα
          have hinit : ((symInitialConfig (encodeInstanceSym inst)).tape p).1 = SymKind.alpha :=
            l3a_alpha_pos_in_initial inst π₀ cfg₁ hprev p hpα
          have hge0 : 0 ≤ p ∧ p.toNat < (encodeInstanceSym inst).length := by
            by_cases hpos : 0 ≤ p
            · by_cases hlen : p.toNat < (encodeInstanceSym inst).length
              · exact ⟨hpos, hlen⟩
              · exfalso
                have hblank : (symInitialConfig (encodeInstanceSym inst)).tape p = Sym.blank := by
                  unfold symInitialConfig
                  dsimp
                  rw [dif_neg]
                  intro hg
                  exact hlen hg.2
                have hc : (Sym.blank).1 = SymKind.alpha := by
                  simpa [hblank] using hinit
                have hnb : (Sym.blank).1 ≠ SymKind.alpha := by
                  decide
                exact hnb hc
            · exfalso
              have hblank : (symInitialConfig (encodeInstanceSym inst)).tape p = Sym.blank := by
                unfold symInitialConfig
                dsimp
                rw [dif_neg]
                intro hg
                exact hpos hg.1
              have hc : (Sym.blank).1 = SymKind.alpha := by
                simpa [hblank] using hinit
              have hnb : (Sym.blank).1 ≠ SymKind.alpha := by
                decide
              exact hnb hc
          have hinit' : ((encodeInstanceSym inst)[p.toNat]).1 = SymKind.alpha := by
            have hget : (symInitialConfig (encodeInstanceSym inst)).tape p =
                (encodeInstanceSym inst)[p.toNat] := by
              unfold symInitialConfig
              dsimp
              rw [dif_pos]
              exact hge0
            simpa [hget] using hinit
          have hzone := l3a_initial_alpha_in_elem_zone inst hm hge0.2 hinit'
          have hcast : (p.toNat : ℤ) = p := Int.toNat_of_nonneg hge0.1
          have hpge : (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) ≤ p := by
            rw [← hcast]
            omega
          have hplt : p < (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by
            rw [← hcast]
            have h2 : (p.toNat : ℤ) ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := by
              omega
            omega
          have hsteps : SymSteps VerifierSym.transition
              (symInitialConfig (encodeInstanceSym inst)) π₀ cfg₁ :=
            (symSteps_initial_iff VerifierSym.transition (encodeInstanceSym inst) π₀ cfg₁).2 hprev
          have hscan := l3a_q2_scan inst hsteps hno101₀ hno100₀ hq1
          have hnb : (cfg₁.tape p).1 ≠ SymKind.alpha :=
            hscan p hpge (by simpa [hL1] using hplt)
          exact hnb hpα
        -- 步写(2 转 3 写回 s = boundary,Dir.S 不动)
        rw [symStepConfig]
        dsimp
        by_cases hpeq : p = cfg₁.headPos
        · rw [if_pos hpeq]
          simp [hres]
          intro hα
          have hnb : SymKind.boundary ≠ SymKind.alpha := by
            decide
          exact hnb (by simpa [hbndr] using hα)
        · rw [if_neg hpeq]
          exact hnoα₁ p
      · -- 3+ 支:源 ≥3 且 ≠101
        have hge1 : cfg₁.state ≥ 3 := by
          have hsrc := l3a_ge3_next_src_not_le1 cfg₁.state (cfg₁.tape cfg₁.headPos) step.result
            htrans hq' hne'
          omega
        have hne1 : cfg₁.state ≠ 101 := by
          intro h101
          have htrans101 : step.result ∈ VerifierSym.transition (101, cfg₁.tape cfg₁.headPos) := by
            simpa [h101] using htrans
          have habs := symTransition_trap101_absorb (cfg₁.tape cfg₁.headPos) step.result htrans101
          exact hne' habs
        have hnoα₁ : ∀ p : ℤ, (cfg₁.tape p).1 ≠ SymKind.alpha :=
          ih hext₀ hno100₀ hno101₀ hge1 hne1
        rw [symStepConfig]
        dsimp
        by_cases hpeq : p = cfg₁.headPos
        · rw [if_pos hpeq]
          have hqne100 : cfg₁.state ≠ 100 := by
            simpa [hfrom] using hno100 step (by simp)
          have hqlt : cfg₁.state < 102 :=
            q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg₁ hprev
          have hw := forkBridge_no_write_branch cfg₁.state hqlt hqne100
            (cfg₁.tape cfg₁.headPos) step.result htrans hne'
          exact hw.1
        · rw [if_neg hpeq]
          exact hnoα₁ p


/-- 分支性 = kind ∈ {α, β}(8 种 kind 全展开;编码无 β,带上无 β 另证)。
    (Bool 版本:decide 显式,避免 Prop↔Bool 混写导致 rw 模式失配。) -/
lemma l3a_isBranch_iff_alpha_or_beta (s : Sym) :
    Sym.isBranch s = decide (s.1 = SymKind.alpha ∨ s.1 = SymKind.beta) := by
  rcases s with ⟨k, m⟩
  cases k <;> simp [Sym.isBranch, SymKind.isBranch]

/-- S5c(1):前字符非分支 ⟹ 其第 4 格 im = false(L 块 st9 读 tprev 第 4 格)。 -/
lemma l3a_tprev_getD3_im_of_not_branch (s : Sym) (hs : Sym.isBranch s = false) :
    F4.im ((symTo4F4 s).getD 3 F4.zero) = false := by
  rw [l3a_symTo4F4_getD3_im, hs]

/-- S5c(2):写符号非分支 ⟹ 写符号第 4 格 im = false(R 块 st11 读 w3)。 -/
lemma l3a_write_getD3_im_of_not_branch (r : SymTransResult) (hw : Sym.isBranch r.writeSym = false) :
    F4.im ((symTo4F4 r.writeSym).getD 3 F4.zero) = false := by
  rw [l3a_symTo4F4_getD3_im, hw]

/-- S5c(3):自身非分支 ⟹ st3 读的 c3 格 im = false(块首字符非分支 ⟹ st3 读 im=false)。 -/
lemma l3a_cell_getD3_im_of_not_branch (s : Sym) (hs : Sym.isBranch s = false) :
    F4.im ((symTo4F4 s).getD 3 F4.zero) = false := by
  rw [l3a_symTo4F4_getD3_im, hs]


/-- S5c 主干:态 ≥3 且 ≠101 ⟹ 带无分支(isBranch = false 全带)。
    = l3a_no_alpha_ge3(无 α)+ no_beta_invariant(无 β)+ isBranch ↔ α∨β。
    (消费者:L 块 st9 读 tprev 第 4 格 im=false;R 块 st11 读 w3 亦排除。) -/
lemma l3a_no_branch_ge3 (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (hpos : ∀ v ∈ inst.elements, 0 < v) (htarget : 0 < inst.target)
    {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg)
    (hext : ∃ (π₂ : List SymStep) (cfg₂ : SymConfig),
      SymReachablePath VerifierSym.transition (encodeInstanceSym inst) (π ++ π₂) cfg₂ ∧
      cfg₂.state = 100)
    (hno100 : ∀ step ∈ π, step.fromState ≠ 100)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101) :
    cfg.state ≥ 3 → cfg.state ≠ 101 →
    ∀ p : ℤ, Sym.isBranch (cfg.tape p) = false := by
  intro hge hne p
  have hα : (cfg.tape p).1 ≠ SymKind.alpha :=
    l3a_no_alpha_ge3 inst hm hpos htarget h hext hno100 hno101 hge hne p
  have hβ : (cfg.tape p).1 ≠ SymKind.beta :=
    no_beta_invariant inst π cfg h p
  unfold Sym.isBranch SymKind.isBranch
  rw [decide_eq_false_iff_not]
  intro hk
  rcases hk with hA | hB
  · exact hα hA
  · exact hβ hB


/-- 表级:移动 L 的转移(且非 101 死步)源态 ≥ 3(0/1 全 R(l3a_le1_move_R)、
    2 自环 R/转 3 S(trans2_next3)——低态域永不左移;101 吸收行由 hne 排除)。
    (L 块左邻非 α 论证的前件:源 cfg 态 ≥ 3 ⟹ l3a_no_branch_ge3 可用。) -/
lemma l3a_Lmove_src_ge3 (q : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (hL : r.moveDir = Dir.L)
    (hne : r.nextState ≠ 101) : 3 ≤ q := by
  by_cases hqin : q ∈ VerifierSym.legalStates
  · have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition ((q : ℕ), s) →
          r.moveDir = Dir.L → r.nextState ≠ 101 → 3 ≤ (q : ℕ) := by
      native_decide
    have hqlt : q < 102 := by
      simp [VerifierSym.legalStates] at hqin
      omega
    exact hb ⟨q, hqlt⟩ s r hr hL hne
  · rw [transition_of_not_legal q s hqin] at hr
    simp at hr
    subst r
    simp at hL

/-- 单例 filter 精确长度:isBranch step.readSym 真 ⟹ 1,假 ⟹ 0。
    (路径级 fork 计数的 cons 支分解。与 l3a_filter_singleton_len_le1/len0 互补。) -/
lemma l3a_filter_singleton_len (step : SymStep) :
    ([step].filter (fun st => Sym.isBranch st.readSym)).length =
      if Sym.isBranch step.readSym then 1 else 0 := by
  by_cases hb : Sym.isBranch step.readSym
  · simp only [List.filter, hb]; norm_num
  · simp only [List.filter, hb]; norm_num

/-- 元素非空 ⟹ 元素区编码非空(每元素前缀 [α],长度 ≥ 1)。
    (l3a_no_branch_ge3 系 hm 前提由 hne : elements ≠ [] 推出。) -/
lemma l3a_encodeElementsSym_length_pos (elems : List ℕ) (hne : elems ≠ []) :
    0 < (encodeElementsSym elems).length := by
  cases elems with
  | nil => exact (hne rfl).elim
  | cons v rest =>
      cases rest with
      | nil => simp [encodeElementsSym]
      | cons w rest' => simp [encodeElementsSym]


/-- S5d 件 1:块内 im-true 读分类(前字符非分支 + 写符号非分支时)。
    12 微步中读 im-true ⟺ i = 3 且自身分支(st0-2/4-8 恒 false;st9-11 由 hprev_nb/hw_nb 排除)。
    (证明体 = project_block 拆解骨架照抄 + 结尾 interval_cases 分类。) -/
lemma l3a_goodblock_read_im_classify {w : List F4} {cfgc : CBTMConfig subsetSumCBTM w}
    {π : ComputationPath} {cfgc' : CBTMConfig subsetSumCBTM w} {cfgs : SymConfig}
    {p : ℤ} {q : ℕ} {sym : Sym} {r : SymTransResult}
    (hblock : GoodBlock w cfgc π cfgc' cfgs p q sym r)
    (hrs : r.nextState < 101)
    (hprev_nb : r.moveDir = Dir.L → Sym.isBranch (cfgs.tape (p - 1)) = false)
    (hw_nb : Sym.isBranch r.writeSym = false) :
    ∀ i : ℕ, i < 12 →
      F4.im ((π.getD i (TransitionStep.mk (encodeState q 0 0) F4.zero
        (CBTMTransResult.mk (encodeState q 0 0) F4.zero Dir.S))).readSym) = true →
      i = 3 ∧ Sym.isBranch sym = true := by
  rcases hblock with ⟨hpath, hlen, hst, hp, hcorr, hread, hq, hbranchq, hvalid_sym, hstep4, hmk, hr, hst', hhead'⟩
  let cells := symTo4F4 sym
  let c0 := cells.getD 0 F4.zero
  let c1 := cells.getD 1 F4.zero
  let c2 := cells.getD 2 F4.zero
  let c3 := cells.getD 3 F4.zero
  let nrs := symTo4F4 r.writeSym
  let w0 := nrs.getD 0 F4.zero
  let w1 := nrs.getD 1 F4.zero
  let w2 := nrs.getD 2 F4.zero
  let w3 := nrs.getD 3 F4.zero
  let d := r.moveDir
  let qn := min r.nextState 101
  let b01 := bufOf3 c0 F4.zero F4.zero
  let b12 := bufOf3 c0 c1 F4.zero
  let b3 := bufOf3 c0 c1 c2
  let regr := encodeResult r
  let tprev := symTo4F4 (cfgs.tape (p - 1))
  let s8 := w0
  let s9 := match d with | Dir.R => w1 | Dir.L => tprev.getD 3 F4.zero | Dir.S => w0
  let s10 := match d with | Dir.R => w2 | Dir.L => tprev.getD 2 F4.zero | Dir.S => w0
  let s11 := match d with | Dir.R => w3 | Dir.L => tprev.getD 1 F4.zero | Dir.S => w0
  -- 1. 拆出 12 步
  rcases tapeSteps_split_last hpath (by intro h; simp [h] at hlen) with
    ⟨step11, π10, cfg11, hπe11, h10, hf11, hr11, ht11, hc11⟩
  rcases tapeSteps_split_last h10 (by
      intro h
      have : (π10 ++ [step11]).length = 12 := by simpa [hπe11] using hlen
      simp [h] at this) with
    ⟨step10, π9, cfg10, hπe10, h9, hf10, hr10, ht10, hc10⟩
  rcases tapeSteps_split_last h9 (by
      intro h
      have : (π9 ++ [step10, step11]).length = 12 := by simpa [hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step9, π8, cfg9, hπe9, h8, hf9, hr9, ht9, hc9⟩
  rcases tapeSteps_split_last h8 (by
      intro h
      have : (π8 ++ [step9, step10, step11]).length = 12 := by simpa [hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step8, π7, cfg8, hπe8, h7, hf8, hr8, ht8, hc8⟩
  rcases tapeSteps_split_last h7 (by
      intro h
      have : (π7 ++ [step8, step9, step10, step11]).length = 12 := by simpa [hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step7, π6, cfg7, hπe7, h6, hf7, hr7, ht7, hc7⟩
  rcases tapeSteps_split_last h6 (by
      intro h
      have : (π6 ++ [step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step6, π5, cfg6, hπe6, h5, hf6, hr6, ht6, hc6⟩
  rcases tapeSteps_split_last h5 (by
      intro h
      have : (π5 ++ [step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step5, π4, cfg5, hπe5, h4, hf5, hr5, ht5, hc5⟩
  rcases tapeSteps_split_last h4 (by
      intro h
      have : (π4 ++ [step5, step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step4, π3, cfg4, hπe4, h3, hf4, hr4, ht4, hc4⟩
  rcases tapeSteps_split_last h3 (by
      intro h
      have : (π3 ++ [step4, step5, step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step3, π2, cfg3, hπe3, h2, hf3, hr3, ht3, hc3⟩
  rcases tapeSteps_split_last h2 (by
      intro h
      have : (π2 ++ [step3, step4, step5, step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe3, hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step2, π1, cfg2, hπe2, h1, hf2, hr2, ht2, hc2⟩
  rcases tapeSteps_split_last h1 (by
      intro h
      have : (π1 ++ [step2, step3, step4, step5, step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe2, hπe3, hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step1, π0, cfg1, hπe1, h0, hf1, hr1, ht1, hc1⟩
  rcases tapeSteps_split_last h0 (by
      intro h
      have : (π0 ++ [step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe1, hπe2, hπe3, hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step0, πn, cfgc0, hπen, hn, hf0, hr0, ht0, hc0⟩
  have hπn : πn = [] := by
    have hsum : (πn ++ [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11]).length = 12 := by
      simpa [hπen, hπe1, hπe2, hπe3, hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
    have hsum' : πn.length + 12 = 12 := by simpa using hsum
    have hlen0 : πn.length = 0 := by omega
    cases πn with
    | nil => rfl
    | cons x xs => simp at hlen0
  have hcfg0 : cfgc0 = cfgc := by
    exact tapeSteps_empty hn hπn
  subst πn
  subst cfgc0
  -- 3. 前 4 格取值与 im 事实
  have hc0v : cfgc.tapeAt (4 * p) = c0 := by
    have hc := hcorr.2.2 p 0 (by norm_num)
    simpa [hread, c0, cells] using hc
  have hc1v : cfgc.tapeAt (4 * p + 1) = c1 := by
    have hc := hcorr.2.2 p 1 (by norm_num)
    simpa [hread, c1, cells] using hc
  have hc2v : cfgc.tapeAt (4 * p + 2) = c2 := by
    have hc := hcorr.2.2 p 2 (by norm_num)
    simpa [hread, c2, cells] using hc
  have hc3v : cfgc.tapeAt (4 * p + 3) = c3 := by
    have hc := hcorr.2.2 p 3 (by norm_num)
    simpa [hread, c3, cells] using hc
  have him0 : F4.im c0 = false := by simpa [c0, cells] using (symTo4F4_im_false_012 sym).1
  have him1 : F4.im c1 = false := by simpa [c1, cells] using (symTo4F4_im_false_012 sym).2.1
  have him2 : F4.im c2 = false := by simpa [c2, cells] using (symTo4F4_im_false_012 sym).2.2
  have him_c3 : F4.im c3 = Sym.isBranch sym := by
    dsimp [c3, cells]
    exact l3a_symTo4F4_getD3_im sym
  have hw0 : F4.im w0 = false := by simpa [w0, nrs] using (symTo4F4_im_false_012 r.writeSym).1
  have hw1 : F4.im w1 = false := by simpa [w1, nrs] using (symTo4F4_im_false_012 r.writeSym).2.1
  have hw2 : F4.im w2 = false := by simpa [w2, nrs] using (symTo4F4_im_false_012 r.writeSym).2.2
  -- 4. 解码辅助
  have hb01 : b01 = bufOf3s 0 c0 0 := by
    dsimp [b01, bufOf3, bufOf3s]
    rcases c0 with ⟨r0, i0⟩
    cases r0 <;> cases i0 <;> simp [F4.zero, F4.one, F4.alpha, F4.beta]
  have hb12 : b12 = b01 + bufOf3s 1 c1 b01 := by
    dsimp [b12, b01, bufOf3, bufOf3s]
    rcases c0 with ⟨r0, i0⟩ <;> rcases c1 with ⟨r1, i1⟩
    cases r0 <;> cases i0 <;> cases r1 <;> cases i1 <;> simp [F4.zero, F4.one, F4.alpha, F4.beta]
  have hb3 : b3 = b12 + bufOf3s 2 c2 b12 := by
    dsimp [b3, b12, b01, bufOf3, bufOf3s]
    rcases c0 with ⟨r0, i0⟩ <;> rcases c1 with ⟨r1, i1⟩ <;> rcases c2 with ⟨r2, i2⟩
    cases r0 <;> cases i0 <;> cases r1 <;> cases i1 <;> cases r2 <;> cases i2 <;>
      simp [F4.zero, F4.one, F4.alpha, F4.beta]
  have hdec1' : decodeState (encodeState (min q 101) 1 b01) = (min q 101, 1, b01) := by
    apply decodeState_encodeState
    · norm_num
    · have hb : b01 ≤ 63 := by
        dsimp [b01, bufOf3]
        rcases c0 with ⟨r0, i0⟩
        cases r0 <;> cases i0 <;> simp [F4.zero, F4.one, F4.alpha, F4.beta]
      exact lt_of_le_of_lt hb (by norm_num)
  have hdec2' : decodeState (encodeState (min q 101) 2 b12) = (min q 101, 2, b12) := by
    apply decodeState_encodeState
    · norm_num
    · have hb : b12 ≤ 63 := by
        dsimp [b12, bufOf3]
        rcases c0 with ⟨r0, i0⟩ <;> rcases c1 with ⟨r1, i1⟩
        cases r0 <;> cases i0 <;> cases r1 <;> cases i1 <;> simp [F4.zero, F4.one, F4.alpha, F4.beta]
      exact lt_of_le_of_lt hb (by norm_num)
  have hdec3' : decodeState (encodeState (min q 101) 3 b3) = (min q 101, 3, b3) := by
    apply decodeState_encodeState
    · norm_num
    · have hb : b3 ≤ 63 := by
        dsimp [b3, bufOf3]
        rcases c0 with ⟨r0, i0⟩ <;> rcases c1 with ⟨r1, i1⟩ <;> rcases c2 with ⟨r2, i2⟩
        cases r0 <;> cases i0 <;> cases r1 <;> cases i1 <;> cases r2 <;> cases i2 <;>
          simp [F4.zero, F4.one, F4.alpha, F4.beta]
      exact lt_of_le_of_lt hb (by norm_num)
  have hqle : q ≤ 101 := hq
  have hns : r.nextState ≤ 101 := transition_nextState_le101 q sym hqle r hr
  have hqnn : min qn 101 = qn := by
    dsimp [qn]
    rw [Nat.min_eq_left]
    exact Nat.min_le_right _ _
  have hqne : qn ≠ 101 := by
    dsimp [qn]
    rw [Nat.min_eq_left (le_of_lt hrs)]
    exact ne_of_lt hrs
  have hregr : regr < 8192 := by
    dsimp [regr, encodeResult]
    have hsk : skOf r.writeSym.1 + (if r.writeSym.2 then 9 else 0) < 18 := by
      rcases r.writeSym with ⟨k, mk⟩
      cases k <;> cases mk <;> simp [skOf]
    have hdir : dirOf r.moveDir < 3 := by
      cases r.moveDir <;> simp [dirOf]
    omega
  have hdecph (ph : ℕ) (hphl : ph < 12) :
      decodeState (encodeState qn ph regr) = (qn, ph, regr) := by
    apply decodeState_encodeState
    · simpa [stepsPerSym] using hphl
    · simpa [regBound] using hregr
  -- 5. 第 0 步:读 c0(im=false)→ 唯一结果 R
  have hst0 : step0.fromState = encodeState q 0 0 := by simpa [hst] using hf0
  have hrd0 : step0.readSym = c0 := by
    simpa [hc0v, hp, c0] using hr0
  have hmem0 : step0.result ∈ transition4 (encodeState q 0 0) c0 := by
    have ht0' : step0.result ∈ subsetSumCBTM.transition (cfgc.state, cfgc.tapeAt cfgc.headPos, cfgc.headPos) := ht0
    rw [hst, hp, hc0v] at ht0'
    simpa [subsetSumCBTM] using ht0'
  have hres0 : step0.result = CBTMTransResult.mk (encodeState (min q 101) 1 b01) c0 Dir.R := by
    dsimp [transition4] at hmem0
    rw [decodeState_encodeState q 0 0 (by norm_num) (by norm_num)] at hmem0
    simp [him0] at hmem0
    simpa [hb01] using hmem0
  have hp1 : cfg1.headPos = 4 * p + 1 := by
    rw [hc0]
    dsimp [stepConfig]
    rw [hres0]
    dsimp
    rw [hp]
    simp [Dir.toInt]
  -- 6. 第 1 步:读 c1
  have hst1 : step1.fromState = encodeState (min q 101) 1 b01 := by
    have hst1' : step1.fromState = cfg1.state := by simpa using hf1
    rw [hst1']
    rw [hc0]
    dsimp [stepConfig]
    rw [hres0]
  have hrd1 : step1.readSym = c1 := by
    have hrd1' : step1.readSym = cfg1.tapeAt cfg1.headPos := by simpa using hr1
    rw [hrd1', hp1]
    rw [hc0]
    rw [stepConfig_tapeAt_eq_of_ne cfgc step0.result (4 * p + 1) (by rw [hp]; omega)]
    rw [hc1v]
  have hmem1 : step1.result ∈ transition4 (encodeState (min q 101) 1 b01) c1 := by
    have ht1' : step1.result ∈ subsetSumCBTM.transition (cfg1.state, cfg1.tapeAt cfg1.headPos, cfg1.headPos) := ht1
    rw [show cfg1.state = encodeState (min q 101) 1 b01 from by simpa [hf1] using hst1] at ht1'
    rw [hp1] at ht1'
    rw [show cfg1.tapeAt (4 * p + 1) = c1 from by simpa [hr1, hp1] using hrd1] at ht1'
    simpa [subsetSumCBTM] using ht1'
  have hres1 : step1.result = CBTMTransResult.mk (encodeState (min q 101) 2 (b01 + bufOf3s 1 c1 b01)) c1 Dir.R := by
    dsimp [transition4] at hmem1
    rw [hdec1'] at hmem1
    simp [him1] at hmem1
    simpa using hmem1
  have hp2 : cfg2.headPos = 4 * p + 2 := by
    rw [hc1]
    dsimp [stepConfig]
    rw [hres1]
    dsimp
    rw [hp1]
    simp [Dir.toInt]
    omega
  -- 7. 第 2 步:读 c2
  have hst2 : step2.fromState = encodeState (min q 101) 2 b12 := by
    have hst2' : step2.fromState = cfg2.state := by simpa using hf2
    rw [hst2']
    rw [hc1]
    dsimp [stepConfig]
    rw [hres1]
    dsimp
    rw [← hb12]
  have hrd2 : step2.readSym = c2 := by
    have hrd2' : step2.readSym = cfg2.tapeAt cfg2.headPos := by simpa using hr2
    rw [hrd2', hp2]
    rw [hc1]
    rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * p + 2) (by rw [hp1]; omega)]
    rw [hc0]
    rw [stepConfig_tapeAt_eq_of_ne cfgc step0.result (4 * p + 2) (by rw [hp]; omega)]
    rw [hc2v]
  have hmem2 : step2.result ∈ transition4 (encodeState (min q 101) 2 b12) c2 := by
    have ht2' : step2.result ∈ subsetSumCBTM.transition (cfg2.state, cfg2.tapeAt cfg2.headPos, cfg2.headPos) := ht2
    rw [show cfg2.state = encodeState (min q 101) 2 b12 from by simpa [hf2] using hst2] at ht2'
    rw [hp2] at ht2'
    rw [show cfg2.tapeAt (4 * p + 2) = c2 from by simpa [hr2, hp2] using hrd2] at ht2'
    simpa [subsetSumCBTM] using ht2'
  have hres2 : step2.result = CBTMTransResult.mk (encodeState (min q 101) 3 (b12 + bufOf3s 2 c2 b12)) c2 Dir.R := by
    dsimp [transition4] at hmem2
    rw [hdec2'] at hmem2
    simp [him2] at hmem2
    simpa using hmem2
  have hp3 : cfg3.headPos = 4 * p + 3 := by
    rw [hc2]
    dsimp [stepConfig]
    rw [hres2]
    dsimp
    rw [hp2]
    simp [Dir.toInt]
    omega
  -- 8. 第 3 步(合成步):hstep4 直接钉死
  have hst3 : step3.fromState = encodeState (min q 101) 3 b3 := by
    have hst3' : step3.fromState = cfg3.state := by simpa using hf3
    rw [hst3']
    rw [hc2]
    dsimp [stepConfig]
    rw [hres2]
    dsimp
    rw [← hb3]
  have hrd3 : step3.readSym = c3 := by
    have hrd3' : step3.readSym = cfg3.tapeAt cfg3.headPos := by simpa using hr3
    rw [hrd3', hp3]
    rw [hc2]
    rw [stepConfig_tapeAt_eq_of_ne cfg2 step2.result (4 * p + 3) (by rw [hp2]; omega)]
    rw [hc1]
    rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * p + 3) (by rw [hp1]; omega)]
    rw [hc0]
    rw [stepConfig_tapeAt_eq_of_ne cfgc step0.result (4 * p + 3) (by rw [hp]; omega)]
    rw [hc3v]
  have hstep3' : step3.result = CBTMTransResult.mk (encodeState r.nextState 4 regr) ((symTo4F4 r.writeSym).getLastD F4.zero) Dir.L := by
    have hπ' : π = [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11] := by
      rw [hπe11, hπe10, hπe9, hπe8, hπe7, hπe6, hπe5, hπe4, hπe3, hπe2, hπe1, hπen]
      rfl
    have hg : π.get ⟨3, by omega⟩ = step3 := by
      simpa [hπ']
    rw [hg] at hstep4
    simpa [regr] using hstep4
  have hp4 : cfg4.headPos = 4 * p + 2 := by
    rw [hc3]
    dsimp [stepConfig]
    rw [hstep3']
    dsimp
    rw [hp3]
    simp [Dir.toInt]
    omega
  -- 9. 第 4 步:读 c2 写 w2 移 L
  have hst4 : step4.fromState = encodeState r.nextState 4 regr := by
    have hst4' : step4.fromState = cfg4.state := by simpa using hf4
    rw [hst4']
    rw [hc3]
    dsimp [stepConfig]
    rw [hstep3']
  have hrd4 : step4.readSym = c2 := by
    have hrd4' : step4.readSym = cfg4.tapeAt cfg4.headPos := by simpa using hr4
    rw [hrd4', hp4]
    rw [hc3]
    rw [stepConfig_tapeAt_eq_of_ne cfg3 step3.result (4 * p + 2) (by rw [hp3]; omega)]
    rw [hc2]
    rw [stepConfig_tapeAt_eq_of_eq cfg2 step2.result (4 * p + 2) (by rw [hp2])]
    rw [hres2]
  have hres4 : step4.result = CBTMTransResult.mk (encodeState qn 5 regr) w2 Dir.L := by
    have hmem4 : step4.result ∈ transition4 (encodeState r.nextState 4 regr) c2 := by
      have ht4' : step4.result ∈ subsetSumCBTM.transition (cfg4.state, cfg4.tapeAt cfg4.headPos, cfg4.headPos) := ht4
      rw [show cfg4.state = encodeState r.nextState 4 regr from by simpa [hf4] using hst4] at ht4'
      rw [hp4] at ht4'
      rw [show cfg4.tapeAt (4 * p + 2) = c2 from by simpa [hr4, hp4] using hrd4] at ht4'
      simpa [subsetSumCBTM] using ht4'
    have hdec4' : decodeState (encodeState r.nextState 4 regr) = (r.nextState, 4, regr) := by
      apply decodeState_encodeState
      · norm_num
      · simpa [regBound] using hregr
    dsimp [transition4] at hmem4
    rw [hdec4'] at hmem4
    simp [him2] at hmem4
    rw [decodeResult_encodeResult_ok r hmk] at hmem4
    dsimp [qn]
    simpa [w2, nrs] using hmem4
  have hp5 : cfg5.headPos = 4 * p + 1 := by
    rw [hc4]
    dsimp [stepConfig]
    rw [hres4]
    dsimp
    rw [hp4]
    simp [Dir.toInt]
    omega
  -- 10. 第 5 步:读 c1 写 w1 移 L
  have hrd5 : step5.readSym = c1 := by
    have hrd5' : step5.readSym = cfg5.tapeAt cfg5.headPos := by simpa using hr5
    rw [hrd5', hp5]
    rw [hc4]
    rw [stepConfig_tapeAt_eq_of_ne cfg4 step4.result (4 * p + 1) (by rw [hp4]; omega)]
    rw [hc3]
    rw [stepConfig_tapeAt_eq_of_ne cfg3 step3.result (4 * p + 1) (by rw [hp3]; omega)]
    rw [hc2]
    rw [stepConfig_tapeAt_eq_of_ne cfg2 step2.result (4 * p + 1) (by rw [hp2]; omega)]
    rw [hc1]
    rw [stepConfig_tapeAt_eq_of_eq cfg1 step1.result (4 * p + 1) (by rw [hp1])]
    rw [hres1]
  have hres5 : step5.result = CBTMTransResult.mk (encodeState qn 6 regr) ((symTo4F4 r.writeSym).getD 1 F4.zero) Dir.L := by
    have hmem5 : step5.result ∈ transition4 (encodeState qn 5 regr) c1 := by
      have ht5' : step5.result ∈ subsetSumCBTM.transition (cfg5.state, cfg5.tapeAt cfg5.headPos, cfg5.headPos) := ht5
      rw [show cfg5.state = encodeState qn 5 regr from by simpa [hf5, stepConfig, hc4, hres4]] at ht5'
      rw [hp5] at ht5'
      rw [show cfg5.tapeAt (4 * p + 1) = c1 from by simpa [hr5, hp5] using hrd5] at ht5'
      change step5.result ∈ transition4 (encodeState qn 5 regr) c1 at ht5'
      exact ht5'
    dsimp [transition4] at hmem5
    rw [hdecph 5 (by norm_num)] at hmem5
    simp [him1] at hmem5
    rw [decodeResult_encodeResult_ok r hmk] at hmem5
    rw [hqnn] at hmem5
    exact hmem5
  have hp6 : cfg6.headPos = 4 * p := by
    rw [hc5]
    dsimp [stepConfig]
    rw [hres5]
    dsimp
    rw [hp5]
    simp [Dir.toInt]
  -- 11. 第 6 步:读 c0 写 w0 移 S
  have hrd6 : step6.readSym = c0 := by
    have hrd6' : step6.readSym = cfg6.tapeAt cfg6.headPos := by simpa using hr6
    rw [hrd6', hp6]
    rw [hc5]
    rw [stepConfig_tapeAt_eq_of_ne cfg5 step5.result (4 * p) (by rw [hp5]; omega)]
    rw [hc4]
    rw [stepConfig_tapeAt_eq_of_ne cfg4 step4.result (4 * p) (by rw [hp4]; omega)]
    rw [hc3]
    rw [stepConfig_tapeAt_eq_of_ne cfg3 step3.result (4 * p) (by rw [hp3]; omega)]
    rw [hc2]
    rw [stepConfig_tapeAt_eq_of_ne cfg2 step2.result (4 * p) (by rw [hp2]; omega)]
    rw [hc1]
    rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * p) (by rw [hp1]; omega)]
    rw [hc0]
    rw [stepConfig_tapeAt_eq_of_eq cfgc step0.result (4 * p) (by rw [hp])]
    rw [hres0]
  have hres6 : step6.result = CBTMTransResult.mk (encodeState qn 7 regr) ((symTo4F4 r.writeSym).getD 0 F4.zero) Dir.S := by
    have hmem6 : step6.result ∈ transition4 (encodeState qn 6 regr) c0 := by
      have ht6' : step6.result ∈ subsetSumCBTM.transition (cfg6.state, cfg6.tapeAt cfg6.headPos, cfg6.headPos) := ht6
      rw [show cfg6.state = encodeState qn 6 regr from by simpa [hf6, stepConfig, hc5, hres5]] at ht6'
      rw [hp6] at ht6'
      rw [show cfg6.tapeAt (4 * p) = c0 from by simpa [hr6, hp6] using hrd6] at ht6'
      change step6.result ∈ transition4 (encodeState qn 6 regr) c0 at ht6'
      exact ht6'
    dsimp [transition4] at hmem6
    rw [hdecph 6 (by norm_num)] at hmem6
    simp [him0] at hmem6
    rw [decodeResult_encodeResult_ok r hmk] at hmem6
    rw [hqnn] at hmem6
    exact hmem6
  have hp7 : cfg7.headPos = 4 * p := by
    rw [hc6]
    dsimp [stepConfig]
    rw [hres6]
    dsimp
    rw [hp6]
    simp [Dir.toInt]
  -- 12. 第 7 步:读 w0 写原符号移 S
  have hrd7 : step7.readSym = w0 := by
    have hrd7' : step7.readSym = cfg7.tapeAt cfg7.headPos := by simpa using hr7
    rw [hrd7', hp7]
    rw [hc6]
    rw [stepConfig_tapeAt_eq_of_eq cfg6 step6.result (4 * p) (by rw [hp6])]
    rw [hres6]
  have hres7 : step7.result = CBTMTransResult.mk (encodeState qn 8 regr) w0 Dir.S := by
    have hmem7 : step7.result ∈ transition4 (encodeState qn 7 regr) w0 := by
      have ht7' : step7.result ∈ subsetSumCBTM.transition (cfg7.state, cfg7.tapeAt cfg7.headPos, cfg7.headPos) := ht7
      rw [show cfg7.state = encodeState qn 7 regr from by simpa [hf7, stepConfig, hc6, hres6]] at ht7'
      rw [hp7] at ht7'
      rw [show cfg7.tapeAt (4 * p) = w0 from by simpa [hr7, hp7] using hrd7] at ht7'
      change step7.result ∈ transition4 (encodeState qn 7 regr) w0 at ht7'
      exact ht7'
    dsimp [transition4] at hmem7
    rw [hdecph 7 (by norm_num)] at hmem7
    simp [hw0] at hmem7
    rw [hqnn] at hmem7
    rw [hmem7]
  have hp8 : cfg8.headPos = 4 * p := by
    rw [hc7]
    dsimp [stepConfig]
    rw [hres7]
    dsimp
    rw [hp7]
    simp [Dir.toInt]
  -- 13. 第 8 步:读 s8 = w0(im=false)
  have hrd8 : step8.readSym = s8 := by
    have hrd8' : step8.readSym = cfg8.tapeAt cfg8.headPos := by simpa using hr8
    rw [hrd8', hp8]
    rw [hc7]
    rw [stepConfig_tapeAt_eq_of_eq cfg7 step7.result (4 * p) (by rw [hp7])]
    rw [hres7]
  have him8s : F4.im s8 = false := by
    dsimp [s8]
    exact hw0
  have hres8 : step8.result = CBTMTransResult.mk (encodeState qn 9 regr) w0 (SymToF4.dirOf.match_1 (fun _ : Dir => Dir) r.moveDir (fun _ => Dir.R) (fun _ => Dir.L) (fun _ => Dir.S)) := by
    have hmem8 : step8.result ∈ transition4 (encodeState qn 8 regr) s8 := by
      have ht8' : step8.result ∈ subsetSumCBTM.transition (cfg8.state, cfg8.tapeAt cfg8.headPos, cfg8.headPos) := ht8
      rw [show cfg8.state = encodeState qn 8 regr from by simpa [hf8, stepConfig, hc7, hres7]] at ht8'
      rw [hp8] at ht8'
      rw [show cfg8.tapeAt (4 * p) = s8 from by simpa [hr8, hp8] using hrd8] at ht8'
      change step8.result ∈ transition4 (encodeState qn 8 regr) s8 at ht8'
      exact ht8'
    dsimp [transition4] at hmem8
    rw [hdecph 8 (by norm_num)] at hmem8
    simp [hw0, s8, hqne] at hmem8
    rw [decodeResult_encodeResult_ok r hmk] at hmem8
    rw [hqnn] at hmem8
    rw [hmem8]
  have hp9 : cfg9.headPos = 4 * p + d.toInt := by
    rw [hc8]
    dsimp [stepConfig]
    rw [hres8]
    dsimp
    rw [hp8]
    dsimp [d]
    rcases hd : r.moveDir with _ | _ | _ <;> simp [hd, Dir.toInt]
  -- 14. hπ' 与 0-8 步分类(共享)
  have hπ' : π = [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11] := by
    rw [hπe11, hπe10, hπe9, hπe8, hπe7, hπe6, hπe5, hπe4, hπe3, hπe2, hπe1, hπen]
    rfl
  have hcls08 : ∀ i : ℕ, i < 9 →
      F4.im ((π.getD i (TransitionStep.mk (encodeState q 0 0) F4.zero
        (CBTMTransResult.mk (encodeState q 0 0) F4.zero Dir.S))).readSym) = true →
      i = 3 ∧ Sym.isBranch sym = true := by
    intro i hi himi
    rw [hπ'] at himi
    interval_cases i <;> simp at himi
    · rw [hrd0, him0] at himi
      cases himi
    · rw [hrd1, him1] at himi
      cases himi
    · rw [hrd2, him2] at himi
      cases himi
    · rw [hrd3, him_c3] at himi
      exact ⟨rfl, himi⟩
    · rw [hrd4, him2] at himi
      cases himi
    · rw [hrd5, him1] at himi
      cases himi
    · rw [hrd6, him0] at himi
      cases himi
    · rw [hrd7, hw0] at himi
      cases himi
    · rw [hrd8, him8s] at himi
      cases himi
  -- 15. 第 9-11 步:按 moveDir 分类
  rcases hd : r.moveDir with _ | _ | _
  · -- d = L:读 tprev 第 4/3/2 格
    have hst9 : step9.fromState = encodeState qn 9 regr := by
      have hst9' : step9.fromState = cfg9.state := by simpa using hf9
      rw [hst9']
      rw [hc8]
      dsimp [stepConfig]
      rw [hres8]
    have hrd9 : step9.readSym = s9 := by
      have hrd9' : step9.readSym = cfg9.tapeAt cfg9.headPos := by simpa using hr9
      rw [hrd9', hp9]
      dsimp [d]
      simp [hd, Dir.toInt]
      rw [hc8]
      rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * p + -1) (by rw [hp8]; omega)]
      rw [hc7]
      rw [stepConfig_tapeAt_eq_of_ne cfg7 step7.result (4 * p + -1) (by rw [hp7]; omega)]
      rw [hc6]
      rw [stepConfig_tapeAt_eq_of_ne cfg6 step6.result (4 * p + -1) (by rw [hp6]; omega)]
      rw [hc5]
      rw [stepConfig_tapeAt_eq_of_ne cfg5 step5.result (4 * p + -1) (by rw [hp5]; omega)]
      rw [hc4]
      rw [stepConfig_tapeAt_eq_of_ne cfg4 step4.result (4 * p + -1) (by rw [hp4]; omega)]
      rw [hc3]
      rw [stepConfig_tapeAt_eq_of_ne cfg3 step3.result (4 * p + -1) (by rw [hp3]; omega)]
      rw [hc2]
      rw [stepConfig_tapeAt_eq_of_ne cfg2 step2.result (4 * p + -1) (by rw [hp2]; omega)]
      rw [hc1]
      rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * p + -1) (by rw [hp1]; omega)]
      rw [hc0]
      rw [stepConfig_tapeAt_eq_of_ne cfgc step0.result (4 * p + -1) (by rw [hp]; omega)]
      rw [show 4 * p + -1 = 4 * (p - 1) + (3 : ℕ) by omega]
      rw [hcorr.2.2 (p - 1) 3 (by norm_num)]
      dsimp [s9, d, tprev]
      simp [hd]
    have him9s : F4.im s9 = false := by
      dsimp [s9, d, tprev]
      simp [hd]
      simpa using (l3a_symTo4F4_getD3_im (cfgs.tape (p - 1))) ▸ (hprev_nb hd)
    have hmem9 : step9.result ∈ transition4 (encodeState qn 9 regr) s9 := by
      have ht9' : step9.result ∈ subsetSumCBTM.transition (cfg9.state, cfg9.tapeAt cfg9.headPos, cfg9.headPos) := ht9
      rw [show cfg9.state = encodeState qn 9 regr from by simpa [hf9] using hst9] at ht9'
      rw [hp9] at ht9'
      dsimp [d] at ht9'
      simp [hd, Dir.toInt] at ht9'
      rw [show cfg9.tapeAt (4 * p + -1) = s9 from by simpa [hr9, hp9, d, hd, Dir.toInt] using hrd9] at ht9'
      simpa [subsetSumCBTM] using ht9'
    have hnotrap9 : step9.result ≠ CBTMTransResult.mk (encodeState 101 10 0) F4.zero Dir.S := by
      intro htr9
      have hp10t : cfg10.headPos = 4 * p + -1 := by
        rw [hc9]
        dsimp [stepConfig]
        rw [htr9]
        dsimp
        rw [hp9]
        dsimp [d]
        simp [hd, Dir.toInt]
        first | done | omega
      have hrd10t : step10.readSym = F4.zero := by
        have hrd10' : step10.readSym = cfg10.tapeAt cfg10.headPos := by simpa using hr10
        rw [hrd10', hp10t]
        rw [hc9]
        rw [stepConfig_tapeAt_eq_of_eq cfg9 step9.result (4 * p + -1) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt])]
        rw [htr9]
      have hmem10t : step10.result ∈ transition4 (encodeState 101 10 0) F4.zero := by
        have ht10' : step10.result ∈ subsetSumCBTM.transition (cfg10.state, cfg10.tapeAt cfg10.headPos, cfg10.headPos) := ht10
        rw [show cfg10.state = encodeState 101 10 0 from by simpa [stepConfig, hc9, htr9]] at ht10'
        rw [hp10t] at ht10'
        rw [show cfg10.tapeAt (4 * p + -1) = F4.zero from by simpa [hr10, hp10t] using hrd10t] at ht10'
        simpa [subsetSumCBTM] using ht10'
      have hres10t : step10.result = CBTMTransResult.mk (encodeState 101 11 0) F4.zero Dir.S :=
        trap_step10_forced step10.result hmem10t
      have hp11t : cfg11.headPos = 4 * p + -1 := by
        rw [hc10]
        dsimp [stepConfig]
        rw [hres10t]
        dsimp
        rw [hc9]
        dsimp [stepConfig]
        rw [htr9]
        dsimp
        rw [hp9]
        dsimp [d]
        simp [hd, Dir.toInt]
        first | done | omega
      have hrd11t : step11.readSym = F4.zero := by
        have hrd11' : step11.readSym = cfg11.tapeAt cfg11.headPos := by simpa using hr11
        rw [hrd11', hp11t]
        rw [hc10]
        rw [stepConfig_tapeAt_eq_of_eq cfg10 step10.result (4 * p + -1) (by rw [hp10t])]
        rw [hres10t]
      have hmem11t : step11.result ∈ transition4 (encodeState 101 11 0) F4.zero := by
        have ht11' : step11.result ∈ subsetSumCBTM.transition (cfg11.state, cfg11.tapeAt cfg11.headPos, cfg11.headPos) := ht11
        rw [show cfg11.state = encodeState 101 11 0 from by simpa [stepConfig, hc10, hres10t]] at ht11'
        rw [hp11t] at ht11'
        rw [show cfg11.tapeAt (4 * p + -1) = F4.zero from by simpa [hr11, hp11t] using hrd11t] at ht11'
        simpa [subsetSumCBTM] using ht11'
      have hres11t : step11.result = CBTMTransResult.mk (encodeState 101 0 0) F4.zero Dir.S :=
        trap_step11_forced step11.result hmem11t
      have hhead_trap : cfgc'.headPos = 4 * p + -1 := by
        rw [hc11]
        dsimp [stepConfig]
        rw [hres11t]
        dsimp
        rw [hp11t]
        simp [Dir.toInt]
      rw [hhead_trap] at hhead'
      simp [hd, Dir.toInt] at hhead'
      first | done | omega
    have hres9 : step9.result = CBTMTransResult.mk (encodeState qn 10 regr) s9 Dir.L := by
      have hres9' : step9.result = CBTMTransResult.mk (encodeState qn 10 regr) s9 Dir.L ∨
          step9.result = CBTMTransResult.mk (encodeState 101 10 0) F4.zero Dir.S := by
        dsimp [transition4] at hmem9
        rw [hdecph 9 (by norm_num)] at hmem9
        rw [decodeResult_encodeResult_ok r hmk] at hmem9
        rw [hqnn] at hmem9
        by_cases him9 : F4.im s9 <;> simp [him9, hqne] at hmem9
        · simpa [hd] using hmem9
        · left
          simpa [hd] using hmem9
      rcases hres9' with hg | htrap
      · exact hg
      · exfalso
        exact hnotrap9 htrap
    have hp10 : cfg10.headPos = 4 * p + -2 := by
      rw [hc9]
      dsimp [stepConfig]
      rw [hres9]
      dsimp
      rw [hp9]
      dsimp [d]
      simp [hd, Dir.toInt]
      first | done | omega
    have hst10 : step10.fromState = encodeState qn 10 regr := by
      have hst10' : step10.fromState = cfg10.state := by simpa using hf10
      rw [hst10']
      rw [hc9]
      dsimp [stepConfig]
      rw [hres9]
    have hrd10 : step10.readSym = s10 := by
      have hrd10' : step10.readSym = cfg10.tapeAt cfg10.headPos := by simpa using hr10
      rw [hrd10', hp10]
      rw [hc9]
      rw [stepConfig_tapeAt_eq_of_ne cfg9 step9.result (4 * p + -2) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt]; first | done | omega)]
      rw [hc8]
      rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * p + -2) (by rw [hp8]; omega)]
      rw [hc7]
      rw [stepConfig_tapeAt_eq_of_ne cfg7 step7.result (4 * p + -2) (by rw [hp7]; omega)]
      rw [hc6]
      rw [stepConfig_tapeAt_eq_of_ne cfg6 step6.result (4 * p + -2) (by rw [hp6]; omega)]
      rw [hc5]
      rw [stepConfig_tapeAt_eq_of_ne cfg5 step5.result (4 * p + -2) (by rw [hp5]; omega)]
      rw [hc4]
      rw [stepConfig_tapeAt_eq_of_ne cfg4 step4.result (4 * p + -2) (by rw [hp4]; omega)]
      rw [hc3]
      rw [stepConfig_tapeAt_eq_of_ne cfg3 step3.result (4 * p + -2) (by rw [hp3]; omega)]
      rw [hc2]
      rw [stepConfig_tapeAt_eq_of_ne cfg2 step2.result (4 * p + -2) (by rw [hp2]; omega)]
      rw [hc1]
      rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * p + -2) (by rw [hp1]; omega)]
      rw [hc0]
      rw [stepConfig_tapeAt_eq_of_ne cfgc step0.result (4 * p + -2) (by rw [hp]; omega)]
      rw [show 4 * p + -2 = 4 * (p - 1) + (2 : ℕ) by omega]
      rw [hcorr.2.2 (p - 1) 2 (by norm_num)]
      dsimp [s10, d, tprev]
      simp [hd]
    have him10s : F4.im s10 = false := by
      dsimp [s10, d, tprev]
      simp [hd]
    have hmem10 : step10.result ∈ transition4 (encodeState qn 10 regr) s10 := by
      have ht10' : step10.result ∈ subsetSumCBTM.transition (cfg10.state, cfg10.tapeAt cfg10.headPos, cfg10.headPos) := ht10
      rw [show cfg10.state = encodeState qn 10 regr from by simpa [hf10] using hst10] at ht10'
      rw [hp10] at ht10'
      rw [show cfg10.tapeAt (4 * p + -2) = s10 from by simpa [hr10, hp10] using hrd10] at ht10'
      simpa [subsetSumCBTM] using ht10'
    have hnotrap10 : step10.result ≠ CBTMTransResult.mk (encodeState 101 11 0) F4.zero Dir.S := by
      intro htr10
      have hp11t : cfg11.headPos = 4 * p + -2 := by
        rw [hc10]
        dsimp [stepConfig]
        rw [htr10]
        dsimp
        rw [hp10]
        simp [Dir.toInt]
        first | done | omega
      have hrd11t : step11.readSym = F4.zero := by
        have hrd11' : step11.readSym = cfg11.tapeAt cfg11.headPos := by simpa using hr11
        rw [hrd11', hp11t]
        rw [hc10]
        rw [stepConfig_tapeAt_eq_of_eq cfg10 step10.result (4 * p + -2) (by rw [hp10])]
        rw [htr10]
      have hmem11t : step11.result ∈ transition4 (encodeState 101 11 0) F4.zero := by
        have ht11' : step11.result ∈ subsetSumCBTM.transition (cfg11.state, cfg11.tapeAt cfg11.headPos, cfg11.headPos) := ht11
        rw [show cfg11.state = encodeState 101 11 0 from by simpa [stepConfig, hc10, htr10]] at ht11'
        rw [hp11t] at ht11'
        rw [show cfg11.tapeAt (4 * p + -2) = F4.zero from by simpa [hr11, hp11t] using hrd11t] at ht11'
        simpa [subsetSumCBTM] using ht11'
      have hres11t : step11.result = CBTMTransResult.mk (encodeState 101 0 0) F4.zero Dir.S :=
        trap_step11_forced step11.result hmem11t
      have hhead_trap : cfgc'.headPos = 4 * p + -2 := by
        rw [hc11]
        dsimp [stepConfig]
        rw [hres11t]
        dsimp
        rw [hp11t]
        simp [Dir.toInt]
        first | done | omega
      rw [hhead_trap] at hhead'
      simp [hd, Dir.toInt] at hhead'
      first | done | omega
    have hres10 : step10.result = CBTMTransResult.mk (encodeState qn 11 regr) s10 Dir.L := by
      have hres10' : step10.result = CBTMTransResult.mk (encodeState qn 11 regr) s10 Dir.L ∨
          step10.result = CBTMTransResult.mk (encodeState 101 11 0) F4.zero Dir.S := by
        dsimp [transition4] at hmem10
        rw [hdecph 10 (by norm_num)] at hmem10
        rw [decodeResult_encodeResult_ok r hmk] at hmem10
        rw [hqnn] at hmem10
        by_cases him10 : F4.im s10 <;> simp [him10, hqne] at hmem10
        · simpa [hd] using hmem10
        · left
          simpa [hd] using hmem10
      rcases hres10' with hg | htrap
      · exact hg
      · exfalso
        exact hnotrap10 htrap
    have hp11 : cfg11.headPos = 4 * p + -3 := by
      rw [hc10]
      dsimp [stepConfig]
      rw [hres10]
      dsimp
      rw [hp10]
      simp [Dir.toInt]
      first | done | omega
    have hst11 : step11.fromState = encodeState qn 11 regr := by
      have hst11' : step11.fromState = cfg11.state := by simpa using hf11
      rw [hst11']
      rw [hc10]
      dsimp [stepConfig]
      rw [hres10]
    have hrd11 : step11.readSym = s11 := by
      have hrd11' : step11.readSym = cfg11.tapeAt cfg11.headPos := by simpa using hr11
      rw [hrd11', hp11]
      rw [hc10]
      rw [stepConfig_tapeAt_eq_of_ne cfg10 step10.result (4 * p + -3) (by rw [hp10]; omega)]
      rw [hc9]
      rw [stepConfig_tapeAt_eq_of_ne cfg9 step9.result (4 * p + -3) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt]; first | done | omega)]
      rw [hc8]
      rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * p + -3) (by rw [hp8]; omega)]
      rw [hc7]
      rw [stepConfig_tapeAt_eq_of_ne cfg7 step7.result (4 * p + -3) (by rw [hp7]; omega)]
      rw [hc6]
      rw [stepConfig_tapeAt_eq_of_ne cfg6 step6.result (4 * p + -3) (by rw [hp6]; omega)]
      rw [hc5]
      rw [stepConfig_tapeAt_eq_of_ne cfg5 step5.result (4 * p + -3) (by rw [hp5]; omega)]
      rw [hc4]
      rw [stepConfig_tapeAt_eq_of_ne cfg4 step4.result (4 * p + -3) (by rw [hp4]; omega)]
      rw [hc3]
      rw [stepConfig_tapeAt_eq_of_ne cfg3 step3.result (4 * p + -3) (by rw [hp3]; omega)]
      rw [hc2]
      rw [stepConfig_tapeAt_eq_of_ne cfg2 step2.result (4 * p + -3) (by rw [hp2]; omega)]
      rw [hc1]
      rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * p + -3) (by rw [hp1]; omega)]
      rw [hc0]
      rw [stepConfig_tapeAt_eq_of_ne cfgc step0.result (4 * p + -3) (by rw [hp]; omega)]
      rw [show 4 * p + -3 = 4 * (p - 1) + (1 : ℕ) by omega]
      rw [hcorr.2.2 (p - 1) 1 (by norm_num)]
      dsimp [s11, d, tprev]
      simp [hd]
    have him11s : F4.im s11 = false := by
      dsimp [s11, d, tprev]
      simp [hd]

    intro i hi himi
    by_cases hlt : i < 9
    · exact hcls08 i hlt himi
    · have hge9 : 9 ≤ i := by omega
      rw [hπ'] at himi
      interval_cases i <;> simp at himi
      · rw [hrd9, him9s] at himi
        cases himi
      · rw [hrd10, him10s] at himi
        cases himi
      · rw [hrd11, him11s] at himi
        cases himi
  · -- d = R:读 w1/w2/w3
    have hc8'1 : cfg8.tapeAt (4 * p + 1) = w1 := by
      rw [hc7]
      rw [stepConfig_tapeAt_eq_of_ne cfg7 step7.result (4 * p + 1) (by rw [hp7]; omega)]
      rw [hc6]
      rw [stepConfig_tapeAt_eq_of_ne cfg6 step6.result (4 * p + 1) (by rw [hp6]; omega)]
      rw [hc5]
      rw [stepConfig_tapeAt_eq_of_eq cfg5 step5.result (4 * p + 1) (by rw [hp5])]
      rw [hres5]
    have hc8'2 : cfg8.tapeAt (4 * p + 2) = w2 := by
      rw [hc7]
      rw [stepConfig_tapeAt_eq_of_ne cfg7 step7.result (4 * p + 2) (by rw [hp7]; omega)]
      rw [hc6]
      rw [stepConfig_tapeAt_eq_of_ne cfg6 step6.result (4 * p + 2) (by rw [hp6]; omega)]
      rw [hc5]
      rw [stepConfig_tapeAt_eq_of_ne cfg5 step5.result (4 * p + 2) (by rw [hp5]; omega)]
      rw [hc4]
      rw [stepConfig_tapeAt_eq_of_eq cfg4 step4.result (4 * p + 2) (by rw [hp4])]
      rw [hres4]
    have hc8'3 : cfg8.tapeAt (4 * p + 3) = w3 := by
      rw [hc7]
      rw [stepConfig_tapeAt_eq_of_ne cfg7 step7.result (4 * p + 3) (by rw [hp7]; omega)]
      rw [hc6]
      rw [stepConfig_tapeAt_eq_of_ne cfg6 step6.result (4 * p + 3) (by rw [hp6]; omega)]
      rw [hc5]
      rw [stepConfig_tapeAt_eq_of_ne cfg5 step5.result (4 * p + 3) (by rw [hp5]; omega)]
      rw [hc4]
      rw [stepConfig_tapeAt_eq_of_ne cfg4 step4.result (4 * p + 3) (by rw [hp4]; omega)]
      rw [hc3]
      rw [stepConfig_tapeAt_eq_of_eq cfg3 step3.result (4 * p + 3) (by rw [hp3])]
      rw [hstep3']
      dsimp [w3, nrs]
      rw [← symTo4F4_getD3_eq_lastD r.writeSym]
    have hst9 : step9.fromState = encodeState qn 9 regr := by
      have hst9' : step9.fromState = cfg9.state := by simpa using hf9
      rw [hst9']
      rw [hc8]
      dsimp [stepConfig]
      rw [hres8]
    have hrd9 : step9.readSym = w1 := by
      have hrd9' : step9.readSym = cfg9.tapeAt cfg9.headPos := by simpa using hr9
      rw [hrd9', hp9]
      dsimp [d]
      simp [hd, Dir.toInt]
      rw [hc8]
      rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * p + 1) (by rw [hp8]; omega)]
      rw [hc8'1]
    have him9s : F4.im s9 = false := by
      dsimp [s9, d]
      simp [hd, hw1]
    have hmem9 : step9.result ∈ transition4 (encodeState qn 9 regr) w1 := by
      have ht9' : step9.result ∈ subsetSumCBTM.transition (cfg9.state, cfg9.tapeAt cfg9.headPos, cfg9.headPos) := ht9
      rw [show cfg9.state = encodeState qn 9 regr from by simpa [hf9] using hst9] at ht9'
      rw [hp9] at ht9'
      dsimp [d] at ht9'
      simp [hd, Dir.toInt] at ht9'
      rw [show cfg9.tapeAt (4 * p + 1) = w1 from by simpa [hr9, hp9, d, hd, Dir.toInt] using hrd9] at ht9'
      simpa [subsetSumCBTM] using ht9'
    have hres9 : step9.result = CBTMTransResult.mk (encodeState qn 10 regr) w1 Dir.R := by
      dsimp [transition4] at hmem9
      rw [hdecph 9 (by norm_num)] at hmem9
      simp [hw1, hqne] at hmem9
      rw [decodeResult_encodeResult_ok r hmk] at hmem9
      rw [hqnn] at hmem9
      simpa [hd] using hmem9
    have hp10 : cfg10.headPos = 4 * p + 2 := by
      rw [hc9]
      dsimp [stepConfig]
      rw [hres9]
      dsimp
      rw [hp9]
      dsimp [d]
      simp [hd, Dir.toInt]
      omega
    have hst10 : step10.fromState = encodeState qn 10 regr := by
      have hst10' : step10.fromState = cfg10.state := by simpa using hf10
      rw [hst10']
      rw [hc9]
      dsimp [stepConfig]
      rw [hres9]
    have hrd10 : step10.readSym = w2 := by
      have hrd10' : step10.readSym = cfg10.tapeAt cfg10.headPos := by simpa using hr10
      rw [hrd10', hp10]
      rw [hc9]
      rw [stepConfig_tapeAt_eq_of_ne cfg9 step9.result (4 * p + 2) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt]; first | done | omega)]
      rw [hc8]
      rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * p + 2) (by rw [hp8]; omega)]
      rw [hc8'2]
    have him10s : F4.im s10 = false := by
      dsimp [s10, d]
      simp [hd, hw2]
    have hmem10 : step10.result ∈ transition4 (encodeState qn 10 regr) w2 := by
      have ht10' : step10.result ∈ subsetSumCBTM.transition (cfg10.state, cfg10.tapeAt cfg10.headPos, cfg10.headPos) := ht10
      rw [show cfg10.state = encodeState qn 10 regr from by simpa [hf10] using hst10] at ht10'
      rw [hp10] at ht10'
      rw [show cfg10.tapeAt (4 * p + 2) = w2 from by simpa [hr10, hp10] using hrd10] at ht10'
      simpa [subsetSumCBTM] using ht10'
    have hres10 : step10.result = CBTMTransResult.mk (encodeState qn 11 regr) w2 Dir.R := by
      dsimp [transition4] at hmem10
      rw [hdecph 10 (by norm_num)] at hmem10
      simp [hw2, hqne] at hmem10
      rw [decodeResult_encodeResult_ok r hmk] at hmem10
      rw [hqnn] at hmem10
      simpa [hd] using hmem10
    have hp11 : cfg11.headPos = 4 * p + 3 := by
      rw [hc10]
      dsimp [stepConfig]
      rw [hres10]
      dsimp
      rw [hp10]
      simp [Dir.toInt]
      omega
    have hst11 : step11.fromState = encodeState qn 11 regr := by
      have hst11' : step11.fromState = cfg11.state := by simpa using hf11
      rw [hst11']
      rw [hc10]
      dsimp [stepConfig]
      rw [hres10]
    have hrd11 : step11.readSym = w3 := by
      have hrd11' : step11.readSym = cfg11.tapeAt cfg11.headPos := by simpa using hr11
      rw [hrd11', hp11]
      rw [hc10]
      rw [stepConfig_tapeAt_eq_of_ne cfg10 step10.result (4 * p + 3) (by rw [hp10]; omega)]
      rw [hc9]
      rw [stepConfig_tapeAt_eq_of_ne cfg9 step9.result (4 * p + 3) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt]; first | done | omega)]
      rw [hc8]
      rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * p + 3) (by rw [hp8]; omega)]
      rw [hc8'3]
    have him11s : F4.im s11 = false := by
      dsimp [s11, d, nrs]
      simp [hd]
      rw [l3a_symTo4F4_getD3_im r.writeSym]
      exact hw_nb
    have himw3 : F4.im w3 = false := by
      dsimp [w3, nrs]
      rw [l3a_symTo4F4_getD3_im r.writeSym]
      exact hw_nb
    intro i hi himi
    by_cases hlt : i < 9
    · exact hcls08 i hlt himi
    · have hge9 : 9 ≤ i := by omega
      rw [hπ'] at himi
      interval_cases i <;> simp at himi
      · rw [hrd9, hw1] at himi
        cases himi
      · rw [hrd10, hw2] at himi
        cases himi
      · rw [hrd11, himw3] at himi
        cases himi
  · -- d = S:读 w0 三次
    have hst9 : step9.fromState = encodeState qn 9 regr := by
      have hst9' : step9.fromState = cfg9.state := by simpa using hf9
      rw [hst9']
      rw [hc8]
      dsimp [stepConfig]
      rw [hres8]
    have hp9s : cfg9.headPos = 4 * p := by
      rw [hc8]
      dsimp [stepConfig]
      rw [hres8]
      dsimp
      rw [hp8]
      simp [hd, Dir.toInt]
    have hrd9 : step9.readSym = w0 := by
      have hrd9' : step9.readSym = cfg9.tapeAt cfg9.headPos := by simpa using hr9
      rw [hrd9', hp9s]
      rw [hc8]
      rw [stepConfig_tapeAt_eq_of_eq cfg8 step8.result (4 * p) (by rw [hp8])]
      rw [hres8]
    have him9s : F4.im s9 = false := by
      dsimp [s9, d]
      simp [hd, hw0]
    have hmem9 : step9.result ∈ transition4 (encodeState qn 9 regr) w0 := by
      have ht9' : step9.result ∈ subsetSumCBTM.transition (cfg9.state, cfg9.tapeAt cfg9.headPos, cfg9.headPos) := ht9
      rw [show cfg9.state = encodeState qn 9 regr from by simpa [hf9] using hst9] at ht9'
      rw [hp9s] at ht9'
      rw [show cfg9.tapeAt (4 * p) = w0 from by simpa [hr9, hp9s] using hrd9] at ht9'
      simpa [subsetSumCBTM] using ht9'
    have hres9 : step9.result = CBTMTransResult.mk (encodeState qn 10 regr) w0 Dir.S := by
      dsimp [transition4] at hmem9
      rw [hdecph 9 (by norm_num)] at hmem9
      simp [hw0, hqne] at hmem9
      rw [decodeResult_encodeResult_ok r hmk] at hmem9
      rw [hqnn] at hmem9
      simpa [hd] using hmem9
    have hp10 : cfg10.headPos = 4 * p := by
      rw [hc9]
      dsimp [stepConfig]
      rw [hres9]
      dsimp
      rw [hp9s]
      simp [Dir.toInt]
    have hst10 : step10.fromState = encodeState qn 10 regr := by
      have hst10' : step10.fromState = cfg10.state := by simpa using hf10
      rw [hst10']
      rw [hc9]
      dsimp [stepConfig]
      rw [hres9]
    have hrd10 : step10.readSym = w0 := by
      have hrd10' : step10.readSym = cfg10.tapeAt cfg10.headPos := by simpa using hr10
      rw [hrd10', hp10]
      rw [hc9]
      rw [stepConfig_tapeAt_eq_of_eq cfg9 step9.result (4 * p) (by rw [hp9s])]
      rw [hres9]
    have him10s : F4.im s10 = false := by
      dsimp [s10, d]
      simp [hd, hw0]
    have hmem10 : step10.result ∈ transition4 (encodeState qn 10 regr) w0 := by
      have ht10' : step10.result ∈ subsetSumCBTM.transition (cfg10.state, cfg10.tapeAt cfg10.headPos, cfg10.headPos) := ht10
      rw [show cfg10.state = encodeState qn 10 regr from by simpa [hf10] using hst10] at ht10'
      rw [hp10] at ht10'
      rw [show cfg10.tapeAt (4 * p) = w0 from by simpa [hr10, hp10] using hrd10] at ht10'
      simpa [subsetSumCBTM] using ht10'
    have hres10 : step10.result = CBTMTransResult.mk (encodeState qn 11 regr) w0 Dir.S := by
      dsimp [transition4] at hmem10
      rw [hdecph 10 (by norm_num)] at hmem10
      simp [hw0, hqne] at hmem10
      rw [decodeResult_encodeResult_ok r hmk] at hmem10
      rw [hqnn] at hmem10
      simpa [hd] using hmem10
    have hp11 : cfg11.headPos = 4 * p := by
      rw [hc10]
      dsimp [stepConfig]
      rw [hres10]
      dsimp
      rw [hp10]
      simp [Dir.toInt]
    have hst11 : step11.fromState = encodeState qn 11 regr := by
      have hst11' : step11.fromState = cfg11.state := by simpa using hf11
      rw [hst11']
      rw [hc10]
      dsimp [stepConfig]
      rw [hres10]
    have hrd11 : step11.readSym = w0 := by
      have hrd11' : step11.readSym = cfg11.tapeAt cfg11.headPos := by simpa using hr11
      rw [hrd11', hp11]
      rw [hc10]
      rw [stepConfig_tapeAt_eq_of_eq cfg10 step10.result (4 * p) (by rw [hp10])]
      rw [hres10]
    have him11s : F4.im s11 = false := by
      dsimp [s11, d]
      simp [hd, hw0]
    intro i hi himi
    by_cases hlt : i < 9
    · exact hcls08 i hlt himi
    · have hge9 : 9 ≤ i := by omega
      rw [hπ'] at himi
      interval_cases i <;> simp at himi
      · rw [hrd9, hw0] at himi
        cases himi
      · rw [hrd10, hw0] at himi
        cases himi
      · rw [hrd11, hw0] at himi
        cases himi

/-- T8a 轮 C(件 1):单块 im-true 读计数 = 分支 ?1:0。
    (拆解照抄 l3a_goodblock_read_im_classify;结尾 filter 逐项化简。) -/
lemma l3a_goodblock_branchCount_eq {w : List F4} {cfgc : CBTMConfig subsetSumCBTM w}
    {π : ComputationPath} {cfgc' : CBTMConfig subsetSumCBTM w} {cfgs : SymConfig}
    {p : ℤ} {q : ℕ} {sym : Sym} {r : SymTransResult}
    (hblock : GoodBlock w cfgc π cfgc' cfgs p q sym r)
    (hrs : r.nextState < 101)
    (hprev_nb : r.moveDir = Dir.L → Sym.isBranch (cfgs.tape (p - 1)) = false)
    (hw_nb : Sym.isBranch r.writeSym = false) :
    (π.filter (fun step => F4.im step.readSym)).length =
      if Sym.isBranch sym then 1 else 0 := by
  rcases hblock with ⟨hpath, hlen, hst, hp, hcorr, hread, hq, hbranchq, hvalid_sym, hstep4, hmk, hr, hst', hhead'⟩
  let cells := symTo4F4 sym
  let c0 := cells.getD 0 F4.zero
  let c1 := cells.getD 1 F4.zero
  let c2 := cells.getD 2 F4.zero
  let c3 := cells.getD 3 F4.zero
  let nrs := symTo4F4 r.writeSym
  let w0 := nrs.getD 0 F4.zero
  let w1 := nrs.getD 1 F4.zero
  let w2 := nrs.getD 2 F4.zero
  let w3 := nrs.getD 3 F4.zero
  let d := r.moveDir
  let qn := min r.nextState 101
  let b01 := bufOf3 c0 F4.zero F4.zero
  let b12 := bufOf3 c0 c1 F4.zero
  let b3 := bufOf3 c0 c1 c2
  let regr := encodeResult r
  let tprev := symTo4F4 (cfgs.tape (p - 1))
  let s8 := w0
  let s9 := match d with | Dir.R => w1 | Dir.L => tprev.getD 3 F4.zero | Dir.S => w0
  let s10 := match d with | Dir.R => w2 | Dir.L => tprev.getD 2 F4.zero | Dir.S => w0
  let s11 := match d with | Dir.R => w3 | Dir.L => tprev.getD 1 F4.zero | Dir.S => w0
  -- 1. 拆出 12 步
  rcases tapeSteps_split_last hpath (by intro h; simp [h] at hlen) with
    ⟨step11, π10, cfg11, hπe11, h10, hf11, hr11, ht11, hc11⟩
  rcases tapeSteps_split_last h10 (by
      intro h
      have : (π10 ++ [step11]).length = 12 := by simpa [hπe11] using hlen
      simp [h] at this) with
    ⟨step10, π9, cfg10, hπe10, h9, hf10, hr10, ht10, hc10⟩
  rcases tapeSteps_split_last h9 (by
      intro h
      have : (π9 ++ [step10, step11]).length = 12 := by simpa [hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step9, π8, cfg9, hπe9, h8, hf9, hr9, ht9, hc9⟩
  rcases tapeSteps_split_last h8 (by
      intro h
      have : (π8 ++ [step9, step10, step11]).length = 12 := by simpa [hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step8, π7, cfg8, hπe8, h7, hf8, hr8, ht8, hc8⟩
  rcases tapeSteps_split_last h7 (by
      intro h
      have : (π7 ++ [step8, step9, step10, step11]).length = 12 := by simpa [hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step7, π6, cfg7, hπe7, h6, hf7, hr7, ht7, hc7⟩
  rcases tapeSteps_split_last h6 (by
      intro h
      have : (π6 ++ [step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step6, π5, cfg6, hπe6, h5, hf6, hr6, ht6, hc6⟩
  rcases tapeSteps_split_last h5 (by
      intro h
      have : (π5 ++ [step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step5, π4, cfg5, hπe5, h4, hf5, hr5, ht5, hc5⟩
  rcases tapeSteps_split_last h4 (by
      intro h
      have : (π4 ++ [step5, step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step4, π3, cfg4, hπe4, h3, hf4, hr4, ht4, hc4⟩
  rcases tapeSteps_split_last h3 (by
      intro h
      have : (π3 ++ [step4, step5, step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step3, π2, cfg3, hπe3, h2, hf3, hr3, ht3, hc3⟩
  rcases tapeSteps_split_last h2 (by
      intro h
      have : (π2 ++ [step3, step4, step5, step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe3, hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step2, π1, cfg2, hπe2, h1, hf2, hr2, ht2, hc2⟩
  rcases tapeSteps_split_last h1 (by
      intro h
      have : (π1 ++ [step2, step3, step4, step5, step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe2, hπe3, hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step1, π0, cfg1, hπe1, h0, hf1, hr1, ht1, hc1⟩
  rcases tapeSteps_split_last h0 (by
      intro h
      have : (π0 ++ [step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe1, hπe2, hπe3, hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step0, πn, cfgc0, hπen, hn, hf0, hr0, ht0, hc0⟩
  have hπn : πn = [] := by
    have hsum : (πn ++ [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11]).length = 12 := by
      simpa [hπen, hπe1, hπe2, hπe3, hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
    have hsum' : πn.length + 12 = 12 := by simpa using hsum
    have hlen0 : πn.length = 0 := by omega
    cases πn with
    | nil => rfl
    | cons x xs => simp at hlen0
  have hcfg0 : cfgc0 = cfgc := by
    exact tapeSteps_empty hn hπn
  subst πn
  subst cfgc0
  -- 3. 前 4 格取值与 im 事实
  have hc0v : cfgc.tapeAt (4 * p) = c0 := by
    have hc := hcorr.2.2 p 0 (by norm_num)
    simpa [hread, c0, cells] using hc
  have hc1v : cfgc.tapeAt (4 * p + 1) = c1 := by
    have hc := hcorr.2.2 p 1 (by norm_num)
    simpa [hread, c1, cells] using hc
  have hc2v : cfgc.tapeAt (4 * p + 2) = c2 := by
    have hc := hcorr.2.2 p 2 (by norm_num)
    simpa [hread, c2, cells] using hc
  have hc3v : cfgc.tapeAt (4 * p + 3) = c3 := by
    have hc := hcorr.2.2 p 3 (by norm_num)
    simpa [hread, c3, cells] using hc
  have him0 : F4.im c0 = false := by simpa [c0, cells] using (symTo4F4_im_false_012 sym).1
  have him1 : F4.im c1 = false := by simpa [c1, cells] using (symTo4F4_im_false_012 sym).2.1
  have him2 : F4.im c2 = false := by simpa [c2, cells] using (symTo4F4_im_false_012 sym).2.2
  have him_c3 : F4.im c3 = Sym.isBranch sym := by
    dsimp [c3, cells]
    exact l3a_symTo4F4_getD3_im sym
  have hw0 : F4.im w0 = false := by simpa [w0, nrs] using (symTo4F4_im_false_012 r.writeSym).1
  have hw1 : F4.im w1 = false := by simpa [w1, nrs] using (symTo4F4_im_false_012 r.writeSym).2.1
  have hw2 : F4.im w2 = false := by simpa [w2, nrs] using (symTo4F4_im_false_012 r.writeSym).2.2
  -- 4. 解码辅助
  have hb01 : b01 = bufOf3s 0 c0 0 := by
    dsimp [b01, bufOf3, bufOf3s]
    rcases c0 with ⟨r0, i0⟩
    cases r0 <;> cases i0 <;> simp [F4.zero, F4.one, F4.alpha, F4.beta]
  have hb12 : b12 = b01 + bufOf3s 1 c1 b01 := by
    dsimp [b12, b01, bufOf3, bufOf3s]
    rcases c0 with ⟨r0, i0⟩ <;> rcases c1 with ⟨r1, i1⟩
    cases r0 <;> cases i0 <;> cases r1 <;> cases i1 <;> simp [F4.zero, F4.one, F4.alpha, F4.beta]
  have hb3 : b3 = b12 + bufOf3s 2 c2 b12 := by
    dsimp [b3, b12, b01, bufOf3, bufOf3s]
    rcases c0 with ⟨r0, i0⟩ <;> rcases c1 with ⟨r1, i1⟩ <;> rcases c2 with ⟨r2, i2⟩
    cases r0 <;> cases i0 <;> cases r1 <;> cases i1 <;> cases r2 <;> cases i2 <;>
      simp [F4.zero, F4.one, F4.alpha, F4.beta]
  have hdec1' : decodeState (encodeState (min q 101) 1 b01) = (min q 101, 1, b01) := by
    apply decodeState_encodeState
    · norm_num
    · have hb : b01 ≤ 63 := by
        dsimp [b01, bufOf3]
        rcases c0 with ⟨r0, i0⟩
        cases r0 <;> cases i0 <;> simp [F4.zero, F4.one, F4.alpha, F4.beta]
      exact lt_of_le_of_lt hb (by norm_num)
  have hdec2' : decodeState (encodeState (min q 101) 2 b12) = (min q 101, 2, b12) := by
    apply decodeState_encodeState
    · norm_num
    · have hb : b12 ≤ 63 := by
        dsimp [b12, bufOf3]
        rcases c0 with ⟨r0, i0⟩ <;> rcases c1 with ⟨r1, i1⟩
        cases r0 <;> cases i0 <;> cases r1 <;> cases i1 <;> simp [F4.zero, F4.one, F4.alpha, F4.beta]
      exact lt_of_le_of_lt hb (by norm_num)
  have hdec3' : decodeState (encodeState (min q 101) 3 b3) = (min q 101, 3, b3) := by
    apply decodeState_encodeState
    · norm_num
    · have hb : b3 ≤ 63 := by
        dsimp [b3, bufOf3]
        rcases c0 with ⟨r0, i0⟩ <;> rcases c1 with ⟨r1, i1⟩ <;> rcases c2 with ⟨r2, i2⟩
        cases r0 <;> cases i0 <;> cases r1 <;> cases i1 <;> cases r2 <;> cases i2 <;>
          simp [F4.zero, F4.one, F4.alpha, F4.beta]
      exact lt_of_le_of_lt hb (by norm_num)
  have hqle : q ≤ 101 := hq
  have hns : r.nextState ≤ 101 := transition_nextState_le101 q sym hqle r hr
  have hqnn : min qn 101 = qn := by
    dsimp [qn]
    rw [Nat.min_eq_left]
    exact Nat.min_le_right _ _
  have hqne : qn ≠ 101 := by
    dsimp [qn]
    rw [Nat.min_eq_left (le_of_lt hrs)]
    exact ne_of_lt hrs
  have hregr : regr < 8192 := by
    dsimp [regr, encodeResult]
    have hsk : skOf r.writeSym.1 + (if r.writeSym.2 then 9 else 0) < 18 := by
      rcases r.writeSym with ⟨k, mk⟩
      cases k <;> cases mk <;> simp [skOf]
    have hdir : dirOf r.moveDir < 3 := by
      cases r.moveDir <;> simp [dirOf]
    omega
  have hdecph (ph : ℕ) (hphl : ph < 12) :
      decodeState (encodeState qn ph regr) = (qn, ph, regr) := by
    apply decodeState_encodeState
    · simpa [stepsPerSym] using hphl
    · simpa [regBound] using hregr
  -- 5. 第 0 步:读 c0(im=false)→ 唯一结果 R
  have hst0 : step0.fromState = encodeState q 0 0 := by simpa [hst] using hf0
  have hrd0 : step0.readSym = c0 := by
    simpa [hc0v, hp, c0] using hr0
  have hmem0 : step0.result ∈ transition4 (encodeState q 0 0) c0 := by
    have ht0' : step0.result ∈ subsetSumCBTM.transition (cfgc.state, cfgc.tapeAt cfgc.headPos, cfgc.headPos) := ht0
    rw [hst, hp, hc0v] at ht0'
    simpa [subsetSumCBTM] using ht0'
  have hres0 : step0.result = CBTMTransResult.mk (encodeState (min q 101) 1 b01) c0 Dir.R := by
    dsimp [transition4] at hmem0
    rw [decodeState_encodeState q 0 0 (by norm_num) (by norm_num)] at hmem0
    simp [him0] at hmem0
    simpa [hb01] using hmem0
  have hp1 : cfg1.headPos = 4 * p + 1 := by
    rw [hc0]
    dsimp [stepConfig]
    rw [hres0]
    dsimp
    rw [hp]
    simp [Dir.toInt]
  -- 6. 第 1 步:读 c1
  have hst1 : step1.fromState = encodeState (min q 101) 1 b01 := by
    have hst1' : step1.fromState = cfg1.state := by simpa using hf1
    rw [hst1']
    rw [hc0]
    dsimp [stepConfig]
    rw [hres0]
  have hrd1 : step1.readSym = c1 := by
    have hrd1' : step1.readSym = cfg1.tapeAt cfg1.headPos := by simpa using hr1
    rw [hrd1', hp1]
    rw [hc0]
    rw [stepConfig_tapeAt_eq_of_ne cfgc step0.result (4 * p + 1) (by rw [hp]; omega)]
    rw [hc1v]
  have hmem1 : step1.result ∈ transition4 (encodeState (min q 101) 1 b01) c1 := by
    have ht1' : step1.result ∈ subsetSumCBTM.transition (cfg1.state, cfg1.tapeAt cfg1.headPos, cfg1.headPos) := ht1
    rw [show cfg1.state = encodeState (min q 101) 1 b01 from by simpa [hf1] using hst1] at ht1'
    rw [hp1] at ht1'
    rw [show cfg1.tapeAt (4 * p + 1) = c1 from by simpa [hr1, hp1] using hrd1] at ht1'
    simpa [subsetSumCBTM] using ht1'
  have hres1 : step1.result = CBTMTransResult.mk (encodeState (min q 101) 2 (b01 + bufOf3s 1 c1 b01)) c1 Dir.R := by
    dsimp [transition4] at hmem1
    rw [hdec1'] at hmem1
    simp [him1] at hmem1
    simpa using hmem1
  have hp2 : cfg2.headPos = 4 * p + 2 := by
    rw [hc1]
    dsimp [stepConfig]
    rw [hres1]
    dsimp
    rw [hp1]
    simp [Dir.toInt]
    omega
  -- 7. 第 2 步:读 c2
  have hst2 : step2.fromState = encodeState (min q 101) 2 b12 := by
    have hst2' : step2.fromState = cfg2.state := by simpa using hf2
    rw [hst2']
    rw [hc1]
    dsimp [stepConfig]
    rw [hres1]
    dsimp
    rw [← hb12]
  have hrd2 : step2.readSym = c2 := by
    have hrd2' : step2.readSym = cfg2.tapeAt cfg2.headPos := by simpa using hr2
    rw [hrd2', hp2]
    rw [hc1]
    rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * p + 2) (by rw [hp1]; omega)]
    rw [hc0]
    rw [stepConfig_tapeAt_eq_of_ne cfgc step0.result (4 * p + 2) (by rw [hp]; omega)]
    rw [hc2v]
  have hmem2 : step2.result ∈ transition4 (encodeState (min q 101) 2 b12) c2 := by
    have ht2' : step2.result ∈ subsetSumCBTM.transition (cfg2.state, cfg2.tapeAt cfg2.headPos, cfg2.headPos) := ht2
    rw [show cfg2.state = encodeState (min q 101) 2 b12 from by simpa [hf2] using hst2] at ht2'
    rw [hp2] at ht2'
    rw [show cfg2.tapeAt (4 * p + 2) = c2 from by simpa [hr2, hp2] using hrd2] at ht2'
    simpa [subsetSumCBTM] using ht2'
  have hres2 : step2.result = CBTMTransResult.mk (encodeState (min q 101) 3 (b12 + bufOf3s 2 c2 b12)) c2 Dir.R := by
    dsimp [transition4] at hmem2
    rw [hdec2'] at hmem2
    simp [him2] at hmem2
    simpa using hmem2
  have hp3 : cfg3.headPos = 4 * p + 3 := by
    rw [hc2]
    dsimp [stepConfig]
    rw [hres2]
    dsimp
    rw [hp2]
    simp [Dir.toInt]
    omega
  -- 8. 第 3 步(合成步):hstep4 直接钉死
  have hst3 : step3.fromState = encodeState (min q 101) 3 b3 := by
    have hst3' : step3.fromState = cfg3.state := by simpa using hf3
    rw [hst3']
    rw [hc2]
    dsimp [stepConfig]
    rw [hres2]
    dsimp
    rw [← hb3]
  have hrd3 : step3.readSym = c3 := by
    have hrd3' : step3.readSym = cfg3.tapeAt cfg3.headPos := by simpa using hr3
    rw [hrd3', hp3]
    rw [hc2]
    rw [stepConfig_tapeAt_eq_of_ne cfg2 step2.result (4 * p + 3) (by rw [hp2]; omega)]
    rw [hc1]
    rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * p + 3) (by rw [hp1]; omega)]
    rw [hc0]
    rw [stepConfig_tapeAt_eq_of_ne cfgc step0.result (4 * p + 3) (by rw [hp]; omega)]
    rw [hc3v]
  have hstep3' : step3.result = CBTMTransResult.mk (encodeState r.nextState 4 regr) ((symTo4F4 r.writeSym).getLastD F4.zero) Dir.L := by
    have hπ' : π = [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11] := by
      rw [hπe11, hπe10, hπe9, hπe8, hπe7, hπe6, hπe5, hπe4, hπe3, hπe2, hπe1, hπen]
      rfl
    have hg : π.get ⟨3, by omega⟩ = step3 := by
      simpa [hπ']
    rw [hg] at hstep4
    simpa [regr] using hstep4
  have hp4 : cfg4.headPos = 4 * p + 2 := by
    rw [hc3]
    dsimp [stepConfig]
    rw [hstep3']
    dsimp
    rw [hp3]
    simp [Dir.toInt]
    omega
  -- 9. 第 4 步:读 c2 写 w2 移 L
  have hst4 : step4.fromState = encodeState r.nextState 4 regr := by
    have hst4' : step4.fromState = cfg4.state := by simpa using hf4
    rw [hst4']
    rw [hc3]
    dsimp [stepConfig]
    rw [hstep3']
  have hrd4 : step4.readSym = c2 := by
    have hrd4' : step4.readSym = cfg4.tapeAt cfg4.headPos := by simpa using hr4
    rw [hrd4', hp4]
    rw [hc3]
    rw [stepConfig_tapeAt_eq_of_ne cfg3 step3.result (4 * p + 2) (by rw [hp3]; omega)]
    rw [hc2]
    rw [stepConfig_tapeAt_eq_of_eq cfg2 step2.result (4 * p + 2) (by rw [hp2])]
    rw [hres2]
  have hres4 : step4.result = CBTMTransResult.mk (encodeState qn 5 regr) w2 Dir.L := by
    have hmem4 : step4.result ∈ transition4 (encodeState r.nextState 4 regr) c2 := by
      have ht4' : step4.result ∈ subsetSumCBTM.transition (cfg4.state, cfg4.tapeAt cfg4.headPos, cfg4.headPos) := ht4
      rw [show cfg4.state = encodeState r.nextState 4 regr from by simpa [hf4] using hst4] at ht4'
      rw [hp4] at ht4'
      rw [show cfg4.tapeAt (4 * p + 2) = c2 from by simpa [hr4, hp4] using hrd4] at ht4'
      simpa [subsetSumCBTM] using ht4'
    have hdec4' : decodeState (encodeState r.nextState 4 regr) = (r.nextState, 4, regr) := by
      apply decodeState_encodeState
      · norm_num
      · simpa [regBound] using hregr
    dsimp [transition4] at hmem4
    rw [hdec4'] at hmem4
    simp [him2] at hmem4
    rw [decodeResult_encodeResult_ok r hmk] at hmem4
    dsimp [qn]
    simpa [w2, nrs] using hmem4
  have hp5 : cfg5.headPos = 4 * p + 1 := by
    rw [hc4]
    dsimp [stepConfig]
    rw [hres4]
    dsimp
    rw [hp4]
    simp [Dir.toInt]
    omega
  -- 10. 第 5 步:读 c1 写 w1 移 L
  have hrd5 : step5.readSym = c1 := by
    have hrd5' : step5.readSym = cfg5.tapeAt cfg5.headPos := by simpa using hr5
    rw [hrd5', hp5]
    rw [hc4]
    rw [stepConfig_tapeAt_eq_of_ne cfg4 step4.result (4 * p + 1) (by rw [hp4]; omega)]
    rw [hc3]
    rw [stepConfig_tapeAt_eq_of_ne cfg3 step3.result (4 * p + 1) (by rw [hp3]; omega)]
    rw [hc2]
    rw [stepConfig_tapeAt_eq_of_ne cfg2 step2.result (4 * p + 1) (by rw [hp2]; omega)]
    rw [hc1]
    rw [stepConfig_tapeAt_eq_of_eq cfg1 step1.result (4 * p + 1) (by rw [hp1])]
    rw [hres1]
  have hres5 : step5.result = CBTMTransResult.mk (encodeState qn 6 regr) ((symTo4F4 r.writeSym).getD 1 F4.zero) Dir.L := by
    have hmem5 : step5.result ∈ transition4 (encodeState qn 5 regr) c1 := by
      have ht5' : step5.result ∈ subsetSumCBTM.transition (cfg5.state, cfg5.tapeAt cfg5.headPos, cfg5.headPos) := ht5
      rw [show cfg5.state = encodeState qn 5 regr from by simpa [hf5, stepConfig, hc4, hres4]] at ht5'
      rw [hp5] at ht5'
      rw [show cfg5.tapeAt (4 * p + 1) = c1 from by simpa [hr5, hp5] using hrd5] at ht5'
      change step5.result ∈ transition4 (encodeState qn 5 regr) c1 at ht5'
      exact ht5'
    dsimp [transition4] at hmem5
    rw [hdecph 5 (by norm_num)] at hmem5
    simp [him1] at hmem5
    rw [decodeResult_encodeResult_ok r hmk] at hmem5
    rw [hqnn] at hmem5
    exact hmem5
  have hp6 : cfg6.headPos = 4 * p := by
    rw [hc5]
    dsimp [stepConfig]
    rw [hres5]
    dsimp
    rw [hp5]
    simp [Dir.toInt]
  -- 11. 第 6 步:读 c0 写 w0 移 S
  have hrd6 : step6.readSym = c0 := by
    have hrd6' : step6.readSym = cfg6.tapeAt cfg6.headPos := by simpa using hr6
    rw [hrd6', hp6]
    rw [hc5]
    rw [stepConfig_tapeAt_eq_of_ne cfg5 step5.result (4 * p) (by rw [hp5]; omega)]
    rw [hc4]
    rw [stepConfig_tapeAt_eq_of_ne cfg4 step4.result (4 * p) (by rw [hp4]; omega)]
    rw [hc3]
    rw [stepConfig_tapeAt_eq_of_ne cfg3 step3.result (4 * p) (by rw [hp3]; omega)]
    rw [hc2]
    rw [stepConfig_tapeAt_eq_of_ne cfg2 step2.result (4 * p) (by rw [hp2]; omega)]
    rw [hc1]
    rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * p) (by rw [hp1]; omega)]
    rw [hc0]
    rw [stepConfig_tapeAt_eq_of_eq cfgc step0.result (4 * p) (by rw [hp])]
    rw [hres0]
  have hres6 : step6.result = CBTMTransResult.mk (encodeState qn 7 regr) ((symTo4F4 r.writeSym).getD 0 F4.zero) Dir.S := by
    have hmem6 : step6.result ∈ transition4 (encodeState qn 6 regr) c0 := by
      have ht6' : step6.result ∈ subsetSumCBTM.transition (cfg6.state, cfg6.tapeAt cfg6.headPos, cfg6.headPos) := ht6
      rw [show cfg6.state = encodeState qn 6 regr from by simpa [hf6, stepConfig, hc5, hres5]] at ht6'
      rw [hp6] at ht6'
      rw [show cfg6.tapeAt (4 * p) = c0 from by simpa [hr6, hp6] using hrd6] at ht6'
      change step6.result ∈ transition4 (encodeState qn 6 regr) c0 at ht6'
      exact ht6'
    dsimp [transition4] at hmem6
    rw [hdecph 6 (by norm_num)] at hmem6
    simp [him0] at hmem6
    rw [decodeResult_encodeResult_ok r hmk] at hmem6
    rw [hqnn] at hmem6
    exact hmem6
  have hp7 : cfg7.headPos = 4 * p := by
    rw [hc6]
    dsimp [stepConfig]
    rw [hres6]
    dsimp
    rw [hp6]
    simp [Dir.toInt]
  -- 12. 第 7 步:读 w0 写原符号移 S
  have hrd7 : step7.readSym = w0 := by
    have hrd7' : step7.readSym = cfg7.tapeAt cfg7.headPos := by simpa using hr7
    rw [hrd7', hp7]
    rw [hc6]
    rw [stepConfig_tapeAt_eq_of_eq cfg6 step6.result (4 * p) (by rw [hp6])]
    rw [hres6]
  have hres7 : step7.result = CBTMTransResult.mk (encodeState qn 8 regr) w0 Dir.S := by
    have hmem7 : step7.result ∈ transition4 (encodeState qn 7 regr) w0 := by
      have ht7' : step7.result ∈ subsetSumCBTM.transition (cfg7.state, cfg7.tapeAt cfg7.headPos, cfg7.headPos) := ht7
      rw [show cfg7.state = encodeState qn 7 regr from by simpa [hf7, stepConfig, hc6, hres6]] at ht7'
      rw [hp7] at ht7'
      rw [show cfg7.tapeAt (4 * p) = w0 from by simpa [hr7, hp7] using hrd7] at ht7'
      change step7.result ∈ transition4 (encodeState qn 7 regr) w0 at ht7'
      exact ht7'
    dsimp [transition4] at hmem7
    rw [hdecph 7 (by norm_num)] at hmem7
    simp [hw0] at hmem7
    rw [hqnn] at hmem7
    rw [hmem7]
  have hp8 : cfg8.headPos = 4 * p := by
    rw [hc7]
    dsimp [stepConfig]
    rw [hres7]
    dsimp
    rw [hp7]
    simp [Dir.toInt]
  -- 13. 第 8 步:读 s8 = w0(im=false)
  have hrd8 : step8.readSym = s8 := by
    have hrd8' : step8.readSym = cfg8.tapeAt cfg8.headPos := by simpa using hr8
    rw [hrd8', hp8]
    rw [hc7]
    rw [stepConfig_tapeAt_eq_of_eq cfg7 step7.result (4 * p) (by rw [hp7])]
    rw [hres7]
  have him8s : F4.im s8 = false := by
    dsimp [s8]
    exact hw0
  have hres8 : step8.result = CBTMTransResult.mk (encodeState qn 9 regr) w0 (SymToF4.dirOf.match_1 (fun _ : Dir => Dir) r.moveDir (fun _ => Dir.R) (fun _ => Dir.L) (fun _ => Dir.S)) := by
    have hmem8 : step8.result ∈ transition4 (encodeState qn 8 regr) s8 := by
      have ht8' : step8.result ∈ subsetSumCBTM.transition (cfg8.state, cfg8.tapeAt cfg8.headPos, cfg8.headPos) := ht8
      rw [show cfg8.state = encodeState qn 8 regr from by simpa [hf8, stepConfig, hc7, hres7]] at ht8'
      rw [hp8] at ht8'
      rw [show cfg8.tapeAt (4 * p) = s8 from by simpa [hr8, hp8] using hrd8] at ht8'
      change step8.result ∈ transition4 (encodeState qn 8 regr) s8 at ht8'
      exact ht8'
    dsimp [transition4] at hmem8
    rw [hdecph 8 (by norm_num)] at hmem8
    simp [hw0, s8, hqne] at hmem8
    rw [decodeResult_encodeResult_ok r hmk] at hmem8
    rw [hqnn] at hmem8
    rw [hmem8]
  have hp9 : cfg9.headPos = 4 * p + d.toInt := by
    rw [hc8]
    dsimp [stepConfig]
    rw [hres8]
    dsimp
    rw [hp8]
    dsimp [d]
    rcases hd : r.moveDir with _ | _ | _ <;> simp [hd, Dir.toInt]
  -- 每步谓词值
  have hprd0 : (F4.im step0.readSym) = false := by rw [hrd0]; exact him0
  have hprd1 : (F4.im step1.readSym) = false := by rw [hrd1]; exact him1
  have hprd2 : (F4.im step2.readSym) = false := by rw [hrd2]; exact him2
  have hprd3 : (F4.im step3.readSym) = Sym.isBranch sym := by rw [hrd3]; exact him_c3
  have hprd4 : (F4.im step4.readSym) = false := by rw [hrd4]; exact him2
  have hprd5 : (F4.im step5.readSym) = false := by rw [hrd5]; exact him1
  have hprd6 : (F4.im step6.readSym) = false := by rw [hrd6]; exact him0
  have hprd7 : (F4.im step7.readSym) = false := by rw [hrd7]; exact hw0
  have hprd8 : (F4.im step8.readSym) = false := by rw [hrd8]; exact him8s
  have hπ' : π = [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11] := by
    rw [hπe11, hπe10, hπe9, hπe8, hπe7, hπe6, hπe5, hπe4, hπe3, hπe2, hπe1, hπen]
    rfl
  rcases hd : r.moveDir with _ | _ | _
  · -- d = L:读 tprev 第 4/3/2 格
    have hst9 : step9.fromState = encodeState qn 9 regr := by
      have hst9' : step9.fromState = cfg9.state := by simpa using hf9
      rw [hst9']
      rw [hc8]
      dsimp [stepConfig]
      rw [hres8]
    have hrd9 : step9.readSym = s9 := by
      have hrd9' : step9.readSym = cfg9.tapeAt cfg9.headPos := by simpa using hr9
      rw [hrd9', hp9]
      dsimp [d]
      simp [hd, Dir.toInt]
      rw [hc8]
      rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * p + -1) (by rw [hp8]; omega)]
      rw [hc7]
      rw [stepConfig_tapeAt_eq_of_ne cfg7 step7.result (4 * p + -1) (by rw [hp7]; omega)]
      rw [hc6]
      rw [stepConfig_tapeAt_eq_of_ne cfg6 step6.result (4 * p + -1) (by rw [hp6]; omega)]
      rw [hc5]
      rw [stepConfig_tapeAt_eq_of_ne cfg5 step5.result (4 * p + -1) (by rw [hp5]; omega)]
      rw [hc4]
      rw [stepConfig_tapeAt_eq_of_ne cfg4 step4.result (4 * p + -1) (by rw [hp4]; omega)]
      rw [hc3]
      rw [stepConfig_tapeAt_eq_of_ne cfg3 step3.result (4 * p + -1) (by rw [hp3]; omega)]
      rw [hc2]
      rw [stepConfig_tapeAt_eq_of_ne cfg2 step2.result (4 * p + -1) (by rw [hp2]; omega)]
      rw [hc1]
      rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * p + -1) (by rw [hp1]; omega)]
      rw [hc0]
      rw [stepConfig_tapeAt_eq_of_ne cfgc step0.result (4 * p + -1) (by rw [hp]; omega)]
      rw [show 4 * p + -1 = 4 * (p - 1) + (3 : ℕ) by omega]
      rw [hcorr.2.2 (p - 1) 3 (by norm_num)]
      dsimp [s9, d, tprev]
      simp [hd]
    have him9s : F4.im s9 = false := by
      dsimp [s9, d, tprev]
      simp [hd]
      simpa using (l3a_symTo4F4_getD3_im (cfgs.tape (p - 1))) ▸ (hprev_nb hd)
    have hmem9 : step9.result ∈ transition4 (encodeState qn 9 regr) s9 := by
      have ht9' : step9.result ∈ subsetSumCBTM.transition (cfg9.state, cfg9.tapeAt cfg9.headPos, cfg9.headPos) := ht9
      rw [show cfg9.state = encodeState qn 9 regr from by simpa [hf9] using hst9] at ht9'
      rw [hp9] at ht9'
      dsimp [d] at ht9'
      simp [hd, Dir.toInt] at ht9'
      rw [show cfg9.tapeAt (4 * p + -1) = s9 from by simpa [hr9, hp9, d, hd, Dir.toInt] using hrd9] at ht9'
      simpa [subsetSumCBTM] using ht9'
    have hnotrap9 : step9.result ≠ CBTMTransResult.mk (encodeState 101 10 0) F4.zero Dir.S := by
      intro htr9
      have hp10t : cfg10.headPos = 4 * p + -1 := by
        rw [hc9]
        dsimp [stepConfig]
        rw [htr9]
        dsimp
        rw [hp9]
        dsimp [d]
        simp [hd, Dir.toInt]
        first | done | omega
      have hrd10t : step10.readSym = F4.zero := by
        have hrd10' : step10.readSym = cfg10.tapeAt cfg10.headPos := by simpa using hr10
        rw [hrd10', hp10t]
        rw [hc9]
        rw [stepConfig_tapeAt_eq_of_eq cfg9 step9.result (4 * p + -1) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt])]
        rw [htr9]
      have hmem10t : step10.result ∈ transition4 (encodeState 101 10 0) F4.zero := by
        have ht10' : step10.result ∈ subsetSumCBTM.transition (cfg10.state, cfg10.tapeAt cfg10.headPos, cfg10.headPos) := ht10
        rw [show cfg10.state = encodeState 101 10 0 from by simpa [stepConfig, hc9, htr9]] at ht10'
        rw [hp10t] at ht10'
        rw [show cfg10.tapeAt (4 * p + -1) = F4.zero from by simpa [hr10, hp10t] using hrd10t] at ht10'
        simpa [subsetSumCBTM] using ht10'
      have hres10t : step10.result = CBTMTransResult.mk (encodeState 101 11 0) F4.zero Dir.S :=
        trap_step10_forced step10.result hmem10t
      have hp11t : cfg11.headPos = 4 * p + -1 := by
        rw [hc10]
        dsimp [stepConfig]
        rw [hres10t]
        dsimp
        rw [hc9]
        dsimp [stepConfig]
        rw [htr9]
        dsimp
        rw [hp9]
        dsimp [d]
        simp [hd, Dir.toInt]
        first | done | omega
      have hrd11t : step11.readSym = F4.zero := by
        have hrd11' : step11.readSym = cfg11.tapeAt cfg11.headPos := by simpa using hr11
        rw [hrd11', hp11t]
        rw [hc10]
        rw [stepConfig_tapeAt_eq_of_eq cfg10 step10.result (4 * p + -1) (by rw [hp10t])]
        rw [hres10t]
      have hmem11t : step11.result ∈ transition4 (encodeState 101 11 0) F4.zero := by
        have ht11' : step11.result ∈ subsetSumCBTM.transition (cfg11.state, cfg11.tapeAt cfg11.headPos, cfg11.headPos) := ht11
        rw [show cfg11.state = encodeState 101 11 0 from by simpa [stepConfig, hc10, hres10t]] at ht11'
        rw [hp11t] at ht11'
        rw [show cfg11.tapeAt (4 * p + -1) = F4.zero from by simpa [hr11, hp11t] using hrd11t] at ht11'
        simpa [subsetSumCBTM] using ht11'
      have hres11t : step11.result = CBTMTransResult.mk (encodeState 101 0 0) F4.zero Dir.S :=
        trap_step11_forced step11.result hmem11t
      have hhead_trap : cfgc'.headPos = 4 * p + -1 := by
        rw [hc11]
        dsimp [stepConfig]
        rw [hres11t]
        dsimp
        rw [hp11t]
        simp [Dir.toInt]
      rw [hhead_trap] at hhead'
      simp [hd, Dir.toInt] at hhead'
      first | done | omega
    have hres9 : step9.result = CBTMTransResult.mk (encodeState qn 10 regr) s9 Dir.L := by
      have hres9' : step9.result = CBTMTransResult.mk (encodeState qn 10 regr) s9 Dir.L ∨
          step9.result = CBTMTransResult.mk (encodeState 101 10 0) F4.zero Dir.S := by
        dsimp [transition4] at hmem9
        rw [hdecph 9 (by norm_num)] at hmem9
        rw [decodeResult_encodeResult_ok r hmk] at hmem9
        rw [hqnn] at hmem9
        by_cases him9 : F4.im s9 <;> simp [him9, hqne] at hmem9
        · simpa [hd] using hmem9
        · left
          simpa [hd] using hmem9
      rcases hres9' with hg | htrap
      · exact hg
      · exfalso
        exact hnotrap9 htrap
    have hp10 : cfg10.headPos = 4 * p + -2 := by
      rw [hc9]
      dsimp [stepConfig]
      rw [hres9]
      dsimp
      rw [hp9]
      dsimp [d]
      simp [hd, Dir.toInt]
      first | done | omega
    have hst10 : step10.fromState = encodeState qn 10 regr := by
      have hst10' : step10.fromState = cfg10.state := by simpa using hf10
      rw [hst10']
      rw [hc9]
      dsimp [stepConfig]
      rw [hres9]
    have hrd10 : step10.readSym = s10 := by
      have hrd10' : step10.readSym = cfg10.tapeAt cfg10.headPos := by simpa using hr10
      rw [hrd10', hp10]
      rw [hc9]
      rw [stepConfig_tapeAt_eq_of_ne cfg9 step9.result (4 * p + -2) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt]; first | done | omega)]
      rw [hc8]
      rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * p + -2) (by rw [hp8]; omega)]
      rw [hc7]
      rw [stepConfig_tapeAt_eq_of_ne cfg7 step7.result (4 * p + -2) (by rw [hp7]; omega)]
      rw [hc6]
      rw [stepConfig_tapeAt_eq_of_ne cfg6 step6.result (4 * p + -2) (by rw [hp6]; omega)]
      rw [hc5]
      rw [stepConfig_tapeAt_eq_of_ne cfg5 step5.result (4 * p + -2) (by rw [hp5]; omega)]
      rw [hc4]
      rw [stepConfig_tapeAt_eq_of_ne cfg4 step4.result (4 * p + -2) (by rw [hp4]; omega)]
      rw [hc3]
      rw [stepConfig_tapeAt_eq_of_ne cfg3 step3.result (4 * p + -2) (by rw [hp3]; omega)]
      rw [hc2]
      rw [stepConfig_tapeAt_eq_of_ne cfg2 step2.result (4 * p + -2) (by rw [hp2]; omega)]
      rw [hc1]
      rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * p + -2) (by rw [hp1]; omega)]
      rw [hc0]
      rw [stepConfig_tapeAt_eq_of_ne cfgc step0.result (4 * p + -2) (by rw [hp]; omega)]
      rw [show 4 * p + -2 = 4 * (p - 1) + (2 : ℕ) by omega]
      rw [hcorr.2.2 (p - 1) 2 (by norm_num)]
      dsimp [s10, d, tprev]
      simp [hd]
    have him10s : F4.im s10 = false := by
      dsimp [s10, d, tprev]
      simp [hd]
    have hmem10 : step10.result ∈ transition4 (encodeState qn 10 regr) s10 := by
      have ht10' : step10.result ∈ subsetSumCBTM.transition (cfg10.state, cfg10.tapeAt cfg10.headPos, cfg10.headPos) := ht10
      rw [show cfg10.state = encodeState qn 10 regr from by simpa [hf10] using hst10] at ht10'
      rw [hp10] at ht10'
      rw [show cfg10.tapeAt (4 * p + -2) = s10 from by simpa [hr10, hp10] using hrd10] at ht10'
      simpa [subsetSumCBTM] using ht10'
    have hnotrap10 : step10.result ≠ CBTMTransResult.mk (encodeState 101 11 0) F4.zero Dir.S := by
      intro htr10
      have hp11t : cfg11.headPos = 4 * p + -2 := by
        rw [hc10]
        dsimp [stepConfig]
        rw [htr10]
        dsimp
        rw [hp10]
        simp [Dir.toInt]
        first | done | omega
      have hrd11t : step11.readSym = F4.zero := by
        have hrd11' : step11.readSym = cfg11.tapeAt cfg11.headPos := by simpa using hr11
        rw [hrd11', hp11t]
        rw [hc10]
        rw [stepConfig_tapeAt_eq_of_eq cfg10 step10.result (4 * p + -2) (by rw [hp10])]
        rw [htr10]
      have hmem11t : step11.result ∈ transition4 (encodeState 101 11 0) F4.zero := by
        have ht11' : step11.result ∈ subsetSumCBTM.transition (cfg11.state, cfg11.tapeAt cfg11.headPos, cfg11.headPos) := ht11
        rw [show cfg11.state = encodeState 101 11 0 from by simpa [stepConfig, hc10, htr10]] at ht11'
        rw [hp11t] at ht11'
        rw [show cfg11.tapeAt (4 * p + -2) = F4.zero from by simpa [hr11, hp11t] using hrd11t] at ht11'
        simpa [subsetSumCBTM] using ht11'
      have hres11t : step11.result = CBTMTransResult.mk (encodeState 101 0 0) F4.zero Dir.S :=
        trap_step11_forced step11.result hmem11t
      have hhead_trap : cfgc'.headPos = 4 * p + -2 := by
        rw [hc11]
        dsimp [stepConfig]
        rw [hres11t]
        dsimp
        rw [hp11t]
        simp [Dir.toInt]
        first | done | omega
      rw [hhead_trap] at hhead'
      simp [hd, Dir.toInt] at hhead'
      first | done | omega
    have hres10 : step10.result = CBTMTransResult.mk (encodeState qn 11 regr) s10 Dir.L := by
      have hres10' : step10.result = CBTMTransResult.mk (encodeState qn 11 regr) s10 Dir.L ∨
          step10.result = CBTMTransResult.mk (encodeState 101 11 0) F4.zero Dir.S := by
        dsimp [transition4] at hmem10
        rw [hdecph 10 (by norm_num)] at hmem10
        rw [decodeResult_encodeResult_ok r hmk] at hmem10
        rw [hqnn] at hmem10
        by_cases him10 : F4.im s10 <;> simp [him10, hqne] at hmem10
        · simpa [hd] using hmem10
        · left
          simpa [hd] using hmem10
      rcases hres10' with hg | htrap
      · exact hg
      · exfalso
        exact hnotrap10 htrap
    have hp11 : cfg11.headPos = 4 * p + -3 := by
      rw [hc10]
      dsimp [stepConfig]
      rw [hres10]
      dsimp
      rw [hp10]
      simp [Dir.toInt]
      first | done | omega
    have hst11 : step11.fromState = encodeState qn 11 regr := by
      have hst11' : step11.fromState = cfg11.state := by simpa using hf11
      rw [hst11']
      rw [hc10]
      dsimp [stepConfig]
      rw [hres10]
    have hrd11 : step11.readSym = s11 := by
      have hrd11' : step11.readSym = cfg11.tapeAt cfg11.headPos := by simpa using hr11
      rw [hrd11', hp11]
      rw [hc10]
      rw [stepConfig_tapeAt_eq_of_ne cfg10 step10.result (4 * p + -3) (by rw [hp10]; omega)]
      rw [hc9]
      rw [stepConfig_tapeAt_eq_of_ne cfg9 step9.result (4 * p + -3) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt]; first | done | omega)]
      rw [hc8]
      rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * p + -3) (by rw [hp8]; omega)]
      rw [hc7]
      rw [stepConfig_tapeAt_eq_of_ne cfg7 step7.result (4 * p + -3) (by rw [hp7]; omega)]
      rw [hc6]
      rw [stepConfig_tapeAt_eq_of_ne cfg6 step6.result (4 * p + -3) (by rw [hp6]; omega)]
      rw [hc5]
      rw [stepConfig_tapeAt_eq_of_ne cfg5 step5.result (4 * p + -3) (by rw [hp5]; omega)]
      rw [hc4]
      rw [stepConfig_tapeAt_eq_of_ne cfg4 step4.result (4 * p + -3) (by rw [hp4]; omega)]
      rw [hc3]
      rw [stepConfig_tapeAt_eq_of_ne cfg3 step3.result (4 * p + -3) (by rw [hp3]; omega)]
      rw [hc2]
      rw [stepConfig_tapeAt_eq_of_ne cfg2 step2.result (4 * p + -3) (by rw [hp2]; omega)]
      rw [hc1]
      rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * p + -3) (by rw [hp1]; omega)]
      rw [hc0]
      rw [stepConfig_tapeAt_eq_of_ne cfgc step0.result (4 * p + -3) (by rw [hp]; omega)]
      rw [show 4 * p + -3 = 4 * (p - 1) + (1 : ℕ) by omega]
      rw [hcorr.2.2 (p - 1) 1 (by norm_num)]
      dsimp [s11, d, tprev]
      simp [hd]
    have him11s : F4.im s11 = false := by
      dsimp [s11, d, tprev]
      simp [hd]

    have hprd9 : (F4.im step9.readSym) = false := by rw [hrd9]; exact him9s
    have hprd10 : (F4.im step10.readSym) = false := by rw [hrd10]; exact him10s
    have hprd11 : (F4.im step11.readSym) = false := by rw [hrd11]; exact him11s
    rw [hπ']
    by_cases hbr : Sym.isBranch sym = true
    · simp [hprd0, hprd1, hprd2, hprd3, hprd4, hprd5, hprd6, hprd7, hprd8, hprd9, hprd10, hprd11, hbr]
    · have hbrf : Sym.isBranch sym = false := by
        cases h : Sym.isBranch sym
        · simpa using h
        · exfalso
          exact hbr h
      simp [hprd0, hprd1, hprd2, hprd3, hprd4, hprd5, hprd6, hprd7, hprd8, hprd9, hprd10, hprd11, hbrf]
  · -- d = R:读 w1/w2/w3
    have hc8'1 : cfg8.tapeAt (4 * p + 1) = w1 := by
      rw [hc7]
      rw [stepConfig_tapeAt_eq_of_ne cfg7 step7.result (4 * p + 1) (by rw [hp7]; omega)]
      rw [hc6]
      rw [stepConfig_tapeAt_eq_of_ne cfg6 step6.result (4 * p + 1) (by rw [hp6]; omega)]
      rw [hc5]
      rw [stepConfig_tapeAt_eq_of_eq cfg5 step5.result (4 * p + 1) (by rw [hp5])]
      rw [hres5]
    have hc8'2 : cfg8.tapeAt (4 * p + 2) = w2 := by
      rw [hc7]
      rw [stepConfig_tapeAt_eq_of_ne cfg7 step7.result (4 * p + 2) (by rw [hp7]; omega)]
      rw [hc6]
      rw [stepConfig_tapeAt_eq_of_ne cfg6 step6.result (4 * p + 2) (by rw [hp6]; omega)]
      rw [hc5]
      rw [stepConfig_tapeAt_eq_of_ne cfg5 step5.result (4 * p + 2) (by rw [hp5]; omega)]
      rw [hc4]
      rw [stepConfig_tapeAt_eq_of_eq cfg4 step4.result (4 * p + 2) (by rw [hp4])]
      rw [hres4]
    have hc8'3 : cfg8.tapeAt (4 * p + 3) = w3 := by
      rw [hc7]
      rw [stepConfig_tapeAt_eq_of_ne cfg7 step7.result (4 * p + 3) (by rw [hp7]; omega)]
      rw [hc6]
      rw [stepConfig_tapeAt_eq_of_ne cfg6 step6.result (4 * p + 3) (by rw [hp6]; omega)]
      rw [hc5]
      rw [stepConfig_tapeAt_eq_of_ne cfg5 step5.result (4 * p + 3) (by rw [hp5]; omega)]
      rw [hc4]
      rw [stepConfig_tapeAt_eq_of_ne cfg4 step4.result (4 * p + 3) (by rw [hp4]; omega)]
      rw [hc3]
      rw [stepConfig_tapeAt_eq_of_eq cfg3 step3.result (4 * p + 3) (by rw [hp3])]
      rw [hstep3']
      dsimp [w3, nrs]
      rw [← symTo4F4_getD3_eq_lastD r.writeSym]
    have hst9 : step9.fromState = encodeState qn 9 regr := by
      have hst9' : step9.fromState = cfg9.state := by simpa using hf9
      rw [hst9']
      rw [hc8]
      dsimp [stepConfig]
      rw [hres8]
    have hrd9 : step9.readSym = w1 := by
      have hrd9' : step9.readSym = cfg9.tapeAt cfg9.headPos := by simpa using hr9
      rw [hrd9', hp9]
      dsimp [d]
      simp [hd, Dir.toInt]
      rw [hc8]
      rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * p + 1) (by rw [hp8]; omega)]
      rw [hc8'1]
    have him9s : F4.im s9 = false := by
      dsimp [s9, d]
      simp [hd, hw1]
    have hmem9 : step9.result ∈ transition4 (encodeState qn 9 regr) w1 := by
      have ht9' : step9.result ∈ subsetSumCBTM.transition (cfg9.state, cfg9.tapeAt cfg9.headPos, cfg9.headPos) := ht9
      rw [show cfg9.state = encodeState qn 9 regr from by simpa [hf9] using hst9] at ht9'
      rw [hp9] at ht9'
      dsimp [d] at ht9'
      simp [hd, Dir.toInt] at ht9'
      rw [show cfg9.tapeAt (4 * p + 1) = w1 from by simpa [hr9, hp9, d, hd, Dir.toInt] using hrd9] at ht9'
      simpa [subsetSumCBTM] using ht9'
    have hres9 : step9.result = CBTMTransResult.mk (encodeState qn 10 regr) w1 Dir.R := by
      dsimp [transition4] at hmem9
      rw [hdecph 9 (by norm_num)] at hmem9
      simp [hw1, hqne] at hmem9
      rw [decodeResult_encodeResult_ok r hmk] at hmem9
      rw [hqnn] at hmem9
      simpa [hd] using hmem9
    have hp10 : cfg10.headPos = 4 * p + 2 := by
      rw [hc9]
      dsimp [stepConfig]
      rw [hres9]
      dsimp
      rw [hp9]
      dsimp [d]
      simp [hd, Dir.toInt]
      omega
    have hst10 : step10.fromState = encodeState qn 10 regr := by
      have hst10' : step10.fromState = cfg10.state := by simpa using hf10
      rw [hst10']
      rw [hc9]
      dsimp [stepConfig]
      rw [hres9]
    have hrd10 : step10.readSym = w2 := by
      have hrd10' : step10.readSym = cfg10.tapeAt cfg10.headPos := by simpa using hr10
      rw [hrd10', hp10]
      rw [hc9]
      rw [stepConfig_tapeAt_eq_of_ne cfg9 step9.result (4 * p + 2) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt]; first | done | omega)]
      rw [hc8]
      rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * p + 2) (by rw [hp8]; omega)]
      rw [hc8'2]
    have him10s : F4.im s10 = false := by
      dsimp [s10, d]
      simp [hd, hw2]
    have hmem10 : step10.result ∈ transition4 (encodeState qn 10 regr) w2 := by
      have ht10' : step10.result ∈ subsetSumCBTM.transition (cfg10.state, cfg10.tapeAt cfg10.headPos, cfg10.headPos) := ht10
      rw [show cfg10.state = encodeState qn 10 regr from by simpa [hf10] using hst10] at ht10'
      rw [hp10] at ht10'
      rw [show cfg10.tapeAt (4 * p + 2) = w2 from by simpa [hr10, hp10] using hrd10] at ht10'
      simpa [subsetSumCBTM] using ht10'
    have hres10 : step10.result = CBTMTransResult.mk (encodeState qn 11 regr) w2 Dir.R := by
      dsimp [transition4] at hmem10
      rw [hdecph 10 (by norm_num)] at hmem10
      simp [hw2, hqne] at hmem10
      rw [decodeResult_encodeResult_ok r hmk] at hmem10
      rw [hqnn] at hmem10
      simpa [hd] using hmem10
    have hp11 : cfg11.headPos = 4 * p + 3 := by
      rw [hc10]
      dsimp [stepConfig]
      rw [hres10]
      dsimp
      rw [hp10]
      simp [Dir.toInt]
      omega
    have hst11 : step11.fromState = encodeState qn 11 regr := by
      have hst11' : step11.fromState = cfg11.state := by simpa using hf11
      rw [hst11']
      rw [hc10]
      dsimp [stepConfig]
      rw [hres10]
    have hrd11 : step11.readSym = w3 := by
      have hrd11' : step11.readSym = cfg11.tapeAt cfg11.headPos := by simpa using hr11
      rw [hrd11', hp11]
      rw [hc10]
      rw [stepConfig_tapeAt_eq_of_ne cfg10 step10.result (4 * p + 3) (by rw [hp10]; omega)]
      rw [hc9]
      rw [stepConfig_tapeAt_eq_of_ne cfg9 step9.result (4 * p + 3) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt]; first | done | omega)]
      rw [hc8]
      rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * p + 3) (by rw [hp8]; omega)]
      rw [hc8'3]
    have him11s : F4.im s11 = false := by
      dsimp [s11, d, nrs]
      simp [hd]
      rw [l3a_symTo4F4_getD3_im r.writeSym]
      exact hw_nb
    have himw3 : F4.im w3 = false := by
      dsimp [w3, nrs]
      rw [l3a_symTo4F4_getD3_im r.writeSym]
      exact hw_nb
    have hprd9 : (F4.im step9.readSym) = false := by rw [hrd9]; exact hw1
    have hprd10 : (F4.im step10.readSym) = false := by rw [hrd10]; exact hw2
    have hprd11 : (F4.im step11.readSym) = false := by rw [hrd11]; exact himw3
    rw [hπ']
    by_cases hbr : Sym.isBranch sym = true
    · simp [hprd0, hprd1, hprd2, hprd3, hprd4, hprd5, hprd6, hprd7, hprd8, hprd9, hprd10, hprd11, hbr]
    · have hbrf : Sym.isBranch sym = false := by
        cases h : Sym.isBranch sym
        · simpa using h
        · exfalso
          exact hbr h
      simp [hprd0, hprd1, hprd2, hprd3, hprd4, hprd5, hprd6, hprd7, hprd8, hprd9, hprd10, hprd11, hbrf]
  · -- d = S:读 w0 三次
    have hst9 : step9.fromState = encodeState qn 9 regr := by
      have hst9' : step9.fromState = cfg9.state := by simpa using hf9
      rw [hst9']
      rw [hc8]
      dsimp [stepConfig]
      rw [hres8]
    have hp9s : cfg9.headPos = 4 * p := by
      rw [hc8]
      dsimp [stepConfig]
      rw [hres8]
      dsimp
      rw [hp8]
      simp [hd, Dir.toInt]
    have hrd9 : step9.readSym = w0 := by
      have hrd9' : step9.readSym = cfg9.tapeAt cfg9.headPos := by simpa using hr9
      rw [hrd9', hp9s]
      rw [hc8]
      rw [stepConfig_tapeAt_eq_of_eq cfg8 step8.result (4 * p) (by rw [hp8])]
      rw [hres8]
    have him9s : F4.im s9 = false := by
      dsimp [s9, d]
      simp [hd, hw0]
    have hmem9 : step9.result ∈ transition4 (encodeState qn 9 regr) w0 := by
      have ht9' : step9.result ∈ subsetSumCBTM.transition (cfg9.state, cfg9.tapeAt cfg9.headPos, cfg9.headPos) := ht9
      rw [show cfg9.state = encodeState qn 9 regr from by simpa [hf9] using hst9] at ht9'
      rw [hp9s] at ht9'
      rw [show cfg9.tapeAt (4 * p) = w0 from by simpa [hr9, hp9s] using hrd9] at ht9'
      simpa [subsetSumCBTM] using ht9'
    have hres9 : step9.result = CBTMTransResult.mk (encodeState qn 10 regr) w0 Dir.S := by
      dsimp [transition4] at hmem9
      rw [hdecph 9 (by norm_num)] at hmem9
      simp [hw0, hqne] at hmem9
      rw [decodeResult_encodeResult_ok r hmk] at hmem9
      rw [hqnn] at hmem9
      simpa [hd] using hmem9
    have hp10 : cfg10.headPos = 4 * p := by
      rw [hc9]
      dsimp [stepConfig]
      rw [hres9]
      dsimp
      rw [hp9s]
      simp [Dir.toInt]
    have hst10 : step10.fromState = encodeState qn 10 regr := by
      have hst10' : step10.fromState = cfg10.state := by simpa using hf10
      rw [hst10']
      rw [hc9]
      dsimp [stepConfig]
      rw [hres9]
    have hrd10 : step10.readSym = w0 := by
      have hrd10' : step10.readSym = cfg10.tapeAt cfg10.headPos := by simpa using hr10
      rw [hrd10', hp10]
      rw [hc9]
      rw [stepConfig_tapeAt_eq_of_eq cfg9 step9.result (4 * p) (by rw [hp9s])]
      rw [hres9]
    have him10s : F4.im s10 = false := by
      dsimp [s10, d]
      simp [hd, hw0]
    have hmem10 : step10.result ∈ transition4 (encodeState qn 10 regr) w0 := by
      have ht10' : step10.result ∈ subsetSumCBTM.transition (cfg10.state, cfg10.tapeAt cfg10.headPos, cfg10.headPos) := ht10
      rw [show cfg10.state = encodeState qn 10 regr from by simpa [hf10] using hst10] at ht10'
      rw [hp10] at ht10'
      rw [show cfg10.tapeAt (4 * p) = w0 from by simpa [hr10, hp10] using hrd10] at ht10'
      simpa [subsetSumCBTM] using ht10'
    have hres10 : step10.result = CBTMTransResult.mk (encodeState qn 11 regr) w0 Dir.S := by
      dsimp [transition4] at hmem10
      rw [hdecph 10 (by norm_num)] at hmem10
      simp [hw0, hqne] at hmem10
      rw [decodeResult_encodeResult_ok r hmk] at hmem10
      rw [hqnn] at hmem10
      simpa [hd] using hmem10
    have hp11 : cfg11.headPos = 4 * p := by
      rw [hc10]
      dsimp [stepConfig]
      rw [hres10]
      dsimp
      rw [hp10]
      simp [Dir.toInt]
    have hst11 : step11.fromState = encodeState qn 11 regr := by
      have hst11' : step11.fromState = cfg11.state := by simpa using hf11
      rw [hst11']
      rw [hc10]
      dsimp [stepConfig]
      rw [hres10]
    have hrd11 : step11.readSym = w0 := by
      have hrd11' : step11.readSym = cfg11.tapeAt cfg11.headPos := by simpa using hr11
      rw [hrd11', hp11]
      rw [hc10]
      rw [stepConfig_tapeAt_eq_of_eq cfg10 step10.result (4 * p) (by rw [hp10])]
      rw [hres10]
    have him11s : F4.im s11 = false := by
      dsimp [s11, d]
      simp [hd, hw0]
    have hprd9 : (F4.im step9.readSym) = false := by rw [hrd9]; exact hw0
    have hprd10 : (F4.im step10.readSym) = false := by rw [hrd10]; exact hw0
    have hprd11 : (F4.im step11.readSym) = false := by rw [hrd11]; exact hw0
    rw [hπ']
    by_cases hbr : Sym.isBranch sym = true
    · simp [hprd0, hprd1, hprd2, hprd3, hprd4, hprd5, hprd6, hprd7, hprd8, hprd9, hprd10, hprd11, hbr]
    · have hbrf : Sym.isBranch sym = false := by
        cases h : Sym.isBranch sym
        · simpa using h
        · exfalso
          exact hbr h
      simp [hprd0, hprd1, hprd2, hprd3, hprd4, hprd5, hprd6, hprd7, hprd8, hprd9, hprd10, hprd11, hbrf]


/-- T8a 轮 C(件 2):L 步(移动 L 且非 101)的前字符非分支。
    = Lmove_src_ge3(源 ≥3)+ no_branch_ge3(带无分支,态 ≥3 处)。 -/
lemma l3a_Lstep_prev_not_branch (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (hpos : ∀ v ∈ inst.elements, 0 < v) (htarget : 0 < inst.target)
    {π : List SymStep} {cfgs : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfgs)
    (hext : ∃ (π₂ : List SymStep) (cfg₂ : SymConfig),
      SymReachablePath VerifierSym.transition (encodeInstanceSym inst) (π ++ π₂) cfg₂ ∧
      cfg₂.state = 100)
    (hno100 : ∀ step ∈ π, step.fromState ≠ 100)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101)
    {q : ℕ} {s : Sym} {r : SymTransResult}
    (hq : cfgs.state = q) (hr : r ∈ VerifierSym.transition (q, s))
    (hL : r.moveDir = Dir.L) (hne : r.nextState ≠ 101) :
    Sym.isBranch (cfgs.tape (cfgs.headPos - 1)) = false := by
  have hge : 3 ≤ q := l3a_Lmove_src_ge3 q s r hr hL hne
  have hge3 : cfgs.state ≥ 3 := by simpa [hq] using hge
  have hqne : cfgs.state ≠ 101 := by
    intro h101
    rw [hq] at h101
    have habs := symTransition_trap101_absorb s r (by simpa [h101] using hr)
    exact hne habs
  exact l3a_no_branch_ge3 inst hm hpos htarget h hext hno100 hno101 hge3 hqne
    (cfgs.headPos - 1)

/-- T8b 轮 D:接受 Sym 路径 ⟹ 块路径,块路径的 im-true 读微步数
    = 读分支 Sym 步数(每块贡献 = 分支?1:0——l3a_goodblock_branchCount_eq,
    前提提供:L 步 hprev_nb = l3a_Lstep_prev_not_branch,写 hw_nb = forkBridge)。
    仿 l3a_symPath_fork_ge 骨架,≥ 升级为 =。 -/
lemma l3a_symPath_fork_eq (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (hpos : ∀ v ∈ inst.elements, 0 < v) (htarget : 0 < inst.target)
    {πs : List SymStep} {cfgs : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) πs cfgs)
    (hext : ∃ (π₂ : List SymStep) (cfg₂ : SymConfig),
      SymReachablePath VerifierSym.transition (encodeInstanceSym inst) (πs ++ π₂) cfg₂ ∧
      cfg₂.state = 100)
    (hsteps_ok : ∀ step ∈ πs, step.fromState ≤ 101)
    (hbranch : ∀ step ∈ πs, Sym.isBranch step.readSym → step.fromState = 2)
    (hno100 : ∀ step ∈ πs, step.fromState ≠ 100)
    (hno101 : ∀ step ∈ πs, step.result.nextState ≠ 101) :
    ∃ πc : ComputationPath, ∃ cfgc : CBTMConfig subsetSumCBTM (flat4F4 (encodeInstanceSym inst)),
      GoodBlockPath (flat4F4 (encodeInstanceSym inst))
        (initialConfig subsetSumCBTM (flat4F4 (encodeInstanceSym inst))) πc cfgc ∧
      blockCorrespond cfgc cfgs ∧
      (πc.filter (fun st => F4.im st.readSym)).length =
        (πs.filter (fun st => Sym.isBranch st.readSym)).length := by
  induction h with
  | nil =>
      refine ⟨[], initialConfig subsetSumCBTM (flat4F4 (encodeInstanceSym inst)),
        GoodBlockPath.nil _, initialBlockCorrespond (encodeInstanceSym inst), ?_⟩
      simp
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
        have hno100₀ : ∀ step₀ ∈ π₀, step₀.fromState ≠ 100 := by
          intro st hst
          exact hno100 st (by simp [hst])
        have hext₀ : ∃ (π₂ : List SymStep) (cfg₂ : SymConfig),
            SymReachablePath VerifierSym.transition (encodeInstanceSym inst) (π₀ ++ π₂) cfg₂ ∧
            cfg₂.state = 100 := by
          rcases hext with ⟨π₂, cfg₂, hpath₂, hacc₂⟩
          refine ⟨[step] ++ π₂, cfg₂, ?_, hacc₂⟩
          simpa [List.append_assoc] using hpath₂
        rcases ih hext₀ hok0 hbr0 hno100₀ hno101₀ with ⟨πc₀, cfgc₁, hbp, hcorr₁, hfork₀⟩
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
        have hrs : step.result.nextState < 101 := by
          have hne : step.result.nextState ≠ 101 := hno101 step (by simp)
          have hle : step.result.nextState ≤ 101 :=
            transition_nextState_le101 cfg₁.state (cfg₁.tape cfg₁.headPos) hqle step.result htrans'
          omega
        rcases expand_sym_step cfg₁.state (cfg₁.tape cfg₁.headPos) step.result htrans' hqle hbr' hrs
          (flat4F4 (encodeInstanceSym inst)) cfgc₁ cfg₁ cfg₁.headPos hcorr₁ hcorr₁.1 hcorr₁.2.1 rfl
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
        have hblock : GoodBlock (flat4F4 (encodeInstanceSym inst)) cfgc₁ πm cfgm cfg₁ cfg₁.headPos cfg₁.state
            (cfg₁.tape cfg₁.headPos) step.result :=
          ⟨hsteps_m, hlen_m, ⟨
          hcorr₁.1,
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
        have hsingle : GoodBlockPath (flat4F4 (encodeInstanceSym inst)) cfgc₁ πm cfgm := by
          simpa using (GoodBlockPath.cons cfgc₁ cfgm cfgm πm [] cfg₁ cfg₁.headPos cfg₁.state
            (cfg₁.tape cfg₁.headPos) step.result hblock (GoodBlockPath.nil cfgm))
        -- fork 组合:块贡献 = 分支 ?1:0(精确;branchCount_eq = classify 分类 + S5c 排除)
        have hprev_nb : step.result.moveDir = Dir.L →
            Sym.isBranch (cfg₁.tape (cfg₁.headPos - 1)) = false := by
          intro hL
          have hno100₀ : ∀ step₀ ∈ π₀, step₀.fromState ≠ 100 := by
            intro st hst
            exact hno100 st (by simp [hst])
          exact l3a_Lstep_prev_not_branch inst hm hpos htarget hprev hext₀ hno100₀ hno101₀
            (by simpa [hfrom]) htrans' hL (hno101 step (by simp))
        have hw_nb : Sym.isBranch step.result.writeSym = false := by
          have hqlt : step.fromState < 102 := by
            have hok1 := hsteps_ok step (by simp)
            omega
          have hqne100 : step.fromState ≠ 100 := hno100 step (by simp)
          have hne1 : step.result.nextState ≠ 101 := hno101 step (by simp)
          have hw := forkBridge_no_write_branch step.fromState hqlt hqne100 step.readSym
            step.result (by simpa [hfrom, hread] using htrans) hne1
          unfold Sym.isBranch SymKind.isBranch
          rw [decide_eq_false_iff_not]
          intro hk
          rcases hk with hA | hB
          · exact hw.1 hA
          · exact hw.2 hB
        have hforkm : (πm.filter (fun st => F4.im st.readSym)).length =
            (if Sym.isBranch step.readSym then 1 else 0) := by
          have hbq := l3a_goodblock_branchCount_eq hblock hrs hprev_nb hw_nb
          simpa [← hread] using hbq
        refine ⟨πc₀ ++ πm, cfgm, GoodBlockPath_append (flat4F4 (encodeInstanceSym inst))
          (initialConfig subsetSumCBTM (flat4F4 (encodeInstanceSym inst))) cfgc₁ cfgm πc₀ πm hbp hsingle, hcorr_m, ?_⟩
        · by_cases hb2 : Sym.isBranch step.readSym
          · rw [List.filter_append, List.length_append]
            rw [List.filter_append, List.length_append]
            have hfm1 : (πm.filter (fun st => F4.im st.readSym)).length = 1 := by
              simpa [hb2] using hforkm
            have hsm1 : ([step].filter (fun st => Sym.isBranch st.readSym)).length = 1 := by
              rw [List.filter_cons]
              simp [hb2]
            rw [hfm1, hsm1]
            omega
          · rw [List.filter_append, List.length_append]
            rw [List.filter_append, List.length_append]
            have hbf : Sym.isBranch step.readSym = false := by
              cases h : Sym.isBranch step.readSym
              · simpa using h
              · exfalso
                exact hb2 h
            have hfm0 : (πm.filter (fun st => F4.im st.readSym)).length = 0 := by
              simpa [hbf] using hforkm
            have hsm0 : ([step].filter (fun st => Sym.isBranch st.readSym)).length = 0 := by
              rw [List.filter_cons]
              simp [hbf]
            rw [hfm0, hsm0]
            omega


lemma l3a_fork_eq_elements (inst : SubsetSumInstance) (hne : inst.elements ≠ [])
    (hpos : ∀ v ∈ inst.elements, 0 < v) (htarget : 0 < inst.target)
    (hholds : subsetSumHolds inst) :
    ∃ πc : ComputationPath,
      ∃ cfgc : CBTMConfig subsetSumCBTM (flat4F4 (encodeInstanceSym inst)),
        GoodBlockPath (flat4F4 (encodeInstanceSym inst))
          (initialConfig subsetSumCBTM (flat4F4 (encodeInstanceSym inst))) πc cfgc ∧
        (πc.filter (fun st => F4.im st.readSym)).length = inst.elements.length := by
  have hacc : symAccepts VerifierSym.verifierSymTransition VerifierSym.acceptStates
      (encodeInstanceSym inst) := (symVerifier_correct inst hne hpos htarget).2 hholds
  rcases hacc with ⟨π, cfg, hpath, hmem⟩
  have hs100 : cfg.state = 100 := by
    simpa [VerifierSym.acceptStates, VerifierSym.qAccept] using hmem
  have hsteps : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π cfg :=
    reachablePath_to_steps hpath
  rcases symSteps_accept_exists_no_100 hsteps (by simpa [VerifierSym.qAccept] using hs100) with
    ⟨π', cfg', hsteps', hacc', hno100'⟩
  have hs100' : cfg'.state = 100 := by simpa [VerifierSym.qAccept] using hacc'
  have hno101' : ∀ step ∈ π', step.result.nextState ≠ 101 := symSteps_accept_no_101 hsteps' hs100'
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
  have hpath' : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π' cfg' :=
    (symSteps_initial_iff VerifierSym.verifierSymTransition (encodeInstanceSym inst) π' cfg').mp hsteps'
  have hcons := fork_conservation inst π' cfg' hpath' hno101' hno100'
  have hfork : (π'.filter (fun step => Sym.isBranch step.readSym)).length = inst.elements.length := by
    rw [hres'] at hcons
    simpa using hcons
  have hsteps_ok' : ∀ step ∈ π', step.fromState ≤ 101 := by
    intro step hst
    have hm := (symReachable_state_mem_legal hpath').2 step hst
    have hdec : ∀ q ∈ VerifierSym.legalStates, q ≤ 101 := by
      native_decide
    exact hdec step.fromState hm
  have hbranch' : ∀ step ∈ π', Sym.isBranch step.readSym → step.fromState = 2 :=
    symSteps_branch_only_q2 hsteps' hno101' hno100'
  have hm0 : 0 < (encodeElementsSym inst.elements).length :=
    l3a_encodeElementsSym_length_pos inst.elements hne
  have hext' : ∃ (π₂ : List SymStep) (cfg₂ : SymConfig),
      SymReachablePath VerifierSym.transition (encodeInstanceSym inst) (π' ++ π₂) cfg₂ ∧
      cfg₂.state = 100 := by
    refine ⟨[], cfg', ?_, hs100'⟩
    simpa using hpath'
  rcases l3a_symPath_fork_eq inst hm0 hpos htarget hpath' hext' hsteps_ok' hbranch' hno100' hno101' with
    ⟨πc, cfgc, hbp, hcorr, hge⟩
  refine ⟨πc, cfgc, hbp, ?_⟩
  rw [hge, ← hfork]

end SymToF4
end Mp
