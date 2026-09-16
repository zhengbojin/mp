import Mp.SubsetSumVerifierReverse5
import Mp.SubsetSumVerifierReverse6


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


/-!
# Reverse7:条款 5(后缀不变)正向方向

目标形态(方案 i/方案 a 后,去 A1 消费方使用):
  `subsetSumCBTM.tapeAccepts (SymToF4.encodeInstanceF4 inst) →
   ∀ gS : List Sym, tapeAccepts (SymToF4.encodeInstanceF4 inst ++ flat4F4 gS)`
(g 限定符号对齐;Sym 层 lift 后经完备性桥直接覆盖,无需任意 F4 残块处理)

换算约定(输入编码 → CBTM 符号版):
- 输入字符(2 bit)↔ 1 个 Sym 符号:符号数不变;
- 1 Sym ↔ 4F4(`symTo4F4`)1 块:按 F4 格计长 ×4;
- 带外/填充 = zero,与格 0-2 的 im=false 一致 ⇒ 零块可解码为 data0 false = blank;
- 一切界论证以符号/块为计数单位:接受路径读位 < |wS|(符号)⟺ 块窗口 < 4·|wS|。

正向链(设计定稿,Round 3 修正:不需 4|wS| ≤ |w|——两歧 + blank 尾回落):
```
tapeAccepts (encF4 inst)     -- w = flat4F4 (encS inst)
  → no_trap 12 分量(ab35a2c):⟨wS, πs, cfgsEnd, htake, hπs, h100, hreach0, …⟩
  → 两歧 r7_wS_prefix_dichotomy:wS <+: encS inst ∨ encS inst <+: wS
    Case 1:wS <+: encS → symSteps_lift_suffix 从 wS 直达 encS inst ++ gS(hreach0 界够)
    Case 2:encS <+: wS,超出块全 data0 false = blank(3b 字段,兄弟 P 加分量在途)
      → symInitialConfig_blank_tail(tape 全等)→ r7_accept_falls_back 落回 encS inst
      → symSteps_lift_suffix → symAccepts (encS inst ++ gS)
  → 完备性桥 symAccepts_implies_tapeAccepts(Compile:317)
  → tapeAccepts (encF4 inst ++ flat4F4 gS)✓
```

内容:
1. `symInitialConfig_append_lt`:初始带在 < |w| 处与 w 一致(任意后缀 g);
2. `symSteps_lift_suffix`:`symSteps_lift_extend`(Reverse5)泛化到任意后缀
   (lift 前提 hheads 保持为 < |w|,不随后缀增长放宽);
3. `r7_sym_accept_append`:no_trap 解码接受路径(SymSteps wS + state=100 + hreach0)
   ⇒ `symAccepts (wS ++ gS)`(任意 Sym 后缀);
4. wS 形态:`flat4F4_length_eq` + `r7_wS_eq_enc_of_blocks_bounded`
   (4|wS| ≤ |w| 前提版:htake + flat4F4_take + 注入 + enc_prefix_unique ⟹ wS = encS inst);
5. 两歧 + blank 尾回落:`r7_wS_prefix_dichotomy`(htake 两歧,不需 4 界)、
   `symInitialConfig_blank_tail`(blank^m 尾 = 带外,tape 函数全等)、
   `symSteps_blank_tail`(路径原样落回)、`r7_accept_falls_back`(两歧第二支组装);
6. [待 3b 字段] 主定理组装:no_trap → 两歧分 Case →(Case 2 用字段 + 回落)→
   lift → 完备性桥 → `r7_tapeAccepts_suffix_forward`。
-/

namespace Mp

open VerifierSym

/-- symInitialConfig 于 w 与 w ++ g 在 i < |w| 处相同(任意后缀 g)。 -/
lemma symInitialConfig_append_lt {w g : List Sym} (i : ℤ) (hi : i < w.length) :
    (symInitialConfig (w ++ g)).tape i = (symInitialConfig w).tape i := by
  induction g generalizing w with
  | nil => simp
  | cons s rest ih =>
      have h1 := SymToF4.symInitialConfig_extend_lt (w := w) (s := s) i hi
      have hw' : i < (w ++ [s]).length := by
        simp [List.length_append]
        omega
      have h2 := ih hw'
      calc
        (symInitialConfig (w ++ s :: rest)).tape i
            = (symInitialConfig ((w ++ [s]) ++ rest)).tape i := by
                rw [show w ++ s :: rest = (w ++ [s]) ++ rest by simp [List.append_assoc]]
        _ = (symInitialConfig (w ++ [s])).tape i := h2
        _ = (symInitialConfig w).tape i := h1

/-- SymSteps 路径从 w 带整体提升到 w ++ g(任意后缀):
每真前缀终点 headPos < |w| 时,lift 后状态/带头不变,< |w| 处磁带一致。 -/
lemma symSteps_lift_suffix {w g : List Sym} {πs : List SymStep} {cfgs : SymConfig}
    (h : SymSteps VerifierSym.transition (symInitialConfig w) πs cfgs)
    (hheads : ∀ (πs₀ : List SymStep) (cfgm : SymConfig),
      πs₀ <+: πs → πs₀ ≠ πs →
      SymSteps VerifierSym.transition (symInitialConfig w) πs₀ cfgm → cfgm.headPos < w.length) :
    ∃ cfgs' : SymConfig, SymSteps VerifierSym.transition (symInitialConfig (w ++ g)) πs cfgs' ∧
      cfgs'.state = cfgs.state ∧ (∀ i : ℤ, i < w.length → cfgs'.tape i = cfgs.tape i) ∧
      cfgs'.headPos = cfgs.headPos := by
  induction h with
  | nil =>
      refine ⟨symInitialConfig (w ++ g), SymSteps.nil, rfl, ?_, rfl⟩
      · intro i hi
        exact symInitialConfig_append_lt (w := w) (g := g) i hi
  | cons πs₀ step cfg₁ hprev hfrom hread htrans ih =>
      have hheads₀ : ∀ (πs₀' : List SymStep) (cfgm : SymConfig),
          πs₀' <+: πs₀ → πs₀' ≠ πs₀ →
          SymSteps VerifierSym.transition (symInitialConfig w) πs₀' cfgm → cfgm.headPos < w.length := by
        intro πs₀' cfgm hpre hne hh
        exact hheads πs₀' cfgm (List.IsPrefix.trans hpre ⟨[step], rfl⟩) (by
          intro heq
          have hlen2 : πs₀'.length = πs₀.length + 1 := by
            simpa using congrArg List.length heq
          rcases hpre with ⟨r, hr⟩
          have hlenr : πs₀'.length ≤ πs₀.length := by
            have : πs₀'.length + r.length = πs₀.length := by
              simpa using congrArg List.length hr
            omega
          omega) hh
      have hhead₀ : cfg₁.headPos < w.length := hheads πs₀ cfg₁ ⟨[step], rfl⟩ (by
        intro heq
        have : (πs₀ ++ [step]).length = πs₀.length := by
          simpa using congrArg List.length heq
        simp at this) hprev
      rcases ih hheads₀ with ⟨cfg₁', hprev', hs₁, ht₁, hp₁⟩
      refine ⟨symStepConfig cfg₁' step.result, SymSteps.cons πs₀ step cfg₁' hprev' ?_ ?_ ?_, ?_, ?_, ?_⟩
      · rw [hs₁]
        exact hfrom
      · rw [hp₁, ht₁ cfg₁.headPos hhead₀]
        exact hread
      · rw [hs₁, hp₁, ht₁ cfg₁.headPos hhead₀]
        exact htrans
      · dsimp [symStepConfig]
      · intro i hi
        dsimp [symStepConfig]
        by_cases hz : i = cfg₁.headPos
        · -- 写位(< |w|):lift 前后同写 step.result.writeSym
          simp [hz, hp₁]
        · have hz' : i ≠ cfg₁'.headPos := by
            intro heq
            apply hz
            rw [hp₁] at heq
            exact heq
          simp [hz, hz', ht₁ i hi]
      · dsimp [symStepConfig]
        rw [hp₁]

/-- 条款 5 正向(Sym 层):no_trap 解码给出的接受路径(SymSteps wS + state=100 + hreach0)
整体提升到 wS ++ gS(任意 Sym 后缀)⇒ wS 接受 ⟹ wS ++ gS 接受。 -/
theorem r7_sym_accept_append {wS gS : List Sym} {πs : List SymStep} {cfgsEnd : SymConfig}
    (hπs : SymSteps VerifierSym.transition (symInitialConfig wS) πs cfgsEnd)
    (h100 : cfgsEnd.state = 100)
    (hreach0 : ∀ (πs₀ : List SymStep) (cfgm : SymConfig),
      πs₀ <+: πs → πs₀ ≠ πs →
      SymSteps VerifierSym.transition (symInitialConfig wS) πs₀ cfgm → cfgm.headPos < wS.length) :
    symAccepts VerifierSym.transition VerifierSym.acceptStates (wS ++ gS) := by
  rcases symSteps_lift_suffix (w := wS) (g := gS) hπs hreach0 with ⟨cfgs', hπs', hs', ht', hp'⟩
  refine ⟨πs, cfgs', ?_, ?_⟩
  · exact (symSteps_initial_iff VerifierSym.transition (wS ++ gS) πs cfgs').1 hπs'
  · rw [hs']
    simp [VerifierSym.acceptStates, VerifierSym.qAccept, h100]

-- =====================================================================
-- wS 形态分析(换算:符号数不变,块长 ×4;4|wS| ≤ |w| 时解码恰覆盖输入)
-- 前提来自 no_trap_path_decodes_prefix 的公开分量(htake/haccS)
-- =====================================================================

/-- 4F4 展平长度 = 4 倍符号数。 -/
lemma flat4F4_length_eq (l : List Sym) : (SymToF4.flat4F4 l).length = 4 * l.length := by
  induction l with
  | nil => simp [SymToF4.flat4F4]
  | cons s rest ih =>
      simp [SymToF4.flat4F4, List.length_append]
      omega

/-- 解码块数不超出输入(4|wS| ≤ |w|,即解码不进入带外 pad)时,
wS 恰为输入的符号层编码:htake + flat4F4_take + 注入性 + enc_prefix_unique。 -/
theorem r7_wS_eq_enc_of_blocks_bounded {inst : SubsetSumInstance} {w : List F4} {wS : List Sym}
    (hw : w = SymToF4.encodeInstanceF4 inst)
    (hlen : 4 * wS.length ≤ w.length)
    (htake : w.take (4 * wS.length) = (SymToF4.flat4F4 wS).take w.length)
    (haccS : symAccepts VerifierSym.transition VerifierSym.acceptStates wS) :
    wS = encodeInstanceSym inst := by
  have hflat : SymToF4.flat4F4 ((encodeInstanceSym inst).take wS.length) = SymToF4.flat4F4 wS := by
    have hL : (SymToF4.flat4F4 (encodeInstanceSym inst)).take (4 * wS.length) =
        (SymToF4.flat4F4 wS).take w.length := by
      simpa [hw, SymToF4.encodeInstanceF4] using htake
    rw [← flat4F4_take] at hL
    have hR : (SymToF4.flat4F4 wS).take w.length = SymToF4.flat4F4 wS := by
      apply List.take_of_length_le
      rw [flat4F4_length_eq]
      exact hlen
    simpa [hR] using hL
  have hInj : (encodeInstanceSym inst).take wS.length = wS :=
    flat4F4_injective hflat
  have hpre : wS <+: encodeInstanceSym inst := by
    refine ⟨(encodeInstanceSym inst).drop wS.length, ?_⟩
    have ht : (encodeInstanceSym inst).take wS.length ++
        (encodeInstanceSym inst).drop wS.length = encodeInstanceSym inst :=
      List.take_append_drop wS.length (encodeInstanceSym inst)
    rw [hInj] at ht
    exact ht
  rcases symAccepts_implies_encodeInstanceSym wS haccS with ⟨inst', g', hwS, hvalid⟩
  have hInst : inst' = inst := by
    rcases hpre with ⟨r, hr⟩
    rw [hwS] at hr
    have hEq : encodeInstanceSym inst' ++ (g' ++ r) = encodeInstanceSym inst ++ [] := by
      rw [← List.append_assoc]
      rw [← hr]
      simp
    exact enc_prefix_unique (inst := inst') (inst' := inst) (g := g' ++ r) (g' := []) hEq
  have hg' : g' = [] := by
    have hwlen : w.length = 4 * (encodeInstanceSym inst).length := by
      rw [hw]
      unfold SymToF4.encodeInstanceF4
      rw [flat4F4_length_eq]
    have hlen' : 4 * wS.length ≤ 4 * (encodeInstanceSym inst).length := by
      simpa [hwlen] using hlen
    have hlenlen : wS.length = (encodeInstanceSym inst).length + g'.length := by
      rw [hwS, hInst]
      simp [List.length_append]
    have hlen0 : g'.length = 0 := by omega
    cases g' with
    | nil => rfl
    | cons _ _ => simp at hlen0
  rw [hwS, hInst, hg']
  simp

-- =====================================================================
-- 前缀两歧 + blank 尾回落(带外解码块 = data0 false = blank 时,路径落回 wS₀)
-- 不需要 4|wS| ≤ |w|:两歧分 Case,第二支靠 blank 尾回落
-- =====================================================================

/-- htake 两歧:解码串 wS 与输入块串 wS₀ 互为前缀(htakeW + flat4F4_take + 注入性)。 -/
theorem r7_wS_prefix_dichotomy {wS₀ wS : List Sym} {w : List F4}
    (hw : w = SymToF4.flat4F4 wS₀)
    (htake : w.take (4 * wS.length) = (SymToF4.flat4F4 wS).take w.length) :
    wS <+: wS₀ ∨ wS₀ <+: wS := by
  by_cases h : 4 * wS.length ≤ w.length
  · -- Case A:4|wS| ≤ |w| ⇒ flat4F4 wS <+: flat4F4 wS₀ ⇒ wS <+: wS₀
    left
    have hL : (SymToF4.flat4F4 wS₀).take (4 * wS.length) =
        (SymToF4.flat4F4 wS).take w.length := by
      simpa [hw] using htake
    have hL' := hL
    rw [← flat4F4_take] at hL
    have hR : (SymToF4.flat4F4 wS).take w.length = SymToF4.flat4F4 wS := by
      apply List.take_of_length_le
      rw [flat4F4_length_eq]
      exact h
    have hInj : wS₀.take wS.length = wS := by
      apply flat4F4_injective
      simpa [hR] using hL
    refine ⟨wS₀.drop wS.length, ?_⟩
    have ht : wS₀.take wS.length ++ wS₀.drop wS.length = wS₀ :=
      List.take_append_drop wS.length wS₀
    rw [hInj] at ht
    exact ht
  · -- Case B:|w| ≤ 4|wS| ⇒ flat4F4 wS₀ = (flat4F4 wS).take |w| ⇒ wS₀ <+: wS
    right
    have hle : w.length ≤ 4 * wS.length := by omega
    have hwlen : w.length = 4 * wS₀.length := by
      rw [hw]
      rw [flat4F4_length_eq]
    have hfull : (SymToF4.flat4F4 wS₀).take (4 * wS.length) = SymToF4.flat4F4 wS₀ := by
      apply List.take_of_length_le
      rw [flat4F4_length_eq]
      omega
    have hL : (SymToF4.flat4F4 wS₀).take (4 * wS.length) =
        (SymToF4.flat4F4 wS).take w.length := by
      simpa [hw] using htake
    have hInj : wS₀ = wS.take wS₀.length := by
      apply flat4F4_injective
      have htmp : (SymToF4.flat4F4 wS).take w.length = SymToF4.flat4F4 (wS.take wS₀.length) := by
        rw [hwlen]
        rw [← flat4F4_take]
      calc
        SymToF4.flat4F4 wS₀ = (SymToF4.flat4F4 wS₀).take (4 * wS.length) := hfull.symm
        _ = (SymToF4.flat4F4 wS).take w.length := hL
        _ = SymToF4.flat4F4 (wS.take wS₀.length) := htmp
    refine ⟨wS.drop wS₀.length, ?_⟩
    have ht : wS.take wS₀.length ++ wS.drop wS₀.length = wS :=
      List.take_append_drop wS₀.length wS
    rw [← hInj] at ht
    exact ht

/-- 初始带在 wS₀ ++ blank^m 与 wS₀ 上全等(blank 尾 = 带外值,不改变 tape 函数)。 -/
lemma symInitialConfig_blank_tail (wS₀ : List Sym) (m : ℕ) :
    (symInitialConfig (wS₀ ++ List.replicate m Sym.blank)).tape =
      (symInitialConfig wS₀).tape := by
  funext i
  unfold symInitialConfig
  dsimp
  by_cases h0 : 0 ≤ i
  · by_cases h1 : i.toNat < wS₀.length
    · have h1' : i.toNat < (wS₀ ++ List.replicate m Sym.blank).length := by
        simp [List.length_append]
        exact Nat.lt_of_lt_of_le h1 (Nat.le_add_right wS₀.length m)
      have hc1 : 0 ≤ i ∧ i.toNat < (wS₀ ++ List.replicate m Sym.blank).length := ⟨h0, h1'⟩
      have hc2 : 0 ≤ i ∧ i.toNat < wS₀.length := ⟨h0, h1⟩
      rw [dif_pos hc1, dif_pos hc2]
      exact List.getElem_append_left h1
    · by_cases h2 : i.toNat < (wS₀ ++ List.replicate m Sym.blank).length
      · have hc1 : 0 ≤ i ∧ i.toNat < (wS₀ ++ List.replicate m Sym.blank).length := ⟨h0, h2⟩
        have hn2 : ¬(0 ≤ i ∧ i.toNat < wS₀.length) := by
          intro h
          exact h1 h.2
        rw [dif_pos hc1, dif_neg hn2]
        have h2len : i.toNat < wS₀.length + m := by
          simpa [List.length_append] using h2
        have hle₀ : wS₀.length ≤ i.toNat := by omega
        rw [List.getElem_append_right (as := wS₀) (bs := List.replicate m Sym.blank) hle₀]
        have hsub : i.toNat - wS₀.length < m := by omega
        exact List.getElem_replicate (by simpa [List.length_replicate] using hsub)
      · have hn1 : ¬(0 ≤ i ∧ i.toNat < (wS₀ ++ List.replicate m Sym.blank).length) := by
          intro h
          exact h2 h.2
        have hn2 : ¬(0 ≤ i ∧ i.toNat < wS₀.length) := by
          intro h
          exact h1 h.2
        rw [dif_neg hn1, dif_neg hn2]
  · have hn1 : ¬(0 ≤ i ∧ i.toNat < (wS₀ ++ List.replicate m Sym.blank).length) := by
      intro h
      exact h0 h.1
    have hn2 : ¬(0 ≤ i ∧ i.toNat < wS₀.length) := by
      intro h
      exact h0 h.1
    rw [dif_neg hn1, dif_neg hn2]

/-- blank 尾输入上的 SymSteps 路径 = 原输入上的同一条路径(初始配置全等)。 -/
lemma symSteps_blank_tail {wS₀ : List Sym} {m : ℕ} {πs : List SymStep} {cfgs : SymConfig}
    (h : SymSteps VerifierSym.transition
      (symInitialConfig (wS₀ ++ List.replicate m Sym.blank)) πs cfgs) :
    SymSteps VerifierSym.transition (symInitialConfig wS₀) πs cfgs := by
  have hcfg : symInitialConfig (wS₀ ++ List.replicate m Sym.blank) = symInitialConfig wS₀ := by
    unfold symInitialConfig
    exact congrArg (fun f : ℤ → Sym => ({ state := 0, tape := f, headPos := 0 } : SymConfig))
      (symInitialConfig_blank_tail wS₀ m)
  simpa [hcfg] using h

/-- 两歧第二支回落:encS inst <+: wS 且超出部分全是 blank(带外解码 data0 false = blank)时,
wS 上的接受路径原样落回 encS inst。 -/
theorem r7_accept_falls_back {wS₀ wS : List Sym} {πs : List SymStep} {cfgsEnd : SymConfig}
    (hpre : wS₀ <+: wS)
    (htail : ∀ i : ℕ, wS₀.length ≤ i → i < wS.length →
      wS.getD i Sym.blank = Sym.blank)
    (hπs : SymSteps VerifierSym.transition (symInitialConfig wS) πs cfgsEnd) :
    SymSteps VerifierSym.transition (symInitialConfig wS₀) πs cfgsEnd := by
  rcases hpre with ⟨r, hr⟩
  have hrl : r.length = wS.length - wS₀.length := by
    have : wS.length = wS₀.length + r.length := by
      rw [← hr]
      simp [List.length_append]
    omega
  have hrep : r = List.replicate (wS.length - wS₀.length) Sym.blank := by
    apply List.ext_getElem
    · simp [List.length_replicate]
      exact hrl
    · intro j hj₁ hj₂
      have hpos : wS₀.length ≤ wS₀.length + j := by omega
      have hj' : wS₀.length + j < wS.length := by
        rw [← hr]
        simp [List.length_append] at hj₁ ⊢
        omega
      have hwj : wS.getD (wS₀.length + j) Sym.blank = Sym.blank :=
        htail (wS₀.length + j) hpos hj'
      have hwj' : r[j]'(hj₁) = Sym.blank := by
        rw [← hr] at hwj
        have hgr : (wS₀ ++ r).getD (wS₀.length + j) Sym.blank = r.getD j Sym.blank := by
          simpa [Nat.add_sub_cancel_left] using
            (List.getD_append_right wS₀ r Sym.blank (wS₀.length + j) (by omega))
        have hrg : r.getD j Sym.blank = Sym.blank := by
          rw [← hgr]
          exact hwj
        -- j < |r| ⇒ getD = getElem
        rw [← List.getD_eq_getElem]
        exact hrg
      rw [List.getElem_replicate hj₂]
      exact hwj'
  have hπs' : SymSteps VerifierSym.transition
      (symInitialConfig (wS₀ ++ List.replicate (wS.length - wS₀.length) Sym.blank)) πs cfgsEnd := by
    rw [← hr] at hπs
    rw [hrep] at hπs
    exact hπs
  exact symSteps_blank_tail (wS₀ := wS₀) (m := wS.length - wS₀.length) hπs'

-- =====================================================================
-- 合法输入(三边界符 #ₗ/#₀/#₁)上机器不越左右边界符(用户确立的机器性质)
-- L1:表级分类(读 boundary 后 R 的 fromState 集合)
-- L2:态-位置链 —— Rset 成员的工作区 ≤ #₀/#ₗ(#₁ 前的结构阻挡)
-- 推论:接受路径读位 < |encS| ⇒ no_trap 解码块不超输入 ⇒ 主定理单链组装
-- =====================================================================

/-- 读 (boundary, false) 后 R 的转移:fromState ∈ Rset ∨ next ∈ {100,101}。 -/
theorem r7_boundary_false_R_class (q : ℕ) (s : Sym) (r : SymTransResult)
    (hq : q < 102) (hs : s.1 = SymKind.boundary) (hs2 : s.2 = false)
    (hr : r ∈ VerifierSym.transition (q, s)) (hm : r.moveDir = Dir.R) :
    q = 0 ∨ q = 1 ∨ q = 38 ∨ q = 28 ∨ q = 77 ∨ q = 9 ∨ q = 12 ∨ q = 11 ∨ q = 14 ∨
      q = 81 ∨ q = 85 ∨ q = 20 ∨ q = 23 ∨ r.nextState = 100 ∨ r.nextState = 101 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → s.1 = SymKind.boundary → s.2 = false →
        r.moveDir = Dir.R →
        (q : ℕ) = 0 ∨ (q : ℕ) = 1 ∨ (q : ℕ) = 38 ∨ (q : ℕ) = 28 ∨ (q : ℕ) = 77 ∨
          (q : ℕ) = 9 ∨ (q : ℕ) = 12 ∨ (q : ℕ) = 11 ∨ (q : ℕ) = 14 ∨ (q : ℕ) = 81 ∨
          (q : ℕ) = 85 ∨ (q : ℕ) = 20 ∨ (q : ℕ) = 23 ∨ r.nextState = 100 ∨
          r.nextState = 101 := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr hs hs2 hm

/-- 读 (boundary, true) 后 R 的转移:fromState ∈ Rset' ∨ next ∈ {100,101}。 -/
theorem r7_boundary_true_R_class (q : ℕ) (s : Sym) (r : SymTransResult)
    (hq : q < 102) (hs : s.1 = SymKind.boundary) (hs2 : s.2 = true)
    (hr : r ∈ VerifierSym.transition (q, s)) (hm : r.moveDir = Dir.R) :
    q = 0 ∨ q = 1 ∨ q = 28 ∨ q = 77 ∨ q = 9 ∨ q = 11 ∨ q = 14 ∨ q = 81 ∨ q = 85 ∨
      q = 20 ∨ q = 23 ∨ r.nextState = 100 ∨ r.nextState = 101 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → s.1 = SymKind.boundary → s.2 = true →
        r.moveDir = Dir.R →
        (q : ℕ) = 0 ∨ (q : ℕ) = 1 ∨ (q : ℕ) = 28 ∨ (q : ℕ) = 77 ∨ (q : ℕ) = 9 ∨
          (q : ℕ) = 11 ∨ (q : ℕ) = 14 ∨ (q : ℕ) = 81 ∨ (q : ℕ) = 85 ∨ (q : ℕ) = 20 ∨
          (q : ℕ) = 23 ∨ r.nextState = 100 ∨ r.nextState = 101 := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr hs hs2 hm

-- ---------------------------------------------------------------------
-- L3'' 块 1:表级引理组(态-位置链的输入)
-- ---------------------------------------------------------------------

/-- 格式态集合(0-38 分支/格式段)的定义谓词。 -/
def r7_fmtState (q : ℕ) : Prop :=
  q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 24 ∨ q = 26 ∨ q = 27 ∨ q = 28 ∨ q = 29 ∨ q = 38

/-- 格式态分离:处理态(q ∉ Fmt)的转移不回到格式态。
    路径 = 初始格式段 + 处理段;格式态只出现在路径开头(consumed/sel 等
    运行时标记只由处理段状态 5/2 之外写,故格式段扫描看到的是初始结构)。 -/
theorem r7_fmt_state_closed {q : ℕ} (hq : q < 102) {s : Sym} {r : SymTransResult}
    (hr : r ∈ VerifierSym.transition (q, s)) :
    ¬ r7_fmtState q → ¬ r7_fmtState r.nextState := by
  intro hqf hnf
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) →
        ¬ ((q : ℕ) = 0 ∨ (q : ℕ) = 1 ∨ (q : ℕ) = 2 ∨ (q : ℕ) = 3 ∨ (q : ℕ) = 24 ∨
          (q : ℕ) = 26 ∨ (q : ℕ) = 27 ∨ (q : ℕ) = 28 ∨ (q : ℕ) = 29 ∨ (q : ℕ) = 38) →
        ¬ (r.nextState = 0 ∨ r.nextState = 1 ∨ r.nextState = 2 ∨ r.nextState = 3 ∨
          r.nextState = 24 ∨ r.nextState = 26 ∨ r.nextState = 27 ∨ r.nextState = 28 ∨
          r.nextState = 29 ∨ r.nextState = 38) := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr hqf hnf

/-- consumed kind 的写:读的格已非 consumed 时写者必为 q = 5(新产生 consumed);
    读 consumed 的转移(81/13/76/8/84/100/101)只可能重写同 kind(如 81 重置 mark)。 -/
theorem r7_consumed_writer_only_5 (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (hns : s.1 ≠ SymKind.consumed)
    (hc : (r.writeSym).1 = SymKind.consumed) :
    q = 5 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → s.1 ≠ SymKind.consumed →
        (r.writeSym).1 = SymKind.consumed → (q : ℕ) = 5 := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr hns hc

/-- sel/nosel kind 的写:读的格已非 sel/nosel 时写者必为 q = 2(读 α 元素头);
    21/51/100/101 读 sel/nosel 只写同 kind。 -/
theorem r7_sel_nosel_writer_only_2 (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s))
    (hns : s.1 ≠ SymKind.sel ∧ s.1 ≠ SymKind.nosel)
    (hc : (r.writeSym).1 = SymKind.sel ∨ (r.writeSym).1 = SymKind.nosel) :
    q = 2 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → s.1 ≠ SymKind.sel → s.1 ≠ SymKind.nosel →
        (r.writeSym).1 = SymKind.sel ∨ (r.writeSym).1 = SymKind.nosel → (q : ℕ) = 2 := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr hns.1 hns.2 hc

/-- 进 81 的转移:fromState ∈ {11,12,14,81}(自 R 穿)或 101。 -/
theorem r7_into_81_class (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h81 : r.nextState = 81) :
    q = 11 ∨ q = 12 ∨ q = 14 ∨ q = 81 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 81 →
        (q : ℕ) = 11 ∨ (q : ℕ) = 12 ∨ (q : ℕ) = 14 ∨ (q : ℕ) = 81 := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr h81

/-- 读 (boundary, true)(#₁ 格式后)写同值:边界格内容只可能被 20 改写(data0 清除,
    20@#₁ 由位置链排除——87 的扫描在 #₀' 停)或 3(格式段标 m)。 -/
theorem r7_boundary_true_write_self (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s))
    (hs : s.1 = SymKind.boundary) (hs2 : s.2 = true) :
    r.writeSym = s ∨ q = 3 ∨ q = 20 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → s.1 = SymKind.boundary → s.2 = true →
        r.writeSym = s ∨ (q : ℕ) = 3 ∨ (q : ℕ) = 20 := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr hs hs2

/-- 写 boundary 的转移:q = 51(新 #₀',读 data0 于元素末位)或 q = 3(#₁ 标 m=1)。
    (51 的写位 = 51 的读位 = 元素末位——由 21 读 sel 后 51 的 L 定位。) -/
theorem r7_boundary_writer_class (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (hb : (r.writeSym).1 = SymKind.boundary)
    (hne : r.writeSym ≠ s) :
    q = 51 ∨ q = 3 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → (r.writeSym).1 = SymKind.boundary →
        r.writeSym ≠ s → (q : ℕ) = 51 ∨ (q : ℕ) = 3 := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr hb hne


-- 自证 getD_append_left(变量级,证法稳定;mathlib 无此名定理)
lemma r7_getD_append_left {α : Type} (l l' : List α) (d : α) (n : ℕ) (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  rw [List.getD_eq_getElem (l ++ l') d (by simp [List.length_append]; omega)]
  rw [List.getElem_append_left h]
  rw [← List.getD_eq_getElem]

-- encS 的左结合段(与 Core:218 定义体的 AST 一致:(([b]++bits)++[b])++elems++[b])
-- X₂ = [b] ++ bits;X₁ = X₂ ++ [b];X₀ = X₁ ++ elems;l = X₀ ++ [b]

/-- encS 的长度分解:L = |bits| + |elems| + 3。 -/
lemma r7_enc_len (inst : SubsetSumInstance) :
    (encodeInstanceSym inst).length =
      (encodeBitsSym inst.target).length + (encodeElementsSym inst.elements).length + 3 := by
  unfold encodeInstanceSym
  simp [List.length_append]
  omega

/-- 位置 0 = #ₗ(左边界符)。 -/
lemma r7_enc_getD_0 (inst : SubsetSumInstance) :
    (encodeInstanceSym inst).getD 0 Sym.blank = Sym.boundary := by
  unfold encodeInstanceSym
  rfl

/-- #₀(中边界符)在 |bits|+1。 -/
lemma r7_enc_getD_mid (inst : SubsetSumInstance) :
    (encodeInstanceSym inst).getD ((encodeBitsSym inst.target).length + 1) Sym.blank =
      Sym.boundary := by
  unfold encodeInstanceSym
  let X₂ : List Sym := [Sym.boundary] ++ encodeBitsSym inst.target
  let X₁ : List Sym := X₂ ++ [Sym.boundary]
  let X₀ : List Sym := X₁ ++ encodeElementsSym inst.elements
  change (X₀ ++ [Sym.boundary]).getD ((encodeBitsSym inst.target).length + 1) Sym.blank =
    Sym.boundary
  have hL₀ : (encodeBitsSym inst.target).length + 1 < X₀.length := by
    dsimp [X₀, X₁, X₂]
    simp [List.length_append]
  have hL₁ : (encodeBitsSym inst.target).length + 1 < X₁.length := by
    dsimp [X₁, X₂]
    simp [List.length_append]
  have hR : X₂.length ≤ (encodeBitsSym inst.target).length + 1 := by
    dsimp [X₂]
    simp [List.length_append]
  calc
    (X₀ ++ [Sym.boundary]).getD ((encodeBitsSym inst.target).length + 1) Sym.blank
        = X₀.getD ((encodeBitsSym inst.target).length + 1) Sym.blank := by
            exact r7_getD_append_left X₀ [Sym.boundary] Sym.blank
              ((encodeBitsSym inst.target).length + 1) hL₀
    _ = X₁.getD ((encodeBitsSym inst.target).length + 1) Sym.blank := by
            exact r7_getD_append_left X₁ (encodeElementsSym inst.elements) Sym.blank
              ((encodeBitsSym inst.target).length + 1) hL₁
    _ = [Sym.boundary].getD
          ((encodeBitsSym inst.target).length + 1 - X₂.length) Sym.blank := by
            exact List.getD_append_right X₂ [Sym.boundary] Sym.blank
              ((encodeBitsSym inst.target).length + 1) hR
    _ = [Sym.boundary].getD 0 Sym.blank := by
            congr 1 <;> dsimp [X₂] <;> simp [List.length_append]
    _ = Sym.boundary := rfl

/-- #₁(右边界符)在最后:位置 L-1。 -/
lemma r7_enc_getD_last (inst : SubsetSumInstance) :
    (encodeInstanceSym inst).getD ((encodeInstanceSym inst).length - 1) Sym.blank =
      Sym.boundary := by
  unfold encodeInstanceSym
  let X₂ : List Sym := [Sym.boundary] ++ encodeBitsSym inst.target
  let X₁ : List Sym := X₂ ++ [Sym.boundary]
  let X₀ : List Sym := X₁ ++ encodeElementsSym inst.elements
  change (X₀ ++ [Sym.boundary]).getD
    (((X₀ ++ [Sym.boundary]).length) - 1) Sym.blank = Sym.boundary
  have hR : X₀.length ≤ ((X₀ ++ [Sym.boundary]).length) - 1 := by
    dsimp [X₀, X₁, X₂]
    simp [List.length_append]
  calc
    (X₀ ++ [Sym.boundary]).getD (((X₀ ++ [Sym.boundary]).length) - 1) Sym.blank
        = [Sym.boundary].getD (((X₀ ++ [Sym.boundary]).length) - 1 - X₀.length) Sym.blank := by
            exact List.getD_append_right X₀ [Sym.boundary] Sym.blank
              (((X₀ ++ [Sym.boundary]).length) - 1) hR
    _ = [Sym.boundary].getD 0 Sym.blank := by
            congr 1 <;> dsimp [X₀, X₁, X₂] <;> simp [List.length_append] <;> omega
    _ = Sym.boundary := rfl

/-- target 区(格 1..|bits|)无 boundary。 -/
lemma r7_enc_getD_bits_kind (inst : SubsetSumInstance) {j : ℕ}
    (hj : j < (encodeBitsSym inst.target).length) :
    ((encodeInstanceSym inst).getD (1 + j) Sym.blank).1 ≠ SymKind.boundary := by
  unfold encodeInstanceSym
  let X₂ : List Sym := [Sym.boundary] ++ encodeBitsSym inst.target
  let X₁ : List Sym := X₂ ++ [Sym.boundary]
  let X₀ : List Sym := X₁ ++ encodeElementsSym inst.elements
  change ((X₀ ++ [Sym.boundary]).getD (1 + j) Sym.blank).1 ≠ SymKind.boundary
  have hL₀ : 1 + j < X₀.length := by
    dsimp [X₀, X₁, X₂]
    simp [List.length_append]
    omega
  have hL₁ : 1 + j < X₁.length := by
    dsimp [X₁, X₂]
    simp [List.length_append]
    omega
  have hL₂ : 1 + j < X₂.length := by
    dsimp [X₂]
    simp [List.length_append]
    omega
  have hR : [Sym.boundary].length ≤ 1 + j := by
    simp
  have hcell : (X₀ ++ [Sym.boundary]).getD (1 + j) Sym.blank =
      (encodeBitsSym inst.target).getD j Sym.blank := by
    calc
      (X₀ ++ [Sym.boundary]).getD (1 + j) Sym.blank
          = X₀.getD (1 + j) Sym.blank := by
              exact r7_getD_append_left X₀ [Sym.boundary] Sym.blank (1 + j) hL₀
      _ = X₁.getD (1 + j) Sym.blank := by
              exact r7_getD_append_left X₁ (encodeElementsSym inst.elements) Sym.blank (1 + j) hL₁
      _ = X₂.getD (1 + j) Sym.blank := by
              exact r7_getD_append_left X₂ [Sym.boundary] Sym.blank (1 + j) hL₂
      _ = (encodeBitsSym inst.target).getD ((1 + j) - [Sym.boundary].length) Sym.blank := by
              exact List.getD_append_right [Sym.boundary] (encodeBitsSym inst.target)
                Sym.blank (1 + j) hR
      _ = (encodeBitsSym inst.target).getD j Sym.blank := by
              congr 1 <;> simp
  rw [hcell]
  rw [List.getD_eq_getElem (encodeBitsSym inst.target) Sym.blank hj]
  have hk := encodeBitsSym_nonboundary inst.target (GetElem.getElem (encodeBitsSym inst.target) j hj)
    (List.getElem_mem hj)
  rcases hk with hk | hk <;> simp [hk]

/-- 元素区(格 |bits|+2 起)无 boundary(元素区在 #₁ 左,不含边界符)。 -/
lemma r7_enc_getD_elems_kind (inst : SubsetSumInstance) {j : ℕ}
    (hj : j < (encodeElementsSym inst.elements).length) :
    ((encodeInstanceSym inst).getD ((encodeBitsSym inst.target).length + 2 + j) Sym.blank).1 ≠
      SymKind.boundary := by
  unfold encodeInstanceSym
  let X₂ : List Sym := [Sym.boundary] ++ encodeBitsSym inst.target
  let X₁ : List Sym := X₂ ++ [Sym.boundary]
  let X₀ : List Sym := X₁ ++ encodeElementsSym inst.elements
  change ((X₀ ++ [Sym.boundary]).getD ((encodeBitsSym inst.target).length + 2 + j) Sym.blank).1 ≠
    SymKind.boundary
  have hL₀ : (encodeBitsSym inst.target).length + 2 + j < X₀.length := by
    dsimp [X₀, X₁, X₂]
    simp [List.length_append]
    omega
  have hR : X₁.length ≤ (encodeBitsSym inst.target).length + 2 + j := by
    dsimp [X₁, X₂]
    simp [List.length_append]
  have hcell : (X₀ ++ [Sym.boundary]).getD ((encodeBitsSym inst.target).length + 2 + j) Sym.blank =
      (encodeElementsSym inst.elements).getD j Sym.blank := by
    calc
      (X₀ ++ [Sym.boundary]).getD ((encodeBitsSym inst.target).length + 2 + j) Sym.blank
          = X₀.getD ((encodeBitsSym inst.target).length + 2 + j) Sym.blank := by
              exact r7_getD_append_left X₀ [Sym.boundary] Sym.blank
                ((encodeBitsSym inst.target).length + 2 + j) hL₀
      _ = (encodeElementsSym inst.elements).getD
            ((encodeBitsSym inst.target).length + 2 + j - X₁.length) Sym.blank := by
              exact List.getD_append_right X₁ (encodeElementsSym inst.elements) Sym.blank
                ((encodeBitsSym inst.target).length + 2 + j) hR
      _ = (encodeElementsSym inst.elements).getD j Sym.blank := by
              congr 1 <;> dsimp [X₁, X₂] <;> simp [List.length_append]
  rw [hcell]
  rw [List.getD_eq_getElem (encodeElementsSym inst.elements) Sym.blank hj]
  exact encodeElementsSym_nonboundary (encodeBitsSym inst.target).length inst.elements
    (GetElem.getElem (encodeElementsSym inst.elements) j hj)
    (List.getElem_mem hj)

-- ---------------------------------------------------------------------
-- L3'' 块 3a:表级分类(状态集 A/B/终态闭合 + 101 吸收)——位置链归纳的输入
-- ---------------------------------------------------------------------

/-- A 区状态(工作区 ≤ #₀ 位置 |bits|+1):target 区定位/减法/清计数。
    (格式检查 24/26/29 扫元素区,属 B。) -/
abbrev r7_AState (q : ℕ) : Prop :=
  q = 0 ∨ q = 1 ∨ q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 12 ∨ q = 14 ∨ q = 27 ∨ q = 28 ∨
    q = 38 ∨ q = 77 ∨ q = 85 ∨ q = 86 ∨ q = 87

/-- B 区状态(工作区 ≤ #₁):元素处理 + 格式检查 + 判定扫描。 -/
abbrev r7_BState (q : ℕ) : Prop :=
  q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 8 ∨ q = 13 ∨ q = 20 ∨ q = 21 ∨ q = 22 ∨ q = 23 ∨
    q = 24 ∨ q = 26 ∨ q = 29 ∨ q = 51 ∨ q = 76 ∨ q = 81 ∨ q = 84

/-- 合法状态集:A ∪ B ∪ 终态。 -/
abbrev r7_legalState (q : ℕ) : Prop :=
  r7_AState q ∨ r7_BState q ∨ q = 100 ∨ q = 101

/-- 101 吸收:101 的转移 nextState 恒 101。 -/
theorem r7_101_absorb (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h101 : q = 101) :
    r.nextState = 101 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 101 → r.nextState = 101 := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr h101

/-- 状态集闭合:合法工作区(A ∪ B)与终态 {100,101} 的转移不越出。
    (机器设计:任何非终态的转移目标仍是非终态工作区或终态。) -/
theorem r7_state_set_closed (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s))
    (hAB : r7_AState q ∨ r7_BState q) :
    r7_legalState r.nextState := by
  have hbbA : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) →
        r7_AState (q : ℕ) → r7_legalState r.nextState := by
    native_decide
  have hbbB : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) →
        r7_BState (q : ℕ) → r7_legalState r.nextState := by
    native_decide
  rcases hAB with hA | hB
  · exact hbbA ⟨q, hq⟩ s r hr hA
  · exact hbbB ⟨q, hq⟩ s r hr hB

/-- A 区状态读 boundary 的转移:next ∈ A ∪ B ∪ {100,101}
    (A 区状态读到 boundary 即 #ₗ/#₀,转入 B 或拒绝/接受,不产生其它 A 态漂移)。 -/
theorem r7_A_read_boundary_class (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s))
    (hA : r7_AState q) (hd : s.1 = SymKind.boundary) :
    r7_legalState r.nextState := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) →
        r7_AState (q : ℕ) → s.1 = SymKind.boundary → r7_legalState r.nextState := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr hA hd

/-- 非空元素列表的编码头部是 α。 -/
lemma r7_elems_head_alpha {elems : List ℕ}
    (hm : 0 < (encodeElementsSym elems).length) :
    (encodeElementsSym elems).getD 0 Sym.blank = Sym.alpha := by
  cases elems with
  | nil => simp [encodeElementsSym] at hm
  | cons hd tl =>
      cases tl with
      | nil =>
          change ([Sym.alpha] ++ encodeBitsSymNative hd).getD 0 Sym.blank = Sym.alpha
          rfl
      | cons v rest =>
          change ([Sym.alpha] ++ encodeBitsSymNative hd ++ encodeElementsSym rest).getD 0 Sym.blank =
            Sym.alpha
          rfl

/-- 元素区首格(位置 |bits|+2)是 α(分支符)——81 穿 #₀ 后读格分类用。 -/
lemma r7_enc_getD_elem_first (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length) :
    (encodeInstanceSym inst).getD ((encodeBitsSym inst.target).length + 2) Sym.blank =
      Sym.alpha := by
  unfold encodeInstanceSym
  let X₂ : List Sym := [Sym.boundary] ++ encodeBitsSym inst.target
  let X₁ : List Sym := X₂ ++ [Sym.boundary]
  let X₀ : List Sym := X₁ ++ encodeElementsSym inst.elements
  change (X₀ ++ [Sym.boundary]).getD ((encodeBitsSym inst.target).length + 2) Sym.blank =
    Sym.alpha
  have hL : (encodeBitsSym inst.target).length + 2 < X₀.length := by
    dsimp [X₀, X₁, X₂]
    simp [List.length_append]
    omega
  have hR : X₁.length ≤ (encodeBitsSym inst.target).length + 2 := by
    dsimp [X₁, X₂]
    simp [List.length_append]
  calc
    (X₀ ++ [Sym.boundary]).getD ((encodeBitsSym inst.target).length + 2) Sym.blank
        = X₀.getD ((encodeBitsSym inst.target).length + 2) Sym.blank := by
            exact r7_getD_append_left X₀ [Sym.boundary] Sym.blank
              ((encodeBitsSym inst.target).length + 2) hL
    _ = (encodeElementsSym inst.elements).getD
          ((encodeBitsSym inst.target).length + 2 - X₁.length) Sym.blank := by
            exact List.getD_append_right X₁ (encodeElementsSym inst.elements) Sym.blank
              ((encodeBitsSym inst.target).length + 2) hR
    _ = (encodeElementsSym inst.elements).getD 0 Sym.blank := by
            congr 1 <;> dsimp [X₁, X₂] <;> simp [List.length_append]
    _ = Sym.alpha := r7_elems_head_alpha hm

/-- 81 读元素区首格类(α/sel/nosel)必 101 S 停(缺省臂)——81 永不深入元素区。 -/
theorem r7_81_elemfirst_class (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (81, s))
    (hs : s.1 = SymKind.alpha ∨ s.1 = SymKind.sel ∨ s.1 = SymKind.nosel) :
    r.nextState = 101 ∧ r.moveDir = Dir.S := by
  have hbb : ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (81, s) →
        (s.1 = SymKind.alpha ∨ s.1 = SymKind.sel ∨ s.1 = SymKind.nosel) →
          r.nextState = 101 ∧ r.moveDir = Dir.S := by
    native_decide
  exact hbb s r hr hs

/-- A 区状态的入边分类:源 ∈ A(移动 R/L/S),或来自 B 的边界跨越 8/76/26/84(L)。 -/
abbrev r7_AsrcSet : Finset ℕ := {0, 1, 9, 10, 11, 12, 14, 27, 28, 38, 77, 85, 86, 87, 8, 76, 26, 84}

theorem r7_into_A_class (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (hnext : r7_AState r.nextState) :
    q ∈ r7_AsrcSet := by
  have hbb0 : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 0 → False := by native_decide
  have hbb1 : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 1 → (q : ℕ) = 0 ∨ (q : ℕ) = 1 := by
    native_decide
  have hbb9 : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 9 → (q : ℕ) = 8 ∨ (q : ℕ) = 9 := by
    native_decide
  have hbb10 : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 10 → (q : ℕ) = 77 ∨ (q : ℕ) = 10 := by
    native_decide
  have hbb11 : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 11 → (q : ℕ) = 10 := by
    native_decide
  have hbb12 : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 12 → (q : ℕ) = 9 ∨ (q : ℕ) = 12 := by
    native_decide
  have hbb14 : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 14 → (q : ℕ) = 11 ∨ (q : ℕ) = 14 := by
    native_decide
  have hbb27 : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 27 → (q : ℕ) = 26 := by
    native_decide
  have hbb28 : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 28 → (q : ℕ) = 38 ∨ (q : ℕ) = 28 := by
    native_decide
  have hbb38 : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 38 → (q : ℕ) = 27 ∨ (q : ℕ) = 38 := by
    native_decide
  have hbb77 : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 77 → (q : ℕ) = 76 ∨ (q : ℕ) = 77 := by
    native_decide
  have hbb85 : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 85 → (q : ℕ) = 84 ∨ (q : ℕ) = 85 := by
    native_decide
  have hbb86 : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 86 → (q : ℕ) = 85 ∨ (q : ℕ) = 86 := by
    native_decide
  have hbb87 : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 87 → (q : ℕ) = 86 ∨ (q : ℕ) = 87 := by
    native_decide
  rcases hnext with h0 | h1 | h9 | h10 | h11 | h12 | h14 | h27 | h28 | h38 | h77 | h85 | h86 | h87
  · exfalso; exact hbb0 ⟨q, hq⟩ s r hr h0
  · rcases hbb1 ⟨q, hq⟩ s r hr h1 with hq0 | hq1
    · rw [show q = 0 from hq0]; native_decide
    · rw [show q = 1 from hq1]; native_decide
  · rcases hbb9 ⟨q, hq⟩ s r hr h9 with hq8 | hq9
    · rw [show q = 8 from hq8]; decide
    · rw [show q = 9 from hq9]; decide
  · rcases hbb10 ⟨q, hq⟩ s r hr h10 with hq77 | hq10
    · rw [show q = 77 from hq77]; decide
    · rw [show q = 10 from hq10]; decide
  · rw [show q = 10 from hbb11 ⟨q, hq⟩ s r hr h11]; decide
  · rcases hbb12 ⟨q, hq⟩ s r hr h12 with hq9 | hq12
    · rw [show q = 9 from hq9]; decide
    · rw [show q = 12 from hq12]; decide
  · rcases hbb14 ⟨q, hq⟩ s r hr h14 with hq11 | hq14
    · rw [show q = 11 from hq11]; decide
    · rw [show q = 14 from hq14]; decide
  · rw [show q = 26 from hbb27 ⟨q, hq⟩ s r hr h27]; decide
  · rcases hbb28 ⟨q, hq⟩ s r hr h28 with hq38 | hq28
    · rw [show q = 38 from hq38]; decide
    · rw [show q = 28 from hq28]; decide
  · rcases hbb38 ⟨q, hq⟩ s r hr h38 with hq27 | hq38
    · rw [show q = 27 from hq27]; decide
    · rw [show q = 38 from hq38]; decide
  · rcases hbb77 ⟨q, hq⟩ s r hr h77 with hq76 | hq77
    · rw [show q = 76 from hq76]; decide
    · rw [show q = 77 from hq77]; decide
  · rcases hbb85 ⟨q, hq⟩ s r hr h85 with hq84 | hq85
    · rw [show q = 84 from hq84]; decide
    · rw [show q = 85 from hq85]; decide
  · rcases hbb86 ⟨q, hq⟩ s r hr h86 with hq85 | hq86
    · rw [show q = 85 from hq85]; decide
    · rw [show q = 86 from hq86]; decide
  · rcases hbb87 ⟨q, hq⟩ s r hr h87 with hq86 | hq87
    · rw [show q = 86 from hq86]; decide
    · rw [show q = 87 from hq87]; decide

-- ---------------------------------------------------------------------
-- L3'' 块 3c:主体(联合归纳 P0'/P2/P5/P6/P9)——位置链核心
-- ---------------------------------------------------------------------

/-- 100 吸收:nextState 恒 100 且 moveDir = S。 -/
theorem r7_100_absorb (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h100 : q = 100) :
    r.nextState = 100 ∧ r.moveDir = Dir.S := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 100 →
        r.nextState = 100 ∧ r.moveDir = Dir.S := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr h100

/-- 101 吸收 + S。 -/
theorem r7_101_absorb_move (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h101 : q = 101) :
    r.nextState = 101 ∧ r.moveDir = Dir.S := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → (q : ℕ) = 101 →
        r.nextState = 101 ∧ r.moveDir = Dir.S := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr h101

/-- 写 boundary 的转移:读格必为 boundary(保 kind),或 q = 51(新 #₀)。 -/
theorem r7_write_boundary_class (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (hw : (r.writeSym).1 = SymKind.boundary) :
    s.1 = SymKind.boundary ∨ q = 51 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → (r.writeSym).1 = SymKind.boundary →
        s.1 = SymKind.boundary ∨ (q : ℕ) = 51 := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr hw

/-- 20 入边:87 S(87 头 ≤ 当前 #₀ ≤ L-2)或 4 L(4 读 nosel,头 ≤ L-3)。 -/
theorem r7_into_20_class (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h20 : r.nextState = 20) :
    (q = 87 ∧ r.moveDir = Dir.S) ∨ (q = 4 ∧ r.moveDir = Dir.L) := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 20 →
        ((q : ℕ) = 87 ∧ r.moveDir = Dir.S) ∨ ((q : ℕ) = 4 ∧ r.moveDir = Dir.L) := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr h20

/-- 22 入边唯 21 S(22 头 = 21 头 = L-1,#₁ 上判定)。 -/
theorem r7_into_22_class (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h22 : r.nextState = 22) :
    q = 21 ∧ r.moveDir = Dir.S := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 22 →
        (q : ℕ) = 21 ∧ r.moveDir = Dir.S := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr h22

/-- A 状态读 boundary 且 moveDir = R 的转移:q ∈ 边界读集合,或 next ∈ {100,101}。 -/
abbrev r7_AboundSet : Finset ℕ := {0, 1, 9, 38, 77, 85, 28, 12, 11, 14}

theorem r7_A_boundary_R_class (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s))
    (hA : r7_AState q) (hd : s.1 = SymKind.boundary) (hR : r.moveDir = Dir.R) :
    q ∈ r7_AboundSet ∨ r.nextState = 100 ∨ r.nextState = 101 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) →
        r7_AState (q : ℕ) → s.1 = SymKind.boundary → r.moveDir = Dir.R →
          ((q : ℕ) ∈ r7_AboundSet ∨ r.nextState = 100 ∨ r.nextState = 101) := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr hA hd hR

/-- legalStates 闭:合法状态的转移目标仍合法。 -/
theorem r7_transition_legal_closed (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hlegal : q ∈ legalStates) (hr : r ∈ VerifierSym.transition (q, s)) :
    r.nextState ∈ legalStates := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → ((q : ℕ) ∈ legalStates) →
        decide (r.nextState ∈ legalStates) = true := by
    native_decide
  exact of_decide_eq_true (hbb ⟨q, hq⟩ s r hr hlegal)

/-- 路径状态恒 ∈ legalStates。 -/
theorem r7_path_state_legal (input : List Sym) (π : List SymStep) (cfg : SymConfig)
    (h : SymReachablePath VerifierSym.transition input π cfg) : cfg.state ∈ legalStates := by
  induction h with
  | nil => simp [symInitialConfig, legalStates]
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      exact r7_transition_legal_closed cfg'.state (q12_path_state_lt102 input π₀ cfg' hprev)
        step.readSym step.result ih (by simpa [hread] using htrans)

/-- legalStates 内状态 ∈ legal(A ∪ B ∪ 终态)。 -/
theorem r7_all_legal (q : ℕ) (hq : q ∈ legalStates) : r7_legalState q := by
  have hbb : ∀ q : Fin 102, ((q : ℕ) ∈ legalStates) → decide (r7_legalState (q : ℕ)) = true := by
    native_decide
  have hsub : legalStates ⊆ Finset.range 102 := by
    native_decide
  have hfin : q < 102 := Finset.mem_range.mp (hsub hq)
  exact of_decide_eq_true (hbb ⟨q, hfin⟩ hq)

/-- 1 入边:0@#ₗ R 或 1 读 data R 自环。 -/
theorem r7_into_1_class (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h1 : r.nextState = 1) :
    q = 0 ∨ q = 1 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 1 → (q : ℕ) = 0 ∨ (q : ℕ) = 1 := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr h1

/-- 28 入边:38@#ₗ R 或 28 读 data R 自环。 -/
theorem r7_into_28_class (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h28 : r.nextState = 28) :
    q = 38 ∨ q = 28 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 28 → (q : ℕ) = 38 ∨ (q : ℕ) = 28 := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr h28

/-- 87 入边:86 S(读 data false 或 boundary false),或 87 读 data R 自环。 -/
theorem r7_into_87_class (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h87 : r.nextState = 87) :
    (q = 86 ∧ r.moveDir = Dir.S) ∨ (q = 87 ∧ r.moveDir = Dir.R) := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 87 →
        ((q : ℕ) = 86 ∧ r.moveDir = Dir.S) ∨ ((q : ℕ) = 87 ∧ r.moveDir = Dir.R) := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr h87

/-- 23 入边:22@#₁ L 或 23 读 data0 L 自环。 -/
theorem r7_into_23_class (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h23 : r.nextState = 23) :
    q = 22 ∨ q = 23 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 23 → (q : ℕ) = 22 ∨ (q : ℕ) = 23 := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr h23

/-- 86 入边:85@#ₗ R 或 86 读 data true R 自环。 -/
theorem r7_into_86_class (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h86 : r.nextState = 86) :
    q = 85 ∨ q = 86 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 86 → (q : ℕ) = 85 ∨ (q : ℕ) = 86 := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr h86

end Mp
