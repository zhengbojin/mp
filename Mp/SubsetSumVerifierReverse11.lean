import Mp.SubsetSumVerifierStepBound
import Mp.SubsetSumCompile
import Mp.SubsetSumVerifierCBTM3      -- GoodBlock / GoodBlockPath（块级几何）
import Mp.SubsetSumVerifierReverse10  -- tapeSteps_prefix_headPos_drift / iso_path_forward_noCan
import Mp.SubsetSumVerifierL3a        -- l3a_goodblock_read_im_classify（块内标记读分类）
import Mp.SubsetSumVerifierCBTM6      -- accept_path_is_good_block_path
import Mp.SubsetSumVerifierPosBound   -- subsetSumIso（NTM2→CBTM 同构实例）
import Mp.SubsetSumVerifierPosBound4  -- a2p 片（初始几何：a2p_bits_native_kind / a2p_enc_elems_getD）

/-!
# [q10 主证明 2/2] `NTM2.Canonical subsetSumNTM2` 装配件

本文件承接 `SubsetSumVerifierReverse10.lean`（q10 = 1/2：CBTM 层 (a) 机制 + 路径桥）。

## δ-18：(b) fork 唯一性 —— 「同一位置至多被读一次分支」

`NTM2.Canonical` 第二枚断句的判据是 `im readSym`，在 Sym 层即 **`Sym.isBranch`**
（α/β，`SymKind.isBranch = decide (k = alpha ∨ k = beta)`），**不是** `symIsMarkedRead`
（`= s.2`，4F4.4 位号）—— 两者不同，勿混。

## 已落库

地基 7 件：`symSteps_prefix_cfg` / `symStepConfig_tape_head` / `symStepConfig_tape_ne` /
`symStep_write_not_branch` / `symSteps_snoc_decomp` / `symSteps_singleton_facts` /
`symTake_succ_eq_snoc`；列表小工具 `symTake_add_eq_take_append`。

**本体**：`symSteps_branchRead_pos_ne` —— 若第 `j` 步在位置 `p` 读到分支（α/β），
则任意更早的步都不可能停在同一格 ⇒ 分支读步位置互异。证法：步 `i` 在 `p` 写出的
符号非分支（`symSteps_writeSym_nonbranch`，力量来源 = 「可延拓到 accept」⇒ 无
101/100 步）⇒ 由 `symSteps_tape_branch_mono` 沿中段传递 ⇒ 步 `j` 之前 `p` 处仍
非分支 ⇒ 与「步 `j` 正是在 `p` 处读到分支」矛盾 ∎
注：结论比 (b) 所需更强 —— **不需要**「步 `i` 也是分支读」这一前提。

## 反演惯用法（本文件全部证明依赖）

`SymSteps` 构造子是 **snoc 形**（`π ++ [step]`），索引含 `append` ⇒ Lean 的
dependent elimination **不反演**。一律走
`symSteps_append_split`（拆到单步）+ `symSteps_singleton_facts`（单步形态）。

## δ-19-12：(W) 块级放电 —— 块内每步写值恒 `im = false`

`(W)` =「路径上每一步写出的符号 `im = false`」，是第二枚断句（`F4.im readSym` 位置互异，
经 `ntm2_branchRead_pos_fresh`）的**唯一路径级前提**。块级放电（`goodBlock_write_im_false`）：

- 非标记读 ⇒ 表级 `transition4_write_im_false`；
- 标记读 ⇒ 相位 8-11 会写回原标记符号（唯一危险支）⇒ 由块内标记读分类
  `l3a_goodblock_read_im_classify`（`im-true` 读只可能是第 3 步）排除到第 3 步，
  而第 3 步写值被 `GoodBlock` 钉住为 `(symTo4F4 r.writeSym).getLastD`，
  再由 `hw_nb`（写符号非分支）收口。

剩余（δ-19-13 装配）：按块实例化三前提 —— `hrs`（块内无 101 步，来自「可延拓到 accept」）、
`hprev_nb`（`[F2]`，`symSteps_left_neighbour_nonbranch`）、`hw_nb`（`[F1]`，
`symSteps_writeSym_nonbranch`）—— 走 Sym 投影（`project_path`）取得，再经
`iso_path_forward_noCan` 回到 NTM2 路径 π。
-/

open Mp

/-- [δ-18-1] 前缀配置存在：存在 `cfgₖ`（`take k` 的终点 = `drop k` 的起点），
    且 `cfgₖ.headPos = symEnd cfg₀.headPos (π.take k)`（位置表口径）。 -/
lemma symSteps_prefix_cfg {M : ℕ × Sym → Finset SymTransResult} {cfg₀ cfg : SymConfig}
    {π : List SymStep} (h : SymSteps M cfg₀ π cfg) (k : ℕ) :
    ∃ cfgₖ : SymConfig,
      SymSteps M cfg₀ (π.take k) cfgₖ ∧ SymSteps M cfgₖ (π.drop k) cfg ∧
      cfgₖ.headPos = symEnd cfg₀.headPos (π.take k) := by
  have h' : π.take k ++ π.drop k = π := List.take_append_drop k π
  obtain ⟨cfgₖ, h1, h2⟩ := symSteps_append_split (M := M) (cfg₀ := cfg₀) (cfg' := cfg)
    (π₀ := π.take k) (rest := π.drop k) (by rw [h']; exact h)
  refine ⟨cfgₖ, h1, h2, ?_⟩
  rw [symSteps_headPos_eq M h1, symEnd_eq_headPos_sum]

/-- [δ-18-2] 步后写格值：写头位置处的新格值 = `writeSym`。 -/
lemma symStepConfig_tape_head (cfg : SymConfig) (r : SymTransResult) :
    (symStepConfig cfg r).tape cfg.headPos = r.writeSym := by
  simp [symStepConfig]

/-- [δ-18-3] 步后非头位置格值不变。 -/
lemma symStepConfig_tape_ne {cfg : SymConfig} {r : SymTransResult} {p : ℤ}
    (hp : p ≠ cfg.headPos) :
    (symStepConfig cfg r).tape p = cfg.tape p := by
  simp [symStepConfig, hp]

/-- [δ-18-4] 点式非分支：合法状态下、非 101/100 的合法转移，写出的符号非分支。 -/
lemma symStep_write_not_branch {cfg : SymConfig} {st : SymStep}
    (hleg : cfg.state ∈ VerifierSym.legalStates)
    (hfrom : st.fromState = cfg.state) (hread : st.readSym = cfg.tape cfg.headPos)
    (htrans : st.result ∈ VerifierSym.transition (cfg.state, cfg.tape cfg.headPos))
    (hrs : st.result.nextState ≠ 101) (hqne : st.fromState ≠ 100) :
    ¬ Sym.isBranch st.result.writeSym := by
  have htr : st.result ∈ VerifierSym.transition (st.fromState, st.readSym) := by
    rw [hfrom, hread]
    exact htrans
  exact symTransition_write_not_branch st.fromState st.readSym st.result
    (by rw [hfrom]; exact hleg) htr hrs hqne

/-- [δ-18-5] snoc 步分解：`π₀ ++ [st]` 的终点 = `symStepConfig cfg₁ st.result`（`cfg₁` = 前缀终点）。 -/
lemma symSteps_snoc_decomp {M : ℕ × Sym → Finset SymTransResult} {cfg₀ cfg' : SymConfig}
    {π₀ : List SymStep} {st : SymStep} (h : SymSteps M cfg₀ (π₀ ++ [st]) cfg') :
    ∃ cfg₁ : SymConfig, SymSteps M cfg₀ π₀ cfg₁ ∧ cfg' = symStepConfig cfg₁ st.result := by
  obtain ⟨cfg₁, h1, h2⟩ := symSteps_append_split (M := M) (cfg₀ := cfg₀) (cfg' := cfg')
    (π₀ := π₀) (rest := [st]) h
  exact ⟨cfg₁, h1, (symSteps_singleton_fromState h2).2⟩

/-- [δ-18-6] 单步路径四元事实：起态/读符号/合法转移/终点配置。
    （`symSteps_singleton_fromState` 的加强版：补出 `readSym` 与表成员。） -/
lemma symSteps_singleton_facts {M : ℕ × Sym → Finset SymTransResult} {cfg₀ cfg' : SymConfig}
    {step : SymStep} (h : SymSteps M cfg₀ [step] cfg') :
    step.fromState = cfg₀.state ∧ step.readSym = cfg₀.tape cfg₀.headPos ∧
    step.result ∈ M (cfg₀.state, cfg₀.tape cfg₀.headPos) ∧
    cfg' = symStepConfig cfg₀ step.result := by
  generalize hL : [step] = L at h
  induction h with
  | nil => simp at hL
  | cons πs step' cfg₁ hprev hfrom hread htrans _ =>
      have hsnoc := snoc_eq_snoc (α := SymStep) (π₁ := []) (π₂ := πs) (a := step) (b := step')
        (by simpa using hL)
      rcases hsnoc with ⟨hπs, hstep'⟩
      subst hstep'
      have hcfg₁ : cfg₁ = cfg₀ := symSteps_nil_cfg (by simpa [hπs] using hprev)
      subst hcfg₁
      exact ⟨hfrom, hread, htrans, rfl⟩

/-- [δ-18-7] `take (i+1)` 的 snoc 分解：`take (i+1) = take i ++ [π[i]]`。 -/
lemma symTake_succ_eq_snoc (π : List SymStep) (i : ℕ) (hi : i < π.length) :
    π.take (i + 1) = π.take i ++ [π.get ⟨i, hi⟩] := by
  induction π generalizing i with
  | nil => simp at hi
  | cons st rest ih =>
      cases i with
      | zero => simp
      | succ k =>
          have hk : k < rest.length := by simpa using hi
          have hget : (st :: rest).get ⟨k + 1, hi⟩ = rest.get ⟨k, hk⟩ := List.get_cons_succ ..
          rw [hget, List.take_succ_cons, List.take_succ_cons, ih k hk, List.cons_append]

/-- [δ-18-8] 列表小工具：`take (a+b) = take a ++ (drop a).take b`。 -/
lemma symTake_add_eq_take_append (π : List SymStep) (a b : ℕ) :
    π.take (a + b) = π.take a ++ (π.drop a).take b := by
  induction a generalizing π with
  | zero => simp
  | succ m ih =>
      cases π with
      | nil => simp
      | cons st rest =>
          rw [show m + 1 + b = (m + b) + 1 from by omega]
          simp only [List.take_succ_cons, List.drop_succ_cons]
          rw [List.cons_append, ← ih rest]

/-- **[δ-18 本体]** 分支读步位置互异（强形式）：若第 `j` 步在位置 `p` 读到分支（α/β），
    则**任意**更早的步（下标 `i < j`）都不可能停在同一格。

    证明：步 `i` 在 `p` 上写出的符号非分支（`symSteps_writeSym_nonbranch`，力量来源 =
    「可延拓到 accept」⇒ 无 101/100 步）⇒ 由格值单调 `symSteps_tape_branch_mono` 沿中段
    传下去 ⇒ 步 `j` 之前 `p` 处仍非分支 ⇒ 但步 `j` 恰在 `p` 处读到分支，矛盾 ∎

    注：结论比 `NTM2.Canonical` (b) 所需更强 —— **不需要**「步 `i` 也是分支读」这一前提。 -/
theorem symSteps_branchRead_pos_ne {cfg₀ cfg : SymConfig} {π : List SymStep}
    (h : SymSteps VerifierSym.transition cfg₀ π cfg)
    (hleg : cfg₀.state ∈ VerifierSym.legalStates)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101)
    (hno100 : ∀ step ∈ π, step.fromState ≠ 100)
    {i j : ℕ} (hij : i < j) (hj : j < π.length)
    (hj' : Sym.isBranch (π.get ⟨j, hj⟩).readSym) :
    symEnd cfg₀.headPos (π.take i) ≠ symEnd cfg₀.headPos (π.take j) := by
  intro hpos
  let πi := π.get ⟨i, lt_trans hij hj⟩
  let πj := π.get ⟨j, hj⟩
  -- 步 i 处的工具（下标 i+1 的 take 分解）
  have htakei : π.take (i + 1) = π.take i ++ [πi] := symTake_succ_eq_snoc π i (lt_trans hij hj)
  have hno101₁ : ∀ st ∈ π.take (i + 1), st.result.nextState ≠ 101 :=
    fun st hst => hno101 st (List.mem_of_mem_take hst)
  have hno100₁ : ∀ st ∈ π.take (i + 1), st.fromState ≠ 100 :=
    fun st hst => hno100 st (List.mem_of_mem_take hst)
  have hπi_mem : πi ∈ π.take i ++ [πi] :=
    List.mem_append.mpr (Or.inr (List.mem_singleton_self πi))
  -- ① 取「步 j 之前」的配置 cJ'，及其单步事实
  have htakej : π.take (j + 1) = π.take j ++ [πj] := symTake_succ_eq_snoc π j hj
  obtain ⟨cJ₁, hpreJ₁, _⟩ := symSteps_prefix_cfg h (j + 1)
  rw [htakej] at hpreJ₁
  obtain ⟨cJ', hpreJ', hsingJ⟩ := symSteps_append_split (M := VerifierSym.transition)
    (cfg₀ := cfg₀) (cfg' := cJ₁) (π₀ := π.take j) (rest := [πj]) hpreJ₁
  obtain ⟨_, hreadj, _, _⟩ := symSteps_singleton_facts hsingJ
  -- ② 把到 cJ' 的路径在 take (i+1) 处劈开 ⇒ c₁（中段起点）
  have hA : π.take (i + 1) ++ (π.drop (i + 1)).take (j - (i + 1)) = π.take j := by
    rw [← symTake_add_eq_take_append π (i + 1) (j - (i + 1))]
    congr 1
    omega
  rw [← hA] at hpreJ'
  obtain ⟨c₁, hpre₁, hmid⟩ := symSteps_append_split (M := VerifierSym.transition)
    (cfg₀ := cfg₀) (cfg' := cJ') (π₀ := π.take (i + 1))
    (rest := (π.drop (i + 1)).take (j - (i + 1))) hpreJ'
  -- ③ 步 i 的终点 c₁ 由 ci 走一步
  rw [htakei] at hpre₁ hno101₁ hno100₁
  obtain ⟨ci, hprei, hsingi⟩ := symSteps_append_split (M := VerifierSym.transition)
    (cfg₀ := cfg₀) (cfg' := c₁) (π₀ := π.take i) (rest := [πi]) hpre₁
  obtain ⟨_, _, _, hc1eq⟩ := symSteps_singleton_facts hsingi
  -- ④ 步 i 写出的符号非分支 ⇒ c₁ 在写头位置非分支
  have hwri : ¬ Sym.isBranch πi.result.writeSym :=
    symSteps_writeSym_nonbranch hpre₁ hleg hno101₁ hno100₁ πi hπi_mem
  have hnb₁ : ¬ Sym.isBranch (c₁.tape ci.headPos) := by
    rw [hc1eq, symStepConfig_tape_head]
    exact hwri
  -- ⑤ 中段格值单调 ⇒ 步 j 之前该位置仍非分支
  have hleg₁ : c₁.state ∈ VerifierSym.legalStates := (symSteps_state_mem_legal hpre₁ hleg).1
  have hno101mid : ∀ st ∈ (π.drop (i + 1)).take (j - (i + 1)), st.result.nextState ≠ 101 :=
    fun st hst => hno101 st (List.mem_of_mem_drop (List.mem_of_mem_take hst))
  have hno100mid : ∀ st ∈ (π.drop (i + 1)).take (j - (i + 1)), st.fromState ≠ 100 :=
    fun st hst => hno100 st (List.mem_of_mem_drop (List.mem_of_mem_take hst))
  have hmono := symSteps_tape_branch_mono hmid hleg₁ hno101mid hno100mid
  have hnbJ : ¬ Sym.isBranch (cJ'.tape ci.headPos) := hmono ci.headPos hnb₁
  -- ⑥ 位置对齐：两步读到同一格 ⇒ 矛盾
  have hci_head : ci.headPos = symEnd cfg₀.headPos (π.take i) := by
    rw [symSteps_headPos_eq VerifierSym.transition hprei, symEnd_eq_headPos_sum]
  have hcJ_head : cJ'.headPos = symEnd cfg₀.headPos (π.take j) := by
    rw [symSteps_headPos_eq VerifierSym.transition hpreJ', symEnd_eq_headPos_sum, hA]
  have hpeq : ci.headPos = cJ'.headPos := by
    rw [hci_head, hcJ_head, hpos]
  have hbr : Sym.isBranch (cJ'.tape ci.headPos) := by
    rw [hpeq]
    rw [← hreadj]
    exact hj'
  exact hnbJ hbr

-- ============================================================================
-- δ-19  Sym → F4 搬运桥（把 δ-18 抬到 `NTM2.Canonical` (b) 所在的 F4 层）
-- ============================================================================

/-- **[δ-19-1] 判据对齐（F4 → Sym）**：若 `symTo4F4 s` 的**末格**虚部为 `true`，则 `s` 是分支符号。

    F4 层 (b) 的前提是 `F4.im step.readSym = true`（「读到一个 im 格」）；本引理把它翻译成
    Sym 层的 `Sym.isBranch`（α/β），从而 δ-18 `symSteps_branchRead_pos_ne` 可以接手。
    取材 = CBTM 层既有单向件 `symTo4F4_getLastD_im_false_of_notBranch`（:89）取逆否。 -/
lemma symTo4F4_getLastD_im_true_branch (s : Sym)
    (h : F4.im ((Mp.SymToF4.symTo4F4 s).getLastD F4.zero) = true) : Sym.isBranch s := by
  by_contra hnb
  have hf := Mp.SymToF4.symTo4F4_getLastD_im_false_of_notBranch s hnb
  rw [hf] at h
  exact Bool.noConfusion h

-- ============================================================================
-- [δ-19-2] 位置算术：`flat4F4` 的块结构（第 j 个 Sym 占 F4 位 `4j .. 4j+3`）
--   块内 3 号位承载分支位 ⇒ F4 层「标记读」的格位 = `4j+3`，对应 Sym 位置 `j`。
-- ============================================================================

/-- [δ-19-2a] 块定位：丢掉前 j 个块 ⇔ 丢掉前 j 个符号。 -/
lemma flat4F4_drop_blocks (w : List Sym) (j : ℕ) :
    (Mp.SymToF4.flat4F4 w).drop (4 * j) = Mp.SymToF4.flat4F4 (w.drop j) := by
  induction w generalizing j with
  | nil => simp [Mp.SymToF4.flat4F4]
  | cons s rest ih =>
    cases j with
    | zero => rfl
    | succ k =>
      rw [show 4 * (k + 1) = 4 * k + 4 by ring]
      rw [show (s :: rest).drop (k + 1) = rest.drop k from List.drop_succ_cons]
      rw [← ih k]
      rw [show Mp.SymToF4.flat4F4 (s :: rest)
            = Mp.SymToF4.symTo4F4 s ++ Mp.SymToF4.flat4F4 rest from rfl]
      rw [List.drop_append, Mp.SymToF4.symTo4F4_length]
      rw [show 4 * k + 4 - 4 = 4 * k by omega]
      rw [List.drop_eq_nil_of_le (by rw [Mp.SymToF4.symTo4F4_length]; omega),
        List.nil_append]

/-- [δ-19-2b] 块分解：第 j 块显式拆出（末格 = 块内 3 号位 = `symTo4F4 (w[j])` 的末格）。

    这是 δ-19 判据对齐的位置依据：F4 层读到 `4j+3` 号位 ⇔ Sym 层读到第 j 个符号。 -/
lemma flat4F4_block_decomp (w : List Sym) (j : ℕ) (hj : j < w.length) :
    (Mp.SymToF4.flat4F4 w).drop (4 * j)
      = Mp.SymToF4.symTo4F4 (w[j]) ++ (Mp.SymToF4.flat4F4 w).drop (4 * j + 4) := by
  rw [flat4F4_drop_blocks w j]
  rw [show w.drop j = w[j] :: w.drop (j + 1) from List.drop_eq_getElem_cons hj]
  rw [show Mp.SymToF4.flat4F4 (w[j] :: w.drop (j + 1))
        = Mp.SymToF4.symTo4F4 (w[j]) ++ Mp.SymToF4.flat4F4 (w.drop (j + 1)) from rfl]
  rw [show 4 * j + 4 = 4 * (j + 1) by ring, ← flat4F4_drop_blocks w (j + 1)]

-- ============================================================================
-- [δ-19-3] 标记格定位：块内 3 号位（= `4j+3`）承载标记位与分支位
-- ============================================================================

/-- [δ-19-3a] `symTo4F4` 丢前 3 格 = 只剩末格（标记位 `s.2` + 分支位 `im`）。

    配合 δ-19-2 的 `flat4F4_block_decomp`（第 j 块 = `symTo4F4 (w[j]) ++ …`），
    即得 F4 层 `4j+3` 号位与 Sym 层第 j 个符号的对应。 -/
lemma symTo4F4_drop_three (s : Sym) :
    (Mp.SymToF4.symTo4F4 s).drop 3 = [(s.2, (Sym.kindBits s.1).2.1)] := by
  rcases s with ⟨k, m⟩
  cases k <;> simp [Mp.SymToF4.symTo4F4, Sym.kindBits]

-- ============================================================================
-- [δ-19-3b/3c] `symTo4F4` 块内末格（3 号位）=(4F4.4 位号, 分支位)
-- ============================================================================

/-- [δ-19-3b] 取格式。 -/
lemma symTo4F4_getElem_three (s : Sym) (h : 3 < (Mp.SymToF4.symTo4F4 s).length) :
    (Mp.SymToF4.symTo4F4 s)[3] = (s.2, (Sym.kindBits s.1).2.1) := by
  rcases s with ⟨k, m⟩
  cases k <;> rfl

/-- [δ-19-3c] `getLastD` 口径（供 δ-19-5 喂 δ-19-1）。 -/
lemma symTo4F4_getLastD_eq_marked (s : Sym) :
    (Mp.SymToF4.symTo4F4 s).getLastD F4.zero = (s.2, (Sym.kindBits s.1).2.1) := by
  rcases s with ⟨k, m⟩
  cases k <;> rfl

-- ============================================================================
-- [δ-19-4] 取格载荷：第 j 个符号的标记格 = 平铺磁带 `4j+3` 号位
-- ============================================================================

/-- [δ-19-4] δ-19-2 给块尺度（第 j 符号占 `4j..4j+3`），本件把**标记格本尊**取出来。 -/
lemma flat4F4_getElem_marked (w : List Sym) (j : ℕ) (hj : j < w.length)
    (h : 4 * j + 3 < (Mp.SymToF4.flat4F4 w).length) :
    (Mp.SymToF4.flat4F4 w)[4 * j + 3] = ((w[j]).2, (Sym.kindBits (w[j]).1).2.1) := by
  rw [← List.getElem_drop (xs := Mp.SymToF4.flat4F4 w) (i := 4 * j) (j := 3)
        (h := by rw [List.length_drop]; omega)]
  simp only [flat4F4_block_decomp w j hj]
  rw [List.getElem_append_left (h := by rw [Mp.SymToF4.symTo4F4_length]; omega)]
  exact symTo4F4_getElem_three (w[j]) (by rw [Mp.SymToF4.symTo4F4_length]; omega)

-- ============================================================================
-- [δ-19-5] F4 层标记读 ⇒ Sym 层分支符号（δ-19 交接件）
-- ============================================================================

/-- [δ-19-5] δ-19-1 把判据从 `F4.im` 翻到 `Sym.isBranch`，δ-19-4 把 `4j+3` 格位对到第 j 个符号；
本件把两者接起来 —— 此后 F4 层的标记读可直接交给 δ-18 的位置口径。 -/
lemma flat4F4_marked_im_true_branch (w : List Sym) (j : ℕ) (hj : j < w.length)
    (h : 4 * j + 3 < (Mp.SymToF4.flat4F4 w).length)
    (him : F4.im ((Mp.SymToF4.flat4F4 w)[4 * j + 3]) = true) : Sym.isBranch (w[j]) := by
  rw [flat4F4_getElem_marked w j hj h] at him
  have hlast : F4.im ((Mp.SymToF4.symTo4F4 (w[j])).getLastD F4.zero) = true := by
    rw [symTo4F4_getLastD_eq_marked]
    exact him
  exact symTo4F4_getLastD_im_true_branch (w[j]) hlast

-- ============================================================================
-- [δ-19-6] 磁带层交接件：拼接口前缀下的标记读 ⇒ Sym 层分支符号
-- ============================================================================

/-- [δ-19-6] `Sym.isBranch` 的 `Bool` 与标记格分支位同口径（构造子 8 例穷举）。 -/
lemma sym_isBranch_iff_branchBit (s : Sym) :
    Sym.isBranch s = true ↔ (Sym.kindBits s.1).2.1 = true := by
  rcases s with ⟨k, m⟩
  cases k <;> rfl

/-- [δ-19-6] 磁带层交接件：`pre ++ gS` 平铺后，块 `pre.length + j` 的标记格（F4 位置
`4*(pre.length+j)+3`）读到 `im = true` ⇒ Sym 层第 j 个符号是分支符号。

消费时取 `pre = encodeInstanceSym inst`：那一层 F4 磁带 = `flat4F4 (pre ++ gS)`
（因 `encodeInstanceF4 inst = flat4F4 (encodeInstanceSym inst)`），于是 F4 层的标记读
可以整句换成 δ-18 认得的 Sym 层位置语言（δ-19-5 只管单块，本件管带前缀的整卷磁带）。
写法要点：`getElem` 的界须显式（`a[i]'h`），且列表改写不可 `rw`（依赖改写会重推界）
—— 一律走 `congrArg` + 值层面等式，只在无证明参数的子项上 `rw`。 -/
lemma flat4F4_append_marked_im_true_branch (pre gS : List Sym) (j : ℕ) (hj : j < gS.length)
    (h : 4 * (pre.length + j) + 3 < (Mp.SymToF4.flat4F4 (pre ++ gS)).length)
    (him : F4.im ((Mp.SymToF4.flat4F4 (pre ++ gS))[4 * (pre.length + j) + 3]) = true) :
    Sym.isBranch (gS[j]) := by
  have hj' : pre.length + j < (pre ++ gS).length := by
    rw [List.length_append]
    exact Nat.add_lt_add_left hj pre.length
  -- 1) δ-19-4 取出该格本尊（`congrArg`：不重推 getElem 的界）
  have hcell : F4.im ((Mp.SymToF4.flat4F4 (pre ++ gS))[4 * (pre.length + j) + 3])
      = F4.im (((pre ++ gS)[pre.length + j]'hj').2,
          (Sym.kindBits ((pre ++ gS)[pre.length + j]'hj').1).2.1) :=
    congrArg F4.im (flat4F4_getElem_marked (pre ++ gS) (pre.length + j) hj' h)
  have him2 : F4.im (((pre ++ gS)[pre.length + j]'hj').2,
      (Sym.kindBits ((pre ++ gS)[pre.length + j]'hj').1).2.1) = true := by
    rw [← hcell]
    exact him
  -- 2) 块号换成 `gS[j]`（先证裸等式，再改无证明参数的子项）
  have hidx : Sym.kindBits ((pre ++ gS)[pre.length + j]'hj').1 = Sym.kindBits (gS[j]).1 := by
    have h1 : (pre ++ gS)[pre.length + j]'hj' = gS[j] := by
      rw [List.getElem_append_right (h₁ := by omega)]
      congr 1
      omega
    rw [h1]
  -- 3) 汇总
  have hb2 : (Sym.kindBits (gS[j]).1).2.1 = true := by
    rw [← hidx]
    simpa [F4.im] using him2
  exact (sym_isBranch_iff_branchBit (gS[j])).mpr hb2

/-- [δ-19-7a] 总装句（**iff 形**）：把 δ-19-6 的单向交接件补成等价——
F4 卷带「块号 `pre.length + j` 的标记格」的虚部位 ⟺ `gS[j]` 是分支符号（α/β）。

用途：F4 层 (b) 判据要在这两个语言之间来回翻译——「F4 在这一格读到标记」当作
「Sym 第 j 步读到分支符号」用（δ-18 的入场券），反向用来把 δ-18 的结论翻回 F4。 -/
lemma flat4F4_append_marked_im_iff_branch (pre gS : List Sym) (j : ℕ) (hj : j < gS.length)
    (h : 4 * (pre.length + j) + 3 < (Mp.SymToF4.flat4F4 (pre ++ gS)).length) :
    F4.im ((Mp.SymToF4.flat4F4 (pre ++ gS))[4 * (pre.length + j) + 3]) = true
      ↔ Sym.isBranch (gS[j]) = true := by
  constructor
  · intro him
    exact flat4F4_append_marked_im_true_branch pre gS j hj h him
  · intro hb
    have hbit : (Sym.kindBits (gS[j]).1).2.1 = true :=
      (sym_isBranch_iff_branchBit (gS[j])).mp hb
    have hj' : pre.length + j < (pre ++ gS).length := by
      rw [List.length_append]
      exact Nat.add_lt_add_left hj pre.length
    have hcell := flat4F4_getElem_marked (pre ++ gS) (pre.length + j) hj' h
    have hchain : F4.im ((Mp.SymToF4.flat4F4 (pre ++ gS))[4 * (pre.length + j) + 3])
        = F4.im (((pre ++ gS)[pre.length + j]'hj').2,
            (Sym.kindBits ((pre ++ gS)[pre.length + j]'hj').1).2.1) :=
      congrArg F4.im hcell
    have hsym : (pre ++ gS)[pre.length + j]'hj' = gS[j] := by
      rw [List.getElem_append_right (h₁ := Nat.le_add_right pre.length j)]
      simp
    have h2 := congrArg (fun s : Sym => F4.im (s.2, (Sym.kindBits s.1).2.1)) hsym
    exact (hchain.trans h2).trans hbit

-- ============================================================================
-- δ-19-7b  相位几何的 Sym 层底座（(b) 总装的两块新地基）
--   α  走位连续性：单步行走经过起终之间的每个整数
--   β0 「已被步访问过的格恒非分支」（[F2-core]：kill + mono）
--   β  头左邻格非分支（[F2]）
--   ＋ 初始带负坐标非分支（blank）
-- ============================================================================

/-- 单步位移界：`Dir.toInt ≤ 1`。 -/
theorem dir_toInt_le_one (d : Dir) : d.toInt ≤ 1 := by
  cases d <;> simp [Dir.toInt]

/-- 单步位移界：`-1 ≤ Dir.toInt`。 -/
theorem dir_toInt_ge_neg_one (d : Dir) : -1 ≤ d.toInt := by
  cases d <;> simp [Dir.toInt]

/-- **[δ-19-7b-α] 走位连续性**：头位轨迹从 `h₀` 走到 `symEnd h₀ π`，每步位移 ∈ {-1,0,1}
    ⇒ 起终之间的每个整数都出现在轨迹里（结尾含终止位）。

    用途：[F2] 的「落点必已被访问过」——头位只能整步移动，故走到 `p` 必已踏过 `p-1`。 -/
theorem symPositions_walk_covers (h₀ k : ℤ) (π : List SymStep)
    (hlo : h₀ ≤ k) (hhi : k ≤ symEnd h₀ π) :
    k ∈ symPositions h₀ π ++ [symEnd h₀ π] := by
  induction π generalizing h₀ with
  | nil =>
      simp only [symPositions, List.nil_append, List.mem_singleton, symEnd] at hhi ⊢
      omega
  | cons st rest ih =>
      simp only [symPositions, symEnd, List.cons_append, List.mem_cons]
      by_cases hk : k = h₀
      · exact Or.inl hk
      · refine Or.inr ?_
        have h1 : h₀ + 1 ≤ k := by omega
        have h2 : st.result.moveDir.toInt ≤ 1 := dir_toInt_le_one _
        exact ih (h₀ + st.result.moveDir.toInt) (by omega) hhi

/-- 轨迹成员 ⇒ 它是某个前缀的终止位（即确实是某一步的起点头位）。 -/
theorem mem_symPositions_exists (h₀ k : ℤ) {π : List SymStep}
    (h : k ∈ symPositions h₀ π) :
    ∃ j, j < π.length ∧ symEnd h₀ (π.take j) = k := by
  induction π generalizing h₀ with
  | nil => simp [symPositions] at h
  | cons st rest ih =>
      simp only [symPositions, List.mem_cons] at h
      rcases h with hk | hk
      · refine ⟨0, by simp, ?_⟩
        rw [hk]
        simp [symEnd]
      · obtain ⟨j, hj, heq⟩ := ih (h₀ + st.result.moveDir.toInt) hk
        refine ⟨j + 1, by simpa using hj, ?_⟩
        rw [List.take_succ_cons]
        simpa [symEnd] using heq

/-- **[δ-19-7b-β0]（[F2-core]）已被步访问过的格恒非分支**：
    若 `k` 是 `πpre` 中第 `j` 步的起点头位，则终点格局 `cfgᵢ` 在 `k` 处非分支。

    证：步 `j` 在自己的头位写入 `writeSym`（接受路径上恒非分支，`symSteps_writeSym_nonbranch`），
    此后只有「写在头位」能改动带值，故格值分支沿路径单调（`symSteps_tape_branch_mono`）。
    —— 这正是 δ-18 证明里的 kill + mono 机制，此处提炼为可复用件。 -/
theorem symSteps_tape_nonbranch_of_visited {cfg₀ cfgᵢ : SymConfig} {πpre : List SymStep}
    (hpre : SymSteps VerifierSym.transition cfg₀ πpre cfgᵢ)
    (hleg : cfg₀.state ∈ VerifierSym.legalStates)
    (hno101 : ∀ step ∈ πpre, step.result.nextState ≠ 101)
    (hno100 : ∀ step ∈ πpre, step.fromState ≠ 100)
    {j : ℕ} (hj : j < πpre.length) :
    ¬ Sym.isBranch (cfgᵢ.tape (symEnd cfg₀.headPos (πpre.take j))) := by
  have hsplit : πpre.take (j + 1) ++ πpre.drop (j + 1) = πpre := List.take_append_drop _ _
  rw [← hsplit] at hpre
  obtain ⟨c₁, hpre₁, htail⟩ := symSteps_append_split (M := VerifierSym.transition)
      (cfg₀ := cfg₀) (cfg' := cfgᵢ) (π₀ := πpre.take (j + 1)) (rest := πpre.drop (j + 1)) hpre
  have htake : πpre.take (j + 1) = πpre.take j ++ [πpre.get ⟨j, hj⟩] :=
    symTake_succ_eq_snoc πpre j hj
  rw [htake] at hpre₁
  obtain ⟨cj, hprej, hsing⟩ := symSteps_append_split (M := VerifierSym.transition)
      (cfg₀ := cfg₀) (cfg' := c₁) (π₀ := πpre.take j) (rest := [πpre.get ⟨j, hj⟩]) hpre₁
  obtain ⟨_, _, _, hceq⟩ := symSteps_singleton_facts hsing
  -- ① 步 j 写出的符号非分支
  have hno101₁ : ∀ st ∈ πpre.take j ++ [πpre.get ⟨j, hj⟩], st.result.nextState ≠ 101 := by
    intro st hst
    exact hno101 st (List.mem_of_mem_take (by rw [htake]; exact hst))
  have hno100₁ : ∀ st ∈ πpre.take j ++ [πpre.get ⟨j, hj⟩], st.fromState ≠ 100 := by
    intro st hst
    exact hno100 st (List.mem_of_mem_take (by rw [htake]; exact hst))
  have hwr : ¬ Sym.isBranch (πpre.get ⟨j, hj⟩).result.writeSym :=
    symSteps_writeSym_nonbranch hpre₁ hleg hno101₁ hno100₁ _
      (List.mem_append.mpr (Or.inr (List.mem_singleton_self _)))
  -- ② 步 j 的起点头位
  have hheadj : cj.headPos = symEnd cfg₀.headPos (πpre.take j) := by
    rw [symSteps_headPos_eq VerifierSym.transition hprej, symEnd_eq_headPos_sum]
  -- ③ c₁ 在该位置非分支
  have hnb₁ : ¬ Sym.isBranch (c₁.tape (symEnd cfg₀.headPos (πpre.take j))) := by
    rw [hceq, ← hheadj, symStepConfig_tape_head]
    exact hwr
  -- ④ 沿尾巴单调
  have hleg₁ : c₁.state ∈ VerifierSym.legalStates := (symSteps_state_mem_legal hpre₁ hleg).1
  have hno101tail : ∀ st ∈ πpre.drop (j + 1), st.result.nextState ≠ 101 :=
    fun st hst => hno101 st (List.mem_of_mem_drop hst)
  have hno100tail : ∀ st ∈ πpre.drop (j + 1), st.fromState ≠ 100 :=
    fun st hst => hno100 st (List.mem_of_mem_drop hst)
  exact symSteps_tape_branch_mono htail hleg₁ hno101tail hno100tail _ hnb₁

/-- **[δ-19-7b-β]（[F2]）头左邻格非分支**：终点格局 `cfgᵢ` 头位的左邻格非分支。

    证：左邻要么落在起始带之外（前提 `hout` 给出它在起始带非分支，再由单调性传下来），
    要么曾被某一步踏过（走位连续性 α 给出「轨迹覆盖」⇒ 取出该步下标 j，由 β0 收口）。

    用途：(b) 总装的扫掠复查项——块头 `p` 左移时相位 9 会读到 `4p-1`（即 `p-1` 位的标记格），
    本件说明该位非分支 ⇒ 该次读不是「读到标记」，风险情形被排除。 -/
theorem symSteps_left_neighbour_nonbranch {cfg₀ cfgᵢ : SymConfig} {πpre : List SymStep}
    (hpre : SymSteps VerifierSym.transition cfg₀ πpre cfgᵢ)
    (hleg : cfg₀.state ∈ VerifierSym.legalStates)
    (hno101 : ∀ step ∈ πpre, step.result.nextState ≠ 101)
    (hno100 : ∀ step ∈ πpre, step.fromState ≠ 100)
    (hhead : cfgᵢ.headPos = symEnd cfg₀.headPos πpre)
    (hout : cfgᵢ.headPos - 1 < cfg₀.headPos → ¬ Sym.isBranch (cfg₀.tape (cfgᵢ.headPos - 1))) :
    ¬ Sym.isBranch (cfgᵢ.tape (cfgᵢ.headPos - 1)) := by
  by_cases hk : cfgᵢ.headPos - 1 < cfg₀.headPos
  · exact symSteps_tape_branch_mono hpre hleg hno101 hno100 _ (hout hk)
  · have hlo : cfg₀.headPos ≤ cfgᵢ.headPos - 1 := by omega
    have hhi : cfgᵢ.headPos - 1 ≤ symEnd cfg₀.headPos πpre := by omega
    rcases List.mem_append.mp (symPositions_walk_covers cfg₀.headPos _ πpre hlo hhi) with hm | hm
    · obtain ⟨j, hj, heq⟩ := mem_symPositions_exists cfg₀.headPos _ hm
      have hres := symSteps_tape_nonbranch_of_visited hpre hleg hno101 hno100 hj
      rwa [heq] at hres
    · simp only [List.mem_singleton] at hm
      omega

/-- 初始带在负坐标处非分支（取值 `Sym.blank`）。 -/
theorem symInitialConfig_tape_nonbranch_of_neg (input : List Sym) {x : ℤ} (hx : x < 0) :
    ¬ Sym.isBranch ((symInitialConfig input).tape x) := by
  have hcond : ¬ (0 ≤ x ∧ x.toNat < input.length) := by omega
  simp only [symInitialConfig, dif_neg hcond, Sym.blank]
  decide

-- ============================================================================
-- δ-19-8：块内前缀窗口（(b)/② 整句装配的位置件之一）
-- ============================================================================

/-- [δ-19-8] 块内前缀窗口：`GoodBlock` 的前 `i` 步（`i ≤ 3`）终点头位落在
    `[4p - i, 4p + i]`。块首头 = `4p`（`GoodBlock` 的 `hp`），每步位移 ∈ {-1,0,1}，
    故由 `tapeSteps_prefix_headPos_drift`（Reverse10）立即得到。

    用途（`NTM2.Canonical` 条款 ② 装配）：块内第 3 步读格为 `4p+3`；前 3 步的头位恒在
    `[4p-3, 4p+3]` 内且**只有第 3 步能到 `4p+3`**（前 2 步 ≤ `4p+2`），故 `4p+3` 格在该块
    前 3 步内不被写 ⇒ 第 3 步读到的 `4p+3` 格内容 = 块首内容（`blockCorrespond`）⇒
    标记读 ⇒ 该格是分支符号的第 4 格 ⇒ 其 Sym 来源即块首头位符号。 -/
lemma goodBlock_prefix_headPos_window {w : List F4}
    {cfgc : CBTMConfig Mp.SymToF4.subsetSumCBTM w}
    {π : ComputationPath} {cfgc' : CBTMConfig Mp.SymToF4.subsetSumCBTM w} {cfgs : SymConfig}
    {p : ℤ} {q : ℕ} {sym : Sym} {r : SymTransResult}
    (hblock : Mp.SymToF4.GoodBlock w cfgc π cfgc' cfgs p q sym r)
    {i : ℕ} (hi : i ≤ 3) {cfgi : CBTMConfig Mp.SymToF4.subsetSumCBTM w}
    (hpre : Mp.SymToF4.TapeSteps Mp.SymToF4.subsetSumCBTM w cfgc (π.take i) cfgi) :
    4 * p - (i : ℤ) ≤ cfgi.headPos ∧ cfgi.headPos ≤ 4 * p + (i : ℤ) := by
  rcases hblock with ⟨hpath, hlen, hst, hp, hcorr, hread, hq, hbranchq, hvalid, hstep4,
    hmk, hr, hst', hhead'⟩
  have hb : ∀ step ∈ π, step.result.moveDir.toInt = -1 ∨ step.result.moveDir.toInt = 0 ∨
      step.result.moveDir.toInt = 1 := by
    intro step _
    cases step.result.moveDir <;> simp [Dir.toInt]
  have hfirst : cfgc.headPos ∈ Set.Icc (4 * p) (4 * p) := by
    rw [hp]
    exact ⟨le_refl _, le_refl _⟩
  obtain ⟨hmain, _⟩ := Mp.SymToF4.tapeSteps_prefix_headPos_drift hpath hb hfirst
  obtain ⟨cfgm, hpathm, hmem⟩ := hmain i (by omega)
  have heq : cfgm = cfgi := Mp.tapeSteps_det (π.take i) hpathm hpre
  rw [heq] at hmem
  exact hmem


namespace Mp.SymToF4

/-- δ-19-9:`delta8` 的值域界(`0 ≤ delta8 m ≤ 3`,`m ≤ 8`)。 -/
lemma delta8_bounds (m : ℕ) (hm : m ≤ 8) : 0 ≤ delta8 m ∧ delta8 m ≤ 3 := by
  interval_cases m <;> norm_num [delta8]

/-- δ-19-9:12 步块内任一步的**步前头位**恒 ∈ `[4p-3, 4p+3]`(块内头位窗口)。
    来源:`tapeSteps12_len_pos`(`inGoodPos` 精确值/区间)+ `delta8` 值域界。
    用途:条款② 的位置论证 —— 更早块的头位被挡在 `4p'+3` 之内。 -/
lemma blockPrefix_headPos_within3 {w : List F4} {cfgc0 cfg : CBTMConfig subsetSumCBTM w}
    {π : ComputationPath} {p : ℤ} {q : ℕ}
    (h : TapeSteps subsetSumCBTM w cfgc0 π cfg)
    (hq0 : cfgc0.state = encodeState q 0 0)
    (hp0 : cfgc0.headPos = 4 * p)
    (htrap : ∀ k (hk : k < π.length), (decodeState (π.get ⟨k, hk⟩).result.nextState).1 ≠ 101) :
    ∀ m (_ : m ≤ π.length) (_ : m ≤ 11),
      ∃ cfgm : CBTMConfig subsetSumCBTM w,
        TapeSteps subsetSumCBTM w cfgc0 (π.take m) cfgm ∧
        4 * p - 3 ≤ cfgm.headPos ∧ cfgm.headPos ≤ 4 * p + 3 := by
  intro m hm hm11
  obtain ⟨cfgm, hpfx⟩ := tapeSteps_prefix_end h m hm
  have htake_len : (π.take m).length = m := by
    rw [List.length_take]
    exact Nat.min_eq_left hm
  have hlen' : (π.take m).length ≤ 12 := by omega
  have htrap' : ∀ k (hk : k < (π.take m).length),
      (decodeState ((π.take m).get ⟨k, hk⟩).result.nextState).1 ≠ 101 := by
    intro k hk
    have hkm : k < m := by omega
    have hkπ : k < π.length := by omega
    have hget : (π.take m).get ⟨k, hk⟩ = π.get ⟨k, hkπ⟩ := by
      simp only [List.get_eq_getElem]
      exact List.getElem_take
    rw [hget]
    exact htrap k hkπ
  have hgood := tapeSteps12_len_pos hpfx hlen' hq0 hp0 htrap'
  rcases hgood with ⟨hA, hB⟩
  rw [htake_len] at hA hB
  have hpair : 4 * p - 3 ≤ cfgm.headPos ∧ cfgm.headPos ≤ 4 * p + 3 := by
    by_cases hm8 : m ≤ 8
    · have he : cfgm.headPos = 4 * p + delta8 m := hA hm8
      have hb := delta8_bounds m hm8
      rw [he]; omega
    · have hi := hB (by omega)
      rcases hi with ⟨hlo, hhi⟩
      constructor <;> omega
  exact ⟨cfgm, hpfx, hpair⟩

end Mp.SymToF4

-- ======================================================================
-- §delta-19-10  ② 装配(路径层):标记读 = 该格首次访问
-- ======================================================================

-- 目标:NTM2.Canonical 的条款②(一般拆分形)。
-- 完全输入无关:只要路径每步「写值虚部 = false」([F4-W]),则读到标记格
-- (虚部 = true)的步必然是该格首次被访问 ⇒ 前缀内无步同位。
-- 剩余唯一义务:为 subsetSumNTM2 的接受路径放电 [F4-W](用 CBTM6
-- `accept_path_is_good_block_path` + 块内逐步写值 + [F1])。

lemma ntm2_snoc_eq_snoc {α : Type} {l₁ l₂ : List α} {a b : α}
    (h : l₁ ++ [a] = l₂ ++ [b]) : l₁ = l₂ ∧ a = b := by
  have hrev : (l₁ ++ [a]).reverse = (l₂ ++ [b]).reverse := by rw [h]
  have hcons : a :: l₁.reverse = b :: l₂.reverse := by simpa using hrev
  have ha : a = b := by simpa using (List.cons.inj hcons).1
  have hπr : l₁.reverse = l₂.reverse := (List.cons.inj hcons).2
  have hπ : l₁ = l₂ := by rw [← List.reverse_reverse l₁, hπr, List.reverse_reverse]
  exact ⟨hπ, ha⟩

/-- [δ-19-10-A] 访问过 ⇒ 内容非标记。

前提 [F4-W]:路径每步写值虚部 = false。
由 snoc 归纳:末尾一步要么写自己(写值非标记),要么不改动 X(前缀已保证)。 -/
lemma ntm2_tape_im_false_of_visited (A : NTM2) (x : List F4) :
    ∀ (π : NTM2ComputationPath) (cfg : NTM2Config A x),
      TapeReachablePathNTM2 A x π cfg →
      (∀ s ∈ π, F4.im s.result.2.1 = false) →
      ∀ X : ℤ, (∃ s ∈ π, s.pos = X) → F4.im (cfg.tape X) = false := by
  intro π cfg hr
  induction hr with
  | nil =>
    intro _ X hX
    simp at hX
  | cons π₀ step cfg₀ hrc hfrom hread hpos htrans ih =>
    intro hW X hX
    have hW₀ : ∀ t ∈ π₀, F4.im t.result.2.1 = false :=
      fun t ht => hW t (List.mem_append.mpr (Or.inl ht))
    have hstep : F4.im step.result.2.1 = false :=
      hW step (List.mem_append.mpr (Or.inr (by simp)))
    rcases hX with ⟨s, hs, hspos⟩
    rcases List.mem_append.mp hs with hs₀ | hs₁
    · have hc := ih hW₀ X ⟨s, hs₀, hspos⟩
      dsimp only [NTM2StepConfig]
      by_cases hx : X = cfg₀.headPos
      · rw [if_pos hx]; exact hstep
      · rw [if_neg hx]; exact hc
    · have hse : s = step := by simpa using hs₁
      have hXpos : X = cfg₀.headPos := by
        rw [← hspos, hse]
        exact hpos
      dsimp only [NTM2StepConfig]
      rw [if_pos hXpos]
      exact hstep

/-- [δ-19-10-B] ②(NTM2 层,一般拆分形)。

标记读的步,其前缀内无任何步停在同一格 ⇒ 标记读位置互异。
证法:设 step 是拆分点,step.pos = 拆点 cfg 的 headPos(hpos),且
step.readSym = cfg.tape cfg.headPos(hread)。若前缀内有步停在 step.pos,
由 (A) 得该处内容非标记,与 readSym 虚部 = true 矛盾。 -/
lemma ntm2_branchRead_pos_fresh (A : NTM2) (x : List F4) :
    ∀ (π : NTM2ComputationPath) (cfg : NTM2Config A x),
      TapeReachablePathNTM2 A x π cfg →
      (∀ s ∈ π, F4.im s.result.2.1 = false) →
      ∀ (π₀ : NTM2ComputationPath) (step : NTM2TransitionStep) (π₁ : NTM2ComputationPath),
        π = π₀ ++ step :: π₁ → F4.im step.readSym = true →
        ∀ s ∈ π₀, s.pos ≠ step.pos := by
  intro π cfg hr
  induction hr with
  | nil =>
    intro _ π₀ step π₁ hsplit _
    simp at hsplit
  | cons π₀' step' cfg₀' hrc hfrom hread hpos htrans ih =>
    intro hW π₀ step π₁ hsplit hvb
    have hW' : ∀ t ∈ π₀', F4.im t.result.2.1 = false :=
      fun t ht => hW t (List.mem_append.mpr (Or.inl ht))
    rcases List.eq_nil_or_concat π₁ with hnil | ⟨π₁', last, hcat⟩
    · subst hnil
      have hsn : π₀' ++ [step'] = π₀ ++ [step] := by simpa using hsplit
      obtain ⟨hπ, hst⟩ := ntm2_snoc_eq_snoc hsn
      subst hπ
      subst hst
      intro s hs hspos
      have hc := ntm2_tape_im_false_of_visited A x π₀' cfg₀' hrc hW' step'.pos ⟨s, hs, hspos⟩
      have h₁ : F4.im (cfg₀'.tape step'.pos) = true := by
        rw [hpos, ← hread]
        exact hvb
      rw [h₁] at hc
      simp at hc
    · have hcat' : π₁ = π₁' ++ [last] := by
        rw [List.concat_eq_append] at hcat
        exact hcat
      subst hcat'
      have hsn : π₀' ++ [step'] = (π₀ ++ step :: π₁') ++ [last] := by
        rw [← List.cons_append, ← List.append_assoc] at hsplit
        exact hsplit
      obtain ⟨hπ, _⟩ := ntm2_snoc_eq_snoc hsn
      exact ih hW' π₀ step π₁' hπ hvb

/-! ### δ-19-11：(W) 放电 —— 表级三件

(W) = 接受路径每步写值 `im = false`，按读符号二分：
* 读 `im = false` 的格：`transition4_write_im_false`（CBTM:343）已给；
* 读 `im = true` 的格：相位 < 8 时纯表可证（本块第二件）；相位 8-11 时
  非陷阱结果写回原符号（本块第三件）⇒ 内容不变，不产生新的标记内容。
辅助件 `trap_nextState_q101` 把"陷阱支解码出 `q = 101`"抽成一步。 -/

namespace Mp.SymToF4

/-- 陷阱转移的两支都取 `nextState = encodeState 101 (nphase ph) 0`
（`nphase ph = if ph = 11 then 0 else ph + 1`），故解码出的 `q` 恒为 101。 -/
lemma trap_nextState_q101 (ph : ℕ) (hph : ph < 12) (r : CBTMTransResult)
    (hr : r.nextState = encodeState 101 (if ph = 11 then 0 else ph + 1) 0) :
    (decodeState r.nextState).1 = 101 := by
  rw [hr]
  exact decodeState_encodeState_q_eq 101 (if ph = 11 then 0 else ph + 1) 0
    (trap_off_nphase_lt ph hph)

/-- (W-b) 表级：读标记格 + 相位 < 8 + 非陷阱 ⇒ 写值非标记。
相位 0-2/4-7 的标记读落陷阱；相位 3 的标记读只走 fork（写 sel/nosel 的 kind 位，恒 false）。 -/
lemma transition4_write_im_false_of_im_true_phase_lt8 (st : ℕ) (s : F4) (him : F4.im s = true)
    (hph8 : (decodeState st).2.1 < 8) (r : CBTMTransResult)
    (hr : r ∈ transition4 st s) (hnt : (decodeState r.nextState).1 ≠ 101) :
    F4.im r.writeSym = false := by
  have hph : (decodeState st).2.1 < 12 := by
    dsimp [decodeState, stepsPerSym, regBound]
    exact Nat.mod_lt _ (by decide : 0 < 12)
  dsimp [transition4] at hr
  by_cases hph3 : (decodeState st).2.1 < 3
  · rw [if_pos hph3, if_pos him] at hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl <;>
      exact absurd (trap_nextState_q101 (decodeState st).2.1 hph _ rfl) hnt
  · by_cases hphE : (decodeState st).2.1 = 3
    · rw [if_neg hph3, if_pos hphE] at hr
      rcases hsym : symOf4F4 (f4ofBuf (decodeState st).2.2).1 (f4ofBuf (decodeState st).2.2).2.1
          (f4ofBuf (decodeState st).2.2).2.2 s with _ | sym
      · simp [hsym] at hr
        rw [if_pos him] at hr
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl <;>
          exact absurd (trap_nextState_q101 (decodeState st).2.1 hph _ rfl) hnt
      · simp [hsym] at hr
        rw [if_pos him] at hr
        by_cases hcond : min (decodeState st).1 101 = 2
            ∧ (f4ofBuf (decodeState st).2.2).1 = F4.zero ∧ F4.re s = false
        · rw [if_pos hcond] at hr
          simp only [Finset.mem_insert, Finset.mem_singleton] at hr
          rcases hr with rfl | rfl
          · exact symTo4F4_getLastD_im_false_of_notBranch Sym.sel (by decide)
          · exact symTo4F4_getLastD_im_false_of_notBranch Sym.nosel (by decide)
        · rw [if_neg hcond] at hr
          simp only [Finset.mem_insert, Finset.mem_singleton] at hr
          rcases hr with rfl | rfl <;>
            exact absurd (trap_nextState_q101 (decodeState st).2.1 hph _ rfl) hnt
    · rw [if_neg hph3, if_neg hphE, if_pos hph8] at hr
      rw [if_pos him] at hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl <;>
        exact absurd (trap_nextState_q101 (decodeState st).2.1 hph _ rfl) hnt

/-- (W-c) 表级：相位 8-11 的标记读 ⇒ 非陷阱结果写回原符号 `s`（即内容不变）。
另一支为陷阱（解码 `q = 101`），由非陷阱假设排除。 -/
lemma transition4_phase_ge8_marked_write_back (st : ℕ) (s : F4) (him : F4.im s = true)
    (h8 : 8 ≤ (decodeState st).2.1) (h12 : (decodeState st).2.1 < 12)
    (r : CBTMTransResult) (hr : r ∈ transition4 st s) (hnt : (decodeState r.nextState).1 ≠ 101) :
    r.writeSym = s := by
  dsimp [transition4] at hr
  rw [if_neg (by omega : ¬ (decodeState st).2.1 < 3),
    if_neg (by omega : ¬ ((decodeState st).2.1 = 3)),
    if_neg (by omega : ¬ ((decodeState st).2.1 < 8)),
    if_pos h12] at hr
  rw [if_pos him] at hr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with h | h
  · rw [h]
  · exact absurd (by rw [h]; exact trap_nextState_q101 (decodeState st).2.1 h12 _ rfl) hnt

/-- (W) 块级放电：好块的 12 步中，每步写出的符号 `im` 位恒 `false`。
- 非标记读 ⇒ 表级 `transition4_write_im_false`；
- 标记读 ⇒ 相位 8-11 的「写回原标记符号」支被 `hprev_nb`/`hw_nb` 排除，故只可能是第 3 步
  （`l3a_goodblock_read_im_classify`），而第 3 步写值被 `GoodBlock` 钉住为
  `(symTo4F4 r.writeSym).getLastD`，由 `hw_nb` 收口。 -/
lemma goodBlock_write_im_false {w : List F4} {cfgc : CBTMConfig subsetSumCBTM w}
    {π : ComputationPath} {cfgc' : CBTMConfig subsetSumCBTM w} {cfgs : SymConfig}
    {p : ℤ} {q : ℕ} {sym : Sym} {r : SymTransResult}
    (hblock : GoodBlock w cfgc π cfgc' cfgs p q sym r)
    (hrs : r.nextState < 101)
    (hprev_nb : r.moveDir = Dir.L → Sym.isBranch (cfgs.tape (p - 1)) = false)
    (hw_nb : Sym.isBranch r.writeSym = false) :
    ∀ st ∈ π, F4.im st.result.writeSym = false := by
  rcases hblock with
    ⟨hpath, hlen, hst, hp, hcorr, hread, hq, hbranchq, hvalid_sym, hstep4, hmk, hr, hst', hhead'⟩
  have hcls := l3a_goodblock_read_im_classify
    ⟨hpath, hlen, hst, hp, hcorr, hread, hq, hbranchq, hvalid_sym, hstep4, hmk, hr, hst', hhead'⟩
    hrs hprev_nb hw_nb
  -- 路径内每步的转移成员关系（表级引理的入口）
  have hmem : ∀ (π' : ComputationPath) (cfg' : CBTMConfig subsetSumCBTM w),
      TapeSteps subsetSumCBTM w cfgc π' cfg' →
      ∀ st ∈ π', ∃ pos : ℤ,
        st.result ∈ subsetSumCBTM.transition (st.fromState, st.readSym, pos) := by
    intro π' cfg' h
    induction h with
    | nil => intro st hmem; simp at hmem
    | cons πm step cfgi hprev hfrom hread htrans ih =>
        intro st hmem
        rw [List.mem_append] at hmem
        rcases hmem with hmem | hmem
        · exact ih st hmem
        · rw [List.mem_singleton] at hmem
          subst hmem
          exact ⟨cfgi.headPos, by rw [hfrom, hread]; exact htrans⟩
  intro st hstmem
  obtain ⟨i, hi, hsti⟩ := List.mem_iff_getElem.mp hstmem
  have hi12 : i < 12 := by rw [hlen] at hi; exact hi
  have hget : π.getD i (TransitionStep.mk (encodeState q 0 0) F4.zero
      (CBTMTransResult.mk (encodeState q 0 0) F4.zero Dir.S)) = π[i] :=
    List.getD_eq_getElem π _ hi
  by_cases him : F4.im st.readSym = true
  · -- 标记读 ⇒ 只可能是第 3 步，写值被钉住
    obtain ⟨hi3, _⟩ := hcls i hi12 (by rw [hget, hsti]; exact him)
    subst hi3
    have hst3 : st = π.get ⟨3, by omega⟩ := by
      rw [← hsti]
      simp only [List.get_eq_getElem]
    rw [hst3, hstep4, ← symTo4F4_getD3_eq_lastD r.writeSym]
    exact l3a_write_getD3_im_of_not_branch r hw_nb
  · -- 非标记读 ⇒ 表级引理
    have hb : F4.im st.readSym = false := by
      cases h : F4.im st.readSym with
      | false => rfl
      | true => exact absurd h him
    obtain ⟨pos, hpos⟩ := hmem π cfgc' hpath st hstmem
    exact transition4_write_im_false st.fromState st.readSym hb st.result
      (by simpa [subsetSumCBTM] using hpos)



/-- δ-19-13a：`hw_nb`（[F1] 前提）的表级放电（表级件）。
好块第 3 步（相位 3）的写值 = `symTo4F4 r.writeSym` 的 kind 格；相位 3 < 8 ⇒ 写值恒非标记：
读非标记走 `transition4_write_im_false`，读标记走 `transition4_write_im_false_of_im_true_phase_lt8`。
⇒ `Sym.isBranch r.writeSym = false` 无需作前提（相位事实由 `path_phase_at` 在装配层供）。 -/
lemma goodBlock_writeSym_nonbranch {w : List F4} {cfgc : CBTMConfig subsetSumCBTM w}
    {π : ComputationPath} {cfgc' : CBTMConfig subsetSumCBTM w} {cfgs : SymConfig}
    {p : ℤ} {q : ℕ} {sym : Sym} {r : SymTransResult}
    (hblock : GoodBlock w cfgc π cfgc' cfgs p q sym r)
    (hrs : r.nextState < 101)
    (hph3 : ∀ (h3 : 3 < π.length), (decodeState (π.get ⟨3, h3⟩).fromState).2.1 < 8) :
    Sym.isBranch r.writeSym = false := by
  rcases hblock with
    ⟨hpath, hlen, hst, hp, hcorr, hread, hq, hbranchq, hvalid_sym, hstep4, hmk, hr, hst', hhead'⟩
  have h3 : 3 < π.length := by rw [hlen]; norm_num
  -- 块内每步的转移成员关系（表级引理的入口）
  have hmem : ∀ (π' : ComputationPath) (cfg' : CBTMConfig subsetSumCBTM w),
      TapeSteps subsetSumCBTM w cfgc π' cfg' → ∀ st ∈ π', ∃ pos : ℤ,
        st.result ∈ subsetSumCBTM.transition (st.fromState, st.readSym, pos) := by
    intro π' cfg' h
    induction h with
    | nil => intro st hmem; simp at hmem
    | cons πm step cfgi hprev hfrom hread' htrans ih =>
        intro st hmem
        rw [List.mem_append] at hmem
        rcases hmem with hmem | hmem
        · exact ih st hmem
        · rw [List.mem_singleton] at hmem
          subst hmem
          exact ⟨cfgi.headPos, by rw [hfrom, hread']; exact htrans⟩
  have hmem3 : π.get ⟨3, h3⟩ ∈ π := by
    refine List.mem_iff_getElem.mpr ⟨3, h3, ?_⟩
    rw [List.get_eq_getElem]
  obtain ⟨pos, hpos⟩ := hmem π cfgc' hpath (π.get ⟨3, h3⟩) hmem3
  have htrans3 : (π.get ⟨3, h3⟩).result ∈ transition4 (π.get ⟨3, h3⟩).fromState
      (π.get ⟨3, h3⟩).readSym := by
    simpa [subsetSumCBTM] using hpos
  have hregok : encodeResult r < 8192 := by
    dsimp [encodeResult]
    have hsk : skOf r.writeSym.1 + (if r.writeSym.2 then 9 else 0) < 18 := by
      rcases r.writeSym with ⟨k, mk⟩
      cases k <;> cases mk <;> simp [skOf]
    have hdir : dirOf r.moveDir < 3 := by
      cases r.moveDir <;> simp [dirOf]
    omega
  have hnt : (decodeState (π.get ⟨3, h3⟩).result.nextState).1 ≠ 101 := by
    rw [hstep4, decodeState_encodeState r.nextState 4 (encodeResult r) (by norm_num) hregok]
    omega
  have hw3 : F4.im (π.get ⟨3, h3⟩).result.writeSym = false := by
    rcases hb : F4.im (π.get ⟨3, h3⟩).readSym with _ | _
    · exact transition4_write_im_false (π.get ⟨3, h3⟩).fromState (π.get ⟨3, h3⟩).readSym hb
        (π.get ⟨3, h3⟩).result htrans3
    · exact transition4_write_im_false_of_im_true_phase_lt8 (π.get ⟨3, h3⟩).fromState
        (π.get ⟨3, h3⟩).readSym hb (hph3 h3) (π.get ⟨3, h3⟩).result htrans3 hnt
  rw [hstep4, ← symTo4F4_getD3_eq_lastD r.writeSym, l3a_symTo4F4_getD3_im r.writeSym] at hw3
  exact hw3

/-- δ-19-13b：(W) 块级（`hw_nb` 已放电版）—— 三前提降为两前提：块内无 101 + [F2]（左邻 kind 格非标记）。 -/
lemma goodBlock_write_im_false_of_hrs_prev {w : List F4} {cfgc : CBTMConfig subsetSumCBTM w}
    {π : ComputationPath} {cfgc' : CBTMConfig subsetSumCBTM w} {cfgs : SymConfig}
    {p : ℤ} {q : ℕ} {sym : Sym} {r : SymTransResult}
    (hblock : GoodBlock w cfgc π cfgc' cfgs p q sym r)
    (hrs : r.nextState < 101)
    (hprev_nb : r.moveDir = Dir.L → Sym.isBranch (cfgs.tape (p - 1)) = false)
    (hph3 : ∀ (h3 : 3 < π.length), (decodeState (π.get ⟨3, h3⟩).fromState).2.1 < 8) :
    ∀ st ∈ π, F4.im st.result.writeSym = false :=
  goodBlock_write_im_false hblock hrs hprev_nb (goodBlock_writeSym_nonbranch hblock hrs hph3)


/-- δ-19-13b：全路径 (W) —— 块级 (W) 的全局装配（Sym 投影口径）。
前提 = 路径起点 Sym 侧「头位左侧所有格皆非标记」不变量 + 无 101 + 相位纪律。 -/
theorem goodBlockPath_write_im_false {w : List F4} {π : ComputationPath}
    {cfgc₀ : CBTMConfig subsetSumCBTM w} {cfgc' : CBTMConfig subsetSumCBTM w}
    (hbp : GoodBlockPath w cfgc₀ π cfgc') (cfgs₀ : SymConfig)
    (hcorr₀ : blockCorrespond cfgc₀ cfgs₀)
    (hinv : ∀ x : ℤ, x < cfgs₀.headPos → Sym.isBranch (cfgs₀.tape x) = false)
    (hno101 : ∀ k (hk : k < π.length), (decodeState (π.get ⟨k, hk⟩).result.nextState).1 ≠ 101)
    (hph : ∀ k (hk : k < π.length), k % 12 = 3 →
      (decodeState (π.get ⟨k, hk⟩).fromState).2.1 < 8) :
    ∀ st ∈ π, F4.im st.result.writeSym = false := by
  induction hbp generalizing cfgs₀ with
  | nil =>
      intro st hmem
      simp at hmem
  | cons cfgc cfgm cfgc'' πm π cfgsb p q sym r hblock htail ih =>
      have hblock' : GoodBlock w cfgc πm cfgm cfgsb p q sym r := hblock
      -- 块内无 101（取整条路径的下标 3）
      have hrs : r.nextState < 101 := by
        rcases hblock with
          ⟨hpath, hlenm, hst, hp, hcorrB, hread, hq, hbranch, hvalid, hstep4, hmk, hr, hst', hhead'⟩
        have hle : r.nextState ≤ 101 := transition_nextState_le101 q sym hq r hr
        have hne : r.nextState ≠ 101 := by
          intro h101
          have hnt := hno101 3 (by
            have hlenm' : πm.length = 12 := hlenm
            simp [List.length_append] at *
            omega)
          have hregok : encodeResult r < 8192 := by
            dsimp [encodeResult]
            have hsk : skOf r.writeSym.1 + (if r.writeSym.2 then 9 else 0) < 18 := by
              rcases r.writeSym with ⟨k, mk⟩
              cases k <;> cases mk <;> simp [skOf]
            have hdir : dirOf r.moveDir < 3 := by
              cases r.moveDir <;> simp [dirOf]
            omega
          have hdec : decodeState (encodeState r.nextState 4 (encodeResult r)) =
              (r.nextState, 4, encodeResult r) :=
            decodeState_encodeState r.nextState 4 (encodeResult r) (by norm_num) hregok
          apply hnt
          change (decodeState ((πm ++ π)[3]'(by
            have hlenm' : πm.length = 12 := hlenm
            simp [List.length_append] at *
            omega)).result.nextState).1 = 101
          rw [List.getElem_append_left (show 3 < πm.length from by
            have hlenm' : πm.length = 12 := hlenm
            simp [List.length_append] at *
            omega)]
          change (decodeState (List.get πm ⟨3, by omega⟩).result.nextState).1 = 101
          rw [hstep4]
          dsimp
          rw [hdec]
          simp [h101]
        omega
      rcases hblock with
        ⟨hpath, hlenm, hst, hp, hcorrB, hread, hq, hbranch, hvalid, hstep4, hmk, hr, hst', hhead'⟩
      -- 相位纪律：块内第 3 步 = 整条路径下标 3
      have hph3 : ∀ (h3 : 3 < πm.length),
          (decodeState (πm.get ⟨3, h3⟩).fromState).2.1 < 8 := by
        intro h3
        have h3' : 3 < (πm ++ π).length := by
          simp only [List.length_append]
          omega
        have hget : (πm ++ π).get ⟨3, h3'⟩ = πm.get ⟨3, h3⟩ := by
          apply List.getElem_append_left
        have := hph 3 h3' (by norm_num)
        rwa [hget] at this
      -- 起点 Sym 配置 cfgs₀ 与块内 cfgsb 一致（三分量）
      have hstate : cfgs₀.state = cfgsb.state := by
        have heq : encodeState cfgs₀.state 0 0 = encodeState cfgsb.state 0 0 := by
          rw [← hcorr₀.1, hcorrB.1]
        have hdec := congrArg decodeState heq
        rw [decodeState_encodeState cfgs₀.state 0 0 (by norm_num) (by norm_num),
          decodeState_encodeState cfgsb.state 0 0 (by norm_num) (by norm_num)] at hdec
        exact congrArg Prod.fst hdec
      have hhead : cfgs₀.headPos = cfgsb.headPos := by
        have h1 := hcorr₀.2.1
        have h2 := hcorrB.2.1
        rw [h2] at h1
        nlinarith
      have htape : cfgs₀.tape = cfgsb.tape := by
        funext i
        apply sym_eq_of_symTo4F4_getD_eq
        intro j hj
        exact (hcorr₀.2.2 i j hj).symm.trans (hcorrB.2.2 i j hj)
      have hinv_b : ∀ x : ℤ, x < cfgsb.headPos →
          Sym.isBranch (cfgsb.tape x) = false := fun x hx => by
        rw [← hhead] at hx
        rw [← htape]
        exact hinv x hx
      -- [F2]：左邻 kind 格非标记 = 不变量在块首 Sym 配置的实例
      have hheadp : cfgsb.headPos = p := by
        have h0 : cfgs₀.headPos = p := by
          have h1 := hcorr₀.2.1
          rw [hp] at h1
          nlinarith
        rw [← hhead]
        exact h0
      have hprev_nb : r.moveDir = Dir.L → Sym.isBranch (cfgsb.tape (p - 1)) = false := by
        intro _
        exact hinv_b (p - 1) (by omega)
      have hWm : ∀ st ∈ πm, F4.im st.result.writeSym = false :=
        goodBlock_write_im_false_of_hrs_prev hblock' hrs hprev_nb hph3
      -- 不变量推到块末 Sym 配置
      have hw_nb : Sym.isBranch r.writeSym = false :=
        goodBlock_writeSym_nonbranch hblock' hrs hph3
      have hdb : r.moveDir.toInt ≤ 1 := by rcases r.moveDir <;> simp [Dir.toInt]
      have hda : -1 ≤ r.moveDir.toInt := by rcases r.moveDir <;> simp [Dir.toInt]
      have hinv' : ∀ x : ℤ, x < (symStepConfig cfgsb r).headPos →
          Sym.isBranch ((symStepConfig cfgsb r).tape x) = false := by
        intro x hx
        have hx' : x < cfgsb.headPos + r.moveDir.toInt := by simpa [symStepConfig] using hx
        by_cases hxp : x = cfgsb.headPos
        · have htx : (symStepConfig cfgsb r).tape x = r.writeSym := by
            simp only [symStepConfig]
            rw [if_pos hxp]
          rw [htx]
          exact hw_nb
        · have htx : (symStepConfig cfgsb r).tape x = cfgsb.tape x := by
            simp only [symStepConfig]
            rw [if_neg hxp]
          rw [htx]
          exact hinv_b x (by omega)
      -- tail 前提（下标平移 12）
      have hlenm0 : πm.length = 12 := hlenm
      have hno101_tail : ∀ k (hk : k < π.length),
          (decodeState ((π.get ⟨k, hk⟩).result.nextState)).1 ≠ 101 := by
        intro k hk
        have hk' : πm.length + k < (πm ++ π).length := by
          simp [List.length_append, hlenm0, hk]
        have hget : (πm ++ π).get ⟨πm.length + k, hk'⟩ = π.get ⟨k, hk⟩ := by
          change (πm ++ π)[πm.length + k] = π[k]
          rw [List.getElem_append_right (by omega)]
          simp
        have hnt := hno101 (πm.length + k) hk'
        rwa [hget] at hnt
      have hph_tail : ∀ k (hk : k < π.length), k % 12 = 3 →
          (decodeState (π.get ⟨k, hk⟩).fromState).2.1 < 8 := by
        intro k hk hk3
        have hk' : πm.length + k < (πm ++ π).length := by
          simp [List.length_append, hlenm0, hk]
        have hget : (πm ++ π).get ⟨πm.length + k, hk'⟩ = π.get ⟨k, hk⟩ := by
          change (πm ++ π)[πm.length + k] = π[k]
          rw [List.getElem_append_right (by omega)]
          simp
        have hmod : (πm.length + k) % 12 = 3 := by
          have h : (πm.length + k) % 12 = k % 12 := by
            rw [hlenm0, Nat.add_mod, Nat.mod_self, Nat.zero_add,
              Nat.mod_eq_of_lt (Nat.mod_lt k (by norm_num))]
          rw [h]
          exact hk3
        have hph' := hph (πm.length + k) hk' hmod
        rwa [hget] at hph'
      have hWπ : ∀ st ∈ π, F4.im st.result.writeSym = false :=
        ih (symStepConfig cfgsb r)
          (project_block w cfgc πm cfgm cfgsb p q sym r hblock' hrs) hinv'
          hno101_tail hph_tail
      intro st hmem
      rw [List.mem_append] at hmem
      rcases hmem with hmem | hmem
      · exact hWm st hmem
      · exact hWπ st hmem


/-- δ-19-14a/b：NTM2 路径镜像 + (W) 抬升 + `NTM2.Canonical subsetSumNTM2` 条款 ②。

- δ-19-14a：`ntm2StepToCBTM` / `ntm2_path_mirror`——NTM2 可达路径镜像到 CBTM，
  **列表逐项对应**（`iso_path_forward_noCan` 只给存在式，故此处自建）；
  再由 `iso_initial_corresp` / `iso_step_config` / `iso_step_forward` 收口。
  `ntm2_write_im_false_of_cbtm`：(W) 由 CBTM 层搬到 NTM2 层。
- δ-19-14b：`ntm2_accept_path_write_im_false_flat`——接受**可延拓**的 NTM2 路径，
  每步写值虚部 = false（即 [F4-W]）。装配链：
  `(π++π₂).map ntm2StepToCBTM` → `TapeSteps`（`tapeSteps_initial_iff`）
  → `accept_path_is_good_block_path`（CBTM6）→ δ-19-13b `goodBlockPath_write_im_false`
  （前提：`accept_path_no_trap` 供无 101、`initialBlockCorrespond` 供起点块对应、
  `path_phase_at_phase` 供相位纪律、`symInitialConfig_tape_nonbranch_of_neg` 供起点不变量）
  → 限到前缀 π。
- δ-19-14b：`ntm2_canonical_clause2`——**条款 ②**（一般拆分形，位置唯一性前缀口径）
  按 `NTM2.Canonical` 字面口径（x = encodeInstanceF4 inst ++ flat4F4 gS）落定。
-/
def ntm2StepToCBTM (s : NTM2TransitionStep) : TransitionStep :=
  { fromState := s.fromState, readSym := s.readSym, result := ntm2ResultToCBTM s.result }

lemma ntm2StepToCBTM_result (s : NTM2TransitionStep) :
    (ntm2StepToCBTM s).result = ntm2ResultToCBTM s.result := rfl

/-- δ-19-14a：NTM2 可达路径镜像到 CBTM（列表逐项对应，位置分量丢弃）。 -/
lemma ntm2_path_mirror (A : NTM2) (M : CBTM) (iso : StructIsoNTM2CBTM A M) (x : List F4) :
    ∀ (π : NTM2ComputationPath) (cfg : NTM2Config A x),
      TapeReachablePathNTM2 A x π cfg →
      TapeReachablePath M x (π.map ntm2StepToCBTM) (ntm2CfgToCBTM A M iso cfg) := by
  intro π cfg hr
  induction hr with
  | nil =>
    simpa [iso_initial_corresp A M iso x] using
      (TapeReachablePath.nil (M := M) (input := x))
  | cons π₀ step cfg₀ hrc hfrom hread hpos htrans ih =>
    have hfull : TapeReachablePathNTM2 A x (π₀ ++ [step]) (NTM2StepConfig cfg₀ step.result) :=
      TapeReachablePathNTM2.cons π₀ step cfg₀ hrc hfrom hread hpos htrans
    have hs_in : step.readSym ∈ A.alphabet :=
      path_step_readSym_mem_alphabet A hfull step (by simp)
    have htrans' : step.result ∈ A.transition (cfg₀.state, step.readSym, cfg₀.headPos) := by
      rw [← hread] at htrans
      exact htrans
    have hmem : ntm2ResultToCBTM step.result ∈
        M.transition (cfg₀.state, (iso.φ_symbol step.readSym).val, cfg₀.headPos) :=
      iso_step_forward A M iso cfg₀.state step.readSym cfg₀.headPos step.result hs_in htrans'
    rw [List.map_append, List.map_cons, List.map_nil]
    rw [iso_step_config A M iso cfg₀ step.result]
    dsimp only [ntm2StepToCBTM]
    refine TapeReachablePath.cons (π₀.map ntm2StepToCBTM) _ (ntm2CfgToCBTM A M iso cfg₀) ih ?_ ?_ ?_
    · dsimp [ntm2CfgToCBTM]
      exact hfrom
    · dsimp [ntm2CfgToCBTM, CBTMConfig.tapeAt]
      exact hread
    · dsimp [ntm2CfgToCBTM, CBTMConfig.tapeAt]
      rw [iso.h_φ_id step.readSym] at hmem
      rw [← hread]
      exact hmem

/-- δ-19-14a：CBTM 层 (W) ⇒ NTM2 层 (W)（同列表镜像）。 -/
lemma ntm2_write_im_false_of_cbtm {π : NTM2ComputationPath}
    (hW : ∀ st ∈ π.map ntm2StepToCBTM, F4.im st.result.writeSym = false) :
    ∀ s ∈ π, F4.im s.result.2.1 = false := by
  intro s hs
  have hmem : ntm2StepToCBTM s ∈ π.map ntm2StepToCBTM :=
    List.mem_map.mpr ⟨s, hs, rfl⟩
  simpa [ntm2StepToCBTM, ntm2ResultToCBTM] using hW (ntm2StepToCBTM s) hmem

/-- δ-19-14b：`flat4F4` 对拼接分配。 -/
lemma flat4F4_append (a b : List Sym) : flat4F4 (a ++ b) = flat4F4 a ++ flat4F4 b := by
  simp [flat4F4, List.flatMap_append]

/-- δ-19-14b：接受可延拓的 NTM2 路径 ⇒ 每步写值非标记（(W) 的 NTM2 层供给，flat 口径）。 -/
theorem ntm2_accept_path_write_im_false_flat {wS : List Sym}
    {π : NTM2ComputationPath}
    (hext : ∃ (π₂ : NTM2ComputationPath) (cfg₂ : NTM2Config subsetSumNTM2 (flat4F4 wS)),
        TapeReachablePathNTM2 subsetSumNTM2 (flat4F4 wS) (π ++ π₂) cfg₂ ∧
        cfg₂.state ∈ subsetSumNTM2.acceptStates) :
    ∀ s ∈ π, F4.im s.result.2.1 = false := by
  obtain ⟨π₂, cfg₂, hr₂, hacc₂⟩ := hext
  have hmir := ntm2_path_mirror subsetSumNTM2 subsetSumCBTM subsetSumIso
    (flat4F4 wS) (π ++ π₂) cfg₂ hr₂
  have hsteps : TapeSteps subsetSumCBTM (flat4F4 wS)
      (initialConfig subsetSumCBTM (flat4F4 wS)) ((π ++ π₂).map ntm2StepToCBTM)
      (ntm2CfgToCBTM subsetSumNTM2 subsetSumCBTM subsetSumIso cfg₂) :=
    (tapeSteps_initial_iff subsetSumCBTM (flat4F4 wS) ((π ++ π₂).map ntm2StepToCBTM)
      (ntm2CfgToCBTM subsetSumNTM2 subsetSumCBTM subsetSumIso cfg₂)).mpr hmir
  have hacc : (ntm2CfgToCBTM subsetSumNTM2 subsetSumCBTM subsetSumIso cfg₂).state ∈
      acceptStates4 := by
    have hmem : (ntm2CfgToCBTM subsetSumNTM2 subsetSumCBTM subsetSumIso cfg₂).state ∈
        subsetSumCBTM.acceptStates := by
      rw [subsetSumIso.h_accept]
      exact hacc₂
    exact hmem
  have hno101 := accept_path_no_trap hsteps hacc
  have hcorr0 : blockCorrespond (initialConfig subsetSumCBTM (flat4F4 wS))
      (symInitialConfig wS) :=
    initialBlockCorrespond wS
  have hq0 : (symInitialConfig wS).state ≤ 101 := by
    dsimp [symInitialConfig]
    norm_num
  have hbp : GoodBlockPath (flat4F4 wS) (initialConfig subsetSumCBTM (flat4F4 wS))
      ((π ++ π₂).map ntm2StepToCBTM)
      (ntm2CfgToCBTM subsetSumNTM2 subsetSumCBTM subsetSumIso cfg₂) :=
    accept_path_is_good_block_path hsteps hacc hno101 hcorr0 hq0
  have hinv : ∀ x : ℤ, x < (symInitialConfig wS).headPos →
      Sym.isBranch ((symInitialConfig wS).tape x) = false := by
    intro x hx
    have hx0 : x < 0 := by simpa [symInitialConfig] using hx
    have h := symInitialConfig_tape_nonbranch_of_neg wS hx0
    cases hb : Sym.isBranch ((symInitialConfig wS).tape x) with
    | false => rfl
    | true => exact (h hb).elim
  have hph : ∀ k (hk : k < ((π ++ π₂).map ntm2StepToCBTM).length), k % 12 = 3 →
      (decodeState (((π ++ π₂).map ntm2StepToCBTM).get ⟨k, hk⟩).fromState).2.1 < 8 := by
    intro k hk hk3
    rw [path_phase_at_phase hsteps k hk, hk3]
    norm_num
  have hW := goodBlockPath_write_im_false hbp (symInitialConfig wS) hcorr0 hinv hno101 hph
  have hWπ : ∀ st ∈ π.map ntm2StepToCBTM, F4.im st.result.writeSym = false := by
    intro st hst
    apply hW st
    rw [List.map_append]
    exact List.mem_append.mpr (Or.inl hst)
  exact ntm2_write_im_false_of_cbtm hWπ

/-- δ-19-14b：条款 ② —— flat 口径（任意 `wS : List Sym`）。 -/
theorem ntm2_canonical_clause2_flat {wS : List Sym}
    {π : NTM2ComputationPath} {cfg : NTM2Config subsetSumNTM2 (flat4F4 wS)}
    (hr : TapeReachablePathNTM2 subsetSumNTM2 (flat4F4 wS) π cfg)
    (hext : ∃ (π₂ : NTM2ComputationPath) (cfg₂ : NTM2Config subsetSumNTM2 (flat4F4 wS)),
        TapeReachablePathNTM2 subsetSumNTM2 (flat4F4 wS) (π ++ π₂) cfg₂ ∧
        cfg₂.state ∈ subsetSumNTM2.acceptStates) :
    ∀ (π₀ : NTM2ComputationPath) (step : NTM2TransitionStep) (π₁ : NTM2ComputationPath),
      π = π₀ ++ step :: π₁ → F4.im step.readSym = true →
      ∀ s ∈ π₀, s.pos ≠ step.pos :=
  ntm2_branchRead_pos_fresh subsetSumNTM2 (flat4F4 wS) π cfg hr
    (ntm2_accept_path_write_im_false_flat hext)

/-- δ-19-14b：条款 ② —— `NTM2.Canonical` 字面口径（x = encodeInstanceF4 inst ++ flat4F4 gS）。 -/
theorem ntm2_canonical_clause2 {inst : SubsetSumInstance} {gS : List Sym} {x : List F4}
    (hx : x = encodeInstanceF4 inst ++ flat4F4 gS)
    {π : NTM2ComputationPath} {cfg : NTM2Config subsetSumNTM2 x}
    (hr : TapeReachablePathNTM2 subsetSumNTM2 x π cfg)
    (hext : ∃ (π₂ : NTM2ComputationPath) (cfg₂ : NTM2Config subsetSumNTM2 x),
        TapeReachablePathNTM2 subsetSumNTM2 x (π ++ π₂) cfg₂ ∧
        cfg₂.state ∈ subsetSumNTM2.acceptStates) :
    ∀ (π₀ : NTM2ComputationPath) (step : NTM2TransitionStep) (π₁ : NTM2ComputationPath),
      π = π₀ ++ step :: π₁ → F4.im step.readSym = true →
      ∀ s ∈ π₀, s.pos ≠ step.pos := by
  have hx' : x = flat4F4 (encodeInstanceSym inst ++ gS) := by
    rw [hx, encodeInstanceF4, flat4F4_append]
  subst hx'
  exact ntm2_canonical_clause2_flat hr hext

end Mp.SymToF4

-- ===== δ-19-15c-4 BEGIN =====
-- (S2′) 步骤 3/4：α（元素标记格）单调 —— 机器永不「凭空」写出 α，
-- 故 s/n 格（只能由 α 格转来，δ-19-15c-3）的位置在初始带上必是 α 格。
namespace Mp

set_option maxRecDepth 200000

/-- δ-19-15c-4（表级）：写出了 α（按 kind）的合法非陷阱步，读符号也必是 α。 -/
theorem writeAlpha_readAlpha (s : Sym) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), s),
      r.nextState ≠ 101 → r.writeSym.1 = SymKind.alpha → s.1 = SymKind.alpha := by
  obtain ⟨k, m⟩ := s
  cases m <;> cases k <;> decide

/-- δ-19-15c-4（表级）：合法状态均 < 102（供 `Fin` 化用）。 -/
theorem legalStates_lt_102 : ∀ q ∈ VerifierSym.legalStates, q < 102 := by
  decide

/-- δ-19-15c-4：α 单调——初始非 α 的格，沿无陷阱路径恒非 α。 -/
lemma symSteps_tape_alpha_mono {cfg₀ cfg : SymConfig} {π : List SymStep}
    (h : SymSteps VerifierSym.transition cfg₀ π cfg)
    (h₀ : cfg₀.state ∈ VerifierSym.legalStates)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101) :
    ∀ x : ℤ, (cfg₀.tape x).1 ≠ SymKind.alpha → (cfg.tape x).1 ≠ SymKind.alpha := by
  induction h with
  | nil =>
      intro x hx
      exact hx
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      have hno₀ : ∀ st ∈ π₀, st.result.nextState ≠ 101 :=
        fun st hst => hno101 st (by rw [List.mem_append]; left; exact hst)
      intro x hx0
      have hxmid : (cfg'.tape x).1 ≠ SymKind.alpha := ih hno₀ x hx0
      dsimp [symStepConfig]
      by_cases hx' : x = cfg'.headPos
      · rw [if_pos hx']
        intro hw
        have hq : step.fromState ∈ VerifierSym.legalStates := by
          rw [hfrom]
          exact (symSteps_state_mem_legal hprev h₀).1
        have h101 : step.result.nextState ≠ 101 := hno101 step (by simp)
        have hreads : step.readSym.1 = SymKind.alpha :=
          writeAlpha_readAlpha step.readSym ⟨step.fromState, legalStates_lt_102 _ hq⟩
            step.result (by rw [← hfrom, ← hread] at htrans; exact htrans) h101 hw
        exact hxmid (by simpa [hx', hread] using hreads)
      · rw [if_neg hx']
        exact hxmid

end Mp
-- ===== δ-19-15c-4 END =====

-- ===== δ-19-15c-5 BEGIN =====
namespace Mp

set_option maxRecDepth 200000

/-- δ-19-15c-5（表级）：状态 4（轮头）上的合法非陷阱转移固定写 `data0`。 -/
theorem transition_four_write_data0 (s : Sym) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), s),
      r.nextState ≠ 101 → q = 4 → r.writeSym.1 = SymKind.data0 := by
  obtain ⟨k, m⟩ := s
  cases m <;> cases k <;> decide

/-- δ-19-15c-5：轮头步（合法、非陷阱）写 `data0`，即消费该格的选择位。 -/
theorem symStep_roundHead_write_data0 {step : SymStep}
    (hleg : step.fromState ∈ VerifierSym.legalStates)
    (h : step.result ∈ VerifierSym.transition (step.fromState, step.readSym))
    (hr : symRoundHead step = true) (h101 : step.result.nextState ≠ 101) :
    step.result.writeSym.1 = SymKind.data0 := by
  have h4 : step.fromState = 4 := by simpa [symRoundHead] using hr
  have hlt : step.fromState < 102 := legalStates_lt_102 step.fromState hleg
  exact transition_four_write_data0 step.readSym ⟨step.fromState, hlt⟩ step.result
    (by simpa [h4] using h) (by simpa [h4] using h101) (by simp [h4])

end Mp
-- ===== δ-19-15c-5 END =====

-- ===== δ-19-15c-6 BEGIN =====
namespace Mp

set_option maxRecDepth 200000

/-- δ-19-15c-6（表级，类型级）：写出 s/n（按 kind）且改变该格的合法非陷阱步，读符号必为 `(α, false)`。 -/
theorem writeSelOrNosel_kind_read_alpha (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      r.nextState ≠ 101 → (r.writeSym.1 = SymKind.sel ∨ r.writeSym.1 = SymKind.nosel) →
      r.writeSym ≠ (k, m) →
      k = SymKind.alpha ∧ m = false := by
  cases m <;> cases k <;> decide

/-- δ-19-15c-6：s/n 逐格回溯 —— 终点某格为 s/n，则该格在起点必为 α（或本就是 s/n）。 -/
lemma symSteps_selNosel_trace {cfgA cfgB : SymConfig} {π : List SymStep}
    (h : SymSteps VerifierSym.transition cfgA π cfgB)
    (h₀ : cfgA.state ∈ VerifierSym.legalStates)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101) :
    ∀ p : ℤ, ((cfgB.tape p).1 = SymKind.sel ∨ (cfgB.tape p).1 = SymKind.nosel) →
      ((cfgA.tape p).1 = SymKind.alpha ∨ (cfgA.tape p).1 = SymKind.sel ∨
        (cfgA.tape p).1 = SymKind.nosel) := by
  induction h with
  | nil => intro p hp; exact Or.inr hp
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      have hsm := symSteps_state_mem_legal hprev h₀
      have hfromleg : step.fromState ∈ VerifierSym.legalStates := by
        rw [hfrom]; exact hsm.1
      have hno₀ : ∀ st ∈ π₀, st.result.nextState ≠ 101 :=
        fun st hst => hno101 st (by rw [List.mem_append]; left; exact hst)
      have hstep101 : step.result.nextState ≠ 101 :=
        hno101 step (by rw [List.mem_append]; exact Or.inr (by simp))
      intro p hp
      dsimp [symStepConfig] at hp
      by_cases hx : p = cfg'.headPos
      · rw [if_pos hx] at hp
        by_cases hsame : step.result.writeSym = step.readSym
        · have hprev_sn : ((cfg'.tape p).1 = SymKind.sel ∨ (cfg'.tape p).1 = SymKind.nosel) := by
            rw [hx, ← hread]
            rw [hsame] at hp
            exact hp
          exact ih hno₀ p hprev_sn
        · have hreads : (step.readSym).1 = SymKind.alpha :=
            (writeSelOrNosel_kind_read_alpha step.readSym.1 step.readSym.2
              ⟨step.fromState, legalStates_lt_102 _ hfromleg⟩ step.result
              (by rw [← hfrom, ← hread] at htrans; exact htrans) hstep101 hp hsame).1
          have hprevα : (cfg'.tape p).1 = SymKind.alpha := by
            rw [hx, ← hread]
            exact hreads
          exact Or.inl (Classical.byContradiction fun hna =>
            (symSteps_tape_alpha_mono hprev h₀ hno₀ p hna) hprevα)
      · rw [if_neg hx] at hp
        exact ih hno₀ p hp

end Mp
-- ===== δ-19-15c-6 END =====

-- ===== δ-19-15c-7 BEGIN =====
namespace Mp

/-- δ-19-15c-7：轮头表 —— 依路径顺序登记每个轮头步的（起始位置, 步）。 -/
def roundHeads (h₀ : ℤ) : List SymStep → List (ℤ × SymStep)
  | [] => []
  | st :: rest =>
      (if symRoundHead st then [(h₀, st)] else []) ++
        roundHeads (h₀ + st.result.moveDir.toInt) rest

/-- δ-19-15c-7：轮头位置表（轮头表的首分量投影）。 -/
def roundPositions (h₀ : ℤ) (π : List SymStep) : List ℤ := (roundHeads h₀ π).map Prod.fst

/-- δ-19-15c-7：轮头表长度 = 轮头步数。 -/
lemma roundHeads_length (h₀ : ℤ) (π : List SymStep) :
    (roundHeads h₀ π).length = (π.filter symRoundHead).length := by
  induction π generalizing h₀ with
  | nil => simp [roundHeads]
  | cons st rest ih =>
      by_cases hs : symRoundHead st = true
      · simp [roundHeads, List.filter, hs, ih]
      · simp [roundHeads, List.filter, hs, ih]

/-- δ-19-15c-7：轮头位置表长度 = 轮头步数。 -/
lemma roundPositions_length (h₀ : ℤ) (π : List SymStep) :
    (roundPositions h₀ π).length = (π.filter symRoundHead).length := by
  simp [roundPositions, roundHeads_length]

/-- δ-19-15c-7：轮头表中的位置必出现在位置表里。 -/
lemma roundHeads_fst_mem {h₀ : ℤ} {π : List SymStep} {p : ℤ} {st : SymStep}
    (h : (p, st) ∈ roundHeads h₀ π) : p ∈ roundPositions h₀ π :=
  List.mem_map.mpr ⟨(p, st), h, rfl⟩

/-- δ-19-15c-7：轮头表非空性的展开：头部必是「本步 + 剩余」。 -/
lemma roundHeads_cons (h₀ : ℤ) (x : SymStep) (rest : List SymStep) :
    roundHeads h₀ (x :: rest) =
      (if symRoundHead x then [(h₀, x)] else []) ++
        roundHeads (h₀ + x.result.moveDir.toInt) rest :=
  rfl

end Mp
-- ===== δ-19-15c-7 END =====

-- ===== δ-19-15c-8 BEGIN =====
namespace Mp

set_option maxRecDepth 200000

/-- δ-19-15c-8：非标记格（kind 既非 α，也非选择位 s/n）。 -/
def Sym.notMarked (s : Sym) : Prop :=
  s.1 ≠ SymKind.alpha ∧ s.1 ≠ SymKind.sel ∧ s.1 ≠ SymKind.nosel

lemma symStepConfig_state (cfg : SymConfig) (r : SymTransResult) :
    (symStepConfig cfg r).state = r.nextState := rfl

lemma symStepConfig_tape_headPos (cfg : SymConfig) (r : SymTransResult) :
    (symStepConfig cfg r).tape cfg.headPos = r.writeSym := by
  simp [symStepConfig]

lemma symStepConfig_tape_of_ne (cfg : SymConfig) (r : SymTransResult) {p : ℤ}
    (h : p ≠ cfg.headPos) : (symStepConfig cfg r).tape p = cfg.tape p := by
  simp [symStepConfig, h]

/-- δ-19-15c-8（表级）：写出 α / s / n（按 kind）的合法非陷阱步，其读符号按 kind 也必为 α / s / n。 -/
lemma writeMarked_readMarked (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      r.nextState ≠ 101 →
      (r.writeSym.1 = SymKind.alpha ∨ r.writeSym.1 = SymKind.sel ∨ r.writeSym.1 = SymKind.nosel) →
      (k = SymKind.alpha ∨ k = SymKind.sel ∨ k = SymKind.nosel) := by
  cases m <;> cases k <;> decide

/-- δ-19-15c-8（步级）：读符号非标记 ⇒ 合法非陷阱步写出的符号也非标记。 -/
lemma notMarked_write_of_notMarked_read {step : SymStep}
    (hq : step.fromState ∈ VerifierSym.legalStates)
    (h : step.result ∈ VerifierSym.transition (step.fromState, step.readSym))
    (h101 : step.result.nextState ≠ 101) (hread : Sym.notMarked step.readSym) :
    Sym.notMarked step.result.writeSym := by
  by_contra hw
  cases hsym : step.readSym with
  | mk k m =>
    rw [hsym] at h hread
    rw [Sym.notMarked] at hread
    have hlt : step.fromState < 102 := legalStates_lt_102 _ hq
    have hw' : step.result.writeSym.1 = SymKind.alpha ∨ step.result.writeSym.1 = SymKind.sel
        ∨ step.result.writeSym.1 = SymKind.nosel := by
      by_cases h1 : step.result.writeSym.1 = SymKind.alpha
      · exact Or.inl h1
      · by_cases h2 : step.result.writeSym.1 = SymKind.sel
        · exact Or.inr (Or.inl h2)
        · by_cases h3 : step.result.writeSym.1 = SymKind.nosel
          · exact Or.inr (Or.inr h3)
          · exact absurd (show Sym.notMarked step.result.writeSym from ⟨h1, h2, h3⟩) hw
    have hk : k = SymKind.alpha ∨ k = SymKind.sel ∨ k = SymKind.nosel :=
      writeMarked_readMarked k m ⟨step.fromState, hlt⟩ step.result h h101 hw'
    rcases hk with h1 | h2 | h3
    · exact hread.1 h1
    · exact hread.2.1 h2
    · exact hread.2.2 h3

end Mp
-- ===== δ-19-15c-8 (part A) END =====

-- ===== δ-19-15c-8B BEGIN =====
namespace Mp

/-- δ-19-15c-8B：轮头位置表的单步展开。 -/
lemma roundPositions_cons (h₀ : ℤ) (x : SymStep) (rest : List SymStep) :
    roundPositions h₀ (x :: rest) =
      (if symRoundHead x then [h₀] else []) ++
        roundPositions (h₀ + x.result.moveDir.toInt) rest := by
  by_cases hr : symRoundHead x = true <;>
    simp [roundPositions, roundHeads_cons, hr]

/-- δ-19-15c-8B：某格在配置起点非标记 ⇒ 从此（含）起不再出现位于该绝对位置的轮头。 -/
lemma roundPositions_not_mem_of_notMarked {cfg₁ cfg : SymConfig} {rest : List SymStep} {p : ℤ}
    (h : SymSteps VerifierSym.transition cfg₁ rest cfg)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (hno101 : ∀ step ∈ rest, step.result.nextState ≠ 101)
    (hcell : Sym.notMarked (cfg₁.tape p)) :
    p ∉ roundPositions cfg₁.headPos rest := by
  induction rest generalizing cfg₁ cfg with
  | nil => simp [roundPositions, roundHeads]
  | cons st rest' ih =>
    obtain ⟨cfg₂, hst, hrest⟩ :=
      symSteps_append_split (π₀ := [st]) (rest := rest') (by simpa using h)
    obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
    have hno101' : ∀ step ∈ rest', step.result.nextState ≠ 101 :=
      fun step hmem => hno101 step (List.mem_cons_of_mem st hmem)
    have h101st : st.result.nextState ≠ 101 := hno101 st List.mem_cons_self
    have hleg₂ : cfg₂.state ∈ VerifierSym.legalStates :=
      (symSteps_state_mem_legal hst hleg).1
    have hhp : cfg₂.headPos = cfg₁.headPos + st.result.moveDir.toInt := by
      rw [hs_cfg]; rfl
    have hcell₂ : Sym.notMarked (cfg₂.tape p) := by
      rw [hs_cfg]
      by_cases hp : p = cfg₁.headPos
      · rw [hp, symStepConfig_tape_headPos]
        refine notMarked_write_of_notMarked_read (by rw [hs_from]; exact hleg)
          (by rw [hs_from, hs_read]; exact hs_mem) h101st ?_
        rw [hp] at hcell
        rw [← hs_read] at hcell
        exact hcell
      · rw [symStepConfig_tape_of_ne _ _ hp]
        exact hcell
    rw [roundPositions_cons]
    intro hmem
    rcases List.mem_append.mp hmem with h1 | h2
    · by_cases hr : symRoundHead st = true
      · rw [if_pos hr] at h1
        simp only [List.mem_singleton] at h1
        rw [h1] at hcell
        have hsn := symRoundHead_read_isSelOrNosel
          (by rw [hs_from, hs_read]; exact hs_mem) hr h101st
        rw [hs_read] at hsn
        rcases hsn with hsel | hnosel
        · exact hcell.2.1 hsel
        · exact hcell.2.2 hnosel
      · rw [if_neg hr] at h1
        exact absurd h1 List.not_mem_nil
    · have h2' : p ∈ roundPositions cfg₂.headPos rest' := by rw [hhp]; exact h2
      exact ih hrest hleg₂ hno101' hcell₂ h2'

end Mp
-- ===== δ-19-15c-8B END =====

-- ===== δ-19-15c-8C BEGIN =====
namespace Mp

/-- δ-19-15c-8C：轮头位置两两互异。 -/
lemma roundPositions_nodup {cfg₀ cfg : SymConfig} {π : List SymStep}
    (h : SymSteps VerifierSym.transition cfg₀ π cfg)
    (hleg : cfg₀.state ∈ VerifierSym.legalStates)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101) :
    (roundPositions cfg₀.headPos π).Nodup := by
  induction π generalizing cfg₀ cfg with
  | nil => simp [roundPositions, roundHeads]
  | cons st rest' ih =>
    obtain ⟨cfg₂, hst, hrest⟩ :=
      symSteps_append_split (π₀ := [st]) (rest := rest') (by simpa using h)
    obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
    have hno101' : ∀ step ∈ rest', step.result.nextState ≠ 101 :=
      fun step hmem => hno101 step (List.mem_cons_of_mem st hmem)
    have h101st : st.result.nextState ≠ 101 := hno101 st List.mem_cons_self
    have hleg₂ : cfg₂.state ∈ VerifierSym.legalStates :=
      (symSteps_state_mem_legal hst hleg).1
    have hhp : cfg₂.headPos = cfg₀.headPos + st.result.moveDir.toInt := by
      rw [hs_cfg]; rfl
    rw [roundPositions_cons]
    refine List.nodup_append.mpr ⟨?_, ?_, ?_⟩
    · by_cases hr : symRoundHead st = true <;> simp [hr]
    · rw [← hhp]; exact ih hrest hleg₂ hno101'
    · intro a ha b hb
      by_cases hr : symRoundHead st = true
      · rw [if_pos hr] at ha
        simp only [List.mem_singleton] at ha
        intro hab
        rw [ha] at hab
        rw [← hab] at hb
        have hnm : Sym.notMarked (cfg₂.tape cfg₀.headPos) := by
          rw [hs_cfg, symStepConfig_tape_headPos]
          have hw := symStep_roundHead_write_data0 (by rw [hs_from]; exact hleg)
            (by rw [hs_from, hs_read]; exact hs_mem) hr h101st
          exact ⟨by rw [hw]; decide, by rw [hw]; decide, by rw [hw]; decide⟩
        have hb' : cfg₀.headPos ∈ roundPositions cfg₂.headPos rest' := by rw [hhp]; exact hb
        exact (roundPositions_not_mem_of_notMarked hrest hleg₂ hno101' hnm) hb'
      · rw [if_neg hr] at ha
        exact absurd ha List.not_mem_nil

end Mp
-- ===== δ-19-15c-8C END =====

-- ===== δ-19-15c-8D BEGIN =====
namespace Mp

/-- δ-19-15c-8D：窗口计数 —— 轮头起始位置全落在 `[lo, hi]` 内且两两互异 ⇒ `#轮 ≤ hi − lo + 1`。 -/
lemma roundHead_count_le_window {cfg₀ cfg : SymConfig} {π : List SymStep} {lo hi : ℤ}
    (h : SymSteps VerifierSym.transition cfg₀ π cfg)
    (hleg : cfg₀.state ∈ VerifierSym.legalStates)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101)
    (hpos : ∀ p ∈ roundPositions cfg₀.headPos π, lo ≤ p ∧ p ≤ hi) :
    (π.filter symRoundHead).length ≤ (hi - lo + 1).toNat := by
  have hnodup : (roundPositions cfg₀.headPos π).Nodup := roundPositions_nodup h hleg hno101
  have hcard : (roundPositions cfg₀.headPos π).toFinset.card
      = (roundPositions cfg₀.headPos π).length := List.toFinset_card_of_nodup hnodup
  have hsub : (roundPositions cfg₀.headPos π).toFinset ⊆ Finset.Icc lo hi := by
    intro p hp
    rw [List.mem_toFinset] at hp
    exact Finset.mem_Icc.mpr (hpos p hp)
  calc (π.filter symRoundHead).length
      = (roundPositions cfg₀.headPos π).length := (roundPositions_length cfg₀.headPos π).symm
    _ = (roundPositions cfg₀.headPos π).toFinset.card := hcard.symm
    _ ≤ (Finset.Icc lo hi).card := Finset.card_le_card hsub
    _ = (hi - lo + 1).toNat := by rw [Int.card_Icc]; congr 1; ring

end Mp
-- ===== δ-19-15c-8D END =====

-- ===== δ-19-15c-9 BEGIN =====
namespace Mp

/-- δ-19-15c-9：轮头位置必是某个步的起始位置（窗口前提从 `symPositions` 转移过来）。 -/
lemma mem_roundPositions_mem_symPositions {h₀ : ℤ} {π : List SymStep} {p : ℤ}
    (h : p ∈ roundPositions h₀ π) : p ∈ symPositions h₀ π := by
  induction π generalizing h₀ with
  | nil => simp [roundPositions, roundHeads] at h
  | cons st rest ih =>
    rw [roundPositions_cons] at h
    rcases List.mem_append.mp h with h1 | h2
    · by_cases hr : symRoundHead st = true
      · rw [if_pos hr] at h1
        simp only [List.mem_singleton] at h1
        rw [h1]
        simp [symPositions]
      · rw [if_neg hr] at h1
        exact absurd h1 List.not_mem_nil
    · rw [symPositions]
      exact List.mem_cons_of_mem h₀ (ih h2)

/-- δ-19-15c-9：窗口前提转移。 -/
lemma roundPositions_window {h₀ : ℤ} {π : List SymStep} {lo hi : ℤ}
    (h : ∀ p ∈ symPositions h₀ π, lo ≤ p ∧ p ≤ hi) :
    ∀ p ∈ roundPositions h₀ π, lo ≤ p ∧ p ≤ hi :=
  fun p hp => h p (mem_roundPositions_mem_symPositions hp)

end Mp
-- ===== δ-19-15c-9 END =====

-- ===== δ-19-15c-10 BEGIN =====
namespace Mp

set_option maxRecDepth 200000

/-- δ-19-15c-10：Sym 层位移恒等式 —— 终点位置 = 起点 + Σ 位移。 -/
lemma symEnd_add_sum (h₀ : ℤ) (π : List SymStep) :
    symEnd h₀ π = h₀ + (π.map (fun st => st.result.moveDir.toInt)).sum := by
  induction π generalizing h₀ with
  | nil => simp [symEnd]
  | cons st rest ih =>
      simp only [symEnd, List.map_cons, List.sum_cons, ih]
      ring

/-- δ-19-15c-10：全 R 列表的位移和为长度。 -/
lemma sum_toInt_eq_length_of_all_R (l : List SymStep)
    (hl : ∀ st ∈ l, st.result.moveDir = Dir.R) :
    (l.map (fun st => st.result.moveDir.toInt)).sum = (l.length : ℤ) := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have ha : (a.result.moveDir : Dir).toInt = 1 := by rw [hl a List.mem_cons_self]; rfl
      have ht := ih (fun st hst => hl st (List.mem_cons_of_mem a hst))
      simp only [List.map_cons, List.sum_cons, List.length_cons, ha, ht]
      omega

/-- δ-19-15c-10：全 R 段（单调右行）长度 ≤ 窗口宽度。 -/
lemma length_le_of_all_R {h₀ : ℤ} {π : List SymStep} {lo hi : ℤ}
    (hmono : ∀ st ∈ π, st.result.moveDir = Dir.R)
    (hlo : lo ≤ h₀) (hhi : symEnd h₀ π ≤ hi) :
    π.length ≤ (hi - lo).toNat := by
  have hsum := sum_toInt_eq_length_of_all_R π hmono
  have hlen : (π.length : ℤ) = symEnd h₀ π - h₀ := by
    rw [symEnd_add_sum, hsum]; ring
  have hbound : (π.length : ℤ) ≤ hi - lo := by rw [hlen]; omega
  have hnn : (0 : ℤ) ≤ hi - lo := by omega
  omega

end Mp
-- ===== δ-19-15c-10 END =====

-- ===== δ-19-15c-11 BEGIN =====
namespace Mp

set_option maxRecDepth 200000

/-- δ-19-15c-11（表级）：方向是 `(状态, 读符号 kind)` 的函数 —— 非陷阱转移的 `moveDir` 唯一。
    α 双分支共享 `readSym` 与 `moveDir`，只有写入符号分叉。 -/
theorem transition_moveDir_unique (k : SymKind) (b : Bool) :
    ∀ (q : Fin 102),
      ∀ r₁ ∈ VerifierSym.transition ((q : ℕ), (k, b)),
      ∀ r₂ ∈ VerifierSym.transition ((q : ℕ), (k, b)),
      r₁.nextState ≠ 101 → r₂.nextState ≠ 101 → r₁.moveDir = r₂.moveDir := by
  cases b <;> cases k <;> decide

/-- δ-19-15c-11（表级）：读未标记 α 且**改变该格**的合法非陷阱步，写的必是 s/n（α 格的唯一转换器）。 -/
theorem alpha_unmarked_change_imp_sel_nosel :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (SymKind.alpha, false)),
      r.nextState ≠ 101 → r.writeSym ≠ (SymKind.alpha, false) →
        (r.writeSym = Sym.sel ∨ r.writeSym = Sym.nosel) := by
  decide

end Mp
-- ===== δ-19-15c-11 END =====

-- ===== δ-19-15c-12 BEGIN =====
namespace Mp

set_option maxRecDepth 200000

/-- δ-19-15c-12：自环转移方向唯一。 -/
theorem selfLoop_moveDir_unique (k₁ : SymKind) (b₁ : Bool)
    (k₂ : SymKind) (b₂ : Bool) :
    ∀ (q : Fin 102),
      ∀ r₁ ∈ VerifierSym.transition ((q : ℕ), (k₁, b₁)),
      ∀ r₂ ∈ VerifierSym.transition ((q : ℕ), (k₂, b₂)),
      r₁.nextState = (q : ℕ) → r₂.nextState = (q : ℕ) →
      r₁.nextState ≠ 101 → r₂.nextState ≠ 101 →
      r₁.moveDir = r₂.moveDir := by
  cases b₁ <;> cases k₁ <;> cases b₂ <;> cases k₂ <;> decide

end Mp
-- ===== δ-19-15c-12 END =====

-- ===== δ-19-15c-13 BEGIN =====
namespace Mp

set_option maxRecDepth 200000

/-- δ-19-15c-13：全 L 单调段的位移和 = 负长度。 -/
lemma sum_toInt_eq_neg_length_of_all_L (l : List SymStep)
    (hl : ∀ st ∈ l, st.result.moveDir = Dir.L) :
    (l.map (fun st => st.result.moveDir.toInt)).sum = -(l.length : ℤ) := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have ha : (a.result.moveDir : Dir).toInt = -1 := by rw [hl a List.mem_cons_self]; rfl
      have ht := ih (fun st hst => hl st (List.mem_cons_of_mem a hst))
      simp only [List.map_cons, List.sum_cons, List.length_cons, ha, ht]
      omega

/-- δ-19-15c-13：全 L 单调段的长度 ≤ 窗口宽度。 -/
lemma length_le_of_all_L {h₀ : ℤ} {π : List SymStep} {lo hi : ℤ}
    (hmono : ∀ st ∈ π, st.result.moveDir = Dir.L)
    (hlo : lo ≤ symEnd h₀ π) (hhi : h₀ ≤ hi) :
    π.length ≤ (hi - lo).toNat := by
  have hsum : (π.map (fun st => st.result.moveDir.toInt)).sum = -(π.length : ℤ) :=
    sum_toInt_eq_neg_length_of_all_L π hmono
  have hlen : (π.length : ℤ) = h₀ - symEnd h₀ π := by
    rw [symEnd_add_sum, hsum]; ring
  have : (π.length : ℤ) ≤ hi - lo := by rw [hlen]; omega
  have hnn : 0 ≤ hi - lo := by omega
  omega

end Mp
-- ===== δ-19-15c-13 END =====

-- ===== δ-19-15c-14 BEGIN =====
namespace Mp

set_option maxRecDepth 200000

/-- δ-19-15c-14：**自环不驻留（排除吸收态）** —— 非陷阱、非 100 状态的自环方向 ≠ S。
    （实测：S-自环仅存于吸收态 100（接受）与 101（陷阱）；接受路径由 `hfirst` 排除 100、`hno101` 排除 101。） -/
theorem selfLoop_moveDir_ne_S (k : SymKind) (b : Bool) :
    ∀ (q : Fin 102),
      ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, b)),
      r.nextState = (q : ℕ) → r.nextState ≠ 101 → (q : ℕ) ≠ 100 → r.moveDir ≠ Dir.S := by
  cases b <;> cases k <;> decide

-- ===== δ-19-15c-15 BEGIN =====
-- [C-2 ⇢ 正式] 转向数势函数核（φ 表由 _p_phi.py 求解：c1=5, c2=8, max φ=14）
--   · turnPhi_step    : 逐表行势约束（kernel decide）
--   · turnPhi_next_lt : 非陷阱步后继 < 102
--   · symTurnCount_snoc : 追加单元素转向数精确公式
--   · turn_budget_core: turns ≤ 5·#(5步) + 8·#(4步) + φ(末态,末方向)
--   （源探针 _probe_turnphi.lean 235 行全绿；公理足迹打印移至复查探针。）

set_option maxRecDepth 200000
set_option maxHeartbeats 20000000

/-- 势函数 φ（主循环 33 态 × 3 方向；其余取 0）。 -/
def turnPhi (q : ℕ) (d : Dir) : ℕ :=
  match q, d with
  | 1, Dir.R => 1
  | 2, Dir.R => 1
  | 3, Dir.S => 2
  | 4, Dir.R => 12
  | 5, Dir.R => 4
  | 5, Dir.S => 5
  | 8, Dir.L => 1
  | 9, Dir.L => 1
  | 10, Dir.R => 2
  | 11, Dir.S => 3
  | 12, Dir.R => 2
  | 13, Dir.R => 4
  | 14, Dir.R => 4
  | 20, Dir.L => 5
  | 20, Dir.S => 9
  | 21, Dir.R => 10
  | 22, Dir.S => 11
  | 23, Dir.L => 12
  | 24, Dir.L => 3
  | 26, Dir.L => 3
  | 27, Dir.L => 3
  | 28, Dir.R => 4
  | 29, Dir.L => 3
  | 38, Dir.L => 3
  | 51, Dir.L => 11
  | 76, Dir.L => 1
  | 77, Dir.L => 1
  | 81, Dir.R => 4
  | 84, Dir.L => 5
  | 85, Dir.L => 5
  | 86, Dir.R => 6
  | 87, Dir.R => 8
  | 87, Dir.S => 7
  | 100, Dir.R => 13
  | 100, Dir.S => 14
  | _, _ => 0

/-- [C-2] 表行势约束（kernel decide 逐行验证）：
    φ(s',d') + 5·[s=5] + 8·[s=4] ≥ φ(s,d) + [d≠d']（非陷阱行）。 -/
theorem turnPhi_step (s : Sym) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), s),
      r.nextState ≠ 101 → ∀ d : Dir,
        turnPhi r.nextState r.moveDir
            + 5 * (if (q : ℕ) = 5 then 1 else 0)
            + 8 * (if (q : ℕ) = 4 then 1 else 0)
          ≥ turnPhi (q : ℕ) d + (if d = r.moveDir then 0 else 1) := by
  obtain ⟨k, m⟩ := s
  cases m <;> cases k <;> decide

/-- [C-2] 非陷阱步后继状态 < 102。 -/
theorem turnPhi_next_lt (s : Sym) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), s),
      r.nextState ≠ 101 → r.nextState < 102 := by
  obtain ⟨k, m⟩ := s
  cases m <;> cases k <;> decide

/-- [C-2] φ ≤ 14。 -/
theorem turnPhi_le : ∀ (q : Fin 102) (d : Dir), turnPhi (q : ℕ) d ≤ 14 := by
  decide

/-- getLast? 双 cons 归约（rfl 级）。 -/
theorem getLast?_cons_cons_eq {α : Type*} (a b : α) (l : List α) :
    (a :: b :: l).getLast? = (b :: l).getLast? := rfl

/-- [C-2] 追加单元素转向数精确公式。 -/
theorem symTurnCount_snoc (l : List Dir) (d : Dir) :
    symTurnCount (l ++ [d])
      = symTurnCount l
        + (match l.getLast? with
            | none => 0
            | some e => if e = d then 0 else 1) := by
  induction l with
  | nil => simp [symTurnCount, List.getLast?]
  | cons e rest ih =>
    cases rest with
    | nil =>
      rw [List.singleton_append]
      by_cases h : e = d
      · subst h
        rw [symTurnCount_cons_cons_self _ []]
        simp [symTurnCount, List.getLast?]
      · rw [symTurnCount_cons_cons_ne h []]
        simp [symTurnCount, List.getLast?, h]
    | cons e₂ rest₂ =>
      rw [List.cons_append, List.cons_append]
      by_cases h : e = e₂
      · subst h
        rw [symTurnCount_cons_cons_self _ (rest₂ ++ [d]),
            symTurnCount_cons_cons_self _ rest₂]
        rw [← List.cons_append]
        rw [ih]
        rw [getLast?_cons_cons_eq]
      · rw [symTurnCount_cons_cons_ne h (rest₂ ++ [d]),
            symTurnCount_cons_cons_ne h rest₂]
        rw [← List.cons_append]
        rw [ih]
        rw [getLast?_cons_cons_eq]
        omega

/-- 路径末方向（空路径取 R）。 -/
def lastDirD (π : List SymStep) : Dir :=
  match π.getLast? with
  | some st => st.result.moveDir
  | none => Dir.R

/-- 单步转向量（空路径为 0）。 -/
def lastTurnD (π : List SymStep) (d : Dir) : ℕ :=
  match π.getLast? with
  | some st => if st.result.moveDir = d then 0 else 1
  | none => 0

/-- [C-2] 追加单步后末方向 = 该步方向。 -/
theorem lastDirD_append_single (π : List SymStep) (step : SymStep) :
    lastDirD (π ++ [step]) = step.result.moveDir := by
  unfold lastDirD
  rw [List.getLast?_append]
  have h1 : ([step] : List SymStep).getLast? = some step := rfl
  rw [h1]
  rfl

/-- [C-2] map 后末方向匹配 = lastTurnD。 -/
theorem lastTurnD_map (π : List SymStep) (d : Dir) :
    (match (π.map (fun st => st.result.moveDir)).getLast? with
      | none => 0
      | some e => if e = d then 0 else 1) = lastTurnD π d := by
  unfold lastTurnD
  rw [List.getLast?_map]
  cases h : π.getLast? with
  | none => simp []
  | some st => simp []

/-- [C-2] lastTurnD ≤ 单步转向指示（空路径时为 0）。 -/
theorem lastTurnD_le (π : List SymStep) (d : Dir) :
    lastTurnD π d ≤ (if lastDirD π = d then 0 else 1) := by
  cases h : π.getLast? with
  | none => simp [lastTurnD, lastDirD, h]
  | some st => simp [lastTurnD, lastDirD, h]

/-- [C-2 核心] 转向数摊销上界：
    turns ≤ 5·#(fromState=5 步) + 8·#(fromState=4 步) + φ(末态, 末方向)。
    （非陷阱路径；起点状态 < 102。） -/
theorem turn_budget_core {cfg₀ cfg : SymConfig} {π : List SymStep}
    (h : SymSteps VerifierSym.transition cfg₀ π cfg)
    (h0 : cfg₀.state < 102)
    (hno : ∀ st ∈ π, st.result.nextState ≠ 101) :
    cfg.state < 102 ∧
      symTurnCount (π.map (fun st => st.result.moveDir))
        ≤ 5 * (π.filter (fun st => st.fromState = 5)).length
          + 8 * (π.filter (fun st => st.fromState = 4)).length
          + turnPhi cfg.state (lastDirD π) := by
  revert hno
  induction h with
  | nil =>
      intro _
      exact ⟨h0, by simp [symTurnCount]⟩
  | cons π' step cfg' hprev hfrom hread htrans ih =>
      intro hno
      have hno₁ : ∀ st ∈ π', st.result.nextState ≠ 101 := by
        intro st hst
        exact hno st (by simp only [List.mem_append]; exact Or.inl hst)
      have hstep101 : step.result.nextState ≠ 101 := hno step (by simp)
      obtain ⟨hlt', hb'⟩ := ih hno₁
      have htrans' : step.result ∈ VerifierSym.transition (cfg'.state, step.readSym) := by
        simpa [← hread] using htrans
      have hlt'' : step.result.nextState < 102 := by
        simpa using turnPhi_next_lt step.readSym ⟨cfg'.state, hlt'⟩ step.result htrans' hstep101
      have hineq :
          turnPhi step.result.nextState step.result.moveDir
              + 5 * (if cfg'.state = 5 then 1 else 0)
              + 8 * (if cfg'.state = 4 then 1 else 0)
            ≥ turnPhi cfg'.state (lastDirD π')
              + (if lastDirD π' = step.result.moveDir then 0 else 1) := by
        simpa using turnPhi_step step.readSym ⟨cfg'.state, hlt'⟩ step.result htrans' hstep101 (lastDirD π')
      have hd := lastTurnD_le π' step.result.moveDir
      have hcnt : ∀ (m : ℕ),
          ((π' ++ [step]).filter (fun st => st.fromState = m)).length
            = (π'.filter (fun st => st.fromState = m)).length
              + (if cfg'.state = m then 1 else 0) := by
        intro m
        rw [List.filter_append, List.length_append]
        have h1 : ([step].filter (fun st => st.fromState = m)).length
            = (if cfg'.state = m then 1 else 0) := by
          by_cases hm : cfg'.state = m
          · simp [List.filter_nil, List.length_cons, List.length_nil, hfrom, hm]
          · simp [List.filter_nil, List.length_nil, hfrom, hm]
        rw [h1]
      have hT : symTurnCount ((π' ++ [step]).map (fun st => st.result.moveDir))
          = symTurnCount (π'.map (fun st => st.result.moveDir))
            + lastTurnD π' step.result.moveDir := by
        simp only [List.map_append, List.map_cons, List.map_nil]
        rw [symTurnCount_snoc, lastTurnD_map]
      have hst : (symStepConfig cfg' step.result).state = step.result.nextState := by
        simp [symStepConfig]
      have hld : lastDirD (π' ++ [step]) = step.result.moveDir := lastDirD_append_single π' step
      refine ⟨?_, ?_⟩
      · rw [hst]; exact hlt''
      · rw [hst, hld, hT, hcnt 5, hcnt 4]
        omega

/-- [C-2 推论] turns ≤ 5·#(5步) + 8·#(4步) + 14。 -/
theorem turn_budget_le14 {cfg₀ cfg : SymConfig} {π : List SymStep}
    (h : SymSteps VerifierSym.transition cfg₀ π cfg)
    (h0 : cfg₀.state < 102)
    (hno : ∀ st ∈ π, st.result.nextState ≠ 101) :
    symTurnCount (π.map (fun st => st.result.moveDir))
      ≤ 5 * (π.filter (fun st => st.fromState = 5)).length
        + 8 * (π.filter (fun st => st.fromState = 4)).length + 14 := by
  obtain ⟨hlt, hb⟩ := turn_budget_core h h0 hno
  have h14 : turnPhi cfg.state (lastDirD π) ≤ 14 := by
    simpa using turnPhi_le ⟨cfg.state, hlt⟩ (lastDirD π)
  omega
-- ===== δ-19-15c-15 END =====

-- ===== δ-19-15c-16 BEGIN =====
-- [C-3 ⇢ 正式] fivePositions：5-步位置表 + 不变式包 + 13 支分派（[4]/dispatch/master 续于薄探针）。
--   （源：_probe_fivepos.lean 13 支全绿内容整体迁入；[4]/else 支与总装待补。）
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000

-- ============================================================
-- [C-3 探针] fivePositions：5-步（位消费事件）位置表
--   镜像 c-7/c-9/c-8D 的轮头表结构。
--   目标链：fivePositions_nodup（唯一剩余件）⇒ F ≤ 窗口 ⇒ hturn。
-- ============================================================

/-- 5-步（位消费事件）。 -/
def symFive (step : SymStep) : Bool := decide (step.fromState = 5)

/-- 5-步表：按路径顺序登记每个 5-步的（起始位置, 步）。 -/
def fiveHeads (h₀ : ℤ) : List SymStep → List (ℤ × SymStep)
  | [] => []
  | st :: rest =>
      (if symFive st then [(h₀, st)] else []) ++
        fiveHeads (h₀ + st.result.moveDir.toInt) rest

/-- 5-步位置表。 -/
def fivePositions (h₀ : ℤ) (π : List SymStep) : List ℤ := (fiveHeads h₀ π).map Prod.fst

lemma fiveHeads_cons (h₀ : ℤ) (x : SymStep) (rest : List SymStep) :
    fiveHeads h₀ (x :: rest) =
      (if symFive x then [(h₀, x)] else []) ++
        fiveHeads (h₀ + x.result.moveDir.toInt) rest :=
  rfl

lemma fiveHeads_length (h₀ : ℤ) (π : List SymStep) :
    (fiveHeads h₀ π).length = (π.filter symFive).length := by
  induction π generalizing h₀ with
  | nil => simp [fiveHeads]
  | cons st rest ih =>
      by_cases hs : symFive st = true
      · simp [fiveHeads, List.filter, hs, ih]
      · simp [fiveHeads, List.filter, hs, ih]

lemma fivePositions_length (h₀ : ℤ) (π : List SymStep) :
    (fivePositions h₀ π).length = (π.filter symFive).length := by
  simp [fivePositions, fiveHeads_length]

lemma fiveHeads_fst_mem {h₀ : ℤ} {π : List SymStep} {p : ℤ} {st : SymStep}
    (h : (p, st) ∈ fiveHeads h₀ π) : p ∈ fivePositions h₀ π :=
  List.mem_map.mpr ⟨(p, st), h, rfl⟩

lemma fivePositions_cons (h₀ : ℤ) (x : SymStep) (rest : List SymStep) :
    fivePositions h₀ (x :: rest) =
      (if symFive x then [h₀] else []) ++
        fivePositions (h₀ + x.result.moveDir.toInt) rest := by
  by_cases hx : symFive x = true <;>
    simp [fivePositions, fiveHeads_cons, hx]

/-- 5-步位置必出现在位置表里（镜像 c-9）。 -/
lemma mem_fivePositions_mem_symPositions {h₀ : ℤ} {π : List SymStep} {p : ℤ}
    (h : p ∈ fivePositions h₀ π) : p ∈ symPositions h₀ π := by
  induction π generalizing h₀ with
  | nil => simp [fivePositions, fiveHeads] at h
  | cons st rest ih =>
    rw [fivePositions_cons] at h
    rcases List.mem_append.mp h with h1 | h2
    · by_cases hf : symFive st = true
      · rw [if_pos hf] at h1
        simp only [List.mem_singleton] at h1
        rw [h1]
        simp [symPositions]
      · rw [if_neg hf] at h1
        exact absurd h1 List.not_mem_nil
    · rw [symPositions]
      exact List.mem_cons_of_mem h₀ (ih h2)

/-- 5-步表对拼接可加（镜像 symPositions_append）。 -/
lemma fiveHeads_append (h₀ : ℤ) (π₁ π₂ : List SymStep) :
    fiveHeads h₀ (π₁ ++ π₂) = fiveHeads h₀ π₁ ++ fiveHeads (symEnd h₀ π₁) π₂ := by
  induction π₁ generalizing h₀ with
  | nil => simp [fiveHeads, symEnd]
  | cons st rest ih => simp [fiveHeads, symEnd, ih]

/-- 5-步位置表对拼接可加。 -/
lemma fivePositions_append (h₀ : ℤ) (π₁ π₂ : List SymStep) :
    fivePositions h₀ (π₁ ++ π₂) = fivePositions h₀ π₁ ++ fivePositions (symEnd h₀ π₁) π₂ := by
  simp [fivePositions, fiveHeads_append, List.map_append]

/-- 追加单步展开。 -/
lemma fivePositions_snoc (h₀ : ℤ) (π : List SymStep) (st : SymStep) :
    fivePositions h₀ (π ++ [st]) =
      fivePositions h₀ π ++ (if symFive st then [symEnd h₀ π] else []) := by
  rw [fivePositions_append]
  cases hs : symFive st <;> simp [fiveHeads, fivePositions, hs]

/-- 窗口前提转移（镜像 c-9）。 -/
lemma fivePositions_window {h₀ : ℤ} {π : List SymStep} {lo hi : ℤ}
    (h : ∀ p ∈ symPositions h₀ π, lo ≤ p ∧ p ≤ hi) :
    ∀ p ∈ fivePositions h₀ π, lo ≤ p ∧ p ≤ hi :=
  fun _p hp => h _p (mem_fivePositions_mem_symPositions hp)

-- ============================================================
-- 表级必然件（kernel decide）
-- ============================================================

/-- 表级：5 行读符号（非陷阱）必为 data0/data1。 -/
theorem five_table_read_data :
    ∀ (k : SymKind) (m : Bool) (r : SymTransResult),
      r ∈ VerifierSym.transition ((5 : ℕ), (k, m)) → r.nextState ≠ 101 →
      k = SymKind.data0 ∨ k = SymKind.data1 := by
  decide

/-- 表级：5 行（非陷阱）写符号必为 consumed。 -/
theorem five_table_write_consumed :
    ∀ (k : SymKind) (m : Bool) (r : SymTransResult),
      r ∈ VerifierSym.transition ((5 : ℕ), (k, m)) → r.nextState ≠ 101 →
      r.writeSym.1 = SymKind.consumed := by
  decide

/-- 步级：5-步（非陷阱）读符号为 data0/data1。 -/
lemma fiveStep_read_data {step : SymStep}
    (_hq : step.fromState ∈ VerifierSym.legalStates)
    (h : step.result ∈ VerifierSym.transition (step.fromState, step.readSym))
    (h101 : step.result.nextState ≠ 101) (hf : step.fromState = 5) :
    step.readSym.1 = SymKind.data0 ∨ step.readSym.1 = SymKind.data1 := by
  cases hsym : step.readSym with
  | mk k m =>
    have h' : step.result ∈ VerifierSym.transition ((5 : ℕ), (k, m)) := by
      rw [hf, hsym] at h
      exact h
    exact five_table_read_data k m step.result h' h101

/-- 步级：5-步（非陷阱）写符号为 consumed。 -/
lemma fiveStep_write_consumed {step : SymStep}
    (_hq : step.fromState ∈ VerifierSym.legalStates)
    (h : step.result ∈ VerifierSym.transition (step.fromState, step.readSym))
    (h101 : step.result.nextState ≠ 101) (hf : step.fromState = 5) :
    step.result.writeSym.1 = SymKind.consumed := by
  cases hsym : step.readSym with
  | mk k m =>
    have h' : step.result ∈ VerifierSym.transition ((5 : ℕ), (k, m)) := by
      rw [hf, hsym] at h
      exact h
    exact five_table_write_consumed k m step.result h' h101

-- ============================================================
-- 标记持久性（Part B 杠杆件）
-- ============================================================

/-- 表级：非陷阱步读标记格（s/n）⇒ 该步是 4（写 d0-）或写出同 kind（恒等）。 -/
theorem mark_table_persist (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      r.nextState ≠ 101 →
      (q : ℕ) = 4 ∨ r.writeSym.1 = k ∨ (k ≠ SymKind.sel ∧ k ≠ SymKind.nosel) := by
  cases m <;> cases k <;> decide

/-- 步级：读标记格的合法非陷阱步是 4 或写出同 kind。 -/
lemma markStep_persist {step : SymStep}
    (hq : step.fromState ∈ VerifierSym.legalStates)
    (h : step.result ∈ VerifierSym.transition (step.fromState, step.readSym))
    (h101 : step.result.nextState ≠ 101)
    (hmark : step.readSym.1 = SymKind.sel ∨ step.readSym.1 = SymKind.nosel) :
    step.fromState = 4 ∨ step.result.writeSym.1 = step.readSym.1 := by
  cases hsym : step.readSym with
  | mk k m =>
    have h' : step.result ∈ VerifierSym.transition (step.fromState, (k, m)) := by
      rw [hsym] at h
      exact h
    have hk : k = SymKind.sel ∨ k = SymKind.nosel := by
      rcases hmark with hs | hn
      · left; rw [hsym] at hs; exact hs
      · right; rw [hsym] at hn; exact hn
    have hpers := mark_table_persist k m
      ⟨step.fromState, legalStates_lt_102 step.fromState hq⟩ step.result h' h101
    rcases hpers with h4 | hw | hnm
    · left; simpa using h4
    · right; simpa using hw
    · exfalso
      rcases hnm with ⟨h1, h2⟩
      rcases hk with hs | hn
      · exact h1 hs
      · exact h2 hn

/-- 路径级：若无 4-步落在 p 上，且 p 处为标记格，则标记沿路径保持（镜像 c-8B）。 -/
theorem marked_persists_of_no_fourHead {cfg₁ cfg : SymConfig} {rest : List SymStep} {p : ℤ}
    (h : SymSteps VerifierSym.transition cfg₁ rest cfg)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (hno101 : ∀ step ∈ rest, step.result.nextState ≠ 101)
    (hmark : (cfg₁.tape p).1 = SymKind.sel ∨ (cfg₁.tape p).1 = SymKind.nosel)
    (hnofour : p ∉ roundPositions cfg₁.headPos rest) :
    (cfg.tape p).1 = SymKind.sel ∨ (cfg.tape p).1 = SymKind.nosel := by
  induction rest generalizing cfg₁ cfg with
  | nil => rw [symSteps_nil_cfg h]; exact hmark
  | cons st rest' ih =>
    obtain ⟨cfg₂, hst, hrest⟩ :=
      symSteps_append_split (π₀ := [st]) (rest := rest') (by simpa using h)
    obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
    have hno101' : ∀ step ∈ rest', step.result.nextState ≠ 101 :=
      fun step hmem => hno101 step (List.mem_cons_of_mem st hmem)
    have h101st : st.result.nextState ≠ 101 := hno101 st List.mem_cons_self
    have hleg₂ : cfg₂.state ∈ VerifierSym.legalStates :=
      (symSteps_state_mem_legal hst hleg).1
    have hhp : cfg₂.headPos = cfg₁.headPos + st.result.moveDir.toInt := by
      rw [hs_cfg]; rfl
    have hnofour' : p ∉ roundPositions cfg₂.headPos rest' := by
      intro hmem
      apply hnofour
      rw [roundPositions_cons]
      exact List.mem_append_right _
        (show p ∈ roundPositions (cfg₁.headPos + st.result.moveDir.toInt) rest' from by
          rw [← hhp]; exact hmem)
    have hmark₂ : (cfg₂.tape p).1 = SymKind.sel ∨ (cfg₂.tape p).1 = SymKind.nosel := by
      rw [hs_cfg]
      by_cases hp : p = cfg₁.headPos
      · rw [hp, symStepConfig_tape_headPos]
        have hread : st.readSym = cfg₁.tape p := by rw [hs_read, hp]
        have hreadmark : st.readSym.1 = SymKind.sel ∨ st.readSym.1 = SymKind.nosel := by
          rw [hread]; exact hmark
        have hpers := markStep_persist (step := st)
          (by rw [hs_from]; exact hleg)
          (by rw [hs_from, hs_read]; exact hs_mem) h101st hreadmark
        rcases hpers with h4 | hw
        · exfalso
          apply hnofour
          rw [roundPositions_cons]
          have hrh : symRoundHead st = true := by simp [symRoundHead, h4]
          rw [if_pos hrh]
          exact List.mem_append_left _ (by simp [hp])
        · rw [hw]
          exact hreadmark
      · rw [symStepConfig_tape_of_ne _ _ hp]
        exact hmark
    exact ih hrest hleg₂ hno101' hmark₂ hnofour'

-- ============================================================
-- 块/标记守恒梁件（表级 decide；for fivePositions_nodup 归纳）
-- ============================================================

/-- 表级：非 5 非 21 步 ⇒ "写 consumed" ⟺ "读 consumed"（consumed 集只由 5/21 改变）。 -/
theorem notFive21_consumed_write_iff (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      r.nextState ≠ 101 → (q : ℕ) ≠ 5 → (q : ℕ) ≠ 21 →
      ((r.writeSym.1 = SymKind.consumed) ↔ (k = SymKind.consumed)) := by
  cases m <;> cases k <;> decide

/-- 表级：非 2 非 4 步 ⇒ "写标记(s/n)" ⟺ "读标记(s/n)"（标记只由 2 造、4 清）。 -/
theorem notTwoFour_mark_write_iff (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      r.nextState ≠ 101 → (q : ℕ) ≠ 2 → (q : ℕ) ≠ 4 →
      ((r.writeSym.1 = SymKind.sel ∨ r.writeSym.1 = SymKind.nosel) ↔
        (k = SymKind.sel ∨ k = SymKind.nosel)) := by
  cases m <;> cases k <;> decide

/-- 表级：入 13（非陷阱）的步读 consumed 且右移（13 链：13 自环 / 81 归队）。 -/
theorem next13_read_consumed_movesR (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      r.nextState ≠ 101 → r.nextState = 13 →
      k = SymKind.consumed ∧ r.moveDir = Dir.R := by
  cases m <;> cases k <;> decide

/-- 表级：自 4 入 5（非陷阱）的步读 sel 且右移（round-head 点火）。 -/
theorem next5_from4_read_sel_movesR (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      r.nextState ≠ 101 → r.nextState = 5 → (q : ℕ) = 4 →
      k = SymKind.sel ∧ r.moveDir = Dir.R := by
  cases m <;> cases k <;> decide

/-- 表级：自 13 入 5（非陷阱）的步读 data 且驻留（13 扫掠首个未消费格）。 -/
theorem next5_from13_read_data_movesS (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      r.nextState ≠ 101 → r.nextState = 5 → (q : ℕ) = 13 →
      (k = SymKind.data0 ∨ k = SymKind.data1) ∧ r.moveDir = Dir.S := by
  cases m <;> cases k <;> decide

/-- 相位簇（只在首个 5 之前出现）。 -/
def symPhaseSet : Finset ℕ := {0, 1, 2, 3, 24, 26, 27, 28, 29, 38}

/-- 表级：相位簇不可逆（入簇 ⇒ 自簇）。 -/
theorem symPhaseSet_step_closed (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      r.nextState ∈ symPhaseSet → (q : ℕ) ∈ symPhaseSet := by
  cases m <;> cases k <;> decide

-- ============================================================
-- E1 件：编码层 α-位置结构（encodeElementsSym 的 α 偏移表）
-- ============================================================

/-- α 偏移表（相对元素区起点）：[0, 1+|b₁|, 1+|b₁|+1+|b₂|, ...]。 -/
def alphaOffsets : List ℕ → List ℕ
  | [] => []
  | v :: rest => 0 :: (alphaOffsets rest).map (fun o => o + (encodeBitsSymNative v).length + 1)

lemma alphaOffsets_length (elems : List ℕ) :
    (alphaOffsets elems).length = elems.length := by
  induction elems with
  | nil => simp [alphaOffsets]
  | cons v rest ih =>
      rw [show alphaOffsets (v :: rest) =
        0 :: (alphaOffsets rest).map (fun o => o + (encodeBitsSymNative v).length + 1) from rfl]
      simp only [List.length_cons, List.length_map]
      omega

lemma alphaOffsets_lt_length (elems : List ℕ) {o : ℕ} (ho : o ∈ alphaOffsets elems) :
    o < (encodeElementsSym elems).length := by
  induction elems generalizing o with
  | nil => simp [alphaOffsets] at ho
  | cons v rest ih =>
      cases rest with
      | nil =>
          rw [show alphaOffsets (v :: []) = [0] from rfl, List.mem_singleton] at ho
          subst ho
          rw [show encodeElementsSym (v :: []) = [Sym.alpha] ++ encodeBitsSymNative v from rfl]
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
      | cons w rest' =>
          rw [show alphaOffsets (v :: w :: rest') =
              0 :: (alphaOffsets (w :: rest')).map
                (fun o => o + (encodeBitsSymNative v).length + 1) from rfl,
              List.mem_cons] at ho
          rcases ho with rfl | hmap
          · rw [show encodeElementsSym (v :: w :: rest') =
                [Sym.alpha] ++ encodeBitsSymNative v ++ encodeElementsSym (w :: rest') from rfl]
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
          · rw [List.mem_map] at hmap
            rcases hmap with ⟨o', ho', rfl⟩
            rw [show encodeElementsSym (v :: w :: rest') =
                [Sym.alpha] ++ encodeBitsSymNative v ++ encodeElementsSym (w :: rest') from rfl]
            have := ih ho'
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega

lemma alphaOffsets_pairwise (elems : List ℕ) :
    (alphaOffsets elems).Pairwise (· < ·) := by
  induction elems with
  | nil => simp [alphaOffsets]
  | cons v rest ih =>
      rw [show alphaOffsets (v :: rest) =
        0 :: (alphaOffsets rest).map (fun o => o + (encodeBitsSymNative v).length + 1) from rfl]
      refine List.pairwise_cons.mpr ⟨?_, ?_⟩
      · intro o ho
        rcases List.mem_map.mp ho with ⟨o', _, rfl⟩
        omega
      · exact ih.map (fun o => o + (encodeBitsSymNative v).length + 1) (fun a b hab => by omega)

/-- E1 主件：元素区格子 kind = α ⟺ 偏移在 α 表中（在区内）。 -/
lemma alpha_iff_mem_offsets (elems : List ℕ) {j : ℕ}
    (hj : j < (encodeElementsSym elems).length) :
    ((encodeElementsSym elems).getD j Sym.blank).1 = SymKind.alpha ↔
      j ∈ alphaOffsets elems := by
  induction elems generalizing j with
  | nil => simp [encodeElementsSym] at hj
  | cons v rest ih =>
      cases rest with
      | nil =>
          cases j with
          | zero =>
              rw [show alphaOffsets (v :: []) = [0] from rfl]
              simp [encodeElementsSym, Sym.alpha]
          | succ k =>
              rw [show alphaOffsets (v :: []) = [0] from rfl]
              have hlen : k < (encodeBitsSymNative v).length := by
                rw [show encodeElementsSym (v :: []) =
                    [Sym.alpha] ++ encodeBitsSymNative v from rfl] at hj
                simp only [List.length_append, List.length_cons, List.length_nil] at hj
                omega
              constructor
              · intro h
                simp only [encodeElementsSym] at h
                change ((encodeBitsSymNative v).getD k Sym.blank).1 = SymKind.alpha at h
                rcases a2p_bits_native_kind v hlen with h0 | h1
                · rw [h0] at h; exact absurd h (by decide)
                · rw [h1] at h; exact absurd h (by decide)
              · intro hmem
                rw [List.mem_singleton] at hmem
                omega
      | cons w rest' =>
          rw [show alphaOffsets (v :: w :: rest') =
              0 :: (alphaOffsets (w :: rest')).map
                (fun o => o + (encodeBitsSymNative v).length + 1) from rfl]
          cases j with
          | zero =>
              simp only [encodeElementsSym]
              simp [Sym.alpha]
          | succ k =>
              simp only [encodeElementsSym]
              by_cases hkb : k < (encodeBitsSymNative v).length
              · constructor
                · intro h
                  change ((encodeBitsSymNative v ++ encodeElementsSym (w :: rest')).getD k
                    Sym.blank).1 = SymKind.alpha at h
                  have hg : (encodeBitsSymNative v ++ encodeElementsSym (w :: rest')).getD k Sym.blank =
                      (encodeBitsSymNative v).getD k Sym.blank :=
                    List.getD_append (encodeBitsSymNative v) (encodeElementsSym (w :: rest'))
                      Sym.blank k hkb
                  rw [hg] at h
                  rcases a2p_bits_native_kind v hkb with h0 | h1
                  · rw [h0] at h; exact absurd h (by decide)
                  · rw [h1] at h; exact absurd h (by decide)
                · intro hmem
                  rw [List.mem_cons] at hmem
                  rcases hmem with h0 | hmap
                  · omega
                  · rw [List.mem_map] at hmap
                    rcases hmap with ⟨o', ho', heq⟩
                    omega
              · constructor
                · intro h
                  change ((encodeBitsSymNative v ++ encodeElementsSym (w :: rest')).getD k
                    Sym.blank).1 = SymKind.alpha at h
                  have hlenv : (encodeBitsSymNative v).length ≤ k := by omega
                  have hg : (encodeBitsSymNative v ++ encodeElementsSym (w :: rest')).getD k Sym.blank =
                      (encodeElementsSym (w :: rest')).getD (k - (encodeBitsSymNative v).length) Sym.blank := by
                    have hh := List.getD_append_right (encodeBitsSymNative v) (encodeElementsSym (w :: rest'))
                      Sym.blank k hlenv
                    simpa using hh
                  rw [hg] at h
                  have hk' : k - (encodeBitsSymNative v).length < (encodeElementsSym (w :: rest')).length := by
                    rw [show encodeElementsSym (v :: w :: rest') =
                        [Sym.alpha] ++ encodeBitsSymNative v ++ encodeElementsSym (w :: rest') from rfl] at hj
                    simp only [List.length_append, List.length_cons, List.length_nil] at hj
                    omega
                  have hiff := ih hk'
                  rw [hiff] at h
                  rw [List.mem_cons]
                  right
                  rw [List.mem_map]
                  exact ⟨k - (encodeBitsSymNative v).length, h, by omega⟩
                · intro hmem
                  rw [List.mem_cons] at hmem
                  rcases hmem with h0 | hmap
                  · omega
                  · rw [List.mem_map] at hmap
                    rcases hmap with ⟨o', ho', heq⟩
                    have hk' : o' < (encodeElementsSym (w :: rest')).length :=
                      alphaOffsets_lt_length (w :: rest') ho'
                    have hiff := ih hk'
                    have hk'' : k - (encodeBitsSymNative v).length < (encodeElementsSym (w :: rest')).length := by omega
                    change ((encodeBitsSymNative v ++ encodeElementsSym (w :: rest')).getD k
                      Sym.blank).1 = SymKind.alpha
                    have hg : (encodeBitsSymNative v ++ encodeElementsSym (w :: rest')).getD k Sym.blank =
                        (encodeElementsSym (w :: rest')).getD (k - (encodeBitsSymNative v).length) Sym.blank := by
                      have hh := List.getD_append_right (encodeBitsSymNative v) (encodeElementsSym (w :: rest'))
                        Sym.blank k (by omega)
                      simpa using hh
                    rw [hg]
                    have hiff2 := ih hk''
                    rw [hiff2]
                    have hkb : k - (encodeBitsSymNative v).length = o' := by omega
                    rw [hkb]
                    exact ho'

-- ============================================================
-- 备用梁件：入 5 源唯一 + 单步 conserved/标记守恒（步级）
-- ============================================================

/-- 表级：非陷阱入 5 的源状态只能是 4 或 13。 -/
theorem next5_fromState_mem (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      r.nextState ≠ 101 → r.nextState = 5 → ((q : ℕ) = 4 ∨ (q : ℕ) = 13) := by
  cases m <;> cases k <;> decide

/-- 步级：非 5 非 21 步（非陷阱）保 consumed 成员关系（任意固定格）。 -/
lemma consumed_mem_step {cfg₁ cfg₂ : SymConfig} {st : SymStep}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (hno101 : st.result.nextState ≠ 101)
    (hne5 : st.fromState ≠ 5) (hne21 : st.fromState ≠ 21) (z : ℤ) :
    ((cfg₂.tape z).1 = SymKind.consumed) ↔ ((cfg₁.tape z).1 = SymKind.consumed) := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  rw [hs_cfg]
  by_cases hz : z = cfg₁.headPos
  · subst hz
    rw [symStepConfig_tape_headPos, ← hs_read]
    have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
    have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
      simpa [← hs_from, ← hs_read] using hs_mem
    exact notFive21_consumed_write_iff st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result
      hm hno101 (by simpa using hne5) (by simpa using hne21)
  · rw [symStepConfig_tape_of_ne _ _ hz]

/-- 步级：非 2 非 4 步（非陷阱）保标记(s/n)成员关系（任意固定格）。 -/
lemma mark_mem_step {cfg₁ cfg₂ : SymConfig} {st : SymStep}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (hno101 : st.result.nextState ≠ 101)
    (hne2 : st.fromState ≠ 2) (hne4 : st.fromState ≠ 4) (z : ℤ) :
    (((cfg₂.tape z).1 = SymKind.sel ∨ (cfg₂.tape z).1 = SymKind.nosel) ↔
      ((cfg₁.tape z).1 = SymKind.sel ∨ (cfg₁.tape z).1 = SymKind.nosel)) := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  rw [hs_cfg]
  by_cases hz : z = cfg₁.headPos
  · subst hz
    rw [symStepConfig_tape_headPos, ← hs_read]
    have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
    have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
      simpa [← hs_from, ← hs_read] using hs_mem
    exact notTwoFour_mark_write_iff st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result
      hm hno101 (by simpa using hne2) (by simpa using hne4)
  · rw [symStepConfig_tape_of_ne _ _ hz]

-- ============================================================
-- 主归纳工具层（片 1）：C1/C2 不变式 + 火点核 + 单步守恒
-- ============================================================

/-- 块不变式（C1）：consumed 格 = 精确区间 [α, p]（空块用 α = p+1 约定）。 -/
def SymBlk (cfg : SymConfig) (α p : ℤ) : Prop :=
  ∀ i : ℤ, (cfg.tape i).1 = SymKind.consumed ↔ α ≤ i ∧ i ≤ p

/-- 标记不变式（C2）：sel/nosel 格全部位于 p 之上。 -/
def SymMarksAbove (cfg : SymConfig) (p : ℤ) : Prop :=
  ∀ i : ℤ, ((cfg.tape i).1 = SymKind.sel ∨ (cfg.tape i).1 = SymKind.nosel) → p < i

lemma SymMarksAbove.mark_gt {cfg : SymConfig} {p : ℤ} (h : SymMarksAbove cfg p)
    {z : ℤ} (hz : (cfg.tape z).1 = SymKind.sel ∨ (cfg.tape z).1 = SymKind.nosel) : p < z :=
  h z hz

/-- 空块形式：无任何 consumed 格 ⇒ 可表示为区间 [p+1, p]。 -/
lemma SymBlk.of_empty {cfg : SymConfig} {p : ℤ}
    (h : ∀ i : ℤ, (cfg.tape i).1 ≠ SymKind.consumed) : SymBlk cfg (p + 1) p := by
  intro i
  constructor
  · intro hc; exact absurd hc (h i)
  · intro hb; omega

/-- 火点核（F1）：若 (q−1) 格为 consumed、q 格为 data，且块区间精确，则 q = p + 1。 -/
lemma fire13_pos_core {cfg : SymConfig} {α p q : ℤ} (hC1 : SymBlk cfg α p)
    (hpred : (cfg.tape (q - 1)).1 = SymKind.consumed)
    (hread : (cfg.tape q).1 = SymKind.data0 ∨ (cfg.tape q).1 = SymKind.data1) :
    q = p + 1 := by
  have h1 : α ≤ q - 1 ∧ q - 1 ≤ p := (hC1 (q - 1)).mp hpred
  have h2 : ¬(α ≤ q ∧ q ≤ p) := by
    intro hc
    have hcons : (cfg.tape q).1 = SymKind.consumed := (hC1 q).mpr hc
    rcases hread with h | h
    · rw [h] at hcons; exact absurd hcons (by decide)
    · rw [h] at hcons; exact absurd hcons (by decide)
  by_cases hq : q ≤ p
  · exact absurd ⟨by omega, hq⟩ h2
  · omega

/-- C1 单步守恒（非 5 非 21 步）。 -/
lemma SymBlk.step_of_notFive21 {cfg₁ cfg₂ : SymConfig} {st : SymStep}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (hno101 : st.result.nextState ≠ 101)
    (hne5 : st.fromState ≠ 5) (hne21 : st.fromState ≠ 21) {α p : ℤ}
    (hC1 : SymBlk cfg₁ α p) : SymBlk cfg₂ α p := by
  intro i
  rw [consumed_mem_step hst hleg hno101 hne5 hne21 i]
  exact hC1 i

/-- C2 单步守恒（非 2 非 4 步）。 -/
lemma SymMarksAbove.step_of_notTwoFour {cfg₁ cfg₂ : SymConfig} {st : SymStep}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (hno101 : st.result.nextState ≠ 101)
    (hne2 : st.fromState ≠ 2) (hne4 : st.fromState ≠ 4) {p : ℤ}
    (hC2 : SymMarksAbove cfg₁ p) : SymMarksAbove cfg₂ p := by
  intro i hi
  rw [mark_mem_step hst hleg hno101 hne2 hne4 i] at hi
  exact hC2 i hi

/-- C1 更新（13 源火：q = p+1 处消费 ⇒ 块右端推进到 p+1）。 -/
lemma SymBlk.fire13_update {cfg₁ cfg₂ : SymConfig} {st : SymStep} {α p : ℤ}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hw : st.result.writeSym.1 = SymKind.consumed)
    (hα : α ≤ p + 1) (hC1 : SymBlk cfg₁ α p)
    (hq : cfg₁.headPos = p + 1) : SymBlk cfg₂ α (p + 1) := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  intro i
  rw [hs_cfg]
  by_cases hi : i = cfg₁.headPos
  · subst hi
    rw [symStepConfig_tape_headPos, hw, hq]
    exact ⟨fun _ => ⟨hα, le_refl _⟩, fun _ => rfl⟩
  · rw [symStepConfig_tape_of_ne _ _ hi]
    have h := hC1 i
    refine ⟨fun hc => ?_, fun hb => h.mpr ⟨hb.1, ?_⟩⟩
    · have hb := h.mp hc
      exact ⟨hb.1, by omega⟩
    · have hne : i ≠ p + 1 := fun h => hi (h.trans hq.symm)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · omega
      · omega

/-- C1 更新（4 源火：块先空、火在 q ⇒ 新块 [q, q]）。 -/
lemma SymBlk.fire4_update {cfg₁ cfg₂ : SymConfig} {st : SymStep} {q : ℤ} {α p : ℤ}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hw : st.result.writeSym.1 = SymKind.consumed)
    (hempty : ∀ i : ℤ, ¬(α ≤ i ∧ i ≤ p)) (hC1 : SymBlk cfg₁ α p)
    (hq : cfg₁.headPos = q) : SymBlk cfg₂ q q := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  intro i
  rw [hs_cfg]
  by_cases hi : i = cfg₁.headPos
  · subst hi
    rw [symStepConfig_tape_headPos, hw, hq]
    exact ⟨fun _ => ⟨le_refl _, le_refl _⟩, fun _ => rfl⟩
  · rw [symStepConfig_tape_of_ne _ _ hi]
    have hne : i ≠ q := fun h => hi (h.trans hq.symm)
    have hnot : (cfg₁.tape i).1 ≠ SymKind.consumed := fun hc => hempty i ((hC1 i).mp hc)
    refine ⟨fun hc => absurd hc hnot, fun hb => ?_⟩
    exfalso
    exact hne (by omega)

-- ============================================================
-- 主归纳工具层（片 2）：α 格恒域（C0′）——α-位置 + 无创造 + 单步保持 + 初始带桥
-- ============================================================

/-- 元素区起点（encS 内偏移）：[#ₗ] + target 位 + [#₀] = |target| + 2。 -/
def encPrefixLen (inst : SubsetSumInstance) : ℕ := (encodeBitsSym inst.target).length + 2

/-- α 位置（绝对坐标）：z = encPrefixLen + o，o ∈ alphaOffsets。 -/
def SymAlphaPos (inst : SubsetSumInstance) (z : ℤ) : Prop :=
  ∃ o : ℕ, o ∈ alphaOffsets inst.elements ∧ z = ((encPrefixLen inst + o : ℕ) : ℤ)

/-- 表级：写 α 的合法非陷阱步，读 kind 也必为 α（机器无 α-创造）。 -/
theorem write_alpha_read_alpha (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      r.nextState ≠ 101 → r.writeSym.1 = SymKind.alpha → k = SymKind.alpha := by
  cases m <;> cases k <;> decide

/-- C0′ 单步保持：kind-α 只在 α 位置（对任意步，非陷阱）。 -/
lemma alphaPos_step {inst : SubsetSumInstance} {cfg₁ cfg₂ : SymConfig} {st : SymStep}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (hno101 : st.result.nextState ≠ 101)
    (h0 : ∀ z : ℤ, (cfg₁.tape z).1 = SymKind.alpha → SymAlphaPos inst z) :
    ∀ z : ℤ, (cfg₂.tape z).1 = SymKind.alpha → SymAlphaPos inst z := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  intro z hz
  rw [hs_cfg] at hz
  by_cases hzc : z = cfg₁.headPos
  · subst hzc
    rw [symStepConfig_tape_headPos] at hz
    have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
    have hm : st.result ∈ VerifierSym.transition (st.fromState, st.readSym.1, st.readSym.2) := by
      simpa [← hs_from, ← hs_read] using hs_mem
    have hk := write_alpha_read_alpha st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
      hno101 hz
    exact h0 cfg₁.headPos (by rw [← hs_read]; exact hk)
  · rw [symStepConfig_tape_of_ne _ _ hzc] at hz
    exact h0 z hz

/-- (a :: t).getD 0 = a。 -/
lemma symGetD_cons_zero (a : Sym) (t : List Sym) : (a :: t).getD 0 Sym.blank = a := rfl

/-- getD 越界默认值：n ≥ 长度时 getD = 默认值。 -/
lemma getD_eq_default_of_length_le (l : List Sym) {n : ℕ} (h : l.length ≤ n) :
    l.getD n Sym.blank = Sym.blank := by
  induction l generalizing n with
  | nil => simp
  | cons a t ih =>
      cases n with
      | zero => simp only [List.length_cons] at h; omega
      | succ n => rw [List.getD_cons_succ]; exact ih (by simpa using h)

/-- 初始带桥（E1 带版，方向 1）：初始带上 kind-α 的格子必在 α 位置。 -/
lemma symInitialConfig_alpha_pos (inst : SubsetSumInstance) :
    ∀ z : ℤ, ((symInitialConfig (encodeInstanceSym inst)).tape z).1 = SymKind.alpha →
      SymAlphaPos inst z := by
  intro z hz
  by_cases hz0 : 0 ≤ z
  · have hget : (symInitialConfig (encodeInstanceSym inst)).tape z =
        (encodeInstanceSym inst).getD z.toNat Sym.blank := by
      show (if h : 0 ≤ z ∧ z.toNat < (encodeInstanceSym inst).length then
          (encodeInstanceSym inst).get ⟨z.toNat, h.2⟩ else Sym.blank) =
        (encodeInstanceSym inst).getD z.toNat Sym.blank
      by_cases hin : z.toNat < (encodeInstanceSym inst).length
      · rw [dif_pos ⟨hz0, hin⟩]
        exact (List.getD_eq_getElem (encodeInstanceSym inst) Sym.blank hin).symm
      · rw [dif_neg (by intro h; exact hin h.2)]
        exact (getD_eq_default_of_length_le (encodeInstanceSym inst) (by omega)).symm
    rw [hget] at hz
    set n := z.toNat with hn
    have hzn : (n : ℤ) = z := by rw [hn]; exact Int.toNat_of_nonneg hz0
    -- 右起四分：whole = Q ++ [b]；Q = Q₂ ++ elements；Q₂ = ([b] ++ bits) ++ [b]
    set Q₂ : List Sym := ([Sym.boundary] ++ encodeBitsSym inst.target) ++ [Sym.boundary] with hQ₂
    set Q : List Sym := Q₂ ++ encodeElementsSym inst.elements with hQ
    have hwhole : encodeInstanceSym inst = Q ++ [Sym.boundary] := by rw [hQ, hQ₂]; rfl
    have hQ₂len : Q₂.length = encPrefixLen inst := by
      rw [hQ₂, encPrefixLen]; simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hQlen : Q.length = encPrefixLen inst + (encodeElementsSym inst.elements).length := by
      rw [hQ, List.length_append, hQ₂len]
    by_cases hdrop : Q.length ≤ n
    · -- 尾区：最后一格 #₁ 或越界
      have h := List.getD_append_right Q [Sym.boundary] Sym.blank n hdrop
      rw [hwhole, h] at hz
      by_cases hlast : n - Q.length = 0
      · rw [hlast] at hz
        rw [symGetD_cons_zero Sym.boundary []] at hz
        exact absurd hz (by decide)
      · have hnn : ([Sym.boundary] : List Sym).length ≤ n - Q.length := by
          simp only [List.length_cons, List.length_nil]; omega
        rw [getD_eq_default_of_length_le [Sym.boundary] hnn] at hz
        exact absurd hz (by decide)
    · by_cases hdrop₂ : Q₂.length ≤ n
      · -- 元素区：a2p_enc_elems_getD 的等价移位 + E1
        have hlt : n < Q.length := by omega
        have h0 : (Q ++ [Sym.boundary]).getD n Sym.blank = Q.getD n Sym.blank :=
          List.getD_append Q [Sym.boundary] Sym.blank n hlt
        rw [hwhole, h0, hQ] at hz
        have h1 : (Q₂ ++ encodeElementsSym inst.elements).getD n Sym.blank =
            (encodeElementsSym inst.elements).getD (n - Q₂.length) Sym.blank :=
          List.getD_append_right Q₂ (encodeElementsSym inst.elements) Sym.blank n hdrop₂
        rw [h1] at hz
        have hj : n - Q₂.length < (encodeElementsSym inst.elements).length := by
          rw [hQlen] at hdrop; omega
        have hmem := (alpha_iff_mem_offsets inst.elements hj).mp hz
        refine ⟨n - Q₂.length, hmem, ?_⟩
        rw [← hzn, ← hQ₂len]
        push_cast
        omega
      · -- 前缀内部：中间 [b] 格 / bits 区 / 首格 #ₗ —— 全部 kind ≠ α
        exfalso
        have hlt : n < Q.length := by omega
        have h0 : (Q ++ [Sym.boundary]).getD n Sym.blank = Q.getD n Sym.blank :=
          List.getD_append Q [Sym.boundary] Sym.blank n hlt
        rw [hwhole, h0, hQ] at hz
        have h1 : (Q₂ ++ encodeElementsSym inst.elements).getD n Sym.blank =
            Q₂.getD n Sym.blank :=
          List.getD_append Q₂ (encodeElementsSym inst.elements) Sym.blank n (by omega)
        rw [h1] at hz
        rw [hQ₂] at hz
        have hQ₂split : Q₂.length = ([Sym.boundary] ++ encodeBitsSym inst.target).length + 1 := by
          rw [hQ₂]; simp only [List.length_append, List.length_cons, List.length_nil]
        by_cases hdrop₃ : ([Sym.boundary] ++ encodeBitsSym inst.target).length ≤ n
        · -- 中间 [b] 格
          have hnn : n = ([Sym.boundary] ++ encodeBitsSym inst.target).length := by omega
          rw [hnn] at hz
          have h3 := List.getD_append_right ([Sym.boundary] ++ encodeBitsSym inst.target)
            [Sym.boundary] Sym.blank ([Sym.boundary] ++ encodeBitsSym inst.target).length
            (le_refl _)
          rw [h3] at hz
          rw [show ([Sym.boundary] ++ encodeBitsSym inst.target).length -
              ([Sym.boundary] ++ encodeBitsSym inst.target).length = 0 from Nat.sub_self _] at hz
          rw [symGetD_cons_zero Sym.boundary []] at hz
          exact absurd hz (by decide)
        · -- bits 区（含 n = 0）
          have hbits : n < ([Sym.boundary] ++ encodeBitsSym inst.target).length := by omega
          rcases Nat.eq_zero_or_pos n with hn0 | hnpos
          · rw [hn0] at hz
            have h4 : (([Sym.boundary] ++ encodeBitsSym inst.target) ++ [Sym.boundary]).getD 0
                Sym.blank = ([Sym.boundary] ++ encodeBitsSym inst.target).getD 0 Sym.blank :=
              List.getD_append ([Sym.boundary] ++ encodeBitsSym inst.target) [Sym.boundary]
                Sym.blank 0 (by simp)
            rw [h4] at hz
            have h5 := List.getD_append [Sym.boundary] (encodeBitsSym inst.target) Sym.blank 0
              (by simp)
            rw [h5] at hz
            rw [symGetD_cons_zero Sym.boundary []] at hz
            exact absurd hz (by decide)
          · have h4 : (([Sym.boundary] ++ encodeBitsSym inst.target) ++ [Sym.boundary]).getD n
                Sym.blank = ([Sym.boundary] ++ encodeBitsSym inst.target).getD n Sym.blank :=
              List.getD_append ([Sym.boundary] ++ encodeBitsSym inst.target) [Sym.boundary]
                Sym.blank n hbits
            rw [h4] at hz
            have h3 := List.getD_append_right [Sym.boundary] (encodeBitsSym inst.target)
              Sym.blank n (by show 1 ≤ n; omega)
            rw [h3] at hz
            rw [show ([Sym.boundary] : List Sym).length = 1 from rfl] at hz
            rw [show encodeBitsSym inst.target = encodeBitsSymNative inst.target from rfl] at hz
            have hbl : ([Sym.boundary] ++ encodeBitsSym inst.target).length =
                (encodeBitsSym inst.target).length + 1 := by
              simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
              omega
            have hj : n - 1 < (encodeBitsSym inst.target).length := by omega
            rcases a2p_bits_native_kind inst.target hj with hk | hk
            · rw [hk] at hz; exact absurd hz (by decide)
            · rw [hk] at hz; exact absurd hz (by decide)
  · -- z < 0：带值 = blank
    exfalso
    have hblank : (symInitialConfig (encodeInstanceSym inst)).tape z = Sym.blank := by
      show (if h : 0 ≤ z ∧ z.toNat < (encodeInstanceSym inst).length then
          (encodeInstanceSym inst).get ⟨z.toNat, h.2⟩ else Sym.blank) = Sym.blank
      rw [dif_neg (by intro h; exact hz0 h.1)]
    rw [hblank] at hz
    exact absurd hz (by decide)

-- ============================================================
-- 主归纳工具层（片 3）：C4 标记账本——marked ⟺ (α-位置 ∧ q₄ < z)
-- ============================================================

/-- 标记谓词：kind 为 sel/nosel（s/n 格）。 -/
abbrev SymMarked (cfg : SymConfig) (z : ℤ) : Prop :=
  (cfg.tape z).1 = SymKind.sel ∨ (cfg.tape z).1 = SymKind.nosel

/-- 标记账本（C4）：marked ⟺ (α-位置 ∧ q₄ < z)。 -/
def SymLedger (inst : SubsetSumInstance) (cfg : SymConfig) (q₄ : ℤ) : Prop :=
  ∀ z : ℤ, SymMarked cfg z ↔ SymAlphaPos inst z ∧ q₄ < z

/-- 表级：2 步（非陷阱）写标记 ⟹ 读 α（标记只由未标记 α 格创造）。 -/
theorem state2_writeMark_read_alpha (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 2 → r.nextState ≠ 101 →
      (r.writeSym.1 = SymKind.sel ∨ r.writeSym.1 = SymKind.nosel) → k = SymKind.alpha := by
  cases m <;> cases k <;> decide

/-- 表级：2 步读标记格 ⟹ 陷阱（nextState = 101）。 -/
theorem state2_readMark_trap (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 2 → (k = SymKind.sel ∨ k = SymKind.nosel) → r.nextState = 101 := by
  cases m <;> cases k <;> decide

/-- 表级：4 步（非陷阱）读标记格且写 d0-（清标记）。 -/
theorem state4_readMark_write_d0 (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 4 → r.nextState ≠ 101 →
      (k = SymKind.sel ∨ k = SymKind.nosel) ∧ r.writeSym.1 = SymKind.data0 := by
  cases m <;> cases k <;> decide

/-- C4 单步保持（非 2 非 4 步：标记集与 q₄ 均不变；含 21——21 行 s/n 恒等）。 -/
lemma ledger_notTwoFour {inst : SubsetSumInstance} {cfg₁ cfg₂ : SymConfig} {st : SymStep}
    {q₄ : ℤ}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (hno101 : st.result.nextState ≠ 101)
    (hne2 : st.fromState ≠ 2) (hne4 : st.fromState ≠ 4)
    (hC4 : SymLedger inst cfg₁ q₄) :
    SymLedger inst cfg₂ q₄ := by
  intro z
  have hmm := mark_mem_step hst hleg hno101 hne2 hne4 z
  constructor
  · intro h; exact (hC4 z).mp (hmm.mp h)
  · intro h; exact hmm.mpr ((hC4 z).mpr h)

/-- C4 单步保持（2 步：在 α 格创造标记；q₄ 不变）。
    需 C0′（kind-α ⇒ α-位置）与 q₄ 低于一切 α-位置（初始相）。 -/
lemma ledger_two {inst : SubsetSumInstance} {cfg₁ cfg₂ : SymConfig} {st : SymStep} {q₄ : ℤ}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (hno101 : st.result.nextState ≠ 101)
    (hfrom : st.fromState = 2)
    (hC4 : SymLedger inst cfg₁ q₄)
    (hα : ∀ z : ℤ, (cfg₁.tape z).1 = SymKind.alpha → SymAlphaPos inst z)
    (hqα : ∀ z : ℤ, SymAlphaPos inst z → q₄ < z) :
    SymLedger inst cfg₂ q₄ := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  intro z
  unfold SymMarked
  rw [hs_cfg]
  by_cases hz : z = cfg₁.headPos
  · subst hz
    rw [symStepConfig_tape_headPos]
    by_cases hw : st.result.writeSym.1 = SymKind.sel ∨ st.result.writeSym.1 = SymKind.nosel
    · have hk : st.readSym.1 = SymKind.alpha :=
        state2_writeMark_read_alpha st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
          (by simpa using hfrom) hno101 hw
      have hαp : SymAlphaPos inst cfg₁.headPos :=
        hα cfg₁.headPos (by rw [← hs_read]; exact hk)
      constructor
      · intro _
        exact ⟨hαp, hqα cfg₁.headPos hαp⟩
      · intro _
        exact hw
    · constructor
      · intro h
        exact absurd h hw
      · intro h
        exfalso
        have hmk : (cfg₁.tape cfg₁.headPos).1 = SymKind.sel ∨
            (cfg₁.tape cfg₁.headPos).1 = SymKind.nosel :=
          (hC4 cfg₁.headPos).mpr h
        have hsr : st.readSym.1 = SymKind.sel ∨ st.readSym.1 = SymKind.nosel := by
          rw [hs_read]; exact hmk
        exact hno101 (state2_readMark_trap st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩
          st.result hm (by simpa using hfrom) hsr)
  · rw [symStepConfig_tape_of_ne _ _ hz]
    exact hC4 z

/-- C4 单步保持（4 步：清 head 标记、q₄ ← head；需无 α-位置夹在 (q₄, head) 之间）。 -/
lemma ledger_four {inst : SubsetSumInstance} {cfg₁ cfg₂ : SymConfig} {st : SymStep} {q₄ : ℤ}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (hno101 : st.result.nextState ≠ 101)
    (hfrom : st.fromState = 4)
    (hC4 : SymLedger inst cfg₁ q₄)
    (hnα : ∀ z : ℤ, q₄ < z → z < cfg₁.headPos → ¬ SymAlphaPos inst z) :
    SymLedger inst cfg₂ cfg₁.headPos := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  have hmd := state4_readMark_write_d0 st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
    (by simpa using hfrom) hno101
  have hqhead : q₄ < cfg₁.headPos := by
    have hmk : (cfg₁.tape cfg₁.headPos).1 = SymKind.sel ∨
        (cfg₁.tape cfg₁.headPos).1 = SymKind.nosel := by
      rw [← hs_read]; exact hmd.1
    exact ((hC4 cfg₁.headPos).mp hmk).2
  intro z
  unfold SymMarked
  rw [hs_cfg]
  by_cases hz : z = cfg₁.headPos
  · subst hz
    rw [symStepConfig_tape_headPos, hmd.2]
    constructor
    · intro h
      rcases h with h | h <;> exact absurd h (by decide)
    · intro h
      exact absurd h.2 (lt_irrefl _)
  · rw [symStepConfig_tape_of_ne _ _ hz]
    constructor
    · intro h
      have hP := (hC4 z).mp h
      refine ⟨hP.1, ?_⟩
      by_contra hcon
      have hzlt : z < cfg₁.headPos := by
        have hle : z ≤ cfg₁.headPos := le_of_not_gt hcon
        omega
      exact (hnα z hP.2 hzlt) hP.1
    · intro h
      exact (hC4 z).mpr ⟨h.1, lt_trans hqhead h.2⟩

-- ============================================================
-- 主归纳工具层（片 4）：C1 块·21 清扫步（B4′ 守卫）
-- （headPos 投影件 = StepBound:3610 `symStepConfig_headPos`，已可达。）
-- ============================================================

/-- 表级：21 步不写 consumed（写 ∈ {d0, s/n, #}——仅清扫与恒等）。 -/
theorem state21_write_not_consumed (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 21 → r.writeSym.1 ≠ SymKind.consumed := by
  cases m <;> cases k <;> decide

/-- B4′（清态形式）：21 步读 consumed 且守卫（consumed 格 ≥ head）⇒ 清格 = 块左端，
    块由 [α, p] 缩为 [α+1, p]（左端单步推进）。 -/
lemma SymBlk.step_21_clear {cfg₁ cfg₂ : SymConfig} {st : SymStep} {α p : ℤ}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (_hno101 : st.result.nextState ≠ 101)
    (hfrom : st.fromState = 21)
    (hread : st.readSym.1 = SymKind.consumed)
    (hC1 : SymBlk cfg₁ α p)
    (hG : ∀ i : ℤ, (cfg₁.tape i).1 = SymKind.consumed → cfg₁.headPos ≤ i) :
    SymBlk cfg₂ (α + 1) p := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  have hwrite : st.result.writeSym.1 ≠ SymKind.consumed :=
    state21_write_not_consumed st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
      (by simpa using hfrom)
  have hkind : (cfg₁.tape cfg₁.headPos).1 = SymKind.consumed := by
    rw [← hs_read]; exact hread
  have hcons : α ≤ cfg₁.headPos ∧ cfg₁.headPos ≤ p := (hC1 cfg₁.headPos).mp hkind
  have hGα : cfg₁.headPos ≤ α := hG α ((hC1 α).mpr ⟨le_refl α, le_trans hcons.1 hcons.2⟩)
  have hheq : cfg₁.headPos = α := by omega
  intro i
  rw [hs_cfg]
  by_cases hi : i = cfg₁.headPos
  · subst hi
    rw [symStepConfig_tape_headPos]
    constructor
    · intro hc; exact absurd hc hwrite
    · intro hb; exfalso; omega
  · rw [symStepConfig_tape_of_ne _ _ hi]
    have hne : i ≠ α := fun h => hi (h.trans hheq.symm)
    constructor
    · intro hc
      have hb := (hC1 i).mp hc
      exact ⟨by omega, hb.2⟩
    · intro hb
      exact (hC1 i).mpr ⟨by omega, hb.2⟩

/-- B4′（保态形式）：21 步读非 consumed ⇒ 块不变（清扫已过格 / 恒等格 / 停格）。 -/
lemma SymBlk.step_21_keep {cfg₁ cfg₂ : SymConfig} {st : SymStep} {α p : ℤ}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (_hno101 : st.result.nextState ≠ 101)
    (hfrom : st.fromState = 21)
    (hread : st.readSym.1 ≠ SymKind.consumed)
    (hC1 : SymBlk cfg₁ α p) :
    SymBlk cfg₂ α p := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  have hwrite : st.result.writeSym.1 ≠ SymKind.consumed :=
    state21_write_not_consumed st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
      (by simpa using hfrom)
  intro i
  rw [hs_cfg]
  by_cases hi : i = cfg₁.headPos
  · subst hi
    rw [symStepConfig_tape_headPos]
    constructor
    · intro hc; exact absurd hc hwrite
    · intro hb; exfalso
      have hkind : st.readSym.1 = SymKind.consumed := by
        rw [hs_read]; exact (hC1 cfg₁.headPos).mpr hb
      exact hread hkind
  · rw [symStepConfig_tape_of_ne _ _ hi]
    exact hC1 i

-- ============================================================
-- 主归纳工具层（片 5）：火记号 + 块内无标记 + 停格越块（停格论证砖）
-- ============================================================

/-- 表级：5 步（非陷阱）读 data 且写 c-（火记号：c- 只由 5 在数据格上产生）。 -/
theorem state5_readData_writeConsumed (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 5 → r.nextState ≠ 101 →
      (k = SymKind.data0 ∨ k = SymKind.data1) ∧ r.writeSym.1 = SymKind.consumed := by
  cases m <;> cases k <;> decide

/-- 块内无标记：块区间无 α-位置 + 账本 ⇒ 块内无标记格（停格与火位的公共砖）。 -/
lemma SymBlk.not_marked_of_no_alphaPos {inst : SubsetSumInstance} {cfg : SymConfig}
    {q₄ α p : ℤ}
    (_hC1 : SymBlk cfg α p) (hC4 : SymLedger inst cfg q₄)
    (hnα : ∀ z : ℤ, α ≤ z → z ≤ p → ¬ SymAlphaPos inst z) :
    ∀ z : ℤ, α ≤ z → z ≤ p → ¬ SymMarked cfg z := by
  intro z h1 h2 hM
  exact hnα z h1 h2 ((hC4 z).mp hM).1

/-- 停格不由块内触发：21 步读标记（停格）且 head ≥ α（行程后件）⇒ 停格 > p。 -/
lemma SymBlk.step_21_stop_not_in_block {inst : SubsetSumInstance} {cfg₁ cfg₂ : SymConfig}
    {st : SymStep} {q₄ α p : ℤ}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (_hfrom : st.fromState = 21)
    (hread : st.readSym.1 = SymKind.sel ∨ st.readSym.1 = SymKind.nosel)
    (hlo : α ≤ cfg₁.headPos)
    (hC1 : SymBlk cfg₁ α p) (hC4 : SymLedger inst cfg₁ q₄)
    (hnα : ∀ z : ℤ, α ≤ z → z ≤ p → ¬ SymAlphaPos inst z) :
    p < cfg₁.headPos := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  by_contra hcon
  have hb : α ≤ cfg₁.headPos ∧ cfg₁.headPos ≤ p := by omega
  have htape : (cfg₁.tape cfg₁.headPos).1 = SymKind.sel ∨
      (cfg₁.tape cfg₁.headPos).1 = SymKind.nosel := by
    rw [← hs_read]; exact hread
  exact (SymBlk.not_marked_of_no_alphaPos hC1 hC4 hnα cfg₁.headPos hb.1 hb.2) htape

-- ============================================================
-- 主归纳工具层（片 6）：行程表件 + 无 α 间隙（SymGapNoAlpha 贯穿件）
-- ============================================================

/-- 表级：21 步续行（仍为 21）⇒ 右移且读非标记。 -/
theorem state21_continue (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 21 → r.nextState = 21 →
      r.moveDir = Dir.R ∧ ¬(k = SymKind.sel ∨ k = SymKind.nosel) := by
  cases m <;> cases k <;> decide

/-- 表级：21 步读标记（停格）⇒ 51、左移、写 kind = 读 kind（恒等保标记）。 -/
theorem state21_stop (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 21 → (k = SymKind.sel ∨ k = SymKind.nosel) →
      r.nextState = 51 ∧ r.moveDir = Dir.L ∧ r.writeSym.1 = k := by
  cases m <;> cases k <;> decide

/-- 表级：51 盖章步（非陷阱）⇒ 读 d0、写 #-、右移至 4。 -/
theorem state51_stamp (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 51 → r.nextState ≠ 101 →
      k = SymKind.data0 ∧ r.writeSym.1 = SymKind.boundary ∧ r.moveDir = Dir.R := by
  cases m <;> cases k <;> decide

/-- 表级：20 入 21（非陷阱）⇒ 读 #-、写 d0-、右移。 -/
theorem state20_enter (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 20 → r.nextState ≠ 101 →
      k = SymKind.boundary ∧ r.writeSym.1 = SymKind.data0 ∧ r.moveDir = Dir.R := by
  cases m <;> cases k <;> decide

/-- 无 α 间隙（行程件）：q₄ 与带头之间无 α-位置（清扫推进的几何账）。 -/
def SymGapNoAlpha (inst : SubsetSumInstance) (q₄ : ℤ) (cfg : SymConfig) : Prop :=
  ∀ z : ℤ, q₄ < z → z < cfg.headPos → ¬ SymAlphaPos inst z

/-- 21 续行步保持无 α 间隙（头右进一格；新格读非标记 ⇒ 账本否定 ⇒ 无 α）。 -/
lemma SymGapNoAlpha.step_21_continue {inst : SubsetSumInstance} {cfg₁ cfg₂ : SymConfig}
    {st : SymStep} {q₄ : ℤ}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (_hno101 : st.result.nextState ≠ 101)
    (hfrom : st.fromState = 21)
    (hcont : st.result.nextState = 21)
    (hGap : SymGapNoAlpha inst q₄ cfg₁)
    (hC4 : SymLedger inst cfg₁ q₄) :
    SymGapNoAlpha inst q₄ cfg₂ := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  have hcont' := state21_continue st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
    (by simpa using hfrom) hcont
  have hhead : cfg₂.headPos = cfg₁.headPos + 1 := by
    rw [hs_cfg, symStepConfig_headPos, hcont'.1]; rfl
  intro z h1 h2
  rw [hhead] at h2
  by_cases hz : z = cfg₁.headPos
  · subst hz
    have hnm : ¬ SymMarked cfg₁ cfg₁.headPos := by
      intro hM
      rw [SymMarked] at hM
      rcases hM with h | h
      · rw [← hs_read] at h; exact hcont'.2 (Or.inl h)
      · rw [← hs_read] at h; exact hcont'.2 (Or.inr h)
    intro hα
    exact hnm ((hC4 cfg₁.headPos).mpr ⟨hα, h1⟩)
  · exact hGap z h1 (by omega)

/-- 21 停格步保持无 α 间隙（范围收缩：头由 z 左移至 z−1）。 -/
lemma SymGapNoAlpha.step_21_stop {inst : SubsetSumInstance} {cfg₁ cfg₂ : SymConfig}
    {st : SymStep} {q₄ : ℤ}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (hread : st.readSym.1 = SymKind.sel ∨ st.readSym.1 = SymKind.nosel)
    (hfrom : st.fromState = 21)
    (hGap : SymGapNoAlpha inst q₄ cfg₁) :
    SymGapNoAlpha inst q₄ cfg₂ := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  have hstop := state21_stop st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
    (by simpa using hfrom) hread
  have hhead : cfg₂.headPos = cfg₁.headPos - 1 := by
    rw [hs_cfg, symStepConfig_headPos, hstop.2.1]; rfl
  intro z h1 h2
  rw [hhead] at h2
  exact hGap z h1 (by omega)

/-- 51 盖章步推进无 α 间隙：头由 z−1 右移至 z；z−1 格读 d0（非标记）+ q₄ < head ⇒ 无 α。 -/
lemma SymGapNoAlpha.step_51 {inst : SubsetSumInstance} {cfg₁ cfg₂ : SymConfig}
    {st : SymStep} {q₄ : ℤ}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (hno101 : st.result.nextState ≠ 101)
    (hfrom : st.fromState = 51)
    (hlow : q₄ < cfg₁.headPos)
    (hGap : SymGapNoAlpha inst q₄ cfg₁)
    (hC4 : SymLedger inst cfg₁ q₄) :
    SymGapNoAlpha inst q₄ cfg₂ := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  have hstamp := state51_stamp st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
    (by simpa using hfrom) hno101
  have hhead : cfg₂.headPos = cfg₁.headPos + 1 := by
    rw [hs_cfg, symStepConfig_headPos, hstamp.2.2]; rfl
  intro z h1 h2
  rw [hhead] at h2
  by_cases hz : z = cfg₁.headPos
  · subst hz
    have hnm : ¬ SymMarked cfg₁ cfg₁.headPos := by
      intro hM
      rw [SymMarked] at hM
      rcases hM with h | h
      · rw [← hs_read] at h; rw [hstamp.1] at h; exact absurd h (by decide)
      · rw [← hs_read] at h; rw [hstamp.1] at h; exact absurd h (by decide)
    intro hα
    exact hnm ((hC4 cfg₁.headPos).mpr ⟨hα, hlow⟩)
  · exact hGap z h1 (by omega)

-- ============================================================
-- 主归纳工具层（片 7）：13-走廊不变式（SymWalkConsumed——fire13 的 hpred 供应）
-- ============================================================

/-- 表级：13 步续行（仍为 13）⇒ 读 c-、写 c-、右移。 -/
theorem state13_continue (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 13 → r.nextState = 13 →
      k = SymKind.consumed ∧ r.writeSym.1 = SymKind.consumed ∧ r.moveDir = Dir.R := by
  cases m <;> cases k <;> decide

/-- 表级：81 步读 c-（走廊入口）⇒ 13、写 c-、右移。 -/
theorem state81_exit (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 81 → k = SymKind.consumed →
      r.nextState = 13 ∧ r.writeSym.1 = SymKind.consumed ∧ r.moveDir = Dir.R := by
  cases m <;> cases k <;> decide

/-- 13-走廊不变式：从 s 到带头之间全为 consumed（81 出口建立、13 续行延伸）。 -/
def SymWalkConsumed (cfg : SymConfig) (s : ℤ) : Prop :=
  ∀ z : ℤ, s ≤ z → z < cfg.headPos → (cfg.tape z).1 = SymKind.consumed

/-- 走廊 hpred 供应件：s < 带头 ⇒ 前格为 consumed（fire13_pos_core 的 hpred）。 -/
lemma SymWalkConsumed.hpred {cfg : SymConfig} {s : ℤ} (hW : SymWalkConsumed cfg s)
    (hq : s < cfg.headPos) :
    (cfg.tape (cfg.headPos - 1)).1 = SymKind.consumed :=
  hW _ (by omega) (by omega)

/-- 走廊平凡形态：s := 带头+1（空区间——非走廊相的重置件）。 -/
lemma SymWalkConsumed.trivial (cfg : SymConfig) : SymWalkConsumed cfg (cfg.headPos + 1) := by
  intro z h1 h2; omega

/-- 13 续行步延伸走廊（新格读 c-、头进一格）。 -/
lemma SymWalkConsumed.step_13_continue {cfg₁ cfg₂ : SymConfig} {st : SymStep} {s : ℤ}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (hfrom : st.fromState = 13)
    (hcont : st.result.nextState = 13)
    (hW : SymWalkConsumed cfg₁ s) :
    SymWalkConsumed cfg₂ s := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  have hcont' := state13_continue st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
    (by simpa using hfrom) hcont
  have hhead : cfg₂.headPos = cfg₁.headPos + 1 := by
    rw [hs_cfg, symStepConfig_headPos, hcont'.2.2]; rfl
  intro z h1 h2
  rw [hhead] at h2
  by_cases hz : z = cfg₁.headPos
  · subst hz
    rw [hs_cfg, symStepConfig_tape_headPos]
    exact hcont'.2.1
  · rw [hs_cfg, symStepConfig_tape_of_ne _ _ hz]
    exact hW z h1 (by omega)

/-- 81 出口步建立走廊（s := 出口格；出口读 c-、写 c-、右移）。 -/
lemma SymWalkConsumed.step_81_exit {cfg₁ cfg₂ : SymConfig} {st : SymStep}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (hfrom : st.fromState = 81)
    (hread : st.readSym.1 = SymKind.consumed) :
    SymWalkConsumed cfg₂ cfg₁.headPos := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  have hx := state81_exit st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
    (by simpa using hfrom) hread
  have hhead : cfg₂.headPos = cfg₁.headPos + 1 := by
    rw [hs_cfg, symStepConfig_headPos, hx.2.2]; rfl
  intro z h1 h2
  rw [hhead] at h2
  have hz : z = cfg₁.headPos := by omega
  subst hz
  rw [hs_cfg, symStepConfig_tape_headPos]
  exact hx.2.1

-- ============================================================
-- 主归纳工具层（片 8）：非标记不可逆（c-8 装置通用化）+ 已清扫区无标记 + 停格越块 v2
-- ============================================================

/-- 表级：21 步读 c-（清扫格）⇒ 写 d0-。 -/
theorem state21_read_consumed_write_d0 (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 21 → k = SymKind.consumed → r.writeSym.1 = SymKind.data0 := by
  cases m <;> cases k <;> decide

/-- 非标记不可逆（通用步级）：非标记格在任一步后仍非标记（c-8 装置的逐格形式）。 -/
lemma notMarked_step {cfg₁ cfg₂ : SymConfig} {st : SymStep} {z : ℤ}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (hno101 : st.result.nextState ≠ 101)
    (hz : Sym.notMarked (cfg₁.tape z)) :
    Sym.notMarked (cfg₂.tape z) := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  rw [hs_cfg]
  by_cases hp : z = cfg₁.headPos
  · rw [hp, symStepConfig_tape_headPos]
    refine notMarked_write_of_notMarked_read (by rw [hs_from]; exact hleg)
      (by rw [hs_from, hs_read]; exact hs_mem) hno101 ?_
    rw [hp, ← hs_read] at hz
    exact hz
  · rw [symStepConfig_tape_of_ne _ _ hp]
    exact hz

/-- 已清扫区无标记：区间 [α₀, α) 全为非标记（清格写 d0、标记不可再生）。 -/
def SymClearedNotMarked (cfg : SymConfig) (α₀ α : ℤ) : Prop :=
  ∀ z : ℤ, α₀ ≤ z → z < α → ¬ SymMarked cfg z

/-- 已清扫区无标记的维持（清扫清格步：旧区逐格不写 + 新区格写 d0 后非标记）。 -/
lemma SymClearedNotMarked.step_21_clear {cfg₁ cfg₂ : SymConfig} {st : SymStep} {α₀ α p : ℤ}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (_hno101 : st.result.nextState ≠ 101)
    (hfrom : st.fromState = 21)
    (hread : st.readSym.1 = SymKind.consumed)
    (hC1 : SymBlk cfg₁ α p)
    (hG : ∀ i : ℤ, (cfg₁.tape i).1 = SymKind.consumed → cfg₁.headPos ≤ i)
    (hCNM : SymClearedNotMarked cfg₁ α₀ α) :
    SymClearedNotMarked cfg₂ α₀ (α + 1) := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  have hd0 : st.result.writeSym.1 = SymKind.data0 :=
    state21_read_consumed_write_d0 st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
      (by simpa using hfrom) hread
  have hkind : (cfg₁.tape cfg₁.headPos).1 = SymKind.consumed := by
    rw [← hs_read]; exact hread
  have hcons : α ≤ cfg₁.headPos ∧ cfg₁.headPos ≤ p := (hC1 cfg₁.headPos).mp hkind
  have hGα : cfg₁.headPos ≤ α := hG α ((hC1 α).mpr ⟨le_refl α, le_trans hcons.1 hcons.2⟩)
  have hheq : cfg₁.headPos = α := by omega
  intro z h1 h2
  by_cases hz : z = cfg₁.headPos
  · subst hz
    intro hM
    rw [SymMarked] at hM
    rw [hs_cfg, symStepConfig_tape_headPos, hd0] at hM
    rcases hM with h | h <;> exact absurd h (by decide)
  · rw [hs_cfg]
    rw [SymMarked]
    rw [symStepConfig_tape_of_ne _ _ hz]
    exact hCNM z h1 (by omega)

/-- 停格越块 v2：21 停格（读标记）⇒ 停格 > 块右端。
    不需局部内容件——Case A 用块区间 + 读非 consumed；Case B 用已清扫区无标记（z 必落在清扫过的区间）。 -/
lemma SymBlk.stop_gt_p_v2 {inst : SubsetSumInstance} {cfg₁ cfg₂ : SymConfig}
    {st : SymStep} {q₄ α₀ α p : ℤ}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (_hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (_hfrom : st.fromState = 21)
    (hread : st.readSym.1 = SymKind.sel ∨ st.readSym.1 = SymKind.nosel)
    (hC1 : SymBlk cfg₁ α p) (hC4 : SymLedger inst cfg₁ q₄)
    (hα₀ : α₀ ≤ q₄ + 1)
    (hCNM : SymClearedNotMarked cfg₁ α₀ α) :
    p < cfg₁.headPos := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  by_contra hcon
  have hkind : (cfg₁.tape cfg₁.headPos).1 = SymKind.sel ∨
      (cfg₁.tape cfg₁.headPos).1 = SymKind.nosel := by
    rw [← hs_read]; exact hread
  have hM : SymMarked cfg₁ cfg₁.headPos := hkind
  have hq : q₄ < cfg₁.headPos := ((hC4 cfg₁.headPos).mp hM).2
  by_cases hge : α ≤ cfg₁.headPos
  · have hcons : (cfg₁.tape cfg₁.headPos).1 = SymKind.consumed :=
      (hC1 cfg₁.headPos).mpr ⟨hge, by omega⟩
    rw [← hs_read] at hcons
    rcases hread with h | h <;> rw [h] at hcons <;> exact absurd hcons (by decide)
  · have hlt : cfg₁.headPos < α := by omega
    exact (hCNM cfg₁.headPos (by omega) hlt) hM

-- ============================================================
-- 主归纳工具层（片 9）：2-段标记扫描覆盖（C4 基座——marked ⟺ α-位置）
-- ============================================================

/-- 表级：2 段续行（仍为 2）⇒ 右移；读 ∈ {α, d0, d1}；α-读写标记、d-读恒等。 -/
theorem state2_cont (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 2 → r.nextState = 2 →
      r.moveDir = Dir.R ∧
      (k = SymKind.alpha ∨ k = SymKind.data0 ∨ k = SymKind.data1) ∧
      (k = SymKind.alpha → (r.writeSym.1 = SymKind.sel ∨ r.writeSym.1 = SymKind.nosel)) ∧
      (k ≠ SymKind.alpha → r.writeSym = (k, m)) := by
  cases m <;> cases k <;> decide

/-- 扫描新鲜性：head 及其右方未被动过（= 扫描起始配置的内容）。 -/
def SymScanFresh (cfg cfg₀ : SymConfig) : Prop :=
  ∀ z : ℤ, cfg.headPos ≤ z → cfg.tape z = cfg₀.tape z

/-- 扫描新鲜性的自反形态（起点件）。 -/
lemma SymScanFresh.refl (cfg : SymConfig) : SymScanFresh cfg cfg :=
  fun _ _ => rfl

/-- 扫描覆盖：扫描起始 s 到 head 之间 marked ⟺ α-位置（q₄=0 版账本）。 -/
def SymScanMarked (inst : SubsetSumInstance) (cfg : SymConfig) (s : ℤ) : Prop :=
  ∀ z : ℤ, s ≤ z → z < cfg.headPos → (SymMarked cfg z ↔ SymAlphaPos inst z)

/-- 扫描续行步保持覆盖（α-读 ⇒ 新格 α 位置且打标记；d-读 ⇒ 新格非 α 非标记）。 -/
lemma SymScanMarked.step_2_cont {inst : SubsetSumInstance} {cfg₀ cfg₁ cfg₂ : SymConfig}
    {st : SymStep} {s : ℤ}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (_hno101 : st.result.nextState ≠ 101)
    (hfrom : st.fromState = 2)
    (hcont : st.result.nextState = 2)
    (hSM : SymScanMarked inst cfg₁ s)
    (hfresh : SymScanFresh cfg₁ cfg₀)
    (hkind₀ : ∀ z : ℤ, s ≤ z → ((cfg₀.tape z).1 = SymKind.alpha ↔ SymAlphaPos inst z)) :
    SymScanMarked inst cfg₂ s := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  have hc := state2_cont st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
    (by simpa using hfrom) hcont
  have hhead : cfg₂.headPos = cfg₁.headPos + 1 := by
    rw [hs_cfg, symStepConfig_headPos, hc.1]; rfl
  have hc₀ : cfg₁.tape cfg₁.headPos = cfg₀.tape cfg₁.headPos :=
    hfresh _ (le_refl _)
  intro z h1 h2
  rw [hhead] at h2
  by_cases hz : z = cfg₁.headPos
  · subst hz
    rw [hs_cfg, SymMarked, symStepConfig_tape_headPos]
    by_cases hk : st.readSym.1 = SymKind.alpha
    · constructor
      · intro hw
        have hkv : (cfg₀.tape cfg₁.headPos).1 = SymKind.alpha := by
          rw [← hc₀, ← hs_read]
          exact hk
        exact (hkind₀ cfg₁.headPos h1).mp hkv
      · intro hαp
        have hkv := (hkind₀ cfg₁.headPos h1).mpr hαp
        have hks : st.readSym.1 = SymKind.alpha := by
          rw [hs_read, hc₀]
          exact hkv
        exact hc.2.2.1 hks
    · have hk' : st.readSym.1 = SymKind.data0 ∨ st.readSym.1 = SymKind.data1 := by
        rcases hc.2.1 with h | h | h
        · exact absurd h hk
        · exact Or.inl h
        · exact Or.inr h
      constructor
      · intro hw
        have hpair := hc.2.2.2 hk
        rw [hpair] at hw
        rcases hk' with h | h <;> rw [h] at hw <;> exact absurd hw (by decide)
      · intro hαp
        have hkv := (hkind₀ cfg₁.headPos h1).mpr hαp
        have hkd : (st.readSym.1) = SymKind.alpha := by
          rw [hs_read, hc₀]
          exact hkv
        exfalso
        exact hk hkd
  · rw [hs_cfg, SymMarked, symStepConfig_tape_of_ne _ _ hz]
    exact hSM z h1 (by omega)

/-- 扫描续行步保持新鲜性（写只在旧 head；新区间从新 head 起未动）。 -/
lemma SymScanFresh.step_2_cont {cfg₀ cfg₁ cfg₂ : SymConfig} {st : SymStep}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (hfrom : st.fromState = 2)
    (hcont : st.result.nextState = 2)
    (hfresh : SymScanFresh cfg₁ cfg₀) :
    SymScanFresh cfg₂ cfg₀ := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  have hc := state2_cont st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
    (by simpa using hfrom) hcont
  have hhead : cfg₂.headPos = cfg₁.headPos + 1 := by
    rw [hs_cfg, symStepConfig_headPos, hc.1]; rfl
  intro z hz
  rw [hhead] at hz
  have hz' : cfg₁.headPos ≤ z := by omega
  have hne : z ≠ cfg₁.headPos := by omega
  rw [hs_cfg, symStepConfig_tape_of_ne _ _ hne]
  exact hfresh z hz'

-- ============================================================
-- 主归纳工具层（片 10）：C4 基座收官——hkind₀ 供给 + 边界件 + 相位出入表件
-- ============================================================

/-- 初始带 = getD 桥（z ≥ 0 时 tape z = input.getD z.toNat）。 -/
lemma symInitialConfig_tape_getD {input : List Sym} {z : ℤ} (hz0 : 0 ≤ z) :
    (symInitialConfig input).tape z = input.getD z.toNat Sym.blank := by
  show (if h : 0 ≤ z ∧ z.toNat < input.length then
      input.get ⟨z.toNat, h.2⟩ else Sym.blank) = input.getD z.toNat Sym.blank
  by_cases hin : z.toNat < input.length
  · rw [dif_pos ⟨hz0, hin⟩]
    exact (List.getD_eq_getElem input Sym.blank hin).symm
  · rw [dif_neg (by intro h; exact hin h.2)]
    exact (getD_eq_default_of_length_le input (by omega)).symm

/-- hkind₀ 供给（⟸ 向）：α-位置格在初始带上的 kind 为 α。 -/
lemma alpha_pos_init_kind (inst : SubsetSumInstance) {z : ℤ} (hαp : SymAlphaPos inst z) :
    ((symInitialConfig (encodeInstanceSym inst)).tape z).1 = SymKind.alpha := by
  rcases hαp with ⟨o, ho, rfl⟩
  have hj : o < (encodeElementsSym inst.elements).length :=
    alphaOffsets_lt_length inst.elements ho
  have hz0 : (0 : ℤ) ≤ ((encPrefixLen inst + o : ℕ) : ℤ) := by positivity
  rw [symInitialConfig_tape_getD hz0]
  have htoNat : (((encPrefixLen inst + o : ℕ) : ℤ)).toNat = encPrefixLen inst + o :=
    Int.toNat_natCast _
  rw [htoNat]
  rw [show (encPrefixLen inst + o : ℕ) =
      (encodeBitsSym inst.target).length + 2 + o from by rw [encPrefixLen]]
  rw [a2p_enc_elems_getD inst hj]
  exact (alpha_iff_mem_offsets inst.elements hj).mpr ho

/-- 边界件 A：α-位置 ≥ 元素区起点。 -/
lemma alpha_pos_ge_prefixLen {inst : SubsetSumInstance} {z : ℤ} (hαp : SymAlphaPos inst z) :
    ((encPrefixLen inst : ℕ) : ℤ) ≤ z := by
  rcases hαp with ⟨o, _, rfl⟩
  push_cast
  omega

/-- 边界件 B：α-位置 < 元素区终点（= 末 #₁ 位置 = prefixLen + |elements|）。 -/
lemma alpha_pos_lt_region_end {inst : SubsetSumInstance} {z : ℤ} (hαp : SymAlphaPos inst z) :
    z < (((encPrefixLen inst + (encodeElementsSym inst.elements).length : ℕ)) : ℤ) := by
  rcases hαp with ⟨o, ho, rfl⟩
  have := alphaOffsets_lt_length inst.elements ho
  push_cast
  omega

/-- 表级：1 段出口（读 #-）⇒ 2、写 #-、右移（2 段起点 = #₀+1）。 -/
theorem state1_exit (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 1 → k = SymKind.boundary →
      r.nextState = 2 ∧ r.writeSym.1 = SymKind.boundary ∧ r.moveDir = Dir.R := by
  cases m <;> cases k <;> decide

/-- 表级：2 段出口（读 #-）⇒ 3、写 #-、停顿（2 段终点 = #₁）。 -/
theorem state2_exit (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 2 → k = SymKind.boundary →
      r.nextState = 3 ∧ r.writeSym.1 = SymKind.boundary ∧ r.moveDir = Dir.S := by
  cases m <;> cases k <;> decide

-- ============================================================
-- 主归纳工具层（片 11）：读标记步 ⇒ head > p（v2 推广） + sel-4 悬挂包
-- ============================================================

/-- 读标记步（任意状态）⇒ 带头 > 块右端（v2 去掉 fromState 约束的推广；
    Case A：块区间 + 读非 consumed；Case B：已清扫区无标记）。 -/
lemma SymBlk.head_gt_p_of_readMarked {inst : SubsetSumInstance} {cfg₁ cfg₂ : SymConfig}
    {st : SymStep} {q₄ α₀ α p : ℤ}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (_hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (hread : st.readSym.1 = SymKind.sel ∨ st.readSym.1 = SymKind.nosel)
    (hC1 : SymBlk cfg₁ α p) (hC4 : SymLedger inst cfg₁ q₄)
    (hα₀ : α₀ ≤ q₄ + 1)
    (hCNM : SymClearedNotMarked cfg₁ α₀ α) :
    p < cfg₁.headPos := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  by_contra hcon
  have hkind : (cfg₁.tape cfg₁.headPos).1 = SymKind.sel ∨
      (cfg₁.tape cfg₁.headPos).1 = SymKind.nosel := by
    rw [← hs_read]; exact hread
  have hM : SymMarked cfg₁ cfg₁.headPos := hkind
  have hq : q₄ < cfg₁.headPos := ((hC4 cfg₁.headPos).mp hM).2
  by_cases hge : α ≤ cfg₁.headPos
  · have hcons : (cfg₁.tape cfg₁.headPos).1 = SymKind.consumed :=
      (hC1 cfg₁.headPos).mpr ⟨hge, by omega⟩
    rw [← hs_read] at hcons
    rcases hread with h | h <;> rw [h] at hcons <;> exact absurd hcons (by decide)
  · have hlt : cfg₁.headPos < α := by omega
    exact (hCNM cfg₁.headPos (by omega) hlt) hM

/-- 表级：4 段 sel 行（⇒ 5）右移。 -/
theorem state4_sel_move (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 4 → r.nextState = 5 → r.moveDir = Dir.R := by
  cases m <;> cases k <;> decide

/-- sel-4 悬挂包：sel-4 步后（进入 5）⇒ (a) 新头 = 旧头+1；(b) p < 旧头+1（= 首火位之上）；
    (c) 块保持（p 不变）。三者即"首火 q = 旧头+1 > p"的全部前提。 -/
lemma SymBlk.selFour_pend {inst : SubsetSumInstance} {cfg₁ cfg₂ : SymConfig}
    {st : SymStep} {q₄ α₀ α p : ℤ}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (hno101 : st.result.nextState ≠ 101)
    (hfrom : st.fromState = 4)
    (hnext5 : st.result.nextState = 5)
    (hC1 : SymBlk cfg₁ α p) (hC4 : SymLedger inst cfg₁ q₄)
    (hα₀ : α₀ ≤ q₄ + 1)
    (hCNM : SymClearedNotMarked cfg₁ α₀ α) :
    cfg₂.headPos = cfg₁.headPos + 1 ∧ p < cfg₁.headPos + 1 ∧ SymBlk cfg₂ α p := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  have hmd := state4_readMark_write_d0 st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
    (by simpa using hfrom) hno101
  have hread : st.readSym.1 = SymKind.sel ∨ st.readSym.1 = SymKind.nosel := hmd.1
  have hgt : p < cfg₁.headPos :=
    SymBlk.head_gt_p_of_readMarked hst hleg hread hC1 hC4 hα₀ hCNM
  have hmove := state4_sel_move st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
    (by simpa using hfrom) hnext5
  have hhead : cfg₂.headPos = cfg₁.headPos + 1 := by
    rw [hs_cfg, symStepConfig_headPos, hmove]; rfl
  have hblk : SymBlk cfg₂ α p :=
    SymBlk.step_of_notFive21 hst hleg hno101 (by omega) (by omega) hC1
  exact ⟨hhead, by omega, hblk⟩

-- ============================================================
-- 主归纳工具层（片 12）：通用维持件——13-数据步 / gap 通用步 / 已清扫区强化版
-- ============================================================

/-- 表级：13 数据行（⇒ 5）停顿。 -/
theorem state13_data_move (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 13 → (k = SymKind.data0 ∨ k = SymKind.data1) → r.moveDir = Dir.S := by
  cases m <;> cases k <;> decide

/-- 走廊数据步保持（13→5 停顿：区间不变 = 走廊保持 + 伴条件 s+1 ≤ head 保持）。 -/
lemma SymWalkConsumed.step_13_data {cfg₁ cfg₂ : SymConfig} {st : SymStep} {s : ℤ}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (hfrom : st.fromState = 13)
    (hread : st.readSym.1 = SymKind.data0 ∨ st.readSym.1 = SymKind.data1)
    (hW : SymWalkConsumed cfg₁ s) :
    SymWalkConsumed cfg₂ s := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  have hmv := state13_data_move st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
    (by simpa using hfrom) hread
  have hS : Dir.S.toInt = (0 : ℤ) := rfl
  have hhead : cfg₂.headPos = cfg₁.headPos := by
    rw [hs_cfg, symStepConfig_headPos, hmv, hS]
    omega
  intro z h1 h2
  rw [hhead] at h2
  rw [hs_cfg, symStepConfig_tape_of_ne _ _ (by omega : z ≠ cfg₁.headPos)]
  exact hW z h1 h2

/-- gap 收缩件：新头 ≤ 旧头 ⇒ gap 保持（任意步——范围收缩）。 -/
lemma SymGapNoAlpha.step_shrink {inst : SubsetSumInstance} {cfg₁ cfg₂ : SymConfig}
    {st : SymStep} {q₄ : ℤ}
    (_hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hhead : cfg₂.headPos ≤ cfg₁.headPos)
    (hGap : SymGapNoAlpha inst q₄ cfg₁) :
    SymGapNoAlpha inst q₄ cfg₂ := by
  intro z h1 h2
  exact hGap z h1 (by omega)

/-- gap 右进件：非标记读 + 右移 ⇒ gap 保持（新格经账本取否 ⇒ 无 α）。 -/
lemma SymGapNoAlpha.step_of_notMarked_read_R {inst : SubsetSumInstance}
    {cfg₁ cfg₂ : SymConfig} {st : SymStep} {q₄ : ℤ}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (_hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (hread : ¬(st.readSym.1 = SymKind.sel ∨ st.readSym.1 = SymKind.nosel))
    (hmove : st.result.moveDir = Dir.R)
    (hGap : SymGapNoAlpha inst q₄ cfg₁)
    (hC4 : SymLedger inst cfg₁ q₄) :
    SymGapNoAlpha inst q₄ cfg₂ := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hhead : cfg₂.headPos = cfg₁.headPos + 1 := by
    rw [hs_cfg, symStepConfig_headPos, hmove]; rfl
  intro z h1 h2
  rw [hhead] at h2
  by_cases hz : z = cfg₁.headPos
  · subst hz
    -- 新格：读非标记 ⇒ 账本否定 ⇒ ¬(α-pos ∧ q₄ < head)；h1: q₄ < head ⇒ ¬α-pos
    have hnm : ¬ SymMarked cfg₁ cfg₁.headPos := by
      intro hM
      rw [SymMarked] at hM
      rcases hM with h | h
      · rw [← hs_read] at h; exact hread (Or.inl h)
      · rw [← hs_read] at h; exact hread (Or.inr h)
    intro hα
    exact hnm ((hC4 cfg₁.headPos).mpr ⟨hα, h1⟩)
  · exact hGap z h1 (by omega)

/-- gap 重置件：q₄ := 当前头（空区间）。 -/
lemma SymGapNoAlpha.rebase (inst : SubsetSumInstance) (cfg : SymConfig) :
    SymGapNoAlpha inst cfg.headPos cfg := by
  intro z h1 h2
  exact absurd h1 (by omega)

/-- 已清扫区（强化版）：区间内**非 {α,s/n}-类**（经 notMarked——对任意步可保）。 -/
def SymClearedGone (cfg : SymConfig) (α₀ α : ℤ) : Prop :=
  ∀ z : ℤ, α₀ ≤ z → z < α → Sym.notMarked (cfg.tape z)

/-- 强化区任意步保持（区间不动时——逐格 notMarked_step）。 -/
lemma SymClearedGone.step_any {cfg₁ cfg₂ : SymConfig} {st : SymStep} {α₀ α : ℤ}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (hno101 : st.result.nextState ≠ 101)
    (hG : SymClearedGone cfg₁ α₀ α) :
    SymClearedGone cfg₂ α₀ α := by
  intro z h1 h2
  exact notMarked_step hst hleg hno101 (hG z h1 h2)

/-- 强化区经清扫清格步扩展（[α₀, α) → [α₀, α+1)：新格写 d0- ⇒ notMarked）。 -/
lemma SymClearedGone.step_21_clear_ext {cfg₁ cfg₂ : SymConfig} {st : SymStep} {α₀ α p : ℤ}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (hno101 : st.result.nextState ≠ 101)
    (hfrom : st.fromState = 21)
    (hread : st.readSym.1 = SymKind.consumed)
    (hC1 : SymBlk cfg₁ α p)
    (hG : ∀ i : ℤ, (cfg₁.tape i).1 = SymKind.consumed → cfg₁.headPos ≤ i)
    (hCG : SymClearedGone cfg₁ α₀ α) :
    SymClearedGone cfg₂ α₀ (α + 1) := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  have hd0 : st.result.writeSym.1 = SymKind.data0 :=
    state21_read_consumed_write_d0 st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
      (by simpa using hfrom) hread
  have hkind : (cfg₁.tape cfg₁.headPos).1 = SymKind.consumed := by
    rw [← hs_read]; exact hread
  have hcons : α ≤ cfg₁.headPos ∧ cfg₁.headPos ≤ p := (hC1 cfg₁.headPos).mp hkind
  have hGα : cfg₁.headPos ≤ α := hG α ((hC1 α).mpr ⟨le_refl α, le_trans hcons.1 hcons.2⟩)
  have hheq : cfg₁.headPos = α := by omega
  intro z h1 h2
  by_cases hz : z = cfg₁.headPos
  · subst hz
    rw [Sym.notMarked, hs_cfg, symStepConfig_tape_headPos, hd0]
    exact ⟨by decide, by decide, by decide⟩
  · exact notMarked_step hst hleg hno101 (hCG z h1 (by omega))

-- ============================================================
-- 主归纳工具层（片 13a）：不变式包结构 + 火点 A 事实（双来源）+ nodup 装配组合件
-- ============================================================

/-- 五元幽灵状态：块左右、最近 4 位、走廊起点、已清扫区下界。 -/
structure SymFiveSt where
  α : ℤ
  p : ℤ
  q₄ : ℤ
  s : ℤ
  α₀ : ℤ

/-- 轮中态集合（rebase 后、首清前的全相位）。 -/
def symMainSet : Finset ℕ := {5, 8, 76, 9, 10, 11, 12, 13, 14, 81, 84, 85, 86, 87, 20}

/-- 作业态集合（hpc 的守卫：不含 5——首火前块可空、p 格非 c；不含 20——[4]-nosel 后全带无 c 格）。 -/
def symWorkSet : Finset ℕ := {8, 76, 9, 10, 11, 12, 13, 14, 81, 84, 85, 86, 87}

/-- 编码末格位置（#₁ 所在格；纯 inst 项——# 账目末臂）。 -/
def symEndPos (inst : SubsetSumInstance) : ℤ :=
  (encPrefixLen inst : ℤ) + (encodeElementsSym inst.elements).length

/-- α-位置恒在编码末格之西（α 偏移 < 元素区长度）。 -/
lemma symAlphaPos_lt_end {inst : SubsetSumInstance} {z : ℤ} (h : SymAlphaPos inst z) :
    z < symEndPos inst := by
  rcases h with ⟨o, ho, rfl⟩
  have ho' : o < (encodeElementsSym inst.elements).length := alphaOffsets_lt_length inst.elements ho
  have ho'' : ((o : ℕ) : ℤ) < (((encodeElementsSym inst.elements).length : ℕ) : ℤ) := by
    exact_mod_cast ho'
  unfold symEndPos
  rw [Nat.cast_add]
  omega

/-- 主不变式包（五元幽灵 + 二十七项事实；各态条件件由主归纳线程）。 -/
structure SymFiveInv (inst : SubsetSumInstance) (cfg : SymConfig) (S : SymFiveSt) : Prop where
  hblk : SymBlk cfg S.α S.p
  hC4 : SymLedger inst cfg S.q₄
  hCNM : SymClearedGone cfg S.α₀ S.α
  hα₀ : S.α₀ ≤ S.q₄ + 1
  hgap : SymGapNoAlpha inst S.q₄ cfg
  hαp : S.α ≤ S.p + 1
  /-- 4/51 态：块为空形（清扫完成的等价形态）。 -/
  hempQ : (cfg.state = 4 ∨ cfg.state = 51) → S.α = S.p + 1
  /-- 20/21 态（清扫进行中）：头下方无 consumed。 -/
  hB4 : (cfg.state = 20 ∨ cfg.state = 21) →
    ∀ z : ℤ, z < cfg.headPos → (cfg.tape z).1 = SymKind.consumed → False
  /-- 5 态（非空形）：头 = p+1（火位即格点）。 -/
  h5pos : cfg.state = 5 → S.α ≠ S.p + 1 → cfg.headPos = S.p + 1
  /-- 5 态：火位 > p（A 事实——跨轮不等式）。 -/
  hA5 : cfg.state = 5 → S.p < cfg.headPos
  /-- 13 态（走廊）：走廊三件套。 -/
  hwalk13 : cfg.state = 13 →
    SymWalkConsumed cfg S.s ∧ S.s < cfg.headPos ∧ S.α ≤ S.s
  /-- 轮中态：q₄−1 格为 #₀（边界锚——86/87 头受控 + 回卷语义）。 -/
  hSharp : cfg.state ∈ symMainSet → (cfg.tape (S.q₄ - 1)).1 = SymKind.boundary
  /-- 86/87 态：头 ≤ q₄−1（R 扫不越 #₀）。 -/
  h86le : (cfg.state = 86 ∨ cfg.state = 87) → cfg.headPos ≤ S.q₄ - 1
  /-- 轮中态：α = q₄+1（块左 = 本轮领头+1）。 -/
  hαqU : cfg.state ∈ symMainSet → S.α = S.q₄ + 1
  /-- 5 态空形支（rebase 后）：头 = q₄+1（本轮首火位）。 -/
  hnext1 : cfg.state = 5 → S.α = S.p + 1 → cfg.headPos = S.q₄ + 1
  /-- q₄ 下界（首轮之后；4 态豁免——含初始 0）。 -/
  hq4ge : 2 ≤ S.q₄ ∨ cfg.state = 4
  /-- # 账目（三臂+条件戳臂）：0=#ₗ；q₄−1=轮中锚（旧 #₀）；symEndPos=#₁（编码末格）；
      4 态头−1=51 新戳位（仅 4 态存活——其余态无孤儿）。 -/
  hbnd : ∀ z : ℤ, (cfg.tape z).1 = SymKind.boundary →
    z = 0 ∨ z = S.q₄ - 1 ∨ z = symEndPos inst ∨ (cfg.state = 4 ∧ z = cfg.headPos - 1)
  /-- 作业态：p 格内容恒为 c（火后未触；84 首撞链的砖）。 -/
  hpc : cfg.state ∈ symWorkSet → (cfg.tape S.p).1 = SymKind.consumed
  /-- 84 态：q₄−1 ≤ 头（L 下行 + 读≠# 维持）。 -/
  h84le : cfg.state = 84 → S.q₄ - 1 ≤ cfg.headPos
  /-- 84 态：头 ≤ p（下行自 z−1）。 -/
  h84le2 : cfg.state = 84 → cfg.headPos ≤ S.p
  /-- 85 态：头 ≤ q₄−2（84 首撞后继续下行）。 -/
  h85le : cfg.state = 85 → cfg.headPos ≤ S.q₄ - 2
  /-- 51 态：头 ≥ p（21 停格读标记 ⇒ 头 > p；51 步新 #₀ 落在 ≥p 区）。 -/
  h51p : cfg.state = 51 → S.p ≤ cfg.headPos
  /-- 4/21/51 态：旧 #₀（= q₄−1 格）已被 20 步销毁（= d0）。 -/
  h20d : (cfg.state = 4 ∨ cfg.state = 21 ∨ cfg.state = 51) → (cfg.tape (S.q₄ - 1)).1 = SymKind.data0
  /-- 4 态：head−1 格为新 #₀（51 盖章写入位 = 旧头）。 -/
  h4head : cfg.state = 4 → (cfg.tape (cfg.headPos - 1)).1 = SymKind.boundary
  /-- 51 态：q₄ ≤ 头（21 停格读标记 ⇒ 停格 > q₄；51 头 = 停格−1）。 -/
  h51q4 : cfg.state = 51 → S.q₄ ≤ cfg.headPos
  /-- 86/87 态：1 ≤ 头（85→86 落 1 起、R 步递增、S 步保持）。 -/
  h86ge : (cfg.state = 86 ∨ cfg.state = 87) → 1 ≤ cfg.headPos
  /-- 20 态：头 = q₄−1（87 穿 #₀ 的 S 保持；4-nosel 的 L 落于 (q₄+1)−1）。 -/
  h20h : cfg.state = 20 → cfg.headPos = S.q₄ - 1
  /-- 5 态：p 格非 #（p = 头−1 格 = 火前格/rebased 格——d0 或 c）。 -/
  h5pc : cfg.state = 5 → (cfg.tape S.p).1 ≠ SymKind.boundary
  /-- 锚内界：q₄ < 编码末格（锚位置在带内；[4] rebase 由"标记⟹α 位置⟹末界"供）。 -/
  hq4e : S.q₄ < symEndPos inst

/-- 强化区 ⇒ v2 所需否定形（适配件）。 -/
lemma SymClearedGone.to_notMarked {cfg : SymConfig} {α₀ α : ℤ}
    (h : SymClearedGone cfg α₀ α) :
    ∀ z : ℤ, α₀ ≤ z → z < α → ¬ SymMarked cfg z := by
  intro z h1 h2 hM
  have hnm := h z h1 h2
  rw [SymMarked] at hM
  rcases hM with hM | hM
  · exact hnm.2.1 hM
  · exact hnm.2.2 hM

/-- 火点 A 事实（走廊来源）：5 步读 data + 走廊伴条件 ⇒ 火位 > p。 -/
lemma fireA_of_walk {cfg₁ cfg₂ : SymConfig} {st : SymStep} {α p s : ℤ}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (hno101 : st.result.nextState ≠ 101)
    (hfrom : st.fromState = 5)
    (hC1 : SymBlk cfg₁ α p)
    (_hW : SymWalkConsumed cfg₁ s) (hslt : s < cfg₁.headPos) (hαs : α ≤ s) :
    p < cfg₁.headPos := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  have h5f := state5_readData_writeConsumed st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
    (by simpa using hfrom) hno101
  have hread : (cfg₁.tape cfg₁.headPos).1 = SymKind.data0 ∨
      (cfg₁.tape cfg₁.headPos).1 = SymKind.data1 := by
    rw [← hs_read]; exact h5f.1
  have hnc : (cfg₁.tape cfg₁.headPos).1 ≠ SymKind.consumed := by
    rcases hread with h | h <;> rw [h] <;> decide
  have hnot : ¬(α ≤ cfg₁.headPos ∧ cfg₁.headPos ≤ p) := fun hc => hnc ((hC1 _).mpr hc)
  have hnp : ¬(cfg₁.headPos ≤ p) := fun hle => hnot ⟨by omega, hle⟩
  omega

/-- nodup 装配组合件：尾部 nodup + 跨段严格下界 ⇒ 全表 nodup。 -/
lemma fivePositions_nodup_cons {h₀ : ℤ} {x : SymStep} {rest : List SymStep}
    (ih : (fivePositions (h₀ + x.result.moveDir.toInt) rest).Nodup)
    (cross : ∀ b ∈ fivePositions (h₀ + x.result.moveDir.toInt) rest, h₀ < b) :
    (fivePositions h₀ (x :: rest)).Nodup := by
  rw [fivePositions_cons]
  refine List.nodup_append.mpr ⟨?_, ?_, ?_⟩
  · by_cases hx : symFive x = true <;> simp [hx]
  · exact ih
  · intro a ha b hb hab
    by_cases hx : symFive x = true
    · rw [if_pos hx] at ha
      simp only [List.mem_singleton] at ha
      have hb' := cross b hb
      rw [ha] at hab
      omega
    · rw [if_neg hx] at ha
      exact absurd ha List.not_mem_nil

-- ============================================================
-- 主归纳工具层（片 14a）：分派表级决定件
-- ============================================================

/-- 4 段：sel 行 ⇒ next = 5。 -/
theorem state4_sel_next (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 4 → k = SymKind.sel → r.nextState = 5 := by
  cases m <;> cases k <;> decide

/-- 4 段：nosel 行 ⇒ next = 20。 -/
theorem state4_nosel_next (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 4 → k = SymKind.nosel → r.nextState = 20 := by
  cases m <;> cases k <;> decide

/-- 4 段：非标记读 ⇒ next = 101。 -/
theorem state4_other_101 (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 4 → k ≠ SymKind.sel → k ≠ SymKind.nosel → r.nextState = 101 := by
  cases m <;> cases k <;> decide

/-- 4 段：nosel 行 ⇒ move = L。 -/
theorem state4_nosel_move (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 4 → k = SymKind.nosel → r.moveDir = Dir.L := by
  cases m <;> cases k <;> decide

/-- 5 段：非陷阱 ⇒ move = L。 -/
theorem state5_move_L (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 5 → r.nextState ≠ 101 → r.moveDir = Dir.L := by
  cases m <;> cases k <;> decide

/-- 13 段：数据行 ⇒ next = 5。 -/
theorem state13_data_next5 (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 13 → (k = SymKind.data0 ∨ k = SymKind.data1) → r.nextState = 5 := by
  cases m <;> cases k <;> decide

/-- 13 段：非数据、非陷阱 ⇒ next = 84 或 13。 -/
theorem state13_notData (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 13 → k ≠ SymKind.data0 → k ≠ SymKind.data1 → r.nextState ≠ 101 →
      r.nextState = 84 ∨ r.nextState = 13 := by
  cases m <;> cases k <;> decide

/-- 13 段：c 续行 ⇒ move = R（且 next = 13）。 -/
theorem state13_cont_R (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 13 → k = SymKind.consumed → r.moveDir = Dir.R := by
  cases m <;> cases k <;> decide

/-- 13 段：出口（next = 84）⇒ move = L。 -/
theorem state13_exit_move (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 13 → r.nextState = 84 → r.moveDir = Dir.L := by
  cases m <;> cases k <;> decide

/-- 81 段：c 出口行 ⇒ next = 13 且 move = R。 -/
theorem state81_c_exit (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 81 → k = SymKind.consumed → r.nextState = 13 ∧ r.moveDir = Dir.R := by
  cases m <;> cases k <;> decide

/-- 81 段：非 c、非陷阱 ⇒ move = R。 -/
theorem state81_move_R (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 81 → r.nextState ≠ 101 → r.moveDir = Dir.R := by
  cases m <;> cases k <;> decide

/-- 81 段：非 c、非陷阱 ⇒ next = 81。 -/
theorem state81_notc_cont (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 81 → k ≠ SymKind.consumed → r.nextState ≠ 101 → r.nextState = 81 := by
  cases m <;> cases k <;> decide

/-- 20 段：非陷阱 ⇒ 读 #、next = 21、写 d0、move = R。 -/
theorem state20_facts (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 20 → r.nextState ≠ 101 →
      k = SymKind.boundary ∧ r.nextState = 21 ∧ r.writeSym.1 = SymKind.data0 ∧
        r.moveDir = Dir.R := by
  cases m <;> cases k <;> decide

/-- 21 段：c 读 ⇒ 清格行（next = 21、写 d0、move = R）。 -/
theorem state21_c_clear (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 21 → k = SymKind.consumed →
      r.nextState = 21 ∧ r.writeSym.1 = SymKind.data0 ∧ r.moveDir = Dir.R := by
  cases m <;> cases k <;> decide

/-- 21 段：标记读 ⇒ 停格行（next = 51、move = L）。 -/
theorem state21_mark_stop (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 21 → (k = SymKind.sel ∨ k = SymKind.nosel) →
      r.nextState = 51 ∧ r.moveDir = Dir.L := by
  cases m <;> cases k <;> decide

/-- 21 段：非 c、非标记、非 #、非陷阱 ⇒ next = 21（恒等/去 m 续行）。 -/
theorem state21_d_cont (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 21 → k ≠ SymKind.consumed → k ≠ SymKind.sel → k ≠ SymKind.nosel →
      k ≠ SymKind.boundary → r.nextState ≠ 101 → r.nextState = 21 := by
  cases m <;> cases k <;> decide

/-- 21 段：# 读 ⇒ 段末行（next = 22、move = S）。 -/
theorem state21_hash_end (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 21 → k = SymKind.boundary → r.nextState = 22 ∧ r.moveDir = Dir.S := by
  cases m <;> cases k <;> decide

/-- 51 段：非陷阱 ⇒ next = 4、move = R。 -/
theorem state51_go (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 51 → r.nextState ≠ 101 → r.nextState = 4 ∧ r.moveDir = Dir.R := by
  cases m <;> cases k <;> decide

/-- 29 段：非陷阱 ⇒ move = L（相位尾）。 -/
theorem state29_move_L (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 29 → r.nextState ≠ 101 → r.moveDir = Dir.L := by
  cases m <;> cases k <;> decide

/-- 标记读（s/n）且非陷阱 ⇒ 状态 ∈ {4,13,21,29,100}。 -/
theorem markRead_states (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (k = SymKind.sel ∨ k = SymKind.nosel) → r.nextState ≠ 101 →
      (q : ℕ) = 4 ∨ (q : ℕ) = 13 ∨ (q : ℕ) = 21 ∨ (q : ℕ) = 29 ∨ (q : ℕ) = 100 := by
  cases m <;> cases k <;> decide

/-- 100 段（吸收自环）：全行 move = S。 -/
theorem state100_move_S (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 100 → r.moveDir = Dir.S := by
  cases m <;> cases k <;> decide

/-- 前缀走廊态在 #-格上的写 = 恒等（86/87 头部受控的砖）。 -/
theorem sharpId_writes (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      ((q : ℕ) = 8 ∨ (q : ℕ) = 76 ∨ (q : ℕ) = 9 ∨ (q : ℕ) = 77 ∨ (q : ℕ) = 13 ∨
        (q : ℕ) = 81 ∨ (q : ℕ) = 84 ∨ (q : ℕ) = 85 ∨ (q : ℕ) = 86 ∨ (q : ℕ) = 87) →
      k = SymKind.boundary → r.writeSym = (k, m) := by
  cases m <;> cases k <;> decide

/-- 10/11/12/14 段在 #-格上必陷。 -/
theorem state10hash_trap (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      ((q : ℕ) = 10 ∨ (q : ℕ) = 11 ∨ (q : ℕ) = 12 ∨ (q : ℕ) = 14) →
      k = SymKind.boundary → r.nextState = 101 := by
  cases m <;> cases k <;> decide

/-- 5 段在 #-格上必陷。 -/
theorem state5hash_trap (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 5 → k = SymKind.boundary → r.nextState = 101 := by
  cases m <;> cases k <;> decide

/-- 86/87 段 R 步的读必为数据类（非 # 非 c）——头受控维持砖。 -/
theorem state8687_R_read (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      ((q : ℕ) = 86 ∨ (q : ℕ) = 87) → r.nextState ≠ 101 → r.moveDir = Dir.R →
      k = SymKind.data0 ∨ k = SymKind.data1 := by
  cases m <;> cases k <;> decide

/-- 84/85 段 L 步读范围（弯道/回卷段）。 -/
theorem state8485_dict (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      ((q : ℕ) = 84 ∨ (q : ℕ) = 85) → r.nextState ≠ 101 →
      k = SymKind.data0 ∨ k = SymKind.data1 ∨ k = SymKind.consumed ∨
        k = SymKind.boundary := by
  cases m <;> cases k <;> decide

/-- #-写者分类：非 #-读步的 #-写仅限 51。 -/
theorem hashWriters (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      k ≠ SymKind.boundary → r.writeSym.1 ≠ SymKind.boundary ∨ (q : ℕ) = 51 := by
  cases m <;> cases k <;> decide

/-- 51 段：非陷阱行写 #（新 #₀）。 -/
theorem state51_write_hash (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 51 → r.nextState ≠ 101 → r.writeSym.1 = SymKind.boundary := by
  cases m <;> cases k <;> decide

/-- #-读恒等：非 {51,3,20} 态读 # ⇒ 写 = 读（恒等）。 -/
theorem hashRead_id (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) ≠ 51 → (q : ℕ) ≠ 3 → (q : ℕ) ≠ 20 → k = SymKind.boundary →
      r.writeSym = (k, m) := by
  cases m <;> cases k <;> decide

/-- #-写者（非 #-读）：非 {51,3,20} 态不写 #。 -/
theorem hashWrite_cases (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) ≠ 51 → (q : ℕ) ≠ 3 → (q : ℕ) ≠ 20 → k ≠ SymKind.boundary →
      r.writeSym.1 ≠ SymKind.boundary := by
  cases m <;> cases k <;> decide

/-- 8487 入口集：next ∈ {84..87} ⇒ from ∈ {13,84,85,86,87}。 -/
theorem no_8487_entry (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (r.nextState = 84 ∨ r.nextState = 85 ∨ r.nextState = 86 ∨ r.nextState = 87) →
      ((q : ℕ) = 13 ∨ (q : ℕ) = 84 ∨ (q : ℕ) = 85 ∨ (q : ℕ) = 86 ∨ (q : ℕ) = 87) := by
  cases m <;> cases k <;> decide

-- ============================================================
-- 主归纳工具层（片 14c）：通用维持机件（hbnd / hpnb 单步）
-- ============================================================

/-- hbnd 单步保持（from ∉ {51,3,20}；(q₄, p) 不动）。 -/
lemma hbnd_step {cfg₁ cfg₂ : SymConfig} {st : SymStep} {q₄ p : ℤ}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (_hno101 : st.result.nextState ≠ 101)
    (hne51 : st.fromState ≠ 51) (hne3 : st.fromState ≠ 3) (hne20 : st.fromState ≠ 20)
    (hbnd : ∀ z : ℤ, (cfg₁.tape z).1 = SymKind.boundary → z = 0 ∨ z = q₄ - 1 ∨ p ≤ z) :
    ∀ z : ℤ, (cfg₂.tape z).1 = SymKind.boundary → z = 0 ∨ z = q₄ - 1 ∨ p ≤ z := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  intro z hz
  by_cases hz1 : z = cfg₁.headPos
  · subst hz1
    have hwrite : st.result.writeSym.1 = SymKind.boundary := by
      rw [hs_cfg, symStepConfig_tape_headPos] at hz
      exact hz
    by_cases hread : st.readSym.1 = SymKind.boundary
    · have hid := hashRead_id st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
        hne51 hne3 hne20 hread
      have hread' : st.readSym.1 = SymKind.boundary :=
        ((congrArg Prod.fst hid).symm).trans hwrite
      exact hbnd cfg₁.headPos (by rw [← hs_read]; exact hread')
    · exact absurd hwrite (hashWrite_cases st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩
        st.result hm hne51 hne3 hne20 hread)
  · rw [hs_cfg, symStepConfig_tape_of_ne _ _ hz1] at hz
    exact hbnd z hz

/-- # 账目框架：非 51/3/20 步 #-格集合完全不变（#-读⟹写#恒等、#-写⟹读#）；
    条件戳臂仅 4 态存活——非 4 前态无孤儿、三臂直接平移。 -/
lemma hbnd_frame {inst : SubsetSumInstance} {cfg₁ cfg₂ : SymConfig} {st : SymStep} {q₄ : ℤ}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (_hno101 : st.result.nextState ≠ 101)
    (hne51 : st.fromState ≠ 51) (hne3 : st.fromState ≠ 3) (hne20 : st.fromState ≠ 20)
    (hnot4 : cfg₁.state ≠ 4)
    (hbnd : ∀ z : ℤ, (cfg₁.tape z).1 = SymKind.boundary →
      z = 0 ∨ z = q₄ - 1 ∨ z = symEndPos inst ∨ (cfg₁.state = 4 ∧ z = cfg₁.headPos - 1)) :
    ∀ z : ℤ, (cfg₂.tape z).1 = SymKind.boundary →
      z = 0 ∨ z = q₄ - 1 ∨ z = symEndPos inst ∨ (cfg₂.state = 4 ∧ z = cfg₂.headPos - 1) := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  intro z hz
  have hz1 : (cfg₁.tape z).1 = SymKind.boundary := by
    rw [hs_cfg] at hz
    by_cases hzh : z = cfg₁.headPos
    · subst hzh
      rw [symStepConfig_tape_headPos] at hz
      by_cases hread : st.readSym.1 = SymKind.boundary
      · rw [← hs_read]; exact hread
      · exact absurd hz (hashWrite_cases st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩
          st.result hm hne51 hne3 hne20 hread)
    · rw [symStepConfig_tape_of_ne _ _ hzh] at hz
      exact hz
  rcases hbnd z hz1 with h0 | hq | hE | ⟨h4, hh⟩
  · exact Or.inl h0
  · exact Or.inr (Or.inl hq)
  · exact Or.inr (Or.inr (Or.inl hE))
  · exact absurd h4 hnot4

/-- hpnb 单步保持（from ∉ {51,3,20}；p 不动）。 -/
lemma hpnb_step {cfg₁ cfg₂ : SymConfig} {st : SymStep} {p : ℤ}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (_hno101 : st.result.nextState ≠ 101)
    (hne51 : st.fromState ≠ 51) (hne3 : st.fromState ≠ 3) (hne20 : st.fromState ≠ 20)
    (hpnb : (cfg₁.tape p).1 ≠ SymKind.boundary) :
    (cfg₂.tape p).1 ≠ SymKind.boundary := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  by_cases hp : p = cfg₁.headPos
  · subst hp
    intro hw2
    have hread : st.readSym.1 ≠ SymKind.boundary := by
      intro h
      rw [hs_read] at h
      exact hpnb h
    rw [hs_cfg, symStepConfig_tape_headPos] at hw2
    exact (hashWrite_cases st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
      hne51 hne3 hne20 hread) hw2
  · rw [hs_cfg, symStepConfig_tape_of_ne _ _ hp]
    exact hpnb

/-- ¬标记读通用件（from ∉ {4,13,21,29,100}）。 -/
lemma not_markRead_of_states {cfg₁ cfg₂ : SymConfig} {st : SymStep}
    (hst : SymSteps VerifierSym.transition cfg₁ [st] cfg₂)
    (hleg : cfg₁.state ∈ VerifierSym.legalStates)
    (hno101 : st.result.nextState ≠ 101)
    (h1 : st.fromState ≠ 4) (h2 : st.fromState ≠ 13) (h3 : st.fromState ≠ 21)
    (h4 : st.fromState ≠ 29) (h5 : st.fromState ≠ 100) :
    ¬(st.readSym.1 = SymKind.sel ∨ st.readSym.1 = SymKind.nosel) := by
  intro hsn
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  have hq := markRead_states st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm hsn hno101
  rcases hq with h | h | h | h | h
  · exact h1 h
  · exact h2 h
  · exact h3 h
  · exact h4 h
  · exact h5 h

-- 84–87 段决定件批次
/-- 84 段：非陷阱 ⇒ next ∈ {84, 85}。 -/
theorem state84_nexts (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 84 → r.nextState ≠ 101 → r.nextState = 84 ∨ r.nextState = 85 := by
  cases m <;> cases k <;> decide

/-- 84 段：84→84 行 ⇒ L。 -/
theorem state84_L (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 84 → r.nextState = 84 → r.moveDir = Dir.L := by
  cases m <;> cases k <;> decide

/-- 84 段：84→84 行读非 #。 -/
theorem state84_no_hash (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 84 → r.nextState = 84 → k ≠ SymKind.boundary := by
  cases m <;> cases k <;> decide

/-- 84 段：84→85 行 ⇒ 读 # 且 L。 -/
theorem state84_HL (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 84 → r.nextState = 85 → k = SymKind.boundary ∧ r.moveDir = Dir.L := by
  cases m <;> cases k <;> decide

/-- 85 段：非陷阱 ⇒ next ∈ {85, 86}。 -/
theorem state85_nexts (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 85 → r.nextState ≠ 101 → r.nextState = 85 ∨ r.nextState = 86 := by
  cases m <;> cases k <;> decide

/-- 85 段：85→85 行 ⇒ L。 -/
theorem state85_L (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 85 → r.nextState = 85 → r.moveDir = Dir.L := by
  cases m <;> cases k <;> decide

/-- 85 段：85→86 行 ⇒ 读 # 且 R。 -/
theorem state85_HR (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 85 → r.nextState = 86 → k = SymKind.boundary ∧ r.moveDir = Dir.R := by
  cases m <;> cases k <;> decide

/-- 85/86/87 段：非陷阱读非 s/n（经 markRead_states 查 4/13/21/29/100 均不中）。 -/
theorem state858687_reads (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      ((q : ℕ) = 85 ∨ (q : ℕ) = 86 ∨ (q : ℕ) = 87) → r.nextState ≠ 101 →
      (k = SymKind.data0 ∨ k = SymKind.data1 ∨ k = SymKind.boundary) := by
  cases m <;> cases k <;> decide

/-- 86 段：非陷阱 ⇒ next ∈ {86, 87}。 -/
theorem state86_nexts (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 86 → r.nextState ≠ 101 → r.nextState = 86 ∨ r.nextState = 87 := by
  cases m <;> cases k <;> decide

/-- 86 段：86→86 行 ⇒ R。 -/
theorem state86_R (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 86 → r.nextState = 86 → r.moveDir = Dir.R := by
  cases m <;> cases k <;> decide

/-- 86 段：86→87 行 ⇒ S。 -/
theorem state86_S (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 86 → r.nextState = 87 → r.moveDir = Dir.S := by
  cases m <;> cases k <;> decide

/-- 87 段：非陷阱 ⇒ next ∈ {87, 20}。 -/
theorem state87_nexts (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 87 → r.nextState ≠ 101 → r.nextState = 87 ∨ r.nextState = 20 := by
  cases m <;> cases k <;> decide

/-- 87 段：87→87 行 ⇒ R。 -/
theorem state87_R (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 87 → r.nextState = 87 → r.moveDir = Dir.R := by
  cases m <;> cases k <;> decide

/-- 87 段：87→20 行 ⇒ 读 # 且 S。 -/
theorem state87_H20 (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 87 → r.nextState = 20 → k = SymKind.boundary ∧ r.moveDir = Dir.S := by
  cases m <;> cases k <;> decide

/-- 84 态读 c 行恒等写（c 保持；hpc 维持砖）。 -/
theorem state84_c_write (m : Bool) : ∀ (q : Fin 102), (q : ℕ) = 84 →
    ∀ r ∈ VerifierSym.transition ((q : ℕ), SymKind.consumed, m), r.writeSym.1 = SymKind.consumed := by
  cases m <;> decide

/-- [C-3] 51 支分派：新 #₀ 落 ≥p 区（a2p 技法：51 头 ≥ p 由 h51p 供；读 d0 一击三得）⇒ 包保持。 -/
lemma five_step_51 {inst : SubsetSumInstance} {cfg₀ cfg₂ : SymConfig} {st : SymStep}
    {S : SymFiveSt}
    (hst : SymSteps VerifierSym.transition cfg₀ [st] cfg₂)
    (hleg : cfg₀.state ∈ VerifierSym.legalStates)
    (hno101 : st.result.nextState ≠ 101)
    (hinv : SymFiveInv inst cfg₀ S)
    (h51h : st.fromState = 51) :
    ∃ S' : SymFiveSt, SymFiveInv inst cfg₂ S' ∧
      (symFive st = true → S'.p = cfg₀.headPos) := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  have hstate : cfg₂.state = st.result.nextState := by rw [hs_cfg]; rfl
  have hhead : cfg₂.headPos = cfg₀.headPos + st.result.moveDir.toInt := by rw [hs_cfg]; rfl
  have hgo := state51_go st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h51h hno101
  have hstamp51 := state51_stamp st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h51h hno101
  have hg4 : st.result.nextState = 4 := hgo.1
  have hmvR51 : st.result.moveDir = Dir.R := hgo.2
  have hd0read : st.readSym.1 = SymKind.data0 := hstamp51.1
  have hne20 : st.result.nextState ≠ 20 := by omega
  have hne21 : st.result.nextState ≠ 21 := by omega
  have hne5 : st.result.nextState ≠ 5 := by omega
  have hne13 : st.result.nextState ≠ 13 := by omega
  have hne51 : st.result.nextState ≠ 51 := by omega
  have hne86 : st.result.nextState ≠ 86 := by omega
  have hne87 : st.result.nextState ≠ 87 := by omega
  have hf2 : st.fromState ≠ 2 := by intro h; omega
  have hf3 : st.fromState ≠ 3 := by intro h; omega
  have hf4 : st.fromState ≠ 4 := by intro h; omega
  have hf5 : st.fromState ≠ 5 := by intro h; omega
  have hf21 : st.fromState ≠ 21 := by intro h; omega
  have hpre51 : cfg₀.state = 51 := hs_from ▸ h51h
  have hq4 : 2 ≤ S.q₄ := hinv.hq4ge.elim id
    (fun h0 => absurd ((hpre51.symm).trans h0) (by decide))
  have h51pre : S.p ≤ cfg₀.headPos := hinv.h51p hpre51
  have hblk' : SymBlk cfg₂ S.α S.p :=
    SymBlk.step_of_notFive21 hst hleg hno101 (fun h => hf5 h) (fun h => hf21 h) hinv.hblk
  have hC4' : SymLedger inst cfg₂ S.q₄ :=
    ledger_notTwoFour hst hleg hno101 (fun h => hf2 h) (fun h => hf4 h) hinv.hC4
  have hCNM' : SymClearedGone cfg₂ S.α₀ S.α := SymClearedGone.step_any hst hleg hno101 hinv.hCNM
  have hα₀' : S.α₀ ≤ S.q₄ + 1 := hinv.hα₀
  have hαp' : S.α ≤ S.p + 1 := hinv.hαp
  have hempQ' : (cfg₂.state = 4 ∨ cfg₂.state = 51) → S.α = S.p + 1 :=
    fun _ => hinv.hempQ (Or.inr hpre51)
  have hB4' : (cfg₂.state = 20 ∨ cfg₂.state = 21) →
      ∀ z : ℤ, z < cfg₂.headPos → (cfg₂.tape z).1 = SymKind.consumed → False := by
    intro h
    rcases h with h | h
    · exact absurd (hstate.symm.trans h) hne20
    · exact absurd (hstate.symm.trans h) hne21
  have h5pos' : cfg₂.state = 5 → S.α ≠ S.p + 1 → cfg₂.headPos = S.p + 1 :=
    fun h _ => absurd (hstate.symm.trans h) hne5
  have hA5' : cfg₂.state = 5 → S.p < cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne5
  have hwalk13' : cfg₂.state = 13 →
      SymWalkConsumed cfg₂ S.s ∧ S.s < cfg₂.headPos ∧ S.α ≤ S.s :=
    fun h => absurd (hstate.symm.trans h) hne13
  have h86le' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → cfg₂.headPos ≤ S.q₄ - 1 := by
    intro h
    rcases h with h86 | h87
    · exact absurd (hstate.symm.trans h86) hne86
    · exact absurd (hstate.symm.trans h87) hne87
  have hnext1' : cfg₂.state = 5 → S.α = S.p + 1 → cfg₂.headPos = S.q₄ + 1 :=
    fun h _ => absurd (hstate.symm.trans h) hne5
  have hq4ge' : 2 ≤ S.q₄ ∨ cfg₂.state = 4 := Or.inl hq4
  have hbnd' : ∀ z : ℤ, (cfg₂.tape z).1 = SymKind.boundary →
      z = 0 ∨ z = S.q₄ - 1 ∨ z = symEndPos inst ∨ (cfg₂.state = 4 ∧ z = cfg₂.headPos - 1) := by
    intro z hz
    by_cases hzh : z = cfg₀.headPos
    · have h4 : cfg₂.state = 4 := hstate.trans hg4
      exact Or.inr (Or.inr (Or.inr ⟨h4, by
        rw [hzh]
        have hh := hhead
        rw [hmvR51] at hh
        rw [hh]
        rw [show Dir.R.toInt = (1 : ℤ) from rfl]
        omega⟩))
    · have hz1 : (cfg₀.tape z).1 = SymKind.boundary := by
        rw [hs_cfg, symStepConfig_tape_of_ne _ _ (show z ≠ cfg₀.headPos by omega)] at hz
        exact hz
      rcases hinv.hbnd z hz1 with h0 | hq | hE | h4e
      · exact Or.inl h0
      · exact Or.inr (Or.inl hq)
      · exact Or.inr (Or.inr (Or.inl hE))
      · exact absurd (h51h.symm.trans (hs_from.trans h4e.1)) (by decide)
  have hSharp' : cfg₂.state ∈ symMainSet → (cfg₂.tape (S.q₄ - 1)).1 = SymKind.boundary :=
    fun h => absurd h (by rw [hstate, hg4]; decide)
  have hαqU' : cfg₂.state ∈ symMainSet → S.α = S.q₄ + 1 :=
    fun h => absurd h (by rw [hstate, hg4]; decide)
  have hpc' : cfg₂.state ∈ symWorkSet → (cfg₂.tape S.p).1 = SymKind.consumed :=
    fun h => absurd h (by rw [hstate, hg4]; decide)
  have h84le' : cfg₂.state = 84 → S.q₄ - 1 ≤ cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) (by rw [hg4]; decide)
  have h84le2' : cfg₂.state = 84 → cfg₂.headPos ≤ S.p :=
    fun h => absurd (hstate.symm.trans h) (by rw [hg4]; decide)
  have h85le' : cfg₂.state = 85 → cfg₂.headPos ≤ S.q₄ - 2 :=
    fun h => absurd (hstate.symm.trans h) (by rw [hg4]; decide)
  have h51p' : cfg₂.state = 51 → S.p ≤ cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) (by rw [hg4]; decide)
  have hgap' : SymGapNoAlpha inst S.q₄ cfg₂ :=
    SymGapNoAlpha.step_of_notMarked_read_R hst hleg
      (fun hsn => hsn.elim (fun h => absurd (hd0read.symm.trans h) (by decide))
        (fun h => absurd (hd0read.symm.trans h) (by decide)))
      hmvR51 hinv.hgap hinv.hC4
  have h20d' : (cfg₂.state = 4 ∨ cfg₂.state = 21 ∨ cfg₂.state = 51) →
      (cfg₂.tape (S.q₄ - 1)).1 = SymKind.data0 := by
    intro _
    have hz : S.q₄ - 1 ≠ cfg₀.headPos := by
      have hge : S.q₄ ≤ cfg₀.headPos := hinv.h51q4 hpre51
      omega
    rw [hs_cfg, symStepConfig_tape_of_ne _ _ hz]
    exact hinv.h20d (Or.inr (Or.inr hpre51))
  have h4head' : cfg₂.state = 4 → (cfg₂.tape (cfg₂.headPos - 1)).1 = SymKind.boundary := by
    intro _
    have hh1 : cfg₂.headPos - 1 = cfg₀.headPos := by
      rw [hhead, hmvR51, show Dir.R.toInt = (1 : ℤ) from rfl]
      ring
    rw [hh1, hs_cfg, symStepConfig_tape_headPos]
    exact hstamp51.2.1
  have h51q4' : cfg₂.state = 51 → S.q₄ ≤ cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne51
  have h86ge' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → 1 ≤ cfg₂.headPos := by
    intro h
    rcases h with h86 | h87
    · exact absurd (hstate.symm.trans h86) hne86
    · exact absurd (hstate.symm.trans h87) hne87
  have h20h' : cfg₂.state = 20 → cfg₂.headPos = S.q₄ - 1 :=
    fun h => absurd (hstate.symm.trans h) hne20
  have h5pc' : cfg₂.state = 5 → (cfg₂.tape S.p).1 ≠ SymKind.boundary :=
    fun h => absurd (hstate.symm.trans h) hne5
  exact ⟨{ α := S.α, p := S.p, q₄ := S.q₄, s := S.s, α₀ := S.α₀ },
    ⟨hblk', hC4', hCNM', hα₀', hgap', hαp', hempQ', hB4', h5pos', hA5', hwalk13',
      hSharp', h86le', hαqU', hnext1', hq4ge', hbnd', hpc', h84le', h84le2', h85le', h51p', h20d', h4head', h51q4', h86ge', h20h', h5pc', hinv.hq4e⟩,
    fun hf => by rw [symFive, h51h] at hf; exact absurd hf (by decide)⟩
/-- [C-3] 85 支分派：84 首撞后下行/进 86 ⇒ 包保持。 -/
lemma five_step_85 {inst : SubsetSumInstance} {cfg₀ cfg₂ : SymConfig} {st : SymStep}
    {S : SymFiveSt}
    (hst : SymSteps VerifierSym.transition cfg₀ [st] cfg₂)
    (hleg : cfg₀.state ∈ VerifierSym.legalStates)
    (hno101 : st.result.nextState ≠ 101)
    (h58 : cfg₀.state ∉ symPhaseSet)
    (hinv : SymFiveInv inst cfg₀ S)
    (h85h : st.fromState = 85) :
    ∃ S' : SymFiveSt, SymFiveInv inst cfg₂ S' ∧
      (symFive st = true → S'.p = cfg₀.headPos) := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  have hstate : cfg₂.state = st.result.nextState := by rw [hs_cfg]; rfl
  have hhead : cfg₂.headPos = cfg₀.headPos + st.result.moveDir.toInt := by rw [hs_cfg]; rfl
  have hres : st.result.nextState = 85 ∨ st.result.nextState = 86 :=
    state85_nexts st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h85h hno101
  have hne4 : st.result.nextState ≠ 4 := by intro h; rcases hres with h' | h' <;> omega
  have hne51 : st.result.nextState ≠ 51 := by intro h; rcases hres with h' | h' <;> omega
  have hne20 : st.result.nextState ≠ 20 := by intro h; rcases hres with h' | h' <;> omega
  have hne21 : st.result.nextState ≠ 21 := by intro h; rcases hres with h' | h' <;> omega
  have hne5 : st.result.nextState ≠ 5 := by intro h; rcases hres with h' | h' <;> omega
  have hne13 : st.result.nextState ≠ 13 := by intro h; rcases hres with h' | h' <;> omega
  have hne84 : st.result.nextState ≠ 84 := by intro h; rcases hres with h' | h' <;> omega
  have hne87 : st.result.nextState ≠ 87 := by intro h; rcases hres with h' | h' <;> omega
  have hf2 : st.fromState ≠ 2 := by intro h; omega
  have hf3 : st.fromState ≠ 3 := by intro h; omega
  have hf4 : st.fromState ≠ 4 := by intro h; omega
  have hf5 : st.fromState ≠ 5 := by intro h; omega
  have hf13 : st.fromState ≠ 13 := by intro h; omega
  have hf20 : st.fromState ≠ 20 := by intro h; omega
  have hf21 : st.fromState ≠ 21 := by intro h; omega
  have hf51 : st.fromState ≠ 51 := by intro h; omega
  have hf100 : st.fromState ≠ 100 := by intro h; omega
  have hpre85 : cfg₀.state = 85 := hs_from ▸ h85h
  have hpreW : cfg₀.state ∈ symWorkSet := by rw [hpre85]; decide
  have hpre : cfg₀.state ∈ symMainSet := by rw [hpre85]; decide
  have h85low : cfg₀.headPos ≤ S.q₄ - 2 := hinv.h85le hpre85
  have hq4 : 2 ≤ S.q₄ := hinv.hq4ge.elim id
    (fun h0 => absurd ((hpre85.symm).trans h0) (by decide))
  have hαple : S.α ≤ S.p := ((hinv.hblk S.p).mp (hinv.hpc hpreW)).1
  have hq4p : S.q₄ + 1 ≤ S.p := by
    have hαq : S.α = S.q₄ + 1 := hinv.hαqU hpre
    omega
  have hblk' : SymBlk cfg₂ S.α S.p :=
    SymBlk.step_of_notFive21 hst hleg hno101 (fun h => hf5 h) (fun h => hf21 h) hinv.hblk
  have hC4' : SymLedger inst cfg₂ S.q₄ :=
    ledger_notTwoFour hst hleg hno101 (fun h => hf2 h) (fun h => hf4 h) hinv.hC4
  have hCNM' : SymClearedGone cfg₂ S.α₀ S.α := SymClearedGone.step_any hst hleg hno101 hinv.hCNM
  have hα₀' : S.α₀ ≤ S.q₄ + 1 := hinv.hα₀
  have hαp' : S.α ≤ S.p + 1 := hinv.hαp
  have hempQ' : (cfg₂.state = 4 ∨ cfg₂.state = 51) → S.α = S.p + 1 := by
    intro h
    rcases h with h | h
    · exact absurd (hstate.symm.trans h) hne4
    · exact absurd (hstate.symm.trans h) hne51
  have hB4' : (cfg₂.state = 20 ∨ cfg₂.state = 21) →
      ∀ z : ℤ, z < cfg₂.headPos → (cfg₂.tape z).1 = SymKind.consumed → False := by
    intro h
    rcases h with h | h
    · exact absurd (hstate.symm.trans h) hne20
    · exact absurd (hstate.symm.trans h) hne21
  have h5pos' : cfg₂.state = 5 → S.α ≠ S.p + 1 → cfg₂.headPos = S.p + 1 :=
    fun h _ => absurd (hstate.symm.trans h) hne5
  have hA5' : cfg₂.state = 5 → S.p < cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne5
  have hwalk13' : cfg₂.state = 13 →
      SymWalkConsumed cfg₂ S.s ∧ S.s < cfg₂.headPos ∧ S.α ≤ S.s :=
    fun h => absurd (hstate.symm.trans h) hne13
  have h86le' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → cfg₂.headPos ≤ S.q₄ - 1 := by
    intro h
    rcases h with h86 | h87
    · have h86r : st.result.nextState = 86 := hstate.symm.trans h86
      have hmvR := (state85_HR st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h85h h86r).2
      rw [hhead, hmvR, show Dir.R.toInt = (1 : ℤ) from rfl]
      omega
    · exact absurd (hstate.symm.trans h87) hne87
  have hnext1' : cfg₂.state = 5 → S.α = S.p + 1 → cfg₂.headPos = S.q₄ + 1 :=
    fun h _ => absurd (hstate.symm.trans h) hne5
  have hq4ge' : 2 ≤ S.q₄ ∨ cfg₂.state = 4 := Or.inl hq4
  have hbnd' : ∀ z : ℤ, (cfg₂.tape z).1 = SymKind.boundary →
      z = 0 ∨ z = S.q₄ - 1 ∨ z = symEndPos inst ∨ (cfg₂.state = 4 ∧ z = cfg₂.headPos - 1) :=
    hbnd_frame hst hleg hno101 (fun h => hf51 h) (fun h => hf3 h) (fun h => hf20 h)
      (fun h => absurd (h85h.symm.trans (hs_from.trans h)) (by decide)) hinv.hbnd
  have hSharp' : cfg₂.state ∈ symMainSet → (cfg₂.tape (S.q₄ - 1)).1 = SymKind.boundary := by
    intro _
    by_cases hdh : st.readSym.1 = SymKind.boundary
    · by_cases hph : cfg₀.headPos = S.q₄ - 1
      · have hid := hashRead_id st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
          (fun h => hf51 h) (fun h => hf3 h) (fun h => hf20 h) hdh
        rw [← hph, hs_cfg, symStepConfig_tape_headPos]
        exact (congrArg Prod.fst hid).trans hdh
      · rw [hs_cfg, symStepConfig_tape_of_ne _ _ (show S.q₄ - 1 ≠ cfg₀.headPos by omega)]
        exact hinv.hSharp hpre
    · have hph : cfg₀.headPos ≠ S.q₄ - 1 := by
        intro he
        have : st.readSym.1 = SymKind.boundary := by rw [hs_read, he]; exact hinv.hSharp hpre
        exact hdh this
      rw [hs_cfg, symStepConfig_tape_of_ne _ _ (show S.q₄ - 1 ≠ cfg₀.headPos by omega)]
      exact hinv.hSharp hpre
  have hαqU' : cfg₂.state ∈ symMainSet → S.α = S.q₄ + 1 := fun _ => hinv.hαqU hpre
  have hpc' : cfg₂.state ∈ symWorkSet → (cfg₂.tape S.p).1 = SymKind.consumed := by
    intro _
    by_cases hph : cfg₀.headPos = S.p
    · exfalso
      omega
    · rw [hs_cfg, symStepConfig_tape_of_ne _ _ (show S.p ≠ cfg₀.headPos by omega)]
      exact hinv.hpc hpreW
  have h84le' : cfg₂.state = 84 → S.q₄ - 1 ≤ cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne84
  have h84le2' : cfg₂.state = 84 → cfg₂.headPos ≤ S.p :=
    fun h => absurd (hstate.symm.trans h) hne84
  have h85le' : cfg₂.state = 85 → cfg₂.headPos ≤ S.q₄ - 2 := by
    intro h855
    have h85r : st.result.nextState = 85 := hstate.symm.trans h855
    have hmvL := state85_L st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h85h h85r
    rw [hhead, hmvL, show Dir.L.toInt = (-1 : ℤ) from rfl]
    omega
  have h51p' : cfg₂.state = 51 → S.p ≤ cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne51
  have hrdnn : ¬(st.readSym.1 = SymKind.sel ∨ st.readSym.1 = SymKind.nosel) :=
    not_markRead_of_states hst hleg hno101 (fun h => hf4 h) (fun h => hf13 h) (fun h => hf21 h)
      (fun h29 => h58 (by rw [← hs_from, h29]; decide)) (fun h => hf100 h)
  have hgap' : SymGapNoAlpha inst S.q₄ cfg₂ := by
    by_cases hmR : st.result.moveDir = Dir.R
    · exact SymGapNoAlpha.step_of_notMarked_read_R hst hleg hrdnn hmR hinv.hgap hinv.hC4
    · have hmv : st.result.moveDir = Dir.L ∨ st.result.moveDir = Dir.R := by
        rcases hres with h' | h'
        · exact Or.inl (state85_L st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h85h h')
        · exact Or.inr ((state85_HR st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h85h h').2)
      have hmvL : st.result.moveDir = Dir.L := hmv.elim id (fun hR => absurd hR hmR)
      have hle : cfg₂.headPos ≤ cfg₀.headPos := by
        rw [hhead, hmvL, show Dir.L.toInt = (-1 : ℤ) from rfl]
        omega
      exact SymGapNoAlpha.step_shrink hst hle hinv.hgap
  have h20d' : (cfg₂.state = 4 ∨ cfg₂.state = 21 ∨ cfg₂.state = 51) →
      (cfg₂.tape (S.q₄ - 1)).1 = SymKind.data0 := by
    intro h
    rcases h with h | h | h
    · exact absurd (hstate.symm.trans h) hne4
    · exact absurd (hstate.symm.trans h) hne21
    · exact absurd (hstate.symm.trans h) hne51
  have h4head' : cfg₂.state = 4 → (cfg₂.tape (cfg₂.headPos - 1)).1 = SymKind.boundary :=
    fun h => absurd (hstate.symm.trans h) hne4
  have h51q4' : cfg₂.state = 51 → S.q₄ ≤ cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne51
  have h86ge' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → 1 ≤ cfg₂.headPos := by
    intro h
    rcases h with h86 | h87
    · have h86r : st.result.nextState = 86 := hstate.symm.trans h86
      have hHR := state85_HR st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h85h h86r
      have hrd : (cfg₀.tape cfg₀.headPos).1 = SymKind.boundary := by
        rw [← hs_read]
        exact hHR.1
      have h0 : (0 : ℤ) ≤ cfg₀.headPos := by
        rcases hinv.hbnd cfg₀.headPos hrd with h0' | hq' | hE' | h4e'
        · omega
        · omega
        · have hE0 : (0 : ℤ) ≤ symEndPos inst := by unfold symEndPos; omega
          omega
        · have := h4e'.2; omega
      rw [hhead, hHR.2, show Dir.R.toInt = (1 : ℤ) from rfl]
      omega
    · exact absurd (hstate.symm.trans h87) hne87
  have h20h' : cfg₂.state = 20 → cfg₂.headPos = S.q₄ - 1 :=
    fun h => absurd (hstate.symm.trans h) hne20
  have h5pc' : cfg₂.state = 5 → (cfg₂.tape S.p).1 ≠ SymKind.boundary :=
    fun h => absurd (hstate.symm.trans h) hne5
  exact ⟨{ α := S.α, p := S.p, q₄ := S.q₄, s := S.s, α₀ := S.α₀ },
    ⟨hblk', hC4', hCNM', hα₀', hgap', hαp', hempQ', hB4', h5pos', hA5', hwalk13',
      hSharp', h86le', hαqU', hnext1', hq4ge', hbnd', hpc', h84le', h84le2', h85le', h51p', h20d', h4head', h51q4', h86ge', h20h', h5pc', hinv.hq4e⟩,
    fun hf => by rw [symFive, h85h] at hf; exact absurd hf (by decide)⟩
/-- [C-3] 86 支分派：清 m 计数器西扫/转 87 ⇒ 包保持。 -/
lemma five_step_86 {inst : SubsetSumInstance} {cfg₀ cfg₂ : SymConfig} {st : SymStep}
    {S : SymFiveSt}
    (hst : SymSteps VerifierSym.transition cfg₀ [st] cfg₂)
    (hleg : cfg₀.state ∈ VerifierSym.legalStates)
    (hno101 : st.result.nextState ≠ 101)
    (h58 : cfg₀.state ∉ symPhaseSet)
    (hinv : SymFiveInv inst cfg₀ S)
    (h86h : st.fromState = 86) :
    ∃ S' : SymFiveSt, SymFiveInv inst cfg₂ S' ∧
      (symFive st = true → S'.p = cfg₀.headPos) := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  have hstate : cfg₂.state = st.result.nextState := by rw [hs_cfg]; rfl
  have hhead : cfg₂.headPos = cfg₀.headPos + st.result.moveDir.toInt := by rw [hs_cfg]; rfl
  have hres : st.result.nextState = 86 ∨ st.result.nextState = 87 :=
    state86_nexts st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h86h hno101
  have hne4 : st.result.nextState ≠ 4 := by intro h; rcases hres with h' | h' <;> omega
  have hne51 : st.result.nextState ≠ 51 := by intro h; rcases hres with h' | h' <;> omega
  have hne20 : st.result.nextState ≠ 20 := by intro h; rcases hres with h' | h' <;> omega
  have hne21 : st.result.nextState ≠ 21 := by intro h; rcases hres with h' | h' <;> omega
  have hne5 : st.result.nextState ≠ 5 := by intro h; rcases hres with h' | h' <;> omega
  have hne13 : st.result.nextState ≠ 13 := by intro h; rcases hres with h' | h' <;> omega
  have hne84 : st.result.nextState ≠ 84 := by intro h; rcases hres with h' | h' <;> omega
  have hne85 : st.result.nextState ≠ 85 := by intro h; rcases hres with h' | h' <;> omega
  have hf2 : st.fromState ≠ 2 := by intro h; omega
  have hf3 : st.fromState ≠ 3 := by intro h; omega
  have hf4 : st.fromState ≠ 4 := by intro h; omega
  have hf5 : st.fromState ≠ 5 := by intro h; omega
  have hf13 : st.fromState ≠ 13 := by intro h; omega
  have hf20 : st.fromState ≠ 20 := by intro h; omega
  have hf21 : st.fromState ≠ 21 := by intro h; omega
  have hf51 : st.fromState ≠ 51 := by intro h; omega
  have hf100 : st.fromState ≠ 100 := by intro h; omega
  have hpre86 : cfg₀.state = 86 := hs_from ▸ h86h
  have hpreW : cfg₀.state ∈ symWorkSet := by rw [hpre86]; decide
  have hpre : cfg₀.state ∈ symMainSet := by rw [hpre86]; decide
  have h86low : cfg₀.headPos ≤ S.q₄ - 1 := hinv.h86le (Or.inl hpre86)
  have hq4 : 2 ≤ S.q₄ := hinv.hq4ge.elim id
    (fun h0 => absurd ((hpre86.symm).trans h0) (by decide))
  have hαple : S.α ≤ S.p := ((hinv.hblk S.p).mp (hinv.hpc hpreW)).1
  have hq4p : S.q₄ + 1 ≤ S.p := by
    have hαq : S.α = S.q₄ + 1 := hinv.hαqU hpre
    omega
  have hblk' : SymBlk cfg₂ S.α S.p :=
    SymBlk.step_of_notFive21 hst hleg hno101 (fun h => hf5 h) (fun h => hf21 h) hinv.hblk
  have hC4' : SymLedger inst cfg₂ S.q₄ :=
    ledger_notTwoFour hst hleg hno101 (fun h => hf2 h) (fun h => hf4 h) hinv.hC4
  have hCNM' : SymClearedGone cfg₂ S.α₀ S.α := SymClearedGone.step_any hst hleg hno101 hinv.hCNM
  have hα₀' : S.α₀ ≤ S.q₄ + 1 := hinv.hα₀
  have hαp' : S.α ≤ S.p + 1 := hinv.hαp
  have hempQ' : (cfg₂.state = 4 ∨ cfg₂.state = 51) → S.α = S.p + 1 := by
    intro h
    rcases h with h | h
    · exact absurd (hstate.symm.trans h) hne4
    · exact absurd (hstate.symm.trans h) hne51
  have hB4' : (cfg₂.state = 20 ∨ cfg₂.state = 21) →
      ∀ z : ℤ, z < cfg₂.headPos → (cfg₂.tape z).1 = SymKind.consumed → False := by
    intro h
    rcases h with h | h
    · exact absurd (hstate.symm.trans h) hne20
    · exact absurd (hstate.symm.trans h) hne21
  have h5pos' : cfg₂.state = 5 → S.α ≠ S.p + 1 → cfg₂.headPos = S.p + 1 :=
    fun h _ => absurd (hstate.symm.trans h) hne5
  have hA5' : cfg₂.state = 5 → S.p < cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne5
  have hwalk13' : cfg₂.state = 13 →
      SymWalkConsumed cfg₂ S.s ∧ S.s < cfg₂.headPos ∧ S.α ≤ S.s :=
    fun h => absurd (hstate.symm.trans h) hne13
  have h86le' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → cfg₂.headPos ≤ S.q₄ - 1 := by
    intro h
    rcases h with h86 | h87
    · have h86r : st.result.nextState = 86 := hstate.symm.trans h86
      have hmvR := state86_R st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h86h h86r
      have hrd := state8687_R_read st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
        (Or.inl h86h) hno101 hmvR
      have hne' : cfg₀.headPos ≠ S.q₄ - 1 := by
        intro he
        have hb : st.readSym.1 = SymKind.boundary := by
          rw [hs_read, he]
          exact hinv.hSharp hpre
        rcases hrd with hd | hd
        · rw [hd] at hb; exact absurd hb (by decide)
        · rw [hd] at hb; exact absurd hb (by decide)
      have h2 : cfg₀.headPos ≤ S.q₄ - 2 := by omega
      rw [hhead, hmvR, show Dir.R.toInt = (1 : ℤ) from rfl]
      omega
    · have h87r : st.result.nextState = 87 := hstate.symm.trans h87
      have hmvS := state86_S st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h86h h87r
      rw [hhead, hmvS, show Dir.S.toInt = (0 : ℤ) from rfl]
      omega
  have hnext1' : cfg₂.state = 5 → S.α = S.p + 1 → cfg₂.headPos = S.q₄ + 1 :=
    fun h _ => absurd (hstate.symm.trans h) hne5
  have hq4ge' : 2 ≤ S.q₄ ∨ cfg₂.state = 4 := Or.inl hq4
  have hbnd' : ∀ z : ℤ, (cfg₂.tape z).1 = SymKind.boundary →
      z = 0 ∨ z = S.q₄ - 1 ∨ z = symEndPos inst ∨ (cfg₂.state = 4 ∧ z = cfg₂.headPos - 1) :=
    hbnd_frame hst hleg hno101 (fun h => hf51 h) (fun h => hf3 h) (fun h => hf20 h)
      (fun h => absurd (h86h.symm.trans (hs_from.trans h)) (by decide)) hinv.hbnd
  have hSharp' : cfg₂.state ∈ symMainSet → (cfg₂.tape (S.q₄ - 1)).1 = SymKind.boundary := by
    intro _
    by_cases hdh : st.readSym.1 = SymKind.boundary
    · by_cases hph : cfg₀.headPos = S.q₄ - 1
      · have hid := hashRead_id st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
          (fun h => hf51 h) (fun h => hf3 h) (fun h => hf20 h) hdh
        rw [← hph, hs_cfg, symStepConfig_tape_headPos]
        exact (congrArg Prod.fst hid).trans hdh
      · rw [hs_cfg, symStepConfig_tape_of_ne _ _ (show S.q₄ - 1 ≠ cfg₀.headPos by omega)]
        exact hinv.hSharp hpre
    · have hph : cfg₀.headPos ≠ S.q₄ - 1 := by
        intro he
        have : st.readSym.1 = SymKind.boundary := by rw [hs_read, he]; exact hinv.hSharp hpre
        exact hdh this
      rw [hs_cfg, symStepConfig_tape_of_ne _ _ (show S.q₄ - 1 ≠ cfg₀.headPos by omega)]
      exact hinv.hSharp hpre
  have hαqU' : cfg₂.state ∈ symMainSet → S.α = S.q₄ + 1 := fun _ => hinv.hαqU hpre
  have hpc' : cfg₂.state ∈ symWorkSet → (cfg₂.tape S.p).1 = SymKind.consumed := by
    intro _
    by_cases hph : cfg₀.headPos = S.p
    · exfalso
      omega
    · rw [hs_cfg, symStepConfig_tape_of_ne _ _ (show S.p ≠ cfg₀.headPos by omega)]
      exact hinv.hpc hpreW
  have h84le' : cfg₂.state = 84 → S.q₄ - 1 ≤ cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne84
  have h84le2' : cfg₂.state = 84 → cfg₂.headPos ≤ S.p :=
    fun h => absurd (hstate.symm.trans h) hne84
  have h85le' : cfg₂.state = 85 → cfg₂.headPos ≤ S.q₄ - 2 :=
    fun h => absurd (hstate.symm.trans h) hne85
  have h51p' : cfg₂.state = 51 → S.p ≤ cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne51
  have hrdnn : ¬(st.readSym.1 = SymKind.sel ∨ st.readSym.1 = SymKind.nosel) :=
    not_markRead_of_states hst hleg hno101 (fun h => hf4 h) (fun h => hf13 h) (fun h => hf21 h)
      (fun h29 => h58 (by rw [← hs_from, h29]; decide)) (fun h => hf100 h)
  have hgap' : SymGapNoAlpha inst S.q₄ cfg₂ := by
    by_cases hmR : st.result.moveDir = Dir.R
    · exact SymGapNoAlpha.step_of_notMarked_read_R hst hleg hrdnn hmR hinv.hgap hinv.hC4
    · have hmv : st.result.moveDir = Dir.R ∨ st.result.moveDir = Dir.S := by
        rcases hres with h' | h'
        · exact Or.inl (state86_R st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h86h h')
        · exact Or.inr (state86_S st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h86h h')
      have hmvS : st.result.moveDir = Dir.S := hmv.elim (fun hR => absurd hR hmR) id
      have hle : cfg₂.headPos ≤ cfg₀.headPos := by
        rw [hhead, hmvS, show Dir.S.toInt = (0 : ℤ) from rfl]
        omega
      exact SymGapNoAlpha.step_shrink hst hle hinv.hgap
  have h20d' : (cfg₂.state = 4 ∨ cfg₂.state = 21 ∨ cfg₂.state = 51) →
      (cfg₂.tape (S.q₄ - 1)).1 = SymKind.data0 := by
    intro h
    rcases h with h | h | h
    · exact absurd (hstate.symm.trans h) hne4
    · exact absurd (hstate.symm.trans h) hne21
    · exact absurd (hstate.symm.trans h) hne51
  have h4head' : cfg₂.state = 4 → (cfg₂.tape (cfg₂.headPos - 1)).1 = SymKind.boundary :=
    fun h => absurd (hstate.symm.trans h) hne4
  have h51q4' : cfg₂.state = 51 → S.q₄ ≤ cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne51
  have h86ge' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → 1 ≤ cfg₂.headPos := by
    intro h
    rcases h with h86 | h87
    · have h86r : st.result.nextState = 86 := hstate.symm.trans h86
      have hmvR := state86_R st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h86h h86r
      have hge : 1 ≤ cfg₀.headPos := hinv.h86ge (Or.inl hpre86)
      rw [hhead, hmvR, show Dir.R.toInt = (1 : ℤ) from rfl]
      omega
    · have h87r : st.result.nextState = 87 := hstate.symm.trans h87
      have hmvS := state86_S st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h86h h87r
      have hge : 1 ≤ cfg₀.headPos := hinv.h86ge (Or.inl hpre86)
      rw [hhead, hmvS, show Dir.S.toInt = (0 : ℤ) from rfl]
      omega
  have h20h' : cfg₂.state = 20 → cfg₂.headPos = S.q₄ - 1 :=
    fun h => absurd (hstate.symm.trans h) hne20
  have h5pc' : cfg₂.state = 5 → (cfg₂.tape S.p).1 ≠ SymKind.boundary :=
    fun h => absurd (hstate.symm.trans h) hne5
  exact ⟨{ α := S.α, p := S.p, q₄ := S.q₄, s := S.s, α₀ := S.α₀ },
    ⟨hblk', hC4', hCNM', hα₀', hgap', hαp', hempQ', hB4', h5pos', hA5', hwalk13',
      hSharp', h86le', hαqU', hnext1', hq4ge', hbnd', hpc', h84le', h84le2', h85le', h51p', h20d', h4head', h51q4', h86ge', h20h', h5pc', hinv.hq4e⟩,
    fun hf => by rw [symFive, h86h] at hf; exact absurd hf (by decide)⟩

/-- [C-3] 87 支分派：R 扫到位（\#₀）→ 20 入清扫（20 入口 hB4 建立！）⇒ 包保持。 -/
lemma five_step_87 {inst : SubsetSumInstance} {cfg₀ cfg₂ : SymConfig} {st : SymStep}
    {S : SymFiveSt}
    (hst : SymSteps VerifierSym.transition cfg₀ [st] cfg₂)
    (hleg : cfg₀.state ∈ VerifierSym.legalStates)
    (hno101 : st.result.nextState ≠ 101)
    (h58 : cfg₀.state ∉ symPhaseSet)
    (hinv : SymFiveInv inst cfg₀ S)
    (h87h : st.fromState = 87) :
    ∃ S' : SymFiveSt, SymFiveInv inst cfg₂ S' ∧
      (symFive st = true → S'.p = cfg₀.headPos) := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  have hstate : cfg₂.state = st.result.nextState := by rw [hs_cfg]; rfl
  have hhead : cfg₂.headPos = cfg₀.headPos + st.result.moveDir.toInt := by rw [hs_cfg]; rfl
  have hres : st.result.nextState = 87 ∨ st.result.nextState = 20 :=
    state87_nexts st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h87h hno101
  have hne4 : st.result.nextState ≠ 4 := by intro h; rcases hres with h' | h' <;> omega
  have hne51 : st.result.nextState ≠ 51 := by intro h; rcases hres with h' | h' <;> omega
  have hne21 : st.result.nextState ≠ 21 := by intro h; rcases hres with h' | h' <;> omega
  have hne5 : st.result.nextState ≠ 5 := by intro h; rcases hres with h' | h' <;> omega
  have hne13 : st.result.nextState ≠ 13 := by intro h; rcases hres with h' | h' <;> omega
  have hne84 : st.result.nextState ≠ 84 := by intro h; rcases hres with h' | h' <;> omega
  have hne85 : st.result.nextState ≠ 85 := by intro h; rcases hres with h' | h' <;> omega
  have hne86 : st.result.nextState ≠ 86 := by intro h; rcases hres with h' | h' <;> omega
  have hf2 : st.fromState ≠ 2 := by intro h; omega
  have hf3 : st.fromState ≠ 3 := by intro h; omega
  have hf4 : st.fromState ≠ 4 := by intro h; omega
  have hf5 : st.fromState ≠ 5 := by intro h; omega
  have hf13 : st.fromState ≠ 13 := by intro h; omega
  have hf20 : st.fromState ≠ 20 := by intro h; omega
  have hf21 : st.fromState ≠ 21 := by intro h; omega
  have hf51 : st.fromState ≠ 51 := by intro h; omega
  have hf100 : st.fromState ≠ 100 := by intro h; omega
  have hpre87 : cfg₀.state = 87 := hs_from ▸ h87h
  have hpreW : cfg₀.state ∈ symWorkSet := by rw [hpre87]; decide
  have hpre : cfg₀.state ∈ symMainSet := by rw [hpre87]; decide
  have h86low : cfg₀.headPos ≤ S.q₄ - 1 := hinv.h86le (Or.inr hpre87)
  have hq4 : 2 ≤ S.q₄ := hinv.hq4ge.elim id
    (fun h0 => absurd ((hpre87.symm).trans h0) (by decide))
  have hαple : S.α ≤ S.p := ((hinv.hblk S.p).mp (hinv.hpc hpreW)).1
  have hq4p : S.q₄ + 1 ≤ S.p := by
    have hαq : S.α = S.q₄ + 1 := hinv.hαqU hpre
    omega
  have hblk' : SymBlk cfg₂ S.α S.p :=
    SymBlk.step_of_notFive21 hst hleg hno101 (fun h => hf5 h) (fun h => hf21 h) hinv.hblk
  have hC4' : SymLedger inst cfg₂ S.q₄ :=
    ledger_notTwoFour hst hleg hno101 (fun h => hf2 h) (fun h => hf4 h) hinv.hC4
  have hCNM' : SymClearedGone cfg₂ S.α₀ S.α := SymClearedGone.step_any hst hleg hno101 hinv.hCNM
  have hα₀' : S.α₀ ≤ S.q₄ + 1 := hinv.hα₀
  have hαp' : S.α ≤ S.p + 1 := hinv.hαp
  have hempQ' : (cfg₂.state = 4 ∨ cfg₂.state = 51) → S.α = S.p + 1 := by
    intro h
    rcases h with h | h
    · exact absurd (hstate.symm.trans h) hne4
    · exact absurd (hstate.symm.trans h) hne51
  have hB4' : (cfg₂.state = 20 ∨ cfg₂.state = 21) →
      ∀ z : ℤ, z < cfg₂.headPos → (cfg₂.tape z).1 = SymKind.consumed → False := by
    intro h
    rcases h with h20 | h21
    · intro z hz hc
      have h20r : st.result.nextState = 20 := hstate.symm.trans h20
      have hmvS := (state87_H20 st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h87h h20r).2
      have hheq : cfg₂.headPos = cfg₀.headPos := by
        rw [hhead, hmvS, show Dir.S.toInt = (0 : ℤ) from rfl]; omega
      rw [hheq] at hz
      have hcons1 : (cfg₀.tape z).1 = SymKind.consumed := by
        rw [hs_cfg, symStepConfig_tape_of_ne _ _ (show z ≠ cfg₀.headPos by omega)] at hc
        exact hc
      have hcz := (hinv.hblk z).mp hcons1
      have hαq2 : S.α = S.q₄ + 1 := hinv.hαqU hpre
      omega
    · exact absurd (hstate.symm.trans h21) hne21
  have h5pos' : cfg₂.state = 5 → S.α ≠ S.p + 1 → cfg₂.headPos = S.p + 1 :=
    fun h _ => absurd (hstate.symm.trans h) hne5
  have hA5' : cfg₂.state = 5 → S.p < cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne5
  have hwalk13' : cfg₂.state = 13 →
      SymWalkConsumed cfg₂ S.s ∧ S.s < cfg₂.headPos ∧ S.α ≤ S.s :=
    fun h => absurd (hstate.symm.trans h) hne13
  have h86le' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → cfg₂.headPos ≤ S.q₄ - 1 := by
    intro h
    rcases h with h86 | h87
    · exact absurd (hstate.symm.trans h86) hne86
    · have h87r : st.result.nextState = 87 := hstate.symm.trans h87
      have hmvR := state87_R st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h87h h87r
      have hrd := state8687_R_read st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
        (Or.inr h87h) hno101 hmvR
      have hne' : cfg₀.headPos ≠ S.q₄ - 1 := by
        intro he
        have hb : st.readSym.1 = SymKind.boundary := by
          rw [hs_read, he]
          exact hinv.hSharp hpre
        rcases hrd with hd | hd
        · rw [hd] at hb; exact absurd hb (by decide)
        · rw [hd] at hb; exact absurd hb (by decide)
      have h2 : cfg₀.headPos ≤ S.q₄ - 2 := by omega
      rw [hhead, hmvR, show Dir.R.toInt = (1 : ℤ) from rfl]
      omega
  have hnext1' : cfg₂.state = 5 → S.α = S.p + 1 → cfg₂.headPos = S.q₄ + 1 :=
    fun h _ => absurd (hstate.symm.trans h) hne5
  have hq4ge' : 2 ≤ S.q₄ ∨ cfg₂.state = 4 := Or.inl hq4
  have hbnd' : ∀ z : ℤ, (cfg₂.tape z).1 = SymKind.boundary →
      z = 0 ∨ z = S.q₄ - 1 ∨ z = symEndPos inst ∨ (cfg₂.state = 4 ∧ z = cfg₂.headPos - 1) :=
    hbnd_frame hst hleg hno101 (fun h => hf51 h) (fun h => hf3 h) (fun h => hf20 h)
      (fun h => absurd (h87h.symm.trans (hs_from.trans h)) (by decide)) hinv.hbnd
  have hSharp' : cfg₂.state ∈ symMainSet → (cfg₂.tape (S.q₄ - 1)).1 = SymKind.boundary := by
    intro _
    by_cases hdh : st.readSym.1 = SymKind.boundary
    · by_cases hph : cfg₀.headPos = S.q₄ - 1
      · have hid := hashRead_id st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
          (fun h => hf51 h) (fun h => hf3 h) (fun h => hf20 h) hdh
        rw [← hph, hs_cfg, symStepConfig_tape_headPos]
        exact (congrArg Prod.fst hid).trans hdh
      · rw [hs_cfg, symStepConfig_tape_of_ne _ _ (show S.q₄ - 1 ≠ cfg₀.headPos by omega)]
        exact hinv.hSharp hpre
    · have hph : cfg₀.headPos ≠ S.q₄ - 1 := by
        intro he
        have : st.readSym.1 = SymKind.boundary := by rw [hs_read, he]; exact hinv.hSharp hpre
        exact hdh this
      rw [hs_cfg, symStepConfig_tape_of_ne _ _ (show S.q₄ - 1 ≠ cfg₀.headPos by omega)]
      exact hinv.hSharp hpre
  have hαqU' : cfg₂.state ∈ symMainSet → S.α = S.q₄ + 1 := fun _ => hinv.hαqU hpre
  have hpc' : cfg₂.state ∈ symWorkSet → (cfg₂.tape S.p).1 = SymKind.consumed := by
    intro _
    by_cases hph : cfg₀.headPos = S.p
    · exfalso
      omega
    · rw [hs_cfg, symStepConfig_tape_of_ne _ _ (show S.p ≠ cfg₀.headPos by omega)]
      exact hinv.hpc hpreW
  have h84le' : cfg₂.state = 84 → S.q₄ - 1 ≤ cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne84
  have h84le2' : cfg₂.state = 84 → cfg₂.headPos ≤ S.p :=
    fun h => absurd (hstate.symm.trans h) hne84
  have h85le' : cfg₂.state = 85 → cfg₂.headPos ≤ S.q₄ - 2 :=
    fun h => absurd (hstate.symm.trans h) hne85
  have h51p' : cfg₂.state = 51 → S.p ≤ cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne51
  have hrdnn : ¬(st.readSym.1 = SymKind.sel ∨ st.readSym.1 = SymKind.nosel) :=
    not_markRead_of_states hst hleg hno101 (fun h => hf4 h) (fun h => hf13 h) (fun h => hf21 h)
      (fun h29 => h58 (by rw [← hs_from, h29]; decide)) (fun h => hf100 h)
  have hgap' : SymGapNoAlpha inst S.q₄ cfg₂ := by
    by_cases hmR : st.result.moveDir = Dir.R
    · exact SymGapNoAlpha.step_of_notMarked_read_R hst hleg hrdnn hmR hinv.hgap hinv.hC4
    · have hmv : st.result.moveDir = Dir.R ∨ st.result.moveDir = Dir.S := by
        rcases hres with h' | h'
        · exact Or.inl (state87_R st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h87h h')
        · exact Or.inr ((state87_H20 st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h87h h').2)
      have hmvS : st.result.moveDir = Dir.S := hmv.elim (fun hR => absurd hR hmR) id
      have hle : cfg₂.headPos ≤ cfg₀.headPos := by
        rw [hhead, hmvS, show Dir.S.toInt = (0 : ℤ) from rfl]
        omega
      exact SymGapNoAlpha.step_shrink hst hle hinv.hgap
  have h20d' : (cfg₂.state = 4 ∨ cfg₂.state = 21 ∨ cfg₂.state = 51) →
      (cfg₂.tape (S.q₄ - 1)).1 = SymKind.data0 := by
    intro h
    rcases h with h | h | h
    · exact absurd (hstate.symm.trans h) hne4
    · exact absurd (hstate.symm.trans h) hne21
    · exact absurd (hstate.symm.trans h) hne51
  have h4head' : cfg₂.state = 4 → (cfg₂.tape (cfg₂.headPos - 1)).1 = SymKind.boundary :=
    fun h => absurd (hstate.symm.trans h) hne4
  have h51q4' : cfg₂.state = 51 → S.q₄ ≤ cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne51
  have h86ge' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → 1 ≤ cfg₂.headPos := by
    intro h
    rcases h with h86 | h87
    · exact absurd (hstate.symm.trans h86) hne86
    · have h87r : st.result.nextState = 87 := hstate.symm.trans h87
      have hmvR := state87_R st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h87h h87r
      have hge : 1 ≤ cfg₀.headPos := hinv.h86ge (Or.inr hpre87)
      rw [hhead, hmvR, show Dir.R.toInt = (1 : ℤ) from rfl]
      omega
  have h20h' : cfg₂.state = 20 → cfg₂.headPos = S.q₄ - 1 := by
    intro h20
    have h20r : st.result.nextState = 20 := hstate.symm.trans h20
    have hS20 := state87_H20 st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h87h h20r
    have hle : cfg₀.headPos ≤ S.q₄ - 1 := hinv.h86le (Or.inr hpre87)
    have hge : 1 ≤ cfg₀.headPos := hinv.h86ge (Or.inr hpre87)
    have hrd : (cfg₀.tape cfg₀.headPos).1 = SymKind.boundary := by
      rw [← hs_read]
      exact hS20.1
    have heq : cfg₀.headPos = S.q₄ - 1 := by
      rcases hinv.hbnd cfg₀.headPos hrd with h0' | hq' | hE' | h4e'
      · omega
      · exact hq'
      · exfalso
        have hq4e := hinv.hq4e
        omega
      · have := h4e'.2; omega
    rw [hhead, hS20.2, show Dir.S.toInt = (0 : ℤ) from rfl]
    omega
  have h5pc' : cfg₂.state = 5 → (cfg₂.tape S.p).1 ≠ SymKind.boundary :=
    fun h => absurd (hstate.symm.trans h) hne5
  exact ⟨{ α := S.α, p := S.p, q₄ := S.q₄, s := S.s, α₀ := S.α₀ },
    ⟨hblk', hC4', hCNM', hα₀', hgap', hαp', hempQ', hB4', h5pos', hA5', hwalk13',
      hSharp', h86le', hαqU', hnext1', hq4ge', hbnd', hpc', h84le', h84le2', h85le', h51p', h20d', h4head', h51q4', h86ge', h20h', h5pc', hinv.hq4e⟩,
    fun hf => by rw [symFive, h87h] at hf; exact absurd hf (by decide)⟩
-- ============================================================
-- 接管轮 B1（2026-09-12）：表件 5 个 + 六支本体之 [5]/[13]
-- ============================================================

/-- 表级：5 段 data0 行 ⇒ next = 8。 -/
theorem state5_next0 (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 5 → k = SymKind.data0 → r.nextState = 8 := by
  cases m <;> cases k <;> decide

/-- 表级：5 段 data1 行 ⇒ next = 76。 -/
theorem state5_next1 (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 5 → k = SymKind.data1 → r.nextState = 76 := by
  cases m <;> cases k <;> decide

/-- 表级：13 段 c 续行 ⇒ next = 13。 -/
theorem state13_c_next (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 13 → k = SymKind.consumed → r.nextState = 13 := by
  cases m <;> cases k <;> decide

/-- 表级：81 段读标记（s/n）⇒ 陷阱 101。 -/
theorem state81_mark_trap (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 81 → (k = SymKind.sel ∨ k = SymKind.nosel) → r.nextState = 101 := by
  cases m <;> cases k <;> decide

/-- 表级：21 段续行（仍 21）⇒ 写 d0（c 清行与数据行统一）。 -/
theorem state21_cont_write_d0 (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (q : ℕ) = 21 → r.nextState = 21 → r.writeSym.1 = SymKind.data0 := by
  cases m <;> cases k <;> decide

/-- [C-3] 5 支分派：火步消费（写 c-、块右端 +1、p := 头）⇒ 包保持。 -/
lemma five_step_5 {inst : SubsetSumInstance} {cfg₀ cfg₂ : SymConfig} {st : SymStep}
    {S : SymFiveSt}
    (hst : SymSteps VerifierSym.transition cfg₀ [st] cfg₂)
    (hleg : cfg₀.state ∈ VerifierSym.legalStates)
    (hno101 : st.result.nextState ≠ 101)
    (hinv : SymFiveInv inst cfg₀ S)
    (h5h : st.fromState = 5) :
    ∃ S' : SymFiveSt, SymFiveInv inst cfg₂ S' ∧
      (symFive st = true → S'.p = cfg₀.headPos) := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  have hstate : cfg₂.state = st.result.nextState := by rw [hs_cfg]; rfl
  have hhead : cfg₂.headPos = cfg₀.headPos + st.result.moveDir.toInt := by rw [hs_cfg]; rfl
  have hpre5 : cfg₀.state = 5 := hs_from ▸ h5h
  have hpre : cfg₀.state ∈ symMainSet := by rw [← hs_from, h5h]; decide
  have h5f := state5_readData_writeConsumed st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩
    st.result hm h5h hno101
  have hwr : st.result.writeSym.1 = SymKind.consumed := h5f.2
  have hmvL : st.result.moveDir = Dir.L :=
    state5_move_L st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h5h hno101
  have hres : st.result.nextState = 8 ∨ st.result.nextState = 76 := by
    rcases h5f.1 with h | h
    · exact Or.inl (state5_next0 st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h5h h)
    · exact Or.inr (state5_next1 st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h5h h)
  have hne4 : st.result.nextState ≠ 4 := by intro h; rcases hres with h' | h' <;> omega
  have hne5 : st.result.nextState ≠ 5 := by intro h; rcases hres with h' | h' <;> omega
  have hne13 : st.result.nextState ≠ 13 := by intro h; rcases hres with h' | h' <;> omega
  have hne20 : st.result.nextState ≠ 20 := by intro h; rcases hres with h' | h' <;> omega
  have hne21 : st.result.nextState ≠ 21 := by intro h; rcases hres with h' | h' <;> omega
  have hne51 : st.result.nextState ≠ 51 := by intro h; rcases hres with h' | h' <;> omega
  have hne84 : st.result.nextState ≠ 84 := by intro h; rcases hres with h' | h' <;> omega
  have hne85 : st.result.nextState ≠ 85 := by intro h; rcases hres with h' | h' <;> omega
  have hne86 : st.result.nextState ≠ 86 := by intro h; rcases hres with h' | h' <;> omega
  have hne87 : st.result.nextState ≠ 87 := by intro h; rcases hres with h' | h' <;> omega
  have hf2 : st.fromState ≠ 2 := by intro h; omega
  have hf3 : st.fromState ≠ 3 := by intro h; omega
  have hf4 : st.fromState ≠ 4 := by intro h; omega
  have hf20 : st.fromState ≠ 20 := by intro h; omega
  have hf21 : st.fromState ≠ 21 := by intro h; omega
  have hf51 : st.fromState ≠ 51 := by intro h; omega
  have hq4 : 2 ≤ S.q₄ := hinv.hq4ge.elim id
    (fun h0 => absurd ((hpre5.symm).trans h0) (by decide))
  have hq : cfg₀.headPos = S.p + 1 := by
    by_cases hemp : S.α = S.p + 1
    · have h1 := hinv.hnext1 hpre5 hemp
      have h2 := hinv.hαqU hpre
      omega
    · exact hinv.h5pos hpre5 hemp
  have hblk' : SymBlk cfg₂ S.α (S.p + 1) :=
    SymBlk.fire13_update hst hwr hinv.hαp hinv.hblk hq
  have hC4' : SymLedger inst cfg₂ S.q₄ :=
    ledger_notTwoFour hst hleg hno101 (fun h => hf2 h) (fun h => hf4 h) hinv.hC4
  have hCNM' : SymClearedGone cfg₂ S.α₀ S.α := SymClearedGone.step_any hst hleg hno101 hinv.hCNM
  have hα₀' : S.α₀ ≤ S.q₄ + 1 := hinv.hα₀
  have hgap' : SymGapNoAlpha inst S.q₄ cfg₂ := by
    have hle : cfg₂.headPos ≤ cfg₀.headPos := by
      rw [hhead, hmvL, show Dir.L.toInt = (-1 : ℤ) from rfl]
      omega
    exact SymGapNoAlpha.step_shrink hst hle hinv.hgap
  have hαp' : S.α ≤ S.p + 1 + 1 := by
    have := hinv.hαp
    omega
  have hempQ' : (cfg₂.state = 4 ∨ cfg₂.state = 51) → S.α = S.p + 1 + 1 := by
    intro h
    rcases h with h | h
    · exact absurd (hstate.symm.trans h) hne4
    · exact absurd (hstate.symm.trans h) hne51
  have hB4' : (cfg₂.state = 20 ∨ cfg₂.state = 21) →
      ∀ z : ℤ, z < cfg₂.headPos → (cfg₂.tape z).1 = SymKind.consumed → False := by
    intro h
    rcases h with h | h
    · exact absurd (hstate.symm.trans h) hne20
    · exact absurd (hstate.symm.trans h) hne21
  have h5pos' : cfg₂.state = 5 → S.α ≠ S.p + 1 + 1 → cfg₂.headPos = S.p + 1 + 1 :=
    fun h _ => absurd (hstate.symm.trans h) hne5
  have hA5' : cfg₂.state = 5 → S.p + 1 < cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne5
  have hwalk13' : cfg₂.state = 13 →
      SymWalkConsumed cfg₂ S.s ∧ S.s < cfg₂.headPos ∧ S.α ≤ S.s :=
    fun h => absurd (hstate.symm.trans h) hne13
  have hSharp' : cfg₂.state ∈ symMainSet → (cfg₂.tape (S.q₄ - 1)).1 = SymKind.boundary := by
    intro _
    by_cases hhe : cfg₀.headPos = S.q₄ - 1
    · have hb : st.readSym.1 = SymKind.boundary := by rw [hs_read, hhe]; exact hinv.hSharp hpre
      have hid := hashRead_id st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
        (fun h => hf51 h) (fun h => hf3 h) (fun h => hf20 h) hb
      rw [← hhe, hs_cfg, symStepConfig_tape_headPos]
      exact (congrArg Prod.fst hid).trans hb
    · rw [hs_cfg, symStepConfig_tape_of_ne _ _ (show S.q₄ - 1 ≠ cfg₀.headPos by omega)]
      exact hinv.hSharp hpre
  have h86le' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → cfg₂.headPos ≤ S.q₄ - 1 := by
    intro h
    rcases h with h | h
    · exact absurd (hstate.symm.trans h) hne86
    · exact absurd (hstate.symm.trans h) hne87
  have hαqU' : cfg₂.state ∈ symMainSet → S.α = S.q₄ + 1 := fun _ => hinv.hαqU hpre
  have hnext1' : cfg₂.state = 5 → S.α = S.p + 1 + 1 → cfg₂.headPos = S.q₄ + 1 :=
    fun h _ => absurd (hstate.symm.trans h) hne5
  have hq4ge' : 2 ≤ S.q₄ ∨ cfg₂.state = 4 := Or.inl hq4
  have hbnd' : ∀ z : ℤ, (cfg₂.tape z).1 = SymKind.boundary →
      z = 0 ∨ z = S.q₄ - 1 ∨ z = symEndPos inst ∨ (cfg₂.state = 4 ∧ z = cfg₂.headPos - 1) := by
    intro z hz
    have hz1 : (cfg₀.tape z).1 = SymKind.boundary := by
      by_cases hz0 : z = cfg₀.headPos
      · exfalso
        rw [hz0, hs_cfg, symStepConfig_tape_headPos, hwr] at hz
        exact absurd hz (by decide)
      · rw [hs_cfg, symStepConfig_tape_of_ne _ _ (show z ≠ cfg₀.headPos by omega)] at hz
        exact hz
    rcases hinv.hbnd z hz1 with h0 | hq' | hE | h4e
    · exact Or.inl h0
    · exact Or.inr (Or.inl hq')
    · exact Or.inr (Or.inr (Or.inl hE))
    · exact absurd (h4e.1.symm.trans hpre5) (by decide)
  have hpc' : cfg₂.state ∈ symWorkSet → (cfg₂.tape (S.p + 1)).1 = SymKind.consumed := by
    intro _
    rw [← hq, hs_cfg, symStepConfig_tape_headPos]
    exact hwr
  have h84le' : cfg₂.state = 84 → S.q₄ - 1 ≤ cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne84
  have h84le2' : cfg₂.state = 84 → cfg₂.headPos ≤ S.p + 1 :=
    fun h => absurd (hstate.symm.trans h) hne84
  have h85le' : cfg₂.state = 85 → cfg₂.headPos ≤ S.q₄ - 2 :=
    fun h => absurd (hstate.symm.trans h) hne85
  have h51p' : cfg₂.state = 51 → S.p + 1 ≤ cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne51
  have h20d' : (cfg₂.state = 4 ∨ cfg₂.state = 21 ∨ cfg₂.state = 51) →
      (cfg₂.tape (S.q₄ - 1)).1 = SymKind.data0 := by
    intro h
    rcases h with h | h | h
    · exact absurd (hstate.symm.trans h) hne4
    · exact absurd (hstate.symm.trans h) hne21
    · exact absurd (hstate.symm.trans h) hne51
  have h4head' : cfg₂.state = 4 → (cfg₂.tape (cfg₂.headPos - 1)).1 = SymKind.boundary :=
    fun h => absurd (hstate.symm.trans h) hne4
  have h51q4' : cfg₂.state = 51 → S.q₄ ≤ cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne51
  have h86ge' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → 1 ≤ cfg₂.headPos := by
    intro h
    rcases h with h | h
    · exact absurd (hstate.symm.trans h) hne86
    · exact absurd (hstate.symm.trans h) hne87
  have h20h' : cfg₂.state = 20 → cfg₂.headPos = S.q₄ - 1 :=
    fun h => absurd (hstate.symm.trans h) hne20
  have h5pc' : cfg₂.state = 5 → (cfg₂.tape (S.p + 1)).1 ≠ SymKind.boundary :=
    fun h => absurd (hstate.symm.trans h) hne5
  exact ⟨{ α := S.α, p := S.p + 1, q₄ := S.q₄, s := S.s, α₀ := S.α₀ },
    ⟨hblk', hC4', hCNM', hα₀', hgap', hαp', hempQ', hB4', h5pos', hA5', hwalk13',
      hSharp', h86le', hαqU', hnext1', hq4ge', hbnd', hpc', h84le', h84le2', h85le', h51p', h20d', h4head', h51q4', h86ge', h20h', h5pc', hinv.hq4e⟩,
    fun _ => by show S.p + 1 = cfg₀.headPos; omega⟩

/-- [C-3] 13 支分派：走廊步（c 续 / data 火 / 标记出口）⇒ 包保持。 -/
lemma five_step_13 {inst : SubsetSumInstance} {cfg₀ cfg₂ : SymConfig} {st : SymStep}
    {S : SymFiveSt}
    (hst : SymSteps VerifierSym.transition cfg₀ [st] cfg₂)
    (hleg : cfg₀.state ∈ VerifierSym.legalStates)
    (hno101 : st.result.nextState ≠ 101)
    (hinv : SymFiveInv inst cfg₀ S)
    (h13h : st.fromState = 13) :
    ∃ S' : SymFiveSt, SymFiveInv inst cfg₂ S' ∧
      (symFive st = true → S'.p = cfg₀.headPos) := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  have hstate : cfg₂.state = st.result.nextState := by rw [hs_cfg]; rfl
  have hhead : cfg₂.headPos = cfg₀.headPos + st.result.moveDir.toInt := by rw [hs_cfg]; rfl
  have hpre13 : cfg₀.state = 13 := hs_from ▸ h13h
  have hpre : cfg₀.state ∈ symMainSet := by rw [← hs_from, h13h]; decide
  have hpreW : cfg₀.state ∈ symWorkSet := by rw [← hs_from, h13h]; decide
  have hres : st.result.nextState = 5 ∨ st.result.nextState = 13 ∨ st.result.nextState = 84 := by
    by_cases hd : st.readSym.1 = SymKind.data0 ∨ st.readSym.1 = SymKind.data1
    · exact Or.inl (state13_data_next5 st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
        h13h hd)
    · rcases state13_notData st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
        h13h (fun h => hd (Or.inl h)) (fun h => hd (Or.inr h)) hno101 with h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
  have hne4 : st.result.nextState ≠ 4 := by intro h; rcases hres with h' | h' | h' <;> omega
  have hne20 : st.result.nextState ≠ 20 := by intro h; rcases hres with h' | h' | h' <;> omega
  have hne21 : st.result.nextState ≠ 21 := by intro h; rcases hres with h' | h' | h' <;> omega
  have hne51 : st.result.nextState ≠ 51 := by intro h; rcases hres with h' | h' | h' <;> omega
  have hne85 : st.result.nextState ≠ 85 := by intro h; rcases hres with h' | h' | h' <;> omega
  have hne86 : st.result.nextState ≠ 86 := by intro h; rcases hres with h' | h' | h' <;> omega
  have hne87 : st.result.nextState ≠ 87 := by intro h; rcases hres with h' | h' | h' <;> omega
  have hf2 : st.fromState ≠ 2 := by intro h; omega
  have hf3 : st.fromState ≠ 3 := by intro h; omega
  have hf4 : st.fromState ≠ 4 := by intro h; omega
  have hf5 : st.fromState ≠ 5 := by intro h; omega
  have hf20 : st.fromState ≠ 20 := by intro h; omega
  have hf21 : st.fromState ≠ 21 := by intro h; omega
  have hf51 : st.fromState ≠ 51 := by intro h; omega
  have hq4 : 2 ≤ S.q₄ := hinv.hq4ge.elim id
    (fun h0 => absurd ((hpre13.symm).trans h0) (by decide))
  have fireFacts : st.result.nextState = 5 →
      (cfg₀.headPos = S.p + 1 ∧ cfg₂.headPos = cfg₀.headPos ∧ S.α = S.q₄ + 1) := by
    intro h5r
    have hd : st.readSym.1 = SymKind.data0 ∨ st.readSym.1 = SymKind.data1 := by
      by_contra hnd
      rcases state13_notData st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
        h13h (fun h => hnd (Or.inl h)) (fun h => hnd (Or.inr h)) hno101 with h | h
      · exact absurd h (by omega)
      · exact absurd h (by omega)
    have hpred : (cfg₀.tape (cfg₀.headPos - 1)).1 = SymKind.consumed :=
      SymWalkConsumed.hpred (hinv.hwalk13 hpre13).1 (hinv.hwalk13 hpre13).2.1
    have hrd : (cfg₀.tape cfg₀.headPos).1 = SymKind.data0 ∨
        (cfg₀.tape cfg₀.headPos).1 = SymKind.data1 := by
      rw [← hs_read]; exact hd
    have hq := fire13_pos_core hinv.hblk hpred hrd
    have hmv := state13_data_move st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
      h13h hd
    have hheadS : cfg₂.headPos = cfg₀.headPos := by
      rw [hhead, hmv, show Dir.S.toInt = (0 : ℤ) from rfl]
      omega
    exact ⟨hq, hheadS, hinv.hαqU hpre⟩
  have exitFacts : st.result.nextState = 84 → cfg₀.headPos = S.p + 1 := by
    intro h84r
    have hpred : (cfg₀.tape (cfg₀.headPos - 1)).1 = SymKind.consumed :=
      SymWalkConsumed.hpred (hinv.hwalk13 hpre13).1 (hinv.hwalk13 hpre13).2.1
    have hnc : st.readSym.1 ≠ SymKind.consumed := by
      intro hc
      have hc' : st.result.nextState = 13 :=
        state13_c_next st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h13h hc
      omega
    have hmem := (hinv.hblk (cfg₀.headPos - 1)).mp hpred
    have hm2 : cfg₀.headPos - 1 ≤ S.p := hmem.2
    have hnot : ¬(cfg₀.headPos ≤ S.p) := by
      intro hle
      have hc'' : st.readSym.1 = SymKind.consumed := by
        rw [hs_read]
        exact (hinv.hblk cfg₀.headPos).mpr ⟨by omega, hle⟩
      exact hnc hc''
    omega
  have hblk' : SymBlk cfg₂ S.α S.p :=
    SymBlk.step_of_notFive21 hst hleg hno101 (fun h => hf5 h) (fun h => hf21 h) hinv.hblk
  have hC4' : SymLedger inst cfg₂ S.q₄ :=
    ledger_notTwoFour hst hleg hno101 (fun h => hf2 h) (fun h => hf4 h) hinv.hC4
  have hCNM' : SymClearedGone cfg₂ S.α₀ S.α := SymClearedGone.step_any hst hleg hno101 hinv.hCNM
  have hα₀' : S.α₀ ≤ S.q₄ + 1 := hinv.hα₀
  have hgap' : SymGapNoAlpha inst S.q₄ cfg₂ := by
    rcases hres with h5r | h13r | h84r
    · rcases (fireFacts h5r) with ⟨hq, hheadS, _⟩
      exact SymGapNoAlpha.step_shrink hst (le_of_eq hheadS) hinv.hgap
    · have hcont' := state13_continue st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
        h13h h13r
      have hnm : ¬(st.readSym.1 = SymKind.sel ∨ st.readSym.1 = SymKind.nosel) :=
        fun h => h.elim (fun h1 => absurd (hcont'.1.symm.trans h1) (by decide))
          (fun h2 => absurd (hcont'.1.symm.trans h2) (by decide))
      exact SymGapNoAlpha.step_of_notMarked_read_R hst hleg hnm hcont'.2.2 hinv.hgap hinv.hC4
    · have hmv := state13_exit_move st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
        h13h h84r
      have hle : cfg₂.headPos ≤ cfg₀.headPos := by
        rw [hhead, hmv, show Dir.L.toInt = (-1 : ℤ) from rfl]
        omega
      exact SymGapNoAlpha.step_shrink hst hle hinv.hgap
  have hαp' : S.α ≤ S.p + 1 := hinv.hαp
  have hempQ' : (cfg₂.state = 4 ∨ cfg₂.state = 51) → S.α = S.p + 1 := by
    intro h
    rcases h with h | h
    · exact absurd (hstate.symm.trans h) hne4
    · exact absurd (hstate.symm.trans h) hne51
  have hB4' : (cfg₂.state = 20 ∨ cfg₂.state = 21) →
      ∀ z : ℤ, z < cfg₂.headPos → (cfg₂.tape z).1 = SymKind.consumed → False := by
    intro h
    rcases h with h | h
    · exact absurd (hstate.symm.trans h) hne20
    · exact absurd (hstate.symm.trans h) hne21
  have h5pos' : cfg₂.state = 5 → S.α ≠ S.p + 1 → cfg₂.headPos = S.p + 1 := by
    intro h5 _
    rcases (fireFacts (hstate.symm.trans h5)) with ⟨hq, hheadS, _⟩
    rw [hheadS, hq]
  have hA5' : cfg₂.state = 5 → S.p < cfg₂.headPos := by
    intro h5
    rcases (fireFacts (hstate.symm.trans h5)) with ⟨hq, hheadS, _⟩
    rw [hheadS, hq]
    omega
  have hwalk13' : cfg₂.state = 13 →
      SymWalkConsumed cfg₂ S.s ∧ S.s < cfg₂.headPos ∧ S.α ≤ S.s := by
    intro h13
    rcases hres with h5r | h13r | h84r
    · exact absurd (hstate.symm.trans h13) (by omega)
    · have hcont' := state13_continue st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
        h13h h13r
      have hW' := SymWalkConsumed.step_13_continue hst hleg h13h h13r
        (hinv.hwalk13 hpre13).1
      have hheadR : cfg₂.headPos = cfg₀.headPos + 1 := by
        rw [hhead, hcont'.2.2, show Dir.R.toInt = (1 : ℤ) from rfl]
      have hslt : S.s < cfg₀.headPos := (hinv.hwalk13 hpre13).2.1
      exact ⟨hW', by omega, (hinv.hwalk13 hpre13).2.2⟩
    · exact absurd (hstate.symm.trans h13) (by omega)
  have hSharp' : cfg₂.state ∈ symMainSet → (cfg₂.tape (S.q₄ - 1)).1 = SymKind.boundary := by
    intro _
    by_cases hhe : cfg₀.headPos = S.q₄ - 1
    · have hb : st.readSym.1 = SymKind.boundary := by rw [hs_read, hhe]; exact hinv.hSharp hpre
      have hid := hashRead_id st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
        (fun h => hf51 h) (fun h => hf3 h) (fun h => hf20 h) hb
      rw [← hhe, hs_cfg, symStepConfig_tape_headPos]
      exact (congrArg Prod.fst hid).trans hb
    · rw [hs_cfg, symStepConfig_tape_of_ne _ _ (show S.q₄ - 1 ≠ cfg₀.headPos by omega)]
      exact hinv.hSharp hpre
  have h86le' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → cfg₂.headPos ≤ S.q₄ - 1 := by
    intro h
    rcases h with h | h
    · exact absurd (hstate.symm.trans h) hne86
    · exact absurd (hstate.symm.trans h) hne87
  have hαqU' : cfg₂.state ∈ symMainSet → S.α = S.q₄ + 1 := fun _ => hinv.hαqU hpre
  have hnext1' : cfg₂.state = 5 → S.α = S.p + 1 → cfg₂.headPos = S.q₄ + 1 := by
    intro h5 hαeq
    rcases (fireFacts (hstate.symm.trans h5)) with ⟨hq, hheadS, hαq⟩
    rw [hheadS, hq]
    omega
  have hq4ge' : 2 ≤ S.q₄ ∨ cfg₂.state = 4 := Or.inl hq4
  have hbnd' : ∀ z : ℤ, (cfg₂.tape z).1 = SymKind.boundary →
      z = 0 ∨ z = S.q₄ - 1 ∨ z = symEndPos inst ∨ (cfg₂.state = 4 ∧ z = cfg₂.headPos - 1) :=
    hbnd_frame hst hleg hno101 (fun h => hf51 h) (fun h => hf3 h) (fun h => hf20 h)
      (fun h => absurd (h13h.symm.trans (hs_from.trans h)) (by decide)) hinv.hbnd
  have hpc' : cfg₂.state ∈ symWorkSet → (cfg₂.tape S.p).1 = SymKind.consumed := by
    intro hw'
    rcases hres with h5r | h13r | h84r
    · exact absurd hw' (by rw [hstate, h5r]; decide)
    · by_cases hph : cfg₀.headPos = S.p
      · have hcont' := state13_continue st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
          h13h h13r
        rw [← hph, hs_cfg, symStepConfig_tape_headPos]
        exact hcont'.2.1
      · rw [hs_cfg, symStepConfig_tape_of_ne _ _ (show S.p ≠ cfg₀.headPos by omega)]
        exact hinv.hpc hpreW
    · have hq_eq := exitFacts h84r
      rw [hs_cfg, symStepConfig_tape_of_ne _ _ (show S.p ≠ cfg₀.headPos by omega)]
      exact hinv.hpc hpreW
  have h84le' : cfg₂.state = 84 → S.q₄ - 1 ≤ cfg₂.headPos := by
    intro h8
    rcases hres with h5r | h13r | h84r
    · exact absurd (hstate.symm.trans h8) (by omega)
    · exact absurd (hstate.symm.trans h8) (by omega)
    · have hq_eq := exitFacts h84r
      have hmv := state13_exit_move st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
        h13h h84r
      have hq4p : S.q₄ + 1 ≤ S.p := by
        have hαq := hinv.hαqU hpre
        have hαple : S.α ≤ S.p := ((hinv.hblk S.p).mp (hinv.hpc hpreW)).1
        omega
      rw [hhead, hmv, show Dir.L.toInt = (-1 : ℤ) from rfl]
      omega
  have h84le2' : cfg₂.state = 84 → cfg₂.headPos ≤ S.p := by
    intro h8
    rcases hres with h5r | h13r | h84r
    · exact absurd (hstate.symm.trans h8) (by omega)
    · exact absurd (hstate.symm.trans h8) (by omega)
    · have hq_eq := exitFacts h84r
      have hmv := state13_exit_move st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
        h13h h84r
      rw [hhead, hmv, show Dir.L.toInt = (-1 : ℤ) from rfl]
      omega
  have h85le' : cfg₂.state = 85 → cfg₂.headPos ≤ S.q₄ - 2 :=
    fun h => absurd (hstate.symm.trans h) hne85
  have h51p' : cfg₂.state = 51 → S.p ≤ cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne51
  have h20d' : (cfg₂.state = 4 ∨ cfg₂.state = 21 ∨ cfg₂.state = 51) →
      (cfg₂.tape (S.q₄ - 1)).1 = SymKind.data0 := by
    intro h
    rcases h with h | h | h
    · exact absurd (hstate.symm.trans h) hne4
    · exact absurd (hstate.symm.trans h) hne21
    · exact absurd (hstate.symm.trans h) hne51
  have h4head' : cfg₂.state = 4 → (cfg₂.tape (cfg₂.headPos - 1)).1 = SymKind.boundary :=
    fun h => absurd (hstate.symm.trans h) hne4
  have h51q4' : cfg₂.state = 51 → S.q₄ ≤ cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne51
  have h86ge' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → 1 ≤ cfg₂.headPos := by
    intro h
    rcases h with h | h
    · exact absurd (hstate.symm.trans h) hne86
    · exact absurd (hstate.symm.trans h) hne87
  have h20h' : cfg₂.state = 20 → cfg₂.headPos = S.q₄ - 1 :=
    fun h => absurd (hstate.symm.trans h) hne20
  have h5pc' : cfg₂.state = 5 → (cfg₂.tape S.p).1 ≠ SymKind.boundary := by
    intro h5c
    have h5r : st.result.nextState = 5 := hstate.symm.trans h5c
    rcases (fireFacts h5r) with ⟨hq, _, _⟩
    have hc : (cfg₀.tape (cfg₀.headPos - 1)).1 = SymKind.consumed :=
      SymWalkConsumed.hpred (hinv.hwalk13 hpre13).1 (hinv.hwalk13 hpre13).2.1
    rw [show S.p = cfg₀.headPos - 1 by omega]
    rw [hs_cfg, symStepConfig_tape_of_ne _ _ (show cfg₀.headPos - 1 ≠ cfg₀.headPos by omega)]
    rw [hc]
    decide
  exact ⟨S, ⟨hblk', hC4', hCNM', hα₀', hgap', hαp', hempQ', hB4', h5pos', hA5', hwalk13',
    hSharp', h86le', hαqU', hnext1', hq4ge', hbnd', hpc', h84le', h84le2', h85le', h51p', h20d', h4head', h51q4', h86ge', h20h', h5pc', hinv.hq4e⟩,
    fun hf => by rw [symFive, h13h] at hf; exact absurd hf (by decide)⟩

-- ============================================================
-- 接管轮 B2（2026-09-12）：六支本体之 [81]/[20]/[21]
-- ============================================================

/-- [C-3] 81 支分派：回扫（c 出口建走廊 s := 头 / 非 c 续扫）⇒ 包保持。 -/
lemma five_step_81 {inst : SubsetSumInstance} {cfg₀ cfg₂ : SymConfig} {st : SymStep}
    {S : SymFiveSt}
    (hst : SymSteps VerifierSym.transition cfg₀ [st] cfg₂)
    (hleg : cfg₀.state ∈ VerifierSym.legalStates)
    (hno101 : st.result.nextState ≠ 101)
    (hinv : SymFiveInv inst cfg₀ S)
    (h81h : st.fromState = 81) :
    ∃ S' : SymFiveSt, SymFiveInv inst cfg₂ S' ∧
      (symFive st = true → S'.p = cfg₀.headPos) := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  have hstate : cfg₂.state = st.result.nextState := by rw [hs_cfg]; rfl
  have hhead : cfg₂.headPos = cfg₀.headPos + st.result.moveDir.toInt := by rw [hs_cfg]; rfl
  have hpre81 : cfg₀.state = 81 := hs_from ▸ h81h
  have hpre : cfg₀.state ∈ symMainSet := by rw [← hs_from, h81h]; decide
  have hpreW : cfg₀.state ∈ symWorkSet := by rw [← hs_from, h81h]; decide
  have hres : st.result.nextState = 13 ∨ st.result.nextState = 81 := by
    by_cases hc : st.readSym.1 = SymKind.consumed
    · exact Or.inl (state81_c_exit st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
        h81h hc).1
    · exact Or.inr (state81_notc_cont st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
        h81h hc hno101)
  have hne4 : st.result.nextState ≠ 4 := by intro h; rcases hres with h' | h' <;> omega
  have hne5 : st.result.nextState ≠ 5 := by intro h; rcases hres with h' | h' <;> omega
  have hne20 : st.result.nextState ≠ 20 := by intro h; rcases hres with h' | h' <;> omega
  have hne21 : st.result.nextState ≠ 21 := by intro h; rcases hres with h' | h' <;> omega
  have hne51 : st.result.nextState ≠ 51 := by intro h; rcases hres with h' | h' <;> omega
  have hne84 : st.result.nextState ≠ 84 := by intro h; rcases hres with h' | h' <;> omega
  have hne85 : st.result.nextState ≠ 85 := by intro h; rcases hres with h' | h' <;> omega
  have hne86 : st.result.nextState ≠ 86 := by intro h; rcases hres with h' | h' <;> omega
  have hne87 : st.result.nextState ≠ 87 := by intro h; rcases hres with h' | h' <;> omega
  have hf2 : st.fromState ≠ 2 := by intro h; omega
  have hf3 : st.fromState ≠ 3 := by intro h; omega
  have hf4 : st.fromState ≠ 4 := by intro h; omega
  have hf5 : st.fromState ≠ 5 := by intro h; omega
  have hf20 : st.fromState ≠ 20 := by intro h; omega
  have hf21 : st.fromState ≠ 21 := by intro h; omega
  have hf51 : st.fromState ≠ 51 := by intro h; omega
  have hq4 : 2 ≤ S.q₄ := hinv.hq4ge.elim id
    (fun h0 => absurd ((hpre81.symm).trans h0) (by decide))
  have hcOf : st.result.nextState = 13 → st.readSym.1 = SymKind.consumed := by
    intro h13r
    by_contra hnc
    exact absurd (state81_notc_cont st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
      h81h hnc hno101) (by omega)
  have hncOf : st.result.nextState = 81 → st.readSym.1 ≠ SymKind.consumed := by
    intro h81r hc0
    exact absurd (state81_c_exit st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
      h81h hc0).1 (by omega)
  have hblk' : SymBlk cfg₂ S.α S.p :=
    SymBlk.step_of_notFive21 hst hleg hno101 (fun h => hf5 h) (fun h => hf21 h) hinv.hblk
  have hC4' : SymLedger inst cfg₂ S.q₄ :=
    ledger_notTwoFour hst hleg hno101 (fun h => hf2 h) (fun h => hf4 h) hinv.hC4
  have hCNM' : SymClearedGone cfg₂ S.α₀ S.α := SymClearedGone.step_any hst hleg hno101 hinv.hCNM
  have hα₀' : S.α₀ ≤ S.q₄ + 1 := hinv.hα₀
  have hgap' : SymGapNoAlpha inst S.q₄ cfg₂ := by
    rcases hres with h13r | h81r
    · have hc0 := hcOf h13r
      have hx := state81_c_exit st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h81h hc0
      have hnm : ¬(st.readSym.1 = SymKind.sel ∨ st.readSym.1 = SymKind.nosel) :=
        fun h => h.elim (fun h1 => absurd (hc0.symm.trans h1) (by decide))
          (fun h2 => absurd (hc0.symm.trans h2) (by decide))
      exact SymGapNoAlpha.step_of_notMarked_read_R hst hleg hnm hx.2 hinv.hgap hinv.hC4
    · have hmv := state81_move_R st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
        h81h hno101
      have hnm : ¬(st.readSym.1 = SymKind.sel ∨ st.readSym.1 = SymKind.nosel) :=
        fun hsn => hno101 (state81_mark_trap st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩
          st.result hm h81h hsn)
      exact SymGapNoAlpha.step_of_notMarked_read_R hst hleg hnm hmv hinv.hgap hinv.hC4
  have hαp' : S.α ≤ S.p + 1 := hinv.hαp
  have hempQ' : (cfg₂.state = 4 ∨ cfg₂.state = 51) → S.α = S.p + 1 := by
    intro h
    rcases h with h | h
    · exact absurd (hstate.symm.trans h) hne4
    · exact absurd (hstate.symm.trans h) hne51
  have hB4' : (cfg₂.state = 20 ∨ cfg₂.state = 21) →
      ∀ z : ℤ, z < cfg₂.headPos → (cfg₂.tape z).1 = SymKind.consumed → False := by
    intro h
    rcases h with h | h
    · exact absurd (hstate.symm.trans h) hne20
    · exact absurd (hstate.symm.trans h) hne21
  have h5pos' : cfg₂.state = 5 → S.α ≠ S.p + 1 → cfg₂.headPos = S.p + 1 :=
    fun h _ => absurd (hstate.symm.trans h) hne5
  have hA5' : cfg₂.state = 5 → S.p < cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne5
  have hwalk13' : cfg₂.state = 13 →
      SymWalkConsumed cfg₂ cfg₀.headPos ∧ cfg₀.headPos < cfg₂.headPos ∧ S.α ≤ cfg₀.headPos := by
    intro h13
    rcases hres with h13r | h81r
    · have hc0 := hcOf h13r
      have hx := state81_c_exit st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h81h hc0
      have hW' := SymWalkConsumed.step_81_exit hst hleg h81h hc0
      have hheadR : cfg₂.headPos = cfg₀.headPos + 1 := by
        rw [hhead, hx.2, show Dir.R.toInt = (1 : ℤ) from rfl]
      have hct : (cfg₀.tape cfg₀.headPos).1 = SymKind.consumed := by rw [← hs_read]; exact hc0
      have hαle : S.α ≤ cfg₀.headPos := ((hinv.hblk cfg₀.headPos).mp hct).1
      exact ⟨hW', by omega, hαle⟩
    · exact absurd (hstate.symm.trans h13) (by omega)
  have hSharp' : cfg₂.state ∈ symMainSet → (cfg₂.tape (S.q₄ - 1)).1 = SymKind.boundary := by
    intro _
    by_cases hhe : cfg₀.headPos = S.q₄ - 1
    · have hb : st.readSym.1 = SymKind.boundary := by rw [hs_read, hhe]; exact hinv.hSharp hpre
      have hid := hashRead_id st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
        (fun h => hf51 h) (fun h => hf3 h) (fun h => hf20 h) hb
      rw [← hhe, hs_cfg, symStepConfig_tape_headPos]
      exact (congrArg Prod.fst hid).trans hb
    · rw [hs_cfg, symStepConfig_tape_of_ne _ _ (show S.q₄ - 1 ≠ cfg₀.headPos by omega)]
      exact hinv.hSharp hpre
  have h86le' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → cfg₂.headPos ≤ S.q₄ - 1 := by
    intro h
    rcases h with h | h
    · exact absurd (hstate.symm.trans h) hne86
    · exact absurd (hstate.symm.trans h) hne87
  have hαqU' : cfg₂.state ∈ symMainSet → S.α = S.q₄ + 1 := fun _ => hinv.hαqU hpre
  have hnext1' : cfg₂.state = 5 → S.α = S.p + 1 → cfg₂.headPos = S.q₄ + 1 :=
    fun h _ => absurd (hstate.symm.trans h) hne5
  have hq4ge' : 2 ≤ S.q₄ ∨ cfg₂.state = 4 := Or.inl hq4
  have hbnd' : ∀ z : ℤ, (cfg₂.tape z).1 = SymKind.boundary →
      z = 0 ∨ z = S.q₄ - 1 ∨ z = symEndPos inst ∨ (cfg₂.state = 4 ∧ z = cfg₂.headPos - 1) :=
    hbnd_frame hst hleg hno101 (fun h => hf51 h) (fun h => hf3 h) (fun h => hf20 h)
      (fun h => absurd (h81h.symm.trans (hs_from.trans h)) (by decide)) hinv.hbnd
  have hpc' : cfg₂.state ∈ symWorkSet → (cfg₂.tape S.p).1 = SymKind.consumed := by
    intro hw'
    rcases hres with h13r | h81r
    · have hc0 := hcOf h13r
      have hx := state81_exit st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h81h hc0
      by_cases hph : cfg₀.headPos = S.p
      · rw [← hph, hs_cfg, symStepConfig_tape_headPos]
        exact hx.2.1
      · rw [hs_cfg, symStepConfig_tape_of_ne _ _ (show S.p ≠ cfg₀.headPos by omega)]
        exact hinv.hpc hpreW
    · have hnc0 := hncOf h81r
      by_cases hph : cfg₀.headPos = S.p
      · exfalso
        have hrc : st.readSym.1 = SymKind.consumed := by rw [hs_read, hph]; exact hinv.hpc hpreW
        exact hnc0 hrc
      · rw [hs_cfg, symStepConfig_tape_of_ne _ _ (show S.p ≠ cfg₀.headPos by omega)]
        exact hinv.hpc hpreW
  have h84le' : cfg₂.state = 84 → S.q₄ - 1 ≤ cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne84
  have h84le2' : cfg₂.state = 84 → cfg₂.headPos ≤ S.p :=
    fun h => absurd (hstate.symm.trans h) hne84
  have h85le' : cfg₂.state = 85 → cfg₂.headPos ≤ S.q₄ - 2 :=
    fun h => absurd (hstate.symm.trans h) hne85
  have h51p' : cfg₂.state = 51 → S.p ≤ cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne51
  have h20d' : (cfg₂.state = 4 ∨ cfg₂.state = 21 ∨ cfg₂.state = 51) →
      (cfg₂.tape (S.q₄ - 1)).1 = SymKind.data0 := by
    intro h
    rcases h with h | h | h
    · exact absurd (hstate.symm.trans h) hne4
    · exact absurd (hstate.symm.trans h) hne21
    · exact absurd (hstate.symm.trans h) hne51
  have h4head' : cfg₂.state = 4 → (cfg₂.tape (cfg₂.headPos - 1)).1 = SymKind.boundary :=
    fun h => absurd (hstate.symm.trans h) hne4
  have h51q4' : cfg₂.state = 51 → S.q₄ ≤ cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne51
  have h86ge' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → 1 ≤ cfg₂.headPos := by
    intro h
    rcases h with h | h
    · exact absurd (hstate.symm.trans h) hne86
    · exact absurd (hstate.symm.trans h) hne87
  have h20h' : cfg₂.state = 20 → cfg₂.headPos = S.q₄ - 1 :=
    fun h => absurd (hstate.symm.trans h) hne20
  have h5pc' : cfg₂.state = 5 → (cfg₂.tape S.p).1 ≠ SymKind.boundary :=
    fun h => absurd (hstate.symm.trans h) hne5
  exact ⟨{ α := S.α, p := S.p, q₄ := S.q₄, s := cfg₀.headPos, α₀ := S.α₀ },
    ⟨hblk', hC4', hCNM', hα₀', hgap', hαp', hempQ', hB4', h5pos', hA5', hwalk13',
      hSharp', h86le', hαqU', hnext1', hq4ge', hbnd', hpc', h84le', h84le2', h85le', h51p', h20d', h4head', h51q4', h86ge', h20h', h5pc', hinv.hq4e⟩,
    fun hf => by rw [symFive, h81h] at hf; exact absurd hf (by decide)⟩

/-- [C-3] 20 支分派：占位扩展入口（#₀ → d0 单步）⇒ 包保持。 -/
lemma five_step_20 {inst : SubsetSumInstance} {cfg₀ cfg₂ : SymConfig} {st : SymStep}
    {S : SymFiveSt}
    (hst : SymSteps VerifierSym.transition cfg₀ [st] cfg₂)
    (hleg : cfg₀.state ∈ VerifierSym.legalStates)
    (hno101 : st.result.nextState ≠ 101)
    (hinv : SymFiveInv inst cfg₀ S)
    (h20h : st.fromState = 20) :
    ∃ S' : SymFiveSt, SymFiveInv inst cfg₂ S' ∧
      (symFive st = true → S'.p = cfg₀.headPos) := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  have hstate : cfg₂.state = st.result.nextState := by rw [hs_cfg]; rfl
  have hhead : cfg₂.headPos = cfg₀.headPos + st.result.moveDir.toInt := by rw [hs_cfg]; rfl
  have hpre20 : cfg₀.state = 20 := hs_from ▸ h20h
  have h20f := state20_facts st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h20h hno101
  have hwr : st.result.writeSym.1 = SymKind.data0 := h20f.2.2.1
  have hmvR : st.result.moveDir = Dir.R := h20f.2.2.2
  have h21r : st.result.nextState = 21 := h20f.2.1
  have hh : cfg₀.headPos = S.q₄ - 1 := hinv.h20h hpre20
  have hne4 : st.result.nextState ≠ 4 := by omega
  have hne5 : st.result.nextState ≠ 5 := by omega
  have hne13 : st.result.nextState ≠ 13 := by omega
  have hne20 : st.result.nextState ≠ 20 := by omega
  have hne51 : st.result.nextState ≠ 51 := by omega
  have hne84 : st.result.nextState ≠ 84 := by omega
  have hne85 : st.result.nextState ≠ 85 := by omega
  have hne86 : st.result.nextState ≠ 86 := by omega
  have hne87 : st.result.nextState ≠ 87 := by omega
  have hf2 : st.fromState ≠ 2 := by intro h; omega
  have hf3 : st.fromState ≠ 3 := by intro h; omega
  have hf4 : st.fromState ≠ 4 := by intro h; omega
  have hf5 : st.fromState ≠ 5 := by intro h; omega
  have hf21 : st.fromState ≠ 21 := by intro h; omega
  have hf51 : st.fromState ≠ 51 := by intro h; omega
  have hq4 : 2 ≤ S.q₄ := hinv.hq4ge.elim id
    (fun h0 => absurd ((hpre20.symm).trans h0) (by decide))
  have hblk' : SymBlk cfg₂ S.α S.p :=
    SymBlk.step_of_notFive21 hst hleg hno101 (fun h => hf5 h) (fun h => hf21 h) hinv.hblk
  have hC4' : SymLedger inst cfg₂ S.q₄ :=
    ledger_notTwoFour hst hleg hno101 (fun h => hf2 h) (fun h => hf4 h) hinv.hC4
  have hCNM' : SymClearedGone cfg₂ S.α₀ S.α := SymClearedGone.step_any hst hleg hno101 hinv.hCNM
  have hα₀' : S.α₀ ≤ S.q₄ + 1 := hinv.hα₀
  have hgap' : SymGapNoAlpha inst S.q₄ cfg₂ :=
    SymGapNoAlpha.step_of_notMarked_read_R hst hleg
      (fun h => h.elim (fun h1 => absurd (h20f.1.symm.trans h1) (by decide))
        (fun h2 => absurd (h20f.1.symm.trans h2) (by decide)))
      hmvR hinv.hgap hinv.hC4
  have hαp' : S.α ≤ S.p + 1 := hinv.hαp
  have hempQ' : (cfg₂.state = 4 ∨ cfg₂.state = 51) → S.α = S.p + 1 := by
    intro h
    rcases h with h | h
    · exact absurd (hstate.symm.trans h) hne4
    · exact absurd (hstate.symm.trans h) hne51
  have hB4' : (cfg₂.state = 20 ∨ cfg₂.state = 21) →
      ∀ z : ℤ, z < cfg₂.headPos → (cfg₂.tape z).1 = SymKind.consumed → False := by
    intro _ z hz hc2
    have hh2 : cfg₂.headPos = cfg₀.headPos + 1 := by
      rw [hhead, hmvR, show Dir.R.toInt = (1 : ℤ) from rfl]
    rw [hh2] at hz
    by_cases hz1 : z = cfg₀.headPos
    · rw [hz1, hs_cfg, symStepConfig_tape_headPos, hwr] at hc2
      exact absurd hc2 (by decide)
    · rw [hs_cfg, symStepConfig_tape_of_ne _ _ hz1] at hc2
      exact hinv.hB4 (Or.inl hpre20) z (by omega) hc2
  have h5pos' : cfg₂.state = 5 → S.α ≠ S.p + 1 → cfg₂.headPos = S.p + 1 :=
    fun h _ => absurd (hstate.symm.trans h) hne5
  have hA5' : cfg₂.state = 5 → S.p < cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne5
  have hwalk13' : cfg₂.state = 13 →
      SymWalkConsumed cfg₂ S.s ∧ S.s < cfg₂.headPos ∧ S.α ≤ S.s :=
    fun h => absurd (hstate.symm.trans h) hne13
  have hSharp' : cfg₂.state ∈ symMainSet → (cfg₂.tape (S.q₄ - 1)).1 = SymKind.boundary :=
    fun h => absurd h (by rw [hstate, h21r]; decide)
  have h86le' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → cfg₂.headPos ≤ S.q₄ - 1 := by
    intro h
    rcases h with h | h
    · exact absurd (hstate.symm.trans h) hne86
    · exact absurd (hstate.symm.trans h) hne87
  have hαqU' : cfg₂.state ∈ symMainSet → S.α = S.q₄ + 1 :=
    fun h => absurd h (by rw [hstate, h21r]; decide)
  have hnext1' : cfg₂.state = 5 → S.α = S.p + 1 → cfg₂.headPos = S.q₄ + 1 :=
    fun h _ => absurd (hstate.symm.trans h) hne5
  have hq4ge' : 2 ≤ S.q₄ ∨ cfg₂.state = 4 := Or.inl hq4
  have hbnd' : ∀ z : ℤ, (cfg₂.tape z).1 = SymKind.boundary →
      z = 0 ∨ z = S.q₄ - 1 ∨ z = symEndPos inst ∨ (cfg₂.state = 4 ∧ z = cfg₂.headPos - 1) := by
    intro z hz
    by_cases hz1 : z = cfg₀.headPos
    · rw [hz1, hs_cfg, symStepConfig_tape_headPos, hwr] at hz
      exact absurd hz (by decide)
    · rw [hs_cfg, symStepConfig_tape_of_ne _ _ hz1] at hz
      rcases hinv.hbnd z hz with h0 | hq | hE | h4e
      · exact Or.inl h0
      · exact Or.inr (Or.inl hq)
      · exact Or.inr (Or.inr (Or.inl hE))
      · exact absurd (hs_from.trans h4e.1) hf4
  have hpc' : cfg₂.state ∈ symWorkSet → (cfg₂.tape S.p).1 = SymKind.consumed :=
    fun h => absurd h (by rw [hstate, h21r]; decide)
  have h84le' : cfg₂.state = 84 → S.q₄ - 1 ≤ cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne84
  have h84le2' : cfg₂.state = 84 → cfg₂.headPos ≤ S.p :=
    fun h => absurd (hstate.symm.trans h) hne84
  have h85le' : cfg₂.state = 85 → cfg₂.headPos ≤ S.q₄ - 2 :=
    fun h => absurd (hstate.symm.trans h) hne85
  have h51p' : cfg₂.state = 51 → S.p ≤ cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne51
  have h20d' : (cfg₂.state = 4 ∨ cfg₂.state = 21 ∨ cfg₂.state = 51) →
      (cfg₂.tape (S.q₄ - 1)).1 = SymKind.data0 := by
    intro _
    rw [← hh, hs_cfg, symStepConfig_tape_headPos]
    exact hwr
  have h4head' : cfg₂.state = 4 → (cfg₂.tape (cfg₂.headPos - 1)).1 = SymKind.boundary :=
    fun h => absurd (hstate.symm.trans h) hne4
  have h51q4' : cfg₂.state = 51 → S.q₄ ≤ cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne51
  have h86ge' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → 1 ≤ cfg₂.headPos := by
    intro h
    rcases h with h | h
    · exact absurd (hstate.symm.trans h) hne86
    · exact absurd (hstate.symm.trans h) hne87
  have h20h' : cfg₂.state = 20 → cfg₂.headPos = S.q₄ - 1 :=
    fun h => absurd (hstate.symm.trans h) hne20
  have h5pc' : cfg₂.state = 5 → (cfg₂.tape S.p).1 ≠ SymKind.boundary :=
    fun h => absurd (hstate.symm.trans h) hne5
  exact ⟨S, ⟨hblk', hC4', hCNM', hα₀', hgap', hαp', hempQ', hB4', h5pos', hA5', hwalk13',
    hSharp', h86le', hαqU', hnext1', hq4ge', hbnd', hpc', h84le', h84le2', h85le', h51p', h20d', h4head', h51q4', h86ge', h20h', h5pc', hinv.hq4e⟩,
    fun hf => by rw [symFive, h20h] at hf; exact absurd hf (by decide)⟩

/-- [C-3] 21 支分派：清格扫描（c 清 α+1 / 数据恒等 / 标记停格 / #₁ 段末）⇒ 包保持。 -/
lemma five_step_21 {inst : SubsetSumInstance} {cfg₀ cfg₂ : SymConfig} {st : SymStep}
    {S : SymFiveSt}
    (hst : SymSteps VerifierSym.transition cfg₀ [st] cfg₂)
    (hleg : cfg₀.state ∈ VerifierSym.legalStates)
    (hno101 : st.result.nextState ≠ 101)
    (hinv : SymFiveInv inst cfg₀ S)
    (h21h : st.fromState = 21) :
    ∃ S' : SymFiveSt, SymFiveInv inst cfg₂ S' ∧
      (symFive st = true → S'.p = cfg₀.headPos) := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  have hstate : cfg₂.state = st.result.nextState := by rw [hs_cfg]; rfl
  have hhead : cfg₂.headPos = cfg₀.headPos + st.result.moveDir.toInt := by rw [hs_cfg]; rfl
  have hpre21 : cfg₀.state = 21 := hs_from ▸ h21h
  have hq4 : 2 ≤ S.q₄ := hinv.hq4ge.elim id
    (fun h0 => absurd ((hpre21.symm).trans h0) (by decide))
  have hf2 : st.fromState ≠ 2 := by intro h; omega
  have hf3 : st.fromState ≠ 3 := by intro h; omega
  have hf4 : st.fromState ≠ 4 := by intro h; omega
  have hf5 : st.fromState ≠ 5 := by intro h; omega
  have hf20 : st.fromState ≠ 20 := by intro h; omega
  have hf51 : st.fromState ≠ 51 := by intro h; omega
  have hG4 : ∀ z : ℤ, (cfg₀.tape z).1 = SymKind.consumed → cfg₀.headPos ≤ z :=
    fun z hz => by by_contra hcon; exact hinv.hB4 (Or.inr hpre21) z (by omega) hz
  by_cases hc : st.readSym.1 = SymKind.consumed
  · have hcc := state21_c_clear st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
      h21h hc
    have h21r : st.result.nextState = 21 := hcc.1
    have hwd0 : st.result.writeSym.1 = SymKind.data0 :=
      state21_cont_write_d0 st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
        h21h h21r
    have hne4 : st.result.nextState ≠ 4 := by omega
    have hne5 : st.result.nextState ≠ 5 := by omega
    have hne13 : st.result.nextState ≠ 13 := by omega
    have hne20 : st.result.nextState ≠ 20 := by omega
    have hne51 : st.result.nextState ≠ 51 := by omega
    have hne84 : st.result.nextState ≠ 84 := by omega
    have hne85 : st.result.nextState ≠ 85 := by omega
    have hne86 : st.result.nextState ≠ 86 := by omega
    have hne87 : st.result.nextState ≠ 87 := by omega
    have hct : (cfg₀.tape cfg₀.headPos).1 = SymKind.consumed := by rw [← hs_read]; exact hc
    have hblk' : SymBlk cfg₂ (S.α + 1) S.p :=
      SymBlk.step_21_clear hst hleg hno101 h21h hc hinv.hblk hG4
    have hC4' : SymLedger inst cfg₂ S.q₄ :=
      ledger_notTwoFour hst hleg hno101 (fun h => hf2 h) (fun h => hf4 h) hinv.hC4
    have hCNM' : SymClearedGone cfg₂ S.α₀ (S.α + 1) :=
      SymClearedGone.step_21_clear_ext hst hleg hno101 h21h hc hinv.hblk hG4 hinv.hCNM
    have hα₀' : S.α₀ ≤ S.q₄ + 1 := hinv.hα₀
    have hgap' : SymGapNoAlpha inst S.q₄ cfg₂ :=
      SymGapNoAlpha.step_21_continue hst hleg hno101 h21h h21r hinv.hgap hinv.hC4
    have hαp' : S.α + 1 ≤ S.p + 1 := by
      have hαle : S.α ≤ S.p := by
        have h1 := ((hinv.hblk cfg₀.headPos).mp hct).1
        have h2 := ((hinv.hblk cfg₀.headPos).mp hct).2
        omega
      omega
    have hempQ' : (cfg₂.state = 4 ∨ cfg₂.state = 51) → S.α + 1 = S.p + 1 := by
      intro h
      rcases h with h | h
      · exact absurd (hstate.symm.trans h) hne4
      · exact absurd (hstate.symm.trans h) hne51
    have hB4' : (cfg₂.state = 20 ∨ cfg₂.state = 21) →
        ∀ z : ℤ, z < cfg₂.headPos → (cfg₂.tape z).1 = SymKind.consumed → False := by
      intro _ z hz hc2
      have hh2 : cfg₂.headPos = cfg₀.headPos + 1 := by
        rw [hhead, hcc.2.2, show Dir.R.toInt = (1 : ℤ) from rfl]
      rw [hh2] at hz
      by_cases hz1 : z = cfg₀.headPos
      · rw [hz1, hs_cfg, symStepConfig_tape_headPos, hwd0] at hc2
        exact absurd hc2 (by decide)
      · rw [hs_cfg, symStepConfig_tape_of_ne _ _ hz1] at hc2
        exact hinv.hB4 (Or.inr hpre21) z (by omega) hc2
    have h5pos' : cfg₂.state = 5 → S.α + 1 ≠ S.p + 1 → cfg₂.headPos = S.p + 1 :=
      fun h _ => absurd (hstate.symm.trans h) hne5
    have hA5' : cfg₂.state = 5 → S.p < cfg₂.headPos :=
      fun h => absurd (hstate.symm.trans h) hne5
    have hwalk13' : cfg₂.state = 13 →
        SymWalkConsumed cfg₂ S.s ∧ S.s < cfg₂.headPos ∧ S.α + 1 ≤ S.s :=
      fun h => absurd (hstate.symm.trans h) hne13
    have hSharp' : cfg₂.state ∈ symMainSet → (cfg₂.tape (S.q₄ - 1)).1 = SymKind.boundary :=
      fun h => absurd h (by rw [hstate, h21r]; decide)
    have h86le' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → cfg₂.headPos ≤ S.q₄ - 1 := by
      intro h
      rcases h with h | h
      · exact absurd (hstate.symm.trans h) hne86
      · exact absurd (hstate.symm.trans h) hne87
    have hαqU' : cfg₂.state ∈ symMainSet → S.α + 1 = S.q₄ + 1 :=
      fun h => absurd h (by rw [hstate, h21r]; decide)
    have hnext1' : cfg₂.state = 5 → S.α + 1 = S.p + 1 → cfg₂.headPos = S.q₄ + 1 :=
      fun h _ => absurd (hstate.symm.trans h) hne5
    have hq4ge' : 2 ≤ S.q₄ ∨ cfg₂.state = 4 := Or.inl hq4
    have hbnd' : ∀ z : ℤ, (cfg₂.tape z).1 = SymKind.boundary →
        z = 0 ∨ z = S.q₄ - 1 ∨ z = symEndPos inst ∨ (cfg₂.state = 4 ∧ z = cfg₂.headPos - 1) := by
      intro z hz
      by_cases hz1 : z = cfg₀.headPos
      · rw [hz1, hs_cfg, symStepConfig_tape_headPos, hwd0] at hz
        exact absurd hz (by decide)
      · rw [hs_cfg, symStepConfig_tape_of_ne _ _ hz1] at hz
        rcases hinv.hbnd z hz with h0 | hq | hE | h4e
        · exact Or.inl h0
        · exact Or.inr (Or.inl hq)
        · exact Or.inr (Or.inr (Or.inl hE))
        · exact absurd (hs_from.trans h4e.1) hf4
    have hpc' : cfg₂.state ∈ symWorkSet → (cfg₂.tape S.p).1 = SymKind.consumed :=
      fun h => absurd h (by rw [hstate, h21r]; decide)
    have h84le' : cfg₂.state = 84 → S.q₄ - 1 ≤ cfg₂.headPos :=
      fun h => absurd (hstate.symm.trans h) hne84
    have h84le2' : cfg₂.state = 84 → cfg₂.headPos ≤ S.p :=
      fun h => absurd (hstate.symm.trans h) hne84
    have h85le' : cfg₂.state = 85 → cfg₂.headPos ≤ S.q₄ - 2 :=
      fun h => absurd (hstate.symm.trans h) hne85
    have h51p' : cfg₂.state = 51 → S.p ≤ cfg₂.headPos :=
      fun h => absurd (hstate.symm.trans h) hne51
    have h20d' : (cfg₂.state = 4 ∨ cfg₂.state = 21 ∨ cfg₂.state = 51) →
        (cfg₂.tape (S.q₄ - 1)).1 = SymKind.data0 := by
      intro _
      by_cases hz : S.q₄ - 1 = cfg₀.headPos
      · rw [hz, hs_cfg, symStepConfig_tape_headPos]
        exact hwd0
      · rw [hs_cfg, symStepConfig_tape_of_ne _ _ hz]
        exact hinv.h20d (Or.inr (Or.inl hpre21))
    have h4head' : cfg₂.state = 4 → (cfg₂.tape (cfg₂.headPos - 1)).1 = SymKind.boundary :=
      fun h => absurd (hstate.symm.trans h) hne4
    have h51q4' : cfg₂.state = 51 → S.q₄ ≤ cfg₂.headPos :=
      fun h => absurd (hstate.symm.trans h) hne51
    have h86ge' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → 1 ≤ cfg₂.headPos := by
      intro h
      rcases h with h | h
      · exact absurd (hstate.symm.trans h) hne86
      · exact absurd (hstate.symm.trans h) hne87
    have h20h' : cfg₂.state = 20 → cfg₂.headPos = S.q₄ - 1 :=
      fun h => absurd (hstate.symm.trans h) hne20
    have h5pc' : cfg₂.state = 5 → (cfg₂.tape S.p).1 ≠ SymKind.boundary :=
      fun h => absurd (hstate.symm.trans h) hne5
    exact ⟨{ α := S.α + 1, p := S.p, q₄ := S.q₄, s := S.s, α₀ := S.α₀ },
      ⟨hblk', hC4', hCNM', hα₀', hgap', hαp', hempQ', hB4', h5pos', hA5', hwalk13',
        hSharp', h86le', hαqU', hnext1', hq4ge', hbnd', hpc', h84le', h84le2', h85le', h51p', h20d', h4head', h51q4', h86ge', h20h', h5pc', hinv.hq4e⟩,
      fun hf => by rw [symFive, h21h] at hf; exact absurd hf (by decide)⟩
  · by_cases hmk : st.readSym.1 = SymKind.sel ∨ st.readSym.1 = SymKind.nosel
    · have hstop := state21_stop st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
        h21h hmk
      have h51r : st.result.nextState = 51 := hstop.1
      have hmvL : st.result.moveDir = Dir.L := hstop.2.1
      have hncM : st.readSym.1 ≠ SymKind.consumed :=
        fun hc0 => hmk.elim (fun h1 => absurd (hc0.symm.trans h1) (by decide))
          (fun h2 => absurd (hc0.symm.trans h2) (by decide))
      have hM : SymMarked cfg₀ cfg₀.headPos := by
        rw [SymMarked, ← hs_read]
        exact hmk
      have hq4lt : S.q₄ < cfg₀.headPos := ((hinv.hC4 cfg₀.headPos).mp hM).2
      have hcnm : SymClearedNotMarked cfg₀ S.α₀ S.α := SymClearedGone.to_notMarked hinv.hCNM
      have hstopP : S.p < cfg₀.headPos :=
        SymBlk.stop_gt_p_v2 hst hleg h21h hmk hinv.hblk hinv.hC4 hinv.hα₀ hcnm
      have hαeq : S.α = S.p + 1 := by
        by_cases hemp : S.α ≤ S.p
        · have h1 : cfg₀.headPos ≤ S.α := by
            by_contra hcon
            exact hinv.hB4 (Or.inr hpre21) S.α (by omega)
              ((hinv.hblk S.α).mpr ⟨le_refl _, hemp⟩)
          have h2 : S.α ≤ cfg₀.headPos := by
            by_contra hcon
            have hlt' : cfg₀.headPos < S.α := by omega
            by_cases hge : S.α₀ ≤ cfg₀.headPos
            · exact (SymClearedGone.to_notMarked hinv.hCNM cfg₀.headPos hge hlt') hM
            · have hq' : S.q₄ < cfg₀.headPos := ((hinv.hC4 cfg₀.headPos).mp hM).2
              omega
          omega
        · have hαp1 := hinv.hαp; omega
      have hne4 : st.result.nextState ≠ 4 := by omega
      have hne5 : st.result.nextState ≠ 5 := by omega
      have hne13 : st.result.nextState ≠ 13 := by omega
      have hne20 : st.result.nextState ≠ 20 := by omega
      have hne21 : st.result.nextState ≠ 21 := by omega
      have hne84 : st.result.nextState ≠ 84 := by omega
      have hne85 : st.result.nextState ≠ 85 := by omega
      have hne86 : st.result.nextState ≠ 86 := by omega
      have hne87 : st.result.nextState ≠ 87 := by omega
      have hblk' : SymBlk cfg₂ S.α S.p :=
        SymBlk.step_21_keep hst hleg hno101 h21h hncM hinv.hblk
      have hC4' : SymLedger inst cfg₂ S.q₄ :=
        ledger_notTwoFour hst hleg hno101 (fun h => hf2 h) (fun h => hf4 h) hinv.hC4
      have hCNM' : SymClearedGone cfg₂ S.α₀ S.α := by
        intro z h1 h2
        rw [hs_cfg, symStepConfig_tape_of_ne _ _ (show z ≠ cfg₀.headPos by omega)]
        exact hinv.hCNM z h1 h2
      have hα₀' : S.α₀ ≤ S.q₄ + 1 := hinv.hα₀
      have hgap' : SymGapNoAlpha inst S.q₄ cfg₂ :=
        SymGapNoAlpha.step_21_stop hst hleg hmk h21h hinv.hgap
      have hαp' : S.α ≤ S.p + 1 := hinv.hαp
      have hempQ' : (cfg₂.state = 4 ∨ cfg₂.state = 51) → S.α = S.p + 1 := fun _ => hαeq
      have hB4' : (cfg₂.state = 20 ∨ cfg₂.state = 21) →
          ∀ z : ℤ, z < cfg₂.headPos → (cfg₂.tape z).1 = SymKind.consumed → False := by
        intro h
        rcases h with h | h
        · exact absurd (hstate.symm.trans h) hne20
        · exact absurd (hstate.symm.trans h) hne21
      have h5pos' : cfg₂.state = 5 → S.α ≠ S.p + 1 → cfg₂.headPos = S.p + 1 :=
        fun h _ => absurd (hstate.symm.trans h) hne5
      have hA5' : cfg₂.state = 5 → S.p < cfg₂.headPos :=
        fun h => absurd (hstate.symm.trans h) hne5
      have hwalk13' : cfg₂.state = 13 →
          SymWalkConsumed cfg₂ S.s ∧ S.s < cfg₂.headPos ∧ S.α ≤ S.s :=
        fun h => absurd (hstate.symm.trans h) hne13
      have hSharp' : cfg₂.state ∈ symMainSet → (cfg₂.tape (S.q₄ - 1)).1 = SymKind.boundary :=
        fun h => absurd h (by rw [hstate, h51r]; decide)
      have h86le' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → cfg₂.headPos ≤ S.q₄ - 1 := by
        intro h
        rcases h with h | h
        · exact absurd (hstate.symm.trans h) hne86
        · exact absurd (hstate.symm.trans h) hne87
      have hαqU' : cfg₂.state ∈ symMainSet → S.α = S.q₄ + 1 :=
        fun h => absurd h (by rw [hstate, h51r]; decide)
      have hnext1' : cfg₂.state = 5 → S.α = S.p + 1 → cfg₂.headPos = S.q₄ + 1 :=
        fun h _ => absurd (hstate.symm.trans h) hne5
      have hq4ge' : 2 ≤ S.q₄ ∨ cfg₂.state = 4 := Or.inl hq4
      have hbnd' : ∀ z : ℤ, (cfg₂.tape z).1 = SymKind.boundary →
          z = 0 ∨ z = S.q₄ - 1 ∨ z = symEndPos inst ∨ (cfg₂.state = 4 ∧ z = cfg₂.headPos - 1) := by
        intro z hz
        by_cases hz1 : z = cfg₀.headPos
        · rw [hz1, hs_cfg, symStepConfig_tape_headPos, hstop.2.2] at hz
          rcases hmk with h1 | h1 <;> rw [h1] at hz <;> exact absurd hz (by decide)
        · rw [hs_cfg, symStepConfig_tape_of_ne _ _ hz1] at hz
          rcases hinv.hbnd z hz with h0 | hq | hE | h4e
          · exact Or.inl h0
          · exact Or.inr (Or.inl hq)
          · exact Or.inr (Or.inr (Or.inl hE))
          · exact absurd (hs_from.trans h4e.1) hf4
      have hpc' : cfg₂.state ∈ symWorkSet → (cfg₂.tape S.p).1 = SymKind.consumed :=
        fun h => absurd h (by rw [hstate, h51r]; decide)
      have h84le' : cfg₂.state = 84 → S.q₄ - 1 ≤ cfg₂.headPos :=
        fun h => absurd (hstate.symm.trans h) hne84
      have h84le2' : cfg₂.state = 84 → cfg₂.headPos ≤ S.p :=
        fun h => absurd (hstate.symm.trans h) hne84
      have h85le' : cfg₂.state = 85 → cfg₂.headPos ≤ S.q₄ - 2 :=
        fun h => absurd (hstate.symm.trans h) hne85
      have h51p' : cfg₂.state = 51 → S.p ≤ cfg₂.headPos := by
        have hle : cfg₂.headPos = cfg₀.headPos - 1 := by
          rw [hhead, hmvL, show Dir.L.toInt = (-1 : ℤ) from rfl]
          omega
        intro _
        omega
      have h20d' : (cfg₂.state = 4 ∨ cfg₂.state = 21 ∨ cfg₂.state = 51) →
          (cfg₂.tape (S.q₄ - 1)).1 = SymKind.data0 := by
        intro _
        rw [hs_cfg, symStepConfig_tape_of_ne _ _ (show S.q₄ - 1 ≠ cfg₀.headPos by omega)]
        exact hinv.h20d (Or.inr (Or.inl hpre21))
      have h4head' : cfg₂.state = 4 → (cfg₂.tape (cfg₂.headPos - 1)).1 = SymKind.boundary :=
        fun h => absurd (hstate.symm.trans h) hne4
      have h51q4' : cfg₂.state = 51 → S.q₄ ≤ cfg₂.headPos := by
        have hle : cfg₂.headPos = cfg₀.headPos - 1 := by
          rw [hhead, hmvL, show Dir.L.toInt = (-1 : ℤ) from rfl]
          omega
        intro _
        omega
      have h86ge' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → 1 ≤ cfg₂.headPos := by
        intro h
        rcases h with h | h
        · exact absurd (hstate.symm.trans h) hne86
        · exact absurd (hstate.symm.trans h) hne87
      have h20h' : cfg₂.state = 20 → cfg₂.headPos = S.q₄ - 1 :=
        fun h => absurd (hstate.symm.trans h) hne20
      have h5pc' : cfg₂.state = 5 → (cfg₂.tape S.p).1 ≠ SymKind.boundary :=
        fun h => absurd (hstate.symm.trans h) hne5
      exact ⟨S, ⟨hblk', hC4', hCNM', hα₀', hgap', hαp', hempQ', hB4', h5pos', hA5', hwalk13',
        hSharp', h86le', hαqU', hnext1', hq4ge', hbnd', hpc', h84le', h84le2', h85le', h51p', h20d', h4head', h51q4', h86ge', h20h', h5pc', hinv.hq4e⟩,
        fun hf => by rw [symFive, h21h] at hf; exact absurd hf (by decide)⟩
    · by_cases hbf : st.readSym.1 = SymKind.boundary
      · have hhe2 := state21_hash_end st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
          h21h hbf
        have h22r : st.result.nextState = 22 := hhe2.1
        have hmvS : st.result.moveDir = Dir.S := hhe2.2
        have hid := hashRead_id st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
          (fun h => hf51 h) (fun h => hf3 h) (fun h => hf20 h) hbf
        have hncS : st.readSym.1 ≠ SymKind.consumed := by
          intro hc0
          exact absurd (hc0.symm.trans hbf) (by decide)
        have hne4 : st.result.nextState ≠ 4 := by omega
        have hne5 : st.result.nextState ≠ 5 := by omega
        have hne13 : st.result.nextState ≠ 13 := by omega
        have hne20 : st.result.nextState ≠ 20 := by omega
        have hne21 : st.result.nextState ≠ 21 := by omega
        have hne51 : st.result.nextState ≠ 51 := by omega
        have hne84 : st.result.nextState ≠ 84 := by omega
        have hne85 : st.result.nextState ≠ 85 := by omega
        have hne86 : st.result.nextState ≠ 86 := by omega
        have hne87 : st.result.nextState ≠ 87 := by omega
        have hblk' : SymBlk cfg₂ S.α S.p :=
          SymBlk.step_21_keep hst hleg hno101 h21h hncS hinv.hblk
        have hC4' : SymLedger inst cfg₂ S.q₄ :=
          ledger_notTwoFour hst hleg hno101 (fun h => hf2 h) (fun h => hf4 h) hinv.hC4
        have hCNM' : SymClearedGone cfg₂ S.α₀ S.α := by
          intro z h1 h2
          have hsame : cfg₂.tape z = cfg₀.tape z := by
            by_cases hz0 : z = cfg₀.headPos
            · rw [hz0, hs_cfg, symStepConfig_tape_headPos, hid, ← hs_read]
            · rw [hs_cfg, symStepConfig_tape_of_ne _ _ hz0]
          rw [hsame]
          exact hinv.hCNM z h1 h2
        have hα₀' : S.α₀ ≤ S.q₄ + 1 := hinv.hα₀
        have hgap' : SymGapNoAlpha inst S.q₄ cfg₂ := by
          have hle : cfg₂.headPos ≤ cfg₀.headPos := by
            rw [hhead, hmvS, show Dir.S.toInt = (0 : ℤ) from rfl]
            omega
          exact SymGapNoAlpha.step_shrink hst hle hinv.hgap
        have hαp' : S.α ≤ S.p + 1 := hinv.hαp
        have hempQ' : (cfg₂.state = 4 ∨ cfg₂.state = 51) → S.α = S.p + 1 :=
          fun h => absurd h (by rw [hstate, h22r]; decide)
        have hB4' : (cfg₂.state = 20 ∨ cfg₂.state = 21) →
            ∀ z : ℤ, z < cfg₂.headPos → (cfg₂.tape z).1 = SymKind.consumed → False :=
          fun h => absurd h (by rw [hstate, h22r]; decide)
        have h5pos' : cfg₂.state = 5 → S.α ≠ S.p + 1 → cfg₂.headPos = S.p + 1 :=
          fun h _ => absurd (hstate.symm.trans h) hne5
        have hA5' : cfg₂.state = 5 → S.p < cfg₂.headPos :=
          fun h => absurd (hstate.symm.trans h) hne5
        have hwalk13' : cfg₂.state = 13 →
            SymWalkConsumed cfg₂ S.s ∧ S.s < cfg₂.headPos ∧ S.α ≤ S.s :=
          fun h => absurd (hstate.symm.trans h) hne13
        have hSharp' : cfg₂.state ∈ symMainSet → (cfg₂.tape (S.q₄ - 1)).1 = SymKind.boundary :=
          fun h => absurd h (by rw [hstate, h22r]; decide)
        have h86le' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → cfg₂.headPos ≤ S.q₄ - 1 := by
          intro h
          rcases h with h | h
          · exact absurd (hstate.symm.trans h) hne86
          · exact absurd (hstate.symm.trans h) hne87
        have hαqU' : cfg₂.state ∈ symMainSet → S.α = S.q₄ + 1 :=
          fun h => absurd h (by rw [hstate, h22r]; decide)
        have hnext1' : cfg₂.state = 5 → S.α = S.p + 1 → cfg₂.headPos = S.q₄ + 1 :=
          fun h _ => absurd (hstate.symm.trans h) hne5
        have hq4ge' : 2 ≤ S.q₄ ∨ cfg₂.state = 4 := Or.inl hq4
        have hbnd' : ∀ z : ℤ, (cfg₂.tape z).1 = SymKind.boundary →
            z = 0 ∨ z = S.q₄ - 1 ∨ z = symEndPos inst ∨ (cfg₂.state = 4 ∧ z = cfg₂.headPos - 1) := by
          intro z hz
          by_cases hz1 : z = cfg₀.headPos
          · have hz2 : (st.result.writeSym).1 = SymKind.boundary := by
              rw [hz1, hs_cfg, symStepConfig_tape_headPos] at hz
              exact hz
            have hb1 : (cfg₀.tape cfg₀.headPos).1 = SymKind.boundary := by
              rw [← hs_read]
              exact ((congrArg Prod.fst hid).symm).trans hz2
            rcases hinv.hbnd cfg₀.headPos hb1 with h0 | hq' | hE' | h4e'
            · exact Or.inl (by omega)
            · exact Or.inr (Or.inl (by omega))
            · exact Or.inr (Or.inr (Or.inl (by omega)))
            · have := h4e'.2; omega
          · rw [hs_cfg, symStepConfig_tape_of_ne _ _ hz1] at hz
            rcases hinv.hbnd z hz with h0 | hq | hE | h4e
            · exact Or.inl h0
            · exact Or.inr (Or.inl hq)
            · exact Or.inr (Or.inr (Or.inl hE))
            · exact absurd (hs_from.trans h4e.1) hf4
        have hpc' : cfg₂.state ∈ symWorkSet → (cfg₂.tape S.p).1 = SymKind.consumed :=
          fun h => absurd h (by rw [hstate, h22r]; decide)
        have h84le' : cfg₂.state = 84 → S.q₄ - 1 ≤ cfg₂.headPos :=
          fun h => absurd (hstate.symm.trans h) hne84
        have h84le2' : cfg₂.state = 84 → cfg₂.headPos ≤ S.p :=
          fun h => absurd (hstate.symm.trans h) hne84
        have h85le' : cfg₂.state = 85 → cfg₂.headPos ≤ S.q₄ - 2 :=
          fun h => absurd (hstate.symm.trans h) hne85
        have h51p' : cfg₂.state = 51 → S.p ≤ cfg₂.headPos :=
          fun h => absurd (hstate.symm.trans h) hne51
        have h20d' : (cfg₂.state = 4 ∨ cfg₂.state = 21 ∨ cfg₂.state = 51) →
            (cfg₂.tape (S.q₄ - 1)).1 = SymKind.data0 :=
          fun h => absurd h (by rw [hstate, h22r]; decide)
        have h4head' : cfg₂.state = 4 → (cfg₂.tape (cfg₂.headPos - 1)).1 = SymKind.boundary :=
          fun h => absurd (hstate.symm.trans h) hne4
        have h51q4' : cfg₂.state = 51 → S.q₄ ≤ cfg₂.headPos :=
          fun h => absurd (hstate.symm.trans h) hne51
        have h86ge' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → 1 ≤ cfg₂.headPos := by
          intro h
          rcases h with h | h
          · exact absurd (hstate.symm.trans h) hne86
          · exact absurd (hstate.symm.trans h) hne87
        have h20h' : cfg₂.state = 20 → cfg₂.headPos = S.q₄ - 1 :=
          fun h => absurd (hstate.symm.trans h) hne20
        have h5pc' : cfg₂.state = 5 → (cfg₂.tape S.p).1 ≠ SymKind.boundary :=
          fun h => absurd (hstate.symm.trans h) hne5
        exact ⟨S, ⟨hblk', hC4', hCNM', hα₀', hgap', hαp', hempQ', hB4', h5pos', hA5', hwalk13',
          hSharp', h86le', hαqU', hnext1', hq4ge', hbnd', hpc', h84le', h84le2', h85le', h51p', h20d', h4head', h51q4', h86ge', h20h', h5pc', hinv.hq4e⟩,
          fun hf => by rw [symFive, h21h] at hf; exact absurd hf (by decide)⟩
      · have h21r : st.result.nextState = 21 :=
          state21_d_cont st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
            h21h hc (fun h => hmk (Or.inl h)) (fun h => hmk (Or.inr h)) hbf hno101
        have hwd0 : st.result.writeSym.1 = SymKind.data0 :=
          state21_cont_write_d0 st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
            h21h h21r
        have hmvR : st.result.moveDir = Dir.R :=
          (state21_continue st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
            h21h h21r).1
        have hne4 : st.result.nextState ≠ 4 := by omega
        have hne5 : st.result.nextState ≠ 5 := by omega
        have hne13 : st.result.nextState ≠ 13 := by omega
        have hne20 : st.result.nextState ≠ 20 := by omega
        have hne51 : st.result.nextState ≠ 51 := by omega
        have hne84 : st.result.nextState ≠ 84 := by omega
        have hne85 : st.result.nextState ≠ 85 := by omega
        have hne86 : st.result.nextState ≠ 86 := by omega
        have hne87 : st.result.nextState ≠ 87 := by omega
        have hblk' : SymBlk cfg₂ S.α S.p :=
          SymBlk.step_21_keep hst hleg hno101 h21h hc hinv.hblk
        have hC4' : SymLedger inst cfg₂ S.q₄ :=
          ledger_notTwoFour hst hleg hno101 (fun h => hf2 h) (fun h => hf4 h) hinv.hC4
        have hCNM' : SymClearedGone cfg₂ S.α₀ S.α := by
          intro z h1 h2
          by_cases hz0 : z = cfg₀.headPos
          · rw [Sym.notMarked, hz0, hs_cfg, symStepConfig_tape_headPos, hwd0]
            exact ⟨by decide, by decide, by decide⟩
          · rw [hs_cfg, symStepConfig_tape_of_ne _ _ hz0]
            exact hinv.hCNM z h1 h2
        have hα₀' : S.α₀ ≤ S.q₄ + 1 := hinv.hα₀
        have hgap' : SymGapNoAlpha inst S.q₄ cfg₂ :=
          SymGapNoAlpha.step_21_continue hst hleg hno101 h21h h21r hinv.hgap hinv.hC4
        have hαp' : S.α ≤ S.p + 1 := hinv.hαp
        have hempQ' : (cfg₂.state = 4 ∨ cfg₂.state = 51) → S.α = S.p + 1 := by
          intro h
          rcases h with h | h
          · exact absurd (hstate.symm.trans h) hne4
          · exact absurd (hstate.symm.trans h) hne51
        have hB4' : (cfg₂.state = 20 ∨ cfg₂.state = 21) →
            ∀ z : ℤ, z < cfg₂.headPos → (cfg₂.tape z).1 = SymKind.consumed → False := by
          intro _ z hz hc2
          have hh2 : cfg₂.headPos = cfg₀.headPos + 1 := by
            rw [hhead, hmvR, show Dir.R.toInt = (1 : ℤ) from rfl]
          rw [hh2] at hz
          by_cases hz1 : z = cfg₀.headPos
          · rw [hz1, hs_cfg, symStepConfig_tape_headPos, hwd0] at hc2
            exact absurd hc2 (by decide)
          · rw [hs_cfg, symStepConfig_tape_of_ne _ _ hz1] at hc2
            exact hinv.hB4 (Or.inr hpre21) z (by omega) hc2
        have h5pos' : cfg₂.state = 5 → S.α ≠ S.p + 1 → cfg₂.headPos = S.p + 1 :=
          fun h _ => absurd (hstate.symm.trans h) hne5
        have hA5' : cfg₂.state = 5 → S.p < cfg₂.headPos :=
          fun h => absurd (hstate.symm.trans h) hne5
        have hwalk13' : cfg₂.state = 13 →
            SymWalkConsumed cfg₂ S.s ∧ S.s < cfg₂.headPos ∧ S.α ≤ S.s :=
          fun h => absurd (hstate.symm.trans h) hne13
        have hSharp' : cfg₂.state ∈ symMainSet → (cfg₂.tape (S.q₄ - 1)).1 = SymKind.boundary :=
          fun h => absurd h (by rw [hstate, h21r]; decide)
        have h86le' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → cfg₂.headPos ≤ S.q₄ - 1 := by
          intro h
          rcases h with h | h
          · exact absurd (hstate.symm.trans h) hne86
          · exact absurd (hstate.symm.trans h) hne87
        have hαqU' : cfg₂.state ∈ symMainSet → S.α = S.q₄ + 1 :=
          fun h => absurd h (by rw [hstate, h21r]; decide)
        have hnext1' : cfg₂.state = 5 → S.α = S.p + 1 → cfg₂.headPos = S.q₄ + 1 :=
          fun h _ => absurd (hstate.symm.trans h) hne5
        have hq4ge' : 2 ≤ S.q₄ ∨ cfg₂.state = 4 := Or.inl hq4
        have hbnd' : ∀ z : ℤ, (cfg₂.tape z).1 = SymKind.boundary →
            z = 0 ∨ z = S.q₄ - 1 ∨ z = symEndPos inst ∨ (cfg₂.state = 4 ∧ z = cfg₂.headPos - 1) := by
          intro z hz
          by_cases hz1 : z = cfg₀.headPos
          · rw [hz1, hs_cfg, symStepConfig_tape_headPos, hwd0] at hz
            exact absurd hz (by decide)
          · rw [hs_cfg, symStepConfig_tape_of_ne _ _ hz1] at hz
            rcases hinv.hbnd z hz with h0 | hq | hE | h4e
            · exact Or.inl h0
            · exact Or.inr (Or.inl hq)
            · exact Or.inr (Or.inr (Or.inl hE))
            · exact absurd (hs_from.trans h4e.1) hf4
        have hpc' : cfg₂.state ∈ symWorkSet → (cfg₂.tape S.p).1 = SymKind.consumed :=
          fun h => absurd h (by rw [hstate, h21r]; decide)
        have h84le' : cfg₂.state = 84 → S.q₄ - 1 ≤ cfg₂.headPos :=
          fun h => absurd (hstate.symm.trans h) hne84
        have h84le2' : cfg₂.state = 84 → cfg₂.headPos ≤ S.p :=
          fun h => absurd (hstate.symm.trans h) hne84
        have h85le' : cfg₂.state = 85 → cfg₂.headPos ≤ S.q₄ - 2 :=
          fun h => absurd (hstate.symm.trans h) hne85
        have h51p' : cfg₂.state = 51 → S.p ≤ cfg₂.headPos :=
          fun h => absurd (hstate.symm.trans h) hne51
        have h20d' : (cfg₂.state = 4 ∨ cfg₂.state = 21 ∨ cfg₂.state = 51) →
            (cfg₂.tape (S.q₄ - 1)).1 = SymKind.data0 := by
          intro _
          by_cases hz : S.q₄ - 1 = cfg₀.headPos
          · rw [hz, hs_cfg, symStepConfig_tape_headPos]
            exact hwd0
          · rw [hs_cfg, symStepConfig_tape_of_ne _ _ hz]
            exact hinv.h20d (Or.inr (Or.inl hpre21))
        have h4head' : cfg₂.state = 4 → (cfg₂.tape (cfg₂.headPos - 1)).1 = SymKind.boundary :=
          fun h => absurd (hstate.symm.trans h) hne4
        have h51q4' : cfg₂.state = 51 → S.q₄ ≤ cfg₂.headPos :=
          fun h => absurd (hstate.symm.trans h) hne51
        have h86ge' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → 1 ≤ cfg₂.headPos := by
          intro h
          rcases h with h | h
          · exact absurd (hstate.symm.trans h) hne86
          · exact absurd (hstate.symm.trans h) hne87
        have h20h' : cfg₂.state = 20 → cfg₂.headPos = S.q₄ - 1 :=
          fun h => absurd (hstate.symm.trans h) hne20
        have h5pc' : cfg₂.state = 5 → (cfg₂.tape S.p).1 ≠ SymKind.boundary :=
          fun h => absurd (hstate.symm.trans h) hne5
        exact ⟨S, ⟨hblk', hC4', hCNM', hα₀', hgap', hαp', hempQ', hB4', h5pos', hA5', hwalk13',
          hSharp', h86le', hαqU', hnext1', hq4ge', hbnd', hpc', h84le', h84le2', h85le', h51p', h20d', h4head', h51q4', h86ge', h20h', h5pc', hinv.hq4e⟩,
          fun hf => by rw [symFive, h21h] at hf; exact absurd hf (by decide)⟩

theorem no_special_entry (k : SymKind) (m : Bool) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), (k, m)),
      (r.nextState = 4 ∨ r.nextState = 5 ∨ r.nextState = 13 ∨ r.nextState = 20 ∨
        r.nextState = 21 ∨ r.nextState = 51) →
      ((q : ℕ) = 4 ∨ (q : ℕ) = 5 ∨ (q : ℕ) = 13 ∨ (q : ℕ) = 20 ∨ (q : ℕ) = 21 ∨
        (q : ℕ) = 28 ∨ (q : ℕ) = 51 ∨ (q : ℕ) = 81 ∨ (q : ℕ) = 87) := by
  cases m <;> cases k <;> decide

-- ============================================================
-- 计数件（nodup 作显式假设；待 Part B 消解）
-- ============================================================

/-- [C-3] 5-步位置互异 + 窗口内 ⇒ #5-步 ≤ 窗口宽度（镜像 c-8D）。 -/
lemma five_count_le_window {cfg₀ cfg : SymConfig} {π : List SymStep} {lo hi : ℤ}
    (hnodup : (fivePositions cfg₀.headPos π).Nodup)
    (hpos : ∀ p ∈ fivePositions cfg₀.headPos π, lo ≤ p ∧ p ≤ hi) :
    (π.filter symFive).length ≤ (hi - lo + 1).toNat := by
  have hcard : (fivePositions cfg₀.headPos π).toFinset.card
      = (fivePositions cfg₀.headPos π).length :=
    List.toFinset_card_of_nodup hnodup
  have hsub : (fivePositions cfg₀.headPos π).toFinset ⊆ Finset.Icc lo hi := by
    intro p hp
    rw [List.mem_toFinset] at hp
    exact Finset.mem_Icc.mpr (hpos p hp)
  calc (π.filter symFive).length
      = (fivePositions cfg₀.headPos π).length := (fivePositions_length cfg₀.headPos π).symm
    _ = (fivePositions cfg₀.headPos π).toFinset.card := hcard.symm
    _ ≤ (Finset.Icc lo hi).card := Finset.card_le_card hsub
    _ = (hi - lo + 1).toNat := by rw [Int.card_Icc]; congr 1; ring

-- ===== δ-19-15c-16 END =====

end Mp
-- ===== δ-19-15c-14 END =====
