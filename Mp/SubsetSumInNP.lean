/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import Mp.ClassicalFramework
import Mp.SubsetSumReal
import Mp.SubsetSumCompile
import Mp.SubsetSumVerifierReverse3
import Mp.SubsetSumVerifierReverse8
import Mp.SubsetSumVerifierT16
import Mp.SubsetSumVerifierQ10
import Mp.A2Bridge

/-!
# 子集和 ∈ NP_F（**A1 公理已清除**，位置模型 V6，2026-09-13 主线 M2/M3）

- 原主公理 `exists_NTM2_solves_subsetSum`（存在一台规范 NTM2 求解子集和）已**删除**。
- 全部消费点重写为对具体机器 `subsetSumNTM2` 的定理簇：
  - ① 求解：`subsetSumNTM2_solves_of_canonical`（正实例，接受 ⟺ holds）
  - ② 语言桥：`subsetSumNTM2_input_bridge`（ntm2InputToCBTM = 恒等）
  - ③ 规范：`subsetSumNTM2_canonical : NTM2.Canonical subsetSumNTM2`（Q10；
    条款 (a)=A-2 成品+镜像、条款 (b)=Reverse11、条款 (c)=**A3 欠条**，兄弟线还债后定理化）
  - ④ 非编码拒绝：`subsetSumNTM2_hrel` / `subsetSumNTM2_rejects_nonencoding`
    （域 = IsSymbolAligned）
  - ⑤ 尾缀无关：`subsetSumNTM2_hrel2`（T16）
- 同构桥 `StructIso_preserves_accepts` 是 **theorem**（A2 消除，Mp.A2Bridge）。
- `toCBTM_polynomialTime`：toCBTM A 是多项式时间的（canonical → 二次界），
  真实定义（IsPolynomialBound + 接受路径长度 ≤ p(输入长度)）。
- `subsetSum_in_NP_F` 由定理簇组装（theorem），供 FinalProof 使用。

-/
namespace Mp

open CBTM
open IVM
open SymToF4

/-- 实例 → F4 串编码（与语言 L 一致：encodeInstanceF4 inst）。 -/
def encodeInstBits (inst : SubsetSumInstance) : List F4 :=
  encodeInstanceF4 inst

/-- NTM2 路径的分叉计数：路径中读标记符号（虚部 = true，即 α/β）的步数。 -/
def ntm2ForkCount (_A : NTM2) (π : NTM2ComputationPath) : ℕ :=
  (π.filter (fun step => F4.im step.readSym = true)).length

/-- 条款 2（语言桥）定理化：ntm2InputToCBTM = 恒等 + encodeInstBits = encodeInstanceF4
    → 定义级相等。 -/
theorem subsetSumNTM2_input_bridge (inst : SubsetSumInstance) (_hne : inst.elements ≠ []) :
    ntm2InputToCBTM subsetSumNTM2 (encodeInstBits inst) = encodeInstanceF4 inst := by
  rfl

/-- 条款 1（求解）定理化（正实例 + 给定 Canonical）：子集和成立 ⟺ subsetSumNTM2 接受编码。
    链：holds ↔ symAccepts（symVerifier_correct）↔ subsetSumCBTM 接受（编译桥）
    ↔ (toCBTM subsetSumNTM2) 接受（toCBTM_subsetSumNTM2_eq）↔ acceptsTape（同构桥，hcan）。
    装配时 hcan 由条款 3 提供；正性由条款 4（接受 ⟹ 合法编码）提供。 -/
theorem subsetSumNTM2_solves_of_canonical (hcan : NTM2.Canonical subsetSumNTM2)
    (inst : SubsetSumInstance) (hne : inst.elements ≠ [])
    (hpos : ∀ v ∈ inst.elements, 0 < v) (htarget : 0 < inst.target) :
    subsetSumHolds inst ↔ subsetSumNTM2.acceptsTape (encodeInstBits inst) := by
  rcases exists_CBTM_iso_NTM2 subsetSumNTM2 with ⟨M, hM, ⟨iso⟩⟩
  subst M
  have hiso : (NTM2.toCBTM subsetSumNTM2) = subsetSumCBTM := toCBTM_subsetSumNTM2_eq
  constructor
  · -- 完备性：holds → acceptsTape
    intro hholds
    have hsym : symAccepts VerifierSym.transition VerifierSym.acceptStates
        (encodeInstanceSym inst) :=
      (symVerifier_correct inst hne hpos htarget).2 hholds
    have hcbtm : subsetSumCBTM.tapeAccepts (flat4F4 (encodeInstanceSym inst)) :=
      (subsetSumCBTM_accepts_iff_symAccepts (encodeInstanceSym inst)).2 hsym
    have hcbtm' : (NTM2.toCBTM subsetSumNTM2).tapeAccepts (encodeInstBits inst) := by
      simpa [hiso, encodeInstBits, encodeInstanceF4, flat4F4] using hcbtm
    exact (StructIso_preserves_accepts subsetSumNTM2 (NTM2.toCBTM subsetSumNTM2) iso hcan
      (encodeInstBits inst) (by
        refine ⟨inst, ([] : List Sym), ?_⟩
        simp [encodeInstBits, encodeInstanceF4, flat4F4])).2 hcbtm'
  · -- 可靠性：acceptsTape → holds
    intro hacc
    have hcbtm' : (NTM2.toCBTM subsetSumNTM2).tapeAccepts (encodeInstBits inst) :=
      (StructIso_preserves_accepts subsetSumNTM2 (NTM2.toCBTM subsetSumNTM2) iso hcan
        (encodeInstBits inst) (by
          refine ⟨inst, ([] : List Sym), ?_⟩
          simp [encodeInstBits, encodeInstanceF4, flat4F4])).1 hacc
    have hcbtm : subsetSumCBTM.tapeAccepts (flat4F4 (encodeInstanceSym inst)) := by
      simpa [hiso, encodeInstBits, encodeInstanceF4, flat4F4] using hcbtm'
    have hsym : symAccepts VerifierSym.transition VerifierSym.acceptStates
        (encodeInstanceSym inst) :=
      (subsetSumCBTM_accepts_iff_symAccepts (encodeInstanceSym inst)).1 hcbtm
    exact (symVerifier_correct inst hne hpos htarget).1 hsym

/-- 条款 4 的推论：toCBTM A 对非编码的符号对齐串拒绝（2026-09-09 用户裁决：\n    hrel 域 = IsSymbolAligned——语言判定域 = 符号对齐串，半块/非法 padding 串不在定义域内）。 -/
lemma toCBTM_rejects_nonencoding (A : NTM2)
    (hrel : ∀ M : CBTM, Nonempty (StructIsoNTM2CBTM A M) →
      ∀ w : List F4, IsSymbolAligned w → M.tapeAccepts w →
        ∃ inst : SubsetSumInstance, ∃ gS : List Sym, w = encodeInstanceF4 inst ++ flat4F4 gS ∧
          inst.elements ≠ [] ∧
          (∀ v ∈ inst.elements, 0 < v) ∧ 0 < inst.target) :
    ∀ w : List F4, IsSymbolAligned w →
      (∀ inst : SubsetSumInstance, inst.elements ≠ [] →
        ∀ gS : List Sym, w ≠ encodeInstanceF4 inst ++ flat4F4 gS) →
      ¬ (NTM2.toCBTM A).tapeAccepts w := by
  intro w hal hnon hacc
  rcases exists_CBTM_iso_NTM2 A with ⟨M, hM, ⟨iso⟩⟩
  subst M
  rcases hrel (NTM2.toCBTM A) ⟨iso⟩ w hal hacc with ⟨inst, gS, hw, hne, _hpos, _htarget⟩
  exact hnon inst hne gS hw

/-- 条款 4 对 subsetSumNTM2 的实例化（hrel 素材 = iso_accepts_implies_encoding，
    Reverse8 域内条款 4 已定理化）：任意与 subsetSumNTM2 同构的 CBTM，对符号对齐输入
    （4F4 计算符号串 = flat4F4 像，2026-09-09 输入层裁决）接受
    ⟹ 输入 = 某非空正实例编码 ++ flat4F4 gS。 -/
lemma subsetSumNTM2_hrel : ∀ M : CBTM, Nonempty (StructIsoNTM2CBTM subsetSumNTM2 M) →
    ∀ w : List F4, IsSymbolAligned w → M.tapeAccepts w →
      ∃ inst : SubsetSumInstance, ∃ gS : List Sym, w = encodeInstanceF4 inst ++ flat4F4 gS ∧
        inst.elements ≠ [] ∧ (∀ v ∈ inst.elements, 0 < v) ∧ 0 < inst.target := by
  intro M hnon w hal hacc
  rcases hnon with ⟨iso⟩
  exact iso_accepts_implies_encoding M iso w (by simpa [IsSymbolAligned] using hal) hacc

/-- T16 第一件：非编码拒绝实例化——toCBTM subsetSumNTM2 对非编码的符号对齐串拒绝
    （toCBTM_rejects_nonencoding 喂 subsetSumNTM2 版 hrel；输入域 = IsSymbolAligned，
    非 4F4 像的 F4 串不是这台机器的输入，不在断言域内）。 -/
lemma subsetSumNTM2_rejects_nonencoding : ∀ w : List F4, IsSymbolAligned w →
    (∀ inst : SubsetSumInstance, inst.elements ≠ [] →
      ∀ gS : List Sym, w ≠ encodeInstanceF4 inst ++ flat4F4 gS) →
    ¬ (NTM2.toCBTM subsetSumNTM2).tapeAccepts w :=
  toCBTM_rejects_nonencoding subsetSumNTM2 subsetSumNTM2_hrel

/-- 规范 NTM2 的路径分叉步数 ≤ 输入长度+1：分叉格（im = true）的**位置互异**
    （条款②新口径「前缀不占同位」，Spec V1.47），位置在 [0, |x|] 内（条款①闭区间）
    → 互异位置数 ≤ |x|+1。 -/
lemma forkCount_le_input_length (A : NTM2) (x : List F4) (π : NTM2ComputationPath)
    (cfg : NTM2Config A x) (hcan : NTM2.Canonical A)
    (hwf : ∃ inst : SubsetSumInstance, ∃ gS : List Sym,
      x = SymToF4.encodeInstanceF4 inst ++ SymToF4.flat4F4 gS)
    (hnoTerm : ∀ step ∈ π, step.fromState ∉ A.acceptStates)
    (hr : TapeReachablePathNTM2 A x π cfg)
    (hext : ∃ (π₂ : NTM2ComputationPath) (cfg₂ : NTM2Config A x),
        TapeReachablePathNTM2 A x (π ++ π₂) cfg₂ ∧ cfg₂.state ∈ A.acceptStates) :
    (π.filter (fun step => F4.im step.readSym = true)).length ≤ x.length + 1 := by
  rcases hcan with ⟨K, hK⟩
  -- 分叉步的位置列表：互异（条款②）+ 非负且在输入区内（条款①）
  have hnodup : ((π.filter (fun step => F4.im step.readSym = true)).map (fun step => step.pos)).Nodup := by
    induction hr with
    | nil => simp
    | cons π₀ step cfg₀ hrc hfrom hread hpos htrans ih =>
        -- 归纳：尾部位置列表互异 + step.pos ∉ 尾部位置集（若 step 分叉）
        have hno₀ : ∀ s ∈ π₀, s.fromState ∉ A.acceptStates := by
          intro s hs
          exact hnoTerm s (by simp [hs])
        have hnoStep : step.fromState ∉ A.acceptStates := hnoTerm step (by simp)
        rcases hext with ⟨π₂, cfg₂, hpath₂, hacc₂⟩
        -- π₀ 可延拓:π₀ ++ (step :: π₂) = π ++ π₂(hpath₂)
        have hext₀ : ∃ (π₀₂ : NTM2ComputationPath) (cfg₀₂ : NTM2Config A x),
            TapeReachablePathNTM2 A x (π₀ ++ π₀₂) cfg₀₂ ∧ cfg₀₂.state ∈ A.acceptStates := by
          refine ⟨step :: π₂, cfg₂, ?_, hacc₂⟩
          simpa using hpath₂
        have hb := hK x (π₀ ++ [step]) (NTM2StepConfig cfg₀ step.result) hwf
          (by
            intro s hs
            rcases List.mem_append.mp hs with hml | hmr
            · exact hnoTerm s (by simp [hml])
            · have hsing : s = step := by simpa using hmr
              rw [hsing]
              exact hnoStep)
          (TapeReachablePathNTM2.cons π₀ step cfg₀ hrc hfrom hread hpos htrans)
          ⟨π₂, cfg₂, hpath₂, hacc₂⟩
        by_cases hvb : F4.im step.readSym = true
        · -- step 分叉：位置列表 = 尾部列表 ++ [step.pos]
          have hfilter_step : ([step].filter (fun s => F4.im s.readSym = true)) = [step] := by
            simp [hvb]
          rw [List.filter_append, List.map_append, hfilter_step]
          rw [List.nodup_append]
          constructor
          · exact ih hno₀ hext₀
          constructor
          · simp
          · -- a ∈ 尾部位置集 与 b = step.pos：前缀不占同位（条款②新口径，Spec V1.47）
            intro a ha b hb'
            rcases List.mem_singleton.mp hb' with rfl
            rcases List.mem_map.mp ha with ⟨t, ht, rfl⟩
            by_contra hpos_eq
            have ht_mem : t ∈ π₀ := (List.mem_filter.mp ht).1
            have hpre : ∀ s ∈ π₀, s.pos ≠ step.pos :=
              hb.2.1 π₀ step [] (by simp) hvb
            exact hpre t ht_mem hpos_eq
        · -- step 非分叉：位置列表就是尾部的
          have hfilter_step : ([step].filter (fun s => F4.im s.readSym = true)) = [] := by
            simp [hvb]
          rw [List.filter_append, List.map_append, hfilter_step]
          simpa using ih hno₀ hext₀
  rcases hext with ⟨π₂, cfg₂, hpath₂, hacc₂⟩
  have h0 : ∀ p : ℤ, p ∈ (π.filter (fun step => F4.im step.readSym = true)).map (fun step => step.pos) → 0 ≤ p := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨step, hstep, rfl⟩
    have hb := hK x π cfg hwf hnoTerm hr ⟨π₂, cfg₂, hpath₂, hacc₂⟩
    have hstep_mem : step ∈ π := (List.mem_filter.mp hstep).1
    exact (hb.1 step hstep_mem).1
  have hlt : ∀ p : ℤ, p ∈ (π.filter (fun step => F4.im step.readSym = true)).map (fun step => step.pos) → p < ((x.length : ℤ) + 1) := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨step, hstep, rfl⟩
    have hb := hK x π cfg hwf hnoTerm hr ⟨π₂, cfg₂, hpath₂, hacc₂⟩
    have hstep_mem : step ∈ π := (List.mem_filter.mp hstep).1
    have hle : step.pos ≤ (x.length : ℤ) := (hb.1 step hstep_mem).2.1
    omega
  have hlen : ((π.filter (fun step => F4.im step.readSym = true)).map (fun step => step.pos)).length =
      (π.filter (fun step => F4.im step.readSym = true)).length := by
    simp
  rw [← hlen]
  exact int_nodup_bounded_length
    ((π.filter (fun step => F4.im step.readSym = true)).map (fun step => step.pos))
    (x.length + 1) hnodup h0 hlt

/-- K ≤ 2^K（K ≥ 0，归纳）。 -/
lemma nat_le_two_pow (K : ℕ) : K ≤ 2 ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
      have h2pow : 0 < 2 ^ K := Nat.pow_pos (by decide : 0 < 2)
      calc
        K + 1 ≤ 2 ^ K + 1 := Nat.succ_le_succ ih
        _ ≤ 2 ^ K + 2 ^ K := by omega
        _ = 2 * 2 ^ K := by rw [two_mul]
        _ = 2 ^ (K + 1) := by
          rw [pow_succ]
          rw [Nat.mul_comm]

/-- 路径终点状态 = 最后一步的 nextState（路径非空时）。 -/
lemma ntm2_path_end_state (A : NTM2) (x : List F4) (π : NTM2ComputationPath)
    (cfg : NTM2Config A x) (h : TapeReachablePathNTM2 A x π cfg) (hne : π ≠ []) :
    cfg.state = (List.getLast π hne).result.1 := by
  induction h with
  | nil => simp at hne
  | cons π₀ step cfg₀ hrc₀ hfrom₀ hread₀ hpos₀ htrans₀ ih₀ =>
      dsimp [NTM2StepConfig]
      cases π₀ with
      | nil => simp
      | cons a rest =>
          have hlast : List.getLast ((a :: rest) ++ [step]) (by simp) = step := by
            rw [List.getLast_append_of_ne_nil (by simp : (a :: rest) ++ [step] ≠ []) (by simp : [step] ≠ [])]
            rfl
          rw [hlast]

/-- toCBTM A 在符号对齐输入上是多项式时间的（二次界，输入语义 = 计算纸带 4F4，
    spec 约定 25）：接受路径只存在于编码串上（条款 4，域 = IsSymbolAligned）；
    编码串 = 复合串（条款 2 语言桥），复合串上的路径与 NTM2 路径同长（同构桥），
    规范（Canonical）给出路径长度 ≤ K · 分叉步数 · 输入长度，
    分叉步数 ≤ 输入长度（forkCount_le_input_length）→ 二次界。
    2026-09-09 用户裁决：输入 = 4F4 计算符号串（flat4F4 像）——机器性质只在
    输入域内断言（isPolynomialTimeAligned），域外 F4 串不是输入（无半符号）。 -/
theorem toCBTM_polynomialTime (A : NTM2) (hcan : NTM2.Canonical A)
    (_hbridge : ∀ inst : SubsetSumInstance, inst.elements ≠ [] →
      ntm2InputToCBTM A (encodeInstBits inst) = encodeInstanceF4 inst)
    (hreject : ∀ w : List F4, IsSymbolAligned w →
      (∀ inst : SubsetSumInstance, inst.elements ≠ [] →
        ∀ gS : List Sym, w ≠ encodeInstanceF4 inst ++ flat4F4 gS) →
      ¬ (NTM2.toCBTM A).tapeAccepts w) :
    CBTM.isPolynomialTimeAligned (NTM2.toCBTM A) := by
  have hcan0 : NTM2.Canonical A := hcan
  rcases hcan with ⟨K, hK⟩
  refine ⟨fun n => K * (n + 2) * (n + 1) * (n + 1), ?_, ?_⟩
  · -- 多项式界：取 k = 12·K + 6（小 n 上 f n = K·(n+2)·(n+1)² 需 k ≥ 12K-1；
    -- n ≥ 2 时 K·(n+2)³ ≤ n^(2K+6) ≤ n^(12K+6)）
    refine ⟨12 * K + 6, ?_⟩
    intro n
    by_cases hn : n ≤ 1
    · have hn0 : n = 0 ∨ n = 1 := by omega
      rcases hn0 with rfl | rfl
      · have hp : 0 ^ (12 * K + 6) = 0 := Nat.zero_pow (by omega : 0 < 12 * K + 6)
        rw [hp]
        norm_num
        nlinarith
      · have hp : 1 ^ (12 * K + 6) = 1 := by simp
        rw [hp]
        norm_num
        nlinarith
    · have hn2 : 2 ≤ n := by omega
      have hn2' : 2 ≤ n + 2 := by omega
      have hKle : K ≤ (n + 2) ^ K := by
        calc
          K ≤ 2 ^ K := nat_le_two_pow K
          _ ≤ (n + 2) ^ K := Nat.pow_le_pow_left hn2' K
      have hnp2 : n + 2 ≤ n ^ 2 := by
        have h2n : 2 * n ≤ n * n := Nat.mul_le_mul_right n hn2
        nlinarith
      calc
        K * (n + 2) * (n + 1) * (n + 1) ≤ K * (n + 2) * (n + 2) * (n + 2) := by
          gcongr <;> omega
        _ ≤ (n + 2) ^ K * (n + 2) * (n + 2) * (n + 2) := by
          gcongr
        _ = (n + 2) ^ K * (n + 2) ^ 3 := by ring
        _ = (n + 2) ^ (K + 3) := by
          rw [pow_add]
        _ ≤ (n ^ 2) ^ (K + 3) := by
          exact Nat.pow_le_pow_left hnp2 (K + 3)
        _ = n ^ (2 * (K + 3)) := by
          rw [Nat.pow_mul]
        _ = n ^ (2 * K + 6) := by ring_nf
        _ ≤ n ^ (12 * K + 6) := by
          exact Nat.pow_le_pow_right (by omega : 0 < n) (by omega : 2 * K + 6 ≤ 12 * K + 6)
        _ ≤ n ^ (12 * K + 6) + (12 * K + 6) := by omega
  · intro w hal π cfg hr hacc hnoTerm
    -- 接受路径给出 tapeAccepts w；由条款 4（域内），w 必为某非空实例的编码串
    have haccT : (NTM2.toCBTM A).tapeAccepts w := ⟨π, cfg, hr, hacc⟩
    by_cases h : ∃ inst : SubsetSumInstance, ∃ gS : List Sym,
        inst.elements ≠ [] ∧ w = encodeInstanceF4 inst ++ flat4F4 gS
    · rcases h with ⟨inst, gS, hne, hw⟩
      have hwf : ∃ inst : SubsetSumInstance, ∃ gS : List Sym,
          w = SymToF4.encodeInstanceF4 inst ++ SymToF4.flat4F4 gS :=
        ⟨inst, gS, hw⟩
      rcases exists_CBTM_iso_NTM2 A with ⟨M, hM, ⟨iso⟩⟩
      subst M
      -- 接受路径满足 hnoTerm（isPolynomialTime 前提=首达即止），直接走同构桥回 NTM2
      rcases iso_path_backward A (NTM2.toCBTM A) iso w hcan0 hwf π cfg hnoTerm hr
        (⟨[], cfg, SymToF4.TapeSteps.nil, by simpa [NTM2.toCBTM] using hacc⟩) with
      ⟨π', cfg', hrc', hcfg', hlen, _hlt, _hnonneg, _hnoπ', _hmap⟩
      have haccA : cfg'.state ∈ A.acceptStates := by
        rw [← iso.h_accept]
        have hstate : cfg.state = cfg'.state := by
          rw [hcfg']
          rfl
        rw [← hstate]
        exact hacc
      -- 规范：路径长度 ≤ K·(分叉+1)·(len+1)（③，界分支）；尾巴分支与终点 ∈ accept 矛盾
      have hb := hK w π' cfg' hwf _hnoπ' hrc' ⟨[], cfg', by simpa using hrc', haccA⟩
      have hfork : (π'.filter (fun step => F4.im step.readSym = true)).length ≤ w.length + 1 :=
        forkCount_le_input_length A w π' cfg' hcan0 hwf _hnoπ' hrc' ⟨[], cfg', by simpa using hrc', haccA⟩
      have hbnd : π'.length ≤
          K * ((π'.filter (fun step => F4.im step.readSym = true)).length + 1) *
            (w.length + 1) * (w.length + 1) := by
        rcases hb.2.2 with hbnd | htail
        · exact hbnd
        · exfalso
          rcases htail with ⟨π₁, π₂, hsplit, hne₂, htail₂⟩
          have hπne : π' ≠ [] := by
            intro hp'
            rw [hp'] at hsplit
            simp at hsplit
            exact hne₂ hsplit.2
          have hlast : List.getLast π' hπne ∈ π₂ := by
            have hlast' : List.getLast (π₁ ++ π₂) (by simpa [hsplit] using hπne) ∈ π₂ := by
              rw [List.getLast_append_of_ne_nil]
              exact List.getLast_mem hne₂
            simpa [hsplit] using hlast'
          have htailLast := htail₂ (List.getLast π' hπne) hlast
          have hend : cfg'.state = (List.getLast π' hπne).result.1 :=
            ntm2_path_end_state A w π' cfg' hrc' hπne
          have hrejLast : cfg'.state ∈ A.rejectStates := by
            rw [hend]
            exact htailLast.2.1
          have hdis := A.h_accept_reject_disjoint
          have hm := Finset.mem_inter.mpr ⟨haccA, hrejLast⟩
          rw [hdis] at hm
          simp at hm
      calc
        π.length = π'.length := hlen
        _ ≤ K * ((π'.filter (fun step => F4.im step.readSym = true)).length + 1) *
            (w.length + 1) * (w.length + 1) := hbnd
        _ ≤ K * (w.length + 2) * (w.length + 1) * (w.length + 1) := by
          exact Nat.mul_le_mul_right (w.length + 1)
            (Nat.mul_le_mul_right (w.length + 1)
              (Nat.mul_le_mul_left K
                (by omega : (π'.filter (fun step => F4.im step.readSym = true)).length + 1 ≤
                  w.length + 2)))
    · exfalso
      apply hreject w hal
      · intro inst hne gS hw
        exact h ⟨inst, gS, hne, hw⟩
      · exact haccT

/-- 子集和 ∈ NP_F：witness = toCBTM subsetSumNTM2（**A1 已清除**，2026-09-13 主线 M2/M3）。
    七处消费点全部定理化：① `subsetSumNTM2_solves_of_canonical`（:85）、
    ② `subsetSumNTM2_input_bridge`（:52）、③ `subsetSumNTM2_canonical`（Q10，条款 (c) = A3 欠条）、
    ④ `subsetSumNTM2_hrel` / `subsetSumNTM2_rejects_nonencoding`（:115/:126）、
    ⑤ `subsetSumNTM2_hrel2`（T16:172）。
    多项式时间（实化 isPolynomialTimeAligned，域内界）：toCBTM_polynomialTime（二次界）。 -/
theorem subsetSum_in_NP_F : IsNP_F subsetSumLanguageF4Real := by
  refine ⟨NTM2.toCBTM subsetSumNTM2, toCBTM_polynomialTime subsetSumNTM2 subsetSumNTM2_canonical
    subsetSumNTM2_input_bridge
    (toCBTM_rejects_nonencoding subsetSumNTM2 subsetSumNTM2_hrel), ?_⟩
  intro w hwf0
  constructor
  · -- 可靠性：M.tapeAccepts w → w ∈ L
    intro hacc
    rcases exists_CBTM_iso_NTM2 subsetSumNTM2 with ⟨M, hM, ⟨iso⟩⟩
    subst M
    rcases subsetSumNTM2_hrel (NTM2.toCBTM subsetSumNTM2) ⟨iso⟩ w hwf0 hacc with
      ⟨inst, gS, hw, hne, hpos, htarget⟩
    -- ⑤（.2 尾缀版 → 原版）：接受 encS ++ gS ⟹ 接受 encS
    have hacc_enc : (NTM2.toCBTM subsetSumNTM2).tapeAccepts (encodeInstanceF4 inst) := by
      have hacc' : (NTM2.toCBTM subsetSumNTM2).tapeAccepts (encodeInstanceF4 inst ++ flat4F4 gS) := by
        simpa [hw] using hacc
      exact (subsetSumNTM2_hrel2 inst hne (encodeElementsSym_nonempty hne) htarget gS).2 hacc'
    have hacc_A : subsetSumNTM2.acceptsTape (encodeInstBits inst) := by
      apply (StructIso_preserves_accepts subsetSumNTM2 (NTM2.toCBTM subsetSumNTM2) iso
        subsetSumNTM2_canonical (encodeInstBits inst)
        (by
          refine ⟨inst, ([] : List Sym), ?_⟩
          simp [encodeInstBits, encodeInstanceF4, flat4F4])).2
      simpa [encodeInstBits, ← hw] using hacc_enc
    have hholds : subsetSumHolds inst :=
      (subsetSumNTM2_solves_of_canonical subsetSumNTM2_canonical inst hne hpos htarget).2 hacc_A
    exact ⟨inst, gS, hw, hne, hpos, htarget, hholds⟩
  · -- 完备性：w ∈ L → M.tapeAccepts w
    intro hL
    rcases hL with ⟨inst, gS, hw, hne, hpos, htarget, hholds⟩
    rcases exists_CBTM_iso_NTM2 subsetSumNTM2 with ⟨M, hM, ⟨iso⟩⟩
    subst M
    have hA : subsetSumNTM2.acceptsTape (encodeInstBits inst) :=
      (subsetSumNTM2_solves_of_canonical subsetSumNTM2_canonical inst hne hpos htarget).1 hholds
    have hb := StructIso_preserves_accepts subsetSumNTM2 (NTM2.toCBTM subsetSumNTM2) iso
      subsetSumNTM2_canonical (encodeInstBits inst)
      (by
        refine ⟨inst, ([] : List Sym), ?_⟩
        simp [encodeInstBits, encodeInstanceF4, flat4F4])
    have hcbtm : (NTM2.toCBTM subsetSumNTM2).tapeAccepts (ntm2InputToCBTM subsetSumNTM2 (encodeInstBits inst)) :=
      hb.1 hA
    have hcbtm_enc : (NTM2.toCBTM subsetSumNTM2).tapeAccepts (encodeInstanceF4 inst) := by
      simpa [encodeInstBits, ntm2InputToCBTM] using hcbtm
    have hcbtm_w : (NTM2.toCBTM subsetSumNTM2).tapeAccepts w := by
      simpa [hw] using (subsetSumNTM2_hrel2 inst hne (encodeElementsSym_nonempty hne) htarget gS).1 hcbtm_enc
    exact hcbtm_w

end Mp
