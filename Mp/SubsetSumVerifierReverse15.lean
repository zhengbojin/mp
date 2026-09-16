/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import Mp.SubsetSumVerifierReverse13
import Mp.SubsetSumVerifierCBTM
import Mp.SubsetSumVerifierReverse13A
import Mp.SubsetSumVerifierPosBound5

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
# R15 · 总装层（⑤ 收口）

消费 R13 的逐元素段（`segSrFold` 全链）与 R12 的判定段（`segS3`），
把「折叠输出 → 判定入口」接线，供四相位串联（`phase_decomp`）与主定理（⑥）使用。
-/

namespace Mp

open SymToF4

/-- [⑤ 接线] 折叠输出（state 22 + 目标区归零 + kinds/无标/清理区全零）⟹ `segS3` 判定段（22 → 100）。

入口取 `(q, n) := (0, (p_e + T).toNat)`：`q` 处为左界符 `Sym.boundary`，
`q + n + 1` 处为终止标记 `Sym.mk boundary true`（即折叠输出头位）。
前件三件由 `judge_pre_of_fold` 组装：`[1, p_e−2]` 区经（kinds + 无标 + 值零）全零，
`[p_e−1, p_e+T]` 区由折叠的清理区全零子句给出。 -/
lemma judge_after_fold (bs : List ℕ) (p_e : ℤ) (cfg' : SymConfig)
    (hp2 : 0 ≤ p_e - 2)
    (hst : cfg'.state = 22)
    (hhd : cfg'.headPos = p_e + 1 + ((famRest bs).length : ℤ))
    (hmark : cfg'.tape (p_e + 1 + ((famRest bs).length : ℤ)) = Sym.mk SymKind.boundary true)
    (hbl : cfg'.tape 0 = Sym.boundary)
    (hreg0 : regVal cfg'.tape ((p_e - 2).toNat) = 0)
    (hkd : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
      (cfg'.tape i).1 = SymKind.data0 ∨ (cfg'.tape i).1 = SymKind.data1)
    (hfl : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 → (cfg'.tape i).2 = false)
    (hz : ∀ i : ℤ, p_e - 1 ≤ i → i ≤ p_e + ((famRest bs).length : ℤ) → cfg'.tape i = Sym.data0) :
    ∃ π cfg₂, SymSteps VerifierSym.transition cfg' π cfg₂ ∧
      π.length ≤ ((p_e + ((famRest bs).length : ℤ)).toNat) + 2 ∧
      cfg₂.state = 100 ∧ cfg₂.headPos = 1 ∧ cfg₂.tape = cfg'.tape := by
  have hTnn : 0 ≤ p_e + ((famRest bs).length : ℤ) := by
    have hlen : (0 : ℤ) ≤ ((famRest bs).length : ℤ) := by positivity
    omega
  have hncast : (((p_e + ((famRest bs).length : ℤ)).toNat : ℕ) : ℤ) =
      p_e + ((famRest bs).length : ℤ) := Int.toNat_of_nonneg hTnn
  obtain ⟨hzero, hb0, hmark0⟩ := judge_pre_of_fold bs p_e cfg' ((famRest bs).length : ℤ)
    hp2 rfl hmark hbl hreg0 hkd hfl hz
  rcases segS3 ((p_e + ((famRest bs).length : ℤ)).toNat) 0 cfg'.tape
    (by
      rw [zero_add, hncast]
      rw [show p_e + ((famRest bs).length : ℤ) + 1 =
          p_e + 1 + ((famRest bs).length : ℤ) from by ring]
      exact hmark)
    (by
      intro i hi1 hi2
      rw [zero_add, hncast] at hi2
      exact hzero i hi1 hi2)
    hb0
    with ⟨π, cfg₂, hs, hlen, hst₂, hhd₂, htape⟩
  refine ⟨π, cfg₂, ?_, ?_, hst₂, ?_, htape⟩
  · have he : cfg' = SymConfig.mk 22 cfg'.tape
        (0 + (((p_e + ((famRest bs).length : ℤ)).toNat : ℕ) : ℤ) + 1) := by
      rw [show 0 + (((p_e + ((famRest bs).length : ℤ)).toNat : ℕ) : ℤ) + 1 =
          p_e + 1 + ((famRest bs).length : ℤ) from by
        rw [hncast]
        ring]
      rw [show cfg' = SymConfig.mk cfg'.state cfg'.tape cfg'.headPos from rfl]
      rw [hst, hhd]
    rw [he]
    exact hs
  · exact hlen
  · rw [hhd₂]
    norm_num

/-! ## ⑤-a 入口桥件：编码 ↔ 值 -/

/-- [入口桥 1] 全 1 位串之值：`ofDigits 2 (replicate b 1) = 2^b − 1`。 -/
lemma ofDigits_two_replicate_one (b : ℕ) :
    Nat.ofDigits 2 (List.replicate b 1) = 2 ^ b - 1 := by
  induction b with
  | zero => simp [Nat.ofDigits]
  | succ b ih =>
      rw [List.replicate_succ, Nat.ofDigits_cons, ih, pow_succ]
      have hb : 1 ≤ 2 ^ b := Nat.one_le_two_pow
      omega

/-- 辅助：`(replicate b 1) 映射 0↦data0/d↦data1 = replicate b data1`。 -/
lemma map_replicate_one_data1 (b : ℕ) :
    (List.replicate b 1).map (fun d => if d = 0 then Sym.data0 else Sym.data1)
      = List.replicate b Sym.data1 := by
  induction b with
  | zero => rfl
  | succ b ih =>
      rw [List.replicate_succ, List.map_cons, ih]
      rfl

/-- [入口桥 2] 全 1 元素的原生编码 = b 个 data1。 -/
lemma encodeBitsSymNative_two_pow_sub_one (b : ℕ) :
    encodeBitsSymNative (2 ^ b - 1) = List.replicate b Sym.data1 := by
  have hdig : Nat.digits 2 (2 ^ b - 1) = List.replicate b 1 := by
    rw [← ofDigits_two_replicate_one b]
    refine Nat.digits_ofDigits 2 (by norm_num) _ ?_ ?_
    · intro l hl
      rw [List.mem_replicate] at hl
      omega
    · intro h
      have : (List.replicate b (1 : ℕ)).getLast h = 1 := by
        rw [List.getLast_replicate]
      omega
  unfold encodeBitsSymNative
  rw [hdig, map_replicate_one_data1]

/-- [入口桥 3] 全 1 位串的编码（`encodeBitsSym` 与 Native 同体）。 -/
lemma encodeBitsSym_two_pow_sub_one (b : ℕ) :
    encodeBitsSym (2 ^ b - 1) = List.replicate b Sym.data1 := by
  rw [show encodeBitsSym (2 ^ b - 1) = encodeBitsSymNative (2 ^ b - 1) from rfl]
  exact encodeBitsSymNative_two_pow_sub_one b

/-- [入口桥 4] 解码的追加单步。 -/
lemma decodeBitsSym_concat_singleton (l : List Sym) (s : Sym) :
    decodeBitsSym (l ++ [s]) = decodeBitsSym l + 2 ^ l.length * bitVal s := by
  unfold decodeBitsSym
  rw [List.map_append, List.map_cons, List.map_nil, Nat.ofDigits_append]
  simp only [List.length_map]
  rw [show Nat.ofDigits 2 [bitVal s] = bitVal s from by simp [Nat.ofDigits, Nat.ofDigits_cons]]

/-- [入口桥 5] `bitVal` 的指示函数形。 -/
lemma bitVal_eq_indicator (s : Sym) :
    bitVal s = if s.1 = SymKind.data1 then 1 else 0 := by
  rcases s with ⟨k, fl⟩
  cases k <;> simp [bitVal]

/-- [入口桥 5b] `bitVal` 的 ℤ 指示函数形。 -/
lemma bitVal_cast_eq (s : Sym) :
    ((bitVal s : ℕ) : ℤ) = if s.1 = SymKind.data1 then 1 else 0 := by
  rcases s with ⟨k, fl⟩
  cases k <;> simp [bitVal]

/-- [入口桥 6] 带磁带一致性的区域值 = 位串值（归纳：自右向左剥离）。 -/
lemma regValA_ofDigits (tape : ℤ → Sym) (b : ℤ) :
    ∀ (l : List Sym) (acc : ℤ),
      (∀ (j : ℕ) (hj : j < l.length), tape (b + (j : ℤ)) = l[j]) →
      regValA tape b l.length acc = acc + (decodeBitsSym l : ℤ) := by
  intro l
  induction l using List.reverseRecOn with
  | nil =>
      intro acc _
      simp [regValA, decodeBitsSym, Nat.ofDigits]
  | append_singleton l s ih =>
      intro acc h
      have hlast : tape (b + (l.length : ℤ)) = s := by
        have hh := h l.length (by simp)
        simpa using hh
      have hpre : ∀ (j : ℕ) (hj : j < l.length), tape (b + (j : ℤ)) = l[j] := by
        intro j hj
        have hh := h j (by simpa using Nat.lt_succ_of_lt hj)
        rwa [List.getElem_append_left hj] at hh
      simp only [List.length_append, List.length_cons, List.length_nil]
      rw [regValA, hlast]
      rw [ih (acc + (if s.1 = SymKind.data1 then (2 : ℤ) ^ l.length else 0)) hpre]
      rw [decodeBitsSym_concat_singleton]
      push_cast
      by_cases hk : s.1 = SymKind.data1
      · rw [if_pos hk, bitVal_cast_eq, if_pos hk]
        ring
      · rw [if_neg hk, bitVal_cast_eq, if_neg hk]
        ring

/-- [入口桥 7] target 区寄存值 = target 值。 -/
lemma regVal_tapeAgrees_encodeBitsSym (tape : ℤ → Sym) (n : ℕ)
    (hagree : tapeAgrees tape 1 (encodeBitsSym n)) :
    regVal tape (encodeBitsSym n).length = (n : ℤ) := by
  have h := regValA_ofDigits tape 1 (encodeBitsSym n) 0 (fun j hj => hagree j hj)
  have hdec : decodeBitsSym (encodeBitsSym n) = n := decodeBitsSym_encodeBitsSym n
  unfold regVal
  rw [h, hdec]
  ring

/-- [入口桥 8] 全 1 全选元素区 = `Sym.sel :: famRest bs`。 -/
lemma encodeElementsSymWithSel_all1 (bs : List ℕ) (hne : bs ≠ []) :
    encodeElementsSymWithSel (bs.map (fun b => 2 ^ b - 1)) (List.replicate bs.length true)
      = Sym.sel :: famRest bs := by
  induction bs with
  | nil => exact absurd rfl hne
  | cons b bs ih =>
      cases bs with
      | nil =>
          show encodeElementsSymWithSel [2 ^ b - 1] [true] = Sym.sel :: famRest [b]
          rw [show encodeElementsSymWithSel [2 ^ b - 1] [true] =
              Sym.sel :: encodeBitsSymNative (2 ^ b - 1) from by
            simp [encodeElementsSymWithSel, joinLists, joinLists_cons]]
          rw [encodeBitsSymNative_two_pow_sub_one, famRest_single]
      | cons c rest =>
          have ih' := ih (by simp)
          show encodeElementsSymWithSel ((2 ^ b - 1) :: ((c :: rest).map (fun b => 2 ^ b - 1)))
              (true :: List.replicate (c :: rest).length true)
            = Sym.sel :: famRest (b :: c :: rest)
          rw [show encodeElementsSymWithSel ((2 ^ b - 1) :: ((c :: rest).map (fun b => 2 ^ b - 1)))
                (true :: List.replicate (c :: rest).length true)
              = Sym.sel :: encodeBitsSymNative (2 ^ b - 1)
                  ++ encodeElementsSymWithSel ((c :: rest).map (fun b => 2 ^ b - 1))
                       (List.replicate (c :: rest).length true) from by
            simp [encodeElementsSymWithSel, List.zip_cons_cons, joinLists, joinLists_cons]]
          rw [encodeBitsSymNative_two_pow_sub_one, ih', famRest_cons_cons]
          simp

/-! ## ⑤-a 桥件续：tapeAgrees 工具 · 最坏族 · 区域性质 -/

/-- [入口桥 9] `tapeAgrees` 头部。 -/
lemma tapeAgrees_head (tape : ℤ → Sym) (a : ℤ) (s : Sym) (l : List Sym)
    (h : tapeAgrees tape a (s :: l)) : tape a = s := by
  have hh := h 0 (by simp)
  simpa using hh

/-- [入口桥 10] `tapeAgrees` 尾部（位移 1）。 -/
lemma tapeAgrees_tail (tape : ℤ → Sym) (a : ℤ) (s : Sym) (l : List Sym)
    (h : tapeAgrees tape a (s :: l)) : tapeAgrees tape (a + 1) l := by
  intro i hi
  have hh := h (i + 1) (by simp [hi])
  have he : a + 1 + (i : ℤ) = a + ((i + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [he]
  simpa using hh

/-- [入口桥 11] 编码格无标。 -/
lemma mem_encodeBitsSym_flag (n : ℕ) {s : Sym} (hs : s ∈ encodeBitsSym n) : s.2 = false := by
  unfold encodeBitsSym at hs
  rcases List.mem_map.mp hs with ⟨d, _, rfl⟩
  by_cases h : d = 0
  · simp [h, Sym.data0]
  · simp [h, Sym.data1]

/-- [入口桥 13] 最坏案例谓词（全 1 元素、和 = target）。 -/
def WorstCase (bs : List ℕ) (inst : SubsetSumInstance) : Prop :=
  inst.elements = bs.map (fun b => 2 ^ b - 1) ∧
    inst.target = (valSum bs).toNat ∧ bs ≠ [] ∧ ∀ b ∈ bs, 1 ≤ b

/-- [入口桥 14] valSum 非负。 -/
lemma valSum_nonneg (bs : List ℕ) : 0 ≤ valSum bs := by
  unfold valSum
  apply List.sum_nonneg
  intro x hx
  rcases List.mem_map.mp hx with ⟨b, _, rfl⟩
  have h1 : (1 : ℤ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
  omega

/-- [入口桥 15] 单元素值 ≤ 族和。 -/
lemma le_valSum_of_mem (bs : List ℕ) (b : ℕ) (hb : b ∈ bs) :
    (2 : ℤ) ^ b - 1 ≤ valSum bs := by
  induction bs with
  | nil => simp at hb
  | cons c rest ih =>
      unfold valSum at ih ⊢
      rw [List.map_cons, List.sum_cons]
      rw [List.mem_cons] at hb
      have hrest : 0 ≤ (List.map (fun b => (2 : ℤ) ^ b - 1) rest).sum := by
        apply List.sum_nonneg
        intro x hx
        rcases List.mem_map.mp hx with ⟨b', _, rfl⟩
        have h1 : (1 : ℤ) ≤ 2 ^ b' := one_le_pow₀ (by norm_num)
        omega
      rcases hb with rfl | hb
      · omega
      · have ih' := ih hb
        have hhead : 0 ≤ (2 : ℤ) ^ c - 1 := by
          have h1 : (1 : ℤ) ≤ 2 ^ c := one_le_pow₀ (by norm_num)
          omega
        omega

/-- [入口桥 16] 全 1 元素位长 ≤ target 位长。 -/
lemma bitlen_le_target (bs : List ℕ) (b : ℕ) (hb : b ∈ bs) (hb1 : 1 ≤ b) :
    (b : ℤ) ≤ ((encodeBitsSym ((valSum bs).toNat)).length : ℤ) := by
  have hterm : (2 : ℤ) ^ b - 1 ≤ valSum bs := le_valSum_of_mem bs b hb
  set target := (valSum bs).toNat with htarget
  have hcast : ((target : ℤ)) = valSum bs := Int.toNat_of_nonneg (valSum_nonneg bs)
  have hle : 2 ^ b - 1 ≤ target := by
    rw [← Nat.cast_le (α := ℤ)]
    have hcast2 : ((2 ^ b - 1 : ℕ) : ℤ) = (2 : ℤ) ^ b - 1 := by
      rw [Nat.cast_sub (Nat.one_le_two_pow)]
      push_cast
      ring
    rw [hcast2, hcast]
    exact hterm
  have htarget_pos : target ≠ 0 := by
    have h1 : 1 ≤ 2 ^ b - 1 := by
      have h2 : 2 ^ 1 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb1
      omega
    omega
  have hlen : b ≤ (encodeBitsSym target).length := by
    have hm : (encodeBitsSym target).length = Nat.log 2 target + 1 := by
      unfold encodeBitsSym
      rw [List.length_map, Nat.length_digits 2 target (by norm_num) htarget_pos]
    rw [hm]
    have hpow : 2 ^ (b - 1) ≤ target := by
      have h2 : 2 ^ (b - 1) ≤ 2 ^ b - 1 := by
        have heq : 2 ^ b = 2 ^ (b - 1) * 2 := by
          rw [← pow_succ]
          congr 1
          omega
        have hp : 1 ≤ 2 ^ (b - 1) := Nat.one_le_two_pow
        omega
      omega
    have hlog : (b - 1) ≤ Nat.log 2 target :=
      (Nat.le_log_iff_pow_le (by norm_num) htarget_pos).mpr hpow
    omega
  exact_mod_cast hlen

/-- [入口桥 17] target 区的格属 kinds。 -/
lemma tgt_region_kind (tape : ℤ → Sym) (n : ℕ)
    (h : tapeAgrees tape 1 (encodeBitsSym n)) :
    ∀ i : ℤ, 1 ≤ i → i ≤ (encodeBitsSym n).length →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1 := by
  intro i hi1 hi2
  have hj : ((i - 1).toNat) < (encodeBitsSym n).length := by
    have hcast : ((i - 1).toNat : ℤ) = i - 1 := Int.toNat_of_nonneg (by omega)
    omega
  have hi : i = 1 + (((i - 1).toNat : ℕ) : ℤ) := by
    have hcast : ((i - 1).toNat : ℤ) = i - 1 := Int.toNat_of_nonneg (by omega)
    omega
  rw [hi]
  have hh := h ((i - 1).toNat) hj
  rw [hh]
  exact mem_encodeBitsSym_kind n (List.getElem_mem hj)

/-- [入口桥 18] target 区的格属无标。 -/
lemma tgt_region_flag (tape : ℤ → Sym) (n : ℕ)
    (h : tapeAgrees tape 1 (encodeBitsSym n)) :
    ∀ i : ℤ, 1 ≤ i → i ≤ (encodeBitsSym n).length → (tape i).2 = false := by
  intro i hi1 hi2
  have hj : ((i - 1).toNat) < (encodeBitsSym n).length := by
    have hcast : ((i - 1).toNat : ℤ) = i - 1 := Int.toNat_of_nonneg (by omega)
    omega
  have hi : i = 1 + (((i - 1).toNat : ℕ) : ℤ) := by
    have hcast : ((i - 1).toNat : ℤ) = i - 1 := Int.toNat_of_nonneg (by omega)
    omega
  rw [hi]
  have hh := h ((i - 1).toNat) hj
  rw [hh]
  exact mem_encodeBitsSym_flag n (List.getElem_mem hj)

/-- [入口桥 19] 格式检验输出 ⟹ 折叠十二前置（全 1 全选最坏实例；`tape` = 打标后磁带）。 -/
lemma fold_pre_of_worst (bs : List ℕ) (inst : SubsetSumInstance) (tape tape₀ : ℤ → Sym)
    (hw : WorstCase bs inst)
    (hout : ∀ i : ℤ, tape i = if i = 2 + ((encodeBitsSym inst.target).length : ℤ) +
        ((encodeElementsSym inst.elements).length : ℤ)
        then Sym.mk SymKind.boundary true else tape₀ i)
    (htgt : tapeAgrees tape₀ 1 (encodeBitsSym inst.target))
    (hbound0 : tape₀ (1 + ((encodeBitsSym inst.target).length : ℤ)) = Sym.boundary)
    (hboundL : tape₀ 0 = Sym.boundary)
    (hels : tapeAgrees tape₀ (2 + ((encodeBitsSym inst.target).length : ℤ))
      (encodeElementsSymWithSel inst.elements (List.replicate inst.elements.length true))) :
    bs ≠ [] ∧ (∀ b ∈ bs, 1 ≤ b) ∧
    (∀ b ∈ bs, (b : ℤ) ≤ (2 + ((encodeBitsSym inst.target).length : ℤ)) - 2) ∧
    tape (2 + ((encodeBitsSym inst.target).length : ℤ)) = Sym.sel ∧
    tape ((2 + ((encodeBitsSym inst.target).length : ℤ)) - 1) = Sym.boundary ∧
    tape 0 = Sym.boundary ∧
    (∀ i : ℤ, 1 ≤ i → i ≤ (2 + ((encodeBitsSym inst.target).length : ℤ)) - 2 →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1) ∧
    (∀ i : ℤ, 1 ≤ i → i ≤ (2 + ((encodeBitsSym inst.target).length : ℤ)) - 2 →
      (tape i).2 = false) ∧
    tapeAgrees tape (2 + ((encodeBitsSym inst.target).length : ℤ) + 1) (famRest bs) ∧
    tape (2 + ((encodeBitsSym inst.target).length : ℤ) + 1 + ((famRest bs).length : ℤ)) =
      Sym.mk SymKind.boundary true ∧
    valSum bs ≤ regVal tape ((2 + ((encodeBitsSym inst.target).length : ℤ) - 2).toNat) ∧
    regVal tape ((2 + ((encodeBitsSym inst.target).length : ℤ) - 2).toNat) = valSum bs := by
  have hlen8 : ((encodeElementsSym inst.elements).length : ℤ) = ((famRest bs).length : ℤ) + 1 := by
    have h1 : (encodeElementsSymWithSel inst.elements
        (List.replicate inst.elements.length true)).length = (encodeElementsSym inst.elements).length :=
      WithSel_length inst.elements _ (by simp)
    have h2 : encodeElementsSymWithSel inst.elements (List.replicate inst.elements.length true)
        = Sym.sel :: famRest bs := by
      rw [show encodeElementsSymWithSel inst.elements (List.replicate inst.elements.length true)
          = encodeElementsSymWithSel (bs.map (fun b => 2 ^ b - 1)) (List.replicate bs.length true)
          from by rw [hw.1, List.length_map],
        encodeElementsSymWithSel_all1 bs hw.2.2.1]
    rw [← h1, h2]
    simp
  have hEpos : 1 ≤ ((encodeElementsSym inst.elements).length : ℤ) := by
    have hT0 : (0 : ℤ) ≤ ((famRest bs).length : ℤ) := Int.natCast_nonneg _
    omega
  have hkeep : ∀ i : ℤ, i ≠ 2 + ((encodeBitsSym inst.target).length : ℤ) +
      ((encodeElementsSym inst.elements).length : ℤ) → tape i = tape₀ i := by
    intro i hi
    rw [hout i, if_neg hi]
  have hels' : tapeAgrees tape₀ (2 + ((encodeBitsSym inst.target).length : ℤ))
      (Sym.sel :: famRest bs) := by
    rw [show encodeElementsSymWithSel inst.elements (List.replicate inst.elements.length true)
        = Sym.sel :: famRest bs from by
      rw [show encodeElementsSymWithSel inst.elements (List.replicate inst.elements.length true)
          = encodeElementsSymWithSel (bs.map (fun b => 2 ^ b - 1)) (List.replicate bs.length true)
          from by rw [hw.1, List.length_map],
        encodeElementsSymWithSel_all1 bs hw.2.2.1]] at hels
    exact hels
  have ht' : (2 + ((encodeBitsSym inst.target).length : ℤ)) - 2
      = ((encodeBitsSym inst.target).length : ℤ) := by ring
  have hnotp2 : ∀ i : ℤ, i ≤ 2 + ((encodeBitsSym inst.target).length : ℤ) +
      ((famRest bs).length : ℤ) →
      i ≠ 2 + ((encodeBitsSym inst.target).length : ℤ) +
        ((encodeElementsSym inst.elements).length : ℤ) := by
    intro i hi hcon
    omega
  have hsel0 : tape (2 + ((encodeBitsSym inst.target).length : ℤ)) = Sym.sel := by
    rw [hkeep _ (hnotp2 _ (by omega))]
    exact tapeAgrees_head tape₀ (2 + ((encodeBitsSym inst.target).length : ℤ)) Sym.sel (famRest bs) hels'
  have hb00 : tape ((2 + ((encodeBitsSym inst.target).length : ℤ)) - 1) = Sym.boundary := by
    rw [hkeep _ (hnotp2 _ (by omega)), show (2 + ((encodeBitsSym inst.target).length : ℤ)) - 1
        = 1 + ((encodeBitsSym inst.target).length : ℤ) from by ring]
    exact hbound0
  have hbL0 : tape 0 = Sym.boundary := by
    rw [hkeep _ (hnotp2 _ (by omega))]
    exact hboundL
  have hkd0 : ∀ i : ℤ, 1 ≤ i → i ≤ (2 + ((encodeBitsSym inst.target).length : ℤ)) - 2 →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1 := by
    intro i hi1 hi2
    rw [ht'] at hi2
    rw [hkeep _ (hnotp2 _ (by omega))]
    exact tgt_region_kind tape₀ inst.target htgt i hi1 hi2
  have hfl0 : ∀ i : ℤ, 1 ≤ i → i ≤ (2 + ((encodeBitsSym inst.target).length : ℤ)) - 2 →
      (tape i).2 = false := by
    intro i hi1 hi2
    rw [ht'] at hi2
    rw [hkeep _ (hnotp2 _ (by omega))]
    exact tgt_region_flag tape₀ inst.target htgt i hi1 hi2
  have henc0 : tapeAgrees tape (2 + ((encodeBitsSym inst.target).length : ℤ) + 1) (famRest bs) := by
    have htail : tapeAgrees tape₀ (2 + ((encodeBitsSym inst.target).length : ℤ) + 1)
        (famRest bs) :=
      tapeAgrees_tail tape₀ (2 + ((encodeBitsSym inst.target).length : ℤ)) Sym.sel (famRest bs) hels'
    intro i hi
    have hlt : ((i : ℤ)) < ((famRest bs).length : ℤ) := by exact_mod_cast hi
    rw [hkeep _ (hnotp2 _ (by omega))]
    exact htail i hi
  have h1m0 : tape (2 + ((encodeBitsSym inst.target).length : ℤ) + 1 +
      ((famRest bs).length : ℤ)) = Sym.mk SymKind.boundary true := by
    rw [hout _]
    rw [if_pos ?_]
    · rw [hlen8]
      ring
  have hr0ex0 : regVal tape ((2 + ((encodeBitsSym inst.target).length : ℤ) - 2).toNat)
      = valSum bs := by
    have ht2 : ((2 + ((encodeBitsSym inst.target).length : ℤ)) - 2).toNat
        = (encodeBitsSym inst.target).length := by
      rw [ht']
      simp
    rw [ht2]
    have hcongr : regVal tape ((encodeBitsSym inst.target).length)
        = regVal tape₀ ((encodeBitsSym inst.target).length) := by
      unfold regVal
      apply regValA_congr_below
      intro j hj
      rw [hkeep _ (hnotp2 _ (by
        have hjcast : (j : ℤ) < ((encodeBitsSym inst.target).length : ℤ) := by exact_mod_cast hj
        omega))]
    rw [hcongr, regVal_tapeAgrees_encodeBitsSym tape₀ inst.target htgt, hw.2.1]
    exact Int.toNat_of_nonneg (valSum_nonneg bs)
  refine ⟨hw.2.2.1, hw.2.2.2, ?_, hsel0, hb00, hbL0, hkd0, hfl0, henc0, h1m0, ?_, hr0ex0⟩
  · intro b hb
    rw [ht', hw.2.1]
    exact bitlen_le_target bs b hb (hw.2.2.2 b hb)
  · exact hr0ex0.ge

/-- [⑤-b 总装] 四相位串联（①α → ②格式 → ③折叠 → ④判定）：
    最坏案例（全 1 元素、全选、和 = target）下初始配置直达状态 100。 -/
theorem phase_decomp (bs : List ℕ) (inst : SubsetSumInstance) (hw : WorstCase bs inst) :
    ∃ π cfg, SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π cfg ∧
      cfg.state = 100 ∧ cfg.headPos = 1 ∧
      π.length ≤ (encodeInstanceSym inst).length + 3 +
        2 * (3 + (encodeBitsSym inst.target).length + (encodeElementsSym inst.elements).length) +
        ((foldLenB bs (2 + ((encodeBitsSym inst.target).length : ℤ))).toNat) +
        (((2 + ((encodeBitsSym inst.target).length : ℤ)) + ((famRest bs).length : ℤ)).toNat + 2) := by
  -- ① α替换
  rcases segS0 inst (List.replicate inst.elements.length true) (by simp) with
    ⟨π₀, cfg₁, hs₀, hst₁, hhd₁, hlen₀, htape0₁, htgt₁, hbnd0₁, hels₁, hbnd1₁⟩
  -- ② 格式检验（需要最坏案例的要素事实）
  have hne : inst.elements ≠ [] := by
    rw [hw.1]
    intro hcon
    exact hw.2.2.1 (List.map_eq_nil_iff.mp hcon)
  have hposE : ∀ v ∈ inst.elements, 0 < v := by
    intro v hv
    rw [hw.1] at hv
    rcases List.mem_map.mp hv with ⟨b, hb, rfl⟩
    have h1 : 1 ≤ b := hw.2.2.2 b hb
    have h2 : (2 : ℕ) ≤ 2 ^ b := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h1
    omega
  have htarget0 : 0 < inst.target := by
    rw [hw.2.1]
    apply Nat.pos_of_ne_zero
    intro hcon
    have hc : (((valSum bs).toNat : ℤ)) = valSum bs := Int.toNat_of_nonneg (valSum_nonneg bs)
    have hzero : valSum bs = 0 := by
      rw [hcon] at hc
      simpa using hc.symm
    cases bs with
    | nil => exact hw.2.2.1 rfl
    | cons b0 rest =>
        have h1 : (2 : ℤ) ^ b0 - 1 ≤ valSum (b0 :: rest) := le_valSum_of_mem _ b0 (by simp)
        have hb0' : 1 ≤ b0 := hw.2.2.2 b0 (by simp)
        have h3 : (2 : ℤ) ≤ 2 ^ b0 := by
          calc (2 : ℤ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ b0 := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hb0'
        omega
  rcases segS1 inst (List.replicate inst.elements.length true) (by simp) hne hposE htarget0
      cfg₁.tape htape0₁ htgt₁ hbnd0₁ hels₁ hbnd1₁ with
    ⟨π₁, cfg₂, hs₁, hst₂, hhd₂, hlen₁, htape_f⟩
  have he₁ : cfg₁ = SymConfig.mk 3 cfg₁.tape (2 + ((encodeBitsSym inst.target).length : ℤ) +
      ((encodeElementsSym inst.elements).length : ℤ)) := by
    rw [show cfg₁ = SymConfig.mk cfg₁.state cfg₁.tape cfg₁.headPos from rfl, hst₁, hhd₁]
  have he₂ : cfg₂ = SymConfig.mk 4 cfg₂.tape (2 + ((encodeBitsSym inst.target).length : ℤ)) := by
    rw [show cfg₂ = SymConfig.mk cfg₂.state cfg₂.tape cfg₂.headPos from rfl, hst₂, hhd₂]
  -- ③ 折叠（十二前置经入口桥）
  have hout : ∀ i : ℤ, cfg₂.tape i = if i = 2 + ((encodeBitsSym inst.target).length : ℤ) +
      ((encodeElementsSym inst.elements).length : ℤ) then Sym.mk SymKind.boundary true else cfg₁.tape i := by
    intro i
    rw [htape_f]
  obtain ⟨hne', hall1', hpos', hsel', hbound0', hboundL', hkd', hfl', henc', h1mark', hR0', hR0ex'⟩ :=
    fold_pre_of_worst bs inst cfg₂.tape cfg₁.tape hw hout htgt₁ hbnd0₁ htape0₁ hels₁
  obtain ⟨π₂, cfg₃, hfold_rest⟩ := segSrFold bs (2 + ((encodeBitsSym inst.target).length : ℤ)) cfg₂.tape
      hne' hall1' hpos' hsel' hbound0' hboundL' hkd' hfl' henc' h1mark' hR0' hR0ex'
  obtain ⟨hs₂, hst₃, hhd₃, hmark₃, hbl₃, hlen₂, hreg₃, hkd₃, hfl₃, hz₃⟩ := hfold_rest
  -- ④ 判定
  rcases judge_after_fold bs (2 + ((encodeBitsSym inst.target).length : ℤ)) cfg₃ (by omega)
      hst₃ hhd₃ hmark₃ hbl₃ hreg₃ hkd₃ hfl₃ hz₃ with
    ⟨π₃, cfg₄, hs₃, hlen₃, hst₄, hhd₄, htape₄⟩
  -- ⑤ 拼接
  refine ⟨π₀ ++ π₁ ++ π₂ ++ π₃, cfg₄, ?_, hst₄, hhd₄, ?_⟩
  · have hB : SymSteps VerifierSym.transition cfg₁ π₁ cfg₂ := by
      rw [← he₁] at hs₁
      exact hs₁
    have hC : SymSteps VerifierSym.transition cfg₂ π₂ cfg₃ := by
      rw [← he₂] at hs₂
      exact hs₂
    have hBC : SymSteps VerifierSym.transition cfg₁ (π₁ ++ π₂) cfg₃ :=
      SymSteps_trans VerifierSym.transition cfg₁ cfg₂ cfg₃ π₁ π₂ hB hC
    have hBCD : SymSteps VerifierSym.transition cfg₁ (π₁ ++ π₂ ++ π₃) cfg₄ :=
      SymSteps_trans VerifierSym.transition cfg₁ cfg₃ cfg₄ (π₁ ++ π₂) π₃ hBC hs₃
    simpa [List.append_assoc] using
      SymSteps_trans VerifierSym.transition (symInitialConfig (encodeInstanceSym inst))
        cfg₁ cfg₄ π₀ (π₁ ++ π₂ ++ π₃) hs₀ hBCD
  · rw [List.length_append, List.length_append, List.length_append]
    have hZ0 : 0 ≤ foldLenB bs (2 + ((encodeBitsSym inst.target).length : ℤ)) :=
      foldLenB_nonneg bs _ (by omega)
    have hb2 : π₂.length ≤ (foldLenB bs (2 + ((encodeBitsSym inst.target).length : ℤ))).toNat := by
      rw [← Nat.cast_le (α := ℤ)]
      rw [Int.toNat_of_nonneg hZ0]
      exact hlen₂
    omega

/-! ## ⑥ 多项式收口：闭形 quadB -/

/-- [⑥ 闭形] 逐元素二次界的闭形上界。 -/
def quadB (bs : List ℕ) (p_e : ℤ) : ℤ :=
  2 * (((bs.map (fun b => b ^ 2)).sum : ℕ) : ℤ)
    + (2 * p_e + 7) * ((bs.sum : ℕ) : ℤ)
    + 2 * (((bs.map (fun b => b + 1)).sum : ℕ) : ℤ) * ((bs.sum : ℕ) : ℤ)
    + ((bs.length : ℤ)) * (4 * p_e + 13)
    + 4 * ((bs.length : ℤ)) * (((bs.map (fun b => b + 1)).sum : ℕ) : ℤ)

/-- [⑥] `foldLenB ≤ quadB`（闭形）。 -/
lemma foldLenB_le_quad (bs : List ℕ) (p_e : ℤ) : foldLenB bs p_e ≤ quadB bs p_e := by
  match bs with
  | [] => simp [quadB]
  | [b] =>
      have hb : (0 : ℤ) ≤ (b : ℤ) := Int.natCast_nonneg b
      have h2 : (0 : ℤ) ≤ (b : ℤ) ^ 2 := sq_nonneg _
      have hB : quadB [b] p_e = 2 * (b : ℤ) ^ 2 + (2 * p_e + 7) * (b : ℤ) +
          2 * ((b : ℤ) + 1) * (b : ℤ) + (4 * p_e + 13) + 4 * ((b : ℤ) + 1) := by
        unfold quadB
        push_cast
        simp
      rw [foldLenB_single, hB]
      nlinarith [hb, h2]
  | b :: c :: rest =>
      have ih := foldLenB_le_quad (c :: rest) (p_e + (b : ℤ) + 1)
      have hb : (0 : ℤ) ≤ (b : ℤ) := Int.natCast_nonneg b
      have hSr : (0 : ℤ) ≤ (((c :: rest).sum : ℕ) : ℤ) := Int.natCast_nonneg _
      have hTtr : (0 : ℤ) ≤ ((((c :: rest).map (fun b => b + 1)).sum : ℕ) : ℤ) :=
        Int.natCast_nonneg _
      have hs2r : (0 : ℤ) ≤ ((((c :: rest).map (fun b => b ^ 2)).sum : ℕ) : ℤ) :=
        Int.natCast_nonneg _
      rw [foldLenB_cons_cons]
      have step1 : (b : ℤ) * (2 * (b : ℤ) + 2 * p_e + 3) + (4 * p_e + 4 * (b : ℤ) + 13) +
            foldLenB (c :: rest) (p_e + (b : ℤ) + 1) ≤
          (b : ℤ) * (2 * (b : ℤ) + 2 * p_e + 3) + (4 * p_e + 4 * (b : ℤ) + 13) +
            quadB (c :: rest) (p_e + (b : ℤ) + 1) := by
        linarith [ih]
      have step2 : (b : ℤ) * (2 * (b : ℤ) + 2 * p_e + 3) + (4 * p_e + 4 * (b : ℤ) + 13) +
            quadB (c :: rest) (p_e + (b : ℤ) + 1) ≤ quadB (b :: c :: rest) p_e := by
        simp only [quadB, List.map_cons, List.sum_cons, List.length_cons]
        push_cast
        have hc : (0 : ℤ) ≤ (c : ℤ) := Int.natCast_nonneg c
        have hn : (0 : ℤ) ≤ ((rest.length : ℕ) : ℤ) := Int.natCast_nonneg _
        have hA1 : (0 : ℤ) ≤ (List.map Nat.cast (List.map (fun b => b ^ 2) rest)).sum := by
          apply List.sum_nonneg
          intro x hx
          rcases List.mem_map.mp hx with ⟨y, _, rfl⟩
          exact Int.natCast_nonneg _
        have hA2 : (0 : ℤ) ≤ (List.map Nat.cast rest).sum := by
          apply List.sum_nonneg
          intro x hx
          rcases List.mem_map.mp hx with ⟨y, _, rfl⟩
          exact Int.natCast_nonneg _
        have hA3 : (0 : ℤ) ≤ (List.map Nat.cast (List.map (fun b => b + 1) rest)).sum := by
          apply List.sum_nonneg
          intro x hx
          rcases List.mem_map.mp hx with ⟨y, _, rfl⟩
          exact Int.natCast_nonneg _
        have hmul : (0 : ℤ) ≤ (List.map Nat.cast (List.map (fun b => b + 1) rest)).sum * (b : ℤ) :=
          mul_nonneg hA3 hb
        have hbc : (0 : ℤ) ≤ (b : ℤ) * (c : ℤ) := mul_nonneg hb hc
        nlinarith [hb, hc, hn, hA1, hA2, hA3, hmul, hbc, sq_nonneg (b : ℤ)]
      linarith [step1, step2]

/-! ## ⑥ 主界：16·(编码长+1)² -/

/-- [⑥] 实例编码长度分解：`1 + t + 1 + E_el + 1`。 -/
lemma encodeInstanceSym_length (inst : SubsetSumInstance) :
    (encodeInstanceSym inst).length = (encodeBitsSym inst.target).length +
      (encodeElementsSym inst.elements).length + 3 := by
  simp [encodeInstanceSym]
  ring

/-- [⑥] `Σ(bᵢ+1) = Σbᵢ + 长度`。 -/
lemma sum_map_succ (l : List ℕ) : (l.map (fun b => b + 1)).sum = l.sum + l.length := by
  induction l with
  | nil => simp
  | cons b l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih]
      omega

/-- [⑥] 元素区长度 = 元素数 + Σ位长。 -/
lemma encodeElementsSym_length_gen (elems : List ℕ) :
    (encodeElementsSym elems).length = elems.length +
      (elems.map (fun v => (encodeBitsSymNative v).length)).sum := by
  induction elems with
  | nil => simp [encodeElementsSym]
  | cons v rest ih =>
      cases rest with
      | nil =>
          show ([Sym.alpha] ++ encodeBitsSymNative v).length = 1 +
            ([v].map (fun v => (encodeBitsSymNative v).length)).sum
          simp
          omega
      | cons w rest' =>
          show ([Sym.alpha] ++ encodeBitsSymNative v ++ encodeElementsSym (w :: rest')).length =
            (v :: w :: rest').length +
              ((v :: w :: rest').map (fun v => (encodeBitsSymNative v).length)).sum
          rw [List.length_append]
          rw [show (encodeElementsSym (w :: rest')).length = (w :: rest').length +
              ((w :: rest').map (fun v => (encodeBitsSymNative v).length)).sum from ih]
          simp only [List.length_append, List.length_cons, List.length_nil, List.map_cons,
            List.sum_cons]
          omega

/-- [⑥] 全 1 族元素区长度 = Σ(bᵢ+1)。 -/
lemma encodeElementsSym_worst_length (bs : List ℕ) :
    (encodeElementsSym (bs.map (fun b => 2 ^ b - 1))).length =
      (bs.map (fun b => b + 1)).sum := by
  rw [encodeElementsSym_length_gen]
  have hmap : (List.map (fun v => (encodeBitsSymNative v).length) (bs.map (fun b => 2 ^ b - 1))).sum
      = bs.sum := by
    rw [List.map_map]
    have hfun : (Function.comp (fun v => (encodeBitsSymNative v).length) (fun b => 2 ^ b - 1))
        = (fun b => b) := by
      funext b
      rw [Function.comp_apply, encodeBitsSymNative_two_pow_sub_one, List.length_replicate]
    rw [hfun]
    simp
  rw [hmap, List.length_map, sum_map_succ]
  omega

/-- [⑥] Σbᵢ² ≤ (Σbᵢ)²。 -/
lemma sum_sq_le_sq_sum (l : List ℕ) : (l.map (fun b => b ^ 2)).sum ≤ l.sum ^ 2 := by
  induction l with
  | nil => simp
  | cons b l ih =>
      simp only [List.map_cons, List.sum_cons]
      have hexp : (b + l.sum) ^ 2 = b ^ 2 + 2 * (b * l.sum) + l.sum ^ 2 := by ring
      rw [hexp]
      omega

set_option maxHeartbeats 900000 in -- 因：闭形放缩含多层乘积项，需高于默认的心跳预算
/-- [⑥ 主界] 最坏案例下 100 段路径长度 ≤ 16·(编码长+1)²。 -/
theorem main_le_quad (bs : List ℕ) (inst : SubsetSumInstance) (hw : WorstCase bs inst) :
    ∃ π cfg, SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π cfg ∧
      cfg.state = 100 ∧
      π.length ≤ 16 * ((encodeInstanceSym inst).length + 1) ^ 2 := by
  rcases phase_decomp bs inst hw with ⟨π, cfg, hs, hst, hhd, hlen⟩
  refine ⟨π, cfg, hs, hst, ?_⟩
  have hE : ((encodeInstanceSym inst).length : ℤ) =
      ((encodeBitsSym inst.target).length : ℤ) +
        ((encodeElementsSym inst.elements).length : ℤ) + 3 := by
    exact_mod_cast encodeInstanceSym_length inst
  have hEel : ((encodeElementsSym inst.elements).length : ℤ) =
      (((bs.map (fun b => b + 1)).sum : ℕ) : ℤ) := by
    rw [hw.1]
    exact_mod_cast encodeElementsSym_worst_length bs
  have hfam1 : ((famRest bs).length : ℤ) + 1 =
      (((bs.map (fun b => b + 1)).sum : ℕ) : ℤ) := by
    have h1 : (encodeElementsSymWithSel inst.elements
        (List.replicate inst.elements.length true)).length =
        (encodeElementsSym inst.elements).length :=
      WithSel_length inst.elements _ (by simp)
    have h2 : encodeElementsSymWithSel inst.elements (List.replicate inst.elements.length true)
        = Sym.sel :: famRest bs := by
      rw [show encodeElementsSymWithSel inst.elements (List.replicate inst.elements.length true)
          = encodeElementsSymWithSel (bs.map (fun b => 2 ^ b - 1)) (List.replicate bs.length true)
          from by rw [hw.1, List.length_map],
        encodeElementsSymWithSel_all1 bs hw.2.2.1]
    have h3 : (encodeElementsSym inst.elements).length = (famRest bs).length + 1 := by
      rw [← h1, h2]
      simp
    rw [show ((famRest bs).length : ℤ) + 1 = (((famRest bs).length + 1 : ℕ) : ℤ) from by push_cast; ring]
    rw [← h3, hEel]
  have hsum_succ : (((bs.map (fun b => b + 1)).sum : ℕ) : ℤ) =
      ((bs.sum : ℕ) : ℤ) + ((bs.length : ℕ) : ℤ) := by
    exact_mod_cast sum_map_succ bs
  have hE0 : (0 : ℤ) ≤ ((encodeInstanceSym inst).length : ℤ) := Int.natCast_nonneg _
  have hn0 : (0 : ℤ) ≤ ((bs.length : ℕ) : ℤ) := Int.natCast_nonneg _
  have hb0 : (0 : ℤ) ≤ ((bs.sum : ℕ) : ℤ) := Int.natCast_nonneg _
  have hTt0 : (0 : ℤ) ≤ (((bs.map (fun b => b + 1)).sum : ℕ) : ℤ) := Int.natCast_nonneg _
  have ht_le : ((encodeBitsSym inst.target).length : ℤ) ≤ ((encodeInstanceSym inst).length : ℤ) := by
    linarith [hE]
  have hEel_le : ((encodeElementsSym inst.elements).length : ℤ) ≤ ((encodeInstanceSym inst).length : ℤ) := by
    linarith [hE]
  have hsb_le : ((bs.sum : ℕ) : ℤ) ≤ ((encodeInstanceSym inst).length : ℤ) := by
    have h1 : ((bs.sum : ℕ) : ℤ) ≤ (((bs.map (fun b => b + 1)).sum : ℕ) : ℤ) := by
      rw [hsum_succ]
      linarith [hn0]
    linarith [h1, hEel.le, hE]
  have hn_le : ((bs.length : ℕ) : ℤ) ≤ ((encodeInstanceSym inst).length : ℤ) := by
    linarith [hTt0, hEel.le, hsum_succ, hn0, hE]
  have hTt : (((bs.map (fun b => b + 1)).sum : ℕ) : ℤ) = ((encodeElementsSym inst.elements).length : ℤ) := hEel.symm
  have hsq' : (((bs.map (fun b => b ^ 2)).sum : ℕ) : ℤ) ≤ ((bs.sum : ℕ) : ℤ) * ((bs.sum : ℕ) : ℤ) := by
    have hcast : (((bs.map (fun b => b ^ 2)).sum : ℕ) : ℤ) ≤ (((bs.sum ^ 2 : ℕ) : ℤ)) := by
      exact_mod_cast sum_sq_le_sq_sum bs
    rw [show (((bs.sum ^ 2 : ℕ) : ℤ)) = ((bs.sum : ℕ) : ℤ) * ((bs.sum : ℕ) : ℤ) from by push_cast; ring] at hcast
    exact hcast
  have hsq2 : (((bs.map (fun b => b ^ 2)).sum : ℕ) : ℤ) ≤
      ((encodeInstanceSym inst).length : ℤ) * ((encodeInstanceSym inst).length : ℤ) := by
    have h1 : ((bs.sum : ℕ) : ℤ) ≤ ((encodeElementsSym inst.elements).length : ℤ) := by
      rw [hEel, hsum_succ]
      linarith [hn0]
    nlinarith [hsq', h1, hb0, hEel_le]
  have hcross : (((bs.map (fun b => b + 1)).sum : ℕ) : ℤ) * ((bs.sum : ℕ) : ℤ) ≤
      ((encodeInstanceSym inst).length : ℤ) * ((encodeInstanceSym inst).length : ℤ) := by
    have h1 : ((bs.sum : ℕ) : ℤ) ≤ ((encodeInstanceSym inst).length : ℤ) := by
      have h1' : ((bs.sum : ℕ) : ℤ) ≤ (((bs.map (fun b => b + 1)).sum : ℕ) : ℤ) := by
        rw [hsum_succ]
        linarith [hn0]
      linarith [h1', hEel.le, hE]
    have h3 : (((bs.map (fun b => b + 1)).sum : ℕ) : ℤ) ≤ ((encodeInstanceSym inst).length : ℤ) := by
      rw [hTt]
      exact hEel_le
    nlinarith [h1, hb0, h3, hn0, hEel_le]
  have hnTt : ((bs.length : ℕ) : ℤ) * (((bs.map (fun b => b + 1)).sum : ℕ) : ℤ) ≤
      ((encodeInstanceSym inst).length : ℤ) * ((encodeInstanceSym inst).length : ℤ) := by
    have h3 : (((bs.map (fun b => b + 1)).sum : ℕ) : ℤ) ≤ ((encodeInstanceSym inst).length : ℤ) := by
      rw [hTt]
      exact hEel_le
    nlinarith [hn_le, hTt0, h3, hEel_le]
  have hfold := foldLenB_le_quad bs (2 + ((encodeBitsSym inst.target).length : ℤ))
  have hfnn : (0 : ℤ) ≤ foldLenB bs (2 + ((encodeBitsSym inst.target).length : ℤ)) :=
    foldLenB_nonneg bs _ (by omega)
  have ht2nn : (0 : ℤ) ≤ 2 + ((encodeBitsSym inst.target).length : ℤ) + ((famRest bs).length : ℤ) := by
    have h1 : (0 : ℤ) ≤ ((encodeBitsSym inst.target).length : ℤ) := Int.natCast_nonneg _
    have h2 : (0 : ℤ) ≤ ((famRest bs).length : ℤ) := Int.natCast_nonneg _
    linarith
  rw [← Nat.cast_le (α := ℤ)]
  have hlenZ : (π.length : ℤ) ≤
      ((encodeInstanceSym inst).length : ℤ) + 3 +
        2 * (3 + ((encodeBitsSym inst.target).length : ℤ) +
          ((encodeElementsSym inst.elements).length : ℤ)) +
        foldLenB bs (2 + ((encodeBitsSym inst.target).length : ℤ)) +
        ((2 + ((encodeBitsSym inst.target).length : ℤ)) + ((famRest bs).length : ℤ)) + 2 := by
    have h3 : (π.length : ℤ) ≤ (((encodeInstanceSym inst).length + 3 +
        2 * (3 + (encodeBitsSym inst.target).length + (encodeElementsSym inst.elements).length) +
        (foldLenB bs (2 + ((encodeBitsSym inst.target).length : ℤ))).toNat +
        (((2 + ((encodeBitsSym inst.target).length : ℤ)) + ((famRest bs).length : ℤ)).toNat + 2) : ℕ) : ℤ) := by
      exact_mod_cast hlen
    have h4 : (((foldLenB bs (2 + ((encodeBitsSym inst.target).length : ℤ))).toNat : ℤ)) ≤
        foldLenB bs (2 + ((encodeBitsSym inst.target).length : ℤ)) := by
      rw [Int.toNat_of_nonneg hfnn]
    have h5 : (((((2 + ((encodeBitsSym inst.target).length : ℤ)) + ((famRest bs).length : ℤ)).toNat) : ℤ)) ≤
        (2 + ((encodeBitsSym inst.target).length : ℤ)) + ((famRest bs).length : ℤ) := by
      rw [Int.toNat_of_nonneg ht2nn]
    have h7 : (((encodeInstanceSym inst).length + 3 +
        2 * (3 + (encodeBitsSym inst.target).length + (encodeElementsSym inst.elements).length) +
        (foldLenB bs (2 + ((encodeBitsSym inst.target).length : ℤ))).toNat +
        (((2 + ((encodeBitsSym inst.target).length : ℤ)) + ((famRest bs).length : ℤ)).toNat + 2) : ℕ) : ℤ) =
        ((encodeInstanceSym inst).length : ℤ) + 3 +
          2 * (3 + ((encodeBitsSym inst.target).length : ℤ) +
            ((encodeElementsSym inst.elements).length : ℤ)) +
          ((foldLenB bs (2 + ((encodeBitsSym inst.target).length : ℤ))).toNat : ℤ) +
          ((((2 + ((encodeBitsSym inst.target).length : ℤ)) + ((famRest bs).length : ℤ)).toNat : ℤ) + 2) := by
      push_cast
      ring
    rw [h7] at h3
    omega
  have hquad : foldLenB bs (2 + ((encodeBitsSym inst.target).length : ℤ)) ≤
      14 * ((encodeInstanceSym inst).length : ℤ) * ((encodeInstanceSym inst).length : ℤ) +
        32 * ((encodeInstanceSym inst).length : ℤ) := by
    have hquad_exp : quadB bs (2 + ((encodeBitsSym inst.target).length : ℤ)) =
        2 * (((bs.map (fun b => b ^ 2)).sum : ℕ) : ℤ) +
          (2 * (2 + ((encodeBitsSym inst.target).length : ℤ)) + 7) * ((bs.sum : ℕ) : ℤ) +
          2 * (((bs.map (fun b => b + 1)).sum : ℕ) : ℤ) * ((bs.sum : ℕ) : ℤ) +
          ((bs.length : ℤ)) * (4 * (2 + ((encodeBitsSym inst.target).length : ℤ)) + 13) +
          4 * ((bs.length : ℤ)) * (((bs.map (fun b => b + 1)).sum : ℕ) : ℤ) := rfl
    rw [hquad_exp] at hfold
    have hp1 : (2 * (2 + ((encodeBitsSym inst.target).length : ℤ)) + 7) * ((bs.sum : ℕ) : ℤ) ≤
        (2 * ((encodeInstanceSym inst).length : ℤ) + 7) * ((encodeInstanceSym inst).length : ℤ) := by
      have h1 : 2 * (2 + ((encodeBitsSym inst.target).length : ℤ)) + 7 ≤
          2 * ((encodeInstanceSym inst).length : ℤ) + 7 := by linarith [ht_le]
      have hA := mul_le_mul_of_nonneg_right h1 hb0
      have hB := mul_le_mul_of_nonneg_left hsb_le (by linarith [hE0] : (0 : ℤ) ≤ 2 * ((encodeInstanceSym inst).length : ℤ) + 7)
      linarith [hA, hB]
    have hp2 : ((bs.length : ℤ)) * (4 * (2 + ((encodeBitsSym inst.target).length : ℤ)) + 13) ≤
        ((encodeInstanceSym inst).length : ℤ) * (4 * ((encodeInstanceSym inst).length : ℤ) + 13) := by
      have h1 : 4 * (2 + ((encodeBitsSym inst.target).length : ℤ)) + 13 ≤
          4 * ((encodeInstanceSym inst).length : ℤ) + 13 := by linarith [ht_le]
      have hA := mul_le_mul_of_nonneg_right h1 hn0
      have hB := mul_le_mul_of_nonneg_right hn_le (by linarith [hE0] : (0 : ℤ) ≤ 4 * ((encodeInstanceSym inst).length : ℤ) + 13)
      linarith [hA, hB]
    nlinarith [hfold, hp1, hp2, hsq2, hcross, hnTt, hb0, hn0, hTt0, hE, ht_le, hEel_le, hn_le,
      sq_nonneg ((encodeInstanceSym inst).length : ℤ)]
  have hT_le : ((famRest bs).length : ℤ) ≤ ((encodeInstanceSym inst).length : ℤ) := by
    linarith [hfam1, hEel.le, hE]
  have hfinal : (π.length : ℤ) ≤
      16 * (((encodeInstanceSym inst).length : ℤ) + 1) * (((encodeInstanceSym inst).length : ℤ) + 1) := by
    have hTt_le : (((bs.map (fun b => b + 1)).sum : ℕ) : ℤ) ≤ ((encodeInstanceSym inst).length : ℤ) := by
      rw [hTt]
      exact hEel_le
    nlinarith [hlenZ, hquad, hE, ht_le, hEel_le, hT_le, hTt_le, hE0]
  rw [show (((16 * ((encodeInstanceSym inst).length + 1) ^ 2 : ℕ) : ℤ)) =
      16 * (((encodeInstanceSym inst).length : ℤ) + 1) * (((encodeInstanceSym inst).length : ℤ) + 1) from by
    push_cast
    ring]
  exact hfinal

/-! ## ⑥ 终形包装：Sym 级与 F4/|x| 级 -/

/-- [⑥ 终形 · Sym 级] 最坏案例下存在达 100 的路径，长度 ≤ 16·(m+1)·(E+1)²（m = 标记读口径松弛）。 -/
theorem main_sym (bs : List ℕ) (inst : SubsetSumInstance) (hw : WorstCase bs inst) (m : ℕ) :
    ∃ K π cfg, SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π cfg ∧
      cfg.state = 100 ∧
      π.length ≤ K * (m + 1) * ((encodeInstanceSym inst).length + 1) ^ 2 := by
  rcases main_le_quad bs inst hw with ⟨π, cfg, hs, hst, hlen⟩
  refine ⟨16, π, cfg, hs, hst, ?_⟩
  have h1 : (0 : ℕ) < m + 1 := Nat.succ_pos m
  calc π.length ≤ 16 * ((encodeInstanceSym inst).length + 1) ^ 2 := hlen
    _ ≤ 16 * (m + 1) * ((encodeInstanceSym inst).length + 1) ^ 2 := by
        have h2 : 1 ≤ m + 1 := h1
        have h3 : 16 * ((encodeInstanceSym inst).length + 1) ^ 2 ≤
            16 * (m + 1) * ((encodeInstanceSym inst).length + 1) ^ 2 := by
          nlinarith [h2, Nat.zero_le ((encodeInstanceSym inst).length + 1),
            Nat.zero_le (m + 1),
            sq_nonneg (((encodeInstanceSym inst).length : ℤ) + 1)]
        exact h3

/-- [⑥ 终形 · F4/|x| 级] x = encodeInstanceF4 inst ++ flat4F4 gS 下，长度 ≤ 16·(m+1)·(|x|+1)²。 -/
theorem main_f4 (bs : List ℕ) (inst : SubsetSumInstance) (gS : List Sym) (hw : WorstCase bs inst)
    (m : ℕ) :
    ∃ K π cfg, SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π cfg ∧
      cfg.state = 100 ∧
      π.length ≤ K * (m + 1) * ((encodeInstanceF4 inst ++ flat4F4 gS).length + 1) ^ 2 := by
  rcases main_le_quad bs inst hw with ⟨π, cfg, hs, hst, hlen⟩
  refine ⟨16, π, cfg, hs, hst, ?_⟩
  -- |x| = 4E + 4|gS| ≥ 4E ⟹ E + 1 ≤ |x| + 1
  have hxlen : (encodeInstanceF4 inst ++ flat4F4 gS).length =
      4 * (encodeInstanceSym inst).length + 4 * gS.length := by
    rw [List.length_append, flat4F4_length, encodeInstanceF4, flat4F4_length]
  have hE_le : (encodeInstanceSym inst).length ≤ (encodeInstanceF4 inst ++ flat4F4 gS).length := by
    rw [hxlen]
    omega
  have hsq : ((encodeInstanceSym inst).length + 1) ^ 2 ≤
      ((encodeInstanceF4 inst ++ flat4F4 gS).length + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have h1 : (0 : ℕ) < m + 1 := Nat.succ_pos m
  calc π.length ≤ 16 * ((encodeInstanceSym inst).length + 1) ^ 2 := hlen
    _ ≤ 16 * ((encodeInstanceF4 inst ++ flat4F4 gS).length + 1) ^ 2 :=
        Nat.mul_le_mul_left 16 hsq
    _ ≤ 16 * (m + 1) * ((encodeInstanceF4 inst ++ flat4F4 gS).length + 1) ^ 2 := by
        have h2 : 1 ≤ m + 1 := h1
        nlinarith [h2, Nat.zero_le ((encodeInstanceF4 inst ++ flat4F4 gS).length + 1),
          Nat.zero_le (m + 1)]


/-! ========== T-P4.2 移植（线2 探针，15:50 吸收包；逐字复制） ========== -/

/-- [链①] `valSum bs < 2^{Σb}`（bs 任意，含 0 位与空表）。 -/
lemma valSum_lt_pow_sum (bs : List ℕ) : valSum bs < (2 : ℤ) ^ bs.sum := by
  induction bs with
  | nil => simp [valSum]
  | cons b rest ih =>
      rw [valSum_cons, List.sum_cons]
      have hkey : (2 : ℤ) ^ b - 1 + 2 ^ (rest.sum) ≤ (2 : ℤ) ^ b * 2 ^ (rest.sum) := by
        have h1 : (0 : ℤ) ≤ (2 : ℤ) ^ b - 1 := by
          have h : (1 : ℤ) ≤ (2 : ℤ) ^ b := one_le_pow₀ (by norm_num)
          omega
        have h2 : (0 : ℤ) ≤ (2 : ℤ) ^ (rest.sum) - 1 := by
          have h : (1 : ℤ) ≤ (2 : ℤ) ^ (rest.sum) := one_le_pow₀ (by norm_num)
          omega
        nlinarith [mul_nonneg h1 h2]
      calc (2 : ℤ) ^ b - 1 + valSum rest
          < (2 : ℤ) ^ b - 1 + 2 ^ (rest.sum) := by linarith
        _ ≤ (2 : ℤ) ^ b * 2 ^ (rest.sum) := hkey
        _ = (2 : ℤ) ^ (b + rest.sum) := by rw [← pow_add]

/-- [链②] `bitWidth (valSum bs).toNat ≤ Σb`（无需正性前提——0 位/空表走零支）。 -/
lemma bitWidth_valSum_le_sum (bs : List ℕ) :
    bitWidth ((valSum bs).toNat) ≤ bs.sum := by
  set t := (valSum bs).toNat with ht
  have hlt : t < 2 ^ bs.sum := by
    have hcast : ((t : ℤ)) = valSum bs := Int.toNat_of_nonneg (valSum_nonneg bs)
    have h : ((t : ℤ)) < ((2 ^ bs.sum : ℕ) : ℤ) := by
      rw [hcast]
      push_cast
      exact valSum_lt_pow_sum bs
    exact_mod_cast h
  rcases Nat.eq_zero_or_pos t with h0 | hpos
  · rw [h0]
    simp [bitWidth]
  · have hlen : (Nat.digits 2 t).length ≤ bs.sum := by
      rw [Nat.length_digits 2 t (by norm_num) (by omega)]
      have hlog : Nat.log 2 t < bs.sum := by
        by_contra hcon
        push Not at hcon
        have hle := (Nat.le_log_iff_pow_le (by norm_num) (by omega : t ≠ 0)).mp hcon
        omega
      omega
    simpa [bitWidth] using hlen

/-- [链③] 主件：族实例编码长 ≤ 2·原实例编码长。 -/
lemma fam_enc_le_two (bs : List ℕ) (inst : SubsetSumInstance)
    (hbs : inst.elements.map bitWidth = bs) :
    (encodeInstanceSym ⟨bs.map (fun b => 2 ^ b - 1), (valSum bs).toNat⟩).length ≤
      2 * (encodeInstanceSym inst).length := by
  have hbitsfam : (encodeBitsSym ((valSum bs).toNat)).length ≤ bs.sum := by
    have heq : (encodeBitsSym ((valSum bs).toNat)).length = bitWidth ((valSum bs).toNat) := by
      simp [encodeBitsSym, bitWidth]
    rw [heq]
    exact bitWidth_valSum_le_sum bs
  have hfam : (encodeInstanceSym ⟨bs.map (fun b => 2 ^ b - 1), (valSum bs).toNat⟩).length =
      (encodeBitsSym ((valSum bs).toNat)).length + (bs.map (fun b => b + 1)).sum + 3 := by
    rw [encodeInstanceSym_length, encodeElementsSym_worst_length]
  have hsum : (inst.elements.map (fun v => (encodeBitsSymNative v).length)).sum = bs.sum := by
    have hmap : inst.elements.map (fun v => (encodeBitsSymNative v).length) =
        inst.elements.map bitWidth := by
      apply List.map_congr_left
      intro v hv
      simp [encodeBitsSymNative, bitWidth]
    rw [hmap, hbs]
  have hlen : bs.length = inst.elements.length := by
    rw [← hbs, List.length_map]
  have hinst : (encodeInstanceSym inst).length =
      (encodeBitsSym inst.target).length + bs.sum + inst.elements.length + 3 := by
    rw [encodeInstanceSym_length, encodeElementsSym_length_gen, hsum]
    omega
  calc (encodeInstanceSym ⟨bs.map (fun b => 2 ^ b - 1), (valSum bs).toNat⟩).length
      = (encodeBitsSym ((valSum bs).toNat)).length + (bs.map (fun b => b + 1)).sum + 3 := hfam
    _ ≤ bs.sum + (bs.sum + bs.length) + 3 := by
        rw [sum_map_succ]
        omega
    _ ≤ 2 * ((encodeBitsSym inst.target).length + bs.sum + inst.elements.length + 3) := by omega
    _ = 2 * (encodeInstanceSym inst).length := by rw [hinst]

/-
  ==============================================================================
  [T-Q2① · C3-κ 前置] 通用首达截断（G6）：截断保前缀长
  ------------------------------------------------------------------------------
  · `truncate_keeps_prefix`（移植落点：R15，2026-09-13）：π 段各步均不从接受态出发
    ⇒ `π.length ≤ 首达截断路径长`；截断产物各步来态 ∉ 接受态 —— 即 C-5 接口
    `hclean`（`A1StepBoundBridge`）的直供形状。
  · 消费：`first_accept_step_split`（A2Bridge:471）；缝探针 `_probe_q2.lean`
    （截断 → hclean → δ-16b 装配；gS=[] 形；一般 gS 形 = G7 参数化另行）。
  ==============================================================================
-/

/-- [T-Q2 · G6 · 首达截断保前缀长] 若 π 段各步均不从接受态出发，则 π.length ≤ 首达截断路径长；
    截断路径各步来态均 ∉ 接受态（= C-5 `hclean` 形状，待装配端直供）。 -/
lemma truncate_keeps_prefix {M : CBTM} {x : List F4} {π π₂ : ComputationPath} {cfg₂ : CBTMConfig M x}
    (h : TapeReachablePath M x (π ++ π₂) cfg₂) (hacc : cfg₂.state ∈ M.acceptStates)
    (hno : ∀ step ∈ π, step.fromState ∉ M.acceptStates) :
    ∃ πt cfgT, TapeReachablePath M x πt cfgT ∧ cfgT.state ∈ M.acceptStates ∧
      (∀ s ∈ πt, s.fromState ∉ M.acceptStates) ∧ π.length ≤ πt.length := by
  rcases first_accept_step_split M x h with hclean | ⟨π₀, step, π₁, hsplit, hacc_st, hclean₀, c₀, hc₀, hstate₀⟩
  · exact ⟨π ++ π₂, cfg₂, h, hacc, hclean,
      by simpa [List.length_append] using Nat.le_add_right π.length π₂.length⟩
  · refine ⟨π₀, c₀, hc₀, ?_, hclean₀, ?_⟩
    · simpa [hstate₀] using hacc_st
    · by_contra hlt
      have hlt : π₀.length < π.length := not_le.mp hlt
      have htake1 : (π ++ π₂).take π.length = π := by
        rw [List.take_append, List.take_of_length_le le_rfl]
        simp
      have htake2 : (π₀ ++ step :: π₁).take π.length =
          π₀ ++ (step :: π₁).take (π.length - π₀.length) := by
        rw [List.take_append, List.take_of_length_le (Nat.le_of_lt hlt)]
      have hdecomp : π = π₀ ++ (step :: π₁).take (π.length - π₀.length) := by
        conv_lhs => rw [← htake1]
        rw [hsplit]
        exact htake2
      obtain ⟨j, hj⟩ : ∃ j, π.length - π₀.length = j + 1 :=
        ⟨π.length - π₀.length - 1, by omega⟩
      have hmem : step ∈ π := by
        rw [hdecomp, hj, List.take_succ_cons]
        simp
      exact hno step hmem hacc_st

/-! ========== T-Q1（线2 移植 · 2026-09-13）：worst 族 ⇒ 位段全1 ⇒ 带面全 data1（装配七件） ========== -/

/-- [Q1-1 · 位段全1] worst 元素位段：`bitsOf (2^b − 1) = replicate b true`（全1位列表）。 -/
lemma bitsOf_two_pow_sub_one (b : ℕ) :
    bitsOf (2 ^ b - 1) = List.replicate b true := by
  rw [bitsOf, encodeBitsSym_two_pow_sub_one b, ← bitsToSym_replicate_true b,
    symToBits_bitsToSym]

/-- [Q1-2 · 全1 ⇒ 全 data1] 位段全1的编码面：`bitsToSym (bitsOf (2^b−1)) = replicate b data1`。 -/
lemma bitsToSym_bitsOf_two_pow_sub_one (b : ℕ) :
    bitsToSym (bitsOf (2 ^ b - 1)) = List.replicate b Sym.data1 := by
  rw [bitsOf_two_pow_sub_one b, bitsToSym_replicate_true b]

/-- [Q1-3 · 带面] 折叠输入面（bitsOf 形）⇒ 全 data1 符号面。 -/
lemma worst_face_all_data1 (b : ℕ) (tape : ℤ → Sym) (base : ℤ)
    (h : tapeAgrees tape base (bitsToSym (bitsOf (2 ^ b - 1)))) :
    tapeAgrees tape base (List.replicate b Sym.data1) := by
  rwa [bitsToSym_bitsOf_two_pow_sub_one b] at h

/-- [Q1-4 · kind 面] 全 data1 符号面 ⇒ 逐格 kind = data1。 -/
lemma worst_face_all_data1_kind (b : ℕ) (tape : ℤ → Sym) (base : ℤ)
    (hface : tapeAgrees tape base (List.replicate b Sym.data1)) :
    ∀ i : ℕ, i < b → (tape (base + (i : ℤ))).1 = SymKind.data1 := by
  intro i hi
  have hi' : i < (List.replicate b Sym.data1).length := by simpa using hi
  have hh := hface i hi'
  have hrep : (List.replicate b Sym.data1)[i]'hi' = Sym.data1 :=
    (List.mem_replicate.mp (List.getElem_mem hi')).2
  rw [hh, hrep]
  rfl

/-- [Q1-5 · getD 形] `segSrSel_gen` hbits 直喂：`(bitsOf (2^b−1)).getD (i−1) false = true`。 -/
lemma worst_hbits_getD (b : ℕ) :
    ∀ i : ℕ, 1 ≤ i → i < b + 1 → (bitsOf (2 ^ b - 1)).getD (i - 1) false = true := by
  intro i hi1 hi2
  rw [bitsOf_two_pow_sub_one b]
  have hk : i - 1 < b := by omega
  have hrep : (List.replicate b true)[i - 1]'(by simpa using hk) = true :=
    (List.mem_replicate.mp (List.getElem_mem (by simpa using hk))).2
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hk), hrep]
  rfl

/-- [Q1-6 · 命名件 · P2 接口候选] worst ⇒ 位段全1 ⇒ 带面全 data1（合并）。 -/
lemma worst_imp_all_ones (b : ℕ) (tape : ℤ → Sym) (base : ℤ)
    (h : tapeAgrees tape base (bitsToSym (bitsOf (2 ^ b - 1)))) :
    tapeAgrees tape base (List.replicate b Sym.data1) ∧
    (∀ i : ℕ, i < b → (tape (base + (i : ℤ))).1 = SymKind.data1) :=
  ⟨worst_face_all_data1 b tape base h,
   worst_face_all_data1_kind b tape base (worst_face_all_data1 b tape base h)⟩

/-- [Q1-7 · 族级] worst 族 ⇒ 每元素位段全1（消费 `WorstCase`）。 -/
lemma worst_imp_all_ones_fam (bs : List ℕ) (inst : SubsetSumInstance)
    (hw : WorstCase bs inst) :
    ∀ v ∈ inst.elements, ∃ b, v = 2 ^ b - 1 ∧ bitsOf v = List.replicate b true := by
  intro v hv
  rw [hw.1] at hv
  rcases List.mem_map.mp hv with ⟨b, _, rfl⟩
  exact ⟨b, rfl, bitsOf_two_pow_sub_one b⟩


set_option maxHeartbeats 900000 in -- 因：quadB 收口 + 全段算术需高预算
/-- [B1 · T-P2.5] 全段界合成（一般实例）：①定长 + ②ρ界 + ③④合成界
    ⟹ `π.length ≤ 16·(m+1)·(E+1)²`（折段经 `quadB` 闭形 + 编码长度恒等式；镜像 `main_le_quad` 收口链）。 -/
theorem run_total_le {inst : SubsetSumInstance} {π π₀ ρ π₁ : List SymStep}
    {step₃ : SymStep} {sel : List Bool} (m : ℕ)
    (hsel_len : sel.length = inst.elements.length)
    (hsplit : π = π₀ ++ step₃ :: (ρ ++ π₁))
    (h₀ : (π₀.length : ℤ) = 2 + ((encodeBitsSym inst.target).length : ℤ) +
        ((encodeElementsSym inst.elements).length : ℤ))
    (hρ : (ρ.length : ℤ) ≤ 2 * (3 + (encodeBitsSym inst.target).length +
        (encodeElementsSym inst.elements).length))
    (h₁ : (π₁.length : ℤ) ≤
      foldLenB (inst.elements.map (fun v => (bitsOf v).length))
          (2 + ((encodeBitsSym inst.target).length : ℤ)) +
        (2 + ((encodeBitsSym inst.target).length : ℤ) +
          ((encodeElementsSymWithSel inst.elements sel).length : ℤ) + 1)) :
    π.length ≤ 16 * (m + 1) * ((encodeInstanceSym inst).length + 1) ^ 2 := by
  have hsum := phases_len_le hsplit h₀ hρ h₁
  -- 基本恒等式
  have hE : ((encodeInstanceSym inst).length : ℤ) =
      ((encodeBitsSym inst.target).length : ℤ) +
        ((encodeElementsSym inst.elements).length : ℤ) + 3 := by
    exact_mod_cast encodeInstanceSym_length inst
  have hW : ((encodeElementsSymWithSel inst.elements sel).length : ℤ) =
      ((encodeElementsSym inst.elements).length : ℤ) := by
    exact_mod_cast WithSel_length inst.elements sel hsel_len
  have hEelKey : ∀ (l : List ℕ),
      (encodeElementsSym l).length =
        ((l.map (fun v => (bitsOf v).length)).map (fun b => b + 1)).sum := by
    intro l
    rw [encodeElementsSym_length_gen]
    induction l with
    | nil => simp
    | cons v rest ih =>
        have hnat : (encodeBitsSymNative v).length = (bitsOf v).length := by
          rw [encNative_eq_bitsToSym_bitsOf v]
          simp [bitsToSym]
        simp only [List.length_cons, List.map_cons, List.sum_cons] at ih ⊢
        rw [hnat]
        omega
  -- 记号：bs = 位长表
  set bs : List ℕ := inst.elements.map (fun v => (bitsOf v).length) with hbs
  have hEel : ((encodeElementsSym inst.elements).length : ℤ) =
      ((bs.map (fun b => b + 1)).sum : ℕ) := by
    rw [hbs]
    exact_mod_cast hEelKey inst.elements
  have hTt : (((bs.map (fun b => b + 1)).sum : ℕ) : ℤ) =
      ((encodeElementsSym inst.elements).length : ℤ) := hEel.symm
  -- 非负/基础界
  have hE0 : (0 : ℤ) ≤ ((encodeInstanceSym inst).length : ℤ) := Int.natCast_nonneg _
  have hn0 : (0 : ℤ) ≤ ((bs.length : ℕ) : ℤ) := Int.natCast_nonneg _
  have hb0 : (0 : ℤ) ≤ ((bs.sum : ℕ) : ℤ) := Int.natCast_nonneg _
  have hTt0 : (0 : ℤ) ≤ (((bs.map (fun b => b + 1)).sum : ℕ) : ℤ) :=
    Int.natCast_nonneg _
  have ht_le : ((encodeBitsSym inst.target).length : ℤ) ≤
      ((encodeInstanceSym inst).length : ℤ) := by linarith [hE]
  have hEel_le : ((encodeElementsSym inst.elements).length : ℤ) ≤
      ((encodeInstanceSym inst).length : ℤ) := by linarith [hE]
  have hsum_succ : (((bs.map (fun b => b + 1)).sum : ℕ) : ℤ) =
      ((bs.sum : ℕ) : ℤ) + ((bs.length : ℕ) : ℤ) := by
    exact_mod_cast sum_map_succ bs
  have hsb_le : ((bs.sum : ℕ) : ℤ) ≤ ((encodeInstanceSym inst).length : ℤ) := by
    have h1 : ((bs.sum : ℕ) : ℤ) ≤ (((bs.map (fun b => b + 1)).sum : ℕ) : ℤ) := by
      rw [hsum_succ]
      linarith [hn0]
    linarith [h1, hEel.le, hE]
  have hn_le : ((bs.length : ℕ) : ℤ) ≤ ((encodeInstanceSym inst).length : ℤ) := by
    linarith [hTt0, hEel.le, hsum_succ, hn0, hE]
  have hsq' : (((bs.map (fun b => b ^ 2)).sum : ℕ) : ℤ) ≤
      ((bs.sum : ℕ) : ℤ) * ((bs.sum : ℕ) : ℤ) := by
    have hcast : (((bs.map (fun b => b ^ 2)).sum : ℕ) : ℤ) ≤
        (((bs.sum ^ 2 : ℕ) : ℤ)) := by
      exact_mod_cast sum_sq_le_sq_sum bs
    rw [show (((bs.sum ^ 2 : ℕ) : ℤ)) =
        ((bs.sum : ℕ) : ℤ) * ((bs.sum : ℕ) : ℤ) from by push_cast; ring] at hcast
    exact hcast
  have hsq2 : (((bs.map (fun b => b ^ 2)).sum : ℕ) : ℤ) ≤
      ((encodeInstanceSym inst).length : ℤ) *
        ((encodeInstanceSym inst).length : ℤ) := by
    nlinarith [hsq', hsb_le, hb0, hE0]
  have hcross : (((bs.map (fun b => b + 1)).sum : ℕ) : ℤ) * ((bs.sum : ℕ) : ℤ) ≤
      ((encodeInstanceSym inst).length : ℤ) *
        ((encodeInstanceSym inst).length : ℤ) := by
    have h3 : (((bs.map (fun b => b + 1)).sum : ℕ) : ℤ) ≤
        ((encodeInstanceSym inst).length : ℤ) := by
      rw [hTt]
      exact hEel_le
    nlinarith [hsb_le, hb0, h3, hTt0, hEel_le]
  have hnTt : ((bs.length : ℕ) : ℤ) *
      (((bs.map (fun b => b + 1)).sum : ℕ) : ℤ) ≤
      ((encodeInstanceSym inst).length : ℤ) *
        ((encodeInstanceSym inst).length : ℤ) := by
    have h3 : (((bs.map (fun b => b + 1)).sum : ℕ) : ℤ) ≤
        ((encodeInstanceSym inst).length : ℤ) := by
      rw [hTt]
      exact hEel_le
    nlinarith [hn_le, hTt0, h3, hEel_le]
  -- quadB 收口（一般版）
  have hfold := foldLenB_le_quad bs (2 + ((encodeBitsSym inst.target).length : ℤ))
  have hquad_exp : quadB bs (2 + ((encodeBitsSym inst.target).length : ℤ)) =
      2 * (((bs.map (fun b => b ^ 2)).sum : ℕ) : ℤ) +
        (2 * (2 + ((encodeBitsSym inst.target).length : ℤ)) + 7) * ((bs.sum : ℕ) : ℤ) +
        2 * (((bs.map (fun b => b + 1)).sum : ℕ) : ℤ) * ((bs.sum : ℕ) : ℤ) +
        ((bs.length : ℤ)) * (4 * (2 + ((encodeBitsSym inst.target).length : ℤ)) + 13) +
        4 * ((bs.length : ℤ)) * (((bs.map (fun b => b + 1)).sum : ℕ) : ℤ) := rfl
  rw [hquad_exp] at hfold
  have hp1 : (2 * (2 + ((encodeBitsSym inst.target).length : ℤ)) + 7) * ((bs.sum : ℕ) : ℤ) ≤
      (2 * ((encodeInstanceSym inst).length : ℤ) + 7) *
        ((encodeInstanceSym inst).length : ℤ) := by
    have h1 : 2 * (2 + ((encodeBitsSym inst.target).length : ℤ)) + 7 ≤
        2 * ((encodeInstanceSym inst).length : ℤ) + 7 := by linarith [ht_le]
    have hA := mul_le_mul_of_nonneg_right h1 hb0
    have hB := mul_le_mul_of_nonneg_left hsb_le
      (by linarith [hE0] : (0 : ℤ) ≤ 2 * ((encodeInstanceSym inst).length : ℤ) + 7)
    linarith [hA, hB]
  have hp2 : ((bs.length : ℤ)) * (4 * (2 + ((encodeBitsSym inst.target).length : ℤ)) + 13) ≤
      ((encodeInstanceSym inst).length : ℤ) * (4 * ((encodeInstanceSym inst).length : ℤ) + 13) := by
    have h1 : 4 * (2 + ((encodeBitsSym inst.target).length : ℤ)) + 13 ≤
        4 * ((encodeInstanceSym inst).length : ℤ) + 13 := by linarith [ht_le]
    have hA := mul_le_mul_of_nonneg_right h1 hn0
    have hB := mul_le_mul_of_nonneg_right hn_le
      (by linarith [hE0] : (0 : ℤ) ≤ 4 * ((encodeInstanceSym inst).length : ℤ) + 13)
    linarith [hA, hB]
  have hquad : foldLenB bs (2 + ((encodeBitsSym inst.target).length : ℤ)) ≤
      14 * ((encodeInstanceSym inst).length : ℤ) *
        ((encodeInstanceSym inst).length : ℤ) +
        32 * ((encodeInstanceSym inst).length : ℤ) := by
    nlinarith [hfold, hp1, hp2, hsq2, hcross, hnTt, hb0, hn0, hTt0, hE, ht_le, hEel_le, hn_le,
      sq_nonneg ((encodeInstanceSym inst).length : ℤ)]
  -- 收口
  have hfinal : (π.length : ℤ) ≤
      16 * ((m : ℤ) + 1) * (((encodeInstanceSym inst).length : ℤ) + 1) ^ 2 := by
    have hm0 : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
    nlinarith [hsum, hquad, hE, hW, ht_le, hEel_le, hE0, hm0,
      sq_nonneg (((encodeInstanceSym inst).length : ℤ) + 1)]
  rw [← Nat.cast_le (α := ℤ)]
  rw [show ((16 * (m + 1) * ((encodeInstanceSym inst).length + 1) ^ 2 : ℕ) : ℤ) =
      16 * ((m : ℤ) + 1) * (((encodeInstanceSym inst).length : ℤ) + 1) ^ 2 from by
    push_cast
    ring]
  exact hfinal


/-- [B2 · T-P5.1] F4/|x| 形收口：`π.length ≤ 16·(m+1)·(|x|+1)²`（`x = encF4 inst ++ flat4F4 gS`）。
    （镜像 `main_f4` 桥：`4·|encS| + 4·|gS| = |x|` ⟹ `E ≤ |x|`） -/
theorem run_total_le_f4 {inst : SubsetSumInstance} {π π₀ ρ π₁ : List SymStep}
    {step₃ : SymStep} {sel : List Bool} (gS : List Sym) (m : ℕ)
    (hsel_len : sel.length = inst.elements.length)
    (hsplit : π = π₀ ++ step₃ :: (ρ ++ π₁))
    (h₀ : (π₀.length : ℤ) = 2 + ((encodeBitsSym inst.target).length : ℤ) +
        ((encodeElementsSym inst.elements).length : ℤ))
    (hρ : (ρ.length : ℤ) ≤ 2 * (3 + (encodeBitsSym inst.target).length +
        (encodeElementsSym inst.elements).length))
    (h₁ : (π₁.length : ℤ) ≤
      foldLenB (inst.elements.map (fun v => (bitsOf v).length))
          (2 + ((encodeBitsSym inst.target).length : ℤ)) +
        (2 + ((encodeBitsSym inst.target).length : ℤ) +
          ((encodeElementsSymWithSel inst.elements sel).length : ℤ) + 1)) :
    π.length ≤ 16 * (m + 1) * ((encodeInstanceF4 inst ++ flat4F4 gS).length + 1) ^ 2 := by
  have hxlen : (encodeInstanceF4 inst ++ flat4F4 gS).length =
      4 * (encodeInstanceSym inst).length + 4 * gS.length := by
    rw [List.length_append, flat4F4_length, encodeInstanceF4, flat4F4_length]
  have hE_le : (encodeInstanceSym inst).length ≤ (encodeInstanceF4 inst ++ flat4F4 gS).length := by
    rw [hxlen]
    omega
  have h16 := run_total_le (inst := inst) (π := π) (π₀ := π₀)
    (ρ := ρ) (π₁ := π₁) (step₃ := step₃) (sel := sel) m
    hsel_len hsplit h₀ hρ h₁
  calc π.length ≤ 16 * (m + 1) * ((encodeInstanceSym inst).length + 1) ^ 2 := h16
    _ ≤ 16 * (m + 1) * ((encodeInstanceF4 inst ++ flat4F4 gS).length + 1) ^ 2 :=
        Nat.mul_le_mul_left (16 * (m + 1)) (Nat.pow_le_pow_left (by omega) 2)

-- ============================================================================
-- [A5 · ② hconf 拼接] 免费域（接受侧）→ hconf 供给：
--   接受运行的每真前缀头位（= 位移和）< |encS| —— 由 A-2 成品件
--   a2_accept_path_read_inside（PosBound5，L3″-gS 通形）加位移和口径
--   symSteps_headPos_eq 直接拼接，供给 sym_run_le_1632 的 hconf 槽；附 hm ↔ hne 桥。
-- ============================================================================

/-- [A5 · ②·1] hm ↔ hne 桥：元素区非空 ↔ 元素表非空。 -/
lemma encodeElementsSym_length_pos_iff {elems : List ℕ} :
    0 < (encodeElementsSym elems).length ↔ elems ≠ [] := by
  constructor
  · intro h hnil
    rw [hnil] at h
    simp [encodeElementsSym] at h
  · intro hne
    cases elems with
    | nil => exact absurd rfl hne
    | cons v rest =>
        rw [encodeElementsSym_length_gen]
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        omega

/-- [A5 · ②·2 hconf 拼接] 接受侧头部局限 → hconf：
    自 `encS inst ++ gS` 的运行达 100 ⟹ 每真前缀位移和 < |encS inst|。
    拼接：前缀 πs.take k（k < πs.length）为真前缀 ⟹ a2 给 cfgsm.headPos < |encS|；
    `symSteps_headPos_eq` 把位移和折算为头位（初始头 = 0）。 -/
lemma hconf_of_accept {inst : SubsetSumInstance} {gS : List Sym}
    {πs : List SymStep} {cfgs' : SymConfig}
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (ht : 0 < inst.target)
    (hrun : SymSteps VerifierSym.transition
      (symInitialConfig (encodeInstanceSym inst ++ gS)) πs cfgs')
    (h100 : cfgs'.state = 100) :
    ∀ k, k < πs.length →
      ((πs.take k).map (fun st => st.result.moveDir.toInt)).sum <
        ((encodeInstanceSym inst).length : ℤ) := by
  intro k hk
  have hreach : SymReachablePath VerifierSym.transition
      (encodeInstanceSym inst ++ gS) πs cfgs' :=
    (symSteps_initial_iff VerifierSym.transition
      (encodeInstanceSym inst ++ gS) πs cfgs').mp hrun
  obtain ⟨cfgsm, hpre, -⟩ := symSteps_append_split (π₀ := πs.take k) (rest := πs.drop k)
    (by rw [List.take_append_drop]; exact hrun)
  have hreach₀ : SymReachablePath VerifierSym.transition
      (encodeInstanceSym inst ++ gS) (πs.take k) cfgsm :=
    (symSteps_initial_iff VerifierSym.transition
      (encodeInstanceSym inst ++ gS) (πs.take k) cfgsm).mp hpre
  have hpfx : List.IsPrefix (πs.take k) πs :=
    ⟨πs.drop k, List.take_append_drop k πs⟩
  have hne : πs.take k ≠ πs := by
    intro hcon
    have hlen : (πs.take k).length = πs.length := congrArg List.length hcon
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at hlen
    omega
  have hlt := a2_accept_path_read_inside inst hm ht gS hreach h100
    (πs.take k) cfgsm hreach₀ hpfx hne
  have hsum := symSteps_headPos_eq VerifierSym.transition hpre
  have hinit : (symInitialConfig (encodeInstanceSym inst ++ gS)).headPos = 0 := rfl
  rw [hinit] at hsum
  omega

-- ============================================================================
-- [A5 · ① 接受侧良形] 接受运行 ⟹ 实例良形（hne/hpos/htarget 三件）——
--   经 Reverse4 `symAccepts_implies_encodeInstanceSym`（解码）+ Reverse6
--   `enc_prefix_unique`（编码前缀唯一 ⟹ 解码实例 = 原实例）。
-- ============================================================================

/-- [A5 · ①·a] symAccepts 形：`encS inst ++ gS` 被接受 ⟹ inst 良形。 -/
lemma wf_of_symAccepts {inst : SubsetSumInstance} {gS : List Sym}
    (hacc : symAccepts VerifierSym.transition VerifierSym.acceptStates
      (encodeInstanceSym inst ++ gS)) :
    inst.elements ≠ [] ∧ (∀ v ∈ inst.elements, 1 ≤ v) ∧ 0 < inst.target := by
  rcases symAccepts_implies_encodeInstanceSym (encodeInstanceSym inst ++ gS) hacc with
    ⟨inst', g', hwS, hne', hpos', ht'⟩
  have hInst : inst = inst' := enc_prefix_unique hwS
  refine ⟨?_, ?_, ?_⟩
  · rw [hInst]; exact hne'
  · intro v hv
    have h0 : 0 < v := hpos' v (by rwa [hInst] at hv)
    omega
  · rw [hInst]; exact ht'

/-- [A5 · ①·b 运行形] 自 `encS inst ++ gS` 的 SymSteps 运行达 100 ⟹ inst 良形
    （hne/hpos/htarget 三件；直供 `sym_run_le_1632` 前件）。 -/
lemma wf_of_accept {inst : SubsetSumInstance} {gS : List Sym}
    {πs : List SymStep} {cfgs' : SymConfig}
    (hrun : SymSteps VerifierSym.transition
      (symInitialConfig (encodeInstanceSym inst ++ gS)) πs cfgs')
    (h100 : cfgs'.state = 100) :
    inst.elements ≠ [] ∧ (∀ v ∈ inst.elements, 1 ≤ v) ∧ 0 < inst.target := by
  apply wf_of_symAccepts
  refine ⟨πs, cfgs', ?_, ?_⟩
  · exact (symSteps_initial_iff VerifierSym.transition
      (encodeInstanceSym inst ++ gS) πs cfgs').mp hrun
  · simpa [VerifierSym.acceptStates, VerifierSym.qAccept] using h100

/-! ========== A5 · ③·核：接受侧折叠入口包（语义上界供给源） ========== -/

/-- [A5 · ③·核] 接受运行 ⟹ 折叠入口包：首达 state-4 配置 `cfg₄`（含 `branch_phase_inv` 六件：
    headPos = 2+|tb| / target 区 frame / 双边界 / 元素区 WithSel 面 / 终界）+ 前缀分解
    `π = π₁ ++ π₂`（π₁ 首达 4）+ 余段运行 `SymSteps cfg₄ π₂ cfg` + **语义上界**
    `selectedSum inst.elements sel ≤ bitsValue (bitsOf inst.target)`（选中和 ≤ target 值）。
    证明 = `symVerifier_correct` 可靠性证明 Case-B 切片：借位越界 ⟹ `main_loop_reject`
    走出 101 ⟹ 与 100 吸收对撞。供 A5·③ 一般接受侧注入（hR0S/hfitS 供给源）。 -/
theorem fold_entry_of_accept {inst : SubsetSumInstance} {π : List SymStep} {cfg : SymConfig}
    (hne : inst.elements ≠ []) (hpos : ∀ v ∈ inst.elements, 0 < v) (htarget : 0 < inst.target)
    (hπ : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π cfg)
    (h100 : cfg.state = 100) :
    ∃ (sel : List Bool) (π₁ π₂ : List SymStep) (cfg₄ : SymConfig),
      sel.length = inst.elements.length ∧
      π = π₁ ++ π₂ ∧
      SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π₁ cfg₄ ∧
      cfg₄.state = 4 ∧
      (∀ {π₀ : List SymStep} {cfg₀ : SymConfig},
        SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π₀ cfg₀ →
        (∃ ρ, π₁ = π₀ ++ ρ) → π₀.length < π₁.length → cfg₀.state ≠ 4) ∧
      SymSteps VerifierSym.transition cfg₄ π₂ cfg ∧
      cfg₄.headPos = 2 + ((encodeBitsSym inst.target).length : ℤ) ∧
      tapeAgrees cfg₄.tape 1 (encodeBitsSym inst.target) ∧
      cfg₄.tape 0 = Sym.boundary ∧
      cfg₄.tape (1 + ((encodeBitsSym inst.target).length : ℤ)) = Sym.boundary ∧
      tapeAgrees cfg₄.tape (2 + ((encodeBitsSym inst.target).length : ℤ))
        (encodeElementsSymWithSel inst.elements sel) ∧
      cfg₄.tape (2 + ((encodeBitsSym inst.target).length : ℤ) +
        ((encodeElementsSymWithSel inst.elements sel).length : ℤ)) =
          Sym.mk SymKind.boundary true ∧
      selectedSum inst.elements sel ≤ bitsValue (bitsOf inst.target) := by
  have _ := htarget
  rcases backchain_to_first4 hπ (by rw [h100]; decide) with
    ⟨π₁, π₂, cfg₄, hsplit, hπ₁, hs4, hno4₁, hrest⟩
  rcases branch_phase_inv inst π₁ cfg₄ hπ₁ hno4₁ hs4 with
    ⟨sel, hsel_len, hhead₄, htarget₄, hb0₄, hb1₄, helems₄, hend₄⟩
  let k : ℕ := (encodeBitsSym inst.target).length
  let tbits : List Bool := bitsOf inst.target
  have htlen : tbits.length = k := by
    dsimp [tbits, k, bitsOf, symToBits, encodeBitsSym, encodeBitsSymNative]
    rw [List.length_map]
  have hhead₅ : cfg₄.headPos = 2 + ((encodeBitsSym inst.target).length : ℤ) := by
    have := hhead₄
    omega
  have hb1₅ : cfg₄.tape (1 + ((encodeBitsSym inst.target).length : ℤ)) = Sym.boundary := by
    have := hb1₄
    simpa using this
  have helems₅ : tapeAgrees cfg₄.tape (2 + ((encodeBitsSym inst.target).length : ℤ))
      (encodeElementsSymWithSel inst.elements sel) := by
    have := helems₄
    simpa using this
  have hend₅ : cfg₄.tape (2 + ((encodeBitsSym inst.target).length : ℤ) +
      ((encodeElementsSymWithSel inst.elements sel).length : ℤ)) =
        Sym.mk SymKind.boundary true := by
    have := hend₄
    simpa using this
  have htarget' : tapeAgrees cfg₄.tape 1 (targetTape 0 tbits) := by
    dsimp [tbits]
    rw [targetTape_zero]
    rw [show bitsToSym (bitsOf inst.target) = encodeBitsSym inst.target from
      (encodeBitsSym_eq_bitsToSym_bitsOf inst.target).symm]
    exact htarget₄
  have hbound' : cfg₄.tape (1 + (k : ℤ)) = Sym.boundary := by
    simpa [k] using hb1₄
  have hhashL' : cfg₄.tape (1 - 1) = Sym.boundary := by
    simpa using hb0₄
  have hpad' : ∀ i : ℤ, 1 + (k : ℤ) ≤ i ∧ i < 1 + (k : ℤ) → cfg₄.tape i = Sym.data0 := by
    intro i hi
    omega
  have helems' : tapeAgrees cfg₄.tape ((1 + (k : ℤ)) + 1)
      (encodeElementsSymWithSel inst.elements sel) := by
    have hpos' : (1 + (k : ℤ)) + 1 = 2 + (k : ℤ) := by omega
    simpa [k, hpos'] using helems₄
  have hend' : (cfg₄.tape ((1 + (k : ℤ)) + 1 +
      (encodeElementsSymWithSel inst.elements sel).length : ℤ)).1 = SymKind.boundary := by
    have hpos' : (1 + (k : ℤ)) + 1 = 2 + (k : ℤ) := by omega
    simpa [k, hpos'] using (congrArg (fun x : Sym => x.1) hend₄)
  have hcfg₄' : cfg₄ = SymConfig.mk 4 cfg₄.tape ((1 + (k : ℤ)) + 1) := by
    cases cfg₄ with
    | mk s t hp =>
        dsimp
        rw [show s = 4 from hs4]
        rw [show hp = (1 + (k : ℤ)) + 1 from by
          dsimp [k] at hhead₄ ⊢
          omega]
  have hrest' : SymSteps VerifierSym.transition
      (SymConfig.mk 4 cfg₄.tape ((1 + (k : ℤ)) + 1)) π₂ cfg := by
    rw [hcfg₄'] at hrest
    exact hrest
  let Pd : ℕ → Prop := fun q =>
    q ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 76, 77, 81, 84, 85, 86, 87, 38, 51, 28, 100, 101} : Finset ℕ)
  have hdet_d : ∀ ⦃q : ℕ⦄ ⦃s : Sym⦄ ⦃r r' : SymTransResult⦄,
      Pd q → r ∈ VerifierSym.transition (q, s) → r' ∈ VerifierSym.transition (q, s) → r = r' := by
    intro q s r r' hq hr hr'
    have hdec : ∀ q ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 76, 77, 81, 84, 85, 86, 87, 38, 51, 28, 100, 101} : Finset ℕ),
        ∀ s : Sym, ∀ r ∈ VerifierSym.transition (q, s), ∀ r' ∈ VerifierSym.transition (q, s), r = r' := by
      native_decide
    dsimp [Pd] at hq
    exact hdec q hq s r hr r' hr'
  have hclose_d : ∀ ⦃q : ℕ⦄ ⦃s : Sym⦄ ⦃r : SymTransResult⦄,
      Pd q → r ∈ VerifierSym.transition (q, s) → Pd r.nextState := by
    intro q s r hq hr
    have hdec : ∀ q ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 76, 77, 81, 84, 85, 86, 87, 38, 51, 28, 100, 101} : Finset ℕ),
        ∀ s : Sym, ∀ r ∈ VerifierSym.transition (q, s),
          r.nextState ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 76, 77, 81, 84, 85, 86, 87, 38, 51, 28, 100, 101} : Finset ℕ) := by
      native_decide
    dsimp [Pd] at hq
    exact hdec q hq s r hr
  have hP₀_d : Pd 4 := by
    dsimp [Pd]
    native_decide
  by_cases hle : selectedSum inst.elements sel ≤ bitsValue tbits
  · refine ⟨sel, π₁, π₂, cfg₄, hsel_len, hsplit, hπ₁, hs4, hno4₁, hrest,
      hhead₅, htarget₄, hb0₄, hb1₅, helems₅, hend₅, ?_⟩
    exact hle
  · exfalso
    have hgt_total : bitsValue tbits < selectedSum inst.elements sel := by omega
    rcases main_loop_reject inst.elements sel tbits 1 (1 + (k : ℤ)) cfg₄.tape
        (by exact hne) (by exact hpos) hsel_len
        (by omega : 1 + (tbits.length : ℤ) ≤ 1 + (k : ℤ))
        htarget' hbound' hhashL' (by simpa only [htlen] using hpad') helems' hend' hgt_total with
      ⟨πr, cfgr, hπr, h101⟩
    have hpfx' := SymSteps_prefix_unique_det (M := VerifierSym.transition) Pd
      (SymConfig.mk 4 cfg₄.tape ((1 + (k : ℤ)) + 1)) hdet_d hclose_d hP₀_d hrest' hπr
    rcases hpfx' with hrev' | hfwd'
    · rcases hrev' with ⟨ρ, _, hρ⟩
      have hcfg100' : cfg = SymConfig.mk 100 cfg.tape cfg.headPos := by
        cases cfg with
        | mk s t p => dsimp; rw [show s = 100 from h100]
      rw [hcfg100'] at hρ
      have hfrom100 : cfgr.state = 100 :=
        steps_from_100 cfg.tape cfg.headPos (π := ρ) (cfg := cfgr) hρ
      rw [hfrom100] at h101
      omega
    · rcases hfwd' with ⟨ρ, _, hρ⟩
      have hcfg101 : cfgr = SymConfig.mk 101 cfgr.tape cfgr.headPos := by
        cases cfgr with
        | mk s t p => dsimp; rw [show s = 101 from h101]
      rw [hcfg101] at hρ
      have h101' : cfg.state = 101 :=
        steps_from_101 cfgr.tape cfgr.headPos (π := ρ) (cfg := cfg) hρ
      rw [h101'] at h100
      omega

-- ============================================================================
-- [A5 · ③·供给批] 值桥 + 总装：运行形 hseg（sym_run_le_1632_fold）——∀-schema 退役替代。
-- ============================================================================

/-- [A5 · ③·供给 · 值桥 0] `valFrom` 权重倍进：`valFrom l (2w) = 2·valFrom l w`。 -/
lemma valFrom_mul_two (l : List Bool) (w : ℤ) : valFrom l (2 * w) = 2 * valFrom l w := by
  induction l generalizing w with
  | nil => simp [valFrom]
  | cons b t ih =>
      simp only [valFrom_cons]
      rw [ih (2 * w)]
      by_cases hb : b <;> simp [hb] <;> ring

/-- [A5 · ③·供给 · 值桥一] `valFrom`（权重 1 起）= `bitsValue`（ℤ 化）。 -/
lemma valFrom_bitsValue (l : List Bool) : valFrom l 1 = ((bitsValue l : ℕ) : ℤ) := by
  induction l with
  | nil => simp [valFrom]
  | cons b t ih =>
      simp only [valFrom_cons, bitsValue_cons]
      rw [valFrom_mul_two t 1, ih]
      by_cases hb : b <;> simp [hb] <;> push_cast <;> ring

/-- [A5 · ③·供给 · 值桥二] 解码单位：`valFrom (bitsOf v) 1 = v`。 -/
lemma valFrom_bitsOf_one (v : ℕ) : valFrom (bitsOf v) 1 = (v : ℤ) := by
  rw [valFrom_bitsValue, bitsValue_bitsOf]

/-- [A5 · ③·供给 · 和桥 0a] `selectedSum` cons（true）。 -/
lemma selectedSum_cons_true (v : ℕ) (rest : List ℕ) (sel' : List Bool) :
    selectedSum (v :: rest) (true :: sel') = v + selectedSum rest sel' := by
  simp [selectedSum, List.zip_cons_cons]

/-- [A5 · ③·供给 · 和桥 0b] `selectedSum` cons（false）。 -/
lemma selectedSum_cons_false (v : ℕ) (rest : List ℕ) (sel' : List Bool) :
    selectedSum (v :: rest) (false :: sel') = selectedSum rest sel' := by
  simp [selectedSum, List.zip_cons_cons]

/-- [A5 · ③·供给 · 和桥三] `chosenVal`（ℤ）= `selectedSum`（ℕ）。 -/
lemma chosenVal_eq_selectedSum (elems : List ℕ) (sels : List Bool) :
    chosenVal elems sels = ((selectedSum elems sels : ℕ) : ℤ) := by
  induction elems generalizing sels with
  | nil => cases sels <;> simp [chosenVal, selectedSum]
  | cons v rest ih =>
      cases sels with
      | nil => simp [chosenVal, selectedSum]
      | cons b s' =>
          cases b with
          | false =>
              rw [chosenVal_cons_false, selectedSum_cons_false]
              exact ih s'
          | true =>
              rw [chosenVal_cons_true, selectedSum_cons_true, ih s', valFrom_bitsOf_one]
              push_cast
              ring

/-- [A5 · ③·供给 · 单项界] 选中单项 ≤ 选中和。 -/
lemma le_selectedSum_of_mem_zip {elems : List ℕ} {sels : List Bool} {p : ℕ × Bool}
    (hp : p ∈ elems.zip sels) (hsel : p.2 = true) : p.1 ≤ selectedSum elems sels := by
  unfold selectedSum
  have h1 : p ∈ (elems.zip sels).filter (fun q => q.2 = true) :=
    List.mem_filter.mpr ⟨hp, by simpa using hsel⟩
  have h2 : p.1 ∈ ((elems.zip sels).filter (fun q => q.2 = true)).map Prod.fst :=
    List.mem_map.mpr ⟨p, h1, rfl⟩
  simpa using List.le_sum_of_mem h2

/-- [A5 · ③·供给甲] hfitS（收窄形）一般接受侧供给：
    `selectedSum ≤ bitsValue tbits` ⟹ 选中元素位长 ≤ |tb|。 -/
lemma hfit_of_entry_bound {inst : SubsetSumInstance} {sel : List Bool}
    (hpos : ∀ v ∈ inst.elements, 0 < v)
    (hle : selectedSum inst.elements sel ≤ bitsValue (bitsOf inst.target)) :
    ∀ p ∈ inst.elements.zip sel, p.2 = true →
      ((bitsOf p.1).length : ℤ) ≤ ((encodeBitsSym inst.target).length : ℤ) := by
  intro p hp hpsel
  have hvle : p.1 ≤ bitsValue (bitsOf inst.target) :=
    le_trans (le_selectedSum_of_mem_zip hp hpsel) hle
  have h0 : 0 < p.1 := hpos p.1 (List.of_mem_zip hp).1
  have hlen : (bitsOf p.1).length ≤ (bitsOf inst.target).length :=
    bitsOf_length_le_of_value_le p.1 (bitsOf inst.target) h0 hvle
  have hclen : (bitsOf inst.target).length = (encodeBitsSym inst.target).length := by
    rw [encodeBitsSym_eq_bitsToSym_bitsOf]
    simp [bitsToSym]
  have hcast : ((bitsOf p.1).length : ℤ) ≤ ((bitsOf inst.target).length : ℤ) := by
    exact_mod_cast hlen
  rw [hclen] at hcast
  exact hcast

/-- [A5 · ③·供给乙] hR0S 一般接受侧供给：frame 处 `chosenVal ≤ regVal`。 -/
lemma chosenVal_le_regVal_entry {inst : SubsetSumInstance} {sel : List Bool} {tape : ℤ → Sym}
    (hle : selectedSum inst.elements sel ≤ bitsValue (bitsOf inst.target))
    (hframe : tapeAgrees tape 1 (encodeBitsSym inst.target)) :
    chosenVal inst.elements sel ≤
      regVal tape ((2 + ((encodeBitsSym inst.target).length : ℤ) - 2).toNat) := by
  have hsum : (selectedSum inst.elements sel : ℤ) ≤ (inst.target : ℤ) := by
    have h := hle
    rw [bitsValue_bitsOf] at h
    exact_mod_cast h
  have hrhs : regVal tape ((2 + ((encodeBitsSym inst.target).length : ℤ) - 2).toNat)
      = (inst.target : ℤ) := by
    have ht2 : ((2 + ((encodeBitsSym inst.target).length : ℤ)) - 2).toNat
        = (encodeBitsSym inst.target).length := by
      rw [show (2 + ((encodeBitsSym inst.target).length : ℤ)) - 2
          = ((encodeBitsSym inst.target).length : ℤ) from by ring]
      exact Int.toNat_natCast _
    rw [ht2]
    exact regVal_tapeAgrees_encodeBitsSym tape inst.target hframe
  rw [chosenVal_eq_selectedSum, hrhs]
  exact hsum

/-- [A5 · ③·供给丙] frame 处 target 区 kinds/flags（`run_tail_len_le` 前件形）。 -/
lemma kinds_marks_of_frame {inst : SubsetSumInstance} {tape : ℤ → Sym}
    (hframe : tapeAgrees tape 1 (encodeBitsSym inst.target)) :
    (∀ i : ℤ, 1 ≤ i → i ≤ ((encodeBitsSym inst.target).length : ℤ) →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1) ∧
    (∀ i : ℤ, 1 ≤ i → i ≤ ((encodeBitsSym inst.target).length : ℤ) →
      (tape i).2 = false) := by
  constructor
  · intro i hi1 hi2
    have hbnd2 : i.toNat - 1 < (encodeBitsSym inst.target).length := by
      have h2 : i.toNat ≤ (encodeBitsSym inst.target).length := (Int.toNat_le).mpr hi2
      have h1 : 1 ≤ i.toNat := (Int.le_toNat (by omega : (0 : ℤ) ≤ i)).mpr hi1
      omega
    have hmem := hframe (i.toNat - 1) hbnd2
    have hcell2 : 1 + ((i.toNat - 1 : ℕ) : ℤ) = i := by
      have h1 : 1 ≤ i.toNat := (Int.le_toNat (by omega : (0 : ℤ) ≤ i)).mpr hi1
      have htn : ((i.toNat : ℕ) : ℤ) = i := Int.toNat_of_nonneg (by omega)
      omega
    rw [hcell2] at hmem
    rw [hmem]
    rcases encodeBitsSym_entries inst.target _ (List.getElem_mem hbnd2) with h | h <;>
      rw [h] <;> [exact Or.inl rfl; exact Or.inr rfl]
  · intro i hi1 hi2
    have hbnd2 : i.toNat - 1 < (encodeBitsSym inst.target).length := by
      have h2 : i.toNat ≤ (encodeBitsSym inst.target).length := (Int.toNat_le).mpr hi2
      have h1 : 1 ≤ i.toNat := (Int.le_toNat (by omega : (0 : ℤ) ≤ i)).mpr hi1
      omega
    have hmem := hframe (i.toNat - 1) hbnd2
    have hcell2 : 1 + ((i.toNat - 1 : ℕ) : ℤ) = i := by
      have h1 : 1 ≤ i.toNat := (Int.le_toNat (by omega : (0 : ℤ) ≤ i)).mpr hi1
      have htn : ((i.toNat : ℕ) : ℤ) = i := Int.toNat_of_nonneg (by omega)
      omega
    rw [hcell2] at hmem
    rw [hmem]
    rcases encodeBitsSym_entries inst.target _ (List.getElem_mem hbnd2) with h | h <;>
      rw [h] <;> rfl

set_option maxHeartbeats 900000 in
/-- [A5 · ③·供给总装] 运行形 hseg：任意 inst/gS、任意自 `encS inst ++ gS` 的洁净运行达 100
    ⟹ 1632 形界（与 C1 同结语）。内部 = port → rf（长度侧）→ `fold_entry_of_accept`（语义侧）
    → 供给甲/乙/丙 → `run_tail_len_le`@cfg₄ → n₁ 反证 → `run_total_le_f4` + 旧算术。 -/
theorem sym_run_le_1632_fold (inst : SubsetSumInstance) (gS : List Sym)
    {πs : List SymStep} {cfgs' : SymConfig}
    (hne : inst.elements ≠ [])
    (hpos : ∀ v ∈ inst.elements, 1 ≤ v)
    (htarget : 0 < inst.target)
    (hconf : ∀ k, k < πs.length →
      ((πs.take k).map (fun st => st.result.moveDir.toInt)).sum <
        ((encodeInstanceSym inst).length : ℤ))
    (hrun : SymSteps VerifierSym.transition
      (symInitialConfig (encodeInstanceSym inst ++ gS)) πs cfgs')
    (hclean : ∀ s ∈ πs, s.fromState ≠ 100)
    (h100 : cfgs'.state = 100) :
    (πs.length : ℤ) ≤ (((encodeInstanceSym inst ++ gS).length : ℤ) * 1632 + 1)
      * (((encodeInstanceSym inst ++ gS).length : ℤ) + 102) := by
  have hpos0 : ∀ v ∈ inst.elements, 0 < v := fun v hv => by have := hpos v hv; omega
  -- ① 输入前缀归约
  obtain ⟨cfg₀, hrun₀, hst₀, -, -⟩ := symSteps_input_append_left (inst := inst) (gS := gS) hrun hconf
  -- ② 格式拆分（长度侧）
  obtain ⟨sel, π₀, ρ, π₁, step₃, cfgm, cf₁, hsel_len, hsplit, -, h₀, -, -, -, -,
      hst, hhp, hρ, hface, hbnd0, hbndL, hkinds, hmarks, hterm, hπ₁⟩ :=
    run_format_split hrun₀ (hst₀.trans h100) hne hpos0 htarget
  -- ③ 核（语义侧）
  rcases fold_entry_of_accept (inst := inst) hne hpos0 htarget hrun₀ (hst₀.trans h100) with
    ⟨sel₄, π₁b, π₂, cfg₄, hsel_len₄, hsplit₄, hπ₁b, hs₄, hno₄, hrest,
      hhead₄, hframe, hb₀₄, hb₁₄, helems₄, hend₄, hle⟩
  -- ④ 供给：hR0 / hfit / kinds / marks / term
  have hR0 : chosenVal inst.elements sel₄ ≤
      regVal cfg₄.tape (((2 + ((encodeBitsSym inst.target).length : ℤ)) - 2).toNat) :=
    chosenVal_le_regVal_entry hle hframe
  have hfit : ∀ p ∈ inst.elements.zip sel₄, p.2 = true →
      ((bitsOf p.1).length : ℤ) ≤ ((encodeBitsSym inst.target).length : ℤ) :=
    hfit_of_entry_bound hpos0 hle
  obtain ⟨hkd₄, hfl₄⟩ := kinds_marks_of_frame (inst := inst) hframe
  have hterm₄ : cfg₄.tape (2 + ((encodeBitsSym inst.target).length : ℤ) +
      ((encodeElementsSym inst.elements).length : ℤ)) = Sym.mk SymKind.boundary true := by
    rw [← WithSel_length inst.elements sel₄ hsel_len₄]
    exact hend₄
  -- ⑤ 尾段界（run_tail @ cfg₄）
  have h₂ : (π₂.length : ℤ) ≤
      foldLenB (inst.elements.map (fun v => (bitsOf v).length))
          (2 + ((encodeBitsSym inst.target).length : ℤ)) +
        (2 + ((encodeBitsSym inst.target).length : ℤ) +
          ((encodeElementsSymWithSel inst.elements sel₄).length : ℤ) + 1) :=
    run_tail_len_le hne hsel_len₄ hpos hfit hs₄ hhead₄ helems₄ hb₁₄ hb₀₄ hkd₄ hfl₄
      hterm₄ hR0 hrest (hst₀.trans h100) (fun s hs => hclean s (by
        rw [hsplit₄]
        exact List.mem_append.mpr (Or.inr hs)))
  -- ⑥ n₁ 合成：π₁b 首达 4 ⟹ |π₁b| ≤ |π₀ ++ step₃ :: ρ|
  have hn₁ : π₁b.length ≤ (π₀ ++ step₃ :: ρ).length := by
    by_cases hlt : (π₀ ++ step₃ :: ρ).length < π₁b.length
    · exfalso
      have hrun₀a : SymSteps VerifierSym.transition
          (symInitialConfig (encodeInstanceSym inst)) (π₀ ++ step₃ :: (ρ ++ π₁)) cfg₀ := by
        simpa [hsplit] using hrun₀
      have hEq : (π₀ ++ step₃ :: ρ) ++ π₁ = π₀ ++ step₃ :: (ρ ++ π₁) := by
        simp [List.append_assoc]
      have hrun₀' : SymSteps VerifierSym.transition
          (symInitialConfig (encodeInstanceSym inst)) ((π₀ ++ step₃ :: ρ) ++ π₁) cfg₀ := by
        rw [hEq]
        exact hrun₀a
      obtain ⟨X, htkX, hdrX⟩ := symSteps_append_split hrun₀'
      have hX4 : X.state = 4 := by
        cases hπ₁nil : π₁ with
        | nil =>
            have hle_s : π₁b.length ≤ πs.length := by
              rw [hsplit₄]
              simp
            have hlen₁ : πs.length = (π₀ ++ step₃ :: ρ).length := by
              rw [hsplit, hπ₁nil]
              simp [List.length_append]
            omega
        | cons s₀ rest =>
            have hdrX' : SymSteps VerifierSym.transition X (s₀ :: rest) cfg₀ := by
              simpa [hπ₁nil] using hdrX
            obtain ⟨X₁, hs₀X, -⟩ := symSteps_append_split (M := VerifierSym.transition)
              (cfg₀ := X) (π₀ := [s₀]) (rest := rest) (by simpa using hdrX')
            obtain ⟨hf₀, -, -, -⟩ := symSteps_singleton_facts hs₀X
            have hπ₁' : SymSteps VerifierSym.transition cf₁ (s₀ :: rest) cfg₀ := by
              simpa [hπ₁nil] using hπ₁
            obtain ⟨Z, hs₀Z, -⟩ := symSteps_append_split (M := VerifierSym.transition)
              (cfg₀ := cf₁) (π₀ := [s₀]) (rest := rest) (by simpa using hπ₁')
            obtain ⟨hf₁, -, -, -⟩ := symSteps_singleton_facts hs₀Z
            rw [← hf₀, hf₁, hst]
      have hpre : ∃ ρ', π₁b = (π₀ ++ step₃ :: ρ) ++ ρ' := by
        have e1 : πs.take (π₀ ++ step₃ :: ρ).length = π₁b.take (π₀ ++ step₃ :: ρ).length := by
          rw [hsplit₄]
          exact List.take_append_of_le_length (by omega)
        have e2 : πs.take (π₀ ++ step₃ :: ρ).length = π₀ ++ step₃ :: ρ := by
          rw [hsplit, ← hEq]
          rw [List.take_append_of_le_length (le_rfl :
            (π₀ ++ step₃ :: ρ).length ≤ (π₀ ++ step₃ :: ρ).length)]
          exact List.take_length
        have e3 : π₁b.take (π₀ ++ step₃ :: ρ).length = π₀ ++ step₃ :: ρ :=
          e1.symm.trans e2
        refine ⟨π₁b.drop (π₀ ++ step₃ :: ρ).length, ?_⟩
        have h := List.take_append_drop (π₀ ++ step₃ :: ρ).length π₁b
        rw [e3] at h
        exact h.symm
      exact hno₄ htkX hpre hlt hX4
    · omega
  -- ⑦ |π₁| ≤ |π₂| ⇒ h₁（旧链第④步入参）
  have hlen_eq₁ : πs.length = (π₀ ++ step₃ :: ρ).length + π₁.length := by
    rw [hsplit]
    simp only [List.length_append, List.length_cons]
    omega
  have hlen_eq₂ : πs.length = π₁b.length + π₂.length := by
    rw [hsplit₄]
    simp
  have hlen_le : π₁.length ≤ π₂.length := by omega
  have hW₄ : ((encodeElementsSymWithSel inst.elements sel₄).length : ℤ)
      = ((encodeElementsSymWithSel inst.elements sel).length : ℤ) := by
    rw [WithSel_length inst.elements sel₄ hsel_len₄, WithSel_length inst.elements sel hsel_len]
  have h₁ : (π₁.length : ℤ) ≤
      foldLenB (inst.elements.map (fun v => (bitsOf v).length))
          (2 + ((encodeBitsSym inst.target).length : ℤ)) +
        (2 + ((encodeBitsSym inst.target).length : ℤ) +
          ((encodeElementsSymWithSel inst.elements sel).length : ℤ) + 1) := by
    have hc : (π₁.length : ℤ) ≤ (π₂.length : ℤ) := by exact_mod_cast hlen_le
    have h₂' := h₂
    rw [hW₄] at h₂'
    exact le_trans hc h₂'
  -- ⑧ 全段收口（B2，m := 5 ⇒ 96 因子）——旧链同步
  have hρ' : (ρ.length : ℤ) ≤ 2 * (3 + ((encodeBitsSym inst.target).length : ℤ) +
      ((encodeElementsSym inst.elements).length : ℤ)) := by
    exact_mod_cast hρ
  have hb2 : (πs.length : ℤ) ≤
      96 * (4 * ((encodeInstanceSym inst ++ gS).length : ℤ) + 1) ^ 2 := by
    have h := run_total_le_f4 (inst := inst) gS 5 hsel_len hsplit h₀ hρ' h₁
    have hxlen : (encodeInstanceF4 inst ++ flat4F4 gS).length + 1 =
        4 * ((encodeInstanceSym inst ++ gS).length) + 1 := by
      simp only [List.length_append, encodeInstanceF4, flat4F4_length]
      ring
    rw [hxlen] at h
    have h5 : (16 : ℕ) * (5 + 1) = 96 := by norm_num
    rw [h5] at h
    exact_mod_cast h
  -- ⑨ 1632 形收口算术——旧链同步
  have hkey : (96 : ℤ) * (4 * ((encodeInstanceSym inst ++ gS).length : ℤ) + 1) ^ 2 ≤
      (((encodeInstanceSym inst ++ gS).length : ℤ) * 1632 + 1) *
        (((encodeInstanceSym inst ++ gS).length : ℤ) + 102) := by
    have hE : (0 : ℤ) ≤ ((encodeInstanceSym inst ++ gS).length : ℤ) := Int.natCast_nonneg _
    nlinarith [hE, sq_nonneg (4 * ((encodeInstanceSym inst ++ gS).length : ℤ) + 1),
      sq_nonneg ((encodeInstanceSym inst ++ gS).length : ℤ)]
  exact le_trans hb2 hkey

-- ============================================================================
-- [C1 · T-P5.3 供给件] hseg 供给：1632 形界（免费域操作化前件显式）。
-- ============================================================================

set_option maxHeartbeats 900000 in -- 因：B2 收口 + 1632 形算术
/-- [C1 · T-P5.3 供给件] 任意 inst/gS、任意自 `encS inst ++ gS` 的洁净运行达 100
    ⟹ `(1632·E + 1)(E + 102)` 形界（E = |encS inst ++ gS|）。
    前件：hne/hpos/htarget（实例良形）；hconf（全头局限 `encS` 前缀内）；
    hfitS/hR0S（cf₁ 出口面语义供给——免费域操作化注入点）。 -/
theorem sym_run_le_1632 (inst : SubsetSumInstance) (gS : List Sym)
    {πs : List SymStep} {cfgs' : SymConfig}
    (hne : inst.elements ≠ [])
    (hpos : ∀ v ∈ inst.elements, 1 ≤ v)
    (htarget : 0 < inst.target)
    (hconf : ∀ k, k < πs.length →
      ((πs.take k).map (fun st => st.result.moveDir.toInt)).sum <
        ((encodeInstanceSym inst).length : ℤ))
    (hfitS : ∀ (sel : List Bool) (cf₁ : SymConfig),
      cf₁.state = 4 →
      cf₁.headPos = 2 + ((encodeBitsSym inst.target).length : ℤ) →
      tapeAgrees cf₁.tape (2 + ((encodeBitsSym inst.target).length : ℤ))
        (encodeElementsSymWithSel inst.elements sel) →
      ∀ p ∈ inst.elements.zip sel, p.2 = true →
        ((bitsOf p.1).length : ℤ) ≤ ((encodeBitsSym inst.target).length : ℤ))
    (hR0S : ∀ (sel : List Bool) (cf₁ : SymConfig),
      cf₁.state = 4 →
      cf₁.headPos = 2 + ((encodeBitsSym inst.target).length : ℤ) →
      tapeAgrees cf₁.tape (2 + ((encodeBitsSym inst.target).length : ℤ))
        (encodeElementsSymWithSel inst.elements sel) →
      chosenVal inst.elements sel ≤
        regVal cf₁.tape (((2 + ((encodeBitsSym inst.target).length : ℤ)) - 2).toNat))
    (hrun : SymSteps VerifierSym.transition
      (symInitialConfig (encodeInstanceSym inst ++ gS)) πs cfgs')
    (hclean : ∀ s ∈ πs, s.fromState ≠ 100)
    (h100 : cfgs'.state = 100) :
    (πs.length : ℤ) ≤ (((encodeInstanceSym inst ++ gS).length : ℤ) * 1632 + 1)
      * (((encodeInstanceSym inst ++ gS).length : ℤ) + 102) := by
  -- ① 输入前缀归约：encS ++ gS → encS
  obtain ⟨cfg₀, hrun₀, hst₀, -, -⟩ := symSteps_input_append_left (inst := inst) (gS := gS) hrun hconf
  -- ② 格式拆分（四段）
  obtain ⟨sel, π₀, ρ, π₁, step₃, cfgm, cf₁, hsel_len, hsplit, -, h₀, -, -, -, -, hst, hhp,
      hρ, hface, hbnd0, hbndL, hkinds, hmarks, hterm, hπ₁⟩ :=
    run_format_split hrun₀ (hst₀.trans h100) hne (fun v hv => by have h1 := hpos v hv; omega) htarget
  -- ③ 尾段界（A1/A2 + 免费域供给）
  have hpos1 : ∀ v ∈ inst.elements, 1 ≤ v := hpos
  have hfit : ∀ p ∈ inst.elements.zip sel, p.2 = true →
      ((bitsOf p.1).length : ℤ) ≤ ((encodeBitsSym inst.target).length : ℤ) :=
    hfitS sel cf₁ hst hhp hface
  have hR0 : chosenVal inst.elements sel ≤
      regVal cf₁.tape (((2 + ((encodeBitsSym inst.target).length : ℤ)) - 2).toNat) :=
    hR0S sel cf₁ hst hhp hface
  have h₁ : (π₁.length : ℤ) ≤
      foldLenB (inst.elements.map (fun v => (bitsOf v).length))
          (2 + ((encodeBitsSym inst.target).length : ℤ)) +
        (2 + ((encodeBitsSym inst.target).length : ℤ) +
          ((encodeElementsSymWithSel inst.elements sel).length : ℤ) + 1) :=
    run_tail_len_le hne hsel_len hpos1 hfit hst hhp hface hbnd0 hbndL hkinds hmarks
      hterm hR0 hπ₁ (hst₀.trans h100) (fun s hs => hclean s (by
        rw [hsplit]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr
          (Or.inr (List.mem_append.mpr (Or.inr hs)))))))
  -- ④ 全段收口（B2，m := 5 ⇒ 96 因子）
  have hρ' : (ρ.length : ℤ) ≤ 2 * (3 + ((encodeBitsSym inst.target).length : ℤ) +
      ((encodeElementsSym inst.elements).length : ℤ)) := by
    exact_mod_cast hρ
  have hb2 : (πs.length : ℤ) ≤
      96 * (4 * ((encodeInstanceSym inst ++ gS).length : ℤ) + 1) ^ 2 := by
    have h := run_total_le_f4 (inst := inst) gS 5 hsel_len hsplit h₀ hρ' h₁
    have hxlen : (encodeInstanceF4 inst ++ flat4F4 gS).length + 1 =
        4 * ((encodeInstanceSym inst ++ gS).length) + 1 := by
      simp only [List.length_append, encodeInstanceF4, flat4F4_length]
      ring
    rw [hxlen] at h
    have h5 : (16 : ℕ) * (5 + 1) = 96 := by norm_num
    rw [h5] at h
    exact_mod_cast h
  -- ⑤ 1632 形收口算术
  have hkey : (96 : ℤ) * (4 * ((encodeInstanceSym inst ++ gS).length : ℤ) + 1) ^ 2 ≤
      (((encodeInstanceSym inst ++ gS).length : ℤ) * 1632 + 1) *
        (((encodeInstanceSym inst ++ gS).length : ℤ) + 102) := by
    have hE : (0 : ℤ) ≤ ((encodeInstanceSym inst ++ gS).length : ℤ) := Int.natCast_nonneg _
    nlinarith [hE, sq_nonneg (4 * ((encodeInstanceSym inst ++ gS).length : ℤ) + 1),
      sq_nonneg ((encodeInstanceSym inst ++ gS).length : ℤ)]
  exact le_trans hb2 hkey


-- ============================================================================
-- [③ · 最坏案例推导批] 免费域（接受路径 100 ∪ 最坏案例）内的 cf₁ 面供给：
--   hfitS（位长 ≤ target 位长）与 hR0（选中和 ≤ 族和）——最坏案例 + 计数式。
-- ============================================================================

/-- [③·2] 全 1 权重和：`valFrom (replicate b true) w = w·(2^b − 1)`。 -/
lemma valFrom_replicate_true (b : ℕ) (w : ℤ) :
    valFrom (List.replicate b true) w = w * ((2 : ℤ) ^ b - 1) := by
  induction b generalizing w with
  | zero => simp [valFrom]
  | succ b ih =>
      have hstep : valFrom (List.replicate (b + 1) true) w
          = w + valFrom (List.replicate b true) (2 * w) := by
        simp [List.replicate_succ, valFrom_cons]
      rw [hstep, ih, pow_succ]
      ring

/-- [③·3] 计数式：选中和 ≤ 全元素值和（一般实例形式）。 -/
lemma chosenVal_le_mapSum (elems : List ℕ) (sels : List Bool) :
    chosenVal elems sels ≤
      (elems.map (fun v => valFrom (bitsOf v) 1)).sum := by
  induction elems generalizing sels with
  | nil => simp [chosenVal]
  | cons v rest ih =>
      cases sels with
      | nil =>
          have h2 : (0 : ℤ) ≤ valFrom (bitsOf v) 1 := valFrom_nonneg (bitsOf v) 1 (by norm_num)
          have h3 : (0 : ℤ) ≤ (List.map (fun v => valFrom (bitsOf v) 1) rest).sum := by
            apply List.sum_nonneg
            intro x hx
            rcases List.mem_map.mp hx with ⟨u, -, rfl⟩
            exact valFrom_nonneg (bitsOf u) 1 (by norm_num)
          simp only [chosenVal, List.zip_nil_right, List.filterMap_nil, List.sum_nil,
            List.map_cons, List.sum_cons]
          linarith [h2, h3]
      | cons b sel' =>
          cases b with
          | true =>
              rw [chosenVal_cons_true, List.map_cons, List.sum_cons]
              have h1 := ih sel'
              have h2 : (0 : ℤ) ≤ valFrom (bitsOf v) 1 := valFrom_nonneg (bitsOf v) 1 (by norm_num)
              linarith
          | false =>
              rw [chosenVal_cons_false, List.map_cons, List.sum_cons]
              have h1 := ih sel'
              have h2 : (0 : ℤ) ≤ valFrom (bitsOf v) 1 := valFrom_nonneg (bitsOf v) 1 (by norm_num)
              linarith

/-- [③·4] 最坏案例 ⟹ 元素区非空。 -/
lemma worst_hne (bs : List ℕ) (inst : SubsetSumInstance) (hw : WorstCase bs inst) :
    inst.elements ≠ [] := by
  rw [hw.1]
  intro hcon
  exact hw.2.2.1 (List.map_eq_nil_iff.mp hcon)

/-- [③·5] 最坏案例 ⟹ 元素皆正。 -/
lemma worst_hpos (bs : List ℕ) (inst : SubsetSumInstance) (hw : WorstCase bs inst) :
    ∀ v ∈ inst.elements, 1 ≤ v := by
  intro v hv
  rw [hw.1] at hv
  rcases List.mem_map.mp hv with ⟨b, hb, rfl⟩
  have h1 : 1 ≤ b := hw.2.2.2 b hb
  have h2 : (2 : ℕ) ≤ 2 ^ b := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h1
  omega

/-- [③·6] 最坏案例 ⟹ target 正。 -/
lemma worst_htarget (bs : List ℕ) (inst : SubsetSumInstance) (hw : WorstCase bs inst) :
    0 < inst.target := by
  rw [hw.2.1]
  apply Nat.pos_of_ne_zero
  intro hcon
  have hc : (((valSum bs).toNat : ℤ)) = valSum bs := Int.toNat_of_nonneg (valSum_nonneg bs)
  have hzero : valSum bs = 0 := by
    rw [hcon] at hc
    simpa using hc.symm
  cases bs with
  | nil => exact hw.2.2.1 rfl
  | cons b0 rest =>
      have h1 : (2 : ℤ) ^ b0 - 1 ≤ valSum (b0 :: rest) := le_valSum_of_mem _ b0 (by simp)
      have hb0' : 1 ≤ b0 := hw.2.2.2 b0 (by simp)
      have h3 : (2 : ℤ) ≤ 2 ^ b0 := by
        calc (2 : ℤ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ b0 := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hb0'
      omega

/-- [③·7] 接受侧推导 · hfitS（最坏案例）：全 1 元素位长 ≤ target 位长。 -/
lemma hfitS_of_worst (bs : List ℕ) (inst : SubsetSumInstance) (hw : WorstCase bs inst) :
    ∀ v ∈ inst.elements, ((bitsOf v).length : ℤ) ≤
      ((encodeBitsSym inst.target).length : ℤ) := by
  intro v hv
  rw [hw.1] at hv
  rcases List.mem_map.mp hv with ⟨b, hb, hveq⟩
  rw [← hveq, bitsOf_two_pow_sub_one, List.length_replicate, hw.2.1]
  exact bitlen_le_target bs b hb (hw.2.2.2 b hb)

/-- [③·8] 接受侧推导 · hR0（最坏案例 · 计数式）：选中和 ≤ 族和。 -/
lemma hR0S_count_worst (bs : List ℕ) (inst : SubsetSumInstance) (hw : WorstCase bs inst)
    (sel : List Bool) :
    chosenVal inst.elements sel ≤ valSum bs := by
  rw [hw.1]
  have h1 := chosenVal_le_mapSum (bs.map (fun b => 2 ^ b - 1)) sel
  have h2 : ((bs.map (fun b => 2 ^ b - 1)).map (fun v => valFrom (bitsOf v) 1)).sum
      = valSum bs := by
    rw [List.map_map]
    have hfun : (Function.comp (fun v => valFrom (bitsOf v) 1) (fun b => 2 ^ b - 1))
        = (fun b => (2 : ℤ) ^ b - 1) := by
      funext b
      rw [Function.comp_apply, bitsOf_two_pow_sub_one, valFrom_replicate_true]
      ring
    rw [hfun]
    unfold valSum
    rfl
  rw [h2] at h1
  exact h1


end Mp
