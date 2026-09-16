/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/


import Mp.CBTM
import Mp.IVM
import Mp.SubsetSumVerifierCore

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
# Sym 验证器 → F4 层（CBTM）的编译层
将 Sym 层验证器 `VerifierSym`（Sym 符号、Sym 磁带）编译为 F4 层
CBTM（`Tape F4`，re/im 双磁带）。编译采用 4F4 展开：
- Sym 磁带的 1 格 = F4 磁带的 4 格；
- 格 0-2 依次承载 kindBits 的 (re₁, re₂, re₃)（im 恒 false）；
- 格 3 承载 (mark, im₁)：im₁ 是分支位——im=true 的读恰发生在
  合成步（phase 3），此时 VerifierSym.transition 恰好给 2 个结果
  （α/β 双分支），从而满足 CBTM 的分支公理；
- Sym 的 1 个转移步 = CBTM 的 12 个转移步（4 读 + 4 写 + 4 移动）。
状态寄存器编码：`(q, phase, reg)`，q = Sym 状态（0..101），
phase = 0..11，reg = 读缓冲（0..63，phase 0-2）或转移结果编码
（phase 3 之后）。

设计备注（分支公理/投影约束/良构性可证性的要求）：
- Sym 状态钳制 `qs = min q 101`：q ≥ 101 时 VerifierSym.transition
  与 q = 101（catch-all `{ret 101 s S}`）行为一致，钳制不改变任何
  可达配置的语义，但使所有公理对任意自然数状态可证；
- 非法编码（symOf4F4 = none）与 phase ≥ 12 分支不再返回 ∅，而是
  返回单例恢复步（写回原符号），保证虚部 false 读恰 1 个结果。
-/

namespace Mp
open CBTM
namespace SymToF4
/-- Sym → 4 个 F4 的编译编码（分支位 im₁ 置于第 4 格）。 -/
def symTo4F4 (s : Sym) : List F4 :=
  let (r1, i1, r2, r3) := Sym.kindBits s.1
  [(r1, false), (r2, false), (r3, false), (s.2, i1)]
/-- symTo4F4 的长度恒为 4。 -/
@[simp] lemma symTo4F4_length (s : Sym) : (symTo4F4 s).length = 4 := rfl
/-- 4 个 F4 → Sym（symTo4F4 的逆；非法编码返回 none）。 -/
def symOf4F4 (a b c d : F4) : Option Sym :=
  if a.2 ∨ b.2 ∨ c.2 then none else
  let r1 := a.1; let r2 := b.1; let r3 := c.1; let i1 := d.2; let m := d.1
  match (r1, i1, r2, r3) with
  | (false, false, false, false) => some (Sym.data0 m)
  | (true, false, false, false) => some (Sym.data1 m)
  | (false, true, false, false) => some (Sym.mk SymKind.alpha m)           -- m 分立：不参与 kind 解码
  | (false, false, false, true) => some (Sym.mk SymKind.consumed m)
  | (true, false, true, true) => some (Sym.mk SymKind.boundary m)          -- boundary（m=mark：#₁ 标记后 m=true）
  | (false, false, true, false) => some (Sym.mk SymKind.sel m)
  | (false, false, true, true) => some (Sym.mk SymKind.nosel m)
  | (true, true, true, false) => some (Sym.mk SymKind.beta m)
  | _ => none
/-- symOf4F4 是 symTo4F4 的右逆（对 4F4.4 位为 false 的规范符号）。 -/
lemma symOf4F4_symTo4F4 (s : Sym) (hmark : s.2 = false) :
    match symTo4F4 s with
    | [a, b, c, d] => symOf4F4 a b c d = some s
    | _ => False := by
  rcases s with ⟨k, m⟩
  cases m with
  | false =>
      cases k <;> simp [symTo4F4, Sym.kindBits, symOf4F4, Sym.data0, Sym.data1, Sym.alpha, Sym.beta,
        Sym.boundary, Sym.sel, Sym.nosel, Sym.consumed, Sym.mk]
  | true => simp at hmark
/-- symTo4F4 的第 0-2 格 im 恒为 false。 -/
@[simp] lemma symTo4F4_im_false_012 (s : Sym) :
    (symTo4F4 s)[0].2 = false ∧ (symTo4F4 s)[1].2 = false ∧ (symTo4F4 s)[2].2 = false := by
  rcases s with ⟨k, m⟩
  cases k <;> cases m <;> simp [symTo4F4, Sym.kindBits]
/-- 非分支符号的 symTo4F4 末格虚部恒 false。 -/
lemma symTo4F4_getLastD_im_false_of_notBranch (s : Sym) (hnb : ¬ Sym.isBranch s) :
    F4.im ((symTo4F4 s).getLastD F4.zero) = false := by
  rcases s with ⟨k, mk⟩
  cases k <;> simp [symTo4F4, Sym.kindBits, Sym.isBranch, SymKind.isBranch, F4.im] at hnb ⊢
/-- symOf4F4 在 d 虚部为 false 时绝不返回分支符号。 -/
lemma symOf4F4_some_notBranch (a b c d : F4) (him : F4.im d = false) (sym : Sym)
    (h : symOf4F4 a b c d = some sym) : ¬ Sym.isBranch sym := by
  rcases a with ⟨ra, ia⟩ <;> rcases b with ⟨rb, ib⟩ <;> rcases c with ⟨rc, ic⟩ <;>
    rcases d with ⟨m, id⟩
  cases ra <;> cases ia <;> cases rb <;> cases ib <;> cases rc <;> cases ic <;> cases m <;> cases id <;>
    simp [F4.im, symOf4F4] at him h
  all_goals (cases h; simp [Sym.isBranch, SymKind.isBranch, Sym.mk, Sym.data0, Sym.data1,
    Sym.alpha, Sym.beta, Sym.consumed, Sym.boundary, Sym.sel, Sym.nosel])
/-- 4F4 展平：Sym 串 → F4 串。 -/
def flat4F4 (l : List Sym) : List F4 :=
  l.flatMap symTo4F4
/-- 子集和实例的 4F4 编译输入。 -/
def encodeInstanceF4 (inst : SubsetSumInstance) : List F4 :=
  flat4F4 (encodeInstanceSym inst)
-- ============================================================================
-- 状态机编码
-- ============================================================================
abbrev qBound : ℕ := 102
abbrev stepsPerSym : ℕ := 12
abbrev regBound : ℕ := 8192
def encodeState (q phase reg : ℕ) : ℕ :=
  q * stepsPerSym * regBound + phase * regBound + reg
def decodeState (n : ℕ) : ℕ × ℕ × ℕ :=
  (n / (stepsPerSym * regBound), (n / regBound) % stepsPerSym, n % regBound)
/-- 3 个 F4 的缓冲编码。 -/
def bufOf3 (a b c : F4) : ℕ :=
  let e (s : F4) : ℕ := if s = F4.zero then 0 else if s = F4.one then 1 else if s = F4.alpha then 2 else 3
  e a + 4 * e b + 16 * e c
/-- 缓冲解码。 -/
def f4ofBuf (n : ℕ) : F4 × F4 × F4 :=
  let d (m : ℕ) : F4 := match m % 4 with
    | 0 => F4.zero | 1 => F4.one | 2 => F4.alpha | _ => F4.beta
  (d n, d (n / 4), d (n / 16))
@[simp] lemma f4ofBuf_bufOf3 (a b c : F4) : f4ofBuf (bufOf3 a b c) = (a, b, c) := by
  rcases a with ⟨ra, ia⟩ <;> rcases b with ⟨rb, ib⟩ <;> rcases c with ⟨rc, ic⟩ <;>
    cases ra <;> cases ia <;> cases rb <;> cases ib <;> cases rc <;> cases ic <;>
    decide
/-- SymKind 的 sk 编码（0..8）。 -/
def skOf (k : SymKind) : ℕ := match k with
  | SymKind.data0 => 0 | SymKind.data1 => 1 | SymKind.alpha => 2
  | SymKind.consumed => 3 | SymKind.boundary => 4 | SymKind.sel => 5
  | SymKind.nosel => 6 | SymKind.beta => 7

/-- Dir 的编码（0..2）。 -/
def dirOf (d : Dir) : ℕ := match d with | Dir.R => 0 | Dir.L => 1 | Dir.S => 2

/-- 转移结果编码。 -/
def encodeResult (r : SymTransResult) : ℕ :=
  let sk' := skOf r.writeSym.1 + (if r.writeSym.2 then 9 else 0)
  r.nextState * 54 + sk' * 3 + dirOf r.moveDir
def decodeResult (n : ℕ) : SymTransResult :=
  let q := n / 54
  let sk' := (n / 3) % 18
  let dir := match n % 3 with | 0 => Dir.R | 1 => Dir.L | _ => Dir.S
  let s : Sym := match sk' % 9 with
    | 0 => Sym.data0 (sk' ≥ 9)
    | 1 => Sym.data1 (sk' ≥ 9)
    | 2 => if sk' ≥ 9 then Sym.mk SymKind.alpha true else Sym.alpha
    | 3 => if sk' ≥ 9 then Sym.mk SymKind.consumed true else Sym.consumed
    | 4 => if sk' ≥ 9 then Sym.mk SymKind.boundary true else Sym.boundary  -- boundary（恢复 mark）
    | 5 => if sk' ≥ 9 then Sym.mk SymKind.sel true else Sym.sel
    | 6 => if sk' ≥ 9 then Sym.mk SymKind.nosel true else Sym.nosel
    | _ => if sk' ≥ 9 then Sym.mk SymKind.beta true else Sym.beta
  SymTransResult.mk q s dir
/-- 状态 2 读无标记 α 恰好 2 个转移结果（β 与带标记 α 读到即陷阱）。 -/
lemma transition_card_two_of_branch (s : Sym) (hα : s.1 = SymKind.alpha) (hm : s.2 = false) :
    (VerifierSym.transition (2, s)).card = 2 := by
  rcases s with ⟨k, mk⟩
  have hk : k = SymKind.alpha := by simpa using hα
  subst k
  have hmk : mk = false := by simpa using hm
  subst mk
  rw [VerifierSym.transition, if_pos (by decide : 2 ∈ VerifierSym.legalStates)]
  decide
/-- q ∈ [4,22] 非分支读：转移结果单元素（card = 1）。 -/
lemma transition_singleton_ge4 (q : ℕ) (s : Sym)
    (hq : 4 ≤ q ∧ q ≤ 22) (hnb : ¬ Sym.isBranch s) :
    (VerifierSym.transition (q, s)).card = 1 := by
  have hq2 := hq.2
  interval_cases q <;> rcases s with ⟨k, mk⟩ <;> cases k <;> cases mk
  all_goals (first | decide | (simp [Sym.isBranch, SymKind.isBranch] at hnb))

lemma transition_card_one_of_notBranch_bounded (q : ℕ) (s : Sym) (hq : q ≤ 101)
    (hnb : ¬ Sym.isBranch s) :
    (VerifierSym.transition (q, s)).card = 1 := by
  by_cases h4 : 4 ≤ q
  · by_cases h22 : q ≤ 22
    · exact transition_singleton_ge4 q s ⟨h4, h22⟩ hnb
    · have h23 : 23 ≤ q := by omega
      interval_cases q <;> rcases s with ⟨k, mk⟩ <;> cases k <;> cases mk
      all_goals decide
  · have hlt4 : q < 4 := by omega
    interval_cases q <;> rcases s with ⟨k, mk⟩ <;> cases k <;> cases mk
    all_goals (first | decide | (simp [Sym.isBranch, SymKind.isBranch] at hnb))
set_option maxHeartbeats 8000000 in
/-- 转移表中任何结果行的 nextState ≤ 101（q ≤ 101）。 -/
theorem transition_nextState_le101 (q : ℕ) (s : Sym) (hq : q ≤ 101) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) : r.nextState ≤ 101 := by
  have hdec : (∀ q ≤ 101, ∀ s : Sym, ∀ r, r ∈ VerifierSym.transition (q, s) → r.nextState ≤ 101) := by
    native_decide
  exact hdec q hq s r hr
set_option maxHeartbeats 8000000 in
/-- 非分支读的转移结果写非分支符号。 -/
theorem transition_write_notBranch (q : ℕ) (s : Sym) (hq : q ≤ 101) (hnb : ¬ Sym.isBranch s)
    (r : SymTransResult) (hr : r ∈ VerifierSym.transition (q, s)) : ¬ Sym.isBranch r.writeSym := by
  have hdec : (∀ q ≤ 101, ∀ s : Sym, ¬ Sym.isBranch s → ∀ r, r ∈ VerifierSym.transition (q, s) → ¬ Sym.isBranch r.writeSym) := by
    native_decide
  exact hdec q hq s hnb r hr
/-- 读阶段缓冲增量：符号 e ∈ {0,1,2,3} × 4^phase。 -/
def bufOf3s (phase : ℕ) (s : F4) (reg : ℕ) : ℕ :=
  let e : ℕ := if s = F4.zero then 0 else if s = F4.one then 1 else if s = F4.alpha then 2 else 3
  e * (4 ^ phase)
/-- 4F4 编译的转移函数（Sym 状态钳制 qs = min q 101，见文件头设计备注）。 -/
def transition4 (st : ℕ) (s : F4) : Finset CBTMTransResult :=
  let (q, phase, reg) := decodeState st
  let qs := min q 101
  let R := Dir.R; let L := Dir.L; let S := Dir.S
  let ret (ns : ℕ) (w : F4) (d : Dir) := CBTMTransResult.mk ns w d
  let nphase := (if phase = 11 then 0 else phase + 1)
  let trap := {ret (encodeState 101 nphase 0) s S, ret (encodeState 101 nphase 0) s R}
  let trap1 := {ret (encodeState 101 nphase 0) s S}
  if phase < 3 then
    -- 读阶段 0-2：缓冲、写回原符号、右移（im=true 的读为非法输入，进陷阱）
    if F4.im s then trap
    else {ret (encodeState qs (phase + 1) (reg + bufOf3s phase s reg)) s R}
  else if phase = 3 then
    -- 合成 Sym、查表、写回第 4 格
    let (a, b, c) := f4ofBuf reg
    match symOf4F4 a b c s with
    | none => (if F4.im s then trap else trap1)
    | some sym =>
        let rs := VerifierSym.transition (qs, sym)
        if F4.im s then
          if qs = 2 ∧ (f4ofBuf reg).1 = F4.zero ∧ F4.re s = false then
            let rsel := SymTransResult.mk 2 Sym.sel Dir.R
            let rnosel := SymTransResult.mk 2 Sym.nosel Dir.R
            {ret (encodeState 2 4 (encodeResult rsel)) ((symTo4F4 Sym.sel).getLastD F4.zero) L,
             ret (encodeState 2 4 (encodeResult rnosel)) ((symTo4F4 Sym.nosel).getLastD F4.zero) L}
          else trap
        else
          rs.image (fun r : SymTransResult =>
            ret (encodeState r.nextState 4 (encodeResult r)) ((symTo4F4 r.writeSym).getLastD F4.zero) L)
  else if phase < 8 then
    -- 写回阶段 4-7：依次写第 2/1/0 格（第 3 格已在 phase 3 写回），phase 7 写回原符号
    if F4.im s then trap
    else
      let r := decodeResult reg
      let l := symTo4F4 r.writeSym
      if phase = 4 then {ret (encodeState qs 5 reg) (l.getD 2 F4.zero) L}
      else if phase = 5 then {ret (encodeState qs 6 reg) (l.getD 1 F4.zero) L}
      else if phase = 6 then {ret (encodeState qs 7 reg) (l.getD 0 F4.zero) S}
      else {ret (encodeState qs 8 reg) s S}
  else if phase < 12 then
    -- 移动阶段 8-11：按 r 的方向移动（写回原符号）
    -- 读 im=true 的格也必须是 2 结果（分支公理）：好路径照常移动，坏路径进陷阱
    let r := decodeResult reg
    let d := match r.moveDir with | Dir.R => R | Dir.L => L | Dir.S => S
    let nst := encodeState
      (if phase = 11 then (if (decodeState st).1 = 101 then 101 else min r.nextState 101) else qs)
      (if phase = 11 then 0 else nphase) (if phase = 11 then 0 else reg)
    if F4.im s then {ret nst s d, ret (encodeState 101 nphase 0) F4.zero S}
    else if (decodeState st).1 = 101 then {ret (encodeState 101 nphase 0) s S}
    else {ret nst s d}
  else
    (if F4.im s then trap else trap1)
/-- 陷阱的两结果基数。 -/
lemma trap_card (phase : ℕ) (s : F4) :
    ({CBTMTransResult.mk (encodeState 101 (if phase = 11 then 0 else phase + 1) 0) s Dir.S,
      CBTMTransResult.mk (encodeState 101 (if phase = 11 then 0 else phase + 1) 0) s Dir.R}
      : Finset CBTMTransResult).card = 2 := by
  rw [Finset.card_eq_two]
  refine ⟨CBTMTransResult.mk (encodeState 101 (if phase = 11 then 0 else phase + 1) 0) s Dir.S,
    CBTMTransResult.mk (encodeState 101 (if phase = 11 then 0 else phase + 1) 0) s Dir.R, ?_, ?_⟩
  · intro h
    have hd := congrArg CBTMTransResult.moveDir h
    simp [Dir.S, Dir.R] at hd
  · ext c
    constructor <;> intro hc <;> simp at hc ⊢ <;> rcases hc with rfl | rfl <;> simp

/-- 移动阶段读 im=true 的双结果基数。 -/
lemma move_card (nst : ℕ) (s : F4) (d : Dir) (nph : ℕ) (him : F4.im s) :
    ({CBTMTransResult.mk nst s d, CBTMTransResult.mk (encodeState 101 nph 0) F4.zero Dir.S} :
      Finset CBTMTransResult).card = 2 := by
  rw [Finset.card_eq_two]
  refine ⟨CBTMTransResult.mk nst s d, CBTMTransResult.mk (encodeState 101 nph 0) F4.zero Dir.S,
    ?_, ?_⟩
  · intro h
    have hw := congrArg CBTMTransResult.writeSym h
    dsimp at hw
    rw [hw] at him
    simp [F4.im, F4.zero] at him
  · ext c
    constructor <;> intro hc <;> simp at hc ⊢ <;> rcases hc with rfl | rfl <;> simp

/-- transition4 读 im=true 的符号恒给 2 个结果。 -/
lemma transition4_card_branch (st : ℕ) (s : F4) (him : F4.im s) :
    (transition4 st s).card = 2 := by
  dsimp [transition4, decodeState]
  by_cases hph : (st / regBound) % stepsPerSym < 3
  · simp [hph, him, trap_card]
  · by_cases hph3 : (st / regBound) % stepsPerSym = 3
    · simp [hph, hph3, him]
      rcases hsym : symOf4F4 ((f4ofBuf (st % regBound)).1) ((f4ofBuf (st % regBound)).2.1)
          ((f4ofBuf (st % regBound)).2.2) s with _ | sym
      · simp [trap_card]
      · by_cases hq2 : min (st / (stepsPerSym * regBound)) 101 = 2 ∧ (f4ofBuf (st % regBound)).1 = F4.zero ∧ F4.re s = false
        · simp [hq2]
          decide
        · simp [hq2, trap_card]
    · by_cases hph8 : (st / regBound) % stepsPerSym < 8
      · simp [hph, hph3, hph8, him, trap_card]
      · by_cases hph12 : (st / regBound) % stepsPerSym < 12
        · simp [hph, hph3, hph8, hph12, him]
          by_cases h11 : st / regBound % stepsPerSym = 11 <;> simp [h11] <;>
            exact move_card _ _ _ _ him
        · exfalso
          exact hph12 (Nat.mod_lt _ (by decide : 0 < stepsPerSym))
/-- transition4 读 im=false 的符号恒给 1 个结果（分支公理/投影约束的 im=false 半支）。 -/
lemma transition4_card_one_of_im_false (st : ℕ) (s : F4) (him : F4.im s = false) :
    (transition4 st s).card = 1 := by
  dsimp [transition4, decodeState]
  by_cases hph : (st / regBound) % stepsPerSym < 3
  · simp [hph, him, Finset.card_singleton]
  · by_cases hph3 : (st / regBound) % stepsPerSym = 3
    · simp [hph, hph3, him]
      rcases hsym : symOf4F4 ((f4ofBuf (st % regBound)).1) ((f4ofBuf (st % regBound)).2.1)
          ((f4ofBuf (st % regBound)).2.2) s with _ | sym
      · simp [Finset.card_singleton]
      · dsimp
        have hqs : min (st / (stepsPerSym * regBound)) 101 ≤ 101 := Nat.min_le_right _ _
        have hnb : ¬ Sym.isBranch sym :=
          symOf4F4_some_notBranch ((f4ofBuf (st % regBound)).1) ((f4ofBuf (st % regBound)).2.1)
            ((f4ofBuf (st % regBound)).2.2) s him sym hsym
        have hc := transition_card_one_of_notBranch_bounded (min (st / (stepsPerSym * regBound)) 101) sym hqs hnb
        rcases (Finset.card_eq_one.mp hc) with ⟨r₀, hr₀⟩
        rw [hr₀]
        simp [Finset.image_singleton, Finset.card_singleton]
    · by_cases hph8 : (st / regBound) % stepsPerSym < 8
      · by_cases h4 : (st / regBound) % stepsPerSym = 4 <;>
          by_cases h5 : (st / regBound) % stepsPerSym = 5 <;>
          by_cases h6 : (st / regBound) % stepsPerSym = 6 <;>
          simp [hph, hph3, hph8, h4, h5, h6, him, Finset.card_singleton]
      · by_cases hph12 : (st / regBound) % stepsPerSym < 12
        · by_cases h11 : (st / regBound) % stepsPerSym = 11 <;>
            by_cases hq101 : st / (stepsPerSym * regBound) = 101 <;>
            simp [hph, hph3, hph8, hph12, h11, him, hq101, Finset.card_singleton]
        · exfalso
          exact hph12 (Nat.mod_lt _ (by decide : 0 < stepsPerSym))
/-- transition4 读 im=false 的符号时写回符号的虚部恒 false。 -/
lemma transition4_write_im_false (st : ℕ) (s : F4) (him : F4.im s = false) (r : CBTMTransResult)
    (hr : r ∈ transition4 st s) : F4.im r.writeSym = false := by
  dsimp [transition4, decodeState] at hr
  by_cases hph : (st / regBound) % stepsPerSym < 3
  · simp [hph, him] at hr
    rcases hr with rfl
    simpa [him]
  · by_cases hph3 : (st / regBound) % stepsPerSym = 3
    · simp [hph, hph3, him] at hr
      split at hr
      case h_1 =>
        rcases r with ⟨n, w, d⟩
        simp_all
      case h_2 val heq =>
        simp [Finset.mem_image] at hr
        obtain ⟨r0, hr0, hf⟩ := hr
        rw [← hf]
        have hnb : ¬ Sym.isBranch val :=
          symOf4F4_some_notBranch ((f4ofBuf (st % regBound)).1) ((f4ofBuf (st % regBound)).2.1)
            ((f4ofBuf (st % regBound)).2.2) s him val heq
        have hw := transition_write_notBranch (min (st / (stepsPerSym * regBound)) 101) val (Nat.min_le_right _ _) hnb r0 hr0
        exact symTo4F4_getLastD_im_false_of_notBranch r0.writeSym hw
    · by_cases hph8 : (st / regBound) % stepsPerSym < 8
      · by_cases h4 : (st / regBound) % stepsPerSym = 4
        · simp [hph, hph3, hph8, h4, him] at hr
          rcases hr with rfl
          have hcell : F4.im ((symTo4F4 (decodeResult (st % regBound)).writeSym).getD 2 F4.zero) = false := by
            simpa [List.getD, symTo4F4_length] using (symTo4F4_im_false_012 (decodeResult (st % regBound)).writeSym).2.2
          simpa [hcell]
        · by_cases h5 : (st / regBound) % stepsPerSym = 5
          · simp [hph, hph3, hph8, h4, h5, him] at hr
            rcases hr with rfl
            have hcell : F4.im ((symTo4F4 (decodeResult (st % regBound)).writeSym).getD 1 F4.zero) = false := by
              simpa [List.getD, symTo4F4_length] using (symTo4F4_im_false_012 (decodeResult (st % regBound)).writeSym).2.1
            simpa [hcell]
          · by_cases h6 : (st / regBound) % stepsPerSym = 6
            · simp [hph, hph3, hph8, h4, h5, h6, him] at hr
              rcases hr with rfl
              have hcell : F4.im ((symTo4F4 (decodeResult (st % regBound)).writeSym).getD 0 F4.zero) = false := by
                simpa [List.getD, symTo4F4_length] using (symTo4F4_im_false_012 (decodeResult (st % regBound)).writeSym).1
              simpa [hcell]
            · simp [hph, hph3, hph8, h4, h5, h6, him] at hr
              rcases hr with rfl
              simpa [him]
      · by_cases hph12 : (st / regBound) % stepsPerSym < 12
        · by_cases h11 : (st / regBound) % stepsPerSym = 11
          · by_cases hq101 : st / (stepsPerSym * regBound) = 101
            · simp [hph, hph3, hph8, hph12, h11, him, hq101] at hr
              rcases hr with rfl
              simpa [him]
            · simp [hph, hph3, hph8, hph12, h11, him, hq101] at hr
              rcases hr with rfl
              simpa [him]
          · by_cases hq101 : st / (stepsPerSym * regBound) = 101
            · simp [hph, hph3, hph8, hph12, h11, him, hq101] at hr
              rcases hr with rfl
              simpa [him]
            · simp [hph, hph3, hph8, hph12, h11, him, hq101] at hr
              rcases hr with rfl
              simpa [him]
        · exfalso
          exact hph12 (Nat.mod_lt _ (by decide : 0 < stepsPerSym))
/-- 编译后的接受态：q = qAccept、phase = 0。 -/
def acceptStates4 : Finset ℕ :=
  (Finset.range regBound).image (fun reg => encodeState VerifierSym.qAccept 0 reg)
def rejectStates4 : Finset ℕ :=
  (Finset.range regBound).image (fun reg => encodeState VerifierSym.qReject 0 reg)
def states4 : Finset ℕ :=
  Finset.range (qBound * stepsPerSym * regBound)
/-- 4F4 编译的 CBTM 验证器。 -/
def subsetSumCBTM : CBTM := {
  states := states4
  startState := encodeState VerifierSym.qStart 0 0
  acceptStates := acceptStates4
  rejectStates := rejectStates4
  alphabet := {F4.zero, F4.one, F4.alpha, F4.beta}
  transition := fun p => transition4 p.1 p.2.1
  blankSym := F4.zero
  h_blank_in_alphabet := by simp [F4.zero]
  h_start_in_states := by
    dsimp [states4, encodeState, VerifierSym.qStart, qBound, stepsPerSym, regBound]
    norm_num
  h_accept_subset := by
    intro q hq
    dsimp [acceptStates4] at hq
    rcases Finset.mem_image.mp hq with ⟨reg, hreg, rfl⟩
    dsimp [states4, encodeState, VerifierSym.qAccept, qBound, stepsPerSym, regBound]
    rw [Finset.mem_range]
    have hlt : reg < 8192 := by
      simpa [regBound] using (Finset.mem_range.mp hreg)
    omega
  h_reject_subset := by
    intro q hq
    dsimp [rejectStates4] at hq
    rcases Finset.mem_image.mp hq with ⟨reg, hreg, rfl⟩
    dsimp [states4, encodeState, VerifierSym.qReject, qBound, stepsPerSym, regBound]
    rw [Finset.mem_range]
    have hlt : reg < 8192 := by
      simpa [regBound] using (Finset.mem_range.mp hreg)
    omega
  h_accept_reject_disjoint := by
    ext q
    constructor <;> intro hq
    · rw [Finset.mem_inter] at hq
      rcases hq with ⟨hqa, hqr⟩
      dsimp [acceptStates4, rejectStates4] at hqa hqr
      rcases Finset.mem_image.mp hqa with ⟨ra, hra, hra'⟩
      rcases Finset.mem_image.mp hqr with ⟨rr, hrr, hrr'⟩
      dsimp [encodeState, VerifierSym.qAccept, VerifierSym.qReject, qBound, stepsPerSym, regBound]
        at hra' hrr'
      have hra_lt : ra < 8192 := by
        simpa [regBound] using (Finset.mem_range.mp hra)
      have hrr_lt : rr < 8192 := by
        simpa [regBound] using (Finset.mem_range.mp hrr)
      omega
    · simpa using hq
  h_branch_rule := by
    intro q s i hs
    have h4 : s = F4.zero ∨ s = F4.one ∨ s = F4.alpha ∨ s = F4.beta := by
      simpa [F4.zero, F4.one, F4.alpha, F4.beta] using hs
    rcases h4 with rfl | rfl | rfl | rfl
    · simpa [F4.im, F4.zero] using transition4_card_one_of_im_false q F4.zero rfl
    · simpa [F4.im, F4.one] using transition4_card_one_of_im_false q F4.one rfl
    · simpa [F4.im, F4.alpha] using transition4_card_branch q F4.alpha rfl
    · simpa [F4.im, F4.beta] using transition4_card_branch q F4.beta rfl
  h_projection_constraint := by
    intro q s i hs him
    have h4 : s = F4.zero ∨ s = F4.one := by
      have h4' : s = F4.zero ∨ s = F4.one ∨ s = F4.alpha ∨ s = F4.beta := by
        simpa [F4.zero, F4.one, F4.alpha, F4.beta] using hs
      rcases h4' with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · simp [F4.im, F4.alpha] at him
      · simp [F4.im, F4.beta] at him
    rcases h4 with rfl | rfl
    · constructor
      · exact transition4_card_one_of_im_false q F4.zero rfl
      · intro r hr
        exact transition4_write_im_false q F4.zero rfl r hr
    · constructor
      · exact transition4_card_one_of_im_false q F4.one rfl
      · intro r hr
        exact transition4_write_im_false q F4.one rfl r hr
  isValid := by
    intro q s i hs r hr
    dsimp [transition4, decodeState] at hr
    have hqmin : min (q / (stepsPerSym * regBound)) 101 ≤ 101 := Nat.min_le_right _ _
    have hreglt : q % regBound < regBound := Nat.mod_lt _ (by decide : 0 < regBound)
    by_cases hph : (q / regBound) % stepsPerSym < 3
    · by_cases him : F4.im s <;> simp [hph, him] at hr
      · rcases hr with h1 | h1
        · subst r
          dsimp [states4, encodeState, qBound, stepsPerSym, regBound]
          rw [Finset.mem_range]
          have hphL : (q / 8192) % 12 < 3 := by
            simpa [stepsPerSym, regBound] using hph
          by_cases h11 : (q / 8192) % 12 = 11 <;> simp [h11] <;> omega
        · subst r
          dsimp [states4, encodeState, qBound, stepsPerSym, regBound]
          rw [Finset.mem_range]
          have hphL : (q / 8192) % 12 < 3 := by
            simpa [stepsPerSym, regBound] using hph
          by_cases h11 : (q / 8192) % 12 = 11 <;> simp [h11] <;> omega
      · rcases r with ⟨n, w, d⟩
        simp_all
        dsimp [states4, encodeState, qBound, stepsPerSym, regBound]
        rw [Finset.mem_range]
        have hph2 : (q / regBound) % stepsPerSym ≤ 2 := by omega
        have hbuf : bufOf3s ((q / regBound) % stepsPerSym) s (q % regBound) ≤ 48 := by
          unfold bufOf3s
          have hle : (q / regBound) % stepsPerSym ≤ 2 := by omega
          have hpow : 4 ^ ((q / regBound) % stepsPerSym) ≤ 16 := by
            interval_cases ((q / regBound) % stepsPerSym) <;> norm_num
          rcases s with ⟨rs, is⟩
          cases rs <;> cases is <;> simp [F4.zero, F4.one, F4.alpha, F4.beta]
          all_goals nlinarith [hpow]
        have hqminL : min (q / 98304) 101 ≤ 101 := by
          simpa [stepsPerSym, regBound] using hqmin
        have hbufL : bufOf3s ((q / 8192) % 12) s (q % 8192) ≤ 48 := by
          simpa [stepsPerSym, regBound] using hbuf
        have hmodL : q % 8192 < 8192 := by
          simpa [regBound] using hreglt
        have hph2L : (q / 8192) % 12 ≤ 2 := by
          simpa [stepsPerSym, regBound] using hph2
        omega
    · by_cases hph3 : (q / regBound) % stepsPerSym = 3
      · by_cases him : F4.im s <;> simp [hph, hph3, him] at hr
        · split at hr
          · simp [him] at hr
            rcases hr with h1 | h1
            · subst r
              dsimp [states4, encodeState, qBound, stepsPerSym, regBound]
              rw [Finset.mem_range]
              by_cases h11 : (q / 8192) % 12 = 11 <;> simp [h11] at * <;> omega
            · subst r
              dsimp [states4, encodeState, qBound, stepsPerSym, regBound]
              rw [Finset.mem_range]
              by_cases h11 : (q / 8192) % 12 = 11 <;> simp [h11] at * <;> omega
          · by_cases hq2 : min (q / (stepsPerSym * regBound)) 101 = 2 ∧ (f4ofBuf (q % regBound)).1 = F4.zero ∧ F4.re s = false <;> simp [hq2] at hr
            · rcases hr with h1 | h1
              · subst r
                dsimp [states4, encodeState, encodeResult, skOf, dirOf, Sym.sel, Sym.nosel, Sym.mk,
                  qBound, stepsPerSym, regBound]
                rw [Finset.mem_range]
                omega
              · subst r
                dsimp [states4, encodeState, encodeResult, skOf, dirOf, Sym.sel, Sym.nosel, Sym.mk,
                  qBound, stepsPerSym, regBound]
                rw [Finset.mem_range]
                omega
            · rcases hr with h1 | h1
              · subst r
                dsimp [states4, encodeState, qBound, stepsPerSym, regBound]
                rw [Finset.mem_range]
                by_cases h11 : (q / 8192) % 12 = 11 <;> simp [h11] at * <;> omega
              · subst r
                dsimp [states4, encodeState, qBound, stepsPerSym, regBound]
                rw [Finset.mem_range]
                by_cases h11 : (q / 8192) % 12 = 11 <;> simp [h11] at * <;> omega
        · split at hr
          case h_1 =>
            rcases r with ⟨n, w, d⟩
            simp_all
            dsimp [states4, encodeState, qBound, stepsPerSym, regBound]
            rw [Finset.mem_range]
            by_cases h11 : (q / 8192) % 12 = 11 <;> simp [h11] at * <;> omega
          case h_2 val heq =>
            simp [Finset.mem_image] at hr
            obtain ⟨r0, hr0, hf⟩ := hr
            rw [← hf]
            have hnext := transition_nextState_le101 (min (q / (stepsPerSym * regBound)) 101) val (Nat.min_le_right _ _) r0 hr0
            dsimp [states4, encodeState, encodeResult, qBound, stepsPerSym, regBound]
            rw [Finset.mem_range]
            rcases r0 with ⟨n0, w0, d0⟩
            rcases w0 with ⟨k0, m0⟩
            cases k0 <;> cases m0 <;> cases d0
            all_goals
              have hnextL : n0 ≤ 101 := by simpa using hnext
              simp [encodeResult, skOf, dirOf]
              omega
      · by_cases hph8 : (q / regBound) % stepsPerSym < 8
        · by_cases him : F4.im s <;> simp [hph, hph3, hph8, him] at hr
          · rcases hr with h1 | h1
            · subst r
              dsimp [states4, encodeState, qBound, stepsPerSym, regBound]
              rw [Finset.mem_range]
              have hph8L : (q / 8192) % 12 < 8 := by
                simpa [stepsPerSym, regBound] using hph8
              by_cases h11 : (q / 8192) % 12 = 11 <;> simp [h11] <;> omega
            · subst r
              dsimp [states4, encodeState, qBound, stepsPerSym, regBound]
              rw [Finset.mem_range]
              have hph8L : (q / 8192) % 12 < 8 := by
                simpa [stepsPerSym, regBound] using hph8
              by_cases h11 : (q / 8192) % 12 = 11 <;> simp [h11] <;> omega
          · by_cases h4 : (q / regBound) % stepsPerSym = 4 <;>
              by_cases h5 : (q / regBound) % stepsPerSym = 5 <;>
              by_cases h6 : (q / regBound) % stepsPerSym = 6 <;>
              simp [h4, h5, h6] at hr
            all_goals
              subst r
              dsimp [states4, encodeState, qBound, stepsPerSym, regBound]
              rw [Finset.mem_range]
              have hqminL : min (q / 98304) 101 ≤ 101 := by
                simpa [stepsPerSym, regBound] using hqmin
              have hmodL : q % 8192 < 8192 := by
                simpa [regBound] using hreglt
              omega
        · by_cases hph12 : (q / regBound) % stepsPerSym < 12
          · by_cases him : F4.im s <;> simp [hph, hph3, hph8, hph12, him] at hr
            · rcases hr with h1 | h1
              · subst r
                dsimp [states4, encodeState, qBound, stepsPerSym, regBound]
                rw [Finset.mem_range]
                have hph12L : (q / 8192) % 12 < 12 := by
                  simpa [stepsPerSym, regBound] using hph12
                by_cases h11 : (q / 8192) % 12 = 11
                · by_cases hq101 : q / 98304 = 101 <;> simp [h11, hq101] <;> omega
                · by_cases hq101 : q / 98304 = 101 <;> simp [h11, hq101] <;> omega
              · subst r
                dsimp [states4, encodeState, qBound, stepsPerSym, regBound]
                rw [Finset.mem_range]
                have hph12L : (q / 8192) % 12 < 12 := by
                  simpa [stepsPerSym, regBound] using hph12
                by_cases h11 : (q / 8192) % 12 = 11 <;> simp [h11] <;> omega
            · by_cases h11 : (q / regBound) % stepsPerSym = 11
              · by_cases hq101 : q / (stepsPerSym * regBound) = 101
                · simp [hph, hph3, hph8, hph12, h11, him, hq101] at hr
                  subst r
                  dsimp [states4, encodeState, qBound, stepsPerSym, regBound]
                  rw [Finset.mem_range]
                  have hmod : (q / 8192) % 12 < 12 := Nat.mod_lt _ (by decide : 0 < 12)
                  by_cases hq11' : (q / 8192) % 12 = 11
                  · simp [hq11']
                  · simp [hq11']
                · rcases r with ⟨n, w, d⟩
                  simp_all
                  dsimp [states4, encodeState, decodeResult, qBound, stepsPerSym, regBound]
                  rw [Finset.mem_range]
                  have hminL : min ((q % 8192) / 54) 101 ≤ 101 := Nat.min_le_right _ _
                  omega
              · by_cases hq101 : q / (stepsPerSym * regBound) = 101
                · simp [hph, hph3, hph8, hph12, h11, him, hq101] at hr
                  subst r
                  dsimp [states4, encodeState, qBound, stepsPerSym, regBound]
                  rw [Finset.mem_range]
                  have hmod : (q / 8192) % 12 < 12 := Nat.mod_lt _ (by decide : 0 < 12)
                  by_cases hq11' : (q / 8192) % 12 = 11
                  · simp [hq11'] at *
                  · simp [hq11']
                    have hm11 : (q / 8192) % 12 ≤ 10 := by omega
                    nlinarith [hm11]
                · rcases r with ⟨n, w, d⟩
                  simp_all
                  dsimp [states4, encodeState, qBound, stepsPerSym, regBound]
                  rw [Finset.mem_range]
                  have hqminL : min (q / 98304) 101 ≤ 101 := by
                    simpa [stepsPerSym, regBound] using hqmin
                  have hmodL : q % 8192 < 8192 := by
                    simpa [regBound] using hreglt
                  have hph12L : (q / 8192) % 12 < 12 := by
                    simpa [stepsPerSym, regBound] using hph12
                  have h11L : ¬ (q / 8192) % 12 = 11 := by
                    simpa [stepsPerSym, regBound] using h11
                  omega
          · exfalso
            exact hph12 (Nat.mod_lt _ (by decide : 0 < stepsPerSym))
  h_transition_outside := by
    intro q s i hs
    have h4 : s = F4.zero ∨ s = F4.one ∨ s = F4.alpha ∨ s = F4.beta := by
      by_contra h
      apply hs
      dsimp [F4.zero, F4.one, F4.alpha, F4.beta] at *
      rcases s with ⟨r, i⟩
      cases r <;> cases i <;> simp at h ⊢
    rcases h4 with rfl | rfl | rfl | rfl <;> simp at hs
}
end SymToF4

-- ======================================================================
-- 磁带语义中段路径与模拟构件（把 subsetSum_in_NP_F 由公理变为定理）
-- ======================================================================
namespace SymToF4

/-- CBTM 磁带语义的中段可达（从任意格局出发）。 -/
inductive TapeSteps (M : CBTM) (input : List F4) (cfg₀ : CBTMConfig M input) :
    ComputationPath → CBTMConfig M input → Prop
  | nil : TapeSteps M input cfg₀ [] cfg₀
  | cons : ∀ (π : ComputationPath) (step : TransitionStep) (cfg' : CBTMConfig M input),
      TapeSteps M input cfg₀ π cfg' →
      step.fromState = cfg'.state →
      step.readSym = cfg'.tapeAt cfg'.headPos →
      step.result ∈ M.transition (cfg'.state, cfg'.tapeAt cfg'.headPos, cfg'.headPos) →
      TapeSteps M input cfg₀ (π ++ [step]) (stepConfig cfg' step.result)

/-- TapeSteps 与 TapeReachablePath 一致（从初始配置出发）。 -/
lemma tapeSteps_initial_iff (M : CBTM) (input : List F4) (π : ComputationPath)
    (cfg : CBTMConfig M input) :
    TapeSteps M input (initialConfig M input) π cfg ↔ TapeReachablePath M input π cfg := by
  constructor <;> intro h
  · induction h
    · exact TapeReachablePath.nil
    · rename_i π₀ step cfg₁ h_ind h_from h_read h_trans ih
      exact TapeReachablePath.cons π₀ step cfg₁ ih h_from h_read h_trans
  · induction h
    · exact TapeSteps.nil
    · rename_i π₀ step cfg h_ind h_from h_read h_trans ih
      exact TapeSteps.cons π₀ step cfg ih h_from h_read h_trans

/-- TapeSteps 的传递性：路径拼接。 -/
lemma TapeSteps_trans (M : CBTM) (input : List F4) (cfg₀ cfg₁ cfg₂ : CBTMConfig M input)
    (π₁ π₂ : ComputationPath) :
    TapeSteps M input cfg₀ π₁ cfg₁ → TapeSteps M input cfg₁ π₂ cfg₂ →
    TapeSteps M input cfg₀ (π₁ ++ π₂) cfg₂ := by
  intro h₁ h₂
  induction h₂ generalizing π₁ with
  | nil => simpa using h₁
  | cons π₂' step cfg h_ind h_from h_read h_trans ih =>
      simpa [List.append_assoc] using TapeSteps.cons (π₁ ++ π₂') step cfg
        (ih π₁ h₁) h_from h_read h_trans

/-- symTo4F4 第 3 格 = 末格。 -/
lemma symTo4F4_getD3_eq_lastD (s : Sym) :
    (symTo4F4 s).getD 3 F4.zero = (symTo4F4 s).getLastD F4.zero := by
  unfold symTo4F4
  rcases s with ⟨k, mk⟩
  cases k <;> rfl

/-- encodeState/decodeState 往返（界内）。 -/
lemma decodeState_encodeState (q ph reg : ℕ) (hph : ph < stepsPerSym) (hr : reg < regBound) :
    decodeState (encodeState q ph reg) = (q, ph, reg) := by
  have hphL : ph < 12 := by simpa [stepsPerSym] using hph
  have hrL : reg < 8192 := by simpa [regBound] using hr
  have hdiv : (q * 12 * 8192 + ph * 8192 + reg) / (12 * 8192) = q := by omega
  have hmod : ((q * 12 * 8192 + ph * 8192 + reg) / 8192) % 12 = ph := by omega
  have hreg : (q * 12 * 8192 + ph * 8192 + reg) % 8192 = reg := by omega
  dsimp [decodeState, encodeState, stepsPerSym, regBound]
  ext <;> omega

/-- encodeResult/decodeResult 往返（标记只出现在 data0/data1）。 -/
lemma decodeResult_encodeResult (r : SymTransResult)
    (hvalid : r.writeSym.2 = true → r.writeSym.1 = SymKind.data0 ∨ r.writeSym.1 = SymKind.data1) :
    decodeResult (encodeResult r) = r := by
  rcases r with ⟨n, w, d⟩
  rcases w with ⟨k, mk⟩
  have hsk : skOf k + (if mk then 9 else 0) < 18 := by
    cases k <;> cases mk <;> simp [skOf]
  have hdir : dirOf d < 3 := by
    cases d <;> simp [dirOf]
  have hq : (encodeResult ⟨n, (k, mk), d⟩) / 54 = n := by
    change (n * 54 + (skOf k + (if mk then 9 else 0)) * 3 + dirOf d) / 54 = n
    omega
  have hsk2 : ((encodeResult ⟨n, (k, mk), d⟩) / 3) % 18 = skOf k + (if mk then 9 else 0) := by
    change ((n * 54 + (skOf k + (if mk then 9 else 0)) * 3 + dirOf d) / 3) % 18 =
      skOf k + (if mk then 9 else 0)
    omega
  have hdir2 : (encodeResult ⟨n, (k, mk), d⟩) % 3 = dirOf d := by
    change (n * 54 + (skOf k + (if mk then 9 else 0)) * 3 + dirOf d) % 3 = dirOf d
    omega
  cases mk with
  | false =>
      cases k <;> cases d
      all_goals simp [decodeResult, hq, hsk2, hdir2, skOf, dirOf, Sym.data0, Sym.data1,
        Sym.consumed, Sym.boundary, Sym.sel, Sym.nosel, Sym.alpha, Sym.beta, Sym.mk]
  | true =>
      rcases hvalid rfl with hk | hk
      · subst hk
        cases d
        all_goals simp [decodeResult, hq, hsk2, hdir2, skOf, dirOf, Sym.data0, Sym.mk]
      · subst hk
        cases d
        all_goals simp [decodeResult, hq, hsk2, hdir2, skOf, dirOf, Sym.data1, Sym.mk]

/-- 状态 2 读无标记 α 恰好给 sel/nosel 双结果（β 与带标记 α 读到即陷阱）。 -/
lemma transition2_branch_eq (s : Sym) (hα : s.1 = SymKind.alpha) (hm : s.2 = false) :
    VerifierSym.transition (2, s) = {SymTransResult.mk 2 Sym.sel Dir.R,
      SymTransResult.mk 2 Sym.nosel Dir.R} := by
  rcases s with ⟨k, mk⟩
  have hk : k = SymKind.alpha := by simpa using hα
  subst k
  have hmk : mk = false := by simpa using hm
  subst mk
  decide

/-- symTo4F4/symOf4F4 往返（标记只出现在 data0/data1）。 -/
lemma symOf4F4_symTo4F4_valid (s : Sym)
    (hvalid : s.2 = true → s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) :
    match symTo4F4 s with
    | [a, b, c, d] => symOf4F4 a b c d = some s
    | _ => False := by
  rcases s with ⟨k, mk⟩
  by_cases hmk : mk = true
  · rcases hvalid hmk with hk | hk
    · subst hk
      simp [symTo4F4, Sym.kindBits, symOf4F4, Sym.data0, Sym.mk]
    · subst hk
      simp [symTo4F4, Sym.kindBits, symOf4F4, Sym.data1, Sym.mk]
  · have hmkf : mk = false := by
      cases mk <;> simp at hmk ⊢
    subst mk
    by_cases hb : SymKind.isBranch k
    · cases k <;> simp [SymKind.isBranch] at hb ⊢
      all_goals simp [symTo4F4, Sym.kindBits, symOf4F4, Sym.alpha, Sym.beta, Sym.mk]
    · cases k <;> simp [SymKind.isBranch] at hb ⊢
      all_goals simp [symTo4F4, Sym.kindBits, symOf4F4, Sym.data0, Sym.data1, Sym.boundary,
        Sym.sel, Sym.nosel, Sym.consumed, Sym.mk, Sym.blank]
/-- symTo4F4/symOf4F4 往返（任意符号：标记位 m 独立于 kind 解码）。 -/
lemma symOf4F4_symTo4F4_all (s : Sym) :
    match symTo4F4 s with
    | [a, b, c, d] => symOf4F4 a b c d = some s
    | _ => False := by
  rcases s with ⟨k, mk⟩
  cases k <;> cases mk <;>
    simp [symTo4F4, Sym.kindBits, symOf4F4, Sym.mk, Sym.data0, Sym.data1, Sym.alpha, Sym.beta,
      Sym.boundary, Sym.sel, Sym.nosel, Sym.consumed, Sym.blank]

/-- encodeResult/decodeResult 往返（任意结果：skOf/dirOf 全枚举覆盖）。 -/
lemma decodeResult_encodeResult_all (r : SymTransResult) :
    decodeResult (encodeResult r) = r := by
  rcases r with ⟨n, w, d⟩
  rcases w with ⟨k, mk⟩
  have hsk : skOf k + (if mk then 9 else 0) < 18 := by
    cases k <;> cases mk <;> simp [skOf]
  have hdir : dirOf d < 3 := by
    cases d <;> simp [dirOf]
  have hq : (encodeResult ⟨n, (k, mk), d⟩) / 54 = n := by
    change (n * 54 + (skOf k + (if mk then 9 else 0)) * 3 + dirOf d) / 54 = n
    omega
  have hsk2 : ((encodeResult ⟨n, (k, mk), d⟩) / 3) % 18 = skOf k + (if mk then 9 else 0) := by
    change ((n * 54 + (skOf k + (if mk then 9 else 0)) * 3 + dirOf d) / 3) % 18 =
      skOf k + (if mk then 9 else 0)
    omega
  have hdir2 : (encodeResult ⟨n, (k, mk), d⟩) % 3 = dirOf d := by
    change (n * 54 + (skOf k + (if mk then 9 else 0)) * 3 + dirOf d) % 3 = dirOf d
    omega
  cases mk with
  | false =>
      cases k <;> cases d
      all_goals simp [decodeResult, hq, hsk2, hdir2, skOf, dirOf, Sym.data0, Sym.data1,
        Sym.alpha, Sym.beta, Sym.boundary, Sym.sel, Sym.nosel, Sym.consumed, Sym.mk]
  | true =>
      cases k <;> cases d
      all_goals simp [decodeResult, hq, hsk2, hdir2, skOf, dirOf, Sym.data0, Sym.data1,
        Sym.alpha, Sym.beta, Sym.boundary, Sym.sel, Sym.nosel, Sym.consumed, Sym.mk]

/-- Sym 格局与 CBTM 格局的全局逐格对应（提升方向用；输入无尾缀）。 -/
def blockCorrespond (cfgc : CBTMConfig subsetSumCBTM w) (cfgs : SymConfig) : Prop :=
  cfgc.state = encodeState cfgs.state 0 0 ∧
  cfgc.headPos = 4 * cfgs.headPos ∧
  ∀ (i : ℤ) (j : ℕ) (hj : j < 4),
    cfgc.tapeAt (4 * i + j) = (symTo4F4 (cfgs.tape i)).getD j F4.zero

/-- 一步格局的磁带取值（if 形式）。 -/
lemma stepConfig_tapeAt_apply {M : CBTM} {input : List F4} (cfg : CBTMConfig M input)
    (r : CBTMTransResult) (z : ℤ) :
    (stepConfig cfg r).tapeAt z = if z = cfg.headPos then r.writeSym else cfg.tapeAt z := by
  by_cases h : z = cfg.headPos <;> simp [stepConfig, CBTMConfig.tapeAt, h]

/-- 未写处的磁带值不变。 -/
lemma stepConfig_tapeAt_eq_of_ne {M : CBTM} {input : List F4} (cfg : CBTMConfig M input)
    (r : CBTMTransResult) (z : ℤ) (hne : z ≠ cfg.headPos) :
    (stepConfig cfg r).tapeAt z = cfg.tapeAt z := by
  rw [stepConfig_tapeAt_apply, if_neg hne]

/-- 带头处写入了 writeSym。 -/
lemma stepConfig_tapeAt_eq_of_eq {M : CBTM} {input : List F4} (cfg : CBTMConfig M input)
    (r : CBTMTransResult) (z : ℤ) (heq : z = cfg.headPos) :
    (stepConfig cfg r).tapeAt z = r.writeSym := by
  rw [stepConfig_tapeAt_apply, if_pos heq]

/-- 空白块取任意位置都是 F4.zero。 -/
lemma symTo4F4_blank_getD (m : ℕ) :
    (symTo4F4 Sym.blank).getD m F4.zero = F4.zero := by
  by_cases hm : m < 4
  · interval_cases m <;> simp [Sym.blank, Sym.data0, Sym.mk, symTo4F4, Sym.kindBits, F4.zero]
  · rw [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none]
    · rfl
    · rw [symTo4F4_length]
      omega

/-- flatMap（每块长 4）的 getD 取值。 -/
lemma flatMap_getD_symTo4F4 (l : List Sym) (n : ℕ) :
    (l.flatMap symTo4F4).getD n F4.zero = (symTo4F4 (l.getD (n / 4) Sym.blank)).getD (n % 4) F4.zero := by
  induction l generalizing n with
  | nil =>
      simp
      exact (symTo4F4_blank_getD (n % 4)).symm
  | cons x xs ih =>
      by_cases hn0 : n < 4
      · have hdiv : n / 4 = 0 := by omega
        have hmod : n % 4 = n := by omega
        rw [List.flatMap_cons,
          List.getD_append (symTo4F4 x) (xs.flatMap symTo4F4) F4.zero n (by
            simpa [symTo4F4_length] using hn0)]
        simp [hdiv, hmod, List.getD_cons_zero]
      · have hdiv : n / 4 = (n - 4) / 4 + 1 := by omega
        have hmod : n % 4 = (n - 4) % 4 := by omega
        have hnle : 4 ≤ n := by omega
        rw [List.flatMap_cons,
          List.getD_append_right (symTo4F4 x) (xs.flatMap symTo4F4) F4.zero n (by
            simpa [symTo4F4_length] using hnle)]
        rw [hdiv, hmod]
        rw [List.getD_cons_succ]
        exact ih (n - 4)

/-- 初始格局的对应。 -/
lemma initialBlockCorrespond (w : List Sym) :
    blockCorrespond (initialConfig subsetSumCBTM (flat4F4 w)) (symInitialConfig w) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [blockCorrespond, initialConfig, subsetSumCBTM, symInitialConfig, SymConfig.mk,
      encodeState, VerifierSym.qStart]
  · dsimp [blockCorrespond, initialConfig, subsetSumCBTM, symInitialConfig, SymConfig.mk]
  · intro i j hj
    have hcell : initialTapeOf (flat4F4 w) F4.zero (4 * i + j) =
        (symTo4F4 ((symInitialConfig w).tape i)).getD j F4.zero := by
      dsimp [initialTapeOf, flat4F4, symInitialConfig, SymConfig.mk]
      by_cases hi : 0 ≤ i ∧ i.toNat < w.length
      · have hconv : (4 * i + ↑j).toNat = 4 * i.toNat + j := by omega
        have hpos : 0 ≤ 4 * i + j ∧ (4 * i + j).toNat < (w.flatMap symTo4F4).length := by
          have hlen : (w.flatMap symTo4F4).length = 4 * w.length := by
            simp [symTo4F4_length, Nat.mul_comm]
          constructor
          · omega
          · rw [hlen]
            omega
        rw [dif_pos hpos]
        have hget : (List.flatMap symTo4F4 w)[(4 * i + ↑j).toNat] =
            (List.flatMap symTo4F4 w).getD (4 * i + ↑j).toNat F4.zero := by
          exact (List.getD_eq_get (List.flatMap symTo4F4 w) F4.zero ⟨(4 * i + ↑j).toNat, hpos.2⟩).symm
        rw [hget]
        rw [flatMap_getD_symTo4F4 w (4 * i + ↑j).toNat]
        have hdiv : (4 * i + ↑j).toNat / 4 = i.toNat := by omega
        have hmod : (4 * i + ↑j).toNat % 4 = j := by omega
        rw [hdiv, hmod]
        change (symTo4F4 (w.getD i.toNat Sym.blank)).getD j F4.zero =
            (symTo4F4 (if h : 0 ≤ i ∧ i.toNat < w.length then w[i.toNat] else Sym.blank)).getD j F4.zero
        rw [List.getD_eq_get w Sym.blank ⟨i.toNat, hi.2⟩, dif_pos hi, List.get_eq_getElem]
      · have hneg : ¬ (0 ≤ 4 * i + j ∧ (4 * i + j).toNat < (w.flatMap symTo4F4).length) := by
          intro h2
          apply hi
          constructor
          · omega
          · have hlen : (w.flatMap symTo4F4).length = 4 * w.length := by
              simp [symTo4F4_length, Nat.mul_comm]
            rw [hlen] at h2
            omega
        rw [dif_neg hneg]
        rw [dif_neg hi]
        simp [Sym.blank, Sym.data0, Sym.mk, symTo4F4, Sym.kindBits, F4.zero] <;>
          interval_cases j <;> rfl
    simpa [initialConfig, subsetSumCBTM, CBTMConfig.tapeAt] using hcell

end SymToF4

-- ============================================================================
-- NTM2 规范谓词（2026-09-06 方案 A：条款 ① 只约束合法编码输入）
-- ============================================================================

/-- 规范 NTM2：存在常数 K，任意**合法编码输入**（x = encodeInstanceF4 inst ++ flat4F4 gS，
    gS : List Sym——2026-09-09 输入层裁决（约定 26）：输入语义 = 计算纸带 4F4 符号串，
    flat4F4 像；非 4F4 像的 F4 串不是这台机器的输入，不在域内）
    上的任意可达路径满足：
    量词收窄（2026-09-09 用户裁决）：约束**可延拓到接受态的路径**（∀ 可达且 ∃ 延拓到
    acceptStates）；下游消费（iso_path_backward/StructIso_preserves_accepts）只在接受路径
    （空延拓）上使用。
    ① 磁头只在输入区及右边界上活动（每步的步前与步后位置均在 [0, |x|] 闭区间——
       验证器接受尾步（23 读 #ₗ → 100 R）步后 pos = |x| 是合法停留，故取闭区间；
       非法输入上允许越界拒绝——反例：flat4F4 [#₀,#₁] 上 2 态读带外 zero 双分支 R）；
    ② 标记格（读符号虚部 = true 的格，即 α/β 空白格）**前缀唯一**：某步读到标记格时，
       其**前缀**内无步停在同一位 ⇒ 标记读的**位置互异**（⇒ 标记读次数 ≤ 位置数 ≤ |x|+1）。
       （2026-09-11 实测裁定 Spec V1.47：**原「全程同位唯一」形式为假**——接受跑上磁头必然
        回到已读标记格（实例 ⟨[2,3],5⟩、位置 5 全程被踩 18 次）；前缀口径与之不冲突，
        且正是下游 `forkCount_le_input_length` 消费的形式）；
    ③ 路径长度 ≤ K·(标记读次数+1)·(|x|+1)²（多项式界：空输入上的一步路径
       也合法——(m+1) 与 (|x|+1)² 因子容纳 m=0 与 x=[] 的情形；
       2026-09-06 用户裁决：主支改二次——减法位处理每元素每数据位一轮、
       每轮全距穿越 O(|x|)，总步 ~Σkᵢ·|x| ≤ |x|²，线性主支不可满足）。 -/
def NTM2.Canonical (A : NTM2) : Prop :=
  ∃ K : ℕ,
    ∀ (x : List F4) (π : NTM2ComputationPath) (cfg : NTM2Config A x),
      (∃ (inst : SubsetSumInstance) (gS : List Sym),
        x = SymToF4.encodeInstanceF4 inst ++ SymToF4.flat4F4 gS) →
      (∀ step ∈ π, step.fromState ∉ A.acceptStates) →
      TapeReachablePathNTM2 A x π cfg →
      (∃ (π₂ : NTM2ComputationPath) (cfg₂ : NTM2Config A x),
          TapeReachablePathNTM2 A x (π ++ π₂) cfg₂ ∧ cfg₂.state ∈ A.acceptStates) →
        (∀ step ∈ π,
          0 ≤ step.pos ∧ step.pos ≤ (x.length : ℤ) ∧
          0 ≤ step.pos + step.result.2.2.toInt ∧
          step.pos + step.result.2.2.toInt ≤ (x.length : ℤ)) ∧
        (∀ (π₀ : NTM2ComputationPath) (step : NTM2TransitionStep) (π₁ : NTM2ComputationPath),
          π = π₀ ++ step :: π₁ → F4.im step.readSym = true →
            ∀ s ∈ π₀, s.pos ≠ step.pos) ∧
        (π.length ≤ K * ((π.filter (fun step => F4.im step.readSym = true)).length + 1) *
            (x.length + 1) * (x.length + 1) ∨
          ∃ (π₁ π₂ : NTM2ComputationPath), π = π₁ ++ π₂ ∧ π₂ ≠ [] ∧
            (∀ step ∈ π₂, step.fromState ∈ A.rejectStates ∧ step.result.1 ∈ A.rejectStates ∧
              step.result.2.2 = Dir.S))

end Mp
