/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/


import Mp.Basic
import Mp.CBTM
import Mp.IVM
import Mp.LowerBound

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


set_option maxHeartbeats 2000000
set_option maxErrors 1000

/-!
# 子集和 CBTM 验证器（逐步减法方案，磁带语义）

本文件构造「子集和 ∈ NP_F」的真实 CBTM 验证器（磁带语义 `CBTM.tapeAccepts`），
采用**逐步减法**算法。

## 编码（4 F4 = 1 个逻辑符号）

逻辑符号 = `SymKind × Bool`，其中 `SymKind` 是 8 种符号，`Bool` 是**4F4.4 位**
（第 4 个 F4 的实部 `re₄`，独立纸带，用作位号标记；虚部 `im₄` 恒 false）。

前 3 个 F4 的实部（`re₁, re₂, re₃`）与第 1 个 F4 的虚部（`im₁`）编码 8 种 `SymKind`；
第 2、3 个 F4 的虚部恒 false。`α` 与 `β` 用 `im₁ = 1` 触发分支。

| SymKind  | 含义         | re₁ | im₁ | re₂ | re₃ |
|----------|--------------|-----|-----|-----|-----|
| data0    | 值 0         | 0   | 0   | 0   | 0   |
| data1    | 值 1         | 1   | 0   | 0   | 0   |
| alpha    | 分支标记     | 0   | 1   | 0   | 0   |
| consumed | 0*（已处理） | 0   | 0   | 0   | 1   |
| boundary | #（边界）    | 1   | 0   | 1   | 1   |
| sel      | s（选中）    | 0   | 0   | 1   | 0   |
| nosel    | s′（不选中） | 0   | 0   | 1   | 1   |
| beta     | 非编码符号(元素区读到即拒) | 1   | 1   | 1   | 0   |

分支公理：`α`、`β` 的 `im₁ = 1`（虚部 true → card = 2），其余符号 `im₁ = 0`
（card = 1）。控制 F4 与第 4 个 F4 的虚部恒 false。

## 带布局（纯正轴，带头只走 ℕ）

```
#ₗ t₀…tₖ₋₁ #₀ α₁ v₁₀…v₁ₖ₋₁ … αₙ vₙ₀…vₙₖ₋₁ #₁
```

- `#ₗ` target 左边界；`t₀…tₖ₋₁` target 位（LSB 在左）；
- `#₀` target 右边界 / 数据区左边界（动态推进，占位扩展）；
- 元素区：每个元素 `α + k 位值`（α 为分支标记，β 不再用于编码，元素区读到 β 即拒绝）；
- `#₁` 数据区右边界。

**没有独立计数器区**：位号 `j` 由 target 区的 4F4.4 位前缀表示（`t₀…t_{j-1}` 的
4F4.4 = 1，`t_j…` 的 4F4.4 = 0）。定位 `t_j` = 从 `#ₗ` 右移找第一个 4F4.4 = 0。
处理完一个元素，target 区 4F4.4 随「占位扩展清零」一起复位。

## 阶段

1. 非确定分支：扫描元素区，遇 `α`/`β` 分支改写为 `sel`/`nosel`。
2. 逐步减法：遇 `sel` 把其值位逐位从 target 减去（读 `v_j = 1` → 写成 `consumed`，
   左移到 `#ₗ`，右移扫 4F4.4 前缀到第一个 0 定位 `t_j`，减 1 借位右传；借位到
   `#₀` 仍有 → 拒绝）；遇 `nosel` 清除值位。减完一个元素 `#₀` 右移（占位扩展）。
3. 判定：数据区扫完到 `#₁`，检查 target 全 0 → 接受，否则拒绝。

本文件仅定义编码层与虚部计数引理；状态机与正确性见后续。
-/

namespace Mp

open CBTM
open IVM
open F4

-- ============================================================================
-- 固定位宽编码（LSB 优先，虚部 false）
-- ============================================================================

/-- 自然数 n 的固定位宽 k 二进制编码（LSB 优先，不足补 0，虚部 false）。

    用 `decide (d ≠ 0)` 显式把 digits 的 0/1 映射为布尔位，避免 `ℕ→Bool` 隐式 coercion。 -/
def natToBinaryF4Fixed (k : ℕ) (n : ℕ) : List F4 :=
  let ds := Nat.digits 2 n
  (ds.map (fun d => (decide (d ≠ 0), false))) ++ List.replicate (k - ds.length) F4.zero

/-- 固定位宽编码的虚部全 false。 -/
lemma natToBinaryF4Fixed_im_false (k n : ℕ) :
    ∀ s ∈ natToBinaryF4Fixed k n, F4.im s = false := by
  intro s hs
  unfold natToBinaryF4Fixed at hs
  rw [List.mem_append] at hs
  rcases hs with (hs | hs)
  · rcases List.mem_map.mp hs with ⟨d, hd, rfl⟩
    rfl
  · have : s = F4.zero := (List.mem_replicate.mp hs).2
    subst s
    simp [F4.zero]

/-- 自然数的二进制位数（0 的位宽记为 1，避免空编码）。 -/
def bitWidth (n : ℕ) : ℕ := (Nat.digits 2 n).length

-- ============================================================================
-- 9 逻辑符号 SymKind 与 Sym = SymKind × Bool（4F4.4 位）
-- ============================================================================

/-- 8 种逻辑符号。 -/
inductive SymKind : Type
  | data0     -- 0（值 0）
  | data1     -- 1（值 1）
  | consumed  -- 0*（已处理标记）
  | alpha     -- α（分支标记）
  | sel       -- s（选中）
  | nosel     -- s′（不选中）
  | beta      -- β（分支位形遗留符号：不再用于编码，元素区读到即拒绝）
  | boundary  -- #（边界）
  deriving DecidableEq, Repr

instance : Fintype SymKind :=
  Fintype.ofList [SymKind.data0, SymKind.data1, SymKind.consumed, SymKind.alpha,
    SymKind.sel, SymKind.nosel, SymKind.beta, SymKind.boundary] <| by
    intro x
    cases x <;> decide

/-- 是否触发分支（虚部 `im₁ = 1`）：`α` 与 `β`。 -/
@[reducible] def SymKind.isBranch (k : SymKind) : Bool :=
  decide (k = SymKind.alpha ∨ k = SymKind.beta)

/-- 逻辑符号 = 8 种符号 + 4F4.4 位（第 4 F4 的 re，位号标记）。 -/
abbrev Sym : Type := SymKind × Bool

namespace Sym

/-- 构造一个逻辑符号（4F4.4 位默认 false）。 -/
def mk (k : SymKind) (mark : Bool := false) : Sym := (k, mark)

@[simp] lemma mk_fst (k : SymKind) (mark : Bool) : (mk k mark).1 = k := rfl
@[simp] lemma mk_snd (k : SymKind) (mark : Bool) : (mk k mark).2 = mark := rfl

/-- 逻辑符号是否触发分支（符号位 `im₁ = 1`）。 -/
@[reducible] def isBranch (s : Sym) : Bool := SymKind.isBranch s.1

/-- 4F4.4 位（第 4 个 F4 的实部）。 -/
def mark (s : Sym) : Bool := s.2

def data0 (mark : Bool := false) : Sym := mk SymKind.data0 mark
def data1 (mark : Bool := false) : Sym := mk SymKind.data1 mark
@[simp] lemma data0_fst : Sym.data0.1 = SymKind.data0 := rfl
@[simp] lemma data1_fst : Sym.data1.1 = SymKind.data1 := rfl
def consumed : Sym := mk SymKind.consumed
def alpha : Sym := mk SymKind.alpha
def sel : Sym := mk SymKind.sel
def nosel : Sym := mk SymKind.nosel
def beta : Sym := mk SymKind.beta
def boundary : Sym := mk SymKind.boundary

/-- blank = data0，4F4.4 位 false。 -/
def blank : Sym := data0 false

/-- 逻辑符号的符号位（re₁, im₁, re₂, re₃）。 -/
def kindBits : SymKind → Bool × Bool × Bool × Bool
  | SymKind.data0 => (false, false, false, false)
  | SymKind.data1 => (true, false, false, false)
  | SymKind.alpha => (false, true, false, false)
  | SymKind.consumed => (false, false, false, true)
  | SymKind.boundary => (true, false, true, true)
  | SymKind.sel => (false, false, true, false)
  | SymKind.nosel => (false, false, true, true)
  | SymKind.beta => (true, true, true, false)

/-- Sym → 4 F4 编码：首 F4（re₁,im₁）、第 2 F4（re₂,false）、第 3 F4（re₃,false）、
    第 4 F4（4F4.4 位,false）。 -/
def toF4s (s : Sym) : List F4 :=
  let (r1, i1, r2, r3) := kindBits s.1
  [(r1, i1), (r2, false), (r3, false), (s.2, false)]

end Sym

-- ============================================================================
-- Sym 层实例编码
-- ============================================================================

/-- 自然数 n 的可变长原生二进制（LSB 左）编码为 Sym 序列（不补零、不截断，与元素位串同构）。 -/
def encodeBitsSym (n : ℕ) : List Sym :=
  (Nat.digits 2 n).map (fun d => if d = 0 then Sym.data0 else Sym.data1)

/-- 元素的原生可变长 Sym 编码（不补零、不截断）：直接是 n 的二进制 digits。 -/
def encodeBitsSymNative (n : ℕ) : List Sym :=
  (Nat.digits 2 n).map (fun d => if d = 0 then Sym.data0 else Sym.data1)

/-- 元素区的 Sym 编码（sep 已取消，元素直接相连，比特串为原生可变长）：
    每个元素 `α + 原生位`（β 不再作为元素标记）。 -/
def encodeElementsSym (elems : List ℕ) : List Sym :=
  match elems with
  | [] => []
  | [v] => [Sym.alpha] ++ encodeBitsSymNative v
  | v :: rest => [Sym.alpha] ++ encodeBitsSymNative v ++ encodeElementsSym rest

/-- Sym 层实例编码（纯正轴，无独立计数器区，无元素分隔符）：

    `#ₗ target #₀ [α + k位值]…[β + k位值] #₁`。 -/
def encodeInstanceSym (inst : SubsetSumInstance) : List Sym :=
  [Sym.boundary] ++
  encodeBitsSym inst.target ++
  [Sym.boundary] ++
  encodeElementsSym inst.elements ++
  [Sym.boundary]

-- ============================================================================
-- 虚部计数引理：Sym 编码展平到 F4 后，虚部 true 的符号数 = 元素个数
-- ============================================================================

/-- `Sym.toF4s` 的虚部 true 数：分支符号（α/β）记 1，否则 0。 -/
lemma imTrueCount_symToF4s (s : Sym) :
    imTrueCount (Sym.toF4s s) = if Sym.isBranch s then 1 else 0 := by
  rcases s with ⟨k, mark⟩
  unfold Sym.toF4s Sym.kindBits imTrueCount Sym.isBranch SymKind.isBranch
  cases k <;> simp [F4.zero, F4.one, F4.alpha, F4.beta]

/-- 展平后虚部 true 数 = 分支符号的个数。 -/
lemma imTrueCount_flatMap_symToF4s (l : List Sym) :
    imTrueCount (l.flatMap Sym.toF4s) = (l.filter Sym.isBranch).length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rw [show (x :: xs).flatMap Sym.toF4s = Sym.toF4s x ++ xs.flatMap Sym.toF4s from rfl]
      rw [imTrueCount_append, ih, imTrueCount_symToF4s]
      rcases x with ⟨k, mark⟩
      by_cases h : SymKind.isBranch k <;>
        simp [h, List.filter_cons, List.length_cons] <;> omega

/-- 原生可变长比特串无分支符号。 -/
lemma filter_branch_encodeBitsSymNative (n : ℕ) :
    (encodeBitsSymNative n).filter Sym.isBranch = [] := by
  rw [List.filter_eq_nil_iff]
  intro s hs
  unfold encodeBitsSymNative at hs
  rcases List.mem_map.mp hs with ⟨d, hd, rfl⟩
  by_cases hd0 : d = 0
  · simp [hd0, Sym.data0, Sym.mk, Sym.isBranch, SymKind.isBranch]
  · simp [hd0, Sym.data1, Sym.mk, Sym.isBranch, SymKind.isBranch]

/-- encodeBitsSym（target 版）无分支符号（定义与 native 同构）。 -/
lemma filter_branch_encodeBitsSym (n : ℕ) :
    (encodeBitsSym n).filter Sym.isBranch = [] := by
  rw [show encodeBitsSym n = encodeBitsSymNative n from rfl]
  exact filter_branch_encodeBitsSymNative n

/-- 每个非最后元素贡献一个 `[alpha]`。 -/
lemma filter_branch_alpha_element (v : ℕ) :
    ((Sym.alpha :: (encodeBitsSymNative v)).filter Sym.isBranch) = [Sym.alpha] := by
  simp [Sym.alpha, Sym.mk, Sym.isBranch, filter_branch_encodeBitsSymNative]

/-- 最后一个元素贡献一个 `[beta]`。 -/
lemma filter_branch_beta_element (v : ℕ) :
    ((Sym.beta :: (encodeBitsSymNative v)).filter Sym.isBranch) = [Sym.beta] := by
  simp [Sym.beta, Sym.mk, Sym.isBranch, filter_branch_encodeBitsSymNative]

/-- 元素区的分支符号数 = 元素个数。 -/
lemma filter_branch_encodeElementsSym_length (elems : List ℕ) :
    ((encodeElementsSym elems).filter Sym.isBranch).length = elems.length := by
  induction elems with
  | nil => rfl
  | cons v rest ih =>
      cases rest with
      | nil =>
          simp [encodeElementsSym, Sym.alpha, Sym.mk, Sym.isBranch, filter_branch_encodeBitsSymNative]
      | cons w rest' =>
          simp [encodeElementsSym, Sym.alpha, Sym.mk, Sym.isBranch,
            filter_branch_encodeBitsSymNative, ih]

/-- 实例编码展平到 F4 后的虚部 true 符号数 = 元素个数。 -/
lemma imTrueCount_encodeInstanceSym (inst : SubsetSumInstance) :
    imTrueCount ((encodeInstanceSym inst).flatMap Sym.toF4s) = inst.elements.length := by
  rw [imTrueCount_flatMap_symToF4s]
  unfold encodeInstanceSym
  simp [List.filter_append, List.filter_singleton, List.length_append, List.length_singleton,
    filter_branch_encodeBitsSymNative, filter_branch_encodeBitsSym,
    filter_branch_encodeElementsSym_length,
    Sym.boundary, Sym.mk, Sym.isBranch]

-- ============================================================================
-- Sym 逻辑层：单带磁带语义
-- ============================================================================

/-- Sym 转移结果。 -/
structure SymTransResult where
  nextState : ℕ
  writeSym : Sym
  moveDir : Dir
  deriving DecidableEq

/-- Sym 转移步。 -/
structure SymStep where
  fromState : ℕ
  readSym : Sym
  result : SymTransResult

/-- Sym 配置（单带，blank = data0）。 -/
structure SymConfig where
  state : ℕ
  tape : ℤ → Sym
  headPos : ℤ

/-- Sym 初始配置：输入写在 [0, n)，其余 blank，带头在 0，状态 0。 -/
def symInitialConfig (input : List Sym) : SymConfig :=
  { state := 0,
    tape := fun i =>
      if h : 0 ≤ i ∧ i.toNat < input.length then input.get ⟨i.toNat, h.2⟩ else Sym.blank,
    headPos := 0 }

/-- Sym 一步格局。 -/
def symStepConfig (cfg : SymConfig) (r : SymTransResult) : SymConfig :=
  { state := r.nextState,
    tape := fun i => if i = cfg.headPos then r.writeSym else cfg.tape i,
    headPos := cfg.headPos + r.moveDir.toInt }

/-- Sym 磁带语义可达路径。 -/
inductive SymReachablePath (M : ℕ × Sym → Finset SymTransResult) (input : List Sym) :
    List SymStep → SymConfig → Prop
  | nil : SymReachablePath M input [] (symInitialConfig input)
  | cons : ∀ (π₀ : List SymStep) (step : SymStep) (cfg : SymConfig),
      SymReachablePath M input π₀ cfg →
      step.fromState = cfg.state →
      step.readSym = cfg.tape cfg.headPos →
      step.result ∈ M (cfg.state, cfg.tape cfg.headPos) →
      SymReachablePath M input (π₀ ++ [step]) (symStepConfig cfg step.result)

/-- Sym 接受：存在一条磁带可达路径，末端状态在接受态。 -/
def symAccepts (M : ℕ × Sym → Finset SymTransResult) (accept : Finset ℕ)
    (input : List Sym) : Prop :=
  ∃ π : List SymStep, ∃ cfg : SymConfig,
    SymReachablePath M input π cfg ∧ cfg.state ∈ accept

-- ============================================================================
-- Sym 状态机：验证器转移表
-- ============================================================================

namespace VerifierSym

/-- 状态编号。 -/
def qAccept : ℕ := 100
def qReject : ℕ := 101
def qStart : ℕ := 0
def qCrossTarget : ℕ := 1
def qBranch : ℕ := 2
def qMarkHash1 : ℕ := 3          -- #₁ 标 m=1 → 格式检查
def qScanElem : ℕ := 4
def qSubScan : ℕ := 5
def qLeftSub : ℕ := 76           -- 减 1 路径左扫（跨 #₀ 进 target）
def qLeftSub2 : ℕ := 77          -- 减 1 路径 target 左扫（到 #ₗ）
def qLeftOnly : ℕ := 8           -- 0 位路径左扫
def qLeftOnly2 : ℕ := 9          -- 0 位路径 target 左扫
def qFindSub : ℕ := 10           -- 右扫定位 t_j（减 1）
def qSubtract : ℕ := 11          -- 按位减（磁头在 t_j，m=1）
def qFindOnly : ℕ := 12          -- 0 位路径：右扫定位 t_j（只记位号，不减）
def qBorrow : ℕ := 14
def qBackA : ℕ := 81             -- 回元素区（穿透 target / #₀ / 选择符位）
def qBackB : ℕ := 13             -- 扫已消耗区
def qClrLeft : ℕ := 84           -- 清理左扫（跨 #₀ 进 target）
def qClrTgt : ℕ := 85            -- 清理 target 左扫（到 #ₗ）
def qClrMark : ℕ := 86           -- 清计数器（m=1 → m=0）
def qClrBack : ℕ := 87           -- 清理右移回 #₀
def qExpandStart : ℕ := 20
def qExpandScan : ℕ := 21
def qNewHash : ℕ := 51           -- 已处理元素末位 → 新 #₀
def qCheck : ℕ := 22
def qCheckLeft : ℕ := 23          -- 判定左扫（全 0 → #ₗ 接受）
def qFmtFirst : ℕ := 24
def qFmtData : ℕ := 29          -- 数据左扫（25 已取消：24 读最高位 data1 → 29 保证 MSB=1）
def qFmtPair : ℕ := 26
def qFmtTgt1 : ℕ := 27
def qFmtTgt : ℕ := 38
def qFmtBack : ℕ := 28

/-- 接受态集合。 -/
def acceptStates : Finset ℕ := {qAccept}

/-- 转移表的合法状态集合（33 个显式状态；不在集合内的状态一律归 101 停机）。 -/
def legalStates : Finset ℕ := {0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23,
  24, 26, 27, 28, 29, 38, 51, 76, 77, 81, 84, 85, 86, 87, 100, 101}

/-- 转移函数（完整转移表）。状态用数字字面量匹配（Lean 模式不归约 def 常量）。
    外层 `if q ∈ legalStates`：表外状态全部归 101，证明时 `if_pos/if_neg` 一步归约（集合成员判定），
    不再需要对 82 臂 match 做符号分割。 -/
def transition : ℕ × Sym → Finset SymTransResult :=
  fun (q, s) =>
    let R := Dir.R; let L := Dir.L; let S := Dir.S
    let ret (ns : ℕ) (w : Sym) (d : Dir) := SymTransResult.mk ns w d
    if q ∈ legalStates then
    match q, s with
    -- 阶段 0：分支（0–3）
    | 0, (SymKind.boundary, _) => {ret 1 s R}                              -- 第一个字符必须为 #
    | 1, (SymKind.data0, _) => {ret 1 s R}                                 -- 进入 target 区
    | 1, (SymKind.data1, _) => {ret 1 s R}
    | 1, (SymKind.boundary, _) => {ret 2 s R}                              -- 离开 target 区
    | 2, (SymKind.alpha, true) => {ret 101 s S}                             -- α 带标记:非法
    | 2, (SymKind.alpha, false) => {ret 2 (Sym.sel) R, ret 2 (Sym.nosel) R} -- α 双分支
    | 2, (SymKind.beta, _) => {ret 101 s S}                                 -- β 非元素标记:拒绝
    | 2, (SymKind.data0, _) => {ret 2 s R}                                 -- bits 区数据位：跳过
    | 2, (SymKind.data1, _) => {ret 2 s R}
    | 2, (SymKind.boundary, _) => {ret 3 s S}                              -- 磁头停在 #₁ 上
    -- 阶段 1.5：格式检查（#₁ 标记 + 元素区成对 + target 区）
    | 3, (SymKind.boundary, true) => {ret 101 s S}                         -- #₁ 已标记：非法
    | 3, (SymKind.boundary, false) => {ret 24 (Sym.mk SymKind.boundary true) L}  -- #₁ 标 m=1
    | 24, (SymKind.data1, false) => {ret 29 s L}                           -- 最高位 1：v>0 ✓（格式检查，反向扫）
    | 24, (SymKind.data0, false) => {ret 101 s L}                          -- 最高位 0（元素 0 或前导 0）：拒绝
    | 29, (SymKind.data0, false) => {ret 29 s L}                           -- v>0 已证：扫完数据
    | 29, (SymKind.data1, false) => {ret 29 s L}
    | 29, (SymKind.sel, false) => {ret 26 s L}                             -- 配对：选择符
    | 29, (SymKind.nosel, false) => {ret 26 s L}
    | 26, (SymKind.data1, false) => {ret 29 s L}                           -- 下一对：最高位 1 → 29 扫完
    | 26, (SymKind.data0, false) => {ret 101 s L}                          -- 下一对最高位 0：拒绝
    | 26, (SymKind.boundary, false) => {ret 27 s L}                        -- #₀ → target 区
    | 27, (SymKind.data1, false) => {ret 38 s L}                           -- target 最高位 1（target>0）：扫
    | 27, (SymKind.data0, false) => {ret 101 s L}                          -- target 最高位 0（target=0 或前导 0）：拒绝
    | 38, (SymKind.data0, false) => {ret 38 s L}                           -- target data 串
    | 38, (SymKind.data1, false) => {ret 38 s L}
    | 38, (SymKind.boundary, false) => {ret 28 s R}                        -- #ₗ → 右移回
    | 28, (SymKind.data0, _) => {ret 28 s R}
    | 28, (SymKind.data1, _) => {ret 28 s R}
    | 28, (SymKind.boundary, _) => {ret 4 s R}                             -- #₀ → 减法阶段
    -- 阶段 2：减法 / 清除
    | 4, (SymKind.sel, _) => {ret 5 (Sym.data0) R}                         -- 选择符 → 0（对应左分解符）
    | 4, (SymKind.nosel, _) => {ret 20 (Sym.data0) L}                      -- 未选择：置选择位 0 进占位扩展
    | 5, (SymKind.data1, _) => {ret 76 (Sym.consumed) L}                   -- 1：记计数器且做减法
    | 5, (SymKind.data0, _) => {ret 8 (Sym.consumed) L}                    -- 0：记计数器但不做减法
    | 5, (SymKind.boundary, _) => {ret 101 s L}
    -- 减法定位 t_j（减 1 路径）
    | 76, (SymKind.boundary, _) => {ret 77 s L}                            -- 跨 #₀ 进 target
    | 76, (SymKind.consumed, _) => {ret 76 s L}
    | 76, (SymKind.data0, _) => {ret 76 s L}
    | 76, (SymKind.data1, _) => {ret 76 s L}
    | 77, (SymKind.boundary, _) => {ret 10 s R}                            -- 到 #ₗ 右移定位
    | 77, (SymKind.data0, _) => {ret 77 s L}
    | 77, (SymKind.data1, _) => {ret 77 s L}
    -- 减法定位 t_j（只记位号路径）
    | 8, (SymKind.boundary, _) => {ret 9 s L}                              -- 0 位路径：跨 #₀
    | 8, (SymKind.consumed, _) => {ret 8 s L}
    | 8, (SymKind.data0, _) => {ret 8 s L}
    | 8, (SymKind.data1, _) => {ret 8 s L}
    | 9, (SymKind.boundary, _) => {ret 12 s R}                            -- 到 #ₗ 右移定位
    | 9, (SymKind.data0, _) => {ret 9 s L}                                -- target 左扫（含 m=1）
    | 9, (SymKind.data1, _) => {ret 9 s L}
    -- 右移找 t_j（扫 m 前缀到第一个 0）
    | 10, (SymKind.data0, true) => {ret 10 (Sym.data0 true) R}             -- 已计数前缀
    | 10, (SymKind.data1, true) => {ret 10 (Sym.data1 true) R}
    | 10, (SymKind.boundary, _) => {ret 101 s L}                           -- target 不足：拒绝
    | 10, (SymKind.data0, false) => {ret 11 (Sym.data0 true) S}            -- 定位到 t_j：标 m=1
    | 10, (SymKind.data1, false) => {ret 11 (Sym.data1 true) S}
    | 12, (SymKind.boundary, false) => {ret 101 s R}                         -- target 不足：拒绝
    | 12, (SymKind.data0, false) => {ret 81 (Sym.data0 true) R}           -- 只记位号，不减
    | 12, (SymKind.data1, false) => {ret 81 (Sym.data1 true) R}
    | 12, (SymKind.data0, true) => {ret 12 (Sym.data0 true) R}            -- 扫已计数前缀
    | 12, (SymKind.data1, true) => {ret 12 (Sym.data1 true) R}
    -- 按位减（磁头在 t_j 上，m=1）
    | 11, (SymKind.data1, m) => {ret 81 (Sym.data0 m) R}                   -- 1-1=0 完
    | 11, (SymKind.data0, m) => {ret 14 (Sym.data1 m) R}                   -- 0-1 借位
    | 11, (SymKind.boundary, _) => {ret 101 s R}
    -- 借位右传
    | 14, (SymKind.data0, m) => {ret 14 (Sym.data1 m) R}                   -- 借位传播
    | 14, (SymKind.data1, m) => {ret 81 (Sym.data0 m) R}                   -- 借位终止
    | 14, (SymKind.boundary, _) => {ret 101 s R}                           -- 借位穿 #₀：拒绝
    -- 回元素区（穿透 target / #₀ / 选择符位）
    | 81, (SymKind.consumed, _) => {ret 13 (Sym.consumed) R}               -- 回到已消耗区开头
    | 81, (SymKind.data0, _) => {ret 81 s R}
    | 81, (SymKind.data1, _) => {ret 81 s R}
    | 81, (SymKind.boundary, _) => {ret 81 s R}                            -- 自然穿透 #
    | 13, (SymKind.consumed, _) => {ret 13 (Sym.consumed) R}               -- 扫已消耗区
    | 13, (SymKind.data0, _) => {ret 5 s S}                                -- 下一未消费位
    | 13, (SymKind.data1, _) => {ret 5 s S}
    | 13, (SymKind.sel, _) => {ret 84 s L}                                 -- 下一元素：清理
    | 13, (SymKind.nosel, _) => {ret 84 s L}
    | 13, (SymKind.boundary, _) => {ret 84 s L}                            -- #₁：末元素清理
    -- 清理（sel 减完）：清计数器
    | 84, (SymKind.boundary, _) => {ret 85 s L}                            -- 跨 #₀ 进 target
    | 84, (SymKind.consumed, _) => {ret 84 s L}
    | 84, (SymKind.data0, _) => {ret 84 s L}
    | 84, (SymKind.data1, _) => {ret 84 s L}
    | 85, (SymKind.boundary, _) => {ret 86 s R}                            -- 到 #ₗ 右移清 m
    | 85, (SymKind.data0, _) => {ret 85 s L}
    | 85, (SymKind.data1, _) => {ret 85 s L}
    | 86, (SymKind.data0, true) => {ret 86 (Sym.mk SymKind.data0 false) R}  -- 清计数器
    | 86, (SymKind.data1, true) => {ret 86 (Sym.mk SymKind.data1 false) R}  -- 清计数器
    | 86, (SymKind.data0, false) => {ret 87 s S}                             -- 第一个 m=0：停
    | 86, (SymKind.data1, false) => {ret 87 s S}                             -- 第一个 m=0：停
    | 86, (SymKind.boundary, false) => {ret 87 s S}                          -- 紧贴 #₀：停（m=0）
    | 87, (SymKind.data0, _) => {ret 87 s R}
    | 87, (SymKind.data1, _) => {ret 87 s R}
    | 87, (SymKind.boundary, _) => {ret 20 s S}                            -- #₀ → 占位扩展
    -- 占位扩展：#₀ → 0，清元素位，遇选择符 → 新 #₀，遇 #₁ → 判定
    | 20, (SymKind.boundary, _) => {ret 21 (Sym.data0) R}                  -- #₀ → 0
    | 21, (SymKind.consumed, _) => {ret 21 (Sym.data0) R}
    | 21, (SymKind.data0, _) => {ret 21 (Sym.data0) R}
    | 21, (SymKind.data1, _) => {ret 21 (Sym.data0) R}
    | 21, (SymKind.sel, _) => {ret 51 s L}                                 -- 下一元素：回置新 #₀
    | 21, (SymKind.nosel, _) => {ret 51 s L}
    | 21, (SymKind.boundary, _) => {ret 22 s S}                            -- #₁ → 判定
    | 51, (SymKind.data0, _) => {ret 4 (Sym.boundary) R}                   -- 末位 → 新 #₀
    -- 阶段 3：判定
    | 22, (SymKind.boundary, true) => {ret 23 s L}                         -- #₁ m=1（格式已查）：进判定
    | 23, (SymKind.data0, _) => {ret 23 s L}                               -- 全 0 左扫
    | 23, (SymKind.data1, _) => {ret 101 s L}                              -- 余 1：拒绝
    | 23, (SymKind.boundary, _) => {ret 100 s R}                           -- #ₗ：接受
    -- 吸收态
    | 100, _ => {ret 100 s S}
    | 101, _ => {ret 101 s S}
    -- 防御性默认（不应到达）
    | _, _ => {ret 101 s S}
    else
      {ret 101 s S}

/-- 验证器 Sym 转移函数（对外别名）。 -/
def verifierSymTransition : ℕ × Sym → Finset SymTransResult := transition

end VerifierSym

-- ============================================================================
-- decode 语义：Sym 串 ↔ 数值（正确性证明基础设施）
-- ============================================================================

/-- 符号位的数值：data1 → 1，其余 → 0。 -/
def bitVal (s : Sym) : ℕ :=
  match s.1 with
  | SymKind.data1 => 1
  | _ => 0

@[simp] lemma bitVal_data1 : bitVal Sym.data1 = 1 := rfl
@[simp] lemma bitVal_data0 : bitVal Sym.data0 = 0 := rfl

/-- data0/data1 符号序列（LSB 在左）解码为自然数。 -/
def decodeBitsSym (l : List Sym) : ℕ :=
  Nat.ofDigits 2 (l.map bitVal)

/-- 若 f 在 l 上逐点恒等，则 l.map f = l。 -/
lemma map_eq_self_of_forall {α : Type} (l : List α) (f : α → α)
    (h : ∀ a ∈ l, f a = a) : l.map f = l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons]
      rw [h a (by simp)]
      rw [ih (fun x hx => h x (by simp [hx]))]

/-- 全 0 数字串解码为 0。 -/
lemma ofDigits_two_replicate_zero (m : ℕ) :
    Nat.ofDigits 2 (List.replicate m 0) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp [List.replicate, Nat.ofDigits, ih]

/-- encodeBitsSym 的干净展开（定义即 digits 的 0/1 → data0/data1，无补零）。 -/
lemma encodeBitsSym_eq (n : ℕ) :
    encodeBitsSym n =
      (Nat.digits 2 n).map (fun d => if d = 0 then Sym.data0 else Sym.data1) := by
  rfl

/-- decode ∘ encodeBitsSym = id（原生可变长）。 -/
lemma decodeBitsSym_encodeBitsSym (n : ℕ) :
    decodeBitsSym (encodeBitsSym n) = n := by
  rw [encodeBitsSym_eq]
  unfold decodeBitsSym
  rw [List.map_map]
  have hdig : (Nat.digits 2 n).map
      (bitVal ∘ (fun d => if d = 0 then Sym.data0 else Sym.data1)) = Nat.digits 2 n := by
    apply map_eq_self_of_forall
    intro d hd
    have hd_lt : d < 2 := Nat.digits_lt_base (by decide : 1 < 2) hd
    change bitVal (if d = 0 then Sym.data0 else Sym.data1) = d
    by_cases h0 : d = 0
    · simp [h0, bitVal]
    · have h1 : d = 1 := by omega
      simp [h0, h1, bitVal]
  rw [hdig]
  rw [Nat.ofDigits_digits]

-- ============================================================================
-- 纯数学减法引理：二进制减 1 / 减 2^j（借位向高位传播）
-- ============================================================================

/-- 位列表（LSB 左）的数值。 -/
def bitsValue (bits : List Bool) : ℕ :=
  Nat.ofDigits 2 (bits.map (fun b => match b with | true => 1 | false => 0))

@[simp] lemma bitsValue_nil : bitsValue [] = 0 := rfl
@[simp] lemma bitsValue_cons (b : Bool) (rest : List Bool) :
    bitsValue (b :: rest) = (match b with | true => 1 | false => 0) + 2 * bitsValue rest := rfl

/-- 列表（LSB 左）中第一个 true 位的索引；全 false 返回长度（0 基准）。 -/
def firstTrueIdx (bits : List Bool) : ℕ :=
  match bits with
  | [] => 0
  | true :: _ => 0
  | false :: rest => (firstTrueIdx rest) + 1

@[simp] lemma firstTrueIdx_nil : firstTrueIdx [] = 0 := rfl
@[simp] lemma firstTrueIdx_true (rest : List Bool) : firstTrueIdx (true :: rest) = 0 := rfl
@[simp] lemma firstTrueIdx_false (rest : List Bool) : firstTrueIdx (false :: rest) = (firstTrueIdx rest) + 1 := rfl

/-- 若列表含 true，则 firstTrueIdx 严格小于长度。 -/
lemma firstTrueIdx_lt_length_of_mem (bits : List Bool) (h : true ∈ bits) :
    firstTrueIdx bits < bits.length := by
  induction bits with
  | nil => simp at h
  | cons b rest ih =>
      cases b with
      | true => simp
      | false =>
          have hrest : true ∈ rest := by simpa using h
          have := ih hrest
          simp [this]

/-- 二进制减 1（LSB 左，借位向高位传播）；借位穿出返回 none。 -/
def subOne (bits : List Bool) : Option (List Bool) :=
  match bits with
  | [] => none
  | true :: rest => some (false :: rest)
  | false :: rest => Option.map (fun r => true :: r) (subOne rest)

@[simp] lemma subOne_nil : subOne [] = none := rfl
@[simp] lemma subOne_true (rest : List Bool) : subOne (true :: rest) = some (false :: rest) := rfl
@[simp] lemma subOne_false (rest : List Bool) :
    subOne (false :: rest) = Option.map (fun r => true :: r) (subOne rest) := rfl

/-- subOne 成功蕴含原值 ≥ 1。 -/
lemma subOne_some_ge_one (bits bits' : List Bool) (h : subOne bits = some bits') :
    1 ≤ bitsValue bits := by
  induction bits generalizing bits' with
  | nil => simp at h
  | cons b rest ih =>
      cases b with
      | true => simp at h ⊢
      | false =>
          cases h2 : subOne rest with
          | none => simp [h2] at h
          | some r =>
              have := ih r (by simpa [h2])
              simp at this ⊢
              omega

/-- 二进制减 1 的正确性。 -/
lemma subOne_correct (bits bits' : List Bool) (h : subOne bits = some bits') :
    bitsValue bits' = bitsValue bits - 1 := by
  induction bits generalizing bits' with
  | nil => simp at h
  | cons b rest ih =>
      cases b with
      | true =>
          simp at h
          subst bits'
          simp
      | false =>
          cases h2 : subOne rest with
          | none => simp [h2] at h
          | some r =>
              simp [h2] at h
              subst bits'
              have hge := subOne_some_ge_one rest r h2
              have ihr := ih r h2
              simp [hge, ihr]
              omega

/-- subOne 保持长度。 -/
lemma subOne_length (bits bits' : List Bool) (h : subOne bits = some bits') :
    bits'.length = bits.length := by
  induction bits generalizing bits' with
  | nil => simp at h
  | cons b rest ih =>
      cases b with
      | true => simp at h; subst bits'; rfl
      | false =>
          cases h2 : subOne rest with
          | none => simp [h2] at h
          | some r =>
              simp [h2] at h
              subst bits'
              have := ih r h2
              simp [this]

/-- subOne 成功 ⟺ 列表含 true。 -/
lemma subOne_some_iff_mem_true (bits : List Bool) :
    (∃ b', subOne bits = some b') ↔ true ∈ bits := by
  constructor
  · intro h
    rcases h with ⟨b', h⟩
    induction bits generalizing b' with
    | nil => simp at h
    | cons b rest ih =>
        cases b with
        | true => simp
        | false =>
            cases h2 : subOne rest with
            | none => simp [h2] at h
            | some r => simp [ih r h2]
  · intro h
    induction bits with
    | nil => simp at h
    | cons b rest ih =>
        cases b with
        | true => exact ⟨false :: rest, rfl⟩
        | false =>
            have hrest : true ∈ rest := by simpa using h
            rcases ih hrest with ⟨b', hb'⟩
            exact ⟨true :: b', by simp [hb']⟩

/-- 对第 j 位减 1（即减 2^j）。 -/
def subOneAt : ℕ → List Bool → Option (List Bool)
  | 0, bits => subOne bits
  | (n+1), b :: rest => Option.map (fun r => b :: r) (subOneAt n rest)
  | (n+1), [] => none

@[simp] lemma subOneAt_zero (bits : List Bool) : subOneAt 0 bits = subOne bits := rfl
@[simp] lemma subOneAt_succ_nil (n : ℕ) : subOneAt (n+1) [] = none := rfl
@[simp] lemma subOneAt_succ_cons (n : ℕ) (b : Bool) (rest : List Bool) :
    subOneAt (n+1) (b :: rest) = Option.map (fun r => b :: r) (subOneAt n rest) := rfl

/-- subOneAt 成功蕴含原值 ≥ 2^j。 -/
lemma subOneAt_some_ge_pow (bits bits' : List Bool) (j : ℕ)
    (h : subOneAt j bits = some bits') : 2 ^ j ≤ bitsValue bits := by
  induction j generalizing bits bits' with
  | zero =>
      simpa using subOne_some_ge_one bits bits' h
  | succ j ih =>
      cases bits with
      | nil => simp at h
      | cons b rest =>
          cases h2 : subOneAt j rest with
          | none => simp [h2] at h
          | some r =>
              have := ih rest r h2
              simp at this ⊢
              rw [pow_succ]
              omega

/-- 减 2^j 的正确性。 -/
lemma subOneAt_correct (bits bits' : List Bool) (j : ℕ)
    (h : subOneAt j bits = some bits') :
    bitsValue bits' = bitsValue bits - 2 ^ j := by
  induction j generalizing bits bits' with
  | zero =>
      simpa using subOne_correct bits bits' h
  | succ j ih =>
      cases bits with
      | nil => simp at h
      | cons b rest =>
          cases h2 : subOneAt j rest with
          | none => simp [h2] at h
          | some r =>
              simp [h2] at h
              subst bits'
              have hge := subOneAt_some_ge_pow rest r j h2
              have ihr := ih rest r h2
              simp [hge, ihr]
              rw [pow_succ]
              omega

/-- subOneAt j bits 展开为「保留前 j 位 + 对 drop j 减一」。 -/
lemma subOneAt_eq_drop (bits : List Bool) (j : ℕ) :
    subOneAt j bits = Option.map (fun r => (bits.take j) ++ r) (subOne (bits.drop j)) := by
  induction j generalizing bits with
  | zero => simp
  | succ j ih =>
      cases bits with
      | nil => simp [subOneAt]
      | cons b rest =>
          rw [subOneAt_succ_cons, ih]
          cases h : subOne (rest.drop j) with
          | none => simp [h]
          | some r => simp [h]

-- ============================================================================
-- 子集和语义与验证器正确性（骨架）
-- ============================================================================

-- 注意：`subsetSumHolds` 与 `selectedSum` 已上移到 `Mp.LowerBound`（与 `SubsetSumInstance`
-- 同层），采用位置选择语义（每个元素位置最多选一次）。本文件经 `import Mp.LowerBound`
-- 直接复用，不再本地定义。

-- ============================================================================
-- 磁带对齐与配置良构（减法不变量的基础）
-- ============================================================================

/-- 磁带在 [a, a + l.length) 与列表 l 逐格一致。 -/
def tapeAgrees (tape : ℤ → Sym) (a : ℤ) (l : List Sym) : Prop :=
  ∀ i : ℕ, ∀ (hi : i < l.length), tape (a + (i : ℤ)) = l[i]

@[simp] lemma tapeAgrees_nil (tape : ℤ → Sym) (a : ℤ) : tapeAgrees tape a [] := by
  intro i hi
  simp at hi

lemma tapeAgrees_cons (tape : ℤ → Sym) (a : ℤ) (s : Sym) (l : List Sym) :
    tapeAgrees tape a (s :: l) ↔ tape a = s ∧ tapeAgrees tape (a + 1) l := by
  constructor
  · intro h
    constructor
    · have h₀ := h 0 (by simp)
      rw [List.getElem_cons_zero s l] at h₀
      simpa using h₀
    · intro i hi
      have h₁ := h (i + 1) (by simp [hi])
      rw [List.getElem_cons_succ] at h₁
      have hidx : (a + ((i + 1 : ℕ) : ℤ)) = (a + 1 + (i : ℤ)) := by omega
      rw [hidx] at h₁
      exact h₁
  · rintro ⟨hs, hl⟩
    intro i hi
    cases i with
    | zero => simpa using hs
    | succ i =>
        have hi' : i < l.length := by simpa using hi
        have h₁ := hl i hi'
        have hidx : (a + 1 + (i : ℤ)) = (a + ((i + 1 : ℕ) : ℤ)) := by omega
        rw [hidx] at h₁
        rw [← List.getElem_cons_succ] at h₁
        exact h₁

lemma tapeAgrees_append (tape : ℤ → Sym) (a : ℤ) (l₁ l₂ : List Sym) :
    tapeAgrees tape a (l₁ ++ l₂) ↔
      tapeAgrees tape a l₁ ∧ tapeAgrees tape (a + (l₁.length : ℤ)) l₂ := by
  constructor
  · intro h
    constructor
    · intro i hi
      have h₁ := h i (by rw [List.length_append]; omega)
      rw [List.getElem_append_left hi] at h₁
      exact h₁
    · intro i hi
      have h₁ := h (l₁.length + i) (by rw [List.length_append]; omega)
      rw [List.getElem_append_right (by omega)] at h₁
      have hidx : (a + ((l₁.length + i : ℕ) : ℤ)) = (a + (l₁.length : ℤ) + (i : ℤ)) := by omega
      rw [hidx] at h₁
      simpa using h₁
  · rintro ⟨h₁, h₂⟩
    intro i hi
    rw [List.length_append] at hi
    by_cases hlt : i < l₁.length
    · have hget : (l₁ ++ l₂)[i] = l₁[i] := by
        rw [List.getElem_append_left hlt]
      rw [hget]
      exact h₁ i hlt
    · have hi₂ : i - l₁.length < l₂.length := by omega
      have hget : (l₁ ++ l₂)[i] = l₂[i - l₁.length] := by
        rw [List.getElem_append_right (by omega)]
      rw [hget]
      have h₂' := h₂ (i - l₁.length) hi₂
      have hidx : (a + (l₁.length : ℤ) + ((i - l₁.length : ℕ) : ℤ)) = (a + (i : ℤ)) := by omega
      rw [hidx] at h₂'
      exact h₂'

/-- 更新 tape 后，与列表的对齐关系保持（更新点在列表之外）。 -/
lemma tapeAgrees_write_outside (tape : ℤ → Sym) (a : ℤ) (l : List Sym)
    (pos : ℤ) (s : Sym) (hpos : pos < a ∨ a + (l.length : ℤ) ≤ pos) :
    tapeAgrees tape a l →
      tapeAgrees (fun i => if i = pos then s else tape i) a l := by
  intro h i hi
  have hne : a + (i : ℤ) ≠ pos := by
    rcases hpos with (hlt | hle)
    · have hnonneg : (0 : ℤ) ≤ (i : ℤ) := by exact_mod_cast Nat.zero_le i
      omega
    · have hltlen : (i : ℤ) < (l.length : ℤ) := by exact_mod_cast hi
      omega
  simp [hne, h i hi]

/-- Sym 列表 → 值位列表（data1 → true，其余 → false）。 -/
def symToBits (l : List Sym) : List Bool :=
  l.map (fun s => match s.1 with | SymKind.data1 => true | _ => false)

/-- 值位列表 → Sym 列表（true → data1，false → data0，4F4.4 位 false）。 -/
def bitsToSym (l : List Bool) : List Sym :=
  l.map (fun b => if b then Sym.data1 else Sym.data0)

/-- bitsToSym 产生符号都是 data0/data1。 -/
lemma bitsToSym_data (l : List Bool) : ∀ s ∈ bitsToSym l, s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
  intro s hs
  rcases List.mem_map.mp hs with ⟨b, hb, rfl⟩
  by_cases hb' : b <;> simp [hb', Sym.data1, Sym.data0, Sym.mk]

/-- bitsToSym 产生符号 4F4.4 位都是 false。 -/
lemma bitsToSym_marks (l : List Bool) : ∀ s ∈ bitsToSym l, s.2 = false := by
  intro s hs
  rcases List.mem_map.mp hs with ⟨b, hb, rfl⟩
  by_cases hb' : b <;> simp [hb', Sym.data1, Sym.data0, Sym.mk]

/-- decodeBitsSym 与 bitsValue ∘ symToBits 一致。 -/
lemma decodeBitsSym_eq_bitsValue (l : List Sym) :
    decodeBitsSym l = bitsValue (symToBits l) := by
  unfold decodeBitsSym bitsValue symToBits
  rw [List.map_map]
  apply congrArg (Nat.ofDigits 2)
  apply List.map_congr_left
  intro s _
  rcases s with ⟨k, m⟩
  cases k <;> rfl

/-- n 的可变长原生二进制值位列表（LSB 左）。 -/
def bitsOf (n : ℕ) : List Bool := symToBits (encodeBitsSym n)

/-- bitsOf 解码为 n。 -/
lemma bitsValue_bitsOf (n : ℕ) : bitsValue (bitsOf n) = n := by
  rw [bitsOf]
  rw [← decodeBitsSym_eq_bitsValue]
  exact decodeBitsSym_encodeBitsSym n

/-- 第 j 位为 1 ⟹ 值 ≥ 2^j（位权贡献）。 -/
lemma bitsValue_ge_pow_of_getElem_true (bits : List Bool) (j : ℕ) (hj : j < bits.length) (h : bits[j] = true) :
    2 ^ j ≤ bitsValue bits := by
  induction bits generalizing j with
  | nil => simp at hj
  | cons b rest ih =>
      cases j with
      | zero =>
          have hb : b = true := by
            simpa using h
          subst b
          simp [bitsValue, Nat.ofDigits]
      | succ j =>
          have hjr : j < rest.length := by
            have hj' : j + 1 < rest.length + 1 := by simpa using hj
            omega
          have h' : rest[j] = true := by
            simp [List.getElem_cons] at h
            exact h
          have hih := ih j hjr h'
          have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by
            rw [pow_succ]
            ring
          rw [hpow]
          rw [bitsValue_cons]
          have h2 : 2 * 2 ^ j ≤ 2 * bitsValue rest := Nat.mul_le_mul_left 2 hih
          cases b <;> omega

/-- bitsOf 的长度 = digits 长度（原生可变长）。 -/
lemma bitsOf_length (n : ℕ) : (bitsOf n).length = (Nat.digits 2 n).length := by
  rw [bitsOf]
  unfold symToBits
  rw [List.length_map]
  unfold encodeBitsSym
  rw [List.length_map]

/-- symToBits ∘ bitsToSym = id。 -/
lemma symToBits_bitsToSym (l : List Bool) : symToBits (bitsToSym l) = l := by
  unfold symToBits bitsToSym
  rw [List.map_map]
  apply map_eq_self_of_forall
  intro b _
  cases b <;> rfl

/-- 从配置 cfg₀ 经过合法步序列 π 到达 cfg'（每步读带头符号、转移合法）。 -/
inductive SymSteps (M : ℕ × Sym → Finset SymTransResult) (cfg₀ : SymConfig) :
    List SymStep → SymConfig → Prop
  | nil : SymSteps M cfg₀ [] cfg₀
  | cons : ∀ (π : List SymStep) (step : SymStep) (cfg' : SymConfig),
      SymSteps M cfg₀ π cfg' →
      step.fromState = cfg'.state →
      step.readSym = cfg'.tape cfg'.headPos →
      step.result ∈ M (cfg'.state, cfg'.tape cfg'.headPos) →
      SymSteps M cfg₀ (π ++ [step]) (symStepConfig cfg' step.result)

/-- SymSteps 与 SymReachablePath 一致（从初始配置出发）。 -/
lemma symSteps_initial_iff (M : ℕ × Sym → Finset SymTransResult) (input : List Sym)
    (π : List SymStep) (cfg : SymConfig) :
    SymSteps M (symInitialConfig input) π cfg ↔ SymReachablePath M input π cfg := by
  constructor <;> intro h
  · induction h
    · exact SymReachablePath.nil
    · rename_i π₀ step cfg₁ h_ind h_from h_read h_trans ih
      exact SymReachablePath.cons π₀ step cfg₁ ih h_from h_read h_trans
  · induction h
    · exact SymSteps.nil
    · rename_i π₀ step cfg h_ind h_from h_read h_trans ih
      exact SymSteps.cons π₀ step cfg ih h_from h_read h_trans

/-- SymSteps 的传递性：路径拼接。 -/
lemma SymSteps_trans (M : ℕ × Sym → Finset SymTransResult) (cfg₀ cfg₁ cfg₂ : SymConfig)
    (π₁ π₂ : List SymStep) :
    SymSteps M cfg₀ π₁ cfg₁ → SymSteps M cfg₁ π₂ cfg₂ →
    SymSteps M cfg₀ (π₁ ++ π₂) cfg₂ := by
  intro h₁ h₂
  induction h₂ generalizing π₁ with
  | nil => simpa using h₁
  | cons π₂' step cfg h_ind h_from h_read h_trans ih =>
      simpa [List.append_assoc] using
        SymSteps.cons (π₁ ++ π₂') step cfg (ih π₁ h₁) h_from h_read h_trans

@[simp] lemma bitsToSym_cons (b : Bool) (l : List Bool) :
    bitsToSym (b :: l) = (if b then Sym.data1 else Sym.data0) :: bitsToSym l := rfl

/-- bitsToSym ∘ symToBits = id（对 data0/data1 且 4F4.4 位 false 的列表）。 -/
lemma bitsToSym_symToBits_of_data (l : List Sym)
    (hdata : ∀ s ∈ l, s.1 = SymKind.data0 ∨ s.1 = SymKind.data1)
    (hmarks : ∀ s ∈ l, s.2 = false) :
    bitsToSym (symToBits l) = l := by
  unfold bitsToSym symToBits
  rw [List.map_map]
  apply map_eq_self_of_forall
  intro s hs
  rcases s with ⟨k, m⟩
  have hk : k = SymKind.data0 ∨ k = SymKind.data1 := hdata (k, m) hs
  have hm : m = false := hmarks (k, m) hs
  subst m
  cases hk <;> subst k <;> rfl

/-- 借位传播（状态 14）实现 subOne：从带头 p、状态 14 出发，
    若 subOne (symToBits bits) = some b'，则到达状态 81，
    磁带在 [p, p+|bits|) 变成 bitsToSym b'，且 p 左侧不变。 -/
lemma trans1_keep (s : Sym) (hs : s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) :
    { nextState := 1, writeSym := s, moveDir := Dir.R } ∈ VerifierSym.transition (1, s) := by
  rcases s with ⟨k, m⟩
  have hs' : k = SymKind.data0 ∨ k = SymKind.data1 := by simpa using hs
  rcases hs' with hk | hk <;> subst k <;> cases m <;> decide

/-- 状态 2 读 α(无标记)/data 符号：α 写 sel，其余写回自身，右移
    （β 与带标记 α 已非元素标记，读到即陷阱）。 -/
lemma trans2_sel (s : Sym)
    (hs : (s.1 = SymKind.alpha ∧ s.2 = false) ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) :
    { nextState := 2, writeSym := (if s.1 = SymKind.alpha then Sym.sel else s),
      moveDir := Dir.R } ∈ VerifierSym.transition (2, s) := by
  rcases s with ⟨k, m⟩
  have hs' : (k = SymKind.alpha ∧ m = false) ∨ k = SymKind.data0 ∨ k = SymKind.data1 := by
    simpa using hs
  rcases hs' with hk | hk | hk
  · rcases hk with ⟨hkα, hm⟩
    subst k
    subst m
    decide
  · subst k; cases m <;> decide
  · subst k; cases m <;> decide

/-- 状态 1 右扫 n 格 data 符号（写回自身）到 #₀，转状态 2，带头 #₀ 右侧。 -/
lemma scanRight1 (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hnb : ∀ i : ℤ, p ≤ i ∧ i < p + (n : ℤ) → (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hbound : tape (p + (n : ℤ)) = Sym.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 1 tape p) π cfg' ∧
      cfg'.state = 2 ∧ cfg'.headPos = p + (n : ℤ) + 1 ∧ cfg'.tape = tape := by
  induction n generalizing p tape with
  | zero =>
      have hbound' : tape p = Sym.boundary := by simpa using hbound
      let r : SymTransResult := { nextState := 2, writeSym := Sym.boundary, moveDir := Dir.R }
      let step : SymStep := { fromState := 1, readSym := Sym.boundary, result := r }
      refine ⟨[step], symStepConfig (SymConfig.mk 1 tape p) step.result, ?_, rfl, ?_, ?_⟩
      refine SymSteps.cons [] step (SymConfig.mk 1 tape p) SymSteps.nil ?_ ?_ ?_
      · rfl
      · change Sym.boundary = tape p
        rw [hbound']
      · change step.result ∈ VerifierSym.transition (1, tape p)
        rw [hbound']
        decide
      · simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
      · simp [symStepConfig, SymConfig.mk, step, r]
        funext i
        by_cases h : i = p <;> simp [h, hbound']
  | succ n ih =>
      let r : SymTransResult := { nextState := 1, writeSym := tape p, moveDir := Dir.R }
      let step : SymStep := { fromState := 1, readSym := tape p, result := r }
      have htrans : step.result ∈ VerifierSym.transition (1, tape p) := by
        exact trans1_keep (tape p) (hnb p (by constructor <;> omega))
      have hstep : SymSteps VerifierSym.transition (SymConfig.mk 1 tape p) [step]
          (symStepConfig (SymConfig.mk 1 tape p) step.result) := by
        refine SymSteps.cons [] step (SymConfig.mk 1 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans
      have hcfg₁ : symStepConfig (SymConfig.mk 1 tape p) step.result = SymConfig.mk 1 tape (p + 1) := by
        simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
        funext i
        by_cases h : i = p <;> simp [h]
      have hnb₁ : ∀ i : ℤ, p + 1 ≤ i ∧ i < p + 1 + (n : ℤ) → (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1 := by
        intro i h
        exact hnb i (by constructor <;> omega)
      have hbound₁ : tape (p + 1 + (n : ℤ)) = Sym.boundary := by
        have h' : p + 1 + (n : ℤ) = p + ((n + 1 : ℕ) : ℤ) := by omega
        rw [h']
        exact hbound
      rcases ih (p + 1) tape hnb₁ hbound₁ with ⟨π', cfg', hπ', hs', hhead', htape'⟩
      refine ⟨[step] ++ π', cfg', ?_, hs', ?_, htape'⟩
      · exact SymSteps_trans VerifierSym.transition (SymConfig.mk 1 tape p) (SymConfig.mk 1 tape (p + 1)) cfg'
          [step] π' (hcfg₁ ▸ hstep) hπ'
      · rw [hhead']
        omega

/-- data 位与 α/β 标记互斥。 -/
lemma kind_data_not_branch (k : SymKind) (hkind : k = SymKind.data0 ∨ k = SymKind.data1)
    (hbranch : k = SymKind.alpha ∨ k = SymKind.beta) : False := by
  rcases hkind with hk0 | hk1 <;> rcases hbranch with ha | hb
  · cases (hk0.symm.trans ha)
  · cases (hk0.symm.trans hb)
  · cases (hk1.symm.trans ha)
  · cases (hk1.symm.trans hb)

/-- 状态 2 右扫 n 格 α(无标记)/data 符号（α 写 sel，其余写回）到 #₁，转状态 3，带头停在 #₁ 上（S）；
    改写后元素区仍全非 boundary，且每格改写为「α → sel，其余写回」。 -/
lemma scanRight2_sel (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hnb : ∀ i : ℤ, p ≤ i ∧ i < p + (n : ℤ) →
      ((tape i).1 = SymKind.alpha ∧ (tape i).2 = false) ∨
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hbound : tape (p + (n : ℤ)) = Sym.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 2 tape p) π cfg' ∧
      cfg'.state = 3 ∧ cfg'.headPos = p + (n : ℤ) ∧
      (∀ i : ℤ, i < p → cfg'.tape i = tape i) ∧
      (∀ i : ℤ, p ≤ i ∧ i < p + (n : ℤ) → (cfg'.tape i).1 ≠ SymKind.boundary) ∧
      (∀ i : ℤ, p ≤ i ∧ i < p + (n : ℤ) →
        ((tape i).1 = SymKind.alpha ∨ (tape i).1 = SymKind.beta) →
          cfg'.tape i = Sym.sel ∨ cfg'.tape i = Sym.nosel) ∧
      (∀ i : ℤ, p ≤ i ∧ i < p + (n : ℤ) →
        ((tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1) → cfg'.tape i = tape i) ∧
      (cfg'.tape (p + (n : ℤ)) = Sym.boundary) := by
  induction n generalizing p tape with
  | zero =>
      have hbound' : tape p = Sym.boundary := by simpa using hbound
      let r : SymTransResult := { nextState := 3, writeSym := Sym.boundary, moveDir := Dir.S }
      let step : SymStep := { fromState := 2, readSym := Sym.boundary, result := r }
      refine ⟨[step], symStepConfig (SymConfig.mk 2 tape p) step.result, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · refine SymSteps.cons [] step (SymConfig.mk 2 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · change Sym.boundary = tape p
          rw [hbound']
        · change step.result ∈ VerifierSym.transition (2, tape p)
          rw [hbound']
          decide
      · simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
      · intro i hlt
        simp [symStepConfig, SymConfig.mk, step, r, hbound']
        intro h
        omega
      · intro i h
        omega
      · intro i h
        omega
      · intro i h
        omega
      · simp [symStepConfig, SymConfig.mk, step, r, hbound']
  | succ n ih =>
      let ws : Sym := if (tape p).1 = SymKind.alpha then Sym.sel else tape p
      let r : SymTransResult := { nextState := 2, writeSym := ws, moveDir := Dir.R }
      let step : SymStep := { fromState := 2, readSym := tape p, result := r }
      have htrans : step.result ∈ VerifierSym.transition (2, tape p) := by
        exact trans2_sel (tape p) (hnb p (by constructor <;> omega))
      let tape₁ : ℤ → Sym := fun i => if i = p then ws else tape i
      have hstep : SymSteps VerifierSym.transition (SymConfig.mk 2 tape p) [step]
          (symStepConfig (SymConfig.mk 2 tape p) step.result) := by
        refine SymSteps.cons [] step (SymConfig.mk 2 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans
      have hcfg₁ : symStepConfig (SymConfig.mk 2 tape p) step.result = SymConfig.mk 2 tape₁ (p + 1) := by
        simp [symStepConfig, SymConfig.mk, step, r, tape₁, Dir.toInt]
      have hnb₁ : ∀ i : ℤ, p + 1 ≤ i ∧ i < p + 1 + (n : ℤ) →
          ((tape₁ i).1 = SymKind.alpha ∧ (tape₁ i).2 = false) ∨
          (tape₁ i).1 = SymKind.data0 ∨ (tape₁ i).1 = SymKind.data1 := by
        intro i h
        have hne : i ≠ p := by omega
        have hnb' := hnb i (by constructor <;> omega)
        simpa [tape₁, hne] using hnb'
      have hbound₁ : tape₁ (p + 1 + (n : ℤ)) = Sym.boundary := by
        have hne : p + 1 + (n : ℤ) ≠ p := by omega
        have h' : p + 1 + (n : ℤ) = p + ((n + 1 : ℕ) : ℤ) := by omega
        rw [show tape₁ (p + 1 + (n : ℤ)) = tape (p + 1 + (n : ℤ)) from by simp [tape₁, hne]]
        rw [h']
        exact hbound
      rcases ih (p + 1) tape₁ hnb₁ hbound₁ with ⟨π', cfg', hπ', hs', hhead', hleft', hnb'', hrew₁', hrew₂', hfinal'⟩
      refine ⟨[step] ++ π', cfg', ?_, hs', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact SymSteps_trans VerifierSym.transition (SymConfig.mk 2 tape p) (SymConfig.mk 2 tape₁ (p + 1)) cfg'
          [step] π' (hcfg₁ ▸ hstep) hπ'
      · rw [hhead']
        omega
      · intro i hlt
        have hi : i < p + 1 := by omega
        have h' := hleft' i hi
        have hne : i ≠ p := by omega
        rw [h']
        simp [tape₁, hne]
      · intro i h
        by_cases heq : i = p
        · subst i
          have hws : ws.1 ≠ SymKind.boundary := by
            by_cases hb : (tape p).1 = SymKind.alpha
            · simp [ws, hb, Sym.sel]
            · have hnb_p := hnb p (by constructor <;> omega)
              have hnb_p' : (tape p).1 = SymKind.data0 ∨ (tape p).1 = SymKind.data1 := by
                rcases hnb_p with h | h | h
                · exfalso; exact hb h.1
                · exact Or.inl h
                · exact Or.inr h
              simp [ws, hb]
              rcases hnb_p' with h' | h' <;> rw [h'] <;> decide
          have h' := hleft' p (by omega)
          rw [h']
          simpa [tape₁] using hws
        · have hi' : p + 1 ≤ i ∧ i < p + 1 + (n : ℤ) := by
            constructor <;> omega
          exact hnb'' i hi'
      · intro i h hkind
        by_cases heq : i = p
        · subst i
          have h' := hleft' p (by omega)
          rw [h']
          rw [show tape₁ p = ws from by simp [tape₁]]
          dsimp [ws]
          rcases hkind with hα | hβ
          · rw [if_pos hα]
            left
            rfl
          · exfalso
            have hnb_p := hnb p (by constructor <;> omega)
            rcases hnb_p with hα' | hd0 | hd1
            · cases (hα'.1 ▸ hβ)
            · cases (hd0 ▸ hβ)
            · cases (hd1 ▸ hβ)
        · have hi' : p + 1 ≤ i ∧ i < p + 1 + (n : ℤ) := by
            constructor <;> omega
          have hrew := hrew₁' i hi' (by
            rw [show tape₁ i = tape i from by
              have hne : i ≠ p := by omega
              simp [tape₁, hne]]
            exact hkind)
          exact hrew
      · intro i h hkind
        by_cases heq : i = p
        · subst i
          have h' := hleft' p (by omega)
          rw [h']
          rw [show tape₁ p = ws from by simp [tape₁]]
          dsimp [ws]
          rw [if_neg]
          · intro ha
            exact kind_data_not_branch (tape p).1 hkind (Or.inl ha)
        · have hi' : p + 1 ≤ i ∧ i < p + 1 + (n : ℤ) := by
            constructor <;> omega
          have hrew := hrew₂' i hi' (by
            rw [show tape₁ i = tape i from by
              have hne : i ≠ p := by omega
              simp [tape₁, hne]]
            exact hkind)
          have hne : i ≠ p := by omega
          have htape₁_i : tape₁ i = tape i := by
            simp [tape₁, hne]
          rw [htape₁_i] at hrew
          exact hrew
      · have hpos : p + ((n + 1 : ℕ) : ℤ) = p + 1 + (n : ℤ) := by
          rw [Nat.cast_succ]
          ring
        rw [hpos]
        exact hfinal'

/-- 初始配置的磁带在 [0, |input|) 与 input 逐格一致。 -/
lemma symInitialConfig_tapeAgrees (input : List Sym) :
    tapeAgrees (symInitialConfig input).tape 0 input := by
  intro i hi
  simp [symInitialConfig, SymConfig.mk, hi]

/-- `encodeBitsSym` 的符号都是 data0/data1（非 boundary）。 -/
lemma encodeBitsSym_nonboundary (n : ℕ) :
    ∀ s ∈ encodeBitsSym n, s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
  intro s hs
  unfold encodeBitsSym at hs
  rcases List.mem_map.mp hs with ⟨d, hd, rfl⟩
  by_cases hd0 : d = 0 <;> simp [hd0, Sym.data0, Sym.data1, Sym.mk]

/-- `encodeBitsSymNative` 的符号都是 data0/data1（非 boundary）。 -/
lemma encodeBitsSymNative_nonboundary (n : ℕ) :
    ∀ s ∈ encodeBitsSymNative n, s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
  intro s hs
  unfold encodeBitsSymNative at hs
  rcases List.mem_map.mp hs with ⟨d, hd, rfl⟩
  by_cases h : d = 0 <;> simp [h, Sym.data0, Sym.data1, Sym.mk]

/-- `encodeElementsSym` 的符号都不是 boundary。 -/
lemma encodeElementsSym_nonboundary (k : ℕ) (elems : List ℕ) :
    ∀ s ∈ encodeElementsSym elems, s.1 ≠ SymKind.boundary := by
  intro s hs
  induction elems generalizing s with
  | nil => simp [encodeElementsSym] at hs
  | cons v rest ih =>
      cases rest with
      | nil =>
          simp [encodeElementsSym] at hs
          rcases hs with h | h
          · simp [Sym.alpha, Sym.mk] at h
            subst s
            decide
          · have h' := encodeBitsSymNative_nonboundary v s h
            rcases h' with h' | h' <;> rw [h'] <;> decide
      | cons w rest' =>
          simp [encodeElementsSym] at hs
          rcases hs with h | h | h
          · simp [Sym.alpha, Sym.mk] at h
            subst s
            decide
          · have h' := encodeBitsSymNative_nonboundary v s h
            rcases h' with h' | h' <;> rw [h'] <;> decide
          · exact ih s h

/-- `encodeElementsSym` 的符号种类：α、data0 或 data1（sep 已取消；β 不再用于编码）。 -/
lemma encodeElementsSym_kind (elems : List ℕ) :
    ∀ s ∈ encodeElementsSym elems,
      s.1 = SymKind.alpha ∨ s.1 = SymKind.beta ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
  intro s hs
  induction elems generalizing s with
  | nil => simp [encodeElementsSym] at hs
  | cons v rest ih =>
      cases rest with
      | nil =>
          simp [encodeElementsSym] at hs
          rcases hs with h | h
          · simp [Sym.alpha, Sym.mk] at h
            subst s
            left
            rfl
          · have h' := encodeBitsSymNative_nonboundary v s h
            rcases h' with h' | h'
            · right; right; left; exact h'
            · right; right; right; exact h'
      | cons w rest' =>
          simp [encodeElementsSym] at hs
          rcases hs with h | h | h
          · simp [Sym.alpha, Sym.mk] at h
            subst s
            left
            rfl
          · have h' := encodeBitsSymNative_nonboundary v s h
            rcases h' with h' | h'
            · right; right; left; exact h'
            · right; right; right; exact h'
          · exact ih s h

/-- 状态 24 读 data0（m=0）：最高位 0（元素 0 或前导 0）：拒绝。 -/
lemma trans24_data0 (s : Sym) (hk : s.1 = SymKind.data0) (hm : s.2 = false) :
    { nextState := 101, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (24, s) := by
  rcases s with ⟨k, m⟩
  have hk' : k = SymKind.data0 := by simpa using hk
  have hm' : m = false := by simpa using hm
  subst m; subst k
  decide

/-- 状态 24 读 data1（m=0）：首位即 1：v>0 ✓，转 29 扫完数据。 -/
lemma trans24_data1 (s : Sym) (hk : s.1 = SymKind.data1) (hm : s.2 = false) :
    { nextState := 29, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (24, s) := by
  rcases s with ⟨k, m⟩
  have hk' : k = SymKind.data1 := by simpa using hk
  have hm' : m = false := by simpa using hm
  subst m; subst k
  decide

/-- 状态 24 读 data（m=0）：d0 → 101（最高位 0：拒绝）、d1 → 29（v>0）。 -/
lemma trans24_data (s : Sym) (hk : s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) (hm : s.2 = false) :
    ({ nextState := 101, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (24, s) ∨
     { nextState := 29, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (24, s)) := by
  rcases s with ⟨k, m⟩
  have hk' : k = SymKind.data0 ∨ k = SymKind.data1 := by simpa using hk
  have hm' : m = false := by simpa using hm
  subst m
  rcases hk' with hk' | hk'
  · subst k
    left
    decide
  · subst k
    right
    decide

/-- 状态 29 读 data（m=0）：v>0 已证，扫完数据保持 29。 -/
lemma trans29_data (s : Sym) (hk : s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) (hm : s.2 = false) :
    { nextState := 29, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (29, s) := by
  rcases s with ⟨k, m⟩
  have hk' : k = SymKind.data0 ∨ k = SymKind.data1 := by simpa using hk
  have hm' : m = false := by simpa using hm
  subst m
  rcases hk' with hk' | hk' <;> subst k <;> decide

/-- 状态 29 读选择符（m=0）：配对 → 26。 -/
lemma trans29_sel (s : Sym) (hk : s.1 = SymKind.sel ∨ s.1 = SymKind.nosel) (hm : s.2 = false) :
    { nextState := 26, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (29, s) := by
  rcases s with ⟨k, m⟩
  have hk' : k = SymKind.sel ∨ k = SymKind.nosel := by simpa using hk
  have hm' : m = false := by simpa using hm
  subst m
  rcases hk' with hk' | hk' <;> subst k <;> decide

/-- 状态 26 读 data0（m=0）：下一对最高位 0：拒绝。 -/
lemma trans26_data0 (s : Sym) (hk : s.1 = SymKind.data0) (hm : s.2 = false) :
    { nextState := 101, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (26, s) := by
  rcases s with ⟨k, m⟩
  have hk' : k = SymKind.data0 := by simpa using hk
  have hm' : m = false := by simpa using hm
  subst m
  subst k
  decide

/-- 状态 26 读 data1（m=0）：转 29 左移（最右位 1，29 扫完剩余）。 -/
lemma trans26_data1 (s : Sym) (hk : s.1 = SymKind.data1) (hm : s.2 = false) :
    { nextState := 29, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (26, s) := by
  rcases s with ⟨k, m⟩
  have hk' : k = SymKind.data1 := by simpa using hk
  have hm' : m = false := by simpa using hm
  subst m
  subst k
  decide

/-- 状态 26 读 #₀（m=0）：转 27 左移。 -/
lemma trans26_hash : { nextState := 27, writeSym := Sym.boundary, moveDir := Dir.L } ∈
    VerifierSym.transition (26, Sym.boundary) := by
  decide

/-- 状态 27 读 data1（m=0）：target 最高位 1（target>0）：转 38 左移。 -/
lemma trans27_data1 (s : Sym) (hk : s.1 = SymKind.data1) (hm : s.2 = false) :
    { nextState := 38, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (27, s) := by
  rcases s with ⟨k, m⟩
  have hk' : k = SymKind.data1 := by simpa using hk
  have hm' : m = false := by simpa using hm
  subst m
  subst k
  decide

/-- 状态 27 读 data0（m=0）：target 最高位 0（target=0 或前导 0）：拒绝。 -/
lemma trans27_data0 (s : Sym) (hk : s.1 = SymKind.data0) (hm : s.2 = false) :
    { nextState := 101, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (27, s) := by
  rcases s with ⟨k, m⟩
  have hk' : k = SymKind.data0 := by simpa using hk
  have hm' : m = false := by simpa using hm
  subst m
  subst k
  decide

/-- 状态 38 读 data（m=0）：写回自身左移。 -/
lemma trans38_data (s : Sym) (hk : s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) (hm : s.2 = false) :
    { nextState := 38, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (38, s) := by
  rcases s with ⟨k, m⟩
  have hk' : k = SymKind.data0 ∨ k = SymKind.data1 := by simpa using hk
  have hm' : m = false := by simpa using hm
  subst m
  rcases hk' with hk' | hk' <;> subst k <;> decide

/-- 状态 38 读 #ₗ（m=0）：转 28 右移。 -/
lemma trans38_hash : { nextState := 28, writeSym := Sym.boundary, moveDir := Dir.R } ∈
    VerifierSym.transition (38, Sym.boundary) := by
  decide

/-- 状态 28 读 data：写回自身右移。 -/
lemma trans28_data (s : Sym) (hk : s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) :
    { nextState := 28, writeSym := s, moveDir := Dir.R } ∈ VerifierSym.transition (28, s) := by
  rcases s with ⟨k, m⟩
  have hk' : k = SymKind.data0 ∨ k = SymKind.data1 := by simpa using hk
  rcases hk' with hk' | hk' <;> subst k <;> cases m <;> decide

/-- 状态 28 读 #₀：转 4 右移。 -/
lemma trans28_hash : { nextState := 4, writeSym := Sym.boundary, moveDir := Dir.R } ∈
    VerifierSym.transition (28, Sym.boundary) := by
  decide

/-- 通用右移引理：状态 q 右移 n 格（读符号满足 keep 条件，写回自身右移）。 -/
lemma scanRightKeep (q : ℕ) (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hkeep : ∀ i : ℤ, p ≤ i ∧ i < p + (n : ℤ) → { nextState := q, writeSym := tape i, moveDir := Dir.R } ∈ VerifierSym.transition (q, tape i)) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk q tape p) π cfg' ∧
      cfg'.state = q ∧ cfg'.headPos = p + (n : ℤ) ∧ cfg'.tape = tape := by
  induction n generalizing p tape with
  | zero => exact ⟨[], SymConfig.mk q tape p, SymSteps.nil, rfl, by simp, rfl⟩
  | succ n ih =>
      let r : SymTransResult := { nextState := q, writeSym := tape p, moveDir := Dir.R }
      let step : SymStep := { fromState := q, readSym := tape p, result := r }
      have htrans : step.result ∈ VerifierSym.transition (q, tape p) := by
        exact hkeep p (by constructor <;> omega)
      have hstep : SymSteps VerifierSym.transition (SymConfig.mk q tape p) [step]
          (symStepConfig (SymConfig.mk q tape p) step.result) := by
        refine SymSteps.cons [] step (SymConfig.mk q tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans
      have hcfg₁ : symStepConfig (SymConfig.mk q tape p) step.result = SymConfig.mk q tape (p + 1) := by
        simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
        funext i
        by_cases h : i = p <;> simp [h]
      have hkeep₁ : ∀ i : ℤ, p + 1 ≤ i ∧ i < p + 1 + (n : ℤ) → { nextState := q, writeSym := tape i, moveDir := Dir.R } ∈ VerifierSym.transition (q, tape i) := by
        intro i h
        exact hkeep i (by constructor <;> omega)
      rcases ih (p + 1) tape hkeep₁ with ⟨π', cfg', hπ', hs', hhead', htape'⟩
      refine ⟨[step] ++ π', cfg', ?_, hs', ?_, htape'⟩
      · exact SymSteps_trans VerifierSym.transition (SymConfig.mk q tape p) (SymConfig.mk q tape (p + 1)) cfg'
          [step] π' (hcfg₁ ▸ hstep) hπ'
      · rw [hhead']
        omega

/-- 通用左扫引理（带位置谓词的 keep 条件，结束符号可为任意 w）：
    状态 q 从带头 p 出发左扫 n 格（写回自身），读 w 后写 w 转 q'（方向 d）。 -/
lemma scanLeftKeepPos (q q' : ℕ) (w : Sym) (d : Dir) (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hkeep : ∀ i : ℤ, p - (n : ℤ) < i ∧ i ≤ p →
      { nextState := q, writeSym := tape i, moveDir := Dir.L } ∈ VerifierSym.transition (q, tape i))
    (hend : { nextState := q', writeSym := w, moveDir := d } ∈ VerifierSym.transition (q, w))
    (hbound : tape (p - (n : ℤ)) = w) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk q tape p) π cfg' ∧
      cfg'.state = q' ∧ cfg'.headPos = p - (n : ℤ) + d.toInt ∧ cfg'.tape = tape := by
  induction n generalizing p tape with
  | zero =>
      let r : SymTransResult := { nextState := q', writeSym := w, moveDir := d }
      let step : SymStep := { fromState := q, readSym := w, result := r }
      have hbound' : tape p = w := by simpa using hbound
      refine ⟨[step], symStepConfig (SymConfig.mk q tape p) step.result, ?_, rfl, ?_, ?_⟩
      · refine SymSteps.cons [] step (SymConfig.mk q tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · change step.readSym = tape p
          rw [hbound']
        · change step.result ∈ VerifierSym.transition (q, tape p)
          rw [hbound']
          exact hend
      · simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
      · simp [symStepConfig, SymConfig.mk, step, r]
        funext i
        by_cases h : i = p <;> simp [h, hbound']
  | succ n ih =>
      let r : SymTransResult := { nextState := q, writeSym := tape p, moveDir := Dir.L }
      let step : SymStep := { fromState := q, readSym := tape p, result := r }
      have htrans : step.result ∈ VerifierSym.transition (q, tape p) := by
        exact hkeep p (by constructor <;> omega)
      have hstep : SymSteps VerifierSym.transition (SymConfig.mk q tape p) [step]
          (symStepConfig (SymConfig.mk q tape p) step.result) := by
        refine SymSteps.cons [] step (SymConfig.mk q tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans
      have hcfg : symStepConfig (SymConfig.mk q tape p) step.result = SymConfig.mk q tape (p - 1) := by
        simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
        constructor
        · funext i
          by_cases h : i = p <;> simp [h]
        · omega
      have hkeep₁ : ∀ i : ℤ, p - 1 - (n : ℤ) < i ∧ i ≤ p - 1 →
          { nextState := q, writeSym := tape i, moveDir := Dir.L } ∈ VerifierSym.transition (q, tape i) := by
        intro i h
        exact hkeep i (by constructor <;> omega)
      have hbound₁ : tape (p - 1 - (n : ℤ)) = w := by
        have h' : p - 1 - (n : ℤ) = p - ((n + 1 : ℕ) : ℤ) := by omega
        rw [h']
        exact hbound
      rcases ih (p - 1) tape hkeep₁ hbound₁ with ⟨π', cfg', hπ', hs', hhead', htape'⟩
      refine ⟨[step] ++ π', cfg', ?_, hs', ?_, ?_⟩
      · exact SymSteps_trans VerifierSym.transition (SymConfig.mk q tape p)
          (SymConfig.mk q tape (p - 1)) cfg' [step] π' (hcfg ▸ hstep) hπ'
      · have hh : cfg'.headPos = p - 1 - (n : ℤ) + d.toInt := by simpa using hhead'
        omega
      · simpa using htape'

/-- 列表之列表的连接（本环境无 List.join）。 -/
def joinLists {α : Type} (l : List (List α)) : List α :=
  l.foldr (fun a acc => a ++ acc) []

lemma joinLists_nil {α : Type} : joinLists ([] : List (List α)) = [] := by
  simp [joinLists]

lemma joinLists_cons {α : Type} (a : List α) (l : List (List α)) :
    joinLists (a :: l) = a ++ joinLists l := by
  simp [joinLists]

lemma joinLists_append {α : Type} (a b : List (List α)) :
    joinLists (a ++ b) = joinLists a ++ joinLists b := by
  induction a with
  | nil => simp [joinLists]
  | cons x rest ih =>
      rw [List.cons_append]
      rw [joinLists_cons (x : List α) (rest ++ b)]
      rw [ih]
      rw [joinLists_cons (x : List α) rest]
      simp [List.append_assoc]

lemma mem_joinLists {α : Type} (x : α) (L : List (List α)) :
    x ∈ joinLists L ↔ ∃ l ∈ L, x ∈ l := by
  induction L with
  | nil => simp [joinLists]
  | cons l rest ih =>
      rw [joinLists_cons (l : List α) rest]
      simp [List.mem_append, ih]

/-- 非空块列表 join 非空（每块的第二分量非空）。 -/
lemma blocksJoin_ne_nil (blocks : List (Sym × List Sym))
    (hne : blocks ≠ [])
    (hnonempty : ∀ b ∈ blocks, b.2 ≠ []) :
    joinLists (List.map (fun b => [b.1] ++ b.2) blocks) ≠ [] := by
  intro hels
  rcases blocks with _ | ⟨b0, bs⟩
  · exact hne rfl
  · have hmem : b0.1 ∈ joinLists (List.map (fun b => [b.1] ++ b.2) (b0 :: bs)) := by
      exact (mem_joinLists b0.1 (List.map (fun b => [b.1] ++ b.2) (b0 :: bs))).mpr ⟨[b0.1] ++ b0.2, by
        rw [List.mem_map]
        exact ⟨b0, List.mem_cons_self, rfl⟩, by simp⟩
    rw [hels] at hmem
    exact List.not_mem_nil hmem

/-- 非空块列表（每块 = 选择符 + 非空 data⁺）join 的末元素是 data 且 m=0。 -/
def chosenSub (s : Sym) : Sym :=
  if s.1 = SymKind.alpha ∨ s.1 = SymKind.beta then Sym.sel else s

/-- chosenSub 在 bits 编码上为恒等（全是 data 格）。 -/
lemma map_chosen_bits (n : ℕ) :
    (encodeBitsSym n).map chosenSub = encodeBitsSym n := by
  rw [encodeBitsSym]
  rw [List.map_map]
  congr
  funext d
  by_cases hd0 : d = 0 <;> simp [hd0, chosenSub, Sym.data0, Sym.data1]

/-- chosenSub 在原生可变长 bits 编码上为恒等。 -/
lemma map_chosen_bitsNative (n : ℕ) :
    (encodeBitsSymNative n).map chosenSub = encodeBitsSymNative n := by
  unfold encodeBitsSymNative
  rw [List.map_map]
  congr
  funext d
  by_cases hd : d = 0 <;> simp [hd, chosenSub, Sym.data0, Sym.data1]

/-- joinLists（全 sel 编码）与 encodeElementsSym 的 chosenSub 逐格替换一致。 -/
lemma joinLists_map_sel_eq (elems : List ℕ) :
    joinLists (elems.map (fun v => [Sym.sel] ++ encodeBitsSymNative v)) =
      (encodeElementsSym elems).map chosenSub := by
  induction elems with
  | nil => rfl
  | cons v rest ih =>
      rw [List.map_cons, joinLists_cons, ih]
      cases rest with
      | nil => simp [encodeElementsSym, List.map_append, map_chosen_bitsNative, Sym.alpha, chosenSub]
      | cons w rest' => simp [encodeElementsSym, List.map_append, map_chosen_bitsNative, Sym.alpha, chosenSub]

/-- 元素区 α/β 全换 sel 的逐格对应。 -/
lemma encodeElementsSym_chosen_cell (elems : List ℕ) (i : ℕ)
    (hi : i < (joinLists (elems.map (fun v => [Sym.sel] ++ encodeBitsSymNative v))).length)
    (hie : i < (encodeElementsSym elems).length) :
    (joinLists (elems.map (fun v => [Sym.sel] ++ encodeBitsSymNative v)))[i] =
      (if ((encodeElementsSym elems)[i]).1 = SymKind.alpha ∨ ((encodeElementsSym elems)[i]).1 = SymKind.beta
       then Sym.sel else (encodeElementsSym elems)[i]) := by
  rw [show (if ((encodeElementsSym elems)[i]).1 = SymKind.alpha ∨ ((encodeElementsSym elems)[i]).1 = SymKind.beta
       then Sym.sel else (encodeElementsSym elems)[i]) =
      ((encodeElementsSym elems).map chosenSub)[i]'(show i < ((encodeElementsSym elems).map chosenSub).length from by
        rw [List.length_map]
        exact hie) from by
    rw [List.getElem_map]
    rfl]
  rw [show (joinLists (elems.map (fun v => [Sym.sel] ++ encodeBitsSymNative v)))[i] =
      ((encodeElementsSym elems).map chosenSub)[i]'(by
        rw [← congrArg List.length (joinLists_map_sel_eq elems)]
        exact hi) from by
    congr 1
    exact joinLists_map_sel_eq elems]

/-- 格式检查左扫（从状态 29、带头在元素区右端数值位左侧一格出发）：
    逐块验证「选择符 + 非空 data⁺」，扫完元素区经 26 读 #₀ → 27（带头 tgt 右端），
    磁带不变。 -/
lemma trans76_keep (s : Sym)
    (hs : s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) :
    { nextState := 76, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (76, s) := by
  rcases s with ⟨k, m⟩
  rcases hs with hk | hk | hk
  · have hk' : k = SymKind.consumed := by simpa using hk
    subst hk'
    cases m <;> decide
  · have hk' : k = SymKind.data0 := by simpa using hk
    subst hk'
    cases m <;> decide
  · have hk' : k = SymKind.data1 := by simpa using hk
    subst hk'
    cases m <;> decide

/-- 状态 77 读 data0/data1：写回自身左移。 -/
lemma trans77_keep (s : Sym)
    (hs : s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) :
    { nextState := 77, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (77, s) := by
  rcases s with ⟨k, m⟩
  rcases hs with hk | hk
  · have hk' : k = SymKind.data0 := by simpa using hk
    subst hk'
    cases m <;> decide
  · have hk' : k = SymKind.data1 := by simpa using hk
    subst hk'
    cases m <;> decide

/-- 状态 8 读 consumed/data0/data1：写回自身左移。 -/
lemma trans8_keep (s : Sym)
    (hs : s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) :
    { nextState := 8, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (8, s) := by
  rcases s with ⟨k, m⟩
  rcases hs with hk | hk | hk
  · have hk' : k = SymKind.consumed := by simpa using hk
    subst hk'
    cases m <;> decide
  · have hk' : k = SymKind.data0 := by simpa using hk
    subst hk'
    cases m <;> decide
  · have hk' : k = SymKind.data1 := by simpa using hk
    subst hk'
    cases m <;> decide

/-- 状态 9 读 data0/data1：写回自身左移。 -/
lemma trans9_keep (s : Sym)
    (hs : s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) :
    { nextState := 9, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (9, s) := by
  rcases s with ⟨k, m⟩
  rcases hs with hk | hk
  · have hk' : k = SymKind.data0 := by simpa using hk
    subst hk'
    cases m <;> decide
  · have hk' : k = SymKind.data1 := by simpa using hk
    subst hk'
    cases m <;> decide

/-- 通用左移引理：状态 q 左移 n 格非 boundary（写回自身），读 boundary 转 q'（写 w，方向 d）。 -/
lemma scanLeftKeep (q q' : ℕ) (w : Sym) (d : Dir) (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hnb : ∀ i : ℤ, p - (n : ℤ) < i ∧ i ≤ p → (tape i).1 ≠ SymKind.boundary)
    (hbound : tape (p - (n : ℤ)) = Sym.boundary)
    (hkeep : ∀ s : Sym, s.1 ≠ SymKind.boundary → { nextState := q, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (q, s))
    (hend : { nextState := q', writeSym := w, moveDir := d } ∈ VerifierSym.transition (q, Sym.boundary))
    (hw : w = Sym.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk q tape p) π cfg' ∧
      cfg'.state = q' ∧ cfg'.headPos = p - (n : ℤ) + d.toInt ∧ cfg'.tape = tape := by
  induction n generalizing p tape with
  | zero =>
      let r : SymTransResult := { nextState := q', writeSym := w, moveDir := d }
      let step : SymStep := { fromState := q, readSym := Sym.boundary, result := r }
      have hbound' : tape p = Sym.boundary := by simpa using hbound
      refine ⟨[step], symStepConfig (SymConfig.mk q tape p) step.result, ?_, rfl, ?_, ?_⟩
      · refine SymSteps.cons [] step (SymConfig.mk q tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · change Sym.boundary = tape p
          rw [hbound']
        · change step.result ∈ VerifierSym.transition (q, tape p)
          rw [hbound']
          exact hend
      · simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
      · simp [symStepConfig, SymConfig.mk, step, r]
        funext i
        by_cases h : i = p <;> simp [h, hw, hbound']
  | succ n ih =>
      let r : SymTransResult := { nextState := q, writeSym := tape p, moveDir := Dir.L }
      let step : SymStep := { fromState := q, readSym := tape p, result := r }
      have htrans : step.result ∈ VerifierSym.transition (q, tape p) := by
        exact hkeep (tape p) (hnb p (by constructor <;> omega))
      have hstep : SymSteps VerifierSym.transition (SymConfig.mk q tape p) [step]
          (symStepConfig (SymConfig.mk q tape p) step.result) := by
        refine SymSteps.cons [] step (SymConfig.mk q tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans
      have hcfg₁ : symStepConfig (SymConfig.mk q tape p) step.result = SymConfig.mk q tape (p - 1) := by
        simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
        constructor
        · funext i
          by_cases h : i = p <;> simp [h]
        · omega
      have hnb₁ : ∀ i : ℤ, p - 1 - (n : ℤ) < i ∧ i ≤ p - 1 → (tape i).1 ≠ SymKind.boundary := by
        intro i h
        exact hnb i (by constructor <;> omega)
      have hbound₁ : tape (p - 1 - (n : ℤ)) = Sym.boundary := by
        have h' : p - 1 - (n : ℤ) = p - ((n + 1 : ℕ) : ℤ) := by omega
        rw [h']
        exact hbound
      rcases ih (p - 1) tape hnb₁ hbound₁ with ⟨π', cfg', hπ', hs', hhead', htape'⟩
      refine ⟨[step] ++ π', cfg', ?_, hs', ?_, htape'⟩
      · exact SymSteps_trans VerifierSym.transition (SymConfig.mk q tape p) (SymConfig.mk q tape (p - 1)) cfg'
          [step] π' (hcfg₁ ▸ hstep) hπ'
      · rw [hhead']
        omega

/-- 若 SymSteps 的每步带头位置都 ≥ p₀，则 cfg.tape i = cfg₀.tape i（i < p₀）。 -/
lemma SymSteps_tape_of_headPos_ge (M) (cfg₀ cfg : SymConfig) (π : List SymStep) (p₀ : ℤ)
    (hπ : SymSteps M cfg₀ π cfg)
    (hge : ∀ π₁ step π₂ cfg₁, π = π₁ ++ [step] ++ π₂ →
        SymSteps M cfg₀ π₁ cfg₁ → p₀ ≤ cfg₁.headPos) :
    ∀ i : ℤ, i < p₀ → cfg.tape i = cfg₀.tape i := by
  intro i hi
  induction hπ with
  | nil => rfl
  | cons π₀ step cfg_before hπ₀ h_from h_read h_trans ih =>
      have hge₀ : p₀ ≤ cfg_before.headPos := hge π₀ step [] cfg_before (by simp) hπ₀
      have hne : i ≠ cfg_before.headPos := by omega
      have htape : (symStepConfig cfg_before step.result).tape i = cfg_before.tape i := by
        simp only [symStepConfig]
        rw [if_neg hne]
      rw [htape]
      have hge₀' : ∀ π₁ step₁ π₂ cfg₁, π₀ = π₁ ++ [step₁] ++ π₂ → SymSteps M cfg₀ π₁ cfg₁ → p₀ ≤ cfg₁.headPos := by
        intro π₁ step₁ π₂ cfg₁ hπ₁ hsteps
        exact hge π₁ step₁ (π₂ ++ [step]) cfg₁ (by rw [hπ₁]; simp) hsteps
      exact ih hge₀'

/-- 若 SymSteps 的每步带头位置都 ≤ p₀，则 cfg.tape i = cfg₀.tape i（i > p₀）。 -/
lemma SymSteps_tape_of_headPos_le (M) (cfg₀ cfg : SymConfig) (π : List SymStep) (p₀ : ℤ)
    (hπ : SymSteps M cfg₀ π cfg)
    (hle : ∀ π₁ step π₂ cfg₁, π = π₁ ++ [step] ++ π₂ →
        SymSteps M cfg₀ π₁ cfg₁ → cfg₁.headPos ≤ p₀) :
    ∀ i : ℤ, p₀ < i → cfg.tape i = cfg₀.tape i := by
  intro i hi
  induction hπ with
  | nil => rfl
  | cons π₀ step cfg_before hπ₀ h_from h_read h_trans ih =>
      have hle₀ : cfg_before.headPos ≤ p₀ := hle π₀ step [] cfg_before (by simp) hπ₀
      have hne : i ≠ cfg_before.headPos := by omega
      have htape : (symStepConfig cfg_before step.result).tape i = cfg_before.tape i := by
        simp only [symStepConfig]
        rw [if_neg hne]
      rw [htape]
      have hle₀' : ∀ π₁ step₁ π₂ cfg₁, π₀ = π₁ ++ [step₁] ++ π₂ → SymSteps M cfg₀ π₁ cfg₁ → cfg₁.headPos ≤ p₀ := by
        intro π₁ step₁ π₂ cfg₁ hπ₁ hsteps
        exact hle π₁ step₁ (π₂ ++ [step]) cfg₁ (by rw [hπ₁]; simp) hsteps
      exact ih hle₀'

/-- 清除一个符号的 4F4.4 标记：consumed/data0 → data0，data1 → data1 false。 -/
def clearSym (s : Sym) : Sym :=
  if s.1 = SymKind.data1 then Sym.data1 false else Sym.data0

@[simp] lemma clearSym_data1 : clearSym Sym.data1 = Sym.data1 false := rfl
@[simp] lemma clearSym_data0 : clearSym Sym.data0 = Sym.data0 := rfl

/-- 状态 q 左移清循环的带头 = p₀ - |π₁|（L 步前缀，|π₁| ≤ n）。 -/
lemma scanLeftClear_headPos (q : ℕ) (n : ℕ) (p₀ : ℤ) (tape : ℤ → Sym)
    (hnb : ∀ i : ℤ, p₀ - (n : ℤ) < i ∧ i ≤ p₀ → (tape i).1 ≠ SymKind.boundary)
    (hclear : ∀ s : Sym, s.1 ≠ SymKind.boundary →
        VerifierSym.transition (q, s) = { { nextState := q, writeSym := clearSym s, moveDir := Dir.L } }) :
    ∀ (π₁ : List SymStep) (cfg₁ : SymConfig),
      SymSteps VerifierSym.transition (SymConfig.mk q tape p₀) π₁ cfg₁ →
      π₁.length ≤ n → cfg₁.headPos = p₀ - (π₁.length : ℤ) ∧ cfg₁.state = q := by
  intro π₁ cfg₁ hπ₁ hlen
  refine Nat.strong_induction_on (p := fun m => ∀ (π₁ : List SymStep) (cfg₁ : SymConfig),
      π₁.length = m → SymSteps VerifierSym.transition (SymConfig.mk q tape p₀) π₁ cfg₁ →
      π₁.length ≤ n → cfg₁.headPos = p₀ - (m : ℤ) ∧ cfg₁.state = q) π₁.length ?_ π₁ cfg₁ rfl hπ₁ hlen
  intro m ih π₁ cfg₁ hlen_m hπ₁ hlen
  cases hπ₁ with
  | nil => simp [SymConfig.mk, ← hlen_m]
  | cons π₀ step₀ cfg_before hπ₀ h_from h_read h_trans =>
      have hlen_m' : π₀.length + 1 = m := by simpa using hlen_m
      simp at hlen
      have hlen₀ : π₀.length ≤ n := by omega
      have hlt : π₀.length < m := by omega
      have hih₀ := ih π₀.length hlt π₀ cfg_before rfl hπ₀ hlen₀
      have hhead₀ : cfg_before.headPos = p₀ - (π₀.length : ℤ) := hih₀.1
      have hstate₀ : cfg_before.state = q := hih₀.2
      have hltn : π₀.length < n := by omega
      have hnb₀ : (step₀.readSym).1 ≠ SymKind.boundary := by
        rw [h_read]
        have htape_eq : cfg_before.tape (p₀ - (π₀.length : ℤ)) = tape (p₀ - (π₀.length : ℤ)) := by
          apply SymSteps_tape_of_headPos_ge VerifierSym.transition (SymConfig.mk q tape p₀) cfg_before π₀ (p₀ - (π₀.length : ℤ) + 1) hπ₀
          · intro π₀₁ step₀₁ π₀₂ cfg₀₁ hπ₀_eq hπ₀₁
            have hπ₀₁_lt : π₀₁.length < π₀.length := by
              rw [hπ₀_eq]
              simp
            have hlen₀₁ : π₀₁.length ≤ n := by omega
            have hlt₁ : π₀₁.length < m := by omega
            have hih₁ := ih π₀₁.length hlt₁ π₀₁ cfg₀₁ rfl hπ₀₁ hlen₀₁
            have hhead₀₁ : cfg₀₁.headPos = p₀ - (π₀₁.length : ℤ) := hih₁.1
            omega
          · omega
        rw [hhead₀]
        rw [htape_eq]
        exact hnb (p₀ - (π₀.length : ℤ)) (by constructor <;> omega)
      have hclear₀ : VerifierSym.transition (q, step₀.readSym) =
          { { nextState := q, writeSym := clearSym step₀.readSym, moveDir := Dir.L } } :=
        hclear step₀.readSym hnb₀
      have hres : step₀.result = { nextState := q, writeSym := clearSym step₀.readSym, moveDir := Dir.L } := by
        rw [hstate₀, ← h_read, hclear₀] at h_trans
        simp at h_trans
        exact h_trans
      simp [SymConfig.mk, symStepConfig, hres, Dir.toInt, hhead₀]
      omega

/-- 状态 q 左移清 n 格（clearSym），读 boundary 转到 q' 写 w 移 d。 -/
lemma scanLeftClear (q q' : ℕ) (w : Sym) (d : Dir) (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hnb : ∀ i : ℤ, p - (n : ℤ) < i ∧ i ≤ p → (tape i).1 ≠ SymKind.boundary)
    (hbound : tape (p - (n : ℤ)) = Sym.boundary)
    (hclear : ∀ s : Sym, s.1 ≠ SymKind.boundary →
        VerifierSym.transition (q, s) = { { nextState := q, writeSym := clearSym s, moveDir := Dir.L } })
    (hend : { nextState := q', writeSym := w, moveDir := d } ∈ VerifierSym.transition (q, Sym.boundary)) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk q tape p) π cfg' ∧
      cfg'.state = q' ∧ cfg'.headPos = p - (n : ℤ) + d.toInt ∧
      (∀ i : ℕ, i < n → cfg'.tape (p - (i : ℤ)) = clearSym (tape (p - (i : ℤ)))) ∧
      cfg'.tape (p - (n : ℤ)) = w ∧
      π.length = n + 1 := by
  induction n generalizing p tape with
  | zero =>
      let r : SymTransResult := { nextState := q', writeSym := w, moveDir := d }
      let step : SymStep := { fromState := q, readSym := Sym.boundary, result := r }
      have hbound' : tape p = Sym.boundary := by simpa using hbound
      refine ⟨[step], symStepConfig (SymConfig.mk q tape p) step.result, ?_, rfl, ?_, ?_, ?_, ?_⟩
      · refine SymSteps.cons [] step (SymConfig.mk q tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · change Sym.boundary = tape p
          rw [hbound']
        · change step.result ∈ VerifierSym.transition (q, tape p)
          rw [hbound']
          exact hend
      · simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
      · intro i hi; omega
      · simp [symStepConfig, SymConfig.mk, step, r]
      · simp
  | succ n ih =>
      let r : SymTransResult := { nextState := q, writeSym := clearSym (tape p), moveDir := Dir.L }
      let step : SymStep := { fromState := q, readSym := tape p, result := r }
      have htrans : step.result ∈ VerifierSym.transition (q, tape p) := by
        rw [hclear (tape p) (hnb p (by constructor <;> omega))]
        simp [step, r]
      have hstep : SymSteps VerifierSym.transition (SymConfig.mk q tape p) [step]
          (symStepConfig (SymConfig.mk q tape p) step.result) := by
        refine SymSteps.cons [] step (SymConfig.mk q tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans
      let tape1 : ℤ → Sym := fun i => if i = p then clearSym (tape p) else tape i
      have hcfg₁ : symStepConfig (SymConfig.mk q tape p) step.result = SymConfig.mk q tape1 (p - 1) := by
        simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
        constructor
        · funext i
          by_cases h : i = p <;> simp [h, tape1]
        · omega
      have hnb₁ : ∀ i : ℤ, p - 1 - (n : ℤ) < i ∧ i ≤ p - 1 → (tape1 i).1 ≠ SymKind.boundary := by
        intro i h
        by_cases hi : i = p
        · subst i; by_cases h : (tape p).1 = SymKind.data1 <;> simp [tape1, clearSym, h]
        · simp [tape1, hi]
          exact hnb i (by constructor <;> omega)
      have hbound₁ : tape1 (p - 1 - (n : ℤ)) = Sym.boundary := by
        have h' : p - 1 - (n : ℤ) = p - ((n + 1 : ℕ) : ℤ) := by omega
        rw [h']
        simp [tape1]
        exact hbound
      rcases ih (p - 1) tape1 hnb₁ hbound₁ with ⟨π', cfg', hπ', hs', hhead', hclear', hbound'', hπ_len'⟩
      refine ⟨[step] ++ π', cfg', ?_, hs', ?_, ?_, ?_, ?_⟩
      · exact SymSteps_trans VerifierSym.transition (SymConfig.mk q tape p) (SymConfig.mk q tape1 (p - 1)) cfg'
          [step] π' (hcfg₁ ▸ hstep) hπ'
      · rw [hhead']
        omega
      · intro i hi
        cases i with
        | zero =>
            have hkeep : cfg'.tape p = (SymConfig.mk q tape1 (p - 1)).tape p := by
              apply SymSteps_tape_of_headPos_le VerifierSym.transition (SymConfig.mk q tape1 (p - 1)) cfg' π' (p - 1) hπ'
              · intro π₁ step₁ π₂ cfg₁ hπ_eq hπ₁
                have hlen₁ : π₁.length ≤ n := by
                  have hπ₁_lt : π₁.length < π'.length := by
                    rw [hπ_eq]
                    simp
                  omega
                have hhead₁ : cfg₁.headPos = (p - 1) - (π₁.length : ℤ) :=
                  (scanLeftClear_headPos q n (p - 1) tape1 hnb₁ hclear π₁ cfg₁ hπ₁ hlen₁).1
                omega
              · omega
            simpa [SymConfig.mk, tape1] using hkeep
        | succ i =>
            have h := hclear' i (by omega)
            have hshift : p - ((i + 1 : ℕ) : ℤ) = (p - 1) - (i : ℤ) := by omega
            have htape1 : tape1 ((p - 1) - (i : ℤ)) = tape ((p - 1) - (i : ℤ)) := by
              simp only [tape1]
              rw [if_neg (by omega : (p - 1) - (i : ℤ) ≠ p)]
            rw [hshift, ← htape1]
            exact h
      · rw [show (p - ((n + 1 : ℕ) : ℤ)) = (p - 1) - (n : ℤ) from by omega]
        exact hbound''
      · simp [hπ_len']

/-- 状态 10 读 (data0/data1, true)：写回自身右移（扫 4F4.4 前缀）。 -/
lemma trans10_marked (s : Sym) (hs : s.2 = true) (hk : s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) :
    { nextState := 10, writeSym := s, moveDir := Dir.R } ∈ VerifierSym.transition (10, s) := by
  rcases s with ⟨k, m⟩
  have hm : m = true := by simpa using hs
  have hk' : k = SymKind.data0 ∨ k = SymKind.data1 := by simpa using hk
  subst m
  cases hk' <;> subst k <;> decide

/-- 状态 14 读 (data0, m)：借位传播（0 写 1，右移）。 -/
lemma trans14_borrow (m : Bool) :
    { nextState := 14, writeSym := Sym.data1 m, moveDir := Dir.R } ∈
      VerifierSym.transition (14, (SymKind.data0, m)) := by
  cases m <;> decide

/-- 状态 13 读 consumed：写 Sym.consumed 右移。 -/
lemma trans13_cons (s : Sym) (hs : s.1 = SymKind.consumed) :
    { nextState := 13, writeSym := Sym.consumed, moveDir := Dir.R } ∈ VerifierSym.transition (13, s) := by
  rcases s with ⟨k, m⟩
  have hk : k = SymKind.consumed := by simpa using hs
  subst k
  cases m <;> decide

/-- 状态 13 右移 n 格 consumed 到 v_{j+1}（data0/data1），转状态 5。 -/
lemma subOne_some_of_ge_one (bits : List Bool) (h : 1 ≤ bitsValue bits) :
    ∃ b', subOne bits = some b' := by
  induction bits with
  | nil => simp at h
  | cons b rest ih =>
      cases b with
      | true => exact ⟨false :: rest, rfl⟩
      | false =>
          have hge : 1 ≤ bitsValue rest := by
            have h' : 2 * bitsValue rest ≥ 1 := by simpa using h
            omega
          rcases ih hge with ⟨b', hb'⟩
          exact ⟨true :: b', by simp [hb']⟩

/-- subOne (bits.drop j) 成功 ⟸ 值 ≥ 2^j。 -/
lemma subOne_drop_some_of_ge_pow (bits : List Bool) (j : ℕ) (h : 2^j ≤ bitsValue bits) :
    ∃ b', subOne (bits.drop j) = some b' := by
  induction bits generalizing j with
  | nil => simp at h
  | cons b rest ih =>
      cases j with
      | zero =>
          exact subOne_some_of_ge_one (b :: rest) (by simpa using h)
      | succ j' =>
          have hge : 2^j' ≤ bitsValue rest := by
            cases b with
            | false =>
                have h' : 2 * 2^j' ≤ 2 * bitsValue rest := by
                  simpa [bitsValue, Nat.ofDigits, pow_succ, mul_comm] using h
                exact Nat.le_of_mul_le_mul_left h' (by decide)
            | true =>
                have h' : 2 * 2^j' ≤ 1 + 2 * bitsValue rest := by
                  simpa [bitsValue, Nat.ofDigits, pow_succ, mul_comm] using h
                omega
          rcases ih j' hge with ⟨b', hb'⟩
          exact ⟨b', by simpa [hb']⟩

/-- target 区编码：前 j 位 4F4.4 = true（已处理标记），后 k-j 位 4F4.4 = false。 -/
def targetTape (j : ℕ) (bits : List Bool) : List Sym :=
  (bits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true) ++
  bitsToSym (bits.drop j)

@[simp] lemma targetTape_length (j : ℕ) (bits : List Bool) :
    (targetTape j bits).length = bits.length := by
  simp [targetTape, bitsToSym, List.length_take, List.length_drop]
  omega

/-- `targetTape` 的符号都不是 boundary。 -/
lemma targetTape_nonboundary (j : ℕ) (bits : List Bool) :
    ∀ s ∈ targetTape j bits, s.1 ≠ SymKind.boundary := by
  intro s hs
  rw [targetTape, List.mem_append] at hs
  rcases hs with h | h
  · rcases List.mem_map.mp h with ⟨b, hb, rfl⟩
    by_cases hb' : b <;> simp [hb'] <;> decide
  · rcases List.mem_map.mp h with ⟨b, hb, rfl⟩
    by_cases hb' : b <;> simp [hb'] <;> decide

/-- targetTape j bits 的第 j 项是 t_j 的值位（4F4.4=false）。 -/
lemma targetTape_getElem_j (j : ℕ) (bits : List Bool) (h : j < bits.length) :
    (targetTape j bits)[j]'(by simpa using h) = (if bits[j] then Sym.data1 else Sym.data0) := by
  simp [targetTape, bitsToSym, List.getElem_append_right, List.getElem_drop,
    Nat.min_eq_left (Nat.le_of_lt h)]

/-- targetTape j bits 的第 io 项（io < j）：4F4.4=true（已处理标记）。 -/
lemma targetTape_getElem_lt (j io : ℕ) (bits : List Bool) (hio : io < bits.length) (hij : io < j) :
    (targetTape j bits)[io]'(by simpa using hio) =
      (if bits[io] then Sym.data1 true else Sym.data0 true) := by
  simp only [targetTape, bitsToSym]
  rw [List.getElem_append_left]
  · simp [List.getElem_take, List.getElem_map]
  · simp [List.length_take, hij, hio]

/-- targetTape j bits 的第 io 项（j ≤ io）：4F4.4=false。 -/
lemma targetTape_getElem_ge (j io : ℕ) (bits : List Bool) (hio : io < bits.length) (hj : j ≤ io) :
    (targetTape j bits)[io]'(by simpa using hio) = (if bits[io] then Sym.data1 else Sym.data0) := by
  have hj_lt : j < bits.length := Nat.lt_of_le_of_lt hj hio
  simp only [targetTape, bitsToSym]
  rw [List.getElem_append_right]
  · simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj_lt), List.getElem_map, List.getElem_drop,
      Nat.add_sub_cancel' hj]
  · simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj_lt)]
    omega

/-- targetTape j bits 的第 io 项：io<j 时 4F4.4=true，否则 4F4.4=false。 -/
lemma targetTape_getElem (j io : ℕ) (bits : List Bool) (hio : io < bits.length) :
    (targetTape j bits)[io]'(by simpa using hio) =
      (if io < j then (if bits[io] then Sym.data1 true else Sym.data0 true)
       else (if bits[io] then Sym.data1 else Sym.data0)) := by
  by_cases hij : io < j
  · rw [if_pos hij]
    exact targetTape_getElem_lt j io bits hio hij
  · rw [if_neg hij]
    exact targetTape_getElem_ge j io bits hio (Nat.le_of_not_gt hij)

/-- 只把 t_j 的 4F4.4 置 true，target 区从 targetTape j 变 targetTape (j+1)。 -/
lemma tape_agrees_targetTape_succ_mark (k j : ℕ) (tbits : List Bool) (p_t : ℤ) (tape tape2 : ℤ → Sym)
    (hlen_le : k ≤ tbits.length) (hj : j < k)
    (htarget : tapeAgrees tape p_t (targetTape j tbits))
    (htape2_tj : tape2 (p_t + (j : ℤ)) = (if tbits[j] then Sym.data1 true else Sym.data0 true))
    (htape2_other : ∀ i : ℤ, p_t ≤ i ∧ i < p_t + (tbits.length : ℤ) → i ≠ p_t + (j : ℤ) → tape2 i = tape i) :
    tapeAgrees tape2 p_t (targetTape (j + 1) tbits) := by
  intro i hi
  have hlen_target : (targetTape (j + 1) tbits).length = tbits.length := by
    simp [targetTape_length]
  have hlt : i < tbits.length := by simpa [hlen_target] using hi
  have hi_tbits : i < tbits.length := hlt
  by_cases hij : i < j + 1
  · have hget : (targetTape (j + 1) tbits)[i]'(by simpa using hi_tbits) = (if tbits[i] then Sym.data1 true else Sym.data0 true) := by
      exact targetTape_getElem_lt (j + 1) i tbits hi_tbits hij
    rw [hget]
    by_cases hij_eq : i = j
    · subst i
      exact htape2_tj
    · have hltj : i < j := by omega
      have h := htarget i (by simpa [targetTape_length] using hi_tbits)
      have hgetj : (targetTape j tbits)[i]'(by simpa using hi_tbits) = (if tbits[i] then Sym.data1 true else Sym.data0 true) := by
        exact targetTape_getElem_lt j i tbits hi_tbits hltj
      have htape : tape (p_t + (i : ℤ)) = (if tbits[i] then Sym.data1 true else Sym.data0 true) := by
        rw [h]
        exact hgetj
      rw [show tape2 (p_t + (i : ℤ)) = tape (p_t + (i : ℤ)) from htape2_other (p_t + (i : ℤ)) (by constructor <;> omega) (by omega)]
      exact htape
  · have hgt : j < i := by omega
    have hget : (targetTape (j + 1) tbits)[i]'(by simpa using hi_tbits) = (if tbits[i] then Sym.data1 else Sym.data0) := by
      exact targetTape_getElem_ge (j + 1) i tbits hi_tbits (Nat.succ_le_of_lt hgt)
    rw [hget]
    have h := htarget i (by simpa [targetTape_length] using hi_tbits)
    have hgetj : (targetTape j tbits)[i]'(by simpa using hi_tbits) = (if tbits[i] then Sym.data1 else Sym.data0) := by
      exact targetTape_getElem_ge j i tbits hi_tbits (Nat.le_of_lt hgt)
    have htape : tape (p_t + (i : ℤ)) = (if tbits[i] then Sym.data1 else Sym.data0) := by
      rw [h]
      exact hgetj
    rw [show tape2 (p_t + (i : ℤ)) = tape (p_t + (i : ℤ)) from htape2_other (p_t + (i : ℤ)) (by constructor <;> omega) (by omega)]
    exact htape

/-- targetTape (j+1)（对 drop j 减一后）拆为「前 j 位标记 + markFirst」。 -/
def markFirst (l : List Bool) : List Sym :=
  match l with
  | [] => []
  | b :: rest => (if b then Sym.data1 true else Sym.data0 true) :: bitsToSym rest

/-- markFirst 产生符号都非 consumed。 -/
lemma markFirst_nonconsumed (l : List Bool) : ∀ s ∈ markFirst l, s.1 ≠ SymKind.consumed := by
  intro s hs
  cases l with
  | nil => simp [markFirst] at hs
  | cons b rest =>
      simp [markFirst] at hs
      rcases hs with rfl | hs
      · by_cases hb : b <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]
      · rcases List.mem_map.mp hs with ⟨x, hx, rfl⟩
        by_cases hx' : x <;> simp [hx', Sym.data1, Sym.data0, Sym.mk]

/-- markFirst 保持长度。 -/
lemma markFirst_length (l : List Bool) : (markFirst l).length = l.length := by
  cases l with
  | nil => rfl
  | cons b rest => simp [markFirst, bitsToSym]

/-- 状态 10/11 的减一操作（10 标 t_j 计数器 m=1 → S 11；11 读 d1 → d0 R 81 完成，
    读 d0 → d1 R 14 借位右传）实现 subOne：值位变 bitsToSym b'，
    首位（t_j）置 m=1（已处理标记），p 左侧与尾部不变。 -/
lemma targetTape_succ_append (bits : List Bool) (j : ℕ) (b' : List Bool)
    (hsub : subOne (bits.drop j) = some b') :
    targetTape (j + 1) ((bits.take j) ++ b') =
      (bits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true) ++ markFirst b' := by
  have hb'_nonempty : b' ≠ [] := by
    intro hb'
    subst b'
    have hlen := subOne_length (bits.drop j) [] hsub
    have hdrop_empty : bits.drop j = [] := List.eq_nil_of_length_eq_zero hlen.symm
    rw [hdrop_empty] at hsub
    simp at hsub
  rcases b' with _ | ⟨b0, btail⟩
  · exfalso; exact hb'_nonempty rfl
  · rw [targetTape]
    have hdrop_nonempty : (bits.drop j) ≠ [] := by
      intro h; rw [h] at hsub; simp at hsub
    have hj_lt : j < bits.length := by
      have hne : (bits.drop j).length ≠ 0 := by
        intro h0; apply hdrop_nonempty; exact List.eq_nil_of_length_eq_zero h0
      rw [List.length_drop] at hne
      omega
    have hlen : (bits.take j).length = j := by
      simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj_lt)]
    have htake : ((bits.take j) ++ (b0 :: btail)).take (j + 1) = (bits.take j) ++ [b0] := by
      rw [List.take_append]
      have hgt : ¬ (j + 1 ≤ (bits.take j).length) := by rw [hlen]; omega
      simp [hgt, hlen]
    have hdrop : ((bits.take j) ++ (b0 :: btail)).drop (j + 1) = btail := by
      rw [List.drop_append]
      have hgt : ¬ (j + 1 ≤ (bits.take j).length) := by rw [hlen]; omega
      simp [hgt, hlen]
    rw [htake, hdrop]
    simp [markFirst, bitsToSym, List.map_append]

/-- #₀（boundary）在 p_e-1 且 target 区（targetTape）非 boundary ⟹ target 结束位 p_t+k < p_e。 -/
lemma boundary_after_target (k j : ℕ) (p_t p_e : ℤ) (tape : ℤ → Sym) (tbits : List Bool)
    (hlen_le : k ≤ tbits.length) (hj : j < k)
    (hp_t_le : p_t + (k : ℤ) ≤ p_e)
    (htarget : tapeAgrees tape p_t (targetTape j tbits))
    (hbound : tape (p_e - 1) = Sym.boundary) :
    p_t + (k : ℤ) < p_e := by
  by_cases h : p_t + (k : ℤ) < p_e
  · exact h
  · exfalso
    have hpe' : p_e = p_t + (k : ℤ) := by omega
    have hk1_lt : k - 1 < k := by omega
    have hlen : (targetTape j tbits).length = tbits.length := by
      simp [targetTape_length]
    have hk1 : k - 1 < (targetTape j tbits).length := by rw [hlen]; omega
    have ht : tape (p_t + ((k - 1 : ℕ) : ℤ)) = (targetTape j tbits)[k - 1]'hk1 := htarget (k - 1) hk1
    have hmem : (targetTape j tbits)[k - 1]'hk1 ∈ targetTape j tbits := List.getElem_mem hk1
    have hnb : ((targetTape j tbits)[k - 1]'hk1).1 ≠ SymKind.boundary :=
      targetTape_nonboundary j tbits ((targetTape j tbits)[k - 1]'hk1) hmem
    have hpos : p_e - 1 = p_t + ((k - 1 : ℕ) : ℤ) := by
      rw [hpe']
      omega
    rw [hpos] at hbound
    rw [ht] at hbound
    exact hnb (by
      simpa [Sym.boundary] using congrArg (fun s : Sym => s.1) hbound)

/-- target 区（tbits.length 长）在 #₀（p_e-1）之前结束（不等宽时 target 比元素区长）。 -/
lemma target_ends_before_pe (k j : ℕ) (p_t p_e : ℤ) (tape : ℤ → Sym) (tbits : List Bool)
    (hlen_le : k ≤ tbits.length) (hj : j < k)
    (hp_t_le : p_t + (k : ℤ) ≤ p_e)
    (htarget : tapeAgrees tape p_t (targetTape j tbits))
    (hbound : tape (p_e - 1) = Sym.boundary) :
    p_t + (tbits.length : ℤ) ≤ p_e - 1 := by
  by_cases h : p_t + (tbits.length : ℤ) ≤ p_e - 1
  · exact h
  · exfalso
    have hgt : p_e - 1 < p_t + (tbits.length : ℤ) := by omega
    have hge_p : p_t ≤ p_e - 1 := by
      have : p_t + (k : ℤ) ≤ p_e - 1 + 1 := by omega
      omega
    let idx : ℕ := (p_e - 1 - p_t).toNat
    have hidx_val : (idx : ℤ) = p_e - 1 - p_t := by
      dsimp [idx]
      exact Int.toNat_of_nonneg (by omega : 0 ≤ p_e - 1 - p_t)
    have hmem_idx : idx < (targetTape j tbits).length := by
      have hlen : (targetTape j tbits).length = tbits.length := by
        simp [targetTape_length]
      rw [hlen]
      have hz : (idx : ℤ) < (tbits.length : ℤ) := by
        rw [hidx_val]
        omega
      exact_mod_cast hz
    have ht : tape (p_e - 1) = (targetTape j tbits)[idx]'(hmem_idx) := by
      have hidx : p_t + (idx : ℤ) = p_e - 1 := by rw [hidx_val]; omega
      rw [← hidx]
      exact htarget idx hmem_idx
    have hmem : (targetTape j tbits)[idx]'(hmem_idx) ∈ targetTape j tbits := List.getElem_mem hmem_idx
    have hnb : ((targetTape j tbits)[idx]'(hmem_idx)).1 ≠ SymKind.boundary :=
      targetTape_nonboundary j tbits ((targetTape j tbits)[idx]'(hmem_idx)) hmem
    rw [ht] at hbound
    exact hnb (by
      simpa [Sym.boundary] using congrArg (fun s : Sym => s.1) hbound)

/-- 减一位循环（v_j = true 减 2^j，v_j = false 只标记）：
    从状态 5、带头 v_j 出发，target 值 `bitsValue tbits → bitsValue tbits - (if v_j then 2^j else 0)`，
    回到状态 5、带头 v_{j+1}，前 j+1 位 4F4.4 标记、前 j+1 位 consumed。 -/
lemma subOneAt_length (bits bits' : List Bool) (j : ℕ) (h : subOneAt j bits = some bits') :
    bits'.length = bits.length := by
  induction j generalizing bits bits' with
  | zero => exact subOne_length bits bits' h
  | succ j ih =>
      cases bits with
      | nil => simp at h
      | cons b rest =>
          cases h2 : subOneAt j rest with
          | none => simp [h2] at h
          | some r =>
              simp [h2] at h
              subst bits'
              have := ih rest r h2
              simp [this]

/-- subOneAt j bits 成功 ⟸ 值 ≥ 2^j。 -/
lemma subOneAt_some_of_ge_pow (bits : List Bool) (j : ℕ) (h : 2 ^ j ≤ bitsValue bits) :
    ∃ bits', subOneAt j bits = some bits' := by
  rw [subOneAt_eq_drop]
  rcases subOne_drop_some_of_ge_pow bits j h with ⟨b', hb'⟩
  exact ⟨(bits.take j) ++ b', by simp [hb']⟩

/-- 从 tbits 的第 j 位起，逐位减 ebits 的 true 位（LSB 左）。 -/
def subAllBitsAt (tbits ebits : List Bool) (j : ℕ) : List Bool :=
  match ebits with
  | [] => tbits
  | b :: rest => subAllBitsAt (if b then (subOneAt j tbits).getD tbits else tbits) rest (j + 1)

/-- 逐位减 ebits 的所有 true 位（LSB 左，j = 0 起）。 -/
def subAllBits (tbits ebits : List Bool) : List Bool := subAllBitsAt tbits ebits 0

/-- subAllBitsAt 保持长度。 -/
lemma subAllBitsAt_length (tbits ebits : List Bool) (j : ℕ) :
    (subAllBitsAt tbits ebits j).length = tbits.length := by
  induction ebits generalizing tbits j with
  | nil => rfl
  | cons b rest ih =>
      dsimp [subAllBitsAt]
      by_cases hb : b
      · cases h : subOneAt j tbits with
        | none => simp [hb, h]; exact ih tbits (j + 1)
        | some r =>
            have hlen : r.length = tbits.length := subOneAt_length tbits r j h
            simp [hb, h, hlen]
            simpa [hlen] using ih r (j + 1)
      · simp [hb]; exact ih tbits (j + 1)

/-- subAllBits 保持长度。 -/
lemma subAllBits_length (tbits ebits : List Bool) : (subAllBits tbits ebits).length = tbits.length := by
  rw [subAllBits]
  exact subAllBitsAt_length tbits ebits 0

/-- subAllBitsAt 的值：bitsValue (subAllBitsAt tbits ebits j) = bitsValue tbits - 2^j * bitsValue ebits。 -/
lemma subAllBitsAt_value (tbits ebits : List Bool) (j : ℕ)
    (hle : 2 ^ j * bitsValue ebits ≤ bitsValue tbits) :
    bitsValue (subAllBitsAt tbits ebits j) = bitsValue tbits - 2 ^ j * bitsValue ebits := by
  induction ebits generalizing tbits j with
  | nil => simp [subAllBitsAt]
  | cons b rest ih =>
      dsimp [subAllBitsAt]
      by_cases hb : b
      · -- b = true：减 2^j
        have hbval : bitsValue (b :: rest) = 1 + 2 * bitsValue rest := by simp [hb]
        have hge : 2 ^ j ≤ bitsValue tbits := by
          have hle' : 2 ^ j * (1 + 2 * bitsValue rest) ≤ bitsValue tbits := by simpa [hbval] using hle
          have h1 : 1 ≤ 1 + 2 * bitsValue rest := by omega
          have hmul : 2 ^ j ≤ 2 ^ j * (1 + 2 * bitsValue rest) := by
            have : 2 ^ j * 1 ≤ 2 ^ j * (1 + 2 * bitsValue rest) := Nat.mul_le_mul_left (2 ^ j) h1
            simpa using this
          exact le_trans hmul hle'
        rcases subOneAt_some_of_ge_pow tbits j hge with ⟨r, hr⟩
        have hsub : bitsValue r = bitsValue tbits - 2 ^ j := subOneAt_correct tbits r j hr
        have hrec := ih r (j + 1) (by
          have hle' : 2 ^ j * (1 + 2 * bitsValue rest) ≤ bitsValue tbits := by simpa [hbval] using hle
          have hle'' : 2 ^ j + 2 ^ j * (2 * bitsValue rest) ≤ bitsValue tbits := by
            have : 2 ^ j + 2 ^ j * (2 * bitsValue rest) = 2 ^ j * (1 + 2 * bitsValue rest) := by ring
            rw [this]
            exact hle'
          have hpow : 2 ^ j * (2 * bitsValue rest) = 2 ^ (j + 1) * bitsValue rest := by
            rw [pow_succ]
            ring
          rw [hsub, ← hpow]
          omega)
        simp [hb, hr, subAllBitsAt]
        rw [hrec, hsub]
        have hpow : 2 ^ j * (1 + 2 * bitsValue rest) = 2 ^ j + 2 ^ (j + 1) * bitsValue rest := by
          rw [mul_add, mul_one, pow_succ]
          ring
        rw [hpow]
        omega
      · -- b = false：不减
        have hbval : bitsValue (b :: rest) = 2 * bitsValue rest := by simp [hb]
        have hrec := ih tbits (j + 1) (by
          have hle' : 2 ^ j * (2 * bitsValue rest) ≤ bitsValue tbits := by simpa [hbval] using hle
          have hpow : 2 ^ (j + 1) * bitsValue rest = 2 ^ j * (2 * bitsValue rest) := by
            rw [pow_succ]
            ring
          rwa [hpow])
        simp [hb, subAllBitsAt]
        rw [hrec]
        have hpow : 2 ^ (j + 1) * bitsValue rest = 2 ^ j * (2 * bitsValue rest) := by
          rw [pow_succ]
          ring
        rw [hpow]

/-- subAllBits 的值：bitsValue (subAllBits tbits ebits) = bitsValue tbits - bitsValue ebits。 -/
lemma subAllBits_value (tbits ebits : List Bool) (hle : bitsValue ebits ≤ bitsValue tbits) :
    bitsValue (subAllBits tbits ebits) = bitsValue tbits - bitsValue ebits := by
  rw [subAllBits]
  simpa using subAllBitsAt_value tbits ebits 0 (by simpa using hle)

/-- bitsValue 的 append 分解：bitsValue (a ++ b) = bitsValue a + 2^a.length * bitsValue b。 -/
lemma bitsValue_append (a b : List Bool) :
    bitsValue (a ++ b) = bitsValue a + 2 ^ a.length * bitsValue b := by
  induction a with
  | nil => simp
  | cons x rest ih =>
      simp [bitsValue_cons, ih, List.length_cons]
      rw [pow_succ]
      ring

/-- bitsValue = 0 ⟺ 全 false。 -/
lemma bitsValue_eq_zero_iff_all_false (bits : List Bool) :
    bitsValue bits = 0 ↔ ∀ b ∈ bits, b = false := by
  induction bits with
  | nil => simp
  | cons b rest ih =>
      simp [bitsValue_cons]
      constructor
      · intro h
        by_cases hb : b = true
        · simp [hb] at h
        · have hbf : b = false := by
            cases b <;> simp at hb ⊢
          have hrest0 : bitsValue rest = 0 := by
            simp [hbf] at h
            omega
          exact ⟨by simpa [hbf], by simpa using (ih.mp hrest0)⟩
      · intro h
        have hb : b = false := h.1
        have hrest : ∀ b' ∈ rest, b' = false := by
          intro b' hb'
          by_contra hbt
          have hb'true : b' = true := by
            cases b' <;> simp at hbt ⊢
          exact h.2 (by simpa [hb'true] using hb')
        simp [hb, ih.mpr hrest]

/-- 2^j * bitsValue (drop j bits) ≤ bitsValue bits（LSB 左的位权）。 -/
lemma bitsValue_drop_le (bits : List Bool) (j : ℕ) :
    2 ^ j * bitsValue (bits.drop j) ≤ bitsValue bits := by
  by_cases hj : j ≤ bits.length
  · have h := bitsValue_append (bits.take j) (bits.drop j)
    rw [List.take_append_drop] at h
    have hlen : (bits.take j).length = j := by simp [List.length_take, Nat.min_eq_left hj]
    rw [h, hlen]
    omega
  · have hdrop : bits.drop j = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [List.length_drop]
      omega
    rw [hdrop]
    simp
/-- 状态 21 读 data/consumed：写 data0 右移（占位扩展的清除）。 -/
lemma trans21_data (s : Sym) (hk : s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.consumed) :
    { nextState := 21, writeSym := Sym.data0, moveDir := Dir.R } ∈ VerifierSym.transition (21, s) := by
  rcases s with ⟨k, m⟩
  cases m <;> rcases hk with hk | hk | hk <;> dsimp at hk <;> simp [hk, VerifierSym.transition, VerifierSym.legalStates]

/-- 状态 21 读选择符/boundary：sel/nosel → 51 L，boundary → 22 S（#₁ → 判定）。 -/
lemma trans21_end (s : Sym) (hk : s.1 = SymKind.sel ∨ s.1 = SymKind.nosel ∨ s.1 = SymKind.boundary) :
    (s.1 = SymKind.sel ∨ s.1 = SymKind.nosel →
      { nextState := 51, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (21, s)) ∧
    (s.1 = SymKind.boundary →
      { nextState := 22, writeSym := s, moveDir := Dir.S } ∈ VerifierSym.transition (21, s)) := by
  rcases s with ⟨k, m⟩
  constructor
  · intro hk'
    rcases hk' with hk' | hk'
    · dsimp at hk'
      subst k
      cases m <;> simp [VerifierSym.transition, VerifierSym.legalStates]
    · dsimp at hk'
      subst k
      cases m <;> simp [VerifierSym.transition, VerifierSym.legalStates]
  · intro hk'
    dsimp at hk'
    subst k
    cases m <;> simp [VerifierSym.transition, VerifierSym.legalStates]

/-- 状态 21 清除扫描：从带头 p 出发（p 处为 data），右扫 n+1 格写 data0，
    遇 sel/nosel → 51（还有下一个元素），遇 boundary → 22（#₁ → 判定）。 -/
lemma scanClear21 (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hstart : tape p = Sym.data0 ∨ tape p = Sym.data1 ∨ tape p = Sym.consumed)
    (hdata : ∀ i : ℕ, i < n → tape (p + 1 + (i : ℤ)) = Sym.data0 ∨
        tape (p + 1 + (i : ℤ)) = Sym.data1 ∨ tape (p + 1 + (i : ℤ)) = Sym.consumed)
    (hend : tape (p + 1 + (n : ℤ)) = Sym.sel ∨ tape (p + 1 + (n : ℤ)) = Sym.nosel ∨
        (tape (p + 1 + (n : ℤ))).1 = SymKind.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 21 tape p) π cfg' ∧
      (cfg'.state = 51 ∨ cfg'.state = 22) ∧
      (cfg'.headPos = p + (n : ℤ) ∨ cfg'.headPos = p + 1 + (n : ℤ)) ∧
      ((tape (p + 1 + (n : ℤ))).1 = SymKind.boundary → cfg'.state = 22 ∧ cfg'.headPos = p + 1 + (n : ℤ)) ∧
      ((tape (p + 1 + (n : ℤ))).1 = SymKind.sel ∨ (tape (p + 1 + (n : ℤ))).1 = SymKind.nosel →
        cfg'.state = 51 ∧ cfg'.headPos = p + (n : ℤ)) ∧
      tapeAgrees cfg'.tape p (List.replicate (n + 1) Sym.data0) ∧
      (cfg'.tape (p + 1 + (n : ℤ)) = Sym.sel ∨
        cfg'.tape (p + 1 + (n : ℤ)) = Sym.nosel ∨ (cfg'.tape (p + 1 + (n : ℤ))).1 = SymKind.boundary) ∧
      (∀ i : ℤ, i < p → cfg'.tape i = tape i) ∧
      (cfg'.tape (p + 1 + (n : ℤ)) = tape (p + 1 + (n : ℤ))) ∧
      (∀ i : ℤ, p + 1 + (n : ℤ) < i → cfg'.tape i = tape i) := by
  induction n generalizing p tape hstart with
  | zero =>
      -- 只有选择位（p 处）是 data，hend 在 p+1：21 读 data → 21 写 data0 R，再读结束符收尾
      let r1 : SymTransResult := { nextState := 21, writeSym := Sym.data0, moveDir := Dir.R }
      let step1 : SymStep := { fromState := 21, readSym := tape p, result := r1 }
      have hstep1 : SymSteps VerifierSym.transition (SymConfig.mk 21 tape p) [step1]
          (symStepConfig (SymConfig.mk 21 tape p) step1.result) := by
        refine SymSteps.cons [] step1 (SymConfig.mk 21 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · change step1.result ∈ VerifierSym.transition (21, tape p)
          exact trans21_data (tape p) (by
            have h1 : (tape p).1 = SymKind.data0 ∨ (tape p).1 = SymKind.data1 ∨ (tape p).1 = SymKind.consumed := by
              rcases hstart with h | h | h <;> simp [h, Sym.data0, Sym.data1, Sym.consumed]
            exact h1)
      let tape1 : ℤ → Sym := fun i => if i = p then Sym.data0 else tape i
      have hcfg1 : symStepConfig (SymConfig.mk 21 tape p) step1.result = SymConfig.mk 21 tape1 (p + 1) := by
        simp [symStepConfig, SymConfig.mk, step1, r1, tape1, Dir.toInt]
      rcases hend with hsel | hnosel | hbound
      · -- sel → 51 L
        let r2 : SymTransResult := { nextState := 51, writeSym := tape (p + 1), moveDir := Dir.L }
        let step2 : SymStep := { fromState := 21, readSym := tape (p + 1), result := r2 }
        have hstep2 : SymSteps VerifierSym.transition (SymConfig.mk 21 tape1 (p + 1)) [step2]
            (symStepConfig (SymConfig.mk 21 tape1 (p + 1)) step2.result) := by
          refine SymSteps.cons [] step2 (SymConfig.mk 21 tape1 (p + 1)) SymSteps.nil ?_ ?_ ?_
          · rfl
          · simp [step2, tape1]
          · change step2.result ∈ VerifierSym.transition (21, tape1 (p + 1))
            simp [tape1]
            have hk1 : (tape (p + 1)).1 = SymKind.sel := by
              have h := congrArg (fun s : Sym => s.1) hsel
              simpa [Sym.sel] using h
            exact (trans21_end (tape (p + 1)) (Or.inl hk1)).1 (Or.inl hk1)
        refine ⟨[step1, step2], symStepConfig (symStepConfig (SymConfig.mk 21 tape p) step1.result) step2.result,
          SymSteps_trans VerifierSym.transition (SymConfig.mk 21 tape p) (SymConfig.mk 21 tape1 (p + 1))
            (symStepConfig (symStepConfig (SymConfig.mk 21 tape p) step1.result) step2.result)
            [step1] [step2] ?_ hstep2, ?_⟩
        · simpa [hcfg1] using hstep1
        · -- 结论：state = 51，headPos = p，replicate 1，保持
          refine ⟨Or.inl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact Or.inl (by simp [symStepConfig, step1, r1, step2, r2, Dir.toInt])
          · intro hb
            exfalso
            have hb' : (tape (p + 1)).1 = SymKind.boundary := by simpa using hb
            have hsel' : (tape (p + 1)).1 = SymKind.sel := by
              have h := congrArg (fun s : Sym => s.1) hsel
              simpa [Sym.sel] using h
            rw [hsel'] at hb'
            cases hb'
          · intro h
            exact ⟨rfl, by simp [symStepConfig, step1, r1, step2, r2, Dir.toInt]⟩
          · -- tapeAgrees replicate 1
            intro i hi
            have hi0 : i = 0 := by
              simp at hi
              omega
            subst i
            simp [List.getElem_replicate, symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt]
          · left
            simp [symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt]
            simpa using hsel
          · intro j hj
            have hj1 : j ≠ p + 1 := by omega
            have hj2 : j ≠ p := by omega
            simp [symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt, hj1, hj2]
          · simp [symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt]
          · intro j hj
            have hj1 : j ≠ p + 1 := by omega
            have hj2 : j ≠ p := by omega
            simp [symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt, hj1, hj2]
      · -- nosel → 51 L
        let r2 : SymTransResult := { nextState := 51, writeSym := tape (p + 1), moveDir := Dir.L }
        let step2 : SymStep := { fromState := 21, readSym := tape (p + 1), result := r2 }
        have hstep2 : SymSteps VerifierSym.transition (SymConfig.mk 21 tape1 (p + 1)) [step2]
            (symStepConfig (SymConfig.mk 21 tape1 (p + 1)) step2.result) := by
          refine SymSteps.cons [] step2 (SymConfig.mk 21 tape1 (p + 1)) SymSteps.nil ?_ ?_ ?_
          · rfl
          · simp [step2, tape1]
          · change step2.result ∈ VerifierSym.transition (21, tape1 (p + 1))
            simp [tape1]
            have hk1 : (tape (p + 1)).1 = SymKind.nosel := by
              have h := congrArg (fun s : Sym => s.1) hnosel
              simpa [Sym.nosel] using h
            exact (trans21_end (tape (p + 1)) (Or.inr (Or.inl hk1))).1 (Or.inr hk1)
        refine ⟨[step1, step2], symStepConfig (symStepConfig (SymConfig.mk 21 tape p) step1.result) step2.result,
          SymSteps_trans VerifierSym.transition (SymConfig.mk 21 tape p) (SymConfig.mk 21 tape1 (p + 1))
            (symStepConfig (symStepConfig (SymConfig.mk 21 tape p) step1.result) step2.result)
            [step1] [step2] ?_ hstep2, ?_⟩
        · simpa [hcfg1] using hstep1
        · refine ⟨Or.inl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact Or.inl (by simp [symStepConfig, step1, r1, step2, r2, Dir.toInt])
          · intro hb
            exfalso
            have hb' : (tape (p + 1)).1 = SymKind.boundary := by simpa using hb
            have hnosel' : (tape (p + 1)).1 = SymKind.nosel := by
              have h := congrArg (fun s : Sym => s.1) hnosel
              simpa [Sym.nosel] using h
            rw [hnosel'] at hb'
            cases hb'
          · intro h
            exact ⟨rfl, by simp [symStepConfig, step1, r1, step2, r2, Dir.toInt]⟩
          · intro i hi
            have hi0 : i = 0 := by
              simp at hi
              omega
            subst i
            simp [List.getElem_replicate, symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt]
          · right; left
            simp [symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt]
            simpa using hnosel
          · intro j hj
            have hj1 : j ≠ p + 1 := by omega
            have hj2 : j ≠ p := by omega
            simp [symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt, hj1, hj2]
          · simp [symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt]
          · intro j hj
            have hj1 : j ≠ p + 1 := by omega
            have hj2 : j ≠ p := by omega
            simp [symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt, hj1, hj2]
      · -- boundary → 22 S（#₁ → 判定）
        let r2 : SymTransResult := { nextState := 22, writeSym := tape (p + 1), moveDir := Dir.S }
        let step2 : SymStep := { fromState := 21, readSym := tape (p + 1), result := r2 }
        have hstep2 : SymSteps VerifierSym.transition (SymConfig.mk 21 tape1 (p + 1)) [step2]
            (symStepConfig (SymConfig.mk 21 tape1 (p + 1)) step2.result) := by
          refine SymSteps.cons [] step2 (SymConfig.mk 21 tape1 (p + 1)) SymSteps.nil ?_ ?_ ?_
          · rfl
          · simp [step2, tape1]
          · change step2.result ∈ VerifierSym.transition (21, tape1 (p + 1))
            simp [tape1]
            have hk2 : (tape (p + 1)).1 = SymKind.boundary := by
              simpa using hbound
            exact (trans21_end (tape (p + 1)) (Or.inr (Or.inr hk2))).2 hk2
        refine ⟨[step1, step2], symStepConfig (symStepConfig (SymConfig.mk 21 tape p) step1.result) step2.result,
          SymSteps_trans VerifierSym.transition (SymConfig.mk 21 tape p) (SymConfig.mk 21 tape1 (p + 1))
            (symStepConfig (symStepConfig (SymConfig.mk 21 tape p) step1.result) step2.result)
            [step1] [step2] ?_ hstep2, ?_⟩
        · simpa [hcfg1] using hstep1
        · refine ⟨Or.inr rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · right
            simp [symStepConfig, step1, r1, step2, r2, Dir.toInt]
          · intro hb
            exact ⟨rfl, by simp [symStepConfig, step1, r1, step2, r2, Dir.toInt]⟩
          · intro h
            exfalso
            rcases h with hsel | hnosel
            · have hk : (tape (p + 1)).1 = SymKind.boundary := by simpa using hbound
              have hsel' : (tape (p + 1)).1 = SymKind.sel := by simpa using hsel
              rw [hsel'] at hk
              cases hk
            · have hk : (tape (p + 1)).1 = SymKind.boundary := by simpa using hbound
              have hnosel' : (tape (p + 1)).1 = SymKind.nosel := by simpa using hnosel
              rw [hnosel'] at hk
              cases hk
          · intro i hi
            have hi0 : i = 0 := by
              simp at hi
              omega
            subst i
            simp [List.getElem_replicate, symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt]
          · right; right
            simp [symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt]
            simpa using hbound
          · intro j hj
            have hj1 : j ≠ p + 1 := by omega
            have hj2 : j ≠ p := by omega
            simp [symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt, hj1, hj2]
          · simp [symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt]
          · intro j hj
            have hj1 : j ≠ p + 1 := by omega
            have hj2 : j ≠ p := by omega
            simp [symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt, hj1, hj2]
  | succ n ih =>
      -- 先清 p 处（选择位），再递归清 p+1 起的 n+1 个
      let r1 : SymTransResult := { nextState := 21, writeSym := Sym.data0, moveDir := Dir.R }
      let step1 : SymStep := { fromState := 21, readSym := tape p, result := r1 }
      have hstep1 : SymSteps VerifierSym.transition (SymConfig.mk 21 tape p) [step1]
          (symStepConfig (SymConfig.mk 21 tape p) step1.result) := by
        refine SymSteps.cons [] step1 (SymConfig.mk 21 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · change step1.result ∈ VerifierSym.transition (21, tape p)
          exact trans21_data (tape p) (by
            have h1 : (tape p).1 = SymKind.data0 ∨ (tape p).1 = SymKind.data1 ∨ (tape p).1 = SymKind.consumed := by
              rcases hstart with h | h | h <;> simp [h, Sym.data0, Sym.data1, Sym.consumed]
            exact h1)
      let tape1 : ℤ → Sym := fun i => if i = p then Sym.data0 else tape i
      have hcfg1 : symStepConfig (SymConfig.mk 21 tape p) step1.result = SymConfig.mk 21 tape1 (p + 1) := by
        simp [symStepConfig, SymConfig.mk, step1, r1, tape1, Dir.toInt]
      have hstart' : tape1 (p + 1) = Sym.data0 ∨ tape1 (p + 1) = Sym.data1 ∨ tape1 (p + 1) = Sym.consumed := by
        have hlt : p + 1 ≠ p := by omega
        simp [tape1, hlt]
        simpa using hdata 0 (by omega)
      have hdata' : ∀ i : ℕ, i < n → tape1 (p + 1 + 1 + (i : ℤ)) = Sym.data0 ∨
          tape1 (p + 1 + 1 + (i : ℤ)) = Sym.data1 ∨ tape1 (p + 1 + 1 + (i : ℤ)) = Sym.consumed := by
        intro i hi
        have h : tape (p + 1 + ((i + 1 : ℕ) : ℤ)) = Sym.data0 ∨
            tape (p + 1 + ((i + 1 : ℕ) : ℤ)) = Sym.data1 ∨ tape (p + 1 + ((i + 1 : ℕ) : ℤ)) = Sym.consumed :=
          hdata (i + 1) (by omega)
        have hpos : p + 1 + 1 + (i : ℤ) = p + 1 + ((i : ℤ) + 1) := by omega
        have hneq : p + 1 + ((i : ℤ) + 1) ≠ p := by omega
        rw [hpos]
        simp [tape1, hneq]
        simpa using h
      have hend' : tape1 (p + 1 + 1 + (n : ℤ)) = Sym.sel ∨ tape1 (p + 1 + 1 + (n : ℤ)) = Sym.nosel ∨
          (tape1 (p + 1 + 1 + (n : ℤ))).1 = SymKind.boundary := by
        have hpos : p + 1 + 1 + (n : ℤ) = p + 1 + ((n : ℤ) + 1) := by omega
        have hneq : p + 1 + ((n : ℤ) + 1) ≠ p := by omega
        rw [hpos]
        simp [tape1, hneq]
        simpa using hend
      rcases ih (p + 1) tape1 hstart' hdata' hend' with ⟨π, cfg', hπ, hs, hhead, hb22, hsel51, hta, hbnd, hleft, hkeep, hright⟩
      refine ⟨[step1] ++ π, cfg', SymSteps_trans VerifierSym.transition (SymConfig.mk 21 tape p)
        (SymConfig.mk 21 tape1 (p + 1)) cfg' [step1] π ?_ hπ, ?_⟩
      · simpa [hcfg1] using hstep1
      · refine ⟨hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rcases hhead with hh | hh
          · left
            rw [hh]
            omega
          · right
            rw [hh]
            omega
        · intro hb
          have hb2 : (tape1 ((p + 1) + 1 + ↑n)).1 = SymKind.boundary := by
            rw [show (p + 1) + 1 + ↑n = p + 1 + (↑n + 1) from by omega]
            have hne : p + 1 + (↑n + 1) ≠ p := by omega
            simp [tape1, hne]
            rwa [show p + 1 + (↑n + 1) = p + 1 + ↑(n + 1) from by omega]
          simpa [show (p + 1) + 1 + ↑n = p + 1 + ↑(n + 1) from by omega] using hb22 hb2
        · intro h
          have h2 : (tape1 ((p + 1) + 1 + ↑n)).1 = SymKind.sel ∨ (tape1 ((p + 1) + 1 + ↑n)).1 = SymKind.nosel := by
            rw [show (p + 1) + 1 + ↑n = p + 1 + (↑n + 1) from by omega]
            have hne : p + 1 + (↑n + 1) ≠ p := by omega
            simp [tape1, hne]
            rwa [show p + 1 + (↑n + 1) = p + 1 + ↑(n + 1) from by omega]
          simpa [show p + 1 + ↑n = p + (↑n + 1) from by omega] using hsel51 h2
        · -- tapeAgrees：p 处 data0 而 p+1 起的由 hta
          intro i hi
          by_cases hi0 : i = 0
          · subst i
            have h := hleft p (by omega)
            simpa [tape1] using h
          · have hi' : i - 1 < (List.replicate (n + 1) Sym.data0).length := by
              simp at hi ⊢
              omega
            have h := hta (i - 1) hi'
            -- 组装：replicate (n+2) 的第 i 格 = data0
            have hi1 : 1 ≤ i := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hi0)
            have hnat : (i - 1 : ℕ) + 1 = i := Nat.sub_add_cancel hi1
            have hsub : ((i - 1 : ℕ) : ℤ) + 1 = (i : ℤ) := by
              rw [← hnat]
              simp
            have hpos : p + 1 + ((i - 1 : ℕ) : ℤ) = p + (i : ℤ) := by
              calc
                p + 1 + ((i - 1 : ℕ) : ℤ) = p + (((i - 1 : ℕ) : ℤ) + 1) := by ring
                _ = p + (i : ℤ) := by rw [hsub]
            simp [List.getElem_replicate]
            rw [← hpos]
            simpa using h
        · rw [show p + 1 + ↑(n + 1) = p + 1 + 1 + ↑n from by omega]
          exact hbnd
        · intro j hj
          have hj1 : j ≠ p := by omega
          simpa [tape1, hj1] using hleft j (by omega)
        · rw [show p + 1 + ↑(n + 1) = p + 1 + 1 + ↑n from by omega]
          simpa [tape1, show p + 1 + 1 + (n : ℤ) ≠ p from by omega] using hkeep
        · intro i hi
          have hi' : p + 1 + 1 + (n : ℤ) < i := by omega
          have h := hright i hi'
          simpa [tape1, show i ≠ p from by omega] using h

/-- 清一个 nosel 元素：从状态 4、带头 nosel 位置 p_e、元素值位 ebits（在 p_e+1 起）
    出发：4 置选择位 0 进占位扩展（20 读左边界 #₀ → 21），21 扫清数据，
    遇 sel/nosel → 51（还有下一个元素），遇 boundary → 22（#₁ → 判定）。 -/
lemma clear_element_correct (ebits : List Bool) (p_e : ℤ) (tape : ℤ → Sym)
    (hsel : tape p_e = Sym.nosel)
    (hbound₀ : tape (p_e - 1) = Sym.boundary)
    (helem : tapeAgrees tape (p_e + 1) (bitsToSym ebits))
    (hend : tape (p_e + 1 + (ebits.length : ℤ)) = Sym.sel ∨
        tape (p_e + 1 + (ebits.length : ℤ)) = Sym.nosel ∨
        (tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) π cfg' ∧
      (cfg'.state = 51 ∨ cfg'.state = 22) ∧
      (cfg'.headPos = p_e + (ebits.length : ℤ) ∨ cfg'.headPos = p_e + 1 + (ebits.length : ℤ)) ∧
      ((tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.boundary → cfg'.state = 22 ∧ cfg'.headPos = p_e + 1 + (ebits.length : ℤ)) ∧
      ((tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.sel ∨ (tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.nosel →
        cfg'.state = 51 ∧ cfg'.headPos = p_e + (ebits.length : ℤ)) ∧
      tapeAgrees cfg'.tape (p_e + 1) (List.replicate ebits.length Sym.data0) ∧
      (cfg'.tape (p_e + 1 + (ebits.length : ℤ)) = Sym.sel ∨
        cfg'.tape (p_e + 1 + (ebits.length : ℤ)) = Sym.nosel ∨
        (cfg'.tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.boundary) ∧
      cfg'.tape (p_e - 1) = Sym.data0 ∧
      cfg'.tape p_e = Sym.data0 ∧
      (∀ i : ℤ, i < p_e - 1 → cfg'.tape i = tape i) ∧
      (cfg'.tape (p_e + 1 + (ebits.length : ℤ)) = tape (p_e + 1 + (ebits.length : ℤ))) ∧
      (∀ i : ℤ, p_e + 1 + (ebits.length : ℤ) < i → cfg'.tape i = tape i) := by
  let r1 : SymTransResult := { nextState := 20, writeSym := Sym.data0, moveDir := Dir.L }
  let step1 : SymStep := { fromState := 4, readSym := Sym.nosel, result := r1 }
  have hstep1 : SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) [step1]
      (symStepConfig (SymConfig.mk 4 tape p_e) step1.result) := by
    refine SymSteps.cons [] step1 (SymConfig.mk 4 tape p_e) SymSteps.nil ?_ ?_ ?_
    · rfl
    · change Sym.nosel = tape p_e
      rw [hsel]
    · change step1.result ∈ VerifierSym.transition (4, tape p_e)
      rw [hsel]
      decide
  let tape1 : ℤ → Sym := fun i => if i = p_e then Sym.data0 else tape i
  have hcfg1 : symStepConfig (SymConfig.mk 4 tape p_e) step1.result =
      SymConfig.mk 20 tape1 (p_e - 1) := by
    simp [symStepConfig, SymConfig.mk, step1, r1, tape1, Dir.toInt]
    omega
  let r2 : SymTransResult := { nextState := 21, writeSym := Sym.data0, moveDir := Dir.R }
  let step2 : SymStep := { fromState := 20, readSym := Sym.boundary, result := r2 }
  have hstep2 : SymSteps VerifierSym.transition (SymConfig.mk 20 tape1 (p_e - 1)) [step2]
      (symStepConfig (SymConfig.mk 20 tape1 (p_e - 1)) step2.result) := by
    refine SymSteps.cons [] step2 (SymConfig.mk 20 tape1 (p_e - 1)) SymSteps.nil ?_ ?_ ?_
    · rfl
    · change Sym.boundary = tape1 (p_e - 1)
      have hne : p_e - 1 ≠ p_e := by omega
      simp [tape1, hne]
      exact hbound₀.symm
    · change step2.result ∈ VerifierSym.transition (20, tape1 (p_e - 1))
      have hne : p_e - 1 ≠ p_e := by omega
      simp [tape1, hne]
      rw [hbound₀]
      decide
  let tape2 : ℤ → Sym := fun i => if i = p_e - 1 then Sym.data0 else tape1 i
  have hcfg2 : symStepConfig (SymConfig.mk 20 tape1 (p_e - 1)) step2.result =
      SymConfig.mk 21 tape2 p_e := by
    simp [symStepConfig, SymConfig.mk, step2, r2, tape2, tape1, Dir.toInt]
  have hstart2 : tape2 p_e = Sym.data0 ∨ tape2 p_e = Sym.data1 ∨ tape2 p_e = Sym.consumed := by
    have hne : p_e ≠ p_e - 1 := by omega
    simp [tape2, tape1, hne]
  have hdata2 : ∀ i : ℕ, i < ebits.length → tape2 (p_e + 1 + (i : ℤ)) = Sym.data0 ∨
      tape2 (p_e + 1 + (i : ℤ)) = Sym.data1 ∨ tape2 (p_e + 1 + (i : ℤ)) = Sym.consumed := by
    intro i hi
    have hne1 : p_e + 1 + (i : ℤ) ≠ p_e := by omega
    have hne2 : p_e + 1 + (i : ℤ) ≠ p_e - 1 := by omega
    simp [tape2, tape1, hne1, hne2]
    have h := helem i (by simpa [bitsToSym] using hi)
    by_cases hb : ebits[i]
    · right; left
      simpa [bitsToSym, hb] using h
    · left
      simpa [bitsToSym, hb] using h
  have hend2 : tape2 (p_e + 1 + (ebits.length : ℤ)) = Sym.sel ∨
      tape2 (p_e + 1 + (ebits.length : ℤ)) = Sym.nosel ∨
      (tape2 (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.boundary := by
    have hne1 : p_e + 1 + (ebits.length : ℤ) ≠ p_e := by omega
    have hne2 : p_e + 1 + (ebits.length : ℤ) ≠ p_e - 1 := by omega
    simp [tape2, tape1, hne1, hne2]
    exact hend
  rcases scanClear21 ebits.length p_e tape2 hstart2 hdata2 hend2 with ⟨π, cfg', hπ, hs, hhead, hb22, hsel51, hta, hbnd, hleft, hkeep, hright⟩
  have hta' : tapeAgrees cfg'.tape (p_e + 1) (List.replicate ebits.length Sym.data0) := by
    intro i hi
    have h := hta (i + 1) (by
      simpa using hi)
    have hpos : p_e + 1 + (i : ℤ) = p_e + ((i + 1 : ℕ) : ℤ) := by
      rw [show ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 by norm_num]
      ring
    rw [hpos]
    exact h
  have hmark : cfg'.tape p_e = Sym.data0 := by
    have h := hta 0 (by simp)
    simpa using h
  refine ⟨[step1, step2] ++ π, cfg', ?_, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hstep1' : SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) [step1]
        (SymConfig.mk 20 tape1 (p_e - 1)) := by
      simpa [hcfg1] using hstep1
    have hstep2' : SymSteps VerifierSym.transition (SymConfig.mk 20 tape1 (p_e - 1)) [step2]
        (SymConfig.mk 21 tape2 p_e) := by
      simpa [hcfg2] using hstep2
    have h12 : SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) [step1, step2]
        (SymConfig.mk 21 tape2 p_e) := by
      exact SymSteps_trans VerifierSym.transition (SymConfig.mk 4 tape p_e) (SymConfig.mk 20 tape1 (p_e - 1))
        (SymConfig.mk 21 tape2 p_e) [step1] [step2] hstep1' hstep2'
    exact SymSteps_trans VerifierSym.transition (SymConfig.mk 4 tape p_e) (SymConfig.mk 21 tape2 p_e) cfg'
      [step1, step2] π h12 hπ
  · exact hhead
  · -- boundary 右端 → 22（由 scanClear21 的 hb22，把 tape2 还原为 tape）
    intro hb
    have hb2 : (tape2 (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.boundary := by
      rw [show tape2 (p_e + 1 + (ebits.length : ℤ)) = tape (p_e + 1 + (ebits.length : ℤ)) from by
        simp [tape2, tape1,
          show p_e + 1 + (ebits.length : ℤ) ≠ p_e - 1 from by omega,
          show p_e + 1 + (ebits.length : ℤ) ≠ p_e from by omega]]
      exact hb
    exact hb22 hb2
  · -- sel/nosel 右端 → 51（由 scanClear21 的 hsel51，把 tape2 还原为 tape）
    intro h
    have hb2' : (tape2 (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.sel ∨
        (tape2 (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.nosel := by
      rw [show tape2 (p_e + 1 + (ebits.length : ℤ)) = tape (p_e + 1 + (ebits.length : ℤ)) from by
        simp [tape2, tape1,
          show p_e + 1 + (ebits.length : ℤ) ≠ p_e - 1 from by omega,
          show p_e + 1 + (ebits.length : ℤ) ≠ p_e from by omega]]
      exact h
    exact hsel51 hb2'
  · exact hta'
  · exact hbnd
  · -- p_e - 1 位置 = data0（状态 20 读 #₀ 时写入）
    have h := hleft (p_e - 1) (by omega)
    rw [h]
    simp [tape2, tape1]
  · exact hmark
  · intro i hi
    have hi' : i < p_e := by omega
    have h := hleft i hi'
    have hne1 : i ≠ p_e - 1 := by omega
    have hne2 : i ≠ p_e := by omega
    rw [h]
    simp [tape2, tape1, hne1, hne2]
  · rw [hkeep]
    simp [tape2, tape1,
      show p_e + 1 + (ebits.length : ℤ) ≠ p_e from by omega,
      show p_e + 1 + (ebits.length : ℤ) ≠ p_e - 1 from by omega]
  · intro i hi
    have h := hright i hi
    have hne1 : i ≠ p_e - 1 := by omega
    have hne2 : i ≠ p_e := by omega
    rw [h]
    simp [tape2, tape1, hne1, hne2]

end Mp
