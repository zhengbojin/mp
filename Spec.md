# Spec.md — P vs NP 形式化验证项目软件规格说明书

- **定位**：本文档是项目各项事项的**约定总纲**（现行版）。凡出现歧义、冲突或需要裁决之处，一律以本文档为准；文档未涉及的，另行补充约定。
- **体例**：节号与条目编号为稳定标识（与代码注释中的引用保持一致）；行号为易失信息，一律以**符号名搜索**为准。

---

## 1. 软件的目的与当前状态

在 **Lean 4**（v4.32.x，lake 工程 `D:\lean4\mp`）中，对 **P ≠ NP 的证明** 做**完全形式化验证**：

- 把证明的全部推理链（从基本定义、编码、转移表，到主定理）写成 Lean 的 `def`/`lemma`/`theorem`；
- **已达成终态**：**0 声明公理 / 0 缺口 / 0 error**，`lake build` 全链通过（8708 jobs）；
- 主链：`subsetSum_in_NP_F`（`Mp/SubsetSumInNP.lean`）与分离结论 `P_F_neq_NP_F` / `P_cb_neq_NP_cb` / `P_neq_NP_with_barriers`（`Mp/FinalProof.lean`）均已组装；`subsetSumNTM2_canonical_clauseC` 已定理化（`Mp/SubsetSumVerifierQ10.lean`）。
- **符号层（ATM/NTM2）分离结论 `P_sym0 ≠ NP_sym0`（集合论意义，对齐域）已组装**（`Mp/ATMAssembly.lean`；完整解释见 §7.7、约定 31）。

**当前状态快照**：

| 项 | 状态 |
|---|---|
| 全库构建 | 绿（`lake build`：8708 jobs 成功；0 错误 / 0 缺口） |
| 声明公理 | **0**（全库检索：无公理声明） |
| 缺口面 | sorry / admit = 0 |
| 公理足迹 | {`propext`, `Classical.choice`, `Quot.sound`} + 既有 `native_decide` 继承足迹（标准面） |
| ③线 C3 步数界 | v5 语义链全链落库：`phase_decomp` / `main_le_quad`（≤ 16·(E+1)²）/ `main_sym`、`main_f4`（`∃K, ≤ K·(m+1)·(|x|+1)²`）——`Mp/SubsetSumVerifierReverse15.lean` |
| 存量辅件 | R11 (S2′) 件、R14 转向件 10 件（非主链素材） |

---

## 2. P vs NP 证明的简要介绍

> 本证明基于用户的 **CBTM / IVM / 数计一体** 框架，要点如下：

1. **CBTM**（Choice-Based Turing Machine）：一台图灵机，其磁带上元素区的分支符号 α/β 触发**真实双分支**（写 sel 或写 nosel）。
2. **IVM**（虚部机制）：每个分支方向对应一个"虚部"代数对象 √p_i。不激活路径（T^Im=0）停留在基域 ℚ；激活路径（T^Im=1）进入扩域 ℚ(√p_i)。两者之差 √p_i ∉ ℚ 即"不可公度性的分离"。
3. **本质维度 κ**：度量单位是**素数平方根对的个数**（每对 {√p_i, −√p_i} 中 −√p_i = −1·√p_i 线性相关，一对贡献一个独立维度）。
4. **P = NP 反证**：判定 P = NP 的机器是**本质 0 维**的（省分叉 = 省维度，恒在 ℚ）；而 NP 完备问题（如子集和）的验证需要 **Ω(n) 维**的分叉。维度 0 与 Ω(n) 的矛盾推出 P ≠ NP。
5. **三层堵死"聪明算法"**：信息论层 + 语义资源层 + 代数独立性层。BGS 相对化定理 = 语义外包（oracle），不构成障碍。
6. **完备 witness**：sel/nosel 序列（非确定路径的实际写入，可由 `scanSelPrefix` 从磁带读回）。
7. **符号层扩展（经典 P≠NP 的集合论意义版本）**：在符号输入图灵机（ATM）与 NTM2 上定义符号层复杂度类——P 类以 **CBTM0 承载**（「DTM≅CBTM0 ⇒ κ=0 传递」的类层形式）、NP 类以 **NTM2 承载**，判定域 = 符号对齐串（对齐域口径）。子集和语言满足 ∈ NP 类而 ∉ P 类，故两类不等：**`P_sym0 ≠ NP_sym0` —— 集合论意义（语言集合不等），对齐域**；该结论与 F 层 `P_F ≠ NP_F` 是**同一定理的两种表述**。诚实边界：语义基础是 CBTM/IVM 框架的内建语义（虚部=分支、不可公度分离）；脱离框架的纯经典框架无法排除假分支（语义超越语法）。见 §7.7。

---

## 3. 形式化验证的概念性模块（从证明到项目的过渡）

| 概念模块 | 说明 | 对应项目实体 |
|---|---|---|
| C1 符号与编码 | Sym = SymKind × Bool（4F4 语义），符号层编码（target/元素/物理/逻辑） | `Sym`、`SymKind`、`encodeBitsSym`、`encodeElementsSym`、`encodeElementsSymWithSel`、`encodeElementsSymChosen` |
| C2 转移表 | 完整转移函数（33 个合法状态集合，表外归 101） | `VerifierSym.transition`、`legalStates` |
| C3 路径与步进 | 非确定路径 π、步进配置、SymSteps | `SymConfig`、`SymStep`、`SymSteps`、`symStepConfig` |
| C4 分支阶段 | 状态 2 读 α 双分支写 sel/nosel（唯一非确定点） | 表级 `(2, alpha-)` 唯一双后继行；`branch_phase*`（CoreA） |
| C5 逐元素处理 | 状态 4→4/22 逐元素（选中：轮减法+清尾；未选：直进；随后占位扩展） | **v5 段件**：`segS0`/`segS1`/`segSrNosel`/`segS3`（R12）、`segSrSel`/`segSrFold`（R13）；数学语义 `subAllSelected`（CoreA） |
| C6 语言正确性（完备/可靠） | 接受路径读回 witness；语言 = 子集和 | `symVerifier_correct`（Reverse3）；Reverse 系相位件 |
| C7 NP 归约与主定理 | 子集和 ∈ NP、P ≠ NP 组装 | `SubsetSumInNP`、`Q10`、`FinalProof` |
| C8 CBTM/IVM 数学层 | 虚部、维度、独立性的数学形式化 | `CBTM*.lean`、`IVM`、`EssentialDimension`、`PrimeSqrtLinearIndep`、`LowerBound` |

---

## 4. 形式化验证的具体模块

> 全库构建绿（0 缺口）。行号为易失信息，一律以**符号名搜索**为准。本节列主干；`Mp/` 共 55 个模块。

### 4.1 数学层与主定理
- `Mp/Basic.lean`：F4（位对）、NTM2（二分支 NTM）等基础定义。
- `Mp/CBTM.lean`：CBTM 定义与 4F4 编译（`symTo4F4`/`symOf4F4`/`flat4F4`/`encodeInstanceF4`/`transition4`）；`NTM2.Canonical` 定义；同构结构 `StructIsoNTM2CBTM` 与存在定理 `exists_CBTM_iso_NTM2`。
- `Mp/IVM.lean`：`CBTM.isPolynomialTime` 等；`Mp/EssentialDimension.lean` / `Mp/PrimeSqrtLinearIndep.lean` / `Mp/LowerBound.lean`：κ、√p 独立性与 `SubsetSumInstance`。
- `Mp/Barriers.lean` / `Mp/ClassicalFramework.lean`：oracle 不变性（相对化/代数化在框架内的处理）。
- `Mp/SubsetSumReal.lean`：语言层（`IsP_F`/`IsNP_F`、`isPolynomialTimeAligned`、`subsetSum_kappa_lower_bound`、`subsetSum_not_in_P_F'`、`flat4F4_length`）。
- `Mp/SubsetSumInNP.lean`：`subsetSum_in_NP_F`（定理）。
- `Mp/FinalProof.lean`：`P_F_neq_NP_F`、`P_cb_neq_NP_cb`、`P_neq_NP_with_barriers`。

### 4.2 验证器 Sym 层（机器本体）
- `Mp/SubsetSumVerifierCore.lean`：`Sym`（= `SymKind × Bool`）、8 kind、编码（`encodeBitsSym`/`encodeElementsSym`/`encodeInstanceSym`）、`VerifierSym.transition`（33 合法态，表外归 101）、`SymConfig`/`SymStep`/`SymSteps`。
- `Mp/SubsetSumVerifierCore1.lean`：段构造（`scanRight*`/`scanLeftKeepPos`/`format_sweep*` 等扫描段及其正确性）。
- `Mp/SubsetSumVerifierCore2.lean`：主循环数学层（`main_loop_correct`、`subAllSelected` 等）。
- `Mp/SubsetSumVerifierCoreA.lean`：选择语义（`encodeElementsSymWithSel`/`Chosen`、`scanSelPrefix`、`branch_phase*`）。
- `Mp/SubsetSumVerifierL3a.lean`：块级 fork 分类（`l3a_goodblock_read_im_classify`、`l3a_Lstep_prev_not_branch` 等）。

### 4.3 4F4 编译层与路径桥
- `Mp/SubsetSumVerifierCBTM.lean` / `CBTM2–6.lean`：12 步展开（`expand_sym_step`）、块投影（`project_block`/`project_path(_gen)`）、相位纪律（`path_phase_at`）、接受路径块分解（`accept_path_is_good_block_path`）。
- `Mp/A2Bridge.lean`：NTM2↔CBTM 路径桥（`iso_initial_corresp`/`iso_step_forward`/`iso_path_forward`/`iso_path_backward`、`first_accept_step_split`、`tapeAccepts_truncate`、`ntm2_path_mirror`）。
- `Mp/SubsetSumCompile.lean`：编译层路径事实（`accept_path_no_trap`、`symSteps_writeSym_nonbranch`、`symAccepts_tail_iff`、`toCBTM_subsetSumNTM2_eq` 等）。

### 4.4 位置界与步数桥
- `Mp/SubsetSumVerifierPosBound.lean` + `PosBound1–5.lean`：位置界族（`a2p_*`；`a2_cbtm_accept_path_prefix_bound`、`a2p_mainloop_no_neg` 等）。
- `Mp/SubsetSumVerifierStepBound.lean`：转向 / 扫掠记账与步数界族（`symTurnCount*`、`symSteps_length_le_of_*`、单向扫掠长度界）。
- `Mp/A1StepBoundBridge.lean`：T15 桥（`a1_sym_path_length_bound`、`a1_cbtm_path_length_bound(_of_accept/_canonical)`、`A1CanonicalPathFacts`）。

### 4.5 相位段件与 v5 主链
- `Mp/SubsetSumVerifierReverse.lean` / `Reverse2–11.lean`：相位段件与基座；R11 含转向 / δ-19 系（只读基座）。
- `Mp/SubsetSumVerifierReverse12.lean`：**阶段绿件**——`segS0`（α替换，≤ L+3）、`segS1`（格式检验，≤ 2L）、`segSrNosel`（未选支，≤ n+5）、`segS3`（判定，≤ n+2）。
- `Mp/SubsetSumVerifierReverse13.lean`：**复杂性单元**——值论（`regValA` 系）、轮（`round_to13`/`round_d0`/`round_chain`）、出口 / 清尾 / 扩展（`exit13`/`cleanup_unit`/`expand_unit`）、末轮链 `last_chain`、段总装 `segSrSel`、元素折叠 `segSrFold`、相位别名（`alpha_phase`/`format_phase`/`judge_phase`/`round_nosel`）。
- `Mp/SubsetSumVerifierReverse14.lean`：**素材库**——表级组 11 件 / 走带族 15 件 / 转向件 10 件。
- `Mp/SubsetSumVerifierReverse15.lean`：**总装层**——`judge_after_fold`、`fold_pre_of_worst`（含 `WorstCase` 最坏族谓词）、`phase_decomp`、`main_le_quad`、`main_sym`、`main_f4`；C3 供给链：`fold_entry_of_accept`、`sym_run_le_1632_fold` 与十供给件。
- **文件纪律**：R11/R12 为只读基座；R13/R14/R15 为主链落点；并发构建经锁协议串行（见 §6.14）。

### 4.6 注入与主定理装配
- `Mp/SubsetSumVerifierQ10.lean`：`subsetSumNTM2_canonical` 装配——(a) 位置界、(b) `ntm2_canonical_clause2`（标记读前缀互异）、(c) = `subsetSumNTM2_canonical_clauseC`（**定理**；由 `subsetSumNTM2_clauseC_wiring` 装配：`hsup := wf_of_accept + hconf_of_accept + sym_run_le_1632_fold`；消费点零改动）。
- `Mp/SubsetSumVerifierT16.lean`：条款⑤（尾缀无关）`subsetSumNTM2_hrel2`（.1 原⟹尾缀版 / .2 尾缀版⟹原）。

---

## 5. 对照表（概念模块 ↔ 证明概念 ↔ 具体模块）

| 概念性模块 | P vs NP 证明中的概念 | 具体模块（定义/引理/定理） |
|---|---|---|
| C1 编码 | 数计一体：语义内建在符号上（虚部 = 分支） | `Sym`、`encodeElementsSymWithSel`（物理，含 sel/nosel 选择符）、`encodeElementsSymChosen`（逻辑，仅选中位串） |
| C2 转移表 | 非确定转移：α 双分支 | `VerifierSym.transition` 的 `\| 2, (alpha,_) => {sel, nosel}` 行、`legalStates` |
| C3 路径 | 见证 = sel/nosel 序列；路径标记 Π∈{α,β}^m | `SymSteps`、`scanSelPrefix`（读回）、`encodeElementsSymWithSel_cell`（按实际写入逐格） |
| C4 分支阶段 | IVM 分叉：激活/不激活两路径 | `branch_phase`、`branch_phase_correct`、`branch_with_sel` |
| C5 逐元素处理 | 子集和的逐元素相减（语义资源层） | `segS0`/`segS1`/`segSrNosel`/`segS3` + `segSrSel`/`segSrFold`（v5 主链）；`subAllSelected` |
| C6 语言正确性 | 完备 witness 的读回 | `symVerifier_correct`（Reverse3）；Reverse 系相位件 |
| C7 主定理 | 维度 0 vs Ω(n) 矛盾 | `SubsetSumInNP`、`Q10`、`FinalProof` |
| C8 数学层 | 本质维度 κ、√p 独立性 | `EssentialDimension`、`PrimeSqrtLinearIndep`、`LowerBound` |

**见证对应（核心约定）**：CBTM = 路径标记 Π∈{α,β}^m；IVM = 激活向量 a∈{0,1}^m；语义展开 Φ : α↦1, β↦0 是双射。

---

## 6. 具体事项约定

1. **可变长原生编码**：元素的位串 = `Nat.digits 2 v` 的可变长（LSB 左，不补零）；target 同理。不使用固定位宽。
2. **target 不得为空**：若 target = 0 则编码为空，格式检查失败；证明中加前提 `htarget : 0 < inst.target`。
3. **元素不得为 0**：加前提 `hpos : ∀ v ∈ inst.elements, 0 < v`（0 元素编码为空被格式检查拒绝）。
4. **nosel 计入长度**：物理编码每块长度 = 1 标记 + native，与标记是 sel 还是 nosel 无关；长度对齐不许假设"全 sel"。
5. **物理/逻辑编码分离**：`encodeElementsSymWithSel`（物理磁带，含选择符，供 tapeAgrees/scan2 校验）与 `encodeElementsSymChosen`（逻辑选中，仅 sel=true 的 native 拼接，供子集和数学验证）不得混用；长度与位置证明前先区分两类长度。
6. **NTM 非确定语义**：α/β 格写 sel 或 nosel 是**真实双分支**（转移表 `{sel, nosel}` 两条），析取不可单值化；`if` 不能模拟非确定选择。
7. **选择从磁带读回**：`scanSelPrefix` 从块头格的实际写入读回选择（写 sel = true，否则 false）；读回仅对格式合法磁带有意义（块头必为 sel/nosel）。
8. **33 状态集合**：`legalStates` 手动列出 33 个合法状态（0,1,2,3,4,5,8,9,10,11,12,13,14,20,21,22,23,24,26,27,28,29,38,51,76,77,81,84,85,86,87,100,101），凡不在此集合的状态一律归 101 停机。
9. **状态转移表一律不动**：转移表（`VerifierSym.transition` 的 match 臂）是既定规格，修改须用户明示。
10. **转移表引理的证明模式**：对 transition 的证明用「显式 `if_pos/if_neg (by decide : q ∈ legalStates)` 一步归约 + **kernel `decide`** 封闭枚举」，禁止裸 `simp [VerifierSym.transition]` 展开（会 isDefEq 超时/爆栈）。**新件不使用 `native_decide`**（会生成逐案例公理，破坏 0 公理标准；确需先报告）；既有 `native_decide` 账仅作**继承足迹**（见 §8.6 注）。
12. **语义优先**：顽固错误先分析本质原因（结构性根源：绕路旧编码/残留/依赖消去/归约前提），经用户澄清语义后再修；禁止症状级补丁。
13. **版本命名**：论文/文档文件命名 `<主题>.<语言>.<大>.<小>`；修正递增小版本另存新文件。
14. **编译、验证与提交口径**：单文件 `lake env lean Mp/<file>.lean`；全链 `lake build`；LF 换行；**绿灯标准 = EXIT=0 / 0 error / 0 缺口**（warning 现存项登记后统一处理，暂不即修）；**单件绿才提交，提交留回滚点**；`git add <明确文件>`（**禁** `add -A`；**禁** `checkout`/`restore`/`stash`/`clean`）；写 `.lake` 的构建先经 `_build.lock.d` 锁协议（BUSY 则等待）；不编造证明。
15. **文件归属与并行**：用户明令「不要修改 X 文件」或并发改同一文件时，只列方案（根因 + 修法 + 风险表）等授权，不动手防冲突；文件纪律见 §4.5。
16. **大型引理分离**：大引理移入独立文件，减少编译时间。
20. **符号图灵机原则与 F4 分配**：P 与 NP 定义在符号图灵机（DTM）与符号非确定图灵机（NTM）之上，字母表 |Σ| ≥ 4 = 2 数据（data0/data1）+ 1 分隔（sep）+ 1 结束（boundary）——分隔与结束内建为符号本身（数计一体），4 为最小完备数。F4 = Bool×Bool：虚部位 = 结构标记（0 数据 / 1 结构）、实部位 = 数据值或结构类；位对分配（字母表 1-1 查表）：(0,0)=data0、(1,0)=data1、(0,1)=sep（分隔符/元素标记）、(1,1)=boundary（边界符/输入结束）。**m（mark）是独立维度**（Sym 第二分量，计数器标记，运行时写入 #₁ 等）——输入编码 m 恒 0，输入格 (0,1)→(alpha,m=0)、(1,1)→(boundary,m=0)。Sym→F4 的组编译 `[(r₁,0),(r₂,0),(r₃,0),(m,i₁)]`（m 落第 4 格实部）是内部实现细节，与字母表解读分属两层。**编译清除语义（信息论）**：符号被强制编译为 bit 序列时，分隔/边界/分支语义被清除——bit 串图灵机无法完成元素区分与边界识别（表示不足），故 P/NP 定义必须停留在符号层（|Σ| ≥ 4）。
21. **最高位校验（MSB）**：为保证 target 与候选元素的最高位恒为 1（二进制编码无前导零、元素非 0），格式检查的最高位读步为：`24 读 data1 → 29`（v>0 ✓，反向扫）、`24 读 data0 → 101`（最高位 0 = 元素 0 或前导 0，拒绝）；`29` 读 data0/data1 继续左扫、读 sel/nosel → 26（配对选择符）。`qFmtData` 常量 = 29。最高位恒为 data1：24/26/27 读 data0 → 101。
22. **NTM2 语法/语义悖论与 IVM 强制分离**：NTM2 的分叉形式上产生两条路径，但实质上（语义上）可能只是一条（转移结果语义重合）；NTM2 只有语法没有语义，无法区分真/假分叉——语义与语法冲突。IVM 强制语义分离：用相同的转移分支测试，IVM 将它转化为实部分支与虚部分支（不激活 T^Im=0 留 ℚ；激活 T^Im=1 进 ℚ(√p_i)；差 √p_i ∉ ℚ 不可公度）——相同的分支变成绝对不同的分支，悖论被显式化。无悖论条件：IVM 中分支路径必须必然不同（语义差异由 √p_i 的代数独立结构确定，非武断指定）。
23. **ATM（算法 TM）：可变输入内建**：在 DTM 基础上定义算法 TM（ATM），把输入格式从外部约定转为内建语法：
    - **动机**：经典 DTM 的「输入结束」是证明层的外部语义承诺（输入写在 [0,|w|)、其余 blank、假设不越界读），不是机器能力——固定长度或无边界标记的形式化下，机器无法区分「输入结束」与「带外」，连只读输入/遍历元素向量都做不到（「有些 DTM 根本不能作为算法考虑」的精确含义 = 无可变输入处理能力的内建基础）。ATM 使输入格式成为机器可读、可验证的语法——「语义内建（数计一体）」原则在输入层的应用。
    - **定义方向**：字母表恰含四类符号 {0, 1, sep, #}（2 数据 + 1 分隔 + 1 边界 = 处理列表输入的最小完备集，见约定 20）；输入 = 元素向量（非无结构位串），规范形式 `# e₁ sep e₂ ⋯ sep e_m #`（# 包裹起止）；元素 = 值 ≥ 1 的位串（无前导 0，合法性内建）。
    - **空白符语义拆分**：经典 blank 兼任「输入结束标记 + 带外填充」两职（语义混淆）——ATM 明确为：输入结束 = #。
    - **与验证器的一致性（已实现结构 = ATM 实例）**：三边界符 #ₗ@0/#₀/#₁@L-1 标记输入骨架；元素头 α = 分隔符（+ 虚部点）；格式检查段（24→29→26→27→38→28）即 ATM 的**输入骨架验证器**；`format_check_precise`/`symAccepts_implies_encodeInstanceSym` = ATM 骨架定理（接受 ⟹ 输入具 ATM 骨架——条款 4 的实质）。
     —当前 `Core:174` `def blank := data0 false`（全库多处引用：q12 IsOutside 类、P9 boundary 位置分类、F4 带外 zero 换算等依赖 data0-false）。
24. **任务执行透明性（禁止子 Agent 分派）**：不得使用子 Agent（subagent/delegate）方式分派任务——任务执行过程不透明、不可控；一切工作由主会话直接执行，用户可见每一步。
25. **输入符号串与计算符号串的对应与计数**：
    - **带结构**：输入纸带 = **单条 F4 带**（1 符号 1 格，F4 = Bool×Bool = 2bit/符号）；计算纸带 = **4 条 F4 带**；**4F4 = 4 带同位置的 4 个 F4 组合 = 计算符号**——"4F4 相当于是 4 带机"。输入 F4 与计算 4F4 之间是一一对应的关系（CBTM 符号版 = 使用 4 条 F4 带子）。
    - **符号计数**：按符号个数计数，**输入串的符号长度与计算纸带符号串的长度一致**（格↔符号换算：4F4 符号 = 4 个 F4 格；`flat4F4`：|flat4F4 wS| = 4·|wS|）。位置界的两种表述同一语义：enc 输入上 [0, 4|wS|]（F4 格）= [0, |wS|]（4F4 符号）。
    - **机器输入 ↔ 编码符号**：机器输入符号与验证器编码符号一一对应、**符号个数相等**；bit 宽不同——机器输入 2bit/符号（F4 位对，约定 20 查表），验证器编码 8bit/编码（Sym 的 4F4 组编译，symTo4F4：kindBits 3bit 布前 3 格实部 + 第 4 格 (m,i₁)——单 F4 格不承载完整 kind，组编码是内部实现细节）。
    - **逻辑映射（padding 规则，逻辑层）**：机器符号字母表 {0, 1, sep, #} ↔ Sym 输入 kind {data0, data1, alpha, boundary} 直接映射（encodeInstanceSym/encodeBitsSym 同款；0→data0、1→data1、sep→α、#→boundary）；输入 padding 在此逻辑层进行（pad 符号经映射成 Sym 后缀），F4 格层的填充 = flat4F4 组。
    - **界语义（Canonical ①）**：① 的位置界 = **每步 pos ∈ [0, |x|] 闭区间**（x = encodeInstanceF4 inst ++ g'，"不越输入"；验证器接受尾步 23 读 #ₗ → 100 R 步后 pos = |x| 是合法停留故取闭区间；非法输入上允许越界拒绝——见 CBTM.lean Canonical 注释）。g' ≠ [] 推广 = A-2：目标即此 [0, |x|]（非 ≤ 4|wS|——后者是 enc 输入的特例 |x| = 4L'）；带后缀输入上机器可合法活动于 g' 区（头 ≤ |x| 即合法）。**输入域**：g' = flat4F4 gS（gS : List Sym）——x = flat4F4 (encS ++ gS) 恒 4 对齐（撕裂块问题消除）；非 4F4 像的 F4 串不是输入，不在域内。
    - **越界不可能 = 定理地位**：越界假设均为错误假设，须以 Lean 定理确定——Lean 侧依据：q12 族（`Reverse6`/`Reverse7L3` 引理区）与 P6l/P6r/P9 位置引理族；合法输入域内的每前缀位置界由 ①线位置界族（`PosBound*`，§4.4）供给。
26. **输入语义 = 计算纸带 4F4（输入层）**：
    - **验证器是 4 带机**：输入符号（逻辑意义 = F4，2bit）在物理实现上**映射到计算带 4F4 符号串**（每计算符号 = 4F4 组，flat4F4 像）；机器（witness）的输入即此——**非 flat4F4 像的 F4 串不是这台机器的输入**（4 带机无"半符号"；"输入整体对齐"是输入语义而非外加限制）。
    - **缺项输入语义已失**（数计一体）：把完整编码"截断"再"补全"（补零/补 boundary/任意带外值）以分析其接受性，是用外部约定编造语义（语义 ≠ 语法 → 悖论）——此类分析是伪问题；缺项输入不接受（定义为假），不进入证明。
    - **ATM = 复杂度分析所需的万能输入规范**：2bit 符号字母表 {0,1,sep,#}（信息论：≥3 符号需 ≥2bit；分隔符/终止符在纯 bit 物理机上无法实现——编译清除语义，约定 20）；分隔（多参数）与终止（输入结束）语义内建于符号，输入格式机器可验证（格式检查 = 骨架验证器）。
    - **机器性质在输入域内断言**：接受性/语言/多项式界（`CBTM.isPolynomialTimeAligned`：∀x IsSymbolAligned → 界）只在 4F4 符号串输入上定义；条款 4（hrel）域化（IsSymbolAligned w 前提）；**Canonical ① 与全部 hwf 的合法输入域同步 = x = encodeInstanceF4 inst ++ flat4F4 gS（gS : List Sym）**——x = flat4F4 (encS ++ gS) 恒 4 对齐（撕裂块问题消除），A-2 = 此域上的位置界 [0, |x|]；"接受 ⟹ 具 enc 前缀"在域内成立（`iso_accepts_implies_encoding`/`symAccepts_implies_encodeInstanceSym`，任意符号输入）。
27. **③线 C3 长度界口径**：
    - **时间语义**：时间数的是**移动的格子数**（位移）；转向为辅助；但**定义层不动、界全部 O 形式、常数不载明**。
    - **条款形**：`∃K, π.length ≤ K·(标记读+1)·(|x|+1)² ∨ 拒绝尾`（K 任意、不载明）。
    - **最坏情形实例族（= 复杂度函数定义域）**：n 个元素、**元素位全 1、全部被选中、target = Σⱼ eⱼ**（单元素 = 退化点）；**target 长度不作独立参数**。依据两条全称单调：sel 块 = nosel 块 + L_j 轮 + 清尾（元素级严格更贵）；位 1 轮 = 位 0 轮 + 1 + 借位链（位级严格更贵）。
    - **计数口径（元素个数非常数）**：n（及派生 |sel|/m/回合数）不为常数；一切计数一律经 **n ≤ L**（L = |encS|）放宽消去；`m` 为自由松弛参数（`run_total_le` 仅用 `0 ≤ m`）。
    - **100 路径模式（表级验证）**：① α替换 → ② 格式检验 → ③ 逐元素（选中 ⇒ L_j 轮减法+清尾；未选 ⇒ `4→20` 直进；随后占位扩展 `20→21/51`）→ ④ 判定 `22→23→100`；「不符合模式 ⇒ 101」。
    - **现行装配链（v5，落件见 §8.6）**：`segS0 → segS1 → segSrFold → segS3` 四相位串联（`phase_decomp`）⇒ `main_le_quad` / `main_sym` / `main_f4`。
    - **存量辅件**：R14 转向件 10 件与表级素材（非主链，见 §8.6）。
28. **导入分层闸门**：`Mp/SubsetSumVerifierPosBound2.lean:3` 导入 `Mp.SubsetSumVerifierStepBound` ⇒ `a2p_*`（PosBound2/3/4/5）位于 `StepBound` **下游**，`StepBound` **不得反向导入**（成环）；相关论证须在 `StepBound` 内自证。
29. **判定域与时间语义、结论强度定位**：
    - **判定域**：`IsSymbolAligned w := ∃ wS, w = flat4F4 wS`（§6.26 的输入域约定在代码层的载体）。P_F/NP_F 的机器正确性与时间界**只在输入域内断言**：`IsP_F L := ∃ M, IsRestricted M ∧ isPolynomialTimeAligned M ∧ (∀ w, IsSymbolAligned w → (M.tapeAccepts w ↔ L w))`；`IsNP_F L` 同理（无 IsRestricted）。非对齐串上语言与机器均无约束（数计一体：4 带机无半符号，缺项输入语义已失）。
    - **两版多项式时间语义**：`CBTM.isPolynomialTime`（Mp.IVM，全输入 + 首达即止语义）与 `CBTM.isPolynomialTimeAligned`（Mp.SubsetSumReal，对齐输入限定版）。关系：`isPolynomialTime M → isPolynomialTimeAligned M`（引理 `isPolynomialTimeAligned_of_isPolynomialTime`）；反向不成立（对齐版不约束非对齐输入）。
    - **结论强度定位（不可误读）**：
      - **结论形态 = 集合论意义的语言类分离**：`P_F ≠ NP_F` 即「存在语言属于 NP_F 而不属于 P_F」（两类集合不等；见证 = 子集和：`subsetSum_in_NP_F` 与 `subsetSum_not_in_P_F'`）。在 **DTM ≅ CBTM0**（取实部 + 虚部全 0，即虚部=0 层）口径下，这就是**经典 P ≠ NP 的框架内形式**：经典（符号）确定机与 CBTM0 同构，P 类中的任何机器都在虚部=0 层运转。
      - **分离引擎（受限机侧）= 能力缺口**：受限字母表机器（`CBTM.IsRestricted`：字母表 ⊆ {F4.zero, F4.one}，`h_alphabet_im_false` 虚部全假；配合 CBTM 硬结构「读字母表外符号 ⇒ 转移为空」⇒ **无虚部标记读取能力**）⇒ 可达读全 im-false ⇒ **κ = 0**；而编码 `encodeInstanceF4` 含 im = true 标记格（每元素一个），子集和的任何正确机须读每个标记格 ⇒ **κ ≥ n**（`subsetSum_kappa_lower_bound`）⇒ 对撞 ⇒ **受限机类不含子集和**（该否定与时间界无关；证明未引用多项式前提 `_hpoly`）。
      - **一般确定性机的对照（经典 P 类的实质内容）**：**存在一般确定性机在指数时间内解出子集和**（枚举所有选择组合并逐一验证）——故对一般确定性机，「解不了」**只在多项式时间约束下成立**；「一般确定性机多项式时间不可解」（= 经典 P ≠ NP 的实质）**不在本工程已证范围**。相应地：**受限机类 ⊆ 一般确定性机类 ⇒ `P_sym0` ⊆ 经典 P 类 ⇒ `P_sym0 ≠ NP_sym0` 不蕴含经典 `P ≠ NP`**。
      - **多项式条件的地位**：在类定义层限定「考察哪一类」；在**受限机侧不承担证明负荷**（能力缺口），在**一般确定性机侧才是实质条件**（指数时间上界的存在 ⇒ 时间下界的论证必要且未证）。
      - **信息论前提（引约定 20）**：经典 P 类定义中的机器只读符号串——**sep/# 与数据不可区分**（结构身份为外部命名，可逆标签）；区分结构需要表示能力（|Σ| ≥ 4，最小完备）。故「经典 P 类」与符号层类的对比**必须经编码桥**，桥的合法性/信息损失即本结论「框架内」限定的技术内容。
      - **边界先验性（引约定 23）——违背信息论**：经典定义中「**输入在何处结束**」是**外部给定**的语义——机器语法不含此信息（δ 无「输入结束」符号/状态；blank 检测机制依赖「输入内不出现 blank」的隐含承诺），单看「纸带 + 无限比特流」则「输入在何处结束」**不可判定**。**该先验假设违背信息论**：输入边界是**非零信息量**（结束位置/长度），而纸带内容与机器语法均**不携带**它——经典定义以「w 由元语言给出 + 其余 blank」的方式**把该信息从外部注入**，等价于凭空获得语法所无的信息（信息无源产生），语义处于**不闭合**状态；多参数结构输入的外部承诺更多（元素边界、参数个数），不闭合程度随之加深。对照：ATM 以 `#` 符号**物理携带**边界信息（分隔/边界内建为可读符号，机器自检——骨架验证器），信息来源在语法内，数计一体。故编码桥除结构语义（上条）外还须论证**边界语义**的对应——二者共同构成本结论「框架内」限定的技术内容。
      - **κ 相异性是代数事实（非标签游戏）**：κ 的语义单位 = 素数平方根对（§2.3）；两路径的相异由素数平方根在 ℚ 上的线性独立承载（`primeSqrt_Q_linearIndependent`；`pathValue_separated`：激活模式不同 ⇒ 路径值不同）——可计算且对符号置换稳定，不可由约定逆转。
      - **同一结论的两种表述**：符号层 `P_sym0 ≠ NP_sym0`（§7.7、约定 31）与 `P_F ≠ NP_F` 是**同一定理**——`isP_sym0_iff_isP_F` 为定义级相等，`subsetSum_not_in_P_sym0` 即 `subsetSum_not_in_P_F`；两者是同一分离的两种命名（F 层 / 符号层），不是两种强度。
      - **诚实边界**：结论的语义基础是 CBTM/IVM 框架的内建语义（虚部 = 分支；不可公度性 √p_i ∉ ℚ 使两条路径在 IVM 中完全分开）。**脱离 CBTM 框架、仅在经典框架下无法证明**经典 P ≠ NP——NTM2 的分支可能是假分支（形式两分支、语义一分支），假分支不可排除（语义超越语法，约定 22）。故本结论必须在框架语义下成立，不能在纯经典框架内闭合。
    - **κ 下界的准确表述**：`subsetSum_kappa_lower_bound` 对**任何满足正确性假设的验证器 M** 成立（hcorrect 是前提），不是「对所有 M」。

30. **hsem 供给口径（终态零 → 运行步 → 初态）**：
    - **供给义务**：fold 入口处 `hsem : regVal tape ((p_e−2).toNat) = chosenVal elems sels`（= `hreg0eq`；消费件 `run_fold_judge`（R13A），下游 `judge_zero_region`/`run_judge_split`）。出口零（`hreg0`，末窗口索引）由**净值式与 hsem 代数直得**（`rw [hreg_f, hreg0eq, sub_self]`，无需格级转移）。
    - **终/初之别（核心口径）**：「100 接受 ⇒ target=0」是**全过程结束后（终态）**的必然条件；**初态 target ≠ 0**（= 目标值，被减数起点）。hsem 的取得必须显式经**运行步**折算——fold 净值会计：**终 = 初 − chosenVal**——**不得把终态条件当初始条件用**。
    - **免费域（仅两域）**：① **100 路径**（§6.27 模式）——该路径自身执行把「终态零 → 初值」折算带齐（构成性可得）；② **最坏案例**（§6.27 族）——**值层直接等式**：初值 = `val(target)` = `Σ val(元素)` = 选中和，无需运行步折返。
    - **一般接受路径不免费** ⇒ 需 α 语义层供给（见证 + 编码保值）或改道免费域。
    - **树锚**：`sym_state_eq100_of_accept`（A1StepBoundBridge）；`bitsValue_bitsOf`（Core）；`WorstCase`（R15）；T-Q1 七件（R15）。
    - **β 符号附记**：规范中 β 无分支语义、元素区读 β 即 101（§8 表行；Core:415）。

31. **符号层复杂度类与经典分离结论（P_sym0 ≠ NP_sym0）**：
    - **类承载**：符号层 P 类以 **CBTM0 承载**（`IsP_sym0` = 受限 CBTM（字母表 ⊆ {zero,one}）+ 对齐域多项式 + 对齐域正确性）——「DTM ≅ CBTM0 ⇒ κ=0 传递」的类层形式；符号层 NP 类以 **NTM2 承载**（`IsNP_sym0`）；判定域 = 符号对齐串（对齐域口径，与约定 29 同）。
    - **分离结论**：**`P_sym0 ≠ NP_sym0`**（集合论意义：两个语言类的集合不等）；见证语言 = 子集和（`subsetSumLanguageF4Real ∈ NP_sym0` 且 `∉ P_sym0`）。精确读法：**受限字母表机器类（多项式时间）≠ NTM2 类（多项式时间）**——P 侧证据为能力缺口（与时间界无关），且**弱于经典 P ≠ NP**（受限机类 ⊆ 一般确定性机类；信息论前提见约定 29）。**与 F 层 `P_F ≠ NP_F` 是同一定理的两种表述**（定义级相等；定位见约定 29、解释见 §7.7）。
    - **代码锚点**：`Mp/ATMAssembly.lean`（`IsP_sym0`/`IsNP_sym0`/`subsetSum_in_NP_sym0`/`subsetSum_not_in_P_sym0`/`P_sym0_neq_NP_sym0`）。
    - **完整解释、链条与诚实边界见 §7.7**。

---

## 7. 自动机模型规范（自动机理解）

> 本节把项目对自动机的理解固化为软件规范：机器族、输入格式、带外语义、语义内建原则。
> 代码实体与概念层的对应以本节为准；与既有约定冲突时，冲突处报用户裁决并登记。

### 7.1 机器族谱与语义分层

| 机器 | 角色 | 关键性质 | 代码实体 |
|---|---|---|---|
| DTM（经典符号图灵机） | P 侧基准 | 确定性；**输入边界外部化**（输入写在 [0,\|w\|)、其余 blank、不越界读是证明层假设，非机器能力） | 受限机（CBTM restricted / 经典形式化） |
| NTM2 | 二分支 NTM | 转移依赖位置 (q,s,i)；vbAt 由空白格转移基数派生；**只有语法没有语义**——分叉语义可能重合（NTM2 悖论，约定 22） | `Basic.lean` NTM2 |
| CBTM | 符号驱动分支机 | 虚部内建：读 im=true 恰 2 结果、写回虚部全 false；磁带语义接受；同构桥保持语言外延 | `CBTM.lean`、`A2Bridge` |
| Sym 验证器 | 语义层机器 | Sym = SymKind × Bool；33 合法状态（legalStates，以代码为准）；边界/分隔/数据符号齐全（符号层语义） | `SubsetSumVerifierCore` |
| ATM（算法 TM） | 概念层：可变输入内建 | 输入 = 边界符包裹的元素向量（约定 23）；骨架可机器验证 | （概念层；实例 = 验证器 + 格式检查段） |

**翻译链**：NTM2 `toCBTM` 恒等翻译 → CBTM；Sym → 4F4 组编译（`subsetSumCBTM` witness）；CBTM ≅ NTM2 结构同构（`StructIsoNTM2CBTM` / `exists_CBTM_iso_NTM2`）。**语义量（κ/激活生成元/本质维度）不随同构传递**——定义在 CBTM 路径的读符号虚部上。

### 7.2 输入格式规范（ATM 形式）

- **字母表语义分类**：\|Σ\| ≥ 4 = 2 数据（data0/data1）+ 1 分隔（sep）+ 1 结束（boundary）——4 为最小完备数；编译（符号→bit）清除分隔/边界/分支语义 → bit 层表示不足，**定义必须停留符号层**（约定 20）。
- **规范输入形态**：边界符包裹的元素向量。项目实例（Sym 层编码）：`#ₗ target #₀ 元素区 #₁`——三边界符位置 0 / n+1 / L-1（#ₗ 输入起始、#₀ target 结束、#₁ 输入结束）。**位置一律 0 基**（List 索引语义，与 `cfg.headPos : ℤ` 一致）：L 个符号占据位置 0 … L-1。
- **初始态申明**：**ATM 的初始态中，读写头位置为 0**——初始读写格 = #ₗ@0；Lean 实体：`symInitialConfig.headPos = 0`（Core:322）。**推论（负位格不入算法定义域）**：0 格以西（−1、−2…）不存在格——初始态及其同相运行**不得以任何负位格为语义前提**；凡以「带外负位格」（含 −1 格）供给语义的论证均违反算法定义。（与下方运行禁区定理 `0 ≤ headPos` 一致：负位格既不假设、也不可达。）
- **长度记法**（贯穿 §7 位置断言；Sym 层只有符号，无 bit）：记 L = 输入符号个数 = `(encodeInstanceSym inst).length` = n + Σ + 3（`r7_enc_len`），其中 n = `(encodeBitsSym inst.target).length` = **target 段符号个数**（data0/data1 符号，每个符号对应 target 的一个二进制 digit）、Σ = `(encodeElementsSym inst.elements).length` = **元素段符号个数**（每元素 = 1 个 α 标记符号 + 值位串符号）；3 = 三边界符符号。#₁@L-1、#₀@n+1；#₀'（活动边界）∈ [n+2, L-3] 由占位扩展链维护。hpos（元素值 ≥ 1）⇒ Σ ≥ 2 且 L ≥ n+5。
- **元素** = 分隔符 α + 原生值位串；值 ≥ 1（无前导零、MSB=data1——**合法性内建**；格式检查 24/26/27 读 data0 → 101 拒绝）。
- **骨架可机器验证**：格式检查段 24→29→26→27→38→28 = ATM 的输入骨架验证器；`format_check_precise`/`symAccepts_implies_encodeInstanceSym` = 骨架定理（接受 ⟹ 输入具 ATM 骨架——条款 4 的实质）。

**合法输入定义（规范层）**：

> 讨论运行（可延拓路径）时**先假设输入是合法的**；不合法输入直接进 101（机器自检，非证明层假设）。合法输入 = 有限长符号串且具 ATM 骨架：

1. **有限长**：输入是 List Sym（List 类型内建有限性）——任意合法输入有限长；有限长是头域/步数论证的边界前提。
2. **至少三个边界符**：合法输入具形态 `#ₗ target #₀ 元素区 #₁`——三边界符 #ₗ / #₀ / #₁；**左边界符 #ₗ 就在带头 0 位置**（#ₗ@0），#₀@n+1，右边界符 #₁@L-1（输入结束）。
3. **内容合法性**（合法性内建于符号，非外部约定）：target ≥ 1（MSB = data1）、每元素值 ≥ 1（无前导零、MSB = data1）——格式检查 24/26/27 读 data0 → 101。
4. **合法性机器自检**：格式检查段（0→1→2→3→24→…→38→28）扫过全输入——不合法形态直接 101；到达选择入口 4 即输入通过骨架验证——故**接受路径（延拓到 100）的输入自动合法**。

**运行禁区定理（须以 Lean 定理确定）**：

> "不可能越过左边界和右边界；**所有考虑越过左边界或者右边界的假设都是错误假设**。"

- **定理（越界禁区）**：可延拓（到 100）路径上的任意 cfg：`0 ≤ cfg.headPos ≤ L-1`——带头恒在三边界符包络 [0, L-1] 内，不越过 #ₗ 之左、不越过 #₁ 之右。
- 推论：一切负头 cfg（头 < 0）与带外漂移 cfg（头 ≥ L——如 21@L/87@L 右漂）作为**可延拓路径成员**的假设均被定理排除（漂移延拓终点 ≠ 100 是定理的证明内容之一）。
- 相关 Lean 件：q12 族（`Reverse6`/`Reverse7L3` 引理区）与 P6l/P6r/P9 位置引理族；合法输入域内的每前缀位置界由 ①线 `PosBound*` 族供给（§4.4）。

### 7.3 带外与空白语义

- **经典 blank 双职问题**：blank 兼任「输入结束标记 + 带外填充」（语义混淆）——ATM 拆分：输入结束 = #，带外 = #（blank 转化为边界符，约定 23）。
- **语义**：`Sym.blank = data0-false`——带外是 `blank` 填充。
- **组编码层为内部实现细节**：kindBits 取值不影响语义与语法（不裁决；以代码 `Sym.kindBits` 为准，boundary = (1,0,1,1) 即 (re₁,im₁,re₂,re₃)）。
- **Lean 实现状态：迁移仍待**——当前 `Core:174` `def blank := data0 false`（全库多处引用依赖 data0-false）。

### 7.4 语义内建原则（数计一体）在自动机层的落点

1. **符号层**：虚部 = 分支（读 im=true 恰 2 结果——分叉由符号规定，非机器任选；不可再生：数据读写写回虚部全 false）；IVM 以不可公度性（√p_i ∉ ℚ）把语法分叉落实为语义分离（约定 22）。
2. **输入层**：边界/分隔内建为符号——输入骨架机器可读、可验证。「有些 DTM 根本不能作为算法考虑（连处理可变输入的能力都没有）」的精确含义 = 输入边界外部化的后果；ATM 使可变输入处理能力内建。
3. **状态层**：m（mark）是独立维度（Sym 第二分量，计数器标记，运行时写入 #₁ 等）——输入编码 m 恒 0，不涉及对虚部的处理。

### 7.5 机器-概念对应锚点（规范引用）

- 带外符号实体：`Sym.blank`（= data0-false）——Reverse7L3 P6l/P6r/P9 系、q12 IsOutside 系、tape/getD 默认值均引用此实体。
- 分叉事件 = 激活（IVM）；见证对应：CBTM 路径标记 Π ∈ {α,β}^m ↔ IVM 激活向量 a ∈ {0,1}^m，Φ : α↦1, β↦0 双射。
- 骨架验证 = 格式检查 = ATM 语义的机器内建（接受路径自动验证输入合法）。
- 可变输入能力：机器族定义（NTM2/CBTM 的 input : List）由 List 类型内建（长度可变）；ATM 骨架谓词承担者 = format_check_precise 系。

### 7.6 验证器运行机制规范（三链模型）

> 本节把对 Sym 验证器（`SubsetSumVerifierCore`）运行机制的理解固化为规范——**消耗链 / 清理链 / 占位扩展链**及其关键语义。运行总判据：**所有操作都发生在右边界符 #₁（含）左侧**；不停左走的状态显然满足；右走状态归约到左走状态即满足。三链是 Reverse7L3 束（P0'…P9 位置引理）与后续终止性/步数界论证的语义依据。

**元素处理主循环**（4 = 入口/回环态；每轮恰处理一个元素）：

| 阶段 | 状态序列 | 职责 | 代码要点（Sym 层转移表） |
|---|---|---|---|
| 选择 | 2 →（α 双分支）→ 4 | 2 读 α 写 sel/nosel（guess 判定）；4 读标记进入消耗或跳过 | 4 读 sel → 5 R 写 data0；4 读 nosel → 20 L **写 data0**（置选择位 0） |
| 消耗链 | 13 → 5 → 8/76 → 9/77 → 10/11/12/14/81 → 13 | 选中元素值逐位减 target：13 读数据位 → 5 S 写 consumed（消耗区右扩）；8/76 L 左扫至中分界符；9/77 转 target 减轮；余位回 13 继续 | 13 读 consumed → 13 R（穿）；13 读 sel/nosel/boundary（α_{k+1}/#₁）→ 84 进清理链 |
| 清理链 | 84 → 85 → 86 → 87 → 20 | 扫过已处理区：84/85/86 L/S 左扫（86 读 data-false → 87 S），87 停于活动边界 #₀'（或原生 #₀@n+1）读 boundary → 20 | 87 扫段止于 #₀'（v 末位 k-1 ≤ L-3），**不读 #₁** |
| 占位扩展链 | 20 → 21 → 51 → 4 | 20 读中分界符写 data0 R 变 21（**中分界符消除**）；21 R 清扫已处理元素区（consumed/data → data0）至第一个 sel/nosel；51 读 data0 → 4 R 写 boundary（**重建 #₀' 于下一元素左邻**）；4 读 α_{k+1} 进入下一轮 | 20 读 boundary → 21 R 写 data0；21 读 data/consumed → 21 R 写 data0；21 读 sel/nosel → 51 L 写回；51 读 data0 → 4 R 写 boundary |
| 判定链 | 22/23 | 末元素处理完进判定：23 左扫 target 余值——全 data0 → 读 #ₗ → 100 接受；遇 data1 → 101 拒绝 | 21 读 #₁ → 22 S；23 读 data1 → 101；23 读 #ₗ → 100 R |

**关键语义（用户原文**）：

1. **20 = 占位扩展（#₀' 挪移器）**："20是占位扩展，即将中边界符挪到新位置，即所处理的元素的数据最高位。由于是元素的数据区，因此，必定在右边界符左边。"——20 读 #₀@n+1 或 #₀'@活动边界；"20 将中分界符消除以后，就变成了 21"（写 data0 R）；**20 的头 ∈ [n+1, L-3]，恒 ≠ 0 且 ≠ L-1**（P6l/P6r 的 20 排除依据）。
2. **末元素省写 #₀'（#₁ 顶替）**："对于最后一个元素的最高位，由于下一位是右边界符，就省去了写中边界符，直接利用右边界符做了中边界符。"——21 清扫直接遇 #₁@L-1 → 22 S 判定入口；#₁ 充当最后的中分界符。
3. **51 = 重建中分界符**："51是重建中分界符，将中分界符建立在下一个元素的左边。"——51 写 boundary@α_{k+1}-1（= 已处理元素 MSB，21 已清 data0）。
4. **4 读 nosel → 20 L 写 data0@α_k**（置选择位 0，非写回 nosel）——21 随后穿过被清的 α_k，把整个未选元素值区清成 data0——**未选元素同样被消除**（无"nosel 死循环"）。
5. **终止性（良基语义来源）**："元素的个数是有限的，每一次占位扩展就消除一个，总有一次会消除完的。" / "4到4，则必然意味着一个元素被处理了。"——4→20→21→51→4 每轮恰消除一个元素（4 = 主循环回环态）；元素有限 ⇒ 扩展序列有限、无无穷循环；"4 到 4"往返数 ≤ 元素数。
6. **sel/nosel 来源**："sel/nosel是alpha被替换得到的。"——初始元素分隔符 = α；2 态双分支把 α 替换为 sel/nosel（guess 判定）；21 清扫以第一个 sel/nosel 为停点（保护当前元素判定格），**绝不越过标记**。
7. **target 区格式约束只属于初始**："通过51的操作，元素被消除了一个，target区不再要求最高位必须是1（这一点是初始输入时需要的）。"——初始要求 target 编码 MSB=1（htarget；格式检查 24/26/27 读 data0 → 101）；元素消除（减轮 10/11/12/14/81 改写 target）后不再要求——23 判定只扫当前余值是否全 0。

**头域几何（位置引理族的规范依据）**：

- 固定边界：#ₗ@0、#₀@n+1、#₁@L-1；活动边界 #₀' ∈ [n+2, L-3]（末轮由 #₁ 顶替）；元素数据区 ⊆ [n+2, L-2]（恒在 #₁ 左侧）。
- 20 头 ∈ [n+1, L-3]（读位 = #₀@n+1 ∨ #₀'@活动边界）；87 读 boundary 的头 ∈ [n+1, L-3]；21 清扫停于第一个 sel/nosel（或 #₁ → 22）。
- 判定链从 #₁@L-1 进入（22 S@L-1 或 21 读 #₁ → 22 S），23 左扫 target 余值至 #ₗ。

---

### 7.7 符号层复杂度类与分离结论（P_sym0 ≠ NP_sym0，集合论意义，对齐域）

> 本节说明符号层（ATM/NTM2）上与经典 P≠NP 对应的分离结论及其精确含义。

**（一）载体与判定域**

- 符号层语言 = `List F4` 上的谓词；符号 {0,1,sep,#} 以 F4 直读值承载（约定 20 查表：0↔(0,0)、1↔(1,0)、sep↔(0,1)、#↔(1,1)）。
- 判定域 = **符号对齐串** `IsSymbolAligned w := ∃ wS, w = flat4F4 wS`（4F4 计算符号串；4 带机无半符号，缺项输入语义已失——约定 26）。类成员资格与机器性质**只在该域内断言**（对齐域口径）。

**（二）类定义（符号层）**

- **P 类（CBTM0 承载）**：`IsP_sym0 L := ∃ M : CBTM, IsRestricted M ∧ isPolynomialTimeAligned M ∧ (∀ w, IsSymbolAligned w → (M.tapeAccepts w ↔ L w))`——受限 CBTM（虚部=0 层同构类，与 DTM 双向同构：`exists_CBTM0_iso_DTM`/`exists_ClassicDTM_iso_restrictedCBTM`）。
- **NP 类（NTM2 承载）**：`IsNP_sym0 L := ∃ A : NTM2, NTM2.isPolynomialTimeAligned A ∧ (∀ w, IsSymbolAligned w → (NTM2.acceptsTape A w ↔ L w))`。

**（三）分离结论**

**`P_sym0 ≠ NP_sym0`**（`Mp/ATMAssembly.lean`）——**集合论意义**：两个语言类的集合不等。见证语言 = 子集和：

- **∈ NP_sym0**：见证机 = `subsetSumNTM2`（CBTM1≅NTM2 同构解机）；正确性 = 对齐域判定正确性（实例形域经同构桥搬运 + 尾缀消去；非编码拒绝）；多项式 = 自 `NTM2.Canonical` 的路径长界 × 分叉界。
- **∉ P_sym0**：F 层分离定理的适配。引擎：受限机（**无虚部读取能力**——字母表 ⊆ {zero,one} 且读字母表外符号转移为空）⇒ 可达读全 im-false ⇒ **κ = 0**；而子集和的任何正确机须**读取每个虚部标记格** ⇒ **κ ≥ n**（下界 `subsetSum_kappa_lower_bound`）⇒ 取 n = 1 的实例矛盾 ⇒ 不含于 P 类。

**（四）定位：受限机类的能力分离；与经典 P≠NP 的距离**

- **已证内容**：受限字母表机器类（CBTM0 承载，虚部=0 层）不含子集和——引擎 = **能力缺口**（受限机无虚部标记读取能力 ⇒ κ = 0；正确性 ⇒ κ ≥ n）。κ 相异性是代数事实（素数平方根 ℚ-线性独立，可计算、对符号置换稳定，非约定标签）。
- **时间条件的正确归属（不可误读）**：上述否定**与时间界无关**（证明未引用 `_hpoly`）——但**这一点只对受限机成立**。**存在一般确定性机在指数时间内解出子集和**（枚举 + 验证），故对一般确定性机，「解不了」**只在多项式时间约束下成立**；「一般确定性机多项式时间不可解」（经典 P≠NP 的实质）**不在本工程已证范围**。
- **与经典 P≠NP 的距离**：**受限机类 ⊆ 一般确定性机类 ⇒ `P_sym0` ⊆ 经典 P 类** ⇒ 本结论（受限机类 ≠ NTM2 类）**弱于**经典 P ≠ NP。加之两层外部语义：**结构语义**（引约定 20：经典 P 类定义中的机器只读符号串，sep/# 与数据不可区分——结构身份为外部命名，可逆标签；区分结构需要表示能力，|Σ| ≥ 4 最小完备）；**边界语义**（引约定 23：「输入在何处结束」为外部给定——δ 无输入结束符号/状态，blank 机制依赖「输入内无 blank」的隐含承诺，单看纸带+无限比特流则边界不可判定；**该先验假设违背信息论**：边界为非零信息量而纸带与语法均不携带，定义外部注入 ⇒ 语义不闭合）。故「经典 P 类 ↔ 符号层类」的对比**必须经编码桥**，桥须论证结构与边界**两种语义**的对应，其合法性/信息损失即本结论「框架内」限定的技术内容。
- **与 F 层的关系**：与 `P_F ≠ NP_F` 是同一定理的两种表述（`isP_sym0_iff_isP_F` 定义级相等；`subsetSum_not_in_P_sym0` 即 `subsetSum_not_in_P_F`）。

**（五）分支语义相异证书（桥件 T1/T2）**

- **T2（代数分开，`Mp/ATMTransfer.lean`）**：`pathValue`（不分号模式版 = Σ√p_i，素数族 `Nat.nth Nat.Prime`）+ `pathValue_separated`——**激活模式不同 ⇒ 路径值不同**（素数平方根 ℚ-线性独立）——「两条路径完全分开」的代数形式。
- **T1（位置桥，`Mp/ATMTransfer.lean`）**：`iso_path_forward_forkCount`——iso 路径对应下 **`ntm2ForkCount A π = branchCount π'`**（读符号恒等翻译）；`iso_vbAt_iff_card_two`——点态 vb=1 ⟺ CBTM 读空白处卡恰 2。

**（六）诚实边界（与约定 22 一致）**

- 结论的语义基础在 CBTM/IVM 框架：虚部 = 分支的内建语义；假分支排除 = 不可公度性（√p_i ∉ ℚ）、在 IVM 中两条路径完全分开。
- **脱离 CBTM 框架、仅在经典框架下无法证明**：NTM2 的分支可能是假分支（形式两分支、语义一分支）——语义超越语法；假分支不可排除，故纯经典框架内不闭合。这正是本结论必须经由框架的原因。
- 备注：符号层 P 类定义式与 F 层 `IsP_F` 定义级一致（`isP_sym0_iff_isP_F`）——**两版结论是同一定理的两种表述**（`subsetSum_not_in_P_sym0` 即 `subsetSum_not_in_P_F`），不是两种强度的结论；定位细则见约定 29。
- **信息论边界（引约定 20）**：bit 层表示不足（编译清除分隔/边界语义）⇒ P/NP 定义必须停留在符号层（|Σ| ≥ 4）；「经典 P 类 ↔ 符号层类」的对比须经编码桥，桥的合法性/信息损失即本结论「框架内」限定的技术内容。
- **边界先验性同样违背信息论（引约定 23）**：经典定义把「输入在何处结束」作为先验外部语义引入——该信息在纸带与语法中均无来源（信息无源产生），语义不闭合；与上条（结构语义外部化）并列，构成编码桥须论证的两种语义对应。

**（七）桥的性质与合法用途（`ClassicDTM.toCBTM`）**

- **构造事实**：`ClassicDTM → CBTM` 的像**强制**字母表为 `{F4.zero, F4.one}`；转移在 sep/边界符（位对 (0,1)、(1,1)）上返回**空集**；同构 `StructIsoClassicDTM` 的转移对应子句**只约束 {zero,one}**。⇒ 该桥是**单向「能力擦除」映射**：4 符号确定机 ↦ 看不见 sep/边界符 的受限机。
- **限制**：若经典 DTM 的运转**需要读 sep/边界符 格**（如解析输入骨架），其像在对应步转移为空 ⇒ 无法模拟 ⇒ **「任意经典 DTM 被 CBTM0 承载」不成立**（sep/边界符 读障碍）。
- **框架口径下的合法用途（唯一）**：框架对「经典确定性计算」的定位是**虚部=0 层**（DTM ≅ CBTM0 = 取实部 + 虚部全 0）。该层上：读符号全 im=false；桥**逐点忠实**（转移对应、接受性保持）；κ ≡ 0。⇒ 桥的正确用途 = **在虚部=0 层内双向搬运行为与 κ=0 结论**（第 4 步「κ=0 传递」的形式依据）+ 双向存在性（`exists_CBTM0_iso_DTM` / `exists_ClassicDTM_iso_restrictedCBTM`）。**它不承载**「能读 sep/边界符 的经典机」。
- **对结论定位的约束**：`P_sym0` 承载的是「虚部=0 层确定机」；**能读标记格的经典机不在承载域** ⇒ 不构成对经典 P 类的完整承载 ⇒ 这是本结论必须带「框架内」限定、且**不能单独**支撑框架外经典 P≠NP 的原因；若将来主张标准语义的经典 P≠NP，需**新的承载论证**。
- **为何不构造「忠实承载」的桥**：形式上不可能——`h_branch_rule` 要求「读 im=true ⇒ 结果卡恰 2」，而确定机读 sep/边界符 只有单结果；`h_transition_outside` 要求字母表外符号读 ⇒ 空集。

## 8. 验证器状态机语义（Sym 版）

> 本节固化对 Sym 层验证器（`VerifierSym`，`SubsetSumVerifierCore.lean` 转移表 33 态）的完整理解：
> 编码与带布局、状态流程语义、状态-区域对应。区域对应声明：**所有状态的活动区域 ⊆ target 区 ∪ 数据区 ∪ 边界
> （#ₗ/#₀/#₁）——不存在越界状态**（可延拓路径头 ∈ [0, L-1] 的表级依据）。

### 8.1 编码与带布局

- 逻辑符号 = `SymKind × Bool`：**8 种 kind**（data0/data1/consumed/alpha/sel/nosel/beta/boundary），
  Bool = m 位（4F4.4，计数器标记，运行时写在 target 位上）。
- 输入编码（encodeInstanceSym）：`#ₗ t₀…t_{k-1} #₀ [α v₁][α v₂]… #₁`——target 位 LSB 在左；每元素 = `α + 原生可变长位`
  （无分隔符，α 兼任分隔与分支符）；**β 不用于编码**，元素区读到即拒绝。
- 运行时带形变化：α 被 sel/nosel 替换（分支）；#₀ 右移（占位扩展）、末轮由 #₁ 顶替；元素位被 consumed（处理中）/
  data0（清除）替换；target 区 m 前缀 = 已处理位号（计数器），元素处理完由 86 复位。

### 8.2 状态流程语义（每条路径/阶段）

| 阶段 | 状态 | 语义 |
|---|---|---|
| **分支** | 0 → 1 → 2 → 3 | 0 验证 #ₗ@0；1 R 扫 target 区；2 R 扫元素区：**读 α(m=0) 双分支写 sel/nosel**（唯一非确定性点），读 α(m=1)/β → 101，data 跳过；遇 #₁ → 3 |
| **格式检查** | 3 → 24 → 29/26 → 27 → 38 → 28 → 4 | 3 标 #₁ m=1 后 L；24 检查元素最高位 = data1（v>0，反向前进）；29 左扫 data；26 在元素头配对（sel/nosel → 29 查下一元素；data1 → 29 继续）；26 读 #₀ → 27 L 查 target 最高位 = data1（27/38）；38 左扫 target 至 #ₗ → 28 R 右扫回；28 穿 #₀ → 4 |
| **主循环**（4 = 入口/回环态，每轮恰处理一个元素） | 4 | 4 读元素头选择符位：sel → 5（选中，清选择位 data0 R）；nosel → 20 L（未选，占位扩展清除） |
| **消耗链** | 13 → 5 → 8/76 → 9/77 → 10/12 → 11/14/81 → 13 | 逐位处理元素值：5 读位：data1 → 76（减 1 路径，写 consumed）；data0 → 8（只记位号路径，写 consumed）。两路均左穿 #₀（76→77、8→9）到 #ₗ 后右扫，沿 m 前缀找第一个 m=0 定位 t_j（10 减路径 / 12 记位号路径）；**减 1**：11 在 t_j（data1 → data0 完成；data0 → 14 借位写 data1），14 借位右传（data0 → data1 传播；data1 → data0 终止；穿 #₀ → 101 = target 不足拒）；81 右回元素区（穿 #₀ 自然穿透），13 扫 consumed 区找下一未消费位；元素耗完（13 读 sel/nosel/#₁）→ 84 |
| **清理链** | 84 → 85 → 86 → 87 → 20 | 84 左穿 #₀（84 读 #₀ → 85）；85 左扫 target 至 #ₗ → 86 R **清计数器**（m=1 → 0，保值）；86 遇 m=0 → 87 S；87 右扫至 #₀ → 20 |
| **占位扩展链** | 20 → 21 → 51 → 4 | 20 读 #₀（#₀ 消除）写 data0 R → 21；21 R 清已处理元素区（consumed/data → data0）；遇下一元素头 sel/nosel → 51 L；51 左扫清区（全 data0）**末位写 boundary = 新 #₀ 重建于下一元素左侧** → 4（下一轮）；21 遇 #₁（末元素，#₁ 顶替 #₀'）→ 22 |
| **判定链** | 22 → 23 → 100/101 | 22 读 #₁(m=1) → 23 L 左扫 target：全 data0 → #ₗ → **100 接受**；遇 data1 → 101 拒绝 |

吸收态：100（accept）/101（reject）均 S 自环，读任意符号不移动不改写。

### 8.3 状态-区域对应表

区域定义：target 区 = 位置 [0, n]（#ₗ@0 … target 位 … #₀@n+1 为右界，含 #₀ 格）；数据区（元素区）= 位置 [n+2, L-1]
（α 元素位 … #₁@L-1 为右界）；「两区」= 单轮内穿越 #₀ 在两侧移动的状态。**表中无越界状态**。

| 区域 | 状态 | 活动说明（含触达边界） |
|---|---|---|
| **target 区** | 0 | 仅读 #ₗ@0（起点验证） |
| | 1 | R 扫 target 位至 #₀ |
| | 9 | 左扫 target（含 m=1 位）至 #ₗ |
| | 10 | R 扫 m 前缀定位 t_j（第一个 m=0 → 11）；读 #₀（target 不足）→ 101 |
| | 11 | t_j 上 S：减 1 / 借位发起 |
| | 12 | R 扫 m 前缀定位 t_j（记位号路径：m=0 → 标 m=1 保值 → 81）；读 #₀ → 101 |
| | 14 | 借位右传（data0→data1；data1→data0 止）；穿 #₀ → 101 |
| | 23 | 左扫 target 判定（data0 过 / data1 → 101）；#ₗ → 100 |
| | 27 | 仅 target 右端首格（最高位 = data1 检查） |
| | 28 | R 扫 target 区回程（#ₗ → #₀ → 4） |
| | 38 | 左扫 target 区（data → 38；#ₗ → 28） |
| | 77 | 左扫 target 区（data → 77；#ₗ → 10） |
| | 85 | 左扫 target 区（data → 85；#ₗ → 86） |
| | 86 | R 扫 target 清计数器（m=1→0 保值；m=0 → 87） |
| | 87 | R 扫 target（data → 87；#₀ → 20） |
| **数据区（元素区）** | 2 | R 扫元素区：α 分支 / data 跳过 / β 拒；#₁ → 3 |
| | 3 | 仅 #₁@L-1（标 m=1 后 → 24 L） |
| | 4 | 元素头选择符位（sel → 5 / nosel → 20；回环入口） |
| | 5 | 元素值位（data1 → 76 / data0 → 8，写 consumed） |
| | 8 | 左走元素区至 #₀（记位号路径） |
| | 13 | R 扫 consumed 区找下一未消费位（data → 5）；元素头/#₁ → 84 |
| | 21 | R 清元素区（consumed/data → data0）；sel/nosel → 51；#₁ → 22 |
| | 22 | 仅 #₁@L-1（m=1 → 23 L） |
| | 24 | 元素区右端最高位检查（#₁ 左邻起反向扫；data0 → 101） |
| | 26 | 左扫配对元素头（sel/nosel/data1 → 29；data0 → 101）；#₀ → 27 |
| | 29 | 左扫元素值位（data → 29；sel/nosel → 26） |
| | 51 | 左扫已清元素区（data0；末位写 boundary = 重建 #₀'）→ 4 |
| | 76 | 左走元素区至 #₀（减 1 路径；consumed/data → 76；#₀ → 77） |
| | 84 | 左走元素区至 #₀（consumed/data → 84；#₀ → 85） |
| **target + 数据区（穿 #₀）** | 81 | target 区 R 扫 → **自然穿透 #₀** → 数据区 consumed 区（consumed → 13）：减法回程 |
| **边界格** | 20 | 仅 #₀ 格（读 boundary → 写 data0 R：占位扩展消除 #₀；活动 #₀' 或原 #₀） |
| **终点吸收** | 100/101 | S 自环，位置不定（100 进入于 #ₗ 左端判定完成；101 进入于各拒绝点），不移动不越界 |

注：26/28/76/8/84/87 等「读 boundary」的臂只触达 #₀/#₁/#ₗ 三个边界格之一，随即转向，不进入另一区行走；
81 是唯一在两区间行走的状态（减法后回程，穿透 #₀）。「应当没有越界」= 上表即全部 33 态的活动范围，
无任何状态可在带外行走（运行禁区定理 P6l/P6r/P9 的表级依据）。

### 8.4 关键语义确认

1. **12 态只动 m（计数器加 1）**：12 读 data0/data1（m=0）→ 写回**同 kind 保值、m=true**（data0 true / data1 true），
   符号值不变——「只记位号，不减」；与 10 态定位（保值标 m）一致。减 1 路径中 11/14 才改写值（借位传播 data0→data1）。
2. **借位右传方向**：LSB 在左（#ₗ 侧），借位向右（#₁ 方向 = 高位）；借位穿 #₀ ⟹ target 不足 → 101。
3. **减法语义**：处理元素位 v_j=1 ⟹ t -= 2^j；v_j=0 ⟹ t 不变仅推进 m 前缀。判定时 target 全 0 ⟺ 选中子集和 = target。
4. **终止性**：主循环 4 → 4 每轮恰消除一个元素（占位扩展），元素数有限 ⟹ 终止；判定链只在末元素处理后进入。
5. **非确定性**：α 是唯一分支格（2 态读 α → {sel, nosel}），读一次即被替换 ⟹ 每元素恰一次分支（②：标记格 ≤ 1 读），
   接受路径 fork 数 = 元素数。

### 8.5 重要函数（模块）与详细语义

模块缩写：**Core** = Mp.SubsetSumVerifierCore（Sym 代数与状态机本体）、**CBTM** = Mp.SubsetSumVerifierCBTM（4F4 编译层）、
**CoreA** = Mp.SubsetSumVerifierCoreA（带选择与数学语义）、**Core1** = Mp.SubsetSumVerifierCore1（段构造）、
**Real** = Mp.SubsetSumReal（语言层）。行号为易失信息，以符号名搜索为准。

**8.5.1 Sym 代数与组码（Core）**

| 函数 | 位置 | 详细语义 |
|---|---|---|
| `SymKind` | Core:124 | 8 种 kind：data0/data1/consumed/alpha/sel/nosel/beta/boundary |
| `Sym` / `Sym.mk k mark` | Core:146/151 | `Sym = SymKind × Bool`；第二分量 = m 位（4F4.4 计数器标记，默认 false） |
| `Sym.data0/data1 (mark)`、`Sym.alpha/sel/nosel/consumed/beta/boundary` | Core:162-171 | 构造器（m 默认 false；α/β = 分支符号） |
| `Sym.kindBits` | Core:177 | kind → `(re₁, im₁, re₂, re₃)` 位组：data0=(0,0,0,0)、data1=(1,0,0,0)、alpha=(0,1,0,0)、consumed=(0,0,0,1)、boundary=(1,0,1,1)、sel=(0,0,1,0)、nosel=(0,0,1,1)、beta=(1,1,1,0) |
| `Sym.toF4s` | Core:189 | Sym → 4×F4：`[(r1,i1),(r2,false),(r3,false),(m,false)]`——**虚部标记 i1 落第 1 格**（计数用排布：im-true 格数 = 分支?1:0） |
| `Sym.blank` | Core:174 | `= data0 false`（带外符号；语义已定为 boundary-false，代码值未迁移——见 §7.3） |

**8.5.2 Sym 层编码（Core）**

| 函数 | 位置 | 详细语义 |
|---|---|---|
| `encodeBitsSym`（= `encodeBitsSymNative`）| Core:200/204 | 自然数 n 的原生可变长二进制（`Nat.digits 2 n`，LSB 左、不补零）→ data0/data1 列表（m=false） |
| `encodeElementsSym` | Core:209 | 元素列表 → `[α v₁][α v₂]…`（每元素前缀 α，β 不用于编码） |
| `encodeInstanceSym` | Core:218 | 实例 → `[#ₗ] ++ target位 ++ [#₀] ++ 元素区 ++ [#₁]`（纯正轴带） |

**8.5.3 运行语义类型（Core）**

| 函数 | 位置 | 详细语义 |
|---|---|---|
| `SymTransResult` | Core:303 | 一步结果 `{nextState, writeSym, moveDir}` |
| `SymStep` | Core:310 | 一步 `{fromState, readSym, result}`（源态 = 步前 cfg 态；读符号 = 步前带头格） |
| `SymConfig` | Core:316 | 格局 `{state, tape : ℤ → Sym, headPos : ℤ}` |
| `symInitialConfig` | Core:322 | 初始格局：state = qStart、带头 0、带 = 输入（带外 = blank） |
| `symStepConfig` | Core:329 | 步后格局：原位写 writeSym、头按 moveDir 移 ±1/0 |
| `SymReachablePath M input` | Core:335 | 归纳定义：从初始 cfg 出发经 π 可达 cfg（Cons 前提 = 转移成员 + 读-带一致 + 源态一致） |
| `symAccepts M accept` | Core:346 | `∃ π cfg, SymReachablePath … ∧ cfg.state ∈ accept`（接受 = 存在到达 accept 集的路径） |

**8.5.4 状态常量与转移表（Core,namespace `VerifierSym`）**

| 函数 | 位置 | 详细语义 |
|---|---|---|
| 状态常量（语义名）| Core:358-402 | `qAccept=100`（吸收接受）、`qReject=101`（吸收拒绝/trap）、`qStart=0`、`qCrossTarget=1`（扫 target）、`qBranch=2`（α 双分支）、`qMarkHash1=3`（标 #₁）、`qScanElem=4`（主循环入口）、`qSubScan=5`（元素位判定）、`qLeftSub=76`/`qLeftSub2=77`（减 1 路径左穿/扫 target）、`qLeftOnly=8`/`qLeftOnly2=9`（记位号路径左穿/扫 target）、`qFindSub=10`（减 1 定位 t_j）、`qSubtract=11`（按位减）、`qFindOnly=12`（记位号定位 t_j）、`qBorrow=14`（借位右传）、`qBackA=81`（回元素区穿透 #₀）、`qBackB=13`（扫 consumed 区）、`qExpandStart=20`/`qExpandScan=21`/`qNewHash=51`（占位扩展链）、`qCheck=22`/`qCheckLeft=23`（判定链）、`qFmtFirst=24`/`qFmtData=29`/`qFmtPair=26`/`qFmtTgt1=27`/`qFmtTgt=38`/`qFmtBack=28`（格式检查链）、`qClrLeft=84`/`qClrTgt=85`/`qClrMark=86`/`qClrBack=87`（清理链） |
| `acceptStates` | Core:401 | `{qAccept} = {100}` |
| `legalStates` | Core:403 | 33 态显式集合；表外状态一律归 101 |
| `transition` | Core:404 | 完整转移表（match 臂全 33 态 × 符号；读-写-移三件；α(m=0) 双结果 = 非确定点）|
| `verifierSymTransition` | Core:533 | `transition` 对外别名 |

**8.5.5 4F4 编译桥（CBTM）**

| 函数 | 位置 | 详细语义 |
|---|---|---|
| `symTo4F4` | CBTM:53 | Sym → 4×F4（编译排布）：`[(r1,false),(r2,false),(r3,false),(m,i1)]`——**前 3 格虚部恒 false，i1（分支性）落第 4 格虚部、m 落第 4 格实部**；第 4 格 im = true ⟺ kind ∈ {α, β}（分支格判定 = 读 4F4 第 4 格 im） |
| `symOf4F4` | CBTM:71 | 4 格 → Sym（symTo4F4 逆；第 0-2 格虚部非 false = 非法编码 → none） |
| `flat4F4` | CBTM:103 | Sym 串 flatMap → F4 串（每个 Sym 展 4 格） |
| `encodeInstanceF4` | CBTM:106 | 实例 → `flat4F4 (encodeInstanceSym inst)`（4F4 编译输入带） |
| `encodeState q phase reg` / `decodeState` | CBTM:114/116 | 12 相位状态编码：`q*12*8192 + phase*8192 + reg`（`stepsPerSym=12`、`regBound=8192`、`qBound=102`） |
| `transition4`/`acceptStates4`/`subsetSumCBTM` | CBTM:207/406/413 | Sym 步的 12 相位展开转移/编译接受态/编译机（见 §7.1 族谱） |

**8.5.6 带选择与数学语义（CoreA）**

| 函数 | 位置 | 详细语义 |
|---|---|---|
| `encodeElementsSymWithSel/Chosen` | CoreA:53/57 | 物理带编码（每元素 α 被 sel/nosel 替换后）/逻辑编码（仅选中元素拼接，供数学验证） |
| `scanSelPrefix` | CoreA:77 | 从带上读回选择：扫描元素头格（sel=true/nosel=false）→ Bool 列表 |
| `subAllSelected` | CoreA:1586 | 数学减法语义函数：k 位 tbits − Σ 选中元素（位列表级，子集和判定的数学基准） |

**8.5.7 段构造与语言正确性（Core1/Reverse3）**

| 函数 | 位置 | 详细语义 |
|---|---|---|
| `scanRight1/scanRightKeep/scanLeftKeepPos/scanRight87` 等 | Core1（区域） | 单段扫描路径构造函数：给定带区间与保持条件，构造一段单调扫过的 SymSteps（步数 = 距离；格式检查/减法定位段的正向证据） |
| `format_sweep_rec/format_sweep_correct` | Core1（区域） | 元素区格式化扫过段（24/26/27/28/38 链）的路径构造与正确性 |
| `symVerifier_correct` | Reverse3:7235 | **主语言正确性**：对合法非空实例，`subsetSumHolds inst ↔ symAccepts VerifierSym.transition VerifierSym.acceptStates (encodeInstanceSym inst)`（验证器语言 = 子集和语言的机器层证明；消费于 `SubsetSumInNP`/`L3a`/`Reverse6`） |

### 8.6 ③线 C3：主链口径与落件速览

**现行主链落件（全部机器验证）**：

| 环节 | 件 | 位置 |
|---|---|---|
| ① α替换 | `segS0`（≤ L+3） | `Reverse12:965` |
| ② 格式检验 | `segS1`（≤ 2L） | `Reverse12:1913` |
| ③ 未选支 | `segSrNosel`（≤ n+5） | `Reverse12:2578` |
| ③ 选中支 | `segSrSel` / `segSrFold`（全1全选族 → 22；段界 `foldLenB` 二次形） | `Reverse13` |
| 折叠→判定接线 | `judge_after_fold` | `Reverse15:40` |
| 四相位串联 | `phase_decomp`（初始 →100，界 = 四段之和） | `Reverse15:475` |
| 主界 | `main_le_quad`（≤ 16·(E+1)²）；`main_sym` / `main_f4`（`∃K, ≤ K·(m+1)·(|x|+1)²`；`x = encodeInstanceF4 inst ++ flat4F4 gS`，|x| 桥经 `flat4F4_length`：|x| = 4E+4|gS| ≥ 4E） | `Reverse15:698/857/875` |
| ④ 判定 | `segS3`（≤ n+2） | `Reverse12:2729` |

**口径**：O 形式、常数不载明；最坏族与 100 路径模式见 §6.27。**12× 桥**：1 Sym 步 = 1 个 4F4 块（12 相位）；Sym 层与 CBTM 层步数换算经 `project_*`/`iso_*` 件（§4.3）。

**存量件**：R14 表级组 / 走带族 / 转向件（素材，非主链）；窗口件（StepBound）。

**公理足迹注**：全链累计公理 = 3 标准（`propext`/`Classical.choice`/`Quot.sound`）+ 既有①线 `native_decide` 继承足迹；新件不新增（约定 10）。全库**声明公理 = 0**。
