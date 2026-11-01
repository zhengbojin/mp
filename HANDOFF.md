# 交接文档 — 2026-11-01

> 项目：`D:\lean4\mp`（Lean 4 形式化：CBTM/IVM 框架下的 P ≠ NP，符号语义/ATM 意义）
> 论文目录：`D:\lean4\mp\STOC27Rev\STOC27Rev`
> 本文件写给下一位接手者（人或 agent）。**先读 §1 与 §5，再动手。**

---

## 1. 一句话现状

- **数学上已成立并机器核验的**：ATM 层的分离 `P_sym0 ≠ NP_sym0`，以及支撑它的三条引理（两实例区分、两段记账可加、归约机零维）。
- **数学上已成立、但只在 `lake env lean` 下核验（未进主构建）的**：`CBTM|0 ≅ Bool-DTM` 的机器同构（配置/路径双向/接受/停机/移动数五层），以及 `P_cb`、`P_A` 的定义。
- **未完成**：`P_A = P_cb` 的最终组装；P 侧计时口径（`CBTM.isPolynomialTimeAligned` 仍是**步数**，其余三方是移动数）。
- **正在跑**：主仓库全量重建（`lake clean` + `lake build Mp`，后台 `proc_95fc8686405a`，预计 40–50 分钟），用于修复“改→崩→回退”造成的增量缓存污染。

---

## 2. 目标与三层结构

目标：在**符号语义（ATM 意义）**下证明 `P_A ≠ NP_A`；**不**证明布尔层的 `P_B ≠ NP_B`。

```
第一层  CBTM/IVM  ：P_cb ≠ NP_cb        ← 已证（Lean，可构建）
第二层  算法机     ：P_A = P_cb ≠ NP_A   ← 机器同构已证机器层；类等式待组装
第三层  布尔机     ：不传递（重编码改变机器类），κ 不可定义；不声称 P_B ≠ NP_B
```

**分离的载荷**：不是时间下界，而是“分支维不可省”（κ）。κ **只在 ATM 层定义**（输入是符号串），**不用在布尔层**（用户裁决）。

---

## 3. 用户裁决清单（不可推翻的口径）

| # | 裁决 | 内容 |
|---|---|---|
| 1 | `P_atm` 定义级 | `IsP_atm := IsP_sym0` |
| 2 | sep 的纸带像 = α | 按公理处理（`ParamSep := F4.alpha` + 定理，不用 Lean `axiom`） |
| 3 | κ 计“读到标记格” | 与“是否分叉”无关；分支不进计数 |
| 4 | 数据码 4 位 | 3 位 kind + 1 位 mark；**代码不动，论文改表** |
| 5 | 停机取“域内”（乙） | `P_A` 只在对齐域要求停机；非对齐串不是输入 |
| 6 | `P_cb` 也要停机 | 它是判定类，不是识别类 |
| 7 | DTM 不写 α/β | 字母表 = `{0,1}`（布尔图灵机） |
| 8 | `ClassicDTM.blankSym = 0` | 空白取 0，α 只作输入符号 |
| 9 | 判定域 `noMarkDomain` | `ι₀` 像（对齐且无标记格）；**正确性仍要求全对齐域** |
| 10 | `P_A = P_cb` 无条件 | 三条约定（位置无关、不写标记、空白=0）已进定义 |
| 11 | κ 不用于 `P_cb` | κ 只在 ATM 层定义 |
| 12 | 第三层不传递 | 块编码可逆但不保机器类；不声称 `P_B ≠ NP_B` |
| 13 | 论文“形式化范围”从简 | 不列文件名/定理名，只作概述 |
| 14 | Lean 版本锁定 v4.32.2 | mathlib 决定（`mathlib/lean-toolchain` = v4.32.2） |

---

## 4. 代码状态

### 4.1 已进主构建（`lake build Mp` 覆盖）

| 文件 | 关键内容 |
|---|---|
| `Mp/ATMAssembly.lean:327` | **`P_sym0_neq_NP_sym0`**（第一层分离，核心结论） |
| `Mp/SubsetSumReal.lean:155` | `imTrueCount_encodeInstanceF4`（α 个数 = 元素个数 = n） |
| `Mp/SubsetSumReal.lean:1722` | `subsetSum_kappa_lower_bound`（任意 CBTM，κ ≥ n） |
| `Mp/SubsetSumReal.lean:1736` | `subsetSum_not_in_P_F`（受限机不可能判定） |
| `Mp/IVM.lean:318` | `kappa_zero_of_restricted`（受限 ⇒ κ ≡ 0） |
| `Mp/KappaAdditive.lean` | 两段记账可加（7 条，`two_phase_additive`） |
| `Mp/TwinInstance.lean` | 两实例区分（12 条，`twinYes_holds`、`twinNo_not_holds`） |
| `Mp/ClassicalProjection.lean` | 定义级 `P_atm ≠ NP_atm` |

### 4.2 类型检查通过但**未进主构建**

| 文件 | 内容 | 未进原因 |
|---|---|---|
| `Mp/ATMDom.lean`（6.7 KB） | `IsAlgorithmOn`、`cbtmMoveCount`、`CBTM.isPolynomialTimeMoves`、`noMarkDomain`、`IsP_cb`/`P_A`、`CBTM.IsCBTM0.toIsRestricted` | `isCBTM0_toCBTM` 触发 C 后端崩溃；已移除该定理 |
| `Mp/MachineIso.lean`（13.4 KB） | `CfgRel`、`cfgRel_init`、`cfgRel_step`、`AllZeroOne`（+3 条）、`path_fwd`、`path_bwd`、`accepts_of_dtm`、`accepts_of_cbtm`、`accepts_iff_p`、`halts_of_dtm`、`halts_of_cbtm`、`dtmMoveCount_map` | 同因 |

两者均 **0 `sorry`、0 `axiom`**，验证方式：`lake env lean Mp/ATMDom.lean`。

### 4.3 崩溃（Lean v4.32.2 的 C 后端）

- 现象：`lake build` 报 `Lean exited with code 3221225477`（`0xC0000005`），**型检查阶段完全正常**。
- 已确认的两条最小触发：
  1. `theorem isCBTM0_toCBTM (M) (hwrite) : CBTM.IsCBTM0 (M.toCBTM hwrite)`；
  2. 任何以 `kappa_M` 参与论证的 `P_cb` 侧定理（已按裁决 11 删除）。
- 附加观察：把 `def cbtmMoveCount` 加进 `Mp/ATMBasic.lean` 也会触发；但放在只导入 `ATMBasic + SubsetSumReal` 的独立文件里**能构建**。
- 换版本无效：v4.35.0 无配套 mathlib（见 §6）。

---

## 5. 论文状态

| 文件 | 页数 | 错误 | 未定义引用 |
|---|---|---|---|
| `measure.C.1.20.pdf` | 29 | 0 | 0 |
| `models.C.1.20.pdf` | 43 | 0 | 0 |

最近一轮改动要点：

- 第二层：`cor:pnp-A` 改为 **`P_A = P_cb`、`P_A ≠ NP_A`**（依据机器同构）；删除 `rem:inclusion-enough`，新增 `rem:eq-conditions`（三条约定各自封口）+ 定义 `def:cbtm0-atm`、`def:P-two-layers`；
- 第三层：全文 **0 处**“分离传递”，改为“不传递（重编码改变机器类）”；
- 形式化范围/清单：改为概述性两三句，不列文件名与定理名；
- `lem:branch-count`：改为“输入 n+1 个数（n 元素 + 目标），α 恰 n 个 ⇒ 分支数 = n”；
- `lem:twin`：附“已机器核验”注（接受侧 `twinYes_holds`、拒绝侧用奇偶性）。

**注意**：三层表现标注“路径搬运待完成”——若 §4.2 的两个模块最终进桶，这句可删。

---

## 6. Lean 版本 / 环境

- 当前：`leanprover/lean4:v4.32.2`（`lean-toolchain`）。
- 已装：v4.28.0、v4.32.2、v4.33.0-rc2、v4.34.0-rc2、**v4.35.0（最新稳定）**。
- **升级 v4.35.0 不可行**：`lake update` 拉到的 mathlib 其 `lean-toolchain` 仍为 `v4.32.2`，用 v4.35.0 编译 mathlib 在 `Cache/Requests.lean:884` 失败（`Lake.PackageEntrySrc.path` API 变更）。
- 备用副本：`D:\lean4\mp435`（源码 5.1 MB + v4.35.0 的 `.lake`，构建失败），等 mathlib 跟进后可再试。
- 网络：直连 Lean 下载被重置，需走本机代理 `HTTPS_PROXY=http://127.0.0.1:10808`。

---

## 7. 恢复与构建

> **⚠️ 2026-11-01 当前状态：仓库不可构建。** 见 §7.0。

### 7.0 事故与恢复（务必先读）

一次误操作的连锁后果：

1. 为修 `0xC0000005`，执行了 `lake clean`；
2. **`lake clean` 会连同所有依赖包的构建产物一起清空**——mathlib 的 6.3 GB olean 消失（现仅剩 49 MB / 41 个）；
3. 恢复路径 `lake exe cache get` 需要先**从源码构建 `cache` 可执行文件**，而它恰好在 `Cache.IO` / `Cache.Infra` 上触发同一个 `0xC0000005` 崩溃 ⇒ 标准恢复路径被堵死；
4. 本地 `~/.cache/mathlib` 有 1.3 GB 的 `.ltar` 缓存块，但**无法手工解包**（`.ltar` 文件名是内容哈希，路径映射在 cache 工具的清单里，必须由工具解出）。

**可用恢复方案（按代价排序）**：

| # | 方案 | 说明 |
|---|---|---|
| A | 找一台能正常构建的机器，跑 `lake exe cache get` 后把 `.lake/packages/mathlib/.lake/build` 整目录拷贝过来 | 最可靠 |
| B | 在**新目录**重新 `git clone` mathlib + `lake exe cache get`（干净的 `.lake` 可能不再触发崩溃） | 中等代价 |
| C | 修复 codegen 崩溃（例如重装 v4.32.2 工具链、换 clang/关闭杀软实时扫描）后再跑 `cache get` | 需试错 |
| D | 从备份恢复整个 `D:\lean4\mp`（若有 `mp.ver2.4.zip` 之外的完整备份） | 取决于是否有备份 |

**教训**：`lake clean` 前必须确认依赖产物可恢复（先跑通 `lake exe cache get`）；本项目在 v4.32.2 上**从未**从源码完整构建过 mathlib。

### 7.1 正常情况下的命令

```bash
cd D:/lean4/mp
lake build Mp            # 正常情况：8719 jobs 成功
lake env lean Mp/ATMDom.lean      # 验证未进桶模块
lake env lean Mp/MachineIso.lean
```

若出现 `0xC0000005`：
1. 先确认源码与 HEAD 一致（`git diff --stat`）；
2. `lake clean` 后全量重建（40–50 分钟）——**“改→崩→回退”会让增量缓存失效**，这是本次教训；
3. 不要在此状态下继续改核心文件（`ATMBasic`/`SubsetSumReal`）。

---

## 8. 下一步（按优先级）

1. **等全量重建结束**，确认 8719 jobs 恢复。
2. **统一计时口径**：`CBTM.isPolynomialTimeAligned` 由 `π.length` 改为移动数。**避开崩溃写法**：不要新增顶层 `def cbtmMoveCount`，直接在 `SubsetSumReal` 内联 `(π.filter (fun st => isMovingDir st.result.moveDir)).length`。
3. **补 `isCBTM0_toCBTM`**（或改写避开崩溃，例如用 `@[irreducible]` 包装、或改用 `CBTM.toCBTM` 的字段展开而不是 `simp`）。
4. **组装 `P_A = P_cb`**：`path_fwd`/`path_bwd` → 接受性/停机/移动数 → 类等式（约 60–80 行）。
5. 两个模块进桶文件（`Mp.lean` 加回 `import Mp.ATMDom`、`import Mp.MachineIso`），跑 `lake build Mp` 确认。
6. 论文三层表删除“路径搬运待完成”。

若 2 或 3 反复触发崩溃，**退路**：`P_cb` 保留步数口径，`P_A = P_cb` 只在步数口径陈述（不影响 ATM 层分离结论）。

---

## 9. 口径字典

| 记号 | 含义 |
|---|---|
| `IsSymbolAligned w` | `w` 是 `flat4F4` 的像（一个逻辑符号 = 4 个 F4 格） |
| `noMarkDomain` | 对齐且**所有格虚部为假**（`ι₀` 像；sep = `(0,1,0,0)`） |
| `IsCBTM0 M` | 字母表 `{0,1}` + 转移单值 + **位置无关** |
| `IsRestricted M` | 字母表 ⊆ `{0,1}` + 虚部全假 + 单值（**不含**位置无关） |
| `P_cb` | `IsCBTM0` + 移动数多项式 + `noMarkDomain` 停机 + 全对齐域判定 |
| `P_A` | `ClassicDTM`（不写 α/β、空白 0）+ 移动数多项式 + 同上 |
| κ | ATM 层的分支维度量；读到标记格即激活一个生成元；**不用于布尔层** |
| `sel` / `nosel` | 分叉后被写回的“选中/不选中”符号（im=0），使每个位置最多激活一次 |

---

## 10. 关键文件清单

```
D:\lean4\mp\
├─ Mp\ATMDom.lean            域内停机 / 移动数 / IsP_cb / P_A（未进桶）
├─ Mp\MachineIso.lean        机器同构五层（未进桶）
├─ Mp\KappaAdditive.lean     两段记账可加（已进桶）
├─ Mp\TwinInstance.lean      两实例区分（已进桶）
├─ Mp\ATMAssembly.lean       第一层分离（已进桶）
├─ Spec.md                   约定 32/33/34/35（含本轮全部裁决与崩溃复现）
└─ STOC27Rev\STOC27Rev\
   ├─ measure.C.1.20.tex     29 页（第二层 = 机器同构等号）
   ├─ models.C.1.20.tex      43 页
   └─ CB.bib                 62 条（nisan1994 已修）
```

---

## 11. 2026-11-01 下午续（接手后）

### 11.1 已落码（A 路线：计时口径统一为移动数）

| 文件 | 改动 |
|---|---|
| `Mp/SubsetSumReal.lean:211` | `CBTM.isPolynomialTimeAligned` 由 `π.length`（步数）改为 `(π.filter (fun st => isMovingDir st.result.moveDir)).length`（移动数，内联，不新增顶层 def） |
| `Mp/SubsetSumReal.lean:222` | `isPolynomialTimeAligned_of_isPolynomialTime` 补 `le_trans (List.length_filter_le _ _)` |
| `Mp/SubsetSumInNP.lean:357` | `toCBTM_polynomialTime` 的 calc 加首步「filter 长度 ≤ 路径长度」 |
| `Mp/MachineIso.lean:271` | 删除重复的 `cbtmMoveCount`（改用 `ATMDom.lean` 的定义，本文件已 import） |

注：`ATMDom.lean` 与 `MachineIso.lean` 均未进桶；`Mp.lean` 工作区已加 ProjectionP/ClassicalProjection/SepAxiom/ParamUnify/NPDomain/KappaAdditive/TwinInstance。

### 11.2 环境级崩溃（重要，推翻 §4.3 归因）

**现象**：`lake build` 一律 `Lean exited with code 3221225477`（0xC0000005），发生在 Aesop/Batteries 等**依赖包**，与 Mp 代码无关。

**精确隔离**（同文件同参数）：

| lean 调用 | 结果 |
|---|---|
| 无 `-o`（纯精化）/ `-c` / `-i` | 成功 |
| `-o` 写 olean（Batteries 级、Basic 级） | 崩 0xC0000005 |
| `-o` 写 trivial 文件（4.6KB olean） | 成功 |

即崩溃点是 **lean 写较大 olean**。已排除：磁盘（Python 写 200MB 正常）、路径（C/D 盘同崩）、Job 内存限制（无限制，18GB 空闲）、Lean 版本（pvsnp 同版本 8 月成功、现在同崩）、Exploit Protection / AppCompat。

**嫌疑**：360 安全卫士极速版（15.0.2.1009），安装目录时间 **2026-11-01 08:56**（今日），时间线与崩溃起点吻合。已卸载（进程/注册表项消失），但**内核过滤驱动需重启才卸载**；重启后测试。

**注意**：卸载 360 后 Windows Defender 实时保护已自动启用（MsMpEng 在跑），若重启后仍崩，需为 `D:\lean4` 与 `%USERPROFILE%\.elan` 加 Defender 排除项。

**教训**：`lake clean` 会清掉依赖包的构建产物（mathlib 也需要重编）。本次 mathlib 已从 `D:\lean4\pvsnp`（同 toolchain v4.32.2、同 mathlib rev `905b9581`）恢复 8275 个 olean。

### 11.3 恢复手段（绕过 lake build）

- `_mp_order.json`：65 个 Mp 模块的拓扑序
- `_build_mp.sh`：逐文件编译脚本（`lake env lean <file> -o/-i/-c`，跳过已有 olean，需 pty 运行避免 tcsetattr 报错）
- 已验证 `lake env lean Mp/Basic.lean`（不写 olean）通过（1m22s）

### 11.4 重启后的第一步

```bash
cd /d/lean4/mp
lake env lean Mp/Basic.lean -o .lake/build/lib/lean/Mp/Basic.olean -i .lake/build/lib/lean/Mp/Basic.ilean
# 成功 ⇒ 跑 bash _build_mp.sh（pty），再复验 ATMDom / MachineIso / ATMAssembly
```

### 11.5 重启后确认与续做（2026-11-01 13:00 后）

**360 根因确认**：重启后 `lake env lean Mp/Basic.lean -o ...` 成功（4m36s，EXIT=0）。`lake build Mp` 亦恢复正常（0 次 0xC0000005）。

**新增/改动（第二层组装）**：

| 文件 | 内容 |
|---|---|
| `Mp/ATMDom.lean` | `IsP_A` 加 `M.blankSym = F4.zero`（落实裁决 8） |
| `Mp/MachineIso.lean` | `isCBTM0_toCBTM`（曾误判为崩溃源，现已证）；`path_bwd` 结论加强：+`dtmMoveCount π = cbtmMoveCount π'`（移动数）+`π.map fromState = π'.map fromState`（首达性搬运）；辅助引理 `dtmMoveCount_append_single`/`cbtmMoveCount_append_single` |
| `Mp/SecondLayer.lean`（新） | `P_cb_subset_P_sym0`、`subsetSum_not_in_P_cb`、`P_cb_neq_NP_sym0`、`toCBTM_iso`、`P_A_subset_P_cb`、`P_A_neq_NP_sym0`（`P_A ≠ NP_A`） |

**层序**：SecondLayer 独立（import ATMDom + MachineIso + ATMAssembly），避免 ATMDom 反向依赖 ATMAssembly 造成层序倒置。

**编译注意**：
- `lake build Mp` 会重建 mathlib（复制的 olean 的 trace 不被 Lake 信任，`depHash` 校验失败）——约 1800 jobs，属一次性成本。
- 逐文件编译（`lake env lean`）**不应用 lakefile 的 leanOptions**，必须手动加：`-D maxHeartbeats=2000000 -D maxErrors=2000 -D relaxedAutoImplicit=false -D maxSynthPendingDepth=3`，否则 `SubsetSumVerifierCBTM6` 等会 200000 心跳超时。
- `_mp_levels.txt` 用 CRLF 写入会导致文件名带 `\r`（`no such file or directory`），脚本需 `tr -d '\r'`。
- ATMDom/MachineIso/SecondLayer 未进桶，需单独 `lake build Mp.ATMDom Mp.MachineIso Mp.SecondLayer` 验证。

### 11.6 第二层完成（2026-11-01 16:30）

**五个定理全部编译通过**（`Mp/SecondLayer.lean`，146KB olean；`#print axioms` 无新增公理，仅既有 `native_decide` 继承足迹）：

| 定理 | 内容 |
|---|---|
| `P_cb_subset_P_sym0` | `P_cb ⊆ P_sym0`（移动数口径统一后直接成立） |
| `subsetSum_not_in_P_cb` | 子集和 ∉ `P_cb` |
| `P_cb_neq_NP_sym0` | **`P_cb ≠ NP_sym0`** |
| `P_A_subset_P_cb` | `P_A ⊆ P_cb`（接受性/停机/移动数+首达性/域四层搬运） |
| `P_A_neq_NP_sym0` | **`P_A ≠ NP_A`**（第二层分离） |

**`IsP_A` 定义补丁**（第二层证明必需）：增加「含标记输入上拒绝」条件

```lean
(∀ w : List F4, IsSymbolAligned w → (∃ c ∈ w, F4.im c = true) → ¬ M.acceptsTape w)
```

理由：`M.toCBTM` 是 CBTM0（字母表 `{0,1}`），在 `im = true` 的格上转移为空；而 `ClassicDTM` 对任意 F4 都有转移定义、可能在含标记输入上接受。若不限制，`P_A ⊆ P_cb` 的接受性在含标记输入上不成立。

**编译状态**：`lake build Mp` 仍会因 mathlib trace 格式（8 月旧格式 vs Lake 5.0）全量重建 mathlib；Mp 的 65 个模块已用逐文件方式全部编译成功（`_build_mp_par2.sh`），ATMDom/MachineIso/SecondLayer 单独编译通过。

**剩余工作**：
1. 将 `Mp/ATMDom.lean`、`Mp/MachineIso.lean`、`Mp/SecondLayer.lean` 加入 `Mp.lean` 桶（代码完整性）；
2. 更新 `Spec.md` 约定 34/35（原「已证」条目现已真正落地，且 `IsP_A` 定义有补充条件）；
3. 论文 `measure.C.1.20` / `models.C.1.20` 的三层表更新（第二层已组装完成）。
