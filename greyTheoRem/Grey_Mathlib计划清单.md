# GreySystem mathlib PR 计划清单（整理版）

> 更新时间：2026-03-28
> 角色：执行清单（不是理论母本）
> 上游理论母本：greyTheoRem/灰色理论参考_整理提纲.md

## 1. 文档用途

本文件只做三件事：

1. 固定 mathlib PR 的边界与约束。
2. 记录当前仓库的真实执行状态。
3. 维护下一阶段可直接开工的任务。

不在本文件做的事：

1. 不重复保存大段理论摘录。
2. 不做研究层公理证明规划。
3. 不作为历史过程流水账。

## 2. 不变硬约束

1. 严禁证明现有 axiom。
2. 允许整理 axiom 的样式、命名、注释、分组与文件位置。
3. 允许把依赖 axiom 的内容移出 PR 候选。
4. 验证样例、演示代码、占位实现、调试内容不进入首轮 PR。
5. 不把整个 GreySystem 作为大而全框架直接投 PR。

## 3. 分层边界（固定）

### 3.1 首轮候选层（Core + A1-A6）

1. GrayNumber.lean
2. GrayOperations.lean
3. GrayAlgebraLemmas.lean
4. GrayAxiomInterfaces.lean（A1-A4, A6 接口层）
5. GrayOperationAxioms.lean（A5 基础约束）

### 3.2 第二轮仓库层（Research/Repository）

1. GrayAxioms.lean
2. GrayBufferAxioms.lean
3. GrayOperationAxioms.lean
4. GrayAxiomsTheorems.lean
5. GraySequenceLemmas.lean
6. GrayRepositoryStructures.lean
7. GrayProvedTheorems.lean
8. GrayAdvanced.lean
9. GrayExamples.lean
10. GraySecondRound.lean（聚合入口）

### 3.3 入口策略

1. GreySystem.lean：最小公共入口（不导入验证层）。
2. GraySecondRound.lean：第二轮聚合入口。

## 4. 当前状态快照（已核对）

1. 全仓 lake build 通过。
2. 首轮候选三文件已形成独立基础层。
3. 第二轮聚合入口已纳入 lakefile roots。
4. 研究层与仓库层边界说明已统一。
5. GrayAdvanced.lean 头部已清理为模块文档并带第二轮边界说明。
6. GraySequenceLemmas.lean 已完成仓库层减噪（移除 second_order_awbo 占位条目）。

## 5. 首轮 PR 最终对外清单（定稿）

### 5.1 文件范围

1. GrayNumber.lean
2. GrayOperations.lean
3. GrayAlgebraLemmas.lean
4. GrayAxiomInterfaces.lean
5. GrayOperationAxioms.lean

### 5.2 对外声明最小集

1. GrayNumber / greyness_interval / greyness_interval_range / mk_interval_gray_number
2. gray_eq / gray_add / gray_neg / gray_sub / gray_mul / gray_inv / gray_div / gray_smul
3. gray_eq_refl / gray_eq_symm / gray_eq_trans
4. zero_gray / one_gray
5. gray_add_comm / gray_add_assoc / gray_add_zero / zero_gray_add / gray_add_neg
6. gray_mul_comm / gray_mul_assoc / one_gray_mul / gray_mul_one
7. gray_left_distrib / gray_right_distrib
8. white_gray_add_equal_greyness / white_gray_mul_equal_greyness / white_gray_sub_equal_greyness / white_gray_div_equal_greyness

### 5.3 明确不进入首轮 PR

1. A7-A9 及其后的研究公理文件。
2. 全部研究依赖定理文件。
3. 序列仓库层与包装层。
4. 高级探索层与样例层。

## 6. 第1-3轮分批提交说明模板（当前仓库）

使用规则：

1. 每批只做一个边界目标，不混入跨轮改造。
2. 每批完成后先跑对应最小验证命令，再跑全仓验证。
3. 任何批次都不引入“证明现有 axiom”的改动。

---

### Round 1（核心层 + A1-A6）

#### R1-B1：基础对象层

文件：

1. GrayNumber.lean

边界：

1. 只允许 GrayNumber 及其直接定义/基础引理改动。
2. 不引入 research/repository 层依赖。

验证命令：

```bash
lake build GrayNumber
```

#### R1-B2：基础运算层

文件：

1. GrayOperations.lean

边界：

1. 只处理 gray_add/sub/mul/div 等基础运算与无公理依赖性质。
2. 禁止引入研究公理文件依赖。

验证命令：

```bash
lake build GrayOperations
```

#### R1-B3：代数引理层

文件：

1. GrayAlgebraLemmas.lean

边界：

1. 仅保留可直接建立在 Round 1 基础层之上的引理。
2. 发现 research 依赖时移出本批，不在本批补公理证明。

验证命令：

```bash
lake build GrayAlgebraLemmas
lake build GreySystem
```

---

### Round 2（Research/Repository 主体层）

#### R2-B1：研究公理层

文件：

1. GrayAxioms.lean
2. GrayBufferAxioms.lean
3. GrayOperationAxioms.lean

边界：

1. 允许注释、命名、结构、分组整理。
2. 严禁新增“为现有 axiom 补证明”的内容。

验证命令：

```bash
lake build GrayAxioms GrayBufferAxioms GrayOperationAxioms
```

#### R2-B2：研究定理与序列仓库层

文件：

1. GrayAxiomsTheorems.lean
2. GraySequenceLemmas.lean
3. GraySequenceCoreLemmas.lean

边界：

1. 仅做研究层定理组织与仓库层可维护性整理。
2. 不把该批声明为首轮可上游 API。

验证命令：

```bash
lake build GrayAxiomsTheorems GraySequenceCoreLemmas GraySequenceLemmas
```

#### R2-B3：仓库包装与第二轮聚合入口

文件：

1. GrayRepositoryStructures.lean
2. GrayProvedTheorems.lean
3. GraySecondRound.lean

边界：

1. 保持第二轮聚合语义，避免反向污染 Round 1 最小入口。
2. 仅做包装/聚合与边界文档一致性修改。

验证命令：

```bash
lake build GrayRepositoryStructures GrayProvedTheorems GraySecondRound
```

---

### Round 3（接口/入口/示例稳定化层）

#### R3-B1：接口与扩展桥接层

文件：

1. GrayAxiomInterfaces.lean
2. GrayBasicExtensions.lean
3. GrayIntervalOperations.lean

边界：

1. 仅做“接口抽象 + 基础扩展 + 区间运算桥接”。
2. 不新增跨层耦合，不改 Round 1 对外最小 API 边界。

验证命令：

```bash
lake build GrayAxiomInterfaces GrayBasicExtensions GrayIntervalOperations
```

#### R3-B2：样例与高级探索层

文件：

1. GrayAdvanced.lean
2. GrayExamples.lean
3. GrayResearchOperations.lean

边界：

1. 作为演示/研究辅助层，不并入首轮候选。
2. 允许文档化整理与边界声明统一。

验证命令：

```bash
lake build GrayAdvanced GrayExamples GrayResearchOperations
```

#### R3-B3：入口与构建配置收口

文件：

1. GreySystem.lean
2. lakefile.lean
3. greyTheoRem/Grey_Mathlib计划清单.md

边界：

1. 只做入口最小化、roots 同步与计划文档同步。
2. 不在本批进行理论层新增。

验证命令：

```bash
lake build GreySystem
lake build
```

---

### 全轮次统一验收命令（每批末尾附加）

```bash
lake build
```

## 7. 命名空间策略（当前决定）

1. 第三轮不引入统一 namespace。
2. 维持首轮候选 API 稳定，避免破坏式改名影响首轮 PR。
3. 如需统一 namespace，放到后续独立破坏性整理批次。

## 8. 状态同步规则（唯一真值）

1. 本文件即执行真值，不再维护多处重复看板。
2. 新任务先写入本文件，再开始代码改动。
3. 状态更新只改“当前状态快照”和“下一步任务”，不改历史叙述。
4. 与其他文档冲突时，以本文件为执行基准、以上游提纲为理论基准。

## 9. Round 4 交付包（本次产出）

### P0-1：首轮 PR 对外提交文本最终版（英文，可直接粘贴 GitHub）

#### PR Title（可直接粘贴）

```text
feat(gray-core): Round1 core extraction with foundational A1-A6 baseline
```

#### PR Body（可直接粘贴）

```markdown
## Summary

This PR prepares the first-round, mathlib-facing extraction of GreySystem by
landing the minimal core API together with the foundational A1-A6 baseline.

## Included in this round

Core modules:
- `GrayNumber.lean`
- `GrayOperations.lean`
- `GrayAlgebraLemmas.lean`

Foundational axiom layer (A1-A6):
- `GrayAxiomInterfaces.lean` (A1-A4 and A6-facing interfaces)
- `GrayOperationAxioms.lean` (A5-A6 foundational constraints)

## Scope boundary

Included:
- Core gray-number object, operations, and foundational algebra lemmas.
- Interface/axiom baseline for A1-A6 required by current GreySystem round-1 policy.

Not included:
- A7-A9 and sequence-buffer research axioms.
- Research-dependent theorem bundles and repository packaging layers.
- Advanced exploratory/examples/validation-only modules.

## Design intent

This keeps review focused on a stable and explicit first-round surface:
1. Core API users can depend on a small, auditable base.
2. A1-A6 assumptions are made explicit now (rather than hidden downstream).
3. Research-heavy layers remain isolated for later rounds.
4. A6 is now materialized as `general_gray_mul_nondec`/`general_gray_div_nondec` and exported via `IsGrayMulDivGreynessNondec` instance.

## Validation

- `lake build GrayNumber`
- `lake build GrayOperations`
- `lake build GrayAlgebraLemmas`
- `lake build GrayAxiomInterfaces`
- `lake build GrayOperationAxioms`
- `lake build GreySystem`
- `lake build`

## Checklist

- [x] Round1 file scope matches plan document.
- [x] A1-A6 boundary is explicit in module/docs comments.
- [x] Build passes for affected modules and full workspace.
- [x] No attempt to prove existing research axioms.
```

### P0-2：首轮 staged commit 草稿（5 文件，3 commits）

#### Commit 1（核心对象与运算）

```bash
git add GrayNumber.lean GrayOperations.lean
git commit -m "feat(gray-core): extract round1 core object and operations"
```

建议提交说明（正文）：

```text
- Land GrayNumber and GrayOperations as the round1 computational core.
- Keep signatures stable for downstream algebra/interface layers.
- Preserve explicit split between core API and research theorem bundles.
```

#### Commit 2（核心引理层）

```bash
git add GrayAlgebraLemmas.lean
git commit -m "feat(gray-core): add foundational algebra lemmas for round1"
```

建议提交说明（正文）：

```text
- Add foundational algebraic laws used by round1 core APIs.
- Keep theorem surface small and reviewable.
- Maintain compatibility with existing downstream wrappers.
```

#### Commit 3（A1-A6 基线）

```bash
git add GrayAxiomInterfaces.lean GrayOperationAxioms.lean
git commit -m "feat(gray-core): include foundational A1-A6 baseline in round1"
```

建议提交说明（正文）：

```text
- Include A1-A4/A6 interfaces in GrayAxiomInterfaces.
- Include A5-A6 foundational constraints in GrayOperationAxioms.
- Keep A7-A9 and higher research layers deferred to later rounds.
```

### P0-3：GraySequenceCoreLemmas 可提炼候选可行性验证（1-2 条）

已执行验证：

```bash
lake build GraySequenceCoreLemmas
```

结果：通过。

候选 A（低风险，优先）：

1. `rule_ago1`
2. 提炼理由：纯展开型 `rfl` 定理，不依赖 research axiom，接口稳定。

候选 B（中风险，可后续）：

1. `monotonic_increasing_transitive`
2. 提炼理由：证明自包含、复用价值高（已被 `GraySequenceLemmas` 与 `GrayExamples` 直接使用）。
3. 风险点：命名和表述可能需泛化（例如向更通用单调框架靠拢）。

结论：

1. 本轮建议先提炼候选 A。
2. 候选 B 进入下一批“命名/泛化评审后提炼”。

### P1-1：GrayProvedTheorems / GrayRepositoryStructures 别名淘汰路线图

当前别名现状：

1. `GrayRepositoryStructures.lean`
2. 别名：`gray_numbers_form_gray_field` -> `exists_gray_add_sub_mul_div`
3. 别名：`gray_numbers_form_gray_linear_space` -> `gray_linear_space_laws_of_white`

阶段化淘汰：

1. 阶段 T0（当前）：保留 `@[deprecated ...]`，允许旧调用继续通过。
2. 阶段 T1（下个迭代）：全仓替换旧名调用到新名，CI 增加“禁止新增旧名引用”检查。
3. 阶段 T2（稳定期后）：删除别名声明，仅保留新名。

执行命令模板：

```bash
grep -R "gray_numbers_form_gray_field\|gray_numbers_form_gray_linear_space" .
```

### P1-2：第二轮模块声明级注释语气统一（已完成）

统一目标语气：

1. 明确“repository-side second-round mathlib PR preparation scope”。
2. 明确“not first-round axiom-free extraction layer”。

已统一文件：

1. GrayAxioms.lean
2. GrayBufferAxioms.lean
3. GrayOperationAxioms.lean
4. GrayAxiomsTheorems.lean
5. GrayRepositoryStructures.lean
6. GrayProvedTheorems.lean
7. GrayAdvanced.lean
8. GrayExamples.lean

## 10. 提交前检查模板

```bash
git diff --staged --stat
git diff --staged
lake build
```

## 11. 公理分解执行状态（本次已落实）

### 11.1 Round 1 剥离与关系切断（完成）

1. 首轮提交范围固定为：`GrayNumber.lean`、`GrayOperations.lean`、`GrayAlgebraLemmas.lean`、`GrayAxiomInterfaces.lean`、`GrayOperationAxioms.lean`。
2. A1-A6 作为基础公理直接纳入首轮；A7-A9 与其后研究层继续保留在第二/三轮。
3. 对外说明更新为：首轮导出核心层 + A1-A6 基础公理，研究扩展层继续后置。

### 11.2 Round 2 接口化+最小公理（完成一轮落地）

1. `GrayAxiomInterfaces.lean` 新增 `IsGraySystemOp`，用于承接 `greyness_non_decreasing` 的接口化迁移。
2. 新增仅依赖接口的示例定理：`white_union_ge_right_of_interface`。
3. `GrayAxiomsTheorems.lean` 新增接口版定理：`white_union_ge_right_interface`，作为“从重公理迁移到接口约束”的样例。

### 11.3 Round 3 研究层 API 过渡（完成一轮落地）

1. 将可计算组件从 `GrayBufferAxioms.lean` 提炼至 `GraySequenceCoreLemmas.lean`：
2. `average_growth_rate`
3. `buffer_operator_growth_rate`
4. `GrayBufferAxioms.lean` 改为复用提炼后的定义与定理，保留研究公理层职责。

### 11.4 可证明基础点（已确认）

1. 序列侧可证明候选：`rule_ago1`、`rule_step_ratio`、`rule_smooth_ratio`、`monotonic_increasing_transitive`、`monotonic_increasing_ge`。
2. 灰数运算侧可证明候选：`gray_add_comm`、`gray_mul_comm`、`gray_left_distrib` 等（位于 `GrayAlgebraLemmas.lean`）。

### 11.5 底层公理追踪器（已建立）

1. `GrayAxioms.lean` 已对每条 `axiom` 增加 `[AxiomTrack]` 标签。
2. 标签维度：`round1=include(A1-A6)/exclude`、`round2=interface-target/keep-research`、`split=high/medium/low`。

### 11.6 当前 axiom 数量（声明级）

统计命令（环境无 `rg`，使用 `grep`）：

```bash
grep -hE "^axiom[[:space:]]" GrayAxioms*.lean GrayBufferAxioms.lean GrayOperationAxioms.lean GrayAxiomsTheorems.lean | wc -l
```

结果：

1. 声明级 `axiom` 总数为 `35`。

## 12. 35 条 Axiom 分批 Sprint 拆单表（逐条）

策略标签说明：

1. 保留：继续作为研究层假设，留在 Round 2/3。
2. 接口化：目标替换为 `class`/`instance` 约束（如 `IsGraySystemOp`、`IsGrayA1A4`）。
3. 可拆证明：可向 `GraySequenceCoreLemmas`/首轮候选层拆出可证明子结论。

### Sprint S1（优先级 P0）：核心接口化切口

| ID | 文件 | Axiom | 处理策略 | 说明 |
|---|---|---|---|---|
| 1 | GrayAxioms | greyness_non_decreasing | 接口化 | 迁移目标：`IsGraySystemOp` |
| 2 | GrayAxioms | union_greyness_property | 接口化 | 对齐 `IsGrayA1A4.union_lower` 风格 |
| 3 | GrayOperationAxioms | general_gray_add_nonneg | 接口化 | 可进入 `IsGrayAddSubGreynessComposite` 约束族 |
| 4 | GrayOperationAxioms | general_gray_add_le_one | 接口化 | 与上条成对处理 |

### Sprint S2（优先级 P1）：序列算子基础层

| ID | 文件 | Axiom | 处理策略 | 说明 |
|---|---|---|---|---|
| 5 | GrayAxioms | sequence_operator_fixed_point | 可拆证明 | 与 `buffer_operator_growth_rate` 联动 |
| 6 | GrayAxioms | sequence_operator_information | 保留 | 语义性强，先保留 |
| 7 | GrayAxioms | sequence_operator_expression | 保留 | 语义性强，先保留 |
| 8 | GrayAxioms | rule_agor | 可拆证明 | 可先拆递推基例/小阶引理 |
| 9 | GrayAxioms | step_smooth_ratio_relation | 可拆证明 | 与 `rule_step_ratio`/`rule_smooth_ratio` 结合 |
| 10 | GrayAxioms | increasing_sequence_step_ratio_range | 可拆证明 | 可先拆有限区间单调子结论 |

### Sprint S3（优先级 P1）：区间-灰数桥接

| ID | 文件 | Axiom | 处理策略 | 说明 |
|---|---|---|---|---|
| 11 | GrayAxioms | union_greyness_equality | 保留 | 条件复杂，先保留研究层 |
| 12 | GrayAxioms | bijection_interval_gray | 可拆证明 | 先拆单向正确性（左逆/右逆分开） |

### Sprint S4（优先级 P2）：指数规律研究块

| ID | 文件 | Axiom | 处理策略 | 说明 |
|---|---|---|---|---|
| 13 | GrayAxioms | homogeneous_exponential_detection | 保留 | 偏研究型等价命题 |
| 14 | GrayAxioms | nonnegative_quasi_smooth_ago_exponential | 保留 | 误差界研究结论 |
| 15 | GrayAxioms | multi_order_ago_exponential | 保留 | 高阶 AGO 研究结论 |

### Sprint S5（优先级 P2）：预处理与归一化

| ID | 文件 | Axiom | 处理策略 | 说明 |
|---|---|---|---|---|
| 16 | GrayAxioms | translation_transform_positive | 可拆证明 | 可从 list 不等式工具先拆子引理 |
| 17 | GrayAxioms | range_normalization_in_interval | 可拆证明 | 可拆上下界分别证明 |
| 18 | GrayAxioms | range_normalization_inverse_correct | 保留 | 先保留，后续需函数反演细化 |

### Sprint S6（优先级 P1）：Buffer 总性质接口化

| ID | 文件 | Axiom | 处理策略 | 说明 |
|---|---|---|---|---|
| 19 | GrayBufferAxioms | weakening_buffer_operator_property | 接口化 | 迁移为 `WeakenOp` 类约束 |
| 20 | GrayBufferAxioms | strengthening_buffer_operator_property | 接口化 | 迁移为 `StrengthenOp` 类约束 |
| 21 | GrayBufferAxioms | buffer_operator_fluctuation_property | 保留 | 先作为研究层总性质 |

### Sprint S7（优先级 P1）：单调/波动序列块

| ID | 文件 | Axiom | 处理策略 | 说明 |
|---|---|---|---|---|
| 22 | GrayBufferAxioms | monotonic_increasing_buffer_properties | 可拆证明 | 与单调引理库结合 |
| 23 | GrayBufferAxioms | monotonic_decreasing_buffer_properties | 可拆证明 | 与上条对偶拆分 |
| 24 | GrayBufferAxioms | fluctuating_buffer_properties | 保留 | 波动范围估计先保留 |

### Sprint S8（优先级 P2）：构造算子分类块

| ID | 文件 | Axiom | 处理策略 | 说明 |
|---|---|---|---|---|
| 25 | GrayBufferAxioms | awbo_is_weakening_operator | 接口化 | 先做算子类实例壳 |
| 26 | GrayBufferAxioms | wawbo_is_weakening_operator | 接口化 | 同上 |
| 27 | GrayBufferAxioms | wgawbo_is_weakening_operator | 接口化 | 同上 |
| 28 | GrayBufferAxioms | esbo_is_strengthening_operator | 接口化 | 强化算子接口实例 |
| 29 | GrayBufferAxioms | asbo_is_strengthening_operator | 接口化 | 强化算子接口实例 |
| 30 | GrayBufferAxioms | wasbo_is_strengthening_operator | 接口化 | 强化算子接口实例 |
| 31 | GrayBufferAxioms | gfbo_negative_is_weakening | 接口化 | 参数化符号条件接口化 |
| 32 | GrayBufferAxioms | gfbo_positive_is_strengthening | 接口化 | 参数化符号条件接口化 |

### Sprint S9（优先级 P2）：特例等价关系块

| ID | 文件 | Axiom | 处理策略 | 说明 |
|---|---|---|---|---|
| 33 | GrayBufferAxioms | awbo_is_special_wawbo | 可拆证明 | 常量权重特例可优先拆 |
| 34 | GrayBufferAxioms | wawbo_is_special_gfbo | 保留 | 依赖非零条件较重，先保留 |
| 35 | GrayBufferAxioms | wasbo_is_special_gfbo | 可拆证明 | α=1 特例可先行证明 |

### Sprint 执行顺序建议

1. 先做 S1 + S2（打通接口化主链与序列可证链）。
2. 再做 S6 + S7（缓冲算子语义层）。
3. 最后处理 S3/S4/S5/S8/S9（研究深水区与特例关系）。

### 当前三条执行指令落实状态（2026-03-28）

1. 按“无直接依赖/弱依赖”优先抽离（T16 起步）：已落实。
2. 新增 `GraySequenceCoreLemmas.iago1_ago1_cancel`，作为 T16 的首个 axiom-free 抽离结果。
3. 按“强绑定”保持研究层（T17-T19）：已落实。
4. T17/T18/T19 继续绑定到研究公理链（G9-G13），不并入首轮候选层。
5. 按“接口化”推进替换（T1/T4/T5）：已落实一轮。
6. 在 `GrayAxiomsTheorems.lean` 新增接口替代定理：
7. `union_inter_bounds_interface`（T1 风格替代）
8. `same_greyness_mul_lower_bound_interface`（T4 风格替代）
9. `white_gray_op_greyness_ge_interface`（T5 风格替代）

### Sprint 执行状态看板（mathlib PR 风格）

| Sprint | 范围 | 当前状态 | 已落地产物 | 验收命令 |
|---|---|---|---|---|
| S1 | 核心接口化（ID 1-4） | 已完成（接口化第一阶段） | `IsGraySystemOp`；`union_inter_bounds_interface`；`white_gray_op_greyness_ge_interface`；`same_greyness_mul_lower_bound_interface`；`add_greyness_nonneg`；`add_greyness_le_one`；`sub_greyness_nonneg`；`sub_greyness_le_one` | `lake build GrayAxiomInterfaces GrayAxiomsTheorems` |
| S2 | 序列算子基础（ID 5-10） | 已完成（可拆证明第一批） | `average_growth_rate`、`buffer_operator_growth_rate`、`iago1_ago1_cancel`；`sequence_operator_fixed_point_at`；`rule_agor_zero`；`rule_agor_succ`；`step_ratio_eq_inv_smooth_ratio`；`increasing_sequence_step_ratio_ge_one_at` | `lake build GraySequenceCoreLemmas GrayAxiomsTheorems` |
| S3 | 区间-灰数桥接（ID 11-12） | 已完成（按既定策略） | `bijection_interval_gray_left`；`bijection_interval_gray_right`；`union_greyness_lower_bound`；`union_greyness_exact_under_subset`（ID 11 保持研究层公理） | `lake build GrayAxiomsTheorems` |
| S4 | 指数规律研究块（ID 13-15） | 已完成（按既定策略） | `homogeneous_exponential_detection_iff`；`homogeneous_exponential_detection_forward`；`homogeneous_exponential_detection_backward`；`nonnegative_quasi_smooth_ago_exponential_exists`；`nonnegative_quasi_smooth_ago_exponential_unpack`；`multi_order_ago_exponential_exists`；`exponential_law_bundle`（ID 13-15 保持研究层公理，不进入首轮） | `lake build GrayAxiomsTheorems GrayAxioms` |
| S5 | 预处理与归一化（ID 16-18） | 已完成（按既定策略） | `translation_transform_positive_member`；`range_normalization_lower_bound`；`range_normalization_upper_bound`；`range_normalization_bounds_bundle`；`range_normalization_inverse_correct_wrapper`（ID 18 保持研究层公理） | `lake build GrayAxiomsTheorems` |
| S6 | Buffer 总性质接口化（ID 19-21） | 已完成（按既定策略） | `IsWeakeningBufferFamily`；`IsStrengtheningBufferFamily`；`weakening_buffer_property_at`；`strengthening_buffer_property_at`；`buffer_fluctuation_max_side`；`buffer_fluctuation_min_side`（ID 21 保持研究层公理） | `lake build GrayAxiomInterfaces GrayAxiomsTheorems GrayBufferAxioms` |
| S7 | 单调/波动序列（ID 22-24） | 已完成（按既定策略） | `monotonic_increasing_awbo_ge`；`monotonic_increasing_strengthening_le`；`monotonic_decreasing_awbo_le`；`monotonic_decreasing_strengthening_ge`；`monotonic_increasing_buffer_properties_bundle`；`monotonic_decreasing_buffer_properties_bundle`；`fluctuating_awbo_amplitude_le`；`fluctuating_strengthening_amplitude_ge`；`fluctuating_buffer_properties_bundle`（ID 24 保持研究层公理） | `lake build GrayAxiomsTheorems GrayBufferAxioms` |
| S8 | 构造算子分类（ID 25-32） | 已完成（按既定策略） | `IsWeightedWeakeningBufferFamily`；`IsWeightedStrengtheningBufferFamily`；`IsGeneralizedBufferBySign`；`wawbo_is_weighted_weakening_family`；`wgawbo_is_weighted_weakening_family`；`esbo_is_strengthening_family`；`asbo_is_strengthening_family`；`wasbo_is_weighted_strengthening_family`；`gfbo_is_generalized_buffer_by_sign`；`wawbo_weakening_at`；`wgawbo_weakening_at`；`esbo_strengthening_at`；`asbo_strengthening_at`；`wasbo_strengthening_at`；`gfbo_negative_weaken_at`；`gfbo_positive_strengthen_at` | `lake build GrayAxiomInterfaces GrayAxiomsTheorems GrayBufferAxioms` |
| S9 | 特例等价关系（ID 33-35） | 已完成（按既定策略） | `IsBufferSpecialization`；`IsStrengtheningBufferSpecialization`；`awbo_wawbo_gfbo_specialization`；`wasbo_gfbo_specialization`；`awbo_eq_wawbo_unit_weights`；`wawbo_eq_gfbo_neg_one`；`wasbo_eq_gfbo_one`；`buffer_specialization_bundle`（ID 34 保持研究层公理） | `lake build GrayAxiomsTheorems GrayBufferAxioms` |

### 本轮“全力完成”执行结果

1. S1 + S2：已完成，接口主链与序列可证链均已落地。
2. S6 + S7：已完成，缓冲算子语义层按既定策略收口（接口化 + 研究层包装并行）。
3. S3/S4/S5/S8/S9：S3/S4/S5/S8/S9 已完成并按既定策略收口；S4 以“研究层封装”方式完成，不进入首轮。


下面是可直接粘贴到 PR 描述的 35 条逐条状态清单。

1. ID 1 | axiom: greyness_non_decreasing | 策略: 接口化完成 | 对应 wrapper/instance: IsGraySystemOp, white_gray_op_greyness_ge_interface | 构建命令: lake build GrayAxiomInterfaces GrayAxiomsTheorems  
2. ID 2 | axiom: union_greyness_property | 策略: 接口化完成 | 对应 wrapper/instance: IsGrayA1A4, union_inter_bounds_interface | 构建命令: lake build GrayAxiomInterfaces GrayAxiomsTheorems  
3. ID 3 | axiom: general_gray_add_nonneg | 策略: 接口化完成 | 对应 wrapper/instance: IsGrayAddSubGreynessComposite, add_greyness_nonneg | 构建命令: lake build GrayAxiomInterfaces GrayAxiomsTheorems  
4. ID 4 | axiom: general_gray_add_le_one | 策略: 接口化完成 | 对应 wrapper/instance: IsGrayAddSubGreynessComposite, add_greyness_le_one | 构建命令: lake build GrayAxiomInterfaces GrayAxiomsTheorems  

5. ID 5 | axiom: sequence_operator_fixed_point | 策略: 可拆证明包装完成 | 对应 wrapper/instance: sequence_operator_fixed_point_at | 构建命令: lake build GrayAxiomsTheorems  
6. ID 6 | axiom: sequence_operator_information | 策略: 保留研究层（按策略） | 对应 wrapper/instance: 无单独 wrapper，作为研究层条件保留 | 构建命令: lake build GrayAxioms  
7. ID 7 | axiom: sequence_operator_expression | 策略: 保留研究层（按策略） | 对应 wrapper/instance: 无单独 wrapper，作为研究层条件保留 | 构建命令: lake build GrayAxioms  
8. ID 8 | axiom: rule_agor | 策略: 可拆证明包装完成 | 对应 wrapper/instance: rule_agor_zero, rule_agor_succ | 构建命令: lake build GrayAxiomsTheorems  
9. ID 9 | axiom: step_smooth_ratio_relation | 策略: 可拆证明包装完成 | 对应 wrapper/instance: step_ratio_eq_inv_smooth_ratio | 构建命令: lake build GrayAxiomsTheorems  
10. ID 10 | axiom: increasing_sequence_step_ratio_range | 策略: 可拆证明包装完成 | 对应 wrapper/instance: increasing_sequence_step_ratio_ge_one_at | 构建命令: lake build GrayAxiomsTheorems  

11. ID 11 | axiom: union_greyness_equality | 策略: 保留研究层并封装完成 | 对应 wrapper/instance: union_greyness_exact_under_subset | 构建命令: lake build GrayAxiomsTheorems  
12. ID 12 | axiom: bijection_interval_gray | 策略: 可拆证明包装完成 | 对应 wrapper/instance: bijection_interval_gray_left, bijection_interval_gray_right | 构建命令: lake build GrayAxiomsTheorems  

13. ID 13 | axiom: homogeneous_exponential_detection | 策略: 保留研究层并封装完成 | 对应 wrapper/instance: homogeneous_exponential_detection_iff, homogeneous_exponential_detection_forward, homogeneous_exponential_detection_backward | 构建命令: lake build GrayAxiomsTheorems GrayAxioms  
14. ID 14 | axiom: nonnegative_quasi_smooth_ago_exponential | 策略: 保留研究层并封装完成 | 对应 wrapper/instance: nonnegative_quasi_smooth_ago_exponential_exists, nonnegative_quasi_smooth_ago_exponential_unpack | 构建命令: lake build GrayAxiomsTheorems GrayAxioms  
15. ID 15 | axiom: multi_order_ago_exponential | 策略: 保留研究层并封装完成 | 对应 wrapper/instance: multi_order_ago_exponential_exists, exponential_law_bundle | 构建命令: lake build GrayAxiomsTheorems GrayAxioms  

16. ID 16 | axiom: translation_transform_positive | 策略: 可拆证明包装完成 | 对应 wrapper/instance: translation_transform_positive_member | 构建命令: lake build GrayAxiomsTheorems  
17. ID 17 | axiom: range_normalization_in_interval | 策略: 可拆证明包装完成 | 对应 wrapper/instance: range_normalization_lower_bound, range_normalization_upper_bound, range_normalization_bounds_bundle | 构建命令: lake build GrayAxiomsTheorems  
18. ID 18 | axiom: range_normalization_inverse_correct | 策略: 保留研究层并封装完成 | 对应 wrapper/instance: range_normalization_inverse_correct_wrapper | 构建命令: lake build GrayAxiomsTheorems  

19. ID 19 | axiom: weakening_buffer_operator_property | 策略: 接口化完成 | 对应 wrapper/instance: IsWeakeningBufferFamily, weakening_buffer_is_weakening_family, weakening_buffer_property_at | 构建命令: lake build GrayAxiomInterfaces GrayAxiomsTheorems GrayBufferAxioms  
20. ID 20 | axiom: strengthening_buffer_operator_property | 策略: 接口化完成 | 对应 wrapper/instance: IsStrengtheningBufferFamily, strengthening_buffer_is_strengthening_family, strengthening_buffer_property_at | 构建命令: lake build GrayAxiomInterfaces GrayAxiomsTheorems GrayBufferAxioms  
21. ID 21 | axiom: buffer_operator_fluctuation_property | 策略: 保留研究层并封装完成 | 对应 wrapper/instance: buffer_fluctuation_max_side, buffer_fluctuation_min_side | 构建命令: lake build GrayAxiomsTheorems GrayBufferAxioms  

22. ID 22 | axiom: monotonic_increasing_buffer_properties | 策略: 可拆证明包装完成 | 对应 wrapper/instance: monotonic_increasing_awbo_ge, monotonic_increasing_strengthening_le, monotonic_increasing_buffer_properties_bundle | 构建命令: lake build GrayAxiomsTheorems GrayBufferAxioms  
23. ID 23 | axiom: monotonic_decreasing_buffer_properties | 策略: 可拆证明包装完成 | 对应 wrapper/instance: monotonic_decreasing_awbo_le, monotonic_decreasing_strengthening_ge, monotonic_decreasing_buffer_properties_bundle | 构建命令: lake build GrayAxiomsTheorems GrayBufferAxioms  
24. ID 24 | axiom: fluctuating_buffer_properties | 策略: 保留研究层并封装完成 | 对应 wrapper/instance: fluctuating_awbo_amplitude_le, fluctuating_strengthening_amplitude_ge, fluctuating_buffer_properties_bundle | 构建命令: lake build GrayAxiomsTheorems GrayBufferAxioms  

25. ID 25 | axiom: awbo_is_weakening_operator | 策略: 接口化完成 | 对应 wrapper/instance: awbo_is_weakening_family | 构建命令: lake build GrayAxiomInterfaces GrayAxiomsTheorems GrayBufferAxioms  
26. ID 26 | axiom: wawbo_is_weakening_operator | 策略: 接口化完成 | 对应 wrapper/instance: IsWeightedWeakeningBufferFamily, wawbo_is_weighted_weakening_family, wawbo_weakening_at | 构建命令: lake build GrayAxiomInterfaces GrayAxiomsTheorems GrayBufferAxioms  
27. ID 27 | axiom: wgawbo_is_weakening_operator | 策略: 接口化完成 | 对应 wrapper/instance: IsWeightedWeakeningBufferFamily, wgawbo_is_weighted_weakening_family, wgawbo_weakening_at | 构建命令: lake build GrayAxiomInterfaces GrayAxiomsTheorems GrayBufferAxioms  
28. ID 28 | axiom: esbo_is_strengthening_operator | 策略: 接口化完成 | 对应 wrapper/instance: IsStrengtheningBufferFamily, esbo_is_strengthening_family, esbo_strengthening_at | 构建命令: lake build GrayAxiomInterfaces GrayAxiomsTheorems GrayBufferAxioms  
29. ID 29 | axiom: asbo_is_strengthening_operator | 策略: 接口化完成 | 对应 wrapper/instance: IsStrengtheningBufferFamily, asbo_is_strengthening_family, asbo_strengthening_at | 构建命令: lake build GrayAxiomInterfaces GrayAxiomsTheorems GrayBufferAxioms  
30. ID 30 | axiom: wasbo_is_strengthening_operator | 策略: 接口化完成 | 对应 wrapper/instance: IsWeightedStrengtheningBufferFamily, wasbo_is_weighted_strengthening_family, wasbo_strengthening_at | 构建命令: lake build GrayAxiomInterfaces GrayAxiomsTheorems GrayBufferAxioms  
31. ID 31 | axiom: gfbo_negative_is_weakening | 策略: 接口化完成 | 对应 wrapper/instance: IsGeneralizedBufferBySign, gfbo_is_generalized_buffer_by_sign, gfbo_negative_weaken_at | 构建命令: lake build GrayAxiomInterfaces GrayAxiomsTheorems GrayBufferAxioms  
32. ID 32 | axiom: gfbo_positive_is_strengthening | 策略: 接口化完成 | 对应 wrapper/instance: IsGeneralizedBufferBySign, gfbo_is_generalized_buffer_by_sign, gfbo_positive_strengthen_at | 构建命令: lake build GrayAxiomInterfaces GrayAxiomsTheorems GrayBufferAxioms  

33. ID 33 | axiom: awbo_is_special_wawbo | 策略: 可拆证明包装完成 | 对应 wrapper/instance: awbo_eq_wawbo_unit_weights, buffer_specialization_bundle | 构建命令: lake build GrayAxiomsTheorems GrayBufferAxioms  
34. ID 34 | axiom: wawbo_is_special_gfbo | 策略: 保留研究层并封装完成 | 对应 wrapper/instance: wawbo_eq_gfbo_neg_one, buffer_specialization_bundle | 构建命令: lake build GrayAxiomsTheorems GrayBufferAxioms  
35. ID 35 | axiom: wasbo_is_special_gfbo | 策略: 可拆证明包装完成 | 对应 wrapper/instance: wasbo_eq_gfbo_one, buffer_specialization_bundle | 构建命令: lake build GrayAxiomsTheorems GrayBufferAxioms  

可附一行总验收命令：lake build