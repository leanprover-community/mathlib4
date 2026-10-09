# Powerset.lean 读后笔记


---

## 记号与语法速查

| 记号 | 含义 |
|---|---|
| `Finset α` | α 的有限集合。内部结构是 `{ val : Multiset α, nodup : val.Nodup }`，即"一个可重复的表 + 一张无重复证明" |
| `s.1` | `s` 的底层 Multiset |
| `s.2` | `s` 的无重复证明 |
| `#s` | `Finset.card s`，元素个数 |
| `⊆` / `⊂` | 子集 / 真子集（`t ⊂ s` 定义为 `t ⊆ s ∧ t ≠ s`） |
| `∅` `∪` `∩` `\` | 空集、并、交、差 |
| `⟨a, b⟩` | 构造结构体的两个字段，这里是 `(val, nodup)` |
| `↔` | 当且仅当 |
| `∈` | 属于 |
| `[DecidableEq α]` | 类型类，表示"能判断 α 的两个元素是否相等"。与`erase`、`\`、`∩`、`insert`、`filter`、`image` 等需要去重的操作相关 |
| `by` | 后面是证明脚本 |
| `simp` / `grind` / `aesop` / `ext` / `lia` | 自动化策略。`ext` 用"逐元素相等"证集合相等；`lia` 处理自然数线性算术 |
| `@[simp]` | 把定理登记进 `simp` 的重写规则库 |
| `variable` / `section` / `namespace` | 变量声明、段落范围、命名空间 |

`mem_powerset` 这个名字在 `Multiset` 与 `Finset` 两个命名空间里都有定义，
Lean 按参数类型自动选择用哪一个。

---

## 一、文件的主要结论

### 1. 成员与格的刻画

```lean
@[simp, grind =] theorem mem_powerset : s ∈ powerset t ↔ s ⊆ t   -- 行 37
```

`s` 属于 `t` 的幂集，当且仅当 `s` 是 `t` 的子集。文件其余定理大多把命题化归到这里。

其他结论：`powerset_mono`（行 57，`s ⊆ t ⟺ powerset s ⊆ powerset t`）、
`powerset_injective` 与 `powerset_inj`（行 61、65，幂集运算保序且单射）、
`coe_powerset`（行 43，与 `Set.powerset` 的对应关系）、
`mem_ssubsets`（行 160）、`mem_powersetCard`（行 202）。

### 2. 计数公式

| 结论 | 公式 | 行 |
|---|---|---|
| 子集总数 | `#(powerset s) = 2 ^ #s` | 103 |
| n 元子集个数 | `#(powersetCard n s) = Nat.choose #s n` | 212 |
| 含固定子集 s 的 n 元子集个数 | `= Nat.choose (#t - #s) (n - #s)` | 234 |
| 该子集族的集合形式 | `((t \ s).powersetCard (n - #s)).image (· ∪ s)` | 218 |
| 为空 / 非空的条件 | `= ∅ ⟺ #s < n`；`非空 ⟺ n ≤ #s` | 264 / 292 |
| n = #s 时 | `powersetCard #s s = {s}` | 299 |

行 218 与 234 的做法是：把必选的 `s` 先取出，从 `t \ s` 中取 `n - #s` 个元素，再并上 `s`。

### 3. 按基数分层与由子集族还原集合

- 行 321 `powerset_card_disjiUnion`：`powerset s` 等于各 `powersetCard i s`（`i < #s + 1`）的无交并。
  不同基数的子集层两两不交，由 `disjoint_powersetCard_of_ne`（行 312）与
  `pairwise_disjoint_powersetCard`（行 316）给出。
- 行 354 `powersetCard_biUnion`：`r ≠ 0` 且 `r ≤ #s` 时，全体 `r` 元子集的并等于 `s`。
- 行 362 `eq_of_powersetCard_eq`：`#a = #b`、`r ≠ 0`、`r ≤ #a`，且
  `a.powersetCard r = b.powersetCard r` 时，`a = b`。
- 行 369 `powersetCard_injOn`：在基数为 `q` 的集合族上，`a ↦ a.powersetCard r` 是单射（`1 ≤ r ≤ q`）。

后两条说明：等势的两个有限集合由它们的全体 `r` 元子集唯一确定。

### 4. 与映射、插入运算的关系

- 行 97 `powerset_image`：`(s.image f).powerset = s.powerset.image (·.image f)`，不需要 `f` 单射。
- 行 76 `image_injOn_powerset_of_injOn`：`f` 在 `s` 上 `InjOn` 时，`(·.image f)` 在 `s.powerset` 上 `InjOn`。
- 行 93 `image_surjOn_powerset`：`(·.image f)` 从 `s.powerset` 满射到 `(s.image f).powerset`。
- 行 111 `powerset_insert` 与行 285 `powersetCard_succ_insert`：加入新元素后，子集分为含该元素与不含该元素两类。

---

## 二、Lean 中的写法

**1. `Finset` 由 `Multiset` 与 `Nodup` 证明组成，定义幂集时用 `pmap` 补齐证明。**

```lean
def powerset (s : Finset α) : Finset (Finset α) :=
  ⟨(s.1.powerset.pmap Finset.mk) fun _t h => nodup_of_le (mem_powerset.1 h) s.nodup,
    s.nodup.powerset.pmap fun _a _ha _b _hb => congr_arg Finset.val⟩
```

- `s.1` 是底层 `Multiset`；`Multiset.powerset` 来自 `Mathlib.Data.Multiset.Powerset`。
- 第一分量用 `pmap Finset.mk` 给每个子 Multiset 配上无重复证明（`nodup_of_le`：子 Multiset 继承母体的 `Nodup`）。
- 第二分量证明幂集本身无重复，用 `congr_arg Finset.val`：两个 `Finset` 相等当且仅当底层 `Multiset` 相等，证明部分无关。
- 定义不依赖 `[DecidableEq α]`，因为无重复性由证明携带，无需执行去重。

**2. 真子集定义为从幂集中删去自身。**

```lean
def ssubsets (s : Finset α) := erase (powerset s) s    -- 行 156
theorem mem_ssubsets : t ∈ s.ssubsets ↔ t ⊂ s          -- 行 160
```

`⊂` 在 Lean 中为 `⊆ 且 ≠`（`ssubset_iff_subset_ne`）。

**3. 合并子集族用 `biUnion id` 或 `sup id`。**

`Finset α` 带有以 `⊆` 为序、`∅` 为底的格结构，`sup_eq_biUnion` 连接二者。
`powersetCard_sup` 用 `sup id = u` 表示全体 `n+1` 元子集的并为 `u`。

**4. 单射与满射用 `Set.InjOn` / `Set.SurjOn`。**

`(·.image f)` 仅在幂集这一子集族上单射，对全体 `Finset α` 不成立，故不使用全局 `Injective`。
`powersetCard_map`（行 373）改用嵌入 `α ↪ β`，嵌入自带单射性，无需 `DecidableEq`。

**5. 有界量词的可判定性。**

文件给出 4 个 `instance`，把 `∃ t ⊆ s, p t` 改写为 `∃ t ∈ s.powerset, …`，后者是在有限集合上取量词，因而可判定。

**6. 自动化标签。**

`[simp]`（`simp` 可用）、`grind =`（注册给 `grind`）、`[norm_cast]`（在 `Finset` 与 `Set` 之间转换）、
`[gcongr]`（单调性参与 `gcongr`）、`[aesop safe apply]`（自动证明 `Nonempty`）。
`mem_powerset`、`mem_ssubsets`、`mem_powersetCard` 带有 `[simp, grind =]`。

---

## 三、各假设的使用位置

### 类型类

| 假设 | 出现的定理 | 原因 | 使用位置 |
|---|---|---|---|
| `[DecidableEq α]` | `SSubsets` 整段（行 153） | `erase` 需要比较元素 | `ssubsets = erase (powerset s) s` |
| `[DecidableEq α]` | `powerset_insert`(111)、`powersetCard_succ_insert`(285) | `insert`、`image` | 递推式的两支 |
| `[DecidableEq α]` | `pairwiseDisjoint_pair_insert`(117) | `insert a t` | 构造 `{t, insert a t}` |
| `[DecidableEq α]` | `biUnion_id_subset_iff_subset_powerset`(89)、`powersetCard_sup`(338)、`powersetCard_biUnion`(354) | `biUnion` 折叠 `∪`，需要去重 | `sup_eq_biUnion`、`u.erase x` |
| `[DecidableEq α]` | `filter_powersetCard_subset`(218)、`card_filter_powersetCard_subset`(234) | `t \ s`、`∪`、`filter` | `card_sdiff_of_subset`、`disjoint_sdiff_self_left` |
| `[DecidableEq α]` | `powersetCard_inter`(272)、`disjoint_powersetCard_powersetCard`(276) | `∩` | `subset_inter_iff` |
| `[DecidableEq β]` | 76、93、97 | `Finset.image` 需要去重 | `(·.image f)`、`s.image f` |
| `[DecidableEq (Finset α)]` | `powerset_card_biUnion`(334) | 外层 `biUnion` 的元素为 `Finset α` | 由 `disjiUnion_eq_biUnion` 得到 |
| `f : α ↪ β` | `powersetCard_map`(373) | 嵌入自带单射性 | `map f (filter ...)`、`card_map` |

`powerset_image`（行 97）显式给出 `[DecidableEq β]`，外层 `image` 所需的 `DecidableEq (Finset α)` 由类型类推断提供；自行复现时可显式写出 `[DecidableEq α]` 或使用 `classical`。

### 项级假设

| 定理（行） | 假设 | 使用位置 |
|---|---|---|
| `image_injOn_powerset_of_injOn`(76) | `H : Set.InjOn f s` | 行 78 用 `H.eq_iff` 证 `a ∈ z ↔ f a ∈ z.image f`；行 79 由成员等价推出子集相等 |
| `injOn_image_of_biUnion_injOn`(83) | `hf : (S.biUnion id : Set α).InjOn f` | 代入上一条（取 `s := S.biUnion id`），行 86 用 `.mono` 把定义域缩到 `S` |
| `notMem_of_mem_powerset_of_notMem`(106) | `ht`、`h` | `mt _ h` 与 `mem_powerset.1 ht : t ⊆ s` |
| `pairwiseDisjoint_pair_insert`(117) | `ha : a ∉ s` | 行 123 `insert_erase_invOn.2.injOn (notMem_mono hi ha) (notMem_mono hj ha)`；末两行用 `Finset.notMem_mono ‹_› ha (mem_insert_self _ _)` 排除 `t = insert a t` |
| `filter_powersetCard_subset`(218) | `hst : s ⊆ t` | 反方向行 228 `union_subset (hyt.trans sdiff_subset) hst` |
| 同上 | `hsn : #s ≤ n` | 行 230 `lia`：`rw` 后目标为 `n - #s + #s = n` |
| `card_filter_powersetCard_subset`(234) | `hst`、`hsn` | `hst` 另用于 `card_sdiff_of_subset hst`；`hsn` 作为前置条件，保证 `n - #s` 与计数公式中的算术成立"。；行 237–242 自造 `hinj`：`(· ∪ s)` 在 `(t \ s).powersetCard (n - #s)` 上单射，用 `union_sdiff_cancel_right` 与 `disjoint_of_subset_left … disjoint_sdiff_self_left` |
| `powersetCard_sup`(338) | `hn : n < u.card` | 行 347–348 `powersetCard_nonempty.2 (le_trans (Nat.le_sub_one_of_lt hn) pred_card_le_card_erase)`，即证 `n ≤ #(u.erase x)`，其中 `pred_card_le_card_erase` 需要 `hx : x ∈ u` |
| `powersetCard_biUnion`(354) | `hr : r ≠ 0` | 行 356 `Nat.exists_eq_succ_of_ne_zero hr`，把 `r` 写成 `n.succ` |
| 同上 | `hrs : r ≤ #s` | 行 358 传给 `powersetCard_sup` 作为 `hn : n < #s` |
| `eq_of_powersetCard_eq`(362) | `hab : #a = #b` | 行 366 `simpa [..., ← hab, hra]`，把右端所需的 `r ≤ #b` 改写为 `r ≤ #a` |
| 同上 | `hr₀ : r ≠ 0`、`hra : r ≤ #a` | 左右两端 `powersetCard_biUnion` 的条件 |
| 同上 | `h : a.powersetCard r = b.powersetCard r` | 行 366 `congr(($h).biUnion id)` |
| 同上 | `classical`（行 365） | 提供 `DecidableEq α` 与谓词可判定性 |
| `powersetCard_injOn`(369) | `hr₀`、`hrq : r ≤ q` | 行 371 交给 `eq_of_powersetCard_eq hbq.symm hr₀ hrq h`；`hbq.symm` 充当 `hab`，因匹配 `rfl : #a = q` 后 `#a` 即 `q` |
| `powersetCard_succ_insert`(285) | `h : x ∉ s` | 保证含 `x` 与不含 `x` 两支不重叠；行 288–289 用 `powerset_insert` 与 `filter_union` |
| `Disjoint.powersetCard_powersetCard_finset`(307) | `h : Disjoint s t` | `grind [disjoint_left]`：公共元素既 ⊆ s 又 ⊆ t |
| 同上 | `hn : n ≠ 0 ∨ m ≠ 0` | 排除 `n = m = 0`，此时两层均为 `{∅}`，不不交 |
| `disjoint_powersetCard_of_ne`(312) | `h : m ≠ n` | 公共元素基数同时等于 `m` 与 `n`，矛盾 |
| `powersetCard_mono`(206) | `h : s ⊆ t` | 行 208 `Subset.trans h₂ h` |
| `empty_mem_ssubsets`(163) | `h : s.Nonempty` | `h.ne_empty.symm` 给出 `∅ ≠ s` |
| `powersetCard_card_add`(269) | `hn : 0 < n` | `simpa` 配合 `powersetCard_eq_empty`（`#s < #s + n`） |

---

## 四、主结果所需的假设

**1. 定义与计数部分不依赖 `[DecidableEq α]`。**

`powerset`、`powersetCard` 的定义，`mem_powerset`、`mem_powersetCard`、`card_powerset`、
`card_powersetCard`、`powerset_mono`、`powerset_inj` 均未声明 `[DecidableEq α]`。
这些结论只使用底层 `Multiset` 运算与 `Nodup` 证明，因此适用于任意类型 `α`。

**2. `[DecidableEq]` 按需逐条声明。**

需要它的运算为 `erase`、`\`、`∩`、`insert`、`∪`（含 `biUnion`）、`filter`、`image`。
`section powersetCard` 未声明全局 `variable [DecidableEq α]`，由各定理分别给出；
`section SSubsets` 因整段使用 `erase`，在行 153 整段声明。

**3. 数值条件对应"非空"与"大小足够"。**

- `r ≠ 0`：排除 `powersetCard 0 s = {∅}` 的情形。
- `r ≤ #s`：等价于 `powersetCard_sup` 的 `n < #s`，用于证明删去任一元素后仍存在 `n` 元子集。
- `#a = #b`：使右端满足 `r ≤ #b`。
- `s ⊆ t`：保证并上 `s` 后仍包含于 `t`。
- `#s ≤ n`：保证 `n - #s + #s = n` 成立。

**4. 不交性作为 `disjiUnion` 的参数传入。**

`powerset_card_disjiUnion` 的第三个参数为 `s.pairwise_disjoint_powersetCard.set_pairwise _`，
因此无需 `DecidableEq (Finset α)`；`powerset_card_biUnion`（行 334）由
`disjiUnion_eq_biUnion` 得到，需要 `[DecidableEq (Finset α)]`。

**5. 行 320 与 333 的 `set_option backward.isDefEq.respectTransparency false`。**

该设置与数学内容无关，用于 elaboration：`disjiUnion` 的不交性参数类型与所给证明对齐时，
若展开定义比对会耗时较长，关闭该选项后按不透明常量比较即可通过。

### 主结果的依赖顺序

```
mem_powersetCard        （成员 ↔ 子集 ∧ 基数）
powersetCard_nonempty   （非空 ↔ n ≤ #s）
powersetCard_succ_insert（加入新元素的递推）
        ↓
powersetCard_sup        （hn : n < #u）
        ↓  r = n.succ
powersetCard_biUnion    （hr : r ≠ 0，hrs : r ≤ #s）
        ↓  congr ((h).biUnion id)
eq_of_powersetCard_eq   （hab，hr₀，hra，h）
        ↓
powersetCard_injOn      （在 #a = q 的集合族上单射）
```

---

## 五、可用 API

**定义**：`Finset.powerset`、`Finset.ssubsets`、`Finset.powersetCard`

**成员判定**：`mem_powerset`、`mem_ssubsets`、`mem_powersetCard`、`coe_powerset`、
`empty_mem_powerset`、`mem_powerset_self`、`empty_mem_ssubsets`、`powerset_empty`、
`powerset_eq_singleton_empty`、`powersetCard_zero`、`powersetCard_self`、
`powersetCard_eq_filter`、`powersetCard_eq_empty`、`powersetCard_nonempty`

**单调性与单射性**：`powerset_mono`、`powerset_injective`、`powerset_inj`、
`powersetCard_mono`、`powersetCard_injOn`、`eq_of_powersetCard_eq`

**与映射相关**：`powerset_image`、`image_surjOn_powerset`、`image_injOn_powerset_of_injOn`、
`injOn_image_of_biUnion_injOn`、`powersetCard_map`、`map_val_val_powersetCard`、`powersetCard_one`

**计数**：`card_powerset`、`card_powersetCard`、`card_filter_powersetCard_subset`、
`filter_powersetCard_subset`、`powersetCard_eq_empty`、`powersetCard_nonempty`、`powersetCard_card_add`

**分解与不交性**：`powerset_insert`、`powersetCard_succ_insert`、`pairwiseDisjoint_pair_insert`、
`powersetCard_inter`、`disjoint_powersetCard_powersetCard`、`disjoint_powersetCard_of_ne`、
`Disjoint.powersetCard_powersetCard_finset`、`pairwise_disjoint_powersetCard`、
`powerset_card_disjiUnion`、`powerset_card_biUnion`、`powersetCard_sup`、`powersetCard_biUnion`、
`powersetCard_empty_subsingleton`、`biUnion_id_subset_iff_subset_powerset`、
`notMem_of_mem_powerset_of_notMem`、`powerset_nonempty`

**可判定性**：`decidableExistsOfDecidableSubsets`、`decidableForallOfDecidableSubsets`、
`decidableExistsOfDecidableSubsets'`、`decidableForallOfDecidableSubsets'`（4 个为 `instance`）；
`decidableExistsOfDecidableSSubsets`、`decidableForallOfDecidableSSubsets` 及其 `'` 版本为 `def`，需显式调用。
