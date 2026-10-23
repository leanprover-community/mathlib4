# Powerset.lean Reading Notes  

---

## Notation and Syntax Quick Reference

| Notation | Meaning |
|---|---|
| `Finset α` | Finite set of α. Internal structure is `{ val : Multiset α, nodup : val.Nodup }`, i.e., "a multiset + a proof of no duplicates" |
| `s.1` | The underlying Multiset of `s` |
| `s.2` | The proof of no duplicates of `s` |
| `#s` | `Finset.card s`, the number of elements |
| `⊆` / `⊂` | Subset / Proper subset (`t ⊂ s` is defined as `t ⊆ s ∧ t ≠ s`) |
| `∅` `∪` `∩` `\\` | Empty set, union, intersection, difference |
| `⟨a, b⟩` | Constructs a structure with two fields, here `(val, nodup)` |
| `↔` | If and only if |
| `∈` | Belongs to |
| `[DecidableEq α]` | Type class indicating "can determine whether two elements of α are equal". Relevant for operations requiring deduplication such as `erase`, `\\`, `∩`, `insert`, `filter`, `image` |
| `by` | Followed by a proof script |
| `simp` / `grind` / `aesop` / `ext` / `lia` | Automation tactics. `ext` proves set equality by "element-wise equality"; `lia` handles natural number linear arithmetic |
| `@[simp]` | Registers a theorem into `simp`'s rewriting rule database |
| `variable` / `section` / `namespace` | Variable declarations, section scopes, namespaces |

The name `mem_powerset` is defined in both the `Multiset` and `Finset` namespaces; Lean automatically selects which one to use based on the parameter type.

---

## I. Main Results of the File

### 1. Membership and Lattice Characterization

```lean
@[simp, grind =] theorem mem_powerset : s ∈ powerset t ↔ s ⊆ t   -- line 37
```

`s` belongs to the powerset of `t` if and only if `s` is a subset of `t`. The rest of the theorems in the file mostly reduce propositions to this statement.

Other results: `powerset_mono` (line 57, `s ⊆ t ⟺ powerset s ⊆ powerset t`),
`powerset_injective` and `powerset_inj` (lines 61, 65, the powerset operation is order-preserving and injective),
`coe_powerset` (line 43, correspondence with `Set.powerset`),
`mem_ssubsets` (line 160), `mem_powersetCard` (line 202).

### 2. Counting Formulas

| Result | Formula | Line |
|---|---|---|
| Total number of subsets | `#(powerset s) = 2 ^ #s` | 103 |
| Number of n-element subsets | `#(powersetCard n s) = Nat.choose #s n` | 212 |
| Number of n-element subsets containing a fixed subset s | `= Nat.choose (#t - #s) (n - #s)` | 234 |
| Set form of this subset family | `((t \\ s).powersetCard (n - #s)).image (· ∪ s)` | 218 |
| Conditions for empty / nonempty | `= ∅ ⟺ #s < n`; `nonempty ⟺ n ≤ #s` | 264 / 292 |
| When n = #s | `powersetCard #s s = {s}` | 299 |

The approach at lines 218 and 234: first extract the mandatory `s`, then select `n - #s` elements from `t \\ s`, and finally union with `s`.

### 3. Stratification by Cardinality and Recovering a Set from Its Subset Family

- Line 321 `powerset_card_disjiUnion`: `powerset s` equals the disjoint union of `powersetCard i s` (for `i < #s + 1`).
  Subset layers of different cardinalities are pairwise disjoint, given by `disjoint_powersetCard_of_ne` (line 312) and
  `pairwise_disjoint_powersetCard` (line 316).
- Line 354 `powersetCard_biUnion`: When `r ≠ 0` and `r ≤ #s`, the union of all `r`-element subsets equals `s`.
- Line 362 `eq_of_powersetCard_eq`: If `#a = #b`, `r ≠ 0`, `r ≤ #a`, and
  `a.powersetCard r = b.powersetCard r`, then `a = b`.
- Line 369 `powersetCard_injOn`: On the family of sets of cardinality `q`, the map `a ↦ a.powersetCard r` is injective (for `1 ≤ r ≤ q`).

The last two results indicate that two equinumerous finite sets are uniquely determined by all their `r`-element subsets.

### 4. Relationship with Mapping and Insert Operations

- Line 97 `powerset_image`: `(s.image f).powerset = s.powerset.image (·.image f)`, does not require `f` to be injective.
- Line 76 `image_injOn_powerset_of_injOn`: When `f` is `InjOn` on `s`, `(·.image f)` is `InjOn` on `s.powerset`.
- Line 93 `image_surjOn_powerset`: `(·.image f)` surjects from `s.powerset` onto `(s.image f).powerset`.
- Line 111 `powerset_insert` and line 285 `powersetCard_succ_insert`: After adding a new element, subsets are divided into two categories — those containing the element and those not.

---

## II. Writing Style in Lean

**1. `Finset` consists of a `Multiset` and a `Nodup` proof; when defining the powerset, `pmap` is used to fill in the proofs.**

```lean
def powerset (s : Finset α) : Finset (Finset α) :=
  ⟨(s.1.powerset.pmap Finset.mk) fun _t h => nodup_of_le (mem_powerset.1 h) s.nodup,
    s.nodup.powerset.pmap fun _a _ha _b _hb => congr_arg Finset.val⟩
```

- `s.1` is the underlying `Multiset`; `Multiset.powerset` comes from `Mathlib.Data.Multiset.Powerset`.
- The first component uses `pmap Finset.mk` to attach a no-duplicates proof to each sub-multiset (`nodup_of_le`: the sub-multiset inherits `Nodup` from the parent).
- The second component proves that the powerset itself has no duplicates, using `congr_arg Finset.val`: two `Finset`s are equal iff their underlying `Multiset`s are equal; the proof part is irrelevant.
- The definition does not depend on `[DecidableEq α]`, because non-duplication is carried by proofs and no runtime deduplication is needed.

**2. Proper subsets are defined as the powerset with itself removed.**

```lean
def ssubsets (s : Finset α) := erase (powerset s) s    -- line 156
theorem mem_ssubsets : t ∈ s.ssubsets ↔ t ⊂ s          -- line 160
```

`⊂` in Lean is `⊆ ∧ ≠` (`ssubset_iff_subset_ne`).

**3. Union of subset families uses `biUnion id` or `sup id`.**

`Finset α` carries a lattice structure ordered by `⊆` with `∅` as bottom; `sup_eq_biUnion` connects the two.
`powersetCard_sup` uses `sup id = u` to state that the union of all `n+1`-element subsets equals `u`.

**4. Injectivity and surjectivity use `Set.InjOn` / `Set.SurjOn`.**

`(·.image f)` is injective only on the subset family that is the powerset; it is not injective on all `Finset α`, so the global `Injective` is not used.
`powersetCard_map` (line 373) instead uses an embedding `α ↪ β`, which carries injectivity by itself and does not require `DecidableEq`.

**5. Decidability of bounded quantifiers.**

The file provides 4 `instance`s that rewrite `∃ t ⊆ s, p t` to `∃ t ∈ s.powerset, …`, where the quantifier ranges over a finite set and is therefore decidable.

**6. Automation labels.**

`[simp]` (usable by `simp`), `grind =` (registered for `grind`), `[norm_cast]` (conversion between `Finset` and `Set`),
`[gcongr]` (monotonicity participates in `gcongr`), `[aesop safe apply]` (automatically proves `Nonempty`).
`mem_powerset`, `mem_ssubsets`, `mem_powersetCard` have `[simp, grind =]`.

---

## III. Usage Locations of Each Hypothesis

### Type Classes

| Hypothesis | Theorems Where Used | Reason | Usage Location |
|---|---|---|---|
| `[DecidableEq α]` | Entire `SSubsets` section (line 153) | `erase` needs to compare elements | `ssubsets = erase (powerset s) s` |
| `[DecidableEq α]` | `powerset_insert`(111), `powersetCard_succ_insert`(285) | `insert`, `image` | The two branches of the recurrence |
| `[DecidableEq α]` | `pairwiseDisjoint_pair_insert`(117) | `insert a t` | Constructing `{t, insert a t}` |
| `[DecidableEq α]` | `biUnion_id_subset_iff_subset_powerset`(89), `powersetCard_sup`(338), `powersetCard_biUnion`(354) | `biUnion` folds `∪`, requiring deduplication | `sup_eq_biUnion`, `u.erase x` |
| `[DecidableEq α]` | `filter_powersetCard_subset`(218), `card_filter_powersetCard_subset`(234) | `t \\ s`, `∪`, `filter` | `card_sdiff_of_subset`, `disjoint_sdiff_self_left` |
| `[DecidableEq α]` | `powersetCard_inter`(272), `disjoint_powersetCard_powersetCard`(276) | `∩` | `subset_inter_iff` |
| `[DecidableEq β]` | 76, 93, 97 | `Finset.image` requires deduplication | `(·.image f)`, `s.image f` |
| `[DecidableEq (Finset α)]` | `powerset_card_biUnion`(334) | The outer `biUnion` operates on elements of type `Finset α` | Derived from `disjiUnion_eq_biUnion` |
| `f : α ↪ β` | `powersetCard_map`(373) | Embeddings carry injectivity by themselves | `map f (filter ...)`, `card_map` |

`powerset_image` (line 97) explicitly specifies `[DecidableEq β]`; the `DecidableEq (Finset α)` required by the outer `image` is inferred by type class resolution; when re-implementing, one can explicitly write `[DecidableEq α]` or use `classical`.

### Term-Level Hypotheses

| Theorem (Line) | Hypothesis | Usage Location |
|---|---|---|
| `image_injOn_powerset_of_injOn`(76) | `H : Set.InjOn f s` | Line 78 uses `H.eq_iff` to prove `a ∈ z ↔ f a ∈ z.image f`; line 79 deduces subset equality from membership equivalence |
| `injOn_image_of_biUnion_injOn`(83) | `hf : (S.biUnion id : Set α).InjOn f` | Substitutes into the previous theorem (taking `s := S.biUnion id`); line 86 uses `.mono` to restrict the domain to `S` |
| `notMem_of_mem_powerset_of_notMem`(106) | `ht`, `h` | `mt _ h` with `mem_powerset.1 ht : t ⊆ s` |
| `pairwiseDisjoint_pair_insert`(117) | `ha : a ∉ s` | Line 123 `insert_erase_invOn.2.injOn (notMem_mono hi ha) (notMem_mono hj ha)`; last two lines use `Finset.notMem_mono ‹_› ha (mem_insert_self _ _)` to exclude `t = insert a t` |
| `filter_powersetCard_subset`(218) | `hst : s ⊆ t` | Reverse direction line 228 `union_subset (hyt.trans sdiff_subset) hst` |
| Same | `hsn : #s ≤ n` | Line 230 `lia`: after `rw`, the goal becomes `n - #s + #s = n` |
| `card_filter_powersetCard_subset`(234) | `hst`, `hsn` | `hst` is also used for `card_sdiff_of_subset hst`; `hsn` serves as a precondition ensuring `n - #s` and the arithmetic in the counting formula are valid. Lines 237–242 construct `hinj`: `(· ∪ s)` is injective on `(t \\ s).powersetCard (n - #s)`, using `union_sdiff_cancel_right` and `disjoint_of_subset_left … disjoint_sdiff_self_left` |
| `powersetCard_sup`(338) | `hn : n < u.card` | Lines 347–348 `powersetCard_nonempty.2 (le_trans (Nat.le_sub_one_of_lt hn) pred_card_le_card_erase)`, i.e., proving `n ≤ #(u.erase x)`, where `pred_card_le_card_erase` requires `hx : x ∈ u` |
| `powersetCard_biUnion`(354) | `hr : r ≠ 0` | Line 356 `Nat.exists_eq_succ_of_ne_zero hr`, writing `r` as `n.succ` |
| Same | `hrs : r ≤ #s` | Line 358 passes this to `powersetCard_sup` as `hn : n < #s` |
| `eq_of_powersetCard_eq`(362) | `hab : #a = #b` | Line 366 `simpa [..., ← hab, hra]`, rewriting the required `r ≤ #b` on the right side to `r ≤ #a` |
| Same | `hr₀ : r ≠ 0`, `hra : r ≤ #a` | Conditions for `powersetCard_biUnion` on both sides |
| Same | `h : a.powersetCard r = b.powersetCard r` | Line 366 `congr(($h).biUnion id)` |
| Same | `classical` (line 365) | Provides `DecidableEq α` and decidability of predicates |
| `powersetCard_injOn`(369) | `hr₀`, `hrq : r ≤ q` | Line 371 delegates to `eq_of_powersetCard_eq hbq.symm hr₀ hrq h`; `hbq.symm` serves as `hab`, since after matching `rfl : #a = q`, `#a` is `q` |
| `powersetCard_succ_insert`(285) | `h : x ∉ s` | Ensures the two branches (with and without `x`) do not overlap; lines 288–289 use `powerset_insert` and `filter_union` |
| `Disjoint.powersetCard_powersetCard_finset`(307) | `h : Disjoint s t` | `grind [disjoint_left]`: any common element is both ⊆ s and ⊆ t |
| Same | `hn : n ≠ 0 ∨ m ≠ 0` | Excludes the case `n = m = 0`, where both layers are `{∅}` and are not disjoint |
| `disjoint_powersetCard_of_ne`(312) | `h : m ≠ n` | A common element's cardinality would equal both `m` and `n`, a contradiction |
| `powersetCard_mono`(206) | `h : s ⊆ t` | Line 208 `Subset.trans h₂ h` |
| `empty_mem_ssubsets`(163) | `h : s.Nonempty` | `h.ne_empty.symm` gives `∅ ≠ s` |
| `powersetCard_card_add`(269) | `hn : 0 < n` | `simpa` with `powersetCard_eq_empty` (`#s < #s + n`) |

---

## IV. Hypotheses Required by the Main Results

**1. Definitions and counting do not depend on `[DecidableEq α]`.**

The definitions of `powerset` and `powersetCard`, as well as `mem_powerset`, `mem_powersetCard`, `card_powerset`,
`card_powersetCard`, `powerset_mono`, and `powerset_inj`, do not declare `[DecidableEq α]`.
These results use only the underlying `Multiset` operations and `Nodup` proofs, and thus apply to any type `α`.

**2. `[DecidableEq]` is declared per theorem as needed.**

The operations requiring it are `erase`, `\\`, `∩`, `insert`, `∪` (including `biUnion`), `filter`, and `image`.
The `section powersetCard` does not declare a global `variable [DecidableEq α]`; each theorem provides it individually.
The `section SSubsets` declares it for the entire section at line 153 because the whole section uses `erase`.

**3. Numerical conditions correspond to "nonempty" and "sufficient size".**

- `r ≠ 0`: Excludes the case `powersetCard 0 s = {∅}`.
- `r ≤ #s`: Equivalent to `n < #s` in `powersetCard_sup`, used to prove that after removing any element, there still exists an `n`-element subset.
- `#a = #b`: Ensures the right side satisfies `r ≤ #b`.
- `s ⊆ t`: Guarantees that after unioning with `s`, the result is still contained in `t`.
- `#s ≤ n`: Ensures `n - #s + #s = n` holds.

**4. Disjointness is passed as a parameter to `disjiUnion`.**

The third argument of `powerset_card_disjiUnion` is `s.pairwise_disjoint_powersetCard.set_pairwise _`,
so `DecidableEq (Finset α)` is not required; `powerset_card_biUnion` (line 334) is
derived from `disjiUnion_eq_biUnion` and does require `[DecidableEq (Finset α)]`.

**5. `set_option backward.isDefEq.respectTransparency false` at lines 320 and 333.**

This setting is unrelated to the mathematical content and is used for elaboration: when aligning the disjointness parameter type of `disjiUnion` with the provided proof,
comparing by expanding definitions would take a long time; disabling this option allows comparison by opaque constants to succeed.

### Dependency Order of Main Results

```
mem_powersetCard        (membership ↔ subset ∧ cardinality)
powersetCard_nonempty   (nonempty ↔ n ≤ #s)
powersetCard_succ_insert(recurrence with a new element)
        ↓
powersetCard_sup        (hn : n < #u)
        ↓  r = n.succ
powersetCard_biUnion    (hr : r ≠ 0, hrs : r ≤ #s)
        ↓  congr ((h).biUnion id)
eq_of_powersetCard_eq   (hab, hr₀, hra, h)
        ↓
powersetCard_injOn      (injective on the family of sets with #a = q)
```

---

## V. Available API

**Definitions**: `Finset.powerset`, `Finset.ssubsets`, `Finset.powersetCard`

**Membership**: `mem_powerset`, `mem_ssubsets`, `mem_powersetCard`, `coe_powerset`,
`empty_mem_powerset`, `mem_powerset_self`, `empty_mem_ssubsets`, `powerset_empty`,
`powerset_eq_singleton_empty`, `powersetCard_zero`, `powersetCard_self`,
`powersetCard_eq_filter`, `powersetCard_eq_empty`, `powersetCard_nonempty`

**Monotonicity and Injectivity**: `powerset_mono`, `powerset_injective`, `powerset_inj`,
`powersetCard_mono`, `powersetCard_injOn`, `eq_of_powersetCard_eq`

**Related to Mappings**: `powerset_image`, `image_surjOn_powerset`, `image_injOn_powerset_of_injOn`,
`injOn_image_of_biUnion_injOn`, `powersetCard_map`, `map_val_val_powersetCard`, `powersetCard_one`

**Counting**: `card_powerset`, `card_powersetCard`, `card_filter_powersetCard_subset`,
`filter_powersetCard_subset`, `powersetCard_eq_empty`, `powersetCard_nonempty`, `powersetCard_card_add`

**Decomposition and Disjointness**: `powerset_insert`, `powersetCard_succ_insert`, `pairwiseDisjoint_pair_insert`,
`powersetCard_inter`, `disjoint_powersetCard_powersetCard`, `disjoint_powersetCard_of_ne`,
`Disjoint.powersetCard_powersetCard_finset`, `pairwise_disjoint_powersetCard`,
`powerset_card_disjiUnion`, `powerset_card_biUnion`, `powersetCard_sup`, `powersetCard_biUnion`,
`powersetCard_empty_subsingleton`, `biUnion_id_subset_iff_subset_powerset`,
`notMem_of_mem_powerset_of_notMem`, `powerset_nonempty`

**Decidability**: `decidableExistsOfDecidableSubsets`, `decidableForallOfDecidableSubsets`,
`decidableExistsOfDecidableSubsets'`, `decidableForallOfDecidableSubsets'` (4 are `instance`s);
`decidableExistsOfDecidableSSubsets`, `decidableForallOfDecidableSSubsets` and their `'` versions are `def`s and must be called explicitly.
