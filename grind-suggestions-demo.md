# Grind Suggestions Demo

This document demonstrates the `grind? +suggestions` tactic, which can automatically
discover minimal `grind only [...]` invocations to replace complex manual proofs.

## How It Works

1. Replace a proof (or proof fragment) with `grind? +suggestions`
2. Build the file to see the suggestions
3. Pick the simplest suggestion (usually the one without internal `#xxxx` references)
4. Verify the replacement compiles

## Demo Instructions

For each example below:
1. Open the file in VS Code
2. Find the theorem/definition
3. Replace the indicated proof section with `grind? +suggestions`
4. Wait for diagnostics or run `lake build <module>`
5. Apply the suggested `grind only [...]` replacement
6. Verify it compiles

---

## Example 1: zpow_add'

**File:** `Mathlib/Algebra/GroupWithZero/Basic.lean`
**Definition:** `zpow_add'`

**Original proof:**
```lean
lemma zpow_add' {m n : ℤ} (h : a ≠ 0 ∨ m + n ≠ 0 ∨ m = 0 ∧ n = 0) :
    a ^ (m + n) = a ^ m * a ^ n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  by_cases ha : a = 0
  · subst a
    simp only [false_or, not_true, Ne, hm, hn, false_and, or_false] at h
    rw [zero_zpow _ h, zero_zpow _ hm, zero_mul]
  · exact zpow_add₀ ha m n
```

**Replacement:**
```lean
lemma zpow_add' {m n : ℤ} (h : a ≠ 0 ∨ m + n ≠ 0 ∨ m = 0 ∧ n = 0) :
    a ^ (m + n) = a ^ m * a ^ n := by
  grind only [mul_eq_zero_of_ne_zero_imp_eq_zero, zpow_add₀, mul_left_eq_self₀,
    zero_zpow_eq_one₀, zero_zpow_eq]
```

---

## Example 2: lcm_dedup

**File:** `Mathlib/Algebra/GCDMonoid/Multiset.lean`
**Definition:** `lcm_dedup`

**Original proof (inductive step):**
```lean
theorem lcm_dedup (s : Multiset α) : (dedup s).lcm = s.lcm :=
  Multiset.induction_on s (by simp) fun a s IH ↦ by
    by_cases h : a ∈ s; swap; · simp [IH, h]
    simp only [h, dedup_cons_of_mem, IH, lcm_cons]
    unfold lcm
    rw [← cons_erase h, fold_cons_left, ← lcm_assoc, lcm_same]
    apply lcm_eq_of_associated_left (associated_normalize _)
```

**Replacement:**
```lean
theorem lcm_dedup (s : Multiset α) : (dedup s).lcm = s.lcm :=
  Multiset.induction_on s (by simp) fun a s IH ↦ by
    grind only [lcm_mono, dedup_cons_of_mem, dedup_cons_of_notMem, dedup_ext, lcm_cons,
      dedup_subset, subset_dedup, lcm_comm, lcm_eq_right_iff, normalize_lcm, lcm_eq_normalize]
```

---

## Example 3: cases_head_iff

**File:** `Mathlib/Logic/Relation.lean`
**Definition:** `cases_head_iff`

**Original proof:**
```lean
theorem cases_head_iff : ReflTransGen r a b ↔ a = b ∨ ∃ c, r a c ∧ ReflTransGen r c b := by
  use cases_head
  rintro (rfl | ⟨c, hac, hcb⟩)
  · rfl
  · exact head hac hcb
```

**Replacement:**
```lean
theorem cases_head_iff : ReflTransGen r a b ↔ a = b ∨ ∃ c, r a c ∧ ReflTransGen r c b := by
  grind only [cases_tail_iff, cases_head, head]
```

---

## Example 4: removeNone_aux

**File:** `Mathlib/Logic/Equiv/Option.lean`
**Definition:** `removeNone_aux`

**Original proof (the `show` block):**
```lean
def removeNone_aux (x : α) : β :=
  if h : (e (some x)).isSome then Option.get _ h
  else
    Option.get _ <|
      show (e none).isSome by
        rw [← Option.ne_none_iff_isSome]
        intro hn
        rw [Option.not_isSome_iff_eq_none, ← hn] at h
        exact Option.some_ne_none _ (e.injective h)
```

**Replacement:**
```lean
def removeNone_aux (x : α) : β :=
  if h : (e (some x)).isSome then Option.get _ h
  else
    Option.get _ <|
      show (e none).isSome by
        grind only [apply_eq_iff_eq, isSome_eq_isSome, isSome_iff_ne_none]
```

---

## Example 5: has_good_supp_iff (partial)

**File:** `Mathlib/Data/QPF/Univariate/Basic.lean`
**Definition:** `has_good_supp_iff`

This example shows replacing just part of a proof. The `intro h'` section at the end
of the proof can be replaced.

**Original proof fragment:**
```lean
  intro h'
  refine ⟨a, f, xeq.symm, ?_⟩; intro i
  apply h'; rw [mem_supp]
  intro a' f' xeq'
  apply h a' f' xeq'
  apply mem_image_of_mem _ (mem_univ _)
```

**Replacement:**
```lean
  intro h'
  grind only [supp_eq, = setOf_false, mem_supp, = subset_def, = mem_image, ← mem_univ]
```

---

## Example 6: prod_subset_prod_iff

**File:** `Mathlib/Data/Set/Prod.lean`
**Definition:** `prod_subset_prod_iff`

**Original proof:**
```lean
theorem prod_subset_prod_iff : s ×ˢ t ⊆ s₁ ×ˢ t₁ ↔ s ⊆ s₁ ∧ t ⊆ t₁ ∨ s = ∅ ∨ t = ∅ := by
  rcases (s ×ˢ t).eq_empty_or_nonempty with h | h
  · simp [h, prod_eq_empty_iff.1 h]
  have st : s.Nonempty ∧ t.Nonempty := by rwa [prod_nonempty_iff] at h
  refine ⟨fun H => Or.inl ⟨?_, ?_⟩, ?_⟩
  · have := image_mono (f := Prod.fst) H
    rwa [fst_image_prod _ st.2, fst_image_prod _ (h.mono H).snd] at this
  · have := image_mono (f := Prod.snd) H
    rwa [snd_image_prod st.1, snd_image_prod (h.mono H).fst] at this
  · intro H
    simp only [st.1.ne_empty, st.2.ne_empty, or_false] at H
    exact prod_mono H.1 H.2
```

**Replacement:**
```lean
theorem prod_subset_prod_iff : s ×ˢ t ⊆ s₁ ×ˢ t₁ ↔ s ⊆ s₁ ∧ t ⊆ t₁ ∨ s = ∅ ∨ t = ∅ := by
  grind only [prod_eq_empty_iff, prod_subset_iff, prod_mono, = subset_def,
    mem_empty_iff_false, mem_prod, empty_subset]
```

---

## Example 7: xPrevIsoSelf

**File:** `Mathlib/Algebra/Homology/HomologicalComplex.lean`
**Definition:** `xPrevIsoSelf`

**Original proof (the `by` block):**
```lean
def xPrevIsoSelf {j : ι} (h : ¬c.Rel (c.prev j) j) : C.xPrev j ≅ C.X j :=
  eqToIso <|
    congr_arg C.X
      (by
        dsimp [ComplexShape.prev]
        rw [dif_neg]
        push_neg; intro i hi
        have : c.prev j = i := c.prev_eq' hi
        rw [this] at h; contradiction)
```

**Replacement:**
```lean
def xPrevIsoSelf {j : ι} (h : ¬c.Rel (c.prev j) j) : C.xPrev j ≅ C.X j :=
  eqToIso <|
    congr_arg C.X
      (by grind only [ComplexShape.prev_eq_self])
```

---

## Example 8: isSheaf_sup

**File:** `Mathlib/CategoryTheory/Sites/Coverage.lean`
**Definition:** `isSheaf_sup`

**Original proof:**
```lean
theorem isSheaf_sup (K L : Coverage C) (P : Cᵒᵖ ⥤ Type*) :
    (Presieve.IsSheaf (K ⊔ L).toGrothendieck) P ↔
    (Presieve.IsSheaf K.toGrothendieck) P ∧ (Presieve.IsSheaf L.toGrothendieck) P := by
  refine ⟨fun h ↦ ⟨Presieve.isSheaf_of_le _ ((gi C).gc.monotone_l le_sup_left) h,
      Presieve.isSheaf_of_le _ ((gi C).gc.monotone_l le_sup_right) h⟩, fun h ↦ ?_⟩
  rw [isSheaf_coverage, isSheaf_coverage] at h
  rw [isSheaf_coverage]
  intro X R hR
  rcases hR with hR | hR
  · exact h.1 R hR
  · exact h.2 R hR
```

**Replacement:**
```lean
theorem isSheaf_sup (K L : Coverage C) (P : Cᵒᵖ ⥤ Type*) :
    (Presieve.IsSheaf (K ⊔ L).toGrothendieck) P ↔
    (Presieve.IsSheaf K.toGrothendieck) P ∧ (Presieve.IsSheaf L.toGrothendieck) P := by
  grind only [isSheaf_coverage, sup_covering, = Set.mem_union]
```

---
