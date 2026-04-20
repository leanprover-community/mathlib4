/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Directed
public import Mathlib.Order.BoundedOrder.Monotone
public import Mathlib.Order.Interval.Set.Basic

/-!
# Upper / lower bounds

In this file we prove various lemmas about upper/lower bounds of a set:
monotonicity, behaviour under `∪`, `∩`, `insert`,
and provide formulas for `∅`, `univ`, and intervals.
-/

@[expose] public section

open Function Set

open OrderDual (toDual ofDual)

variable {α β γ : Type*}

section

variable [Preorder α] {s t u : Set α} {a b : α}

@[to_dual]
theorem mem_upperBounds : a ∈ upperBounds s ↔ ∀ x ∈ s, x ≤ a :=
  Iff.rfl

@[to_dual]
lemma mem_upperBounds_iff_subset_Iic : a ∈ upperBounds s ↔ s ⊆ Iic a := Iff.rfl

@[to_dual]
theorem bddAbove_def : BddAbove s ↔ ∃ x, ∀ y ∈ s, y ≤ x :=
  Iff.rfl

@[to_dual]
theorem top_mem_upperBounds [OrderTop α] (s : Set α) : ⊤ ∈ upperBounds s := fun _ _ => le_top

@[to_dual (attr := simp)]
theorem isLeast_bot_iff [OrderBot α] : IsLeast s ⊥ ↔ ⊥ ∈ s :=
  and_iff_left <| bot_mem_lowerBounds _

/-- A set `s` is not bounded above if and only if for each `x` there exists `y ∈ s` such that `x`
is not greater than or equal to `y`. This version only assumes `Preorder` structure and uses
`¬(y ≤ x)`. A version for linear orders is called `not_bddAbove_iff`. -/
@[to_dual
/-- A set `s` is not bounded below if and only if for each `x` there exists `y ∈ s` such that `x`
is not less than or equal to `y`. This version only assumes `Preorder` structure and uses
`¬(x ≤ y)`. A version for linear orders is called `not_bddBelow_iff`. -/]
theorem not_bddAbove_iff' : ¬BddAbove s ↔ ∀ x, ∃ y ∈ s, ¬y ≤ x := by
  simp [BddAbove, upperBounds, Set.Nonempty]

/-- A set `s` is not bounded above if and only if for each `x` there exists `y ∈ s` that is greater
than `x`. A version for preorders is called `not_bddAbove_iff'`. -/
@[to_dual
/-- A set `s` is not bounded below if and only if for each `x` there exists `y ∈ s` that is less
than `x`. A version for preorders is called `not_bddBelow_iff'`. -/]
theorem not_bddAbove_iff {α : Type*} [LinearOrder α] {s : Set α} :
    ¬BddAbove s ↔ ∀ x, ∃ y ∈ s, x < y := by
  simp only [not_bddAbove_iff', not_le]

@[to_dual (attr := simp)]
lemma bddAbove_preimage_ofDual {s : Set α} : BddAbove (ofDual ⁻¹' s) ↔ BddBelow s := Iff.rfl

@[to_dual (attr := simp)]
lemma bddAbove_preimage_toDual {s : Set αᵒᵈ} : BddAbove (toDual ⁻¹' s) ↔ BddBelow s := Iff.rfl

@[to_dual]
theorem BddAbove.dual (h : BddAbove s) : BddBelow (ofDual ⁻¹' s) :=
  h

@[to_dual]
theorem IsLeast.dual (h : IsLeast s a) : IsGreatest (ofDual ⁻¹' s) (toDual a) :=
  h

@[to_dual]
theorem IsLUB.dual (h : IsLUB s a) : IsGLB (ofDual ⁻¹' s) (toDual a) :=
  h

/-- If `a` is the least element of a set `s`, then subtype `s` is an order with bottom element. -/
@[to_dual
/-- If `a` is the greatest element of a set `s`, then subtype `s` is an order with top element. -/]
abbrev IsLeast.orderBot (h : IsLeast s a) :
    OrderBot s where
  bot := ⟨a, h.1⟩
  bot_le := Subtype.forall.2 h.2

@[to_dual]
theorem isLUB_congr (h : upperBounds s = upperBounds t) : IsLUB s a ↔ IsLUB t a := by
  rw [IsLUB, IsLUB, h]

@[to_dual (attr := simp)]
lemma IsCofinalFor.of_subset (hst : s ⊆ t) : IsCofinalFor s t :=
  fun a ha ↦ ⟨a, hst ha, le_rfl⟩

@[to_dual]
alias HasSubset.Subset.isCofinalFor := IsCofinalFor.of_subset

@[deprecated HasSubset.Subset.isCofinalFor (since := "2026-01-08")]
alias HasSubset.Subset.iscofinalfor := IsCofinalFor.of_subset
@[deprecated HasSubset.Subset.isCoinitialFor (since := "2026-01-08")]
alias HasSubset.Subset.iscoinitialfor := IsCoinitialFor.of_subset

@[to_dual (attr := refl)]
protected lemma IsCofinalFor.rfl : IsCofinalFor s s := .of_subset .rfl

@[to_dual]
protected lemma IsCofinalFor.trans (hst : IsCofinalFor s t) (htu : IsCofinalFor t u) :
    IsCofinalFor s u :=
  fun _a ha ↦ let ⟨_b, hb, hab⟩ := hst ha; let ⟨c, hc, hbc⟩ := htu hb; ⟨c, hc, hab.trans hbc⟩

@[to_dual]
protected lemma IsCofinalFor.mono_left (hst : s ⊆ t) (htu : IsCofinalFor t u) :
    IsCofinalFor s u := hst.isCofinalFor.trans htu

@[to_dual]
protected lemma IsCofinalFor.mono_right (htu : t ⊆ u) (hst : IsCofinalFor s t) :
    IsCofinalFor s u := hst.trans htu.isCofinalFor

lemma DirectedOn.isCofinalFor_fst_image_prod_snd_image {β : Type*} [Preorder β] {s : Set (α × β)}
    (hs : DirectedOn (· ≤ ·) s) : IsCofinalFor ((Prod.fst '' s) ×ˢ (Prod.snd '' s)) s := by
  rintro ⟨_, _⟩ ⟨⟨x, hx, rfl⟩, y, hy, rfl⟩
  obtain ⟨z, hz, hxz, hyz⟩ := hs _ hx _ hy
  exact ⟨z, hz, hxz.1, hyz.2⟩

/-!
### Monotonicity
-/


@[to_dual]
theorem upperBounds_mono_set ⦃s t : Set α⦄ (hst : s ⊆ t) : upperBounds t ⊆ upperBounds s :=
  fun _ hb _ h => hb <| hst h

@[to_dual (attr := gcongr)]
lemma upperBounds_mono_of_isCofinalFor (hst : IsCofinalFor s t) : upperBounds t ⊆ upperBounds s :=
  fun _a ha _b hb ↦ let ⟨_c, hc, hbc⟩ := hst hb; hbc.trans (ha hc)

@[to_dual]
theorem upperBounds_mono_mem ⦃a b⦄ (hab : a ≤ b) : a ∈ upperBounds s → b ∈ upperBounds s :=
  fun ha _ h => le_trans (ha h) hab

@[to_dual]
theorem upperBounds_mono ⦃s t : Set α⦄ (hst : s ⊆ t) ⦃a b⦄ (hab : a ≤ b) :
    a ∈ upperBounds t → b ∈ upperBounds s := fun ha =>
  upperBounds_mono_set hst <| upperBounds_mono_mem hab ha

/-- If `s ⊆ t` and `t` is bounded above, then so is `s`. -/
@[to_dual (attr := gcongr) /-- If `s ⊆ t` and `t` is bounded below, then so is `s`. -/]
theorem BddAbove.mono ⦃s t : Set α⦄ (h : s ⊆ t) : BddAbove t → BddAbove s :=
  Nonempty.mono <| upperBounds_mono_set h

/-- If `a` is a least upper bound for sets `s` and `p`, then it is a least upper bound for any
set `t`, `s ⊆ t ⊆ p`. -/
@[to_dual /-- If `a` is a greatest lower bound for sets `s` and `p`, then it is a greater lower
bound for any set `t`, `s ⊆ t ⊆ p`. -/]
theorem IsLUB.of_subset_of_superset {s t p : Set α} (hs : IsLUB s a) (hp : IsLUB p a) (hst : s ⊆ t)
    (htp : t ⊆ p) : IsLUB t a :=
  ⟨upperBounds_mono_set htp hp.1, lowerBounds_mono_set (upperBounds_mono_set hst) hs.2⟩

@[to_dual]
theorem IsLeast.mono (ha : IsLeast s a) (hb : IsLeast t b) (hst : s ⊆ t) : b ≤ a :=
  hb.2 (hst ha.1)

@[to_dual]
theorem IsLUB.mono (ha : IsLUB s a) (hb : IsLUB t b) (hst : s ⊆ t) : a ≤ b :=
  IsLeast.mono hb ha <| upperBounds_mono_set hst

@[to_dual]
theorem subset_lowerBounds_upperBounds (s : Set α) : s ⊆ lowerBounds (upperBounds s) :=
  fun _ hx _ hy => hy hx

@[to_dual]
theorem Set.Nonempty.bddAbove_lowerBounds (hs : s.Nonempty) : BddAbove (lowerBounds s) :=
  hs.mono (subset_upperBounds_lowerBounds s)

/-!
### Conversions
-/


@[to_dual]
theorem IsLeast.isGLB (h : IsLeast s a) : IsGLB s a :=
  ⟨h.2, fun _ hb => hb h.1⟩

@[to_dual]
theorem IsLUB.upperBounds_eq (h : IsLUB s a) : upperBounds s = Ici a :=
  Set.ext fun _ => ⟨fun hb => h.2 hb, fun hb => upperBounds_mono_mem hb h.1⟩

@[to_dual]
theorem IsLeast.lowerBounds_eq (h : IsLeast s a) : lowerBounds s = Iic a :=
  h.isGLB.lowerBounds_eq

@[to_dual]
theorem IsGreatest.lt_iff (h : IsGreatest s a) : a < b ↔ ∀ x ∈ s, x < b :=
  ⟨fun hlt _x hx => (h.2 hx).trans_lt hlt, fun h' => h' _ h.1⟩

@[to_dual le_isGLB_iff]
theorem isLUB_le_iff (h : IsLUB s a) : a ≤ b ↔ b ∈ upperBounds s := by
  rw [h.upperBounds_eq]
  rfl

@[to_dual]
theorem isLUB_iff_le_iff : IsLUB s a ↔ ∀ b, a ≤ b ↔ b ∈ upperBounds s :=
  ⟨fun h _ => isLUB_le_iff h, fun H => ⟨(H _).1 le_rfl, fun b hb => (H b).2 hb⟩⟩

/-- If `s` has a least upper bound, then it is bounded above. -/
@[to_dual /-- If `s` has a greatest lower bound, then it is bounded below. -/]
theorem IsLUB.bddAbove (h : IsLUB s a) : BddAbove s :=
  ⟨a, h.1⟩

/-- If `s` has a greatest element, then it is bounded above. -/
@[to_dual /-- If `s` has a least element, then it is bounded below. -/]
theorem IsGreatest.bddAbove (h : IsGreatest s a) : BddAbove s :=
  ⟨a, h.2⟩

@[to_dual]
theorem IsLeast.nonempty (h : IsLeast s a) : s.Nonempty :=
  ⟨a, h.1⟩

/-!
### Union and intersection
-/

@[to_dual (attr := simp)]
theorem upperBounds_union : upperBounds (s ∪ t) = upperBounds s ∩ upperBounds t :=
  Subset.antisymm (fun _ hb => ⟨fun _ hx => hb (Or.inl hx), fun _ hx => hb (Or.inr hx)⟩)
    fun _ hb _ hx => hx.elim (fun hs => hb.1 hs) fun ht => hb.2 ht

@[to_dual]
theorem union_upperBounds_subset_upperBounds_inter :
    upperBounds s ∪ upperBounds t ⊆ upperBounds (s ∩ t) :=
  union_subset (upperBounds_mono_set inter_subset_left)
    (upperBounds_mono_set inter_subset_right)

@[to_dual]
theorem isLeast_union_iff {a : α} {s t : Set α} :
    IsLeast (s ∪ t) a ↔ IsLeast s a ∧ a ∈ lowerBounds t ∨ a ∈ lowerBounds s ∧ IsLeast t a := by
  simp [IsLeast, lowerBounds_union, or_and_right, and_comm (a := a ∈ t), and_assoc]

/-- If `s` is bounded, then so is `s ∩ t` -/
@[to_dual /-- If `s` is bounded, then so is `s ∩ t` -/]
theorem BddAbove.inter_of_left (h : BddAbove s) : BddAbove (s ∩ t) :=
  h.mono inter_subset_left

/-- If `t` is bounded, then so is `s ∩ t` -/
@[to_dual /-- If `t` is bounded, then so is `s ∩ t` -/]
theorem BddAbove.inter_of_right (h : BddAbove t) : BddAbove (s ∩ t) :=
  h.mono inter_subset_right

/-- In a directed order, the union of bounded above sets is bounded above. -/
@[to_dual /-- In a codirected order, the union of bounded below sets is bounded below. -/]
theorem BddAbove.union [IsDirectedOrder α] {s t : Set α} :
    BddAbove s → BddAbove t → BddAbove (s ∪ t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨c, hca, hcb⟩ := exists_ge_ge a b
  rw [BddAbove, upperBounds_union]
  exact ⟨c, upperBounds_mono_mem hca ha, upperBounds_mono_mem hcb hb⟩

/-- In a directed order, the union of two sets is bounded above if and only if both sets are. -/
@[to_dual
/-- In a codirected order, the union of two sets is bounded below if and only if both sets are. -/]
theorem bddAbove_union [IsDirectedOrder α] {s t : Set α} :
    BddAbove (s ∪ t) ↔ BddAbove s ∧ BddAbove t :=
  ⟨fun h => ⟨h.mono subset_union_left, h.mono subset_union_right⟩, fun h =>
    h.1.union h.2⟩

/-- If `a` is the least upper bound of `s` and `b` is the least upper bound of `t`,
then `a ⊔ b` is the least upper bound of `s ∪ t`. -/
@[to_dual /-- If `a` is the greatest lower bound of `s` and `b` is the greatest lower bound of `t`,
then `a ⊓ b` is the greatest lower bound of `s ∪ t`. -/]
theorem IsLUB.union [SemilatticeSup γ] {a b : γ} {s t : Set γ} (hs : IsLUB s a) (ht : IsLUB t b) :
    IsLUB (s ∪ t) (a ⊔ b) :=
  ⟨fun _ h =>
    h.casesOn (fun h => le_sup_of_le_left <| hs.left h) fun h => le_sup_of_le_right <| ht.left h,
    fun _ hc =>
    sup_le (hs.right fun _ hd => hc <| Or.inl hd) (ht.right fun _ hd => hc <| Or.inr hd)⟩

/-- If `a` is the least element of `s` and `b` is the least element of `t`,
then `min a b` is the least element of `s ∪ t`. -/
@[to_dual /-- If `a` is the greatest element of `s` and `b` is the greatest element of `t`,
then `max a b` is the greatest element of `s ∪ t`. -/]
theorem IsLeast.union [LinearOrder γ] {a b : γ} {s t : Set γ} (ha : IsLeast s a)
    (hb : IsLeast t b) : IsLeast (s ∪ t) (min a b) :=
  ⟨by rcases le_total a b with h | h <;> simp [h, ha.1, hb.1], (ha.isGLB.union hb.isGLB).1⟩

@[to_dual]
theorem IsLUB.inter_Ici_of_mem [LinearOrder γ] {s : Set γ} {a b : γ} (ha : IsLUB s a) (hb : b ∈ s) :
    IsLUB (s ∩ Ici b) a :=
  ⟨fun _ hx => ha.1 hx.1, fun c hc =>
    have hbc : b ≤ c := hc ⟨hb, le_rfl⟩
    ha.2 fun x hx => ((le_total x b).elim fun hxb => hxb.trans hbc) fun hbx => hc ⟨hx, hbx⟩⟩

theorem bddAbove_iff_exists_ge [SemilatticeSup γ] {s : Set γ} (x₀ : γ) :
    BddAbove s ↔ ∃ x, x₀ ≤ x ∧ ∀ y ∈ s, y ≤ x := by
  rw [bddAbove_def, exists_ge_and_iff_exists]
  exact Monotone.ball fun x _ => monotone_le

@[to_dual existing bddAbove_iff_exists_ge]
theorem bddBelow_iff_exists_le [SemilatticeInf γ] {s : Set γ} (x₀ : γ) :
    BddBelow s ↔ ∃ x, x ≤ x₀ ∧ ∀ y ∈ s, x ≤ y :=
  bddAbove_iff_exists_ge (toDual x₀)

@[to_dual exists_le]
theorem BddAbove.exists_ge [SemilatticeSup γ] {s : Set γ} (hs : BddAbove s) (x₀ : γ) :
    ∃ x, x₀ ≤ x ∧ ∀ y ∈ s, y ≤ x :=
  (bddAbove_iff_exists_ge x₀).mp hs

/-!
### Specific sets
#### Unbounded intervals
-/


@[to_dual]
theorem isLeast_Ici : IsLeast (Ici a) a :=
  ⟨self_mem_Ici, fun _ => id⟩

@[to_dual]
theorem isGreatest_Ioi_top [OrderTop α] (ha : ¬ IsMax a) : IsGreatest (Ioi a) ⊤ :=
  ⟨(not_isMax_iff.1 ha).elim fun _ => lt_top_of_lt, fun _ _ => le_top⟩

@[to_dual]
theorem isLUB_Iic : IsLUB (Iic a) a :=
  isGreatest_Iic.isLUB

@[to_dual]
theorem upperBounds_Iic : upperBounds (Iic a) = Ici a :=
  isLUB_Iic.upperBounds_eq

@[to_dual]
theorem bddAbove_Iic : BddAbove (Iic a) :=
  isLUB_Iic.bddAbove

@[to_dual]
theorem bddAbove_Iio : BddAbove (Iio a) :=
  ⟨a, fun _ hx => le_of_lt hx⟩

@[to_dual]
theorem le_of_isLUB_Iio (a : α) (hb : IsLUB (Iio a) b) : b ≤ a :=
  (isLUB_le_iff hb).mpr fun _ hk => le_of_lt hk

@[deprecated (since := "2026-01-17")] alias lub_Iio_le := le_of_isLUB_Iio
@[deprecated (since := "2026-01-17")] alias le_glb_Ioi := le_of_isGLB_Ioi

@[to_dual]
theorem lub_Iio_eq_self_or_Iio_eq_Iic [PartialOrder γ] {j : γ} (i : γ) (hj : IsLUB (Iio i) j) :
    j = i ∨ Iio i = Iic j := by
  rcases eq_or_lt_of_le (le_of_isLUB_Iio i hj) with hj_eq_i | hj_lt_i
  · exact Or.inl hj_eq_i
  · right
    exact Set.ext fun k => ⟨fun hk_lt => hj.1 hk_lt, fun hk_le_j => lt_of_le_of_lt hk_le_j hj_lt_i⟩
section

variable [LinearOrder γ]

@[to_dual]
theorem exists_lub_Iio (i : γ) : ∃ j, IsLUB (Iio i) j := by
  by_cases! h_exists_lt : ∃ j, j ∈ upperBounds (Iio i) ∧ j < i
  · obtain ⟨j, hj_ub, hj_lt_i⟩ := h_exists_lt
    exact ⟨j, hj_ub, fun k hk_ub => hk_ub hj_lt_i⟩
  · refine ⟨i, fun j hj => le_of_lt hj, ?_⟩
    rw [mem_lowerBounds]
    exact h_exists_lt

variable [DenselyOrdered γ]

@[to_dual]
theorem isLUB_Iio {a : γ} : IsLUB (Iio a) a :=
  ⟨fun _ hx => le_of_lt hx, fun _ hy => le_of_forall_lt_imp_le_of_dense hy⟩

@[to_dual]
theorem upperBounds_Iio {a : γ} : upperBounds (Iio a) = Ici a :=
  isLUB_Iio.upperBounds_eq

end

/-!
#### Singleton
-/


@[to_dual (attr := simp)]
theorem isGreatest_singleton : IsGreatest {a} a :=
  ⟨mem_singleton a, fun _ hx => le_of_eq <| eq_of_mem_singleton hx⟩

@[to_dual (attr := simp)]
theorem isLUB_singleton : IsLUB {a} a :=
  isGreatest_singleton.isLUB

@[to_dual (attr := simp)]
lemma bddAbove_singleton : BddAbove ({a} : Set α) := isLUB_singleton.bddAbove

@[to_dual (attr := simp)]
theorem upperBounds_singleton : upperBounds {a} = Ici a :=
  isLUB_singleton.upperBounds_eq

/-!
#### Bounded intervals
-/


@[simp] lemma bddAbove_Icc : BddAbove (Icc a b) := ⟨b, fun _ => And.right⟩
@[simp] lemma bddBelow_Icc : BddBelow (Icc a b) := ⟨a, fun _ => And.left⟩
@[simp] lemma bddAbove_Ico : BddAbove (Ico a b) := bddAbove_Icc.mono Ico_subset_Icc_self
@[simp] lemma bddBelow_Ico : BddBelow (Ico a b) := bddBelow_Icc.mono Ico_subset_Icc_self
@[simp] lemma bddAbove_Ioc : BddAbove (Ioc a b) := bddAbove_Icc.mono Ioc_subset_Icc_self
@[simp] lemma bddBelow_Ioc : BddBelow (Ioc a b) := bddBelow_Icc.mono Ioc_subset_Icc_self
@[simp] lemma bddAbove_Ioo : BddAbove (Ioo a b) := bddAbove_Icc.mono Ioo_subset_Icc_self
@[simp] lemma bddBelow_Ioo : BddBelow (Ioo a b) := bddBelow_Icc.mono Ioo_subset_Icc_self

theorem isGreatest_Icc (h : a ≤ b) : IsGreatest (Icc a b) b :=
  ⟨right_mem_Icc.2 h, fun _ => And.right⟩

theorem isLUB_Icc (h : a ≤ b) : IsLUB (Icc a b) b :=
  (isGreatest_Icc h).isLUB

theorem upperBounds_Icc (h : a ≤ b) : upperBounds (Icc a b) = Ici b :=
  (isLUB_Icc h).upperBounds_eq

theorem isLeast_Icc (h : a ≤ b) : IsLeast (Icc a b) a :=
  ⟨left_mem_Icc.2 h, fun _ => And.left⟩

theorem isGLB_Icc (h : a ≤ b) : IsGLB (Icc a b) a :=
  (isLeast_Icc h).isGLB

theorem lowerBounds_Icc (h : a ≤ b) : lowerBounds (Icc a b) = Iic a :=
  (isGLB_Icc h).lowerBounds_eq

theorem isGreatest_Ioc (h : a < b) : IsGreatest (Ioc a b) b :=
  ⟨right_mem_Ioc.2 h, fun _ => And.right⟩

theorem isLUB_Ioc (h : a < b) : IsLUB (Ioc a b) b :=
  (isGreatest_Ioc h).isLUB

theorem upperBounds_Ioc (h : a < b) : upperBounds (Ioc a b) = Ici b :=
  (isLUB_Ioc h).upperBounds_eq

theorem isLeast_Ico (h : a < b) : IsLeast (Ico a b) a :=
  ⟨left_mem_Ico.2 h, fun _ => And.left⟩

theorem isGLB_Ico (h : a < b) : IsGLB (Ico a b) a :=
  (isLeast_Ico h).isGLB

theorem lowerBounds_Ico (h : a < b) : lowerBounds (Ico a b) = Iic a :=
  (isGLB_Ico h).lowerBounds_eq

section

variable [SemilatticeSup γ] [DenselyOrdered γ]

theorem isGLB_Ioo {a b : γ} (h : a < b) : IsGLB (Ioo a b) a :=
  ⟨fun _ hx => hx.1.le, fun x hx => by
    rcases eq_or_lt_of_le (le_sup_right : a ≤ x ⊔ a) with h₁ | h₂
    · exact h₁.symm ▸ le_sup_left
    obtain ⟨y, lty, ylt⟩ := exists_between h₂
    apply (not_lt_of_ge (sup_le (hx ⟨lty, ylt.trans_le (sup_le _ h.le)⟩) lty.le) ylt).elim
    obtain ⟨u, au, ub⟩ := exists_between h
    apply (hx ⟨au, ub⟩).trans ub.le⟩

theorem lowerBounds_Ioo {a b : γ} (hab : a < b) : lowerBounds (Ioo a b) = Iic a :=
  (isGLB_Ioo hab).lowerBounds_eq

theorem isGLB_Ioc {a b : γ} (hab : a < b) : IsGLB (Ioc a b) a :=
  (isGLB_Ioo hab).of_subset_of_superset (isGLB_Icc hab.le) Ioo_subset_Ioc_self Ioc_subset_Icc_self

theorem lowerBounds_Ioc {a b : γ} (hab : a < b) : lowerBounds (Ioc a b) = Iic a :=
  (isGLB_Ioc hab).lowerBounds_eq

end

section

variable [SemilatticeInf γ] [DenselyOrdered γ]

theorem isLUB_Ioo {a b : γ} (hab : a < b) : IsLUB (Ioo a b) b := by
  simpa only [Ioo_toDual] using isGLB_Ioo hab.dual

theorem upperBounds_Ioo {a b : γ} (hab : a < b) : upperBounds (Ioo a b) = Ici b :=
  (isLUB_Ioo hab).upperBounds_eq

theorem isLUB_Ico {a b : γ} (hab : a < b) : IsLUB (Ico a b) b := by
  simpa only [Ioc_toDual] using isGLB_Ioc hab.dual

theorem upperBounds_Ico {a b : γ} (hab : a < b) : upperBounds (Ico a b) = Ici b :=
  (isLUB_Ico hab).upperBounds_eq

end

@[to_dual]
theorem bddBelow_iff_subset_Ici : BddBelow s ↔ ∃ a, s ⊆ Ici a :=
  Iff.rfl

theorem bddBelow_bddAbove_iff_subset_Icc : BddBelow s ∧ BddAbove s ↔ ∃ a b, s ⊆ Icc a b := by
  simp [Ici_inter_Iic.symm, subset_inter_iff, bddBelow_iff_subset_Ici,
    bddAbove_iff_subset_Iic, exists_and_left, exists_and_right]

/-!
#### Univ
-/

@[to_dual (attr := simp)] theorem isGreatest_univ_iff : IsGreatest univ a ↔ IsTop a := by
  simp [IsGreatest, mem_upperBounds, IsTop]

@[to_dual]
theorem isGreatest_univ [OrderTop α] : IsGreatest (univ : Set α) ⊤ :=
  isGreatest_univ_iff.2 isTop_top

@[to_dual (attr := simp)]
theorem OrderTop.upperBounds_univ [PartialOrder γ] [OrderTop γ] :
    upperBounds (univ : Set γ) = {⊤} := by rw [isGreatest_univ.upperBounds_eq, Ici_top]

@[to_dual]
theorem isLUB_univ [OrderTop α] : IsLUB (univ : Set α) ⊤ :=
  isGreatest_univ.isLUB

@[to_dual (attr := simp)]
theorem NoTopOrder.upperBounds_univ [NoTopOrder α] : upperBounds (univ : Set α) = ∅ :=
  eq_empty_of_subset_empty fun b hb =>
    not_isTop b fun x => hb (mem_univ x)

@[to_dual (attr := simp)]
theorem not_bddAbove_univ [NoTopOrder α] : ¬BddAbove (univ : Set α) := by simp [BddAbove]

/-!
#### Empty set
-/


@[to_dual (attr := simp)]
theorem upperBounds_empty : upperBounds (∅ : Set α) = univ := by
  simp only [upperBounds, eq_univ_iff_forall, mem_setOf_eq, forall_mem_empty, forall_true_iff]

@[to_dual (attr := simp)]
theorem bddAbove_empty [Nonempty α] : BddAbove (∅ : Set α) := by
  simp only [BddAbove, upperBounds_empty, univ_nonempty]

@[to_dual (attr := simp)] theorem isGLB_empty_iff : IsGLB ∅ a ↔ IsTop a := by
  simp [IsGLB]

@[to_dual]
theorem isGLB_empty [OrderTop α] : IsGLB ∅ (⊤ : α) :=
  isGLB_empty_iff.2 isTop_top

@[to_dual]
theorem IsLUB.nonempty [NoBotOrder α] (hs : IsLUB s a) : s.Nonempty :=
  nonempty_iff_ne_empty.2 fun h =>
    not_isBot a fun _ => hs.right <| by rw [h, upperBounds_empty]; exact mem_univ _

@[to_dual]
theorem nonempty_of_not_bddAbove [ha : Nonempty α] (h : ¬BddAbove s) : s.Nonempty :=
  (Nonempty.elim ha) fun x => (not_bddAbove_iff'.1 h x).imp fun _ ha => ha.1

/-!
#### insert
-/


/-- Adding a point to a set preserves its boundedness above. -/
@[to_dual (attr := simp) /-- Adding a point to a set preserves its boundedness below. -/]
theorem bddAbove_insert [IsDirectedOrder α] {s : Set α} {a : α} :
    BddAbove (insert a s) ↔ BddAbove s := by
  simp only [insert_eq, bddAbove_union, bddAbove_singleton, true_and]

@[to_dual]
protected theorem BddAbove.insert [IsDirectedOrder α] {s : Set α} (a : α) :
    BddAbove s → BddAbove (insert a s) :=
  bddAbove_insert.2

@[to_dual]
protected theorem IsLUB.insert [SemilatticeSup γ] (a) {b} {s : Set γ} (hs : IsLUB s b) :
    IsLUB (insert a s) (a ⊔ b) := by
  rw [insert_eq]
  exact isLUB_singleton.union hs

@[to_dual]
protected theorem IsGreatest.insert [LinearOrder γ] (a) {b} {s : Set γ} (hs : IsGreatest s b) :
    IsGreatest (insert a s) (max a b) := by
  rw [insert_eq]
  exact isGreatest_singleton.union hs

@[to_dual (attr := simp)]
theorem upperBounds_insert (a : α) (s : Set α) :
    upperBounds (insert a s) = Ici a ∩ upperBounds s := by
  rw [insert_eq, upperBounds_union, upperBounds_singleton]

/-- When there is a global maximum, every set is bounded above. -/
@[to_dual (attr := simp) /-- When there is a global minimum, every set is bounded below. -/]
protected theorem OrderTop.bddAbove [OrderTop α] (s : Set α) : BddAbove s :=
  ⟨⊤, fun a _ => OrderTop.le_top a⟩

/-- Sets are automatically bounded or cobounded in complete lattices. To use the same statements
in complete and conditionally complete lattices but let automation fill automatically the
boundedness proofs in complete lattices, we use the tactic `bddDefault` in the statements,
in the form `(hA : BddAbove A := by bddDefault)`. -/
macro "bddDefault" : tactic =>
  `(tactic| first
    | apply OrderTop.bddAbove
    | apply OrderBot.bddBelow)

/-!
#### Pair
-/


@[to_dual]
theorem isLUB_pair [SemilatticeSup γ] {a b : γ} : IsLUB {a, b} (a ⊔ b) :=
  isLUB_singleton.insert _

@[to_dual]
theorem isGreatest_pair [LinearOrder γ] {a b : γ} : IsGreatest {a, b} (max a b) :=
  isGreatest_singleton.insert _

/-!
#### Lower/upper bounds
-/


@[to_dual (attr := simp)]
theorem isLUB_lowerBounds : IsLUB (lowerBounds s) a ↔ IsGLB s a :=
  ⟨fun H => ⟨fun _ hx => H.2 <| subset_upperBounds_lowerBounds s hx, H.1⟩, IsGreatest.isLUB⟩

end

section Minimal

variable [Preorder α] {s : Set α} {a b : α}

theorem DirectedOn.le_of_minimal (h : DirectedOn (fun x y ↦ y ≤ x) s) (hMin : Minimal (· ∈ s) a)
    (hb : b ∈ s) : a ≤ b := by
  obtain ⟨z, hz, hza, hzb⟩ := h a hMin.1 b hb
  exact (hMin.2 hz hza).trans hzb

theorem DirectedOn.le_of_maximal (h : DirectedOn (· ≤ ·) s) (hMax : Maximal (· ∈ s) a)
    (hb : b ∈ s) : b ≤ a := by
  obtain ⟨z, hz, haz, hbz⟩ := h a hMax.1 b hb
  exact hbz.trans (hMax.2 hz haz)

theorem DirectedOn.minimal_iff_isLeast (h : DirectedOn (fun x y ↦ y ≤ x) s) :
    Minimal (· ∈ s) a ↔ IsLeast s a :=
  ⟨fun hMin ↦ ⟨hMin.1, fun _ hy ↦ h.le_of_minimal hMin hy⟩, fun h ↦ ⟨h.1, fun _ hy _ ↦ h.2 hy⟩⟩

theorem DirectedOn.maximal_iff_isGreatest (h : DirectedOn (· ≤ ·) s) :
    Maximal (· ∈ s) a ↔ IsGreatest s a :=
  minimal_iff_isLeast (α := αᵒᵈ) h

end Minimal

theorem minimal_iff_isLeast [LinearOrder α] {s : Set α} {a : α} :
    Minimal (· ∈ s) a ↔ IsLeast s a :=
  (Std.Total.directedOn s).minimal_iff_isLeast

theorem maximal_iff_isGreatest [LinearOrder α] {s : Set α} {a : α} :
    Maximal (· ∈ s) a ↔ IsGreatest s a :=
  (Std.Total.directedOn s).maximal_iff_isGreatest

/-!
### (In)equalities with the least upper bound and the greatest lower bound
-/


section Preorder

variable [Preorder α] [Preorder β] {s s' : Set α} {t : Set β} {a b : α}

theorem lowerBounds_le_upperBounds (ha : a ∈ lowerBounds s) (hb : b ∈ upperBounds s) :
    s.Nonempty → a ≤ b
  | ⟨_, hc⟩ => le_trans (ha hc) (hb hc)

theorem lowerBounds_le_upperBounds_of_nonempty_inter (h : (s ∩ s').Nonempty)
    (ha : a ∈ lowerBounds s) (hb : b ∈ upperBounds s') : a ≤ b := by
  have ⟨x, hx, hx'⟩ := h
  exact le_trans (ha hx) (hb hx')

theorem isGLB_le_isLUB (ha : IsGLB s a) (hb : IsLUB s b) (hs : s.Nonempty) : a ≤ b :=
  lowerBounds_le_upperBounds ha.1 hb.1 hs

theorem isGLB_le_isLUB_of_nonempty_inter (h : (s ∩ s').Nonempty) (ha : IsGLB s a)
    (hb : IsLUB s' b) : a ≤ b :=
  lowerBounds_le_upperBounds_of_nonempty_inter h ha.left hb.left

@[to_dual lt_isGLB_iff]
theorem isLUB_lt_iff (ha : IsLUB s a) : a < b ↔ ∃ c ∈ upperBounds s, c < b :=
  ⟨fun hb => ⟨a, ha.1, hb⟩, fun ⟨_, hcs, hcb⟩ => lt_of_le_of_lt (ha.2 hcs) hcb⟩

theorem le_of_isLUB_le_isGLB {x y} (ha : IsGLB s a) (hb : IsLUB s b) (hab : b ≤ a) (hx : x ∈ s)
    (hy : y ∈ s) : x ≤ y :=
  calc
    x ≤ b := hb.1 hx
    _ ≤ a := hab
    _ ≤ y := ha.1 hy

@[to_dual (attr := simp)] lemma upperBounds_prod (hs : s.Nonempty) (ht : t.Nonempty) :
    upperBounds (s ×ˢ t) = upperBounds s ×ˢ upperBounds t := by
  ext; rw [← nonempty_coe_sort] at hs ht; aesop (add simp [upperBounds, Prod.le_def, forall_and])

@[to_dual]
lemma IsLUB.prod {b : β} (hs : s.Nonempty) (ht : t.Nonempty) (ha : IsLUB s a) (hb : IsLUB t b) :
    IsLUB (s ×ˢ t) (a, b) := by simp_all +contextual [IsLUB, IsLeast, lowerBounds]

end Preorder

section PartialOrder

variable [PartialOrder α] {s : Set α} {a b : α}

@[to_dual]
theorem IsLeast.unique (Ha : IsLeast s a) (Hb : IsLeast s b) : a = b :=
  le_antisymm (Ha.right Hb.left) (Hb.right Ha.left)

@[to_dual]
theorem IsLeast.isLeast_iff_eq (Ha : IsLeast s a) : IsLeast s b ↔ a = b :=
  Iff.intro Ha.unique fun h => h ▸ Ha

@[to_dual]
theorem IsLUB.unique (Ha : IsLUB s a) (Hb : IsLUB s b) : a = b :=
  IsLeast.unique Ha Hb

theorem Set.subsingleton_of_isLUB_le_isGLB (Ha : IsGLB s a) (Hb : IsLUB s b) (hab : b ≤ a) :
    s.Subsingleton := fun _ hx _ hy =>
  le_antisymm (le_of_isLUB_le_isGLB Ha Hb hab hx hy) (le_of_isLUB_le_isGLB Ha Hb hab hy hx)

theorem isGLB_lt_isLUB_of_ne (Ha : IsGLB s a) (Hb : IsLUB s b) {x y} (Hx : x ∈ s) (Hy : y ∈ s)
    (Hxy : x ≠ y) : a < b :=
  lt_iff_le_not_ge.2
    ⟨lowerBounds_le_upperBounds Ha.1 Hb.1 ⟨x, Hx⟩, fun hab =>
      Hxy <| Set.subsingleton_of_isLUB_le_isGLB Ha Hb hab Hx Hy⟩

end PartialOrder

section LinearOrder

variable [LinearOrder α] {s : Set α} {a b : α}

@[to_dual isGLB_lt_iff]
theorem lt_isLUB_iff (h : IsLUB s a) : b < a ↔ ∃ c ∈ s, b < c := by
  simp_rw [← not_le, isLUB_le_iff h, mem_upperBounds, not_forall, not_le, exists_prop]

@[to_dual none]
theorem IsLUB.exists_between (h : IsLUB s a) (hb : b < a) : ∃ c ∈ s, b < c ∧ c ≤ a :=
  let ⟨c, hcs, hbc⟩ := (lt_isLUB_iff h).1 hb
  ⟨c, hcs, hbc, h.1 hcs⟩

@[to_dual none]
theorem IsLUB.exists_between' (h : IsLUB s a) (h' : a ∉ s) (hb : b < a) : ∃ c ∈ s, b < c ∧ c < a :=
  let ⟨c, hcs, hbc, hca⟩ := h.exists_between hb
  ⟨c, hcs, hbc, hca.lt_of_ne fun hac => h' <| hac ▸ hcs⟩

@[to_dual none]
theorem IsGLB.exists_between (h : IsGLB s a) (hb : a < b) : ∃ c ∈ s, a ≤ c ∧ c < b :=
  let ⟨c, hcs, hbc⟩ := (isGLB_lt_iff h).1 hb
  ⟨c, hcs, h.1 hcs, hbc⟩

@[to_dual none]
theorem IsGLB.exists_between' (h : IsGLB s a) (h' : a ∉ s) (hb : a < b) : ∃ c ∈ s, a < c ∧ c < b :=
  let ⟨c, hcs, hac, hcb⟩ := h.exists_between hb
  ⟨c, hcs, hac.lt_of_ne fun hac => h' <| hac.symm ▸ hcs, hcb⟩

end LinearOrder

theorem isGreatest_himp [GeneralizedHeytingAlgebra α] (a b : α) :
    IsGreatest {w | w ⊓ a ≤ b} (a ⇨ b) := by
  simp [IsGreatest, mem_upperBounds]

theorem isLeast_sdiff [GeneralizedCoheytingAlgebra α] (a b : α) :
    IsLeast {w | a ≤ b ⊔ w} (a \ b) := by
  simp [IsLeast, mem_lowerBounds]

theorem isGreatest_compl [HeytingAlgebra α] (a : α) :
    IsGreatest {w | Disjoint w a} (aᶜ) := by
  simpa only [himp_bot, disjoint_iff_inf_le] using isGreatest_himp a ⊥

theorem isLeast_hnot [CoheytingAlgebra α] (a : α) :
    IsLeast {w | Codisjoint a w} (￢a) := by
  simpa only [CoheytingAlgebra.top_sdiff, codisjoint_iff_le_sup] using isLeast_sdiff ⊤ a

instance Nat.instDecidableIsLeast (p : ℕ → Prop) (n : ℕ) [DecidablePred p] :
    Decidable (IsLeast { n : ℕ | p n } n) :=
  decidable_of_iff (p n ∧ ∀ k < n, ¬p k) <| .and .rfl <| by
    simp [mem_lowerBounds, @imp_not_comm _ (p _)]

/-- An alternative constructor for `SemilatticeSup` using `IsLUB`. -/
@[to_dual (attr := implicit_reducible)
/-- An alternative constructor for `SemilatticeInf` using `IsGLB`. -/]
def SemilatticeSup.ofIsLUB [PartialOrder α] (sup : α → α → α)
    (isLUB_pair : ∀ a b, IsLUB {a, b} (sup a b)) :
    SemilatticeSup α where
  sup := sup
  le_sup_left a b := (isLUB_pair a b).1 (mem_insert _ _)
  le_sup_right a b := (isLUB_pair a b).1 (mem_insert_of_mem _ (mem_singleton _))
  sup_le a b _ hac hbc := (isLUB_pair a b).2 (forall_insert_of_forall (forall_eq.mpr hbc) hac)

/-- An alternative constructor for `Lattice` using `IsLUB` and `IsGLB`. -/
@[implicit_reducible, to_dual self (reorder := 3 4, 5 6)]
def Lattice.ofIsLUBofIsGLB [PartialOrder α] (sup inf : α → α → α)
    (isLUB_pair : ∀ a b, IsLUB {a, b} (sup a b)) (isGLB_pair : ∀ a b, IsGLB {a, b} (inf a b)) :
    Lattice α where
  __ := SemilatticeSup.ofIsLUB sup isLUB_pair
  __ := SemilatticeInf.ofIsGLB inf isGLB_pair
