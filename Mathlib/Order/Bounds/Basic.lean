/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Set.NAry
import Mathlib.Order.Directed

#align_import order.bounds.basic from "leanprover-community/mathlib"@"b1abe23ae96fef89ad30d9f4362c307f72a55010"

/-!
# Upper / lower bounds

In this file we define:
* `upperBounds`, `lowerBounds` : the set of upper bounds (resp., lower bounds) of a set;
* `BddAbove s`, `BddBelow s` : the set `s` is bounded above (resp., below), i.e., the set of upper
  (resp., lower) bounds of `s` is nonempty;
* `IsLeast s a`, `IsGreatest s a` : `a` is a least (resp., greatest) element of `s`;
  for a partial order, it is unique if exists;
* `IsLUB s a`, `IsGLB s a` : `a` is a least upper bound (resp., a greatest lower bound)
  of `s`; for a partial order, it is unique if exists.
We also prove various lemmas about monotonicity, behaviour under `∪`, `∩`, `insert`, and provide
formulas for `∅`, `univ`, and intervals.
-/


open Function Set

open OrderDual (toDual ofDual)

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

section

variable [Preorder α] [Preorder β] {s t : Set α} {a b : α}

/-!
### Definitions
-/


/-- The set of upper bounds of a set. -/
def upperBounds (s : Set α) : Set α :=
  { x | ∀ ⦃a⦄, a ∈ s → a ≤ x }
#align upper_bounds upperBounds

/-- The set of lower bounds of a set. -/
def lowerBounds (s : Set α) : Set α :=
  { x | ∀ ⦃a⦄, a ∈ s → x ≤ a }
#align lower_bounds lowerBounds

/-- A set is bounded above if there exists an upper bound. -/
def BddAbove (s : Set α) :=
  (upperBounds s).Nonempty
#align bdd_above BddAbove

/-- A set is bounded below if there exists a lower bound. -/
def BddBelow (s : Set α) :=
  (lowerBounds s).Nonempty
#align bdd_below BddBelow

/-- `a` is a least element of a set `s`; for a partial order, it is unique if exists. -/
def IsLeast (s : Set α) (a : α) : Prop :=
  a ∈ s ∧ a ∈ lowerBounds s
#align is_least IsLeast

/-- `a` is a greatest element of a set `s`; for a partial order, it is unique if exists. -/
def IsGreatest (s : Set α) (a : α) : Prop :=
  a ∈ s ∧ a ∈ upperBounds s
#align is_greatest IsGreatest

/-- `a` is a least upper bound of a set `s`; for a partial order, it is unique if exists. -/
def IsLUB (s : Set α) : α → Prop :=
  IsLeast (upperBounds s)
#align is_lub IsLUB

/-- `a` is a greatest lower bound of a set `s`; for a partial order, it is unique if exists. -/
def IsGLB (s : Set α) : α → Prop :=
  IsGreatest (lowerBounds s)
#align is_glb IsGLB

theorem mem_upperBounds : a ∈ upperBounds s ↔ ∀ x ∈ s, x ≤ a :=
  Iff.rfl
#align mem_upper_bounds mem_upperBounds

theorem mem_lowerBounds : a ∈ lowerBounds s ↔ ∀ x ∈ s, a ≤ x :=
  Iff.rfl
#align mem_lower_bounds mem_lowerBounds

lemma mem_upperBounds_iff_subset_Iic : a ∈ upperBounds s ↔ s ⊆ Iic a := Iff.rfl
#align mem_upper_bounds_iff_subset_Iic mem_upperBounds_iff_subset_Iic

lemma mem_lowerBounds_iff_subset_Ici : a ∈ lowerBounds s ↔ s ⊆ Ici a := Iff.rfl
#align mem_lower_bounds_iff_subset_Ici mem_lowerBounds_iff_subset_Ici

theorem bddAbove_def : BddAbove s ↔ ∃ x, ∀ y ∈ s, y ≤ x :=
  Iff.rfl
#align bdd_above_def bddAbove_def

theorem bddBelow_def : BddBelow s ↔ ∃ x, ∀ y ∈ s, x ≤ y :=
  Iff.rfl
#align bdd_below_def bddBelow_def

theorem bot_mem_lowerBounds [OrderBot α] (s : Set α) : ⊥ ∈ lowerBounds s := fun _ _ => bot_le
#align bot_mem_lower_bounds bot_mem_lowerBounds

theorem top_mem_upperBounds [OrderTop α] (s : Set α) : ⊤ ∈ upperBounds s := fun _ _ => le_top
#align top_mem_upper_bounds top_mem_upperBounds

@[simp]
theorem isLeast_bot_iff [OrderBot α] : IsLeast s ⊥ ↔ ⊥ ∈ s :=
  and_iff_left <| bot_mem_lowerBounds _
#align is_least_bot_iff isLeast_bot_iff

@[simp]
theorem isGreatest_top_iff [OrderTop α] : IsGreatest s ⊤ ↔ ⊤ ∈ s :=
  and_iff_left <| top_mem_upperBounds _
#align is_greatest_top_iff isGreatest_top_iff

/-- A set `s` is not bounded above if and only if for each `x` there exists `y ∈ s` such that `x`
is not greater than or equal to `y`. This version only assumes `Preorder` structure and uses
`¬(y ≤ x)`. A version for linear orders is called `not_bddAbove_iff`. -/
theorem not_bddAbove_iff' : ¬BddAbove s ↔ ∀ x, ∃ y ∈ s, ¬y ≤ x := by
  simp [BddAbove, upperBounds, Set.Nonempty]
#align not_bdd_above_iff' not_bddAbove_iff'

/-- A set `s` is not bounded below if and only if for each `x` there exists `y ∈ s` such that `x`
is not less than or equal to `y`. This version only assumes `Preorder` structure and uses
`¬(x ≤ y)`. A version for linear orders is called `not_bddBelow_iff`. -/
theorem not_bddBelow_iff' : ¬BddBelow s ↔ ∀ x, ∃ y ∈ s, ¬x ≤ y :=
  @not_bddAbove_iff' αᵒᵈ _ _
#align not_bdd_below_iff' not_bddBelow_iff'

/-- A set `s` is not bounded above if and only if for each `x` there exists `y ∈ s` that is greater
than `x`. A version for preorders is called `not_bddAbove_iff'`. -/
theorem not_bddAbove_iff {α : Type*} [LinearOrder α] {s : Set α} :
    ¬BddAbove s ↔ ∀ x, ∃ y ∈ s, x < y := by
  simp only [not_bddAbove_iff', not_le]
#align not_bdd_above_iff not_bddAbove_iff

/-- A set `s` is not bounded below if and only if for each `x` there exists `y ∈ s` that is less
than `x`. A version for preorders is called `not_bddBelow_iff'`. -/
theorem not_bddBelow_iff {α : Type*} [LinearOrder α] {s : Set α} :
    ¬BddBelow s ↔ ∀ x, ∃ y ∈ s, y < x :=
  @not_bddAbove_iff αᵒᵈ _ _
#align not_bdd_below_iff not_bddBelow_iff

theorem BddAbove.dual (h : BddAbove s) : BddBelow (ofDual ⁻¹' s) :=
  h
#align bdd_above.dual BddAbove.dual

theorem BddBelow.dual (h : BddBelow s) : BddAbove (ofDual ⁻¹' s) :=
  h
#align bdd_below.dual BddBelow.dual

theorem IsLeast.dual (h : IsLeast s a) : IsGreatest (ofDual ⁻¹' s) (toDual a) :=
  h
#align is_least.dual IsLeast.dual

theorem IsGreatest.dual (h : IsGreatest s a) : IsLeast (ofDual ⁻¹' s) (toDual a) :=
  h
#align is_greatest.dual IsGreatest.dual

theorem IsLUB.dual (h : IsLUB s a) : IsGLB (ofDual ⁻¹' s) (toDual a) :=
  h
#align is_lub.dual IsLUB.dual

theorem IsGLB.dual (h : IsGLB s a) : IsLUB (ofDual ⁻¹' s) (toDual a) :=
  h
#align is_glb.dual IsGLB.dual

/-- If `a` is the least element of a set `s`, then subtype `s` is an order with bottom element. -/
abbrev IsLeast.orderBot (h : IsLeast s a) :
    OrderBot s where
  bot := ⟨a, h.1⟩
  bot_le := Subtype.forall.2 h.2
#align is_least.order_bot IsLeast.orderBot

/-- If `a` is the greatest element of a set `s`, then subtype `s` is an order with top element. -/
abbrev IsGreatest.orderTop (h : IsGreatest s a) :
    OrderTop s where
  top := ⟨a, h.1⟩
  le_top := Subtype.forall.2 h.2
#align is_greatest.order_top IsGreatest.orderTop

/-!
### Monotonicity
-/


theorem upperBounds_mono_set ⦃s t : Set α⦄ (hst : s ⊆ t) : upperBounds t ⊆ upperBounds s :=
  fun _ hb _ h => hb <| hst h
#align upper_bounds_mono_set upperBounds_mono_set

theorem lowerBounds_mono_set ⦃s t : Set α⦄ (hst : s ⊆ t) : lowerBounds t ⊆ lowerBounds s :=
  fun _ hb _ h => hb <| hst h
#align lower_bounds_mono_set lowerBounds_mono_set

theorem upperBounds_mono_mem ⦃a b⦄ (hab : a ≤ b) : a ∈ upperBounds s → b ∈ upperBounds s :=
  fun ha _ h => le_trans (ha h) hab
#align upper_bounds_mono_mem upperBounds_mono_mem

theorem lowerBounds_mono_mem ⦃a b⦄ (hab : a ≤ b) : b ∈ lowerBounds s → a ∈ lowerBounds s :=
  fun hb _ h => le_trans hab (hb h)
#align lower_bounds_mono_mem lowerBounds_mono_mem

theorem upperBounds_mono ⦃s t : Set α⦄ (hst : s ⊆ t) ⦃a b⦄ (hab : a ≤ b) :
    a ∈ upperBounds t → b ∈ upperBounds s := fun ha =>
  upperBounds_mono_set hst <| upperBounds_mono_mem hab ha
#align upper_bounds_mono upperBounds_mono

theorem lowerBounds_mono ⦃s t : Set α⦄ (hst : s ⊆ t) ⦃a b⦄ (hab : a ≤ b) :
    b ∈ lowerBounds t → a ∈ lowerBounds s := fun hb =>
  lowerBounds_mono_set hst <| lowerBounds_mono_mem hab hb
#align lower_bounds_mono lowerBounds_mono

/-- If `s ⊆ t` and `t` is bounded above, then so is `s`. -/
theorem BddAbove.mono ⦃s t : Set α⦄ (h : s ⊆ t) : BddAbove t → BddAbove s :=
  Nonempty.mono <| upperBounds_mono_set h
#align bdd_above.mono BddAbove.mono

/-- If `s ⊆ t` and `t` is bounded below, then so is `s`. -/
theorem BddBelow.mono ⦃s t : Set α⦄ (h : s ⊆ t) : BddBelow t → BddBelow s :=
  Nonempty.mono <| lowerBounds_mono_set h
#align bdd_below.mono BddBelow.mono

/-- If `a` is a least upper bound for sets `s` and `p`, then it is a least upper bound for any
set `t`, `s ⊆ t ⊆ p`. -/
theorem IsLUB.of_subset_of_superset {s t p : Set α} (hs : IsLUB s a) (hp : IsLUB p a) (hst : s ⊆ t)
    (htp : t ⊆ p) : IsLUB t a :=
  ⟨upperBounds_mono_set htp hp.1, lowerBounds_mono_set (upperBounds_mono_set hst) hs.2⟩
#align is_lub.of_subset_of_superset IsLUB.of_subset_of_superset

/-- If `a` is a greatest lower bound for sets `s` and `p`, then it is a greater lower bound for any
set `t`, `s ⊆ t ⊆ p`. -/
theorem IsGLB.of_subset_of_superset {s t p : Set α} (hs : IsGLB s a) (hp : IsGLB p a) (hst : s ⊆ t)
    (htp : t ⊆ p) : IsGLB t a :=
  hs.dual.of_subset_of_superset hp hst htp
#align is_glb.of_subset_of_superset IsGLB.of_subset_of_superset

theorem IsLeast.mono (ha : IsLeast s a) (hb : IsLeast t b) (hst : s ⊆ t) : b ≤ a :=
  hb.2 (hst ha.1)
#align is_least.mono IsLeast.mono

theorem IsGreatest.mono (ha : IsGreatest s a) (hb : IsGreatest t b) (hst : s ⊆ t) : a ≤ b :=
  hb.2 (hst ha.1)
#align is_greatest.mono IsGreatest.mono

theorem IsLUB.mono (ha : IsLUB s a) (hb : IsLUB t b) (hst : s ⊆ t) : a ≤ b :=
  IsLeast.mono hb ha <| upperBounds_mono_set hst
#align is_lub.mono IsLUB.mono

theorem IsGLB.mono (ha : IsGLB s a) (hb : IsGLB t b) (hst : s ⊆ t) : b ≤ a :=
  IsGreatest.mono hb ha <| lowerBounds_mono_set hst
#align is_glb.mono IsGLB.mono

theorem subset_lowerBounds_upperBounds (s : Set α) : s ⊆ lowerBounds (upperBounds s) :=
  fun _ hx _ hy => hy hx
#align subset_lower_bounds_upper_bounds subset_lowerBounds_upperBounds

theorem subset_upperBounds_lowerBounds (s : Set α) : s ⊆ upperBounds (lowerBounds s) :=
  fun _ hx _ hy => hy hx
#align subset_upper_bounds_lower_bounds subset_upperBounds_lowerBounds

theorem Set.Nonempty.bddAbove_lowerBounds (hs : s.Nonempty) : BddAbove (lowerBounds s) :=
  hs.mono (subset_upperBounds_lowerBounds s)
#align set.nonempty.bdd_above_lower_bounds Set.Nonempty.bddAbove_lowerBounds

theorem Set.Nonempty.bddBelow_upperBounds (hs : s.Nonempty) : BddBelow (upperBounds s) :=
  hs.mono (subset_lowerBounds_upperBounds s)
#align set.nonempty.bdd_below_upper_bounds Set.Nonempty.bddBelow_upperBounds

/-!
### Conversions
-/


theorem IsLeast.isGLB (h : IsLeast s a) : IsGLB s a :=
  ⟨h.2, fun _ hb => hb h.1⟩
#align is_least.is_glb IsLeast.isGLB

theorem IsGreatest.isLUB (h : IsGreatest s a) : IsLUB s a :=
  ⟨h.2, fun _ hb => hb h.1⟩
#align is_greatest.is_lub IsGreatest.isLUB

theorem IsLUB.upperBounds_eq (h : IsLUB s a) : upperBounds s = Ici a :=
  Set.ext fun _ => ⟨fun hb => h.2 hb, fun hb => upperBounds_mono_mem hb h.1⟩
#align is_lub.upper_bounds_eq IsLUB.upperBounds_eq

theorem IsGLB.lowerBounds_eq (h : IsGLB s a) : lowerBounds s = Iic a :=
  h.dual.upperBounds_eq
#align is_glb.lower_bounds_eq IsGLB.lowerBounds_eq

theorem IsLeast.lowerBounds_eq (h : IsLeast s a) : lowerBounds s = Iic a :=
  h.isGLB.lowerBounds_eq
#align is_least.lower_bounds_eq IsLeast.lowerBounds_eq

theorem IsGreatest.upperBounds_eq (h : IsGreatest s a) : upperBounds s = Ici a :=
  h.isLUB.upperBounds_eq
#align is_greatest.upper_bounds_eq IsGreatest.upperBounds_eq

-- Porting note (#10756): new lemma
theorem IsGreatest.lt_iff (h : IsGreatest s a) : a < b ↔ ∀ x ∈ s, x < b :=
  ⟨fun hlt _x hx => (h.2 hx).trans_lt hlt, fun h' => h' _ h.1⟩

-- Porting note (#10756): new lemma
theorem IsLeast.lt_iff (h : IsLeast s a) : b < a ↔ ∀ x ∈ s, b < x :=
  h.dual.lt_iff

theorem isLUB_le_iff (h : IsLUB s a) : a ≤ b ↔ b ∈ upperBounds s := by
  rw [h.upperBounds_eq]
  rfl
#align is_lub_le_iff isLUB_le_iff

theorem le_isGLB_iff (h : IsGLB s a) : b ≤ a ↔ b ∈ lowerBounds s := by
  rw [h.lowerBounds_eq]
  rfl
#align le_is_glb_iff le_isGLB_iff

theorem isLUB_iff_le_iff : IsLUB s a ↔ ∀ b, a ≤ b ↔ b ∈ upperBounds s :=
  ⟨fun h _ => isLUB_le_iff h, fun H => ⟨(H _).1 le_rfl, fun b hb => (H b).2 hb⟩⟩
#align is_lub_iff_le_iff isLUB_iff_le_iff

theorem isGLB_iff_le_iff : IsGLB s a ↔ ∀ b, b ≤ a ↔ b ∈ lowerBounds s :=
  @isLUB_iff_le_iff αᵒᵈ _ _ _
#align is_glb_iff_le_iff isGLB_iff_le_iff

/-- If `s` has a least upper bound, then it is bounded above. -/
theorem IsLUB.bddAbove (h : IsLUB s a) : BddAbove s :=
  ⟨a, h.1⟩
#align is_lub.bdd_above IsLUB.bddAbove

/-- If `s` has a greatest lower bound, then it is bounded below. -/
theorem IsGLB.bddBelow (h : IsGLB s a) : BddBelow s :=
  ⟨a, h.1⟩
#align is_glb.bdd_below IsGLB.bddBelow

/-- If `s` has a greatest element, then it is bounded above. -/
theorem IsGreatest.bddAbove (h : IsGreatest s a) : BddAbove s :=
  ⟨a, h.2⟩
#align is_greatest.bdd_above IsGreatest.bddAbove

/-- If `s` has a least element, then it is bounded below. -/
theorem IsLeast.bddBelow (h : IsLeast s a) : BddBelow s :=
  ⟨a, h.2⟩
#align is_least.bdd_below IsLeast.bddBelow

theorem IsLeast.nonempty (h : IsLeast s a) : s.Nonempty :=
  ⟨a, h.1⟩
#align is_least.nonempty IsLeast.nonempty

theorem IsGreatest.nonempty (h : IsGreatest s a) : s.Nonempty :=
  ⟨a, h.1⟩
#align is_greatest.nonempty IsGreatest.nonempty

/-!
### Union and intersection
-/

@[simp]
theorem upperBounds_union : upperBounds (s ∪ t) = upperBounds s ∩ upperBounds t :=
  Subset.antisymm (fun _ hb => ⟨fun _ hx => hb (Or.inl hx), fun _ hx => hb (Or.inr hx)⟩)
    fun _ hb _ hx => hx.elim (fun hs => hb.1 hs) fun ht => hb.2 ht
#align upper_bounds_union upperBounds_union

@[simp]
theorem lowerBounds_union : lowerBounds (s ∪ t) = lowerBounds s ∩ lowerBounds t :=
  @upperBounds_union αᵒᵈ _ s t
#align lower_bounds_union lowerBounds_union

theorem union_upperBounds_subset_upperBounds_inter :
    upperBounds s ∪ upperBounds t ⊆ upperBounds (s ∩ t) :=
  union_subset (upperBounds_mono_set <| inter_subset_left _ _)
    (upperBounds_mono_set <| inter_subset_right _ _)
#align union_upper_bounds_subset_upper_bounds_inter union_upperBounds_subset_upperBounds_inter

theorem union_lowerBounds_subset_lowerBounds_inter :
    lowerBounds s ∪ lowerBounds t ⊆ lowerBounds (s ∩ t) :=
  @union_upperBounds_subset_upperBounds_inter αᵒᵈ _ s t
#align union_lower_bounds_subset_lower_bounds_inter union_lowerBounds_subset_lowerBounds_inter

theorem isLeast_union_iff {a : α} {s t : Set α} :
    IsLeast (s ∪ t) a ↔ IsLeast s a ∧ a ∈ lowerBounds t ∨ a ∈ lowerBounds s ∧ IsLeast t a := by
  simp [IsLeast, lowerBounds_union, or_and_right, and_comm (a := a ∈ t), and_assoc]
#align is_least_union_iff isLeast_union_iff

theorem isGreatest_union_iff :
    IsGreatest (s ∪ t) a ↔
      IsGreatest s a ∧ a ∈ upperBounds t ∨ a ∈ upperBounds s ∧ IsGreatest t a :=
  @isLeast_union_iff αᵒᵈ _ a s t
#align is_greatest_union_iff isGreatest_union_iff

/-- If `s` is bounded, then so is `s ∩ t` -/
theorem BddAbove.inter_of_left (h : BddAbove s) : BddAbove (s ∩ t) :=
  h.mono <| inter_subset_left s t
#align bdd_above.inter_of_left BddAbove.inter_of_left

/-- If `t` is bounded, then so is `s ∩ t` -/
theorem BddAbove.inter_of_right (h : BddAbove t) : BddAbove (s ∩ t) :=
  h.mono <| inter_subset_right s t
#align bdd_above.inter_of_right BddAbove.inter_of_right

/-- If `s` is bounded, then so is `s ∩ t` -/
theorem BddBelow.inter_of_left (h : BddBelow s) : BddBelow (s ∩ t) :=
  h.mono <| inter_subset_left s t
#align bdd_below.inter_of_left BddBelow.inter_of_left

/-- If `t` is bounded, then so is `s ∩ t` -/
theorem BddBelow.inter_of_right (h : BddBelow t) : BddBelow (s ∩ t) :=
  h.mono <| inter_subset_right s t
#align bdd_below.inter_of_right BddBelow.inter_of_right

/-- In a directed order, the union of bounded above sets is bounded above. -/
theorem BddAbove.union [IsDirected α (· ≤ ·)] {s t : Set α} :
    BddAbove s → BddAbove t → BddAbove (s ∪ t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨c, hca, hcb⟩ := exists_ge_ge a b
  rw [BddAbove, upperBounds_union]
  exact ⟨c, upperBounds_mono_mem hca ha, upperBounds_mono_mem hcb hb⟩
#align bdd_above.union BddAbove.union

/-- In a directed order, the union of two sets is bounded above if and only if both sets are. -/
theorem bddAbove_union [IsDirected α (· ≤ ·)] {s t : Set α} :
    BddAbove (s ∪ t) ↔ BddAbove s ∧ BddAbove t :=
  ⟨fun h => ⟨h.mono <| subset_union_left s t, h.mono <| subset_union_right s t⟩, fun h =>
    h.1.union h.2⟩
#align bdd_above_union bddAbove_union

/-- In a codirected order, the union of bounded below sets is bounded below. -/
theorem BddBelow.union [IsDirected α (· ≥ ·)] {s t : Set α} :
    BddBelow s → BddBelow t → BddBelow (s ∪ t) :=
  @BddAbove.union αᵒᵈ _ _ _ _
#align bdd_below.union BddBelow.union

/-- In a codirected order, the union of two sets is bounded below if and only if both sets are. -/
theorem bddBelow_union [IsDirected α (· ≥ ·)] {s t : Set α} :
    BddBelow (s ∪ t) ↔ BddBelow s ∧ BddBelow t :=
  @bddAbove_union αᵒᵈ _ _ _ _
#align bdd_below_union bddBelow_union

/-- If `a` is the least upper bound of `s` and `b` is the least upper bound of `t`,
then `a ⊔ b` is the least upper bound of `s ∪ t`. -/
theorem IsLUB.union [SemilatticeSup γ] {a b : γ} {s t : Set γ} (hs : IsLUB s a) (ht : IsLUB t b) :
    IsLUB (s ∪ t) (a ⊔ b) :=
  ⟨fun _ h =>
    h.casesOn (fun h => le_sup_of_le_left <| hs.left h) fun h => le_sup_of_le_right <| ht.left h,
    fun _ hc =>
    sup_le (hs.right fun _ hd => hc <| Or.inl hd) (ht.right fun _ hd => hc <| Or.inr hd)⟩
#align is_lub.union IsLUB.union

/-- If `a` is the greatest lower bound of `s` and `b` is the greatest lower bound of `t`,
then `a ⊓ b` is the greatest lower bound of `s ∪ t`. -/
theorem IsGLB.union [SemilatticeInf γ] {a₁ a₂ : γ} {s t : Set γ} (hs : IsGLB s a₁)
    (ht : IsGLB t a₂) : IsGLB (s ∪ t) (a₁ ⊓ a₂) :=
  hs.dual.union ht
#align is_glb.union IsGLB.union

/-- If `a` is the least element of `s` and `b` is the least element of `t`,
then `min a b` is the least element of `s ∪ t`. -/
theorem IsLeast.union [LinearOrder γ] {a b : γ} {s t : Set γ} (ha : IsLeast s a)
    (hb : IsLeast t b) : IsLeast (s ∪ t) (min a b) :=
  ⟨by rcases le_total a b with h | h <;> simp [h, ha.1, hb.1], (ha.isGLB.union hb.isGLB).1⟩
#align is_least.union IsLeast.union

/-- If `a` is the greatest element of `s` and `b` is the greatest element of `t`,
then `max a b` is the greatest element of `s ∪ t`. -/
theorem IsGreatest.union [LinearOrder γ] {a b : γ} {s t : Set γ} (ha : IsGreatest s a)
    (hb : IsGreatest t b) : IsGreatest (s ∪ t) (max a b) :=
  ⟨by rcases le_total a b with h | h <;> simp [h, ha.1, hb.1], (ha.isLUB.union hb.isLUB).1⟩
#align is_greatest.union IsGreatest.union

theorem IsLUB.inter_Ici_of_mem [LinearOrder γ] {s : Set γ} {a b : γ} (ha : IsLUB s a) (hb : b ∈ s) :
    IsLUB (s ∩ Ici b) a :=
  ⟨fun _ hx => ha.1 hx.1, fun c hc =>
    have hbc : b ≤ c := hc ⟨hb, le_rfl⟩
    ha.2 fun x hx => ((le_total x b).elim fun hxb => hxb.trans hbc) fun hbx => hc ⟨hx, hbx⟩⟩
#align is_lub.inter_Ici_of_mem IsLUB.inter_Ici_of_mem

theorem IsGLB.inter_Iic_of_mem [LinearOrder γ] {s : Set γ} {a b : γ} (ha : IsGLB s a) (hb : b ∈ s) :
    IsGLB (s ∩ Iic b) a :=
  ha.dual.inter_Ici_of_mem hb
#align is_glb.inter_Iic_of_mem IsGLB.inter_Iic_of_mem

theorem bddAbove_iff_exists_ge [SemilatticeSup γ] {s : Set γ} (x₀ : γ) :
    BddAbove s ↔ ∃ x, x₀ ≤ x ∧ ∀ y ∈ s, y ≤ x := by
  rw [bddAbove_def, exists_ge_and_iff_exists]
  exact Monotone.ball fun x _ => monotone_le
#align bdd_above_iff_exists_ge bddAbove_iff_exists_ge

theorem bddBelow_iff_exists_le [SemilatticeInf γ] {s : Set γ} (x₀ : γ) :
    BddBelow s ↔ ∃ x, x ≤ x₀ ∧ ∀ y ∈ s, x ≤ y :=
  bddAbove_iff_exists_ge (toDual x₀)
#align bdd_below_iff_exists_le bddBelow_iff_exists_le

theorem BddAbove.exists_ge [SemilatticeSup γ] {s : Set γ} (hs : BddAbove s) (x₀ : γ) :
    ∃ x, x₀ ≤ x ∧ ∀ y ∈ s, y ≤ x :=
  (bddAbove_iff_exists_ge x₀).mp hs
#align bdd_above.exists_ge BddAbove.exists_ge

theorem BddBelow.exists_le [SemilatticeInf γ] {s : Set γ} (hs : BddBelow s) (x₀ : γ) :
    ∃ x, x ≤ x₀ ∧ ∀ y ∈ s, x ≤ y :=
  (bddBelow_iff_exists_le x₀).mp hs
#align bdd_below.exists_le BddBelow.exists_le

/-!
### Specific sets
#### Unbounded intervals
-/


theorem isLeast_Ici : IsLeast (Ici a) a :=
  ⟨left_mem_Ici, fun _ => id⟩
#align is_least_Ici isLeast_Ici

theorem isGreatest_Iic : IsGreatest (Iic a) a :=
  ⟨right_mem_Iic, fun _ => id⟩
#align is_greatest_Iic isGreatest_Iic

theorem isLUB_Iic : IsLUB (Iic a) a :=
  isGreatest_Iic.isLUB
#align is_lub_Iic isLUB_Iic

theorem isGLB_Ici : IsGLB (Ici a) a :=
  isLeast_Ici.isGLB
#align is_glb_Ici isGLB_Ici

theorem upperBounds_Iic : upperBounds (Iic a) = Ici a :=
  isLUB_Iic.upperBounds_eq
#align upper_bounds_Iic upperBounds_Iic

theorem lowerBounds_Ici : lowerBounds (Ici a) = Iic a :=
  isGLB_Ici.lowerBounds_eq
#align lower_bounds_Ici lowerBounds_Ici

theorem bddAbove_Iic : BddAbove (Iic a) :=
  isLUB_Iic.bddAbove
#align bdd_above_Iic bddAbove_Iic

theorem bddBelow_Ici : BddBelow (Ici a) :=
  isGLB_Ici.bddBelow
#align bdd_below_Ici bddBelow_Ici

theorem bddAbove_Iio : BddAbove (Iio a) :=
  ⟨a, fun _ hx => le_of_lt hx⟩
#align bdd_above_Iio bddAbove_Iio

theorem bddBelow_Ioi : BddBelow (Ioi a) :=
  ⟨a, fun _ hx => le_of_lt hx⟩
#align bdd_below_Ioi bddBelow_Ioi

theorem lub_Iio_le (a : α) (hb : IsLUB (Iio a) b) : b ≤ a :=
  (isLUB_le_iff hb).mpr fun _ hk => le_of_lt hk
#align lub_Iio_le lub_Iio_le

theorem le_glb_Ioi (a : α) (hb : IsGLB (Ioi a) b) : a ≤ b :=
  @lub_Iio_le αᵒᵈ _ _ a hb
#align le_glb_Ioi le_glb_Ioi

theorem lub_Iio_eq_self_or_Iio_eq_Iic [PartialOrder γ] {j : γ} (i : γ) (hj : IsLUB (Iio i) j) :
    j = i ∨ Iio i = Iic j := by
  cases' eq_or_lt_of_le (lub_Iio_le i hj) with hj_eq_i hj_lt_i
  · exact Or.inl hj_eq_i
  · right
    exact Set.ext fun k => ⟨fun hk_lt => hj.1 hk_lt, fun hk_le_j => lt_of_le_of_lt hk_le_j hj_lt_i⟩
#align lub_Iio_eq_self_or_Iio_eq_Iic lub_Iio_eq_self_or_Iio_eq_Iic

theorem glb_Ioi_eq_self_or_Ioi_eq_Ici [PartialOrder γ] {j : γ} (i : γ) (hj : IsGLB (Ioi i) j) :
    j = i ∨ Ioi i = Ici j :=
  @lub_Iio_eq_self_or_Iio_eq_Iic γᵒᵈ _ j i hj
#align glb_Ioi_eq_self_or_Ioi_eq_Ici glb_Ioi_eq_self_or_Ioi_eq_Ici

section

variable [LinearOrder γ]

theorem exists_lub_Iio (i : γ) : ∃ j, IsLUB (Iio i) j := by
  by_cases h_exists_lt : ∃ j, j ∈ upperBounds (Iio i) ∧ j < i
  · obtain ⟨j, hj_ub, hj_lt_i⟩ := h_exists_lt
    exact ⟨j, hj_ub, fun k hk_ub => hk_ub hj_lt_i⟩
  · refine ⟨i, fun j hj => le_of_lt hj, ?_⟩
    rw [mem_lowerBounds]
    by_contra h
    refine h_exists_lt ?_
    push_neg at h
    exact h
#align exists_lub_Iio exists_lub_Iio

theorem exists_glb_Ioi (i : γ) : ∃ j, IsGLB (Ioi i) j :=
  @exists_lub_Iio γᵒᵈ _ i
#align exists_glb_Ioi exists_glb_Ioi

variable [DenselyOrdered γ]

theorem isLUB_Iio {a : γ} : IsLUB (Iio a) a :=
  ⟨fun _ hx => le_of_lt hx, fun _ hy => le_of_forall_ge_of_dense hy⟩
#align is_lub_Iio isLUB_Iio

theorem isGLB_Ioi {a : γ} : IsGLB (Ioi a) a :=
  @isLUB_Iio γᵒᵈ _ _ a
#align is_glb_Ioi isGLB_Ioi

theorem upperBounds_Iio {a : γ} : upperBounds (Iio a) = Ici a :=
  isLUB_Iio.upperBounds_eq
#align upper_bounds_Iio upperBounds_Iio

theorem lowerBounds_Ioi {a : γ} : lowerBounds (Ioi a) = Iic a :=
  isGLB_Ioi.lowerBounds_eq
#align lower_bounds_Ioi lowerBounds_Ioi

end

/-!
#### Singleton
-/


theorem isGreatest_singleton : IsGreatest {a} a :=
  ⟨mem_singleton a, fun _ hx => le_of_eq <| eq_of_mem_singleton hx⟩
#align is_greatest_singleton isGreatest_singleton

theorem isLeast_singleton : IsLeast {a} a :=
  @isGreatest_singleton αᵒᵈ _ a
#align is_least_singleton isLeast_singleton

theorem isLUB_singleton : IsLUB {a} a :=
  isGreatest_singleton.isLUB
#align is_lub_singleton isLUB_singleton

theorem isGLB_singleton : IsGLB {a} a :=
  isLeast_singleton.isGLB
#align is_glb_singleton isGLB_singleton

theorem bddAbove_singleton : BddAbove ({a} : Set α) :=
  isLUB_singleton.bddAbove
#align bdd_above_singleton bddAbove_singleton

theorem bddBelow_singleton : BddBelow ({a} : Set α) :=
  isGLB_singleton.bddBelow
#align bdd_below_singleton bddBelow_singleton

@[simp]
theorem upperBounds_singleton : upperBounds {a} = Ici a :=
  isLUB_singleton.upperBounds_eq
#align upper_bounds_singleton upperBounds_singleton

@[simp]
theorem lowerBounds_singleton : lowerBounds {a} = Iic a :=
  isGLB_singleton.lowerBounds_eq
#align lower_bounds_singleton lowerBounds_singleton

/-!
#### Bounded intervals
-/


theorem bddAbove_Icc : BddAbove (Icc a b) :=
  ⟨b, fun _ => And.right⟩
#align bdd_above_Icc bddAbove_Icc

theorem bddBelow_Icc : BddBelow (Icc a b) :=
  ⟨a, fun _ => And.left⟩
#align bdd_below_Icc bddBelow_Icc

theorem bddAbove_Ico : BddAbove (Ico a b) :=
  bddAbove_Icc.mono Ico_subset_Icc_self
#align bdd_above_Ico bddAbove_Ico

theorem bddBelow_Ico : BddBelow (Ico a b) :=
  bddBelow_Icc.mono Ico_subset_Icc_self
#align bdd_below_Ico bddBelow_Ico

theorem bddAbove_Ioc : BddAbove (Ioc a b) :=
  bddAbove_Icc.mono Ioc_subset_Icc_self
#align bdd_above_Ioc bddAbove_Ioc

theorem bddBelow_Ioc : BddBelow (Ioc a b) :=
  bddBelow_Icc.mono Ioc_subset_Icc_self
#align bdd_below_Ioc bddBelow_Ioc

theorem bddAbove_Ioo : BddAbove (Ioo a b) :=
  bddAbove_Icc.mono Ioo_subset_Icc_self
#align bdd_above_Ioo bddAbove_Ioo

theorem bddBelow_Ioo : BddBelow (Ioo a b) :=
  bddBelow_Icc.mono Ioo_subset_Icc_self
#align bdd_below_Ioo bddBelow_Ioo

theorem isGreatest_Icc (h : a ≤ b) : IsGreatest (Icc a b) b :=
  ⟨right_mem_Icc.2 h, fun _ => And.right⟩
#align is_greatest_Icc isGreatest_Icc

theorem isLUB_Icc (h : a ≤ b) : IsLUB (Icc a b) b :=
  (isGreatest_Icc h).isLUB
#align is_lub_Icc isLUB_Icc

theorem upperBounds_Icc (h : a ≤ b) : upperBounds (Icc a b) = Ici b :=
  (isLUB_Icc h).upperBounds_eq
#align upper_bounds_Icc upperBounds_Icc

theorem isLeast_Icc (h : a ≤ b) : IsLeast (Icc a b) a :=
  ⟨left_mem_Icc.2 h, fun _ => And.left⟩
#align is_least_Icc isLeast_Icc

theorem isGLB_Icc (h : a ≤ b) : IsGLB (Icc a b) a :=
  (isLeast_Icc h).isGLB
#align is_glb_Icc isGLB_Icc

theorem lowerBounds_Icc (h : a ≤ b) : lowerBounds (Icc a b) = Iic a :=
  (isGLB_Icc h).lowerBounds_eq
#align lower_bounds_Icc lowerBounds_Icc

theorem isGreatest_Ioc (h : a < b) : IsGreatest (Ioc a b) b :=
  ⟨right_mem_Ioc.2 h, fun _ => And.right⟩
#align is_greatest_Ioc isGreatest_Ioc

theorem isLUB_Ioc (h : a < b) : IsLUB (Ioc a b) b :=
  (isGreatest_Ioc h).isLUB
#align is_lub_Ioc isLUB_Ioc

theorem upperBounds_Ioc (h : a < b) : upperBounds (Ioc a b) = Ici b :=
  (isLUB_Ioc h).upperBounds_eq
#align upper_bounds_Ioc upperBounds_Ioc

theorem isLeast_Ico (h : a < b) : IsLeast (Ico a b) a :=
  ⟨left_mem_Ico.2 h, fun _ => And.left⟩
#align is_least_Ico isLeast_Ico

theorem isGLB_Ico (h : a < b) : IsGLB (Ico a b) a :=
  (isLeast_Ico h).isGLB
#align is_glb_Ico isGLB_Ico

theorem lowerBounds_Ico (h : a < b) : lowerBounds (Ico a b) = Iic a :=
  (isGLB_Ico h).lowerBounds_eq
#align lower_bounds_Ico lowerBounds_Ico

section

variable [SemilatticeSup γ] [DenselyOrdered γ]

theorem isGLB_Ioo {a b : γ} (h : a < b) : IsGLB (Ioo a b) a :=
  ⟨fun x hx => hx.1.le, fun x hx => by
    cases' eq_or_lt_of_le (le_sup_right : a ≤ x ⊔ a) with h₁ h₂
    · exact h₁.symm ▸ le_sup_left
    obtain ⟨y, lty, ylt⟩ := exists_between h₂
    apply (not_lt_of_le (sup_le (hx ⟨lty, ylt.trans_le (sup_le _ h.le)⟩) lty.le) ylt).elim
    obtain ⟨u, au, ub⟩ := exists_between h
    apply (hx ⟨au, ub⟩).trans ub.le⟩
#align is_glb_Ioo isGLB_Ioo

theorem lowerBounds_Ioo {a b : γ} (hab : a < b) : lowerBounds (Ioo a b) = Iic a :=
  (isGLB_Ioo hab).lowerBounds_eq
#align lower_bounds_Ioo lowerBounds_Ioo

theorem isGLB_Ioc {a b : γ} (hab : a < b) : IsGLB (Ioc a b) a :=
  (isGLB_Ioo hab).of_subset_of_superset (isGLB_Icc hab.le) Ioo_subset_Ioc_self Ioc_subset_Icc_self
#align is_glb_Ioc isGLB_Ioc

theorem lowerBounds_Ioc {a b : γ} (hab : a < b) : lowerBounds (Ioc a b) = Iic a :=
  (isGLB_Ioc hab).lowerBounds_eq
#align lower_bound_Ioc lowerBounds_Ioc

end

section

variable [SemilatticeInf γ] [DenselyOrdered γ]

theorem isLUB_Ioo {a b : γ} (hab : a < b) : IsLUB (Ioo a b) b := by
  simpa only [dual_Ioo] using isGLB_Ioo hab.dual
#align is_lub_Ioo isLUB_Ioo

theorem upperBounds_Ioo {a b : γ} (hab : a < b) : upperBounds (Ioo a b) = Ici b :=
  (isLUB_Ioo hab).upperBounds_eq
#align upper_bounds_Ioo upperBounds_Ioo

theorem isLUB_Ico {a b : γ} (hab : a < b) : IsLUB (Ico a b) b := by
  simpa only [dual_Ioc] using isGLB_Ioc hab.dual
#align is_lub_Ico isLUB_Ico

theorem upperBounds_Ico {a b : γ} (hab : a < b) : upperBounds (Ico a b) = Ici b :=
  (isLUB_Ico hab).upperBounds_eq
#align upper_bounds_Ico upperBounds_Ico

end

theorem bddBelow_iff_subset_Ici : BddBelow s ↔ ∃ a, s ⊆ Ici a :=
  Iff.rfl
#align bdd_below_iff_subset_Ici bddBelow_iff_subset_Ici

theorem bddAbove_iff_subset_Iic : BddAbove s ↔ ∃ a, s ⊆ Iic a :=
  Iff.rfl
#align bdd_above_iff_subset_Iic bddAbove_iff_subset_Iic

theorem bddBelow_bddAbove_iff_subset_Icc : BddBelow s ∧ BddAbove s ↔ ∃ a b, s ⊆ Icc a b := by
  simp [Ici_inter_Iic.symm, subset_inter_iff, bddBelow_iff_subset_Ici,
    bddAbove_iff_subset_Iic, exists_and_left, exists_and_right]
#align bdd_below_bdd_above_iff_subset_Icc bddBelow_bddAbove_iff_subset_Icc

/-!
#### Univ
-/

@[simp] theorem isGreatest_univ_iff : IsGreatest univ a ↔ IsTop a := by
  simp [IsGreatest, mem_upperBounds, IsTop]
#align is_greatest_univ_iff isGreatest_univ_iff

theorem isGreatest_univ [OrderTop α] : IsGreatest (univ : Set α) ⊤ :=
  isGreatest_univ_iff.2 isTop_top
#align is_greatest_univ isGreatest_univ

@[simp]
theorem OrderTop.upperBounds_univ [PartialOrder γ] [OrderTop γ] :
    upperBounds (univ : Set γ) = {⊤} := by rw [isGreatest_univ.upperBounds_eq, Ici_top]
#align order_top.upper_bounds_univ OrderTop.upperBounds_univ

theorem isLUB_univ [OrderTop α] : IsLUB (univ : Set α) ⊤ :=
  isGreatest_univ.isLUB
#align is_lub_univ isLUB_univ

@[simp]
theorem OrderBot.lowerBounds_univ [PartialOrder γ] [OrderBot γ] :
    lowerBounds (univ : Set γ) = {⊥} :=
  @OrderTop.upperBounds_univ γᵒᵈ _ _
#align order_bot.lower_bounds_univ OrderBot.lowerBounds_univ

@[simp] theorem isLeast_univ_iff : IsLeast univ a ↔ IsBot a :=
  @isGreatest_univ_iff αᵒᵈ _ _
#align is_least_univ_iff isLeast_univ_iff

theorem isLeast_univ [OrderBot α] : IsLeast (univ : Set α) ⊥ :=
  @isGreatest_univ αᵒᵈ _ _
#align is_least_univ isLeast_univ

theorem isGLB_univ [OrderBot α] : IsGLB (univ : Set α) ⊥ :=
  isLeast_univ.isGLB
#align is_glb_univ isGLB_univ

@[simp]
theorem NoMaxOrder.upperBounds_univ [NoMaxOrder α] : upperBounds (univ : Set α) = ∅ :=
  eq_empty_of_subset_empty fun b hb =>
    let ⟨_, hx⟩ := exists_gt b
    not_le_of_lt hx (hb trivial)
#align no_max_order.upper_bounds_univ NoMaxOrder.upperBounds_univ

@[simp]
theorem NoMinOrder.lowerBounds_univ [NoMinOrder α] : lowerBounds (univ : Set α) = ∅ :=
  @NoMaxOrder.upperBounds_univ αᵒᵈ _ _
#align no_min_order.lower_bounds_univ NoMinOrder.lowerBounds_univ

@[simp]
theorem not_bddAbove_univ [NoMaxOrder α] : ¬BddAbove (univ : Set α) := by simp [BddAbove]
#align not_bdd_above_univ not_bddAbove_univ

@[simp]
theorem not_bddBelow_univ [NoMinOrder α] : ¬BddBelow (univ : Set α) :=
  @not_bddAbove_univ αᵒᵈ _ _
#align not_bdd_below_univ not_bddBelow_univ

/-!
#### Empty set
-/


@[simp]
theorem upperBounds_empty : upperBounds (∅ : Set α) = univ := by
  simp only [upperBounds, eq_univ_iff_forall, mem_setOf_eq, forall_mem_empty, forall_true_iff]
#align upper_bounds_empty upperBounds_empty

@[simp]
theorem lowerBounds_empty : lowerBounds (∅ : Set α) = univ :=
  @upperBounds_empty αᵒᵈ _
#align lower_bounds_empty lowerBounds_empty

@[simp]
theorem bddAbove_empty [Nonempty α] : BddAbove (∅ : Set α) := by
  simp only [BddAbove, upperBounds_empty, univ_nonempty]
#align bdd_above_empty bddAbove_empty

@[simp]
theorem bddBelow_empty [Nonempty α] : BddBelow (∅ : Set α) := by
  simp only [BddBelow, lowerBounds_empty, univ_nonempty]
#align bdd_below_empty bddBelow_empty

@[simp] theorem isGLB_empty_iff : IsGLB ∅ a ↔ IsTop a := by
  simp [IsGLB]
#align is_glb_empty_iff isGLB_empty_iff

@[simp] theorem isLUB_empty_iff : IsLUB ∅ a ↔ IsBot a :=
  @isGLB_empty_iff αᵒᵈ _ _
#align is_lub_empty_iff isLUB_empty_iff

theorem isGLB_empty [OrderTop α] : IsGLB ∅ (⊤ : α) :=
  isGLB_empty_iff.2 isTop_top
#align is_glb_empty isGLB_empty

theorem isLUB_empty [OrderBot α] : IsLUB ∅ (⊥ : α) :=
  @isGLB_empty αᵒᵈ _ _
#align is_lub_empty isLUB_empty

theorem IsLUB.nonempty [NoMinOrder α] (hs : IsLUB s a) : s.Nonempty :=
  let ⟨a', ha'⟩ := exists_lt a
  nonempty_iff_ne_empty.2 fun h =>
    not_le_of_lt ha' <| hs.right <| by rw [h, upperBounds_empty]; exact mem_univ _
#align is_lub.nonempty IsLUB.nonempty

theorem IsGLB.nonempty [NoMaxOrder α] (hs : IsGLB s a) : s.Nonempty :=
  hs.dual.nonempty
#align is_glb.nonempty IsGLB.nonempty

theorem nonempty_of_not_bddAbove [ha : Nonempty α] (h : ¬BddAbove s) : s.Nonempty :=
  (Nonempty.elim ha) fun x => (not_bddAbove_iff'.1 h x).imp fun _ ha => ha.1
#align nonempty_of_not_bdd_above nonempty_of_not_bddAbove

theorem nonempty_of_not_bddBelow [Nonempty α] (h : ¬BddBelow s) : s.Nonempty :=
  @nonempty_of_not_bddAbove αᵒᵈ _ _ _ h
#align nonempty_of_not_bdd_below nonempty_of_not_bddBelow

/-!
#### insert
-/


/-- Adding a point to a set preserves its boundedness above. -/
@[simp]
theorem bddAbove_insert [IsDirected α (· ≤ ·)] {s : Set α} {a : α} :
    BddAbove (insert a s) ↔ BddAbove s := by
  simp only [insert_eq, bddAbove_union, bddAbove_singleton, true_and_iff]
#align bdd_above_insert bddAbove_insert

protected theorem BddAbove.insert [IsDirected α (· ≤ ·)] {s : Set α} (a : α) :
    BddAbove s → BddAbove (insert a s) :=
  bddAbove_insert.2
#align bdd_above.insert BddAbove.insert

/-- Adding a point to a set preserves its boundedness below. -/
@[simp]
theorem bddBelow_insert [IsDirected α (· ≥ ·)] {s : Set α} {a : α} :
    BddBelow (insert a s) ↔ BddBelow s := by
  simp only [insert_eq, bddBelow_union, bddBelow_singleton, true_and_iff]
#align bdd_below_insert bddBelow_insert

protected theorem BddBelow.insert [IsDirected α (· ≥ ·)] {s : Set α} (a : α) :
    BddBelow s → BddBelow (insert a s) :=
  bddBelow_insert.2
#align bdd_below.insert BddBelow.insert

protected theorem IsLUB.insert [SemilatticeSup γ] (a) {b} {s : Set γ} (hs : IsLUB s b) :
    IsLUB (insert a s) (a ⊔ b) := by
  rw [insert_eq]
  exact isLUB_singleton.union hs
#align is_lub.insert IsLUB.insert

protected theorem IsGLB.insert [SemilatticeInf γ] (a) {b} {s : Set γ} (hs : IsGLB s b) :
    IsGLB (insert a s) (a ⊓ b) := by
  rw [insert_eq]
  exact isGLB_singleton.union hs
#align is_glb.insert IsGLB.insert

protected theorem IsGreatest.insert [LinearOrder γ] (a) {b} {s : Set γ} (hs : IsGreatest s b) :
    IsGreatest (insert a s) (max a b) := by
  rw [insert_eq]
  exact isGreatest_singleton.union hs
#align is_greatest.insert IsGreatest.insert

protected theorem IsLeast.insert [LinearOrder γ] (a) {b} {s : Set γ} (hs : IsLeast s b) :
    IsLeast (insert a s) (min a b) := by
  rw [insert_eq]
  exact isLeast_singleton.union hs
#align is_least.insert IsLeast.insert

@[simp]
theorem upperBounds_insert (a : α) (s : Set α) :
    upperBounds (insert a s) = Ici a ∩ upperBounds s := by
  rw [insert_eq, upperBounds_union, upperBounds_singleton]
#align upper_bounds_insert upperBounds_insert

@[simp]
theorem lowerBounds_insert (a : α) (s : Set α) :
    lowerBounds (insert a s) = Iic a ∩ lowerBounds s := by
  rw [insert_eq, lowerBounds_union, lowerBounds_singleton]
#align lower_bounds_insert lowerBounds_insert

/-- When there is a global maximum, every set is bounded above. -/
@[simp]
protected theorem OrderTop.bddAbove [OrderTop α] (s : Set α) : BddAbove s :=
  ⟨⊤, fun a _ => OrderTop.le_top a⟩
#align order_top.bdd_above OrderTop.bddAbove

/-- When there is a global minimum, every set is bounded below. -/
@[simp]
protected theorem OrderBot.bddBelow [OrderBot α] (s : Set α) : BddBelow s :=
  ⟨⊥, fun a _ => OrderBot.bot_le a⟩
#align order_bot.bdd_below OrderBot.bddBelow

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


theorem isLUB_pair [SemilatticeSup γ] {a b : γ} : IsLUB {a, b} (a ⊔ b) :=
  isLUB_singleton.insert _
#align is_lub_pair isLUB_pair

theorem isGLB_pair [SemilatticeInf γ] {a b : γ} : IsGLB {a, b} (a ⊓ b) :=
  isGLB_singleton.insert _
#align is_glb_pair isGLB_pair

theorem isLeast_pair [LinearOrder γ] {a b : γ} : IsLeast {a, b} (min a b) :=
  isLeast_singleton.insert _
#align is_least_pair isLeast_pair

theorem isGreatest_pair [LinearOrder γ] {a b : γ} : IsGreatest {a, b} (max a b) :=
  isGreatest_singleton.insert _
#align is_greatest_pair isGreatest_pair

/-!
#### Lower/upper bounds
-/


@[simp]
theorem isLUB_lowerBounds : IsLUB (lowerBounds s) a ↔ IsGLB s a :=
  ⟨fun H => ⟨fun _ hx => H.2 <| subset_upperBounds_lowerBounds s hx, H.1⟩, IsGreatest.isLUB⟩
#align is_lub_lower_bounds isLUB_lowerBounds

@[simp]
theorem isGLB_upperBounds : IsGLB (upperBounds s) a ↔ IsLUB s a :=
  @isLUB_lowerBounds αᵒᵈ _ _ _
#align is_glb_upper_bounds isGLB_upperBounds

end

/-!
### (In)equalities with the least upper bound and the greatest lower bound
-/


section Preorder

variable [Preorder α] {s : Set α} {a b : α}

theorem lowerBounds_le_upperBounds (ha : a ∈ lowerBounds s) (hb : b ∈ upperBounds s) :
    s.Nonempty → a ≤ b
  | ⟨_, hc⟩ => le_trans (ha hc) (hb hc)
#align lower_bounds_le_upper_bounds lowerBounds_le_upperBounds

theorem isGLB_le_isLUB (ha : IsGLB s a) (hb : IsLUB s b) (hs : s.Nonempty) : a ≤ b :=
  lowerBounds_le_upperBounds ha.1 hb.1 hs
#align is_glb_le_is_lub isGLB_le_isLUB

theorem isLUB_lt_iff (ha : IsLUB s a) : a < b ↔ ∃ c ∈ upperBounds s, c < b :=
  ⟨fun hb => ⟨a, ha.1, hb⟩, fun ⟨_, hcs, hcb⟩ => lt_of_le_of_lt (ha.2 hcs) hcb⟩
#align is_lub_lt_iff isLUB_lt_iff

theorem lt_isGLB_iff (ha : IsGLB s a) : b < a ↔ ∃ c ∈ lowerBounds s, b < c :=
  isLUB_lt_iff ha.dual
#align lt_is_glb_iff lt_isGLB_iff

theorem le_of_isLUB_le_isGLB {x y} (ha : IsGLB s a) (hb : IsLUB s b) (hab : b ≤ a) (hx : x ∈ s)
    (hy : y ∈ s) : x ≤ y :=
  calc
    x ≤ b := hb.1 hx
    _ ≤ a := hab
    _ ≤ y := ha.1 hy
#align le_of_is_lub_le_is_glb le_of_isLUB_le_isGLB

end Preorder

section PartialOrder

variable [PartialOrder α] {s : Set α} {a b : α}

theorem IsLeast.unique (Ha : IsLeast s a) (Hb : IsLeast s b) : a = b :=
  le_antisymm (Ha.right Hb.left) (Hb.right Ha.left)
#align is_least.unique IsLeast.unique

theorem IsLeast.isLeast_iff_eq (Ha : IsLeast s a) : IsLeast s b ↔ a = b :=
  Iff.intro Ha.unique fun h => h ▸ Ha
#align is_least.is_least_iff_eq IsLeast.isLeast_iff_eq

theorem IsGreatest.unique (Ha : IsGreatest s a) (Hb : IsGreatest s b) : a = b :=
  le_antisymm (Hb.right Ha.left) (Ha.right Hb.left)
#align is_greatest.unique IsGreatest.unique

theorem IsGreatest.isGreatest_iff_eq (Ha : IsGreatest s a) : IsGreatest s b ↔ a = b :=
  Iff.intro Ha.unique fun h => h ▸ Ha
#align is_greatest.is_greatest_iff_eq IsGreatest.isGreatest_iff_eq

theorem IsLUB.unique (Ha : IsLUB s a) (Hb : IsLUB s b) : a = b :=
  IsLeast.unique Ha Hb
#align is_lub.unique IsLUB.unique

theorem IsGLB.unique (Ha : IsGLB s a) (Hb : IsGLB s b) : a = b :=
  IsGreatest.unique Ha Hb
#align is_glb.unique IsGLB.unique

theorem Set.subsingleton_of_isLUB_le_isGLB (Ha : IsGLB s a) (Hb : IsLUB s b) (hab : b ≤ a) :
    s.Subsingleton := fun _ hx _ hy =>
  le_antisymm (le_of_isLUB_le_isGLB Ha Hb hab hx hy) (le_of_isLUB_le_isGLB Ha Hb hab hy hx)
#align set.subsingleton_of_is_lub_le_is_glb Set.subsingleton_of_isLUB_le_isGLB

theorem isGLB_lt_isLUB_of_ne (Ha : IsGLB s a) (Hb : IsLUB s b) {x y} (Hx : x ∈ s) (Hy : y ∈ s)
    (Hxy : x ≠ y) : a < b :=
  lt_iff_le_not_le.2
    ⟨lowerBounds_le_upperBounds Ha.1 Hb.1 ⟨x, Hx⟩, fun hab =>
      Hxy <| Set.subsingleton_of_isLUB_le_isGLB Ha Hb hab Hx Hy⟩
#align is_glb_lt_is_lub_of_ne isGLB_lt_isLUB_of_ne

end PartialOrder

section LinearOrder

variable [LinearOrder α] {s : Set α} {a b : α}

theorem lt_isLUB_iff (h : IsLUB s a) : b < a ↔ ∃ c ∈ s, b < c := by
  simp_rw [← not_le, isLUB_le_iff h, mem_upperBounds, not_forall, not_le, exists_prop]
#align lt_is_lub_iff lt_isLUB_iff

theorem isGLB_lt_iff (h : IsGLB s a) : a < b ↔ ∃ c ∈ s, c < b :=
  lt_isLUB_iff h.dual
#align is_glb_lt_iff isGLB_lt_iff

theorem IsLUB.exists_between (h : IsLUB s a) (hb : b < a) : ∃ c ∈ s, b < c ∧ c ≤ a :=
  let ⟨c, hcs, hbc⟩ := (lt_isLUB_iff h).1 hb
  ⟨c, hcs, hbc, h.1 hcs⟩
#align is_lub.exists_between IsLUB.exists_between

theorem IsLUB.exists_between' (h : IsLUB s a) (h' : a ∉ s) (hb : b < a) : ∃ c ∈ s, b < c ∧ c < a :=
  let ⟨c, hcs, hbc, hca⟩ := h.exists_between hb
  ⟨c, hcs, hbc, hca.lt_of_ne fun hac => h' <| hac ▸ hcs⟩
#align is_lub.exists_between' IsLUB.exists_between'

theorem IsGLB.exists_between (h : IsGLB s a) (hb : a < b) : ∃ c ∈ s, a ≤ c ∧ c < b :=
  let ⟨c, hcs, hbc⟩ := (isGLB_lt_iff h).1 hb
  ⟨c, hcs, h.1 hcs, hbc⟩
#align is_glb.exists_between IsGLB.exists_between

theorem IsGLB.exists_between' (h : IsGLB s a) (h' : a ∉ s) (hb : a < b) : ∃ c ∈ s, a < c ∧ c < b :=
  let ⟨c, hcs, hac, hcb⟩ := h.exists_between hb
  ⟨c, hcs, hac.lt_of_ne fun hac => h' <| hac.symm ▸ hcs, hcb⟩
#align is_glb.exists_between' IsGLB.exists_between'

end LinearOrder

/-!
### Images of upper/lower bounds under monotone functions
-/


namespace MonotoneOn

variable [Preorder α] [Preorder β] {f : α → β} {s t : Set α} (Hf : MonotoneOn f t) {a : α}
  (Hst : s ⊆ t)

theorem mem_upperBounds_image (Has : a ∈ upperBounds s) (Hat : a ∈ t) :
    f a ∈ upperBounds (f '' s) :=
  forall_mem_image.2 fun _ H => Hf (Hst H) Hat (Has H)
#align monotone_on.mem_upper_bounds_image MonotoneOn.mem_upperBounds_image

theorem mem_upperBounds_image_self : a ∈ upperBounds t → a ∈ t → f a ∈ upperBounds (f '' t) :=
  Hf.mem_upperBounds_image subset_rfl
#align monotone_on.mem_upper_bounds_image_self MonotoneOn.mem_upperBounds_image_self

theorem mem_lowerBounds_image (Has : a ∈ lowerBounds s) (Hat : a ∈ t) :
    f a ∈ lowerBounds (f '' s) :=
  forall_mem_image.2 fun _ H => Hf Hat (Hst H) (Has H)
#align monotone_on.mem_lower_bounds_image MonotoneOn.mem_lowerBounds_image

theorem mem_lowerBounds_image_self : a ∈ lowerBounds t → a ∈ t → f a ∈ lowerBounds (f '' t) :=
  Hf.mem_lowerBounds_image subset_rfl
#align monotone_on.mem_lower_bounds_image_self MonotoneOn.mem_lowerBounds_image_self

theorem image_upperBounds_subset_upperBounds_image (Hst : s ⊆ t) :
    f '' (upperBounds s ∩ t) ⊆ upperBounds (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩
  exact Hf.mem_upperBounds_image Hst ha.1 ha.2
#align monotone_on.image_upper_bounds_subset_upper_bounds_image MonotoneOn.image_upperBounds_subset_upperBounds_image

theorem image_lowerBounds_subset_lowerBounds_image :
    f '' (lowerBounds s ∩ t) ⊆ lowerBounds (f '' s) :=
  Hf.dual.image_upperBounds_subset_upperBounds_image Hst
#align monotone_on.image_lower_bounds_subset_lower_bounds_image MonotoneOn.image_lowerBounds_subset_lowerBounds_image

/-- The image under a monotone function on a set `t` of a subset which has an upper bound in `t`
  is bounded above. -/
theorem map_bddAbove : (upperBounds s ∩ t).Nonempty → BddAbove (f '' s) := fun ⟨C, hs, ht⟩ =>
  ⟨f C, Hf.mem_upperBounds_image Hst hs ht⟩
#align monotone_on.map_bdd_above MonotoneOn.map_bddAbove

/-- The image under a monotone function on a set `t` of a subset which has a lower bound in `t`
  is bounded below. -/
theorem map_bddBelow : (lowerBounds s ∩ t).Nonempty → BddBelow (f '' s) := fun ⟨C, hs, ht⟩ =>
  ⟨f C, Hf.mem_lowerBounds_image Hst hs ht⟩
#align monotone_on.map_bdd_below MonotoneOn.map_bddBelow

/-- A monotone map sends a least element of a set to a least element of its image. -/
theorem map_isLeast (Ha : IsLeast t a) : IsLeast (f '' t) (f a) :=
  ⟨mem_image_of_mem _ Ha.1, Hf.mem_lowerBounds_image_self Ha.2 Ha.1⟩
#align monotone_on.map_is_least MonotoneOn.map_isLeast

/-- A monotone map sends a greatest element of a set to a greatest element of its image. -/
theorem map_isGreatest (Ha : IsGreatest t a) : IsGreatest (f '' t) (f a) :=
  ⟨mem_image_of_mem _ Ha.1, Hf.mem_upperBounds_image_self Ha.2 Ha.1⟩
#align monotone_on.map_is_greatest MonotoneOn.map_isGreatest

end MonotoneOn

namespace AntitoneOn

variable [Preorder α] [Preorder β] {f : α → β} {s t : Set α} (Hf : AntitoneOn f t) {a : α}
  (Hst : s ⊆ t)

theorem mem_upperBounds_image (Has : a ∈ lowerBounds s) : a ∈ t → f a ∈ upperBounds (f '' s) :=
  Hf.dual_right.mem_lowerBounds_image Hst Has
#align antitone_on.mem_upper_bounds_image AntitoneOn.mem_upperBounds_image

theorem mem_upperBounds_image_self : a ∈ lowerBounds t → a ∈ t → f a ∈ upperBounds (f '' t) :=
  Hf.dual_right.mem_lowerBounds_image_self
#align antitone_on.mem_upper_bounds_image_self AntitoneOn.mem_upperBounds_image_self

theorem mem_lowerBounds_image : a ∈ upperBounds s → a ∈ t → f a ∈ lowerBounds (f '' s) :=
  Hf.dual_right.mem_upperBounds_image Hst
#align antitone_on.mem_lower_bounds_image AntitoneOn.mem_lowerBounds_image

theorem mem_lowerBounds_image_self : a ∈ upperBounds t → a ∈ t → f a ∈ lowerBounds (f '' t) :=
  Hf.dual_right.mem_upperBounds_image_self
#align antitone_on.mem_lower_bounds_image_self AntitoneOn.mem_lowerBounds_image_self

theorem image_lowerBounds_subset_upperBounds_image :
    f '' (lowerBounds s ∩ t) ⊆ upperBounds (f '' s) :=
  Hf.dual_right.image_lowerBounds_subset_lowerBounds_image Hst
#align antitone_on.image_lower_bounds_subset_upper_bounds_image AntitoneOn.image_lowerBounds_subset_upperBounds_image

theorem image_upperBounds_subset_lowerBounds_image :
    f '' (upperBounds s ∩ t) ⊆ lowerBounds (f '' s) :=
  Hf.dual_right.image_upperBounds_subset_upperBounds_image Hst
#align antitone_on.image_upper_bounds_subset_lower_bounds_image AntitoneOn.image_upperBounds_subset_lowerBounds_image

/-- The image under an antitone function of a set which is bounded above is bounded below. -/
theorem map_bddAbove : (upperBounds s ∩ t).Nonempty → BddBelow (f '' s) :=
  Hf.dual_right.map_bddAbove Hst
#align antitone_on.map_bdd_above AntitoneOn.map_bddAbove

/-- The image under an antitone function of a set which is bounded below is bounded above. -/
theorem map_bddBelow : (lowerBounds s ∩ t).Nonempty → BddAbove (f '' s) :=
  Hf.dual_right.map_bddBelow Hst
#align antitone_on.map_bdd_below AntitoneOn.map_bddBelow

/-- An antitone map sends a greatest element of a set to a least element of its image. -/
theorem map_isGreatest : IsGreatest t a → IsLeast (f '' t) (f a) :=
  Hf.dual_right.map_isGreatest
#align antitone_on.map_is_greatest AntitoneOn.map_isGreatest

/-- An antitone map sends a least element of a set to a greatest element of its image. -/
theorem map_isLeast : IsLeast t a → IsGreatest (f '' t) (f a) :=
  Hf.dual_right.map_isLeast
#align antitone_on.map_is_least AntitoneOn.map_isLeast

end AntitoneOn

namespace Monotone

variable [Preorder α] [Preorder β] {f : α → β} (Hf : Monotone f) {a : α} {s : Set α}

theorem mem_upperBounds_image (Ha : a ∈ upperBounds s) : f a ∈ upperBounds (f '' s) :=
  forall_mem_image.2 fun _ H => Hf (Ha H)
#align monotone.mem_upper_bounds_image Monotone.mem_upperBounds_image

theorem mem_lowerBounds_image (Ha : a ∈ lowerBounds s) : f a ∈ lowerBounds (f '' s) :=
  forall_mem_image.2 fun _ H => Hf (Ha H)
#align monotone.mem_lower_bounds_image Monotone.mem_lowerBounds_image

theorem image_upperBounds_subset_upperBounds_image : f '' upperBounds s ⊆ upperBounds (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩
  exact Hf.mem_upperBounds_image ha
#align monotone.image_upper_bounds_subset_upper_bounds_image Monotone.image_upperBounds_subset_upperBounds_image

theorem image_lowerBounds_subset_lowerBounds_image : f '' lowerBounds s ⊆ lowerBounds (f '' s) :=
  Hf.dual.image_upperBounds_subset_upperBounds_image
#align monotone.image_lower_bounds_subset_lower_bounds_image Monotone.image_lowerBounds_subset_lowerBounds_image

/-- The image under a monotone function of a set which is bounded above is bounded above. See also
`BddAbove.image2`. -/
theorem map_bddAbove : BddAbove s → BddAbove (f '' s)
  | ⟨C, hC⟩ => ⟨f C, Hf.mem_upperBounds_image hC⟩
#align monotone.map_bdd_above Monotone.map_bddAbove

/-- The image under a monotone function of a set which is bounded below is bounded below. See also
`BddBelow.image2`. -/
theorem map_bddBelow : BddBelow s → BddBelow (f '' s)
  | ⟨C, hC⟩ => ⟨f C, Hf.mem_lowerBounds_image hC⟩
#align monotone.map_bdd_below Monotone.map_bddBelow

/-- A monotone map sends a least element of a set to a least element of its image. -/
theorem map_isLeast (Ha : IsLeast s a) : IsLeast (f '' s) (f a) :=
  ⟨mem_image_of_mem _ Ha.1, Hf.mem_lowerBounds_image Ha.2⟩
#align monotone.map_is_least Monotone.map_isLeast

/-- A monotone map sends a greatest element of a set to a greatest element of its image. -/
theorem map_isGreatest (Ha : IsGreatest s a) : IsGreatest (f '' s) (f a) :=
  ⟨mem_image_of_mem _ Ha.1, Hf.mem_upperBounds_image Ha.2⟩
#align monotone.map_is_greatest Monotone.map_isGreatest

end Monotone

namespace Antitone

variable [Preorder α] [Preorder β] {f : α → β} (hf : Antitone f) {a : α} {s : Set α}

theorem mem_upperBounds_image : a ∈ lowerBounds s → f a ∈ upperBounds (f '' s) :=
  hf.dual_right.mem_lowerBounds_image
#align antitone.mem_upper_bounds_image Antitone.mem_upperBounds_image

theorem mem_lowerBounds_image : a ∈ upperBounds s → f a ∈ lowerBounds (f '' s) :=
  hf.dual_right.mem_upperBounds_image
#align antitone.mem_lower_bounds_image Antitone.mem_lowerBounds_image

theorem image_lowerBounds_subset_upperBounds_image : f '' lowerBounds s ⊆ upperBounds (f '' s) :=
  hf.dual_right.image_lowerBounds_subset_lowerBounds_image
#align antitone.image_lower_bounds_subset_upper_bounds_image Antitone.image_lowerBounds_subset_upperBounds_image

theorem image_upperBounds_subset_lowerBounds_image : f '' upperBounds s ⊆ lowerBounds (f '' s) :=
  hf.dual_right.image_upperBounds_subset_upperBounds_image
#align antitone.image_upper_bounds_subset_lower_bounds_image Antitone.image_upperBounds_subset_lowerBounds_image

/-- The image under an antitone function of a set which is bounded above is bounded below. -/
theorem map_bddAbove : BddAbove s → BddBelow (f '' s) :=
  hf.dual_right.map_bddAbove
#align antitone.map_bdd_above Antitone.map_bddAbove

/-- The image under an antitone function of a set which is bounded below is bounded above. -/
theorem map_bddBelow : BddBelow s → BddAbove (f '' s) :=
  hf.dual_right.map_bddBelow
#align antitone.map_bdd_below Antitone.map_bddBelow

/-- An antitone map sends a greatest element of a set to a least element of its image. -/
theorem map_isGreatest : IsGreatest s a → IsLeast (f '' s) (f a) :=
  hf.dual_right.map_isGreatest
#align antitone.map_is_greatest Antitone.map_isGreatest

/-- An antitone map sends a least element of a set to a greatest element of its image. -/
theorem map_isLeast : IsLeast s a → IsGreatest (f '' s) (f a) :=
  hf.dual_right.map_isLeast
#align antitone.map_is_least Antitone.map_isLeast

end Antitone

section Image2

variable [Preorder α] [Preorder β] [Preorder γ] {f : α → β → γ} {s : Set α} {t : Set β} {a : α}
  {b : β}

section MonotoneMonotone

variable (h₀ : ∀ b, Monotone (swap f b)) (h₁ : ∀ a, Monotone (f a))

theorem mem_upperBounds_image2 (ha : a ∈ upperBounds s) (hb : b ∈ upperBounds t) :
    f a b ∈ upperBounds (image2 f s t) :=
  forall_image2_iff.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy
#align mem_upper_bounds_image2 mem_upperBounds_image2

theorem mem_lowerBounds_image2 (ha : a ∈ lowerBounds s) (hb : b ∈ lowerBounds t) :
    f a b ∈ lowerBounds (image2 f s t) :=
  forall_image2_iff.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy
#align mem_lower_bounds_image2 mem_lowerBounds_image2

theorem image2_upperBounds_upperBounds_subset :
    image2 f (upperBounds s) (upperBounds t) ⊆ upperBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦ mem_upperBounds_image2 h₀ h₁ ha hb
#align image2_upper_bounds_upper_bounds_subset image2_upperBounds_upperBounds_subset

theorem image2_lowerBounds_lowerBounds_subset :
    image2 f (lowerBounds s) (lowerBounds t) ⊆ lowerBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦ mem_lowerBounds_image2 h₀ h₁ ha hb
#align image2_lower_bounds_lower_bounds_subset image2_lowerBounds_lowerBounds_subset

/-- See also `Monotone.map_bddAbove`. -/
protected theorem BddAbove.image2 : BddAbove s → BddAbove t → BddAbove (image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2 h₀ h₁ ha hb⟩
#align bdd_above.image2 BddAbove.image2

/-- See also `Monotone.map_bddBelow`. -/
protected theorem BddBelow.image2 : BddBelow s → BddBelow t → BddBelow (image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_lowerBounds_image2 h₀ h₁ ha hb⟩
#align bdd_below.image2 BddBelow.image2

protected theorem IsGreatest.image2 (ha : IsGreatest s a) (hb : IsGreatest t b) :
    IsGreatest (image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_upperBounds_image2 h₀ h₁ ha.2 hb.2⟩
#align is_greatest.image2 IsGreatest.image2

protected theorem IsLeast.image2 (ha : IsLeast s a) (hb : IsLeast t b) :
    IsLeast (image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_lowerBounds_image2 h₀ h₁ ha.2 hb.2⟩
#align is_least.image2 IsLeast.image2

end MonotoneMonotone

section MonotoneAntitone

variable (h₀ : ∀ b, Monotone (swap f b)) (h₁ : ∀ a, Antitone (f a))

theorem mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds (ha : a ∈ upperBounds s)
    (hb : b ∈ lowerBounds t) : f a b ∈ upperBounds (image2 f s t) :=
  forall_image2_iff.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy
#align mem_upper_bounds_image2_of_mem_upper_bounds_of_mem_lower_bounds mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds

theorem mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_upperBounds (ha : a ∈ lowerBounds s)
    (hb : b ∈ upperBounds t) : f a b ∈ lowerBounds (image2 f s t) :=
  forall_image2_iff.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy
#align mem_lower_bounds_image2_of_mem_lower_bounds_of_mem_upper_bounds mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_upperBounds

theorem image2_upperBounds_lowerBounds_subset_upperBounds_image2 :
    image2 f (upperBounds s) (lowerBounds t) ⊆ upperBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds h₀ h₁ ha hb
#align image2_upper_bounds_lower_bounds_subset_upper_bounds_image2 image2_upperBounds_lowerBounds_subset_upperBounds_image2

theorem image2_lowerBounds_upperBounds_subset_lowerBounds_image2 :
    image2 f (lowerBounds s) (upperBounds t) ⊆ lowerBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦
    mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_upperBounds h₀ h₁ ha hb
#align image2_lower_bounds_upper_bounds_subset_lower_bounds_image2 image2_lowerBounds_upperBounds_subset_lowerBounds_image2

theorem BddAbove.bddAbove_image2_of_bddBelow :
    BddAbove s → BddBelow t → BddAbove (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds h₀ h₁ ha hb⟩
#align bdd_above.bdd_above_image2_of_bdd_below BddAbove.bddAbove_image2_of_bddBelow

theorem BddBelow.bddBelow_image2_of_bddAbove :
    BddBelow s → BddAbove t → BddBelow (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_upperBounds h₀ h₁ ha hb⟩
#align bdd_below.bdd_below_image2_of_bdd_above BddBelow.bddBelow_image2_of_bddAbove

theorem IsGreatest.isGreatest_image2_of_isLeast (ha : IsGreatest s a) (hb : IsLeast t b) :
    IsGreatest (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1,
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds h₀ h₁ ha.2 hb.2⟩
#align is_greatest.is_greatest_image2_of_is_least IsGreatest.isGreatest_image2_of_isLeast

theorem IsLeast.isLeast_image2_of_isGreatest (ha : IsLeast s a) (hb : IsGreatest t b) :
    IsLeast (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1,
    mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_upperBounds h₀ h₁ ha.2 hb.2⟩
#align is_least.is_least_image2_of_is_greatest IsLeast.isLeast_image2_of_isGreatest

end MonotoneAntitone

section AntitoneAntitone

variable (h₀ : ∀ b, Antitone (swap f b)) (h₁ : ∀ a, Antitone (f a))

theorem mem_upperBounds_image2_of_mem_lowerBounds (ha : a ∈ lowerBounds s)
    (hb : b ∈ lowerBounds t) : f a b ∈ upperBounds (image2 f s t) :=
  forall_image2_iff.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy
#align mem_upper_bounds_image2_of_mem_lower_bounds mem_upperBounds_image2_of_mem_lowerBounds

theorem mem_lowerBounds_image2_of_mem_upperBounds (ha : a ∈ upperBounds s)
    (hb : b ∈ upperBounds t) : f a b ∈ lowerBounds (image2 f s t) :=
  forall_image2_iff.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy
#align mem_lower_bounds_image2_of_mem_upper_bounds mem_lowerBounds_image2_of_mem_upperBounds

theorem image2_upperBounds_upperBounds_subset_upperBounds_image2 :
    image2 f (lowerBounds s) (lowerBounds t) ⊆ upperBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦
    mem_upperBounds_image2_of_mem_lowerBounds h₀ h₁ ha hb
#align image2_upper_bounds_upper_bounds_subset_upper_bounds_image2 image2_upperBounds_upperBounds_subset_upperBounds_image2

theorem image2_lowerBounds_lowerBounds_subset_lowerBounds_image2 :
    image2 f (upperBounds s) (upperBounds t) ⊆ lowerBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦
    mem_lowerBounds_image2_of_mem_upperBounds h₀ h₁ ha hb
#align image2_lower_bounds_lower_bounds_subset_lower_bounds_image2 image2_lowerBounds_lowerBounds_subset_lowerBounds_image2

theorem BddBelow.image2_bddAbove : BddBelow s → BddBelow t → BddAbove (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2_of_mem_lowerBounds h₀ h₁ ha hb⟩
#align bdd_below.image2_bdd_above BddBelow.image2_bddAbove

theorem BddAbove.image2_bddBelow : BddAbove s → BddAbove t → BddBelow (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_lowerBounds_image2_of_mem_upperBounds h₀ h₁ ha hb⟩
#align bdd_above.image2_bdd_below BddAbove.image2_bddBelow

theorem IsLeast.isGreatest_image2 (ha : IsLeast s a) (hb : IsLeast t b) :
    IsGreatest (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_upperBounds_image2_of_mem_lowerBounds h₀ h₁ ha.2 hb.2⟩
#align is_least.is_greatest_image2 IsLeast.isGreatest_image2

theorem IsGreatest.isLeast_image2 (ha : IsGreatest s a) (hb : IsGreatest t b) :
    IsLeast (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_lowerBounds_image2_of_mem_upperBounds h₀ h₁ ha.2 hb.2⟩
#align is_greatest.is_least_image2 IsGreatest.isLeast_image2

end AntitoneAntitone

section AntitoneMonotone

variable (h₀ : ∀ b, Antitone (swap f b)) (h₁ : ∀ a, Monotone (f a))

theorem mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds (ha : a ∈ lowerBounds s)
    (hb : b ∈ upperBounds t) : f a b ∈ upperBounds (image2 f s t) :=
  forall_image2_iff.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy
#align mem_upper_bounds_image2_of_mem_upper_bounds_of_mem_upper_bounds mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds

theorem mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_lowerBounds (ha : a ∈ upperBounds s)
    (hb : b ∈ lowerBounds t) : f a b ∈ lowerBounds (image2 f s t) :=
  forall_image2_iff.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy
#align mem_lower_bounds_image2_of_mem_lower_bounds_of_mem_lower_bounds mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_lowerBounds

theorem image2_lowerBounds_upperBounds_subset_upperBounds_image2 :
    image2 f (lowerBounds s) (upperBounds t) ⊆ upperBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds h₀ h₁ ha hb
#align image2_lower_bounds_upper_bounds_subset_upper_bounds_image2 image2_lowerBounds_upperBounds_subset_upperBounds_image2

theorem image2_upperBounds_lowerBounds_subset_lowerBounds_image2 :
    image2 f (upperBounds s) (lowerBounds t) ⊆ lowerBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦
    mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_lowerBounds h₀ h₁ ha hb
#align image2_upper_bounds_lower_bounds_subset_lower_bounds_image2 image2_upperBounds_lowerBounds_subset_lowerBounds_image2

theorem BddBelow.bddAbove_image2_of_bddAbove :
    BddBelow s → BddAbove t → BddAbove (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds h₀ h₁ ha hb⟩
#align bdd_below.bdd_above_image2_of_bdd_above BddBelow.bddAbove_image2_of_bddAbove

theorem BddAbove.bddBelow_image2_of_bddAbove :
    BddAbove s → BddBelow t → BddBelow (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_lowerBounds h₀ h₁ ha hb⟩
#align bdd_above.bdd_below_image2_of_bdd_above BddAbove.bddBelow_image2_of_bddAbove

theorem IsLeast.isGreatest_image2_of_isGreatest (ha : IsLeast s a) (hb : IsGreatest t b) :
    IsGreatest (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1,
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds h₀ h₁ ha.2 hb.2⟩
#align is_least.is_greatest_image2_of_is_greatest IsLeast.isGreatest_image2_of_isGreatest

theorem IsGreatest.isLeast_image2_of_isLeast (ha : IsGreatest s a) (hb : IsLeast t b) :
    IsLeast (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1,
    mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_lowerBounds h₀ h₁ ha.2 hb.2⟩
#align is_greatest.is_least_image2_of_is_least IsGreatest.isLeast_image2_of_isLeast

end AntitoneMonotone

end Image2

section Prod

variable {α β : Type*} [Preorder α] [Preorder β]

lemma bddAbove_prod {s : Set (α × β)} :
    BddAbove s ↔ BddAbove (Prod.fst '' s) ∧ BddAbove (Prod.snd '' s) :=
  ⟨fun ⟨p, hp⟩ ↦ ⟨⟨p.1, forall_mem_image.2 fun _q hq ↦ (hp hq).1⟩,
    ⟨p.2, forall_mem_image.2 fun _q hq ↦ (hp hq).2⟩⟩,
    fun ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ↦ ⟨⟨x, y⟩, fun _p hp ↦
      ⟨hx <| mem_image_of_mem _ hp, hy <| mem_image_of_mem _ hp⟩⟩⟩

lemma bddBelow_prod {s : Set (α × β)} :
    BddBelow s ↔ BddBelow (Prod.fst '' s) ∧ BddBelow (Prod.snd '' s) :=
  bddAbove_prod (α := αᵒᵈ) (β := βᵒᵈ)

lemma bddAbove_range_prod {F : ι → α × β} :
    BddAbove (range F) ↔ BddAbove (range <| Prod.fst ∘ F) ∧ BddAbove (range <| Prod.snd ∘ F) := by
  simp only [bddAbove_prod, ← range_comp]

lemma bddBelow_range_prod {F : ι → α × β} :
    BddBelow (range F) ↔ BddBelow (range <| Prod.fst ∘ F) ∧ BddBelow (range <| Prod.snd ∘ F) :=
  bddAbove_range_prod (α := αᵒᵈ) (β := βᵒᵈ)

theorem isLUB_prod {s : Set (α × β)} (p : α × β) :
    IsLUB s p ↔ IsLUB (Prod.fst '' s) p.1 ∧ IsLUB (Prod.snd '' s) p.2 := by
  refine
    ⟨fun H =>
      ⟨⟨monotone_fst.mem_upperBounds_image H.1, fun a ha => ?_⟩,
        ⟨monotone_snd.mem_upperBounds_image H.1, fun a ha => ?_⟩⟩,
      fun H => ⟨?_, ?_⟩⟩
  · suffices h : (a, p.2) ∈ upperBounds s from (H.2 h).1
    exact fun q hq => ⟨ha <| mem_image_of_mem _ hq, (H.1 hq).2⟩
  · suffices h : (p.1, a) ∈ upperBounds s from (H.2 h).2
    exact fun q hq => ⟨(H.1 hq).1, ha <| mem_image_of_mem _ hq⟩
  · exact fun q hq => ⟨H.1.1 <| mem_image_of_mem _ hq, H.2.1 <| mem_image_of_mem _ hq⟩
  · exact fun q hq =>
      ⟨H.1.2 <| monotone_fst.mem_upperBounds_image hq,
        H.2.2 <| monotone_snd.mem_upperBounds_image hq⟩
#align is_lub_prod isLUB_prod

theorem isGLB_prod {s : Set (α × β)} (p : α × β) :
    IsGLB s p ↔ IsGLB (Prod.fst '' s) p.1 ∧ IsGLB (Prod.snd '' s) p.2 :=
  @isLUB_prod αᵒᵈ βᵒᵈ _ _ _ _
#align is_glb_prod isGLB_prod

end Prod


section Pi

variable {π : α → Type*} [∀ a, Preorder (π a)]

lemma bddAbove_pi {s : Set (∀ a, π a)} :
    BddAbove s ↔ ∀ a, BddAbove (Function.eval a '' s) :=
  ⟨fun ⟨f, hf⟩ a ↦ ⟨f a, forall_mem_image.2 fun _ hg ↦ hf hg a⟩,
    fun h ↦ ⟨fun a ↦ (h a).some, fun _ hg a ↦ (h a).some_mem <| mem_image_of_mem _ hg⟩⟩

lemma bddBelow_pi {s : Set (∀ a, π a)} :
    BddBelow s ↔ ∀ a, BddBelow (Function.eval a '' s) :=
  bddAbove_pi (π := fun a ↦ (π a)ᵒᵈ)

lemma bddAbove_range_pi {F : ι → ∀ a, π a} :
    BddAbove (range F) ↔ ∀ a, BddAbove (range fun i ↦ F i a) := by
  simp only [bddAbove_pi, ← range_comp]
  rfl

lemma bddBelow_range_pi {F : ι → ∀ a, π a} :
    BddBelow (range F) ↔ ∀ a, BddBelow (range fun i ↦ F i a) :=
  bddAbove_range_pi (π := fun a ↦ (π a)ᵒᵈ)

theorem isLUB_pi {s : Set (∀ a, π a)} {f : ∀ a, π a} :
    IsLUB s f ↔ ∀ a, IsLUB (Function.eval a '' s) (f a) := by
  classical
    refine
      ⟨fun H a => ⟨(Function.monotone_eval a).mem_upperBounds_image H.1, fun b hb => ?_⟩, fun H =>
        ⟨?_, ?_⟩⟩
    · suffices h : Function.update f a b ∈ upperBounds s from Function.update_same a b f ▸ H.2 h a
      exact fun g hg => le_update_iff.2 ⟨hb <| mem_image_of_mem _ hg, fun i _ => H.1 hg i⟩
    · exact fun g hg a => (H a).1 (mem_image_of_mem _ hg)
    · exact fun g hg a => (H a).2 ((Function.monotone_eval a).mem_upperBounds_image hg)
#align is_lub_pi isLUB_pi

theorem isGLB_pi {s : Set (∀ a, π a)} {f : ∀ a, π a} :
    IsGLB s f ↔ ∀ a, IsGLB (Function.eval a '' s) (f a) :=
  @isLUB_pi α (fun a => (π a)ᵒᵈ) _ s f
#align is_glb_pi isGLB_pi

end Pi

theorem IsGLB.of_image [Preorder α] [Preorder β] {f : α → β} (hf : ∀ {x y}, f x ≤ f y ↔ x ≤ y)
    {s : Set α} {x : α} (hx : IsGLB (f '' s) (f x)) : IsGLB s x :=
  ⟨fun _ hy => hf.1 <| hx.1 <| mem_image_of_mem _ hy, fun _ hy =>
    hf.1 <| hx.2 <| Monotone.mem_lowerBounds_image (fun _ _ => hf.2) hy⟩
#align is_glb.of_image IsGLB.of_image

theorem IsLUB.of_image [Preorder α] [Preorder β] {f : α → β} (hf : ∀ {x y}, f x ≤ f y ↔ x ≤ y)
    {s : Set α} {x : α} (hx : IsLUB (f '' s) (f x)) : IsLUB s x :=
  ⟨fun _ hy => hf.1 <| hx.1 <| mem_image_of_mem _ hy, fun _ hy =>
    hf.1 <| hx.2 <| Monotone.mem_upperBounds_image (fun _ _ => hf.2) hy⟩
#align is_lub.of_image IsLUB.of_image

lemma BddAbove.range_mono [Preorder β] {f : α → β} (g : α → β) (h : ∀ a, f a ≤ g a)
    (hbdd : BddAbove (range g)) : BddAbove (range f) := by
  obtain ⟨C, hC⟩ := hbdd
  use C
  rintro - ⟨x, rfl⟩
  exact (h x).trans (hC <| mem_range_self x)

lemma BddBelow.range_mono [Preorder β] (f : α → β) {g : α → β} (h : ∀ a, f a ≤ g a)
    (hbdd : BddBelow (range f)) : BddBelow (range g) :=
  BddAbove.range_mono (β := βᵒᵈ) f h hbdd

lemma BddAbove.range_comp {γ : Type*} [Preorder β] [Preorder γ] {f : α → β} {g : β → γ}
    (hf : BddAbove (range f)) (hg : Monotone g) : BddAbove (range (fun x => g (f x))) := by
  change BddAbove (range (g ∘ f))
  simpa only [Set.range_comp] using hg.map_bddAbove hf

lemma BddBelow.range_comp {γ : Type*} [Preorder β] [Preorder γ] {f : α → β} {g : β → γ}
    (hf : BddBelow (range f)) (hg : Monotone g) : BddBelow (range (fun x => g (f x))) := by
  change BddBelow (range (g ∘ f))
  simpa only [Set.range_comp] using hg.map_bddBelow hf

section ScottContinuous
variable [Preorder α] [Preorder β] {f : α → β} {a : α}

/-- A function between preorders is said to be Scott continuous if it preserves `IsLUB` on directed
sets. It can be shown that a function is Scott continuous if and only if it is continuous wrt the
Scott topology.

The dual notion

```lean
∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≥ ·) d → ∀ ⦃a⦄, IsGLB d a → IsGLB (f '' d) (f a)
```

does not appear to play a significant role in the literature, so is omitted here.
-/
def ScottContinuous (f : α → β) : Prop :=
  ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → IsLUB (f '' d) (f a)
#align scott_continuous ScottContinuous

protected theorem ScottContinuous.monotone (h : ScottContinuous f) : Monotone f := by
  refine fun a b hab =>
    (h (insert_nonempty _ _) (directedOn_pair le_refl hab) ?_).1
      (mem_image_of_mem _ <| mem_insert _ _)
  rw [IsLUB, upperBounds_insert, upperBounds_singleton,
    inter_eq_self_of_subset_right (Ici_subset_Ici.2 hab)]
  exact isLeast_Ici
#align scott_continuous.monotone ScottContinuous.monotone

end ScottContinuous
