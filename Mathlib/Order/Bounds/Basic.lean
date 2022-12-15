/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
! This file was ported from Lean 3 source module order.bounds.basic
! leanprover-community/mathlib commit aba57d4d3dae35460225919dcd82fe91355162f9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Set.NAry

/-!
# Upper / lower bounds
In this file we define:
* `upper_bounds`, `lower_bounds` : the set of upper bounds (resp., lower bounds) of a set;
* `bdd_above s`, `bdd_below s` : the set `s` is bounded above (resp., below), i.e., the set of upper
  (resp., lower) bounds of `s` is nonempty;
* `is_least s a`, `is_greatest s a` : `a` is a least (resp., greatest) element of `s`;
  for a partial order, it is unique if exists;
* `is_lub s a`, `is_glb s a` : `a` is a least upper bound (resp., a greatest lower bound)
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

/-- `a` is a greatest element of a set `s`; for a partial order, it is unique if exists -/
def IsGreatest (s : Set α) (a : α) : Prop :=
  a ∈ s ∧ a ∈ upperBounds s
#align is_greatest IsGreatest

/-- `a` is a least upper bound of a set `s`; for a partial order, it is unique if exists. -/
def IsLub (s : Set α) : α → Prop :=
  IsLeast (upperBounds s)
#align is_lub IsLub

/-- `a` is a greatest lower bound of a set `s`; for a partial order, it is unique if exists. -/
def IsGlb (s : Set α) : α → Prop :=
  IsGreatest (lowerBounds s)
#align is_glb IsGlb

theorem mem_upper_bounds : a ∈ upperBounds s ↔ ∀ x ∈ s, x ≤ a :=
  Iff.rfl
#align mem_upper_bounds mem_upper_bounds

theorem mem_lower_bounds : a ∈ lowerBounds s ↔ ∀ x ∈ s, a ≤ x :=
  Iff.rfl
#align mem_lower_bounds mem_lower_bounds

theorem bdd_above_def : BddAbove s ↔ ∃ x, ∀ y ∈ s, y ≤ x :=
  Iff.rfl
#align bdd_above_def bdd_above_def

theorem bdd_below_def : BddBelow s ↔ ∃ x, ∀ y ∈ s, x ≤ y :=
  Iff.rfl
#align bdd_below_def bdd_below_def

theorem bot_mem_lower_bounds [OrderBot α] (s : Set α) : ⊥ ∈ lowerBounds s := fun _ _ => bot_le
#align bot_mem_lower_bounds bot_mem_lower_bounds

theorem top_mem_upper_bounds [OrderTop α] (s : Set α) : ⊤ ∈ upperBounds s := fun _ _ => le_top
#align top_mem_upper_bounds top_mem_upper_bounds

@[simp]
theorem is_least_bot_iff [OrderBot α] : IsLeast s ⊥ ↔ ⊥ ∈ s :=
  and_iff_left <| bot_mem_lower_bounds _
#align is_least_bot_iff is_least_bot_iff

@[simp]
theorem is_greatest_top_iff [OrderTop α] : IsGreatest s ⊤ ↔ ⊤ ∈ s :=
  and_iff_left <| top_mem_upper_bounds _
#align is_greatest_top_iff is_greatest_top_iff

/-- A set `s` is not bounded above if and only if for each `x` there exists `y ∈ s` such that `x`
is not greater than or equal to `y`. This version only assumes `preorder` structure and uses
`¬(y ≤ x)`. A version for linear orders is called `not_bdd_above_iff`. -/
theorem not_bdd_above_iff' : ¬BddAbove s ↔ ∀ x, ∃ y ∈ s, ¬y ≤ x := by
  simp [BddAbove, upperBounds, Set.Nonempty]
#align not_bdd_above_iff' not_bdd_above_iff'

/-- A set `s` is not bounded below if and only if for each `x` there exists `y ∈ s` such that `x`
is not less than or equal to `y`. This version only assumes `preorder` structure and uses
`¬(x ≤ y)`. A version for linear orders is called `not_bdd_below_iff`. -/
theorem not_bdd_below_iff' : ¬BddBelow s ↔ ∀ x, ∃ y ∈ s, ¬x ≤ y :=
  @not_bdd_above_iff' αᵒᵈ _ _
#align not_bdd_below_iff' not_bdd_below_iff'

/-- A set `s` is not bounded above if and only if for each `x` there exists `y ∈ s` that is greater
than `x`. A version for preorders is called `not_bdd_above_iff'`. -/
theorem not_bdd_above_iff {α : Type _} [LinearOrder α] {s : Set α} :
    ¬BddAbove s ↔ ∀ x, ∃ y ∈ s, x < y := by simp only [not_bdd_above_iff', not_le]
#align not_bdd_above_iff not_bdd_above_iff

/-- A set `s` is not bounded below if and only if for each `x` there exists `y ∈ s` that is less
than `x`. A version for preorders is called `not_bdd_below_iff'`. -/
theorem not_bdd_below_iff {α : Type _} [LinearOrder α] {s : Set α} :
    ¬BddBelow s ↔ ∀ x, ∃ y ∈ s, y < x :=
  @not_bdd_above_iff αᵒᵈ _ _
#align not_bdd_below_iff not_bdd_below_iff

theorem BddAbove.dual (h : BddAbove s) : BddBelow (of_dual ⁻¹' s) :=
  h
#align bdd_above.dual BddAbove.dual

theorem BddBelow.dual (h : BddBelow s) : BddAbove (of_dual ⁻¹' s) :=
  h
#align bdd_below.dual BddBelow.dual

theorem IsLeast.dual (h : IsLeast s a) : IsGreatest (of_dual ⁻¹' s) (toDual a) :=
  h
#align is_least.dual IsLeast.dual

theorem IsGreatest.dual (h : IsGreatest s a) : IsLeast (of_dual ⁻¹' s) (toDual a) :=
  h
#align is_greatest.dual IsGreatest.dual

theorem IsLub.dual (h : IsLub s a) : IsGlb (of_dual ⁻¹' s) (toDual a) :=
  h
#align is_lub.dual IsLub.dual

theorem IsGlb.dual (h : IsGlb s a) : IsLub (of_dual ⁻¹' s) (toDual a) :=
  h
#align is_glb.dual IsGlb.dual

/-- If `a` is the least element of a set `s`, then subtype `s` is an order with bottom element. -/
@[reducible]
def IsLeast.orderBot (h : IsLeast s a) :
    OrderBot s where
  bot := ⟨a, h.1⟩
  bot_le := Subtype.forall.2 h.2
#align is_least.order_bot IsLeast.orderBot

/-- If `a` is the greatest element of a set `s`, then subtype `s` is an order with top element. -/
@[reducible]
def IsGreatest.orderTop (h : IsGreatest s a) :
    OrderTop s where
  top := ⟨a, h.1⟩
  le_top := Subtype.forall.2 h.2
#align is_greatest.order_top IsGreatest.orderTop

/-!
### Monotonicity
-/


theorem upper_bounds_mono_set ⦃s t : Set α⦄ (hst : s ⊆ t) : upperBounds t ⊆ upperBounds s :=
  fun _ hb _ h => hb <| hst h
#align upper_bounds_mono_set upper_bounds_mono_set

theorem lower_bounds_mono_set ⦃s t : Set α⦄ (hst : s ⊆ t) : lowerBounds t ⊆ lowerBounds s :=
  fun _ hb _ h => hb <| hst h
#align lower_bounds_mono_set lower_bounds_mono_set

theorem upper_bounds_mono_mem ⦃a b⦄ (hab : a ≤ b) : a ∈ upperBounds s → b ∈ upperBounds s :=
  fun ha _ h => le_trans (ha h) hab
#align upper_bounds_mono_mem upper_bounds_mono_mem

theorem lower_bounds_mono_mem ⦃a b⦄ (hab : a ≤ b) : b ∈ lowerBounds s → a ∈ lowerBounds s :=
  fun hb _ h => le_trans hab (hb h)
#align lower_bounds_mono_mem lower_bounds_mono_mem

theorem upper_bounds_mono ⦃s t : Set α⦄ (hst : s ⊆ t) ⦃a b⦄ (hab : a ≤ b) :
    a ∈ upperBounds t → b ∈ upperBounds s := fun ha =>
  upper_bounds_mono_set hst <| upper_bounds_mono_mem hab ha
#align upper_bounds_mono upper_bounds_mono

theorem lower_bounds_mono ⦃s t : Set α⦄ (hst : s ⊆ t) ⦃a b⦄ (hab : a ≤ b) :
    b ∈ lowerBounds t → a ∈ lowerBounds s := fun hb =>
  lower_bounds_mono_set hst <| lower_bounds_mono_mem hab hb
#align lower_bounds_mono lower_bounds_mono

/-- If `s ⊆ t` and `t` is bounded above, then so is `s`. -/
theorem BddAbove.mono ⦃s t : Set α⦄ (h : s ⊆ t) : BddAbove t → BddAbove s :=
  Nonempty.mono <| upper_bounds_mono_set h
#align bdd_above.mono BddAbove.mono

/-- If `s ⊆ t` and `t` is bounded below, then so is `s`. -/
theorem BddBelow.mono ⦃s t : Set α⦄ (h : s ⊆ t) : BddBelow t → BddBelow s :=
  Nonempty.mono <| lower_bounds_mono_set h
#align bdd_below.mono BddBelow.mono

/-- If `a` is a least upper bound for sets `s` and `p`, then it is a least upper bound for any
set `t`, `s ⊆ t ⊆ p`. -/
theorem IsLub.of_subset_of_superset {s t p : Set α} (hs : IsLub s a) (hp : IsLub p a) (hst : s ⊆ t)
    (htp : t ⊆ p) : IsLub t a :=
  ⟨upper_bounds_mono_set htp hp.1, lower_bounds_mono_set (upper_bounds_mono_set hst) hs.2⟩
#align is_lub.of_subset_of_superset IsLub.of_subset_of_superset

/-- If `a` is a greatest lower bound for sets `s` and `p`, then it is a greater lower bound for any
set `t`, `s ⊆ t ⊆ p`. -/
theorem IsGlb.of_subset_of_superset {s t p : Set α} (hs : IsGlb s a) (hp : IsGlb p a) (hst : s ⊆ t)
    (htp : t ⊆ p) : IsGlb t a :=
  hs.dual.of_subset_of_superset hp hst htp
#align is_glb.of_subset_of_superset IsGlb.of_subset_of_superset

theorem IsLeast.mono (ha : IsLeast s a) (hb : IsLeast t b) (hst : s ⊆ t) : b ≤ a :=
  hb.2 (hst ha.1)
#align is_least.mono IsLeast.mono

theorem IsGreatest.mono (ha : IsGreatest s a) (hb : IsGreatest t b) (hst : s ⊆ t) : a ≤ b :=
  hb.2 (hst ha.1)
#align is_greatest.mono IsGreatest.mono

theorem IsLub.mono (ha : IsLub s a) (hb : IsLub t b) (hst : s ⊆ t) : a ≤ b :=
  hb.mono ha <| upper_bounds_mono_set hst
#align is_lub.mono IsLub.mono

theorem IsGlb.mono (ha : IsGlb s a) (hb : IsGlb t b) (hst : s ⊆ t) : b ≤ a :=
  hb.mono ha <| lower_bounds_mono_set hst
#align is_glb.mono IsGlb.mono

theorem subset_lower_bounds_upper_bounds (s : Set α) : s ⊆ lowerBounds (upperBounds s) :=
  fun _ hx _ hy => hy hx
#align subset_lower_bounds_upper_bounds subset_lower_bounds_upper_bounds

theorem subset_upper_bounds_lower_bounds (s : Set α) : s ⊆ upperBounds (lowerBounds s) :=
  fun _ hx _ hy => hy hx
#align subset_upper_bounds_lower_bounds subset_upper_bounds_lower_bounds

theorem Set.Nonempty.bdd_above_lower_bounds (hs : s.Nonempty) : BddAbove (lowerBounds s) :=
  hs.mono (subset_upper_bounds_lower_bounds s)
#align set.nonempty.bdd_above_lower_bounds Set.Nonempty.bdd_above_lower_bounds

theorem Set.Nonempty.bdd_below_upper_bounds (hs : s.Nonempty) : BddBelow (upperBounds s) :=
  hs.mono (subset_lower_bounds_upper_bounds s)
#align set.nonempty.bdd_below_upper_bounds Set.Nonempty.bdd_below_upper_bounds

/-!
### Conversions
-/


theorem IsLeast.isGlb (h : IsLeast s a) : IsGlb s a :=
  ⟨h.2, fun _ hb => hb h.1⟩
#align is_least.is_glb IsLeast.isGlb

theorem IsGreatest.isLub (h : IsGreatest s a) : IsLub s a :=
  ⟨h.2, fun _ hb => hb h.1⟩
#align is_greatest.is_lub IsGreatest.isLub

theorem IsLub.upperBounds_eq (h : IsLub s a) : upperBounds s = Ici a :=
  Set.ext fun _ => ⟨fun hb => h.2 hb, fun hb => upper_bounds_mono_mem hb h.1⟩
#align is_lub.upper_bounds_eq IsLub.upperBounds_eq

theorem IsGlb.lower_bounds_eq (h : IsGlb s a) : lowerBounds s = Iic a :=
  h.dual.upperBounds_eq
#align is_glb.lower_bounds_eq IsGlb.lower_bounds_eq

theorem IsLeast.lower_bounds_eq (h : IsLeast s a) : lowerBounds s = Iic a :=
  h.isGlb.lower_bounds_eq
#align is_least.lower_bounds_eq IsLeast.lower_bounds_eq

theorem IsGreatest.upper_bounds_eq (h : IsGreatest s a) : upperBounds s = Ici a :=
  h.isLub.upperBounds_eq
#align is_greatest.upper_bounds_eq IsGreatest.upper_bounds_eq

theorem is_lub_le_iff (h : IsLub s a) : a ≤ b ↔ b ∈ upperBounds s := by
  rw [h.upperBounds_eq]
  rfl
#align is_lub_le_iff is_lub_le_iff

theorem le_is_glb_iff (h : IsGlb s a) : b ≤ a ↔ b ∈ lowerBounds s := by
  rw [h.lower_bounds_eq]
  rfl
#align le_is_glb_iff le_is_glb_iff

theorem is_lub_iff_le_iff : IsLub s a ↔ ∀ b, a ≤ b ↔ b ∈ upperBounds s :=
  ⟨fun h _ => is_lub_le_iff h, fun H => ⟨(H _).1 le_rfl, fun b hb => (H b).2 hb⟩⟩
#align is_lub_iff_le_iff is_lub_iff_le_iff

theorem is_glb_iff_le_iff : IsGlb s a ↔ ∀ b, b ≤ a ↔ b ∈ lowerBounds s :=
  @is_lub_iff_le_iff αᵒᵈ _ _ _
#align is_glb_iff_le_iff is_glb_iff_le_iff

/-- If `s` has a least upper bound, then it is bounded above. -/
theorem IsLub.bddAbove (h : IsLub s a) : BddAbove s :=
  ⟨a, h.1⟩
#align is_lub.bdd_above IsLub.bddAbove

/-- If `s` has a greatest lower bound, then it is bounded below. -/
theorem IsGlb.bddBelow (h : IsGlb s a) : BddBelow s :=
  ⟨a, h.1⟩
#align is_glb.bdd_below IsGlb.bddBelow

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
theorem upper_bounds_union : upperBounds (s ∪ t) = upperBounds s ∩ upperBounds t :=
  Subset.antisymm (fun _ hb => ⟨fun _ hx => hb (Or.inl hx), fun _ hx => hb (Or.inr hx)⟩)
    fun _ hb _ hx => hx.elim (fun hs => hb.1 hs) fun ht => hb.2 ht
#align upper_bounds_union upper_bounds_union

@[simp]
theorem lower_bounds_union : lowerBounds (s ∪ t) = lowerBounds s ∩ lowerBounds t :=
  @upper_bounds_union αᵒᵈ _ s t
#align lower_bounds_union lower_bounds_union

theorem union_upper_bounds_subset_upper_bounds_inter :
    upperBounds s ∪ upperBounds t ⊆ upperBounds (s ∩ t) :=
  union_subset (upper_bounds_mono_set <| inter_subset_left _ _)
    (upper_bounds_mono_set <| inter_subset_right _ _)
#align union_upper_bounds_subset_upper_bounds_inter union_upper_bounds_subset_upper_bounds_inter

theorem union_lower_bounds_subset_lower_bounds_inter :
    lowerBounds s ∪ lowerBounds t ⊆ lowerBounds (s ∩ t) :=
  @union_upper_bounds_subset_upper_bounds_inter αᵒᵈ _ s t
#align union_lower_bounds_subset_lower_bounds_inter union_lower_bounds_subset_lower_bounds_inter

theorem isLeast_union_iff {a : α} {s t : Set α} :
    IsLeast (s ∪ t) a ↔ IsLeast s a ∧ a ∈ lowerBounds t ∨ a ∈ lowerBounds s ∧ IsLeast t a := by
  simp [IsLeast, lower_bounds_union, or_and_right, and_comm' (a ∈ t), and_assoc]
#align is_least_union_iff isLeast_union_iff

theorem is_greatest_union_iff :
    IsGreatest (s ∪ t) a ↔
      IsGreatest s a ∧ a ∈ upperBounds t ∨ a ∈ upperBounds s ∧ IsGreatest t a :=
  @isLeast_union_iff αᵒᵈ _ a s t
#align is_greatest_union_iff is_greatest_union_iff

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

/-- If `s` and `t` are bounded above sets in a `semilattice_sup`, then so is `s ∪ t`. -/
theorem BddAbove.union [SemilatticeSup γ] {s t : Set γ} :
    BddAbove s → BddAbove t → BddAbove (s ∪ t) := by
  rintro ⟨bs, hs⟩ ⟨bt, ht⟩
  use bs ⊔ bt
  rw [upper_bounds_union]
  exact ⟨upper_bounds_mono_mem le_sup_left hs, upper_bounds_mono_mem le_sup_right ht⟩
#align bdd_above.union BddAbove.union

/-- The union of two sets is bounded above if and only if each of the sets is. -/
theorem bdd_above_union [SemilatticeSup γ] {s t : Set γ} :
    BddAbove (s ∪ t) ↔ BddAbove s ∧ BddAbove t :=
  ⟨fun h => ⟨h.mono <| subset_union_left s t, h.mono <| subset_union_right s t⟩, fun h =>
    h.1.union h.2⟩
#align bdd_above_union bdd_above_union

theorem BddBelow.union [SemilatticeInf γ] {s t : Set γ} :
    BddBelow s → BddBelow t → BddBelow (s ∪ t) :=
  @BddAbove.union γᵒᵈ _ s t
#align bdd_below.union BddBelow.union

/-- The union of two sets is bounded above if and only if each of the sets is.-/
theorem bdd_below_union [SemilatticeInf γ] {s t : Set γ} :
    BddBelow (s ∪ t) ↔ BddBelow s ∧ BddBelow t :=
  @bdd_above_union γᵒᵈ _ s t
#align bdd_below_union bdd_below_union

/-- If `a` is the least upper bound of `s` and `b` is the least upper bound of `t`,
then `a ⊔ b` is the least upper bound of `s ∪ t`. -/
theorem IsLub.union [SemilatticeSup γ] {a b : γ} {s t : Set γ} (hs : IsLub s a) (ht : IsLub t b) :
    IsLub (s ∪ t) (a ⊔ b) :=
  ⟨fun _ h =>
    h.casesOn (fun h => le_sup_of_le_left <| hs.left h) fun h => le_sup_of_le_right <| ht.left h,
    fun _ hc =>
    sup_le (hs.right fun _ hd => hc <| Or.inl hd) (ht.right fun _ hd => hc <| Or.inr hd)⟩
#align is_lub.union IsLub.union

/-- If `a` is the greatest lower bound of `s` and `b` is the greatest lower bound of `t`,
then `a ⊓ b` is the greatest lower bound of `s ∪ t`. -/
theorem IsGlb.union [SemilatticeInf γ] {a₁ a₂ : γ} {s t : Set γ} (hs : IsGlb s a₁)
    (ht : IsGlb t a₂) : IsGlb (s ∪ t) (a₁ ⊓ a₂) :=
  hs.dual.union ht
#align is_glb.union IsGlb.union

/-- If `a` is the least element of `s` and `b` is the least element of `t`,
then `min a b` is the least element of `s ∪ t`. -/
theorem IsLeast.union [LinearOrder γ] {a b : γ} {s t : Set γ} (ha : IsLeast s a)
    (hb : IsLeast t b) : IsLeast (s ∪ t) (min a b) :=
  ⟨by cases' le_total a b with h h <;> simp [h, ha.1, hb.1], (ha.isGlb.union hb.isGlb).1⟩
#align is_least.union IsLeast.union

/-- If `a` is the greatest element of `s` and `b` is the greatest element of `t`,
then `max a b` is the greatest element of `s ∪ t`. -/
theorem IsGreatest.union [LinearOrder γ] {a b : γ} {s t : Set γ} (ha : IsGreatest s a)
    (hb : IsGreatest t b) : IsGreatest (s ∪ t) (max a b) :=
  ⟨by cases' le_total a b with h h <;> simp [h, ha.1, hb.1], (ha.isLub.union hb.isLub).1⟩
#align is_greatest.union IsGreatest.union

theorem IsLub.inter_Ici_of_mem [LinearOrder γ] {s : Set γ} {a b : γ} (ha : IsLub s a) (hb : b ∈ s) :
    IsLub (s ∩ Ici b) a :=
  ⟨fun _ hx => ha.1 hx.1, fun c hc =>
    have hbc : b ≤ c := hc ⟨hb, le_rfl⟩
    ha.2 fun x hx => ((le_total x b).elim fun hxb => hxb.trans hbc) fun hbx => hc ⟨hx, hbx⟩⟩
#align is_lub.inter_Ici_of_mem IsLub.inter_Ici_of_mem

theorem IsGlb.inter_Iic_of_mem [LinearOrder γ] {s : Set γ} {a b : γ} (ha : IsGlb s a) (hb : b ∈ s) :
    IsGlb (s ∩ Iic b) a :=
  ha.dual.inter_Ici_of_mem hb
#align is_glb.inter_Iic_of_mem IsGlb.inter_Iic_of_mem

theorem bdd_above_iff_exists_ge [SemilatticeSup γ] {s : Set γ} (x₀ : γ) :
    BddAbove s ↔ ∃ x, x₀ ≤ x ∧ ∀ y ∈ s, y ≤ x := by
  rw [bdd_above_def, exists_ge_and_iff_exists]
  exact Monotone.ball fun x _ => monotone_le
#align bdd_above_iff_exists_ge bdd_above_iff_exists_ge

theorem bdd_below_iff_exists_le [SemilatticeInf γ] {s : Set γ} (x₀ : γ) :
    BddBelow s ↔ ∃ x, x ≤ x₀ ∧ ∀ y ∈ s, x ≤ y :=
  bdd_above_iff_exists_ge (toDual x₀)
#align bdd_below_iff_exists_le bdd_below_iff_exists_le

theorem BddAbove.exists_ge [SemilatticeSup γ] {s : Set γ} (hs : BddAbove s) (x₀ : γ) :
    ∃ x, x₀ ≤ x ∧ ∀ y ∈ s, y ≤ x :=
  (bdd_above_iff_exists_ge x₀).mp hs
#align bdd_above.exists_ge BddAbove.exists_ge

theorem BddBelow.exists_le [SemilatticeInf γ] {s : Set γ} (hs : BddBelow s) (x₀ : γ) :
    ∃ x, x ≤ x₀ ∧ ∀ y ∈ s, x ≤ y :=
  (bdd_below_iff_exists_le x₀).mp hs
#align bdd_below.exists_le BddBelow.exists_le

/-!
### Specific sets
#### Unbounded intervals
-/


theorem is_least_Ici : IsLeast (Ici a) a :=
  ⟨left_mem_Ici, fun _ => id⟩
#align is_least_Ici is_least_Ici

theorem is_greatest_Iic : IsGreatest (Iic a) a :=
  ⟨right_mem_Iic, fun _ => id⟩
#align is_greatest_Iic is_greatest_Iic

theorem is_lub_Iic : IsLub (Iic a) a :=
  is_greatest_Iic.isLub
#align is_lub_Iic is_lub_Iic

theorem is_glb_Ici : IsGlb (Ici a) a :=
  is_least_Ici.isGlb
#align is_glb_Ici is_glb_Ici

theorem upper_bounds_Iic : upperBounds (Iic a) = Ici a :=
  is_lub_Iic.upperBounds_eq
#align upper_bounds_Iic upper_bounds_Iic

theorem lower_bounds_Ici : lowerBounds (Ici a) = Iic a :=
  is_glb_Ici.lower_bounds_eq
#align lower_bounds_Ici lower_bounds_Ici

theorem bdd_above_Iic : BddAbove (Iic a) :=
  is_lub_Iic.bddAbove
#align bdd_above_Iic bdd_above_Iic

theorem bdd_below_Ici : BddBelow (Ici a) :=
  is_glb_Ici.bddBelow
#align bdd_below_Ici bdd_below_Ici

theorem bdd_above_Iio : BddAbove (Iio a) :=
  ⟨a, fun _ hx => le_of_lt hx⟩
#align bdd_above_Iio bdd_above_Iio

theorem bdd_below_Ioi : BddBelow (Ioi a) :=
  ⟨a, fun _ hx => le_of_lt hx⟩
#align bdd_below_Ioi bdd_below_Ioi

theorem lub_Iio_le (a : α) (hb : IsLub (Iio a) b) : b ≤ a :=
  (is_lub_le_iff hb).mpr fun _ hk => le_of_lt hk
#align lub_Iio_le lub_Iio_le

theorem le_glb_Ioi (a : α) (hb : IsGlb (Ioi a) b) : a ≤ b :=
  @lub_Iio_le αᵒᵈ _ _ a hb
#align le_glb_Ioi le_glb_Ioi

theorem lub_Iio_eq_self_or_Iio_eq_Iic [PartialOrder γ] {j : γ} (i : γ) (hj : IsLub (Iio i) j) :
    j = i ∨ Iio i = Iic j := by
  cases' eq_or_lt_of_le (lub_Iio_le i hj) with hj_eq_i hj_lt_i
  · exact Or.inl hj_eq_i
  · right
    exact Set.ext fun k => ⟨fun hk_lt => hj.1 hk_lt, fun hk_le_j => lt_of_le_of_lt hk_le_j hj_lt_i⟩
#align lub_Iio_eq_self_or_Iio_eq_Iic lub_Iio_eq_self_or_Iio_eq_Iic

theorem glb_Ioi_eq_self_or_Ioi_eq_Ici [PartialOrder γ] {j : γ} (i : γ) (hj : IsGlb (Ioi i) j) :
    j = i ∨ Ioi i = Ici j :=
  @lub_Iio_eq_self_or_Iio_eq_Iic γᵒᵈ _ j i hj
#align glb_Ioi_eq_self_or_Ioi_eq_Ici glb_Ioi_eq_self_or_Ioi_eq_Ici

section

variable [LinearOrder γ]

theorem exists_lub_Iio (i : γ) : ∃ j, IsLub (Iio i) j := by
  by_cases h_exists_lt : ∃ j, j ∈ upperBounds (Iio i) ∧ j < i
  · obtain ⟨j, hj_ub, hj_lt_i⟩ := h_exists_lt
    exact ⟨j, hj_ub, fun k hk_ub => hk_ub hj_lt_i⟩
  · refine' ⟨i, fun j hj => le_of_lt hj, _⟩
    rw [mem_lower_bounds]
    by_contra h
    refine' h_exists_lt _
    push_neg at h
    exact h
#align exists_lub_Iio exists_lub_Iio

theorem exists_glb_Ioi (i : γ) : ∃ j, IsGlb (Ioi i) j :=
  @exists_lub_Iio γᵒᵈ _ i
#align exists_glb_Ioi exists_glb_Ioi

variable [DenselyOrdered γ]

theorem is_lub_Iio {a : γ} : IsLub (Iio a) a :=
  ⟨fun _ hx => le_of_lt hx, fun _ hy => le_of_forall_ge_of_dense hy⟩
#align is_lub_Iio is_lub_Iio

theorem is_glb_Ioi {a : γ} : IsGlb (Ioi a) a :=
  @is_lub_Iio γᵒᵈ _ _ a
#align is_glb_Ioi is_glb_Ioi

theorem upperBounds_Iio {a : γ} : upperBounds (Iio a) = Ici a :=
  is_lub_Iio.upperBounds_eq
#align upper_bounds_Iio upperBounds_Iio

theorem lowerBounds_Ioi {a : γ} : lowerBounds (Ioi a) = Iic a :=
  is_glb_Ioi.lower_bounds_eq
#align lower_bounds_Ioi lowerBounds_Ioi

end

/-!
#### Singleton
-/


theorem is_greatest_singleton : IsGreatest {a} a :=
  ⟨mem_singleton a, fun _ hx => le_of_eq <| eq_of_mem_singleton hx⟩
#align is_greatest_singleton is_greatest_singleton

theorem is_least_singleton : IsLeast {a} a :=
  @is_greatest_singleton αᵒᵈ _ a
#align is_least_singleton is_least_singleton

theorem is_lub_singleton : IsLub {a} a :=
  is_greatest_singleton.isLub
#align is_lub_singleton is_lub_singleton

theorem is_glb_singleton : IsGlb {a} a :=
  is_least_singleton.isGlb
#align is_glb_singleton is_glb_singleton

theorem bdd_above_singleton : BddAbove ({a} : Set α) :=
  is_lub_singleton.bddAbove
#align bdd_above_singleton bdd_above_singleton

theorem bdd_below_singleton : BddBelow ({a} : Set α) :=
  is_glb_singleton.bddBelow
#align bdd_below_singleton bdd_below_singleton

@[simp]
theorem upper_bounds_singleton : upperBounds {a} = Ici a :=
  is_lub_singleton.upperBounds_eq
#align upper_bounds_singleton upper_bounds_singleton

@[simp]
theorem lower_bounds_singleton : lowerBounds {a} = Iic a :=
  is_glb_singleton.lower_bounds_eq
#align lower_bounds_singleton lower_bounds_singleton

/-!
#### Bounded intervals
-/


theorem bdd_above_Icc : BddAbove (Icc a b) :=
  ⟨b, fun _ => And.right⟩
#align bdd_above_Icc bdd_above_Icc

theorem bdd_below_Icc : BddBelow (Icc a b) :=
  ⟨a, fun _ => And.left⟩
#align bdd_below_Icc bdd_below_Icc

theorem bdd_above_Ico : BddAbove (Ico a b) :=
  bdd_above_Icc.mono Ico_subset_Icc_self
#align bdd_above_Ico bdd_above_Ico

theorem bdd_below_Ico : BddBelow (Ico a b) :=
  bdd_below_Icc.mono Ico_subset_Icc_self
#align bdd_below_Ico bdd_below_Ico

theorem bdd_above_Ioc : BddAbove (Ioc a b) :=
  bdd_above_Icc.mono Ioc_subset_Icc_self
#align bdd_above_Ioc bdd_above_Ioc

theorem bdd_below_Ioc : BddBelow (Ioc a b) :=
  bdd_below_Icc.mono Ioc_subset_Icc_self
#align bdd_below_Ioc bdd_below_Ioc

theorem bdd_above_Ioo : BddAbove (Ioo a b) :=
  bdd_above_Icc.mono Ioo_subset_Icc_self
#align bdd_above_Ioo bdd_above_Ioo

theorem bdd_below_Ioo : BddBelow (Ioo a b) :=
  bdd_below_Icc.mono Ioo_subset_Icc_self
#align bdd_below_Ioo bdd_below_Ioo

theorem is_greatest_Icc (h : a ≤ b) : IsGreatest (Icc a b) b :=
  ⟨right_mem_Icc.2 h, fun _ => And.right⟩
#align is_greatest_Icc is_greatest_Icc

theorem is_lub_Icc (h : a ≤ b) : IsLub (Icc a b) b :=
  (is_greatest_Icc h).isLub
#align is_lub_Icc is_lub_Icc

theorem upper_bounds_Icc (h : a ≤ b) : upperBounds (Icc a b) = Ici b :=
  (is_lub_Icc h).upperBounds_eq
#align upper_bounds_Icc upper_bounds_Icc

theorem is_least_Icc (h : a ≤ b) : IsLeast (Icc a b) a :=
  ⟨left_mem_Icc.2 h, fun _ => And.left⟩
#align is_least_Icc is_least_Icc

theorem is_glb_Icc (h : a ≤ b) : IsGlb (Icc a b) a :=
  (is_least_Icc h).isGlb
#align is_glb_Icc is_glb_Icc

theorem lower_bounds_Icc (h : a ≤ b) : lowerBounds (Icc a b) = Iic a :=
  (is_glb_Icc h).lower_bounds_eq
#align lower_bounds_Icc lower_bounds_Icc

theorem is_greatest_Ioc (h : a < b) : IsGreatest (Ioc a b) b :=
  ⟨right_mem_Ioc.2 h, fun _ => And.right⟩
#align is_greatest_Ioc is_greatest_Ioc

theorem is_lub_Ioc (h : a < b) : IsLub (Ioc a b) b :=
  (is_greatest_Ioc h).isLub
#align is_lub_Ioc is_lub_Ioc

theorem upper_bounds_Ioc (h : a < b) : upperBounds (Ioc a b) = Ici b :=
  (is_lub_Ioc h).upperBounds_eq
#align upper_bounds_Ioc upper_bounds_Ioc

theorem is_least_Ico (h : a < b) : IsLeast (Ico a b) a :=
  ⟨left_mem_Ico.2 h, fun _ => And.left⟩
#align is_least_Ico is_least_Ico

theorem is_glb_Ico (h : a < b) : IsGlb (Ico a b) a :=
  (is_least_Ico h).isGlb
#align is_glb_Ico is_glb_Ico

theorem lower_bounds_Ico (h : a < b) : lowerBounds (Ico a b) = Iic a :=
  (is_glb_Ico h).lower_bounds_eq
#align lower_bounds_Ico lower_bounds_Ico

section

variable [SemilatticeSup γ] [DenselyOrdered γ]

theorem is_glb_Ioo {a b : γ} (h : a < b) : IsGlb (Ioo a b) a :=
  ⟨fun x hx => hx.1.le, fun x hx => by
    cases' eq_or_lt_of_le (le_sup_right : a ≤ x ⊔ a) with h₁ h₂
    · exact h₁.symm ▸ le_sup_left
    obtain ⟨y, lty, ylt⟩ := exists_between h₂
    apply (not_lt_of_le (sup_le (hx ⟨lty, ylt.trans_le (sup_le _ h.le)⟩) lty.le) ylt).elim
    obtain ⟨u, au, ub⟩ := exists_between h
    apply (hx ⟨au, ub⟩).trans ub.le⟩
#align is_glb_Ioo is_glb_Ioo

theorem lower_bounds_Ioo {a b : γ} (hab : a < b) : lowerBounds (Ioo a b) = Iic a :=
  (is_glb_Ioo hab).lower_bounds_eq
#align lower_bounds_Ioo lower_bounds_Ioo

theorem is_glb_Ioc {a b : γ} (hab : a < b) : IsGlb (Ioc a b) a :=
  (is_glb_Ioo hab).of_subset_of_superset (is_glb_Icc hab.le) Ioo_subset_Ioc_self Ioc_subset_Icc_self
#align is_glb_Ioc is_glb_Ioc

theorem lower_bound_Ioc {a b : γ} (hab : a < b) : lowerBounds (Ioc a b) = Iic a :=
  (is_glb_Ioc hab).lower_bounds_eq
#align lower_bound_Ioc lower_bound_Ioc

end

section

variable [SemilatticeInf γ] [DenselyOrdered γ]

theorem is_lub_Ioo {a b : γ} (hab : a < b) : IsLub (Ioo a b) b := by
  simpa only [dual_Ioo] using is_glb_Ioo hab.dual
#align is_lub_Ioo is_lub_Ioo

theorem upper_bounds_Ioo {a b : γ} (hab : a < b) : upperBounds (Ioo a b) = Ici b :=
  (is_lub_Ioo hab).upperBounds_eq
#align upper_bounds_Ioo upper_bounds_Ioo

theorem is_lub_Ico {a b : γ} (hab : a < b) : IsLub (Ico a b) b := by
  simpa only [dual_Ioc] using is_glb_Ioc hab.dual
#align is_lub_Ico is_lub_Ico

theorem upper_bounds_Ico {a b : γ} (hab : a < b) : upperBounds (Ico a b) = Ici b :=
  (is_lub_Ico hab).upperBounds_eq
#align upper_bounds_Ico upper_bounds_Ico

end

theorem bdd_below_iff_subset_Ici : BddBelow s ↔ ∃ a, s ⊆ Ici a :=
  Iff.rfl
#align bdd_below_iff_subset_Ici bdd_below_iff_subset_Ici

theorem bdd_above_iff_subset_Iic : BddAbove s ↔ ∃ a, s ⊆ Iic a :=
  Iff.rfl
#align bdd_above_iff_subset_Iic bdd_above_iff_subset_Iic

theorem bdd_below_bdd_above_iff_subset_Icc : BddBelow s ∧ BddAbove s ↔ ∃ a b, s ⊆ Icc a b := by
  simp only [Ici_inter_Iic.symm, subset_inter_iff, bdd_below_iff_subset_Ici,
    bdd_above_iff_subset_Iic, exists_and_left, exists_and_right]
#align bdd_below_bdd_above_iff_subset_Icc bdd_below_bdd_above_iff_subset_Icc

/-!
#### Univ
-/


theorem is_greatest_univ [Preorder γ] [OrderTop γ] : IsGreatest (univ : Set γ) ⊤ :=
  ⟨mem_univ _, fun _ _ => le_top⟩
#align is_greatest_univ is_greatest_univ

@[simp]
theorem OrderTop.upper_bounds_univ [PartialOrder γ] [OrderTop γ] :
    upperBounds (univ : Set γ) = {⊤} := by rw [is_greatest_univ.upper_bounds_eq, Ici_top]
#align order_top.upper_bounds_univ OrderTop.upper_bounds_univ

theorem is_lub_univ [Preorder γ] [OrderTop γ] : IsLub (univ : Set γ) ⊤ :=
  is_greatest_univ.isLub
#align is_lub_univ is_lub_univ

@[simp]
theorem OrderBot.lower_bounds_univ [PartialOrder γ] [OrderBot γ] :
    lowerBounds (univ : Set γ) = {⊥} :=
  @OrderTop.upper_bounds_univ γᵒᵈ _ _
#align order_bot.lower_bounds_univ OrderBot.lower_bounds_univ

theorem is_least_univ [Preorder γ] [OrderBot γ] : IsLeast (univ : Set γ) ⊥ :=
  @is_greatest_univ γᵒᵈ _ _
#align is_least_univ is_least_univ

theorem is_glb_univ [Preorder γ] [OrderBot γ] : IsGlb (univ : Set γ) ⊥ :=
  is_least_univ.isGlb
#align is_glb_univ is_glb_univ

@[simp]
theorem NoMaxOrder.upper_bounds_univ [NoMaxOrder α] : upperBounds (univ : Set α) = ∅ :=
  eq_empty_of_subset_empty fun b hb =>
    let ⟨_, hx⟩ := exists_gt b
    not_le_of_lt hx (hb trivial)
#align no_max_order.upper_bounds_univ NoMaxOrder.upper_bounds_univ

@[simp]
theorem NoMinOrder.lower_bounds_univ [NoMinOrder α] : lowerBounds (univ : Set α) = ∅ :=
  @NoMaxOrder.upper_bounds_univ αᵒᵈ _ _
#align no_min_order.lower_bounds_univ NoMinOrder.lower_bounds_univ

@[simp]
theorem not_bdd_above_univ [NoMaxOrder α] : ¬BddAbove (univ : Set α) := by simp [BddAbove]
#align not_bdd_above_univ not_bdd_above_univ

@[simp]
theorem not_bdd_below_univ [NoMinOrder α] : ¬BddBelow (univ : Set α) :=
  @not_bdd_above_univ αᵒᵈ _ _
#align not_bdd_below_univ not_bdd_below_univ

/-!
#### Empty set
-/


@[simp]
theorem upper_bounds_empty : upperBounds (∅ : Set α) = univ := by
  simp only [upperBounds, eq_univ_iff_forall, mem_setOf_eq, ball_empty_iff, forall_true_iff]
#align upper_bounds_empty upper_bounds_empty

@[simp]
theorem lower_bounds_empty : lowerBounds (∅ : Set α) = univ :=
  @upper_bounds_empty αᵒᵈ _
#align lower_bounds_empty lower_bounds_empty

@[simp]
theorem bdd_above_empty [Nonempty α] : BddAbove (∅ : Set α) := by
  simp only [BddAbove, upper_bounds_empty, univ_nonempty]
#align bdd_above_empty bdd_above_empty

@[simp]
theorem bdd_below_empty [Nonempty α] : BddBelow (∅ : Set α) := by
  simp only [BddBelow, lower_bounds_empty, univ_nonempty]
#align bdd_below_empty bdd_below_empty

theorem is_glb_empty [Preorder γ] [OrderTop γ] : IsGlb ∅ (⊤ : γ) := by
  simp only [IsGlb, lower_bounds_empty, is_greatest_univ]
#align is_glb_empty is_glb_empty

theorem is_lub_empty [Preorder γ] [OrderBot γ] : IsLub ∅ (⊥ : γ) :=
  @is_glb_empty γᵒᵈ _ _
#align is_lub_empty is_lub_empty

theorem IsLub.nonempty [NoMinOrder α] (hs : IsLub s a) : s.Nonempty :=
  let ⟨a', ha'⟩ := exists_lt a
  nonempty_iff_ne_empty.2 fun h =>
    not_le_of_lt ha' <| hs.right <| by simp only [h, upper_bounds_empty]
#align is_lub.nonempty IsLub.nonempty

theorem IsGlb.nonempty [NoMaxOrder α] (hs : IsGlb s a) : s.Nonempty :=
  hs.dual.nonempty
#align is_glb.nonempty IsGlb.nonempty

theorem nonempty_of_not_bdd_above [ha : Nonempty α] (h : ¬BddAbove s) : s.Nonempty :=
  (Nonempty.elim ha) fun x => (not_bdd_above_iff'.1 h x).imp fun _ ha => ha.1
#align nonempty_of_not_bdd_above nonempty_of_not_bdd_above

theorem nonempty_of_not_bdd_below [Nonempty α] (h : ¬BddBelow s) : s.Nonempty :=
  @nonempty_of_not_bdd_above αᵒᵈ _ _ _ h
#align nonempty_of_not_bdd_below nonempty_of_not_bdd_below

/-!
#### insert
-/


/-- Adding a point to a set preserves its boundedness above. -/
@[simp]
theorem bdd_above_insert [SemilatticeSup γ] (a : γ) {s : Set γ} :
    BddAbove (insert a s) ↔ BddAbove s := by
  simp only [insert_eq, bdd_above_union, bdd_above_singleton, true_and_iff]
#align bdd_above_insert bdd_above_insert

theorem BddAbove.insert [SemilatticeSup γ] (a : γ) {s : Set γ} (hs : BddAbove s) :
    BddAbove (insert a s) :=
  (bdd_above_insert a).2 hs
#align bdd_above.insert BddAbove.insert

/-- Adding a point to a set preserves its boundedness below.-/
@[simp]
theorem bdd_below_insert [SemilatticeInf γ] (a : γ) {s : Set γ} :
    BddBelow (insert a s) ↔ BddBelow s := by
  simp only [insert_eq, bdd_below_union, bdd_below_singleton, true_and_iff]
#align bdd_below_insert bdd_below_insert

theorem BddBelow.insert [SemilatticeInf γ] (a : γ) {s : Set γ} (hs : BddBelow s) :
    BddBelow (insert a s) :=
  (bdd_below_insert a).2 hs
#align bdd_below.insert BddBelow.insert

theorem IsLub.insert [SemilatticeSup γ] (a) {b} {s : Set γ} (hs : IsLub s b) :
    IsLub (insert a s) (a ⊔ b) := by
  rw [insert_eq]
  exact is_lub_singleton.union hs
#align is_lub.insert IsLub.insert

theorem IsGlb.insert [SemilatticeInf γ] (a) {b} {s : Set γ} (hs : IsGlb s b) :
    IsGlb (insert a s) (a ⊓ b) := by
  rw [insert_eq]
  exact is_glb_singleton.union hs
#align is_glb.insert IsGlb.insert

theorem IsGreatest.insert [LinearOrder γ] (a) {b} {s : Set γ} (hs : IsGreatest s b) :
    IsGreatest (insert a s) (max a b) := by
  rw [insert_eq]
  exact is_greatest_singleton.union hs
#align is_greatest.insert IsGreatest.insert

theorem IsLeast.insert [LinearOrder γ] (a) {b} {s : Set γ} (hs : IsLeast s b) :
    IsLeast (insert a s) (min a b) := by
  rw [insert_eq]
  exact is_least_singleton.union hs
#align is_least.insert IsLeast.insert

@[simp]
theorem upper_bounds_insert (a : α) (s : Set α) :
    upperBounds (insert a s) = Ici a ∩ upperBounds s := by
  rw [insert_eq, upper_bounds_union, upper_bounds_singleton]
#align upper_bounds_insert upper_bounds_insert

@[simp]
theorem lower_bounds_insert (a : α) (s : Set α) :
    lowerBounds (insert a s) = Iic a ∩ lowerBounds s := by
  rw [insert_eq, lower_bounds_union, lower_bounds_singleton]
#align lower_bounds_insert lower_bounds_insert

/-- When there is a global maximum, every set is bounded above. -/
@[simp]
protected theorem OrderTop.bddAbove [Preorder γ] [OrderTop γ] (s : Set γ) : BddAbove s :=
  ⟨⊤, fun a _ => OrderTop.le_top a⟩
#align order_top.bdd_above OrderTop.bddAbove

/-- When there is a global minimum, every set is bounded below. -/
@[simp]
protected theorem OrderBot.bddBelow [Preorder γ] [OrderBot γ] (s : Set γ) : BddBelow s :=
  ⟨⊥, fun a _ => OrderBot.bot_le a⟩
#align order_bot.bdd_below OrderBot.bddBelow

/-!
#### Pair
-/


theorem is_lub_pair [SemilatticeSup γ] {a b : γ} : IsLub {a, b} (a ⊔ b) :=
  is_lub_singleton.insert _
#align is_lub_pair is_lub_pair

theorem is_glb_pair [SemilatticeInf γ] {a b : γ} : IsGlb {a, b} (a ⊓ b) :=
  is_glb_singleton.insert _
#align is_glb_pair is_glb_pair

theorem is_least_pair [LinearOrder γ] {a b : γ} : IsLeast {a, b} (min a b) :=
  is_least_singleton.insert _
#align is_least_pair is_least_pair

theorem is_greatest_pair [LinearOrder γ] {a b : γ} : IsGreatest {a, b} (max a b) :=
  is_greatest_singleton.insert _
#align is_greatest_pair is_greatest_pair

/-!
#### Lower/upper bounds
-/


@[simp]
theorem is_lub_lower_bounds : IsLub (lowerBounds s) a ↔ IsGlb s a :=
  ⟨fun H => ⟨fun _ hx => H.2 <| subset_upper_bounds_lower_bounds s hx, H.1⟩, IsGreatest.isLub⟩
#align is_lub_lower_bounds is_lub_lower_bounds

@[simp]
theorem is_glb_upper_bounds : IsGlb (upperBounds s) a ↔ IsLub s a :=
  @is_lub_lower_bounds αᵒᵈ _ _ _
#align is_glb_upper_bounds is_glb_upper_bounds

end

/-!
### (In)equalities with the least upper bound and the greatest lower bound
-/


section Preorder

variable [Preorder α] {s : Set α} {a b : α}

theorem lower_bounds_le_upper_bounds (ha : a ∈ lowerBounds s) (hb : b ∈ upperBounds s) :
    s.Nonempty → a ≤ b
  | ⟨_, hc⟩ => le_trans (ha hc) (hb hc)
#align lower_bounds_le_upper_bounds lower_bounds_le_upper_bounds

theorem is_glb_le_is_lub (ha : IsGlb s a) (hb : IsLub s b) (hs : s.Nonempty) : a ≤ b :=
  lower_bounds_le_upper_bounds ha.1 hb.1 hs
#align is_glb_le_is_lub is_glb_le_is_lub

theorem is_lub_lt_iff (ha : IsLub s a) : a < b ↔ ∃ c ∈ upperBounds s, c < b :=
  ⟨fun hb => ⟨a, ha.1, hb⟩, fun ⟨_, hcs, hcb⟩ => lt_of_le_of_lt (ha.2 hcs) hcb⟩
#align is_lub_lt_iff is_lub_lt_iff

theorem lt_is_glb_iff (ha : IsGlb s a) : b < a ↔ ∃ c ∈ lowerBounds s, b < c :=
  is_lub_lt_iff ha.dual
#align lt_is_glb_iff lt_is_glb_iff

theorem le_of_is_lub_le_is_glb {x y} (ha : IsGlb s a) (hb : IsLub s b) (hab : b ≤ a) (hx : x ∈ s)
    (hy : y ∈ s) : x ≤ y :=
  calc
    x ≤ b := hb.1 hx
    _ ≤ a := hab
    _ ≤ y := ha.1 hy

#align le_of_is_lub_le_is_glb le_of_is_lub_le_is_glb

end Preorder

section PartialOrder

variable [PartialOrder α] {s : Set α} {a b : α}

theorem IsLeast.unique (Ha : IsLeast s a) (Hb : IsLeast s b) : a = b :=
  le_antisymm (Ha.right Hb.left) (Hb.right Ha.left)
#align is_least.unique IsLeast.unique

theorem IsLeast.is_least_iff_eq (Ha : IsLeast s a) : IsLeast s b ↔ a = b :=
  Iff.intro Ha.unique fun h => h ▸ Ha
#align is_least.is_least_iff_eq IsLeast.is_least_iff_eq

theorem IsGreatest.unique (Ha : IsGreatest s a) (Hb : IsGreatest s b) : a = b :=
  le_antisymm (Hb.right Ha.left) (Ha.right Hb.left)
#align is_greatest.unique IsGreatest.unique

theorem IsGreatest.is_greatest_iff_eq (Ha : IsGreatest s a) : IsGreatest s b ↔ a = b :=
  Iff.intro Ha.unique fun h => h ▸ Ha
#align is_greatest.is_greatest_iff_eq IsGreatest.is_greatest_iff_eq

theorem IsLub.unique (Ha : IsLub s a) (Hb : IsLub s b) : a = b :=
  Ha.unique Hb
#align is_lub.unique IsLub.unique

theorem IsGlb.unique (Ha : IsGlb s a) (Hb : IsGlb s b) : a = b :=
  Ha.unique Hb
#align is_glb.unique IsGlb.unique

theorem Set.subsingleton_of_is_lub_le_is_glb (Ha : IsGlb s a) (Hb : IsLub s b) (hab : b ≤ a) :
    s.Subsingleton := fun _ hx _ hy =>
  le_antisymm (le_of_is_lub_le_is_glb Ha Hb hab hx hy) (le_of_is_lub_le_is_glb Ha Hb hab hy hx)
#align set.subsingleton_of_is_lub_le_is_glb Set.subsingleton_of_is_lub_le_is_glb

theorem is_glb_lt_is_lub_of_ne (Ha : IsGlb s a) (Hb : IsLub s b) {x y} (Hx : x ∈ s) (Hy : y ∈ s)
    (Hxy : x ≠ y) : a < b :=
  lt_iff_le_not_le.2
    ⟨lower_bounds_le_upper_bounds Ha.1 Hb.1 ⟨x, Hx⟩, fun hab =>
      Hxy <| Set.subsingleton_of_is_lub_le_is_glb Ha Hb hab Hx Hy⟩
#align is_glb_lt_is_lub_of_ne is_glb_lt_is_lub_of_ne

end PartialOrder

section LinearOrder

variable [LinearOrder α] {s : Set α} {a b : α}

theorem lt_is_lub_iff (h : IsLub s a) : b < a ↔ ∃ c ∈ s, b < c := by
  simp only [← not_le, is_lub_le_iff h, mem_upper_bounds, not_forall]
#align lt_is_lub_iff lt_is_lub_iff

theorem is_glb_lt_iff (h : IsGlb s a) : a < b ↔ ∃ c ∈ s, c < b :=
  lt_is_lub_iff h.dual
#align is_glb_lt_iff is_glb_lt_iff

theorem IsLub.exists_between (h : IsLub s a) (hb : b < a) : ∃ c ∈ s, b < c ∧ c ≤ a :=
  let ⟨c, hcs, hbc⟩ := (lt_is_lub_iff h).1 hb
  ⟨c, hcs, hbc, h.1 hcs⟩
#align is_lub.exists_between IsLub.exists_between

theorem IsLub.exists_between' (h : IsLub s a) (h' : a ∉ s) (hb : b < a) : ∃ c ∈ s, b < c ∧ c < a :=
  let ⟨c, hcs, hbc, hca⟩ := h.exists_between hb
  ⟨c, hcs, hbc, hca.lt_of_ne fun hac => h' <| hac ▸ hcs⟩
#align is_lub.exists_between' IsLub.exists_between'

theorem IsGlb.exists_between (h : IsGlb s a) (hb : a < b) : ∃ c ∈ s, a ≤ c ∧ c < b :=
  let ⟨c, hcs, hbc⟩ := (is_glb_lt_iff h).1 hb
  ⟨c, hcs, h.1 hcs, hbc⟩
#align is_glb.exists_between IsGlb.exists_between

theorem IsGlb.exists_between' (h : IsGlb s a) (h' : a ∉ s) (hb : a < b) : ∃ c ∈ s, a < c ∧ c < b :=
  let ⟨c, hcs, hac, hcb⟩ := h.exists_between hb
  ⟨c, hcs, hac.lt_of_ne fun hac => h' <| hac.symm ▸ hcs, hcb⟩
#align is_glb.exists_between' IsGlb.exists_between'

end LinearOrder

/-!
### Images of upper/lower bounds under monotone functions
-/


namespace MonotoneOn

variable [Preorder α] [Preorder β] {f : α → β} {s t : Set α} (Hf : MonotoneOn f t) {a : α}
  (Hst : s ⊆ t)

-- Porting note: include is deprecated
--include Hf

theorem mem_upper_bounds_image (Has : a ∈ upperBounds s) (Hat : a ∈ t) :
    f a ∈ upperBounds (f '' s) :=
  ball_image_of_ball fun _ H => Hf (Hst H) Hat (Has H)
#align monotone_on.mem_upper_bounds_image MonotoneOn.mem_upper_bounds_image

theorem mem_upper_bounds_image_self : a ∈ upperBounds t → a ∈ t → f a ∈ upperBounds (f '' t) :=
  Hf.mem_upper_bounds_image subset_rfl
#align monotone_on.mem_upper_bounds_image_self MonotoneOn.mem_upper_bounds_image_self

theorem mem_lower_bounds_image (Has : a ∈ lowerBounds s) (Hat : a ∈ t) :
    f a ∈ lowerBounds (f '' s) :=
  ball_image_of_ball fun _ H => Hf Hat (Hst H) (Has H)
#align monotone_on.mem_lower_bounds_image MonotoneOn.mem_lower_bounds_image

theorem mem_lower_bounds_image_self : a ∈ lowerBounds t → a ∈ t → f a ∈ lowerBounds (f '' t) :=
  Hf.mem_lower_bounds_image subset_rfl
#align monotone_on.mem_lower_bounds_image_self MonotoneOn.mem_lower_bounds_image_self

theorem image_upper_bounds_subset_upper_bounds_image (Hst : s ⊆ t) :
    f '' (upperBounds s ∩ t) ⊆ upperBounds (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩
  exact Hf.mem_upper_bounds_image Hst ha.1 ha.2
#align
  monotone_on.image_upper_bounds_subset_upper_bounds_image MonotoneOn.image_upper_bounds_subset_upper_bounds_image

theorem image_lower_bounds_subset_lower_bounds_image :
    f '' (lowerBounds s ∩ t) ⊆ lowerBounds (f '' s) :=
  Hf.dual.image_upper_bounds_subset_upper_bounds_image Hst
#align
  monotone_on.image_lower_bounds_subset_lower_bounds_image MonotoneOn.image_lower_bounds_subset_lower_bounds_image

/-- The image under a monotone function on a set `t` of a subset which has an upper bound in `t`
  is bounded above. -/
theorem map_bdd_above : (upperBounds s ∩ t).Nonempty → BddAbove (f '' s) := fun ⟨C, hs, ht⟩ =>
  ⟨f C, Hf.mem_upper_bounds_image Hst hs ht⟩
#align monotone_on.map_bdd_above MonotoneOn.map_bdd_above

/-- The image under a monotone function on a set `t` of a subset which has a lower bound in `t`
  is bounded below. -/
theorem map_bdd_below : (lowerBounds s ∩ t).Nonempty → BddBelow (f '' s) := fun ⟨C, hs, ht⟩ =>
  ⟨f C, Hf.mem_lower_bounds_image Hst hs ht⟩
#align monotone_on.map_bdd_below MonotoneOn.map_bdd_below

/-- A monotone map sends a least element of a set to a least element of its image. -/
theorem map_is_least (Ha : IsLeast t a) : IsLeast (f '' t) (f a) :=
  ⟨mem_image_of_mem _ Ha.1, Hf.mem_lower_bounds_image_self Ha.2 Ha.1⟩
#align monotone_on.map_is_least MonotoneOn.map_is_least

/-- A monotone map sends a greatest element of a set to a greatest element of its image. -/
theorem map_is_greatest (Ha : IsGreatest t a) : IsGreatest (f '' t) (f a) :=
  ⟨mem_image_of_mem _ Ha.1, Hf.mem_upper_bounds_image_self Ha.2 Ha.1⟩
#align monotone_on.map_is_greatest MonotoneOn.map_is_greatest

end MonotoneOn

namespace AntitoneOn

variable [Preorder α] [Preorder β] {f : α → β} {s t : Set α} (Hf : AntitoneOn f t) {a : α}
  (Hst : s ⊆ t)

-- Porting note: include is deprecated
--include Hf

theorem mem_upper_bounds_image (Has : a ∈ lowerBounds s) : a ∈ t → f a ∈ upperBounds (f '' s) :=
  Hf.dual_right.mem_lower_bounds_image Hst Has
#align antitone_on.mem_upper_bounds_image AntitoneOn.mem_upper_bounds_image

theorem mem_upper_bounds_image_self : a ∈ lowerBounds t → a ∈ t → f a ∈ upperBounds (f '' t) :=
  Hf.dual_right.mem_lower_bounds_image_self
#align antitone_on.mem_upper_bounds_image_self AntitoneOn.mem_upper_bounds_image_self

theorem mem_lower_bounds_image : a ∈ upperBounds s → a ∈ t → f a ∈ lowerBounds (f '' s) :=
  Hf.dual_right.mem_upper_bounds_image Hst
#align antitone_on.mem_lower_bounds_image AntitoneOn.mem_lower_bounds_image

theorem mem_lower_bounds_image_self : a ∈ upperBounds t → a ∈ t → f a ∈ lowerBounds (f '' t) :=
  Hf.dual_right.mem_upper_bounds_image_self
#align antitone_on.mem_lower_bounds_image_self AntitoneOn.mem_lower_bounds_image_self

theorem image_lower_bounds_subset_upper_bounds_image :
    f '' (lowerBounds s ∩ t) ⊆ upperBounds (f '' s) :=
  Hf.dual_right.image_lower_bounds_subset_lower_bounds_image Hst
#align
  antitone_on.image_lower_bounds_subset_upper_bounds_image AntitoneOn.image_lower_bounds_subset_upper_bounds_image

theorem image_upper_bounds_subset_lower_bounds_image :
    f '' (upperBounds s ∩ t) ⊆ lowerBounds (f '' s) :=
  Hf.dual_right.image_upper_bounds_subset_upper_bounds_image Hst
#align
  antitone_on.image_upper_bounds_subset_lower_bounds_image AntitoneOn.image_upper_bounds_subset_lower_bounds_image

/-- The image under an antitone function of a set which is bounded above is bounded below. -/
theorem map_bdd_above : (upperBounds s ∩ t).Nonempty → BddBelow (f '' s) :=
  Hf.dual_right.map_bdd_above Hst
#align antitone_on.map_bdd_above AntitoneOn.map_bdd_above

/-- The image under an antitone function of a set which is bounded below is bounded above. -/
theorem map_bdd_below : (lowerBounds s ∩ t).Nonempty → BddAbove (f '' s) :=
  Hf.dual_right.map_bdd_below Hst
#align antitone_on.map_bdd_below AntitoneOn.map_bdd_below

/-- An antitone map sends a greatest element of a set to a least element of its image. -/
theorem map_is_greatest : IsGreatest t a → IsLeast (f '' t) (f a) :=
  Hf.dual_right.map_is_greatest
#align antitone_on.map_is_greatest AntitoneOn.map_is_greatest

/-- An antitone map sends a least element of a set to a greatest element of its image. -/
theorem map_is_least : IsLeast t a → IsGreatest (f '' t) (f a) :=
  Hf.dual_right.map_is_least
#align antitone_on.map_is_least AntitoneOn.map_is_least

end AntitoneOn

namespace Monotone

variable [Preorder α] [Preorder β] {f : α → β} (Hf : Monotone f) {a : α} {s : Set α}

-- Porting note: include is deprecated
--include Hf

theorem mem_upper_bounds_image (Ha : a ∈ upperBounds s) : f a ∈ upperBounds (f '' s) :=
  ball_image_of_ball fun _ H => Hf (Ha H)
#align monotone.mem_upper_bounds_image Monotone.mem_upper_bounds_image

theorem mem_lower_bounds_image (Ha : a ∈ lowerBounds s) : f a ∈ lowerBounds (f '' s) :=
  ball_image_of_ball fun _ H => Hf (Ha H)
#align monotone.mem_lower_bounds_image Monotone.mem_lower_bounds_image

theorem image_upper_bounds_subset_upper_bounds_image : f '' upperBounds s ⊆ upperBounds (f '' s) :=
  by
  rintro _ ⟨a, ha, rfl⟩
  exact Hf.mem_upper_bounds_image ha
#align
  monotone.image_upper_bounds_subset_upper_bounds_image Monotone.image_upper_bounds_subset_upper_bounds_image

theorem image_lower_bounds_subset_lower_bounds_image : f '' lowerBounds s ⊆ lowerBounds (f '' s) :=
  Hf.dual.image_upper_bounds_subset_upper_bounds_image
#align
  monotone.image_lower_bounds_subset_lower_bounds_image Monotone.image_lower_bounds_subset_lower_bounds_image

/-- The image under a monotone function of a set which is bounded above is bounded above. See also
`bdd_above.image2`. -/
theorem map_bdd_above : BddAbove s → BddAbove (f '' s)
  | ⟨C, hC⟩ => ⟨f C, Hf.mem_upper_bounds_image hC⟩
#align monotone.map_bdd_above Monotone.map_bdd_above

/-- The image under a monotone function of a set which is bounded below is bounded below. See also
`bdd_below.image2`. -/
theorem map_bdd_below : BddBelow s → BddBelow (f '' s)
  | ⟨C, hC⟩ => ⟨f C, Hf.mem_lower_bounds_image hC⟩
#align monotone.map_bdd_below Monotone.map_bdd_below

/-- A monotone map sends a least element of a set to a least element of its image. -/
theorem map_is_least (Ha : IsLeast s a) : IsLeast (f '' s) (f a) :=
  ⟨mem_image_of_mem _ Ha.1, Hf.mem_lower_bounds_image Ha.2⟩
#align monotone.map_is_least Monotone.map_is_least

/-- A monotone map sends a greatest element of a set to a greatest element of its image. -/
theorem map_is_greatest (Ha : IsGreatest s a) : IsGreatest (f '' s) (f a) :=
  ⟨mem_image_of_mem _ Ha.1, Hf.mem_upper_bounds_image Ha.2⟩
#align monotone.map_is_greatest Monotone.map_is_greatest

end Monotone

namespace Antitone

variable [Preorder α] [Preorder β] {f : α → β} (hf : Antitone f) {a : α} {s : Set α}

theorem mem_upper_bounds_image : a ∈ lowerBounds s → f a ∈ upperBounds (f '' s) :=
  hf.dual_right.mem_lower_bounds_image
#align antitone.mem_upper_bounds_image Antitone.mem_upper_bounds_image

theorem mem_lower_bounds_image : a ∈ upperBounds s → f a ∈ lowerBounds (f '' s) :=
  hf.dual_right.mem_upper_bounds_image
#align antitone.mem_lower_bounds_image Antitone.mem_lower_bounds_image

theorem image_lower_bounds_subset_upper_bounds_image : f '' lowerBounds s ⊆ upperBounds (f '' s) :=
  hf.dual_right.image_lower_bounds_subset_lower_bounds_image
#align
  antitone.image_lower_bounds_subset_upper_bounds_image Antitone.image_lower_bounds_subset_upper_bounds_image

theorem image_upper_bounds_subset_lower_bounds_image : f '' upperBounds s ⊆ lowerBounds (f '' s) :=
  hf.dual_right.image_upper_bounds_subset_upper_bounds_image
#align
  antitone.image_upper_bounds_subset_lower_bounds_image Antitone.image_upper_bounds_subset_lower_bounds_image

/-- The image under an antitone function of a set which is bounded above is bounded below. -/
theorem map_bdd_above : BddAbove s → BddBelow (f '' s) :=
  hf.dual_right.map_bdd_above
#align antitone.map_bdd_above Antitone.map_bdd_above

/-- The image under an antitone function of a set which is bounded below is bounded above. -/
theorem map_bdd_below : BddBelow s → BddAbove (f '' s) :=
  hf.dual_right.map_bdd_below
#align antitone.map_bdd_below Antitone.map_bdd_below

/-- An antitone map sends a greatest element of a set to a least element of its image. -/
theorem map_is_greatest : IsGreatest s a → IsLeast (f '' s) (f a) :=
  hf.dual_right.map_is_greatest
#align antitone.map_is_greatest Antitone.map_is_greatest

/-- An antitone map sends a least element of a set to a greatest element of its image. -/
theorem map_is_least : IsLeast s a → IsGreatest (f '' s) (f a) :=
  hf.dual_right.map_is_least
#align antitone.map_is_least Antitone.map_is_least

end Antitone

section Image2

variable [Preorder α] [Preorder β] [Preorder γ] {f : α → β → γ} {s : Set α} {t : Set β} {a : α}
  {b : β}

section MonotoneMonotone

variable (h₀ : ∀ b, Monotone (swap f b)) (h₁ : ∀ a, Monotone (f a))

-- Porting note: include is deprecated
--include h₀ h₁

theorem mem_upper_bounds_image2 (ha : a ∈ upperBounds s) (hb : b ∈ upperBounds t) :
    f a b ∈ upperBounds (image2 f s t) :=
  forall_image2_iff.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy
#align mem_upper_bounds_image2 mem_upper_bounds_image2

theorem mem_lower_bounds_image2 (ha : a ∈ lowerBounds s) (hb : b ∈ lowerBounds t) :
    f a b ∈ lowerBounds (image2 f s t) :=
  forall_image2_iff.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy
#align mem_lower_bounds_image2 mem_lower_bounds_image2

theorem image2_upper_bounds_upper_bounds_subset :
    image2 f (upperBounds s) (upperBounds t) ⊆ upperBounds (image2 f s t) := by
  rintro _ ⟨a, b, ha, hb, rfl⟩
  exact mem_upper_bounds_image2 h₀ h₁ ha hb
#align image2_upper_bounds_upper_bounds_subset image2_upper_bounds_upper_bounds_subset

theorem image2_lower_bounds_lower_bounds_subset :
    image2 f (lowerBounds s) (lowerBounds t) ⊆ lowerBounds (image2 f s t) := by
  rintro _ ⟨a, b, ha, hb, rfl⟩
  exact mem_lower_bounds_image2 h₀ h₁ ha hb
#align image2_lower_bounds_lower_bounds_subset image2_lower_bounds_lower_bounds_subset

/-- See also `monotone.map_bdd_above`. -/
theorem BddAbove.image2 : BddAbove s → BddAbove t → BddAbove (image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upper_bounds_image2 h₀ h₁ ha hb⟩
#align bdd_above.image2 BddAbove.image2

/-- See also `monotone.map_bdd_below`. -/
theorem BddBelow.image2 : BddBelow s → BddBelow t → BddBelow (image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_lower_bounds_image2 h₀ h₁ ha hb⟩
#align bdd_below.image2 BddBelow.image2

theorem IsGreatest.image2 (ha : IsGreatest s a) (hb : IsGreatest t b) :
    IsGreatest (image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_upper_bounds_image2 h₀ h₁ ha.2 hb.2⟩
#align is_greatest.image2 IsGreatest.image2

theorem IsLeast.image2 (ha : IsLeast s a) (hb : IsLeast t b) : IsLeast (image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_lower_bounds_image2 h₀ h₁ ha.2 hb.2⟩
#align is_least.image2 IsLeast.image2

end MonotoneMonotone

section MonotoneAntitone

variable (h₀ : ∀ b, Monotone (swap f b)) (h₁ : ∀ a, Antitone (f a))

-- Porting note: include is deprecated
--include h₀ h₁

theorem mem_upper_bounds_image2_of_mem_upper_bounds_of_mem_lower_bounds (ha : a ∈ upperBounds s)
    (hb : b ∈ lowerBounds t) : f a b ∈ upperBounds (image2 f s t) :=
  forall_image2_iff.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy
#align
  mem_upper_bounds_image2_of_mem_upper_bounds_of_mem_lower_bounds mem_upper_bounds_image2_of_mem_upper_bounds_of_mem_lower_bounds

theorem mem_lower_bounds_image2_of_mem_lower_bounds_of_mem_upper_bounds (ha : a ∈ lowerBounds s)
    (hb : b ∈ upperBounds t) : f a b ∈ lowerBounds (image2 f s t) :=
  forall_image2_iff.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy
#align
  mem_lower_bounds_image2_of_mem_lower_bounds_of_mem_upper_bounds mem_lower_bounds_image2_of_mem_lower_bounds_of_mem_upper_bounds

theorem image2_upper_bounds_lower_bounds_subset_upper_bounds_image2 :
    image2 f (upperBounds s) (lowerBounds t) ⊆ upperBounds (image2 f s t) := by
  rintro _ ⟨a, b, ha, hb, rfl⟩
  exact mem_upper_bounds_image2_of_mem_upper_bounds_of_mem_lower_bounds h₀ h₁ ha hb
#align
  image2_upper_bounds_lower_bounds_subset_upper_bounds_image2 image2_upper_bounds_lower_bounds_subset_upper_bounds_image2

theorem image2_lower_bounds_upper_bounds_subset_lower_bounds_image2 :
    image2 f (lowerBounds s) (upperBounds t) ⊆ lowerBounds (image2 f s t) := by
  rintro _ ⟨a, b, ha, hb, rfl⟩
  exact mem_lower_bounds_image2_of_mem_lower_bounds_of_mem_upper_bounds h₀ h₁ ha hb
#align
  image2_lower_bounds_upper_bounds_subset_lower_bounds_image2 image2_lower_bounds_upper_bounds_subset_lower_bounds_image2

theorem BddAbove.bdd_above_image2_of_bdd_below :
    BddAbove s → BddBelow t → BddAbove (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upper_bounds_image2_of_mem_upper_bounds_of_mem_lower_bounds h₀ h₁ ha hb⟩
#align bdd_above.bdd_above_image2_of_bdd_below BddAbove.bdd_above_image2_of_bdd_below

theorem BddBelow.bdd_below_image2_of_bdd_above :
    BddBelow s → BddAbove t → BddBelow (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_lower_bounds_image2_of_mem_lower_bounds_of_mem_upper_bounds h₀ h₁ ha hb⟩
#align bdd_below.bdd_below_image2_of_bdd_above BddBelow.bdd_below_image2_of_bdd_above

theorem IsGreatest.is_greatest_image2_of_is_least (ha : IsGreatest s a) (hb : IsLeast t b) :
    IsGreatest (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1,
    mem_upper_bounds_image2_of_mem_upper_bounds_of_mem_lower_bounds h₀ h₁ ha.2 hb.2⟩
#align is_greatest.is_greatest_image2_of_is_least IsGreatest.is_greatest_image2_of_is_least

theorem IsLeast.is_least_image2_of_is_greatest (ha : IsLeast s a) (hb : IsGreatest t b) :
    IsLeast (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1,
    mem_lower_bounds_image2_of_mem_lower_bounds_of_mem_upper_bounds h₀ h₁ ha.2 hb.2⟩
#align is_least.is_least_image2_of_is_greatest IsLeast.is_least_image2_of_is_greatest

end MonotoneAntitone

section AntitoneAntitone

variable (h₀ : ∀ b, Antitone (swap f b)) (h₁ : ∀ a, Antitone (f a))

-- Porting note: include is deprecated
--include h₀ h₁

theorem mem_upper_bounds_image2_of_mem_lower_bounds (ha : a ∈ lowerBounds s)
    (hb : b ∈ lowerBounds t) : f a b ∈ upperBounds (image2 f s t) :=
  forall_image2_iff.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy
#align mem_upper_bounds_image2_of_mem_lower_bounds mem_upper_bounds_image2_of_mem_lower_bounds

theorem mem_lower_bounds_image2_of_mem_upper_bounds (ha : a ∈ upperBounds s)
    (hb : b ∈ upperBounds t) : f a b ∈ lowerBounds (image2 f s t) :=
  forall_image2_iff.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy
#align mem_lower_bounds_image2_of_mem_upper_bounds mem_lower_bounds_image2_of_mem_upper_bounds

theorem image2_upper_bounds_upper_bounds_subset_upper_bounds_image2 :
    image2 f (lowerBounds s) (lowerBounds t) ⊆ upperBounds (image2 f s t) := by
  rintro _ ⟨a, b, ha, hb, rfl⟩
  exact mem_upper_bounds_image2_of_mem_lower_bounds h₀ h₁ ha hb
#align
  image2_upper_bounds_upper_bounds_subset_upper_bounds_image2 image2_upper_bounds_upper_bounds_subset_upper_bounds_image2

theorem image2_lower_bounds_lower_bounds_subset_lower_bounds_image2 :
    image2 f (upperBounds s) (upperBounds t) ⊆ lowerBounds (image2 f s t) := by
  rintro _ ⟨a, b, ha, hb, rfl⟩
  exact mem_lower_bounds_image2_of_mem_upper_bounds h₀ h₁ ha hb
#align
  image2_lower_bounds_lower_bounds_subset_lower_bounds_image2 image2_lower_bounds_lower_bounds_subset_lower_bounds_image2

theorem BddBelow.image2_bdd_above : BddBelow s → BddBelow t → BddAbove (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upper_bounds_image2_of_mem_lower_bounds h₀ h₁ ha hb⟩
#align bdd_below.image2_bdd_above BddBelow.image2_bdd_above

theorem BddAbove.image2_bdd_below : BddAbove s → BddAbove t → BddBelow (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_lower_bounds_image2_of_mem_upper_bounds h₀ h₁ ha hb⟩
#align bdd_above.image2_bdd_below BddAbove.image2_bdd_below

theorem IsLeast.is_greatest_image2 (ha : IsLeast s a) (hb : IsLeast t b) :
    IsGreatest (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_upper_bounds_image2_of_mem_lower_bounds h₀ h₁ ha.2 hb.2⟩
#align is_least.is_greatest_image2 IsLeast.is_greatest_image2

theorem IsGreatest.is_least_image2 (ha : IsGreatest s a) (hb : IsGreatest t b) :
    IsLeast (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_lower_bounds_image2_of_mem_upper_bounds h₀ h₁ ha.2 hb.2⟩
#align is_greatest.is_least_image2 IsGreatest.is_least_image2

end AntitoneAntitone

section AntitoneMonotone

variable (h₀ : ∀ b, Antitone (swap f b)) (h₁ : ∀ a, Monotone (f a))

-- Porting note: include is deprecated
--include h₀ h₁

theorem mem_upper_bounds_image2_of_mem_upper_bounds_of_mem_upper_bounds (ha : a ∈ lowerBounds s)
    (hb : b ∈ upperBounds t) : f a b ∈ upperBounds (image2 f s t) :=
  forall_image2_iff.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy
#align
  mem_upper_bounds_image2_of_mem_upper_bounds_of_mem_upper_bounds mem_upper_bounds_image2_of_mem_upper_bounds_of_mem_upper_bounds

theorem mem_lower_bounds_image2_of_mem_lower_bounds_of_mem_lower_bounds (ha : a ∈ upperBounds s)
    (hb : b ∈ lowerBounds t) : f a b ∈ lowerBounds (image2 f s t) :=
  forall_image2_iff.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy
#align
  mem_lower_bounds_image2_of_mem_lower_bounds_of_mem_lower_bounds mem_lower_bounds_image2_of_mem_lower_bounds_of_mem_lower_bounds

theorem image2_lower_bounds_upper_bounds_subset_upper_bounds_image2 :
    image2 f (lowerBounds s) (upperBounds t) ⊆ upperBounds (image2 f s t) := by
  rintro _ ⟨a, b, ha, hb, rfl⟩
  exact mem_upper_bounds_image2_of_mem_upper_bounds_of_mem_upper_bounds h₀ h₁ ha hb
#align
  image2_lower_bounds_upper_bounds_subset_upper_bounds_image2 image2_lower_bounds_upper_bounds_subset_upper_bounds_image2

theorem image2_upper_bounds_lower_bounds_subset_lower_bounds_image2 :
    image2 f (upperBounds s) (lowerBounds t) ⊆ lowerBounds (image2 f s t) := by
  rintro _ ⟨a, b, ha, hb, rfl⟩
  exact mem_lower_bounds_image2_of_mem_lower_bounds_of_mem_lower_bounds h₀ h₁ ha hb
#align
  image2_upper_bounds_lower_bounds_subset_lower_bounds_image2 image2_upper_bounds_lower_bounds_subset_lower_bounds_image2

theorem BddBelow.bdd_above_image2_of_bdd_above :
    BddBelow s → BddAbove t → BddAbove (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upper_bounds_image2_of_mem_upper_bounds_of_mem_upper_bounds h₀ h₁ ha hb⟩
#align bdd_below.bdd_above_image2_of_bdd_above BddBelow.bdd_above_image2_of_bdd_above

theorem BddAbove.bdd_below_image2_of_bdd_above :
    BddAbove s → BddBelow t → BddBelow (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_lower_bounds_image2_of_mem_lower_bounds_of_mem_lower_bounds h₀ h₁ ha hb⟩
#align bdd_above.bdd_below_image2_of_bdd_above BddAbove.bdd_below_image2_of_bdd_above

theorem IsLeast.is_greatest_image2_of_is_greatest (ha : IsLeast s a) (hb : IsGreatest t b) :
    IsGreatest (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1,
    mem_upper_bounds_image2_of_mem_upper_bounds_of_mem_upper_bounds h₀ h₁ ha.2 hb.2⟩
#align is_least.is_greatest_image2_of_is_greatest IsLeast.is_greatest_image2_of_is_greatest

theorem IsGreatest.is_least_image2_of_is_least (ha : IsGreatest s a) (hb : IsLeast t b) :
    IsLeast (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1,
    mem_lower_bounds_image2_of_mem_lower_bounds_of_mem_lower_bounds h₀ h₁ ha.2 hb.2⟩
#align is_greatest.is_least_image2_of_is_least IsGreatest.is_least_image2_of_is_least

end AntitoneMonotone

end Image2

theorem IsGlb.of_image [Preorder α] [Preorder β] {f : α → β} (hf : ∀ {x y}, f x ≤ f y ↔ x ≤ y)
    {s : Set α} {x : α} (hx : IsGlb (f '' s) (f x)) : IsGlb s x :=
  ⟨fun _ hy => hf.1 <| hx.1 <| mem_image_of_mem _ hy, fun _ hy =>
    hf.1 <| hx.2 <| Monotone.mem_lower_bounds_image (fun _ _ => hf.2) hy⟩
#align is_glb.of_image IsGlb.of_image

theorem IsLub.of_image [Preorder α] [Preorder β] {f : α → β} (hf : ∀ {x y}, f x ≤ f y ↔ x ≤ y)
    {s : Set α} {x : α} (hx : IsLub (f '' s) (f x)) : IsLub s x :=
  @IsGlb.of_image αᵒᵈ βᵒᵈ _ _ f (fun x y => hf) _ _ hx
#align is_lub.of_image IsLub.of_image

theorem is_lub_pi {π : α → Type _} [∀ a, Preorder (π a)] {s : Set (∀ a, π a)} {f : ∀ a, π a} :
    IsLub s f ↔ ∀ a, IsLub (Function.eval a '' s) (f a) := by
  classical
    refine'
      ⟨fun H a => ⟨(Function.monotone_eval a).mem_upper_bounds_image H.1, fun b hb => _⟩, fun H =>
        ⟨_, _⟩⟩
    · suffices : Function.update f a b ∈ upperBounds s
      exact Function.update_same a b f ▸ H.2 this a
      refine' fun g hg => le_update_iff.2 ⟨hb <| mem_image_of_mem _ hg, fun i hi => H.1 hg i⟩
    · exact fun g hg a => (H a).1 (mem_image_of_mem _ hg)
    · exact fun g hg a => (H a).2 ((Function.monotone_eval a).mem_upper_bounds_image hg)
#align is_lub_pi is_lub_pi

theorem is_glb_pi {π : α → Type _} [∀ a, Preorder (π a)] {s : Set (∀ a, π a)} {f : ∀ a, π a} :
    IsGlb s f ↔ ∀ a, IsGlb (Function.eval a '' s) (f a) :=
  @is_lub_pi α (fun a => (π a)ᵒᵈ) _ s f
#align is_glb_pi is_glb_pi

theorem is_lub_prod [Preorder α] [Preorder β] {s : Set (α × β)} (p : α × β) :
    IsLub s p ↔ IsLub (Prod.fst '' s) p.1 ∧ IsLub (Prod.snd '' s) p.2 := by
  refine'
    ⟨fun H =>
      ⟨⟨monotone_fst.mem_upper_bounds_image H.1, fun a ha => _⟩,
        ⟨monotone_snd.mem_upper_bounds_image H.1, fun a ha => _⟩⟩,
      fun H => ⟨_, _⟩⟩
  · suffices : (a, p.2) ∈ upperBounds s
    exact (H.2 this).1
    exact fun q hq => ⟨ha <| mem_image_of_mem _ hq, (H.1 hq).2⟩
  · suffices : (p.1, a) ∈ upperBounds s
    exact (H.2 this).2
    exact fun q hq => ⟨(H.1 hq).1, ha <| mem_image_of_mem _ hq⟩
  · exact fun q hq => ⟨H.1.1 <| mem_image_of_mem _ hq, H.2.1 <| mem_image_of_mem _ hq⟩
  ·
    exact fun q hq =>
      ⟨H.1.2 <| monotone_fst.mem_upper_bounds_image hq,
        H.2.2 <| monotone_snd.mem_upper_bounds_image hq⟩
#align is_lub_prod is_lub_prod

theorem is_glb_prod [Preorder α] [Preorder β] {s : Set (α × β)} (p : α × β) :
    IsGlb s p ↔ IsGlb (Prod.fst '' s) p.1 ∧ IsGlb (Prod.snd '' s) p.2 :=
  @is_lub_prod αᵒᵈ βᵒᵈ _ _ _ _
#align is_glb_prod is_glb_prod
