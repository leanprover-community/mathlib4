/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Set.NAry
import Mathlib.Order.Directed

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

/-- The set of lower bounds of a set. -/
def lowerBounds (s : Set α) : Set α :=
  { x | ∀ ⦃a⦄, a ∈ s → x ≤ a }

/-- A set is bounded above if there exists an upper bound. -/
def BddAbove (s : Set α) :=
  (upperBounds s).Nonempty

/-- A set is bounded below if there exists a lower bound. -/
def BddBelow (s : Set α) :=
  (lowerBounds s).Nonempty

/-- `a` is a least element of a set `s`; for a partial order, it is unique if exists. -/
def IsLeast (s : Set α) (a : α) : Prop :=
  a ∈ s ∧ a ∈ lowerBounds s

/-- `a` is a greatest element of a set `s`; for a partial order, it is unique if exists. -/
def IsGreatest (s : Set α) (a : α) : Prop :=
  a ∈ s ∧ a ∈ upperBounds s

/-- `a` is a least upper bound of a set `s`; for a partial order, it is unique if exists. -/
def IsLUB (s : Set α) : α → Prop :=
  IsLeast (upperBounds s)

/-- `a` is a greatest lower bound of a set `s`; for a partial order, it is unique if exists. -/
def IsGLB (s : Set α) : α → Prop :=
  IsGreatest (lowerBounds s)

theorem mem_upperBounds : a ∈ upperBounds s ↔ ∀ x ∈ s, x ≤ a :=
  Iff.rfl

theorem mem_lowerBounds : a ∈ lowerBounds s ↔ ∀ x ∈ s, a ≤ x :=
  Iff.rfl

lemma mem_upperBounds_iff_subset_Iic : a ∈ upperBounds s ↔ s ⊆ Iic a := Iff.rfl

lemma mem_lowerBounds_iff_subset_Ici : a ∈ lowerBounds s ↔ s ⊆ Ici a := Iff.rfl

theorem bddAbove_def : BddAbove s ↔ ∃ x, ∀ y ∈ s, y ≤ x :=
  Iff.rfl

theorem bddBelow_def : BddBelow s ↔ ∃ x, ∀ y ∈ s, x ≤ y :=
  Iff.rfl

theorem bot_mem_lowerBounds [OrderBot α] (s : Set α) : ⊥ ∈ lowerBounds s := fun _ _ => bot_le

theorem top_mem_upperBounds [OrderTop α] (s : Set α) : ⊤ ∈ upperBounds s := fun _ _ => le_top

@[simp]
theorem isLeast_bot_iff [OrderBot α] : IsLeast s ⊥ ↔ ⊥ ∈ s :=
  and_iff_left <| bot_mem_lowerBounds _

@[simp]
theorem isGreatest_top_iff [OrderTop α] : IsGreatest s ⊤ ↔ ⊤ ∈ s :=
  and_iff_left <| top_mem_upperBounds _

/-- A set `s` is not bounded above if and only if for each `x` there exists `y ∈ s` such that `x`
is not greater than or equal to `y`. This version only assumes `Preorder` structure and uses
`¬(y ≤ x)`. A version for linear orders is called `not_bddAbove_iff`. -/
theorem not_bddAbove_iff' : ¬BddAbove s ↔ ∀ x, ∃ y ∈ s, ¬y ≤ x := by
  simp [BddAbove, upperBounds, Set.Nonempty]

/-- A set `s` is not bounded below if and only if for each `x` there exists `y ∈ s` such that `x`
is not less than or equal to `y`. This version only assumes `Preorder` structure and uses
`¬(x ≤ y)`. A version for linear orders is called `not_bddBelow_iff`. -/
theorem not_bddBelow_iff' : ¬BddBelow s ↔ ∀ x, ∃ y ∈ s, ¬x ≤ y :=
  @not_bddAbove_iff' αᵒᵈ _ _

/-- A set `s` is not bounded above if and only if for each `x` there exists `y ∈ s` that is greater
than `x`. A version for preorders is called `not_bddAbove_iff'`. -/
theorem not_bddAbove_iff {α : Type*} [LinearOrder α] {s : Set α} :
    ¬BddAbove s ↔ ∀ x, ∃ y ∈ s, x < y := by
  simp only [not_bddAbove_iff', not_le]

/-- A set `s` is not bounded below if and only if for each `x` there exists `y ∈ s` that is less
than `x`. A version for preorders is called `not_bddBelow_iff'`. -/
theorem not_bddBelow_iff {α : Type*} [LinearOrder α] {s : Set α} :
    ¬BddBelow s ↔ ∀ x, ∃ y ∈ s, y < x :=
  @not_bddAbove_iff αᵒᵈ _ _

@[simp] lemma bddBelow_preimage_ofDual {s : Set α} : BddBelow (ofDual ⁻¹' s) ↔ BddAbove s := Iff.rfl
@[simp] lemma bddAbove_preimage_ofDual {s : Set α} : BddAbove (ofDual ⁻¹' s) ↔ BddBelow s := Iff.rfl

@[simp] lemma bddBelow_preimage_toDual {s : Set αᵒᵈ} :
    BddBelow (toDual ⁻¹' s) ↔ BddAbove s := Iff.rfl

@[simp] lemma bddAbove_preimage_toDual {s : Set αᵒᵈ} :
    BddAbove (toDual ⁻¹' s) ↔ BddBelow s := Iff.rfl

theorem BddAbove.dual (h : BddAbove s) : BddBelow (ofDual ⁻¹' s) :=
  h

theorem BddBelow.dual (h : BddBelow s) : BddAbove (ofDual ⁻¹' s) :=
  h

theorem IsLeast.dual (h : IsLeast s a) : IsGreatest (ofDual ⁻¹' s) (toDual a) :=
  h

theorem IsGreatest.dual (h : IsGreatest s a) : IsLeast (ofDual ⁻¹' s) (toDual a) :=
  h

theorem IsLUB.dual (h : IsLUB s a) : IsGLB (ofDual ⁻¹' s) (toDual a) :=
  h

theorem IsGLB.dual (h : IsGLB s a) : IsLUB (ofDual ⁻¹' s) (toDual a) :=
  h

/-- If `a` is the least element of a set `s`, then subtype `s` is an order with bottom element. -/
abbrev IsLeast.orderBot (h : IsLeast s a) :
    OrderBot s where
  bot := ⟨a, h.1⟩
  bot_le := Subtype.forall.2 h.2

/-- If `a` is the greatest element of a set `s`, then subtype `s` is an order with top element. -/
abbrev IsGreatest.orderTop (h : IsGreatest s a) :
    OrderTop s where
  top := ⟨a, h.1⟩
  le_top := Subtype.forall.2 h.2

/-!
### Monotonicity
-/


theorem upperBounds_mono_set ⦃s t : Set α⦄ (hst : s ⊆ t) : upperBounds t ⊆ upperBounds s :=
  fun _ hb _ h => hb <| hst h

theorem lowerBounds_mono_set ⦃s t : Set α⦄ (hst : s ⊆ t) : lowerBounds t ⊆ lowerBounds s :=
  fun _ hb _ h => hb <| hst h

theorem upperBounds_mono_mem ⦃a b⦄ (hab : a ≤ b) : a ∈ upperBounds s → b ∈ upperBounds s :=
  fun ha _ h => le_trans (ha h) hab

theorem lowerBounds_mono_mem ⦃a b⦄ (hab : a ≤ b) : b ∈ lowerBounds s → a ∈ lowerBounds s :=
  fun hb _ h => le_trans hab (hb h)

theorem upperBounds_mono ⦃s t : Set α⦄ (hst : s ⊆ t) ⦃a b⦄ (hab : a ≤ b) :
    a ∈ upperBounds t → b ∈ upperBounds s := fun ha =>
  upperBounds_mono_set hst <| upperBounds_mono_mem hab ha

theorem lowerBounds_mono ⦃s t : Set α⦄ (hst : s ⊆ t) ⦃a b⦄ (hab : a ≤ b) :
    b ∈ lowerBounds t → a ∈ lowerBounds s := fun hb =>
  lowerBounds_mono_set hst <| lowerBounds_mono_mem hab hb

/-- If `s ⊆ t` and `t` is bounded above, then so is `s`. -/
theorem BddAbove.mono ⦃s t : Set α⦄ (h : s ⊆ t) : BddAbove t → BddAbove s :=
  Nonempty.mono <| upperBounds_mono_set h

/-- If `s ⊆ t` and `t` is bounded below, then so is `s`. -/
theorem BddBelow.mono ⦃s t : Set α⦄ (h : s ⊆ t) : BddBelow t → BddBelow s :=
  Nonempty.mono <| lowerBounds_mono_set h

/-- If `a` is a least upper bound for sets `s` and `p`, then it is a least upper bound for any
set `t`, `s ⊆ t ⊆ p`. -/
theorem IsLUB.of_subset_of_superset {s t p : Set α} (hs : IsLUB s a) (hp : IsLUB p a) (hst : s ⊆ t)
    (htp : t ⊆ p) : IsLUB t a :=
  ⟨upperBounds_mono_set htp hp.1, lowerBounds_mono_set (upperBounds_mono_set hst) hs.2⟩

/-- If `a` is a greatest lower bound for sets `s` and `p`, then it is a greater lower bound for any
set `t`, `s ⊆ t ⊆ p`. -/
theorem IsGLB.of_subset_of_superset {s t p : Set α} (hs : IsGLB s a) (hp : IsGLB p a) (hst : s ⊆ t)
    (htp : t ⊆ p) : IsGLB t a :=
  hs.dual.of_subset_of_superset hp hst htp

theorem IsLeast.mono (ha : IsLeast s a) (hb : IsLeast t b) (hst : s ⊆ t) : b ≤ a :=
  hb.2 (hst ha.1)

theorem IsGreatest.mono (ha : IsGreatest s a) (hb : IsGreatest t b) (hst : s ⊆ t) : a ≤ b :=
  hb.2 (hst ha.1)

theorem IsLUB.mono (ha : IsLUB s a) (hb : IsLUB t b) (hst : s ⊆ t) : a ≤ b :=
  IsLeast.mono hb ha <| upperBounds_mono_set hst

theorem IsGLB.mono (ha : IsGLB s a) (hb : IsGLB t b) (hst : s ⊆ t) : b ≤ a :=
  IsGreatest.mono hb ha <| lowerBounds_mono_set hst

theorem subset_lowerBounds_upperBounds (s : Set α) : s ⊆ lowerBounds (upperBounds s) :=
  fun _ hx _ hy => hy hx

theorem subset_upperBounds_lowerBounds (s : Set α) : s ⊆ upperBounds (lowerBounds s) :=
  fun _ hx _ hy => hy hx

theorem Set.Nonempty.bddAbove_lowerBounds (hs : s.Nonempty) : BddAbove (lowerBounds s) :=
  hs.mono (subset_upperBounds_lowerBounds s)

theorem Set.Nonempty.bddBelow_upperBounds (hs : s.Nonempty) : BddBelow (upperBounds s) :=
  hs.mono (subset_lowerBounds_upperBounds s)

/-!
### Conversions
-/


theorem IsLeast.isGLB (h : IsLeast s a) : IsGLB s a :=
  ⟨h.2, fun _ hb => hb h.1⟩

theorem IsGreatest.isLUB (h : IsGreatest s a) : IsLUB s a :=
  ⟨h.2, fun _ hb => hb h.1⟩

theorem IsLUB.upperBounds_eq (h : IsLUB s a) : upperBounds s = Ici a :=
  Set.ext fun _ => ⟨fun hb => h.2 hb, fun hb => upperBounds_mono_mem hb h.1⟩

theorem IsGLB.lowerBounds_eq (h : IsGLB s a) : lowerBounds s = Iic a :=
  h.dual.upperBounds_eq

theorem IsLeast.lowerBounds_eq (h : IsLeast s a) : lowerBounds s = Iic a :=
  h.isGLB.lowerBounds_eq

theorem IsGreatest.upperBounds_eq (h : IsGreatest s a) : upperBounds s = Ici a :=
  h.isLUB.upperBounds_eq

theorem IsGreatest.lt_iff (h : IsGreatest s a) : a < b ↔ ∀ x ∈ s, x < b :=
  ⟨fun hlt _x hx => (h.2 hx).trans_lt hlt, fun h' => h' _ h.1⟩

theorem IsLeast.lt_iff (h : IsLeast s a) : b < a ↔ ∀ x ∈ s, b < x :=
  h.dual.lt_iff

theorem isLUB_le_iff (h : IsLUB s a) : a ≤ b ↔ b ∈ upperBounds s := by
  rw [h.upperBounds_eq]
  rfl

theorem le_isGLB_iff (h : IsGLB s a) : b ≤ a ↔ b ∈ lowerBounds s := by
  rw [h.lowerBounds_eq]
  rfl

theorem isLUB_iff_le_iff : IsLUB s a ↔ ∀ b, a ≤ b ↔ b ∈ upperBounds s :=
  ⟨fun h _ => isLUB_le_iff h, fun H => ⟨(H _).1 le_rfl, fun b hb => (H b).2 hb⟩⟩

theorem isGLB_iff_le_iff : IsGLB s a ↔ ∀ b, b ≤ a ↔ b ∈ lowerBounds s :=
  @isLUB_iff_le_iff αᵒᵈ _ _ _

/-- If `s` has a least upper bound, then it is bounded above. -/
theorem IsLUB.bddAbove (h : IsLUB s a) : BddAbove s :=
  ⟨a, h.1⟩

/-- If `s` has a greatest lower bound, then it is bounded below. -/
theorem IsGLB.bddBelow (h : IsGLB s a) : BddBelow s :=
  ⟨a, h.1⟩

/-- If `s` has a greatest element, then it is bounded above. -/
theorem IsGreatest.bddAbove (h : IsGreatest s a) : BddAbove s :=
  ⟨a, h.2⟩

/-- If `s` has a least element, then it is bounded below. -/
theorem IsLeast.bddBelow (h : IsLeast s a) : BddBelow s :=
  ⟨a, h.2⟩

theorem IsLeast.nonempty (h : IsLeast s a) : s.Nonempty :=
  ⟨a, h.1⟩

theorem IsGreatest.nonempty (h : IsGreatest s a) : s.Nonempty :=
  ⟨a, h.1⟩

/-!
### Union and intersection
-/

@[simp]
theorem upperBounds_union : upperBounds (s ∪ t) = upperBounds s ∩ upperBounds t :=
  Subset.antisymm (fun _ hb => ⟨fun _ hx => hb (Or.inl hx), fun _ hx => hb (Or.inr hx)⟩)
    fun _ hb _ hx => hx.elim (fun hs => hb.1 hs) fun ht => hb.2 ht

@[simp]
theorem lowerBounds_union : lowerBounds (s ∪ t) = lowerBounds s ∩ lowerBounds t :=
  @upperBounds_union αᵒᵈ _ s t

theorem union_upperBounds_subset_upperBounds_inter :
    upperBounds s ∪ upperBounds t ⊆ upperBounds (s ∩ t) :=
  union_subset (upperBounds_mono_set inter_subset_left)
    (upperBounds_mono_set inter_subset_right)

theorem union_lowerBounds_subset_lowerBounds_inter :
    lowerBounds s ∪ lowerBounds t ⊆ lowerBounds (s ∩ t) :=
  @union_upperBounds_subset_upperBounds_inter αᵒᵈ _ s t

theorem isLeast_union_iff {a : α} {s t : Set α} :
    IsLeast (s ∪ t) a ↔ IsLeast s a ∧ a ∈ lowerBounds t ∨ a ∈ lowerBounds s ∧ IsLeast t a := by
  simp [IsLeast, lowerBounds_union, or_and_right, and_comm (a := a ∈ t), and_assoc]

theorem isGreatest_union_iff :
    IsGreatest (s ∪ t) a ↔
      IsGreatest s a ∧ a ∈ upperBounds t ∨ a ∈ upperBounds s ∧ IsGreatest t a :=
  @isLeast_union_iff αᵒᵈ _ a s t

/-- If `s` is bounded, then so is `s ∩ t` -/
theorem BddAbove.inter_of_left (h : BddAbove s) : BddAbove (s ∩ t) :=
  h.mono inter_subset_left

/-- If `t` is bounded, then so is `s ∩ t` -/
theorem BddAbove.inter_of_right (h : BddAbove t) : BddAbove (s ∩ t) :=
  h.mono inter_subset_right

/-- If `s` is bounded, then so is `s ∩ t` -/
theorem BddBelow.inter_of_left (h : BddBelow s) : BddBelow (s ∩ t) :=
  h.mono inter_subset_left

/-- If `t` is bounded, then so is `s ∩ t` -/
theorem BddBelow.inter_of_right (h : BddBelow t) : BddBelow (s ∩ t) :=
  h.mono inter_subset_right

/-- In a directed order, the union of bounded above sets is bounded above. -/
theorem BddAbove.union [IsDirected α (· ≤ ·)] {s t : Set α} :
    BddAbove s → BddAbove t → BddAbove (s ∪ t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨c, hca, hcb⟩ := exists_ge_ge a b
  rw [BddAbove, upperBounds_union]
  exact ⟨c, upperBounds_mono_mem hca ha, upperBounds_mono_mem hcb hb⟩

/-- In a directed order, the union of two sets is bounded above if and only if both sets are. -/
theorem bddAbove_union [IsDirected α (· ≤ ·)] {s t : Set α} :
    BddAbove (s ∪ t) ↔ BddAbove s ∧ BddAbove t :=
  ⟨fun h => ⟨h.mono subset_union_left, h.mono subset_union_right⟩, fun h =>
    h.1.union h.2⟩

/-- In a codirected order, the union of bounded below sets is bounded below. -/
theorem BddBelow.union [IsDirected α (· ≥ ·)] {s t : Set α} :
    BddBelow s → BddBelow t → BddBelow (s ∪ t) :=
  @BddAbove.union αᵒᵈ _ _ _ _

/-- In a codirected order, the union of two sets is bounded below if and only if both sets are. -/
theorem bddBelow_union [IsDirected α (· ≥ ·)] {s t : Set α} :
    BddBelow (s ∪ t) ↔ BddBelow s ∧ BddBelow t :=
  @bddAbove_union αᵒᵈ _ _ _ _

/-- If `a` is the least upper bound of `s` and `b` is the least upper bound of `t`,
then `a ⊔ b` is the least upper bound of `s ∪ t`. -/
theorem IsLUB.union [SemilatticeSup γ] {a b : γ} {s t : Set γ} (hs : IsLUB s a) (ht : IsLUB t b) :
    IsLUB (s ∪ t) (a ⊔ b) :=
  ⟨fun _ h =>
    h.casesOn (fun h => le_sup_of_le_left <| hs.left h) fun h => le_sup_of_le_right <| ht.left h,
    fun _ hc =>
    sup_le (hs.right fun _ hd => hc <| Or.inl hd) (ht.right fun _ hd => hc <| Or.inr hd)⟩

/-- If `a` is the greatest lower bound of `s` and `b` is the greatest lower bound of `t`,
then `a ⊓ b` is the greatest lower bound of `s ∪ t`. -/
theorem IsGLB.union [SemilatticeInf γ] {a₁ a₂ : γ} {s t : Set γ} (hs : IsGLB s a₁)
    (ht : IsGLB t a₂) : IsGLB (s ∪ t) (a₁ ⊓ a₂) :=
  hs.dual.union ht

/-- If `a` is the least element of `s` and `b` is the least element of `t`,
then `min a b` is the least element of `s ∪ t`. -/
theorem IsLeast.union [LinearOrder γ] {a b : γ} {s t : Set γ} (ha : IsLeast s a)
    (hb : IsLeast t b) : IsLeast (s ∪ t) (min a b) :=
  ⟨by rcases le_total a b with h | h <;> simp [h, ha.1, hb.1], (ha.isGLB.union hb.isGLB).1⟩

/-- If `a` is the greatest element of `s` and `b` is the greatest element of `t`,
then `max a b` is the greatest element of `s ∪ t`. -/
theorem IsGreatest.union [LinearOrder γ] {a b : γ} {s t : Set γ} (ha : IsGreatest s a)
    (hb : IsGreatest t b) : IsGreatest (s ∪ t) (max a b) :=
  ⟨by rcases le_total a b with h | h <;> simp [h, ha.1, hb.1], (ha.isLUB.union hb.isLUB).1⟩

theorem IsLUB.inter_Ici_of_mem [LinearOrder γ] {s : Set γ} {a b : γ} (ha : IsLUB s a) (hb : b ∈ s) :
    IsLUB (s ∩ Ici b) a :=
  ⟨fun _ hx => ha.1 hx.1, fun c hc =>
    have hbc : b ≤ c := hc ⟨hb, le_rfl⟩
    ha.2 fun x hx => ((le_total x b).elim fun hxb => hxb.trans hbc) fun hbx => hc ⟨hx, hbx⟩⟩

theorem IsGLB.inter_Iic_of_mem [LinearOrder γ] {s : Set γ} {a b : γ} (ha : IsGLB s a) (hb : b ∈ s) :
    IsGLB (s ∩ Iic b) a :=
  ha.dual.inter_Ici_of_mem hb

theorem bddAbove_iff_exists_ge [SemilatticeSup γ] {s : Set γ} (x₀ : γ) :
    BddAbove s ↔ ∃ x, x₀ ≤ x ∧ ∀ y ∈ s, y ≤ x := by
  rw [bddAbove_def, exists_ge_and_iff_exists]
  exact Monotone.ball fun x _ => monotone_le

theorem bddBelow_iff_exists_le [SemilatticeInf γ] {s : Set γ} (x₀ : γ) :
    BddBelow s ↔ ∃ x, x ≤ x₀ ∧ ∀ y ∈ s, x ≤ y :=
  bddAbove_iff_exists_ge (toDual x₀)

theorem BddAbove.exists_ge [SemilatticeSup γ] {s : Set γ} (hs : BddAbove s) (x₀ : γ) :
    ∃ x, x₀ ≤ x ∧ ∀ y ∈ s, y ≤ x :=
  (bddAbove_iff_exists_ge x₀).mp hs

theorem BddBelow.exists_le [SemilatticeInf γ] {s : Set γ} (hs : BddBelow s) (x₀ : γ) :
    ∃ x, x ≤ x₀ ∧ ∀ y ∈ s, x ≤ y :=
  (bddBelow_iff_exists_le x₀).mp hs

/-!
### Specific sets
#### Unbounded intervals
-/


theorem isLeast_Ici : IsLeast (Ici a) a :=
  ⟨left_mem_Ici, fun _ => id⟩

theorem isGreatest_Iic : IsGreatest (Iic a) a :=
  ⟨right_mem_Iic, fun _ => id⟩

theorem isLUB_Iic : IsLUB (Iic a) a :=
  isGreatest_Iic.isLUB

theorem isGLB_Ici : IsGLB (Ici a) a :=
  isLeast_Ici.isGLB

theorem upperBounds_Iic : upperBounds (Iic a) = Ici a :=
  isLUB_Iic.upperBounds_eq

theorem lowerBounds_Ici : lowerBounds (Ici a) = Iic a :=
  isGLB_Ici.lowerBounds_eq

theorem bddAbove_Iic : BddAbove (Iic a) :=
  isLUB_Iic.bddAbove

theorem bddBelow_Ici : BddBelow (Ici a) :=
  isGLB_Ici.bddBelow

theorem bddAbove_Iio : BddAbove (Iio a) :=
  ⟨a, fun _ hx => le_of_lt hx⟩

theorem bddBelow_Ioi : BddBelow (Ioi a) :=
  ⟨a, fun _ hx => le_of_lt hx⟩

theorem lub_Iio_le (a : α) (hb : IsLUB (Iio a) b) : b ≤ a :=
  (isLUB_le_iff hb).mpr fun _ hk => le_of_lt hk

theorem le_glb_Ioi (a : α) (hb : IsGLB (Ioi a) b) : a ≤ b :=
  @lub_Iio_le αᵒᵈ _ _ a hb

theorem lub_Iio_eq_self_or_Iio_eq_Iic [PartialOrder γ] {j : γ} (i : γ) (hj : IsLUB (Iio i) j) :
    j = i ∨ Iio i = Iic j := by
  rcases eq_or_lt_of_le (lub_Iio_le i hj) with hj_eq_i | hj_lt_i
  · exact Or.inl hj_eq_i
  · right
    exact Set.ext fun k => ⟨fun hk_lt => hj.1 hk_lt, fun hk_le_j => lt_of_le_of_lt hk_le_j hj_lt_i⟩

theorem glb_Ioi_eq_self_or_Ioi_eq_Ici [PartialOrder γ] {j : γ} (i : γ) (hj : IsGLB (Ioi i) j) :
    j = i ∨ Ioi i = Ici j :=
  @lub_Iio_eq_self_or_Iio_eq_Iic γᵒᵈ _ j i hj

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

theorem exists_glb_Ioi (i : γ) : ∃ j, IsGLB (Ioi i) j :=
  @exists_lub_Iio γᵒᵈ _ i

variable [DenselyOrdered γ]

theorem isLUB_Iio {a : γ} : IsLUB (Iio a) a :=
  ⟨fun _ hx => le_of_lt hx, fun _ hy => le_of_forall_ge_of_dense hy⟩

theorem isGLB_Ioi {a : γ} : IsGLB (Ioi a) a :=
  @isLUB_Iio γᵒᵈ _ _ a

theorem upperBounds_Iio {a : γ} : upperBounds (Iio a) = Ici a :=
  isLUB_Iio.upperBounds_eq

theorem lowerBounds_Ioi {a : γ} : lowerBounds (Ioi a) = Iic a :=
  isGLB_Ioi.lowerBounds_eq

end

/-!
#### Singleton
-/


@[simp] theorem isGreatest_singleton : IsGreatest {a} a :=
  ⟨mem_singleton a, fun _ hx => le_of_eq <| eq_of_mem_singleton hx⟩

@[simp] theorem isLeast_singleton : IsLeast {a} a :=
  @isGreatest_singleton αᵒᵈ _ a

@[simp] theorem isLUB_singleton : IsLUB {a} a :=
  isGreatest_singleton.isLUB

@[simp] theorem isGLB_singleton : IsGLB {a} a :=
  isLeast_singleton.isGLB

@[simp] lemma bddAbove_singleton : BddAbove ({a} : Set α) := isLUB_singleton.bddAbove

@[simp] lemma bddBelow_singleton : BddBelow ({a} : Set α) := isGLB_singleton.bddBelow

@[simp]
theorem upperBounds_singleton : upperBounds {a} = Ici a :=
  isLUB_singleton.upperBounds_eq

@[simp]
theorem lowerBounds_singleton : lowerBounds {a} = Iic a :=
  isGLB_singleton.lowerBounds_eq

/-!
#### Bounded intervals
-/


theorem bddAbove_Icc : BddAbove (Icc a b) :=
  ⟨b, fun _ => And.right⟩

theorem bddBelow_Icc : BddBelow (Icc a b) :=
  ⟨a, fun _ => And.left⟩

theorem bddAbove_Ico : BddAbove (Ico a b) :=
  bddAbove_Icc.mono Ico_subset_Icc_self

theorem bddBelow_Ico : BddBelow (Ico a b) :=
  bddBelow_Icc.mono Ico_subset_Icc_self

theorem bddAbove_Ioc : BddAbove (Ioc a b) :=
  bddAbove_Icc.mono Ioc_subset_Icc_self

theorem bddBelow_Ioc : BddBelow (Ioc a b) :=
  bddBelow_Icc.mono Ioc_subset_Icc_self

theorem bddAbove_Ioo : BddAbove (Ioo a b) :=
  bddAbove_Icc.mono Ioo_subset_Icc_self

theorem bddBelow_Ioo : BddBelow (Ioo a b) :=
  bddBelow_Icc.mono Ioo_subset_Icc_self

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
  ⟨fun x hx => hx.1.le, fun x hx => by
    rcases eq_or_lt_of_le (le_sup_right : a ≤ x ⊔ a) with h₁ | h₂
    · exact h₁.symm ▸ le_sup_left
    obtain ⟨y, lty, ylt⟩ := exists_between h₂
    apply (not_lt_of_le (sup_le (hx ⟨lty, ylt.trans_le (sup_le _ h.le)⟩) lty.le) ylt).elim
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
  simpa only [dual_Ioo] using isGLB_Ioo hab.dual

theorem upperBounds_Ioo {a b : γ} (hab : a < b) : upperBounds (Ioo a b) = Ici b :=
  (isLUB_Ioo hab).upperBounds_eq

theorem isLUB_Ico {a b : γ} (hab : a < b) : IsLUB (Ico a b) b := by
  simpa only [dual_Ioc] using isGLB_Ioc hab.dual

theorem upperBounds_Ico {a b : γ} (hab : a < b) : upperBounds (Ico a b) = Ici b :=
  (isLUB_Ico hab).upperBounds_eq

end

theorem bddBelow_iff_subset_Ici : BddBelow s ↔ ∃ a, s ⊆ Ici a :=
  Iff.rfl

theorem bddAbove_iff_subset_Iic : BddAbove s ↔ ∃ a, s ⊆ Iic a :=
  Iff.rfl

theorem bddBelow_bddAbove_iff_subset_Icc : BddBelow s ∧ BddAbove s ↔ ∃ a b, s ⊆ Icc a b := by
  simp [Ici_inter_Iic.symm, subset_inter_iff, bddBelow_iff_subset_Ici,
    bddAbove_iff_subset_Iic, exists_and_left, exists_and_right]

/-!
#### Univ
-/

@[simp] theorem isGreatest_univ_iff : IsGreatest univ a ↔ IsTop a := by
  simp [IsGreatest, mem_upperBounds, IsTop]

theorem isGreatest_univ [OrderTop α] : IsGreatest (univ : Set α) ⊤ :=
  isGreatest_univ_iff.2 isTop_top

@[simp]
theorem OrderTop.upperBounds_univ [PartialOrder γ] [OrderTop γ] :
    upperBounds (univ : Set γ) = {⊤} := by rw [isGreatest_univ.upperBounds_eq, Ici_top]

theorem isLUB_univ [OrderTop α] : IsLUB (univ : Set α) ⊤ :=
  isGreatest_univ.isLUB

@[simp]
theorem OrderBot.lowerBounds_univ [PartialOrder γ] [OrderBot γ] :
    lowerBounds (univ : Set γ) = {⊥} :=
  @OrderTop.upperBounds_univ γᵒᵈ _ _

@[simp] theorem isLeast_univ_iff : IsLeast univ a ↔ IsBot a :=
  @isGreatest_univ_iff αᵒᵈ _ _

theorem isLeast_univ [OrderBot α] : IsLeast (univ : Set α) ⊥ :=
  @isGreatest_univ αᵒᵈ _ _

theorem isGLB_univ [OrderBot α] : IsGLB (univ : Set α) ⊥ :=
  isLeast_univ.isGLB

@[simp]
theorem NoMaxOrder.upperBounds_univ [NoMaxOrder α] : upperBounds (univ : Set α) = ∅ :=
  eq_empty_of_subset_empty fun b hb =>
    let ⟨_, hx⟩ := exists_gt b
    not_le_of_lt hx (hb trivial)

@[simp]
theorem NoMinOrder.lowerBounds_univ [NoMinOrder α] : lowerBounds (univ : Set α) = ∅ :=
  @NoMaxOrder.upperBounds_univ αᵒᵈ _ _

@[simp]
theorem not_bddAbove_univ [NoMaxOrder α] : ¬BddAbove (univ : Set α) := by simp [BddAbove]

@[simp]
theorem not_bddBelow_univ [NoMinOrder α] : ¬BddBelow (univ : Set α) :=
  @not_bddAbove_univ αᵒᵈ _ _

/-!
#### Empty set
-/


@[simp]
theorem upperBounds_empty : upperBounds (∅ : Set α) = univ := by
  simp only [upperBounds, eq_univ_iff_forall, mem_setOf_eq, forall_mem_empty, forall_true_iff]

@[simp]
theorem lowerBounds_empty : lowerBounds (∅ : Set α) = univ :=
  @upperBounds_empty αᵒᵈ _

@[simp]
theorem bddAbove_empty [Nonempty α] : BddAbove (∅ : Set α) := by
  simp only [BddAbove, upperBounds_empty, univ_nonempty]

@[simp]
theorem bddBelow_empty [Nonempty α] : BddBelow (∅ : Set α) := by
  simp only [BddBelow, lowerBounds_empty, univ_nonempty]

@[simp] theorem isGLB_empty_iff : IsGLB ∅ a ↔ IsTop a := by
  simp [IsGLB]

@[simp] theorem isLUB_empty_iff : IsLUB ∅ a ↔ IsBot a :=
  @isGLB_empty_iff αᵒᵈ _ _

theorem isGLB_empty [OrderTop α] : IsGLB ∅ (⊤ : α) :=
  isGLB_empty_iff.2 isTop_top

theorem isLUB_empty [OrderBot α] : IsLUB ∅ (⊥ : α) :=
  @isGLB_empty αᵒᵈ _ _

theorem IsLUB.nonempty [NoMinOrder α] (hs : IsLUB s a) : s.Nonempty :=
  let ⟨a', ha'⟩ := exists_lt a
  nonempty_iff_ne_empty.2 fun h =>
    not_le_of_lt ha' <| hs.right <| by rw [h, upperBounds_empty]; exact mem_univ _

theorem IsGLB.nonempty [NoMaxOrder α] (hs : IsGLB s a) : s.Nonempty :=
  hs.dual.nonempty

theorem nonempty_of_not_bddAbove [ha : Nonempty α] (h : ¬BddAbove s) : s.Nonempty :=
  (Nonempty.elim ha) fun x => (not_bddAbove_iff'.1 h x).imp fun _ ha => ha.1

theorem nonempty_of_not_bddBelow [Nonempty α] (h : ¬BddBelow s) : s.Nonempty :=
  @nonempty_of_not_bddAbove αᵒᵈ _ _ _ h

/-!
#### insert
-/


/-- Adding a point to a set preserves its boundedness above. -/
@[simp]
theorem bddAbove_insert [IsDirected α (· ≤ ·)] {s : Set α} {a : α} :
    BddAbove (insert a s) ↔ BddAbove s := by
  simp only [insert_eq, bddAbove_union, bddAbove_singleton, true_and_iff]

protected theorem BddAbove.insert [IsDirected α (· ≤ ·)] {s : Set α} (a : α) :
    BddAbove s → BddAbove (insert a s) :=
  bddAbove_insert.2

/-- Adding a point to a set preserves its boundedness below. -/
@[simp]
theorem bddBelow_insert [IsDirected α (· ≥ ·)] {s : Set α} {a : α} :
    BddBelow (insert a s) ↔ BddBelow s := by
  simp only [insert_eq, bddBelow_union, bddBelow_singleton, true_and_iff]

protected theorem BddBelow.insert [IsDirected α (· ≥ ·)] {s : Set α} (a : α) :
    BddBelow s → BddBelow (insert a s) :=
  bddBelow_insert.2

protected theorem IsLUB.insert [SemilatticeSup γ] (a) {b} {s : Set γ} (hs : IsLUB s b) :
    IsLUB (insert a s) (a ⊔ b) := by
  rw [insert_eq]
  exact isLUB_singleton.union hs

protected theorem IsGLB.insert [SemilatticeInf γ] (a) {b} {s : Set γ} (hs : IsGLB s b) :
    IsGLB (insert a s) (a ⊓ b) := by
  rw [insert_eq]
  exact isGLB_singleton.union hs

protected theorem IsGreatest.insert [LinearOrder γ] (a) {b} {s : Set γ} (hs : IsGreatest s b) :
    IsGreatest (insert a s) (max a b) := by
  rw [insert_eq]
  exact isGreatest_singleton.union hs

protected theorem IsLeast.insert [LinearOrder γ] (a) {b} {s : Set γ} (hs : IsLeast s b) :
    IsLeast (insert a s) (min a b) := by
  rw [insert_eq]
  exact isLeast_singleton.union hs

@[simp]
theorem upperBounds_insert (a : α) (s : Set α) :
    upperBounds (insert a s) = Ici a ∩ upperBounds s := by
  rw [insert_eq, upperBounds_union, upperBounds_singleton]

@[simp]
theorem lowerBounds_insert (a : α) (s : Set α) :
    lowerBounds (insert a s) = Iic a ∩ lowerBounds s := by
  rw [insert_eq, lowerBounds_union, lowerBounds_singleton]

/-- When there is a global maximum, every set is bounded above. -/
@[simp]
protected theorem OrderTop.bddAbove [OrderTop α] (s : Set α) : BddAbove s :=
  ⟨⊤, fun a _ => OrderTop.le_top a⟩

/-- When there is a global minimum, every set is bounded below. -/
@[simp]
protected theorem OrderBot.bddBelow [OrderBot α] (s : Set α) : BddBelow s :=
  ⟨⊥, fun a _ => OrderBot.bot_le a⟩

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

theorem isGLB_pair [SemilatticeInf γ] {a b : γ} : IsGLB {a, b} (a ⊓ b) :=
  isGLB_singleton.insert _

theorem isLeast_pair [LinearOrder γ] {a b : γ} : IsLeast {a, b} (min a b) :=
  isLeast_singleton.insert _

theorem isGreatest_pair [LinearOrder γ] {a b : γ} : IsGreatest {a, b} (max a b) :=
  isGreatest_singleton.insert _

/-!
#### Lower/upper bounds
-/


@[simp]
theorem isLUB_lowerBounds : IsLUB (lowerBounds s) a ↔ IsGLB s a :=
  ⟨fun H => ⟨fun _ hx => H.2 <| subset_upperBounds_lowerBounds s hx, H.1⟩, IsGreatest.isLUB⟩

@[simp]
theorem isGLB_upperBounds : IsGLB (upperBounds s) a ↔ IsLUB s a :=
  @isLUB_lowerBounds αᵒᵈ _ _ _

end

/-!
### (In)equalities with the least upper bound and the greatest lower bound
-/


section Preorder

variable [Preorder α] {s : Set α} {a b : α}

theorem lowerBounds_le_upperBounds (ha : a ∈ lowerBounds s) (hb : b ∈ upperBounds s) :
    s.Nonempty → a ≤ b
  | ⟨_, hc⟩ => le_trans (ha hc) (hb hc)

theorem isGLB_le_isLUB (ha : IsGLB s a) (hb : IsLUB s b) (hs : s.Nonempty) : a ≤ b :=
  lowerBounds_le_upperBounds ha.1 hb.1 hs

theorem isLUB_lt_iff (ha : IsLUB s a) : a < b ↔ ∃ c ∈ upperBounds s, c < b :=
  ⟨fun hb => ⟨a, ha.1, hb⟩, fun ⟨_, hcs, hcb⟩ => lt_of_le_of_lt (ha.2 hcs) hcb⟩

theorem lt_isGLB_iff (ha : IsGLB s a) : b < a ↔ ∃ c ∈ lowerBounds s, b < c :=
  isLUB_lt_iff ha.dual

theorem le_of_isLUB_le_isGLB {x y} (ha : IsGLB s a) (hb : IsLUB s b) (hab : b ≤ a) (hx : x ∈ s)
    (hy : y ∈ s) : x ≤ y :=
  calc
    x ≤ b := hb.1 hx
    _ ≤ a := hab
    _ ≤ y := ha.1 hy

end Preorder

section PartialOrder

variable [PartialOrder α] {s : Set α} {a b : α}

theorem IsLeast.unique (Ha : IsLeast s a) (Hb : IsLeast s b) : a = b :=
  le_antisymm (Ha.right Hb.left) (Hb.right Ha.left)

theorem IsLeast.isLeast_iff_eq (Ha : IsLeast s a) : IsLeast s b ↔ a = b :=
  Iff.intro Ha.unique fun h => h ▸ Ha

theorem IsGreatest.unique (Ha : IsGreatest s a) (Hb : IsGreatest s b) : a = b :=
  le_antisymm (Hb.right Ha.left) (Ha.right Hb.left)

theorem IsGreatest.isGreatest_iff_eq (Ha : IsGreatest s a) : IsGreatest s b ↔ a = b :=
  Iff.intro Ha.unique fun h => h ▸ Ha

theorem IsLUB.unique (Ha : IsLUB s a) (Hb : IsLUB s b) : a = b :=
  IsLeast.unique Ha Hb

theorem IsGLB.unique (Ha : IsGLB s a) (Hb : IsGLB s b) : a = b :=
  IsGreatest.unique Ha Hb

theorem Set.subsingleton_of_isLUB_le_isGLB (Ha : IsGLB s a) (Hb : IsLUB s b) (hab : b ≤ a) :
    s.Subsingleton := fun _ hx _ hy =>
  le_antisymm (le_of_isLUB_le_isGLB Ha Hb hab hx hy) (le_of_isLUB_le_isGLB Ha Hb hab hy hx)

theorem isGLB_lt_isLUB_of_ne (Ha : IsGLB s a) (Hb : IsLUB s b) {x y} (Hx : x ∈ s) (Hy : y ∈ s)
    (Hxy : x ≠ y) : a < b :=
  lt_iff_le_not_le.2
    ⟨lowerBounds_le_upperBounds Ha.1 Hb.1 ⟨x, Hx⟩, fun hab =>
      Hxy <| Set.subsingleton_of_isLUB_le_isGLB Ha Hb hab Hx Hy⟩

end PartialOrder

section LinearOrder

variable [LinearOrder α] {s : Set α} {a b : α}

theorem lt_isLUB_iff (h : IsLUB s a) : b < a ↔ ∃ c ∈ s, b < c := by
  simp_rw [← not_le, isLUB_le_iff h, mem_upperBounds, not_forall, not_le, exists_prop]

theorem isGLB_lt_iff (h : IsGLB s a) : a < b ↔ ∃ c ∈ s, c < b :=
  lt_isLUB_iff h.dual

theorem IsLUB.exists_between (h : IsLUB s a) (hb : b < a) : ∃ c ∈ s, b < c ∧ c ≤ a :=
  let ⟨c, hcs, hbc⟩ := (lt_isLUB_iff h).1 hb
  ⟨c, hcs, hbc, h.1 hcs⟩

theorem IsLUB.exists_between' (h : IsLUB s a) (h' : a ∉ s) (hb : b < a) : ∃ c ∈ s, b < c ∧ c < a :=
  let ⟨c, hcs, hbc, hca⟩ := h.exists_between hb
  ⟨c, hcs, hbc, hca.lt_of_ne fun hac => h' <| hac ▸ hcs⟩

theorem IsGLB.exists_between (h : IsGLB s a) (hb : a < b) : ∃ c ∈ s, a ≤ c ∧ c < b :=
  let ⟨c, hcs, hbc⟩ := (isGLB_lt_iff h).1 hb
  ⟨c, hcs, h.1 hcs, hbc⟩

theorem IsGLB.exists_between' (h : IsGLB s a) (h' : a ∉ s) (hb : a < b) : ∃ c ∈ s, a < c ∧ c < b :=
  let ⟨c, hcs, hac, hcb⟩ := h.exists_between hb
  ⟨c, hcs, hac.lt_of_ne fun hac => h' <| hac.symm ▸ hcs, hcb⟩

end LinearOrder

/-!
### Images of upper/lower bounds under monotone functions
-/


namespace MonotoneOn

variable [Preorder α] [Preorder β] {f : α → β} {s t : Set α} {a : α}

theorem mem_upperBounds_image (Hf : MonotoneOn f t) (Hst : s ⊆ t) (Has : a ∈ upperBounds s)
    (Hat : a ∈ t) : f a ∈ upperBounds (f '' s) :=
  forall_mem_image.2 fun _ H => Hf (Hst H) Hat (Has H)

theorem mem_upperBounds_image_self (Hf : MonotoneOn f t) :
    a ∈ upperBounds t → a ∈ t → f a ∈ upperBounds (f '' t) :=
  Hf.mem_upperBounds_image subset_rfl

theorem mem_lowerBounds_image (Hf : MonotoneOn f t) (Hst : s ⊆ t) (Has : a ∈ lowerBounds s)
    (Hat : a ∈ t) : f a ∈ lowerBounds (f '' s) :=
  forall_mem_image.2 fun _ H => Hf Hat (Hst H) (Has H)

theorem mem_lowerBounds_image_self (Hf : MonotoneOn f t) :
    a ∈ lowerBounds t → a ∈ t → f a ∈ lowerBounds (f '' t) :=
  Hf.mem_lowerBounds_image subset_rfl

theorem image_upperBounds_subset_upperBounds_image (Hf : MonotoneOn f t) (Hst : s ⊆ t) :
    f '' (upperBounds s ∩ t) ⊆ upperBounds (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩
  exact Hf.mem_upperBounds_image Hst ha.1 ha.2

theorem image_lowerBounds_subset_lowerBounds_image (Hf : MonotoneOn f t) (Hst : s ⊆ t) :
    f '' (lowerBounds s ∩ t) ⊆ lowerBounds (f '' s) :=
  Hf.dual.image_upperBounds_subset_upperBounds_image Hst

/-- The image under a monotone function on a set `t` of a subset which has an upper bound in `t`
  is bounded above. -/
theorem map_bddAbove (Hf : MonotoneOn f t) (Hst : s ⊆ t) :
    (upperBounds s ∩ t).Nonempty → BddAbove (f '' s) := fun ⟨C, hs, ht⟩ =>
  ⟨f C, Hf.mem_upperBounds_image Hst hs ht⟩

/-- The image under a monotone function on a set `t` of a subset which has a lower bound in `t`
  is bounded below. -/
theorem map_bddBelow (Hf : MonotoneOn f t) (Hst : s ⊆ t) :
    (lowerBounds s ∩ t).Nonempty → BddBelow (f '' s) := fun ⟨C, hs, ht⟩ =>
  ⟨f C, Hf.mem_lowerBounds_image Hst hs ht⟩

/-- A monotone map sends a least element of a set to a least element of its image. -/
theorem map_isLeast (Hf : MonotoneOn f t) (Ha : IsLeast t a) : IsLeast (f '' t) (f a) :=
  ⟨mem_image_of_mem _ Ha.1, Hf.mem_lowerBounds_image_self Ha.2 Ha.1⟩

/-- A monotone map sends a greatest element of a set to a greatest element of its image. -/
theorem map_isGreatest (Hf : MonotoneOn f t) (Ha : IsGreatest t a) : IsGreatest (f '' t) (f a) :=
  ⟨mem_image_of_mem _ Ha.1, Hf.mem_upperBounds_image_self Ha.2 Ha.1⟩

end MonotoneOn

namespace AntitoneOn

variable [Preorder α] [Preorder β] {f : α → β} {s t : Set α} {a : α}

theorem mem_upperBounds_image (Hf : AntitoneOn f t) (Hst : s ⊆ t) (Has : a ∈ lowerBounds s) :
    a ∈ t → f a ∈ upperBounds (f '' s) :=
  Hf.dual_right.mem_lowerBounds_image Hst Has

theorem mem_upperBounds_image_self (Hf : AntitoneOn f t) :
    a ∈ lowerBounds t → a ∈ t → f a ∈ upperBounds (f '' t) :=
  Hf.dual_right.mem_lowerBounds_image_self

theorem mem_lowerBounds_image (Hf : AntitoneOn f t) (Hst : s ⊆ t) :
    a ∈ upperBounds s → a ∈ t → f a ∈ lowerBounds (f '' s) :=
  Hf.dual_right.mem_upperBounds_image Hst

theorem mem_lowerBounds_image_self (Hf : AntitoneOn f t) :
    a ∈ upperBounds t → a ∈ t → f a ∈ lowerBounds (f '' t) :=
  Hf.dual_right.mem_upperBounds_image_self

theorem image_lowerBounds_subset_upperBounds_image (Hf : AntitoneOn f t) (Hst : s ⊆ t) :
    f '' (lowerBounds s ∩ t) ⊆ upperBounds (f '' s) :=
  Hf.dual_right.image_lowerBounds_subset_lowerBounds_image Hst

theorem image_upperBounds_subset_lowerBounds_image (Hf : AntitoneOn f t) (Hst : s ⊆ t) :
    f '' (upperBounds s ∩ t) ⊆ lowerBounds (f '' s) :=
  Hf.dual_right.image_upperBounds_subset_upperBounds_image Hst

/-- The image under an antitone function of a set which is bounded above is bounded below. -/
theorem map_bddAbove (Hf : AntitoneOn f t) (Hst : s ⊆ t) :
    (upperBounds s ∩ t).Nonempty → BddBelow (f '' s) :=
  Hf.dual_right.map_bddAbove Hst

/-- The image under an antitone function of a set which is bounded below is bounded above. -/
theorem map_bddBelow (Hf : AntitoneOn f t) (Hst : s ⊆ t) :
    (lowerBounds s ∩ t).Nonempty → BddAbove (f '' s) :=
  Hf.dual_right.map_bddBelow Hst

/-- An antitone map sends a greatest element of a set to a least element of its image. -/
theorem map_isGreatest (Hf : AntitoneOn f t) : IsGreatest t a → IsLeast (f '' t) (f a) :=
  Hf.dual_right.map_isGreatest

/-- An antitone map sends a least element of a set to a greatest element of its image. -/
theorem map_isLeast (Hf : AntitoneOn f t) : IsLeast t a → IsGreatest (f '' t) (f a) :=
  Hf.dual_right.map_isLeast

end AntitoneOn

namespace Monotone

variable [Preorder α] [Preorder β] {f : α → β} (Hf : Monotone f) {a : α} {s : Set α}

include Hf

theorem mem_upperBounds_image (Ha : a ∈ upperBounds s) : f a ∈ upperBounds (f '' s) :=
  forall_mem_image.2 fun _ H => Hf (Ha H)

theorem mem_lowerBounds_image (Ha : a ∈ lowerBounds s) : f a ∈ lowerBounds (f '' s) :=
  forall_mem_image.2 fun _ H => Hf (Ha H)

theorem image_upperBounds_subset_upperBounds_image :
    f '' upperBounds s ⊆ upperBounds (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩
  exact Hf.mem_upperBounds_image ha

theorem image_lowerBounds_subset_lowerBounds_image : f '' lowerBounds s ⊆ lowerBounds (f '' s) :=
  Hf.dual.image_upperBounds_subset_upperBounds_image

/-- The image under a monotone function of a set which is bounded above is bounded above. See also
`BddAbove.image2`. -/
theorem map_bddAbove : BddAbove s → BddAbove (f '' s)
  | ⟨C, hC⟩ => ⟨f C, Hf.mem_upperBounds_image hC⟩

/-- The image under a monotone function of a set which is bounded below is bounded below. See also
`BddBelow.image2`. -/
theorem map_bddBelow : BddBelow s → BddBelow (f '' s)
  | ⟨C, hC⟩ => ⟨f C, Hf.mem_lowerBounds_image hC⟩

/-- A monotone map sends a least element of a set to a least element of its image. -/
theorem map_isLeast (Ha : IsLeast s a) : IsLeast (f '' s) (f a) :=
  ⟨mem_image_of_mem _ Ha.1, Hf.mem_lowerBounds_image Ha.2⟩

/-- A monotone map sends a greatest element of a set to a greatest element of its image. -/
theorem map_isGreatest (Ha : IsGreatest s a) : IsGreatest (f '' s) (f a) :=
  ⟨mem_image_of_mem _ Ha.1, Hf.mem_upperBounds_image Ha.2⟩

end Monotone

namespace Antitone

variable [Preorder α] [Preorder β] {f : α → β} (hf : Antitone f) {a : α} {s : Set α}

include hf

theorem mem_upperBounds_image : a ∈ lowerBounds s → f a ∈ upperBounds (f '' s) :=
  hf.dual_right.mem_lowerBounds_image

theorem mem_lowerBounds_image : a ∈ upperBounds s → f a ∈ lowerBounds (f '' s) :=
  hf.dual_right.mem_upperBounds_image

theorem image_lowerBounds_subset_upperBounds_image : f '' lowerBounds s ⊆ upperBounds (f '' s) :=
  hf.dual_right.image_lowerBounds_subset_lowerBounds_image

theorem image_upperBounds_subset_lowerBounds_image : f '' upperBounds s ⊆ lowerBounds (f '' s) :=
  hf.dual_right.image_upperBounds_subset_upperBounds_image

/-- The image under an antitone function of a set which is bounded above is bounded below. -/
theorem map_bddAbove : BddAbove s → BddBelow (f '' s) :=
  hf.dual_right.map_bddAbove

/-- The image under an antitone function of a set which is bounded below is bounded above. -/
theorem map_bddBelow : BddBelow s → BddAbove (f '' s) :=
  hf.dual_right.map_bddBelow

/-- An antitone map sends a greatest element of a set to a least element of its image. -/
theorem map_isGreatest : IsGreatest s a → IsLeast (f '' s) (f a) :=
  hf.dual_right.map_isGreatest

/-- An antitone map sends a least element of a set to a greatest element of its image. -/
theorem map_isLeast : IsLeast s a → IsGreatest (f '' s) (f a) :=
  hf.dual_right.map_isLeast

end Antitone

section Image2

variable [Preorder α] [Preorder β] [Preorder γ] {f : α → β → γ} {s : Set α} {t : Set β} {a : α}
  {b : β}

section MonotoneMonotone

variable (h₀ : ∀ b, Monotone (swap f b)) (h₁ : ∀ a, Monotone (f a))

include h₀ h₁

theorem mem_upperBounds_image2 (ha : a ∈ upperBounds s) (hb : b ∈ upperBounds t) :
    f a b ∈ upperBounds (image2 f s t) :=
  forall_image2_iff.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

theorem mem_lowerBounds_image2 (ha : a ∈ lowerBounds s) (hb : b ∈ lowerBounds t) :
    f a b ∈ lowerBounds (image2 f s t) :=
  forall_image2_iff.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

theorem image2_upperBounds_upperBounds_subset :
    image2 f (upperBounds s) (upperBounds t) ⊆ upperBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦ mem_upperBounds_image2 h₀ h₁ ha hb

theorem image2_lowerBounds_lowerBounds_subset :
    image2 f (lowerBounds s) (lowerBounds t) ⊆ lowerBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦ mem_lowerBounds_image2 h₀ h₁ ha hb

/-- See also `Monotone.map_bddAbove`. -/
protected theorem BddAbove.image2 :
    BddAbove s → BddAbove t → BddAbove (image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2 h₀ h₁ ha hb⟩

/-- See also `Monotone.map_bddBelow`. -/
protected theorem BddBelow.image2 :
    BddBelow s → BddBelow t → BddBelow (image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_lowerBounds_image2 h₀ h₁ ha hb⟩

protected theorem IsGreatest.image2 (ha : IsGreatest s a) (hb : IsGreatest t b) :
    IsGreatest (image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_upperBounds_image2 h₀ h₁ ha.2 hb.2⟩

protected theorem IsLeast.image2 (ha : IsLeast s a) (hb : IsLeast t b) :
    IsLeast (image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_lowerBounds_image2 h₀ h₁ ha.2 hb.2⟩

end MonotoneMonotone

section MonotoneAntitone

variable (h₀ : ∀ b, Monotone (swap f b)) (h₁ : ∀ a, Antitone (f a))

include h₀ h₁

theorem mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds (ha : a ∈ upperBounds s)
    (hb : b ∈ lowerBounds t) : f a b ∈ upperBounds (image2 f s t) :=
  forall_image2_iff.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

theorem mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_upperBounds (ha : a ∈ lowerBounds s)
    (hb : b ∈ upperBounds t) : f a b ∈ lowerBounds (image2 f s t) :=
  forall_image2_iff.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

theorem image2_upperBounds_lowerBounds_subset_upperBounds_image2 :
    image2 f (upperBounds s) (lowerBounds t) ⊆ upperBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds h₀ h₁ ha hb

theorem image2_lowerBounds_upperBounds_subset_lowerBounds_image2 :
    image2 f (lowerBounds s) (upperBounds t) ⊆ lowerBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦
    mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_upperBounds h₀ h₁ ha hb

theorem BddAbove.bddAbove_image2_of_bddBelow :
    BddAbove s → BddBelow t → BddAbove (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds h₀ h₁ ha hb⟩

theorem BddBelow.bddBelow_image2_of_bddAbove :
    BddBelow s → BddAbove t → BddBelow (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_upperBounds h₀ h₁ ha hb⟩

theorem IsGreatest.isGreatest_image2_of_isLeast (ha : IsGreatest s a) (hb : IsLeast t b) :
    IsGreatest (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1,
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds h₀ h₁ ha.2 hb.2⟩

theorem IsLeast.isLeast_image2_of_isGreatest (ha : IsLeast s a) (hb : IsGreatest t b) :
    IsLeast (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1,
    mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_upperBounds h₀ h₁ ha.2 hb.2⟩

end MonotoneAntitone

section AntitoneAntitone

variable (h₀ : ∀ b, Antitone (swap f b)) (h₁ : ∀ a, Antitone (f a))

include h₀ h₁

theorem mem_upperBounds_image2_of_mem_lowerBounds (ha : a ∈ lowerBounds s)
    (hb : b ∈ lowerBounds t) : f a b ∈ upperBounds (image2 f s t) :=
  forall_image2_iff.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

theorem mem_lowerBounds_image2_of_mem_upperBounds (ha : a ∈ upperBounds s)
    (hb : b ∈ upperBounds t) : f a b ∈ lowerBounds (image2 f s t) :=
  forall_image2_iff.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

theorem image2_upperBounds_upperBounds_subset_upperBounds_image2 :
    image2 f (lowerBounds s) (lowerBounds t) ⊆ upperBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦
    mem_upperBounds_image2_of_mem_lowerBounds h₀ h₁ ha hb

theorem image2_lowerBounds_lowerBounds_subset_lowerBounds_image2 :
    image2 f (upperBounds s) (upperBounds t) ⊆ lowerBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦
    mem_lowerBounds_image2_of_mem_upperBounds h₀ h₁ ha hb

theorem BddBelow.image2_bddAbove : BddBelow s → BddBelow t → BddAbove (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2_of_mem_lowerBounds h₀ h₁ ha hb⟩

theorem BddAbove.image2_bddBelow : BddAbove s → BddAbove t → BddBelow (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_lowerBounds_image2_of_mem_upperBounds h₀ h₁ ha hb⟩

theorem IsLeast.isGreatest_image2 (ha : IsLeast s a) (hb : IsLeast t b) :
    IsGreatest (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_upperBounds_image2_of_mem_lowerBounds h₀ h₁ ha.2 hb.2⟩

theorem IsGreatest.isLeast_image2 (ha : IsGreatest s a) (hb : IsGreatest t b) :
    IsLeast (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_lowerBounds_image2_of_mem_upperBounds h₀ h₁ ha.2 hb.2⟩

end AntitoneAntitone

section AntitoneMonotone

variable (h₀ : ∀ b, Antitone (swap f b)) (h₁ : ∀ a, Monotone (f a))

include h₀ h₁

theorem mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds (ha : a ∈ lowerBounds s)
    (hb : b ∈ upperBounds t) : f a b ∈ upperBounds (image2 f s t) :=
  forall_image2_iff.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

theorem mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_lowerBounds (ha : a ∈ upperBounds s)
    (hb : b ∈ lowerBounds t) : f a b ∈ lowerBounds (image2 f s t) :=
  forall_image2_iff.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

theorem image2_lowerBounds_upperBounds_subset_upperBounds_image2 :
    image2 f (lowerBounds s) (upperBounds t) ⊆ upperBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds h₀ h₁ ha hb

theorem image2_upperBounds_lowerBounds_subset_lowerBounds_image2 :
    image2 f (upperBounds s) (lowerBounds t) ⊆ lowerBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦
    mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_lowerBounds h₀ h₁ ha hb

theorem BddBelow.bddAbove_image2_of_bddAbove :
    BddBelow s → BddAbove t → BddAbove (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds h₀ h₁ ha hb⟩

theorem BddAbove.bddBelow_image2_of_bddAbove :
    BddAbove s → BddBelow t → BddBelow (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_lowerBounds h₀ h₁ ha hb⟩

theorem IsLeast.isGreatest_image2_of_isGreatest (ha : IsLeast s a) (hb : IsGreatest t b) :
    IsGreatest (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1,
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds h₀ h₁ ha.2 hb.2⟩

theorem IsGreatest.isLeast_image2_of_isLeast (ha : IsGreatest s a) (hb : IsLeast t b) :
    IsLeast (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1,
    mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_lowerBounds h₀ h₁ ha.2 hb.2⟩

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

theorem isGLB_prod {s : Set (α × β)} (p : α × β) :
    IsGLB s p ↔ IsGLB (Prod.fst '' s) p.1 ∧ IsGLB (Prod.snd '' s) p.2 :=
  @isLUB_prod αᵒᵈ βᵒᵈ _ _ _ _

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

theorem isGLB_pi {s : Set (∀ a, π a)} {f : ∀ a, π a} :
    IsGLB s f ↔ ∀ a, IsGLB (Function.eval a '' s) (f a) :=
  @isLUB_pi α (fun a => (π a)ᵒᵈ) _ s f

end Pi

theorem IsGLB.of_image [Preorder α] [Preorder β] {f : α → β} (hf : ∀ {x y}, f x ≤ f y ↔ x ≤ y)
    {s : Set α} {x : α} (hx : IsGLB (f '' s) (f x)) : IsGLB s x :=
  ⟨fun _ hy => hf.1 <| hx.1 <| mem_image_of_mem _ hy, fun _ hy =>
    hf.1 <| hx.2 <| Monotone.mem_lowerBounds_image (fun _ _ => hf.2) hy⟩

theorem IsLUB.of_image [Preorder α] [Preorder β] {f : α → β} (hf : ∀ {x y}, f x ≤ f y ↔ x ≤ y)
    {s : Set α} {x : α} (hx : IsLUB (f '' s) (f x)) : IsLUB s x :=
  ⟨fun _ hy => hf.1 <| hx.1 <| mem_image_of_mem _ hy, fun _ hy =>
    hf.1 <| hx.2 <| Monotone.mem_upperBounds_image (fun _ _ => hf.2) hy⟩

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

protected theorem ScottContinuous.monotone (h : ScottContinuous f) : Monotone f := by
  refine fun a b hab =>
    (h (insert_nonempty _ _) (directedOn_pair le_refl hab) ?_).1
      (mem_image_of_mem _ <| mem_insert _ _)
  rw [IsLUB, upperBounds_insert, upperBounds_singleton,
    inter_eq_self_of_subset_right (Ici_subset_Ici.2 hab)]
  exact isLeast_Ici

end ScottContinuous
