/-
Copyright (c) 2024 Ira Fesefeldt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ira Fesefeldt
-/
module

public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Order.CompletePartialOrder

/-!
# Ordinal Approximants for the Fixed points on complete lattices

This file sets up the ordinal-indexed approximation theory of fixed points
of a monotone function in a complete lattice [Cousot1979].
The proof follows loosely the one from [Echenique2005].

However, the proof given here is not constructive as we use the non-constructive axiomatization of
ordinals from mathlib. It still allows an approximation scheme indexed over the ordinals.

## Main definitions

* `OrdinalApprox.lfpApprox`: The ordinal-indexed approximation of the least fixed point
  greater or equal than an initial value of a bundled monotone function.
* `OrdinalApprox.gfpApprox`: The ordinal-indexed approximation of the greatest fixed point
  less or equal than an initial value of a bundled monotone function.

## Main theorems
* `OrdinalApprox.lfp_mem_range_lfpApprox`: The ordinal-indexed approximation of
  the least fixed point eventually reaches the least fixed point
* `OrdinalApprox.gfp_mem_range_gfpApprox`: The ordinal-indexed approximation of
  the greatest fixed point eventually reaches the greatest fixed point

## References
* [F. Echenique, *A short and constructive proof of Tarski’s fixed-point theorem*][Echenique2005]
* [P. Cousot & R. Cousot, *Constructive Versions of Tarski's Fixed Point Theorems*][Cousot1979]

## Tags

fixed point, complete lattice, monotone function, ordinals, approximation
-/

@[expose] public section

namespace Cardinal

universe u
variable {α : Type u}
variable (g : Ordinal → α)

open Cardinal Ordinal SuccOrder Function Set

theorem not_injective_limitation_set : ¬ InjOn g (Iio (ord <| succ #α)) := by
  intro h_inj
  have h := lift_mk_le_lift_mk_of_injective <| injOn_iff_injective.1 h_inj
  have mk_initialSeg_subtype :
      #(Iio (ord <| succ #α)) = lift.{u + 1} (succ #α) := by
    simpa only [coe_setOf, card_typein, card_ord] using mk_Iio_ordinal (ord <| succ #α)
  rw [mk_initialSeg_subtype, lift_lift, lift_le] at h
  exact not_le_of_gt (Order.lt_succ #α) h

end Cardinal

namespace OrdinalApprox

universe u
variable {α : Type u}
variable [CompletePartialOrder α] (f : α →o α) (x : α)

set_option linter.unusedVariables false in
/-- The ordinal-indexed sequence approximating the least fixed point greater than
an initial value `x`. It is defined in such a way that we have `lfpApprox 0 x = x` and
`lfpApprox a x = ⨆ b < a, f (lfpApprox b x)`. -/
def lfpApprox (a : Ordinal.{u}) : α :=
  sSup ({ f (lfpApprox b) | (b : Ordinal) (h : b < a) } ∪ {x})
termination_by a
decreasing_by exact h

variable {β : Type u}
variable [CompleteLattice β] (g : β →o β) (y : β)

set_option linter.unusedVariables false in
/-- The ordinal-indexed sequence approximating the greatest fixed point greater than
an initial value `x`. It is defined in such a way that we have `gfpApprox 0 x = x` and
`gfpApprox a x = ⨅ b < a, f (lfpApprox b x)`. -/
def gfpApprox (a : Ordinal.{u}) : β :=
  sInf ({ g (gfpApprox b) | (b : Ordinal) (h : b < a) } ∪ {y})
termination_by a
decreasing_by exact h

open Function fixedPoints Cardinal Order OrderHom



theorem directedOn_lfpApprox (a : Ordinal.{u}) (h : x ≤ f x) :
    DirectedOn (· ≤ ·) ({ f (lfpApprox f x b) | (b : Ordinal) (h : b < a) } ∪ {x}) := by
  induction a using Ordinal.induction with
  | h i ih =>
    rintro z (⟨b, h_b, h_z⟩ | h_z) y (⟨c, h_c, h_y⟩ | h_y)
    · cases le_total b c
      case inl h_bc =>
        use y
        apply And.intro (by left; use c)
        apply And.intro ?_ (by rfl)
        rw [← h_z, ← h_y]
        apply f.mono
        unfold lfpApprox
        apply DirectedOn.sSup_le_sSup (ih b h_b) (ih c h_c)
        grind only [= Set.subset_def, = Set.setOf_true, = Set.mem_union, usr Set.mem_setOf_eq]
      case inr h_cb =>
        use z
        apply And.intro (by left; use b)
        apply And.intro (by rfl)
        simp only
        rw [← h_z, ← h_y]
        apply f.mono
        unfold lfpApprox
        apply DirectedOn.sSup_le_sSup (ih c h_c) (ih b h_b)
        grind only [= Set.subset_def, = Set.setOf_true, = Set.mem_union, usr Set.mem_setOf_eq]
    · use z
      apply And.intro (by left; use b)
      apply And.intro (by rfl)
      simp only
      rw [← h_z, h_y]
      apply le_trans h
      apply f.mono
      unfold lfpApprox
      apply (ih b h_b).le_sSup
      right
      rfl
    · use y
      apply And.intro (by left; use c)
      apply And.intro ?_ (by rfl)
      simp only
      rw [← h_y, h_z]
      apply le_trans h
      apply f.mono
      unfold lfpApprox
      apply (ih c h_c).le_sSup
      right
      rfl
    · use x
      apply And.intro
      · right
        rfl
      · rw [h_z, h_y]
        trivial

theorem lfpApprox_monotone_of_le (h_f : x ≤ f x) : Monotone (lfpApprox f x) := by
  intro a b h
  rw [lfpApprox, lfpApprox]
  apply DirectedOn.sSup_le_sSup (directedOn_lfpApprox _ _ _ h_f) (directedOn_lfpApprox _ _ _ h_f)
  apply Set.union_subset_union ?_ (by rfl)
  simp only [exists_prop, Set.setOf_subset_setOf, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  intro a' h'
  use a'
  exact ⟨lt_of_lt_of_le h' h, rfl⟩

theorem le_lfpApprox_of_le {a : Ordinal} (h_f : x ≤ f x) : x ≤ lfpApprox f x a := by
  rw [lfpApprox]
  apply (directedOn_lfpApprox _ _ _ h_f).le_sSup
  simp only [exists_prop, Set.union_singleton, Set.mem_insert_iff, Set.mem_setOf_eq, true_or]

theorem lfpApprox_add_one_of_le (h : x ≤ f x) (a : Ordinal) :
    lfpApprox f x (a + 1) = f (lfpApprox f x a) := by
  apply le_antisymm
  · conv => left; rw [lfpApprox]
    apply (directedOn_lfpApprox _ _ _ h).sSup_le
    simp only [Ordinal.add_one_eq_succ, lt_succ_iff, exists_prop, Set.union_singleton,
      Set.mem_insert_iff, Set.mem_setOf_eq, forall_eq_or_imp, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    apply And.intro
    · apply le_trans h
      apply Monotone.imp f.monotone
      exact le_lfpApprox_of_le f x h
    · intro a' h'
      apply f.2; apply lfpApprox_monotone_of_le f x h; exact h'
  · conv => right; rw [lfpApprox]
    apply (directedOn_lfpApprox _ _ _ h).le_sSup
    simp only [Ordinal.add_one_eq_succ, lt_succ_iff, exists_prop]
    rw [Set.mem_union]
    apply Or.inl
    simp only [Set.mem_setOf_eq]
    use a

theorem lfpApprox_mono_left_of_le (f g : α →o α) (h_f : x ≤ f x) (h_g : x ≤ g x) :
    f ≤ g → lfpApprox f x ≤ lfpApprox g x := by
  intro h a
  induction a using Ordinal.induction with
  | h i ih =>
    rw [lfpApprox, lfpApprox]
    apply (directedOn_lfpApprox _ _ _ h_f).sSup_le
    rintro y (⟨b, h_b, h_y⟩ | h_y)
    · rw [← h_y]
      apply (directedOn_lfpApprox _ _ _ h_g).le_sSup_of_le
      · left
        use b
      · exact le_trans (f.mono (ih b h_b)) (h _)
    · apply (directedOn_lfpApprox _ _ _ h_g).le_sSup
      right
      exact h_y

theorem lfpApprox_mono_mid_of_le {x₁ x₂ : α} (h_f₁ : x₁ ≤ f x₁) (h_f₂ : x₂ ≤ f x₂) :
    x₁ ≤ x₂ → lfpApprox f x₁ ≤ lfpApprox f x₂ := by
  intro h a
  induction a using Ordinal.induction with
  | h i ih =>
    rw [lfpApprox, lfpApprox]
    apply (directedOn_lfpApprox _ _ _ h_f₁).sSup_le
    rintro y (⟨a, h_a, h_y⟩ | h_y)
    · rw [← h_y]
      apply (directedOn_lfpApprox _ _ _ h_f₂).le_sSup_of_le
      · left
        use a
      · apply f.mono
        exact ih a h_a
    · apply (directedOn_lfpApprox _ _ _ h_f₂).le_sSup_of_le
      · right
        rfl
      · rw [h_y]
        exact h

/-- The approximations of the least fixed point stabilize at a fixed point of `f` -/
theorem lfpApprox_eq_of_mem_fixedPoints {a b : Ordinal} (h_init : x ≤ f x) (h_ab : a ≤ b)
    (h : lfpApprox f x a ∈ fixedPoints f) : lfpApprox f x b = lfpApprox f x a := by
  rw [mem_fixedPoints_iff] at h
  induction b using Ordinal.induction with | h b IH =>
  apply le_antisymm
  · conv => left; rw [lfpApprox]
    apply (directedOn_lfpApprox _ _ _ h_init).sSup_le
    simp only [exists_prop, Set.union_singleton, Set.mem_insert_iff, Set.mem_setOf_eq,
      forall_eq_or_imp, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    apply And.intro (le_lfpApprox_of_le f x h_init)
    intro a' ha'b
    by_cases! haa : a' < a
    · rw [← lfpApprox_add_one_of_le f x h_init]
      apply lfpApprox_monotone_of_le f x h_init
      simp only [Ordinal.add_one_eq_succ, succ_le_iff]
      exact haa
    · rw [IH a' ha'b haa, h]
  · exact lfpApprox_monotone_of_le f x h_init h_ab

/-- There are distinct indices smaller than the successor of the domain's cardinality
yielding the same value -/
theorem exists_lfpApprox_eq_lfpApprox : ∃ a < ord <| succ #α, ∃ b < ord <| succ #α,
    a ≠ b ∧ lfpApprox f x a = lfpApprox f x b := by
  have h_ninj := not_injective_limitation_set <| lfpApprox f x
  rw [Set.injOn_iff_injective, Function.not_injective_iff] at h_ninj
  let ⟨a, b, h_fab, h_nab⟩ := h_ninj
  use a.val; apply And.intro a.prop
  use b.val; apply And.intro b.prop
  apply And.intro
  · intro h_eq; rw [Subtype.coe_inj] at h_eq; exact h_nab h_eq
  · exact h_fab

/-- If the sequence of ordinal-indexed approximations takes a value twice,
then it actually stabilised at that value. -/
lemma lfpApprox_mem_fixedPoints_of_eq {a b c : Ordinal}
    (h_init : x ≤ f x) (h_ab : a < b) (h_ac : a ≤ c) (h_fab : lfpApprox f x a = lfpApprox f x b) :
    lfpApprox f x c ∈ fixedPoints f := by
  have lfpApprox_mem_fixedPoint :
      lfpApprox f x a ∈ fixedPoints f := by
    rw [mem_fixedPoints_iff, ← lfpApprox_add_one_of_le f x h_init]
    exact Monotone.eq_of_ge_of_le (lfpApprox_monotone_of_le f x h_init)
      h_fab (SuccOrder.le_succ a) (SuccOrder.succ_le_of_lt h_ab)
  rw [lfpApprox_eq_of_mem_fixedPoints f x h_init]
  · exact lfpApprox_mem_fixedPoint
  · exact h_ac
  · exact lfpApprox_mem_fixedPoint

/-- The approximation at the index of the successor of the domain's cardinality is a fixed point -/
theorem lfpApprox_ord_mem_fixedPoint (h_init : x ≤ f x) :
    lfpApprox f x (ord <| succ #α) ∈ fixedPoints f := by
  let ⟨a, h_a, b, h_b, h_nab, h_fab⟩ := exists_lfpApprox_eq_lfpApprox f x
  cases le_total a b with
  | inl h_ab =>
    exact lfpApprox_mem_fixedPoints_of_eq f x h_init
      (h_nab.lt_of_le h_ab) (le_of_lt h_a) h_fab
  | inr h_ba =>
    exact lfpApprox_mem_fixedPoints_of_eq f x h_init
      (h_nab.symm.lt_of_le h_ba) (le_of_lt h_b) (h_fab.symm)

/-- Every value of the approximation is less or equal than every fixed point of `f`
greater or equal than the initial value -/
theorem lfpApprox_le_of_mem_fixedPoints_of_le {a : α} (h_init : x ≤ f x)
    (h_a : a ∈ fixedPoints f) (h_le_init : x ≤ a) (i : Ordinal) : lfpApprox f x i ≤ a := by
  induction i using Ordinal.induction with
  | h i IH =>
    rw [lfpApprox]
    apply (directedOn_lfpApprox _ _ _ h_init).sSup_le
    simp only [exists_prop]
    intro y h_y
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff] at h_y
    cases h_y with
    | inl h_y =>
      let ⟨j, h_j_lt, h_j⟩ := h_y
      rw [← h_j, ← h_a]
      exact f.monotone' (IH j h_j_lt)
    | inr h_y =>
      rw [h_y]
      exact h_le_init

theorem lfpApprox_monotone : Monotone (lfpApprox g y) := by
  intro a b h
  rw [lfpApprox, lfpApprox]
  gcongr sSup (?_ ∪ {y})
  simp only [exists_prop, Set.setOf_subset_setOf, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  intro a' h'
  use a'
  exact ⟨lt_of_lt_of_le h' h, rfl⟩

theorem le_lfpApprox {a : Ordinal} : y ≤ lfpApprox g y a := by
  rw [lfpApprox]
  apply le_sSup
  simp only [exists_prop, Set.union_singleton, Set.mem_insert_iff, Set.mem_setOf_eq, true_or]

theorem lfpApprox_mono_left : Monotone (lfpApprox : (β →o β) → _) := by
  intro f g h x a
  induction a using Ordinal.induction with
  | h i ih =>
    rw [lfpApprox, lfpApprox]
    apply sSup_le
    simp only [exists_prop, Set.union_singleton, Set.mem_insert_iff, Set.mem_setOf_eq, sSup_insert,
      forall_eq_or_imp, le_sup_left, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      true_and]
    intro i' h_lt
    apply le_sup_of_le_right
    apply le_sSup_of_le
    · use i'
    · apply le_trans (h _)
      simp only [OrderHom.toFun_eq_coe]
      exact g.monotone (ih i' h_lt)

theorem lfpApprox_mono_mid : Monotone (lfpApprox g) := by
  intro x₁ x₂ h a
  induction a using Ordinal.induction with
  | h i ih =>
    rw [lfpApprox, lfpApprox]
    apply sSup_le
    simp only [exists_prop, Set.union_singleton, Set.mem_insert_iff, Set.mem_setOf_eq, sSup_insert,
      forall_eq_or_imp, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    constructor
    · exact le_sup_of_le_left h
    · intro i' h_i'
      apply le_sup_of_le_right
      apply le_sSup_of_le
      · use i'
      · exact g.monotone (ih i' h_i')

/-- Every value of the approximation is less or equal than every fixed point of `f`
greater or equal than the initial value -/
theorem lfpApprox_le_of_mem_fixedPoints {a : β}
    (h_a : a ∈ fixedPoints g) (h_le_init : y ≤ a) (i : Ordinal) : lfpApprox g y i ≤ a := by
  induction i using Ordinal.induction with
  | h i IH =>
    rw [lfpApprox]
    apply sSup_le
    simp only [exists_prop]
    intro y h_y
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff] at h_y
    cases h_y with
    | inl h_y =>
      let ⟨j, h_j_lt, h_j⟩ := h_y
      rw [← h_j, ← h_a]
      exact g.monotone' (IH j h_j_lt)
    | inr h_y =>
      rw [h_y]
      exact h_le_init

/-- The approximation sequence converges at the successor of the domain's cardinality
to the least fixed point if starting from `⊥` -/
theorem lfpApprox_ord_eq_lfp : lfpApprox g ⊥ (ord <| succ #β) = g.lfp := by
  apply le_antisymm
  · have h_lfp : ∃ y : fixedPoints g, g.lfp = y := by use ⊥; exact rfl
    let ⟨y, h_y⟩ := h_lfp; rw [h_y]
    exact lfpApprox_le_of_mem_fixedPoints g ⊥ y.2 bot_le (ord <| succ #β)
  · have h_fix : ∃ y : fixedPoints g, lfpApprox g ⊥ (ord <| succ #β) = y := by
      simpa only [Subtype.exists, mem_fixedPoints, exists_prop, exists_eq_right'] using
        lfpApprox_ord_mem_fixedPoint g ⊥ bot_le
    let ⟨x, h_x⟩ := h_fix; rw [h_x]
    exact lfp_le_fixed g x.prop

/-- Some approximation of the least fixed point starting from `⊥` is the least fixed point. -/
theorem lfp_mem_range_lfpApprox : g.lfp ∈ Set.range (lfpApprox g ⊥) := by
  use ord <| succ #β
  exact lfpApprox_ord_eq_lfp g

-- By unsealing these recursive definitions we can relate them
-- by definitional equality
unseal gfpApprox lfpApprox

theorem gfpApprox_antitone : Antitone (gfpApprox g y) :=
  lfpApprox_monotone g.dual y

theorem gfpApprox_le {a : Ordinal} : gfpApprox g y a ≤ y :=
  le_lfpApprox g.dual y

theorem gfpApprox_add_one_of_le (h : g y ≤ y) (a : Ordinal) :
    gfpApprox g y (a + 1) = g (gfpApprox g y a) :=
  lfpApprox_add_one_of_le g.dual y h a

theorem gfpApprox_mono_left : Monotone (gfpApprox : (β →o β) → _) := by
  intro f g h
  have : g.dual ≤ f.dual := h
  exact lfpApprox_mono_left this

theorem gfpApprox_mono_mid : Monotone (gfpApprox g) :=
  fun _ _ h => lfpApprox_mono_mid g.dual h

/-- The approximations of the greatest fixed point stabilize at a fixed point of `f` -/
theorem gfpApprox_eq_of_mem_fixedPoints {a b : Ordinal} (h_init : g y ≤ y) (h_ab : a ≤ b)
    (h : gfpApprox g y a ∈ fixedPoints g) : gfpApprox g y b = gfpApprox g y a :=
  lfpApprox_eq_of_mem_fixedPoints g.dual y h_init h_ab h

/-- There are distinct indices smaller than the successor of the domain's cardinality
yielding the same value -/
theorem exists_gfpApprox_eq_gfpApprox : ∃ a < ord <| succ #β, ∃ b < ord <| succ #β,
    a ≠ b ∧ gfpApprox g y a = gfpApprox g y b :=
  exists_lfpApprox_eq_lfpApprox g.dual y

/-- The approximation at the index of the successor of the domain's cardinality is a fixed point -/
lemma gfpApprox_ord_mem_fixedPoint (h_init : g y ≤ y) :
    gfpApprox g y (ord <| succ #β) ∈ fixedPoints g :=
  lfpApprox_ord_mem_fixedPoint g.dual y h_init

/-- Every value of the approximation is greater or equal than every fixed point of `f`
less or equal than the initial value -/
lemma le_gfpApprox_of_mem_fixedPoints {a : β}
    (h_a : a ∈ fixedPoints g) (h_le_init : a ≤ y) (i : Ordinal) : a ≤ gfpApprox g y i :=
  lfpApprox_le_of_mem_fixedPoints g.dual y h_a h_le_init i

/-- The approximation sequence converges at the successor of the domain's cardinality
to the greatest fixed point if starting from `⊥` -/
theorem gfpApprox_ord_eq_gfp : gfpApprox g ⊤ (ord <| succ #β) = g.gfp :=
  lfpApprox_ord_eq_lfp g.dual

/-- Some approximation of the least fixed point starting from `⊤` is the greatest fixed point. -/
theorem gfp_mem_range_gfpApprox : g.gfp ∈ Set.range (gfpApprox g ⊤) :=
  lfp_mem_range_lfpApprox g.dual

end OrdinalApprox
