/-
Copyright (c) 2024 Ira Fesefeldt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ira Fesefeldt
-/
import Mathlib.Order.FixedPoints
import Mathlib.Logic.Function.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic


/-!
# Ordinal Approximants for the Fixed points on complete lattices

This file sets up the ordinal approximation theory of fixed points
of a monotone function in a complete lattice [Cousot1979].
The proof follows loosely the one from [Echenique2005].

However, the proof given here is not constructive as we use the non-constructive axiomatization of
ordinals from mathlib. It still allows an approximation scheme indexed over the ordinals.

## Main definitions

* `OrdinalApprox.lfpApprox`: The ordinal approximation of
  the least fixed point of a bundled monotone function.
* `OrdinalApprox.gfpApprox`: The ordinal approximation of
  the greatest fixed point of a bundled monotone function.

## Main theorems
* `OrdinalApprox.lfpApprox_is_lfp`: The approximation of
  the least fixed point eventually reaches the least fixed point
* `OrdinalApprox.gfpApprox_is_gfp`: The approximation of
  the greatest fixed point eventually reaches the greatest fixed point

## References
* [F. Echenique, *A short and constructive proof of Tarski’s fixed-point theorem*][Echenique2005]
* [P. Cousot & R. Cousot, *Constructive Versions of Tarski's Fixed Point Theorems*][Cousot1979]

## Tags

fixed point, complete lattice, monotone function, ordinals, approximation
-/

namespace Cardinal

universe u
variable {α : Type u}
variable (g : Ordinal → α)

open Cardinal Ordinal SuccOrder Function Set

theorem not_injective_limitation_set : ¬ Set.InjOn g (Set.Iio (ord <| succ #α)) := by
  intro h_inj
  have h := lift_mk_le_lift_mk_of_injective <| Set.injOn_iff_injective.1 h_inj
  have mk_initialSeg_subtype :
      #(Iio (ord <| succ #α)) = lift.{u+1, u} (succ #α) := by
    simpa only [coe_setOf, card_typein, card_ord] using mk_initialSeg (ord <| succ #α)
  rw [mk_initialSeg_subtype, Cardinal.lift_lift, Cardinal.lift_le] at h
  exact not_le_of_lt (Order.lt_succ #α) h



end Cardinal

namespace OrdinalApprox

universe u
variable {α : Type u}
variable [CompleteLattice α] (f : α →o α)

open Function fixedPoints Cardinal Order OrderHom

set_option linter.unusedVariables false in
/-- Ordinal approximants of the least fixed points -/
def lfpApprox (a : Ordinal.{u}) : α :=
  sSup { f (lfpApprox b) | (b : Ordinal) (h : b < a) }
termination_by a
decreasing_by exact h

theorem lfpApprox_monotone : Monotone (lfpApprox f) := by
  unfold Monotone; intros a b h; unfold lfpApprox
  refine sSup_le_sSup ?h
  simp only [exists_prop, Set.setOf_subset_setOf, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂]
  intros a' h'
  use a'
  exact ⟨lt_of_lt_of_le h' h, rfl⟩

theorem lfpApprox_addition (a : Ordinal.{u}) : f (lfpApprox f a) = lfpApprox f (a+1) := by
  apply le_antisymm
  · conv => right; unfold lfpApprox
    apply le_sSup
    simp only [Ordinal.add_one_eq_succ, lt_succ_iff, exists_prop, Set.mem_setOf_eq]
    use a
  · conv => left; unfold lfpApprox
    apply sSup_le
    simp only [Ordinal.add_one_eq_succ, lt_succ_iff, exists_prop, Set.mem_setOf_eq,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intros a' h
    apply f.2; apply lfpApprox_monotone; exact h

/-- The ordinal approximants of the least fixed points are stabilizing
  when reaching a fixed point of f -/
theorem lfpApprox_stabilizing_at_fixedPoint (a : Ordinal.{u}) (h: lfpApprox f a ∈ fixedPoints f) :
    ∀ b > a, lfpApprox f b = lfpApprox f a := by
  intro b hab; rw [mem_fixedPoints_iff] at h
  induction b using Ordinal.induction with | h b IH =>
  apply le_antisymm
  · conv => left; unfold lfpApprox
    apply sSup_le
    simp only [exists_prop, Set.mem_setOf_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro a' ha'b
    by_cases haa : a' < a
    · rw [lfpApprox_addition]
      apply lfpApprox_monotone
      simp only [Ordinal.add_one_eq_succ, succ_le_iff]
      exact haa
    · simp only [not_lt] at haa
      cases le_iff_lt_or_eq.mp haa with
      | inl haa => specialize IH a' ha'b haa; rw [IH, h]
      | inr haa => rw [← haa, h]
  · conv => right; unfold lfpApprox
    apply le_sSup
    simp only [exists_prop, Set.mem_setOf_eq]
    use a

/-- Every value after a fixed point of f is also a fixed point of f -/
theorem lfpApprox_ordinals_after_fixed_are_fixed (a : Ordinal.{u})
    (h : lfpApprox f a ∈ fixedPoints f) : ∀ b > a, lfpApprox f b ∈ fixedPoints f  := by
  intro b h_ab
  rw [mem_fixedPoints_iff]
  have h_stab := lfpApprox_stabilizing_at_fixedPoint f a h b h_ab
  rw [h_stab]
  exact mem_fixedPoints_iff.mp h

/-- There are distinct ordinals smaller than the successor of the domains cardinals
  with equal value -/
theorem disctinct_ordinal_eq_lfpApprox : ∃ i < ord <| succ #α, ∃ j < ord <| succ #α,
    i ≠ j ∧ lfpApprox f i = lfpApprox f j := by
  -- have h_ninj := Function.not_injective_iff.1
  --   ( Set.injOn_iff_injective.1 <| not_injective_limitation_set <| lfpApprox f)
  have h_ninj := not_injective_limitation_set <| lfpApprox f
  rw [Set.injOn_iff_injective, Function.not_injective_iff] at h_ninj
  let ⟨a, b, h_fab, h_nab⟩ := h_ninj
  use a.val; apply And.intro a.prop
  use b.val; apply And.intro b.prop
  apply And.intro
  · intro h_eq; rw [Subtype.coe_inj] at h_eq; exact h_nab h_eq
  · exact h_fab

/-- If there are disctinct ordinals with equal value then
  every value succeding the smaller ordinal are fixed points -/
lemma lfpApprox_mem_fixedPoints_of_eq (a b : Ordinal.{u}) (h : a < b)
    (h_fab : lfpApprox f a = lfpApprox f b) :
    ∀ i ≥ a, lfpApprox f i ∈ fixedPoints f := by
  intro i h_i
  have lfpApprox_has_one_fixedPoint (c d : Ordinal.{u}) (h : c < d)
      (h_fab : lfpApprox f c = lfpApprox f d) :
      lfpApprox f c ∈ fixedPoints f := by
    rw [mem_fixedPoints_iff, lfpApprox_addition]
    exact Monotone.eq_of_le_of_le (lfpApprox_monotone f)
      h_fab (SuccOrder.le_succ c) (SuccOrder.succ_le_of_lt h)
  obtain rfl | h_ia := eq_or_ne i a
  · exact lfpApprox_has_one_fixedPoint i b h h_fab
  · apply lfpApprox_ordinals_after_fixed_are_fixed f a
    · exact lfpApprox_has_one_fixedPoint a b h h_fab
    · exact Ne.lt_of_le' h_ia h_i

/-- A fixed point of f is reached after the successor of the domains cardinality -/
theorem lfpApprox_has_fixedPoint_cardinal : lfpApprox f (ord <| succ #α) ∈ fixedPoints f := by
  let ⟨a, h_a, b, h_b, h_nab, h_fab⟩ := disctinct_ordinal_eq_lfpApprox f
  cases le_total a b with
  | inl h_ab =>
    exact lfpApprox_mem_fixedPoints_of_eq f a b (h_nab.lt_of_le h_ab) h_fab
      (ord <| succ #α) (le_of_lt h_a)
  | inr h_ba =>
    exact lfpApprox_mem_fixedPoints_of_eq f b a (h_nab.symm.lt_of_le h_ba)
      (h_fab.symm) (ord <| succ #α) (le_of_lt h_b)

/-- Every value of the ordinal approximants are less or equal than every fixed point of f -/
theorem lfpApprox_le_fixedPoint : ∀ a : fixedPoints f, ∀ i : Ordinal, lfpApprox f i ≤ a := by
  intro ⟨a, h_a⟩ i
  induction i using Ordinal.induction with
  | h i IH =>
    unfold lfpApprox
    apply sSup_le
    simp only [exists_prop, Set.mem_setOf_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro j h_j
    rw [← h_a]
    apply f.monotone'
    exact IH j h_j

/-- The least fixed point of f is reached after the successor of the domains cardinality -/
theorem lfpApprox_cardinal_is_lfp : lfpApprox f (ord <| succ #α) = lfp f := by
  apply le_antisymm
  · have h_lfp : ∃ x : fixedPoints f, lfp f = x := by use ⊥; exact rfl
    let ⟨x, h_x⟩ := h_lfp; rw [h_x]
    exact lfpApprox_le_fixedPoint f x (ord <| succ #α)
  · have h_fix : ∃ x : fixedPoints f, lfpApprox f (ord <| succ #α) = x := by
      simpa only [Subtype.exists, mem_fixedPoints, exists_prop, exists_eq_right'] using
        lfpApprox_has_fixedPoint_cardinal f
    let ⟨x, h_x⟩ := h_fix; rw [h_x]
    exact lfp_le_fixed f x.prop

/-- Some ordinal approximation of the least fixed point is the least fixed point.
  Also known as ordinal approximation of the least fixed point.-/
theorem lfpApprox_is_lfp : ∃ a : Ordinal, lfpApprox f a = lfp f := by
  use (ord <| succ #α)
  exact lfpApprox_cardinal_is_lfp f

set_option linter.unusedVariables false in
/-- Ordinal approximants of the greatest fixed points -/
def gfpApprox (a : Ordinal.{u}) : α :=
  sInf { f (gfpApprox b) | (b : Ordinal) (h : b < a) }
termination_by a
decreasing_by exact h

theorem gfpApprox_antitone : Antitone (gfpApprox f) :=
  lfpApprox_monotone (OrderHom.dual f)

theorem gfpApprox_addition (a : Ordinal.{u}) : f (gfpApprox f a) = gfpApprox f (a+1) :=
  lfpApprox_addition (OrderHom.dual f) a

/-- The ordinal approximants of the least fixed points are stabilizing
  when reaching a fixed point of f -/
theorem gfpApprox_stabilizing_at_fixedPoint (a : Ordinal.{u}) (h : gfpApprox f a ∈ fixedPoints f) :
    ∀ b > a, gfpApprox f b = gfpApprox f a :=
  lfpApprox_stabilizing_at_fixedPoint (OrderHom.dual f) a h

/-- Every value after a fixed point of f is also a fixed point of f -/
theorem gfpApprox_ordinals_after_fixed_are_fixed (a : Ordinal.{u})
    (h: gfpApprox f a ∈ fixedPoints f) : ∀ b > a, gfpApprox f b ∈ fixedPoints f :=
  lfpApprox_ordinals_after_fixed_are_fixed (OrderHom.dual f) a h

/-- There are distinct ordinals smaller than the successor of the domains cardinals with
  equal value -/
theorem disctinct_ordinal_eq_gfpApprox : ∃ i < ord <| succ #α, ∃ j < ord <| succ #α,
    i ≠ j ∧ gfpApprox f i = gfpApprox f j :=
  disctinct_ordinal_eq_lfpApprox (OrderHom.dual f)

/-- A fixed point of f is reached after the successor of the domains cardinality -/
lemma gfpApprox_has_fixedPoint_cardinal : gfpApprox f (ord <| succ #α) ∈ fixedPoints f :=
  lfpApprox_has_fixedPoint_cardinal (OrderHom.dual f)

/-- Every value of the ordinal approximants are greater or equal than every fixed point of f -/
lemma gfpApprox_ge_fixedPoint : ∀ a : fixedPoints f, ∀ i : Ordinal, gfpApprox f i ≥ a :=
  lfpApprox_le_fixedPoint (OrderHom.dual f)

/-- The greatest fixed point of f is reached after the successor of the domains cardinality -/
theorem gfpApprox_cardinal_is_gfp : gfpApprox f (ord <| succ #α) = gfp f :=
  lfpApprox_cardinal_is_lfp (OrderHom.dual f)

/-- Some ordinal approximation of the greatest fixed point is the greatest fixed point.
  Also known as ordinal approximation of the greatest fixed point.-/
theorem gfpApprox_is_gfp : ∃ a : Ordinal, gfpApprox f a = gfp f :=
  lfpApprox_is_lfp (OrderHom.dual f)

end OrdinalApprox
