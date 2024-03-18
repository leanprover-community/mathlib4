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

theorem not_injective_limitation_set : ¬ InjOn g (Iio (ord <| succ #α)) := by
  intro h_inj
  have h := lift_mk_le_lift_mk_of_injective <| injOn_iff_injective.1 h_inj
  have mk_initialSeg_subtype :
      #(Iio (ord <| succ #α)) = lift.{u+1, u} (succ #α) := by
    simpa only [coe_setOf, card_typein, card_ord] using mk_initialSeg (ord <| succ #α)
  rw [mk_initialSeg_subtype, lift_lift, lift_le] at h
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

theorem lfpApprox_add_one (a : Ordinal.{u}) : lfpApprox f (a+1) = f (lfpApprox f a) := by
  apply le_antisymm
  · conv => left; unfold lfpApprox
    apply sSup_le
    simp only [Ordinal.add_one_eq_succ, lt_succ_iff, exists_prop, Set.mem_setOf_eq,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intros a' h
    apply f.2; apply lfpApprox_monotone; exact h
  · conv => right; unfold lfpApprox
    apply le_sSup
    simp only [Ordinal.add_one_eq_succ, lt_succ_iff, exists_prop, Set.mem_setOf_eq]
    use a

/-- The ordinal approximants of the least fixed points are stabilizing
  when reaching a fixed point of f -/
theorem lfpApprox_eq_of_mem_fixedPoint {a b : Ordinal.{u}} (h_ab : a ≤ b)
    (h: lfpApprox f a ∈ fixedPoints f) : lfpApprox f b = lfpApprox f a := by
  rw [mem_fixedPoints_iff] at h
  induction b using Ordinal.induction with | h b IH =>
  apply le_antisymm
  · conv => left; unfold lfpApprox
    apply sSup_le
    simp only [exists_prop, Set.mem_setOf_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro a' ha'b
    by_cases haa : a' < a
    · rw [← lfpApprox_add_one]
      apply lfpApprox_monotone
      simp only [Ordinal.add_one_eq_succ, succ_le_iff]
      exact haa
    · simp only [not_lt] at haa
      cases le_iff_lt_or_eq.mp haa with
      | inl haa => specialize IH a' ha'b (le_of_lt haa); rw [IH, h]
      | inr haa => rw [← haa, h]
  · exact lfpApprox_monotone f h_ab

/-- There are distinct ordinals smaller than the successor of the domains cardinals
  with equal value -/
theorem distinct_ordinal_eq_lfpApprox : ∃ a < ord <| succ #α, ∃ b < ord <| succ #α,
    a ≠ b ∧ lfpApprox f a = lfpApprox f b := by
  have h_ninj := not_injective_limitation_set <| lfpApprox f
  rw [Set.injOn_iff_injective, Function.not_injective_iff] at h_ninj
  let ⟨a, b, h_fab, h_nab⟩ := h_ninj
  use a.val; apply And.intro a.prop
  use b.val; apply And.intro b.prop
  apply And.intro
  · intro h_eq; rw [Subtype.coe_inj] at h_eq; exact h_nab h_eq
  · exact h_fab

/-- If there are distinct ordinals with equal value then
  every value succeding the smaller ordinal are fixed points -/
lemma lfpApprox_mem_fixedPoints_of_eq {a b c : Ordinal.{u}} (h_ab : a < b) (h_ac : a ≤ c)
    (h_fab : lfpApprox f a = lfpApprox f b) :
    lfpApprox f c ∈ fixedPoints f := by
  have lfpApprox_has_one_fixedPoint :
      lfpApprox f a ∈ fixedPoints f := by
    rw [mem_fixedPoints_iff, ← lfpApprox_add_one]
    exact Monotone.eq_of_le_of_le (lfpApprox_monotone f)
      h_fab (SuccOrder.le_succ a) (SuccOrder.succ_le_of_lt h_ab)
  rw [lfpApprox_eq_of_mem_fixedPoint f]
  · exact lfpApprox_has_one_fixedPoint
  · exact h_ac
  · exact lfpApprox_has_one_fixedPoint

/-- A fixed point of f is reached after the successor of the domains cardinality -/
theorem lfpApprox_has_fixedPoint_cardinal : lfpApprox f (ord <| succ #α) ∈ fixedPoints f := by
  let ⟨a, h_a, b, h_b, h_nab, h_fab⟩ := distinct_ordinal_eq_lfpApprox f
  cases le_total a b with
  | inl h_ab =>
    exact lfpApprox_mem_fixedPoints_of_eq f (h_nab.lt_of_le h_ab) (le_of_lt h_a) h_fab
  | inr h_ba =>
    exact lfpApprox_mem_fixedPoints_of_eq f (h_nab.symm.lt_of_le h_ba) (le_of_lt h_b) (h_fab.symm)

/-- Every value of the ordinal approximants are less or equal than every fixed point of f -/
theorem lfpApprox_le_fixedPoint {a : α} (h_a : a ∈ fixedPoints f) (i : Ordinal) :
    lfpApprox f i ≤ a := by
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
    exact lfpApprox_le_fixedPoint f x.2 (ord <| succ #α)
  · have h_fix : ∃ x : fixedPoints f, lfpApprox f (ord <| succ #α) = x := by
      simpa only [Subtype.exists, mem_fixedPoints, exists_prop, exists_eq_right'] using
        lfpApprox_has_fixedPoint_cardinal f
    let ⟨x, h_x⟩ := h_fix; rw [h_x]
    exact lfp_le_fixed f x.prop

/-- Some ordinal approximation of the least fixed point is the least fixed point. -/
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

theorem gfpApprox_add_one (a : Ordinal.{u}) : gfpApprox f (a+1) = f (gfpApprox f a) :=
  lfpApprox_add_one (OrderHom.dual f) a

/-- The ordinal approximants of the least fixed points are stabilizing
  when reaching a fixed point of f -/
theorem gfpApprox_eq_of_mem_fixedPoint {a b : Ordinal.{u}} (h_ab : a ≤ b)
    (h: gfpApprox f a ∈ fixedPoints f) : gfpApprox f b = gfpApprox f a :=
  lfpApprox_eq_of_mem_fixedPoint (OrderHom.dual f) h_ab h

/-- There are distinct ordinals smaller than the successor of the domains cardinals with
  equal value -/
theorem distinct_ordinal_eq_gfpApprox : ∃ a < ord <| succ #α, ∃ b < ord <| succ #α,
    a ≠ b ∧ gfpApprox f a = gfpApprox f b :=
  distinct_ordinal_eq_lfpApprox (OrderHom.dual f)

/-- A fixed point of f is reached after the successor of the domains cardinality -/
lemma gfpApprox_has_fixedPoint_cardinal : gfpApprox f (ord <| succ #α) ∈ fixedPoints f :=
  lfpApprox_has_fixedPoint_cardinal (OrderHom.dual f)

/-- Every value of the ordinal approximants are greater or equal than every fixed point of f -/
lemma gfpApprox_ge_fixedPoint {a : α} (h_a : a ∈ fixedPoints f) (i : Ordinal) : gfpApprox f i ≥ a :=
  lfpApprox_le_fixedPoint (OrderHom.dual f) h_a i

/-- The greatest fixed point of f is reached after the successor of the domains cardinality -/
theorem gfpApprox_cardinal_is_gfp : gfpApprox f (ord <| succ #α) = gfp f :=
  lfpApprox_cardinal_is_lfp (OrderHom.dual f)

/-- Some ordinal approximation of the greatest fixed point is the greatest fixed point. -/
theorem gfpApprox_is_gfp : ∃ a : Ordinal, gfpApprox f a = gfp f :=
  lfpApprox_is_lfp (OrderHom.dual f)

end OrdinalApprox
