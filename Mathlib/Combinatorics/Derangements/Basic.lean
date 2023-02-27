/-
Copyright (c) 2021 Henry Swanson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henry Swanson

! This file was ported from Lean 3 source module combinatorics.derangements.basic
! leanprover-community/mathlib commit 9407b03373c8cd201df99d6bc5514fc2db44054f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Dynamics.FixedPoints.Basic
import Mathbin.GroupTheory.Perm.Option
import Mathbin.Logic.Equiv.Defs
import Mathbin.Logic.Equiv.Option

/-!
# Derangements on types

In this file we define `derangements α`, the set of derangements on a type `α`.

We also define some equivalences involving various subtypes of `perm α` and `derangements α`:
* `derangements_option_equiv_sigma_at_most_one_fixed_point`: An equivalence between
  `derangements (option α)` and the sigma-type `Σ a : α, {f : perm α // fixed_points f ⊆ a}`.
* `derangements_recursion_equiv`: An equivalence between `derangements (option α)` and the
  sigma-type `Σ a : α, (derangements (({a}ᶜ : set α) : Type _) ⊕ derangements α)` which is later
  used to inductively count the number of derangements.

In order to prove the above, we also prove some results about the effect of `equiv.remove_none`
on derangements: `remove_none.fiber_none` and `remove_none.fiber_some`.
-/


open Equiv Function

/-- A permutation is a derangement if it has no fixed points. -/
def derangements (α : Type _) : Set (Perm α) :=
  { f : Perm α | ∀ x : α, f x ≠ x }
#align derangements derangements

variable {α β : Type _}

theorem mem_derangements_iff_fixedPoints_eq_empty {f : Perm α} :
    f ∈ derangements α ↔ fixedPoints f = ∅ :=
  Set.eq_empty_iff_forall_not_mem.symm
#align mem_derangements_iff_fixed_points_eq_empty mem_derangements_iff_fixedPoints_eq_empty

/-- If `α` is equivalent to `β`, then `derangements α` is equivalent to `derangements β`. -/
def Equiv.derangementsCongr (e : α ≃ β) : derangements α ≃ derangements β :=
  e.permCongr.subtypeEquiv fun f => e.forall_congr' <| by simp
#align equiv.derangements_congr Equiv.derangementsCongr

namespace derangements

/-- Derangements on a subtype are equivalent to permutations on the original type where points are
fixed iff they are not in the subtype. -/
protected def subtypeEquiv (p : α → Prop) [DecidablePred p] :
    derangements (Subtype p) ≃ { f : Perm α // ∀ a, ¬p a ↔ a ∈ fixedPoints f } :=
  calc
    derangements (Subtype p) ≃
        { f : { f : Perm α // ∀ a, ¬p a → a ∈ fixedPoints f } // ∀ a, a ∈ fixedPoints f → ¬p a } :=
      by
      refine' (perm.subtype_equiv_subtype_perm p).subtypeEquiv fun f => ⟨fun hf a hfa ha => _, _⟩
      · refine' hf ⟨a, ha⟩ (Subtype.ext _)
        rwa [mem_fixed_points, is_fixed_pt, perm.subtype_equiv_subtype_perm, @coeFn_coe_base',
          Equiv.coe_fn_mk, Subtype.coe_mk, Equiv.Perm.ofSubtype_apply_of_mem] at hfa
      rintro hf ⟨a, ha⟩ hfa
      refine' hf _ _ ha
      change perm.subtype_equiv_subtype_perm p f a = a
      rw [perm.subtype_equiv_subtype_perm_apply_of_mem f ha, hfa, Subtype.coe_mk]
    _ ≃ { f : Perm α // ∃ h : ∀ a, ¬p a → a ∈ fixedPoints f, ∀ a, a ∈ fixedPoints f → ¬p a } :=
      subtypeSubtypeEquivSubtypeExists _ _
    _ ≃ { f : Perm α // ∀ a, ¬p a ↔ a ∈ fixedPoints f } :=
      subtypeEquivRight fun f => by
        simp_rw [exists_prop, ← forall_and, ← iff_iff_implies_and_implies]
    
#align derangements.subtype_equiv derangements.subtypeEquiv

/-- The set of permutations that fix either `a` or nothing is equivalent to the sum of:
    - derangements on `α`
    - derangements on `α` minus `a`. -/
def atMostOneFixedPointEquivSumDerangements [DecidableEq α] (a : α) :
    { f : Perm α // fixedPoints f ⊆ {a} } ≃ Sum (derangements ({a}ᶜ : Set α)) (derangements α) :=
  calc
    { f : Perm α // fixedPoints f ⊆ {a} } ≃
        Sum { f : { f : Perm α // fixedPoints f ⊆ {a} } // a ∈ fixedPoints f }
          { f : { f : Perm α // fixedPoints f ⊆ {a} } // a ∉ fixedPoints f } :=
      (Equiv.sumCompl _).symm
    _ ≃
        Sum { f : Perm α // fixedPoints f ⊆ {a} ∧ a ∈ fixedPoints f }
          { f : Perm α // fixedPoints f ⊆ {a} ∧ a ∉ fixedPoints f } :=
      by
      refine' Equiv.sumCongr _ _ <;>
        · convert subtype_subtype_equiv_subtype_inter _ _
          ext f
          rfl
    _ ≃ Sum { f : Perm α // fixedPoints f = {a} } { f : Perm α // fixedPoints f = ∅ } :=
      by
      refine' Equiv.sumCongr (subtype_equiv_right fun f => _) (subtype_equiv_right fun f => _)
      · rw [Set.eq_singleton_iff_unique_mem, and_comm']
        rfl
      · rw [Set.eq_empty_iff_forall_not_mem]
        refine' ⟨fun h x hx => h.2 (h.1 hx ▸ hx), fun h => ⟨fun x hx => (h _ hx).elim, h _⟩⟩
    _ ≃ Sum (derangements ({a}ᶜ : Set α)) (derangements α) :=
      by
      refine'
        Equiv.sumCongr ((derangements.subtypeEquiv _).trans <| subtype_equiv_right fun x => _).symm
          (subtype_equiv_right fun f => mem_derangements_iff_fixed_points_eq_empty.symm)
      rw [eq_comm, Set.ext_iff]
      simp_rw [Set.mem_compl_iff, Classical.not_not]
    
#align derangements.at_most_one_fixed_point_equiv_sum_derangements derangements.atMostOneFixedPointEquivSumDerangements

namespace Equiv

variable [DecidableEq α]

/-- The set of permutations `f` such that the preimage of `(a, f)` under
    `equiv.perm.decompose_option` is a derangement. -/
def RemoveNone.fiber (a : Option α) : Set (Perm α) :=
  { f : Perm α | (a, f) ∈ Equiv.Perm.decomposeOption '' derangements (Option α) }
#align derangements.equiv.remove_none.fiber derangements.Equiv.RemoveNone.fiber

theorem RemoveNone.mem_fiber (a : Option α) (f : Perm α) :
    f ∈ RemoveNone.fiber a ↔
      ∃ F : Perm (Option α), F ∈ derangements (Option α) ∧ F none = a ∧ removeNone F = f :=
  by simp [remove_none.fiber, derangements]
#align derangements.equiv.remove_none.mem_fiber derangements.Equiv.RemoveNone.mem_fiber

theorem RemoveNone.fiber_none : RemoveNone.fiber (@none α) = ∅ :=
  by
  rw [Set.eq_empty_iff_forall_not_mem]
  intro f hyp
  rw [remove_none.mem_fiber] at hyp
  rcases hyp with ⟨F, F_derangement, F_none, _⟩
  exact F_derangement none F_none
#align derangements.equiv.remove_none.fiber_none derangements.Equiv.RemoveNone.fiber_none

/-- For any `a : α`, the fiber over `some a` is the set of permutations
    where `a` is the only possible fixed point. -/
theorem RemoveNone.fiber_some (a : α) :
    RemoveNone.fiber (some a) = { f : Perm α | fixedPoints f ⊆ {a} } :=
  by
  ext f
  constructor
  · rw [remove_none.mem_fiber]
    rintro ⟨F, F_derangement, F_none, rfl⟩ x x_fixed
    rw [mem_fixed_points_iff] at x_fixed
    apply_fun some  at x_fixed
    cases' Fx : F (some x) with y
    · rwa [remove_none_none F Fx, F_none, Option.some_inj, eq_comm] at x_fixed
    · exfalso
      rw [remove_none_some F ⟨y, Fx⟩] at x_fixed
      exact F_derangement _ x_fixed
  · intro h_opfp
    use equiv.perm.decompose_option.symm (some a, f)
    constructor
    · intro x
      apply_fun swap none (some a)
      simp only [perm.decompose_option_symm_apply, swap_apply_self, perm.coe_mul]
      cases x
      · simp
      simp only [Equiv.optionCongr_apply, Option.map_some']
      by_cases x_vs_a : x = a
      · rw [x_vs_a, swap_apply_right]
        apply Option.some_ne_none
      have ne_1 : some x ≠ none := Option.some_ne_none _
      have ne_2 : some x ≠ some a := (Option.some_injective α).ne_iff.mpr x_vs_a
      rw [swap_apply_of_ne_of_ne ne_1 ne_2, (Option.some_injective α).ne_iff]
      intro contra
      exact x_vs_a (h_opfp contra)
    · rw [apply_symm_apply]
#align derangements.equiv.remove_none.fiber_some derangements.Equiv.RemoveNone.fiber_some

end Equiv

section Option

variable [DecidableEq α]

/-- The set of derangements on `option α` is equivalent to the union over `a : α`
    of "permutations with `a` the only possible fixed point". -/
def derangementsOptionEquivSigmaAtMostOneFixedPoint :
    derangements (Option α) ≃ Σa : α, { f : Perm α | fixedPoints f ⊆ {a} } :=
  by
  have fiber_none_is_false : equiv.remove_none.fiber (@none α) → False :=
    by
    rw [equiv.remove_none.fiber_none]
    exact IsEmpty.false
  calc
    derangements (Option α) ≃ Equiv.Perm.decomposeOption '' derangements (Option α) :=
      Equiv.image _ _
    _ ≃ Σa : Option α, ↥(equiv.remove_none.fiber a) := set_prod_equiv_sigma _
    _ ≃ Σa : α, ↥(equiv.remove_none.fiber (some a)) :=
      sigma_option_equiv_of_some _ fiber_none_is_false
    _ ≃ Σa : α, { f : perm α | fixed_points f ⊆ {a} } := by simp_rw [equiv.remove_none.fiber_some]
    
#align derangements.derangements_option_equiv_sigma_at_most_one_fixed_point derangements.derangementsOptionEquivSigmaAtMostOneFixedPoint

/-- The set of derangements on `option α` is equivalent to the union over all `a : α` of
    "derangements on `α` ⊕ derangements on `{a}ᶜ`". -/
def derangementsRecursionEquiv :
    derangements (Option α) ≃
      Σa : α, Sum (derangements (({a}ᶜ : Set α) : Type _)) (derangements α) :=
  derangementsOptionEquivSigmaAtMostOneFixedPoint.trans
    (sigmaCongrRight atMostOneFixedPointEquivSumDerangements)
#align derangements.derangements_recursion_equiv derangements.derangementsRecursionEquiv

end Option

end derangements

