/-
Copyright (c) 2021 Henry Swanson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henry Swanson
-/
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.GroupTheory.Perm.Option
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Option

#align_import combinatorics.derangements.basic from "leanprover-community/mathlib"@"9407b03373c8cd201df99d6bc5514fc2db44054f"

/-!
# Derangements on types

In this file we define `derangements α`, the set of derangements on a type `α`.

We also define some equivalences involving various subtypes of `Perm α` and `derangements α`:
* `derangementsOptionEquivSigmaAtMostOneFixedPoint`: An equivalence between
  `derangements (Option α)` and the sigma-type `Σ a : α, {f : Perm α // fixed_points f ⊆ a}`.
* `derangementsRecursionEquiv`: An equivalence between `derangements (Option α)` and the
  sigma-type `Σ a : α, (derangements (({a}ᶜ : Set α) : Type*) ⊕ derangements α)` which is later
  used to inductively count the number of derangements.

In order to prove the above, we also prove some results about the effect of `Equiv.removeNone`
on derangements: `RemoveNone.fiber_none` and `RemoveNone.fiber_some`.
-/


open Equiv Function

/-- A permutation is a derangement if it has no fixed points. -/
def derangements (α : Type*) : Set (Perm α) :=
  { f : Perm α | ∀ x : α, f x ≠ x }
#align derangements derangements

variable {α β : Type*}

theorem mem_derangements_iff_fixedPoints_eq_empty {f : Perm α} :
    f ∈ derangements α ↔ fixedPoints f = ∅ :=
  Set.eq_empty_iff_forall_not_mem.symm
#align mem_derangements_iff_fixed_points_eq_empty mem_derangements_iff_fixedPoints_eq_empty

/-- If `α` is equivalent to `β`, then `derangements α` is equivalent to `derangements β`. -/
def Equiv.derangementsCongr (e : α ≃ β) : derangements α ≃ derangements β :=
  e.permCongr.subtypeEquiv fun {f} => e.forall_congr <| by
   intro b; simp only [ne_eq, permCongr_apply, symm_apply_apply, EmbeddingLike.apply_eq_iff_eq]
   -- ⊢ ↑f b ≠ b ↔ ↑(↑(permCongr e) f) (↑e b) ≠ ↑e b
            -- 🎉 no goals
#align equiv.derangements_congr Equiv.derangementsCongr

namespace derangements

/-- Derangements on a subtype are equivalent to permutations on the original type where points are
fixed iff they are not in the subtype. -/
protected def subtypeEquiv (p : α → Prop) [DecidablePred p] :
    derangements (Subtype p) ≃ { f : Perm α // ∀ a, ¬p a ↔ a ∈ fixedPoints f } :=
  calc
    derangements (Subtype p) ≃ { f : { f : Perm α // ∀ a, ¬p a → a ∈ fixedPoints f } //
        ∀ a, a ∈ fixedPoints f → ¬p a } := by
      refine' (Perm.subtypeEquivSubtypePerm p).subtypeEquiv fun f => ⟨fun hf a hfa ha => _, _⟩
      -- ⊢ False
      · refine' hf ⟨a, ha⟩ (Subtype.ext _)
        -- ⊢ ↑(↑f { val := a, property := ha }) = ↑{ val := a, property := ha }
        simp_rw [mem_fixedPoints, IsFixedPt, Perm.subtypeEquivSubtypePerm,
        Equiv.coe_fn_mk, Perm.ofSubtype_apply_of_mem _ ha] at hfa
        assumption
        -- 🎉 no goals
      rintro hf ⟨a, ha⟩ hfa
      -- ⊢ False
      refine' hf _ _ ha
      -- ⊢ a ∈ fixedPoints ↑↑(↑(Perm.subtypeEquivSubtypePerm p) f)
      simp only [Perm.subtypeEquivSubtypePerm_apply_coe, mem_fixedPoints]
      -- ⊢ IsFixedPt (↑(↑Perm.ofSubtype f)) a
      dsimp [IsFixedPt]
      -- ⊢ ↑(↑Perm.ofSubtype f) a = a
      simp_rw [Perm.ofSubtype_apply_of_mem _ ha, hfa]
      -- 🎉 no goals
    _ ≃ { f : Perm α // ∃ _h : ∀ a, ¬p a → a ∈ fixedPoints f, ∀ a, a ∈ fixedPoints f → ¬p a } :=
      subtypeSubtypeEquivSubtypeExists _ _
    _ ≃ { f : Perm α // ∀ a, ¬p a ↔ a ∈ fixedPoints f } :=
      subtypeEquivRight fun f => by
        simp_rw [exists_prop, ← forall_and, ← iff_iff_implies_and_implies]
        -- 🎉 no goals
#align derangements.subtype_equiv derangements.subtypeEquiv

universe u
/-- The set of permutations that fix either `a` or nothing is equivalent to the sum of:
    - derangements on `α`
    - derangements on `α` minus `a`. -/
def atMostOneFixedPointEquivSum_derangements [DecidableEq α] (a : α) :
    { f : Perm α // fixedPoints f ⊆ {a} } ≃ Sum (derangements ({a}ᶜ : Set α)) (derangements α) :=
  calc
    { f : Perm α // fixedPoints f ⊆ {a} } ≃
        Sum { f : { f : Perm α // fixedPoints f ⊆ {a} } // a ∈ fixedPoints f }
          { f : { f : Perm α // fixedPoints f ⊆ {a} } // a ∉ fixedPoints f } :=
      (Equiv.sumCompl _).symm
    _ ≃ Sum { f : Perm α // fixedPoints f ⊆ {a} ∧ a ∈ fixedPoints f }
          { f : Perm α // fixedPoints f ⊆ {a} ∧ a ∉ fixedPoints f } := by
      -- porting note: `subtypeSubtypeEquivSubtypeInter` no longer works with placeholder `_`s.
      refine' Equiv.sumCongr _ _
      -- ⊢ { f // a ∈ fixedPoints ↑↑f } ≃ { f // fixedPoints ↑f ⊆ {a} ∧ a ∈ fixedPoints …
      · exact subtypeSubtypeEquivSubtypeInter
          (fun x : Perm α => fixedPoints x ⊆ {a})
          (a ∈ fixedPoints ·)
      · exact subtypeSubtypeEquivSubtypeInter
          (fun x : Perm α => fixedPoints x ⊆ {a})
          (¬a ∈ fixedPoints ·)
    _ ≃ Sum { f : Perm α // fixedPoints f = {a} } { f : Perm α // fixedPoints f = ∅ } := by
      refine' Equiv.sumCongr (subtypeEquivRight fun f => _) (subtypeEquivRight fun f => _)
      -- ⊢ fixedPoints ↑f ⊆ {a} ∧ a ∈ fixedPoints ↑f ↔ fixedPoints ↑f = {a}
      · rw [Set.eq_singleton_iff_unique_mem, and_comm]
        -- ⊢ a ∈ fixedPoints ↑f ∧ fixedPoints ↑f ⊆ {a} ↔ a ∈ fixedPoints ↑f ∧ ∀ (x : α),  …
        rfl
        -- 🎉 no goals
      · rw [Set.eq_empty_iff_forall_not_mem]
        -- ⊢ fixedPoints ↑f ⊆ {a} ∧ ¬a ∈ fixedPoints ↑f ↔ ∀ (x : α), ¬x ∈ fixedPoints ↑f
        refine' ⟨fun h x hx => h.2 (h.1 hx ▸ hx), fun h => ⟨fun x hx => (h _ hx).elim, h _⟩⟩
        -- 🎉 no goals
    _ ≃ Sum (derangements ({a}ᶜ : Set α)) (derangements α) := by
      -- porting note: was `subtypeEquiv _` but now needs the placeholder to be provided explicitly
      refine'
        Equiv.sumCongr ((derangements.subtypeEquiv (· ∈ ({a}ᶜ : Set α))).trans <|
            subtypeEquivRight fun x => _).symm
          (subtypeEquivRight fun f => mem_derangements_iff_fixedPoints_eq_empty.symm)
      rw [eq_comm, Set.ext_iff]
      -- ⊢ (∀ (a_1 : α), ¬a_1 ∈ {a}ᶜ ↔ a_1 ∈ fixedPoints ↑x) ↔ ∀ (x_1 : α), x_1 ∈ {a} ↔ …
      simp_rw [Set.mem_compl_iff, Classical.not_not]
      -- 🎉 no goals
#align derangements.at_most_one_fixed_point_equiv_sum_derangements derangements.atMostOneFixedPointEquivSum_derangements

namespace Equiv

variable [DecidableEq α]

/-- The set of permutations `f` such that the preimage of `(a, f)` under
    `Equiv.Perm.decomposeOption` is a derangement. -/
def RemoveNone.fiber (a : Option α) : Set (Perm α) :=
  { f : Perm α | (a, f) ∈ Equiv.Perm.decomposeOption '' derangements (Option α) }
#align derangements.equiv.remove_none.fiber derangements.Equiv.RemoveNone.fiber

theorem RemoveNone.mem_fiber (a : Option α) (f : Perm α) :
    f ∈ RemoveNone.fiber a ↔
      ∃ F : Perm (Option α), F ∈ derangements (Option α) ∧ F none = a ∧ removeNone F = f :=
  by simp [RemoveNone.fiber, derangements]
     -- 🎉 no goals
#align derangements.equiv.remove_none.mem_fiber derangements.Equiv.RemoveNone.mem_fiber

theorem RemoveNone.fiber_none : RemoveNone.fiber (@none α) = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  -- ⊢ ∀ (x : Perm α), ¬x ∈ fiber none
  intro f hyp
  -- ⊢ False
  rw [RemoveNone.mem_fiber] at hyp
  -- ⊢ False
  rcases hyp with ⟨F, F_derangement, F_none, _⟩
  -- ⊢ False
  exact F_derangement none F_none
  -- 🎉 no goals
#align derangements.equiv.remove_none.fiber_none derangements.Equiv.RemoveNone.fiber_none

/-- For any `a : α`, the fiber over `some a` is the set of permutations
    where `a` is the only possible fixed point. -/
theorem RemoveNone.fiber_some (a : α) :
    RemoveNone.fiber (some a) = { f : Perm α | fixedPoints f ⊆ {a} } := by
  ext f
  -- ⊢ f ∈ fiber (some a) ↔ f ∈ {f | fixedPoints ↑f ⊆ {a}}
  constructor
  -- ⊢ f ∈ fiber (some a) → f ∈ {f | fixedPoints ↑f ⊆ {a}}
  · rw [RemoveNone.mem_fiber]
    -- ⊢ (∃ F, F ∈ derangements (Option α) ∧ ↑F none = some a ∧ removeNone F = f) → f …
    rintro ⟨F, F_derangement, F_none, rfl⟩ x x_fixed
    -- ⊢ x ∈ {a}
    rw [mem_fixedPoints_iff] at x_fixed
    -- ⊢ x ∈ {a}
    apply_fun some at x_fixed
    -- ⊢ x ∈ {a}
    cases' Fx : F (some x) with y
    -- ⊢ x ∈ {a}
    · rwa [removeNone_none F Fx, F_none, Option.some_inj, eq_comm] at x_fixed
      -- 🎉 no goals
    · exfalso
      -- ⊢ False
      rw [removeNone_some F ⟨y, Fx⟩] at x_fixed
      -- ⊢ False
      exact F_derangement _ x_fixed
      -- 🎉 no goals
  · intro h_opfp
    -- ⊢ f ∈ fiber (some a)
    use Equiv.Perm.decomposeOption.symm (some a, f)
    -- ⊢ ↑Perm.decomposeOption.symm (some a, f) ∈ derangements (Option α) ∧ ↑Perm.dec …
    constructor
    -- ⊢ ↑Perm.decomposeOption.symm (some a, f) ∈ derangements (Option α)
    · intro x
      -- ⊢ ↑(↑Perm.decomposeOption.symm (some a, f)) x ≠ x
      apply_fun fun x => Equiv.swap none (some a) x
      -- ⊢ (fun x => ↑(Equiv.swap none (some a)) x) (↑(↑Perm.decomposeOption.symm (some …
      simp only [Perm.decomposeOption_symm_apply, swap_apply_self, Perm.coe_mul]
      -- ⊢ ↑(Equiv.swap none (some a)) ((↑(Equiv.swap none (some a)) ∘ ↑(optionCongr f) …
      cases' x with x
      -- ⊢ ↑(Equiv.swap none (some a)) ((↑(Equiv.swap none (some a)) ∘ ↑(optionCongr f) …
      · simp
        -- 🎉 no goals
      simp only [comp, optionCongr_apply, Option.map_some', swap_apply_self]
      -- ⊢ some (↑f x) ≠ ↑(Equiv.swap none (some a)) (some x)
      by_cases x_vs_a : x = a
      -- ⊢ some (↑f x) ≠ ↑(Equiv.swap none (some a)) (some x)
      · rw [x_vs_a, swap_apply_right]
        -- ⊢ some (↑f a) ≠ none
        apply Option.some_ne_none
        -- 🎉 no goals
      have ne_1 : some x ≠ none := Option.some_ne_none _
      -- ⊢ some (↑f x) ≠ ↑(Equiv.swap none (some a)) (some x)
      have ne_2 : some x ≠ some a := (Option.some_injective α).ne_iff.mpr x_vs_a
      -- ⊢ some (↑f x) ≠ ↑(Equiv.swap none (some a)) (some x)
      rw [swap_apply_of_ne_of_ne ne_1 ne_2, (Option.some_injective α).ne_iff]
      -- ⊢ ↑f x ≠ x
      intro contra
      -- ⊢ False
      exact x_vs_a (h_opfp contra)
      -- 🎉 no goals
    · rw [apply_symm_apply]
      -- 🎉 no goals
#align derangements.equiv.remove_none.fiber_some derangements.Equiv.RemoveNone.fiber_some

end Equiv

section Option

variable [DecidableEq α]

/-- The set of derangements on `Option α` is equivalent to the union over `a : α`
    of "permutations with `a` the only possible fixed point". -/
def derangementsOptionEquivSigmaAtMostOneFixedPoint :
    derangements (Option α) ≃ Σa : α, { f : Perm α | fixedPoints f ⊆ {a} } := by
  have fiber_none_is_false : Equiv.RemoveNone.fiber (@none α) → False := by
    rw [Equiv.RemoveNone.fiber_none]
    exact IsEmpty.false
  calc
    derangements (Option α) ≃ Equiv.Perm.decomposeOption '' derangements (Option α) :=
      Equiv.image _ _
    _ ≃ Σa : Option α, ↥(Equiv.RemoveNone.fiber a) := setProdEquivSigma _
    _ ≃ Σa : α, ↥(Equiv.RemoveNone.fiber (some a)) :=
      sigmaOptionEquivOfSome _ fiber_none_is_false
    _ ≃ Σa : α, { f : Perm α | fixedPoints f ⊆ {a} } := by
      simp_rw [Equiv.RemoveNone.fiber_some]
      rfl
#align derangements.derangements_option_equiv_sigma_at_most_one_fixed_point derangements.derangementsOptionEquivSigmaAtMostOneFixedPoint

/-- The set of derangements on `Option α` is equivalent to the union over all `a : α` of
    "derangements on `α` ⊕ derangements on `{a}ᶜ`". -/
def derangementsRecursionEquiv :
    derangements (Option α) ≃
      Σa : α, Sum (derangements (({a}ᶜ : Set α) : Type _)) (derangements α) :=
  derangementsOptionEquivSigmaAtMostOneFixedPoint.trans
    (sigmaCongrRight atMostOneFixedPointEquivSum_derangements)
#align derangements.derangements_recursion_equiv derangements.derangementsRecursionEquiv

end Option

end derangements
