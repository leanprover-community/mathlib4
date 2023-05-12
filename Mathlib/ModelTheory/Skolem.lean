/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module model_theory.skolem
! leanprover-community/mathlib commit 3d7987cda72abc473c7cdbbb075170e9ac620042
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.ModelTheory.ElementaryMaps

/-!
# Skolem Functions and Downward Löwenheim–Skolem

## Main Definitions
* `first_order.language.skolem₁` is a language consisting of Skolem functions for another language.

## Main Results
* `first_order.language.exists_elementary_substructure_card_eq` is the Downward Löwenheim–Skolem
  theorem: If `s` is a set in an `L`-structure `M` and `κ` an infinite cardinal such that
  `max (# s, L.card) ≤ κ` and `κ ≤ # M`, then `M` has an elementary substructure containing `s` of
  cardinality `κ`.

## TODO
* Use `skolem₁` recursively to construct an actual Skolemization of a language.

-/


universe u v w w'

namespace FirstOrder

namespace Language

open Structure Cardinal

open Cardinal

variable (L : Language.{u, v}) {M : Type w} [Nonempty M] [L.Structure M]

/-- A language consisting of Skolem functions for another language.
Called `skolem₁` because it is the first step in building a Skolemization of a language. -/
@[simps]
def skolem₁ : Language :=
  ⟨fun n => L.BoundedFormula Empty (n + 1), fun _ => Empty⟩
#align first_order.language.skolem₁ FirstOrder.Language.skolem₁

variable {L}

theorem card_functions_sum_skolem₁ :
    (#Σn, (L.Sum L.skolem₁).Functions n) = (#Σn, L.BoundedFormula Empty (n + 1)) :=
  by
  simp only [card_functions_sum, skolem₁_functions, lift_id', mk_sigma, sum_add_distrib']
  rw [add_comm, add_eq_max, max_eq_left]
  · refine' sum_le_sum _ _ fun n => _
    rw [← lift_le, lift_lift, lift_mk_le]
    refine' ⟨⟨fun f => (func f default).bdEqual (func f default), fun f g h => _⟩⟩
    rcases h with ⟨rfl, ⟨rfl⟩⟩
    rfl
  · rw [← mk_sigma]
    exact infinite_iff.1 (Infinite.of_injective (fun n => ⟨n, ⊥⟩) fun x y xy => (Sigma.mk.inj xy).1)
#align first_order.language.card_functions_sum_skolem₁ FirstOrder.Language.card_functions_sum_skolem₁

theorem card_functions_sum_skolem₁_le : (#Σn, (L.Sum L.skolem₁).Functions n) ≤ max ℵ₀ L.card :=
  by
  rw [card_functions_sum_skolem₁]
  trans #Σn, L.bounded_formula Empty n
  ·
    exact
      ⟨⟨Sigma.map Nat.succ fun _ => id,
          nat.succ_injective.sigma_map fun _ => Function.injective_id⟩⟩
  · refine' trans bounded_formula.card_le (lift_le.1 _)
    simp only [mk_empty, lift_zero, lift_uzero, zero_add]
#align first_order.language.card_functions_sum_skolem₁_le FirstOrder.Language.card_functions_sum_skolem₁_le

/-- The structure assigning each function symbol of `L.skolem₁` to a skolem function generated with
choice. -/
noncomputable instance skolem₁Structure : L.skolem₁.Structure M :=
  ⟨fun n φ x => Classical.epsilon fun a => φ.realize default (Fin.snoc x a : _ → M), fun _ r =>
    Empty.elim r⟩
#align first_order.language.skolem₁_Structure FirstOrder.Language.skolem₁Structure

namespace Substructure

theorem skolem₁_reduct_isElementary (S : (L.Sum L.skolem₁).Substructure M) :
    (LHom.sumInl.substructureReduct S).IsElementary :=
  by
  apply (Lhom.sum_inl.substructure_reduct S).is_elementary_of_exists
  intro n φ x a h
  let φ' : (L.sum L.skolem₁).Functions n := Lhom.sum_inr.on_function φ
  exact
    ⟨⟨fun_map φ' (coe ∘ x), S.fun_mem (Lhom.sum_inr.on_function φ) (coe ∘ x) fun i => (x i).2⟩,
      Classical.epsilon_spec ⟨a, h⟩⟩
#align first_order.language.substructure.skolem₁_reduct_is_elementary FirstOrder.Language.Substructure.skolem₁_reduct_isElementary

/-- Any `L.sum L.skolem₁`-substructure is an elementary `L`-substructure. -/
noncomputable def elementarySkolem₁Reduct (S : (L.Sum L.skolem₁).Substructure M) :
    L.ElementarySubstructure M :=
  ⟨LHom.sumInl.substructureReduct S, S.skolem₁_reduct_isElementary⟩
#align first_order.language.substructure.elementary_skolem₁_reduct FirstOrder.Language.Substructure.elementarySkolem₁Reduct

theorem coeSort_elementarySkolem₁Reduct (S : (L.Sum L.skolem₁).Substructure M) :
    (S.elementarySkolem₁Reduct : Type w) = S :=
  rfl
#align first_order.language.substructure.coe_sort_elementary_skolem₁_reduct FirstOrder.Language.Substructure.coeSort_elementarySkolem₁Reduct

end Substructure

open Substructure

variable (L) (M)

instance : Small (⊥ : (L.Sum L.skolem₁).Substructure M).elementarySkolem₁Reduct :=
  by
  rw [coe_sort_elementary_skolem₁_reduct]
  infer_instance

theorem exists_small_elementarySubstructure : ∃ S : L.ElementarySubstructure M, Small.{max u v} S :=
  ⟨Substructure.elementarySkolem₁Reduct ⊥, inferInstance⟩
#align first_order.language.exists_small_elementary_substructure FirstOrder.Language.exists_small_elementarySubstructure

variable {M}

/-- The Downward Löwenheim–Skolem theorem :
  If `s` is a set in an `L`-structure `M` and `κ` an infinite cardinal such that
  `max (# s, L.card) ≤ κ` and `κ ≤ # M`, then `M` has an elementary substructure containing `s` of
  cardinality `κ`.  -/
theorem exists_elementarySubstructure_card_eq (s : Set M) (κ : Cardinal.{w'}) (h1 : ℵ₀ ≤ κ)
    (h2 : Cardinal.lift.{w'} (#s) ≤ Cardinal.lift.{w} κ)
    (h3 : Cardinal.lift.{w'} L.card ≤ Cardinal.lift.{max u v} κ)
    (h4 : Cardinal.lift.{w} κ ≤ Cardinal.lift.{w'} (#M)) :
    ∃ S : L.ElementarySubstructure M, s ⊆ S ∧ Cardinal.lift.{w'} (#S) = Cardinal.lift.{w} κ :=
  by
  obtain ⟨s', hs'⟩ := Cardinal.le_mk_iff_exists_set.1 h4
  rw [← aleph_0_le_lift] at h1
  rw [← hs'] at *
  refine'
    ⟨elementary_skolem₁_reduct (closure (L.sum L.skolem₁) (s ∪ Equiv.ulift '' s')),
      (s.subset_union_left _).trans subset_closure, _⟩
  have h := mk_image_eq_lift _ s' equiv.ulift.injective
  rw [lift_umax, lift_id'] at h
  rw [coe_sort_elementary_skolem₁_reduct, ← h, lift_inj]
  refine'
    le_antisymm (lift_le.1 (lift_card_closure_le.trans _))
      (mk_le_mk_of_subset ((Set.subset_union_right _ _).trans subset_closure))
  rw [max_le_iff, aleph_0_le_lift, ← aleph_0_le_lift, h, add_eq_max, max_le_iff, lift_le]
  refine' ⟨h1, (mk_union_le _ _).trans _, (lift_le.2 card_functions_sum_skolem₁_le).trans _⟩
  · rw [← lift_le, lift_add, h, add_comm, add_eq_max h1]
    exact max_le le_rfl h2
  · rw [lift_max, lift_aleph_0, max_le_iff, aleph_0_le_lift, and_comm', ← lift_le.{_, w'},
      lift_lift, lift_lift, ← aleph_0_le_lift, h]
    refine' ⟨_, h1⟩
    simp only [← lift_lift, lift_umax, lift_umax']
    rw [lift_lift, ← lift_lift.{w', w} L.card]
    refine' trans (lift_le.{_, w}.2 h3) _
    rw [lift_lift, ← lift_lift.{w, max u v}, ← hs', ← h, lift_lift, lift_lift, lift_lift]
  · refine' trans _ (lift_le.2 (mk_le_mk_of_subset (Set.subset_union_right _ _)))
    rw [aleph_0_le_lift, ← aleph_0_le_lift, h]
    exact h1
#align first_order.language.exists_elementary_substructure_card_eq FirstOrder.Language.exists_elementarySubstructure_card_eq

end Language

end FirstOrder

