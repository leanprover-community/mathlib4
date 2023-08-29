/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.ModelTheory.ElementaryMaps

#align_import model_theory.skolem from "leanprover-community/mathlib"@"3d7987cda72abc473c7cdbbb075170e9ac620042"

/-!
# Skolem Functions and Downward Löwenheim–Skolem

## Main Definitions
* `FirstOrder.Language.skolem₁` is a language consisting of Skolem functions for another language.

## Main Results
* `FirstOrder.Language.exists_elementarySubstructure_card_eq` is the Downward Löwenheim–Skolem
  theorem: If `s` is a set in an `L`-structure `M` and `κ` an infinite cardinal such that
  `max (#s, L.card) ≤ κ` and `κ ≤ # M`, then `M` has an elementary substructure containing `s` of
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
#align first_order.language.skolem₁_functions FirstOrder.Language.skolem₁_Functions

variable {L}

theorem card_functions_sum_skolem₁ :
    #(Σ n, (L.sum L.skolem₁).Functions n) = #(Σ n, L.BoundedFormula Empty (n + 1)) := by
  simp only [card_functions_sum, skolem₁_Functions, mk_sigma, sum_add_distrib']
  -- ⊢ ((sum fun i => lift.{max u v, u} #(Functions L i)) + sum fun i => lift.{u, m …
  conv_lhs => enter [2, 1, i]; rw [lift_id'.{u, v}]
  -- ⊢ ((sum fun i => lift.{max u v, u} #(Functions L i)) + sum fun i => #(BoundedF …
  rw [add_comm, add_eq_max, max_eq_left]
  -- ⊢ (sum fun i => lift.{max u v, u} #(Functions L i)) ≤ sum fun i => #(BoundedFo …
  · refine' sum_le_sum _ _ fun n => _
    -- ⊢ lift.{max u v, u} #(Functions L n) ≤ #(BoundedFormula L Empty (n + 1))
    rw [← lift_le.{_, max u v}, lift_lift, lift_mk_le.{v}]
    -- ⊢ Nonempty (Functions L n ↪ BoundedFormula L Empty (n + 1))
    refine' ⟨⟨fun f => (func f default).bdEqual (func f default), fun f g h => _⟩⟩
    -- ⊢ f = g
    rcases h with ⟨rfl, ⟨rfl⟩⟩
    -- ⊢ f = f
    rfl
    -- 🎉 no goals
  · rw [← mk_sigma]
    -- ⊢ ℵ₀ ≤ #((i : ℕ) × BoundedFormula L Empty (i + 1))
    exact infinite_iff.1 (Infinite.of_injective (fun n => ⟨n, ⊥⟩) fun x y xy =>
      (Sigma.mk.inj_iff.1 xy).1)
#align first_order.language.card_functions_sum_skolem₁ FirstOrder.Language.card_functions_sum_skolem₁

theorem card_functions_sum_skolem₁_le : #(Σ n, (L.sum L.skolem₁).Functions n) ≤ max ℵ₀ L.card := by
  rw [card_functions_sum_skolem₁]
  -- ⊢ #((n : ℕ) × BoundedFormula L Empty (n + 1)) ≤ max ℵ₀ (card L)
  trans #(Σ n, L.BoundedFormula Empty n)
  -- ⊢ #((n : ℕ) × BoundedFormula L Empty (n + 1)) ≤ #((n : ℕ) × BoundedFormula L E …
  · exact
      ⟨⟨Sigma.map Nat.succ fun _ => id,
          Nat.succ_injective.sigma_map fun _ => Function.injective_id⟩⟩
  · refine' _root_.trans BoundedFormula.card_le (lift_le.{max u v}.1 _)
    -- ⊢ lift.{max u v, max u v} (max ℵ₀ (lift.{max u v, 0} #Empty + lift.{0, max u v …
    simp only [mk_empty, lift_zero, lift_uzero, zero_add]
    -- ⊢ lift.{max u v, max u v} (max ℵ₀ (card L)) ≤ lift.{max u v, max u v} (max ℵ₀  …
    rfl
    -- 🎉 no goals
#align first_order.language.card_functions_sum_skolem₁_le FirstOrder.Language.card_functions_sum_skolem₁_le

/-- The structure assigning each function symbol of `L.skolem₁` to a skolem function generated with
choice. -/
noncomputable instance skolem₁Structure : L.skolem₁.Structure M :=
  ⟨fun {_} φ x => Classical.epsilon fun a => φ.Realize default (Fin.snoc x a : _ → M), fun {_} r =>
    Empty.elim r⟩
set_option linter.uppercaseLean3 false in
#align first_order.language.skolem₁_Structure FirstOrder.Language.skolem₁Structure

namespace Substructure

theorem skolem₁_reduct_isElementary (S : (L.sum L.skolem₁).Substructure M) :
    (LHom.sumInl.substructureReduct S).IsElementary := by
  apply (LHom.sumInl.substructureReduct S).isElementary_of_exists
  -- ⊢ ∀ (n : ℕ) (φ : BoundedFormula L Empty (n + 1)) (x : Fin n → { x // x ∈ ↑(LHo …
  intro n φ x a h
  -- ⊢ ∃ b, BoundedFormula.Realize φ default (Fin.snoc (Subtype.val ∘ x) ↑b)
  let φ' : (L.sum L.skolem₁).Functions n := LHom.sumInr.onFunction φ
  -- ⊢ ∃ b, BoundedFormula.Realize φ default (Fin.snoc (Subtype.val ∘ x) ↑b)
  exact
    ⟨⟨funMap φ' ((↑) ∘ x), S.fun_mem (LHom.sumInr.onFunction φ) ((↑) ∘ x) (by
      exact fun i => (x i).2)⟩,
      by exact Classical.epsilon_spec (p := fun a => BoundedFormula.Realize φ default
          (Fin.snoc (Subtype.val ∘ x) a)) ⟨a, h⟩⟩
#align first_order.language.substructure.skolem₁_reduct_is_elementary FirstOrder.Language.Substructure.skolem₁_reduct_isElementary

/-- Any `L.sum L.skolem₁`-substructure is an elementary `L`-substructure. -/
noncomputable def elementarySkolem₁Reduct (S : (L.sum L.skolem₁).Substructure M) :
    L.ElementarySubstructure M :=
  ⟨LHom.sumInl.substructureReduct S, S.skolem₁_reduct_isElementary⟩
#align first_order.language.substructure.elementary_skolem₁_reduct FirstOrder.Language.Substructure.elementarySkolem₁Reduct

theorem coeSort_elementarySkolem₁Reduct (S : (L.sum L.skolem₁).Substructure M) :
    (S.elementarySkolem₁Reduct : Type w) = S :=
  rfl
#align first_order.language.substructure.coe_sort_elementary_skolem₁_reduct FirstOrder.Language.Substructure.coeSort_elementarySkolem₁Reduct

end Substructure

open Substructure

variable (L) (M)

instance Substructure.elementarySkolem₁Reduct.instSmall :
    Small (⊥ : (L.sum L.skolem₁).Substructure M).elementarySkolem₁Reduct := by
  rw [coeSort_elementarySkolem₁Reduct]
  -- ⊢ Small.{?u.38339, w} { x // x ∈ ⊥ }
  infer_instance
  -- 🎉 no goals
#align first_order.language.elementary_skolem₁_reduct.small FirstOrder.Language.Substructure.elementarySkolem₁Reduct.instSmall

theorem exists_small_elementarySubstructure : ∃ S : L.ElementarySubstructure M, Small.{max u v} S :=
  ⟨Substructure.elementarySkolem₁Reduct ⊥, inferInstance⟩
#align first_order.language.exists_small_elementary_substructure FirstOrder.Language.exists_small_elementarySubstructure

variable {M}

/-- The Downward Löwenheim–Skolem theorem :
  If `s` is a set in an `L`-structure `M` and `κ` an infinite cardinal such that
  `max (#s, L.card) ≤ κ` and `κ ≤ # M`, then `M` has an elementary substructure containing `s` of
  cardinality `κ`.  -/
theorem exists_elementarySubstructure_card_eq (s : Set M) (κ : Cardinal.{w'}) (h1 : ℵ₀ ≤ κ)
    (h2 : Cardinal.lift.{w'} #s ≤ Cardinal.lift.{w} κ)
    (h3 : Cardinal.lift.{w'} L.card ≤ Cardinal.lift.{max u v} κ)
    (h4 : Cardinal.lift.{w} κ ≤ Cardinal.lift.{w'} #M) :
    ∃ S : L.ElementarySubstructure M, s ⊆ S ∧ Cardinal.lift.{w'} #S = Cardinal.lift.{w} κ := by
  obtain ⟨s', hs'⟩ := Cardinal.le_mk_iff_exists_set.1 h4
  -- ⊢ ∃ S, s ⊆ ↑S ∧ lift.{w', w} #{ x // x ∈ S } = lift.{w, w'} κ
  rw [← aleph0_le_lift.{_, w}] at h1
  -- ⊢ ∃ S, s ⊆ ↑S ∧ lift.{w', w} #{ x // x ∈ S } = lift.{w, w'} κ
  rw [← hs'] at h1 h2 ⊢
  -- ⊢ ∃ S, s ⊆ ↑S ∧ lift.{w', w} #{ x // x ∈ S } = #↑s'
  refine'
    ⟨elementarySkolem₁Reduct (closure (L.sum L.skolem₁) (s ∪ Equiv.ulift '' s')),
      (s.subset_union_left _).trans subset_closure, _⟩
  have h := mk_image_eq_lift _ s' Equiv.ulift.injective
  -- ⊢ lift.{w', w} #{ x // x ∈ elementarySkolem₁Reduct (LowerAdjoint.toFun (closur …
  rw [lift_umax.{w, w'}, lift_id'.{w, w'}] at h
  -- ⊢ lift.{w', w} #{ x // x ∈ elementarySkolem₁Reduct (LowerAdjoint.toFun (closur …
  rw [coeSort_elementarySkolem₁Reduct, ← h, lift_inj]
  -- ⊢ #{ x // x ∈ LowerAdjoint.toFun (closure (Language.sum L (skolem₁ L))) (s ∪ ↑ …
  refine'
    le_antisymm (lift_le.1 (lift_card_closure_le.trans _))
      (mk_le_mk_of_subset ((Set.subset_union_right _ _).trans subset_closure))
  rw [max_le_iff, aleph0_le_lift, ← aleph0_le_lift.{_, w'}, h, add_eq_max, max_le_iff, lift_le]
  -- ⊢ ℵ₀ ≤ #↑s' ∧ #↑(s ∪ ↑Equiv.ulift '' s') ≤ #↑(↑Equiv.ulift '' s') ∧ lift.{w, m …
  refine' ⟨h1, (mk_union_le _ _).trans _, (lift_le.2 card_functions_sum_skolem₁_le).trans _⟩
  · rw [← lift_le, lift_add, h, add_comm, add_eq_max h1]
    -- ⊢ max (#↑s') (lift.{w', w} #↑s) ≤ #↑s'
    exact max_le le_rfl h2
    -- 🎉 no goals
  · rw [lift_max, lift_aleph0, max_le_iff, aleph0_le_lift, and_comm, ← lift_le.{w'},
      lift_lift, lift_lift, ← aleph0_le_lift, h]
    refine' ⟨_, h1⟩
    -- ⊢ lift.{max w w', max u v} (card L) ≤ lift.{max (max u v) w', w} #↑(↑Equiv.uli …
    rw [← lift_lift.{w', w}]
    -- ⊢ lift.{w, max w' u v} (lift.{w', max u v} (card L)) ≤ lift.{max (max u v) w', …
    refine' _root_.trans (lift_le.{w}.2 h3) _
    -- ⊢ lift.{w, max (max u v) w'} (lift.{max u v, w'} κ) ≤ lift.{max (max u v) w',  …
    rw [lift_lift, ← lift_lift.{w, max u v}, ← hs', ← h, lift_lift]
    -- 🎉 no goals
  · refine' _root_.trans _ (lift_le.2 (mk_le_mk_of_subset (Set.subset_union_right _ _)))
    -- ⊢ ℵ₀ ≤ lift.{max u v, w} #↑(↑Equiv.ulift '' s')
    rw [aleph0_le_lift, ← aleph0_le_lift, h]
    -- ⊢ ℵ₀ ≤ #↑s'
    exact h1
    -- 🎉 no goals
#align first_order.language.exists_elementary_substructure_card_eq FirstOrder.Language.exists_elementarySubstructure_card_eq

end Language

end FirstOrder
