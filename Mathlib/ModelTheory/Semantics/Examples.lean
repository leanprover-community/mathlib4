/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Mathlib.ModelTheory.Semantics.Formula
import Mathlib.ModelTheory.Syntax.Examples

/-!
# Basics on First-Order Semantics
This file defines the interpretations of first-order terms, formulas, sentences, and theories
in a style inspired by the [Flypitch project](https://flypitch.github.io/).

## Main Definitions

## Main Results

## Implementation Notes

## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/


universe u v w u' v'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {L' : Language}
variable {M : Type w} {N P : Type*} [L.Structure M] [L.Structure N] [L.Structure P] [Nonempty M]
variable {α : Type u'} {β : Type v'} {γ : Type*} {n : ℕ}
variable {T : L.Theory}

open FirstOrder Cardinal

open Structure Cardinal Fin

namespace Relations

open BoundedFormula

variable {r : L.Relations 2}

@[simp]
theorem realize_reflexive : M ⊨ r.reflexive ↔ Reflexive fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ => realize_rel₂

@[simp]
theorem realize_irreflexive : M ⊨ r.irreflexive ↔ Irreflexive fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ => not_congr realize_rel₂

@[simp]
theorem realize_symmetric : M ⊨ r.symmetric ↔ Symmetric fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ => forall_congr' fun _ => imp_congr realize_rel₂ realize_rel₂

@[simp]
theorem realize_antisymmetric :
    M ⊨ r.antisymmetric ↔ AntiSymmetric fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ =>
    forall_congr' fun _ => imp_congr realize_rel₂ (imp_congr realize_rel₂ Iff.rfl)

@[simp]
theorem realize_transitive : M ⊨ r.transitive ↔ Transitive fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ =>
    forall_congr' fun _ =>
      forall_congr' fun _ => imp_congr realize_rel₂ (imp_congr realize_rel₂ realize_rel₂)

@[simp]
theorem realize_total : M ⊨ r.total ↔ Total fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ =>
    forall_congr' fun _ => realize_sup.trans (or_congr realize_rel₂ realize_rel₂)

end Relations

section Cardinality

variable (L)
@[simp]
theorem Sentence.realize_cardGe (n) : M ⊨ Sentence.cardGe L n ↔ ↑n ≤ #M := by
  rw [← lift_mk_fin, ← lift_le.{0}, lift_lift, lift_mk_le, Sentence.cardGe, Sentence.Realize,
    BoundedFormula.realize_exs]
  simp_rw [BoundedFormula.realize_foldr_inf]
  simp only [Function.comp_apply, List.mem_map, Prod.exists, Ne, List.mem_product,
    List.mem_finRange, forall_exists_index, and_imp, List.mem_filter, true_and_iff]
  refine ⟨?_, fun xs => ⟨xs.some, ?_⟩⟩
  · rintro ⟨xs, h⟩
    refine ⟨⟨xs, fun i j ij => ?_⟩⟩
    contrapose! ij
    have hij := h _ i j (by simpa using ij) rfl
    simp only [BoundedFormula.realize_not, Term.realize, BoundedFormula.realize_bdEqual,
      Sum.elim_inr] at hij
    exact hij
  · rintro _ i j ij rfl
    simpa using ij

@[simp]
theorem model_infiniteTheory_iff : M ⊨ L.infiniteTheory ↔ Infinite M := by
  simp [infiniteTheory, infinite_iff, aleph0_le]

instance model_infiniteTheory [h : Infinite M] : M ⊨ L.infiniteTheory :=
  L.model_infiniteTheory_iff.2 h

@[simp]
theorem model_nonemptyTheory_iff : M ⊨ L.nonemptyTheory ↔ Nonempty M := by
  simp only [nonemptyTheory, Theory.model_iff, Set.mem_singleton_iff, forall_eq,
    Sentence.realize_cardGe, Nat.cast_one, one_le_iff_ne_zero, mk_ne_zero_iff]

instance model_nonempty [h : Nonempty M] : M ⊨ L.nonemptyTheory :=
  L.model_nonemptyTheory_iff.2 h

theorem model_distinctConstantsTheory {M : Type w} [L[[α]].Structure M] (s : Set α) :
    M ⊨ L.distinctConstantsTheory s ↔ Set.InjOn (fun i : α => (L.con i : M)) s := by
  simp only [distinctConstantsTheory, Theory.model_iff, Set.mem_image, Set.mem_inter,
    Set.mem_prod, Set.mem_compl, Prod.exists, forall_exists_index, and_imp]
  refine ⟨fun h a as b bs ab => ?_, ?_⟩
  · contrapose! ab
    have h' := h _ a b ⟨⟨as, bs⟩, ab⟩ rfl
    simp only [Sentence.Realize, Formula.realize_not, Formula.realize_equal,
      Term.realize_constants] at h'
    exact h'
  · rintro h φ a b ⟨⟨as, bs⟩, ab⟩ rfl
    simp only [Sentence.Realize, Formula.realize_not, Formula.realize_equal, Term.realize_constants]
    exact fun contra => ab (h as bs contra)

theorem card_le_of_model_distinctConstantsTheory (s : Set α) (M : Type w) [L[[α]].Structure M]
    [h : M ⊨ L.distinctConstantsTheory s] : Cardinal.lift.{w} #s ≤ Cardinal.lift.{u'} #M :=
  lift_mk_le'.2 ⟨⟨_, Set.injOn_iff_injective.1 ((L.model_distinctConstantsTheory s).1 h)⟩⟩

end Cardinality

namespace ElementarilyEquivalent

theorem nonempty_iff (h : M ≅[L] N) : Nonempty M ↔ Nonempty N :=
  (model_nonemptyTheory_iff L).symm.trans (h.theory_model_iff.trans (model_nonemptyTheory_iff L))

theorem nonempty [Mn : Nonempty M] (h : M ≅[L] N) : Nonempty N :=
  h.nonempty_iff.1 Mn

theorem infinite_iff (h : M ≅[L] N) : Infinite M ↔ Infinite N :=
  (model_infiniteTheory_iff L).symm.trans (h.theory_model_iff.trans (model_infiniteTheory_iff L))

theorem infinite [Mi : Infinite M] (h : M ≅[L] N) : Infinite N :=
  h.infinite_iff.1 Mi

end ElementarilyEquivalent

end Language

end FirstOrder
