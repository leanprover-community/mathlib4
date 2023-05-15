/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module model_theory.types
! leanprover-community/mathlib commit 98bd247d933fb581ff37244a5998bd33d81dd46d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.ModelTheory.Satisfiability

/-!
# Type Spaces
This file defines the space of complete types over a first-order theory.
(Note that types in model theory are different from types in type theory.)

## Main Definitions
* `first_order.language.Theory.complete_type`:
  `T.complete_type α` consists of complete types over the theory `T` with variables `α`.
* `first_order.language.Theory.type_of` is the type of a given tuple.
* `first_order.language.Theory.realized_types`: `T.realized_types M α` is the set of
  types in `T.complete_type α` that are realized in `M` - that is, the type of some tuple in `M`.

## Main Results
* `first_order.language.Theory.complete_type.nonempty_iff`:
  The space `T.complete_type α` is nonempty exactly when `T` is satisfiable.
* `first_order.language.Theory.complete_type.exists_Model_is_realized_in`: Every type is realized in
some model.

## Implementation Notes
* Complete types are implemented as maximal consistent theories in an expanded language.
More frequently they are described as maximal consistent sets of formulas, but this is equivalent.

## TODO
* Connect `T.complete_type α` to sets of formulas `L.formula α`.

-/


universe u v w w'

open Cardinal Set

open Cardinal FirstOrder Classical

namespace FirstOrder

namespace Language

namespace Theory

variable {L : Language.{u, v}} (T : L.Theory) (α : Type w)

/-- A complete type over a given theory in a certain type of variables is a maximally
  consistent (with the theory) set of formulas in that type. -/
structure CompleteType where
  toTheory : L[[α]].Theory
  subset' : (L.lhomWithConstants α).onTheory T ⊆ to_Theory
  is_maximal' : to_Theory.IsMaximal
#align first_order.language.Theory.complete_type FirstOrder.Language.Theory.CompleteType

variable {T α}

namespace CompleteType

instance : SetLike (T.CompleteType α) L[[α]].Sentence :=
  ⟨fun p => p.toTheory, fun p q h => by
    cases p
    cases q
    congr ⟩

theorem isMaximal (p : T.CompleteType α) : IsMaximal (p : L[[α]].Theory) :=
  p.is_maximal'
#align first_order.language.Theory.complete_type.is_maximal FirstOrder.Language.Theory.CompleteType.isMaximal

theorem subset (p : T.CompleteType α) : (L.lhomWithConstants α).onTheory T ⊆ (p : L[[α]].Theory) :=
  p.subset'
#align first_order.language.Theory.complete_type.subset FirstOrder.Language.Theory.CompleteType.subset

theorem mem_or_not_mem (p : T.CompleteType α) (φ : L[[α]].Sentence) : φ ∈ p ∨ φ.Not ∈ p :=
  p.IsMaximal.mem_or_not_mem φ
#align first_order.language.Theory.complete_type.mem_or_not_mem FirstOrder.Language.Theory.CompleteType.mem_or_not_mem

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mem_of_models (p : T.CompleteType α) {φ : L[[α]].Sentence}
    (h : (L.lhomWithConstants α).onTheory T ⊨ φ) : φ ∈ p :=
  (p.mem_or_not_mem φ).resolve_right fun con =>
    ((models_iff_not_satisfiable _).1 h)
      (p.IsMaximal.1.mono (union_subset p.Subset (singleton_subset_iff.2 Con)))
#align first_order.language.Theory.complete_type.mem_of_models FirstOrder.Language.Theory.CompleteType.mem_of_models

theorem not_mem_iff (p : T.CompleteType α) (φ : L[[α]].Sentence) : φ.Not ∈ p ↔ ¬φ ∈ p :=
  ⟨fun hf ht =>
    by
    have h : ¬is_satisfiable ({φ, φ.not} : L[[α]].Theory) :=
      by
      rintro ⟨@⟨_, _, h, _⟩⟩
      simp only [model_iff, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq] at h
      exact h.2 h.1
    refine' h (p.is_maximal.1.mono _)
    rw [insert_subset, singleton_subset_iff]
    exact ⟨ht, hf⟩, (p.mem_or_not_mem φ).resolve_left⟩
#align first_order.language.Theory.complete_type.not_mem_iff FirstOrder.Language.Theory.CompleteType.not_mem_iff

@[simp]
theorem compl_setOf_mem {φ : L[[α]].Sentence} :
    { p : T.CompleteType α | φ ∈ p }ᶜ = { p : T.CompleteType α | φ.Not ∈ p } :=
  ext fun _ => (not_mem_iff _ _).symm
#align first_order.language.Theory.complete_type.compl_set_of_mem FirstOrder.Language.Theory.CompleteType.compl_setOf_mem

theorem setOf_subset_eq_empty_iff (S : L[[α]].Theory) :
    { p : T.CompleteType α | S ⊆ ↑p } = ∅ ↔
      ¬((L.lhomWithConstants α).onTheory T ∪ S).IsSatisfiable :=
  by
  rw [iff_not_comm, ← not_nonempty_iff_eq_empty, Classical.not_not, Set.Nonempty]
  refine'
    ⟨fun h =>
      ⟨⟨L[[α]].completeTheory h.some, (subset_union_left _ S).trans complete_theory.subset,
          complete_theory.is_maximal _ _⟩,
        (subset_union_right ((L.Lhom_with_constants α).onTheory T) _).trans complete_theory.subset⟩,
      _⟩
  rintro ⟨p, hp⟩
  exact p.is_maximal.1.mono (union_subset p.subset hp)
#align first_order.language.Theory.complete_type.set_of_subset_eq_empty_iff FirstOrder.Language.Theory.CompleteType.setOf_subset_eq_empty_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem setOf_mem_eq_univ_iff (φ : L[[α]].Sentence) :
    { p : T.CompleteType α | φ ∈ p } = univ ↔ (L.lhomWithConstants α).onTheory T ⊨ φ :=
  by
  rw [models_iff_not_satisfiable, ← compl_empty_iff, compl_set_of_mem, ← set_of_subset_eq_empty_iff]
  simp
#align first_order.language.Theory.complete_type.set_of_mem_eq_univ_iff FirstOrder.Language.Theory.CompleteType.setOf_mem_eq_univ_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem setOf_subset_eq_univ_iff (S : L[[α]].Theory) :
    { p : T.CompleteType α | S ⊆ ↑p } = univ ↔
      ∀ φ, φ ∈ S → (L.lhomWithConstants α).onTheory T ⊨ φ :=
  by
  have h : { p : T.complete_type α | S ⊆ ↑p } = ⋂₀ ((fun φ => { p | φ ∈ p }) '' S) :=
    by
    ext
    simp [subset_def]
  simp_rw [h, sInter_eq_univ, ← set_of_mem_eq_univ_iff]
  refine' ⟨fun h φ φS => h _ ⟨_, φS, rfl⟩, _⟩
  rintro h _ ⟨φ, h1, rfl⟩
  exact h _ h1
#align first_order.language.Theory.complete_type.set_of_subset_eq_univ_iff FirstOrder.Language.Theory.CompleteType.setOf_subset_eq_univ_iff

theorem nonempty_iff : Nonempty (T.CompleteType α) ↔ T.IsSatisfiable :=
  by
  rw [← is_satisfiable_on_Theory_iff (Lhom_with_constants_injective L α)]
  rw [nonempty_iff_univ_nonempty, nonempty_iff_ne_empty, Ne.def, not_iff_comm, ←
    union_empty ((L.Lhom_with_constants α).onTheory T), ← set_of_subset_eq_empty_iff]
  simp
#align first_order.language.Theory.complete_type.nonempty_iff FirstOrder.Language.Theory.CompleteType.nonempty_iff

instance : Nonempty (CompleteType ∅ α) :=
  nonempty_iff.2 (isSatisfiable_empty L)

theorem iInter_setOf_subset {ι : Type _} (S : ι → L[[α]].Theory) :
    (⋂ i : ι, { p : T.CompleteType α | S i ⊆ p }) = { p | (⋃ i : ι, S i) ⊆ p } :=
  by
  ext
  simp only [mem_Inter, mem_set_of_eq, Union_subset_iff]
#align first_order.language.Theory.complete_type.Inter_set_of_subset FirstOrder.Language.Theory.CompleteType.iInter_setOf_subset

theorem toList_foldr_inf_mem {p : T.CompleteType α} {t : Finset L[[α]].Sentence} :
    t.toList.foldr (· ⊓ ·) ⊤ ∈ p ↔ (t : L[[α]].Theory) ⊆ ↑p :=
  by
  simp_rw [subset_def, ← SetLike.mem_coe, p.is_maximal.mem_iff_models, models_sentence_iff,
    sentence.realize, formula.realize, bounded_formula.realize_foldr_inf, Finset.mem_toList]
  exact ⟨fun h φ hφ M => h _ _ hφ, fun h M φ hφ => h _ hφ _⟩
#align first_order.language.Theory.complete_type.to_list_foldr_inf_mem FirstOrder.Language.Theory.CompleteType.toList_foldr_inf_mem

end CompleteType

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
variable {M : Type w'} [L.Structure M] [Nonempty M] [M ⊨ T] (T)

/-- The set of all formulas true at a tuple in a structure forms a complete type. -/
def typeOf (v : α → M) : T.CompleteType α :=
  haveI : (constants_on α).Structure M := constants_on.Structure v
  { toTheory := L[[α]].completeTheory M
    subset' := model_iff_subset_complete_theory.1 ((Lhom.on_Theory_model _ T).2 inferInstance)
    is_maximal' := complete_theory.is_maximal _ _ }
#align first_order.language.Theory.type_of FirstOrder.Language.Theory.typeOf

namespace CompleteType

variable {T} {v : α → M}

@[simp]
theorem mem_typeOf {φ : L[[α]].Sentence} :
    φ ∈ T.typeOf v ↔ (Formula.equivSentence.symm φ).realize v :=
  letI : (constants_on α).Structure M := constants_on.Structure v
  mem_complete_theory.trans (formula.realize_equiv_sentence_symm _ _ _).symm
#align first_order.language.Theory.complete_type.mem_type_of FirstOrder.Language.Theory.CompleteType.mem_typeOf

theorem formula_mem_typeOf {φ : L.Formula α} : Formula.equivSentence φ ∈ T.typeOf v ↔ φ.realize v :=
  by simp
#align first_order.language.Theory.complete_type.formula_mem_type_of FirstOrder.Language.Theory.CompleteType.formula_mem_typeOf

end CompleteType

variable (M)

/-- A complete type `p` is realized in a particular structure when there is some
  tuple `v` whose type is `p`. -/
@[simp]
def realizedTypes (α : Type w) : Set (T.CompleteType α) :=
  Set.range (T.typeOf : (α → M) → T.CompleteType α)
#align first_order.language.Theory.realized_types FirstOrder.Language.Theory.realizedTypes

theorem exists_modelType_is_realized_in (p : T.CompleteType α) :
    ∃ M : Theory.ModelType.{u, v, max u v w} T, p ∈ T.realizedTypes M α :=
  by
  obtain ⟨M⟩ := p.is_maximal.1
  refine' ⟨(M.subtheory_Model p.subset).reduct (L.Lhom_with_constants α), fun a => (L.con a : M), _⟩
  refine' SetLike.ext fun φ => _
  simp only [complete_type.mem_type_of]
  refine'
    (formula.realize_equiv_sentence_symm_con _ _).trans
      (trans (trans _ (p.is_maximal.is_complete.realize_sentence_iff φ M))
        (p.is_maximal.mem_iff_models φ).symm)
  rfl
#align first_order.language.Theory.exists_Model_is_realized_in FirstOrder.Language.Theory.exists_modelType_is_realized_in

end Theory

end Language

end FirstOrder

