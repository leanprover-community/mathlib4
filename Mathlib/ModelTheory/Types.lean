/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.ModelTheory.Satisfiability

/-!
# Type Spaces

This file defines the space of complete types over a first-order theory.
(Note that types in model theory are different from types in type theory.)

## Main Definitions

- `FirstOrder.Language.Theory.CompleteType`:
  `T.CompleteType α` consists of complete types over the theory `T` with variables `α`.
- `FirstOrder.Language.Theory.typeOf` is the type of a given tuple.
- `FirstOrder.Language.Theory.realizedTypes`: `T.realizedTypes M α` is the set of
  types in `T.CompleteType α` that are realized in `M` - that is, the type of some tuple in `M`.

## Main Results

- `FirstOrder.Language.Theory.CompleteType.nonempty_iff`:
  The space `T.CompleteType α` is nonempty exactly when `T` is satisfiable.
- `FirstOrder.Language.Theory.CompleteType.exists_modelType_is_realized_in`: Every type is realized
  in some model.

## Implementation Notes

- Complete types are implemented as maximal consistent theories in an expanded language.
  More frequently they are described as maximal consistent sets of formulas, but this is equivalent.

## TODO

- Connect `T.CompleteType α` to sets of formulas `L.Formula α`.
-/



universe u v w w'

open Cardinal Set FirstOrder

namespace FirstOrder

namespace Language

namespace Theory

variable {L : Language.{u, v}} (T : L.Theory) (α : Type w)

/-- A complete type over a given theory in a certain type of variables is a maximally
  consistent (with the theory) set of formulas in that type. -/
structure CompleteType where
  /-- The underlying theory -/
  toTheory : L[[α]].Theory
  subset' : (L.lhomWithConstants α).onTheory T ⊆ toTheory
  isMaximal' : toTheory.IsMaximal

variable {T α}

namespace CompleteType

attribute [coe] CompleteType.toTheory

instance Sentence.instSetLike : SetLike (T.CompleteType α) (L[[α]].Sentence) :=
  ⟨fun p => p.toTheory, fun p q h => by
    cases p
    cases q
    congr ⟩

theorem isMaximal (p : T.CompleteType α) : IsMaximal (p : L[[α]].Theory) :=
  p.isMaximal'

theorem subset (p : T.CompleteType α) : (L.lhomWithConstants α).onTheory T ⊆ (p : L[[α]].Theory) :=
  p.subset'

theorem mem_or_not_mem (p : T.CompleteType α) (φ : L[[α]].Sentence) : φ ∈ p ∨ φ.not ∈ p :=
  p.isMaximal.mem_or_not_mem φ

theorem mem_of_models (p : T.CompleteType α) {φ : L[[α]].Sentence}
    (h : (L.lhomWithConstants α).onTheory T ⊨ᵇ φ) : φ ∈ p :=
  (p.mem_or_not_mem φ).resolve_right fun con =>
    ((models_iff_not_satisfiable _).1 h)
      (p.isMaximal.1.mono (union_subset p.subset (singleton_subset_iff.2 con)))

theorem not_mem_iff (p : T.CompleteType α) (φ : L[[α]].Sentence) : φ.not ∈ p ↔ φ ∉ p :=
  ⟨fun hf ht => by
    have h : ¬IsSatisfiable ({φ, φ.not} : L[[α]].Theory) := by
      rintro ⟨@⟨_, _, h, _⟩⟩
      simp only [model_iff, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq] at h
      exact h.2 h.1
    refine h (p.isMaximal.1.mono ?_)
    rw [insert_subset_iff, singleton_subset_iff]
    exact ⟨ht, hf⟩, (p.mem_or_not_mem φ).resolve_left⟩

@[simp]
theorem compl_setOf_mem {φ : L[[α]].Sentence} :
    { p : T.CompleteType α | φ ∈ p }ᶜ = { p : T.CompleteType α | φ.not ∈ p } :=
  ext fun _ => (not_mem_iff _ _).symm

theorem setOf_subset_eq_empty_iff (S : L[[α]].Theory) :
    { p : T.CompleteType α | S ⊆ ↑p } = ∅ ↔
      ¬((L.lhomWithConstants α).onTheory T ∪ S).IsSatisfiable := by
  rw [iff_not_comm, ← not_nonempty_iff_eq_empty, Classical.not_not, Set.Nonempty]
  refine
    ⟨fun h =>
      ⟨⟨L[[α]].completeTheory h.some, (subset_union_left (t := S)).trans completeTheory.subset,
          completeTheory.isMaximal (L[[α]]) h.some⟩,
        (((L.lhomWithConstants α).onTheory T).subset_union_right).trans completeTheory.subset⟩,
      ?_⟩
  rintro ⟨p, hp⟩
  exact p.isMaximal.1.mono (union_subset p.subset hp)

theorem setOf_mem_eq_univ_iff (φ : L[[α]].Sentence) :
    { p : T.CompleteType α | φ ∈ p } = Set.univ ↔ (L.lhomWithConstants α).onTheory T ⊨ᵇ φ := by
  rw [models_iff_not_satisfiable, ← compl_empty_iff, compl_setOf_mem, ← setOf_subset_eq_empty_iff]
  simp

theorem setOf_subset_eq_univ_iff (S : L[[α]].Theory) :
    { p : T.CompleteType α | S ⊆ ↑p } = Set.univ ↔
      ∀ φ, φ ∈ S → (L.lhomWithConstants α).onTheory T ⊨ᵇ φ := by
  have h : { p : T.CompleteType α | S ⊆ ↑p } = ⋂₀ ((fun φ => { p | φ ∈ p }) '' S) := by
    ext
    simp [subset_def]
  simp_rw [h, sInter_eq_univ, ← setOf_mem_eq_univ_iff]
  refine ⟨fun h φ φS => h _ ⟨_, φS, rfl⟩, ?_⟩
  rintro h _ ⟨φ, h1, rfl⟩
  exact h _ h1

theorem nonempty_iff : Nonempty (T.CompleteType α) ↔ T.IsSatisfiable := by
  rw [← isSatisfiable_onTheory_iff (lhomWithConstants_injective L α)]
  rw [nonempty_iff_univ_nonempty, nonempty_iff_ne_empty, Ne, not_iff_comm,
    ← union_empty ((L.lhomWithConstants α).onTheory T), ← setOf_subset_eq_empty_iff]
  simp

instance instNonempty : Nonempty (CompleteType (∅ : L.Theory) α) :=
  nonempty_iff.2 (isSatisfiable_empty L)

theorem iInter_setOf_subset {ι : Type*} (S : ι → L[[α]].Theory) :
    ⋂ i : ι, { p : T.CompleteType α | S i ⊆ p } =
      { p : T.CompleteType α | ⋃ i : ι, S i ⊆ p } := by
  ext
  simp only [mem_iInter, mem_setOf_eq, iUnion_subset_iff]

theorem toList_foldr_inf_mem {p : T.CompleteType α} {t : Finset (L[[α]]).Sentence} :
    t.toList.foldr (· ⊓ ·) ⊤ ∈ p ↔ (t : L[[α]].Theory) ⊆ ↑p := by
  simp_rw [subset_def, ← SetLike.mem_coe, p.isMaximal.mem_iff_models, models_sentence_iff,
    Sentence.Realize, Formula.Realize, BoundedFormula.realize_foldr_inf, Finset.mem_toList]
  exact ⟨fun h φ hφ M => h _ _ hφ, fun h M φ hφ => h _ hφ _⟩

end CompleteType

variable {M : Type w'} [L.Structure M] [Nonempty M] [M ⊨ T] (T)

/-- The set of all formulas true at a tuple in a structure forms a complete type. -/
def typeOf (v : α → M) : T.CompleteType α :=
  haveI : (constantsOn α).Structure M := constantsOn.structure v
  { toTheory := L[[α]].completeTheory M
    subset' := model_iff_subset_completeTheory.1 ((LHom.onTheory_model _ T).2 inferInstance)
    isMaximal' := completeTheory.isMaximal _ _ }

namespace CompleteType

variable {T} {v : α → M}

@[simp]
theorem mem_typeOf {φ : L[[α]].Sentence} :
    φ ∈ T.typeOf v ↔ (Formula.equivSentence.symm φ).Realize v :=
  letI : (constantsOn α).Structure M := constantsOn.structure v
  mem_completeTheory.trans (Formula.realize_equivSentence_symm _ _ _).symm

theorem formula_mem_typeOf {φ : L.Formula α} :
    Formula.equivSentence φ ∈ T.typeOf v ↔ φ.Realize v := by simp

end CompleteType

variable (M)

/-- A complete type `p` is realized in a particular structure when there is some
  tuple `v` whose type is `p`. -/
@[simp]
def realizedTypes (α : Type w) : Set (T.CompleteType α) :=
  Set.range (T.typeOf : (α → M) → T.CompleteType α)

section

theorem exists_modelType_is_realized_in (p : T.CompleteType α) :
    ∃ M : Theory.ModelType.{u, v, max u v w} T, p ∈ T.realizedTypes M α := by
  obtain ⟨M⟩ := p.isMaximal.1
  refine ⟨(M.subtheoryModel p.subset).reduct (L.lhomWithConstants α), fun a => (L.con a : M), ?_⟩
  refine SetLike.ext fun φ => ?_
  simp only [CompleteType.mem_typeOf]
  refine
    (@Formula.realize_equivSentence_symm_con _
      ((M.subtheoryModel p.subset).reduct (L.lhomWithConstants α)) _ _ M.struc _ φ).trans
      (_root_.trans (_root_.trans ?_ (p.isMaximal.isComplete.realize_sentence_iff φ M))
        (p.isMaximal.mem_iff_models φ).symm)
  rfl

end

end Theory

end Language

end FirstOrder
