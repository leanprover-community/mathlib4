/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.ModelTheory.Satisfiability

#align_import model_theory.types from "leanprover-community/mathlib"@"98bd247d933fb581ff37244a5998bd33d81dd46d"

/-!
# Type Spaces
This file defines the space of complete types over a first-order theory.
(Note that types in model theory are different from types in type theory.)

## Main Definitions
* `FirstOrder.Language.Theory.CompleteType`:
  `T.CompleteType α` consists of complete types over the theory `T` with variables `α`.
* `FirstOrder.Language.Theory.typeOf` is the type of a given tuple.
* `FirstOrder.Language.Theory.realizedTypes`: `T.realizedTypes M α` is the set of
  types in `T.CompleteType α` that are realized in `M` - that is, the type of some tuple in `M`.

## Main Results
* `FirstOrder.Language.Theory.CompleteType.nonempty_iff`:
  The space `T.CompleteType α` is nonempty exactly when `T` is satisfiable.
* `FirstOrder.Language.Theory.CompleteType.exists_modelType_is_realized_in`: Every type is realized
in some model.

## Implementation Notes
* Complete types are implemented as maximal consistent theories in an expanded language.
More frequently they are described as maximal consistent sets of formulas, but this is equivalent.

## TODO
* Connect `T.CompleteType α` to sets of formulas `L.Formula α`.

-/


set_option linter.uppercaseLean3 false

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
  subset' : (L.lhomWithConstants α).onTheory T ⊆ toTheory
  isMaximal' : toTheory.IsMaximal
#align first_order.language.Theory.complete_type FirstOrder.Language.Theory.CompleteType
#align first_order.language.Theory.complete_type.to_Theory FirstOrder.Language.Theory.CompleteType.toTheory
#align first_order.language.Theory.complete_type.subset' FirstOrder.Language.Theory.CompleteType.subset'
#align first_order.language.Theory.complete_type.is_maximal' FirstOrder.Language.Theory.CompleteType.isMaximal'

variable {T α}

namespace CompleteType

attribute [coe] CompleteType.toTheory

instance Sentence.instSetLike : SetLike (T.CompleteType α) (L[[α]].Sentence) :=
  ⟨fun p => p.toTheory, fun p q h => by
    cases p
    -- ⊢ { toTheory := toTheory✝, subset' := subset'✝, isMaximal' := isMaximal'✝ } = q
    cases q
    -- ⊢ { toTheory := toTheory✝¹, subset' := subset'✝¹, isMaximal' := isMaximal'✝¹ } …
    congr ⟩
    -- 🎉 no goals
#align first_order.language.Theory.complete_type.sentence.set_like FirstOrder.Language.Theory.CompleteType.Sentence.instSetLike

theorem isMaximal (p : T.CompleteType α) : IsMaximal (p : L[[α]].Theory) :=
  p.isMaximal'
#align first_order.language.Theory.complete_type.is_maximal FirstOrder.Language.Theory.CompleteType.isMaximal

theorem subset (p : T.CompleteType α) : (L.lhomWithConstants α).onTheory T ⊆ (p : L[[α]].Theory) :=
  p.subset'
#align first_order.language.Theory.complete_type.subset FirstOrder.Language.Theory.CompleteType.subset

theorem mem_or_not_mem (p : T.CompleteType α) (φ : L[[α]].Sentence) : φ ∈ p ∨ φ.not ∈ p :=
  p.isMaximal.mem_or_not_mem φ
#align first_order.language.Theory.complete_type.mem_or_not_mem FirstOrder.Language.Theory.CompleteType.mem_or_not_mem

theorem mem_of_models (p : T.CompleteType α) {φ : L[[α]].Sentence}
    (h : (L.lhomWithConstants α).onTheory T ⊨ᵇ φ) : φ ∈ p :=
  (p.mem_or_not_mem φ).resolve_right fun con =>
    ((models_iff_not_satisfiable _).1 h)
      (p.isMaximal.1.mono (union_subset p.subset (singleton_subset_iff.2 con)))
#align first_order.language.Theory.complete_type.mem_of_models FirstOrder.Language.Theory.CompleteType.mem_of_models

theorem not_mem_iff (p : T.CompleteType α) (φ : L[[α]].Sentence) : φ.not ∈ p ↔ ¬φ ∈ p :=
  ⟨fun hf ht => by
    have h : ¬IsSatisfiable ({φ, φ.not} : L[[α]].Theory) := by
      rintro ⟨@⟨_, _, h, _⟩⟩
      simp only [model_iff, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq] at h
      exact h.2 h.1
    refine' h (p.isMaximal.1.mono _)
    -- ⊢ {φ, Formula.not φ} ⊆ ↑p
    rw [insert_subset_iff, singleton_subset_iff]
    -- ⊢ φ ∈ ↑p ∧ Formula.not φ ∈ ↑p
    exact ⟨ht, hf⟩, (p.mem_or_not_mem φ).resolve_left⟩
    -- 🎉 no goals
#align first_order.language.Theory.complete_type.not_mem_iff FirstOrder.Language.Theory.CompleteType.not_mem_iff

@[simp]
theorem compl_setOf_mem {φ : L[[α]].Sentence} :
    { p : T.CompleteType α | φ ∈ p }ᶜ = { p : T.CompleteType α | φ.not ∈ p } :=
  ext fun _ => (not_mem_iff _ _).symm
#align first_order.language.Theory.complete_type.compl_set_of_mem FirstOrder.Language.Theory.CompleteType.compl_setOf_mem

theorem setOf_subset_eq_empty_iff (S : L[[α]].Theory) :
    { p : T.CompleteType α | S ⊆ ↑p } = ∅ ↔
      ¬((L.lhomWithConstants α).onTheory T ∪ S).IsSatisfiable := by
  rw [iff_not_comm, ← not_nonempty_iff_eq_empty, Classical.not_not, Set.Nonempty]
  -- ⊢ IsSatisfiable (LHom.onTheory (lhomWithConstants L α) T ∪ S) ↔ ∃ x, x ∈ {p |  …
  refine'
    ⟨fun h =>
      ⟨⟨L[[α]].completeTheory h.some, (subset_union_left _ S).trans completeTheory.subset,
          completeTheory.isMaximal (L[[α]]) h.some⟩,
        (subset_union_right ((L.lhomWithConstants α).onTheory T) _).trans completeTheory.subset⟩,
      _⟩
  rintro ⟨p, hp⟩
  -- ⊢ IsSatisfiable (LHom.onTheory (lhomWithConstants L α) T ∪ S)
  exact p.isMaximal.1.mono (union_subset p.subset hp)
  -- 🎉 no goals
#align first_order.language.Theory.complete_type.set_of_subset_eq_empty_iff FirstOrder.Language.Theory.CompleteType.setOf_subset_eq_empty_iff

theorem setOf_mem_eq_univ_iff (φ : L[[α]].Sentence) :
    { p : T.CompleteType α | φ ∈ p } = Set.univ ↔ (L.lhomWithConstants α).onTheory T ⊨ᵇ φ := by
  rw [models_iff_not_satisfiable, ← compl_empty_iff, compl_setOf_mem, ← setOf_subset_eq_empty_iff]
  -- ⊢ {p | Formula.not φ ∈ p} = ∅ ↔ {p | {Formula.not φ} ⊆ ↑p} = ∅
  simp
  -- 🎉 no goals
#align first_order.language.Theory.complete_type.set_of_mem_eq_univ_iff FirstOrder.Language.Theory.CompleteType.setOf_mem_eq_univ_iff

theorem setOf_subset_eq_univ_iff (S : L[[α]].Theory) :
    { p : T.CompleteType α | S ⊆ ↑p } = Set.univ ↔
      ∀ φ, φ ∈ S → (L.lhomWithConstants α).onTheory T ⊨ᵇ φ := by
  have h : { p : T.CompleteType α | S ⊆ ↑p } = ⋂₀ ((fun φ => { p | φ ∈ p }) '' S) := by
    ext
    simp [subset_def]
  simp_rw [h, sInter_eq_univ, ← setOf_mem_eq_univ_iff]
  -- ⊢ (∀ (s : Set (CompleteType T α)), s ∈ (fun φ => {p | φ ∈ p}) '' S → s = Set.u …
  refine' ⟨fun h φ φS => h _ ⟨_, φS, rfl⟩, _⟩
  -- ⊢ (∀ (φ : Sentence (L[[α]])), φ ∈ S → {p | φ ∈ p} = Set.univ) → ∀ (s : Set (Co …
  rintro h _ ⟨φ, h1, rfl⟩
  -- ⊢ (fun φ => {p | φ ∈ p}) φ = Set.univ
  exact h _ h1
  -- 🎉 no goals
#align first_order.language.Theory.complete_type.set_of_subset_eq_univ_iff FirstOrder.Language.Theory.CompleteType.setOf_subset_eq_univ_iff

theorem nonempty_iff : Nonempty (T.CompleteType α) ↔ T.IsSatisfiable := by
  rw [← isSatisfiable_onTheory_iff (lhomWithConstants_injective L α)]
  -- ⊢ Nonempty (CompleteType T α) ↔ IsSatisfiable (LHom.onTheory (lhomWithConstant …
  rw [nonempty_iff_univ_nonempty, nonempty_iff_ne_empty, Ne.def, not_iff_comm,
    ← union_empty ((L.lhomWithConstants α).onTheory T), ← setOf_subset_eq_empty_iff]
  simp
  -- 🎉 no goals
#align first_order.language.Theory.complete_type.nonempty_iff FirstOrder.Language.Theory.CompleteType.nonempty_iff

instance instNonempty : Nonempty (CompleteType (∅ : L.Theory) α) :=
  nonempty_iff.2 (isSatisfiable_empty L)
#align first_order.language.Theory.complete_type.nonempty FirstOrder.Language.Theory.CompleteType.instNonempty

theorem iInter_setOf_subset {ι : Type*} (S : ι → L[[α]].Theory) :
    ⋂ i : ι, { p : T.CompleteType α | S i ⊆ p } =
      { p : T.CompleteType α | ⋃ i : ι, S i ⊆ p } := by
  ext
  -- ⊢ x✝ ∈ ⋂ (i : ι), {p | S i ⊆ ↑p} ↔ x✝ ∈ {p | ⋃ (i : ι), S i ⊆ ↑p}
  simp only [mem_iInter, mem_setOf_eq, iUnion_subset_iff]
  -- 🎉 no goals
#align first_order.language.Theory.complete_type.Inter_set_of_subset FirstOrder.Language.Theory.CompleteType.iInter_setOf_subset

theorem toList_foldr_inf_mem {p : T.CompleteType α} {t : Finset (L[[α]]).Sentence} :
    t.toList.foldr (· ⊓ ·) ⊤ ∈ p ↔ (t : L[[α]].Theory) ⊆ ↑p := by
  simp_rw [subset_def, ← SetLike.mem_coe, p.isMaximal.mem_iff_models, models_sentence_iff,
    Sentence.Realize, Formula.Realize, BoundedFormula.realize_foldr_inf, Finset.mem_toList]
  exact ⟨fun h φ hφ M => h _ _ hφ, fun h M φ hφ => h _ hφ _⟩
  -- 🎉 no goals
#align first_order.language.Theory.complete_type.to_list_foldr_inf_mem FirstOrder.Language.Theory.CompleteType.toList_foldr_inf_mem

end CompleteType

variable {M : Type w'} [L.Structure M] [Nonempty M] [M ⊨ T] (T)

/-- The set of all formulas true at a tuple in a structure forms a complete type. -/
def typeOf (v : α → M) : T.CompleteType α :=
  haveI : (constantsOn α).Structure M := constantsOn.structure v
  { toTheory := L[[α]].completeTheory M
    subset' := model_iff_subset_completeTheory.1 ((LHom.onTheory_model _ T).2 inferInstance)
    isMaximal' := completeTheory.isMaximal _ _ }
#align first_order.language.Theory.type_of FirstOrder.Language.Theory.typeOf

namespace CompleteType

variable {T} {v : α → M}

@[simp]
theorem mem_typeOf {φ : L[[α]].Sentence} :
    φ ∈ T.typeOf v ↔ (Formula.equivSentence.symm φ).Realize v :=
  letI : (constantsOn α).Structure M := constantsOn.structure v
  mem_completeTheory.trans (Formula.realize_equivSentence_symm _ _ _).symm
#align first_order.language.Theory.complete_type.mem_type_of FirstOrder.Language.Theory.CompleteType.mem_typeOf

theorem formula_mem_typeOf {φ : L.Formula α} : Formula.equivSentence φ ∈ T.typeOf v ↔ φ.Realize v :=
  by simp
     -- 🎉 no goals
#align first_order.language.Theory.complete_type.formula_mem_type_of FirstOrder.Language.Theory.CompleteType.formula_mem_typeOf

end CompleteType

variable (M)

/-- A complete type `p` is realized in a particular structure when there is some
  tuple `v` whose type is `p`. -/
@[simp]
def realizedTypes (α : Type w) : Set (T.CompleteType α) :=
  Set.range (T.typeOf : (α → M) → T.CompleteType α)
#align first_order.language.Theory.realized_types FirstOrder.Language.Theory.realizedTypes

section
-- Porting note: This instance interrupts synthesizing instances.
attribute [-instance] FirstOrder.Language.withConstants_expansion

theorem exists_modelType_is_realized_in (p : T.CompleteType α) :
    ∃ M : Theory.ModelType.{u, v, max u v w} T, p ∈ T.realizedTypes M α := by
  obtain ⟨M⟩ := p.isMaximal.1
  -- ⊢ ∃ M, p ∈ realizedTypes T (↑M) α
  refine' ⟨(M.subtheoryModel p.subset).reduct (L.lhomWithConstants α), fun a => (L.con a : M), _⟩
  -- ⊢ (typeOf T fun a => ↑(Language.con L a)) = p
  refine' SetLike.ext fun φ => _
  -- ⊢ (φ ∈ typeOf T fun a => ↑(Language.con L a)) ↔ φ ∈ p
  simp only [CompleteType.mem_typeOf]
  -- ⊢ (Formula.Realize (↑Formula.equivSentence.symm φ) fun a => ↑(Language.con L a …
  refine'
    (@Formula.realize_equivSentence_symm_con _
      ((M.subtheoryModel p.subset).reduct (L.lhomWithConstants α)) _ _ M.struc _ φ).trans
      (_root_.trans (_root_.trans _ (p.isMaximal.isComplete.realize_sentence_iff φ M))
        (p.isMaximal.mem_iff_models φ).symm)
  rfl
  -- 🎉 no goals
#align first_order.language.Theory.exists_Model_is_realized_in FirstOrder.Language.Theory.exists_modelType_is_realized_in

end

end Theory

end Language

end FirstOrder
