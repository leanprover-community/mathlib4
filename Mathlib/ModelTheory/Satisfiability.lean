/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.ModelTheory.Ultraproducts
import Mathlib.ModelTheory.Bundled
import Mathlib.ModelTheory.Skolem

#align_import model_theory.satisfiability from "leanprover-community/mathlib"@"d565b3df44619c1498326936be16f1a935df0728"

/-!
# First-Order Satisfiability
This file deals with the satisfiability of first-order theories, as well as equivalence over them.

## Main Definitions
* `FirstOrder.Language.Theory.IsSatisfiable`: `T.IsSatisfiable` indicates that `T` has a nonempty
model.
* `FirstOrder.Language.Theory.IsFinitelySatisfiable`: `T.IsFinitelySatisfiable` indicates that
every finite subset of `T` is satisfiable.
* `FirstOrder.Language.Theory.IsComplete`: `T.IsComplete` indicates that `T` is satisfiable and
models each sentence or its negation.
* `FirstOrder.Language.Theory.SemanticallyEquivalent`: `T.SemanticallyEquivalent φ ψ` indicates
that `φ` and `ψ` are equivalent formulas or sentences in models of `T`.
* `Cardinal.Categorical`: A theory is `κ`-categorical if all models of size `κ` are isomorphic.

## Main Results
* The Compactness Theorem, `FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable`,
shows that a theory is satisfiable iff it is finitely satisfiable.
* `FirstOrder.Language.completeTheory.isComplete`: The complete theory of a structure is
complete.
* `FirstOrder.Language.Theory.exists_large_model_of_infinite_model` shows that any theory with an
infinite model has arbitrarily large models.
* `FirstOrder.Language.Theory.exists_elementaryEmbedding_card_eq`: The Upward Löwenheim–Skolem
Theorem: If `κ` is a cardinal greater than the cardinalities of `L` and an infinite `L`-structure
`M`, then `M` has an elementary extension of cardinality `κ`.

## Implementation Details
* Satisfiability of an `L.Theory` `T` is defined in the minimal universe containing all the symbols
of `L`. By Löwenheim-Skolem, this is equivalent to satisfiability in any universe.

-/


set_option linter.uppercaseLean3 false

universe u v w w'

open Cardinal CategoryTheory

open Cardinal FirstOrder

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {T : L.Theory} {α : Type w} {n : ℕ}

namespace Theory

variable (T)

/-- A theory is satisfiable if a structure models it. -/
def IsSatisfiable : Prop :=
  Nonempty (ModelType.{u, v, max u v} T)
#align first_order.language.Theory.is_satisfiable FirstOrder.Language.Theory.IsSatisfiable

/-- A theory is finitely satisfiable if all of its finite subtheories are satisfiable. -/
def IsFinitelySatisfiable : Prop :=
  ∀ T0 : Finset L.Sentence, (T0 : L.Theory) ⊆ T → IsSatisfiable (T0 : L.Theory)
#align first_order.language.Theory.is_finitely_satisfiable FirstOrder.Language.Theory.IsFinitelySatisfiable

variable {T} {T' : L.Theory}

theorem Model.isSatisfiable (M : Type w) [Nonempty M] [L.Structure M] [M ⊨ T] :
    T.IsSatisfiable :=
  ⟨((⊥ : Substructure _ (ModelType.of T M)).elementarySkolem₁Reduct.toModel T).shrink⟩
#align first_order.language.Theory.model.is_satisfiable FirstOrder.Language.Theory.Model.isSatisfiable

theorem IsSatisfiable.mono (h : T'.IsSatisfiable) (hs : T ⊆ T') : T.IsSatisfiable :=
  ⟨(Theory.Model.mono (ModelType.is_model h.some) hs).bundled⟩
#align first_order.language.Theory.is_satisfiable.mono FirstOrder.Language.Theory.IsSatisfiable.mono

theorem isSatisfiable_empty (L : Language.{u, v}) : IsSatisfiable (∅ : L.Theory) :=
  ⟨default⟩
#align first_order.language.Theory.is_satisfiable_empty FirstOrder.Language.Theory.isSatisfiable_empty

theorem isSatisfiable_of_isSatisfiable_onTheory {L' : Language.{w, w'}} (φ : L →ᴸ L')
    (h : (φ.onTheory T).IsSatisfiable) : T.IsSatisfiable :=
  Model.isSatisfiable (h.some.reduct φ)
#align first_order.language.Theory.is_satisfiable_of_is_satisfiable_on_Theory FirstOrder.Language.Theory.isSatisfiable_of_isSatisfiable_onTheory

theorem isSatisfiable_onTheory_iff {L' : Language.{w, w'}} {φ : L →ᴸ L'} (h : φ.Injective) :
    (φ.onTheory T).IsSatisfiable ↔ T.IsSatisfiable := by
  classical
    refine ⟨isSatisfiable_of_isSatisfiable_onTheory φ, fun h' => ?_⟩
    haveI : Inhabited h'.some := Classical.inhabited_of_nonempty'
    exact Model.isSatisfiable (h'.some.defaultExpansion h)
#align first_order.language.Theory.is_satisfiable_on_Theory_iff FirstOrder.Language.Theory.isSatisfiable_onTheory_iff

theorem IsSatisfiable.isFinitelySatisfiable (h : T.IsSatisfiable) : T.IsFinitelySatisfiable :=
  fun _ => h.mono
#align first_order.language.Theory.is_satisfiable.is_finitely_satisfiable FirstOrder.Language.Theory.IsSatisfiable.isFinitelySatisfiable

/-- The **Compactness Theorem of first-order logic**: A theory is satisfiable if and only if it is
finitely satisfiable. -/
theorem isSatisfiable_iff_isFinitelySatisfiable {T : L.Theory} :
    T.IsSatisfiable ↔ T.IsFinitelySatisfiable :=
  ⟨Theory.IsSatisfiable.isFinitelySatisfiable, fun h => by
    classical
      set M : Finset T → Type max u v := fun T0 : Finset T =>
        (h (T0.map (Function.Embedding.subtype fun x => x ∈ T)) T0.map_subtype_subset).some.Carrier
      let M' := Filter.Product (Ultrafilter.of (Filter.atTop : Filter (Finset T))) M
      have h' : M' ⊨ T := by
        refine ⟨fun φ hφ => ?_⟩
        rw [Ultraproduct.sentence_realize]
        refine
          Filter.Eventually.filter_mono (Ultrafilter.of_le _)
            (Filter.eventually_atTop.2
              ⟨{⟨φ, hφ⟩}, fun s h' =>
                Theory.realize_sentence_of_mem (s.map (Function.Embedding.subtype fun x => x ∈ T))
                  ?_⟩)
        simp only [Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image, Finset.mem_coe,
          Subtype.exists, Subtype.coe_mk, exists_and_right, exists_eq_right]
        exact ⟨hφ, h' (Finset.mem_singleton_self _)⟩
      exact ⟨ModelType.of T M'⟩⟩
#align first_order.language.Theory.is_satisfiable_iff_is_finitely_satisfiable FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable

theorem isSatisfiable_directed_union_iff {ι : Type*} [Nonempty ι] {T : ι → L.Theory}
    (h : Directed (· ⊆ ·) T) : Theory.IsSatisfiable (⋃ i, T i) ↔ ∀ i, (T i).IsSatisfiable := by
  refine ⟨fun h' i => h'.mono (Set.subset_iUnion _ _), fun h' => ?_⟩
  rw [isSatisfiable_iff_isFinitelySatisfiable, IsFinitelySatisfiable]
  intro T0 hT0
  obtain ⟨i, hi⟩ := h.exists_mem_subset_of_finset_subset_biUnion hT0
  exact (h' i).mono hi
#align first_order.language.Theory.is_satisfiable_directed_union_iff FirstOrder.Language.Theory.isSatisfiable_directed_union_iff

theorem isSatisfiable_union_distinctConstantsTheory_of_card_le (T : L.Theory) (s : Set α)
    (M : Type w') [Nonempty M] [L.Structure M] [M ⊨ T]
    (h : Cardinal.lift.{w'} #s ≤ Cardinal.lift.{w} #M) :
    ((L.lhomWithConstants α).onTheory T ∪ L.distinctConstantsTheory s).IsSatisfiable := by
  haveI : Inhabited M := Classical.inhabited_of_nonempty inferInstance
  rw [Cardinal.lift_mk_le'] at h
  letI : (constantsOn α).Structure M := constantsOn.structure (Function.extend (↑) h.some default)
  have : M ⊨ (L.lhomWithConstants α).onTheory T ∪ L.distinctConstantsTheory s := by
    refine ((LHom.onTheory_model _ _).2 inferInstance).union ?_
    rw [model_distinctConstantsTheory]
    refine fun a as b bs ab => ?_
    rw [← Subtype.coe_mk a as, ← Subtype.coe_mk b bs, ← Subtype.ext_iff]
    exact
      h.some.injective
        ((Subtype.coe_injective.extend_apply h.some default ⟨a, as⟩).symm.trans
          (ab.trans (Subtype.coe_injective.extend_apply h.some default ⟨b, bs⟩)))
  exact Model.isSatisfiable M
#align first_order.language.Theory.is_satisfiable_union_distinct_constants_theory_of_card_le FirstOrder.Language.Theory.isSatisfiable_union_distinctConstantsTheory_of_card_le

theorem isSatisfiable_union_distinctConstantsTheory_of_infinite (T : L.Theory) (s : Set α)
    (M : Type w') [L.Structure M] [M ⊨ T] [Infinite M] :
    ((L.lhomWithConstants α).onTheory T ∪ L.distinctConstantsTheory s).IsSatisfiable := by
  classical
    rw [distinctConstantsTheory_eq_iUnion, Set.union_iUnion, isSatisfiable_directed_union_iff]
    · exact fun t =>
        isSatisfiable_union_distinctConstantsTheory_of_card_le T _ M
          ((lift_le_aleph0.2 (finset_card_lt_aleph0 _).le).trans
            (aleph0_le_lift.2 (aleph0_le_mk M)))
    · apply Monotone.directed_le
      refine monotone_const.union (monotone_distinctConstantsTheory.comp ?_)
      simp only [Finset.coe_map, Function.Embedding.coe_subtype]
      exact Monotone.comp (g := Set.image ((↑) : s → α)) (f := ((↑) : Finset s → Set s))
        Set.monotone_image fun _ _ => Finset.coe_subset.2
#align first_order.language.Theory.is_satisfiable_union_distinct_constants_theory_of_infinite FirstOrder.Language.Theory.isSatisfiable_union_distinctConstantsTheory_of_infinite

/-- Any theory with an infinite model has arbitrarily large models. -/
theorem exists_large_model_of_infinite_model (T : L.Theory) (κ : Cardinal.{w}) (M : Type w')
    [L.Structure M] [M ⊨ T] [Infinite M] :
    ∃ N : ModelType.{_, _, max u v w} T, Cardinal.lift.{max u v w} κ ≤ #N := by
  obtain ⟨N⟩ :=
    isSatisfiable_union_distinctConstantsTheory_of_infinite T (Set.univ : Set κ.out) M
  refine ⟨(N.is_model.mono (Set.subset_union_left _ _)).bundled.reduct _, ?_⟩
  haveI : N ⊨ distinctConstantsTheory _ _ := N.is_model.mono (Set.subset_union_right _ _)
  rw [ModelType.reduct_Carrier, coe_of]
  refine _root_.trans (lift_le.2 (le_of_eq (Cardinal.mk_out κ).symm)) ?_
  rw [← mk_univ]
  refine
    (card_le_of_model_distinctConstantsTheory L Set.univ N).trans (lift_le.{max u v w}.1 ?_)
  rw [lift_lift]
#align first_order.language.Theory.exists_large_model_of_infinite_model FirstOrder.Language.Theory.exists_large_model_of_infinite_model

theorem isSatisfiable_iUnion_iff_isSatisfiable_iUnion_finset {ι : Type*} (T : ι → L.Theory) :
    IsSatisfiable (⋃ i, T i) ↔ ∀ s : Finset ι, IsSatisfiable (⋃ i ∈ s, T i) := by
  classical
    refine
      ⟨fun h s => h.mono (Set.iUnion_mono fun _ => Set.iUnion_subset_iff.2 fun _ => refl _),
        fun h => ?_⟩
    rw [isSatisfiable_iff_isFinitelySatisfiable]
    intro s hs
    rw [Set.iUnion_eq_iUnion_finset] at hs
    obtain ⟨t, ht⟩ := Directed.exists_mem_subset_of_finset_subset_biUnion (by
      exact Monotone.directed_le fun t1 t2 (h : ∀ ⦃x⦄, x ∈ t1 → x ∈ t2) =>
        Set.iUnion_mono fun _ => Set.iUnion_mono' fun h1 => ⟨h h1, refl _⟩) hs
    exact (h t).mono ht
#align first_order.language.Theory.is_satisfiable_Union_iff_is_satisfiable_Union_finset FirstOrder.Language.Theory.isSatisfiable_iUnion_iff_isSatisfiable_iUnion_finset

end Theory

variable (L)

/-- A version of The Downward Löwenheim–Skolem theorem where the structure `N` elementarily embeds
into `M`, but is not by type a substructure of `M`, and thus can be chosen to belong to the universe
of the cardinal `κ`.
 -/
theorem exists_elementaryEmbedding_card_eq_of_le (M : Type w') [L.Structure M] [Nonempty M]
    (κ : Cardinal.{w}) (h1 : ℵ₀ ≤ κ) (h2 : lift.{w} L.card ≤ Cardinal.lift.{max u v} κ)
    (h3 : lift.{w'} κ ≤ Cardinal.lift.{w} #M) :
    ∃ N : Bundled L.Structure, Nonempty (N ↪ₑ[L] M) ∧ #N = κ := by
  obtain ⟨S, _, hS⟩ := exists_elementarySubstructure_card_eq L ∅ κ h1 (by simp) h2 h3
  have : Small.{w} S := by
    rw [← lift_inj.{_, w + 1}, lift_lift, lift_lift] at hS
    exact small_iff_lift_mk_lt_univ.2 (lt_of_eq_of_lt hS κ.lift_lt_univ')
  refine
    ⟨(equivShrink S).bundledInduced L,
      ⟨S.subtype.comp (Equiv.bundledInducedEquiv L _).symm.toElementaryEmbedding⟩,
      lift_inj.1 (_root_.trans ?_ hS)⟩
  simp only [Equiv.bundledInduced_α, lift_mk_shrink']
#align first_order.language.exists_elementary_embedding_card_eq_of_le FirstOrder.Language.exists_elementaryEmbedding_card_eq_of_le

section
-- Porting note: This instance interrupts synthesizing instances.
attribute [-instance] FirstOrder.Language.withConstants_expansion

/-- The **Upward Löwenheim–Skolem Theorem**: If `κ` is a cardinal greater than the cardinalities of
`L` and an infinite `L`-structure `M`, then `M` has an elementary extension of cardinality `κ`. -/
theorem exists_elementaryEmbedding_card_eq_of_ge (M : Type w') [L.Structure M] [iM : Infinite M]
    (κ : Cardinal.{w}) (h1 : Cardinal.lift.{w} L.card ≤ Cardinal.lift.{max u v} κ)
    (h2 : Cardinal.lift.{w} #M ≤ Cardinal.lift.{w'} κ) :
    ∃ N : Bundled L.Structure, Nonempty (M ↪ₑ[L] N) ∧ #N = κ := by
  obtain ⟨N0, hN0⟩ := (L.elementaryDiagram M).exists_large_model_of_infinite_model κ M
  rw [← lift_le.{max u v}, lift_lift, lift_lift] at h2
  obtain ⟨N, ⟨NN0⟩, hN⟩ :=
    exists_elementaryEmbedding_card_eq_of_le (L[[M]]) N0 κ
      (aleph0_le_lift.1 ((aleph0_le_lift.2 (aleph0_le_mk M)).trans h2))
      (by
        simp only [card_withConstants, lift_add, lift_lift]
        rw [add_comm, add_eq_max (aleph0_le_lift.2 (infinite_iff.1 iM)), max_le_iff]
        rw [← lift_le.{w'}, lift_lift, lift_lift] at h1
        exact ⟨h2, h1⟩)
      (hN0.trans (by rw [← lift_umax', lift_id]))
  letI := (lhomWithConstants L M).reduct N
  haveI h : N ⊨ L.elementaryDiagram M :=
    (NN0.theory_model_iff (L.elementaryDiagram M)).2 inferInstance
  refine ⟨Bundled.of N, ⟨?_⟩, hN⟩
  apply ElementaryEmbedding.ofModelsElementaryDiagram L M N
#align first_order.language.exists_elementary_embedding_card_eq_of_ge FirstOrder.Language.exists_elementaryEmbedding_card_eq_of_ge

end

/-- The Löwenheim–Skolem Theorem: If `κ` is a cardinal greater than the cardinalities of `L`
and an infinite `L`-structure `M`, then there is an elementary embedding in the appropriate
direction between then `M` and a structure of cardinality `κ`. -/
theorem exists_elementaryEmbedding_card_eq (M : Type w') [L.Structure M] [iM : Infinite M]
    (κ : Cardinal.{w}) (h1 : ℵ₀ ≤ κ) (h2 : lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) :
    ∃ N : Bundled L.Structure, (Nonempty (N ↪ₑ[L] M) ∨ Nonempty (M ↪ₑ[L] N)) ∧ #N = κ := by
  cases le_or_gt (lift.{w'} κ) (Cardinal.lift.{w} #M) with
  | inl h =>
    obtain ⟨N, hN1, hN2⟩ := exists_elementaryEmbedding_card_eq_of_le L M κ h1 h2 h
    exact ⟨N, Or.inl hN1, hN2⟩
  | inr h =>
    obtain ⟨N, hN1, hN2⟩ := exists_elementaryEmbedding_card_eq_of_ge L M κ h2 (le_of_lt h)
    exact ⟨N, Or.inr hN1, hN2⟩
#align first_order.language.exists_elementary_embedding_card_eq FirstOrder.Language.exists_elementaryEmbedding_card_eq

/-- A consequence of the Löwenheim–Skolem Theorem: If `κ` is a cardinal greater than the
cardinalities of `L` and an infinite `L`-structure `M`, then there is a structure of cardinality `κ`
elementarily equivalent to `M`. -/
theorem exists_elementarilyEquivalent_card_eq (M : Type w') [L.Structure M] [Infinite M]
    (κ : Cardinal.{w}) (h1 : ℵ₀ ≤ κ) (h2 : lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) :
    ∃ N : CategoryTheory.Bundled L.Structure, (M ≅[L] N) ∧ #N = κ := by
  obtain ⟨N, NM | MN, hNκ⟩ := exists_elementaryEmbedding_card_eq L M κ h1 h2
  · exact ⟨N, NM.some.elementarilyEquivalent.symm, hNκ⟩
  · exact ⟨N, MN.some.elementarilyEquivalent, hNκ⟩
#align first_order.language.exists_elementarily_equivalent_card_eq FirstOrder.Language.exists_elementarilyEquivalent_card_eq

variable {L}

namespace Theory

theorem exists_model_card_eq (h : ∃ M : ModelType.{u, v, max u v} T, Infinite M) (κ : Cardinal.{w})
    (h1 : ℵ₀ ≤ κ) (h2 : Cardinal.lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) :
    ∃ N : ModelType.{u, v, w} T, #N = κ := by
  cases h with
  | intro M MI =>
    haveI := MI
    obtain ⟨N, hN, rfl⟩ := exists_elementarilyEquivalent_card_eq L M κ h1 h2
    haveI : Nonempty N := hN.nonempty
    exact ⟨hN.theory_model.bundled, rfl⟩
#align first_order.language.Theory.exists_model_card_eq FirstOrder.Language.Theory.exists_model_card_eq

variable (T)

/-- A theory models a (bounded) formula when any of its nonempty models realizes that formula on all
  inputs. -/
def ModelsBoundedFormula (φ : L.BoundedFormula α n) : Prop :=
  ∀ (M : ModelType.{u, v, max u v} T) (v : α → M) (xs : Fin n → M), φ.Realize v xs
#align first_order.language.Theory.models_bounded_formula FirstOrder.Language.Theory.ModelsBoundedFormula

-- Porting note: In Lean3 it was `⊨` but ambiguous.
@[inherit_doc FirstOrder.Language.Theory.ModelsBoundedFormula]
infixl:51 " ⊨ᵇ " => ModelsBoundedFormula -- input using \|= or \vDash, but not using \models

variable {T}

theorem models_formula_iff {φ : L.Formula α} :
    T ⊨ᵇ φ ↔ ∀ (M : ModelType.{u, v, max u v} T) (v : α → M), φ.Realize v :=
  forall_congr' fun _ => forall_congr' fun _ => Unique.forall_iff
#align first_order.language.Theory.models_formula_iff FirstOrder.Language.Theory.models_formula_iff

theorem models_sentence_iff {φ : L.Sentence} : T ⊨ᵇ φ ↔ ∀ M : ModelType.{u, v, max u v} T, M ⊨ φ :=
  models_formula_iff.trans (forall_congr' fun _ => Unique.forall_iff)
#align first_order.language.Theory.models_sentence_iff FirstOrder.Language.Theory.models_sentence_iff

theorem models_sentence_of_mem {φ : L.Sentence} (h : φ ∈ T) : T ⊨ᵇ φ :=
  models_sentence_iff.2 fun _ => realize_sentence_of_mem T h
#align first_order.language.Theory.models_sentence_of_mem FirstOrder.Language.Theory.models_sentence_of_mem

theorem models_iff_not_satisfiable (φ : L.Sentence) : T ⊨ᵇ φ ↔ ¬IsSatisfiable (T ∪ {φ.not}) := by
  rw [models_sentence_iff, IsSatisfiable]
  refine
    ⟨fun h1 h2 =>
      (Sentence.realize_not _).1
        (realize_sentence_of_mem (T ∪ {Formula.not φ})
          (Set.subset_union_right _ _ (Set.mem_singleton _)))
        (h1 (h2.some.subtheoryModel (Set.subset_union_left _ _))),
      fun h M => ?_⟩
  contrapose! h
  rw [← Sentence.realize_not] at h
  refine
    ⟨{  Carrier := M
        is_model := ⟨fun ψ hψ => hψ.elim (realize_sentence_of_mem _) fun h' => ?_⟩ }⟩
  rw [Set.mem_singleton_iff.1 h']
  exact h
#align first_order.language.Theory.models_iff_not_satisfiable FirstOrder.Language.Theory.models_iff_not_satisfiable

theorem ModelsBoundedFormula.realize_sentence {φ : L.Sentence} (h : T ⊨ᵇ φ) (M : Type*)
    [L.Structure M] [M ⊨ T] [Nonempty M] : M ⊨ φ := by
  rw [models_iff_not_satisfiable] at h
  contrapose! h
  have : M ⊨ T ∪ {Formula.not φ} := by
    simp only [Set.union_singleton, model_iff, Set.mem_insert_iff, forall_eq_or_imp,
      Sentence.realize_not]
    rw [← model_iff]
    exact ⟨h, inferInstance⟩
  exact Model.isSatisfiable M
#align first_order.language.Theory.models_bounded_formula.realize_sentence FirstOrder.Language.Theory.ModelsBoundedFormula.realize_sentence

theorem models_of_models_theory {T' : L.Theory}
    (h : ∀ φ : L.Sentence, φ ∈ T' → T ⊨ᵇ φ)
    {φ : L.Formula α} (hφ : T' ⊨ᵇ φ) : T ⊨ᵇ φ := by
  simp only [models_sentence_iff] at h
  intro M
  have hM : M ⊨ T' := T'.model_iff.2 (fun ψ hψ => h ψ hψ M)
  let M' : ModelType T' := ⟨M⟩
  exact hφ M'

/-- An alternative statement of the Compactness Theorem. A formula `φ` is modeled by a
theory iff there is a finite subset `T0` of the theory such that `φ` is modeled by `T0` -/
theorem models_iff_finset_models {φ : L.Sentence} :
    T ⊨ᵇ φ ↔ ∃ T0 : Finset L.Sentence, (T0 : L.Theory) ⊆ T ∧ (T0 : L.Theory) ⊨ᵇ φ := by
  simp only [models_iff_not_satisfiable]
  rw [← not_iff_not, not_not, isSatisfiable_iff_isFinitelySatisfiable, IsFinitelySatisfiable]
  push_neg
  letI := Classical.decEq (Sentence L)
  constructor
  · intro h T0 hT0
    simpa using h (T0 ∪ {Formula.not φ})
      (by
        simp only [Finset.coe_union, Finset.coe_singleton]
        exact Set.union_subset_union hT0 (Set.Subset.refl _))
  · intro h T0 hT0
    exact IsSatisfiable.mono (h (T0.erase (Formula.not φ))
      (by simpa using hT0)) (by simp)

/-- A theory is complete when it is satisfiable and models each sentence or its negation. -/
def IsComplete (T : L.Theory) : Prop :=
  T.IsSatisfiable ∧ ∀ φ : L.Sentence, T ⊨ᵇ φ ∨ T ⊨ᵇ φ.not
#align first_order.language.Theory.is_complete FirstOrder.Language.Theory.IsComplete

namespace IsComplete

theorem models_not_iff (h : T.IsComplete) (φ : L.Sentence) : T ⊨ᵇ φ.not ↔ ¬T ⊨ᵇ φ := by
  cases' h.2 φ with hφ hφn
  · simp only [hφ, not_true, iff_false_iff]
    rw [models_sentence_iff, not_forall]
    refine ⟨h.1.some, ?_⟩
    simp only [Sentence.realize_not, Classical.not_not]
    exact models_sentence_iff.1 hφ _
  · simp only [hφn, true_iff_iff]
    intro hφ
    rw [models_sentence_iff] at *
    exact hφn h.1.some (hφ _)
#align first_order.language.Theory.is_complete.models_not_iff FirstOrder.Language.Theory.IsComplete.models_not_iff

theorem realize_sentence_iff (h : T.IsComplete) (φ : L.Sentence) (M : Type*) [L.Structure M]
    [M ⊨ T] [Nonempty M] : M ⊨ φ ↔ T ⊨ᵇ φ := by
  cases' h.2 φ with hφ hφn
  · exact iff_of_true (hφ.realize_sentence M) hφ
  · exact
      iff_of_false ((Sentence.realize_not M).1 (hφn.realize_sentence M))
        ((h.models_not_iff φ).1 hφn)
#align first_order.language.Theory.is_complete.realize_sentence_iff FirstOrder.Language.Theory.IsComplete.realize_sentence_iff

end IsComplete

/-- A theory is maximal when it is satisfiable and contains each sentence or its negation.
  Maximal theories are complete. -/
def IsMaximal (T : L.Theory) : Prop :=
  T.IsSatisfiable ∧ ∀ φ : L.Sentence, φ ∈ T ∨ φ.not ∈ T
#align first_order.language.Theory.is_maximal FirstOrder.Language.Theory.IsMaximal

theorem IsMaximal.isComplete (h : T.IsMaximal) : T.IsComplete :=
  h.imp_right (forall_imp fun _ => Or.imp models_sentence_of_mem models_sentence_of_mem)
#align first_order.language.Theory.is_maximal.is_complete FirstOrder.Language.Theory.IsMaximal.isComplete

theorem IsMaximal.mem_or_not_mem (h : T.IsMaximal) (φ : L.Sentence) : φ ∈ T ∨ φ.not ∈ T :=
  h.2 φ
#align first_order.language.Theory.is_maximal.mem_or_not_mem FirstOrder.Language.Theory.IsMaximal.mem_or_not_mem

theorem IsMaximal.mem_of_models (h : T.IsMaximal) {φ : L.Sentence} (hφ : T ⊨ᵇ φ) : φ ∈ T := by
  refine (h.mem_or_not_mem φ).resolve_right fun con => ?_
  rw [models_iff_not_satisfiable, Set.union_singleton, Set.insert_eq_of_mem con] at hφ
  exact hφ h.1
#align first_order.language.Theory.is_maximal.mem_of_models FirstOrder.Language.Theory.IsMaximal.mem_of_models

theorem IsMaximal.mem_iff_models (h : T.IsMaximal) (φ : L.Sentence) : φ ∈ T ↔ T ⊨ᵇ φ :=
  ⟨models_sentence_of_mem, h.mem_of_models⟩
#align first_order.language.Theory.is_maximal.mem_iff_models FirstOrder.Language.Theory.IsMaximal.mem_iff_models

/-- Two (bounded) formulas are semantically equivalent over a theory `T` when they have the same
interpretation in every model of `T`. (This is also known as logical equivalence, which also has a
proof-theoretic definition.) -/
def SemanticallyEquivalent (T : L.Theory) (φ ψ : L.BoundedFormula α n) : Prop :=
  T ⊨ᵇ φ.iff ψ
#align first_order.language.Theory.semantically_equivalent FirstOrder.Language.Theory.SemanticallyEquivalent

@[refl]
theorem SemanticallyEquivalent.refl (φ : L.BoundedFormula α n) : T.SemanticallyEquivalent φ φ :=
  fun M v xs => by rw [BoundedFormula.realize_iff]
#align first_order.language.Theory.semantically_equivalent.refl FirstOrder.Language.Theory.SemanticallyEquivalent.refl

instance : IsRefl (L.BoundedFormula α n) T.SemanticallyEquivalent :=
  ⟨SemanticallyEquivalent.refl⟩

@[symm]
theorem SemanticallyEquivalent.symm {φ ψ : L.BoundedFormula α n}
    (h : T.SemanticallyEquivalent φ ψ) : T.SemanticallyEquivalent ψ φ := fun M v xs => by
  rw [BoundedFormula.realize_iff, Iff.comm, ← BoundedFormula.realize_iff]
  exact h M v xs
#align first_order.language.Theory.semantically_equivalent.symm FirstOrder.Language.Theory.SemanticallyEquivalent.symm

@[trans]
theorem SemanticallyEquivalent.trans {φ ψ θ : L.BoundedFormula α n}
    (h1 : T.SemanticallyEquivalent φ ψ) (h2 : T.SemanticallyEquivalent ψ θ) :
    T.SemanticallyEquivalent φ θ := fun M v xs => by
  have h1' := h1 M v xs
  have h2' := h2 M v xs
  rw [BoundedFormula.realize_iff] at *
  exact ⟨h2'.1 ∘ h1'.1, h1'.2 ∘ h2'.2⟩
#align first_order.language.Theory.semantically_equivalent.trans FirstOrder.Language.Theory.SemanticallyEquivalent.trans

theorem SemanticallyEquivalent.realize_bd_iff {φ ψ : L.BoundedFormula α n} {M : Type max u v}
    [Nonempty M] [L.Structure M] [T.Model M] (h : T.SemanticallyEquivalent φ ψ)
    {v : α → M} {xs : Fin n → M} : φ.Realize v xs ↔ ψ.Realize v xs :=
  BoundedFormula.realize_iff.1 (h (ModelType.of T M) v xs)
#align first_order.language.Theory.semantically_equivalent.realize_bd_iff FirstOrder.Language.Theory.SemanticallyEquivalent.realize_bd_iff

theorem SemanticallyEquivalent.realize_iff {φ ψ : L.Formula α} {M : Type max u v} [Nonempty M]
    [L.Structure M] (_hM : T.Model M) (h : T.SemanticallyEquivalent φ ψ) {v : α → M} :
    φ.Realize v ↔ ψ.Realize v :=
  h.realize_bd_iff
#align first_order.language.Theory.semantically_equivalent.realize_iff FirstOrder.Language.Theory.SemanticallyEquivalent.realize_iff

/-- Semantic equivalence forms an equivalence relation on formulas. -/
def semanticallyEquivalentSetoid (T : L.Theory) : Setoid (L.BoundedFormula α n) where
  r := SemanticallyEquivalent T
  iseqv := ⟨fun _ => refl _, fun {_ _} h => h.symm, fun {_ _ _} h1 h2 => h1.trans h2⟩
#align first_order.language.Theory.semantically_equivalent_setoid FirstOrder.Language.Theory.semanticallyEquivalentSetoid

protected theorem SemanticallyEquivalent.all {φ ψ : L.BoundedFormula α (n + 1)}
    (h : T.SemanticallyEquivalent φ ψ) : T.SemanticallyEquivalent φ.all ψ.all := by
  simp_rw [SemanticallyEquivalent, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_all]
  exact fun M v xs => forall_congr' fun a => h.realize_bd_iff
#align first_order.language.Theory.semantically_equivalent.all FirstOrder.Language.Theory.SemanticallyEquivalent.all

protected theorem SemanticallyEquivalent.ex {φ ψ : L.BoundedFormula α (n + 1)}
    (h : T.SemanticallyEquivalent φ ψ) : T.SemanticallyEquivalent φ.ex ψ.ex := by
  simp_rw [SemanticallyEquivalent, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_ex]
  exact fun M v xs => exists_congr fun a => h.realize_bd_iff
#align first_order.language.Theory.semantically_equivalent.ex FirstOrder.Language.Theory.SemanticallyEquivalent.ex

protected theorem SemanticallyEquivalent.not {φ ψ : L.BoundedFormula α n}
    (h : T.SemanticallyEquivalent φ ψ) : T.SemanticallyEquivalent φ.not ψ.not := by
  simp_rw [SemanticallyEquivalent, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_not]
  exact fun M v xs => not_congr h.realize_bd_iff
#align first_order.language.Theory.semantically_equivalent.not FirstOrder.Language.Theory.SemanticallyEquivalent.not

protected theorem SemanticallyEquivalent.imp {φ ψ φ' ψ' : L.BoundedFormula α n}
    (h : T.SemanticallyEquivalent φ ψ) (h' : T.SemanticallyEquivalent φ' ψ') :
    T.SemanticallyEquivalent (φ.imp φ') (ψ.imp ψ') := by
  simp_rw [SemanticallyEquivalent, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_imp]
  exact fun M v xs => imp_congr h.realize_bd_iff h'.realize_bd_iff
#align first_order.language.Theory.semantically_equivalent.imp FirstOrder.Language.Theory.SemanticallyEquivalent.imp

end Theory

namespace completeTheory

variable (L) (M : Type w)
variable [L.Structure M]

theorem isSatisfiable [Nonempty M] : (L.completeTheory M).IsSatisfiable :=
  Theory.Model.isSatisfiable M
#align first_order.language.complete_theory.is_satisfiable FirstOrder.Language.completeTheory.isSatisfiable

theorem mem_or_not_mem (φ : L.Sentence) : φ ∈ L.completeTheory M ∨ φ.not ∈ L.completeTheory M := by
  simp_rw [completeTheory, Set.mem_setOf_eq, Sentence.Realize, Formula.realize_not, or_not]
#align first_order.language.complete_theory.mem_or_not_mem FirstOrder.Language.completeTheory.mem_or_not_mem

theorem isMaximal [Nonempty M] : (L.completeTheory M).IsMaximal :=
  ⟨isSatisfiable L M, mem_or_not_mem L M⟩
#align first_order.language.complete_theory.is_maximal FirstOrder.Language.completeTheory.isMaximal

theorem isComplete [Nonempty M] : (L.completeTheory M).IsComplete :=
  (completeTheory.isMaximal L M).isComplete
#align first_order.language.complete_theory.is_complete FirstOrder.Language.completeTheory.isComplete

end completeTheory

namespace BoundedFormula

variable (φ ψ : L.BoundedFormula α n)

theorem semanticallyEquivalent_not_not : T.SemanticallyEquivalent φ φ.not.not := fun M v xs => by
  simp
#align first_order.language.bounded_formula.semantically_equivalent_not_not FirstOrder.Language.BoundedFormula.semanticallyEquivalent_not_not

theorem imp_semanticallyEquivalent_not_sup : T.SemanticallyEquivalent (φ.imp ψ) (φ.not ⊔ ψ) :=
  fun M v xs => by simp [imp_iff_not_or]
#align first_order.language.bounded_formula.imp_semantically_equivalent_not_sup FirstOrder.Language.BoundedFormula.imp_semanticallyEquivalent_not_sup

theorem sup_semanticallyEquivalent_not_inf_not :
    T.SemanticallyEquivalent (φ ⊔ ψ) (φ.not ⊓ ψ.not).not := fun M v xs => by simp [imp_iff_not_or]
#align first_order.language.bounded_formula.sup_semantically_equivalent_not_inf_not FirstOrder.Language.BoundedFormula.sup_semanticallyEquivalent_not_inf_not

theorem inf_semanticallyEquivalent_not_sup_not :
    T.SemanticallyEquivalent (φ ⊓ ψ) (φ.not ⊔ ψ.not).not := fun M v xs => by
  simp
#align first_order.language.bounded_formula.inf_semantically_equivalent_not_sup_not FirstOrder.Language.BoundedFormula.inf_semanticallyEquivalent_not_sup_not

theorem all_semanticallyEquivalent_not_ex_not (φ : L.BoundedFormula α (n + 1)) :
    T.SemanticallyEquivalent φ.all φ.not.ex.not := fun M v xs => by simp
#align first_order.language.bounded_formula.all_semantically_equivalent_not_ex_not FirstOrder.Language.BoundedFormula.all_semanticallyEquivalent_not_ex_not

theorem ex_semanticallyEquivalent_not_all_not (φ : L.BoundedFormula α (n + 1)) :
    T.SemanticallyEquivalent φ.ex φ.not.all.not := fun M v xs => by simp
#align first_order.language.bounded_formula.ex_semantically_equivalent_not_all_not FirstOrder.Language.BoundedFormula.ex_semanticallyEquivalent_not_all_not

theorem semanticallyEquivalent_all_liftAt : T.SemanticallyEquivalent φ (φ.liftAt 1 n).all :=
  fun M v xs => by
  rw [realize_iff, realize_all_liftAt_one_self]
#align first_order.language.bounded_formula.semantically_equivalent_all_lift_at FirstOrder.Language.BoundedFormula.semanticallyEquivalent_all_liftAt

end BoundedFormula

namespace Formula

variable (φ ψ : L.Formula α)

theorem semanticallyEquivalent_not_not : T.SemanticallyEquivalent φ φ.not.not :=
  BoundedFormula.semanticallyEquivalent_not_not φ
#align first_order.language.formula.semantically_equivalent_not_not FirstOrder.Language.Formula.semanticallyEquivalent_not_not

theorem imp_semanticallyEquivalent_not_sup : T.SemanticallyEquivalent (φ.imp ψ) (φ.not ⊔ ψ) :=
  BoundedFormula.imp_semanticallyEquivalent_not_sup φ ψ
#align first_order.language.formula.imp_semantically_equivalent_not_sup FirstOrder.Language.Formula.imp_semanticallyEquivalent_not_sup

theorem sup_semanticallyEquivalent_not_inf_not :
    T.SemanticallyEquivalent (φ ⊔ ψ) (φ.not ⊓ ψ.not).not :=
  BoundedFormula.sup_semanticallyEquivalent_not_inf_not φ ψ
#align first_order.language.formula.sup_semantically_equivalent_not_inf_not FirstOrder.Language.Formula.sup_semanticallyEquivalent_not_inf_not

theorem inf_semanticallyEquivalent_not_sup_not :
    T.SemanticallyEquivalent (φ ⊓ ψ) (φ.not ⊔ ψ.not).not :=
  BoundedFormula.inf_semanticallyEquivalent_not_sup_not φ ψ
#align first_order.language.formula.inf_semantically_equivalent_not_sup_not FirstOrder.Language.Formula.inf_semanticallyEquivalent_not_sup_not

end Formula

namespace BoundedFormula

theorem IsQF.induction_on_sup_not {P : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n}
    (h : IsQF φ) (hf : P (⊥ : L.BoundedFormula α n))
    (ha : ∀ ψ : L.BoundedFormula α n, IsAtomic ψ → P ψ)
    (hsup : ∀ {φ₁ φ₂}, P φ₁ → P φ₂ → P (φ₁ ⊔ φ₂)) (hnot : ∀ {φ}, P φ → P φ.not)
    (hse :
      ∀ {φ₁ φ₂ : L.BoundedFormula α n}, Theory.SemanticallyEquivalent ∅ φ₁ φ₂ → (P φ₁ ↔ P φ₂)) :
    P φ :=
  IsQF.recOn h hf @(ha) fun {φ₁ φ₂} _ _ h1 h2 =>
    (hse (φ₁.imp_semanticallyEquivalent_not_sup φ₂)).2 (hsup (hnot h1) h2)
#align first_order.language.bounded_formula.is_qf.induction_on_sup_not FirstOrder.Language.BoundedFormula.IsQF.induction_on_sup_not

theorem IsQF.induction_on_inf_not {P : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n}
    (h : IsQF φ) (hf : P (⊥ : L.BoundedFormula α n))
    (ha : ∀ ψ : L.BoundedFormula α n, IsAtomic ψ → P ψ)
    (hinf : ∀ {φ₁ φ₂}, P φ₁ → P φ₂ → P (φ₁ ⊓ φ₂)) (hnot : ∀ {φ}, P φ → P φ.not)
    (hse :
      ∀ {φ₁ φ₂ : L.BoundedFormula α n}, Theory.SemanticallyEquivalent ∅ φ₁ φ₂ → (P φ₁ ↔ P φ₂)) :
    P φ :=
  h.induction_on_sup_not hf ha
    (fun {φ₁ φ₂} h1 h2 =>
      (hse (φ₁.sup_semanticallyEquivalent_not_inf_not φ₂)).2 (hnot (hinf (hnot h1) (hnot h2))))
    (fun {_} => hnot) fun {_ _} => hse
#align first_order.language.bounded_formula.is_qf.induction_on_inf_not FirstOrder.Language.BoundedFormula.IsQF.induction_on_inf_not

theorem semanticallyEquivalent_toPrenex (φ : L.BoundedFormula α n) :
    (∅ : L.Theory).SemanticallyEquivalent φ φ.toPrenex := fun M v xs => by
  rw [realize_iff, realize_toPrenex]
#align first_order.language.bounded_formula.semantically_equivalent_to_prenex FirstOrder.Language.BoundedFormula.semanticallyEquivalent_toPrenex

theorem induction_on_all_ex {P : ∀ {m}, L.BoundedFormula α m → Prop} (φ : L.BoundedFormula α n)
    (hqf : ∀ {m} {ψ : L.BoundedFormula α m}, IsQF ψ → P ψ)
    (hall : ∀ {m} {ψ : L.BoundedFormula α (m + 1)}, P ψ → P ψ.all)
    (hex : ∀ {m} {φ : L.BoundedFormula α (m + 1)}, P φ → P φ.ex)
    (hse : ∀ {m} {φ₁ φ₂ : L.BoundedFormula α m},
      Theory.SemanticallyEquivalent ∅ φ₁ φ₂ → (P φ₁ ↔ P φ₂)) :
    P φ := by
  suffices h' : ∀ {m} {φ : L.BoundedFormula α m}, φ.IsPrenex → P φ from
    (hse φ.semanticallyEquivalent_toPrenex).2 (h' φ.toPrenex_isPrenex)
  intro m φ hφ
  induction' hφ with _ _ hφ _ _ _ hφ _ _ _ hφ
  · exact hqf hφ
  · exact hall hφ
  · exact hex hφ
#align first_order.language.bounded_formula.induction_on_all_ex FirstOrder.Language.BoundedFormula.induction_on_all_ex

theorem induction_on_exists_not {P : ∀ {m}, L.BoundedFormula α m → Prop} (φ : L.BoundedFormula α n)
    (hqf : ∀ {m} {ψ : L.BoundedFormula α m}, IsQF ψ → P ψ)
    (hnot : ∀ {m} {φ : L.BoundedFormula α m}, P φ → P φ.not)
    (hex : ∀ {m} {φ : L.BoundedFormula α (m + 1)}, P φ → P φ.ex)
    (hse : ∀ {m} {φ₁ φ₂ : L.BoundedFormula α m},
      Theory.SemanticallyEquivalent ∅ φ₁ φ₂ → (P φ₁ ↔ P φ₂)) :
    P φ :=
  φ.induction_on_all_ex (fun {_ _} => hqf)
    (fun {_ φ} hφ => (hse φ.all_semanticallyEquivalent_not_ex_not).2 (hnot (hex (hnot hφ))))
    (fun {_ _} => hex) fun {_ _ _} => hse
#align first_order.language.bounded_formula.induction_on_exists_not FirstOrder.Language.BoundedFormula.induction_on_exists_not

end BoundedFormula

end Language

end FirstOrder

namespace Cardinal

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} (κ : Cardinal.{w}) (T : L.Theory)

/-- A theory is `κ`-categorical if all models of size `κ` are isomorphic. -/
def Categorical : Prop :=
  ∀ M N : T.ModelType, #M = κ → #N = κ → Nonempty (M ≃[L] N)
#align cardinal.categorical Cardinal.Categorical

/-- The Łoś–Vaught Test : a criterion for categorical theories to be complete. -/
theorem Categorical.isComplete (h : κ.Categorical T) (h1 : ℵ₀ ≤ κ)
    (h2 : Cardinal.lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) (hS : T.IsSatisfiable)
    (hT : ∀ M : Theory.ModelType.{u, v, max u v} T, Infinite M) : T.IsComplete :=
  ⟨hS, fun φ => by
    obtain ⟨_, _⟩ := Theory.exists_model_card_eq ⟨hS.some, hT hS.some⟩ κ h1 h2
    rw [Theory.models_sentence_iff, Theory.models_sentence_iff]
    by_contra! con
    obtain ⟨⟨MF, hMF⟩, MT, hMT⟩ := con
    rw [Sentence.realize_not, Classical.not_not] at hMT
    refine hMF ?_
    haveI := hT MT
    haveI := hT MF
    obtain ⟨NT, MNT, hNT⟩ := exists_elementarilyEquivalent_card_eq L MT κ h1 h2
    obtain ⟨NF, MNF, hNF⟩ := exists_elementarilyEquivalent_card_eq L MF κ h1 h2
    obtain ⟨TF⟩ := h (MNT.toModel T) (MNF.toModel T) hNT hNF
    exact
      ((MNT.realize_sentence φ).trans
        ((TF.realize_sentence φ).trans (MNF.realize_sentence φ).symm)).1 hMT⟩
#align cardinal.categorical.is_complete Cardinal.Categorical.isComplete

theorem empty_theory_categorical (T : Language.empty.Theory) : κ.Categorical T := fun M N hM hN =>
  by rw [empty.nonempty_equiv_iff, hM, hN]
#align cardinal.empty_Theory_categorical Cardinal.empty_theory_categorical

theorem empty_infinite_Theory_isComplete : Language.empty.infiniteTheory.IsComplete :=
  (empty_theory_categorical.{0} ℵ₀ _).isComplete ℵ₀ _ le_rfl (by simp)
    ⟨Theory.Model.bundled ((model_infiniteTheory_iff Language.empty).2
      (inferInstanceAs (Infinite ℕ)))⟩ fun M =>
    (model_infiniteTheory_iff Language.empty).1 M.is_model
#align cardinal.empty_infinite_Theory_is_complete Cardinal.empty_infinite_Theory_isComplete

end Cardinal
