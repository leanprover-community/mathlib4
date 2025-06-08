/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.ModelTheory.Ultraproducts
import Mathlib.ModelTheory.Bundled
import Mathlib.ModelTheory.Skolem
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# First-Order Satisfiability

This file deals with the satisfiability of first-order theories, as well as equivalence over them.

## Main Definitions

- `FirstOrder.Language.Theory.IsSatisfiable`: `T.IsSatisfiable` indicates that `T` has a nonempty
  model.
- `FirstOrder.Language.Theory.IsFinitelySatisfiable`: `T.IsFinitelySatisfiable` indicates that
  every finite subset of `T` is satisfiable.
- `FirstOrder.Language.Theory.IsComplete`: `T.IsComplete` indicates that `T` is satisfiable and
  models each sentence or its negation.
- `Cardinal.Categorical`: A theory is `κ`-categorical if all models of size `κ` are isomorphic.

## Main Results

- The Compactness Theorem, `FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable`,
  shows that a theory is satisfiable iff it is finitely satisfiable.
- `FirstOrder.Language.completeTheory.isComplete`: The complete theory of a structure is
  complete.
- `FirstOrder.Language.Theory.exists_large_model_of_infinite_model` shows that any theory with an
  infinite model has arbitrarily large models.
- `FirstOrder.Language.Theory.exists_elementaryEmbedding_card_eq`: The Upward Löwenheim–Skolem
  Theorem: If `κ` is a cardinal greater than the cardinalities of `L` and an infinite `L`-structure
  `M`, then `M` has an elementary extension of cardinality `κ`.

## Implementation Details

- Satisfiability of an `L.Theory` `T` is defined in the minimal universe containing all the symbols
  of `L`. By Löwenheim-Skolem, this is equivalent to satisfiability in any universe.
-/



universe u v w w'

open Cardinal CategoryTheory

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {T : L.Theory} {α : Type w} {n : ℕ}

namespace Theory

variable (T)

/-- A theory is satisfiable if a structure models it. -/
def IsSatisfiable : Prop :=
  Nonempty (ModelType.{u, v, max u v} T)

/-- A theory is finitely satisfiable if all of its finite subtheories are satisfiable. -/
def IsFinitelySatisfiable : Prop :=
  ∀ T0 : Finset L.Sentence, (T0 : L.Theory) ⊆ T → IsSatisfiable (T0 : L.Theory)

variable {T} {T' : L.Theory}

theorem Model.isSatisfiable (M : Type w) [Nonempty M] [L.Structure M] [M ⊨ T] :
    T.IsSatisfiable :=
  ⟨((⊥ : Substructure _ (ModelType.of T M)).elementarySkolem₁Reduct.toModel T).shrink⟩

theorem IsSatisfiable.mono (h : T'.IsSatisfiable) (hs : T ⊆ T') : T.IsSatisfiable :=
  ⟨(Theory.Model.mono (ModelType.is_model h.some) hs).bundled⟩

theorem isSatisfiable_empty (L : Language.{u, v}) : IsSatisfiable (∅ : L.Theory) :=
  ⟨default⟩

theorem isSatisfiable_of_isSatisfiable_onTheory {L' : Language.{w, w'}} (φ : L →ᴸ L')
    (h : (φ.onTheory T).IsSatisfiable) : T.IsSatisfiable :=
  Model.isSatisfiable (h.some.reduct φ)

theorem isSatisfiable_onTheory_iff {L' : Language.{w, w'}} {φ : L →ᴸ L'} (h : φ.Injective) :
    (φ.onTheory T).IsSatisfiable ↔ T.IsSatisfiable := by
  classical
    refine ⟨isSatisfiable_of_isSatisfiable_onTheory φ, fun h' => ?_⟩
    haveI : Inhabited h'.some := Classical.inhabited_of_nonempty'
    exact Model.isSatisfiable (h'.some.defaultExpansion h)

theorem IsSatisfiable.isFinitelySatisfiable (h : T.IsSatisfiable) : T.IsFinitelySatisfiable :=
  fun _ => h.mono

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

theorem isSatisfiable_directed_union_iff {ι : Type*} [Nonempty ι] {T : ι → L.Theory}
    (h : Directed (· ⊆ ·) T) : Theory.IsSatisfiable (⋃ i, T i) ↔ ∀ i, (T i).IsSatisfiable := by
  refine ⟨fun h' i => h'.mono (Set.subset_iUnion _ _), fun h' => ?_⟩
  rw [isSatisfiable_iff_isFinitelySatisfiable, IsFinitelySatisfiable]
  intro T0 hT0
  obtain ⟨i, hi⟩ := h.exists_mem_subset_of_finset_subset_biUnion hT0
  exact (h' i).mono hi

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

/-- Any theory with an infinite model has arbitrarily large models. -/
theorem exists_large_model_of_infinite_model (T : L.Theory) (κ : Cardinal.{w}) (M : Type w')
    [L.Structure M] [M ⊨ T] [Infinite M] :
    ∃ N : ModelType.{_, _, max u v w} T, Cardinal.lift.{max u v w} κ ≤ #N := by
  obtain ⟨N⟩ :=
    isSatisfiable_union_distinctConstantsTheory_of_infinite T (Set.univ : Set κ.out) M
  refine ⟨(N.is_model.mono Set.subset_union_left).bundled.reduct _, ?_⟩
  haveI : N ⊨ distinctConstantsTheory _ _ := N.is_model.mono Set.subset_union_right
  rw [ModelType.reduct_Carrier, coe_of]
  refine _root_.trans (lift_le.2 (le_of_eq (Cardinal.mk_out κ).symm)) ?_
  rw [← mk_univ]
  refine
    (card_le_of_model_distinctConstantsTheory L Set.univ N).trans (lift_le.{max u v w}.1 ?_)
  rw [lift_lift]

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

section

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
      (hN0.trans (by rw [← lift_umax, lift_id]))
  letI := (lhomWithConstants L M).reduct N
  haveI h : N ⊨ L.elementaryDiagram M :=
    (NN0.theory_model_iff (L.elementaryDiagram M)).2 inferInstance
  refine ⟨Bundled.of N, ⟨?_⟩, hN⟩
  apply ElementaryEmbedding.ofModelsElementaryDiagram L M N

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

/-- A consequence of the Löwenheim–Skolem Theorem: If `κ` is a cardinal greater than the
cardinalities of `L` and an infinite `L`-structure `M`, then there is a structure of cardinality `κ`
elementarily equivalent to `M`. -/
theorem exists_elementarilyEquivalent_card_eq (M : Type w') [L.Structure M] [Infinite M]
    (κ : Cardinal.{w}) (h1 : ℵ₀ ≤ κ) (h2 : lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) :
    ∃ N : CategoryTheory.Bundled L.Structure, (M ≅[L] N) ∧ #N = κ := by
  obtain ⟨N, NM | MN, hNκ⟩ := exists_elementaryEmbedding_card_eq L M κ h1 h2
  · exact ⟨N, NM.some.elementarilyEquivalent.symm, hNκ⟩
  · exact ⟨N, MN.some.elementarilyEquivalent, hNκ⟩

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

variable (T)

/-- A theory models a (bounded) formula when any of its nonempty models realizes that formula on all
  inputs. -/
def ModelsBoundedFormula (φ : L.BoundedFormula α n) : Prop :=
  ∀ (M : ModelType.{u, v, max u v w} T) (v : α → M) (xs : Fin n → M), φ.Realize v xs

@[inherit_doc FirstOrder.Language.Theory.ModelsBoundedFormula]
infixl:51 " ⊨ᵇ " => ModelsBoundedFormula -- input using \|= or \vDash, but not using \models

variable {T}

theorem models_formula_iff {φ : L.Formula α} :
    T ⊨ᵇ φ ↔ ∀ (M : ModelType.{u, v, max u v w} T) (v : α → M), φ.Realize v :=
  forall_congr' fun _ => forall_congr' fun _ => Unique.forall_iff

theorem models_sentence_iff {φ : L.Sentence} : T ⊨ᵇ φ ↔ ∀ M : ModelType.{u, v, max u v} T, M ⊨ φ :=
  models_formula_iff.trans (forall_congr' fun _ => Unique.forall_iff)

theorem models_sentence_of_mem {φ : L.Sentence} (h : φ ∈ T) : T ⊨ᵇ φ :=
  models_sentence_iff.2 fun _ => realize_sentence_of_mem T h

theorem models_iff_not_satisfiable (φ : L.Sentence) : T ⊨ᵇ φ ↔ ¬IsSatisfiable (T ∪ {φ.not}) := by
  rw [models_sentence_iff, IsSatisfiable]
  refine
    ⟨fun h1 h2 =>
      (Sentence.realize_not _).1
        (realize_sentence_of_mem (T ∪ {Formula.not φ})
          (Set.subset_union_right (Set.mem_singleton _)))
        (h1 (h2.some.subtheoryModel Set.subset_union_left)),
      fun h M => ?_⟩
  contrapose! h
  rw [← Sentence.realize_not] at h
  refine
    ⟨{  Carrier := M
        is_model := ⟨fun ψ hψ => hψ.elim (realize_sentence_of_mem _) fun h' => ?_⟩ }⟩
  rw [Set.mem_singleton_iff.1 h']
  exact h

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

theorem models_formula_iff_onTheory_models_equivSentence {φ : L.Formula α} :
    T ⊨ᵇ φ ↔ (L.lhomWithConstants α).onTheory T ⊨ᵇ Formula.equivSentence φ := by
  refine ⟨fun h => models_sentence_iff.2 (fun M => ?_),
    fun h => models_formula_iff.2 (fun M v => ?_)⟩
  · letI := (L.lhomWithConstants α).reduct M
    have : (L.lhomWithConstants α).IsExpansionOn M := LHom.isExpansionOn_reduct _ _
      -- why doesn't that instance just work?
    rw [Formula.realize_equivSentence]
    have : M ⊨ T := (LHom.onTheory_model _ _).1 M.is_model -- why isn't M.is_model inferInstance?
    let M' := Theory.ModelType.of T M
    exact h M' (fun a => (L.con a : M)) _
  · letI : (constantsOn α).Structure M := constantsOn.structure v
    have : M ⊨ (L.lhomWithConstants α).onTheory T := (LHom.onTheory_model _ _).2 inferInstance
    exact (Formula.realize_equivSentence _ _).1 (h.realize_sentence M)

theorem ModelsBoundedFormula.realize_formula {φ : L.Formula α} (h : T ⊨ᵇ φ) (M : Type*)
    [L.Structure M] [M ⊨ T] [Nonempty M] {v : α → M} : φ.Realize v := by
  rw [models_formula_iff_onTheory_models_equivSentence] at h
  letI : (constantsOn α).Structure M := constantsOn.structure v
  have : M ⊨ (L.lhomWithConstants α).onTheory T := (LHom.onTheory_model _ _).2 inferInstance
  exact (Formula.realize_equivSentence _ _).1 (h.realize_sentence M)

theorem models_toFormula_iff {φ : L.BoundedFormula α n} : T ⊨ᵇ φ.toFormula ↔ T ⊨ᵇ φ := by
  refine ⟨fun h M v xs => ?_, ?_⟩
  · have h' : φ.toFormula.Realize (Sum.elim v xs) := h.realize_formula M
    simp only [BoundedFormula.realize_toFormula, Sum.elim_comp_inl, Sum.elim_comp_inr] at h'
    exact h'
  · simp only [models_formula_iff, BoundedFormula.realize_toFormula]
    exact fun h M v => h M _ _

theorem ModelsBoundedFormula.realize_boundedFormula
    {φ : L.BoundedFormula α n} (h : T ⊨ᵇ φ) (M : Type*)
    [L.Structure M] [M ⊨ T] [Nonempty M] {v : α → M} {xs : Fin n → M} : φ.Realize v xs := by
  have h' : φ.toFormula.Realize (Sum.elim v xs) := (models_toFormula_iff.2 h).realize_formula M
  simp only [BoundedFormula.realize_toFormula, Sum.elim_comp_inl, Sum.elim_comp_inr] at h'
  exact h'

theorem models_of_models_theory {T' : L.Theory}
    (h : ∀ φ : L.Sentence, φ ∈ T' → T ⊨ᵇ φ)
    {φ : L.Formula α} (hφ : T' ⊨ᵇ φ) : T ⊨ᵇ φ := fun M => by
  have hM : M ⊨ T' := T'.model_iff.2 (fun ψ hψ => (h ψ hψ).realize_sentence M)
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

namespace IsComplete

theorem models_not_iff (h : T.IsComplete) (φ : L.Sentence) : T ⊨ᵇ φ.not ↔ ¬T ⊨ᵇ φ := by
  rcases h.2 φ with hφ | hφn
  · simp only [hφ, not_true, iff_false]
    rw [models_sentence_iff, not_forall]
    refine ⟨h.1.some, ?_⟩
    simp only [Sentence.realize_not, Classical.not_not]
    exact models_sentence_iff.1 hφ _
  · simp only [hφn, true_iff]
    intro hφ
    rw [models_sentence_iff] at *
    exact hφn h.1.some (hφ _)

theorem realize_sentence_iff (h : T.IsComplete) (φ : L.Sentence) (M : Type*) [L.Structure M]
    [M ⊨ T] [Nonempty M] : M ⊨ φ ↔ T ⊨ᵇ φ := by
  rcases h.2 φ with hφ | hφn
  · exact iff_of_true (hφ.realize_sentence M) hφ
  · exact
      iff_of_false ((Sentence.realize_not M).1 (hφn.realize_sentence M))
        ((h.models_not_iff φ).1 hφn)

end IsComplete

/-- A theory is maximal when it is satisfiable and contains each sentence or its negation.
  Maximal theories are complete. -/
def IsMaximal (T : L.Theory) : Prop :=
  T.IsSatisfiable ∧ ∀ φ : L.Sentence, φ ∈ T ∨ φ.not ∈ T

theorem IsMaximal.isComplete (h : T.IsMaximal) : T.IsComplete :=
  h.imp_right (forall_imp fun _ => Or.imp models_sentence_of_mem models_sentence_of_mem)

theorem IsMaximal.mem_or_not_mem (h : T.IsMaximal) (φ : L.Sentence) : φ ∈ T ∨ φ.not ∈ T :=
  h.2 φ

theorem IsMaximal.mem_of_models (h : T.IsMaximal) {φ : L.Sentence} (hφ : T ⊨ᵇ φ) : φ ∈ T := by
  refine (h.mem_or_not_mem φ).resolve_right fun con => ?_
  rw [models_iff_not_satisfiable, Set.union_singleton, Set.insert_eq_of_mem con] at hφ
  exact hφ h.1

theorem IsMaximal.mem_iff_models (h : T.IsMaximal) (φ : L.Sentence) : φ ∈ T ↔ T ⊨ᵇ φ :=
  ⟨models_sentence_of_mem, h.mem_of_models⟩

end Theory

namespace completeTheory

variable (L) (M : Type w)
variable [L.Structure M]

theorem isSatisfiable [Nonempty M] : (L.completeTheory M).IsSatisfiable :=
  Theory.Model.isSatisfiable M

theorem mem_or_not_mem (φ : L.Sentence) : φ ∈ L.completeTheory M ∨ φ.not ∈ L.completeTheory M := by
  simp_rw [completeTheory, Set.mem_setOf_eq, Sentence.Realize, Formula.realize_not, or_not]

theorem isMaximal [Nonempty M] : (L.completeTheory M).IsMaximal :=
  ⟨isSatisfiable L M, mem_or_not_mem L M⟩

theorem isComplete [Nonempty M] : (L.completeTheory M).IsComplete :=
  (completeTheory.isMaximal L M).isComplete

end completeTheory

end Language

end FirstOrder

namespace Cardinal

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} (κ : Cardinal.{w}) (T : L.Theory)

/-- A theory is `κ`-categorical if all models of size `κ` are isomorphic. -/
def Categorical : Prop :=
  ∀ M N : T.ModelType, #M = κ → #N = κ → Nonempty (M ≃[L] N)

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
        ((StrongHomClass.realize_sentence TF φ).trans (MNF.realize_sentence φ).symm)).1 hMT⟩

theorem empty_theory_categorical (T : Language.empty.Theory) : κ.Categorical T := fun M N hM hN =>
  by rw [empty.nonempty_equiv_iff, hM, hN]

theorem empty_infinite_Theory_isComplete : Language.empty.infiniteTheory.IsComplete :=
  (empty_theory_categorical.{0} ℵ₀ _).isComplete ℵ₀ _ le_rfl (by simp)
    ⟨by
      haveI : Language.empty.Structure ℕ := emptyStructure
      exact ((model_infiniteTheory_iff Language.empty).2 (inferInstanceAs (Infinite ℕ))).bundled⟩
    fun M => (model_infiniteTheory_iff Language.empty).1 M.is_model

end Cardinal
