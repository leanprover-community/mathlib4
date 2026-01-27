/-
Copyright (c) 2018 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Junyan Xu
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.Noetherian.Orzech

/-! # Bases of modules and the Orzech property

It is shown in this file that any spanning set of a module over a ring satisfying the Orzech
property of cardinality not exceeding the rank of the module must be linearly independent,
and therefore is a basis.
-/

@[expose] public section

section Basis

open Module Submodule

variable {R M : Type*} [Semiring R] [OrzechProperty R] [AddCommMonoid M] [Module R M]

theorem linearIndependent_of_top_le_span_of_card_le_finrank {ι : Type*} [Fintype ι] {b : ι → M}
    (spans : ⊤ ≤ span R (Set.range b)) (card_le : Fintype.card ι ≤ finrank R M) :
    LinearIndependent R b := by
  rw [← Finsupp.range_linearCombination, top_le_iff, LinearMap.range_eq_top] at spans
  have := Module.Finite.of_surjective _ spans
  have ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank card_le
  exact OrzechProperty.injective_of_surjective_of_injective
    _ _ (hf.comp _ (Fintype.equivFin _).injective) spans

theorem linearIndependent_of_top_le_span_of_card_eq_finrank {ι : Type*} [Fintype ι] {b : ι → M}
    (spans : ⊤ ≤ span R (Set.range b)) (card_eq : Fintype.card ι = finrank R M) :
    LinearIndependent R b :=
  linearIndependent_of_top_le_span_of_card_le_finrank spans card_eq.le

/-- A finite family of vectors is linearly independent if and only if
its cardinality equals the dimension of its span. -/
theorem linearIndependent_iff_card_eq_finrank_span [Nontrivial R] {ι} [Fintype ι] {b : ι → M} :
    LinearIndependent R b ↔ Fintype.card ι = (Set.range b).finrank R where
  mp h := (finrank_span_eq_card h).symm
  mpr hc := by
    refine (LinearMap.linearIndependent_iff_of_injOn _ (subtype_injective _).injOn).mpr <|
      linearIndependent_of_top_le_span_of_card_eq_finrank (b := fun i ↦ ⟨b i, subset_span ⟨i, rfl⟩⟩)
        (fun ⟨_, _⟩ _ ↦ (subtype_injective _).mem_set_image.mp ?_) hc
    rwa [← map_coe, ← span_image, ← Set.range_comp]

theorem linearIndependent_iff_card_le_finrank_span [Nontrivial R] {ι} [Fintype ι] {b : ι → M} :
    LinearIndependent R b ↔ Fintype.card ι ≤ (Set.range b).finrank R := by
  rw [linearIndependent_iff_card_eq_finrank_span, (finrank_range_le_card _).ge_iff_eq']

/-- A family of `finrank R M` vectors forms a basis if they span the whole space,
provided `R` satisfies the Orzech property. -/
noncomputable def basisOfTopLeSpanOfCardEqFinrank {ι : Type*} [Fintype ι] (b : ι → M)
    (le_span : ⊤ ≤ span R (Set.range b)) (card_eq : Fintype.card ι = finrank R M) : Basis ι R M :=
  Basis.mk (linearIndependent_of_top_le_span_of_card_eq_finrank le_span card_eq) le_span

@[simp]
theorem coe_basisOfTopLeSpanOfCardEqFinrank {ι : Type*} [Fintype ι] (b : ι → M)
    (le_span : ⊤ ≤ span R (Set.range b)) (card_eq : Fintype.card ι = finrank R M) :
    ⇑(basisOfTopLeSpanOfCardEqFinrank b le_span card_eq) = b :=
  Basis.coe_mk _ _

/-- A finset of `finrank R M` vectors forms a basis if they span the whole space,
provided `R` satisfies the Orzech property. -/
@[simps! repr_apply]
noncomputable def finsetBasisOfTopLeSpanOfCardEqFinrank {s : Finset M}
    (le_span : ⊤ ≤ span R (s : Set M)) (card_eq : s.card = finrank R M) : Basis {x // x ∈ s} R M :=
  basisOfTopLeSpanOfCardEqFinrank ((↑) : ↥(s : Set M) → M)
    ((@Subtype.range_coe_subtype _ fun x => x ∈ s).symm ▸ le_span)
    (_root_.trans (Fintype.card_coe _) card_eq)

/-- A set of `finrank R M` vectors forms a basis if they span the whole space,
provided `R` satisfies the Orzech property. -/
@[simps! repr_apply]
noncomputable def setBasisOfTopLeSpanOfCardEqFinrank {s : Set M} [Fintype s]
    (le_span : ⊤ ≤ span R s) (card_eq : s.toFinset.card = finrank R M) : Basis s R M :=
  basisOfTopLeSpanOfCardEqFinrank ((↑) : s → M) ((@Subtype.range_coe_subtype _ s).symm ▸ le_span)
    (_root_.trans s.toFinset_card.symm card_eq)

end Basis
