/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen,
Kim Morrison, Chris Hughes, Anne Baanen, Junyan Xu
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Dimension of vector spaces

In this file we provide results about `Module.rank` and `Module.finrank` of vector spaces
over division rings.

## Main statements

For vector spaces (i.e. modules over a field), we have

* `rank_quotient_add_rank_of_divisionRing`: if `V₁` is a submodule of `V`, then
  `Module.rank (V/V₁) + Module.rank V₁ = Module.rank V`.
* `rank_range_add_rank_ker`: the rank-nullity theorem.

See also `Mathlib/LinearAlgebra/Dimension/ErdosKaplansky.lean` for the Erdős-Kaplansky theorem.

-/

@[expose] public section


noncomputable section

universe u₀ u v v' v'' u₁' w w'

variable {K R : Type u} {M V V₁ V₂ V₃ : Type v} {V' V'₁ : Type v'} {V'' : Type v''}
variable {ι : Type w} {ι' : Type w'} {η : Type u₁'} {φ : η → Type*}

open Cardinal Basis Submodule Function Set

section Module

section DivisionRing

variable [DivisionRing K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup V'] [Module K V']
variable [AddCommGroup V₁] [Module K V₁]

/-- If a vector space has a finite dimension, the index set of `Basis.ofVectorSpace` is finite. -/
theorem Module.Basis.finite_ofVectorSpaceIndex_of_rank_lt_aleph0 (h : Module.rank K V < ℵ₀) :
    (Basis.ofVectorSpaceIndex K V).Finite :=
  Set.finite_def.2 <| (Basis.ofVectorSpace K V).nonempty_fintype_index_of_rank_lt_aleph0 h

/-- Also see `rank_quotient_add_rank`. -/
theorem rank_quotient_add_rank_of_divisionRing (p : Submodule K V) :
    Module.rank K (V ⧸ p) + Module.rank K p = Module.rank K V := by
  classical
    let ⟨f⟩ := quotient_prod_linearEquiv p
    exact rank_prod'.symm.trans f.rank_eq

instance DivisionRing.hasRankNullity : HasRankNullity.{u₀} K where
  rank_quotient_add_rank := rank_quotient_add_rank_of_divisionRing
  exists_set_linearIndependent V _ _ := by
    let b := Module.Free.chooseBasis K V
    refine ⟨range b, ?_, b.linearIndependent.linearIndepOn_id⟩
    rw [← lift_injective.eq_iff, mk_range_eq_of_injective b.injective,
      Module.Free.rank_eq_card_chooseBasisIndex]

section

variable [AddCommGroup V₂] [Module K V₂]
variable [AddCommGroup V₃] [Module K V₃]

open LinearMap

/-- This is mostly an auxiliary lemma for `Submodule.rank_sup_add_rank_inf_eq`. -/
theorem rank_add_rank_split (db : V₂ →ₗ[K] V) (eb : V₃ →ₗ[K] V) (cd : V₁ →ₗ[K] V₂)
    (ce : V₁ →ₗ[K] V₃) (hde : ⊤ ≤ LinearMap.range db ⊔ LinearMap.range eb) (hgd : ker cd = ⊥)
    (eq : db.comp cd = eb.comp ce) (eq₂ : ∀ d e, db d = eb e → ∃ c, cd c = d ∧ ce c = e) :
    Module.rank K V + Module.rank K V₁ = Module.rank K V₂ + Module.rank K V₃ := by
  have hf : Surjective (coprod db eb) := by
    rwa [← range_eq_top, range_coprod, eq_top_iff]
  conv =>
    rhs
    rw [← rank_prod', rank_eq_of_surjective hf]
  congr 1
  apply LinearEquiv.rank_eq
  let L : V₁ →ₗ[K] ker (coprod db eb) :=
    LinearMap.codRestrict _ (prod cd (-ce)) <| by
      simpa [add_eq_zero_iff_eq_neg] using LinearMap.ext_iff.1 eq
  refine LinearEquiv.ofBijective L ⟨?_, ?_⟩
  · rw [← ker_eq_bot, ker_codRestrict, ker_prod, hgd, bot_inf_eq]
  · rw [← range_eq_top, eq_top_iff, LinearMap.range_codRestrict, ← map_le_iff_le_comap,
      Submodule.map_top, range_subtype]
    rintro ⟨d, e⟩
    have h := eq₂ d (-e)
    simp only [add_eq_zero_iff_eq_neg, LinearMap.prod_apply, mem_ker,
      Prod.mk_inj, coprod_apply, map_neg, neg_apply, LinearMap.mem_range, Pi.prod] at h ⊢
    grind

end

end DivisionRing

end Module

section Basis

open Module

-- TODO: move this section to a new file `OrzechProperty.lean`.
variable [Semiring R] [OrzechProperty R] [AddCommMonoid M] [Module R M]

example (K) [DivisionRing K] : OrzechProperty K := inferInstance

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
        (fun ⟨x, hx⟩ _ ↦ (subtype_injective _).mem_set_image.mp ?_) hc
    rwa [← map_coe, ← span_image, ← range_comp]

theorem linearIndependent_iff_card_le_finrank_span [Nontrivial R] {ι} [Fintype ι] {b : ι → M} :
    LinearIndependent R b ↔ Fintype.card ι ≤ (Set.range b).finrank R := by
  rw [linearIndependent_iff_card_eq_finrank_span, (finrank_range_le_card _).ge_iff_eq']

/-- A family of `finrank R M` vectors forms a basis if they span the whole space,
if `R` satisfies the Orzech property. -/
noncomputable def basisOfTopLeSpanOfCardEqFinrank {ι : Type*} [Fintype ι] (b : ι → M)
    (le_span : ⊤ ≤ span R (Set.range b)) (card_eq : Fintype.card ι = finrank R M) : Basis ι R M :=
  Basis.mk (linearIndependent_of_top_le_span_of_card_eq_finrank le_span card_eq) le_span

@[simp]
theorem coe_basisOfTopLeSpanOfCardEqFinrank {ι : Type*} [Fintype ι] (b : ι → M)
    (le_span : ⊤ ≤ span R (Set.range b)) (card_eq : Fintype.card ι = finrank R M) :
    ⇑(basisOfTopLeSpanOfCardEqFinrank b le_span card_eq) = b :=
  Basis.coe_mk _ _

/-- A finset of `finrank R M` vectors forms a basis if they span the whole space. -/
@[simps! repr_apply]
noncomputable def finsetBasisOfTopLeSpanOfCardEqFinrank {s : Finset M}
    (le_span : ⊤ ≤ span R (s : Set M)) (card_eq : s.card = finrank R M) : Basis {x // x ∈ s} R M :=
  basisOfTopLeSpanOfCardEqFinrank ((↑) : ↥(s : Set M) → M)
    ((@Subtype.range_coe_subtype _ fun x => x ∈ s).symm ▸ le_span)
    (_root_.trans (Fintype.card_coe _) card_eq)

/-- A set of `finrank R M` vectors forms a basis if they span the whole space. -/
@[simps! repr_apply]
noncomputable def setBasisOfTopLeSpanOfCardEqFinrank {s : Set M} [Fintype s]
    (le_span : ⊤ ≤ span R s) (card_eq : s.toFinset.card = finrank R M) : Basis s R M :=
  basisOfTopLeSpanOfCardEqFinrank ((↑) : s → M) ((@Subtype.range_coe_subtype _ s).symm ▸ le_span)
    (_root_.trans s.toFinset_card.symm card_eq)

end Basis
