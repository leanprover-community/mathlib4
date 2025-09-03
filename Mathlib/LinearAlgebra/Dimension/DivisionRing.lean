/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen,
Kim Morrison, Chris Hughes, Anne Baanen, Junyan Xu
-/
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.RankNullity

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


noncomputable section

universe u₀ u v v' v'' u₁' w w'

variable {K R : Type u} {V V₁ V₂ V₃ : Type v} {V' V'₁ : Type v'} {V'' : Type v''}
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
  · rw [← range_eq_top, eq_top_iff, range_codRestrict, ← map_le_iff_le_comap,
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

variable [DivisionRing K] [AddCommGroup V] [Module K V]

theorem linearIndependent_of_top_le_span_of_card_eq_finrank {ι : Type*} [Fintype ι] {b : ι → V}
    (spans : ⊤ ≤ span K (Set.range b)) (card_eq : Fintype.card ι = finrank K V) :
    LinearIndependent K b :=
  linearIndependent_iff'.mpr fun s g dependent i i_mem_s => by
    classical
    by_contra gx_ne_zero
    -- We'll derive a contradiction by showing `b '' (univ \ {i})` of cardinality `n - 1`
    -- spans a vector space of dimension `n`.
    refine not_le_of_gt (span_lt_top_of_card_lt_finrank
      (show (b '' (Set.univ \ {i})).toFinset.card < finrank K V from ?_)) ?_
    · calc
        (b '' (Set.univ \ {i})).toFinset.card = ((Set.univ \ {i}).toFinset.image b).card := by
          rw [Set.toFinset_card, Fintype.card_ofFinset]
        _ ≤ (Set.univ \ {i}).toFinset.card := Finset.card_image_le
        _ = (Finset.univ.erase i).card := (congr_arg Finset.card (Finset.ext (by simp [and_comm])))
        _ < Finset.univ.card := Finset.card_erase_lt_of_mem (Finset.mem_univ i)
        _ = finrank K V := card_eq
    -- We already have that `b '' univ` spans the whole space,
    -- so we only need to show that the span of `b '' (univ \ {i})` contains each `b j`.
    refine spans.trans (span_le.mpr ?_)
    rintro _ ⟨j, rfl, rfl⟩
    -- The case that `j ≠ i` is easy because `b j ∈ b '' (univ \ {i})`.
    by_cases j_eq : j = i
    swap
    · refine subset_span ⟨j, (Set.mem_diff _).mpr ⟨Set.mem_univ _, ?_⟩, rfl⟩
      exact mt Set.mem_singleton_iff.mp j_eq
    -- To show `b i ∈ span (b '' (univ \ {i}))`, we use that it's a weighted sum
    -- of the other `b j`s.
    rw [j_eq, SetLike.mem_coe, show b i = -((g i)⁻¹ • (s.erase i).sum fun j => g j • b j) from _]
    · refine neg_mem (smul_mem _ _ (sum_mem fun k hk => ?_))
      obtain ⟨k_ne_i, _⟩ := Finset.mem_erase.mp hk
      refine smul_mem _ _ (subset_span ⟨k, ?_, rfl⟩)
      simp_all only [Set.mem_univ, Set.mem_diff, Set.mem_singleton_iff, and_self, not_false_eq_true]
    -- To show `b i` is a weighted sum of the other `b j`s, we'll rewrite this sum
    -- to have the form of the assumption `dependent`.
    apply eq_neg_of_add_eq_zero_left
    calc
      (b i + (g i)⁻¹ • (s.erase i).sum fun j => g j • b j) =
          (g i)⁻¹ • (g i • b i + (s.erase i).sum fun j => g j • b j) := by
        rw [smul_add, ← mul_smul, inv_mul_cancel₀ gx_ne_zero, one_smul]
      _ = (g i)⁻¹ • (0 : V) := congr_arg _ ?_
      _ = 0 := smul_zero _
    -- And then it's just a bit of manipulation with finite sums.
    rwa [← Finset.insert_erase i_mem_s, Finset.sum_insert (Finset.notMem_erase _ _)] at dependent

/-- A finite family of vectors is linearly independent if and only if
its cardinality equals the dimension of its span. -/
theorem linearIndependent_iff_card_eq_finrank_span {ι : Type*} [Fintype ι] {b : ι → V} :
    LinearIndependent K b ↔ Fintype.card ι = (Set.range b).finrank K := by
  constructor
  · intro h
    exact (finrank_span_eq_card h).symm
  · intro hc
    let f := Submodule.subtype (span K (Set.range b))
    let b' : ι → span K (Set.range b) := fun i =>
      ⟨b i, mem_span.2 fun p hp => hp (Set.mem_range_self _)⟩
    have hs : ⊤ ≤ span K (Set.range b') := by
      intro x
      have h : span K (f '' Set.range b') = map f (span K (Set.range b')) := span_image f
      have hf : f '' Set.range b' = Set.range b := by
        ext x
        simp [f, b', Set.mem_image, Set.mem_range]
      rw [hf] at h
      have hx : (x : V) ∈ span K (Set.range b) := x.property
      simp_rw [h] at hx
      simpa [f, mem_map] using hx
    have hi : LinearMap.ker f = ⊥ := ker_subtype _
    convert (linearIndependent_of_top_le_span_of_card_eq_finrank hs hc).map' _ hi

theorem linearIndependent_iff_card_le_finrank_span {ι : Type*} [Fintype ι] {b : ι → V} :
    LinearIndependent K b ↔ Fintype.card ι ≤ (Set.range b).finrank K := by
  rw [linearIndependent_iff_card_eq_finrank_span, (finrank_range_le_card _).ge_iff_eq']

/-- A family of `finrank K V` vectors forms a basis if they span the whole space. -/
noncomputable def basisOfTopLeSpanOfCardEqFinrank {ι : Type*} [Fintype ι] (b : ι → V)
    (le_span : ⊤ ≤ span K (Set.range b)) (card_eq : Fintype.card ι = finrank K V) : Basis ι K V :=
  Basis.mk (linearIndependent_of_top_le_span_of_card_eq_finrank le_span card_eq) le_span

@[simp]
theorem coe_basisOfTopLeSpanOfCardEqFinrank {ι : Type*} [Fintype ι] (b : ι → V)
    (le_span : ⊤ ≤ span K (Set.range b)) (card_eq : Fintype.card ι = finrank K V) :
    ⇑(basisOfTopLeSpanOfCardEqFinrank b le_span card_eq) = b :=
  Basis.coe_mk _ _

/-- A finset of `finrank K V` vectors forms a basis if they span the whole space. -/
@[simps! repr_apply]
noncomputable def finsetBasisOfTopLeSpanOfCardEqFinrank {s : Finset V}
    (le_span : ⊤ ≤ span K (s : Set V)) (card_eq : s.card = finrank K V) : Basis {x // x ∈ s} K V :=
  basisOfTopLeSpanOfCardEqFinrank ((↑) : ↥(s : Set V) → V)
    ((@Subtype.range_coe_subtype _ fun x => x ∈ s).symm ▸ le_span)
    (_root_.trans (Fintype.card_coe _) card_eq)

/-- A set of `finrank K V` vectors forms a basis if they span the whole space. -/
@[simps! repr_apply]
noncomputable def setBasisOfTopLeSpanOfCardEqFinrank {s : Set V} [Fintype s]
    (le_span : ⊤ ≤ span K s) (card_eq : s.toFinset.card = finrank K V) : Basis s K V :=
  basisOfTopLeSpanOfCardEqFinrank ((↑) : s → V) ((@Subtype.range_coe_subtype _ s).symm ▸ le_span)
    (_root_.trans s.toFinset_card.symm card_eq)

end Basis
