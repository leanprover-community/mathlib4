/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Algebra.Module.Zlattice
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.NumberTheory.NumberField.Embeddings
import Mathlib.NumberTheory.NumberField.FractionalIdeal

#align_import number_theory.number_field.canonical_embedding from "leanprover-community/mathlib"@"60da01b41bbe4206f05d34fd70c8dd7498717a30"

/-!
# Canonical embedding of a number field

The canonical embedding of a number field `K` of degree `n` is the ring homomorphism
`K →+* ℂ^n` that sends `x ∈ K` to `(φ_₁(x),...,φ_n(x))` where the `φ_i`'s are the complex
embeddings of `K`. Note that we do not choose an ordering of the embeddings, but instead map `K`
into the type `(K →+* ℂ) → ℂ` of `ℂ`-vectors indexed by the complex embeddings.

## Main definitions and results

* `NumberField.canonicalEmbedding`: the ring homomorphism `K →+* ((K →+* ℂ) → ℂ)` defined by
sending `x : K` to the vector `(φ x)` indexed by `φ : K →+* ℂ`.

* `NumberField.canonicalEmbedding.integerLattice.inter_ball_finite`: the intersection of the
image of the ring of integers by the canonical embedding and any ball centered at `0` of finite
radius is finite.

* `NumberField.mixedEmbedding`: the ring homomorphism from `K →+* ({ w // IsReal w } → ℝ) ×
({ w // IsComplex w } → ℂ)` that sends `x ∈ K` to `(φ_w x)_w` where `φ_w` is the embedding
associated to the infinite place `w`. In particular, if `w` is real then `φ_w : K →+* ℝ` and, if
`w` is complex, `φ_w` is an arbitrary choice between the two complex embeddings defining the place
`w`.

* `NumberField.mixedEmbedding.exists_ne_zero_mem_ringOfIntegers_lt`: let
`f : InfinitePlace K → ℝ≥0`, if the product `∏ w, f w` is large enough, then there exists a
nonzero algebraic integer `a` in `K` such that `w a < f w` for all infinite places `w`.

## Tags

number field, infinite places
-/

variable (K : Type*) [Field K]

namespace NumberField.canonicalEmbedding

open NumberField

/-- The canonical embedding of a number field `K` of degree `n` into `ℂ^n`. -/
def _root_.NumberField.canonicalEmbedding : K →+* ((K →+* ℂ) → ℂ) := Pi.ringHom fun φ => φ

theorem _root_.NumberField.canonicalEmbedding_injective [NumberField K] :
    Function.Injective (NumberField.canonicalEmbedding K) := RingHom.injective _

variable {K}

@[simp]
theorem apply_at (φ : K →+* ℂ) (x : K) : (NumberField.canonicalEmbedding K x) φ = φ x := rfl

open scoped ComplexConjugate

/-- The image of `canonicalEmbedding` lives in the `ℝ`-submodule of the `x ∈ ((K →+* ℂ) → ℂ)` such
that `conj x_φ = x_(conj φ)` for all `∀ φ : K →+* ℂ`. -/
theorem conj_apply {x : ((K →+* ℂ) → ℂ)} (φ : K →+* ℂ)
    (hx : x ∈ Submodule.span ℝ (Set.range (canonicalEmbedding K))) :
    conj (x φ) = x (ComplexEmbedding.conjugate φ) := by
  refine Submodule.span_induction hx ?_ ?_ (fun _ _ hx hy => ?_) (fun a _ hx => ?_)
  · rintro _ ⟨x, rfl⟩
    rw [apply_at, apply_at, ComplexEmbedding.conjugate_coe_eq]
  · rw [Pi.zero_apply, Pi.zero_apply, map_zero]
  · rw [Pi.add_apply, Pi.add_apply, map_add, hx, hy]
  · rw [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
    exact congrArg ((a : ℂ) * ·) hx

theorem nnnorm_eq [NumberField K] (x : K) :
    ‖canonicalEmbedding K x‖₊ = Finset.univ.sup (fun φ : K →+* ℂ => ‖φ x‖₊) := by
  simp_rw [Pi.nnnorm_def, apply_at]

theorem norm_le_iff [NumberField K] (x : K) (r : ℝ) :
    ‖canonicalEmbedding K x‖ ≤ r ↔ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ r := by
  obtain hr | hr := lt_or_le r 0
  · obtain ⟨φ⟩ := (inferInstance : Nonempty (K →+* ℂ))
    refine iff_of_false ?_ ?_
    exact (hr.trans_le (norm_nonneg _)).not_le
    exact fun h => hr.not_le (le_trans (norm_nonneg _) (h φ))
  · lift r to NNReal using hr
    simp_rw [← coe_nnnorm, nnnorm_eq, NNReal.coe_le_coe, Finset.sup_le_iff, Finset.mem_univ,
      forall_true_left]

variable (K)

/-- The image of `𝓞 K` as a subring of `ℂ^n`. -/
def integerLattice : Subring ((K →+* ℂ) → ℂ) :=
  (RingHom.range (algebraMap (𝓞 K) K)).map (canonicalEmbedding K)

theorem integerLattice.inter_ball_finite [NumberField K] (r : ℝ) :
    ((integerLattice K : Set ((K →+* ℂ) → ℂ)) ∩ Metric.closedBall 0 r).Finite := by
  obtain hr | _ := lt_or_le r 0
  · simp [Metric.closedBall_eq_empty.2 hr]
  · have heq : ∀ x, canonicalEmbedding K x ∈ Metric.closedBall 0 r ↔
        ∀ φ : K →+* ℂ, ‖φ x‖ ≤ r := by
      intro x; rw [← norm_le_iff, mem_closedBall_zero_iff]
    convert (Embeddings.finite_of_norm_le K ℂ r).image (canonicalEmbedding K)
    ext; constructor
    · rintro ⟨⟨_, ⟨x, rfl⟩, rfl⟩, hx⟩
      exact ⟨↑x, ⟨SetLike.coe_mem x, fun φ => (heq x).mp hx φ⟩, rfl⟩
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      exact ⟨⟨x, ⟨⟨x, hx1⟩, rfl⟩, rfl⟩, (heq x).mpr hx2⟩

open Module Fintype FiniteDimensional

/-- A `ℂ`-basis of `ℂ^n` that is also a `ℤ`-basis of the `integerLattice`. -/
noncomputable def latticeBasis [NumberField K] :
    Basis (Free.ChooseBasisIndex ℤ (𝓞 K)) ℂ ((K →+* ℂ) → ℂ) := by
  classical
  -- Let `B` be the canonical basis of `(K →+* ℂ) → ℂ`. We prove that the determinant of
  -- the image by `canonicalEmbedding` of the integral basis of `K` is nonzero. This
  -- will imply the result.
    let B := Pi.basisFun ℂ (K →+* ℂ)
    let e : (K →+* ℂ) ≃ Free.ChooseBasisIndex ℤ (𝓞 K) :=
      equivOfCardEq ((Embeddings.card K ℂ).trans (finrank_eq_card_basis (integralBasis K)))
    let M := B.toMatrix (fun i => canonicalEmbedding K (integralBasis K (e i)))
    suffices M.det ≠ 0 by
      rw [← isUnit_iff_ne_zero, ← Basis.det_apply, ← is_basis_iff_det] at this
      refine basisOfLinearIndependentOfCardEqFinrank
        ((linearIndependent_equiv e.symm).mpr this.1) ?_
      rw [← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, finrank_fintype_fun_eq_card,
        Embeddings.card]
  -- In order to prove that the determinant is nonzero, we show that it is equal to the
  -- square of the discriminant of the integral basis and thus it is not zero
    let N := Algebra.embeddingsMatrixReindex ℚ ℂ (fun i => integralBasis K (e i))
      RingHom.equivRatAlgHom
    rw [show M = N.transpose by { ext:2; rfl }]
    rw [Matrix.det_transpose, ← pow_ne_zero_iff two_ne_zero]
    convert (map_ne_zero_iff _ (algebraMap ℚ ℂ).injective).mpr
      (Algebra.discr_not_zero_of_basis ℚ (integralBasis K))
    rw [← Algebra.discr_reindex ℚ (integralBasis K) e.symm]
    exact (Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ
      (fun i => integralBasis K (e i)) RingHom.equivRatAlgHom).symm

@[simp]
theorem latticeBasis_apply [NumberField K] (i : Free.ChooseBasisIndex ℤ (𝓞 K)) :
    latticeBasis K i = (canonicalEmbedding K) (integralBasis K i) := by
  simp only [latticeBasis, integralBasis_apply, coe_basisOfLinearIndependentOfCardEqFinrank,
    Function.comp_apply, Equiv.apply_symm_apply]

theorem mem_span_latticeBasis [NumberField K] (x : (K →+* ℂ) → ℂ) :
    x ∈ Submodule.span ℤ (Set.range (latticeBasis K)) ↔ x ∈ canonicalEmbedding K '' (𝓞 K) := by
  have h₁ : Set.range (latticeBasis K) =
      (canonicalEmbedding K).toIntAlgHom.toLinearMap '' (Set.range (integralBasis K)) := by
    rw [← Set.range_comp]; exact congrArg Set.range (funext (fun i => latticeBasis_apply K i))
  have h₂ : (Submodule.span ℤ (Set.range (integralBasis K)) : Set K) = 𝓞 K := by
    ext; exact mem_span_integralBasis K
  rw [h₁, ← Submodule.map_span, ← SetLike.mem_coe, Submodule.map_coe, h₂, AlgHom.coe_toLinearMap,
    RingHom.coe_toIntAlgHom]

end NumberField.canonicalEmbedding

namespace NumberField.mixedEmbedding

open NumberField NumberField.InfinitePlace FiniteDimensional

/-- The space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K`. -/
local notation "E" K =>
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)

/-- The mixed embedding of a number field `K` of signature `(r₁, r₂)` into `ℝ^r₁ × ℂ^r₂`. -/
noncomputable def _root_.NumberField.mixedEmbedding : K →+* (E K) :=
  RingHom.prod (Pi.ringHom fun w => embedding_of_isReal w.prop)
    (Pi.ringHom fun w => w.val.embedding)

instance [NumberField K] : Nontrivial (E K) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  obtain hw | hw := w.isReal_or_isComplex
  · have : Nonempty {w : InfinitePlace K // IsReal w} := ⟨⟨w, hw⟩⟩
    exact nontrivial_prod_left
  · have : Nonempty {w : InfinitePlace K // IsComplex w} := ⟨⟨w, hw⟩⟩
    exact nontrivial_prod_right

protected theorem finrank [NumberField K] : finrank ℝ (E K) = finrank ℚ K := by
  classical
  rw [finrank_prod, finrank_pi, finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
    Finset.card_univ, ← NrRealPlaces, ← NrComplexPlaces, ← card_real_embeddings,
    Algebra.id.smul_eq_mul, mul_comm, ← card_complex_embeddings, ← NumberField.Embeddings.card K ℂ,
    Fintype.card_subtype_compl, Nat.add_sub_of_le (Fintype.card_subtype_le _)]

theorem _root_.NumberField.mixedEmbedding_injective [NumberField K] :
    Function.Injective (NumberField.mixedEmbedding K) := by
  exact RingHom.injective _

section commMap

/-- The linear map that makes `canonicalEmbedding` and `mixedEmbedding` commute, see
`commMap_canonical_eq_mixed`. -/
noncomputable def commMap : ((K →+* ℂ) → ℂ) →ₗ[ℝ] (E K) where
  toFun := fun x => ⟨fun w => (x w.val.embedding).re, fun w => x w.val.embedding⟩
  map_add' := by
    simp only [Pi.add_apply, Complex.add_re, Prod.mk_add_mk, Prod.mk.injEq]
    exact fun _ _ => ⟨rfl, rfl⟩
  map_smul' := by
    simp only [Pi.smul_apply, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, RingHom.id_apply, Prod.smul_mk, Prod.mk.injEq]
    exact fun _ _ => ⟨rfl, rfl⟩

theorem commMap_apply_of_isReal (x : (K →+* ℂ) → ℂ) {w : InfinitePlace K} (hw : IsReal w) :
    (commMap K x).1 ⟨w, hw⟩ = (x w.embedding).re := rfl

theorem commMap_apply_of_isComplex (x : (K →+* ℂ) → ℂ) {w : InfinitePlace K} (hw : IsComplex w) :
    (commMap K x).2 ⟨w, hw⟩ = x w.embedding := rfl

@[simp]
theorem commMap_canonical_eq_mixed (x : K) :
    commMap K (canonicalEmbedding K x) = mixedEmbedding K x := by
  simp only [canonicalEmbedding, commMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.ringHom_apply,
    mixedEmbedding, RingHom.prod_apply, Prod.mk.injEq]
  exact ⟨rfl, rfl⟩

/-- This is a technical result to ensure that the image of the `ℂ`-basis of `ℂ^n` defined in
`canonicalEmbedding.latticeBasis` is a `ℝ`-basis of `ℝ^r₁ × ℂ^r₂`,
see `mixedEmbedding.latticeBasis`. -/
theorem disjoint_span_commMap_ker [NumberField K] :
    Disjoint (Submodule.span ℝ (Set.range (canonicalEmbedding.latticeBasis K)))
      (LinearMap.ker (commMap K)) := by
  refine LinearMap.disjoint_ker.mpr (fun x h_mem h_zero => ?_)
  replace h_mem : x ∈ Submodule.span ℝ (Set.range (canonicalEmbedding K)) := by
    refine (Submodule.span_mono ?_) h_mem
    rintro _ ⟨i, rfl⟩
    exact ⟨integralBasis K i, (canonicalEmbedding.latticeBasis_apply K i).symm⟩
  ext1 φ
  rw [Pi.zero_apply]
  by_cases hφ : ComplexEmbedding.IsReal φ
  · apply Complex.ext
    · rw [← embedding_mk_eq_of_isReal hφ, ← commMap_apply_of_isReal K x ⟨φ, hφ, rfl⟩]
      exact congrFun (congrArg (fun x => x.1) h_zero) ⟨InfinitePlace.mk φ, _⟩
    · rw [Complex.zero_im, ← Complex.conj_eq_iff_im, canonicalEmbedding.conj_apply _ h_mem,
        ComplexEmbedding.isReal_iff.mp hφ]
  · have := congrFun (congrArg (fun x => x.2) h_zero) ⟨InfinitePlace.mk φ, ⟨φ, hφ, rfl⟩⟩
    cases embedding_mk_eq φ with
    | inl h => rwa [← h, ← commMap_apply_of_isComplex K x ⟨φ, hφ, rfl⟩]
    | inr h =>
        apply RingHom.injective (starRingEnd ℂ)
        rwa [canonicalEmbedding.conj_apply _ h_mem, ← h, map_zero,
          ← commMap_apply_of_isComplex K x ⟨φ, hφ, rfl⟩]

end commMap

noncomputable section stdBasis

open scoped Classical
open Complex MeasureTheory MeasureTheory.Measure Zspan Matrix BigOperators
  ComplexConjugate

variable [NumberField K]

/-- The type indexing the basis `stdBasis`. -/
abbrev index := {w : InfinitePlace K // IsReal w} ⊕ ({w : InfinitePlace K // IsComplex w}) × (Fin 2)

/-- The `ℝ`-basis of `({w // IsReal w} → ℝ) × ({ w // IsComplex w } → ℂ)` formed by the vector
equal to `1` at `w` and `0` elsewhere for `IsReal w` and by the couple of vectors equal to `1`
(resp. `I`) at `w` and `0` elsewhere for `IsComplex w`. -/
def stdBasis : Basis (index K) ℝ (E K) :=
  Basis.prod (Pi.basisFun ℝ _)
    (Basis.reindex (Pi.basis fun _ => basisOneI) (Equiv.sigmaEquivProd _ _))

variable {K}

@[simp]
theorem stdBasis_apply_ofIsReal (x : E K) (w : {w : InfinitePlace K // IsReal w}) :
    (stdBasis K).repr x (Sum.inl w) = x.1 w := rfl

@[simp]
theorem stdBasis_apply_ofIsComplex_fst (x : E K) (w : {w : InfinitePlace K // IsComplex w}) :
    (stdBasis K).repr x (Sum.inr ⟨w, 0⟩) = (x.2 w).re := rfl

@[simp]
theorem stdBasis_apply_ofIsComplex_snd (x : E K) (w : {w : InfinitePlace K // IsComplex w}) :
    (stdBasis K).repr x (Sum.inr ⟨w, 1⟩) = (x.2 w).im := rfl

variable (K)

theorem fundamentalDomain_stdBasis :
    fundamentalDomain (stdBasis K) =
        (Set.univ.pi fun _ => Set.Ico 0 1) ×ˢ
        (Set.univ.pi fun _ => Complex.measurableEquivPi⁻¹' (Set.univ.pi fun _ => Set.Ico 0 1)) := by
  ext
  simp [stdBasis, mem_fundamentalDomain, Complex.measurableEquivPi]

theorem volume_fundamentalDomain_stdBasis :
    volume (fundamentalDomain (stdBasis K)) = 1 := by
  rw [fundamentalDomain_stdBasis, volume_eq_prod, prod_prod, volume_pi, volume_pi, pi_pi, pi_pi,
    Complex.volume_preserving_equiv_pi.measure_preimage ?_, volume_pi, pi_pi, Real.volume_Ico,
    sub_zero, ENNReal.ofReal_one, Finset.prod_const_one, Finset.prod_const_one,
    Finset.prod_const_one, one_mul]
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)

/-- The `Equiv` between `index K` and `K →+* ℂ` defined by sending a real infinite place `w` to
the unique corresponding embedding `w.embedding`, and the pair `⟨w, 0⟩` (resp. `⟨w, 1⟩`) for a
complex infinite place `w` to `w.embedding` (resp. `conjugate w.embedding`). -/
def indexEquiv : (index K) ≃ (K →+* ℂ) := by
  refine Equiv.ofBijective (fun c => ?_)
    ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨?_, ?_⟩)
  · cases c with
    | inl w => exact w.val.embedding
    | inr wj => rcases wj with ⟨w, j⟩
                exact if j = 0 then w.val.embedding else ComplexEmbedding.conjugate w.val.embedding
  · intro φ
    by_cases hφ : ComplexEmbedding.IsReal φ
    · exact ⟨Sum.inl (InfinitePlace.mkReal ⟨φ, hφ⟩), by simp [embedding_mk_eq_of_isReal hφ]⟩
    · by_cases hw : (InfinitePlace.mk φ).embedding = φ
      · exact ⟨Sum.inr ⟨InfinitePlace.mkComplex ⟨φ, hφ⟩, 0⟩, by simp [hw]⟩
      · exact ⟨Sum.inr ⟨InfinitePlace.mkComplex ⟨φ, hφ⟩, 1⟩,
          by simp [(embedding_mk_eq φ).resolve_left hw]⟩
  · rw [Embeddings.card, ← mixedEmbedding.finrank K,
      ← FiniteDimensional.finrank_eq_card_basis (stdBasis K)]

variable {K}

@[simp]
theorem indexEquiv_apply_ofIsReal (w : {w : InfinitePlace K // IsReal w}) :
    (indexEquiv K) (Sum.inl w) = w.val.embedding := rfl

@[simp]
theorem indexEquiv_apply_ofIsComplex_fst (w : {w : InfinitePlace K // IsComplex w}) :
    (indexEquiv K) (Sum.inr ⟨w, 0⟩) = w.val.embedding := rfl

@[simp]
theorem indexEquiv_apply_ofIsComplex_snd (w : {w : InfinitePlace K // IsComplex w}) :
    (indexEquiv K) (Sum.inr ⟨w, 1⟩) = ComplexEmbedding.conjugate w.val.embedding := rfl

variable (K)

/-- The matrix that gives the representation on `stdBasis` of the image by `commMap` of an
element `x` of `(K →+* ℂ) → ℂ` fixed by the map `x_φ ↦ conj x_(conjugate φ)`,
see `stdBasis_repr_eq_matrixToStdBasis_mul`. -/
def matrixToStdBasis : Matrix (index K) (index K) ℂ :=
  fromBlocks (diagonal fun _ => 1) 0 0 <| reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)
    (blockDiagonal (fun _ => (2 : ℂ)⁻¹ • !![1, 1; - I, I]))

theorem det_matrixToStdBasis :
    (matrixToStdBasis K).det = (2⁻¹ * I) ^ NrComplexPlaces K :=
  calc
  _ = ∏ _k : { w : InfinitePlace K // IsComplex w }, det ((2 : ℂ)⁻¹ • !![1, 1; -I, I]) := by
      rw [matrixToStdBasis, det_fromBlocks_zero₂₁, det_diagonal, Finset.prod_const_one, one_mul,
          det_reindex_self, det_blockDiagonal]
  _ = ∏ _k : { w : InfinitePlace K // IsComplex w }, (2⁻¹ * Complex.I) := by
      refine Finset.prod_congr (Eq.refl _) (fun _ _ => ?_)
      field_simp; ring
  _ = (2⁻¹ * Complex.I) ^ Fintype.card {w : InfinitePlace K // IsComplex w} := by
      rw [Finset.prod_const, Fintype.card]

/-- Let `x : (K →+* ℂ) → ℂ` such that `x_φ = conj x_(conj φ)` for all `φ : K →+* ℂ`, then the
representation of `commMap K x` on `stdBasis` is given (up to reindexing) by the product of
`matrixToStdBasis` by `x`. -/
theorem stdBasis_repr_eq_matrixToStdBasis_mul (x : (K →+* ℂ) → ℂ)
    (hx : ∀ φ, conj (x φ) = x (ComplexEmbedding.conjugate φ)) (c : index K) :
    ((stdBasis K).repr (commMap K x) c : ℂ) =
      (matrixToStdBasis K *ᵥ (x ∘ (indexEquiv K))) c := by
  simp_rw [commMap, matrixToStdBasis, LinearMap.coe_mk, AddHom.coe_mk,
    mulVec, dotProduct, Function.comp_apply, index, Fintype.sum_sum_type,
    diagonal_one, reindex_apply, ← Finset.univ_product_univ, Finset.sum_product,
    indexEquiv_apply_ofIsReal, Fin.sum_univ_two, indexEquiv_apply_ofIsComplex_fst,
    indexEquiv_apply_ofIsComplex_snd, smul_of, smul_cons, smul_eq_mul,
    mul_one, smul_empty, Equiv.prodComm_symm, Equiv.coe_prodComm]
  cases c with
  | inl w =>
      simp_rw [stdBasis_apply_ofIsReal, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
        one_apply, Matrix.zero_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true, add_zero, Finset.sum_const_zero, add_zero,
        ← conj_eq_iff_re, hx (embedding w.val), conjugate_embedding_eq_of_isReal w.prop]
  | inr c =>
    rcases c with ⟨w, j⟩
    fin_cases j
    · simp_rw [Fin.mk_zero, stdBasis_apply_ofIsComplex_fst, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, Matrix.zero_apply, submatrix_apply,
        blockDiagonal_apply, Prod.swap_prod_mk, ite_mul, zero_mul, Finset.sum_const_zero,
        zero_add, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
        of_apply, cons_val', cons_val_zero, cons_val_one,
        head_cons, ← hx (embedding w), re_eq_add_conj]
      field_simp
    · simp_rw [Fin.mk_one, stdBasis_apply_ofIsComplex_snd, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, Matrix.zero_apply, submatrix_apply,
        blockDiagonal_apply, Prod.swap_prod_mk, ite_mul, zero_mul, Finset.sum_const_zero,
        zero_add, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
        of_apply, cons_val', cons_val_zero, cons_val_one,
        head_cons, ← hx (embedding w), im_eq_sub_conj]
      ring_nf; field_simp

end stdBasis

noncomputable section integerLattice

variable [NumberField K]

open Module FiniteDimensional Module.Free

open scoped nonZeroDivisors

/-- A `ℝ`-basis of `ℝ^r₁ × ℂ^r₂` that is also a `ℤ`-basis of the image of `𝓞 K`. -/
def latticeBasis :
    Basis (ChooseBasisIndex ℤ (𝓞 K)) ℝ (E K) := by
  classical
    -- We construct an `ℝ`-linear independent family from the image of
    -- `canonicalEmbedding.lattice_basis` by `commMap`
    have := LinearIndependent.map (LinearIndependent.restrict_scalars
      (by { simpa only [Complex.real_smul, mul_one] using Complex.ofReal_injective })
      (canonicalEmbedding.latticeBasis K).linearIndependent)
      (disjoint_span_commMap_ker K)
    -- and it's a basis since it has the right cardinality
    refine basisOfLinearIndependentOfCardEqFinrank this ?_
    rw [← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, finrank_prod, finrank_pi,
      finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
      ← NrRealPlaces, ← NrComplexPlaces, ← card_real_embeddings, Algebra.id.smul_eq_mul, mul_comm,
      ← card_complex_embeddings, ← NumberField.Embeddings.card K ℂ, Fintype.card_subtype_compl,
      Nat.add_sub_of_le (Fintype.card_subtype_le _)]

@[simp]
theorem latticeBasis_apply (i : ChooseBasisIndex ℤ (𝓞 K)) :
    latticeBasis K i = (mixedEmbedding K) (integralBasis K i) := by
  simp only [latticeBasis, coe_basisOfLinearIndependentOfCardEqFinrank, Function.comp_apply,
    canonicalEmbedding.latticeBasis_apply, integralBasis_apply, commMap_canonical_eq_mixed]

theorem mem_span_latticeBasis (x : (E K)) :
    x ∈ Submodule.span ℤ (Set.range (latticeBasis K)) ↔ x ∈ mixedEmbedding K '' (𝓞 K) := by
  have h₁ : Set.range (latticeBasis K) =
      (mixedEmbedding K).toIntAlgHom.toLinearMap '' (Set.range (integralBasis K)) := by
    rw [← Set.range_comp]; exact congrArg Set.range (funext (fun i => latticeBasis_apply K i))
  have h₂ : (Submodule.span ℤ (Set.range (integralBasis K)) : Set K) = 𝓞 K := by
    ext; exact mem_span_integralBasis K
  rw [h₁, ← Submodule.map_span, ← SetLike.mem_coe, Submodule.map_coe, h₂, AlgHom.coe_toLinearMap,
    RingHom.coe_toIntAlgHom]

theorem mem_rat_span_latticeBasis (x : K) :
    mixedEmbedding K x ∈ Submodule.span ℚ (Set.range (latticeBasis K)) := by
  rw [← Basis.sum_repr (integralBasis K) x, map_sum]
  simp_rw [map_rat_smul]
  refine Submodule.sum_smul_mem _ _ (fun i _ ↦ Submodule.subset_span ?_)
  rw [← latticeBasis_apply]
  exact Set.mem_range_self i

theorem latticeBasis_repr_apply (x : K) (i : ChooseBasisIndex ℤ (𝓞 K)) :
    (latticeBasis K).repr (mixedEmbedding K x) i = (integralBasis K).repr x i := by
  rw [← Basis.restrictScalars_repr_apply ℚ _ ⟨_, mem_rat_span_latticeBasis K x⟩, eq_ratCast,
    Rat.cast_inj]
  let f := (mixedEmbedding K).toRatAlgHom.toLinearMap.codRestrict _
    (fun x ↦ mem_rat_span_latticeBasis K x)
  suffices ((latticeBasis K).restrictScalars ℚ).repr.toLinearMap ∘ₗ f =
    (integralBasis K).repr.toLinearMap from DFunLike.congr_fun (LinearMap.congr_fun this x) i
  refine Basis.ext (integralBasis K) (fun i ↦ ?_)
  have : f (integralBasis K i) = ((latticeBasis K).restrictScalars ℚ) i := by
    apply Subtype.val_injective
    rw [LinearMap.codRestrict_apply, AlgHom.toLinearMap_apply, Basis.restrictScalars_apply,
      latticeBasis_apply, RingHom.toRatAlgHom_apply]
  simp_rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this, Basis.repr_self]

variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The generalized index of the lattice generated by `I` in the lattice generated by
`𝓞 K` is equal to the norm of the ideal `I`. The result is stated in terms of base change
determinant and is the translation of `NumberField.det_basisOfFractionalIdeal_eq_absNorm` in
`ℝ^r₁ × ℂ^r₂`. This is useful, in particular, to prove that the family obtained from
the `ℤ`-basis of `I` is actually an `ℝ`-basis of `ℝ^r₁ × ℂ^r₂`, see
`fractionalIdealLatticeBasis`. -/
theorem det_basisOfFractionalIdeal_eq_norm
    (e : (ChooseBasisIndex ℤ (𝓞 K)) ≃ (ChooseBasisIndex ℤ I)) :
    |Basis.det (latticeBasis K) ((mixedEmbedding K ∘ (basisOfFractionalIdeal K I) ∘ e))| =
      FractionalIdeal.absNorm I.1 := by
  suffices Basis.det (latticeBasis K) ((mixedEmbedding K ∘ (basisOfFractionalIdeal K I) ∘ e)) =
      (algebraMap ℚ ℝ) ((Basis.det (integralBasis K)) ((basisOfFractionalIdeal K I) ∘ e)) by
    rw [this, eq_ratCast, ← Rat.cast_abs, ← Equiv.symm_symm e, ← Basis.coe_reindex,
      det_basisOfFractionalIdeal_eq_absNorm K I e]
  rw [Basis.det_apply, Basis.det_apply, RingHom.map_det]
  congr
  ext i j
  simp_rw [RingHom.mapMatrix_apply, Matrix.map_apply, Basis.toMatrix_apply, Function.comp_apply]
  exact latticeBasis_repr_apply K _ i

/-- A `ℝ`-basis of `ℝ^r₁ × ℂ^r₂` that is also a `ℤ`-basis of the image of the fractional
ideal `I`. -/
def fractionalIdealLatticeBasis :
    Basis (ChooseBasisIndex ℤ I) ℝ (E K) := by
  let e : (ChooseBasisIndex ℤ (𝓞 K)) ≃ (ChooseBasisIndex ℤ I) := by
    refine Fintype.equivOfCardEq ?_
    rw [← finrank_eq_card_chooseBasisIndex, ← finrank_eq_card_chooseBasisIndex,
      fractionalIdeal_rank]
  refine Basis.reindex ?_ e
  suffices IsUnit ((latticeBasis K).det ((mixedEmbedding K) ∘ (basisOfFractionalIdeal K I) ∘ e)) by
    rw [← is_basis_iff_det] at this
    exact Basis.mk this.1 (by rw [this.2])
  rw [isUnit_iff_ne_zero, ne_eq, ← abs_eq_zero.not, det_basisOfFractionalIdeal_eq_norm,
    Rat.cast_eq_zero, FractionalIdeal.absNorm_eq_zero_iff]
  exact Units.ne_zero I

@[simp]
theorem fractionalIdealLatticeBasis_apply (i : ChooseBasisIndex ℤ I) :
    fractionalIdealLatticeBasis K I i = (mixedEmbedding K) (basisOfFractionalIdeal K I i) := by
  simp only [fractionalIdealLatticeBasis, Basis.coe_reindex, Basis.coe_mk, Function.comp_apply,
    Equiv.apply_symm_apply]

theorem mem_span_fractionalIdealLatticeBasis (x : (E K)) :
    x ∈ Submodule.span ℤ (Set.range (fractionalIdealLatticeBasis K I)) ↔
      x ∈ mixedEmbedding K '' I := by
  have h₁ : Set.range (fractionalIdealLatticeBasis K I) =
      (mixedEmbedding K).toIntAlgHom.toLinearMap '' (Set.range (basisOfFractionalIdeal K I)) := by
    rw [← Set.range_comp]
    exact congr_arg Set.range (funext (fun i ↦ fractionalIdealLatticeBasis_apply K I i))
  have h₂ : Submodule.span ℤ (Set.range (basisOfFractionalIdeal K I)) = (I : Set K) := by
    ext; erw [mem_span_basisOfFractionalIdeal]
  rw [h₁, ← Submodule.map_span, ← SetLike.mem_coe, Submodule.map_coe, h₂, AlgHom.coe_toLinearMap,
    RingHom.coe_toIntAlgHom]

end integerLattice

section convexBodyLT

open Metric NNReal

variable (f : InfinitePlace K → ℝ≥0)

/-- The convex body defined by `f`: the set of points `x : E` such that `‖x w‖ < f w` for all
infinite places `w`. -/
abbrev convexBodyLT : Set (E K) :=
  (Set.univ.pi (fun w : { w : InfinitePlace K // IsReal w } => ball 0 (f w))) ×ˢ
  (Set.univ.pi (fun w : { w : InfinitePlace K // IsComplex w } => ball 0 (f w)))

theorem convexBodyLT_mem {x : K} :
    mixedEmbedding K x ∈ (convexBodyLT K f) ↔ ∀ w : InfinitePlace K, w x < f w := by
  simp_rw [mixedEmbedding, RingHom.prod_apply, Set.mem_prod, Set.mem_pi, Set.mem_univ,
    forall_true_left, mem_ball_zero_iff, Pi.ringHom_apply, ← Complex.norm_real,
    embedding_of_isReal_apply, Subtype.forall, ← ball_or_left, ← not_isReal_iff_isComplex, em,
    forall_true_left, norm_embedding_eq]

theorem convexBodyLT_neg_mem (x : E K) (hx : x ∈ (convexBodyLT K f)) :
    -x ∈ (convexBodyLT K f) := by
  simp only [Set.mem_prod, Prod.fst_neg, Set.mem_pi, Set.mem_univ, Pi.neg_apply,
    mem_ball_zero_iff, norm_neg, Real.norm_eq_abs, forall_true_left, Subtype.forall,
    Prod.snd_neg, Complex.norm_eq_abs] at hx ⊢
  exact hx

theorem convexBodyLT_convex : Convex ℝ (convexBodyLT K f) :=
  Convex.prod (convex_pi (fun _ _ => convex_ball _ _)) (convex_pi (fun _ _ => convex_ball _ _))

open Fintype MeasureTheory MeasureTheory.Measure ENNReal

open scoped Classical BigOperators

variable [NumberField K]

instance : IsAddHaarMeasure (volume : Measure (E K)) := prod.instIsAddHaarMeasure volume volume

instance : NoAtoms (volume : Measure (E K)) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  by_cases hw : IsReal w
  exact @prod.instNoAtoms_fst _ _ _ _ volume volume _ (pi_noAtoms ⟨w, hw⟩)
  · exact @prod.instNoAtoms_snd _ _ _ _ volume volume _
      (pi_noAtoms ⟨w, not_isReal_iff_isComplex.mp hw⟩)

/-- The fudge factor that appears in the formula for the volume of `convexBodyLT`. -/
noncomputable abbrev convexBodyLTFactor : ℝ≥0 :=
  (2 : ℝ≥0) ^ NrRealPlaces K * NNReal.pi ^ NrComplexPlaces K

theorem convexBodyLTFactor_ne_zero : convexBodyLTFactor K ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ pi_ne_zero)

theorem one_le_convexBodyLTFactor : 1 ≤ convexBodyLTFactor K :=
  one_le_mul₀ (one_le_pow_of_one_le one_le_two _)
    (one_le_pow_of_one_le (le_trans one_le_two Real.two_le_pi) _)

/-- The volume of `(ConvexBodyLt K f)` where `convexBodyLT K f` is the set of points `x`
such that `‖x w‖ < f w` for all infinite places `w`. -/
theorem convexBodyLT_volume :
    volume (convexBodyLT K f) = (convexBodyLTFactor K) * ∏ w, (f w) ^ (mult w) := by
  calc
    _ = (∏ x : {w // InfinitePlace.IsReal w}, ENNReal.ofReal (2 * (f x.val))) *
          ∏ x : {w // InfinitePlace.IsComplex w}, ENNReal.ofReal (f x.val) ^ 2 * pi := by
      simp_rw [volume_eq_prod, prod_prod, volume_pi, pi_pi, Real.volume_ball, Complex.volume_ball]
    _ = ((2:ℝ≥0) ^ NrRealPlaces K * (∏ x : {w // InfinitePlace.IsReal w}, ENNReal.ofReal (f x.val)))
          * ((∏ x : {w // IsComplex w}, ENNReal.ofReal (f x.val) ^ 2) *
            NNReal.pi ^ NrComplexPlaces K) := by
      simp_rw [ofReal_mul (by norm_num : 0 ≤ (2 : ℝ)), Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, ofReal_ofNat, ofReal_coe_nnreal, coe_ofNat]
    _ = (convexBodyLTFactor K) * ((∏ x : {w // InfinitePlace.IsReal w}, .ofReal (f x.val)) *
        (∏ x : {w // IsComplex w}, ENNReal.ofReal (f x.val) ^ 2)) := by
      simp_rw [convexBodyLTFactor, coe_mul, ENNReal.coe_pow]
      ring
    _ = (convexBodyLTFactor K) * ∏ w, (f w) ^ (mult w) := by
      simp_rw [mult, pow_ite, pow_one, Finset.prod_ite, ofReal_coe_nnreal, not_isReal_iff_isComplex,
        coe_mul, coe_finset_prod, ENNReal.coe_pow]
      congr 2
      · refine (Finset.prod_subtype (Finset.univ.filter _) ?_ (fun w => (f w : ℝ≥0∞))).symm
        exact fun _ => by simp only [Finset.mem_univ, forall_true_left, Finset.mem_filter, true_and]
      · refine (Finset.prod_subtype (Finset.univ.filter _) ?_ (fun w => (f w : ℝ≥0∞) ^ 2)).symm
        exact fun _ => by simp only [Finset.mem_univ, forall_true_left, Finset.mem_filter, true_and]

variable {f}

/-- This is a technical result: quite often, we want to impose conditions at all infinite places
but one and choose the value at the remaining place so that we can apply
`exists_ne_zero_mem_ringOfIntegers_lt`. -/
theorem adjust_f {w₁ : InfinitePlace K} (B : ℝ≥0) (hf : ∀ w, w ≠ w₁ → f w ≠ 0) :
    ∃ g : InfinitePlace K → ℝ≥0, (∀ w, w ≠ w₁ → g w = f w) ∧ ∏ w, (g w) ^ mult w = B := by
  let S := ∏ w in Finset.univ.erase w₁, (f w) ^ mult w
  refine ⟨Function.update f w₁ ((B * S⁻¹) ^ (mult w₁ : ℝ)⁻¹), ?_, ?_⟩
  · exact fun w hw => Function.update_noteq hw _ f
  · rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w₁), Function.update_same,
      Finset.prod_congr rfl fun w hw => by rw [Function.update_noteq (Finset.ne_of_mem_erase hw)],
      ← NNReal.rpow_nat_cast, ← NNReal.rpow_mul, inv_mul_cancel, NNReal.rpow_one, mul_assoc,
      inv_mul_cancel, mul_one]
    · rw [Finset.prod_ne_zero_iff]
      exact fun w hw => pow_ne_zero _ (hf w (Finset.ne_of_mem_erase hw))
    · rw [mult]; split_ifs <;> norm_num

end convexBodyLT

section convexBodyLT'

open  Metric ENNReal NNReal

open scoped Classical

variable (f : InfinitePlace K → ℝ≥0) (w₀ : {w : InfinitePlace K // IsComplex w})

/-- A version of `convexBodyLT` with an additional condition at a fixed complex place. This is
needed to ensure the element constructed is not real, see for example
`exists_primitive_element_lt_of_isComplex`.
-/
abbrev convexBodyLT' : Set (E K) :=
  (Set.univ.pi (fun w : { w : InfinitePlace K // IsReal w } ↦ ball 0 (f w))) ×ˢ
  (Set.univ.pi (fun w : { w : InfinitePlace K // IsComplex w } ↦
    if w = w₀ then {x | |x.re| < 1 ∧ |x.im| < (f w : ℝ) ^ 2} else ball 0 (f w)))

theorem convexBodyLT'_mem {x : K} :
    mixedEmbedding K x ∈ convexBodyLT' K f w₀ ↔
      (∀ w : InfinitePlace K, w ≠ w₀ → w x < f w) ∧
      |(w₀.val.embedding x).re| < 1 ∧ |(w₀.val.embedding x).im| < (f w₀: ℝ) ^ 2 := by
  simp_rw [mixedEmbedding, RingHom.prod_apply, Set.mem_prod, Set.mem_pi, Set.mem_univ,
    forall_true_left, Pi.ringHom_apply, apply_ite, mem_ball_zero_iff, ← Complex.norm_real,
    embedding_of_isReal_apply, norm_embedding_eq, Subtype.forall, Set.mem_setOf_eq]
  refine ⟨fun ⟨h₁, h₂⟩ ↦ ⟨fun w h_ne ↦ ?_, ?_⟩, fun ⟨h₁, h₂⟩ ↦ ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩⟩
  · by_cases hw : IsReal w
    · exact norm_embedding_eq w _ ▸ h₁ w hw
    · specialize h₂ w (not_isReal_iff_isComplex.mp hw)
      rwa [if_neg (by exact Subtype.ne_of_val_ne h_ne)] at h₂
  · simpa [if_true] using h₂ w₀.val w₀.prop
  · exact h₁ w (ne_of_isReal_isComplex hw w₀.prop)
  · by_cases h_ne : w = w₀
    · simpa [h_ne]
    · rw [if_neg (by exact Subtype.ne_of_val_ne h_ne)]
      exact h₁ w h_ne

theorem convexBodyLT'_neg_mem (x : E K) (hx : x ∈ convexBodyLT' K f w₀) :
    -x ∈ convexBodyLT' K f w₀ := by
  simp [Set.mem_prod, Prod.fst_neg, Set.mem_pi, Set.mem_univ, Pi.neg_apply,
    mem_ball_zero_iff, norm_neg, Real.norm_eq_abs, forall_true_left, Subtype.forall,
    Prod.snd_neg, Complex.norm_eq_abs] at hx ⊢
  convert hx using 3
  split_ifs <;> simp

theorem convexBodyLT'_convex : Convex ℝ (convexBodyLT' K f w₀) := by
  refine Convex.prod (convex_pi (fun _ _ => convex_ball _ _)) (convex_pi (fun _ _ => ?_))
  split_ifs
  · simp_rw [abs_lt]
    refine Convex.inter ((convex_halfspace_re_gt _).inter  (convex_halfspace_re_lt _))
      ((convex_halfspace_im_gt _).inter  (convex_halfspace_im_lt _))
  · exact convex_ball _ _

open MeasureTheory MeasureTheory.Measure

open scoped Classical BigOperators

variable [NumberField K]

/-- The fudge factor that appears in the formula for the volume of `convexBodyLT'`. -/
noncomputable abbrev convexBodyLT'Factor : ℝ≥0 :=
  (2 : ℝ≥0) ^ (NrRealPlaces K + 2) * NNReal.pi ^ (NrComplexPlaces K - 1)

theorem convexBodyLT'Factor_ne_zero : convexBodyLT'Factor K ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ pi_ne_zero)

theorem one_le_convexBodyLT'Factor : 1 ≤ convexBodyLT'Factor K :=
  one_le_mul₀ (one_le_pow_of_one_le one_le_two _)
    (one_le_pow_of_one_le (le_trans one_le_two Real.two_le_pi) _)

theorem convexBodyLT'_volume :
    volume (convexBodyLT' K f w₀) = convexBodyLT'Factor K * ∏ w, (f w) ^ (mult w) := by
  have vol_box : ∀ B : ℝ≥0, volume {x : ℂ | |x.re| < 1 ∧ |x.im| < B^2} = 4*B^2 := by
    intro B
    rw [← (Complex.volume_preserving_equiv_real_prod.symm).measure_preimage]
    simp_rw [Set.preimage_setOf_eq, Complex.measurableEquivRealProd_symm_apply]
    rw [show {a : ℝ × ℝ | |a.1| < 1 ∧ |a.2| < B ^ 2} =
      Set.Ioo (-1:ℝ) (1:ℝ) ×ˢ Set.Ioo (- (B:ℝ) ^ 2) ((B:ℝ) ^ 2) by
        ext; simp_rw [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ioo, abs_lt]]
    simp_rw [volume_eq_prod, prod_prod, Real.volume_Ioo, sub_neg_eq_add, one_add_one_eq_two,
      ← two_mul, ofReal_mul zero_le_two, ofReal_pow (coe_nonneg B), ofReal_ofNat,
      ofReal_coe_nnreal, ← mul_assoc, show (2:ℝ≥0∞) * 2 = 4 by norm_num]
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_lt (measurable_norm.comp Complex.measurable_re) measurable_const
    · exact measurableSet_lt (measurable_norm.comp Complex.measurable_im) measurable_const
  calc
    _ = (∏ x : {w // InfinitePlace.IsReal w}, ENNReal.ofReal (2 * (f x.val))) *
          ((∏ x in Finset.univ.erase  w₀, ENNReal.ofReal (f x.val) ^ 2 * pi) *
          (4 * (f w₀) ^ 2)) := by
      simp_rw [volume_eq_prod, prod_prod, volume_pi, pi_pi, Real.volume_ball]
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ w₀)]
      congr 2
      · refine Finset.prod_congr rfl (fun w' hw' ↦ ?_)
        rw [if_neg (Finset.ne_of_mem_erase hw'), Complex.volume_ball]
      · simpa only [ite_true] using vol_box (f w₀)
    _ = ((2 : ℝ≥0) ^ NrRealPlaces K *
          (∏ x : {w // InfinitePlace.IsReal w}, ENNReal.ofReal (f x.val))) *
            ((∏ x in Finset.univ.erase  w₀, ENNReal.ofReal (f x.val) ^ 2) *
              ↑pi ^ (NrComplexPlaces K - 1) * (4 * (f w₀) ^ 2)) := by
      simp_rw [ofReal_mul (by norm_num : 0 ≤ (2 : ℝ)), Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ofReal_ofNat,
        ofReal_coe_nnreal, coe_ofNat]
    _ = convexBodyLT'Factor K * (∏ x : {w // InfinitePlace.IsReal w}, ENNReal.ofReal (f x.val))
        * (∏ x : {w // IsComplex w}, ENNReal.ofReal (f x.val) ^ 2) := by
      rw [show (4 : ℝ≥0∞) = (2 : ℝ≥0) ^ 2 by norm_num, convexBodyLT'Factor, pow_add,
        ← Finset.prod_erase_mul _ _ (Finset.mem_univ w₀), ofReal_coe_nnreal]
      simp_rw [coe_mul, ENNReal.coe_pow]
      ring
    _ = convexBodyLT'Factor K * ∏ w, (f w) ^ (mult w) := by
      simp_rw [mult, pow_ite, pow_one, Finset.prod_ite, ofReal_coe_nnreal, not_isReal_iff_isComplex,
        coe_mul, coe_finset_prod, ENNReal.coe_pow, mul_assoc]
      congr 3
      · refine (Finset.prod_subtype (Finset.univ.filter _) ?_ (fun w => (f w : ℝ≥0∞))).symm
        exact fun _ => by simp only [Finset.mem_univ, forall_true_left, Finset.mem_filter, true_and]
      · refine (Finset.prod_subtype (Finset.univ.filter _) ?_ (fun w => (f w : ℝ≥0∞) ^ 2)).symm
        exact fun _ => by simp only [Finset.mem_univ, forall_true_left, Finset.mem_filter, true_and]

end convexBodyLT'

section convexBodySum

open ENNReal MeasureTheory Fintype

open scoped Real Classical BigOperators NNReal

variable [NumberField K] (B : ℝ)
variable {K}

/-- The function that sends `x : ({w // IsReal w} → ℝ) × ({w // IsComplex w} → ℂ)` to
  `∑ w, ‖x.1 w‖ + 2 * ∑ w, ‖x.2 w‖`. It defines a norm and it used to define `convexBodySum`. -/
noncomputable abbrev convexBodySumFun (x : E K) : ℝ := ∑ w, ‖x.1 w‖ + 2 * ∑ w, ‖x.2 w‖

theorem convexBodySumFun_nonneg (x : E K) :
    0 ≤ convexBodySumFun x := by
  refine add_nonneg ?_ ?_
  · exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  · exact mul_nonneg zero_le_two (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

theorem convexBodySumFun_neg (x : E K) :
    convexBodySumFun (- x) = convexBodySumFun x := by
  simp_rw [convexBodySumFun, Prod.fst_neg, Prod.snd_neg, Pi.neg_apply, norm_neg]

theorem convexBodySumFun_add_le (x y : E K) :
    convexBodySumFun (x + y) ≤ convexBodySumFun x + convexBodySumFun y := by
  simp_rw [convexBodySumFun, Prod.fst_add, Pi.add_apply, Prod.snd_add]
  refine (add_le_add
    (Finset.sum_le_sum (fun w _ => norm_add_le (x.1 w) (y.1 w)))
    (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun w _ => norm_add_le (x.2 w) (y.2 w))) (by norm_num))).trans_eq ?_
  simp_rw [Finset.sum_add_distrib, mul_add]
  ring

theorem convexBodySumFun_smul (c : ℝ) (x : E K) :
    convexBodySumFun (c • x) = |c| * convexBodySumFun x := by
  simp_rw [convexBodySumFun, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
    Complex.real_smul, norm_mul, Complex.norm_real, ← Finset.mul_sum, Real.norm_eq_abs]
  ring

theorem convexBodySumFun_eq_zero_iff (x : E K) :
    convexBodySumFun x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [add_eq_zero_iff' (Finset.sum_nonneg fun _ _ => norm_nonneg _) (mul_nonneg zero_le_two
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)), Finset.mul_sum,
      Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => mul_nonneg zero_le_two (norm_nonneg _)),
      Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => norm_nonneg _)] at h
    ext : 2
    · exact norm_eq_zero.mp (h.1 _ (Finset.mem_univ _))
    · exact norm_eq_zero.1 <| eq_zero_of_ne_zero_of_mul_left_eq_zero two_ne_zero <| h.2 _ <|
        Finset.mem_univ _
  · simp only [convexBodySumFun, h, Prod.fst_zero, Pi.zero_apply, norm_zero, Finset.sum_const_zero,
      Prod.snd_zero, mul_zero, add_zero]

theorem norm_le_convexBodySumFun (x : E K) : ‖x‖ ≤ convexBodySumFun x := by
  refine max_le ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (convexBodySumFun_nonneg x)).mpr (fun w => ?_)
    refine le_add_of_le_of_nonneg ?_ ?_
    · exact Finset.single_le_sum (fun z _ => norm_nonneg (x.1 z)) (Finset.mem_univ w)
    · exact mul_nonneg zero_le_two <| Finset.sum_nonneg (fun w _ => norm_nonneg (x.2 w))
  · refine (pi_norm_le_iff_of_nonneg (convexBodySumFun_nonneg x)).mpr (fun w => ?_)
    refine le_add_of_nonneg_of_le ?_ ?_
    · exact Finset.sum_nonneg (fun w _ => norm_nonneg (x.1 w))
    · rw [Finset.mul_sum]
      refine le_trans (by linarith [norm_nonneg (x.2 w)] : ‖x.2 w‖ ≤ 2 * ‖x.2 w‖) ?_
      exact Finset.single_le_sum (fun z _ => mul_nonneg zero_le_two (norm_nonneg (x.2 z)))
        (Finset.mem_univ w)

variable (K)

theorem convexBodySumFun_continuous :
    Continuous (convexBodySumFun : (E K) → ℝ) := by
  refine Continuous.add ?_ ?_
  · exact continuous_finset_sum Finset.univ
      (fun i _ => continuous_norm.comp' (continuous_apply i).fst')
  · refine Continuous.const_smul ?_ (2:ℝ)
    exact continuous_finset_sum Finset.univ
      (fun i _ => continuous_norm.comp' (continuous_apply i).snd')

/-- The convex body equal to the set of points `x : E` such that
  `∑ w real, ‖x w‖ + 2 * ∑ w complex, ‖x w‖ ≤ B`. -/
abbrev convexBodySum : Set (E K)  := { x | convexBodySumFun x ≤ B }

theorem convexBodySum_volume_eq_zero_of_le_zero {B} (hB : B ≤ 0) :
    volume (convexBodySum K B) = 0 := by
  obtain hB | hB := lt_or_eq_of_le hB
  · suffices convexBodySum K B = ∅ by rw [this, measure_empty]
    ext x
    refine ⟨fun hx => ?_, fun h => h.elim⟩
    rw [Set.mem_setOf] at hx
    linarith [convexBodySumFun_nonneg x]
  · suffices convexBodySum K B = { 0 } by rw [this, measure_singleton]
    ext
    rw [convexBodySum, Set.mem_setOf_eq, Set.mem_singleton_iff, hB, ← convexBodySumFun_eq_zero_iff]
    exact (convexBodySumFun_nonneg _).le_iff_eq

theorem convexBodySum_mem {x : K} :
    mixedEmbedding K x ∈ (convexBodySum K B) ↔
      ∑ w : InfinitePlace K, (mult w) * w.val x ≤ B := by
  simp_rw [Set.mem_setOf_eq, mixedEmbedding, RingHom.prod_apply, convexBodySumFun, Pi.ringHom_apply,
    ← Complex.norm_real, embedding_of_isReal_apply, norm_embedding_eq, mult, Nat.cast_ite, ite_mul,
    Finset.sum_ite, Finset.filter_congr (fun _ _ => not_isReal_iff_isComplex), Finset.mul_sum,
    ← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ, Nat.cast_one, one_mul, Nat.cast_ofNat]
  rfl

theorem convexBodySum_neg_mem {x : E K} (hx : x ∈ (convexBodySum K B)) :
    -x ∈ (convexBodySum K B) := by
  rw [Set.mem_setOf, convexBodySumFun_neg]
  exact hx

theorem convexBodySum_convex : Convex ℝ (convexBodySum K B) := by
  refine Convex_subadditive_le (fun _ _ => convexBodySumFun_add_le _ _) (fun c x h => ?_) B
  rw [convexBodySumFun_smul c x, abs_eq_self.mpr h]

theorem convexBodySum_isBounded : Bornology.IsBounded (convexBodySum K B) := by
  refine Metric.isBounded_iff.mpr ⟨B + B, fun x hx y hy => ?_⟩
  refine le_trans (norm_sub_le x y) (add_le_add ?_ ?_)
  · exact le_trans (norm_le_convexBodySumFun x) hx
  · exact le_trans (norm_le_convexBodySumFun y) hy

theorem convexBodySum_compact : IsCompact (convexBodySum K B) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  refine ⟨?_, convexBodySum_isBounded K B⟩
  convert IsClosed.preimage (convexBodySumFun_continuous K) (isClosed_Icc : IsClosed (Set.Icc 0 B))
  ext
  simp [convexBodySumFun_nonneg]

/-- The fudge factor that appears in the formula for the volume of `convexBodyLt`. -/
noncomputable abbrev convexBodySumFactor : ℝ≥0 :=
  (2 : ℝ≥0) ^ NrRealPlaces K * (NNReal.pi / 2) ^ NrComplexPlaces K / (finrank ℚ K).factorial

theorem convexBodySumFactor_ne_zero : convexBodySumFactor K ≠ 0 := by
  refine div_ne_zero ?_ <| Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  exact mul_ne_zero (pow_ne_zero _ two_ne_zero)
    (pow_ne_zero _ (div_ne_zero NNReal.pi_ne_zero two_ne_zero))

open MeasureTheory MeasureTheory.Measure Real in
theorem convexBodySum_volume :
    volume (convexBodySum K B) = (convexBodySumFactor K) * (.ofReal B) ^ (finrank ℚ K) := by
  obtain hB | hB := le_or_lt B 0
  · rw [convexBodySum_volume_eq_zero_of_le_zero K hB, ofReal_eq_zero.mpr hB, zero_pow, mul_zero]
    exact finrank_pos.ne'
  · suffices volume (convexBodySum K 1) = (convexBodySumFactor K) by
      rw [mul_comm]
      convert addHaar_smul volume B (convexBodySum K 1)
      · simp_rw [← Set.preimage_smul_inv₀ (ne_of_gt hB), Set.preimage_setOf_eq, convexBodySumFun,
          Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, Complex.real_smul, smul_eq_mul, norm_mul,
          Complex.ofReal_inv, norm_inv, norm_eq_abs B, Complex.norm_eq_abs B, Complex.abs_ofReal,
          abs_eq_self.mpr (le_of_lt hB), ← Finset.mul_sum, ← mul_assoc, mul_comm (2:ℝ), mul_assoc,
          ← mul_add, inv_mul_le_iff hB, mul_one]
      · rw [abs_pow, ofReal_pow (abs_nonneg _), abs_eq_self.mpr (le_of_lt hB),
          mixedEmbedding.finrank]
      · exact this.symm
    rw [MeasureTheory.measure_le_eq_lt _ ((convexBodySumFun_eq_zero_iff 0).mpr rfl)
      convexBodySumFun_neg convexBodySumFun_add_le
      (fun hx => (convexBodySumFun_eq_zero_iff _).mp hx)
      (fun r x => le_of_eq (convexBodySumFun_smul r x))]
    rw [measure_lt_one_eq_integral_div_gamma (g := fun x : (E K) => convexBodySumFun x)
      volume ((convexBodySumFun_eq_zero_iff 0).mpr rfl) convexBodySumFun_neg convexBodySumFun_add_le
      (fun hx => (convexBodySumFun_eq_zero_iff _).mp hx)
      (fun r x => le_of_eq (convexBodySumFun_smul r x)) zero_lt_one]
    simp_rw [mixedEmbedding.finrank, div_one, Gamma_nat_eq_factorial, ofReal_div_of_pos
      (Nat.cast_pos.mpr (Nat.factorial_pos _)), Real.rpow_one, ofReal_coe_nat]
    suffices ∫ x : E K, exp (-convexBodySumFun x) =
        (2:ℝ) ^ NrRealPlaces K * (π / 2) ^ NrComplexPlaces K by
      rw [this, convexBodySumFactor, ofReal_mul (by positivity), ofReal_pow zero_le_two,
        ofReal_pow (by positivity), ofReal_div_of_pos zero_lt_two, ofReal_ofNat,
        ← NNReal.coe_real_pi, ofReal_coe_nnreal, coe_div (Nat.cast_ne_zero.mpr
        (Nat.factorial_ne_zero _)), coe_mul, coe_pow, coe_pow, coe_ofNat, coe_div two_ne_zero,
        coe_ofNat, coe_nat]
    calc
      _ = (∫ x : {w : InfinitePlace K // IsReal w} → ℝ, ∏ w, exp (- ‖x w‖)) *
              (∫ x : {w : InfinitePlace K // IsComplex w} → ℂ, ∏ w, exp (- 2 * ‖x w‖)) := by
        simp_rw [convexBodySumFun, neg_add, ← neg_mul, Finset.mul_sum, ← Finset.sum_neg_distrib,
          exp_add, exp_sum, ← integral_prod_mul, volume_eq_prod]
      _ = (∫ x : ℝ, exp (-|x|)) ^ NrRealPlaces K *
              (∫ x : ℂ, Real.exp (-2 * ‖x‖)) ^ NrComplexPlaces K := by
        rw [integral_fintype_prod_eq_pow _ (fun x => exp (- ‖x‖)), integral_fintype_prod_eq_pow _
          (fun x => exp (- 2 * ‖x‖))]
        simp_rw [norm_eq_abs]
      _ =  (2 * Gamma (1 / 1 + 1)) ^ NrRealPlaces K *
              (π * (2:ℝ) ^ (-(2:ℝ) / 1) * Gamma (2 / 1 + 1)) ^ NrComplexPlaces K := by
        rw [integral_comp_abs (f := fun x => exp (- x)), ← integral_exp_neg_rpow zero_lt_one,
          ← Complex.integral_exp_neg_mul_rpow le_rfl zero_lt_two]
        simp_rw [Real.rpow_one]
      _ = (2:ℝ) ^ NrRealPlaces K * (π / 2) ^ NrComplexPlaces K := by
        simp_rw [div_one, one_add_one_eq_two, Gamma_add_one two_ne_zero, Gamma_two, mul_one,
          mul_assoc, ← Real.rpow_add_one two_ne_zero, show (-2:ℝ) + 1 = -1 by norm_num,
          Real.rpow_neg_one]
        rfl

end convexBodySum

section minkowski

open scoped Classical
open MeasureTheory MeasureTheory.Measure FiniteDimensional Zspan Real Submodule

open scoped ENNReal NNReal nonZeroDivisors IntermediateField

variable [NumberField K] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The bound that appears in **Minkowski Convex Body theorem**, see
`MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`. See
`NumberField.mixedEmbedding.volume_fundamentalDomain_idealLatticeBasis_eq` and
`NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis` for the computation of
`volume (fundamentalDomain (idealLatticeBasis K))`. -/
noncomputable def minkowskiBound : ℝ≥0∞ :=
  volume (fundamentalDomain (fractionalIdealLatticeBasis K I)) * (2 : ℝ≥0∞) ^ (finrank ℝ (E K))

theorem volume_fundamentalDomain_fractionalIdealLatticeBasis :
    volume (fundamentalDomain (fractionalIdealLatticeBasis K I)) =
      .ofReal (FractionalIdeal.absNorm I.1) *  volume (fundamentalDomain (latticeBasis K)) := by
  let e : (Module.Free.ChooseBasisIndex ℤ I) ≃ (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) := by
    refine Fintype.equivOfCardEq ?_
    rw [← finrank_eq_card_chooseBasisIndex, ← finrank_eq_card_chooseBasisIndex,
      fractionalIdeal_rank]
  rw [← fundamentalDomain_reindex (fractionalIdealLatticeBasis K I) e,
    measure_fundamentalDomain ((fractionalIdealLatticeBasis K I).reindex e)]
  rw [show (fractionalIdealLatticeBasis K I).reindex e = (mixedEmbedding K) ∘
      (basisOfFractionalIdeal K I) ∘ e.symm by
    ext1; simp only [Basis.coe_reindex, Function.comp_apply, fractionalIdealLatticeBasis_apply]]
  rw [mixedEmbedding.det_basisOfFractionalIdeal_eq_norm]

theorem minkowskiBound_lt_top : minkowskiBound K I < ⊤ := by
  refine ENNReal.mul_lt_top ?_ ?_
  · exact ne_of_lt (fundamentalDomain_isBounded _).measure_lt_top
  · exact ne_of_lt (ENNReal.pow_lt_top (lt_top_iff_ne_top.mpr ENNReal.two_ne_top) _)

theorem minkowskiBound_pos : 0 < minkowskiBound K I := by
  refine zero_lt_iff.mpr (mul_ne_zero ?_ ?_)
  · exact Zspan.measure_fundamentalDomain_ne_zero _
  · exact ENNReal.pow_ne_zero two_ne_zero _

variable {f : InfinitePlace K → ℝ≥0} (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- Let `I` be a fractional ideal of `K`. Assume that `f : InfinitePlace K → ℝ≥0` is such that
`minkowskiBound K I < volume (convexBodyLT K f)` where `convexBodyLT K f` is the set of
points `x` such that `‖x w‖ < f w` for all infinite places `w` (see `convexBodyLT_volume` for
the computation of this volume), then there exists a nonzero algebraic number `a` in `I` such
that `w a < f w` for all infinite places `w`. -/
theorem exists_ne_zero_mem_ideal_lt (h : minkowskiBound K I < volume (convexBodyLT K f)) :
    ∃ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K), a ≠ 0 ∧ ∀ w : InfinitePlace K, w a < f w := by
  have h_fund := Zspan.isAddFundamentalDomain (fractionalIdealLatticeBasis K I) volume
  have : Countable (span ℤ (Set.range (fractionalIdealLatticeBasis K I))).toAddSubgroup := by
    change Countable (span ℤ (Set.range (fractionalIdealLatticeBasis K I)) : Set (E K))
    infer_instance
  obtain ⟨⟨x, hx⟩, h_nz, h_mem⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    h_fund (convexBodyLT_neg_mem K f) (convexBodyLT_convex K f) h
  rw [mem_toAddSubgroup, mem_span_fractionalIdealLatticeBasis] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a, ha, by simpa using h_nz, (convexBodyLT_mem K f).mp h_mem⟩

/-- A version of `exists_ne_zero_mem_ideal_lt` where the absolute value of the real part of `a` is
smaller than `1` at some fixed complex place. This is useful to ensure that `a` is not real. -/
theorem exists_ne_zero_mem_ideal_lt' (w₀ : {w : InfinitePlace K // IsComplex w})
    (h : minkowskiBound K I < volume (convexBodyLT' K f w₀)) :
    ∃ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K), a ≠ 0 ∧ (∀ w : InfinitePlace K, w ≠ w₀ → w a < f w) ∧
      |(w₀.val.embedding a).re| < 1 ∧ |(w₀.val.embedding a).im| < (f w₀ : ℝ) ^ 2:= by
  have h_fund := Zspan.isAddFundamentalDomain (fractionalIdealLatticeBasis K I) volume
  have : Countable (span ℤ (Set.range (fractionalIdealLatticeBasis K I))).toAddSubgroup := by
    change Countable (span ℤ (Set.range (fractionalIdealLatticeBasis K I)) : Set (E K))
    infer_instance
  obtain ⟨⟨x, hx⟩, h_nz, h_mem⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    h_fund (convexBodyLT'_neg_mem K f w₀) (convexBodyLT'_convex K f w₀) h
  rw [mem_toAddSubgroup, mem_span_fractionalIdealLatticeBasis] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a, ha, by simpa using h_nz, (convexBodyLT'_mem K f w₀).mp h_mem⟩

/-- A version of `exists_ne_zero_mem_ideal_lt` for the ring of integers of `K`. -/
theorem exists_ne_zero_mem_ringOfIntegers_lt (h : minkowskiBound K ↑1 < volume (convexBodyLT K f)) :
    ∃ a ∈ 𝓞 K, a ≠ 0 ∧ ∀ w : InfinitePlace K, w a < f w := by
  obtain ⟨_, h_mem, h_nz, h_bd⟩ := exists_ne_zero_mem_ideal_lt K ↑1 h
  obtain ⟨⟨a, ha⟩, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp h_mem
  exact ⟨a, ha, h_nz, h_bd⟩

/-- A version of `exists_ne_zero_mem_ideal_lt'` for the ring of integers of `K`. -/
theorem exists_ne_zero_mem_ringOfIntegers_lt' (w₀ : {w : InfinitePlace K // IsComplex w})
    (h : minkowskiBound K ↑1 < volume (convexBodyLT' K f w₀)) :
    ∃ a ∈ 𝓞 K, a ≠ 0 ∧ (∀ w : InfinitePlace K, w ≠ w₀ → w a < f w) ∧
      |(w₀.val.embedding a).re| < 1 ∧ |(w₀.val.embedding a).im| < (f w₀ : ℝ) ^ 2 := by
  obtain ⟨_, h_mem, h_nz, h_bd⟩ := exists_ne_zero_mem_ideal_lt' K ↑1 w₀ h
  obtain ⟨⟨a, ha⟩, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp h_mem
  exact ⟨a, ha, h_nz, h_bd⟩

theorem exists_primitive_element_lt_of_isReal {w₀ : InfinitePlace K} (hw₀ : IsReal w₀) {B : ℝ≥0}
    (hB : minkowskiBound K ↑1 < convexBodyLTFactor K * B) :
    ∃ a ∈ 𝓞 K, ℚ⟮(a:K)⟯ = ⊤ ∧ (∀ w : InfinitePlace K, w a < max B 1) := by
  have : minkowskiBound K ↑1 < volume (convexBodyLT K (fun w ↦ if w = w₀ then B else 1)) := by
    rw [convexBodyLT_volume, ← Finset.prod_erase_mul _ _ (Finset.mem_univ w₀)]
    simp_rw [ite_pow, one_pow]
    rw [Finset.prod_ite_eq']
    simp_rw [Finset.not_mem_erase, ite_false, mult, hw₀, ite_true, one_mul, pow_one]
    exact hB
  obtain ⟨a, ha, h_nz, h_le⟩ := exists_ne_zero_mem_ringOfIntegers_lt K this
  refine ⟨a, ha, ?_, fun w ↦ lt_of_lt_of_le (h_le w) ?_⟩
  · exact is_primitive_element_of_infinitePlace_lt (x := ⟨a, ha⟩) (Subtype.ne_of_val_ne h_nz)
      (fun w h_ne ↦ by convert (if_neg h_ne) ▸ h_le w) (Or.inl hw₀)
  · split_ifs <;> simp

theorem exists_primitive_element_lt_of_isComplex {w₀ : InfinitePlace K} (hw₀ : IsComplex w₀)
    {B : ℝ≥0} (hB : minkowskiBound K ↑1 < convexBodyLT'Factor K * B) :
    ∃ a ∈ 𝓞 K, ℚ⟮(a:K)⟯ = ⊤ ∧ (∀ w : InfinitePlace K, w a < Real.sqrt (1 + B ^ 2)) := by
  have : minkowskiBound K ↑1 <
      volume (convexBodyLT' K (fun w ↦ if w = w₀ then NNReal.sqrt B else 1) ⟨w₀, hw₀⟩) := by
    rw [convexBodyLT'_volume, ← Finset.prod_erase_mul _ _ (Finset.mem_univ w₀)]
    simp_rw [ite_pow, one_pow]
    rw [Finset.prod_ite_eq']
    simp_rw [Finset.not_mem_erase, ite_false, mult, not_isReal_iff_isComplex.mpr hw₀,
      ite_true, ite_false, one_mul, NNReal.sq_sqrt]
    exact hB
  obtain ⟨a, ha, h_nz, h_le, h_le₀⟩ := exists_ne_zero_mem_ringOfIntegers_lt' K ⟨w₀, hw₀⟩ this
  refine ⟨a, ha, ?_, fun w ↦ ?_⟩
  · exact is_primitive_element_of_infinitePlace_lt (x := ⟨a, ha⟩) (Subtype.ne_of_val_ne h_nz)
      (fun w h_ne ↦ by convert if_neg h_ne ▸ h_le w h_ne) (Or.inr h_le₀.1)
  · by_cases h_eq : w = w₀
    · rw [if_pos rfl] at h_le₀
      dsimp only at h_le₀
      rw [h_eq, ← norm_embedding_eq, Real.lt_sqrt (norm_nonneg _), ← Complex.re_add_im
        (embedding w₀ a), Complex.norm_eq_abs, Complex.abs_add_mul_I, Real.sq_sqrt (by positivity)]
      refine add_lt_add ?_ ?_
      · rw [← sq_abs, sq_lt_one_iff (abs_nonneg _)]
        exact h_le₀.1
      · rw [sq_lt_sq, NNReal.abs_eq, ← NNReal.sq_sqrt B]
        exact h_le₀.2
    · refine lt_of_lt_of_le (if_neg h_eq ▸ h_le w h_eq) ?_
      rw [NNReal.coe_one, Real.le_sqrt' zero_lt_one, one_pow]
      set_option tactic.skipAssignedInstances false in norm_num

theorem exists_ne_zero_mem_ideal_of_norm_le {B : ℝ}
    (h : (minkowskiBound K I) ≤ volume (convexBodySum K B)) :
    ∃ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K), a ≠ 0 ∧
      |Algebra.norm ℚ (a:K)| ≤ (B / (finrank ℚ K)) ^ (finrank ℚ K) := by
  have hB : 0 ≤ B := by
    contrapose! h
    rw [convexBodySum_volume_eq_zero_of_le_zero K (le_of_lt h)]
    exact minkowskiBound_pos K I
  -- Some inequalities that will be useful later on
  have h1 : 0 < (finrank ℚ K : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr finrank_pos)
  have h2 : 0 ≤ B / (finrank ℚ K) := div_nonneg hB (Nat.cast_nonneg _)
  have h_fund := Zspan.isAddFundamentalDomain (fractionalIdealLatticeBasis K I) volume
  have : Countable (span ℤ (Set.range (fractionalIdealLatticeBasis K I))).toAddSubgroup := by
    change Countable (span ℤ (Set.range (fractionalIdealLatticeBasis K I)): Set (E K))
    infer_instance
  obtain ⟨⟨x, hx⟩, h_nz, h_mem⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      h_fund (fun _ ↦ convexBodySum_neg_mem K B) (convexBodySum_convex K B)
      (convexBodySum_compact K B) h
  rw [mem_toAddSubgroup, mem_span_fractionalIdealLatticeBasis] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨a, ha, by simpa using h_nz, ?_⟩
  rw [← rpow_nat_cast, ← rpow_le_rpow_iff (by simp only [Rat.cast_abs, abs_nonneg])
      (rpow_nonneg h2 _) h1, ← rpow_mul h2,  mul_inv_cancel (Nat.cast_ne_zero.mpr
      (ne_of_gt finrank_pos)), rpow_one, le_div_iff' (Nat.cast_pos.mpr finrank_pos)]
  refine le_trans ?_ ((convexBodySum_mem K B).mp h_mem)
  rw [← le_div_iff' (Nat.cast_pos.mpr finrank_pos), ← sum_mult_eq, Nat.cast_sum]
  refine le_trans ?_ (geom_mean_le_arith_mean Finset.univ _ _ (fun _ _ => Nat.cast_nonneg _)
    ?_ (fun _ _ => AbsoluteValue.nonneg _ _))
  · simp_rw [← prod_eq_abs_norm, rpow_nat_cast, NumberField.InfinitePlace.infinitePlace_apply,
      le_rfl]
  · rw [← Nat.cast_sum, sum_mult_eq, Nat.cast_pos]
    exact finrank_pos

theorem exists_ne_zero_mem_ringOfIntegers_of_norm_le {B : ℝ}
    (h : (minkowskiBound K ↑1) ≤ volume (convexBodySum K B)) :
    ∃ a ∈ 𝓞 K, a ≠ 0 ∧ |Algebra.norm ℚ (a:K)| ≤ (B / (finrank ℚ K)) ^ (finrank ℚ K) := by
  obtain ⟨_, h_mem, h_nz, h_bd⟩ := exists_ne_zero_mem_ideal_of_norm_le K ↑1 h
  obtain ⟨⟨a, ha⟩, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp h_mem
  exact ⟨a, ha, h_nz, h_bd⟩

end minkowski

end NumberField.mixedEmbedding
