/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.NumberTheory.NumberField.Units.Basic

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

* `NumberField.mixedEmbedding`: the ring homomorphism from `K` to the mixed space
`K →+* ({ w // IsReal w } → ℝ) × ({ w // IsComplex w } → ℂ)` that sends `x ∈ K` to `(φ_w x)_w`
where `φ_w` is the embedding associated to the infinite place `w`. In particular, if `w` is real
then `φ_w : K →+* ℝ` and, if `w` is complex, `φ_w` is an arbitrary choice between the two complex
embeddings defining the place `w`.

## Tags

number field, infinite places
-/

variable (K : Type*) [Field K]

namespace NumberField.canonicalEmbedding

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
  refine Submodule.span_induction ?_ ?_ (fun _ _ _ _ hx hy => ?_) (fun a _ _ hx => ?_) hx
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
  obtain hr | hr := lt_or_ge r 0
  · obtain ⟨φ⟩ := (inferInstance : Nonempty (K →+* ℂ))
    refine iff_of_false ?_ ?_
    · exact (hr.trans_le (norm_nonneg _)).not_ge
    · exact fun h => hr.not_ge (le_trans (norm_nonneg _) (h φ))
  · lift r to NNReal using hr
    simp_rw [← coe_nnnorm, nnnorm_eq, NNReal.coe_le_coe, Finset.sup_le_iff, Finset.mem_univ,
      forall_true_left]

variable (K)

/-- The image of `𝓞 K` as a subring of `ℂ^n`. -/
def integerLattice : Subring ((K →+* ℂ) → ℂ) :=
  (RingHom.range (algebraMap (𝓞 K) K)).map (canonicalEmbedding K)

theorem integerLattice.inter_ball_finite [NumberField K] (r : ℝ) :
    ((integerLattice K : Set ((K →+* ℂ) → ℂ)) ∩ Metric.closedBall 0 r).Finite := by
  obtain hr | _ := lt_or_ge r 0
  · simp [Metric.closedBall_eq_empty.2 hr]
  · have heq : ∀ x, canonicalEmbedding K x ∈ Metric.closedBall 0 r ↔
        ∀ φ : K →+* ℂ, ‖φ x‖ ≤ r := by
      intro x; rw [← norm_le_iff, mem_closedBall_zero_iff]
    convert (Embeddings.finite_of_norm_le K ℂ r).image (canonicalEmbedding K)
    ext; constructor
    · rintro ⟨⟨_, ⟨x, rfl⟩, rfl⟩, hx⟩
      exact ⟨x, ⟨SetLike.coe_mem x, fun φ => (heq _).mp hx φ⟩, rfl⟩
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      exact ⟨⟨x, ⟨⟨x, hx1⟩, rfl⟩, rfl⟩, (heq x).mpr hx2⟩

open Module Fintype Module

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
      exact (basisOfPiSpaceOfLinearIndependent this.1).reindex e
  -- In order to prove that the determinant is nonzero, we show that it is equal to the
  -- square of the discriminant of the integral basis and thus it is not zero
    let N := Algebra.embeddingsMatrixReindex ℚ ℂ (fun i => integralBasis K (e i))
      RingHom.equivRatAlgHom
    rw [show M = N.transpose by { ext : 2; rfl }]
    rw [Matrix.det_transpose, ← pow_ne_zero_iff two_ne_zero]
    convert (map_ne_zero_iff _ (algebraMap ℚ ℂ).injective).mpr
      (Algebra.discr_not_zero_of_basis ℚ (integralBasis K))
    rw [← Algebra.discr_reindex ℚ (integralBasis K) e.symm]
    exact (Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ
      (fun i => integralBasis K (e i)) RingHom.equivRatAlgHom).symm

@[simp]
theorem latticeBasis_apply [NumberField K] (i : Free.ChooseBasisIndex ℤ (𝓞 K)) :
    latticeBasis K i = (canonicalEmbedding K) (integralBasis K i) := by
  simp [latticeBasis, integralBasis_apply, coe_basisOfPiSpaceOfLinearIndependent,
    Function.comp_apply, Equiv.apply_symm_apply]

theorem mem_span_latticeBasis [NumberField K] {x : (K →+* ℂ) → ℂ} :
    x ∈ Submodule.span ℤ (Set.range (latticeBasis K)) ↔
      x ∈ ((canonicalEmbedding K).comp (algebraMap (𝓞 K) K)).range := by
  rw [show Set.range (latticeBasis K) =
      (canonicalEmbedding K).toIntAlgHom.toLinearMap '' (Set.range (integralBasis K)) by
    rw [← Set.range_comp]; exact congrArg Set.range (funext (fun i => latticeBasis_apply K i))]
  rw [← Submodule.map_span, ← SetLike.mem_coe, Submodule.map_coe]
  rw [← RingHom.map_range, Subring.mem_map, Set.mem_image]
  simp only [SetLike.mem_coe, mem_span_integralBasis K]
  rfl

theorem mem_rat_span_latticeBasis [NumberField K] (x : K) :
    canonicalEmbedding K x ∈ Submodule.span ℚ (Set.range (latticeBasis K)) := by
  rw [← Basis.sum_repr (integralBasis K) x, map_sum]
  simp_rw [map_rat_smul]
  refine Submodule.sum_smul_mem _ _ (fun i _ ↦ Submodule.subset_span ?_)
  rw [← latticeBasis_apply]
  exact Set.mem_range_self i

theorem integralBasis_repr_apply [NumberField K] (x : K) (i : Free.ChooseBasisIndex ℤ (𝓞 K)) :
    (latticeBasis K).repr (canonicalEmbedding K x) i = (integralBasis K).repr x i := by
  rw [← Basis.restrictScalars_repr_apply ℚ _ ⟨_, mem_rat_span_latticeBasis K x⟩, eq_ratCast,
    Rat.cast_inj]
  let f := (canonicalEmbedding K).toRatAlgHom.toLinearMap.codRestrict _
    (fun x ↦ mem_rat_span_latticeBasis K x)
  suffices ((latticeBasis K).restrictScalars ℚ).repr.toLinearMap ∘ₗ f =
    (integralBasis K).repr.toLinearMap from DFunLike.congr_fun (LinearMap.congr_fun this x) i
  refine Basis.ext (integralBasis K) (fun i ↦ ?_)
  have : f (integralBasis K i) = ((latticeBasis K).restrictScalars ℚ) i := by
    apply Subtype.val_injective
    rw [LinearMap.codRestrict_apply, AlgHom.toLinearMap_apply, Basis.restrictScalars_apply,
      latticeBasis_apply]
    rfl
  simp_rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this, Basis.repr_self]

end NumberField.canonicalEmbedding

namespace NumberField.mixedEmbedding

open NumberField.InfinitePlace Module Finset

/-- The mixed space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K`. -/
abbrev mixedSpace :=
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)

/-- The mixed embedding of a number field `K` into the mixed space of `K`. -/
noncomputable def _root_.NumberField.mixedEmbedding : K →+* (mixedSpace K) :=
  RingHom.prod (Pi.ringHom fun w => embedding_of_isReal w.prop)
    (Pi.ringHom fun w => w.val.embedding)

@[simp]
theorem mixedEmbedding_apply_isReal (x : K) (w : {w // IsReal w}) :
    (mixedEmbedding K x).1 w = embedding_of_isReal w.prop x := by
  simp_rw [mixedEmbedding, RingHom.prod_apply, Pi.ringHom_apply]

@[simp]
theorem mixedEmbedding_apply_isComplex (x : K) (w : {w // IsComplex w}) :
    (mixedEmbedding K x).2 w = w.val.embedding x := by
  simp_rw [mixedEmbedding, RingHom.prod_apply, Pi.ringHom_apply]

@[deprecated (since := "2025-02-28")] alias mixedEmbedding_apply_ofIsReal :=
  mixedEmbedding_apply_isReal
@[deprecated (since := "2025-02-28")] alias mixedEmbedding_apply_ofIsComplex :=
  mixedEmbedding_apply_isComplex

instance [NumberField K] : Nontrivial (mixedSpace K) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  obtain hw | hw := w.isReal_or_isComplex
  · have : Nonempty {w : InfinitePlace K // IsReal w} := ⟨⟨w, hw⟩⟩
    exact nontrivial_prod_left
  · have : Nonempty {w : InfinitePlace K // IsComplex w} := ⟨⟨w, hw⟩⟩
    exact nontrivial_prod_right

protected theorem finrank [NumberField K] : finrank ℝ (mixedSpace K) = finrank ℚ K := by
  classical
  rw [finrank_prod, finrank_pi, finrank_pi_fintype, Complex.finrank_real_complex, sum_const,
    card_univ, ← nrRealPlaces, ← nrComplexPlaces, ← card_real_embeddings, Algebra.id.smul_eq_mul,
    mul_comm, ← card_complex_embeddings, ← NumberField.Embeddings.card K ℂ,
    Fintype.card_subtype_compl, Nat.add_sub_of_le (Fintype.card_subtype_le _)]

theorem _root_.NumberField.mixedEmbedding_injective [NumberField K] :
    Function.Injective (NumberField.mixedEmbedding K) := by
  exact RingHom.injective _

section Measure

open MeasureTheory.Measure MeasureTheory

variable [NumberField K]

open Classical in
instance : IsAddHaarMeasure (volume : Measure (mixedSpace K)) :=
  prod.instIsAddHaarMeasure volume volume

open Classical in
instance : NoAtoms (volume : Measure (mixedSpace K)) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  by_cases hw : IsReal w
  · have : NoAtoms (volume : Measure ({w : InfinitePlace K // IsReal w} → ℝ)) := pi_noAtoms ⟨w, hw⟩
    exact prod.instNoAtoms_fst
  · have : NoAtoms (volume : Measure ({w : InfinitePlace K // IsComplex w} → ℂ)) :=
      pi_noAtoms ⟨w, not_isReal_iff_isComplex.mp hw⟩
    exact prod.instNoAtoms_snd

variable {K} in
open Classical in
/-- The set of points in the mixedSpace that are equal to `0` at a fixed (real) place has
volume zero. -/
theorem volume_eq_zero (w : {w // IsReal w}) :
    volume ({x : mixedSpace K | x.1 w = 0}) = 0 := by
  let A : AffineSubspace ℝ (mixedSpace K) :=
    Submodule.toAffineSubspace (Submodule.mk ⟨⟨{x | x.1 w = 0}, by aesop⟩, rfl⟩ (by aesop))
  convert Measure.addHaar_affineSubspace volume A fun h ↦ ?_
  simpa [A] using (h ▸ Set.mem_univ _ : 1 ∈ A)

end Measure

section commMap

/-- The linear map that makes `canonicalEmbedding` and `mixedEmbedding` commute, see
`commMap_canonical_eq_mixed`. -/
noncomputable def commMap : ((K →+* ℂ) → ℂ) →ₗ[ℝ] (mixedSpace K) where
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
`canonicalEmbedding.latticeBasis` is a `ℝ`-basis of the mixed space `ℝ^r₁ × ℂ^r₂`,
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

noncomputable section norm

variable {K}

open scoped Classical in
/-- The norm at the infinite place `w` of an element of the mixed space -/
def normAtPlace (w : InfinitePlace K) : (mixedSpace K) →*₀ ℝ where
  toFun x := if hw : IsReal w then ‖x.1 ⟨w, hw⟩‖ else ‖x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩‖
  map_zero' := by simp
  map_one' := by simp
  map_mul' x y := by split_ifs <;> simp

theorem normAtPlace_nonneg (w : InfinitePlace K) (x : mixedSpace K) :
    0 ≤ normAtPlace w x := by
  rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs <;> exact norm_nonneg _

theorem normAtPlace_neg (w : InfinitePlace K) (x : mixedSpace K) :
    normAtPlace w (- x) = normAtPlace w x := by
  rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs <;> simp

theorem normAtPlace_add_le (w : InfinitePlace K) (x y : mixedSpace K) :
    normAtPlace w (x + y) ≤ normAtPlace w x + normAtPlace w y := by
  rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs <;> exact norm_add_le _ _

theorem normAtPlace_smul (w : InfinitePlace K) (x : mixedSpace K) (c : ℝ) :
    normAtPlace w (c • x) = |c| * normAtPlace w x := by
  rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs <;> simp

theorem normAtPlace_real (w : InfinitePlace K) (c : ℝ) :
    normAtPlace w ((fun _ ↦ c, fun _ ↦ c) : (mixedSpace K)) = |c| := by
  rw [show ((fun _ ↦ c, fun _ ↦ c) : (mixedSpace K)) = c • 1 by ext <;> simp, normAtPlace_smul,
    map_one, mul_one]

theorem normAtPlace_apply_of_isReal {w : InfinitePlace K} (hw : IsReal w) (x : mixedSpace K) :
    normAtPlace w x = ‖x.1 ⟨w, hw⟩‖ := by
  rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, dif_pos]

theorem normAtPlace_apply_of_isComplex {w : InfinitePlace K} (hw : IsComplex w) (x : mixedSpace K) :
    normAtPlace w x = ‖x.2 ⟨w, hw⟩‖ := by
  rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
    dif_neg (not_isReal_iff_isComplex.mpr hw)]

@[deprecated (since := "2025-02-28")] alias normAtPlace_apply_isReal := normAtPlace_apply_of_isReal
@[deprecated (since := "2025-02-28")] alias normAtPlace_apply_isComplex :=
  normAtPlace_apply_of_isComplex

@[simp]
theorem normAtPlace_apply (w : InfinitePlace K) (x : K) :
    normAtPlace w (mixedEmbedding K x) = w x := by
  simp_rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, mixedEmbedding,
    RingHom.prod_apply, Pi.ringHom_apply, norm_embedding_of_isReal, norm_embedding_eq, dite_eq_ite,
    ite_id]

theorem forall_normAtPlace_eq_zero_iff {x : mixedSpace K} :
    (∀ w, normAtPlace w x = 0) ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · ext w
    · exact norm_eq_zero.mp (normAtPlace_apply_of_isReal w.prop _ ▸ h w.1)
    · exact norm_eq_zero.mp (normAtPlace_apply_of_isComplex w.prop _ ▸ h w.1)
  · simp_rw [h, map_zero, implies_true]

@[simp]
theorem exists_normAtPlace_ne_zero_iff {x : mixedSpace K} :
    (∃ w, normAtPlace w x ≠ 0) ↔ x ≠ 0 := by
  rw [ne_eq, ← forall_normAtPlace_eq_zero_iff, not_forall]

@[fun_prop]
theorem continuous_normAtPlace (w : InfinitePlace K) :
    Continuous (normAtPlace w) := by
  simp_rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs <;> fun_prop

variable [NumberField K]

open scoped Classical in
theorem nnnorm_eq_sup_normAtPlace (x : mixedSpace K) :
    ‖x‖₊ = univ.sup fun w ↦ ⟨normAtPlace w x, normAtPlace_nonneg w x⟩ := by
  have :
      (univ : Finset (InfinitePlace K)) =
      (univ.image (fun w : {w : InfinitePlace K // IsReal w} ↦ w.1)) ∪
      (univ.image (fun w : {w : InfinitePlace K // IsComplex w} ↦ w.1)) := by
    ext; simp [isReal_or_isComplex]
  rw [this, sup_union, univ.sup_image, univ.sup_image,
    Prod.nnnorm_def, Pi.nnnorm_def, Pi.nnnorm_def]
  congr
  · ext w
    simp [normAtPlace_apply_of_isReal w.prop]
  · ext w
    simp [normAtPlace_apply_of_isComplex w.prop]

open scoped Classical in
theorem norm_eq_sup'_normAtPlace (x : mixedSpace K) :
    ‖x‖ = univ.sup' univ_nonempty fun w ↦ normAtPlace w x := by
  rw [← coe_nnnorm, nnnorm_eq_sup_normAtPlace, ← sup'_eq_sup univ_nonempty, ← NNReal.val_eq_coe,
    ← OrderHom.Subtype.val_coe, map_finset_sup', OrderHom.Subtype.val_coe]
  simp only [Function.comp_apply]

/-- The norm of `x` is `∏ w, (normAtPlace x) ^ mult w`. It is defined such that the norm of
`mixedEmbedding K a` for `a : K` is equal to the absolute value of the norm of `a` over `ℚ`,
see `norm_eq_norm`. -/
protected def norm : (mixedSpace K) →*₀ ℝ where
  toFun x := ∏ w, (normAtPlace w x) ^ (mult w)
  map_one' := by simp only [map_one, one_pow, prod_const_one]
  map_zero' := by simp [mult]
  map_mul' _ _ := by simp only [map_mul, mul_pow, prod_mul_distrib]

protected theorem norm_apply (x : mixedSpace K) :
    mixedEmbedding.norm x = ∏ w, (normAtPlace w x) ^ (mult w) := rfl

protected theorem norm_nonneg (x : mixedSpace K) :
    0 ≤ mixedEmbedding.norm x := univ.prod_nonneg fun _ _ ↦ pow_nonneg (normAtPlace_nonneg _ _) _

protected theorem norm_eq_zero_iff {x : mixedSpace K} :
    mixedEmbedding.norm x = 0 ↔ ∃ w, normAtPlace w x = 0 := by
  simp_rw [mixedEmbedding.norm, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, prod_eq_zero_iff,
    mem_univ, true_and, pow_eq_zero_iff mult_ne_zero]

protected theorem norm_ne_zero_iff {x : mixedSpace K} :
    mixedEmbedding.norm x ≠ 0 ↔ ∀ w, normAtPlace w x ≠ 0 := by
  rw [← not_iff_not]
  simp_rw [ne_eq, mixedEmbedding.norm_eq_zero_iff, not_not, not_forall, not_not]

theorem norm_eq_of_normAtPlace_eq {x y : mixedSpace K}
    (h : ∀ w, normAtPlace w x = normAtPlace w y) :
    mixedEmbedding.norm x = mixedEmbedding.norm y := by
  simp_rw [mixedEmbedding.norm_apply, h]

theorem norm_smul (c : ℝ) (x : mixedSpace K) :
    mixedEmbedding.norm (c • x) = |c| ^ finrank ℚ K * (mixedEmbedding.norm x) := by
  simp_rw [mixedEmbedding.norm_apply, normAtPlace_smul, mul_pow, prod_mul_distrib,
    prod_pow_eq_pow_sum, sum_mult_eq]

theorem norm_real (c : ℝ) :
    mixedEmbedding.norm ((fun _ ↦ c, fun _ ↦ c) : (mixedSpace K)) = |c| ^ finrank ℚ K := by
  rw [show ((fun _ ↦ c, fun _ ↦ c) : (mixedSpace K)) = c • 1 by ext <;> simp, norm_smul, map_one,
    mul_one]

@[simp]
theorem norm_eq_norm (x : K) :
    mixedEmbedding.norm (mixedEmbedding K x) = |Algebra.norm ℚ x| := by
  simp_rw [mixedEmbedding.norm_apply, normAtPlace_apply, prod_eq_abs_norm]

theorem norm_unit (u : (𝓞 K)ˣ) :
    mixedEmbedding.norm (mixedEmbedding K u) = 1 := by
  rw [norm_eq_norm, Units.norm, Rat.cast_one]

theorem norm_eq_zero_iff' {x : mixedSpace K} (hx : x ∈ Set.range (mixedEmbedding K)) :
    mixedEmbedding.norm x = 0 ↔ x = 0 := by
  obtain ⟨a, rfl⟩ := hx
  rw [norm_eq_norm, Rat.cast_abs, abs_eq_zero, Rat.cast_eq_zero, Algebra.norm_eq_zero_iff,
    map_eq_zero]

variable (K) in
@[fun_prop]
protected theorem continuous_norm : Continuous (mixedEmbedding.norm : (mixedSpace K) → ℝ) := by
  refine continuous_finset_prod Finset.univ fun _ _ ↦ ?_
  simp_rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, dite_pow]
  split_ifs <;> fun_prop

end norm

noncomputable section stdBasis

open Complex MeasureTheory MeasureTheory.Measure ZSpan Matrix ComplexConjugate

variable [NumberField K]

/-- The type indexing the basis `stdBasis`. -/
abbrev index := {w : InfinitePlace K // IsReal w} ⊕ ({w : InfinitePlace K // IsComplex w}) × (Fin 2)

open scoped Classical in
/-- The `ℝ`-basis of the mixed space of `K` formed by the vector equal to `1` at `w` and `0`
elsewhere for `IsReal w` and by the couple of vectors equal to `1` (resp. `I`) at `w` and `0`
elsewhere for `IsComplex w`. -/
def stdBasis : Basis (index K) ℝ (mixedSpace K) :=
  Basis.prod (Pi.basisFun ℝ _)
    (Basis.reindex (Pi.basis fun _ => basisOneI) (Equiv.sigmaEquivProd _ _))

variable {K}

@[simp]
theorem stdBasis_apply_isReal (x : mixedSpace K) (w : {w : InfinitePlace K // IsReal w}) :
    (stdBasis K).repr x (Sum.inl w) = x.1 w := rfl

@[simp]
theorem stdBasis_apply_isComplex_fst (x : mixedSpace K)
    (w : {w : InfinitePlace K // IsComplex w}) :
    (stdBasis K).repr x (Sum.inr ⟨w, 0⟩) = (x.2 w).re := rfl

@[simp]
theorem stdBasis_apply_isComplex_snd (x : mixedSpace K)
    (w : {w : InfinitePlace K // IsComplex w}) :
    (stdBasis K).repr x (Sum.inr ⟨w, 1⟩) = (x.2 w).im := rfl

@[deprecated (since := "2025-02-28")] alias stdBasis_apply_ofIsReal := stdBasis_apply_isReal
@[deprecated (since := "2025-02-28")] alias stdBasis_apply_ofIsComplex_fst :=
  stdBasis_apply_isComplex_fst
@[deprecated (since := "2025-02-28")] alias stdBasis_apply_ofIsComplex_snd :=
  stdBasis_apply_isComplex_snd

variable (K)

open scoped Classical in
theorem fundamentalDomain_stdBasis :
    fundamentalDomain (stdBasis K) =
        (Set.univ.pi fun _ => Set.Ico 0 1) ×ˢ
        (Set.univ.pi fun _ => Complex.measurableEquivPi⁻¹' (Set.univ.pi fun _ => Set.Ico 0 1)) := by
  ext
  simp [stdBasis, mem_fundamentalDomain, Complex.measurableEquivPi]

open scoped Classical in
theorem volume_fundamentalDomain_stdBasis :
    volume (fundamentalDomain (stdBasis K)) = 1 := by
  rw [fundamentalDomain_stdBasis, volume_eq_prod, prod_prod, volume_pi, volume_pi, pi_pi, pi_pi,
    Complex.volume_preserving_equiv_pi.measure_preimage ?_, volume_pi, pi_pi, Real.volume_Ico,
    sub_zero, ENNReal.ofReal_one, prod_const_one, prod_const_one, prod_const_one, one_mul]
  exact (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)).nullMeasurableSet

open scoped Classical in
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
      ← Module.finrank_eq_card_basis (stdBasis K)]

variable {K}

@[simp]
theorem indexEquiv_apply_isReal (w : {w : InfinitePlace K // IsReal w}) :
    (indexEquiv K) (Sum.inl w) = w.val.embedding := rfl

@[simp]
theorem indexEquiv_apply_isComplex_fst (w : {w : InfinitePlace K // IsComplex w}) :
    (indexEquiv K) (Sum.inr ⟨w, 0⟩) = w.val.embedding := rfl

@[simp]
theorem indexEquiv_apply_isComplex_snd (w : {w : InfinitePlace K // IsComplex w}) :
    (indexEquiv K) (Sum.inr ⟨w, 1⟩) = ComplexEmbedding.conjugate w.val.embedding := rfl

@[deprecated (since := "2025-02-28")] alias indexEquiv_apply_ofIsReal := indexEquiv_apply_isReal
@[deprecated (since := "2025-02-28")] alias indexEquiv_apply_ofIsComplex_fst :=
  indexEquiv_apply_isComplex_fst
@[deprecated (since := "2025-02-28")] alias indexEquiv_apply_ofIsComplex_snd :=
  indexEquiv_apply_isComplex_snd

variable (K)

open scoped Classical in
/-- The matrix that gives the representation on `stdBasis` of the image by `commMap` of an
element `x` of `(K →+* ℂ) → ℂ` fixed by the map `x_φ ↦ conj x_(conjugate φ)`,
see `stdBasis_repr_eq_matrixToStdBasis_mul`. -/
def matrixToStdBasis : Matrix (index K) (index K) ℂ :=
  fromBlocks (diagonal fun _ => 1) 0 0 <| reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)
    (blockDiagonal (fun _ => (2 : ℂ)⁻¹ • !![1, 1; - I, I]))

open scoped Classical in
theorem det_matrixToStdBasis :
    (matrixToStdBasis K).det = (2⁻¹ * I) ^ nrComplexPlaces K :=
  calc
  _ = ∏ _k : { w : InfinitePlace K // IsComplex w }, det ((2 : ℂ)⁻¹ • !![1, 1; -I, I]) := by
      rw [matrixToStdBasis, det_fromBlocks_zero₂₁, det_diagonal, prod_const_one, one_mul,
          det_reindex_self, det_blockDiagonal]
  _ = ∏ _k : { w : InfinitePlace K // IsComplex w }, (2⁻¹ * Complex.I) := by
      refine prod_congr (Eq.refl _) (fun _ _ => ?_)
      field_simp; ring
  _ = (2⁻¹ * Complex.I) ^ Fintype.card {w : InfinitePlace K // IsComplex w} := by
      rw [prod_const, Fintype.card]

open scoped Classical in
/-- Let `x : (K →+* ℂ) → ℂ` such that `x_φ = conj x_(conj φ)` for all `φ : K →+* ℂ`, then the
representation of `commMap K x` on `stdBasis` is given (up to reindexing) by the product of
`matrixToStdBasis` by `x`. -/
theorem stdBasis_repr_eq_matrixToStdBasis_mul (x : (K →+* ℂ) → ℂ)
    (hx : ∀ φ, conj (x φ) = x (ComplexEmbedding.conjugate φ)) (c : index K) :
    ((stdBasis K).repr (commMap K x) c : ℂ) =
      (matrixToStdBasis K *ᵥ (x ∘ (indexEquiv K))) c := by
  simp_rw [commMap, matrixToStdBasis, LinearMap.coe_mk, AddHom.coe_mk,
    mulVec, dotProduct, Function.comp_apply, index, Fintype.sum_sum_type,
    diagonal_one, reindex_apply, ← univ_product_univ, sum_product,
    indexEquiv_apply_isReal, Fin.sum_univ_two, indexEquiv_apply_isComplex_fst,
    indexEquiv_apply_isComplex_snd, smul_of, smul_cons, smul_eq_mul,
    mul_one, Matrix.smul_empty, Equiv.prodComm_symm, Equiv.coe_prodComm]
  cases c with
  | inl w =>
      simp_rw [stdBasis_apply_isReal, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
        one_apply, Matrix.zero_apply, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true,
        add_zero, sum_const_zero, add_zero, ← conj_eq_iff_re, hx (embedding w.val),
        conjugate_embedding_eq_of_isReal w.prop]
  | inr c =>
    rcases c with ⟨w, j⟩
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, id_eq, stdBasis_apply_isComplex_fst, re_eq_add_conj,
        mul_neg, fromBlocks_apply₂₁, zero_apply, zero_mul, sum_const_zero, fromBlocks_apply₂₂,
        submatrix_apply, Prod.swap_prod_mk, blockDiagonal_apply, of_apply, cons_val', cons_val_zero,
        empty_val', cons_val_fin_one, ite_mul, cons_val_one, head_cons, sum_add_distrib, sum_ite_eq,
        mem_univ, ↓reduceIte, ← hx (embedding w), zero_add]
      field_simp
    · simp only [Fin.mk_one, Fin.isValue, id_eq, stdBasis_apply_isComplex_snd, im_eq_sub_conj,
        mul_neg, fromBlocks_apply₂₁, zero_apply, zero_mul, sum_const_zero, fromBlocks_apply₂₂,
        submatrix_apply, Prod.swap_prod_mk, blockDiagonal_apply, of_apply, cons_val', cons_val_zero,
        empty_val', cons_val_fin_one, cons_val_one, head_fin_const, ite_mul, neg_mul, head_cons,
        sum_add_distrib, sum_ite_eq, mem_univ, ↓reduceIte, ← hx (embedding w), zero_add]
      ring_nf; field_simp

end stdBasis

noncomputable section integerLattice

variable [NumberField K]

open Module.Free

open scoped nonZeroDivisors

/-- The image of the ring of integers of `K` in the mixed space. -/
protected abbrev integerLattice : Submodule ℤ (mixedSpace K) :=
  LinearMap.range ((mixedEmbedding K).comp (algebraMap (𝓞 K) K)).toIntAlgHom.toLinearMap

/-- A `ℝ`-basis of the mixed space that is also a `ℤ`-basis of the image of `𝓞 K`. -/
def latticeBasis :
    Basis (ChooseBasisIndex ℤ (𝓞 K)) ℝ (mixedSpace K) := by
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
      finrank_pi_fintype, Complex.finrank_real_complex, sum_const, card_univ, ← nrRealPlaces,
      ← nrComplexPlaces, ← card_real_embeddings, Algebra.id.smul_eq_mul, mul_comm,
      ← card_complex_embeddings, ← NumberField.Embeddings.card K ℂ, Fintype.card_subtype_compl,
      Nat.add_sub_of_le (Fintype.card_subtype_le _)]

@[simp]
theorem latticeBasis_apply (i : ChooseBasisIndex ℤ (𝓞 K)) :
    latticeBasis K i = (mixedEmbedding K) (integralBasis K i) := by
  simp only [latticeBasis, coe_basisOfLinearIndependentOfCardEqFinrank, Function.comp_apply,
    canonicalEmbedding.latticeBasis_apply, integralBasis_apply, commMap_canonical_eq_mixed]

theorem mem_span_latticeBasis {x : (mixedSpace K)} :
    x ∈ Submodule.span ℤ (Set.range (latticeBasis K)) ↔
      x ∈ mixedEmbedding.integerLattice K := by
  rw [show Set.range (latticeBasis K) =
      (mixedEmbedding K).toIntAlgHom.toLinearMap '' (Set.range (integralBasis K)) by
    rw [← Set.range_comp]; exact congrArg Set.range (funext (fun i => latticeBasis_apply K i))]
  rw [← Submodule.map_span, ← SetLike.mem_coe, Submodule.map_coe]
  simp only [Set.mem_image, SetLike.mem_coe, mem_span_integralBasis K,
    RingHom.mem_range, exists_exists_eq_and]
  rfl

theorem span_latticeBasis :
    Submodule.span ℤ (Set.range (latticeBasis K)) = mixedEmbedding.integerLattice K :=
  Submodule.ext_iff.mpr fun _ ↦ mem_span_latticeBasis K

instance : DiscreteTopology (mixedEmbedding.integerLattice K) := by
  classical
  rw [← span_latticeBasis]
  infer_instance

open Classical in
instance : IsZLattice ℝ (mixedEmbedding.integerLattice K) := by
  simp_rw [← span_latticeBasis]
  infer_instance

open Classical in
theorem fundamentalDomain_integerLattice :
    MeasureTheory.IsAddFundamentalDomain (mixedEmbedding.integerLattice K)
      (ZSpan.fundamentalDomain (latticeBasis K)) := by
  rw [← span_latticeBasis]
  exact ZSpan.isAddFundamentalDomain (latticeBasis K) _

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
      latticeBasis_apply]
    rfl
  simp_rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this, Basis.repr_self]

variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The image of the fractional ideal `I` in the mixed space. -/
abbrev idealLattice : Submodule ℤ (mixedSpace K) := LinearMap.range <|
  (mixedEmbedding K).toIntAlgHom.toLinearMap ∘ₗ ((I : Submodule (𝓞 K) K).subtype.restrictScalars ℤ)

theorem mem_idealLattice {x : mixedSpace K} :
    x ∈ idealLattice K I ↔ ∃ y, y ∈ (I : Set K) ∧ mixedEmbedding K y = x := by
  simp [idealLattice]

/-- The generalized index of the lattice generated by `I` in the lattice generated by
`𝓞 K` is equal to the norm of the ideal `I`. The result is stated in terms of base change
determinant and is the translation of `NumberField.det_basisOfFractionalIdeal_eq_absNorm` in
the mixed space. This is useful, in particular, to prove that the family obtained from
the `ℤ`-basis of `I` is actually an `ℝ`-basis of the mixed space, see
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

/-- A `ℝ`-basis of the mixed space of `K` that is also a `ℤ`-basis of the image of the fractional
ideal `I`. -/
def fractionalIdealLatticeBasis :
    Basis (ChooseBasisIndex ℤ I) ℝ (mixedSpace K) := by
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

theorem mem_span_fractionalIdealLatticeBasis {x : (mixedSpace K)} :
    x ∈ Submodule.span ℤ (Set.range (fractionalIdealLatticeBasis K I)) ↔
      x ∈ mixedEmbedding K '' I := by
  rw [show Set.range (fractionalIdealLatticeBasis K I) =
        (mixedEmbedding K).toIntAlgHom.toLinearMap '' (Set.range (basisOfFractionalIdeal K I)) by
      rw [← Set.range_comp]
      exact congr_arg Set.range (funext (fun i ↦ fractionalIdealLatticeBasis_apply K I i))]
  rw [← Submodule.map_span, ← SetLike.mem_coe, Submodule.map_coe]
  rw [show Submodule.span ℤ (Set.range (basisOfFractionalIdeal K I)) = (I : Set K) by
        ext; simp [mem_span_basisOfFractionalIdeal]]
  rfl

theorem span_idealLatticeBasis :
    (Submodule.span ℤ (Set.range (fractionalIdealLatticeBasis K I))) =
      (mixedEmbedding.idealLattice K I) := by
  ext x
  simp [mem_span_fractionalIdealLatticeBasis]

instance : DiscreteTopology (mixedEmbedding.idealLattice K I) := by
  classical
  rw [← span_idealLatticeBasis]
  infer_instance

open Classical in
instance : IsZLattice ℝ (mixedEmbedding.idealLattice K I) := by
  simp_rw [← span_idealLatticeBasis]
  infer_instance

open Classical in
theorem fundamentalDomain_idealLattice :
    MeasureTheory.IsAddFundamentalDomain (mixedEmbedding.idealLattice K I)
      (ZSpan.fundamentalDomain (fractionalIdealLatticeBasis K I)) := by
  rw [← span_idealLatticeBasis]
  exact ZSpan.isAddFundamentalDomain (fractionalIdealLatticeBasis K I) _

end integerLattice

noncomputable section

namespace euclidean

open MeasureTheory NumberField Submodule

/-- The mixed space `ℝ^r₁ × ℂ^r₂`, with `(r₁, r₂)` the signature of `K`, as an Euclidean space. -/
protected abbrev mixedSpace :=
    (WithLp 2 ((EuclideanSpace ℝ {w : InfinitePlace K // IsReal w}) ×
      (EuclideanSpace ℂ {w : InfinitePlace K // IsComplex w})))

instance : Ring (euclidean.mixedSpace K) :=
  have : Ring (EuclideanSpace ℝ {w : InfinitePlace K // IsReal w}) := Pi.ring
  have : Ring (EuclideanSpace ℂ {w : InfinitePlace K // IsComplex w}) := Pi.ring
  inferInstanceAs (Ring (_ × _))

instance : MeasurableSpace (euclidean.mixedSpace K) := borel _

instance : BorelSpace (euclidean.mixedSpace K) := ⟨rfl⟩

variable [NumberField K]

open Classical in
/-- The continuous linear equivalence between the euclidean mixed space and the mixed space. -/
def toMixed : (euclidean.mixedSpace K) ≃L[ℝ] (mixedSpace K) :=
  (WithLp.linearEquiv _ _ _).toContinuousLinearEquiv

instance : Nontrivial (euclidean.mixedSpace K) := (toMixed K).toEquiv.nontrivial

protected theorem finrank :
    finrank ℝ (euclidean.mixedSpace K) = finrank ℚ K := by
  rw [LinearEquiv.finrank_eq (toMixed K).toLinearEquiv, mixedEmbedding.finrank]

open Classical in
/-- An orthonormal basis of the euclidean mixed space. -/
def stdOrthonormalBasis : OrthonormalBasis (index K) ℝ (euclidean.mixedSpace K) :=
  OrthonormalBasis.prod (EuclideanSpace.basisFun _ ℝ)
    ((Pi.orthonormalBasis fun _ ↦ Complex.orthonormalBasisOneI).reindex (Equiv.sigmaEquivProd _ _))

open Classical in
theorem stdOrthonormalBasis_map_eq :
    (euclidean.stdOrthonormalBasis K).toBasis.map (toMixed K).toLinearEquiv =
      mixedEmbedding.stdBasis K := by
  ext <;> rfl

open Classical in
theorem volumePreserving_toMixed :
    MeasurePreserving (toMixed K) where
  measurable := (toMixed K).continuous.measurable
  map_eq := by
    rw [← (OrthonormalBasis.addHaar_eq_volume (euclidean.stdOrthonormalBasis K)), Basis.map_addHaar,
      stdOrthonormalBasis_map_eq, Basis.addHaar_eq_iff, Basis.coe_parallelepiped,
      ← measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped (stdBasis K) volume),
      volume_fundamentalDomain_stdBasis K]

open Classical in
theorem volumePreserving_toMixed_symm :
    MeasurePreserving (toMixed K).symm := by
  have : MeasurePreserving (toMixed K).toHomeomorph.toMeasurableEquiv := volumePreserving_toMixed K
  exact this.symm

open Classical in
/-- The image of ring of integers `𝓞 K` in the euclidean mixed space. -/
protected def integerLattice : Submodule ℤ (euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (mixedEmbedding.integerLattice K) (toMixed K).toLinearMap

instance : DiscreteTopology (euclidean.integerLattice K) := by
  classical
  rw [euclidean.integerLattice]
  infer_instance

open Classical in
instance : IsZLattice ℝ (euclidean.integerLattice K) := by
  simp_rw [euclidean.integerLattice]
  infer_instance

end euclidean

end

noncomputable section plusPart

open ContinuousLinearEquiv

variable {K} (s : Set {w : InfinitePlace K // IsReal w})

open Classical in
/-- Let `s` be a set of real places, define the continuous linear equiv of the mixed space that
swaps sign at places in `s` and leaves the rest unchanged. -/
def negAt :
    mixedSpace K ≃L[ℝ] mixedSpace K :=
  (piCongrRight fun w ↦ if w ∈ s then neg ℝ else ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
    (ContinuousLinearEquiv.refl ℝ _)

variable {s}

@[simp]
theorem negAt_apply_isReal_and_mem (x : mixedSpace K) {w : {w // IsReal w}} (hw : w ∈ s) :
    (negAt s x).1 w = - x.1 w := by
  simp_rw [negAt, prodCongr_apply, piCongrRight_apply, if_pos hw,
    ContinuousLinearEquiv.neg_apply]

@[simp]
theorem negAt_apply_isReal_and_notMem (x : mixedSpace K) {w : {w // IsReal w}} (hw : w ∉ s) :
    (negAt s x).1 w = x.1 w := by
  simp_rw [negAt, prodCongr_apply, piCongrRight_apply, if_neg hw,
    ContinuousLinearEquiv.refl_apply]

@[deprecated (since := "2025-05-23")]
alias negAt_apply_isReal_and_not_mem := negAt_apply_isReal_and_notMem

@[simp]
theorem negAt_apply_isComplex (x : mixedSpace K) (w : {w // IsComplex w}) :
    (negAt s x).2 w = x.2 w := rfl

@[deprecated (since := "2025-02-28")] alias negAt_apply_of_isReal_and_mem :=
  negAt_apply_isReal_and_mem
@[deprecated (since := "2025-02-28")] alias negAt_apply_of_isReal_and_not_mem :=
  negAt_apply_isReal_and_notMem
@[deprecated (since := "2025-02-28")] alias negAt_apply_of_isComplex := negAt_apply_isComplex

@[simp]
theorem negAt_apply_snd (x : mixedSpace K) :
    (negAt s x).2 = x.2 := rfl

theorem negAt_apply_norm_isReal (x : mixedSpace K) (w : {w // IsReal w}) :
    ‖(negAt s x).1 w‖ = ‖x.1 w‖ := by
  by_cases hw : w ∈ s <;> simp [hw]

@[deprecated (since := "2025-02-28")] alias negAt_apply_abs_of_isReal := negAt_apply_norm_isReal
@[deprecated (since := "2025-03-01")] alias negAt_apply_abs_isReal := negAt_apply_norm_isReal

open MeasureTheory Classical in
/-- `negAt` preserves the volume . -/
theorem volume_preserving_negAt [NumberField K] :
    MeasurePreserving (negAt s) := by
  refine MeasurePreserving.prod (volume_preserving_pi fun w ↦ ?_) (MeasurePreserving.id _)
  by_cases hw : w ∈ s
  · simp_rw [if_pos hw]
    exact Measure.measurePreserving_neg _
  · simp_rw [if_neg hw]
    exact MeasurePreserving.id _

variable (s) in
/-- `negAt` preserves `normAtPlace`. -/
@[simp]
theorem normAtPlace_negAt (x : mixedSpace K) (w : InfinitePlace K) :
    normAtPlace w (negAt s x) = normAtPlace w x := by
  obtain hw | hw := isReal_or_isComplex w
  · simp_rw [normAtPlace_apply_of_isReal hw, negAt_apply_norm_isReal]
  · simp_rw [normAtPlace_apply_of_isComplex hw, negAt_apply_isComplex]

/-- `negAt` preserves the `norm`. -/
@[simp]
theorem norm_negAt [NumberField K] (x : mixedSpace K) :
    mixedEmbedding.norm (negAt s x) = mixedEmbedding.norm x :=
  norm_eq_of_normAtPlace_eq (fun w ↦ normAtPlace_negAt _ _ w)

/-- `negAt` is its own inverse. -/
@[simp]
theorem negAt_symm :
    (negAt s).symm = negAt s := by
  ext x w
  · by_cases hw : w ∈ s
    · simp_rw [negAt_apply_isReal_and_mem _ hw, negAt, prodCongr_symm,
        prodCongr_apply, piCongrRight_symm_apply, if_pos hw, symm_neg,
        neg_apply]
    · simp_rw [negAt_apply_isReal_and_notMem _ hw, negAt, prodCongr_symm,
        prodCongr_apply, piCongrRight_symm_apply, if_neg hw, refl_symm,
        refl_apply]
  · rfl

/-- For `x : mixedSpace K`, the set `signSet x` is the set of real places `w` s.t. `x w ≤ 0`. -/
def signSet (x : mixedSpace K) : Set {w : InfinitePlace K // IsReal w} := {w | x.1 w ≤ 0}

@[simp]
theorem negAt_signSet_apply_isReal (x : mixedSpace K) (w : {w // IsReal w}) :
    (negAt (signSet x) x).1 w = ‖x.1 w‖ := by
  by_cases hw : x.1 w ≤ 0
  · rw [negAt_apply_isReal_and_mem _ hw, Real.norm_of_nonpos hw]
  · rw [negAt_apply_isReal_and_notMem _ hw, Real.norm_of_nonneg (lt_of_not_ge hw).le]

@[simp]
theorem negAt_signSet_apply_isComplex (x : mixedSpace K) (w : {w // IsComplex w}) :
    (negAt (signSet x) x).2 w = x.2 w := rfl

@[deprecated (since := "2025-02-28")] alias negAt_signSet_apply_of_isReal :=
  negAt_signSet_apply_isReal
@[deprecated (since := "2025-02-28")] alias negAt_signSet_apply_of_isComplex :=
  negAt_signSet_apply_isComplex

variable (A : Set (mixedSpace K)) {x : mixedSpace K}

variable (s) in
/-- `negAt s A` is also equal to the preimage of `A` by `negAt s`. This fact is used to simplify
some proofs. -/
theorem negAt_preimage : negAt s ⁻¹' A = negAt s '' A := by
  rw [ContinuousLinearEquiv.image_eq_preimage, negAt_symm]

/-- The `plusPart` of a subset `A` of the `mixedSpace` is the set of points in `A` that are
positive at all real places. -/
abbrev plusPart : Set (mixedSpace K) := A ∩ {x | ∀ w, 0 < x.1 w}

theorem neg_of_mem_negA_plusPart (hx : x ∈ negAt s '' (plusPart A)) {w : {w // IsReal w}}
    (hw : w ∈ s) : x.1 w < 0 := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [negAt_apply_isReal_and_mem _ hw, neg_lt_zero]
  exact hy.2 w

theorem pos_of_notMem_negAt_plusPart (hx : x ∈ negAt s '' (plusPart A)) {w : {w // IsReal w}}
    (hw : w ∉ s) : 0 < x.1 w := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [negAt_apply_isReal_and_notMem _ hw]
  exact hy.2 w

@[deprecated (since := "2025-05-23")]
alias pos_of_not_mem_negAt_plusPart := pos_of_notMem_negAt_plusPart

open scoped Function in -- required for scoped `on` notation
/-- The images of `plusPart` by `negAt` are pairwise disjoint. -/
theorem disjoint_negAt_plusPart : Pairwise (Disjoint on (fun s ↦ negAt s '' (plusPart A))) := by
  intro s t hst
  refine Set.disjoint_left.mpr fun _ hx hx' ↦ ?_
  obtain ⟨w, hw | hw⟩ : ∃ w, (w ∈ s ∧ w ∉ t) ∨ (w ∈ t ∧ w ∉ s) := Set.symmDiff_nonempty.mpr hst
  · exact lt_irrefl _ <|
      (neg_of_mem_negA_plusPart A hx hw.1).trans (pos_of_notMem_negAt_plusPart A hx' hw.2)
  · exact lt_irrefl _ <|
      (neg_of_mem_negA_plusPart A hx' hw.1).trans (pos_of_notMem_negAt_plusPart A hx hw.2)

-- We will assume from now that `A` is symmetric at real places
variable (hA : ∀ x, x ∈ A ↔ (fun w ↦ ‖x.1 w‖, x.2) ∈ A)

include hA in
theorem mem_negAt_plusPart_of_mem (hx₁ : x ∈ A) (hx₂ : ∀ w, x.1 w ≠ 0) :
    x ∈ negAt s '' (plusPart A) ↔ (∀ w, w ∈ s → x.1 w < 0) ∧ (∀ w, w ∉ s → x.1 w > 0) := by
  refine ⟨fun hx ↦ ⟨fun _ hw ↦ neg_of_mem_negA_plusPart A hx hw,
      fun _ hw ↦ pos_of_notMem_negAt_plusPart A hx hw⟩,
      fun ⟨h₁, h₂⟩ ↦
        ⟨(fun w ↦ ‖x.1 w‖, x.2), ⟨(hA x).mp hx₁, fun w ↦ norm_pos_iff.mpr (hx₂ w)⟩, ?_⟩⟩
  ext w
  · by_cases hw : w ∈ s
    · simp [negAt_apply_isReal_and_mem _ hw, abs_of_neg (h₁ w hw)]
    · simp [negAt_apply_isReal_and_notMem _ hw, abs_of_pos (h₂ w hw)]
  · rfl

include hA in
/-- Assume that `A`  is symmetric at real places then, the union of the images of `plusPart`
by `negAt` and of the set of elements of `A` that are zero at at least one real place
is equal to `A`. -/
theorem iUnion_negAt_plusPart_union :
    (⋃ s, negAt s '' (plusPart A)) ∪ (A ∩ (⋃ w, {x | x.1 w = 0})) = A := by
  ext x
  rw [Set.mem_union, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iUnion]
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro (⟨s, ⟨x, ⟨hx, _⟩, rfl⟩⟩ | h)
    · simp_rw +singlePass [hA, negAt_apply_norm_isReal, negAt_apply_snd]
      rwa [← hA]
    · exact h.left
  · obtain hx | hx := exists_or_forall_not (fun w ↦ x.1 w = 0)
    · exact Or.inr ⟨h, hx⟩
    · refine Or.inl ⟨signSet x,
        (mem_negAt_plusPart_of_mem A hA h hx).mpr ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩⟩
      · exact lt_of_le_of_ne hw (hx w)
      · exact lt_of_le_of_ne (lt_of_not_ge hw).le (Ne.symm (hx w))

open MeasureTheory

variable [NumberField K]

include hA in
open Classical in
theorem iUnion_negAt_plusPart_ae :
    ⋃ s, negAt s '' (plusPart A) =ᵐ[volume] A := by
  nth_rewrite 2 [← iUnion_negAt_plusPart_union A hA]
  refine (MeasureTheory.union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr ?_)).symm
  exact measure_mono_null Set.inter_subset_right
    (measure_iUnion_null_iff.mpr fun _ ↦ volume_eq_zero _)

variable {A} in
theorem measurableSet_plusPart (hm : MeasurableSet A) :
    MeasurableSet (plusPart A) := by
  convert_to MeasurableSet (A ∩ (⋂ w, {x | 0 < x.1 w}))
  · ext; simp
  · refine hm.inter (MeasurableSet.iInter fun _ ↦ ?_)
    exact measurableSet_lt measurable_const ((measurable_pi_apply _).comp' measurable_fst)

variable (s) in
theorem measurableSet_negAt_plusPart (hm : MeasurableSet A) :
    MeasurableSet (negAt s '' (plusPart A)) :=
  negAt_preimage s _ ▸ (measurableSet_plusPart hm).preimage (negAt s).continuous.measurable

variable {A}

open Classical in
/-- The image of the `plusPart` of `A` by `negAt` have all the same volume as `plusPart A`. -/
theorem volume_negAt_plusPart (hm : MeasurableSet A) :
    volume (negAt s '' (plusPart A)) = volume (plusPart A) := by
  rw [← negAt_symm, ContinuousLinearEquiv.image_symm_eq_preimage,
    volume_preserving_negAt.measure_preimage (measurableSet_plusPart hm).nullMeasurableSet]

include hA in
open Classical in
/-- If a subset `A` of the `mixedSpace` is symmetric at real places, then its volume is
`2^ nrRealPlaces K` times the volume of its `plusPart`. -/
theorem volume_eq_two_pow_mul_volume_plusPart (hm : MeasurableSet A) :
    volume A = 2 ^ nrRealPlaces K * volume (plusPart A) := by
  simp only [← measure_congr (iUnion_negAt_plusPart_ae A hA),
    measure_iUnion (disjoint_negAt_plusPart A) (fun _ ↦ measurableSet_negAt_plusPart _ A hm),
    volume_negAt_plusPart hm, tsum_fintype, sum_const, card_univ, Fintype.card_set, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat, nrRealPlaces]

end plusPart

noncomputable section realSpace

open MeasureTheory

/--
The `realSpace` associated to a number field `K` is the real vector space indexed by the
infinite places of `K`.
-/
abbrev realSpace := InfinitePlace K → ℝ

variable {K}

/-- The set of points in the `realSpace` that are equal to `0` at a fixed place has volume zero. -/
theorem realSpace.volume_eq_zero [NumberField K] (w : InfinitePlace K) :
    volume ({x : realSpace K | x w = 0}) = 0 := by
  let A : AffineSubspace ℝ (realSpace K) :=
    Submodule.toAffineSubspace (Submodule.mk ⟨⟨{x | x w = 0}, by aesop⟩, rfl⟩ (by aesop))
  convert Measure.addHaar_affineSubspace volume A fun h ↦ ?_
  simpa [A] using (h ▸ Set.mem_univ _ : 1 ∈ A)

/--
The continuous linear map from `realSpace K` to `mixedSpace K` which is the identity at real
places and the natural map `ℝ → ℂ` at complex places.
-/
def mixedSpaceOfRealSpace : realSpace K →L[ℝ] mixedSpace K :=
  .prod (.pi fun w ↦ .proj w.1) (.pi fun w ↦ Complex.ofRealCLM.comp (.proj w.1))

theorem mixedSpaceOfRealSpace_apply (x : realSpace K) :
    mixedSpaceOfRealSpace x = ⟨fun w ↦ x w.1, fun w ↦ x w.1⟩ := rfl

variable (K) in
theorem injective_mixedSpaceOfRealSpace :
    Function.Injective (mixedSpaceOfRealSpace : realSpace K → mixedSpace K) := by
  refine (injective_iff_map_eq_zero mixedSpaceOfRealSpace).mpr fun _ h ↦ ?_
  rw [mixedSpaceOfRealSpace_apply, Prod.mk_eq_zero, funext_iff, funext_iff] at h
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · exact h.1 ⟨w, hw⟩
  · exact Complex.ofReal_inj.mp <| h.2 ⟨w, hw⟩

theorem normAtPlace_mixedSpaceOfRealSpace {x : realSpace K} {w : InfinitePlace K} (hx : 0 ≤ x w) :
    normAtPlace w (mixedSpaceOfRealSpace x) = x w := by
  simp only [mixedSpaceOfRealSpace_apply]
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtPlace_apply_of_isReal hw, Real.norm_of_nonneg hx]
  · rw [normAtPlace_apply_of_isComplex hw, Complex.norm_of_nonneg hx]

open scoped Classical in
/--
The map from the `mixedSpace K` to `realSpace K` that sends the values at complex places
to their norm.
-/
abbrev normAtComplexPlaces (x : mixedSpace K) : realSpace K :=
    fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩ else normAtPlace w x

@[simp]
theorem normAtComplexPlaces_apply_isReal {x : mixedSpace K} (w : {w // IsReal w}) :
    normAtComplexPlaces x w = x.1 w := by
  rw [normAtComplexPlaces, dif_pos]

@[simp]
theorem normAtComplexPlaces_apply_isComplex {x : mixedSpace K} (w : {w // IsComplex w}) :
    normAtComplexPlaces x w = ‖x.2 w‖ := by
  rw [normAtComplexPlaces, dif_neg (not_isReal_iff_isComplex.mpr w.prop),
    normAtPlace_apply_of_isComplex]

theorem normAtComplexPlaces_mixedSpaceOfRealSpace {x : realSpace K}
    (hx : ∀ w, IsComplex w → 0 ≤ x w) :
    normAtComplexPlaces (mixedSpaceOfRealSpace x) = x := by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtComplexPlaces_apply_isReal ⟨w, hw⟩, mixedSpaceOfRealSpace_apply]
  · rw [normAtComplexPlaces_apply_isComplex ⟨w, hw⟩, mixedSpaceOfRealSpace_apply,
      Complex.norm_of_nonneg (hx w hw)]

/--
The map from the `mixedSpace K` to `realSpace K` that sends each component to its norm.
-/
abbrev normAtAllPlaces (x : mixedSpace K) : realSpace K :=
    fun w ↦ normAtPlace w x

@[simp]
theorem normAtAllPlaces_apply (x : mixedSpace K) (w : InfinitePlace K) :
    normAtAllPlaces x w = normAtPlace w x := rfl

variable (K) in
theorem continuous_normAtAllPlaces :
    Continuous (normAtAllPlaces : mixedSpace K → realSpace K) := by fun_prop

theorem normAtAllPlaces_nonneg (x : mixedSpace K) (w : InfinitePlace K) :
    0 ≤ normAtAllPlaces x w := normAtPlace_nonneg _ _

theorem normAtAllPlaces_mixedSpaceOfRealSpace {x : realSpace K} (hx : ∀ w, 0 ≤ x w) :
    normAtAllPlaces (mixedSpaceOfRealSpace x) = x := by
  ext
  rw [normAtAllPlaces_apply, normAtPlace_mixedSpaceOfRealSpace (hx _)]

theorem normAtAllPlaces_mixedEmbedding (x : K) (w : InfinitePlace K) :
    normAtAllPlaces (mixedEmbedding K x) w = w x := by
  rw [normAtAllPlaces_apply, normAtPlace_apply]

theorem normAtAllPlaces_normAtAllPlaces (x : mixedSpace K) :
    normAtAllPlaces (mixedSpaceOfRealSpace (normAtAllPlaces x)) = normAtAllPlaces x :=
  normAtAllPlaces_mixedSpaceOfRealSpace fun _ ↦ (normAtAllPlaces_nonneg _ _)

theorem normAtAllPlaces_norm_at_real_places (x : mixedSpace K) :
    normAtAllPlaces (fun w ↦ ‖x.1 w‖, x.2) = normAtAllPlaces x := by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · simp_rw [normAtAllPlaces, normAtPlace_apply_of_isReal hw, norm_norm]
  · simp_rw [normAtAllPlaces, normAtPlace_apply_of_isComplex hw]

theorem normAtComplexPlaces_normAtAllPlaces (x : mixedSpace K) :
    normAtComplexPlaces (mixedSpaceOfRealSpace (normAtAllPlaces x)) = normAtAllPlaces x :=
  normAtComplexPlaces_mixedSpaceOfRealSpace fun _ _ ↦ (normAtAllPlaces_nonneg _ _)

theorem normAtAllPlaces_eq_of_normAtComplexPlaces_eq {x y : mixedSpace K}
    (h : normAtComplexPlaces x = normAtComplexPlaces y) :
    normAtAllPlaces x = normAtAllPlaces y := by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · simpa [normAtAllPlaces_apply, normAtPlace_apply_of_isReal hw,
      normAtComplexPlaces_apply_isReal ⟨w, hw⟩] using congr_arg (|·|) (congr_fun h w)
  · simpa [normAtAllPlaces_apply, normAtPlace_apply_of_isComplex hw,
      normAtComplexPlaces_apply_isComplex ⟨w, hw⟩] using congr_fun h w

theorem normAtAllPlaces_image_preimage_of_nonneg {s : Set (realSpace K)}
    (hs : ∀ x ∈ s, ∀ w, 0 ≤ x w) :
    normAtAllPlaces '' (normAtAllPlaces ⁻¹' s) = s := by
  rw [Set.image_preimage_eq_iff]
  rintro x hx
  refine ⟨mixedSpaceOfRealSpace x, funext fun w ↦ ?_⟩
  rw [normAtAllPlaces_apply, normAtPlace_mixedSpaceOfRealSpace (hs x hx w)]

end realSpace

end NumberField.mixedEmbedding
