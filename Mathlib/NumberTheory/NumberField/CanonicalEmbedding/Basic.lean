/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Algebra.Module.Zlattice.Basic
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
    · exact (hr.trans_le (norm_nonneg _)).not_le
    · exact fun h => hr.not_le (le_trans (norm_nonneg _) (h φ))
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
      exact ⟨x, ⟨SetLike.coe_mem x, fun φ => (heq _).mp hx φ⟩, rfl⟩
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
    x ∈ Submodule.span ℤ (Set.range (latticeBasis K)) ↔
      x ∈ ((canonicalEmbedding K).comp (algebraMap (𝓞 K) K)).range := by
  have h₁ : Set.range (latticeBasis K) =
      (canonicalEmbedding K).toIntAlgHom.toLinearMap '' (Set.range (integralBasis K)) := by
    rw [← Set.range_comp]; exact congrArg Set.range (funext (fun i => latticeBasis_apply K i))
  rw [h₁, ← Submodule.map_span, ← SetLike.mem_coe, Submodule.map_coe]
  rw [← RingHom.map_range, Subring.mem_map, Set.mem_image]
  simp only [SetLike.mem_coe, mem_span_integralBasis K, AlgHom.coe_toLinearMap,
    RingHom.coe_toIntAlgHom]

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

open NumberField NumberField.InfinitePlace FiniteDimensional Finset

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
  rw [finrank_prod, finrank_pi, finrank_pi_fintype, Complex.finrank_real_complex, sum_const,
    card_univ, ← NrRealPlaces, ← NrComplexPlaces, ← card_real_embeddings, Algebra.id.smul_eq_mul,
    mul_comm, ← card_complex_embeddings, ← NumberField.Embeddings.card K ℂ,
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

noncomputable section norm

open scoped Classical

variable {K}

/-- The norm at the infinite place `w` of an element of
`({w // IsReal w} → ℝ) × ({ w // IsComplex w } → ℂ)`. -/
def normAtPlace (w : InfinitePlace K) : (E K) →*₀ ℝ where
  toFun x := if hw : IsReal w then ‖x.1 ⟨w, hw⟩‖ else ‖x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩‖
  map_zero' := by simp
  map_one' := by simp
  map_mul' x y := by split_ifs <;> simp

theorem normAtPlace_nonneg  (w : InfinitePlace K) (x : E K) :
    0 ≤ normAtPlace w x := by
  rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs <;> exact norm_nonneg _

theorem normAtPlace_neg (w : InfinitePlace K) (x : E K)  :
    normAtPlace w (- x) = normAtPlace w x := by
  rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs <;> simp

theorem normAtPlace_add_le (w : InfinitePlace K) (x y : E K) :
    normAtPlace w (x + y) ≤ normAtPlace w x + normAtPlace w y := by
  rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs <;> exact norm_add_le _ _

theorem normAtPlace_smul (w : InfinitePlace K) (x : E K) (c : ℝ) :
    normAtPlace w (c • x) = |c| * normAtPlace w x := by
  rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs
  · rw [Prod.smul_fst, Pi.smul_apply, norm_smul, Real.norm_eq_abs]
  · rw [Prod.smul_snd, Pi.smul_apply, norm_smul, Real.norm_eq_abs, Complex.norm_eq_abs]

theorem normAtPlace_real (w : InfinitePlace K) (c : ℝ) :
    normAtPlace w ((fun _ ↦ c, fun _ ↦ c) : (E K)) = |c| := by
  rw [show ((fun _ ↦ c, fun _ ↦ c) : (E K)) = c • 1 by ext <;> simp, normAtPlace_smul, map_one,
    mul_one]

theorem normAtPlace_apply_isReal {w : InfinitePlace K} (hw : IsReal w) (x : E K):
    normAtPlace w x = ‖x.1 ⟨w, hw⟩‖ := by
  rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, dif_pos]

theorem normAtPlace_apply_isComplex {w : InfinitePlace K} (hw : IsComplex w) (x : E K) :
    normAtPlace w x = ‖x.2 ⟨w, hw⟩‖ := by
  rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
    dif_neg (not_isReal_iff_isComplex.mpr hw)]

@[simp]
theorem normAtPlace_apply (w : InfinitePlace K) (x : K) :
    normAtPlace w (mixedEmbedding K x) = w x := by
  simp_rw [normAtPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, mixedEmbedding,
    RingHom.prod_apply, Pi.ringHom_apply, norm_embedding_of_isReal, norm_embedding_eq, dite_eq_ite,
    ite_id]

theorem normAtPlace_eq_zero {x : E K} :
    (∀ w, normAtPlace w x = 0) ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · ext w
    · exact norm_eq_zero'.mp (normAtPlace_apply_isReal w.prop _ ▸ h w.1)
    · exact norm_eq_zero'.mp (normAtPlace_apply_isComplex w.prop _ ▸ h w.1)
  · simp_rw [h, map_zero, implies_true]

variable [NumberField K]

theorem nnnorm_eq_sup_normAtPlace (x : E K) :
    ‖x‖₊ = univ.sup fun w ↦ ⟨normAtPlace w x, normAtPlace_nonneg w x⟩ := by
  have :
      (univ : Finset (InfinitePlace K)) =
      (univ.image (fun w : {w : InfinitePlace K // IsReal w} ↦ w.1)) ∪
      (univ.image (fun w : {w : InfinitePlace K // IsComplex w} ↦ w.1)) := by
    ext; simp [isReal_or_isComplex]
  rw [this, sup_union, univ.sup_image, univ.sup_image, sup_eq_max,
    Prod.nnnorm_def', Pi.nnnorm_def, Pi.nnnorm_def]
  congr
  · ext w
    simp [normAtPlace_apply_isReal w.prop]
  · ext w
    simp [normAtPlace_apply_isComplex w.prop]

theorem norm_eq_sup'_normAtPlace (x : E K) :
    ‖x‖ = univ.sup' univ_nonempty fun w ↦ normAtPlace w x := by
  rw [← coe_nnnorm, nnnorm_eq_sup_normAtPlace, ← sup'_eq_sup univ_nonempty, ← NNReal.val_eq_coe,
    ← OrderHom.Subtype.val_coe, map_finset_sup', OrderHom.Subtype.val_coe]
  simp only [Function.comp_apply]

/-- The norm of `x` is `∏ w, (normAtPlace x) ^ mult w`. It is defined such that the norm of
`mixedEmbedding K a` for `a : K` is equal to the absolute value of the norm of `a` over `ℚ`,
see `norm_eq_norm`. -/
protected def norm : (E K) →*₀ ℝ where
  toFun x := ∏ w, (normAtPlace w x) ^ (mult w)
  map_one' := by simp only [map_one, one_pow, prod_const_one]
  map_zero' := by simp [mult]
  map_mul' _ _ := by simp only [map_mul, mul_pow, prod_mul_distrib]

protected theorem norm_apply (x : E K) :
    mixedEmbedding.norm x = ∏ w, (normAtPlace w x) ^ (mult w) := rfl

protected theorem norm_nonneg (x : E K) :
    0 ≤ mixedEmbedding.norm x := univ.prod_nonneg fun _ _ ↦ pow_nonneg (normAtPlace_nonneg _ _) _

protected theorem norm_eq_zero_iff {x : E K} :
    mixedEmbedding.norm x = 0 ↔ ∃ w, normAtPlace w x = 0 := by
  simp_rw [mixedEmbedding.norm, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, prod_eq_zero_iff,
    mem_univ, true_and, pow_eq_zero_iff mult_ne_zero]

protected theorem norm_ne_zero_iff {x : E K} :
    mixedEmbedding.norm x ≠ 0 ↔ ∀ w, normAtPlace w x ≠ 0 := by
  rw [← not_iff_not]
  simp_rw [ne_eq, mixedEmbedding.norm_eq_zero_iff, not_not, not_forall, not_not]

theorem norm_smul (c : ℝ) (x : E K) :
    mixedEmbedding.norm (c • x) = |c| ^ finrank ℚ K * (mixedEmbedding.norm x) := by
  simp_rw [mixedEmbedding.norm_apply, normAtPlace_smul, mul_pow, prod_mul_distrib,
    prod_pow_eq_pow_sum, sum_mult_eq]

theorem norm_real (c : ℝ) :
    mixedEmbedding.norm ((fun _ ↦ c, fun _ ↦ c) : (E K)) = |c| ^ finrank ℚ K := by
  rw [show ((fun _ ↦ c, fun _ ↦ c) : (E K)) = c • 1 by ext <;> simp, norm_smul, map_one, mul_one]

@[simp]
theorem norm_eq_norm (x : K) :
    mixedEmbedding.norm (mixedEmbedding K x) = |Algebra.norm ℚ x| := by
  simp_rw [mixedEmbedding.norm_apply, normAtPlace_apply, prod_eq_abs_norm]

theorem norm_eq_zero_iff' {x : E K} (hx : x ∈ Set.range (mixedEmbedding K)) :
    mixedEmbedding.norm x = 0 ↔ x = 0 := by
  obtain ⟨a, rfl⟩ := hx
  rw [norm_eq_norm, Rat.cast_abs, abs_eq_zero, Rat.cast_eq_zero, Algebra.norm_eq_zero_iff,
    map_eq_zero]

end norm

noncomputable section stdBasis

open scoped Classical

open Complex MeasureTheory MeasureTheory.Measure Zspan Matrix BigOperators Finset ComplexConjugate

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
    sub_zero, ENNReal.ofReal_one, prod_const_one, prod_const_one, prod_const_one, one_mul]
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
      rw [matrixToStdBasis, det_fromBlocks_zero₂₁, det_diagonal, prod_const_one, one_mul,
          det_reindex_self, det_blockDiagonal]
  _ = ∏ _k : { w : InfinitePlace K // IsComplex w }, (2⁻¹ * Complex.I) := by
      refine prod_congr (Eq.refl _) (fun _ _ => ?_)
      field_simp; ring
  _ = (2⁻¹ * Complex.I) ^ Fintype.card {w : InfinitePlace K // IsComplex w} := by
      rw [prod_const, Fintype.card]

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
    indexEquiv_apply_ofIsReal, Fin.sum_univ_two, indexEquiv_apply_ofIsComplex_fst,
    indexEquiv_apply_ofIsComplex_snd, smul_of, smul_cons, smul_eq_mul,
    mul_one, Matrix.smul_empty, Equiv.prodComm_symm, Equiv.coe_prodComm]
  cases c with
  | inl w =>
      simp_rw [stdBasis_apply_ofIsReal, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
        one_apply, Matrix.zero_apply, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true,
        add_zero, sum_const_zero, add_zero, ← conj_eq_iff_re, hx (embedding w.val),
        conjugate_embedding_eq_of_isReal w.prop]
  | inr c =>
    rcases c with ⟨w, j⟩
    fin_cases j
    · simp_rw [Fin.mk_zero, stdBasis_apply_ofIsComplex_fst, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, Matrix.zero_apply, submatrix_apply,
        blockDiagonal_apply, Prod.swap_prod_mk, ite_mul, zero_mul, sum_const_zero, zero_add,
        sum_add_distrib, sum_ite_eq, mem_univ, ite_true, of_apply, cons_val', cons_val_zero,
        cons_val_one, head_cons, ← hx (embedding w), re_eq_add_conj]
      field_simp
    · simp_rw [Fin.mk_one, stdBasis_apply_ofIsComplex_snd, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, Matrix.zero_apply, submatrix_apply, blockDiagonal_apply,
        Prod.swap_prod_mk, ite_mul, zero_mul, sum_const_zero, zero_add, sum_add_distrib, sum_ite_eq,
        mem_univ, ite_true, of_apply, cons_val', cons_val_zero, cons_val_one, head_cons,
        ← hx (embedding w), im_eq_sub_conj]
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
      finrank_pi_fintype, Complex.finrank_real_complex, sum_const, card_univ, ← NrRealPlaces,
      ← NrComplexPlaces, ← card_real_embeddings, Algebra.id.smul_eq_mul, mul_comm,
      ← card_complex_embeddings, ← NumberField.Embeddings.card K ℂ, Fintype.card_subtype_compl,
      Nat.add_sub_of_le (Fintype.card_subtype_le _)]

@[simp]
theorem latticeBasis_apply (i : ChooseBasisIndex ℤ (𝓞 K)) :
    latticeBasis K i = (mixedEmbedding K) (integralBasis K i) := by
  simp only [latticeBasis, coe_basisOfLinearIndependentOfCardEqFinrank, Function.comp_apply,
    canonicalEmbedding.latticeBasis_apply, integralBasis_apply, commMap_canonical_eq_mixed]

theorem mem_span_latticeBasis (x : (E K)) :
    x ∈ Submodule.span ℤ (Set.range (latticeBasis K)) ↔
      x ∈ ((mixedEmbedding K).comp (algebraMap (𝓞 K) K)).range := by
  have h₁ : Set.range (latticeBasis K) =
      (mixedEmbedding K).toIntAlgHom.toLinearMap '' (Set.range (integralBasis K)) := by
    rw [← Set.range_comp]; exact congrArg Set.range (funext (fun i => latticeBasis_apply K i))
  rw [h₁]
  rw [← Submodule.map_span, ← SetLike.mem_coe, Submodule.map_coe]
  simp only [Set.mem_image, SetLike.mem_coe, mem_span_integralBasis K,
    RingHom.mem_range, exists_exists_eq_and, AlgHom.coe_toLinearMap, RingHom.coe_toIntAlgHom,
    RingHom.coe_comp, Function.comp_apply]

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

end NumberField.mixedEmbedding
