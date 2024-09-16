/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Mathlib.Tactic.Rify

/-!
# Number field discriminant
This file defines the discriminant of a number field.

## Main definitions

* `NumberField.discr`: the absolute discriminant of a number field.

## Main result

* `NumberField.abs_discr_gt_two`: **Hermite-Minkowski Theorem**. A nontrivial number field has
discriminant greater than `2`.

* `NumberField.finite_of_discr_bdd`: **Hermite Theorem**. Let `N` be an integer. There are only
finitely many number fields (in some fixed extension of `ℚ`) of discriminant bounded by `N`.

## Tags
number field, discriminant
-/

-- TODO. Rewrite some of the FLT results on the disciminant using the definitions and results of
-- this file

namespace NumberField

open FiniteDimensional NumberField NumberField.InfinitePlace Matrix

open scoped Classical Real nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

/-- The absolute discriminant of a number field. -/
noncomputable abbrev discr : ℤ := Algebra.discr ℤ (RingOfIntegers.basis K)

theorem coe_discr : (discr K : ℚ) = Algebra.discr ℚ (integralBasis K) :=
  (Algebra.discr_localizationLocalization ℤ _ K (RingOfIntegers.basis K)).symm

theorem discr_ne_zero : discr K ≠ 0 := by
  rw [← (Int.cast_injective (α := ℚ)).ne_iff, coe_discr]
  exact Algebra.discr_not_zero_of_basis ℚ (integralBasis K)

theorem discr_eq_discr {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ (𝓞 K)) :
    Algebra.discr ℤ b = discr K := by
  let b₀ := Basis.reindex (RingOfIntegers.basis K) (Basis.indexEquiv (RingOfIntegers.basis K) b)
  rw [Algebra.discr_eq_discr (𝓞 K) b b₀, Basis.coe_reindex, Algebra.discr_reindex]

theorem discr_eq_discr_of_algEquiv {L : Type*} [Field L] [NumberField L] (f : K ≃ₐ[ℚ] L) :
    discr K = discr L := by
  let f₀ : 𝓞 K ≃ₗ[ℤ] 𝓞 L := (f.restrictScalars ℤ).mapIntegralClosure.toLinearEquiv
  rw [← Rat.intCast_inj, coe_discr, Algebra.discr_eq_discr_of_algEquiv (integralBasis K) f,
    ← discr_eq_discr L ((RingOfIntegers.basis K).map f₀)]
  change _ = algebraMap ℤ ℚ _
  rw [← Algebra.discr_localizationLocalization ℤ (nonZeroDivisors ℤ) L]
  congr
  ext
  simp only [Function.comp_apply, integralBasis_apply, Basis.localizationLocalization_apply,
    Basis.map_apply]
  rfl

open MeasureTheory MeasureTheory.Measure ZSpan NumberField.mixedEmbedding
  NumberField.InfinitePlace ENNReal NNReal Complex

theorem _root_.NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis :
    volume (fundamentalDomain (latticeBasis K)) =
      (2 : ℝ≥0∞)⁻¹ ^ NrComplexPlaces K * sqrt ‖discr K‖₊ := by
  let f : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ (K →+* ℂ) :=
    (canonicalEmbedding.latticeBasis K).indexEquiv (Pi.basisFun ℂ _)
  let e : (index K) ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 K) := (indexEquiv K).trans f.symm
  let M := (mixedEmbedding.stdBasis K).toMatrix ((latticeBasis K).reindex e.symm)
  let N := Algebra.embeddingsMatrixReindex ℚ ℂ (integralBasis K ∘ f.symm)
    RingHom.equivRatAlgHom
  suffices M.map Complex.ofReal = (matrixToStdBasis K) *
      (Matrix.reindex (indexEquiv K).symm (indexEquiv K).symm N).transpose by
    calc volume (fundamentalDomain (latticeBasis K))
      _ = ‖((mixedEmbedding.stdBasis K).toMatrix ((latticeBasis K).reindex e.symm)).det‖₊ := by
        rw [← fundamentalDomain_reindex _ e.symm, ← norm_toNNReal, measure_fundamentalDomain
          ((latticeBasis K).reindex e.symm), volume_fundamentalDomain_stdBasis, mul_one]
        rfl
      _ = ‖(matrixToStdBasis K).det * N.det‖₊ := by
        rw [← nnnorm_real, ← ofReal_eq_coe, RingHom.map_det, RingHom.mapMatrix_apply, this,
          det_mul, det_transpose, det_reindex_self]
      _ = (2 : ℝ≥0∞)⁻¹ ^ Fintype.card {w : InfinitePlace K // IsComplex w} * sqrt ‖N.det ^ 2‖₊ := by
        have : ‖Complex.I‖₊ = 1 := by rw [← norm_toNNReal, norm_eq_abs, abs_I, Real.toNNReal_one]
        rw [det_matrixToStdBasis, nnnorm_mul, nnnorm_pow, nnnorm_mul, this, mul_one, nnnorm_inv,
          coe_mul, ENNReal.coe_pow, ← norm_toNNReal, RCLike.norm_two, Real.toNNReal_ofNat,
          coe_inv two_ne_zero, coe_ofNat, nnnorm_pow, NNReal.sqrt_sq]
      _ = (2 : ℝ≥0∞)⁻¹ ^ Fintype.card { w // IsComplex w } * NNReal.sqrt ‖discr K‖₊ := by
        rw [← Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two, Algebra.discr_reindex,
          ← coe_discr, map_intCast, ← Complex.nnnorm_intCast]
  ext : 2
  dsimp only [M]
  rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.coe_reindex, Function.comp_apply,
    Equiv.symm_symm, latticeBasis_apply, ← commMap_canonical_eq_mixed, Complex.ofReal_eq_coe,
    stdBasis_repr_eq_matrixToStdBasis_mul K _ (fun _ => rfl)]
  rfl

theorem exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K), a ≠ 0 ∧
      |Algebra.norm ℚ (a : K)| ≤ FractionalIdeal.absNorm I.1 * (4 / π) ^ NrComplexPlaces K *
        (finrank ℚ K).factorial / (finrank ℚ K) ^ (finrank ℚ K) * Real.sqrt |discr K| := by
  -- The smallest possible value for `exists_ne_zero_mem_ideal_of_norm_le`
  let B := (minkowskiBound K I * (convexBodySumFactor K)⁻¹).toReal ^ (1 / (finrank ℚ K : ℝ))
  have h_le : (minkowskiBound K I) ≤ volume (convexBodySum K B) := by
    refine le_of_eq ?_
    rw [convexBodySum_volume, ← ENNReal.ofReal_pow (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul toReal_nonneg, div_mul_cancel₀, Real.rpow_one, ofReal_toReal, mul_comm,
      mul_assoc, ← coe_mul, inv_mul_cancel₀ (convexBodySumFactor_ne_zero K), ENNReal.coe_one,
      mul_one]
    · exact mul_ne_top (ne_of_lt (minkowskiBound_lt_top K I)) coe_ne_top
    · exact (Nat.cast_ne_zero.mpr (ne_of_gt finrank_pos))
  convert exists_ne_zero_mem_ideal_of_norm_le K I h_le
  rw [div_pow B, ← Real.rpow_natCast B, ← Real.rpow_mul (by positivity), div_mul_cancel₀ _
    (Nat.cast_ne_zero.mpr <| ne_of_gt finrank_pos), Real.rpow_one, mul_comm_div, mul_div_assoc']
  congr 1
  rw [eq_comm]
  calc
    _ = FractionalIdeal.absNorm I.1 * (2 : ℝ)⁻¹ ^ NrComplexPlaces K * sqrt ‖discr K‖₊ *
          (2 : ℝ) ^ finrank ℚ K * ((2 : ℝ) ^ NrRealPlaces K * (π / 2) ^ NrComplexPlaces K /
            (Nat.factorial (finrank ℚ K)))⁻¹ := by
      simp_rw [minkowskiBound, convexBodySumFactor,
        volume_fundamentalDomain_fractionalIdealLatticeBasis,
        volume_fundamentalDomain_latticeBasis, toReal_mul, toReal_pow, toReal_inv, coe_toReal,
        toReal_ofNat, mixedEmbedding.finrank, mul_assoc]
      rw [ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg I.1))]
      simp_rw [NNReal.coe_inv, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_div,
        coe_real_pi, NNReal.coe_ofNat, NNReal.coe_natCast]
    _ = FractionalIdeal.absNorm I.1 * (2 : ℝ) ^ (finrank ℚ K - NrComplexPlaces K - NrRealPlaces K +
          NrComplexPlaces K : ℤ) * Real.sqrt ‖discr K‖ * Nat.factorial (finrank ℚ K) *
            π⁻¹ ^ (NrComplexPlaces K) := by
      simp_rw [inv_div, div_eq_mul_inv, mul_inv, ← zpow_neg_one, ← zpow_natCast, mul_zpow,
        ← zpow_mul, neg_one_mul, mul_neg_one, neg_neg, Real.coe_sqrt, coe_nnnorm, sub_eq_add_neg,
        zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0)]
      ring
    _ = FractionalIdeal.absNorm I.1 * (2 : ℝ) ^ (2 * NrComplexPlaces K : ℤ) * Real.sqrt ‖discr K‖ *
          Nat.factorial (finrank ℚ K) * π⁻¹ ^ (NrComplexPlaces K) := by
      congr
      rw [← card_add_two_mul_card_eq_rank, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring
    _ = FractionalIdeal.absNorm I.1 * (4 / π) ^ NrComplexPlaces K * (finrank ℚ K).factorial *
          Real.sqrt |discr K| := by
      rw [Int.norm_eq_abs, zpow_mul, show (2 : ℝ) ^ (2 : ℤ) = 4 by norm_cast, div_pow,
        inv_eq_one_div, div_pow, one_pow, zpow_natCast]
      ring

theorem exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_discr :
    ∃ (a : 𝓞 K), a ≠ 0 ∧
      |Algebra.norm ℚ (a : K)| ≤ (4 / π) ^ NrComplexPlaces K *
        (finrank ℚ K).factorial / (finrank ℚ K) ^ (finrank ℚ K) * Real.sqrt |discr K| := by
  obtain ⟨_, h_mem, h_nz, h_nm⟩ := exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr K ↑1
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp h_mem
  refine ⟨a, ne_zero_of_map h_nz, ?_⟩
  simp_rw [Units.val_one, FractionalIdeal.absNorm_one, Rat.cast_one, one_mul] at h_nm
  exact h_nm

variable {K}

theorem abs_discr_ge (h : 1 < finrank ℚ K) :
    (4 / 9 : ℝ) * (3 * π / 4) ^ finrank ℚ K ≤ |discr K| := by
  -- We use `exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_discr` to get a nonzero
  -- algebraic integer `x` of small norm and the fact that `1 ≤ |Norm x|` to get a lower bound
  -- on `sqrt |discr K|`.
  obtain ⟨x, h_nz, h_bd⟩ := exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_discr K
  have h_nm : (1 : ℝ) ≤ |Algebra.norm ℚ (x : K)| := by
    rw [← Algebra.coe_norm_int, ← Int.cast_one, ← Int.cast_abs, Rat.cast_intCast, Int.cast_le]
    exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr h_nz)
  replace h_bd := le_trans h_nm h_bd
  rw [← inv_mul_le_iff (by positivity), inv_div, mul_one, Real.le_sqrt (by positivity)
    (by positivity), ← Int.cast_abs, div_pow, mul_pow, ← pow_mul, ← pow_mul] at h_bd
  refine le_trans ?_ h_bd
  -- The sequence `a n` is a lower bound for `|discr K|`. We prove below by induction an uniform
  -- lower bound for this sequence from which we deduce the result.
  let a : ℕ → ℝ := fun n => (n : ℝ) ^ (n * 2) / ((4 / π) ^ n * (n.factorial : ℝ) ^ 2)
  suffices ∀ n, 2 ≤ n → (4 / 9 : ℝ) * (3 * π / 4) ^ n ≤ a n by
    refine le_trans (this (finrank ℚ K) h) ?_
    simp only [a]
    gcongr
    · exact (one_le_div Real.pi_pos).2 Real.pi_le_four
    · rw [← card_add_two_mul_card_eq_rank, mul_comm]
      exact Nat.le_add_left _ _
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact le_of_eq <| by norm_num [a, Nat.factorial_two]; field_simp; ring
  | succ m _ h_m =>
      suffices (3 : ℝ) ≤ (1 + 1 / m : ℝ) ^ (2 * m) by
        convert_to _ ≤ (a m) * (1 + 1 / m : ℝ) ^ (2 * m) / (4 / π)
        · simp_rw [a, add_mul, one_mul, pow_succ, Nat.factorial_succ]
          field_simp; ring
        · rw [_root_.le_div_iff₀ (by positivity), pow_succ]
          convert (mul_le_mul h_m this (by positivity) (by positivity)) using 1
          field_simp; ring
      refine le_trans (le_of_eq (by field_simp; norm_num)) (one_add_mul_le_pow ?_ (2 * m))
      exact le_trans (by norm_num : (-2 : ℝ) ≤ 0) (by positivity)

/-- **Hermite-Minkowski Theorem**. A nontrivial number field has discriminant greater than `2`. -/
theorem abs_discr_gt_two (h : 1 < finrank ℚ K) : 2 < |discr K| := by
  rw [← Nat.succ_le_iff] at h
  rify
  calc
    (2 : ℝ) < (4 / 9) * (3 * π / 4) ^ 2 := by
      nlinarith [Real.pi_gt_three]
    _ ≤ (4 / 9 : ℝ) * (3 * π / 4) ^ finrank ℚ K := by
      gcongr
      linarith [Real.pi_gt_three]
    _ ≤ |(discr K : ℝ)| := mod_cast abs_discr_ge h

/-!
### Hermite Theorem
This section is devoted to the proof of Hermite theorem.

Let `N` be an integer . We prove that the set `S` of finite extensions `K` of `ℚ`
(in some fixed extension `A` of `ℚ`) such that `|discr K| ≤ N` is finite by proving, using
`finite_of_finite_generating_set`, that there exists a finite set `T ⊆ A` such that
`∀ K ∈ S, ∃ x ∈ T, K = ℚ⟮x⟯` .

To find the set `T`, we construct a finite set `T₀` of polynomials in `ℤ[X]` containing, for each
`K ∈ S`, the minimal polynomial of a primitive element of `K`. The set `T` is then the union of
roots in `A` of the polynomials in `T₀`. More precisely, the set `T₀` is the set of all polynomials
in `ℤ[X]` of degrees and coefficients bounded by some explicit constants depending only on `N`.

Indeed, we prove that, for any field `K` in `S`, its degree is bounded, see
`rank_le_rankOfDiscrBdd`, and also its Minkowski bound, see `minkowskiBound_lt_boundOfDiscBdd`.
Thus it follows from `mixedEmbedding.exists_primitive_element_lt_of_isComplex` and
`mixedEmbedding.exists_primitive_element_lt_of_isReal` that there exists an algebraic integer
`x` of `K` such that `K = ℚ(x)` and the conjugates of `x` are all bounded by some quantity
depending only on `N`.

Since the primitive element `x` is constructed differently depending on whether `K` has a infinite
real place or not, the theorem is proved in two parts.
-/

namespace hermiteTheorem

open Polynomial

open scoped IntermediateField

variable (A : Type*) [Field A] [CharZero A]

theorem finite_of_finite_generating_set {p : IntermediateField ℚ A → Prop}
    (S : Set {F : IntermediateField ℚ A // p F}) {T : Set A}
    (hT : T.Finite) (h : ∀ F ∈ S, ∃ x ∈ T, F = ℚ⟮x⟯) :
    S.Finite := by
  rw [← Set.finite_coe_iff] at hT
  refine Set.finite_coe_iff.mp <| Finite.of_injective
    (fun ⟨F, hF⟩ ↦ (⟨(h F hF).choose, (h F hF).choose_spec.1⟩ : T)) (fun _ _ h_eq ↦ ?_)
  rw [Subtype.ext_iff_val, Subtype.ext_iff_val]
  convert congr_arg (ℚ⟮·⟯) (Subtype.mk_eq_mk.mp h_eq)
  all_goals exact (h _ (Subtype.mem _)).choose_spec.2

variable (N : ℕ)

/-- An upper bound on the degree of a number field `K` with `|discr K| ≤ N`,
see `rank_le_rankOfDiscrBdd`. -/
noncomputable abbrev rankOfDiscrBdd : ℕ :=
  max 1 (Nat.floor ((Real.log ((9 / 4 : ℝ) * N) / Real.log (3 * π / 4))))

/-- An upper bound on the Minkowski bound of a number field `K` with `|discr K| ≤ N`;
see `minkowskiBound_lt_boundOfDiscBdd`. -/
noncomputable abbrev boundOfDiscBdd : ℝ≥0 := sqrt N * (2 : ℝ≥0) ^ rankOfDiscrBdd N + 1

variable {N} (hK : |discr K| ≤ N)

include hK in
/-- If `|discr K| ≤ N` then the degree of `K` is at most `rankOfDiscrBdd`. -/
theorem rank_le_rankOfDiscrBdd :
    finrank ℚ K ≤ rankOfDiscrBdd N := by
  have h_nz : N ≠ 0 := by
    refine fun h ↦ discr_ne_zero K ?_
    rwa [h, Nat.cast_zero, abs_nonpos_iff] at hK
  have h₂ : 1 < 3 * π / 4 := by
    rw [_root_.lt_div_iff (by positivity), ← _root_.div_lt_iff' (by positivity), one_mul]
    linarith [Real.pi_gt_three]
  obtain h | h := lt_or_le 1 (finrank ℚ K)
  · apply le_max_of_le_right
    rw [Nat.le_floor_iff]
    · have h := le_trans (abs_discr_ge h) (Int.cast_le.mpr hK)
      contrapose! h
      rw [← Real.rpow_natCast]
      rw [Real.log_div_log] at h
      refine lt_of_le_of_lt ?_ (mul_lt_mul_of_pos_left
        (Real.rpow_lt_rpow_of_exponent_lt h₂ h) (by positivity : (0 : ℝ) < 4 / 9))
      rw [Real.rpow_logb (lt_trans zero_lt_one h₂) (ne_of_gt h₂) (by positivity), ← mul_assoc,
            ← inv_div, inv_mul_cancel₀ (by norm_num), one_mul, Int.cast_natCast]
    · refine div_nonneg (Real.log_nonneg ?_) (Real.log_nonneg (le_of_lt h₂))
      rw [mul_comm, ← mul_div_assoc, _root_.le_div_iff₀ (by positivity), one_mul,
        ← _root_.div_le_iff₀ (by positivity)]
      exact le_trans (by norm_num) (Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr h_nz))
  · exact le_max_of_le_left h

include hK in
/-- If `|discr K| ≤ N` then the Minkowski bound of `K` is less than `boundOfDiscrBdd`. -/
theorem minkowskiBound_lt_boundOfDiscBdd : minkowskiBound K ↑1 < boundOfDiscBdd N := by
  have : boundOfDiscBdd N - 1 < boundOfDiscBdd N := by
    simp_rw [boundOfDiscBdd, add_tsub_cancel_right, lt_add_iff_pos_right, zero_lt_one]
  refine lt_of_le_of_lt ?_ (coe_lt_coe.mpr this)
  rw [minkowskiBound, volume_fundamentalDomain_fractionalIdealLatticeBasis, boundOfDiscBdd,
    add_tsub_cancel_right, Units.val_one, FractionalIdeal.absNorm_one, Rat.cast_one,
    ENNReal.ofReal_one, one_mul, mixedEmbedding.finrank, volume_fundamentalDomain_latticeBasis,
    coe_mul, ENNReal.coe_pow, coe_ofNat, show sqrt N = (1 : ℝ≥0∞) * sqrt N by rw [one_mul]]
  gcongr
  · exact pow_le_one _ (by positivity) (by norm_num)
  · rwa [sqrt_le_sqrt, ← NNReal.coe_le_coe, coe_nnnorm, Int.norm_eq_abs, ← Int.cast_abs,
      NNReal.coe_natCast, ← Int.cast_natCast, Int.cast_le]
  · exact one_le_two
  · exact rank_le_rankOfDiscrBdd hK

include hK in
theorem natDegree_le_rankOfDiscrBdd (a : 𝓞 K) (h : ℚ⟮(a : K)⟯ = ⊤) :
    natDegree (minpoly ℤ (a : K)) ≤ rankOfDiscrBdd N := by
  rw [Field.primitive_element_iff_minpoly_natDegree_eq,
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ a.isIntegral_coe,
    (minpoly.monic a.isIntegral_coe).natDegree_map] at h
  exact h.symm ▸ rank_le_rankOfDiscrBdd hK

variable (N)

theorem finite_of_discr_bdd_of_isReal :
    {K : { F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
      haveI :  NumberField K := @NumberField.mk _ _ inferInstance K.prop
      {w : InfinitePlace K | IsReal w}.Nonempty ∧ |discr K| ≤ N }.Finite := by
  -- The bound on the degree of the generating polynomials
  let D := rankOfDiscrBdd N
  -- The bound on the Minkowski bound
  let B := boundOfDiscBdd N
  -- The bound on the coefficients of the generating polynomials
  let C := Nat.ceil ((max B 1) ^ D *  Nat.choose D (D / 2))
  refine finite_of_finite_generating_set A _ (bUnion_roots_finite (algebraMap ℤ A) D
      (Set.finite_Icc (-C : ℤ) C)) (fun ⟨K, hK₀⟩ ⟨hK₁, hK₂⟩ ↦ ?_)
  -- We now need to prove that each field is generated by an element of the union of the rootset
  simp_rw [Set.mem_iUnion]
  haveI : NumberField K := @NumberField.mk _ _ inferInstance hK₀
  obtain ⟨w₀, hw₀⟩ := hK₁
  suffices minkowskiBound K ↑1 < (convexBodyLTFactor K) * B by
    obtain ⟨x, hx₁, hx₂⟩ := exists_primitive_element_lt_of_isReal K hw₀ this
    have hx := x.isIntegral_coe
    refine ⟨x, ⟨⟨minpoly ℤ (x : K), ⟨?_, fun i ↦ ?_⟩, ?_⟩, ?_⟩⟩
    · exact natDegree_le_rankOfDiscrBdd hK₂ x hx₁
    · rw [Set.mem_Icc, ← abs_le, ← @Int.cast_le ℝ]
      refine (Eq.trans_le ?_ <| Embeddings.coeff_bdd_of_norm_le
          ((le_iff_le (x : K) _).mp (fun w ↦ le_of_lt (hx₂ w))) i).trans ?_
      · rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hx, coeff_map, eq_intCast,
          Int.norm_cast_rat, Int.norm_eq_abs, Int.cast_abs]
      · refine le_trans ?_ (Nat.le_ceil _)
        rw [show max ↑(max (B : ℝ≥0) 1) (1 : ℝ) = max (B : ℝ) 1 by simp, val_eq_coe, NNReal.coe_mul,
          NNReal.coe_pow, NNReal.coe_max, NNReal.coe_one, NNReal.coe_natCast]
        gcongr
        · exact le_max_right _ 1
        · exact rank_le_rankOfDiscrBdd hK₂
        · exact (Nat.choose_le_choose _ (rank_le_rankOfDiscrBdd hK₂)).trans
            (Nat.choose_le_middle _ _)
    · refine mem_rootSet.mpr ⟨minpoly.ne_zero hx, ?_⟩
      exact (aeval_algebraMap_eq_zero_iff _ _ _).mpr (minpoly.aeval ℤ (x : K))
    · rw [← (IntermediateField.lift_injective _).eq_iff, eq_comm] at hx₁
      convert hx₁ <;> simp
  have := one_le_convexBodyLTFactor K
  convert lt_of_le_of_lt (mul_right_mono (coe_le_coe.mpr this))
    (ENNReal.mul_lt_mul_left' (by positivity) coe_ne_top (minkowskiBound_lt_boundOfDiscBdd hK₂))
  simp_rw [ENNReal.coe_one, one_mul]

theorem finite_of_discr_bdd_of_isComplex :
    {K : { F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
      haveI :  NumberField K := @NumberField.mk _ _ inferInstance K.prop
      {w : InfinitePlace K | IsComplex w}.Nonempty ∧ |discr K| ≤ N }.Finite := by
  -- The bound on the degree of the generating polynomials
  let D := rankOfDiscrBdd N
  -- The bound on the Minkowski bound
  let B := boundOfDiscBdd N
  -- The bound on the coefficients of the generating polynomials
  let C := Nat.ceil ((max (sqrt (1 + B ^ 2)) 1) ^ D * Nat.choose D (D / 2))
  refine finite_of_finite_generating_set A _ (bUnion_roots_finite (algebraMap ℤ A) D
      (Set.finite_Icc (-C : ℤ) C)) (fun ⟨K, hK₀⟩ ⟨hK₁, hK₂⟩ ↦ ?_)
  -- We now need to prove that each field is generated by an element of the union of the rootset
  simp_rw [Set.mem_iUnion]
  haveI : NumberField K := @NumberField.mk _ _ inferInstance hK₀
  obtain ⟨w₀, hw₀⟩ := hK₁
  suffices minkowskiBound K ↑1 < (convexBodyLT'Factor K) * boundOfDiscBdd N by
    obtain ⟨x, hx₁, hx₂⟩ := exists_primitive_element_lt_of_isComplex K hw₀ this
    have hx := x.isIntegral_coe
    refine ⟨x, ⟨⟨minpoly ℤ (x : K), ⟨?_, fun i ↦ ?_⟩, ?_⟩, ?_⟩⟩
    · exact natDegree_le_rankOfDiscrBdd hK₂ x hx₁
    · rw [Set.mem_Icc, ← abs_le, ← @Int.cast_le ℝ]
      refine (Eq.trans_le ?_ <| Embeddings.coeff_bdd_of_norm_le
          ((le_iff_le (x : K) _).mp (fun w ↦ le_of_lt (hx₂ w))) i).trans ?_
      · rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hx, coeff_map, eq_intCast,
          Int.norm_cast_rat, Int.norm_eq_abs, Int.cast_abs]
      · refine le_trans ?_ (Nat.le_ceil _)
        rw [val_eq_coe, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_max, NNReal.coe_one,
          Real.coe_sqrt, NNReal.coe_add 1, NNReal.coe_one, NNReal.coe_pow]
        gcongr
        · exact le_max_right _ 1
        · exact rank_le_rankOfDiscrBdd hK₂
        · rw [NNReal.coe_natCast, Nat.cast_le]
          exact (Nat.choose_le_choose _ (rank_le_rankOfDiscrBdd hK₂)).trans
            (Nat.choose_le_middle _ _)
    · refine mem_rootSet.mpr ⟨minpoly.ne_zero hx, ?_⟩
      exact (aeval_algebraMap_eq_zero_iff _ _ _).mpr (minpoly.aeval ℤ (x : K))
    · rw [← (IntermediateField.lift_injective _).eq_iff, eq_comm] at hx₁
      convert hx₁ <;> simp
  have := one_le_convexBodyLT'Factor K
  convert lt_of_le_of_lt (mul_right_mono (coe_le_coe.mpr this))
    (ENNReal.mul_lt_mul_left' (by positivity) coe_ne_top (minkowskiBound_lt_boundOfDiscBdd hK₂))
  simp_rw [ENNReal.coe_one, one_mul]

/-- **Hermite Theorem**. Let `N` be an integer. There are only finitely many number fields
(in some fixed extension of `ℚ`) of discriminant bounded by `N`. -/
theorem _root_.NumberField.finite_of_discr_bdd :
    {K : { F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
      haveI :  NumberField K := @NumberField.mk _ _ inferInstance K.prop
      |discr K| ≤ N }.Finite := by
  refine Set.Finite.subset (Set.Finite.union (finite_of_discr_bdd_of_isReal A N)
    (finite_of_discr_bdd_of_isComplex A N)) ?_
  rintro ⟨K, hK₀⟩ hK₁
  haveI : NumberField K := @NumberField.mk _ _ inferInstance hK₀
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
  by_cases hw₀ : IsReal w₀
  · apply Set.mem_union_left
    exact ⟨⟨w₀, hw₀⟩, hK₁⟩
  · apply Set.mem_union_right
    exact ⟨⟨w₀, not_isReal_iff_isComplex.mp hw₀⟩, hK₁⟩

end hermiteTheorem

end NumberField

namespace Rat

open NumberField

/-- The absolute discriminant of the number field `ℚ` is 1. -/
@[simp]
theorem numberField_discr : discr ℚ = 1 := by
  let b : Basis (Fin 1) ℤ (𝓞 ℚ) :=
    Basis.map (Basis.singleton (Fin 1) ℤ) ringOfIntegersEquiv.toAddEquiv.toIntLinearEquiv.symm
  calc NumberField.discr ℚ
    _ = Algebra.discr ℤ b := by convert (discr_eq_discr ℚ b).symm
    _ = Algebra.trace ℤ (𝓞 ℚ) (b default * b default) := by
      rw [Algebra.discr_def, Matrix.det_unique, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    _ = Algebra.trace ℤ (𝓞 ℚ) 1 := by
      rw [Basis.map_apply, RingEquiv.toAddEquiv_eq_coe, AddEquiv.toIntLinearEquiv_symm,
        AddEquiv.coe_toIntLinearEquiv, Basis.singleton_apply,
        show (AddEquiv.symm ↑ringOfIntegersEquiv) (1 : ℤ) = ringOfIntegersEquiv.symm 1 by rfl,
        map_one, mul_one]
    _ = 1 := by rw [Algebra.trace_eq_matrix_trace b]; norm_num

alias _root_.NumberField.discr_rat := numberField_discr

end Rat

variable {ι ι'} (K) [Field K] [DecidableEq ι] [DecidableEq ι'] [Fintype ι] [Fintype ι']

/-- If `b` and `b'` are `ℚ`-bases of a number field `K` such that
`∀ i j, IsIntegral ℤ (b.toMatrix b' i j)` and `∀ i j, IsIntegral ℤ (b'.toMatrix b i j)` then
`discr ℚ b = discr ℚ b'`. -/
theorem Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral [NumberField K]
    {b : Basis ι ℚ K} {b' : Basis ι' ℚ K} (h : ∀ i j, IsIntegral ℤ (b.toMatrix b' i j))
    (h' : ∀ i j, IsIntegral ℤ (b'.toMatrix b i j)) : discr ℚ b = discr ℚ b' := by
  replace h' : ∀ i j, IsIntegral ℤ (b'.toMatrix (b.reindex (b.indexEquiv b')) i j) := by
    intro i j
    convert h' i ((b.indexEquiv b').symm j)
    simp [Basis.toMatrix_apply]
  classical
  rw [← (b.reindex (b.indexEquiv b')).toMatrix_map_vecMul b', discr_of_matrix_vecMul,
    ← one_mul (discr ℚ b), Basis.coe_reindex, discr_reindex]
  congr
  have hint : IsIntegral ℤ ((b.reindex (b.indexEquiv b')).toMatrix b').det :=
    IsIntegral.det fun i j => h _ _
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hunit : IsUnit r := by
    have : IsIntegral ℤ (b'.toMatrix (b.reindex (b.indexEquiv b'))).det :=
      IsIntegral.det fun i j => h' _ _
    obtain ⟨r', hr'⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
    refine isUnit_iff_exists_inv.2 ⟨r', ?_⟩
    suffices algebraMap ℤ ℚ (r * r') = 1 by
      rw [← RingHom.map_one (algebraMap ℤ ℚ)] at this
      exact (IsFractionRing.injective ℤ ℚ) this
    rw [RingHom.map_mul, hr, hr', ← Matrix.det_mul,
      Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
  rw [← RingHom.map_one (algebraMap ℤ ℚ), ← hr]
  cases' Int.isUnit_iff.1 hunit with hp hm
  · simp [hp]
  · simp [hm]
