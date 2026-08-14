/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.Analysis.Normed.Lp.ProdLp

/-! # Unitization equipped with the $L^1$ norm

In another file, the `Unitization 𝕜 A` of a non-unital normed `𝕜`-algebra `A` is equipped with the
norm inherited as the pullback via a map (closely related to) the left-regular representation of the
algebra on itself (see `Unitization.instNormedRing`).

However, this construction is only valid (and an isometry) when `A` is a `RegularNormedAlgebra`.
Sometimes it is useful to consider the unitization of a non-unital algebra with the $L^1$ norm
instead. This file provides that norm on the type synonym `WithLp 1 (Unitization 𝕜 A)`, along
with the algebra isomorphism between `Unitization 𝕜 A` and `WithLp 1 (Unitization 𝕜 A)`.
Note that `TrivSqZeroExt` is also equipped with the $L^1$ norm in the analogous way, but it is
registered as an instance without the type synonym.

One application of this is a straightforward proof that the quasispectrum of an element in a
non-unital Banach algebra is compact, which can be established by passing to the unitization.
-/

@[expose] public section

variable (𝕜 A : Type*) [NormedField 𝕜] [NonUnitalNormedRing A]
variable [NormedSpace 𝕜 A]

namespace WithLp

open Unitization

/-- The natural map between `Unitization 𝕜 A` and `𝕜 × A`, transferred to their `WithLp 1`
synonyms. -/
noncomputable def unitization_addEquiv_prod : WithLp 1 (Unitization 𝕜 A) ≃+ WithLp 1 (𝕜 × A) :=
  (WithLp.linearEquiv 1 𝕜 (Unitization 𝕜 A)).toAddEquiv.trans <|
    (addEquiv 𝕜 A).trans (WithLp.linearEquiv 1 𝕜 (𝕜 × A)).symm.toAddEquiv

noncomputable instance instUnitizationNormedAddCommGroup :
    NormedAddCommGroup (WithLp 1 (Unitization 𝕜 A)) :=
  NormedAddCommGroup.induced (WithLp 1 (Unitization 𝕜 A)) (WithLp 1 (𝕜 × A))
    (unitization_addEquiv_prod 𝕜 A) (AddEquiv.injective _)

/-- Bundle `WithLp.unitization_addEquiv_prod` as a `UniformEquiv`. -/
noncomputable def uniformEquiv_unitization_addEquiv_prod :
    WithLp 1 (Unitization 𝕜 A) ≃ᵤ WithLp 1 (𝕜 × A) :=
  { unitization_addEquiv_prod 𝕜 A with
    uniformContinuous_invFun := uniformContinuous_comap' uniformContinuous_id
    uniformContinuous_toFun := uniformContinuous_iff_le_comap.mpr le_rfl }

instance instCompleteSpace [CompleteSpace 𝕜] [CompleteSpace A] :
    CompleteSpace (WithLp 1 (Unitization 𝕜 A)) :=
  completeSpace_congr (uniformEquiv_unitization_addEquiv_prod 𝕜 A).isUniformEmbedding |>.mpr
    inferInstance

variable {𝕜 A}

open ENNReal in
lemma unitization_norm_def (x : WithLp 1 (Unitization 𝕜 A)) :
    ‖x‖ = ‖(ofLp x).fst‖ + ‖(ofLp x).snd‖ := calc
  ‖x‖ = (‖(ofLp x).fst‖ ^ (1 : ℝ≥0∞).toReal +
      ‖(ofLp x).snd‖ ^ (1 : ℝ≥0∞).toReal) ^ (1 / (1 : ℝ≥0∞).toReal) :=
    prod_norm_eq_add (by simp : 0 < (1 : ℝ≥0∞).toReal) _
  _ = ‖(ofLp x).fst‖ + ‖(ofLp x).snd‖ := by simp

lemma unitization_nnnorm_def (x : WithLp 1 (Unitization 𝕜 A)) :
    ‖x‖₊ = ‖(ofLp x).fst‖₊ + ‖(ofLp x).snd‖₊ :=
  Subtype.ext <| unitization_norm_def x

lemma unitization_norm_inr (x : A) : ‖toLp 1 (x : Unitization 𝕜 A)‖ = ‖x‖ := by
  simp [unitization_norm_def]

lemma unitization_nnnorm_inr (x : A) : ‖toLp 1 (x : Unitization 𝕜 A)‖₊ = ‖x‖₊ := by
  simp [unitization_nnnorm_def]

lemma unitization_isometry_inr : Isometry fun x : A ↦ toLp 1 (x : Unitization 𝕜 A) :=
  AddMonoidHomClass.isometry_of_norm
    ((WithLp.linearEquiv 1 𝕜 (Unitization 𝕜 A)).symm.comp <| Unitization.inrHom 𝕜 𝕜 A)
    unitization_norm_inr

variable [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

instance instUnitizationRing : Ring (WithLp 1 (Unitization 𝕜 A)) :=
  (WithLp.equiv 1 (Unitization 𝕜 A)).ring

@[simp]
lemma unitization_mul (x y : WithLp 1 (Unitization 𝕜 A)) : ofLp (x * y) = ofLp x * ofLp y := rfl

instance {R : Type*} [CommSemiring R] [Algebra R 𝕜] [DistribMulAction R A] [IsScalarTower R 𝕜 A] :
    Algebra R (WithLp 1 (Unitization 𝕜 A)) :=
  (WithLp.equiv 1 (Unitization 𝕜 A)).algebra R

@[simp]
lemma unitization_ofLp_one : ofLp (1 : WithLp 1 (Unitization 𝕜 A)) = 1 := rfl

@[simp]
lemma unitization_toLp_one : toLp 1 (1 : Unitization 𝕜 A) = 1 := rfl

instance : NormOneClass (WithLp 1 (Unitization 𝕜 A)) where
  norm_one := by simp [unitization_norm_def]

@[simp]
lemma unitization_algebraMap (r : 𝕜) :
    ofLp (algebraMap 𝕜 (WithLp 1 (Unitization 𝕜 A)) r) = algebraMap 𝕜 (Unitization 𝕜 A) r := rfl

/-- `equiv` bundled as an algebra isomorphism with `Unitization 𝕜 A`. -/
@[simps!]
def unitizationAlgEquiv (R : Type*) [CommSemiring R] [Algebra R 𝕜] [DistribMulAction R A]
    [IsScalarTower R 𝕜 A] : WithLp 1 (Unitization 𝕜 A) ≃ₐ[R] Unitization 𝕜 A where
  __ := WithLp.linearEquiv _ R _
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

noncomputable instance instUnitizationNormedRing : NormedRing (WithLp 1 (Unitization 𝕜 A)) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le x y := by
    simp_rw [unitization_norm_def, add_mul, mul_add, unitization_mul, fst_mul, snd_mul]
    rw [add_assoc, add_assoc]
    gcongr
    · exact norm_mul_le _ _
    · apply (norm_add_le _ _).trans
      gcongr
      · simp [norm_smul]
      · apply (norm_add_le _ _).trans
        gcongr
        · simp [norm_smul, mul_comm]
        · exact norm_mul_le _ _

noncomputable instance instUnitizationNormedAlgebra :
    NormedAlgebra 𝕜 (WithLp 1 (Unitization 𝕜 A)) where
  norm_smul_le r x := by
    simp_rw [unitization_norm_def, ofLp_smul, fst_smul, snd_smul, norm_smul, mul_add]
    exact le_rfl

open Finset in
variable (𝕜 A) in
/-- This version is for non-unital algebras because currently `HasSummableGeomSeries` takes a
`NormedRing` hypothesis (requiring the algebra to be unital), in part because we have no `Pow ℕ+ G`
for semigroups `G`. When we change the definition of `HasSummableGeomSeries` to allow for unital
algebras, then this can replace the unprimed instance. -/
theorem hasSummableGeometricSeries_unitization'
    (h_summable : ∀ x : A, ‖x‖ < 1 → Summable (fun n ↦ (· * x)^[n] x)) :
    HasSummableGeomSeries (WithLp 1 (Unitization 𝕜 A)) where
  summable_geometric_of_norm_lt_one x h_norm := by
    /- Take `x = (r, a) : Unitization 𝕜 A` with `‖x‖ = ‖r‖ + ‖a‖ < 1`.
    Then `‖r‖ < 1` and `‖b‖ < 1` where `b := (1 - r)⁻¹ • a`. By hypothesis, the geometric series
    associated to `b` is summable. The one associated to `r` is summable because `𝕜` is a normed
    field. -/
    let (eq := hx) (r, a) := (ofLp x).toProd
    have hra_norm : ‖r‖ + ‖a‖ < 1 := by simpa [hx, unitization_norm_def] using h_norm
    have hr_norm : ‖r‖ < 1 := by grind [norm_nonneg]
    have hr1 : r ≠ 1 := by grind [norm_one]
    set b : A := (1 - r)⁻¹ • a with hb
    specialize h_summable b <| calc
      ‖b‖ ≤ (1 - ‖r‖)⁻¹ * ‖a‖ := by
        rw [hb, norm_smul, norm_inv]
        gcongr
        linarith [norm_sub_norm_le 1 r, norm_one (α := 𝕜)]
      _ < (1 - ‖r‖)⁻¹ * (1 - ‖r‖) := by gcongr; linarith
      _ = 1 := inv_mul_cancel₀ <| by positivity
    /- Denote by `s := ∑' n, b^(n+1)` (expressed via iterating `(· * b)`, since `A` need not be
    unital) the sum of the series, which satisfies `s - b * s = b`. -/
    set s : A := ∑' n, (· * b)^[n] b with hs_def
    have hs : s - b * s = b := calc
      s - b * s = s - ∑' n, (· * b)^[n + 1] b := by
        congr
        rw [hs_def, ← h_summable.tsum_mul_left]
        refine tsum_congr fun n ↦ ?_
        induction n with
        | zero => rfl
        | succ n ih => grind [Function.iterate_succ_apply']
      _ = b + ∑' n, (· * b)^[n + 1] b - ∑' n, (· * b)^[n + 1] b :=
        congr($(h_summable.tsum_eq_zero_add) - _)
      _ = b := by simp
    -- `y := (1 - r)⁻¹ • (1 + s)` is the inverse of `1 - x` which simply amounts to a calculation.
    set y := toLp 1 ((1 - r)⁻¹ • (1 + s) : Unitization 𝕜 A) with hL_def
    have hy : (1 - x) * y = 1 := by
      apply ofLp_injective
      have hxeq : ofLp x = inl r + (a : Unitization 𝕜 A) := by
        simpa [hx] using (inl_fst_add_inr_snd_eq (ofLp x)).symm
      rw [unitization_mul, ofLp_sub, unitization_ofLp_one, hxeq, hL_def, ofLp_toLp]
      have : (1 - inl (A := A) r) = algebraMap 𝕜 _ (1 - r) := by simp [algebraMap_eq_inl]
      rw [← sub_sub, this, sub_mul, ← Algebra.smul_def, smul_inv_smul₀ (by grind),
        mul_smul_comm, ← smul_mul_assoc, ← inr_smul, ← hb]
      grind [mul_add, inr_sub, inr_mul]
    /- Since `y` is the inverse of `1 - x`, we conclude `∑ i ∈ range n, x ^ i = y - x ^ n * y`.
    And since `‖x‖ < 1`, the series `∑' i, ‖x ^ i‖` is summable, so it suffices to show that the
    partial sums converge to `y`. But since `x ^ n` tends to `0`, this follows immediately. -/
    have hpartial (n : ℕ) : ∑ i ∈ range n, x ^ i = y - x ^ n * y := by
      simpa [mul_assoc, hy, sub_mul] using congr($(geom_sum_mul_neg x n) * y)
    apply HasSum.summable (a := y)
    have hx_summable : Summable (‖x ^ ·‖) := summable_norm_geometric_of_norm_lt_one h_norm
    rw [hasSum_iff_tendsto_nat_of_summable_norm hx_summable]
    simpa [hpartial] using tendsto_const_nhds (x := y) |>.sub <|
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one h_norm).mul tendsto_const_nhds

instance hasSummableGeometricSeries_unitization (𝕜 A : Type*)
    [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [HasSummableGeomSeries A] :
    HasSummableGeomSeries (WithLp 1 (Unitization 𝕜 A)) :=
  hasSummableGeometricSeries_unitization' 𝕜 A fun x hx ↦ by
    convert! summable_nat_add_iff 1 |>.mpr <| summable_geometric_of_norm_lt_one (K := A) hx with n
    induction n <;> simp [pow_succ', mul_assoc]

end WithLp
