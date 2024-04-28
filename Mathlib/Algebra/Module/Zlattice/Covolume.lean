/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Covolume of ℤ-lattices

Let `E` be a finite dimensional real vector space.

Let `L` be a `ℤ`-lattice defined as a discrete `AddSubgroup E` that spans `E` over `ℝ`.

## Main definitions and results

* `Zlattice.covolume`: the covolume of `L` defined as the volume of an arbitrary fundamental
domain of `L`.

* `Zlattice.covolume_eq_measure_fundamentalDomain`: the covolume of `L` does not depend on the
choice of the fundamental domain of `L`.

* `Zlattice.covolume_eq_det`: if `L` is a lattice in `ℝ^n`, then its covolume is the absolute
value of the determinant of any `ℤ`-basis of `L`.

* `Zlattice.covolume.tendsto_card_div_pow`: Let `s` be a bounded measurable set of `ι → ℝ`, then
the number of points in `s ∩ n⁻¹ • L` divided by `n ^ card ι` tends to `volume s / covolume L`
when `n : ℕ` tends to infinity. See also `Zlattice.covolume.tendsto_card_div_pow'` for a version
for `InnerProductSpace ℝ E` and `Zlattice.covolume.tendsto_card_div_pow''` for the general version.

* `Zlattice.covolume.tendsto_card_le_div`: Let `X` be a cone in `ι → ℝ` and let `F : (ι → ℝ) → ℝ`
be a function such that `F (c • x) = c ^ card ι * F x`. Then the number of points `x ∈ X` such that
`F x ≤ c` divided by `c` tends to `volume {x ∈ X | F x ≤ 1} / covolume L` when `c : ℝ` tends to
infinity. See also `Zlattice.covolume.tendsto_card_le_div'` for a version for
`InnerProductSpace ℝ E` and `Zlattice.covolume.tendsto_card_le_div''` for the general version.

-/

noncomputable section

namespace Zlattice

open Submodule MeasureTheory FiniteDimensional Module Bornology

section General

variable (K : Type*) [NormedLinearOrderedField K] [HasSolidNorm K] [FloorRing K]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E]
variable [ProperSpace E] [MeasurableSpace E]
variable (L : AddSubgroup E) [DiscreteTopology L] [IsZlattice K L]

/-- The covolume of a `ℤ`-lattice is the volume of some fundamental domain; see
`Zlattice.covolume_eq_volume` for the proof that the volume does not depend on the choice of
the fundamental domain. -/
def covolume (μ : Measure E := by volume_tac) : ℝ := (addCovolume L E μ).toReal

end General

section Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable (L : AddSubgroup E) [DiscreteTopology L] [IsZlattice ℝ L]
variable (μ : Measure E := by volume_tac) [Measure.IsAddHaarMeasure μ]

theorem covolume_eq_measure_fundamentalDomain {F : Set E} (h : IsAddFundamentalDomain L F μ) :
    covolume L μ = (μ F).toReal := congr_arg ENNReal.toReal (h.covolume_eq_volume μ)

theorem covolume_ne_zero : covolume L μ ≠ 0 := by
  rw [covolume_eq_measure_fundamentalDomain L μ (isAddFundamentalDomain (Free.chooseBasis ℤ L) μ),
    ENNReal.toReal_ne_zero]
  refine ⟨Zspan.measure_fundamentalDomain_ne_zero _, ne_of_lt ?_⟩
  exact IsBounded.measure_lt_top (Zspan.fundamentalDomain_isBounded _)

theorem covolume_pos : 0 < covolume L μ :=
  lt_of_le_of_ne ENNReal.toReal_nonneg (covolume_ne_zero L μ).symm

theorem covolume_eq_det_mul_measure {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L)
    (b₀ : Basis ι ℝ E) :
    covolume L μ = |b₀.det ((↑) ∘ b)| * (μ (Zspan.fundamentalDomain b₀)).toReal := by
  rw [covolume_eq_measure_fundamentalDomain L μ (isAddFundamentalDomain b μ),
    Zspan.measure_fundamentalDomain _ _ b₀, measure_congr
    (Zspan.fundamentalDomain_ae_parallelepiped b₀ μ), ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (by positivity)]
  congr
  ext
  exact b.ofZlatticeBasis_apply ℝ L _

theorem covolume_eq_det {ι : Type*} [Fintype ι] [DecidableEq ι] (L : AddSubgroup (ι → ℝ))
    [DiscreteTopology L] [IsZlattice ℝ L] (b : Basis ι ℤ L) :
    covolume L = |(Matrix.of ((↑) ∘ b)).det| := by
  rw [covolume_eq_measure_fundamentalDomain L volume (isAddFundamentalDomain b volume),
    Zspan.volume_fundamentalDomain, ENNReal.toReal_ofReal (by positivity)]
  congr
  ext1
  exact b.ofZlatticeBasis_apply ℝ L _

theorem volume_image_eq_volume_div_covolume {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {s : Set E} (hs : MeasurableSet s) (L : AddSubgroup E) [DiscreteTopology L] [IsZlattice ℝ L]
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) :
    volume ((b.ofZlatticeBasis ℝ).equivFun '' s) = volume s / ENNReal.ofReal (covolume L) := by
  classical
  let e : Fin (finrank ℝ E) ≃ ι :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, finrank_eq_card_basis (b.ofZlatticeBasis ℝ)])
  have h₁ : MeasurableSet ((b.ofZlatticeBasis ℝ).equivFun '' s) :=
    (b.ofZlatticeBasis ℝ).equivFunL.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hs
  have h₂ : (Subtype.val ∘ b) = (b.ofZlatticeBasis ℝ) := by ext; simp
  -- This is useful for positivity later on
  have h₃ : ((stdOrthonormalBasis ℝ E).toBasis.reindex e).det (Subtype.val ∘ b) ≠ 0 :=
    isUnit_iff_ne_zero.mp (h₂ ▸ Basis.isUnit_det _ _)
  have h₄ : (b.ofZlatticeBasis ℝ).equivFun ≪≫ₗ (WithLp.linearEquiv 2 _  _).symm ≪≫ₗ
      ((stdOrthonormalBasis ℝ E).reindex e).repr.toLinearEquiv.symm =
      (b.ofZlatticeBasis ℝ).equiv ((stdOrthonormalBasis ℝ E).reindex e).toBasis (Equiv.refl ι) := by
    refine (b.ofZlatticeBasis ℝ).ext' fun _ ↦ ?_
    simp_rw [LinearEquiv.trans_apply, Basis.equivFun_apply, Basis.repr_self,
      Finsupp.single_eq_pi_single, WithLp.linearEquiv_symm_apply, WithLp.equiv_symm_single _ (1:ℝ),
      LinearIsometryEquiv.toLinearEquiv_symm, LinearIsometryEquiv.coe_toLinearEquiv,
      OrthonormalBasis.repr_symm_single, Basis.equiv_apply, Equiv.refl_apply,
      OrthonormalBasis.reindex_toBasis, OrthonormalBasis.coe_reindex, Basis.coe_reindex,
      OrthonormalBasis.coe_toBasis]
  rw [← (EuclideanSpace.volume_preserving_measurableEquiv _).measure_preimage h₁]
  rw [← ((stdOrthonormalBasis ℝ E).reindex e).measurePreserving_repr.measure_preimage
    ((MeasurableEquiv.measurableSet_preimage _).mpr h₁)]
  simp_rw [EuclideanSpace.coe_measurableEquiv, ← WithLp.linearEquiv_apply 2 ℝ,
    ← LinearIsometryEquiv.coe_toLinearEquiv, ← LinearEquiv.image_symm_eq_preimage,
    ← Set.image_comp, ← LinearEquiv.coe_coe, ← LinearMap.coe_comp, LinearEquiv.comp_coe]
  rw [h₄, LinearEquiv.coe_coe, LinearEquiv.image_eq_preimage,
    Measure.addHaar_preimage_linearEquiv, LinearEquiv.symm_symm, ← Basis.det_basis, ← Basis.det_inv,
    Units.val_inv_eq_inv_val, IsUnit.unit_spec, covolume_eq_det_mul_measure L volume b
    ((stdOrthonormalBasis ℝ E).reindex e).toBasis, OrthonormalBasis.reindex_toBasis,
    Zspan.fundamentalDomain_reindex, measure_congr (Zspan.fundamentalDomain_ae_parallelepiped _
    volume), OrthonormalBasis.coe_toBasis, OrthonormalBasis.volume_parallelepiped,
    ENNReal.one_toReal, mul_one, mul_comm, div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos
    (by positivity), abs_inv, ← h₂]
  rfl

end Basic

namespace covolume

section General

open Filter Fintype Pointwise Topology BoxIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable {L : AddSubgroup E} [DiscreteTopology L] [IsZlattice ℝ L]
variable {ι : Type*} [Fintype ι] (b : Basis ι ℤ L)

theorem tendsto_card_div_pow'' {s : Set E} (hs₁ : IsBounded s) (hs₂ : MeasurableSet s) :
    Tendsto (fun n : ℕ ↦ (Nat.card (s ∩ (n : ℝ)⁻¹ • L : Set E) : ℝ) / n ^ card ι)
      atTop (𝓝 (volume ((b.ofZlatticeBasis ℝ).equivFun '' s)).toReal) := by
  refine Tendsto.congr' ?_
    (unitPartition.tendsto_card_div_pow' ((b.ofZlatticeBasis ℝ).equivFun '' s) ?_ ?_)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    congr
    refine Nat.card_congr <| ((b.ofZlatticeBasis ℝ).equivFun.toEquiv.subtypeEquiv fun x ↦ ?_).symm
    simp_rw [Set.mem_inter_iff, ← b.ofZlatticeBasis_span ℝ, coe_toAddSubgroup,
      LinearEquiv.coe_toEquiv, Basis.equivFun_apply, Set.mem_image, DFunLike.coe_fn_eq,
      EmbeddingLike.apply_eq_iff_eq, exists_eq_right, and_congr_right_iff,
      Set.mem_inv_smul_set_iff₀ (by aesop : (n:ℝ) ≠ 0), ← Finsupp.coe_smul, ← LinearEquiv.map_smul,
      SetLike.mem_coe, Basis.mem_span_iff_repr_mem, Pi.basisFun_repr, implies_true]
  · rw [← NormedSpace.isVonNBounded_iff ℝ] at hs₁ ⊢
    exact Bornology.IsVonNBounded.image hs₁ ((b.ofZlatticeBasis ℝ).equivFunL : E →L[ℝ] ι → ℝ)
  · exact (b.ofZlatticeBasis ℝ).equivFunL.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hs₂

variable {X : Set E} (hX : ∀ ⦃x⦄ ⦃r : ℝ⦄, x ∈ X → 0 ≤ r → r • x ∈ X)
variable {F : E → ℝ} (hF₁ : ∀ x ⦃r : ℝ⦄, 0 ≤ r →  F (r • x) = r ^ card ι * (F x))
  (hF₂ : IsBounded {x ∈ X | F x ≤ 1}) (hF₃ : MeasurableSet {x ∈ X | F x ≤ 1})

private theorem tendsto_card_le_div''_aux {c : ℝ} (hc : 0 < c) :
    c • {x ∈ X | F x ≤ 1} = {x ∈ X | F x ≤ c ^ card ι} := by
  obtain ⟨hc₁, hc₂⟩ := lt_iff_le_and_ne.mp hc
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
    refine ⟨hX hy₁ hc₁, ?_⟩
    rw [hF₁ _ hc₁]
    exact mul_le_of_le_one_right (pow_nonneg hc₁ _) hy₂
  · refine fun ⟨hx₁, hx₂⟩ ↦
      ⟨c⁻¹ • x, ⟨hX hx₁ (inv_nonneg_of_nonneg hc₁), ?_⟩, smul_inv_smul₀ (hc₂.symm) _⟩
    rw [hF₁ _ (inv_nonneg_of_nonneg hc₁), inv_pow]
    exact inv_mul_le_one_of_le hx₂ (pow_nonneg hc₁ _)

theorem tendsto_card_le_div'' [Nonempty ι] :
    Tendsto (fun c : ℝ ↦
      Nat.card ({x ∈ X | F x ≤ c} ∩ L : Set E) / (c : ℝ))
        atTop (𝓝 (volume ((b.ofZlatticeBasis ℝ).equivFun '' {x ∈ X | F x ≤ 1})).toReal) := by
  have h : (card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr card_ne_zero
  refine Tendsto.congr' ?_ <| (unitPartition.tendsto_card_div_pow
      ((b.ofZlatticeBasis ℝ).equivFun '' {x ∈ X | F x ≤ 1}) ?_ ?_ fun x y hx hy ↦ ?_).comp
        (tendsto_rpow_atTop <| inv_pos.mpr
          (Nat.cast_pos.mpr card_pos) : Tendsto (fun x ↦ x ^ (card ι : ℝ)⁻¹) atTop atTop)
  · filter_upwards [eventually_gt_atTop 0] with c hc
    obtain ⟨hc₁, hc₂⟩ := lt_iff_le_and_ne.mp hc
    rw [Function.comp_apply, ← Real.rpow_natCast, Real.rpow_inv_rpow hc₁ h, eq_comm]
    congr
    refine Nat.card_congr <| Equiv.subtypeEquiv ((b.ofZlatticeBasis ℝ).equivFun.toEquiv.trans
          (Equiv.smulRight (a := c ^ (- (card ι : ℝ)⁻¹)) (by aesop))) fun _ ↦ ?_
    rw [Set.mem_inter_iff, Set.mem_inter_iff, Equiv.trans_apply, LinearEquiv.coe_toEquiv,
      Equiv.smulRight_apply, Real.rpow_neg hc₁, Set.smul_mem_smul_set_iff₀ (by aesop),
      ← Set.mem_smul_set_iff_inv_smul_mem₀ (by aesop), ← image_smul_set,
      tendsto_card_le_div''_aux hX hF₁ (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hc₁,
      inv_mul_cancel h, Real.rpow_one]
    simp_rw [SetLike.mem_coe, Set.mem_image, EmbeddingLike.apply_eq_iff_eq, exists_eq_right,
      and_congr_right_iff, ← b.ofZlatticeBasis_span ℝ, mem_toAddSubgroup,
      Basis.mem_span_iff_repr_mem, Pi.basisFun_repr, Basis.equivFun_apply, implies_true]
  · rw [← NormedSpace.isVonNBounded_iff ℝ] at hF₂ ⊢
    exact Bornology.IsVonNBounded.image hF₂ ((b.ofZlatticeBasis ℝ).equivFunL : E →L[ℝ] ι → ℝ)
  · exact (b.ofZlatticeBasis ℝ).equivFunL.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hF₃
  · simp_rw [← image_smul_set]
    apply Set.image_mono
    rw [tendsto_card_le_div''_aux hX hF₁ hx,
      tendsto_card_le_div''_aux hX hF₁ (lt_of_lt_of_le hx hy)]
    exact fun a ⟨ha₁, ha₂⟩ ↦ ⟨ha₁, le_trans ha₂ <| pow_le_pow_left (le_of_lt hx) hy _⟩

end General

section Pi

open Filter Fintype Pointwise Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (L : AddSubgroup (ι → ℝ)) [DiscreteTopology L] [IsZlattice ℝ L]

theorem tendsto_card_div_pow (b : Basis ι ℤ L) {s : Set (ι → ℝ)} (hs₁ : IsBounded s)
    (hs₂ : MeasurableSet s) :
    Tendsto (fun n : ℕ ↦ (Nat.card (s ∩ (n : ℝ)⁻¹ • L : Set (ι → ℝ)) : ℝ) / n ^ card ι)
      atTop (𝓝 ((volume s).toReal / covolume L)) := by
  convert tendsto_card_div_pow'' b hs₁ hs₂
  rw [LinearEquiv.image_eq_preimage, Measure.addHaar_preimage_linearEquiv, LinearEquiv.symm_symm,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), covolume_eq_det_mul_measure L
    volume b (Pi.basisFun ℝ ι), div_eq_mul_inv, Zspan.fundamentalDomain_pi_basisFun, volume_pi_pi,
    Real.volume_Ico, sub_zero, ENNReal.ofReal_one, Finset.prod_const_one, ENNReal.one_toReal,
    mul_one, show (((↑) : L → _) ∘ ⇑b) = (b.ofZlatticeBasis ℝ) by ext; simp, ← Basis.det_inv,
    Units.val_inv_eq_inv_val, IsUnit.unit_spec, abs_inv, inv_inv, mul_comm, Basis.det_basis]
  rfl

variable {X : Set (ι → ℝ)} (hX : ∀ ⦃x⦄ ⦃r : ℝ⦄, x ∈ X → 0 ≤ r → r • x ∈ X)
variable {F : (ι → ℝ) → ℝ} (hF₁ : ∀ x ⦃r : ℝ⦄, 0 ≤ r →  F (r • x) = r ^ card ι * (F x))
  (hF₂ : IsBounded {x ∈ X | F x ≤ 1}) (hF₃ : MeasurableSet {x ∈ X | F x ≤ 1})

theorem tendsto_card_le_div [Nonempty ι]:
    Tendsto (fun c : ℝ ↦
      Nat.card ({x ∈ X | F x ≤ c} ∩ L : Set (ι → ℝ)) / (c : ℝ))
        atTop (𝓝 ((volume {x ∈ X | F x ≤ 1}).toReal / covolume L)) := by
  let e : Free.ChooseBasisIndex ℤ ↥L ≃ ι := by
    refine Fintype.equivOfCardEq ?_
    rw [← finrank_eq_card_chooseBasisIndex, Zlattice.rank ℝ, finrank_fintype_fun_eq_card]
  let b := (Module.Free.chooseBasis ℤ L).reindex e
  convert tendsto_card_le_div'' b hX hF₁ hF₂ hF₃
  rw [LinearEquiv.image_eq_preimage, Measure.addHaar_preimage_linearEquiv, LinearEquiv.symm_symm,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), covolume_eq_det_mul_measure L
    volume b (Pi.basisFun ℝ ι), div_eq_mul_inv, Zspan.fundamentalDomain_pi_basisFun, volume_pi_pi,
    Real.volume_Ico, sub_zero, ENNReal.ofReal_one, Finset.prod_const_one, ENNReal.one_toReal,
    mul_one, show (((↑) : L → _) ∘ ⇑b) = (b.ofZlatticeBasis ℝ) by ext; simp, ← Basis.det_inv,
    Units.val_inv_eq_inv_val, IsUnit.unit_spec, abs_inv, inv_inv, mul_comm, Basis.det_basis]
  rfl

end Pi

section InnerProductSpace

open Filter Pointwise Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (L : AddSubgroup E) [DiscreteTopology L] [IsZlattice ℝ L]

theorem tendsto_card_div_pow' {s : Set E} (hs₁ : IsBounded s) (hs₂ : MeasurableSet s) :
    Tendsto (fun n : ℕ ↦ (Nat.card (s ∩ (n : ℝ)⁻¹ • L : Set E) : ℝ) / n ^ finrank ℝ E)
      atTop (𝓝 ((volume s).toReal / covolume L)) := by
  let b := Module.Free.chooseBasis ℤ L
  convert tendsto_card_div_pow'' b hs₁ hs₂
  · rw [← finrank_eq_card_chooseBasisIndex, Zlattice.rank ℝ L]
  · rw [volume_image_eq_volume_div_covolume hs₂, ENNReal.toReal_div, ENNReal.toReal_ofReal]
    exact le_of_lt (covolume_pos L)

variable {X : Set E} (hX : ∀ ⦃x⦄ ⦃r : ℝ⦄, x ∈ X → 0 ≤ r → r • x ∈ X)
variable {F : E → ℝ} (hF₁ : ∀ x ⦃r : ℝ⦄, 0 ≤ r →  F (r • x) = r ^ finrank ℝ E * (F x))
  (hF₂ : IsBounded {x ∈ X | F x ≤ 1}) (hF₃ : MeasurableSet {x ∈ X | F x ≤ 1})

theorem tendsto_card_le_div' [Nontrivial E]:
    Tendsto (fun c : ℝ ↦
      Nat.card ({x ∈ X | F x ≤ c} ∩ L : Set E) / (c : ℝ))
        atTop (𝓝 ((volume {x ∈ X | F x ≤ 1}).toReal / covolume L)) := by
  let b := Module.Free.chooseBasis ℤ L
  convert tendsto_card_le_div'' b hX ?_ hF₂ hF₃
  · rw [volume_image_eq_volume_div_covolume hF₃, ENNReal.toReal_div, ENNReal.toReal_ofReal]
    exact le_of_lt (covolume_pos L)
  · rwa [← finrank_eq_card_chooseBasisIndex, Zlattice.rank ℝ L]
  · have : Nontrivial L := nontrivial_of_finrank_pos <| (Zlattice.rank ℝ L).symm ▸ finrank_pos
    infer_instance

end InnerProductSpace

end covolume

end Zlattice
