/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Analysis.BoxIntegral.UnitPartition
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Covolume of ℤ-lattices

Let `E` be a finite-dimensional real vector space.

Let `L` be a `ℤ`-lattice `L` defined as a discrete `ℤ`-submodule of `E` that spans `E` over `ℝ`.

## Main definitions and results

* `ZLattice.covolume`: the covolume of `L` defined as the volume of an arbitrary fundamental
  domain of `L`.

* `ZLattice.covolume_eq_measure_fundamentalDomain`: the covolume of `L` does not depend on the
  choice of the fundamental domain of `L`.

* `ZLattice.covolume_eq_det`: if `L` is a lattice in `ℝ^n`, then its covolume is the absolute
  value of the determinant of any `ℤ`-basis of `L`.

* `ZLattice.covolume_div_covolume_eq_relIndex`: Let `L₁` be a sub-`ℤ`-lattice of `L₂`. Then the
  index of `L₁` inside `L₂` is equal to `covolume L₁ / covolume L₂`.

* `ZLattice.covolume.tendsto_card_div_pow`: Let `s` be a bounded measurable set of `ι → ℝ`, then
  the number of points in `s ∩ n⁻¹ • L` divided by `n ^ card ι` tends to `volume s / covolume L`
  when `n : ℕ` tends to infinity.
  See also `ZLattice.covolume.tendsto_card_div_pow'` for a version for `InnerProductSpace ℝ E` and
  `ZLattice.covolume.tendsto_card_div_pow''` for the general version.

* `ZLattice.covolume.tendsto_card_le_div`: Let `X` be a cone in `ι → ℝ` and let `F : (ι → ℝ) → ℝ`
  be a function such that `F (c • x) = c ^ card ι * F x`. Then the number of points `x ∈ X` such
  that `F x ≤ c` divided by `c` tends to `volume {x ∈ X | F x ≤ 1} / covolume L`
  when `c : ℝ` tends to infinity.
  See also `ZLattice.covolume.tendsto_card_le_div'` for a version for `InnerProductSpace ℝ E` and
  `ZLattice.covolume.tendsto_card_le_div''` for the general version.

## Naming convention

Some results are true in the case where the ambient finite-dimensional real vector space is the
pi-space `ι → ℝ` and in the case where it is an `InnerProductSpace`. We use the following
convention: the plain name is for the pi case, for e.g. `volume_image_eq_volume_div_covolume`. For
the same result in the `InnerProductSpace` case, we add a `prime`, for e.g.
`volume_image_eq_volume_div_covolume'`. When the same result exists in the
general case, we had two primes, e.g. `covolume.tendsto_card_div_pow''`.

-/

@[expose] public section

noncomputable section

namespace ZLattice

open Submodule MeasureTheory Module MeasureTheory Module ZSpan

section General

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] (L : Submodule ℤ E)

/-- The covolume of a `ℤ`-lattice is the volume of some fundamental domain; see
`ZLattice.covolume_eq_volume` for the proof that the volume does not depend on the choice of
the fundamental domain. -/
def covolume (μ : Measure E := by volume_tac) : ℝ := (addCovolume L E μ).toReal

end General

section Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
variable (μ : Measure E := by volume_tac) [Measure.IsAddHaarMeasure μ]

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
theorem covolume_eq_measure_fundamentalDomain {F : Set E} (h : IsAddFundamentalDomain L F μ) :
    covolume L μ = μ.real F := by
  have : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddInvariantMeasure L E μ := (inferInstance : VAddInvariantMeasure L.toAddSubgroup E μ)
  exact congr_arg ENNReal.toReal (h.covolume_eq_volume μ)

set_option backward.privateInPublic true in
theorem covolume_ne_zero : covolume L μ ≠ 0 := by
  rw [covolume_eq_measure_fundamentalDomain L μ (isAddFundamentalDomain (Free.chooseBasis ℤ L) μ),
    measureReal_ne_zero_iff (ne_of_lt _)]
  · exact measure_fundamentalDomain_ne_zero _
  · exact Bornology.IsBounded.measure_lt_top (fundamentalDomain_isBounded _)

set_option backward.privateInPublic true in
theorem covolume_pos : 0 < covolume L μ :=
  lt_of_le_of_ne ENNReal.toReal_nonneg (covolume_ne_zero L μ).symm

set_option backward.privateInPublic true in
theorem covolume_comap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (ν : Measure F := by volume_tac) [Measure.IsAddHaarMeasure ν]
    {e : F ≃L[ℝ] E} (he : MeasurePreserving e ν μ) :
    covolume (ZLattice.comap ℝ L e.toLinearMap) ν = covolume L μ := by
  rw [covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain (Free.chooseBasis ℤ L) μ),
    covolume_eq_measure_fundamentalDomain _ _ ((isAddFundamentalDomain
    ((Free.chooseBasis ℤ L).ofZLatticeComap ℝ L e.toLinearEquiv) ν)), ← he.measureReal_preimage
    (fundamentalDomain_measurableSet _).nullMeasurableSet, ← e.image_symm_eq_preimage,
    ← e.symm.coe_toLinearEquiv, map_fundamentalDomain]
  congr!
  ext; simp

set_option backward.privateInPublic true in
theorem covolume_eq_det_mul_measureReal {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L)
    (b₀ : Basis ι ℝ E) :
    covolume L μ = |b₀.det ((↑) ∘ b)| * μ.real (fundamentalDomain b₀) := by
  rw [covolume_eq_measure_fundamentalDomain L μ (isAddFundamentalDomain b μ),
    measureReal_fundamentalDomain _ _ b₀,
    measureReal_congr (fundamentalDomain_ae_parallelepiped b₀ μ)]
  congr
  ext
  exact b.ofZLatticeBasis_apply ℝ L _

theorem covolume_eq_det {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis ι ℤ L) :
    covolume L = |(Matrix.of ((↑) ∘ b)).det| := by
  rw [covolume_eq_measure_fundamentalDomain L volume (isAddFundamentalDomain b volume),
    volume_real_fundamentalDomain]
  congr
  ext1
  exact b.ofZLatticeBasis_apply ℝ L _

theorem covolume_eq_det_inv {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis ι ℤ L) :
    covolume L = |(LinearEquiv.det (b.ofZLatticeBasis ℝ L).equivFun : ℝ)|⁻¹ := by
  classical
  rw [covolume_eq_det L b, ← Pi.basisFun_det_apply, show (((↑) : L → _) ∘ ⇑b) =
    (b.ofZLatticeBasis ℝ) by ext; simp, ← Basis.det_inv, ← abs_inv, Units.val_inv_eq_inv_val,
    IsUnit.unit_spec, ← Basis.det_basis, LinearEquiv.coe_det]
  rfl

/--
Let `L₁` be a sub-`ℤ`-lattice of `L₂`. Then the index of `L₁` inside `L₂` is equal to
`covolume L₁ / covolume L₂`.
-/
theorem covolume_div_covolume_eq_relIndex {ι : Type*} [Fintype ι] (L₁ L₂ : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L₁] [IsZLattice ℝ L₁] [DiscreteTopology L₂] [IsZLattice ℝ L₂] (h : L₁ ≤ L₂) :
    covolume L₁ / covolume L₂ = L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by
  classical
  let b₁ := IsZLattice.basis L₁
  let b₂ := IsZLattice.basis L₂
  rw [AddSubgroup.relIndex_eq_natAbs_det L₁.toAddSubgroup L₂.toAddSubgroup h b₁ b₂,
    Nat.cast_natAbs, Int.cast_abs]
  trans |(b₂.ofZLatticeBasis ℝ).det (b₁.ofZLatticeBasis ℝ)|
  · rw [← Basis.det_mul_det _ (Pi.basisFun ℝ ι) _, abs_mul, Pi.basisFun_det_apply,
      ← Basis.det_inv, Units.val_inv_eq_inv_val, IsUnit.unit_spec, Pi.basisFun_det_apply,
      covolume_eq_det _ b₁, covolume_eq_det _ b₂, mul_comm, abs_inv]
    congr 3 <;> ext <;> simp
  · rw [Basis.det_apply, Basis.det_apply, Int.cast_det]
    congr; ext i j
    rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.toMatrix_apply, Basis.ofZLatticeBasis_apply]
    exact (b₂.ofZLatticeBasis_repr_apply ℝ L₂ ⟨b₁ j, h (coe_mem _)⟩ i)

/--
A more general version of `covolume_div_covolume_eq_relIndex`;
see the `Naming conventions` section in the introduction.
-/
theorem covolume_div_covolume_eq_relIndex' {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L₁ L₂ : Submodule ℤ E) [DiscreteTopology L₁] [IsZLattice ℝ L₁] [DiscreteTopology L₂]
    [IsZLattice ℝ L₂] (h : L₁ ≤ L₂) :
    covolume L₁ / covolume L₂ = L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by
  let f := (EuclideanSpace.equiv _ ℝ).symm.trans
    (stdOrthonormalBasis ℝ E).repr.toContinuousLinearEquiv.symm
  have hf : MeasurePreserving f := (stdOrthonormalBasis ℝ E).measurePreserving_repr_symm.comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).symm
  rw [← covolume_comap L₁ volume volume hf, ← covolume_comap L₂ volume volume hf,
    covolume_div_covolume_eq_relIndex _ _ (fun _ h' ↦ h h'), ZLattice.comap_toAddSubgroup,
    ZLattice.comap_toAddSubgroup, Nat.cast_inj, LinearEquiv.toAddMonoidHom_commutes,
    AddSubgroup.comap_equiv_eq_map_symm', AddSubgroup.comap_equiv_eq_map_symm',
    AddSubgroup.relIndex_map_map_of_injective _ _ f.symm.injective]

theorem volume_image_eq_volume_div_covolume {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis ι ℤ L) {s : Set (ι → ℝ)} :
    volume ((b.ofZLatticeBasis ℝ L).equivFun '' s) = volume s / ENNReal.ofReal (covolume L) := by
  rw [LinearEquiv.image_eq_preimage_symm, Measure.addHaar_preimage_linearEquiv,
    LinearEquiv.symm_symm, covolume_eq_det_inv L b, ENNReal.div_eq_inv_mul,
    ENNReal.ofReal_inv_of_pos (abs_pos.2 (LinearEquiv.det _).ne_zero), inv_inv, LinearEquiv.coe_det]

/-- A more general version of `ZLattice.volume_image_eq_volume_div_covolume`;
see the `Naming conventions` section in the introduction. -/
theorem volume_image_eq_volume_div_covolume' {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] {ι : Type*} [Fintype ι]
    (b : Basis ι ℤ L) {s : Set E} (hs : NullMeasurableSet s) :
    volume ((b.ofZLatticeBasis ℝ).equivFun '' s) = volume s / ENNReal.ofReal (covolume L) := by
  classical
  let e : Fin (finrank ℝ E) ≃ ι :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, finrank_eq_card_basis (b.ofZLatticeBasis ℝ)])
  let f := (EuclideanSpace.equiv ι ℝ).symm.trans
    ((stdOrthonormalBasis ℝ E).reindex e).repr.toContinuousLinearEquiv.symm
  have hf : MeasurePreserving f :=
    ((stdOrthonormalBasis ℝ E).reindex e).measurePreserving_repr_symm.comp
      (PiLp.volume_preserving_toLp ι)
  rw [← hf.measure_preimage hs, ← (covolume_comap L volume volume hf),
    ← volume_image_eq_volume_div_covolume (ZLattice.comap ℝ L f.toLinearMap)
    (b.ofZLatticeComap ℝ L f.toLinearEquiv), Basis.ofZLatticeBasis_comap,
    ← f.image_symm_eq_preimage, ← Set.image_comp]
  simp

end Basic

namespace covolume

section General

open Filter Fintype Pointwise Topology BoxIntegral Bornology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
variable {ι : Type*} [Fintype ι] (b : Basis ι ℤ L)

/-- A version of `ZLattice.covolume.tendsto_card_div_pow` for the general case;
see the `Naming convention` section in the introduction. -/
theorem tendsto_card_div_pow'' [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {s : Set E} (hs₁ : IsBounded s) (hs₂ : MeasurableSet s)
    (hs₃ : volume (frontier ((b.ofZLatticeBasis ℝ).equivFun '' s)) = 0) :
    Tendsto (fun n : ℕ ↦ (Nat.card (s ∩ (n : ℝ)⁻¹ • L : Set E) : ℝ) / n ^ card ι)
      atTop (𝓝 (volume.real ((b.ofZLatticeBasis ℝ).equivFun '' s))) := by
  refine Tendsto.congr' ?_
    (tendsto_card_div_pow_atTop_volume ((b.ofZLatticeBasis ℝ).equivFun '' s) ?_ ?_ hs₃)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    congr
    refine Nat.card_congr <| ((b.ofZLatticeBasis ℝ).equivFun.toEquiv.subtypeEquiv fun x ↦ ?_).symm
    simp_rw [Set.mem_inter_iff, ← b.ofZLatticeBasis_span ℝ, LinearEquiv.coe_toEquiv,
      Basis.equivFun_apply, Set.mem_image, DFunLike.coe_fn_eq, EmbeddingLike.apply_eq_iff_eq,
      exists_eq_right, and_congr_right_iff, Set.mem_inv_smul_set_iff₀
      (mod_cast hn.ne' : (n : ℝ) ≠ 0), ← Finsupp.coe_smul, ← map_smul, SetLike.mem_coe,
      Basis.mem_span_iff_repr_mem, Pi.basisFun_repr, implies_true]
  · rw [← NormedSpace.isVonNBounded_iff ℝ] at hs₁ ⊢
    exact Bornology.IsVonNBounded.image hs₁ ((b.ofZLatticeBasis ℝ).equivFunL : E →L[ℝ] ι → ℝ)
  · exact (b.ofZLatticeBasis ℝ).equivFunL.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hs₂

private theorem tendsto_card_le_div''_aux
    {X : Set E} (hX : ∀ ⦃x⦄ ⦃r : ℝ⦄, x ∈ X → 0 < r → r • x ∈ X)
    {F : E → ℝ} (hF₁ : ∀ x ⦃r : ℝ⦄, 0 ≤ r → F (r • x) = r ^ card ι * (F x)) {c : ℝ} (hc : 0 < c) :
    c • {x ∈ X | F x ≤ 1} = {x ∈ X | F x ≤ c ^ card ι} := by
  ext x
  simp_rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne', Set.mem_setOf_eq, hF₁ _
    (inv_pos_of_pos hc).le, inv_pow, inv_mul_le_iff₀ (pow_pos hc _), mul_one, and_congr_left_iff]
  exact fun _ ↦ ⟨fun h ↦ (smul_inv_smul₀ hc.ne' x) ▸ hX h hc, fun h ↦ hX h (inv_pos_of_pos hc)⟩

/-- A version of `ZLattice.covolume.tendsto_card_le_div` for the general case;
see the `Naming conventions` section in the introduction. -/
theorem tendsto_card_le_div'' [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Nonempty ι] {X : Set E} (hX : ∀ ⦃x⦄ ⦃r : ℝ⦄, x ∈ X → 0 < r → r • x ∈ X)
    {F : E → ℝ} (h₁ : ∀ x ⦃r : ℝ⦄, 0 ≤ r → F (r • x) = r ^ card ι * (F x))
    (h₂ : IsBounded {x ∈ X | F x ≤ 1}) (h₃ : MeasurableSet {x ∈ X | F x ≤ 1})
    (h₄ : volume (frontier ((b.ofZLatticeBasis ℝ L).equivFun '' {x | x ∈ X ∧ F x ≤ 1})) = 0) :
    Tendsto (fun c : ℝ ↦
      Nat.card ({x ∈ X | F x ≤ c} ∩ L : Set E) / (c : ℝ))
        atTop (𝓝 (volume.real ((b.ofZLatticeBasis ℝ).equivFun '' {x ∈ X | F x ≤ 1}))) := by
  refine Tendsto.congr' ?_ <| (tendsto_card_div_pow_atTop_volume'
      ((b.ofZLatticeBasis ℝ).equivFun '' {x ∈ X | F x ≤ 1}) ?_ ?_ h₄ fun x y hx hy ↦ ?_).comp
        (tendsto_rpow_atTop <| inv_pos.mpr
          (Nat.cast_pos.mpr card_pos) : Tendsto (fun x ↦ x ^ (card ι : ℝ)⁻¹) atTop atTop)
  · filter_upwards [eventually_gt_atTop 0] with c hc
    have aux₁ : (card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr card_ne_zero
    have aux₂ : 0 < c ^ (card ι : ℝ)⁻¹ := Real.rpow_pos_of_pos hc _
    have aux₃ : (c ^ (card ι : ℝ)⁻¹)⁻¹ ≠ 0 := inv_ne_zero aux₂.ne'
    have aux₄ : c ^ (-(card ι : ℝ)⁻¹) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
    obtain ⟨hc₁, hc₂⟩ := lt_iff_le_and_ne.mp hc
    rw [Function.comp_apply, ← Real.rpow_natCast, Real.rpow_inv_rpow hc₁ aux₁, eq_comm]
    congr
    refine Nat.card_congr <| Equiv.subtypeEquiv ((b.ofZLatticeBasis ℝ).equivFun.toEquiv.trans
          (Equiv.smulRight aux₄)) fun _ ↦ ?_
    rw [Set.mem_inter_iff, Set.mem_inter_iff, Equiv.trans_apply, LinearEquiv.coe_toEquiv,
      Equiv.smulRight_apply, Real.rpow_neg hc₁, Set.smul_mem_smul_set_iff₀ aux₃,
      ← Set.mem_smul_set_iff_inv_smul_mem₀ aux₂.ne', ← image_smul_set,
      tendsto_card_le_div''_aux hX h₁ aux₂, ← Real.rpow_natCast, ← Real.rpow_mul hc₁,
      inv_mul_cancel₀ aux₁, Real.rpow_one]
    simp_rw [SetLike.mem_coe, Set.mem_image, EmbeddingLike.apply_eq_iff_eq, exists_eq_right,
      and_congr_right_iff, ← b.ofZLatticeBasis_span ℝ, Basis.mem_span_iff_repr_mem,
      Pi.basisFun_repr, Basis.equivFun_apply, implies_true]
  · rw [← NormedSpace.isVonNBounded_iff ℝ] at h₂ ⊢
    exact Bornology.IsVonNBounded.image h₂ ((b.ofZLatticeBasis ℝ).equivFunL : E →L[ℝ] ι → ℝ)
  · exact (b.ofZLatticeBasis ℝ).equivFunL.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr h₃
  · simp_rw [← image_smul_set]
    apply Set.image_mono
    rw [tendsto_card_le_div''_aux hX h₁ hx,
      tendsto_card_le_div''_aux hX h₁ (lt_of_lt_of_le hx hy)]
    exact fun a ⟨ha₁, ha₂⟩ ↦ ⟨ha₁, le_trans ha₂ <| pow_le_pow_left₀ (le_of_lt hx) hy _⟩

end General

section Pi

open Filter Fintype Pointwise Topology Bornology

private theorem frontier_equivFun {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} [Finite ι]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    (b : Basis ι ℝ E) (s : Set E) :
    frontier (b.equivFun '' s) = b.equivFun '' (frontier s) := by
  rw [LinearEquiv.image_eq_preimage_symm, LinearEquiv.image_eq_preimage_symm]
  exact (Homeomorph.preimage_frontier b.equivFunL.toHomeomorph.symm s).symm

variable {ι : Type*} [Fintype ι]
variable (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]

theorem tendsto_card_div_pow (b : Basis ι ℤ L) {s : Set (ι → ℝ)} (hs₁ : IsBounded s)
    (hs₂ : MeasurableSet s) (hs₃ : volume (frontier s) = 0) :
    Tendsto (fun n : ℕ ↦ (Nat.card (s ∩ (n : ℝ)⁻¹ • L : Set (ι → ℝ)) : ℝ) / n ^ card ι)
      atTop (𝓝 (volume.real s / covolume L)) := by
  classical
  convert tendsto_card_div_pow'' b hs₁ hs₂ ?_
  · simp only [measureReal_def]
    rw [volume_image_eq_volume_div_covolume L b, ENNReal.toReal_div,
      ENNReal.toReal_ofReal (covolume_pos L volume).le]
  · rw [frontier_equivFun, volume_image_eq_volume_div_covolume, hs₃, ENNReal.zero_div]

theorem tendsto_card_le_div {X : Set (ι → ℝ)} (hX : ∀ ⦃x⦄ ⦃r : ℝ⦄, x ∈ X → 0 < r → r • x ∈ X)
    {F : (ι → ℝ) → ℝ} (h₁ : ∀ x ⦃r : ℝ⦄, 0 ≤ r → F (r • x) = r ^ card ι * (F x))
    (h₂ : IsBounded {x ∈ X | F x ≤ 1}) (h₃ : MeasurableSet {x ∈ X | F x ≤ 1})
    (h₄ : volume (frontier {x | x ∈ X ∧ F x ≤ 1}) = 0) [Nonempty ι] :
    Tendsto (fun c : ℝ ↦
      Nat.card ({x ∈ X | F x ≤ c} ∩ L : Set (ι → ℝ)) / (c : ℝ))
        atTop (𝓝 (volume.real {x ∈ X | F x ≤ 1} / covolume L)) := by
  classical
  let e : Free.ChooseBasisIndex ℤ ↥L ≃ ι := by
    refine Fintype.equivOfCardEq ?_
    rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ, finrank_fintype_fun_eq_card]
  let b := (Module.Free.chooseBasis ℤ L).reindex e
  convert tendsto_card_le_div'' b hX h₁ h₂ h₃ ?_
  · simp only [measureReal_def]
    rw [volume_image_eq_volume_div_covolume L b, ENNReal.toReal_div,
      ENNReal.toReal_ofReal (covolume_pos L volume).le]
  · rw [frontier_equivFun, volume_image_eq_volume_div_covolume, h₄, ENNReal.zero_div]

end Pi

section InnerProductSpace

open Filter Pointwise Topology Bornology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- A version of `ZLattice.covolume.tendsto_card_div_pow` for the `InnerProductSpace` case;
see the `Naming convention` section in the introduction. -/
theorem tendsto_card_div_pow' {s : Set E} (hs₁ : IsBounded s) (hs₂ : MeasurableSet s)
    (hs₃ : volume (frontier s) = 0) :
    Tendsto (fun n : ℕ ↦ (Nat.card (s ∩ (n : ℝ)⁻¹ • L : Set E) : ℝ) / n ^ finrank ℝ E)
      atTop (𝓝 (volume.real s / covolume L)) := by
  let b := Module.Free.chooseBasis ℤ L
  convert tendsto_card_div_pow'' b hs₁ hs₂ ?_
  · rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]
  · simp only [measureReal_def]
    rw [volume_image_eq_volume_div_covolume' L b hs₂.nullMeasurableSet, ENNReal.toReal_div,
      ENNReal.toReal_ofReal (covolume_pos L volume).le]
  · rw [frontier_equivFun, volume_image_eq_volume_div_covolume', hs₃, ENNReal.zero_div]
    exact NullMeasurableSet.of_null hs₃

/-- A version of `ZLattice.covolume.tendsto_card_le_div` for the `InnerProductSpace` case;
see the `Naming convention` section in the introduction. -/
theorem tendsto_card_le_div' [Nontrivial E] {X : Set E} {F : E → ℝ}
    (hX : ∀ ⦃x⦄ ⦃r : ℝ⦄, x ∈ X → 0 < r → r • x ∈ X)
    (h₁ : ∀ x ⦃r : ℝ⦄, 0 ≤ r → F (r • x) = r ^ finrank ℝ E * (F x))
    (h₂ : IsBounded {x ∈ X | F x ≤ 1}) (h₃ : MeasurableSet {x ∈ X | F x ≤ 1})
    (h₄ : volume (frontier {x ∈ X | F x ≤ 1}) = 0) :
    Tendsto (fun c : ℝ ↦
      Nat.card ({x ∈ X | F x ≤ c} ∩ L : Set E) / (c : ℝ))
        atTop (𝓝 (volume.real {x ∈ X | F x ≤ 1} / covolume L)) := by
  let b := Module.Free.chooseBasis ℤ L
  convert tendsto_card_le_div'' b hX ?_ h₂ h₃ ?_
  · simp only [measureReal_def]
    rw [volume_image_eq_volume_div_covolume' L b h₃.nullMeasurableSet, ENNReal.toReal_div,
      ENNReal.toReal_ofReal (covolume_pos L volume).le]
  · have : Nontrivial L := nontrivial_of_finrank_pos <| (ZLattice.rank ℝ L).symm ▸ finrank_pos
    infer_instance
  · rwa [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]
  · rw [frontier_equivFun, volume_image_eq_volume_div_covolume', h₄, ENNReal.zero_div]
    exact NullMeasurableSet.of_null h₄

end InnerProductSpace

end covolume

end ZLattice
