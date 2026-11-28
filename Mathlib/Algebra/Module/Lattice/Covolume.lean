/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot, Justus Springer
-/
module

public import Mathlib.Algebra.Module.Lattice.Discrete
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Lebesgue.Parallelepiped

import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

/-!
# Covolume of lattices

Let `E` be a finite-dimensional real vector space, `L` a full `ℤ`-lattice in `E` and `μ` a Haar
measure on `E`.

## Main definitions and results

* `Submodule.covolume`: the covolume of `L` with respect to `μ`, defined as the measure of an
  arbitrary fundamental domain of `L`.

* `Submodule.covolume_eq_measure_fundamentalDomain`: the covolume of `L` does not depend on the
  choice of the fundamental domain of `L`.

* `Submodule.covolume_eq_det`: if `L` is a lattice in `ℝ^n`, then its covolume is the absolute
  value of the determinant of any `ℤ`-basis of `L`.

* `Submodule.covolume_div_covolume_eq_relIndex`: Let `L₁` be a sublattice of `L₂`. Then the
  index of `L₁` inside `L₂` is equal to `covolume L₁ / covolume L₂`.

* `Submodule.volume_image_eq_measure_div_covolume`: The volume of the image of a set `s` under
  the coordinate map of a basis of `L` is the measure of `s` divided by the covolume of `L`.

* `Submodule.tendsto_card_div_pow`, `Submodule.tendsto_card_div_pow'`: the number of points of
  `t⁻¹ • L` in a set `s` is asymptotically `t ^ finrank ℝ E * μ s / covolume L μ`, as `t → ∞`
  through the natural numbers resp. the reals.

* `Submodule.tendsto_card_le_div`: for a cone `X` and `F` homogeneous of degree `finrank ℝ E`,
  the number of points `x ∈ X ∩ L` with `F x ≤ c` is asymptotically
  `c * μ {x ∈ X | F x ≤ 1} / covolume L μ`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Submodule

section FundamentalDomain

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E]

/-- The half-open parallelepiped spanned by a basis of a full lattice `L` is a fundamental domain
of `L`. -/
theorem Submodule.IsFullLattice.isAddFundamentalDomain {L : Submodule ℤ E} [IsFullLattice ℝ L]
    (b : Module.Basis ι ℤ L) (μ : Measure E) :
    IsAddFundamentalDomain L (halfOpenParallelepiped ℝ (b.extendOfIsFullLattice ℝ)) μ := by
  have h := (b.extendOfIsFullLattice ℝ).isAddFundamentalDomain_halfOpenParallelepiped μ
  rwa [b.span_extendOfIsFullLattice ℝ] at h

end FundamentalDomain

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] (L : Submodule ℤ E)

/-- The covolume of a lattice is the volume of some fundamental domain; see
`Submodule.covolume_eq_measure_fundamentalDomain` for the proof that the volume does not depend on
the choice of the fundamental domain. -/
def covolume (μ : Measure E := by volume_tac) : ℝ := (addCovolume L E μ).toReal

theorem covolume_def (μ : Measure E) : L.covolume μ = (addCovolume L E μ).toReal := rfl

variable [NormedSpace ℝ E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
variable [IsFullLattice ℝ L]

theorem covolume_eq_measure_fundamentalDomain {F : Set E} (h : IsAddFundamentalDomain L F μ) :
    L.covolume μ = μ.real F :=
  congr($(h.covolume_eq_volume μ).toReal)

theorem covolume_comap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [Measure.IsAddHaarMeasure ν]
    {e : F ≃L[ℝ] E} (he : MeasurePreserving e ν μ) :
    (L.comap (e.toLinearEquiv.restrictScalars ℤ).toLinearMap).covolume ν = L.covolume μ := by
  have h := IsFullLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ L) μ
  have h' := h.preimage_of_equiv he.quasiMeasurePreserving
    ((e.toLinearEquiv.restrictScalars ℤ).ofSubmodule' L).symm.bijective
    fun _ _ ↦ by simp [vadd_def]
  rw [covolume_eq_measure_fundamentalDomain _ _ h, covolume_eq_measure_fundamentalDomain _ _ h',
    he.measureReal_preimage h.nullMeasurableSet]

variable [FiniteDimensional ℝ E]

theorem ofReal_covolume : .ofReal (L.covolume μ) = addCovolume L E μ := by
  apply ENNReal.ofReal_toReal
  rw [(IsFullLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ L) μ).covolume_eq_volume μ]
  finiteness

theorem covolume_ne_zero : L.covolume μ ≠ 0 := by
  rw [covolume_eq_measure_fundamentalDomain L μ
    (IsFullLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ L) μ), measureReal_ne_zero_iff]
  exact addHaar_halfOpenParallelepiped_ne_zero μ _

theorem covolume_pos : 0 < L.covolume μ :=
  lt_of_le_of_ne ENNReal.toReal_nonneg (covolume_ne_zero L μ).symm

theorem covolume_eq_det_mul_measureReal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ L) (b₀ : Module.Basis ι ℝ E) :
    L.covolume μ = |b₀.det ((↑) ∘ b)| * μ.real (halfOpenParallelepiped ℝ b₀) := by
  rw [covolume_eq_measure_fundamentalDomain L μ (IsFullLattice.isAddFundamentalDomain b μ),
    addHaar_real_halfOpenParallelepiped_eq μ b₀, b.coe_extendOfIsFullLattice ℝ]

theorem covolume_eq_det {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℝ))
    [IsFullLattice ℝ L] (b : Module.Basis ι ℤ L) :
    L.covolume = |(Matrix.of ((↑) ∘ b)).det| := by
  rw [covolume_eq_measure_fundamentalDomain L volume
    (IsFullLattice.isAddFundamentalDomain b volume), volume_real_halfOpenParallelepiped,
    b.coe_extendOfIsFullLattice ℝ]

theorem covolume_eq_det_inv {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℝ))
    [IsFullLattice ℝ L] (b : Module.Basis ι ℤ L) :
    L.covolume = |((b.extendOfIsFullLattice ℝ).equivFun.det : ℝ)|⁻¹ := by
  classical
  rw [covolume_eq_det L b, ← Pi.basisFun_det_apply, ← b.coe_extendOfIsFullLattice ℝ,
    ← Module.Basis.det_inv, ← abs_inv, Units.val_inv_eq_inv_val, IsUnit.unit_spec,
    ← Module.Basis.det_basis, Module.Basis.equiv_basisFun, LinearEquiv.coe_det]

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `L₁` be a sublattice of `L₂`. Then the index of `L₁` inside `L₂` is equal to
`covolume L₁ / covolume L₂`. -/
theorem covolume_div_covolume_eq_relIndex (L₁ L₂ : Submodule ℤ E) [IsFullLattice ℝ L₁]
    [IsFullLattice ℝ L₂] (h : L₁ ≤ L₂) :
    L₁.covolume μ / L₂.covolume μ = L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by
  classical
  let b₁ := Module.finBasisOfFinrankEq ℤ L₁ (IsFullLattice.finrank_eq ℝ L₁)
  let b₂ := Module.finBasisOfFinrankEq ℤ L₂ (IsFullLattice.finrank_eq ℝ L₂)
  let b₀ := b₂.extendOfIsFullLattice ℝ
  rw [L₁.toAddSubgroup.relIndex_eq_natAbs_det L₂.toAddSubgroup h b₁ b₂,
    Nat.cast_natAbs, Int.cast_abs, covolume_eq_det_mul_measureReal L₁ μ b₁ b₀,
    covolume_eq_det_mul_measureReal L₂ μ b₂ b₀, ← b₂.coe_extendOfIsFullLattice ℝ,
    Module.Basis.det_self, abs_one, one_mul, mul_div_cancel_right₀,
    ← b₁.coe_extendOfIsFullLattice ℝ, Module.Basis.det_apply, Module.Basis.det_apply, Int.cast_det]
  · congr
    ext i j
    rw [Matrix.map_apply, Module.Basis.toMatrix_apply, Module.Basis.toMatrix_apply,
      Module.Basis.extendOfIsFullLattice_apply]
    exact (b₂.extendOfIsFullLattice_repr_apply ℝ ⟨b₁ j, h (coe_mem _)⟩ i)
  · exact ((measureReal_ne_zero_iff).mpr (addHaar_halfOpenParallelepiped_ne_zero μ b₀))

/-- The volume of the image of a set `s` under the coordinate map of a basis of `L` is the measure
of `s` divided by the covolume of `L`. -/
theorem volume_image_eq_measure_div_covolume {ι : Type*} [Fintype ι] (b : Module.Basis ι ℤ L)
    (s : Set E) :
    volume ((b.extendOfIsFullLattice ℝ).equivFun '' s) = μ s / ENNReal.ofReal (L.covolume μ) := by
  set b' := b.extendOfIsFullLattice ℝ
  let φ : E ≃ᵐ (ι → ℝ) := b'.equivFunL.toHomeomorph.toMeasurableEquiv
  have hφ : ⇑φ = b'.equivFun := by ext; simp [φ]
  have : (Measure.map φ μ).IsAddHaarMeasure := b'.equivFunL.isAddHaarMeasure_map μ
  have hν : Measure.map φ μ = ENNReal.ofReal (L.covolume μ) • volume := by
    rw [Measure.addHaarMeasure_unique (Measure.map φ μ) (.piIcc01 ι), addHaarMeasure_eq_volume_pi,
      φ.map_apply, ofReal_covolume, (IsFullLattice.isAddFundamentalDomain b μ).covolume_eq_volume μ,
      addHaar_halfOpenParallelepiped, parallelepiped_basis_eq]
    congr 2
    ext x
    simp [hφ, b', TopologicalSpace.PositiveCompacts.piIcc01, Pi.le_def, forall_and]
  rw [ENNReal.eq_div_iff (ENNReal.ofReal_pos.2 (covolume_pos L μ)).ne' ENNReal.ofReal_ne_top]
  conv_rhs => rw [← φ.preimage_image s, ← φ.map_apply, hν, smul_apply, smul_eq_mul, hφ]

/-- The `measureReal` version of `Submodule.volume_image_eq_measure_div_covolume`. -/
theorem volume_real_image_eq_measureReal_div_covolume {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℤ L) (s : Set E) :
    volume.real ((b.extendOfIsFullLattice ℝ).equivFun '' s) = μ.real s / L.covolume μ := by
  rw [measureReal_def, volume_image_eq_measure_div_covolume L μ b, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (covolume_pos L μ).le, measureReal_def]

section Counting

open Bornology Filter Pointwise Topology

/-- Let `s` be a bounded, measurable set whose frontier has measure zero. Then
`card (s ∩ n⁻¹ • L) / n ^ finrank ℝ E` tends to `μ s / covolume L μ` as `n → ∞`. -/
theorem tendsto_card_div_pow {s : Set E} (hs₁ : IsBounded s) (hs₂ : MeasurableSet s)
    (hs₃ : μ (frontier s) = 0) :
    Tendsto (fun n : ℕ ↦ (Nat.card (s ∩ (n : ℝ)⁻¹ • L : Set E) : ℝ) / n ^ Module.finrank ℝ E)
      atTop (𝓝 (μ.real s / L.covolume μ)) := by
  let b := Module.Free.chooseBasis ℤ L
  set b' := b.extendOfIsFullLattice ℝ
  rw [← volume_real_image_eq_measureReal_div_covolume L μ b, ← IsFullLattice.finrank_eq ℝ L,
    Module.finrank_eq_card_chooseBasisIndex]
  refine tendsto_card_div_pow_atTop_volume (b'.equivFun '' s) ?_ ?_ ?_ |>.congr' ?_
  · exact hs₁.image b'.equivFunL.toContinuousLinearMap
  · exact b'.equivFunL.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hs₂
  · rw [← LinearEquiv.coe_toContinuousLinearEquiv', ← ContinuousLinearEquiv.image_frontier,
      LinearEquiv.coe_toContinuousLinearEquiv', volume_image_eq_measure_div_covolume L μ b, hs₃,
      ENNReal.zero_div]
  · filter_upwards with n
    rw [← Nat.card_image_of_injective b'.equivFun.injective, Set.image_inter b'.equivFun.injective,
      image_smul_set, b.image_equivFun_extendOfIsFullLattice ℝ]

/-- Let `s` be a bounded, measurable set whose frontier has measure zero. Then
`card (s ∩ t⁻¹ • L) / t ^ finrank ℝ E` tends to `μ s / covolume L μ` as `t → ∞`, where `t`
is a real variable. -/
theorem tendsto_card_div_pow' {s : Set E} (hs₁ : IsBounded s) (hs₂ : MeasurableSet s)
    (hs₃ : μ (frontier s) = 0) (hs₄ : ∀ ⦃x y : ℝ⦄, 0 < x → x ≤ y → x • s ⊆ y • s) :
    Tendsto (fun t : ℝ ↦ (Nat.card (s ∩ t⁻¹ • L : Set E) : ℝ) / t ^ Module.finrank ℝ E)
      atTop (𝓝 (μ.real s / L.covolume μ)) := by
  let b := Module.Free.chooseBasis ℤ L
  set b' := b.extendOfIsFullLattice ℝ
  rw [← volume_real_image_eq_measureReal_div_covolume L μ b, ← IsFullLattice.finrank_eq ℝ L,
    Module.finrank_eq_card_chooseBasisIndex]
  refine tendsto_card_div_pow_atTop_volume' (b'.equivFun '' s) ?_ ?_ ?_ ?_ |>.congr' ?_
  · exact hs₁.image b'.equivFunL.toContinuousLinearMap
  · exact b'.equivFunL.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hs₂
  · rw [← LinearEquiv.coe_toContinuousLinearEquiv', ← ContinuousLinearEquiv.image_frontier,
      LinearEquiv.coe_toContinuousLinearEquiv', volume_image_eq_measure_div_covolume L μ b, hs₃,
      ENNReal.zero_div]
  · intro x y hx hxy
    rw [← image_smul_set, ← image_smul_set]
    exact Set.image_mono (hs₄ hx hxy)
  · filter_upwards with t
    rw [← Nat.card_image_of_injective b'.equivFun.injective, Set.image_inter b'.equivFun.injective,
      image_smul_set, b.image_equivFun_extendOfIsFullLattice ℝ]

private theorem tendsto_card_le_div_aux {E : Type*} [AddCommGroup E] [Module ℝ E] {X : Set E}
    (hX : ∀ ⦃x⦄ ⦃r : ℝ⦄, x ∈ X → 0 < r → r • x ∈ X)
    {d : ℕ} {F : E → ℝ} (hF : ∀ x ⦃r : ℝ⦄, 0 ≤ r → F (r • x) = r ^ d * F x) {c : ℝ}
    (hc : 0 < c) : c • {x ∈ X | F x ≤ 1} = {x ∈ X | F x ≤ c ^ d} := by
  ext x
  simp_rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne', Set.mem_ofPred_eq, hF _
    (inv_pos_of_pos hc).le, inv_pow, inv_mul_le_iff₀ (pow_pos hc _), mul_one, and_congr_left_iff]
  exact fun _ ↦ ⟨fun h ↦ (smul_inv_smul₀ hc.ne' x) ▸ hX h hc, fun h ↦ hX h (inv_pos_of_pos hc)⟩

/-- Let `X` be a cone and `F` a function on `X` that is homogeneous of degree `finrank ℝ E`,
such that `{x ∈ X | F x ≤ 1}` is bounded, measurable and its frontier has measure zero. Then
`card {x ∈ X ∩ L | F x ≤ c} / c` tends to `μ {x ∈ X | F x ≤ 1} / covolume L μ` as `c → ∞`. -/
theorem tendsto_card_le_div [Nontrivial E] {X : Set E}
    (hX : ∀ ⦃x⦄ ⦃r : ℝ⦄, x ∈ X → 0 < r → r • x ∈ X) {F : E → ℝ}
    (h₁ : ∀ x ⦃r : ℝ⦄, 0 ≤ r → F (r • x) = r ^ Module.finrank ℝ E * F x)
    (h₂ : IsBounded {x ∈ X | F x ≤ 1}) (h₃ : MeasurableSet {x ∈ X | F x ≤ 1})
    (h₄ : μ (frontier {x ∈ X | F x ≤ 1}) = 0) :
    Tendsto (fun c : ℝ ↦ Nat.card ({x ∈ X | F x ≤ c} ∩ L : Set E) / c)
      atTop (𝓝 (μ.real {x ∈ X | F x ≤ 1} / L.covolume μ)) := by
  set S := {x ∈ X | F x ≤ 1}
  have hd : 0 < Module.finrank ℝ E := Module.finrank_pos
  have hS {t : ℝ} (ht : 0 < t) := tendsto_card_le_div_aux hX h₁ ht
  refine (tendsto_card_div_pow' L μ h₂ h₃ h₄ (fun x y hx hxy ↦ ?_)).comp
    (tendsto_rpow_atTop (inv_pos.mpr (Nat.cast_pos.mpr hd))) |>.congr' ?_
  · rw [hS hx, hS (hx.trans_le hxy)]
    intro a ⟨ha₁, ha₂⟩
    exact ⟨ha₁, ha₂.trans (pow_le_pow_left₀ hx.le hxy _)⟩
  filter_upwards [eventually_gt_atTop 0] with c hc
  set t := c ^ (Module.finrank ℝ E : ℝ)⁻¹
  have ht : 0 < t := Real.rpow_pos_of_pos hc _
  have htc : t • S = {x ∈ X | F x ≤ c} := by
    rw [hS ht, Real.rpow_inv_natCast_pow hc.le hd.ne']
  have hL : t • S ∩ L = (t • ·) '' (S ∩ t⁻¹ • L) := by
    rw [Set.image_smul, Set.smul_set_inter₀ ht.ne', smul_inv_smul₀ ht.ne']
  rw [Function.comp_apply, Real.rpow_inv_natCast_pow hc.le hd.ne', ← htc, hL,
    Nat.card_image_of_injective (MulAction.injective₀ ht.ne')]

end Counting

end Submodule
