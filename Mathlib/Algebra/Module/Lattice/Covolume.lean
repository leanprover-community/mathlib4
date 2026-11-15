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

import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Covolume of lattices

Let `E` be a finite-dimensional real vector space and `L` a full `ℤ`-lattice in `E`.

## Main definitions and results

* `Module.Basis.isAddFundamentalDomain_halfOpenParallelepiped`: the half-open parallelepiped
  spanned by a basis `b` of a real normed space is a fundamental domain of `span ℤ (range b)`.

* `Submodule.covolume`: the covolume of `L`, defined as the volume of an arbitrary fundamental
  domain of `L`.

* `Submodule.covolume_eq_measure_fundamentalDomain`: the covolume of `L` does not depend on the
  choice of the fundamental domain of `L`.

* `Submodule.covolume_eq_det`: if `L` is a lattice in `ℝ^n`, then its covolume is the absolute
  value of the determinant of any `ℤ`-basis of `L`.

* `Submodule.covolume_div_covolume_eq_relIndex`: Let `L₁` be a sublattice of `L₂`. Then the
  index of `L₁` inside `L₂` is equal to `covolume L₁ / covolume L₂`.

-/

@[expose] public section

noncomputable section

open MeasureTheory Set Submodule

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] (b : Module.Basis ι ℝ E)

theorem Module.Basis.isAddFundamentalDomain_halfOpenParallelepiped (μ : Measure E) :
    IsAddFundamentalDomain (span ℤ (range b)) (halfOpenParallelepiped ℝ b) μ :=
  .mk' (measurableSet_halfOpenParallelepiped b).nullMeasurableSet
    b.existsUnique_vadd_mem_halfOpenParallelepiped

/-- The half-open parallelepiped spanned by a basis of a full lattice `L` is a fundamental domain
of `L`. -/
theorem Submodule.IsFullLattice.isAddFundamentalDomain {L : Submodule ℤ E} [IsFullLattice ℝ L]
    (b : Module.Basis ι ℤ L) (μ : Measure E) :
    IsAddFundamentalDomain L (halfOpenParallelepiped ℝ (b.extendOfIsFullLattice ℝ)) μ := by
  have h := (b.extendOfIsFullLattice ℝ).isAddFundamentalDomain_halfOpenParallelepiped μ
  rwa [b.extendOfIsFullLattice_span ℝ] at h

namespace Submodule

section General

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] (L : Submodule ℤ E)

/-- The covolume of a lattice is the volume of some fundamental domain; see
`Submodule.covolume_eq_measure_fundamentalDomain` for the proof that the volume does not depend on
the choice of the fundamental domain. -/
def covolume (μ : Measure E := by volume_tac) : ℝ := (addCovolume L E μ).toReal

theorem covolume_def (μ : Measure E) : L.covolume μ = (addCovolume L E μ).toReal := rfl

end General

section Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [IsFullLattice ℝ L]
variable (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem covolume_eq_measure_fundamentalDomain {F : Set E} (h : IsAddFundamentalDomain L F μ) :
    L.covolume μ = μ.real F :=
  congr($(h.covolume_eq_volume μ).toReal)

theorem covolume_comap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
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
/--
Let `L₁` be a sublattice of `L₂`. Then the index of `L₁` inside `L₂` is equal to
`covolume L₁ / covolume L₂`.
-/
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
theorem volume_image_eq_volume_div_covolume {ι : Type*} [Fintype ι] (b : Module.Basis ι ℤ L)
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

end Basic

end Submodule
