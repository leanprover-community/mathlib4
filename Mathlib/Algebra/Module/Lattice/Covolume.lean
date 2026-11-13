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

## Naming convention

Some results are true in the case where the ambient finite-dimensional real vector space is the
pi-space `ι → ℝ` and in the case where it is an `InnerProductSpace`. We use the following
convention: the plain name is for the pi case, for e.g. `volume_image_eq_volume_div_covolume`. For
the same result in the `InnerProductSpace` case, we add a `prime`, for e.g.
`volume_image_eq_volume_div_covolume'`.
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

theorem ofReal_covolume : ENNReal.ofReal (L.covolume μ) = addCovolume L E μ := by
  rw [covolume_def, ENNReal.ofReal_toReal]
  rw [(IsFullLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ L) μ).covolume_eq_volume μ]
  exact (isBounded_halfOpenParallelepiped (K := ℝ) _).measure_lt_top.ne

theorem covolume_ne_zero : L.covolume μ ≠ 0 := by
  rw [covolume_eq_measure_fundamentalDomain L μ
    (IsFullLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ L) μ),
    measureReal_ne_zero_iff (ne_of_lt _)]
  · exact addHaar_halfOpenParallelepiped_ne_zero μ _
  · exact (isBounded_halfOpenParallelepiped _).measure_lt_top

theorem covolume_pos : 0 < L.covolume μ :=
  lt_of_le_of_ne ENNReal.toReal_nonneg (covolume_ne_zero L μ).symm

theorem covolume_eq_det_mul_measureReal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ L) (b₀ : Module.Basis ι ℝ E) :
    L.covolume μ = |b₀.det ((↑) ∘ b)| * μ.real (halfOpenParallelepiped ℝ b₀) := by
  rw [covolume_eq_measure_fundamentalDomain L μ (IsFullLattice.isAddFundamentalDomain b μ),
    addHaar_real_halfOpenParallelepiped_eq μ b₀]
  congr
  ext
  exact b.extendOfIsFullLattice_apply ℝ _

theorem covolume_eq_det {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℝ))
    [IsFullLattice ℝ L] (b : Module.Basis ι ℤ L) :
    L.covolume = |(Matrix.of ((↑) ∘ b)).det| := by
  rw [covolume_eq_measure_fundamentalDomain L volume
    (IsFullLattice.isAddFundamentalDomain b volume), volume_real_halfOpenParallelepiped]
  congr
  ext1
  exact b.extendOfIsFullLattice_apply ℝ _

theorem covolume_eq_det_inv {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℝ))
    [IsFullLattice ℝ L] (b : Module.Basis ι ℤ L) :
    L.covolume = |(LinearEquiv.det (b.extendOfIsFullLattice ℝ).equivFun : ℝ)|⁻¹ := by
  classical
  rw [covolume_eq_det L b, ← Pi.basisFun_det_apply, show (((↑) : L → _) ∘ ⇑b) =
    (b.extendOfIsFullLattice ℝ) by ext; simp, ← Module.Basis.det_inv, ← abs_inv,
    Units.val_inv_eq_inv_val, IsUnit.unit_spec, ← Module.Basis.det_basis, LinearEquiv.coe_det]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Let `L₁` be a sublattice of `L₂`. Then the index of `L₁` inside `L₂` is equal to
`covolume L₁ / covolume L₂`.
-/
theorem covolume_div_covolume_eq_relIndex {ι : Type*} [Fintype ι] (L₁ L₂ : Submodule ℤ (ι → ℝ))
    [IsFullLattice ℝ L₁] [IsFullLattice ℝ L₂] (h : L₁ ≤ L₂) :
    L₁.covolume / L₂.covolume = L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by
  classical
  let b₁ := IsFullLattice.basisOfPi ℝ L₁
  let b₂ := IsFullLattice.basisOfPi ℝ L₂
  rw [AddSubgroup.relIndex_eq_natAbs_det L₁.toAddSubgroup L₂.toAddSubgroup h b₁ b₂,
    Nat.cast_natAbs, Int.cast_abs]
  trans |(b₂.extendOfIsFullLattice ℝ).det (b₁.extendOfIsFullLattice ℝ)|
  · rw [← Module.Basis.det_mul_det _ (Pi.basisFun ℝ ι) _, abs_mul, Pi.basisFun_det_apply,
      ← Module.Basis.det_inv, Units.val_inv_eq_inv_val, IsUnit.unit_spec, Pi.basisFun_det_apply,
      covolume_eq_det _ b₁, covolume_eq_det _ b₂, mul_comm, abs_inv]
    congr 3 <;> ext <;> simp
  · rw [Module.Basis.det_apply, Module.Basis.det_apply, Int.cast_det]
    congr; ext i j
    rw [Matrix.map_apply, Module.Basis.toMatrix_apply, Module.Basis.toMatrix_apply,
      Module.Basis.extendOfIsFullLattice_apply]
    exact (b₂.extendOfIsFullLattice_repr_apply ℝ ⟨b₁ j, h (coe_mem _)⟩ i)

/--
A more general version of `covolume_div_covolume_eq_relIndex`;
see the `Naming conventions` section in the introduction.
-/
theorem covolume_div_covolume_eq_relIndex' {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L₁ L₂ : Submodule ℤ E) [IsFullLattice ℝ L₁] [IsFullLattice ℝ L₂] (h : L₁ ≤ L₂) :
    L₁.covolume / L₂.covolume = L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by
  let f := (EuclideanSpace.equiv _ ℝ).symm.trans
    (stdOrthonormalBasis ℝ E).repr.toContinuousLinearEquiv.symm
  have hf : MeasurePreserving f := (stdOrthonormalBasis ℝ E).measurePreserving_repr_symm.comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).symm
  rw [← covolume_comap L₁ volume volume hf, ← covolume_comap L₂ volume volume hf,
    covolume_div_covolume_eq_relIndex _ _ (fun _ h' ↦ h h'), comap_toAddSubgroup,
    comap_toAddSubgroup, Nat.cast_inj, AddSubgroup.relIndex_comap,
    AddSubgroup.map_comap_eq_self_of_surjective]
  exact f.surjective

theorem volume_image_eq_volume_div_covolume {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℝ))
    [IsFullLattice ℝ L] (b : Module.Basis ι ℤ L) {s : Set (ι → ℝ)} :
    volume ((b.extendOfIsFullLattice ℝ).equivFun '' s) =
      volume s / ENNReal.ofReal L.covolume := by
  rw [LinearEquiv.image_eq_preimage_symm, Measure.addHaar_preimage_linearEquiv,
    LinearEquiv.symm_symm, covolume_eq_det_inv L b, ENNReal.div_eq_inv_mul,
    ENNReal.ofReal_inv_of_pos (abs_pos.2 (LinearEquiv.det _).ne_zero), inv_inv, LinearEquiv.coe_det]

set_option backward.isDefEq.respectTransparency.types false in
/-- A more general version of `Submodule.volume_image_eq_volume_div_covolume`;
see the `Naming conventions` section in the introduction. -/
theorem volume_image_eq_volume_div_covolume' {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [IsFullLattice ℝ L] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℤ L) {s : Set E} (hs : NullMeasurableSet s) :
    volume ((b.extendOfIsFullLattice ℝ).equivFun '' s) =
      volume s / ENNReal.ofReal L.covolume := by
  let e : Fin (Module.finrank ℝ E) ≃ ι := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Module.finrank_eq_card_basis (b.extendOfIsFullLattice ℝ)])
  let f := (EuclideanSpace.equiv ι ℝ).symm.trans
    ((stdOrthonormalBasis ℝ E).reindex e).repr.toContinuousLinearEquiv.symm
  have hf : MeasurePreserving f :=
    ((stdOrthonormalBasis ℝ E).reindex e).measurePreserving_repr_symm.comp
      (PiLp.volume_preserving_toLp ι)
  let b' := b.map ((f.toLinearEquiv.restrictScalars ℤ).ofSubmodule' L).symm
  have hb : b'.extendOfIsFullLattice ℝ = (b.extendOfIsFullLattice ℝ).map f.symm.toLinearEquiv :=
    Module.Basis.eq_of_apply_eq fun i ↦ by simp [b', LinearEquiv.ofSubmodule'_symm_apply]
  rw [← hf.measure_preimage hs, ← (covolume_comap L volume volume hf),
    ← volume_image_eq_volume_div_covolume _ b', hb,
    ← f.image_symm_eq_preimage, ← Set.image_comp]
  simp

end Basic

end Submodule
