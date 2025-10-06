/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Continuous linear maps on a Hilbert space are a `StarOrderedRing`

In this file we show that the continuous linear maps on a complex Hilbert space form a
`StarOrderedRing`.  Note that they are already equipped with the Loewner partial order. We also
prove that, with respect to this partial order, a map is positive if every element of the
real spectrum is nonnegative. Consequently, when `H` is a Hilbert space, then `H →L[ℂ] H` is
equipped with all the usual instances of the continuous functional calculus.

-/

namespace ContinuousLinearMap

open RCLike
open scoped NNReal

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]

open scoped InnerProductSpace in
lemma IsPositive.spectrumRestricts {f : H →L[𝕜] H} (hf : f.IsPositive) :
    SpectrumRestricts f ContinuousMap.realToNNReal := by
  rw [SpectrumRestricts.nnreal_iff]
  intro c hc
  contrapose! hc
  rw [spectrum.notMem_iff, IsUnit.sub_iff, sub_eq_add_neg, ← map_neg]
  rw [← neg_pos] at hc
  set c := -c
  exact isUnit_of_forall_le_norm_inner_map _ (c := ⟨c, hc.le⟩) hc fun x ↦ calc
    ‖x‖ ^ 2 * c = re ⟪algebraMap ℝ (H →L[𝕜] H) c x, x⟫_𝕜 := by
      rw [Algebra.algebraMap_eq_smul_one, ← algebraMap_smul 𝕜 c (1 : (H →L[𝕜] H)), coe_smul',
        Pi.smul_apply, one_apply, inner_smul_left, RCLike.algebraMap_eq_ofReal, conj_ofReal,
        re_ofReal_mul, inner_self_eq_norm_sq, mul_comm]
    _ ≤ re ⟪(f + (algebraMap ℝ (H →L[𝕜] H)) c) x, x⟫_𝕜 := by
      simpa only [add_apply, inner_add_left, map_add, le_add_iff_nonneg_left]
        using hf.re_inner_nonneg_left x
    _ ≤ ‖⟪(f + (algebraMap ℝ (H →L[𝕜] H)) c) x, x⟫_𝕜‖ := RCLike.re_le_norm _

instance : NonnegSpectrumClass ℝ (H →L[𝕜] H) where
  quasispectrum_nonneg_of_nonneg f hf :=
    QuasispectrumRestricts.nnreal_iff.mp <| sub_zero f ▸ hf.spectrumRestricts

/-- Because this takes `ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint` as an argument,
and for the moment we only have this for `𝕜 := ℂ`, this is not registered as an instance. -/
lemma instStarOrderedRingRCLike
    [ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint] :
    StarOrderedRing (H →L[𝕜] H) where
  le_iff f g := by
    constructor
    · intro h
      rw [le_def] at h
      obtain ⟨p, hp₁, -, hp₃⟩ :=
        CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts h.1 h.spectrumRestricts
      refine ⟨p ^ 2, ?_, by symm; rwa [add_comm, ← eq_sub_iff_add_eq]⟩
      exact AddSubmonoid.subset_closure ⟨p, by simp only [hp₁.star_eq, sq]⟩
    · rintro ⟨p, hp, rfl⟩
      rw [le_def, add_sub_cancel_left]
      induction hp using AddSubmonoid.closure_induction with
      | mem _ hf =>
        obtain ⟨f, rfl⟩ := hf
        simpa using ContinuousLinearMap.IsPositive.adjoint_conj isPositive_one f
      | zero => exact isPositive_zero
      | add f g _ _ hf hg => exact hf.add hg

instance instStarOrderedRing {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : StarOrderedRing (H →L[ℂ] H) :=
  instStarOrderedRingRCLike

end ContinuousLinearMap
