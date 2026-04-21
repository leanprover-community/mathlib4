/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.ProperAction.CompactlyGenerated

/-!
# Transitivity and properness of actions

We show that the actions of `SL(2, ℝ)` and `GL(2, ℝ)` on the upper half-plane are jointly
continuous, and the action of `SL(2, ℝ)` is proper. (These results require more imports
than in `UpperHalfPlane.Topology`, because they use the topology on the group as well)

TODO: Show properness of the action of `PGL(2, ℝ)` once this is defined.
-/
set_option backward.defeqAttrib.useBackward true

open scoped MatrixGroups Pointwise

public section

namespace UpperHalfPlane

@[fun_prop]
theorem num_continuous : Continuous ↿num := by unfold num; fun_prop

@[fun_prop]
theorem denom_continuous : Continuous ↿denom := by unfold denom; fun_prop

lemma continuous_toSL2R : Continuous toSL2R := by
  apply continuous_induced_rng.mpr
  simp only [Function.comp_def, coe_toSL2R]
  fun_prop (disch := grind [im_pos])

/-- The action of `SL(2, ℝ)` on `ℍ` is jointly continuous. -/
instance instContinuousSMulSL2R : ContinuousSMul SL(2, ℝ) ℍ where
  continuous_smul := by
    suffices ∀ (g : SL(2, ℝ)) (τ : ℍ),
        ContinuousAt (fun ⟨h, z⟩ ↦ (h 0 0 * (z : ℂ) + h 0 1) / (h 1 0 * z + h 1 1)) (g, τ) by
      simpa [continuous_induced_rng, continuous_iff_continuousAt, Function.comp_def,
        coe_specialLinearGroup_apply]
    intro g τ
    fun_prop (disch := exact denom_ne_zero g τ)

open Topology in
lemma σ_eventuallyEq (g : GL (Fin 2) ℝ) : σ =ᶠ[𝓝 g] fun _ ↦ σ g := by
  by_cases hg : 0 < g.det.val
  · suffices {h | 0 < h.det.val} ∈ 𝓝 g by
      filter_upwards [this] with h hh using by simp only [σ, hh, ↓reduceIte, hg]
    exact isOpen_Ioi (a := (0 : ℝ)) |>.preimage (by fun_prop) |>.mem_nhds hg
  · suffices {h | ¬0 < h.det.val} ∈ 𝓝 g by
      filter_upwards [this] with h hh using by simp only [σ, hh, ↓reduceIte, hg]
    simp only [not_lt, le_iff_lt_or_eq, Units.ne_zero, or_false] at hg ⊢
    exact isOpen_Iio (a := (0 : ℝ)) |>.preimage (by fun_prop) |>.mem_nhds hg

/-- The action of `GL(2, ℝ)` on `ℍ` is jointly continuous. -/
instance instContinuousSMulGL2R : ContinuousSMul (GL (Fin 2) ℝ) ℍ := by
  constructor
  simp only [continuous_induced_rng, Function.comp_def, coe_smul, continuous_iff_continuousAt,
    Prod.forall]
  refine fun g τ ↦ .congr ?_ (f := fun x ↦ (σ g) (num x.1 x.2 / denom x.1 x.2))
    (by filter_upwards [(σ_eventuallyEq g).prod_inl_nhds _] using by simp +contextual)
  fun_prop (disch := apply denom_ne_zero)

section proper_orbit_map

/-- Preliminary lemma for compactness of the orbit map. -/
private lemma cdsq_le {K : Set ℍ} (hK : IsCompact K) :
    ∃ A, ∀ g : SL(2, ℝ), g • I ∈ K → g 1 0 ^ 2 + g 1 1 ^ 2 ≤ A := by
  rcases K.eq_empty_or_nonempty with rfl | hKne; · simp
  obtain ⟨δ, hδ, hδK⟩ : ∃ δ > 0, ∀ z ∈ K, δ ≤ z.im :=
    match hK.exists_isMinOn hKne continuous_im.continuousOn with | ⟨z, _, h⟩ => ⟨_, z.im_pos, h⟩
  refine ⟨1 / δ, fun g hg ↦ ?_⟩
  specialize hδK (g • I) hg
  simp only [MulAction.compHom_smul_def, im_smul_eq_div_normSq, Matrix.SpecialLinearGroup.det_mapGL,
    Units.val_one, abs_one, I_im, mul_one] at hδK
  rw [le_div_iff₀ (normSq_denom_pos (Matrix.SpecialLinearGroup.mapGL ℝ g) (show I.im ≠ 0 by simp)),
    mul_comm, ← le_div_iff₀ hδ] at hδK
  simpa [Complex.normSq, add_comm, denom, sq] using hδK

/-- Preliminary lemma for compactness of the orbit map. -/
private lemma absq_le {K : Set ℍ} (hK : IsCompact K) :
    ∃ A : ℝ, ∀ g : SL(2, ℝ), g • I ∈ K → g 0 0 ^ 2 + g 0 1 ^ 2 ≤ A := by
  let S : SL(2, ℝ) := ⟨!![0, -1; 1, 0], by simp⟩
  obtain ⟨A, hA⟩ := cdsq_le (K := S • K) (hK.image <| continuous_const_smul S)
  refine ⟨A, fun g hg ↦ ?_⟩
  convert hA (S * g) (by rwa [mul_smul, Set.smul_mem_smul_set_iff]) using 1
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.eta_fin_two g.val, Matrix.mul_fin_two]
  simp

/-- The orbit map `g ↦ g • I` is a proper map `SL(2, ℝ) → ℍ`. -/
lemma isProperMap_smul_I : IsProperMap fun g : SL(2, ℝ) ↦ g • I := by
  refine isProperMap_iff_isCompact_preimage.mpr ⟨by fun_prop, fun K hK ↦ ?_⟩
  obtain ⟨A, hA⟩ := absq_le hK
  obtain ⟨A', hA'⟩ := cdsq_le hK
  -- activate the sup-norm on matrices
  let : SeminormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℝ) := Matrix.seminormedAddCommGroup
  have : ProperSpace (Matrix (Fin 2) (Fin 2) ℝ) := pi_properSpace
  have : IsCompact {m : Matrix (Fin 2) (Fin 2) ℝ | ∀ i j, |m i j| ≤ max √A √A'} := by
    convert ProperSpace.isCompact_closedBall (0 : Matrix (Fin 2) (Fin 2) ℝ) (max √A √A')
    simp only [le_sup_iff, Fin.forall_fin_two, Fin.isValue, Metric.closedBall, dist_zero_right,
      Matrix.norm_def, pi_norm_le_iff_of_nonempty, Real.norm_eq_abs]
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `ext` was not necessary.
    The cause of this might be `Matrix` function application defeq abuse. -/
    ext; grind
  have := Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage this
  refine this.of_isClosed_subset (hK.isClosed.preimage <| by fun_prop) (fun g hg ↦ ?_)
  intro i j
  fin_cases i
  · refine le_trans ?_ <| le_max_left √A √A'
    exact Real.le_sqrt_of_sq_le <| le_trans (by fin_cases j <;> simp [sq_nonneg]) (hA g hg)
  · refine le_trans ?_ <| le_max_right √A √A'
    exact Real.le_sqrt_of_sq_le <| le_trans (by fin_cases j <;> simp [sq_nonneg]) (hA' g hg)

instance instProperSMul : ProperSMul SL(2, ℝ) ℍ :=
  MulAction.properSMul_of_proper_orbitMap isProperMap_smul_I

end proper_orbit_map

end UpperHalfPlane

end
