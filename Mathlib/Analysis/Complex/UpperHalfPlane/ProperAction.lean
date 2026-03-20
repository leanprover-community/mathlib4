/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Topology.Algebra.ProperAction.Fiberwise
import Mathlib.Topology.Instances.Matrix

/-!
# Transitivity and properness of actions

We show that the actions of `SL(2, ℝ)` and `GL(2, ℝ)` on the upper half-plane are jointly
continuous, and the action of `SL(2, ℝ)` is proper.

TODO: Show properness of the action of `PGL(2, ℝ)` once this is defined.
-/

open scoped MatrixGroups Pointwise

public section

-- This lemma has nothing to do with the upper half-plane, but there is no obvious upstream
-- place for it to go.
/-- The set of matrices with bounded entries is compact. -/
lemma Matrix.isCompact_forall_apply_le {R m n : Type*} [SeminormedAddCommGroup R]
    [ProperSpace R] (B : ℝ) [Finite m] [Finite n] :
    IsCompact {m : Matrix m n R | ∀ i j, ‖m i j‖ ≤ B} := by
  let e : (m → n → R) ≃ₜ Matrix m n R := { Matrix.of with }
  rcases isEmpty_or_nonempty m with hm | hm; · simp
  rcases isEmpty_or_nonempty n with hn | hn; · simp
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  convert e.isCompact_image.mpr (isCompact_closedBall 0 B) using 1
  ext t
  simp [pi_norm_le_iff_of_nonempty, e]

namespace UpperHalfPlane

section toSL2R

/-- Map from `ℍ` to `SL(2, ℝ)`, giving a continuous section of the map `g ↦ g • I`. -/
noncomputable def toSL2R (z : ℍ) : SL(2, ℝ) :=
  ⟨!![√z.im, z.re / √z.im; 0, 1 / √z.im], by
    simp [mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr z.im_pos)]⟩

lemma toSL2R_apply (z : ℍ) : z.toSL2R =
  ⟨!![√z.im, z.re / √z.im; 0, 1 / √z.im], by
    simp [mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr z.im_pos)]⟩ := rfl

@[simp] lemma coe_toSL2R (z : ℍ) : z.toSL2R = !![√z.im, z.re / √z.im; 0, 1 / √z.im] := rfl

@[simp] lemma toSL2R_smul_I (z : ℍ) : z.toSL2R • I = z := by
  have : √z.im ≠ (0 : ℂ) := by simpa [Real.sqrt_ne_zero'] using z.im_pos
  ext
  suffices z.re / √z.im + √z.im * Complex.I = z * (↑√z.im)⁻¹ by
    rw [coe_specialLinearGroup_apply, div_eq_iff (mod_cast denom_ne_zero z.toSL2R I)]
    simpa [add_comm]
  rw [div_add' (hc := this), mul_right_comm, ← Complex.ofReal_mul, ← Real.sqrt_mul z.im_pos.le,
    Real.sqrt_mul_self z.im_pos.le, re_add_im, div_eq_mul_inv]

lemma continuous_toSL2R : Continuous toSL2R := by
  refine continuous_induced_rng.mpr (continuous_matrix fun i j ↦ ?_)
  fin_cases i <;> fin_cases j
  · exact Real.continuous_sqrt.comp continuous_im
  · exact continuous_re.div₀ (by fun_prop) (fun τ : ℍ ↦ Real.sqrt_ne_zero'.mpr τ.im_pos)
  · exact continuous_const
  · simpa using .inv₀ (by fun_prop) (fun τ : ℍ ↦ Real.sqrt_ne_zero'.mpr τ.im_pos)

end toSL2R

/-- `SL(2, ℝ)` acts transitively on the upper half-plane. -/
instance isPretransitiveSL2R : MulAction.IsPretransitive SL(2, ℝ) ℍ :=
  .of_orbit fun z ↦ ⟨_, toSL2R_smul_I z⟩

/-- `GL(2, ℝ)` acts transitively on the upper half-plane. -/
instance isPretransitiveGL2R : MulAction.IsPretransitive (GL (Fin 2) ℝ) ℍ :=
  .of_smul_eq ((↑) : SL(2, ℝ) → _) fun {g z} ↦ (MulAction.compHom_smul_def _ g z).symm

/-- The action of `SL(2, ℝ)` on `ℍ` is jointly continuous. -/
instance instContinuousSMulSL2R : ContinuousSMul SL(2, ℝ) ℍ := by
  constructor
  suffices ∀ (g : SL(2, ℝ)) (τ : ℍ),
      ContinuousAt (fun ⟨h, z⟩ ↦ (h 0 0 * (z : ℂ) + h 0 1) / (h 1 0 * z + h 1 1)) (g, τ) by
    simpa [continuous_induced_rng, continuous_iff_continuousAt, Function.comp_def,
      coe_specialLinearGroup_apply]
  refine fun g τ ↦ .div ?_ ?_ (denom_ne_zero g τ) <;>
  refine .add (.mul ?_ (by fun_prop)) ?_ <;>
  · refine (Complex.continuous_ofReal.comp ?_).continuousAt
    exact (continuous_subtype_val.matrix_elem _ _).comp continuous_fst

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
  refine ContinuousAt.comp (by fun_prop) (.div₀ ?_ ?_ (denom_ne_zero _ _)) <;>
  · refine .add (.mul ?_ (by fun_prop)) ?_ <;>
    · refine (Complex.continuous_ofReal.comp ?_).continuousAt
      refine Continuous.comp (g := fun g : GL (Fin 2) ℝ ↦ g _ _) ?_ continuous_fst
      exact (continuous_id.matrix_elem _ _).comp Units.continuous_val

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
  have : IsCompact {m : Matrix (Fin 2) (Fin 2) ℝ | ∀ i j, |m i j| ≤ max √A √A'} := by
    apply Matrix.isCompact_forall_apply_le
  have := Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage this
  refine this.of_isClosed_subset (hK.isClosed.preimage <| by fun_prop) (fun g hg ↦ ?_)
  intro i j
  fin_cases i
  · refine le_trans ?_ <| le_max_left √A √A'
    exact Real.le_sqrt_of_sq_le <| le_trans (by fin_cases j <;> simp [sq_nonneg]) (hA g hg)
  · refine le_trans ?_ <| le_max_right √A √A'
    exact Real.le_sqrt_of_sq_le <| le_trans (by fin_cases j <;> simp [sq_nonneg]) (hA' g hg)

instance instProperSMul : ProperSMul SL(2, ℝ) ℍ := by
  apply MulAction.properSMul_of_isCompact_setOf_inter_nonempty
  intro U V hU hV
  let U' := {g : SL(2, ℝ) | g • I ∈ U}
  let V' := {g : SL(2, ℝ) | g • I ∈ V}
  have hU' : IsCompact U' := isProperMap_smul_I.isCompact_preimage hU
  have hV' : IsCompact V' := isProperMap_smul_I.isCompact_preimage hV
  suffices {g | (U ∩ g • V).Nonempty} = (fun x ↦ x.1 * x.2⁻¹) '' (U' ×ˢ V') from
    this ▸ (hU'.prod hV').image (by fun_prop)
  ext w
  constructor
  · rintro ⟨τ, ⟨hτ, hτ'⟩⟩
    use (τ.toSL2R, w⁻¹ * τ.toSL2R)
    simpa [U', V', hτ, mul_smul, ← V.mem_smul_set_iff_inv_smul_mem]
  · rintro ⟨⟨g, h⟩, ⟨hg, hh⟩, rfl⟩
    refine ⟨g • I, hg, ?_⟩
    simpa [mul_smul, Set.mem_inv_smul_set_iff]

end proper_orbit_map

end UpperHalfPlane

end
