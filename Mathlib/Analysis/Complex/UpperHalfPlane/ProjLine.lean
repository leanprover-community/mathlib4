/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints

/-!
# Embedding the upper half-plane into the projective line
-/

@[expose] public noncomputable section

open UpperHalfPlane Matrix GeneralLinearGroup

lemma UpperHalfPlane.toOnePoint_smul {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (τ : ℍ) :
    (↑(g • τ) : OnePoint ℂ) = (g.map Complex.ofRealHom) • τ := by
  have : g 1 0 * (τ : ℂ) + g 1 1 ≠ 0 := UpperHalfPlane.denom_ne_zero g τ
  simp [OnePoint.smul_some_eq_ite, this, UpperHalfPlane.coe_smul_of_det_pos hg, num, denom]

/-- If `g` is parabolic, then `g` has no fixed points in `ℍ`. -/
lemma UpperHalfPlane.smul_ne_self_of_isParabolic {g : GL (Fin 2) ℝ} (hg : g.IsParabolic) (τ : ℍ) :
    g • τ ≠ τ :=
  fun hτ ↦ hg.not_isElliptic <|
    isElliptic_of_exists_smul_eq_self hg.val_det_pos hg.not_mem_center ⟨τ, hτ⟩

/-- If `g` is hyperbolic, then `g` has no fixed points in `ℍ`. -/
lemma UpperHalfPlane.smul_ne_self_of_isHyperbolic {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val)
    (hgh : g.IsHyperbolic) (τ : ℍ) : g • τ ≠ τ :=
  fun hτ ↦ hgh.not_isElliptic <|
    isElliptic_of_exists_smul_eq_self hg hgh.not_mem_center ⟨τ, hτ⟩

namespace UpperHalfPlane
/-!
## Stabilizers and fixed points
-/

/-- The pointwise stabilizer of the vertical line `ℝ₊ • I` in `GL(2, ℝ)₊` is the scalar multiples
of the identity. -/
lemma forall_smul_pos_mul_I_eq_iff_of_det_pos {g : GL (Fin 2) ℝ} (hdet : 0 < g.det.val) :
    (∀ (t : ℝ) (ht : 0 < t), g • (⟨t * .I, by simpa⟩ : ℍ) = ⟨t * .I, by simpa⟩)
      ↔ ∃ r : ℝˣ, g = r • 1 where
  mp hg := by
    have hg1 : g • I = I := by simpa using hg 1 (by norm_num)
    have hp : ¬g.IsParabolic := fun h ↦ I.smul_ne_self_of_isParabolic h hg1
    have hh : ¬g.IsHyperbolic := fun h ↦ I.smul_ne_self_of_isHyperbolic hdet h hg1
    have he : ¬g.IsElliptic := fun he ↦ by
      have hI := (gl_smul_eq_self_iff_eq_fixedPt he).1 hg1
      have h2I := (gl_smul_eq_self_iff_eq_fixedPt he).1 <| hg 2 (by norm_num)
      simpa [UpperHalfPlane.ext_iff] using hI.trans h2I.symm
    obtain ⟨r, hr⟩ : g.val ∈ Set.range (Matrix.scalar (Fin 2)) := by
      simp only [Matrix.IsParabolic] at hp
      grind [eq_of_ge_of_le (not_lt.mp he) (not_lt.mp hh)]
    have := Units.mul_inv g
    rw [← hr] at this
    use .mkOfMulEqOne r _ (by simpa using congr_arg (· 0 0) this)
    simp [Units.ext_iff, Units.smul_def, ← hr, Matrix.smul_one_eq_diagonal]
  mpr := by
    rintro ⟨r, rfl⟩ t ht
    ext
    simp [coe_smul_of_det_pos hdet, num, denom, Units.smul_def]

/-- The pointwise stabilizer of the vertical line `ℝ₊ • I` in `GL(2, ℝ)` consists of the scalar
multiples of the identity and of `J = [-1, 0; 0, 1]`. -/
lemma forall_smul_pos_mul_I_eq_iff {g : GL (Fin 2) ℝ} :
    (∀ (t : ℝ) (ht : 0 < t), g • (⟨t * .I, by simpa⟩ : ℍ) = ⟨t * .I, by simpa⟩) ↔
      (∃ r : ℝˣ, g = r • 1) ∨ (∃ r : ℝˣ, g = r • J) := by
  by_cases h : 0 < g.det.val
  · rw [forall_smul_pos_mul_I_eq_iff_of_det_pos h]
    suffices ¬∃ r, g = r • J by tauto
    contrapose! h
    obtain ⟨r, rfl⟩ := h
    simp [Units.smul_def, mul_self_nonneg r.val]
  · -- If `det g < 0`, we show that `g * J⁻¹` also fixes the vertical line
    have : ¬∃ r : ℝˣ, g = r • 1 := by
      contrapose! h
      rcases h with ⟨r, rfl⟩
      refine lt_of_le_of_ne' ?_ (Units.ne_zero _)
      simp [Units.smul_def, sq_nonneg]
    rw [eq_false_intro this, false_or]
    conv =>
      enter [1, t, ht, 1]
      rw [← (J_smul_eq_self_iff (x := ⟨t * .I, by simpa⟩)).mpr (by simp),
        ← SemigroupAction.mul_smul, ← inv_J]
    rw [forall_smul_pos_mul_I_eq_iff_of_det_pos]
    · simp only [mul_inv_eq_iff_eq_mul (a := g), smul_one_mul]
    · rw [map_mul, map_inv, det_J, inv_neg_one, mul_neg_one, Units.val_neg]
      grind [g.det_ne_zero.lt_or_gt, Matrix.GeneralLinearGroup.val_det_apply]

end UpperHalfPlane

end
