/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform

/-!
# Derivatives of modular forms

This file defines normalized derivative $D = \frac{1}{2\pi i} \frac{d}{dz}$
and serre dervative $\partial_k := D - \frac{k}{12} E_2$ of modular forms.

TODO:
- Serre derivative preserves modularity, i.e. $\partial_k (M_k) \subseteq M_{k+2}$.
- Use above, prove Ramanujan's identities. See [here](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/main/SpherePacking/ModularForms/RamanujanIdentities.lean)
  for `sorry`-free proofs.
-/

open UpperHalfPlane hiding I
open Real Complex
open scoped Manifold MatrixGroups ModularForm

namespace Derivative

@[expose] public noncomputable section

/--
Normalized derivative $D = \frac{1}{2\pi i} \frac{d}{dz}$.
-/
def normalizedDerivOfComplex (F : ℍ → ℂ) (z : ℍ) : ℂ := (2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z

/-- We denote the normalized derivative by `D`. -/
scoped notation "D" => normalizedDerivOfComplex

/--
The derivative operator `D` preserves MDifferentiability.
If `F : ℍ → ℂ` is MDifferentiable, then `D F` is also MDifferentiable.
-/
theorem normalizedDerivOfComplex_mdifferentiable {F : ℍ → ℂ} (hF : MDiff F) : MDiff (D F) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hF ⊢
  let c : ℂ := (2 * π * I)⁻¹
  have hDeriv : DifferentiableOn ℂ (fun z ↦ c * deriv (F ∘ ofComplex) z) upperHalfPlaneSet := by
    simpa [c] using (hF.deriv isOpen_upperHalfPlaneSet).const_mul ((2 * π * I)⁻¹)
  refine hDeriv.congr ?_
  intro z hz
  simp [normalizedDerivOfComplex, c, Function.comp_apply, ofComplex_apply_of_im_pos hz]

/-!
Basic properties of normalized derivative.
-/
@[simp]
theorem normalizedDerivOfComplex_add (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    D (F + G) = D F + D G := by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  have hGz := UpperHalfPlane.mdifferentiableAt_iff.mp (hG z)
  simp only [normalizedDerivOfComplex, Pi.add_apply]
  rw [show (F + G) ∘ ofComplex = F ∘ ofComplex + G ∘ ofComplex from rfl,
    deriv_add hFz hGz, mul_add]

@[simp]
theorem normalizedDerivOfComplex_sub (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    D (F - G) = D F - D G := by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  have hGz := UpperHalfPlane.mdifferentiableAt_iff.mp (hG z)
  simp only [normalizedDerivOfComplex, Pi.sub_apply]
  rw [show (F - G) ∘ ofComplex = F ∘ ofComplex - G ∘ ofComplex from rfl,
    deriv_sub hFz hGz, mul_sub]

@[simp]
theorem normalizedDerivOfComplex_const (c : ℂ) : D (fun _ ↦ c) = 0 := by
  ext z
  change (2 * π * I)⁻¹ * deriv (fun _ : ℂ ↦ c) (z : ℂ) = 0
  simp [deriv_const]

@[simp]
theorem normalizedDerivOfComplex_smul (c : ℂ) (F : ℍ → ℂ) (hF : MDiff F) : D (c • F) = c • D F := by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  simp only [normalizedDerivOfComplex, Pi.smul_apply, smul_eq_mul]
  rw [show (c • F) ∘ ofComplex = c • (F ∘ ofComplex) from rfl,
    deriv_const_smul c hFz, smul_eq_mul]
  ring

@[simp]
theorem normalizedDerivOfComplex_neg (F : ℍ → ℂ) (hF : MDiff F) : D (-F) = -D F := by
  have : -F = (-1 : ℂ) • F := by ext; simp
  rw [this, normalizedDerivOfComplex_smul _ _ hF]
  ext
  simp

@[simp]
theorem normalizedDerivOfComplex_mul (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    D (F * G) = D F * G + F * D G := by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  have hGz := UpperHalfPlane.mdifferentiableAt_iff.mp (hG z)
  simp only [normalizedDerivOfComplex, Pi.add_apply, Pi.mul_apply]
  rw [show (F * G) ∘ ofComplex = (F ∘ ofComplex) * (G ∘ ofComplex) from rfl,
    deriv_mul hFz hGz]
  simp [Function.comp_apply, ofComplex_apply]
  ring

@[simp]
theorem normalizedDerivOfComplex_pow (F : ℍ → ℂ) (n : ℕ) (hF : MDiff F) :
    D (F ^ n) = n * F ^ (n - 1) * D F := by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  simp only [normalizedDerivOfComplex, Pi.mul_apply, Pi.pow_apply]
  rw [show (F ^ n) ∘ ofComplex = (F ∘ ofComplex) ^ n from rfl, deriv_pow hFz n]
  simp [Function.comp_apply, ofComplex_apply]
  ring

/--
Serre derivative of weight $k$.
-/
def serreDerivative (k : ℂ) (F : ℍ → ℂ) (z : ℍ) : ℂ :=
  D F z - k * 12⁻¹ * EisensteinSeries.E2 z * F z

@[simp]
lemma serreDerivative_apply (k : ℂ) (F : ℍ → ℂ) (z : ℍ) :
    serreDerivative k F z = D F z - k * 12⁻¹ * EisensteinSeries.E2 z * F z := rfl

@[simp]
lemma serreDerivative_eq (k : ℂ) (F : ℍ → ℂ) :
    serreDerivative k F = fun z ↦ D F z - k * 12⁻¹ * EisensteinSeries.E2 z * F z := rfl

/-!
Basic properties of Serre derivative.
-/
theorem serreDerivative_add (k : ℂ) (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    serreDerivative k (F + G) = serreDerivative k F + serreDerivative k G := by
  ext z
  simp [serreDerivative, normalizedDerivOfComplex_add F G hF hG]
  ring_nf

theorem serreDerivative_sub (k : ℂ) (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    serreDerivative k (F - G) = serreDerivative k F - serreDerivative k G := by
  ext z
  simp [serreDerivative, normalizedDerivOfComplex_sub F G hF hG]
  ring_nf

theorem serreDerivative_smul (k : ℂ) (c : ℂ) (F : ℍ → ℂ) (hF : MDiff F) :
    serreDerivative k (c • F) = c • (serreDerivative k F) := by
  ext z
  simp [serreDerivative, normalizedDerivOfComplex_smul c F hF, smul_eq_mul]
  ring_nf

theorem serreDerivative_mul (k₁ k₂ : ℂ) (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    serreDerivative (k₁ + k₂) (F * G) = (serreDerivative k₁ F) * G + F * (serreDerivative k₂ G)
    := by
  ext z
  simp [serreDerivative, normalizedDerivOfComplex_mul F G hF hG]
  ring_nf

/--
The Serre derivative preserves MDifferentiability.
If `F : ℍ → ℂ` is MDifferentiable, then `serreDerivative k F` is also MDifferentiable.
-/
theorem serreDerivative_mdifferentiable {F : ℍ → ℂ} (k : ℂ) (hF : MDiff F) :
    MDiff (serreDerivative k F) := by
  refine (normalizedDerivOfComplex_mdifferentiable hF).sub ?_
  convert
    (MDifferentiable.mul mdifferentiable_const (E2_mdifferentiable.mul hF) :
      MDiff (fun z ↦ (k * 12⁻¹) * (EisensteinSeries.E2 z * F z)))
  simp [Pi.mul_apply, mul_assoc, mul_left_comm, mul_comm]


open ModularGroup

variable (γ : SL(2, ℤ))

/-- Derivative of the denominator function: d/dz[cz + d] = c. -/
lemma deriv_denom (z : ℂ) :
    deriv (fun w => denom γ w) z = ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) := by
  simp only [denom]
  rw [deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one]; simp

/-- Derivative of the numerator function: d/dz[az + b] = a. -/
lemma deriv_num (z : ℂ) :
    deriv (fun w => num γ w) z = ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) := by
  simp only [num]
  rw [deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one]; simp

/-- Differentiability of denom. -/
lemma differentiableAt_denom (z : ℂ) :
    DifferentiableAt ℂ (fun w => denom γ w) z := by simp only [denom]; fun_prop

/-- Differentiability of num. -/
lemma differentiableAt_num (z : ℂ) :
    DifferentiableAt ℂ (fun w => num γ w) z := by simp only [num]; fun_prop

/-- Derivative of the Möbius transformation: d/dz[(az+b)/(cz+d)] = 1/(cz+d)².
Uses det(γ) = 1: a(cz+d) - c(az+b) = ad - bc = 1. -/
lemma deriv_moebius (z : ℍ) :
    deriv (fun w => num γ w / denom γ w) z = 1 / (denom γ z) ^ 2 := by
  have hz : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have hdet : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * (γ 1 1) -
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) * (γ 1 0) = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ
    simp only [Matrix.det_fin_two, ← Int.cast_mul, ← Int.cast_sub] at this ⊢
    exact_mod_cast this
  rw [deriv_fun_div (differentiableAt_num γ z) (differentiableAt_denom γ z) hz,
      deriv_num, deriv_denom]
  simp only [denom_apply, num, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom,
    Matrix.map_apply, ofReal_intCast] at *
  have hnum_eq : ((γ 0 0 : ℤ) : ℂ) * ((γ 1 0 : ℤ) * z + (γ 1 1 : ℤ)) -
      ((γ 0 0 : ℤ) * z + (γ 0 1 : ℤ)) * (γ 1 0 : ℤ) = 1 := by linear_combination hdet
  simp only [hnum_eq, one_div]

/-- Derivative of denom^(-k): d/dz[(cz+d)^(-k)] = -k * c * (cz+d)^(-k-1). -/
lemma deriv_denom_zpow (k : ℤ) (z : ℍ) :
    deriv (fun w => (denom γ w) ^ (-k)) z =
        (-k : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * (denom γ z) ^ (-k - 1) := by
  have hz : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have hd : HasDerivAt (fun w => denom γ w)
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) (z : ℂ) := by
    rw [← deriv_denom]; exact (differentiableAt_denom γ (z : ℂ)).hasDerivAt
  rw [show (fun w => (denom γ w) ^ (-k)) = (· ^ (-k)) ∘ (denom γ ·) from rfl,
    ((hasDerivAt_zpow (-k) _ (Or.inl hz)).comp _ hd).deriv]
  simp only [Int.cast_neg]; ring


/--
The derivative anomaly: how D interacts with the slash action.
This is the key computation for proving Serre derivative equivariance.
-/
lemma D_slash (k : ℤ) (F : ℍ → ℂ) (hF : MDiff F) (γ : SL(2, ℤ)) :
    D (F ∣[k] γ) = (D F ∣[k + 2] γ) -
        (fun z : ℍ => (k : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) * (F ∣[k] γ) z) := by
  ext z
  unfold normalizedDerivOfComplex
  simp only [Pi.sub_apply]
  have hz_denom_ne : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have hdet_pos : (0 : ℝ) < ((γ : GL (Fin 2) ℝ).det).val := by simp
  have hcomp : deriv (((F ∣[k] γ)) ∘ ofComplex) z =
      deriv (fun w => (F ∘ ofComplex) (num γ w / denom γ w) * (denom γ w) ^ (-k)) z := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw]
    rw [ModularForm.SL_slash_apply (f := F) (k := k) γ ⟨w, hw⟩]
    congr 1
    · let gz : ℍ := γ • ⟨w, hw⟩
      have hsmul : (gz : ℂ) = num γ w / denom γ w := by
        have h := UpperHalfPlane.coe_smul_of_det_pos hdet_pos ⟨w, hw⟩
        simp only [gz] at h ⊢; exact h
      have hmob_im : (num γ w / denom γ w).im > 0 := hsmul ▸ gz.im_pos
      congr 1; exact UpperHalfPlane.ext (by rw [ofComplex_apply_of_im_pos hmob_im]; exact hsmul)
  rw [hcomp]
  have hdenom_ne : ∀ w : ℂ, w.im > 0 → denom γ w ≠ 0 := fun w hw =>
    UpperHalfPlane.denom_ne_zero γ ⟨w, hw⟩
  have hdiff_mobius : DifferentiableAt ℂ (fun w => num γ w / denom γ w) z :=
    (differentiableAt_num γ z).div (differentiableAt_denom γ z) (hdenom_ne z z.im_pos)
  have hmob_eq : ↑(γ • z) = num γ z / denom γ z :=
    UpperHalfPlane.coe_smul_of_det_pos hdet_pos z
  have hdiff_F_comp : DifferentiableAt ℂ (F ∘ ofComplex) (num γ z / denom γ z) :=
    UpperHalfPlane.mdifferentiableAt_iff.mp (hF ⟨_, hmob_eq ▸ (γ • z).im_pos⟩)
  have hcomp_eq : (fun w => (F ∘ ofComplex) (num γ w / denom γ w)) =
      (F ∘ ofComplex) ∘ (fun w => num γ w / denom γ w) := rfl
  have hdiff_F_mobius : DifferentiableAt ℂ (fun w => (F ∘ ofComplex) (num γ w / denom γ w)) z := by
    rw [hcomp_eq]; exact hdiff_F_comp.comp (z : ℂ) hdiff_mobius
  -- Product rule, chain rule, and specific derivative formulas
  rw [show (fun w => (F ∘ ofComplex) (num γ w / denom γ w) * (denom γ w) ^ (-k)) =
      (fun w => (F ∘ ofComplex) (num γ w / denom γ w)) * (fun w => (denom γ w) ^ (-k)) from rfl,
    deriv_mul hdiff_F_mobius
      (.zpow (differentiableAt_denom γ z) (Or.inl (hdenom_ne z z.im_pos))),
    hcomp_eq, (hdiff_F_comp.hasDerivAt.comp (z : ℂ) hdiff_mobius.hasDerivAt).deriv,
    deriv_moebius, deriv_denom_zpow]
  simp only [ModularForm.SL_slash_apply, Function.comp_apply, ← hmob_eq, ofComplex_apply]
  -- Combine zpow terms
  have hpow1 : 1 / (denom γ z) ^ 2 * (denom γ z) ^ (-k) = (denom γ z) ^ (-(k + 2)) := by
    rw [one_div, ← zpow_natCast _ 2, ← zpow_neg, ← zpow_add₀ hz_denom_ne]; congr 1; ring
  have hpow2 : (denom γ z) ^ (-k - 1) = (denom γ z) ^ (-1 : ℤ) * (denom γ z) ^ (-k) := by
    rw [← zpow_add₀ hz_denom_ne]; congr 1; ring
  conv_lhs => rw [mul_assoc _ (1 / denom γ z ^ 2) _, hpow1, hpow2]
  simp only [zpow_neg_one]; ring

/--
Serre derivative is equivariant under the slash action. More precisely, if `F` is invariant
under the slash action of weight `k`, then `serreDerivative k F` is invariant under the slash action
of weight `k + 2`.
-/
theorem serreDerivative_slash_equivariant (k : ℤ) (F : ℍ → ℂ) (hF : MDiff F) :
    ∀ γ : SL(2, ℤ), serreDerivative k F ∣[k + 2] γ = serreDerivative k (F ∣[k] γ) := by
  intro γ
  ext z
  simp only [serreDerivative_apply]
  -- Rewrite LHS using mul_slash and serreDerivative definition
  have hLHS : (serreDerivative (k : ℂ) F ∣[k + 2] γ) z =
      (D F ∣[k + 2] γ) z - ↑k * 12⁻¹ * ((EisensteinSeries.E2 ∣[(2 : ℤ)] γ) z * (F ∣[k] γ) z) := by
    have h := congrFun (ModularForm.mul_slash_SL2 (2 : ℤ) k γ EisensteinSeries.E2 F) z
    simp only [Pi.mul_apply, show (2 : ℤ) + k = k + 2 from by omega] at h
    simp only [ModularForm.SL_slash_apply, serreDerivative_apply, Pi.mul_apply] at h ⊢
    rw [← h]; ring
  rw [hLHS]
  -- Substitute D slash and E2 slash action formulas pointwise
  have hDz := congrFun (D_slash k F hF γ) z
  have hE2z := congrFun (EisensteinSeries.E2_slash_action γ) z
  simp only [Pi.sub_apply] at hDz
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hE2z
  rw [hDz, hE2z]
  simp only [show EisensteinSeries.D2 γ z = (2 * ↑π * I * ↑↑(γ 1 0)) / denom γ ↑z from rfl,
    riemannZeta_two]
  field_simp [UpperHalfPlane.denom_ne_zero γ z, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring_nf; simp only [I_sq]; ring

theorem serreDerivative_slash_invariant (k : ℤ) (F : ℍ → ℂ) (hF : MDiff F)
    (γ : SL(2, ℤ)) (h : F ∣[k] γ = F) :
    serreDerivative k F ∣[k + 2] γ = serreDerivative k F := by
  rw [serreDerivative_slash_equivariant, h]
  exact hF


end

end Derivative
