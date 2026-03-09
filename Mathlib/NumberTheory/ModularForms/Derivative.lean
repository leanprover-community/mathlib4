/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable

open UpperHalfPlane hiding I
open Real Complex
open scoped Manifold

@[expose] public noncomputable section

/-!
# Derivatives of modular forms

This file defines normalized derivative $D = \frac{1}{2\pi i} \frac{d}{dz}$
and serre dervative $\partial_k := D - \frac{k}{12} E_2$ of modular forms.

TODO:
- Serre derivative preserves modularity, i.e. $\partial_k (M_k) \subseteq M_{k+2}$.
- Use above, prove Ramanujan's identities. See [here](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/main/SpherePacking/ModularForms/RamanujanIdentities.lean)
  for `sorry`-free proofs.
-/
@[expose] public noncomputable def D (F : ℍ → ℂ) : ℍ → ℂ :=
  fun (z : ℍ) => (2 * π * I)⁻¹ * ((deriv (F ∘ ofComplex)) z)

/--
The derivative operator `D` preserves MDifferentiability.
If `F : ℍ → ℂ` is MDifferentiable, then `D F` is also MDifferentiable.
-/
theorem D_differentiable {F : ℍ → ℂ} (hF : MDiff F) : MDiff (D F) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hF ⊢
  let c : ℂ := (2 * π * I)⁻¹
  have hDeriv : DifferentiableOn ℂ (fun z => c * deriv (F ∘ ofComplex) z) upperHalfPlaneSet := by
    simpa [c] using (hF.deriv isOpen_upperHalfPlaneSet).const_mul ((2 * π * I)⁻¹)
  refine hDeriv.congr ?_
  intro z hz
  simp [D, c, Function.comp_apply, ofComplex_apply_of_im_pos hz]

/--
Basic properties of derivatives: linearity, Leibniz rule, etc.
-/
@[simp]
theorem D_add (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    D (F + G) = D F + D G := by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  have hGz := UpperHalfPlane.mdifferentiableAt_iff.mp (hG z)
  simp only [D, Pi.add_apply]
  rw [show (F + G) ∘ ofComplex = F ∘ ofComplex + G ∘ ofComplex from rfl,
    deriv_add hFz hGz, mul_add]

@[simp]
theorem D_sub (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) : D (F - G) = D F - D G := by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  have hGz := UpperHalfPlane.mdifferentiableAt_iff.mp (hG z)
  simp only [D, Pi.sub_apply]
  rw [show (F - G) ∘ ofComplex = F ∘ ofComplex - G ∘ ofComplex from rfl,
    deriv_sub hFz hGz, mul_sub]

@[simp]
theorem D_smul (c : ℂ) (F : ℍ → ℂ) (hF : MDiff F) : D (c • F) = c • D F := by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  simp only [D, Pi.smul_apply, smul_eq_mul]
  rw [show (c • F) ∘ ofComplex = c • (F ∘ ofComplex) from rfl,
    deriv_const_smul c hFz, smul_eq_mul]
  ring

@[simp]
theorem D_neg (F : ℍ → ℂ) (hF : MDiff F) : D (-F) = -D F := by
  have : -F = (-1 : ℂ) • F := by ext; simp
  rw [this, D_smul _ _ hF]
  ext
  simp

@[simp]
theorem D_mul (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) : D (F * G) = D F * G + F * D G := by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  have hGz := UpperHalfPlane.mdifferentiableAt_iff.mp (hG z)
  simp only [D, Pi.add_apply, Pi.mul_apply]
  rw [show (F * G) ∘ ofComplex = (F ∘ ofComplex) * (G ∘ ofComplex) from rfl,
    deriv_mul hFz hGz]
  simp [Function.comp_apply, ofComplex_apply]
  ring


@[simp]
theorem D_sq (F : ℍ → ℂ) (hF : MDiff F) : D (F ^ 2) = 2 * F * D F := by
  rw [sq, D_mul F F hF hF]
  ext z
  simp only [Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply]
  ring

@[simp]
theorem D_const (c : ℂ) : D (Function.const _ c) = 0 := by
  ext z
  change (2 * π * I)⁻¹ * deriv (fun _ : ℂ => c) (z : ℂ) = 0
  simp [deriv_const]

/--
Serre derivative of weight $k$.
-/
@[expose] public noncomputable def SerreD (k : ℂ) (F : ℍ → ℂ) : ℍ → ℂ :=
  fun z => D F z - k * 12⁻¹ * EisensteinSeries.E2 z * F z

@[simp]
lemma SerreD_apply (k : ℂ) (F : ℍ → ℂ) (z : ℍ) :
    SerreD k F z = D F z - k * 12⁻¹ * EisensteinSeries.E2 z * F z := rfl

@[simp]
lemma SerreD_eq (k : ℂ) (F : ℍ → ℂ) :
    SerreD k F = fun z => D F z - k * 12⁻¹ * EisensteinSeries.E2 z * F z := rfl

/--
Basic properties of Serre derivative.
-/
@[simp]
theorem SerreD_add (k : ℂ) (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    SerreD k (F + G) = SerreD k F + SerreD k G := by
  ext z
  simp [SerreD, D_add F G hF hG]
  ring_nf

@[simp]
theorem SerreD_sub (k : ℂ) (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    SerreD k (F - G) = SerreD k F - SerreD k G := by
  ext z
  simp [SerreD, D_sub F G hF hG]
  ring_nf

@[simp]
theorem SerreD_smul (k : ℂ) (c : ℂ) (F : ℍ → ℂ) (hF : MDiff F) :
    SerreD k (c • F) = c • (SerreD k F) := by
  ext z
  simp [SerreD, D_smul c F hF, smul_eq_mul]
  ring_nf

@[simp]
theorem SerreD_mul (k₁ k₂ : ℂ) (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    SerreD (k₁ + k₂) (F * G) = (SerreD k₁ F) * G + F * (SerreD k₂ G) := by
  ext z
  simp [SerreD, D_mul F G hF hG]
  ring_nf

/--
The Serre derivative preserves MDifferentiability.
If `F : ℍ → ℂ` is MDifferentiable, then `SerreD k F` is also MDifferentiable.
-/
theorem SerreD_mdifferentiable {F : ℍ → ℂ} (k : ℂ) (hF : MDiff F) : MDiff (SerreD k F) := by
  refine (D_differentiable hF).sub ?_
  convert
    (MDifferentiable.mul mdifferentiable_const (E2_mdifferentiable.mul hF) :
      MDiff (fun z => (k * 12⁻¹) * (EisensteinSeries.E2 z * F z)))
  simp [Pi.mul_apply, mul_assoc, mul_left_comm, mul_comm]
