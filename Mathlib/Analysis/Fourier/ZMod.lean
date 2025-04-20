/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Algebra.Group.EvenFunction
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.NumberTheory.DirichletCharacter.GaussSum

/-!
# Fourier theory on `ZMod N`

Basic definitions and properties of the discrete Fourier transform for functions on `ZMod N`
(taking values in an arbitrary `ℂ`-vector space).

### Main definitions and results

* `ZMod.dft`: the Fourier transform, with respect to the standard additive character
  `ZMod.stdAddChar` (mapping `j mod N` to `exp (2 * π * I * j / N)`). The notation `𝓕`, scoped in
  namespace `ZMod`, is available for this.
* `ZMod.dft_dft`: the Fourier inversion formula.
* `DirichletCharacter.fourierTransform_eq_inv_mul_gaussSum`: the discrete Fourier transform of a
  primitive Dirichlet character `χ` is a Gauss sum times `χ⁻¹`.
-/

open MeasureTheory Finset AddChar ZMod

namespace ZMod

variable {N : ℕ} [NeZero N] {E : Type*} [AddCommGroup E] [Module ℂ E]

section private_defs
/-
It doesn't _quite_ work to define the Fourier transform as a `LinearEquiv` in one go, because that
leads to annoying repetition between the proof fields. So we set up a private definition first,
prove a minimal set of lemmas about it, and then define the `LinearEquiv` using that.

**Do not add more lemmas about `auxDFT`**: it should be invisible to end-users.
-/

/--
The discrete Fourier transform on `ℤ / N ℤ` (with the counting measure). This definition is
private because it is superseded by the bundled `LinearEquiv` version.
-/
private noncomputable def auxDFT (Φ : ZMod N → E) (k : ZMod N) : E :=
  ∑ j : ZMod N, stdAddChar (-(j * k)) • Φ j

private lemma auxDFT_neg (Φ : ZMod N → E) : auxDFT (fun j ↦ Φ (-j)) = fun k ↦ auxDFT Φ (-k) := by
  ext1 k; simpa only [auxDFT] using
    Fintype.sum_equiv (Equiv.neg _) _ _ (fun j ↦ by rw [Equiv.neg_apply, neg_mul_neg])

/-- Fourier inversion formula, discrete case. -/
private lemma auxDFT_auxDFT (Φ : ZMod N → E) : auxDFT (auxDFT Φ) = fun j ↦ (N : ℂ) • Φ (-j) := by
  ext1 j
  simp only [auxDFT, mul_comm _ j, smul_sum, ← smul_assoc, smul_eq_mul, ← map_add_eq_mul, ←
    neg_add, ← add_mul]
  rw [sum_comm]
  simp only [← sum_smul, ← neg_mul]
  have h1 (t : ZMod N) : ∑ i, stdAddChar (t * i) = if t = 0 then ↑N else 0 := by
    split_ifs with h
    · simp only [h, zero_mul, map_zero_eq_one, sum_const, card_univ, card,
        nsmul_eq_mul, mul_one]
    · exact sum_eq_zero_of_ne_one (isPrimitive_stdAddChar N h)
  have h2 (x j : ZMod N) : -(j + x) = 0 ↔ x = -j := by
    rw [neg_add, add_comm, add_eq_zero_iff_neg_eq, neg_neg]
  simp only [h1, h2, ite_smul, zero_smul, sum_ite_eq', mem_univ, ite_true]

private lemma auxDFT_smul (c : ℂ) (Φ : ZMod N → E) :
    auxDFT (c • Φ) = c • auxDFT Φ := by
  ext; simp only [Pi.smul_def, auxDFT, smul_sum, smul_comm c]

end private_defs

section defs

/--
The discrete Fourier transform on `ℤ / N ℤ` (with the counting measure), bundled as a linear
equivalence. Denoted as `𝓕` within the `ZMod` namespace.
-/
noncomputable def dft : (ZMod N → E) ≃ₗ[ℂ] (ZMod N → E) where
  toFun := auxDFT
  map_add' Φ₁ Φ₂ := by
    ext; simp only [auxDFT, Pi.add_def, smul_add, sum_add_distrib]
  map_smul' c Φ := by
    ext; simp only [auxDFT, Pi.smul_apply, RingHom.id_apply, smul_sum, smul_comm c]
  invFun Φ k := (N : ℂ)⁻¹ • auxDFT Φ (-k)
  left_inv Φ := by
    simp only [auxDFT_auxDFT, neg_neg, ← mul_smul, inv_mul_cancel₀ (NeZero.ne _), one_smul]
  right_inv Φ := by
    ext1 j
    simp only [← Pi.smul_def, auxDFT_smul, auxDFT_neg, auxDFT_auxDFT, neg_neg, ← mul_smul,
      inv_mul_cancel₀ (NeZero.ne _), one_smul]

@[inherit_doc] scoped notation "𝓕" => dft

/-- The inverse Fourier transform on `ZMod N`. -/
scoped notation "𝓕⁻" => LinearEquiv.symm dft

lemma dft_apply (Φ : ZMod N → E) (k : ZMod N) :
    𝓕 Φ k = ∑ j : ZMod N, stdAddChar (-(j * k)) • Φ j :=
  rfl

lemma dft_def (Φ : ZMod N → E) :
    𝓕 Φ = fun k ↦ ∑ j : ZMod N, stdAddChar (-(j * k)) • Φ j :=
  rfl

lemma invDFT_apply (Ψ : ZMod N → E) (k : ZMod N) :
    𝓕⁻ Ψ k = (N : ℂ)⁻¹ • ∑ j : ZMod N, stdAddChar (j * k) • Ψ j := by
  simp only [dft, LinearEquiv.coe_symm_mk, auxDFT, mul_neg, neg_neg]

lemma invDFT_def (Ψ : ZMod N → E) :
    𝓕⁻ Ψ = fun k ↦ (N : ℂ)⁻¹ • ∑ j : ZMod N, stdAddChar (j * k) • Ψ j :=
  funext <| invDFT_apply Ψ

lemma invDFT_apply' (Ψ : ZMod N → E) (k : ZMod N) : 𝓕⁻ Ψ k = (N : ℂ)⁻¹ • 𝓕 Ψ (-k) :=
  rfl

lemma invDFT_def' (Ψ : ZMod N → E) : 𝓕⁻ Ψ = fun k ↦ (N : ℂ)⁻¹ • 𝓕 Ψ (-k) :=
  rfl

lemma dft_apply_zero (Φ : ZMod N → E) : 𝓕 Φ 0 = ∑ j, Φ j := by
  simp only [dft_apply, mul_zero, neg_zero, map_zero_eq_one, one_smul]

/--
The discrete Fourier transform agrees with the general one (assuming the target space is a complete
normed space).
-/
lemma dft_eq_fourier {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Φ : ZMod N → E) (k : ZMod N) :
    𝓕 Φ k = Fourier.fourierIntegral toCircle Measure.count Φ k := by
  simp only [dft_apply, stdAddChar_apply, Fourier.fourierIntegral_def, Circle.smul_def,
    integral_countable' <| .of_finite .., count_real_singleton, one_smul, tsum_fintype]

end defs

section arith
/-!
## Compatibility with scalar multiplication

These lemmas are more general than `LinearEquiv.map_mul` etc, since they allow any scalars that
commute with the `ℂ`-action, rather than just `ℂ` itself.
-/

lemma dft_const_smul {R : Type*} [DistribSMul R E] [SMulCommClass R ℂ E] (r : R) (Φ : ZMod N → E) :
    𝓕 (r • Φ) = r • 𝓕 Φ := by
  simp only [Pi.smul_def, dft_def, smul_sum, smul_comm]

lemma dft_smul_const {R : Type*} [Ring R] [Module ℂ R] [Module R E] [IsScalarTower ℂ R E]
    (Φ : ZMod N → R) (e : E) :
    𝓕 (fun j ↦ Φ j • e) = fun k ↦ 𝓕 Φ k • e := by
  simp only [dft_def, sum_smul, smul_assoc]

lemma dft_const_mul {R : Type*} [Ring R] [Algebra ℂ R] (r : R) (Φ : ZMod N → R) :
    𝓕 (fun j ↦ r * Φ j) = fun k ↦ r * 𝓕 Φ k :=
  dft_const_smul r Φ

lemma dft_mul_const {R : Type*} [Ring R] [Algebra ℂ R] (Φ : ZMod N → R) (r : R) :
    𝓕 (fun j ↦ Φ j * r) = fun k ↦ 𝓕 Φ k * r :=
  dft_smul_const Φ r

end arith

section inversion

lemma dft_comp_neg (Φ : ZMod N → E) : 𝓕 (fun j ↦ Φ (-j)) = fun k ↦ 𝓕 Φ (-k) :=
  auxDFT_neg ..

/-- Fourier inversion formula, discrete case. -/
lemma dft_dft (Φ : ZMod N → E) : 𝓕 (𝓕 Φ) = fun j ↦ (N : ℂ) • Φ (-j) :=
  auxDFT_auxDFT ..

end inversion

lemma dft_comp_unitMul (Φ : ZMod N → E) (u : (ZMod N)ˣ) (k : ZMod N) :
    𝓕 (fun j ↦ Φ (u.val * j)) k = 𝓕 Φ (u⁻¹.val * k) := by
  refine Fintype.sum_equiv u.mulLeft _ _ fun x ↦ ?_
  simp only [mul_comm u.val, u.mulLeft_apply, ← mul_assoc, u.mul_inv_cancel_right]

section signs

/-- The discrete Fourier transform of `Φ` is even if and only if `Φ` itself is. -/
lemma dft_even_iff {Φ : ZMod N → ℂ} : (𝓕 Φ).Even ↔ Φ.Even := by
  have h {f : ZMod N → ℂ} (hf : f.Even) : (𝓕 f).Even := by
    simp only [Function.Even, ← congr_fun (dft_comp_neg f), funext hf, implies_true]
  refine ⟨fun hΦ x ↦ ?_, h⟩
  simpa only [neg_neg, smul_right_inj (NeZero.ne (N : ℂ)), dft_dft] using h hΦ (-x)

/-- The discrete Fourier transform of `Φ` is odd if and only if `Φ` itself is. -/
lemma dft_odd_iff {Φ : ZMod N → ℂ} : (𝓕 Φ).Odd ↔ Φ.Odd := by
  have h {f : ZMod N → ℂ} (hf : f.Odd) : (𝓕 f).Odd := by
    simp only [Function.Odd, ← congr_fun (dft_comp_neg f), funext hf, ← Pi.neg_apply, map_neg,
      implies_true]
  refine ⟨fun hΦ x ↦ ?_, h⟩
  simpa only [neg_neg, dft_dft, ← smul_neg, smul_right_inj (NeZero.ne (N : ℂ))] using h hΦ (-x)

end signs

end ZMod

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

lemma fourierTransform_eq_gaussSum_mulShift (χ : DirichletCharacter ℂ N) (k : ZMod N) :
    𝓕 χ k = gaussSum χ (stdAddChar.mulShift (-k)) := by
  simp only [dft_apply, smul_eq_mul]
  congr 1 with j
  rw [mulShift_apply, mul_comm j, neg_mul, stdAddChar_apply, mul_comm (χ _)]

/-- For a primitive Dirichlet character `χ`, the Fourier transform of `χ` is a constant multiple
of `χ⁻¹` (and the constant is essentially the Gauss sum). -/
lemma IsPrimitive.fourierTransform_eq_inv_mul_gaussSum {χ : DirichletCharacter ℂ N}
    (hχ : IsPrimitive χ) (k : ZMod N) :
    𝓕 χ k = χ⁻¹ (-k) * gaussSum χ stdAddChar := by
  rw [fourierTransform_eq_gaussSum_mulShift, gaussSum_mulShift_of_isPrimitive _ hχ]

end DirichletCharacter
