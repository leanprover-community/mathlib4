import Mathlib.Algebra.Lie.Weights.Killing
import Mathlib.LinearAlgebra.RootSystem.Basic
import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Field.Basic
import LeanCopilot

/-!
# Theta maps of Lie algebras

Text here please.

## Main definitions

  * `Theta`

## Tags

Tags here please.
-/

namespace LieAlgebra

namespace Theta

section AdAction

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] {h e f : L}

lemma pow_0_ad_e_e (t : Kˣ) : (((t : K) • (ad K L e)) ^ 0) e = e := rfl

lemma pow_1_ad_e_e (t : Kˣ) : (((t : K) • (ad K L e)) ^ 1) e = 0 := by
  rw [pow_one, LinearMap.smul_apply, ad_apply, lie_self, smul_zero]

lemma pow_0_ad_e_f (t : Kˣ) : (((t : K) • (ad K L e)) ^ 0) f = f := rfl

lemma pow_1_ad_e_f (t : Kˣ) (ht : IsSl2Triple h e f) :
  (((t : K) • (ad K L e)) ^ 1) f = (t : K) • h := by
  rw [pow_one, LinearMap.smul_apply, ad_apply, ht.lie_e_f]

lemma pow_2_ad_e_f (t : Kˣ) (ht : IsSl2Triple h e f) : (((t : K) • (ad K L e)) ^ 2) f =
    (-2 : ℤ) • (t : K) ^ 2 • e := by
  calc
    (((t : K) • (ad K L e)) ^ 2) f = ((t : K) • (ad K L e)) ((((t : K) • (ad K L e)) ^ 1) f) := rfl
    _ = (-2 : ℤ) • (t : K) ^ 2 • e := by
      rw [pow_1_ad_e_f t ht, map_smul, LinearMap.smul_apply, ad_apply, neg_smul, ← lie_skew,
        ht.lie_h_e_nsmul]
      simp only [smul_neg, two_smul, smul_add]
      rw [← mul_smul]
      ring_nf

lemma pow_3_ad_e_f (t : Kˣ) (ht : IsSl2Triple h e f) : (((t : K) • (ad K L e)) ^ 3) f = 0 := by
  calc
    (((t : K) • (ad K L e)) ^ 3) f = ((t : K) • (ad K L e)) ((((t : K) • (ad K L e)) ^ 2) f) := rfl
    _ = ((t : K) • (ad K L e)) ((-2 : ℤ) • ((t : K) ^ 2 • e)) := by
      rw [pow_2_ad_e_f t ht]
    _ = 0 := by
      simp only [LinearMap.smul_apply, ad_apply, lie_smul, lie_self, smul_zero]

lemma pow_0_ad_e_h (t : Kˣ) : (((t : K) • (ad K L e)) ^ 0) h = h := rfl

lemma pow_1_ad_e_h (t : Kˣ) (ht : IsSl2Triple h e f) : (((t : K) • (ad K L e)) ^ 1) h =
    (-2 : ℤ) • (t : K) • e := by
  rw [pow_one, LinearMap.smul_apply, ad_apply, ← lie_skew, ht.lie_h_e_nsmul]
  simp only [two_smul, smul_add, smul_neg, neg_smul]

lemma pow_2_ad_e_h (t : Kˣ) (ht : IsSl2Triple h e f) : (((t : K) • (ad K L e)) ^ 2) h = 0 := by
  calc
    (((t : K) • (ad K L e)) ^ 2) h = ((t : K) • (ad K L e)) ((((t : K) • (ad K L e)) ^ 1) h) := rfl
    _ = ((t : K) • (ad K L e)) ((-2 : ℤ) • (t : K) • e) := by
      rw [pow_1_ad_e_h t ht]
    _ = 0 := by
      simp only [LinearMap.smul_apply, ad_apply, lie_smul, lie_self, smul_zero]

lemma pow_0_ad_f_e (t : Kˣ) : ((-(t⁻¹ : K) • (ad K L f)) ^ 0) e = e := rfl

lemma pow_1_ad_f_e (t : Kˣ) (ht : IsSl2Triple h e f) :
  ((-(t⁻¹ : K) • (ad K L f)) ^ 1) e = (t⁻¹ : K) • h := by
  rw [pow_one, LinearMap.smul_apply, ad_apply, ← lie_skew, ht.lie_e_f, neg_smul_neg (t : K)⁻¹ h]

lemma pow_2_ad_f_e (t : Kˣ) (ht : IsSl2Triple h e f) : ((-(t⁻¹ : K) • (ad K L f)) ^ 2) e =
    (-2 : ℤ) • (t : K) ^ (-2 : ℤ) • f := by
  calc
    ((-(t⁻¹ : K) • (ad K L f)) ^ 2) e =
      (-(t⁻¹ : K) • (ad K L f)) (((-(t⁻¹ : K) • (ad K L f)) ^ 1) e) := rfl
    _ = (-2 : ℤ) • (t : K) ^ (-2 : ℤ) • f := by
      rw [pow_1_ad_f_e t ht, map_smul, LinearMap.smul_apply, ad_apply, neg_smul, ← lie_skew,
        ht.lie_h_f_nsmul]
      simp only [two_smul, neg_neg, smul_add, smul_neg, neg_smul]
      rw [← mul_smul]
      ring_nf
      norm_cast

lemma pow_3_ad_f_e (t : Kˣ) (ht : IsSl2Triple h e f) : ((-(t⁻¹ : K) • (ad K L f)) ^ 3) e = 0 := by
  calc
    ((-(t⁻¹ : K) • (ad K L f)) ^ 3) e = (-(t⁻¹ : K) • (ad K L f))
      (((-(t⁻¹ : K) • (ad K L f)) ^ 2) e) := rfl
    _ = (-(t⁻¹ : K) • (ad K L f)) ((-2 : ℤ) • (t : K) ^ (-2 : ℤ) • f) := by
      rw [pow_2_ad_f_e t ht]
    _ = 0 := by
      simp only [LinearMap.smul_apply, ad_apply, lie_smul, lie_self, smul_zero]

lemma pow_0_ad_f_f (t : Kˣ) : ((-(t⁻¹ : K) • (ad K L f)) ^ 0) f = f := rfl

lemma pow_1_ad_f_f (t : Kˣ) : ((-(t⁻¹ : K) • (ad K L f)) ^ 1) f = 0 := by
  rw [pow_one, LinearMap.smul_apply, ad_apply, lie_self, smul_zero]

lemma pow_0_ad_f_h (t : Kˣ) : ((-(t⁻¹ : K) • (ad K L f)) ^ 0) h = h := rfl

lemma pow_1_ad_f_h (t : Kˣ) (ht : IsSl2Triple h e f) : ((-(t⁻¹ : K) • (ad K L f)) ^ 1) h =
    (-2 : ℤ) • (t⁻¹ : K) • f := by
  rw [pow_one, LinearMap.smul_apply, ad_apply, ← lie_skew, ht.lie_h_f_nsmul]
  simp only [two_smul, neg_add_rev, neg_neg, smul_add, neg_smul]

lemma pow_2_ad_f_h (t : Kˣ) (ht : IsSl2Triple h e f) : ((-(t⁻¹ : K) • (ad K L f)) ^ 2) h = 0 := by
  calc
    ((-(t⁻¹ : K) • (ad K L f)) ^ 2) h = (-(t⁻¹ : K) • (ad K L f))
      (((-(t⁻¹ : K) • (ad K L f)) ^ 1) h) := rfl
    _ = (-(t⁻¹ : K) • (ad K L f)) ((-2 : ℤ) • (t⁻¹ : K) • f) := by
      rw [pow_1_ad_f_h t ht]
    _ = 0 := by
      simp only [LinearMap.smul_apply, ad_apply, lie_smul, lie_self, smul_zero]

end AdAction

section ThetaRootSpace

open LieModule

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] {h e f : L}
variable (H : LieSubalgebra K L) [LieRing.IsNilpotent H] {α : Weight K H L} [CharZero K]
  [LieAlgebra ℚ L] [IsTriangularizable K H L] [FiniteDimensional K L]

section Nilpotent

omit [LieAlgebra ℚ L]

lemma nilpotent_e (t : Kˣ) (he : e ∈ rootSpace H α) (hα : α.IsNonZero) :
    IsNilpotent (t • (ad K L e)) := by
  have he' : (t : K) • e ∈ rootSpace H α := by
    apply Submodule.smul_mem
    exact he
  have := LieAlgebra.isNilpotent_ad_of_mem_rootSpace H hα he'
  rwa [LieHom.map_smul] at this

lemma nilpotent_e_map (t : Kˣ) (he : e ∈ rootSpace H α) (hα : α.IsNonZero) :
    IsNilpotent ((t : K) • (LieDerivation.ad K L e)).toLinearMap := by
  have := nilpotent_e H t he hα
  rwa [LieDerivation.coe_smul_linearMap, LieDerivation.coe_ad_apply_eq_ad_apply]

lemma nilpotent_f (t : Kˣ) (hf : f ∈ rootSpace H (-α)) (hα : α.IsNonZero) :
    IsNilpotent (-(t⁻¹ : K) • (ad K L f)) := by
  have hf' : -(t⁻¹ : K) • f ∈ rootSpace H (-α) := by
    apply Submodule.smul_mem
    exact hf
  have := LieAlgebra.isNilpotent_ad_of_mem_rootSpace H (neg_ne_zero.mpr hα) hf'
  rwa [LieHom.map_smul] at this

lemma nilpotent_f_map (t : Kˣ) (hf : f ∈ rootSpace H (-α)) (hα : α.IsNonZero) :
    IsNilpotent (-(t⁻¹ : K) • (LieDerivation.ad K L f)).toLinearMap := by
  have := nilpotent_f H t hf hα
  rwa [LieDerivation.coe_smul_linearMap, LieDerivation.coe_ad_apply_eq_ad_apply]

end Nilpotent

section ExpAdAction

noncomputable def exp_ad_e (hα : α.IsNonZero) (he : e ∈ rootSpace H α) (t : Kˣ) : L ≃ₗ⁅K⁆ L := by
  exact LieDerivation.exp ((t : K) • (LieDerivation.ad K L e)) (nilpotent_e_map H t he hα)

lemma exp_ad_e_apply (hα : α.IsNonZero) (he : e ∈ rootSpace H α) (t : Kˣ) : exp_ad_e H hα he t =
    LieDerivation.exp ((t : K) • LieDerivation.ad K L e) (nilpotent_e_map H t he hα) := by
  ext x
  convert rfl

noncomputable def exp_ad_f (hα : α.IsNonZero) (hf : f ∈ rootSpace H (-α)) (t : Kˣ) : L ≃ₗ⁅K⁆ L := by
  exact LieDerivation.exp (-(t⁻¹ : K) • (LieDerivation.ad K L f)) (nilpotent_f_map H t hf hα)

lemma exp_ad_f_apply (hα : α.IsNonZero) (hf : f ∈ rootSpace H (-α)) (t : Kˣ) : exp_ad_f H hα hf t =
    LieDerivation.exp (-(t⁻¹ : K) • LieDerivation.ad K L f) (nilpotent_f_map H t hf hα) := by
  ext x
  convert rfl

open Finset

lemma exp_ad_e_e (hα : α.IsNonZero) (he : e ∈ rootSpace H α) (t : Kˣ) :
    (exp_ad_e H hα he t) e = e := by
  rw [exp_ad_e_apply, LieDerivation.exp_apply_apply ((t : K) • (LieDerivation.ad K L e))]
  have := IsNilpotent.exp_eq_sum_apply (M := L) (A := (Module.End K L)) (pow_1_ad_e_e t)
    (nilpotent_e H t he hα)
  simp only [LieDerivation.coe_smul_linearMap, LieDerivation.coe_ad_apply_eq_ad_apply]
  simp only [range_one, sum_singleton] at this
  rwa [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul] at this

lemma exp_ad_e_f (hα : α.IsNonZero) (he : e ∈ rootSpace H α) (t : Kˣ) (ht : IsSl2Triple h e f) :
    (exp_ad_e H hα he t) f = f + (t : K) • h - ((t : K) ^ 2) • e := by
  rw [exp_ad_e_apply, LieDerivation.exp_apply_apply ((t : K) • (LieDerivation.ad K L e))]
  have := IsNilpotent.exp_eq_sum_apply (M := L) (A := (Module.End K L)) (pow_3_ad_e_f t ht)
    (nilpotent_e H t he hα)
  simp only [LinearMap.smul_def, smul_assoc] at this
  simp only [LieDerivation.coe_smul_linearMap, LieDerivation.coe_ad_apply_eq_ad_apply]
  rw [this, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, pow_0_ad_e_f t, pow_1_ad_e_f t ht, pow_2_ad_e_f t ht,
      Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, Nat.factorial_one, Nat.factorial_two]
  abel_nf
  refine (add_right_inj f).mpr ?_
  simp only [neg_smul, smul_neg]
  rw [two_smul, smul_add, ← add_smul]
  field_simp

lemma exp_ad_e_h (hα : α.IsNonZero) (he : e ∈ rootSpace H α) (t : Kˣ) (ht : IsSl2Triple h e f) :
    (exp_ad_e H hα he t) h = h - (2 : ℤ) • (t : K) • e := by
  rw [exp_ad_e_apply, LieDerivation.exp_apply_apply ((t : K) • (LieDerivation.ad K L e))]
  have := IsNilpotent.exp_eq_sum_apply (M := L) (A := (Module.End K L)) (pow_2_ad_e_h t ht)
    (nilpotent_e H t he hα)
  simp only [LinearMap.smul_def, smul_assoc] at this
  simp only [LieDerivation.coe_smul_linearMap, LieDerivation.coe_ad_apply_eq_ad_apply]
  rw [this, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, pow_0_ad_e_h t, pow_1_ad_e_h t ht,
      Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, Nat.factorial_one]
  abel_nf
  refine (add_right_inj h).mpr ?_
  rw [Nat.cast_one, inv_one, neg_smul, smul_neg, one_smul]

lemma exp_ad_f_e (hα : α.IsNonZero) (hf : f ∈ rootSpace H (-α)) (t : Kˣ) (ht : IsSl2Triple h e f) :
    (exp_ad_f H hα hf t) e = e + (t⁻¹ : K) • h - (t : K) ^ (-2 : ℤ) • f := by
  rw [exp_ad_f_apply, LieDerivation.exp_apply_apply (-(t⁻¹ : K) • (LieDerivation.ad K L f))]
  have := IsNilpotent.exp_eq_sum_apply (M := L) (A := (Module.End K L)) (pow_3_ad_f_e t ht)
    (nilpotent_f H t hf hα)
  simp only [LinearMap.smul_def, smul_assoc] at this
  simp only [LieDerivation.coe_smul_linearMap, LieDerivation.coe_ad_apply_eq_ad_apply]
  rw [this, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, pow_0_ad_f_e t, pow_1_ad_f_e t ht, pow_2_ad_f_e t ht,
      Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, Nat.factorial_one, Nat.factorial_two]
  abel_nf
  refine (add_right_inj e).mpr ?_
  simp only [neg_smul, smul_neg]
  rw [two_smul, smul_add, ← add_smul]
  field_simp

lemma exp_ad_f_f (hα : α.IsNonZero) (hf : f ∈ rootSpace H (-α)) (t : Kˣ) :
    (exp_ad_f H hα hf t) f = f := by
  rw [exp_ad_f_apply, LieDerivation.exp_apply_apply (-(t⁻¹ : K) • (LieDerivation.ad K L f))]
  have := IsNilpotent.exp_eq_sum_apply (M := L) (A := (Module.End K L)) (pow_1_ad_f_f t)
    (nilpotent_f H t hf hα)
  simp only [LieDerivation.coe_smul_linearMap, LieDerivation.coe_ad_apply_eq_ad_apply]
  simp only [range_one, sum_singleton] at this
  rwa [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul] at this

lemma exp_ad_f_h (hα : α.IsNonZero) (hf : f ∈ rootSpace H (-α)) (t : Kˣ) (ht : IsSl2Triple h e f) :
    (exp_ad_f H hα hf t) h = h - (2 : ℤ) • (t⁻¹ : K) • f := by
  rw [exp_ad_f_apply, LieDerivation.exp_apply_apply (-(t⁻¹ : K) • (LieDerivation.ad K L f))]
  have := IsNilpotent.exp_eq_sum_apply (M := L) (A := (Module.End K L)) (pow_2_ad_f_h t ht)
    (nilpotent_f H t hf hα)
  simp only [LinearMap.smul_def, smul_assoc] at this
  simp only [LieDerivation.coe_smul_linearMap, LieDerivation.coe_ad_apply_eq_ad_apply]
  rw [this, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, pow_0_ad_f_h t, pow_1_ad_f_h t ht,
      Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, Nat.factorial_one]
  abel_nf
  refine (add_right_inj h).mpr ?_
  rw [Nat.cast_one, inv_one, neg_smul, smul_neg, one_smul]

end ExpAdAction

noncomputable def theta (hα : α.IsNonZero) (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (- α))
    (t : Kˣ) : L ≃ₗ⁅K⁆ L := by
  exact ((exp_ad_e H hα he t).trans (exp_ad_f H hα hf t)).trans (exp_ad_e H hα he t)

lemma theta_apply (hα : α.IsNonZero) (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (- α))
    (t : Kˣ) : theta H hα he hf t =
      ((exp_ad_e H hα he t) ∘ (exp_ad_f H hα hf t)) ∘ (exp_ad_e H hα he t) := by
  ext x
  rfl

theorem theta_eα (hα : α.IsNonZero) (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (- α)) (t : Kˣ)
    (ht : IsSl2Triple h e f) : theta H hα he hf t e = (-(t : K) ^ (-2 : ℤ) : K) • f := by
  dsimp [theta]
  rw [exp_ad_e_e H hα he t, exp_ad_f_e H hα hf t ht]
  have : (exp_ad_e H hα he t) ((e + (t : K)⁻¹ • h) - ((t : K) ^ (-2 : ℤ) • f)) =
      (exp_ad_e H hα he t) (e + (t : K)⁻¹ • h) - (exp_ad_e H hα he t) ((t : K) ^ (-2 : ℤ) • f) := by
    apply LinearMap.map_sub
  rw [this]
  have : (exp_ad_e H hα he t) (e + (t : K)⁻¹ • h) =
      (exp_ad_e H hα he t) e + (exp_ad_e H hα he t) ((t : K)⁻¹ • h) := by
    apply LinearMap.map_add
  rw [this]
  have : (exp_ad_e H hα he t) ((t : K)⁻¹ • h) = (t : K)⁻¹ • ((exp_ad_e H hα he t) h) := by
    apply LinearMap.map_smul
  rw [this]
  have fu₁ : ((t : K) ^ (2 : ℤ))⁻¹ * (t : K) ^ 2 = 1 := by
    norm_cast
    field_simp
  have fu₂ : ((t : K) ^ (2 : ℤ))⁻¹ * (t : K) = (t : K)⁻¹ := by
    have : (t : K) ^ (2 : ℤ) = (t : K) ^ (2 : ℕ) := by
      norm_cast
    rw [this, pow_two (t : K), mul_inv_rev, IsUnit.inv_mul_cancel_right]
    exact Units.isUnit t
  have : (exp_ad_e H hα he t) ((t : K) ^ (-2 : ℤ) • f) =
      (t : K) ^ (-2 : ℤ) • ((exp_ad_e H hα he t) f) := by
    apply LinearMap.map_smul
  rw [this, exp_ad_e_e H hα he t, exp_ad_e_f H hα he t ht, exp_ad_e_h H hα he t ht, smul_sub,
    two_smul, smul_add, ← add_smul, add_smul, ← mul_smul, add_sub, smul_sub, smul_add, ← mul_smul,
      ← mul_smul, zpow_neg, neg_smul, fu₁, fu₂, IsUnit.inv_mul_cancel, one_smul,
        add_sub_add_left_eq_sub, sub_sub_sub_cancel_right, sub_add_cancel_right]
  exact Units.isUnit t

theorem theta_fα (hα : α.IsNonZero) (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (- α)) (t : Kˣ)
    (ht : IsSl2Triple h e f) : theta H hα he hf t f = (-(t ^ (2 : ℤ)) : K) • e := by
  dsimp [theta]
  rw [exp_ad_e_f H hα he t ht]
  have : (exp_ad_f H hα hf t) (f + (t : K) • h - (t : K) ^ 2 • e) =
      (exp_ad_f H hα hf t) (f + (t : K) • h) - (exp_ad_f H hα hf t) ((t : K) ^ 2 • e) := by
    apply LinearMap.map_sub
  rw [this]
  have : (exp_ad_f H hα hf t) (f + (t : K) • h) =
      (exp_ad_f H hα hf t) f + (exp_ad_f H hα hf t) ((t : K) • h) := by
    apply LinearMap.map_add
  rw [this]
  have : (exp_ad_f H hα hf t) ((t : K) • h) = (t : K) • (exp_ad_f H hα hf t) h := by
    apply LinearMap.map_smul
  rw [this]
  have : (exp_ad_f H hα hf t) ((t : K) ^ 2 • e) = (t : K) ^ 2 • (exp_ad_f H hα hf t) e := by
    apply LinearMap.map_smul
  rw [this]
  rw [exp_ad_f_e H hα hf t ht, exp_ad_f_f H hα hf t, exp_ad_f_h H hα hf t ht, zpow_neg]
  have : f + (t : K) • (h - (2 : ℤ) • (t : K)⁻¹ • f) -
      (t : K) ^ 2 • (e + (t : K)⁻¹ • h - ((t : K) ^ (2 : ℤ))⁻¹ • f) = - (t : K) ^ 2 • e := by
    have h₁ : (t : K) ^ 2 * ((t : K) ^ (2 : ℤ))⁻¹ = 1 := by
      norm_cast
      field_simp
    have h₂ : (t : K) ^ 2 * (t : K)⁻¹ = (t : K) := by
      field_simp
      rw [pow_two (t : K)]
    have h₃ : ((t : K) • (2 : ℤ) • (t : K)⁻¹ • f) = 2 • f := by
      rw [two_smul, smul_add, ← mul_smul, two_smul, IsUnit.mul_inv_cancel, one_smul]
      exact Units.isUnit t
    rw [smul_sub, smul_sub, smul_add, neg_smul, ← mul_smul, ← mul_smul, h₁, h₂, add_sub, sub_sub,
      add_sub, h₃, two_smul, one_smul]
    abel
  rw [this]
  have : (exp_ad_e H hα he t) (-(t : K) ^ 2 • e) = -(t : K) ^ 2 • (exp_ad_e H hα he t) e := by
     apply LinearMap.map_smul
  rw [this, exp_ad_e_e H hα he t, neg_smul, neg_smul]
  norm_cast

theorem theta_hα (hα : α.IsNonZero) (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (- α)) (t : Kˣ)
    (ht : IsSl2Triple h e f) : theta H hα he hf t h = -h := by
  calc
    theta H hα he hf t h = theta H hα he hf t ⁅e, f⁆ := by
      rw [ht.lie_e_f]
    _ = ⁅theta H hα he hf t e, theta H hα he hf t f⁆ := by
      apply LieHom.map_lie
    _ = (((t : K) ^ (2 : ℤ))⁻¹ * (t : K) ^ (2 : ℤ)) • ⁅f, e⁆ := by
      rw [theta_eα H hα he hf t ht, theta_fα H hα he hf t ht, smul_lie, lie_smul, zpow_neg,
        neg_smul, ← smul_neg, neg_smul, neg_neg, mul_smul]
    _ = ⁅f, e⁆ := by
      norm_cast
      field_simp
    _ = - h := by
      rw [← lie_skew, ht.lie_e_f]

end ThetaRootSpace

section ThetaGeneral

open LieModule

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [IsKilling K L]
variable (H : LieSubalgebra K L) [H.IsCartanSubalgebra] {α : Weight K H L} [CharZero K]
  [LieAlgebra ℚ L] [IsTriangularizable K H L] [FiniteDimensional K L] {hα eα fα : L}

theorem theta_h_kerα {h : H} (hnz : α.IsNonZero) (heα : eα ∈ rootSpace H α)
    (hfα : fα ∈ rootSpace H (- α)) (t : Kˣ) (h₀ : h ∈ α.ker) : theta H hnz heα hfα t h = h := by
  have se₀ : ⁅eα, (h : L)⁆ = 0 := by
    have h₁ : α h = 0 := h₀
    have h₂ := IsKilling.lie_eq_smul_of_mem_rootSpace heα h
    rw [h₁, zero_smul] at h₂
    have : ⁅(h : L), eα⁆ = 0 := h₂
    rw [← lie_skew] at this
    exact neg_eq_zero.mp this
  have sf₀ : ⁅fα, (h : L)⁆ = 0 := by
    have h₁ : α h = 0 := h₀
    have h₂ := IsKilling.lie_eq_smul_of_mem_rootSpace hfα h
    simp only [LieSubalgebra.coe_bracket_of_module, Pi.neg_apply, neg_smul] at h₂
    rw [h₁, zero_smul] at h₂
    have : ⁅(h : L), fα⁆ = 0 := by
      rw [h₂, neg_zero]
    rw [← lie_skew] at this
    exact neg_eq_zero.mp this
  have se₁ :  (((t : K) • (ad K L eα)) ^ 1) h = 0 := by
    rw [pow_one, LinearMap.smul_apply, ad_apply, se₀, smul_zero]
  have sf₁ :  ((-(t⁻¹ : K) • (ad K L fα)) ^ 1) h = 0 := by
    rw [pow_one, LinearMap.smul_apply, ad_apply, sf₀, smul_zero]
  have se₂ : (exp_ad_e H hnz heα t) h = h := by
    rw [exp_ad_e_apply,  LieDerivation.exp_apply_apply ((t : K) • (LieDerivation.ad K L eα))]
    have := IsNilpotent.exp_eq_sum_apply (M := L) (A := (Module.End K L)) se₁
      (nilpotent_e H t heα hnz)
    simp only [LinearMap.smul_def, smul_assoc] at this
    simp only [LieDerivation.coe_smul_linearMap, LieDerivation.coe_ad_apply_eq_ad_apply]
    rw [this, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_0_ad_e_h t,
        Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
  have sf₂ : (exp_ad_f H hnz hfα t) h = h := by
    rw [exp_ad_f_apply,  LieDerivation.exp_apply_apply (-(t⁻¹ : K) • (LieDerivation.ad K L fα))]
    have := IsNilpotent.exp_eq_sum_apply (M := L) (A := (Module.End K L)) sf₁
      (nilpotent_f H t hfα hnz)
    simp only [LinearMap.smul_def, smul_assoc] at this
    simp only [LieDerivation.coe_smul_linearMap, LieDerivation.coe_ad_apply_eq_ad_apply]
    rw [this, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_0_ad_f_h t,
        Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
  dsimp [theta]
  rw [se₂, sf₂, se₂]

theorem theta_h (hnz : α.IsNonZero) (heα : eα ∈ rootSpace H α) (hfα : fα ∈ rootSpace H (- α))
    (t : Kˣ) (ht : IsSl2Triple hα eα fα) (h : H) : theta H hnz heα hfα t h = h - (α h) • hα  := by
  have hef := IsKilling.lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg heα hfα
  lift hα to H using by simpa only [← ht.lie_e_f, hef] using H.smul_mem _ (Submodule.coe_mem _)
  obtain ⟨⟨h_ker, h₀⟩, ⟨⟨dir, h₁⟩, ⟨hsum, _⟩⟩⟩ :=
    Submodule.existsUnique_add_of_isCompl (IsKilling.isCompl_ker_weight_span_coroot α) h
  obtain ⟨k, h_dir⟩ := Submodule.mem_span_singleton.mp h₁
  norm_cast at hsum
  rw [h_dir.symm] at hsum
  have cor := _root_.IsSl2Triple.h_eq_coroot hnz ht heα hfα
  rw [SetLike.coe_eq_coe] at cor
  rw [← cor] at hsum
  rw [← hsum]
  have : (theta H hnz heα hfα t) ((h_ker + (k • hα : L)) : L) =
      (theta H hnz heα hfα t) h_ker + (theta H hnz heα hfα t) (k • hα) := by
    apply LinearMap.map_add
  erw [this]
  have : (theta H hnz heα hfα t) (k • hα) = k • theta H hnz heα hfα t hα := by
     apply LinearMap.map_smul
  rw [theta_h_kerα H hnz heα hfα t h₀, this, theta_hα H hnz heα hfα t ht]
  have := IsKilling.root_apply_coroot hnz
  rw [cor.symm] at this
  rw [smul_neg, map_add, map_smul, smul_eq_mul, this, add_smul]
  norm_cast
  have : α h_ker = 0 := h₀
  rw [this, mul_smul, two_smul, smul_add, ← add_assoc, zero_smul, zero_add,
    add_sub_add_right_eq_sub, sub_eq_add_neg]

theorem theta_pow_2 (hnz : α.IsNonZero) (heα : eα ∈ rootSpace H α) (hfα : fα ∈ rootSpace H (- α))
    (t : Kˣ) (ht : IsSl2Triple hα eα fα) (h : H) :
      theta H hnz heα hfα t (theta H hnz heα hfα t h) = h := by
  rw [theta_h H hnz heα hfα t ht h]
  have : (theta H hnz heα hfα t) (h - α h • hα) =
      theta H hnz heα hfα t h - theta H hnz heα hfα t (α h • hα) := by
    apply LinearMap.map_sub
  rw [this]
  have : (theta H hnz heα hfα t) (α h • hα) = α h • (theta H hnz heα hfα t hα) := by
    apply LinearMap.map_smul
  rw [this, theta_h H hnz heα hfα t ht h, theta_hα H hnz heα hfα t ht, smul_neg, sub_neg_eq_add,
    sub_add_cancel]

theorem theta_act {x : L} {β : Weight K H L} (hnz : α.IsNonZero) (heα : eα ∈ rootSpace H α)
    (hfα : fα ∈ rootSpace H (- α)) (t : Kˣ) (ht : IsSl2Triple hα eα fα) (hx : x ∈ rootSpace H β) :
      (theta H hnz heα hfα t) x ∈ rootSpace H (β - β (IsKilling.coroot α) • α) := by
  have hef := IsKilling.lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg heα hfα
  lift hα to H using by simpa only [← ht.lie_e_f, hef] using H.smul_mem _ (Submodule.coe_mem _)
  have key : ∀ (h : H), ⁅h, (theta H hnz heα hfα t) x⁆ =
      ((β - β (IsKilling.coroot α) • α : H → K) h) • ((theta H hnz heα hfα t) x) := by
    intro h
    have hh := theta_pow_2 H hnz heα hfα t ht h
    have : ⁅h, (theta H hnz heα hfα t) x⁆ = ⁅(theta H hnz heα hfα t) ((theta H hnz heα hfα t) h), (theta H hnz heα hfα t) x⁆ := by
      rw [hh]
      simp
    rw [this]
    have : ⁅(theta H hnz heα hfα t) ((theta H hnz heα hfα t) h), (theta H hnz heα hfα t) x⁆ =
        (theta H hnz heα hfα t) ⁅((theta H hnz heα hfα t) h), x⁆ := by
      exact Eq.symm (LieEquiv.map_lie (theta H hnz heα hfα t) ((theta H hnz heα hfα t) ↑h) x)
    rw [this]
    rw [theta_h H hnz heα hfα t ht h]
    have := IsKilling.lie_eq_smul_of_mem_rootSpace hx (h - α h • hα)
    have zzz : (theta H hnz heα hfα t) ⁅h - α h • hα, x⁆ = (theta H hnz heα hfα t) (β (h - α h • hα) • x) := by
      rw [this]
    erw [zzz]
    have : (theta H hnz heα hfα t) (β (h - α h • hα) • x) = β (h - α h • hα) • ((theta H hnz heα hfα t) x) := by
      apply LinearMap.map_smul
    rw [this]
    have cor := _root_.IsSl2Triple.h_eq_coroot hnz ht heα hfα
    rw [SetLike.coe_eq_coe] at cor
    rw [cor.symm]
    simp
    have : (β h - α h * β hα) = (β h - β hα * α h) := by
      rw [mul_comm]
    rw [this]
  simp at key
  have := (mem_genWeightSpace (L := H) (R := K) L (β - β (IsKilling.coroot α) • α)
    ((theta H hnz heα hfα t) x)).2
  apply this
  intro h
  obtain ⟨aa, bb⟩ := h
  use 1
  simp
  have := key aa bb
  rw [this.symm]
  simp

end ThetaGeneral

end Theta

end LieAlgebra
