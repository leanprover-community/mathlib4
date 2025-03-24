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

namespace Theta

open LieAlgebra

open LieModule

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

variable {h e f : L}

section AdAction

lemma pow_0_ad_e_e (t : Kˣ) : (((t : K) • (ad K L e)) ^ 0) e = e := rfl

lemma pow_1_ad_e_e (t : Kˣ) : (((t : K) • (ad K L e)) ^ 1) e = 0 := by
  rw [pow_one, LinearMap.smul_apply, ad_apply, lie_self, smul_zero]

lemma pow_0_ad_e_f (t : Kˣ) : (((t : K) • (ad K L e)) ^ 0) f = f := rfl

lemma pow_1_ad_e_f (t : Kˣ) (ht : IsSl2Triple h e f) :
  (((t : K) • (ad K L e)) ^ 1) f = (t : K) • h := by
  rw [pow_one, LinearMap.smul_apply, ad_apply, ht.lie_e_f]

lemma pow_2_ad_e_f (t : Kˣ) (ht : IsSl2Triple h e f) : (((t : K) • (ad K L e)) ^ 2) f =
    (-2 : ℤ) • (t : K) ^ 2 • e := by
  have h₁ : ((t : K) • ((t : K) • ((2 : ℕ) • e))) = 2 • (t : K) ^ 2 • e := by
    simp [two_smul]
    rw [← mul_smul]
    ring_nf
  calc
    (((t : K) • (ad K L e)) ^ 2) f = ((t : K) • (ad K L e)) ((((t : K) • (ad K L e)) ^ 1) f) := rfl
    _ = (-2 : ℤ) • (t : K) ^ 2 • e := by
      rw [pow_1_ad_e_f t ht, map_smul, LinearMap.smul_apply, ad_apply, neg_smul, ← lie_skew,
        ht.lie_h_e_nsmul]
      simp only [smul_neg, neg_inj]
      rw [h₁]
      exact (ofNat_smul_eq_nsmul ℤ 2 ((t : K) ^ 2 • e)).symm

lemma pow_3_ad_e_f (t : Kˣ) (ht : IsSl2Triple h e f) : (((t : K) • (ad K L e)) ^ 3) f = 0 := by
  calc
    (((t : K) • (ad K L e)) ^ 3) f = ((t : K) • (ad K L e)) ((((t : K) • (ad K L e)) ^ 2) f) := rfl
    _ = ((t : K) • (ad K L e)) ((-2 : ℤ) • ((t : K) ^ 2 • e)) := by
      rw [pow_2_ad_e_f t ht]
    _ = (-2 : ℤ) • (-(t : K) ^ 2) • (((t : K) • (ad K L e)) e) := by
      simp only [LinearMap.smul_apply, ad_apply, lie_neg, lie_smul, lie_self, smul_zero, neg_zero]
    _ = 0 := by
      simp only [LinearMap.smul_apply, ad_apply, lie_self, smul_zero]

end AdAction

variable (H : LieSubalgebra K L) [LieRing.IsNilpotent H] {α : Weight K H L} [CharZero K]
  [LieAlgebra ℚ L] [IsTriangularizable K H L] [FiniteDimensional K L]

section RootSpace

omit [CharZero K] [IsTriangularizable K H L] [FiniteDimensional K L] [LieAlgebra ℚ L]

lemma he' (t : Kˣ) (he : e ∈ rootSpace H α) : (t : K) • e ∈ rootSpace H α := by
  apply Submodule.smul_mem
  exact he

end RootSpace

section Nilpotent

omit [LieAlgebra ℚ L]

lemma nilpotent_e (t : Kˣ) (he : e ∈ rootSpace H α) (hα : α.IsNonZero) :
    IsNilpotent (t • (ad K L e)) := by
  have := LieAlgebra.isNilpotent_ad_of_mem_rootSpace H hα (he' H t he)
  rwa [LieHom.map_smul] at this

lemma nilpotent_e_map (t : Kˣ) (he : e ∈ rootSpace H α) (hα : α.IsNonZero) :
    IsNilpotent ((t : K) • (LieDerivation.ad K L e)).toLinearMap := by
  have := nilpotent_e H t he hα
  rwa [LieDerivation.coe_smul_linearMap, LieDerivation.coe_ad_apply_eq_ad_apply]

end Nilpotent

noncomputable def exp_ad_e (hα : α.IsNonZero) (he : e ∈ rootSpace H α) (t : Kˣ) : L ≃ₗ⁅K⁆ L := by
  exact LieDerivation.exp ((t : K) • (LieDerivation.ad K L e)) (nilpotent_e_map H t he hα)

lemma exp_ad_e_apply (hα : α.IsNonZero) (he : e ∈ rootSpace H α) (t : Kˣ) : exp_ad_e H hα he t =
    LieDerivation.exp ((t : K)  • LieDerivation.ad K L e) (nilpotent_e_map H t he hα) := by
  ext x
  convert rfl



/-
noncomputable def exp_ad_f (hα : α.IsNonZero) (hf : f ∈ rootSpace H (-α)) (t : Kˣ) : L ≃ₗ⁅K⁆ L := by
  let D := LieDerivation.instDerivation K L (-(t⁻¹ : K) • f)
  have hf' : -(t⁻¹ : K) • f ∈ rootSpace H (- α) := by
    apply Submodule.smul_mem
    exact hf
  have n₀ : ((- α) : H → K) ≠ 0 := neg_ne_zero.mpr hα
  exact LieDerivation.exp D (LieAlgebra.isNilpotent_ad_of_mem_rootSpace H n₀ hf')

noncomputable def theta (hα : α.IsNonZero) (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (- α))
    (t : Kˣ) : L ≃ₗ⁅K⁆ L := by
  exact ((exp_ad_e H hα he t).trans (exp_ad_f H hα hf t)).trans (exp_ad_e H hα he t)
-/

section ExpAdAction

open Finset

open scoped Nat


lemma exp_ad_e_e (hα : α.IsNonZero) (he : e ∈ rootSpace H α) (t : Kˣ) :
    (exp_ad_e H hα he t) e = e := by
  rw [exp_ad_e_apply, LieDerivation.exp_apply_apply ((t : K) • (LieDerivation.ad K L e))]
  have := IsNilpotent.exp_eq_sum' (M := L) (A := (Module.End K L)) (pow_1_ad_e_e t)
    (nilpotent_e H t he hα)
  simp only [LinearMap.one_apply, LieDerivation.coe_smul_linearMap,
    LieDerivation.coe_ad_apply_eq_ad_apply]
  simp only [range_one, sum_singleton] at this
  rwa [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul] at this

lemma exp_ad_e_f (hα : α.IsNonZero) (he : e ∈ rootSpace H α) (t : Kˣ) (ht : IsSl2Triple h e f) :
    (exp_ad_e H hα he t) f = f + (t : K) • h - ((t : K) ^ 2) • e := by
  rw [exp_ad_e_apply, LieDerivation.exp_apply_apply ((t : K) • (LieDerivation.ad K L e))]
  have := IsNilpotent.exp_eq_sum' (M := L) (A := (Module.End K L)) (pow_3_ad_e_f t ht)
    (nilpotent_e H t he hα)
  simp only [LinearMap.smul_def, smul_assoc] at this
  simp only [LieDerivation.coe_smul_linearMap, LieDerivation.coe_ad_apply_eq_ad_apply]
  rw [this, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, pow_0_ad_e_f t, pow_1_ad_e_f t ht, pow_2_ad_e_f t ht,
      Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, Nat.factorial_one, Nat.factorial_two]
  abel_nf
  refine (add_right_inj f).mpr ?_
  simp only [neg_smul, smul_neg, add_right_inj]
  rw [two_smul, smul_add, ← add_smul]
  field_simp

end ExpAdAction

/-
theorem theta_e {α : Weight K H L} {h e f : L} (hα : α.IsNonZero) (ht : IsSl2Triple h e f)
    (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (- α)) (t : Kˣ) :
      theta H hα ht he hf t e = ((t⁻¹ ^ 2) : K) • f := by
  sorry

theorem theta_f {α : Weight K H L} {h e f : L} (hα : α.IsNonZero) (ht : IsSl2Triple h e f)
    (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (- α)) (t : Kˣ) :
      theta H hα ht he hf t f = ((t ^ 2) : K) • e := by
  sorry

theorem theta_h {α : Weight K H L} {h e f : L} (hα : α.IsNonZero) (ht : IsSl2Triple h e f)
    (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (- α)) (t : Kˣ) :
      theta H hα ht he hf t h = - h := by
  calc
    theta H hα ht he hf t h = theta H hα ht he hf t ⁅e, f⁆ := by
      rw [ht.lie_e_f]
    _ = ⁅theta H hα ht he hf t e, theta H hα ht he hf t f⁆ := by
      apply LieHom.map_lie
    _ = ⁅((t⁻¹) ^ 2 : K) • f, (t ^ 2 : K) • e⁆ := by
      rw [theta_e H hα ht he hf t, theta_f H hα ht he hf t]
    _ = ((t⁻¹) ^ 2 : K) • ⁅f, (t ^ 2 : K) • e⁆ := by
      rw [smul_lie]
    _ = ((t⁻¹) ^ 2 : K) • (t ^ 2 : K) • ⁅f, e⁆ := by
      rw [lie_smul]
    _ = (((t⁻¹) ^ 2 : K) * (t ^ 2 : K)) • ⁅f, e⁆ := by
      simp
    _ = ⁅f, e⁆ := by
      simp_all only [Units.val_inv_eq_inv_val, inv_pow, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, pow_eq_zero_iff, Units.ne_zero, IsUnit.inv_mul_cancel, one_smul]
    _ = - ⁅e, f⁆ := by
      rw [lie_skew]
    _ = - h := by
      rw [ht.lie_e_f]


-/




/-
lemma theta_apply {α : Weight K H L} {h e f : L} (hα : α.IsNonZero) (ht : IsSl2Triple h e f)
    (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (- α)) (t : Kˣ) : theta H hα ht he hf t =
      LieDerivation.exp (LieDerivation.instDerivation K L e) (LieAlgebra.isNilpotent_ad_of_mem_rootSpace H hα he) ∘
      LieDerivation.exp (LieDerivation.instDerivation K L f) (LieAlgebra.isNilpotent_ad_of_mem_rootSpace H (neg_ne_zero.mpr hα) hf) ∘
      LieDerivation.exp (LieDerivation.instDerivation K L e) (LieAlgebra.isNilpotent_ad_of_mem_rootSpace H hα he) := by
  ext x
  dsimp [theta]
-/

end Theta
