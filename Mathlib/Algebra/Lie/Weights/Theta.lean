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

open scoped Nat

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

theorem rrr44 (t : Kˣ) : (t : K) ^ (2 : ℤ) = (t : K) * (t : K) := by
  have ssss : (t : K) ^ (2 : ℤ) = (t : K) ^ (2 : ℕ) := by
    norm_cast
  rw [ssss]
  exact pow_two (t : K)


theorem rrrrr2 (t : Kˣ) : ((t : K) ^ (2 : ℤ))⁻¹ * (t : K) = (t : K)⁻¹ := by
  have : (t : K) ≠ (0 : K) := by
    exact Units.ne_zero t
  field_simp
  rw [rrr44 t]
  simp_all only [ne_eq, Units.ne_zero, not_false_eq_true, mul_eq_zero, or_self, div_self]

  --search_proof

theorem theta_e (hα : α.IsNonZero) (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (- α)) (t : Kˣ)
    (ht : IsSl2Triple h e f) : theta H hα he hf t e = (-(t : K) ^ (-2 : ℤ) : K) • f := by
  rw [theta_apply]
  simp
  rw [exp_ad_e_e H hα he t]
  rw [exp_ad_f_e H hα hf t ht]
  --rw [exp_ad_e_apply]
  --simp [LinearMap.map_add]
  --apply LinearMap.map_add
  have ttt0 : (e + (t : K)⁻¹ • h) - ((t : K) ^ (-2 : ℤ) • f) = (e + (t : K)⁻¹ • h) + (- (t : K) ^ (-2 : ℤ) • f) := by
    simp_all only [Int.reduceNeg, zpow_neg, neg_smul]
    abel
  rw [ttt0]
  have ttt : (exp_ad_e H hα he t) ((e + (t : K)⁻¹ • h) + (- (t : K) ^ (-2 : ℤ) • f)) = (exp_ad_e H hα he t) (e + (t : K)⁻¹ • h) + (exp_ad_e H hα he t) (- (t : K) ^ (-2 : ℤ) • f) := by
    apply LinearMap.map_add
  rw [ttt]
  --have help : (t : K)⁻¹ = (t⁻¹ : K) := by
  --  field_simp
  --rw [help]
  have ttt2 : (exp_ad_e H hα he t) (e + (t : K)⁻¹ • h) = (exp_ad_e H hα he t) e + (exp_ad_e H hα he t) ((t : K)⁻¹ • h) := by
    apply LinearMap.map_add
  rw [ttt2]
  have ttt3 : (exp_ad_e H hα he t) ((t : K)⁻¹ • h) = (t : K)⁻¹ • ((exp_ad_e H hα he t) h) := by
    apply LinearMap.map_smul
  rw [ttt3]
  have ttt4 : (exp_ad_e H hα he t) (-(t : K) ^ (-2 : ℤ) • f) = -(t : K) ^ (-2 : ℤ) • ((exp_ad_e H hα he t) f) := by
    apply LinearMap.map_smul
  rw [ttt4]
  rw [exp_ad_e_e H hα he t]
  rw [exp_ad_e_f H hα he t ht]
  rw [exp_ad_e_h H hα he t ht]
  simp

  have s5 : (t : K)⁻¹ • (2 : ℤ) • (t : K) • e = 2 • e := by
    rw [two_smul, smul_add, ← add_smul]
    rw [add_smul]
    rw [← mul_smul]
    simp
    rw [two_smul]
  have s4 : e + (t : K)⁻¹ • (h - (2 : ℤ) • (t : K) • e) = (t : K)⁻¹ • h - e := by
    rw [smul_sub]
    rw [s5]
    abel
  rw [s4]
  rw [smul_sub]
  rw [smul_add]
  simp
  rw [← mul_smul]
  have : (t : K) ≠ (0 : K) := by
    exact Units.ne_zero t
  have rrrr : ((t : K) ^ (2 : ℤ))⁻¹ * (t : K) ^ 2 = 1 := by
    norm_cast
    field_simp
  rw [rrrr]
  simp
  rw [← mul_smul]
  rw [rrrrr2 t]
  simp















/-
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
      simp_all only [Units.val_inv_eq_inv_val, inv_pow, isUnit_iff_ne_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Units.ne_zero,
          IsUnit.inv_mul_cancel, one_smul]
    _ = - ⁅e, f⁆ := by
      rw [lie_skew]
    _ = - h := by
      rw [ht.lie_e_f]


-/




/-
lemma theta_apply {α : Weight K H L} {h e f : L} (hα : α.IsNonZero) (ht : IsSl2Triple h e f)
    (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (- α)) (t : Kˣ) : theta H hα ht he hf t =
      LieDerivation.exp (LieDerivation.instDerivation K L e)
        (LieAlgebra.isNilpotent_ad_of_mem_rootSpace H hα he) ∘
      LieDerivation.exp (LieDerivation.instDerivation K L f)
        (LieAlgebra.isNilpotent_ad_of_mem_rootSpace H (neg_ne_zero.mpr hα) hf) ∘
      LieDerivation.exp (LieDerivation.instDerivation K L e)
        (LieAlgebra.isNilpotent_ad_of_mem_rootSpace H hα he) := by
  ext x
  dsimp [theta]
-/

end Theta
