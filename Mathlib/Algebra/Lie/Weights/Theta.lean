import Mathlib.Algebra.Lie.Weights.Killing
import Mathlib.LinearAlgebra.RootSystem.Basic
import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
import Mathlib.Algebra.Algebra.Rat
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

open LieModule

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [Module ℚ L]
  (H : LieSubalgebra K L) [LieRing.IsNilpotent H]
  [IsTriangularizable K H L] [FiniteDimensional K L]

variable {α : Weight K H L} {h e f : L}

lemma he' (t : Kˣ) (he : e ∈ rootSpace H α) : (t : K) • e ∈ rootSpace H α := by
  apply Submodule.smul_mem
  exact he

lemma nil (t : Kˣ) (he : e ∈ rootSpace H α) (hα : α.IsNonZero) : IsNilpotent ((LieDerivation.ad K L) (t • e)).toLinearMap := by
  simp_all
  have ttt := LieAlgebra.isNilpotent_ad_of_mem_rootSpace H hα (he' H t he)
  simp_all only [LieHom.map_smul]
  sorry

lemma nil2 (t : Kˣ) (he : e ∈ rootSpace H α) (hα : α.IsNonZero) : IsNilpotent ((t : K) • (LieDerivation.ad K L) (e)).toLinearMap := by
  --simp_all
  have ttt := LieAlgebra.isNilpotent_ad_of_mem_rootSpace H hα (he' H t he)
  simp_all only [LieHom.map_smul]
  simp_all only [LieDerivation.coe_smul_linearMap, LieDerivation.coe_ad_apply_eq_ad_apply]

noncomputable def exp_ad_e (hα : α.IsNonZero) (he : e ∈ rootSpace H α) (t : Kˣ) : L ≃ₗ⁅K⁆ L := by
  exact LieDerivation.exp (LieDerivation.ad K L ((t : K) • e)) (nil H t he hα)



lemma exp_ad_e_apply (hα : α.IsNonZero) (he : e ∈ rootSpace H α) (t : Kˣ) :
    exp_ad_e H hα he t = LieDerivation.exp (LieDerivation.ad K L ((t : K) • e)) (nil H t he hα) := by
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


open Finset
open scoped Nat


noncomputable def nilpo (t : Kˣ) (e : L) : ℕ := nilpotencyClass (t • (ad K L) e)

lemma pow_0_ad_e_f (t : Kˣ) (ht : IsSl2Triple h e f) :
  ((0 : ℕ).factorial : ℚ)⁻¹ • (((t : K) • (ad K L) e) ^ 0) f = f := by
  simp

lemma pow_1_ad_e_f (t : Kˣ) (ht : IsSl2Triple h e f) :
  ((1 : ℕ).factorial : ℚ)⁻¹ • (((t : K) • (ad K L) e) ^ 1) f = (t : K) • h := by
  simp
  rw [ht.lie_e_f]

lemma pow_2_ad_e_f (t : Kˣ) (ht : IsSl2Triple h e f) :
  ((2 : ℕ).factorial : ℚ)⁻¹ • (((t : K) • (ad K L) e) ^ 2) f = -(t : K) ^ 2 • e := by
  simp
  have mi : ((t : K) * (t : K)) • 2 • e = 2 • ((t : K) * (t : K)) • e := by
    sorry

  have hhhh : ((2 : ℕ).factorial : ℚ)⁻¹ • ((t : K) • ((t : K) • -((2 : ℚ) • e))) = -(t : K) ^ 2 • e := by
    simp
    rw [← mul_smul]

    --norm_cast
    --simp



    have hhhhh: ((2 : ℕ).factorial : ℚ)⁻¹ • ((t : K) • ((t : K) • (-((2 : ℚ) • e)))) = (((2 : ℕ).factorial : ℚ)⁻¹ * (t : K)) • ((t : K) • -((2 : ℚ)  • e)) := by
      --nth_rewrite 1 [← mul_smul]
      simp




  calc
  ((2 : ℕ).factorial : ℚ)⁻¹ • (((t : K) • (ad K L) e) ^ 2) f = ((2 : ℕ).factorial : ℚ)⁻¹ • ((t : K) • (ad K L) e) (((t : K) • (ad K L) e) f) := by
    exact rfl
  _ = ((2 : ℕ).factorial : ℚ)⁻¹ • ((t : K) • (ad K L) e) (((1 : ℕ).factorial : ℚ)⁻¹ • (((t : K) • (ad K L) e) ^ 1) f) := by
    sorry
  _ = ((2 : ℕ).factorial : ℚ)⁻¹ • ((t : K) • (ad K L) e) ((t : K) • h) := by rw [pow_1_ad_e_f t ht]
  _ = -(t : K) ^ 2 • e := by
    simp
    rw [← lie_skew]
    rw [ht.lie_h_e_nsmul]
    --search_proof




lemma exp_ad_e_f (hα : α.IsNonZero) (he : e ∈ rootSpace H α) (t : Kˣ) (ht : IsSl2Triple h e f) :
    (exp_ad_e H hα he t) f = f + h - e := by
  rw [exp_ad_e_apply]
  simp
  have ttt := LieDerivation.exp_apply ((t : K) • (LieDerivation.ad K L) e) (nil2 H t he hα)

  have ttt2 : ((t : K) • (LieDerivation.ad K L) e).exp (nil2 H t he hα) f = IsNilpotent.exp ((t : K) • (LieDerivation.ad K L) e).toLinearMap f := by
    apply LieDerivation.exp_apply_apply ((t : K) • (LieDerivation.ad K L) e) (nil2 H t he hα) f

  rw [ttt2]
  have tttt : (((t : K) • (ad K L e)) ^ 3) f = 0 := by
    sorry
  have sss := IsNilpotent.exp_eq_sum' (M := L) (A := (Module.End K L)) tttt
  simp_all only [LieDerivation.coe_smul_linearMap, LieDerivation.coe_ad_apply_eq_ad_apply,
    LinearMap.smul_def, smul_assoc]
  have unf : ∑ x ∈ range 3, (x.factorial : ℚ)⁻¹ • (((t : K) • (ad K L) e) ^ x) f =
      ((0 : ℕ).factorial : ℚ)⁻¹ • (((t : K) • (ad K L) e) ^ 0) f +
      ((1 : ℕ).factorial : ℚ)⁻¹ • (((t : K) • (ad K L) e) ^ 1) f +
      ((2 : ℕ).factorial : ℚ)⁻¹ • (((t : K) • (ad K L) e) ^ 2) f := by
    rw [Finset.sum_range_succ]
    rw [Finset.sum_range_succ]
    rw [Finset.sum_range_succ]
    rw [Finset.sum_range_zero]
    simp_all only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, LinearMap.one_apply, one_smul, zero_add,
      Nat.factorial_one, pow_one, LinearMap.smul_apply, ad_apply, Nat.factorial_two, Nat.cast_ofNat]
  rw [unf]


  --rw [sss]

  /-
  dsimp [IsNilpotent.exp]
  have ttt : (((ad K L ((t : K) • e))) ^ 3) e = 0 := by
    sorry
  --simp [toLinearMap]
  --simp
  --unfold IsNilpotent.exp
  --simp [LieEquiv]

  simp
  let n := nilpotencyClass (t • (ad K L) e)
  let A := ∑ x ∈ Finset.range n, ((x.factorial : ℚ) : K)⁻¹ • ((t • (ad K L) e) ^ x)
  search_proof
  --apply IsNilpotent.exp_eq_sum' ttt
  -/

  sorry

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

end LieAlgebra
