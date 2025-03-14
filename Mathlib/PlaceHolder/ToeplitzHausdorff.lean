-- This module serves as the root of the `ToeplitzHausdorff` library.
-- Import modules here that should be built as part of the library.
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Convex.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.Module.Defs

open Complex Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (A : Matrix n n ℂ)

def numericalRange (A : Matrix n n ℂ) : Set ℂ :=
  { z | ∃ x : EuclideanSpace ℂ n, ‖x‖ = 1 ∧ z = dotProduct (star x) (A.mulVec x) }

def convex_set (S : Set ℂ) : Prop :=
  ∀ (z1 z2: ℂ) (t : ℝ) , (z1 ∈ S) -> (z2 ∈ S) -> (0 <= t) -> (t <= 1) -> 
    (1 - t) * z1 + t * z2 ∈ S

open Classical

theorem toeplitz_hausdorff {A : Matrix n n ℂ} (hA : Aᴴ = A):
  convex_set (numericalRange A) := 
  by 
    intros z₁ z₂ t hz₁ hz₂ ht₀ ht
    obtain ⟨x₁, hx₁, hz₁'⟩ := hz₁
    obtain ⟨x₂, hx₂, hz₂'⟩ := hz₂

    let v := (1 - t) • x₁ + t • x₂
    by_cases hv : v = 0
    {
      have eq_v : (1 - t) • x₁ + t • x₂ = 0 := hv
      have eq_1 : (1 - t) • x₁ = -(t • x₂) := by 
        rw[add_eq_zero_iff_eq_neg] at eq_v; exact eq_v
      have norm_eq : ‖(1 - t) • x₁‖ = ‖-(t • x₂)‖ := congrArg (λ v => ‖v‖) eq_1
      rw [norm_smul, hx₁, norm_neg, norm_smul, hx₂, mul_one, mul_one] at norm_eq
      have h1t: 0 <= 1 - t  := sub_nonneg.mpr ht
      have rm_norm1 : ‖(1 - t)‖ = 1 - t := abs_of_nonneg h1t
      have rm_norm2: ‖t‖ = t := abs_of_nonneg ht₀
      rw [rm_norm1 , rm_norm2] at norm_eq
      have t_eq_half : t = 1/2 := by linarith
      rw [t_eq_half] at eq_1
      ring_nf at eq_1
      rw [←smul_neg, smul_right_inj (by norm_num)] at eq_1
      simp_all [numericalRange, hA]
      have z_eq : z₁ = z₂ := by
        calc
          z₁ = -(star x₂ ⬝ᵥ (A *ᵥ -x₂)) := hz₁'
          _ = star x₂ ⬝ᵥ - -(A *ᵥ x₂) := by rw [ ←mulVec_neg, dotProduct_neg]
          _ = star x₂ ⬝ᵥ A *ᵥ x₂ := by ring_nf
          _ = z₂ := by rw [hz₂']
      have conv_eq : (1-t)*z₁ + t*z₂ = z₁ := by
        rw [t_eq_half, z_eq]
        ring_nf
      use x₂
      simp_all [hx₂]
    }
    {
      let xₜ := ‖v‖⁻¹ • v
      use xₜ
      have h_norm : ‖‖v‖⁻¹ • v‖ = 1 := by
         simp [norm_smul, hv]
      simp_all
      have expand_xt : star xₜ ⬝ᵥA *ᵥxₜ = (star v ⬝ᵥA *ᵥv) / ‖v‖^2 := by 
        rw [star_smul, star_trivial, mulVec_smul, dotProduct_smul]
        field_simp [hv]
        ring_nf
        simp
      rw [expand_xt]
      have exp1 : star v ⬝ᵥ A *ᵥv =
        (1-t)^2 * (star x₁ ⬝ᵥ A *ᵥx₁)
        + t^2 * (star x₂ ⬝ᵥ A *ᵥ x₂)
        + t*(1-t)*(star x₁ ⬝ᵥ A *ᵥ x₂ + star x₂ ⬝ᵥ A *ᵥ x₁) := by
          simp [v] 
          rw [mulVec_add, mulVec_smul, mulVec_smul]
          rw [dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_smul, dotProduct_smul]
          simp
          ring_nf
      have exp2 : ‖v‖^2 = (1-t)^2 + t^2 + 2*t*(1-t)* (star x₁ ⬝ᵥ x₂) := by 
        norm_cast
        rw [norm_add_sq_real]
        rw [norm_smul, norm_smul] 
        rw [hx₁, hx₂]
        rw [Real.norm_eq_abs, Real.norm_eq_abs]
        rw [inner_smul_left, inner_smul_right]
        rw [starRingEnd_apply, star_trivial]
        rw [_root_.abs_of_nonneg (sub_nonneg.mpr ht), _root_.abs_of_nonneg  ht₀]
      have conv_eq : (star v ⬝ᵥ A *ᵥ v) / ‖v‖^2 = (1-t) * (star x₁ ⬝ᵥ A *ᵥ x₁) + t * (star x₂ ⬝ᵥ A *ᵥ x₂) := by
        rw [exp1, exp2]
        -- rw [star_dotProduct, star_mulVec, star_dotProduct, star_mulVec]
        sorry
    }
