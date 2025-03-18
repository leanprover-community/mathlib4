-- This module serves as the root of the `ToeplitzHausdorff` library.
-- Import modules here that should be built as part of the library.
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Convex.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Rayleigh

open Complex Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (A : Matrix n n ℂ)

def numericalRange (A : Matrix n n ℂ) : Set ℂ :=
  { z | ∃ x : EuclideanSpace ℂ n, ‖x‖ = 1 ∧ z = dotProduct (star x) (A.mulVec x) }

def convex_set (S : Set ℂ) : Prop :=
  ∀ (z1 z2: ℂ) (t : ℝ) , (z1 ∈ S) -> (z2 ∈ S) -> (0 <= t) -> (t <= 1) -> 
    (1 - t) * z1 + t * z2 ∈ S

open Classical

lemma sum_complex_star {n : Type*} [Fintype n] (x₁ x₂ : n → ℂ) :
  ∑ x : n, ( (x₂ x).re * (x₁ x).re + (x₂ x).im * (x₁ x).im )
  = (∑ i, (star (x₁ i) * x₂ i)).re := by
    have h : ∀ i, (x₂ i).re * (x₁ i).re + (x₂ i).im * (x₁ i).im = (star (x₁ i) * x₂ i).re := by
      intro i
      simp
      ring_nf
    simp_rw [h]
    simp [Complex.re_sum]



theorem toeplitz_hausdorff {A : Matrix n n ℂ} (hA : Aᴴ = A):
  -- TODO use Convex rather than convex_set
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
      have norm_eq : ‖(1 - t) • x₁‖ = ‖-(t • x₂)‖ := congrArg (fun v => ‖v‖) eq_1
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

      -- We can go ahead and define the quadratic form of the norm of v to use its properties
      have expand_xt : star xₜ ⬝ᵥA *ᵥxₜ = (star v ⬝ᵥA *ᵥv) / ‖v‖^2 := by 
        rw [star_smul, star_trivial, mulVec_smul, dotProduct_smul]
        field_simp [hv]
        ring_nf
        simp

      rw [expand_xt]

      -- Rewrite qudratic form of the numerator using our unit vectors and t
      have exp1 : star v ⬝ᵥ A *ᵥv =
        (1-t)^2 * (star x₁ ⬝ᵥ A *ᵥx₁)
        + t^2 * (star x₂ ⬝ᵥ A *ᵥ x₂)
        + t*(1-t)*(star x₁ ⬝ᵥ A *ᵥ x₂ + star x₂ ⬝ᵥ A *ᵥ x₁) := by
          simp [v] 
          rw [mulVec_add, mulVec_smul, mulVec_smul]
          rw [dotProduct_add, dotProduct_add, dotProduct_smul]
          rw [dotProduct_smul, dotProduct_smul, dotProduct_smul]
          simp
          ring_nf

      -- Rewrite qudratic form of the denominator using our unit vectors and t
      have exp2 : ‖v‖^2 = (1-t)^2 + t^2 + 2*t*(1-t)* (star x₁ ⬝ᵥ x₂).re := by
        norm_cast at *
        rw [norm_add_sq_real]
        rw [norm_smul, norm_smul] 
        rw [Real.norm_eq_abs, Real.norm_eq_abs]
        rw [hx₁, hx₂]
        rw [inner_smul_left, inner_smul_right]
        rw [starRingEnd_apply, star_trivial]
        rw [_root_.abs_of_nonneg (sub_nonneg.mpr ht), _root_.abs_of_nonneg  ht₀]
        simp
        rw [sum_complex_star]
        simp [dotProduct]
        ring_nf
        
      -- using the expansion of the numerator and the denominator,
      -- simplify the quadratic form of the norm of v
      have conv_eq : (star v ⬝ᵥ A *ᵥ v) / ‖v‖^2 = 
        (1-t) * (star x₁ ⬝ᵥ A *ᵥ x₁) + t * (star x₂ ⬝ᵥ A *ᵥ x₂) := by
         
        have H : ((1 : ℂ) - ↑t)^2 + ↑t^2 + 2 * ↑t * (1 - ↑t) * ↑(star x₁ ⬝ᵥ x₂).re ≠ 0 := by
          intro h
          simp_all
          sorry

        have rhA : A = Aᴴ := by simp [hA]


        
        norm_cast
        rw [exp1, exp2]
        rw [←hz₁', ←hz₂'] 
        simp

        let first_term := star x₁ ⬝ᵥ A *ᵥ x₂
        let second_term := star x₂ ⬝ᵥ A *ᵥ x₁


        have h_cross : first_term + second_term = 2 * (first_term).re := by
          have symm : second_term = star first_term := by
            unfold first_term second_term
            conv =>
              lhs;
              rw [dotProduct_mulVec, rhA, vecMul_conjTranspose, star_dotProduct]
            simp
          simp [symm] 
          rw [re_eq_add_conj]
          ring_nf

        rw [h_cross]

        -- pull the two out of the numerator
        conv_lhs =>
          pattern (_ * (2 * _ ))
          rw [mul_comm]
        
        apply div_eq_of_eq_mul H
        -- ring_nf
        rw [exp2]
        -- stuck here
        
        sorry 


        
        -- have h_expanded : ((1 - ↑t) * z₁ + ↑t * z₂) * 
        --   ((1 - ↑t) ^ 2 + ↑t ^ 2 + 2 * ↑t * (1 - ↑t) * ↑(star x₁ ⬝ᵥ x₂).re) = 
        --   (1 - ↑t) ^ 3 * z₁ 
        -- + (1 - ↑t) * ↑t^2 * z₁ 
        -- + 2 * ↑t * (1 - ↑t) ^ 2 * z₁ * ↑(star x₁ ⬝ᵥ x₂).re 
        -- + (1 - ↑t) ^ 2 * ↑t * z₂ 
        -- + ↑t ^ 3 * z₂ 
        -- + 2 * ↑t ^ 2 * (1 - ↑t) * z₂ * ↑(star x₁ ⬝ᵥ x₂).re := by 
        --   ring_nf


        -- have h_regrouped : ((1 - ↑t) * z₁ + ↑t * z₂) * 
        --   ((1 - ↑t) ^ 2 + ↑t ^ 2 + 2 * ↑t * (1 - ↑t) * ↑(star x₁ ⬝ᵥ x₂).re) = 
        --   (1  - ↑t) * z₁ * ((1 - ↑t)^2 + t^2  + 2 * ↑t * (1  - ↑t) * ↑(star x₁ ⬝ᵥ x₂).re) 
        -- + (↑t * z₂) * ( (1- ↑t)^2 + ↑t^2 + 2 * ↑t * (1 - ↑t) * ↑(star x₁ ⬝ᵥ x₂).re) := by 
        --     ring_nf

        -- have rhs_rw : ((1 - ↑t) * z₁ + ↑t * z₂) * 
        --   ((1 - ↑t) ^ 2 + ↑t ^ 2 + 2 * ↑t * (1 - ↑t) * ↑(star x₁ ⬝ᵥ x₂).re) = 
        --   ((1 - ↑t) * z₁ + ↑t * z₂) * ((1 - ↑t)^2 + ↑t^2 + 2 * ↑t * (1 - ↑t) * ↑(star x₁ ⬝ᵥ x₂).re)
        --    := by 
        --     ring_nf



        -- rw [rhs_rw]
        -- let idk := ContinuousLinearMap.rayleighQuotient()
        norm_cast at *
        -- simp
        -- ring_nf
        

        -- have lhs_rw : (1 - ↑t) ^ 2 * z₁ + ↑t ^ 2 * z₂ + 2 * first_term.re * (↑t * (1 - ↑t)) =
        --   (1 - ↑t) * ↑t * ((1 - ↑t) * z₁ + ↑t * z₂ + 2 * first_term.re) := by 
        --   ring_nf
          

        -- simp
        -- ring_nf
        
        
      simp [conv_eq]
      linarith  
    }
