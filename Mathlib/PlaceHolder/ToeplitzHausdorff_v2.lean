-- This module serves as the root of the `ToeplitzHausdorff` library.
-- Import modules here that should be built as part of the library.
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Convex.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Star.Basic

open Complex Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (A : Matrix n n ℂ)

def numericalRange (A : Matrix n n ℂ) : Set ℂ :=
  { z | ∃ x : EuclideanSpace ℂ n, ‖x‖ = 1 ∧ z = dotProduct (star x) (A.mulVec x) }

def convex_set (S : Set ℂ) : Prop :=
  ∀ (z1 z2: ℂ) (t : ℝ) , (z1 ∈ S) -> (z2 ∈ S) -> (0 <= t) -> (t <= 1) -> 
    (1 - t) * z1 + t * z2 ∈ S

open Classical



lemma add_conj_eq_two_re (z : ℂ) : z + star z = 2 * z.re:= by
  rw [Complex.re_eq_add_conj]
  ring_nf
  simp

lemma inner_eq_dot {n : Type*} [Fintype n] [DecidableEq n] (x y : EuclideanSpace ℂ n) :
  star x ⬝ᵥ y = inner x y := by
  rw [dotProduct]
  simp [mul_comm]


-- just used for easier pattern matching
lemma inner_self_eq_dot {n : Type*} [Fintype n] [DecidableEq n] (x : EuclideanSpace ℂ n) :
  star x ⬝ᵥ x = inner x x := by simp [inner_eq_dot]

theorem toeplitz_hausdorff {A : Matrix n n ℂ}
 (hA : Aᴴ = A):
  -- TODO use Convex rather than convex_set
  convex_set (numericalRange A) := 
  by 
    intros z₁ z₂ t hz₁ hz₂ ht₀ ht
    obtain ⟨x₁, hx₁, hz₁'⟩ := hz₁
    obtain ⟨x₂, hx₂, hz₂'⟩ := hz₂

    -- let v := (1 - t) • x₁ + t • x₂
    let v := (1 - t) • z₁ + t • z₂
    by_cases hv : v = 0
    {
      have eq_v : (1 - t) • z₁ + t • z₂ = 0 := hv
      have eq_1 : (1 - t) • z₁ = -(t • z₂) := by 
        rw[add_eq_zero_iff_eq_neg] at eq_v; exact eq_v
      simp_all
      -- TODO FINISH UP THE DEGENERATE CASE
      sorry
    }
    {
      -- Construct our interpolated vector weith convenient weights a and b
      let a := Real.sqrt (1 - t)
      let b := Real.sqrt t
      have ha_nonneg : 0 ≤ a := Real.sqrt_nonneg (1 - t)
      have hb_nonneg : 0 ≤ b := Real.sqrt_nonneg t
      have ha_sq : a * a = 1 - t := Real.mul_self_sqrt (sub_nonneg.mpr ht)
      have hb_sq : b * b = t := Real.mul_self_sqrt ht₀
      have hab_sum : a * a + b * b = 1:= by rw [ha_sq, hb_sq, sub_add_cancel]
      let y := a • x₁ + b • x₂
      let unit_y := (1 / ‖y‖) • y
      use unit_y

      -- first we need to prove that ||unit_y|| = 1
      have norm_unit_y_eq_one : ‖unit_y‖ = 1 := by
        unfold unit_y
        simp [norm_smul, norm_div, norm_one, norm_norm]
        field_simp
        rw [div_self]
        simp []
        sorry
      simp [norm_unit_y_eq_one]
      

      -- then prove the Rayleigh quotient of unit_y is equal to the Convex Combination of z₁ and z₂
      let ray_quot_unit_y := star unit_y ⬝ᵥ A *ᵥ unit_y
      let ray_quot_y := star y ⬝ᵥ A *ᵥ y
      let inner_prod_y := star y ⬝ᵥy
      
      let ray_quot_as_y : ray_quot_unit_y = ray_quot_y / inner_prod_y := by
        sorry

      have hA' : A = Aᴴ := by simp [hA]
      have rhs_eq_ray : star unit_y ⬝ᵥ A *ᵥ unit_y = ray_quot_unit_y := by rfl
      simp [rhs_eq_ray, ray_quot_as_y]
      unfold ray_quot_y inner_prod_y y
       

      -- numerator expansion
      conv_rhs=>
        lhs;
        rw [mulVec_add, star_add]
        rw [dotProduct_add] 
        rw [star_smul, star_smul]
        simp only [star_trivial] -- we know a and b are real
        rw [mulVec_smul]
        rw [dotProduct_smul]
        rw [mulVec_smul]
        rw [dotProduct_smul]
        simp
        rw [←mul_assoc, ←mul_assoc, ←mul_assoc, ←mul_assoc, ←add_assoc]
        norm_cast
        rw [ha_sq, hb_sq] -- we rearraged to get a*a and b*b which we know equal (1-t) and t
        rw [←hz₁', ←hz₂'] -- sub in z1 and z2 for readability
        simp 
        rw [star_dotProduct]
        rw [hA']
        rw [mulVec_conjTranspose, star_star]
        rw [←dotProduct_mulVec]
        rw [hA]

      -- Line up inner products in the form 
      have h_reorder : (1 - ↑t) * z₁ + ↑a * ↑b * star (star x₁ ⬝ᵥ A *ᵥ x₂) 
      + ↑b * ↑a * star x₁ ⬝ᵥ A *ᵥ x₂ 
      + ↑t * z₂ 
      =
        (1 - ↑t) * z₁ 
      + ↑t * z₂ 
      + ↑a * ↑b *
      (star x₁ ⬝ᵥ A *ᵥ x₂ + star (star x₁ ⬝ᵥA *ᵥ x₂)) := by ring_nf
      rw [h_reorder]

      rw [add_conj_eq_two_re] -- relate the cross products
      rw [←mul_assoc]

      have group_sqs : ↑a * ↑b * star x₂ ⬝ᵥ x₁ + ↑a * ↑b * star x₁ ⬝ᵥ x₂ + ↑a ^ 2 + ↑b ^ 2 = 
        ↑a * a  + b * b + ↑a * ↑b * star x₂ ⬝ᵥ x₁ + ↑a * ↑b * star x₁ ⬝ᵥ x₂ := by ring_nf

      -- denominator expansion
      conv_rhs=>
        rhs;
        rw [star_add] 
        rw [dotProduct_add]
        rw [star_smul, star_smul]
        rw [dotProduct_smul, dotProduct_smul]
        simp [star_trivial]
        ring_nf
        simp 
        rw [inner_self_eq_dot, inner_self_eq_dot]
        rw [←inner_self_ofReal_re, inner_self_eq_norm_sq]
        rw [←inner_self_ofReal_re, inner_self_eq_norm_sq]
        simp [hx₁, hx₂]
        rw [group_sqs]
        norm_cast
        rw [hab_sum]
        rw [add_assoc, ←mul_add]
        rw [inner_eq_dot, ←inner_conj_symm]
        rw [←inner_eq_dot]
        conv =>
          pattern ((starRingEnd ℂ) _ + _)
          rw [add_comm, starRingEnd_apply]
        rw [add_conj_eq_two_re ]
        simp
        ring_nf

      have x1_neqz : x₁ ≠ 0 := by
        simp [←norm_eq_zero, hx₁]
        simp [norm_one]

      have x2_neqz : x₂ ≠ 0 := by
        simp [←norm_eq_zero, hx₂]
        simp [norm_one]


      have position_2 : 1 + a * b * (star x₁ ⬝ᵥ x₂).re * 2 = 
        1 + a * b * (2 * ↑(star x₁ ⬝ᵥ x₂).re) := by ring_nf



      have denom_neqz : (1 + ↑a * ↑b * ↑(star x₁ ⬝ᵥ x₂).re * 2) ≠ 0 := by
        simp
        rw [position_2] 
        sorry

      -- TODO MOVE THE DENOMINATOR OVER TO THE LHS
      -- apply (div_eq_iff denom_neqz).mp

      -- TODO REARRANGE LHS SUCH THAT WE HAVE ℜ(starx1⬝vx2)⋅(a2z1+b2z2)

      -- TODO simplify to (1−t)z1+tz2+2abℜ(starx1⬝vA∗vx2),
      -- And then finish
 


      sorry
    
    }

