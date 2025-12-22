/-
Copyright (c) 2025 Gregory Wickham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Wickham
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.GNSConstruction.Defs
public import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# The *-homomorphism of the GNS construction

In this file we define the unital ⋆-homomorphism from our C⋆-algebra `A` into the Hilbert space
`f.GNS_HilbertSpace` that is constructed in Mathlib.Analysis.CStarAlgebra.GNSConstruction.Defs.

## Main results

- `f.π` : The unital *-homomorphism from `A` into the bounded linear operators on
  `f.GNS_HilbertSpace`.

## References

Most of this work follows from private course notes prepared by Professor Konrad Aguilar at Pomona
College.

For another, similar approach, see "A Primer on Spectral Theory" by Bernard Aupetit, the other main
refence used here.
-/
@[expose] public section
open scoped ComplexOrder
open Complex
open UniformSpace
open UniformSpace.Completion
open Submodule
open ContinuousLinearMap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A]
variable (f : A →ₚ[ℂ] ℂ)

namespace PositiveLinearMap
/--
Left multiplication of elements of `f.GNS` by elements of `A`  is linear. This is used to construct
our desired *-homomorphism.
-/
noncomputable
def A_mul_GNS : A →ₗ[ℂ] f.GNS →ₗ[ℂ] f.GNS
  := (LinearMap.mul ℂ f.GNS)

lemma A_GNS_mul_apply (a : A) (b : f.GNS) :
  f.A_mul_GNS a b = (f.toGNS a) * b := by rfl

instance : HMul A f.GNS f.GNS where
  hMul a b := (f.toGNS a) * b

instance : HMul f.GNS A f.GNS where
  hMul a b := (f.ofGNS a) * b

lemma A_mul_GNS_def (a : A) (b : f.GNS) : a * b = f.A_mul_GNS a b := by rfl

variable (a : A) [StarOrderedRing A]

/--
This theorem allows us to extend multiplication of elements of `A` to multiplicaton of and element
of `A` with an element of `f.GNS_Quotient`.
-/
theorem A_mul_GNS_well_defined :
  f.GNS_Submodule ≤ Submodule.comap (f.A_mul_GNS a) (f.GNS_Submodule) := by
  intro x xh
  have hab := f.induced_inner_norm_sq_self_le ((star a) * (a * x)) x
  rw [star_mul, star_star, xh, mul_zero] at hab
  norm_cast at hab
  apply (_root_.sq_nonpos_iff ‖f (star (a * x) * a * x)‖).mp at hab
  rwa [norm_eq_zero, mul_assoc] at hab

/--
This defines a linear operator on `f.GNS_Quotient` by left multiplication by a fixed element of `A`.
-/
noncomputable
def π_OfA_nonCont : (f.GNS_Quotient) →ₗ[ℂ] (f.GNS_Quotient) where
  toFun := Submodule.mapQ f.GNS_Submodule f.GNS_Submodule (f.A_mul_GNS a)
    (f.A_mul_GNS_well_defined a)
  map_add' := by simp
  map_smul' := by simp

/--
When the element of `f.GNS_Quotient` is constructed from an element of `f.GNS`, the linear operator
simplifies to multiplication.
-/
@[simp]
lemma π_OfA_apply (b : f.GNS) :
  (f.π_OfA_nonCont a) (Submodule.Quotient.mk b) =
    Submodule.Quotient.mk (a * b) := by rfl

/--
This positive linear functional simply helps with some of the below proofs. There should be no
reason to reference it outside of this file.
-/
def g (b : A) : A →ₚ[ℂ] ℂ where
  toFun x := f (star b * x * b)
  map_add' x y := by rw [mul_add, add_mul, map_add]
  map_smul' m x := by simp
  monotone' := by
    unfold Monotone
    intro y z hyz
    apply le_neg_add_iff_le.mp
    obtain ⟨q, hq⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg_of_le hyz)
    rw [add_comm, ← sub_eq_add_neg, ← map_sub, mul_assoc, mul_assoc,
      ← mul_sub (star b) (z * b) (y * b), ← sub_mul, ← mul_assoc,
      hq, ← mul_assoc, mul_assoc (star b * star q), ← star_mul]
    exact f.map_nonneg (star_mul_self_nonneg (q * b))

@[simp]
lemma g_apply (b : f.GNS) (x : f.GNS) :
  f (star b * x * b) = (f.g b) x := by rfl

/--
The linear operator has a bounded unit ball.
-/
lemma π_OfA_bounded_unit_ball :
  (∀ z ∈ Metric.ball 0 1, ‖(f.π_OfA_nonCont a) z‖ ≤ ‖a‖) := by
  intro b bh
  rw [Metric.mem_ball, dist_zero_right, InnerProductSpace.Core.norm_eq_sqrt_re_inner] at bh
  induction b using Submodule.Quotient.induction_on with | _ b
  rw [GNS_Quotient_inner_apply, RCLike.re_to_complex] at bh
  have bh' : √(f (star b * b)).re ≤ 1 := by linarith
  have prodInR := f.re_of_self_star_self (star b)
  have staraaPos := (mul_star_self_nonneg (star a : A))
  have starbPos := f.map_nonneg (mul_star_self_nonneg (star b : A))
  rw [star_star, π_OfA_apply] at *
  have bh2 : (f (star b * b)).re ≤ 1 := (Real.sqrt_le_one (x := (f (star b * b)).re)).mp bh'
  have hyp1 : f (star b * b) ≤ 1 := by rw [← prodInR]; norm_cast
  rw [InnerProductSpace.Core.norm_eq_sqrt_re_inner, GNS_Quotient_inner_apply, star_mul,
    RCLike.re_to_complex, ← mul_assoc]
  nth_rw 2 [mul_assoc]
  rw [g_apply]
  have g_of_one : (f.g b) 1 = f (star b * b) := by simp [← f.g_apply b 1]
  have g_of_star_a_a_real := re_of_self_star_self (f.g b) (star a)
  have gval_real : ((f.g b) (star a * a)).re = ((f.g b) (star a * a)) := by
    rwa [star_star] at g_of_star_a_a_real
  have g_pos := PositiveLinearMap.map_nonneg (f.g b) (mul_star_self_nonneg (star a : A))
  have gval_pos : 0 ≤ ((f.g b) (star a * a)).re := by
    rwa [star_star, ← gval_real, zero_le_real] at g_pos
  have step2 := PositiveLinearMap.norm_apply_le_of_nonneg (f.g b) (star a * a) staraaPos
  rw [g_of_one, ← gval_real, norm_real, Real.norm_eq_abs, abs_of_nonneg gval_pos] at step2
  have step3 : ‖f (star b * b)‖ * ‖star a * a‖ ≤ 1 * ‖star a * a‖ := by
    nlinarith [norm_nonneg (star a * a), norm_nonneg (f (star b * b)),
      (CStarAlgebra.norm_le_one_iff_of_nonneg (f (star b * b)) starbPos).mpr hyp1]
  norm_num at step3
  nth_rw 2 [CStarRing.norm_star_mul_self] at step3
  rw [← pow_two] at step3
  have step4 : ((f.g b) (star a * a)).re ≤ ‖a‖ ^ 2 := by linarith
  exact (Real.sqrt_le_left (norm_nonneg a)).mpr step4

/--
The linear operator has a bound.
-/
lemma bound_on_π_ofA_exists :
  ∃ C, ∀ (z : f.GNS_Quotient), ‖(π_OfA_nonCont f a) z‖ ≤ C * ‖z‖ :=
  LinearMap.bound_of_ball_bound (Real.zero_lt_one) (norm a) (f.π_OfA_nonCont a)
    (f.π_OfA_bounded_unit_ball a)

/--
The linear operator on `f.GNS_Quotient` is continuous (because it is bounded).
-/
noncomputable
def π_ofA_onQuot : f.GNS_Quotient →L[ℂ] f.GNS_Quotient :=
  LinearMap.mkContinuousOfExistsBound (f.π_OfA_nonCont a) (f.bound_on_π_ofA_exists a)

@[simp]
lemma π_eq_π_nonCont_on_input (b : f.GNS_Quotient) :
  (f.π_ofA_onQuot a) b = (f.π_OfA_nonCont a) b := by dsimp [π_ofA_onQuot]

@[simp]
lemma π_apply_on_quot (b : f.GNS) :
  ((f.π_ofA_onQuot a) (Submodule.Quotient.mk b)) = Submodule.Quotient.mk (a * b) := by simp

@[simp]
lemma π_completion_onQuot_equiv (b : f.GNS_Quotient) :
  Completion.map ⇑(π_ofA_onQuot f a) ↑b = (π_ofA_onQuot f a) b := by
    simp [map_coe (ContinuousLinearMap.uniformContinuous (f.π_ofA_onQuot a))]

/--
We define the linear operator on `f.GNS_HilbertSpac`, which is parameterized by an `a : A`, as a
continuous linear map.
-/
noncomputable
def π_OfA (a : f.GNS) : f.GNS_HilbertSpace →L[ℂ] f.GNS_HilbertSpace where
  toFun := Completion.map (f.π_ofA_onQuot a)
  map_add' x y := by
    induction x using Completion.induction_on with
    | hp => exact (isClosed_eq ((continuous_map).comp (by continuity))
        (Continuous.add (continuous_map) (continuous_const)))
    | ih x
    induction y using Completion.induction_on with
    | hp => exact (isClosed_eq ((continuous_map).comp (by continuity))
        (Continuous.add (continuous_const) (continuous_map)))
    | ih y
    rw [← Completion.coe_add]
    simp only [π_completion_onQuot_equiv, map_add]
    rw [Completion.coe_add]
  map_smul' x y := by
    induction y using Completion.induction_on with
    | hp => exact (isClosed_eq ((continuous_map).comp (continuous_const_smul x))
        (Continuous.smul (continuous_const) (continuous_map)))
    | ih y
    rw [← Completion.coe_smul, π_completion_onQuot_equiv]
    simp
  cont := continuous_map

/--
We define the unital *-homomorphism from `A` into the bounded linear operators on
`f.GNS_HilbertSpace`, denoted `H f →L[ℂ] H f`. Thus, our final *-homormorphism is
`f.π : A →⋆ₐ[ℂ] H f →L[ℂ] H f`.
-/
noncomputable
def π : StarAlgHom ℂ A (f.GNS_HilbertSpace →L[ℂ] f.GNS_HilbertSpace) where
  toFun := π_OfA f
  map_one' := by
    ext b
    induction b using Completion.induction_on with
    | hp => exact (isClosed_eq (by continuity) (by continuity))
    | ih b
    induction b using Quotient.induction_on
    simp [π_OfA]
  map_mul' a b := by
    ext c
    induction c using Completion.induction_on with
    | hp => exact (isClosed_eq (by continuity)
          (ContinuousLinearMap.continuous ((f.π_OfA a).comp (f.π_OfA b))))
    | ih c
    induction c using Quotient.induction_on
    simp [π_OfA, ← mul_assoc]
  map_zero' := by
    ext y
    induction y using Completion.induction_on with
    | hp => exact (isClosed_eq (by continuity) (by continuity))
    | ih y
    induction y using Quotient.induction_on
    simp [π_OfA]
    rfl
  map_add' x y := by
    ext c
    rw [add_apply]
    induction c using Completion.induction_on with
    | hp => exact (isClosed_eq (by continuity) (by continuity))
    | ih c
    induction c using Quotient.induction_on
    simp [π_OfA, π_OfA_nonCont, A_mul_GNS, Completion.coe_add]
  commutes' r := by
    simp only [← RingHom.smulOneHom_eq_algebraMap, RingHom.smulOneHom_apply, π_OfA]
    congr
    ext c
    simp only [π_ofA_onQuot, LinearMap.mkContinuousOfExistsBound_apply]
    induction c using Quotient.induction_on
    simp
  map_star' a := by
    refine (eq_adjoint_iff (f.π_OfA (star a)) (f.π_OfA a)).mpr ?_
    intro x y
    induction x using Completion.induction_on with
    | hp => exact (isClosed_eq (by continuity)
      (Continuous.inner (continuous_id) (continuous_const)))
    | ih x
    induction y using Completion.induction_on with
    | hp => exact (isClosed_eq (Continuous.inner (continuous_const) (continuous_id))
        (Continuous.inner (by continuity) (by continuity)))
    | ih y
    induction x using Quotient.induction_on
    induction y using Quotient.induction_on
    have (a b : f.GNS_Quotient) : inner ℂ (coe' a) (coe' b) =
      GNS_Quotient_inner f a b := by rw [inner_coe]; rfl
    simp [π_OfA, this, mul_assoc]

theorem π_continuous : Continuous (f.π) :=
  NonUnitalStarAlgHom.CStarAlgHom_continuous (A := A)
    (B := (f.GNS_HilbertSpace →L[ℂ] f.GNS_HilbertSpace)) (f.π)

end PositiveLinearMap
