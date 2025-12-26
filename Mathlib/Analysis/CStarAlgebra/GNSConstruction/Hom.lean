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
open ContinuousLinearMap
open UniformSpace
open UniformSpace.Completion

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

namespace PositiveLinearMap

noncomputable instance : NormedSpace ℂ f.GNS :=
  InnerProductSpace.Core.toNormedSpace (c := f.preInnerProdSpace)

variable (a : A)

lemma fprop (a : A) : ‖f a‖ ≤ ‖f‖ * ‖a‖ := le_opNorm (f : A →L[ℂ] ℂ) a


@[simp]
lemma ofTo : f.ofGNS (f.toGNS a) = a := by rfl


@[simp]
lemma toOf : f.toGNS (f.ofGNS a) = a := by rfl

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
lemma g_apply (x b : A):
  f (star b * x * b) = (f.g b) x := by rfl

noncomputable
def const_mul_GNS_nonCont : f.GNS →ₗ[ℂ] f.GNS where
  toFun b := f.toGNS ((ContinuousLinearMap.mul (R := A) (𝕜 := ℂ) a) (f.ofGNS b))
  map_add' x y := by simp [map_add]
  map_smul' c x := by simp_all

noncomputable
def const_mul_GNS : f.GNS →L[ℂ] f.GNS := by
  refine LinearMap.mkContinuous (f.const_mul_GNS_nonCont a) (‖a‖) ?_
  intro x
  simp only [GNS_norm_def]
  have move_const : ‖a‖ = √((‖a‖) ^ 2) := by simp_all only [norm_nonneg, Real.sqrt_sq]
  have : 0 ≤ (‖a‖) ^ 2 := by exact pow_two_nonneg ‖a‖
  have : 0 ≤ star (f.ofGNS x) * f.ofGNS x := by exact star_mul_self_nonneg (f.ofGNS x)
  have : 0 ≤ (f (star (f.ofGNS x) * f.ofGNS x)) := by exact PositiveLinearMap.map_nonneg f this
  have : (0 : ℂ) ≤ (f (star (f.ofGNS x) * f.ofGNS x)).re := by
    rw [f.re_of_star_mul_self]; simp_all
  have : 0 ≤ (f (star (f.ofGNS x) * f.ofGNS x)).re := by simp_all
  have : 0 ≤ (‖a‖) ^ 2 * (f (star (f.ofGNS x) * f.ofGNS x)).re := by
    (expose_names; exact mul_nonneg this_1 this)
  rw [move_const, ← Real.sqrt_mul']
  · apply (Real.sqrt_le_sqrt_iff this).mpr
    dsimp [const_mul_GNS_nonCont]
    simp only [ofTo, star_mul]
    nth_rw 1 [← mul_assoc]
    nth_rw 2 [mul_assoc]
    rw [f.g_apply (star a * a) (f.ofGNS x)]
    suffices ((f.g (f.ofGNS x)) (star a * a)).re ≤
        ‖a‖ ^ 2 * (f (star (f.ofGNS x) * 1 * f.ofGNS x)).re by
      simp at this
      assumption
    rw [f.g_apply (1) (f.ofGNS x)]
    rw [← opNorm_eq_of_one, pow_two, ← CStarRing.norm_star_mul_self]
    have main := fprop ((f.g (f.ofGNS x))) (star a * a)
    have re_eq_self := re_of_self_star_self ((f.g (f.ofGNS x))) (star a)
    simp only [star_star] at re_eq_self
    have : 0 ≤ (star a * a) := by exact star_mul_self_nonneg a
    have : 0 ≤ (f.g (f.ofGNS x)) (star a * a) := PositiveLinearMap.map_nonneg (f.g (f.ofGNS x)) this
    have : ‖(f.g (f.ofGNS x)) (star a * a)‖ = ((f.g (f.ofGNS x)) (star a * a)).re := by
      suffices (‖(f.g (f.ofGNS x)) (star a * a)‖ : ℂ) = (((f.g (f.ofGNS x)) (star a * a)).re : ℂ) by
        norm_cast at this
      rw [re_eq_self]
      exact norm_of_nonneg' this
    rw [← this, mul_comm]
    have : (‖f.g (f.ofGNS x)‖ : ℂ).re = ‖f.g (f.ofGNS x)‖ := by simp
    rwa [this]
  assumption

noncomputable
def A_mul_GNS : A →ₗ[ℂ] f.GNS →L[ℂ] f.GNS where
  toFun a := f.const_mul_GNS a
  map_add' x y := by
    ext b
    dsimp [const_mul_GNS, const_mul_GNS_nonCont]
    rw [← map_add, add_mul]
  map_smul' c x := by
    ext b
    simp_all only [RingHom.id_apply, coe_smul', Pi.smul_apply]
    dsimp [const_mul_GNS, const_mul_GNS_nonCont]
    rw [← map_smul]
    simp

noncomputable
def constA_mul_Quot_toQuot : f.GNS_Quotient →L[ℂ] f.GNS_Quotient where
  toFun := (SeparationQuotient.mkCLM (M := f.GNS) (R := ℂ)) ∘ (f.A_mul_GNS a) ∘
      (SeparationQuotient.outCLM (E := f.GNS) (K := ℂ))
  map_add' := by simp_all
  map_smul' := by simp_all

@[simp]
lemma π_completion_onQuot_equiv (b : f.GNS_Quotient) :
  Completion.map ⇑(f.constA_mul_Quot_toQuot a) ↑b = (f.constA_mul_Quot_toQuot a) b := by
    simp [map_coe (ContinuousLinearMap.uniformContinuous (f.constA_mul_Quot_toQuot a))]

noncomputable
def π_ofA (a : A) : f.GNS_HilbertSpace →L[ℂ] f.GNS_HilbertSpace where
  toFun := Completion.map (f.constA_mul_Quot_toQuot a)
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

variable [StarOrderedRing A]

noncomputable
def π : StarAlgHom ℂ A (f.GNS_HilbertSpace →L[ℂ] f.GNS_HilbertSpace) where
  toFun := f.π_ofA
  map_one' := by
    ext b
    dsimp [π_ofA]
    induction b using Completion.induction_on with
    | hp => exact (isClosed_eq (by continuity) (by continuity))
    | ih b
    simp_all only [π_completion_onQuot_equiv, Completion.coe_inj]
    dsimp [constA_mul_Quot_toQuot, A_mul_GNS, const_mul_GNS, const_mul_GNS_nonCont]
    simp_all
  map_mul' a b := by
    ext c
    induction c using Completion.induction_on with
    | hp => exact (isClosed_eq (by continuity)
          (ContinuousLinearMap.continuous ((f.π_ofA a).comp (f.π_ofA b))))
    | ih c
    simp [π_ofA]
    dsimp [constA_mul_Quot_toQuot, A_mul_GNS, const_mul_GNS, const_mul_GNS_nonCont]
    congr 2
    sorry
  map_zero' := by
    ext b
    dsimp [π_ofA]
    induction b using Completion.induction_on with
    | hp => exact (isClosed_eq (by continuity) (by continuity))
    | ih b
    simp_all only [π_completion_onQuot_equiv]
    dsimp [constA_mul_Quot_toQuot, A_mul_GNS, const_mul_GNS, const_mul_GNS_nonCont]
    simp_all
  map_add' x y := by
    ext c
    rw [add_apply]
    induction c using Completion.induction_on with
    | hp => exact (isClosed_eq (by continuity) (by continuity))
    | ih c
    simp [π_ofA, constA_mul_Quot_toQuot, A_mul_GNS, const_mul_GNS]
    sorry
  commutes' r := by sorry
  map_star' a := by
    refine (eq_adjoint_iff (f.π_ofA (star a)) (f.π_ofA a)).mpr ?_
    intro x y
    induction x using Completion.induction_on with
    | hp => exact (isClosed_eq (by continuity)
      (Continuous.inner (continuous_id) (continuous_const)))
    | ih x
    induction y using Completion.induction_on with
    | hp => exact (isClosed_eq (Continuous.inner (continuous_const) (continuous_id))
        (Continuous.inner (by continuity) (by continuity)))
    | ih y
    sorry


end PositiveLinearMap
