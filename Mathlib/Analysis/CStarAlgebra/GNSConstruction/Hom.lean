/-
Copyright (c) 2025 Gregory Wickham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Wickham
-/
module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
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
open Complex ContinuousLinearMap UniformSpace Completion

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)
namespace PositiveLinearMap

@[simps!]
noncomputable def const_mul_GNS (a : A) : f.GNS →L[ℂ] f.GNS :=
  (f.toGNS.toLinearMap ∘ₗ LinearMap.mul ℂ A a ∘ₗ f.ofGNS.toLinearMap).mkContinuous ‖a‖ fun x ↦ by
    rw [← sq_le_sq₀ (by positivity) (by positivity), mul_pow, ← RCLike.ofReal_le_ofReal (K := ℂ),
      RCLike.ofReal_pow, RCLike.ofReal_eq_complex_ofReal, GNS_norm_sq]
    have : star (f.ofGNS x) * star a * (a * f.ofGNS x) ≤
        ‖a‖ ^ 2 • star (f.ofGNS x) * f.ofGNS x := by
      rw [← mul_assoc, mul_assoc _ (star a), sq, ← CStarRing.norm_star_mul_self (x := a),
        smul_mul_assoc]
      exact CStarAlgebra.star_left_conjugate_le_norm_smul
    calc
      _ ≤ f (‖a‖ ^ 2 • star (f.ofGNS x) * f.ofGNS x) := by simpa using OrderHomClass.mono f this
      _ = _ := by simp [← Complex.coe_smul, GNS_norm_sq, smul_mul_assoc]

noncomputable
def A_mul_GNS : A →ₗ[ℂ] f.GNS →L[ℂ] f.GNS where
  toFun a := f.const_mul_GNS a
  map_add' _ _ := by ext b; simp [const_mul_GNS]
  map_smul' _ _ := by ext b; simp [const_mul_GNS]

@[simps]
noncomputable def π_ofA (a : A) : f.GNS_HilbertSpace →L[ℂ] f.GNS_HilbertSpace where
  toFun := Completion.map <| f.A_mul_GNS a
  map_add' x y := by
    induction x, y using Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x y =>
      simp [Completion.map_coe, ← Completion.coe_add, ContinuousLinearMap.uniformContinuous]
  map_smul' r x := by
    induction x using Completion.induction_on with
    | hp =>
      exact isClosed_eq (continuous_map.comp <| continuous_const_smul r)
        (continuous_map.const_smul _) -- fun_prop is failing on these goals for some reason
    | ih x =>
      simp [Completion.map_coe, ← Completion.coe_smul, ContinuousLinearMap.uniformContinuous]
  cont := continuous_map

@[simp]
lemma A_mul_GNS_prod_eq_comp (a b : A) :
    f.A_mul_GNS (a * b) = f.A_mul_GNS (a) ∘ f.A_mul_GNS (b) := by
  ext c
  simp [A_mul_GNS, const_mul_GNS, mul_assoc]

noncomputable def π : NonUnitalStarAlgHom ℂ A (f.GNS_HilbertSpace →L[ℂ] f.GNS_HilbertSpace) where
  toFun := f.π_ofA
  map_smul' r a := by
    ext x
    induction x using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x
    simp [map_coe, ContinuousLinearMap.uniformContinuous, UniformContinuous.const_smul _ r]
  map_zero' := by
    ext b
    dsimp [π_ofA]
    simp only [map_zero]
    induction b using Completion.induction_on with
    | hp => exact (isClosed_eq (by continuity) (by continuity))
    | ih b
    dsimp [A_mul_GNS, const_mul_GNS]
    simp [Completion.map_coe, ContinuousLinearMap.uniformContinuous]
    rfl
  map_add' x y := by
    ext c
    simp only [π_ofA, coe_mk', LinearMap.coe_mk, AddHom.coe_mk, add_apply]
    induction c using Completion.induction_on with
      | hp => exact (isClosed_eq (by continuity) (by continuity))
      | ih c
    simp [Completion.map_coe, ContinuousLinearMap.uniformContinuous]
    norm_cast
  map_mul' a b := by
    ext c
    simp only [π_ofA, coe_mk', LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.coe_mul,
      Function.comp_apply]
    induction c using Completion.induction_on with
      | hp => exact (isClosed_eq (by continuity)
            (ContinuousLinearMap.continuous ((f.π_ofA a).comp (f.π_ofA b))))
      | ih c
    simp only [A_mul_GNS_prod_eq_comp, ContinuousLinearMap.uniformContinuous, map_coe]
    rw [Completion.map_coe]
    · simp
    exact ContinuousLinearMap.uniformContinuous ((f.A_mul_GNS a).comp (f.A_mul_GNS b))
  map_star' a := by
    refine (eq_adjoint_iff (π_ofA f (star a)) (π_ofA f a)).mpr ?_
    intro x y
    induction x using Completion.induction_on with
    | hp => exact (isClosed_eq (by continuity)
      (Continuous.inner (continuous_id) (continuous_const)))
    | ih x
    induction y using Completion.induction_on with
    | hp => exact (isClosed_eq (Continuous.inner (continuous_const) (continuous_id))
        (Continuous.inner (by continuity) (by continuity)))
    | ih y
    simp_all only [π_ofA_apply]
    rw [Completion.map_coe (ContinuousLinearMap.uniformContinuous (f.A_mul_GNS a)),
      Completion.map_coe (ContinuousLinearMap.uniformContinuous (f.A_mul_GNS (star a)))]
    simp_all [GNS_inner_def, A_mul_GNS]
    group

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

noncomputable def π_unital : StarAlgHom ℂ A (f.GNS_HilbertSpace →L[ℂ] f.GNS_HilbertSpace) where
  toFun := f.π
  map_one' := by
    ext b
    dsimp [π, π_ofA]
    induction b using Completion.induction_on with
    | hp => exact (isClosed_eq (by continuity) (by continuity))
    | ih b
    rw [Completion.map_coe (ContinuousLinearMap.uniformContinuous (f.A_mul_GNS 1))]
    simp_all [A_mul_GNS, const_mul_GNS]
  commutes' r := by
    dsimp [π]
    simp only [← RingHom.smulOneHom_eq_algebraMap, RingHom.smulOneHom_apply, π_ofA]
    congr
    ext c
    simp [A_mul_GNS, const_mul_GNS]
  map_mul' := MulHomClass.map_mul f.π
  map_zero' := map_zero f.π
  map_add' := AddHomClass.map_add f.π
  map_star' := map_star f.π

end PositiveLinearMap
