/-
Copyright (c) 2025 Gregory Wickham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Wickham
-/
module

public import Mathlib.Analysis.CStarAlgebra.GNSConstruction.Defs
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The *-homomorphism of the GNS construction

In this file we define both the unital and non-unital ⋆-homomorphisms from a C⋆-algebra `A`
into the algebra of bounded operators on a Hilbert space.

## Main results

- `f.π` : The non-unital *-homomorphism from a non-unital `A` into the bounded linear operators on
  `f.GNS_HilbertSpace`.
- `f.π_unital` : The unital *-homomorphism from a unital `A` into the bounded linear operators on
  `f.GNS_HilbertSpace`.

-/
@[expose] public section
open scoped ComplexOrder
open Complex ContinuousLinearMap UniformSpace Completion

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (f : A →ₚ[ℂ] ℂ)

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

@[simps!]
noncomputable def π_ofA (a : A) : f.GNS_HilbertSpace →L[ℂ] f.GNS_HilbertSpace :=
  mapCLM (f.const_mul_GNS a)

@[simp]
lemma const_mul_GNS_prod_eq_comp (a b : A) :
    f.const_mul_GNS (a * b) = f.const_mul_GNS (a) ∘ f.const_mul_GNS (b) := by
  ext c
  simp [mul_assoc]

noncomputable def π : NonUnitalStarAlgHom ℂ A (f.GNS_HilbertSpace →L[ℂ] f.GNS_HilbertSpace) where
  toFun := f.π_ofA
  map_smul' r a := by
    ext x
    induction x using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x
    simp [ContinuousLinearMap.uniformContinuous, map_coe, smul_mul_assoc]
  map_zero' := by
    ext b
    induction b using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih b
    simp [map_coe, ContinuousLinearMap.uniformContinuous]
    rfl
  map_add' x y := by
    ext c
    induction c using Completion.induction_on with
      | hp => apply isClosed_eq <;> fun_prop
      | ih c
    simp [ContinuousLinearMap.uniformContinuous, map_coe, add_mul, map_add, Completion.coe_add]
  map_mul' a b := by
    ext c
    induction c using Completion.induction_on with
      | hp => apply isClosed_eq <;> fun_prop
      | ih c
    simp only [π_ofA, mapCLM, coe_mk', LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.coe_mul,
      Function.comp_apply, const_mul_GNS_prod_eq_comp, ContinuousLinearMap.uniformContinuous,
      map_coe, const_mul_GNS_apply, ofGNS_toGNS]
    rw [map_coe]
    · simp
    exact ContinuousLinearMap.uniformContinuous ((f.const_mul_GNS a).comp (f.const_mul_GNS b))
  map_star' a := by
    refine (eq_adjoint_iff (π_ofA f (star a)) (π_ofA f a)).mpr ?_
    intro x y
    induction x, y using Completion.induction_on₂ with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x y
    simp only [π_ofA_apply]
    rw [map_coe (ContinuousLinearMap.uniformContinuous (f.const_mul_GNS a)),
      map_coe (ContinuousLinearMap.uniformContinuous (f.const_mul_GNS (star a)))]
    simp [GNS_inner_def, const_mul_GNS, mul_assoc]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (f : A →ₚ[ℂ] ℂ)

noncomputable def π_unital : StarAlgHom ℂ A (f.GNS_HilbertSpace →L[ℂ] f.GNS_HilbertSpace) where
  toFun := f.π
  map_one' := by
    ext b
    induction b using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih b
    dsimp [π, π_ofA]
    rw [map_coe (ContinuousLinearMap.uniformContinuous (f.const_mul_GNS 1))]
    simp [const_mul_GNS, const_mul_GNS]
  commutes' r := by
    dsimp [π]
    simp only [← RingHom.smulOneHom_eq_algebraMap, RingHom.smulOneHom_apply, π_ofA, mapCLM]
    congr
    ext c
    simp [const_mul_GNS, const_mul_GNS]
  map_mul' := map_mul f.π
  map_zero' := map_zero f.π
  map_add' := map_add f.π
  map_star' := map_star f.π

end PositiveLinearMap
