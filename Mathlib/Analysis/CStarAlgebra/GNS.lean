/-
Copyright (c) 2025 Gregory Wickham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Wickham
-/
module

public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# The GNS (Gelfand-Naimark-Segal) construction

This file contains the constructions and definitions that produce a *-homomorphism from an arbitrary
C*-algebra into the algebra of bounded linear operators on some Hilbert space.

## Main results

- `f.GNS` : a type synonym of `NonUnitalCStarAlgebra` `A` that "forgets" the norm of `A` and bundles
  in a fixed linear functional `f` so that we can construct an inner product and inner
  product-induced norm.
- `f.GNS_HilbertSpace` : the Hilbert space completion of `f.GNS`.
- `f.π` : The non-unital *-homomorphism from a non-unital `A` into the bounded linear operators on
  `f.GNS_HilbertSpace`.
- `f.π_unital` : The unital *-homomorphism from a unital `A` into the bounded linear operators on
  `f.GNS_HilbertSpace`.
-/

@[expose] public section
open scoped ComplexOrder
open Complex ContinuousLinearMap UniformSpace Completion

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] (f : A →ₚ[ℂ] ℂ)

namespace PositiveLinearMap

set_option linter.unusedVariables false in
/-- The GNS space on a non-unital C⋆-algebra with a positive linear functional. This is a type
synonym of `A`. -/
@[nolint unusedArguments]
def GNS (f : A →ₚ[ℂ] ℂ) := A

instance : AddCommGroup f.GNS := inferInstanceAs (AddCommGroup A)
instance : Module ℂ f.GNS := inferInstanceAs (Module ℂ A)

/-- The map from the C⋆-algebra to the GNS space, as a linear equivalence. -/
def toGNS : A ≃ₗ[ℂ] f.GNS := LinearEquiv.refl ℂ _

/-- The map from the GNS space to the C⋆-algebra, as a linear equivalence. -/
def ofGNS : f.GNS ≃ₗ[ℂ] A := (f.toGNS).symm

@[simp]
lemma toGNS_ofGNS (a : f.GNS) : f.toGNS (f.ofGNS a) = a := rfl

@[simp]
lemma ofGNS_toGNS (a : A) : f.ofGNS (f.toGNS a) = a := rfl

variable [StarOrderedRing A]

/--
The (semi-)inner product space whose elements are the elements of `A`, but which has an
inner product-induced norm induced by `f` which is different from the norm on `A`.
-/
@[simps]
def GNSInnerProdSpace : PreInnerProductSpace.Core ℂ f.GNS where
  inner a b := f (star (f.ofGNS a) * f.ofGNS b)
  conj_inner_symm := by simp [← Complex.star_def, ← map_star f]
  re_inner_nonneg _ := RCLike.nonneg_iff.mp (f.map_nonneg (star_mul_self_nonneg _)) |>.1
  add_left _ _ _ := by rw [map_add, star_add, add_mul, map_add]
  smul_left := by simp [smul_mul_assoc]

noncomputable instance : SeminormedAddCommGroup f.GNS :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := f.GNSInnerProdSpace)
noncomputable instance : InnerProductSpace ℂ f.GNS :=
  InnerProductSpace.ofCore f.GNSInnerProdSpace

lemma GNS_norm_def (a : f.GNS) :
    ‖a‖ = (f (star (f.ofGNS a) * f.ofGNS a)).re.sqrt := rfl

lemma GNS_norm_sq (a : f.GNS) :
    ‖a‖ ^ 2 = (f (star (f.ofGNS a) * f.ofGNS a)) := by
  have : 0 ≤ f (star (f.ofGNS a) * f.ofGNS a) := map_nonneg f <| star_mul_self_nonneg _
  rw [GNS_norm_def, ← ofReal_pow, Real.sq_sqrt]
  · rw [conj_eq_iff_re.mp this.star_eq]
  · rwa [re_nonneg_iff_nonneg this.isSelfAdjoint]

/--
The Hilbert space constructed from a positive linear functional on a C⋆-algebra.
-/
abbrev GNS_HilbertSpace := UniformSpace.Completion f.GNS

/--
The bounded operator on `f.GNS` that will be extended to a bounded operator on `f.GNS_HilbertSpace`.
The map is defined as left multiplication by a fixed element `a : A`.
-/
@[simps!]
noncomputable def GNS_op (a : A) : f.GNS →L[ℂ] f.GNS :=
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

@[simp]
lemma GNS_op_prod_eq_comp (a b : A) : f.GNS_op (a * b) = f.GNS_op (a) ∘ f.GNS_op (b) := by
  ext c; simp [mul_assoc]

/--
The non-unital ⋆-homomorphism/⋆-representation of A into the bounded operators on a Hilbert space
that is constructed from a linear functional `f` on a possibly non-unital C⋆-algebra.
-/
noncomputable def π : A →⋆ₙₐ[ℂ] (f.GNS_HilbertSpace →L[ℂ] f.GNS_HilbertSpace) where
  toFun a := mapCLM (f.GNS_op a)
  map_smul' r a := by
    ext x
    induction x using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x => simp [smul_mul_assoc]
  map_zero' := by
    ext b
    induction b using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih b => simp [Completion.coe_zero]
  map_add' x y := by
    ext c
    induction c using Completion.induction_on with
      | hp => apply isClosed_eq <;> fun_prop
      | ih c => simp [add_mul, Completion.coe_add]
  map_mul' a b := by
    ext c
    induction c using Completion.induction_on with
      | hp => apply isClosed_eq <;> fun_prop
      | ih c =>
      have := map_coe ((f.GNS_op a).comp (f.GNS_op b)).uniformContinuous
      simp_all
  map_star' a := by
    refine (eq_adjoint_iff (mapCLM (f.GNS_op (star a))) (mapCLM (f.GNS_op a))).mpr ?_
    intro x y
    induction x, y using Completion.induction_on₂ with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x y => simp [mul_assoc]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (f : A →ₚ[ℂ] ℂ)

/--
The unital ⋆-homomorphism/⋆-representation of A into the bounded operators on a Hilbert space
that is constructed from a linear functional `f` on a unital C⋆-algebra.
-/
noncomputable def π_unital : A →⋆ₐ[ℂ] (f.GNS_HilbertSpace →L[ℂ] f.GNS_HilbertSpace) where
  toFun := f.π
  map_one' := by
    ext b
    induction b using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih b => simp [π]
  commutes' r := by
    dsimp [π]
    simp only [← RingHom.smulOneHom_eq_algebraMap, RingHom.smulOneHom_apply, mapCLM]
    congr; ext c; simp
  map_mul' := map_mul f.π
  map_zero' := map_zero f.π
  map_add' := map_add f.π
  map_star' := map_star f.π

end PositiveLinearMap
