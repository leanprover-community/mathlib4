/-
Copyright (c) 2025 Gregory Wickham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Wickham
-/
module

public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# The GNS (Gelfand-Naimark-Segal) construction

This file contains the constructions and definitions that produce a ⋆-homomorphism from an arbitrary
C⋆-algebra into the algebra of bounded linear operators on some Hilbert space.

## Main results

- `f.preGNS` : a type synonym of `A` that forgets the norm of `A` and bundles in a fixed linear
  functional `f` so that we can construct an inner product and inner product-induced norm.
- `f.GNS` : the Hilbert space completion of `f.preGNS`.
- `f.gnsNonUnitalStarAlgHom` : The non-unital *-homomorphism from a non-unital `A` into the bounded
  linear operators on `f.GNS`.
- `f.gnsStarAlgHom` : The unital *-homomorphism from a unital `A` into the bounded linear operators
  on `f.GNS`.

## TODO

- Explicitly construct a unit norm cyclic vector ζ such that
  a ↦ ⟨(f.gns(NonUnital)StarAlgHom a) * ζ, ,ζ⟩ is a state on `A` for both unital and non-unital
  cases.

-/

@[expose] public section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] (f : A →ₚ[ℂ] ℂ)

namespace PositiveLinearMap

set_option linter.unusedVariables false in
/-- The GNS space on a non-unital C⋆-algebra with a positive linear functional. This is a type
synonym of `A`. -/
@[nolint unusedArguments]
def preGNS (f : A →ₚ[ℂ] ℂ) := A

instance : AddCommGroup f.preGNS := inferInstanceAs (AddCommGroup A)
instance : Module ℂ f.preGNS := inferInstanceAs (Module ℂ A)

/-- The map from the C⋆-algebra to the GNS space, as a linear equivalence. -/
def toPreGNS : A ≃ₗ[ℂ] f.preGNS := LinearEquiv.refl ℂ _

/-- The map from the GNS space to the C⋆-algebra, as a linear equivalence. -/
def ofPreGNS : f.preGNS ≃ₗ[ℂ] A := f.toPreGNS.symm

@[simp]
lemma toPreGNS_ofPreGNS (a : f.preGNS) : f.toPreGNS (f.ofPreGNS a) = a := rfl

@[simp]
lemma ofPreGNS_toPreGNS (a : A) : f.ofPreGNS (f.toPreGNS a) = a := rfl

variable [StarOrderedRing A]

/--
The (semi-)inner product space whose elements are the elements of `A`, but which has an
inner product-induced norm induced by `f` which is different from the norm on `A`.
-/
abbrev preGNSInnerProdSpace : PreInnerProductSpace.Core ℂ f.preGNS where
  inner a b := f (star (f.ofPreGNS a) * f.ofPreGNS b)
  conj_inner_symm := by simp [← Complex.star_def, ← map_star f]
  re_inner_nonneg _ := RCLike.nonneg_iff.mp (f.map_nonneg (star_mul_self_nonneg _)) |>.1
  add_left _ _ _ := by rw [map_add, star_add, add_mul, map_add]
  smul_left := by simp [smul_mul_assoc]

noncomputable instance : SeminormedAddCommGroup f.preGNS :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := f.preGNSInnerProdSpace)
noncomputable instance : InnerProductSpace ℂ f.preGNS :=
  InnerProductSpace.ofCore f.preGNSInnerProdSpace

lemma preGNS_inner_def (a b : f.preGNS) :
    ⟪a, b⟫_ℂ = f (star (f.ofPreGNS a) * f.ofPreGNS b) := rfl

lemma preGNS_norm_def (a : f.preGNS) :
    ‖a‖ = (f (star (f.ofPreGNS a) * f.ofPreGNS a)).re.sqrt := rfl

lemma preGNS_norm_sq (a : f.preGNS) :
    ‖a‖ ^ 2 = (f (star (f.ofPreGNS a) * f.ofPreGNS a)) := by
  have : 0 ≤ f (star (f.ofPreGNS a) * f.ofPreGNS a) := map_nonneg f <| star_mul_self_nonneg _
  rw [preGNS_norm_def, ← ofReal_pow, Real.sq_sqrt]
  · rw [conj_eq_iff_re.mp this.star_eq]
  · rwa [re_nonneg_iff_nonneg this.isSelfAdjoint]

/--
The Hilbert space constructed from a positive linear functional on a C⋆-algebra.
-/
abbrev GNS := UniformSpace.Completion f.preGNS

/--
The continuous linear map from a C⋆-algebra `A` to the `PositiveLinearMap.preGNS` space induced by
a positive linear functional `f : A →ₚ[ℂ] ℂ`. This map is given by left-multiplication by `a`:
`fun (a : A) (x : f.preGNS) ↦ f.toPreGNS (a * f.ofPreGNS x)`.
-/
@[simps!]
noncomputable def leftMulMapPreGNS (a : A) : f.preGNS →L[ℂ] f.preGNS :=
  f.toPreGNS.toLinearMap ∘ₗ mul ℂ A a ∘ₗ f.ofPreGNS.toLinearMap |>.mkContinuous ‖a‖ fun x ↦ by
    rw [← sq_le_sq₀ (by positivity) (by positivity), mul_pow, ← RCLike.ofReal_le_ofReal (K := ℂ),
      RCLike.ofReal_pow, RCLike.ofReal_eq_complex_ofReal, preGNS_norm_sq]
    have : star (f.ofPreGNS x) * star a * (a * f.ofPreGNS x) ≤
        ‖a‖ ^ 2 • star (f.ofPreGNS x) * f.ofPreGNS x := by
      rw [← mul_assoc, mul_assoc _ (star a), sq, ← CStarRing.norm_star_mul_self (x := a),
        smul_mul_assoc]
      exact CStarAlgebra.star_left_conjugate_le_norm_smul
    calc
      _ ≤ f (‖a‖ ^ 2 • star (f.ofPreGNS x) * f.ofPreGNS x) := by
        simpa using OrderHomClass.mono f this
      _ = _ := by simp [← Complex.coe_smul, preGNS_norm_sq, smul_mul_assoc]

@[simp]
lemma leftMulMapPreGNS_mul_eq_comp (a b : A) :
    f.leftMulMapPreGNS (a * b) = f.leftMulMapPreGNS a ∘ f.leftMulMapPreGNS b := by
  ext c; simp [mul_assoc]

/--
The non-unital ⋆-homomorphism/⋆-representation of A into the bounded operators on a Hilbert space
that is constructed from a positive linear functional `f` on a possibly non-unital C⋆-algebra.
-/
noncomputable def gnsNonUnitalStarAlgHom : A →⋆ₙₐ[ℂ] (f.GNS →L[ℂ] f.GNS) where
  toFun a := completion (f.leftMulMapPreGNS a)
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
      have := map_coe (f.leftMulMapPreGNS a ∘L f.leftMulMapPreGNS b).uniformContinuous
      simp_all [mul_assoc]
  map_star' a := by
    refine (eq_adjoint_iff (completion (f.leftMulMapPreGNS (star a)))
      (completion (f.leftMulMapPreGNS a))).mpr ?_
    intro x y
    induction x, y using Completion.induction_on₂ with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x y => simp [mul_assoc, preGNS_inner_def]

lemma gnsNonUnitalStarAlgHom_apply {a : A} :
    f.gnsNonUnitalStarAlgHom a = completion (f.leftMulMapPreGNS a) := rfl

@[simp]
lemma gnsNonUnitalStarAlgHom_apply_coe {a : A} {b : f.preGNS} :
    f.gnsNonUnitalStarAlgHom a b = f.leftMulMapPreGNS a b := by
  simp [gnsNonUnitalStarAlgHom_apply]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (f : A →ₚ[ℂ] ℂ)

@[simp]
private lemma gnsNonUnitalStarAlgHom_map_one : f.gnsNonUnitalStarAlgHom 1 = 1 := by
  ext b
  induction b using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih b => simp [gnsNonUnitalStarAlgHom]

/--
The unital ⋆-homomorphism/⋆-representation of A into the bounded operators on a Hilbert space
that is constructed from a positive linear functional `f` on a unital C⋆-algebra.
-/
@[simps]
noncomputable def gnsStarAlgHom : A →⋆ₐ[ℂ] (f.GNS →L[ℂ] f.GNS) where
  __ := f.gnsNonUnitalStarAlgHom
  map_one' := by simp
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one]

end PositiveLinearMap
