/-
Copyright (c) 2025 Gregory Wickham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Wickham
-/
module

public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.InnerProductSpace.Defs

/-!
# Positive linear functionals on C*-algebras

In this file we introduce establish some basic facts of positive linear functionals, which are
`PositiveLinearMaps` from a C*-algebra `A` to ℂ.

## Main results

- `re_of_isSelfAdjoint`: if `a` is a self-adjoint element of the C*-algebra, `f a` must
  be a real number.
- `re_of_self_star_self`: a useful corrollary that states that `f (a * star a)` is real for all
  `a` in `A`.
- `PreInnerProductSpaceOnA` : the `PreInnerProductSpace` structure over `A` induced by defining
  the inner product, `inner ℂ a b := f (star a * b)`.
- `induced_inner_mul_inner_self_le` : the inner product satisfies a version of the Cauchy-Schwarz
  inequality.
- `induced_inner_norm_sq_self_le` : the inner product satisfies the Cauchy-Schwarz inequality.
-/

@[expose] public section

open ComplexConjugate
open scoped ComplexOrder
open Complex

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

namespace PositiveLinearMap

/--
If `f` is a positive linear functional and `a` is self-adjoint, then `f a` is a real number.
-/
lemma re_of_isSelfAdjoint (a : A) (ha : IsSelfAdjoint a) : (f (a)).re = f (a) :=
  conj_eq_iff_re.mp (map_isSelfAdjoint f a ha)

/--
If `f` is a positive linear functional, then `f (a * star a)` is a real number.
-/
lemma re_of_self_star_self (a : A) : (f (a * star a)).re = f (a * star a) :=
  re_of_isSelfAdjoint f (a * star a) (IsSelfAdjoint.mul_star_self a)

/--
If `f` is a positive linear functional, then `f (a * star a)` is a real number.
-/
lemma re_of_star_mul_self (a : A) : (f (star a * a)).re = f (star a * a) := by
  have := f.re_of_self_star_self (star a)
  simp_all

/--
If `f` is a positive linear functional, then `f (star a * b)` is a semi-inner product
(positive semidefinite sesquilinear form) which makes `A` into a `PreInnerProductSpace`.
-/
private
noncomputable instance PreInnerProductSpaceOnA : PreInnerProductSpace.Core ℂ (A) where
  inner a b := f (star a * b)
  conj_inner_symm x y := by apply star_inj.mp; rw [← map_star f (star x * y)]; simp
  re_inner_nonneg x :=
    (RCLike.re_nonneg_of_nonneg (x := f (star x * x))
      (LE.le.isSelfAdjoint (PositiveLinearMap.map_nonneg f (star_mul_self_nonneg x)))).mpr
        (PositiveLinearMap.map_nonneg f (star_mul_self_nonneg x))
  add_left x y z := by rw [star_add, add_mul, map_add]
  smul_left x y r := by simp

/--
The semi-inner product `f (star a * b)` satisfies a version of the Cauchy-Schwarz inequality.
-/
theorem induced_inner_mul_inner_self_le (a b : A) :
    ‖f (star a * b)‖ * ‖f (star b * a)‖ ≤ RCLike.re (f (star a * a)) * RCLike.re (f (star b * b)) :=
  RCLike.ofReal_le_ofReal.mp
    (InnerProductSpace.Core.inner_mul_inner_self_le (c := PreInnerProductSpaceOnA f) a b)

/--
The semi-inner product `f (star a * b)` satisfies the Cauchy-Schwarz inequality.
-/
theorem induced_inner_norm_sq_self_le (a b : A) :
    norm (f (star a * b)) ^ 2 ≤ f (star a * a) * f (star b * b) := by
  have cs := induced_inner_mul_inner_self_le f a b
  apply Complex.real_le_real.mpr at cs
  have inner_re := InnerProductSpace.Core.inner_self_ofReal_re (c := PreInnerProductSpaceOnA f)
  nth_rw 2 [Complex.ofReal_mul] at cs
  have conj_symm := PreInnerProductSpace.Core.conj_inner_symm (PreInnerProductSpaceOnA f) a b
  have norm_eq_conj_norm : ↑‖(starRingEnd ℂ) ((PreInnerProductSpaceOnA f).inner b a)‖ =
    ↑‖(PreInnerProductSpaceOnA f).inner b a‖ := by simp
  have (a : A) (b : A) : (PreInnerProductSpaceOnA f).inner a b = f (star a * b) := by exact rfl
  simp_all only [ofReal_mul, RCLike.re_to_complex, coe_algebraMap, ← pow_two]

/--
If `f (star a * a) = 0`, then for all `b : A`, `f (star a * b) = 0`.
-/
lemma maps_zero_prod_to_zero
  (a b : A) (h : f (star a * a) = 0) : f (star a * b) = 0 := by
  have hab := induced_inner_norm_sq_self_le f a b
  rw [h, zero_mul] at hab
  rw [← norm_eq_zero]
  norm_cast at hab
  exact (_root_.sq_nonpos_iff ‖f (star a * b)‖).mp hab

/-
def toCLM : A →L[ℂ] ℂ where
  toFun := f
  map_add' := by simp
  map_smul' := by simp
-/
@[coe]
def PLF.toCLM (f : A →ₚ[ℂ] ℂ) : A →L[ℂ] ℂ where
  toFun := f
  map_add' := by simp
  map_smul' := by simp

instance : Coe (A →ₚ[ℂ] ℂ) (A →L[ℂ] ℂ) where
  coe := PLF.toCLM

noncomputable
instance : Norm (A →ₚ[ℂ] ℂ) where
  norm f := ‖(f : A →L[ℂ] ℂ)‖

-- I know this is true, but I will attempt to formalize the proof later
theorem opNorm_eq_of_one : ‖f‖ = f 1 := sorry

end PositiveLinearMap
