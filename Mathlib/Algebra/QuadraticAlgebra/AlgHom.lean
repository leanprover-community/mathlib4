/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Algebra homomorphisms between quadratic algebras

An `R`-algebra homomorphism `f : QuadraticAlgebra R a b →ₐ[R] QuadraticAlgebra R a' b'` is
determined by the image of `ω`, and its matrix in the bases `1, ω` is `[1, (f ω).re; 0, (f ω).im]`.
Furthermore `f` is injective exactly when `(f ω).im` is regular, bijective exactly when it is
a unit. Finally, an injective `f` preserves the trace and the norm, and commutes with conjugation.

## Main results

* `QuadraticAlgebra.toMatrix_algHom`, `QuadraticAlgebra.det_toMatrix_algHom`: the matrix of `f` in
  the bases `1, ω` is `[1, (f ω).re; 0, (f ω).im]`, whose determinant is `(f ω).im`.
* `QuadraticAlgebra.isRegular_im_omega_iff_injective`: `f` is injective iff `(f ω).im` is regular.
* `QuadraticAlgebra.isUnit_im_omega_iff_bijective`: `f` is bijective iff `(f ω).im` is a unit.
* `QuadraticAlgebra.isUnit_im_omega_of_algEquiv`: for an algebra isomorphism, `(e ω).im` is a unit.
* `QuadraticAlgebra.trace_algHom`, `QuadraticAlgebra.algHom_star`, `QuadraticAlgebra.norm_algHom`:
  an injective algebra homomorphism preserves the trace and the norm, and commutes with conjugation.
-/

@[expose] public section

namespace QuadraticAlgebra

variable {R : Type*} [CommRing R] {a b a' b' : R}
  (f : QuadraticAlgebra R a b →ₐ[R] QuadraticAlgebra R a' b')

private theorem smul_omega_sub_eq :
    (trace (f ω) - b) • f ω = algebraMap R _ (norm (f ω)) + a • 1 := by
  rw [sub_smul, ← sub_neg_eq_add, sub_eq_sub_iff_sub_eq_sub, ← sq_eq_trace_smul_sub_norm]
  grind [omega_pow_two_eq_add, map_smul, _=_ map_pow]

/-- The matrix of an algebra homomorphism `f` between quadratic algebras in the bases `1, ω` is
`[1, (f ω).re; 0, (f ω).im]` since `f 1 = 1`. In particular, its determinant is `(f ω).im`,
see `det_toMatrix_algHom`. -/
theorem toMatrix_algHom :
    f.toLinearMap.toMatrix (basis a b) (basis a' b') = !![1, (f ω).re; 0, (f ω).im] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply]

/-- The determinant of an algebra homomorphism `f` between quadratic algebras, in the bases `1, ω`,
is `(f ω).im`. -/
theorem det_toMatrix_algHom :
    (f.toLinearMap.toMatrix (basis a b) (basis a' b')).det = (f ω).im := by
  simp [toMatrix_algHom, Matrix.det_fin_two]

private theorem mulVec_toMatrix_comp_eq :
    (f.toLinearMap.toMatrix (basis a b) (basis a' b')).mulVec ∘ (basis a b).equivFun =
      (basis a' b').equivFun ∘ f :=
  funext fun x ↦ LinearMap.toMatrix_mulVec_repr (basis a b) (basis a' b') f.toLinearMap x

/-- An algebra homomorphism `f` between quadratic algebras is injective exactly when `(f ω).im` is
regular, which is the determinant of `f` in the bases `1, ω`, see `det_toMatrix_algHom`. -/
theorem isRegular_im_omega_iff_injective :
    IsRegular (f ω).im ↔ Function.Injective f := by
  rw [← det_toMatrix_algHom, isRegular_iff_mem_nonZeroDivisors,
    ← Matrix.nonsingular_iff_det_mem_nonZeroDivisors, ← Matrix.isLeftRegular_iff_nonsingular,
    Matrix.isLeftRegular_iff_mulVec_injective,
    ← Function.Injective.of_comp_iff' _ (basis a b).equivFun.bijective,
    ← (basis a' b').equivFun.injective.of_comp_iff, mulVec_toMatrix_comp_eq]

/-- An algebra homomorphism `f` between quadratic algebras is bijective exactly when `(f ω).im` is
a unit, the injective case being `isRegular_im_omega_iff_injective`. -/
theorem isUnit_im_omega_iff_bijective :
    IsUnit (f ω).im ↔ Function.Bijective f := by
  suffices Function.Surjective f ↔ IsUnit (f ω).im by
    rw [Function.Bijective, ← isRegular_im_omega_iff_injective, this, iff_and_self]
    exact fun h ↦ IsUnit.isRegular h
  rw [← det_toMatrix_algHom, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_surjective_iff_isUnit,
    ← Function.Surjective.of_comp_iff' (basis a' b').equivFun.bijective,
    ← (basis a b).equivFun.surjective.of_comp_iff, mulVec_toMatrix_comp_eq]

/-- Any `R`-algebra isomorphism between quadratic algebras sends `ω` to an element
whose imaginary part is a unit. -/
theorem isUnit_im_omega_of_algEquiv (e : QuadraticAlgebra R a b ≃ₐ[R] QuadraticAlgebra R a' b') :
    IsUnit (e ω).im :=
  (isUnit_im_omega_iff_bijective e.toAlgHom).mpr e.bijective

/-- An injective algebra homomorphism sends `ω` to an element of trace `b`. -/
theorem trace_algHom_omega (hf : Function.Injective f) :
    trace (f ω) = b := by
  have h := (isRegular_im_omega_iff_injective f).mpr hf
  simpa [h.right.mul_right_eq_zero_iff, sub_eq_zero] using congr_arg im (smul_omega_sub_eq f)

/-- An injective algebra homomorphism sends `ω` to an element of norm `-a`. -/
theorem norm_algHom_omega (hf : Function.Injective f) :
    norm (f ω) = -a := by
  simpa [trace_algHom_omega f hf, ← Algebra.algebraMap_eq_smul_one, add_eq_zero_iff_eq_neg,
    ← map_neg] using (smul_omega_sub_eq f).symm

/-- An injective algebra homomorphism preserves traces. -/
theorem trace_algHom (hf : Function.Injective f) (x : QuadraticAlgebra R a b) :
    trace (f x) = trace x := by
  rw [← re_smul_add_im_smul x]
  simp [trace_algHom_omega f hf, mul_comm]

/-- An injective algebra homomorphism commutes with conjugation. -/
theorem algHom_star (hf : Function.Injective f) (x : QuadraticAlgebra R a b) :
    f (star x) = star (f x) := by
  rw [star_eq, map_sub, AlgHom.commutes, star_eq (f x), trace_algHom f hf]

/-- An injective algebra homomorphism preserves norms. -/
theorem norm_algHom (hf : Function.Injective f) (x : QuadraticAlgebra R a b) :
    norm (f x) = norm x := by
  apply algebraMap_injective
  rw [algebraMap_norm_eq_mul_star, ← algHom_star f hf, ← map_mul, ← algebraMap_norm_eq_mul_star,
    AlgHom.commutes]

end QuadraticAlgebra
