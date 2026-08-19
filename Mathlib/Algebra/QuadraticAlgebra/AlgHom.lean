/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Nonsingular

/-!
# Algebra maps between quadratic algebras

An `R`-algebra map `f : QuadraticAlgebra R a b →ₐ[R] QuadraticAlgebra R a' b'` is determined by
the image of `ω`, and its matrix in the bases `1, ω` is `!![1, (f ω).re; 0, (f ω).im]`. Its
determinant `(f ω).im` governs everything: `f` is injective exactly when `(f ω).im` is regular,
and an injective `f` preserves the trace, the conjugation and the norm.

## Main results

* `QuadraticAlgebra.isRegular_im_omega_iff_injective`: `f` is injective iff `(f ω).im` is regular.
* `QuadraticAlgebra.trace_algHom`, `QuadraticAlgebra.algHom_star`,
  `QuadraticAlgebra.norm_algHom`: an injective algebra map preserves trace, conjugation and norm.
* `QuadraticAlgebra.isUnit_im_omega_of_algEquiv`: for an algebra isomorphism, `(e ω).im` is a unit.
-/

@[expose] public section

namespace QuadraticAlgebra

variable {R : Type*} [CommRing R] {a b a' b' : R}
  (f : QuadraticAlgebra R a b →ₐ[R] QuadraticAlgebra R a' b')

private theorem smul_omega_sub_eq :
    (trace (f ω) - b) • f ω = algebraMap R _ (norm (f ω)) + a • 1 := by
  rw [sub_smul, ← sub_neg_eq_add, sub_eq_sub_iff_sub_eq_sub, ← sq_eq_trace_smul_sub_norm,
    sub_neg_eq_add, ← map_pow, sq, omega_mul_omega_eq_add, map_add, map_smul, map_smul, map_one,
    add_comm]

/-- The matrix of an algebra map `f` between quadratic algebras in the bases `1, ω` is
`[1, (f ω).re; 0, (f ω).im]` since `f 1 = 1`. In particular, its determinant is `(f ω).im`,
see `det_toMatrix_algHom`. -/
theorem toMatrix_algHom :
    f.toLinearMap.toMatrix (basis a b) (basis a' b') = !![1, (f ω).re; 0, (f ω).im] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply]

/-- The determinant of an algebra map `f` between quadratic algebras, in the bases `1, ω`,
is `(f ω).im`. -/
theorem det_toMatrix_algHom :
    (f.toLinearMap.toMatrix (basis a b) (basis a' b')).det = (f ω).im := by
  simp [toMatrix_algHom, Matrix.det_fin_two]

/-- An algebra map `f` between quadratic algebras is injective exactly when `(f ω).im` is
regular, that being the determinant of `f` in the bases `1, ω`, see `det_toMatrix_algHom`. -/
theorem isRegular_im_omega_iff_injective :
    IsRegular (f ω).im ↔ Function.Injective f := by
  have h : (f.toLinearMap.toMatrix (basis a b) (basis a' b')).mulVec ∘ (basis a b).equivFun =
      (basis a' b').equivFun ∘ f :=
    funext fun x ↦ LinearMap.toMatrix_mulVec_repr (basis a b) (basis a' b') f.toLinearMap x
  rw [isRegular_iff_mem_nonZeroDivisors, ← det_toMatrix_algHom,
    ← Matrix.nonsingular_iff_det_mem_nonZeroDivisors, ← Matrix.isLeftRegular_iff_nonsingular,
    Matrix.isLeftRegular_iff_mulVec_injective,
    ← Function.Injective.of_comp_iff' _ (basis a b).equivFun.bijective,
    ← (basis a' b').equivFun.injective.of_comp_iff, h]

/-- An injective algebra map sends `ω` to an element of trace `b`. -/
theorem trace_algHom_omega (hf : Function.Injective f) :
    trace (f ω) = b := by
  have h := (isRegular_im_omega_iff_injective f).mpr hf
  simpa [h.right.mul_right_eq_zero_iff, sub_eq_zero] using congr_arg im (smul_omega_sub_eq f)

/-- An injective algebra map sends `ω` to an element of norm `-a`. -/
theorem norm_algHom_omega (hf : Function.Injective f) :
    norm (f ω) = -a := by
  simpa [trace_algHom_omega f hf, ← Algebra.algebraMap_eq_smul_one, add_eq_zero_iff_eq_neg,
    ← map_neg] using (smul_omega_sub_eq f).symm

/-- An injective algebra map preserves traces. -/
theorem trace_algHom (hf : Function.Injective f) (x : QuadraticAlgebra R a b) :
    trace (f x) = trace x := by
  rw [← re_smul_add_im_smul x]
  simp [trace_algHom_omega f hf, mul_comm]

/-- An injective algebra map commutes with conjugation. -/
theorem algHom_star (hf : Function.Injective f) (x : QuadraticAlgebra R a b) :
    f (star x) = star (f x) := by
  rw [star_eq, map_sub, AlgHom.commutes, star_eq (f x), trace_algHom f hf]

/-- An injective algebra map preserves norms. -/
theorem norm_algHom (hf : Function.Injective f) (x : QuadraticAlgebra R a b) :
    norm (f x) = norm x := by
  apply algebraMap_injective
  rw [algebraMap_norm_eq_mul_star, ← algHom_star f hf, ← map_mul, ← algebraMap_norm_eq_mul_star,
    AlgHom.commutes]

/-- Any `R`-algebra isomorphism between quadratic algebras sends `ω` to an element
whose imaginary part is a unit. -/
theorem isUnit_im_omega_of_algEquiv (e : QuadraticAlgebra R a b ≃ₐ[R] QuadraticAlgebra R a' b') :
    IsUnit (e ω).im := by
  have h := e.toLinearEquiv.isUnit_det (basis a b) (basis a' b')
  rwa [show (LinearMap.toMatrix (basis a b) (basis a' b')) e.toLinearEquiv.toLinearMap
      = (LinearMap.toMatrix (basis a b) (basis a' b')) e.toAlgHom.toLinearMap from rfl,
    det_toMatrix_algHom] at h

end QuadraticAlgebra
