/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Nonsingular

/-!
# Discriminant of a quadratic algebra

This file introduces the discriminant of a quadratic algebra `QuadraticAlgebra R a b` (with the
convention `ω² = a + b·ω`), describes how it transforms under a change of generator, and derives
the classification of quadratic algebras up to isomorphism together with a criterion, over a
field, for `QuadraticAlgebra K a b` to be a field.

## Main definitions

* `QuadraticAlgebra.discr`: the discriminant `discr a b = b ^ 2 + 4 * a`.

## Main results

* `QuadraticAlgebra.discr_changeGenerator`: the discriminant scales by `u ^ 2` under the change
  of generator `ω ↦ u • ω + k`.
* `QuadraticAlgebra.exists_sq_eq_iff_isSquare_discr`: over a ring with `2` invertible,
  `X ^ 2 - b * X - a` has a root iff `discr a b` is a square.
* `QuadraticAlgebra.nonempty_algEquiv_iff_of_invertible_two` and
  `QuadraticAlgebra.nonempty_algEquiv_int_iff`: the discriminant classifies quadratic algebras
  up to isomorphism, modulo squares of units when `2` is invertible and exactly over `ℤ`.
* `QuadraticAlgebra.isField_iff_not_isSquare_discr`: over a field with `2 ≠ 0`,
  `QuadraticAlgebra K a b` is a field iff `discr a b` is not a square.
-/

@[expose] public section

namespace QuadraticAlgebra

variable {R : Type*}

section discr

/-- The discriminant of the quadratic algebra `QuadraticAlgebra R a b`, that is, the
discriminant `b ^ 2 + 4 * a` of the polynomial `X ^ 2 - b * X - a`. -/
def discr [CommSemiring R] (a b : R) : R := b ^ 2 + 4 * a

theorem discr_def [CommSemiring R] (a b : R) : discr a b = b ^ 2 + 4 * a := rfl

/-- `z.im ^ 2` times the discriminant of the algebra equals `trace z ^ 2 - 4 * norm z`. -/
theorem im_sq_mul_discr [CommRing R] {a b : R} (z : QuadraticAlgebra R a b) :
    z.im ^ 2 * discr a b = trace z ^ 2 - 4 * norm z := by
  rw [trace_def, norm_def, discr_def]; ring

/-- Under the change of generator `ω ↦ u • ω + k` (see `QuadraticAlgebra.changeGenerator`), the
discriminant is multiplied by `u ^ 2`. -/
theorem discr_changeGenerator [CommRing R] (a b u k : R) :
    discr (u ^ 2 * a - u * b * k - k ^ 2) (u * b + 2 * k) = u ^ 2 * discr a b := by
  rw [discr_def, discr_def]; ring

@[deprecated (since := "2026-08-14")] alias discr_map := discr_changeGenerator

/-- The discriminant is the square of the different `ω - star ω`. -/
theorem algebraMap_discr [CommRing R] (a b : R) :
    algebraMap R (QuadraticAlgebra R a b) (discr a b) = (ω - star ω) ^ 2 := by
  rw [discr_def]; ext <;> simp [sq] <;> ring

-- The `a = 1` case of `Mathlib.Algebra.QuadraticDiscriminant`, reproved to avoid its heavy
-- transitive import of `Mathlib.Order.Filter.AtTopBot.Field`.
/-- If `2` is invertible, the polynomial `X ^ 2 - b * X - a` has a root if and only if the
discriminant is a square. -/
theorem exists_sq_eq_iff_isSquare_discr [CommRing R] [Invertible (2 : R)] {a b : R} :
    (∃ r : R, r ^ 2 = a + b * r) ↔ IsSquare (discr a b) := by
  rw [isSquare_iff_exists_sq, discr_def]
  exact ⟨fun ⟨r, hr⟩ ↦ ⟨2 * r - b, by grind⟩,
    fun ⟨r, hr⟩ ↦ ⟨⅟2 * (b + r), by grind [mul_invOf_self (2 : R)]⟩⟩

end discr

section classification

variable [CommRing R] {a b a' b' : R}
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

/-- The transformation law for an injective algebra map. -/
theorem discr_eq_im_sq_mul_discr (hf : Function.Injective f) :
    discr a b = (f ω).im ^ 2 * discr a' b' := by
  rw [im_sq_mul_discr (f ω), trace_algHom_omega f hf, norm_algHom_omega f hf, discr_def]
  ring

/-- Any `R`-algebra isomorphism between quadratic algebras sends `ω` to an element
whose imaginary part is a unit. -/
theorem isUnit_im_omega_of_algEquiv (e : QuadraticAlgebra R a b ≃ₐ[R] QuadraticAlgebra R a' b') :
    IsUnit (e ω).im := by
  have h := e.toLinearEquiv.isUnit_det (basis a b) (basis a' b')
  rwa [show (LinearMap.toMatrix (basis a b) (basis a' b')) e.toLinearEquiv.toLinearMap
      = (LinearMap.toMatrix (basis a b) (basis a' b')) e.toAlgHom.toLinearMap from rfl,
    det_toMatrix_algHom] at h

/-- `discr_eq_im_sq_mul_discr` for an `R`-algebra isomorphism `e`, for which `(e ω).im` is
automatically a unit (`isUnit_im_omega_of_algEquiv`). -/
theorem discr_eq_im_sq_mul_discr' (e : QuadraticAlgebra R a b ≃ₐ[R] QuadraticAlgebra R a' b') :
    discr a b = (e ω).im ^ 2 * discr a' b' := by
  rw [discr_eq_im_sq_mul_discr e.toAlgHom, AlgEquiv.toAlgHom_apply]
  exact e.injective

/-- If `2` is a unit, `QuadraticAlgebra R a b` is isomorphic to the standard form
`QuadraticAlgebra R (discr a b) 0`. -/
def algEquivDiscrZero [Invertible (2 : R)] (a b : R) :
    QuadraticAlgebra R a b ≃ₐ[R] QuadraticAlgebra R (discr a b) 0 :=
  (changeGeneratorEquiv a b (unitOfInvertible (2 : R)) (-b)
    (by grind [discr_def, val_unitOfInvertible]) (by grind [val_unitOfInvertible])).symm

/-- If `2` is regular, `QuadraticAlgebra R a b` and `QuadraticAlgebra R a' b'` are isomorphic
iff `discr a b = u ^ 2 * discr a' b'` for some unit `u` with `2 ∣ b - u * b'`. -/
theorem nonempty_algEquiv_iff (h : IsRegular (2 : R)) :
    Nonempty (QuadraticAlgebra R a b ≃ₐ[R] QuadraticAlgebra R a' b') ↔
      ∃ u : Rˣ, discr a b = (u : R) ^ 2 * discr a' b' ∧ 2 ∣ (b - u * b') := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun ⟨u, hu, ⟨k, hk⟩⟩ ↦ ⟨changeGeneratorEquiv a' b' u k ?_ (by grind)⟩⟩
  · refine ⟨(isUnit_im_omega_of_algEquiv e).unit,
      by rw [discr_eq_im_sq_mul_discr' e, IsUnit.unit_spec], ⟨(e ω).re, ?_⟩⟩
    rw [IsUnit.unit_spec, sub_eq_iff_eq_add', add_comm, mul_comm _ b', ← trace_def, eq_comm]
    exact trace_algHom_omega e.toAlgHom e.injective
  · rw [discr_def, discr_def] at hu
    rw [← h.left.eq_iff, mul_sub, mul_sub, ← mul_rotate, ← mul_assoc, ← mul_assoc, ← mul_assoc,
      ← hk, ← h.left.eq_iff, mul_sub, ← mul_assoc, ← mul_assoc, ← pow_two, ← mul_pow, ← hk]
    grind

/-- If `2` is invertible, the discriminant classifies quadratic algebras up to
isomorphism, modulo squares of units. -/
theorem nonempty_algEquiv_iff_of_invertible_two [Invertible (2 : R)] :
    Nonempty (QuadraticAlgebra R a b ≃ₐ[R] QuadraticAlgebra R a' b') ↔
      ∃ u : Rˣ, discr a b = (u : R) ^ 2 * discr a' b' := by
  rw [nonempty_algEquiv_iff (isUnit_of_invertible (2 : R)).isRegular]
  simp [(isUnit_of_invertible (2 : R)).dvd]

/-- Over `ℤ` the discriminant is a complete invariant of quadratic algebras up to
isomorphism. -/
theorem nonempty_algEquiv_int_iff {a b a' b' : ℤ} :
    Nonempty (QuadraticAlgebra ℤ a b ≃ₐ[ℤ] QuadraticAlgebra ℤ a' b') ↔
      discr a b = discr a' b' := by
  rw [nonempty_algEquiv_iff (IsRegular.of_ne_zero two_ne_zero)]
  refine ⟨fun ⟨u, hu, _⟩ ↦ by rwa [Int.isUnit_sq u.isUnit, one_mul] at hu, fun h ↦ ?_⟩
  obtain _ | _ : 2 ∣ (b + b') ∨ 2 ∣ (b - b') := by
    rw [← Prime.dvd_mul Int.prime_two, ← sq_sub_sq]
    refine ⟨2 * a' - 2 * a, ?_⟩
    rwa [mul_sub, ← mul_assoc, ← mul_assoc, show (2 : ℤ) * 2 = 4 by norm_num,
      sub_eq_sub_iff_add_eq_add, ← discr_def, add_comm, ← discr_def]
  · exact ⟨-1, by simpa, by simpa⟩
  · exact ⟨1, by simpa, by simpa⟩

end classification

section field

-- This `Fact (∀ r, r ^ 2 ≠ …)` instance is the bridge that lets the `Field` instance on
-- `QuadraticAlgebra K a b` fire from `¬ IsSquare (discr a b)` alone (the `b = 0` bridge from
-- `¬ IsSquare a` lives in `Basic.lean`).
instance {K : Type*} [Field K] {a b : K} [NeZero (2 : K)] [Fact (¬ IsSquare (discr a b))] :
    Fact (∀ r : K, r ^ 2 ≠ a + b * r) :=
  letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  ⟨not_exists.mp <| exists_sq_eq_iff_isSquare_discr.not.mpr Fact.out⟩

variable {K : Type*} [Field K]

/-- If `discr a b` is a square, `QuadraticAlgebra K a b` is not a field. -/
theorem not_isField_of_isSquare_discr [NeZero (2 : K)] {a b : K}
    (h : IsSquare (discr a b)) : ¬ IsField (QuadraticAlgebra K a b) := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  obtain ⟨r, hr⟩ := exists_sq_eq_iff_isSquare_discr.mpr h
  intro hfield
  let := hfield.toField
  have : (⟨r, -1⟩ : QuadraticAlgebra K a b) ∈ nonZeroDivisors (QuadraticAlgebra K a b) := by
    simp [mem_nonZeroDivisors_iff_ne_zero, QuadraticAlgebra.ext_iff]
  rw [← norm_mem_nonZeroDivisors_iff, show norm ⟨r, -1⟩ = 0 by rw [norm_def]; grind] at this
  exact zero_notMem_nonZeroDivisors this

/-- If `2 ≠ 0` in the field `K`, `QuadraticAlgebra K a b` is a field iff `discr a b` is
not a square. -/
theorem isField_iff_not_isSquare_discr [NeZero (2 : K)] {a b : K} :
    IsField (QuadraticAlgebra K a b) ↔ ¬ IsSquare (discr a b) := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  refine ⟨fun hfield h ↦ not_isField_of_isSquare_discr h hfield, fun h ↦ ?_⟩
  have : Fact (¬ IsSquare (discr a b)) := ⟨h⟩
  exact Field.toIsField (QuadraticAlgebra K a b)

-- The general bridge makes the `Field` instance inferable from `¬ IsSquare (discr a b)`
-- if `2 ≠ 0` in the field.
example {a b : ℚ} [Fact (¬ IsSquare (discr a b))] : Field (QuadraticAlgebra ℚ a b) := inferInstance

end field

end QuadraticAlgebra
