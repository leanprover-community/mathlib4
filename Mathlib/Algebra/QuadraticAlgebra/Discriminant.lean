/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.AlgHom
public import Mathlib.Data.Nat.Prime.Int

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

/-- `discr a b = b ^ 2 + 4 * a ≡ 0, 1 mod 4` for every `a b : ℤ`. -/
theorem discr_emod_four (a b : ℤ) : discr a b % 4 = 0 ∨ discr a b % 4 = 1 := by
  rw [discr_def]; have := Int.sq_emod_four b; lia

/-- The discriminant commutes with a base change `R → S`. -/
@[simp]
theorem discr_algebraMap {S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] (a b : R) :
    discr (algebraMap R S a) (algebraMap R S b) = algebraMap R S (discr a b) := by
  simp [discr_def, map_ofNat]

/-- `z.im ^ 2` times the discriminant of the algebra equals `trace z ^ 2 - 4 * norm z`. -/
theorem im_sq_mul_discr [CommRing R] {a b : R} (z : QuadraticAlgebra R a b) :
    z.im ^ 2 * discr a b = trace z ^ 2 - 4 * norm z := by
  rw [trace_def, norm_def, discr_def]; ring

/-- `im_sq_mul_discr` solved for `4 * norm z`. -/
theorem four_mul_norm_eq [CommRing R] {a b : R} (z : QuadraticAlgebra R a b) :
    4 * norm z = trace z ^ 2 - discr a b * z.im ^ 2 := by
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

/-- The transformation law for an injective algebra map. -/
theorem discr_eq_im_sq_mul_discr (hf : Function.Injective f) :
    discr a b = (f ω).im ^ 2 * discr a' b' := by
  rw [im_sq_mul_discr (f ω), trace_algHom_omega f hf, norm_algHom_omega f hf, discr_def]
  ring

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

@[simp]
theorem re_algEquivDiscrZero_apply [Invertible (2 : R)] (z : QuadraticAlgebra R a b) :
    (algEquivDiscrZero a b z).re = z.re + ⅟2 * b * z.im := by
  simp [algEquivDiscrZero, mul_comm]

@[simp]
theorem im_algEquivDiscrZero_apply [Invertible (2 : R)] (z : QuadraticAlgebra R a b) :
    (algEquivDiscrZero a b z).im = ⅟2 * z.im := by
  simp [algEquivDiscrZero, mul_comm]

@[simp]
theorem re_algEquivDiscrZero_symm_apply [Invertible (2 : R)]
    (z : QuadraticAlgebra R (discr a b) 0) :
    ((algEquivDiscrZero a b).symm z).re = z.re - b * z.im := by
  simp [algEquivDiscrZero, mul_comm, sub_eq_add_neg]

@[simp]
theorem im_algEquivDiscrZero_symm_apply [Invertible (2 : R)]
    (z : QuadraticAlgebra R (discr a b) 0) :
    ((algEquivDiscrZero a b).symm z).im = 2 * z.im := by
  simp [algEquivDiscrZero, mul_comm]

@[simp]
theorem algEquivDiscrZero_apply_add_smul [Invertible (2 : R)] (x y : R) :
    algEquivDiscrZero a b (x • 1 + y • ω) = (x + ⅟2 * b * y) • 1 + (⅟2 * y) • ω := by
  ext <;> simp [mul_comm]

@[simp]
theorem algEquivDiscrZero_symm_apply_add_smul [Invertible (2 : R)] (x y : R) :
    (algEquivDiscrZero a b).symm (x • 1 + y • ω) = (x - b * y) • 1 + (2 * y) • ω := by
  ext <;> simp [mul_comm, sub_eq_add_neg]

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
