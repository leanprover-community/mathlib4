/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Int.Basic

/-!
# Quadratic Number Fields

This file defines quadratic number fields `ℚ(√d)` as specializations of the
`QuadraticAlgebra` construction, and establishes that they are number fields.

## Main Definitions

* `Qsqrtd d` : The quadratic algebra `QuadraticAlgebra ℚ d 0`, representing `ℚ(√d)`.
* `QuadFieldParam d` : Class asserting that `d : ℤ` is a valid parameter for a quadratic
  number field (squarefree and `d ≠ 1`).
* `QuadraticNumberField d` : The quadratic number field `ℚ(√d)` for a valid parameter `d`.

## Main Results

* `Qsqrtd.zero_not_isReduced` : `ℚ(√0)` is not reduced (has nilpotents).
* `Qsqrtd.one_not_isField` : `ℚ(√1) ≅ ℚ × ℚ` is not a field (has zero divisors).
* `QuadFieldParam.not_isSquare` : A valid parameter is not a perfect square in `ℤ`.
* `QuadraticNumberField.instField` : `ℚ(√d)` is a field for valid parameters.
* `QuadraticNumberField.instNumberField` : `ℚ(√d)` is a number field.
* `QuadraticNumberField.instIsQuadraticExtension` : `ℚ(√d)/ℚ` is a degree-2 extension.

## Implementation Notes

The type `Qsqrtd d` is defined for any `d : ℚ`, while `QuadraticNumberField d` requires
`d : ℤ` with a `QuadFieldParam d` instance (squarefree, `d ≠ 1`). The `QuadFieldParam`
class packages exactly the conditions needed to ensure `ℚ(√d)` is a field.

Common instances are provided for `-1`, `-3`, and any `d` with `|d|` prime.

## Tags

quadratic field, number field, quadratic extension
-/

@[expose] public section

/-- The quadratic field `ℚ(√d)` as a type alias for `QuadraticAlgebra ℚ d 0`. -/
abbrev Qsqrtd (d : ℚ) : Type := QuadraticAlgebra ℚ d 0

namespace Qsqrtd

variable {d : ℚ}

/-- The norm of `x : ℚ(√d)`, defined as `N(x) = x · x̄ = x.re² - d · x.im²`. -/
abbrev norm (x : Qsqrtd d) : ℚ := QuadraticAlgebra.norm x

/-! ### Degeneracies -/

/-- `ℚ(√0)` is not reduced because `√0² = 0` but `√0 ≠ 0`. -/
theorem zero_not_isReduced : ¬IsReduced (Qsqrtd (0 : ℚ)) := by
  intro ⟨h⟩
  have hnil : IsNilpotent (⟨0, 1⟩ : Qsqrtd 0) :=
    ⟨2, by ext <;> simp [pow_succ, pow_zero, QuadraticAlgebra.mk_mul_mk]⟩
  have hne : (⟨0, 1⟩ : Qsqrtd 0) ≠ 0 := by
    intro heq; exact one_ne_zero (congr_arg QuadraticAlgebra.im heq)
  exact hne (h _ hnil)

/-- `ℚ(√0)` is not a field (it has nilpotents). -/
theorem zero_not_isField : ¬IsField (Qsqrtd (0 : ℚ)) := by
  intro hF
  haveI := hF.isDomain
  exact zero_not_isReduced (inferInstance : IsReduced (Qsqrtd (0 : ℚ)))

/-- `ℚ(√1) ≅ ℚ × ℚ` is not a field (it has zero divisors). -/
theorem one_not_isField : ¬IsField (Qsqrtd (1 : ℚ)) := by
  intro hF
  haveI := hF.isDomain
  have hprod : (⟨1, 1⟩ : Qsqrtd 1) * ⟨1, -1⟩ = 0 := by
    ext <;> simp
  have hne : (⟨1, 1⟩ : Qsqrtd 1) ≠ 0 := by
    intro h; exact one_ne_zero (congr_arg QuadraticAlgebra.re h)
  have hne' : (⟨1, -1⟩ : Qsqrtd 1) ≠ 0 := by
    intro h; exact one_ne_zero (congr_arg QuadraticAlgebra.re h)
  rcases mul_eq_zero.mp hprod with h | h <;> contradiction

end Qsqrtd

/-! ## Quadratic Field Parameters -/

/-- Parameters for quadratic number fields `ℚ(√d)`.

A valid parameter is a squarefree integer `d ≠ 1`. The condition `d ≠ 0`
is not stored as a field since it follows from `Squarefree.ne_zero`. -/
class QuadFieldParam (d : ℤ) : Prop where
  squarefree : Squarefree d
  ne_one : d ≠ 1

namespace QuadFieldParam

private lemma eq_one_of_squarefree_isSquare {d : ℤ} (hd : Squarefree d)
    (hsq : IsSquare d) : d = 1 := by
  rcases hsq with ⟨z, hz⟩
  by_cases huz : IsUnit z
  · rcases Int.isUnit_iff.mp huz with hz1 | hz1 <;> simpa [hz1] using hz
  · have hsqz2 : Squarefree (z ^ 2) := by simpa [hz, pow_two] using hd
    have h01 : (2 : ℕ) = 0 ∨ (2 : ℕ) = 1 :=
      Squarefree.eq_zero_or_one_of_pow_of_not_isUnit (x := z) (n := 2) hsqz2 huz
    norm_num at h01

/-- For a quadratic parameter, nonzero follows from squarefreeness. -/
theorem ne_zero (d : ℤ) [QuadFieldParam d] : d ≠ 0 :=
  (QuadFieldParam.squarefree (d := d)).ne_zero

/-- For a valid parameter `d`, the integer `d` is not a perfect square. -/
theorem not_isSquare (d : ℤ) [QuadFieldParam d] : ¬IsSquare d := by
  intro hdSq
  exact (QuadFieldParam.ne_one (d := d))
    (eq_one_of_squarefree_isSquare (QuadFieldParam.squarefree (d := d)) hdSq)

/-- Any squarefree `d ≠ 1` is a valid quadratic-field parameter. -/
theorem of_squarefree_ne_one (d : ℤ) (hd : Squarefree d) (h1 : d ≠ 1) :
    QuadFieldParam d :=
  { squarefree := hd, ne_one := h1 }

/-- A prime integer gives a valid quadratic-field parameter. -/
theorem of_prime (d : ℤ) (hd : Prime d) : QuadFieldParam d := by
  refine of_squarefree_ne_one d hd.squarefree ?_
  intro h1
  exact hd.not_unit (h1 ▸ isUnit_one)

/-- If `|d|` is prime, then `d` is a valid quadratic-field parameter. -/
theorem of_natAbs_prime (d : ℤ) (hd : Nat.Prime d.natAbs) :
    QuadFieldParam d :=
  of_prime d (Int.prime_iff_natAbs_prime.2 hd)

end QuadFieldParam

/-! ### Common Parameter Instances -/

/-- Instance for any `d` where `|d|` is prime (via `Fact`). -/
instance (d : ℤ) [Fact (Nat.Prime d.natAbs)] : QuadFieldParam d :=
  QuadFieldParam.of_natAbs_prime d (Fact.out)

/-- Instance for any squarefree `d ≠ 1` (via `Fact`). -/
instance (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] : QuadFieldParam d :=
  QuadFieldParam.of_squarefree_ne_one d (Fact.out) (Fact.out)

/-- The Gaussian field `ℚ(√(-1)) = ℚ(i)` has valid parameter `-1`. -/
instance : QuadFieldParam (-1) where
  squarefree := by simp
  ne_one := by decide

/-- The Eisenstein field `ℚ(√(-3))` has valid parameter `-3`. -/
instance : QuadFieldParam (-3 : ℤ) := by
  letI : Fact (Nat.Prime ((-3 : ℤ).natAbs)) := ⟨by decide⟩
  exact inferInstance

/-! ## Quadratic Number Field -/

/-- The quadratic number field `ℚ(√d)` as a type, for valid parameter `d`. -/
abbrev QuadraticNumberField (d : ℤ) [QuadFieldParam d] : Type := Qsqrtd (d : ℚ)

namespace QuadraticNumberField

/-- `ℚ(√d)` is a field for any valid parameter `d`. -/
instance instField {d : ℤ} [QuadFieldParam d] : Field (QuadraticNumberField d) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) := ⟨by
    intro r hr
    have hsqQ : IsSquare ((d : ℤ) : ℚ) := ⟨r, by nlinarith [hr]⟩
    exact (QuadFieldParam.not_isSquare d) (Rat.isSquare_intCast_iff.mp hsqQ)
  ⟩
  infer_instance

/-- The `Module ℚ` instance from the `Field` algebra structure on `ℚ(√d)` coincides with
the `QuadraticAlgebra` module structure. This resolves the diamond between the two paths. -/
private theorem module_eq (d : ℤ) [QuadFieldParam d] :
    (Algebra.toModule : Module ℚ (QuadraticNumberField d)) =
      QuadraticAlgebra.instModule := by
  refine Module.ext' _ _ ?_
  intro r x
  rw [Algebra.smul_def]
  rw [show (algebraMap ℚ (QuadraticNumberField d) r) = QuadraticAlgebra.C r by
        ext <;> simp [QuadraticNumberField]]
  rw [QuadraticAlgebra.C_mul_eq_smul]

/-- `ℚ(√d)` is a number field: characteristic zero and finite-dimensional over `ℚ`. -/
instance instNumberField {d : ℤ} [QuadFieldParam d] :
    NumberField (QuadraticNumberField d) where
  to_charZero := by infer_instance
  to_finiteDimensional := by
    letI : Module ℚ (QuadraticNumberField d) := QuadraticAlgebra.instModule
    exact module_eq d ▸ (inferInstance : Module.Finite ℚ (QuadraticNumberField d))

/-- `ℚ(√d)/ℚ` is a quadratic extension: free of rank 2 over `ℚ`. -/
instance instIsQuadraticExtension {d : ℤ} [QuadFieldParam d] :
    Algebra.IsQuadraticExtension ℚ (QuadraticNumberField d) where
  finrank_eq_two' := module_eq d ▸ QuadraticAlgebra.finrank_eq_two (d : ℚ) 0

end QuadraticNumberField
