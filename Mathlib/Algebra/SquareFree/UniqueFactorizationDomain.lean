/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.SquareFree.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Square-free elements of unique factorization domains

## Main results:
 * `squarefree_mul_iff`: `x * y` is square-free iff `x` and `y` are coprime and each square-free.

-/

variable {R : Type*} [CommRing R] [IsDomain R] {x y p : R}

variable [IsPrincipalIdealRing R] [GCDMonoid R] -- Too strong
-- variable [UniqueFactorizationMonoid R] -- Should be sufficient

-- TODO Drop hypothesis `hp`
theorem dvd_right_of_squarefree_of_prime_of_mul_dvd_mul
    (hx : Squarefree x) (hp : Prime p) (h : p * p ∣ x * y) :
    p ∣ y := by
  by_contra contra
  replace contra : IsCoprime p y := hp.coprime_iff_not_dvd.mpr contra
  exact hp.not_unit (hx p <| (contra.mul_left contra).dvd_of_dvd_mul_right h)

-- TODO Drop hypothesis `hp`
theorem dvd_left_of_squarefree_of_prime_of_mul_dvd_mul
    (hy : Squarefree y) (hp : Prime p) (h : p * p ∣ x * y) :
    p ∣ x := by
  rw [mul_comm x y] at h
  exact dvd_right_of_squarefree_of_prime_of_mul_dvd_mul hy hp h

theorem squarefree_mul_iff :
    Squarefree (x * y) ↔ IsCoprime x y ∧ Squarefree x ∧ Squarefree y := by
  refine ⟨fun h ↦ ⟨?_, h.of_mul_left, h.of_mul_right⟩, fun ⟨hxy, hx, hy⟩ ↦ ?_⟩
  · refine isCoprime_of_prime_dvd (by contrapose! h; simp [h]) fun p hp hpx hpy ↦ ?_
    exact hp.not_unit <| h p (mul_dvd_mul hpx hpy)
  · intro d
    induction' d using UniqueFactorizationMonoid.induction_on_prime with _ hu _ p _ hp _
    · simp [hx.ne_zero, hy.ne_zero]
    · exact fun _ ↦ hu
    · intro contra
      exfalso
      apply hp.not_unit
      suffices p ∣ x ∧ p ∣ y by exact hxy.isUnit_of_dvd' this.1 this.2
      replace contra : p * p ∣ x * y := by
        rw [mul_mul_mul_comm] at contra; exact dvd_of_mul_right_dvd contra
      exact ⟨dvd_left_of_squarefree_of_prime_of_mul_dvd_mul hy hp contra,
        dvd_right_of_squarefree_of_prime_of_mul_dvd_mul hx hp contra⟩
