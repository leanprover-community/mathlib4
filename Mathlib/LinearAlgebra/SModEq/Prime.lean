/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.LinearAlgebra.SModEq.Basic
import Mathlib.RingTheory.Ideal.Operations

/-! # Lemmas for SModEq with prime powers -/

namespace SModEq

variable {R : Type*} [CommRing R] {I : Ideal R} {p : ℕ} (pr : p.Prime) (hpI : (p : R) ∈ I)
include pr hpI

theorem pow_prime {x y : R} {m : ℕ} (hm : m ≠ 0) (h : x ≡ y [SMOD I ^ m]) :
    x ^ p ≡ y ^ p [SMOD I ^ (m + 1)] := by
  rw [SModEq.sub_mem] at h ⊢
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq' pr (x - y) y
  rw [sub_add_cancel] at hr
  rw [hr, add_right_comm, add_sub_cancel_right, mul_assoc _ y]
  refine add_mem ?_ ?_
  · have := Ideal.pow_mem_pow h p
    rw [← pow_mul] at this
    exact I.pow_le_pow_right (by grw [add_one_le_two_mul (by grind), pr.two_le, mul_comm]) this
  · rw [pow_succ']
    exact Ideal.mul_mem_right _ _ <| I.mul_mem_mul hpI h

theorem pow_prime_pow {x y : R} (h : x ≡ y [SMOD I]) {m : ℕ} :
    x ^ p ^ m ≡ y ^ p ^ m [SMOD I ^ (m + 1)] := by
  induction m with
  | zero => simpa
  | succ m ih =>
    simp_rw [pow_succ _ m, pow_mul]
    exact ih.pow_prime pr hpI m.succ_ne_zero

end SModEq
