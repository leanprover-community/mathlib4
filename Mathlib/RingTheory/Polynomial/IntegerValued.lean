/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Binomial

import Mathlib.Algebra.Polynomial.Roots

/-!
# Integer-valued polynomials

We define the `ℤ`-subalgebra `Polynomial.intValued` of `ℚ[X]` of polynomials that take integer
values at all integers, and show that the binomial polynomials `Ring.choose X n` form a `ℤ`-basis
of it (Pólya).

## Main results

* `Polynomial.eq_sum_fwdDiff_iter_smul_choose`: Newton's forward difference formula. Over a field
  of characteristic zero, `P = ∑ k ≤ deg P, (Δᵏ P)(0) • Ring.choose X k`.
* `Polynomial.mem_intValued_iff_forall_natCast`: a rational polynomial is integer-valued as soon
  as it takes integer values at all natural numbers.
* `Polynomial.exists_eq_sum_intCast_smul_choose`: **Pólya's theorem**. An integer-valued
  polynomial `P` is an integer combination of the `Ring.choose X k` with `k ≤ deg P`.
* `Polynomial.intValuedBasis`: the `Ring.choose X n` form a basis of `Polynomial.intValued` over
  `ℤ`.

## References

* [P.-J. Cahen and J.-L. Chabert, *Integer-valued polynomials*][cahen1997], Chapter I
-/

@[expose] public section

open Finset fwdDiff

namespace Polynomial

section Newton

variable {K : Type*} [Field K] [CharZero K]

theorem eval_choose_X (a : K) (n : ℕ) : (Ring.choose (X : K[X]) n).eval a = Ring.choose a n := by
  simpa using Ring.map_choose (evalRingHom a) (X : K[X]) n

theorem eval_natCast_choose_X (m n : ℕ) :
    (Ring.choose (X : K[X]) n).eval (m : K) = (m.choose n : K) := by
  rw [eval_choose_X, Ring.choose_natCast]

/-- **Newton's forward difference formula**: over a field of characteristic zero, a polynomial
is the combination of the binomial polynomials `Ring.choose X k` whose coefficients are its
iterated forward differences at `0`. -/
theorem eq_sum_fwdDiff_iter_smul_choose (P : K[X]) :
    P = ∑ k ∈ range (P.natDegree + 1), (Δ_[1]^[k] P.eval 0) • Ring.choose (X : K[X]) k := by
  apply eq_of_infinite_eval_eq
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (Nat.cast_injective (R := K)))
  rintro _ ⟨m, rfl⟩
  simp only [Set.mem_ofPred_eq, eval_finsetSum, eval_smul, eval_natCast_choose_X, smul_eq_mul]
  have h := shift_eq_sum_fwdDiff_iter 1 P.eval m 0
  rw [zero_add, nsmul_one] at h
  rw [h, sum_subset (range_mono (by omega : m + 1 ≤ m + P.natDegree + 1)),
    sum_subset (range_mono (by omega : P.natDegree + 1 ≤ m + P.natDegree + 1))]
  · exact sum_congr rfl fun k _ ↦ by rw [nsmul_eq_mul, mul_comm]
  · intro k _ hk
    rw [mem_range, not_lt] at hk
    simp [fwdDiff_iter_eq_zero_of_degree_lt (by omega : P.natDegree < k)]
  · intro k _ hk
    rw [mem_range, not_lt] at hk
    simp [Nat.choose_eq_zero_of_lt (by omega : m < k)]

end Newton

/-- The integer-valued polynomials: the `ℤ`-subalgebra of `ℚ[X]` of polynomials taking integer
values at all integers. -/
noncomputable def intValued : Subalgebra ℤ ℚ[X] where
  carrier := {P | ∀ n : ℤ, P.eval (n : ℚ) ∈ Set.range ((↑) : ℤ → ℚ)}
  mul_mem' {P Q} hP hQ n := by
    obtain ⟨a, ha⟩ := hP n
    obtain ⟨b, hb⟩ := hQ n
    exact ⟨a * b, by simp [ha, hb]⟩
  add_mem' {P Q} hP hQ n := by
    obtain ⟨a, ha⟩ := hP n
    obtain ⟨b, hb⟩ := hQ n
    exact ⟨a + b, by simp [ha, hb]⟩
  algebraMap_mem' c _ := ⟨c, by simp⟩

theorem mem_intValued {P : ℚ[X]} :
    P ∈ intValued ↔ ∀ n : ℤ, P.eval (n : ℚ) ∈ Set.range ((↑) : ℤ → ℚ) :=
  Iff.rfl

theorem choose_X_mem_intValued (n : ℕ) : Ring.choose (X : ℚ[X]) n ∈ intValued :=
  fun m ↦ ⟨Ring.choose m n, by
    rw [eval_choose_X]; exact_mod_cast Ring.map_choose (Int.castRingHom ℚ) m n⟩

/-- **Pólya's theorem**: a rational polynomial taking integer values at all natural numbers is an
integer combination of the binomial polynomials `Ring.choose X k` with `k ≤ deg P`. -/
theorem exists_eq_sum_intCast_smul_choose {P : ℚ[X]}
    (hP : ∀ m : ℕ, P.eval (m : ℚ) ∈ Set.range ((↑) : ℤ → ℚ)) :
    ∃ c : ℕ → ℤ, P = ∑ k ∈ range (P.natDegree + 1), (c k : ℚ) • Ring.choose (X : ℚ[X]) k := by
  choose f hf using hP
  refine ⟨fun k ↦ Δ_[1]^[k] f 0, ?_⟩
  conv_lhs => rw [P.eq_sum_fwdDiff_iter_smul_choose]
  refine sum_congr rfl fun k _ ↦ ?_
  congr 1
  dsimp only
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
  push_cast
  simp [hf, zsmul_eq_mul]

theorem mem_intValued_iff_forall_natCast {P : ℚ[X]} :
    P ∈ intValued ↔ ∀ m : ℕ, P.eval (m : ℚ) ∈ Set.range ((↑) : ℤ → ℚ) := by
  refine ⟨fun h m ↦ by exact_mod_cast h m, fun h ↦ ?_⟩
  obtain ⟨c, hc⟩ := exists_eq_sum_intCast_smul_choose h
  rw [hc]
  exact Subalgebra.sum_mem _ fun k _ ↦ by
    rw [Int.cast_smul_eq_zsmul]
    exact Subalgebra.zsmul_mem _ (choose_X_mem_intValued k) _

theorem linearIndependent_choose_X : LinearIndependent ℤ fun n ↦ Ring.choose (X : ℚ[X]) n := by
  classical
  rw [linearIndependent_iff']
  intro s g hs i hi
  have hval : (fun m : ℕ ↦ ∑ k ∈ s, g k * (m.choose k : ℤ)) = 0 := by
    funext m
    have := congrArg (eval (m : ℚ)) hs
    rw [eval_finsetSum, eval_zero] at this
    simp only [eval_smul, eval_natCast_choose_X] at this
    simp only [zsmul_eq_mul] at this
    simpa using (by exact_mod_cast this : ∑ k ∈ s, g k * (m.choose k : ℤ) = 0)
  have hf : (fun m : ℕ ↦ ∑ k ∈ s, g k * (m.choose k : ℤ)) =
      ∑ k ∈ s, g k • fun m : ℕ ↦ (m.choose k : ℤ) := by
    funext m
    simp [Finset.sum_apply]
  have h0 : Δ_[1]^[i] (fun m : ℕ ↦ ∑ k ∈ s, g k * (m.choose k : ℤ)) 0 = 0 := by
    simp [hval, fwdDiff_iter_eq_sum_shift]
  rw [hf, fwdDiff_iter_finsetSum, Finset.sum_apply] at h0
  simp only [fwdDiff_iter_const_smul, Pi.smul_apply, fwdDiff_iter_choose_zero, smul_eq_mul,
    mul_ite, mul_one, mul_zero] at h0
  simpa [hi] using h0

/-- **Pólya's basis**: the binomial polynomials `Ring.choose X n` form a `ℤ`-basis of the
integer-valued polynomials. -/
noncomputable def intValuedBasis : Module.Basis ℕ ℤ intValued :=
  Module.Basis.mk (v := fun n ↦ ⟨Ring.choose X n, choose_X_mem_intValued n⟩)
    (.of_comp intValued.val.toLinearMap linearIndependent_choose_X)
    (fun P _ ↦ by
      obtain ⟨c, hc⟩ := exists_eq_sum_intCast_smul_choose fun m ↦ P.2 m
      have : P = ∑ k ∈ range ((P : ℚ[X]).natDegree + 1),
          c k • (⟨Ring.choose X k, choose_X_mem_intValued k⟩ : intValued) := by
        refine Subtype.ext (hc.trans ?_)
        simp [Int.cast_smul_eq_zsmul]
      rw [this]
      exact Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))

@[simp]
theorem coe_intValuedBasis (n : ℕ) : (intValuedBasis n : ℚ[X]) = Ring.choose X n := by
  simp [intValuedBasis]

instance : Module.Free ℤ intValued := .of_basis intValuedBasis

end Polynomial
