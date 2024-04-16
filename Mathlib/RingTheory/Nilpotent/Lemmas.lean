/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

#align_import ring_theory.nilpotent from "leanprover-community/mathlib"@"da420a8c6dd5bdfb85c4ced85c34388f633bc6ff"

/-!
# Nilpotent elements

-/

universe u v

open BigOperators Function Set

variable {R S : Type*} {x y : R}

theorem RingHom.ker_isRadical_iff_reduced_of_surjective {S F} [CommSemiring R] [CommRing S]
    [FunLike F R S] [RingHomClass F R S] {f : F} (hf : Function.Surjective f) :
    (RingHom.ker f).IsRadical ↔ IsReduced S := by
  simp_rw [isReduced_iff, hf.forall, IsNilpotent, ← map_pow, ← RingHom.mem_ker]
  rfl
#align ring_hom.ker_is_radical_iff_reduced_of_surjective RingHom.ker_isRadical_iff_reduced_of_surjective

theorem Prime.isRadical [CommMonoidWithZero R] {y : R} (hy : Prime y) : IsRadical y :=
  fun _ _ ↦ hy.dvd_of_dvd_pow

theorem isRadical_iff_span_singleton [CommSemiring R] :
    IsRadical y ↔ (Ideal.span ({y} : Set R)).IsRadical := by
  simp_rw [IsRadical, ← Ideal.mem_span_singleton]
  exact forall_swap.trans (forall_congr' fun r => exists_imp.symm)
#align is_radical_iff_span_singleton isRadical_iff_span_singleton

namespace Commute

section Semiring

variable [Semiring R] (h_comm : Commute x y)

theorem add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero {m n k : ℕ}
    (hx : x ^ m = 0) (hy : y ^ n = 0) (h : m + n ≤ k + 1) :
    (x + y) ^ k = 0 := by
  rw [h_comm.add_pow']
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  suffices x ^ i * y ^ j = 0 by simp only [this, nsmul_eq_mul, mul_zero]
  by_cases hi : m ≤ i
  rw [pow_eq_zero_of_le hi hx, zero_mul]
  rw [pow_eq_zero_of_le ?_ hy, mul_zero]
  linarith [Finset.mem_antidiagonal.mp hij]

theorem add_pow_add_eq_zero_of_pow_eq_zero {m n : ℕ}
    (hx : x ^ m = 0) (hy : y ^ n = 0) :
    (x + y) ^ (m + n - 1) = 0 :=
  h_comm.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero hx hy <| by rw [← Nat.sub_le_iff_le_add]

theorem isNilpotent_add (hx : IsNilpotent x) (hy : IsNilpotent y) : IsNilpotent (x + y) := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, hm⟩ := hy
  exact ⟨_, add_pow_add_eq_zero_of_pow_eq_zero h_comm hn hm⟩
#align commute.is_nilpotent_add Commute.isNilpotent_add

protected lemma isNilpotent_sum {ι : Type*} {s : Finset ι} {f : ι → R}
    (hnp : ∀ i ∈ s, IsNilpotent (f i)) (h_comm : ∀ i j, i ∈ s → j ∈ s → Commute (f i) (f j)) :
    IsNilpotent (∑ i in s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert j s hj ih => ?_
  rw [Finset.sum_insert hj]
  apply Commute.isNilpotent_add
  · exact Commute.sum_right _ _ _ (fun i hi ↦ h_comm _ _ (by simp) (by simp [hi]))
  · apply hnp; simp
  · exact ih (fun i hi ↦ hnp i (by simp [hi]))
      (fun i j hi hj ↦ h_comm i j (by simp [hi]) (by simp [hj]))

protected lemma isNilpotent_mul_left_iff (hy : y ∈ nonZeroDivisorsLeft R) :
    IsNilpotent (x * y) ↔ IsNilpotent x := by
  refine' ⟨_, h_comm.isNilpotent_mul_left⟩
  rintro ⟨k, hk⟩
  rw [mul_pow h_comm] at hk
  exact ⟨k, (nonZeroDivisorsLeft R).pow_mem hy k _ hk⟩

protected lemma isNilpotent_mul_right_iff (hx : x ∈ nonZeroDivisorsRight R) :
    IsNilpotent (x * y) ↔ IsNilpotent y := by
  refine' ⟨_, h_comm.isNilpotent_mul_right⟩
  rintro ⟨k, hk⟩
  rw [mul_pow h_comm] at hk
  exact ⟨k, (nonZeroDivisorsRight R).pow_mem hx k _ hk⟩

end Semiring

section Ring

variable [Ring R] (h_comm : Commute x y)

theorem isNilpotent_sub (hx : IsNilpotent x) (hy : IsNilpotent y) : IsNilpotent (x - y) := by
  rw [← neg_right_iff] at h_comm
  rw [← isNilpotent_neg_iff] at hy
  rw [sub_eq_add_neg]
  exact h_comm.isNilpotent_add hx hy
#align commute.is_nilpotent_sub Commute.isNilpotent_sub

end Ring

end Commute

section CommSemiring

variable [CommSemiring R] {x y : R}

lemma isNilpotent_sum {ι : Type*} {s : Finset ι} {f : ι → R}
    (hnp : ∀ i ∈ s, IsNilpotent (f i)) :
    IsNilpotent (∑ i in s, f i) :=
  Commute.isNilpotent_sum hnp fun _ _ _ _ ↦ Commute.all _ _

/-- The nilradical of a commutative semiring is the ideal of nilpotent elements. -/
def nilradical (R : Type*) [CommSemiring R] : Ideal R :=
  (0 : Ideal R).radical
#align nilradical nilradical

theorem mem_nilradical : x ∈ nilradical R ↔ IsNilpotent x :=
  Iff.rfl
#align mem_nilradical mem_nilradical

theorem nilradical_eq_sInf (R : Type*) [CommSemiring R] :
    nilradical R = sInf { J : Ideal R | J.IsPrime } :=
  (Ideal.radical_eq_sInf ⊥).trans <| by simp_rw [and_iff_right bot_le]
#align nilradical_eq_Inf nilradical_eq_sInf

theorem nilpotent_iff_mem_prime : IsNilpotent x ↔ ∀ J : Ideal R, J.IsPrime → x ∈ J := by
  rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]
  rfl
#align nilpotent_iff_mem_prime nilpotent_iff_mem_prime

theorem nilradical_le_prime (J : Ideal R) [H : J.IsPrime] : nilradical R ≤ J :=
  (nilradical_eq_sInf R).symm ▸ sInf_le H
#align nilradical_le_prime nilradical_le_prime

@[simp]
theorem nilradical_eq_zero (R : Type*) [CommSemiring R] [IsReduced R] : nilradical R = 0 :=
  Ideal.ext fun _ => isNilpotent_iff_eq_zero
#align nilradical_eq_zero nilradical_eq_zero

end CommSemiring

namespace LinearMap

variable (R) {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]

@[simp]
theorem isNilpotent_mulLeft_iff (a : A) : IsNilpotent (mulLeft R a) ↔ IsNilpotent a := by
  constructor <;> rintro ⟨n, hn⟩ <;> use n <;>
      simp only [mulLeft_eq_zero_iff, pow_mulLeft] at hn ⊢ <;>
    exact hn
#align linear_map.is_nilpotent_mul_left_iff LinearMap.isNilpotent_mulLeft_iff

@[simp]
theorem isNilpotent_mulRight_iff (a : A) : IsNilpotent (mulRight R a) ↔ IsNilpotent a := by
  constructor <;> rintro ⟨n, hn⟩ <;> use n <;>
      simp only [mulRight_eq_zero_iff, pow_mulRight] at hn ⊢ <;>
    exact hn
#align linear_map.is_nilpotent_mul_right_iff LinearMap.isNilpotent_mulRight_iff

variable {R}
variable {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M] [Module R M]

@[simp]
lemma isNilpotent_toMatrix_iff (b : Basis ι R M) (f : M →ₗ[R] M) :
    IsNilpotent (toMatrix b b f) ↔ IsNilpotent f := by
  refine' exists_congr fun k ↦ _
  rw [toMatrix_pow]
  exact (toMatrix b b).map_eq_zero_iff

end LinearMap

namespace Module.End

variable {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
variable {f : Module.End R M} {p : Submodule R M} (hp : p ≤ p.comap f)

theorem IsNilpotent.mapQ (hnp : IsNilpotent f) : IsNilpotent (p.mapQ p f hp) := by
  obtain ⟨k, hk⟩ := hnp
  use k
  simp [← p.mapQ_pow, hk]
#align module.End.is_nilpotent.mapq Module.End.IsNilpotent.mapQ

end Module.End
