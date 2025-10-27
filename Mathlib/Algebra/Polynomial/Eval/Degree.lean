/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# Evaluation of polynomials and degrees

This file contains results on the interaction of `Polynomial.eval` and `Polynomial.degree`.

-/

noncomputable section

open Finset AddMonoidAlgebra

open Polynomial

namespace Polynomial

universe u v w y

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

section Eval₂

section

variable [Semiring S] (f : R →+* S) (x : S)

theorem eval₂_eq_sum_range :
    p.eval₂ f x = ∑ i ∈ Finset.range (p.natDegree + 1), f (p.coeff i) * x ^ i :=
  _root_.trans (congr_arg _ p.as_sum_range)
    (_root_.trans (eval₂_finset_sum f _ _ x) (congr_arg _ (by simp)))

theorem eval₂_eq_sum_range' (f : R →+* S) {p : R[X]} {n : ℕ} (hn : p.natDegree < n) (x : S) :
    eval₂ f x p = ∑ i ∈ Finset.range n, f (p.coeff i) * x ^ i := by
  rw [eval₂_eq_sum, p.sum_over_range' _ _ hn]
  intro i
  rw [f.map_zero, zero_mul]

end

end Eval₂

section Eval

variable {x : R}

theorem eval_eq_sum_range {p : R[X]} (x : R) :
    p.eval x = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i := by
  rw [eval_eq_sum, sum_over_range]; simp

theorem eval_eq_sum_range' {p : R[X]} {n : ℕ} (hn : p.natDegree < n) (x : R) :
    p.eval x = ∑ i ∈ Finset.range n, p.coeff i * x ^ i := by
  rw [eval_eq_sum, p.sum_over_range' _ _ hn]; simp

/-- A reformulation of the expansion of (1 + y)^d:
$$(d + 1) (1 + y)^d - (d + 1)y^d = \sum_{i = 0}^d {d + 1 \choose i} \cdot i \cdot y^{i - 1}.$$
-/
theorem eval_monomial_one_add_sub [CommRing S] (d : ℕ) (y : S) :
    eval (1 + y) (monomial d (d + 1 : S)) - eval y (monomial d (d + 1 : S)) =
      ∑ x_1 ∈ range (d + 1), ↑((d + 1).choose x_1) * (↑x_1 * y ^ (x_1 - 1)) := by
  have cast_succ : (d + 1 : S) = ((d.succ : ℕ) : S) := by simp only [Nat.cast_succ]
  rw [cast_succ, eval_monomial, eval_monomial, add_comm, add_pow]
  simp only [one_pow, mul_one, mul_comm (y ^ _) (d.choose _)]
  rw [sum_range_succ, mul_add, Nat.choose_self, Nat.cast_one, one_mul, add_sub_cancel_right,
    mul_sum, sum_range_succ', Nat.cast_zero, zero_mul, mul_zero, add_zero]
  refine sum_congr rfl fun y _hy => ?_
  rw [← mul_assoc, ← mul_assoc, ← Nat.cast_mul, Nat.succ_mul_choose_eq, Nat.cast_mul,
    Nat.add_sub_cancel]

end Eval

section Comp

theorem coeff_comp_degree_mul_degree (hqd0 : natDegree q ≠ 0) :
    coeff (p.comp q) (natDegree p * natDegree q) =
    leadingCoeff p * leadingCoeff q ^ natDegree p := by
  rw [comp, eval₂_def, coeff_sum]
  refine Eq.trans (Finset.sum_eq_single p.natDegree ?h₀ ?h₁) ?h₂
  case h₂ =>
    simp only [coeff_natDegree, coeff_C_mul, coeff_pow_mul_natDegree]
  case h₀ =>
    intro b hbs hbp
    refine coeff_eq_zero_of_natDegree_lt (natDegree_mul_le.trans_lt ?_)
    rw [natDegree_C, zero_add]
    refine natDegree_pow_le.trans_lt ?_
    gcongr
    exact lt_of_le_of_ne (le_natDegree_of_mem_supp _ hbs) hbp
  case h₁ =>
    simp +contextual

@[simp] lemma comp_C_mul_X_coeff {r : R} {n : ℕ} :
    (p.comp <| C r * X).coeff n = p.coeff n * r ^ n := by
  simp_rw [comp, eval₂_eq_sum_range, (commute_X _).symm.mul_pow,
    ← C_pow, finset_sum_coeff, coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single n _ fun h ↦ ?_, if_pos rfl, mul_one]
  · intro b _ h; simp_rw [if_neg h.symm, mul_zero]
  · rw [coeff_eq_zero_of_natDegree_lt, zero_mul]
    rwa [Finset.mem_range_succ_iff, not_le] at h

lemma comp_C_mul_X_eq_zero_iff {r : R} (hr : r ∈ nonZeroDivisors R) :
    p.comp (C r * X) = 0 ↔ p = 0 := by
  simp_rw [ext_iff]
  refine forall_congr' fun n ↦ ?_
  rw [comp_C_mul_X_coeff, coeff_zero, mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hr _)]

end Comp

section Map

variable [Semiring S] {f : R →+* S} {p : R[X]}

variable (f) in
/-- If `R` and `S` are isomorphic, then so are their polynomial rings. -/
@[simps!]
def mapEquiv (e : R ≃+* S) : R[X] ≃+* S[X] :=
  RingEquiv.ofHomInv (mapRingHom (e : R →+* S)) (mapRingHom (e.symm : S →+* R)) (by ext; simp)
    (by ext; simp)

theorem map_monic_eq_zero_iff (hp : p.Monic) : p.map f = 0 ↔ ∀ x, f x = 0 :=
  ⟨fun hfp x =>
    calc
      f x = f x * f p.leadingCoeff := by simp only [mul_one, hp.leadingCoeff, f.map_one]
      _ = f x * (p.map f).coeff p.natDegree := congr_arg _ (coeff_map _ _).symm
      _ = 0 := by simp only [hfp, mul_zero, coeff_zero],
    fun h => ext fun n => by simp only [h, coeff_map, coeff_zero]⟩

theorem map_monic_ne_zero (hp : p.Monic) [Nontrivial S] : p.map f ≠ 0 := fun h =>
  f.map_one_ne_zero ((map_monic_eq_zero_iff hp).mp h _)

lemma degree_map_le : degree (p.map f) ≤ degree p := by
  refine (degree_le_iff_coeff_zero _ _).2 fun m hm => ?_
  rw [degree_lt_iff_coeff_zero] at hm
  simp [hm m le_rfl]

lemma natDegree_map_le : natDegree (p.map f) ≤ natDegree p := natDegree_le_natDegree degree_map_le

lemma degree_map_lt (hp : f p.leadingCoeff = 0) (hp₀ : p ≠ 0) : (p.map f).degree < p.degree := by
  refine degree_map_le.lt_of_ne fun hpq ↦ hp₀ ?_
  rw [leadingCoeff, ← coeff_map, ← natDegree_eq_natDegree hpq, ← leadingCoeff, leadingCoeff_eq_zero]
    at hp
  rw [← degree_eq_bot, ← hpq, hp, degree_zero]

lemma natDegree_map_lt (hp : f p.leadingCoeff = 0) (hp₀ : map f p ≠ 0) :
    (p.map f).natDegree < p.natDegree :=
  natDegree_lt_natDegree hp₀ <| degree_map_lt hp <| by rintro rfl; simp at hp₀

/-- Variant of `natDegree_map_lt` that assumes `0 < natDegree p` instead of `map f p ≠ 0`. -/
lemma natDegree_map_lt' (hp : f p.leadingCoeff = 0) (hp₀ : 0 < natDegree p) :
    (p.map f).natDegree < p.natDegree := by
  by_cases H : map f p = 0
  · rwa [H, natDegree_zero]
  · exact natDegree_map_lt hp H

theorem degree_map_eq_of_leadingCoeff_ne_zero (f : R →+* S) (hf : f (leadingCoeff p) ≠ 0) :
    degree (p.map f) = degree p := by
  grind [degree_eq_natDegree, coeff_map, coeff_natDegree, le_degree_of_ne_zero, degree_map_le,
    le_antisymm, leadingCoeff_ne_zero, RingHom.map_zero]

theorem natDegree_map_of_leadingCoeff_ne_zero (f : R →+* S) (hf : f (leadingCoeff p) ≠ 0) :
    natDegree (p.map f) = natDegree p :=
  natDegree_eq_of_degree_eq (degree_map_eq_of_leadingCoeff_ne_zero f hf)

theorem leadingCoeff_map_of_leadingCoeff_ne_zero (f : R →+* S) (hf : f (leadingCoeff p) ≠ 0) :
    leadingCoeff (p.map f) = f (leadingCoeff p) := by
  grind [natDegree_map_of_leadingCoeff_ne_zero, coeff_map, coeff_natDegree]

theorem nextCoeff_map_of_leadingCoeff_ne_zero (f : R →+* S) (hf : f p.leadingCoeff ≠ 0) :
    (p.map f).nextCoeff = f p.nextCoeff := by
  grind [nextCoeff, natDegree_map_of_leadingCoeff_ne_zero, coeff_map, map_zero]

end Map

end Semiring

section CommSemiring

section Eval

section

variable [Semiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

theorem eval₂_comp {x : S} : eval₂ f x (p.comp q) = eval₂ f (eval₂ f x q) p := by
  rw [comp, p.as_sum_range]; simp [eval₂_finset_sum, eval₂_pow]

@[simp]
theorem iterate_comp_eval₂ (k : ℕ) (t : S) :
    eval₂ f t (p.comp^[k] q) = (fun x => eval₂ f x p)^[k] (eval₂ f t q) := by
  induction k with
  | zero => simp
  | succ k IH => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', eval₂_comp, IH]

end

section

variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

@[simp]
theorem iterate_comp_eval :
    ∀ (k : ℕ) (t : R), (p.comp^[k] q).eval t = (fun x => p.eval x)^[k] (q.eval t) :=
  iterate_comp_eval₂ _

end

end Eval

end CommSemiring

section
variable [Semiring R] [CommRing S] [IsDomain S] (φ : R →+* S) {f : R[X]}

lemma isUnit_of_isUnit_leadingCoeff_of_isUnit_map (hf : IsUnit f.leadingCoeff)
    (H : IsUnit (map φ f)) : IsUnit f := by
  have dz := degree_eq_zero_of_isUnit H
  rw [degree_map_eq_of_leadingCoeff_ne_zero] at dz
  · rw [eq_C_of_degree_eq_zero dz]
    refine IsUnit.map C ?_
    convert hf
    change coeff f 0 = coeff f (natDegree f)
    rw [(degree_eq_iff_natDegree_eq _).1 dz]
    · rfl
    rintro rfl
    simp at H
  · intro h
    have u : IsUnit (φ f.leadingCoeff) := IsUnit.map φ hf
    rw [h] at u
    simp at u

end

end Polynomial
