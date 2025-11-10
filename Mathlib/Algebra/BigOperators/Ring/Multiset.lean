/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Bhavik Mehta, Eric Wieser
-/
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Multiset.Antidiagonal
import Mathlib.Data.Multiset.Sections

/-! # Lemmas about `Multiset.sum` and `Multiset.prod` requiring extra algebra imports -/


variable {ι M M₀ R : Type*}

namespace Multiset
section CommMonoid
variable [CommMonoid M] [HasDistribNeg M]

@[simp] lemma prod_map_neg (s : Multiset M) : (s.map Neg.neg).prod = (-1) ^ card s * s.prod :=
  Quotient.inductionOn s (by simp)

end CommMonoid

section CommMonoidWithZero
variable [CommMonoidWithZero M₀] {s : Multiset M₀}

lemma prod_eq_zero (h : (0 : M₀) ∈ s) : s.prod = 0 := by
  rcases Multiset.exists_cons_of_mem h with ⟨s', hs'⟩; simp [hs', Multiset.prod_cons]

variable [NoZeroDivisors M₀] [Nontrivial M₀] {s : Multiset M₀}

@[simp] lemma prod_eq_zero_iff : s.prod = 0 ↔ (0 : M₀) ∈ s :=
  Quotient.inductionOn s fun l ↦ by rw [quot_mk_to_coe, prod_coe]; exact List.prod_eq_zero_iff

lemma prod_ne_zero (h : (0 : M₀) ∉ s) : s.prod ≠ 0 := mt prod_eq_zero_iff.1 h

end CommMonoidWithZero

section NonUnitalNonAssocSemiring
variable [NonUnitalNonAssocSemiring R] {a : R} {s : Multiset ι} {f : ι → R}

lemma sum_map_mul_left : sum (s.map fun i ↦ a * f i) = a * sum (s.map f) :=
  Multiset.induction_on s (by simp) fun i s ih => by simp [ih, mul_add]

lemma sum_map_mul_right : sum (s.map fun i ↦ f i * a) = sum (s.map f) * a :=
  Multiset.induction_on s (by simp) fun a s ih => by simp [ih, add_mul]

end NonUnitalNonAssocSemiring

section NonUnitalSemiring
variable [NonUnitalSemiring R] {s : Multiset R} {a : R}

lemma dvd_sum : (∀ x ∈ s, a ∣ x) → a ∣ s.sum :=
  Multiset.induction_on s (fun _ ↦ dvd_zero _) fun x s ih h ↦ by
    rw [sum_cons]
    exact dvd_add (h _ (mem_cons_self _ _)) (ih fun y hy ↦ h _ <| mem_cons.2 <| Or.inr hy)

end NonUnitalSemiring

section CommSemiring
variable [CommSemiring R]

lemma prod_map_sum {s : Multiset (Multiset R)} :
    prod (s.map sum) = sum ((Sections s).map prod) :=
  Multiset.induction_on s (by simp) fun a s ih ↦ by
    simp [ih, map_bind, sum_map_mul_left, sum_map_mul_right]

lemma prod_map_add {s : Multiset ι} {f g : ι → R} :
    prod (s.map fun i ↦ f i + g i) =
      sum ((antidiagonal s).map fun p ↦ (p.1.map f).prod * (p.2.map g).prod) := by
  refine s.induction_on ?_ fun a s ih ↦ ?_
  · simp only [map_zero, prod_zero, antidiagonal_zero, map_singleton, mul_one, sum_singleton]
  · simp only [map_cons, prod_cons, ih, sum_map_mul_left.symm, add_mul, mul_left_comm (f a),
      mul_left_comm (g a), sum_map_add, antidiagonal_cons, Prod.map_fst, Prod.map_snd,
      id_eq, map_add, map_map, Function.comp_apply, mul_assoc, sum_add]
    exact add_comm _ _

end CommSemiring
end Multiset

open Multiset

namespace Commute

variable [NonUnitalNonAssocSemiring R] (s : Multiset R)

theorem multiset_sum_right (a : R) (h : ∀ b ∈ s, Commute a b) : Commute a s.sum := by
  induction s using Quotient.inductionOn
  rw [quot_mk_to_coe, sum_coe]
  exact Commute.list_sum_right _ _ h

theorem multiset_sum_left (b : R) (h : ∀ a ∈ s, Commute a b) : Commute s.sum b :=
  ((Commute.multiset_sum_right _ _) fun _ ha => (h _ ha).symm).symm

end Commute
