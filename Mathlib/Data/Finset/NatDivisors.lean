/-
Copyright (c) 2023 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Yury Kudryashov
-/
module

public import Mathlib.NumberTheory.Divisors
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.GCDMonoid.Nat

/-!
# `Nat.divisors` as a multiplicative homomorphism

The main definition of this file is `Nat.divisorsHom : ℕ →* Finset ℕ`,
exhibiting `Nat.divisors` as a multiplicative homomorphism from `ℕ` to `Finset ℕ`.
-/

@[expose] public section

open Nat Finset
open scoped Pointwise

/-- The divisors of a product of natural numbers are the pointwise product of the divisors of the
factors. -/
lemma Nat.divisors_mul (m n : ℕ) : divisors (m * n) = divisors m * divisors n := by
  ext k
  simp_rw [mem_mul, mem_divisors, Nat.dvd_mul, mul_ne_zero_iff, ← exists_and_left,
    ← exists_and_right]
  simp only [and_assoc, and_comm, and_left_comm]

/-- `Nat.divisors` as a `MonoidHom`. -/
@[simps]
def Nat.divisorsHom : ℕ →* Finset ℕ where
  toFun := Nat.divisors
  map_mul' := divisors_mul
  map_one' := divisors_one

lemma Nat.Prime.divisors_sq {p : ℕ} (hp : p.Prime) : (p ^ 2).divisors = {p ^ 2, p, 1} := by
  simp [divisors_prime_pow hp, range_add_one]

lemma List.nat_divisors_prod (l : List ℕ) : divisors l.prod = (l.map divisors).prod :=
  map_list_prod Nat.divisorsHom l

lemma Multiset.nat_divisors_prod (s : Multiset ℕ) : divisors s.prod = (s.map divisors).prod :=
  map_multiset_prod Nat.divisorsHom s

lemma Finset.nat_divisors_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    divisors (∏ i ∈ s, f i) = ∏ i ∈ s, divisors (f i) :=
  map_prod Nat.divisorsHom f s

namespace Nat.Coprime

lemma divisors_mul_injective {m n : ℕ} (hmn : m.Coprime n) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2) (m.divisors ×ˢ n.divisors) := by
intro p1 hp1 p2 hp2 heq
  let hmn' := (Nat.coprime_iff_isRelPrime.mp hmn)
  simp only [Set.mem_prod, SetLike.mem_coe, mem_divisors] at hp1 hp2
  exact (hmn'.existsUnique_dvd_dvd_of_dvd_mul
    (mul_dvd_mul hp1.1.1 hp1.2.1)).unique
    ⟨hp1.1.1, hp1.2.1, rfl⟩
    ⟨hp2.1.1, hp2.2.1, heq.symm⟩

theorem card_divisors_mul {m n : ℕ} (hmn : m.Coprime n) :
    #(m * n).divisors = #m.divisors * #n.divisors := by
  rw [Nat.divisors_mul]
  exact (Finset.card_mul_iff).2 (divisors_mul_injective hmn)

theorem sum_divisors_mul {m n : ℕ} (hmn : m.Coprime n) :
    ∑ d ∈ (m * n).divisors, d = (∑ d ∈ m.divisors, d) * ∑ d ∈ n.divisors, d := by
  rw [Nat.divisors_mul, Finset.mul_def,
      Finset.sum_image (by exact_mod_cast divisors_mul_injective hmn), Finset.sum_product]
  simpa using
    (Finset.sum_mul_sum m.divisors n.divisors (fun d : ℕ => d) (fun d : ℕ => d)).symm

end Nat.Coprime
