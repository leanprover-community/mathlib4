/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Data.Nat.Init

/-!
# Known cases of Kaplansky's conjectures on group rings

Currently, this file only proves a sufficient condition for the unit conjecture to hold.

-/

namespace MonoidAlgebra

variable {R M : Type*} [Semiring R] [NoZeroDivisors R]

theorem card_support_mul_le_one_iff [Mul M] [TwoUniqueProds M] {f g : MonoidAlgebra R M} :
    (f * g).support.card ≤ 1 ↔ f.support.card * g.support.card ≤ 1 where
  mp h := by
    contrapose! h
    have ⟨p1, h1, p2, h2, ne, um⟩ := TwoUniqueProds.uniqueMul_of_one_lt_card h
    rw [Finset.mem_product] at h1 h2
    exact Finset.one_lt_card.mpr ⟨_, mul_mem_support_mul_of_uniqueMul um.1 h1.1 h1.2, _,
      mul_mem_support_mul_of_uniqueMul um.2 h2.1 h2.2, (ne <| Prod.ext_iff.2 <| um.2 h1.1 h1.2 ·)⟩
  mpr h := by classical
    exact (Finset.card_le_card <| support_mul ..).trans <| (Finset.card_mul_le ..).trans h

theorem card_support_mul_eq_one_iff [Mul M] [TwoUniqueProds M] {f g : MonoidAlgebra R M} :
    (f * g).support.card = 1 ↔ f.support.card = 1 ∧ g.support.card = 1 := by
  simp_rw [← Nat.mul_eq_one_iff, le_antisymm_iff, Nat.one_le_iff_ne_zero, mul_ne_zero_iff,
    card_support_mul_le_one_iff, Finset.card_ne_zero, Finsupp.support_nonempty_iff,
    mul_ne_zero_iff (a := f)]

/-- Kaplansky's unit conjecture holds over a semiring without zero divisors with a monoid with
two unique products. It is known to fail over at least one field of every characteristic with
the Promislow group which is torsion-free but does not have unique products
(notice that a group with unique products automatically has two unique products). -/
theorem isUnit_iff_of_twoUniqueProds [Monoid M] [TwoUniqueProds M] {f : MonoidAlgebra R M} :
    IsUnit f ↔ ∃ (m : Mˣ) (r : Rˣ), f = single ↑m ↑r where
  mp h := by
    nontriviality R
    obtain ⟨g, eq⟩ := isUnit_iff_exists.mp h
    have := card_support_mul_eq_one_iff.mp <| congr_arg (·.card) (eq.1 ▸ support_one)
    simp_rw [Finsupp.card_support_eq_one] at this
    have ⟨⟨mf, hmf, hf⟩, mg, hmg, hg⟩ := this
    rw [hf, hg, one_def] at eq
    iterate 2 rw [single_mul_single, Finsupp.single_eq_single_iff] at eq
    simp_rw [one_ne_zero, and_false, or_false] at eq
    exact ⟨⟨mf, mg, eq.1.1, eq.2.1⟩, ⟨_, _, eq.1.2, eq.2.2⟩, hf⟩
  mpr := by rintro ⟨m, r, rfl⟩; exact isUnit_single m.isUnit r.isUnit

end MonoidAlgebra

namespace AddMonoidAlgebra

variable {R M : Type*} [Semiring R] [NoZeroDivisors R]

theorem card_support_mul_le_one_iff [Add M] [TwoUniqueSums M] {f g : R[M]} :
    (f * g).support.card ≤ 1 ↔ f.support.card * g.support.card ≤ 1 :=
  MonoidAlgebra.card_support_mul_le_one_iff (M := Multiplicative M)

theorem card_support_mul_eq_one_iff [Add M] [TwoUniqueSums M] {f g : R[M]} :
    (f * g).support.card = 1 ↔ f.support.card = 1 ∧ g.support.card = 1 :=
  MonoidAlgebra.card_support_mul_eq_one_iff (M := Multiplicative M)

theorem isUnit_iff_of_twoUniqueSums [AddMonoid M] [TwoUniqueSums M] {f : R[M]} :
    IsUnit f ↔ ∃ (m : AddUnits M) (r : Rˣ), f = single ↑m ↑r := by
  rw [← unitsMultiplicativeEquivAddUnits.exists_congr_right]
  exact MonoidAlgebra.isUnit_iff_of_twoUniqueProds (M := Multiplicative M)

end AddMonoidAlgebra
