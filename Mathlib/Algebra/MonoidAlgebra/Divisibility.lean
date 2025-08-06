/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Data.Nat.Init

/-!
# Units and irreducible and prime elements in monoid algebras

-/

variable {M R : Type*} {m : M} {r : R}

section Semiring

variable [Semiring R]

namespace MonoidAlgebra

section Semigroup

variable [Semigroup M]

theorem single_dvd_iff {f : MonoidAlgebra R M} :
    single m r ∣ f ↔ ∀ x ∈ f.support, m ∣ x ∧ r ∣ f x where
  mp := by
    rintro ⟨f, rfl⟩ x hx
    classical
    have hx := f.support_single_mul_subset _ _ hx
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hx
    refine ⟨⟨x, rfl⟩, ?_⟩
    rw [mul_def, Finsupp.sum_apply]
    refine Finset.dvd_sum fun y _ ↦
      (Finset.dvd_sum fun z _ ↦ ?_).trans (Finset.sum_apply' ..).symm.dvd
    simp_rw [Finsupp.single_apply]
    split_ifs
    exacts [⟨_, rfl⟩, (dvd_zero _).trans (zero_mul _).symm.dvd, dvd_zero _]
  mpr h := by
    choose m' hm using (h · · |>.1)
    choose r' hr using (h · · |>.2)
    use ∑ x : f.support, single (m' x x.2) (r' x x.2)
    simp_rw [Finset.mul_sum, single_mul_single, ← hm, ← hr]
    exact ((Finset.sum_coe_sort ..).trans f.sum_single).symm

end Semigroup

section Monoid

variable [Monoid M]

theorem isUnit_single (hm : IsUnit m) (hr : IsUnit r) : IsUnit (single m r) :=
  (Prod.isUnit_iff (x := (r, m)).mpr ⟨hr, hm⟩).map singleHom

theorem isUnit_single_iff [Nontrivial R] : IsUnit (single m r) ↔ IsUnit m ∧ IsUnit r where
  mp h := by
    have hm : IsUnit m := by
      rw [isUnit_iff_exists_and_exists] at h ⊢
      simp_rw [eq_comm (b := (1 : M))]
      apply h.imp <;> refine fun ⟨a, eq⟩ ↦ of_not_not fun h ↦ one_ne_zero (α := R) ?_
      · exact .trans (by simp [eq, one_def]) (single_mul_apply_of_not_exists_mul r a h)
      · exact .trans (by simp [eq, one_def]) (mul_single_apply_of_not_exists_mul r a h)
    use hm
    obtain ⟨m, rfl⟩ := hm
    rw [isUnit_iff_exists_and_exists] at h ⊢
    apply h.imp <;>
      refine fun ⟨a, eq⟩ ↦ ⟨a ↑m⁻¹, .trans (.symm ?_) (congr($eq 1).trans Finsupp.single_eq_same)⟩
    · exact single_mul_apply_aux _ fun _ _ ↦ m.mul_eq_one_iff_inv_eq.trans eq_comm
    · exact mul_single_apply_aux _ fun _ _ ↦ m.mul_eq_one_iff_eq_inv
  mpr h := isUnit_single h.1 h.2

theorem isUnit_right_of_single (h : IsUnit (single m r)) : IsUnit r := by
  nontriviality R
  exact (isUnit_single_iff.mp h).2

end Monoid

section NoZeroDivisors

variable [NoZeroDivisors R]

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

end NoZeroDivisors

end MonoidAlgebra

namespace AddMonoidAlgebra

section AddMonoid

variable [AddMonoid M]

theorem isUnit_single (hm : IsAddUnit m) (hr : IsUnit r) : IsUnit (single m r) :=
  MonoidAlgebra.isUnit_single (M := Multiplicative M) (isUnit_ofAdd_iff.mpr hm) hr

theorem isUnit_single_iff [Nontrivial R] : IsUnit (single m r) ↔ IsAddUnit m ∧ IsUnit r := by
  rw [MonoidAlgebra.isUnit_single_iff (M := Multiplicative M), ← isUnit_ofAdd_iff]; rfl

theorem isUnit_right_of_single (h : IsUnit (single m r)) : IsUnit r :=
  MonoidAlgebra.isUnit_right_of_single (M := Multiplicative M) h

end AddMonoid

section NoZeroDivisors

variable [NoZeroDivisors R]

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

end NoZeroDivisors

end AddMonoidAlgebra

end Semiring

section CommSemiring

variable [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]

theorem MonoidAlgebra.prime_single [CommMonoid M] [UniqueProds M]
    (hm : Preprime m) (hr : IsUnit r) : Prime (single m r) where
  1 := Finsupp.single_ne_zero.mpr hr.ne_zero
  2.1 h := hm.1 (isUnit_single_iff.mp h).1
  2.2 f g dvd := by
    simp_rw [single_dvd_iff, hr.dvd, and_true] at dvd ⊢
    contrapose! dvd
    classical
    simp_rw [← Finset.filter_nonempty_iff] at dvd
    have ⟨mf, hf, mg, hg, um⟩ := UniqueProds.uniqueMul_of_nonempty dvd.1 dvd.2
    simp_rw [Finset.mem_filter] at hf hg
    have ndvd : ¬ m ∣ mf * mg := fun h ↦ (hm.2 _ _ h).elim hf.2 hg.2
    refine ⟨mf * mg, mul_mem_support_mul_of_uniqueMul (fun m₁ m₂ h₁ h₂ eq ↦ ?_) hf.1 hg.1, ndvd⟩
    rw [← eq, hm.dvd_mul, not_or] at ndvd
    refine um ?_ ?_ eq <;> rw [Finset.mem_filter]
    exacts [⟨h₁, ndvd.1⟩, ⟨h₂, ndvd.2⟩]

theorem AddMonoidAlgebra.prime_single [AddCommMonoid M] [UniqueSums M]
    (hm : AddPrime m) (hr : IsUnit r) : Prime (single m r) :=
  MonoidAlgebra.prime_single (preprime_ofAdd_iff.mpr hm) hr

end CommSemiring
