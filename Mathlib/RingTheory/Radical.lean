/-
Copyright (c) 2024 Jineon Baek, Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek, Seewoo Lee, Bhavik Mehta, Arend Mellendijk
-/
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Order.Group.Finset
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.RingTheory.UniqueFactorizationDomain.Nat
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.Squarefree.Basic

/-!
# Radical of an element of a unique factorization normalization monoid

This file defines a radical of an element `a` of a unique factorization normalization
monoid, which is defined as a product of normalized prime factors of `a` without duplication.
This is different from the radical of an ideal.

## Main declarations

- `radical`: The radical of an element `a` in a unique factorization monoid is the product of
  its prime factors.
- `radical_eq_of_associated`: If `a` and `b` are associates, i.e. `a * u = b` for some unit `u`,
  then `radical a = radical b`.
- `radical_unit_mul`: Multiplying unit does not change the radical.
- `radical_dvd_self`: `radical a` divides `a`.
- `radical_pow`: `radical (a ^ n) = radical a` for any `n ≥ 1`
- `radical_of_prime`: Radical of a prime element is equal to its normalization
- `radical_pow_of_prime`: Radical of a power of prime element is equal to its normalization
- `radical_mul`: Radical is multiplicative for two relatively prime elements.
- `radical_prod`: Radical is multiplicative for finitely many relatively prime elements.

### For unique factorization domains

### For Euclidean domains

- `EuclideanDomain.divRadical`: For an element `a` in an Euclidean domain, `a / radical a`.
- `EuclideanDomain.divRadical_mul`: `divRadical` of a product is the product of `divRadical`s.
- `IsCoprime.divRadical`: `divRadical` of coprime elements are coprime.

## For natural numbers

- `UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors`: The prime factors of a natural number
  are the same as the prime factors defined in `Nat.primeFactors`.
- `Nat.radical_le_self`: The radical of a natural number is less than or equal to the number itself.
- `Nat.two_le_radical`: If a natural number is at least 2, then its radical is at least 2.

## TODO

- Make a comparison with `Ideal.radical`. Especially, for principal ideal,
  `Ideal.radical (Ideal.span {a}) = Ideal.span {radical a}`.
-/

noncomputable section

namespace UniqueFactorizationMonoid

-- `CancelCommMonoidWithZero` is required by `UniqueFactorizationMonoid`
variable {M : Type*} [CancelCommMonoidWithZero M] [NormalizationMonoid M]
  [UniqueFactorizationMonoid M] {a b u : M}

open scoped Classical in
/-- The finite set of prime factors of an element in a unique factorization monoid. -/
def primeFactors (a : M) : Finset M :=
  (normalizedFactors a).toFinset

lemma mem_primeFactors : a ∈ primeFactors b ↔ a ∈ normalizedFactors b := by
  simp only [primeFactors, Multiset.mem_toFinset]

theorem _root_.Associated.primeFactors_eq {a b : M} (h : Associated a b) :
    primeFactors a = primeFactors b := by
  unfold primeFactors
  rw [h.normalizedFactors_eq]

@[simp] lemma primeFactors_zero : primeFactors (0 : M) = ∅ := by simp [primeFactors]

@[simp] lemma primeFactors_one : primeFactors (1 : M) = ∅ := by simp [primeFactors]

lemma pairwise_primeFactors_isRelPrime :
    Set.Pairwise (primeFactors a : Set M) IsRelPrime := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  intro x hx y hy hxy
  simp only [Finset.mem_coe, mem_primeFactors, mem_normalizedFactors_iff' ha₀] at hx hy
  rw [hx.1.isRelPrime_iff_not_dvd]
  contrapose! hxy
  have : Associated x y := hx.1.associated_of_dvd hy.1 hxy
  exact this.eq_of_normalized hx.2.1 hy.2.1

theorem primeFactors_pow (a : M) {n : ℕ} (hn : n ≠ 0) : primeFactors (a ^ n) = primeFactors a := by
  simp_rw [primeFactors, normalizedFactors_pow, Multiset.toFinset_nsmul _ _ hn]

@[simp]
theorem primeFactors_pow' (a : M) {n : ℕ} [NeZero n] : primeFactors (a ^ n) = primeFactors a :=
  primeFactors_pow a NeZero.out

lemma normalizedFactors_nodup (ha : IsRadical a) : (normalizedFactors a).Nodup := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  rwa [← squarefree_iff_nodup_normalizedFactors ha₀, ← isRadical_iff_squarefree_of_ne_zero ha₀]

/--
If `x` is a unit, then the finset of prime factors of `x` is empty.
The converse is true with a nonzero assumption, see `primeFactors_eq_empty_iff`.
-/
lemma primeFactors_of_isUnit (h : IsUnit a) : primeFactors a = ∅ := by
  classical
  rw [primeFactors, normalizedFactors_of_isUnit h, Multiset.toFinset_zero]

/--
The finset of prime factors of `x` is empty if and only if `x` is a unit.
The converse is true without the nonzero assumption, see `primeFactors_of_isUnit`.
-/
theorem primeFactors_eq_empty_iff (ha : a ≠ 0) : primeFactors a = ∅ ↔ IsUnit a := by
  classical
  rw [primeFactors, Multiset.toFinset_eq_empty, normalizedFactors_eq_zero_iff ha]

lemma primeFactors_val_eq_normalizedFactors (ha : IsRadical a) :
    (primeFactors a).val = normalizedFactors a := by
  classical
  rw [primeFactors, Multiset.toFinset_val, Multiset.dedup_eq_self]
  exact normalizedFactors_nodup ha

-- Note that the non-zero assumptions are necessary here.
theorem primeFactors_mul_eq_union [DecidableEq M] (ha : a ≠ 0) (hb : b ≠ 0) :
    primeFactors (a * b) = primeFactors a ∪ primeFactors b := by
  ext p
  simp [mem_normalizedFactors_iff', mem_primeFactors, ha, hb]

/-- Relatively prime elements have disjoint prime factors (as finsets). -/
theorem disjoint_primeFactors (hc : IsRelPrime a b) :
    Disjoint (primeFactors a) (primeFactors b) := by
  classical
  exact Multiset.disjoint_toFinset.mpr (disjoint_normalizedFactors hc)

theorem primeFactors_mul_eq_disjUnion (hc : IsRelPrime a b) :
    primeFactors (a * b) =
      (primeFactors a).disjUnion (primeFactors b) (disjoint_primeFactors hc) := by
  obtain rfl | ha := eq_or_ne a 0
  · rw [isRelPrime_zero_left] at hc
    simp only [zero_mul, primeFactors_zero, Finset.empty_disjUnion, primeFactors_of_isUnit hc]
  obtain rfl | hb := eq_or_ne b 0
  · rw [isRelPrime_zero_right] at hc
    simp only [mul_zero, primeFactors_zero, primeFactors_of_isUnit hc, Finset.disjUnion_empty]
  classical
  rw [Finset.disjUnion_eq_union, primeFactors_mul_eq_union ha hb]

/--
Radical of an element `a` in a unique factorization monoid is the product of
the prime factors of `a`.
-/
def radical (a : M) : M :=
  (primeFactors a).prod id

@[simp] theorem radical_zero : radical (0 : M) = 1 := by simp [radical]
@[deprecated (since := "2025-05-31")] alias radical_zero_eq := radical_zero

@[simp] theorem radical_one : radical (1 : M) = 1 := by simp [radical]
@[deprecated (since := "2025-05-31")] alias radical_one_eq := radical_one

lemma radical_eq_of_primeFactors_eq (h : primeFactors a = primeFactors b) :
    radical a = radical b := by
  simp only [radical, h]

theorem radical_eq_of_associated (h : Associated a b) : radical a = radical b :=
  radical_eq_of_primeFactors_eq h.primeFactors_eq

lemma radical_associated (ha : IsRadical a) (ha' : a ≠ 0) :
    Associated (radical a) a := by
  rw [radical, ← Finset.prod_val, primeFactors_val_eq_normalizedFactors ha]
  exact prod_normalizedFactors ha'

/-- If `a` is a radical element, then it divides its radical. -/
lemma _root_.IsRadical.dvd_radical (ha : IsRadical a) (ha' : a ≠ 0) : a ∣ radical a :=
  (radical_associated ha ha').dvd'

theorem radical_of_isUnit (h : IsUnit a) : radical a = 1 :=
  (radical_eq_of_associated (associated_one_iff_isUnit.mpr h)).trans radical_one

theorem radical_mul_of_isUnit_left (h : IsUnit u) : radical (u * a) = radical a :=
  radical_eq_of_associated (associated_unit_mul_left _ _ h)

theorem radical_mul_of_isUnit_right (h : IsUnit u) : radical (a * u) = radical a :=
  radical_eq_of_associated (associated_mul_unit_left _ _ h)

theorem radical_pow (a : M) {n : ℕ} (hn : n ≠ 0) : radical (a ^ n) = radical a := by
  simp_rw [radical, primeFactors_pow a hn]

theorem radical_dvd_self : radical a ∣ a := by
  classical
  by_cases ha : a = 0
  · rw [ha]
    apply dvd_zero
  · rw [radical, ← Finset.prod_val, ← (prod_normalizedFactors ha).dvd_iff_dvd_right]
    apply Multiset.prod_dvd_prod_of_le
    rw [primeFactors, Multiset.toFinset_val]
    apply Multiset.dedup_le

theorem radical_of_prime (ha : Prime a) : radical a = normalize a := by
  rw [radical, primeFactors]
  rw [normalizedFactors_irreducible ha.irreducible]
  simp only [Multiset.toFinset_singleton, id, Finset.prod_singleton]

theorem radical_pow_of_prime (ha : Prime a) {n : ℕ} (hn : n ≠ 0) :
    radical (a ^ n) = normalize a := by
  rw [radical_pow a hn]
  exact radical_of_prime ha

@[simp] theorem radical_ne_zero [Nontrivial M] : radical a ≠ 0 := by
  rw [radical, ← Finset.prod_val]
  apply Multiset.prod_ne_zero
  rw [primeFactors]
  simp only [Multiset.toFinset_val, Multiset.mem_dedup]
  exact zero_notMem_normalizedFactors _

/--
An irreducible `a` divides the radical of `b` if and only if it divides `b` itself.
Note this generalises to radical elements `a`, see `UniqueFactorizationMonoid.dvd_radical_iff`.
-/
lemma dvd_radical_iff_of_irreducible (ha : Irreducible a) (hb : b ≠ 0) :
    a ∣ radical b ↔ a ∣ b := by
  constructor
  · intro ha
    exact ha.trans radical_dvd_self
  · intro ha'
    obtain ⟨c, hc, hc'⟩ := exists_mem_normalizedFactors_of_dvd hb ha ha'
    exact hc'.dvd.trans (Finset.dvd_prod_of_mem _ (by simpa [mem_primeFactors] using hc))

lemma isRadical_radical : IsRadical (radical a) := by
  intro n p ha
  rw [radical]
  apply Finset.prod_dvd_of_isRelPrime
  · exact pairwise_primeFactors_isRelPrime
  intro i hi
  simp only [mem_primeFactors] at hi
  have : i ∣ radical a := by
    rw [dvd_radical_iff_of_irreducible]
    · exact dvd_of_mem_normalizedFactors hi
    · exact irreducible_of_normalized_factor i hi
    · rintro rfl
      simp only [normalizedFactors_zero, Multiset.notMem_zero] at hi
  exact (prime_of_normalized_factor i hi).isRadical n p (this.trans ha)

lemma squarefree_radical : Squarefree (radical a) := by
  nontriviality M
  exact isRadical_radical.squarefree (by simp [radical_ne_zero])

@[simp] lemma primeFactors_radical : primeFactors (radical a) = primeFactors a := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp [primeFactors]
  have : Nontrivial M := ⟨a, 0, ha₀⟩
  ext p
  simp +contextual [mem_primeFactors, mem_normalizedFactors_iff',
    dvd_radical_iff_of_irreducible, ha₀]

theorem radical_eq_one_iff : radical a = 1 ↔ a = 0 ∨ IsUnit a := by
  refine ⟨?_, (Or.elim · (by simp +contextual) radical_of_isUnit)⟩
  intro h
  rw [or_iff_not_imp_left]
  intro ha
  have : primeFactors a = ∅ := by rw [← primeFactors_radical, h, primeFactors_one]
  rwa [primeFactors_eq_empty_iff ha] at this

@[simp]
lemma radical_radical : radical (radical a) = radical a :=
  radical_eq_of_primeFactors_eq primeFactors_radical

lemma radical_dvd_radical_iff_normalizedFactors_subset_normalizedFactors :
    radical a ∣ radical b ↔ normalizedFactors a ⊆ normalizedFactors b := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  have : Nontrivial M := ⟨a, 0, ha₀⟩
  rw [dvd_iff_normalizedFactors_le_normalizedFactors radical_ne_zero radical_ne_zero,
    Multiset.le_iff_subset (normalizedFactors_nodup isRadical_radical)]
  simp only [Multiset.subset_iff, ← mem_primeFactors, primeFactors_radical]

lemma radical_dvd_radical_iff_primeFactors_subset_primeFactors :
    radical a ∣ radical b ↔ primeFactors a ⊆ primeFactors b := by
  classical
  rw [radical_dvd_radical_iff_normalizedFactors_subset_normalizedFactors, primeFactors,
    primeFactors, Multiset.toFinset_subset]

/-- If `a` divides `b`, then the radical of `a` divides the radical of `b`. The theorem requires
that `b ≠ 0`, since `radical 0 = 1` but `a ∣ 0` holds for every `a`. -/
lemma radical_dvd_radical (h : a ∣ b) (hb₀ : b ≠ 0) : radical a ∣ radical b := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  rw [dvd_iff_normalizedFactors_le_normalizedFactors ha₀ hb₀] at h
  rw [radical_dvd_radical_iff_normalizedFactors_subset_normalizedFactors]
  exact Multiset.subset_of_le h

/--
If `a` is a radical element, then `a` divides the radical of `b` if and only if it divides `b`.
Note the forward implication holds without the `b ≠ 0` assumption via `radical_dvd_self`.
-/
lemma dvd_radical_iff (ha : IsRadical a) (hb₀ : b ≠ 0) : a ∣ radical b ↔ a ∣ b := by
  refine ⟨fun ha' ↦ ha'.trans radical_dvd_self, fun hab ↦ ?_⟩
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp_all
  · exact (ha.dvd_radical ha₀).trans (radical_dvd_radical hab hb₀)

theorem radical_dvd_iff_primeFactors_subset (hb : b ≠ 0) :
    radical a ∣ b ↔ primeFactors a ⊆ primeFactors b := by
  rw [← dvd_radical_iff isRadical_radical hb,
    radical_dvd_radical_iff_primeFactors_subset_primeFactors]

/-- Radical is multiplicative for relatively prime elements. -/
theorem radical_mul (hc : IsRelPrime a b) :
    radical (a * b) = radical a * radical b := by
  simp_rw [radical]
  rw [primeFactors_mul_eq_disjUnion hc, Finset.prod_disjUnion (disjoint_primeFactors hc)]

theorem radical_prod {ι : Type*} {f : ι → M} (s : Finset ι)
    (h : Set.Pairwise (s : Set ι) (Function.onFun IsRelPrime f)) :
    radical (∏ i ∈ s, f i) = ∏ i ∈ s, radical (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s his ih =>
    simp only [Finset.prod_cons]
    rw [Finset.coe_cons,
      Set.pairwise_insert_of_symmetric_of_notMem (symmetric_isRelPrime.comap _) (by simpa)] at h
    rw [radical_mul, ih h.1]
    exact IsRelPrime.prod_right h.2

theorem radical_mul_dvd : radical (a * b) ∣ radical a * radical b := by
  classical
  obtain rfl | ha := eq_or_ne a 0
  · simp
  obtain rfl | hb := eq_or_ne b 0
  · simp
  nontriviality M
  simp [radical_dvd_iff_primeFactors_subset, primeFactors_mul_eq_union,
    primeFactors_mul_eq_union ha hb, primeFactors_radical]

theorem radical_prod_dvd {ι : Type*} {s : Finset ι} {f : ι → M} :
    radical (∏ i ∈ s, f i) ∣ ∏ i ∈ s, radical (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s h ih =>
    simp only [Finset.prod_cons]
    exact radical_mul_dvd.trans (mul_dvd_mul_left _ ih)

end UniqueFactorizationMonoid

open UniqueFactorizationMonoid

/-! Theorems for UFDs -/
namespace UniqueFactorizationDomain

variable {R : Type*} [CommRing R] [IsDomain R] [NormalizationMonoid R]
  [UniqueFactorizationMonoid R] {a b : R}

/-- Coprime elements have disjoint prime factors (as multisets). -/
@[deprecated "UniqueFactorizationMonoid.disjoint_normalizedFactors, IsCoprime.isRelPrime"
  (since := "2025-05-31")]
theorem disjoint_normalizedFactors (hc : IsCoprime a b) :
    Disjoint (normalizedFactors a) (normalizedFactors b) :=
  UniqueFactorizationMonoid.disjoint_normalizedFactors hc.isRelPrime

/-- Coprime elements have disjoint prime factors (as finsets). -/
@[deprecated "UniqueFactorizationMonoid.disjoint_primeFactors, IsCoprime.isRelPrime"
  (since := "2025-05-31")]
theorem disjoint_primeFactors (hc : IsCoprime a b) :
    Disjoint (primeFactors a) (primeFactors b) :=
  UniqueFactorizationMonoid.disjoint_primeFactors hc.isRelPrime

set_option linter.deprecated false in
@[deprecated "UniqueFactorizationMonoid.primeFactors_mul_eq_disjUnion, IsCoprime.isRelPrime"
  (since := "2025-05-31")]
theorem mul_primeFactors_disjUnion
    (hc : IsCoprime a b) : primeFactors (a * b) =
    (primeFactors a).disjUnion (primeFactors b) (disjoint_primeFactors hc) :=
  UniqueFactorizationMonoid.primeFactors_mul_eq_disjUnion hc.isRelPrime

/-- Radical is multiplicative for coprime elements. -/
@[deprecated "UniqueFactorizationMonoid.radical_mul, IsCoprime.isRelPrime" (since := "2025-05-31")]
theorem radical_mul (hc : IsCoprime a b) :
    radical (a * b) = radical a * radical b :=
  UniqueFactorizationMonoid.radical_mul hc.isRelPrime

@[simp]
theorem radical_neg : radical (-a) = radical a :=
  radical_eq_of_associated Associated.rfl.neg_left

theorem radical_neg_one : radical (-1 : R) = 1 := by simp

end UniqueFactorizationDomain

open UniqueFactorizationDomain
namespace EuclideanDomain

variable {E : Type*} [EuclideanDomain E] [NormalizationMonoid E] [UniqueFactorizationMonoid E]
  {a b u x : E}

/-- Division of an element by its radical in an Euclidean domain. -/
def divRadical (a : E) : E := a / radical a

theorem radical_mul_divRadical : radical a * divRadical a = a := by
  rw [divRadical, ← EuclideanDomain.mul_div_assoc _ radical_dvd_self,
    mul_div_cancel_left₀ _ radical_ne_zero]

theorem divRadical_mul_radical : divRadical a * radical a = a := by
  rw [mul_comm]
  exact radical_mul_divRadical

theorem divRadical_ne_zero (ha : a ≠ 0) : divRadical a ≠ 0 := by
  rw [← radical_mul_divRadical (a := a)] at ha
  exact right_ne_zero_of_mul ha

theorem divRadical_isUnit (hu : IsUnit u) : IsUnit (divRadical u) := by
  rwa [divRadical, radical_of_isUnit hu, EuclideanDomain.div_one]

theorem eq_divRadical (h : radical a * x = a) : x = divRadical a := by
  apply EuclideanDomain.eq_div_of_mul_eq_left radical_ne_zero
  rwa [mul_comm]

theorem divRadical_mul (hab : IsCoprime a b) :
    divRadical (a * b) = divRadical a * divRadical b := by
  symm; apply eq_divRadical
  rw [UniqueFactorizationMonoid.radical_mul hab.isRelPrime]
  rw [mul_mul_mul_comm, radical_mul_divRadical, radical_mul_divRadical]

theorem divRadical_dvd_self (a : E) : divRadical a ∣ a :=
  ⟨radical a, divRadical_mul_radical.symm⟩

theorem _root_.IsCoprime.divRadical {a b : E} (h : IsCoprime a b) :
    IsCoprime (divRadical a) (divRadical b) := by
  rw [← radical_mul_divRadical (a := a)] at h
  rw [← radical_mul_divRadical (a := b)] at h
  exact h.of_mul_left_right.of_mul_right_right

end EuclideanDomain

section Nat

lemma UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors :
    primeFactors = Nat.primeFactors := by
  ext n : 1
  rw [primeFactors, Nat.factors_eq, Nat.primeFactors]
  -- this convert is necessary because of the different DecidableEq instances
  convert List.toFinset_coe _

namespace Nat

@[simp] theorem radical_le_self_iff {n : ℕ} : radical n ≤ n ↔ n ≠ 0 :=
  ⟨by aesop, fun h ↦ Nat.le_of_dvd (by cutsat) radical_dvd_self⟩

@[simp] theorem two_le_radical_iff {n : ℕ} : 2 ≤ radical n ↔ 2 ≤ n := by
  refine ⟨?_, ?_⟩
  · match n with | 0 | 1 | _ + 2 => simp
  · intro hn
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by cutsat)
    trans p
    · apply hp.two_le
    · apply Nat.le_of_dvd (Nat.pos_of_ne_zero radical_ne_zero)
      rwa [dvd_radical_iff_of_irreducible hp.prime.irreducible (by cutsat)]

@[simp] theorem one_lt_radical_iff {n : ℕ} : 1 < radical n ↔ 1 < n := two_le_radical_iff

@[simp] theorem radical_le_one_iff {n : ℕ} : radical n ≤ 1 ↔ n ≤ 1 := by
  simpa only [not_lt] using one_lt_radical_iff.not

theorem radical_pos (n : ℕ) : 0 < radical n := pos_of_ne_zero radical_ne_zero

end Nat

end Nat
