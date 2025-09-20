/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Squarefree elements of monoids
An element of a monoid is squarefree when it is not divisible by any squares
except the squares of units.

Results about squarefree natural numbers are proved in `Data.Nat.Squarefree`.

## Main Definitions
- `Squarefree r` indicates that `r` is only divisible by `x * x` if `x` is a unit.

## Main Results
- `multiplicity.squarefree_iff_emultiplicity_le_one`: `x` is `Squarefree` iff for every `y`, either
  `emultiplicity y x ≤ 1` or `IsUnit y`.
- `UniqueFactorizationMonoid.squarefree_iff_nodup_factors`: A nonzero element `x` of a unique
  factorization monoid is squarefree iff `factors x` has no duplicate factors.

## Tags
squarefree, multiplicity

-/


variable {R : Type*}

/-- An element of a monoid is squarefree if the only squares that
  divide it are the squares of units. -/
def Squarefree [Monoid R] (r : R) : Prop :=
  ∀ x : R, x * x ∣ r → IsUnit x

theorem IsRelPrime.of_squarefree_mul [CommMonoid R] {m n : R} (h : Squarefree (m * n)) :
    IsRelPrime m n := fun c hca hcb ↦ h c (mul_dvd_mul hca hcb)

@[simp]
theorem IsUnit.squarefree [CommMonoid R] {x : R} (h : IsUnit x) : Squarefree x := fun _ hdvd =>
  isUnit_of_mul_isUnit_left (isUnit_of_dvd_unit hdvd h)

theorem squarefree_one [CommMonoid R] : Squarefree (1 : R) :=
  isUnit_one.squarefree

@[simp]
theorem not_squarefree_zero [MonoidWithZero R] [Nontrivial R] : ¬Squarefree (0 : R) := by
  rw [Squarefree, not_forall]
  exact ⟨0, by simp⟩

theorem Squarefree.ne_zero [MonoidWithZero R] [Nontrivial R] {m : R} (hm : Squarefree (m : R)) :
    m ≠ 0 := by
  rintro rfl
  exact not_squarefree_zero hm

@[simp]
theorem Irreducible.squarefree [CommMonoid R] {x : R} (h : Irreducible x) : Squarefree x := by
  rintro y ⟨z, hz⟩
  rw [mul_assoc] at hz
  rcases h.isUnit_or_isUnit hz with (hu | hu)
  · exact hu
  · apply isUnit_of_mul_isUnit_left hu

@[simp]
theorem Prime.squarefree [CancelCommMonoidWithZero R] {x : R} (h : Prime x) : Squarefree x :=
  h.irreducible.squarefree

theorem Squarefree.of_mul_left [Monoid R] {m n : R} (hmn : Squarefree (m * n)) : Squarefree m :=
  fun p hp => hmn p (dvd_mul_of_dvd_left hp n)

theorem Squarefree.of_mul_right [CommMonoid R] {m n : R} (hmn : Squarefree (m * n)) :
    Squarefree n := fun p hp => hmn p (dvd_mul_of_dvd_right hp m)

theorem Squarefree.squarefree_of_dvd [Monoid R] {x y : R} (hdvd : x ∣ y) (hsq : Squarefree y) :
    Squarefree x := fun _ h => hsq _ (h.trans hdvd)

theorem Squarefree.eq_zero_or_one_of_pow_of_not_isUnit [Monoid R] {x : R} {n : ℕ}
    (h : Squarefree (x ^ n)) (h' : ¬ IsUnit x) :
    n = 0 ∨ n = 1 := by
  contrapose! h'
  replace h' : 2 ≤ n := by omega
  have : x * x ∣ x ^ n := by rw [← sq]; exact pow_dvd_pow x h'
  exact h.squarefree_of_dvd this x (refl _)

theorem Squarefree.pow_dvd_of_pow_dvd [Monoid R] {x y : R} {n : ℕ}
    (hx : Squarefree y) (h : x ^ n ∣ y) : x ^ n ∣ x := by
  by_cases hu : IsUnit x
  · exact (hu.pow n).dvd
  · rcases (hx.squarefree_of_dvd h).eq_zero_or_one_of_pow_of_not_isUnit hu with rfl | rfl <;> simp

section SquarefreeGcdOfSquarefree

variable {α : Type*} [CancelCommMonoidWithZero α] [GCDMonoid α]

theorem Squarefree.gcd_right (a : α) {b : α} (hb : Squarefree b) : Squarefree (gcd a b) :=
  hb.squarefree_of_dvd (gcd_dvd_right _ _)

theorem Squarefree.gcd_left {a : α} (b : α) (ha : Squarefree a) : Squarefree (gcd a b) :=
  ha.squarefree_of_dvd (gcd_dvd_left _ _)

end SquarefreeGcdOfSquarefree

theorem squarefree_iff_emultiplicity_le_one [CommMonoid R] (r : R) :
    Squarefree r ↔ ∀ x : R, emultiplicity x r ≤ 1 ∨ IsUnit x := by
  refine forall_congr' fun a => ?_
  rw [← sq, pow_dvd_iff_le_emultiplicity, or_iff_not_imp_left, not_le, imp_congr _ Iff.rfl]
  norm_cast
  rw [← one_add_one_eq_two]
  exact Order.add_one_le_iff_of_not_isMax (by simp)

section Irreducible

variable [CommMonoidWithZero R] [WfDvdMonoid R]

theorem squarefree_iff_no_irreducibles {x : R} (hx₀ : x ≠ 0) :
    Squarefree x ↔ ∀ p, Irreducible p → ¬ (p * p ∣ x) := by
  refine ⟨fun h p hp hp' ↦ hp.not_isUnit (h p hp'), fun h d hd ↦ by_contra fun hdu ↦ ?_⟩
  have hd₀ : d ≠ 0 := ne_zero_of_dvd_ne_zero (ne_zero_of_dvd_ne_zero hx₀ hd) (dvd_mul_left d d)
  obtain ⟨p, irr, dvd⟩ := WfDvdMonoid.exists_irreducible_factor hdu hd₀
  exact h p irr ((mul_dvd_mul dvd dvd).trans hd)

theorem irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree (r : R) :
    (∀ x : R, Irreducible x → ¬x * x ∣ r) ↔ (r = 0 ∧ ∀ x : R, ¬Irreducible x) ∨ Squarefree r := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases eq_or_ne r 0 with (rfl | hr)
    · exact .inl (by simpa using h)
    · exact .inr ((squarefree_iff_no_irreducibles hr).mpr h)
  · rintro (⟨rfl, h⟩ | h)
    · simpa using h
    intro x hx t
    exact hx.not_isUnit (h x t)

theorem squarefree_iff_irreducible_sq_not_dvd_of_ne_zero {r : R} (hr : r ≠ 0) :
    Squarefree r ↔ ∀ x : R, Irreducible x → ¬x * x ∣ r := by
  simpa [hr] using (irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree r).symm

theorem squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible {r : R}
    (hr : ∃ x : R, Irreducible x) : Squarefree r ↔ ∀ x : R, Irreducible x → ¬x * x ∣ r := by
  rw [irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree, ← not_exists]
  simp only [hr, not_true, false_or, and_false]

end Irreducible

section IsRadical

section
variable [CommMonoidWithZero R] [DecompositionMonoid R]

theorem Squarefree.isRadical {x : R} (hx : Squarefree x) : IsRadical x :=
  (isRadical_iff_pow_one_lt 2 one_lt_two).2 fun y hy ↦ by
    obtain ⟨a, b, ha, hb, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul (sq y ▸ hy)
    exact (IsRelPrime.of_squarefree_mul hx).mul_dvd ha hb

theorem Squarefree.dvd_pow_iff_dvd {x y : R} {n : ℕ} (hsq : Squarefree x) (h0 : n ≠ 0) :
    x ∣ y ^ n ↔ x ∣ y := ⟨hsq.isRadical n y, (·.pow h0)⟩

end

variable [CancelCommMonoidWithZero R] {x y p d : R}

theorem IsRadical.squarefree (h0 : x ≠ 0) (h : IsRadical x) : Squarefree x := by
  rintro z ⟨w, rfl⟩
  specialize h 2 (z * w) ⟨w, by simp_rw [pow_two, mul_left_comm, ← mul_assoc]⟩
  rwa [← one_mul (z * w), mul_assoc, mul_dvd_mul_iff_right, ← isUnit_iff_dvd_one] at h
  rw [mul_assoc, mul_ne_zero_iff] at h0; exact h0.2

namespace Squarefree

theorem pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right {k : ℕ}
    (hx : Squarefree x) (hp : Prime p) (h : p ^ (k + 1) ∣ x * y) :
    p ^ k ∣ y := by
  by_cases hxp : p ∣ x
  · obtain ⟨x', rfl⟩ := hxp
    have hx' : ¬ p ∣ x' := fun contra ↦ hp.not_unit <| hx p (mul_dvd_mul_left p contra)
    replace h : p ^ k ∣ x' * y := by
      rw [pow_succ', mul_assoc] at h
      exact (mul_dvd_mul_iff_left hp.ne_zero).mp h
    exact hp.pow_dvd_of_dvd_mul_left _ hx' h
  · exact (pow_dvd_pow _ k.le_succ).trans (hp.pow_dvd_of_dvd_mul_left _ hxp h)

theorem pow_dvd_of_squarefree_of_pow_succ_dvd_mul_left {k : ℕ}
    (hy : Squarefree y) (hp : Prime p) (h : p ^ (k + 1) ∣ x * y) :
    p ^ k ∣ x := by
  rw [mul_comm] at h
  exact pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right hy hp h

variable [DecompositionMonoid R]

theorem dvd_of_squarefree_of_mul_dvd_mul_right (hx : Squarefree x) (h : d * d ∣ x * y) : d ∣ y := by
  nontriviality R
  obtain ⟨a, b, ha, hb, eq⟩ := exists_dvd_and_dvd_of_dvd_mul h
  replace ha : Squarefree a := hx.squarefree_of_dvd ha
  obtain ⟨c, hc⟩ : a ∣ d := ha.isRadical 2 d ⟨b, by rw [sq, eq]⟩
  rw [hc, mul_assoc, (mul_right_injective₀ ha.ne_zero).eq_iff] at eq
  exact dvd_trans ⟨c, by rw [hc, ← eq, mul_comm]⟩ hb

theorem dvd_of_squarefree_of_mul_dvd_mul_left (hy : Squarefree y) (h : d * d ∣ x * y) : d ∣ x :=
  dvd_of_squarefree_of_mul_dvd_mul_right hy (mul_comm x y ▸ h)

end Squarefree

variable [DecompositionMonoid R]

/-- `x * y` is square-free iff `x` and `y` have no common factors and are themselves square-free. -/
theorem squarefree_mul_iff : Squarefree (x * y) ↔ IsRelPrime x y ∧ Squarefree x ∧ Squarefree y :=
  ⟨fun h ↦ ⟨IsRelPrime.of_squarefree_mul h, h.of_mul_left, h.of_mul_right⟩,
    fun ⟨hp, sqx, sqy⟩ _ dvd ↦ hp (sqy.dvd_of_squarefree_of_mul_dvd_mul_left dvd)
      (sqx.dvd_of_squarefree_of_mul_dvd_mul_right dvd)⟩

open scoped Function in
theorem Finset.squarefree_prod_of_pairwise_isCoprime {ι : Type*} {s : Finset ι}
    {f : ι → R} (hs : Set.Pairwise s.toSet (IsRelPrime on f)) (hs' : ∀ i ∈ s, Squarefree (f i)) :
    Squarefree (∏ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons, squarefree_mul_iff]
    rw [Finset.coe_cons, Set.pairwise_insert] at hs
    refine ⟨.prod_right fun i hi ↦ ?_, hs' a (by simp), ?_⟩
    · exact (hs.right i (by simp [hi]) fun h ↦ ha (h ▸ hi)).left
    · exact ih hs.left fun i hi ↦ hs' i <| Finset.mem_cons_of_mem hi

theorem isRadical_iff_squarefree_or_zero : IsRadical x ↔ Squarefree x ∨ x = 0 :=
  ⟨fun hx ↦ (em <| x = 0).elim .inr fun h ↦ .inl <| hx.squarefree h,
    Or.rec Squarefree.isRadical <| by
      rintro rfl
      rw [zero_isRadical_iff]
      infer_instance⟩

theorem isRadical_iff_squarefree_of_ne_zero (h : x ≠ 0) : IsRadical x ↔ Squarefree x :=
  ⟨IsRadical.squarefree h, Squarefree.isRadical⟩

end IsRadical

namespace UniqueFactorizationMonoid

variable [CancelCommMonoidWithZero R] [UniqueFactorizationMonoid R]

lemma _root_.exists_squarefree_dvd_pow_of_ne_zero {x : R} (hx : x ≠ 0) :
    ∃ (y : R) (n : ℕ), Squarefree y ∧ y ∣ x ∧ x ∣ y ^ n := by
  induction x using WfDvdMonoid.induction_on_irreducible with
  | zero => contradiction
  | unit u hu => exact ⟨1, 0, squarefree_one, one_dvd u, hu.dvd⟩
  | mul z p hz hp ih =>
    obtain ⟨y, n, hy, hyx, hy'⟩ := ih hz
    rcases n.eq_zero_or_pos with rfl | hn
    · exact ⟨p, 1, hp.squarefree, dvd_mul_right p z, by simp [isUnit_of_dvd_one (pow_zero y ▸ hy')]⟩
    by_cases hp' : p ∣ y
    · exact ⟨y, n + 1, hy, dvd_mul_of_dvd_right hyx _,
        mul_comm p z ▸ pow_succ y n ▸ mul_dvd_mul hy' hp'⟩
    · suffices Squarefree (p * y) from ⟨p * y, n, this,
        mul_dvd_mul_left p hyx, mul_pow p y n ▸ mul_dvd_mul (dvd_pow_self p hn.ne') hy'⟩
      exact squarefree_mul_iff.mpr ⟨hp.isRelPrime_iff_not_dvd.mpr hp', hp.squarefree, hy⟩

theorem squarefree_iff_nodup_normalizedFactors [NormalizationMonoid R] {x : R}
    (x0 : x ≠ 0) : Squarefree x ↔ Multiset.Nodup (normalizedFactors x) := by
  classical
  rw [squarefree_iff_emultiplicity_le_one, Multiset.nodup_iff_count_le_one]
  haveI := nontrivial_of_ne x 0 x0
  constructor <;> intro h a
  · by_cases hmem : a ∈ normalizedFactors x
    · have ha := irreducible_of_normalized_factor _ hmem
      rcases h a with (h | h)
      · rw [← normalize_normalized_factor _ hmem]
        rw [emultiplicity_eq_count_normalizedFactors ha x0] at h
        assumption_mod_cast
      · have := ha.1
        contradiction
    · simp [Multiset.count_eq_zero_of_notMem hmem]
  · rw [or_iff_not_imp_right]
    intro hu
    rcases eq_or_ne a 0 with rfl | h0
    · simp [x0]
    rcases WfDvdMonoid.exists_irreducible_factor hu h0 with ⟨b, hib, hdvd⟩
    apply le_trans (emultiplicity_le_emultiplicity_of_dvd_left hdvd)
    rw [emultiplicity_eq_count_normalizedFactors hib x0]
    exact_mod_cast h (normalize b)

end UniqueFactorizationMonoid

namespace Int

@[simp]
theorem squarefree_natAbs {n : ℤ} : Squarefree n.natAbs ↔ Squarefree n := by
  simp_rw [Squarefree, natAbs_surjective.forall, ← natAbs_mul, natAbs_dvd_natAbs,
    isUnit_iff_natAbs_eq, Nat.isUnit_iff]

@[simp]
theorem squarefree_natCast {n : ℕ} : Squarefree (n : ℤ) ↔ Squarefree n := by
  rw [← squarefree_natAbs, natAbs_natCast]

end Int
