/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Riccardo Brasca

-/
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Cyclotomic units.

We gather miscellaneous results about units given by sums of powers of roots of unit, the so called
*cyclotomic units*.


## Main results

* `IsPrimitiveRoot.associated_pow_sub_one_of_coprime` : given an `n`-th primitive root of unity `ζ,`
  we have that `ζ - 1` and `ζ ^ j - 1` are associated for all `j` coprime with `n`.
* `IsPrimitiveRoot.associated_pow_sub_one_pow_of_coprime` : given an `n`-th primitive root of unity
  `ζ`, we have that `ζ ^ j - 1` and `ζ ^ j - 1` are associated for all `i` and `j` coprime with `n`.
* `IsPrimitiveRoot.associated_pow_add_sub_sub_one` : given an `n`-th primitive root of unity `ζ`,
  where `2 ≤ n`, we have that `ζ - 1` and `ζ ^ (i + j) - ζ ^ i` are associated for all and `j`
  coprime with `n` and all `i`.

## Implementation details

We sometimes state series of results of the form `a = u * b`, `IsUnit u` and `Associated a b`.
Often, `Associated a b` is everything one needs, and it is more convenient to use, we include the
other version for completeness.
-/

open Polynomial Finset Nat

variable {n i j k p : ℕ} {A K : Type*} {ζ : A}

variable [CommRing A] [IsDomain A]

namespace IsPrimitiveRoot

/-- Given an `n`-th primitive root of unity `ζ,` we have that `ζ - 1` and `ζ ^ j - 1` are associated
  for all `j` coprime with `n`. -/
theorem associated_pow_sub_one_of_coprime (hζ : IsPrimitiveRoot ζ n) (hj : j.Coprime n) :
    Associated (ζ - 1) (ζ ^ j - 1) := by
  refine associated_of_dvd_dvd ⟨∑ i ∈ range j, ζ ^ i, (mul_geom_sum _ _).symm⟩ ?_
  match n with
  | 0 => simp_all
  | 1 => simp_all
  | n + 2 =>
      obtain ⟨m, hm⟩ := exists_mul_emod_eq_one_of_coprime hj (by omega)
      use ∑ i ∈ range m, (ζ ^ j) ^ i
      rw [mul_geom_sum, ← pow_mul, ← pow_mod_orderOf, ← hζ.eq_orderOf, hm, pow_one]

/-- Given an `n`-th primitive root of unity `ζ`, we have that `ζ ^ j - 1` and `ζ ^ j - 1` are
  associated for all `i` and `j` coprime with `n`. -/
theorem associated_pow_sub_one_pow_of_coprime (hζ : IsPrimitiveRoot ζ n)
    (hk : k.Coprime n) (hj : j.Coprime n) : Associated (ζ ^ j - 1) (ζ ^ k - 1) := by
  suffices ∀ {j}, (j.Coprime n) → Associated (ζ - 1) (ζ ^ j - 1) by
    grind [Associated.trans, Associated.symm]
  exact hζ.associated_pow_sub_one_of_coprime

/-- Given an `n`-th primitive root of unity `ζ`, where `2 ≤ n`, we have that `∑ i ∈ range k, ζ ^ i`
  is a unit for all `i` and `j` coprime with `n`. This is the unit given by
  `associated_pow_sub_one_pow_of_coprime` (see
  `pow_sub_one_mul_geom_sum_eq_pow_sub_one_mul_geom_sum` below). -/
theorem geom_sum_isUnit (hζ : IsPrimitiveRoot ζ n) (hn : 2 ≤ n) (hk : k.Coprime n) :
    IsUnit (∑ i ∈ range k, ζ ^ i) := by
  obtain ⟨u, hu⟩ := hζ.associated_pow_sub_one_pow_of_coprime hk (coprime_one_left n)
  convert u.isUnit
  apply mul_right_injective₀ (show 1 - ζ ≠ 0 by grind [sub_one_ne_zero])
  grind [mul_neg_geom_sum]

/-- The explicit formula giving `associated_pow_sub_one_pow_of_coprime` above. -/
theorem pow_sub_one_mul_geom_sum_eq_pow_sub_one_mul_geom_sum (hζ : IsPrimitiveRoot ζ n)
    (hn : 2 ≤ n) : (ζ ^ j - 1) * ∑ i ∈ range k, ζ ^ i = (ζ ^ k - 1) * ∑ i ∈ range j, ζ ^ i := by
  apply mul_left_injective₀ (hζ.sub_one_ne_zero (by omega))
  grind [geom_sum_mul]

theorem pow_sub_one_eq_geom_sum_mul_geom_sum_inv_mul_pow_sub_one (hζ : IsPrimitiveRoot ζ n)
    (hn : 2 ≤ n) (hk : k.Coprime n) (hj : j.Coprime n) : (ζ ^ j - 1) =
      (hζ.geom_sum_isUnit hn hj).unit * (hζ.geom_sum_isUnit hn hk).unit⁻¹ * (ζ ^ k - 1) := by
  grind [IsUnit.mul_val_inv, pow_sub_one_mul_geom_sum_eq_pow_sub_one_mul_geom_sum, IsUnit.unit_spec]

/-- Given an `n`-th primitive root of unity `ζ`, where `2 ≤ n`, we have that `ζ - 1` and
  `ζ ^ (i + j) - ζ ^ i` are associated for all and `j` coprime with `n` and all `i`. See
  `pow_sub_one_eq_geom_sum_mul_geom_sum_inv_mul_pow_sub_one` above for the explicit formula of the
  unit. -/
theorem associated_pow_add_sub_sub_one (hζ : IsPrimitiveRoot ζ n) (hn : 2 ≤ n) (i : ℕ)
    (hjn : j.Coprime n) : Associated (ζ - 1) (ζ ^ (i + j) - ζ ^ i) := by
  use (hζ.isUnit (by omega)).unit ^ i * (hζ.geom_sum_isUnit hn hjn).unit
  suffices (ζ - 1) * ζ ^ i * ∑ i ∈ range j, ζ ^ i = (ζ ^ (i + j) - ζ ^ i) by
    simp [← this, mul_assoc]
  grind [mul_geom_sum]

/-- If `p` is prime and `ζ` is a `p`-th primitive root of unit, then `ζ - 1` and `η₁ - η₂` are
  associated for all distincts `p`-th root of unit `η₁` and `η₂`. -/
lemma associated_sub_one_mem_nthRootsFinset_sub (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime)
      {η₁ η₂ : A} (hη₁ : η₁ ∈ nthRootsFinset p 1) (hη₂ : η₂ ∈ nthRootsFinset p 1) (e : η₁ ≠ η₂) :
    Associated (ζ - 1) (η₁ - η₂) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i, hi, rfl⟩ :=
    hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hp.pos 1).1 hη₁)
  obtain ⟨j, hj, rfl⟩ :=
    hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hp.pos 1).1 hη₂)
  wlog hij : j ≤ i
  · simpa using (this hζ ‹_› ‹_› _ hj ‹_› _ hi ‹_› e.symm (by omega)).neg_right
  have H : (i - j).Coprime p := (coprime_of_lt_prime (by grind) (by grind) hp).symm
  obtain ⟨u, h⟩ := hζ.associated_pow_add_sub_sub_one hp.two_le j H
  simp only [hij, add_tsub_cancel_of_le] at h
  rw [← h, associated_mul_unit_right_iff]


end IsPrimitiveRoot
