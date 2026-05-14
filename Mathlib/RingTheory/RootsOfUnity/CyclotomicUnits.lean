/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Riccardo Brasca
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Ring.Associated
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Cyclotomic units.

We gather miscellaneous results about units given by sums of powers of roots of unit, the so-called
*cyclotomic units*.


## Main results

* `IsPrimitiveRoot.associated_sub_one_pow_sub_one_of_coprime` : given an `n`-th primitive root of
  unity `ζ`, we have that `ζ - 1` and `ζ ^ j - 1` are associated for all `j` coprime with `n`.
* `IsPrimitiveRoot.associated_pow_sub_one_pow_of_coprime` : given an `n`-th primitive root of unity
  `ζ`, we have that `ζ ^ i - 1` and `ζ ^ j - 1` are associated for all `i` and `j` coprime with `n`.
* `IsPrimitiveRoot.associated_pow_add_sub_sub_one` : given an `n`-th primitive root of unity `ζ`,
  where `2 ≤ n`, we have that `ζ - 1` and `ζ ^ (i + j) - ζ ^ i` are associated for all and `j`
  coprime with `n` and all `i`.

## Implementation details

We sometimes state series of results of the form `a = u * b`, `IsUnit u` and `Associated a b`.
Often, `Associated a b` is everything one needs, and it is more convenient to use, we include the
other version for completeness.
-/

public section

open Polynomial Finset Nat

variable {n i j p : ℕ} {A K : Type*} {ζ : A}

variable [CommRing A] [IsDomain A] {R : Type*} [CommRing R] [Algebra R A]

namespace IsPrimitiveRoot

/-- Given an `n`-th primitive root of unity `ζ,` we have that `ζ - 1` and `ζ ^ j - 1` are associated
  for all `j` coprime with `n`.
  `pow_sub_one_mul_geom_sum_eq_pow_sub_one_mul_geom_sum` gives an explicit formula for the unit. -/
theorem associated_sub_one_pow_sub_one_of_coprime (hζ : IsPrimitiveRoot ζ n) (hj : j.Coprime n) :
    Associated (ζ - 1) (ζ ^ j - 1) := by
  refine associated_of_dvd_dvd ⟨∑ i ∈ range j, ζ ^ i, (mul_geom_sum _ _).symm⟩ ?_
  match n with
  | 0 => simp_all
  | 1 => simp_all
  | n + 2 =>
      obtain ⟨m, -, hm⟩ := exists_mul_mod_eq_one_of_coprime hj (by lia)
      use ∑ i ∈ range m, (ζ ^ j) ^ i
      rw [mul_geom_sum, ← pow_mul, ← pow_mod_orderOf, ← hζ.eq_orderOf, hm, pow_one]

/-- Given an `n`-th primitive root of unity `ζ`, we have that `ζ ^ j - 1` and `ζ ^ i - 1` are
  associated for all `i` and `j` coprime with `n`. -/
theorem associated_pow_sub_one_pow_of_coprime (hζ : IsPrimitiveRoot ζ n)
    (hi : i.Coprime n) (hj : j.Coprime n) : Associated (ζ ^ j - 1) (ζ ^ i - 1) := by
  suffices ∀ {j}, j.Coprime n → Associated (ζ - 1) (ζ ^ j - 1) by
    grind [Associated.trans, Associated.symm]
  exact hζ.associated_sub_one_pow_sub_one_of_coprime

/-- Given an `n`-th primitive root of unity `ζ`, we have that `ζ - 1` is associated to any of its
  conjugate. -/
theorem associated_sub_one_map_sub_one {n : ℕ} [NeZero n] (hζ : IsPrimitiveRoot ζ n)
    (σ : A ≃ₐ[R] A) : Associated (ζ - 1) (σ (ζ - 1)) := by
  rw [map_sub, map_one, ← hζ.autToPow_spec R σ]
  apply hζ.associated_sub_one_pow_sub_one_of_coprime
  exact ZMod.val_coe_unit_coprime ((autToPow R hζ) σ)

/-- Given an `n`-th primitive root of unity `ζ`, we have that two conjugates of `ζ - 1`
  are associated. -/
theorem associated_map_sub_one_map_sub_one {n : ℕ} [NeZero n] (hζ : IsPrimitiveRoot ζ n)
    (σ τ : A ≃ₐ[R] A) : Associated (σ (ζ - 1)) (τ (ζ - 1)) := by
  rw [map_sub, map_sub, map_one, map_one, ← hζ.autToPow_spec R σ, ← hζ.autToPow_spec R τ]
  apply hζ.associated_pow_sub_one_pow_of_coprime <;>
  exact ZMod.val_coe_unit_coprime ((autToPow R hζ) _)

/-- Given an `n`-th primitive root of unity `ζ`, where `2 ≤ n`, we have that `∑ i ∈ range j, ζ ^ i`
  is a unit for all `j` coprime with `n`. This is the unit given by
  `associated_pow_sub_one_pow_of_coprime` (see
  `pow_sub_one_mul_geom_sum_eq_pow_sub_one_mul_geom_sum`). -/
theorem geom_sum_isUnit (hζ : IsPrimitiveRoot ζ n) (hn : 2 ≤ n) (hj : j.Coprime n) :
    IsUnit (∑ i ∈ range j, ζ ^ i) := by
  obtain ⟨u, hu⟩ := hζ.associated_pow_sub_one_pow_of_coprime hj (coprime_one_left n)
  convert u.isUnit
  apply mul_right_injective₀ (show 1 - ζ ≠ 0 by grind [sub_one_ne_zero])
  grind [mul_neg_geom_sum]

/-- Similar to `geom_sum_isUnit`, but instead of assuming `2 ≤ n` we assume that `j` is a unit in
  `A`. -/
theorem geom_sum_isUnit' (hζ : IsPrimitiveRoot ζ n) (hj : j.Coprime n) (hj_Unit : IsUnit (j : A)) :
    IsUnit (∑ i ∈ range j, ζ ^ i) := by
  match n with
  | 0 => simp_all
  | 1 => simp_all
  | n + 2 => exact geom_sum_isUnit hζ (by linarith) hj

theorem pow_sub_one_eq_geom_sum_mul_geom_sum_inv_mul_pow_sub_one (hζ : IsPrimitiveRoot ζ n)
    (hn : 2 ≤ n) (hi : i.Coprime n) (hj : j.Coprime n) :
    (ζ ^ j - 1) =
      (hζ.geom_sum_isUnit hn hj).unit * (hζ.geom_sum_isUnit hn hi).unit⁻¹ * (ζ ^ i - 1) := by
  grind [IsUnit.mul_val_inv, pow_sub_one_mul_geom_sum_eq_pow_sub_one_mul_geom_sum, IsUnit.unit_spec]

/-- Given an `n`-th primitive root of unity `ζ`, where `2 ≤ n`, we have that `ζ - 1` and
  `ζ ^ (i + j) - ζ ^ i` are associated for all and `j` coprime with `n` and all `i`. See
  `pow_sub_one_eq_geom_sum_mul_geom_sum_inv_mul_pow_sub_one` for the explicit formula of the
  unit. -/
theorem associated_pow_add_sub_sub_one (hζ : IsPrimitiveRoot ζ n) (hn : 2 ≤ n) (i : ℕ)
    (hjn : j.Coprime n) : Associated (ζ - 1) (ζ ^ (i + j) - ζ ^ i) := by
  use (hζ.isUnit (by lia)).unit ^ i * (hζ.geom_sum_isUnit hn hjn).unit
  suffices (ζ - 1) * ζ ^ i * ∑ i ∈ range j, ζ ^ i = (ζ ^ (i + j) - ζ ^ i) by
    simp [← this, mul_assoc]
  grind [mul_geom_sum]

/-- If `p` is prime and `ζ` is a `p`-th primitive root of unity, then `ζ - 1` and `η₁ - η₂` are
  associated for all distinct `p`-th roots of unity `η₁` and `η₂`. -/
lemma ntRootsFinset_pairwise_associated_sub_one_sub_of_prime (hζ : IsPrimitiveRoot ζ p)
    (hp : p.Prime) :
    Set.Pairwise (nthRootsFinset p (1 : A)) (fun η₁ η₂ ↦ Associated (ζ - 1) (η₁ - η₂)) := by
  intro η₁ hη₁ η₂ hη₂ e
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i, hi, rfl⟩ :=
    hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hp.pos 1).1 hη₁)
  obtain ⟨j, hj, rfl⟩ :=
    hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hp.pos 1).1 hη₂)
  wlog hij : j ≤ i
  · simpa using (this hζ ‹_› ‹_› _ hj ‹_› _ hi ‹_› e.symm (by lia)).neg_right
  have H : (i - j).Coprime p := (coprime_of_lt_prime (by grind) (by grind) hp).symm
  obtain ⟨u, h⟩ := hζ.associated_pow_add_sub_sub_one hp.two_le j H
  simp only [hij, add_tsub_cancel_of_le] at h
  rw [← h, associated_mul_unit_right_iff]

end IsPrimitiveRoot
