/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Xavier Roblot
-/
import Mathlib.Algebra.Regular.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Torsion-free monoids with zero

We prove that if `M` is an `UniqueFactorizationMonoid` that can be equipped with a
`NormalizationMonoid` structure and such that `Mˣ` is torsion-free, then `M` is torsion-free.

Note. You need to import this file to get that the monoid of ideals of a Dedekind domain is
torsion-free.
-/

variable {M : Type*} [CancelCommMonoidWithZero M]

theorem IsMulTorsionFree.mk' (ih : ∀ x ≠ 0, ∀ y ≠ 0, ∀ n ≠ 0, (x ^ n : M) = y ^ n → x = y) :
    IsMulTorsionFree M := by
  refine ⟨fun n hn x y hxy ↦ ?_⟩
  by_cases h : x ≠ 0 ∧ y ≠ 0
  · exact ih x h.1 y h.2 n hn hxy
  grind [pow_eq_zero, zero_pow]

variable [UniqueFactorizationMonoid M] [NormalizationMonoid M] [IsMulTorsionFree Mˣ]

namespace UniqueFactorizationMonoid

instance : IsMulTorsionFree M := by
  refine .mk' fun x hx y hy n hn hxy ↦ ?_
  obtain ⟨u, hu⟩ : Associated x y := by
    have := (Associated.of_eq hxy).normalizedFactors_eq
    rwa [normalizedFactors_pow, normalizedFactors_pow, nsmul_right_inj hn,
      ← associated_iff_normalizedFactors_eq_normalizedFactors hx hy] at this
  replace hx : IsLeftRegular (x ^ n) := (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hx).pow n
  rw [← hu, mul_pow, eq_comm, IsLeftRegular.mul_left_eq_self_iff hx, ← Units.val_pow_eq_pow_val,
    Units.val_eq_one, IsMulTorsionFree.pow_eq_one_iff_left hn] at hxy
  rwa [hxy, Units.val_one, mul_one] at hu

end UniqueFactorizationMonoid
