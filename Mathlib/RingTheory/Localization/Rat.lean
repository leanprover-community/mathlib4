/-
Copyright (c) 2025 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
module

public import Mathlib.RingTheory.Localization.NumDen
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Ring-theoretic fractions in `ℚ`
-/

public section

namespace Rat

open IsFractionRing

theorem isLocalizationIsInteger_iff (q : ℚ) :
    IsLocalization.IsInteger ℤ q ↔ q ∈ Set.range Int.cast := by
  simp [IsLocalization.IsInteger]

theorem associated_num_den (q : ℚ) :
    Associated (IsFractionRing.num ℤ q) q.num ∧ Associated (IsFractionRing.den ℤ q : ℤ) q.den :=
  num_den_unique ℤ q q.num ⟨q.den, by simp⟩
    (by simpa [isRelPrime_iff_isCoprime, Int.isCoprime_iff_nat_coprime] using q.reduced)
    (by simp [Rat.num_div_den])

theorem isFractionRingDen (q : ℚ) : (IsFractionRing.den ℤ q : ℤ).natAbs = q.den := by
  simpa [Int.associated_iff_natAbs] using q.associated_num_den.2

theorem isFractionRingNum (q : ℚ) : Associated (IsFractionRing.num ℤ q : ℤ) q.num :=
  q.associated_num_den.1

end Rat
