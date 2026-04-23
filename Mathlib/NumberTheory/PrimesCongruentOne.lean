/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Init
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.ArithMult.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!
# Primes congruent to one

We prove that, for any positive `k : ℕ`, there are infinitely many primes `p` such that
`p ≡ 1 [MOD k]`.
-/

public section


namespace Nat

open Polynomial Nat Filter

open scoped Nat

/-- For any positive `k : ℕ` there exists an arbitrarily large prime `p` such that
`p ≡ 1 [MOD k]`. -/
theorem exists_prime_gt_modEq_one {k : ℕ} (n : ℕ) (hk0 : k ≠ 0) :
    ∃ p : ℕ, Nat.Prime p ∧ n < p ∧ p ≡ 1 [MOD k] := by
  rcases (one_le_iff_ne_zero.2 hk0).eq_or_lt with (rfl | hk1)
  · rcases exists_infinite_primes (n + 1) with ⟨p, hnp, hp⟩
    exact ⟨p, hp, hnp, modEq_one⟩
  let b := k * (n !)
  have hgt : 1 < (eval (↑b) (cyclotomic k ℤ)).natAbs := by
    rcases le_iff_exists_add'.1 hk1.le with ⟨k, rfl⟩
    have hb : 2 ≤ b := le_mul_of_le_of_one_le hk1 n.factorial_pos
    calc
      1 ≤ b - 1 := le_tsub_of_add_le_left hb
      _ < (eval (b : ℤ) (cyclotomic (k + 1) ℤ)).natAbs :=
        sub_one_lt_natAbs_cyclotomic_eval hk1 (succ_le_iff.1 hb).ne'
  let p := minFac (eval (↑b) (cyclotomic k ℤ)).natAbs
  haveI hprime : Fact p.Prime := ⟨minFac_prime (ne_of_lt hgt).symm⟩
  have hroot : IsRoot (cyclotomic k (ZMod p)) (castRingHom (ZMod p) b) := by
    have : ((b : ℤ) : ZMod p) = ↑(Int.castRingHom (ZMod p) b) := by simp
    rw [IsRoot.def, ← map_cyclotomic_int k (ZMod p), eval_map, coe_castRingHom,
      ← Int.cast_natCast, this, eval₂_hom, Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd]
    apply Int.dvd_natAbs.1
    exact mod_cast minFac_dvd (eval (↑b) (cyclotomic k ℤ)).natAbs
  have hpb : ¬p ∣ b :=
    hprime.1.coprime_iff_not_dvd.1 (coprime_of_root_cyclotomic hk0.bot_lt hroot).symm
  refine ⟨p, hprime.1, not_le.1 fun habs => ?_, ?_⟩
  · exact hpb (dvd_mul_of_dvd_right (dvd_factorial (minFac_pos _) habs) _)
  · have hdiv : orderOf (b : ZMod p) ∣ p - 1 :=
      ZMod.orderOf_dvd_card_sub_one (mt (CharP.cast_eq_zero_iff _ _ _).1 hpb)
    haveI : NeZero (k : ZMod p) :=
      NeZero.of_not_dvd (ZMod p) fun hpk => hpb (dvd_mul_of_dvd_left hpk _)
    have : k = orderOf (b : ZMod p) := (isRoot_cyclotomic_iff.mp hroot).eq_orderOf
    rw [← this] at hdiv
    exact ((modEq_iff_dvd' hprime.1.pos).2 hdiv).symm

theorem frequently_atTop_modEq_one {k : ℕ} (hk0 : k ≠ 0) :
    ∃ᶠ p in atTop, Nat.Prime p ∧ p ≡ 1 [MOD k] := by
  refine frequently_atTop.2 fun n => ?_
  obtain ⟨p, hp⟩ := exists_prime_gt_modEq_one n hk0
  exact ⟨p, ⟨hp.2.1.le, hp.1, hp.2.2⟩⟩

/-- For any positive `k : ℕ` there are infinitely many primes `p` such that `p ≡ 1 [MOD k]`. -/
theorem infinite_setOf_prime_modEq_one {k : ℕ} (hk0 : k ≠ 0) :
    Set.Infinite {p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD k]} :=
  frequently_atTop_iff_infinite.1 (frequently_atTop_modEq_one hk0)

end Nat
