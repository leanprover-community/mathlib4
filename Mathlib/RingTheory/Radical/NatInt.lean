/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Arend Mellendijk
-/
module

public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.RingTheory.Radical.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Nat

/-!
# The radical in `ℕ`

- `UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors`: The prime factors of a natural number
  are the same as the prime factors defined in `Nat.primeFactors`.
- `Nat.radical_le_self_iff`: if `n ≠ 0`, `radical n ≤ n`.
- `Nat.two_le_radical_iff`: `2 ≤ n.radical` iff `2 ≤ n`.

## TODO

Add declarations for `ℤ`.
-/

@[expose] public section

open UniqueFactorizationMonoid

section Nat

lemma UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors :
    primeFactors = Nat.primeFactors := by
  ext n : 1
  rw [primeFactors, Nat.factors_eq, Nat.primeFactors]
  -- this convert is necessary because of the different DecidableEq instances
  convert List.toFinset_coe _

namespace Nat

@[simp] theorem radical_le_self_iff {n : ℕ} : radical n ≤ n ↔ n ≠ 0 :=
  ⟨by aesop, fun h ↦ Nat.le_of_dvd (by lia) radical_dvd_self⟩

@[simp] theorem two_le_radical_iff {n : ℕ} : 2 ≤ radical n ↔ 2 ≤ n := by
  refine ⟨?_, ?_⟩
  · match n with | 0 | 1 | _ + 2 => simp
  · intro hn
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by lia)
    trans p
    · apply hp.two_le
    · apply Nat.le_of_dvd (Nat.pos_of_ne_zero radical_ne_zero)
      rwa [dvd_radical_iff_of_irreducible hp.prime.irreducible (by lia)]

@[simp] theorem one_lt_radical_iff {n : ℕ} : 1 < radical n ↔ 1 < n := two_le_radical_iff

@[simp] theorem radical_le_one_iff {n : ℕ} : radical n ≤ 1 ↔ n ≤ 1 := by
  simpa only [not_lt] using one_lt_radical_iff.not

theorem radical_pos (n : ℕ) : 0 < radical n := pos_of_ne_zero radical_ne_zero

open Qq Lean Mathlib.Meta Finset

namespace Mathlib.Meta.Positivity
open Positivity

attribute [local instance] monadLiftOptionMetaM in
/-- Positivity extension for radical. Proves radicals are nonzero. -/
@[positivity UniqueFactorizationMonoid.radical _]
meta def evalRadical : PositivityExt where eval {u α} _ _ e := do
  match e with
  | ~q(@radical _ $inst $inst' $inst'' $n) =>
    have _ := ← synthInstanceQ q(Nontrivial $α)
    assertInstancesCommute
    return .nonzero q(radical_ne_zero)
  | _ => throwError "not radical"

example : 0 < radical 100 := by positivity

end Mathlib.Meta.Positivity

end Nat

end Nat
