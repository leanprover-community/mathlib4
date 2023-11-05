/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Polynomial.Content

#align_import algebra.gcd_monoid.div from "leanprover-community/mathlib"@"b537794f8409bc9598febb79cd510b1df5f4539d"

/-!
# Basic results about setwise gcds on normalized gcd monoid with a division.

## Main results

* `Finset.Nat.gcd_div_eq_one`: given a nonempty Finset `s` and a function `f` from `s` to
  `ℕ`, if `d = s.gcd`, then the `gcd` of `(f i) / d` equals `1`.
* `Finset.Int.gcd_div_eq_one`: given a nonempty Finset `s` and a function `f` from `s` to
  `ℤ`, if `d = s.gcd`, then the `gcd` of `(f i) / d` equals `1`.
* `Finset.Polynomial.gcd_div_eq_one`: given a nonempty Finset `s` and a function `f` from
  `s` to `K[X]`, if `d = s.gcd`, then the `gcd` of `(f i) / d` equals `1`.

## TODO
Add a typeclass to state these results uniformly.

-/


namespace Finset

namespace Nat

/-- Given a nonempty Finset `s` and a function `f` from `s` to `ℕ`, if `d = s.gcd`,
then the `gcd` of `(f i) / d` is equal to `1`. -/
theorem gcd_div_eq_one {β : Type*} {f : β → ℕ} (s : Finset β) {x : β} (hx : x ∈ s)
    (hfz : f x ≠ 0) : (s.gcd fun b => f b / s.gcd f) = 1 := by
  obtain ⟨g, he, hg⟩ := Finset.extract_gcd f ⟨x, hx⟩
  refine' (Finset.gcd_congr rfl fun a ha => _).trans hg
  rw [he a ha, Nat.mul_div_cancel_left]
  exact Nat.pos_of_ne_zero (mt Finset.gcd_eq_zero_iff.1 fun h => hfz <| h x hx)
#align finset.nat.gcd_div_eq_one Finset.Nat.gcd_div_eq_one

theorem gcd_div_id_eq_one {s : Finset ℕ} {x : ℕ} (hx : x ∈ s) (hnz : x ≠ 0) :
    (s.gcd fun b => b / s.gcd id) = 1 :=
  gcd_div_eq_one s hx hnz
#align finset.nat.gcd_div_id_eq_one Finset.Nat.gcd_div_id_eq_one

end Nat

namespace Int

/-- Given a nonempty Finset `s` and a function `f` from `s` to `ℤ`, if `d = s.gcd`,
then the `gcd` of `(f i) / d` is equal to `1`. -/
theorem gcd_div_eq_one {β : Type*} {f : β → ℤ} (s : Finset β) {x : β} (hx : x ∈ s)
    (hfz : f x ≠ 0) : (s.gcd fun b => f b / s.gcd f) = 1 := by
  obtain ⟨g, he, hg⟩ := Finset.extract_gcd f ⟨x, hx⟩
  refine' (Finset.gcd_congr rfl fun a ha => _).trans hg
  rw [he a ha, Int.mul_ediv_cancel_left]
  exact mt Finset.gcd_eq_zero_iff.1 fun h => hfz <| h x hx
#align finset.int.gcd_div_eq_one Finset.Int.gcd_div_eq_one

theorem gcd_div_id_eq_one {s : Finset ℤ} {x : ℤ} (hx : x ∈ s) (hnz : x ≠ 0) :
    (s.gcd fun b => b / s.gcd id) = 1 :=
  gcd_div_eq_one s hx hnz
#align finset.int.gcd_div_id_eq_one Finset.Int.gcd_div_id_eq_one

end Int

namespace Polynomial

open Polynomial Classical

noncomputable section

variable {K : Type*} [Field K]

/-- Given a nonempty Finset `s` and a function `f` from `s` to `K[X]`, if `d = s.gcd f`,
then the `gcd` of `(f i) / d` is equal to `1`. -/
theorem gcd_div_eq_one {β : Type*} {f : β → Polynomial K} (s : Finset β) {x : β} (hx : x ∈ s)
    (hfz : f x ≠ 0) : (s.gcd fun b => f b / s.gcd f) = 1 := by
  obtain ⟨g, he, hg⟩ := Finset.extract_gcd f ⟨x, hx⟩
  refine' (Finset.gcd_congr rfl fun a ha => _).trans hg
  rw [he a ha, EuclideanDomain.mul_div_cancel_left]
  exact mt Finset.gcd_eq_zero_iff.1 fun h => hfz <| h x hx
#align finset.polynomial.gcd_div_eq_one Finset.Polynomial.gcd_div_eq_one

theorem gcd_div_id_eq_one {s : Finset (Polynomial K)} {x : Polynomial K}
    (hx : x ∈ s) (hnz : x ≠ 0) : (s.gcd fun b => b / s.gcd id) = 1 :=
  gcd_div_eq_one s hx hnz
#align finset.polynomial.gcd_div_id_eq_one Finset.Polynomial.gcd_div_id_eq_one

end

end Polynomial

end Finset
