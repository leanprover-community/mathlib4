/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Lemmas about `ℤₘ₀`.
-/

assert_not_exists Ring

local notation "ℤₘ₀" => WithZero (Multiplicative ℤ)

namespace WithZero

open Multiplicative

theorem ofAdd_zpow (a : ℤ) : (↑(ofAdd a) : ℤₘ₀) = ofAdd (1 : ℤ) ^ a := by
  rw [← WithZero.coe_zpow, WithZero.coe_inj, ← Int.ofAdd_mul, one_mul]

theorem ofAdd_neg_one_pow_comm (a : ℤ) (n : ℕ) :
    ((↑(ofAdd (-1 : ℤ)) : ℤₘ₀) ^ (-a)) ^ n = ofAdd (n : ℤ) ^ a := by
  rw [ofAdd_zpow (-1)]
  simp only [zpow_neg, zpow_one, inv_zpow', inv_inv, coe_zpow]
  rw [← zpow_natCast, zpow_comm, ← ofAdd_zpow]

end WithZero

#min_imports

#exit

-- open scoped Multiplicative

-- **CHECK FROM HERE ON**
open Multiplicative

instance : IsCyclic ℤₘ₀ˣ :=
  isCyclic_of_surjective WithZero.unitsWithZeroEquiv.symm (MulEquiv.surjective _)

instance : Nontrivial ℤₘ₀ˣ :=
  Function.Surjective.nontrivial (f := WithZero.unitsWithZeroEquiv) (MulEquiv.surjective _)

open Subgroup
lemma top_eq_zpowers_neg_one :
    zpowers (ofAdd (-1 : ℤ)) = (⊤ : Subgroup (Multiplicative ℤ)) := by
  rw [← coe_eq_univ, ← ofAdd_image_zmultiples_eq_zpowers_ofAdd]
  simp

open LinearOrderedCommGroup WithZero in
lemma genLTOne_eq_neg_one : unitsWithZeroEquiv.symm (ofAdd (-1 : ℤ)) = (genLTOne (ℤₘ₀ˣ)) :=  by
  let e := (unitsWithZeroEquiv (α := Multiplicative ℤ)).symm
  refine genLTOne_unique (e (ofAdd (-1 : ℤ))) ⟨?_, ?_⟩
  · simpa only [Int.reduceNeg, ofAdd_neg, map_inv, Left.inv_lt_one_iff] using
      compareOfLessAndEq_eq_lt.mp rfl
  rw [← map_top_of_surjective e.toMonoidHom (MulEquiv.surjective _), ← top_eq_zpowers_neg_one,
    MonoidHom.map_zpowers]
  rfl


end Multiplicative
