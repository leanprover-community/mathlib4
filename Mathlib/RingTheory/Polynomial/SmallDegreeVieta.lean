/-
Copyright (c) 2025 Qinchuan Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qinchuan Zhang
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Vieta's Formula for polynomial of small degrees.
-/

namespace Multiset

-- TODO: `Multiset.insert_eq_cons` being simp means that `esymm {x1, x2}` is not simp normal form
@[simp] lemma esymm_pair_one {R : Type*} [CommSemiring R] (x1 x2 : R) :
    esymm (x1 ::ₘ {x2}) 1 = x2 + x1 := by
  simp [esymm, powersetCard_one]

@[simp] lemma esymm_pair_two {R : Type*} [CommSemiring R] (x1 x2 : R) :
    esymm (x1 ::ₘ {x2}) 2 = x1 * x2 := by
  simp [esymm, powersetCard_one]

end Multiset

namespace Polynomial

/-- **Vieta's formula** for quadratic in term of `Polynomial.roots`.
This is a consequence of `Polynomial.coeff_eq_esymm_roots_of_card`. -/
lemma quadratic_vieta {R : Type*} [CommRing R] [IsDomain R] {a b c x1 x2 : R}
    (hroots : (C a * X ^ 2 + C b * X + C c).roots = {x1, x2}) :
    b = -a * (x1 + x2) ∧ c = a * x1 * x2 := by
  let p : R[X] := C a * X ^ 2 + C b * X + C c
  have := p.card_roots'
  have hp_natDegree : p.natDegree = 2 := le_antisymm natDegree_quadratic_le
    (by convert p.card_roots'; rw [hroots, Multiset.card_pair])
  have hp_roots_card : p.roots.card = p.natDegree := by
    rw [hp_natDegree, hroots, Multiset.card_pair]
  simpa [leadingCoeff, hp_natDegree, p, hroots, mul_assoc, add_comm x1] using
    And.intro (coeff_eq_esymm_roots_of_card hp_roots_card (k := 1) (by norm_num [hp_natDegree]))
      (coeff_eq_esymm_roots_of_card hp_roots_card (k := 0) (by norm_num [hp_natDegree]))

/-- **Vieta's formula** for quadratic in term of `Polynomial.roots`. -/
lemma quadratic_vieta' {R : Type*} [Field R] {a b c x1 x2 : R} (ha : a ≠ 0)
    (hroots : (C a * X ^ 2 + C b * X + C c).roots = {x1, x2}) :
    x1 + x2 = -b / a ∧ x1 * x2 = c / a := by
  refine And.imp ?_ ?_ (quadratic_vieta hroots)
  · field_simp; intro h; linear_combination h
  · field_simp; intro h; linear_combination -h

end Polynomial
