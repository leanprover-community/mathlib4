/-
Copyright (c) 2025 Qinchuan Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qinchuan Zhang
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
-- import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Vieta's Formula for polynomial of small degrees.
-/

namespace Polynomial

variable {R T S : Type*}

/-- **Vieta's formula** for quadratics. -/
lemma eq_neg_mul_add_of_roots_quadratic_eq_pair [CommRing R] [IsDomain R] {x1 x2 : R} {p : R[X]}
    (hp : p.natDegree = 2) (hroots : p.roots = {x1, x2}) :
    p.coeff 1 = -p.coeff 2 * (x1 + x2) := by
  have hp_roots_card : p.roots.card = p.natDegree := by
    rw [hp, hroots, Multiset.card_pair]
  simpa [leadingCoeff, hp, hroots, mul_assoc, add_comm x1] using
    coeff_eq_esymm_roots_of_card hp_roots_card (k := 1) (by simp [hp])

/-- **Vieta's formula** for quadratics. -/
lemma eq_mul_mul_of_roots_quadratic_eq_pair [CommRing R] [IsDomain R] {x1 x2 : R} {p : R[X]}
    (hp : p.natDegree = 2) (hroots : p.roots = {x1, x2}) :
    p.coeff 0 = p.coeff 2 * x1 * x2 := by
  have hp_roots_card : p.roots.card = p.natDegree := by
    rw [hp, hroots, Multiset.card_pair]
  simpa [leadingCoeff, hp, hroots, mul_assoc, add_comm x1] using
    coeff_eq_esymm_roots_of_card hp_roots_card (k := 0) (by simp [hp])


/-- **Vieta's formula** for quadratics (`aroots` version). -/
lemma eq_neg_mul_add_of_aroots_quadratic_eq_pair
    [CommRing T] [CommRing S] [IsDomain S] [Algebra T S] {x1 x2 : S} (p : T[X])
    (hp : p.natDegree = 2)
    (haroots : p.aroots S = {x1, x2}) :
    algebraMap T S (p.coeff 1) = -algebraMap T S (p.coeff 2) * (x1 + x2) := by
  rw [aroots_def] at haroots
  have hp_roots_card' : (map (algebraMap T S) p).roots.card = 2 := by
    rw [haroots, Multiset.card_pair]
  rw [← coeff_map, ← coeff_map]
  apply eq_neg_mul_add_of_roots_quadratic_eq_pair _ haroots
  rw [le_antisymm_iff]
  constructor
  · rw [← hp]
    exact natDegree_map_le
  · rw [← hp_roots_card']
    exact card_roots' (map (algebraMap T S) p)


/-- **Vieta's formula** for quadratics (`aroots` version). -/
lemma eq_mul_mul_of_aroots_quadratic_eq_pair [CommRing T] [CommRing S] [IsDomain S] [Algebra T S]
    {a b c : T} {x1 x2 : S} (haroots : (C a * X ^ 2 + C b * X + C c).aroots S = {x1, x2}) :
    algebraMap T S c = algebraMap T S a * x1 * x2 := by
  rw [aroots_def, show map (algebraMap T S) (C a * X ^ 2 + C b * X + C c) = C ((algebraMap T S) a) *
    X ^ 2 + C ((algebraMap T S) b) * X + C ((algebraMap T S) c) by simp] at haroots
  exact eq_mul_mul_of_roots_quadratic_eq_pair haroots


/-- **Vieta's formula** for quadratics as an iff. -/
lemma roots_quadratic_eq_pair_iff_of_ne_zero [CommRing R] [IsDomain R] {x1 x2 : R} {p : R[X]}
    (hp : p.natDegree = 2) (ha : p.coeff 2 ≠ 0) :
    p.roots = {x1, x2} ↔
      p.coeff 1 = -(p.coeff 2) * (x1 + x2) ∧ (p.coeff 0) = (p.coeff 2) * x1 * x2 :=
  let a := p.coeff 2
  let b := p.coeff 1
  let c := p.coeff 0
  have roots_of_ne_zero_of_vieta (hvieta : b = -a * (x1 + x2) ∧ c = a * x1 * x2) :
      p.roots = {x1, x2} := by
    suffices p = C a * (X - C x1) * (X - C x2) by
      have h1 : C a * (X - C x1) ≠ 0 := mul_ne_zero (by simpa) (Polynomial.X_sub_C_ne_zero _)
      have h2 : C a * (X - C x1) * (X - C x2) ≠ 0 := mul_ne_zero h1 (Polynomial.X_sub_C_ne_zero _)
      simp [this, Polynomial.roots_mul h2, Polynomial.roots_mul h1]
    have ep : p = C a * X ^ 2 + C b * X + C c := by
      sorry
    simpa [ep, hvieta.1, hvieta.2] using by ring
  ⟨fun h => ⟨eq_neg_mul_add_of_roots_quadratic_eq_pair hp h,
    eq_mul_mul_of_roots_quadratic_eq_pair hp h⟩,
    roots_of_ne_zero_of_vieta⟩

/-- **Vieta's formula** for quadratics as an iff (`aroots` version). -/
lemma aroots_quadratic_eq_pair_iff_of_ne_zero [CommRing T] [CommRing S] [IsDomain S]
    [Algebra T S] {a b c : T} {x1 x2 : S} (ha : algebraMap T S a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).aroots S = {x1, x2} ↔
      algebraMap T S b = -algebraMap T S a * (x1 + x2) ∧
      algebraMap T S c = algebraMap T S a * x1 * x2 := by
  rw [aroots_def, show map (algebraMap T S) (C a * X ^ 2 + C b * X + C c) = C ((algebraMap T S) a) *
    X ^ 2 + C ((algebraMap T S) b) * X + C ((algebraMap T S) c) by simp]
  exact roots_quadratic_eq_pair_iff_of_ne_zero ha

/-- **Vieta's formula** for quadratics as an iff (`Field` version). -/
lemma roots_quadratic_eq_pair_iff_of_ne_zero' [Field R] {a b c x1 x2 : R} (ha : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).roots = {x1, x2} ↔
      x1 + x2 = -b / a ∧ x1 * x2 = c / a := by
  rw [roots_quadratic_eq_pair_iff_of_ne_zero ha]
  field_simp
  exact and_congr ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
    ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩

/-- **Vieta's formula** for quadratics as an iff (`aroots, Field` version). -/
lemma aroots_quadratic_eq_pair_iff_of_ne_zero' [CommRing T] [Field S] [Algebra T S] {a b c : T}
    {x1 x2 : S} (ha : algebraMap T S a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).aroots S = {x1, x2} ↔
      x1 + x2 = -algebraMap T S b / algebraMap T S a ∧
      x1 * x2 = algebraMap T S c / algebraMap T S a := by
  rw [aroots_def, show map (algebraMap T S) (C a * X ^ 2 + C b * X + C c) = C ((algebraMap T S) a) *
    X ^ 2 + C ((algebraMap T S) b) * X + C ((algebraMap T S) c) by simp]
  exact roots_quadratic_eq_pair_iff_of_ne_zero' ha

end Polynomial
