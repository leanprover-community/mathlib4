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

namespace Polynomial

variable {R T S : Type*}

lemma eq_quadratic_of_degree_le_two [Semiring R] {p : R[X]} (hp : p.degree ≤ 2) :
    p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
  rw [p.as_sum_range_C_mul_X_pow'
    (Nat.lt_of_le_of_lt (natDegree_le_iff_degree_le.mpr hp) (Nat.lt_add_one 2))]
  simp [Finset.sum_range_succ]
  abel

/-- **Vieta's formula** for quadratics. -/
lemma eq_neg_mul_add_of_roots_quadratic_eq_pair [CommRing R] [IsDomain R] {a b c x1 x2 : R}
    (hroots : (C a * X ^ 2 + C b * X + C c).roots = {x1, x2}) :
    b = -a * (x1 + x2) := by
  let p : R[X] := C a * X ^ 2 + C b * X + C c
  have hp_natDegree : p.natDegree = 2 := le_antisymm natDegree_quadratic_le
    (by convert p.card_roots'; rw [hroots, Multiset.card_pair])
  have hp_roots_card : p.roots.card = p.natDegree := by
    rw [hp_natDegree, hroots, Multiset.card_pair]
  simpa [leadingCoeff, hp_natDegree, p, hroots, mul_assoc, add_comm x1] using
    coeff_eq_esymm_roots_of_card hp_roots_card (k := 1) (by simp [hp_natDegree])

/-- **Vieta's formula** for quadratics. -/
lemma eq_mul_mul_of_roots_quadratic_eq_pair [CommRing R] [IsDomain R] {a b c x1 x2 : R}
    (hroots : (C a * X ^ 2 + C b * X + C c).roots = {x1, x2}) :
    c = a * x1 * x2 := by
  let p : R[X] := C a * X ^ 2 + C b * X + C c
  have hp_natDegree : p.natDegree = 2 := le_antisymm natDegree_quadratic_le
    (by convert p.card_roots'; rw [hroots, Multiset.card_pair])
  have hp_roots_card : p.roots.card = p.natDegree := by
    rw [hp_natDegree, hroots, Multiset.card_pair]
  simpa [leadingCoeff, hp_natDegree, p, hroots, mul_assoc, add_comm x1] using
    coeff_eq_esymm_roots_of_card hp_roots_card (k := 0) (by simp [hp_natDegree])

/-- **Vieta's formula** for quadratics (`aroots` version). -/
lemma eq_neg_mul_add_of_aroots_quadratic_eq_pair
    [CommRing T] [CommRing S] [IsDomain S] [Algebra T S] {a b c : T} {x1 x2 : S}
    (haroots : (C a * X ^ 2 + C b * X + C c).aroots S = {x1, x2}) :
    algebraMap T S b = -algebraMap T S a * (x1 + x2) := by
  rw [aroots_def, show map (algebraMap T S) (C a * X ^ 2 + C b * X + C c) = C ((algebraMap T S) a) *
    X ^ 2 + C ((algebraMap T S) b) * X + C ((algebraMap T S) c) by simp] at haroots
  exact eq_neg_mul_add_of_roots_quadratic_eq_pair haroots

/-- **Vieta's formula** for quadratics (`aroots` version). -/
lemma eq_mul_mul_of_aroots_quadratic_eq_pair [CommRing T] [CommRing S] [IsDomain S] [Algebra T S]
    {a b c : T} {x1 x2 : S} (haroots : (C a * X ^ 2 + C b * X + C c).aroots S = {x1, x2}) :
    algebraMap T S c = algebraMap T S a * x1 * x2 := by
  rw [aroots_def, show map (algebraMap T S) (C a * X ^ 2 + C b * X + C c) = C ((algebraMap T S) a) *
    X ^ 2 + C ((algebraMap T S) b) * X + C ((algebraMap T S) c) by simp] at haroots
  exact eq_mul_mul_of_roots_quadratic_eq_pair haroots

/-- **Vieta's formula** for quadratics as an iff. -/
lemma roots_quadratic_eq_pair_iff_of_ne_zero [CommRing R] [IsDomain R] {a b c x1 x2 : R}
    (ha : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).roots = {x1, x2} ↔
      b = -a * (x1 + x2) ∧ c = a * x1 * x2 :=
  have roots_of_ne_zero_of_vieta (hvieta : b = -a * (x1 + x2) ∧ c = a * x1 * x2) :
      (C a * X ^ 2 + C b * X + C c).roots = {x1, x2} := by
    suffices C a * X ^ 2 + C b * X + C c = C a * (X - C x1) * (X - C x2) by
      have h1 : C a * (X - C x1) ≠ 0 := mul_ne_zero (by simpa) (Polynomial.X_sub_C_ne_zero _)
      have h2 : C a * (X - C x1) * (X - C x2) ≠ 0 := mul_ne_zero h1 (Polynomial.X_sub_C_ne_zero _)
      simp [this, Polynomial.roots_mul h2, Polynomial.roots_mul h1]
    simpa [hvieta.1, hvieta.2] using by ring
  ⟨fun h => ⟨eq_neg_mul_add_of_roots_quadratic_eq_pair h, eq_mul_mul_of_roots_quadratic_eq_pair h⟩,
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
