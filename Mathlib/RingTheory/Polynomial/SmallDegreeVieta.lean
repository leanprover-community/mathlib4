/-
Copyright (c) 2025 Qinchuan Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qinchuan Zhang
-/
module

public import Mathlib.RingTheory.Polynomial.Vieta

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Vieta's Formula for polynomial of small degrees.
-/

public section

namespace Polynomial

variable {R T S : Type*}

lemma eq_quadratic_of_degree_le_two [Semiring R] {p : R[X]} (hp : p.degree ≤ 2) :
    p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
  rw [p.as_sum_range_C_mul_X_pow'
    (Nat.lt_of_le_of_lt (natDegree_le_iff_degree_le.mpr hp) (Nat.lt_add_one 2))]
  simp [Finset.sum_range_succ]
  abel

private theorem vieta_aux [CommRing R] [IsDomain R] {x1 x2 : R} {p : R[X]}
    (hp : p.degree ≤ 2) (hroots : p.roots = {x1, x2}) :
    p.coeff 1 = -p.coeff 2 * (x1 + x2) ∧ p.coeff 0 = p.coeff 2 * x1 * x2 := by
  have hn : p ≠ 0 := p.ne_zero_of_roots_ne_zero (by simp [hroots])
  have c2 : 2 = p.roots.card := by rw [hroots, Multiset.card_pair]
  have hpr := (hp.trans_eq (congrArg Nat.cast c2)).antisymm (card_roots hn)
  have hp' : p.degree = 2 := by rw [hpr, ← c2, Nat.cast_ofNat]
  have H (k) (hk : k ≤ 2) :=
    coeff_eq_esymm_roots_of_card (natDegree_eq_of_degree_eq_some hpr).symm (k := k)
    (by simpa [natDegree_eq_of_degree_eq_some hp'])
  simpa [leadingCoeff, natDegree_eq_of_degree_eq_some hp', hroots, mul_assoc, add_comm x1] using
    And.intro (H 1 (by norm_num)) (H 0 (by norm_num))

/-- **Vieta's formula** for quadratics, linear coefficient. -/
lemma eq_neg_mul_add_of_degree_two_of_roots_eq_pair [CommRing R] [IsDomain R] {x1 x2 : R} {p : R[X]}
    (hp : p.degree ≤ 2) (hroots : p.roots = {x1, x2}) : p.coeff 1 = -p.coeff 2 * (x1 + x2) :=
  (vieta_aux hp hroots).1

@[deprecated eq_neg_mul_add_of_degree_two_of_roots_eq_pair (since := "2026-01-10")]
lemma eq_neg_mul_add_of_roots_quadratic_eq_pair [CommRing R] [IsDomain R] {a b c x1 x2 : R}
    (hroots : (C a * X ^ 2 + C b * X + C c).roots = {x1, x2}) :
    b = -a * (x1 + x2) := by
  convert eq_neg_mul_add_of_degree_two_of_roots_eq_pair degree_quadratic_le hroots <;> simp

/-- **Vieta's formula** for quadratics, constant coefficient. -/
lemma eq_mul_mul_of_roots_degree_two_eq_pair [CommRing R] [IsDomain R] {x1 x2 : R} {p : R[X]}
    (hp : p.degree ≤ 2) (hroots : p.roots = {x1, x2}) : p.coeff 0 = p.coeff 2 * x1 * x2 :=
  (vieta_aux hp hroots).2

@[deprecated eq_mul_mul_of_roots_degree_two_eq_pair (since := "2026-01-10")]
lemma eq_mul_mul_of_roots_quadratic_eq_pair [CommRing R] [IsDomain R] {a b c x1 x2 : R}
    (hroots : (C a * X ^ 2 + C b * X + C c).roots = {x1, x2}) :
    c = a * x1 * x2 := by
  convert eq_mul_mul_of_roots_degree_two_eq_pair degree_quadratic_le hroots <;> simp

/-- **Vieta's formula** for quadratics (`aroots` version), linear coefficient. -/
lemma eq_neg_mul_add_of_aroots_degree_two_eq_pair
    [CommRing T] [CommRing S] [IsDomain S] [Algebra T S] {p : T[X]} {x1 x2 : S}
    (hp : p.degree ≤ 2) (haroots : p.aroots S = {x1, x2}) :
    algebraMap T S (p.coeff 1) = -algebraMap T S (p.coeff 2) * (x1 + x2) := by
  simp_rw [← coeff_map]
  exact eq_neg_mul_add_of_degree_two_of_roots_eq_pair (degree_map_le.trans hp) haroots

@[deprecated eq_neg_mul_add_of_aroots_degree_two_eq_pair (since := "2026-01-10")]
lemma eq_neg_mul_add_of_aroots_quadratic_eq_pair
    [CommRing T] [CommRing S] [IsDomain S] [Algebra T S] {a b c : T} {x1 x2 : S}
    (haroots : (C a * X ^ 2 + C b * X + C c).aroots S = {x1, x2}) :
    algebraMap T S b = -algebraMap T S a * (x1 + x2) := by
  convert eq_neg_mul_add_of_aroots_degree_two_eq_pair degree_quadratic_le haroots <;> simp

/-- **Vieta's formula** for quadratics (`aroots` version), constant coefficient. -/
lemma eq_mul_mul_of_aroots_degree_two_eq_pair [CommRing T] [CommRing S] [IsDomain S] [Algebra T S]
    {p : T[X]} {x1 x2 : S} (hp : p.degree ≤ 2) (haroots : p.aroots S = {x1, x2}) :
    algebraMap T S (p.coeff 0) = algebraMap T S (p.coeff 2) * x1 * x2 := by
  simp_rw [← coeff_map]
  exact eq_mul_mul_of_roots_degree_two_eq_pair (degree_map_le.trans hp) haroots

@[deprecated eq_mul_mul_of_aroots_degree_two_eq_pair (since := "2026-01-10")]
lemma eq_mul_mul_of_aroots_quadratic_eq_pair [CommRing T] [CommRing S] [IsDomain S] [Algebra T S]
    {a b c : T} {x1 x2 : S} (haroots : (C a * X ^ 2 + C b * X + C c).aroots S = {x1, x2}) :
    algebraMap T S c = algebraMap T S a * x1 * x2 := by
  convert eq_mul_mul_of_aroots_degree_two_eq_pair degree_quadratic_le haroots <;> simp

/-- **Vieta's formula** for quadratics as an iff. -/
lemma roots_degree_two_eq_pair_iff_of_ne_zero [CommRing R] [IsDomain R] {x1 x2 : R} {p : R[X]}
    (hp : p.degree = 2) :
    p.roots = {x1, x2} ↔ p.coeff 1 = -p.coeff 2 * (x1 + x2) ∧ p.coeff 0 = p.coeff 2 * x1 * x2 := by
  refine ⟨vieta_aux hp.le, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  suffices p = (X - C x1) * (X - C x2) * C (p.coeff 2) by
    have h : (X - C x1) * (X - C x2) ≠ 0 := by simp [sub_eq_zero]
    rw [this, roots_mul (mul_ne_zero h _), roots_mul h]
    · simp
    · simpa using coeff_ne_zero_of_eq_degree hp
  rw [eq_quadratic_of_degree_le_two hp.le]
  simpa [h₁, h₂] using by ring

@[deprecated roots_degree_two_eq_pair_iff_of_ne_zero (since := "2026-01-10")]
lemma roots_quadratic_eq_pair_iff_of_ne_zero [CommRing R] [IsDomain R] {a b c x1 x2 : R}
    (ha : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).roots = {x1, x2} ↔
      b = -a * (x1 + x2) ∧ c = a * x1 * x2 := by
  convert roots_degree_two_eq_pair_iff_of_ne_zero (degree_quadratic ha) <;> simp

/-- **Vieta's formula** for quadratics as an iff (`aroots` version). -/
lemma aroots_degree_two_eq_pair_iff_of_ne_zero [CommRing T] [CommRing S] [IsDomain S]
    [Algebra T S] {p : T[X]} {x1 x2 : S} (ha : (map (algebraMap T S) p).degree = 2) :
    p.aroots S = {x1, x2} ↔
      algebraMap T S (p.coeff 1) = -algebraMap T S (p.coeff 2) * (x1 + x2) ∧
      algebraMap T S (p.coeff 0) = algebraMap T S (p.coeff 2) * x1 * x2 := by
  rw [roots_degree_two_eq_pair_iff_of_ne_zero ha, coeff_map, coeff_map, coeff_map]

@[deprecated aroots_degree_two_eq_pair_iff_of_ne_zero (since := "2026-01-10")]
lemma aroots_quadratic_eq_pair_iff_of_ne_zero [CommRing T] [CommRing S] [IsDomain S]
    [Algebra T S] {a b c : T} {x1 x2 : S} (ha : algebraMap T S a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).aroots S = {x1, x2} ↔
      algebraMap T S b = -algebraMap T S a * (x1 + x2) ∧
      algebraMap T S c = algebraMap T S a * x1 * x2 := by
  convert aroots_degree_two_eq_pair_iff_of_ne_zero _
  · simp
  · simp
  · simp
  · simp
  · simpa using degree_quadratic ha

/-- **Vieta's formula** for quadratics as an iff (`Field` version). -/
lemma roots_degree_two_eq_pair_iff_of_ne_zero' [Field R] {p : R[X]} {x1 x2 : R}
    (hp : p.degree = 2) : p.roots = {x1, x2} ↔
      x1 + x2 = -p.coeff 1 / p.coeff 2 ∧ x1 * x2 = p.coeff 0 / p.coeff 2 := by
  have hp' := coeff_ne_zero_of_eq_degree hp
  rw [roots_degree_two_eq_pair_iff_of_ne_zero hp]
  apply and_congr
  · rw [eq_div_iff hp', eq_comm, ← neg_eq_iff_eq_neg]
    ring_nf
  · rw [eq_div_iff hp', eq_comm]
    ring_nf

@[deprecated roots_degree_two_eq_pair_iff_of_ne_zero' (since := "2026-01-10")]
lemma roots_quadratic_eq_pair_iff_of_ne_zero' [Field R] {a b c x1 x2 : R} (ha : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).roots = {x1, x2} ↔
      x1 + x2 = -b / a ∧ x1 * x2 = c / a := by
  convert roots_degree_two_eq_pair_iff_of_ne_zero' (degree_quadratic ha) <;> simp

/-- **Vieta's formula** for quadratics as an iff (`aroots, Field` version). -/
lemma aroots_degree_two_eq_pair_iff_of_ne_zero' [CommRing T] [Field S] [Algebra T S] {p : T[X]}
    {x1 x2 : S} (ha : (map (algebraMap T S) p).degree = 2) :
    p.aroots S = {x1, x2} ↔
      x1 + x2 = -algebraMap T S (p.coeff 1) / algebraMap T S (p.coeff 2) ∧
      x1 * x2 = algebraMap T S (p.coeff 0) / algebraMap T S (p.coeff 2) := by
  rw [aroots_def, roots_degree_two_eq_pair_iff_of_ne_zero' ha, coeff_map, coeff_map, coeff_map]

@[deprecated aroots_degree_two_eq_pair_iff_of_ne_zero' (since := "2026-01-10")]
lemma aroots_quadratic_eq_pair_iff_of_ne_zero' [CommRing T] [Field S] [Algebra T S] {a b c : T}
    {x1 x2 : S} (ha : algebraMap T S a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).aroots S = {x1, x2} ↔
      x1 + x2 = -algebraMap T S b / algebraMap T S a ∧
      x1 * x2 = algebraMap T S c / algebraMap T S a := by
  convert aroots_degree_two_eq_pair_iff_of_ne_zero' _
  · simp
  · simp
  · simp
  · simp
  · simpa using degree_quadratic ha

end Polynomial
