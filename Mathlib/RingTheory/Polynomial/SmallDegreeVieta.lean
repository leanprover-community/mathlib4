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
    [CommRing T] [CommRing S] [IsDomain S] [Algebra T S] {p : T[X]} {x1 x2 : S}
    (hp : p.natDegree = 2) (haroots : p.aroots S = {x1, x2}) :
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
    {p : T[X]} {x1 x2 : S} (hp : p.natDegree = 2) (haroots : p.aroots S = {x1, x2}) :
    algebraMap T S (p.coeff 0) = algebraMap T S (p.coeff 2) * x1 * x2 := by
  rw [aroots_def] at haroots
  have hp_roots_card' : (map (algebraMap T S) p).roots.card = 2 := by
    rw [haroots, Multiset.card_pair]
  rw [← coeff_map, ← coeff_map]
  apply eq_mul_mul_of_roots_quadratic_eq_pair _ haroots
  rw [le_antisymm_iff]
  constructor
  · rw [← hp]
    exact natDegree_map_le
  · rw [← hp_roots_card']
    exact card_roots' (map (algebraMap T S) p)

lemma test [CommRing R] {p : R[X]} (hp : p.natDegree = 2) : (p.coeff 2) ≠ 0 := by
  apply coeff_ne_zero_of_eq_degree
  unfold natDegree at hp
  rw [WithBot.unbotD_eq_iff] at hp
  simp at hp
  rw [hp]
  norm_cast


/-- **Vieta's formula** for quadratics as an iff. -/
lemma roots_quadratic_eq_pair_iff_of_ne_zero [CommRing R] [IsDomain R] {x1 x2 : R} {p : R[X]}
    (hp : p.natDegree = 2) :
    p.roots = {x1, x2} ↔
      p.coeff 1 = -(p.coeff 2) * (x1 + x2) ∧ (p.coeff 0) = (p.coeff 2) * x1 * x2 :=
  let a := p.coeff 2
  let b := p.coeff 1
  let c := p.coeff 0
  have roots_of_ne_zero_of_vieta (hvieta : b = -a * (x1 + x2) ∧ c = a * x1 * x2) :
      p.roots = {x1, x2} := by
    suffices p = C a * (X - C x1) * (X - C x2) by
      have h0 : (p.coeff 2) ≠ 0 := test hp
      have h1 : C a * (X - C x1) ≠ 0 := mul_ne_zero (by simpa) (Polynomial.X_sub_C_ne_zero _)
      have h2 : C a * (X - C x1) * (X - C x2) ≠ 0 := mul_ne_zero h1 (Polynomial.X_sub_C_ne_zero _)
      simp [this, Polynomial.roots_mul h2, Polynomial.roots_mul h1]
    have ep : p = C a * X ^ 2 + C b * X + C c := by
      rw [C_mul_X_pow_eq_monomial]
      sorry
    simpa [ep, hvieta.1, hvieta.2] using by ring
  ⟨fun h => ⟨eq_neg_mul_add_of_roots_quadratic_eq_pair hp h,
    eq_mul_mul_of_roots_quadratic_eq_pair hp h⟩,
    roots_of_ne_zero_of_vieta⟩

/-- **Vieta's formula** for quadratics as an iff (`aroots` version). -/
lemma aroots_quadratic_eq_pair_iff_of_ne_zero [CommRing T] [CommRing S] [IsDomain S]
    [Algebra T S] {p : T[X]} {x1 x2 : S} (ha : (map (algebraMap T S) p).natDegree = 2) :
    p.aroots S = {x1, x2} ↔
      algebraMap T S (p.coeff 1) = -algebraMap T S (p.coeff 2) * (x1 + x2) ∧
      algebraMap T S (p.coeff 0) = algebraMap T S (p.coeff 2) * x1 * x2 := by
  let a := p.coeff 2
  let b := p.coeff 1
  let c := p.coeff 0
  rw [roots_quadratic_eq_pair_iff_of_ne_zero ha, coeff_map, coeff_map, coeff_map]

/-- **Vieta's formula** for quadratics as an iff (`Field` version). -/
lemma roots_quadratic_eq_pair_iff_of_ne_zero' [Field R] {p : R[X]} {x1 x2 : R}
    (hp : p.natDegree = 2) : p.roots = {x1, x2} ↔
      x1 + x2 = -(p.coeff 1) / (p.coeff 2) ∧ x1 * x2 = (p.coeff 0) / (p.coeff 2) := by
  rw [roots_quadratic_eq_pair_iff_of_ne_zero hp]
  field_simp
  have h0 : (p.coeff 2) ≠ 0 := test hp
  apply and_congr
  · constructor
    · intro h
      rw [h, neg_div, neg_neg, mul_div_cancel_left₀ _ h0]
    · intro h
      rw [h, mul_neg, neg_neg, (mul_div_cancel₀ _ h0)]
  · constructor
    · intro h
      rw [h, mul_assoc, mul_div_cancel_left₀ _ h0]
    · intro h
      rw [mul_assoc, h, mul_div_cancel₀ _ h0]

/-- **Vieta's formula** for quadratics as an iff (`aroots, Field` version). -/
lemma aroots_quadratic_eq_pair_iff_of_ne_zero' [CommRing T] [Field S] [Algebra T S] {p : T[X]}
    {x1 x2 : S} (ha : (map (algebraMap T S) p).natDegree = 2) :
    p.aroots S = {x1, x2} ↔
      x1 + x2 = -algebraMap T S (p.coeff 1) / algebraMap T S (p.coeff 2) ∧
      x1 * x2 = algebraMap T S (p.coeff 0) / algebraMap T S (p.coeff 2) := by
  rw [aroots_def]
  rw [roots_quadratic_eq_pair_iff_of_ne_zero' ha]
  apply and_congr
  · rw [coeff_map, coeff_map]
  · rw [coeff_map, coeff_map]

end Polynomial
