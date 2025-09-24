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
  have e1 : (map (algebraMap T S) p).natDegree = 2 := le_antisymm
    (by simpa [← hp] using natDegree_map_le)
    (by simpa [← aroots_def, haroots, ← Multiset.card_pair]
      using (map (algebraMap T S) p).card_roots')
  rw [← coeff_map, ← coeff_map]
  exact eq_neg_mul_add_of_roots_quadratic_eq_pair e1 haroots

/-- **Vieta's formula** for quadratics (`aroots` version). -/
lemma eq_mul_mul_of_aroots_quadratic_eq_pair [CommRing T] [CommRing S] [IsDomain S] [Algebra T S]
    {p : T[X]} {x1 x2 : S} (hp : p.natDegree = 2) (haroots : p.aroots S = {x1, x2}) :
    algebraMap T S (p.coeff 0) = algebraMap T S (p.coeff 2) * x1 * x2 := by
  have e1 : (map (algebraMap T S) p).natDegree = 2 := le_antisymm
    (by simpa [← hp] using natDegree_map_le)
    (by simpa [← aroots_def, haroots, ← Multiset.card_pair]
      using (map (algebraMap T S) p).card_roots')
  rw [← coeff_map, ← coeff_map]
  exact eq_mul_mul_of_roots_quadratic_eq_pair e1 haroots

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
      have h0 : (p.coeff 2) ≠ 0 := coeff_ne_zero_of_eq_natDegree Nat.zero_lt_two hp
      have h1 : C a * (X - C x1) ≠ 0 := mul_ne_zero (by simpa) (Polynomial.X_sub_C_ne_zero _)
      have h2 : C a * (X - C x1) * (X - C x2) ≠ 0 := mul_ne_zero h1 (Polynomial.X_sub_C_ne_zero _)
      simp [this, Polynomial.roots_mul h2, Polynomial.roots_mul h1]
    have ep : p = C a * X ^ 2 + C b * X + C c := eq_quadratic_of_natDegree_le_two (Nat.le_of_eq hp)
    simpa [ep, hvieta.1, hvieta.2] using by ring_nf
  ⟨fun h => ⟨eq_neg_mul_add_of_roots_quadratic_eq_pair hp h,
    eq_mul_mul_of_roots_quadratic_eq_pair hp h⟩,
    roots_of_ne_zero_of_vieta⟩

/-- **Vieta's formula** for quadratics as an iff (`aroots` version). -/
lemma aroots_quadratic_eq_pair_iff_of_ne_zero [CommRing T] [CommRing S] [IsDomain S]
    [Algebra T S] {p : T[X]} {x1 x2 : S} (ha : (map (algebraMap T S) p).natDegree = 2) :
    p.aroots S = {x1, x2} ↔
      algebraMap T S (p.coeff 1) = -algebraMap T S (p.coeff 2) * (x1 + x2) ∧
      algebraMap T S (p.coeff 0) = algebraMap T S (p.coeff 2) * x1 * x2 := by
  rw [roots_quadratic_eq_pair_iff_of_ne_zero ha, coeff_map, coeff_map, coeff_map]

/-- **Vieta's formula** for quadratics as an iff (`Field` version). -/
lemma roots_quadratic_eq_pair_iff_of_ne_zero' [Field R] {p : R[X]} {x1 x2 : R}
    (hp : p.natDegree = 2) : p.roots = {x1, x2} ↔
      x1 + x2 = -(p.coeff 1) / (p.coeff 2) ∧ x1 * x2 = (p.coeff 0) / (p.coeff 2) := by
  rw [roots_quadratic_eq_pair_iff_of_ne_zero hp]
  have h0 : (p.coeff 2) ≠ 0 := coeff_ne_zero_of_eq_natDegree Nat.zero_lt_two hp
  field_simp
  exact and_congr ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
    ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩

/-- **Vieta's formula** for quadratics as an iff (`aroots, Field` version). -/
lemma aroots_quadratic_eq_pair_iff_of_ne_zero' [CommRing T] [Field S] [Algebra T S] {p : T[X]}
    {x1 x2 : S} (ha : (map (algebraMap T S) p).natDegree = 2) :
    p.aroots S = {x1, x2} ↔
      x1 + x2 = -algebraMap T S (p.coeff 1) / algebraMap T S (p.coeff 2) ∧
      x1 * x2 = algebraMap T S (p.coeff 0) / algebraMap T S (p.coeff 2) := by
  rw [aroots_def, roots_quadratic_eq_pair_iff_of_ne_zero' ha, coeff_map, coeff_map, coeff_map]

end Polynomial
