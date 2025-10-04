/-
Copyright (c) 2025 Qinchuan Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qinchuan Zhang
-/
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Vieta's Formula for polynomial of small degrees.
-/

namespace Polynomial

variable {R T S : Type*}

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

lemma quadratic_eq_of_vieta [CommRing R] {a b c x1 x2 : R}
    (hsum : b = -a * (x1 + x2)) (hprod : c = a * x1 * x2) :
    C a * X ^ 2 + C b * X + C c = C a * (X - C x1) * (X - C x2) := by
  simpa [hsum, hprod] using by ring

lemma roots_of_ne_zero_of_vieta [CommRing R] [IsDomain R] {a b c x1 x2 : R} (ha : a ≠ 0)
    (hsum : b = -a * (x1 + x2)) (hprod : c = a * x1 * x2) :
    (C a * X ^ 2 + C b * X + C c).roots = {x1, x2} := by
  have e1 : C a * (X - C x1) * (X - C x2) ≠ 0 := by
    rw [← quadratic_eq_of_vieta hsum hprod]
    exact not_zero_iff.mpr ⟨2, by simp [ha]⟩
  simp [quadratic_eq_of_vieta hsum hprod, Polynomial.roots_mul e1, roots_C_mul _ ha]

/-- **Vieta's formula** for quadratics as an iff. -/
lemma roots_quadratic_eq_pair_iff_of_ne_zero [CommRing R] [IsDomain R] {a b c x1 x2 : R}
    (ha : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).roots = {x1, x2} ↔
      b = -a * (x1 + x2) ∧ c = a * x1 * x2 :=
  ⟨fun h => ⟨eq_neg_mul_add_of_roots_quadratic_eq_pair h, eq_mul_mul_of_roots_quadratic_eq_pair h⟩,
    fun h => roots_of_ne_zero_of_vieta ha h.1 h.2⟩

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

/-
Polynomial versions of results in `Algebra.QuadraticDiscriminant`
-/
section QuadraticDiscriminant

variable [Field R] {a b c : R}

/-- Roots of a quadratic equation. -/
theorem isRoot_quadratic_iff [NeZero (2 : R)] (ha : a ≠ 0) {s : R}
    (h : discrim a b c = s ^ 2) (x : R) :
    IsRoot (C a * X ^ 2 + C b * X + C c) x ↔ x = (-b + s) / (2 * a) ∨ x = (-b - s) / (2 * a) := by
  rw [sq] at h
  rw [← quadratic_eq_zero_iff ha h]; simp [sq]

/-- Root of a quadratic when its discriminant equals zero -/
theorem isRoot_quadratic_iff_of_discrim_eq_zero [NeZero (2 : R)] (ha : a ≠ 0)
    (h : discrim a b c = 0) (x : R) :
    IsRoot (C a * X ^ 2 + C b * X + C c) x ↔ x = -b / (2 * a) := by
  rw [← quadratic_eq_zero_iff_of_discrim_eq_zero ha h]; simp [sq]

/-- A quadratic has no root if its discriminant has no square root. -/
lemma not_isRoot_of_discrim_ne_sq (h : ∀ s : R, discrim a b c ≠ s^2) (x : R) :
    ¬ IsRoot (C a * X ^ 2 + C b * X + C c) x := by
  convert quadratic_ne_zero_of_discrim_ne_sq h x using 1; simp [sq]

/-- Quantifier elimination for a quadratic equation in characteristic `≠ 2`. -/
lemma exists_isRoot_quadratic_iff [NeZero (2 : R)] (ha : a ≠ 0) :
    (∃ x, IsRoot (C a * X ^ 2 + C b * X + C c) x) ↔ ∃ s, discrim a b c = s ^ 2 := ⟨
  fun ⟨x, hx⟩ => by by_contra hc; exact (not_isRoot_of_discrim_ne_sq (not_exists.mp hc) x) hx,
  fun ⟨s, hs⟩ => ⟨(-b + s) / (2 * a), (isRoot_quadratic_iff ha hs _).mpr (Or.inl rfl)⟩⟩

theorem mem_roots_quadratic_iff_of_discrim_eq_sq [NeZero (2 : R)] (ha : a ≠ 0)
    {z s : R} (h : discrim a b c = s ^ 2) :
    z ∈ (C a * X ^ 2 + C b * X + C c).roots ↔ z = (-b + s) / (2 * a) ∨ z = (-b - s) / (2 * a) := by
  rw [mem_roots (not_zero_iff.mpr ⟨2, by simp [ha]⟩), isRoot_quadratic_iff ha h]

theorem vieta_of_discrim_eq_sq [NeZero (2 : R)] (ha : a ≠ 0) {s : R} (h : discrim a b c = s ^ 2) :
    b = -a * ((-b + s) / (2 * a) + (-b - s) / (2 * a)) ∧
      c = a * ((-b + s) / (2 * a)) * ((-b - s) / (2 * a)) := by
  ring_nf
  rw [← h, discrim]
  field_simp
  ring_nf
  exact ⟨trivial, trivial⟩

theorem quadratic_eq_of_discrim_eq_sq [NeZero (2 : R)] (ha : a ≠ 0) {s : R}
    (h : discrim a b c = s ^ 2) : C a * X ^ 2 + C b * X + C c =
      C a * (X - C ((-b + s) / (2 * a))) * (X - C ((-b - s) / (2 * a))) :=
  quadratic_eq_of_vieta (vieta_of_discrim_eq_sq ha h).1 (vieta_of_discrim_eq_sq ha h).2

theorem roots_quadratic_of_discrim_eq_sq [NeZero (2 : R)] (ha : a ≠ 0) {s : R}
    (h : discrim a b c = s ^ 2) :
    (C a * X ^ 2 + C b * X + C c).roots = {(-b + s) / (2 * a), (-b - s) / (2 * a)} :=
  roots_of_ne_zero_of_vieta ha (vieta_of_discrim_eq_sq ha h).1 (vieta_of_discrim_eq_sq ha h).2

end QuadraticDiscriminant

end Polynomial
