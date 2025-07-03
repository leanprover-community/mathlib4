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

lemma quadratic_ne_zero [Semiring R] {a b c : R} (ha : a ≠ 0) : C a * X ^ 2 + C b * X + C c ≠ 0 :=
  fun hx ↦ ha (by rw [show a = (C a * X ^ 2 + C b * X + C c).coeff 2 by
    simp, hx, coeff_zero])

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
    coeff_eq_esymm_roots_of_card hp_roots_card (k := 1) (by norm_num [hp_natDegree])

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
    coeff_eq_esymm_roots_of_card hp_roots_card (k := 0) (by norm_num [hp_natDegree])

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
    (hvieta : b = -a * (x1 + x2) ∧ c = a * x1 * x2) :
    C a * X ^ 2 + C b * X + C c = C a * (X - C x1) * (X - C x2) := by
  simpa [hvieta.1, hvieta.2] using by ring

lemma roots_of_ne_zero_of_vieta [CommRing R] [IsDomain R] {a b c x1 x2 : R} (ha : a ≠ 0)
    (hvieta : b = -a * (x1 + x2) ∧ c = a * x1 * x2) :
    (C a * X ^ 2 + C b * X + C c).roots = {x1, x2} := by
  have e1 : C a * (X - C x1) * (X - C x2) ≠ 0 := by
    rw [← quadratic_eq_of_vieta hvieta]
    exact quadratic_ne_zero ha
  simp [quadratic_eq_of_vieta hvieta, Polynomial.roots_mul e1, roots_C_mul _ ha]

/-- **Vieta's formula** for quadratics as an iff. -/
lemma roots_quadratic_eq_pair_iff_of_ne_zero [CommRing R] [IsDomain R] {a b c x1 x2 : R}
    (ha : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).roots = {x1, x2} ↔
      b = -a * (x1 + x2) ∧ c = a * x1 * x2 :=
  ⟨fun h => ⟨eq_neg_mul_add_of_roots_quadratic_eq_pair h, eq_mul_mul_of_roots_quadratic_eq_pair h⟩,
    roots_of_ne_zero_of_vieta ha⟩

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
    (h : discrim a b c = s * s) (x : R) :
    IsRoot (C a * X ^ 2 + C b * X + C c) x ↔ x = (-b + s) / (2 * a) ∨ x = (-b - s) / (2 * a) := by
  rw [← quadratic_eq_zero_iff ha h]; simp [pow_two]

/-- Root of a quadratic when its discriminant equals zero -/
theorem isRoot_quadratic_iff_of_discrim_eq_zero [NeZero (2 : R)] (ha : a ≠ 0)
    (h : discrim a b c = 0) (x : R) :
    IsRoot (C a * X ^ 2 + C b * X + C c) x ↔ x = -b / (2 * a) := by
  rw [← quadratic_eq_zero_iff_of_discrim_eq_zero ha h]; simp [pow_two]

/-- A quadratic has no root if its discriminant has no square root. -/
theorem not_isRoot_of_discrim_ne_sq (h : ∀ s : R, discrim a b c ≠ s^2) (x : R) :
    ¬ IsRoot (C a * X ^ 2 + C b * X + C c) x := by
  convert quadratic_ne_zero_of_discrim_ne_sq h x using 1; simp [pow_two]

theorem mem_roots_quadratic_iff_of_discrim_eq_sq [NeZero (2 : R)] (ha : a ≠ 0)
    {z s : R} (h : discrim a b c = s * s) :
    z ∈ (C a * X ^ 2 + C b * X + C c).roots ↔ z = (-b + s) / (2 * a) ∨ z = (-b - s) / (2 * a) := by
  rw [mem_roots (quadratic_ne_zero ha), isRoot_quadratic_iff ha h]

theorem vieta_of_discrim_eq_sq [NeZero (2 : R)] (ha : a ≠ 0) {s : R} (h : discrim a b c = s * s) :
    b = -a * ((-b + s) / (2 * a) + (-b - s) / (2 * a)) ∧
      c = a * ((-b + s) / (2 * a)) * ((-b - s) / (2 * a)) := by
  ring_nf
  rw [sq s, ← h, discrim]
  field_simp
  ring_nf

theorem quadratic_eq_of_discrim_eq_sq [NeZero (2 : R)] (ha : a ≠ 0) {s : R}
    (h : discrim a b c = s * s) : C a * X ^ 2 + C b * X + C c =
      C a * (X - C ((-b + s) / (2 * a))) * (X - C ((-b - s) / (2 * a))) :=
  quadratic_eq_of_vieta (vieta_of_discrim_eq_sq ha h)

theorem roots_quadratic_of_discrim_ne_sq (h : ∀ s : R, discrim a b c ≠ s^2) :
    (C a * X ^ 2 + C b * X + C c).roots = ∅ :=
  Multiset.eq_zero_of_forall_notMem (fun r hc => not_isRoot_of_discrim_ne_sq h r
    (mem_roots'.mp hc).2)

theorem roots_quadratic_of_discrim_eq_sq [NeZero (2 : R)] (ha : a ≠ 0) {s : R}
    (h : discrim a b c = s * s) :
    (C a * X ^ 2 + C b * X + C c).roots = {(-b + s) / (2 * a), (-b - s) / (2 * a)} :=
  roots_of_ne_zero_of_vieta ha (vieta_of_discrim_eq_sq ha h)

end QuadraticDiscriminant

end Polynomial
