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

/-- **Vieta's formula** for quadratic in term of `Polynomial.roots`.
This is a consequence of `Polynomial.coeff_eq_esymm_roots_of_card`. -/
lemma quadratic_vieta [CommRing R] [IsDomain R] {a b c x1 x2 : R}
    (hroots : (C a * X ^ 2 + C b * X + C c).roots = {x1, x2}) :
    b = -a * (x1 + x2) ∧ c = a * x1 * x2 := by
  let p : R[X] := C a * X ^ 2 + C b * X + C c
  have hp_natDegree : p.natDegree = 2 := le_antisymm natDegree_quadratic_le
    (by convert p.card_roots'; rw [hroots, Multiset.card_pair])
  have hp_roots_card : p.roots.card = p.natDegree := by
    rw [hp_natDegree, hroots, Multiset.card_pair]
  simpa [leadingCoeff, hp_natDegree, p, hroots, mul_assoc, add_comm x1] using
    And.intro (coeff_eq_esymm_roots_of_card hp_roots_card (k := 1) (by norm_num [hp_natDegree]))
      (coeff_eq_esymm_roots_of_card hp_roots_card (k := 0) (by norm_num [hp_natDegree]))

/-- **Vieta's formula** for quadratic, `aroots` version. -/
lemma quadratic_vieta_aroots [CommRing T] [CommRing S] [IsDomain S] [Algebra T S]
    {a b c : T} {x1 x2 : S} (haroots : (C a * X ^ 2 + C b * X + C c).aroots S = {x1, x2}) :
    algebraMap T S b = -algebraMap T S a * (x1 + x2) ∧
    algebraMap T S c = algebraMap T S a * x1 * x2 := by
  rw [aroots_def, show map (algebraMap T S) (C a * X ^ 2 + C b * X + C c) = C ((algebraMap T S) a) *
    X ^ 2 + C ((algebraMap T S) b) * X + C ((algebraMap T S) c) by simp] at haroots
  exact quadratic_vieta haroots

private lemma roots_of_ne_zero_of_vieta [CommRing R] [IsDomain R] {a b c x1 x2 : R}
    (ha : a ≠ 0) (hvieta : b = -a * (x1 + x2) ∧ c = a * x1 * x2) :
    (C a * X ^ 2 + C b * X + C c).roots = {x1, x2} := by
  suffices C a * X ^ 2 + C b * X + C c = C a * (X - C x1) * (X - C x2) by
    have h1 : C a * (X - C x1) ≠ 0 := mul_ne_zero (by simpa) (Polynomial.X_sub_C_ne_zero _)
    have h2 : C a * (X - C x1) * (X - C x2) ≠ 0 := mul_ne_zero h1 (Polynomial.X_sub_C_ne_zero _)
    simp [this, Polynomial.roots_mul h2, Polynomial.roots_mul h1]
  simpa [hvieta.1, hvieta.2] using by ring

/-- **Vieta's formula** for quadratic in term of `Polynomial.roots`. -/
lemma quadratic_vieta_iff_of_ne_zero [CommRing R] [IsDomain R] {a b c x1 x2 : R}
    (ha : a ≠ 0) : (C a * X ^ 2 + C b * X + C c).roots = {x1, x2} ↔
      b = -a * (x1 + x2) ∧ c = a * x1 * x2 :=
  ⟨quadratic_vieta, roots_of_ne_zero_of_vieta ha⟩

lemma quadratic_vieta_aroots_iff_of_ne_zero [CommRing T] [CommRing S] [IsDomain S]
    [Algebra T S] {a b c : T} {x1 x2 : S} (ha : algebraMap T S a ≠ 0) :
      (C a * X ^ 2 + C b * X + C c).aroots S = {x1, x2} ↔
        algebraMap T S b = -algebraMap T S a * (x1 + x2) ∧
        algebraMap T S c = algebraMap T S a * x1 * x2 := by
  refine ⟨quadratic_vieta_aroots, ?_⟩
  intro ⟨hb, hc⟩
  rw [aroots_def, show map (algebraMap T S) (C a * X ^ 2 + C b * X + C c) = C ((algebraMap T S) a) *
    X ^ 2 + C ((algebraMap T S) b) * X + C ((algebraMap T S) c) by simp]
  exact roots_of_ne_zero_of_vieta ha ⟨hb, hc⟩

/-- **Vieta's formula** for quadratic in term of `Polynomial.roots`. -/
lemma quadratic_vieta_iff_of_ne_zero' [Field R] {a b c x1 x2 : R} (ha : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).roots = {x1, x2} ↔
      x1 + x2 = -b / a ∧ x1 * x2 = c / a := by
  rw [quadratic_vieta_iff_of_ne_zero ha]
  field_simp
  exact and_congr ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
    ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩

end Polynomial
