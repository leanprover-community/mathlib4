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

/-
Polynomial versions of results in `Algebra.QuadraticDiscriminant`
-/
section QuadraticDiscriminant

variable [Field R]

variable {a b c : R}

/-- Roots of a quadratic equation. -/
theorem quadratic_eq_zero_iff [NeZero (2 : R)] (ha : a ≠ 0) {s : R}
    (h : discrim a b c = s * s) (x : R) :
    IsRoot (a • X ^ 2 + b • X + C c) x ↔ x = (-b + s) / (2 * a) ∨ x = (-b - s) / (2 * a) := by
  simp only [IsRoot.def, eval_add, eval_smul, eval_pow, eval_X, smul_eq_mul, eval_C]
  rw [sq, _root_.quadratic_eq_zero_iff ha h]

/-- Root of a quadratic when its discriminant equals zero -/
theorem quadratic_eq_zero_iff_of_discrim_eq_zero [NeZero (2 : R)] (ha : a ≠ 0)
    (h : discrim a b c = 0) (x : R) : IsRoot (a • X ^ 2 + b • X + C c) x ↔ x = -b / (2 * a) := by
  simp only [IsRoot.def, eval_add, eval_smul, eval_pow, eval_X, smul_eq_mul, eval_C]
  rw [sq, _root_.quadratic_eq_zero_iff_of_discrim_eq_zero ha h]

/-- A quadratic has no root if its discriminant has no square root. -/
theorem quadratic_ne_zero_of_discrim_ne_sq (h : ∀ s : R, discrim a b c ≠ s^2) (x : R) :
    ¬ IsRoot (a • X ^ 2 + b • X + C c) x := by
  simp only [IsRoot.def, eval_add, eval_smul, eval_pow, eval_X, smul_eq_mul, eval_C]
  rw [← ne_eq, sq]
  exact _root_.quadratic_ne_zero_of_discrim_ne_sq h _

lemma quadratic_ne_zero (ha : a ≠ 0) : (a • X ^ 2 + b • X + C c) ≠ 0 := by
  have hc : (a • X ^ 2 + b • X + C c).coeff 2 = a := by
    simp [coeff_add, coeff_C_mul, coeff_smul, coeff_X_of_ne_one (Nat.add_one_add_one_ne_one),
      coeff_C_ne_zero (n:=2) ((Nat.zero_ne_add_one 1).symm)]
  rw [← hc] at ha
  by_contra hx
  exact ha (congrFun (congrArg coeff hx) 2)

theorem quadratic_roots_of_discrim_ne_sq (ha : a ≠ 0) (h : ∀ s : R, discrim a b c ≠ s^2) :
    (a • X ^ 2 + b • X + C c).roots = ∅ := Multiset.eq_zero_of_forall_notMem (fun r => by
  by_contra hc
  exact (quadratic_ne_zero_of_discrim_ne_sq h _) ((mem_roots (quadratic_ne_zero ha)).mp hc))

theorem quadratic_roots_iff_of_discrim_eq_sq [NeZero (2 : R)] (ha : a ≠ 0)
    {z s : R} (h : discrim a b c = s * s) :
    z ∈ (a • X ^ 2 + b • X + C c).roots ↔ z = (-b + s) / (2 * a) ∨ z = (-b - s) / (2 * a) := by
  rw [mem_roots (quadratic_ne_zero ha), quadratic_eq_zero_iff ha h]

#check Polynomial

theorem quadratic_roots_of_discrim_eq_sq [DecidableEq R] [NeZero (2 : R)] (ha : a ≠ 0) {s : R}
    (h : discrim a b c = s * s) :
    (a • X ^ 2 + b • X + C c).roots = {(-b + s) / (2 * a), (-b - s) / (2 * a)} := by
  have e1 : a • X ^ 2 + b • X + C c =
      a • (X - C ((-b + s) / (2 * a))) * (X - C ((-b - s) / (2 * a))) := by
    simp only [Algebra.smul_mul_assoc]
    ring_nf
    rw [C_add]
    rw [C_sub]
    ring_nf
    rw [← C_pow]
    ring_nf
    rw [smul_add]
    rw [smul_add]
    rw [add_comm _ (a • X ^ 2)]
    rw [add_assoc]
    rw [add_assoc]
    rw [add_right_inj]
    rw [map_neg, mul_neg, neg_mul, neg_neg]
    rw [C_mul]
    rw [← C_pow]
    rw [← C_sub]
    rw [smul_C]
    ring_nf
    rw [smul_sub]
    rw [← smul_mul_assoc]

    --rw [smul_assoc]
    rw [← Algebra.smul_mul_assoc]
    rw [← smul_mul_assoc]
    rw [mul_assoc]
    rw [mul_comm _ 2]
    rw [← C_2]
    rw [← C_mul]
    rw [mul_inv_cancel₀ two_ne_zero]
    rw [C_1]
    rw [mul_one]
    rw [sq s]
    rw [← h]
    rw [discrim]
    ring_nf
    rw [smul_sub]
    rw [smul_eq_mul a]
    rw [mul_assoc a]
    rw [mul_inv_cancel₀ ha]

    rw [C_1]
    have e2 : 2 * C (2 : R)⁻¹ = C (2 * 2⁻¹) := by
      rw [map_mul]
      rw [mul_left_inj']
      rfl
      have gg (a b c : R) (h : a ≠ 0) : b*a = c*a ↔ b = c := by exact mul_left_inj' h
      rw [mul_cancel_right]
      simp only [ne_eq, map_mul, mul_eq_mul_right_iff, map_eq_zero, inv_eq_zero]
      apply Or.inl
      rfl
    rw [e2]
   -- rw [monomial_mul_C]
    --rw [← smul_eq_mul]
    simp?
    rw [← smul_eq_mul 2]
    --rw [smul_C]



    rw [smul_algebraMap]
    simp only [map_neg, map_mul, mul_neg, neg_mul, neg_neg]

    rw [← h, discrim]
    ring_nf
    have p2 : (2 : K) ^ 2 = (4 : K) := by norm_num
    rw [add_comm _ (a * x ^ 2), mul_assoc, inv_mul_cancel₀ two_ne_zero, mul_one, mul_comm _ a⁻¹,
      ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ ha, one_mul, ← p2, mul_assoc, ← mul_pow,
      inv_mul_cancel₀ two_ne_zero, one_pow, mul_one, mul_comm _ c, mul_assoc, ← mul_pow,
      mul_inv_cancel₀ ha, one_pow, mul_one]




    --simp only [Algebra.smul_mul_assoc]
    ring_nf
    convert e0
    sorry
  rw [e1, Polynomial.roots_mul (by rw [← e1]; exact quadratic_ne_zero ha)]
  simp_all only [ne_eq, Algebra.smul_mul_assoc, not_false_eq_true, roots_smul_nonzero,
    roots_X_sub_C, Multiset.singleton_add, Multiset.insert_eq_cons]



end QuadraticDiscriminant

end Polynomial
