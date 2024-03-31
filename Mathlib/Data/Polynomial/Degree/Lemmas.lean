/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathlib.Data.Polynomial.Eval

#align_import data.polynomial.degree.lemmas from "leanprover-community/mathlib"@"728baa2f54e6062c5879a3e397ac6bac323e506f"

/-!
# Theory of degrees of polynomials

Some of the main results include
- `natDegree_comp_le` : The degree of the composition is at most the product of degrees

-/


noncomputable section

open Polynomial

open Finsupp Finset

namespace Polynomial

universe u v w

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

section Degree

theorem natDegree_comp_le : natDegree (p.comp q) ≤ natDegree p * natDegree q :=
  letI := Classical.decEq R
  if h0 : p.comp q = 0 then by rw [h0, natDegree_zero]; exact Nat.zero_le _
  else
    WithBot.coe_le_coe.1 <|
      calc
        ↑(natDegree (p.comp q)) = degree (p.comp q) := (degree_eq_natDegree h0).symm
        _ = _ := (congr_arg degree comp_eq_sum_left)
        _ ≤ _ := (degree_sum_le _ _)
        _ ≤ _ :=
          Finset.sup_le fun n hn =>
            calc
              degree (C (coeff p n) * q ^ n) ≤ degree (C (coeff p n)) + degree (q ^ n) :=
                degree_mul_le _ _
              _ ≤ natDegree (C (coeff p n)) + n • degree q :=
                (add_le_add degree_le_natDegree (degree_pow_le _ _))
              _ ≤ natDegree (C (coeff p n)) + n • ↑(natDegree q) :=
                (add_le_add_left (nsmul_le_nsmul_right (@degree_le_natDegree _ _ q) n) _)
              _ = (n * natDegree q : ℕ) := by
                rw [natDegree_C, Nat.cast_zero, zero_add, nsmul_eq_mul];
                  simp
              _ ≤ (natDegree p * natDegree q : ℕ) :=
                WithBot.coe_le_coe.2 <|
                  mul_le_mul_of_nonneg_right (le_natDegree_of_ne_zero (mem_support_iff.1 hn))
                    (Nat.zero_le _)
#align polynomial.nat_degree_comp_le Polynomial.natDegree_comp_le

theorem degree_pos_of_root {p : R[X]} (hp : p ≠ 0) (h : IsRoot p a) : 0 < degree p :=
  lt_of_not_ge fun hlt => by
    have := eq_C_of_degree_le_zero hlt
    rw [IsRoot, this, eval_C] at h
    simp only [h, RingHom.map_zero] at this
    exact hp this
#align polynomial.degree_pos_of_root Polynomial.degree_pos_of_root

theorem natDegree_le_iff_coeff_eq_zero : p.natDegree ≤ n ↔ ∀ N : ℕ, n < N → p.coeff N = 0 := by
  simp_rw [natDegree_le_iff_degree_le, degree_le_iff_coeff_zero, Nat.cast_lt]
#align polynomial.nat_degree_le_iff_coeff_eq_zero Polynomial.natDegree_le_iff_coeff_eq_zero

theorem natDegree_add_le_iff_left {n : ℕ} (p q : R[X]) (qn : q.natDegree ≤ n) :
    (p + q).natDegree ≤ n ↔ p.natDegree ≤ n := by
  refine' ⟨fun h => _, fun h => natDegree_add_le_of_degree_le h qn⟩
  refine' natDegree_le_iff_coeff_eq_zero.mpr fun m hm => _
  convert natDegree_le_iff_coeff_eq_zero.mp h m hm using 1
  rw [coeff_add, natDegree_le_iff_coeff_eq_zero.mp qn _ hm, add_zero]
#align polynomial.nat_degree_add_le_iff_left Polynomial.natDegree_add_le_iff_left

theorem natDegree_add_le_iff_right {n : ℕ} (p q : R[X]) (pn : p.natDegree ≤ n) :
    (p + q).natDegree ≤ n ↔ q.natDegree ≤ n := by
  rw [add_comm]
  exact natDegree_add_le_iff_left _ _ pn
#align polynomial.nat_degree_add_le_iff_right Polynomial.natDegree_add_le_iff_right

theorem natDegree_C_mul_le (a : R) (f : R[X]) : (C a * f).natDegree ≤ f.natDegree :=
  calc
    (C a * f).natDegree ≤ (C a).natDegree + f.natDegree := natDegree_mul_le
    _ = 0 + f.natDegree := by rw [natDegree_C a]
    _ = f.natDegree := zero_add _
set_option linter.uppercaseLean3 false in
#align polynomial.nat_degree_C_mul_le Polynomial.natDegree_C_mul_le

theorem natDegree_mul_C_le (f : R[X]) (a : R) : (f * C a).natDegree ≤ f.natDegree :=
  calc
    (f * C a).natDegree ≤ f.natDegree + (C a).natDegree := natDegree_mul_le
    _ = f.natDegree + 0 := by rw [natDegree_C a]
    _ = f.natDegree := add_zero _
set_option linter.uppercaseLean3 false in
#align polynomial.nat_degree_mul_C_le Polynomial.natDegree_mul_C_le

theorem eq_natDegree_of_le_mem_support (pn : p.natDegree ≤ n) (ns : n ∈ p.support) :
    p.natDegree = n :=
  le_antisymm pn (le_natDegree_of_mem_supp _ ns)
#align polynomial.eq_nat_degree_of_le_mem_support Polynomial.eq_natDegree_of_le_mem_support

theorem natDegree_C_mul_eq_of_mul_eq_one {ai : R} (au : ai * a = 1) :
    (C a * p).natDegree = p.natDegree :=
  le_antisymm (natDegree_C_mul_le a p)
    (calc
      p.natDegree = (1 * p).natDegree := by nth_rw 1 [← one_mul p]
      _ = (C ai * (C a * p)).natDegree := by rw [← C_1, ← au, RingHom.map_mul, ← mul_assoc]
      _ ≤ (C a * p).natDegree := natDegree_C_mul_le ai (C a * p))
set_option linter.uppercaseLean3 false in
#align polynomial.nat_degree_C_mul_eq_of_mul_eq_one Polynomial.natDegree_C_mul_eq_of_mul_eq_one

theorem natDegree_mul_C_eq_of_mul_eq_one {ai : R} (au : a * ai = 1) :
    (p * C a).natDegree = p.natDegree :=
  le_antisymm (natDegree_mul_C_le p a)
    (calc
      p.natDegree = (p * 1).natDegree := by nth_rw 1 [← mul_one p]
      _ = (p * C a * C ai).natDegree := by rw [← C_1, ← au, RingHom.map_mul, ← mul_assoc]
      _ ≤ (p * C a).natDegree := natDegree_mul_C_le (p * C a) ai)
set_option linter.uppercaseLean3 false in
#align polynomial.nat_degree_mul_C_eq_of_mul_eq_one Polynomial.natDegree_mul_C_eq_of_mul_eq_one

/-- Although not explicitly stated, the assumptions of lemma `nat_degree_mul_C_eq_of_mul_ne_zero`
force the polynomial `p` to be non-zero, via `p.leading_coeff ≠ 0`.
-/
theorem natDegree_mul_C_eq_of_mul_ne_zero (h : p.leadingCoeff * a ≠ 0) :
    (p * C a).natDegree = p.natDegree := by
  refine' eq_natDegree_of_le_mem_support (natDegree_mul_C_le p a) _
  refine' mem_support_iff.mpr _
  rwa [coeff_mul_C]
set_option linter.uppercaseLean3 false in
#align polynomial.nat_degree_mul_C_eq_of_mul_ne_zero Polynomial.natDegree_mul_C_eq_of_mul_ne_zero

/-- Although not explicitly stated, the assumptions of lemma `nat_degree_C_mul_eq_of_mul_ne_zero`
force the polynomial `p` to be non-zero, via `p.leading_coeff ≠ 0`.
-/
theorem natDegree_C_mul_eq_of_mul_ne_zero (h : a * p.leadingCoeff ≠ 0) :
    (C a * p).natDegree = p.natDegree := by
  refine' eq_natDegree_of_le_mem_support (natDegree_C_mul_le a p) _
  refine' mem_support_iff.mpr _
  rwa [coeff_C_mul]
set_option linter.uppercaseLean3 false in
#align polynomial.nat_degree_C_mul_eq_of_mul_ne_zero Polynomial.natDegree_C_mul_eq_of_mul_ne_zero

theorem natDegree_add_coeff_mul (f g : R[X]) :
    (f * g).coeff (f.natDegree + g.natDegree) = f.coeff f.natDegree * g.coeff g.natDegree := by
  simp only [coeff_natDegree, coeff_mul_degree_add_degree]
#align polynomial.nat_degree_add_coeff_mul Polynomial.natDegree_add_coeff_mul

theorem natDegree_lt_coeff_mul (h : p.natDegree + q.natDegree < m + n) :
    (p * q).coeff (m + n) = 0 :=
  coeff_eq_zero_of_natDegree_lt (natDegree_mul_le.trans_lt h)
#align polynomial.nat_degree_lt_coeff_mul Polynomial.natDegree_lt_coeff_mul

theorem coeff_mul_of_natDegree_le (pm : p.natDegree ≤ m) (qn : q.natDegree ≤ n) :
    (p * q).coeff (m + n) = p.coeff m * q.coeff n := by
  simp_rw [← Polynomial.toFinsupp_apply, toFinsupp_mul]
  refine AddMonoidAlgebra.apply_add_of_supDegree_le ?_ Function.injective_id ?_ ?_
  · simp
  · rwa [supDegree_eq_natDegree, id_eq]
  · rwa [supDegree_eq_natDegree, id_eq]
#align polynomial.coeff_mul_of_nat_degree_le Polynomial.coeff_mul_of_natDegree_le

theorem coeff_pow_of_natDegree_le (pn : p.natDegree ≤ n) :
    (p ^ m).coeff (m * n) = p.coeff n ^ m := by
  induction' m with m hm
  · simp
  · rw [pow_succ, pow_succ, ← hm, Nat.succ_mul, coeff_mul_of_natDegree_le _ pn]
    refine' natDegree_pow_le.trans (le_trans _ (le_refl _))
    exact mul_le_mul_of_nonneg_left pn m.zero_le
#align polynomial.coeff_pow_of_nat_degree_le Polynomial.coeff_pow_of_natDegree_le

theorem coeff_pow_eq_ite_of_natDegree_le_of_le {o : ℕ}
    (pn : natDegree p ≤ n) (mno : m * n ≤ o) :
    coeff (p ^ m) o = if o = m * n then (coeff p n) ^ m else 0 := by
  rcases eq_or_ne o (m * n) with rfl | h
  · simpa only [ite_true] using coeff_pow_of_natDegree_le pn
  · simpa only [h, ite_false] using coeff_eq_zero_of_natDegree_lt <|
      lt_of_le_of_lt (natDegree_pow_le_of_le m pn) (lt_of_le_of_ne mno h.symm)

theorem coeff_add_eq_left_of_lt (qn : q.natDegree < n) : (p + q).coeff n = p.coeff n :=
  (coeff_add _ _ _).trans <|
    (congr_arg _ <| coeff_eq_zero_of_natDegree_lt <| qn).trans <| add_zero _
#align polynomial.coeff_add_eq_left_of_lt Polynomial.coeff_add_eq_left_of_lt

theorem coeff_add_eq_right_of_lt (pn : p.natDegree < n) : (p + q).coeff n = q.coeff n := by
  rw [add_comm]
  exact coeff_add_eq_left_of_lt pn
#align polynomial.coeff_add_eq_right_of_lt Polynomial.coeff_add_eq_right_of_lt

theorem degree_sum_eq_of_disjoint (f : S → R[X]) (s : Finset S)
    (h : Set.Pairwise { i | i ∈ s ∧ f i ≠ 0 } (Ne on degree ∘ f)) :
    degree (s.sum f) = s.sup fun i => degree (f i) := by
  classical
  induction' s using Finset.induction_on with x s hx IH
  · simp
  · simp only [hx, Finset.sum_insert, not_false_iff, Finset.sup_insert]
    specialize IH (h.mono fun _ => by simp (config := { contextual := true }))
    rcases lt_trichotomy (degree (f x)) (degree (s.sum f)) with (H | H | H)
    · rw [← IH, sup_eq_right.mpr H.le, degree_add_eq_right_of_degree_lt H]
    · rcases s.eq_empty_or_nonempty with (rfl | hs)
      · simp
      obtain ⟨y, hy, hy'⟩ := Finset.exists_mem_eq_sup s hs fun i => degree (f i)
      rw [IH, hy'] at H
      by_cases hx0 : f x = 0
      · simp [hx0, IH]
      have hy0 : f y ≠ 0 := by
        contrapose! H
        simpa [H, degree_eq_bot] using hx0
      refine' absurd H (h _ _ fun H => hx _)
      · simp [hx0]
      · simp [hy, hy0]
      · exact H.symm ▸ hy
    · rw [← IH, sup_eq_left.mpr H.le, degree_add_eq_left_of_degree_lt H]
#align polynomial.degree_sum_eq_of_disjoint Polynomial.degree_sum_eq_of_disjoint

theorem natDegree_sum_eq_of_disjoint (f : S → R[X]) (s : Finset S)
    (h : Set.Pairwise { i | i ∈ s ∧ f i ≠ 0 } (Ne on natDegree ∘ f)) :
    natDegree (s.sum f) = s.sup fun i => natDegree (f i) := by
  by_cases H : ∃ x ∈ s, f x ≠ 0
  · obtain ⟨x, hx, hx'⟩ := H
    have hs : s.Nonempty := ⟨x, hx⟩
    refine' natDegree_eq_of_degree_eq_some _
    rw [degree_sum_eq_of_disjoint]
    · rw [← Finset.sup'_eq_sup hs, ← Finset.sup'_eq_sup hs,
        Nat.cast_withBot, Finset.coe_sup' hs, ←
        Finset.sup'_eq_sup hs]
      refine' le_antisymm _ _
      · rw [Finset.sup'_le_iff]
        intro b hb
        by_cases hb' : f b = 0
        · simpa [hb'] using hs
        rw [degree_eq_natDegree hb', Nat.cast_withBot]
        exact Finset.le_sup' (fun i : S => (natDegree (f i) : WithBot ℕ)) hb
      · rw [Finset.sup'_le_iff]
        intro b hb
        simp only [Finset.le_sup'_iff, exists_prop, Function.comp_apply]
        by_cases hb' : f b = 0
        · refine' ⟨x, hx, _⟩
          contrapose! hx'
          simpa [← Nat.cast_withBot, hb', degree_eq_bot] using hx'
        exact ⟨b, hb, (degree_eq_natDegree hb').ge⟩
    · exact h.imp fun x y hxy hxy' => hxy (natDegree_eq_of_degree_eq hxy')
  · push_neg at H
    rw [Finset.sum_eq_zero H, natDegree_zero, eq_comm, show 0 = ⊥ from rfl, Finset.sup_eq_bot_iff]
    intro x hx
    simp [H x hx]
#align polynomial.nat_degree_sum_eq_of_disjoint Polynomial.natDegree_sum_eq_of_disjoint

set_option linter.deprecated false in
theorem natDegree_bit0 (a : R[X]) : (bit0 a).natDegree ≤ a.natDegree :=
  (natDegree_add_le _ _).trans (max_self _).le
#align polynomial.nat_degree_bit0 Polynomial.natDegree_bit0

set_option linter.deprecated false in
theorem natDegree_bit1 (a : R[X]) : (bit1 a).natDegree ≤ a.natDegree :=
  (natDegree_add_le _ _).trans (by simp [natDegree_bit0])
#align polynomial.nat_degree_bit1 Polynomial.natDegree_bit1

variable [Semiring S]

theorem natDegree_pos_of_eval₂_root {p : R[X]} (hp : p ≠ 0) (f : R →+* S) {z : S}
    (hz : eval₂ f z p = 0) (inj : ∀ x : R, f x = 0 → x = 0) : 0 < natDegree p :=
  lt_of_not_ge fun hlt => by
    have A : p = C (p.coeff 0) := eq_C_of_natDegree_le_zero hlt
    rw [A, eval₂_C] at hz
    simp only [inj (p.coeff 0) hz, RingHom.map_zero] at A
    exact hp A
#align polynomial.nat_degree_pos_of_eval₂_root Polynomial.natDegree_pos_of_eval₂_root

theorem degree_pos_of_eval₂_root {p : R[X]} (hp : p ≠ 0) (f : R →+* S) {z : S}
    (hz : eval₂ f z p = 0) (inj : ∀ x : R, f x = 0 → x = 0) : 0 < degree p :=
  natDegree_pos_iff_degree_pos.mp (natDegree_pos_of_eval₂_root hp f hz inj)
#align polynomial.degree_pos_of_eval₂_root Polynomial.degree_pos_of_eval₂_root

@[simp]
theorem coe_lt_degree {p : R[X]} {n : ℕ} : (n : WithBot ℕ) < degree p ↔ n < natDegree p := by
  by_cases h : p = 0
  · simp [h]
  simp [degree_eq_natDegree h, Nat.cast_lt]
#align polynomial.coe_lt_degree Polynomial.coe_lt_degree

@[simp]
theorem degree_map_eq_iff {f : R →+* S} {p : Polynomial R} :
    degree (map f p) = degree p ↔ f (leadingCoeff p) ≠ 0 ∨ p = 0 := by
  rcases eq_or_ne p 0 with h|h
  · simp [h]
  simp only [h, or_false]
  refine ⟨fun h2 ↦ ?_, degree_map_eq_of_leadingCoeff_ne_zero f⟩
  have h3 : natDegree (map f p) = natDegree p := by simp_rw [natDegree, h2]
  have h4 : map f p ≠ 0 := by
    rwa [ne_eq, ← degree_eq_bot, h2, degree_eq_bot]
  rwa [← coeff_natDegree, ← coeff_map, ← h3, coeff_natDegree, ne_eq, leadingCoeff_eq_zero]

@[simp]
theorem natDegree_map_eq_iff {f : R →+* S} {p : Polynomial R} :
    natDegree (map f p) = natDegree p ↔ f (p.leadingCoeff) ≠ 0 ∨ natDegree p = 0 := by
  rcases eq_or_ne (natDegree p) 0 with h|h
  · simp_rw [h, ne_eq, or_true, iff_true, ← Nat.le_zero, ← h, natDegree_map_le f p]
  have h2 : p ≠ 0 := by rintro rfl; simp at h
  have h3 : degree p ≠ (0 : ℕ)  := degree_ne_of_natDegree_ne h
  simp_rw [h, or_false, natDegree, WithBot.unbot'_eq_unbot'_iff, degree_map_eq_iff]
  simp [h, h2, h3] -- simp doesn't rewrite in the hypothesis for some reason
  tauto

theorem natDegree_pos_of_nextCoeff_ne_zero (h : p.nextCoeff ≠ 0) : 0 < p.natDegree := by
  rw [nextCoeff] at h
  by_cases hpz : p.natDegree = 0
  · simp_all only [ne_eq, zero_le, ite_true, not_true_eq_false]
  · apply Nat.zero_lt_of_ne_zero hpz

end Degree

end Semiring

section Ring

variable [Ring R] {p q : R[X]}

theorem natDegree_sub : (p - q).natDegree = (q - p).natDegree := by rw [← natDegree_neg, neg_sub]
#align polynomial.nat_degree_sub Polynomial.natDegree_sub

theorem natDegree_sub_le_iff_left (qn : q.natDegree ≤ n) :
    (p - q).natDegree ≤ n ↔ p.natDegree ≤ n := by
  rw [← natDegree_neg] at qn
  rw [sub_eq_add_neg, natDegree_add_le_iff_left _ _ qn]
#align polynomial.nat_degree_sub_le_iff_left Polynomial.natDegree_sub_le_iff_left

theorem natDegree_sub_le_iff_right (pn : p.natDegree ≤ n) :
    (p - q).natDegree ≤ n ↔ q.natDegree ≤ n := by rwa [natDegree_sub, natDegree_sub_le_iff_left]
#align polynomial.nat_degree_sub_le_iff_right Polynomial.natDegree_sub_le_iff_right

theorem coeff_sub_eq_left_of_lt (dg : q.natDegree < n) : (p - q).coeff n = p.coeff n := by
  rw [← natDegree_neg] at dg
  rw [sub_eq_add_neg, coeff_add_eq_left_of_lt dg]
#align polynomial.coeff_sub_eq_left_of_lt Polynomial.coeff_sub_eq_left_of_lt

theorem coeff_sub_eq_neg_right_of_lt (df : p.natDegree < n) : (p - q).coeff n = -q.coeff n := by
  rwa [sub_eq_add_neg, coeff_add_eq_right_of_lt, coeff_neg]
#align polynomial.coeff_sub_eq_neg_right_of_lt Polynomial.coeff_sub_eq_neg_right_of_lt

end Ring

section NoZeroDivisors

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]} {a : R}

theorem degree_mul_C (a0 : a ≠ 0) : (p * C a).degree = p.degree := by
  rw [degree_mul, degree_C a0, add_zero]
set_option linter.uppercaseLean3 false in
#align polynomial.degree_mul_C Polynomial.degree_mul_C

theorem degree_C_mul (a0 : a ≠ 0) : (C a * p).degree = p.degree := by
  rw [degree_mul, degree_C a0, zero_add]
set_option linter.uppercaseLean3 false in
#align polynomial.degree_C_mul Polynomial.degree_C_mul

theorem natDegree_mul_C (a0 : a ≠ 0) : (p * C a).natDegree = p.natDegree := by
  simp only [natDegree, degree_mul_C a0]
set_option linter.uppercaseLean3 false in
#align polynomial.natDegree_mul_C Polynomial.natDegree_mul_C

theorem natDegree_C_mul (a0 : a ≠ 0) : (C a * p).natDegree = p.natDegree := by
  simp only [natDegree, degree_C_mul a0]
set_option linter.uppercaseLean3 false in
#align polynomial.nat_degree_C_mul Polynomial.natDegree_C_mul

@[simp]
lemma nextCoeff_C_mul_X_add_C (ha : a ≠ 0) (c : R) : nextCoeff (C a * X + C c) = c := by
  rw [nextCoeff_of_natDegree_pos] <;> simp [ha]

lemma natDegree_eq_one : p.natDegree = 1 ↔ ∃ a ≠ 0, ∃ b, C a * X + C b = p := by
  refine ⟨fun hp ↦ ⟨p.coeff 1, fun h ↦ ?_, p.coeff 0, ?_⟩, ?_⟩
  · rw [← hp, coeff_natDegree, leadingCoeff_eq_zero] at h
    aesop
  · ext n
    obtain _ | _ | n := n
    · simp
    · simp
    · simp only [coeff_add, coeff_mul_X, coeff_C_succ, add_zero]
      rw [coeff_eq_zero_of_natDegree_lt]
      simp [hp]
  · rintro ⟨a, ha, b, rfl⟩
    simp [ha]

theorem natDegree_comp : natDegree (p.comp q) = natDegree p * natDegree q := by
  by_cases q0 : q.natDegree = 0
  · rw [degree_le_zero_iff.mp (natDegree_eq_zero_iff_degree_le_zero.mp q0), comp_C, natDegree_C,
      natDegree_C, mul_zero]
  · by_cases p0 : p = 0
    · simp only [p0, zero_comp, natDegree_zero, zero_mul]
    refine' le_antisymm natDegree_comp_le (le_natDegree_of_ne_zero _)
    simp only [coeff_comp_degree_mul_degree q0, p0, mul_eq_zero, leadingCoeff_eq_zero, or_self_iff,
      ne_zero_of_natDegree_gt (Nat.pos_of_ne_zero q0), pow_ne_zero, Ne, not_false_iff]
#align polynomial.nat_degree_comp Polynomial.natDegree_comp

@[simp]
theorem natDegree_iterate_comp (k : ℕ) :
    (p.comp^[k] q).natDegree = p.natDegree ^ k * q.natDegree := by
  induction' k with k IH
  · simp
  · rw [Function.iterate_succ_apply', natDegree_comp, IH, pow_succ', mul_assoc]
#align polynomial.nat_degree_iterate_comp Polynomial.natDegree_iterate_comp

theorem leadingCoeff_comp (hq : natDegree q ≠ 0) :
    leadingCoeff (p.comp q) = leadingCoeff p * leadingCoeff q ^ natDegree p := by
  rw [← coeff_comp_degree_mul_degree hq, ← natDegree_comp, coeff_natDegree]
#align polynomial.leading_coeff_comp Polynomial.leadingCoeff_comp

end NoZeroDivisors

section DivisionRing

variable {K : Type*} [DivisionRing K]

/-! Useful lemmas for the "monicization" of a nonzero polynomial `p`. -/
@[simp]
theorem irreducible_mul_leadingCoeff_inv {p : K[X]} :
    Irreducible (p * C (leadingCoeff p)⁻¹) ↔ Irreducible p := by
  by_cases hp0 : p = 0
  · simp [hp0]
  exact irreducible_mul_isUnit
    (isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero (leadingCoeff_ne_zero.mpr hp0))))

@[simp] lemma dvd_mul_leadingCoeff_inv {p q : K[X]} (hp0 : p ≠ 0) :
    q ∣ p * C (leadingCoeff p)⁻¹ ↔ q ∣ p :=
  IsUnit.dvd_mul_right <| isUnit_C.mpr <| IsUnit.mk0 _ <|
    inv_ne_zero <| leadingCoeff_ne_zero.mpr hp0

theorem monic_mul_leadingCoeff_inv {p : K[X]} (h : p ≠ 0) : Monic (p * C (leadingCoeff p)⁻¹) := by
  rw [Monic, leadingCoeff_mul, leadingCoeff_C,
    mul_inv_cancel (show leadingCoeff p ≠ 0 from mt leadingCoeff_eq_zero.1 h)]
#align polynomial.monic_mul_leading_coeff_inv Polynomial.monic_mul_leadingCoeff_inv

-- `simp` normal form of `degree_mul_leadingCoeff_inv`
@[simp] lemma degree_leadingCoeff_inv {p : K[X]} (hp0 : p ≠ 0) :
    degree (C (leadingCoeff p)⁻¹) = 0 :=
  degree_C (inv_ne_zero <| leadingCoeff_ne_zero.mpr hp0)

theorem degree_mul_leadingCoeff_inv (p : K[X]) {q : K[X]} (h : q ≠ 0) :
    degree (p * C (leadingCoeff q)⁻¹) = degree p := by
  have h₁ : (leadingCoeff q)⁻¹ ≠ 0 := inv_ne_zero (mt leadingCoeff_eq_zero.1 h)
  rw [degree_mul_C h₁]
#align polynomial.degree_mul_leading_coeff_inv Polynomial.degree_mul_leadingCoeff_inv

theorem natDegree_mul_leadingCoeff_inv (p : K[X]) {q : K[X]} (h : q ≠ 0) :
    natDegree (p * C (leadingCoeff q)⁻¹) = natDegree p :=
  natDegree_eq_of_degree_eq (degree_mul_leadingCoeff_inv _ h)

theorem degree_mul_leadingCoeff_self_inv (p : K[X]) :
    degree (p * C (leadingCoeff p)⁻¹) = degree p := by
  by_cases hp : p = 0
  · simp [hp]
  exact degree_mul_leadingCoeff_inv _ hp

theorem natDegree_mul_leadingCoeff_self_inv (p : K[X]) :
    natDegree (p * C (leadingCoeff p)⁻¹) = natDegree p :=
  natDegree_eq_of_degree_eq (degree_mul_leadingCoeff_self_inv _)

-- `simp` normal form of `degree_mul_leadingCoeff_self_inv`
@[simp] lemma degree_add_degree_leadingCoeff_inv (p : K[X]) :
    degree p + degree (C (leadingCoeff p)⁻¹) = degree p := by
  rw [← degree_mul, degree_mul_leadingCoeff_self_inv]

end DivisionRing

end Polynomial
