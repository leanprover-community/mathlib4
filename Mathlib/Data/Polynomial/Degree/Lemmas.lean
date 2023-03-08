/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker

! This file was ported from Lean 3 source module data.polynomial.degree.lemmas
! leanprover-community/mathlib commit 302eab4f46abb63de520828de78c04cb0f9b5836
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Polynomial.Eval

/-!
# Theory of degrees of polynomials

Some of the main results include
- `nat_degree_comp_le` : The degree of the composition is at most the product of degrees

-/


noncomputable section

open Classical Polynomial

open Finsupp Finset

namespace Polynomial

universe u v w

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

section Degree

theorem natDegree_comp_le : natDegree (p.comp q) ≤ natDegree p * natDegree q :=
  if h0 : p.comp q = 0 then by rw [h0, nat_degree_zero] <;> exact Nat.zero_le _
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
              _ ≤ natDegree (C (coeff p n)) + n • natDegree q :=
                (add_le_add_left (nsmul_le_nsmul_of_le_right (@degree_le_natDegree _ _ q) n) _)
              _ = (n * natDegree q : ℕ) := by
                rw [nat_degree_C, WithBot.coe_zero, zero_add, ← WithBot.coe_nsmul, nsmul_eq_mul] <;>
                  simp
              _ ≤ (natDegree p * natDegree q : ℕ) :=
                WithBot.coe_le_coe.2 <|
                  mul_le_mul_of_nonneg_right (le_natDegree_of_ne_zero (mem_support_iff.1 hn))
                    (Nat.zero_le _)
              
        
#align polynomial.nat_degree_comp_le Polynomial.natDegree_comp_le

theorem degree_pos_of_root {p : R[X]} (hp : p ≠ 0) (h : IsRoot p a) : 0 < degree p :=
  lt_of_not_ge fun hlt => by
    have := eq_C_of_degree_le_zero hlt
    rw [is_root, this, eval_C] at h
    simp only [h, RingHom.map_zero] at this
    exact hp this
#align polynomial.degree_pos_of_root Polynomial.degree_pos_of_root

theorem natDegree_le_iff_coeff_eq_zero : p.natDegree ≤ n ↔ ∀ N : ℕ, n < N → p.coeff N = 0 := by
  simp_rw [nat_degree_le_iff_degree_le, degree_le_iff_coeff_zero, WithBot.coe_lt_coe]
#align polynomial.nat_degree_le_iff_coeff_eq_zero Polynomial.natDegree_le_iff_coeff_eq_zero

theorem natDegree_add_le_iff_left {n : ℕ} (p q : R[X]) (qn : q.natDegree ≤ n) :
    (p + q).natDegree ≤ n ↔ p.natDegree ≤ n :=
  by
  refine' ⟨fun h => _, fun h => nat_degree_add_le_of_degree_le h qn⟩
  refine' nat_degree_le_iff_coeff_eq_zero.mpr fun m hm => _
  convert nat_degree_le_iff_coeff_eq_zero.mp h m hm using 1
  rw [coeff_add, nat_degree_le_iff_coeff_eq_zero.mp qn _ hm, add_zero]
#align polynomial.nat_degree_add_le_iff_left Polynomial.natDegree_add_le_iff_left

theorem natDegree_add_le_iff_right {n : ℕ} (p q : R[X]) (pn : p.natDegree ≤ n) :
    (p + q).natDegree ≤ n ↔ q.natDegree ≤ n :=
  by
  rw [add_comm]
  exact nat_degree_add_le_iff_left _ _ pn
#align polynomial.nat_degree_add_le_iff_right Polynomial.natDegree_add_le_iff_right

theorem natDegree_c_mul_le (a : R) (f : R[X]) : (C a * f).natDegree ≤ f.natDegree :=
  calc
    (C a * f).natDegree ≤ (C a).natDegree + f.natDegree := natDegree_mul_le
    _ = 0 + f.natDegree := by rw [nat_degree_C a]
    _ = f.natDegree := zero_add _
    
#align polynomial.nat_degree_C_mul_le Polynomial.natDegree_c_mul_le

theorem natDegree_mul_c_le (f : R[X]) (a : R) : (f * C a).natDegree ≤ f.natDegree :=
  calc
    (f * C a).natDegree ≤ f.natDegree + (C a).natDegree := natDegree_mul_le
    _ = f.natDegree + 0 := by rw [nat_degree_C a]
    _ = f.natDegree := add_zero _
    
#align polynomial.nat_degree_mul_C_le Polynomial.natDegree_mul_c_le

theorem eq_natDegree_of_le_mem_support (pn : p.natDegree ≤ n) (ns : n ∈ p.support) :
    p.natDegree = n :=
  le_antisymm pn (le_natDegree_of_mem_supp _ ns)
#align polynomial.eq_nat_degree_of_le_mem_support Polynomial.eq_natDegree_of_le_mem_support

theorem natDegree_c_mul_eq_of_mul_eq_one {ai : R} (au : ai * a = 1) :
    (C a * p).natDegree = p.natDegree :=
  le_antisymm (natDegree_c_mul_le a p)
    (calc
      p.natDegree = (1 * p).natDegree := by nth_rw 1 [← one_mul p]
      _ = (C ai * (C a * p)).natDegree := by rw [← C_1, ← au, RingHom.map_mul, ← mul_assoc]
      _ ≤ (C a * p).natDegree := natDegree_c_mul_le ai (C a * p)
      )
#align polynomial.nat_degree_C_mul_eq_of_mul_eq_one Polynomial.natDegree_c_mul_eq_of_mul_eq_one

theorem natDegree_mul_c_eq_of_mul_eq_one {ai : R} (au : a * ai = 1) :
    (p * C a).natDegree = p.natDegree :=
  le_antisymm (natDegree_mul_c_le p a)
    (calc
      p.natDegree = (p * 1).natDegree := by nth_rw 1 [← mul_one p]
      _ = (p * C a * C ai).natDegree := by rw [← C_1, ← au, RingHom.map_mul, ← mul_assoc]
      _ ≤ (p * C a).natDegree := natDegree_mul_c_le (p * C a) ai
      )
#align polynomial.nat_degree_mul_C_eq_of_mul_eq_one Polynomial.natDegree_mul_c_eq_of_mul_eq_one

/-- Although not explicitly stated, the assumptions of lemma `nat_degree_mul_C_eq_of_mul_ne_zero`
force the polynomial `p` to be non-zero, via `p.leading_coeff ≠ 0`.
-/
theorem natDegree_mul_c_eq_of_mul_ne_zero (h : p.leadingCoeff * a ≠ 0) :
    (p * C a).natDegree = p.natDegree :=
  by
  refine' eq_nat_degree_of_le_mem_support (nat_degree_mul_C_le p a) _
  refine' mem_support_iff.mpr _
  rwa [coeff_mul_C]
#align polynomial.nat_degree_mul_C_eq_of_mul_ne_zero Polynomial.natDegree_mul_c_eq_of_mul_ne_zero

/-- Although not explicitly stated, the assumptions of lemma `nat_degree_C_mul_eq_of_mul_ne_zero`
force the polynomial `p` to be non-zero, via `p.leading_coeff ≠ 0`.
-/
theorem natDegree_c_mul_eq_of_mul_ne_zero (h : a * p.leadingCoeff ≠ 0) :
    (C a * p).natDegree = p.natDegree :=
  by
  refine' eq_nat_degree_of_le_mem_support (nat_degree_C_mul_le a p) _
  refine' mem_support_iff.mpr _
  rwa [coeff_C_mul]
#align polynomial.nat_degree_C_mul_eq_of_mul_ne_zero Polynomial.natDegree_c_mul_eq_of_mul_ne_zero

theorem natDegree_add_coeff_mul (f g : R[X]) :
    (f * g).coeff (f.natDegree + g.natDegree) = f.coeff f.natDegree * g.coeff g.natDegree := by
  simp only [coeff_nat_degree, coeff_mul_degree_add_degree]
#align polynomial.nat_degree_add_coeff_mul Polynomial.natDegree_add_coeff_mul

theorem natDegree_lt_coeff_mul (h : p.natDegree + q.natDegree < m + n) :
    (p * q).coeff (m + n) = 0 :=
  coeff_eq_zero_of_natDegree_lt (natDegree_mul_le.trans_lt h)
#align polynomial.nat_degree_lt_coeff_mul Polynomial.natDegree_lt_coeff_mul

theorem coeff_mul_of_natDegree_le (pm : p.natDegree ≤ m) (qn : q.natDegree ≤ n) :
    (p * q).coeff (m + n) = p.coeff m * q.coeff n :=
  by
  rcases eq_or_lt_of_le pm with (rfl | hm) <;> rcases eq_or_lt_of_le qn with (rfl | hn)
  · exact nat_degree_add_coeff_mul _ _
  · rw [coeff_eq_zero_of_nat_degree_lt hn, mul_zero]
    exact nat_degree_lt_coeff_mul (add_lt_add_left hn _)
  · rw [coeff_eq_zero_of_nat_degree_lt hm, zero_mul]
    exact nat_degree_lt_coeff_mul (add_lt_add_right hm _)
  · rw [coeff_eq_zero_of_nat_degree_lt hn, mul_zero]
    exact nat_degree_lt_coeff_mul (add_lt_add hm hn)
#align polynomial.coeff_mul_of_nat_degree_le Polynomial.coeff_mul_of_natDegree_le

theorem coeff_pow_of_natDegree_le (pn : p.natDegree ≤ n) : (p ^ m).coeff (n * m) = p.coeff n ^ m :=
  by
  induction' m with m hm
  · simp
  · rw [pow_succ', pow_succ', ← hm, Nat.mul_succ, coeff_mul_of_nat_degree_le _ pn]
    refine' nat_degree_pow_le.trans (le_trans _ (mul_comm _ _).le)
    exact mul_le_mul_of_nonneg_left pn m.zero_le
#align polynomial.coeff_pow_of_nat_degree_le Polynomial.coeff_pow_of_natDegree_le

theorem coeff_add_eq_left_of_lt (qn : q.natDegree < n) : (p + q).coeff n = p.coeff n :=
  (coeff_add _ _ _).trans <|
    (congr_arg _ <| coeff_eq_zero_of_natDegree_lt <| qn).trans <| add_zero _
#align polynomial.coeff_add_eq_left_of_lt Polynomial.coeff_add_eq_left_of_lt

theorem coeff_add_eq_right_of_lt (pn : p.natDegree < n) : (p + q).coeff n = q.coeff n :=
  by
  rw [add_comm]
  exact coeff_add_eq_left_of_lt pn
#align polynomial.coeff_add_eq_right_of_lt Polynomial.coeff_add_eq_right_of_lt

theorem degree_sum_eq_of_disjoint (f : S → R[X]) (s : Finset S)
    (h : Set.Pairwise { i | i ∈ s ∧ f i ≠ 0 } (Ne on degree ∘ f)) :
    degree (s.Sum f) = s.sup fun i => degree (f i) :=
  by
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
    natDegree (s.Sum f) = s.sup fun i => natDegree (f i) :=
  by
  by_cases H : ∃ x ∈ s, f x ≠ 0
  · obtain ⟨x, hx, hx'⟩ := H
    have hs : s.nonempty := ⟨x, hx⟩
    refine' nat_degree_eq_of_degree_eq_some _
    rw [degree_sum_eq_of_disjoint]
    · rw [← Finset.sup'_eq_sup hs, ← Finset.sup'_eq_sup hs, Finset.coe_sup', ←
        Finset.sup'_eq_sup hs]
      refine' le_antisymm _ _
      · rw [Finset.sup'_le_iff]
        intro b hb
        by_cases hb' : f b = 0
        · simpa [hb'] using hs
        rw [degree_eq_nat_degree hb']
        exact Finset.le_sup' _ hb
      · rw [Finset.sup'_le_iff]
        intro b hb
        simp only [Finset.le_sup'_iff, exists_prop, Function.comp_apply]
        by_cases hb' : f b = 0
        · refine' ⟨x, hx, _⟩
          contrapose! hx'
          simpa [hb', degree_eq_bot] using hx'
        exact ⟨b, hb, (degree_eq_nat_degree hb').ge⟩
    · exact h.imp fun x y hxy hxy' => hxy (nat_degree_eq_of_degree_eq hxy')
  · push_neg  at H
    rw [Finset.sum_eq_zero H, nat_degree_zero, eq_comm, show 0 = ⊥ from rfl, Finset.sup_eq_bot_iff]
    intro x hx
    simp [H x hx]
#align polynomial.nat_degree_sum_eq_of_disjoint Polynomial.natDegree_sum_eq_of_disjoint

theorem natDegree_bit0 (a : R[X]) : (bit0 a).natDegree ≤ a.natDegree :=
  (natDegree_add_le _ _).trans (max_self _).le
#align polynomial.nat_degree_bit0 Polynomial.natDegree_bit0

theorem natDegree_bit1 (a : R[X]) : (bit1 a).natDegree ≤ a.natDegree :=
  (natDegree_add_le _ _).trans (by simp [nat_degree_bit0])
#align polynomial.nat_degree_bit1 Polynomial.natDegree_bit1

variable [Semiring S]

theorem natDegree_pos_of_eval₂_root {p : R[X]} (hp : p ≠ 0) (f : R →+* S) {z : S}
    (hz : eval₂ f z p = 0) (inj : ∀ x : R, f x = 0 → x = 0) : 0 < natDegree p :=
  lt_of_not_ge fun hlt =>
    by
    have A : p = C (p.coeff 0) := eq_C_of_nat_degree_le_zero hlt
    rw [A, eval₂_C] at hz
    simp only [inj (p.coeff 0) hz, RingHom.map_zero] at A
    exact hp A
#align polynomial.nat_degree_pos_of_eval₂_root Polynomial.natDegree_pos_of_eval₂_root

theorem degree_pos_of_eval₂_root {p : R[X]} (hp : p ≠ 0) (f : R →+* S) {z : S}
    (hz : eval₂ f z p = 0) (inj : ∀ x : R, f x = 0 → x = 0) : 0 < degree p :=
  natDegree_pos_iff_degree_pos.mp (natDegree_pos_of_eval₂_root hp f hz inj)
#align polynomial.degree_pos_of_eval₂_root Polynomial.degree_pos_of_eval₂_root

@[simp]
theorem coe_lt_degree {p : R[X]} {n : ℕ} : (n : WithBot ℕ) < degree p ↔ n < natDegree p :=
  by
  by_cases h : p = 0
  · simp [h]
  rw [degree_eq_nat_degree h, WithBot.coe_lt_coe]
#align polynomial.coe_lt_degree Polynomial.coe_lt_degree

end Degree

end Semiring

section Ring

variable [Ring R] {p q : R[X]}

theorem natDegree_sub : (p - q).natDegree = (q - p).natDegree := by rw [← nat_degree_neg, neg_sub]
#align polynomial.nat_degree_sub Polynomial.natDegree_sub

theorem natDegree_sub_le_iff_left (qn : q.natDegree ≤ n) :
    (p - q).natDegree ≤ n ↔ p.natDegree ≤ n :=
  by
  rw [← nat_degree_neg] at qn
  rw [sub_eq_add_neg, nat_degree_add_le_iff_left _ _ qn]
#align polynomial.nat_degree_sub_le_iff_left Polynomial.natDegree_sub_le_iff_left

theorem natDegree_sub_le_iff_right (pn : p.natDegree ≤ n) :
    (p - q).natDegree ≤ n ↔ q.natDegree ≤ n := by rwa [nat_degree_sub, nat_degree_sub_le_iff_left]
#align polynomial.nat_degree_sub_le_iff_right Polynomial.natDegree_sub_le_iff_right

theorem coeff_sub_eq_left_of_lt (dg : q.natDegree < n) : (p - q).coeff n = p.coeff n :=
  by
  rw [← nat_degree_neg] at dg
  rw [sub_eq_add_neg, coeff_add_eq_left_of_lt dg]
#align polynomial.coeff_sub_eq_left_of_lt Polynomial.coeff_sub_eq_left_of_lt

theorem coeff_sub_eq_neg_right_of_lt (df : p.natDegree < n) : (p - q).coeff n = -q.coeff n := by
  rwa [sub_eq_add_neg, coeff_add_eq_right_of_lt, coeff_neg]
#align polynomial.coeff_sub_eq_neg_right_of_lt Polynomial.coeff_sub_eq_neg_right_of_lt

end Ring

section NoZeroDivisors

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

theorem degree_mul_c (a0 : a ≠ 0) : (p * C a).degree = p.degree := by
  rw [degree_mul, degree_C a0, add_zero]
#align polynomial.degree_mul_C Polynomial.degree_mul_c

theorem degree_c_mul (a0 : a ≠ 0) : (C a * p).degree = p.degree := by
  rw [degree_mul, degree_C a0, zero_add]
#align polynomial.degree_C_mul Polynomial.degree_c_mul

theorem natDegree_mul_c (a0 : a ≠ 0) : (p * C a).natDegree = p.natDegree := by
  simp only [nat_degree, degree_mul_C a0]
#align polynomial.nat_degree_mul_C Polynomial.natDegree_mul_c

theorem natDegree_c_mul (a0 : a ≠ 0) : (C a * p).natDegree = p.natDegree := by
  simp only [nat_degree, degree_C_mul a0]
#align polynomial.nat_degree_C_mul Polynomial.natDegree_c_mul

theorem natDegree_comp : natDegree (p.comp q) = natDegree p * natDegree q :=
  by
  by_cases q0 : q.nat_degree = 0
  ·
    rw [degree_le_zero_iff.mp (nat_degree_eq_zero_iff_degree_le_zero.mp q0), comp_C, nat_degree_C,
      nat_degree_C, mul_zero]
  · by_cases p0 : p = 0
    · simp only [p0, zero_comp, nat_degree_zero, zero_mul]
    refine' le_antisymm nat_degree_comp_le (le_nat_degree_of_ne_zero _)
    simp only [coeff_comp_degree_mul_degree q0, p0, mul_eq_zero, leading_coeff_eq_zero, or_self_iff,
      ne_zero_of_nat_degree_gt (Nat.pos_of_ne_zero q0), pow_ne_zero, Ne.def, not_false_iff]
#align polynomial.nat_degree_comp Polynomial.natDegree_comp

theorem leadingCoeff_comp (hq : natDegree q ≠ 0) :
    leadingCoeff (p.comp q) = leadingCoeff p * leadingCoeff q ^ natDegree p := by
  rw [← coeff_comp_degree_mul_degree hq, ← nat_degree_comp, coeff_nat_degree]
#align polynomial.leading_coeff_comp Polynomial.leadingCoeff_comp

end NoZeroDivisors

end Polynomial

