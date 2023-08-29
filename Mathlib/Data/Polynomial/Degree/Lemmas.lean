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

open Classical Polynomial

open Finsupp Finset

namespace Polynomial

universe u v w

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

section Degree

theorem natDegree_comp_le : natDegree (p.comp q) ≤ natDegree p * natDegree q :=
  if h0 : p.comp q = 0 then by rw [h0, natDegree_zero]; exact Nat.zero_le _
                               -- ⊢ 0 ≤ natDegree p * natDegree q
                                                        -- 🎉 no goals
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
                (add_le_add_left (nsmul_le_nsmul_of_le_right (@degree_le_natDegree _ _ q) n) _)
              _ = (n * natDegree q : ℕ) := by
                rw [natDegree_C, Nat.cast_zero, zero_add, nsmul_eq_mul];
                -- ⊢ ↑n * ↑(natDegree q) = ↑(n * natDegree q)
                  simp
                  -- 🎉 no goals
              _ ≤ (natDegree p * natDegree q : ℕ) :=
                WithBot.coe_le_coe.2 <|
                  mul_le_mul_of_nonneg_right (le_natDegree_of_ne_zero (mem_support_iff.1 hn))
                    (Nat.zero_le _)
#align polynomial.nat_degree_comp_le Polynomial.natDegree_comp_le

theorem degree_pos_of_root {p : R[X]} (hp : p ≠ 0) (h : IsRoot p a) : 0 < degree p :=
  lt_of_not_ge fun hlt => by
    have := eq_C_of_degree_le_zero hlt
    -- ⊢ False
    rw [IsRoot, this, eval_C] at h
    -- ⊢ False
    simp only [h, RingHom.map_zero] at this
    -- ⊢ False
    exact hp this
    -- 🎉 no goals
#align polynomial.degree_pos_of_root Polynomial.degree_pos_of_root

theorem natDegree_le_iff_coeff_eq_zero : p.natDegree ≤ n ↔ ∀ N : ℕ, n < N → p.coeff N = 0 := by
  simp_rw [natDegree_le_iff_degree_le, degree_le_iff_coeff_zero, Nat.cast_withBot,
    WithBot.coe_lt_coe]
#align polynomial.nat_degree_le_iff_coeff_eq_zero Polynomial.natDegree_le_iff_coeff_eq_zero

theorem natDegree_add_le_iff_left {n : ℕ} (p q : R[X]) (qn : q.natDegree ≤ n) :
    (p + q).natDegree ≤ n ↔ p.natDegree ≤ n := by
  refine' ⟨fun h => _, fun h => natDegree_add_le_of_degree_le h qn⟩
  -- ⊢ natDegree p ≤ n
  refine' natDegree_le_iff_coeff_eq_zero.mpr fun m hm => _
  -- ⊢ coeff p m = 0
  convert natDegree_le_iff_coeff_eq_zero.mp h m hm using 1
  -- ⊢ coeff p m = coeff (p + q) m
  rw [coeff_add, natDegree_le_iff_coeff_eq_zero.mp qn _ hm, add_zero]
  -- 🎉 no goals
#align polynomial.nat_degree_add_le_iff_left Polynomial.natDegree_add_le_iff_left

theorem natDegree_add_le_iff_right {n : ℕ} (p q : R[X]) (pn : p.natDegree ≤ n) :
    (p + q).natDegree ≤ n ↔ q.natDegree ≤ n := by
  rw [add_comm]
  -- ⊢ natDegree (q + p) ≤ n ↔ natDegree q ≤ n
  exact natDegree_add_le_iff_left _ _ pn
  -- 🎉 no goals
#align polynomial.nat_degree_add_le_iff_right Polynomial.natDegree_add_le_iff_right

theorem natDegree_C_mul_le (a : R) (f : R[X]) : (C a * f).natDegree ≤ f.natDegree :=
  calc
    (C a * f).natDegree ≤ (C a).natDegree + f.natDegree := natDegree_mul_le
    _ = 0 + f.natDegree := by rw [natDegree_C a]
                              -- 🎉 no goals
    _ = f.natDegree := zero_add _
set_option linter.uppercaseLean3 false in
#align polynomial.nat_degree_C_mul_le Polynomial.natDegree_C_mul_le

theorem natDegree_mul_C_le (f : R[X]) (a : R) : (f * C a).natDegree ≤ f.natDegree :=
  calc
    (f * C a).natDegree ≤ f.natDegree + (C a).natDegree := natDegree_mul_le
    _ = f.natDegree + 0 := by rw [natDegree_C a]
                              -- 🎉 no goals
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
                                            -- 🎉 no goals
      _ = (C ai * (C a * p)).natDegree := by rw [← C_1, ← au, RingHom.map_mul, ← mul_assoc]
                                             -- 🎉 no goals
      _ ≤ (C a * p).natDegree := natDegree_C_mul_le ai (C a * p))
set_option linter.uppercaseLean3 false in
#align polynomial.nat_degree_C_mul_eq_of_mul_eq_one Polynomial.natDegree_C_mul_eq_of_mul_eq_one

theorem natDegree_mul_C_eq_of_mul_eq_one {ai : R} (au : a * ai = 1) :
    (p * C a).natDegree = p.natDegree :=
  le_antisymm (natDegree_mul_C_le p a)
    (calc
      p.natDegree = (p * 1).natDegree := by nth_rw 1 [← mul_one p]
                                            -- 🎉 no goals
      _ = (p * C a * C ai).natDegree := by rw [← C_1, ← au, RingHom.map_mul, ← mul_assoc]
                                           -- 🎉 no goals
      _ ≤ (p * C a).natDegree := natDegree_mul_C_le (p * C a) ai)
set_option linter.uppercaseLean3 false in
#align polynomial.nat_degree_mul_C_eq_of_mul_eq_one Polynomial.natDegree_mul_C_eq_of_mul_eq_one

/-- Although not explicitly stated, the assumptions of lemma `nat_degree_mul_C_eq_of_mul_ne_zero`
force the polynomial `p` to be non-zero, via `p.leading_coeff ≠ 0`.
-/
theorem natDegree_mul_C_eq_of_mul_ne_zero (h : p.leadingCoeff * a ≠ 0) :
    (p * C a).natDegree = p.natDegree := by
  refine' eq_natDegree_of_le_mem_support (natDegree_mul_C_le p a) _
  -- ⊢ natDegree p ∈ support (p * ↑C a)
  refine' mem_support_iff.mpr _
  -- ⊢ coeff (p * ↑C a) (natDegree p) ≠ 0
  rwa [coeff_mul_C]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.nat_degree_mul_C_eq_of_mul_ne_zero Polynomial.natDegree_mul_C_eq_of_mul_ne_zero

/-- Although not explicitly stated, the assumptions of lemma `nat_degree_C_mul_eq_of_mul_ne_zero`
force the polynomial `p` to be non-zero, via `p.leading_coeff ≠ 0`.
-/
theorem natDegree_C_mul_eq_of_mul_ne_zero (h : a * p.leadingCoeff ≠ 0) :
    (C a * p).natDegree = p.natDegree := by
  refine' eq_natDegree_of_le_mem_support (natDegree_C_mul_le a p) _
  -- ⊢ natDegree p ∈ support (↑C a * p)
  refine' mem_support_iff.mpr _
  -- ⊢ coeff (↑C a * p) (natDegree p) ≠ 0
  rwa [coeff_C_mul]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.nat_degree_C_mul_eq_of_mul_ne_zero Polynomial.natDegree_C_mul_eq_of_mul_ne_zero

theorem natDegree_add_coeff_mul (f g : R[X]) :
    (f * g).coeff (f.natDegree + g.natDegree) = f.coeff f.natDegree * g.coeff g.natDegree := by
  simp only [coeff_natDegree, coeff_mul_degree_add_degree]
  -- 🎉 no goals
#align polynomial.nat_degree_add_coeff_mul Polynomial.natDegree_add_coeff_mul

theorem natDegree_lt_coeff_mul (h : p.natDegree + q.natDegree < m + n) :
    (p * q).coeff (m + n) = 0 :=
  coeff_eq_zero_of_natDegree_lt (natDegree_mul_le.trans_lt h)
#align polynomial.nat_degree_lt_coeff_mul Polynomial.natDegree_lt_coeff_mul

theorem coeff_mul_of_natDegree_le (pm : p.natDegree ≤ m) (qn : q.natDegree ≤ n) :
    (p * q).coeff (m + n) = p.coeff m * q.coeff n := by
  rcases eq_or_lt_of_le pm with (rfl | hm) <;> rcases eq_or_lt_of_le qn with (rfl | hn)
  -- ⊢ coeff (p * q) (natDegree p + n) = coeff p (natDegree p) * coeff q n
                                               -- ⊢ coeff (p * q) (natDegree p + natDegree q) = coeff p (natDegree p) * coeff q  …
                                               -- ⊢ coeff (p * q) (m + natDegree q) = coeff p m * coeff q (natDegree q)
  · exact natDegree_add_coeff_mul _ _
    -- 🎉 no goals
  · rw [coeff_eq_zero_of_natDegree_lt hn, mul_zero]
    -- ⊢ coeff (p * q) (natDegree p + n) = 0
    exact natDegree_lt_coeff_mul (add_lt_add_left hn _)
    -- 🎉 no goals
  · rw [coeff_eq_zero_of_natDegree_lt hm, zero_mul]
    -- ⊢ coeff (p * q) (m + natDegree q) = 0
    exact natDegree_lt_coeff_mul (add_lt_add_right hm _)
    -- 🎉 no goals
  · rw [coeff_eq_zero_of_natDegree_lt hn, mul_zero]
    -- ⊢ coeff (p * q) (m + n) = 0
    exact natDegree_lt_coeff_mul (add_lt_add hm hn)
    -- 🎉 no goals
#align polynomial.coeff_mul_of_nat_degree_le Polynomial.coeff_mul_of_natDegree_le

theorem coeff_pow_of_natDegree_le (pn : p.natDegree ≤ n) :
    (p ^ m).coeff (m * n) = p.coeff n ^ m := by
  induction' m with m hm
  -- ⊢ coeff (p ^ Nat.zero) (Nat.zero * n) = coeff p n ^ Nat.zero
  · simp
    -- 🎉 no goals
  · rw [pow_succ', pow_succ', ← hm, Nat.succ_mul, coeff_mul_of_natDegree_le _ pn]
    -- ⊢ natDegree (p ^ m) ≤ m * n
    refine' natDegree_pow_le.trans (le_trans _ (le_refl _))
    -- ⊢ m * natDegree p ≤ m * n
    exact mul_le_mul_of_nonneg_left pn m.zero_le
    -- 🎉 no goals
#align polynomial.coeff_pow_of_nat_degree_le Polynomial.coeff_pow_of_natDegree_le

theorem coeff_pow_eq_ite_of_natDegree_le_of_le {o : ℕ}
    (pn : natDegree p ≤ n) (mno : m * n ≤ o) :
    coeff (p ^ m) o = if o = m * n then (coeff p n) ^ m else 0 := by
  rcases eq_or_ne o (m * n) with rfl | h
  -- ⊢ coeff (p ^ m) (m * n) = if m * n = m * n then coeff p n ^ m else 0
  · simpa only [ite_true] using coeff_pow_of_natDegree_le pn
    -- 🎉 no goals
  · simpa only [h, ite_false] using coeff_eq_zero_of_natDegree_lt $
      lt_of_le_of_lt (natDegree_pow_le_of_le m pn) (lt_of_le_of_ne mno h.symm)

theorem coeff_add_eq_left_of_lt (qn : q.natDegree < n) : (p + q).coeff n = p.coeff n :=
  (coeff_add _ _ _).trans <|
    (congr_arg _ <| coeff_eq_zero_of_natDegree_lt <| qn).trans <| add_zero _
#align polynomial.coeff_add_eq_left_of_lt Polynomial.coeff_add_eq_left_of_lt

theorem coeff_add_eq_right_of_lt (pn : p.natDegree < n) : (p + q).coeff n = q.coeff n := by
  rw [add_comm]
  -- ⊢ coeff (q + p) n = coeff q n
  exact coeff_add_eq_left_of_lt pn
  -- 🎉 no goals
#align polynomial.coeff_add_eq_right_of_lt Polynomial.coeff_add_eq_right_of_lt

theorem degree_sum_eq_of_disjoint (f : S → R[X]) (s : Finset S)
    (h : Set.Pairwise { i | i ∈ s ∧ f i ≠ 0 } (Ne on degree ∘ f)) :
    degree (s.sum f) = s.sup fun i => degree (f i) := by
  induction' s using Finset.induction_on with x s hx IH
  -- ⊢ degree (Finset.sum ∅ f) = sup ∅ fun i => degree (f i)
  · simp
    -- 🎉 no goals
  · simp only [hx, Finset.sum_insert, not_false_iff, Finset.sup_insert]
    -- ⊢ degree (f x + Finset.sum s fun x => f x) = degree (f x) ⊔ sup s fun i => deg …
    specialize IH (h.mono fun _ => by simp (config := { contextual := true }))
    -- ⊢ degree (f x + Finset.sum s fun x => f x) = degree (f x) ⊔ sup s fun i => deg …
    rcases lt_trichotomy (degree (f x)) (degree (s.sum f)) with (H | H | H)
    · rw [← IH, sup_eq_right.mpr H.le, degree_add_eq_right_of_degree_lt H]
      -- 🎉 no goals
    · rcases s.eq_empty_or_nonempty with (rfl | hs)
      -- ⊢ degree (f x + Finset.sum ∅ fun x => f x) = degree (f x) ⊔ sup ∅ fun i => deg …
      · simp
        -- 🎉 no goals
      obtain ⟨y, hy, hy'⟩ := Finset.exists_mem_eq_sup s hs fun i => degree (f i)
      -- ⊢ degree (f x + Finset.sum s fun x => f x) = degree (f x) ⊔ sup s fun i => deg …
      rw [IH, hy'] at H
      -- ⊢ degree (f x + Finset.sum s fun x => f x) = degree (f x) ⊔ sup s fun i => deg …
      by_cases hx0 : f x = 0
      -- ⊢ degree (f x + Finset.sum s fun x => f x) = degree (f x) ⊔ sup s fun i => deg …
      · simp [hx0, IH]
        -- 🎉 no goals
      have hy0 : f y ≠ 0 := by
        contrapose! H
        simpa [H, degree_eq_bot] using hx0
      refine' absurd H (h _ _ fun H => hx _)
      · simp [hx0]
        -- 🎉 no goals
      · simp [hy, hy0]
        -- 🎉 no goals
      · exact H.symm ▸ hy
        -- 🎉 no goals
    · rw [← IH, sup_eq_left.mpr H.le, degree_add_eq_left_of_degree_lt H]
      -- 🎉 no goals
#align polynomial.degree_sum_eq_of_disjoint Polynomial.degree_sum_eq_of_disjoint

theorem natDegree_sum_eq_of_disjoint (f : S → R[X]) (s : Finset S)
    (h : Set.Pairwise { i | i ∈ s ∧ f i ≠ 0 } (Ne on natDegree ∘ f)) :
    natDegree (s.sum f) = s.sup fun i => natDegree (f i) := by
  by_cases H : ∃ x ∈ s, f x ≠ 0
  -- ⊢ natDegree (Finset.sum s f) = sup s fun i => natDegree (f i)
  · obtain ⟨x, hx, hx'⟩ := H
    -- ⊢ natDegree (Finset.sum s f) = sup s fun i => natDegree (f i)
    have hs : s.Nonempty := ⟨x, hx⟩
    -- ⊢ natDegree (Finset.sum s f) = sup s fun i => natDegree (f i)
    refine' natDegree_eq_of_degree_eq_some _
    -- ⊢ degree (Finset.sum s f) = ↑(sup s fun i => natDegree (f i))
    rw [degree_sum_eq_of_disjoint]
    -- ⊢ (sup s fun i => degree (f i)) = ↑(sup s fun i => natDegree (f i))
    · rw [← Finset.sup'_eq_sup hs, ← Finset.sup'_eq_sup hs,
        Nat.cast_withBot, Finset.coe_sup' hs, ←
        Finset.sup'_eq_sup hs]
      refine' le_antisymm _ _
      -- ⊢ (sup' s hs fun i => degree (f i)) ≤ sup' s hs (WithBot.some ∘ fun i => natDe …
      · rw [Finset.sup'_le_iff]
        -- ⊢ ∀ (b : S), b ∈ s → degree (f b) ≤ sup' s hs (WithBot.some ∘ fun i => natDegr …
        intro b hb
        -- ⊢ degree (f b) ≤ sup' s hs (WithBot.some ∘ fun i => natDegree (f i))
        by_cases hb' : f b = 0
        -- ⊢ degree (f b) ≤ sup' s hs (WithBot.some ∘ fun i => natDegree (f i))
        · simpa [hb'] using hs
          -- 🎉 no goals
        rw [degree_eq_natDegree hb', Nat.cast_withBot]
        -- ⊢ ↑(natDegree (f b)) ≤ sup' s hs (WithBot.some ∘ fun i => natDegree (f i))
        exact Finset.le_sup' (fun i : S => (natDegree (f i) : WithBot ℕ)) hb
        -- 🎉 no goals
      · rw [Finset.sup'_le_iff]
        -- ⊢ ∀ (b : S), b ∈ s → (WithBot.some ∘ fun i => natDegree (f i)) b ≤ sup' s hs f …
        intro b hb
        -- ⊢ (WithBot.some ∘ fun i => natDegree (f i)) b ≤ sup' s hs fun i => degree (f i)
        simp only [Finset.le_sup'_iff, exists_prop, Function.comp_apply]
        -- ⊢ ∃ b_1, b_1 ∈ s ∧ ↑(natDegree (f b)) ≤ degree (f b_1)
        by_cases hb' : f b = 0
        -- ⊢ ∃ b_1, b_1 ∈ s ∧ ↑(natDegree (f b)) ≤ degree (f b_1)
        · refine' ⟨x, hx, _⟩
          -- ⊢ ↑(natDegree (f b)) ≤ degree (f x)
          contrapose! hx'
          -- ⊢ f x = 0
          simpa [← Nat.cast_withBot, hb', degree_eq_bot] using hx'
          -- 🎉 no goals
        exact ⟨b, hb, (degree_eq_natDegree hb').ge⟩
        -- 🎉 no goals
    · exact h.imp fun x y hxy hxy' => hxy (natDegree_eq_of_degree_eq hxy')
      -- 🎉 no goals
  · push_neg at H
    -- ⊢ natDegree (Finset.sum s f) = sup s fun i => natDegree (f i)
    rw [Finset.sum_eq_zero H, natDegree_zero, eq_comm, show 0 = ⊥ from rfl, Finset.sup_eq_bot_iff]
    -- ⊢ ∀ (s_1 : S), s_1 ∈ s → natDegree (f s_1) = ⊥
    intro x hx
    -- ⊢ natDegree (f x) = ⊥
    simp [H x hx]
    -- 🎉 no goals
#align polynomial.nat_degree_sum_eq_of_disjoint Polynomial.natDegree_sum_eq_of_disjoint

set_option linter.deprecated false in
theorem natDegree_bit0 (a : R[X]) : (bit0 a).natDegree ≤ a.natDegree :=
  (natDegree_add_le _ _).trans (max_self _).le
#align polynomial.nat_degree_bit0 Polynomial.natDegree_bit0

set_option linter.deprecated false in
theorem natDegree_bit1 (a : R[X]) : (bit1 a).natDegree ≤ a.natDegree :=
  (natDegree_add_le _ _).trans (by simp [natDegree_bit0])
                                   -- 🎉 no goals
#align polynomial.nat_degree_bit1 Polynomial.natDegree_bit1

variable [Semiring S]

theorem natDegree_pos_of_eval₂_root {p : R[X]} (hp : p ≠ 0) (f : R →+* S) {z : S}
    (hz : eval₂ f z p = 0) (inj : ∀ x : R, f x = 0 → x = 0) : 0 < natDegree p :=
  lt_of_not_ge fun hlt => by
    have A : p = C (p.coeff 0) := eq_C_of_natDegree_le_zero hlt
    -- ⊢ False
    rw [A, eval₂_C] at hz
    -- ⊢ False
    simp only [inj (p.coeff 0) hz, RingHom.map_zero] at A
    -- ⊢ False
    exact hp A
    -- 🎉 no goals
#align polynomial.nat_degree_pos_of_eval₂_root Polynomial.natDegree_pos_of_eval₂_root

theorem degree_pos_of_eval₂_root {p : R[X]} (hp : p ≠ 0) (f : R →+* S) {z : S}
    (hz : eval₂ f z p = 0) (inj : ∀ x : R, f x = 0 → x = 0) : 0 < degree p :=
  natDegree_pos_iff_degree_pos.mp (natDegree_pos_of_eval₂_root hp f hz inj)
#align polynomial.degree_pos_of_eval₂_root Polynomial.degree_pos_of_eval₂_root

@[simp]
theorem coe_lt_degree {p : R[X]} {n : ℕ} : (n : WithBot ℕ) < degree p ↔ n < natDegree p := by
  by_cases h : p = 0
  -- ⊢ ↑n < degree p ↔ n < natDegree p
  · simp [h]
    -- 🎉 no goals
  simp [degree_eq_natDegree h, Nat.cast_withBot, WithBot.coe_lt_coe]
  -- 🎉 no goals
#align polynomial.coe_lt_degree Polynomial.coe_lt_degree

end Degree

end Semiring

section Ring

variable [Ring R] {p q : R[X]}

theorem natDegree_sub : (p - q).natDegree = (q - p).natDegree := by rw [← natDegree_neg, neg_sub]
                                                                    -- 🎉 no goals
#align polynomial.nat_degree_sub Polynomial.natDegree_sub

theorem natDegree_sub_le_iff_left (qn : q.natDegree ≤ n) :
    (p - q).natDegree ≤ n ↔ p.natDegree ≤ n := by
  rw [← natDegree_neg] at qn
  -- ⊢ natDegree (p - q) ≤ n ↔ natDegree p ≤ n
  rw [sub_eq_add_neg, natDegree_add_le_iff_left _ _ qn]
  -- 🎉 no goals
#align polynomial.nat_degree_sub_le_iff_left Polynomial.natDegree_sub_le_iff_left

theorem natDegree_sub_le_iff_right (pn : p.natDegree ≤ n) :
    (p - q).natDegree ≤ n ↔ q.natDegree ≤ n := by rwa [natDegree_sub, natDegree_sub_le_iff_left]
                                                  -- 🎉 no goals
#align polynomial.nat_degree_sub_le_iff_right Polynomial.natDegree_sub_le_iff_right

theorem coeff_sub_eq_left_of_lt (dg : q.natDegree < n) : (p - q).coeff n = p.coeff n := by
  rw [← natDegree_neg] at dg
  -- ⊢ coeff (p - q) n = coeff p n
  rw [sub_eq_add_neg, coeff_add_eq_left_of_lt dg]
  -- 🎉 no goals
#align polynomial.coeff_sub_eq_left_of_lt Polynomial.coeff_sub_eq_left_of_lt

theorem coeff_sub_eq_neg_right_of_lt (df : p.natDegree < n) : (p - q).coeff n = -q.coeff n := by
  rwa [sub_eq_add_neg, coeff_add_eq_right_of_lt, coeff_neg]
  -- 🎉 no goals
#align polynomial.coeff_sub_eq_neg_right_of_lt Polynomial.coeff_sub_eq_neg_right_of_lt

end Ring

section NoZeroDivisors

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

theorem degree_mul_C (a0 : a ≠ 0) : (p * C a).degree = p.degree := by
  rw [degree_mul, degree_C a0, add_zero]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.degree_mul_C Polynomial.degree_mul_C

theorem degree_C_mul (a0 : a ≠ 0) : (C a * p).degree = p.degree := by
  rw [degree_mul, degree_C a0, zero_add]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.degree_C_mul Polynomial.degree_C_mul

theorem natDegree_mul_C (a0 : a ≠ 0) : (p * C a).natDegree = p.natDegree := by
  simp only [natDegree, degree_mul_C a0]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.natDegree_mul_C Polynomial.natDegree_mul_C

theorem natDegree_C_mul (a0 : a ≠ 0) : (C a * p).natDegree = p.natDegree := by
  simp only [natDegree, degree_C_mul a0]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.nat_degree_C_mul Polynomial.natDegree_C_mul

theorem natDegree_comp : natDegree (p.comp q) = natDegree p * natDegree q := by
  by_cases q0 : q.natDegree = 0
  -- ⊢ natDegree (comp p q) = natDegree p * natDegree q
  · rw [degree_le_zero_iff.mp (natDegree_eq_zero_iff_degree_le_zero.mp q0), comp_C, natDegree_C,
      natDegree_C, mul_zero]
  · by_cases p0 : p = 0
    -- ⊢ natDegree (comp p q) = natDegree p * natDegree q
    · simp only [p0, zero_comp, natDegree_zero, zero_mul]
      -- 🎉 no goals
    refine' le_antisymm natDegree_comp_le (le_natDegree_of_ne_zero _)
    -- ⊢ coeff (comp p q) (natDegree p * natDegree q) ≠ 0
    simp only [coeff_comp_degree_mul_degree q0, p0, mul_eq_zero, leadingCoeff_eq_zero, or_self_iff,
      ne_zero_of_natDegree_gt (Nat.pos_of_ne_zero q0), pow_ne_zero, Ne.def, not_false_iff]
#align polynomial.nat_degree_comp Polynomial.natDegree_comp

@[simp]
theorem natDegree_iterate_comp (k : ℕ) :
    (p.comp^[k] q).natDegree = p.natDegree ^ k * q.natDegree := by
  induction' k with k IH
  -- ⊢ natDegree ((comp p)^[Nat.zero] q) = natDegree p ^ Nat.zero * natDegree q
  · simp
    -- 🎉 no goals
  · rw [Function.iterate_succ_apply', natDegree_comp, IH, pow_succ, mul_assoc]
    -- 🎉 no goals
#align polynomial.nat_degree_iterate_comp Polynomial.natDegree_iterate_comp

theorem leadingCoeff_comp (hq : natDegree q ≠ 0) :
    leadingCoeff (p.comp q) = leadingCoeff p * leadingCoeff q ^ natDegree p := by
  rw [← coeff_comp_degree_mul_degree hq, ← natDegree_comp, coeff_natDegree]
  -- 🎉 no goals
#align polynomial.leading_coeff_comp Polynomial.leadingCoeff_comp

end NoZeroDivisors

end Polynomial
