/-
Copyright (c) 2023 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
import Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries
import Mathlib.Data.Nat.Parity

/-!
# Convergence of integer continued fractions

This file proves that integer continued fractions are cauchy sequences and converge to a
real number.
-/

universe u v

open Nat

namespace GeneralizedContinuedFraction

variable {K : Type u} [LinearOrderedField K]

theorem convergents_sub_convergents_succ
    {g : GeneralizedContinuedFraction K} [g.IsContinuedFraction] {n : ℕ}
    (hg : ¬g.TerminatedAt n) :
    convergents g n - convergents g (n + 1) =
      (-1) ^ (n + 1) * (denominators g n)⁻¹ * (denominators g (n + 1))⁻¹ := by
  have hdn1 := _root_.ne_of_gt (g.zero_lt_denom (n + 1))
  have hdn := _root_.ne_of_gt (g.zero_lt_denom n)
  apply mul_left_injective₀ hdn1
  apply mul_left_injective₀ hdn
  simp only [convergents]
  convert g.determinant hg using 1 <;> field_simp <;> ring

theorem convergents_lt_convergents_succ_of_even
    {g : GeneralizedContinuedFraction K} [g.IsIntegerContinuedFraction] {n : ℕ} (hne : Even n)
    (hg : ¬g.TerminatedAt n) : convergents g n < convergents g (n + 1) := by
  rw [← sub_neg, convergents_sub_convergents_succ hg]
  apply mul_neg_of_neg_of_pos
  · apply mul_neg_of_neg_of_pos
    · rw [(hne.add_odd odd_one).neg_one_pow]; exact neg_one_lt_zero
    · rw [inv_pos]; exact zero_lt_denom n
  · rw [inv_pos]; exact zero_lt_denom (n + 1)

theorem convergents_succ_lt_convergents_of_odd
    {g : GeneralizedContinuedFraction K} [g.IsIntegerContinuedFraction] {n : ℕ} (hno : Odd n)
    (hg : ¬g.TerminatedAt n) : convergents g (n + 1) < convergents g n := by
  rw [← sub_pos, convergents_sub_convergents_succ hg]
  apply mul_pos
  · apply mul_pos
    · rw [(hno.add_odd odd_one).neg_one_pow]; exact zero_lt_one
    · rw [inv_pos]; exact zero_lt_denom n
  · rw [inv_pos]; exact zero_lt_denom (n + 1)

theorem convergents_sub_convergents_add_two
    {g : GeneralizedContinuedFraction K} [g.IsContinuedFraction] {n : ℕ}
    (hg : ¬g.TerminatedAt (n + 1)) :
    convergents g n - convergents g (n + 2) =
      (-1) ^ (n + 1) * (denominators g (n + 1))⁻¹ *
        ((denominators g n)⁻¹ - (denominators g (n + 2))⁻¹) :=
  have hg' : ¬g.TerminatedAt n := mt (terminated_stable (le_of_lt n.lt_succ_self)) hg
  calc
    convergents g n - convergents g (n + 2)
      = (convergents g n - convergents g (n + 1)) +
          (convergents g (n + 1) - convergents g (n + 2)) := by ring
    _ = (-1) ^ (n + 1) * (denominators g n)⁻¹ * (denominators g (n + 1))⁻¹ +
          (-1) ^ (n + 2) * (denominators g (n + 1))⁻¹ * (denominators g (n + 2))⁻¹ :=
      congr_arg₂ (· + ·)
        (convergents_sub_convergents_succ hg') (convergents_sub_convergents_succ hg)
    _ = (-1) ^ (n + 1) * (denominators g (n + 1))⁻¹ *
          ((denominators g n)⁻¹ - (denominators g (n + 2))⁻¹) := by ring

theorem lt_of_succ_succ_get?_continuantsAux_b
    {g : GeneralizedContinuedFraction K} [g.IsContinuedFraction] {n : ℕ} {b : K} (hn : 1 ≤ n)
    (nth_partDenom_eq : g.partialDenominators.get? n = some b) :
    b * (g.continuantsAux (n + 1)).b < (g.continuantsAux (n + 2)).b := by
  obtain ⟨gp_n, nth_s_eq, rfl⟩ : ∃ gp_n, g.s.get? n = some gp_n ∧ gp_n.b = b
  exact exists_s_b_of_partDenom nth_partDenom_eq
  simp [IsSimpleContinuedFraction.partNum_eq_one (partNum_eq_s_a nth_s_eq),
    continuantsAux_recurrence nth_s_eq rfl rfl]
  exact g.zero_lt_continuantsAux_b hn

/-- Shows that `bₙ * Bₙ < Bₙ₊₁`, where `bₙ` is the `n`th partial denominator and `Bₙ₊₁` and `Bₙ` are
the `n + 1`th and `n`th denominator of the continued fraction, and `1 ≤ n`. -/
theorem lt_of_succ_get?_denom
    {g : GeneralizedContinuedFraction K} [g.IsContinuedFraction] {n : ℕ} {b : K} (hn : 1 ≤ n)
    (nth_partDenom_eq : g.partialDenominators.get? n = some b) :
    b * g.denominators n < g.denominators (n + 1) := by
  rw [denom_eq_conts_b, nth_cont_eq_succ_nth_contAux]
  exact lt_of_succ_succ_get?_continuantsAux_b hn nth_partDenom_eq

theorem denom_lt_denom_succ_of_one_le
    {g : GeneralizedContinuedFraction K} [g.IsIntegerContinuedFraction] {n : ℕ} (hn : 1 ≤ n)
    (not_terminatedAt_n : ¬g.TerminatedAt n) :
    g.denominators n < g.denominators (n + 1) := by
  obtain ⟨cp, hcp⟩ : ∃ cp, g.s.get? n = some cp :=
    Option.ne_none_iff_exists'.mp not_terminatedAt_n
  have hcpb : 1 ≤ cp.b := by
    rcases IsIntegerContinuedFraction.partDenom_eq_int (partDenom_eq_s_b hcp)
      with ⟨m, hm⟩
    have hgpb := IsContinuedFraction.zero_lt_partDenom (partDenom_eq_s_b hcp)
    rw [hm] at hgpb ⊢; norm_cast0 at hgpb ⊢; rwa [← Int.sub_one_lt_iff, Int.sub_self]
  have hd := lt_of_succ_get?_denom hn (partDenom_eq_s_b hcp)
  nlinarith only [hcpb, hd, g.zero_lt_denom n]

theorem denom_lt_denom_add_two
    {g : GeneralizedContinuedFraction K} [g.IsIntegerContinuedFraction] {n : ℕ}
    (hg : ¬g.TerminatedAt (n + 1)) :
    g.denominators n < g.denominators (n + 2) :=
  calc
    g.denominators n ≤ g.denominators (n + 1) := denom_mono
    _                < g.denominators (n + 2) :=
      denom_lt_denom_succ_of_one_le (by linarith only) hg

theorem convergents_lt_convergents_add_two_of_even
    {g : GeneralizedContinuedFraction K} [g.IsIntegerContinuedFraction] {n : ℕ} (hne : Even n)
    (hg : ¬g.TerminatedAt (n + 1)) : convergents g n < convergents g (n + 2) := by
  rw [← sub_neg, convergents_sub_convergents_add_two hg]
  apply mul_neg_of_neg_of_pos
  · apply mul_neg_of_neg_of_pos
    · rw [(hne.add_odd odd_one).neg_one_pow]; exact neg_one_lt_zero
    · rw [inv_pos]; exact zero_lt_denom (n + 1)
  · rw [sub_pos]; exact inv_lt_inv_of_lt (zero_lt_denom n) (denom_lt_denom_add_two hg)

theorem convergents_add_two_lt_convergents_of_odd
    {g : GeneralizedContinuedFraction K} [g.IsIntegerContinuedFraction] {n : ℕ} (hno : Odd n)
    (hg : ¬g.TerminatedAt (n + 1)) : convergents g (n + 2) < convergents g n := by
  rw [← sub_pos, convergents_sub_convergents_add_two hg]
  apply mul_pos
  · apply mul_pos
    · rw [(hno.add_odd odd_one).neg_one_pow]; exact zero_lt_one
    · rw [inv_pos]; exact zero_lt_denom (n + 1)
  · rw [sub_pos]; exact inv_lt_inv_of_lt (zero_lt_denom n) (denom_lt_denom_add_two hg)

theorem convergents_lt_convergents_of_even
    {g : GeneralizedContinuedFraction K} [g.IsIntegerContinuedFraction]
    {m n : ℕ} (hg : ¬g.TerminatedAt (n - 1)) (hme : Even m) (hmn : m < n) :
    g.convergents m < g.convergents n := by
  replace hmn := exists_eq_add_of_lt hmn; rcases hmn with ⟨k, rfl⟩
  rw [Nat.add_sub_cancel] at hg
  wlog hk : Odd k generalizing k hg
  · rw [← even_iff_not_odd, even_iff_exists_two_mul] at hk; rcases hk with ⟨k', rfl⟩
    apply lt_of_le_of_lt (b := g.convergents (m + 2 * k'))
    · cases k' using Nat.casesAuxOn with
      | zero     => rfl
      | succ k'' =>
        simp only [mul_add, mul_one, ← add_assoc] at hg ⊢
        have hg' : ¬g.TerminatedAt (m + 2 * k'' + 1) :=
          mt (terminated_stable ((m + 2 * k'' + 1).le_add_right 1)) hg
        exact le_of_lt (this (2 * k'' + 1) hg' (odd_two_mul_add_one k''))
    · exact convergents_lt_convergents_succ_of_even (hme.add (even_two_mul k')) hg
  rcases hk with ⟨k', rfl⟩
  simp only [← add_assoc] at hg ⊢
  induction k' using Nat.recAuxOn with
  | zero        => exact convergents_lt_convergents_add_two_of_even hme hg
  | succ k'' ih =>
    simp only [mul_add, mul_one, ← add_assoc] at hg ⊢
    trans g.convergents (m + 2 * k'' + 2)
    · exact ih (mt (terminated_stable ((m + 2 * k'' + 1).le_add_right 2)) hg)
    · exact convergents_lt_convergents_add_two_of_even
        ((hme.add (even_two_mul k'')).add even_two) hg

theorem convergents_lt_convergents_of_odd
    {g : GeneralizedContinuedFraction K} [g.IsIntegerContinuedFraction]
    {m n : ℕ} (hg : ¬g.TerminatedAt (n - 1)) (hmo : Odd m) (hmn : m < n) :
    g.convergents n < g.convergents m := by
  replace hmn := exists_eq_add_of_lt hmn; rcases hmn with ⟨k, rfl⟩
  rw [Nat.add_sub_cancel] at hg
  wlog hk : Odd k generalizing k hg
  · rw [← even_iff_not_odd, even_iff_exists_two_mul] at hk; rcases hk with ⟨k', rfl⟩
    apply lt_of_lt_of_le (b := g.convergents (m + 2 * k'))
    · exact convergents_succ_lt_convergents_of_odd (hmo.add_even (even_two_mul k')) hg
    · cases k' using Nat.casesAuxOn with
      | zero     => rfl
      | succ k'' =>
        simp only [mul_add, mul_one, ← add_assoc] at hg ⊢
        have hg' : ¬g.TerminatedAt (m + 2 * k'' + 1) :=
          mt (terminated_stable ((m + 2 * k'' + 1).le_add_right 1)) hg
        exact le_of_lt (this (2 * k'' + 1) hg' (odd_two_mul_add_one k''))
  rcases hk with ⟨k', rfl⟩
  simp only [← add_assoc] at hg ⊢
  induction k' using Nat.recAuxOn with
  | zero        => exact convergents_add_two_lt_convergents_of_odd hmo hg
  | succ k'' ih =>
    simp only [mul_add, mul_one, ← add_assoc] at hg ⊢
    trans g.convergents (m + 2 * k'' + 2)
    · exact convergents_add_two_lt_convergents_of_odd
        ((hmo.add_even (even_two_mul k'')).add_even even_two) hg
    · exact ih (mt (terminated_stable ((m + 2 * k'' + 1).le_add_right 2)) hg)

theorem convergents_le_convergents_of_even
    {g : GeneralizedContinuedFraction K} [g.IsIntegerContinuedFraction]
    {m n : ℕ} (hme : Even m) (hmn : m ≤ n) : g.convergents m ≤ g.convergents n := by
  rw [le_iff_eq_or_lt] at hmn; rcases hmn with rfl | hmn
  · rfl
  · by_cases hg : g.TerminatedAt (n - 1)
    · by_cases hg' : g.TerminatedAt m
      · exact ge_of_eq (convergents_stable_of_terminated (le_of_lt hmn) hg')
      · have het : ∃ l, g.TerminatedAt l := ⟨n - 1, hg⟩
        trans g.convergents (Nat.find het)
        · have hmf : m < Nat.find het :=
            lt_of_not_le (fun hfm => hg' (terminated_stable hfm (Nat.find_spec het)))
          have hg'' : ¬g.TerminatedAt (Nat.find het - 1) :=
            Nat.find_min het (Nat.sub_lt (Nat.zero_lt_of_lt hmf) Nat.zero_lt_one)
          exact le_of_lt (convergents_lt_convergents_of_even hg'' hme hmf)
        · exact ge_of_eq (convergents_stable_of_terminated
            (le_trans (Nat.find_min' het hg) (Nat.sub_le n 1)) (Nat.find_spec het))
    · exact le_of_lt (convergents_lt_convergents_of_even hg hme hmn)

theorem convergents_le_convergents_of_odd
    {g : GeneralizedContinuedFraction K} [g.IsIntegerContinuedFraction]
    {m n : ℕ} (hme : Odd m) (hmn : m ≤ n) : g.convergents n ≤ g.convergents m := by
  rw [le_iff_eq_or_lt] at hmn; rcases hmn with rfl | hmn
  · rfl
  · by_cases hg : g.TerminatedAt (n - 1)
    · by_cases hg' : g.TerminatedAt m
      · exact le_of_eq (convergents_stable_of_terminated (le_of_lt hmn) hg')
      · have het : ∃ l, g.TerminatedAt l := ⟨n - 1, hg⟩
        trans g.convergents (Nat.find het)
        · exact le_of_eq (convergents_stable_of_terminated
            (le_trans (Nat.find_min' het hg) (Nat.sub_le n 1)) (Nat.find_spec het))
        · have hmf : m < Nat.find het :=
            lt_of_not_le (fun hfm => hg' (terminated_stable hfm (Nat.find_spec het)))
          have hg'' : ¬g.TerminatedAt (Nat.find het - 1) :=
            Nat.find_min het (Nat.sub_lt (Nat.zero_lt_of_lt hmf) Nat.zero_lt_one)
          exact le_of_lt (convergents_lt_convergents_of_odd hg'' hme hmf)
    · exact le_of_lt (convergents_lt_convergents_of_odd hg hme hmn)

theorem cauchySeq'_convergents [Archimedean K]
    {g : GeneralizedContinuedFraction K} [g.IsIntegerContinuedFraction] :
    ∀ ε > (0 : K), ∃ N : ℕ, ∀ᵉ (m ≥ N) (n ≥ N), |g.convergents m - g.convergents n| < ε := by
  intro ε hε
  rcases exists_nat_gt ε⁻¹ with ⟨N', hN'⟩
  let N := max N' 5
  exists N + 1
  intro m hm n hn
  apply lt_of_le_of_lt (b := |g.convergents N - g.convergents (N + 1)|)
  · rw [← max_sub_min_eq_abs, ← max_sub_min_eq_abs]
    apply And.elim sub_le_sub
    cases N.even_or_odd with
    | inl heN =>
      rw [max_eq_left (convergents_le_convergents_of_even (g := g) heN (N.le_add_right 1)),
        min_eq_right (convergents_le_convergents_of_even (g := g) heN (N.le_add_right 1)),
        max_le_iff, le_min_iff]
      exact
        ⟨⟨convergents_le_convergents_of_odd (heN.add_odd odd_one) hn,
          convergents_le_convergents_of_odd (heN.add_odd odd_one) hm⟩,
          ⟨convergents_le_convergents_of_even heN (le_trans (N.le_add_right 1) hn),
            convergents_le_convergents_of_even heN (le_trans (N.le_add_right 1) hm)⟩⟩
    | inr hoN =>
      rw [max_eq_right (convergents_le_convergents_of_odd (g := g) hoN (N.le_add_right 1)),
        min_eq_left (convergents_le_convergents_of_odd (g := g) hoN (N.le_add_right 1)),
        max_le_iff, le_min_iff]
      exact
        ⟨⟨convergents_le_convergents_of_odd hoN (le_trans (N.le_add_right 1) hn),
          convergents_le_convergents_of_odd hoN (le_trans (N.le_add_right 1) hm)⟩,
          ⟨convergents_le_convergents_of_even (hoN.add_odd odd_one) hn,
            convergents_le_convergents_of_even (hoN.add_odd odd_one) hm⟩⟩
  · by_cases hg : g.TerminatedAt N
    · rwa [← convergents_stable_of_terminated (N.le_add_right 1) hg, sub_self, abs_zero]
    · rw [convergents_sub_convergents_succ hg, abs_mul, abs_mul, abs_neg_one_pow, one_mul,
        abs_of_pos (inv_pos_of_pos (zero_lt_denom N)),
        abs_of_pos (inv_pos_of_pos (zero_lt_denom (N + 1))), ← mul_inv,
        inv_lt (mul_pos (zero_lt_denom N) (zero_lt_denom (N + 1))) hε]
      calc
        ε⁻¹ < (N' : K) := hN'
        _   ≤ ↑N := by exact_mod_cast le_max_left N' 5
        _   ≤ ↑(Nat.fib N) := by exact_mod_cast le_fib_self (le_max_right N' 5)
        _   ≤ ↑(Nat.fib (N + 1)) := by exact_mod_cast fib_le_fib_succ
        _   ≤ ↑(Nat.fib (N + 1)) * ↑(Nat.fib (N + 1)) := by exact_mod_cast (fib (N + 1)).le_mul_self
        _   ≤ ↑(Nat.fib (N + 1)) * ↑(Nat.fib (N + 2)) :=
          mul_le_mul_of_nonneg_left
            (by exact_mod_cast fib_le_fib_succ) (by exact_mod_cast (fib (N + 1)).zero_le)
        _   ≤ g.denominators N * g.denominators (N + 1) :=
          mul_le_mul
            (succ_nth_fib_le_of_nth_denom (Or.inr (mt (terminated_stable N.pred_le) hg)))
            (succ_nth_fib_le_of_nth_denom (Or.inr hg))
            (by exact_mod_cast (fib (N + 2)).zero_le)
            zero_le_denom


end GeneralizedContinuedFraction
