/-
Copyright (c) 2025 Štěpán Holub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Štěpán Holub
-/
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Nat.Lattice

/-! # Periods of words (Lists)

This file defines the notion of a period of a word (list) and proves the Periodicity Lemma,

## Implementation notes

The definition of a period is given in terms of self-overlap.
Equivalent characterizations in terms of indices and modular arithmetic are also provided.

## Tags

periodicity lemma, Fine-Wilf theorem, period, periodicity

-/

variable {α : Type*}

open List Nat

namespace List

/--
`HasPeriod w p`, means that the list `w` has the period `p`.
The definition is given in terms of a self-overlap.
-/

def HasPeriod (w : List α) (p : ℕ) : Prop := w <+: take p w ++ w

/-- An equivalent definition of `HasPeriod w p` by indeces. -/

lemma HasPeriod_iff_getElem? (p : ℕ) (w : List α) : (HasPeriod w p) ↔
    (∀ i < w.length - p, w[i]? = w[i + p]?) := by
  apply Iff.intro
  · rw [HasPeriod]; intro pref j len
    have i1: j < w.length := by omega
    have i2: j + p < w.length := by omega
    have min: p < w.length := by omega
    have e: j + p - (take p w).length = j := by
      simp_all [min_eq_left_of_lt]
    simp_all [getElem_append_right, IsPrefix.getElem pref, min_eq_left_of_lt]
  · intro lhs; rw [HasPeriod]
    have drop: drop p w <+: w := by
      simp only [prefix_iff_getElem?, length_drop, getElem_drop]
      intro i leni
      have len : i + p < w.length := by omega
      simp_all only [getElem?_pos, add_comm p i]
    rw [← @prefix_append_right_inj α (w.drop p) w (w.take p)] at drop
    simp_all

@[simp]
lemma HasPeriod_zero (w : List α) : HasPeriod w 0 := by
  rw [HasPeriod]; simp_all

@[simp]
lemma HasPeriod_empty (p : ℕ) : HasPeriod ([] : List α) p := by
  rw [HasPeriod]; simp_all

@[simp]
lemma HasPeriod_large (w : List α) (p : ℕ) (large : w.length ≤ p) : HasPeriod w p := by
  rw [HasPeriod]; simp_all [(take_eq_self_iff w).mpr large]

lemma HasPeriod_mod (p i : ℕ) (w : List α) (per : HasPeriod w p)
    (less : i < w.length) : w[i]? = w[i % p]? := by
  by_cases p_zero: p = 0
  · have : i % p = i := by rw [p_zero, mod_zero]
    exact congrArg (getElem? w) (id (Eq.symm this))
  · cases lt_or_ge i p with
  | inl small =>
      have eq : i % p = i := by exact mod_eq_of_lt small
      rw [eq]
  | inr large =>
      have len' : i - p < w.length := by omega
      have IH: w[i - p]? = w[(i - p) % p]? := HasPeriod_mod p (i - p) w per len'
      rw [HasPeriod_iff_getElem?] at per
      have minus: i - p < w.length - p := by omega
      have per' := per (i - p) minus
      simp only [IH, large, Nat.sub_add_cancel] at per'
      have mod : i % p = (i - p) % p := by exact mod_eq_sub_mod large
      simpa [mod] using per'.symm

/-- An equivalent definition of `HasPeriod w p` by modular equivalence on indeces. -/
lemma HasPeriod_iff_mod (p : ℕ) (w : List α) : (HasPeriod w p) ↔
    (∀ i < w.length, w[i]? = w[i % p]?) := by
  apply Iff.intro
  · intro per i len
    exact HasPeriod_mod p i w per len
  · intro mod
    rw [HasPeriod_iff_getElem?]; intro i less
    have less1 : i + p < w.length := by omega
    have less2 : i < w.length := by omega
    have mod1 : w[i + p]? = w[(i + p) % p]? := mod (i + p) less1
    have mod2 : w[i]? = w[i % p]? := mod i less2
    have eq: (i + p) % p = i % p := by exact add_mod_right i p
    rw [mod1,eq, mod2]

/-- If `w` has a period `p`, then any of its factors has a period `p` as well. -/
lemma period_factor_period (u v w : List α) (p : ℕ) (per : HasPeriod (u ++ v ++ w) p) :
    HasPeriod v p := by
  suffices h : ∀ j < v.length - p, v[j]? = v[j + p]? by simpa [HasPeriod_iff_getElem?]
  intro j len
  have t: (u ++ (v ++ w))[j + u.length]? = v[j]? := by
    rw [getElem?_append_right]
    rw [Nat.add_sub_cancel]
    rw [getElem?_append_left]
    all_goals omega
  have tp: (u ++ (v ++ w))[j + u.length + p]? = v[j + p]? := by
    have eq: j + u.length + p - u.length = j + p := by omega
    rw [getElem?_append_right]
    · rw [getElem?_append_left]
      · exact congrArg (getElem? v) eq
      · omega
    · omega
  have : ∀ i < u.length + (v.length + w.length) - p,
      (u ++ (v ++ w))[i]? = (u ++ (v ++ w))[i + p]? := by
   simp_all [HasPeriod_iff_getElem?]
  refine (tp ▸(t ▸ (this (j + u.length) ?len))); omega

lemma drop_pref_of_period {w : List α} (p : ℕ) (per : HasPeriod w p) :
    drop p w <+: w := by
  rw [←(prefix_append_right_inj (take p w))]
  simp_all [HasPeriod, take_append_drop]

/-- If `w` has a period `p`, and we extend it to the left by its prefix whose length divides `p`,
then the resulting word also has a period `p`. -/
lemma extend_periods_left (p n : ℕ) (w : List α) (dvd : p ∣ n)
    (len : n ≤ w.length) (per : HasPeriod w p) : HasPeriod (take n w ++ w) p := by
  rcases Nat.eq_zero_or_pos p with rfl | p_pos
  · simp_all [HasPeriod]
  rcases Nat.eq_zero_or_pos n with rfl | pos
  · simp_all
  rw [HasPeriod_iff_mod];
  have mod_w : ∀ i < w.length, w[i]? = w[i % p]? := by
    exact fun i a => HasPeriod_mod p i w per a
  suffices h: ∀ i < n + w.length, (take n w ++ w)[i]? = (take n w ++ w)[i % p]? by simp_all
  intro i less_i
  have mod_p: ∀ j < n + length w, (take n w ++ w)[j]? = w[j % p]? := by
    intro j less_j
    if pref : j < n then
      -- indeces within `take n w` can be reduced due to the period of `w`
      exact calc
        (take n w ++ w)[j]? = (take n w)[j]? := by
          refine getElem?_append_left ?_; simp_all
        _ = w[j]? := by exact getElem?_take_of_lt pref
        _ = w[j % p]? := by refine mod_w j ?_; omega
    else
      -- larger indeces are indeces of `w` decreased by `n`
      have j_minus: j - n < w.length := by omega
      have j_mod: (j - n) % p = j % p := by
        convert_to (j - p * (n / p)) % p = j % p
        rw [Nat.mul_div_cancel' dvd]
        refine sub_mul_mod ?_
        rw [Nat.mul_div_cancel' dvd]
        simp_all
      exact calc
        (take n w ++ w)[j]? = w[j - n]? := by
          convert_to (take n w ++ w)[j]? = w[j - (take n w).length]?
          simp_all
          refine getElem?_append_right ?_; simp_all
        _ = w[(j - n) % p]? := by refine mod_w (j - n) ?_; omega
        _ = w[j % p]? := by rw [j_mod]
  have less_mod: i % p < n + w.length := by
    have : i % p < p := mod_lt i p_pos; have : p ≤ n := le_of_dvd pos dvd; omega
  rw [mod_p i less_i, mod_p (i % p) less_mod, mod_mod]


/-- Induction step for the `periodicity_lemma` -/
lemma two_periods_step {p q : ℕ} {w : List α} (per_p : HasPeriod w p) (per_q : HasPeriod w q)
    (w_len : q < w.length) (q_lt_p : q < p) : HasPeriod (drop q w) (p - q) := by
  rw [HasPeriod_iff_getElem?]; rw [HasPeriod_iff_getElem?] at per_p per_q
  simp only [length_drop, getElem?_drop]
  intro i i_lt
  exact calc
     w[q + i]? = w[i + q]? := congrArg (getElem? w) (add_comm q i)
     _         = w[i]? := by refine (per_q i ?_).symm; omega
     _         = w[i + p]? := by  refine (per_p i ?_); omega
     _         = w[q + (i + (p - q))]? := by
      apply congrArg (getElem? w); omega

/-- The Periodicity Lemma, also known as the Fine and Wilf theorem, shows that if word `w` of length
at least `p + q - gcd p q` has two periods `p` and `q`, then it has a period `gcd p q`.

The proof is similar to the Euclidean algorithm for computing `gcd`.
-/

theorem periodicity_lemma (w : List α) (p q : ℕ) (per_p : HasPeriod w p) (per_q : HasPeriod w q)
    (len : p + q - p.gcd q ≤ w.length) : HasPeriod w (p.gcd q) := by
  rcases Nat.eq_zero_or_pos p with rfl | p_pos
  · simp_all [HasPeriod]
  rcases Nat.eq_zero_or_pos q with rfl | q_pos
  · simp_all [HasPeriod]
  cases hyp: compare p q with
  | lt => -- if `p` is less than `q`, switch the two periods
      have p_lt_q := Nat.compare_eq_lt.mp hyp
      exact (gcd_comm q p ▸ periodicity_lemma w q p) per_q per_p (add_comm p q ▸ len)
  | eq => simpa [(Nat.compare_eq_eq).mp hyp]
  | gt =>
      have q_lt_p : q < p  := by exact Nat.compare_eq_gt.mp hyp
      have gcd_lt_p : p.gcd q < p := by
        refine Ne.lt_of_le ?_ (gcd_le_left q p_pos)
        simp [gcd_eq_left_iff_dvd, not_dvd_of_pos_of_lt q_pos q_lt_p]
      have : q < w.length := by omega
      have per_diff : HasPeriod (drop q w) (p - q) :=
        two_periods_step per_p per_q this q_lt_p
      have per_q' : HasPeriod (drop q w) q := by
        apply period_factor_period (take q w) (drop q w) [] q
        all_goals simp_all
      have gcd_stable : (p - q).gcd q = p.gcd q := gcd_sub_self_left (le_of_lt q_lt_p)
      have drop_len: q ≤ (drop q w).length := by
        rw [length_drop];
        have : p.gcd q ≤ p - q := by
          rw [← gcd_stable]; apply gcd_le_left q; omega
        omega
      have take_eq : take q (drop q w) = take q w := by
          let ⟨z,hz⟩ := drop_pref_of_period q per_q
          convert_to take q (drop q w) = take q (drop q w ++ z); rw [hz]
          exact (take_append_of_le_length drop_len).symm

      have IH : HasPeriod (drop q w) (gcd (p - q) q) := by
          apply periodicity_lemma (drop q w) (p - q) q
          · exact per_diff
          · exact per_q'
          · simp; omega
      convert_to HasPeriod (take q (drop q w) ++ drop q w) (p.gcd q)
      · rw [take_eq, take_append_drop q w]
      · apply extend_periods_left (p.gcd q) q (drop q w)
        · exact gcd_dvd_right p q
        · exact drop_len
        · exact (gcd_stable ▸ IH)
  termination_by (q,p)
  decreasing_by
    all_goals omega

end List
