/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Finite.Polynomial

/-!
# The charge reduction: one-sided charge support implies the Mathieu–Zhao property

Two real Gaussians assemble into one complex Gaussian `Z`, and the Gaussian expectation `E` on
`ℂ[Z, W]` (with `Z = X 0` and `W = X 1`) is determined by the Wick rule
`E (Z ^ a * W ^ b) = a ! * if a = b then 1 else 0`.

The *charge* of a monomial `Z ^ a * W ^ b` is `a - b`, and `E` annihilates every monomial of
nonzero charge. The planar nullcone conjecture `NC2` asserts that a member of the nullcone of `E`
has one-sided charge support. This file proves the elementary step that turns that conclusion into
the Gaussian moment conjecture in dimension two:

  one-sided charge support ⟹ Mathieu–Zhao, i.e. `GMC(2)` for that `P`.

The argument is pure charge arithmetic: if every monomial of `P` has charge at least `1`, then for
any `Q` every monomial of `Q * P ^ m` has charge at least `m - degree_W Q`, which is positive for
large `m`, whence `E (Q * P ^ m) = 0`.
-/

open MvPolynomial Finset

namespace GMC2

/-- Charge of a monomial (exponent vector) in two variables Z = var 0, W = var 1. -/
def charge (s : Fin 2 →₀ ℕ) : ℤ := (s 0 : ℤ) - (s 1 : ℤ)

/-- Wick weight of a monomial: `a!` on the diagonal `Z^a W^a` (charge 0), else 0. -/
noncomputable def wt (s : Fin 2 →₀ ℕ) : ℂ := if s 0 = s 1 then (Nat.factorial (s 0) : ℂ) else 0

/-- The Gaussian expectation `E[Z^a W^b] = a! [a=b]`, extended linearly. -/
noncomputable def E (P : MvPolynomial (Fin 2) ℂ) : ℂ := ∑ s ∈ P.support, P.coeff s * wt s

@[simp] lemma charge_add (s t : Fin 2 →₀ ℕ) : charge (s + t) = charge s + charge t := by
  simp only [charge, Finsupp.add_apply]; push_cast; ring

/-- Charge 0 is exactly the diagonal; off-diagonal the Wick weight is 0. -/
lemma wt_of_charge_ne {s : Fin 2 →₀ ℕ} (h : charge s ≠ 0) : wt s = 0 := by
  unfold wt
  split_ifs with hh
  · exact absurd (by simp [charge, hh]) h
  · rfl

/-- If every monomial of `P` has nonzero charge, then `E P = 0`. -/
lemma E_eq_zero_of_charges_ne {P : MvPolynomial (Fin 2) ℂ}
    (h : ∀ s ∈ P.support, charge s ≠ 0) : E P = 0 := by
  unfold E
  refine Finset.sum_eq_zero (fun s hs => ?_)
  rw [wt_of_charge_ne (h s hs), mul_zero]

/-- Charges add and are bounded below on powers: if every monomial of `P` has charge `≥ 1`,
then every monomial of `P^m` has charge `≥ m`. -/
lemma le_charge_of_mem_support_pow {P : MvPolynomial (Fin 2) ℂ}
    (hP : ∀ s ∈ P.support, (1 : ℤ) ≤ charge s) :
    ∀ (m : ℕ), ∀ s ∈ (P ^ m).support, (m : ℤ) ≤ charge s := by
  intro m
  induction m with
  | zero =>
    intro s hs
    simp only [pow_zero] at hs
    have : s = 0 := by
      have := MvPolynomial.support_one (R := ℂ) (σ := Fin 2)
      rw [this] at hs; exact Finset.mem_singleton.mp hs
    simp [this, charge]
  | succ n ih =>
    intro s hs
    rw [pow_succ] at hs
    have hmem := MvPolynomial.support_mul _ _ hs
    rw [Finset.mem_add] at hmem
    obtain ⟨a, ha, b, hb, rfl⟩ := hmem
    rw [charge_add]
    have h1 := ih a ha
    have h2 := hP b hb
    push_cast
    linarith

/-- The negative-charge mirror of `le_charge_of_mem_support_pow`: if every monomial of
`P` has charge at most `-1`, every monomial of `P^m` has charge at most `-m`. -/
lemma charge_le_neg_of_mem_support_pow {P : MvPolynomial (Fin 2) ℂ}
    (hP : ∀ s ∈ P.support, charge s ≤ (-1 : ℤ)) :
    ∀ (m : ℕ), ∀ s ∈ (P ^ m).support, charge s ≤ -(m : ℤ) := by
  intro m
  induction m with
  | zero =>
    intro s hs
    simp only [pow_zero] at hs
    have : s = 0 := by
      have := MvPolynomial.support_one (R := ℂ) (σ := Fin 2)
      rw [this] at hs
      exact Finset.mem_singleton.mp hs
    simp [this, charge]
  | succ n ih =>
    intro s hs
    rw [pow_succ] at hs
    have hmem := MvPolynomial.support_mul _ _ hs
    rw [Finset.mem_add] at hmem
    obtain ⟨a, ha, b, hb, rfl⟩ := hmem
    rw [charge_add]
    have h1 := ih a ha
    have h2 := hP b hb
    push_cast
    linarith

/-- Strictly positive charge support is in the moment nullcone: every positive power has
zero Gaussian expectation. -/
theorem moments_zero_of_charge_pos (P : MvPolynomial (Fin 2) ℂ)
    (hP : ∀ s ∈ P.support, (1 : ℤ) ≤ charge s) :
    ∀ m : ℕ, 1 ≤ m → E (P ^ m) = 0 := by
  intro m hm
  apply E_eq_zero_of_charges_ne
  intro s hs hzero
  have hcharge := le_charge_of_mem_support_pow hP m s hs
  rw [hzero] at hcharge
  exact (not_le_of_gt (by exact_mod_cast hm)) hcharge

/-- Strictly negative charge support is in the moment nullcone: every positive power has
zero Gaussian expectation. -/
theorem moments_zero_of_charge_neg (P : MvPolynomial (Fin 2) ℂ)
    (hP : ∀ s ∈ P.support, charge s ≤ (-1 : ℤ)) :
    ∀ m : ℕ, 1 ≤ m → E (P ^ m) = 0 := by
  intro m hm
  apply E_eq_zero_of_charges_ne
  intro s hs hzero
  have hcharge := charge_le_neg_of_mem_support_pow hP m s hs
  rw [hzero] at hcharge
  have hmz : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  linarith

/-- **The reduction NC2 ⇒ GMC(2).** If every monomial of `P` has charge `≥ 1` (the one-sided
conclusion of the 2-D nullcone conjecture), then `ker E` is Mathieu–Zhao at `P`: for every `Q`
there is a threshold `N` beyond which `E (Q * P^m) = 0`.  Explicit threshold: `N = deg_W Q + 1`. -/
theorem mathieuZhao_of_charge_pos (P Q : MvPolynomial (Fin 2) ℂ)
    (hP : ∀ s ∈ P.support, (1 : ℤ) ≤ charge s) :
    ∃ N : ℕ, ∀ m ≥ N, E (Q * P ^ m) = 0 := by
  refine ⟨(Q.support.sup fun s => s 1) + 1, fun m hm => ?_⟩
  apply E_eq_zero_of_charges_ne
  intro s hs
  have hmem := MvPolynomial.support_mul _ _ hs
  rw [Finset.mem_add] at hmem
  obtain ⟨c, hc, b, hb, rfl⟩ := hmem
  -- charge b ≥ m (from the power), charge c ≥ -(c 1) ≥ -(sup)
  have hb2 := le_charge_of_mem_support_pow hP m b hb
  have hc1 : (c 1 : ℤ) ≤ ((Q.support.sup fun s => s 1 : ℕ) : ℤ) := by
    exact_mod_cast Finset.le_sup (f := fun s => s 1) hc
  have hcc : -(c 1 : ℤ) ≤ charge c := by
    have : (0 : ℤ) ≤ (c 0 : ℤ) := by positivity
    simp only [charge]; linarith
  have hmN : ((Q.support.sup fun s => s 1 : ℕ) : ℤ) + 1 ≤ (m : ℤ) := by exact_mod_cast hm
  -- charge (c + b) ≥ 1 > 0
  rw [charge_add]
  have : (1 : ℤ) ≤ charge c + charge b := by linarith
  linarith

/-- Negative-charge branch of the NC2-to-GMC(2) reduction. The explicit threshold is one
more than the largest `Z` exponent in `Q`. -/
theorem mathieuZhao_of_charge_neg (P Q : MvPolynomial (Fin 2) ℂ)
    (hP : ∀ s ∈ P.support, charge s ≤ (-1 : ℤ)) :
    ∃ N : ℕ, ∀ m ≥ N, E (Q * P ^ m) = 0 := by
  refine ⟨(Q.support.sup fun s => s 0) + 1, fun m hm => ?_⟩
  apply E_eq_zero_of_charges_ne
  intro s hs
  have hmem := MvPolynomial.support_mul _ _ hs
  rw [Finset.mem_add] at hmem
  obtain ⟨c, hc, b, hb, rfl⟩ := hmem
  have hb2 := charge_le_neg_of_mem_support_pow hP m b hb
  have hc0 : (c 0 : ℤ) ≤ ((Q.support.sup fun s => s 0 : ℕ) : ℤ) := by
    exact_mod_cast Finset.le_sup (f := fun s => s 0) hc
  have hcc : charge c ≤ (c 0 : ℤ) := by
    have : (0 : ℤ) ≤ (c 1 : ℤ) := by positivity
    simp only [charge]
    linarith
  have hmN : ((Q.support.sup fun s => s 0 : ℕ) : ℤ) + 1 ≤ (m : ℤ) := by
    exact_mod_cast hm
  rw [charge_add]
  have : charge c + charge b ≤ (-1 : ℤ) := by linarith
  linarith

/-- The charge-one-sided conclusion of NC2, with both orientations retained explicitly. -/
def ChargeOneSided (P : MvPolynomial (Fin 2) ℂ) : Prop :=
  (∀ s ∈ P.support, (1 : ℤ) ≤ charge s) ∨
  (∀ s ∈ P.support, charge s ≤ (-1 : ℤ))

/-- A pointwise formulation of the two-dimensional nullcone statement for one polynomial. -/
def NC2At (P : MvPolynomial (Fin 2) ℂ) : Prop :=
  (∀ m : ℕ, 1 ≤ m → E (P ^ m) = 0) → ChargeOneSided P

/-- Both strict one-sided loci are moment-null. This is the easy converse in NC2. -/
theorem moments_zero_of_charge_oneSided (P : MvPolynomial (Fin 2) ℂ)
    (hP : ChargeOneSided P) : ∀ m : ℕ, 1 ≤ m → E (P ^ m) = 0 := by
  rcases hP with hpos | hneg
  · exact moments_zero_of_charge_pos P hpos
  · exact moments_zero_of_charge_neg P hneg

/-- **NC2 implies GMC(2), formal interface.** Once null moments classify `P` as strictly
charge-one-sided, the elementary charge bounds prove eventual vanishing of `E (Q * P^m)`
for every multiplier `Q`. No tournament ordering, tie-breaker, or Paley identification enters. -/
theorem mathieuZhao_of_nc2At (P Q : MvPolynomial (Fin 2) ℂ)
    (hNC2 : NC2At P) (hnull : ∀ m : ℕ, 1 ≤ m → E (P ^ m) = 0) :
    ∃ N : ℕ, ∀ m ≥ N, E (Q * P ^ m) = 0 := by
  rcases hNC2 hnull with hpos | hneg
  · exact mathieuZhao_of_charge_pos P Q hpos
  · exact mathieuZhao_of_charge_neg P Q hneg

/-- The full two-dimensional nullcone conjecture, uniformly over all
polynomials. -/
def NC2 : Prop := ∀ P : MvPolynomial (Fin 2) ℂ, NC2At P

/-- **GMC(2) follows formally from NC2.**  All analytic and arithmetic work is
concentrated in the classification `NC2`; the charge reduction then gives
eventual Mathieu--Zhao vanishing for every multiplier. -/
theorem gmc2_of_nc2 (hNC2 : NC2) (P Q : MvPolynomial (Fin 2) ℂ)
    (hnull : ∀ m : ℕ, 1 ≤ m → E (P ^ m) = 0) :
    ∃ N : ℕ, ∀ m ≥ N, E (Q * P ^ m) = 0 :=
  mathieuZhao_of_nc2At P Q (hNC2 P) hnull

/-- Frobenius collapse of a natural-weighted finite sum.  This is the generic
whole-face identity used in normalized residue equation (15). -/
theorem sum_natCast_mul_pow_char
    {R : Type*} [CommRing R] (p : ℕ) [ExpChar R p]
    {ι : Type*} (S : Finset ι) (w : ι → ℕ) (g : ι → R) :
    (∑ s ∈ S, (w s : R) * g s) ^ p =
      ∑ s ∈ S, (w s : R) * (g s) ^ p := by
  rw [sum_pow_char]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [mul_pow, ← frobenius_def, map_natCast]

end GMC2

-- Axiom audit: should be only propext / Classical.choice / Quot.sound (Mathlib standard).
