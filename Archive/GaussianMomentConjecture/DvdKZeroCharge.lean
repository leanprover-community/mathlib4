/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.ConstantTermRelations
import Archive.GaussianMomentConjecture.DvdKInterface
import Archive.GaussianMomentConjecture.DvdKUniqueChannel
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NormNum

/-!
# `DvdK1` for supports containing a zero charge

`ChargesStraddleZero` is `(∃ i, q i = 0) ∨ (both signs present)`.  This module discharges the
**first disjunct** unconditionally and elementarily: if some charge is zero, then at `m = 1` the
single composition supported at that index is the *unique* balanced channel, so the constant term is
`c i₀ ≠ 0`.  Consequently the general one-variable Duistermaat–van der Kallen input `DvdK1` only has
to be established on the second disjunct (both signs, no zero charge).
-/

namespace GMC2.DvdKZeroCharge

open GMC2.ConstantTermRelations

/-- A `ℕ`-valued function on a fintype summing to `1` is a single unit mass. -/
theorem eq_single_of_sum_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι → ℕ) (h : ∑ i, r i = 1) (j : ι) (hj : r j ≠ 0) :
    ∀ i, r i = if i = j then 1 else 0 := by
  have hle : r j ≤ 1 := h ▸ Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
  have hrj : r j = 1 := le_antisymm hle (Nat.one_le_iff_ne_zero.mpr hj)
  have hrest : ∑ i ∈ Finset.univ.erase j, r i = 0 := by
    have hadd : r j + ∑ i ∈ Finset.univ.erase j, r i = 1 := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ j)]; exact h
    omega
  intro i
  by_cases hi : i = j
  · subst hi; simp [hrj]
  · have hmem : i ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
    have : r i = 0 := (Finset.sum_eq_zero_iff.mp hrest) i hmem
    simp [hi, this]

/-- **`DvdK1` when a zero charge is present.** If `q i₀ = 0` (with `q` injective, `c` nonvanishing),
then `[z⁰] f¹ = c i₀ ≠ 0`; formally, the constant-term relation is nonzero at `m = 1`. -/
theorem dvdK1_of_zero_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℤ) (c : ι → ℂ) (hq : Function.Injective q) (hc : ∀ i, c i ≠ 0)
    (i0 : ι) (hi0 : q i0 = 0) :
    ∃ m : ℕ, 1 ≤ m ∧ MvPolynomial.aeval c (constantTermRelation q m) ≠ 0 := by
  classical
  refine ⟨1, le_refl 1, ?_⟩
  set r0 : ι → ℕ := fun i => if i = i0 then 1 else 0 with hr0def
  have hr0mem : r0 ∈ Finset.piAntidiag (Finset.univ : Finset ι) 1 := by
    rw [Finset.mem_piAntidiag]
    exact ⟨by simp [hr0def, Finset.sum_ite_eq'], fun i _ => Finset.mem_univ i⟩
  have hbal : totalCharge q r0 = 0 := by
    unfold totalCharge
    rw [Finset.sum_eq_single i0]
    · simp [hr0def, hi0]
    · intro b _ hb; simp [hr0def, hb]
    · intro h; exact absurd (Finset.mem_univ i0) h
  have huniq : ∀ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) 1,
      totalCharge q r = 0 → r = r0 := by
    intro r hr hrbal
    rw [Finset.mem_piAntidiag] at hr
    obtain ⟨hsum, _⟩ := hr
    -- `r` is a single unit mass at some `j`; balancedness forces `q j = 0`, hence `j = i0`.
    have hne : ∃ j, r j ≠ 0 := by
      have hsne : ∑ i, r i ≠ 0 := by rw [hsum]; norm_num
      obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsne
      exact ⟨j, hj⟩
    obtain ⟨j, hj⟩ := hne
    have hrj : ∀ i, r i = if i = j then 1 else 0 := eq_single_of_sum_eq_one r hsum j hj
    have hqj : q j = 0 := by
      have : totalCharge q r = q j := by
        unfold totalCharge
        rw [Finset.sum_eq_single j]
        · simp [hrj]
        · intro b _ hb; simp [hrj, hb]
        · intro h; exact absurd (Finset.mem_univ j) h
      rw [this] at hrbal; exact hrbal
    have hji0 : j = i0 := hq (by rw [hqj, hi0])
    funext i
    rw [hrj i, hr0def, hji0]
  exact GMC2.DvdKUniqueChannel.ct_ne_zero_of_unique_balanced q c hc 1 r0 hr0mem hbal huniq

/-- The one-variable DvdK input, restricted to the **both-signs (no-zero) case**: a strictly
negative and a strictly positive charge are present. -/
def DvdK1BothSigns : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (q : ι → ℤ) (c : ι → ℂ),
    Function.Injective q → (∀ i, c i ≠ 0) →
    (∃ i, q i < 0) → (∃ j, 0 < q j) →
    ∃ m : ℕ, 1 ≤ m ∧
      MvPolynomial.aeval c (GMC2.ConstantTermRelations.constantTermRelation q m) ≠ 0

/-- **Reduction of `DvdK1` to the both-signs case.** Since `ChargesStraddleZero` is
`(a zero charge) ∨ (both signs)` and the zero-charge disjunct is elementary (`dvdK1_of_zero_mem`),
the full one-variable Duistermaat–van der Kallen input follows from its both-signs restriction. This
isolates the genuinely hard case handled by the Galois orbit-product route (the orbit-product
argument). -/
theorem dvdK1_of_bothSigns (h : DvdK1BothSigns) : GMC2.DvdKInterface.DvdK1 := by
  intro ι _ _ q c hq hc hstraddle
  rcases hstraddle with ⟨i0, _, hi0⟩ | ⟨⟨i, _, hi⟩, ⟨j, _, hj⟩⟩
  · have h0 : ((q i0 : ℤ) : ℚ) = 0 := hi0
    exact dvdK1_of_zero_mem q c hq hc i0 (by exact_mod_cast h0)
  · have hin : ((q i : ℤ) : ℚ) < 0 := hi
    have hjp : (0 : ℚ) < ((q j : ℤ) : ℚ) := hj
    exact h ι q c hq hc ⟨i, by exact_mod_cast hin⟩ ⟨j, by exact_mod_cast hjp⟩

/-- **Rescaling invariance.** The constant-term relation depends on the charges only through which
compositions are balanced, so it is unchanged when all charges are rescaled by a nonzero common
factor `g` (`q₁ = g·q₂`). Hence `DvdK1` for `q₁` and for `q₂` coincide — the hard case may assume
the charges have gcd `1`. -/
theorem constantTermRelation_scale {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q1 q2 : ι → ℤ) (g : ℤ) (hg : g ≠ 0) (hscale : ∀ i, q1 i = g * q2 i) (m : ℕ) :
    constantTermRelation q1 m = constantTermRelation q2 m := by
  unfold constantTermRelation
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have hchg : totalCharge q1 r = g * totalCharge q2 r := by
    unfold totalCharge
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [hscale i]; ring)
  by_cases hbal : totalCharge q2 r = 0
  · rw [if_pos hbal, if_pos (by rw [hchg, hbal, mul_zero])]
  · rw [if_neg hbal, if_neg (by rw [hchg]; exact mul_ne_zero hg hbal)]

end GMC2.DvdKZeroCharge

