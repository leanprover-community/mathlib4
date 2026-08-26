/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.Reduction
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Complex.Basic

/-!
# One-dimensional charge geometry for NC2

For a finite support of integral charges, failure of strict one-sidedness has
an elementary exact form: either the support contains charge zero, or it
contains charges of both signs.  This is the one-dimensional convex-hull
bridge used when the lowest-balanced-face argument is converted back into the
`ChargeOneSided` conclusion of `NC2At`.
-/

open MvPolynomial

namespace GMC2

/-- The exact discrete witness that the charge support meets or straddles
zero.  In one dimension this is equivalent to `0` belonging to its convex
hull, without importing convex-analysis machinery. -/
def ChargeStraddlesZero (P : MvPolynomial (Fin 2) ℂ) : Prop :=
  (∃ s ∈ P.support, charge s = 0) ∨
    ((∃ s ∈ P.support, charge s < 0) ∧
      ∃ t ∈ P.support, 0 < charge t)

/-- Integral charge support is strictly one-sided exactly when it neither
meets nor crosses zero. -/
theorem chargeOneSided_iff_not_straddlesZero
    (P : MvPolynomial (Fin 2) ℂ) :
    ChargeOneSided P ↔ ¬ChargeStraddlesZero P := by
  constructor
  · intro hOne hStraddle
    rcases hOne with hpos | hneg
    · rcases hStraddle with hzero | ⟨hminus, _⟩
      · obtain ⟨s, hs, hq⟩ := hzero
        have := hpos s hs
        omega
      · obtain ⟨s, hs, hq⟩ := hminus
        have := hpos s hs
        omega
    · rcases hStraddle with hzero | ⟨_, hplus⟩
      · obtain ⟨s, hs, hq⟩ := hzero
        have := hneg s hs
        omega
      · obtain ⟨s, hs, hq⟩ := hplus
        have := hneg s hs
        omega
  · intro hNoStraddle
    by_cases hplus : ∃ t ∈ P.support, 0 < charge t
    · left
      intro s hs
      have hspos : 0 < charge s := by
        by_contra hnot
        have hsle : charge s ≤ 0 := le_of_not_gt hnot
        rcases lt_or_eq_of_le hsle with hsneg | hszero
        · exact hNoStraddle (Or.inr ⟨⟨s, hs, hsneg⟩, hplus⟩)
        · exact hNoStraddle (Or.inl ⟨s, hs, hszero⟩)
      omega
    · right
      intro s hs
      have hsle : charge s ≤ 0 := by
        by_contra hnot
        exact hplus ⟨s, hs, lt_of_not_ge hnot⟩
      have hsne : charge s ≠ 0 := by
        intro hzero
        exact hNoStraddle (Or.inl ⟨s, hs, hzero⟩)
      omega

/-- Negating the classification gives the exact obstruction form consumed by
the lowest-face argument. -/
theorem not_chargeOneSided_iff_straddlesZero
    (P : MvPolynomial (Fin 2) ℂ) :
    ¬ChargeOneSided P ↔ ChargeStraddlesZero P := by
  classical
  rw [chargeOneSided_iff_not_straddlesZero]
  constructor
  · intro hnn
    by_contra hn
    exact hnn hn
  · intro h hn
    exact hn h

/-- Compatibility form of the lowest-balanced-face theorem contrapositive: failure of strict
one-sidedness is equivalent to witnesses on both weak sides of zero. -/
theorem not_chargeOneSided_iff (P : MvPolynomial (Fin 2) ℂ) :
    ¬ChargeOneSided P ↔
      (∃ s ∈ P.support, charge s ≤ 0) ∧
        ∃ t ∈ P.support, 0 ≤ charge t := by
  unfold ChargeOneSided
  push Not
  constructor
  · rintro ⟨⟨s, hs, hs1⟩, ⟨t, ht, ht1⟩⟩
    exact ⟨⟨s, hs, by omega⟩, ⟨t, ht, by omega⟩⟩
  · rintro ⟨⟨s, hs, hs0⟩, ⟨t, ht, ht0⟩⟩
    exact ⟨⟨s, hs, by omega⟩, ⟨t, ht, by omega⟩⟩

end GMC2
