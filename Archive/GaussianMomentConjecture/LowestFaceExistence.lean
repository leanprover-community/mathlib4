/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Existence of a rational lowest balanced face in one charge dimension

For a finite rational point set `(q i, a i)`, assume that the charges contain
zero or contain values of both signs.  This file constructs a rational affine
functional `a - λ q` which is minimized on a face whose charges still contain
zero or values of both signs.

This is the finite, one-dimensional linear-programming input used by the
lowest-balanced-face argument for `the lowest-balanced-face theorem`.  The proof is elementary: the
possible height at charge zero is attained either by a neutral point or by the
intersection of the segment joining a negative and a positive point.  We take
the least of those finitely many rational heights and construct a supporting
slope.

No convex-analysis or real-closure interface is hidden here.  In particular,
the theorem starts with rational heights and charges and returns rational
`λ` and `δ`.
-/

open Finset

namespace GMC2.LowestFaceExistence

variable {ι : Type*}

/-- Indices with zero, negative, or positive charge. -/
def neutral (S : Finset ι) (q : ι → ℚ) : Finset ι :=
  S.filter fun i => q i = 0

def negative (S : Finset ι) (q : ι → ℚ) : Finset ι :=
  S.filter fun i => q i < 0

def positive (S : Finset ι) (q : ι → ℚ) : Finset ι :=
  S.filter fun i => 0 < q i

/-- Height at charge zero of the segment joining `i` to `j`. -/
def pairHeight (a q : ι → ℚ) (i j : ι) : ℚ :=
  (q j * a i - q i * a j) / (q j - q i)

/-- The finite list of all rational heights at charge zero contributed by a
neutral point or by a negative-positive pair. -/
def balancedHeights (S : Finset ι) (a q : ι → ℚ) : Finset ℚ :=
  (neutral S q).image a ∪
    ((negative S q).product (positive S q)).image
      (fun ij => pairHeight a q ij.1 ij.2)

/-- A one-dimensional finite charge set contains zero in its convex hull,
expressed without importing a convex-hull API. -/
def ChargesStraddleZero (S : Finset ι) (q : ι → ℚ) : Prop :=
  (∃ i ∈ S, q i = 0) ∨
    ((∃ i ∈ S, q i < 0) ∧ ∃ j ∈ S, 0 < q j)

lemma pairHeight_ge_iff_slope_le
    (a q : ι → ℚ) (δ : ℚ) {i j : ι}
    (hi : q i < 0) (hj : 0 < q j) :
    δ ≤ pairHeight a q i j ↔
      (a i - δ) / q i ≤ (a j - δ) / q j := by
  have hqi : q i ≠ 0 := ne_of_lt hi
  have hqj : q j ≠ 0 := ne_of_gt hj
  have hden : 0 < q j - q i := sub_pos.mpr (hi.trans hj)
  constructor
  · intro h
    have hmul : δ * (q j - q i) ≤ q j * a i - q i * a j := by
      exact (le_div_iff₀ hden).mp h
    have hcross : q i * (a j - δ) ≤ (a i - δ) * q j := by
      nlinarith only [hmul]
    apply (div_le_iff_of_neg hi).2
    have : q i * (a j - δ) / q j ≤ a i - δ :=
      (div_le_iff₀ hj).2 (by simpa [mul_comm] using hcross)
    calc
      (a j - δ) / q j * q i = q i * (a j - δ) / q j := by ring
      _ ≤ a i - δ := this
  · intro h
    have hstep : (a j - δ) / q j * q i ≤ a i - δ :=
      (div_le_iff_of_neg hi).1 h
    have hstep' : q i * (a j - δ) / q j ≤ a i - δ := by
      calc
        q i * (a j - δ) / q j = (a j - δ) / q j * q i := by ring
        _ ≤ a i - δ := hstep
    have hcross : q i * (a j - δ) ≤ (a i - δ) * q j :=
      (div_le_iff₀ hj).1 hstep'
    apply (le_div_iff₀ hden).2
    nlinarith only [hcross]

lemma pairHeight_eq_iff_slope_eq
    (a q : ι → ℚ) (δ : ℚ) {i j : ι}
    (hi : q i < 0) (hj : 0 < q j) :
    pairHeight a q i j = δ ↔
      (a i - δ) / q i = (a j - δ) / q j := by
  constructor
  · intro h
    have hqi : q i ≠ 0 := ne_of_lt hi
    have hqj : q j ≠ 0 := ne_of_gt hj
    have hden : q j - q i ≠ 0 := ne_of_gt (sub_pos.mpr (hi.trans hj))
    have hnum : q j * a i - q i * a j = δ * (q j - q i) := by
      exact (div_eq_iff hden).mp h
    apply (div_eq_div_iff hqi hqj).2
    linear_combination hnum
  · intro h
    have hqi : q i ≠ 0 := ne_of_lt hi
    have hqj : q j ≠ 0 := ne_of_gt hj
    have hden : q j - q i ≠ 0 := ne_of_gt (sub_pos.mpr (hi.trans hj))
    have hcross : (a i - δ) * q j = (a j - δ) * q i :=
      (div_eq_div_iff hqi hqj).1 h
    apply (div_eq_iff hden).2
    linear_combination hcross

lemma balancedHeights_nonempty
    (S : Finset ι) (a q : ι → ℚ)
    (h : ChargesStraddleZero S q) : (balancedHeights S a q).Nonempty := by
  rcases h with ⟨i, hiS, hqi⟩ | ⟨⟨i, hiS, hqi⟩, ⟨j, hjS, hqj⟩⟩
  · refine ⟨a i, ?_⟩
    apply Finset.mem_union_left
    exact Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨hiS, hqi⟩, rfl⟩
  · refine ⟨pairHeight a q i j, ?_⟩
    apply Finset.mem_union_right
    exact Finset.mem_image.2
      ⟨(i, j), Finset.mem_product.2
        ⟨Finset.mem_filter.2 ⟨hiS, hqi⟩,
          Finset.mem_filter.2 ⟨hjS, hqj⟩⟩, rfl⟩

/-- **Rational lowest-balanced-face existence.**

If the charges of a finite rational support straddle zero, there are rational
`λ` and `δ` such that `a i - λ q i ≥ δ` on the whole support and the equality
face itself still straddles zero.  The final disjunction gives explicit face
witnesses: either a neutral equality point, or one negative and one positive
equality point.

This is stronger than merely producing a minimizer: it produces the rational
supporting functional needed to define the Laurent face, while retaining a
balanced address on that face. -/
theorem exists_rational_lowest_balanced_face
    (S : Finset ι) (a q : ι → ℚ)
    (hstraddle : ChargesStraddleZero S q) :
    ∃ lambda delta : ℚ,
      (∀ i ∈ S, delta ≤ a i - lambda * q i) ∧
      ((∃ i ∈ S, q i = 0 ∧ a i - lambda * q i = delta) ∨
        ∃ i ∈ S, ∃ j ∈ S,
          q i < 0 ∧ 0 < q j ∧
          a i - lambda * q i = delta ∧ a j - lambda * q j = delta) := by
  let H := balancedHeights S a q
  have hH : H.Nonempty := balancedHeights_nonempty S a q hstraddle
  let δ : ℚ := H.min' hH
  have hδmem : δ ∈ H := H.min'_mem hH
  have hδle : ∀ x ∈ H, δ ≤ x := fun x hx => H.min'_le x hx
  have hneutral : ∀ i ∈ S, q i = 0 → δ ≤ a i := by
    intro i hiS hqi
    apply hδle (a i)
    apply Finset.mem_union_left
    exact Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨hiS, hqi⟩, rfl⟩
  have hpairs : ∀ i ∈ S, q i < 0 → ∀ j ∈ S, 0 < q j →
      δ ≤ pairHeight a q i j := by
    intro i hiS hqi j hjS hqj
    apply hδle (pairHeight a q i j)
    apply Finset.mem_union_right
    exact Finset.mem_image.2
      ⟨(i, j), Finset.mem_product.2
        ⟨Finset.mem_filter.2 ⟨hiS, hqi⟩,
          Finset.mem_filter.2 ⟨hjS, hqj⟩⟩, rfl⟩
  rcases Finset.mem_union.1 hδmem with hδneutral | hδpair
  · rcases Finset.mem_image.1 hδneutral with ⟨z, hz, haz⟩
    have hz' := Finset.mem_filter.1 hz
    by_cases hneg : (negative S q).Nonempty
    · have hnegImage :
          ((negative S q).image (fun i => (a i - δ) / q i)).Nonempty :=
        Finset.image_nonempty.2 hneg
      let lambda : ℚ := ((negative S q).image (fun i => (a i - δ) / q i)).max'
          hnegImage
      have hlowerNeg : ∀ i ∈ S, q i < 0 → (a i - δ) / q i ≤ lambda := by
        intro i hiS hqi
        apply Finset.le_max'
        exact Finset.mem_image.2
          ⟨i, Finset.mem_filter.2 ⟨hiS, hqi⟩, rfl⟩
      refine ⟨lambda, δ, ?_, Or.inl ?_⟩
      · intro i hiS
        rcases lt_trichotomy (q i) 0 with hqi | hqi | hqi
        · have hslope := hlowerNeg i hiS hqi
          have hmul := (div_le_iff_of_neg hqi).mp hslope
          dsimp [lambda] at hmul ⊢
          linarith
        · have hzero : q i = 0 := hqi
          simpa [hzero] using hneutral i hiS hzero
        · have hmaxmem := Finset.max'_mem
            ((negative S q).image (fun k => (a k - δ) / q k)) hnegImage
          rcases Finset.mem_image.1 hmaxmem with ⟨k, hk, hkLambda⟩
          have hk' := Finset.mem_filter.1 hk
          have hkCross : (a k - δ) / q k ≤ (a i - δ) / q i :=
            (pairHeight_ge_iff_slope_le a q δ hk'.2 hqi).mp
              (hpairs k hk'.1 hk'.2 i hiS hqi)
          have hlambda : lambda = (a k - δ) / q k := by
            dsimp [lambda]
            exact hkLambda.symm
          have : lambda ≤ (a i - δ) / q i := hlambda.trans_le hkCross
          have hmul := (le_div_iff₀ hqi).mp this
          linarith
      · refine ⟨z, hz'.1, hz'.2, ?_⟩
        rw [hz'.2, mul_zero, sub_zero]
        exact haz
    · by_cases hpos : (positive S q).Nonempty
      · have hposImage :
            ((positive S q).image (fun i => (a i - δ) / q i)).Nonempty :=
          Finset.image_nonempty.2 hpos
        let lambda : ℚ := ((positive S q).image (fun i => (a i - δ) / q i)).min'
            hposImage
        have hupperPos : ∀ i ∈ S, 0 < q i → lambda ≤ (a i - δ) / q i := by
          intro i hiS hqi
          apply Finset.min'_le
          exact Finset.mem_image.2
            ⟨i, Finset.mem_filter.2 ⟨hiS, hqi⟩, rfl⟩
        refine ⟨lambda, δ, ?_, Or.inl ?_⟩
        · intro i hiS
          rcases lt_trichotomy (q i) 0 with hqi | hqi | hqi
          · exfalso
            exact hneg ⟨i, Finset.mem_filter.2 ⟨hiS, hqi⟩⟩
          · have hzero : q i = 0 := hqi
            simpa [hzero] using hneutral i hiS hzero
          · have hmul := (le_div_iff₀ hqi).mp (hupperPos i hiS hqi)
            dsimp [lambda] at hmul ⊢
            linarith
        · refine ⟨z, hz'.1, hz'.2, ?_⟩
          rw [hz'.2, mul_zero, sub_zero]
          exact haz
      · refine ⟨0, δ, ?_, Or.inl ?_⟩
        · intro i hiS
          have hqi : q i = 0 := by
            rcases lt_trichotomy (q i) 0 with hqi | hqi | hqi
            · exact (hneg ⟨i, Finset.mem_filter.2 ⟨hiS, hqi⟩⟩).elim
            · exact hqi
            · exact (hpos ⟨i, Finset.mem_filter.2 ⟨hiS, hqi⟩⟩).elim
          simpa [hqi] using hneutral i hiS hqi
        · refine ⟨z, hz'.1, hz'.2, ?_⟩
          simpa [hz'.2] using haz
  · rcases Finset.mem_image.1 hδpair with ⟨⟨n, p⟩, hnp, hpairδ⟩
    have hn := Finset.mem_filter.1 (Finset.mem_product.1 hnp).1
    have hp := Finset.mem_filter.1 (Finset.mem_product.1 hnp).2
    let lambda : ℚ := (a n - δ) / q n
    have hslopeEq : (a n - δ) / q n = (a p - δ) / q p :=
      (pairHeight_eq_iff_slope_eq a q δ hn.2 hp.2).mp hpairδ
    refine ⟨lambda, δ, ?_, Or.inr ?_⟩
    · intro i hiS
      rcases lt_trichotomy (q i) 0 with hqi | hqi | hqi
      · have hcross : (a i - δ) / q i ≤ (a p - δ) / q p :=
          (pairHeight_ge_iff_slope_le a q δ hqi hp.2).mp
            (hpairs i hiS hqi p hp.1 hp.2)
        have hslope : (a i - δ) / q i ≤ lambda := by
          simpa [lambda, hslopeEq] using hcross
        have hmul := (div_le_iff_of_neg hqi).mp hslope
        dsimp [lambda] at hmul ⊢
        linarith
      · have hzero : q i = 0 := hqi
        simpa [hzero] using hneutral i hiS hzero
      · have hcross : (a n - δ) / q n ≤ (a i - δ) / q i :=
          (pairHeight_ge_iff_slope_le a q δ hn.2 hqi).mp
            (hpairs n hn.1 hn.2 i hiS hqi)
        have hmul := (le_div_iff₀ hqi).mp (by simpa [lambda] using hcross)
        dsimp [lambda] at hmul ⊢
        linarith
    · refine ⟨n, hn.1, p, hp.1, hn.2, hp.2, ?_, ?_⟩
      · have hqn : q n ≠ 0 := ne_of_lt hn.2
        dsimp [lambda]
        rw [div_mul_cancel₀ _ hqn]
        ring
      · have hqp : q p ≠ 0 := ne_of_gt hp.2
        have : lambda = (a p - δ) / q p := by simpa [lambda] using hslopeEq
        rw [this, div_mul_cancel₀ _ hqp]
        ring

end GMC2.LowestFaceExistence

