/-
Copyright (c) 2026 Andrew McRoberts. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew McRoberts using Ravel
-/
module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
public import Mathlib.Analysis.Polynomial.Sturm

/-!
# Certified Sturm chains from a polynomial-remainder-sequence certificate

This file bridges the exact algebraic data a Euclidean or pseudo-remainder-sequence (PRS)
computation naturally produces -- a positive-scaled recurrence at each step, a nonzero-constant
Bézout identity between `p` and its derivative, and a nonzero-constant terminal element -- to the
`IsSturmSequence` semantics consumed by `Mathlib.Analysis.Polynomial.Sturm`'s root-count theorem.

## Main definitions

* `Polynomial.CertifiedSturmChain`: exact PRS-style algebraic data sufficient to construct an
  `IsSturmSequence`.

## Main theorem

* `Polynomial.CertifiedSturmChain.count_roots_between`: Sturm's theorem instantiated directly
  from a certified exact chain.

## References

This development was produced independently from the classical mathematical sources
[eisermann2012sturm] and [pebayRojasThompson2022], without consulting Manuel Eberl's
formalisation cited by `Mathlib.Analysis.Polynomial.Sturm` or that file's own development.

* [Michael Eisermann, *The Fundamental Theorem of Algebra Made Effective: An Elementary
  Real-Algebraic Proof via Sturm Chains*][eisermann2012sturm]
* [Philippe Pébay, J. Maurice Rojas, David C. Thompson, *Sturm's Theorem with
  Endpoints*][pebayRojasThompson2022]
-/

@[expose] public section

namespace Polynomial

/-- A strictly positive scaled recurrence forces the two flank
polynomials to have opposite signs at every root of the middle one. -/
theorem positive_scaled_recurrence_sign_reversal
    {a x : ℝ} {p q r s : Polynomial ℝ}
    (ha : 0 < a)
    (hrec : C a * p = q * r - s)
    (hr : r.eval x = 0) :
    SignType.sign (s.eval x) = -SignType.sign (p.eval x) := by
  have hval := congrArg (fun t : Polynomial ℝ => t.eval x) hrec
  have hval' : a * p.eval x = -s.eval x := by
    simpa [Polynomial.eval_mul, hr] using hval
  have hs : s.eval x = -(a * p.eval x) := by
    linarith
  by_cases hp : p.eval x = 0
  · have hs0 : s.eval x = 0 := by simp [hs, hp]
    simp [hp, hs0]
  · by_cases hppos : 0 < p.eval x
    · have hap : 0 < a * p.eval x := mul_pos ha hppos
      have hsneg : s.eval x < 0 := by
        rw [hs]
        exact neg_neg_of_pos hap
      rw [sign_neg hsneg, sign_pos hppos]
    · have hpneg : p.eval x < 0 := lt_of_le_of_ne (not_lt.mp hppos) hp
      have haneg : a * p.eval x < 0 := mul_neg_of_pos_of_neg ha hpneg
      have hspos : 0 < s.eval x := by
        rw [hs]
        exact neg_pos.mpr haneg
      rw [sign_pos hspos, sign_neg hpneg]
      norm_num

/-- A Bézout identity equal to a nonzero constant rules out a common real root. -/
theorem bezout_nonzero_constant_no_common_real_root
    {p q u v : Polynomial ℝ} {c : ℝ}
    (hbez : u * p + v * q = C c)
    (hc : c ≠ 0) :
    ∀ x : ℝ, ¬(p.eval x = 0 ∧ q.eval x = 0) := by
  intro x hx
  have hval := congrArg (fun t : Polynomial ℝ => t.eval x) hbez
  have hzero : (0 : ℝ) = c := by
    simpa [Polynomial.eval_mul, hx.1, hx.2] using hval
  exact hc hzero.symm

/-- At a simple real root, `p * p'` has the sign of `x - x₀`
on a punctured neighborhood. -/
theorem simple_root_derivative_punctured_sign
    (p : Polynomial ℝ) {x0 : ℝ}
    (hp0 : p.eval x0 = 0)
    (hd0 : p.derivative.eval x0 ≠ 0) :
    ∀ᶠ x in nhdsWithin x0 {x0}ᶜ,
      SignType.sign ((p * p.derivative).eval x) =
        if x > x0 then 1 else -1 := by
  have hhd : HasDerivAt (fun x => p.eval x) (p.derivative.eval x0) x0 :=
    Polynomial.hasDerivAt p x0
  let d : ℝ := p.derivative.eval x0
  let slopeExt : ℝ → ℝ := dslope (fun x => p.eval x) x0
  have hslope : ContinuousAt slopeExt x0 :=
    continuousAt_dslope_same.mpr hhd.differentiableAt
  have hderiv : ContinuousAt (fun x : ℝ => p.derivative.eval x) x0 :=
    (Polynomial.continuous p.derivative).continuousAt
  have hprod :
      ContinuousAt (fun x => slopeExt x * p.derivative.eval x) x0 :=
    hslope.mul hderiv
  have hd : d ≠ 0 := by
    simpa [d] using hd0
  have hsq : 0 < d * d := mul_self_pos.mpr hd
  have hslope_x0 : slopeExt x0 = d := by
    simp only [slopeExt, dslope_same]
    exact hhd.deriv
  have hprod0 : 0 < slopeExt x0 * p.derivative.eval x0 := by
    rw [hslope_x0]
    exact hsq
  have hev :
      ∀ᶠ x in nhds x0, 0 < slopeExt x * p.derivative.eval x :=
    continuousAt_const.eventually_lt hprod hprod0
  have hev' :
      ∀ᶠ x in nhdsWithin x0 {x0}ᶜ,
        0 < slopeExt x * p.derivative.eval x :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hev
  have hpunct :
      ∀ᶠ x in nhdsWithin x0 {x0}ᶜ, x ∈ ({x0}ᶜ : Set ℝ) :=
    self_mem_nhdsWithin
  filter_upwards [hev', hpunct] with x hpositive hxmem
  have hx : x ≠ x0 := by
    simpa using hxmem
  have hxsub : x - x0 ≠ 0 := sub_ne_zero.mpr hx
  have hslope_x :
      slopeExt x = p.eval x / (x - x0) := by
    simp only [slopeExt, dslope_of_ne _ hx, slope_def_field, hp0, sub_zero]
  have hfactor :
      (p * p.derivative).eval x =
        (x - x0) * (slopeExt x * p.derivative.eval x) := by
    rw [Polynomial.eval_mul, hslope_x]
    field_simp [hxsub]
  rw [hfactor, sign_mul, sign_pos hpositive, mul_one]
  by_cases hgt : x > x0
  · rw [if_pos hgt, sign_pos (sub_pos.mpr hgt)]
  · have hlt : x < x0 := lt_of_le_of_ne (not_lt.mp hgt) hx
    rw [if_neg hgt, sign_neg (sub_neg.mpr hlt)]

/-- A constant terminal polynomial has point-independent sign. -/
theorem constant_terminal_sign {c x y : ℝ} :
    SignType.sign ((C c).eval x) = SignType.sign ((C c).eval y) := by
  simp

/-- Exact algebraic evidence sufficient to promote a polynomial chain
into the canonical Sturm semantics used by the root-count theorem. -/
structure CertifiedSturmChain (p : Polynomial ℝ) (ps : List (Polynomial ℝ)) : Prop where
  ne_nil : ps ≠ []
  length_ge_two : 2 ≤ ps.length
  second_mem : 1 < ps.length
  head_eq_p : ps.head ne_nil = p
  second_eq_derivative : ps[1]'second_mem = p.derivative
  recurrence :
    ∀ (i : ℕ) (hi : i + 2 < ps.length),
      ∃ (a : ℝ) (q : Polynomial ℝ),
        0 < a ∧
        C a * (ps[i]'(by omega)) =
          q * (ps[i+1]'(by omega)) - (ps[i+2]'(by omega))
  terminal_constant :
    ∃ c : ℝ, c ≠ 0 ∧ ps.getLast ne_nil = C c
  bezout :
    ∃ (u v : Polynomial ℝ) (c : ℝ),
      c ≠ 0 ∧ u * p + v * (ps[1]'second_mem) = C c

/-- Promote a typed exact PRS certificate to the semantic `IsSturmSequence`
interface consumed by the root-count theorem. -/
theorem CertifiedSturmChain.toIsSturmSequence
    {p : Polynomial ℝ} {ps : List (Polynomial ℝ)}
    (h : CertifiedSturmChain p ps) :
    IsSturmSequence p ps := by
  rcases h.terminal_constant with ⟨ct, hct, hlast⟩
  rcases h.bezout with ⟨u, v, cb, hcb, hbez⟩
  have hnoCommon :
      ∀ x : ℝ, ¬(p.eval x = 0 ∧ (ps[1]'h.second_mem).eval x = 0) :=
    bezout_nonzero_constant_no_common_real_root hbez hcb
  have hquasi : IsQuasiSturmSequence ps := by
    refine
      { ne_nil := h.ne_nil
        last_sign_const := ?_
        signs := ?_ }
    · intro x y
      rw [hlast]
      exact constant_terminal_sign
    · intro i x hi hmiddle
      rcases h.recurrence i hi with ⟨a, q, ha, hrec⟩
      exact positive_scaled_recurrence_sign_reversal ha hrec hmiddle
  refine
    { toIsQuasiSturmSequence := hquasi
      length_ge_two := h.length_ge_two
      head_eq_p := h.head_eq_p
      deriv_sign := ?_
      squarefree_pair := ?_ }
  · intro x0 hp0
    have hsecond_ne : (ps[1]'h.second_mem).eval x0 ≠ 0 := by
      intro hz
      exact hnoCommon x0 ⟨hp0, hz⟩
    have hd0 : p.derivative.eval x0 ≠ 0 := by
      rw [← h.second_eq_derivative]
      exact hsecond_ne
    have hs := simple_root_derivative_punctured_sign p hp0 hd0
    rw [← h.second_eq_derivative] at hs
    exact hs
  · intro x
    exact hnoCommon x

/-- Root-counting corollary for an exact certified PRS chain.  This is the
end-to-end semantic consumer: algebraic certificate -> `IsSturmSequence` -> Sturm root count. -/
theorem CertifiedSturmChain.count_roots_between
    {p : Polynomial ℝ} {ps : List (Polynomial ℝ)}
    (h : CertifiedSturmChain p ps) (hpne : p ≠ 0) :
    ∀ a b : ℝ, a ≤ b →
      (sturmVariations ps a : ℤ) - sturmVariations ps b =
        ({x : ℝ | a < x ∧ x ≤ b ∧ p.eval x = 0}.ncard : ℤ) := by
  exact h.toIsSturmSequence.count_roots_between hpne

end Polynomial
