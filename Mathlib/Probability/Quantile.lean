/-
Copyright (c) 2026 Gabriel Anton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Anton
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Probability.CDF
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.MonotoneContinuity

/-!
# The lower quantile function of a real cdf-like function

The *lower quantile function* of `F : ℝ → ℝ` at level `p` is the infimum of the set of
points at which `F` has reached `p`. For the cdf of a probability measure it is the
generalized inverse.

## Main definitions

* `ProbabilityTheory.quantileSet F p`: the set `{x | p ≤ F x}`.
* `ProbabilityTheory.lowerQuantile F p`: the infimum of `quantileSet F p`.

## Main statements



## Implementation notes

`sInf` of a set that is empty or unbounded below returns the junk value `0`. A lemma
stated without `Set.Nonempty` and `BddBelow` hypotheses is therefore either false or
accidentally true of the junk value, and a reader cannot tell which. Every general lemma
carries those two hypotheses by name.

`quantileSet F p` is definitionally `F ⁻¹' Set.Ici p`.

`Mathlib/Order/SemiconjSup.lean` defines `IsOrderRightAdjoint`, built by
`isOrderRightAdjoint_csSup` as a supremum over a *sub*-level set. That is the order-dual
construction, the *upper* generalized inverse; neither definition unfolds to the other.

Everything is stated for `F : ℝ → ℝ`. The order core generalizes to a
`ConditionallyCompleteLinearOrder` domain; see the generality register.

## Tags

quantile, generalized inverse, cumulative distribution function, cdf, Galois connection
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- The set of points at which `F` has reached the level `p`. For a cdf `F` this is the
set of candidate `p`-quantiles. -/
def quantileSet (F : ℝ → ℝ) (p : ℝ) : Set ℝ := {x : ℝ | p ≤ F x}

/-- The lower quantile function, that is the generalized inverse of `F`: the infimum of
the points at which `F` has reached the level `p`.

When `quantileSet F p` is empty or is not bounded below, `sInf` returns the junk value `0`
and this definition carries no information. Every lemma below that says anything about
this value assumes `Set.Nonempty (quantileSet F p)` and `BddBelow (quantileSet F p)` by
name. -/
noncomputable def lowerQuantile (F : ℝ → ℝ) (p : ℝ) : ℝ :=
  sInf (quantileSet F p)

theorem quantileSet_def (F : ℝ → ℝ) (p : ℝ) :
    quantileSet F p = {x : ℝ | p ≤ F x} := rfl

theorem lowerQuantile_def (F : ℝ → ℝ) (p : ℝ) :
    lowerQuantile F p = sInf (quantileSet F p) := rfl

/-- One half of the Galois connection, and the half that needs nothing but boundedness:
if `F` has reached `p` at `x` then the quantile is at or below `x`. -/
theorem lowerQuantile_le_of_le (F : ℝ → ℝ) (p x : ℝ)
    (hbd : BddBelow (quantileSet F p)) (hx : p ≤ F x) :
    lowerQuantile F p ≤ x :=
  csInf_le hbd hx

/-- If `x` is below every point at which `F` has reached `p`, then `x` is at or below the
quantile. -/
theorem le_lowerQuantile (F : ℝ → ℝ) (p x : ℝ)
    (hne : Set.Nonempty (quantileSet F p))
    (hlb : ∀ y : ℝ, p ≤ F y → x ≤ y) :
    x ≤ lowerQuantile F p :=
  le_csInf hne hlb

/-- The lower quantile is the least point at which `F` has reached `p`, whenever such a
least point exists. Both side conditions follow from the two hypotheses, so this form
needs neither stated separately. -/
theorem lowerQuantile_eq (F : ℝ → ℝ) (p x : ℝ)
    (hx : p ≤ F x) (hlb : ∀ y : ℝ, p ≤ F y → x ≤ y) :
    lowerQuantile F p = x := by
  have hne : Set.Nonempty (quantileSet F p) := Exists.intro x hx
  have hbd : BddBelow (quantileSet F p) := Exists.intro x hlb
  exact le_antisymm (csInf_le hbd hx) (le_csInf hne hlb)

/-- Monotonicity in the level. The asymmetry in the hypotheses is not an accident: the
lower level needs boundedness, since its set is the larger one, and the upper level needs
nonemptiness, since its set is the smaller one. -/
theorem lowerQuantile_mono (F : ℝ → ℝ) (p q : ℝ) (hpq : p ≤ q)
    (hbd : BddBelow (quantileSet F p)) (hne : Set.Nonempty (quantileSet F q)) :
    lowerQuantile F p ≤ lowerQuantile F q :=
  csInf_le_csInf hbd hne (fun _ hx => le_trans hpq hx)

/-- Below the quantile, `F` has not yet reached `p`. Needs boundedness only. -/
theorem apply_lt_of_lt_lowerQuantile (F : ℝ → ℝ) (p x : ℝ)
    (hbd : BddBelow (quantileSet F p)) (hx : x < lowerQuantile F p) :
    F x < p :=
  not_le.mp (fun hc => absurd (csInf_le hbd hc) (not_le.mpr hx))

/-- If `F` is monotone and is strictly below `p` somewhere, the quantile set is bounded
below by that point. -/
theorem bddBelow_quantileSet_of_lt (F : ℝ → ℝ) (p a : ℝ)
    (hF : Monotone F) (ha : F a < p) :
    BddBelow (quantileSet F p) := by
  refine Exists.intro a ?_
  intro y hy
  rcases le_or_gt a y with h | h
  · exact h
  · exact absurd hy (not_le.mpr (lt_of_le_of_lt (hF (le_of_lt h)) ha))

/-- The converse, which does not need monotonicity. Together with the previous lemma this
says that, for monotone `F`, `BddBelow (quantileSet F p)` holds exactly when `p` exceeds
some value of `F`; the direction proved here holds for any `F`. -/
theorem exists_apply_lt_of_bddBelow (F : ℝ → ℝ) (p : ℝ)
    (hbd : BddBelow (quantileSet F p)) :
    ∃ a : ℝ, F a < p := by
  cases hbd with
  | intro b hb =>
    refine Exists.intro (b - 1) ?_
    rcases lt_or_ge (F (b - 1)) p with h | h
    · exact h
    · exact absurd (hb h) (by linarith)

theorem quantileSet_id (p : ℝ) :
    quantileSet (fun x : ℝ => x) p = Set.Ici p := rfl

theorem lowerQuantile_id (p : ℝ) : lowerQuantile (fun x : ℝ => x) p = p := by
  rw [lowerQuantile_def, quantileSet_id, csInf_Ici]

end ProbabilityTheory
