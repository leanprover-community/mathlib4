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

* `ProbabilityTheory.lowerQuantile_le_iff`: the Galois connection.
* `ProbabilityTheory.le_apply_lowerQuantile`: attainment.
* `ProbabilityTheory.apply_lowerQuantile`: the plug-in identity.
* `ProbabilityTheory.not_forall_le_apply_lowerQuantile` and its companions:
  the right-continuity hypotheses are refuted as `¬ ∀ ...`, not merely
  motivated.

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

/-- Attainment. Under monotonicity and right continuity at the quantile, the infimum is
attained: `F` has already reached `p` at the quantile itself.

This is the only place right continuity is used. `F` is at or above `p` at every point
strictly to the right of the quantile, and right continuity transports that to the
quantile itself. Without right continuity the statement is false, which is why the
hypothesis is named rather than assumed away; see `not_forall_le_apply_lowerQuantile`.

`BddBelow (quantileSet F p)` is deliberately absent: the proof does not consume it, and a
hypothesis a proof does not use makes the statement weaker than what was proved. If the
quantile set is unbounded below the statement still holds, because `F` is then at or above
`p` everywhere. -/
theorem le_apply_lowerQuantile (F : ℝ → ℝ) (p : ℝ)
    (hF : Monotone F)
    (hne : Set.Nonempty (quantileSet F p))
    (hrc : ContinuousWithinAt F (Set.Ici (lowerQuantile F p)) (lowerQuantile F p)) :
    p ≤ F (lowerQuantile F p) := by
  have key : ∀ x : ℝ, lowerQuantile F p < x → p ≤ F x := by
    intro x hx
    cases exists_lt_of_csInf_lt hne hx with
    | intro y hy =>
      cases hy with
      | intro hyS hylt => exact le_trans hyS (hF (le_of_lt hylt))
  have hEv : Filter.Eventually (fun x : ℝ => p ≤ F x)
      (nhdsWithin (lowerQuantile F p) (Set.Ioi (lowerQuantile F p))) :=
    Filter.eventually_of_mem self_mem_nhdsWithin (fun x hx => key x hx)
  have hT : Filter.Tendsto F (nhdsWithin (lowerQuantile F p) (Set.Ioi (lowerQuantile F p)))
      (nhds (F (lowerQuantile F p))) :=
    hrc.mono Set.Ioi_subset_Ici_self
  exact ge_of_tendsto hT hEv

/-- The Galois connection, both directions, hypotheses named and minimal.

The reverse direction needs boundedness alone; the forward direction needs monotonicity,
nonemptiness and right continuity, all three through attainment. Stated as an `Iff`
because that is the form every downstream use wants. -/
theorem lowerQuantile_le_iff (F : ℝ → ℝ) (p x : ℝ)
    (hF : Monotone F)
    (hne : Set.Nonempty (quantileSet F p))
    (hbd : BddBelow (quantileSet F p))
    (hrc : ContinuousWithinAt F (Set.Ici (lowerQuantile F p)) (lowerQuantile F p)) :
    lowerQuantile F p ≤ x ↔ p ≤ F x := by
  constructor
  · intro h
    exact le_trans (le_apply_lowerQuantile F p hF hne hrc) (hF h)
  · intro h
    exact csInf_le hbd h

/-- The strict form of the Galois connection, obtained by negating both sides. It is
recorded separately because the strict form is the one that reads as "the quantile is the
first crossing point". -/
theorem lt_lowerQuantile_iff (F : ℝ → ℝ) (p x : ℝ)
    (hF : Monotone F)
    (hne : Set.Nonempty (quantileSet F p))
    (hbd : BddBelow (quantileSet F p))
    (hrc : ContinuousWithinAt F (Set.Ici (lowerQuantile F p)) (lowerQuantile F p)) :
    x < lowerQuantile F p ↔ F x < p := by
  constructor
  · intro h
    exact apply_lt_of_lt_lowerQuantile F p x hbd h
  · intro h
    exact not_le.mp
      (fun hc => absurd (le_trans (le_apply_lowerQuantile F p hF hne hrc) (hF hc))
        (not_le.mpr h))

/-- The Galois connection in the form a cdf supplies directly: a `StieltjesFunction`
carries right continuity at every point as a structure field, so this version has no side
condition to discharge at the quantile. -/
theorem lowerQuantile_le_iff_of_rightContinuous (F : ℝ → ℝ) (p x : ℝ)
    (hF : Monotone F)
    (hne : Set.Nonempty (quantileSet F p))
    (hbd : BddBelow (quantileSet F p))
    (hrc : ∀ y : ℝ, ContinuousWithinAt F (Set.Ici y) y) :
    lowerQuantile F p ≤ x ↔ p ≤ F x :=
  lowerQuantile_le_iff F p x hF hne hbd (hrc (lowerQuantile F p))

/-- Under continuity of `F` at the quantile, `F` composed with its own generalized inverse
is the identity at that level.

Both halves are used and neither is free: the lower bound is attainment, which is right
continuity, and the upper bound is the left limit, which is left continuity. At a jump of
`F` the identity fails, which is why continuity is a hypothesis here and not in the Galois
connection; see `not_forall_apply_lowerQuantile`. -/
theorem apply_lowerQuantile (F : ℝ → ℝ) (p : ℝ)
    (hF : Monotone F)
    (hne : Set.Nonempty (quantileSet F p))
    (hbd : BddBelow (quantileSet F p))
    (hc : ContinuousAt F (lowerQuantile F p)) :
    F (lowerQuantile F p) = p := by
  refine le_antisymm ?_ (le_apply_lowerQuantile F p hF hne hc.continuousWithinAt)
  have hEv : Filter.Eventually (fun x : ℝ => F x ≤ p)
      (nhdsWithin (lowerQuantile F p) (Set.Iio (lowerQuantile F p))) :=
    Filter.eventually_of_mem self_mem_nhdsWithin
      (fun x hx => le_of_lt (apply_lt_of_lt_lowerQuantile F p x hbd hx))
  have hT : Filter.Tendsto F (nhdsWithin (lowerQuantile F p) (Set.Iio (lowerQuantile F p)))
      (nhds (F (lowerQuantile F p))) := hc.continuousWithinAt
  exact le_of_tendsto hT hEv

/-- A monotone function that is not right continuous at the origin. -/
noncomputable def jumpAtZero : ℝ → ℝ := fun x : ℝ => if 0 < x then 1 else 0

theorem monotone_jumpAtZero : Monotone jumpAtZero := by
  intro a b hab
  simp only [jumpAtZero]
  split_ifs with ha hb hb
  · exact le_refl 1
  · exact absurd (lt_of_lt_of_le ha hab) hb
  · exact zero_le_one
  · exact le_refl 0

theorem jumpAtZero_zero : jumpAtZero 0 = 0 := by
  simp only [jumpAtZero]
  norm_num

theorem jumpAtZero_one : jumpAtZero 1 = 1 := by
  simp only [jumpAtZero]
  norm_num

theorem quantileSet_jumpAtZero_one : quantileSet jumpAtZero 1 = Set.Ioi 0 := by
  ext x
  simp only [quantileSet_def, Set.mem_ofPred_eq, Set.mem_Ioi, jumpAtZero]
  split_ifs with hx
  · exact Iff.intro (fun _ => hx) (fun _ => le_refl 1)
  · exact Iff.intro (fun h => absurd h (by norm_num)) (fun h => absurd h hx)

/-- The quantile of the jump function at level one is the origin, which is exactly the
point the function has not yet reached. -/
theorem lowerQuantile_jumpAtZero_one : lowerQuantile jumpAtZero 1 = 0 := by
  rw [lowerQuantile_def, quantileSet_jumpAtZero_one, csInf_Ioi]

theorem nonempty_quantileSet_jumpAtZero_one :
    Set.Nonempty (quantileSet jumpAtZero 1) :=
  Exists.intro 1 (le_of_eq jumpAtZero_one.symm)

theorem bddBelow_quantileSet_jumpAtZero_one :
    BddBelow (quantileSet jumpAtZero 1) := by
  rw [quantileSet_jumpAtZero_one]
  exact bddBelow_Ioi

/-- Attainment is false without right continuity. -/
theorem not_forall_le_apply_lowerQuantile :
    ¬ ∀ F : ℝ → ℝ, ∀ p : ℝ, Monotone F →
      Set.Nonempty (quantileSet F p) → p ≤ F (lowerQuantile F p) := by
  intro h
  have hcon := h jumpAtZero 1 monotone_jumpAtZero nonempty_quantileSet_jumpAtZero_one
  rw [lowerQuantile_jumpAtZero_one, jumpAtZero_zero] at hcon
  linarith

/-- The forward half of the Galois connection is false without right continuity. The
reverse half survives, which is why the two halves are proved separately above. -/
theorem not_forall_lowerQuantile_le_iff :
    ¬ ∀ F : ℝ → ℝ, ∀ p x : ℝ, Monotone F →
      Set.Nonempty (quantileSet F p) → BddBelow (quantileSet F p) →
      (lowerQuantile F p ≤ x ↔ p ≤ F x) := by
  intro h
  have hcon := h jumpAtZero 1 0 monotone_jumpAtZero nonempty_quantileSet_jumpAtZero_one
    bddBelow_quantileSet_jumpAtZero_one
  rw [lowerQuantile_jumpAtZero_one, jumpAtZero_zero] at hcon
  have := hcon.mp (le_refl 0)
  linarith

/-- The plug-in identity is false without continuity. -/
theorem not_forall_apply_lowerQuantile :
    ¬ ∀ F : ℝ → ℝ, ∀ p : ℝ, Monotone F →
      Set.Nonempty (quantileSet F p) → BddBelow (quantileSet F p) →
      F (lowerQuantile F p) = p := by
  intro h
  have hcon := h jumpAtZero 1 monotone_jumpAtZero nonempty_quantileSet_jumpAtZero_one
    bddBelow_quantileSet_jumpAtZero_one
  rw [lowerQuantile_jumpAtZero_one, jumpAtZero_zero] at hcon
  linarith

end ProbabilityTheory
