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
* `ProbabilityTheory.lowerQuantile_cdf_le_iff`: the Galois connection for
  the cdf of a probability measure, with no side condition beyond `0 < p`
  and `p < 1`.
* `ProbabilityTheory.continuousWithinAt_lowerQuantile_Iic`: left continuity
  in the level.
* `ProbabilityTheory.lowerQuantile_cdf_map`: equivariance.
* `ProbabilityTheory.not_forall_le_apply_lowerQuantile` and its companions:
  the right-continuity hypotheses are refuted as `¬ ∀ ...`, not merely
  motivated.
* `ProbabilityTheory.not_galoisConnection_lowerQuantile_cdf`: the bundled
  `GaloisConnection` packaging is FALSE for every measure.

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

/-- The quantile set of a cdf is nonempty at every level strictly below one, because the
cdf tends to one at `atTop`. -/
theorem nonempty_quantileSet_cdf (μ : Measure ℝ) (p : ℝ)
    (hp : p < 1) :
    Set.Nonempty (quantileSet (cdf μ) p) := by
  have h := (tendsto_cdf_atTop μ).eventually (eventually_gt_nhds hp)
  cases h.exists with
  | intro x hx => exact Exists.intro x (le_of_lt hx)

/-- The quantile set of a cdf is bounded below at every level strictly above zero, because
the cdf tends to zero at `atBot`. -/
theorem bddBelow_quantileSet_cdf (μ : Measure ℝ) (p : ℝ)
    (hp : 0 < p) :
    BddBelow (quantileSet (cdf μ) p) := by
  have h := (tendsto_cdf_atBot μ).eventually (eventually_lt_nhds hp)
  cases h.exists with
  | intro a ha => exact bddBelow_quantileSet_of_lt (cdf μ) p a (monotone_cdf μ) ha

/-- The Galois connection for a probability measure, with no side condition beyond the
level lying strictly inside the unit interval. This is the form a user of the theory
actually wants.

The `IsProbabilityMeasure` instance is not consumed by the proof. It is kept so that this
lemma and the three like it below remain the probability-measure-facing form of the
general cdf lemmas above, whose instances were dropped where their proofs did not use
them. -/
@[nolint unusedArguments]
theorem lowerQuantile_cdf_le_iff (μ : Measure ℝ) [IsProbabilityMeasure μ] (p x : ℝ)
    (h0 : 0 < p) (h1 : p < 1) :
    lowerQuantile (cdf μ) p ≤ x ↔ p ≤ cdf μ x :=
  lowerQuantile_le_iff (cdf μ) p x (monotone_cdf μ)
    (nonempty_quantileSet_cdf μ p h1) (bddBelow_quantileSet_cdf μ p h0)
    ((cdf μ).right_continuous (lowerQuantile (cdf μ) p))

/-- Monotonicity of the quantile of a probability measure in the level, side conditions
discharged. The unconsumed instance is kept for the reason given at
`lowerQuantile_cdf_le_iff`. -/
@[nolint unusedArguments]
theorem lowerQuantile_cdf_mono (μ : Measure ℝ) [IsProbabilityMeasure μ] (p q : ℝ)
    (hpq : p ≤ q) (h0 : 0 < p) (h1 : q < 1) :
    lowerQuantile (cdf μ) p ≤ lowerQuantile (cdf μ) q :=
  lowerQuantile_mono (cdf μ) p q hpq (bddBelow_quantileSet_cdf μ p h0)
    (nonempty_quantileSet_cdf μ q h1)

/-- Attainment for the cdf of a probability measure: the cdf has reached `p` at the
`p`-quantile. Only `p < 1` is needed, inherited from the sharpened
`le_apply_lowerQuantile`. -/
@[nolint unusedArguments]
theorem le_cdf_lowerQuantile (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ)
    (h1 : p < 1) :
    p ≤ cdf μ (lowerQuantile (cdf μ) p) :=
  le_apply_lowerQuantile (cdf μ) p (monotone_cdf μ)
    (nonempty_quantileSet_cdf μ p h1)
    ((cdf μ).right_continuous (lowerQuantile (cdf μ) p))

/-- The adjunction, bundled. The lower quantile is left adjoint to `F`, for any `F` that
is monotone, right continuous, and whose quantile set is nonempty and bounded below at
every level. -/
theorem galoisConnection_lowerQuantile (F : ℝ → ℝ)
    (hF : Monotone F)
    (hrc : ∀ y : ℝ, ContinuousWithinAt F (Set.Ici y) y)
    (hne : ∀ p : ℝ, Set.Nonempty (quantileSet F p))
    (hbd : ∀ p : ℝ, BddBelow (quantileSet F p)) :
    GaloisConnection (lowerQuantile F) F :=
  fun p x => lowerQuantile_le_iff F p x hF (hne p) (hbd p) (hrc (lowerQuantile F p))

/-- The bundled hypotheses are satisfiable. The four hypotheses of
`galoisConnection_lowerQuantile` hold simultaneously for the identity, so the bundled
statement is not vacuous, and the quantile it induces is the identity, which is the sanity
check every generalized inverse has to pass. -/
theorem galoisConnection_lowerQuantile_id :
    GaloisConnection (lowerQuantile (fun x : ℝ => x)) (fun x : ℝ => x) :=
  galoisConnection_lowerQuantile (fun x : ℝ => x) (fun _ _ h => h)
    (fun _ => continuousWithinAt_id) (fun p => Exists.intro p (le_refl p))
    (fun p => Exists.intro p (fun _ hy => hy))

/-- The bundled hypotheses fail for every cdf. At level zero the quantile set of a cdf is
the whole line, because a cdf is nonnegative. -/
theorem not_forall_bddBelow_quantileSet_cdf (μ : Measure ℝ) :
    ¬ ∀ p : ℝ, BddBelow (quantileSet (cdf μ) p) := by
  intro h
  cases exists_apply_lt_of_bddBelow (cdf μ) 0 (h 0) with
  | intro a ha => exact absurd ha (not_lt.mpr (cdf_nonneg μ a))

/-- And at level two it is empty, because a cdf is at most one. -/
theorem not_forall_nonempty_quantileSet_cdf (μ : Measure ℝ) :
    ¬ ∀ p : ℝ, Set.Nonempty (quantileSet (cdf μ) p) := by
  intro h
  cases h 2 with
  | intro x hx =>
    exact absurd (le_trans hx (cdf_le_one μ x)) (by norm_num)

/-- The bundled conclusion is false for every measure, which is stronger than
saying this development's bundling lemma does not reach it.

At level two the quantile set is empty, so the quantile takes the junk value zero, so the
left side of the adjunction holds at `x = 0` while the right side would require two to be
at most a cdf value. The pointwise form is unaffected and is the form to use. -/
theorem not_galoisConnection_lowerQuantile_cdf (μ : Measure ℝ) :
    ¬ GaloisConnection (lowerQuantile (cdf μ)) (fun x : ℝ => cdf μ x) := by
  intro h
  have h2 := (h 2 (lowerQuantile (cdf μ) 2)).mp (le_refl _)
  have h1 := cdf_le_one μ (lowerQuantile (cdf μ) 2)
  linarith

/-- Left continuity, as a limit statement: the quantile function tends to its value at `p`
along levels approaching `p` from below.

The hypotheses are those of `p` alone. Nonemptiness and boundedness at the nearby lower
levels are derived inside the proof rather than assumed, which is what makes the statement
usable: a caller who can check `p` need not also check a neighbourhood. -/
theorem tendsto_lowerQuantile_nhdsLT (F : ℝ → ℝ) (p : ℝ)
    (hF : Monotone F)
    (hne : Set.Nonempty (quantileSet F p))
    (hbd : BddBelow (quantileSet F p)) :
    Filter.Tendsto (fun q : ℝ => lowerQuantile F q) (nhdsWithin p (Set.Iio p))
      (nhds (lowerQuantile F p)) := by
  cases exists_apply_lt_of_bddBelow F p hbd with
  | intro a ha =>
    have hneq : ∀ q : ℝ, q ≤ p → Set.Nonempty (quantileSet F q) := by
      intro q hq
      cases hne with
      | intro x hx => exact Exists.intro x (le_trans hq hx)
    refine tendsto_order.mpr (And.intro ?_ ?_)
    · -- levels just below `p` keep the quantile above any `c` strictly below the quantile
      intro c hc
      have hc2 : c < (c + lowerQuantile F p) / 2 := by linarith
      have hc3 : (c + lowerQuantile F p) / 2 < lowerQuantile F p := by linarith
      have hFc : F ((c + lowerQuantile F p) / 2) < p :=
        apply_lt_of_lt_lowerQuantile F p _ hbd hc3
      have h1 : Filter.Eventually
          (fun q : ℝ => F ((c + lowerQuantile F p) / 2) < q)
          (nhdsWithin p (Set.Iio p)) :=
        Filter.eventually_of_mem (nhdsWithin_le_nhds (Ioi_mem_nhds hFc)) (fun _ hq => hq)
      have h2 : Filter.Eventually (fun q : ℝ => q < p) (nhdsWithin p (Set.Iio p)) :=
        Filter.eventually_of_mem self_mem_nhdsWithin (fun _ hq => hq)
      refine Filter.Eventually.mono (h1.and h2) ?_
      intro q hq
      refine lt_of_lt_of_le hc2 ?_
      refine le_lowerQuantile F q _ (hneq q (le_of_lt hq.2)) ?_
      intro y hy
      rcases le_or_gt ((c + lowerQuantile F p) / 2) y with h | h
      · exact h
      · exact absurd hy (not_le.mpr (lt_of_le_of_lt (hF (le_of_lt h)) hq.1))
    · -- levels below `p` keep the quantile below any `c` strictly above the quantile
      intro c hc
      have h1 : Filter.Eventually (fun q : ℝ => F a < q) (nhdsWithin p (Set.Iio p)) :=
        Filter.eventually_of_mem (nhdsWithin_le_nhds (Ioi_mem_nhds ha)) (fun _ hq => hq)
      have h2 : Filter.Eventually (fun q : ℝ => q < p) (nhdsWithin p (Set.Iio p)) :=
        Filter.eventually_of_mem self_mem_nhdsWithin (fun _ hq => hq)
      refine Filter.Eventually.mono (h1.and h2) ?_
      intro q hq
      refine lt_of_le_of_lt ?_ hc
      exact lowerQuantile_mono F q p (le_of_lt hq.2)
        (bddBelow_quantileSet_of_lt F q a hF hq.1) hne

/-- Left continuity, as a continuity statement on the closed left ray. -/
theorem continuousWithinAt_lowerQuantile_Iic (F : ℝ → ℝ) (p : ℝ)
    (hF : Monotone F)
    (hne : Set.Nonempty (quantileSet F p))
    (hbd : BddBelow (quantileSet F p)) :
    ContinuousWithinAt (fun q : ℝ => lowerQuantile F q) (Set.Iic p) p := by
  rw [← Set.Iio_union_right (a := p)]
  refine continuousWithinAt_union.mpr (And.intro ?_ ?_)
  · exact tendsto_lowerQuantile_nhdsLT F p hF hne hbd
  · exact continuousWithinAt_singleton

/-- Left continuity of the quantile of a probability measure, side conditions discharged.
The unconsumed instance is kept for the reason given at `lowerQuantile_cdf_le_iff`. -/
@[nolint unusedArguments]
theorem continuousWithinAt_lowerQuantile_cdf_Iic (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (p : ℝ) (h0 : 0 < p) (h1 : p < 1) :
    ContinuousWithinAt (fun q : ℝ => lowerQuantile (cdf μ) q) (Set.Iic p) p :=
  continuousWithinAt_lowerQuantile_Iic (cdf μ) p (monotone_cdf μ)
    (nonempty_quantileSet_cdf μ p h1) (bddBelow_quantileSet_cdf μ p h0)

/-- If `F` is strictly monotone and takes the value `p` at `x`, then the quantile at level
`p` is exactly `x`. Continuity is not needed: continuity is what produces a solution, not
what makes the solution unique. -/
theorem lowerQuantile_eq_of_strictMono (F : ℝ → ℝ) (p x : ℝ)
    (hF : StrictMono F) (hx : F x = p) :
    lowerQuantile F p = x := by
  refine lowerQuantile_eq F p x (le_of_eq hx.symm) ?_
  intro y hy
  exact hF.le_iff_le.mp (le_trans (le_of_eq hx) hy)

/-- Existence and uniqueness on an interval. Under continuity and strict monotonicity on
`Set.Icc a b`, with `F` strictly below `p` at the left end and at or above `p` at the
right end, there is exactly one solution of `F x = p` in the interval, and the lower
quantile is it.

The global monotonicity hypothesis is doing real work: without it `F` could return above
`p` somewhere to the left of `a`, and the infimum would sit there instead. The strictness
of `F a < p` is likewise load bearing: at `F a = p` the quantile can escape to the left of
`a`.

`hab` is derivable from `hMono`, `hpa` and `hpb`, and is kept anyway because every
interval lemma in mathlib carries it and a reader matching this against
`intermediate_value_Icc` should not have to notice it is absent. -/
theorem exists_lowerQuantile_eq_of_monotone_of_continuousOn_of_strictMonoOn (F : ℝ → ℝ) (a b p : ℝ)
    (hab : a ≤ b)
    (hMono : Monotone F)
    (hCont : ContinuousOn F (Set.Icc a b))
    (hStrict : StrictMonoOn F (Set.Icc a b))
    (hpa : F a < p) (hpb : p ≤ F b) :
    ∃ x : ℝ, a ≤ x ∧ x ≤ b ∧ F x = p ∧ lowerQuantile F p = x ∧
      ∀ y : ℝ, a ≤ y → y ≤ b → F y = p → y = x := by
  have hmem := And.intro (le_of_lt hpa) hpb
  have hsub := intermediate_value_Icc hab hCont hmem
  cases hsub with
  | intro x hx =>
    cases hx with
    | intro hxmem hxval =>
      refine Exists.intro x (And.intro hxmem.1 (And.intro hxmem.2 (And.intro hxval ?_)))
      have hlb : ∀ y : ℝ, p ≤ F y → x ≤ y := by
        intro y hy
        rcases le_or_gt x y with h | h
        · exact h
        · rcases le_or_gt y a with hya | hya
          · exact absurd hy (not_le.mpr (lt_of_le_of_lt (hMono hya) hpa))
          · have hymem :=
              And.intro (le_of_lt hya) (le_trans (le_of_lt h) hxmem.2)
            exact absurd hy
              (not_le.mpr (lt_of_lt_of_eq (hStrict hymem hxmem h) hxval))
      refine And.intro (lowerQuantile_eq F p x (le_of_eq hxval.symm) hlb) ?_
      intro y hya hyb hyval
      exact hStrict.injOn (And.intro hya hyb) hxmem (hyval.trans hxval.symm)

/-- The quantile set transports as an image. -/
theorem quantileSet_comp_symm (F : ℝ → ℝ) (e : OrderIso ℝ ℝ) (p : ℝ) :
    quantileSet (fun y : ℝ => F (e.symm y)) p
      = Set.image (fun x : ℝ => e x) (quantileSet F p) := by
  rw [Set.image_eq_preimage_of_inverse e.symm_apply_apply e.apply_symm_apply]
  rfl

/-- Equivariance, functional form: the quantile of the transformed function is the
transform of the quantile. -/
theorem lowerQuantile_comp_symm (F : ℝ → ℝ) (e : OrderIso ℝ ℝ) (p : ℝ)
    (hne : Set.Nonempty (quantileSet F p))
    (hbd : BddBelow (quantileSet F p)) :
    lowerQuantile (fun y : ℝ => F (e.symm y)) p = e (lowerQuantile F p) := by
  rw [lowerQuantile_def, lowerQuantile_def, quantileSet_comp_symm F e p]
  exact (OrderIso.map_csInf' e hne hbd).symm

/-- The cdf of a pushforward along an order isomorphism, evaluated. -/
theorem cdf_map_orderIso (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (e : OrderIso ℝ ℝ) (y : ℝ) :
    cdf (Measure.map (fun x : ℝ => e x) μ) y = cdf μ (e.symm y) := by
  have hmeas : Measurable (fun x : ℝ => e x) := (OrderIso.continuous e).measurable
  have : IsProbabilityMeasure (Measure.map (fun x : ℝ => e x) μ) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  have hpre : Set.preimage (fun x : ℝ => e x) (Set.Iic y) = Set.Iic (e.symm y) := by
    ext z
    exact Iff.symm e.le_symm_apply
  rw [cdf_eq_real, cdf_eq_real, map_measureReal_apply hmeas measurableSet_Iic, hpre]

/-- Equivariance, measure-theoretic form: the quantile of the pushforward law is the
transform of the quantile of the original law. This is what the phrase "the quantile of a
monotone transform is the monotone transform of the quantile" actually means. -/
theorem lowerQuantile_cdf_map (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (e : OrderIso ℝ ℝ) (p : ℝ) (h0 : 0 < p) (h1 : p < 1) :
    lowerQuantile (cdf (Measure.map (fun x : ℝ => e x) μ)) p
      = e (lowerQuantile (cdf μ) p) := by
  have hfun : (fun y : ℝ => cdf (Measure.map (fun x : ℝ => e x) μ) y)
      = (fun y : ℝ => cdf μ (e.symm y)) :=
    funext (fun y => cdf_map_orderIso μ e y)
  have hstep : lowerQuantile (fun y : ℝ => cdf (Measure.map (fun x : ℝ => e x) μ) y) p
      = lowerQuantile (fun y : ℝ => cdf μ (e.symm y)) p := by rw [hfun]
  refine hstep.trans ?_
  exact lowerQuantile_comp_symm (cdf μ) e p
    (nonempty_quantileSet_cdf μ p h1) (bddBelow_quantileSet_cdf μ p h0)

end ProbabilityTheory
