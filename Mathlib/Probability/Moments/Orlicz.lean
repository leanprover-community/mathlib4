/-
Copyright (c) 2026 Rob Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob Sneiderman
-/
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.SubGaussian

/-!
# Orlicz norm and Orlicz spaces — Phase A scaffolding (DRAFT / RFC)

**This is a draft / RFC PR.** All theorems below are `sorry`-stubbed and
the file is *not* yet expected to compile against `master`. The purpose
of opening it now is to surface reviewer feedback on the proposed API
direction *before* proof work commits — see the
"Framing questions for reviewers" section.

The file proposes a Phase A scaffolding for Orlicz norms / Orlicz spaces
in `Mathlib.Probability.Moments`. The motivation is the gap explicitly
called out by the upstream `Mathlib.Probability.Moments.SubGaussian`
docstring:

> *TODO: implement definitions for (i)-(iv) when it makes sense. For
> example the maximal constant `K₄` such that (iv) is true is an
> Orlicz norm.*

This PR addresses that TODO and lays the foundation for sub-exponential
random variables (`ψ_1`-Orlicz) in a follow-on PR, which is the natural
companion to `SubGaussian` and required by every textbook treatment of
fast-rate concentration (Boucheron-Lugosi-Massart Ch. 2, Vershynin §2.5,
Wainwright Ch. 2).

## Three-phase plan (for reviewer context; this PR is Phase A only)

* **Phase A — this PR:** `YoungFunction`, `orliczNorm`, the `ψ_p` family,
  basic Orlicz norm properties, and the two equivalences relating
  `ψ_2`-Orlicz finiteness ↔ sub-Gaussian MGF and `ψ_1`-Orlicz finiteness
  ↔ sub-exponential MGF (the latter requires a sub-exponential predicate
  not yet upstream — see framing question 3 below).
* **Phase B — follow-on PR:** Bennett / Bernstein / Freedman tail
  inequalities reformulated in Orlicz language.
* **Phase C — later:** VC fundamental theorem with the matching lower
  bound via Fano-Le Cam-Assouad (orthogonal track).

## Main definitions (proposed)

* `ProbabilityTheory.YoungFunction`: a convex, non-decreasing function
  `ψ : ℝ≥0 → ℝ≥0` with `ψ 0 = 0`, unbounded above. Bundled as a
  structure.
* `ProbabilityTheory.YoungFunction.psi`: the `ψ_p(x) = exp(x^p) - 1`
  family. `ψ_2` characterises sub-Gaussian; `ψ_1` characterises
  sub-exponential.
* `ProbabilityTheory.orliczNorm`: the Orlicz norm
  `‖X‖_ψ := sInf { c > 0 | μ[ψ(|X|/c)] ≤ 1 }`, with the convention
  that the infimum is `⊤` when the set is empty.

## Main statements (proposed, all `sorry`)

* `orliczNorm_zero`, `orliczNorm_nonneg`, `orliczNorm_add_le`: basic
  Seminorm-style properties.
* `orliczNorm_psi2_lt_top_iff_hasSubgaussianMGF`: the bridge to the
  existing sub-Gaussian MGF API.
* `orliczNorm_psi1_lt_top_iff_hasSubexponentialMGF`: the bridge to the
  sub-exponential MGF predicate (which itself is the subject of a
  companion sketch in the author's private FormalSLT repo).

## Implementation notes (proposed)

The presentation follows Vershynin §2.5 and Boucheron-Lugosi-Massart
§4.2. The bundled `YoungFunction` structure is chosen over a typeclass
to keep the `ψ_p` family parameterisable by `p` without typeclass
juggling. Discussion under framing question 1 below.

## Framing questions for reviewers

This DRAFT PR exists to surface design feedback on three explicit
choices. The proofs are all `sorry` and the file is not expected to
compile against `master` yet. Comments specifically on framing are
welcome; please defer line-level proof critique.

1. **Bundled `YoungFunction` vs. a `IsYoungFunction` typeclass.** Current
   draft: bundled structure (as below). Alternative: typeclass over
   `ℝ≥0 → ℝ≥0`. Bundled wins for the parameterised `ψ_p` family;
   typeclass wins for composition with the existing `Lp` machinery.
   Reviewer guidance welcome.

2. **`Lᵠ` as a subspace of `Lp` vs. an independent space.** Not yet
   defined in this PR. The intended downstream presentation is `Lᵠ` as
   the subspace of `Lp 1 μ` for which `orliczNorm < ⊤`. Alternatives:
   define `Lᵠ` as its own bundled type with a coercion, or skip `Lᵠ`
   entirely in Phase A and keep only the norm.

3. **Whether to introduce `HasSubexponentialMGF` in this PR or as a
   prerequisite separate PR.** The
   `orliczNorm_psi1_lt_top_iff_hasSubexponentialMGF` statement below
   references a predicate not yet upstream. The author's preferred
   sequencing is a separate prerequisite PR for `HasSubexponentialMGF`
   that mirrors `HasSubgaussianMGF`, with this Orlicz PR rebasing onto
   it. Reviewer preference welcome.

## External context (not part of the PR)

The author's broader 12-week sprint that this PR sits within is tracked
in a private repository at
`Robby955/lean-statistical-learning`, in particular
`docs/research/FORMALSLT_DIRECTION_REVIEW_2026-05-29.md`. This is shared
for context only; the upstreamed contribution stands on its own
mathematical merit independent of the downstream learning-theory
application.

## References

* [R. Vershynin, *High-dimensional probability: An introduction with
  applications in data science*][vershynin2018high], §2.5.
* [S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities*],
  §4.2.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {m₀ : MeasurableSpace Ω}

/-- A **Young function** is a convex, non-decreasing function
`ψ : ℝ≥0 → ℝ≥0` with `ψ 0 = 0`, unbounded above. Bundled as a structure
to permit parameterised families such as `ψ_p`. -/
structure YoungFunction where
  /-- The underlying function. -/
  toFun : ℝ≥0 → ℝ≥0
  /-- `ψ 0 = 0`. -/
  zero_at_zero : toFun 0 = 0
  /-- `ψ` is monotone (which combined with `zero_at_zero` gives non-negativity). -/
  mono : Monotone toFun
  /-- `ψ` is convex when viewed as a function `ℝ → ℝ` on the non-negative reals. -/
  convex_on_nonneg :
    ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => ((toFun x.toNNReal : ℝ≥0) : ℝ))
  /-- `ψ` is unbounded above; equivalently, `ψ` is not eventually constant. -/
  unbounded : ∀ M : ℝ≥0, ∃ x : ℝ≥0, M < toFun x

namespace YoungFunction

instance : CoeFun YoungFunction (fun _ => ℝ≥0 → ℝ≥0) := ⟨toFun⟩

/-- The Young function `ψ_p(x) = exp(x^p) - 1` for `p ≥ 1`. -/
noncomputable def psi (p : ℝ) (_hp : 1 ≤ p) : YoungFunction := sorry

/-- `ψ_2` — characterises sub-Gaussian random variables. -/
noncomputable def psi2 : YoungFunction := psi 2 (by norm_num)

/-- `ψ_1` — characterises sub-exponential random variables. -/
noncomputable def psi1 : YoungFunction := psi 1 le_rfl

end YoungFunction

/-- The **Orlicz norm** of a random variable `X` with respect to a
Young function `ψ`:
`‖X‖_ψ := sInf { c > 0 | μ[ψ(|X|/c)] ≤ 1 }`,
with the convention that the infimum is `⊤` when the set is empty. -/
noncomputable def orliczNorm
    (X : Ω → ℝ) (μ : Measure Ω) (ψ : YoungFunction) : ℝ≥0∞ :=
  sorry

variable {μ : Measure Ω} (ψ : YoungFunction)

@[simp]
theorem orliczNorm_zero : orliczNorm (fun _ : Ω => (0 : ℝ)) μ ψ = 0 := sorry

theorem orliczNorm_nonneg (X : Ω → ℝ) : 0 ≤ orliczNorm X μ ψ := sorry

/-- Triangle inequality for the Orlicz norm. -/
theorem orliczNorm_add_le (X Y : Ω → ℝ) :
    orliczNorm (fun ω => X ω + Y ω) μ ψ ≤
      orliczNorm X μ ψ + orliczNorm Y μ ψ := sorry

/-- Positive homogeneity for the Orlicz norm. -/
theorem orliczNorm_smul (X : Ω → ℝ) (c : ℝ) :
    orliczNorm (fun ω => c * X ω) μ ψ =
      (ENNReal.ofReal |c|) * orliczNorm X μ ψ := sorry

/-! ## Sub-Gaussian / sub-exponential equivalences -/

/-- A random variable has finite `ψ_2`-Orlicz norm iff it has a
sub-Gaussian moment-generating function, up to a universal constant.
This is the bridge to the existing `Mathlib.Probability.Moments.SubGaussian`
API. -/
theorem orliczNorm_psi2_lt_top_iff_hasSubgaussianMGF
    [IsProbabilityMeasure μ] (X : Ω → ℝ) :
    orliczNorm X μ YoungFunction.psi2 < ⊤ ↔
      ∃ c : ℝ≥0, HasSubgaussianMGF X c μ := sorry

/-- A random variable has finite `ψ_1`-Orlicz norm iff its moment-
generating function is bounded in a neighborhood of zero (the
sub-exponential characterisation). The companion predicate
`HasSubexponentialMGF` is the subject of a prerequisite PR; see
framing question 3 in the module docstring. -/
theorem orliczNorm_psi1_lt_top_characterization
    [IsProbabilityMeasure μ] (X : Ω → ℝ) :
    orliczNorm X μ YoungFunction.psi1 < ⊤ ↔
      ∃ K : ℝ≥0, K ≠ 0 ∧ ∀ t : ℝ, |t| < 1 / K →
        Integrable (fun ω => Real.exp (t * X ω)) μ ∧
        (∫ ω, Real.exp (t * X ω) ∂μ) ≤
          Real.exp ((K : ℝ) * t ^ 2 / 2 / (1 - |t| * K)) := sorry

end ProbabilityTheory
