/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
public import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Truncated

/-!
# Deficiencies of Meromorphic Functions

Let `f` be meromorphic on the complex plane and let `a` be a value in `ℂ ∪ {∞}`, represented as an
element of `WithTop ℂ`. The characteristic function `characteristic f a` is the sum of two terms:
the proximity function `proximity f a`, which measures how close `f` comes to `a` on the circle of
radius `r`, and the logarithmic counting function `logCounting f a`, which counts the solutions of
`f = a` in the disk of radius `r`. By the First Main Theorem, `characteristic f a` agrees with
`characteristic f ⊤` up to a bounded function, so that the latter measures the growth of `f`
independently of `a`. The deficiency of `a` is the asymptotic share of the proximity function in
this growth. Values with positive deficiency are attained less often than the growth of `f` allows.

This file defines the deficiency and its truncated variant.

## Main definitions

- `ValueDistribution.deficiency`: the deficiency of `a`, the `liminf` as `r → ∞` of the quotient
  `proximity f a r / characteristic f ⊤ r`.
- `ValueDistribution.truncatedDeficiency`: the truncated deficiency of `a`, one minus the `limsup`
  as `r → ∞` of the quotient `truncatedLogCounting f a r / characteristic f ⊤ r`. The truncated
  logarithmic counting function counts the solutions of `f = a` without multiplicity.

## Main results

- `ValueDistribution.isBigO_truncatedLogCounting_characteristic_top`: if `f` is meromorphic and its
  characteristic function `characteristic f ⊤` tends to infinity, then the truncated logarithmic
  counting function is big-O of `characteristic f ⊤`.

## Implementation notes

The deficiencies are defined for every function `f : ℂ → E`, but they carry meaning only if the
characteristic function `characteristic f ⊤` tends to infinity. This is the case for every
meromorphic function that is not constant outside a discrete set.

For real-valued functions, the API for `Filter.liminf` and `Filter.limsup` requires boundedness
hypotheses (`Filter.IsBoundedUnder`, `Filter.IsCoboundedUnder`). For the quotients that define the
deficiencies, these hypotheses follow from `ValueDistribution.isBigO_proximity_characteristic_top`
and `ValueDistribution.isBigO_truncatedLogCounting_characteristic_top`, using
`Asymptotics.div_isBoundedUnder_of_isBigO`.

See Section VII.3 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677], Section 2.5 of
[Hayman, *Meromorphic Functions*][MR164038] or Section 2.3 of [Noguchi-Winkelmann, *Nevanlinna
Theory in Several Complex Variables and Diophantine Approximation*][MR3156076] for a detailed
discussion.
-/

@[expose] public section


open Asymptotics Filter Real

namespace ValueDistribution

/-!
## Definition of the Deficiencies
-/

section Definitions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/--
The **deficiency** of a value `a`: the asymptotic proportion of the characteristic function that
stems from the proximity function, i.e. from radii `r` where `f` is close to `a` on a large portion
of the circle `‖z‖ = r`. Values with positive deficiency are attained less often than the First Main
Theorem allows.
-/
noncomputable def deficiency (f : ℂ → E) (a : WithTop E) : ℝ :=
  liminf (fun r ↦ proximity f a r / characteristic f ⊤ r) atTop

/--
The **truncated deficiency** of a value `a`, defined through the truncated logarithmic counting
function `truncatedLogCounting f a`, which counts the solutions of `f = a` without multiplicity. It
measures both the deficiency of `a` and the asymptotic amount of ramification of `f` over `a`. For
meromorphic functions with unbounded characteristic function, the truncated deficiency dominates the
deficiency.
-/
noncomputable def truncatedDeficiency (f : ℂ → E) (a : WithTop E) : ℝ :=
  1 - limsup (fun r ↦ truncatedLogCounting f a r / characteristic f ⊤ r) atTop

end Definitions

/-!
## Comparison with the Characteristic Function

If the characteristic function `characteristic f ⊤` of a meromorphic function `f` tends to infinity,
then the functions that enter the definitions of the deficiencies are big-O of it. For the proximity
function, this is `ValueDistribution.isBigO_proximity_characteristic_top`.
-/

variable {f : ℂ → ℂ} {a : WithTop ℂ}

/--
If `f` is meromorphic on the complex plane and its characteristic function tends to infinity, then
the truncated logarithmic counting function `truncatedLogCounting f a` is big-O of
`characteristic f ⊤`.
-/
theorem isBigO_truncatedLogCounting_characteristic_top (hf : Meromorphic f)
    (hT : Tendsto (characteristic f ⊤) atTop atTop) :
    truncatedLogCounting f a =O[atTop] characteristic f ⊤ :=
  isBigO_truncatedLogCounting_logCounting.trans (isBigO_logCounting_characteristic_top hf hT)

end ValueDistribution
