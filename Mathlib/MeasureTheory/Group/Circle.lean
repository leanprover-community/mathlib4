/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Measure-theoretic results about the circle

This file is a place to collect measure-theoretic results about `Circle`, the unit circle in `ℂ`.
It equips it with the Borel structure inherited from the ambient subtype, which is what makes
`Circle`-valued functions (such as the additive characters `Real.fourierChar` and `Real.probChar`)
measurable.

See `Mathlib/MeasureTheory/Group/AddCircle.lean` for the additive circle `ℝ / ℤ`.
-/

@[expose] public section

namespace Circle

instance : MeasurableSpace Circle := inferInstanceAs <| MeasurableSpace <| Subtype _

instance : BorelSpace Circle :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)

end Circle
