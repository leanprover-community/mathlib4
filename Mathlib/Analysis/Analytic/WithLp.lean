/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Analytic.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Analyticity on `WithLp`
-/

public section

open WithLp

open scoped ENNReal

namespace WithLp

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (p : ℝ≥0∞) [Fact (1 ≤ p)]

lemma analyticOn_ofLp (s : Set (WithLp p (E × F))) : AnalyticOn 𝕜 ofLp s :=
  (prodContinuousLinearEquiv p 𝕜 E F).analyticOn s

lemma analyticOn_toLp (s : Set (E × F)) : AnalyticOn 𝕜 (toLp p) s :=
  (prodContinuousLinearEquiv p 𝕜 E F).symm.analyticOn s

end WithLp

namespace PiLp

variable {𝕜 ι : Type*} [Fintype ι] {E : ι → Type*} [NontriviallyNormedField 𝕜]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] (p : ℝ≥0∞) [Fact (1 ≤ p)]

lemma analyticOn_ofLp (s : Set (PiLp p E)) : AnalyticOn 𝕜 ofLp s :=
  (continuousLinearEquiv p 𝕜 E).analyticOn s

lemma analyticOn_toLp (s : Set (Π i, E i)) : AnalyticOn 𝕜 (toLp p) s :=
  (continuousLinearEquiv p 𝕜 E).symm.analyticOn s

end PiLp
