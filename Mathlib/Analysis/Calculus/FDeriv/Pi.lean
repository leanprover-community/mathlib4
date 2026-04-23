/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Sqrt
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Metrizable.Uniformity

/-!
# Derivatives on pi-types.
-/

public section

variable {𝕜 ι : Type*} [DecidableEq ι] [NontriviallyNormedField 𝕜]
variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

@[fun_prop]
theorem hasFDerivAt_update (x : ∀ i, E i) {i : ι} (y : E i) :
    HasFDerivAt (Function.update x i) (.pi (Pi.single i (.id 𝕜 (E i)))) y := by
  rw [hasFDerivAt_pi]
  intro j
  rcases eq_or_ne j i with rfl | hij
  · simpa using hasFDerivAt_id _
  · simpa [hij] using hasFDerivAt_const _ _

@[fun_prop]
theorem hasFDerivAt_single {i : ι} (y : E i) :
    HasFDerivAt (Pi.single i) (.pi (Pi.single i (.id 𝕜 (E i)))) y :=
  hasFDerivAt_update 0 y

theorem fderiv_update (x : ∀ i, E i) {i : ι} (y : E i) :
    fderiv 𝕜 (Function.update x i) y = .pi (Pi.single i (.id 𝕜 (E i))) :=
  (hasFDerivAt_update x y).fderiv

theorem fderiv_single {i : ι} (y : E i) :
    fderiv 𝕜 (Pi.single i) y = .pi (Pi.single i (.id 𝕜 (E i))) :=
  fderiv_update 0 y
