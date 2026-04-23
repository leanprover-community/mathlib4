/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Alternating.Curry
public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
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

/-!
# Currying continuous alternating forms

In this file we define `ContinuousAlternatingMap.curryLeft`
which interprets a continuous alternating map in `n + 1` variables
as a continuous linear map in the 0th variable
taking values in the continuous alternating maps in `n` variables.
-/

@[expose] public section

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : ℕ}

namespace ContinuousAlternatingMap

/-- Given a continuous alternating map `f` in `n+1` variables, split the first variable to obtain
a continuous linear map into continuous alternating maps in `n` variables,
given by `x ↦ (m ↦ f (Matrix.vecCons x m))`.
It can be thought of as a map $Hom(\bigwedge^{n+1} M, N) \to Hom(M, Hom(\bigwedge^n M, N))$.

This is `ContinuousMultilinearMap.curryLeft` for `AlternatingMap`. See also
`ContinuousAlternatingMap.curryLeftLI`. -/
noncomputable def curryLeft (f : E [⋀^Fin (n + 1)]→L[𝕜] F) : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F :=
  AlternatingMap.mkContinuousLinear f.toAlternatingMap.curryLeft ‖f‖
    f.toContinuousMultilinearMap.norm_map_cons_le

@[simp]
lemma toContinuousMultilinearMap_curryLeft (f : E [⋀^Fin (n + 1)]→L[𝕜] F) (x : E) :
    (f.curryLeft x).toContinuousMultilinearMap = f.toContinuousMultilinearMap.curryLeft x :=
  rfl

@[simp]
lemma toAlternatingMap_curryLeft (f : E [⋀^Fin (n + 1)]→L[𝕜] F) (x : E) :
    (f.curryLeft x).toAlternatingMap = f.toAlternatingMap.curryLeft x :=
  rfl

@[simp]
lemma norm_curryLeft (f : E [⋀^Fin (n + 1)]→L[𝕜] F) : ‖f.curryLeft‖ = ‖f‖ :=
  f.toContinuousMultilinearMap.curryLeft_norm

@[simp]
theorem curryLeft_apply_apply (f : E [⋀^Fin (n + 1)]→L[𝕜] F) (x : E) (v : Fin n → E) :
    curryLeft f x v = f (Matrix.vecCons x v) :=
  rfl

@[simp]
theorem curryLeft_zero : curryLeft (0 : E [⋀^Fin (n + 1)]→L[𝕜] F) = 0 :=
  rfl

@[simp]
theorem curryLeft_add (f g : E [⋀^Fin (n + 1)]→L[𝕜] F) :
    curryLeft (f + g) = curryLeft f + curryLeft g :=
  rfl

@[simp]
theorem curryLeft_smul (r : 𝕜) (f : E [⋀^Fin (n + 1)]→L[𝕜] F) :
    curryLeft (r • f) = r • curryLeft f :=
  rfl

/-- `ContinuousAlternatingMap.curryLeft` as a `LinearIsometry`. -/
@[simps]
noncomputable def curryLeftLI :
    (E [⋀^Fin (n + 1)]→L[𝕜] F) →ₗᵢ[𝕜] (E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) where
  toFun f := f.curryLeft
  map_add' := curryLeft_add
  map_smul' := curryLeft_smul
  norm_map' := norm_curryLeft

/-- Currying with the same element twice gives the zero map. -/
@[simp]
theorem curryLeft_same (f : E [⋀^Fin (n + 2)]→L[𝕜] F) (x : E) :
    (f.curryLeft x).curryLeft x = 0 :=
  ext fun _ ↦ f.map_eq_zero_of_eq _ (by simp) Fin.zero_ne_one

@[simp]
theorem curryLeft_compContinuousAlternatingMap (g : F →L[𝕜] G) (f : E [⋀^Fin (n + 1)]→L[𝕜] F)
    (x : E) :
    (g.compContinuousAlternatingMap f).curryLeft x =
      g.compContinuousAlternatingMap (f.curryLeft x) :=
  rfl

@[simp]
theorem curryLeft_compContinuousLinearMap (g : F [⋀^Fin (n + 1)]→L[𝕜] G) (f : E →L[𝕜] F) (x : E) :
    (g.compContinuousLinearMap f).curryLeft x = (g.curryLeft (f x)).compContinuousLinearMap f :=
  ext fun v ↦ congr_arg g <| funext fun i ↦ by cases i using Fin.cases <;> simp

end ContinuousAlternatingMap
