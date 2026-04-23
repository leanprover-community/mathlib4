/-
Copyright (c) 2025 A Tucker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A Tucker
-/
module

public import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Order.Filter.Prod
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Neighborhoods

/-!
# Implicit function theorem — domain a product space

This specialization of the implicit function theorem applies to an uncurried bivariate function
`f : E₁ × E₂ → F` and assumes strict differentiability of `f` at `u : E₁ × E₂` as well as
invertibility of `f₂u : E₂ →L[𝕜] F` its partial derivative with respect to the second argument.

It proves the existence of `ψ : E₁ → E₂` such that for `v` in a neighbourhood of `u` we have
`f v = f u ↔ ψ v.1 = v.2`. This is `HasStrictFDerivAt.implicitFunctionOfProdDomain`. A formula for
its first derivative follows.

## Tags

implicit function
-/

public section

open Filter
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

namespace HasStrictFDerivAt

variable {u : E₁ × E₂} {f : E₁ × E₂ → F} {f'u : E₁ × E₂ →L[𝕜] F}

/-- Given `f : E₁ × E₂ → F` strictly differentiable at `u` with invertible partial derivative
`f₂u : E₂ →L[𝕜] F`, we may construct an `ImplicitFunctionData 𝕜 (E₁ × E₂) F E₁` with `f` as its
`leftFun` and `Prod.fst : E₁ × E₂ → E₁` as its `rightFun` by proving that the kernels of the
associated `leftDeriv` and `rightDeriv` are complementary. -/
def implicitFunctionDataOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ImplicitFunctionData 𝕜 (E₁ × E₂) F E₁ where
  leftFun := f
  rightFun := Prod.fst
  pt := u
  leftDeriv := f'u
  hasStrictFDerivAt_leftFun := dfu
  rightDeriv := .fst 𝕜 E₁ E₂
  hasStrictFDerivAt_rightFun := hasStrictFDerivAt_fst
  range_leftDeriv := by
    have : (f'u ∘L .inr 𝕜 E₁ E₂).range ≤ f'u.range := LinearMap.range_comp_le_range ..
    rwa [LinearMap.range_eq_top.mpr if₂u.surjective, top_le_iff] at this
  range_rightDeriv := Submodule.range_fst
  isCompl_ker := by
    constructor
    · rw [LinearMap.disjoint_ker]
      intro (_, y) h rfl
      simpa using (injective_iff_map_eq_zero _).mp if₂u.injective y h
    · rw [Submodule.codisjoint_iff_exists_add_eq]
      intro v
      have ⟨y, hy⟩ := if₂u.surjective (f'u v)
      use v - (0, y), (0, y)
      aesop

@[simp] theorem pt_implicitFunctionDataOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    (dfu.implicitFunctionDataOfProdDomain if₂u).pt = u := by
  rfl

@[simp] theorem leftFun_implicitFunctionDataOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    (dfu.implicitFunctionDataOfProdDomain if₂u).leftFun = f := by
  rfl

@[simp] theorem rightFun_implicitFunctionDataOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    (dfu.implicitFunctionDataOfProdDomain if₂u).rightFun = Prod.fst := by
  rfl

/-- Implicit function `ψ : E₁ → E₂` associated with the (uncurried) bivariate function
`f : E₁ × E₂ → F` at `u : E₁ × E₂`. -/
noncomputable def implicitFunctionOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    E₁ → E₂ :=
  fun x => ((dfu.implicitFunctionDataOfProdDomain if₂u).implicitFunction (f u) x).2

theorem implicitFunctionOfProdDomain_def
    {dfu : HasStrictFDerivAt f f'u u} {if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible} :
    dfu.implicitFunctionOfProdDomain if₂u =
      fun x => ((dfu.implicitFunctionDataOfProdDomain if₂u).implicitFunction (f u) x).2 := by
  rfl

theorem eventually_apply_eq_iff_implicitFunctionOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ∀ᶠ v in 𝓝 u, f v = f u ↔ dfu.implicitFunctionOfProdDomain if₂u v.1 = v.2 := by
  let φ := dfu.implicitFunctionDataOfProdDomain if₂u
  filter_upwards [φ.leftFun_eq_iff_implicitFunction, φ.rightFun_implicitFunction_eq_rightFun]
  exact fun v h _ => Iff.trans h ⟨congrArg _, by aesop⟩

theorem hasStrictFDerivAt_implicitFunctionOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    HasStrictFDerivAt (dfu.implicitFunctionOfProdDomain if₂u)
      (-(f'u ∘L .inr 𝕜 E₁ E₂).inverse ∘L (f'u ∘L .inl 𝕜 E₁ E₂)) u.1 := by
  suffices f'u ∘L (.prod (.id ..) (-(f'u ∘L .inr ..).inverse ∘L (f'u ∘L .inl ..))) = 0 from
    ((dfu.implicitFunctionDataOfProdDomain if₂u).hasStrictFDerivAt_implicitFunction _
      (ContinuousLinearMap.fst_comp_prod _ _) this).snd
  ext
  rw [f'u.comp_apply, ← f'u.comp_inl_add_comp_inr]
  simp [map_neg, if₂u]

theorem tendsto_implicitFunctionOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    Tendsto (dfu.implicitFunctionOfProdDomain if₂u) (𝓝 u.1) (𝓝 u.2) := by
  have := (dfu.hasStrictFDerivAt_implicitFunctionOfProdDomain if₂u).continuousAt.tendsto
  rwa [(dfu.eventually_apply_eq_iff_implicitFunctionOfProdDomain if₂u).self_of_nhds.mp rfl] at this

theorem eventually_apply_implicitFunctionOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ∀ᶠ x in 𝓝 u.1, f (x, dfu.implicitFunctionOfProdDomain if₂u x) = f u := by
  have hψ := dfu.tendsto_implicitFunctionOfProdDomain if₂u
  set ψ := dfu.implicitFunctionOfProdDomain if₂u
  suffices ∀ᶠ x in 𝓝 u.1, f (x, ψ x) = f u ↔ ψ x = ψ x by simpa using this
  apply Eventually.image_of_prod (r := fun x y => f (x, y) = f u ↔ ψ x = y) hψ
  rw [← nhds_prod_eq]
  exact dfu.eventually_apply_eq_iff_implicitFunctionOfProdDomain if₂u

end HasStrictFDerivAt

end
