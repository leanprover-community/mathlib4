/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# Currying alternating forms

In this file we define `AlternatingMap.curryLeft`
which interprets an alternating map in `n + 1` variables
as a linear map in the 0th variable taking values in the alternating maps in `n` variables.
-/

variable {R : Type*} {M M₂ N N₂ : Type*} [CommSemiring R] [AddCommMonoid M]
  [AddCommMonoid M₂] [AddCommMonoid N] [AddCommMonoid N₂] [Module R M] [Module R M₂]
  [Module R N] [Module R N₂] {n : ℕ}

namespace AlternatingMap

/-- Given an alternating map `f` in `n+1` variables, split the first variable to obtain
a linear map into alternating maps in `n` variables, given by `x ↦ (m ↦ f (Matrix.vecCons x m))`.
It can be thought of as a map $Hom(\bigwedge^{n+1} M, N) \to Hom(M, Hom(\bigwedge^n M, N))$.

This is `MultilinearMap.curryLeft` for `AlternatingMap`. See also
`AlternatingMap.curryLeftLinearMap`. -/
@[simps apply_toMultilinearMap]
def curryLeft (f : M [⋀^Fin n.succ]→ₗ[R] N) : M →ₗ[R] M [⋀^Fin n]→ₗ[R] N where
  toFun m :=
    { f.toMultilinearMap.curryLeft m with
      map_eq_zero_of_eq' v i j hv hij :=
        f.map_eq_zero_of_eq _ (by simpa) ((Fin.succ_injective _).ne hij) }
  map_add' _ _ := ext fun _ => f.map_vecCons_add _ _ _
  map_smul' _ _ := ext fun _ => f.map_vecCons_smul _ _ _

@[simp]
theorem curryLeft_apply_apply (f : M [⋀^Fin n.succ]→ₗ[R] N) (x : M) (v : Fin n → M) :
    curryLeft f x v = f (Matrix.vecCons x v) :=
  rfl

@[simp]
theorem curryLeft_zero : curryLeft (0 : M [⋀^Fin n.succ]→ₗ[R] N) = 0 :=
  rfl

@[simp]
theorem curryLeft_add (f g : M [⋀^Fin n.succ]→ₗ[R] N) :
    curryLeft (f + g) = curryLeft f + curryLeft g :=
  rfl

@[simp]
theorem curryLeft_smul (r : R) (f : M [⋀^Fin n.succ]→ₗ[R] N) :
    curryLeft (r • f) = r • curryLeft f :=
  rfl

/-- `AlternatingMap.curryLeft` as a `LinearMap`. This is a separate definition as dot notation
does not work for this version. -/
@[simps]
def curryLeftLinearMap :
    (M [⋀^Fin n.succ]→ₗ[R] N) →ₗ[R] M →ₗ[R] M [⋀^Fin n]→ₗ[R] N where
  toFun f := f.curryLeft
  map_add' := curryLeft_add
  map_smul' := curryLeft_smul

/-- Currying with the same element twice gives the zero map. -/
@[simp]
theorem curryLeft_same (f : M [⋀^Fin n.succ.succ]→ₗ[R] N) (m : M) :
    (f.curryLeft m).curryLeft m = 0 :=
  ext fun _ => f.map_eq_zero_of_eq _ (by simp) Fin.zero_ne_one

@[simp]
theorem curryLeft_compAlternatingMap (g : N →ₗ[R] N₂)
    (f : M [⋀^Fin n.succ]→ₗ[R] N) (m : M) :
    (g.compAlternatingMap f).curryLeft m = g.compAlternatingMap (f.curryLeft m) :=
  rfl

@[simp]
theorem curryLeft_compLinearMap (g : M₂ →ₗ[R] M) (f : M [⋀^Fin n.succ]→ₗ[R] N) (m : M₂) :
    (f.compLinearMap g).curryLeft m = (f.curryLeft (g m)).compLinearMap g :=
  ext fun v ↦ congr_arg f <| funext fun i ↦ by cases i using Fin.cases <;> simp

end AlternatingMap
