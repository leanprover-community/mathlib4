/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.LinearAlgebra.Symmetric.Basic
public import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# Currying symmetric forms

In this file we define `SymmetricMap.curryLeft`
which interprets a symmetric map in `n + 1` variables
as a linear map in the 0th variable taking values in the symmetric maps in `n` variables.

TODO: is this file useful? what for?
-/

@[expose] public section

variable {R : Type*} {M M₂ N N₂ : Type*} [CommSemiring R] [AddCommMonoid M]
  [AddCommMonoid M₂] [AddCommMonoid N] [AddCommMonoid N₂] [Module R M] [Module R M₂]
  [Module R N] [Module R N₂] {n : ℕ}

namespace SymmetricMap

/-- Given a symmetric map `f` in `n+1` variables, split the first variable to obtain
a linear map into symmetric maps in `n` variables, given by `x ↦ (m ↦ f (Matrix.vecCons x m))`.
It can be thought of as a map $Hom(\bigwedge^{n+1} M, N) \to Hom(M, Hom(\bigwedge^n M, N))$.

This is `MultilinearMap.curryLeft` for `SymmetricMap`. See also
`SymmetricMap.curryLeftLinearMap`. -/
@[simps apply_toMultilinearMap]
def curryLeft (f : M [Sym^Fin n.succ]→ₗ[R] N) : M →ₗ[R] M [Sym^Fin n]→ₗ[R] N where
  toFun m :=
    { f.toMultilinearMap.curryLeft m with
      map_eq_map_of_swap' v i j _ := by
        -- apply f.map_eq_map_of_swap' --v i j
        --sorry --f.map_eq_map_of_swap' _ (by simpa) ((Fin.succ_injective _).ne hij) }
        sorry
    }
  map_add' _ _ := ext fun _ => f.map_vecCons_add _ _ _
  map_smul' _ _ := ext fun _ => f.map_vecCons_smul _ _ _

@[simp]
theorem curryLeft_apply_apply (f : M [Sym^Fin n.succ]→ₗ[R] N) (x : M) (v : Fin n → M) :
    curryLeft f x v = f (Matrix.vecCons x v) :=
  rfl

@[simp]
theorem curryLeft_zero : curryLeft (0 : M [Sym^Fin n.succ]→ₗ[R] N) = 0 :=
  rfl

@[simp]
theorem curryLeft_add (f g : M [Sym^Fin n.succ]→ₗ[R] N) :
    curryLeft (f + g) = curryLeft f + curryLeft g :=
  rfl

@[simp]
theorem curryLeft_smul (r : R) (f : M [Sym^Fin n.succ]→ₗ[R] N) :
    curryLeft (r • f) = r • curryLeft f :=
  rfl

/-- `SymmetricMap.curryLeft` as a `LinearMap`. This is a separate definition as dot notation
does not work for this version. -/
@[simps]
def curryLeftLinearMap :
    (M [Sym^Fin n.succ]→ₗ[R] N) →ₗ[R] M →ₗ[R] M [Sym^Fin n]→ₗ[R] N where
  toFun f := f.curryLeft
  map_add' := curryLeft_add
  map_smul' := curryLeft_smul

@[simp]
theorem curryLeft_compSymmetricMap (g : N →ₗ[R] N₂)
    (f : M [Sym^Fin n.succ]→ₗ[R] N) (m : M) :
    (g.compSymmetricMap f).curryLeft m = g.compSymmetricMap (f.curryLeft m) :=
  rfl

@[simp]
theorem curryLeft_compLinearMap (g : M₂ →ₗ[R] M) (f : M [Sym^Fin n.succ]→ₗ[R] N) (m : M₂) :
    (f.compLinearMap g).curryLeft m = (f.curryLeft (g m)).compLinearMap g :=
  ext fun v ↦ congr_arg f <| funext fun i ↦ by cases i using Fin.cases <;> simp

end SymmetricMap
