/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam

! This file was ported from Lean 3 source module topology.homotopy.equiv
! leanprover-community/mathlib commit 3d7987cda72abc473c7cdbbb075170e9ac620042
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Homotopy.Basic

/-!

# Homotopy equivalences between topological spaces

In this file, we define homotopy equivalences between topological spaces `X` and `Y` as a pair of
functions `f : C(X, Y)` and `g : C(Y, X)` such that `f.comp g` and `g.comp f` are both homotopic
to `id`.

## Main definitions

- `continuous_map.homotopy_equiv` is the type of homotopy equivalences between topological spaces.

## Notation

We introduce the notation `X ≃ₕ Y` for `continuous_map.homotopy_equiv X Y` in the `continuous_map`
locale.

-/


universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace ContinuousMap

/-- A homotopy equivalence between topological spaces `X` and `Y` are a pair of functions
`to_fun : C(X, Y)` and `inv_fun : C(Y, X)` such that `to_fun.comp inv_fun` and `inv_fun.comp to_fun`
are both homotopic to `id`.
-/
@[ext]
structure HomotopyEquiv (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] where
  toFun : C(X, Y)
  invFun : C(Y, X)
  left_inv : (inv_fun.comp to_fun).Homotopic (ContinuousMap.id X)
  right_inv : (to_fun.comp inv_fun).Homotopic (ContinuousMap.id Y)
#align continuous_map.homotopy_equiv ContinuousMap.HomotopyEquiv

-- mathport name: continuous_map.homotopy_equiv
scoped infixl:25 " ≃ₕ " => ContinuousMap.HomotopyEquiv

namespace HomotopyEquiv

instance : CoeFun (HomotopyEquiv X Y) fun _ => X → Y :=
  ⟨fun h => h.toFun⟩

@[simp]
theorem toFun_eq_coe (h : HomotopyEquiv X Y) : (h.toFun : X → Y) = h :=
  rfl
#align continuous_map.homotopy_equiv.to_fun_eq_coe ContinuousMap.HomotopyEquiv.toFun_eq_coe

@[continuity]
theorem continuous (h : HomotopyEquiv X Y) : Continuous h :=
  h.toFun.Continuous
#align continuous_map.homotopy_equiv.continuous ContinuousMap.HomotopyEquiv.continuous

end HomotopyEquiv

end ContinuousMap

open ContinuousMap

namespace Homeomorph

/-- Any homeomorphism is a homotopy equivalence.
-/
def toHomotopyEquiv (h : X ≃ₜ Y) : X ≃ₕ Y
    where
  toFun := ⟨h⟩
  invFun := ⟨h.symm⟩
  left_inv := by
    convert ContinuousMap.Homotopic.refl _
    ext
    simp
  right_inv := by
    convert ContinuousMap.Homotopic.refl _
    ext
    simp
#align homeomorph.to_homotopy_equiv Homeomorph.toHomotopyEquiv

@[simp]
theorem coe_toHomotopyEquiv (h : X ≃ₜ Y) : ⇑h.toHomotopyEquiv = h :=
  rfl
#align homeomorph.coe_to_homotopy_equiv Homeomorph.coe_toHomotopyEquiv

end Homeomorph

namespace ContinuousMap

namespace HomotopyEquiv

/-- If `X` is homotopy equivalent to `Y`, then `Y` is homotopy equivalent to `X`.
-/
def symm (h : X ≃ₕ Y) : Y ≃ₕ X where
  toFun := h.invFun
  invFun := h.toFun
  left_inv := h.right_inv
  right_inv := h.left_inv
#align continuous_map.homotopy_equiv.symm ContinuousMap.HomotopyEquiv.symm

@[simp]
theorem coe_invFun (h : HomotopyEquiv X Y) : (⇑h.invFun : Y → X) = ⇑h.symm :=
  rfl
#align continuous_map.homotopy_equiv.coe_inv_fun ContinuousMap.HomotopyEquiv.coe_invFun

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def Simps.apply (h : X ≃ₕ Y) : X → Y :=
  h
#align continuous_map.homotopy_equiv.simps.apply ContinuousMap.HomotopyEquiv.Simps.apply

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def Simps.symmApply (h : X ≃ₕ Y) : Y → X :=
  h.symm
#align continuous_map.homotopy_equiv.simps.symm_apply ContinuousMap.HomotopyEquiv.Simps.symmApply

initialize_simps_projections HomotopyEquiv (to_fun_to_fun → apply, inv_fun_to_fun → symm_apply,
  -toFun, -invFun)

/-- Any topological space is homotopy equivalent to itself.
-/
@[simps]
def refl (X : Type u) [TopologicalSpace X] : X ≃ₕ X :=
  (Homeomorph.refl X).toHomotopyEquiv
#align continuous_map.homotopy_equiv.refl ContinuousMap.HomotopyEquiv.refl

instance : Inhabited (HomotopyEquiv Unit Unit) :=
  ⟨refl Unit⟩

/--
If `X` is homotopy equivalent to `Y`, and `Y` is homotopy equivalent to `Z`, then `X` is homotopy
equivalent to `Z`.
-/
@[simps]
def trans (h₁ : X ≃ₕ Y) (h₂ : Y ≃ₕ Z) : X ≃ₕ Z
    where
  toFun := h₂.toFun.comp h₁.toFun
  invFun := h₁.invFun.comp h₂.invFun
  left_inv := by
    refine' homotopic.trans _ h₁.left_inv
    change (h₁.inv_fun.comp h₂.inv_fun).comp (h₂.to_fun.comp h₁.to_fun) with
      h₁.inv_fun.comp ((h₂.inv_fun.comp h₂.to_fun).comp h₁.to_fun)
    refine' homotopic.hcomp _ (homotopic.refl _)
    refine' homotopic.trans ((homotopic.refl _).hcomp h₂.left_inv) _
    -- simp,
    rw [ContinuousMap.id_comp]
  right_inv := by
    refine' homotopic.trans _ h₂.right_inv
    change (h₂.to_fun.comp h₁.to_fun).comp (h₁.inv_fun.comp h₂.inv_fun) with
      h₂.to_fun.comp ((h₁.to_fun.comp h₁.inv_fun).comp h₂.inv_fun)
    refine' homotopic.hcomp _ (homotopic.refl _)
    refine' homotopic.trans ((homotopic.refl _).hcomp h₁.right_inv) _
    rw [id_comp]
#align continuous_map.homotopy_equiv.trans ContinuousMap.HomotopyEquiv.trans

theorem symm_trans (h₁ : X ≃ₕ Y) (h₂ : Y ≃ₕ Z) : (h₁.trans h₂).symm = h₂.symm.trans h₁.symm := by
  ext <;> rfl
#align continuous_map.homotopy_equiv.symm_trans ContinuousMap.HomotopyEquiv.symm_trans

end HomotopyEquiv

end ContinuousMap

open ContinuousMap

namespace Homeomorph

@[simp]
theorem refl_toHomotopyEquiv (X : Type u) [TopologicalSpace X] :
    (Homeomorph.refl X).toHomotopyEquiv = HomotopyEquiv.refl X :=
  rfl
#align homeomorph.refl_to_homotopy_equiv Homeomorph.refl_toHomotopyEquiv

@[simp]
theorem symm_toHomotopyEquiv (h : X ≃ₜ Y) : h.symm.toHomotopyEquiv = h.toHomotopyEquiv.symm :=
  rfl
#align homeomorph.symm_to_homotopy_equiv Homeomorph.symm_toHomotopyEquiv

@[simp]
theorem trans_toHomotopyEquiv (h₀ : X ≃ₜ Y) (h₁ : Y ≃ₜ Z) :
    (h₀.trans h₁).toHomotopyEquiv = h₀.toHomotopyEquiv.trans h₁.toHomotopyEquiv :=
  rfl
#align homeomorph.trans_to_homotopy_equiv Homeomorph.trans_toHomotopyEquiv

end Homeomorph

