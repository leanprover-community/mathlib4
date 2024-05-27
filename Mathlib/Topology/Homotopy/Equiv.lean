/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
import Mathlib.Topology.Homotopy.Basic

#align_import topology.homotopy.equiv from "leanprover-community/mathlib"@"3d7987cda72abc473c7cdbbb075170e9ac620042"

/-!

# Homotopy equivalences between topological spaces

In this file, we define homotopy equivalences between topological spaces `X` and `Y` as a pair of
functions `f : C(X, Y)` and `g : C(Y, X)` such that `f.comp g` and `g.comp f` are both homotopic
to `ContinuousMap.id`.

## Main definitions

- `ContinuousMap.HomotopyEquiv` is the type of homotopy equivalences between topological spaces.

## Notation

We introduce the notation `X ≃ₕ Y` for `ContinuousMap.HomotopyEquiv X Y` in the `ContinuousMap`
locale.

-/

universe u v w x

variable {X : Type u} {Y : Type v} {Z : Type w} {Z' : Type x}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace Z']

namespace ContinuousMap

/-- A homotopy equivalence between topological spaces `X` and `Y` are a pair of functions
`toFun : C(X, Y)` and `invFun : C(Y, X)` such that `toFun.comp invFun` and `invFun.comp toFun`
are both homotopic to corresponding identity maps.
-/
@[ext]
structure HomotopyEquiv (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] where
  toFun : C(X, Y)
  invFun : C(Y, X)
  left_inv : (invFun.comp toFun).Homotopic (ContinuousMap.id X)
  right_inv : (toFun.comp invFun).Homotopic (ContinuousMap.id Y)
#align continuous_map.homotopy_equiv ContinuousMap.HomotopyEquiv

scoped infixl:25 " ≃ₕ " => ContinuousMap.HomotopyEquiv

namespace HomotopyEquiv

/-- Coercion of a `HomotopyEquiv` to function. While the Lean 4 way is to unfold coercions, this
auxiliary definition will make porting of Lean 3 code easier.

Porting note (#11215): TODO: drop this definition. -/
@[coe] def toFun' (e : X ≃ₕ Y) : X → Y := e.toFun

instance : CoeFun (X ≃ₕ Y) fun _ => X → Y := ⟨toFun'⟩

@[simp]
theorem toFun_eq_coe (h : HomotopyEquiv X Y) : (h.toFun : X → Y) = h :=
  rfl
#align continuous_map.homotopy_equiv.to_fun_eq_coe ContinuousMap.HomotopyEquiv.toFun_eq_coe

@[continuity]
theorem continuous (h : HomotopyEquiv X Y) : Continuous h :=
  h.toFun.continuous
#align continuous_map.homotopy_equiv.continuous ContinuousMap.HomotopyEquiv.continuous

end HomotopyEquiv

end ContinuousMap

open ContinuousMap

namespace Homeomorph

/-- Any homeomorphism is a homotopy equivalence.
-/
def toHomotopyEquiv (h : X ≃ₜ Y) : X ≃ₕ Y where
  toFun := h
  invFun := h.symm
  left_inv := by rw [symm_comp_toContinuousMap]
  right_inv := by rw [toContinuousMap_comp_symm]
#align homeomorph.to_homotopy_equiv Homeomorph.toHomotopyEquiv

@[simp]
theorem coe_toHomotopyEquiv (h : X ≃ₜ Y) : (h.toHomotopyEquiv : X → Y) = h :=
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
def Simps.symm_apply (h : X ≃ₕ Y) : Y → X :=
  h.symm
#align continuous_map.homotopy_equiv.simps.symm_apply ContinuousMap.HomotopyEquiv.Simps.symm_apply

initialize_simps_projections HomotopyEquiv (toFun_toFun → apply, invFun_toFun → symm_apply,
  -toFun, -invFun)

/-- Any topological space is homotopy equivalent to itself.
-/
@[simps!]
def refl (X : Type u) [TopologicalSpace X] : X ≃ₕ X :=
  (Homeomorph.refl X).toHomotopyEquiv
#align continuous_map.homotopy_equiv.refl ContinuousMap.HomotopyEquiv.refl
#align continuous_map.homotopy_equiv.refl_apply ContinuousMap.HomotopyEquiv.refl_apply
#align continuous_map.homotopy_equiv.refl_symm_apply ContinuousMap.HomotopyEquiv.refl_symm_apply

instance : Inhabited (HomotopyEquiv Unit Unit) :=
  ⟨refl Unit⟩

/--
If `X` is homotopy equivalent to `Y`, and `Y` is homotopy equivalent to `Z`, then `X` is homotopy
equivalent to `Z`.
-/
@[simps!]
def trans (h₁ : X ≃ₕ Y) (h₂ : Y ≃ₕ Z) : X ≃ₕ Z where
  toFun := h₂.toFun.comp h₁.toFun
  invFun := h₁.invFun.comp h₂.invFun
  left_inv := by
    refine Homotopic.trans ?_ h₁.left_inv
    exact ((Homotopic.refl _).hcomp h₂.left_inv).hcomp (Homotopic.refl _)
  right_inv := by
    refine Homotopic.trans ?_ h₂.right_inv
    exact ((Homotopic.refl _).hcomp h₁.right_inv).hcomp (Homotopic.refl _)
#align continuous_map.homotopy_equiv.trans ContinuousMap.HomotopyEquiv.trans
#align continuous_map.homotopy_equiv.trans_apply ContinuousMap.HomotopyEquiv.trans_apply
#align continuous_map.homotopy_equiv.trans_symm_apply ContinuousMap.HomotopyEquiv.trans_symm_apply

theorem symm_trans (h₁ : X ≃ₕ Y) (h₂ : Y ≃ₕ Z) : (h₁.trans h₂).symm = h₂.symm.trans h₁.symm := rfl
#align continuous_map.homotopy_equiv.symm_trans ContinuousMap.HomotopyEquiv.symm_trans

/-- If `X` is homotopy equivalent to `Y` and `Z` is homotopy equivalent to `Z'`, then `X × Z` is
homotopy equivalent to `Z × Z'`. -/
def prodCongr (h₁ : X ≃ₕ Y) (h₂ : Z ≃ₕ Z') : (X × Z) ≃ₕ (Y × Z') where
  toFun := h₁.toFun.prodMap h₂.toFun
  invFun := h₁.invFun.prodMap h₂.invFun
  left_inv := h₁.left_inv.prodMap h₂.left_inv
  right_inv := h₁.right_inv.prodMap h₂.right_inv

/-- If `X i` is homotopy equivalent to `Y i` for each `i`, then the space of functions (a.k.a. the
indexed product) `∀ i, X i` is homotopy equivalent to `∀ i, Y i`. -/
def piCongrRight {ι : Type*} {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] (h : ∀ i, X i ≃ₕ Y i) :
    (∀ i, X i) ≃ₕ (∀ i, Y i) where
  toFun := .piMap fun i ↦ (h i).toFun
  invFun := .piMap fun i ↦ (h i).invFun
  left_inv := .piMap fun i ↦ (h i).left_inv
  right_inv := .piMap fun i ↦ (h i).right_inv

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
