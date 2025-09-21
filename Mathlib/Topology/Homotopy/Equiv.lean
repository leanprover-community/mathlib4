/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
import Mathlib.Topology.Homotopy.Basic

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
  /-- The forward map of an homotopy.

  Do NOT use directly. Use the coercion instead. -/
  toFun : C(X, Y)
  /-- The backward map of an homotopy.

  Do NOT use `e.invFun` directly. Use the coercion of `e.symm` instead. -/
  invFun : C(Y, X)
  left_inv : (invFun.comp toFun).Homotopic (ContinuousMap.id X)
  right_inv : (toFun.comp invFun).Homotopic (ContinuousMap.id Y)

@[inherit_doc] scoped infixl:25 " ≃ₕ " => ContinuousMap.HomotopyEquiv

namespace HomotopyEquiv

instance : CoeFun (X ≃ₕ Y) fun _ => X → Y := ⟨fun f => f.toFun⟩

@[continuity]
theorem continuous (h : HomotopyEquiv X Y) : Continuous h :=
  h.toFun.continuous

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

@[simp]
theorem coe_toHomotopyEquiv (h : X ≃ₜ Y) : (h.toHomotopyEquiv : X → Y) = h :=
  rfl

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

@[simp]
theorem coe_invFun (h : HomotopyEquiv X Y) : (⇑h.invFun : Y → X) = ⇑h.symm :=
  rfl

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def Simps.apply (h : X ≃ₕ Y) : X → Y :=
  h

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def Simps.symm_apply (h : X ≃ₕ Y) : Y → X :=
  h.symm

initialize_simps_projections HomotopyEquiv (toFun_toFun → apply, invFun_toFun → symm_apply,
  -toFun, -invFun)

/-- Any topological space is homotopy equivalent to itself.
-/
@[simps!]
def refl (X : Type u) [TopologicalSpace X] : X ≃ₕ X :=
  (Homeomorph.refl X).toHomotopyEquiv

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
    exact .comp (.refl _) (.comp h₂.left_inv (.refl _))
  right_inv := by
    refine Homotopic.trans ?_ h₂.right_inv
    exact .comp (.refl _) <| .comp h₁.right_inv (.refl _)

theorem symm_trans (h₁ : X ≃ₕ Y) (h₂ : Y ≃ₕ Z) : (h₁.trans h₂).symm = h₂.symm.trans h₁.symm := rfl

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

@[simp]
theorem symm_toHomotopyEquiv (h : X ≃ₜ Y) : h.symm.toHomotopyEquiv = h.toHomotopyEquiv.symm :=
  rfl

@[simp]
theorem trans_toHomotopyEquiv (h₀ : X ≃ₜ Y) (h₁ : Y ≃ₜ Z) :
    (h₀.trans h₁).toHomotopyEquiv = h₀.toHomotopyEquiv.trans h₁.toHomotopyEquiv :=
  rfl

end Homeomorph
