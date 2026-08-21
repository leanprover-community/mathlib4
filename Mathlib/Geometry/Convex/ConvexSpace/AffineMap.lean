/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-!
# Bundled affine maps between convex spaces

If `X` and `Y` are convex spaces (over `R`), we introduce the type
`ConvexSpace.AffineMap R X Y` of bundled affine maps from `X` to `Y`.

-/

@[expose] public section

variable {R : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]

namespace Convexity.ConvexSpace

variable (R) in
/-- The type of (bundled) affine maps between two convex spaces. -/
protected structure AffineMap
    (X Y : Type*) [ConvexSpace R X] [ConvexSpace R Y] where
  /-- The underlying map of an affine map between convex spaces. -/
  toFun : X → Y
  isAffineMap_toFun : IsAffineMap R toFun := by fun_prop

namespace AffineMap

instance {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y] :
    FunLike (ConvexSpace.AffineMap R X Y) X Y where
  coe := ConvexSpace.AffineMap.toFun
  coe_injective := fun ⟨f, _⟩ ⟨g, _⟩ h ↦ by simpa

initialize_simps_projections ConvexSpace.AffineMap (toFun → apply)

@[ext]
lemma ext {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y]
    {f g : ConvexSpace.AffineMap R X Y} (h : (f : X → Y) = g) : f = g :=
  DFunLike.coe_injective h

@[fun_prop]
lemma isAffineMap
    {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y]
    (f : ConvexSpace.AffineMap R X Y) :
    IsAffineMap R f :=
  f.isAffineMap_toFun

/-- The identity map, as a bundled affine map of convex spaces. -/
@[simps, implicit_reducible]
def id (X : Type*) [ConvexSpace R X] :
    ConvexSpace.AffineMap R X X where
  toFun := _root_.id

/-- The composition of bundled affine maps between convex spaces. -/
@[simps, implicit_reducible]
def comp
    {X Y Z : Type*} [ConvexSpace R X] [ConvexSpace R Y] [ConvexSpace R Z]
    (g : ConvexSpace.AffineMap R Y Z) (f : ConvexSpace.AffineMap R X Y) :
    ConvexSpace.AffineMap R X Z where
  toFun := g ∘ f

@[simp]
lemma coe_comp
    {X Y Z : Type*} [ConvexSpace R X] [ConvexSpace R Y] [ConvexSpace R Z]
    (g : ConvexSpace.AffineMap R Y Z) (f : ConvexSpace.AffineMap R X Y) :
    ⇑(g.comp f) = g ∘ f := rfl

@[simp]
lemma id_comp
    {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y]
    (f : ConvexSpace.AffineMap R X Y) :
    (AffineMap.id _).comp f = f := rfl

@[simp]
lemma comp_id
    {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y]
    (f : ConvexSpace.AffineMap R X Y) :
    f.comp (.id _) = f := rfl

lemma assoc {X Y Z T : Type*}
    [ConvexSpace R X] [ConvexSpace R Y] [ConvexSpace R Z] [ConvexSpace R T]
    (f₁ : ConvexSpace.AffineMap R Z T) (f₂ : ConvexSpace.AffineMap R Y Z)
    (f₃ : ConvexSpace.AffineMap R X Y) :
    (f₁.comp f₂).comp f₃ = f₁.comp (f₂.comp f₃) :=
  rfl

/-- A constant map between convex spaces, as a bundled affine map. -/
@[simps, implicit_reducible]
def const {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y] (y : Y) :
    ConvexSpace.AffineMap R X Y where
  toFun _ := y

end AffineMap

end Convexity.ConvexSpace
