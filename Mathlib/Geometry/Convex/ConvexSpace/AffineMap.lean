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

end ConvexSpace.AffineMap


namespace StdSimplex

@[ext]
lemma affineMap_ext {M : Type*} {Y : Type*} [ConvexSpace R Y]
    {f g : ConvexSpace.AffineMap R (StdSimplex R M) Y}
    (h : ∀ (i : M), f (.single i) = g (.single i)) : f = g := by
  ext x
  conv_lhs => rw [← iConvexComb_single x]
  conv_rhs => rw [← iConvexComb_single x]
  rw [f.isAffineMap.map_iConvexComb, g.isAffineMap.map_iConvexComb]
  aesop

/-- The (bundled) affine map `StdSimplex R M → StdSimplex R N` induced
by a map `f : M → N`. -/
noncomputable def affineMap {M N : Type*} (f : M → N) :
    ConvexSpace.AffineMap R (StdSimplex R M) (StdSimplex R N) where
  toFun := map f

@[simp]
lemma coe_affineMap {M N : Type*} (f : M → N) :
    ⇑(affineMap (R := R) f) = map f := rfl

@[simp]
lemma affineMap_id (M : Type*) :
    affineMap (R := R) (id : M → M) = .id _ := by
  aesop

/-- Given a map `f : M → X` where `X` is a convex space over `R`, this is the affine
map `StdSimplex R M → X` which sends the vertex corresponding to `m : M` to `f m`. -/
noncomputable def affineMapMk {M X : Type*} [ConvexSpace R X] (f : M → X) :
    ConvexSpace.AffineMap R (StdSimplex R M) X where
  toFun x := iConvexComb x f
  isAffineMap_toFun.map_sConvexComb s := by simp

lemma affineMapMk_apply {M : Type*} {Y : Type*} [ConvexSpace R Y] (f : M → Y)
    (s : StdSimplex R M) :
    affineMapMk (R := R) f s = iConvexComb s f := rfl

@[simp]
lemma affineMapMk_single {M : Type*} {Y : Type*} [ConvexSpace R Y] (f : M → Y) (m : M) :
    affineMapMk (R := R) f (.single m) = f m := by
  simp [affineMapMk_apply]

lemma affineMapMk_surjective {M : Type*} {Y : Type*} [ConvexSpace R Y]
    (s : ConvexSpace.AffineMap R (StdSimplex R M) Y) :
    ∃ (f : M → Y), affineMapMk f = s :=
  ⟨fun i ↦ s (single i), by ext; simp [affineMapMk_apply]⟩

lemma comp_affineMapMk {M : Type*} {Y Z : Type*} [ConvexSpace R Y] [ConvexSpace R Z]
    (f : ConvexSpace.AffineMap R Y Z) (g : M → Y) :
    f.comp (affineMapMk g) = affineMapMk (f ∘ g) := by
  aesop

end StdSimplex

end Convexity
