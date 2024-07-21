/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.CommSq

/-!
# The category of commutative squares

In this file, we define a bundled version of `CommSq`
which allows to consider commutative squares as
objects in a category `Square C`.

The four objects in a commutative square are
numbered as follows:
```
X₁ --> X₂
|      |
v      v
X₃ --> X₄
```

We define the flip functor, and two equivalences with
the category `Arrow (Arrow C)`, depending on whether
we consider a commutative square as a horizontal
morphism between two vertical maps (`arrowArrowEquivalence`)
or a vertical morphism betwen two horizontal
maps (`arrowArrowEquivalence'`).

## TODO
* define `Functor.mapSquare`
* introduce the pullback cone, the pushout cocone
attached to `sq : Square C` and define the
properties `IsPushout` and `IsPullback`.
* construct the equivalence `(Square C)ᵒᵖ ≌ Square C`

-/

universe v u

namespace CategoryTheory

open Category

variable (C : Type u) [Category.{v} C]

/-- The category of commutative squares in a category. -/
structure Square where
  /-- the top-left object -/
  {X₁ : C}
  /-- the top-right object -/
  {X₂ : C}
  /-- the bottom-left object -/
  {X₃ : C}
  /-- the bottom-right object -/
  {X₄ : C}
  /-- the top morphism -/
  f₁₂ : X₁ ⟶ X₂
  /-- the left morphism -/
  f₁₃ : X₁ ⟶ X₃
  /-- the right morphism -/
  f₂₄ : X₂ ⟶ X₄
  /-- the bottom morphism -/
  f₃₄ : X₃ ⟶ X₄
  fac : f₁₂ ≫ f₂₄ = f₁₃ ≫ f₃₄

namespace Square

variable {C}

lemma commSq (sq : Square C) : CommSq sq.f₁₂ sq.f₁₃ sq.f₂₄ sq.f₃₄ where
  w := sq.fac

/-- A morphism between two commutative squares consists of 4 morphisms
which extend these two squares into a commuting cube. -/
@[ext]
structure Hom (sq₁ sq₂ : Square C) where
  /-- the top-left morphism -/
  τ₁ : sq₁.X₁ ⟶ sq₂.X₁
  /-- the top-right morphism -/
  τ₂ : sq₁.X₂ ⟶ sq₂.X₂
  /-- the bottom-left morphism -/
  τ₃ : sq₁.X₃ ⟶ sq₂.X₃
  /-- the bottom-right morphism -/
  τ₄ : sq₁.X₄ ⟶ sq₂.X₄
  comm₁₂ : sq₁.f₁₂ ≫ τ₂ = τ₁ ≫ sq₂.f₁₂ := by aesop_cat
  comm₁₃ : sq₁.f₁₃ ≫ τ₃ = τ₁ ≫ sq₂.f₁₃ := by aesop_cat
  comm₂₄ : sq₁.f₂₄ ≫ τ₄ = τ₂ ≫ sq₂.f₂₄ := by aesop_cat
  comm₃₄ : sq₁.f₃₄ ≫ τ₄ = τ₃ ≫ sq₂.f₃₄ := by aesop_cat

namespace Hom

attribute [reassoc (attr := simp)] comm₁₂ comm₁₃ comm₂₄ comm₃₄

/-- The identity of a commutative square. -/
@[simps]
def id (sq : Square C) : Hom sq sq where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
  τ₄ := 𝟙 _

/-- The composition of morphisms of squares. -/
@[simps]
def comp {sq₁ sq₂ sq₃ : Square C} (f : Hom sq₁ sq₂) (g : Hom sq₂ sq₃) : Hom sq₁ sq₃ where
  τ₁ := f.τ₁ ≫ g.τ₁
  τ₂ := f.τ₂ ≫ g.τ₂
  τ₃ := f.τ₃ ≫ g.τ₃
  τ₄ := f.τ₄ ≫ g.τ₄

end Hom

@[simps!]
instance category : Category (Square C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[ext]
lemma hom_ext {sq₁ sq₂ : Square C} {f g : sq₁ ⟶ sq₂}
    (h₁ : f.τ₁ = g.τ₁) (h₂ : f.τ₂ = g.τ₂)
    (h₃ : f.τ₃ = g.τ₃) (h₄ : f.τ₄ = g.τ₄) : f = g :=
  Hom.ext _ _ h₁ h₂ h₃ h₄

/-- Constructor for isomorphisms in `Square c` -/
def isoMk {sq₁ sq₂ : Square C} (e₁ : sq₁.X₁ ≅ sq₂.X₁) (e₂ : sq₁.X₂ ≅ sq₂.X₂)
    (e₃ : sq₁.X₃ ≅ sq₂.X₃) (e₄ : sq₁.X₄ ≅ sq₂.X₄)
    (comm₁₂ : sq₁.f₁₂ ≫ e₂.hom = e₁.hom ≫ sq₂.f₁₂)
    (comm₁₃ : sq₁.f₁₃ ≫ e₃.hom = e₁.hom ≫ sq₂.f₁₃)
    (comm₂₄ : sq₁.f₂₄ ≫ e₄.hom = e₂.hom ≫ sq₂.f₂₄)
    (comm₃₄ : sq₁.f₃₄ ≫ e₄.hom = e₃.hom ≫ sq₂.f₃₄) :
    sq₁ ≅ sq₂ where
  hom :=
    { τ₁ := e₁.hom
      τ₂ := e₂.hom
      τ₃ := e₃.hom
      τ₄ := e₄.hom }
  inv :=
    { τ₁ := e₁.inv
      τ₂ := e₂.inv
      τ₃ := e₃.inv
      τ₄ := e₄.inv
      comm₁₂ := by simp only [← cancel_mono e₂.hom, assoc, Iso.inv_hom_id,
                      comp_id, comm₁₂, Iso.inv_hom_id_assoc]
      comm₁₃ := by simp only [← cancel_mono e₃.hom, assoc, Iso.inv_hom_id,
                      comp_id, comm₁₃, Iso.inv_hom_id_assoc]
      comm₂₄ := by simp only [← cancel_mono e₄.hom, assoc, Iso.inv_hom_id,
                      comp_id, comm₂₄, Iso.inv_hom_id_assoc]
      comm₃₄ := by simp only [← cancel_mono e₄.hom, assoc, Iso.inv_hom_id,
                      comp_id, comm₃₄, Iso.inv_hom_id_assoc] }

/-- Flipping a square by switching the top-right and the bottom-left objects. -/
@[simps]
def flip (sq : Square C) : Square C where
  fac := sq.fac.symm

/-- The functor which flips commutative squares. -/
@[simps]
def flipFunctor : Square C ⥤ Square C where
  obj := flip
  map φ :=
    { τ₁ := φ.τ₁
      τ₂ := φ.τ₃
      τ₃ := φ.τ₂
      τ₄ := φ.τ₄ }

/-- Flipping commutative squares is an auto-equivalence. -/
@[simps]
def flipEquivalence : Square C ≌ Square C where
  functor := flipFunctor
  inverse := flipFunctor
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- The functor `Square C ⥤ Arrow (Arrow C)` which sends a
commutative square `sq` to the obvious arrow from the left morphism of `sq`
to the right morphism of `sq`. -/
@[simps!]
def toArrowArrowFunctor : Square C ⥤ Arrow (Arrow C) where
  obj sq := Arrow.mk (Arrow.homMk sq.fac : Arrow.mk sq.f₁₃ ⟶ Arrow.mk sq.f₂₄)
  map φ := Arrow.homMk (u := Arrow.homMk φ.comm₁₃.symm)
    (v := Arrow.homMk φ.comm₂₄.symm) (by aesop_cat)

/-- The functor `Arrow (Arrow C) ⥤ Square C` which sends
a morphism `Arrow.mk f ⟶ Arrow.mk g` to the commutative square
with `f` on the left side and `g` on the right side. -/
@[simps!]
def fromArrowArrowFunctor : Arrow (Arrow C) ⥤ Square C where
  obj f := { fac := f.hom.w }
  map φ :=
    { τ₁ := φ.left.left
      τ₂ := φ.right.left
      τ₃ := φ.left.right
      τ₄ := φ.right.right
      comm₁₂ := Arrow.leftFunc.congr_map φ.w.symm
      comm₁₃ := φ.left.w.symm
      comm₂₄ := φ.right.w.symm
      comm₃₄ := Arrow.rightFunc.congr_map φ.w.symm }

/-- The equivalence `Square C ≌ Arrow (Arrow C)` which sends a
commutative square `sq` to the obvious arrow from the left morphism of `sq`
to the right morphism of `sq`. -/
@[simps]
def arrowArrowEquivalence : Square C ≌ Arrow (Arrow C) where
  functor := toArrowArrowFunctor
  inverse := fromArrowArrowFunctor
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- The functor `Square C ⥤ Arrow (Arrow C)` which sends a
commutative square `sq` to the obvious arrow from the top morphism of `sq`
to the bottom morphism of `sq`. -/
@[simps!]
def toArrowArrowFunctor' : Square C ⥤ Arrow (Arrow C) where
  obj sq := Arrow.mk (Arrow.homMk sq.fac.symm : Arrow.mk sq.f₁₂ ⟶ Arrow.mk sq.f₃₄)
  map φ := Arrow.homMk (u := Arrow.homMk φ.comm₁₂.symm)
    (v := Arrow.homMk φ.comm₃₄.symm) (by aesop_cat)

/-- The functor `Arrow (Arrow C) ⥤ Square C` which sends
a morphism `Arrow.mk f ⟶ Arrow.mk g` to the commutative square
with `f` on the top side and `g` on the bottom side. -/
@[simps!]
def fromArrowArrowFunctor' : Arrow (Arrow C) ⥤ Square C where
  obj f := { fac := f.hom.w.symm }
  map φ :=
    { τ₁ := φ.left.left
      τ₂ := φ.left.right
      τ₃ := φ.right.left
      τ₄ := φ.right.right
      comm₁₂ := φ.left.w.symm
      comm₁₃ := Arrow.leftFunc.congr_map φ.w.symm
      comm₂₄ := Arrow.rightFunc.congr_map φ.w.symm
      comm₃₄ := φ.right.w.symm }

/-- The equivalence `Square C ≌ Arrow (Arrow C)` which sends a
commutative square `sq` to the obvious arrow from the top morphism of `sq`
to the bottom morphism of `sq`. -/
@[simps]
def arrowArrowEquivalence' : Square C ≌ Arrow (Arrow C) where
  functor := toArrowArrowFunctor'
  inverse := fromArrowArrowFunctor'
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end Square

end CategoryTheory
