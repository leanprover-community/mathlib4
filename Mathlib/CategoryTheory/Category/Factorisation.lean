/-
Copyright (c) 2023 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# The Factorisation Category of a Category

`Factorisation f` is the category containing as objects all factorisations of a morphism `f`.

We show that `Factorisation f` always has an initial and a terminal object.

we also show that `Factorisation f` is isomorphic to a comma category in two ways,
both as iterated comma categories. Given `f : X ⟶ Y`, `(X/C)/f ≌ Factorisation f ≌ f/(C/Y)`.

TODO: Make `MonoFactorisation f` a special case of a `Factorisation f`.
-/

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

/-- Factorisations of a morphism `f` as a structure, containing, one object, two morphisms,
and the condition that their composition equals `f`. -/
structure Factorisation {X Y : C} (f : X ⟶ Y) where
  /-- The midpoint of the factorisation. -/
  mid : C
  /-- The morphism into the factorisation midpoint. -/
  ι   : X ⟶ mid
  /-- The morphism out of the factorisation midpoint. -/
  π   : mid ⟶ Y
  /-- The factorisation condition. -/
  ι_π : ι ≫ π = f := by aesop_cat

attribute [simp] Factorisation.ι_π

namespace Factorisation

variable {X Y : C} {f : X ⟶ Y}

/-- Morphisms of `Factorisation f` consist of morphism between their midpoints and the obvious
commutativity conditions. -/
@[ext]
protected structure Hom (d e : Factorisation f) : Type (max u v) where
  /-- The morphism between the midpoints of the factorizations. -/
  h : d.mid ⟶ e.mid
  /-- The left commuting triangle of the factorization morphism. -/
  ι_h : d.ι ≫ h = e.ι := by aesop_cat
  /-- The right commuting triangle of the factorization morphism. -/
  h_π : h ≫ e.π = d.π := by aesop_cat

attribute [simp] Factorisation.Hom.ι_h Factorisation.Hom.h_π

/-- The identity morphism of `Factorisation f`. -/
@[simps]
protected def Hom.id (d : Factorisation f) : Factorisation.Hom d d where
  h := 𝟙 _

/-- Composition of morphisms in `Factorisation f`. -/
@[simps]
protected def Hom.comp {d₁ d₂ d₃ : Factorisation f}
    (f : Factorisation.Hom d₁ d₂) (g : Factorisation.Hom d₂ d₃) : Factorisation.Hom d₁ d₃ where
  h := f.h ≫ g.h
  ι_h := by rw [← Category.assoc, f.ι_h, g.ι_h]
  h_π := by rw [Category.assoc, g.h_π, f.h_π]

instance : Category.{max u v} (Factorisation f) where
  Hom d e := Factorisation.Hom d e
  id d := Factorisation.Hom.id d
  comp f g := Factorisation.Hom.comp f g

/- We now aim to show that `Factorisation f` is equivalent to iterated comma categories
in two different ways.
Namely, given `f : X ⟶ Y`, we will have `(X/C)/f` ≌ `Factorisation f` ≌ `f/(C/Y)`.
-/
section IteratedCommaCategories

variable (f : X ⟶ Y)

/- `Factorisation f ≌ (X/C)/f` -/
section OverOfUnder

/-- We aim to show `Factorisation f` ≌ `(X/C)/f`. That is to say,
we aim to show the two functors we defined below are inverses of each other.
-/
def factorisationEquivOverUnderMk : Factorisation f ≌ Over (Under.mk f) where
  functor := {
    obj := fun α => Over.mk (Under.homMk α.π : Under.mk α.ι ⟶ Under.mk f)
    map := fun κ => Over.homMk (Under.homMk κ.h κ.ι_h) (Under.UnderMorphism.ext (by simp))
  }
  inverse := {
    obj := fun α => {
      mid := α.left.right,
      ι := α.left.hom,
      π := α.hom.right
    }
    map := fun κ => {
      h := κ.left.right,
      ι_h := Under.w κ.left,
      h_π := by rw [← Under.comp_right, Over.w]
    }
  }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end OverOfUnder

/- `Factorisation f ≌ f/(C/Y)` -/
section UnderOfOver

/-- proving that the two functors below are inverses of each other.
Thus formulating the ≌ relationship. -/
def factorisationEquivUnderOverMk : Factorisation f ≌ Under (Over.mk f) where
  functor := {
    obj := fun α => Under.mk (Over.homMk α.ι : Over.mk f ⟶ Over.mk α.π)
    map := fun κ => Under.homMk (Over.homMk κ.h κ.h_π) (Over.OverMorphism.ext (by simp))
  }
  inverse := {
    obj := fun α => {
      mid := α.right.left
      ι := α.hom.left
      π := α.right.hom
    }
    map := fun κ => {
      h := κ.right.left
      ι_h := by rw [← Over.comp_left, Under.w]
      h_π := Over.w κ.right
    }
  }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end UnderOfOver

end IteratedCommaCategories

variable (d : Factorisation f)

/-- The initial object in `Factorisation f`, with the domain of `f` as its midpoint. -/
@[simps]
protected def initial : Factorisation f where
  mid := X
  ι := 𝟙 _
  π := f

/-- The unique morphism out of `Factorisation.initial f`. -/
@[simps]
protected def initialHom (d : Factorisation f) :
    Factorisation.Hom (Factorisation.initial : Factorisation f) d where
  h := d.ι

instance : Unique ((Factorisation.initial : Factorisation f) ⟶ d) where
  default := Factorisation.initialHom d
  uniq f := by apply Factorisation.Hom.ext; simp [← f.ι_h]

/-- The terminal object in `Factorisation f`, with the codomain of `f` as its midpoint. -/
@[simps]
protected def terminal : Factorisation f where
  mid := Y
  ι := f
  π := 𝟙 _

/-- The unique morphism into `Factorisation.terminal f`. -/
@[simps]
protected def terminalHom (d : Factorisation f) :
    Factorisation.Hom d (Factorisation.terminal : Factorisation f) where
  h := d.π

instance : Unique (d ⟶ (Factorisation.terminal : Factorisation f)) where
  default := Factorisation.terminalHom d
  uniq f := by apply Factorisation.Hom.ext; simp [← f.h_π]

open Limits

/-- The initial factorisation is an initial object -/
def IsInitial_initial : IsInitial (Factorisation.initial : Factorisation f) := IsInitial.ofUnique _

instance : HasInitial (Factorisation f) := Limits.hasInitial_of_unique Factorisation.initial

/-- The terminal factorisation is a terminal object -/
def IsTerminal_terminal : IsTerminal (Factorisation.terminal : Factorisation f) :=
IsTerminal.ofUnique _

instance : HasTerminal (Factorisation f) := Limits.hasTerminal_of_unique Factorisation.terminal

/-- The forgetful functor from `Factorisation f` to the underlying category `C`. -/
@[simps]
def forget : Factorisation f ⥤ C where
  obj := Factorisation.mid
  map f := f.h

end Factorisation

end CategoryTheory
