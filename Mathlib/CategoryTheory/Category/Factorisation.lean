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

To give an idea of how the proof works:

Both
1. an object in `C/Y`
2. an object in `X/C`
can be viewed as a morphism `f : X ⟶ Y` in Category `C`
from the perspective of over/under categories.

Let's first consider `(X/C)/f`

Similarly, an object `α` in `(X/C)/f` can be viewed as a morphism `f₁ : f₀ ⟶ f` in Category `X/C`
where `f₀` and `f` are both objects of `X/C`,
thus morphisms of form `X ⟶ ?` in Category `C` (morphisms with domain X).
We know `f : X ⟶ Y`. Take `f₀ : X ⟶ Z₁`.
Then `α` is determined by the object-morphism pair of `(f₀, f₁)`.
By definitions of Under Categories, we can know that the morphism `f₁` will satisfy:
`f₀ ≫ f₁ = f`.

Assume another similar object-morphism pair in `X/C`, `(g₀, g₁)` determines
another object `β` in `(X / C) / f`, with `g₀ : X ⟶ Z₂`.

A morphism `κ : α ⟶ β` in `(X / C) / f`, by definition of Over Categories,
is a morphism in `X/C` making the following diagram commute:
           κ
    α  ---------> β
    |             |
f₁  |             | g₁
    ∨             ∨
    f      ==     f

so f₁ = κ ≫ g₁.

As we have discussed, `α` can be determined by the pair `(f₀, f₁)`, where the latter could be used
to formulate objects in the factorisation category.

Given `f₀ : X ⟶ Z`, and `f₀ ≫ f₁ = f`, we can see that the pair `(f₀, f₁)` can also be used to
structure a factorisation.
The map `κ : α ⟶ β` could thus be transferred to a map `κ' : ⟨ f₀, f₁ ⟩ ⟶ ⟨ g₀, g₁ ⟩` in `Fact f`.
Such assignment of mapping and object would form a functor, and evidently this functor is an iso if
we try to construct the `α`s and `β`s in the reversed direction from factorisations.
Thus we have conceptually shown `Factorisation f` is equivalent to one iterated comma category
`(X/C)/f` (being an over category on an under category),
and we can show similar results for `f/(C/Y)` (an under category on an over category).
-/
section IteratedCommaCategories

variable (f : X ⟶ Y)

/- `Factorisation f ≌ (X/C)/f` -/
section OverOfUnder

/-- The functor from `Factorisation f` to `(X/C)/f` -/
def fromFactToOverOfUnder : Factorisation f ⥤ Over (Under.mk f) where
  obj α := Over.mk (Under.homMk α.π : Under.mk α.ι ⟶ Under.mk f)
  map κ := Over.homMk (Under.homMk κ.h κ.ι_h) (Under.UnderMorphism.ext (by simp))

/-- The functor from `(X/C)/f` to `Factorisation f` -/
def fromOverOfUndertoFact : Over (Under.mk f) ⥤ Factorisation f where
  obj α := {
    mid := α.left.right,
    ι := α.left.hom,
    π := α.hom.right
  }
  map κ := {
    h := κ.left.right,
    ι_h := Under.w κ.left,
    h_π := by (rw [← Under.comp_right, Over.w])
  }

/-- We aim to show `Factorisation f` ≌ `(X/C)/f`. That is to say,
we aim to show the two functors we defined above are inverses of each other.
-/
def factEqOverOfUnder : Factorisation f ≌ Over (Under.mk f) where
  functor := fromFactToOverOfUnder f
  inverse := fromOverOfUndertoFact f
  unitIso := NatIso.ofComponents (fun g => {
    hom := 𝟙 g
    inv := 𝟙 g
  })
  counitIso := NatIso.ofComponents (fun g => {
    hom := 𝟙 (fromOverOfUndertoFact f ⋙ fromFactToOverOfUnder f).obj g
    inv := 𝟙 (fromOverOfUndertoFact f ⋙ fromFactToOverOfUnder f).obj g
  })

end OverOfUnder

/- `Factorisation f ≌ f/(C/Y)` -/
section UnderOfOver

/-- The functor turning `Factorisation f` into `f/(C/Y)` -/
def fromFactToUnderOfOver : Factorisation f ⥤ Under (Over.mk f) where
  obj α := Under.mk (Over.homMk α.ι : Over.mk f ⟶ Over.mk α.π)
  map κ := Under.homMk (Over.homMk κ.h κ.h_π) (Over.OverMorphism.ext (by simp))

/-- The functor turning `f/(C/Y)` into `Factorisation f` -/
def fromUnderOfOvertoFact : Under (Over.mk f) ⥤ Factorisation f where
  obj α := { mid := α.right.left, ι := α.hom.left, π := α.right.hom}
  map κ := {h := κ.right.left, ι_h := by (rw [← Over.comp_left, Under.w]), h_π := Over.w κ.right}

/-- proving that the two functors above are inverses of each other.
Thus formulating the ≌ relationship. -/
def factEqUnderOfOver : Factorisation f ≌ Under (Over.mk f) where
  functor := fromFactToUnderOfOver f
  inverse := fromUnderOfOvertoFact f
  unitIso := NatIso.ofComponents (fun g => {
    hom := 𝟙 g
    inv := 𝟙 g
  })
  counitIso := NatIso.ofComponents (fun g => {
    hom := 𝟙 (fromUnderOfOvertoFact f ⋙ fromFactToUnderOfOver f).obj g
    inv := 𝟙 (fromUnderOfOvertoFact f ⋙ fromFactToUnderOfOver f).obj g
  })

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
