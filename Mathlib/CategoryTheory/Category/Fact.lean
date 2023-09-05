/-
Copyright (c) 2023 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Arrow
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# The Factorisation Category of a Category

`Fact f` is the category containing as objects all factorisations of a morphism `f`.

We show that `Fact f` always has an initial and a terminal object.

TODO: Show that `Fact f` is isomorphic to a comma category in two ways.

TODO: Make `MonoFactorisation f` a special case of a `Fact f`.
-/

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

/-- Factorisations of a morphism `f` as a structure, containing, one object, two morphisms,
and the condition that their composition equals `f`. -/
structure Fact {X Y : C} (f : X ⟶ Y) where
  /-- The midpoint of the factorisation. -/
  D   : C
  /-- The morphism into the factorisation midpoint. -/
  ι   : X ⟶ D
  /-- The morphism out of the factorisation midpoint. -/
  π   : D ⟶ Y
  /-- The factorisation condition. -/
  ι_π : ι ≫ π = f := by aesop_cat

attribute [simp] Fact.ι_π

namespace Fact

variable {X Y : C} {f : X ⟶ Y}

/-- Morphisms of `Fact f` consist of morphism between their midpoints and the obvious
commutativity conditions. -/
@[ext]
protected structure Hom (d e : Fact f) : Type (max u v) where
  /-- The morphism between the midpoints of the factorizations. -/
  h : d.D ⟶ e.D
  /-- The left commuting triangle of the factorization morphism. -/
  ι_h : d.ι ≫ h = e.ι := by aesop_cat
  /-- The right commuting triangle of the factorization morphism. -/
  h_π : h ≫ e.π = d.π := by aesop_cat

attribute [simp] Fact.Hom.ι_h Fact.Hom.h_π

/-- The identity morphism of `Fact f`. -/
@[simps]
protected def Hom.id (d : Fact f) : Fact.Hom d d where
  h := 𝟙 _

/-- Composition of morphisms in `Fact f`. -/
@[simps]
protected def Hom.comp {d₁ d₂ d₃ : Fact f} (f : Fact.Hom d₁ d₂) (g : Fact.Hom d₂ d₃) :
    Fact.Hom d₁ d₃ where
  h := f.h ≫ g.h
  ι_h := by rw [← Category.assoc, f.ι_h, g.ι_h]
  h_π := by rw [Category.assoc, g.h_π, f.h_π]

instance : Category.{max u v} (Fact f) where
  Hom d e := Fact.Hom d e
  id d := Fact.Hom.id d
  comp f g := Fact.Hom.comp f g

variable (d : Fact f)

/-- The initial object in `Fact f`, with the domain of `f` as its midpoint. -/
@[simps]
protected def initial : Fact f where
  D := X
  ι := 𝟙 _
  π := f

/-- The unique morphism out of `Fact.initial f`. -/
@[simps]
protected def initialHom (d : Fact f) : Fact.Hom (Fact.initial : Fact f) d where
  h := d.ι

instance : Unique ((Fact.initial : Fact f) ⟶ d) where
  default := Fact.initialHom d
  uniq f := by apply Fact.Hom.ext; simp [← f.ι_h]

/-- The terminal object in `Fact f`, with the codomain of `f` as its midpoint. -/
@[simps]
protected def terminal : Fact f where
  D := Y
  ι := f
  π := 𝟙 _

/-- The unique morphism into `Fact.terminal f`. -/
@[simps]
protected def terminalHom (d : Fact f) : Fact.Hom d (Fact.terminal : Fact f) where
  h := d.π

instance : Unique (d ⟶ (Fact.terminal : Fact f)) where
  default := Fact.terminalHom d
  uniq f := by apply Fact.Hom.ext; simp [← f.h_π]

open Limits

instance : IsInitial (Fact.initial : Fact f) := IsInitial.ofUnique _

instance : HasInitial (Fact f) := Limits.hasInitial_of_unique Fact.initial

instance : IsTerminal (Fact.terminal : Fact f) := IsTerminal.ofUnique _

instance : HasTerminal (Fact f) := Limits.hasTerminal_of_unique Fact.terminal

/-- The forgetful functor from `Fact f` to the underlying category `C`. -/
@[simps]
def forget : Fact f ⥤ C where
  obj := Fact.D
  map f := f.h

end Fact
