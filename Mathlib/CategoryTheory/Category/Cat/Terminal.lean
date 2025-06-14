/-
Copyright (c) 2025 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier, Emily Riehl
-/
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Terminal categories

We prove that a category is terminal if its underlying type has a `Unique` structure and the
category has an `IsDiscrete` instance.

We then use this to provide various examples of terminal categories.

TODO: Show the converse: that terminal categories have a unique object and are discrete.

TODO: Provide an analogous characterization of terminal categories as codiscrete categories
with a unique object.

-/

universe v u v' u'

open CategoryTheory Limits Functor

namespace CategoryTheory

/-- The constant functor to the default object of a category whose underlying type is inhabited. -/
def Functor.toInhabited {T : Type u} [Category.{v} T] [Inhabited T]
    (X : Type u') [Category.{v'} X] : X ⥤ T := (const X).obj default

/-- Any two functors to a discrete category on a unique object are *equal*. -/
theorem Discrete.functor_ext_of_unique {T : Type u} [Category.{v} T] [Unique T] [IsDiscrete T]
    {X : Type u'} [Category.{v'} X] (F G : X ⥤ T) : F = G :=
  Functor.ext fun X => by simp only [eq_iff_true_of_subsingleton]
namespace Cat

/-- A discrete category with a unique object is terminal. -/
def isDiscreteUnique.isTerminal {T : Type u} [Category.{v} T] [Unique T] [IsDiscrete T] :
    IsTerminal (Cat.of T) :=
  IsTerminal.ofUniqueHom (fun X ↦ toInhabited (T := T) X)
    (fun _ _ ↦ Discrete.functor_ext_of_unique (T := T) _ _)

/-- Any `T : Cat.{u, u}` with a unique object and discrete homs is isomorphic to `⊤_ Cat.{u, u}.` -/
noncomputable def terminalDiscreteUniqueIso
    {T : Type u} [Category.{u} T] [Unique T] [IsDiscrete T] : ⊤_ Cat.{u, u} ≅ Cat.of T :=
  terminalIsoIsTerminal isDiscreteUnique.isTerminal

/-- The discrete category on `PUnit` is terminal. -/
def isTerminalDiscretePUnit : IsTerminal (Cat.of (Discrete PUnit)) :=
  isDiscreteUnique.isTerminal

/-- Any terminal object `T : Cat.{u, u}` is isomorphic to `Cat.of (Discrete PUnit)`. -/
def isoDiscretePUnitOfIsTerminal {T : Type u} [Category.{u} T] (hT : IsTerminal (Cat.of T)) :
    Cat.of T ≅ Cat.of (Discrete PUnit) :=
  IsTerminal.uniqueUpToIso hT isTerminalDiscretePUnit


end Cat

end CategoryTheory
