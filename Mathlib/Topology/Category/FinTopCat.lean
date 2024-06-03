/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Category of finite topological spaces

Definition of the category of finite topological spaces with the canonical
forgetful functors.

-/


universe u

open CategoryTheory

/-- A bundled finite topological space. -/
structure FinTopCat where
  /-- carrier of a finite topological space. -/
  α : Type u
  [fintype : Fintype α]
  [topologicalSpace : TopologicalSpace α]

namespace FinTopCat

instance : Inhabited FinTopCat :=
  ⟨⟨PUnit⟩⟩

instance : CoeSort FinTopCat (Type u) :=
  ⟨FinTopCat.α⟩

attribute [instance] fintype topologicalSpace

instance : Category FinTopCat.{u} where
  Hom X Y := { f : X → Y // Continuous f }
  id X := ⟨id, by continuity⟩
  comp f g := ⟨g.val.comp f.val, g.property.comp f.property⟩

instance : ConcreteCategory FinTopCat.{u} where
  forget := { obj := fun X ↦ X.α, map := fun f ↦ f.val }
  forget_faithful := ⟨fun {_ _ a b} h ↦ Subtype.ext h⟩

instance (X : FinTopCat) : TopologicalSpace ((forget FinTopCat).obj X) :=
  X.topologicalSpace

instance (X : FinTopCat) : Fintype ((forget FinTopCat).obj X) :=
  X.fintype

/-- Construct a bundled `FinTopCat` from the underlying type and the appropriate typeclasses. -/
def of (X : Type u) [Fintype X] [TopologicalSpace X] : FinTopCat :=
  ⟨X⟩

@[simp]
theorem coe_of (X : Type u) [Fintype X] [TopologicalSpace X] :
    (of X : Type u) = X :=
  rfl

/-- The forgetful functor to `FintypeCat`. -/
instance : HasForget₂ FinTopCat FintypeCat :=
  HasForget₂.mk' (fun X ↦ FintypeCat.of X) (fun _ ↦ rfl) (fun f ↦ f.val) HEq.rfl

instance (X : FinTopCat) : TopologicalSpace ((forget₂ FinTopCat FintypeCat).obj X) :=
  X.topologicalSpace

/-- The forgetful functor to `TopCat`. -/
instance : HasForget₂ FinTopCat TopCat :=
  HasForget₂.mk' (fun R ↦ TopCat.of R) (fun _ ↦ rfl) (fun f ↦ ⟨f.1, f.2⟩) HEq.rfl

instance (X : FinTopCat) : Fintype ((forget₂ FinTopCat TopCat).obj X) :=
  X.fintype

end FinTopCat
