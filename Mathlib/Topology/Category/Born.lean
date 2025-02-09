/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Topology.Bornology.Hom

/-!
# The category of bornologies

This defines `Born`, the category of bornologies.
-/


universe u

open CategoryTheory

/-- The category of bornologies. -/
structure Born where
  /-- The underlying bornology. -/
  carrier : Type*
  [str : Bornology carrier]

attribute [instance] Born.str

namespace Born

instance : CoeSort Born Type* :=
  ⟨carrier⟩

/-- Construct a bundled `Born` from a `Bornology`. -/
abbrev of (α : Type*) [Bornology α] : Born where
  carrier := α

instance : Inhabited Born :=
  ⟨of PUnit⟩

instance : LargeCategory.{u} Born where
  Hom X Y := LocallyBoundedMap X Y
  id X := LocallyBoundedMap.id X
  comp f g := g.comp f

instance : ConcreteCategory Born (LocallyBoundedMap · ·) where
  hom f := f
  ofHom f := f

end Born
