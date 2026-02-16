/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.CategoryTheory.Types.Basic

/-!
# The Kleisli construction on the Type category

Define the Kleisli category for (control) monads.
`CategoryTheory/Monad/Kleisli` defines the general version for a monad on `C`, and demonstrates
the equivalence between the two.

## TODO

Generalise this to work with CategoryTheory.Monad
-/

@[expose] public section


universe u v

namespace CategoryTheory

-- This file is about Lean 3 declaration "Kleisli".

/-- The Kleisli category on the (type-)monad `m`. Note that the monad is not assumed to be lawful
yet. -/
@[nolint unusedArguments]
def KleisliCat (_ : Type u → Type v) :=
  TypeCat.{u}

/-- Construct an object of the Kleisli category from a type. -/
def KleisliCat.mk (m) (α : Type u) : KleisliCat m :=
  TypeCat.of α

instance KleisliCat.categoryStruct {m} [Monad.{u, v} m] :
    CategoryStruct (KleisliCat m) where
  Hom α β := TypeCat.Fun α.carrier (m β.carrier)
  id _ := ⟨fun x ↦ pure x⟩
  comp f g := ⟨f.as >=> g.as⟩

@[ext]
theorem KleisliCat.ext {m} [Monad.{u, v} m] (α β : KleisliCat m)
    (f g : α ⟶ β) (h : ∀ x, f.as x = g.as x) : f = g := TypeCat.Fun.ext <| funext h

instance KleisliCat.category {m} [Monad.{u, v} m] [LawfulMonad m] : Category (KleisliCat m) := by
  refine { id_comp := ?_, comp_id := ?_, assoc := ?_ } <;> intros <;>
  ext <;>
  simp +unfoldPartialApp [CategoryStruct.id, CategoryStruct.comp, (· >=> ·)]

@[simp]
theorem KleisliCat.id_def {m} [Monad m] (α : KleisliCat m) : 𝟙 α = ⟨fun x ↦ pure x⟩ :=
  rfl

theorem KleisliCat.comp_def {m} [Monad m] (α β γ : KleisliCat m) (xs : α ⟶ β) (ys : β ⟶ γ)
    (a : α.carrier) : (xs ≫ ys).as a = xs.as a >>= ys.as :=
  rfl

instance : Inhabited (KleisliCat id) :=
  ⟨.mk id PUnit⟩

instance {α : Type u} [Inhabited α] : Inhabited (KleisliCat.mk id α).carrier :=
  ⟨show α from default⟩

end CategoryTheory
