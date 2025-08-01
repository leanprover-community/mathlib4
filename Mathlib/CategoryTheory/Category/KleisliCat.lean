/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/

import Mathlib.CategoryTheory.Category.Basic

/-!
# The Kleisli construction on the Type category

Define the Kleisli category for (control) monads.
`CategoryTheory/Monad/Kleisli` defines the general version for a monad on `C`, and demonstrates
the equivalence between the two.

## TODO

Generalise this to work with CategoryTheory.Monad
-/


universe u v

namespace CategoryTheory

-- This file is about Lean 3 declaration "Kleisli".

/-- The Kleisli category on the (type-)monad `m`. Note that the monad is not assumed to be lawful
yet. -/
@[nolint unusedArguments]
def KleisliCat (_ : Type u → Type v) :=
  Type u

/-- Construct an object of the Kleisli category from a type. -/
def KleisliCat.mk (m) (α : Type u) : KleisliCat m :=
  α

instance KleisliCat.categoryStruct {m} [Monad.{u, v} m] :
    CategoryStruct (KleisliCat m) where
  Hom α β := α → m β
  id _ x := pure x
  comp f g := f >=> g

instance KleisliCat.category {m} [Monad.{u, v} m] [LawfulMonad m] : Category (KleisliCat m) := by
  -- Porting note: was
  -- refine' { id_comp' := _, comp_id' := _, assoc' := _ } <;> intros <;> ext <;> unfold_projs <;>
  --  simp only [(· >=> ·), functor_norm]
  refine { id_comp := ?_, comp_id := ?_, assoc := ?_ } <;> intros <;>
  refine funext (fun x => ?_) <;>
  simp +unfoldPartialApp [CategoryStruct.id, CategoryStruct.comp, (· >=> ·)]

@[simp]
theorem KleisliCat.id_def {m} [Monad m] (α : KleisliCat m) : 𝟙 α = @pure m _ α :=
  rfl

theorem KleisliCat.comp_def {m} [Monad m] (α β γ : KleisliCat m) (xs : α ⟶ β) (ys : β ⟶ γ) (a : α) :
    (xs ≫ ys) a = xs a >>= ys :=
  rfl

instance : Inhabited (KleisliCat id) :=
  ⟨PUnit⟩

instance {α : Type u} [Inhabited α] : Inhabited (KleisliCat.mk id α) :=
  ⟨show α from default⟩

end CategoryTheory
