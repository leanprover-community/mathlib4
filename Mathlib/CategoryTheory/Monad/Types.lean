/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.monad.types
! leanprover-community/mathlib commit 7c77279eec0b350e1e15ebda7cc4f74ee3fd58fb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Monad.Basic
import Mathbin.CategoryTheory.Monad.Kleisli
import Mathbin.CategoryTheory.Category.Kleisli
import Mathbin.CategoryTheory.Types

/-!

# Convert from `monad` (i.e. Lean's `Type`-based monads) to `category_theory.monad`

This allows us to use these monads in category theory.

-/


namespace CategoryTheory

section

universe u

variable (m : Type u → Type u) [Monad m] [LawfulMonad m]

/-- A lawful `control.monad` gives a category theory `monad` on the category of types.
-/
@[simps]
def ofTypeMonad : Monad (Type u)
    where
  toFunctor := ofTypeFunctor m
  η' := ⟨@pure m _, fun α β f => (LawfulApplicative.map_comp_pure f).symm⟩
  μ' := ⟨@joinM m _, fun α β (f : α → β) => funext fun a => joinM_map_map f a⟩
  assoc' α := funext fun a => joinM_map_joinM a
  left_unit' α := funext fun a => joinM_pure a
  right_unit' α := funext fun a => joinM_map_pure a
#align category_theory.of_type_monad CategoryTheory.ofTypeMonad

/-- The `Kleisli` category of a `control.monad` is equivalent to the `kleisli` category of its
category-theoretic version, provided the monad is lawful.
-/
@[simps]
def eq : KleisliCat m ≌ Kleisli (of_type_monad m)
    where
  Functor :=
    { obj := fun X => X
      map := fun X Y f => f
      map_id' := fun X => rfl
      map_comp' := fun X Y Z f g => by
        unfold_projs
        ext
        dsimp
        simp [joinM, seq_bind_eq] }
  inverse :=
    { obj := fun X => X
      map := fun X Y f => f
      map_id' := fun X => rfl
      map_comp' := fun X Y Z f g => by
        unfold_projs
        ext
        dsimp
        simp [joinM, seq_bind_eq] }
  unitIso := by
    refine' nat_iso.of_components (fun X => iso.refl X) fun X Y f => _
    change f >=> pure = pure >=> f
    simp [functor_norm]
  counitIso := NatIso.ofComponents (fun X => Iso.refl X) fun X Y f => by tidy
#align category_theory.eq CategoryTheory.eq

end

end CategoryTheory

