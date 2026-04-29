/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Category.KleisliCat
public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Monad.Kleisli
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Control.Basic
public meta import Mathlib.Tactic.Attr.Register

/-!

# Convert from `Monad` (i.e. Lean's `Type`-based monads) to `CategoryTheory.Monad`

This allows us to use these monads in category theory.

-/

@[expose] public section


namespace CategoryTheory

section

universe u

variable (m : Type u → Type u) [_root_.Monad m] [LawfulMonad m]

/-- A lawful `Control.Monad` gives a category theory `Monad` on the category of types.
-/
@[simps! obj map η_app μ_app]
def ofTypeMonad : Monad (Type u) where
  toFunctor := ofTypeFunctor m
  η := ⟨fun X ↦ TypeCat.ofHom (@pure m _ X), fun _ _ f => by
    ext x; exact (LawfulApplicative.map_pure f x).symm⟩
  μ := ⟨fun X ↦ TypeCat.ofHom (@joinM m _ X), fun _ _ _ => by ext _; exact joinM_map_map _ _⟩
  assoc _ := by ext; exact joinM_map_joinM _
  left_unit _ := by ext; exact joinM_pure _
  right_unit _ := by ext; exact joinM_map_pure _

set_option backward.isDefEq.respectTransparency false in
/-- The `Kleisli` category of a `Control.Monad` is equivalent to the `Kleisli` category of its
category-theoretic version, provided the monad is lawful.
-/
@[simps]
def kleisliCatEquivKleisli : KleisliCat m ≌ Kleisli (ofTypeMonad m) where
  functor :=
    { obj X := Kleisli.mk _ X
      map f := ⟨TypeCat.ofHom f⟩
      map_id := fun _ => rfl
      map_comp := fun f g => by
        ext
        simp [joinM]
        rfl }
  inverse :=
    { obj X := X.of
      map f x := f.of x
      map_id := fun _ => rfl
      map_comp := fun f g => by
        dsimp
        ext t
        simp [joinM]
        rfl }
  unitIso := by
    refine NatIso.ofComponents (fun X => Iso.refl X) fun f => ?_
    change f >=> pure = pure >=> f
    simp [functor_norm]
  counitIso := NatIso.ofComponents fun X => Iso.refl X

@[deprecated (since := "2026-04-16")] alias eq := kleisliCatEquivKleisli

end

end CategoryTheory
