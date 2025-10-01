/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Category.KleisliCat
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Monad.Kleisli
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Control.Basic

/-!

# Convert from `Monad` (i.e. Lean's `Type`-based monads) to `CategoryTheory.Monad`

This allows us to use these monads in category theory.

-/


namespace CategoryTheory

section

universe u

variable (m : Type u → Type u) [_root_.Monad m] [LawfulMonad m]

/-- A lawful `Control.Monad` gives a category theory `Monad` on the category of types.
-/
@[simps!]
def ofTypeMonad : Monad (Type u) where
  toFunctor := ofTypeFunctor m
  η := ⟨@pure m _, fun _ _ f => funext fun x => (LawfulApplicative.map_pure f x).symm⟩
  μ := ⟨@joinM m _, fun _ _ _ => funext fun _ => joinM_map_map _ _⟩
  assoc _ := funext fun _ => joinM_map_joinM _
  left_unit _ := funext fun _ => joinM_pure _
  right_unit _ := funext fun _ => joinM_map_pure _

/-- The `Kleisli` category of a `Control.Monad` is equivalent to the `Kleisli` category of its
category-theoretic version, provided the monad is lawful.
-/
@[simps]
def eq : KleisliCat m ≌ Kleisli (ofTypeMonad m) where
  functor :=
    { obj := fun X => X
      map := fun f => f
      map_id := fun _ => rfl
      map_comp := fun f g => by
        unfold_projs
        funext t
        simp only [ofTypeMonad_obj, Function.comp_apply, ofTypeMonad_map, ofTypeMonad_μ_app, joinM,
          bind_map_left, id_eq]
        rfl }
  inverse :=
    { obj := fun X => X
      map := fun f => f
      map_id := fun _ => rfl
      map_comp := fun f g => by
        unfold_projs
        -- Porting note: Need these instances for some lemmas below.
        --Should they be added as actual instances elsewhere?
        letI : _root_.Monad (ofTypeMonad m).obj :=
          show _root_.Monad m from inferInstance
        letI : LawfulMonad (ofTypeMonad m).obj :=
          show LawfulMonad m from inferInstance
        funext t
        simp only [ofTypeMonad_obj, Function.comp_apply, ofTypeMonad_map, ofTypeMonad_μ_app, joinM,
          bind_map_left, id_eq]
        rfl }
  unitIso := by
    refine NatIso.ofComponents (fun X => Iso.refl X) fun f => ?_
    change f >=> pure = pure >=> f
    simp [functor_norm]
  counitIso := NatIso.ofComponents fun X => Iso.refl X

end

end CategoryTheory
