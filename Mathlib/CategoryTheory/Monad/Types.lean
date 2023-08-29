/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Monad.Kleisli
import Mathlib.CategoryTheory.Category.KleisliCat
import Mathlib.CategoryTheory.Types
import Mathlib.Control.Basic -- Porting note: Needed for `joinM_map_map`, etc.

#align_import category_theory.monad.types from "leanprover-community/mathlib"@"7c77279eec0b350e1e15ebda7cc4f74ee3fd58fb"

/-!

# Convert from `Monad` (i.e. Lean's `Type`-based monads) to `CategoryTheory.Monad`

This allows us to use these monads in category theory.

-/


namespace CategoryTheory

section

universe u

variable (m : Type u → Type u) [_root_.Monad m] [LawfulMonad m]

-- Porting note: Used `apply ...` instead of the direct term
-- in a few proofs below to avoid introducing typeclass instances inline.

/-- A lawful `Control.Monad` gives a category theory `Monad` on the category of types.
-/
@[simps!]
def ofTypeMonad : Monad (Type u) where
  toFunctor := ofTypeFunctor m
  η' := ⟨@pure m _, fun α β f => funext fun x => (LawfulApplicative.map_pure f x).symm⟩
  μ' := ⟨@joinM m _, fun α β (f : α → β) => funext fun a => by apply joinM_map_map⟩
                                                               -- 🎉 no goals
  assoc' α := funext fun a => by apply joinM_map_joinM
                                 -- 🎉 no goals
  left_unit' α := funext fun a => by apply joinM_pure
                                     -- 🎉 no goals
  right_unit' α := funext fun a => by apply joinM_map_pure
                                      -- 🎉 no goals
#align category_theory.of_type_monad CategoryTheory.ofTypeMonad

/-- The `Kleisli` category of a `Control.Monad` is equivalent to the `Kleisli` category of its
category-theoretic version, provided the monad is lawful.
-/
@[simps]
def eq : KleisliCat m ≌ Kleisli (ofTypeMonad m) where
  functor :=
    { obj := fun X => X
      map := fun f => f
      map_id := fun X => rfl
      map_comp := fun f g => by
        --unfold_projs
        funext t
        -- ⊢ { obj := fun X => X, map := fun {X Y} f => f }.map (f ≫ g) t = ({ obj := fun …
        -- Porting note: missing tactic `unfold_projs`, using `change` instead.
        change _ = joinM (g <$> (f t))
        -- ⊢ { obj := fun X => X, map := fun {X Y} f => f }.map (f ≫ g) t = joinM (g <$>  …
        simp only [joinM, seq_bind_eq, Function.comp.left_id]
        -- ⊢ (f ≫ g) t = f t >>= g
        rfl }
        -- 🎉 no goals
  inverse :=
    { obj := fun X => X
      map := fun f => f
      map_id := fun X => rfl
      map_comp := fun f g => by
        --unfold_projs
        --Porting note: Need these instances for some lemmas below.
        --Should they be added as actual instances elsewhere?
        letI : _root_.Monad (ofTypeMonad m).obj :=
          show _root_.Monad m from inferInstance
        letI : LawfulMonad (ofTypeMonad m).obj :=
          show LawfulMonad m from inferInstance
        funext t
        -- ⊢ { obj := fun X => X, map := fun {X Y} f => f }.map (f ≫ g) t = ({ obj := fun …
        dsimp
        -- ⊢ (f ≫ g) t = (f ≫ g) t
        -- Porting note: missing tactic `unfold_projs`, using `change` instead.
        change joinM (g <$> (f t)) = _
        -- ⊢ joinM (g <$> f t) = (f ≫ g) t
        simp only [joinM, seq_bind_eq, Function.comp.left_id]
        -- ⊢ f t >>= g = (f ≫ g) t
        rfl }
        -- 🎉 no goals
  unitIso := by
    refine' NatIso.ofComponents (fun X => Iso.refl X) fun f => _
    -- ⊢ (𝟭 (KleisliCat m)).map f ≫ ((fun X => Iso.refl X) Y✝).hom = ((fun X => Iso.r …
    change f >=> pure = pure >=> f
    -- ⊢ f >=> pure = pure >=> f
    simp [functor_norm]
    -- 🎉 no goals
  counitIso := NatIso.ofComponents fun X => Iso.refl X
#align category_theory.eq CategoryTheory.eq

end

end CategoryTheory
