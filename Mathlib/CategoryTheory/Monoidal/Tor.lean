/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Functor.LeftDerived
import Mathlib.CategoryTheory.Monoidal.Preadditive

#align_import category_theory.monoidal.tor from "leanprover-community/mathlib"@"09f981f72d43749f1fa072deade828d9c1e185bb"

/-!
# Tor, the left-derived functor of tensor product

We define `Tor C n : C ⥤ C ⥤ C`, by left-deriving in the second factor of `(X, Y) ↦ X ⊗ Y`.

For now we have almost nothing to say about it!

It would be good to show that this is naturally isomorphic to the functor obtained
by left-deriving in the first factor, instead.
For now we define `Tor'` by left-deriving in the first factor,
but showing `Tor C n ≅ Tor' C n` will require a bit more theory!
Possibly it's best to axiomatize delta functors, and obtain a unique characterisation?

-/


noncomputable section

open CategoryTheory.Limits

open CategoryTheory.MonoidalCategory

namespace CategoryTheory

variable {C : Type*} [Category C] [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C]
  [HasZeroObject C] [HasEqualizers C] [HasCokernels C] [HasImages C] [HasImageMaps C]
  [HasProjectiveResolutions C]

variable (C)

/-- We define `Tor C n : C ⥤ C ⥤ C` by left-deriving in the second factor of `(X, Y) ↦ X ⊗ Y`. -/
@[simps]
def Tor (n : ℕ) : C ⥤ C ⥤ C where
  obj X := Functor.leftDerived ((tensoringLeft C).obj X) n
  map f := NatTrans.leftDerived ((tensoringLeft C).map f) n
set_option linter.uppercaseLean3 false in
#align category_theory.Tor CategoryTheory.Tor

/-- An alternative definition of `Tor`, where we left-derive in the first factor instead. -/
@[simps! obj_obj]
def Tor' (n : ℕ) : C ⥤ C ⥤ C :=
  Functor.flip
    { obj := fun X => Functor.leftDerived ((tensoringRight C).obj X) n
      map := fun f => NatTrans.leftDerived ((tensoringRight C).map f) n }
set_option linter.uppercaseLean3 false in
#align category_theory.Tor' CategoryTheory.Tor'

-- porting note: the `checkType` linter complains about the automatically generated
-- lemma `Tor'_map_app`, but not about this one
@[simp]
lemma Tor'_map_app' (n : ℕ) {X Y : C} (f : X ⟶ Y) (Z : C) :
    ((Tor' C n).map f).app Z = (Functor.leftDerived ((tensoringRight C).obj Z) n).map f := by
  rfl

-- porting note: this specific lemma was added because otherwise the internals of
-- `NatTrans.leftDerived` leaks into the RHS (it was already so in mathlib)
@[simp]
lemma Tor'_obj_map (n : ℕ) {X Y : C} (Z : C) (f : X ⟶ Y) :
    ((Tor' C n).obj Z).map f = (NatTrans.leftDerived ((tensoringRight C).map f) n).app Z := rfl

open ZeroObject

/-- The higher `Tor` groups for `X` and `Y` are zero if `Y` is projective. -/
def torSuccOfProjective (X Y : C) [Projective Y] (n : ℕ) : ((Tor C (n + 1)).obj X).obj Y ≅ 0 :=
  ((tensoringLeft C).obj X).leftDerivedObjProjectiveSucc n Y
set_option linter.uppercaseLean3 false in
#align category_theory.Tor_succ_of_projective CategoryTheory.torSuccOfProjective

/-- The higher `Tor'` groups for `X` and `Y` are zero if `X` is projective. -/
def tor'SuccOfProjective (X Y : C) [Projective X] (n : ℕ) : ((Tor' C (n + 1)).obj X).obj Y ≅ 0 := by
  -- This unfortunately needs a manual `dsimp`, to avoid a slow unification problem.
  dsimp only [Tor', Functor.flip]
  exact ((tensoringRight C).obj Y).leftDerivedObjProjectiveSucc n X
set_option linter.uppercaseLean3 false in
#align category_theory.Tor'_succ_of_projective CategoryTheory.tor'SuccOfProjective

end CategoryTheory

assert_not_exists Module.abelian
