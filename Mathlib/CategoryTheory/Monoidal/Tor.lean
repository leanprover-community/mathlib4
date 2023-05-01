/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.monoidal.tor
! leanprover-community/mathlib commit 09f981f72d43749f1fa072deade828d9c1e185bb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Functor.LeftDerived
import Mathbin.CategoryTheory.Monoidal.Preadditive

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

variable {C : Type _} [Category C] [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C]
  [HasZeroObject C] [HasEqualizers C] [HasCokernels C] [HasImages C] [HasImageMaps C]
  [HasProjectiveResolutions C]

variable (C)

/-- We define `Tor C n : C ⥤ C ⥤ C` by left-deriving in the second factor of `(X, Y) ↦ X ⊗ Y`. -/
@[simps]
def tor (n : ℕ) : C ⥤ C ⥤ C
    where
  obj X := Functor.leftDerived ((tensoringLeft C).obj X) n
  map X Y f := NatTrans.leftDerived ((tensoringLeft C).map f) n
  map_id' X := by rw [(tensoring_left C).map_id, nat_trans.left_derived_id]
  map_comp' X Y Z f g := by rw [(tensoring_left C).map_comp, nat_trans.left_derived_comp]
#align category_theory.Tor CategoryTheory.tor

/-- An alternative definition of `Tor`, where we left-derive in the first factor instead. -/
@[simps]
def tor' (n : ℕ) : C ⥤ C ⥤ C :=
  Functor.flip
    { obj := fun X => Functor.leftDerived ((tensoringRight C).obj X) n
      map := fun X Y f => NatTrans.leftDerived ((tensoringRight C).map f) n
      map_id' := fun X => by rw [(tensoring_right C).map_id, nat_trans.left_derived_id]
      map_comp' := fun X Y Z f g => by
        rw [(tensoring_right C).map_comp, nat_trans.left_derived_comp] }
#align category_theory.Tor' CategoryTheory.tor'

open ZeroObject

/-- The higher `Tor` groups for `X` and `Y` are zero if `Y` is projective. -/
def torSuccOfProjective (X Y : C) [Projective Y] (n : ℕ) : ((tor C (n + 1)).obj X).obj Y ≅ 0 :=
  ((tensoringLeft C).obj X).leftDerivedObjProjectiveSucc n Y
#align category_theory.Tor_succ_of_projective CategoryTheory.torSuccOfProjective

/-- The higher `Tor'` groups for `X` and `Y` are zero if `X` is projective. -/
def tor'SuccOfProjective (X Y : C) [Projective X] (n : ℕ) : ((tor' C (n + 1)).obj X).obj Y ≅ 0 :=
  by
  -- This unfortunately needs a manual `dsimp`, to avoid a slow unification problem.
  dsimp only [Tor', functor.flip]
  exact ((tensoring_right C).obj Y).leftDerivedObjProjectiveSucc n X
#align category_theory.Tor'_succ_of_projective CategoryTheory.tor'SuccOfProjective

end CategoryTheory

assert_not_exists Module.abelian

