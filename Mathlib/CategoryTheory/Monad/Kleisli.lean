/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki, Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.monad.kleisli
! leanprover-community/mathlib commit 545f0fb9837ce297da8eae0fec799d70191e97d4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Adjunction.Basic
import Mathbin.CategoryTheory.Monad.Basic

/-! # Kleisli category on a (co)monad

This file defines the Kleisli category on a monad `(T, η_ T, μ_ T)` as well as the co-Kleisli
category on a comonad `(U, ε_ U, δ_ U)`. It also defines the Kleisli adjunction which gives rise to
the monad `(T, η_ T, μ_ T)` as well as the co-Kleisli adjunction which gives rise to the comonad
`(U, ε_ U, δ_ U)`.

## References
* [Riehl, *Category theory in context*, Definition 5.2.9][riehl2017]
-/


namespace CategoryTheory

universe v u

-- morphism levels before object levels. See note [category_theory universes].
variable {C : Type u} [Category.{v} C]

/-- The objects for the Kleisli category of the monad `T : monad C`, which are the same
thing as objects of the base category `C`.
-/
@[nolint unused_arguments]
def Kleisli (T : Monad C) :=
  C
#align category_theory.kleisli CategoryTheory.Kleisli

namespace Kleisli

variable (T : Monad C)

instance [Inhabited C] (T : Monad C) : Inhabited (Kleisli T) :=
  ⟨(default : C)⟩

/-- The Kleisli category on a monad `T`.
    cf Definition 5.2.9 in [Riehl][riehl2017]. -/
instance Kleisli.category : Category (Kleisli T)
    where
  Hom := fun X Y : C => X ⟶ (T : C ⥤ C).obj Y
  id X := T.η.app X
  comp X Y Z f g := f ≫ (T : C ⥤ C).map g ≫ T.μ.app Z
  id_comp' X Y f := by
    rw [← T.η.naturality_assoc f, T.left_unit]
    apply category.comp_id
  assoc' W X Y Z f g h :=
    by
    simp only [functor.map_comp, category.assoc, monad.assoc]
    erw [T.μ.naturality_assoc]
#align category_theory.kleisli.kleisli.category CategoryTheory.Kleisli.Kleisli.category

namespace Adjunction

/-- The left adjoint of the adjunction which induces the monad `(T, η_ T, μ_ T)`. -/
@[simps]
def toKleisli : C ⥤ Kleisli T where
  obj X := (X : Kleisli T)
  map X Y f := (f ≫ T.η.app Y : _)
  map_comp' X Y Z f g := by
    unfold_projs
    simp [← T.η.naturality g]
#align category_theory.kleisli.adjunction.to_kleisli CategoryTheory.Kleisli.Adjunction.toKleisli

/-- The right adjoint of the adjunction which induces the monad `(T, η_ T, μ_ T)`. -/
@[simps]
def fromKleisli : Kleisli T ⥤ C where
  obj X := T.obj X
  map X Y f := T.map f ≫ T.μ.app Y
  map_id' X := T.right_unit _
  map_comp' X Y Z f g := by
    unfold_projs
    simp only [functor.map_comp, category.assoc]
    erw [← T.μ.naturality_assoc g, T.assoc]
    rfl
#align category_theory.kleisli.adjunction.from_kleisli CategoryTheory.Kleisli.Adjunction.fromKleisli

/-- The Kleisli adjunction which gives rise to the monad `(T, η_ T, μ_ T)`.
    cf Lemma 5.2.11 of [Riehl][riehl2017]. -/
def adj : toKleisli T ⊣ fromKleisli T :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y => Equiv.refl (X ⟶ T.obj Y)
      homEquiv_naturality_left_symm := fun X Y Z f g =>
        by
        unfold_projs
        dsimp
        rw [category.assoc, ← T.η.naturality_assoc g, functor.id_map]
        dsimp
        simp [monad.left_unit] }
#align category_theory.kleisli.adjunction.adj CategoryTheory.Kleisli.Adjunction.adj

/-- The composition of the adjunction gives the original functor. -/
def toKleisliCompFromKleisliIsoSelf : toKleisli T ⋙ fromKleisli T ≅ T :=
  NatIso.ofComponents (fun X => Iso.refl _) fun X Y f =>
    by
    dsimp
    simp
#align category_theory.kleisli.adjunction.to_kleisli_comp_from_kleisli_iso_self CategoryTheory.Kleisli.Adjunction.toKleisliCompFromKleisliIsoSelf

end Adjunction

end Kleisli

/-- The objects for the co-Kleisli category of the comonad `U : monad C`, which are the same
thing as objects of the base category `C`.
-/
@[nolint unused_arguments]
def Cokleisli (U : Comonad C) :=
  C
#align category_theory.cokleisli CategoryTheory.Cokleisli

namespace Cokleisli

variable (U : Comonad C)

instance [Inhabited C] (U : Comonad C) : Inhabited (Cokleisli U) :=
  ⟨(default : C)⟩

/-- The co-Kleisli category on a comonad `U`.-/
instance Cokleisli.category : Category (Cokleisli U)
    where
  Hom := fun X Y : C => (U : C ⥤ C).obj X ⟶ Y
  id X := U.ε.app X
  comp X Y Z f g := U.δ.app X ≫ (U : C ⥤ C).map f ≫ g
  id_comp' X Y f := by rw [U.right_counit_assoc]
  assoc' W X Y Z f g h := by
    unfold_projs
    simp only [functor.map_comp, ← category.assoc, U.δ.naturality_assoc, functor.comp_map,
      U.coassoc]
#align category_theory.cokleisli.cokleisli.category CategoryTheory.Cokleisli.Cokleisli.category

namespace Adjunction

/-- The right adjoint of the adjunction which induces the comonad `(U, ε_ U, δ_ U)`. -/
@[simps]
def toCokleisli : C ⥤ Cokleisli U
    where
  obj X := (X : Cokleisli U)
  map X Y f := (U.ε.app X ≫ f : _)
  map_comp' X Y Z f g := by
    unfold_projs
    simp [← U.ε.naturality g]
#align category_theory.cokleisli.adjunction.to_cokleisli CategoryTheory.Cokleisli.Adjunction.toCokleisli

/-- The left adjoint of the adjunction which induces the comonad `(U, ε_ U, δ_ U)`. -/
@[simps]
def fromCokleisli : Cokleisli U ⥤ C where
  obj X := U.obj X
  map X Y f := U.δ.app X ≫ U.map f
  map_id' X := U.right_counit _
  map_comp' X Y Z f g := by
    unfold_projs
    dsimp
    simp only [functor.map_comp, ← category.assoc]
    rw [comonad.coassoc]
    simp only [category.assoc, nat_trans.naturality, functor.comp_map]
#align category_theory.cokleisli.adjunction.from_cokleisli CategoryTheory.Cokleisli.Adjunction.fromCokleisli

/-- The co-Kleisli adjunction which gives rise to the monad `(U, ε_ U, δ_ U)`. -/
def adj : fromCokleisli U ⊣ toCokleisli U :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y => Equiv.refl (U.obj X ⟶ Y)
      homEquiv_naturality_right := fun X Y Z f g =>
        by
        unfold_projs; dsimp; erw [← category.assoc (U.map f), U.ε.naturality]; dsimp
        simp only [← category.assoc, comonad.left_counit, category.id_comp] }
#align category_theory.cokleisli.adjunction.adj CategoryTheory.Cokleisli.Adjunction.adj

/-- The composition of the adjunction gives the original functor. -/
def toCokleisliCompFromCokleisliIsoSelf : toCokleisli U ⋙ fromCokleisli U ≅ U :=
  NatIso.ofComponents (fun X => Iso.refl _) fun X Y f =>
    by
    dsimp
    simp
#align category_theory.cokleisli.adjunction.to_cokleisli_comp_from_cokleisli_iso_self CategoryTheory.Cokleisli.Adjunction.toCokleisliCompFromCokleisliIsoSelf

end Adjunction

end Cokleisli

end CategoryTheory

