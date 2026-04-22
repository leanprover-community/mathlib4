/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Profunctor.Comp

/-!

# The Profunctor Bicategory

This file defines the bicategory `ProfCat` whose objects are categories and whose 1-morphisms are
profunctors.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

/-- The bicategory of categories where the 1-morphisms are profunctors. -/
@[nolint checkUnivs]
structure ProfCat where
  of ::
  /-- The objects of the bicategory are types... -/
  obj : Type u
  /-- ... bundled with a category instance. -/
  [str : Category.{v} obj]

instance : CoeSort ProfCat (Type u) :=
  ⟨ProfCat.obj⟩

attribute [instance] ProfCat.str

open Limits Types Profunctor

namespace Profunctor

section

@[reassoc (attr := simp)]
lemma pentagon {C D E F G : Type u} [Category* C] [Category* D] [Category* E]
  [Category* F] [Category* G] (P : Profunctor.{max u w} C D) (Q : Profunctor.{max u w} D E)
    (R : Profunctor.{max u w} E F) (S : Profunctor.{max u w} F G) :
    whiskerRight S (P.associator Q R).hom ≫
        (P.associator (Q.comp R) S).hom ≫ P.whiskerLeft (Q.associator R S).hom =
      ((P.comp Q).associator R S).hom ≫ (P.associator Q (R.comp S)).hom := by
  ext _ _ ⟨_, ⟨_, ⟨_, _, _⟩, _⟩, _⟩
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma triangle {C D E : Type u} [Category* C] [Category.{u} D] [Category* E]
    (P : Profunctor.{u} C D) (Q : Profunctor.{u} D E) :
    (P.associator (Profunctor.id (C := D)) Q).hom ≫ P.whiskerLeft (Q.leftUnitor.hom) =
      whiskerRight Q (P.rightUnitor.hom) := by
  ext _ _ ⟨_, ⟨_, _, g⟩, _⟩
  dsimp [chosenCoend.map_apply, Quot.map]
  symm
  apply Quot.sound
  rw [coendRel_iff]
  exact ⟨g, by simp⟩

end

end Profunctor

set_option backward.isDefEq.respectTransparency false in
instance : Bicategory ProfCat.{u, u} where
  Hom X Y := Profunctor.{u} X Y
  id X := .id
  comp P Q := P.comp Q
  whiskerLeft P _ _ f := P.whiskerLeft f
  whiskerRight f R := whiskerRight R f
  associator P Q R := P.associator Q R
  leftUnitor P := P.leftUnitor
  rightUnitor P := P.rightUnitor

end CategoryTheory
