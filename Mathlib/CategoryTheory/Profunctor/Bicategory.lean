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
profunctors. The 2-morphisms are natural transformations between profunctors.

The bicategory instance is defined on `ProfCat.{u, u}`, with profunctors valued in `Type u`.
Its operations simplify to the corresponding operations in the `Profunctor` namespace.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

set_option linter.checkUnivs false in
/-- The bicategory of categories where the 1-morphisms are profunctors. -/
structure ProfCat where
  of ::
  /-- The objects of the bicategory are types... -/
  obj : Type u
  /-- ... bundled with a category instance. -/
  [str : Category.{v} obj]

initialize_simps_projections ProfCat (-str)

instance : CoeSort ProfCat (Type u) :=
  ⟨ProfCat.obj⟩

attribute [instance] ProfCat.str

namespace ProfCat

@[simp]
lemma of_obj (C : Type u) [Category.{v} C] : (of C).obj = C := rfl

@[simp]
lemma coe_of (C : ProfCat.{v, u}) : of C = C := rfl

end ProfCat

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

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [local simp] Types.chosenCoend_def in
@[reassoc (attr := simp)]
lemma triangle {C D E : Type u} [Category* C] [Category.{u} D] [Category* E]
    (P : Profunctor.{u} C D) (Q : Profunctor.{u} D E) :
    (P.associator (Profunctor.id (C := D)) Q).hom ≫ P.whiskerLeft (Q.leftUnitor.hom) =
      whiskerRight Q (P.rightUnitor.hom) := by
  ext _ _ ⟨_, ⟨_, _, g⟩, _⟩
  dsimp [chosenCoend.map_apply, Quot.map, associatorHomFun]
  symm
  apply Quot.sound
  rw [coendRel_iff]
  exact ⟨g, by simp [associatorHomFun, leftUnitor, rightUnitor]⟩

end

end Profunctor

namespace ProfCat

/-- The bicategory of categories, profunctors, and natural transformations. -/
-- Stop at the profunctor operations instead of unfolding the quotient constructions.
@[simps! id comp whiskerLeft whiskerRight associator leftUnitor rightUnitor]
instance bicategory : Bicategory ProfCat.{u, u} where
  Hom X Y := Profunctor.{u} X Y
  id X := .id
  comp P Q := P.comp Q
  whiskerLeft {_ _ _} P {_ _} f := P.whiskerLeft f
  whiskerRight f R := whiskerRight R f
  associator P Q R := P.associator Q R
  leftUnitor P := P.leftUnitor
  rightUnitor P := P.rightUnitor

variable {C D : ProfCat.{u, u}} {P Q : C ⟶ D}

/-- Two 2-morphisms in `ProfCat` are equal if they agree on every element. -/
@[ext]
lemma hom_ext {η θ : P ⟶ Q}
    (h : ∀ (X : C) (Y : Dᵒᵖ) (x : (P.obj X).obj Y),
      (η.app X).app Y x = (θ.app X).app Y x) : η = θ := by
  apply NatTrans.ext
  funext X
  apply NatTrans.ext
  funext Y
  exact ConcreteCategory.hom_ext _ _ (h X Y)

end ProfCat

end CategoryTheory
