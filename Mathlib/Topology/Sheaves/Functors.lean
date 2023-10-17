/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Andrew Yang
-/
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.CategoryTheory.Sites.Pushforward

#align_import topology.sheaves.functors from "leanprover-community/mathlib"@"85d6221d32c37e68f05b2e42cde6cee658dae5e9"

/-!
# functors between categories of sheaves

Show that the pushforward of a sheaf is a sheaf, and define
the pushforward functor from the category of C-valued sheaves
on X to that of sheaves on Y, given a continuous map between
topological spaces X and Y.

## Main definitions
- `TopCat.Sheaf.pushforward`:
    The pushforward functor between sheaf categories over topological spaces.
- `TopCat.Sheaf.pullback`: The pullback functor between sheaf categories over topological spaces.
- `TopCat.Sheaf.pullbackPushforwardAdjunction`:
  The adjunction between pullback and pushforward for sheaves on topological spaces.

-/


noncomputable section

universe w v u

open CategoryTheory

open CategoryTheory.Limits

open TopologicalSpace

variable {C : Type u} [Category.{v} C]

variable {X Y : TopCat.{w}} (f : X ⟶ Y)

variable ⦃ι : Type w⦄ {U : ι → Opens Y}

namespace TopCat

namespace Sheaf

open Presheaf

/-- The pushforward of a sheaf (by a continuous map) is a sheaf.
-/
theorem pushforward_sheaf_of_sheaf {F : X.Presheaf C} (h : F.IsSheaf) : (f _* F).IsSheaf :=
pullback_isSheaf_of_coverPreserving (compatiblePreserving_opens_map f)
  (coverPreserving_opens_map f) ⟨F, h⟩
set_option linter.uppercaseLean3 false in
#align Top.sheaf.pushforward_sheaf_of_sheaf TopCat.Sheaf.pushforward_sheaf_of_sheaf

variable (C)

/-- The pushforward functor.
-/
def pushforward (f : X ⟶ Y) : X.Sheaf C ⥤ Y.Sheaf C :=
Sites.pullback _ (compatiblePreserving_opens_map f) (coverPreserving_opens_map f)
set_option linter.uppercaseLean3 false in
#align Top.sheaf.pushforward TopCat.Sheaf.pushforward

lemma pushforward_forget (f : X ⟶ Y) :
    pushforward C f ⋙ forget C Y = forget C X ⋙ Presheaf.pushforward C f := rfl

/--
Pushforward of sheaves is isomorphic (actually definitionally equal) to pushforward of presheaves.
-/
def pushforwardForgetIso (f : X ⟶ Y) :
    pushforward C f ⋙ forget C Y ≅ forget C X ⋙ Presheaf.pushforward C f := Iso.refl _

variable {C}

@[simp] lemma pushforward_obj_val (f : X ⟶ Y) (F : X.Sheaf C) :
  ((pushforward C f).obj F).1 = f _* F.1 := rfl

@[simp] lemma pushforward_map (f : X ⟶ Y) {F F' : X.Sheaf C} (α : F ⟶ F') :
  ((pushforward C f).map α).1 = (Presheaf.pushforward C f).map α.1 := rfl

variable (A : Type*) [Category.{w} A] [ConcreteCategory.{w} A] [HasColimits A] [HasLimits A]
variable [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [ReflectsIsomorphisms (CategoryTheory.forget A)]

/--
The pushforward functor.
-/
def pullback (f : X ⟶ Y) : Y.Sheaf A ⥤ X.Sheaf A :=
Sites.pushforward A _ _ (Opens.map f)

lemma pullback_eq (f : X ⟶ Y) :
    pullback A f = forget A Y ⋙ Presheaf.pullback A f ⋙ presheafToSheaf _ _ := rfl

/--
The pullback of a sheaf is isomorphic (actually definitionally equal) to the sheafification
of the pullback as a presheaf.
-/
def pullbackIso (f : X ⟶ Y) :
    pullback A f ≅ forget A Y ⋙ Presheaf.pullback A f ⋙ presheafToSheaf _ _ := Iso.refl _

/-- The adjunction between pullback and pushforward for sheaves on topological spaces. -/
def pullbackPushforwardAdjunction (f : X ⟶ Y) :
    pullback A f ⊣ pushforward A f :=
Sites.pullbackPushforwardAdjunction _ _ _ _ _

instance : IsLeftAdjoint (pullback A f) := ⟨_, pullbackPushforwardAdjunction A f⟩
instance : IsRightAdjoint (pushforward A f) := ⟨_, pullbackPushforwardAdjunction A f⟩


end Sheaf

end TopCat
