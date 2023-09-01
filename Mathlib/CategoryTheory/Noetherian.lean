/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.Simple

#align_import category_theory.noetherian from "leanprover-community/mathlib"@"7c4c90f422a4a4477e4d8bc4dc9f1e634e6b2349"

/-!
# Artinian and noetherian categories

An artinian category is a category in which objects do not
have infinite decreasing sequences of subobjects.

A noetherian category is a category in which objects do not
have infinite increasing sequences of subobjects.

We show that any nonzero artinian object has a simple subobject.

## Future work
The Jordan-Hölder theorem, following https://stacks.math.columbia.edu/tag/0FCK.
-/


namespace CategoryTheory

open CategoryTheory.Limits

variable {C : Type*} [Category C]

/-- A noetherian object is an object
which does not have infinite increasing sequences of subobjects.

See https://stacks.math.columbia.edu/tag/0FCG
-/
class NoetherianObject (X : C) : Prop where
  subobject_gt_wellFounded' : WellFounded ((· > ·) : Subobject X → Subobject X → Prop)
#align category_theory.noetherian_object CategoryTheory.NoetherianObject

lemma NoetherianObject.subobject_gt_wellFounded (X : C) [NoetherianObject X] :
    WellFounded ((· > ·) : Subobject X → Subobject X → Prop) :=
  NoetherianObject.subobject_gt_wellFounded'

/-- An artinian object is an object
which does not have infinite decreasing sequences of subobjects.

See https://stacks.math.columbia.edu/tag/0FCF
-/
class ArtinianObject (X : C) : Prop where
  subobject_lt_wellFounded' : WellFounded ((· < ·) : Subobject X → Subobject X → Prop)
#align category_theory.artinian_object CategoryTheory.ArtinianObject

lemma ArtinianObject.subobject_lt_wellFounded (X : C) [ArtinianObject X] :
    WellFounded ((· < ·) : Subobject X → Subobject X → Prop) :=
  ArtinianObject.subobject_lt_wellFounded'

variable (C)

/-- A category is noetherian if it is essentially small and all objects are noetherian. -/
class Noetherian extends EssentiallySmall C : Prop where
  noetherianObject : ∀ X : C, NoetherianObject X
#align category_theory.noetherian CategoryTheory.Noetherian

attribute [instance] Noetherian.noetherianObject

/-- A category is artinian if it is essentially small and all objects are artinian. -/
class Artinian extends EssentiallySmall C : Prop where
  artinianObject : ∀ X : C, ArtinianObject X
#align category_theory.artinian CategoryTheory.Artinian

attribute [instance] Artinian.artinianObject

variable {C}

open Subobject

variable [HasZeroMorphisms C] [HasZeroObject C]

theorem exists_simple_subobject {X : C} [ArtinianObject X] (h : ¬IsZero X) :
    ∃ Y : Subobject X, Simple (Y : C) := by
  haveI : Nontrivial (Subobject X) := nontrivial_of_not_isZero h
  haveI := isAtomic_of_orderBot_wellFounded_lt (ArtinianObject.subobject_lt_wellFounded X)
  obtain ⟨Y, s⟩ := (IsAtomic.eq_bot_or_exists_atom_le (⊤ : Subobject X)).resolve_left top_ne_bot
  exact ⟨Y, (subobject_simple_iff_isAtom _).mpr s.1⟩
#align category_theory.exists_simple_subobject CategoryTheory.exists_simple_subobject

/-- Choose an arbitrary simple subobject of a non-zero artinian object. -/
noncomputable def simpleSubobject {X : C} [ArtinianObject X] (h : ¬IsZero X) : C :=
  (exists_simple_subobject h).choose
#align category_theory.simple_subobject CategoryTheory.simpleSubobject

/-- The monomorphism from the arbitrary simple subobject of a non-zero artinian object. -/
noncomputable def simpleSubobjectArrow {X : C} [ArtinianObject X] (h : ¬IsZero X) :
    simpleSubobject h ⟶ X :=
  (exists_simple_subobject h).choose.arrow
#align category_theory.simple_subobject_arrow CategoryTheory.simpleSubobjectArrow

instance mono_simpleSubobjectArrow {X : C} [ArtinianObject X] (h : ¬IsZero X) :
    Mono (simpleSubobjectArrow h) := by
  dsimp only [simpleSubobjectArrow]
  infer_instance

instance {X : C} [ArtinianObject X] (h : ¬IsZero X) : Simple (simpleSubobject h) :=
  (exists_simple_subobject h).choose_spec

end CategoryTheory
