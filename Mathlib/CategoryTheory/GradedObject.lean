/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.graded_object
! leanprover-community/mathlib commit 6876fa15e3158ff3e4a4e2af1fb6e1945c6e8803
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GroupPower.Lemmas
import Mathbin.CategoryTheory.Pi.Basic
import Mathbin.CategoryTheory.Shift.Basic
import Mathbin.CategoryTheory.ConcreteCategory.Basic

/-!
# The category of graded objects

For any type `β`, a `β`-graded object over some category `C` is just
a function `β → C` into the objects of `C`.
We put the "pointwise" category structure on these, as the non-dependent specialization of
`category_theory.pi`.

We describe the `comap` functors obtained by precomposing with functions `β → γ`.

As a consequence a fixed element (e.g. `1`) in an additive group `β` provides a shift
functor on `β`-graded objects

When `C` has coproducts we construct the `total` functor `graded_object β C ⥤ C`,
show that it is faithful, and deduce that when `C` is concrete so is `graded_object β C`.
-/


open CategoryTheory.pi

open CategoryTheory.Limits

namespace CategoryTheory

universe w v u

/-- A type synonym for `β → C`, used for `β`-graded objects in a category `C`. -/
def GradedObject (β : Type w) (C : Type u) : Type max w u :=
  β → C
#align category_theory.graded_object CategoryTheory.GradedObject

-- Satisfying the inhabited linter...
instance inhabitedGradedObject (β : Type w) (C : Type u) [Inhabited C] :
    Inhabited (GradedObject β C) :=
  ⟨fun b => Inhabited.default⟩
#align category_theory.inhabited_graded_object CategoryTheory.inhabitedGradedObject

-- `s` is here to distinguish type synonyms asking for different shifts
/-- A type synonym for `β → C`, used for `β`-graded objects in a category `C`
with a shift functor given by translation by `s`.
-/
@[nolint unused_arguments]
abbrev GradedObjectWithShift {β : Type w} [AddCommGroup β] (s : β) (C : Type u) : Type max w u :=
  GradedObject β C
#align category_theory.graded_object_with_shift CategoryTheory.GradedObjectWithShift

namespace GradedObject

variable {C : Type u} [Category.{v} C]

instance categoryOfGradedObjects (β : Type w) : Category.{max w v} (GradedObject β C) :=
  CategoryTheory.pi fun _ => C
#align category_theory.graded_object.category_of_graded_objects CategoryTheory.GradedObject.categoryOfGradedObjects

/-- The projection of a graded object to its `i`-th component. -/
@[simps]
def eval {β : Type w} (b : β) : GradedObject β C ⥤ C
    where
  obj X := X b
  map X Y f := f b
#align category_theory.graded_object.eval CategoryTheory.GradedObject.eval

section

variable (C)

/-- The natural isomorphism comparing between
pulling back along two propositionally equal functions.
-/
@[simps]
def comapEq {β γ : Type w} {f g : β → γ} (h : f = g) : comap (fun _ => C) f ≅ comap (fun _ => C) g
    where
  Hom := { app := fun X b => eqToHom (by dsimp [comap]; subst h) }
  inv := { app := fun X b => eqToHom (by dsimp [comap]; subst h) }
#align category_theory.graded_object.comap_eq CategoryTheory.GradedObject.comapEq

theorem comapEq_symm {β γ : Type w} {f g : β → γ} (h : f = g) :
    comapEq C h.symm = (comapEq C h).symm := by tidy
#align category_theory.graded_object.comap_eq_symm CategoryTheory.GradedObject.comapEq_symm

theorem comapEq_trans {β γ : Type w} {f g h : β → γ} (k : f = g) (l : g = h) :
    comapEq C (k.trans l) = comapEq C k ≪≫ comapEq C l :=
  by
  ext (X b)
  simp
#align category_theory.graded_object.comap_eq_trans CategoryTheory.GradedObject.comapEq_trans

@[simp]
theorem eqToHom_apply {β : Type w} {X Y : ∀ b : β, C} (h : X = Y) (b : β) :
    (eqToHom h : X ⟶ Y) b = eqToHom (by subst h) :=
  by
  subst h
  rfl
#align category_theory.graded_object.eq_to_hom_apply CategoryTheory.GradedObject.eqToHom_apply

/-- The equivalence between β-graded objects and γ-graded objects,
given an equivalence between β and γ.
-/
@[simps]
def comapEquiv {β γ : Type w} (e : β ≃ γ) : GradedObject β C ≌ GradedObject γ C
    where
  Functor := comap (fun _ => C) (e.symm : γ → β)
  inverse := comap (fun _ => C) (e : β → γ)
  counitIso :=
    (comapComp (fun _ => C) _ _).trans
      (comapEq C
        (by
          ext
          simp))
  unitIso :=
    (comapEq C
          (by
            ext
            simp)).trans
      (comapComp _ _ _).symm
  functor_unitIso_comp' X := by
    ext b
    dsimp
    simp
#align category_theory.graded_object.comap_equiv CategoryTheory.GradedObject.comapEquiv

-- See note [dsimp, simp].
end

instance hasShift {β : Type _} [AddCommGroup β] (s : β) : HasShift (GradedObjectWithShift s C) ℤ :=
  hasShiftMk _ _
    { f := fun n => comap (fun _ => C) fun b : β => b + n • s
      zero :=
        comapEq C
            (by
              ext
              simp) ≪≫
          comapId β fun _ => C
      add := fun m n =>
        comapEq C
            (by
              ext
              simp [add_zsmul, add_comm]) ≪≫
          (comapComp _ _ _).symm
      assoc_hom_app := fun m₁ m₂ m₃ X => by
        ext
        dsimp
        simp
      zero_add_hom_app := fun n X => by
        ext
        dsimp
        simpa
      add_zero_hom_app := fun n X => by
        ext
        dsimp
        simpa }
#align category_theory.graded_object.has_shift CategoryTheory.GradedObject.hasShift

@[simp]
theorem shiftFunctor_obj_apply {β : Type _} [AddCommGroup β] (s : β) (X : β → C) (t : β) (n : ℤ) :
    (shiftFunctor (GradedObjectWithShift s C) n).obj X t = X (t + n • s) :=
  rfl
#align category_theory.graded_object.shift_functor_obj_apply CategoryTheory.GradedObject.shiftFunctor_obj_apply

@[simp]
theorem shiftFunctor_map_apply {β : Type _} [AddCommGroup β] (s : β)
    {X Y : GradedObjectWithShift s C} (f : X ⟶ Y) (t : β) (n : ℤ) :
    (shiftFunctor (GradedObjectWithShift s C) n).map f t = f (t + n • s) :=
  rfl
#align category_theory.graded_object.shift_functor_map_apply CategoryTheory.GradedObject.shiftFunctor_map_apply

instance hasZeroMorphisms [HasZeroMorphisms C] (β : Type w) :
    HasZeroMorphisms.{max w v} (GradedObject β C) where Zero X Y := { zero := fun b => 0 }
#align category_theory.graded_object.has_zero_morphisms CategoryTheory.GradedObject.hasZeroMorphisms

@[simp]
theorem zero_apply [HasZeroMorphisms C] (β : Type w) (X Y : GradedObject β C) (b : β) :
    (0 : X ⟶ Y) b = 0 :=
  rfl
#align category_theory.graded_object.zero_apply CategoryTheory.GradedObject.zero_apply

section

open ZeroObject

instance hasZeroObject [HasZeroObject C] [HasZeroMorphisms C] (β : Type w) :
    HasZeroObject.{max w v} (GradedObject β C) := by
  refine'
      ⟨⟨fun b => 0, fun X => ⟨⟨⟨fun b => 0⟩, fun f => _⟩⟩, fun X =>
          ⟨⟨⟨fun b => 0⟩, fun f => _⟩⟩⟩⟩ <;>
    ext
#align category_theory.graded_object.has_zero_object CategoryTheory.GradedObject.hasZeroObject

end

end GradedObject

namespace GradedObject

-- The universes get a little hairy here, so we restrict the universe level for the grading to 0.
-- Since we're typically interested in grading by ℤ or a finite group, this should be okay.
-- If you're grading by things in higher universes, have fun!
variable (β : Type)

variable (C : Type u) [Category.{v} C]

variable [HasCoproducts.{0} C]

section

attribute [local tidy] tactic.discrete_cases

/-- The total object of a graded object is the coproduct of the graded components.
-/
noncomputable def total : GradedObject β C ⥤ C
    where
  obj X := ∐ fun i : β => X i
  map X Y f := Limits.Sigma.map fun i => f i
#align category_theory.graded_object.total CategoryTheory.GradedObject.total

end

variable [HasZeroMorphisms C]

/--
The `total` functor taking a graded object to the coproduct of its graded components is faithful.
To prove this, we need to know that the coprojections into the coproduct are monomorphisms,
which follows from the fact we have zero morphisms and decidable equality for the grading.
-/
instance : Faithful (total β C)
    where map_injective' X Y f g w := by
    classical
      ext i
      replace w := sigma.ι (fun i : β => X i) i ≫= w
      erw [colimit.ι_map, colimit.ι_map] at w
      simp at *
      exact mono.right_cancellation _ _ w

end GradedObject

namespace GradedObject

noncomputable section

variable (β : Type)

variable (C : Type (u + 1)) [LargeCategory C] [ConcreteCategory C] [HasCoproducts.{0} C]
  [HasZeroMorphisms C]

instance : ConcreteCategory (GradedObject β C) where forget := total β C ⋙ forget C

instance : HasForget₂ (GradedObject β C) C where forget₂ := total β C

end GradedObject

end CategoryTheory

