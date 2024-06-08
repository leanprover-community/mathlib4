/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

#align_import category_theory.limits.shapes.strict_initial from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Strict initial objects

This file sets up the basic theory of strict initial objects: initial objects where every morphism
to it is an isomorphism. This generalises a property of the empty set in the category of sets:
namely that the only function to the empty set is from itself.

We say `C` has strict initial objects if every initial object is strict, ie given any morphism
`f : A ⟶ I` where `I` is initial, then `f` is an isomorphism.
Strictly speaking, this says that *any* initial object must be strict, rather than that strict
initial objects exist, which turns out to be a more useful notion to formalise.

If the binary product of `X` with a strict initial object exists, it is also initial.

To show a category `C` with an initial object has strict initial objects, the most convenient way
is to show any morphism to the (chosen) initial object is an isomorphism and use
`hasStrictInitialObjects_of_initial_is_strict`.

The dual notion (strict terminal objects) occurs much less frequently in practice so is ignored.

## TODO

* Construct examples of this: `Type*`, `TopCat`, `Groupoid`, simplicial types, posets.
* Construct the bottom element of the subobject lattice given strict initials.
* Show cartesian closed categories have strict initials

## References
* https://ncatlab.org/nlab/show/strict+initial+object
-/


universe v u

namespace CategoryTheory

namespace Limits

open Category

variable (C : Type u) [Category.{v} C]

section StrictInitial

/-- We say `C` has strict initial objects if every initial object is strict, ie given any morphism
`f : A ⟶ I` where `I` is initial, then `f` is an isomorphism.

Strictly speaking, this says that *any* initial object must be strict, rather than that strict
initial objects exist.
-/
class HasStrictInitialObjects : Prop where
  out : ∀ {I A : C} (f : A ⟶ I), IsInitial I → IsIso f
#align category_theory.limits.has_strict_initial_objects CategoryTheory.Limits.HasStrictInitialObjects

variable {C}

section

variable [HasStrictInitialObjects C] {I : C}

theorem IsInitial.isIso_to (hI : IsInitial I) {A : C} (f : A ⟶ I) : IsIso f :=
  HasStrictInitialObjects.out f hI
#align category_theory.limits.is_initial.is_iso_to CategoryTheory.Limits.IsInitial.isIso_to

theorem IsInitial.strict_hom_ext (hI : IsInitial I) {A : C} (f g : A ⟶ I) : f = g := by
  haveI := hI.isIso_to f
  haveI := hI.isIso_to g
  exact eq_of_inv_eq_inv (hI.hom_ext (inv f) (inv g))
#align category_theory.limits.is_initial.strict_hom_ext CategoryTheory.Limits.IsInitial.strict_hom_ext

theorem IsInitial.subsingleton_to (hI : IsInitial I) {A : C} : Subsingleton (A ⟶ I) :=
  ⟨hI.strict_hom_ext⟩
#align category_theory.limits.is_initial.subsingleton_to CategoryTheory.Limits.IsInitial.subsingleton_to

instance (priority := 100) initial_mono_of_strict_initial_objects : InitialMonoClass C where
  isInitial_mono_from := fun _ hI => { right_cancellation := fun _ _ _ => hI.strict_hom_ext _ _ }
#align category_theory.limits.initial_mono_of_strict_initial_objects CategoryTheory.Limits.initial_mono_of_strict_initial_objects

/-- If `I` is initial, then `X ⨯ I` is isomorphic to it. -/
@[simps! hom]
noncomputable def mulIsInitial (X : C) [HasBinaryProduct X I] (hI : IsInitial I) : X ⨯ I ≅ I := by
  have := hI.isIso_to (prod.snd : X ⨯ I ⟶ I)
  exact asIso prod.snd
#align category_theory.limits.mul_is_initial CategoryTheory.Limits.mulIsInitial

@[simp]
theorem mulIsInitial_inv (X : C) [HasBinaryProduct X I] (hI : IsInitial I) :
    (mulIsInitial X hI).inv = hI.to _ :=
  hI.hom_ext _ _
#align category_theory.limits.mul_is_initial_inv CategoryTheory.Limits.mulIsInitial_inv

/-- If `I` is initial, then `I ⨯ X` is isomorphic to it. -/
@[simps! hom]
noncomputable def isInitialMul (X : C) [HasBinaryProduct I X] (hI : IsInitial I) : I ⨯ X ≅ I := by
   have := hI.isIso_to (prod.fst : I ⨯ X ⟶ I)
   exact asIso prod.fst
#align category_theory.limits.is_initial_mul CategoryTheory.Limits.isInitialMul

@[simp]
theorem isInitialMul_inv (X : C) [HasBinaryProduct I X] (hI : IsInitial I) :
    (isInitialMul X hI).inv = hI.to _ :=
  hI.hom_ext _ _
#align category_theory.limits.is_initial_mul_inv CategoryTheory.Limits.isInitialMul_inv

variable [HasInitial C]

instance initial_isIso_to {A : C} (f : A ⟶ ⊥_ C) : IsIso f :=
  initialIsInitial.isIso_to _
#align category_theory.limits.initial_is_iso_to CategoryTheory.Limits.initial_isIso_to

@[ext]
theorem initial.strict_hom_ext {A : C} (f g : A ⟶ ⊥_ C) : f = g :=
  initialIsInitial.strict_hom_ext _ _
#align category_theory.limits.initial.hom_ext CategoryTheory.Limits.initial.hom_ext

theorem initial.subsingleton_to {A : C} : Subsingleton (A ⟶ ⊥_ C) :=
  initialIsInitial.subsingleton_to
#align category_theory.limits.initial.subsingleton_to CategoryTheory.Limits.initial.subsingleton_to

/-- The product of `X` with an initial object in a category with strict initial objects is itself
initial.
This is the generalisation of the fact that `X × Empty ≃ Empty` for types (or `n * 0 = 0`).
-/
@[simps! hom]
noncomputable def mulInitial (X : C) [HasBinaryProduct X (⊥_ C)] : X ⨯ ⊥_ C ≅ ⊥_ C :=
  mulIsInitial _ initialIsInitial
#align category_theory.limits.mul_initial CategoryTheory.Limits.mulInitial

@[simp]
theorem mulInitial_inv (X : C) [HasBinaryProduct X (⊥_ C)] : (mulInitial X).inv = initial.to _ :=
  Subsingleton.elim _ _
#align category_theory.limits.mul_initial_inv CategoryTheory.Limits.mulInitial_inv

/-- The product of `X` with an initial object in a category with strict initial objects is itself
initial.
This is the generalisation of the fact that `Empty × X ≃ Empty` for types (or `0 * n = 0`).
-/
@[simps! hom]
noncomputable def initialMul (X : C) [HasBinaryProduct (⊥_ C) X] : (⊥_ C) ⨯ X ≅ ⊥_ C :=
  isInitialMul _ initialIsInitial
#align category_theory.limits.initial_mul CategoryTheory.Limits.initialMul

@[simp]
theorem initialMul_inv (X : C) [HasBinaryProduct (⊥_ C) X] : (initialMul X).inv = initial.to _ :=
  Subsingleton.elim _ _
#align category_theory.limits.initial_mul_inv CategoryTheory.Limits.initialMul_inv

end

/-- If `C` has an initial object such that every morphism *to* it is an isomorphism, then `C`
has strict initial objects. -/
theorem hasStrictInitialObjects_of_initial_is_strict [HasInitial C]
    (h : ∀ (A) (f : A ⟶ ⊥_ C), IsIso f) : HasStrictInitialObjects C :=
  { out := fun {I A} f hI =>
      haveI := h A (f ≫ hI.to _)
      ⟨⟨hI.to _ ≫ inv (f ≫ hI.to (⊥_ C)), by rw [← assoc, IsIso.hom_inv_id], hI.hom_ext _ _⟩⟩ }
#align category_theory.limits.has_strict_initial_objects_of_initial_is_strict CategoryTheory.Limits.hasStrictInitialObjects_of_initial_is_strict

end StrictInitial

section StrictTerminal

/-- We say `C` has strict terminal objects if every terminal object is strict, ie given any morphism
`f : I ⟶ A` where `I` is terminal, then `f` is an isomorphism.

Strictly speaking, this says that *any* terminal object must be strict, rather than that strict
terminal objects exist.
-/
class HasStrictTerminalObjects : Prop where
  out : ∀ {I A : C} (f : I ⟶ A), IsTerminal I → IsIso f
#align category_theory.limits.has_strict_terminal_objects CategoryTheory.Limits.HasStrictTerminalObjects

variable {C}

section

variable [HasStrictTerminalObjects C] {I : C}

theorem IsTerminal.isIso_from (hI : IsTerminal I) {A : C} (f : I ⟶ A) : IsIso f :=
  HasStrictTerminalObjects.out f hI
#align category_theory.limits.is_terminal.is_iso_from CategoryTheory.Limits.IsTerminal.isIso_from

theorem IsTerminal.strict_hom_ext (hI : IsTerminal I) {A : C} (f g : I ⟶ A) : f = g := by
  haveI := hI.isIso_from f
  haveI := hI.isIso_from g
  exact eq_of_inv_eq_inv (hI.hom_ext (inv f) (inv g))
#align category_theory.limits.is_terminal.strict_hom_ext CategoryTheory.Limits.IsTerminal.strict_hom_ext

theorem IsTerminal.subsingleton_to (hI : IsTerminal I) {A : C} : Subsingleton (I ⟶ A) :=
  ⟨hI.strict_hom_ext⟩
#align category_theory.limits.is_terminal.subsingleton_to CategoryTheory.Limits.IsTerminal.subsingleton_to

variable {J : Type v} [SmallCategory J]

/-- If all but one object in a diagram is strict terminal, then the limit is isomorphic to the
said object via `limit.π`. -/
theorem limit_π_isIso_of_is_strict_terminal (F : J ⥤ C) [HasLimit F] (i : J)
    (H : ∀ (j) (_ : j ≠ i), IsTerminal (F.obj j)) [Subsingleton (i ⟶ i)] : IsIso (limit.π F i) := by
  classical
    refine ⟨⟨limit.lift _ ⟨_, ⟨?_, ?_⟩⟩, ?_, ?_⟩⟩
    · exact fun j =>
        dite (j = i)
          (fun h => eqToHom (by cases h; rfl))
          fun h => (H _ h).from _
    · intro j k f
      split_ifs with h h_1 h_1
      · cases h
        cases h_1
        obtain rfl : f = 𝟙 _ := Subsingleton.elim _ _
        simp
      · cases h
        erw [Category.comp_id]
        haveI : IsIso (F.map f) := (H _ h_1).isIso_from _
        rw [← IsIso.comp_inv_eq]
        apply (H _ h_1).hom_ext
      · cases h_1
        apply (H _ h).hom_ext
      · apply (H _ h).hom_ext
    · ext
      rw [assoc, limit.lift_π]
      dsimp only
      split_ifs with h
      · cases h
        rw [id_comp, eqToHom_refl]
        exact comp_id _
      · apply (H _ h).hom_ext
    · rw [limit.lift_π]
      simp
#align category_theory.limits.limit_π_is_iso_of_is_strict_terminal CategoryTheory.Limits.limit_π_isIso_of_is_strict_terminal

variable [HasTerminal C]

instance terminal_isIso_from {A : C} (f : ⊤_ C ⟶ A) : IsIso f :=
  terminalIsTerminal.isIso_from _
#align category_theory.limits.terminal_is_iso_from CategoryTheory.Limits.terminal_isIso_from

@[ext]
theorem terminal.strict_hom_ext {A : C} (f g : ⊤_ C ⟶ A) : f = g :=
  terminalIsTerminal.strict_hom_ext _ _
#align category_theory.limits.terminal.hom_ext CategoryTheory.Limits.terminal.hom_ext

theorem terminal.subsingleton_to {A : C} : Subsingleton (⊤_ C ⟶ A) :=
  terminalIsTerminal.subsingleton_to
#align category_theory.limits.terminal.subsingleton_to CategoryTheory.Limits.terminal.subsingleton_to

end

/-- If `C` has an object such that every morphism *from* it is an isomorphism, then `C`
has strict terminal objects. -/
theorem hasStrictTerminalObjects_of_terminal_is_strict (I : C) (h : ∀ (A) (f : I ⟶ A), IsIso f) :
    HasStrictTerminalObjects C :=
  { out := fun {I' A} f hI' =>
      haveI := h A (hI'.from _ ≫ f)
      ⟨⟨inv (hI'.from I ≫ f) ≫ hI'.from I, hI'.hom_ext _ _, by rw [assoc, IsIso.inv_hom_id]⟩⟩ }
#align category_theory.limits.has_strict_terminal_objects_of_terminal_is_strict CategoryTheory.Limits.hasStrictTerminalObjects_of_terminal_is_strict

end StrictTerminal

end Limits

end CategoryTheory
