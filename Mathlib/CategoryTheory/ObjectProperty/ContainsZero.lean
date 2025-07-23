/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Properties of objects which hold for a zero object

Given a category `C` and `P : ObjectProperty C`, we define a type class `P.ContainsZero`
expressing that there exists a zero object for which `P` holds. (We do not require
that `P` holds for all zero objects, as in some applications (e.g. triangulated categories),
`P` may not necessarily be closed under isomorphisms.)

-/

universe v v' u u'

namespace CategoryTheory

open Limits ZeroObject

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace ObjectProperty

variable (P : ObjectProperty C)

/-- Given `P : ObjectProperty C`, we say that `P.ContainsZero` if there exists
a zero object for which `P` holds. When `P` is closed under isomorphisms,
this holds for any zero object. -/
class ContainsZero : Prop where
  exists_zero : ∃ (Z : C), IsZero Z ∧ P Z

lemma exists_prop_of_containsZero [P.ContainsZero] :
    ∃ (Z : C), IsZero Z ∧ P Z :=
  ContainsZero.exists_zero

lemma prop_of_isZero [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    {Z : C} (hZ : IsZero Z) :
    P Z := by
  obtain ⟨Z₀, hZ₀, h₀⟩ := P.exists_prop_of_containsZero
  exact P.prop_of_iso (hZ₀.iso hZ) h₀

lemma prop_zero [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [HasZeroObject C] :
    P 0 :=
  P.prop_of_isZero (isZero_zero C)

instance [HasZeroObject C] : (⊤ : ObjectProperty C).ContainsZero where
  exists_zero := ⟨0, isZero_zero C, by simp⟩

instance [HasZeroObject C] : ContainsZero (IsZero (C := C)) where
  exists_zero := ⟨0, isZero_zero C, isZero_zero C⟩

instance [P.ContainsZero] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] : (P.map F).ContainsZero where
  exists_zero := by
    obtain ⟨Z, h₁, h₂⟩ := P.exists_prop_of_containsZero
    exact ⟨F.obj Z, F.map_isZero h₁, P.prop_map_obj F h₂⟩

instance [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : D ⥤ C) [F.PreservesZeroMorphisms] [HasZeroObject D] :
    (P.inverseImage F).ContainsZero where
  exists_zero :=
    ⟨0, isZero_zero D, P.prop_of_isZero (F.map_isZero (isZero_zero D))⟩

instance [P.ContainsZero] : P.isoClosure.ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ, hP⟩ := P.exists_prop_of_containsZero
    exact ⟨Z, hZ, P.le_isoClosure _ hP⟩

end ObjectProperty

/-- Given a functor `F : C ⥤ D`, this is the property of objects of `C`
satisfies by those `X : C` such that `IsZero (F.obj X)`. -/
abbrev Functor.kernel (F : C ⥤ D) : ObjectProperty C :=
  ObjectProperty.inverseImage IsZero F

end CategoryTheory
