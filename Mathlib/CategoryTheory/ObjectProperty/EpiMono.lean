/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Properties of objects that are stable under subobjects and quotients

Given a category `C` and `P : ObjectProperty C`, we define type classes
`P.IsStableUnderSubobjects` and `P.IsStableUnderQuotients` expressing
that `P` is stable under subobjects (resp. quotients).

-/

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace ObjectProperty

variable (P : ObjectProperty C)

/-- Given `P : ObjectProperty C`, we say that `P` is stable under subobjects,
if for any monomorphism `X ⟶ Y`, `P Y` implies `P X`. -/
class IsStableUnderSubobjects : Prop where
  prop_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (hY : P Y) : P X

section

variable [P.IsStableUnderSubobjects]

lemma prop_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (hY : P Y) : P X :=
  IsStableUnderSubobjects.prop_of_mono f hY

instance : P.IsClosedUnderIsomorphisms where
  of_iso e := P.prop_of_mono e.inv

lemma prop_X₁_of_shortExact [HasZeroMorphisms C] {S : ShortComplex C} (hS : S.ShortExact)
    (h₂ : P S.X₂) : P S.X₁ := by
  have := hS.mono_f
  exact P.prop_of_mono S.f h₂

end

section

/-- Given `P : ObjectProperty C`, we say that `P` is stable under quotients,
if for any epimorphism `X ⟶ Y`, `P X` implies `P Y`. -/
class IsStableUnderQuotients : Prop where
  prop_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (hX : P X) : P Y

variable [P.IsStableUnderQuotients]

lemma prop_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (hX : P X) : P Y :=
  IsStableUnderQuotients.prop_of_epi f hX

instance : P.IsClosedUnderIsomorphisms where
  of_iso e := P.prop_of_epi e.hom

lemma prop_X₃_of_shortExact [HasZeroMorphisms C] {S : ShortComplex C} (hS : S.ShortExact)
    (h₂ : P S.X₂) : P S.X₃ := by
  have := hS.epi_g
  exact P.prop_of_epi S.g h₂

end

instance : (⊤ : ObjectProperty C).IsStableUnderSubobjects where
  prop_of_mono := by simp

instance : (⊤ : ObjectProperty C).IsStableUnderQuotients where
  prop_of_epi := by simp

instance [HasZeroMorphisms C] : IsStableUnderSubobjects (IsZero (C := C)) where
  prop_of_mono f _ hX := IsZero.of_mono f hX

instance [HasZeroMorphisms C] : IsStableUnderQuotients (IsZero (C := C)) where
  prop_of_epi f _ hX := IsZero.of_epi f hX

end ObjectProperty

end CategoryTheory
