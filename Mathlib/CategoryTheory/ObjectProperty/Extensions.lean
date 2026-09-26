/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Opposite

/-!
# Properties of objects that are closed under extensions

Given a category `C` and `P : ObjectProperty C`, we define a type
class `P.IsClosedUnderExtensions` expressing that the property
is closed under extensions. We also show that this condition is self-dual:
`P.op` is closed under extensions iff `P` is.

-/

public section

universe v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace ObjectProperty

variable (P : ObjectProperty C)

section

variable [HasZeroMorphisms C]

/-- Given `P : ObjectProperty C`, we say that `P` is closed under extensions
if whenever `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` is a short exact short complex,
then `P X₁` and `P X₃` implies `P X₂`. -/
class IsClosedUnderExtensions : Prop where
  prop_X₂_of_shortExact {S : ShortComplex C} (hS : S.ShortExact)
      (h₁ : P S.X₁) (h₃ : P S.X₃) : P S.X₂

lemma prop_X₂_of_shortExact [P.IsClosedUnderExtensions]
    {S : ShortComplex C} (hS : S.ShortExact)
    (h₁ : P S.X₁) (h₃ : P S.X₃) : P S.X₂ :=
  IsClosedUnderExtensions.prop_X₂_of_shortExact hS h₁ h₃

instance : (⊤ : ObjectProperty C).IsClosedUnderExtensions where
  prop_X₂_of_shortExact := by simp

instance : IsClosedUnderExtensions (IsZero (C := C)) where
  prop_X₂_of_shortExact hS h₁ h₃ :=
    hS.exact.isZero_of_both_isZero h₁ h₃

instance [P.IsClosedUnderExtensions] (F : D ⥤ C)
    [HasZeroMorphisms D] [F.PreservesZeroMorphisms]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (P.inverseImage F).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := by
    have := hS.mono_f
    have := hS.epi_g
    exact P.prop_X₂_of_shortExact (hS.map F) h₁ h₃

section Opposite

/-- A property of objects `P.op` is closed under extensions iff `P` is, since a short
complex in `Cᵒᵖ` is short exact iff the corresponding short complex in `C` is. -/
lemma isClosedUnderExtensions_op_iff :
    P.op.IsClosedUnderExtensions ↔ P.IsClosedUnderExtensions :=
  ⟨fun h ↦ ⟨fun hS h₁ h₃ ↦ h.prop_X₂_of_shortExact hS.op h₃ h₁⟩,
    fun h ↦ ⟨fun hS h₁ h₃ ↦ h.prop_X₂_of_shortExact hS.unop h₃ h₁⟩⟩

instance [P.IsClosedUnderExtensions] : P.op.IsClosedUnderExtensions := by
  rwa [isClosedUnderExtensions_op_iff]

/-- A property of objects `Q.unop` is closed under extensions iff `Q` is. -/
lemma isClosedUnderExtensions_unop_iff (Q : ObjectProperty Cᵒᵖ) :
    Q.unop.IsClosedUnderExtensions ↔ Q.IsClosedUnderExtensions :=
  Q.unop.isClosedUnderExtensions_op_iff.symm

instance (Q : ObjectProperty Cᵒᵖ) [Q.IsClosedUnderExtensions] :
    Q.unop.IsClosedUnderExtensions := by
  rwa [isClosedUnderExtensions_unop_iff]

end Opposite

end

lemma prop_biprod {X₁ X₂ : C} (h₁ : P X₁) (h₂ : P X₂) [Preadditive C] [HasZeroObject C]
    [P.IsClosedUnderExtensions] [HasBinaryBiproduct X₁ X₂] :
    P (X₁ ⊞ X₂) :=
  P.prop_X₂_of_shortExact
    (ShortComplex.Splitting.ofHasBinaryBiproduct X₁ X₂).shortExact h₁ h₂

end ObjectProperty

end CategoryTheory
