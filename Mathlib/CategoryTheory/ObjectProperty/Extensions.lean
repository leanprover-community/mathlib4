/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.SetLike

/-!
# Properties of objects that are closed under extensions

Given a category `C` and `P : ObjectProperty C`, we define a type
class `P.IsClosedUnderExtensions` expressing that the property
is closed under extensions.

-/

@[expose] public section

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
    hS.exact.isZero_of_both_zeros (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

instance [P.IsClosedUnderExtensions] (F : D ⥤ C)
    [HasZeroMorphisms D] [F.PreservesZeroMorphisms]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (P.inverseImage F).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := by
    have := hS.mono_f
    have := hS.epi_g
    exact P.prop_X₂_of_shortExact (hS.map F) h₁ h₃

end

lemma prop_biprod {X₁ X₂ : C} (h₁ : P X₁) (h₂ : P X₂) [Preadditive C] [HasZeroObject C]
    [P.IsClosedUnderExtensions] [HasBinaryBiproduct X₁ X₂] :
    P (X₁ ⊞ X₂) :=
  P.prop_X₂_of_shortExact
    (ShortComplex.Splitting.ofHasBinaryBiproduct X₁ X₂).shortExact h₁ h₂

end ObjectProperty

end CategoryTheory
