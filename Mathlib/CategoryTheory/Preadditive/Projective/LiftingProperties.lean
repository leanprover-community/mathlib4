/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# Characterization of projective objects in terms of lifting properties

An object `P` is projective iff the morphism `0 ⟶ P` has the
left lifting property with respect to epimorphisms,
`projective_iff_llp_epimorphisms_zero`.

-/

universe v u

namespace CategoryTheory

open Limits ZeroObject

variable {C : Type u} [Category.{v} C]

namespace Projective

lemma hasLiftingProperty_of_isZero
    {Z P X Y : C} (i : Z ⟶ P) (p : X ⟶ Y) [Epi p] [Projective P] (hZ : IsZero Z) :
    HasLiftingProperty i p where
  sq_hasLift {f g} sq := ⟨⟨{
    l := Projective.factorThru g p
    fac_left := hZ.eq_of_src _ _ }⟩⟩

instance {X Y P : C} (p : X ⟶ Y) [Epi p] [Projective P] [HasZeroObject C] (i : 0 ⟶ P) :
    HasLiftingProperty (i : 0 ⟶ P) p :=
  Projective.hasLiftingProperty_of_isZero i p (isZero_zero C)

end Projective

lemma projective_iff_llp_epimorphisms_of_isZero
    [HasZeroMorphisms C] {P Z : C} (i : Z ⟶ P) (hZ : IsZero Z) :
    Projective P ↔ (MorphismProperty.epimorphisms C).llp i := by
  obtain rfl := hZ.eq_of_src i 0
  constructor
  · intro _ X Y p (_ : Epi p)
    exact Projective.hasLiftingProperty_of_isZero 0 p hZ
  · intro h
    constructor
    intro X Y f p hp
    have := h _ hp
    have sq : CommSq 0 (0 : Z ⟶ P) p f := ⟨by simp⟩
    exact ⟨sq.lift, by simp⟩

lemma projective_iff_llp_epimorphisms_zero
    [HasZeroMorphisms C] [HasZeroObject C] (P : C) :
    Projective P ↔ (MorphismProperty.epimorphisms C).llp (0 : 0 ⟶ P) :=
  projective_iff_llp_epimorphisms_of_isZero _ (isZero_zero C)

end CategoryTheory
