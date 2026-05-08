/-
Copyright (c) 2026 Nailin Guan, Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Jingting Wang
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.MorphismProperty.Ind
public import Mathlib.CategoryTheory.SmallObject.Iteration.Nonempty
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.RingHom.Flat

/-!

# Filtered colimit of local ring via local homomorphisms is local ring

In this file, we deal with filtered colimit of local ring via local homomorphisms, proving it is
again local, with maximal ideal equal to the union of images of maximal ideals.

# Main results

* `CommRingCat.FilteredColimit.isLocalRing_of_isColimit` : Filtered colimit of local ring
  via local homomorphisms is local ring.

* `CommRingCat.FilteredColimit.maximalIdeal_eq_iUnion_of_isColimit` : Filtered colimit of local ring
  via local homomorphisms has maximal ideal equal to union of images of maximal ideals.

-/

@[expose] public section

universe u v w

open IsLocalRing CategoryTheory SmallObject Limits

open Polynomial

variable (R : Type u) [CommRing R]

open CategoryTheory Limits IsLocalRing

variable {J : Type u} [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{u}) {c : Cocone F}
  [h_obj : ∀ (j : J), IsLocalRing (F.obj j)]
  [h_hom : ∀ (j j' : J) (f : j ⟶ j'), IsLocalHom (F.map f).hom]

namespace CommRingCat.FilteredColimit

theorem isLocalRing_of_isColimit (hc : IsColimit c) : IsLocalRing c.pt := by
  sorry

lemma maximalIdeal_eq_iUnion_of_isColimit (hc : IsColimit c) :
    (isLocalRing_of_isColimit F hc).maximalIdeal =
    ⋃ (j : J), ((c.ι.app j) '' (maximalIdeal (F.obj j)) : Set c.pt) := by
  sorry

omit h_obj in
lemma isLocalHom_ι (hc : IsColimit c) (j : J) : IsLocalHom (c.ι.app j).hom := by
  sorry

end CommRingCat.FilteredColimit
