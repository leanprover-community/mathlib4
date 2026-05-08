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
public import Mathlib.Algebra.Category.Ring.FilteredColimits

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


namespace CommRingCat.FilteredColimit

lemma nonunits_le_of_isColimit (hc : IsColimit c) :
    (nonunits c.pt : Set _) ≤ ⋃ (j : J), (c.ι.app j) '' (nonunits (F.obj j)) := by
  intro x hx
  obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep F hc x
  exact Set.mem_iUnion.mpr ⟨j, ⟨y, fun h ↦ hx (h.map _), rfl⟩⟩

variable [h_hom : ∀ (j j' : J) (f : j ⟶ j'), IsLocalHom (F.map f).hom]

lemma isLocalHom_ι (hc : IsColimit c) (j : J) :
    IsLocalHom (c.ι.app j).hom := by
  apply IsLocalHom.mk
  rintro x ⟨y, hy⟩
  obtain ⟨j1, z, hz⟩ := Concrete.isColimit_exists_rep F hc (y⁻¹).1
  obtain ⟨j2, f', g', _⟩ := IsFilteredOrEmpty.cocone_objs j j1
  have : (c.ι.app j2).hom ((F.map f' x) * (F.map g' z)) = (c.ι.app j2).hom 1 := by
    simp only [map_mul, map_one, ← comp_apply]
    simp only [Functor.const_obj_obj, Cocone.w]
    convert y.mul_inv
    exact hy.symm
  obtain ⟨j3, f3, g3, hfg3⟩ := Concrete.isColimit_exists_of_rep_eq F hc _ _ this
  obtain ⟨j4, i4, h4⟩ := IsFilteredOrEmpty.cocone_maps f3 g3
  refine isUnit_of_map_unit (F.map (f' ≫ f3 ≫ i4)).hom x <| isUnit_iff_exists_inv.mpr <|
    ⟨(F.map (g' ≫ g3 ≫ i4)).hom z, h4 ▸ ?_⟩
  simpa using congr((F.map i4).hom $hfg3)

set_option backward.isDefEq.respectTransparency false in
lemma nonunits_eq_iUnion_of_isColimit (hc : IsColimit c) :
    (nonunits c.pt : Set _) = ⋃ (j : J), (c.ι.app j) '' (nonunits (F.obj j)) := by
  apply le_antisymm (nonunits_le_of_isColimit F hc) (fun x hx ↦ ?_)
  obtain ⟨j, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
  have := isLocalHom_ι F hc j
  exact (map_mem_nonunits_iff _ _).mpr hy

variable [h_obj : ∀ (j : J), IsLocalRing (F.obj j)]

theorem isLocalRing_of_isColimit (hc : IsColimit c) : IsLocalRing c.pt := by
  have : Nontrivial c.pt := FilteredColimits.nontrivial (c := c) hc
  have h_nonunits_eq := nonunits_eq_iUnion_of_isColimit F hc
  have h_isLocalHom := isLocalHom_ι F hc
  refine IsLocalRing.of_nonunits_add (fun a b ha hb ↦ h_nonunits_eq ▸ (Set.mem_iUnion.mpr ?_))
  simp only [h_nonunits_eq, Functor.const_obj_obj, Set.mem_iUnion, Set.mem_image] at ha hb
  obtain ⟨j, a, ha, rfl⟩ := ha
  obtain ⟨j', b, hb, rfl⟩ := hb
  obtain ⟨j'', f, g, _⟩ := IsFilteredOrEmpty.cocone_objs j j'
  refine ⟨j'', ⟨F.map f a + F.map g b, (h_obj j'').nonunits_add
    ((map_mem_nonunits_iff _ _).mpr ha) ((map_mem_nonunits_iff _ _).mpr hb), ?_⟩⟩
  simp only [map_add, ← comp_apply]
  simp only [Functor.const_obj_obj, Cocone.w c]
  rfl

lemma maximalIdeal_eq_iUnion_of_isColimit (hc : IsColimit c) :
    (isLocalRing_of_isColimit F hc).maximalIdeal =
    ⋃ (j : J), ((c.ι.app j) '' (maximalIdeal (F.obj j)) : Set c.pt) :=
  nonunits_eq_iUnion_of_isColimit F hc

lemma maximalIdeal_eq_iSup_of_isColimit (hc : IsColimit c) :
    (isLocalRing_of_isColimit F hc).maximalIdeal =
    ⨆ (j : J), ((maximalIdeal (F.obj j)).map (c.ι.app j).hom : Ideal c.pt) := by
  refine le_antisymm ?_ (iSup_le fun j ↦ ?_)
  · apply (maximalIdeal_eq_iUnion_of_isColimit F hc).trans_le
    apply Set.iUnion_subset fun j ↦ le_trans ?_ (SetLike.coe_mono (le_iSup _ j))
    exact Ideal.subset_span
  · have : IsLocalRing (((Functor.const J).obj c.pt).obj j) := isLocalRing_of_isColimit F hc
    exact ((IsLocalRing.local_hom_TFAE (c.ι.app j).hom).out 0 2).mp (isLocalHom_ι F hc j)

end CommRingCat.FilteredColimit
