/-
Copyright (c) 2024 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
import Mathlib.AlgebraicGeometry.Scheme

def CategoryTheory.Limits.CoconeOfIso
    {J : Type*} [Category J] {C : Type*} [Category C]
    (c : C) (F : Functor J C) (f : ∀ (j : J), F.obj j ≅ c)
    (h : ∀ (j1 j2 : J) (l : j1 ⟶ j2), CategoryStruct.comp (F.map l) (f j2).hom = (f j1).hom) :
    Limits.Cocone F where
  pt := c
  ι := ⟨fun j ↦ (f j).hom, by simpa only [Functor.const_obj_obj, Functor.const_obj_map,
    Category.comp_id] using h⟩

noncomputable def CategoryTheory.Limits.CoconeOfIso.isColimitOfHasInitial
    {J : Type*} [Category J] [Limits.HasInitial J]
    {C : Type*} [Category C] (c : C) (F : Functor J C) (f : ∀ (j : J), F.obj j ≅ c)
    (h : ∀ (j1 j2 : J) (l : j1 ⟶ j2), CategoryStruct.comp (F.map l) (f j2).hom = (f j1).hom) :
    Limits.IsColimit (Limits.CoconeOfIso c F f h) where
  desc := fun s ↦ CategoryStruct.comp (f (Limits.initial J)).inv (s.ι.app (Limits.initial J))
  fac := fun s j ↦ by
    unfold CoconeOfIso
    rw [← Iso.eq_inv_comp, Iso.inv_comp_eq, (h (⊥_ J) j (initial.to j)).symm]
    simp only [Functor.const_obj_obj, Category.assoc, Iso.hom_inv_id_assoc, NatTrans.naturality,
      Functor.const_obj_map, Category.comp_id]
  uniq := fun s m h1 ↦ by simp_rw [← h1 (⊥_ J)]; erw [Iso.inv_hom_id_assoc]

theorem TopologicalSpace.OpenNhds.op_top_eq_initial {X : TopCat} (x : X) :
    Opposite.op (⊤ : TopologicalSpace.OpenNhds x) = ⊥_ (TopologicalSpace.OpenNhds x)ᵒᵖ := by
  have : CategoryTheory.Limits.IsInitial (Opposite.op (⊤ : TopologicalSpace.OpenNhds x)) := {
    desc := fun s ↦ CategoryTheory.opHomOfLE le_top
    fac := by simp only [CategoryTheory.Limits.asEmptyCocone_pt,
      CategoryTheory.Functor.const_obj_obj, CategoryTheory.Limits.asEmptyCocone_ι_app,
      CategoryTheory.Discrete.mk_as, id_eq, IsEmpty.forall_iff, implies_true]
    uniq := fun _ _ _ ↦ rfl
  }
  exact Opposite.op_eq_iff_eq_unop.mpr (Eq.symm (eq_top_iff.2 fun x hx ↦
    ((CategoryTheory.Limits.IsInitial.uniqueUpToIso this
    CategoryTheory.Limits.initialIsInitial).inv.unop ⟨x, hx⟩).2))
