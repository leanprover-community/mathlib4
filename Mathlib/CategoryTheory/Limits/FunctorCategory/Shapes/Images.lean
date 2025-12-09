/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.Subpresheaf.Image
public import Mathlib.Tactic.CategoryTheory.CategoryStar

/-!

# The category of type-valued functors has images
-/

@[expose] public section

universe u

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]

attribute [local simp] FunctorToTypes.naturality in
/-- The image of a natural transformation between type-valued functors is a `MonoFactorisation` -/
@[simps]
def NatTrans.monoFactorisation {F G : C ⥤ Type u} (f : F ⟶ G) : MonoFactorisation f where
  I := (Subpresheaf.range f).toPresheaf
  m := (Subpresheaf.range f).ι
  e := Subpresheaf.toRange f

/-- The image of a natural transformation between type-valued functors satisfies the universal
property of images -/
noncomputable def NatTrans.monoFactorisationIsImage {F G : C ⥤ Type u} (f : F ⟶ G) :
    IsImage f.monoFactorisation where
  lift H := {
    app X := fun ⟨x, hx⟩ ↦ H.e.app _ hx.choose
    naturality X Y g := by
      ext ⟨⟩
      apply show Function.Injective (H.m.app Y) by rw [← mono_iff_injective]; infer_instance
      simp only [monoFactorisation_I, Subpresheaf.toPresheaf_obj, Subpresheaf.range_obj,
        types_comp_apply, Subpresheaf.toPresheaf_map_coe, MonoFactorisation.fac_apply,
        FunctorToTypes.naturality]
      generalize_proofs h₁ h₂
      rw [h₁.choose_spec, h₂.choose_spec] }
  lift_fac H := by
    ext
    simp only [monoFactorisation_I, Subpresheaf.toPresheaf_obj, Subpresheaf.range_obj,
      FunctorToTypes.comp, MonoFactorisation.fac_apply, monoFactorisation_m, Subpresheaf.ι_app]
    generalize_proofs h
    exact h.choose_spec

instance : HasImages (C ⥤ Type*) where
  has_image f := { exists_image := ⟨ { F := _, isImage := f.monoFactorisationIsImage } ⟩ }

instance : HasStrongEpiMonoFactorisations (C ⥤ Type*) where
  has_fac {F G} f := ⟨{ I := image f, m := image.ι f, e := factorThruImage f }⟩

end CategoryTheory
