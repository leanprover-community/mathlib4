/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Thomas Read, Andrew Yang, Dagur Asgeirsson, Joël Riou
-/
import Mathlib.CategoryTheory.Adjunction.Basic
/-!

# Uniqueness of adjoints

This file shows that adjoints are unique up to natural isomorphism.

## Main results
* `Adjunction.natTransEquiv` and `Adjunction.natIsoEquiv` If `F ⊣ G` and `F' ⊣ G'` are adjunctions,
  then there are equivalences `(G ⟶ G') ≃ (F' ⟶ F)` and `(G ≅ G') ≃ (F' ≅ F)`.
Everything else is deduced from this:

* `Adjunction.leftAdjointUniq` : If `F` and `F'` are both left adjoint to `G`, then they are
  naturally isomorphic.

* `Adjunction.rightAdjointUniq` : If `G` and `G'` are both right adjoint to `F`, then they are
  naturally isomorphic.
-/

open CategoryTheory

variable {C D : Type*} [Category C] [Category D]

namespace CategoryTheory.Adjunction

/--
If `F ⊣ G` and `F' ⊣ G'` are adjunctions, then giving a natural transformation `G ⟶ G'` is the
same as giving a natural transformation `F' ⟶ F`.
-/
@[simps]
def natTransEquiv {F F' : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G') :
    (G ⟶ G') ≃ (F' ⟶ F) where
  toFun f := {
    app := fun X ↦ F'.map ((adj1.unit ≫ whiskerLeft F f).app X) ≫ adj2.counit.app _
    naturality := by
      intro X Y g
      simp only [← Category.assoc, ← Functor.map_comp]
      erw [(adj1.unit ≫ (whiskerLeft F f)).naturality]
      simp
  }
  invFun f := {
    app := fun X ↦ adj2.unit.app (G.obj X) ≫ G'.map (f.app (G.obj X) ≫ adj1.counit.app X)
    naturality := by
      intro X Y g
      erw [← adj2.unit_naturality_assoc]
      simp only [← Functor.map_comp]
      simp
  }
  left_inv f := by
    ext X
    simp only [Functor.comp_obj, NatTrans.comp_app, Functor.id_obj, whiskerLeft_app,
      Functor.map_comp, Category.assoc, unit_naturality_assoc, right_triangle_components_assoc]
    erw [← f.naturality (adj1.counit.app X), ← Category.assoc]
    simp
  right_inv f := by
    ext
    simp

@[simp]
lemma natTransEquiv_id {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    natTransEquiv adj adj (𝟙 _) = 𝟙 _ := by ext; simp

@[simp]
lemma natTransEquiv_id_symm {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    (natTransEquiv adj adj).symm (𝟙 _) = 𝟙 _ := by ext; simp

@[simp]
lemma natTransEquiv_comp {F F' F'' : C ⥤ D} {G G' G'' : D ⥤ C}
    (adj1 : F ⊣ G) (adj2 : F' ⊣ G') (adj3 : F'' ⊣ G'') (f : G ⟶ G') (g : G' ⟶ G'') :
    natTransEquiv adj2 adj3 g ≫ natTransEquiv adj1 adj2 f = natTransEquiv adj1 adj3 (f ≫ g) := by
  apply (natTransEquiv adj1 adj3).symm.injective
  ext X
  simp only [natTransEquiv_symm_apply_app, Functor.comp_obj, NatTrans.comp_app,
    natTransEquiv_apply_app, Functor.id_obj, whiskerLeft_app, Functor.map_comp, Category.assoc,
    unit_naturality_assoc, right_triangle_components_assoc, Equiv.symm_apply_apply,
    ← g.naturality_assoc, ← g.naturality]
  simp only [← Category.assoc, unit_naturality, Functor.comp_obj, right_triangle_components,
    Category.comp_id, ← f.naturality, Category.id_comp]

@[simp]
lemma natTransEquiv_comp_symm {F F' F'' : C ⥤ D} {G G' G'' : D ⥤ C}
    (adj1 : F ⊣ G) (adj2 : F' ⊣ G') (adj3 : F'' ⊣ G'') (f : F' ⟶ F) (g : F'' ⟶ F') :
    (natTransEquiv adj1 adj2).symm f ≫ (natTransEquiv adj2 adj3).symm g =
      (natTransEquiv adj1 adj3).symm (g ≫ f) := by
  apply (natTransEquiv adj1 adj3).injective
  ext
  simp

/--
If `F ⊣ G` and `F' ⊣ G'` are adjunctions, then giving a natural isomorphism `G ≅ G'` is the
same as giving a natural transformation `F' ≅ F`.
-/
@[simps]
def natIsoEquiv {F F' : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G') :
    (G ≅ G') ≃ (F' ≅ F) where
  toFun i := {
    hom := natTransEquiv adj1 adj2 i.hom
    inv := natTransEquiv adj2 adj1 i.inv
  }
  invFun i := {
    hom := (natTransEquiv adj1 adj2).symm i.hom
    inv := (natTransEquiv adj2 adj1).symm i.inv }
  left_inv i := by simp
  right_inv i := by simp

/-- If `F` and `F'` are both left adjoint to `G`, then they are naturally isomorphic. -/
def leftAdjointUniq {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) : F ≅ F' :=
  (natIsoEquiv adj1 adj2 (Iso.refl _)).symm

-- Porting note (#10618): removed simp as simp can prove this
theorem homEquiv_leftAdjointUniq_hom_app {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
    (x : C) : adj1.homEquiv _ _ ((leftAdjointUniq adj1 adj2).hom.app x) = adj2.unit.app x := by
  simp [leftAdjointUniq]

@[reassoc (attr := simp)]
theorem unit_leftAdjointUniq_hom {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) :
    adj1.unit ≫ whiskerRight (leftAdjointUniq adj1 adj2).hom G = adj2.unit := by
  ext x
  rw [NatTrans.comp_app, ← homEquiv_leftAdjointUniq_hom_app adj1 adj2]
  simp [← G.map_comp]

@[reassoc (attr := simp)]
theorem unit_leftAdjointUniq_hom_app
    {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (x : C) :
    adj1.unit.app x ≫ G.map ((leftAdjointUniq adj1 adj2).hom.app x) = adj2.unit.app x := by
  rw [← unit_leftAdjointUniq_hom adj1 adj2]; rfl

@[reassoc (attr := simp)]
theorem leftAdjointUniq_hom_counit {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) :
    whiskerLeft G (leftAdjointUniq adj1 adj2).hom ≫ adj2.counit = adj1.counit := by
  ext x
  simp only [Functor.comp_obj, Functor.id_obj, leftAdjointUniq, Iso.symm_hom, natIsoEquiv_apply_inv,
    Iso.refl_inv, NatTrans.comp_app, whiskerLeft_app, natTransEquiv_apply_app, whiskerLeft_id',
    Category.comp_id, Category.assoc]
  rw [← adj1.counit_naturality, ← Category.assoc, ← F.map_comp]
  simp

@[reassoc (attr := simp)]
theorem leftAdjointUniq_hom_app_counit {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
    (x : D) :
    (leftAdjointUniq adj1 adj2).hom.app (G.obj x) ≫ adj2.counit.app x = adj1.counit.app x := by
  rw [← leftAdjointUniq_hom_counit adj1 adj2]
  rfl

theorem leftAdjointUniq_inv_app {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (x : C) :
    (leftAdjointUniq adj1 adj2).inv.app x = (leftAdjointUniq adj2 adj1).hom.app x :=
  rfl

@[reassoc (attr := simp)]
theorem leftAdjointUniq_trans {F F' F'' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
    (adj3 : F'' ⊣ G) :
    (leftAdjointUniq adj1 adj2).hom ≫ (leftAdjointUniq adj2 adj3).hom =
      (leftAdjointUniq adj1 adj3).hom := by
  simp [leftAdjointUniq]

@[reassoc (attr := simp)]
theorem leftAdjointUniq_trans_app {F F' F'' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
    (adj3 : F'' ⊣ G) (x : C) :
    (leftAdjointUniq adj1 adj2).hom.app x ≫ (leftAdjointUniq adj2 adj3).hom.app x =
      (leftAdjointUniq adj1 adj3).hom.app x := by
  rw [← leftAdjointUniq_trans adj1 adj2 adj3]
  rfl

@[simp]
theorem leftAdjointUniq_refl {F : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) :
    (leftAdjointUniq adj1 adj1).hom = 𝟙 _ := by
  simp [leftAdjointUniq]

/-- If `G` and `G'` are both right adjoint to `F`, then they are naturally isomorphic. -/
def rightAdjointUniq {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') : G ≅ G' :=
  (natIsoEquiv adj1 adj2).symm (Iso.refl _)

-- Porting note (#10618): simp can prove this
theorem homEquiv_symm_rightAdjointUniq_hom_app {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G)
    (adj2 : F ⊣ G') (x : D) :
    (adj2.homEquiv _ _).symm ((rightAdjointUniq adj1 adj2).hom.app x) = adj1.counit.app x := by
  simp [rightAdjointUniq]

@[reassoc (attr := simp)]
theorem unit_rightAdjointUniq_hom_app {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
    (x : C) : adj1.unit.app x ≫ (rightAdjointUniq adj1 adj2).hom.app (F.obj x) =
      adj2.unit.app x := by
  simp only [Functor.id_obj, Functor.comp_obj, rightAdjointUniq, natIsoEquiv_symm_apply_hom,
    Iso.refl_hom, natTransEquiv_symm_apply_app, NatTrans.id_app, Category.id_comp]
  rw [← adj2.unit_naturality_assoc, ← G'.map_comp]
  simp

@[reassoc (attr := simp)]
theorem unit_rightAdjointUniq_hom {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') :
    adj1.unit ≫ whiskerLeft F (rightAdjointUniq adj1 adj2).hom = adj2.unit := by
  ext x
  simp

@[reassoc (attr := simp)]
theorem rightAdjointUniq_hom_app_counit {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
    (x : D) :
    F.map ((rightAdjointUniq adj1 adj2).hom.app x) ≫ adj2.counit.app x = adj1.counit.app x := by
  simp [rightAdjointUniq]

@[reassoc (attr := simp)]
theorem rightAdjointUniq_hom_counit {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') :
    whiskerRight (rightAdjointUniq adj1 adj2).hom F ≫ adj2.counit = adj1.counit := by
  ext
  simp

theorem rightAdjointUniq_inv_app {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
    (x : D) : (rightAdjointUniq adj1 adj2).inv.app x = (rightAdjointUniq adj2 adj1).hom.app x :=
  rfl

@[reassoc (attr := simp)]
theorem rightAdjointUniq_trans {F : C ⥤ D} {G G' G'' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
    (adj3 : F ⊣ G'') :
    (rightAdjointUniq adj1 adj2).hom ≫ (rightAdjointUniq adj2 adj3).hom =
      (rightAdjointUniq adj1 adj3).hom := by
  simp [rightAdjointUniq]

@[reassoc (attr := simp)]
theorem rightAdjointUniq_trans_app {F : C ⥤ D} {G G' G'' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
    (adj3 : F ⊣ G'') (x : D) :
    (rightAdjointUniq adj1 adj2).hom.app x ≫ (rightAdjointUniq adj2 adj3).hom.app x =
      (rightAdjointUniq adj1 adj3).hom.app x := by
  rw [← rightAdjointUniq_trans adj1 adj2 adj3]
  rfl


@[simp]
theorem rightAdjointUniq_refl {F : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) :
    (rightAdjointUniq adj1 adj1).hom = 𝟙 _ := by
  delta rightAdjointUniq
  simp

end Adjunction

end CategoryTheory
