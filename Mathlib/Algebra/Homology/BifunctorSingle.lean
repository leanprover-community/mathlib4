/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.BifunctorFlip

/-!
# Evaluating bifunctors on a single complex

-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex ZeroObject

namespace CochainComplex

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D] [HasZeroObject D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
  [∀ (X₁ : C₁), (F.obj X₁).PreservesZeroMorphisms]

instance [HasZeroObject C₁] (X₁ : C₁) (K₂ : CochainComplex C₂ ℤ) (x₁ : ℤ) :
    HasMapBifunctor ((single C₁ (ComplexShape.up ℤ) x₁).obj X₁) K₂ F (.up ℤ) :=
  fun n ↦ by
    obtain ⟨x₂, rfl⟩ : ∃ (x₂ : ℤ), n = x₁ + x₂ := ⟨n - x₁, by simp⟩
    refine ⟨⟨Cofan.mk ((F.obj X₁).obj (K₂.X x₂)) (fun ⟨⟨p, q⟩, hpq⟩ ↦
      if hpq : p = x₁ ∧ q = x₂ then
        (F.map (singleObjXIsoOfEq (.up ℤ) x₁ X₁ p hpq.1).hom).app _ ≫ (F.obj X₁).map
          (eqToHom (by
            obtain rfl := hpq.2
            rfl))
        else 0), {
          desc s :=
            (F.map (singleObjXIsoOfEq (.up ℤ) x₁ X₁ x₁ rfl).inv).app _ ≫ s.ι.app ⟨⟨x₁, x₂⟩, by simp⟩
          fac s := by
            rintro ⟨⟨p, q⟩, hpq⟩
            simp only [Set.mem_preimage, Set.mem_singleton_iff, ComplexShape.π_def] at hpq
            by_cases hp : p = x₁
            · subst hp
              obtain rfl : q = x₂ := by omega
              simp
            · apply IsZero.eq_of_src
              dsimp
              apply IsZero.obj
              apply Functor.map_isZero
              exact isZero_single_obj_X _ _ _ _ hp
          uniq s m hm := by
            have := hm ⟨⟨x₁, x₂⟩, by simp⟩
            dsimp at this
            simp only [and_self, reduceDIte, CategoryTheory.Functor.map_id,
              Category.comp_id] at this
            simp [← this]
        }⟩⟩

instance [HasZeroObject C₂] (X₂ : C₂) (K₁ : CochainComplex C₁ ℤ) (x₂ : ℤ) :
    HasMapBifunctor K₁ ((single C₂ (ComplexShape.up ℤ) x₂).obj X₂) F (.up ℤ) := by
  rw [← hasMapBifunctor_flip_iff]
  infer_instance

@[simps inv]
noncomputable def mapBifunctorSingle₁XIso
    [HasZeroObject C₁] (X₁ : C₁) (K₂ : CochainComplex C₂ ℤ) (n : ℤ) :
    (mapBifunctor ((single C₁ (.up ℤ) 0).obj X₁) K₂ F (.up ℤ)).X n ≅
      (((F.obj X₁).mapHomologicalComplex (.up ℤ)).obj K₂).X n where
  hom := mapBifunctorDesc (fun p q hpq ↦
    if hpq : p = 0 ∧ q = n then
      (F.map (singleObjXIsoOfEq (.up ℤ) 0 X₁ p hpq.1).hom).app _ ≫
        (F.obj X₁).map (eqToHom (by obtain rfl := hpq.2; rfl)) else 0)
  inv := (F.map (singleObjXSelf (.up ℤ) 0 X₁).inv).app _ ≫
      ιMapBifunctor ((single C₁ (.up ℤ) 0).obj X₁) K₂ F (.up ℤ) 0 n n (by simp)
  hom_inv_id := by
    ext p q hpq
    simp only [ComplexShape.π_def] at hpq
    by_cases hp : p = 0
    · subst hp
      obtain rfl : n = q := by omega
      simp [singleObjXSelf]
    · apply IsZero.eq_of_src
      apply IsZero.obj
      apply Functor.map_isZero
      exact isZero_single_obj_X _ _ _ _ hp
  inv_hom_id := by simp [singleObjXSelf]

section
variable [HasZeroObject C₁] (X₁ : C₁)

@[simps! inv_f]
noncomputable def mapBifunctorSingle₁Iso (K₂ : CochainComplex C₂ ℤ) :
    mapBifunctor ((single C₁ (.up ℤ) 0).obj X₁) K₂ F (.up ℤ) ≅
      ((F.obj X₁).mapHomologicalComplex (.up ℤ)).obj K₂ :=
  (Hom.isoOfComponents (fun n ↦ (mapBifunctorSingle₁XIso F X₁ K₂ n).symm) (by
    rintro n _ rfl
    dsimp
    simp only [Category.assoc, NatTrans.naturality_assoc]
    congr 1
    rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
      mapBifunctor.d₁_eq _ _ F _ (i₁' := 1) (by simp) _ _ (by dsimp; omega),
      single_obj_d, Functor.map_zero, zero_app, zero_comp, smul_zero, zero_add,
      mapBifunctor.d₂_eq _ _ F _ _ (i₂' := n + 1) (by simp) _ (by dsimp; omega)]
    dsimp
    simp only [one_smul])).symm

@[reassoc (attr := simp)]
lemma mapBifunctorSingle₁Iso_inv_naturality {K₂ K₂' : CochainComplex C₂ ℤ} (φ : K₂ ⟶ K₂') :
    (mapBifunctorSingle₁Iso F X₁ K₂).inv ≫ mapBifunctorMap (𝟙 _) φ F (.up ℤ) =
      ((F.obj X₁).mapHomologicalComplex _).map φ ≫ (mapBifunctorSingle₁Iso F X₁ K₂').inv := by
  aesop_cat

@[reassoc (attr := simp)]
lemma mapBifunctorSingle₁Iso_hom_naturality {K₂ K₂' : CochainComplex C₂ ℤ} (φ : K₂ ⟶ K₂') :
    mapBifunctorMap (𝟙 _) φ F (.up ℤ) ≫ (mapBifunctorSingle₁Iso F X₁ K₂').hom =
      (mapBifunctorSingle₁Iso F X₁ K₂).hom ≫ ((F.obj X₁).mapHomologicalComplex _).map φ  := by
  rw [← cancel_epi (mapBifunctorSingle₁Iso F X₁ K₂).inv, Iso.inv_hom_id_assoc,
    mapBifunctorSingle₁Iso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]

end

section

variable [HasZeroObject C₂] (X₂ : C₂)

@[simps! -isSimp hom inv]
noncomputable def mapBifunctorSingle₂Iso
    (K₁ : CochainComplex C₁ ℤ) :
    mapBifunctor K₁ ((single C₂ (.up ℤ) 0).obj X₂) F (.up ℤ) ≅
      ((F.flip.obj X₂).mapHomologicalComplex (.up ℤ)).obj K₁ :=
  (mapBifunctorFlipIso _ _ _ _).symm ≪≫ mapBifunctorSingle₁Iso F.flip X₂ K₁

attribute [local simp] mapBifunctorSingle₂Iso_inv

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma mapBifunctorSingle₂Iso_inv_naturality {K₁ K₁' : CochainComplex C₁ ℤ} (φ : K₁ ⟶ K₁') :
    (mapBifunctorSingle₂Iso F X₂ K₁).inv ≫ mapBifunctorMap φ (𝟙 _) F (.up ℤ) =
      ((F.flip.obj X₂).mapHomologicalComplex _).map φ ≫ (mapBifunctorSingle₂Iso F X₂ K₁').inv := by
  aesop_cat

@[reassoc (attr := simp)]
lemma mapBifunctorSingle₂Iso_hom_naturality {K₁ K₁' : CochainComplex C₁ ℤ} (φ : K₁ ⟶ K₁') :
    mapBifunctorMap φ (𝟙 _) F (.up ℤ) ≫ (mapBifunctorSingle₂Iso F X₂ K₁').hom =
      (mapBifunctorSingle₂Iso F X₂ K₁).hom ≫ ((F.flip.obj X₂).mapHomologicalComplex _).map φ := by
  rw [← cancel_epi (mapBifunctorSingle₂Iso F X₂ K₁).inv, Iso.inv_hom_id_assoc,
    mapBifunctorSingle₂Iso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]

end

variable [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ),
    HasMapBifunctor K₁ K₂ F (.up ℤ)]

@[simps! hom_app inv_app]
noncomputable def map₂HomologicalComplexObjSingleIso
    [HasZeroObject C₁] (X₁ : C₁) :
    (F.map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)).obj
        ((single C₁ (.up ℤ) 0).obj X₁) ≅
          (F.obj X₁).mapHomologicalComplex (.up ℤ) :=
  NatIso.ofComponents (mapBifunctorSingle₁Iso F X₁)

@[simps! hom_app inv_app]
noncomputable def map₂HomologicalComplexFlipObjSingleIso
    [HasZeroObject C₂] (X₂ : C₂) :
    (F.map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj
        ((single C₂ (.up ℤ) 0).obj X₂) ≅
          (F.flip.obj X₂).mapHomologicalComplex (.up ℤ) :=
  NatIso.ofComponents (mapBifunctorSingle₂Iso F X₂)

end CochainComplex
