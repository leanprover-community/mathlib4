/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# Action of bifunctor on mapping cones
-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D] [Preadditive D]

namespace CochainComplex

section

variable
  [Preadditive C₁] [HasZeroMorphisms C₂]
  {K₁ L₁ : CochainComplex C₁ ℤ} (φ : K₁ ⟶ L₁) (K₂ : CochainComplex C₂ ℤ)
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive]
  [∀ (X₁ : C₁), (F.obj X₁).PreservesZeroMorphisms]
  [HasHomotopyCofiber φ]

open HomComplex mappingCone

namespace mapBifunctorMappingCone₁Iso

variable [HasMapBifunctor (mappingCone φ) K₂ F (ComplexShape.up ℤ)]

section

variable [HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]

noncomputable def ι₁ : Cochain (mapBifunctor K₁ K₂ F (.up ℤ))
    (mapBifunctor (mappingCone φ) K₂ F (.up ℤ)) (-1) :=
  Cochain.mk (fun n m hnm ↦ mapBifunctorDesc (fun p q hpq ↦
    (F.map ((inl φ).v p (p - 1) (by omega))).app _ ≫
      ιMapBifunctor _ _ _ _ _ _ _ (by dsimp at hpq ⊢; omega)))

@[reassoc]
lemma ι_ι₁ (p q n : ℤ) (hpq : p + q = n) (m : ℤ) (hnm : n + (-1) = m)
    (p' : ℤ) (hp' : p' + 1 = p) :
    ιMapBifunctor K₁ K₂ F (.up ℤ) p q n hpq ≫ (ι₁ φ K₂ F).v n m hnm =
      (F.map ((inl φ).v p p' (by omega))).app _ ≫
        ιMapBifunctor _ _ _ _ _ _ _ (by dsimp; omega) := by
  obtain rfl : p' = p - 1 := by omega
  simp [ι₁]

noncomputable def p₁₀ : Cochain (mapBifunctor (mappingCone φ) K₂ F (.up ℤ))
    (mapBifunctor K₁ K₂ F (.up ℤ)) 1 :=
  Cochain.mk (fun n m hnm ↦ mapBifunctorDesc (fun p q hpq ↦
    (F.map ((fst φ).1.v p _ rfl)).app _ ≫
      ιMapBifunctor _ _ _ _ _ _ _ (by dsimp at hpq ⊢; omega)))

@[reassoc]
lemma ι_p₁₀_v (p q n : ℤ) (hpq : p + q = n) (m : ℤ) (hnm : n + 1 = m)
    (p' : ℤ) (hp' : p + 1 = p') :
   ιMapBifunctor (mappingCone φ) K₂ F (.up ℤ) p q n hpq ≫
      (p₁₀ φ K₂ F).v n m hnm = (F.map ((fst φ).1.v p p' hp')).app _ ≫
        ιMapBifunctor _ _ _ _ _ _ _ (by dsimp; omega) := by
  subst hp'
  simp [p₁₀]

@[simp]
lemma ι₁_p₁₀ : (ι₁ φ K₂ F).comp (p₁₀ φ K₂ F) (neg_add_cancel 1) = Cochain.ofHom (𝟙 _) := by
  ext n p q hpq
  dsimp at hpq
  simp [Cochain.comp_v _ _ (neg_add_cancel 1) n (n - 1) n (by omega) (by omega),
    ι_ι₁_assoc _ _ _ p q n hpq (n - 1) (by omega) (p - 1) (by omega),
    ι_p₁₀_v _ _ _ (p - 1) q (n - 1) (by omega) n (by omega) p (by omega),
    ← Functor.map_comp, ← NatTrans.comp_app_assoc]

@[simp]
lemma inr_p₁₀ [HasMapBifunctor L₁ K₂ F (ComplexShape.up ℤ)] :
    (Cochain.ofHom (mapBifunctorMap (inr φ) (𝟙 K₂) F (.up ℤ))).comp
    (p₁₀ φ K₂ F) (zero_add 1) = 0 := by
  ext n _ rfl p q hpq
  dsimp at hpq
  simp [ι_p₁₀_v _ _ _ p q n hpq _ rfl _ rfl, ← Functor.map_comp,
      ← NatTrans.comp_app_assoc]

set_option backward.defeqAttrib.useBackward true in
@[simps!]
noncomputable def p₁ : Cocycle (mapBifunctor (mappingCone φ) K₂ F (.up ℤ))
    (mapBifunctor K₁ K₂ F (.up ℤ)) 1 :=
  Cocycle.mk (p₁₀ φ K₂ F) 2 (by omega) (by
    ext n _ rfl p q hpq
    dsimp at hpq
    have h₁ : (ComplexShape.up ℤ).Rel (p + 1) (p + 2) := by dsimp; omega
    have h₂ : (ComplexShape.up ℤ).Rel q (q + 1) := rfl
    have h₃ : (ComplexShape.up ℤ).Rel p (p + 1) := rfl
    simp [δ_v 1 2 rfl _ n (n + 2) rfl (n + 1) (n + 1) (by omega) rfl,
      ι_p₁₀_v_assoc _ _ _ p q n hpq (n + 1) rfl (p + 1) rfl,
      ι_p₁₀_v _ _ _ p (q + 1) (n + 1) (by omega) (n + 2) (by omega) (p + 1) rfl,
      ι_p₁₀_v _ _ _ (p + 1) q (n + 1) (by omega) (n + 2) (by omega) (p + 2) (by omega),
      mapBifunctor.d_eq, Int.negOnePow_even 2 ⟨1, rfl⟩,
      mapBifunctor.d₁_eq K₁ K₂ F (.up ℤ) h₁ q (n + 2) (by dsimp; omega),
      mapBifunctor.d₂_eq K₁ K₂ F (.up ℤ) (p + 1) h₂ (n + 2) (by dsimp; omega),
      mapBifunctor.d₁_eq (mappingCone φ) K₂ F (.up ℤ) h₃ q (n + 1) (by dsimp; omega),
      mapBifunctor.d₂_eq (mappingCone φ) K₂ F (.up ℤ) p h₂ (n + 1) (by dsimp; omega),
      Int.negOnePow_succ, ← Functor.map_comp, ← NatTrans.comp_app_assoc,
      d_fst_v φ p (p + 1) (p + 2) rfl (by omega)]
    abel)

end

section

variable [HasMapBifunctor L₁ K₂ F (ComplexShape.up ℤ)]

noncomputable def p₂ : Cochain (mapBifunctor (mappingCone φ) K₂ F (.up ℤ))
    (mapBifunctor L₁ K₂ F (.up ℤ)) 0 :=
  Cochain.ofHoms (fun _ ↦ mapBifunctorDesc (fun _ _ hpq ↦
    (F.map ((snd φ).v _ _ (add_zero _))).app _ ≫
      ιMapBifunctor _ _ _ _ _ _ _ hpq))

@[reassoc (attr := simp)]
lemma ι_p₂_v (p q n : ℤ) (hpq : p + q = n) :
    ιMapBifunctor (mappingCone φ) K₂ F (.up ℤ) p q n hpq ≫ (p₂ φ K₂ F).v n n (add_zero n) =
      (F.map ((snd φ).v _ _ (add_zero _))).app _ ≫
        ιMapBifunctor _ _ _ _ _ _ _ hpq := by
  simp [p₂]

@[simp]
lemma inr_p₂ : (Cochain.ofHom (mapBifunctorMap (inr φ) (𝟙 K₂) F (.up ℤ))).comp
    (p₂ φ K₂ F) (zero_add 0) = Cochain.ofHom (𝟙 _) := by
  ext n p q hpq
  dsimp at hpq
  simp [← Functor.map_comp, ← NatTrans.comp_app_assoc]

@[simp]
lemma ι₁_p₂ [HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)] :
    (ι₁ φ K₂ F).comp (p₂ φ K₂ F) (add_zero _) = 0 := by
  ext n m hnm p q hpq
  obtain rfl : m = n - 1 := by omega
  dsimp at hpq
  simp [ι_ι₁_assoc _ _ _ p q n hpq (n - 1) (by omega) (p - 1) (by omega),
    ← Functor.map_comp, ← NatTrans.comp_app_assoc]

end

variable [HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
  [HasMapBifunctor L₁ K₂ F (ComplexShape.up ℤ)]
  [HasHomotopyCofiber (mapBifunctorMap φ (𝟙 K₂) F (.up ℤ))]

noncomputable def hom : mapBifunctor (mappingCone φ) K₂ F (.up ℤ) ⟶
      mappingCone (mapBifunctorMap φ (𝟙 K₂) F (.up ℤ)) :=
  mappingCone.lift _ (p₁ φ K₂ F) (p₂ φ K₂ F) (by
    ext n _ rfl p q hpq
    dsimp at hpq
    have h₁ : (ComplexShape.up ℤ).Rel q (q + 1) := rfl
    have h₂ : (ComplexShape.up ℤ).Rel p (p + 1) := rfl
    simp [mapBifunctor.d_eq, ι_p₁₀_v_assoc _ _ _ p q n _ _ rfl _ rfl,
      mapBifunctor.d₁_eq (mappingCone φ) K₂ F (.up ℤ) h₂ q (n + 1) (by dsimp; omega),
      mapBifunctor.d₂_eq (mappingCone φ) K₂ F (.up ℤ) p h₁ (n + 1) (by dsimp; omega),
      mapBifunctor.d₁_eq L₁ K₂ F (.up ℤ) h₂ q (n + 1) (by dsimp; omega),
      mapBifunctor.d₂_eq L₁ K₂ F (.up ℤ) p h₁ (n + 1) (by dsimp; omega),
      ← Functor.map_comp, ← NatTrans.comp_app_assoc, d_snd_v])

set_option backward.defeqAttrib.useBackward true in
noncomputable def inv :
    mappingCone (mapBifunctorMap φ (𝟙 K₂) F (.up ℤ)) ⟶
      mapBifunctor (mappingCone φ) K₂ F (.up ℤ) :=
  mappingCone.desc _ (ι₁ φ K₂ F) (mapBifunctorMap (inr φ) (𝟙 K₂) F (.up ℤ)) (by
    ext n p q hpq
    dsimp at hpq
    have h₁ : (ComplexShape.up ℤ).Rel p (p + 1) := rfl
    have h₂ : (ComplexShape.up ℤ).Rel q (q + 1) := rfl
    have h₃ : (ComplexShape.up ℤ).Rel (p - 1) p := by dsimp; omega
    rw [δ_v (-1) 0 (neg_add_cancel 1) _ _ _ (add_zero n) (n - 1) (n + 1) rfl rfl]
    simp [ι_ι₁_assoc φ K₂ F p q n hpq (n - 1) (by omega) (p - 1) (by omega),
      mapBifunctor.d_eq, mapBifunctor.d₁_eq K₁ K₂ F (.up ℤ) h₁ q (n + 1) (by dsimp; omega),
      mapBifunctor.d₂_eq K₁ K₂ F (.up ℤ) p h₂ (n + 1) (by dsimp; omega),
      mapBifunctor.d₁_eq (mappingCone φ) K₂ F (.up ℤ) h₃ q n (by dsimp; omega),
      mapBifunctor.d₂_eq (mappingCone φ) K₂ F (.up ℤ) (p - 1) h₂ n (by dsimp; omega),
      ι_ι₁ _ _ _ (p + 1) q (n + 1) (by omega) n (by omega) p (by omega),
      ι_ι₁ _ _ _ p (q + 1) (n + 1) (by omega) n (by omega) (p - 1) (by omega),
      Int.negOnePow_sub, inl_v_d φ p (p - 1) (p + 1) (by omega) (by omega),
      ← Functor.map_comp, ← NatTrans.comp_app_assoc, ]
    abel)

@[reassoc (attr := simp)]
lemma inr_inv : inr _ ≫ inv φ K₂ F = mapBifunctorMap (inr φ) (𝟙 K₂) F (.up ℤ) := by
  simp [inv]

@[simp]
lemma inl_inv : (inl _).comp (Cochain.ofHom (inv φ K₂ F)) (add_zero _) = ι₁ φ K₂ F  := by
  simp [inv]

@[simp]
lemma hom_fst :
    (Cochain.ofHom (hom φ K₂ F)).comp (fst _).1 (zero_add 1) =
      p₁₀ φ K₂ F := by
  simp [hom]

@[simp]
lemma hom_snd :
    (Cochain.ofHom (hom φ K₂ F)).comp (snd _) (zero_add 0) = p₂ φ K₂ F := by
  simp [hom]

@[reassoc (attr := simp)]
lemma hom_inv_id : hom φ K₂ F ≫ inv φ K₂ F = 𝟙 _ := by
  ext n p q hpq
  dsimp [hom, inv] at hpq ⊢
  simp only [lift_f _ _ _ _ _ _ rfl, p₁_coe, desc_f _ _ _ _ _ _ rfl,
    Preadditive.comp_add, Preadditive.add_comp, Category.assoc, inl_v_fst_v_assoc,
    inr_f_fst_v_assoc, zero_comp, comp_zero, add_zero, inl_v_snd_v_assoc, inr_f_snd_v_assoc,
    zero_add, ι_p₁₀_v_assoc _ _ _ p q n hpq _ rfl _ rfl,
    ι_ι₁ _ _ _ (p + 1) q (n + 1) (by omega) n (by omega) p (by omega), ι_p₂_v_assoc,
    ι_mapBifunctorMap, id_f, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  simp only [← NatTrans.comp_app_assoc, ← Functor.map_comp, ← Preadditive.add_comp,
    ← NatTrans.app_add, ← Functor.map_add, mappingCone.id_X,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma inv_hom_id : inv φ K₂ F ≫ hom φ K₂ F = 𝟙 _ := by
  apply (Cocycle.equivHom _ _).injective
  ext : 1
  rw [ext_cochain_from_iff _ (-1) 0 (neg_add_cancel 1),
    ext_cochain_to_iff _ 0 1 (zero_add 1),
    mappingCone.ext_cochain_to_iff _ (-1) 0 (neg_add_cancel 1)]
  dsimp
  simp only [Cochain.ofHom_comp, Cochain.comp_assoc_of_second_is_zero_cochain,
    hom_fst, Cochain.comp_id, inl_fst, hom_snd,
    inl_snd, inr_fst, inr_snd]
  simp only [← Cochain.comp_assoc_of_second_is_zero_cochain, ← Cochain.ofHom_comp,
    inl_inv, inr_inv, inr_p₁₀, inr_p₂, ι₁_p₁₀, ι₁_p₂, and_self]

end mapBifunctorMappingCone₁Iso

variable [HasMapBifunctor (mappingCone φ) K₂ F (ComplexShape.up ℤ)]
  [HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
  [HasMapBifunctor L₁ K₂ F (ComplexShape.up ℤ)]
  [HasHomotopyCofiber (mapBifunctorMap φ (𝟙 K₂) F (.up ℤ))]

open mapBifunctorMappingCone₁Iso in
@[simps]
noncomputable def mapBifunctorMappingCone₁Iso :
    mapBifunctor (mappingCone φ) K₂ F (.up ℤ) ≅
      mappingCone (mapBifunctorMap φ (𝟙 K₂) F (.up ℤ)) where
  hom := hom φ K₂ F
  inv := inv φ K₂ F

@[reassoc (attr := simp)]
lemma mapBifunctorMap_inr_mapBifunctorMappingCone₁Iso_hom :
    mapBifunctorMap (mappingCone.inr φ) (𝟙 K₂) F (.up ℤ) ≫
      mapBifunctorMappingCone₁Iso.hom φ K₂ F =
    inr (mapBifunctorMap φ (𝟙 K₂) F (.up ℤ)) := by
  apply (Cocycle.equivHom _ _).injective
  ext : 1
  simp [ext_cochain_to_iff _ 0 1 (zero_add 1)]

end

/- -/

section

variable
  [HasZeroMorphisms C₁] [Preadditive C₂]
  (K₁ : CochainComplex C₁ ℤ) {K₂ L₂ : CochainComplex C₂ ℤ} (φ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
  [∀ (X₁ : C₁), (F.obj X₁).Additive]
  [HasHomotopyCofiber φ]

open HomComplex mappingCone

namespace mapBifunctorMappingCone₂Iso

variable [HasMapBifunctor K₁ (mappingCone φ) F (ComplexShape.up ℤ)]

section

variable [HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]

noncomputable def ι₁ : Cochain (mapBifunctor K₁ K₂ F (.up ℤ))
    (mapBifunctor K₁ (mappingCone φ) F (.up ℤ)) (-1) :=
  Cochain.mk (fun n m hnm ↦ mapBifunctorDesc (fun p q hpq ↦
    p.negOnePow • (F.obj (K₁.X p)).map ((inl φ).v q (q - 1) (by omega)) ≫
      ιMapBifunctor _ _ _ _ _ _ _ (by dsimp at hpq ⊢; omega)))

@[reassoc]
lemma ι_ι₁ (p q n : ℤ) (hpq : p + q = n) (m : ℤ) (hnm : n + (-1) = m)
    (q' : ℤ) (hq' : q' + 1 = q) :
    ιMapBifunctor K₁ K₂ F (.up ℤ) p q n hpq ≫ (ι₁ K₁ φ F).v n m hnm =
      p.negOnePow • (F.obj (K₁.X p)).map ((inl φ).v q q' (by omega)) ≫
        ιMapBifunctor _ _ _ _ _ _ _ (by dsimp; omega) := by
  obtain rfl : q' = q - 1 := by omega
  simp [ι₁]

noncomputable def p₁₀ : Cochain (mapBifunctor K₁ (mappingCone φ) F (.up ℤ))
    (mapBifunctor K₁ K₂ F (.up ℤ)) 1 :=
  Cochain.mk (fun n m hnm ↦ mapBifunctorDesc (fun p q hpq ↦
    p.negOnePow • (F.obj (K₁.X p)).map ((fst φ).1.v q _ rfl) ≫
      ιMapBifunctor _ _ _ _ _ _ _ (by dsimp at hpq ⊢; omega)))

@[reassoc]
lemma ι_p₁₀_v (p q n : ℤ) (hpq : p + q = n) (m : ℤ) (hnm : n + 1 = m)
    (q' : ℤ) (hq' : q + 1 = q') :
   ιMapBifunctor K₁ (mappingCone φ) F (.up ℤ) p q n hpq ≫
      (p₁₀ K₁ φ F).v n m hnm = p.negOnePow • (F.obj (K₁.X p)).map ((fst φ).1.v q q' hq') ≫
        ιMapBifunctor _ _ _ _ _ _ _ (by dsimp; omega) := by
  subst hq'
  simp [p₁₀]

@[simp]
lemma ι₁_p₁₀ : (ι₁ K₁ φ F).comp (p₁₀ K₁ φ F) (neg_add_cancel 1) = Cochain.ofHom (𝟙 _) := by
  ext n p q hpq
  dsimp at hpq
  simp [Cochain.comp_v _ _ (neg_add_cancel 1) n (n - 1) n (by omega) (by omega),
    ι_ι₁_assoc _ _ _ p q n hpq (n - 1) (by omega) (q - 1) (by omega),
    ι_p₁₀_v _ _ _ p (q - 1) (n - 1) (by omega) n (by omega) q (by omega),
    ← Functor.map_comp_assoc, smul_smul]

@[simp]
lemma inr_p₁₀ [HasMapBifunctor K₁ L₂ F (ComplexShape.up ℤ)] :
    (Cochain.ofHom (mapBifunctorMap (𝟙 K₁) (inr φ) F (.up ℤ))).comp
    (p₁₀ K₁ φ F) (zero_add 1) = 0 := by
  ext n _ rfl p q hpq
  dsimp at hpq
  simp [ι_p₁₀_v _ _ _ p q n hpq _ rfl _ rfl, ← Functor.map_comp_assoc]

set_option backward.defeqAttrib.useBackward true in
@[simps!]
noncomputable def p₁ : Cocycle (mapBifunctor K₁ (mappingCone φ) F (.up ℤ))
    (mapBifunctor K₁ K₂ F (.up ℤ)) 1 :=
  Cocycle.mk (p₁₀ K₁ φ F) 2 (by omega) (by
    ext n _ rfl p q hpq
    dsimp at hpq
    have h₁ : (ComplexShape.up ℤ).Rel (q + 1) (q + 2) := by dsimp; omega
    have h₂ : (ComplexShape.up ℤ).Rel p (p + 1) := rfl
    have h₃ : (ComplexShape.up ℤ).Rel q (q + 1) := rfl
    simp [δ_v 1 2 rfl _ n (n + 2) rfl (n + 1) (n + 1) (by omega) rfl,
      ι_p₁₀_v_assoc _ _ _ p q n hpq (n + 1) rfl (q + 1) rfl,
      ι_p₁₀_v _ _ _ p (q + 1) (n + 1) (by omega) (n + 2) (by omega) (q + 2) (by omega),
      ι_p₁₀_v _ _ _ (p + 1) q (n + 1) (by omega) (n + 2) (by omega) (q + 1) (by omega),
      mapBifunctor.d_eq, Int.negOnePow_even 2 ⟨1, rfl⟩,
      mapBifunctor.d₁_eq K₁ K₂ F (.up ℤ) h₂ (q + 1) (n + 2) (by dsimp; omega),
      mapBifunctor.d₂_eq K₁ K₂ F (.up ℤ) p h₁ (n + 2) (by dsimp; omega),
      mapBifunctor.d₂_eq K₁ (mappingCone φ) F (.up ℤ) p h₃ (n + 1) (by dsimp; omega),
      mapBifunctor.d₁_eq K₁ (mappingCone φ) F (.up ℤ) h₂ q (n + 1) (by dsimp; omega),
      -Functor.map_comp, ← Functor.map_comp_assoc,
      d_fst_v φ q (q + 1) (q + 2) rfl (by omega), smul_smul,
      Int.negOnePow_succ]
    abel)

end

section

variable [HasMapBifunctor K₁ L₂ F (ComplexShape.up ℤ)]

noncomputable def p₂ : Cochain (mapBifunctor K₁ (mappingCone φ) F (.up ℤ))
    (mapBifunctor K₁ L₂ F (.up ℤ)) 0 :=
  Cochain.ofHoms (fun _ ↦ mapBifunctorDesc (fun _ _ hpq ↦
    (F.obj (K₁.X _)).map ((snd φ).v _ _ (add_zero _)) ≫
      ιMapBifunctor _ _ _ _ _ _ _ hpq))

@[reassoc (attr := simp)]
lemma ι_p₂_v (p q n : ℤ) (hpq : p + q = n) :
    ιMapBifunctor K₁ (mappingCone φ) F (.up ℤ) p q n hpq ≫ (p₂ K₁ φ F).v n n (add_zero n) =
    (F.obj (K₁.X _)).map ((snd φ).v _ _ (add_zero _)) ≫
      ιMapBifunctor _ _ _ _ _ _ _ hpq := by
  simp [p₂]

@[simp]
lemma inr_p₂ : (Cochain.ofHom (mapBifunctorMap (𝟙 K₁) (inr φ) F (.up ℤ))).comp
    (p₂ K₁ φ F) (zero_add 0) = Cochain.ofHom (𝟙 _) := by
  ext n p q hpq
  simp [← Functor.map_comp_assoc]

@[simp]
lemma ι₁_p₂ [HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)] :
    (ι₁ K₁ φ F).comp (p₂ K₁ φ F) (add_zero _) = 0 := by
  ext n m hnm p q hpq
  obtain rfl : m = n - 1 := by omega
  dsimp at hpq
  simp [ι_ι₁_assoc _ _ _ p q n hpq (n - 1) (by omega) (q - 1) (by omega),
    ← Functor.map_comp_assoc]

end

variable [HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
  [HasMapBifunctor K₁ L₂ F (ComplexShape.up ℤ)]
  [HasHomotopyCofiber (mapBifunctorMap (𝟙 K₁) φ F (.up ℤ))]

noncomputable def hom : mapBifunctor K₁ (mappingCone φ) F (.up ℤ) ⟶
      mappingCone (mapBifunctorMap (𝟙 K₁) φ F (.up ℤ)) :=
  mappingCone.lift _ (p₁ K₁ φ F) (p₂ K₁ φ F) (by
    ext n _ rfl p q hpq
    dsimp at hpq
    have h₁ : (ComplexShape.up ℤ).Rel p (p + 1) := rfl
    have h₂ : (ComplexShape.up ℤ).Rel q (q + 1) := rfl
    simp [mapBifunctor.d_eq, ι_p₁₀_v_assoc _ _ _ p q n _ _ rfl _ rfl,
      mapBifunctor.d₂_eq K₁ (mappingCone φ) F (.up ℤ) p h₂ (n + 1) (by dsimp; omega),
      mapBifunctor.d₁_eq K₁ (mappingCone φ) F (.up ℤ) h₁ q (n + 1) (by dsimp; omega),
      mapBifunctor.d₂_eq K₁ L₂ F (.up ℤ) p h₂ (n + 1) (by dsimp; omega),
      mapBifunctor.d₁_eq K₁ L₂ F (.up ℤ) h₁ q (n + 1) (by dsimp; omega),
      -Functor.map_comp, ← Functor.map_comp_assoc, d_snd_v])

set_option backward.defeqAttrib.useBackward true in
noncomputable def inv :
    mappingCone (mapBifunctorMap (𝟙 K₁) φ F (.up ℤ)) ⟶
      mapBifunctor K₁ (mappingCone φ) F (.up ℤ) :=
  mappingCone.desc _ (ι₁ K₁ φ F) (mapBifunctorMap (𝟙 K₁) (inr φ) F (.up ℤ)) (by
    ext n p q hpq
    dsimp at hpq
    have h₁ : (ComplexShape.up ℤ).Rel q (q + 1) := rfl
    have h₂ : (ComplexShape.up ℤ).Rel p (p + 1) := rfl
    have h₃ : (ComplexShape.up ℤ).Rel (q - 1) q := by dsimp; omega
    rw [δ_v (-1) 0 (neg_add_cancel 1) _ _ _ (add_zero n) (n - 1) (n + 1) rfl rfl]
    simp [ι_ι₁_assoc K₁ φ F p q n hpq (n - 1) (by omega) (q - 1) (by omega),
      ι_ι₁ _ _ _ p (q + 1) (n + 1) (by omega) n (by omega) q (by omega),
      ι_ι₁ _ _ _ (p + 1) q (n + 1) (by omega) n (by omega) (q - 1) (by omega),
      mapBifunctor.d_eq,
      mapBifunctor.d₂_eq K₁ K₂ F (.up ℤ) p h₁ (n + 1) (by dsimp; omega),
      mapBifunctor.d₁_eq K₁ K₂ F (.up ℤ) h₂ q (n + 1) (by dsimp; omega),
      mapBifunctor.d₂_eq K₁ (mappingCone φ) F (.up ℤ) p h₃ n (by dsimp; omega),
      mapBifunctor.d₁_eq K₁ (mappingCone φ) F (.up ℤ) h₂ (q - 1) n (by dsimp; omega),
      inl_v_d φ q (q - 1) (q + 1) (by omega) (by omega),
      smul_smul, -Functor.map_comp, ← Functor.map_comp_assoc,
      Int.negOnePow_succ]
    abel)

@[reassoc (attr := simp)]
lemma inr_inv : inr _ ≫ inv K₁ φ F = mapBifunctorMap (𝟙 K₁) (inr φ) F (.up ℤ) := by
  simp [inv]

@[simp]
lemma inl_inv : (inl _).comp (Cochain.ofHom (inv K₁ φ F)) (add_zero _) = ι₁ K₁ φ F  := by
  simp [inv]

@[simp]
lemma hom_fst :
    (Cochain.ofHom (hom K₁ φ F)).comp (fst _).1 (zero_add 1) =
      p₁₀ K₁ φ F := by
  simp [hom]

@[simp]
lemma hom_snd :
    (Cochain.ofHom (hom K₁ φ F)).comp (snd _) (zero_add 0) = p₂ K₁ φ F := by
  simp [hom]

@[reassoc (attr := simp)]
lemma hom_inv_id : hom K₁ φ F ≫ inv K₁ φ F = 𝟙 _ := by
  ext n p q hpq
  dsimp [hom, inv] at hpq ⊢
  simp only [lift_f _ _ _ _ _ _ rfl, p₁_coe, Preadditive.add_comp, Category.assoc,
    inl_v_desc_f, inr_f_desc_f, Preadditive.comp_add, ι_p₁₀_v_assoc _ _ _ p q n hpq _ rfl _ rfl,
    Linear.units_smul_comp, ι_ι₁ _ _ _ p (q + 1) (n + 1) (by omega) n (by omega) q (by omega),
    Linear.comp_units_smul, smul_smul, Int.units_mul_self, one_smul, ι_p₂_v_assoc,
    ι_mapBifunctorMap, id_f, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    Category.comp_id]
  simp only [← Functor.map_comp_assoc, ← Preadditive.add_comp, ← Functor.map_add,
    mappingCone.id_X, CategoryTheory.Functor.map_id, Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma inv_hom_id : inv K₁ φ F ≫ hom K₁ φ F = 𝟙 _ := by
  apply (Cocycle.equivHom _ _).injective
  ext : 1
  rw [ext_cochain_from_iff _ (-1) 0 (neg_add_cancel 1),
    ext_cochain_to_iff _ 0 1 (zero_add 1),
    mappingCone.ext_cochain_to_iff _ (-1) 0 (neg_add_cancel 1)]
  dsimp
  simp only [Cochain.ofHom_comp, Cochain.comp_assoc_of_second_is_zero_cochain,
    hom_fst, Cochain.comp_id, inl_fst, hom_snd, inl_snd, inr_fst, inr_snd]
  simp only [← Cochain.comp_assoc_of_second_is_zero_cochain, ← Cochain.ofHom_comp,
    inl_inv, inr_inv, inr_p₁₀, inr_p₂, ι₁_p₁₀, ι₁_p₂, and_self]

end mapBifunctorMappingCone₂Iso

variable [HasMapBifunctor K₁ (mappingCone φ) F (ComplexShape.up ℤ)]
  [HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
  [HasMapBifunctor K₁ L₂ F (ComplexShape.up ℤ)]
  [HasHomotopyCofiber (mapBifunctorMap (𝟙 K₁) φ F (.up ℤ))]

open mapBifunctorMappingCone₂Iso in
@[simps]
noncomputable def mapBifunctorMappingCone₂Iso :
    mapBifunctor K₁ (mappingCone φ) F (.up ℤ) ≅
      mappingCone (mapBifunctorMap (𝟙 K₁) φ F (.up ℤ)) where
  hom := hom K₁ φ F
  inv := inv K₁ φ F

@[reassoc (attr := simp)]
lemma mapBifunctorMap_inr_mapBifunctorMappingCone₂Iso_hom :
    mapBifunctorMap (𝟙 K₁) (mappingCone.inr φ) F (.up ℤ) ≫
      mapBifunctorMappingCone₂Iso.hom K₁ φ F =
    inr (mapBifunctorMap (𝟙 K₁) φ F (.up ℤ)) := by
  apply (Cocycle.equivHom _ _).injective
  ext : 1
  simp [ext_cochain_to_iff _ 0 1 (zero_add 1)]

end

end CochainComplex
