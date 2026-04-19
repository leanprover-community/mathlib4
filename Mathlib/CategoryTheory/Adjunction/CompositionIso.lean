/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Compatibilities for left adjoints from compatibilities satisfied by right adjoints

In this file, given isomorphisms between compositions of right adjoint functors,
we obtain isomorphisms between the corresponding compositions of the left adjoint functors,
and show that the left adjoint functors satisfy properties similar to the left/right
unitality and the associativity of pseudofunctors if the right adjoint functors
satisfy the corresponding properties.

This is used in `Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback` to study
the behaviour with respect to composition of the pullback functors on presheaves
of modules, by reducing these definitions and properties to the (obvious) case of the
pushforward functors. Similar results are obtained for sheaves of modules
in `Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous`.

-/

@[expose] public section

namespace CategoryTheory

variable {C₀ C₁ C₂ C₃ : Type*} [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]

open Functor

namespace Adjunction

section

variable {F : C₀ ⥤ C₀} {G : C₀ ⥤ C₀} (adj : F ⊣ G) (e : G ≅ 𝟭 C₀)

/-- If a right adjoint functor is isomorphic to the identity functor,
so is the left adjoint. -/
@[simps! -isSimp]
def leftAdjointIdIso {F : C₀ ⥤ C₀} {G : C₀ ⥤ C₀} (adj : F ⊣ G) (e : G ≅ 𝟭 C₀) :
    F ≅ 𝟭 C₀ := (conjugateIsoEquiv .id adj).symm e.symm

@[simp]
lemma conjugateEquiv_leftAdjointIdIso_hom :
    conjugateEquiv .id adj (leftAdjointIdIso adj e).hom = e.inv := by
  simp [leftAdjointIdIso]

end

section

variable {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₀₂ : C₀ ⥤ C₂}
  {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₂₀ : C₂ ⥤ C₀}
  (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₀₂ : F₀₂ ⊣ G₂₀)

/-- A natural transformation `G₂₀ ⟶ G₂₁ ⋙ G₁₀` involving right adjoint functors
induces a natural transformation `F₀₁ ⋙ F₁₂ ⟶ F₀₂` between the corresponding
left adjoint functors. -/
@[simps! -isSimp]
def leftAdjointCompNatTrans (τ₀₁₂ : G₂₀ ⟶ G₂₁ ⋙ G₁₀) :
    F₀₁ ⋙ F₁₂ ⟶ F₀₂ :=
  (conjugateEquiv adj₀₂ (adj₀₁.comp adj₁₂)).symm τ₀₁₂

/-- A natural isomorphism `G₂₁ ⋙ G₁₀ ≅ G₂₀` involving right adjoint functors
induces a natural isomorphism `F₀₁ ⋙ F₁₂ ≅ F₀₂` between the corresponding
left adjoint functors. -/
@[simps! -isSimp]
def leftAdjointCompIso (e₀₁₂ : G₂₁ ⋙ G₁₀ ≅ G₂₀) :
    F₀₁ ⋙ F₁₂ ≅ F₀₂ :=
  (conjugateIsoEquiv adj₀₂ (adj₀₁.comp adj₁₂)).symm e₀₁₂.symm

lemma leftAdjointCompIso_hom (e₀₁₂ : G₂₁ ⋙ G₁₀ ≅ G₂₀) :
    (leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e₀₁₂).hom =
      leftAdjointCompNatTrans adj₀₁ adj₁₂ adj₀₂ e₀₁₂.inv :=
  rfl

@[simp]
lemma conjugateEquiv_leftAdjointCompIso_inv (e₀₁₂ : G₂₁ ⋙ G₁₀ ≅ G₂₀) :
    conjugateEquiv (adj₀₁.comp adj₁₂) adj₀₂
      (leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e₀₁₂).inv = e₀₁₂.hom := by
  dsimp only [leftAdjointCompIso]
  simp

end

set_option backward.isDefEq.respectTransparency false in
lemma leftAdjointCompIso_comp_id
    {F₀₁ : C₀ ⥤ C₁} {F₁₁' : C₁ ⥤ C₁} {G₁₀ : C₁ ⥤ C₀} {G₁'₁ : C₁ ⥤ C₁}
    (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₁' : F₁₁' ⊣ G₁'₁)
    (e₀₁₁' : G₁'₁ ⋙ G₁₀ ≅ G₁₀) (e₁'₁ : G₁'₁ ≅ 𝟭 _)
    (h : e₀₁₁' = isoWhiskerRight e₁'₁ G₁₀ ≪≫ leftUnitor G₁₀) :
    leftAdjointCompIso adj₀₁ adj₁₁' adj₀₁ e₀₁₁' =
      isoWhiskerLeft _ (leftAdjointIdIso adj₁₁' e₁'₁) ≪≫ rightUnitor F₀₁ := by
  subst h
  ext X₀
  simp [leftAdjointCompIso_hom_app, leftAdjointIdIso_hom_app,
    ← Functor.map_comp_assoc, -Functor.map_comp]

lemma leftAdjointCompIso_id_comp
    {F₀₀' : C₀ ⥤ C₀} {F₀'₁ : C₀ ⥤ C₁} {G₀'₀ : C₀ ⥤ C₀} {G₁₀' : C₁ ⥤ C₀}
    (adj₀₀' : F₀₀' ⊣ G₀'₀) (adj₀'₁ : F₀'₁ ⊣ G₁₀')
    (e₀₀'₁ : G₁₀' ⋙ G₀'₀ ≅ G₁₀') (e₀'₀ : G₀'₀ ≅ 𝟭 _)
    (h : e₀₀'₁ = isoWhiskerLeft G₁₀' e₀'₀ ≪≫ rightUnitor G₁₀') :
    leftAdjointCompIso adj₀₀' adj₀'₁ adj₀'₁ e₀₀'₁ =
      isoWhiskerRight (leftAdjointIdIso adj₀₀' e₀'₀) F₀'₁ ≪≫ leftUnitor F₀'₁ := by
  subst h
  ext X₀
  have h₁ := congr_map F₀'₁ (adj₀₀'.counit.naturality (adj₀'₁.unit.app X₀))
  have h₂ := congr_map (F₀₀' ⋙ F₀'₁) (e₀'₀.inv.naturality (adj₀'₁.unit.app X₀))
  simp only [id_obj, comp_obj, Functor.id_map, Functor.comp_map, Functor.map_comp] at h₁ h₂
  simp [leftAdjointCompIso_hom_app, leftAdjointIdIso_hom_app,
    reassoc_of% h₂, reassoc_of% h₁]

section

variable
  {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₂₃ : C₂ ⥤ C₃} {F₀₂ : C₀ ⥤ C₂} {F₁₃ : C₁ ⥤ C₃} {F₀₃ : C₀ ⥤ C₃}
  {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₃₂ : C₃ ⥤ C₂} {G₂₀ : C₂ ⥤ C₀} {G₃₁ : C₃ ⥤ C₁} {G₃₀ : C₃ ⥤ C₀}
  (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₂₃ : F₂₃ ⊣ G₃₂) (adj₀₂ : F₀₂ ⊣ G₂₀)
  (adj₁₃ : F₁₃ ⊣ G₃₁) (adj₀₃ : F₀₃ ⊣ G₃₀)

section

variable (τ₀₁₂ : G₂₀ ⟶ G₂₁ ⋙ G₁₀) (τ₁₂₃ : G₃₁ ⟶ G₃₂ ⋙ G₂₁)
  (τ₀₁₃ : G₃₀ ⟶ G₃₁ ⋙ G₁₀) (τ₀₂₃ : G₃₀ ⟶ G₃₂ ⋙ G₂₀)

lemma leftAdjointCompNatTrans₀₁₃_eq_conjugateEquiv_symm :
    whiskerLeft _ (leftAdjointCompNatTrans adj₁₂ adj₂₃ adj₁₃ τ₁₂₃) ≫
      leftAdjointCompNatTrans adj₀₁ adj₁₃ adj₀₃ τ₀₁₃ =
    (conjugateEquiv adj₀₃ (adj₀₁.comp (adj₁₂.comp adj₂₃))).symm
      (τ₀₁₃ ≫ whiskerRight τ₁₂₃ G₁₀) := by
  obtain ⟨τ₁₂₃, rfl⟩ := (conjugateEquiv adj₁₃ (adj₁₂.comp adj₂₃)).surjective τ₁₂₃
  obtain ⟨τ₀₁₃, rfl⟩ := (conjugateEquiv adj₀₃ (adj₀₁.comp adj₁₃)).surjective τ₀₁₃
  apply (conjugateEquiv adj₀₃ (adj₀₁.comp (adj₁₂.comp adj₂₃))).injective
  simp [leftAdjointCompNatTrans, ← conjugateEquiv_whiskerLeft _ _ adj₀₁]

lemma leftAdjointCompNatTrans₀₂₃_eq_conjugateEquiv_symm :
    (associator _ _ _).inv ≫
      whiskerRight (leftAdjointCompNatTrans adj₀₁ adj₁₂ adj₀₂ τ₀₁₂) F₂₃ ≫
          leftAdjointCompNatTrans adj₀₂ adj₂₃ adj₀₃ τ₀₂₃ =
    (conjugateEquiv adj₀₃ (adj₀₁.comp (adj₁₂.comp adj₂₃))).symm
      (τ₀₂₃ ≫ whiskerLeft G₃₂ τ₀₁₂ ≫ (associator _ _ _).inv) := by
  obtain ⟨τ₀₁₂, rfl⟩ := (conjugateEquiv adj₀₂ (adj₀₁.comp adj₁₂)).surjective τ₀₁₂
  obtain ⟨τ₀₂₃, rfl⟩ := (conjugateEquiv adj₀₃ (adj₀₂.comp adj₂₃)).surjective τ₀₂₃
  apply (conjugateEquiv adj₀₃ (adj₀₁.comp (adj₁₂.comp adj₂₃))).injective
  simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply, leftAdjointCompNatTrans]
  rw [← cancel_mono (associator G₃₂ G₂₁ G₁₀).hom, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, ← conjugateEquiv_associator_hom adj₀₁ adj₁₂ adj₂₃,
    ← conjugateEquiv_whiskerRight _ _ adj₂₃, conjugateEquiv_comp, Iso.hom_inv_id_assoc,
    conjugateEquiv_comp]

lemma leftAdjointCompNatTrans_assoc
    (h : τ₀₂₃ ≫ whiskerLeft G₃₂ τ₀₁₂ =
      τ₀₁₃ ≫ whiskerRight τ₁₂₃ G₁₀ ≫ (associator _ _ _).hom) :
    whiskerLeft _ (leftAdjointCompNatTrans adj₁₂ adj₂₃ adj₁₃ τ₁₂₃) ≫
        leftAdjointCompNatTrans adj₀₁ adj₁₃ adj₀₃ τ₀₁₃ =
      (associator _ _ _).inv ≫
        whiskerRight (leftAdjointCompNatTrans adj₀₁ adj₁₂ adj₀₂ τ₀₁₂) F₂₃ ≫
          leftAdjointCompNatTrans adj₀₂ adj₂₃ adj₀₃ τ₀₂₃ := by
  simp [leftAdjointCompNatTrans₀₁₃_eq_conjugateEquiv_symm,
    leftAdjointCompNatTrans₀₂₃_eq_conjugateEquiv_symm, reassoc_of% h]

end

lemma leftAdjointCompIso_assoc
    (e₀₁₂ : G₂₁ ⋙ G₁₀ ≅ G₂₀) (e₁₂₃ : G₃₂ ⋙ G₂₁ ≅ G₃₁)
    (e₀₁₃ : G₃₁ ⋙ G₁₀ ≅ G₃₀) (e₀₂₃ : G₃₂ ⋙ G₂₀ ≅ G₃₀)
    (h : isoWhiskerLeft G₃₂ e₀₁₂ ≪≫ e₀₂₃ =
      (associator _ _ _).symm ≪≫ isoWhiskerRight e₁₂₃ _ ≪≫ e₀₁₃) :
    isoWhiskerLeft _ (leftAdjointCompIso adj₁₂ adj₂₃ adj₁₃ e₁₂₃) ≪≫
        leftAdjointCompIso adj₀₁ adj₁₃ adj₀₃ e₀₁₃ =
      (associator _ _ _).symm ≪≫
        isoWhiskerRight (leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e₀₁₂) F₂₃ ≪≫
          leftAdjointCompIso adj₀₂ adj₂₃ adj₀₃ e₀₂₃ := by
  ext : 1
  dsimp [leftAdjointCompIso_hom]
  exact leftAdjointCompNatTrans_assoc _ _ _ _ _ _ _ _ _ _
    (by simpa using congr_arg Iso.inv h)

end

end Adjunction

end CategoryTheory
