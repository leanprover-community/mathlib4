/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Change of sheaf of rings

In this file, we define the restriction of scalars functor
`restrictScalars α : SheafOfModules.{v} R' ⥤ SheafOfModules.{v} R`
attached to a morphism of sheaves of rings `α : R ⟶ R'`. We also show that
an isomorphism `α : R ≅ R'` induces an equivalence of categories
`restrictScalarsEquivalenceOfIso α : SheafOfModules R' ≌ SheafOfModules R`.

-/

@[expose] public section

universe v v' u u'

open CategoryTheory

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}

namespace SheafOfModules

variable {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R')

/-- The restriction of scalars functor `SheafOfModules R' ⥤ SheafOfModules R`
induced by a morphism of sheaves of rings `R ⟶ R'`. -/
@[simps]
noncomputable def restrictScalars :
    SheafOfModules.{v} R' ⥤ SheafOfModules.{v} R where
  obj M' :=
    { val := (PresheafOfModules.restrictScalars α.hom).obj M'.val
      isSheaf := M'.isSheaf }
  map φ := { val := (PresheafOfModules.restrictScalars α.hom).map φ.val }

instance : (restrictScalars.{v} α).Additive where

instance : (restrictScalars (𝟙 R)).Full := inferInstanceAs (𝟭 _).Full

@[simp]
theorem restrictScalars.map_app_hom_apply (α : R ⟶ R') {M M' : SheafOfModules.{v} R'} (g : M ⟶ M')
    {X : Cᵒᵖ} (m : ((restrictScalars α).obj M).val.obj X) :
    ((restrictScalars α).map g).val.app X m = g.val.app X m := rfl

@[simp]
theorem restrictScalars.smul_def (α : R ⟶ R') {M : SheafOfModules.{v} R'} {X : Cᵒᵖ}
    (r : R.obj.obj X) (m : ((restrictScalars α).obj M).val.obj X) :
    r • m = α.hom.app X r • show M.val.obj X from m :=
  rfl

theorem restrictScalars.smul_def' (α : R ⟶ R') {M : SheafOfModules.{v} R'} {X : Cᵒᵖ}
    (r : R.obj.obj X) (m : M.val.obj X) :
    r • (show ((restrictScalars α).obj M).val.obj X from m) = α.hom.app X r • m :=
  rfl

section

variable {α β : R ⟶ R'} (e : α = β)

/-- Restrictions scalars along equal morphisms are naturally isomorphic. -/
noncomputable def restrictScalarsCongr : restrictScalars α ≅ restrictScalars β :=
  NatIso.ofComponents <| fun M ↦ (fullyFaithfulForget _).preimageIso <|
    (PresheafOfModules.restrictScalarsCongr (by subst e; rfl)).app M.val

@[simp]
lemma restrictScalarsCongr_symm : (restrictScalarsCongr e).symm = restrictScalarsCongr e.symm :=
  rfl

@[simp]
lemma restrictScalarsCongr_hom_app_val_app_hom_apply
    {M : SheafOfModules.{v} R'} {X : Cᵒᵖ} (m : M.val.obj X) :
    ((restrictScalarsCongr e).hom.app M).val.app X m = m :=
  rfl

@[simp]
lemma restrictScalarsCongr_inv_app_val_app_hom_apply
    {M : SheafOfModules.{v} R'} {X : Cᵒᵖ} (m : M.val.obj X) :
    ((restrictScalarsCongr e).inv.app M).val.app X m = m :=
  rfl

end

section

variable (f : R ⟶ R) (hf : f = 𝟙 R)

/-- The restriction of scalars by a morphism that is the identity identifies to the
identity functor. -/
noncomputable def restrictScalarsId' : restrictScalars f ≅ 𝟭 _ :=
  NatIso.ofComponents <| fun M ↦ (fullyFaithfulForget _).preimageIso <|
    (PresheafOfModules.restrictScalarsId' f.hom (by subst hf; rfl)).app M.val

@[simp]
lemma restrictScalarsId'_hom_app_app_hom_apply
    {M : SheafOfModules.{v} R} {X : Cᵒᵖ} (m : M.val.obj X) :
    ((restrictScalarsId' f hf).hom.app M).val.app X m = m :=
  rfl

@[simp]
lemma restrictScalarsId'_inv_app_app_hom_apply
    {M : SheafOfModules.{v} R} {X : Cᵒᵖ} (m : M.val.obj X) :
    ((restrictScalarsId' f hf).inv.app M).val.app X m = m :=
  rfl

@[reassoc]
lemma restrictScalarsId'_app_hom_naturality {M N : SheafOfModules R} (φ : M ⟶ N) :
    (restrictScalars f).map φ ≫ ((restrictScalarsId' f hf).app N).hom =
      ((restrictScalarsId' f hf).app M).hom ≫ φ :=
  (restrictScalarsId' f hf).hom.naturality φ

@[reassoc]
lemma restrictScalarsId'_app_inv_naturality {M N : SheafOfModules R} (φ : M ⟶ N) :
    φ ≫ ((restrictScalarsId' f hf).app N).inv =
      ((restrictScalarsId' f hf).app M).inv ≫ (restrictScalars f).map φ :=
  (restrictScalarsId' f hf).inv.naturality φ

variable (R) in
/-- The restriction of scalars by the identity morphism identifies to the
identity functor. -/
noncomputable abbrev restrictScalarsId : restrictScalars (𝟙 R) ≅ 𝟭 _ :=
  restrictScalarsId' (𝟙 R) rfl

end

section

variable {R₁ R₂ R₃ : Sheaf J RingCat.{u}} (f : R₁ ⟶ R₂) (g : R₂ ⟶ R₃) (gf : R₁ ⟶ R₃)
  (hgf : f ≫ g = gf)

/-- The restriction of scalars by a composition of morphisms identifies to the
composition of the restriction of scalars functors. -/
noncomputable def restrictScalarsComp' :
    restrictScalars gf ≅ restrictScalars g ⋙ restrictScalars f :=
  NatIso.ofComponents <| fun M ↦ (fullyFaithfulForget _).preimageIso <|
    (PresheafOfModules.restrictScalarsComp' f.hom g.hom gf.hom (by subst hgf; rfl)).app M.val

@[simp]
lemma restrictScalarsComp'_hom_app_app_hom_apply
    {M : SheafOfModules.{v} R₃} {X : Cᵒᵖ} (m : M.val.obj X) :
    ((restrictScalarsComp' f g gf hgf).hom.app M).val.app X m = m :=
  rfl

@[simp]
lemma restrictScalarsComp'_inv_app_app_hom_apply
    {M : SheafOfModules.{v} R₃} {X : Cᵒᵖ} (m : M.val.obj X) :
    ((restrictScalarsComp' f g gf hgf).inv.app M).val.app X m = m :=
  rfl

@[reassoc]
lemma restrictScalarsComp'_app_hom_naturality {M N : SheafOfModules R₃} (φ : M ⟶ N) :
    (restrictScalars gf).map φ ≫ ((restrictScalarsComp' f g gf hgf).app N).hom =
      ((restrictScalarsComp' f g gf hgf).app M).hom ≫
        (restrictScalars f).map ((restrictScalars g).map φ) :=
  (restrictScalarsComp' f g gf hgf).hom.naturality φ

@[reassoc]
lemma restrictScalarsComp'_app_inv_naturality {M N : SheafOfModules R₃} (φ : M ⟶ N) :
    (restrictScalars f).map ((restrictScalars g).map φ) ≫
        ((restrictScalarsComp' f g gf hgf).app N).inv =
      ((restrictScalarsComp' f g gf hgf).app M).inv ≫ (restrictScalars gf).map φ :=
  (restrictScalarsComp' f g gf hgf).inv.naturality φ

/-- The restriction of scalars by a composition of morphisms identifies to the
composition of the restriction of scalars functors. -/
noncomputable abbrev restrictScalarsComp :
    restrictScalars (f ≫ g) ≅ restrictScalars g ⋙ restrictScalars f :=
  restrictScalarsComp' f g _ rfl

end

/-- The equivalence of categories `SheafOfModules R' ≌ SheafOfModules R` induced by
`α : R ≅ R'`. -/
@[simps]
noncomputable def restrictScalarsEquivalenceOfIso (α : R ≅ R') :
    SheafOfModules.{v} R' ≌ SheafOfModules.{v} R where
  functor := restrictScalars α.hom
  inverse := restrictScalars α.inv
  unitIso := (restrictScalarsId R').symm ≪≫ restrictScalarsComp' _ _ _ α.inv_hom_id
  counitIso := (restrictScalarsComp' _ _ _ α.hom_inv_id).symm ≪≫ restrictScalarsId R

instance restrictScalars_isEquivalence_of_isIso (α : R ⟶ R') [IsIso α] :
    (restrictScalars α).IsEquivalence :=
  (restrictScalarsEquivalenceOfIso (asIso α)).isEquivalence_functor

end SheafOfModules

namespace PresheafOfModules

variable {R R' : Cᵒᵖ ⥤ RingCat.{u}} (α : R ⟶ R')
  {M₁ M₂ : PresheafOfModules.{v} R'}

/-- The functor `PresheafOfModules.restrictScalars α` induces bijections on
morphisms if `α` is locally surjective and the target presheaf is a sheaf. -/
noncomputable def restrictHomEquivOfIsLocallySurjective
    (hM₂ : Presheaf.IsSheaf J M₂.presheaf) [Presheaf.IsLocallySurjective J α] :
    (M₁ ⟶ M₂) ≃ ((restrictScalars α).obj M₁ ⟶ (restrictScalars α).obj M₂) where
  toFun f := (restrictScalars α).map f
  invFun g := homMk ((toPresheaf R).map g) (fun X r' m ↦ by
    apply hM₂.isSeparated _ _ (Presheaf.imageSieve_mem J α r')
    rintro Y p ⟨r : R.obj _, hr⟩
    have hg : ∀ (z : M₁.obj X), g.app _ (M₁.map p.op z) = M₂.map p.op (g.app X z) :=
      fun z ↦ CategoryTheory.congr_fun (g.naturality p.op) z
    change M₂.map p.op (g.app X (r' • m)) = M₂.map p.op (r' • show M₂.obj X from g.app X m)
    dsimp at hg ⊢
    rw [← hg, M₂.map_smul, ← hg, ← hr]
    erw [← (g.app _).hom.map_smul]
    rw [M₁.map_smul, ← hr]
    rfl)

end PresheafOfModules
