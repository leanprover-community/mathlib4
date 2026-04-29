/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf

/-!
# Change of presheaf of rings

In this file, we define the restriction of scalars functor
`restrictScalars α : PresheafOfModules.{v} R' ⥤ PresheafOfModules.{v} R`
attached to a morphism of presheaves of rings `α : R ⟶ R'`. We also show that
an isomorphism `α : R ≅ R'` induces an equivalence of categories
`restrictScalarsEquivalenceOfIso α : PresheafOfModules R' ≌ PresheafOfModules R`.

-/

@[expose] public section

universe v v' u u'

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u'} [Category.{v'} C] {R R' : Cᵒᵖ ⥤ RingCat.{u}}

/-- The restriction of scalars of presheaves of modules, on objects. -/
@[simps]
noncomputable def restrictScalarsObj (M' : PresheafOfModules.{v} R') (α : R ⟶ R') :
    PresheafOfModules R where
  obj := fun X ↦ (ModuleCat.restrictScalars (α.app X).hom).obj (M'.obj X)
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(X := ...)` and `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  map := fun {X Y} f ↦ ModuleCat.ofHom
      (X := (ModuleCat.restrictScalars (α.app X).hom).obj (M'.obj X))
      (Y := (ModuleCat.restrictScalars (R.map f).hom).obj
        ((ModuleCat.restrictScalars (α.app Y).hom).obj (M'.obj Y)))
    { toFun := M'.map f
      map_add' := map_add _
      map_smul' := fun r x ↦ (M'.map_smul f (α.app _ r) x).trans (by
        have eq := RingHom.congr_fun (congrArg RingCat.Hom.hom <| α.naturality f) r
        dsimp at eq
        rw [← eq]
        rfl) }

/-- The restriction of scalars functor `PresheafOfModules R' ⥤ PresheafOfModules R`
induced by a morphism of presheaves of rings `R ⟶ R'`. -/
@[simps]
noncomputable def restrictScalars (α : R ⟶ R') :
    PresheafOfModules.{v} R' ⥤ PresheafOfModules.{v} R where
  obj M' := M'.restrictScalarsObj α
  map φ' :=
    { app := fun X ↦ (ModuleCat.restrictScalars (α.app X).hom).map (Hom.app φ' X)
      naturality := fun {X Y} f ↦ by
        ext x
        exact naturality_apply φ' f x }

instance (α : R ⟶ R') : (restrictScalars.{v} α).Additive where

instance : (restrictScalars (𝟙 R)).Full := inferInstanceAs (𝟭 _).Full

instance (α : R ⟶ R') : (restrictScalars α).Faithful where
  map_injective h := (toPresheaf R').map_injective ((toPresheaf R).congr_map h)

/-- The isomorphism `restrictScalars α ⋙ toPresheaf R ≅ toPresheaf R'` for any
morphism of presheaves of rings `α : R ⟶ R'`. -/
noncomputable def restrictScalarsCompToPresheaf (α : R ⟶ R') :
    restrictScalars.{v} α ⋙ toPresheaf R ≅ toPresheaf R' := Iso.refl _

@[simp]
theorem restrictScalars.map_app_hom_apply (α : R ⟶ R') {M M' : PresheafOfModules.{v} R'} (g : M ⟶ M')
    {X : Cᵒᵖ} (m : ((restrictScalars α).obj M).obj X) :
    ((restrictScalars α).map g).app X m = g.app X m := rfl

@[simp]
theorem restrictScalars.smul_def (α : R ⟶ R') {M : PresheafOfModules.{v} R'} {X : Cᵒᵖ}
    (r : R.obj X) (m : ((restrictScalars α).obj M).obj X) :
    r • m = α.app X r • show M.obj X from m :=
  rfl

theorem restrictScalars.smul_def' (α : R ⟶ R') {M : PresheafOfModules.{v} R'} {X : Cᵒᵖ}
    (r : R.obj X) (m : M.obj X) :
    r • (show ((restrictScalars α).obj M).obj X from m) = α.app X r • m :=
  rfl

section

variable {α β : R ⟶ R'} (e : α = β)

/-- Restriction of scalars along equal morphisms are naturally isomorphic. -/
noncomputable def restrictScalarsCongr : restrictScalars α ≅ restrictScalars β :=
  NatIso.ofComponents <| fun M ↦ PresheafOfModules.isoMk <|
    fun X ↦ (ModuleCat.restrictScalarsCongr (by subst e; rfl)).app (M.obj X)

@[simp]
lemma restrictScalarsCongr_symm : (restrictScalarsCongr e).symm = restrictScalarsCongr e.symm :=
  rfl

@[simp]
lemma restrictScalarsCongr_hom_app_app_hom_apply
    {M : PresheafOfModules.{v} R'} {X : Cᵒᵖ} (m : M.obj X) :
    ((restrictScalarsCongr e).hom.app M).app X m = m :=
  rfl

@[simp]
lemma restrictScalarsCongr_inv_app_app_hom_apply
    {M : PresheafOfModules.{v} R'} {X : Cᵒᵖ} (m : M.obj X) :
    ((restrictScalarsCongr e).inv.app M).app X m = m :=
  rfl

end

section

variable (f : R ⟶ R) (hf : f = 𝟙 R)

/-- The restriction of scalars by a morphism that is the identity identifies to the
identity functor. -/
noncomputable def restrictScalarsId' : restrictScalars f ≅ 𝟭 _ :=
  NatIso.ofComponents <| fun M ↦ PresheafOfModules.isoMk <|
    fun X ↦ ModuleCat.restrictScalarsId'App (f.app X).hom (by subst hf; rfl) (M.obj X)

@[simp]
lemma restrictScalarsId'_hom_app_app_hom_apply
    {M : PresheafOfModules.{v} R} {X : Cᵒᵖ} (m : M.obj X) :
    ((restrictScalarsId' f hf).hom.app M).app X m = m :=
  rfl

@[simp]
lemma restrictScalarsId'_inv_app_app_hom_apply
    {M : PresheafOfModules.{v} R} {X : Cᵒᵖ} (m : M.obj X) :
    ((restrictScalarsId' f hf).inv.app M).app X m = m :=
  rfl

@[reassoc]
lemma restrictScalarsId'_app_hom_naturality {M N : PresheafOfModules R} (φ : M ⟶ N) :
    (restrictScalars f).map φ ≫ ((restrictScalarsId' f hf).app N).hom =
      ((restrictScalarsId' f hf).app M).hom ≫ φ :=
  (restrictScalarsId' f hf).hom.naturality φ

@[reassoc]
lemma restrictScalarsId'_app_inv_naturality {M N : PresheafOfModules R} (φ : M ⟶ N) :
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

variable {R₁ R₂ R₃ : Cᵒᵖ ⥤ RingCat.{u}} (f : R₁ ⟶ R₂) (g : R₂ ⟶ R₃) (gf : R₁ ⟶ R₃)
  (hgf : f ≫ g = gf)

/-- The restriction of scalars by a composition of morphisms identifies to the
composition of the restriction of scalars functors. -/
noncomputable def restrictScalarsComp' :
    restrictScalars gf ≅ restrictScalars g ⋙ restrictScalars f :=
  NatIso.ofComponents <| fun M ↦ PresheafOfModules.isoMk <|
    fun X ↦ ModuleCat.restrictScalarsComp'App (f.app X).hom (g.app X).hom (gf.app X).hom
      (by subst hgf; rfl) (M.obj X)

@[simp]
lemma restrictScalarsComp'_hom_app_app_hom_apply
    {M : PresheafOfModules.{v} R₃} {X : Cᵒᵖ} (m : M.obj X) :
    ((restrictScalarsComp' f g gf hgf).hom.app M).app X m = m :=
  rfl

@[simp]
lemma restrictScalarsComp'_inv_app_app_hom_apply
    {M : PresheafOfModules.{v} R₃} {X : Cᵒᵖ} (m : M.obj X) :
    ((restrictScalarsComp' f g gf hgf).inv.app M).app X m = m :=
  rfl

@[reassoc]
lemma restrictScalarsComp'_app_hom_naturality {M N : PresheafOfModules R₃} (φ : M ⟶ N) :
    (restrictScalars gf).map φ ≫ ((restrictScalarsComp' f g gf hgf).app N).hom =
      ((restrictScalarsComp' f g gf hgf).app M).hom ≫
        (restrictScalars f).map ((restrictScalars g).map φ) :=
  (restrictScalarsComp' f g gf hgf).hom.naturality φ

@[reassoc]
lemma restrictScalarsComp'_app_inv_naturality {M N : PresheafOfModules R₃} (φ : M ⟶ N) :
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

/-- The equivalence of categories `PresheafOfModules R' ≌ PresheafOfModules R` induced by
`α : R ≅ R'`. -/
@[simps]
noncomputable def restrictScalarsEquivalenceOfIso (α : R ≅ R') :
    PresheafOfModules.{v} R' ≌ PresheafOfModules.{v} R where
  functor := restrictScalars α.hom
  inverse := restrictScalars α.inv
  unitIso := (restrictScalarsId R').symm ≪≫ restrictScalarsComp' _ _ _ α.inv_hom_id
  counitIso := (restrictScalarsComp' _ _ _ α.hom_inv_id).symm ≪≫ restrictScalarsId R

instance restrictScalars_isEquivalence_of_isIso (α : R ⟶ R') [IsIso α] :
    (restrictScalars α).IsEquivalence :=
  (restrictScalarsEquivalenceOfIso (asIso α)).isEquivalence_functor

end PresheafOfModules
