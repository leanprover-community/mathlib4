/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.HomEquiv
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

/-!
# Shrinking morphisms in localized categories

Given a class of morphisms `W : MorphismProperty C`, and two objects `X` and `Y`,
we introduce a type-class `HasSmallLocalizedHom.{w} W X Y` which expresses
that in the localized category with respect to `W`, the type of morphisms from `X`
to `Y` is `w`-small for a certain universe `w`. Under this assumption,
we define `SmallHom.{w} W X Y : Type w` as the shrunk type. For any localization
functor `L : C ⥤ D` for `W`, we provide a bijection
`SmallHom.equiv.{w} W L : SmallHom.{w} W X Y ≃ (L.obj X ⟶ L.obj Y)` that is compatible
with the composition of morphisms.

-/

@[expose] public section

universe w'' w w' v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory

open Category

namespace Localization

variable {C : Type u₁} [Category.{v₁} C] (W : MorphismProperty C)
  {D : Type u₂} [Category.{v₂} D]
  {D' : Type u₃} [Category.{v₃} D']

section

variable (L : C ⥤ D) [L.IsLocalization W] (X Y Z : C)

/-- This property holds if the type of morphisms between `X` and `Y`
in the localized category with respect to `W : MorphismProperty C`
is small. -/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the universe `w` would default to a
-- universe output parameter. See Note [universe output parameters and typeclass caching].
@[univ_out_params]
class HasSmallLocalizedHom : Prop where
  small : Small.{w} (W.Q.obj X ⟶ W.Q.obj Y)

attribute [instance] HasSmallLocalizedHom.small

variable {X Y Z}

lemma hasSmallLocalizedHom_iff :
    HasSmallLocalizedHom.{w} W X Y ↔ Small.{w} (L.obj X ⟶ L.obj Y) := by
  constructor
  · intro h
    exact small_map (homEquiv W W.Q L).symm
  · intro h
    exact ⟨small_map (homEquiv W W.Q L)⟩

include L in
lemma hasSmallLocalizedHom_of_isLocalization :
    HasSmallLocalizedHom.{v₂} W X Y := by
  rw [hasSmallLocalizedHom_iff W L]
  infer_instance

variable (X Y) in
lemma small_of_hasSmallLocalizedHom [HasSmallLocalizedHom.{w} W X Y] :
    Small.{w} (L.obj X ⟶ L.obj Y) := by
  rwa [← hasSmallLocalizedHom_iff W]

lemma hasSmallLocalizedHom_iff_of_isos {X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y') :
    HasSmallLocalizedHom.{w} W X Y ↔ HasSmallLocalizedHom.{w} W X' Y' := by
  simp only [hasSmallLocalizedHom_iff W W.Q]
  exact small_congr (Iso.homCongr (W.Q.mapIso e) (W.Q.mapIso e'))

lemma hasSmallLocalizedHom_of_isos {X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y')
    [HasSmallLocalizedHom.{w} W X Y] :
    HasSmallLocalizedHom.{w} W X' Y' := by
  rwa [← hasSmallLocalizedHom_iff_of_isos _ e e']

variable (X) in
lemma hasSmallLocalizedHom_iff_target {Y Y' : C} (f : Y ⟶ Y') (hf : W f) :
    HasSmallLocalizedHom.{w} W X Y ↔ HasSmallLocalizedHom.{w} W X Y' := by
  simp only [hasSmallLocalizedHom_iff W W.Q]
  exact small_congr (Iso.homCongr (Iso.refl _) (Localization.isoOfHom W.Q W f hf))

lemma hasSmallLocalizedHom_iff_source {X' : C} (f : X ⟶ X') (hf : W f) (Y : C) :
    HasSmallLocalizedHom.{w} W X Y ↔ HasSmallLocalizedHom.{w} W X' Y := by
  simp only [hasSmallLocalizedHom_iff W W.Q]
  exact small_congr (Iso.homCongr (Localization.isoOfHom W.Q W f hf) (Iso.refl _))

end

/-- The type of morphisms from `X` to `Y` in the localized category
with respect to `W : MorphismProperty C` that is shrunk to `Type w`
when `HasSmallLocalizedHom.{w} W X Y` holds. -/
def SmallHom (X Y : C) [HasSmallLocalizedHom.{w} W X Y] : Type w :=
  Shrink.{w} (W.Q.obj X ⟶ W.Q.obj Y)

namespace SmallHom

/-- The canonical bijection `SmallHom.{w} W X Y ≃ (L.obj X ⟶ L.obj Y)`
when `L` is a localization functor for `W : MorphismProperty C` and
that `HasSmallLocalizedHom.{w} W X Y` holds. -/
noncomputable def equiv (L : C ⥤ D) [L.IsLocalization W] {X Y : C}
    [HasSmallLocalizedHom.{w} W X Y] :
    SmallHom.{w} W X Y ≃ (L.obj X ⟶ L.obj Y) :=
  letI := small_of_hasSmallLocalizedHom.{w} W W.Q X Y
  (equivShrink _).symm.trans (homEquiv W W.Q L)

set_option backward.isDefEq.respectTransparency false in
lemma equiv_equiv_symm (L : C ⥤ D) [L.IsLocalization W]
    (L' : C ⥤ D') [L'.IsLocalization W] (G : D ⥤ D')
    (e : L ⋙ G ≅ L') {X Y : C} [HasSmallLocalizedHom.{w} W X Y]
    (f : L.obj X ⟶ L.obj Y) :
    equiv W L' ((equiv W L).symm f) =
      e.inv.app X ≫ G.map f ≫ e.hom.app Y := by
  dsimp [equiv]
  rw [Equiv.symm_apply_apply, homEquiv_trans]
  apply homEquiv_eq

/-- The element in `SmallHom W X Y` induced by `f : X ⟶ Y`. -/
noncomputable def mk {X Y : C} [HasSmallLocalizedHom.{w} W X Y] (f : X ⟶ Y) :
    SmallHom.{w} W X Y :=
  (equiv.{w} W W.Q).symm (W.Q.map f)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma equiv_mk (L : C ⥤ D) [L.IsLocalization W] {X Y : C}
    [HasSmallLocalizedHom.{w} W X Y] (f : X ⟶ Y) :
    equiv.{w} W L (mk W f) = L.map f := by
  simp [equiv, mk]

variable {W}

/-- The formal inverse in `SmallHom W X Y` of a morphism `f : Y ⟶ X` such that `W f`. -/
noncomputable def mkInv {X Y : C} (f : Y ⟶ X) (hf : W f) [HasSmallLocalizedHom.{w} W X Y] :
    SmallHom.{w} W X Y :=
  (equiv.{w} W W.Q).symm (Localization.isoOfHom W.Q W f hf).inv

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma equiv_mkInv (L : C ⥤ D) [L.IsLocalization W] {X Y : C} (f : Y ⟶ X) (hf : W f)
    [HasSmallLocalizedHom.{w} W X Y] :
    equiv.{w} W L (mkInv f hf) = (Localization.isoOfHom L W f hf).inv := by
  simp only [equiv, mkInv, Equiv.symm_trans_apply, Equiv.symm_symm, homEquiv_symm_apply,
    Equiv.trans_apply, Equiv.symm_apply_apply, homEquiv_isoOfHom_inv]

/-- The composition on `SmallHom W`. -/
noncomputable def comp {X Y Z : C} [HasSmallLocalizedHom.{w} W X Y]
    [HasSmallLocalizedHom.{w} W Y Z] [HasSmallLocalizedHom.{w} W X Z]
    (α : SmallHom.{w} W X Y) (β : SmallHom.{w} W Y Z) :
    SmallHom.{w} W X Z :=
  (equiv W W.Q).symm (equiv W W.Q α ≫ equiv W W.Q β)

set_option backward.isDefEq.respectTransparency false in
lemma equiv_comp (L : C ⥤ D) [L.IsLocalization W] {X Y Z : C} [HasSmallLocalizedHom.{w} W X Y]
    [HasSmallLocalizedHom.{w} W Y Z] [HasSmallLocalizedHom.{w} W X Z]
    (α : SmallHom.{w} W X Y) (β : SmallHom.{w} W Y Z) :
    equiv W L (α.comp β) = equiv W L α ≫ equiv W L β := by
  letI := small_of_hasSmallLocalizedHom.{w} W W.Q X Y
  letI := small_of_hasSmallLocalizedHom.{w} W W.Q Y Z
  obtain ⟨α, rfl⟩ := (equivShrink _).surjective α
  obtain ⟨β, rfl⟩ := (equivShrink _).surjective β
  dsimp [equiv, comp]
  rw [Equiv.symm_apply_apply]
  simp only [homEquiv_refl, homEquiv_comp]

section

variable {X Y Z T : C}

lemma mk_comp_mk [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W Y Z]
    [HasSmallLocalizedHom.{w} W X Z] (f : X ⟶ Y) (g : Y ⟶ Z) :
    (mk W f).comp (mk W g) = mk W (f ≫ g) :=
  (equiv W W.Q).injective (by simp [equiv_comp])

@[simp]
lemma comp_mk_id [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W Y Y]
    (α : SmallHom.{w} W X Y) :
    α.comp (mk W (𝟙 Y)) = α :=
  (equiv W W.Q).injective (by simp [equiv_comp])

@[simp]
lemma mk_id_comp [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W X X]
    (α : SmallHom.{w} W X Y) :
    (mk W (𝟙 X)).comp α = α :=
  (equiv W W.Q).injective (by simp [equiv_comp])

@[simp]
lemma comp_assoc [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W X Z]
    [HasSmallLocalizedHom.{w} W X T] [HasSmallLocalizedHom.{w} W Y Z]
    [HasSmallLocalizedHom.{w} W Y T] [HasSmallLocalizedHom.{w} W Z T]
    (α : SmallHom.{w} W X Y) (β : SmallHom.{w} W Y Z) (γ : SmallHom.{w} W Z T) :
    (α.comp β).comp γ = α.comp (β.comp γ) := by
  apply (equiv W W.Q).injective
  simp only [equiv_comp, assoc]

@[simp]
lemma mk_comp_mkInv [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W Y X]
    [HasSmallLocalizedHom.{w} W Y Y] (f : Y ⟶ X) (hf : W f) :
    (mk W f).comp (mkInv f hf) = mk W (𝟙 Y) :=
  (equiv W W.Q).injective (by simp [equiv_comp])

@[simp]
lemma mkInv_comp_mk [HasSmallLocalizedHom.{w} W X X] [HasSmallLocalizedHom.{w} W X Y]
    [HasSmallLocalizedHom.{w} W Y X] (f : Y ⟶ X) (hf : W f) :
    (mkInv f hf).comp (mk W f) = mk W (𝟙 X) :=
  (equiv W W.Q).injective (by simp [equiv_comp])

end

section ChangeOfUniverse

/-- Up to an equivalence, the type `SmallHom.{w} W X Y n` does not depend on the universe `w`. -/
noncomputable def chgUniv {X Y : C}
    [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w''} W X Y] :
    SmallHom.{w} W X Y ≃ SmallHom.{w''} W X Y :=
  (equiv.{w} W W.Q).trans (equiv.{w''} W W.Q).symm

lemma equiv_chgUniv (L : C ⥤ D) [L.IsLocalization W] {X Y : C}
    [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w''} W X Y]
    (e : SmallHom.{w} W X Y) :
    equiv W L (chgUniv.{w''} e) = equiv W L e := by
  obtain ⟨f, rfl⟩ := (equiv W W.Q).symm.surjective e
  dsimp [chgUniv]
  simp only [Equiv.apply_symm_apply,
    equiv_equiv_symm W _ _ _ (Localization.compUniqFunctor W.Q L W)]

end ChangeOfUniverse

end SmallHom

end Localization

namespace LocalizerMorphism

open Localization

variable {C₁ : Type u₁} [Category.{v₁} C₁] {W₁ : MorphismProperty C₁}
  {C₂ : Type u₂} [Category.{v₂} C₂] {W₂ : MorphismProperty C₂}
  {D₁ : Type u₃} [Category.{v₃} D₁] {D₂ : Type u₄} [Category.{v₄} D₂]
  (Φ : LocalizerMorphism W₁ W₂) (L₁ : C₁ ⥤ D₁) [L₁.IsLocalization W₁]
  (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂]

section

variable {X Y : C₁}

variable [HasSmallLocalizedHom.{w} W₁ X Y]
  [HasSmallLocalizedHom.{w'} W₂ (Φ.functor.obj X) (Φ.functor.obj Y)]

/-- The action of a localizer morphism on `SmallHom`. -/
noncomputable def smallHomMap (f : SmallHom.{w} W₁ X Y) :
    SmallHom.{w'} W₂ (Φ.functor.obj X) (Φ.functor.obj Y) :=
  (SmallHom.equiv W₂ W₂.Q).symm
    (Iso.homCongr ((CatCommSq.iso Φ.functor W₁.Q W₂.Q _).symm.app _)
      ((CatCommSq.iso Φ.functor W₁.Q W₂.Q _).symm.app _)
      ((Φ.localizedFunctor W₁.Q W₂.Q).map ((SmallHom.equiv W₁ W₁.Q) f)))

set_option backward.isDefEq.respectTransparency false in
lemma equiv_smallHomMap (G : D₁ ⥤ D₂) (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G)
    (f : SmallHom.{w} W₁ X Y) :
    (SmallHom.equiv W₂ L₂) (Φ.smallHomMap f) =
      e.hom.app X ≫ G.map (SmallHom.equiv W₁ L₁ f) ≫ e.inv.app Y := by
  obtain ⟨g, rfl⟩ := (SmallHom.equiv W₁ W₁.Q).symm.surjective f
  simp only [smallHomMap, Equiv.apply_symm_apply]
  let G' := Φ.localizedFunctor W₁.Q W₂.Q
  let β := CatCommSq.iso Φ.functor W₁.Q W₂.Q G'
  let E₁ := (uniq W₁.Q L₁ W₁).functor
  let α₁ : W₁.Q ⋙ E₁ ≅ L₁ := compUniqFunctor W₁.Q L₁ W₁
  let E₂ := (uniq W₂.Q L₂ W₂).functor
  let α₂ : W₂.Q ⋙ E₂ ≅ L₂ := compUniqFunctor W₂.Q L₂ W₂
  rw [SmallHom.equiv_equiv_symm W₁ W₁.Q L₁ E₁ α₁,
    SmallHom.equiv_equiv_symm W₂ W₂.Q L₂ E₂ α₂]
  change α₂.inv.app _ ≫ E₂.map (β.hom.app X ≫ G'.map g ≫ β.inv.app Y) ≫ _ = _
  let γ : G' ⋙ E₂ ≅ E₁ ⋙ G := liftNatIso W₁.Q W₁ (W₁.Q ⋙ G' ⋙ E₂) (W₁.Q ⋙ E₁ ⋙ G) _ _
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight β.symm E₂ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ α₂ ≪≫ e ≪≫
      Functor.isoWhiskerRight α₁.symm G ≪≫ Functor.associator _ _ _)
  have hγ : ∀ (X : C₁), γ.hom.app (W₁.Q.obj X) =
      E₂.map (β.inv.app X) ≫ α₂.hom.app (Φ.functor.obj X) ≫
        e.hom.app X ≫ G.map (α₁.inv.app X) := fun X ↦ by
    simp [γ, id_comp, comp_id]
  simp only [Functor.map_comp, ← NatIso.naturality_1 γ, ← Functor.comp_map,
    ← cancel_epi (e.inv.app X), ← cancel_epi (G.map (α₁.hom.app X)),
    ← cancel_epi (γ.hom.app (W₁.Q.obj X)), assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, id_comp,
    Iso.hom_inv_id_app_assoc]
  simp only [hγ, assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    Functor.map_id, id_comp, Iso.hom_inv_id_app_assoc,
    Iso.hom_inv_id_app, Functor.comp_obj, comp_id]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma smallHomMap_mk (f : X ⟶ Y) :
    Φ.smallHomMap (SmallHom.mk _ f) =
      SmallHom.mk _ (Φ.functor.map f) := by
  apply (SmallHom.equiv W₂ W₂.Q).injective
  simp [Φ.equiv_smallHomMap W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q) (CatCommSq.iso _ _ _ _)]

end

section

variable {X Y Z : C₁}

variable [HasSmallLocalizedHom.{w} W₁ X Y] [HasSmallLocalizedHom.{w} W₁ Y Z]
  [HasSmallLocalizedHom.{w} W₁ X Z]
  [HasSmallLocalizedHom.{w'} W₂ (Φ.functor.obj X) (Φ.functor.obj Y)]
  [HasSmallLocalizedHom.{w'} W₂ (Φ.functor.obj Y) (Φ.functor.obj Z)]
  [HasSmallLocalizedHom.{w'} W₂ (Φ.functor.obj X) (Φ.functor.obj Z)]

set_option backward.isDefEq.respectTransparency false in
lemma smallHomMap_comp (f : SmallHom.{w} W₁ X Y) (g : SmallHom.{w} W₁ Y Z) :
    Φ.smallHomMap (f.comp g) = (Φ.smallHomMap f).comp (Φ.smallHomMap g) := by
  apply (SmallHom.equiv W₂ W₂.Q).injective
  simp [Φ.equiv_smallHomMap W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q) (CatCommSq.iso _ _ _ _),
    SmallHom.equiv_comp]

end

section

variable {X Y : C₁} [HasSmallLocalizedHom.{w} W₁ X Y] {X' Y' : C₂}
  [HasSmallLocalizedHom.{w'} W₂ X' X']
  [HasSmallLocalizedHom.{w'} W₂ X' Y']
  [HasSmallLocalizedHom.{w'} W₂ Y' Y']
  (eX : Φ.functor.obj X ≅ X') (eY : Φ.functor.obj Y ≅ Y')

/-- The action of a localizer morphism `Φ` on `SmallHom`. In this version, we allow
the replacement of objects `Φ.functor.obj` by isomorphic objects. -/
noncomputable def smallHomMap' (f : SmallHom.{w} W₁ X Y) :
    SmallHom.{w'} W₂ X' Y' :=
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eX.symm eY.symm
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eX.symm (Iso.refl Y')
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eY.symm (Iso.refl Y')
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ (Iso.refl X') eX.symm
  (SmallHom.mk _ eX.inv).comp ((Φ.smallHomMap f).comp (SmallHom.mk _ eY.hom))

lemma equiv_smallHomMap' (G : D₁ ⥤ D₂) (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G)
    (f : SmallHom.{w} W₁ X Y) :
    SmallHom.equiv W₂ L₂ (Φ.smallHomMap' eX eY f) =
      L₂.map eX.inv ≫ e.hom.app X ≫ G.map (SmallHom.equiv W₁ L₁ f) ≫
        e.inv.app Y ≫ L₂.map eY.hom := by
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eY.symm (Iso.refl Y')
  simp [smallHomMap', SmallHom.equiv_comp, Φ.equiv_smallHomMap L₁ L₂ G e]

@[simp]
lemma smallHomMap'_mk (f : X ⟶ Y) :
    Φ.smallHomMap' eX eY (SmallHom.mk _ f) =
      SmallHom.mk _ (eX.inv ≫ Φ.functor.map f ≫ eY.hom) := by
  simp [smallHomMap', SmallHom.mk_comp_mk]

end

section

variable {X Y Z : C₁} [HasSmallLocalizedHom.{w} W₁ X Y] [HasSmallLocalizedHom.{w} W₁ Y Z]
  [HasSmallLocalizedHom.{w} W₁ X Z] {X' Y' Z' : C₂}
  [HasSmallLocalizedHom.{w'} W₂ X' X'] [HasSmallLocalizedHom.{w'} W₂ Y' Y']
  [HasSmallLocalizedHom.{w'} W₂ Z' Z'] [HasSmallLocalizedHom.{w'} W₂ X' Y']
  [HasSmallLocalizedHom.{w'} W₂ Y' Z'] [HasSmallLocalizedHom.{w'} W₂ X' Z']
  (eX : Φ.functor.obj X ≅ X') (eY : Φ.functor.obj Y ≅ Y') (eZ : Φ.functor.obj Z ≅ Z')

lemma smallHomMap'_comp (f : SmallHom.{w} W₁ X Y) (g : SmallHom.{w} W₁ Y Z) :
    Φ.smallHomMap' eX eZ (f.comp g) =
      (Φ.smallHomMap' eX eY f).comp (Φ.smallHomMap' eY eZ g) := by
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eX.symm eY.symm
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eY.symm (Iso.refl Y')
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eX.symm (Iso.refl Z')
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eY.symm eZ.symm
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eY.symm (Iso.refl Z')
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ (Iso.refl Y') eY.symm
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eY.symm eY.symm
  simp only [smallHomMap', smallHomMap_comp, SmallHom.comp_assoc]
  congr 2
  rw [← SmallHom.comp_assoc, SmallHom.mk_comp_mk, eY.hom_inv_id, SmallHom.mk_id_comp]

end

end LocalizerMorphism

end CategoryTheory
