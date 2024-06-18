/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.LocalizerMorphism
import Mathlib.Logic.Small.Defs

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

universe w w' v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {W : MorphismProperty C}
  {C' : Type u₂} [Category.{v₂} C'] {W' : MorphismProperty C'}
  {D : Type u₃} [Category.{v₃} D]
  {D' : Type u₄} [Category.{v₄} D']

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W W')
  (L : C ⥤ D) [L.IsLocalization W]
  (L' : C' ⥤ D') [L'.IsLocalization W'] {X Y : C}

noncomputable def homMap (f : L.obj X ⟶ L.obj Y) :
    L'.obj (Φ.functor.obj X) ⟶ L'.obj (Φ.functor.obj Y) :=
  Iso.homEquiv ((CatCommSq.iso _ _ _ _).symm.app _) ((CatCommSq.iso _ _ _ _).symm.app _)
    ((Φ.localizedFunctor L L').map f)

lemma homMap_apply (G : D ⥤ D') (e : Φ.functor ⋙ L' ≅ L ⋙ G) (f : L.obj X ⟶ L.obj Y) :
    Φ.homMap L L' f = e.hom.app X ≫ G.map f ≫ e.inv.app Y := by
  let G' := Φ.localizedFunctor L L'
  let e' := CatCommSq.iso Φ.functor L L' G'
  change e'.hom.app X ≫ G'.map f ≫ e'.inv.app Y = _
  letI : Localization.Lifting L W (Φ.functor ⋙ L') G := ⟨e.symm⟩
  let α : G' ≅ G := Localization.liftNatIso L W (L ⋙ G') (Φ.functor ⋙ L') _ _ e'.symm
  have : e = e' ≪≫ isoWhiskerLeft _ α := by
    ext X
    dsimp [α]
    rw [Localization.liftNatTrans_app]
    erw [Category.id_comp]
    rw [Iso.hom_inv_id_app_assoc]
    rfl
  simp [this]

end LocalizerMorphism

variable (W)

namespace MorphismProperty

variable (L : C ⥤ D) [L.IsLocalization W] (L' : C ⥤ D') [L'.IsLocalization W] (X Y Z : C)

/-- This property holds if the type of morphisms between `X` and `Y`
in the localized category with respect to `W : MorphismProperty C`
is small. -/
class HasSmallLocalizedHom : Prop where
  small : Small.{w} (W.Q.obj X ⟶ W.Q.obj Y)

variable {X Y Z}

/-- Bijection between types of morphisms in two localized categories
for the same class of morphisms `W`. -/
noncomputable def localizationsHomEquiv :
    (L.obj X ⟶ L.obj Y) ≃ (L'.obj X ⟶ L'.obj Y) :=
  (Localization.uniq L L' W).fullyFaithfulFunctor.homEquiv.trans
    (Iso.homEquiv ((Localization.compUniqFunctor L L' W).app X)
      ((Localization.compUniqFunctor L L' W).app Y))

lemma localizationsHomEquiv_eq_homMap (f : L.obj X ⟶ L.obj Y) :
    localizationsHomEquiv W L L' f = (LocalizerMorphism.id W).homMap L L' f :=
  ((LocalizerMorphism.id W).homMap_apply L L' (Localization.uniq L L' W).functor
    (Localization.compUniqFunctor L L' W).symm f).symm

lemma localizationsHomEquiv_eq (G : D ⥤ D') (e : L ⋙ G ≅ L') (f : L.obj X ⟶ L.obj Y) :
    localizationsHomEquiv W L L' f = e.inv.app X ≫ G.map f ≫ e.hom.app Y := by
  rw [localizationsHomEquiv_eq_homMap]
  exact (LocalizerMorphism.id W).homMap_apply L L' G e.symm f

@[simp]
lemma localizationsHomEquiv_map (f : X ⟶ Y) :
    localizationsHomEquiv W L L' (L.map f) = L'.map f := by
  dsimp [localizationsHomEquiv]
  erw [← NatTrans.naturality_assoc]
  simp

variable (X) in
@[simp]
lemma localizationsHomEquiv_id :
    localizationsHomEquiv W L L' (𝟙 (L.obj X)) = 𝟙 (L'.obj X) := by
  simpa using localizationsHomEquiv_map W L L' (𝟙 X)

@[simp]
lemma localizationHomEquiv_refl :
    localizationsHomEquiv W L L (X := X) (Y := Y) = Equiv.refl _ := by
  ext f
  simpa using localizationsHomEquiv_eq W L L (𝟭 _) (Iso.refl _) f

lemma localizationHomEquiv_comp (f : L.obj X ⟶ L.obj Y) (g : L.obj Y ⟶ L.obj Z) :
    localizationsHomEquiv W L L' (f ≫ g) =
      localizationsHomEquiv W L L' f ≫ localizationsHomEquiv W L L' g := by
  simp [localizationsHomEquiv]

lemma localizationsHomEquiv_isoOfHom_inv (f : X ⟶ Y) (hf : W f):
    localizationsHomEquiv W L L' ((Localization.isoOfHom L W f hf).inv) =
      (Localization.isoOfHom L' W f hf).inv := by
  rw [← cancel_mono (Localization.isoOfHom L' W f hf).hom, Iso.inv_hom_id,
    Localization.isoOfHom_hom, ← localizationsHomEquiv_map W L,
    ← localizationHomEquiv_comp, Localization.isoOfHom_inv, IsIso.inv_hom_id,
    localizationsHomEquiv_id]

lemma hasSmallLocalizedHom_iff :
    HasSmallLocalizedHom.{w} W X Y ↔ Small.{w} (L.obj X ⟶ L.obj Y) := by
  constructor
  · intro h
    have := h.small
    exact small_map (localizationsHomEquiv W W.Q L).symm
  · intro h
    exact ⟨small_map (localizationsHomEquiv W W.Q L)⟩

lemma hasSmallLocalizedHom_of_isLocalization :
    HasSmallLocalizedHom.{v₃} W X Y := by
  rw [W.hasSmallLocalizedHom_iff L]
  infer_instance

variable (X Y) in
lemma small_of_hasSmallLocalizedHom [HasSmallLocalizedHom.{w} W X Y] :
    Small.{w} (L.obj X ⟶ L.obj Y) := by
  rwa [← W.hasSmallLocalizedHom_iff]

lemma hasSmallLocalizedHom_iff_of_isos {X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y') :
    HasSmallLocalizedHom.{w} W X Y ↔ HasSmallLocalizedHom.{w} W X' Y' := by
  simp only [W.hasSmallLocalizedHom_iff W.Q]
  exact small_congr (Iso.homEquiv (W.Q.mapIso e) (W.Q.mapIso e'))

end MorphismProperty

namespace Localization

variable (Φ : LocalizerMorphism W W') (L : C ⥤ D) [L.IsLocalization W]
  (L' : C' ⥤ D') [L'.IsLocalization W'] (X Y Z : C)

open MorphismProperty

/-- The type of morphisms from `X` to `Y` in the localized category
with respect to `W : MorphismProperty C` that is shrunk to `Type w`
when `HasSmallLocalizedHom.{w} W X Y` holds. -/
def SmallHom [HasSmallLocalizedHom.{w} W X Y] : Type w :=
  letI := small_of_hasSmallLocalizedHom.{w} W W.Q X Y
  Shrink.{w} (W.Q.obj X ⟶ W.Q.obj Y)

namespace SmallHom

variable {X Y Z}

/-- The canonical bijection `SmallHom.{w} W X Y ≃ (L.obj X ⟶ L.obj Y)`
when `L` is a localization functor for `W : MorphismProperty C` and
that `HasSmallLocalizedHom.{w} W X Y` holds. -/
noncomputable def equiv [HasSmallLocalizedHom.{w} W X Y] :
    SmallHom.{w} W X Y ≃ (L.obj X ⟶ L.obj Y) :=
  letI := small_of_hasSmallLocalizedHom.{w} W W.Q X Y
  (equivShrink _).symm.trans (W.localizationsHomEquiv W.Q L)

variable [HasSmallLocalizedHom.{w} W X Y]

/-- The element in `SmallHom W X Y` induced by `f : X ⟶ Y`. -/
noncomputable def mk (f : X ⟶ Y) : SmallHom.{w} W X Y :=
  (equiv.{w} W W.Q).symm (W.Q.map f)

@[simp]
lemma equiv_mk (f : X ⟶ Y) : equiv.{w} W L (mk W f) = L.map f := by
  simp [equiv, mk]

variable {W} in
/-- The formal inverse in `SmallHom W X Y` of a morphism `f : Y ⟶ X` such that `W f`. -/
noncomputable def mkInv (f : Y ⟶ X) (hf : W f) : SmallHom.{w} W X Y :=
  (equiv.{w} W W.Q).symm (Localization.isoOfHom W.Q W f hf).inv

@[simp]
lemma equiv_mkInv (f : Y ⟶ X) (hf : W f) :
    equiv.{w} W L (mkInv f hf) = (Localization.isoOfHom L W f hf).inv := by
  dsimp only [equiv, mkInv]
  simp only [localizationHomEquiv_refl, Equiv.trans_refl, Equiv.symm_symm,
    Equiv.trans_apply, Equiv.symm_apply_apply, localizationsHomEquiv_isoOfHom_inv]

section

variable [HasSmallLocalizedHom.{w} W Y Z] [HasSmallLocalizedHom.{w} W X Z]

variable {W}

variable (α : SmallHom.{w} W X Y) (β : SmallHom.{w} W Y Z)

/-- The composition on `SmallHom W`. -/
noncomputable def comp (α : SmallHom.{w} W X Y) (β : SmallHom.{w} W Y Z) :
    SmallHom.{w} W X Z :=
  (equiv W W.Q).symm (equiv W W.Q α ≫ equiv W W.Q β)

lemma equiv_comp : equiv W L (α.comp β) = equiv W L α ≫ equiv W L β := by
  letI := small_of_hasSmallLocalizedHom.{w} W W.Q X Y
  letI := small_of_hasSmallLocalizedHom.{w} W W.Q Y Z
  obtain ⟨α, rfl⟩ := (equivShrink _).surjective α
  obtain ⟨β, rfl⟩ := (equivShrink _).surjective β
  dsimp [equiv, comp]
  rw [Equiv.symm_apply_apply]
  erw [(equivShrink _).symm_apply_apply, (equivShrink _).symm_apply_apply]
  rw [← localizationHomEquiv_comp, localizationHomEquiv_refl, Equiv.refl_symm,
    Equiv.refl_apply, Equiv.refl_apply, localizationHomEquiv_comp]

lemma mk_comp_mk (f : X ⟶ Y) (g : Y ⟶ Z) :
    (mk W f).comp (mk W g) = mk W (f ≫ g) :=
  (equiv W W.Q).injective (by simp [equiv_comp])

end

section

variable [HasSmallLocalizedHom.{w} W Y X]

@[simp]
lemma mk_comp_mkInv (f : Y ⟶ X) (hf : W f) [HasSmallLocalizedHom.{w} W Y Y] :
    (mk W f).comp (mkInv f hf) = mk W (𝟙 Y) :=
  (equiv W W.Q).injective (by simp [equiv_comp])

@[simp]
lemma mkInv_comp_mk (f : Y ⟶ X) (hf : W f) [HasSmallLocalizedHom.{w} W X X] :
    (mkInv f hf).comp (mk W f)= mk W (𝟙 X) :=
  (equiv W W.Q).injective (by simp [equiv_comp])

end

variable {W}

section

variable [W'.HasSmallLocalizedHom (Φ.functor.obj X) (Φ.functor.obj Y)]

/-- The action of a localizer morphism on `SmallHom`. -/
noncomputable def map (f : SmallHom.{w} W X Y) :
    SmallHom.{w'} W' (Φ.functor.obj X) (Φ.functor.obj Y) :=
  (equiv W' W'.Q).symm
    (Iso.homEquiv ((CatCommSq.iso Φ.functor W.Q W'.Q _).symm.app _)
      ((CatCommSq.iso Φ.functor W.Q W'.Q _).symm.app _)
      ((Φ.localizedFunctor W.Q W'.Q).map ((equiv W W.Q) f)))

lemma equiv_map (G : D ⥤ D') (e : Φ.functor ⋙ L' ≅ L ⋙ G) (f : SmallHom.{w} W X Y) :
    (equiv W' L') (f.map Φ) = e.hom.app X ≫ G.map (equiv W L f) ≫ e.inv.app Y := by
  sorry

end

variable [HasSmallLocalizedHom.{w} W Y Z] [HasSmallLocalizedHom.{w} W X Z]
  [W'.HasSmallLocalizedHom (Φ.functor.obj X) (Φ.functor.obj Y)]
  [W'.HasSmallLocalizedHom (Φ.functor.obj Y) (Φ.functor.obj Z)]
  [W'.HasSmallLocalizedHom (Φ.functor.obj X) (Φ.functor.obj Z)]

lemma map_comp (f : SmallHom.{w} W X Y) (g : SmallHom.{w} W Y Z) :
    (f.comp g).map Φ = (f.map Φ).comp (g.map Φ) := by
  apply (equiv W' W'.Q).injective
  simp [equiv_map Φ W.Q W'.Q (Φ.localizedFunctor W.Q W'.Q) (CatCommSq.iso _ _ _ _), equiv_comp]

end SmallHom

end Localization

end CategoryTheory
