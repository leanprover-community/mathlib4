/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Bicategory.Functor.Cat
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

/-!
# Codescent data

-/

universe t t' w v v' u u'

namespace CategoryTheory

open Category Limits Bicategory

namespace Pseudofunctor

variable {C : Type u} [Bicategory.{w, v} C]
  (F : Pseudofunctor C Cat.{v', u'}) {ι : Type t} (X : ι → C)

/-
Let us use `CodescentData` for a "covariant" pseudofunctor from `F` to `Cat`.
The "codescent" property for `F`, a family of objects `X : ι → C` and
an initial object `X₀`, there is an equivalence of categories
(induced by `toCodescentDataOfIsInitial`) from `F.obj X₀` to
`F.CodescentData X`.

We shall use the name `DescentData` for the case of a pseudofunctor
from the locally discrete bicategory associated to the opposite category
of `C`, especially when `C` is endowed with a Grothendieck topology, and
for this we shall apply `CodescentData` to the restriction of the
pseudofunctor to `LocallyDiscrete (Over X)ᵒᵖ` for `X : C`.

-/

structure CodescentData where
  obj (i : ι) : F.obj (X i)
  iso ⦃Y : C⦄ ⦃i₁ i₂ : ι⦄ (f₁ : X i₁ ⟶ Y) (f₂ : X i₂ ⟶ Y) :
      (F.map f₁).obj (obj i₁) ≅ (F.map f₂).obj (obj i₂)
  iso_comp' ⦃Y' Y : C⦄ (g : Y ⟶ Y') ⦃i₁ i₂ : ι⦄ (f₁ : X i₁ ⟶ Y) (f₂ : X i₂ ⟶ Y)
      (f₁g : X i₁ ⟶ Y') (f₂g : X i₂ ⟶ Y') (hf₁g : f₁ ≫ g = f₁g) (hf₂g : f₂ ≫ g = f₂g) :
      iso f₁g f₂g =
        (F.mapComp' f₁ g f₁g).app (obj i₁) ≪≫ Functor.mapIso (F.map g) (iso f₁ f₂) ≪≫
          (F.mapComp' f₂ g f₂g).symm.app (obj i₂)
  iso_trans ⦃Y : C⦄ ⦃i₁ i₂ i₃ : ι⦄ (f₁ : X i₁ ⟶ Y) (f₂ : X i₂ ⟶ Y) (f₃ : X i₃ ⟶ Y) :
    iso f₁ f₂ ≪≫ iso f₂ f₃ = iso f₁ f₃ := by aesop_cat

namespace CodescentData

variable {F X}

@[simps]
def mk' (obj : ∀ i, F.obj (X i))
    (hom : ∀ ⦃Y : C⦄ ⦃i₁ i₂ : ι⦄ (f₁ : X i₁ ⟶ Y) (f₂ : X i₂ ⟶ Y),
      (F.map f₁).obj (obj i₁) ⟶ (F.map f₂).obj (obj i₂))
    (hom_comp' : ∀ ⦃Y' Y : C⦄ (g : Y ⟶ Y') ⦃i₁ i₂ : ι⦄ (f₁ : X i₁ ⟶ Y) (f₂ : X i₂ ⟶ Y)
      (f₁g : X i₁ ⟶ Y') (f₂g : X i₂ ⟶ Y') (hf₁g : f₁ ≫ g = f₁g) (hf₂g : f₂ ≫ g = f₂g),
      hom f₁g f₂g =
        (F.mapComp' f₁ g f₁g).hom.app _ ≫
          (F.map g).map (hom f₁ f₂) ≫
            (F.mapComp' f₂ g f₂g).inv.app _ := by aesop_cat)
    (hom_self : ∀ ⦃Y : C⦄ ⦃i : ι⦄ (f : X i ⟶ Y), hom f f = 𝟙 _ := by aesop_cat)
    (comp_hom : ∀ ⦃Y : C⦄ ⦃i₁ i₂ i₃ : ι⦄ (f₁ : X i₁ ⟶ Y) (f₂ : X i₂ ⟶ Y) (f₃ : X i₃ ⟶ Y),
      hom f₁ f₂ ≫ hom f₂ f₃ = hom f₁ f₃ := by aesop_cat) : F.CodescentData X where
  obj := obj
  iso Y i₁ i₂ f₁ f₂ :=
    { hom := hom f₁ f₂
      inv := hom f₂ f₁ }
  iso_comp' Y' Y g i₁ i₂ f₁ f₂ f₁g f₂g hf₁g hf₂g := by
    ext
    exact hom_comp' g f₁ f₂ f₁g f₂g hf₁g hf₂g

section

variable (D : F.CodescentData X)

@[reassoc (attr := simp)]
lemma iso_hom_iso_hom ⦃Y : C⦄ ⦃i₁ i₂ i₃ : ι⦄
    (f₁ : X i₁ ⟶ Y) (f₂ : X i₂ ⟶ Y) (f₃ : X i₃ ⟶ Y) :
    (D.iso f₁ f₂).hom ≫ (D.iso f₂ f₃).hom = (D.iso f₁ f₃).hom := by
  simp [← D.iso_trans f₁ f₂ f₃]

@[simp]
lemma iso_self ⦃Y : C⦄ ⦃i : ι⦄ (f : X i ⟶ Y) :
    D.iso f f = Iso.refl _ := by
  ext
  simp [← cancel_epi (D.iso f f).hom]

@[simp]
lemma iso_symm ⦃Y : C⦄ ⦃i₁ i₂ : ι⦄
    (f₁ : X i₁ ⟶ Y) (f₂ : X i₂ ⟶ Y) :
    (D.iso f₁ f₂).symm = D.iso f₂ f₁ := by
  ext
  simp [← cancel_epi (D.iso f₁ f₂).hom]

lemma iso_inv ⦃Y : C⦄ ⦃i₁ i₂ : ι⦄
    (f₁ : X i₁ ⟶ Y) (f₂ : X i₂ ⟶ Y) :
    (D.iso f₁ f₂).inv = (D.iso f₂ f₁).hom :=
  congr_arg Iso.hom (D.iso_symm f₁ f₂)

end

@[ext]
structure Hom (D₁ D₂ : F.CodescentData X) where
  hom (i : ι) : D₁.obj i ⟶ D₂.obj i
  comm ⦃Y : C⦄ ⦃i₁ i₂ : ι⦄ (f₁ : X i₁ ⟶ Y) (f₂ : X i₂ ⟶ Y) :
    (F.map f₁).map (hom i₁) ≫ (D₂.iso f₁ f₂).hom =
      (D₁.iso f₁ f₂).hom ≫ (F.map f₂).map (hom i₂) := by aesop_cat

attribute [reassoc (attr := simp)] Hom.comm

instance : Category (F.CodescentData X) where
  Hom := Hom
  id D := { hom i := 𝟙 _ }
  comp {D₁ D₂ D₃} φ ψ :=
    { hom i := φ.hom i ≫ ψ.hom i
      comm Y i₁ i₂ f₁ f₂ := by
        simp only [Functor.map_comp, assoc]
        rw [ψ.comm, φ.comm_assoc] }

@[ext]
lemma hom_ext {D₁ D₂ : F.CodescentData X} {f g : D₁ ⟶ D₂}
    (h : ∀ i, f.hom i = g.hom i) : f = g :=
  Hom.ext (funext h)

@[simp]
lemma id_hom (D : F.CodescentData X) (i : ι) : Hom.hom (𝟙 D) i = 𝟙 _ := rfl

@[simp, reassoc]
lemma comp_hom {D₁ D₂ D₃ : F.CodescentData X} (f : D₁ ⟶ D₂) (g : D₂ ⟶ D₃) (i : ι) :
    (f ≫ g).hom i = f.hom i ≫ g.hom i := rfl


namespace Hom

variable {D₁ D₂ : F.CodescentData X} (f : D₁ ⟶ D₂)

@[reassoc]
lemma map_map ⦃Y : C⦄ ⦃i₁ i₂ : ι⦄ (f₁ : X i₁ ⟶ Y) (f₂ : X i₂ ⟶ Y) :
    (F.map f₁).map (f.hom i₁) =
      (D₁.iso f₁ f₂).hom ≫ (F.map f₂).map (f.hom i₂) ≫ (D₂.iso f₁ f₂).inv := by
  rw [← comm_assoc, Iso.hom_inv_id, comp_id]

@[reassoc]
lemma map_map' ⦃Y : C⦄ ⦃i₁ i₂ : ι⦄ (f₁ : X i₁ ⟶ Y) (f₂ : X i₂ ⟶ Y) :
    (F.map f₂).map (f.hom i₂) =
      (D₁.iso f₁ f₂).inv ≫ (F.map f₁).map (f.hom i₁) ≫ (D₂.iso f₁ f₂).hom := by
  simp

end Hom

variable {ι' : Type t'} {X' : ι' → C} {p : ι' → ι} (π : ∀ i', X (p i') ⟶ X' i')

abbrev pullbackObjObj (D : F.CodescentData X) (i' : ι') : F.obj (X' i') :=
  (F.map (π i')).obj (D.obj (p i'))

def pullbackObjIso
    (D : F.CodescentData X) ⦃Y : C⦄ ⦃i₁ i₂ : ι'⦄ (f₁ : X' i₁ ⟶ Y) (f₂ : X' i₂ ⟶ Y) :
    (F.map f₁).obj (pullbackObjObj π D i₁) ≅ (F.map f₂).obj (pullbackObjObj π D i₂) :=
  (F.mapComp' (π i₁) f₁ _ rfl).symm.app _ ≪≫
      D.iso _ _ ≪≫ (F.mapComp' (π i₂) f₂ _ rfl).app _

def pullbackObjIso_eq
    (D : F.CodescentData X) ⦃Y : C⦄ ⦃i₁ i₂ : ι'⦄ (f₁ : X' i₁ ⟶ Y) (f₂ : X' i₂ ⟶ Y)
    (g₁ : X (p i₁) ⟶ Y) (g₂ : X (p i₂) ⟶ Y) (hg₁ : g₁ = π i₁ ≫ f₁) (hg₂ : g₂ = π i₂ ≫ f₂) :
    pullbackObjIso π D f₁ f₂ = (F.mapComp' (π i₁) f₁ g₁).symm.app _ ≪≫
      D.iso g₁ g₂ ≪≫ (F.mapComp' (π i₂) f₂ g₂).app _ := by
  subst hg₁ hg₂
  rfl

@[reassoc (attr := simp)]
lemma pullbackObjIso_hom_comp
    (D : F.CodescentData X) ⦃Y : C⦄ ⦃i₁ i₂ i₃ : ι'⦄
    (f₁ : X' i₁ ⟶ Y) (f₂ : X' i₂ ⟶ Y) (f₃ : X' i₃ ⟶ Y)
    (g₁ : X (p i₁) ⟶ Y) (g₂ : X (p i₂) ⟶ Y) (g₃ : X (p i₃) ⟶ Y)
    (hg₁ : g₁ = π i₁ ≫ f₁) (hg₂ : g₂ = π i₂ ≫ f₂) (hg₃ : g₃ = π i₃ ≫ f₃) :
    (pullbackObjIso π D f₁ f₂).hom ≫ (pullbackObjIso π D f₂ f₃).hom =
      (pullbackObjIso π D f₁ f₃).hom := by
  simp [pullbackObjIso_eq π D _ _ g₁ g₂ hg₁ hg₂, pullbackObjIso_eq π D _ _ g₂ g₃ hg₂ hg₃,
    pullbackObjIso_eq π D _ _ g₁ g₃ hg₁ hg₃]

variable [Strict C]

@[simps]
def pullbackObj (D : F.CodescentData X) : F.CodescentData X' where
  obj := pullbackObjObj π D
  iso := pullbackObjIso π D
  iso_comp' Y' Y g i₁ i₂ f₁ f₂ f₁g f₂g hf₁g hf₂g := by
    ext
    dsimp
    rw [pullbackObjIso_eq π D f₁ f₂ _ _ rfl rfl,
      pullbackObjIso_eq π D f₁g f₂g _ _ rfl rfl,
      D.iso_comp' g (π i₁ ≫ f₁) (π i₂ ≫ f₂) (π i₁ ≫ f₁g) (π i₂ ≫ f₂g)
        (by aesop_cat) (by aesop_cat)]
    dsimp [pullbackObjObj]
    simp only [assoc, Functor.map_comp_assoc]
    rw [F.mapComp'_inv_app_comp_mapComp'_hom_app_assoc _ _ _ _ _ _ rfl hf₁g rfl,
      F.mapComp'_inv_app_comp_mapComp'_hom_app' _ _ _ _ _ _ rfl hf₂g rfl]
  iso_trans Y i₁ i₂ i₃ f₁ f₂ f₃ := by ext; simp

abbrev pullbackMapHom {D₁ D₂ : F.CodescentData X} (f : D₁ ⟶ D₂) (i' : ι'):
    pullbackObjObj π D₁ i' ⟶ pullbackObjObj π D₂ i' :=
  (F.map (π i')).map (f.hom (p i'))

attribute [local simp] pullbackObjIso pullbackMapHom

@[simps]
def pullbackMap {D₁ D₂ : F.CodescentData X} (f : D₁ ⟶ D₂) :
    pullbackObj π D₁ ⟶ pullbackObj π D₂ where
  hom i' := pullbackMapHom π f i'

-- note: up to a natural isomorphism, this should not depend on the choice of `p` or `π`,
-- but only that any object `X' i'` is a target of a map from some `X i`
@[simps]
def pullback : F.CodescentData X ⥤ F.CodescentData X' where
  obj := pullbackObj π
  map f := pullbackMap π f

end CodescentData

variable [Strict C]

def toCodescentDataOfIsInitial (X₀ : C) (hX₀ : IsInitial X₀) :
    F.obj X₀ ⥤ F.CodescentData X where
  obj A :=
    { obj i := (F.map (hX₀.to (X i))).obj A
      iso Y i₁ i₂ f₁ f₂ :=
        (F.mapComp' (hX₀.to (X i₁)) f₁ (hX₀.to Y) (by simp)).symm.app A ≪≫
          (F.mapComp' (hX₀.to (X i₂)) f₂ (hX₀.to Y) (by simp)).app A
      iso_comp' Y' Y g i₁ i₂ f₁ f₂ f₁g f₂g hf₁g hf₂g := by
        ext
        dsimp
        rw [Functor.map_comp, assoc, F.mapComp'₀₁₃_inv_app_assoc (hX₀.to (X i₁))
          f₁ g (hX₀.to Y) f₁g (hX₀.to Y') (by simp) hf₁g (by simp) A,
          F.mapComp'₀₁₃_hom_app (hX₀.to (X i₂))
            f₂ g (hX₀.to Y) f₂g (hX₀.to Y') (by simp) hf₂g (by simp) A,
            Iso.inv_hom_id_app_assoc]
      iso_trans := by
        intros
        ext
        dsimp
        rw [assoc, Iso.hom_inv_id_app_assoc] }
  map {A B} f :=
    { hom i := (F.map _).map f
      comm := by
        intros
        dsimp
        rw [mapComp'_inv_naturality_assoc, NatTrans.naturality, assoc, Cat.comp_map] }
  map_id := by intros; ext; dsimp; simp only [Functor.map_id]
  map_comp := by intros; ext; dsimp; simp only [Functor.map_comp]

end Pseudofunctor

end CategoryTheory
