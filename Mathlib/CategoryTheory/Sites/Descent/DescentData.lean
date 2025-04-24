/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

/-!
# Descent data

-/

universe t w v' u' v u

namespace CategoryTheory

open Category Limits Bicategory

namespace Pseudofunctor

section

variable {B C : Type*} [Bicategory B] [Bicategory C]
  (F : Pseudofunctor B C)
  {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (fg : a ⟶ c) (hfg : f ≫ g = fg := by aesop_cat)

def mapComp' : F.map fg ≅ F.map f ≫ F.map g := by
  subst hfg
  exact F.mapComp f g

@[simp]
lemma mapComp_rfl : F.mapComp' f g _ rfl = F.mapComp f g := rfl

lemma mapComp'_def (hfg : f ≫ g = fg) : F.mapComp' f g fg hfg =
    eqToIso (by rw [hfg]) ≪≫ F.mapComp f g := by
  subst hfg
  simp

lemma mapComp_comp_mapComp {a b c d : B}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (F.mapComp (f ≫ g) h).hom ≫ (F.mapComp f g).hom ▷ F.map h =
      F.map₂ (α_ _ _ _).hom ≫ (F.mapComp f (g ≫ h)).hom ≫ F.map f ◁ (F.mapComp g h).hom ≫
      (α_ _ _ _).inv := by
  simp

set_option linter.unusedTactic false

section

variable {a b c d : B} [IsLocallyDiscrete B]
  (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  (fg : a ⟶ c) (gh : b ⟶ d) (fgh : a ⟶ d)
  (hfg : f ≫ g = fg) (hgh : g ≫ h = gh) (hfgh : f ≫ g ≫ h = fgh)

@[reassoc]
lemma map₂_mapComp_hom_eq_mapComp'_hom
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    F.map₂ (α_ f g h).hom ≫ (F.mapComp f (g ≫ h)).hom =
      (F.mapComp' f (g ≫ h) ((f ≫ g) ≫ h)).hom := by
  simp_rw [mapComp'_def]
  simp [Subsingleton.elim ((α_ f g h).hom) (eqToHom (by simp))]

@[reassoc]
lemma mapComp'_hom_comp_mapComp'_hom :
    (F.mapComp' fg h fgh).hom ≫ (F.mapComp' f g fg hfg).hom ▷ F.map h =
      (F.mapComp' f gh fgh).hom ≫ F.map f ◁ (F.mapComp' g h gh hgh).hom ≫
      (α_ _ _ _).inv := by
  subst hfg hgh
  obtain rfl : (f ≫ g) ≫ h = fgh := by aesop_cat
  simp_rw [mapComp_rfl, mapComp_comp_mapComp]
  simp [← map₂_mapComp_hom_eq_mapComp'_hom_assoc]

@[reassoc]
lemma mapComp'_hom_of_comp_eq :
    (F.mapComp' f gh fgh).hom =
      (F.mapComp' fg h fgh).hom ≫ (F.mapComp' f g fg hfg).hom ▷ F.map h ≫
        (α_ _ _ _).hom ≫ F.map f ◁ (F.mapComp' g h gh hgh).inv := by
  rw [F.mapComp'_hom_comp_mapComp'_hom_assoc f g h fg gh fgh hfg hgh hfgh]
  simp

@[reassoc]
lemma whiskerLeft_mapComp'_inv_comp_mapComp'_inv :
    F.map f ◁ (F.mapComp' g h gh hgh).inv ≫ (F.mapComp' f gh fgh).inv =
      (α_ _ _ _).inv ≫ (F.mapComp' f g fg hfg).inv ▷ F.map h ≫
      (F.mapComp' fg h fgh).inv := by
  simp [← cancel_epi (F.map f ◁ (F.mapComp' g h gh hgh).hom),
    ← cancel_epi (F.mapComp' f gh fgh).hom,
    ← mapComp'_hom_comp_mapComp'_hom_assoc _ f g h fg gh fgh hfg hgh hfgh]

@[reassoc]
lemma whiskerRight_mapComp'_inv_comp_mapComp'_inv :
    (F.mapComp' f g fg hfg).inv ▷ F.map h ≫ (F.mapComp' fg h fgh).inv =
    (α_ _ _ _).hom ≫ F.map f ◁ (F.mapComp' g h gh hgh).inv ≫ (F.mapComp' f gh fgh).inv
    := by
  sorry

@[reassoc]
lemma mapComp'_inv_of_comp_eq :
    (F.mapComp' f gh fgh).inv =
      F.map f ◁ (F.mapComp' g h gh hgh).hom ≫ (α_ _ _ _).inv ≫
      (F.mapComp' f g fg hfg).inv ▷ F.map h ≫
      (F.mapComp' fg h fgh).inv := by
  sorry


end

end

variable {C : Type u} [Bicategory.{w, v} C] [IsLocallyDiscrete C]
  (F : Pseudofunctor C Cat.{v', u'})
  {ι : Type w} (X : ι → C)

structure DescentData where
  obj (i : ι) : F.obj (X i)
  iso ⦃Y : C⦄ ⦃i₁ i₂ : ι⦄ (f₁ : X i₁ ⟶ Y) (f₂ : X i₂ ⟶ Y) :
      (F.map f₁).obj (obj i₁) ≅ (F.map f₂).obj (obj i₂)
  iso_comp ⦃Y' Y : C⦄ (g : Y ⟶ Y') ⦃i₁ i₂ : ι⦄ (f₁ : X i₁ ⟶ Y) (f₂ : X i₂ ⟶ Y) :
      iso (f₁ ≫ g) (f₂ ≫ g) =
        (F.mapComp f₁ g).app _ ≪≫
          Functor.mapIso (F.map g) (iso f₁ f₂) ≪≫
            (F.mapComp f₂ g).symm.app _ := by aesop_cat
  iso_trans ⦃Y : C⦄ ⦃i₁ i₂ i₃ : ι⦄ (f₁ : X i₁ ⟶ Y) (f₂ : X i₂ ⟶ Y) (f₃ : X i₃ ⟶ Y) :
    iso f₁ f₂ ≪≫ iso f₂ f₃ = iso f₁ f₃ := by aesop_cat

namespace DescentData

variable {F X}

def mk' (obj : ∀ i, F.obj (X i))
    (hom : ∀ ⦃Y : C⦄ ⦃i₁ i₂ : ι⦄ (f₁ : X i₁ ⟶ Y) (f₂ : X i₂ ⟶ Y),
      (F.map f₁).obj (obj i₁) ⟶ (F.map f₂).obj (obj i₂))
    (hom_comp : ∀ ⦃Y' Y : C⦄ (g : Y ⟶ Y') ⦃i₁ i₂ : ι⦄ (f₁ : X i₁ ⟶ Y) (f₂ : X i₂ ⟶ Y),
      hom (f₁ ≫ g) (f₂ ≫ g) =
        (F.mapComp f₁ g).hom.app _ ≫
          (F.map g).map (hom f₁ f₂) ≫
            (F.mapComp f₂ g).inv.app _ := by aesop_cat)
    (hom_self : ∀ ⦃Y : C⦄ ⦃i : ι⦄ (f : X i ⟶ Y), hom f f = 𝟙 _ := by aesop_cat)
    (comp_hom : ∀ ⦃Y : C⦄ ⦃i₁ i₂ i₃ : ι⦄ (f₁ : X i₁ ⟶ Y) (f₂ : X i₂ ⟶ Y) (f₃ : X i₃ ⟶ Y),
      hom f₁ f₂ ≫ hom f₂ f₃ = hom f₁ f₃ := by aesop_cat) : F.DescentData X where
  obj := obj
  iso Y i₁ i₂ f₁ f₂ :=
    { hom := hom f₁ f₂
      inv := hom f₂ f₁ }

section Unique

variable (X : C)

set_option maxHeartbeats 0 in
def mk'' (obj : F.obj X) (c : BinaryCofan X X)
    (hc : IsColimit c) (map : c.pt ⟶ X)
    (heq : map = hc.desc (BinaryCofan.mk (𝟙 _) (𝟙 _)))
    {Z : C} {ι₁₂ ι₂₃ : c.pt ⟶ Z}
    (h : IsPushout c.inl c.inr ι₂₃ ι₁₂)
    (p₁ p₂ p₃ : X ⟶ Z)
    (hp₁ : c.inl ≫ ι₁₂ = p₁)
    (hp₂ : c.inr ≫ ι₁₂ = p₂)
    (hp₃ : c.inr ≫ ι₂₃ = p₃)
    (hom : (F.map c.inl).obj obj ⟶ (F.map c.inr).obj obj)
    (hom_self : (F.map map).map hom =
      (F.mapComp' c.inl map (𝟙 _) (by aesop_cat)).inv.app obj ≫
      (F.mapComp' c.inr map (𝟙 _) (by aesop_cat)).hom.app obj) :
    F.DescentData (fun _ : PUnit ↦ X) := by
  refine mk' (fun _ ↦ obj) (fun Y _ _ f₁ f₂ ↦ ?_) ?_ ?_ ?_
  · let p : c.pt ⟶ Y := hc.desc <| BinaryCofan.mk f₁ f₂
    exact (F.mapComp' c.inl p f₁ (by aesop_cat)).hom.app obj ≫ (F.map p).map hom ≫
      (F.mapComp' c.inr p f₂ (by aesop_cat)).inv.app obj
  · intro Y Y' g _ _ f₁ f₂
    simp only [pair_obj_left, Functor.const_obj_obj, Cat.comp_obj,
      pair_obj_right, Functor.map_comp, assoc]
    simp_rw [← mapComp_rfl]
    have := F.mapComp'_hom_comp_mapComp'_hom
      c.inl (hc.desc (BinaryCofan.mk f₁ f₂)) g f₁
      (hc.desc (BinaryCofan.mk (f₁ ≫ g) (f₂ ≫ g)))
      (f₁ ≫ g) (by simp) (by apply BinaryCofan.IsColimit.hom_ext hc <;> simp) (by simp)
    have := congr($(this).app obj)
    dsimp
    dsimp at this
    rw [← mapComp_rfl]
    erw [reassoc_of% this]
    congr 1
    rw [← mapComp_rfl]
    have := F.whiskerRight_mapComp'_inv_comp_mapComp'_inv
      c.inr (hc.desc (BinaryCofan.mk f₁ f₂)) g f₂
      (hc.desc (BinaryCofan.mk (f₁ ≫ g) (f₂ ≫ g)))
      (f₂ ≫ g) (by simp) (by apply BinaryCofan.IsColimit.hom_ext hc <;> simp) (by simp)
    have := congr($(this).app obj)
    dsimp at this
    erw [this]
    simp only [← Category.assoc]
    congr 1
    simp only [Category.assoc]
    have := NatIso.naturality_2 (F.mapComp' (hc.desc (BinaryCofan.mk f₁ f₂)) g
      (hc.desc (BinaryCofan.mk (f₁ ≫ g) (f₂ ≫ g)))
      (by apply BinaryCofan.IsColimit.hom_ext hc <;> simp)) hom
    dsimp at this
    rw [← this]
    congr 1
    simp_rw [← Category.assoc]
    congr 1
    simp [Cat.associator_hom_app, Cat.associator_inv_app]
  · intro Y _ f
    dsimp
    have hfac : hc.desc (BinaryCofan.mk f f) = map ≫ f := by
      rw [heq]
      apply BinaryCofan.IsColimit.hom_ext hc <;> simp
    have homself' := (F.map f).congr_map hom_self
    dsimp at homself'
    have := F.mapComp'_hom_of_comp_eq c.inl map f (𝟙 X)
      (hc.desc (BinaryCofan.mk f f)) f (by aesop_cat) (by aesop_cat) (by aesop_cat)
    have h1 := congr($(this).app obj)
    clear this
    dsimp at h1
    have := F.mapComp'_inv_of_comp_eq c.inr map f (𝟙 X)
      (hc.desc (BinaryCofan.mk f f)) f (by aesop_cat) (by aesop_cat) (by aesop_cat)
    have h2 := congr($(this).app obj)
    clear this
    dsimp at h2
    rw [h1, h2]
    simp only [NatTrans.naturality_assoc, Cat.comp_obj, Cat.comp_map, assoc,
      Iso.inv_hom_id_app_assoc]
    rw [homself']
    simp only [Cat.associator_hom_app, Cat.comp_obj, eqToHom_refl, Functor.map_comp,
      Cat.associator_inv_app, id_comp, assoc]
    simp_rw [← Functor.map_comp_assoc]
    simp
  · intro Y _ _ _ f₁ f₂ f₃
    dsimp
    sorry

end Unique

@[ext]
structure Hom (D₁ D₂ : F.DescentData X) where
  hom (i : ι) : D₁.obj i ⟶ D₂.obj i
  comm ⦃Y : C⦄ ⦃i₁ i₂ : ι⦄ (f₁ : X i₁ ⟶ Y) (f₂ : X i₂ ⟶ Y) :
    (F.map f₁).map (hom i₁) ≫ (D₂.iso f₁ f₂).hom =
      (D₁.iso f₁ f₂).hom ≫ (F.map f₂).map (hom i₂) := by aesop_cat

attribute [reassoc (attr := simp)] Hom.comm

instance : Category (F.DescentData X) where
  Hom := Hom
  id D := { hom i := 𝟙 _ }
  comp {D₁ D₂ D₃} φ ψ :=
    { hom i := φ.hom i ≫ ψ.hom i
      comm Y i₁ i₂ f₁ f₂ := by
        simp only [Functor.map_comp, assoc]
        rw [ψ.comm, φ.comm_assoc] }

end DescentData

def toDescentDataOfIsTerminal (X₀ : C) (hX₀ : IsInitial X₀) :
    F.obj X₀ ⥤ F.DescentData X where
  obj A :=
    { obj i := (F.map (hX₀.to (X i))).obj A
      iso Y i₁ i₂ f₁ f₂ :=
        (F.mapComp' (hX₀.to (X i₁)) f₁ (hX₀.to Y) (by simp)).symm.app A ≪≫
          (F.mapComp' (hX₀.to (X i₂)) f₂ (hX₀.to Y) (by simp)).app A
      iso_comp Y' Y g i₁ i₂ f₁ f₂ := by
        sorry }
  map {A B} f :=
    { hom i := (F.map _).map f
      comm Y i₁ i₂ f₁ f₂ := by
        dsimp
        sorry }

end Pseudofunctor

end CategoryTheory
