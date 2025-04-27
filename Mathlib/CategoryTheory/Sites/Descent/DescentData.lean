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
# Descent data

-/

universe t w v v' u u'

namespace CategoryTheory

open Category Limits Bicategory

namespace Pseudofunctor

variable {C : Type u} [Bicategory.{w, v} C]
  (F : Pseudofunctor C Cat.{v', u'}) {ι : Type t} (X : ι → C)

structure DescentData where
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

namespace DescentData

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
      hom f₁ f₂ ≫ hom f₂ f₃ = hom f₁ f₃ := by aesop_cat) : F.DescentData X where
  obj := obj
  iso Y i₁ i₂ f₁ f₂ :=
    { hom := hom f₁ f₂
      inv := hom f₂ f₁ }
  iso_comp' Y' Y g i₁ i₂ f₁ f₂ f₁g f₂g hf₁g hf₂g := by
    ext
    exact hom_comp' g f₁ f₂ f₁g f₂g hf₁g hf₂g

section

variable (D : F.DescentData X)

@[simp]
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

@[ext]
lemma hom_ext {D₁ D₂ : F.DescentData X} {f g : D₁ ⟶ D₂}
    (h : ∀ i, f.hom i = g.hom i) : f = g :=
  Hom.ext (funext h)

@[simp]
lemma id_hom (D : F.DescentData X) (i : ι) : Hom.hom (𝟙 D) i = 𝟙 _ := rfl

@[simp, reassoc]
lemma comp_hom {D₁ D₂ D₃ : F.DescentData X} (f : D₁ ⟶ D₂) (g : D₂ ⟶ D₃) (i : ι) :
    (f ≫ g).hom i = f.hom i ≫ g.hom i := rfl


namespace Hom

variable {D₁ D₂ : F.DescentData X} (f : D₁ ⟶ D₂)

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

end DescentData

variable [Strict C]

def toDescentDataOfIsInitial (X₀ : C) (hX₀ : IsInitial X₀) :
    F.obj X₀ ⥤ F.DescentData X where
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

namespace DescentData

section Unique

variable {X : C} (obj : F.obj X) (c : BinaryCofan X X)
    (hc : IsColimit c) (map : c.pt ⟶ X)
    (heq : map = hc.desc (BinaryCofan.mk (𝟙 _) (𝟙 _)))
    {Z : C} {ι₁₂ ι₂₃ : c.pt ⟶ Z}
    (h : IsPushout c.inl c.inr ι₂₃ ι₁₂)
    (p₁ p₂ p₃ : X ⟶ Z)
    (hp₁ : c.inl ≫ ι₁₂ = p₁) (hp₂ : c.inr ≫ ι₁₂ = p₂) (hp₃ : c.inr ≫ ι₂₃ = p₃)
    (hom : (F.map c.inl).obj obj ⟶ (F.map c.inr).obj obj)
    (hom_self : (F.map map).map hom =
      (F.mapComp' c.inl map (𝟙 X)).inv.app obj ≫
      (F.mapComp' c.inr map (𝟙 X)).hom.app obj)

def mk''Hom {Y : C} (f₁ f₂ : X ⟶ Y) :
    (F.map f₁).obj obj ⟶ (F.map f₂).obj obj :=
  (F.mapComp' c.inl _ f₁ (by simp)).hom.app obj ≫
    (F.map (hc.desc (BinaryCofan.mk f₁ f₂))).map hom ≫
      (F.mapComp' c.inr _ f₂ (by simp)).inv.app obj

lemma mk''Hom_eq {Y : C} (f₁ f₂ : X ⟶ Y) (p : c.pt ⟶ Y) (hp₁ : c.inl ≫ p = f₁)
    (hp₂ : c.inr ≫ p = f₂) :
    mk''Hom F obj c hc hom f₁ f₂ =
      (F.mapComp' c.inl p f₁ hp₁).hom.app obj ≫ (F.map p).map hom ≫
        (F.mapComp' c.inr p f₂ hp₂).inv.app obj := by
  obtain rfl : p = (hc.desc <| BinaryCofan.mk f₁ f₂) := by
    apply BinaryCofan.IsColimit.hom_ext hc <;> simp [hp₁, hp₂]
  rfl

@[simp]
lemma mk''Hom_inl_inr :
    mk''Hom F obj c hc hom c.inl c.inr = hom := by
  simp [mk''Hom_eq F obj c hc hom c.inl c.inr (𝟙 _) (by simp) (by simp),
    mapComp'_comp_id_hom_app, mapComp'_comp_id_inv_app]

lemma mk''Hom_comp' {Y' Y : C} (g : Y ⟶ Y') (f₁ f₂ : X ⟶ Y)
      (f₁g : X ⟶ Y') (f₂g : X ⟶ Y') (hf₁g : f₁ ≫ g = f₁g) (hf₂g : f₂ ≫ g = f₂g) :
    mk''Hom F obj c hc hom f₁g f₂g =
      (F.mapComp' f₁ g f₁g hf₁g).hom.app obj ≫
        (F.map g).map (mk''Hom F obj c hc hom f₁ f₂) ≫
          (F.mapComp' f₂ g f₂g hf₂g).inv.app obj := by
  let p : c.pt ⟶ Y := hc.desc (BinaryCofan.mk f₁ f₂)
  dsimp
  rw [mk''Hom_eq _ _ _ _ _ _ _ p (by simp [p]) (by simp [p]),
    mk''Hom_eq _ _ _ _ _ _ _ (p ≫ g) (by aesop_cat) (by aesop_cat)]
  dsimp
  simp only [Functor.map_comp, assoc]
  rw [← F.mapComp'_hom_app_comp_mapComp'_hom_app_map_obj_assoc
    _ _ _ _ (p ≫ g) _ (by aesop_cat) (by aesop_cat) (by aesop_cat),
    F.map_map_mapComp'_inv_app_comp_mapComp'_inv_app
    _ _ _ _ (p ≫ g) _ (by aesop_cat) (by aesop_cat) (by aesop_cat),
    ← F.mapComp'_hom_naturality_assoc, Iso.hom_inv_id_app_assoc]

include hom_self in
lemma mk''Hom_self {Y : C} (f : X ⟶ Y) :
    mk''Hom F obj c hc hom f f = 𝟙 _ := by
  rw [mk''Hom_comp' F obj c hc hom (map ≫ f) c.inl c.inr f f
      (by aesop_cat) (by aesop_cat), mk''Hom_inl_inr,
    ← F.mapComp'_naturality_2_assoc map f (map ≫ f) rfl hom,
    hom_self, Functor.map_comp_assoc,
    F.mapComp'_inv_app_map_obj_comp_mapComp'_inv_app _ _ _
      (𝟙 X) _ _ (by aesop_cat) (by aesop_cat) (by aesop_cat),
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, assoc,
    Iso.hom_inv_id_app, comp_id,
    F.mapComp'_hom_app_comp_mapComp'_hom_app_map_obj_assoc
      _ _ _ (𝟙 X) _ _ (by aesop_cat) (by aesop_cat) (by aesop_cat),
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Functor.map_id]
  simp only [id_comp, Iso.hom_inv_id_app]

/-- Constructor for `Pseudofunctor.DescentData` for a family consisting
of only one object `X` equipped with a chosen binary and ternary coproduct. -/
def mk''
    (hom_comp : mk''Hom F obj c hc hom p₁ p₂ ≫ mk''Hom F obj c hc hom p₂ p₃ =
      mk''Hom F obj c hc hom p₁ p₃) : F.DescentData (fun _ : PUnit.{t + 1} ↦ X) :=
  mk' (fun _ ↦ obj) (fun _ _ _ ↦ mk''Hom F obj c hc hom)
    (fun _ _ _ _ _ ↦ mk''Hom_comp' _ _ _ _ _ _) (by
      rintro Y ⟨⟩ f
      exact mk''Hom_self F obj c hc map heq hom hom_self f) (by
      rintro Y ⟨⟩ ⟨⟩ ⟨⟩ f₁ f₂ f₃
      obtain ⟨φ, hφ₁, hφ₂, hφ₃⟩ :
          ∃ (φ : Z ⟶ Y), c.inl ≫ ι₁₂ ≫ φ = f₁ ∧
            c.inr ≫ ι₁₂ ≫ φ = f₂ ∧ c.inr ≫ ι₂₃ ≫ φ = f₃ :=
        ⟨h.desc (hc.desc (BinaryCofan.mk f₂ f₃))
          (hc.desc (BinaryCofan.mk f₁ f₂)) (by simp), by simp, by simp, by simp⟩
      simp only [mk''Hom_comp' F obj c hc hom φ p₁ p₂ f₁ f₂ (by aesop_cat) (by aesop_cat),
        mk''Hom_comp' F obj c hc hom φ p₂ p₃ f₂ f₃ (by aesop_cat) (by aesop_cat),
        mk''Hom_comp' F obj c hc hom φ p₁ p₃ f₁ f₃ (by aesop_cat) (by aesop_cat),
        assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, hom_comp])

end Unique

end DescentData

end Pseudofunctor

end CategoryTheory
