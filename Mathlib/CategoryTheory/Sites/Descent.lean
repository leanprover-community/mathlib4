import Mathlib.CategoryTheory.Sites.ObjectsCoverTop
import Mathlib.CategoryTheory.Sites.Over

universe v' v u' u

namespace CategoryTheory

open Category

namespace GrothendieckTopology

namespace ObjectsCoverTop

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {I : Type*} {Y : I → C}

structure SheafDescentData (hY : J.ObjectsCoverTop Y)
    (A : Type u') [Category.{v'} A] where
  sheaf (i : I) : Sheaf (J.over (Y i)) A
  iso ⦃X : C⦄ ⦃i₁ i₂ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) :
    (J.overMapPullback A f₁).obj (sheaf i₁) ≅
      (J.overMapPullback A f₂).obj (sheaf i₂)
  pullback_iso ⦃X X' : C⦄ (g : X' ⟶ X) ⦃i₁ i₂ : I⦄
      (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) :
      iso (g ≫ f₁) (g ≫ f₂) = (J.overMapPullbackComp A g f₁).symm.app _ ≪≫
        (J.overMapPullback A g).mapIso (iso f₁ f₂) ≪≫ (J.overMapPullbackComp A g f₂).app _ := by aesop_cat
  iso_trans ⦃X : C⦄ ⦃i₁ i₂ i₃ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) (f₃ : X ⟶ Y i₃) :
    iso f₁ f₂ ≪≫ iso f₂ f₃ = iso f₁ f₃ := by aesop_cat

namespace SheafDescentData

variable {hY : J.ObjectsCoverTop Y} {A : Type u'} [Category.{v'} A]
    (D D₁ D₂ D₃ : hY.SheafDescentData A)

attribute [simp] iso_trans

@[reassoc (attr := simp)]
lemma iso_trans_hom ⦃X : C⦄ ⦃i₁ i₂ i₃ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) (f₃ : X ⟶ Y i₃) :
    (D.iso f₁ f₂).hom ≫ (D.iso f₂ f₃).hom = (D.iso f₁ f₃).hom := by
  rw [← Iso.trans_hom, D.iso_trans]

@[reassoc (attr := simp)]
lemma iso_trans_inv ⦃X : C⦄ ⦃i₁ i₂ i₃ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) (f₃ : X ⟶ Y i₃) :
    (D.iso f₂ f₃).inv ≫ (D.iso f₁ f₂).inv = (D.iso f₁ f₃).inv := by
  rw [← Iso.trans_inv, D.iso_trans]

lemma iso_refl_hom ⦃X : C⦄ ⦃i : I⦄ (f : X ⟶ Y i) :
    (D.iso f f).hom = 𝟙 _ := by
  rw [← cancel_mono (D.iso f f).hom, iso_trans_hom, id_comp]

@[simp 1000]
lemma iso_refl ⦃X : C⦄ ⦃i : I⦄ (f : X ⟶ Y i) :
    D.iso f f = Iso.refl _ := by
  ext1
  rw [iso_refl_hom, Iso.refl_hom]

lemma iso_refl_inv ⦃X : C⦄ ⦃i : I⦄ (f : X ⟶ Y i) :
    (D.iso f f).inv = 𝟙 _ := by simp

lemma iso_inv ⦃X : C⦄ ⦃i₁ i₂ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) :
    (D.iso f₁ f₂).inv = (D.iso f₂ f₁).hom := by
  rw [← cancel_mono (D.iso f₁ f₂).hom, Iso.inv_hom_id, iso_trans_hom, iso_refl, Iso.refl_hom]

lemma iso_symm ⦃X : C⦄ ⦃i₁ i₂ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) :
    (D.iso f₁ f₂).symm = D.iso f₂ f₁ := by
  ext1
  rw [Iso.symm_hom, iso_inv]

@[ext]
structure Hom where
  hom (i : I) : D₁.sheaf i ⟶ D₂.sheaf i
  comm ⦃X : C⦄ ⦃i₁ i₂ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) :
    (J.overMapPullback A f₁).map (hom i₁) ≫ (D₂.iso f₁ f₂).hom =
    (D₁.iso f₁ f₂).hom ≫ (J.overMapPullback A f₂).map (hom i₂) := by aesop_cat

namespace Hom

attribute [reassoc (attr := simp)] comm

@[simps]
def id : Hom D D where
  hom _ := 𝟙 _

variable {D₁ D₂ D₃}

@[simps]
def comp (α : Hom D₁ D₂) (β : Hom D₂ D₃): Hom D₁ D₃ where
  hom i := α.hom i ≫ β.hom i

instance : Category (hY.SheafDescentData A) where
  Hom := Hom
  id := id
  comp := comp

lemma congr_hom {f g : D₁ ⟶ D₂} (h : f = g) (i : I) : f.hom i = g.hom i := by
  subst h
  rfl

end Hom

lemma hom_ext {D₁ D₂ : hY.SheafDescentData A} {f g : D₁ ⟶ D₂}
    (h : ∀ i, f.hom i = g.hom i) : f = g :=
  Hom.ext _ _ (funext h)

end SheafDescentData

variable {hY : J.ObjectsCoverTop Y} (A : Type u') [Category.{v'} A]

@[simps]
def sheafToDescentData : Sheaf J A ⥤ hY.SheafDescentData A where
  obj F :=
    { sheaf := fun i => (J.overPullback A (Y i)).obj F
      iso := fun _ _ _ _ _ => Iso.refl _
      pullback_iso := sorry }
  map {F G} φ :=
    { hom := fun i => (J.overPullback A (Y i)).map φ }

instance : Faithful (hY.sheafToDescentData A) where
  map_injective {F G} φ ψ h := by
    have := SheafDescentData.Hom.congr_hom h
    sorry

end ObjectsCoverTop

end GrothendieckTopology

end CategoryTheory
