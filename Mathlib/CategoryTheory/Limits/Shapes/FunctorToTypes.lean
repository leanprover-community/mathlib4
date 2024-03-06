/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Limits.Types

/-!
# Binary (co)products of type-valued functors.

Defines an explicit construction of binary products and coproducts of type-valued functors.

Also defines isomorphisms to the categorical product and coproduct, respectively.

-/


open CategoryTheory.Limits

universe w v u

namespace CategoryTheory.FunctorToTypes

variable {C : Type u} [Category.{v} C]

section prod

/-- `prod F G` is the explicit binary product of type-valued functors `F` and `G`. -/
def prod (F G : C ⥤ Type w) : C ⥤ Type w where
  obj a := F.obj a × G.obj a
  map f a := (F.map f a.1, G.map f a.2)

  /-- The first projection of `prod F G`, onto `F`. -/
@[simps]
def prod.fst {F G : C ⥤ Type w} : (prod F G) ⟶ F where
  app _ a := a.1

/-- The second projection of `prod F G`, onto `G`. -/
@[simps]
def prod.snd {F G : C ⥤ Type w} : (prod F G) ⟶ G where
  app _ a := a.2

/-- Given natural transformations `F ⟶ F₁` and `F ⟶ F₂`, construct
a natural transformation `F ⟶ prod F₁ F₂`. -/
def natTransProd {F F₁ F₂ : C ⥤ Type w} (τ₁ : F ⟶ F₁) (τ₂ : F ⟶ F₂) :
    F ⟶ prod F₁ F₂ where
  app x y := ⟨τ₁.app x y, τ₂.app x y⟩
  naturality _ _ _ := by
    ext a
    simp only [types_comp_apply, FunctorToTypes.naturality]
    aesop

/-- The binary fan whose point is `prod F G`. -/
@[simps!]
def binaryProductCone (F G : C ⥤ Type w) : BinaryFan F G :=
  BinaryFan.mk (prod.fst) (prod.snd)

/-- `prod F G` is a limit cone. -/
@[simps]
def binaryProductLimit (F G : C ⥤ Type w) : IsLimit (binaryProductCone F G) where
  lift (s : BinaryFan F G) := natTransProd s.fst s.snd
  fac _ := fun ⟨j⟩ ↦ WalkingPair.casesOn j rfl rfl
  uniq _ _ h := by
    simp only [← h ⟨WalkingPair.right⟩, ← h ⟨WalkingPair.left⟩]
    congr

/-- `prod F G` is a binary product for `F` and `G`. -/
def binaryProductLimitCone (F G : C ⥤ Type w) : Limits.LimitCone (pair F G) :=
  ⟨_, binaryProductLimit F G⟩

/-- The categorical binary product of type-valued functors is `prod F G`. -/
noncomputable def binaryProductIso (F G : C ⥤ Type w) : F ⨯ G ≅ prod F G :=
  limit.isoLimitCone (binaryProductLimitCone F G)

@[simp]
lemma binaryProductIso_hom_comp_fst (F G : C ⥤ Type w) :
    (binaryProductIso F G).hom ≫ prod.fst = Limits.prod.fst := by aesop

@[simp]
lemma binaryProductIso_hom_comp_snd (F G : C ⥤ Type w) :
    (binaryProductIso F G).hom ≫ prod.snd = Limits.prod.snd := by aesop

@[simp]
lemma binaryProductIso_inv_comp_fst (F G : C ⥤ Type w) :
    (binaryProductIso F G).inv ≫ Limits.prod.fst = prod.fst := by
  simp [binaryProductIso, binaryProductLimitCone]

@[simp]
lemma binaryProductIso_inv_comp_fst_apply (F G : C ⥤ Type w) (a : C)
    (z : (prod F G).obj a) :
    (Limits.prod.fst (X := F)).app a ((binaryProductIso F G).inv.app a z) = z.1 :=
  congr_fun (congr_app (binaryProductIso_inv_comp_fst F G) a) z

@[simp]
lemma binaryProductIso_inv_comp_snd (F G : C ⥤ Type w) :
    (binaryProductIso F G).inv ≫ Limits.prod.snd = prod.snd := by
    simp [binaryProductIso, binaryProductLimitCone]

@[simp]
lemma binaryProductIso_inv_comp_snd_apply (F G : C ⥤ Type w) (a : C)
    (z : (prod F G).obj a) :
    (Limits.prod.snd (X := F)).app a ((binaryProductIso F G).inv.app a z) = z.2 :=
  congr_fun (congr_app (binaryProductIso_inv_comp_snd F G) a) z

/-- Construct an element of `(F ⨯ G).obj a` from an element of `F.obj a` and
an element of `G.obj a`. -/
noncomputable
def prodMk {F G : C ⥤ Type w} {a : C} (x : F.obj a) (y : G.obj a) :
    (F ⨯ G).obj a := ((binaryProductIso F G).inv).app a ⟨x, y⟩

@[simp]
lemma prodMk_fst {F G : C ⥤ Type w} {a : C} (x : F.obj a) (y : G.obj a) :
    (Limits.prod.fst (X := F) (Y := G)).app a (prodMk x y) = x := by
  simp only [prodMk, binaryProductIso_inv_comp_fst_apply]

@[simp]
lemma prodMk_snd {F G : C ⥤ Type w} {a : C} (x : F.obj a) (y : G.obj a) :
    (Limits.prod.snd (X := F) (Y := G)).app a (prodMk x y) = y := by
  simp only [prodMk, binaryProductIso_inv_comp_snd_apply]

@[ext]
lemma prod_ext {F G : C ⥤ Type w} {a : C} (z w : (prod F G).obj a)
    (h1 : z.1 = w.1) (h2 : z.2 = w.2) : z = w := Prod.ext h1 h2

/-- `(F ⨯ G).obj a` is in bijection with the product of `F.obj a` and `G.obj a`. -/
@[simps]
noncomputable
def binaryProductEquiv (F G : C ⥤ Type w) (a : C) :
    (F ⨯ G).obj a ≃ (F.obj a) × (G.obj a) where
  toFun z := ⟨(((binaryProductIso F G).hom).app a z).1, (((binaryProductIso F G).hom).app a z).2⟩
  invFun z := prodMk z.1 z.2
  left_inv _ := by simp [prodMk]
  right_inv _ := by simp [prodMk]

@[ext]
lemma prod_ext' (F G : C ⥤ Type w) (n : C) (z w : (F ⨯ G).obj n)
    (h1 : (Limits.prod.fst (X := F)).app n z = (Limits.prod.fst (X := F)).app n w)
    (h2 : (Limits.prod.snd (X := F)).app n z = (Limits.prod.snd (X := F)).app n w) :
    z = w := by
  apply Equiv.injective (binaryProductEquiv F G n)
  aesop

end prod

section coprod

/-- `coprod F G` is the explicit binary coproduct of type-valued functors `F` and `G`. -/
def coprod (F G : C ⥤ Type w) : C ⥤ Type w where
  obj a := F.obj a ⊕ G.obj a
  map f x := by
    cases x with
    | inl x => exact .inl (F.map f x)
    | inr x => exact .inr (G.map f x)

/-- The left inclusion of `F` into `coprod F G`. -/
@[simps]
def coprod.inl {F G : C ⥤ Type w} : F ⟶ (coprod F G) where
  app _ x := .inl x

  /-- The right inclusion of `G` into `coprod F G`. -/
@[simps]
def coprod.inr {F G : C ⥤ Type w} : G ⟶ (coprod F G) where
  app _ x := .inr x

/-- Given natural transformations `F₁ ⟶ F` and `F₂ ⟶ F`, construct
a natural transformation `coprod F₁ F₂ ⟶ F`. -/
def natTransSum {F F₁ F₂ : C ⥤ Type w} (τ₁ : F₁ ⟶ F) (τ₂ : F₂ ⟶ F) :
    coprod F₁ F₂ ⟶ F where
  app a x := by
     cases x with
     | inl x => exact τ₁.app a x
     | inr x => exact τ₂.app a x
  naturality _ _ _:= by
    ext x
    cases x with | _ => simp only [coprod, types_comp_apply, FunctorToTypes.naturality]

/-- The binary cofan whose point is `coprod F G`. -/
@[simps!]
def binaryCoproductCocone (F G : C ⥤ Type w) : BinaryCofan F G :=
  BinaryCofan.mk (coprod.inl) (coprod.inr)

/-- `coprod F G` is a colimit cocone. -/
@[simps]
def binaryCoproductColimit (F G : C ⥤ Type w) : IsColimit (binaryCoproductCocone F G) where
  desc (s : BinaryCofan F G) := natTransSum s.inl s.inr
  fac _ := fun ⟨j⟩ ↦ WalkingPair.casesOn j rfl rfl
  uniq _ _ h := by
    ext _ x
    cases x with | _ => simp [← h ⟨WalkingPair.right⟩, ← h ⟨WalkingPair.left⟩]; congr

/-- `coprod F G` is a binary coproduct for `F` and `G`. -/
def binaryCoproductColimitCocone (F G : C ⥤ Type w) : Limits.ColimitCocone (pair F G) :=
  ⟨_, binaryCoproductColimit F G⟩

/-- The categorical binary coproduct of type-valued functors is `coprod F G`. -/
noncomputable def binaryCoproductIso (F G : C ⥤ Type w) : F ⨿ G ≅ coprod F G :=
  colimit.isoColimitCocone (binaryCoproductColimitCocone F G)

@[simp]
lemma binaryCoproductIso_inl_comp_hom (F G : C ⥤ Type w) :
    Limits.coprod.inl ≫ (binaryCoproductIso F G).hom = coprod.inl := by
  simp [binaryCoproductIso]
  aesop

@[simp]
lemma binaryCoproductIso_inl_comp_hom_apply (F G : C ⥤ Type w) (a : C) (x : F.obj a) :
    (binaryCoproductIso F G).hom.app a ((Limits.coprod.inl (X := F)).app a x) = .inl x :=
  congr_fun (congr_app (binaryCoproductIso_inl_comp_hom F G) a) x

@[simp]
lemma binaryCoproductIso_inr_comp_hom (F G : C ⥤ Type w) :
    Limits.coprod.inr ≫ (binaryCoproductIso F G).hom = coprod.inr := by
  simp [binaryCoproductIso]
  aesop

@[simp]
lemma binaryCoproductIso_inr_comp_hom_apply (F G : C ⥤ Type w) (a : C) (x : G.obj a) :
    (binaryCoproductIso F G).hom.app a ((Limits.coprod.inr (X := F)).app a x) = .inr x :=
  congr_fun (congr_app (binaryCoproductIso_inr_comp_hom F G) a) x

@[simp]
lemma binaryCoproductIso_inl_comp_inv (F G : C ⥤ Type w) :
    coprod.inl ≫ (binaryCoproductIso F G).inv = (Limits.coprod.inl (X := F)) := by
  aesop

@[simp]
lemma binaryCoproductIso_inl_comp_inv_apply (F G : C ⥤ Type w) (a : C) (x : F.obj a) :
    (binaryCoproductIso F G).inv.app a (coprod.inl.app a x) =
    (Limits.coprod.inl (X := F)).app a x := by
  aesop

@[simp]
lemma binaryCoproductIso_inr_comp_inv (F G : C ⥤ Type w) :
    coprod.inr ≫ (binaryCoproductIso F G).inv = (Limits.coprod.inr (X := F)) := by
  aesop

@[simp]
lemma binaryCoproductIso_inr_comp_inv_apply (F G : C ⥤ Type w) (a : C) (x : G.obj a) :
    (binaryCoproductIso F G).inv.app a (coprod.inr.app a x) =
    (Limits.coprod.inr (X := F)).app a x := by
  aesop

/-- `(F ⨿ G).obj a` is in bijection with disjoint union of `F.obj a` and `G.obj a`. -/
@[simps]
noncomputable
def binaryCoproductEquiv (F G : C ⥤ Type w) (a : C) :
    (F ⨿ G).obj a ≃ (F.obj a) ⊕ (G.obj a) where
  toFun z := ((binaryCoproductIso F G).hom.app a z)
  invFun z := ((binaryCoproductIso F G).inv.app a z)
  left_inv _ := by simp only [hom_inv_id_app_apply]
  right_inv _ := by simp only [inv_hom_id_app_apply]

end coprod
