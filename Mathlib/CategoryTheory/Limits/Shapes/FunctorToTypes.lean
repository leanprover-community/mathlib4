/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen, Robert Maxton
-/
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# (Co)products of type-valued functors

Defines an explicit construction of products and coproducts of type-valued functors.

Also defines isomorphisms to the categorical product and coproduct, respectively.
-/


open CategoryTheory.Limits

universe w v u i

namespace CategoryTheory.FunctorToTypes

variable {C : Type u} [Category.{v} C]
variable (F G : C ⥤ Type w)

section prod

/-- `prod F G` is the explicit binary product of type-valued functors `F` and `G`. -/
def prod : C ⥤ Type w where
  obj a := F.obj a × G.obj a
  map f a := (F.map f a.1, G.map f a.2)

variable {F G}

/-- The first projection of `prod F G`, onto `F`. -/
@[simps]
def prod.fst : prod F G ⟶ F where
  app _ a := a.1

/-- The second projection of `prod F G`, onto `G`. -/
@[simps]
def prod.snd : prod F G ⟶ G where
  app _ a := a.2

/-- Given natural transformations `F ⟶ F₁` and `F ⟶ F₂`, construct
a natural transformation `F ⟶ prod F₁ F₂`. -/
@[simps]
def prod.lift {F₁ F₂ : C ⥤ Type w} (τ₁ : F ⟶ F₁) (τ₂ : F ⟶ F₂) :
    F ⟶ prod F₁ F₂ where
  app x y := ⟨τ₁.app x y, τ₂.app x y⟩
  naturality _ _ _ := by
    ext a
    simp only [types_comp_apply, FunctorToTypes.naturality]
    aesop

@[simp]
lemma prod.lift_fst {F₁ F₂ : C ⥤ Type w} (τ₁ : F ⟶ F₁) (τ₂ : F ⟶ F₂) :
    prod.lift τ₁ τ₂ ≫ prod.fst = τ₁ := rfl

@[simp]
lemma prod.lift_snd {F₁ F₂ : C ⥤ Type w} (τ₁ : F ⟶ F₁) (τ₂ : F ⟶ F₂) :
    prod.lift τ₁ τ₂ ≫ prod.snd = τ₂ := rfl

variable (F G)

/-- The binary fan whose point is `prod F G`. -/
@[simps!]
def binaryProductCone : BinaryFan F G :=
  BinaryFan.mk prod.fst prod.snd

/-- `prod F G` is a limit cone. -/
@[simps]
def binaryProductLimit : IsLimit (binaryProductCone F G) where
  lift (s : BinaryFan F G) := prod.lift s.fst s.snd
  fac _ := fun ⟨j⟩ ↦ WalkingPair.casesOn j rfl rfl
  uniq _ _ h := by
    simp only [← h ⟨WalkingPair.right⟩, ← h ⟨WalkingPair.left⟩]
    congr

/-- `prod F G` is a binary product for `F` and `G`. -/
def binaryProductLimitCone : Limits.LimitCone (pair F G) :=
  ⟨_, binaryProductLimit F G⟩

/-- The categorical binary product of type-valued functors is `prod F G`. -/
noncomputable def binaryProductIso : F ⨯ G ≅ prod F G :=
  limit.isoLimitCone (binaryProductLimitCone F G)

@[simp]
lemma binaryProductIso_hom_comp_fst :
    (binaryProductIso F G).hom ≫ prod.fst = Limits.prod.fst := rfl

@[simp]
lemma binaryProductIso_hom_comp_snd :
    (binaryProductIso F G).hom ≫ prod.snd = Limits.prod.snd := rfl

@[simp]
lemma binaryProductIso_inv_comp_fst :
    (binaryProductIso F G).inv ≫ Limits.prod.fst = prod.fst := by
  simp [binaryProductIso, binaryProductLimitCone]

@[simp]
lemma binaryProductIso_inv_comp_fst_apply (a : C) (z : (prod F G).obj a) :
    (Limits.prod.fst (X := F)).app a ((binaryProductIso F G).inv.app a z) = z.1 :=
  congr_fun (congr_app (binaryProductIso_inv_comp_fst F G) a) z

@[simp]
lemma binaryProductIso_inv_comp_snd :
    (binaryProductIso F G).inv ≫ Limits.prod.snd = prod.snd := by
  simp [binaryProductIso, binaryProductLimitCone]

@[simp]
lemma binaryProductIso_inv_comp_snd_apply (a : C) (z : (prod F G).obj a) :
    (Limits.prod.snd (X := F)).app a ((binaryProductIso F G).inv.app a z) = z.2 :=
  congr_fun (congr_app (binaryProductIso_inv_comp_snd F G) a) z

variable {F G}

/-- Construct an element of `(F ⨯ G).obj a` from an element of `F.obj a` and
an element of `G.obj a`. -/
noncomputable
def prodMk {a : C} (x : F.obj a) (y : G.obj a) : (F ⨯ G).obj a :=
  ((binaryProductIso F G).inv).app a ⟨x, y⟩

@[simp]
lemma prodMk_fst {a : C} (x : F.obj a) (y : G.obj a) :
    (Limits.prod.fst (X := F)).app a (prodMk x y) = x := by
  simp only [prodMk, binaryProductIso_inv_comp_fst_apply]

@[simp]
lemma prodMk_snd {a : C} (x : F.obj a) (y : G.obj a) :
    (Limits.prod.snd (X := F)).app a (prodMk x y) = y := by
  simp only [prodMk, binaryProductIso_inv_comp_snd_apply]

@[ext]
lemma prod_ext {a : C} (z w : (prod F G).obj a) (h1 : z.1 = w.1) (h2 : z.2 = w.2) :
    z = w := Prod.ext h1 h2

variable (F G)

/-- `(F ⨯ G).obj a` is in bijection with the product of `F.obj a` and `G.obj a`. -/
@[simps]
noncomputable
def binaryProductEquiv (a : C) : (F ⨯ G).obj a ≃ (F.obj a) × (G.obj a) where
  toFun z := ⟨((binaryProductIso F G).hom.app a z).1, ((binaryProductIso F G).hom.app a z).2⟩
  invFun z := prodMk z.1 z.2
  left_inv _ := by simp [prodMk]
  right_inv _ := by simp [prodMk]

@[ext]
lemma prod_ext' (a : C) (z w : (F ⨯ G).obj a)
    (h1 : (Limits.prod.fst (X := F)).app a z = (Limits.prod.fst (X := F)).app a w)
    (h2 : (Limits.prod.snd (X := F)).app a z = (Limits.prod.snd (X := F)).app a w) :
    z = w := by
  apply Equiv.injective (binaryProductEquiv F G a)
  aesop

end prod

section coprod

/-- `coprod F G` is the explicit binary coproduct of type-valued functors `F` and `G`. -/
def coprod : C ⥤ Type w where
  obj a := F.obj a ⊕ G.obj a
  map f x := by
    cases x with
    | inl x => exact .inl (F.map f x)
    | inr x => exact .inr (G.map f x)

variable {F G}

/-- The left inclusion of `F` into `coprod F G`. -/
@[simps]
def coprod.inl : F ⟶ coprod F G where
  app _ x := .inl x

/-- The right inclusion of `G` into `coprod F G`. -/
@[simps]
def coprod.inr : G ⟶ coprod F G where
  app _ x := .inr x

/-- Given natural transformations `F₁ ⟶ F` and `F₂ ⟶ F`, construct
a natural transformation `coprod F₁ F₂ ⟶ F`. -/
@[simps]
def coprod.desc {F₁ F₂ : C ⥤ Type w} (τ₁ : F₁ ⟶ F) (τ₂ : F₂ ⟶ F) :
    coprod F₁ F₂ ⟶ F where
  app a x := by
     cases x with
     | inl x => exact τ₁.app a x
     | inr x => exact τ₂.app a x
  naturality _ _ _ := by
    ext x
    cases x with | _ => simp only [coprod, types_comp_apply, FunctorToTypes.naturality]

@[simp]
lemma coprod.desc_inl {F₁ F₂ : C ⥤ Type w} (τ₁ : F₁ ⟶ F) (τ₂ : F₂ ⟶ F) :
    coprod.inl ≫ coprod.desc τ₁ τ₂ = τ₁ := rfl

@[simp]
lemma coprod.desc_inr {F₁ F₂ : C ⥤ Type w} (τ₁ : F₁ ⟶ F) (τ₂ : F₂ ⟶ F) :
    coprod.inr ≫ coprod.desc τ₁ τ₂ = τ₂ := rfl

variable (F G)

/-- The binary cofan whose point is `coprod F G`. -/
@[simps!]
def binaryCoproductCocone : BinaryCofan F G :=
  BinaryCofan.mk coprod.inl coprod.inr

/-- `coprod F G` is a colimit cocone. -/
@[simps]
def binaryCoproductColimit : IsColimit (binaryCoproductCocone F G) where
  desc (s : BinaryCofan F G) := coprod.desc s.inl s.inr
  fac _ := fun ⟨j⟩ ↦ WalkingPair.casesOn j rfl rfl
  uniq _ _ h := by
    ext _ x
    cases x with | _ => simp [← h ⟨WalkingPair.right⟩, ← h ⟨WalkingPair.left⟩]

/-- `coprod F G` is a binary coproduct for `F` and `G`. -/
def binaryCoproductColimitCocone : Limits.ColimitCocone (pair F G) :=
  ⟨_, binaryCoproductColimit F G⟩

/-- The categorical binary coproduct of type-valued functors is `coprod F G`. -/
noncomputable def binaryCoproductIso : F ⨿ G ≅ coprod F G :=
  colimit.isoColimitCocone (binaryCoproductColimitCocone F G)

@[simp]
lemma inl_comp_binaryCoproductIso_hom :
    Limits.coprod.inl ≫ (binaryCoproductIso F G).hom = coprod.inl := by
  simp only [binaryCoproductIso]
  aesop

@[simp]
lemma inl_comp_binaryCoproductIso_hom_apply (a : C) (x : F.obj a) :
    (binaryCoproductIso F G).hom.app a ((Limits.coprod.inl (X := F)).app a x) = .inl x :=
  congr_fun (congr_app (inl_comp_binaryCoproductIso_hom F G) a) x

@[simp]
lemma inr_comp_binaryCoproductIso_hom :
    Limits.coprod.inr ≫ (binaryCoproductIso F G).hom = coprod.inr := by
  simp [binaryCoproductIso]
  aesop

@[simp]
lemma inr_comp_binaryCoproductIso_hom_apply (a : C) (x : G.obj a) :
    (binaryCoproductIso F G).hom.app a ((Limits.coprod.inr (X := F)).app a x) = .inr x :=
  congr_fun (congr_app (inr_comp_binaryCoproductIso_hom F G) a) x

@[simp]
lemma inl_comp_binaryCoproductIso_inv :
    coprod.inl ≫ (binaryCoproductIso F G).inv = (Limits.coprod.inl (X := F)) := rfl

@[simp]
lemma inl_comp_binaryCoproductIso_inv_apply (a : C) (x : F.obj a) :
    (binaryCoproductIso F G).inv.app a (.inl x) = (Limits.coprod.inl (X := F)).app a x := rfl

@[simp]
lemma inr_comp_binaryCoproductIso_inv :
    coprod.inr ≫ (binaryCoproductIso F G).inv = (Limits.coprod.inr (X := F)) := rfl

@[simp]
lemma inr_comp_binaryCoproductIso_inv_apply (a : C) (x : G.obj a) :
    (binaryCoproductIso F G).inv.app a (.inr x) = (Limits.coprod.inr (X := F)).app a x := rfl

variable {F G}

/-- Construct an element of `(F ⨿ G).obj a` from an element of `F.obj a` -/
noncomputable
abbrev coprodInl {a : C} (x : F.obj a) : (F ⨿ G).obj a :=
  (binaryCoproductIso F G).inv.app a (.inl x)

/-- Construct an element of `(F ⨿ G).obj a` from an element of `G.obj a` -/
noncomputable
abbrev coprodInr {a : C} (x : G.obj a) : (F ⨿ G).obj a :=
  (binaryCoproductIso F G).inv.app a (.inr x)

variable (F G)

/-- `(F ⨿ G).obj a` is in bijection with disjoint union of `F.obj a` and `G.obj a`. -/
@[simps]
noncomputable
def binaryCoproductEquiv (a : C) :
    (F ⨿ G).obj a ≃ (F.obj a) ⊕ (G.obj a) where
  toFun z := (binaryCoproductIso F G).hom.app a z
  invFun z := (binaryCoproductIso F G).inv.app a z
  left_inv _ := by simp only [hom_inv_id_app_apply]
  right_inv _ := by simp only [inv_hom_id_app_apply]

end coprod

variable {J : Type i} (F : J → C ⥤ Type max w i)

section pi

/-- `pi F` is the explicit indexed product of a family of type-valued functors `F i`. -/
def pi : C ⥤ Type max w i where
  obj a := Π j, (F j).obj a
  map f a := fun j => (F j).map f (a j)

variable {F}

/-- The `j`th projection of `pi F`, onto `F j`. -/
@[simps]
def pi.π (j : J) : pi F ⟶ F j where
  app _ a := a j

/-- Given natural transformations `(i : ι) → (G ⟶ F i)`, construct
a natural transformation `G ⟶ pi F`. -/
@[simps]
def pi.lift {G : C ⥤ Type max w i} (τ : ∀ j, G ⟶ F j) : G ⟶ pi F where
  app x y := fun j => (τ j).app x y
  naturality _ _ _ := by
    ext a
    simp only [types_comp_apply, FunctorToTypes.naturality]
    aesop

@[simp]
lemma pi.lift_π {G : C ⥤ Type max w i} (τ : ∀ j, G ⟶ F j) (j : J) :
    pi.lift τ ≫ pi.π j = τ j := rfl

variable (F)

/-- The fan whose point is `pi F`. -/
@[simps!]
def productCone : Fan F :=
  Fan.mk (pi F) pi.π

/-- `pi F` is a limit cone. -/
@[simps]
def productLimit : IsLimit (productCone F) where
  lift (s : Fan F) := pi.lift (s.π.app ⟨·⟩)
  fac _ := fun ⟨j⟩ ↦ by ext; simp
  uniq _ _ h := by ext; simp only [← h]; congr

/-- `pi F` is a product for `F`. -/
def productLimitCone : Limits.LimitCone (Discrete.functor F) :=
  ⟨_, productLimit F⟩

/-- The categorical product of type-valued functors is `pi F`. -/
noncomputable def productIso : ∏ᶜ F ≅ pi F :=
  limit.isoLimitCone (productLimitCone F)

@[simp]
lemma productIso_hom_comp_π (j : J) :
    (productIso F).hom ≫ pi.π j = Pi.π F j := rfl

@[simp]
lemma productIso_inv_comp_π (j : J) :
    (productIso F).inv ≫ Pi.π F j = pi.π j := by
  rw [Iso.inv_comp_eq]; rfl

@[simp]
lemma productIso_inv_comp_π_apply (a : C) (j : J) (z : (pi F).obj a) :
    (Pi.π F j).app a ((productIso F).inv.app a z) = z j :=
  congr_fun (congr_app (productIso_inv_comp_π F j) a) z



variable {F}

/-- Construct an element of `(pi F).obj a` from a family of elements `j ↦ (F j).obj a`. -/
noncomputable
def piMk {a : C} (x : Π j, (F j).obj a) : (∏ᶜ F).obj a :=
  ((productIso F).inv).app a x

@[simp]
lemma piMk_π {a : C} (x : Π j, (F j).obj a) (j : J) :
    (Pi.π F j).app a (piMk x) = x j := by
  simp only [piMk, productIso_inv_comp_π_apply]

@[ext]
lemma pi_ext {a : C} (z w : (pi F).obj a)
    (h : ∀ j, (pi.π j).app a z = (pi.π j).app a w) :
    z = w := by
  funext j
  simpa [pi.π] using h j

variable (F)

@[ext]
lemma pi_ext' (a : C) (z w : (∏ᶜ F).obj a)
    (h : ∀ j, (Pi.π F j).app a z = (Pi.π F j).app a w) :
    z = w := by
  apply Equiv.injective (piObjIso F a).toEquiv
  apply Types.limit_ext; intro ⟨j⟩
  simp_rw [Discrete.functor_obj_eq_as, Iso.toEquiv_fun, ← types_comp_apply (piObjIso F a).hom,
  ← Pi.π.eq_def, piObjIso_hom_comp_π, h]

end pi

section sigma

/-- `sigma F` is the explicit coproduct of type-valued functors `F i`. -/
def sigma : C ⥤ Type max w i where
  obj a := Σ j, (F j).obj a
  map f | ⟨j, x⟩ => ⟨j, (F j).map f x⟩

variable {F}

/-- The `j`th inclusion of `F j` into `sigma F`. -/
@[simps]
def sigma.ι (j : J) : F j ⟶ sigma F where
  app _ x := ⟨j, x⟩

/-- Given natural transformations `(j : J) → (F j ⟶ G)`, construct
a natural transformation `sigma F ⟶ G`. -/
@[simps]
def sigma.desc {G : C ⥤ Type max w i} (τ : (j : J) → F j ⟶ G) : sigma F ⟶ G where
  app a | ⟨j, x⟩ => (τ j).app a x
  naturality _ _ _ := by
    ext ⟨j, x⟩
    simp [sigma, FunctorToTypes.naturality]

@[simp]
lemma sigma.desc_ι {G : C ⥤ Type max w i} (τ : (j : J) → F j ⟶ G) (j : J) :
    sigma.ι j ≫ sigma.desc τ = τ j := rfl

variable (F)

/-- The cofan whose point is `sigma F`. -/
@[simps!]
def coproductCofan : Cofan F :=
  Cofan.mk (sigma F) sigma.ι

/-- `sigma F` is a colimit cocone. -/
@[simps]
def coproductColimit : IsColimit (coproductCofan F) where
  desc (s : Cofan F) := sigma.desc (s.ι.app ⟨·⟩)
  fac _ | ⟨j⟩ => by simp [coproductCofan]
  uniq _ _ h := by
    ext _ ⟨j, x⟩
    simp [← h, coproductCofan, sigma.ι]

/-- `sigma F` is a coproduct for `F`. -/
def coproductColimitCocone : Limits.ColimitCocone (Discrete.functor F) :=
  ⟨_, coproductColimit F⟩

/-- The categorical coproduct of type-valued functors is `sigma F`. -/
noncomputable def coproductIso : ∐ F ≅ sigma F :=
  colimit.isoColimitCocone (coproductColimitCocone F)

@[simp]
lemma ι_comp_coproductIso_hom (j : J) :
    Sigma.ι F j ≫ (coproductIso F).hom = sigma.ι j := by
  simp only [coproductIso]
  aesop

@[simp]
lemma ι_comp_coproductIso_hom_apply (a : C) (j : J) (x : (F j).obj a) :
    (coproductIso F).hom.app a ((Sigma.ι F j).app a x) = (sigma.ι j).app a x :=
  congr_fun (congr_app (ι_comp_coproductIso_hom F j) a) x

@[simp]
lemma ι_comp_coproductIso_inv (j : J) :
    sigma.ι j ≫ (coproductIso F).inv = Sigma.ι F j := rfl

@[simp]
lemma ι_comp_coproductIso_inv_apply (a : C) (j : J) (x : (F j).obj a) :
    (coproductIso F).inv.app a ((sigma.ι j).app a x) = (Sigma.ι F j).app a x := rfl

variable {F G}

/-- Construct an element of `(∐ F).obj a` from a `j` and an element of `(F j).obj a` -/
noncomputable
abbrev sigmaMk {a : C} (j : J) (x : (F j).obj a) : (∐ F).obj a :=
  (coproductIso F).inv.app a ⟨j, x⟩

@[elab_as_elim, cases_eliminator]
noncomputable def Sigma.obj_recOn {a : C} {motive : (∐ F).obj a → Sort*} (z : (∐ F).obj a)
    (mk : (j : J) → (x : (F j).obj a) → motive (sigmaMk j x)) : motive z :=
  let z' := (coproductIso F).hom.app a z
  have h : z = (coproductIso F).inv.app a z' := by
    unfold z'
    rw [← types_comp_apply _ ((coproductIso F).inv.app a), Iso.hom_inv_id_app]
    rfl
  cast (congrArg motive h.symm) (mk z'.1 z'.2)

@[simp]
lemma Sigma.obj_recOn_mk {a : C} {motive : (∐ F).obj a → Sort*}
    (mk : (j : J) → (x : (F j).obj a) → motive (sigmaMk j x))
    (j : J) (x : (F j).obj a) : Sigma.obj_recOn (sigmaMk j x) mk = mk j x := by
  unfold Sigma.obj_recOn sigmaMk
  rw [cast_eq_iff_heq, ← types_comp_apply _ ((coproductIso F).hom.app a), Iso.inv_hom_id_app]
  rfl

end sigma
end CategoryTheory.FunctorToTypes
