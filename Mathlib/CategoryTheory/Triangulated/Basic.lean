/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Shift.Basic

/-!
# Triangles

This file contains the definition of triangles in an additive category with an additive shift.
It also defines morphisms between these triangles.

TODO: generalise this to n-angles in n-angulated categories as in https://arxiv.org/abs/1006.4592
-/

@[expose] public section


noncomputable section

open CategoryTheory Limits

universe v v₀ v₁ v₂ u u₀ u₁ u₂

namespace CategoryTheory.Pretriangulated

open CategoryTheory.Category

/-
We work in a category `C` equipped with a shift.
-/
variable (C : Type u) [Category.{v} C] [HasShift C ℤ]

/-- A triangle in `C` is a sextuple `(X,Y,Z,f,g,h)` where `X,Y,Z` are objects of `C`,
and `f : X ⟶ Y`, `g : Y ⟶ Z`, `h : Z ⟶ X⟦1⟧` are morphisms in `C`. -/
@[stacks 0144]
structure Triangle where mk' ::
  /-- the first object of a triangle -/
  obj₁ : C
  /-- the second object of a triangle -/
  obj₂ : C
  /-- the third object of a triangle -/
  obj₃ : C
  /-- the first morphism of a triangle -/
  mor₁ : obj₁ ⟶ obj₂
  /-- the second morphism of a triangle -/
  mor₂ : obj₂ ⟶ obj₃
  /-- the third morphism of a triangle -/
  mor₃ : obj₃ ⟶ obj₁⟦(1 : ℤ)⟧

variable {C}

/-- A triangle `(X,Y,Z,f,g,h)` in `C` is defined by the morphisms `f : X ⟶ Y`, `g : Y ⟶ Z`
and `h : Z ⟶ X⟦1⟧`.
-/
@[simps]
def Triangle.mk {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧) : Triangle C where
  obj₁ := X
  obj₂ := Y
  obj₃ := Z
  mor₁ := f
  mor₂ := g
  mor₃ := h

section

variable [HasZeroObject C] [HasZeroMorphisms C]

open ZeroObject

instance : Inhabited (Triangle C) :=
  ⟨⟨0, 0, 0, 0, 0, 0⟩⟩

/-- For each object in `C`, there is a triangle of the form `(X,X,0,𝟙 X,0,0)`
-/
@[simps!]
def contractibleTriangle (X : C) : Triangle C :=
  Triangle.mk (𝟙 X) (0 : X ⟶ 0) 0

end

/-- A morphism of triangles `(X,Y,Z,f,g,h) ⟶ (X',Y',Z',f',g',h')` in `C` is a triple of morphisms
`a : X ⟶ X'`, `b : Y ⟶ Y'`, `c : Z ⟶ Z'` such that
`a ≫ f' = f ≫ b`, `b ≫ g' = g ≫ c`, and `a⟦1⟧' ≫ h = h' ≫ c`.
In other words, we have a commutative diagram:
```
     f      g      h
  X  ───> Y  ───> Z  ───> X⟦1⟧
  │       │       │        │
  │a      │b      │c       │a⟦1⟧'
  V       V       V        V
  X' ───> Y' ───> Z' ───> X'⟦1⟧
     f'     g'     h'
```
-/
@[ext, stacks 0144]
structure TriangleMorphism (T₁ : Triangle C) (T₂ : Triangle C) where
  /-- the first morphism in a triangle morphism -/
  hom₁ : T₁.obj₁ ⟶ T₂.obj₁
  /-- the second morphism in a triangle morphism -/
  hom₂ : T₁.obj₂ ⟶ T₂.obj₂
  /-- the third morphism in a triangle morphism -/
  hom₃ : T₁.obj₃ ⟶ T₂.obj₃
  /-- the first commutative square of a triangle morphism -/
  comm₁ : T₁.mor₁ ≫ hom₂ = hom₁ ≫ T₂.mor₁ := by cat_disch
  /-- the second commutative square of a triangle morphism -/
  comm₂ : T₁.mor₂ ≫ hom₃ = hom₂ ≫ T₂.mor₂ := by cat_disch
  /-- the third commutative square of a triangle morphism -/
  comm₃ : T₁.mor₃ ≫ hom₁⟦1⟧' = hom₃ ≫ T₂.mor₃ := by cat_disch

attribute [reassoc (attr := simp)] TriangleMorphism.comm₁ TriangleMorphism.comm₂
  TriangleMorphism.comm₃

/-- The identity triangle morphism.
-/
@[simps]
def triangleMorphismId (T : Triangle C) : TriangleMorphism T T where
  hom₁ := 𝟙 T.obj₁
  hom₂ := 𝟙 T.obj₂
  hom₃ := 𝟙 T.obj₃

instance (T : Triangle C) : Inhabited (TriangleMorphism T T) :=
  ⟨triangleMorphismId T⟩

variable {T₁ T₂ T₃ : Triangle C}

/-- Composition of triangle morphisms gives a triangle morphism.
-/
@[simps]
def TriangleMorphism.comp (f : TriangleMorphism T₁ T₂) (g : TriangleMorphism T₂ T₃) :
    TriangleMorphism T₁ T₃ where
  hom₁ := f.hom₁ ≫ g.hom₁
  hom₂ := f.hom₂ ≫ g.hom₂
  hom₃ := f.hom₃ ≫ g.hom₃

/-- Triangles with triangle morphisms form a category.
-/
@[simps]
instance triangleCategory : Category (Triangle C) where
  Hom A B := TriangleMorphism A B
  id A := triangleMorphismId A
  comp f g := f.comp g

@[ext]
lemma Triangle.hom_ext {A B : Triangle C} (f g : A ⟶ B)
    (h₁ : f.hom₁ = g.hom₁) (h₂ : f.hom₂ = g.hom₂) (h₃ : f.hom₃ = g.hom₃) : f = g :=
  TriangleMorphism.ext h₁ h₂ h₃

@[simp]
lemma id_hom₁ (A : Triangle C) : TriangleMorphism.hom₁ (𝟙 A) = 𝟙 _ := rfl
@[simp]
lemma id_hom₂ (A : Triangle C) : TriangleMorphism.hom₂ (𝟙 A) = 𝟙 _ := rfl
@[simp]
lemma id_hom₃ (A : Triangle C) : TriangleMorphism.hom₃ (𝟙 A) = 𝟙 _ := rfl

@[simp, reassoc]
lemma comp_hom₁ {X Y Z : Triangle C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom₁ = f.hom₁ ≫ g.hom₁ := rfl
@[simp, reassoc]
lemma comp_hom₂ {X Y Z : Triangle C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom₂ = f.hom₂ ≫ g.hom₂ := rfl
@[simp, reassoc]
lemma comp_hom₃ {X Y Z : Triangle C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom₃ = f.hom₃ ≫ g.hom₃ := rfl

/-- Make a morphism between triangles from the required data. -/
@[simps]
def Triangle.homMk (A B : Triangle C)
    (hom₁ : A.obj₁ ⟶ B.obj₁) (hom₂ : A.obj₂ ⟶ B.obj₂) (hom₃ : A.obj₃ ⟶ B.obj₃)
    (comm₁ : A.mor₁ ≫ hom₂ = hom₁ ≫ B.mor₁ := by cat_disch)
    (comm₂ : A.mor₂ ≫ hom₃ = hom₂ ≫ B.mor₂ := by cat_disch)
    (comm₃ : A.mor₃ ≫ hom₁⟦1⟧' = hom₃ ≫ B.mor₃ := by cat_disch) :
    A ⟶ B where
  hom₁ := hom₁
  hom₂ := hom₂
  hom₃ := hom₃
  comm₁ := comm₁
  comm₂ := comm₂
  comm₃ := comm₃

/-- Make an isomorphism between triangles from the required data. -/
@[simps]
def Triangle.isoMk (A B : Triangle C)
    (iso₁ : A.obj₁ ≅ B.obj₁) (iso₂ : A.obj₂ ≅ B.obj₂) (iso₃ : A.obj₃ ≅ B.obj₃)
    (comm₁ : A.mor₁ ≫ iso₂.hom = iso₁.hom ≫ B.mor₁ := by cat_disch)
    (comm₂ : A.mor₂ ≫ iso₃.hom = iso₂.hom ≫ B.mor₂ := by cat_disch)
    (comm₃ : A.mor₃ ≫ iso₁.hom⟦1⟧' = iso₃.hom ≫ B.mor₃ := by cat_disch) : A ≅ B where
  hom := Triangle.homMk _ _ iso₁.hom iso₂.hom iso₃.hom comm₁ comm₂ comm₃
  inv := Triangle.homMk _ _ iso₁.inv iso₂.inv iso₃.inv
    (by simp only [← cancel_mono iso₂.hom, assoc, Iso.inv_hom_id, comp_id,
      comm₁, Iso.inv_hom_id_assoc])
    (by simp only [← cancel_mono iso₃.hom, assoc, Iso.inv_hom_id, comp_id,
      comm₂, Iso.inv_hom_id_assoc])
    (by simp only [← cancel_mono (iso₁.hom⟦(1 : ℤ)⟧'), Category.assoc, comm₃,
      Iso.inv_hom_id_assoc, ← Functor.map_comp, Iso.inv_hom_id,
      Functor.map_id, Category.comp_id])

lemma Triangle.isIso_of_isIsos {A B : Triangle C} (f : A ⟶ B)
    (h₁ : IsIso f.hom₁) (h₂ : IsIso f.hom₂) (h₃ : IsIso f.hom₃) : IsIso f := by
  let e := Triangle.isoMk A B (asIso f.hom₁) (asIso f.hom₂) (asIso f.hom₃)
    (by simp) (by simp) (by simp)
  exact (inferInstance : IsIso e.hom)

@[reassoc (attr := simp)]
lemma _root_.CategoryTheory.Iso.hom_inv_id_triangle_hom₁ {A B : Triangle C} (e : A ≅ B) :
    e.hom.hom₁ ≫ e.inv.hom₁ = 𝟙 _ := by rw [← comp_hom₁, e.hom_inv_id, id_hom₁]
@[reassoc (attr := simp)]
lemma _root_.CategoryTheory.Iso.hom_inv_id_triangle_hom₂ {A B : Triangle C} (e : A ≅ B) :
    e.hom.hom₂ ≫ e.inv.hom₂ = 𝟙 _ := by rw [← comp_hom₂, e.hom_inv_id, id_hom₂]
@[reassoc (attr := simp)]
lemma _root_.CategoryTheory.Iso.hom_inv_id_triangle_hom₃ {A B : Triangle C} (e : A ≅ B) :
    e.hom.hom₃ ≫ e.inv.hom₃ = 𝟙 _ := by rw [← comp_hom₃, e.hom_inv_id, id_hom₃]

@[reassoc (attr := simp)]
lemma _root_.CategoryTheory.Iso.inv_hom_id_triangle_hom₁ {A B : Triangle C} (e : A ≅ B) :
    e.inv.hom₁ ≫ e.hom.hom₁ = 𝟙 _ := by rw [← comp_hom₁, e.inv_hom_id, id_hom₁]
@[reassoc (attr := simp)]
lemma _root_.CategoryTheory.Iso.inv_hom_id_triangle_hom₂ {A B : Triangle C} (e : A ≅ B) :
    e.inv.hom₂ ≫ e.hom.hom₂ = 𝟙 _ := by rw [← comp_hom₂, e.inv_hom_id, id_hom₂]
@[reassoc (attr := simp)]
lemma _root_.CategoryTheory.Iso.inv_hom_id_triangle_hom₃ {A B : Triangle C} (e : A ≅ B) :
    e.inv.hom₃ ≫ e.hom.hom₃ = 𝟙 _ := by rw [← comp_hom₃, e.inv_hom_id, id_hom₃]

lemma Triangle.eqToHom_hom₁ {A B : Triangle C} (h : A = B) :
    (eqToHom h).hom₁ = eqToHom (by subst h; rfl) := by subst h; rfl
lemma Triangle.eqToHom_hom₂ {A B : Triangle C} (h : A = B) :
    (eqToHom h).hom₂ = eqToHom (by subst h; rfl) := by subst h; rfl
lemma Triangle.eqToHom_hom₃ {A B : Triangle C} (h : A = B) :
    (eqToHom h).hom₃ = eqToHom (by subst h; rfl) := by subst h; rfl

namespace Triangle

section Preadditive

variable [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]

@[simps (attr := grind =)]
instance : Zero (T₁ ⟶ T₂) where
  zero :=
    { hom₁ := 0
      hom₂ := 0
      hom₃ := 0 }

@[simps (attr := grind =)]
instance : Add (T₁ ⟶ T₂) where
  add f g :=
    { hom₁ := f.hom₁ + g.hom₁
      hom₂ := f.hom₂ + g.hom₂
      hom₃ := f.hom₃ + g.hom₃ }

@[simps (attr := grind =)]
instance : Neg (T₁ ⟶ T₂) where
  neg f :=
    { hom₁ := -f.hom₁
      hom₂ := -f.hom₂
      hom₃ := -f.hom₃ }

@[simps (attr := grind =)]
instance : Sub (T₁ ⟶ T₂) where
  sub f g :=
    { hom₁ := f.hom₁ - g.hom₁
      hom₂ := f.hom₂ - g.hom₂
      hom₃ := f.hom₃ - g.hom₃ }

section

variable {R : Type*} [Semiring R] [Linear R C]
  [∀ (n : ℤ), Functor.Linear R (shiftFunctor C n)]

@[simps (attr := grind =)]
instance : SMul R (T₁ ⟶ T₂) where
  smul n f :=
    { hom₁ := n • f.hom₁
      hom₂ := n • f.hom₂
      hom₃ := n • f.hom₃ }

omit [∀ (n : ℤ), (shiftFunctor C n).Additive]

end

instance : AddCommGroup (T₁ ⟶ T₂) where
  zero_add f := by ext <;> apply zero_add
  add_assoc f g h := by ext <;> apply add_assoc
  add_zero f := by ext <;> apply add_zero
  add_comm f g := by ext <;> apply add_comm
  neg_add_cancel f := by ext <;> apply neg_add_cancel
  sub_eq_add_neg f g := by ext <;> apply sub_eq_add_neg
  nsmul n f := n • f
  nsmul_zero f := by cat_disch
  nsmul_succ n f := by ext <;> apply AddMonoid.nsmul_succ
  zsmul n f := n • f
  zsmul_zero' := by cat_disch
  zsmul_succ' n f := by ext <;> apply SubNegMonoid.zsmul_succ'
  zsmul_neg' n f := by ext <;> apply SubNegMonoid.zsmul_neg'

instance : Preadditive (Triangle C) where

end Preadditive

section Linear

variable [Preadditive C] {R : Type*} [Semiring R] [Linear R C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [∀ (n : ℤ), Functor.Linear R (shiftFunctor C n)]

attribute [local simp] mul_smul add_smul in
instance : Module R (T₁ ⟶ T₂) where
  one_smul := by aesop
  mul_smul := by aesop
  smul_zero := by aesop
  smul_add := by aesop
  add_smul := by aesop
  zero_smul := by aesop

instance : Linear R (Triangle C) where

end Linear

end Triangle

/-- The obvious triangle `X₁ ⟶ X₁ ⊞ X₂ ⟶ X₂ ⟶ X₁⟦1⟧`. -/
@[simps!]
def binaryBiproductTriangle (X₁ X₂ : C) [HasZeroMorphisms C] [HasBinaryBiproduct X₁ X₂] :
    Triangle C :=
  Triangle.mk biprod.inl (Limits.biprod.snd : X₁ ⊞ X₂ ⟶ _) 0

/-- The obvious triangle `X₁ ⟶ X₁ ⨯ X₂ ⟶ X₂ ⟶ X₁⟦1⟧`. -/
@[simps!]
def binaryProductTriangle (X₁ X₂ : C) [HasZeroMorphisms C] [HasBinaryProduct X₁ X₂] :
    Triangle C :=
  Triangle.mk ((Limits.prod.lift (𝟙 X₁) 0)) (Limits.prod.snd : X₁ ⨯ X₂ ⟶ _) 0

set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism of triangles
`binaryProductTriangle X₁ X₂ ≅ binaryBiproductTriangle X₁ X₂`. -/
@[simps!]
def binaryProductTriangleIsoBinaryBiproductTriangle
    (X₁ X₂ : C) [HasZeroMorphisms C] [HasBinaryBiproduct X₁ X₂] :
    binaryProductTriangle X₁ X₂ ≅ binaryBiproductTriangle X₁ X₂ :=
  Triangle.isoMk _ _ (Iso.refl _) (biprod.isoProd X₁ X₂).symm (Iso.refl _)
    (by cat_disch) (by simp) (by simp)

section

variable {J : Type*} (T : J → Triangle C)
  [HasProduct (fun j => (T j).obj₁)] [HasProduct (fun j => (T j).obj₂)]
  [HasProduct (fun j => (T j).obj₃)] [HasProduct (fun j => (T j).obj₁⟦(1 : ℤ)⟧)]

/-- The product of a family of triangles. -/
@[simps!]
def productTriangle : Triangle C :=
  Triangle.mk (Limits.Pi.map (fun j => (T j).mor₁))
    (Limits.Pi.map (fun j => (T j).mor₂))
    (Limits.Pi.map (fun j => (T j).mor₃) ≫ inv (piComparison _ _))

set_option backward.isDefEq.respectTransparency false in
/-- A projection from the product of a family of triangles. -/
@[simps]
def productTriangle.π (j : J) :
    productTriangle T ⟶ T j where
  hom₁ := Pi.π _ j
  hom₂ := Pi.π _ j
  hom₃ := Pi.π _ j

/-- The fan given by `productTriangle T`. -/
@[simp]
def productTriangle.fan : Fan T := Fan.mk (productTriangle T) (productTriangle.π T)

set_option backward.isDefEq.respectTransparency false in
/-- A family of morphisms `T' ⟶ T j` lifts to a morphism `T' ⟶ productTriangle T`. -/
@[simps]
def productTriangle.lift {T' : Triangle C} (φ : ∀ j, T' ⟶ T j) :
    T' ⟶ productTriangle T where
  hom₁ := Pi.lift (fun j => (φ j).hom₁)
  hom₂ := Pi.lift (fun j => (φ j).hom₂)
  hom₃ := Pi.lift (fun j => (φ j).hom₃)
  comm₃ := by
    dsimp
    rw [← cancel_mono (piComparison _ _), assoc, assoc, assoc, IsIso.inv_hom_id, comp_id]
    cat_disch

set_option backward.isDefEq.respectTransparency false in
/-- The triangle `productTriangle T` satisfies the universal property of the categorical
product of the triangles `T`. -/
def productTriangle.isLimitFan : IsLimit (productTriangle.fan T) :=
  mkFanLimit _ (fun s => productTriangle.lift T s.proj) (fun s j => by cat_disch) (by
    intro s m hm
    ext1
    all_goals
      exact Pi.hom_ext _ _ (fun j => (by simp [← hm])))

set_option backward.isDefEq.respectTransparency false in
lemma productTriangle.zero₃₁ [HasZeroMorphisms C]
    (h : ∀ j, (T j).mor₃ ≫ (T j).mor₁⟦(1 : ℤ)⟧' = 0) :
    (productTriangle T).mor₃ ≫ (productTriangle T).mor₁⟦1⟧' = 0 := by
  have : HasProduct (fun j => (T j).obj₂⟦(1 : ℤ)⟧) :=
    ⟨_, isLimitFanMkObjOfIsLimit (shiftFunctor C (1 : ℤ)) _ _
      (productIsProduct (fun j => (T j).obj₂))⟩
  dsimp
  change _ ≫ (Pi.lift (fun j => Pi.π _ j ≫ (T j).mor₁))⟦(1 : ℤ)⟧' = 0
  rw [assoc, ← cancel_mono (piComparison _ _), zero_comp, assoc, assoc]
  ext j
  simp [h j]

end

variable (C) in
/-- The functor `C ⥤ Triangle C` which sends `X` to `contractibleTriangle X`. -/
@[simps]
def contractibleTriangleFunctor [HasZeroObject C] [HasZeroMorphisms C] : C ⥤ Triangle C where
  obj X := contractibleTriangle X
  map f :=
    { hom₁ := f
      hom₂ := f
      hom₃ := 0 }

namespace Triangle

/-- The first projection `Triangle C ⥤ C`. -/
@[simps]
def π₁ : Triangle C ⥤ C where
  obj T := T.obj₁
  map f := f.hom₁

/-- The second projection `Triangle C ⥤ C`. -/
@[simps]
def π₂ : Triangle C ⥤ C where
  obj T := T.obj₂
  map f := f.hom₂

/-- The third projection `Triangle C ⥤ C`. -/
@[simps]
def π₃ : Triangle C ⥤ C where
  obj T := T.obj₃
  map f := f.hom₃

/-- The first morphism of a triangle, as a natural transformation `π₁ ⟶ π₂`. -/
@[simps]
def π₁Toπ₂ : (π₁ : Triangle C ⥤ C) ⟶ Triangle.π₂ where
  app T := T.mor₁

/-- The second morphism of a triangle, as a natural transformation `π₂ ⟶ π₃`. -/
@[simps]
def π₂Toπ₃ : (π₂ : Triangle C ⥤ C) ⟶ Triangle.π₃ where
  app T := T.mor₂

/-- The third morphism of a triangle, as a natural
transformation `π₃ ⟶ π₁ ⋙ shiftFunctor _ (1 : ℤ)`. -/
@[simps]
def π₃Toπ₁ : (π₃ : Triangle C ⥤ C) ⟶ π₁ ⋙ shiftFunctor C (1 : ℤ) where
  app T := T.mor₃

section

variable {A B : Triangle C} (φ : A ⟶ B) [IsIso φ]

instance : IsIso φ.hom₁ := (inferInstance : IsIso (π₁.map φ))
instance : IsIso φ.hom₂ := (inferInstance : IsIso (π₂.map φ))
instance : IsIso φ.hom₃ := (inferInstance : IsIso (π₃.map φ))

end

section

open Functor

variable {J : Type*} [Category* J]

set_option backward.isDefEq.respectTransparency false in
/-- Constructor for functors to the category of triangles. -/
@[simps]
def functorMk {obj₁ obj₂ obj₃ : J ⥤ C}
    (mor₁ : obj₁ ⟶ obj₂) (mor₂ : obj₂ ⟶ obj₃) (mor₃ : obj₃ ⟶ obj₁ ⋙ shiftFunctor C (1 : ℤ)) :
    J ⥤ Triangle C where
  obj j := mk (mor₁.app j) (mor₂.app j) (mor₃.app j)
  map φ :=
    { hom₁ := obj₁.map φ
      hom₂ := obj₂.map φ
      hom₃ := obj₃.map φ }

/-- Constructor for natural transformations between functors to the
category of triangles. -/
@[simps]
def functorHomMk (A B : J ⥤ Triangle C) (hom₁ : A ⋙ π₁ ⟶ B ⋙ π₁)
    (hom₂ : A ⋙ π₂ ⟶ B ⋙ π₂) (hom₃ : A ⋙ π₃ ⟶ B ⋙ π₃)
    (comm₁ : whiskerLeft A π₁Toπ₂ ≫ hom₂ = hom₁ ≫ whiskerLeft B π₁Toπ₂ := by cat_disch)
    (comm₂ : whiskerLeft A π₂Toπ₃ ≫ hom₃ = hom₂ ≫ whiskerLeft B π₂Toπ₃ := by cat_disch)
    (comm₃ : whiskerLeft A π₃Toπ₁ ≫ whiskerRight hom₁ (shiftFunctor C (1 : ℤ)) =
      hom₃ ≫ whiskerLeft B π₃Toπ₁ := by cat_disch) : A ⟶ B where
  app j :=
    { hom₁ := hom₁.app j
      hom₂ := hom₂.app j
      hom₃ := hom₃.app j
      comm₁ := NatTrans.congr_app comm₁ j
      comm₂ := NatTrans.congr_app comm₂ j
      comm₃ := NatTrans.congr_app comm₃ j }
  naturality _ _ φ := by
    ext
    · exact hom₁.naturality φ
    · exact hom₂.naturality φ
    · exact hom₃.naturality φ

/-- Constructor for natural transformations between functors constructed
with `functorMk`. -/
@[simps!]
def functorHomMk'
    {obj₁ obj₂ obj₃ : J ⥤ C}
    {mor₁ : obj₁ ⟶ obj₂} {mor₂ : obj₂ ⟶ obj₃} {mor₃ : obj₃ ⟶ obj₁ ⋙ shiftFunctor C (1 : ℤ)}
    {obj₁' obj₂' obj₃' : J ⥤ C}
    {mor₁' : obj₁' ⟶ obj₂'} {mor₂' : obj₂' ⟶ obj₃'}
    {mor₃' : obj₃' ⟶ obj₁' ⋙ shiftFunctor C (1 : ℤ)}
    (hom₁ : obj₁ ⟶ obj₁') (hom₂ : obj₂ ⟶ obj₂') (hom₃ : obj₃ ⟶ obj₃')
    (comm₁ : mor₁ ≫ hom₂ = hom₁ ≫ mor₁')
    (comm₂ : mor₂ ≫ hom₃ = hom₂ ≫ mor₂')
    (comm₃ : mor₃ ≫ whiskerRight hom₁ (shiftFunctor C (1 : ℤ)) = hom₃ ≫ mor₃') :
    functorMk mor₁ mor₂ mor₃ ⟶ functorMk mor₁' mor₂' mor₃' :=
  functorHomMk _ _ hom₁ hom₂ hom₃ comm₁ comm₂ comm₃

set_option backward.isDefEq.respectTransparency false in
/-- Constructor for natural isomorphisms between functors to the
category of triangles. -/
@[simps]
def functorIsoMk (A B : J ⥤ Triangle C) (iso₁ : A ⋙ π₁ ≅ B ⋙ π₁)
    (iso₂ : A ⋙ π₂ ≅ B ⋙ π₂) (iso₃ : A ⋙ π₃ ≅ B ⋙ π₃)
    (comm₁ : whiskerLeft A π₁Toπ₂ ≫ iso₂.hom = iso₁.hom ≫ whiskerLeft B π₁Toπ₂)
    (comm₂ : whiskerLeft A π₂Toπ₃ ≫ iso₃.hom = iso₂.hom ≫ whiskerLeft B π₂Toπ₃)
    (comm₃ : whiskerLeft A π₃Toπ₁ ≫ whiskerRight iso₁.hom (shiftFunctor C (1 : ℤ)) =
      iso₃.hom ≫ whiskerLeft B π₃Toπ₁) : A ≅ B where
  hom := functorHomMk _ _ iso₁.hom iso₂.hom iso₃.hom comm₁ comm₂ comm₃
  inv := functorHomMk _ _ iso₁.inv iso₂.inv iso₃.inv
    (by simp only [← cancel_epi iso₁.hom, ← reassoc_of% comm₁,
          Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc])
    (by simp only [← cancel_epi iso₂.hom, ← reassoc_of% comm₂,
          Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc])
    (by
      simp only [← cancel_epi iso₃.hom, ← reassoc_of% comm₃, Iso.hom_inv_id_assoc,
        ← whiskerRight_comp, Iso.hom_inv_id, whiskerRight_id']
      apply comp_id)

/-- Constructor for natural isomorphisms between functors constructed
with `functorMk`. -/
@[simps!]
def functorIsoMk'
    {obj₁ obj₂ obj₃ : J ⥤ C}
    {mor₁ : obj₁ ⟶ obj₂} {mor₂ : obj₂ ⟶ obj₃} {mor₃ : obj₃ ⟶ obj₁ ⋙ shiftFunctor C (1 : ℤ)}
    {obj₁' obj₂' obj₃' : J ⥤ C}
    {mor₁' : obj₁' ⟶ obj₂'} {mor₂' : obj₂' ⟶ obj₃'}
    {mor₃' : obj₃' ⟶ obj₁' ⋙ shiftFunctor C (1 : ℤ)}
    (iso₁ : obj₁ ≅ obj₁') (iso₂ : obj₂ ≅ obj₂') (iso₃ : obj₃ ≅ obj₃')
    (comm₁ : mor₁ ≫ iso₂.hom = iso₁.hom ≫ mor₁')
    (comm₂ : mor₂ ≫ iso₃.hom = iso₂.hom ≫ mor₂')
    (comm₃ : mor₃ ≫ whiskerRight iso₁.hom (shiftFunctor C (1 : ℤ)) = iso₃.hom ≫ mor₃') :
    functorMk mor₁ mor₂ mor₃ ≅ functorMk mor₁' mor₂' mor₃' :=
  functorIsoMk _ _ iso₁ iso₂ iso₃ comm₁ comm₂ comm₃

end

end Triangle

end CategoryTheory.Pretriangulated
