/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.RingTheory.Bialgebra.Equiv

/-!
# The category of commutative bialgebras over a commutative ring

This file defines the bundled category `CommBialgCat R` of commutative bialgebras over a fixed
commutative ring `R` along with the forgetful functor to `CommAlgCat`.
-/

@[expose] public section

noncomputable section

open Bialgebra Coalgebra Opposite CategoryTheory Limits MonObj
open scoped MonoidalCategory

universe v u
variable {R : Type u} [CommRing R]

variable (R) in
set_option backward.privateInPublic true in
/-- The category of commutative `R`-bialgebras and their morphisms. -/
structure CommBialgCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type v
  [commRing : CommRing carrier]
  [bialgebra : Bialgebra R carrier]

namespace CommBialgCat
variable {A B C : CommBialgCat.{v} R} {X Y Z : Type v} [CommRing X] [Bialgebra R X]
  [CommRing Y] [Bialgebra R Y] [CommRing Z] [Bialgebra R Z]

attribute [instance] commRing bialgebra

initialize_simps_projections CommBialgCat (-commRing, -bialgebra)

instance : CoeSort (CommBialgCat R) (Type v) := ⟨carrier⟩

attribute [coe] CommBialgCat.carrier

variable (R) in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Turn an unbundled `R`-bialgebra into the corresponding object in the category of `R`-bialgebras.

This is the preferred way to construct a term of `CommBialgCat R`. -/
abbrev of (X : Type v) [CommRing X] [Bialgebra R X] : CommBialgCat.{v} R := ⟨X⟩

variable (R) in
lemma coe_of (X : Type v) [CommRing X] [Bialgebra R X] : (of R X : Type v) = X := rfl

set_option backward.privateInPublic true in
/-- The type of morphisms in `CommBialgCat R`. -/
@[ext]
structure Hom (A B : CommBialgCat.{v} R) where
  private mk ::
  /-- The underlying bialgebra map. -/
  hom' : A →ₐc[R] B

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : Category (CommBialgCat.{v} R) where
  Hom A B := Hom A B
  id A := ⟨.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : ConcreteCategory (CommBialgCat.{v} R) (· →ₐc[R] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `CommBialgCat` back into a `BialgHom`. -/
abbrev Hom.hom (f : Hom A B) : A →ₐc[R] B := ConcreteCategory.hom (C := CommBialgCat R) f

/-- Typecheck a `BialgHom` as a morphism in `CommBialgCat R`. -/
abbrev ofHom {X Y : Type v} {_ : CommRing X} {_ : CommRing Y} {_ : Bialgebra R X}
    {_ : Bialgebra R Y} (f : X →ₐc[R] Y) : of R X ⟶ of R Y :=
  ConcreteCategory.ofHom (C := CommBialgCat R) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (A B : CommBialgCat.{v} R) (f : Hom A B) := f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp] lemma hom_id : (𝟙 A : A ⟶ A).hom = AlgHom.id R A := rfl
@[simp] lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

lemma id_apply (A : CommBialgCat.{v} R) (a : A) : (𝟙 A : A ⟶ A) a = a := by simp
lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp

@[ext] lemma hom_ext {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g := Hom.ext hf

@[simp] lemma hom_ofHom (f : X →ₐc[R] Y) : (ofHom f).hom = f := rfl
@[simp] lemma ofHom_hom (f : A ⟶ B) : ofHom f.hom = f := rfl

@[simp] lemma ofHom_id : ofHom (.id R X) = 𝟙 (of R X) := rfl

@[simp]
lemma ofHom_comp (f : X →ₐc[R] Y) (g : Y →ₐc[R] Z) : ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

lemma ofHom_apply (f : X →ₐc[R] Y) (x : X) : ofHom f x = f x := rfl

lemma inv_hom_apply (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by simp
lemma hom_inv_apply (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by simp

instance : Inhabited (CommBialgCat R) := ⟨of R R⟩

lemma forget_obj (A : CommBialgCat.{v} R) : (forget (CommBialgCat.{v} R)).obj A = A :=
  rfl

@[deprecated ConcreteCategory.forget_map_eq_ofHom (since := "2026-03-06")]
lemma forget_map (f : A ⟶ B) : (forget (CommBialgCat.{v} R)).map f = (f : _ → _) := rfl

instance : CommRing ((forget (CommBialgCat R)).obj A) := inferInstanceAs <| CommRing A

instance : Bialgebra R ((forget (CommBialgCat R)).obj A) := inferInstanceAs <| Bialgebra R A

instance hasForgetToCommAlgCat : HasForget₂ (CommBialgCat.{v} R) (CommAlgCat.{v} R) where
  forget₂.obj M := .of R M
  forget₂.map f := CommAlgCat.ofHom f.hom

@[simp] lemma forget₂_commAlgCat_obj (A : CommBialgCat.{v} R) :
    (forget₂ (CommBialgCat.{v} R) (CommAlgCat.{v} R)).obj A = .of R A := rfl

@[simp] lemma forget₂_commAlgCat_map (f : A ⟶ B) :
    (forget₂ (CommBialgCat.{v} R) (CommAlgCat.{v} R)).map f = CommAlgCat.ofHom f.hom := rfl

/-- Forgetting to the underlying type and then building the bundled object returns the original
bialgebra. -/
@[simps]
def ofSelfIso (M : CommBialgCat.{v} R) : of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

/-- Build an isomorphism in the category `CommBialgCat R` from a `BialgEquiv` between
`Bialgebra`s. -/
@[simps]
def isoMk {X Y : Type v} {_ : CommRing X} {_ : CommRing Y} {_ : Bialgebra R X}
    {_ : Bialgebra R Y} (e : X ≃ₐc[R] Y) : of R X ≅ of R Y where
  hom := ofHom (e : X →ₐc[R] Y)
  inv := ofHom (e.symm : Y →ₐc[R] X)

/-- Build a `BialgEquiv` from an isomorphism in the category `CommBialgCat R`. -/
@[simps apply, simps -isSimp symm_apply]
def bialgEquivOfIso (i : A ≅ B) : A ≃ₐc[R] B where
  __ := i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

/-- Bialgebra equivalences between `Bialgebra`s are the same as isomorphisms in `CommBialgCat`. -/
@[simps]
def isoEquivBialgEquiv : (of R X ≅ of R Y) ≃ (X ≃ₐc[R] Y) where
  toFun := bialgEquivOfIso
  invFun := isoMk
  left_inv _ := rfl
  right_inv _ := rfl

instance reflectsIsomorphisms_forget : (forget (CommBialgCat.{u} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (CommBialgCat.{u} R)).map f)
    let e : X ≃ₐc[R] Y := { f.hom, i.toEquiv with }
    exact (isoMk e).isIso_hom

end CommBialgCat

attribute [local ext] Quiver.Hom.unop_inj

instance CommAlgCat.monObjOpOf {A : Type u} [CommRing A] [Bialgebra R A] :
    MonObj (op <| CommAlgCat.of R A) where
  one := (CommAlgCat.ofHom <| counitAlgHom R A).op
  mul := (CommAlgCat.ofHom <| comulAlgHom R A).op
  one_mul := by ext; exact Coalgebra.rTensor_counit_comul _
  mul_one := by ext; exact Coalgebra.lTensor_counit_comul _
  mul_assoc := by ext; exact (Coalgebra.coassoc_symm_apply _).symm

@[simp]
lemma CommAlgCat.one_op_of_unop_hom {A : Type u} [CommRing A] [Bialgebra R A] :
    η[op <| CommAlgCat.of R A].unop.hom = counitAlgHom R A := rfl

@[simp]
lemma CommAlgCat.mul_op_of_unop_hom {A : Type u} [CommRing A] [Bialgebra R A] :
    μ[op <| CommAlgCat.of R A].unop.hom = comulAlgHom R A := rfl

instance {A : Type u} [CommRing A] [Bialgebra R A] [IsCocomm R A] :
    IsCommMonObj (Opposite.op <| CommAlgCat.of R A) where
  mul_comm := by ext; exact comm_comul R _

instance {A B : Type u} [CommRing A] [Bialgebra R A] [CommRing B] [Bialgebra R B]
    (f : A →ₐc[R] B) : IsMonHom (CommAlgCat.ofHom (f : A →ₐ[R] B)).op where
  mul_hom := by
    ext
    simp
    sorry

instance (A : (CommAlgCat R)ᵒᵖ) [MonObj A] : Bialgebra R A.unop :=
  .ofAlgHom μ[A].unop.hom η[A].unop.hom
    congr(($((MonObj.mul_assoc_flip A).symm)).unop.hom)
    congr(($(MonObj.one_mul A)).unop.hom)
    congr(($(MonObj.mul_one A)).unop.hom)

variable (R) in
/-- Commutative bialgebras over a commutative ring `R` are the same thing as comonoid
`R`-algebras. -/
@[simps! functor_obj_unop_X inverse_obj unitIso_hom_app
  unitIso_inv_app counitIso_hom_app counitIso_inv_app]
def commBialgCatEquivComonCommAlgCat : CommBialgCat R ≌ (Mon (CommAlgCat R)ᵒᵖ)ᵒᵖ where
  functor.obj A := .op <| .mk <| .op <| .of R A
  functor.map {A B} f := .op <| .mk' <| .op <| CommAlgCat.ofHom f.hom
  inverse.obj A := .of R A.unop.X.unop
  inverse.map {A B} f := CommBialgCat.ofHom <| .ofAlgHom f.unop.hom.unop.hom
    congr(($(IsMonHom.one_hom (f := f.unop.hom))).unop.hom)
    congr(($((IsMonHom.mul_hom (f := f.unop.hom)).symm)).unop.hom)
  unitIso.hom := 𝟙 _
  unitIso.inv := 𝟙 _
  counitIso.hom := 𝟙 _
  counitIso.inv := 𝟙 _

@[simp]
lemma commBialgCatEquivComonCommAlgCat_functor_map_unop_hom {A B : CommBialgCat R} (f : A ⟶ B) :
  ((commBialgCatEquivComonCommAlgCat R).functor.map f).unop.hom =
    (CommAlgCat.ofHom (AlgHomClass.toAlgHom f.hom)).op := rfl

@[simp]
lemma commBialgCatEquivComonCommAlgCat_inverse_map_unop_hom
    {A B : (Mon (CommAlgCat R)ᵒᵖ)ᵒᵖ} (f : A ⟶ B) :
  AlgHomClass.toAlgHom ((commBialgCatEquivComonCommAlgCat R).inverse.map f).hom =
    f.unop.hom.unop.hom := rfl

instance {A : CommBialgCat.{u} R} [IsCocomm R A] :
    IsCommMonObj ((commBialgCatEquivComonCommAlgCat R).functor.obj A).unop.X :=
  inferInstanceAs <| IsCommMonObj <| op <| CommAlgCat.of R A
