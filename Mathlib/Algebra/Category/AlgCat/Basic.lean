/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Category instance for algebras over a commutative ring

We introduce the bundled category `AlgCat` of algebras over a fixed commutative ring `R` along
with the forgetful functors to `RingCat` and `ModuleCat`. We furthermore show that the functor
associating to a type the free `R`-algebra on that type is left adjoint to the forgetful functor.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

variable (R : Type u) [CommRing R]

/-- The category of R-algebras and their morphisms. -/
structure AlgCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type v
  [isRing : Ring carrier]
  [isAlgebra : Algebra R carrier]

attribute [instance] AlgCat.isRing AlgCat.isAlgebra

initialize_simps_projections AlgCat (-isRing, -isAlgebra)

namespace AlgCat

instance : CoeSort (AlgCat R) (Type v) :=
  ⟨AlgCat.carrier⟩

attribute [coe] AlgCat.carrier

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `AlgCat R`. -/
abbrev of (X : Type v) [Ring X] [Algebra R X] : AlgCat.{v} R :=
  ⟨X⟩

lemma coe_of (X : Type v) [Ring X] [Algebra R X] : (of R X : Type v) = X :=
  rfl

variable {R} in
/-- The type of morphisms in `AlgCat R`. -/
@[ext]
structure Hom (A B : AlgCat.{v} R) where
  private mk ::
  /-- The underlying algebra map. -/
  hom' : A →ₐ[R] B

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : Category (AlgCat.{v} R) where
  Hom A B := Hom A B
  id A := ⟨AlgHom.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : ConcreteCategory (AlgCat.{v} R) (· →ₐ[R] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

variable {R} in
/-- Turn a morphism in `AlgCat` back into an `AlgHom`. -/
abbrev Hom.hom {A B : AlgCat.{v} R} (f : Hom A B) :=
  ConcreteCategory.hom (C := AlgCat R) f

variable {R} in
/-- Typecheck an `AlgHom` as a morphism in `AlgCat`. -/
abbrev ofHom {A B : Type v} [Ring A] [Ring B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    of R A ⟶ of R B :=
  ConcreteCategory.ofHom (C := AlgCat R) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (A B : AlgCat.{v} R) (f : Hom A B) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
lemma hom_id {A : AlgCat.{v} R} : (𝟙 A : A ⟶ A).hom = AlgHom.id R A := rfl

/- Provided for rewriting. -/
lemma id_apply (A : AlgCat.{v} R) (a : A) :
    (𝟙 A : A ⟶ A) a = a := by simp

@[simp]
lemma hom_comp {A B C : AlgCat.{v} R} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply {A B C : AlgCat.{v} R} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
    (f ≫ g) a = g (f a) := by simp

@[ext]
lemma hom_ext {A B : AlgCat.{v} R} {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
lemma hom_ofHom {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [Algebra R X] [Ring Y]
    [Algebra R Y] (f : X →ₐ[R] Y) : (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom {A B : AlgCat.{v} R} (f : A ⟶ B) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {X : Type v} [Ring X] [Algebra R X] : ofHom (AlgHom.id R X) = 𝟙 (of R X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type v} [Ring X] [Ring Y] [Ring Z] [Algebra R X] [Algebra R Y]
    [Algebra R Z] (f : X →ₐ[R] Y) (g : Y →ₐ[R] Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [Algebra R X] [Ring Y]
    [Algebra R Y] (f : X →ₐ[R] Y) (x : X) : ofHom f x = f x := rfl

lemma inv_hom_apply {A B : AlgCat.{v} R} (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by
  simp

lemma hom_inv_apply {A B : AlgCat.{v} R} (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by
  simp

instance : Inhabited (AlgCat R) :=
  ⟨of R R⟩

lemma forget_obj {A : AlgCat.{v} R} : (forget (AlgCat.{v} R)).obj A = A := rfl

@[deprecated ConcreteCategory.forget_map_eq_ofHom (since := "2026-03-03")]
lemma forget_map {A B : AlgCat.{v} R} (f : A ⟶ B) :
    (forget (AlgCat.{v} R)).map f = (f : _ → _) :=
  rfl

instance {S : AlgCat.{v} R} : Ring ((forget (AlgCat R)).obj S) :=
  inferInstanceAs <| Ring S.carrier

instance {S : AlgCat.{v} R} : Algebra R ((forget (AlgCat R)).obj S) :=
  inferInstanceAs <| Algebra R S.carrier

instance hasForgetToRing : HasForget₂ (AlgCat.{v} R) RingCat.{v} where
  forget₂ :=
    { obj := fun A => ↧A
      map := fun f => RingCat.ofHom f.hom.toRingHom }

@[simp]
lemma forget₂_ringCat_obj (X : AlgCat.{v} R) :
    (forget₂ (AlgCat.{v} R) RingCat.{v}).obj X = ↧X :=
  rfl

@[simp]
lemma forget₂_ringCat_map {X Y : AlgCat.{v} R} (f : X ⟶ Y) :
    (forget₂ (AlgCat.{v} R) RingCat.{v}).map f = RingCat.ofHom f.hom :=
  rfl

instance (A : AlgCat.{v} R) : Algebra R ((forget₂ (AlgCat.{v} R) RingCat).obj A) :=
  inferInstanceAs <| Algebra R A

instance hasForgetToModule : HasForget₂ (AlgCat.{v} R) (ModuleCat.{v} R) where
  forget₂ :=
    { obj := fun M => ModuleCat.of R M
      map := fun f => ModuleCat.ofHom f.hom.toLinearMap }

@[simp]
lemma forget₂_module_obj (X : AlgCat.{v} R) :
    (forget₂ (AlgCat.{v} R) (ModuleCat.{v} R)).obj X = ModuleCat.of R X :=
  rfl

@[simp]
lemma forget₂_module_map {X Y : AlgCat.{v} R} (f : X ⟶ Y) :
    (forget₂ (AlgCat.{v} R) (ModuleCat.{v} R)).map f = ModuleCat.ofHom f.hom.toLinearMap :=
  rfl

/-- The "free algebra" functor, sending a type `S` to the free algebra on `S`. -/
@[simps! obj map]
def free : Type u ⥤ AlgCat.{u} R where
  obj S := of R (FreeAlgebra R S)
  map f := ofHom <| FreeAlgebra.lift _ <| FreeAlgebra.ι _ ∘ f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The free/forget adjunction for `R`-algebras. -/
def adj : free.{u} R ⊣ forget (AlgCat.{u} R) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := fun f ↦ ↾((FreeAlgebra.lift _).symm f.hom)
          invFun := fun f ↦ ofHom <| (FreeAlgebra.lift _) f
          left_inv := fun f ↦ by aesop
          right_inv := fun f ↦ by aesop } }

instance : (forget (AlgCat.{u} R)).IsRightAdjoint := (adj R).isRightAdjoint

end AlgCat

variable {R}
variable {X₁ X₂ : Type v}

/-- Build an isomorphism in the category `AlgCat R` from an `AlgEquiv` between `Algebra`s. -/
@[simps]
def AlgEquiv.toAlgebraIso {g₁ : Ring X₁} {g₂ : Ring X₂} {m₁ : Algebra R X₁} {m₂ : Algebra R X₂}
    (e : X₁ ≃ₐ[R] X₂) : AlgCat.of R X₁ ≅ AlgCat.of R X₂ where
  hom := AlgCat.ofHom (e : X₁ →ₐ[R] X₂)
  inv := AlgCat.ofHom (e.symm : X₂ →ₐ[R] X₁)

namespace CategoryTheory.Iso

/-- Build an `AlgEquiv` from an isomorphism in the category `AlgCat R`. -/
@[simps]
def toAlgEquiv {X Y : AlgCat.{v} R} (i : X ≅ Y) : X ≃ₐ[R] Y :=
  { i.hom.hom with
    toFun := i.hom
    invFun := i.inv
    left_inv := fun x ↦ by simp
    right_inv := fun x ↦ by simp }

end CategoryTheory.Iso

/-- Algebra equivalences between `Algebra`s are the same as (isomorphic to) isomorphisms in
`AlgCat`. -/
@[simps]
def algEquivIsoAlgebraIso {X Y : Type v} [Ring X] [Ring Y] [Algebra R X] [Algebra R Y] :
    (X ≃ₐ[R] Y) ≅ (AlgCat.of R X ≅ AlgCat.of R Y) where
  hom := ↾fun e ↦ e.toAlgebraIso
  inv := ↾fun i ↦ i.toAlgEquiv

instance AlgCat.forget_reflects_isos : (forget (AlgCat.{v} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (AlgCat.{v} R)).map f)
    let e : X ≃ₐ[R] Y := { f.hom, i.toEquiv with }
    exact e.toAlgebraIso.isIso_hom

namespace AlgCat

/-- The restriction of scalars functor `AlgCat S ⥤ AlgCat R` induced by a ring homomorphism
`R →+* S`. -/
@[simps]
def restrictScalars {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    AlgCat.{v} S ⥤ AlgCat.{v} R where
  obj A :=
    letI : Algebra R A := Algebra.compHom _ f
    AlgCat.of R A
  map {A B} g :=
    letI : Algebra R A := Algebra.compHom _ f
    letI : Algebra R B := Algebra.compHom _ f
    letI : Algebra R S := f.toAlgebra
    haveI : IsScalarTower R S A := .of_algebraMap_eq' rfl
    haveI : IsScalarTower R S B := .of_algebraMap_eq' rfl
    AlgCat.ofHom (g.hom.restrictScalars _)

-- The option makes `simps` produce the correct lemmas
set_option backward.isDefEq.respectTransparency false in
/-- Restricting scalars along the identity is isomorphic to the identity. -/
@[simps!]
def restrictScalarsId' {R : Type*} [CommRing R] (f : R →+* R) (hf : f = .id R) :
    AlgCat.restrictScalars.{v} f ≅ 𝟭 _ :=
  NatIso.ofComponents
    fun A ↦ AlgEquiv.toAlgebraIso <|
      @AlgEquiv.ofRingEquiv (f := RingEquiv.refl _) _ _ _ _ _ _
        ((restrictScalars f).obj A).isAlgebra _ fun _ ↦ by subst hf; rfl

-- The option makes `simps` produce the correct lemmas
set_option backward.isDefEq.respectTransparency false in
/-- Restricting scalars along a composition is isomorphic to the composition
of restriction of scalars. -/
@[simps!]
def restrictScalarsComp' {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S)
      (g : S →+* T) (gf : R →+* T) (hfg : gf = g.comp f) :
    AlgCat.restrictScalars.{v} gf ≅
      AlgCat.restrictScalars.{v} g ⋙ AlgCat.restrictScalars.{v} f :=
  NatIso.ofComponents
    fun A ↦ AlgEquiv.toAlgebraIso <|
      @AlgEquiv.ofRingEquiv (f := RingEquiv.refl _) _ _ _ _ _ _
        ((restrictScalars gf).obj A).isAlgebra
        ((restrictScalars f).obj ((restrictScalars g).obj A)).isAlgebra
        fun _ ↦ by subst hfg; rfl

/-- A ring isomorphism induces an equivalence of categories of algebras. -/
@[simps]
def restrictScalarsEquivalenceOfRingEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    AlgCat.{u} S ≌ AlgCat.{u} R where
  functor := restrictScalars e.toRingHom
  inverse := restrictScalars e.symm.toRingHom
  unitIso := (restrictScalarsId' _ rfl).symm ≪≫
    restrictScalarsComp' _ _ _ e.toRingHom_comp_symm_toRingHom.symm
  counitIso := (restrictScalarsComp' _ _ _ e.symm_toRingHom_comp_toRingHom.symm).symm ≪≫
    restrictScalarsId' _ rfl

instance {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    (restrictScalars e.toRingHom).IsEquivalence :=
  inferInstanceAs <| (restrictScalarsEquivalenceOfRingEquiv e).functor.IsEquivalence

instance {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    (restrictScalars e.symm.toRingHom).IsEquivalence :=
  inferInstanceAs <| (restrictScalarsEquivalenceOfRingEquiv e).inverse.IsEquivalence

/-- The equivalence of categories of `ℤ`-algebras and rings. -/
@[simps! (dsimpLhs := true) functor inverse_obj inverse_map_hom unitIso_hom_app_hom_apply counitIso]
def intEquivalence : AlgCat.{u} ℤ ≌ RingCat.{u} where
  functor := forget₂ _ _
  inverse.obj A := AlgCat.of ℤ A
  inverse.map f := AlgCat.ofHom f.hom.toIntAlgHom
  unitIso := NatIso.ofComponents
    fun A ↦ AlgEquiv.toAlgebraIso (@.ofRingEquiv (f := RingEquiv.refl _)
      _ _ _ _ _ _ _ (Ring.toIntAlgebra _) fun _ ↦ by simp)
  counitIso := Iso.refl _

instance : (forget₂ (AlgCat.{u} ℤ) RingCat.{u}).IsEquivalence :=
  inferInstanceAs <| intEquivalence.functor.IsEquivalence

end AlgCat
