/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Category instance for algebras over a commutative ring

We introduce the bundled category `AlgebraCat` of algebras over a fixed commutative ring `R` along
with the forgetful functors to `RingCat` and `ModuleCat`. We furthermore show that the functor
associating to a type the free `R`-algebra on that type is left adjoint to the forgetful functor.
-/


open CategoryTheory Limits

universe v u

variable (R : Type u) [CommRing R]

/-- The category of R-algebras and their morphisms. -/
structure AlgebraCat where
  carrier : Type v
  [isRing : Ring carrier]
  [isAlgebra : Algebra R carrier]

-- Porting note: typemax hack to fix universe complaints
/-- An alias for `AlgebraCat.{max u₁ u₂}`, to deal around unification issues.
Since the universe the ring lives in can be inferred, we put that last. -/
@[nolint checkUnivs]
abbrev AlgebraCatMax.{v₁, v₂, u₁} (R : Type u₁) [CommRing R] := AlgebraCat.{max v₁ v₂} R

attribute [instance] AlgebraCat.isRing AlgebraCat.isAlgebra

initialize_simps_projections AlgebraCat (-isRing, -isAlgebra)

namespace AlgebraCat

instance : CoeSort (AlgebraCat R) (Type v) :=
  ⟨AlgebraCat.carrier⟩

attribute [coe] AlgebraCat.carrier

variable {R} in
@[ext]
structure Hom (A B : AlgebraCat.{v} R) where
  algHom : A →ₐ[R] B

instance : Category (AlgebraCat.{v} R) where
  Hom A B := Hom A B
  id A := ⟨AlgHom.id R A⟩
  comp f g := ⟨g.algHom.comp f.algHom⟩

@[simp]
lemma algHom_id {A : AlgebraCat.{v} R} : (𝟙 A : A ⟶ A).algHom = AlgHom.id R A := rfl

@[simp]
lemma algHom_comp {A B C : AlgebraCat.{v} R} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).algHom = g.algHom.comp f.algHom := rfl

@[ext]
lemma hom_ext {A B : AlgebraCat.{v} R} {f g : A ⟶ B} (hf : f.algHom = g.algHom) : f = g :=
  Hom.ext hf

instance {M N : AlgebraCat.{v} R} : FunLike (M ⟶ N) M N where
  coe f := f.algHom
  coe_injective' f g h := by
    ext : 1
    simpa using h

@[simp]
lemma coe_algHom {M N : AlgebraCat.{v} R} (f : M ⟶ N) : ⇑f.algHom = ⇑f := rfl

instance {M N : AlgebraCat.{v} R} : AlgHomClass (M ⟶ N) R M N where
  map_mul f := map_mul f.algHom
  map_one f := map_one f.algHom
  map_add f := map_add f.algHom
  map_zero f := map_zero f.algHom
  commutes f := f.algHom.commutes

instance : ConcreteCategory.{v} (AlgebraCat.{v} R) where
  forget :=
    { obj := fun R => R
      map := fun f => f.algHom }
  forget_faithful := ⟨fun h => by ext x; simpa using congrFun h x⟩

@[simp]
lemma forget_obj {A : AlgebraCat.{v} R} : (forget _).obj A = A := rfl

@[simp]
lemma forget_map {A B : AlgebraCat.{v} R} (f : A ⟶ B) :
    (forget _).map f = f :=
  rfl

instance {S : AlgebraCat.{v} R} : Ring ((forget (AlgebraCat R)).obj S) :=
  (inferInstance : Ring S.carrier)

instance {S : AlgebraCat.{v} R} : Algebra R ((forget (AlgebraCat R)).obj S) :=
  (inferInstance : Algebra R S.carrier)

instance hasForgetToRing : HasForget₂ (AlgebraCat.{v} R) RingCat.{v} where
  forget₂ :=
    { obj := fun A => RingCat.of A
      map := fun f => RingCat.ofHom f.algHom.toRingHom }

instance hasForgetToModule : HasForget₂ (AlgebraCat.{v} R) (ModuleCat.{v} R) where
  forget₂ :=
    { obj := fun M => ModuleCat.of R M
      map := fun f => ModuleCat.asHom f.algHom.toLinearMap }

@[simp]
lemma forget₂_module_obj (X : AlgebraCat.{v} R) :
    (forget₂ (AlgebraCat.{v} R) (ModuleCat.{v} R)).obj X = ModuleCat.of R X :=
  rfl

@[simp]
lemma forget₂_module_map {X Y : AlgebraCat.{v} R} (f : X ⟶ Y) :
    (forget₂ (AlgebraCat.{v} R) (ModuleCat.{v} R)).map f = ModuleCat.asHom f.algHom.toLinearMap :=
  rfl

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. -/
def of (X : Type v) [Ring X] [Algebra R X] : AlgebraCat.{v} R :=
  ⟨X⟩

/-- Typecheck a `AlgHom` as a morphism in `AlgebraCat R`. -/
def ofHom {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [Algebra R X] [Ring Y] [Algebra R Y]
    (f : X →ₐ[R] Y) : of R X ⟶ of R Y :=
  ⟨f⟩

@[simp]
lemma algHom_ofHom {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [Algebra R X] [Ring Y]
    [Algebra R Y] (f : X →ₐ[R] Y) : (ofHom f).algHom = f := rfl

@[simp]
lemma ofHom_algHom {A B : AlgebraCat.{v} R} (f : A ⟶ B) :
    @ofHom _ _ no_index _ no_index _ _ _ _ _ (Hom.algHom f) = f := rfl

@[simp]
lemma ofHom_id {X : Type v} [Ring X] [Algebra R X] : ofHom (AlgHom.id R X) = 𝟙 (of R X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type v} [Ring X] [Ring Y] [Ring Z] [Algebra R X] [Algebra R Y]
    [Algebra R Z] (f : X →ₐ[R] Y) (g : Y →ₐ[R] Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

@[simp]
theorem ofHom_apply {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [Algebra R X] [Ring Y]
    [Algebra R Y] (f : X →ₐ[R] Y) (x : X) : ofHom f x = f x :=
  rfl

instance : Inhabited (AlgebraCat R) :=
  ⟨of R R⟩

@[simp]
theorem coe_of (X : Type u) [Ring X] [Algebra R X] : (of R X : Type u) = X :=
  rfl

variable {R}

/-- Forgetting to the underlying type and then building the bundled object returns the original
algebra. -/
@[simps]
def ofSelfIso (M : AlgebraCat.{v} R) : AlgebraCat.of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

variable {M N U : AlgebraCat.{v} R}

@[simp]
theorem id_apply (m : M) : (𝟙 M : M → M) m = m :=
  rfl

@[simp]
theorem coe_comp (f : M ⟶ N) (g : N ⟶ U) : (f ≫ g : M → U) = g ∘ f :=
  rfl

variable (R)

/-- The "free algebra" functor, sending a type `S` to the free algebra on `S`. -/
@[simps! obj map]
def free : Type u ⥤ AlgebraCat.{u} R where
  obj S := of R (FreeAlgebra R S)
  map f := ofHom <| FreeAlgebra.lift _ <| FreeAlgebra.ι _ ∘ f
  -- Porting note (#11041): `apply FreeAlgebra.hom_ext` was `ext1`.
  map_id X := by
    ext : 1
    apply FreeAlgebra.hom_ext
    ext
    simp
  map_comp {X Y Z} f g := by
  -- Porting note (#11041): `apply FreeAlgebra.hom_ext` was `ext1`.
    ext : 1
    apply FreeAlgebra.hom_ext
    ext
    simp

/-- The free/forget adjunction for `R`-algebras. -/
def adj : free.{u} R ⊣ forget (AlgebraCat.{u} R) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := fun f ↦ (FreeAlgebra.lift _).symm f.algHom
          invFun := fun f ↦ ofHom <| (FreeAlgebra.lift _) f
          left_inv := fun f ↦ by simp
          right_inv := fun f ↦ by simp
        }
      homEquiv_naturality_left_symm := by
        intros
        ext : 1
        apply FreeAlgebra.hom_ext
        ext
        simp
      homEquiv_naturality_right := by
        intros
        ext
        simp }

instance : (forget (AlgebraCat.{u} R)).IsRightAdjoint := (adj R).isRightAdjoint

end AlgebraCat

variable {R}
variable {X₁ X₂ : Type u}

/-- Build an isomorphism in the category `AlgebraCat R` from a `AlgEquiv` between `Algebra`s. -/
@[simps]
def AlgEquiv.toAlgebraIso {g₁ : Ring X₁} {g₂ : Ring X₂} {m₁ : Algebra R X₁} {m₂ : Algebra R X₂}
    (e : X₁ ≃ₐ[R] X₂) : AlgebraCat.of R X₁ ≅ AlgebraCat.of R X₂ where
  hom := AlgebraCat.ofHom (e : X₁ →ₐ[R] X₂)
  inv := AlgebraCat.ofHom (e.symm : X₂ →ₐ[R] X₁)
  hom_inv_id := by ext x; exact e.left_inv x
  inv_hom_id := by ext x; exact e.right_inv x

namespace CategoryTheory.Iso

/-- Build a `AlgEquiv` from an isomorphism in the category `AlgebraCat R`. -/
@[simps]
def toAlgEquiv {X Y : AlgebraCat R} (i : X ≅ Y) : X ≃ₐ[R] Y :=
  { i.hom.algHom with
    toFun := i.hom
    invFun := i.inv
    left_inv := fun x => by
      -- Porting note: was `by tidy`
      change (i.hom ≫ i.inv) x = x
      simp
    right_inv := fun x => by
      -- Porting note: was `by tidy`
      change (i.inv ≫ i.hom) x = x
      simp }

end CategoryTheory.Iso

/-- Algebra equivalences between `Algebra`s are the same as (isomorphic to) isomorphisms in
`AlgebraCat`. -/
@[simps]
def algEquivIsoAlgebraIso {X Y : Type u} [Ring X] [Ring Y] [Algebra R X] [Algebra R Y] :
    (X ≃ₐ[R] Y) ≅ AlgebraCat.of R X ≅ AlgebraCat.of R Y where
  hom e := e.toAlgebraIso
  inv i := i.toAlgEquiv

instance AlgebraCat.forget_reflects_isos : (forget (AlgebraCat.{u} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (AlgebraCat.{u} R)).map f)
    let e : X ≃ₐ[R] Y := { f.algHom, i.toEquiv with }
    exact e.toAlgebraIso.isIso_hom
