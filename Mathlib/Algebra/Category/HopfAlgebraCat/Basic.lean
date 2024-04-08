/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert A. Spencer, Markus Himmel, Amelia Livingston
-/
import Mathlib.Algebra.Category.BialgebraCat.Basic
import Mathlib.RingTheory.HopfAlgebra

/-!
# The category of Hopf `R`-algebras

`HopfAlgebraCat.{v} R` is the category of bundled Hopf `R`-algebras with carrier in the universe v.

This file simply mimics `Mathlib.Algebra.Category.ModuleCat.Basic`.

-/

universe v u

variable (R : Type u) [CommRing R]

/-- Objects in the category of Hopf `R`-algebras. -/
structure HopfAlgebraCat where
  /-- the underlying type of an object in `HopfAlgebraCat R` -/
  carrier : Type v
  [isRing : Ring carrier]
  [isHopfAlgebra : HopfAlgebra R carrier]

attribute [instance] HopfAlgebraCat.isRing HopfAlgebraCat.isHopfAlgebra

/-- An alias for `HopfAlgebraCat.{max u₁ u₂}`, to deal around unification issues.
Since the universe the ring lives in can be inferred, we put that last. -/
@[nolint checkUnivs]
abbrev HopfAlgebraCatMax.{v₁, v₂, u₁} (R : Type u₁) [CommRing R] := HopfAlgebraCat.{max v₁ v₂, u₁} R

namespace HopfAlgebraCat
open CategoryTheory CategoryTheory.Limits

instance : CoeSort (HopfAlgebraCat.{v} R) (Type v) :=
  ⟨HopfAlgebraCat.carrier⟩

attribute [coe] HopfAlgebraCat.carrier

instance HopfAlgebraCategory : Category.{v, max (v+1) u} (HopfAlgebraCat.{v} R) where
  Hom M N := M →ₐc[R] N
  id _ := BialgHom.id R _
  comp f g := g.comp f

instance {M N : HopfAlgebraCat.{v} R} : FunLike (M ⟶ N) M N :=
  inferInstanceAs (FunLike (M →ₐc[R] N) M N)

instance {M N : HopfAlgebraCat.{v} R} : BialgHomClass (M ⟶ N) R M N :=
  BialgHom.bialgHomClass

instance hopfAlgebraConcreteCategory : ConcreteCategory.{v} (HopfAlgebraCat.{v} R) where
  forget :=
    { obj := fun R => R
      map := fun f => f }
  forget_faithful := ⟨fun h => BialgHom.ext (fun x => by
    dsimp at h
    rw [h])⟩

-- how necessary are all these?
instance {M : HopfAlgebraCat.{v} R} : Ring ((forget (HopfAlgebraCat R)).obj M) :=
  (inferInstance : Ring M)
instance {M : HopfAlgebraCat.{v} R} : Module R ((forget (HopfAlgebraCat R)).obj M) :=
  (inferInstance : Module R M)
instance {M : HopfAlgebraCat.{v} R} : Algebra R ((forget (HopfAlgebraCat R)).obj M) :=
  (inferInstance : Algebra R M)
instance {M : HopfAlgebraCat.{v} R} : Coalgebra R ((forget (HopfAlgebraCat R)).obj M) :=
  (inferInstance : Coalgebra R M)
instance {M : HopfAlgebraCat.{v} R} : Bialgebra R ((forget (HopfAlgebraCat R)).obj M) :=
  (inferInstance : Bialgebra R M)
instance {M : HopfAlgebraCat.{v} R} : HopfAlgebra R ((forget (HopfAlgebraCat R)).obj M) :=
  (inferInstance : HopfAlgebra R M)

@[ext]
lemma ext {M N : HopfAlgebraCat.{v} R} {f₁ f₂ : M ⟶ N} (h : ∀ (x : M), f₁ x = f₂ x) : f₁ = f₂ :=
  DFunLike.ext _ _ h

instance hasForgetToBialgebra : HasForget₂ (HopfAlgebraCat R) (BialgebraCat R) where
  forget₂ :=
    { obj := fun M => BialgebraCat.of R M
      map := fun f => BialgebraCat.ofHom f }

instance hasForgetToCoalgebra : HasForget₂ (HopfAlgebraCat R) (CoalgebraCat R) where
  forget₂ :=
    { obj := fun M => CoalgebraCat.of R M
      map := fun f => CoalgebraCat.ofHom f }

instance hasForgetToAlgebra : HasForget₂ (HopfAlgebraCat R) (AlgebraCat R) where
  forget₂ :=
    { obj := fun M => AlgebraCat.of R M
      map := fun f => AlgebraCat.ofHom f }

instance hasForgetToModule : HasForget₂ (HopfAlgebraCat R) (ModuleCat R) where
  forget₂ :=
    { obj := fun M => ModuleCat.of R M
      map := fun f => ModuleCat.ofHom f }

instance hasForgetToRing : HasForget₂ (HopfAlgebraCat R) RingCat where
  forget₂ :=
    { obj := fun M => RingCat.of M
      map := fun f => RingCat.ofHom f }

/-- The object in the category of Hopf R-algebras associated to an Hopf R-algebra. -/
def of (X : Type v) [Ring X] [HopfAlgebra R X] : HopfAlgebraCat R :=
  ⟨X⟩

@[simp]
theorem forget₂_bialgebraCat_obj (X : HopfAlgebraCat R) :
    (forget₂ (HopfAlgebraCat R) (BialgebraCat R)).obj X = BialgebraCat.of R X :=
  rfl

@[simp]
theorem forget₂_algebraCat_obj (X : HopfAlgebraCat R) :
    (forget₂ (HopfAlgebraCat R) (AlgebraCat R)).obj X = AlgebraCat.of R X :=
  rfl

@[simp]
theorem forget₂_coalgebraCat_obj (X : HopfAlgebraCat R) :
    (forget₂ (HopfAlgebraCat R) (CoalgebraCat R)).obj X = CoalgebraCat.of R X :=
  rfl

@[simp]
theorem bialgebraCat_of_of (X : Type v) [Ring X]
    [HopfAlgebra R X] :
    BialgebraCat.of R (of R X) = BialgebraCat.of R X :=
  rfl

@[simp]
theorem algebraCat_of_of (X : Type v) [Ring X]
    [HopfAlgebra R X] :
    AlgebraCat.of R (of R X) = AlgebraCat.of R X :=
  rfl

@[simp]
theorem CoalgebraCat_of_of (X : Type v) [Ring X]
    [HopfAlgebra R X] :
    CoalgebraCat.of R (of R X) = CoalgebraCat.of R X :=
  rfl

@[simp]
theorem forget₂_bialgebraCat_map (X Y : HopfAlgebraCat R) (f : X ⟶ Y) :
    (forget₂ (HopfAlgebraCat R) (BialgebraCat R)).map f = f :=
  rfl

@[simp]
theorem forget₂_algebraCat_map (X Y : HopfAlgebraCat R) (f : X ⟶ Y) :
    (forget₂ (HopfAlgebraCat R) (AlgebraCat R)).map f = (f : X →ₐ[R] Y) :=
  rfl

@[simp]
theorem forget₂_coalgebraCat_map (X Y : HopfAlgebraCat R) (f : X ⟶ Y) :
    (forget₂ (HopfAlgebraCat R) (CoalgebraCat R)).map f = (f : X →ₗc[R] Y) :=
  rfl

/-- Typecheck a `BialgHom` as a morphism in `HopfAlgebraCat R`. -/
def ofHom {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [HopfAlgebra R X]
    [Ring Y] [HopfAlgebra R Y] (f : X →ₐc[R] Y) : of R X ⟶ of R Y :=
  f

@[simp 1100]
theorem ofHom_apply {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [HopfAlgebra R X]
    [Ring Y] [HopfAlgebra R Y] (f : X →ₐc[R] Y) (x : X) : ofHom f x = f x :=
  rfl

instance ofUnique {X : Type v} [Ring X] [HopfAlgebra R X] [i : Unique X] : Unique (of R X) :=
  i

variable {R}

/-- Forgetting to the underlying type and then building the bundled object returns the original
Hopf algebra. -/
@[simps]
def ofSelfIso (M : HopfAlgebraCat R) : HopfAlgebraCat.of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

variable {M N U : HopfAlgebraCat.{v} R}

@[simp]
theorem id_apply (m : M) : (𝟙 M : M → M) m = m :=
  rfl

@[simp]
theorem coe_comp (f : M ⟶ N) (g : N ⟶ U) : (f ≫ g : M → U) = g ∘ f :=
  rfl

theorem comp_def (f : M ⟶ N) (g : N ⟶ U) : f ≫ g = g.comp f :=
  rfl

@[simp] lemma forget_map (f : M ⟶ N) : (forget (HopfAlgebraCat R)).map f = (f : M → N) := rfl

end HopfAlgebraCat

variable {R}

variable {X₁ X₂ : Type v}

section

/-- Build an isomorphism in the category `HopfAlgebraCat R` from a `BialgEquiv`
between Hopf algebras. -/
@[simps]
def BialgEquiv.toHopfAlgebraIso {g₁ : Ring X₁} {g₂ : Ring X₂}
    {c₁ : HopfAlgebra R X₁} {c₂ : HopfAlgebra R X₂} (e : X₁ ≃ₐc[R] X₂) :
    HopfAlgebraCat.of R X₁ ≅ HopfAlgebraCat.of R X₂ where
  hom := (e : X₁ →ₐc[R] X₂)
  inv := (e.symm : X₂ →ₐc[R] X₁)
  hom_inv_id := by ext; apply e.left_inv
  inv_hom_id := by ext; apply e.right_inv

/-- Build an isomorphism in the category `HopfAlgebraCat R` from a `BialgEquiv`
between Hopf algebras. -/
abbrev BialgEquiv.toHopfAlgebraIso' {M N : HopfAlgebraCat.{v} R} (i : M ≃ₐc[R] N) : M ≅ N :=
  i.toHopfAlgebraIso

/-- Build an isomorphism in the category `HopfAlgebraCat R` from a `BialgEquiv`
between Hopf algebras. -/
abbrev BialgEquiv.toHopfAlgebraIso'Left
    {X₁ : HopfAlgebraCat.{v} R} [Ring X₂] [HopfAlgebra R X₂]
    (e : X₁ ≃ₐc[R] X₂) : X₁ ≅ HopfAlgebraCat.of R X₂ :=
  e.toHopfAlgebraIso

/-- Build an isomorphism in the category `HopfAlgebraCat R` from a `BialgEquiv`
between Hopf algebras. -/
abbrev BialgEquiv.toHopfAlgebraIso'Right
    [Ring X₁] [HopfAlgebra R X₁] {X₂ : HopfAlgebraCat.{v} R}
    (e : X₁ ≃ₐc[R] X₂) : HopfAlgebraCat.of R X₁ ≅ X₂ :=
  e.toHopfAlgebraIso

namespace CategoryTheory.Iso

/-- Build a `BialgEquiv` from an isomorphism in the category `HopfAlgebraCat R`. -/
def toBialgEquiv' {X Y : HopfAlgebraCat R} (i : X ≅ Y) : X ≃ₐc[R] Y :=
  { i.hom with
    invFun := i.inv
    left_inv := fun x => BialgHom.congr_fun i.3 x
    right_inv := fun x => BialgHom.congr_fun i.4 x }

@[simp]
theorem toBialgEquiv'_apply {X Y : HopfAlgebraCat R} (i : X ≅ Y) (x : X) :
    i.toBialgEquiv' x = i.hom x :=
  rfl

@[simp]
theorem toBialgEquiv'_toBialgHom {X Y : HopfAlgebraCat R} (i : X ≅ Y) :
    (i.toBialgEquiv' : X →ₐc[R] Y) = i.hom :=
  rfl

@[simp]
theorem toBialgEquiv'_symm_toBialgHom {X Y : HopfAlgebraCat R} (i : X ≅ Y) :
    (i.toBialgEquiv'.symm : Y →ₐc[R] X) = i.inv :=
  rfl

end CategoryTheory.Iso

/-- Bialgebra equivalences of Hopf algebras are the same as (isomorphic to) isomorphisms
in `HopfAlgebraCat R` -/
@[simps]
def bialgEquivIsoHopfAlgebraIso {X Y : Type u} [Ring X] [Ring Y]
    [HopfAlgebra R X] [HopfAlgebra R Y] :
    (X ≃ₐc[R] Y) ≅ HopfAlgebraCat.of R X ≅ HopfAlgebraCat.of R Y where
  hom e := e.toHopfAlgebraIso
  inv i := i.toBialgEquiv'

end
