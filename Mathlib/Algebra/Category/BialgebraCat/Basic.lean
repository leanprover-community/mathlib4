/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert A. Spencer, Markus Himmel, Amelia Livingston
-/
import Mathlib.RingTheory.Bialgebra.Equiv
import Mathlib.Algebra.Category.CoalgebraCat.Basic
import Mathlib.Algebra.Category.AlgebraCat.Basic

/-!
# The category of `R`-bialgebras

`BialgebraCat.{v} R` is the category of bundled `R`-bialgebras with carrier in the universe v.

This file simply mimics `Mathlib.Algebra.Category.ModuleCat.Basic`.

-/

universe v u

variable (R : Type u) [CommRing R]

/-- Objects in the category of `R`-bialgebras. -/
structure BialgebraCat where
  /-- the underlying type of an object in `BialgebraCat R` -/
  carrier : Type v
  [isRing : Ring carrier]
  [isBialgebra : Bialgebra R carrier]

attribute [instance] BialgebraCat.isRing BialgebraCat.isBialgebra

/-- An alias for `BialgebraCat.{max u₁ u₂}`, to deal around unification issues.
Since the universe the ring lives in can be inferred, we put that last. -/
@[nolint checkUnivs]
abbrev BialgebraCatMax.{v₁, v₂, u₁} (R : Type u₁) [CommRing R] := BialgebraCat.{max v₁ v₂, u₁} R

namespace BialgebraCat
open CategoryTheory CategoryTheory.Limits

instance : CoeSort (BialgebraCat.{v} R) (Type v) :=
  ⟨BialgebraCat.carrier⟩

attribute [coe] BialgebraCat.carrier

instance BialgebraCategory : Category.{v, max (v+1) u} (BialgebraCat.{v} R) where
  Hom M N := M →ₐc[R] N
  id _ := BialgHom.id R _
  comp f g := g.comp f
  id_comp _ := BialgHom.id_comp _
  comp_id _ := BialgHom.comp_id _
  assoc f g h := BialgHom.comp_assoc h g f

instance {M N : BialgebraCat.{v} R} : FunLike (M ⟶ N) M N :=
  inferInstanceAs (FunLike (M →ₐc[R] N) M N)

instance {M N : BialgebraCat.{v} R} : BialgHomClass (M ⟶ N) R M N :=
  BialgHom.bialgHomClass

instance bialgConcreteCategory : ConcreteCategory.{v} (BialgebraCat.{v} R) where
  forget :=
    { obj := fun R => R
      map := fun f => f }
  forget_faithful := ⟨fun h => BialgHom.ext (fun x => by
    dsimp at h
    rw [h])⟩

-- Porting note:
-- One might hope these two instances would not be needed,
-- as we already have `Ring M` and `Module R M`,
-- but sometimes we seem to need these when rewriting by lemmas about generic concrete categories.
instance {M : BialgebraCat.{v} R} : Ring ((forget (BialgebraCat R)).obj M) :=
  (inferInstance : Ring M)
instance {M : BialgebraCat.{v} R} : Module R ((forget (BialgebraCat R)).obj M) :=
  (inferInstance : Module R M)
instance {M : BialgebraCat.{v} R} : Algebra R ((forget (BialgebraCat R)).obj M) :=
  (inferInstance : Algebra R M)
instance {M : BialgebraCat.{v} R} : Coalgebra R ((forget (BialgebraCat R)).obj M) :=
  (inferInstance : Coalgebra R M)
instance {M : BialgebraCat.{v} R} : Bialgebra R ((forget (BialgebraCat R)).obj M) :=
  (inferInstance : Bialgebra R M)

@[ext]
lemma ext {M N : BialgebraCat.{v} R} {f₁ f₂ : M ⟶ N} (h : ∀ (x : M), f₁ x = f₂ x) : f₁ = f₂ :=
  DFunLike.ext _ _ h

instance hasForgetToCoalgebra : HasForget₂ (BialgebraCat R) (CoalgebraCat R) where
  forget₂ :=
    { obj := fun M => CoalgebraCat.of R M
      map := fun f => CoalgebraCat.ofHom f }

instance hasForgetToAlgebra : HasForget₂ (BialgebraCat R) (AlgebraCat R) where
  forget₂ :=
    { obj := fun M => AlgebraCat.of R M
      map := fun f => AlgebraCat.ofHom f }

instance hasForgetToModule : HasForget₂ (BialgebraCat R) (ModuleCat R) where
  forget₂ :=
    { obj := fun M => ModuleCat.of R M
      map := fun f => ModuleCat.ofHom f }

instance hasForgetToRing : HasForget₂ (BialgebraCat R) RingCat where
  forget₂ :=
    { obj := fun M => RingCat.of M
      map := fun f => RingCat.ofHom f }

/-- The object in the category of R-bialgebras associated to an R-bialgebra. -/
def of (X : Type v) [Ring X]  [Bialgebra R X] : BialgebraCat R :=
  ⟨X⟩

@[simp]
theorem forget₂_coalgebraCat_obj (X : BialgebraCat R) :
    (forget₂ (BialgebraCat R) (CoalgebraCat R)).obj X = CoalgebraCat.of R X :=
  rfl

@[simp]
theorem forget₂_algebraCat_obj (X : BialgebraCat R) :
    (forget₂ (BialgebraCat R) (AlgebraCat R)).obj X = AlgebraCat.of R X :=
  rfl

@[simp]
theorem coalgebraCat_of_of (X : Type v) [Ring X]
    [Bialgebra R X] :
    CoalgebraCat.of R (of R X) = CoalgebraCat.of R X :=
  rfl

@[simp]
theorem algebraCat_of_of (X : Type v) [Ring X]
    [Bialgebra R X] :
    AlgebraCat.of R (of R X) = AlgebraCat.of R X :=
  rfl

@[simp]
theorem forget₂_coalgebraCat_map (X Y : BialgebraCat R) (f : X ⟶ Y) :
    (forget₂ (BialgebraCat R) (CoalgebraCat R)).map f = (f : X →ₗc[R] Y) :=
  rfl

@[simp]
theorem forget₂_algebraCat_map (X Y : BialgebraCat R) (f : X ⟶ Y) :
    (forget₂ (BialgebraCat R) (AlgebraCat R)).map f = (f : X →ₐ[R] Y) :=
  rfl

/-- Typecheck a `BialgHom` as a morphism in `BialgebraCat R`. -/
def ofHom {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [Bialgebra R X]
    [Ring Y] [Bialgebra R Y] (f : X →ₐc[R] Y) : of R X ⟶ of R Y :=
  f

@[simp 1100]
theorem ofHom_apply {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [Bialgebra R X]
    [Ring Y] [Bialgebra R Y] (f : X →ₐc[R] Y) (x : X) : ofHom f x = f x :=
  rfl

instance ofUnique {X : Type v} [Ring X] [Bialgebra R X] [i : Unique X] : Unique (of R X) :=
  i

/-
-- Porting note: the simpNF linter complains, but we really need this?!
-- @[simp, nolint simpNF]
theorem coe_of (X : Type v) [Ring X] [Bialgebra R X] : (of R X : Type v) = X :=
  rfl
-/

variable {R}

/-- Forgetting to the underlying type and then building the bundled object returns the original
bialgebra. -/
@[simps]
def ofSelfIso (M : BialgebraCat R) : BialgebraCat.of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

variable {M N U : BialgebraCat.{v} R}

@[simp]
theorem id_apply (m : M) : (𝟙 M : M → M) m = m :=
  rfl

@[simp]
theorem coe_comp (f : M ⟶ N) (g : N ⟶ U) : (f ≫ g : M → U) = g ∘ f :=
  rfl

theorem comp_def (f : M ⟶ N) (g : N ⟶ U) : f ≫ g = g.comp f :=
  rfl

@[simp] lemma forget_map (f : M ⟶ N) : (forget (BialgebraCat R)).map f = (f : M → N) := rfl

end BialgebraCat

variable {R}

variable {X₁ X₂ : Type v}

section

/-- Build an isomorphism in the category `BialgebraCat R` from a `BialgEquiv`
between bialgebras. -/
@[simps]
def BialgEquiv.toBialgIso {g₁ : Ring X₁} {g₂ : Ring X₂}
      {c₁ : Bialgebra R X₁} {c₂ : Bialgebra R X₂} (e : X₁ ≃ₐc[R] X₂) :
      BialgebraCat.of R X₁ ≅ BialgebraCat.of R X₂ where
  hom := (e : X₁ →ₐc[R] X₂)
  inv := (e.symm : X₂ →ₐc[R] X₁)
  hom_inv_id := by ext; apply e.left_inv
  inv_hom_id := by ext; apply e.right_inv

/-- Build an isomorphism in the category `BialgebraCat R` from a `BialgEquiv`
between bialgebras. -/
abbrev BialgEquiv.toBialgIso' {M N : BialgebraCat.{v} R} (i : M ≃ₐc[R] N) : M ≅ N :=
  i.toBialgIso

/-- Build an isomorphism in the category `BialgebraCat R` from a `BialgEquiv`
between bialgebras. -/
abbrev BialgEquiv.toBialgIso'Left {X₁ : BialgebraCat.{v} R} [Ring X₂] [Module R X₂] [Bialgebra R X₂]
    (e : X₁ ≃ₐc[R] X₂) : X₁ ≅ BialgebraCat.of R X₂ :=
  e.toBialgIso

/-- Build an isomorphism in the category `BialgebraCat R` from a `BialgEquiv`
between bialgebras. -/
abbrev BialgEquiv.toBialgIso'Right [Ring X₁] [Module R X₁] [Bialgebra R X₁] {X₂ : BialgebraCat.{v} R}
    (e : X₁ ≃ₐc[R] X₂) : BialgebraCat.of R X₁ ≅ X₂ :=
  e.toBialgIso

namespace CategoryTheory.Iso

/-- Build a `BialgEquiv` from an isomorphism in the category `BialgebraCat R`. -/
def toBialgEquiv {X Y : BialgebraCat R} (i : X ≅ Y) : X ≃ₐc[R] Y :=
  { i.hom with
    invFun := i.inv
    left_inv := fun x => BialgHom.congr_fun i.3 x
    right_inv := fun x => BialgHom.congr_fun i.4 x }

@[simp]
theorem toBialgEquiv_apply {X Y : BialgebraCat R} (i : X ≅ Y) (x : X) :
    i.toBialgEquiv x = i.hom x :=
  rfl

@[simp]
theorem toBialgEquiv_toBialgHom {X Y : BialgebraCat R} (i : X ≅ Y) :
    (i.toBialgEquiv : X →ₐc[R] Y) = i.hom :=
  rfl

@[simp]
theorem toBialgEquiv_symm_toBialgHom {X Y : BialgebraCat R} (i : X ≅ Y) :
    (i.toBialgEquiv.symm : Y →ₐc[R] X) = i.inv :=
  rfl

end CategoryTheory.Iso

/-- Bialgebra equivalences are the same as (isomorphic to) isomorphisms
in `BialgebraCat R` -/
@[simps]
def bialgEquivIsoBialgIso {X Y : Type u} [Ring X] [Ring Y]
    [Bialgebra R X] [Bialgebra R Y] :
    (X ≃ₐc[R] Y) ≅ BialgebraCat.of R X ≅ BialgebraCat.of R Y where
  hom e := e.toBialgIso
  inv i := i.toBialgEquiv

end
