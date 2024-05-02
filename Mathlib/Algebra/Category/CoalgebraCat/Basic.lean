/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.RingTheory.Coalgebra.Equiv
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# The category of `R`-coalgebras

`CoalgebraCat.{v} R` is the category of bundled `R`-coalgebras with carrier in the universe v.

This file simply mimics `Mathlib.Algebra.Category.ModuleCat.Basic`.

-/

universe v u

variable (R : Type u) [CommRing R]

/-- Objects in the category of `R`-coalgebras. -/
structure CoalgebraCat where
  /-- the underlying type of an object in `CoalgebraCat R` -/
  carrier : Type v
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module R carrier]
  [isCoalgebra : Coalgebra R carrier]

attribute [instance] CoalgebraCat.isAddCommGroup CoalgebraCat.isModule CoalgebraCat.isCoalgebra

/-- An alias for `CoalgebraCat.{max u₁ u₂}`, to deal around unification issues.
Since the universe the ring lives in can be inferred, we put that last. -/
@[nolint checkUnivs]
abbrev CoalgebraCatMax.{v₁, v₂, u₁} (R : Type u₁) [CommRing R] := CoalgebraCat.{max v₁ v₂, u₁} R

namespace CoalgebraCat
open CategoryTheory CategoryTheory.Limits

instance : CoeSort (CoalgebraCat.{v} R) (Type v) :=
  ⟨CoalgebraCat.carrier⟩

attribute [coe] CoalgebraCat.carrier

instance coalgebraCategory : Category.{v, max (v+1) u} (CoalgebraCat.{v} R) where
  Hom M N := M →ₗc[R] N
  id _ := CoalgHom.id R _
  comp f g := g.comp f
  id_comp _ := CoalgHom.id_comp _
  comp_id _ := CoalgHom.comp_id _
  assoc f g h := CoalgHom.comp_assoc h g f

instance {M N : CoalgebraCat.{v} R} : FunLike (M ⟶ N) M N :=
  inferInstanceAs (FunLike (M →ₗc[R] N) M N)

instance {M N : CoalgebraCat.{v} R} : CoalgHomClass (M ⟶ N) R M N :=
  CoalgHom.coalgHomClass

instance coalgebraConcreteCategory : ConcreteCategory.{v} (CoalgebraCat.{v} R) where
  forget :=
    { obj := fun R => R
      map := fun f => f.toFun }
  forget_faithful := ⟨fun h => CoalgHom.ext (fun x => by
    dsimp at h
    rw [h])⟩

instance {M : CoalgebraCat.{v} R} : AddCommGroup ((forget (CoalgebraCat R)).obj M) :=
  (inferInstance : AddCommGroup M)
instance {M : CoalgebraCat.{v} R} : Module R ((forget (CoalgebraCat R)).obj M) :=
  (inferInstance : Module R M)
instance {M : CoalgebraCat.{v} R} : Coalgebra R ((forget (CoalgebraCat R)).obj M) :=
  (inferInstance : Coalgebra R M)

@[ext]
lemma ext {M N : CoalgebraCat.{v} R} {f₁ f₂ : M ⟶ N} (h : ∀ (x : M), f₁ x = f₂ x) : f₁ = f₂ :=
  DFunLike.ext _ _ h

instance hasForgetToModule : HasForget₂ (CoalgebraCat R) (ModuleCat R) where
  forget₂ :=
    { obj := fun M => ModuleCat.of R M
      map := fun f => ModuleCat.ofHom f.toLinearMap }

instance {M : CoalgebraCat.{v} R} :
    AddCommGroup ((forget₂ (CoalgebraCat R) (ModuleCat R)).obj M) :=
  (inferInstance : AddCommGroup M)
instance {M : CoalgebraCat.{v} R} : Module R ((forget₂ (CoalgebraCat R) (ModuleCat R)).obj M) :=
  (inferInstance : Module R M)
instance {M : CoalgebraCat.{v} R} : Coalgebra R ((forget₂ (CoalgebraCat R) (ModuleCat R)).obj M) :=
  (inferInstance : Coalgebra R M)

instance {M : CoalgebraCat.{v} R} : Coalgebra R (ModuleCat.of R M) :=
  (inferInstance : Coalgebra R M)

instance hasForgetToAddCommGroup : HasForget₂ (CoalgebraCat R) AddCommGroupCat where
  forget₂ :=
    { obj := fun M => AddCommGroupCat.of M
      map := fun f => AddCommGroupCat.ofHom f.toLinearMap }

/-- The object in the category of R-coalgebras associated to an R-coalgebra. -/
def of (X : Type v) [AddCommGroup X] [Module R X] [Coalgebra R X] : CoalgebraCat R :=
  ⟨X⟩

@[simp]
theorem forget₂_obj (X : CoalgebraCat R) :
    (forget₂ (CoalgebraCat R) (ModuleCat R)).obj X = ModuleCat.of R X :=
  rfl

@[simp]
theorem forget₂_map (X Y : CoalgebraCat R) (f : X ⟶ Y) :
    (forget₂ (CoalgebraCat R) (ModuleCat R)).map f = (f : X →ₗ[R] Y) :=
  rfl

/-- Typecheck a `CoalgHom` as a morphism in `CoalgebraCat R`. -/
def ofHom {R : Type u} [CommRing R] {X Y : Type v} [AddCommGroup X] [Module R X] [Coalgebra R X]
    [AddCommGroup Y] [Module R Y] [Coalgebra R Y] (f : X →ₗc[R] Y) : of R X ⟶ of R Y :=
  f

@[simp 1100]
theorem ofHom_apply {R : Type u} [CommRing R] {X Y : Type v} [AddCommGroup X]
    [Module R X] [Coalgebra R X]
    [AddCommGroup Y] [Module R Y] [Coalgebra R Y] (f : X →ₗc[R] Y) (x : X) : ofHom f x = f x :=
  rfl

instance ofUnique {X : Type v} [AddCommGroup X] [Module R X] [Coalgebra R X]
    [i : Unique X] : Unique (of R X) :=
  i

variable {R}

/-- Forgetting to the underlying type and then building the bundled object returns the original
coalgebra. -/
@[simps]
def ofSelfIso (M : CoalgebraCat R) : CoalgebraCat.of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

variable {M N U : CoalgebraCat.{v} R}

@[simp]
theorem id_apply (m : M) : (𝟙 M : M → M) m = m :=
  rfl

@[simp]
theorem coe_comp (f : M ⟶ N) (g : N ⟶ U) : (f ≫ g : M → U) = g ∘ f :=
  rfl

theorem comp_def (f : M ⟶ N) (g : N ⟶ U) : f ≫ g = g.comp f :=
  rfl

@[simp] lemma forget_map (f : M ⟶ N) : (forget (CoalgebraCat R)).map f = (f : M → N) := rfl

end CoalgebraCat

variable {R}

variable {X₁ X₂ : Type v}

section

/-- Build an isomorphism in the category `CoalgebraCat R` from a `CoalgEquiv`
between coalgebras. -/
@[simps]
def CoalgEquiv.toCoalgebraIso {g₁ : AddCommGroup X₁} {g₂ : AddCommGroup X₂} {m₁ : Module R X₁}
    {c₁ : Coalgebra R X₁} {m₂ : Module R X₂} {c₂ : Coalgebra R X₂} (e : X₁ ≃ₗc[R] X₂) :
    CoalgebraCat.of R X₁ ≅ CoalgebraCat.of R X₂ where
  hom := (e : X₁ →ₗc[R] X₂)
  inv := (e.symm : X₂ →ₗc[R] X₁)
  hom_inv_id := by ext; apply e.left_inv
  inv_hom_id := by ext; apply e.right_inv

/-- Build an isomorphism in the category `CoalgebraCat R` from a `CoalgEquiv`
between coalgebras. -/
abbrev CoalgEquiv.toCoalgebraIso' {M N : CoalgebraCat.{v} R} (i : M ≃ₗc[R] N) : M ≅ N :=
  i.toCoalgebraIso

/-- Build an isomorphism in the category `CoalgebraCat R` from a `CoalgEquiv`
between coalgebras. -/
abbrev CoalgEquiv.toCoalgebraIso'Left {X₁ : CoalgebraCat.{v} R}
    [AddCommGroup X₂] [Module R X₂] [Coalgebra R X₂]
    (e : X₁ ≃ₗc[R] X₂) : X₁ ≅ CoalgebraCat.of R X₂ :=
  e.toCoalgebraIso

/-- Build an isomorphism in the category `CoalgebraCat R` from a `CoalgEquiv`
between coalgebras. -/
abbrev CoalgEquiv.toCoalgebraIso'Right
    [AddCommGroup X₁] [Module R X₁] [Coalgebra R X₁] {X₂ : CoalgebraCat.{v} R}
    (e : X₁ ≃ₗc[R] X₂) : CoalgebraCat.of R X₁ ≅ X₂ :=
  e.toCoalgebraIso

namespace CategoryTheory.Iso

/-- Build a `CoalgEquiv` from an isomorphism in the category `CoalgebraCat R`. -/
def toCoalgEquiv {X Y : CoalgebraCat R} (i : X ≅ Y) : X ≃ₗc[R] Y :=
  { i.hom with
    invFun := i.inv
    left_inv := fun x => CoalgHom.congr_fun i.3 x
    right_inv := fun x => CoalgHom.congr_fun i.4 x }

@[simp]
theorem toCoalgEquiv_apply {X Y : CoalgebraCat R} (i : X ≅ Y) (x : X) :
    i.toCoalgEquiv x = i.hom x :=
  rfl

@[simp]
theorem toCoalgEquiv_toCoalgHom {X Y : CoalgebraCat R} (i : X ≅ Y) :
    (i.toCoalgEquiv : X →ₗc[R] Y) = i.hom :=
  rfl

@[simp]
theorem toCoalgEquiv_symm_toCoalgHom {X Y : CoalgebraCat R} (i : X ≅ Y) :
    (i.toCoalgEquiv.symm : Y →ₗc[R] X) = i.inv :=
  rfl

end CategoryTheory.Iso

/-- Coalgebra equivalences are the same as (isomorphic to) isomorphisms
in `CoalgebraCat R` -/
@[simps]
def coalgEquivIsoCoalgebraIso {X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
    [Module R X] [Coalgebra R X] [Module R Y] [Coalgebra R Y] :
    (X ≃ₗc[R] Y) ≅ CoalgebraCat.of R X ≅ CoalgebraCat.of R Y where
  hom e := e.toCoalgebraIso
  inv i := i.toCoalgEquiv

end
