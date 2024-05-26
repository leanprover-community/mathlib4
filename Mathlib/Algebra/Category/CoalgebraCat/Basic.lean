/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.RingTheory.Coalgebra.Equiv
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Category instance for coalgebras over a commutative ring

We introduce the bundled category `CoalgebraCat` of coalgebras over a fixed commutative ring `R`
along with the forgetful functor to `ModuleCat`.

This is mostly a copy-paste from `Mathlib.Algebra.Category.AlgebraCat.Basic`.
-/

set_option linter.uppercaseLean3 false

open CategoryTheory

open CategoryTheory.Limits

universe v u

variable (R : Type u) [CommRing R]

/-- The category of R-coalgebras and their morphisms. -/
structure CoalgebraCat extends ModuleCat.{v} R where
  [isCoalgebra : Coalgebra R carrier]

attribute [instance] CoalgebraCat.isCoalgebra

initialize_simps_projections CoalgebraCat (-isCoalgebra)

namespace CoalgebraCat

instance : CoeSort (CoalgebraCat R) (Type v) :=
  ⟨fun C => C.carrier⟩

instance : Category (CoalgebraCat.{v} R) where
  Hom A B := A →ₗc[R] B
  id A := CoalgHom.id R A
  comp f g := g.comp f

instance {M N : CoalgebraCat.{v} R} : FunLike (M ⟶ N) M N :=
  CoalgHom.funLike

instance {M N : CoalgebraCat.{v} R} : CoalgHomClass (M ⟶ N) R M N :=
  CoalgHom.coalgHomClass

instance : ConcreteCategory.{v} (CoalgebraCat.{v} R) where
  forget :=
    { obj := fun R => R
      map := fun f => f.toFun }
  forget_faithful := ⟨fun h => CoalgHom.ext (by intros x; dsimp at h; rw [h])⟩

instance {S : CoalgebraCat.{v} R} : Coalgebra R ((forget (CoalgebraCat R)).obj S) :=
  (inferInstance : Coalgebra R S.carrier)

instance hasForgetToModule : HasForget₂ (CoalgebraCat.{v} R) (ModuleCat.{v} R) where
  forget₂ :=
    { obj := fun M => ModuleCat.of R M
      map := fun f => ModuleCat.ofHom f.toLinearMap }

@[simp]
lemma forget₂_module_obj (X : CoalgebraCat.{v} R) :
    (forget₂ (CoalgebraCat.{v} R) (ModuleCat.{v} R)).obj X = ModuleCat.of R X :=
  rfl

@[simp]
lemma forget₂_module_map {X Y : CoalgebraCat.{v} R} (f : X ⟶ Y) :
    (forget₂ (CoalgebraCat.{v} R) (ModuleCat.{v} R)).map f = ModuleCat.ofHom f.toLinearMap :=
  rfl

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. -/
def of (X : Type v) [AddCommGroup X] [Module R X] [Coalgebra R X] : CoalgebraCat.{v} R :=
  ⟨⟨X⟩⟩

/-- Typecheck a `CoalgHom` as a morphism in `CoalgebraCat R`. -/
def ofHom {R : Type u} [CommRing R] {X Y : Type v}
    [AddCommGroup X] [Module R X] [Coalgebra R X] [AddCommGroup Y] [Module R Y] [Coalgebra R Y]
    (f : X →ₗc[R] Y) : of R X ⟶ of R Y :=
  f

@[simp]
theorem ofHom_apply {R : Type u} [CommRing R] {X Y : Type v}
    [AddCommGroup X] [Module R X] [Coalgebra R X] [AddCommGroup Y] [Module R Y] [Coalgebra R Y]
    (f : X →ₗc[R] Y) (x : X) : ofHom f x = f x :=
  rfl

noncomputable instance : Inhabited (CoalgebraCat R) :=
  ⟨of R R⟩

@[simp]
theorem coe_of (X : Type u) [AddCommGroup X] [Module R X] [Coalgebra R X] : (of R X : Type u) = X :=
  rfl

variable {R}

/-- Forgetting to the underlying type and then building the bundled object returns the original
coalgebra. -/
@[simps]
def ofSelfIso (M : CoalgebraCat.{v} R) : CoalgebraCat.of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

variable {M N U : ModuleCat.{v} R}

@[simp]
theorem id_apply (m : M) : (𝟙 M : M → M) m = m :=
  rfl

@[simp]
theorem coe_comp (f : M ⟶ N) (g : N ⟶ U) : (f ≫ g : M → U) = g ∘ f :=
  rfl

end CoalgebraCat

variable {X₁ X₂ : Type u}

/--
Build an isomorphism in the category `CoalgebraCat R` from a `CoalgEquiv` between `Coalgebra`s.
-/
@[simps]
def CoalgEquiv.toCoalgebraIso
    {g₁ : AddCommGroup X₁} {g₂ : AddCommGroup X₂} {_ : Module R X₁} {_ : Module R X₂}
    {m₁ : Coalgebra R X₁} {m₂ : Coalgebra R X₂}
    (e : X₁ ≃ₗc[R] X₂) : CoalgebraCat.of R X₁ ≅ CoalgebraCat.of R X₂ where
  hom := (e : X₁ →ₗc[R] X₂)
  inv := (e.symm : X₂ →ₗc[R] X₁)
  hom_inv_id := by ext x; exact e.left_inv x
  inv_hom_id := by ext x; exact e.right_inv x

namespace CategoryTheory.Iso

/-- Build a `CoalgEquiv` from an isomorphism in the category `CoalgebraCat R`. -/
@[simps]
def toCoalgEquiv {X Y : CoalgebraCat R} (i : X ≅ Y) : X ≃ₗc[R] Y :=
  { i.hom with
    toFun := i.hom
    invFun := i.inv
    left_inv := fun x => by
      change (i.hom ≫ i.inv) x = x
      simp only [Iso.hom_inv_id]
      erw [id_apply]
    right_inv := fun x => by
      change (i.inv ≫ i.hom) x = x
      simp only [Iso.inv_hom_id]
      erw [id_apply] }

end CategoryTheory.Iso

/-- Coalgebra equivalences between `Coalgebra`s are the same as (isomorphic to) isomorphisms in
`CoalgebraCat`. -/
@[simps]
def coalgEquivIsoCoalgebraIso {X Y : Type u}
    [AddCommGroup X] [Module R X] [Coalgebra R X] [AddCommGroup Y] [Module R Y] [Coalgebra R Y] :
    (X ≃ₗc[R] Y) ≅ CoalgebraCat.of R X ≅ CoalgebraCat.of R Y where
  hom e := e.toCoalgebraIso
  inv i := i.toCoalgEquiv

instance CoalgebraCat.forget_reflects_isos :
    (forget (CoalgebraCat.{u} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (CoalgebraCat.{u} R)).map f)
    let e : X ≃ₗc[R] Y := { f, i.toEquiv with }
    exact ⟨(IsIso.of_iso e.toCoalgebraIso).1⟩

/-!
`@[simp]` lemmas for `CoalgHom.comp` and categorical identities.
-/

@[simp] theorem CoalgHom.comp_id_coalgebraCat
    {R} [CommRing R] {G : CoalgebraCat.{u} R}
    {H : Type u} [AddCommGroup H] [Module R H] [Coalgebra R H] (f : G →ₗc[R] H) :
    f.comp (𝟙 G) = f :=
  Category.id_comp (CoalgebraCat.ofHom f)
@[simp] theorem CoalgHom.id_coalgebraCat_comp
    {R} [CommRing R] {G : Type u} [AddCommGroup G] [Module R G] [Coalgebra R G]
    {H : CoalgebraCat.{u} R} (f : G →ₗc[R] H) :
    CoalgHom.comp (𝟙 H) f = f :=
  Category.comp_id (CoalgebraCat.ofHom f)
