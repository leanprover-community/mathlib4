/-
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Category.AlgebraCat.Basic
import Mathlib.Algebra.Algebra.RestrictScalars
set_option linter.uppercaseLean3 false

open CategoryTheory

open CategoryTheory.Limits

universe v u

variable (R : Type u) [CommRing R]

/-- The category of commutative R-algebras and their morphisms. -/
structure CommAlg where
  carrier : Type v
  [isCommRing : CommRing carrier]
  [isAlgebra : Algebra R carrier]

-- Porting note: typemax hack to fix universe complaints
/-- An alias for `CommAlg.{max u₁ u₂}`, to deal around unification issues.
Since the universe the ring lives in can be inferred, we put that last. -/
@[nolint checkUnivs]
abbrev CommAlgMax.{v₁, v₂, u₁} (R : Type u₁) [CommRing R] := CommAlg.{max v₁ v₂} R

attribute [instance] CommAlg.isCommRing CommAlg.isAlgebra

initialize_simps_projections CommAlg (-isCommRing, -isAlgebra)

namespace CommAlg

instance : CoeSort (CommAlg R) (Type v) :=
  ⟨CommAlg.carrier⟩

attribute [coe] CommAlg.carrier

instance : Category (CommAlg.{v} R) where
  Hom A B := A →ₐ[R] B
  id A := AlgHom.id R A
  comp f g := g.comp f

instance {M N : CommAlg.{v} R} : AlgHomClass (M ⟶ N) R M N :=
  AlgHom.algHomClass

instance : ConcreteCategory.{v} (CommAlg.{v} R) where
  forget :=
    { obj := fun R => R
      map := fun f => f.toFun }
  forget_faithful := ⟨fun h => AlgHom.ext (by intros x; dsimp at h; rw [h])⟩

instance {S : CommAlg.{v} R} : CommRing ((forget (CommAlg R)).obj S) :=
  (inferInstance : CommRing S.carrier)

instance {S : CommAlg.{v} R} : Algebra R ((forget (CommAlg R)).obj S) :=
  (inferInstance : Algebra R S.carrier)

instance hasForgetToCommRing : HasForget₂ (CommAlg.{v} R) CommRingCat.{v} where
  forget₂ :=
    { obj := fun A => CommRingCat.of A
      map := fun f => CommRingCat.ofHom f.toRingHom }

instance hasForgetToAlgebra : HasForget₂ (CommAlg.{v} R) (AlgebraCat.{v} R) where
  forget₂ :=
    { obj := fun M => AlgebraCat.of R M
      map := fun f => AlgebraCat.ofHom f }

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. -/
def of (X : Type v) [CommRing X] [Algebra R X] : CommAlg.{v} R :=
  ⟨X⟩

/-- Typecheck a `AlgHom` as a morphism in `CommAlg R`. -/
def ofHom {R : Type u} [CommRing R] {X Y : Type v} [CommRing X] [Algebra R X]
    [CommRing Y] [Algebra R Y] (f : X →ₐ[R] Y) : of R X ⟶ of R Y :=
  f

@[simp]
theorem ofHom_apply {R : Type u} [CommRing R] {X Y : Type v} [CommRing X] [Algebra R X]
    [CommRing Y] [Algebra R Y] (f : X →ₐ[R] Y) (x : X) : ofHom f x = f x :=
  rfl

instance : Inhabited (CommAlg R) :=
  ⟨of R R⟩

@[simp]
theorem coe_of (X : Type u) [CommRing X] [Algebra R X] : (of R X : Type u) = X :=
  rfl

variable {R}

/-- Forgetting to the underlying type and then building the bundled object returns the original
algebra. -/
@[simps]
def ofSelfIso (M : CommAlg.{v} R) : CommAlg.of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

variable {M N U : CommAlg.{v} R}

@[simp]
theorem id_apply (m : M) : (𝟙 M : M → M) m = m :=
  rfl

@[simp]
theorem coe_comp (f : M ⟶ N) (g : N ⟶ U) : (f ≫ g : M → U) = g ∘ f :=
  rfl

end CommAlg

variable {X₁ X₂ : Type u}

/-- Build an isomorphism in the category `CommAlg R` from a `AlgEquiv` between
commutative `Algebra`s. -/
@[simps]
def AlgEquiv.toCommAlgIso {g₁ : CommRing X₁} {g₂ : CommRing X₂}
    {m₁ : Algebra R X₁} {m₂ : Algebra R X₂}
    (e : X₁ ≃ₐ[R] X₂) : CommAlg.of R X₁ ≅ CommAlg.of R X₂ where
  hom := (e : X₁ →ₐ[R] X₂)
  inv := (e.symm : X₂ →ₐ[R] X₁)
  hom_inv_id := by ext x; exact e.left_inv x
  inv_hom_id := by ext x; exact e.right_inv x

namespace CategoryTheory.Iso

/-- Build a `AlgEquiv` from an isomorphism in the category `CommAlg R`. -/
@[simps]
def toCommAlgEquiv {X Y : CommAlg R} (i : X ≅ Y) : X ≃ₐ[R] Y where
  toFun := i.hom
  invFun := i.inv
  left_inv x := by
    -- porting note: was `by tidy`
    change (i.hom ≫ i.inv) x = x
    simp only [hom_inv_id]
    rw [id_apply]
  right_inv x := by
    -- porting note: was `by tidy`
    change (i.inv ≫ i.hom) x = x
    simp only [inv_hom_id]
    rw [id_apply]
  map_add' := i.hom.map_add -- Porting note: was `by tidy`
  map_mul' := i.hom.map_mul -- Porting note: was `by tidy`
  commutes' := i.hom.commutes -- Porting note: was `by tidy`

end CategoryTheory.Iso

/-- Algebra equivalences between commutative `Algebra`s are the same as (isomorphic to) isomorphisms
in `CommAlg`. -/
@[simps]
def commAlgEquivIsoCommAlgebraIso {X Y : Type u} [CommRing X] [CommRing Y]
    [Algebra R X] [Algebra R Y] :
    (X ≃ₐ[R] Y) ≅ CommAlg.of R X ≅ CommAlg.of R Y where
  hom e := e.toCommAlgIso
  inv i := i.toCommAlgEquiv

-- absolutely not.
-- Porting note: changed to `CoeOut`
/-instance (X : Type u) [CommRing X] [Algebra R X] : CoeOut (Subalgebra R X) (CommAlg R) :=
  ⟨fun N => CommAlg.of R N⟩-/

instance CommAlg.forget_reflects_isos : ReflectsIsomorphisms (forget (CommAlg.{u} R)) where
  reflects {X Y} f _ := by
    let i := asIso ((forget (CommAlg.{u} R)).map f)
    let e : X ≃ₐ[R] Y := { f, i.toEquiv with }
    exact ⟨(IsIso.of_iso e.toAlgebraIso).1⟩

axiom ffs {α : Sort _} : α

def CommAlg.restrictScalars (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
  CommAlg S ⥤ CommAlg R where
    obj := fun A => CommAlg.of R (RestrictScalars R S A)
    map := fun {A B} f =>
      @AlgHom.restrictScalars R S (RestrictScalars R S A)
        (RestrictScalars R S B) _ _ _ _ _ A.3 B.3 _ _ _ _ f
    map_id := ffs
    map_comp := ffs
