/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_
public import Mathlib.Algebra.Ring.Basic

/-!
# Ring objects

-/

@[expose] public section

universe v u

namespace CategoryTheory

open MonoidalCategory CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [BraidedCategory C]

open scoped MonObj AddMonObj

/-- A ring object in a cartesian monoidal category is an object that is equipped
with an additive group structure and a (multiplicative) monoid structure that
is left and right distributive over the additive structure. -/
class RingObj (R : C) extends AddGrpObj R, IsCommAddMonObj R, MonObj R where
  mul_add (R) : R ◁ σ ≫ μ = lift ((R ◁ fst _ _) ≫ μ) ((R ◁ snd _ _) ≫ μ) ≫ σ
  add_mul (R) : σ ▷ R ≫ μ = lift (fst _ _ ▷ _ ≫ μ) (snd _ _ ▷ _ ≫ μ) ≫ σ

section

variable {R : C} [RingObj R] {X : C}

lemma Hom.mul_add (a b c : X ⟶ R) : a * (b + c) = a * b + a * c := by
  have := lift a (lift b c) ≫= RingObj.mul_add R
  simp only [lift_whiskerLeft_assoc] at this
  simp only [add_def, mul_def, this, ← Category.assoc]
  congr 1
  cat_disch

lemma Hom.add_mul (a b c : X ⟶ R) : (a + b) * c = a * c + b * c := by
  have := lift (lift a b) c ≫= RingObj.add_mul R
  simp only [lift_whiskerRight_assoc] at this
  simp only [add_def, mul_def, this, ← Category.assoc]
  congr 1
  cat_disch

/-- If `G` is a ring object, then `Hom(X, G)` has a ring structure. -/
abbrev Hom.ring {X : C} : Ring (X ⟶ R) where
  left_distrib := Hom.mul_add
  right_distrib := Hom.add_mul
  mul_zero a := by simpa using mul_add a 0 0
  zero_mul a := by simpa using add_mul 0 0 a

scoped[CategoryTheory.MonObj] attribute [instance] Hom.ring

end

/-- A commutative ring object in a cartesian monoidal category is a
ring object such that the multiplicative law is commutative. -/
class CommRingObj (R : C) extends RingObj R, IsCommMonObj R where

/-- If `G` is a commutative ring object, then `Hom(X, G)` has a commutative ring structure. -/
abbrev Hom.commRing {R : C} {X : C} [CommRingObj R] : CommRing (X ⟶ R) where

scoped[CategoryTheory.MonObj] attribute [instance] Hom.commRing

/-- The property that a morphism between ring objects is a ring morphism. -/
class IsRingHom {R₁ R₂ : C} [RingObj R₁] [RingObj R₂] (f : R₁ ⟶ R₂)
  extends IsAddMonHom f, IsMonHom f

instance IsRingHom.id (R : C) [RingObj R] : IsRingHom (𝟙 R) where

instance IsRingHom.comp {R₁ R₂ R₃ : C} [RingObj R₁] [RingObj R₂] [RingObj R₃]
    (f : R₁ ⟶ R₂) (g : R₂ ⟶ R₃) [IsRingHom f] [IsRingHom g] :
    IsRingHom (f ≫ g) where

variable (C) in
/-- The category of ring objects in a cartesian monoidal category. -/
structure Rng where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [ringObj : RingObj X]

namespace Rng

attribute [instance] ringObj

/-- A morphism of ring objects. -/
@[ext]
structure Hom (R₁ R₂ : Rng C) where
  /-- The underlying morphism -/
  hom : R₁.X ⟶ R₂.X
  [isRingHom : IsRingHom hom]

attribute [instance] Hom.isRingHom

@[simps]
instance : Category (Rng C) where
  Hom R₁ R₂ := Hom R₁ R₂
  id X := { hom := 𝟙 _ }
  comp f g := { hom := f.hom ≫ g.hom }

@[ext]
lemma hom_ext {R₁ R₂ : Rng C} {f g : R₁ ⟶ R₂} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

variable (C) in
/-- The forgetful functor from the category of ring objects in `C` to `C`. -/
@[simps]
def forget : Rng C ⥤ C where
  obj R := R.X
  map f := f.hom

instance : (forget C).Faithful where

variable (C) in
/-- The forgetful functor from the category of ring objects in `C`
to the category of monoid objects in `C`. -/
@[simps]
def forget₂Mon : Rng C ⥤ Mon C where
  obj R := .mk R.X
  map f := .mk f.hom

variable (C) in
/-- The forgetful functor from the category of ring objects in `C`
to the category of additive monoid objects in `C`. -/
@[simps]
def forget₂AddMon : Rng C ⥤ AddMon C where
  obj R := .mk R.X
  map f := .mk f.hom

end Rng

variable (C) in
/-- The category of commutative ring objects in a cartesian monoidal category. -/
structure CommRng where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [commRingObj : CommRingObj X]

namespace CommRng

attribute [instance] commRingObj

/-- A morphism of commutative ring objects. -/
@[ext]
structure Hom (R₁ R₂ : CommRng C) where
  /-- The underlying morphism -/
  hom : R₁.X ⟶ R₂.X
  [isRingHom : IsRingHom hom]

attribute [instance] Hom.isRingHom

@[simps]
instance : Category (CommRng C) where
  Hom R₁ R₂ := Hom R₁ R₂
  id X := { hom := 𝟙 _ }
  comp f g := { hom := f.hom ≫ g.hom }

@[ext]
lemma hom_ext {R₁ R₂ : CommRng C} {f g : R₁ ⟶ R₂} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

variable (C) in
/-- The forgetful functor from the category of ring objects in `C` to `C`. -/
@[simps]
def forget : CommRng C ⥤ C where
  obj R := R.X
  map f := f.hom

variable (C) in
/-- The forgetful functor from the category of commutative ring objects
to the category of ring objects. -/
def forget₂Rng : CommRng C ⥤ Rng C where
  obj R := .mk R.X
  map f := { hom := f.hom }

variable (C) in
/-- The forgetful functor `CommRng C ⥤ Rng C` is fully faithful. -/
def fullyFaithfulForget₂Rng : (forget₂Rng C).FullyFaithful where
  preimage f := { hom := f.hom, isRingHom := f.isRingHom }

instance : (forget₂Rng C).Faithful :=
  (fullyFaithfulForget₂Rng C).faithful

instance : (forget₂Rng C).Full :=
  (fullyFaithfulForget₂Rng C).full

instance : (forget C).Faithful where

end CommRng

end CategoryTheory
