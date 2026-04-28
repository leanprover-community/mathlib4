/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

import Mathlib.Tactic.CategoryTheory.MkConcreteCategory
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.CategoryTheory.ConcreteCategory.Basic

open CategoryTheory

universe v u

/-- A test category whose morphisms are wrappers around functions. -/
structure TestCat where
  /-- The underlying type. -/
  α : Type u

namespace TestCat

@[ext]
structure Fun (X Y : TestCat.{u}) where
  toFun : X.α → Y.α

instance (X Y : TestCat.{u}) : FunLike (Fun X Y) X.α Y.α where
  coe := Fun.toFun
  coe_injective' _ _ _ := by aesop

protected def Fun.id (X : TestCat.{u}) : Fun X X where
  toFun := id

protected def Fun.comp {X Y Z : TestCat.{u}} (f : Fun X Y) (g : Fun Y Z) : Fun X Z where
  toFun := g.toFun ∘ f.toFun

mk_concrete_category TestCat Fun Fun.id Fun.comp

/-- info: TestCat.Hom.{u_1} (X Y : TestCat) : Type u_1 -/
#guard_msgs in
#check Hom

/-- info: TestCat.Hom.mk.{u_1} {X Y : TestCat} (hom' : X.Fun Y) : X.Hom Y -/
#guard_msgs in
#check Hom.mk

/-- info: TestCat.Hom.hom'.{u_1} {X Y : TestCat} (self : X.Hom Y) : X.Fun Y -/
#guard_msgs in
#check Hom.hom'

/-- info: TestCat.Hom.ext.{u_1} {X Y : TestCat} {x y : X.Hom Y} (hom' : x.hom' = y.hom') : x = y -/
#guard_msgs in
#check Hom.ext

/-- info: TestCat.instCategory.{u_1} : Category.{u_1, u_1 + 1} TestCat -/
#guard_msgs in
#check TestCat.instCategory

/-- info: TestCat.instConcreteCategory.{u_1} : ConcreteCategory TestCat Fun -/
#guard_msgs in
#check TestCat.instConcreteCategory

/-- info: TestCat.Hom.hom.{u_1} {X Y : TestCat} (f : X.Hom Y) : X.Fun Y -/
#guard_msgs in
#check Hom.hom

/-- info: TestCat.ofHom.{u_1} {X Y : TestCat} (f : X.Fun Y) : X ⟶ Y -/
#guard_msgs in
#check ofHom

/-- info: TestCat.Hom.Simps.hom.{u_1} (X Y : TestCat) (f : X.Hom Y) : X.Fun Y -/
#guard_msgs in
#check Hom.Simps.hom

/-- info: TestCat.hom_id.{u_1} {X : TestCat} : Hom.hom (𝟙 X) = Fun.id X -/
#guard_msgs in
#check hom_id

/-- info: TestCat.hom_comp.{u_1} {X Y Z : TestCat} (f : X ⟶ Y) (g : Y ⟶ Z) : Hom.hom (f ≫ g) = (Hom.hom f).comp (Hom.hom g) -/
#guard_msgs in
#check hom_comp

/-- info: TestCat.hom_ofHom.{u_1} {X Y : TestCat} (f : X.Fun Y) : Hom.hom (ConcreteCategory.ofHom f) = f -/
#guard_msgs in
#check hom_ofHom

/-- info: TestCat.ofHom_hom.{u_1} {X Y : TestCat} (f : X ⟶ Y) : ConcreteCategory.ofHom (Hom.hom f) = f -/
#guard_msgs in
#check ofHom_hom

example : Category TestCat := inferInstance

example : ConcreteCategory TestCat Fun := inferInstance

example {X Y : TestCat} (f : X ⟶ Y) : f.hom = ConcreteCategory.hom f := rfl

example {X Y : TestCat} (f : Fun X Y) : (ofHom f).hom = f := by
  dsimp

example {X Y : TestCat} (f : X ⟶ Y) : ofHom f.hom = f := by
  dsimp

example {X : TestCat} : (𝟙 X : X ⟶ X).hom = Fun.id X := by
  dsimp

example {X Y Z : TestCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = Fun.comp f.hom g.hom := by
  dsimp

example {X Y : TestCat} (f g : X ⟶ Y) (h : f.hom = g.hom) : f = g :=
  Hom.ext h

example {X Y : TestCat} (f g : X ⟶ Y) (h : ∀ x, f x = g x) : f = g := by
  cat_disch

example {X Y : TestCat} (f : Fun X Y) (x : X.α) : ofHom f x = f x := by
  dsimp

end TestCat

variable (R : Type u) [Ring R]

structure ModuleTestCat where
  carrier : Type v
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module R carrier]

attribute [instance] ModuleTestCat.isAddCommGroup
attribute [instance 1100] ModuleTestCat.isModule

namespace ModuleTestCat

/-- Construct a bundled `ModuleTestCat` from the underlying type and typeclass. -/
abbrev of (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] :
    ModuleTestCat R :=
  ⟨M⟩

instance : CoeSort (ModuleTestCat.{v} R) (Type v) :=
  ⟨ModuleTestCat.carrier⟩

attribute [coe] ModuleTestCat.carrier

variable {R} in
mk_concrete_category (ModuleTestCat R) (· →ₗ[R] ·) (LinearMap.id ·) (LinearMap.comp · ·)
  with_of_hom {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
  hom_type (X →ₗ[R] Y) from (of R X) to (of R Y)

/-- info: ModuleTestCat.Hom.{u, u_1, u_2} {R : Type u} [Ring R] (X : ModuleTestCat R) (Y : ModuleTestCat R) : Type (max u_1 u_2) -/
#guard_msgs in
#check Hom

/--
info: ModuleTestCat.Hom.mk.{u, u_1, u_2} {R : Type u} [Ring R] {X : ModuleTestCat R} {Y : ModuleTestCat R}
  (hom' : ↑X →ₗ[R] ↑Y) : X.Hom Y
-/
#guard_msgs in
#check Hom.mk

/--
info: ModuleTestCat.Hom.hom'.{u, u_1, u_2} {R : Type u} [Ring R] {X : ModuleTestCat R} {Y : ModuleTestCat R}
  (self : X.Hom Y) : ↑X →ₗ[R] ↑Y
-/
#guard_msgs in
#check Hom.hom'

/--
info: ModuleTestCat.Hom.ext.{u, u_1, u_2} {R : Type u} {inst✝ : Ring R} {X : ModuleTestCat R} {Y : ModuleTestCat R}
  {x y : X.Hom Y} (hom' : x.hom' = y.hom') : x = y
-/
#guard_msgs in
#check Hom.ext

/-- info: ModuleTestCat.instCategory.{u, u_1} {R : Type u} [Ring R] : Category.{u_1, max u (u_1 + 1)} (ModuleTestCat R) -/
#guard_msgs in
#check ModuleTestCat.instCategory

/-- info: ModuleTestCat.instConcreteCategory.{u, u_1} {R : Type u} [Ring R] :
  ConcreteCategory (ModuleTestCat R) fun x1 x2 => ↑x1 →ₗ[R] ↑x2 -/
#guard_msgs in
#check ModuleTestCat.instConcreteCategory

/-- info: ModuleTestCat.Hom.hom.{u, u_1} {R : Type u} [Ring R] {X Y : ModuleTestCat R} (f : X.Hom Y) : ↑X →ₗ[R] ↑Y -/
#guard_msgs in
#check Hom.hom

/-- info: ModuleTestCat.ofHom.{v, u} {R : Type u} [Ring R] {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y]
  [Module R Y] (f : X →ₗ[R] Y) : of R X ⟶ of R Y -/
#guard_msgs in
#check ofHom

/--
info: ModuleTestCat.Hom.Simps.hom.{u, u_1, u_2} {R : Type u} [Ring R] (X : ModuleTestCat R) (Y : ModuleTestCat R)
  (f : X.Hom Y) : (fun x1 x2 => ↑x1 →ₗ[R] ↑x2) X Y
-/
#guard_msgs in
#check Hom.Simps.hom

/-- info: ModuleTestCat.hom_id.{u, u_1} {R : Type u} [Ring R] {X : ModuleTestCat R} : Hom.hom (𝟙 X) = LinearMap.id -/
#guard_msgs in
#check hom_id

/-- info: ModuleTestCat.hom_comp.{u, u_1} {R : Type u} [Ring R] {X Y Z : ModuleTestCat R} (f : X ⟶ Y) (g : Y ⟶ Z) :
  Hom.hom (f ≫ g) = Hom.hom g ∘ₗ Hom.hom f -/
#guard_msgs in
#check hom_comp

/-- info: ModuleTestCat.hom_ofHom.{u, u_1} {R : Type u} [Ring R] {X Y : ModuleTestCat R} (f : ↑X →ₗ[R] ↑Y) :
  Hom.hom (ConcreteCategory.ofHom f) = f -/
#guard_msgs in
#check hom_ofHom

/-- info: ModuleTestCat.ofHom_hom.{u, u_1} {R : Type u} [Ring R] {X Y : ModuleTestCat R} (f : X ⟶ Y) :
  ConcreteCategory.ofHom (Hom.hom f) = f -/
#guard_msgs in
#check ofHom_hom

example : Category (ModuleTestCat.{v} R) := inferInstance

example : ConcreteCategory (ModuleTestCat.{v} R) (fun X Y => X →ₗ[R] Y) := inferInstance

example {X Y : ModuleTestCat.{v} R} (f : X ⟶ Y) : f.hom = ConcreteCategory.hom f := rfl

example {X Y : ModuleTestCat.{v} R} (f : X →ₗ[R] Y) : (ofHom f).hom = f := by
  dsimp

example {X Y : ModuleTestCat.{v} R} (f : X ⟶ Y) : ofHom f.hom = f := by
  dsimp

example {X : ModuleTestCat.{v} R} : (𝟙 X : X ⟶ X).hom = LinearMap.id := by
  dsimp

example {X Y Z : ModuleTestCat.{v} R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = LinearMap.comp g.hom f.hom := by
  dsimp

example {X Y : ModuleTestCat.{v} R} (f g : X ⟶ Y) (h : f.hom = g.hom) : f = g :=
  Hom.ext h

example {X Y : ModuleTestCat.{v} R} (f g : X ⟶ Y) (h : ∀ x, f x = g x) : f = g := by
  cat_disch

example {X Y : ModuleTestCat.{v} R} (f : X →ₗ[R] Y) (x : X) : ofHom f x = f x := by
  dsimp

end ModuleTestCat

/-- Additive test category for the `to_additive` form of `mk_concrete_category`. -/
structure AdditiveTestCat where
  /-- The underlying type. -/
  carrier : Type u
  [str : AddMonoid carrier]

/-- Multiplicative test category for the `to_additive` form of `mk_concrete_category`. -/
@[to_additive AdditiveTestCat]
structure MultiplicativeTestCat where
  /-- The underlying type. -/
  carrier : Type u
  [str : Monoid carrier]

attribute [instance] AdditiveTestCat.str MultiplicativeTestCat.str

namespace MultiplicativeTestCat

/-- Construct a bundled `MultiplicativeTestCat` from the underlying type and typeclass. -/
@[to_additive /-- Construct a bundled `AdditiveTestCat` from the underlying type and typeclass. -/]
abbrev of (M : Type u) [Monoid M] : MultiplicativeTestCat :=
  ⟨M⟩

@[to_additive instCoeSortAdditiveTestCat]
instance instCoeSort : CoeSort MultiplicativeTestCat (Type u) :=
  ⟨MultiplicativeTestCat.carrier⟩

end MultiplicativeTestCat

attribute [coe] AdditiveTestCat.carrier MultiplicativeTestCat.carrier

@[to_additive AdditiveTestCat]
mk_concrete_category MultiplicativeTestCat (· →* ·) (MonoidHom.id ·) (MonoidHom.comp · ·)
  with_of_hom {X Y : Type u} [Monoid X] [Monoid Y]
  hom_type (X →* Y) from (MultiplicativeTestCat.of X) to (MultiplicativeTestCat.of Y)
  to_additive AdditiveTestCat (· →+ ·) (AddMonoidHom.id ·) (AddMonoidHom.comp · ·)
  with_of_hom {X Y : Type u} [AddMonoid X] [AddMonoid Y]
  hom_type (X →+ Y) from (AdditiveTestCat.of X) to (AdditiveTestCat.of Y)

namespace MultiplicativeTestCat

/-- info: MultiplicativeTestCat.Hom.{u_1, u_2} (X : MultiplicativeTestCat) (Y : MultiplicativeTestCat) : Type (max u_1 u_2) -/
#guard_msgs in
#check Hom

/-- info: MultiplicativeTestCat.instCategory.{u_1} : Category.{u_1, u_1 + 1} MultiplicativeTestCat -/
#guard_msgs in
#check MultiplicativeTestCat.instCategory

/-- info: MultiplicativeTestCat.instConcreteCategory.{u_1} : ConcreteCategory MultiplicativeTestCat fun x1 x2 => ↑x1 →* ↑x2 -/
#guard_msgs in
#check MultiplicativeTestCat.instConcreteCategory

/-- info: MultiplicativeTestCat.Hom.hom.{u_1} {X Y : MultiplicativeTestCat} (f : X.Hom Y) : ↑X →* ↑Y -/
#guard_msgs in
#check Hom.hom

/-- info: MultiplicativeTestCat.ofHom.{u} {X Y : Type u} [Monoid X] [Monoid Y] (f : X →* Y) : of X ⟶ of Y -/
#guard_msgs in
#check ofHom

example : Category MultiplicativeTestCat := inferInstance

example : ConcreteCategory MultiplicativeTestCat (fun X Y => X →* Y) := inferInstance

example {X Y : Type u} [Monoid X] [Monoid Y] (f : X →* Y) : (ofHom f).hom = f := by
  dsimp

example {X Y Z : MultiplicativeTestCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = MonoidHom.comp g.hom f.hom := by
  dsimp

end MultiplicativeTestCat

namespace AdditiveTestCat

/-- info: AdditiveTestCat.Hom.{u_1, u_2} (X : AdditiveTestCat) (Y : AdditiveTestCat) : Type (max u_1 u_2) -/
#guard_msgs in
#check Hom

/-- info: AdditiveTestCat.instCategory.{u_1} : Category.{u_1, u_1 + 1} AdditiveTestCat -/
#guard_msgs in
#check AdditiveTestCat.instCategory

/-- info: AdditiveTestCat.instConcreteCategory.{u_1} : ConcreteCategory AdditiveTestCat fun x1 x2 => ↑x1 →+ ↑x2 -/
#guard_msgs in
#check AdditiveTestCat.instConcreteCategory

/-- info: AdditiveTestCat.Hom.hom.{u_1} {X Y : AdditiveTestCat} (f : X.Hom Y) : ↑X →+ ↑Y -/
#guard_msgs in
#check Hom.hom

/-- info: AdditiveTestCat.ofHom.{u} {X Y : Type u} [AddMonoid X] [AddMonoid Y] (f : X →+ Y) : of X ⟶ of Y -/
#guard_msgs in
#check ofHom

example : Category AdditiveTestCat := inferInstance

example : ConcreteCategory AdditiveTestCat (fun X Y => X →+ Y) := inferInstance

example {X Y : Type u} [AddMonoid X] [AddMonoid Y] (f : X →+ Y) : (ofHom f).hom = f := by
  dsimp

example {X Y Z : AdditiveTestCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = AddMonoidHom.comp g.hom f.hom := by
  dsimp

end AdditiveTestCat
