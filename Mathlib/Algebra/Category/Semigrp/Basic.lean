/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
import Mathlib.Algebra.PEmptyInstances
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.CategoryTheory.Elementwise
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Category instances for `Mul`, `Add`, `Semigroup` and `AddSemigroup`

We introduce the bundled categories:
* `MagmaCat`
* `AddMagmaCat`
* `Semigrp`
* `AddSemigrp`

along with the relevant forgetful functors between them.

This closely follows `Mathlib/Algebra/Category/MonCat/Basic.lean`.

## TODO

* Limits in these categories
* free/forgetful adjunctions
-/


universe u v

open CategoryTheory

/-- The category of additive magmas and additive magma morphisms. -/
structure AddMagmaCat : Type (u + 1) where
  /-- The underlying additive magma. -/
  (carrier : Type u)
  [str : Add carrier]

/-- The category of magmas and magma morphisms. -/
@[to_additive]
structure MagmaCat : Type (u + 1) where
  /-- The underlying magma. -/
  (carrier : Type u)
  [str : Mul carrier]

attribute [instance] AddMagmaCat.str MagmaCat.str
attribute [to_additive existing] MagmaCat.carrier MagmaCat.str

initialize_simps_projections AddMagmaCat (carrier → coe, -str)
initialize_simps_projections MagmaCat (carrier → coe, -str)

namespace MagmaCat

@[to_additive]
instance : CoeSort MagmaCat (Type u) :=
  ⟨MagmaCat.carrier⟩

attribute [coe] AddMagmaCat.carrier MagmaCat.carrier

/-- Construct a bundled `MagmaCat` from the underlying type and typeclass. -/
@[to_additive "Construct a bundled `AddMagmaCat` from the underlying type and typeclass."]
abbrev of (M : Type u) [Mul M] : MagmaCat := ⟨M⟩

end MagmaCat

/-- The type of morphisms in `AddMagmaCat R`. -/
@[ext]
structure AddMagmaCat.Hom (A B : AddMagmaCat.{u}) where
  private mk ::
  /-- The underlying `AddHom`. -/
  hom' : A →ₙ+ B

/-- The type of morphisms in `MagmaCat R`. -/
@[to_additive, ext]
structure MagmaCat.Hom (A B : MagmaCat.{u}) where
  private mk ::
  /-- The underlying `MulHom`. -/
  hom' : A →ₙ* B

attribute [to_additive existing AddMagmaCat.Hom.mk] MagmaCat.Hom.mk

namespace MagmaCat

@[to_additive]
instance : Category MagmaCat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨MulHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

@[to_additive]
instance : ConcreteCategory MagmaCat (· →ₙ* ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `MagmaCat` back into a `MulHom`. -/
@[to_additive "Turn a morphism in `AddMagmaCat` back into an `AddHom`."]
abbrev Hom.hom {X Y : MagmaCat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := MagmaCat) f

/-- Typecheck a `MulHom` as a morphism in `MagmaCat`. -/
@[to_additive "Typecheck an `AddHom` as a morphism in `AddMagmaCat`. "]
abbrev ofHom {X Y : Type u} [Mul X] [Mul Y] (f : X →ₙ* Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := MagmaCat) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (X Y : MagmaCat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)
initialize_simps_projections AddMagmaCat.Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[to_additive (attr := simp)]
lemma coe_id {X : MagmaCat} : (𝟙 X : X → X) = id := rfl

@[to_additive (attr := simp)]
lemma coe_comp {X Y Z : MagmaCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[to_additive (attr := simp)]
lemma forget_map {X Y : MagmaCat} (f : X ⟶ Y) :
    (forget MagmaCat).map f = f := rfl

@[to_additive (attr := ext)]
lemma ext {X Y : MagmaCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[to_additive]
-- This is not `simp` to avoid rewriting in types of terms.
theorem coe_of (M : Type u) [Mul M] : (MagmaCat.of M : Type u) = M := rfl

@[to_additive (attr := simp)]
lemma hom_id {M : MagmaCat} : (𝟙 M : M ⟶ M).hom = MulHom.id M := rfl

/- Provided for rewriting. -/
@[to_additive]
lemma id_apply (M : MagmaCat) (x : M) :
    (𝟙 M : M ⟶ M) x = x := by simp

@[to_additive (attr := simp)]
lemma hom_comp {M N T : MagmaCat} (f : M ⟶ N) (g : N ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
@[to_additive]
lemma comp_apply {M N T : MagmaCat} (f : M ⟶ N) (g : N ⟶ T) (x : M) :
    (f ≫ g) x = g (f x) := by simp

@[to_additive (attr := ext)]
lemma hom_ext {M N : MagmaCat} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[to_additive (attr := simp)]
lemma hom_ofHom {M N : Type u} [Mul M] [Mul N] (f : M →ₙ* N) :
  (ofHom f).hom = f := rfl

@[to_additive (attr := simp)]
lemma ofHom_hom {M N : MagmaCat} (f : M ⟶ N) :
    ofHom (Hom.hom f) = f := rfl

@[to_additive (attr := simp)]
lemma ofHom_id {M : Type u} [Mul M] : ofHom (MulHom.id M) = 𝟙 (of M) := rfl

@[to_additive (attr := simp)]
lemma ofHom_comp {M N P : Type u} [Mul M] [Mul N] [Mul P]
    (f : M →ₙ* N) (g : N →ₙ* P) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

@[to_additive]
lemma ofHom_apply {X Y : Type u} [Mul X] [Mul Y] (f : X →ₙ* Y) (x : X) :
    (ofHom f) x = f x := rfl

@[to_additive]
lemma inv_hom_apply {M N : MagmaCat} (e : M ≅ N) (x : M) : e.inv (e.hom x) = x := by
  simp

@[to_additive]
lemma hom_inv_apply {M N : MagmaCat} (e : M ≅ N) (s : N) : e.hom (e.inv s) = s := by
  simp

@[to_additive (attr := simp)]
lemma mulEquiv_coe_eq {X Y : Type _} [Mul X] [Mul Y] (e : X ≃* Y) :
    (ofHom (e : X →ₙ* Y)).hom = ↑e :=
  rfl

@[to_additive]
instance : Inhabited MagmaCat :=
  ⟨MagmaCat.of PEmpty⟩

end MagmaCat

/-- The category of additive semigroups and semigroup morphisms. -/
structure AddSemigrp : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : AddSemigroup carrier]

/-- The category of semigroups and semigroup morphisms. -/
@[to_additive]
structure Semigrp : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : Semigroup carrier]

attribute [instance] AddSemigrp.str Semigrp.str
attribute [to_additive existing] Semigrp.carrier Semigrp.str

initialize_simps_projections AddSemigrp (carrier → coe, -str)
initialize_simps_projections Semigrp (carrier → coe, -str)

namespace Semigrp

@[to_additive]
instance : CoeSort Semigrp (Type u) :=
  ⟨Semigrp.carrier⟩

attribute [coe] AddSemigrp.carrier Semigrp.carrier

/-- Construct a bundled `Semigrp` from the underlying type and typeclass. -/
@[to_additive "Construct a bundled `AddSemigrp` from the underlying type and typeclass."]
abbrev of (M : Type u) [Semigroup M] : Semigrp := ⟨M⟩

end Semigrp

/-- The type of morphisms in `AddSemigrp R`. -/
@[ext]
structure AddSemigrp.Hom (A B : AddSemigrp.{u}) where
  private mk ::
  /-- The underlying `AddHom`. -/
  hom' : A →ₙ+ B

/-- The type of morphisms in `Semigrp R`. -/
@[to_additive, ext]
structure Semigrp.Hom (A B : Semigrp.{u}) where
  private mk ::
  /-- The underlying `MulHom`. -/
  hom' : A →ₙ* B

attribute [to_additive existing AddSemigrp.Hom.mk] Semigrp.Hom.mk

namespace Semigrp

@[to_additive]
instance : Category Semigrp.{u} where
  Hom X Y := Hom X Y
  id X := ⟨MulHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

@[to_additive]
instance : ConcreteCategory Semigrp (· →ₙ* ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `Semigrp` back into a `MulHom`. -/
@[to_additive "Turn a morphism in `AddSemigrp` back into an `AddHom`."]
abbrev Hom.hom {X Y : Semigrp.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := Semigrp) f

/-- Typecheck a `MulHom` as a morphism in `Semigrp`. -/
@[to_additive "Typecheck an `AddHom` as a morphism in `AddSemigrp`. "]
abbrev ofHom {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X →ₙ* Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := Semigrp) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (X Y : Semigrp.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)
initialize_simps_projections AddSemigrp.Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[to_additive (attr := simp)]
lemma coe_id {X : Semigrp} : (𝟙 X : X → X) = id := rfl

@[to_additive (attr := simp)]
lemma coe_comp {X Y Z : Semigrp} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[to_additive (attr := deprecated "Use hom_comp instead" (since := "2025-01-28"))]
lemma comp_def {X Y Z : Semigrp} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g).hom = g.hom.comp f.hom := rfl

@[simp] lemma forget_map {X Y : Semigrp} (f : X ⟶ Y) : (forget Semigrp).map f = (f : X → Y) := rfl

@[to_additive (attr := ext)]
lemma ext {X Y : Semigrp} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[to_additive]
-- This is not `simp` to avoid rewriting in types of terms.
theorem coe_of (R : Type u) [Semigroup R] : ↑(Semigrp.of R) = R :=
  rfl

@[to_additive (attr := simp)]
lemma hom_id {X : Semigrp} : (𝟙 X : X ⟶ X).hom = MulHom.id X := rfl

/- Provided for rewriting. -/
@[to_additive]
lemma id_apply (X : Semigrp) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[to_additive (attr := simp)]
lemma hom_comp {X Y T : Semigrp} (f : X ⟶ Y) (g : Y ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
@[to_additive]
lemma comp_apply {X Y T : Semigrp} (f : X ⟶ Y) (g : Y ⟶ T) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[to_additive (attr := ext)]
lemma hom_ext {X Y : Semigrp} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[to_additive (attr := simp)]
lemma hom_ofHom {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X →ₙ* Y) : (ofHom f).hom = f := rfl

@[to_additive (attr := simp)]
lemma ofHom_hom {X Y : Semigrp} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[to_additive (attr := simp)]
lemma ofHom_id {X : Type u} [Semigroup X] : ofHom (MulHom.id X) = 𝟙 (of X) := rfl

@[to_additive (attr := simp)]
lemma ofHom_comp {X Y Z : Type u} [Semigroup X] [Semigroup Y] [Semigroup Z]
    (f : X →ₙ* Y) (g : Y →ₙ* Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

@[to_additive]
lemma ofHom_apply {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X →ₙ* Y) (x : X) :
    (ofHom f) x = f x := rfl

@[to_additive]
lemma inv_hom_apply {X Y : Semigrp} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

@[to_additive]
lemma hom_inv_apply {X Y : Semigrp} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

@[to_additive (attr := simp)]
lemma mulEquiv_coe_eq {X Y : Type _} [Semigroup X] [Semigroup Y] (e : X ≃* Y) :
    (ofHom (e : X →ₙ* Y)).hom = ↑e :=
  rfl

@[to_additive]
instance : Inhabited Semigrp :=
  ⟨Semigrp.of PEmpty⟩

@[to_additive]
instance hasForgetToMagmaCat : HasForget₂ Semigrp MagmaCat where
  forget₂ :=
    { obj R := MagmaCat.of R
      map f := MagmaCat.ofHom f.hom }

end Semigrp

variable {X Y : Type u}

section

variable [Mul X] [Mul Y]

/-- Build an isomorphism in the category `MagmaCat` from a `MulEquiv` between `Mul`s. -/
@[to_additive (attr := simps)
      "Build an isomorphism in the category `AddMagmaCat` from an `AddEquiv` between `Add`s."]
def MulEquiv.toMagmaCatIso (e : X ≃* Y) : MagmaCat.of X ≅ MagmaCat.of Y where
  hom := MagmaCat.ofHom e.toMulHom
  inv := MagmaCat.ofHom e.symm.toMulHom

end

section

variable [Semigroup X] [Semigroup Y]

/-- Build an isomorphism in the category `Semigroup` from a `MulEquiv` between `Semigroup`s. -/
@[to_additive (attr := simps)
  "Build an isomorphism in the category
  `AddSemigroup` from an `AddEquiv` between `AddSemigroup`s."]
def MulEquiv.toSemigrpIso (e : X ≃* Y) : Semigrp.of X ≅ Semigrp.of Y where
  hom := Semigrp.ofHom e.toMulHom
  inv := Semigrp.ofHom e.symm.toMulHom

end

namespace CategoryTheory.Iso

/-- Build a `MulEquiv` from an isomorphism in the category `MagmaCat`. -/
@[to_additive
      "Build an `AddEquiv` from an isomorphism in the category `AddMagmaCat`."]
def magmaCatIsoToMulEquiv {X Y : MagmaCat} (i : X ≅ Y) : X ≃* Y :=
  MulHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

/-- Build a `MulEquiv` from an isomorphism in the category `Semigroup`. -/
@[to_additive
  "Build an `AddEquiv` from an isomorphism in the category `AddSemigroup`."]
def semigrpIsoToMulEquiv {X Y : Semigrp} (i : X ≅ Y) : X ≃* Y :=
  MulHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

end CategoryTheory.Iso

/-- multiplicative equivalences between `Mul`s are the same as (isomorphic to) isomorphisms
in `MagmaCat` -/
@[to_additive
    "additive equivalences between `Add`s are the same
    as (isomorphic to) isomorphisms in `AddMagmaCat`"]
def mulEquivIsoMagmaIso {X Y : Type u} [Mul X] [Mul Y] :
    X ≃* Y ≅ MagmaCat.of X ≅ MagmaCat.of Y where
  hom e := e.toMagmaCatIso
  inv i := i.magmaCatIsoToMulEquiv

/-- multiplicative equivalences between `Semigroup`s are the same as (isomorphic to) isomorphisms
in `Semigroup` -/
@[to_additive
  "additive equivalences between `AddSemigroup`s are
  the same as (isomorphic to) isomorphisms in `AddSemigroup`"]
def mulEquivIsoSemigrpIso {X Y : Type u} [Semigroup X] [Semigroup Y] :
    X ≃* Y ≅ Semigrp.of X ≅ Semigrp.of Y where
  hom e := e.toSemigrpIso
  inv i := i.semigrpIsoToMulEquiv

@[to_additive]
instance MagmaCat.forgetReflectsIsos : (forget MagmaCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget MagmaCat).map f)
    let e : X ≃* Y := { f.hom, i.toEquiv with }
    exact e.toMagmaCatIso.isIso_hom

@[to_additive]
instance Semigrp.forgetReflectsIsos : (forget Semigrp.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget Semigrp).map f)
    let e : X ≃* Y := { f.hom, i.toEquiv with }
    exact e.toSemigrpIso.isIso_hom

/--
Ensure that `forget₂ CommMonCat MonCat` automatically reflects isomorphisms.
We could have used `CategoryTheory.HasForget.ReflectsIso` alternatively.
-/
@[to_additive]
instance Semigrp.forget₂_full : (forget₂ Semigrp MagmaCat).Full where
  map_surjective f := ⟨ofHom f.hom, rfl⟩

/-!
Once we've shown that the forgetful functors to type reflect isomorphisms,
we automatically obtain that the `forget₂` functors between our concrete categories
reflect isomorphisms.
-/

example : (forget₂ Semigrp MagmaCat).ReflectsIsomorphisms := inferInstance
