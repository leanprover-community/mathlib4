/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Eilenberg-Moore (co)algebras for a (co)monad

This file defines Eilenberg-Moore (co)algebras for a (co)monad,
and provides the category instance for them.

Further it defines the adjoint pair of free and forgetful functors, respectively
from and to the original category, as well as the adjoint pair of forgetful and
cofree functors, respectively from and to the original category.

## References
* [Riehl, *Category theory in context*, Section 5.2.4][riehl2017]
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section


namespace CategoryTheory

open Category

universe v₁ u₁

-- morphism levels before object levels. See note [category_theory universes].
variable {C : Type u₁} [Category.{v₁} C]

to_dual_name_hint Algebra Coalgebra, Free Cofree, Mono Epi, Right Left

/-- An Eilenberg-Moore algebra for a monad `T`.
cf Definition 5.2.3 in [Riehl][riehl2017]. -/
structure Monad.Algebra (T : Monad C) : Type max u₁ v₁ where
  /-- The underlying object associated to an algebra. -/
  A : C
  /-- The structure morphism associated to an algebra. -/
  a : (T : C ⥤ C).obj A ⟶ A
  /-- The unit axiom associated to an algebra. -/
  unit : T.η.app A ≫ a = 𝟙 A := by cat_disch
  /-- The associativity axiom associated to an algebra. -/
  assoc : T.μ.app A ≫ a = (T : C ⥤ C).map a ≫ a := by cat_disch

/-- An Eilenberg-Moore coalgebra for a comonad `T`. -/
@[to_dual]
structure Comonad.Coalgebra (T : Comonad C) : Type max u₁ v₁ where
  /-- The underlying object associated to a coalgebra. -/
  A : C
  /-- The structure morphism associated to a coalgebra. -/
  a : A ⟶ (T : C ⥤ C).obj A
  /-- The counit axiom associated to a coalgebra. -/
  counit : a ≫ T.ε.app A = 𝟙 A := by cat_disch
  /-- The coassociativity axiom associated to a coalgebra. -/
  coassoc : a ≫ T.δ.app A = a ≫ T.map a := by cat_disch

attribute [reassoc] Monad.Algebra.unit Monad.Algebra.assoc
attribute [reassoc] Comonad.Coalgebra.counit Comonad.Coalgebra.coassoc

/-- A morphism of Eilenberg–Moore algebras for the monad `T`. -/
@[ext]
structure Monad.Algebra.Hom {T : Monad C} (A B : Algebra T) where
  /-- The underlying morphism associated to a morphism of algebras. -/
  f : A.A ⟶ B.A
  /-- Compatibility with the structure morphism, for a morphism of algebras. -/
  h : (T : C ⥤ C).map f ≫ B.a = A.a ≫ f := by cat_disch

/-- A morphism of Eilenberg-Moore coalgebras for the comonad `T`. -/
@[ext, to_dual (reorder := A B)]
structure Comonad.Coalgebra.Hom {T : Comonad C} (A B : Coalgebra T) where
  /-- The underlying morphism associated to a morphism of coalgebras. -/
  f : A.A ⟶ B.A
  /-- Compatibility with the structure morphism, for a morphism of coalgebras. -/
  h : A.a ≫ (T : C ⥤ C).map f = f ≫ B.a := by cat_disch

attribute [to_dual existing] Monad.Algebra.Hom.ext
attribute [reassoc (attr := simp)] Monad.Algebra.Hom.h Comonad.Coalgebra.Hom.h

namespace Monad.Algebra

variable {T : Monad C}

namespace Hom

/-- The identity homomorphism for an Eilenberg–Moore algebra. -/
@[to_dual /-- The identity homomorphism for an Eilenberg–Moore coalgebra. -/]
def id (A : Algebra T) : Hom A A where f := 𝟙 A.A

instance (A : Algebra T) : Inhabited (Hom A A) :=
  ⟨{ f := 𝟙 _ }⟩

/-- Composition of Eilenberg–Moore algebra homomorphisms. -/
@[to_dual (reorder := f g) /-- Composition of Eilenberg–Moore coalgebra homomorphisms. -/]
def comp {P Q R : Algebra T} (f : Hom P Q) (g : Hom Q R) : Hom P R where f := f.f ≫ g.f

end Hom

@[to_dual]
instance : CategoryStruct (Algebra T) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[to_dual (attr := ext)]
lemma Hom.ext' (X Y : Algebra T) (f g : X ⟶ Y) (h : f.f = g.f) : f = g := Hom.ext h

@[to_dual (attr := simp) (reorder := f g)]
theorem comp_eq_comp {A A' A'' : Algebra T} (f : A ⟶ A') (g : A' ⟶ A'') :
    Algebra.Hom.comp f g = f ≫ g :=
  rfl

@[to_dual (attr := simp)]
theorem id_eq_id (A : Algebra T) : Algebra.Hom.id A = 𝟙 A :=
  rfl

@[to_dual (attr := simp)]
theorem id_f (A : Algebra T) : (𝟙 A : A ⟶ A).f = 𝟙 A.A :=
  rfl

@[to_dual (attr := simp) (reorder := f g)]
theorem comp_f {A A' A'' : Algebra T} (f : A ⟶ A') (g : A' ⟶ A'') : (f ≫ g).f = f.f ≫ g.f :=
  rfl

/-- The category of Eilenberg-Moore algebras for a monad.
cf Definition 5.2.4 in [Riehl][riehl2017]. -/
@[to_dual /-- The category of Eilenberg-Moore coalgebras for a comonad. -/]
instance eilenbergMoore : Category (Algebra T) where

/--
To construct an isomorphism of algebras, it suffices to give an isomorphism of the carriers which
commutes with the structure morphisms.
-/
@[to_dual (attr := simps)
/--
To construct an isomorphism of coalgebras, it suffices to give an isomorphism of the carriers which
commutes with the structure morphisms.
-/]
def isoMk {A B : Algebra T} (h : A.A ≅ B.A)
    (w : (T : C ⥤ C).map h.hom ≫ B.a = A.a ≫ h.hom := by cat_disch) : A ≅ B where
  hom := { f := h.hom }
  inv :=
    { f := h.inv
      h := by
        rw [h.eq_comp_inv, Category.assoc, ← w, ← Functor.map_comp_assoc]
        simp }

end Algebra

variable (T : Monad C)

/-- The forgetful functor from the Eilenberg-Moore category, forgetting the algebraic structure. -/
@[to_dual (attr := simps, implicit_reducible)
/-- The forgetful functor from the Eilenberg-Moore category, forgetting the coalgebraic
structure. -/]
def forget : Algebra T ⥤ C where
  obj A := A.A
  map f := f.f

/-- The free functor from the Eilenberg-Moore category, constructing an algebra for any object. -/
@[to_dual (attr := simps, implicit_reducible)
/-- The cofree functor from the Eilenberg-Moore category, constructing a coalgebra for any
object. -/]
def free : C ⥤ Algebra T where
  obj X :=
    { A := T.obj X
      a := T.μ.app X
      assoc := (T.assoc _).symm }
  map f :=
    { f := T.map f
      h := T.μ.naturality _ }

@[to_dual]
instance [Inhabited C] : Inhabited (Algebra T) :=
  ⟨(free T).obj default⟩

-- The other two `simps` projection lemmas can be derived from these two, so `simp_nf` complains if
-- those are added too
/-- The adjunction between the free and forgetful constructions for Eilenberg-Moore algebras for
  a monad. cf Lemma 5.2.8 of [Riehl][riehl2017]. -/
@[simps! unit counit]
def adj : T.free ⊣ T.forget :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => T.η.app X ≫ f.f
          invFun := fun f =>
            { f := T.map f ≫ Y.a
              h := by simp [← Y.assoc, ← T.μ.naturality_assoc] }
          left_inv := fun f => by
            ext
            simp
          right_inv := fun f => by
            dsimp only [forget_obj]
            rw [← T.η.naturality_assoc, Y.unit]
            apply Category.comp_id } }

open Comonad in
/-- The adjunction between the cofree and forgetful constructions for Eilenberg-Moore coalgebras
for a comonad.
-/
@[simps! unit counit]
def _root_.CategoryTheory.Comonad.adj (T : Comonad C) : T.forget ⊣ T.cofree :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f =>
            { f := X.a ≫ T.map f
              h := by simp [← Coalgebra.coassoc_assoc] }
          invFun := fun g => g.f ≫ T.ε.app Y
          left_inv := fun f => by
            dsimp
            rw [Category.assoc, T.ε.naturality, Functor.id_map, X.counit_assoc]
          right_inv := fun g => by
            ext1; dsimp
            rw [Functor.map_comp, g.h_assoc, cofree_obj_a, Comonad.right_counit]
            apply comp_id } }

/-- Given an algebra morphism whose carrier part is an isomorphism, we get an algebra isomorphism.
-/
@[to_dual
/-- Given a coalgebra morphism whose carrier part is an isomorphism, we get a coalgebra isomorphism.
-/]
theorem algebra_iso_of_iso {A B : Algebra T} (f : A ⟶ B) [IsIso f.f] : IsIso f :=
  ⟨⟨{ f := inv f.f, h := by simp }, by cat_disch⟩⟩

@[to_dual]
instance forget_reflects_iso : T.forget.ReflectsIsomorphisms where
  reflects {_ _} f [IsIso f.f] := algebra_iso_of_iso T f

@[to_dual]
instance forget_faithful : T.forget.Faithful where

/-- Given an algebra morphism whose carrier part is an epimorphism, we get an algebra epimorphism.
-/
@[to_dual
/-- Given a coalgebra morphism whose carrier part is a monomorphism, we get an algebra monomorphism.
-/]
theorem algebra_epi_of_epi {X Y : Algebra T} (f : X ⟶ Y) [h : Epi f.f] : Epi f :=
  (forget T).epi_of_epi_map h

/-- Given an algebra morphism whose carrier part is a monomorphism, we get an algebra monomorphism.
-/
@[to_dual
/-- Given a coalgebra morphism whose carrier part is an epimorphism, we get an algebra epimorphism.
-/]
theorem algebra_mono_of_mono {X Y : Algebra T} (f : X ⟶ Y) [h : Mono f.f] : Mono f :=
  (forget T).mono_of_mono_map h

@[to_dual]
instance : T.forget.IsRightAdjoint :=
  ⟨T.free, ⟨T.adj⟩⟩

/--
Given a monad morphism from `T₂` to `T₁`, we get a functor from the algebras of `T₁` to algebras of
`T₂`.
-/
@[simps]
def algebraFunctorOfMonadHom {T₁ T₂ : Monad C} (h : T₂ ⟶ T₁) : Algebra T₁ ⥤ Algebra T₂ where
  obj A :=
    { A := A.A
      a := h.app A.A ≫ A.a
      unit := by simp [A.unit]
      assoc := by simp [A.assoc] }
  map f := { f := f.f }

set_option backward.isDefEq.respectTransparency.types false in
/--
The identity monad morphism induces the identity functor from the category of algebras to itself.
-/
@[simps (rhsMd := .default)]
def algebraFunctorOfMonadHomId {T₁ : Monad C} : algebraFunctorOfMonadHom (𝟙 T₁) ≅ 𝟭 _ :=
  NatIso.ofComponents fun X => Algebra.isoMk (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
/-- A composition of monad morphisms gives the composition of corresponding functors.
-/
@[simps (rhsMd := .default)]
def algebraFunctorOfMonadHomComp {T₁ T₂ T₃ : Monad C} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    algebraFunctorOfMonadHom (f ≫ g) ≅ algebraFunctorOfMonadHom g ⋙ algebraFunctorOfMonadHom f :=
  NatIso.ofComponents fun X => Algebra.isoMk (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
/-- If `f` and `g` are two equal morphisms of monads, then the functors of algebras induced by them
are isomorphic.
We define it like this as opposed to using `eqToIso` so that the components are nicer to prove
lemmas about.
-/
@[simps (rhsMd := .default)]
def algebraFunctorOfMonadHomEq {T₁ T₂ : Monad C} {f g : T₁ ⟶ T₂} (h : f = g) :
    algebraFunctorOfMonadHom f ≅ algebraFunctorOfMonadHom g :=
  NatIso.ofComponents fun X => Algebra.isoMk (Iso.refl _)

/-- Isomorphic monads give equivalent categories of algebras. Furthermore, they are equivalent as
categories over `C`, that is, we have `algebraEquivOfIsoMonads h ⋙ forget = forget`.
-/
@[simps]
def algebraEquivOfIsoMonads {T₁ T₂ : Monad C} (h : T₁ ≅ T₂) : Algebra T₁ ≌ Algebra T₂ where
  functor := algebraFunctorOfMonadHom h.inv
  inverse := algebraFunctorOfMonadHom h.hom
  unitIso :=
    algebraFunctorOfMonadHomId.symm ≪≫
      algebraFunctorOfMonadHomEq (by simp) ≪≫ algebraFunctorOfMonadHomComp _ _
  counitIso :=
    (algebraFunctorOfMonadHomComp _ _).symm ≪≫
      algebraFunctorOfMonadHomEq (by simp) ≪≫ algebraFunctorOfMonadHomId

@[simp]
theorem algebra_equiv_of_iso_monads_comp_forget {T₁ T₂ : Monad C} (h : T₁ ⟶ T₂) :
    algebraFunctorOfMonadHom h ⋙ forget _ = forget _ :=
  rfl

end Monad

@[deprecated (since := "2026-10-08")]
alias Comonad.algebra_epi_of_epi := Comonad.coalgebra_epi_of_epi
@[deprecated (since := "2026-10-08")]
alias Comonad.algebra_mono_of_mono := Comonad.coalgebra_mono_of_mono

end CategoryTheory
