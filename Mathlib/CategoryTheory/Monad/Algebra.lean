/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.monad.algebra
! leanprover-community/mathlib commit 14b69e9f3c16630440a2cbd46f1ddad0d561dee7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Monad.Basic
import Mathbin.CategoryTheory.Adjunction.Basic
import Mathbin.CategoryTheory.Functor.EpiMono

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


namespace CategoryTheory

open Category

universe v₁ u₁

-- morphism levels before object levels. See note [category_theory universes].
variable {C : Type u₁} [Category.{v₁} C]

namespace Monad

/-- An Eilenberg-Moore algebra for a monad `T`.
    cf Definition 5.2.3 in [Riehl][riehl2017]. -/
structure Algebra (T : Monad C) : Type max u₁ v₁ where
  a : C
  a : (T : C ⥤ C).obj A ⟶ A
  unit' : T.η.app A ≫ a = 𝟙 A := by obviously
  assoc' : T.μ.app A ≫ a = (T : C ⥤ C).map a ≫ a := by obviously
#align category_theory.monad.algebra CategoryTheory.Monad.Algebra

restate_axiom algebra.unit'

restate_axiom algebra.assoc'

attribute [reassoc.1] algebra.unit algebra.assoc

namespace Algebra

variable {T : Monad C}

/-- A morphism of Eilenberg–Moore algebras for the monad `T`. -/
@[ext]
structure Hom (A B : Algebra T) where
  f : A.a ⟶ B.a
  h' : (T : C ⥤ C).map f ≫ B.a = A.a ≫ f := by obviously
#align category_theory.monad.algebra.hom CategoryTheory.Monad.Algebra.Hom

restate_axiom hom.h'

attribute [simp, reassoc.1] hom.h

namespace Hom

/-- The identity homomorphism for an Eilenberg–Moore algebra. -/
def id (A : Algebra T) : Hom A A where f := 𝟙 A.a
#align category_theory.monad.algebra.hom.id CategoryTheory.Monad.Algebra.Hom.id

instance (A : Algebra T) : Inhabited (Hom A A) :=
  ⟨{ f := 𝟙 _ }⟩

/-- Composition of Eilenberg–Moore algebra homomorphisms. -/
def comp {P Q R : Algebra T} (f : Hom P Q) (g : Hom Q R) : Hom P R where f := f.f ≫ g.f
#align category_theory.monad.algebra.hom.comp CategoryTheory.Monad.Algebra.Hom.comp

end Hom

instance : CategoryStruct (Algebra T) where
  Hom := Hom
  id := Hom.id
  comp := @Hom.comp _ _ _

@[simp]
theorem comp_eq_comp {A A' A'' : Algebra T} (f : A ⟶ A') (g : A' ⟶ A'') :
    Algebra.Hom.comp f g = f ≫ g :=
  rfl
#align category_theory.monad.algebra.comp_eq_comp CategoryTheory.Monad.Algebra.comp_eq_comp

@[simp]
theorem id_eq_id (A : Algebra T) : Algebra.Hom.id A = 𝟙 A :=
  rfl
#align category_theory.monad.algebra.id_eq_id CategoryTheory.Monad.Algebra.id_eq_id

@[simp]
theorem id_f (A : Algebra T) : (𝟙 A : A ⟶ A).f = 𝟙 A.a :=
  rfl
#align category_theory.monad.algebra.id_f CategoryTheory.Monad.Algebra.id_f

@[simp]
theorem comp_f {A A' A'' : Algebra T} (f : A ⟶ A') (g : A' ⟶ A'') : (f ≫ g).f = f.f ≫ g.f :=
  rfl
#align category_theory.monad.algebra.comp_f CategoryTheory.Monad.Algebra.comp_f

/-- The category of Eilenberg-Moore algebras for a monad.
    cf Definition 5.2.4 in [Riehl][riehl2017]. -/
instance eilenbergMoore : Category (Algebra T) where
#align category_theory.monad.algebra.EilenbergMoore CategoryTheory.Monad.Algebra.eilenbergMoore

/--
To construct an isomorphism of algebras, it suffices to give an isomorphism of the carriers which
commutes with the structure morphisms.
-/
@[simps]
def isoMk {A B : Algebra T} (h : A.a ≅ B.a) (w : (T : C ⥤ C).map h.Hom ≫ B.a = A.a ≫ h.Hom) : A ≅ B
    where
  Hom := { f := h.Hom }
  inv :=
    { f := h.inv
      h' := by
        rw [h.eq_comp_inv, category.assoc, ← w, ← functor.map_comp_assoc]
        simp }
#align category_theory.monad.algebra.iso_mk CategoryTheory.Monad.Algebra.isoMk

end Algebra

variable (T : Monad C)

/-- The forgetful functor from the Eilenberg-Moore category, forgetting the algebraic structure. -/
@[simps]
def forget : Algebra T ⥤ C where
  obj A := A.a
  map A B f := f.f
#align category_theory.monad.forget CategoryTheory.Monad.forget

/-- The free functor from the Eilenberg-Moore category, constructing an algebra for any object. -/
@[simps]
def free : C ⥤ Algebra T
    where
  obj X :=
    { a := T.obj X
      a := T.μ.app X
      assoc' := (T.and_assoc _).symm }
  map X Y f :=
    { f := T.map f
      h' := T.μ.naturality _ }
#align category_theory.monad.free CategoryTheory.Monad.free

instance [Inhabited C] : Inhabited (Algebra T) :=
  ⟨(free T).obj default⟩

-- The other two `simps` projection lemmas can be derived from these two, so `simp_nf` complains if
-- those are added too
/-- The adjunction between the free and forgetful constructions for Eilenberg-Moore algebras for
  a monad. cf Lemma 5.2.8 of [Riehl][riehl2017]. -/
@[simps Unit counit]
def adj : T.free ⊣ T.forget :=
  Adjunction.mkOfHomEquiv
    {
      homEquiv := fun X Y =>
        { toFun := fun f => T.η.app X ≫ f.f
          invFun := fun f =>
            { f := T.map f ≫ Y.a
              h' := by
                dsimp
                simp [← Y.assoc, ← T.μ.naturality_assoc] }
          left_inv := fun f => by
            ext
            dsimp
            simp
          right_inv := fun f =>
            by
            dsimp only [forget_obj, monad_to_functor_eq_coe]
            rw [← T.η.naturality_assoc, Y.unit]
            apply category.comp_id } }
#align category_theory.monad.adj CategoryTheory.Monad.adj

/-- Given an algebra morphism whose carrier part is an isomorphism, we get an algebra isomorphism.
-/
theorem algebra_iso_of_iso {A B : Algebra T} (f : A ⟶ B) [IsIso f.f] : IsIso f :=
  ⟨⟨{   f := inv f.f
        h' := by
          rw [is_iso.eq_comp_inv f.f, category.assoc, ← f.h]
          simp },
      by tidy⟩⟩
#align category_theory.monad.algebra_iso_of_iso CategoryTheory.Monad.algebra_iso_of_iso

instance forget_reflects_iso : ReflectsIsomorphisms T.forget
    where reflects A B := algebra_iso_of_iso T
#align category_theory.monad.forget_reflects_iso CategoryTheory.Monad.forget_reflects_iso

instance forget_faithful : Faithful T.forget where
#align category_theory.monad.forget_faithful CategoryTheory.Monad.forget_faithful

/-- Given an algebra morphism whose carrier part is an epimorphism, we get an algebra epimorphism.
-/
theorem algebra_epi_of_epi {X Y : Algebra T} (f : X ⟶ Y) [h : Epi f.f] : Epi f :=
  (forget T).epi_of_epi_map h
#align category_theory.monad.algebra_epi_of_epi CategoryTheory.Monad.algebra_epi_of_epi

/-- Given an algebra morphism whose carrier part is a monomorphism, we get an algebra monomorphism.
-/
theorem algebra_mono_of_mono {X Y : Algebra T} (f : X ⟶ Y) [h : Mono f.f] : Mono f :=
  (forget T).mono_of_mono_map h
#align category_theory.monad.algebra_mono_of_mono CategoryTheory.Monad.algebra_mono_of_mono

instance : IsRightAdjoint T.forget :=
  ⟨T.free, T.adj⟩

@[simp]
theorem leftAdjoint_forget : leftAdjoint T.forget = T.free :=
  rfl
#align category_theory.monad.left_adjoint_forget CategoryTheory.Monad.leftAdjoint_forget

@[simp]
theorem ofRightAdjoint_forget : Adjunction.ofRightAdjoint T.forget = T.adj :=
  rfl
#align category_theory.monad.of_right_adjoint_forget CategoryTheory.Monad.ofRightAdjoint_forget

/--
Given a monad morphism from `T₂` to `T₁`, we get a functor from the algebras of `T₁` to algebras of
`T₂`.
-/
@[simps]
def algebraFunctorOfMonadHom {T₁ T₂ : Monad C} (h : T₂ ⟶ T₁) : Algebra T₁ ⥤ Algebra T₂
    where
  obj A :=
    { a := A.a
      a := h.app A.a ≫ A.a
      unit' := by
        dsimp
        simp [A.unit]
      assoc' := by
        dsimp
        simp [A.assoc] }
  map A₁ A₂ f := { f := f.f }
#align category_theory.monad.algebra_functor_of_monad_hom CategoryTheory.Monad.algebraFunctorOfMonadHom

/--
The identity monad morphism induces the identity functor from the category of algebras to itself.
-/
@[simps (config := { rhsMd := semireducible })]
def algebraFunctorOfMonadHomId {T₁ : Monad C} : algebraFunctorOfMonadHom (𝟙 T₁) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun X =>
      Algebra.isoMk (Iso.refl _)
        (by
          dsimp
          simp))
    fun X Y f => by
    ext
    dsimp
    simp
#align category_theory.monad.algebra_functor_of_monad_hom_id CategoryTheory.Monad.algebraFunctorOfMonadHomId

/-- A composition of monad morphisms gives the composition of corresponding functors.
-/
@[simps (config := { rhsMd := semireducible })]
def algebraFunctorOfMonadHomComp {T₁ T₂ T₃ : Monad C} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    algebraFunctorOfMonadHom (f ≫ g) ≅ algebraFunctorOfMonadHom g ⋙ algebraFunctorOfMonadHom f :=
  NatIso.ofComponents
    (fun X =>
      Algebra.isoMk (Iso.refl _)
        (by
          dsimp
          simp))
    fun X Y f => by
    ext
    dsimp
    simp
#align category_theory.monad.algebra_functor_of_monad_hom_comp CategoryTheory.Monad.algebraFunctorOfMonadHomComp

/-- If `f` and `g` are two equal morphisms of monads, then the functors of algebras induced by them
are isomorphic.
We define it like this as opposed to using `eq_to_iso` so that the components are nicer to prove
lemmas about.
-/
@[simps (config := { rhsMd := semireducible })]
def algebraFunctorOfMonadHomEq {T₁ T₂ : Monad C} {f g : T₁ ⟶ T₂} (h : f = g) :
    algebraFunctorOfMonadHom f ≅ algebraFunctorOfMonadHom g :=
  NatIso.ofComponents
    (fun X =>
      Algebra.isoMk (Iso.refl _)
        (by
          dsimp
          simp [h]))
    fun X Y f => by
    ext
    dsimp
    simp
#align category_theory.monad.algebra_functor_of_monad_hom_eq CategoryTheory.Monad.algebraFunctorOfMonadHomEq

/-- Isomorphic monads give equivalent categories of algebras. Furthermore, they are equivalent as
categories over `C`, that is, we have `algebra_equiv_of_iso_monads h ⋙ forget = forget`.
-/
@[simps]
def algebraEquivOfIsoMonads {T₁ T₂ : Monad C} (h : T₁ ≅ T₂) : Algebra T₁ ≌ Algebra T₂
    where
  Functor := algebraFunctorOfMonadHom h.inv
  inverse := algebraFunctorOfMonadHom h.Hom
  unitIso :=
    algebraFunctorOfMonadHomId.symm ≪≫
      algebraFunctorOfMonadHomEq (by simp) ≪≫ algebraFunctorOfMonadHomComp _ _
  counitIso :=
    (algebraFunctorOfMonadHomComp _ _).symm ≪≫
      algebraFunctorOfMonadHomEq (by simp) ≪≫ algebraFunctorOfMonadHomId
#align category_theory.monad.algebra_equiv_of_iso_monads CategoryTheory.Monad.algebraEquivOfIsoMonads

@[simp]
theorem algebra_equiv_of_iso_monads_comp_forget {T₁ T₂ : Monad C} (h : T₁ ⟶ T₂) :
    algebraFunctorOfMonadHom h ⋙ forget _ = forget _ :=
  rfl
#align category_theory.monad.algebra_equiv_of_iso_monads_comp_forget CategoryTheory.Monad.algebra_equiv_of_iso_monads_comp_forget

end Monad

namespace Comonad

/-- An Eilenberg-Moore coalgebra for a comonad `T`. -/
@[nolint has_nonempty_instance]
structure Coalgebra (G : Comonad C) : Type max u₁ v₁ where
  a : C
  a : A ⟶ (G : C ⥤ C).obj A
  counit' : a ≫ G.ε.app A = 𝟙 A := by obviously
  coassoc' : a ≫ G.δ.app A = a ≫ G.map a := by obviously
#align category_theory.comonad.coalgebra CategoryTheory.Comonad.Coalgebra

restate_axiom coalgebra.counit'

restate_axiom coalgebra.coassoc'

attribute [reassoc.1] coalgebra.counit coalgebra.coassoc

namespace Coalgebra

variable {G : Comonad C}

/-- A morphism of Eilenberg-Moore coalgebras for the comonad `G`. -/
@[ext, nolint has_nonempty_instance]
structure Hom (A B : Coalgebra G) where
  f : A.a ⟶ B.a
  h' : A.a ≫ (G : C ⥤ C).map f = f ≫ B.a := by obviously
#align category_theory.comonad.coalgebra.hom CategoryTheory.Comonad.Coalgebra.Hom

restate_axiom hom.h'

attribute [simp, reassoc.1] hom.h

namespace Hom

/-- The identity homomorphism for an Eilenberg–Moore coalgebra. -/
def id (A : Coalgebra G) : Hom A A where f := 𝟙 A.a
#align category_theory.comonad.coalgebra.hom.id CategoryTheory.Comonad.Coalgebra.Hom.id

/-- Composition of Eilenberg–Moore coalgebra homomorphisms. -/
def comp {P Q R : Coalgebra G} (f : Hom P Q) (g : Hom Q R) : Hom P R where f := f.f ≫ g.f
#align category_theory.comonad.coalgebra.hom.comp CategoryTheory.Comonad.Coalgebra.Hom.comp

end Hom

/-- The category of Eilenberg-Moore coalgebras for a comonad. -/
instance : CategoryStruct (Coalgebra G) where
  Hom := Hom
  id := Hom.id
  comp := @Hom.comp _ _ _

@[simp]
theorem comp_eq_comp {A A' A'' : Coalgebra G} (f : A ⟶ A') (g : A' ⟶ A'') :
    Coalgebra.Hom.comp f g = f ≫ g :=
  rfl
#align category_theory.comonad.coalgebra.comp_eq_comp CategoryTheory.Comonad.Coalgebra.comp_eq_comp

@[simp]
theorem id_eq_id (A : Coalgebra G) : Coalgebra.Hom.id A = 𝟙 A :=
  rfl
#align category_theory.comonad.coalgebra.id_eq_id CategoryTheory.Comonad.Coalgebra.id_eq_id

@[simp]
theorem id_f (A : Coalgebra G) : (𝟙 A : A ⟶ A).f = 𝟙 A.a :=
  rfl
#align category_theory.comonad.coalgebra.id_f CategoryTheory.Comonad.Coalgebra.id_f

@[simp]
theorem comp_f {A A' A'' : Coalgebra G} (f : A ⟶ A') (g : A' ⟶ A'') : (f ≫ g).f = f.f ≫ g.f :=
  rfl
#align category_theory.comonad.coalgebra.comp_f CategoryTheory.Comonad.Coalgebra.comp_f

/-- The category of Eilenberg-Moore coalgebras for a comonad. -/
instance eilenbergMoore : Category (Coalgebra G) where
#align category_theory.comonad.coalgebra.EilenbergMoore CategoryTheory.Comonad.Coalgebra.eilenbergMoore

/--
To construct an isomorphism of coalgebras, it suffices to give an isomorphism of the carriers which
commutes with the structure morphisms.
-/
@[simps]
def isoMk {A B : Coalgebra G} (h : A.a ≅ B.a) (w : A.a ≫ (G : C ⥤ C).map h.Hom = h.Hom ≫ B.a) :
    A ≅ B where
  Hom := { f := h.Hom }
  inv :=
    { f := h.inv
      h' := by
        rw [h.eq_inv_comp, ← reassoc_of w, ← functor.map_comp]
        simp }
#align category_theory.comonad.coalgebra.iso_mk CategoryTheory.Comonad.Coalgebra.isoMk

end Coalgebra

variable (G : Comonad C)

/-- The forgetful functor from the Eilenberg-Moore category, forgetting the coalgebraic
structure. -/
@[simps]
def forget : Coalgebra G ⥤ C where
  obj A := A.a
  map A B f := f.f
#align category_theory.comonad.forget CategoryTheory.Comonad.forget

/-- The cofree functor from the Eilenberg-Moore category, constructing a coalgebra for any
object. -/
@[simps]
def cofree : C ⥤ Coalgebra G
    where
  obj X :=
    { a := G.obj X
      a := G.δ.app X
      coassoc' := (G.coassoc _).symm }
  map X Y f :=
    { f := G.map f
      h' := (G.δ.naturality _).symm }
#align category_theory.comonad.cofree CategoryTheory.Comonad.cofree

-- The other two `simps` projection lemmas can be derived from these two, so `simp_nf` complains if
-- those are added too
/-- The adjunction between the cofree and forgetful constructions for Eilenberg-Moore coalgebras
for a comonad.
-/
@[simps Unit counit]
def adj : G.forget ⊣ G.cofree :=
  Adjunction.mkOfHomEquiv
    {
      homEquiv := fun X Y =>
        { toFun := fun f =>
            { f := X.a ≫ G.map f
              h' := by
                dsimp
                simp [← coalgebra.coassoc_assoc] }
          invFun := fun g => g.f ≫ G.ε.app Y
          left_inv := fun f => by
            dsimp
            rw [category.assoc, G.ε.naturality, functor.id_map, X.counit_assoc]
          right_inv := fun g => by
            ext1; dsimp
            rw [functor.map_comp, g.h_assoc, cofree_obj_a, comonad.right_counit]
            apply comp_id } }
#align category_theory.comonad.adj CategoryTheory.Comonad.adj

/-- Given a coalgebra morphism whose carrier part is an isomorphism, we get a coalgebra isomorphism.
-/
theorem coalgebra_iso_of_iso {A B : Coalgebra G} (f : A ⟶ B) [IsIso f.f] : IsIso f :=
  ⟨⟨{   f := inv f.f
        h' := by
          rw [is_iso.eq_inv_comp f.f, ← f.h_assoc]
          simp },
      by tidy⟩⟩
#align category_theory.comonad.coalgebra_iso_of_iso CategoryTheory.Comonad.coalgebra_iso_of_iso

instance forget_reflects_iso : ReflectsIsomorphisms G.forget
    where reflects A B := coalgebra_iso_of_iso G
#align category_theory.comonad.forget_reflects_iso CategoryTheory.Comonad.forget_reflects_iso

instance forget_faithful : Faithful (forget G) where
#align category_theory.comonad.forget_faithful CategoryTheory.Comonad.forget_faithful

/-- Given a coalgebra morphism whose carrier part is an epimorphism, we get an algebra epimorphism.
-/
theorem algebra_epi_of_epi {X Y : Coalgebra G} (f : X ⟶ Y) [h : Epi f.f] : Epi f :=
  (forget G).epi_of_epi_map h
#align category_theory.comonad.algebra_epi_of_epi CategoryTheory.Comonad.algebra_epi_of_epi

/-- Given a coalgebra morphism whose carrier part is a monomorphism, we get an algebra monomorphism.
-/
theorem algebra_mono_of_mono {X Y : Coalgebra G} (f : X ⟶ Y) [h : Mono f.f] : Mono f :=
  (forget G).mono_of_mono_map h
#align category_theory.comonad.algebra_mono_of_mono CategoryTheory.Comonad.algebra_mono_of_mono

instance : IsLeftAdjoint G.forget :=
  ⟨_, G.adj⟩

@[simp]
theorem rightAdjoint_forget : rightAdjoint G.forget = G.cofree :=
  rfl
#align category_theory.comonad.right_adjoint_forget CategoryTheory.Comonad.rightAdjoint_forget

@[simp]
theorem ofLeftAdjoint_forget : Adjunction.ofLeftAdjoint G.forget = G.adj :=
  rfl
#align category_theory.comonad.of_left_adjoint_forget CategoryTheory.Comonad.ofLeftAdjoint_forget

end Comonad

end CategoryTheory

