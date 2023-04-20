/-
Copyright (c) 2022 Joseph Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta, Johan Commelin, Reid Barton, Rob Lewis, Joseph Hua

! This file was ported from Lean 3 source module category_theory.endofunctor.algebra
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Functor.ReflectsIsomorphisms
import Mathbin.CategoryTheory.Limits.Shapes.Terminal

/-!

# Algebras of endofunctors

This file defines (co)algebras of an endofunctor, and provides the category instance for them.
It also defines the forgetful functor from the category of (co)algebras. It is shown that the
structure map of the initial algebra of an endofunctor is an isomorphism. Furthermore, it is shown
that for an adjunction `F ⊣ G` the category of algebras over `F` is equivalent to the category of
coalgebras over `G`.

## TODO

* Prove the dual result about the structure map of the terminal coalgebra of an endofunctor.
* Prove that if the countable infinite product over the powers of the endofunctor exists, then
  algebras over the endofunctor coincide with algebras over the free monad on the endofunctor.
-/


universe v u

namespace CategoryTheory

namespace Endofunctor

variable {C : Type u} [Category.{v} C]

/-- An algebra of an endofunctor; `str` stands for "structure morphism" -/
structure Algebra (F : C ⥤ C) where
  a : C
  str : F.obj A ⟶ A
#align category_theory.endofunctor.algebra CategoryTheory.Endofunctor.Algebra

instance [Inhabited C] : Inhabited (Algebra (𝟭 C)) :=
  ⟨⟨default, 𝟙 _⟩⟩

namespace Algebra

variable {F : C ⥤ C} (A : Algebra F) {A₀ A₁ A₂ : Algebra F}

/-
```
        str
   F A₀ -----> A₀
    |          |
F f |          | f
    V          V
   F A₁ -----> A₁
        str
```
-/
/-- A morphism between algebras of endofunctor `F` -/
@[ext]
structure Hom (A₀ A₁ : Algebra F) where
  f : A₀.1 ⟶ A₁.1
  h' : F.map f ≫ A₁.str = A₀.str ≫ f := by obviously
#align category_theory.endofunctor.algebra.hom CategoryTheory.Endofunctor.Algebra.Hom

restate_axiom hom.h'

attribute [simp, reassoc.1] hom.h

namespace Hom

/-- The identity morphism of an algebra of endofunctor `F` -/
def id : Hom A A where f := 𝟙 _
#align category_theory.endofunctor.algebra.hom.id CategoryTheory.Endofunctor.Algebra.Hom.id

instance : Inhabited (Hom A A) :=
  ⟨{ f := 𝟙 _ }⟩

/-- The composition of morphisms between algebras of endofunctor `F` -/
def comp (f : Hom A₀ A₁) (g : Hom A₁ A₂) : Hom A₀ A₂ where f := f.1 ≫ g.1
#align category_theory.endofunctor.algebra.hom.comp CategoryTheory.Endofunctor.Algebra.Hom.comp

end Hom

instance (F : C ⥤ C) : CategoryStruct (Algebra F)
    where
  Hom := Hom
  id := Hom.id
  comp := @Hom.comp _ _ _

@[simp]
theorem id_eq_id : Algebra.Hom.id A = 𝟙 A :=
  rfl
#align category_theory.endofunctor.algebra.id_eq_id CategoryTheory.Endofunctor.Algebra.id_eq_id

@[simp]
theorem id_f : (𝟙 _ : A ⟶ A).1 = 𝟙 A.1 :=
  rfl
#align category_theory.endofunctor.algebra.id_f CategoryTheory.Endofunctor.Algebra.id_f

variable {A₀ A₁ A₂} (f : A₀ ⟶ A₁) (g : A₁ ⟶ A₂)

@[simp]
theorem comp_eq_comp : Algebra.Hom.comp f g = f ≫ g :=
  rfl
#align category_theory.endofunctor.algebra.comp_eq_comp CategoryTheory.Endofunctor.Algebra.comp_eq_comp

@[simp]
theorem comp_f : (f ≫ g).1 = f.1 ≫ g.1 :=
  rfl
#align category_theory.endofunctor.algebra.comp_f CategoryTheory.Endofunctor.Algebra.comp_f

/-- Algebras of an endofunctor `F` form a category -/
instance (F : C ⥤ C) : Category (Algebra F) where

/-- To construct an isomorphism of algebras, it suffices to give an isomorphism of the As which
commutes with the structure morphisms.
-/
@[simps]
def isoMk (h : A₀.1 ≅ A₁.1) (w : F.map h.Hom ≫ A₁.str = A₀.str ≫ h.Hom) : A₀ ≅ A₁
    where
  Hom := { f := h.Hom }
  inv :=
    { f := h.inv
      h' := by
        rw [h.eq_comp_inv, category.assoc, ← w, ← functor.map_comp_assoc]
        simp }
#align category_theory.endofunctor.algebra.iso_mk CategoryTheory.Endofunctor.Algebra.isoMk

/-- The forgetful functor from the category of algebras, forgetting the algebraic structure. -/
@[simps]
def forget (F : C ⥤ C) : Algebra F ⥤ C where
  obj A := A.1
  map A B f := f.1
#align category_theory.endofunctor.algebra.forget CategoryTheory.Endofunctor.Algebra.forget

/-- An algebra morphism with an underlying isomorphism hom in `C` is an algebra isomorphism. -/
theorem iso_of_iso (f : A₀ ⟶ A₁) [IsIso f.1] : IsIso f :=
  ⟨⟨{   f := inv f.1
        h' := by
          rw [is_iso.eq_comp_inv f.1, category.assoc, ← f.h]
          simp },
      by tidy⟩⟩
#align category_theory.endofunctor.algebra.iso_of_iso CategoryTheory.Endofunctor.Algebra.iso_of_iso

instance forget_reflects_iso : ReflectsIsomorphisms (forget F) where reflects A B := iso_of_iso
#align category_theory.endofunctor.algebra.forget_reflects_iso CategoryTheory.Endofunctor.Algebra.forget_reflects_iso

instance forget_faithful : Faithful (forget F) where
#align category_theory.endofunctor.algebra.forget_faithful CategoryTheory.Endofunctor.Algebra.forget_faithful

/-- An algebra morphism with an underlying epimorphism hom in `C` is an algebra epimorphism. -/
theorem epi_of_epi {X Y : Algebra F} (f : X ⟶ Y) [h : Epi f.1] : Epi f :=
  (forget F).epi_of_epi_map h
#align category_theory.endofunctor.algebra.epi_of_epi CategoryTheory.Endofunctor.Algebra.epi_of_epi

/-- An algebra morphism with an underlying monomorphism hom in `C` is an algebra monomorphism. -/
theorem mono_of_mono {X Y : Algebra F} (f : X ⟶ Y) [h : Mono f.1] : Mono f :=
  (forget F).mono_of_mono_map h
#align category_theory.endofunctor.algebra.mono_of_mono CategoryTheory.Endofunctor.Algebra.mono_of_mono

/-- From a natural transformation `α : G → F` we get a functor from
algebras of `F` to algebras of `G`.
-/
@[simps]
def functorOfNatTrans {F G : C ⥤ C} (α : G ⟶ F) : Algebra F ⥤ Algebra G
    where
  obj A :=
    { a := A.1
      str := α.app A.1 ≫ A.str }
  map A₀ A₁ f := { f := f.1 }
#align category_theory.endofunctor.algebra.functor_of_nat_trans CategoryTheory.Endofunctor.Algebra.functorOfNatTrans

/-- The identity transformation induces the identity endofunctor on the category of algebras. -/
@[simps (config := { rhsMd := semireducible })]
def functorOfNatTransId : functorOfNatTrans (𝟙 F) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun X =>
      isoMk (Iso.refl _)
        (by
          dsimp
          simp))
    fun X Y f => by
    ext
    dsimp
    simp
#align category_theory.endofunctor.algebra.functor_of_nat_trans_id CategoryTheory.Endofunctor.Algebra.functorOfNatTransId

/-- A composition of natural transformations gives the composition of corresponding functors. -/
@[simps (config := { rhsMd := semireducible })]
def functorOfNatTransComp {F₀ F₁ F₂ : C ⥤ C} (α : F₀ ⟶ F₁) (β : F₁ ⟶ F₂) :
    functorOfNatTrans (α ≫ β) ≅ functorOfNatTrans β ⋙ functorOfNatTrans α :=
  NatIso.ofComponents
    (fun X =>
      isoMk (Iso.refl _)
        (by
          dsimp
          simp))
    fun X Y f => by
    ext
    dsimp
    simp
#align category_theory.endofunctor.algebra.functor_of_nat_trans_comp CategoryTheory.Endofunctor.Algebra.functorOfNatTransComp

/--
If `α` and `β` are two equal natural transformations, then the functors of algebras induced by them
are isomorphic.
We define it like this as opposed to using `eq_to_iso` so that the components are nicer to prove
lemmas about.
-/
@[simps (config := { rhsMd := semireducible })]
def functorOfNatTransEq {F G : C ⥤ C} {α β : F ⟶ G} (h : α = β) :
    functorOfNatTrans α ≅ functorOfNatTrans β :=
  NatIso.ofComponents
    (fun X =>
      isoMk (Iso.refl _)
        (by
          dsimp
          simp [h]))
    fun X Y f => by
    ext
    dsimp
    simp
#align category_theory.endofunctor.algebra.functor_of_nat_trans_eq CategoryTheory.Endofunctor.Algebra.functorOfNatTransEq

/-- Naturally isomorphic endofunctors give equivalent categories of algebras.
Furthermore, they are equivalent as categories over `C`, that is,
we have `equiv_of_nat_iso h ⋙ forget = forget`.
-/
@[simps]
def equivOfNatIso {F G : C ⥤ C} (α : F ≅ G) : Algebra F ≌ Algebra G
    where
  Functor := functorOfNatTrans α.inv
  inverse := functorOfNatTrans α.Hom
  unitIso := functorOfNatTransId.symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransComp _ _
  counitIso :=
    (functorOfNatTransComp _ _).symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransId
#align category_theory.endofunctor.algebra.equiv_of_nat_iso CategoryTheory.Endofunctor.Algebra.equivOfNatIso

namespace Initial

variable {A} (h : Limits.IsInitial A)

/-- The inverse of the structure map of an initial algebra -/
@[simp]
def strInv : A.1 ⟶ F.obj A.1 :=
  (h.to ⟨F.obj A.1, F.map A.str⟩).1
#align category_theory.endofunctor.algebra.initial.str_inv CategoryTheory.Endofunctor.Algebra.Initial.strInv

theorem left_inv' : (⟨strInv h ≫ A.str⟩ : A ⟶ A) = 𝟙 A :=
  Limits.IsInitial.hom_ext h _ (𝟙 A)
#align category_theory.endofunctor.algebra.initial.left_inv' CategoryTheory.Endofunctor.Algebra.Initial.left_inv'

theorem left_inv : strInv h ≫ A.str = 𝟙 _ :=
  congr_arg Hom.f (left_inv' h)
#align category_theory.endofunctor.algebra.initial.left_inv CategoryTheory.Endofunctor.Algebra.Initial.left_inv

theorem right_inv : A.str ≫ strInv h = 𝟙 _ :=
  by
  rw [str_inv, ← (h.to ⟨F.obj A.1, F.map A.str⟩).h, ← F.map_id, ← F.map_comp]
  congr
  exact left_inv h
#align category_theory.endofunctor.algebra.initial.right_inv CategoryTheory.Endofunctor.Algebra.Initial.right_inv

/-- The structure map of the inital algebra is an isomorphism,
hence endofunctors preserve their initial algebras
-/
theorem str_isIso (h : Limits.IsInitial A) : IsIso A.str :=
  { out := ⟨strInv h, right_inv _, left_inv _⟩ }
#align category_theory.endofunctor.algebra.initial.str_is_iso CategoryTheory.Endofunctor.Algebra.Initial.str_isIso

end Initial

end Algebra

/-- A coalgebra of an endofunctor; `str` stands for "structure morphism" -/
structure Coalgebra (F : C ⥤ C) where
  V : C
  str : V ⟶ F.obj V
#align category_theory.endofunctor.coalgebra CategoryTheory.Endofunctor.Coalgebra

instance [Inhabited C] : Inhabited (Coalgebra (𝟭 C)) :=
  ⟨⟨default, 𝟙 _⟩⟩

namespace Coalgebra

variable {F : C ⥤ C} (V : Coalgebra F) {V₀ V₁ V₂ : Coalgebra F}

/-
```
        str
    V₀ -----> F V₀
    |          |
  f |          | F f
    V          V
    V₁ -----> F V₁
        str
```
-/
/-- A morphism between coalgebras of an endofunctor `F` -/
@[ext]
structure Hom (V₀ V₁ : Coalgebra F) where
  f : V₀.1 ⟶ V₁.1
  h' : V₀.str ≫ F.map f = f ≫ V₁.str := by obviously
#align category_theory.endofunctor.coalgebra.hom CategoryTheory.Endofunctor.Coalgebra.Hom

restate_axiom hom.h'

attribute [simp, reassoc.1] hom.h

namespace Hom

/-- The identity morphism of an algebra of endofunctor `F` -/
def id : Hom V V where f := 𝟙 _
#align category_theory.endofunctor.coalgebra.hom.id CategoryTheory.Endofunctor.Coalgebra.Hom.id

instance : Inhabited (Hom V V) :=
  ⟨{ f := 𝟙 _ }⟩

/-- The composition of morphisms between algebras of endofunctor `F` -/
def comp (f : Hom V₀ V₁) (g : Hom V₁ V₂) : Hom V₀ V₂ where f := f.1 ≫ g.1
#align category_theory.endofunctor.coalgebra.hom.comp CategoryTheory.Endofunctor.Coalgebra.Hom.comp

end Hom

instance (F : C ⥤ C) : CategoryStruct (Coalgebra F)
    where
  Hom := Hom
  id := Hom.id
  comp := @Hom.comp _ _ _

@[simp]
theorem id_eq_id : Coalgebra.Hom.id V = 𝟙 V :=
  rfl
#align category_theory.endofunctor.coalgebra.id_eq_id CategoryTheory.Endofunctor.Coalgebra.id_eq_id

@[simp]
theorem id_f : (𝟙 _ : V ⟶ V).1 = 𝟙 V.1 :=
  rfl
#align category_theory.endofunctor.coalgebra.id_f CategoryTheory.Endofunctor.Coalgebra.id_f

variable {V₀ V₁ V₂} (f : V₀ ⟶ V₁) (g : V₁ ⟶ V₂)

@[simp]
theorem comp_eq_comp : Coalgebra.Hom.comp f g = f ≫ g :=
  rfl
#align category_theory.endofunctor.coalgebra.comp_eq_comp CategoryTheory.Endofunctor.Coalgebra.comp_eq_comp

@[simp]
theorem comp_f : (f ≫ g).1 = f.1 ≫ g.1 :=
  rfl
#align category_theory.endofunctor.coalgebra.comp_f CategoryTheory.Endofunctor.Coalgebra.comp_f

/-- Coalgebras of an endofunctor `F` form a category -/
instance (F : C ⥤ C) : Category (Coalgebra F) where

/-- To construct an isomorphism of coalgebras, it suffices to give an isomorphism of the Vs which
commutes with the structure morphisms.
-/
@[simps]
def isoMk (h : V₀.1 ≅ V₁.1) (w : V₀.str ≫ F.map h.Hom = h.Hom ≫ V₁.str) : V₀ ≅ V₁
    where
  Hom := { f := h.Hom }
  inv :=
    { f := h.inv
      h' := by
        rw [h.eq_inv_comp, ← category.assoc, ← w, category.assoc, ← functor.map_comp]
        simp only [iso.hom_inv_id, Functor.map_id, category.comp_id] }
#align category_theory.endofunctor.coalgebra.iso_mk CategoryTheory.Endofunctor.Coalgebra.isoMk

/-- The forgetful functor from the category of coalgebras, forgetting the coalgebraic structure. -/
@[simps]
def forget (F : C ⥤ C) : Coalgebra F ⥤ C
    where
  obj A := A.1
  map A B f := f.1
#align category_theory.endofunctor.coalgebra.forget CategoryTheory.Endofunctor.Coalgebra.forget

/-- A coalgebra morphism with an underlying isomorphism hom in `C` is a coalgebra isomorphism. -/
theorem iso_of_iso (f : V₀ ⟶ V₁) [IsIso f.1] : IsIso f :=
  ⟨⟨{   f := inv f.1
        h' := by
          rw [is_iso.eq_inv_comp f.1, ← category.assoc, ← f.h, category.assoc]
          simp },
      by tidy⟩⟩
#align category_theory.endofunctor.coalgebra.iso_of_iso CategoryTheory.Endofunctor.Coalgebra.iso_of_iso

instance forget_reflects_iso : ReflectsIsomorphisms (forget F) where reflects A B := iso_of_iso
#align category_theory.endofunctor.coalgebra.forget_reflects_iso CategoryTheory.Endofunctor.Coalgebra.forget_reflects_iso

instance forget_faithful : Faithful (forget F) where
#align category_theory.endofunctor.coalgebra.forget_faithful CategoryTheory.Endofunctor.Coalgebra.forget_faithful

/-- An algebra morphism with an underlying epimorphism hom in `C` is an algebra epimorphism. -/
theorem epi_of_epi {X Y : Coalgebra F} (f : X ⟶ Y) [h : Epi f.1] : Epi f :=
  (forget F).epi_of_epi_map h
#align category_theory.endofunctor.coalgebra.epi_of_epi CategoryTheory.Endofunctor.Coalgebra.epi_of_epi

/-- An algebra morphism with an underlying monomorphism hom in `C` is an algebra monomorphism. -/
theorem mono_of_mono {X Y : Coalgebra F} (f : X ⟶ Y) [h : Mono f.1] : Mono f :=
  (forget F).mono_of_mono_map h
#align category_theory.endofunctor.coalgebra.mono_of_mono CategoryTheory.Endofunctor.Coalgebra.mono_of_mono

/-- From a natural transformation `α : F → G` we get a functor from
coalgebras of `F` to coalgebras of `G`.
-/
@[simps]
def functorOfNatTrans {F G : C ⥤ C} (α : F ⟶ G) : Coalgebra F ⥤ Coalgebra G
    where
  obj V :=
    { V := V.1
      str := V.str ≫ α.app V.1 }
  map V₀ V₁ f :=
    { f := f.1
      h' := by rw [category.assoc, ← α.naturality, ← category.assoc, f.h, category.assoc] }
#align category_theory.endofunctor.coalgebra.functor_of_nat_trans CategoryTheory.Endofunctor.Coalgebra.functorOfNatTrans

/-- The identity transformation induces the identity endofunctor on the category of coalgebras. -/
@[simps (config := { rhsMd := semireducible })]
def functorOfNatTransId : functorOfNatTrans (𝟙 F) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun X =>
      isoMk (Iso.refl _)
        (by
          dsimp
          simp))
    fun X Y f => by
    ext
    dsimp
    simp
#align category_theory.endofunctor.coalgebra.functor_of_nat_trans_id CategoryTheory.Endofunctor.Coalgebra.functorOfNatTransId

/-- A composition of natural transformations gives the composition of corresponding functors. -/
@[simps (config := { rhsMd := semireducible })]
def functorOfNatTransComp {F₀ F₁ F₂ : C ⥤ C} (α : F₀ ⟶ F₁) (β : F₁ ⟶ F₂) :
    functorOfNatTrans (α ≫ β) ≅ functorOfNatTrans α ⋙ functorOfNatTrans β :=
  NatIso.ofComponents
    (fun X =>
      isoMk (Iso.refl _)
        (by
          dsimp
          simp))
    fun X Y f => by
    ext
    dsimp
    simp
#align category_theory.endofunctor.coalgebra.functor_of_nat_trans_comp CategoryTheory.Endofunctor.Coalgebra.functorOfNatTransComp

/-- If `α` and `β` are two equal natural transformations, then the functors of coalgebras induced by
them are isomorphic.
We define it like this as opposed to using `eq_to_iso` so that the components are nicer to prove
lemmas about.
-/
@[simps (config := { rhsMd := semireducible })]
def functorOfNatTransEq {F G : C ⥤ C} {α β : F ⟶ G} (h : α = β) :
    functorOfNatTrans α ≅ functorOfNatTrans β :=
  NatIso.ofComponents
    (fun X =>
      isoMk (Iso.refl _)
        (by
          dsimp
          simp [h]))
    fun X Y f => by
    ext
    dsimp
    simp
#align category_theory.endofunctor.coalgebra.functor_of_nat_trans_eq CategoryTheory.Endofunctor.Coalgebra.functorOfNatTransEq

/-- Naturally isomorphic endofunctors give equivalent categories of coalgebras.
Furthermore, they are equivalent as categories over `C`, that is,
we have `equiv_of_nat_iso h ⋙ forget = forget`.
-/
@[simps]
def equivOfNatIso {F G : C ⥤ C} (α : F ≅ G) : Coalgebra F ≌ Coalgebra G
    where
  Functor := functorOfNatTrans α.Hom
  inverse := functorOfNatTrans α.inv
  unitIso := functorOfNatTransId.symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransComp _ _
  counitIso :=
    (functorOfNatTransComp _ _).symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransId
#align category_theory.endofunctor.coalgebra.equiv_of_nat_iso CategoryTheory.Endofunctor.Coalgebra.equivOfNatIso

end Coalgebra

namespace Adjunction

variable {F : C ⥤ C} {G : C ⥤ C}

theorem Algebra.homEquiv_naturality_str (adj : F ⊣ G) (A₁ A₂ : Algebra F) (f : A₁ ⟶ A₂) :
    (adj.homEquiv A₁.a A₁.a) A₁.str ≫ G.map f.f = f.f ≫ (adj.homEquiv A₂.a A₂.a) A₂.str := by
  rw [← adjunction.hom_equiv_naturality_right, ← adjunction.hom_equiv_naturality_left, f.h]
#align category_theory.endofunctor.adjunction.algebra.hom_equiv_naturality_str CategoryTheory.Endofunctor.Adjunction.Algebra.homEquiv_naturality_str

theorem Coalgebra.homEquiv_naturality_str_symm (adj : F ⊣ G) (V₁ V₂ : Coalgebra G) (f : V₁ ⟶ V₂) :
    F.map f.f ≫ (adj.homEquiv V₂.V V₂.V).symm V₂.str = (adj.homEquiv V₁.V V₁.V).symm V₁.str ≫ f.f :=
  by
  rw [← adjunction.hom_equiv_naturality_left_symm, ← adjunction.hom_equiv_naturality_right_symm,
    f.h]
#align category_theory.endofunctor.adjunction.coalgebra.hom_equiv_naturality_str_symm CategoryTheory.Endofunctor.Adjunction.Coalgebra.homEquiv_naturality_str_symm

/-- Given an adjunction `F ⊣ G`, the functor that associates to an algebra over `F` a
coalgebra over `G` defined via adjunction applied to the structure map. -/
def Algebra.toCoalgebraOf (adj : F ⊣ G) : Algebra F ⥤ Coalgebra G
    where
  obj A :=
    { V := A.1
      str := (adj.homEquiv A.1 A.1).toFun A.2 }
  map A₁ A₂ f :=
    { f := f.1
      h' := Algebra.homEquiv_naturality_str adj A₁ A₂ f }
#align category_theory.endofunctor.adjunction.algebra.to_coalgebra_of CategoryTheory.Endofunctor.Adjunction.Algebra.toCoalgebraOf

/-- Given an adjunction `F ⊣ G`, the functor that associates to a coalgebra over `G` an algebra over
`F` defined via adjunction applied to the structure map. -/
def Coalgebra.toAlgebraOf (adj : F ⊣ G) : Coalgebra G ⥤ Algebra F
    where
  obj V :=
    { a := V.1
      str := (adj.homEquiv V.1 V.1).invFun V.2 }
  map V₁ V₂ f :=
    { f := f.1
      h' := Coalgebra.homEquiv_naturality_str_symm adj V₁ V₂ f }
#align category_theory.endofunctor.adjunction.coalgebra.to_algebra_of CategoryTheory.Endofunctor.Adjunction.Coalgebra.toAlgebraOf

/-- Given an adjunction, assigning to an algebra over the left adjoint a coalgebra over its right
adjoint and going back is isomorphic to the identity functor. -/
def AlgCoalgEquiv.unitIso (adj : F ⊣ G) :
    𝟭 (Algebra F) ≅ Algebra.toCoalgebraOf adj ⋙ Coalgebra.toAlgebraOf adj
    where
  Hom :=
    { app := fun A =>
        { f := 𝟙 A.1
          h' := by
            erw [F.map_id, category.id_comp, category.comp_id]
            apply (adj.hom_equiv _ _).left_inv A.str }
      naturality' := fun A₁ A₂ f => by
        ext1
        dsimp
        erw [category.id_comp, category.comp_id]
        rfl }
  inv :=
    { app := fun A =>
        { f := 𝟙 A.1
          h' := by
            erw [F.map_id, category.id_comp, category.comp_id]
            apply ((adj.hom_equiv _ _).left_inv A.str).symm }
      naturality' := fun A₁ A₂ f => by
        ext1
        dsimp
        erw [category.comp_id, category.id_comp]
        rfl }
  hom_inv_id' := by
    ext
    exact category.comp_id _
  inv_hom_id' := by
    ext
    exact category.comp_id _
#align category_theory.endofunctor.adjunction.alg_coalg_equiv.unit_iso CategoryTheory.Endofunctor.Adjunction.AlgCoalgEquiv.unitIso

/-- Given an adjunction, assigning to a coalgebra over the right adjoint an algebra over the left
adjoint and going back is isomorphic to the identity functor. -/
def AlgCoalgEquiv.counitIso (adj : F ⊣ G) :
    Coalgebra.toAlgebraOf adj ⋙ Algebra.toCoalgebraOf adj ≅ 𝟭 (Coalgebra G)
    where
  Hom :=
    { app := fun V =>
        { f := 𝟙 V.1
          h' := by
            dsimp
            erw [G.map_id, category.id_comp, category.comp_id]
            apply (adj.hom_equiv _ _).right_inv V.str }
      naturality' := fun V₁ V₂ f => by
        ext1
        dsimp
        erw [category.comp_id, category.id_comp]
        rfl }
  inv :=
    { app := fun V =>
        { f := 𝟙 V.1
          h' := by
            dsimp
            rw [G.map_id, category.comp_id, category.id_comp]
            apply ((adj.hom_equiv _ _).right_inv V.str).symm }
      naturality' := fun V₁ V₂ f => by
        ext1
        dsimp
        erw [category.comp_id, category.id_comp]
        rfl }
  hom_inv_id' := by
    ext
    exact category.comp_id _
  inv_hom_id' := by
    ext
    exact category.comp_id _
#align category_theory.endofunctor.adjunction.alg_coalg_equiv.counit_iso CategoryTheory.Endofunctor.Adjunction.AlgCoalgEquiv.counitIso

/-- If `F` is left adjoint to `G`, then the category of algebras over `F` is equivalent to the
category of coalgebras over `G`. -/
def algebraCoalgebraEquiv (adj : F ⊣ G) : Algebra F ≌ Coalgebra G
    where
  Functor := Algebra.toCoalgebraOf adj
  inverse := Coalgebra.toAlgebraOf adj
  unitIso := AlgCoalgEquiv.unitIso adj
  counitIso := AlgCoalgEquiv.counitIso adj
  functor_unitIso_comp' A := by
    ext
    exact category.comp_id _
#align category_theory.endofunctor.adjunction.algebra_coalgebra_equiv CategoryTheory.Endofunctor.Adjunction.algebraCoalgebraEquiv

end Adjunction

end Endofunctor

end CategoryTheory

