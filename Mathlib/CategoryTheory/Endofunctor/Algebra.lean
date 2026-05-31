/-
Copyright (c) 2022 Joseph Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta, Johan Commelin, Reid Barton, Robert Y. Lewis, Joseph Hua
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Functor.EpiMono

/-!

# Algebras of endofunctors

This file defines (co)algebras of an endofunctor, and provides the category instance for them.
It also defines the forgetful functor from the category of (co)algebras. It is shown that the
structure map of the initial algebra of an endofunctor is an isomorphism. Furthermore, it is shown
that for an adjunction `F ⊣ G` the category of algebras over `F` is equivalent to the category of
coalgebras over `G`.

## TODO

* Prove that if the countable infinite product over the powers of the endofunctor exists, then
  algebras over the endofunctor coincide with algebras over the free monad on the endofunctor.
-/

@[expose] public section


universe v u

namespace CategoryTheory

namespace Endofunctor

variable {C : Type u} [Category.{v} C]

/-- An algebra of an endofunctor; `str` stands for "structure morphism" -/
structure Algebra (F : C ⥤ C) where
  /-- carrier of the algebra -/
  a : C
  /-- structure morphism of the algebra -/
  str : F.obj a ⟶ a

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
  /-- underlying morphism between the carriers -/
  f : A₀.1 ⟶ A₁.1
  /-- compatibility condition -/
  h : F.map f ≫ A₁.str = A₀.str ≫ f := by cat_disch

attribute [reassoc (attr := simp)] Hom.h

namespace Hom

/-- The identity morphism of an algebra of endofunctor `F` -/
def id : Hom A A where f := 𝟙 _

instance : Inhabited (Hom A A) :=
  ⟨{ f := 𝟙 _ }⟩

/-- The composition of morphisms between algebras of endofunctor `F` -/
def comp (f : Hom A₀ A₁) (g : Hom A₁ A₂) : Hom A₀ A₂ where f := f.1 ≫ g.1

end Hom

instance (F : C ⥤ C) : CategoryStruct (Algebra F) where
  Hom := Hom
  id := Hom.id
  comp := @Hom.comp _ _ _

@[ext]
lemma ext {A B : Algebra F} {f g : A ⟶ B} (w : f.f = g.f := by cat_disch) : f = g :=
  Hom.ext w

@[simp]
theorem id_eq_id : Algebra.Hom.id A = 𝟙 A :=
  rfl

@[simp]
theorem id_f : (𝟙 _ : A ⟶ A).1 = 𝟙 A.1 :=
  rfl

variable (f : A₀ ⟶ A₁) (g : A₁ ⟶ A₂)

@[simp]
theorem comp_eq_comp : Algebra.Hom.comp f g = f ≫ g :=
  rfl

@[simp]
theorem comp_f : (f ≫ g).1 = f.1 ≫ g.1 :=
  rfl

/-- Algebras of an endofunctor `F` form a category -/
instance (F : C ⥤ C) : Category (Algebra F) := { }

/-- To construct an isomorphism of algebras, it suffices to give an isomorphism of the As which
commutes with the structure morphisms.
-/
@[simps!]
def isoMk (h : A₀.1 ≅ A₁.1) (w : F.map h.hom ≫ A₁.str = A₀.str ≫ h.hom := by cat_disch) :
    A₀ ≅ A₁ where
  hom := { f := h.hom }
  inv :=
    { f := h.inv
      h := by
        rw [h.eq_comp_inv, Category.assoc, ← w, ← Functor.map_comp_assoc]
        simp }

/-- The forgetful functor from the category of algebras, forgetting the algebraic structure. -/
@[simps]
def forget (F : C ⥤ C) : Algebra F ⥤ C where
  obj A := A.1
  map := Hom.f

/-- An algebra morphism with an underlying isomorphism hom in `C` is an algebra isomorphism. -/
theorem iso_of_iso (f : A₀ ⟶ A₁) [IsIso f.1] : IsIso f :=
  ⟨⟨{ f := inv f.1
      h := by simp }, by cat_disch, by cat_disch⟩⟩

instance forget_reflects_iso : (forget F).ReflectsIsomorphisms where reflects := iso_of_iso

instance forget_faithful : (forget F).Faithful := { }

/-- An algebra morphism with an underlying epimorphism hom in `C` is an algebra epimorphism. -/
theorem epi_of_epi {X Y : Algebra F} (f : X ⟶ Y) [h : Epi f.1] : Epi f :=
  (forget F).epi_of_epi_map h

/-- An algebra morphism with an underlying monomorphism hom in `C` is an algebra monomorphism. -/
theorem mono_of_mono {X Y : Algebra F} (f : X ⟶ Y) [h : Mono f.1] : Mono f :=
  (forget F).mono_of_mono_map h

/-- From a natural transformation `α : G → F` we get a functor from
algebras of `F` to algebras of `G`.
-/
@[simps]
def functorOfNatTrans {F G : C ⥤ C} (α : G ⟶ F) : Algebra F ⥤ Algebra G where
  obj A :=
    { a := A.1
      str := α.app _ ≫ A.str }
  map f := { f := f.1 }

set_option backward.defeqAttrib.useBackward true in
/-- The identity transformation induces the identity endofunctor on the category of algebras. -/
@[simps!]
def functorOfNatTransId : functorOfNatTrans (𝟙 F) ≅ 𝟭 _ :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
/-- A composition of natural transformations gives the composition of corresponding functors. -/
@[simps!]
def functorOfNatTransComp {F₀ F₁ F₂ : C ⥤ C} (α : F₀ ⟶ F₁) (β : F₁ ⟶ F₂) :
    functorOfNatTrans (α ≫ β) ≅ functorOfNatTrans β ⋙ functorOfNatTrans α :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)

/--
If `α` and `β` are two equal natural transformations, then the functors of algebras induced by them
are isomorphic.
We define it like this as opposed to using `eq_to_iso` so that the components are nicer to prove
lemmas about.
-/
@[simps!]
def functorOfNatTransEq {F G : C ⥤ C} {α β : F ⟶ G} (h : α = β) :
    functorOfNatTrans α ≅ functorOfNatTrans β :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
/-- Naturally isomorphic endofunctors give equivalent categories of algebras.
Furthermore, they are equivalent as categories over `C`, that is,
we have `equiv_of_nat_iso h ⋙ forget = forget`.
-/
@[simps]
def equivOfNatIso {F G : C ⥤ C} (α : F ≅ G) : Algebra F ≌ Algebra G where
  functor := functorOfNatTrans α.inv
  inverse := functorOfNatTrans α.hom
  unitIso := functorOfNatTransId.symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransComp _ _
  counitIso :=
    (functorOfNatTransComp _ _).symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransId

namespace Initial

variable {A : Algebra F} (h : Limits.IsInitial A)
/-- The inverse of the structure map of an initial algebra -/
@[simp]
def strInv : A.1 ⟶ F.obj A.1 :=
  (h.to ⟨F.obj A.a, F.map A.str⟩).f

theorem left_inv' :
    ⟨strInv h ≫ A.str, by rw [← Category.assoc, F.map_comp, strInv, ← Hom.h]⟩ = 𝟙 A :=
  Limits.IsInitial.hom_ext h _ (𝟙 A)

theorem left_inv : strInv h ≫ A.str = 𝟙 _ :=
  congr_arg Hom.f (left_inv' h)

theorem right_inv : A.str ≫ strInv h = 𝟙 _ := by
  rw [strInv, ← (h.to ⟨F.obj A.1, F.map A.str⟩).h, ← F.map_id, ← F.map_comp]
  congr
  exact left_inv h

/-- The structure map of the initial algebra is an isomorphism,
hence endofunctors preserve their initial algebras
-/
theorem str_isIso (h : Limits.IsInitial A) : IsIso A.str :=
  { out := ⟨strInv h, right_inv _, left_inv _⟩ }

end Initial

end Algebra

/-- A coalgebra of an endofunctor; `str` stands for "structure morphism" -/
structure Coalgebra (F : C ⥤ C) where
  /-- carrier of the coalgebra -/
  V : C
  /-- structure morphism of the coalgebra -/
  str : V ⟶ F.obj V

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
  /-- underlying morphism between two carriers -/
  f : V₀.1 ⟶ V₁.1
  /-- compatibility condition -/
  h : V₀.str ≫ F.map f = f ≫ V₁.str := by cat_disch

attribute [reassoc (attr := simp)] Hom.h

namespace Hom

/-- The identity morphism of an algebra of endofunctor `F` -/
def id : Hom V V where f := 𝟙 _

instance : Inhabited (Hom V V) :=
  ⟨{ f := 𝟙 _ }⟩

/-- The composition of morphisms between algebras of endofunctor `F` -/
def comp (f : Hom V₀ V₁) (g : Hom V₁ V₂) : Hom V₀ V₂ where f := f.1 ≫ g.1

end Hom

instance (F : C ⥤ C) : CategoryStruct (Coalgebra F) where
  Hom := Hom
  id := Hom.id
  comp := @Hom.comp _ _ _

@[ext]
lemma ext {A B : Coalgebra F} {f g : A ⟶ B} (w : f.f = g.f := by cat_disch) : f = g :=
  Hom.ext w

@[simp]
theorem id_eq_id : Coalgebra.Hom.id V = 𝟙 V :=
  rfl

@[simp]
theorem id_f : (𝟙 _ : V ⟶ V).1 = 𝟙 V.1 :=
  rfl

variable (f : V₀ ⟶ V₁) (g : V₁ ⟶ V₂)

@[simp]
theorem comp_eq_comp : Coalgebra.Hom.comp f g = f ≫ g :=
  rfl

@[simp]
theorem comp_f : (f ≫ g).1 = f.1 ≫ g.1 :=
  rfl

/-- Coalgebras of an endofunctor `F` form a category -/
instance (F : C ⥤ C) : Category (Coalgebra F) := { }

/-- To construct an isomorphism of coalgebras, it suffices to give an isomorphism of the Vs which
commutes with the structure morphisms.
-/
@[simps]
def isoMk (h : V₀.1 ≅ V₁.1) (w : V₀.str ≫ F.map h.hom = h.hom ≫ V₁.str := by cat_disch) :
    V₀ ≅ V₁ where
  hom := { f := h.hom }
  inv :=
    { f := h.inv
      h := by
        rw [h.eq_inv_comp, ← Category.assoc, ← w, Category.assoc, ← F.map_comp]
        simp only [Iso.hom_inv_id, Functor.map_id, Category.comp_id] }

/-- The forgetful functor from the category of coalgebras, forgetting the coalgebraic structure. -/
@[simps]
def forget (F : C ⥤ C) : Coalgebra F ⥤ C where
  obj A := A.1
  map f := f.1

/-- A coalgebra morphism with an underlying isomorphism hom in `C` is a coalgebra isomorphism. -/
theorem iso_of_iso (f : V₀ ⟶ V₁) [IsIso f.1] : IsIso f :=
  ⟨⟨{ f := inv f.1
      h := by
        rw [IsIso.eq_inv_comp f.1, ← Category.assoc, ← f.h, Category.assoc]
        simp }, by cat_disch, by cat_disch⟩⟩

instance forget_reflects_iso : (forget F).ReflectsIsomorphisms where reflects := iso_of_iso

instance forget_faithful : (forget F).Faithful := { }

/-- An algebra morphism with an underlying epimorphism hom in `C` is an algebra epimorphism. -/
theorem epi_of_epi {X Y : Coalgebra F} (f : X ⟶ Y) [h : Epi f.1] : Epi f :=
  (forget F).epi_of_epi_map h

/-- An algebra morphism with an underlying monomorphism hom in `C` is an algebra monomorphism. -/
theorem mono_of_mono {X Y : Coalgebra F} (f : X ⟶ Y) [h : Mono f.1] : Mono f :=
  (forget F).mono_of_mono_map h

/-- From a natural transformation `α : F → G` we get a functor from
coalgebras of `F` to coalgebras of `G`.
-/
@[simps]
def functorOfNatTrans {F G : C ⥤ C} (α : F ⟶ G) : Coalgebra F ⥤ Coalgebra G where
  obj V :=
    { V := V.1
      str := V.str ≫ α.app V.1 }
  map f :=
    { f := f.1
      h := by rw [Category.assoc, ← α.naturality, ← Category.assoc, f.h, Category.assoc] }

set_option backward.defeqAttrib.useBackward true in
/-- The identity transformation induces the identity endofunctor on the category of coalgebras. -/
@[simps!]
def functorOfNatTransId : functorOfNatTrans (𝟙 F) ≅ 𝟭 _ :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
/-- A composition of natural transformations gives the composition of corresponding functors. -/
@[simps!]
def functorOfNatTransComp {F₀ F₁ F₂ : C ⥤ C} (α : F₀ ⟶ F₁) (β : F₁ ⟶ F₂) :
    functorOfNatTrans (α ≫ β) ≅ functorOfNatTrans α ⋙ functorOfNatTrans β :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)

/-- If `α` and `β` are two equal natural transformations, then the functors of coalgebras induced by
them are isomorphic.
We define it like this as opposed to using `eq_to_iso` so that the components are nicer to prove
lemmas about.
-/
@[simps!]
def functorOfNatTransEq {F G : C ⥤ C} {α β : F ⟶ G} (h : α = β) :
    functorOfNatTrans α ≅ functorOfNatTrans β :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
/-- Naturally isomorphic endofunctors give equivalent categories of coalgebras.
Furthermore, they are equivalent as categories over `C`, that is,
we have `equiv_of_nat_iso h ⋙ forget = forget`.
-/
@[simps]
def equivOfNatIso {F G : C ⥤ C} (α : F ≅ G) : Coalgebra F ≌ Coalgebra G where
  functor := functorOfNatTrans α.hom
  inverse := functorOfNatTrans α.inv
  unitIso := functorOfNatTransId.symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransComp _ _
  counitIso :=
    (functorOfNatTransComp _ _).symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransId

namespace Terminal

variable {A : Coalgebra F} (h : Limits.IsTerminal A)

/-- The inverse of the structure map of a terminal coalgebra -/
@[simp]
def strInv : F.obj A.1 ⟶ A.1 :=
  (h.from ⟨F.obj A.V, F.map A.str⟩).f

theorem right_inv' :
    ⟨A.str ≫ strInv h, by rw [Category.assoc, F.map_comp, strInv, ← Hom.h] ⟩ = 𝟙 A :=
  Limits.IsTerminal.hom_ext h _ (𝟙 A)

theorem right_inv : A.str ≫ strInv h = 𝟙 _ :=
  congr_arg Hom.f (right_inv' h)

theorem left_inv : strInv h ≫ A.str = 𝟙 _ := by
  rw [strInv, ← (h.from ⟨F.obj A.V, F.map A.str⟩).h, ← F.map_id, ← F.map_comp]
  congr
  exact right_inv h

/-- The structure map of the terminal coalgebra is an isomorphism,
hence endofunctors preserve their terminal coalgebras
-/
theorem str_isIso (h : Limits.IsTerminal A) : IsIso A.str :=
  { out := ⟨strInv h, right_inv _, left_inv _⟩  }

end Terminal

end Coalgebra

namespace Adjunction

variable {F : C ⥤ C} {G : C ⥤ C}

theorem Algebra.homEquiv_naturality_str (adj : F ⊣ G) (A₁ A₂ : Algebra F) (f : A₁ ⟶ A₂) :
    (adj.homEquiv A₁.a A₁.a) A₁.str ≫ G.map f.f = f.f ≫ (adj.homEquiv A₂.a A₂.a) A₂.str := by
  rw [← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left, f.h]

theorem Coalgebra.homEquiv_naturality_str_symm (adj : F ⊣ G) (V₁ V₂ : Coalgebra G) (f : V₁ ⟶ V₂) :
    F.map f.f ≫ (adj.homEquiv V₂.V V₂.V).symm V₂.str =
    (adj.homEquiv V₁.V V₁.V).symm V₁.str ≫ f.f := by
  rw [← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm,
    f.h]

/-- Given an adjunction `F ⊣ G`, the functor that associates to an algebra over `F` a
coalgebra over `G` defined via adjunction applied to the structure map. -/
@[simps!]
def Algebra.toCoalgebraOf (adj : F ⊣ G) : Algebra F ⥤ Coalgebra G where
  obj A :=
    { V := A.1
      str := (adj.homEquiv A.1 A.1).toFun A.2 }
  map f :=
    { f := f.1
      h := Algebra.homEquiv_naturality_str adj _ _ f }

/-- Given an adjunction `F ⊣ G`, the functor that associates to a coalgebra over `G` an algebra over
`F` defined via adjunction applied to the structure map. -/
@[simps!]
def Coalgebra.toAlgebraOf (adj : F ⊣ G) : Coalgebra G ⥤ Algebra F where
  obj V :=
    { a := V.1
      str := (adj.homEquiv V.1 V.1).invFun V.2 }
  map f :=
    { f := f.1
      h := Coalgebra.homEquiv_naturality_str_symm adj _ _ f }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given an adjunction, assigning to an algebra over the left adjoint a coalgebra over its right
adjoint and going back is isomorphic to the identity functor. -/
@[simps!]
def AlgCoalgEquiv.unitIso (adj : F ⊣ G) :
    𝟭 (Algebra F) ≅ Algebra.toCoalgebraOf adj ⋙ Coalgebra.toAlgebraOf adj :=
  NatIso.ofComponents (fun _ ↦ Algebra.isoMk <| Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given an adjunction, assigning to a coalgebra over the right adjoint an algebra over the left
adjoint and going back is isomorphic to the identity functor. -/
@[simps!]
def AlgCoalgEquiv.counitIso (adj : F ⊣ G) :
    Coalgebra.toAlgebraOf adj ⋙ Algebra.toCoalgebraOf adj ≅ 𝟭 (Coalgebra G) :=
  NatIso.ofComponents (fun _ ↦ Coalgebra.isoMk <| Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
/-- If `F` is left adjoint to `G`, then the category of algebras over `F` is equivalent to the
category of coalgebras over `G`. -/
@[simps!]
def algebraCoalgebraEquiv (adj : F ⊣ G) : Algebra F ≌ Coalgebra G where
  functor := Algebra.toCoalgebraOf adj
  inverse := Coalgebra.toAlgebraOf adj
  unitIso := AlgCoalgEquiv.unitIso adj
  counitIso := AlgCoalgEquiv.counitIso adj
  functor_unitIso_comp A := by
    ext
    simp

end Adjunction

end Endofunctor

end CategoryTheory
