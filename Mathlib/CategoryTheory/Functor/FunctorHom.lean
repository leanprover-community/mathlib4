/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Enriched.Basic

/-!
# Internal hom in functor categories

Given functors `F G : C ⥤ D`, define a functor `functorHom F G` from `C` to `Type max v' v u`,
which is a proxy for the "internal hom" functor Hom(F ⊗ coyoneda(-), G). This is used to show
that the functor category `C ⥤ D` is enriched over `C ⥤ Type max v' v u`. This is also useful
for showing that `C ⥤ Type max w v u` is monoidal closed.

See `Mathlib/CategoryTheory/Closed/FunctorToTypes.lean`.

-/

@[expose] public section


universe w v' v u u'

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

variable (F G : C ⥤ D)

namespace CategoryTheory.Functor

/-- Given functors `F G : C ⥤ D`, `HomObj F G A` is a proxy for the type
of "morphisms" `F ⊗ A ⟶ G`, where `A : C ⥤ Type w` (`w` an arbitrary universe). -/
@[ext]
structure HomObj (A : C ⥤ Type w) where
  /-- The morphism `F.obj c ⟶ G.obj c` associated with `a : A.obj c`. -/
  app (c : C) (a : A.obj c) : F.obj c ⟶ G.obj c
  naturality {c d : C} (f : c ⟶ d) (a : A.obj c) :
    F.map f ≫ app d (A.map f a) = app c a ≫ G.map f := by cat_disch

/-- When `F`, `G`, and `A` are all functors `C ⥤ Type w`, then `HomObj F G A` is in
bijection with `F ⊗ A ⟶ G`. -/
@[simps]
def homObjEquiv (F G A : C ⥤ Type w) : (HomObj F G A) ≃ (F ⊗ A ⟶ G) where
  toFun a := ⟨fun X ↦ TypeCat.ofHom fun ⟨x, y⟩ ↦ a.app X y x, fun X Y f ↦ by
    ext ⟨x, y⟩
    simpa using ConcreteCategory.congr_hom (a.naturality f y) x⟩
  invFun a := ⟨fun X y ↦ TypeCat.ofHom (fun x ↦ a.app X (x, y)), fun φ y ↦ by
    ext x
    simpa using (a.naturality_apply φ) (x, y)⟩
  left_inv _ := by aesop
  right_inv _ := by aesop

namespace HomObj

attribute [reassoc (attr := simp)] naturality

variable {F G} {A : C ⥤ Type w}

lemma congr_app {f g : HomObj F G A} (h : f = g) (X : C)
    (a : A.obj X) : f.app X a = g.app X a := by subst h; rfl

/-- Given a natural transformation `F ⟶ G`, get a term of `HomObj F G A` by "ignoring" `A`. -/
@[simps]
def ofNatTrans (f : F ⟶ G) : HomObj F G A where
  app X _ := f.app X

/-- The identity `HomObj F F A`. -/
@[simps!]
def id (A : C ⥤ Type w) : HomObj F F A := ofNatTrans (𝟙 F)

/-- Composition of `f : HomObj F G A` with `g : HomObj G M A`. -/
@[simps]
def comp {M : C ⥤ D} (f : HomObj F G A) (g : HomObj G M A) : HomObj F M A where
  app X a := f.app X a ≫ g.app X a

/-- Given a morphism `A' ⟶ A`, send a term of `HomObj F G A` to a term of `HomObj F G A'`. -/
@[simps]
def map {A' : C ⥤ Type w} (f : A' ⟶ A) (x : HomObj F G A) : HomObj F G A' where
  app Δ a := x.app Δ (f.app Δ a)
  naturality {Δ Δ'} φ a := by
    rw [← x.naturality φ (f.app Δ a), f.naturality_apply φ a]

end HomObj

/-- The contravariant functor taking `A : C ⥤ Type w` to `HomObj F G A`, i.e. Hom(F ⊗ -, G). -/
@[simps obj map]
def homObjFunctor : (C ⥤ Type w)ᵒᵖ ⥤ Type (max w v' u) where
  obj A := HomObj F G A.unop
  map {A A'} f := TypeCat.ofHom fun x ↦
    { app := fun X a ↦ x.app X (f.unop.app _ a)
      naturality := fun {X Y} φ a ↦ by
        rw [← HomObj.naturality]
        congr 2
        exact ConcreteCategory.congr_hom (f.unop.naturality φ) a }

/-- Composition of `homObjFunctor` with the co-Yoneda embedding, i.e. Hom(F ⊗ coyoneda(-), G).
When `F G : C ⥤ Type max v' v u`, this is the internal hom of `F` and `G`: see
`Mathlib/CategoryTheory/Closed/FunctorToTypes.lean`. -/
abbrev functorHom (F G : C ⥤ D) : C ⥤ Type (max v' v u) :=
  coyoneda.rightOp ⋙ homObjFunctor.{v} F G

variable {F G} in
@[ext]
lemma functorHom_ext {X : C} {x y : (F.functorHom G).obj X}
    (h : ∀ (Y : C) (f : X ⟶ Y), x.app Y f = y.app Y f) : x = y :=
  HomObj.ext (by ext; apply h)

set_option backward.isDefEq.respectTransparency false in
/-- The equivalence `(A ⟶ F.functorHom G) ≃ HomObj F G A`. -/
@[simps]
def functorHomEquiv (A : C ⥤ Type (max u v v')) : (A ⟶ F.functorHom G) ≃ HomObj F G A where
  toFun φ :=
    { app := fun X a ↦ (φ.app X a).app X (𝟙 _)
      naturality := fun {X Y} f a => by
        rw [← (φ.app X a).naturality f (𝟙 _)]
        have := HomObj.congr_app (ConcreteCategory.congr_hom (φ.naturality f) a) Y (𝟙 _)
        simp_all [-NatTrans.naturality, functorHom, homObjFunctor] }
  invFun x :=
    { app X := TypeCat.ofHom (fun a ↦ { app := fun Y f => x.app Y (A.map f a) })
      naturality X Y f := by
        ext
        simp [functorHom, homObjFunctor] }
  left_inv φ := by
    ext X a Y f
    exact (HomObj.congr_app (ConcreteCategory.congr_hom (φ.naturality f) a) Y (𝟙 _)).trans
      (congr_arg ((φ.app X a).app Y) (by simp))
  right_inv x := by simp [functorHom, homObjFunctor]

set_option backward.isDefEq.respectTransparency false in
variable {F G} in
/-- Morphisms `(𝟙_ (C ⥤ Type max v' v u) ⟶ F.functorHom G)` are in bijection with
morphisms `F ⟶ G`. -/
@[simps]
def natTransEquiv : (𝟙_ (C ⥤ Type (max v' v u)) ⟶ F.functorHom G) ≃ (F ⟶ G) where
  toFun f := ⟨fun X ↦ (f.app X (PUnit.unit)).app X (𝟙 _), by
    intro X Y φ
    rw [← (f.app X (PUnit.unit)).naturality φ]
    congr 1
    have := HomObj.congr_app (ConcreteCategory.congr_hom (f.naturality φ) PUnit.unit) Y (𝟙 Y)
    dsimp [functorHom, homObjFunctor] at this
    aesop ⟩
  invFun f := { app _ := TypeCat.ofHom (fun _ ↦ HomObj.ofNatTrans f) }
  left_inv f := by
    ext X a Y φ
    have := HomObj.congr_app (ConcreteCategory.congr_hom (f.naturality φ) PUnit.unit) Y (𝟙 Y)
    dsimp [functorHom, homObjFunctor] at this
    aesop

end CategoryTheory.Functor

open Functor

namespace CategoryTheory.Enriched.Functor

@[simp]
lemma natTransEquiv_symm_app_app_apply (F G : C ⥤ D) (f : F ⟶ G)
    {X : C} {a : (𝟙_ (C ⥤ Type (max v' v u))).obj X} (Y : C) {φ : X ⟶ Y} :
    dsimp% ((natTransEquiv.symm f).app X a).app Y φ = f.app Y := rfl

@[simp]
lemma natTransEquiv_symm_whiskerRight_functorHom_app (K L : C ⥤ D) (X : C) (f : K ⟶ K)
    (x : 𝟙_ _ ⊗ (K.functorHom L).obj X) :
    dsimp% (natTransEquiv.symm f ▷ K.functorHom L).app X x =
    (HomObj.ofNatTrans f, x.2) := rfl

@[simp]
lemma functorHom_whiskerLeft_natTransEquiv_symm_app (K L : C ⥤ D) (X : C) (f : L ⟶ L)
    (x : (K.functorHom L).obj X ⊗ 𝟙_ _) :
    dsimp% (K.functorHom L ◁ natTransEquiv.symm f).app X x =
    (x.1, HomObj.ofNatTrans f) := rfl

@[simp]
lemma whiskerLeft_app_apply (K L M N : C ⥤ D)
    (g : L.functorHom M ⊗ M.functorHom N ⟶ L.functorHom N)
    {X : C} (a : (K.functorHom L ⊗ L.functorHom M ⊗ M.functorHom N).obj X) :
    dsimp% (K.functorHom L ◁ g).app X a = ⟨a.1, g.app X a.2⟩ := rfl

@[simp]
lemma whiskerRight_app_apply (K L M N : C ⥤ D)
    (f : K.functorHom L ⊗ L.functorHom M ⟶ K.functorHom M)
    {X : C} (a : ((K.functorHom L ⊗ L.functorHom M) ⊗ M.functorHom N).obj X) :
    dsimp% (f ▷ M.functorHom N).app X a = ⟨f.app X a.1, a.2⟩ := rfl

@[simp]
lemma associator_inv_apply (K L M N : C ⥤ D) {X : C}
    (x : ((K.functorHom L) ⊗ (L.functorHom M) ⊗ (M.functorHom N)).obj X) :
    dsimp% (α_ ((K.functorHom L).obj X) ((L.functorHom M).obj X) ((M.functorHom N).obj X)).inv x =
    ⟨⟨x.1, x.2.1⟩, x.2.2⟩ := rfl

@[simp]
lemma associator_hom_apply (K L M N : C ⥤ D) {X : C}
    (x : (((K.functorHom L) ⊗ (L.functorHom M)) ⊗ (M.functorHom N)).obj X) :
    dsimp% (α_ ((K.functorHom L).obj X) ((L.functorHom M).obj X) ((M.functorHom N).obj X)).hom x =
    ⟨x.1.1, x.1.2, x.2⟩ := rfl

attribute [local simp] functorHom types_tensorObj_def in
instance : EnrichedCategory (C ⥤ Type (max v' v u)) (C ⥤ D) where
  Hom := functorHom
  id F := natTransEquiv.symm (𝟙 F)
  comp F G H := { app _ := TypeCat.ofHom (fun f ↦ f.1.comp f.2) }

end CategoryTheory.Enriched.Functor
