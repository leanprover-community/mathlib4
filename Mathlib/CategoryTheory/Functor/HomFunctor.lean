import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.ChosenFiniteProducts.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Monoidal.OfChosenFiniteProducts.Basic

universe w v' v u u'

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

variable (F G : C ⥤ D)

-- `A ⊗ F ⟶ G`
@[ext]
structure HomObj (A : C ⥤ Type w) where
  app (X : C) (a : A.obj X) : F.obj X ⟶ G.obj X
  naturality {X Y : C} (φ : X ⟶ Y) (a : A.obj X) :
    F.map φ ≫ app Y (A.map φ a) = app X a ≫ G.map φ := by aesop_cat

namespace HomObj

attribute [reassoc (attr := simp)] naturality

variable {F G} in
lemma congr_app {A : C ⥤ Type w} {f g : HomObj F G A} (h : f = g) (X : C)
    (a : A.obj X) : f.app X a = g.app X a := by subst h; rfl

@[simps]
def id (A : C ⥤ Type w) : HomObj F F A where
  app _ _ := 𝟙 _

variable {F G}

@[simps]
def comp {M : C ⥤ D} {A : C ⥤ Type w} (f : HomObj F G A) (g : HomObj G M A) : HomObj F M A where
  app X a := f.app X a ≫ g.app X a

variable {A : C ⥤ Type w} (x : HomObj F G A)

@[simps]
def map {A' : C ⥤ Type w} (f : A' ⟶ A) : HomObj F G A' where
  app Δ a := x.app Δ (f.app Δ a)
  naturality {Δ Δ'} φ a := by
    dsimp
    rw [← x.naturality φ (f.app Δ a), FunctorToTypes.naturality _ _ f φ a]

end HomObj

-- the functor which sends `A : C ⥤ Type w` to the type `A ⊗ F ⟶ G`
@[simps!]
def homFunctor : (C ⥤ Type w)ᵒᵖ ⥤ Type max w v' u where
  obj A := HomObj F G A.unop
  map {A A'} f x := x.map f.unop

def functorHom (F G : C ⥤ D) : C ⥤ Type max v' v u := coyoneda.rightOp ⋙ homFunctor.{v} F G

variable {F G} in
@[ext]
lemma functorHom_ext {X : C} {x y : (functorHom F G).obj X}
    (h : ∀ (Y : C) (f : X ⟶ Y), x.app Y f = y.app Y f) : x = y :=
  HomObj.ext _ _ (by ext; apply h)

def NatTransEquiv : (functorHom F G).sections ≃ (F ⟶ G) where
  toFun := fun ⟨u, hu⟩ ↦
    { app := fun X ↦ (u X).app X (𝟙 _)
      naturality := fun X Y φ ↦ by
        dsimp
        rw [← HomObj.congr_app (hu φ) Y (𝟙 Y)]
        rw [← (u X).naturality φ (𝟙 _)]
        simp [functorHom]
    }
  invFun := fun f ↦ ⟨fun X ↦ { app := fun Y _ ↦ f.app Y }, by intro _ _ _; ext; aesop⟩
  left_inv := by
    simp [sections]
    rintro ⟨u, hu⟩
    ext X Y φ
    rw [← HomObj.congr_app (hu φ) Y (𝟙 Y)]
    dsimp [functorHom]
    aesop
  right_inv _ := by aesop

def HomEquiv (A : C ⥤ Type max u v v') :
    (A ⟶ functorHom F G) ≃ HomObj F G A where
  toFun φ :=
    { app := fun X a => (φ.app X a).app X (𝟙 _)
      naturality := fun {X Y} f a => by
        erw [← (φ.app X a).naturality f (𝟙 _)]
        have := HomObj.congr_app (congr_fun (φ.naturality f) a) Y (𝟙 _)
        dsimp [functorHom] at this
        aesop }
  invFun x :=
    { app := fun X a =>
        { app := fun Y f => x.app Y (A.map f a)
          naturality := fun {Y Z} φ f => by
            rw [← x.naturality φ (A.map f a), ← FunctorToTypes.map_comp_apply]
            rfl }
      naturality := fun X Y f => by
        dsimp
        ext a Z (φ : Y ⟶ Z)
        dsimp
        rw [← FunctorToTypes.map_comp_apply]
        rfl }
  left_inv φ := by
    ext X a Y f
    exact (HomObj.congr_app (congr_fun (φ.naturality f) a) Y (𝟙 _)).trans
      (congr_arg ((φ.app X a).app Y) (by simp))
  right_inv x := by
    ext X a
    dsimp
    erw [FunctorToTypes.map_id_apply _ _]

@[simp]
lemma _root_.Functor.comp_app_apply {A A' A'' : C ⥤ Type v} (f : A ⟶ A') (g : A' ⟶ A'')
    {X : C} (x : A.obj X) :
    (f ≫ g).app X x = g.app X (f.app X x) := rfl

@[simp]
lemma _root_.Functor.id_app_apply (A : C ⥤ Type v) {X : C} (x : A.obj X) :
    NatTrans.app (𝟙 A) X x = x := rfl

open MonoidalCategory

def prodhomequiv (F G H : C ⥤ Type max u v v') : (F.HomObj H G) ≃ (F ⊗ G ⟶ H) where
  toFun a := ⟨fun X ⟨x, y⟩ ↦ a.app X y x, fun X Y f ↦ by
    ext ⟨x, y⟩
    erw [congr_fun (a.naturality f y) x]
    rfl ⟩
  invFun a := ⟨fun X y x ↦ a.app X (x, y), fun φ y ↦ by
    ext x
    erw [congr_fun (a.naturality φ) (x, y)]
    rfl ⟩
  left_inv a := by aesop
  right_inv a := by aesop

def aux (P : C ⥤ D) : 𝟙_ (C ⥤ Type (max v' v u)) ⟶ P.functorHom P where
  app X _ := ((NatTransEquiv P P).symm (𝟙 _)).1 X

def aux' (K L M : C ⥤ D) : K.functorHom L ⊗ L.functorHom M ⟶ K.functorHom M where
  app := fun X ⟨f, g⟩ => f.comp g

@[simp]
lemma auxlemma (K L : C ⥤ D) (X Y : C) (a : (K.functorHom L).obj X) (φ : X ⟶ Y) :
    ((K.aux ▷ K.functorHom L).app X (PUnit.unit, a)).1.app Y φ = (𝟙 _) := rfl

@[simp]
lemma auxlemma' (K L : C ⥤ D) (X Y : C) (a : (K.functorHom L).obj X) (φ : X ⟶ Y) :
    ((K.aux ▷ K.functorHom L).app X (PUnit.unit, a)).2.app Y φ = a.app Y φ := rfl

@[simp]
lemma auxlemma'' (K L: C ⥤ D) (X Y : C) (a : (K.functorHom L).obj X) (φ : X ⟶ Y) :
    ((K.functorHom L ◁ L.aux).app X (a, PUnit.unit)).2.app Y φ = 𝟙 _ := rfl

@[simp]
lemma auxlemma''' (K L: C ⥤ D) (X Y : C) (a : (K.functorHom L).obj X) (φ : X ⟶ Y) :
    ((K.functorHom L ◁ L.aux).app X (a, PUnit.unit)).1.app Y φ = a.app Y φ := rfl

@[simp]
lemma whiskerLeft_app_apply (K L M N : C ⥤ D) (g : L.functorHom M ⊗ M.functorHom N ⟶ L.functorHom N)
    {X : C} (a : (K.functorHom L ⊗ L.functorHom M ⊗ M.functorHom N).obj X) :
    (K.functorHom L ◁ g).app X a = ⟨a.1, g.app X a.2⟩ := rfl

@[simp]
lemma whiskerRight_app_apply (K L M N : C ⥤ D) (f : K.functorHom L ⊗ L.functorHom M ⟶ K.functorHom M)
    {X : C} (a : ((K.functorHom L ⊗ L.functorHom M) ⊗ M.functorHom N).obj X) :
    (f ▷  M.functorHom N).app X a = ⟨f.app X a.1, a.2⟩ := rfl

@[simp]
lemma associator_inv_app_apply (K L M N : C ⥤ D) {X : C}
    (x : ((K.functorHom L) ⊗ (L.functorHom M) ⊗ (M.functorHom N)).obj X) :
    (α_ ((K.functorHom L).obj X) ((L.functorHom M).obj X) ((M.functorHom N).obj X)).inv x =
    ⟨⟨x.1, x.2.1⟩, x.2.2⟩ := rfl

@[simp]
lemma associator_hom_app_apply (K L M N : C ⥤ D) {X : C}
    (x : ( ((K.functorHom L) ⊗ (L.functorHom M)) ⊗ (M.functorHom N)).obj X) :
    (α_ ((K.functorHom L).obj X) ((L.functorHom M).obj X) ((M.functorHom N).obj X)).hom x =
    ⟨x.1.1, x.1.2, x.2⟩ := rfl

noncomputable instance : EnrichedCategory (C ⥤ Type max v' v u) (C ⥤ D) where
  Hom := functorHom
  id := aux
  comp := aux'
  id_comp K L := by
    ext X a Y φ
    change (HomObj.comp ((K.aux ▷ K.functorHom L).app X (PUnit.unit, a)).1 ((K.aux ▷ K.functorHom L).app X (PUnit.unit, a)).2).app Y φ = _
    aesop
  comp_id K L := by
    ext X a Y φ
    change (HomObj.comp ((K.functorHom L ◁ L.aux).app X (a, PUnit.unit)).1 ((K.functorHom L ◁ L.aux).app X (a, PUnit.unit)).2).app Y φ = _
    aesop
  assoc K L M N := by
    ext X a Y φ
    dsimp only [aux']
    aesop

end Functor
