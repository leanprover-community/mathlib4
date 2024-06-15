import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

universe w v' v u u'

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

variable (F G : C ⥤ D)

open MonoidalCategory

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

def HomObjEquiv (F G H : C ⥤ Type max u v v') : (F.HomObj H G) ≃ (F ⊗ G ⟶ H) where
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

@[simps!]
def homObjFunctor : (C ⥤ Type w)ᵒᵖ ⥤ Type max w v' u where
  obj A := HomObj F G A.unop
  map {A A'} f x := x.map f.unop

def functorHom : C ⥤ Type max v' v u := coyoneda.rightOp ⋙ homObjFunctor.{v} F G

variable {F G} in
@[ext]
lemma functorHom_ext {X : C} {x y : (functorHom F G).obj X}
    (h : ∀ (Y : C) (f : X ⟶ Y), x.app Y f = y.app Y f) : x = y :=
  HomObj.ext _ _ (by ext; apply h)

/-
def functorHomSectionsEquiv : (functorHom F G).sections ≃ (F ⟶ G) where
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

def functorHomSectionsEquiv' : (functorHom F G).sections ≃ (𝟙_ _ ⟶ functorHom F G) where
  toFun := fun ⟨u, hu⟩ ↦ ⟨fun X _ ↦ u X, by dsimp only [sections] at hu; aesop⟩
  invFun := by
    intro f
    refine ⟨fun X ↦ f.app X (PUnit.unit), by
      intro X Y φ
      have := congr_fun (f.naturality φ) PUnit.unit
      dsimp only [types_comp_apply] at this
      rw [← this]
      rfl
    ⟩
  left_inv _ := rfl
  right_inv _ := by rfl
-/

def natTransEquiv : (F ⟶ G) ≃ (𝟙_ _ ⟶ functorHom F G) where
  toFun f := ⟨fun X _ ↦ ⟨fun Y _ ↦ f.app Y, by aesop⟩, by aesop⟩
  invFun f := ⟨fun X ↦ (f.app X (PUnit.unit)).app X (𝟙 _), by
    intro X Y φ
    rw [← (f.app X (PUnit.unit)).naturality φ]
    congr 1
    have := HomObj.congr_app (congr_fun (f.naturality φ) PUnit.unit) Y (𝟙 Y)
    dsimp [functorHom] at this
    aesop ⟩
  left_inv _ := rfl
  right_inv f := by
    ext X a Y φ
    have := HomObj.congr_app (congr_fun (f.naturality φ) PUnit.unit) Y (𝟙 Y)
    dsimp [functorHom] at this
    aesop

def functorHomEquiv (A : C ⥤ Type max u v v') :
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
        { app := fun Y f => x.app Y (A.map f a) }
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
  right_inv x := by aesop

noncomputable def Id (K : C ⥤ D) : 𝟙_ (C ⥤ Type max v' v u) ⟶ K.functorHom K :=
  natTransEquiv _ _ (𝟙 _)

@[simp]
lemma aux (K : C ⥤ D) {A : C ⥤ Type max v v' u} (X Y : C) (φ : X ⟶ Y) {a : A.obj X} :
    (((K.functorHomEquiv K A).symm (HomObj.id K A)).app X a).app Y φ = 𝟙 _ := rfl

@[simp]
lemma aux' (K : C ⥤ D) (X Y : C) (φ : X ⟶ Y) :
    ((natTransEquiv K K (𝟙 _)).app X PUnit.unit).app Y φ = 𝟙 _ := rfl

@[simp]
lemma aux'' (K : C ⥤ D) (X Y : C) (φ : X ⟶ Y) :
    (K.Id.app X PUnit.unit).app Y φ = 𝟙 _ := rfl

@[simp]
lemma id_whiskerRight_functorHom_app (K L : C ⥤ D) (X : C)
    (x : 𝟙_ _ ⊗ (K.functorHom L).obj X) :
    ((K.Id ▷ K.functorHom L).app X x) = (K.Id.app X x.1, x.2) := rfl

@[simp]
lemma functorHom_whiskerLeft_id_app (K L : C ⥤ D) (X : C)
    (x : (K.functorHom L).obj X ⊗ 𝟙_ _) :
    ((K.functorHom L ◁ L.Id).app X x) = (x.1, L.Id.app X x.2) := rfl

@[simp]
lemma whiskerLeft_app_apply (K L M N : C ⥤ D)
    (g : L.functorHom M ⊗ M.functorHom N ⟶ L.functorHom N)
    {X : C} (a : (K.functorHom L ⊗ L.functorHom M ⊗ M.functorHom N).obj X) :
    (K.functorHom L ◁ g).app X a = ⟨a.1, g.app X a.2⟩ := rfl

@[simp]
lemma whiskerRight_app_apply (K L M N : C ⥤ D)
    (f : K.functorHom L ⊗ L.functorHom M ⟶ K.functorHom M)
    {X : C} (a : ((K.functorHom L ⊗ L.functorHom M) ⊗ M.functorHom N).obj X) :
    (f ▷  M.functorHom N).app X a = ⟨f.app X a.1, a.2⟩ := rfl

@[simp]
lemma associator_inv_apply (K L M N : C ⥤ D) {X : C}
    (x : ((K.functorHom L) ⊗ (L.functorHom M) ⊗ (M.functorHom N)).obj X) :
    (α_ ((K.functorHom L).obj X) ((L.functorHom M).obj X) ((M.functorHom N).obj X)).inv x =
    ⟨⟨x.1, x.2.1⟩, x.2.2⟩ := rfl

@[simp]
lemma associator_hom_apply (K L M N : C ⥤ D) {X : C}
    (x : ( ((K.functorHom L) ⊗ (L.functorHom M)) ⊗ (M.functorHom N)).obj X) :
    (α_ ((K.functorHom L).obj X) ((L.functorHom M).obj X) ((M.functorHom N).obj X)).hom x =
    ⟨x.1.1, x.1.2, x.2⟩ := rfl

noncomputable instance enrichedCategory : EnrichedCategory (C ⥤ Type max v' v u) (C ⥤ D) where
  Hom := functorHom
  id := Id
  comp K L M := { app := fun X ⟨f, g⟩ => f.comp g }


open Simplicial Functor

noncomputable instance : EnrichedCategory (SSet.{v}) (SimplicialObject C) := enrichedCategory

noncomputable instance : SimplicialCategory (SimplicialObject C) where
  homEquiv := natTransEquiv

noncomputable instance : SimplicialCategory SSet.{v} := by
  dsimp [SSet]
  infer_instance
