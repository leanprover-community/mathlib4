import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.ChosenFiniteProducts.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Types.Basic

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
        erw [← (φ.app X a).naturality f (𝟙 _),]
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

/-
@[simp]
lemma unitHomEquiv_symm_equivNatTrans_symm_app_app {F G : C ⥤ D} (φ : F ⟶ G)
    (X : C) (Y : C) (f : X ⟶ Y) :
    (((functorHom F G).unitHomEquiv.symm ((simplicialHomEquiv₀ K L).symm φ)).app X PUnit.unit).app Y f =
      φ.app Y := by
  rfl
-/

open MonoidalCategory

-- idk if this is true
noncomputable instance : EnrichedCategory (C ⥤ Type max v' v u) (C ⥤ D) where
  Hom := functorHom
  id _ := { app := fun X h ↦ ⟨fun Y φ ↦ (𝟙 _), by aesop⟩ }
  comp K L M := { app := fun X ⟨f, g⟩ => f.comp g }
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-
noncomputable instance : SimplicialCategory (SimplicialObject C) where
  homEquiv K L := by
    exact (simplicialHomEquiv₀ K L).symm.trans (simplicialHom K L).unitHomEquiv.symm

noncomputable instance : SimplicialCategory SSet.{v} := by
  dsimp [SSet]
  infer_instance
-/

end Functor
