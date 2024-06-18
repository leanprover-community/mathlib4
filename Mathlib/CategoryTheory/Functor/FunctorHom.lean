import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Enriched.Basic

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

variable {A : C ⥤ Type w}

@[simps]
def comp {M : C ⥤ D} (f : HomObj F G A) (g : HomObj G M A) : HomObj F M A where
  app X a := f.app X a ≫ g.app X a

/-- -/
@[simps]
def map (x : HomObj F G A) {A' : C ⥤ Type w} (f : A' ⟶ A) : HomObj F G A' where
  app Δ a := x.app Δ (f.app Δ a)
  naturality {Δ Δ'} φ a := by
    dsimp
    rw [← x.naturality φ (f.app Δ a), FunctorToTypes.naturality _ _ f φ a]

@[simps]
def ofNatTrans (f : F ⟶ G) : HomObj F G A where
  app X _ := f.app X

end HomObj

/-- The contravariant functor taking `A : C ⥤ Type w` to `HomObj F G A`. -/
@[simps!]
def HomObjFunctor : (C ⥤ Type w)ᵒᵖ ⥤ Type max w v' u where
  obj A := HomObj F G A.unop
  map {A A'} f x := x.map f.unop

def functorHom : C ⥤ Type max v' v u := coyoneda.rightOp ⋙ HomObjFunctor.{v} F G

variable {F G} in
@[ext]
lemma functorHom_ext {X : C} {x y : (functorHom F G).obj X}
    (h : ∀ (Y : C) (f : X ⟶ Y), x.app Y f = y.app Y f) : x = y :=
  HomObj.ext _ _ (by ext; apply h)

def functorHomEquiv (A : C ⥤ Type max u v v') : (A ⟶ functorHom F G) ≃ HomObj F G A where
  toFun φ :=
    { app := fun X a ↦ (φ.app X a).app X (𝟙 _)
      naturality := fun {X Y} f a => by
        rw [← (φ.app X a).naturality f (𝟙 _)]
        have := HomObj.congr_app (congr_fun (φ.naturality f) a) Y (𝟙 _)
        dsimp [functorHom] at this
        aesop }
  invFun x :=
    { app := fun X a ↦ { app := fun Y f => x.app Y (A.map f a) }
      naturality := fun X Y f => by
        ext a Z φ
        dsimp only [types_comp_apply]
        rw [← FunctorToTypes.map_comp_apply]
        rfl }
  left_inv φ := by
    ext X a Y f
    exact (HomObj.congr_app (congr_fun (φ.naturality f) a) Y (𝟙 _)).trans
      (congr_arg ((φ.app X a).app Y) (by simp))
  right_inv x := by aesop

variable {F G} in
@[simps]
def natTransEquiv : (F ⟶ G) ≃ (𝟙_ _ ⟶ functorHom F G) where
  toFun f := ⟨fun _ _ ↦ HomObj.ofNatTrans f, _⟩
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

@[simp]
lemma natTransEquiv_app_app_apply (F G : C ⥤ D) (f : F ⟶ G)
    {X : C} {a : (𝟙_ (C ⥤ Type (max v' v u))).obj X} (Y : C) {φ : X ⟶ Y} :
    ((natTransEquiv f).app X a).app Y φ = f.app Y := rfl

@[simp]
lemma natTransEquiv_whiskerRight_functorHom_app (K L : C ⥤ D) (X : C) (f : K ⟶ K)
    (x : 𝟙_ _ ⊗ (K.functorHom L).obj X) :
    ((natTransEquiv f ▷ K.functorHom L).app X x) =
    (HomObj.ofNatTrans f, x.2) := rfl

@[simp]
lemma functorHom_whiskerLeft_natTransEquiv_app (K L : C ⥤ D) (X : C) (f : L ⟶ L)
    (x : (K.functorHom L).obj X ⊗ 𝟙_ _) :
    ((K.functorHom L ◁ natTransEquiv f).app X x) =
    (x.1, HomObj.ofNatTrans f) := rfl

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
  id F := natTransEquiv (𝟙 F)
  comp F G H := { app := fun X ⟨f, g⟩ => f.comp g }

end Functor
