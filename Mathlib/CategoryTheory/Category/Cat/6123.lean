
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.CategoryTheory.Category.Basic

section Mathlib.CategoryTheory.Functor.Basic

namespace CategoryTheory

universe v v₁ v₂ v₃ u u₁ u₂ u₃

structure Functor (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]
    extends Prefunctor C D : Type max v₁ v₂ u₁ u₂ where

scoped [CategoryTheory] infixr:26 " ⥤ " => Functor

namespace Functor

section

variable (C : Type u₁) [Category.{v₁} C]

protected def id : C ⥤ C where
  obj X := X
  map f := f

scoped [CategoryTheory] notation "𝟭" => Functor.id

variable {C}

theorem id_obj (X : C) : (𝟭 C).obj X = X := rfl

theorem id_map {X Y : C} (f : X ⟶ Y) : (𝟭 C).map f = f := rfl

end

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

@[simps obj]
def comp (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E where
  obj X := G.obj (F.obj X)
  map f := G.map (F.map f)

scoped [CategoryTheory] infixr:80 " ⋙ " => Functor.comp

theorem comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y : C} (f : X ⟶ Y) :
    (F ⋙ G).map f = G.map (F.map f) := rfl

end Functor

end CategoryTheory

end Mathlib.CategoryTheory.Functor.Basic

section Mathlib.CategoryTheory.NatTrans

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

structure NatTrans (F G : C ⥤ D) : Type max u₁ v₂ where
  app : ∀ X : C, F.obj X ⟶ G.obj X
  naturality : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), F.map f ≫ app Y = app X ≫ G.map f

namespace NatTrans

/-- `NatTrans.id F` is the identity natural transformation on a functor `F`. -/
protected def id (F : C ⥤ D) : NatTrans F F where
  app X := 𝟙 (F.obj X)
  naturality := sorry

variable {F G H : C ⥤ D}

def vcomp (α : NatTrans F G) (β : NatTrans G H) : NatTrans F H where
  app X := α.app X ≫ β.app X
  naturality := sorry

end NatTrans

end CategoryTheory


end Mathlib.CategoryTheory.NatTrans

section Mathlib.CategoryTheory.Functor.Category

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

variable {C D}

instance Functor.category : Category.{max u₁ v₂} (C ⥤ D) where
  Hom F G := NatTrans F G
  id F := NatTrans.id F
  comp α β := NatTrans.vcomp α β
  comp_id := sorry
  id_comp := sorry
  assoc := sorry

end CategoryTheory

end Mathlib.CategoryTheory.Functor.Category

section Mathlib.CategoryTheory.EqToHom

universe v₁ u₁

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

def eqToHom {X Y : C} (p : X = Y) : X ⟶ Y := by rw [p]; exact 𝟙 _

end CategoryTheory

end Mathlib.CategoryTheory.EqToHom

section Mathlib.CategoryTheory.Functor.Const

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory

namespace CategoryTheory.Functor

variable (J : Type u₁) [Category.{v₁} J]
variable {C : Type u₂} [Category.{v₂} C]

@[simps]
def const : C ⥤ J ⥤ C where
  obj X :=
    { obj := fun _ => X
      map := fun _ => 𝟙 X }
  map f := { app := fun _ => f, naturality := sorry }

end CategoryTheory.Functor


end Mathlib.CategoryTheory.Functor.Const

section Mathlib.CategoryTheory.DiscreteCategory

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₁' u₂ u₃

structure Discrete (α : Type u₁) where
  as : α

instance discreteCategory (α : Type u₁) : SmallCategory (Discrete α) where
  Hom X Y := ULift (PLift (X.as = Y.as))
  id _ := ULift.up (PLift.up rfl)
  comp {X Y Z} g f := by
    cases X
    cases Y
    cases Z
    rcases f with ⟨⟨⟨⟩⟩⟩
    exact g
  comp_id := sorry
  id_comp := sorry
  assoc := sorry

namespace Discrete

variable {α : Type u₁}

theorem eq_of_hom {X Y : Discrete α} (i : X ⟶ Y) : X.as = Y.as :=
  i.down.down

protected abbrev eqToHom {X Y : Discrete α} (h : X.as = Y.as) : X ⟶ Y :=
  eqToHom sorry

variable {C : Type u₂} [Category.{v₂} C]

def functor {I : Type u₁} (F : I → C) : Discrete I ⥤ C where
  obj := F ∘ Discrete.as
  map {X Y} f := by
    dsimp
    rcases f with ⟨⟨h⟩⟩
    exact eqToHom (congrArg _ h)

end Discrete

end CategoryTheory


end Mathlib.CategoryTheory.DiscreteCategory

section Mathlib.CategoryTheory.Types

namespace CategoryTheory

universe v v' w u u'

instance types : LargeCategory (Type u) where
  Hom a b := a → b
  id _ := id
  comp f g := g ∘ f

end CategoryTheory

end Mathlib.CategoryTheory.Types

section Mathlib.CategoryTheory.Bicategory.Basic

namespace CategoryTheory

universe w v u

open Category

class Bicategory (B : Type u) extends CategoryStruct.{v} B where
  homCategory : ∀ a b : B, Category.{w} (a ⟶ b) := by infer_instance

end CategoryTheory

end Mathlib.CategoryTheory.Bicategory.Basic

section Mathlib.CategoryTheory.Bicategory.Strict

namespace CategoryTheory

universe w v u

variable (B : Type u) [Bicategory.{w, v} B]

instance (priority := 100) StrictBicategory.category : Category B where
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

end CategoryTheory

end Mathlib.CategoryTheory.Bicategory.Strict

section Mathlib.CategoryTheory.Category.Cat

universe v u

namespace CategoryTheory

open Bicategory

def Cat :=
  Bundled Category.{v, u}

namespace Cat

instance : CoeSort Cat (Type u) :=
  ⟨Bundled.α⟩

instance str (C : Cat.{v, u}) : Category.{v, u} C :=
  Bundled.str C

def of (C : Type u) [Category.{v} C] : Cat.{v, u} :=
  Bundled.of C

instance bicategory : Bicategory.{max v u, max v u} Cat.{v, u} where
  Hom C D := C ⥤ D
  id C := 𝟭 C
  comp F G := F ⋙ G
  homCategory := fun _ _ => Functor.category

@[simp] theorem of_α (C) [Category C] : (of C).α = C := rfl

def objects : Cat.{v, u} ⥤ Type u where
  obj C := C
  map F := F.obj

instance (X : Cat.{v, u}) : Category (objects.obj X) := (inferInstance : Category X)

end Cat

@[simps]
def typeToCat : Type u ⥤ Cat where
  obj X := Cat.of (Discrete X)
  map := fun {X} {Y} f => by
    dsimp
    exact Discrete.functor (Discrete.mk ∘ f)

end CategoryTheory


end Mathlib.CategoryTheory.Category.Cat

section Mathlib.CategoryTheory.Adjunction.Basic

namespace CategoryTheory

open Category

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

structure Adjunction (F : C ⥤ D) (G : D ⥤ C) where
  unit : 𝟭 C ⟶ F.comp G
  counit : G.comp F ⟶ 𝟭 D

infixl:15 " ⊣ " => Adjunction

namespace Adjunction

structure CoreHomEquivUnitCounit (F : C ⥤ D) (G : D ⥤ C) where
  homEquiv : ∀ X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)
  unit : 𝟭 C ⟶ F ⋙ G
  counit : G ⋙ F ⟶ 𝟭 D
  homEquiv_counit : ∀ {X Y g}, (homEquiv X Y).symm g = F.map g ≫ counit.app Y

variable {F : C ⥤ D} {G : D ⥤ C}

@[simps]
def mk' (adj : CoreHomEquivUnitCounit F G) : F ⊣ G where
  unit := adj.unit
  counit := adj.counit

end Adjunction

end CategoryTheory


end Mathlib.CategoryTheory.Adjunction.Basic

section Mathlib.CategoryTheory.IsConnected

universe w₁ w₂ v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory.Category

namespace CategoryTheory

class IsPreconnected (J : Type u₁) [Category.{v₁} J] : Prop where
  iso_constant :
    ∀ {α : Type u₁} (F : J ⥤ Discrete α) (j : J), False

class IsConnected (J : Type u₁) [Category.{v₁} J] extends IsPreconnected J : Prop where
  [is_nonempty : Nonempty J]

variable {J : Type u₁} [Category.{v₁} J]

def Zag (j₁ j₂ : J) : Prop :=
  Nonempty (j₁ ⟶ j₂) ∨ Nonempty (j₂ ⟶ j₁)

def Zigzag : J → J → Prop :=
  Relation.ReflTransGen Zag

def Zigzag.setoid (J : Type u₂) [Category.{v₁} J] : Setoid J where
  r := Zigzag
  iseqv := sorry

end CategoryTheory

end

end Mathlib.CategoryTheory.IsConnected

section Mathlib.CategoryTheory.ConnectedComponents

universe v₁ v₂ v₃ u₁ u₂

noncomputable section

namespace CategoryTheory

variable {J : Type u₁} [Category.{v₁} J]

def ConnectedComponents (J : Type u₁) [Category.{v₁} J] : Type u₁ :=
  Quotient (Zigzag.setoid J)

def Functor.mapConnectedComponents {K : Type u₂} [Category.{v₂} K] (F : J ⥤ K)
    (x : ConnectedComponents J) : ConnectedComponents K :=
  x |> Quotient.lift (Quotient.mk (Zigzag.setoid _) ∘ F.obj) sorry

def ConnectedComponents.functorToDiscrete   (X : Type*)
    (f : ConnectedComponents J → X) : J ⥤ Discrete X where
  obj Y :=  Discrete.mk (f (Quotient.mk (Zigzag.setoid _) Y))
  map g := Discrete.eqToHom sorry

def ConnectedComponents.liftFunctor (J) [Category J] {X : Type*} (F :J ⥤ Discrete X) :
    (ConnectedComponents J → X) :=
  Quotient.lift (fun c => (F.obj c).as) sorry

def ConnectedComponents.typeToCatHomEquiv (J) [Category J] (X : Type*) :
    (ConnectedComponents J → X) ≃ (J ⥤ Discrete X)   where
  toFun := ConnectedComponents.functorToDiscrete _
  invFun := ConnectedComponents.liftFunctor _
  left_inv := sorry
  right_inv  := sorry

end CategoryTheory

end

end Mathlib.CategoryTheory.ConnectedComponents

universe v u
namespace CategoryTheory.Cat

variable (X : Type u) (C : Cat)

private def typeToCatObjectsAdjHomEquiv : (typeToCat.obj X ⟶ C) ≃ (X ⟶ Cat.objects.obj C) where
  toFun f x := f.obj ⟨x⟩
  invFun := Discrete.functor
  left_inv F := sorry
  right_inv _ := sorry

private def typeToCatObjectsAdjCounitApp : (Cat.objects ⋙ typeToCat).obj C ⥤ C where
  obj := Discrete.as
  map := eqToHom ∘ Discrete.eq_of_hom

/-- `typeToCat : Type ⥤ Cat` is left adjoint to `Cat.objects : Cat ⥤ Type` -/
def typeToCatObjectsAdj : typeToCat ⊣ Cat.objects :=
  Adjunction.mk' {
    homEquiv := typeToCatObjectsAdjHomEquiv
    unit := sorry
    counit := {
      app := typeToCatObjectsAdjCounitApp
      naturality := sorry }
    homEquiv_counit := by
      intro X Y g
      simp_all only [typeToCat_obj, Functor.id_obj, typeToCat_map, of_α, id_eq]
      rfl }

def connectedComponents : Cat.{v, u} ⥤ Type u where
  obj C := ConnectedComponents C
  map F := Functor.mapConnectedComponents F

def connectedComponentsTypeToCatAdj : connectedComponents ⊣ typeToCat :=
  Adjunction.mk' {
    homEquiv := fun C X ↦ ConnectedComponents.typeToCatHomEquiv C X
    unit :=
      { app:= fun C  ↦ ConnectedComponents.functorToDiscrete _ (𝟙 (connectedComponents.obj C))
        naturality := by
          intro X Y f
          simp_all only [Functor.id_obj, Functor.comp_obj, typeToCat_obj, Functor.id_map,
            Functor.comp_map, typeToCat_map, of_α, id_eq]
          rfl }
    counit := sorry
    homEquiv_counit := sorry }

end CategoryTheory.Cat
