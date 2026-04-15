module

public import Mathlib.CategoryTheory.Limits.Shapes.End
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Profunctor.Basic

@[expose] public section

universe w v u

namespace CategoryTheory

namespace Limits

open Opposite

class ChosenCoends.{v',u'} (C : Type*) [Category* C] where
  cowedge {J : Type u'} [Category.{v'} J] (F : Jᵒᵖ ⥤ J ⥤ C) : Cowedge F
  isCoend {J : Type u'} [Category.{v'} J] (F : Jᵒᵖ ⥤ J ⥤ C) : IsColimit (cowedge F)

variable {C : Type*} [Category* C] [ChosenCoends.{v, u} C]

section

variable {J : Type u} [Category.{v} J] (F : Jᵒᵖ ⥤ J ⥤ C)

def chosenCoend : C := (ChosenCoends.cowedge F).pt

def chosenCoend.ι (X : J) : (F.obj (op X)).obj X ⟶ chosenCoend F :=
  (ChosenCoends.cowedge F).π X

lemma chosenCoend.condition {X X' : J} (f : X ⟶ X') :
    (F.map f.op).app _ ≫ chosenCoend.ι F X = (F.obj _).map f ≫ chosenCoend.ι F X' :=
  (ChosenCoends.cowedge F).condition f

variable {F}

@[ext]
lemma chosenCoend.hom_ext {X : C} {f g : chosenCoend F ⟶ X}
    (h : ∀ j, chosenCoend.ι F j ≫ f = chosenCoend.ι F j ≫ g) : f = g := by
  apply (ChosenCoends.isCoend F).hom_ext
  rintro (a | a)
  · simpa using _ ≫= h _
  · exact h _

variable {X : C} (f : ∀ j, (F.obj (op j)).obj j ⟶ X)
  (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), (F.map g.op).app i ≫ f i = (F.obj (op j)).map g ≫ f j)

def chosenCoend.desc : chosenCoend F ⟶ X :=
  Cowedge.IsColimit.desc (ChosenCoends.isCoend F) f hf

@[reassoc (attr := simp)]
lemma chosenCoend.ι_desc (j : J) : chosenCoend.ι F j ≫ chosenCoend.desc f hf = f j := by
  apply IsColimit.fac

def chosenCoend.map {G : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) : chosenCoend F ⟶ chosenCoend G :=
  chosenCoend.desc (fun x ↦ (f.app (op x)).app x ≫ chosenCoend.ι _ _) (fun j j' φ ↦ by
    simp [chosenCoend.condition])

@[reassoc (attr := simp)]
lemma chosenCoend.ι_map {G : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) (j : J) :
    chosenCoend.ι F j ≫ chosenCoend.map f = (f.app _).app _ ≫ chosenCoend.ι G j := by
  simp [chosenCoend.map]

@[simp]
lemma chosenCoend.map_id : chosenCoend.map (𝟙 F) = 𝟙 _ := by cat_disch

@[reassoc (attr := simp)]
lemma chosenCoend.map_comp {G H : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) (g : G ⟶ H) :
    chosenCoend.map f ≫ chosenCoend.map g = chosenCoend.map (f ≫ g) := by
  cat_disch

end

end Limits

namespace Profunctor

universe w' v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] [Limits.ChosenCoends.{v₂, u₂} (Type (max w w'))]

open Opposite

@[simps! obj_obj obj_map map_app]
def compDiagram (P : Profunctor.{w} C D) (Q : Profunctor.{w'} D E) (X : C) (Y : E) :
    Dᵒᵖ ⥤ D ⥤ Type max w w' where
  obj U := {
    obj V := ((P.obj X).obj U) × ((Q.obj V).obj (Opposite.op Y))
    map f := TypeCat.ofHom (Prod.map id ((Q.map f).app _)) }
  map g := { app U := TypeCat.ofHom (Prod.map ((P.obj _).map g) id) }

@[simps]
def compDiagramMap (P : Profunctor.{w} C D) (Q : Profunctor.{w'} D E)
    {X X' : C} {Y Y' : E} (f : X ⟶ X') (g : Y ⟶ Y') :
    compDiagram P Q X Y' ⟶ compDiagram P Q X' Y where
  app d := { app d' := TypeCat.ofHom (Prod.map ((P.map f).app d) ((Q.obj d').map g.op)) }

open Limits

abbrev compObj (P : Profunctor.{w} C D) (Q : Profunctor.{w'} D E) (X : C) (Y : E) : Type max w w' :=
  chosenCoend <| compDiagram P Q X Y

noncomputable abbrev compMap (P : Profunctor.{w} C D) (Q : Profunctor.{w'} D E)
    {X X' : C} {Y Y' : E} (f : X ⟶ X') (g : Y ⟶ Y') :
    compObj P Q X Y' ⟶ compObj P Q X' Y :=
  chosenCoend.map <| compDiagramMap P Q f g

@[simp]
lemma compMap_id (P : Profunctor.{w} C D) (Q : Profunctor.{w'} D E) (X : C) (Y : E) :
    P.compMap Q (𝟙 X) (𝟙 Y) = 𝟙 _ := by
  convert chosenCoend.map_id
  cat_disch

@[simp]
lemma compMap_comp (P : Profunctor.{w} C D) (Q : Profunctor.{w'} D E)
    {X₁ X₂ X₃ : C} {Y₁ Y₂ Y₃ : E} (f : X₁ ⟶ X₂) (f' : X₂ ⟶ X₃) (g : Y₁ ⟶ Y₂) (g' : Y₂ ⟶ Y₃) :
    P.compMap Q (f ≫ f') (g ≫ g') = P.compMap Q f g' ≫ P.compMap Q f' g := by
  convert (chosenCoend.map_comp _ _).symm
  cat_disch

@[simps! obj_obj obj_map map_app]
noncomputable def comp (P : Profunctor.{w} C D) (Q : Profunctor.{w'} D E) :
    Profunctor.{max w w'} C E :=
  .ofCore { obj X Y := compObj P Q X Y, map f g := compMap P Q f g }

end Profunctor

open Limits in
@[implicit_reducible]
noncomputable def chosenCoendsType : ChosenCoends.{v, u} (Type max v u w) where
  cowedge F := Functor.coconeTypesEquiv _ (multispanIndexCoend F).multispan.coconeTypes
  isCoend F := Types.TypeMax.colimitCoconeIsColimit (multispanIndexCoend F).multispan

noncomputable instance : Limits.ChosenCoends.{v, u} (Type (max v u)) :=
  chosenCoendsType

end CategoryTheory
