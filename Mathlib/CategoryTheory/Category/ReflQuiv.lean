/-
Copyright (c) 2024 Mario Carneiro and Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl
-/
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Category.Quiv

/-!
# The category of refl quivers

The category `ReflQuiv` of (bundled) reflexive quivers, and the free/forgetful adjunction between
`Cat` and `ReflQuiv`.
-/

namespace CategoryTheory
universe v u v₁ v₂ u₁ u₂

/-- Category of refl quivers. -/
@[nolint checkUnivs]
def ReflQuiv :=
  Bundled ReflQuiver.{v + 1, u}

namespace ReflQuiv

instance : CoeSort ReflQuiv (Type u) where coe := Bundled.α

instance (C : ReflQuiv.{v, u}) : ReflQuiver.{v + 1, u} C := C.str

/-- The underlying quiver of a reflexive quiver.-/
def toQuiv (C : ReflQuiv.{v, u}) : Quiv.{v, u} := Quiv.of C.α

/-- Construct a bundled `ReflQuiv` from the underlying type and the typeclass. -/
def of (C : Type u) [ReflQuiver.{v + 1} C] : ReflQuiv.{v, u} := Bundled.of C

instance : Inhabited ReflQuiv := ⟨ReflQuiv.of (Discrete default)⟩

@[simp] theorem of_val (C : Type u) [ReflQuiver C] : (ReflQuiv.of C) = C := rfl

/-- Category structure on `ReflQuiv` -/
instance category : LargeCategory.{max v u} ReflQuiv.{v, u} where
  Hom C D := ReflPrefunctor C D
  id C := ReflPrefunctor.id C
  comp F G := ReflPrefunctor.comp F G

theorem id_eq_id (X : ReflQuiv) : 𝟙 X = 𝟭rq X := rfl
theorem comp_eq_comp {X Y Z : ReflQuiv} (F : X ⟶ Y) (G : Y ⟶ Z) : F ≫ G = F ⋙rq G := rfl

/-- The forgetful functor from categories to quivers. -/
@[simps]
def forget : Cat.{v, u} ⥤ ReflQuiv.{v, u} where
  obj C := ReflQuiv.of C
  map F := F.toReflPrefunctor

theorem forget_faithful {C D : Cat.{v, u}} (F G : C ⥤ D)
    (hyp : forget.map F = forget.map G) : F = G := by
  cases F; cases G; cases hyp; rfl

theorem forget.Faithful : Functor.Faithful (forget) where
  map_injective := fun hyp ↦ forget_faithful _ _ hyp

/-- The forgetful functor from categories to quivers. -/
@[simps]
def forgetToQuiv : ReflQuiv.{v, u} ⥤ Quiv.{v, u} where
  obj V := Quiv.of V
  map F := F.toPrefunctor

theorem forgetToQuiv_faithful {V W : ReflQuiv} (F G : V ⥤rq W)
    (hyp : forgetToQuiv.map F = forgetToQuiv.map G) : F = G := by
  cases F; cases G; cases hyp; rfl

instance forgetToQuiv.Faithful : Functor.Faithful forgetToQuiv where
  map_injective := fun hyp ↦ forgetToQuiv_faithful _ _ hyp

theorem forget_forgetToQuiv : forget ⋙ forgetToQuiv = Quiv.forget := rfl

/-- An isomorphism of quivers lifts to an isomorphism of reflexive quivers given a suitable
compatibility with the identities. -/
def isoOfQuivIso {V W : Type u} [ReflQuiver V] [ReflQuiver W]
    (e : Quiv.of V ≅ Quiv.of W)
    (h_id : ∀ (X : V), e.hom.map (𝟙rq X) = ReflQuiver.id (obj := W) (e.hom.obj X)) :
    ReflQuiv.of V ≅ ReflQuiv.of W where
  hom := ReflPrefunctor.mk e.hom h_id
  inv := ReflPrefunctor.mk e.inv
    (fun Y => (Quiv.homEquivOfIso e).injective (by simp [Quiv.hom_map_inv_map_of_iso, h_id]))
  hom_inv_id := by
    apply forgetToQuiv.map_injective
    exact e.hom_inv_id
  inv_hom_id := by
    apply forgetToQuiv.map_injective
    exact e.inv_hom_id

/-- Compatible equivalences of types and hom-types induce an isomorphism of reflexive quivers. -/
def isoOfEquiv {V W : Type u } [ReflQuiver V] [ReflQuiver W] (e : V ≃ W)
    (he : ∀ (X Y : V), (X ⟶ Y) ≃ (e X ⟶ e Y))
    (h_id : ∀ (X : V), he _ _ (𝟙rq X) = ReflQuiver.id (obj := W) (e X)) :
    ReflQuiv.of V ≅ ReflQuiv.of W := isoOfQuivIso (Quiv.isoOfEquiv e he) h_id

end ReflQuiv

namespace ReflPrefunctor

/-- A refl prefunctor can be promoted to a functor if it respects composition.-/
def toFunctor {C D : Cat} (F : (ReflQuiv.of C) ⟶ (ReflQuiv.of D))
    (hyp : ∀ {X Y Z : ↑C} (f : X ⟶ Y) (g : Y ⟶ Z),
      F.map (CategoryStruct.comp (obj := C) f g) =
        CategoryStruct.comp (obj := D) (F.map f) (F.map g)) : C ⥤ D where
  obj := F.obj
  map := F.map
  map_id := F.map_id
  map_comp := hyp

end ReflPrefunctor

namespace Cat

/-- The hom relation that identifies the specified reflexivity arrows with the nil paths.-/
inductive FreeReflRel {V} [ReflQuiver V] : (X Y : Paths V) → (f g : X ⟶ Y) → Prop
  | mk {X : V} : FreeReflRel X X (Quiver.Hom.toPath (𝟙rq X)) .nil

/-- A reflexive quiver generates a free category, defined as as quotient of the free category
on its underlying quiver (called the "path category") by the hom relation that uses the specified
reflexivity arrows as the identity arrows. -/
def FreeRefl (V) [ReflQuiver V] :=
  Quotient (C := Cat.free.obj (Quiv.of V)) (FreeReflRel (V := V))

instance (V) [ReflQuiver V] : Category (FreeRefl V) :=
  inferInstanceAs (Category (Quotient _))

/-- The quotient functor associated to a quotient category defines a natural map from the free
category on the underlying quiver of a refl quiver to the free category on the reflexive quiver.-/
def FreeRefl.quotientFunctor (V) [ReflQuiver V] : Cat.free.obj (Quiv.of V) ⥤ FreeRefl V :=
  Quotient.functor (C := Cat.free.obj (Quiv.of V)) (FreeReflRel (V := V))

/-- This is a specialization of `Quotient.lift_unique'` rather than `Quotient.lift_unique`, hence
the prime in the name.-/
theorem FreeRefl.lift_unique' {V} [ReflQuiver V] {D} [Category D] (F₁ F₂ : FreeRefl V ⥤ D)
    (h : quotientFunctor V ⋙ F₁ = quotientFunctor V ⋙ F₂) :
    F₁ = F₂ :=
  Quotient.lift_unique' (C := Cat.free.obj (Quiv.of V)) (FreeReflRel (V := V)) _ _ h

/-- The functor sending a reflexive quiver to the free category it generates, a quotient of
its path category.-/
@[simps!]
def freeRefl : ReflQuiv.{v, u} ⥤ Cat.{max u v, u} where
  obj V := Cat.of (FreeRefl V)
  map f := Quotient.lift _ ((by exact Cat.free.map f.toPrefunctor) ⋙ FreeRefl.quotientFunctor _)
    (fun X Y f g hfg => by
      apply Quotient.sound
      cases hfg
      simp [ReflPrefunctor.map_id]
      constructor)
  map_id X := by
    dsimp
    refine (Quotient.lift_unique _ _ _ _ ((Functor.comp_id _).trans <|
      (Functor.id_comp _).symm.trans ?_)).symm
    congr 1
    exact (free.map_id X.toQuiv).symm
  map_comp {X Y Z} f g := by
    dsimp
    apply (Quotient.lift_unique _ _ _ _ _).symm
    have : free.map (f ≫ g).toPrefunctor =
        free.map (X := X.toQuiv) (Y := Y.toQuiv) f.toPrefunctor ⋙
        free.map (X := Y.toQuiv) (Y := Z.toQuiv) g.toPrefunctor := by
      show _ = _ ≫ _
      rw [← Functor.map_comp]; rfl
    rw [this, Functor.assoc]
    show _ ⋙ _ ⋙ _ = _
    rw [← Functor.assoc, Quotient.lift_spec, Functor.assoc, FreeRefl.quotientFunctor,
      Quotient.lift_spec]

theorem freeRefl_naturality {X Y} [ReflQuiver X] [ReflQuiver Y] (f : X ⥤rq Y) :
    free.map (X := Quiv.of X) (Y := Quiv.of Y) f.toPrefunctor ⋙
    FreeRefl.quotientFunctor ↑Y =
    FreeRefl.quotientFunctor ↑X ⋙ freeRefl.map (X := ReflQuiv.of X) (Y := ReflQuiv.of Y) f := by
  simp only [free_obj, FreeRefl.quotientFunctor, freeRefl, ReflQuiv.of_val]
  rw [Quotient.lift_spec]

/-- We will make use of the natural quotient map from the free category on the underlying
quiver of a refl quiver to the free category on the reflexive quiver.-/
def freeReflNatTrans : ReflQuiv.forgetToQuiv ⋙ Cat.free ⟶ freeRefl where
  app V := FreeRefl.quotientFunctor V
  naturality _ _ f := freeRefl_naturality f

end Cat

namespace ReflQuiv
open Category Functor

/-- The unit components are defined as the composite of the corresponding unit component for the
adjunction between categories and quivers with the map underlying the quotient functor.-/
@[simps! toPrefunctor obj map]
def adj.unit.app (V : ReflQuiv.{max u v, u}) : V ⥤rq forget.obj (Cat.freeRefl.obj V) where
  toPrefunctor := Quiv.adj.unit.app (V.toQuiv) ⋙q
    Quiv.forget.map (Cat.FreeRefl.quotientFunctor V)
  map_id := fun _ => Quotient.sound _ ⟨⟩

/-- This is used in the proof of both triangle equalities.-/
theorem adj.unit.component_eq (V : ReflQuiv.{max u v, u}) :
    forgetToQuiv.map (adj.unit.app V) = Quiv.adj.unit.app (V.toQuiv) ≫
    Quiv.forget.map (Y := Cat.of _) (Cat.FreeRefl.quotientFunctor V) := rfl

/-- The counit components are defined using the universal property of the quotient
from the corresponding counit component for the adjunction between categories and quivers.-/
@[simps!]
def adj.counit.app (C : Cat) : Cat.freeRefl.obj (forget.obj C) ⥤ C :=
  Quotient.lift Cat.FreeReflRel (Quiv.adj.counit.app C) (by
    intro x y f g rel
    cases rel
    unfold Quiv.adj
    simp only [Adjunction.mkOfHomEquiv_counit_app, Equiv.coe_fn_symm_mk,
      Quiv.lift_map, Prefunctor.mapPath_toPath, composePath_toPath]
    rfl)

/-- The counit of `ReflQuiv.adj` is closely related to the counit of `Quiv.adj`.-/
@[simp]
theorem adj.counit.component_eq (C : Cat) :
    Cat.FreeRefl.quotientFunctor C ⋙ adj.counit.app C =
    Quiv.adj.counit.app C := rfl

/-- The counit of `ReflQuiv.adj` is closely related to the counit of `Quiv.adj`. For ease of use,
we introduce primed version for unbundled categories.-/
@[simp]
theorem adj.counit.component_eq' (C) [Category C] :
    Cat.FreeRefl.quotientFunctor C ⋙ adj.counit.app (Cat.of C) =
    Quiv.adj.counit.app (Cat.of C) := rfl

/--
The adjunction between forming the free category on a reflexive quiver, and forgetting a category
to a reflexive quiver.
-/
nonrec def adj : Cat.freeRefl.{max u v, u} ⊣ ReflQuiv.forget :=
  Adjunction.mkOfUnitCounit {
    unit := {
      app := adj.unit.app
      naturality := fun V W f ↦ by exact rfl
    }
    counit := {
      app := adj.counit.app
      naturality := fun C D F ↦ Quotient.lift_unique' _ _ _ (Quiv.adj.counit.naturality F)
    }
    left_triangle := by
      ext V
      apply Cat.FreeRefl.lift_unique'
      simp only [id_obj, Cat.free_obj, comp_obj, Cat.freeRefl_obj_α, NatTrans.comp_app,
        forget_obj, whiskerRight_app, associator_hom_app, whiskerLeft_app, id_comp,
        NatTrans.id_app']
      rw [Cat.id_eq_id, Cat.comp_eq_comp]
      simp only [Cat.freeRefl_obj_α, Functor.comp_id]
      rw [← Functor.assoc, ← Cat.freeRefl_naturality, Functor.assoc]
      dsimp [Cat.freeRefl]
      rw [adj.counit.component_eq' (Cat.FreeRefl V)]
      conv =>
        enter [1, 1, 2]
        apply (Quiv.comp_eq_comp (X := Quiv.of _) (Y := Quiv.of _) (Z := Quiv.of _) ..).symm
      rw [Cat.free.map_comp]
      show (_ ⋙ ((Quiv.forget ⋙ Cat.free).map (X := Cat.of _) (Y := Cat.of _)
        (Cat.FreeRefl.quotientFunctor V))) ⋙ _ = _
      rw [Functor.assoc, ← Cat.comp_eq_comp]
      conv => enter [1, 2]; apply Quiv.adj.counit.naturality
      rw [Cat.comp_eq_comp, ← Functor.assoc, ← Cat.comp_eq_comp]
      conv => enter [1, 1]; apply Quiv.adj.left_triangle_components V.toQuiv
      exact Functor.id_comp _
    right_triangle := by
      ext C
      exact forgetToQuiv_faithful _ _ (Quiv.adj.right_triangle_components C)
  }

end ReflQuiv

end CategoryTheory
