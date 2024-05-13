/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RepresentationTheory.Action.Concrete
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Algebra.Group.Basic

/-!

# Topological subcategories of `Action V G`

For a concrete category `V` and a monoid `G`, equipped with a topological space instance,
we define the subcategory `ContAction V G` of all objects of `Action V G` with a
`TopologicalSpace` instance on the underlying type such that the induced action
is continuouos.

We also define a category `DiscreteContAction V G` as the full subcategory of `ContAction V G`,
where the underlying topological space is discrete.

Finally we define inclusion functors into `Action V G` and `TopCat`.

-/

universe u v

open CategoryTheory Limits

namespace Action

variable (V : Type (u + 1)) [LargeCategory V] [ConcreteCategory V]
variable (G : MonCat.{u}) [TopologicalSpace G]

/-- The subcategory of `Action V G` where the underlying types are equipped with a
`TopologicalSpace` instance and the action of `G` is continuous. -/
structure ContAction extends Action V G where
  /-- The topological space structure on the underlying type. -/
  topologicalSpace : TopologicalSpace ((CategoryTheory.forget _).obj toAction)
  actionContinuous : ContinuousSMul G ((CategoryTheory.forget _).obj toAction)

namespace ContAction

instance : Coe (ContAction V G) (Action V G) where
  coe X := X.toAction

variable {V} {G}

attribute [instance] topologicalSpace actionContinuous

/-- A homomorphisms between two objects of `ContAction V G` is a continuous homomorphism
of the underlying objects in `Action V G`. -/
@[ext]
structure Hom (X Y : ContAction V G) where
  /-- The underlying homomorphism of objects of `Action V G`. -/
  hom : X.toAction ⟶ Y.toAction
  isContinuous : Continuous ((CategoryTheory.forget (Action V G)).map hom)

/-- The identity homomorphism in `ContAction V G`. -/
@[simps]
def Hom.id (X : ContAction V G) : Hom X X where
  hom := 𝟙 X.toAction
  isContinuous := by
    rw [CategoryTheory.Functor.map_id]
    exact continuous_id

/-- Composition of homomorphisms in `ContAction V G`. -/
@[simps]
def Hom.comp {X Y Z : ContAction V G} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  hom := f.hom ≫ g.hom
  isContinuous := by
    rw [Functor.map_comp, types_comp]
    exact Continuous.comp g.isContinuous f.isContinuous

variable (V G) in
instance category : Category (ContAction V G) where
  Hom X Y := Hom X Y
  id X := Hom.id X
  comp f g := Hom.comp f g

@[ext]
lemma hom_ext {X Y : ContAction V G} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  Hom.ext f g h

@[simp]
lemma id_hom (X : ContAction V G) : Hom.hom (𝟙 X) = 𝟙 X.toAction :=
  rfl

@[simp]
lemma comp_hom {X Y Z : ContAction V G} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

variable (V G)

/-- The forgetful functor from `ContAction V G` to types. Do not use this directly, but use the
`ConcreteCategory` API instead. -/
@[simps]
def forget : ContAction V G ⥤ Type u where
  obj X := (CategoryTheory.forget (Action V G)).obj X
  map {X Y} f := (CategoryTheory.forget (Action V G)).map f.hom

instance : Functor.Faithful (forget V G) where
  map_injective {_ _} _ _ h :=
    hom_ext <| (CategoryTheory.forget (Action V G)).map_injective h

instance concreteCategory : ConcreteCategory (ContAction V G) where
  forget := forget V G

variable {V G}

instance (X : ContAction V G) : TopologicalSpace ((CategoryTheory.forget _).obj X) :=
  X.topologicalSpace

variable (V G)

section Inclusions

/-- The canonical inclusion in `Action V G`. -/
@[simps]
def incl : ContAction V G ⥤ Action V G where
  obj X := X
  map {X Y} f := f.hom

instance : HasForget₂ (ContAction V G) (Action V G) where
  forget₂ := incl V G

/-- The canonical inclusion in `TopCat`. -/
@[simps]
def toTopCat : ContAction V G ⥤ TopCat where
  obj X := TopCat.of ((CategoryTheory.forget (ContAction V G)).obj X)
  map {X Y} f := ⟨(CategoryTheory.forget (ContAction V G)).map f, f.isContinuous⟩

instance : HasForget₂ (ContAction V G) TopCat where
  forget₂ := toTopCat V G

end Inclusions

section Discrete

/-- A predicate on an `X : ContAction V G` saying that the topology on the underlying type of `X`
is discrete. -/
def isDiscrete (X : ContAction V G) : Prop := DiscreteTopology ((CategoryTheory.forget _).obj X)

/-- The subcategory of `ContAction V G` where the topology is discrete. -/
def DiscreteContAction : Type _ := FullSubcategory (isDiscrete V G)

namespace DiscreteContAction

instance : Category (DiscreteContAction V G) :=
  FullSubcategory.category (isDiscrete V G)

instance : ConcreteCategory (DiscreteContAction V G) :=
  FullSubcategory.concreteCategory (isDiscrete V G)

variable {V G}

instance (X : DiscreteContAction V G) : TopologicalSpace ((CategoryTheory.forget _).obj X) :=
  X.obj.topologicalSpace

instance (X : DiscreteContAction V G) : DiscreteTopology ((CategoryTheory.forget _).obj X) :=
  X.property

end DiscreteContAction

end Discrete

end ContAction
