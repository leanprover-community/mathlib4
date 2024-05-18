/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RepresentationTheory.Action.Concrete
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Category.TopCat.Basic

/-!

# Topological subcategories of `Action V G`

For a concrete category `V`, where the forgetful functor factors via `TopCat`,
and a monoid `G`, equipped with a topological space instance,
we define the full subcategory `ContAction V G` of all objects of `Action V G`
where the induced action is continuouos.

We also define a category `DiscreteContAction V G` as the full subcategory of `ContAction V G`,
where the underlying topological space is discrete.

Finally we define inclusion functors into `Action V G` and `TopCat` in terms
of `HasForget₂` instances.

-/

universe u v

open CategoryTheory Limits

namespace Action

variable (V : Type (u + 1)) [LargeCategory V] [ConcreteCategory V] [HasForget₂ V TopCat]
variable (G : MonCat.{u}) [TopologicalSpace G]

instance : HasForget₂ (Action V G) TopCat :=
  HasForget₂.trans (Action V G) V TopCat

instance (X : Action V G) : MulAction G ((CategoryTheory.forget₂ _ TopCat).obj X) where
  smul g x := ((CategoryTheory.forget₂ _ TopCat).map (X.ρ g)) x
  one_smul x := by
    show ((CategoryTheory.forget₂ _ TopCat).map (X.ρ 1)) x = x
    simp
  mul_smul g h x := by
    show (CategoryTheory.forget₂ _ TopCat).map (X.ρ (g * h)) x =
      ((CategoryTheory.forget₂ _ TopCat).map (X.ρ h)
        ≫ (CategoryTheory.forget₂ _ TopCat).map (X.ρ g)) x
    rw [← Functor.map_comp, map_mul]
    rfl

def IsContinuous (X : Action V G) : Prop :=
  ContinuousSMul G ((CategoryTheory.forget₂ _ TopCat).obj X)

def ContAction : Type _ := FullSubcategory (IsContinuous V G)

instance : Category (ContAction V G) :=
  FullSubcategory.category (IsContinuous V G)

instance : ConcreteCategory (ContAction V G) :=
  FullSubcategory.concreteCategory (IsContinuous V G)

instance : HasForget₂ (ContAction V G) (Action V G) :=
  FullSubcategory.hasForget₂ (IsContinuous V G)

instance : HasForget₂ (ContAction V G) V :=
  HasForget₂.trans (ContAction V G) (Action V G) V

instance : HasForget₂ (ContAction V G) TopCat :=
  HasForget₂.trans (ContAction V G) (Action V G) TopCat

namespace ContAction

instance : Coe (ContAction V G) (Action V G) where
  coe X := X.obj

section Discrete

/-- A predicate on an `X : ContAction V G` saying that the topology on the underlying type of `X`
is discrete. -/
def IsDiscrete (X : ContAction V G) : Prop :=
  DiscreteTopology ((CategoryTheory.forget₂ _ TopCat).obj X)

/-- The subcategory of `ContAction V G` where the topology is discrete. -/
def DiscreteContAction : Type _ := FullSubcategory (IsDiscrete V G)

namespace DiscreteContAction

instance : Category (DiscreteContAction V G) :=
  FullSubcategory.category (IsDiscrete V G)

instance : ConcreteCategory (DiscreteContAction V G) :=
  FullSubcategory.concreteCategory (IsDiscrete V G)

instance : HasForget₂ (DiscreteContAction V G) (ContAction V G) :=
  FullSubcategory.hasForget₂ (IsDiscrete V G)

instance : HasForget₂ (DiscreteContAction V G) TopCat :=
  HasForget₂.trans (DiscreteContAction V G) (ContAction V G) TopCat

variable {V G}

instance (X : DiscreteContAction V G) :
    DiscreteTopology ((CategoryTheory.forget₂ _ TopCat).obj X) :=
  X.property

end DiscreteContAction

end Discrete

end ContAction
