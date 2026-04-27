/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sets.Opens

/-!
# The standard conservative family of points for the site attached to a topological space

If `X` is a topological space, any `x : X` defines a point of the site
attached to `X`.

## TODO

* Redefine the stalks functors in `Mathlib/Topology/Sheaves/Stalks.lean`
  using `GrothendieckTopology.Point.presheafFiber`.

-/

@[expose] public section

universe u

namespace Opens

open CategoryTheory GrothendieckTopology TopologicalSpace

variable {X : Type u} [TopologicalSpace X] (x : X)

/-- Given a topological space `X` and `x : X`, this is the point of the site
`(Opens X, Opens.grothendieckTopology X)` corresponding to `x`. -/
def pointGrothendieckTopology : Point.{u} (grothendieckTopology X) where
  fiber.obj U := ULift.{u} (PLift (x ∈ U))
  fiber.map f := ↾ fun h ↦ ⟨⟨leOfHom f h.down.down⟩⟩
  isCofiltered :=
    { nonempty := ⟨⊤, ⟨⟨by simp⟩⟩⟩
      cone_objs := by
        rintro ⟨U, ⟨⟨hU⟩⟩⟩ ⟨V, ⟨⟨hV⟩⟩⟩
        exact ⟨⟨U ⊓ V, ⟨⟨⟨hU, hV⟩⟩⟩⟩, ⟨homOfLE (by simp), rfl⟩,
          ⟨homOfLE (by simp), rfl⟩, ⟨⟩⟩
      cone_maps _ _ _ _ := ⟨_, 𝟙 _, rfl⟩ }
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective := by
    rintro U R hR ⟨⟨hU⟩⟩
    obtain ⟨V, f, hf, hV⟩ := hR x hU
    exact ⟨_, _, hf, ⟨⟨hV⟩⟩, rfl⟩

variable (X) in
/-- When `X` is a topological space, this is the obvious conservative family of
points on the site `(Opens X, Opens.grothendieckTopology X)`. -/
def pointsGrothendieckTopology : ObjectProperty (Point.{u} (grothendieckTopology X)) :=
  ObjectProperty.ofObj pointGrothendieckTopology
  deriving ObjectProperty.Small.{u}

variable (X) in
lemma isConservativeFamilyOfPoints_pointsGrothendieckTopology :
    (pointsGrothendieckTopology X).IsConservativeFamilyOfPoints :=
  .mk' (fun U S hS x hx ↦ by
    obtain ⟨V, f, hf, ⟨⟨hV⟩⟩, _⟩ := hS ⟨_, ⟨x⟩⟩ ⟨⟨hx⟩⟩
    exact ⟨V, f, hf, hV⟩)

instance : HasEnoughPoints.{u} (grothendieckTopology X) where
  exists_objectProperty :=
    ⟨_, inferInstance, isConservativeFamilyOfPoints_pointsGrothendieckTopology X⟩

instance (U : Opens X) (Φ : Point.{u} (grothendieckTopology X)) :
    Subsingleton (Φ.fiber.obj U) :=
  Φ.subsingleton_fiber_obj (homOfLE le_top) Limits.isTerminalTop

instance : Quiver.IsThin (Point.{u} (grothendieckTopology X)) :=
  fun _ _ ↦ ⟨fun _ _ ↦ by ext; subsingleton⟩

/-- A point `x` of a topological space `X` specializes to `y` if and only iff
there is a (unique) morphism between the corresponding points of the site
`(Opens X, grothendieckTopology X)`. -/
def pointGrothendieckTopologyHomEquiv {x y : X} :
    (pointGrothendieckTopology x ⟶ pointGrothendieckTopology y) ≃ x ⤳ y where
  toFun f := specializes_iff_forall_open.2 (fun U h₁ h₂ ↦ (f.hom.app ⟨U, h₁⟩ ⟨⟨h₂⟩⟩).down.down)
  invFun s := { hom.app U := ↾ fun hU ↦
    ⟨⟨specializes_iff_forall_open.1 s _ U.2 hU.down.down⟩⟩ }
  left_inv _ := by subsingleton
  right_inv _ := rfl

end Opens
