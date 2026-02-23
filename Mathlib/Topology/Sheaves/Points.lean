/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# The standard conservative families of points for the site attached to a topological space

If `X` is a topological space, any `x : X` defined a point of the site
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

def pointGrothendieckTopology.fiber : Opens X ⥤ Type u where
  obj U := ULift.{u} (PLift (x ∈ U))
  map f h := ⟨⟨leOfHom f h.down.down⟩⟩

instance : IsCofiltered (pointGrothendieckTopology.fiber x).Elements where
  nonempty := ⟨⊤, ⟨⟨by simp⟩⟩⟩
  cone_objs := by
    rintro ⟨U, ⟨⟨hU⟩⟩⟩ ⟨V, ⟨⟨hV⟩⟩⟩
    exact ⟨⟨U ⊓ V, ⟨⟨⟨hU, hV⟩⟩⟩⟩, ⟨homOfLE (by simp), rfl⟩,
      ⟨homOfLE (by simp), rfl⟩, ⟨⟩⟩
  cone_maps _ _ _ _ := ⟨_, 𝟙 _, rfl⟩

instance : InitiallySmall.{u} (pointGrothendieckTopology.fiber x).Elements :=
  initiallySmall_of_essentiallySmall _

/-- Given a topological space `X` and `x : X`, this is the point of the site
`(Opens X, Opens.grothendieckTopology X)` corresponding to `x`. -/
def pointGrothendieckTopology : Point.{u} (grothendieckTopology X) where
  fiber := pointGrothendieckTopology.fiber x
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
lemma isConservative_pointsGrothendieckTopology :
    (pointsGrothendieckTopology X).IsConservativeFamilyOfPoints :=
  .mk' (fun U S hS x hx ↦ by
    obtain ⟨V, f, hf, ⟨⟨hV⟩⟩, _⟩ := hS ⟨_, ⟨x⟩⟩ ⟨⟨hx⟩⟩
    exact ⟨V, f, hf, hV⟩)

instance : HasEnoughPoints.{u} (grothendieckTopology X) where
  exists_objectProperty :=
    ⟨_, inferInstance, isConservative_pointsGrothendieckTopology X⟩

end Opens
