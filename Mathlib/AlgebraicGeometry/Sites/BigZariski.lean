/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Adam Topaz
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Sites.Pretopology
import Mathlib.CategoryTheory.Sites.Canonical
/-!
# The big Zariski site of schemes

In this file, we define the Zariski topology, as a Grothendieck topology on the
category `Scheme.{u}`: this is `Scheme.zariskiTopology.{u}`. If `X : Scheme.{u}`,
the Zariski topology on `Over X` can be obtained as `Scheme.zariskiTopology.over X`
(see `CategoryTheory.Sites.Over`.).

TODO:
* If `Y : Scheme.{u}`, define a continuous functor from the category of opens of `Y`
to `Over Y`, and show that a presheaf on `Over Y` is a sheaf for the Zariski topology
iff its "restriction" to the topological space `Z` is a sheaf for all `Z : Over Y`.
* We should have good notions of (pre)sheaves of `Type (u + 1)` (e.g. associated
sheaf functor, pushforward, pullbacks) on `Scheme.{u}` for this topology. However,
some constructions in the `CategoryTheory.Sites` folder currently assume that
the site is a small category: this should be generalized. As a result,
this big Zariski site can considered as a test case of the Grothendieck topology API
for future applications to étale cohomology.

-/

universe v u

open CategoryTheory

namespace AlgebraicGeometry

namespace Scheme

/-- The Zariski pretopology on the category of schemes. -/
def zariskiPretopology : Pretopology (Scheme.{u}) where
  coverings Y S := ∃ (U : OpenCover.{u} Y), S = Presieve.ofArrows U.obj U.map
  has_isos Y X f _ := ⟨openCoverOfIsIso f, (Presieve.ofArrows_pUnit _).symm⟩
  pullbacks := by
    rintro Y X f _ ⟨U, rfl⟩
    exact ⟨U.pullbackCover' f, (Presieve.ofArrows_pullback _ _ _).symm⟩
  transitive := by
    rintro X _ T ⟨U, rfl⟩ H
    choose V hV using H
    use U.bind (fun j => V (U.map j) ⟨j⟩)
    simpa only [OpenCover.bind, ← hV] using Presieve.ofArrows_bind U.obj U.map _
      (fun _ f H => (V f H).obj) (fun _ f H => (V f H).map)

/-- The Zariski topology on the category of schemes. -/
abbrev zariskiTopology : GrothendieckTopology (Scheme.{u}) :=
  zariskiPretopology.toGrothendieck

lemma zariskiPretopology_openCover {Y : Scheme.{u}} (U : OpenCover.{u} Y) :
    zariskiPretopology Y (Presieve.ofArrows U.obj U.map) :=
  ⟨U, rfl⟩

lemma zariskiTopology_openCover {Y : Scheme.{u}} (U : OpenCover.{v} Y) :
    zariskiTopology Y (Sieve.generate (Presieve.ofArrows U.obj U.map)) := by
  let V : OpenCover.{u} Y :=
    { J := Y
      obj := fun y => U.obj (U.f y)
      map := fun y => U.map (U.f y)
      f := id
      Covers := U.Covers
      IsOpen := fun _ => U.IsOpen _ }
  refine ⟨_, zariskiPretopology_openCover V, ?_⟩
  rintro _ _ ⟨y⟩
  exact ⟨_, 𝟙 _, U.map (U.f y), ⟨_⟩, by simp⟩

lemma subcanonical_zariskiTopology : Sheaf.Subcanonical zariskiTopology := by
  apply Sheaf.Subcanonical.of_yoneda_isSheaf
  intro X
  rw [Presieve.isSheaf_pretopology]
  rintro Y S ⟨𝓤,rfl⟩ x hx
  let e : Y ⟶ X := 𝓤.glueMorphisms (fun j => x (𝓤.map _) (.mk _)) <| by
    intro i j
    apply hx
    exact Limits.pullback.condition
  refine ⟨e, ?_, ?_⟩
  · rintro Z e ⟨j⟩
    dsimp [e]
    rw [𝓤.ι_glueMorphisms]
  · intro e' h
    apply 𝓤.hom_ext
    intro j
    rw [𝓤.ι_glueMorphisms]
    exact h (𝓤.map j) (.mk j)

end Scheme

end AlgebraicGeometry
