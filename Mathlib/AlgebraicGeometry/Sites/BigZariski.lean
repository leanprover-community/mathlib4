/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Sites.Pretopology
/-!
# The big Zariski site of schemes

In this file, we define the Zariski topology, as a Grothendieck topology on the
category `Scheme.{u}`: this is `Scheme.zariskiTopology.{u}`. If `X : Scheme.{u}`,
the Zariski topology on `Over X` can be obtained as `Scheme.zariskiTopology.over X`
(see `CategoryTheory.Sites.Over`.).

-/

universe w v u

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
  Transitive := by
    rintro X _ T ⟨U, rfl⟩ H
    choose V hV using H
    use U.bind (fun j => V (U.map j) ⟨j⟩)
    simpa only [OpenCover.bind, ← hV] using Presieve.ofArrows_bind U.obj U.map _
      (fun _ f H => (V f H).obj) (fun _ f H => (V f H).map)

/-- The Zariski topology on the category of schemes. -/
abbrev zariskiTopology : GrothendieckTopology (Scheme.{u}) :=
  zariskiPretopology.{u}.toGrothendieck

end Scheme

end AlgebraicGeometry
