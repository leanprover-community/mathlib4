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
the Zariski topology on `Over X` can be obtained as `Scheme.zariskiTopology.over X`.

-/

universe w v u

open CategoryTheory

-- to be moved
theorem CategoryTheory.Presieve.ofArrows_bind'
    {C : Type*} [Category C] {ι : Type*} {X : C} (Z : ι → C) (g : ∀ i : ι, Z i ⟶ X)
    {ι' : ι → Type*} (W : ∀ i, ι' i → C) (h : ∀ i i', W i i' ⟶ Z i)
    (T : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, ofArrows Z g f → Presieve Y)
    (hT : ∀ (i : ι), T ⟨i⟩ = ofArrows (W i) (h i)) :
    (ofArrows Z g).bind T =
      (ofArrows (fun (⟨i, i'⟩ : Sigma ι') => W i i') (fun ⟨i, i'⟩ => h i i' ≫ g i)) := by
  funext X
  ext f
  constructor
  · rintro ⟨Y, a, _, ⟨i⟩, h, rfl⟩
    rw [hT] at h
    obtain ⟨i'⟩ := h
    exact ⟨show Sigma ι' from ⟨i, i'⟩⟩
  · rintro ⟨i, i'⟩
    exact ⟨_, h i i', _, ⟨i⟩, by rw [hT]; exact ⟨i'⟩, rfl⟩

namespace AlgebraicGeometry

namespace Scheme

namespace OpenCover
-- to be moved

/-- Given `U : OpenCover X`, this is a choice of lifting of `x : X` in `U.obj (U.f x)`. -/
noncomputable def lift {X : Scheme} (U : OpenCover X) (x : X) : U.obj (U.f x) :=
  (U.Covers x).choose

@[simp]
lemma lift_covers {X : Scheme} (U : OpenCover X) (x : X) :
    (U.map (U.f x)).1.base (U.lift x) = x :=
  (U.Covers x).choose_spec

/-- Composition of open covers -/
@[simps J obj map]
noncomputable def trans {X : Scheme.{u}} (U : OpenCover.{v} X)
    (V : ∀ (j : U.J), OpenCover.{w} (U.obj j)) : OpenCover.{max v w} X where
  J := Sigma (fun j ↦ (V j).J)
  obj := fun ⟨j, k⟩ => (V j).obj k
  map := fun ⟨j, k⟩ => (V j).map k ≫ U.map j
  f x := ⟨U.f x, (V (U.f x)).f (U.lift x)⟩
  Covers x := ⟨(V (U.f x)).lift (U.lift x), by simp⟩

end OpenCover

/-- The Zariski pretopology on the category of schemes. -/
def zariskiPretopology : Pretopology (Scheme.{u}) where
  coverings Y S := ∃ (U : OpenCover.{u} Y), S = Presieve.ofArrows U.obj U.map
  has_isos Y X f _ := ⟨openCoverOfIsIso f, (Presieve.ofArrows_pUnit _).symm⟩
  pullbacks := by
    rintro Y X f _ ⟨U, rfl⟩
    exact ⟨U.pullbackCover' f, (Presieve.ofArrows_pullback _ _ _).symm⟩
  Transitive := by
    rintro X _ T ⟨U, rfl⟩ H
    let V : ∀ (j : U.J), OpenCover (U.obj j) := fun j => (H (U.map j) ⟨j⟩).choose
    exact ⟨U.trans V, Presieve.ofArrows_bind' U.obj U.map (fun i => (V i).obj)
      (fun i => (V i).map) T (fun j => (H (U.map j) ⟨j⟩).choose_spec)⟩

/-- The Zariski topology on the category of schemes. -/
abbrev zariskiTopology : GrothendieckTopology (Scheme.{u}) :=
  zariskiPretopology.{u}.toGrothendieck

end Scheme

end AlgebraicGeometry
