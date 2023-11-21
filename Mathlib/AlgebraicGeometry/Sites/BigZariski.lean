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

universe u

open CategoryTheory

lemma CategoryTheory.Presieve.ofArrows.mk' {C : Type*} [Category C] {ι : Type*}
    (Y : ι → C) {X : C} (f : ∀ i, Y i ⟶ X) {Z : C} (g : Z ⟶ X) (i : ι) (hZ : Z = Y i)
    (hg : g = eqToHom hZ ≫ f i) :
    Presieve.ofArrows Y f g := by
  subst hZ
  obtain rfl : g = f i := by simpa using hg
  exact ⟨i⟩

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
    let S := fun (j : U.J) ↦ T (U.map j) ⟨j⟩
    let V : ∀ (j : U.J), OpenCover (U.obj j) := fun j => (H (U.map j) ⟨j⟩).choose
    have hV : ∀ (j : U.J) , S j = Presieve.ofArrows (V j).obj (V j).map :=
      fun j => (H (U.map j) ⟨j⟩).choose_spec
    obtain ⟨σ, hσ⟩  : ∃ (σ : ∀ (x : X), U.obj (U.f x)),
      ∀ (x : X), (U.map (U.f x)).1.base (σ x) = x := ⟨fun x => (U.Covers x).choose,
        fun x => (U.Covers x).choose_spec⟩
    let W : OpenCover.{u} X :=
      { J := Sigma (fun (j : U.J) ↦ (V j).J)
        obj := fun ⟨j, k⟩ => (V j).obj k
        map := fun ⟨j, k⟩ => (V j).map k ≫ U.map j
        f := fun x => ⟨U.f x, (V (U.f x)).f (σ x)⟩
        Covers := fun x => by
          obtain ⟨y, hy⟩ := (V (U.f x)).Covers (σ x)
          exact ⟨y, (congr_arg (U.map (U.f x)).1.base hy).trans (hσ _)⟩ }
    refine' ⟨W, _⟩
    funext Y
    ext f
    constructor
    · rintro ⟨Z, a, _, ⟨j⟩, (h : S _ _), rfl⟩
      rw [hV] at h
      obtain ⟨j⟩ := h
      exact Presieve.ofArrows.mk' _ _ _ ⟨_, j⟩ rfl (by simp)
    · rintro ⟨j, k⟩
      exact ⟨_, (V j).map k, _, ⟨j⟩, show S _ _ by rw [hV]; exact ⟨k⟩, rfl⟩

/-- The Zariski topology on the category of schemes. -/
abbrev zariskiTopology : GrothendieckTopology (Scheme.{u}) :=
  zariskiPretopology.{u}.toGrothendieck

end Scheme

end AlgebraicGeometry
