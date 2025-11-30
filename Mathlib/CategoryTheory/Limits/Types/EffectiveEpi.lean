/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Coequalizers
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono

/-!
# Epimorphisms of types are effective epimorphisms

We show that epimorphisms of types are regular epimorphisms.
In particular, they are effective epimorphisms.

-/

@[expose] public section

universe u

namespace CategoryTheory.Limits.Types

/-- Let `p : Y ⟶ X` be a morphism of types. Assume that `Z` is a pullback of
two copies of `p`. We done `p₁` and `p₂` the two projections `Z ⟶ Y`.
If `p` is surjective, then `p : Y ⟶ X` is the coequalizer of `p₁` and `p₂`. -/
noncomputable def isColimitCoforkOfIsPullbackOfSurjective
    {Z Y X : Type u} {p : Y ⟶ X} {p₁ p₂ : Z ⟶ Y} (sq : IsPullback p₁ p₂ p p)
    (hp : Function.Surjective p) :
    IsColimit (Cofork.ofπ _ sq.w) :=
  Nonempty.some (by
    rw [nonempty_isColimit_cofork_iff]
    obtain ⟨s, hs⟩ := hp.hasRightInverse
    let e : Function.Coequalizer p₁ p₂ ≃ X :=
      { toFun := Function.Coequalizer.desc p₁ p₂ p sq.w
        invFun x := Function.Coequalizer.mk _ _ (s x)
        left_inv y := by
          obtain ⟨y, rfl⟩ := y.mk_surjective
          obtain ⟨z, h₁, h₂⟩ := exists_of_isPullback sq (s (p y)) y (hs (p y))
          dsimp
          rw [← h₁, ← h₂, Function.Coequalizer.condition]
        right_inv := hs }
    exact e.bijective)

variable {X Y : Type u} (p : X ⟶ Y)

/-- If `p` is an epimorphism in the category of types,
then it is also a regular epimorphism. -/
noncomputable def regularEpiOfEpi [Epi p] : RegularEpi p where
  W := pullback p p
  left := pullback.fst _ _
  right := pullback.snd _ _
  w := pullback.condition
  isColimit :=
    isColimitCoforkOfIsPullbackOfSurjective (IsPullback.of_hasPullback p p) (by
      rw [← epi_iff_surjective]
      infer_instance)

lemma effectiveEpi_of_epi [Epi p] : EffectiveEpi p := by
  have := regularEpiOfEpi p
  infer_instance

end CategoryTheory.Limits.Types
