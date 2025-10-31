/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Sites.Pretopology
import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.CategoryTheory.Sites.Hypercover.Zero

/-!
# The site induced by a morphism property

Let `C` be a category with pullbacks and `P` be a multiplicative morphism property which is
stable under base change. Then `P` induces a pretopology, where coverings are given by presieves
whose elements satisfy `P`.

Standard examples of pretopologies in algebraic geometry, such as the étale site, are obtained from
this construction by intersecting with the pretopology of surjective families.

-/

universe w

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C]

namespace MorphismProperty

variable {P Q : MorphismProperty C}

/-- This is the precoverage on `C` where covering presieves are those where every
morphism satisfies `P`. -/
def precoverage (P : MorphismProperty C) : Precoverage C where
  coverings X S := ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → P f

@[simp]
lemma ofArrows_mem_precoverage {X : C} {ι : Type*} {Y : ι → C} {f : ∀ i, Y i ⟶ X} :
    .ofArrows Y f ∈ precoverage P X ↔ ∀ i, P (f i) :=
  ⟨fun h i ↦ h ⟨i⟩, fun h _ g ⟨i⟩ ↦ h i⟩

instance [P.ContainsIdentities] [P.RespectsIso] : P.precoverage.HasIsos where
  mem_coverings_of_isIso f _ _ _ := fun ⟨⟩ ↦ P.of_isIso f

instance [P.IsStableUnderBaseChange] : P.precoverage.IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι} S X f hf T g W p₁ p₂ h Z g hg := by
    obtain ⟨i⟩ := hg
    exact P.of_isPullback (h i).flip (hf ⟨i⟩)

instance [P.IsStableUnderComposition] : P.precoverage.IsStableUnderComposition where
  comp_mem_coverings {ι} S X f hf σ Y g hg Z p := by
    intro ⟨i⟩
    exact P.comp_mem _ _ (hg _ ⟨i.2⟩) (hf ⟨i.1⟩)

instance : Precoverage.Small.{w} P.precoverage where
  zeroHypercoverSmall E := by
    constructor
    use PEmpty, PEmpty.elim
    simp

lemma precoverage_monotone (hPQ : P ≤ Q) : precoverage P ≤ precoverage Q :=
  fun _ _ hR _ _ hg ↦ hPQ _ (hR hg)

variable (P Q) in
lemma precoverage_inf : precoverage (P ⊓ Q) = precoverage P ⊓ precoverage Q := by
  ext X R
  exact ⟨fun hS ↦ ⟨fun _ _ hf ↦ (hS hf).left, fun _ _ hf ↦ (hS hf).right⟩,
    fun h ↦ fun _ _ hf ↦ ⟨h.left hf, h.right hf⟩⟩

/-- If `P` is stable under base change, this is the coverage on `C` where covering presieves
are those where every morphism satisfies `P`. -/
@[simps toPrecoverage]
def coverage (P : MorphismProperty C) [P.IsStableUnderBaseChange] [P.HasPullbacks] :
    Coverage C where
  __ := precoverage P
  pullback X Y f S hS := by
    have : S.HasPullbacks f := ⟨fun {W} h hh ↦ P.hasPullback _ (hS hh)⟩
    refine ⟨S.pullbackArrows f, ?_, .pullbackArrows f S⟩
    intro Z g ⟨W, a, h⟩
    have := S.hasPullback f h
    exact P.pullback_snd _ _ (hS h)

/-- If `P` is stable under base change, it induces a Grothendieck topology: the one associated
to `coverage P`. -/
abbrev grothendieckTopology (P : MorphismProperty C) [P.IsStableUnderBaseChange] [P.HasPullbacks] :
    GrothendieckTopology C :=
  P.coverage.toGrothendieck

section HasPullbacks

variable [P.IsStableUnderBaseChange] [HasPullbacks C]

/-- If `P` is a multiplicative morphism property which is stable under base change on a category
`C` with pullbacks, then `P` induces a pretopology, where coverings are given by presieves whose
elements satisfy `P`. -/
@[simps! toPrecoverage]
def pretopology (P : MorphismProperty C) [P.IsMultiplicative] [P.IsStableUnderBaseChange] :
    Pretopology C :=
  (precoverage P).toPretopology

/-- If `P` is also multiplicative, the coverage induced by `P` is the pretopology induced by `P`. -/
lemma coverage_eq_toCoverage_pretopology [P.IsMultiplicative] :
    P.coverage = P.pretopology.toCoverage := rfl

/-- If `P` is also multiplicative, the topology induced by `P` is the topology induced by the
pretopology induced by `P`. -/
lemma grothendieckTopology_eq_toGrothendieck_pretopology [P.IsMultiplicative] :
    P.grothendieckTopology = P.pretopology.toGrothendieck := by
  rw [grothendieckTopology, coverage_eq_toCoverage_pretopology,
    Pretopology.toGrothendieck_toCoverage]

section

variable {P Q : MorphismProperty C}
  [P.IsMultiplicative] [P.IsStableUnderBaseChange]
  [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]

lemma pretopology_monotone (hPQ : P ≤ Q) : P.pretopology ≤ Q.pretopology :=
  precoverage_monotone hPQ

@[deprecated (since := "2025-08-28")]
alias pretopology_le := pretopology_monotone

variable (P Q) in
lemma pretopology_inf : (P ⊓ Q).pretopology = P.pretopology ⊓ Q.pretopology := by
  ext : 1
  simp only [pretopology_toPrecoverage, precoverage_inf]
  rfl

end

end HasPullbacks

end CategoryTheory.MorphismProperty
