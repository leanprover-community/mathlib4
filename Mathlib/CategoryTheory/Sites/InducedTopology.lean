/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Sites.DenseSubsite

/-!
# Induced Topology

We say that a functor `G : C ⥤ (D, K)` is locally dense if for each covering sieve `T` in `D` of
some `X : C`, `T ∩ mor(C)` generates a covering sieve of `X` in `D`. A locally dense fully faithful
functor then induces a topology on `C` via `{ T ∩ mor(C) | T ∈ K }`. Note that this is equal to
the collection of sieves on `C` whose image generates a covering sieve. This construction would
make `C` both cover-lifting and cover-preserving.

Some typical examples are full and cover-dense functors (for example the functor from a basis of a
topological space `X` into `Opens X`). The functor `Over X ⥤ C` is also locally dense, and the
induced topology can then be used to construct the big sites associated to a scheme.

Given a cover-dense functor `G : C ⥤ (D, K)` between small sites, we then have
`Sheaf (H.inducedTopology) A ≌ Sheaf K A`. This is known as the comparison lemma.

## References

* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.2.
* https://ncatlab.org/nlab/show/dense+sub-site
* https://ncatlab.org/nlab/show/comparison+lemma

-/


namespace CategoryTheory

universe v u

open Limits Opposite Presieve

variable {C : Type*} [Category C] {D : Type*} [Category D] (G : C ⥤ D)
variable (K : GrothendieckTopology D)
variable (A : Type v) [Category.{u} A]

namespace Functor

/-- If a functor `G : C ⥤ (D, K)` is fully faithful and locally dense,
then the set `{ T ∩ mor(C) | T ∈ K }` is a grothendieck topology of `C`.
-/
@[simps]
def inducedTopology [G.IsCoverDense K] : GrothendieckTopology C where
  sieves X S := K _ (S.functorPushforward G)
  top_mem' X := by
    change K _ _
    rw [Sieve.functorPushforward_top]
    exact K.top_mem _
  pullback_stable' X Y S iYX hS := by
    apply K.transitive (K.pullback_stable (G.map iYX) hS)
    intro V iVY ⟨W, iWX, iVW, hiWX, e₁⟩
    apply K.transitive (G.coverByImage_mem _ _)
    rintro Z _ ⟨U, iZU, iUY, rfl⟩
    rw [Sieve.pullback_comp]
    apply K.pullback_stable
    clear iZU Z
    rw [← Sieve.pullback_comp]
    apply K.transitive (G.functorPushforward_hasLift_mem _ (iUY ≫ iVY))
    rintro Z _ ⟨U₁, iU₁U, iZU₁, ⟨iU₁Y, e₂⟩, rfl⟩
    rw [Sieve.pullback_comp]
    apply K.pullback_stable
    clear iZU₁ Z
    apply K.transitive (G.functorPushforward_hasLift_mem _ (G.map iU₁U ≫ iUY ≫ iVW))
    rintro Z _ ⟨U₂, iU₂U₁, iZU₂, ⟨iU₂W, e₃⟩, rfl⟩
    rw [Sieve.pullback_comp]
    apply K.pullback_stable
    clear iZU₂ Z
    apply K.superset_covering ?_
      (G.functorPushforward_equalizer_mem _ (iU₂U₁ ≫ iU₁Y ≫ iYX) (iU₂W ≫ iWX)
        (by simp [e₁, e₂, e₃]))
    rintro Z _ ⟨U₃, iU₃U₂, iZU₃, e₄ : _ = _, rfl⟩
    simp_rw [← Sieve.pullback_comp, ← e₂, ← G.map_comp]
    refine ⟨_, iU₃U₂ ≫ iU₂U₁ ≫ iU₁Y, iZU₃, ?_, by simp⟩
    simpa [e₄] using S.downward_closed hiWX (iU₃U₂ ≫ iU₂W)
  transitive' X S hS S' H' := by
    apply K.transitive hS
    rintro Y _ ⟨Z, g, i, hg, rfl⟩
    rw [Sieve.pullback_comp]
    apply K.pullback_stable i
    refine K.superset_covering ?_ (H' hg)
    rintro W _ ⟨Z', g', i', hg, rfl⟩
    refine ⟨Z', g' ≫ g , i', hg, ?_⟩
    simp

/-- If `J` is the induced topology of `K` along `G`,
then `(C, J)` is a denses subsite of `(D, K)`. -/
instance [G.IsCoverDense K] :
    G.IsDenseSubsite (G.inducedTopology K) K where
  isDense := inferInstance
  functorPushforward_mem_iff := Iff.rfl

@[deprecated (since := "2024-07-23")]
alias inducedTopologyOfIsCoverDense := Functor.inducedTopology

/-- Cover-dense functors induces an equivalence of categories of sheaves.

This is known as the comparison lemma. It requires that the sites are small and the value category
is complete.
-/
noncomputable def sheafInducedTopologyEquivOfIsCoverDense
    [G.IsCoverDense K] [∀ (X : Dᵒᵖ), HasLimitsOfShape (StructuredArrow X G.op) A] :
    Sheaf (G.inducedTopology K) A ≌ Sheaf K A :=
  Functor.IsCoverDense.sheafEquivOfCoverPreservingCoverLifting G
    (G.inducedTopology K) K A

end Functor

end CategoryTheory
