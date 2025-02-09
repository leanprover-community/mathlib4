/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

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

Given a fully faithful cover-dense functor `G : C ⥤ (D, K)` between small sites, we then have
`Sheaf (H.inducedTopology) A ≌ Sheaf K A`. This is known as the comparison lemma.

## References

* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.2.
* https://ncatlab.org/nlab/show/dense+sub-site
* https://ncatlab.org/nlab/show/comparison+lemma

-/

namespace CategoryTheory

universe v u

open Limits Opposite Presieve CategoryTheory

variable {C : Type*} [Category C] {D : Type*} [Category D] (G : C ⥤ D)
variable {J : GrothendieckTopology C} (K : GrothendieckTopology D)
variable (A : Type v) [Category.{u} A]

namespace Functor

-- variables (A) [full G] [faithful G]
/-- We say that a functor `C ⥤ D` into a site is "locally dense" if
for each covering sieve `T` in `D`, `T ∩ mor(C)` generates a covering sieve in `D`.
-/
class LocallyCoverDense : Prop where
  functorPushforward_functorPullback_mem :
    ∀ ⦃X : C⦄ (T : K (G.obj X)), (T.val.functorPullback G).functorPushforward G ∈ K (G.obj X)

variable [G.LocallyCoverDense K]

theorem pushforward_cover_iff_cover_pullback [G.Full] [G.Faithful] {X : C} (S : Sieve X) :
    K _ (S.functorPushforward G) ↔ ∃ T : K (G.obj X), T.val.functorPullback G = S := by
  constructor
  · intro hS
    exact ⟨⟨_, hS⟩, (Sieve.fullyFaithfulFunctorGaloisCoinsertion G X).u_l_eq S⟩
  · rintro ⟨T, rfl⟩
    exact LocallyCoverDense.functorPushforward_functorPullback_mem T

variable [G.IsLocallyFull K] [G.IsLocallyFaithful K]

/-- If a functor `G : C ⥤ (D, K)` is fully faithful and locally dense,
then the set `{ T ∩ mor(C) | T ∈ K }` is a grothendieck topology of `C`.
-/
@[simps]
def inducedTopology : GrothendieckTopology C where
  sieves _ S := K _ (S.functorPushforward G)
  top_mem' X := by
    change K _ _
    rw [Sieve.functorPushforward_top]
    exact K.top_mem _
  pullback_stable' X Y S iYX hS := by
    apply K.transitive (LocallyCoverDense.functorPushforward_functorPullback_mem
      ⟨_, K.pullback_stable (G.map iYX) hS⟩)
    rintro Z _ ⟨U, iUY, iZU, ⟨W, iWX, iUW, hiWX, e₁⟩, rfl⟩
    rw [Sieve.pullback_comp]
    apply K.pullback_stable
    clear iZU Z
    apply K.transitive (G.functorPushforward_imageSieve_mem _ iUW)
    rintro Z _ ⟨U₁, iU₁U, iZU₁, ⟨iU₁W, e₂⟩, rfl⟩
    rw [Sieve.pullback_comp]
    apply K.pullback_stable
    clear iZU₁ Z
    apply K.superset_covering ?_ (G.functorPushforward_equalizer_mem _
      (iU₁U ≫ iUY ≫ iYX) (iU₁W ≫ iWX) (by simp [e₁, e₂]))
    rintro Z _ ⟨U₂, iU₂U₁, iZU₂, e₃ : _ = _, rfl⟩
    refine ⟨_, iU₂U₁ ≫ iU₁U ≫ iUY, iZU₂, ?_, by simp⟩
    simpa [e₃] using S.downward_closed hiWX (iU₂U₁ ≫ iU₁W)
  transitive' X S hS S' H' := by
    apply K.transitive hS
    rintro Y _ ⟨Z, g, i, hg, rfl⟩
    rw [Sieve.pullback_comp]
    apply K.pullback_stable i
    refine K.superset_covering ?_ (H' hg)
    rintro W _ ⟨Z', g', i', hg, rfl⟩
    refine ⟨Z', g' ≫ g , i', hg, ?_⟩
    simp

@[simp]
lemma mem_inducedTopology_sieves_iff {X : C} (S : Sieve X) :
    S ∈ (G.inducedTopology K) X ↔ (S.functorPushforward G) ∈ K (G.obj X) :=
  Iff.rfl

/-- `G` is cover-lifting wrt the induced topology. -/
instance inducedTopology_isCocontinuous : G.IsCocontinuous (G.inducedTopology K) K :=
  ⟨@fun _ S hS => LocallyCoverDense.functorPushforward_functorPullback_mem ⟨S, hS⟩⟩

/-- `G` is cover-preserving wrt the induced topology. -/
theorem inducedTopology_coverPreserving : CoverPreserving (G.inducedTopology K) K G :=
  ⟨@fun _ _ hS => hS⟩

instance (priority := 900) locallyCoverDense_of_isCoverDense [G.IsCoverDense K] :
    G.LocallyCoverDense K where
  functorPushforward_functorPullback_mem _ _ :=
    IsCoverDense.functorPullback_pushforward_covering _

instance (priority := 900) [G.IsCoverDense K] : G.IsDenseSubsite (G.inducedTopology K) K where
  functorPushforward_mem_iff := Iff.rfl

variable (J)

instance over_forget_locallyCoverDense (X : C) : (Over.forget X).LocallyCoverDense J where
  functorPushforward_functorPullback_mem Y T := by
    convert T.property
    ext Z f
    constructor
    · rintro ⟨_, _, g', hg, rfl⟩
      exact T.val.downward_closed hg g'
    · intro hf
      exact ⟨Over.mk (f ≫ Y.hom), Over.homMk f, 𝟙 _, hf, (Category.id_comp _).symm⟩

/-- Cover-dense functors induces an equivalence of categories of sheaves.

This is known as the comparison lemma. It requires that the sites are small and the value category
is complete.
-/
noncomputable def sheafInducedTopologyEquivOfIsCoverDense
    [G.IsCoverDense K] [∀ (X : Dᵒᵖ), HasLimitsOfShape (StructuredArrow X G.op) A] :
    Sheaf (G.inducedTopology K) A ≌ Sheaf K A :=
  Functor.IsDenseSubsite.sheafEquiv G
    (G.inducedTopology K) K A

end Functor

end CategoryTheory
