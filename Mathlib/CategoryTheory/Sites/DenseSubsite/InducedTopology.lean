/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.InducedTopology

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

@[expose] public section

namespace CategoryTheory

universe v u

open Limits Opposite Presieve CategoryTheory

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (G : C ⥤ D)
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
    S.functorPushforward G ∈ K (G.obj X) ↔ ∃ T : K (G.obj X), T.val.functorPullback G = S := by
  constructor
  · intro hS
    exact ⟨⟨_, hS⟩, (Sieve.fullyFaithfulFunctorGaloisCoinsertion G X).u_l_eq S⟩
  · rintro ⟨T, rfl⟩
    exact LocallyCoverDense.functorPushforward_functorPullback_mem T

variable [G.IsLocallyFull K] [G.IsLocallyFaithful K]

/-- If `G` is locally fully faithful and locally cover dense, `G` is cover-preserving w.r.t. the
restricted topology. -/
theorem coverPreserving_restrictedTopology : CoverPreserving (G.restrictedTopology K) K G where
  cover_preserve hS := by
    rw [Functor.restrictedTopology] at hS
    induction hS with
    | of X S hS => rwa [← Sieve.generate_map_eq_functorPushforward]
    | top X => simp
    | pullback X S _ Y f ih =>
      apply K.transitive (LocallyCoverDense.functorPushforward_functorPullback_mem
        ⟨_, K.pullback_stable (G.map f) ih⟩)
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
        (iU₁U ≫ iUY ≫ f) (iU₁W ≫ iWX) (by simp [e₁, e₂]))
      rintro Z _ ⟨U₂, iU₂U₁, iZU₂, e₃ : _ = _, rfl⟩
      refine ⟨_, iU₂U₁ ≫ iU₁U ≫ iUY, iZU₂, ?_, by simp⟩
      simpa [e₃] using S.downward_closed hiWX (iU₂U₁ ≫ iU₁W)
    | transitive X S R _ _ hS H' =>
      apply K.transitive hS
      rintro Y _ ⟨Z, g, i, hg, rfl⟩
      rw [Sieve.pullback_comp]
      apply K.pullback_stable i
      refine K.superset_covering ?_ (H' hg)
      rintro W _ ⟨Z', g', i', hg, rfl⟩
      refine ⟨Z', g' ≫ g, i', hg, ?_⟩
      simp

@[deprecated (since := "2026-05-28")]
alias inducedTopology_coverPreserving := coverPreserving_restrictedTopology

variable {G K} in
/-- If a functor `G : C ⥤ (D, K)` is locally fully faithful and locally dense, `S` is
a covering in the restricted topology on `C` if its image generates a `K`-cover. -/
@[simp]
lemma mem_restrictedTopology_iff {X : C} {S : Sieve X} :
    S ∈ G.restrictedTopology K X ↔ S.functorPushforward G ∈ K (G.obj X) :=
  ⟨fun hS ↦ (G.coverPreserving_restrictedTopology K).cover_preserve hS,
    G.mem_restrictedTopology_of_functorPushforward_mem⟩

@[deprecated (since := "2026-05-28")]
alias mem_inducedTopology_sieves_iff := mem_restrictedTopology_iff

/-- `G` is cover-lifting w.r.t. the induced topology. -/
instance : G.IsCocontinuous (G.restrictedTopology K) K where
  cover_lift hS := by
    apply G.mem_restrictedTopology_of_functorPushforward_mem
    exact LocallyCoverDense.functorPushforward_functorPullback_mem ⟨_, hS⟩

instance (priority := 900) locallyCoverDense_of_isCoverDense [G.IsCoverDense K] :
    G.LocallyCoverDense K where
  functorPushforward_functorPullback_mem _ _ :=
    IsCoverDense.functorPullback_pushforward_covering _

instance (priority := 900) [G.IsCoverDense K] : G.IsDenseSubsite (G.restrictedTopology K) K where
  functorPushforward_mem_iff := mem_restrictedTopology_iff.symm

instance (priority := 900) [G.IsCoverDense K] : G.IsDenseSubsite (G.inducedTopology K) K := by
  rw [← restrictedTopology_eq_inducedTopology]
  infer_instance

@[simp]
lemma mem_inducedTopology_iff_of_isCoverDense [G.IsCoverDense K] {X : C} (S : Sieve X) :
    S ∈ G.inducedTopology K X ↔ S.functorPushforward G ∈ K (G.obj X) := by
  simp [← restrictedTopology_eq_inducedTopology]

variable (J)

instance over_forget_locallyCoverDense (X : C) : (Over.forget X).LocallyCoverDense J where
  functorPushforward_functorPullback_mem Y T := by
    convert! T.property
    ext Z f
    constructor
    · rintro ⟨_, _, g', hg, rfl⟩
      exact T.val.downward_closed hg g'
    · intro hf
      exact ⟨Over.mk (f ≫ Y.hom), Over.homMk f, 𝟙 _, hf, (Category.id_comp _).symm⟩

/-- Cover-dense functors induce an equivalence of categories of sheaves.

This is known as the comparison lemma. It requires that the sites are small and the value category
is complete.
-/
noncomputable def sheafInducedTopologyEquivOfIsCoverDense
    [G.IsCoverDense K] [∀ (X : Dᵒᵖ), HasLimitsOfShape (StructuredArrow X G.op) A] :
    Sheaf (G.inducedTopology K) A ≌ Sheaf K A :=
  Functor.IsDenseSubsite.sheafEquiv (G.inducedTopology K) K G A

end Functor

namespace Precoverage

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) (K : Precoverage D)

variable [K.HasIsos] [K.IsStableUnderBaseChange] [K.IsStableUnderComposition]
  [K.HasPullbacks]

lemma locallyCoverDense_of_map_functorPullback_mem
    (H : ∀ {S : C} {R : Presieve (F.obj S)}, R ∈ K (F.obj S) →
      Presieve.map F (Presieve.functorPullback F R) ∈ K (F.obj S)) :
    F.LocallyCoverDense K.toGrothendieck where
  functorPushforward_functorPullback_mem U := fun ⟨T, hT⟩ ↦ by
    rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hT ⊢
    obtain ⟨R, hR, hle⟩ := hT
    refine ⟨_, H hR, ?_⟩
    refine le_trans ?_
      (Presieve.functorPushforward_monotone (Presieve.functorPullback_monotone hle))
    rw [← Sieve.arrows_generate_map_eq_functorPushforward]
    exact Sieve.le_generate _

lemma toGrothendieck_comap_eq_restrictedTopology [F.Faithful] [F.Full]
    (H : ∀ {S : C} {R : Presieve (F.obj S)}, R ∈ K (F.obj S) →
      Presieve.map F (Presieve.functorPullback F R) ∈ K (F.obj S)) :
    (K.comap F).toGrothendieck = F.restrictedTopology K.toGrothendieck := by
  have : F.LocallyCoverDense K.toGrothendieck :=
    K.locallyCoverDense_of_map_functorPullback_mem F H
  refine le_antisymm ?_ fun X T hT ↦ ?_
  · apply toGrothendieck_comap_le_restrictedTopology
  · rw [Functor.mem_restrictedTopology_iff] at hT
    rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hT
    obtain ⟨R, hR, hle⟩ := hT
    refine GrothendieckTopology.superset_covering
        (S := Sieve.generate (Presieve.functorPullback F R)) _ ?_ ?_
    · refine le_trans (le_trans (Sieve.generate_functorPullback_le F R)
        (Sieve.functorPullback_monotone _ _ (Sieve.generate_mono hle))) ?_
      rw [Sieve.generate_sieve, Sieve.functorPullback_functorPushforward_eq]
    · exact Precoverage.generate_mem_toGrothendieck (H hR)

@[deprecated (since := "2026-05-28")]
alias toGrothendieck_comap_eq_inducedTopology := toGrothendieck_comap_eq_restrictedTopology

@[deprecated (since := "2026-05-28")]
alias toGrothendieck_comap_le_inducedTopology := toGrothendieck_comap_le_restrictedTopology

end Precoverage

end CategoryTheory
