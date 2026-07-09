/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Over
public import Mathlib.AlgebraicGeometry.Sites.Pretopology
public import Mathlib.CategoryTheory.MorphismProperty.CommaSites
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Small sites

In this file we define the small sites associated to morphism properties and give
generating pretopologies.

## Main definitions

- `AlgebraicGeometry.Scheme.overGrothendieckTopology`: the Grothendieck topology on `Over S`
  obtained by localizing the topology on `Scheme` induced by `P` at `S`.
- `AlgebraicGeometry.Scheme.overPretopology`: the pretopology on `Over S` defined by
  `P`-coverings of `S`-schemes. The induced topology agrees with
  `AlgebraicGeometry.Scheme.overGrothendieckTopology`.
- `AlgebraicGeometry.Scheme.smallGrothendieckTopology`: the by the inclusion
  `P.Over ⊤ S ⥤ Over S` induced topology on `P.Over ⊤ S`.
- `AlgebraicGeometry.Scheme.smallPretopology`: the pretopology on `P.Over ⊤ S` defined by
  `P`-coverings of `S`-schemes with `P`. The induced topology agrees
  with `AlgebraicGeometry.Scheme.smallGrothendieckTopology`.

-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {P Q : MorphismProperty Scheme.{u}} {S : Scheme.{u}}

variable [Q.IsStableUnderComposition]

private lemma map_functorPullback_mem_coverings (hPQ : P ≤ Q) (X : Q.Over ⊤ S)
    {R : Presieve ((MorphismProperty.Over.forget Q ⊤ S).obj X)}
    (hR : R ∈ ((precoverage P).over S).coverings ((MorphismProperty.Over.forget Q ⊤ S).obj X)) :
    letI F := MorphismProperty.Over.forget Q ⊤ S
    (R.functorPullback F).map F ∈ ((precoverage P).over S).coverings (F.obj X) := by
  have hle : precoverage P ≤ Q.precoverage := fun _ _ hR _ _ hf ↦ hPQ _ (hR.2 hf)
  obtain ⟨T, rfl⟩ := MorphismProperty.exists_map_eq_of_presieve (precoverage P) hle hR
  simpa using hR

variable [P.IsStableUnderBaseChange]

/-- The presieve defined by a `P`-cover of `S`-schemes. -/
def Cover.toPresieveOver {X : Over S} (𝒰 : Cover.{u} (precoverage P) X.left) [𝒰.Over S] :
    Presieve X :=
  Presieve.ofArrows (fun i ↦ (𝒰.X i).asOver S) (fun i ↦ (𝒰.f i).asOver S)

/-- The presieve defined by a `P`-cover of `S`-schemes with `Q`. -/
def Cover.toPresieveOverProp {X : Q.Over ⊤ S} (𝒰 : Cover.{u} (precoverage P) X.left) [𝒰.Over S]
    (h : ∀ j, Q (𝒰.X j ↘ S)) : Presieve X :=
  Presieve.ofArrows (fun i ↦ (𝒰.X i).asOverProp S (h i)) (fun i ↦ (𝒰.f i).asOverProp S)

set_option backward.defeqAttrib.useBackward true in
lemma Cover.overEquiv_generate_toPresieveOver_eq_ofArrows {X : Over S}
    (𝒰 : Cover.{u} (precoverage P) X.left)
    [𝒰.Over S] : Sieve.overEquiv X (Sieve.generate 𝒰.toPresieveOver) =
      Sieve.ofArrows 𝒰.X 𝒰.f := by
  ext V f
  simp only [Sieve.overEquiv_iff, Sieve.generate_apply]
  constructor
  · rintro ⟨U, h, g, ⟨k⟩, hcomp⟩
    exact ⟨𝒰.X k, h.left, 𝒰.f k, ⟨k⟩, congrArg CommaMorphism.left hcomp⟩
  · rintro ⟨U, h, g, ⟨k⟩, hcomp⟩
    have : 𝒰.f k ≫ X.hom = 𝒰.X k ↘ S := comp_over (𝒰.f k) S
    refine ⟨(𝒰.X k).asOver S, Over.homMk h (by simp [← hcomp, this]), (𝒰.f k).asOver S, ⟨k⟩, ?_⟩
    ext : 1
    simpa

lemma Cover.toPresieveOver_le_arrows_iff {X : Over S} (R : Sieve X)
    (𝒰 : Cover.{u} (precoverage P) X.left) [𝒰.Over S] :
    𝒰.toPresieveOver ≤ R.arrows ↔
      Presieve.ofArrows 𝒰.X 𝒰.f ≤ (Sieve.overEquiv X R).arrows := by
  simp_rw [← Sieve.giGenerate.gc.le_iff_le, ← (Sieve.overEquiv X).map_rel_iff]
  rw [overEquiv_generate_toPresieveOver_eq_ofArrows]

variable [P.IsMultiplicative] [P.RespectsIso]

variable (P Q S)

abbrev overPretopology : Pretopology (Over S) :=
  ((Scheme.precoverage P).over S).toPretopology

/-- The topology on `Over S` induced from the topology on `Scheme` defined by `P`.
This agrees with the topology induced by `S.overPretopology P`, see
`AlgebraicGeometry.Scheme.overGrothendieckTopology_eq_toGrothendieck_overPretopology`. -/
abbrev overGrothendieckTopology : GrothendieckTopology (Over S) :=
  (Scheme.grothendieckTopology P).over S

lemma overGrothendieckTopology_eq_toGrothendieck_overPretopology :
    S.overGrothendieckTopology P = (S.overPretopology P).toGrothendieck := by
  rw [Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck]
  exact over_toGrothendieck_eq_toGrothendieck_comap_forget (precoverage P) S

variable {S}

omit [P.RespectsIso] in
lemma mem_overGrothendieckTopology (X : Over S) (R : Sieve X) :
    R ∈ S.overGrothendieckTopology P X ↔
      ∃ (𝒰 : Cover.{u} (precoverage P) X.left) (_ : 𝒰.Over S), 𝒰.toPresieveOver ≤ R.arrows := by
  rw [GrothendieckTopology.mem_over_iff, mem_grothendieckTopology_iff]
  constructor
  · rintro ⟨𝒰, hle⟩
    letI (i : 𝒰.I₀) : (𝒰.X i).Over S := { hom := 𝒰.f i ≫ X.hom }
    letI : 𝒰.Over S :=
      { over := inferInstance
        isOver_map := fun i ↦ ⟨rfl⟩ }
    refine ⟨𝒰, inferInstance, ?_⟩
    rwa [Cover.toPresieveOver_le_arrows_iff]
  · rintro ⟨𝒰, h𝒰, hle⟩
    exact ⟨𝒰, (Cover.toPresieveOver_le_arrows_iff R 𝒰).mp hle⟩

variable (S) {P Q} in
lemma locallyCoverDense_of_le (hPQ : P ≤ Q) :
    (MorphismProperty.Over.forget Q ⊤ S).LocallyCoverDense (overGrothendieckTopology P S) := by
  rw [overGrothendieckTopology_eq_toGrothendieck_overPretopology,
    Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck]
  apply Precoverage.locallyCoverDense_of_map_functorPullback_mem
  apply map_functorPullback_mem_coverings hPQ

instance : (MorphismProperty.Over.forget P ⊤ S).LocallyCoverDense (overGrothendieckTopology P S) :=
  locallyCoverDense_of_le S le_rfl

variable (S) {Q} in
/-- If `P` and `Q` are morphism properties with `P ≤ Q`, this is the Grothendieck topology
induced via the forgetful functor `Q.Over ⊤ S ⥤ Over S` by the topology defined by `P`. -/
abbrev smallGrothendieckTopology : GrothendieckTopology (Q.Over ⊤ S) :=
  (MorphismProperty.Over.forget Q ⊤ S).restrictedTopology (S.overGrothendieckTopology P)

@[deprecated (since := "2026-05-28")]
alias smallGrothendieckTopologyOfLE := smallGrothendieckTopology

variable [Q.IsStableUnderBaseChange] [Q.HasOfPostcompProperty Q]

/-- The pretopology defined on the subcategory of `S`-schemes satisfying `Q` where coverings
are given by `P`-coverings in `S`-schemes satisfying `Q`.
The most common case is `P = Q`. In this case, this is simply surjective families
in `S`-schemes with `P`. -/
abbrev smallPretopology : Pretopology (Q.Over ⊤ S) :=
  (((precoverage P).over S).comap (MorphismProperty.Over.forget Q ⊤ S)).toPretopology

variable (S) {P Q} in
lemma smallGrothendieckTopology_eq_toGrothendieck_smallPretopology (hPQ : P ≤ Q) :
    S.smallGrothendieckTopology P = (S.smallPretopology P Q).toGrothendieck := by
  rw [smallGrothendieckTopology, overGrothendieckTopology_eq_toGrothendieck_overPretopology,
    Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck,
    Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck,
    ← Precoverage.toGrothendieck_comap_eq_restrictedTopology]
  apply map_functorPullback_mem_coverings hPQ

@[deprecated (since := "2026-05-28")]
alias smallGrothendieckTopologyOfLE_eq_toGrothendieck_smallPretopology :=
  smallGrothendieckTopology_eq_toGrothendieck_smallPretopology

variable {P Q}

lemma mem_toGrothendieck_smallPretopology (X : Q.Over ⊤ S) (R : Sieve X) :
    R ∈ (S.smallPretopology P Q).toGrothendieck X ↔
      ∀ x : X.left, ∃ (Y : Q.Over ⊤ S) (f : Y ⟶ X) (y : Y.left),
        R f ∧ P f.left ∧ f.left y = x := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨T, ⟨hs, hP⟩, hle⟩ x
    obtain ⟨Z, g, hg, hx⟩ := (Presieve.mem_comap_jointlySurjectivePrecoverage_iff _).mp hs x
    obtain ⟨hg⟩ := hg
    obtain ⟨hf⟩ := hg
    obtain ⟨y, hy⟩ := hx
    exact ⟨_, _, y, hle _ _ hf, hP (Presieve.map_map (Presieve.map_map hf)), hy⟩
  · refine ⟨fun Y f ↦ R f ∧ P f.left, ⟨?_, ?_⟩, fun Y f hf ↦ hf.1⟩
    · refine (Presieve.mem_comap_jointlySurjectivePrecoverage_iff _).mpr fun x ↦ ?_
      obtain ⟨Y, f, y, hR, hP, hy⟩ := h x
      exact ⟨Y.left, f.left, Presieve.map_map (Presieve.map_map ⟨hR, hP⟩), y, hy⟩
    · rintro Z g ⟨⟨⟨-, hP⟩⟩⟩
      exact hP

lemma mem_smallGrothendieckTopology (X : P.Over ⊤ S) (R : Sieve X) :
    R ∈ S.smallGrothendieckTopology P X ↔
      ∃ (𝒰 : Cover.{u} (precoverage P) X.left) (_ : 𝒰.Over S) (h : ∀ j, P (𝒰.X j ↘ S)),
          𝒰.toPresieveOverProp h ≤ R.arrows := by
  simp only [smallGrothendieckTopology, Functor.mem_restrictedTopology_iff,
    mem_overGrothendieckTopology]
  constructor
  · rintro ⟨𝒰, h𝒰, hle⟩
    have hj (j : 𝒰.I₀) : P (𝒰.X j ↘ S) := by
      rw [← comp_over (𝒰.f j) S]
      exact P.comp_mem _ _ (𝒰.map_prop j) X.prop
    refine ⟨𝒰, h𝒰, hj, ?_⟩
    rintro - - ⟨i⟩
    let fi : (𝒰.X i).asOverProp S (hj i) ⟶ X := (𝒰.f i).asOverProp S
    have h : R.functorPushforward _ ((MorphismProperty.Over.forget P ⊤ S).map fi) := hle _ _ ⟨i⟩
    rwa [Sieve.functorPushforward_apply, Sieve.mem_functorPushforward_iff_of_full_of_faithful] at h
  · rintro ⟨𝒰, h𝒰, p, hle⟩
    refine ⟨𝒰, h𝒰, ?_⟩
    rintro - - ⟨i⟩
    exact ⟨(𝒰.X i).asOverProp S (p i), (𝒰.f i).asOverProp S, 𝟙 _, hle _ _ ⟨i⟩, rfl⟩

end AlgebraicGeometry.Scheme
