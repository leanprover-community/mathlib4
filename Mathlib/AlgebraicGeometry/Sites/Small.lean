/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Cover.Over
import Mathlib.AlgebraicGeometry.Sites.Pretopology
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.CategoryTheory.Sites.Over

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

universe v u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {P Q : MorphismProperty Scheme.{u}} {S : Scheme.{u}}
  [P.IsStableUnderBaseChange]

/-- The presieve defined by a `P`-cover of `S`-schemes. -/
def Cover.toPresieveOver {X : Over S} (𝒰 : Cover.{u} (precoverage P) X.left) [𝒰.Over S] :
    Presieve X :=
  Presieve.ofArrows (fun i ↦ (𝒰.X i).asOver S) (fun i ↦ (𝒰.f i).asOver S)

/-- The presieve defined by a `P`-cover of `S`-schemes with `Q`. -/
def Cover.toPresieveOverProp {X : Q.Over ⊤ S} (𝒰 : Cover.{u} (precoverage P) X.left) [𝒰.Over S]
    (h : ∀ j, Q (𝒰.X j ↘ S)) : Presieve X :=
  Presieve.ofArrows (fun i ↦ (𝒰.X i).asOverProp S (h i)) (fun i ↦ (𝒰.f i).asOverProp S)

lemma Cover.overEquiv_generate_toPresieveOver_eq_ofArrows {X : Over S}
    (𝒰 : Cover.{u} (precoverage P) X.left)
    [𝒰.Over S] : Sieve.overEquiv X (Sieve.generate 𝒰.toPresieveOver) =
      Sieve.ofArrows 𝒰.X 𝒰.f := by
  ext V f
  simp only [Sieve.overEquiv_iff, Functor.const_obj_obj, Sieve.generate_apply]
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
  simp_rw [← Sieve.giGenerate.gc.le_iff_le, ← Sieve.overEquiv_le_overEquiv_iff]
  rw [overEquiv_generate_toPresieveOver_eq_ofArrows]

variable [P.IsMultiplicative] [P.RespectsIso]

variable (P Q S)

/-- The pretopology on `Over S` induced by `P` where coverings are given by `P`-covers
of `S`-schemes. -/
def overPretopology : Pretopology (Over S) where
  coverings Y R := ∃ (𝒰 : Cover.{u} (precoverage P) Y.left) (_ : 𝒰.Over S), R = 𝒰.toPresieveOver
  has_isos {X Y} f _ := ⟨coverOfIsIso f.left, inferInstance, (Presieve.ofArrows_pUnit _).symm⟩
  pullbacks := by
    rintro Y X f _ ⟨𝒰, h, rfl⟩
    refine ⟨𝒰.pullbackCoverOver' S f.left, inferInstance, ?_⟩
    simpa [Cover.toPresieveOver] using
      (Presieve.ofArrows_pullback f (fun i ↦ (𝒰.X i).asOver S) (fun i ↦ (𝒰.f i).asOver S)).symm
  transitive := by
    rintro X _ T ⟨𝒰, h, rfl⟩ H
    choose V h hV using H
    refine ⟨𝒰.bind (fun j => V ((𝒰.f j).asOver S) ⟨j⟩), inferInstance, ?_⟩
    convert Presieve.ofArrows_bind _ (fun j ↦ (𝒰.f j).asOver S) _
      (fun Y f H j ↦ ((V f H).X j).asOver S) (fun Y f H j ↦ ((V f H).f j).asOver S)
    apply hV

/-- The topology on `Over S` induced from the topology on `Scheme` defined by `P`.
This agrees with the topology induced by `S.overPretopology P`, see
`AlgebraicGeometry.Scheme.overGrothendieckTopology_eq_toGrothendieck_overPretopology`. -/
abbrev overGrothendieckTopology : GrothendieckTopology (Over S) :=
  (Scheme.grothendieckTopology P).over S

lemma overGrothendieckTopology_eq_toGrothendieck_overPretopology :
    S.overGrothendieckTopology P = (S.overPretopology P).toGrothendieck := by
  ext X R
  rw [GrothendieckTopology.mem_over_iff]
  constructor
  · intro hR
    obtain ⟨𝒰, hle⟩ := exists_cover_of_mem_grothendieckTopology hR
    rw [mem_grothendieckTopology_iff] at hR
    letI (i : 𝒰.I₀) : (𝒰.X i).Over S := { hom := 𝒰.f i ≫ X.hom }
    letI : 𝒰.Over S :=
      { over := inferInstance
        isOver_map := fun i ↦ ⟨rfl⟩ }
    use 𝒰.toPresieveOver, ⟨𝒰, inferInstance, rfl⟩
    rwa [Cover.toPresieveOver_le_arrows_iff]
  · rintro ⟨T, ⟨𝒰, h, rfl⟩, hT⟩
    use Presieve.ofArrows 𝒰.X 𝒰.f, 𝒰.mem_pretopology
    rwa [Cover.toPresieveOver_le_arrows_iff] at hT

variable {S}

lemma mem_overGrothendieckTopology (X : Over S) (R : Sieve X) :
    R ∈ S.overGrothendieckTopology P X ↔
      ∃ (𝒰 : Cover.{u} (precoverage P) X.left) (_ : 𝒰.Over S), 𝒰.toPresieveOver ≤ R.arrows := by
  rw [overGrothendieckTopology_eq_toGrothendieck_overPretopology]
  constructor
  · rintro ⟨T, ⟨𝒰, h, rfl⟩, hle⟩
    use 𝒰, h
  · rintro ⟨𝒰, h𝒰, hle⟩
    exact ⟨𝒰.toPresieveOver, ⟨𝒰, h𝒰, rfl⟩, hle⟩

variable [Q.IsStableUnderComposition]

variable (S) {P Q} in
lemma locallyCoverDense_of_le (hPQ : P ≤ Q) :
    (MorphismProperty.Over.forget Q ⊤ S).LocallyCoverDense (overGrothendieckTopology P S) where
  functorPushforward_functorPullback_mem X := by
    intro ⟨T, hT⟩
    rw [mem_overGrothendieckTopology] at hT ⊢
    obtain ⟨𝒰, h, hle⟩ := hT
    use 𝒰, h
    rintro - - ⟨i⟩
    have p : Q (𝒰.X i ↘ S) := by
      rw [← comp_over (𝒰.f i) S]
      exact Q.comp_mem _ _ (hPQ _ <| 𝒰.map_prop i) X.prop
    use (𝒰.X i).asOverProp S p, MorphismProperty.Over.homMk (𝒰.f i) (comp_over (𝒰.f i) S), 𝟙 _
    exact ⟨hle _ ⟨i⟩, rfl⟩

instance : (MorphismProperty.Over.forget P ⊤ S).LocallyCoverDense (overGrothendieckTopology P S) :=
  locallyCoverDense_of_le S le_rfl

variable (S) {P Q} in
/-- If `P` and `Q` are morphism properties with `P ≤ Q`, this is the Grothendieck topology
induced via the forgetful functor `Q.Over ⊤ S ⥤ Over S` by the topology defined by `P`. -/
abbrev smallGrothendieckTopologyOfLE (hPQ : P ≤ Q) : GrothendieckTopology (Q.Over ⊤ S) :=
  letI : (MorphismProperty.Over.forget Q ⊤ S).LocallyCoverDense (overGrothendieckTopology P S) :=
    locallyCoverDense_of_le S hPQ
  (MorphismProperty.Over.forget Q ⊤ S).inducedTopology (S.overGrothendieckTopology P)

/-- The Grothendieck topology on the category of schemes over `S` with `P` induced by `P`, i.e.
coverings are simply surjective families. This is the induced topology by the topology on `S`
defined by `P` via the inclusion `P.Over ⊤ S ⥤ Over S`.

This is a special case of `smallGrothendieckTopologyOfLE` for the case `P = Q`. -/
abbrev smallGrothendieckTopology : GrothendieckTopology (P.Over ⊤ S) :=
  (MorphismProperty.Over.forget P ⊤ S).inducedTopology (S.overGrothendieckTopology P)

variable [Q.IsStableUnderBaseChange] [Q.HasOfPostcompProperty Q]

/-- The pretopology defined on the subcategory of `S`-schemes satisfying `Q` where coverings
are given by `P`-coverings in `S`-schemes satisfying `Q`.
The most common case is `P = Q`. In this case, this is simply surjective families
in `S`-schemes with `P`. -/
def smallPretopology : Pretopology (Q.Over ⊤ S) where
  coverings Y R :=
    ∃ (𝒰 : Cover.{u} (precoverage P) Y.left) (_ : 𝒰.Over S) (h : ∀ j : 𝒰.I₀, Q (𝒰.X j ↘ S)),
      R = 𝒰.toPresieveOverProp h
  has_isos {X Y} f := ⟨coverOfIsIso f.left, inferInstance, fun _ ↦ Y.prop,
    (Presieve.ofArrows_pUnit _).symm⟩
  pullbacks := by
    rintro Y X f _ ⟨𝒰, h, p, rfl⟩
    refine ⟨𝒰.pullbackCoverOverProp' S f.left (Q := Q) Y.prop X.prop p, inferInstance, ?_, ?_⟩
    · intro j
      apply MorphismProperty.Comma.prop
    · exact (Presieve.ofArrows_pullback f (fun i ↦ ⟨(𝒰.X i).asOver S, p i⟩)
        (fun i ↦ ⟨(𝒰.f i).asOver S, trivial, trivial⟩)).symm
  transitive := by
    rintro X _ T ⟨𝒰, h, p, rfl⟩ H
    choose V h pV hV using H
    let 𝒱j (j : 𝒰.I₀) : (Cover (precoverage P) ((𝒰.X j).asOverProp S (p j)).left) :=
      V ((𝒰.f j).asOverProp S) ⟨j⟩
    refine ⟨𝒰.bind (fun j ↦ 𝒱j j), inferInstance, fun j ↦ pV _ _ _, ?_⟩
    convert Presieve.ofArrows_bind _ (fun j ↦ ((𝒰.f j).asOverProp S)) _
      (fun Y f H j ↦ ((V f H).X j).asOverProp S (pV _ _ _))
      (fun Y f H j ↦ ((V f H).f j).asOverProp S)
    apply hV

variable (S) {P Q} in
lemma smallGrothendieckTopologyOfLE_eq_toGrothendieck_smallPretopology (hPQ : P ≤ Q) :
    S.smallGrothendieckTopologyOfLE hPQ = (S.smallPretopology P Q).toGrothendieck := by
  ext X R
  simp only [Pretopology.mem_toGrothendieck, Functor.mem_inducedTopology_sieves_iff,
    MorphismProperty.Comma.forget_obj, mem_overGrothendieckTopology]
  constructor
  · intro ⟨𝒰, h, le⟩
    have hj (j : 𝒰.I₀) : Q (𝒰.X j ↘ S) := by
      rw [← comp_over (𝒰.f j)]
      exact Q.comp_mem _ _ (hPQ _ <| 𝒰.map_prop _) X.prop
    refine ⟨𝒰.toPresieveOverProp hj, ?_, ?_⟩
    · use 𝒰, h, hj
    · rintro - - ⟨i⟩
      let fi : (𝒰.X i).asOverProp S (hj i) ⟶ X := (𝒰.f i).asOverProp S
      have : R.functorPushforward _ ((MorphismProperty.Over.forget Q ⊤ S).map fi) := le _ ⟨i⟩
      rwa [Sieve.functorPushforward_apply,
        Sieve.mem_functorPushforward_iff_of_full_of_faithful] at this
  · rintro ⟨T, ⟨𝒰, h, p, rfl⟩, le⟩
    use 𝒰, h
    rintro - - ⟨i⟩
    exact ⟨(𝒰.X i).asOverProp S (p i), (𝒰.f i).asOverProp S, 𝟙 _, le _ ⟨i⟩, rfl⟩

lemma smallGrothendieckTopology_eq_toGrothendieck_smallPretopology [P.HasOfPostcompProperty P] :
    S.smallGrothendieckTopology P = (S.smallPretopology P P).toGrothendieck :=
  S.smallGrothendieckTopologyOfLE_eq_toGrothendieck_smallPretopology le_rfl

variable {P Q}

lemma mem_toGrothendieck_smallPretopology (X : Q.Over ⊤ S) (R : Sieve X) :
    R ∈ (S.smallPretopology P Q).toGrothendieck X ↔
      ∀ x : X.left, ∃ (Y : Q.Over ⊤ S) (f : Y ⟶ X) (y : Y.left),
        R f ∧ P f.left ∧ f.left y = x := by
  rw [Pretopology.mem_toGrothendieck]
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨T, ⟨𝒰, h, p, rfl⟩, hle⟩
    intro x
    obtain ⟨y, hy⟩ := 𝒰.covers x
    refine ⟨(𝒰.X (𝒰.idx x)).asOverProp S (p _), (𝒰.f (𝒰.idx x)).asOverProp S, y, hle _ ?_,
      𝒰.map_prop _, hy⟩
    use 𝒰.idx x
  · choose Y f y hf hP hy using h
    let 𝒰 : X.left.Cover (precoverage P) :=
      { I₀ := X.left,
        X := fun i ↦ (Y i).left
        f := fun i ↦ (f i).left
        mem₀ := by
          rw [presieve₀_mem_precoverage_iff]
          refine ⟨fun x ↦ ⟨x, y x, hy x⟩, hP⟩ }
    letI : 𝒰.Over S :=
      { over := fun i ↦ inferInstance
        isOver_map := fun i ↦ inferInstance }
    refine ⟨𝒰.toPresieveOverProp fun i ↦ MorphismProperty.Comma.prop _, ?_, ?_⟩
    · use 𝒰, inferInstance, fun i ↦ MorphismProperty.Comma.prop _
    · rintro - - ⟨i⟩
      exact hf i

lemma mem_smallGrothendieckTopology [P.HasOfPostcompProperty P] (X : P.Over ⊤ S) (R : Sieve X) :
    R ∈ S.smallGrothendieckTopology P X ↔
      ∃ (𝒰 : Cover.{u} (precoverage P) X.left) (_ : 𝒰.Over S) (h : ∀ j, P (𝒰.X j ↘ S)),
          𝒰.toPresieveOverProp h ≤ R.arrows := by
  rw [smallGrothendieckTopology_eq_toGrothendieck_smallPretopology]
  constructor
  · rintro ⟨T, ⟨𝒰, h, p, rfl⟩, hle⟩
    use 𝒰, h, p
  · rintro ⟨𝒰, h𝒰, p, hle⟩
    exact ⟨𝒰.toPresieveOverProp p, ⟨𝒰, h𝒰, p, rfl⟩, hle⟩

end AlgebraicGeometry.Scheme
