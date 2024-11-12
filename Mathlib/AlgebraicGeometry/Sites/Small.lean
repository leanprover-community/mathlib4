/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Cover.Over
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.CategoryTheory.Sites.MorphismProperty
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.InducedTopology

/-!
# Small sites

In this file we define the small sites associated to morphism properties and give
generating pretopologies.

-/

universe v u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative] [P.RespectsIso]
  [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P] [P.HasOfPostcompProperty]

variable (S : Scheme.{u})

instance {C : Type*} [Category C] {S : C} (X : Over S) : OverClass X.left S where
  hom := X.hom

instance {C : Type*} [Category C] {S : C} {X Y : Over S} (f : X ⟶ Y) : HomIsOver f.left S where
  comp_over := Over.w f

variable {S P} in
def Cover.toPresieveOver {X : Over S} (𝒰 : Cover.{u} P X.left) [𝒰.Over S] : Presieve X :=
  Presieve.ofArrows (fun i ↦ (𝒰.obj i).asOver S) (fun i ↦ (𝒰.map i).asOver S)

variable {S} {P} {Q : MorphismProperty Scheme.{u}} in
def Cover.toPresieveOverWithProp {X : P.Over ⊤ S} (𝒰 : Cover.{u} Q X.left) [𝒰.Over S]
    (h : ∀ j, P (𝒰.obj j ↘ S)) :
    Presieve X :=
  Presieve.ofArrows (fun i ↦ ⟨(𝒰.obj i).asOver S, h i⟩)
    (fun i ↦ ⟨(𝒰.map i).asOver S, trivial, trivial⟩)

lemma Cover.toPresieveOver_pullbackCover {X W : Over S} (𝒰 : Cover.{u} P X.left) [𝒰.Over S]
    (f : W ⟶ X) :
    (𝒰.pullbackCoverOver' S f.left).toPresieveOver = Presieve.pullbackArrows f 𝒰.toPresieveOver := by
  simpa [Cover.toPresieveOver] using
    Presieve.ofArrows_pullback f (fun i ↦ (𝒰.obj i).asOver S) (fun i ↦ (𝒰.map i).asOver S)

lemma foo {X : Over S} (𝒰 : Cover.{u} P X.left)
    [𝒰.Over S] :
    Sieve.overEquiv X (Sieve.generate 𝒰.toPresieveOver) =
      Sieve.ofArrows 𝒰.obj 𝒰.map := by
  ext V f
  rw [Sieve.overEquiv_iff]
  simp
  constructor
  · rintro ⟨U, h, g, ⟨k⟩, hcomp⟩
    use 𝒰.obj k, h.left, 𝒰.map k
    constructor
    · use k
    · apply_fun CommaMorphism.left at hcomp
      exact hcomp
  · rintro ⟨U, h, g, ⟨k⟩, hcomp⟩
    have : 𝒰.map k ≫ X.hom = 𝒰.obj k ↘ S := comp_over (𝒰.map k) S
    let h' : Over.mk (f ≫ X.hom) ⟶ OverClass.asOver (X := 𝒰.obj k) S :=
      Over.homMk h (by simp [← hcomp, this])
    use OverClass.asOver (X := 𝒰.obj k) S, h', OverClass.asOverHom S (𝒰.map k)
    constructor
    · use k
    · ext : 1
      simpa

lemma Cover.toPresieveOver_le_arrows_iff {X : Over S} (R : Sieve X) (𝒰 : Cover.{u} P X.left)
    [𝒰.Over S] :
     𝒰.toPresieveOver ≤ R.arrows ↔
      Presieve.ofArrows 𝒰.obj 𝒰.map ≤ (Sieve.overEquiv X R).arrows := by
  constructor
  · rintro h - - ⟨i⟩
    simp [Sieve.overEquiv]
    have : 𝒰.toPresieveOver (OverClass.asOverHom S (𝒰.map i)) := by use i
    have := h (OverClass.asOver (X := (𝒰.obj i)) S) this
    use OverClass.asOver (X := (𝒰.obj i)) S, OverClass.asOverHom S (𝒰.map i), 𝟙 _
    constructor
    · exact this
    · rfl
  · intro h Y g ⟨i⟩
    have : Presieve.ofArrows 𝒰.obj 𝒰.map (𝒰.map i) := by use i
    have := h _ this
    obtain ⟨Z, g, h, hg, hcomp⟩ := this
    have : 𝒰.obj i ↘ S = 𝒰.map i ≫ X.hom := (comp_over (𝒰.map i) S).symm
    simp at hcomp
    let h' : (𝒰.obj i).asOver S ⟶ Z :=
      Over.homMk h (by simp [this, hcomp])
    have : (𝒰.map i).asOver S = h' ≫ g := by
      ext : 1
      exact hcomp
    rw [this]
    apply R.downward_closed
    exact hg

def overPretopology : Pretopology (Over S) where
  coverings Y R := ∃ (𝒰 : Cover.{u} P Y.left) (_ : 𝒰.Over S), R = 𝒰.toPresieveOver
  has_isos {X Y} f _ := ⟨coverOfIsIso f.left, inferInstance, (Presieve.ofArrows_pUnit _).symm⟩
  pullbacks := by
    rintro Y X f _ ⟨𝒰, h, rfl⟩
    refine ⟨𝒰.pullbackCoverOver' S f.left, inferInstance, ?_⟩
    simpa [Cover.toPresieveOver] using
      (Presieve.ofArrows_pullback f (fun i ↦ (𝒰.obj i).asOver S) (fun i ↦ (𝒰.map i).asOver S)).symm
  transitive := by
    rintro X _ T ⟨𝒰, h, rfl⟩ H
    choose V h hV using H
    refine ⟨𝒰.bind (fun j => V ((𝒰.map j).asOver S) ⟨j⟩), inferInstance, ?_⟩
    convert Presieve.ofArrows_bind _ (fun j ↦ (𝒰.map j).asOver S) _
      (fun Y f H j ↦ ((V f H).obj j).asOver S) (fun Y f H j ↦ ((V f H).map j).asOver S)
    apply hV

variable (Q : MorphismProperty Scheme.{u}) [Q.IsMultiplicative] [Q.RespectsIso]
  [Q.IsStableUnderBaseChange] [IsJointlySurjectivePreserving Q]
  [Q.HasOfPostcompProperty]

/-- The pretopology defind on the subcategory of `S`-schemes satisfying `P` where coverings
are given by `Q`-coverings in `S`-schemes satisfying `P`.
The most common case is `P = Q`. In this case, this is simply surjective families
in `S`-schemes with `P`. -/
def smallPretopology : Pretopology (P.Over ⊤ S) where
  coverings Y R := ∃ (𝒰 : Cover.{u} Q Y.left) (_ : 𝒰.Over S) (h : ∀ j : 𝒰.J, P (𝒰.obj j ↘ S)),
    R = 𝒰.toPresieveOverWithProp h
  has_isos {X Y} f := ⟨coverOfIsIso f.left, inferInstance, fun _ ↦ Y.prop,
    (Presieve.ofArrows_pUnit _).symm⟩
  pullbacks := by
    rintro Y X f _ ⟨𝒰, h, p, rfl⟩
    refine ⟨𝒰.pullbackCoverOverProp' S f.left (Q := P) Y.prop X.prop p, inferInstance, ?_, ?_⟩
    · intro j
      apply MorphismProperty.Comma.prop
    · simp [Cover.toPresieveOverWithProp]
      symm
      convert Presieve.ofArrows_pullback f (fun i ↦ ⟨(𝒰.obj i).asOver S, p i⟩)
              (fun i ↦ ⟨(𝒰.map i).asOver S, trivial, trivial⟩)
  transitive := by
    rintro X _ T ⟨𝒰, h, p, rfl⟩ H
    choose V h pV hV using H
    let 𝒱j (j : 𝒰.J) : (Cover Q ((𝒰.obj j).asOverProp S (p j)).left) :=
      V ((𝒰.map j).asOverProp S) ⟨j⟩
    refine ⟨𝒰.bind (fun j ↦ 𝒱j j), inferInstance, fun j ↦ pV _ _ _, ?_⟩
    convert Presieve.ofArrows_bind _ (fun j ↦ ((𝒰.map j).asOverProp S)) _
      (fun Y f H j ↦ ((V f H).obj j).asOverProp S (pV _ _ _))
      (fun Y f H j ↦ ((V f H).map j).asOverProp S)
    apply hV

abbrev overTopology : GrothendieckTopology (Over S) :=
  (Scheme.grothendieckTopology P).over S

lemma overTopology_eq_toGrothendieck_overPretopology :
    overTopology P S = (overPretopology P S).toGrothendieck := by
  ext X R
  rw [GrothendieckTopology.mem_over_iff, Pretopology.mem_toGrothendieck]
  constructor
  · rintro ⟨T, ⟨𝒰, rfl⟩, hT⟩
    letI (i : 𝒰.J) : OverClass (𝒰.obj i) S := { hom := 𝒰.map i ≫ X.hom }
    letI : 𝒰.Over S := {
      over := inferInstance
      isOver_map := fun i ↦ ⟨rfl⟩
    }
    use 𝒰.toPresieveOver, ⟨𝒰, inferInstance, rfl⟩
    rwa [Cover.toPresieveOver_le_arrows_iff]
  · rintro ⟨T, ⟨𝒰, h, rfl⟩, hT⟩
    use Presieve.ofArrows 𝒰.obj 𝒰.map, ⟨𝒰, rfl⟩
    rwa [Cover.toPresieveOver_le_arrows_iff] at hT

lemma mem_overTopology (X : Over S) (R : Sieve X) :
    R ∈ S.overTopology P X ↔
      ∃ (𝒰 : Cover.{u} P X.left) (_ : 𝒰.Over S),
          𝒰.toPresieveOver ≤ R.arrows := by
  rw [overTopology_eq_toGrothendieck_overPretopology]
  constructor
  · rintro ⟨T, ⟨𝒰, h, rfl⟩, hle⟩
    use 𝒰, h
  · rintro ⟨𝒰, h𝒰, hle⟩
    exact ⟨𝒰.toPresieveOver, ⟨𝒰, h𝒰, rfl⟩, hle⟩

variable {Q : MorphismProperty Scheme.{u}} [Q.IsStableUnderComposition]

variable {P} in
lemma locallyCoverDense_of_le (hPQ : P ≤ Q) :
    (MorphismProperty.Over.forget Q ⊤ S).LocallyCoverDense (overTopology P S) where
  functorPushforward_functorPullback_mem X := by
    intro ⟨T, hT⟩
    rw [mem_overTopology] at hT ⊢
    obtain ⟨𝒰, h, hle⟩ := hT
    use 𝒰, h
    simp only [MorphismProperty.Comma.forget_obj, Sieve.functorPushforward_apply,
      Sieve.functorPullback_apply]
    rintro - - ⟨i⟩
    have : Q (𝒰.obj i ↘ S) := by
      rw [← comp_over (𝒰.map i) S]
      exact Q.comp_mem _ _ (hPQ _ <| 𝒰.map_prop i) X.prop
    let Ui : Q.Over ⊤ S := ⟨OverClass.asOver (X := 𝒰.obj i) S, this⟩
    use Ui, MorphismProperty.Over.homMk (𝒰.map i) (comp_over (𝒰.map i) S), 𝟙 _
    simp only [Presieve.functorPullback_mem, MorphismProperty.Comma.forget_obj,
      MorphismProperty.Comma.forget_map, MorphismProperty.Over.homMk_hom, Category.id_comp]
    exact ⟨hle _ (by use i), rfl⟩

instance : (MorphismProperty.Over.forget P ⊤ S).LocallyCoverDense (overTopology P S) :=
  locallyCoverDense_of_le S le_rfl

/-- If `P` and `Q` are morphism properties with `P ≤ Q`, this is the Grothendieck topology
induced via the forgetful functor `Q.Over ⊤ S ⥤ Over S` by the topology defined by `P`. -/
abbrev smallTopologyOfLE (hPQ : P ≤ Q) : GrothendieckTopology (Q.Over ⊤ S) :=
  letI : (MorphismProperty.Over.forget Q ⊤ S).LocallyCoverDense (overTopology P S) :=
    locallyCoverDense_of_le S hPQ
  (MorphismProperty.Over.forget Q ⊤ S).inducedTopology (S.overTopology P)

variable [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]
  [IsJointlySurjectivePreserving Q] [Q.HasOfPostcompProperty]

lemma _root_.CategoryTheory.Sieve.mem_functorPushforward_of_full {C D : Type*} [Category C]
    [Category D] (F : C ⥤ D) [F.Full] {X Y : C} (R : Sieve X) (f : F.obj Y ⟶ F.obj X) :
    (R.functorPushforward F).arrows f ↔ ∃ (g : Y ⟶ X), F.map g = f ∧ R g := by
  constructor
  · intro ⟨Z, g, h, hg, hcomp⟩
    obtain ⟨h', hh'⟩ := F.map_surjective h
    use h' ≫ g
    simp [hh', hcomp]
    apply R.downward_closed hg
  · intro ⟨g, hcomp, hg⟩
    use Y, g, 𝟙 _, hg
    simp [hcomp]

lemma _root_.CategoryTheory.Sieve.mem_functorPushforward_of_full_of_faithful {C D : Type*}
    [Category C] [Category D]
    (F : C ⥤ D) [F.Full] [F.Faithful] {X Y : C} (R : Sieve X) (f : Y ⟶ X) :
    (R.functorPushforward F).arrows (F.map f) ↔ R f := by
  rw [Sieve.mem_functorPushforward_of_full]
  constructor
  · intro ⟨g, hcomp, hg⟩
    rwa [← F.map_injective hcomp]
  · intro hf
    use f

lemma smallTopologyOfLE_eq_toGrothendieck_smallPretopology (hPQ : P ≤ Q) :
    smallTopologyOfLE P S hPQ = (smallPretopology Q S P).toGrothendieck := by
  ext X R
  rw [Pretopology.mem_toGrothendieck]
  simp
  rw [mem_overTopology]
  constructor
  · intro ⟨𝒰, h, le⟩
    have hj (j : 𝒰.J) : Q (𝒰.obj j ↘ S) := by
      rw [← comp_over (𝒰.map j)]
      exact Q.comp_mem _ _ (hPQ _ <| 𝒰.map_prop _) X.prop
    use 𝒰.toPresieveOverWithProp hj
    constructor
    · use 𝒰, h, hj
    · rintro - - ⟨i⟩
      let fi : (𝒰.obj i).asOverProp S (hj i) ⟶ X := ⟨(𝒰.map i).asOver S, trivial, trivial⟩
      have : 𝒰.toPresieveOver ((MorphismProperty.Over.forget Q ⊤ S).map fi) := by use i
      have : R.functorPushforward _ ((MorphismProperty.Over.forget Q ⊤ S).map fi) := le _ this
      rwa [Sieve.mem_functorPushforward_of_full_of_faithful] at this
  · rintro ⟨T, ⟨𝒰, h, p, rfl⟩, le⟩
    use 𝒰, h
    rintro - - ⟨i⟩
    use (𝒰.obj i).asOverProp S (p i), (𝒰.map i).asOverProp S, 𝟙 _
    simp only [MorphismProperty.Comma.forget_obj, MorphismProperty.Comma.forget_map,
      MorphismProperty.Comma.Hom.hom_mk, Category.id_comp, and_true]
    apply le
    use i

/-- A special case of `smallTopologyOfLE` for the most common case, where `P = Q`. -/
abbrev smallTopology : GrothendieckTopology (P.Over ⊤ S) :=
  (MorphismProperty.Over.forget P ⊤ S).inducedTopology (S.overTopology P)

lemma smallTopology_eq_toGrothendieck_smallPretopology :
    S.smallTopology P = (S.smallPretopology P P).toGrothendieck :=
  smallTopologyOfLE_eq_toGrothendieck_smallPretopology _ _ le_rfl 

lemma mem_toGrothendieck_smallPretopology (X : P.Over ⊤ S) (R : Sieve X) :
    R ∈ (S.smallPretopology P Q).toGrothendieck _ X ↔
      ∀ x : X.left, ∃ (Y : P.Over ⊤ S) (f : Y ⟶ X) (y : Y.left),
        R f ∧ Q f.left ∧ f.left.base y = x := by
  rw [Pretopology.mem_toGrothendieck]
  constructor
  · rintro ⟨T, ⟨𝒰, h, p, rfl⟩, hle⟩
    intro x
    obtain ⟨y, hy⟩ := 𝒰.covers x
    refine ⟨(𝒰.obj (𝒰.f x)).asOverProp S (p _), (𝒰.map (𝒰.f x)).asOverProp S, y, hle _ ?_,
      𝒰.map_prop _, hy⟩
    use 𝒰.f x
  · intro h
    choose Y f y hf hQ hy using h
    let 𝒰 : X.left.Cover Q :=
      { J := X.left,
        obj := fun i ↦ (Y i).left
        map := fun i ↦ (f i).left
        map_prop := hQ
        f := id
        covers := fun i ↦ ⟨y i, hy i⟩ }
    letI : 𝒰.Over S :=
      { over := fun i ↦ inferInstance
        isOver_map := fun i ↦ inferInstance }
    use 𝒰.toPresieveOverWithProp fun i ↦ MorphismProperty.Comma.prop _
    constructor
    · use 𝒰, inferInstance, fun i ↦ MorphismProperty.Comma.prop _
    · rintro - - ⟨i⟩
      exact hf i

lemma mem_smallTopology (X : P.Over ⊤ S) (R : Sieve X) :
    R ∈ S.smallTopology P X ↔
      ∃ (𝒰 : Cover.{u} P X.left) (_ : 𝒰.Over S) (h : ∀ j, P (𝒰.obj j ↘ S)),
          𝒰.toPresieveOverWithProp h ≤ R.arrows := by
  rw [smallTopology_eq_toGrothendieck_smallPretopology]
  constructor
  · rintro ⟨T, ⟨𝒰, h, p, rfl⟩, hle⟩
    use 𝒰, h, p
  · rintro ⟨𝒰, h𝒰, p, hle⟩
    exact ⟨𝒰.toPresieveOverWithProp p, ⟨𝒰, h𝒰, p, rfl⟩, hle⟩

end AlgebraicGeometry.Scheme
