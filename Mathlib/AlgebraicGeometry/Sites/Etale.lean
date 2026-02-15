/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.CategoryTheory.Limits.Elements
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!

# The étale site

In this file we define the big étale site, i.e. the étale topology as a Grothendieck topology
on the category of schemes.

-/

@[expose] public section

universe v u

open CategoryTheory MorphismProperty Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Big étale site: the étale precoverage on the category of schemes. -/
def etalePrecoverage : Precoverage Scheme.{u} :=
  precoverage @Etale

/-- Big étale site: the étale pretopology on the category of schemes. -/
def etalePretopology : Pretopology Scheme.{u} :=
  pretopology @Etale

/-- Big étale site: the étale topology on the category of schemes. -/
abbrev etaleTopology : GrothendieckTopology Scheme.{u} :=
  grothendieckTopology @Etale

lemma zariskiTopology_le_etaleTopology : zariskiTopology ≤ etaleTopology := by
  apply grothendieckTopology_monotone
  intro X Y f hf
  infer_instance

/-- The small étale site of a scheme is the Grothendieck topology on the
category of schemes étale over `X` induced from the étale topology on `Scheme.{u}`. -/
def smallEtaleTopology (X : Scheme.{u}) : GrothendieckTopology X.Etale :=
  X.smallGrothendieckTopology (P := @Etale)

/-- The pretopology generating the small étale site. -/
def smallEtalePretopology (X : Scheme.{u}) : Pretopology X.Etale :=
  X.smallPretopology (Q := @Etale) (P := @Etale)

lemma ofArrows_mem_smallEtaleTopology_iff
    {X : Scheme.{u}} {W : X.Etale} {ι : Type*}
    {Z : ι → X.Etale} (f : ∀ i, Z i ⟶ W) :
    Sieve.ofArrows _ f ∈ smallEtaleTopology _ _ ↔
      ⋃ i, Set.range (f i).left = .univ := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ (mem_smallGrothendieckTopology _ _).2 ?_⟩
  · obtain ⟨U, _, _, hU⟩ := (mem_smallGrothendieckTopology _ _).1 hf
    ext y
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, ⟨u, rfl⟩⟩ := ((ofArrows_mem_precoverage_iff _).1 U.mem₀).1 y
    obtain ⟨_, b, _, ⟨j⟩, fac⟩ := hU _ ⟨i⟩
    replace fac : b.left ≫ (f j).left = U.f i :=
      (Etale.forget _ ⋙ CategoryTheory.Over.forget _).congr_map fac
    exact ⟨j, b.left u, by simp [← fac]⟩
  · have (w : W.left) : ∃ (i : ι), w ∈ Set.range (f i).left := by
      have := Set.mem_univ w
      simp [← hf] at this
      tauto
    choose i z hz using this
    let V : Cover (precoverage @Etale) W.left :=
      Cover.mkOfCovers W.left (fun w ↦ (Z (i w)).left)
        (fun w ↦ (f (i w)).left) (fun w ↦ ⟨_, _, hz w⟩) inferInstance
    letI : Cover.Over X V :=
      { over w := ⟨(Z (i w)).hom⟩
        isOver_map w := by cat_disch }
    have (w : W.left) : Etale (V.X w ↘ X) :=
      inferInstanceAs (Etale (Z (i w)).hom)
    refine ⟨V, inferInstance, inferInstance, ?_⟩
    rintro _ _ ⟨w⟩
    refine ⟨_, 𝟙 _, _, ⟨i w⟩, by cat_disch⟩

instance {S : Scheme.{u}} (𝒰 : S.Cover (precoverage @Etale)) (i : 𝒰.I₀) : Etale (𝒰.f i) :=
  𝒰.map_prop i

end AlgebraicGeometry.Scheme
