/-
Copyright (c) 2026 Jakob Scharmberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scharmberg
-/

module

public import Mathlib.Algebra.Homology.ComplexShape
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.BourbakiWitt
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Category.TopPair

/-!
# Eilenberg-Steenrod homology theories

In this file we introduce the Eilenberg-Steenrod axioms for homology theories.

The data for a homology theory is bundled in a structure `HomologyPretheory` consisting of functors
`Hₚ i : TopPair ⥤ C` and `H i : TopCat ⥤ C` which represent the `i`th relative and regular homology,
respectively, (indexed by a `ComplexShape`) and a proof that they agree on `TopCat`. They also
require boundary morphisms `δ i j :  Hₚ i ⟶ proj₂ ⋙ H j` for the long exact sequence of
topological pairs. These are nonzero only if `c.Rel i j`.

We introduce a type class for each axiom. In addition, there are bundled type classes
`IsExtraordinaryEilenbergSteenrod` with the homotopy, excision, additivity, and exactness axioms and
`IsEilenbergSteenrod` on a `HomologyPretheory` on `ComplexShape.down ℕ : ComplexShape ℕ` which
extends the former by the dimension axiom.

Excision is formulated in terms of complements of topological pairs: Suppose `U` and `V` are
complements of a topological pair `X` with embeddings `f : U ⟶ X` and `g : V ⟶ X`. Suppose further
that the closure of `Hom.fst f (U.fst)` is a subset of the interior of the image of `X.snd` in
`X.fst`. Then the excision axiom postulates that the homology of `X` is isomorphic to that of `V`.
Note that this closure condition a priori seems weaker than in the literature. However, we prove
that under these assumptions, `U` is actually an isomorphism.
-/

@[expose] public section

open CategoryTheory TopPair ObjectProperty

universe u

namespace TopPair

/-- A `HomologyPretheory` is the data of an Eilenberg-Steenrod homology theory. -/
@[ext]
structure HomologyPretheory
    (C : Type*) [Category* C] [Limits.HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι) where
  /-- The relative homology functor of a `HomologyPretheory`. -/
  Hₚ (i : ι) : TopPair.{u} ⥤ C
  /-- The regular homology functor of a `HomologyPretheory`. -/
  H (i : ι) : TopCat.{u} ⥤ C
  /-- `Hₚ` and `H` agree on `TopCat`. -/
  iso (i : ι) : H i ≅ incl ⋙ Hₚ i
  /-- The boundary natural transformation of a `HomologyPretheory`. -/
  δ (i j : ι) : Hₚ i ⟶ proj₂ ⋙ H j
  /-- The boundary map is only nonzero if `c.Rel i j`. -/
  shape_δ (i j : ι) (h : ¬ c.Rel i j) : δ i j = 0 := by cat_disch

namespace HomologyPretheory

variable {C : Type*} [Category* C] [Limits.HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}

/-- A morphism in the category `HomologyPretheory`. -/
@[ext]
structure Hom (HP HP' : HomologyPretheory.{u} C c) where
  /-- The natural transformation of relative homology functors in a morphism of
  `HomologyPretheory`s. -/
  homₚ (i : ι) : HP.Hₚ i ⟶ HP'.Hₚ i
  /-- The natural transformation of homology functors in a morphism of
  `HomologyPretheory`s. -/
  hom (i : ι) : HP.H i ⟶ HP'.H i := (HP.iso i).hom ≫ incl.whiskerLeft (homₚ i) ≫ (HP'.iso i).inv
  /-- `homₚ` and `hom` need to be compatible with `HomologyPretheory.iso`. -/
  iso_comm (i : ι) :
    (HP.iso i).hom ≫ incl.whiskerLeft (homₚ i) = hom i ≫ (HP'.iso i).hom := by cat_disch
  /-- `homₚ` needs to be compatible with the boundary maps. -/
  w (i j : ι) : HP.δ i j ≫ proj₂.whiskerLeft (hom j) = homₚ i ≫ HP'.δ i j := by cat_disch

attribute [reassoc (attr := simp)] Hom.iso_comm
attribute [reassoc (attr := local simp)] Hom.w

@[simps]
instance : Category (HomologyPretheory.{u} C c) where
  Hom := HomologyPretheory.Hom
  id _ := { homₚ _ := 𝟙 _ }
  comp f g := { homₚ _ := f.homₚ _ ≫ g.homₚ _ }

variable {HP HP' : HomologyPretheory.{u} C c}

-- TODO: generate this with `@[to_app]`
@[reassoc]
lemma Hom.iso_comm_app (f : HP ⟶ HP') (i : ι) (X : TopCat.{u}) :
    (HP.iso i).hom.app X ≫ (f.homₚ i).app (ofTopCat X) = (f.hom i).app X ≫ (HP'.iso i).hom.app X :=
  congr($(f.iso_comm _).app _)

-- TODO: generate this with `@[to_app]`
@[reassoc]
lemma Hom.w_app (f : HP ⟶ HP') (i j : ι) (X : TopPair.{u}) :
    (HP.δ i j).app X ≫ (f.hom j).app X.left = (f.homₚ i).app X ≫ (HP'.δ i j).app X :=
  congr($(f.w _ _).app _)

@[reassoc]
lemma iso_homₚ_inv_hom (f : HP ⟶ HP') (i : ι) :
    (HP.iso i).hom ≫ incl.whiskerLeft (f.homₚ i) ≫ (HP'.iso i).inv = f.hom i := by simp

-- TODO: generate this with `@[to_app]`
@[reassoc (attr := simp)]
lemma iso_homₚ_inv_hom_app (f : HP ⟶ HP') (i : ι) (X : TopCat.{u}) :
    (HP.iso i).hom.app X ≫ (f.homₚ i).app (ofTopCat X) ≫ (HP'.iso i).inv.app X = (f.hom i).app X :=
  congr($(iso_homₚ_inv_hom _ _).app _)

@[reassoc (attr := simp)]
lemma inv_hom_iso_homₚ (f : HP ⟶ HP') (i : ι) :
    (HP.iso i).inv ≫ f.hom i ≫ (HP'.iso i).hom = incl.whiskerLeft (f.homₚ i) :=
  ((Iso.inv_comp_eq (HP.iso i)).mpr (f.iso_comm i).symm)

-- TODO: generate this with `@[to_app]`
@[reassoc (attr := simp)]
lemma inv_hom_iso_homₚ_app (f : HP ⟶ HP') (i : ι) (X : TopCat.{u}) :
    (HP.iso i).inv.app X ≫ (f.hom i).app X ≫ (HP'.iso i).hom.app X = (f.homₚ i).app (ofTopCat X) :=
  congr($(inv_hom_iso_homₚ _ _).app _)

/-- The forgetful functor that sends a `HomologyPretheory` to it's relative homology functor `Hₚ`.
-/
@[simps]
def hₚFunctor (i : ι) : HomologyPretheory.{u} C c ⥤ TopPair.{u} ⥤ C where
  obj HP := HP.Hₚ i
  map f := f.homₚ i

instance (f : HP ⟶ HP') [IsIso f] (i : ι) : IsIso (f.homₚ i) :=
  inferInstanceAs (IsIso ((HomologyPretheory.hₚFunctor i).map f))

/-- The forgetful functor that sends a `HomologyPretheory` to it's homology functor `H`. -/
@[simps]
def hFunctor (i : ι) : HomologyPretheory.{u} C c ⥤ TopCat.{u} ⥤ C where
  obj HP := HP.H i
  map f := f.hom i

instance (f : HP ⟶ HP') [IsIso f] (i : ι) : IsIso (f.hom i) :=
  inferInstanceAs (IsIso ((HomologyPretheory.hFunctor i).map f))

variable (HP HP' : HomologyPretheory.{u} C c)

/-- A `HomologyPretheory` is homotopy-invariant if its homology functor `Hₚ` takes homotopic maps to
the same map in homology -/
class IsHomotopyInvariant (HP : HomologyPretheory.{u} C c) where
  map_eq_of_homotopy (HP) {X Y : TopPair.{u}} {f g : X ⟶ Y} (F : Homotopy f g) (i : ι) :
    (HP.Hₚ i).map f = (HP.Hₚ i).map g := by cat_disch

export IsHomotopyInvariant (map_eq_of_homotopy)

variable (C c) in
/-- An abbreviation for `HomologyPretheory.IsHomotopyInvariant` as `ObjectProperty`. -/
abbrev isHomotopyInvariant : ObjectProperty (HomologyPretheory.{u} C c) :=
  IsHomotopyInvariant

@[simp]
lemma isHomotopyInvariant_iff : isHomotopyInvariant C c HP ↔ IsHomotopyInvariant HP := .rfl

instance : IsClosedUnderIsomorphisms (isHomotopyInvariant.{u} C c) where
  of_iso e _ := ⟨fun F _ ↦ by
    simp only [← cancel_epi ((e.hom.homₚ _).app _), ← NatTrans.naturality,
      map_eq_of_homotopy _ F _]⟩

set_option linter.unusedVariables false in
/-- A `HomologyPretheory` has the excision-isomorphism, if cutting out a sufficiently nice subspace
`U` from a space `X` yields an isomorphism `Hₚ i X ≅ Hₚ i (X \ U)`. -/
class HasExcisionIso where
  [excision ⦃X U V : TopPair⦄ (f : U ⟶ X) (g : V ⟶ X) (hf : IsEmbedding f) (hg : IsEmbedding g)
      (hcompl : TopPair.IsCompl f g)
      (hU : closure (Set.range (Hom.fst f)) ⊆ interior (Set.range X.map)) (i : ι) :
      IsIso ((HP.Hₚ i).map g)]

instance : IsClosedUnderIsomorphisms (C := HomologyPretheory C c) HasExcisionIso where
  of_iso e hHP := { excision _ _ _ _ _ hf hg hcompl hU _ := (NatIso.isIso_map_iff
    ((hₚFunctor _).mapIso e) _).mp (hHP.excision _ _ hf hg hcompl hU _) }

set_option backward.isDefEq.respectTransparency false in
/-- Under the assumptions of excision, the map of the pair `U` is an isomorphism. -/
lemma isIso_of_isCompl_closure ⦃X U V : TopPair⦄ (f : U ⟶ X) (g : V ⟶ X) (hf : IsEmbedding f)
    (hcompl : TopPair.IsCompl f g)
    (hU : closure (Set.range (Hom.fst f)) ⊆ interior (Set.range X.map)) : IsIso U.map := by
  have surjective_U : Function.Surjective U.map := by
    rw [← Set.range_eq_univ, Set.Subset.antisymm_iff]
    use (by simp)
    rw [← Set.image_subset_image_iff hf.fst.injective]
    have h₀ : Set.range (Hom.fst f) ⊆ Hom.fst f '' Set.range U.map ∪ Hom.fst g '' Set.range V.map :=
      by
      simp only [← Set.range_comp, ← CategoryTheory.hom_comp]
      simp only [← Arrow.w, CategoryTheory.hom_comp, Set.range_comp, ← Set.image_union,
        ← Set.sup_eq_union, codisjoint_iff.mp hcompl.snd.codisjoint, Set.top_eq_univ,
        Set.image_univ]
      calc
        Set.range (Hom.fst f) ⊆ closure (Set.range (Hom.fst f)) := subset_closure
        _ ⊆ interior (Set.range X.map) := hU
        _ ⊆ Set.range X.map := interior_subset
    have h₁ : Disjoint (Set.range (Hom.fst f)) (Hom.fst g '' Set.range V.map) := by
      rw [Set.disjoint_iff, ← Set.disjoint_iff_inter_eq_empty.mp hcompl.fst.disjoint]
      grind
    simp [Disjoint.subset_left_of_subset_union h₀ h₁]
  apply TopCat.isIso_of_bijective_of_isOpenMap _
    ⟨U.prop.injective, surjective_U⟩
  apply Topology.IsInducing.isOpenMap U.prop.isInducing
  simp [Function.Surjective.range_eq surjective_U]

/-- A `HomologyPretheory` is additive if its homology functor preserves coproducts. -/
class IsAdditive where
  /-- An extraordinary Eilenberg-Steenrod homology functor preserves colimits. -/
  [additive (J : Type u) (i : ι) : Limits.PreservesColimitsOfShape (Discrete J) (HP.H i)]

attribute [instance] IsAdditive.additive

instance IsAdditive.additive_of_small [IsAdditive HP] (J : Type*) [Small.{u} J] (i : ι) :
    Limits.PreservesColimitsOfShape (Discrete J) (HP.H i) :=
  Limits.preservesColimitsOfShape_of_equiv (Discrete.equivalence (equivShrink _).symm) _

instance : IsClosedUnderIsomorphisms (C := HomologyPretheory C c) IsAdditive where
  of_iso {HP HP'} e _ := { additive _ _ := Limits.preservesColimitsOfShape_of_natIso ((HP.iso _) ≪≫
    Functor.isoWhiskerLeft incl ((hₚFunctor _).mapIso e) ≪≫ (HP'.iso _).symm) }

/-- This imposes that a `HomologyPretheory` has the long exact sequence of topological pairs
`⋯ ⟶ H (c.next i) X.fst ⟶ Hₚ (c.next i) X) ⟶ H i X.snd ⟶ H i X.fst ⟶ ⋯`. -/
class HasPairSequence where
  /-- Exactness of the sequence `H i X.fst ⟶ Hₚ i X ⟶ H j X.snd.` -/
  exact_pair (X : TopPair) (i j : ι) (hij : c.Rel i j) :
      (ComposableArrows.mk₂ ((HP.Hₚ i).map X.j) ((HP.δ i j).app _)).Exact := by cat_disch
  /-- Exactness of the sequence `Hₚ i X ⟶ H j X.snd ⟶ H j X.fst`. -/
  exact_snd (X : TopPair) (i j : ι) (hij : c.Rel i j) :
      (ComposableArrows.mk₂ ((HP.δ i j).app _) ((HP.H j).map X.map)).Exact := by cat_disch
  /-- Exactness of the sequence `H i X.snd ⟶ H i X.fst ⟶ Hₚ i X`. -/
  exact_fst (X : TopPair) (i : ι) :
      (ComposableArrows.mk₂ ((HP.H i).map X.map) ((HP.iso i).hom.app _
      ≫ (HP.Hₚ i).map X.j)).Exact := by cat_disch

set_option backward.isDefEq.respectTransparency false in
instance : IsClosedUnderIsomorphisms (C := HomologyPretheory C c) HasPairSequence where
  of_iso {HP HP'} e hPS := {
    exact_pair X i j hij := by
      let pairSeq := ComposableArrows.mk₂ ((HP.Hₚ i).map X.j) ((HP.δ i j).app X)
      let pairSeq' := ComposableArrows.mk₂ ((HP'.Hₚ i).map X.j) ((HP'.δ i j).app X)
      have pairSeqIso : pairSeq ≅ pairSeq' :=
        ComposableArrows.isoMk₂
          (((hₚFunctor _).mapIso e).app _)
          (((hₚFunctor _).mapIso e).app _)
          ((proj₂.isoWhiskerLeft ((HP.iso _) ≪≫
            incl.isoWhiskerLeft ((hₚFunctor _).mapIso e) ≪≫
            (HP'.iso _).symm)).app _)
          (by cat_disch)
          (by
            simp [pairSeq, pairSeq', ComposableArrows.Precomp.map, -Functor.isoWhiskerLeft_trans, Hom.w_app])
      exact ComposableArrows.exact_of_iso pairSeqIso (hPS.exact_pair _ _ _ hij)
    exact_snd X i j hij := by
      let pairSeq := ComposableArrows.mk₂ ((HP.δ i j).app X) ((HP.H j).map X.map)
      let pairSeq' := ComposableArrows.mk₂ ((HP'.δ i j).app X) ((HP'.H j).map X.map)
      have pairSeqIso : pairSeq ≅ pairSeq' :=
        ComposableArrows.isoMk₂
          (((hₚFunctor _).mapIso e).app _)
          ((proj₂.isoWhiskerLeft ((HP.iso _) ≪≫
            incl.isoWhiskerLeft ((hₚFunctor _).mapIso e) ≪≫
            (HP'.iso _).symm)).app _)
          (((HP.iso _) ≪≫ incl.isoWhiskerLeft ((hₚFunctor _).mapIso e) ≪≫
            (HP'.iso _).symm).app _)
          (by
            simp [pairSeq, pairSeq', -Functor.isoWhiskerLeft_trans, Hom.w_app])
          (by
            simp only [NatIso.trans_app, Iso.trans_hom, Iso.app_hom, Functor.isoWhiskerLeft_hom]
            erw [iso_homₚ_inv_hom_app]
            simp [pairSeq, pairSeq', ComposableArrows.Precomp.map])
      exact ComposableArrows.exact_of_iso pairSeqIso (hPS.exact_snd _ _ _ hij)
    exact_fst X i := by
      let pairSeq := ComposableArrows.mk₂ ((HP.H i).map X.map)
        ((HP.iso i).hom.app X.fst ≫ (HP.Hₚ i).map X.j)
      let pairSeq' := ComposableArrows.mk₂ ((HP'.H i).map X.map)
        ((HP'.iso i).hom.app X.fst ≫ (HP'.Hₚ i).map X.j)
      have pairSeqIso : pairSeq ≅ pairSeq' :=
        ComposableArrows.isoMk₂
          ((proj₂.isoWhiskerLeft ((HP.iso _) ≪≫
            incl.isoWhiskerLeft ((hₚFunctor _).mapIso e) ≪≫
            (HP'.iso _).symm)).app _)
          (((HP.iso _) ≪≫ incl.isoWhiskerLeft ((hₚFunctor _).mapIso e) ≪≫
            (HP'.iso _).symm).app _)
          (((hₚFunctor _).mapIso e).app _)
          (by
            simp only [NatIso.trans_app, Iso.trans_hom, Iso.app_hom, Functor.isoWhiskerLeft_hom]
            erw [iso_homₚ_inv_hom_app]
            simp [pairSeq, pairSeq'])
          (by
            simp [pairSeq, pairSeq', ComposableArrows.Precomp.map, hₚFunctor])
      exact ComposableArrows.exact_of_iso pairSeqIso (hPS.exact_fst _ _)
  }

/-- An extraordinary Eilenberg-Steenrod homology theory requires the homotopy, excision, additivity,
and exactness axioms. -/
class IsExtraordinaryEilenbergSteenrod where
  /-- Invariance of an extraordinary Eilenberg-Steenrod homology theory on homotopic maps. -/
  [homotopy : IsHomotopyInvariant HP]
  /-- Excision axiom of an extraordinary Eilenberg-Steenrod homology theory. -/
  [excision : HasExcisionIso HP]
  /-- An extraordinary Eilenberg-Steenrod homology functor preserves coproducts. -/
  [additive : IsAdditive HP]
  /-- The long exact sequence of topological pairs in an extraordinary Eilenberg-Steenrod homology
  theory. -/
  [exact : HasPairSequence HP]

instance : IsClosedUnderIsomorphisms (C := HomologyPretheory C c) IsExtraordinaryEilenbergSteenrod
    where
  of_iso e h := {
    homotopy :=
      instIsClosedUnderIsomorphismsIsHomotopyInvariant.of_iso e h.homotopy
    excision := instIsClosedUnderIsomorphismsHasExcisionIso.of_iso e h.excision
    additive := instIsClosedUnderIsomorphismsIsAdditive.of_iso e h.additive
    exact := instIsClosedUnderIsomorphismsHasPairSequence.of_iso e h.exact
  }

variable (HP HP' : HomologyPretheory.{u} C (ComplexShape.down ℕ))

/-- A `HomologyPretheory` on `ComplexShape.down ℕ` has the dimension axiom if it is trivial on the
terminal space for `n > 0`. -/
class HasDimensionAxiom where
  dimension : ∀ (n : ℕ) (_ : n ≠ 0), Limits.IsZero ((HP.H n).obj (TopCat.of PUnit)) := by cat_disch

instance : IsClosedUnderIsomorphisms (C := HomologyPretheory C (ComplexShape.down ℕ))
    HasDimensionAxiom where
  of_iso {HP HP'} e h := ⟨fun n hn ↦ (Iso.isZero_iff (((HP.iso _) ≪≫ Functor.isoWhiskerLeft incl
    ((hₚFunctor _).mapIso e) ≪≫ (HP'.iso _).symm).app
    (TopCat.of PUnit))).mp (h.dimension n hn)⟩

/-- An Eilenberg-Steenrod homology theory is an extraordinary Eilenberg-Steenrod homology theory
which additionally satisfies the dimension axiom. -/
class IsEilenbergSteenrod extends IsExtraordinaryEilenbergSteenrod.{u} HP where
  /-- An Eilenberg-Steenrod homology theory is trivial on the terminal space for `n > 0`. -/
  [dimension : HasDimensionAxiom HP]

instance : IsClosedUnderIsomorphisms (C := HomologyPretheory C (ComplexShape.down ℕ))
    IsEilenbergSteenrod where
  of_iso e h := {
    1 := instIsClosedUnderIsomorphismsIsExtraordinaryEilenbergSteenrod.of_iso e h.1
    dimension :=
      instIsClosedUnderIsomorphismsNatDownHasDimensionAxiom.of_iso e h.dimension
  }

end HomologyPretheory

end TopPair
