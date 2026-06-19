/-
Copyright (c) 2026 Jakob Scharmberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scharmberg
-/
module

public import Mathlib.Algebra.Homology.ComplexShape
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Topology.Category.TopPair

/-!
# Eilenberg-Steenrod homology theories

In this file we introduce the Eilenberg-Steenrod axioms for homology theories.

The data for a homology theory is bundled in a structure `HomologyPretheory` consisting of functors
`Hₚ i : TopPair ⥤ C` and `H i : TopCat ⥤ C` which represent the `i`th relative and regular homology,
respectively, (indexed by a `ComplexShape`) and a proof that they agree on `TopCat`. They also
require boundary morphisms `δ i j :  Hₚ i ⟶ proj₂ ⋙ H j` for the long exact sequence of
topological pairs. These are nonzero only if `c.Rel i j`.

We introduce a type class for each axiom:

* `IsHomotopyInvariant`: Homotopic maps induce the same map in homology.
* `HasExcisionIso`: For a sufficiently nice subset `U ⊆ A`, the inclusion `(X \ U, A \ U) → (X, A)`
  induces an isomorphism in homology.
* `IsAdditive`: Homology preserves coproducts.
* `HasPairSequence`: For a topological pair `(X, A)`, the sequence
  `⋯ ⟶ Hₙ(X) ⟶ Hₙ(X, A) ⟶ Hₙ₋₁(A) ⟶ Hₙ₋₁(X) ⟶ Hₙ₋₁(X, A) ⟶ ⋯`
  is exact.
* `HasDimensionAxiom`: A `HomologyPretheory` on `ComplexShape.down ℕ : ComplexShape ℕ` has the
  dimension axiom, if homology is zero for positive indices.

 In addition, there are bundled type classes
`IsExtraordinaryEilenbergSteenrod` with the homotopy-invariance, excision, additivity, and pair
sequence axioms and `IsEilenbergSteenrod` which extends the former by the dimension axiom.

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
lemma isHomotopyInvariant_iff :
    isHomotopyInvariant C c HP ↔ IsHomotopyInvariant HP := .rfl

instance : IsClosedUnderIsomorphisms (isHomotopyInvariant.{u} C c) where
  of_iso e _ := ⟨fun F _ ↦ by
    simp only [← cancel_epi ((e.hom.homₚ _).app _), ← NatTrans.naturality,
      map_eq_of_homotopy _ F _]⟩

set_option linter.unusedVariables false in
/-- A `HomologyPretheory` has the excision-isomorphism, if cutting out a sufficiently nice subspace
`U` from a space `X` yields an isomorphism `Hₚ i X ≅ Hₚ i (X \ U)`. -/
@[mk_iff]
class HasExcisionIso where
  isIso_of_closure_interior_of_isCompl ⦃X U V : TopPair⦄ (f : U ⟶ X) (g : V ⟶ X)
      (hf : IsEmbedding f) (hg : IsEmbedding g) (hcompl : TopPair.IsCompl f g)
      (hU : closure (Set.range (Hom.fst f)) ⊆ interior (Set.range X.map)) (i : ι) :
      IsIso ((HP.Hₚ i).map g)

export HasExcisionIso (isIso_of_closure_interior_of_isCompl)

variable (C c) in
/-- An abbreviation for `HomologyPretheory.HasExcisionIso` as `ObjectProperty`. -/
abbrev hasExcisionIso : ObjectProperty (HomologyPretheory.{u} C c) :=
  HasExcisionIso

@[simp]
lemma hasExcisionIso_iff' : hasExcisionIso C c HP ↔ HP.HasExcisionIso := .rfl

instance : IsClosedUnderIsomorphisms (hasExcisionIso.{u} C c) where
  of_iso e hHP := { isIso_of_closure_interior_of_isCompl _ _ _ _ _ hf hg hcompl hU _ :=
    (NatIso.isIso_map_iff ((hₚFunctor _).mapIso e) _).mp (hHP.isIso_of_closure_interior_of_isCompl _
      _ hf hg hcompl hU _) }

/-- A `HomologyPretheory` is additive if its homology functor preserves coproducts. -/
class IsAdditive where
  /-- An extraordinary Eilenberg-Steenrod homology functor preserves colimits. -/
  [preserves_coproducts_u (J : Type u) (i : ι) :
      Limits.PreservesColimitsOfShape (Discrete J) (HP.H i)]

attribute [instance] IsAdditive.preserves_coproducts_u

export IsAdditive (preserves_coproducts_u)

variable (C c) in
/-- An abbreviation for `HomologyPretheory.IsAdditive` as `ObjectProperty`. -/
abbrev isAdditive : ObjectProperty (HomologyPretheory.{u} C c) :=
  IsAdditive

@[simp]
lemma isAdditive_iff : isAdditive C c HP ↔ HP.IsAdditive := .rfl

instance IsAdditive.preserves_coproducts_of_small
    [HP.IsAdditive] (J : Type*) [Small.{u} J] (i : ι) :
      Limits.PreservesColimitsOfShape (Discrete J) (HP.H i) :=
  Limits.preservesColimitsOfShape_of_equiv (Discrete.equivalence (equivShrink _).symm) _

instance : IsClosedUnderIsomorphisms (isAdditive.{u} C c) where
  of_iso {HP HP'} e _ := { preserves_coproducts_u _ _ :=
    Limits.preservesColimitsOfShape_of_natIso ((HP.iso _) ≪≫
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

export HasPairSequence (exact_pair exact_snd exact_fst)

variable (C c) in
/-- An abbreviation for `HomologyPretheory.HasPairSequence` as `ObjectProperty`. -/
abbrev hasPairSequence : ObjectProperty (HomologyPretheory.{u} C c) :=
  HasPairSequence

@[simp]
lemma hasPairSequence_iff : hasPairSequence C c HP ↔ HP.HasPairSequence := .rfl

variable {HP HP'} in
abbrev hₚIsoOfIso (e : HP ≅ HP') (i : ι) : HP.Hₚ i ≅ HP'.Hₚ i := ((hₚFunctor i).mapIso e)

variable {HP HP'} in
abbrev hIsoOfIso (e : HP ≅ HP') (i : ι) : HP.H i ≅ HP'.H i :=
  (HP.iso i) ≪≫ incl.isoWhiskerLeft ((hₚFunctor i).mapIso e) ≪≫ (HP'.iso i).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance : IsClosedUnderIsomorphisms (hasPairSequence.{u} C c) where
  of_iso {HP HP'} e hPS := {
    exact_pair X i j hij := by
      let pairSeq := ComposableArrows.mk₂ ((HP.Hₚ i).map X.j) ((HP.δ i j).app X)
      let pairSeq' := ComposableArrows.mk₂ ((HP'.Hₚ i).map X.j) ((HP'.δ i j).app X)
      have pairSeqIso : pairSeq ≅ pairSeq' :=
        ComposableArrows.isoMk₂
          ((hₚIsoOfIso e _).app _)
          ((hₚIsoOfIso e _).app _)
          ((proj₂.isoWhiskerLeft (hIsoOfIso e _)).app _)
          (by cat_disch)
          (by simp [pairSeq, pairSeq', ComposableArrows.Precomp.map, -Functor.isoWhiskerLeft_trans,
            Hom.w_app])
      exact ComposableArrows.exact_of_iso pairSeqIso (hPS.exact_pair _ _ _ hij)
    exact_snd X i j hij := by
      let pairSeq := ComposableArrows.mk₂ ((HP.δ i j).app X) ((HP.H j).map X.map)
      let pairSeq' := ComposableArrows.mk₂ ((HP'.δ i j).app X) ((HP'.H j).map X.map)
      have pairSeqIso : pairSeq ≅ pairSeq' :=
        ComposableArrows.isoMk₂
          ((hₚIsoOfIso e _).app _)
          ((proj₂.isoWhiskerLeft (hIsoOfIso e _)).app _)
          ((hIsoOfIso e _).app _)
          (by simp [pairSeq, pairSeq', -Functor.isoWhiskerLeft_trans, Hom.w_app])
          (by simp [pairSeq, pairSeq', ComposableArrows.Precomp.map])
      exact ComposableArrows.exact_of_iso pairSeqIso (hPS.exact_snd _ _ _ hij)
    exact_fst X i := by
      let pairSeq := ComposableArrows.mk₂ ((HP.H i).map X.map)
        ((HP.iso i).hom.app X.fst ≫ (HP.Hₚ i).map X.j)
      let pairSeq' := ComposableArrows.mk₂ ((HP'.H i).map X.map)
        ((HP'.iso i).hom.app X.fst ≫ (HP'.Hₚ i).map X.j)
      have pairSeqIso : pairSeq ≅ pairSeq' :=
        ComposableArrows.isoMk₂
          ((proj₂.isoWhiskerLeft (hIsoOfIso e _)).app _)
          ((hIsoOfIso e _).app _)
          ((hₚIsoOfIso e _).app _)
          (by simp [pairSeq, pairSeq'])
          (by simp [pairSeq, pairSeq', ComposableArrows.Precomp.map, Hom.iso_comm_app_assoc])
      exact ComposableArrows.exact_of_iso pairSeqIso (hPS.exact_fst _ _)
  }

/-- An extraordinary Eilenberg-Steenrod homology theory requires the homotopy, excision, additivity,
and exactness axioms. -/
class IsExtraordinaryEilenbergSteenrod where
  /-- Invariance of an extraordinary Eilenberg-Steenrod homology theory on homotopic maps. -/
  [isHomotopyInvariant : HP.IsHomotopyInvariant]
  /-- Excision axiom of an extraordinary Eilenberg-Steenrod homology theory. -/
  [hasExcisionIso : HP.HasExcisionIso]
  /-- An extraordinary Eilenberg-Steenrod homology functor preserves coproducts. -/
  [isAdditive : HP.IsAdditive]
  /-- The long exact sequence of topological pairs in an extraordinary Eilenberg-Steenrod homology
  theory. -/
  [hasPairSequence : HP.HasPairSequence]

attribute [instance] IsExtraordinaryEilenbergSteenrod.isHomotopyInvariant
  IsExtraordinaryEilenbergSteenrod.hasExcisionIso
  IsExtraordinaryEilenbergSteenrod.isAdditive
  IsExtraordinaryEilenbergSteenrod.hasPairSequence

variable (C c) in
/-- An abbreviation for `HomologyPretheory.IsExtraordinaryEilenbergSteenrod` as `ObjectProperty`. -/
abbrev isExtraordinaryEilenbergSteenrod : ObjectProperty (HomologyPretheory.{u} C c) :=
  IsExtraordinaryEilenbergSteenrod

@[simp]
lemma isExtraordinaryEilenbergSteenrod_iff :
    isExtraordinaryEilenbergSteenrod C c HP ↔ HP.IsExtraordinaryEilenbergSteenrod := .rfl

instance : IsClosedUnderIsomorphisms (isExtraordinaryEilenbergSteenrod C c)
    where
  of_iso e h := {
    isHomotopyInvariant :=
      instIsClosedUnderIsomorphismsIsHomotopyInvariant.of_iso e h.isHomotopyInvariant
    hasExcisionIso := instIsClosedUnderIsomorphismsHasExcisionIso.of_iso e h.hasExcisionIso
    isAdditive := instIsClosedUnderIsomorphismsIsAdditive.of_iso e h.isAdditive
    hasPairSequence := instIsClosedUnderIsomorphismsHasPairSequence.of_iso e h.hasPairSequence
  }

variable (HP HP' : HomologyPretheory.{u} C (ComplexShape.down ℕ))

/-- A `HomologyPretheory` on `ComplexShape.down ℕ` has the dimension axiom if it is trivial on the
terminal space for `n > 0`. -/
class HasDimensionAxiom where
  isZero_PUnit_of_gt_zero : ∀ (n : ℕ) (_ : n ≠ 0), Limits.IsZero ((HP.H n).obj (TopCat.of PUnit)) :=
    by cat_disch

export HasDimensionAxiom (isZero_PUnit_of_gt_zero)

variable (C) in
/-- An abbreviation for `HomologyPretheory.HasDimensionAxiom` as `ObjectProperty`. -/
abbrev hasDimensionAxiom : ObjectProperty (HomologyPretheory.{u} C (ComplexShape.down ℕ)) :=
  HasDimensionAxiom

@[simp]
lemma hasDimensionAxiom_iff :
    hasDimensionAxiom C HP ↔ HP.HasDimensionAxiom := .rfl

instance : IsClosedUnderIsomorphisms (hasDimensionAxiom.{u} C) where
  of_iso {HP HP'} e h := ⟨fun n hn ↦ (Iso.isZero_iff (((HP.iso _) ≪≫ Functor.isoWhiskerLeft incl
    ((hₚFunctor _).mapIso e) ≪≫ (HP'.iso _).symm).app
    (TopCat.of PUnit))).mp (h.isZero_PUnit_of_gt_zero n hn)⟩

/-- An Eilenberg-Steenrod homology theory is an extraordinary Eilenberg-Steenrod homology theory
which additionally satisfies the dimension axiom. -/
class IsEilenbergSteenrod extends HP.IsExtraordinaryEilenbergSteenrod.{u} where
  /-- An Eilenberg-Steenrod homology theory is trivial on the terminal space for `n > 0`. -/
  [hasDimensionAxiom : HP.HasDimensionAxiom]

attribute [instance] IsEilenbergSteenrod.hasDimensionAxiom

variable (C) in
/-- An abbreviation for `HomologyPretheory.HasPairSequence` as `ObjectProperty`. -/
abbrev isEilenbergSteenrod : ObjectProperty (HomologyPretheory.{u} C (ComplexShape.down ℕ)) :=
  IsEilenbergSteenrod

@[simp]
lemma isEilenbergSteenrod_iff :
    isEilenbergSteenrod C HP ↔ HP.IsEilenbergSteenrod := .rfl

instance : IsClosedUnderIsomorphisms (isEilenbergSteenrod.{u} C) where
  of_iso e h := {
    1 := instIsClosedUnderIsomorphismsIsExtraordinaryEilenbergSteenrod.of_iso e h.1
    hasDimensionAxiom :=
      instIsClosedUnderIsomorphismsNatDownHasDimensionAxiom.of_iso e h.hasDimensionAxiom
  }

end HomologyPretheory

end TopPair
