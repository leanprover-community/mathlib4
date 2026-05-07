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

universe u v

namespace TopPair

/-- A `HomologyPretheory` is the data of an Eilenberg-Steenrod homology theory. -/
@[ext]
structure HomologyPretheory
    (C : Type v) [Category C] [Limits.HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι) where
  /-- The relative homology functor of a `HomologyPretheory`. -/
  Hₚ (i : ι) : TopPair.{u} ⥤ C
  /-- The regular homology functor of a `HomologyPretheory`. -/
  H (i : ι) : TopCat.{u} ⥤ C
  /-- The proof that `Hₚ` and `H` agree on `TopCat` -/
  iso (i : ι) : H i ≅ incl ⋙ Hₚ i
  /-- The boundary natural transformation of a `HomologyPretheory`. -/
  δ (i j : ι) : (Hₚ i) ⟶ proj₂ ⋙ H j
  /-- The boundary map is only nonzero if `c.Rel i j`. -/
  shape_δ (i j : ι) (h : ¬ c.Rel i j) : δ i j = 0 := by cat_disch

namespace HomologyPretheory

variable {C : Type v} [Category C] [Limits.HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}

/-- A morphism in the category `HomologyPretheory`. -/
@[ext]
structure Hom (HP HP' : HomologyPretheory C c) where
  /-- The natural transformation of relative homology functors in a morphism of
  `HomologyPretheory`s. -/
  hom (i : ι) : HP.Hₚ i ⟶ HP'.Hₚ i
  /-- `hom` needs to be compatible with the boundary maps. -/
  w (i j : ι) : dsimp% HP.δ i j ≫ proj₂.whiskerLeft ((HP.iso j).hom ≫ incl.whiskerLeft (hom j) ≫
      (HP'.iso j).inv) = hom i ≫ HP'.δ i j := by cat_disch

attribute [local simp] Hom.w

@[local simp]
lemma Hom.w_congr_app' {HP HP' : HomologyPretheory C c} (f : HP.Hom HP') (i j : ι) (X : TopPair) :
    (HP.δ i j).app X ≫ (proj₂.whiskerLeft ((HP.iso j).hom ≫ incl.whiskerLeft (f.hom j) ≫
    (HP'.iso j).inv)).app X = (f.hom i).app X ≫ (HP'.δ i j).app X := by
  simp only [← NatTrans.comp_app]
  apply NatTrans.congr_app
  exact f.w i j

@[local simp]
lemma Hom.w_congr_app {HP HP' : HomologyPretheory C c} (f : HP.Hom HP') (i j : ι) (X : TopPair) :
    dsimp% (HP.δ i j).app X ≫ (proj₂.whiskerLeft ((HP.iso j).hom ≫ incl.whiskerLeft (f.hom j) ≫
    (HP'.iso j).inv)).app X = (f.hom i).app X ≫ (HP'.δ i j).app X := Hom.w_congr_app' f i j X

set_option backward.isDefEq.respectTransparency false in
@[simps]
instance : Category (HomologyPretheory C c) where
  Hom := HomologyPretheory.Hom
  id _ := { hom _ := NatTrans.id _ }
  comp f g := {
    hom i := f.hom i ≫ g.hom i
    w i j := by
      have hf := f.w i j
      have hg := g.w i j
      simp_all only [Functor.whiskerLeft_comp, ← Category.assoc]
      rw [← Category.comp_id (incl.whiskerLeft (f.hom j)), ← (iso _ j).inv_hom_id]
      simp only [Functor.whiskerLeft_comp, ← Category.assoc]
      simp only [hf, Category.assoc (f.hom i), hg]
  }

set_option backward.isDefEq.respectTransparency false in
/-- Given an isomoprhism of `HomologyPretheory`s, we get an isomorphism of the homology functors
`Hₚ i`. -/
@[simps]
def Iso.hom {HP HP' : HomologyPretheory C c} (f : HP ≅ HP') (i : ι) : HP.Hₚ i ≅ HP'.Hₚ i where
  hom := f.hom.hom i
  inv := f.inv.hom i
  hom_inv_id := by
    simp only [← comp_hom]
    cat_disch
  inv_hom_id := by
    simp only [← comp_hom]
    cat_disch

end HomologyPretheory

/-- Under the assumptions of excision, the map of the pair `U` is in fact surjective. -/
lemma surjective_of_isCompl_closure ⦃X U V : TopPair⦄ (f : U ⟶ X) (g : V ⟶ X) (hf : IsEmbedding f)
    (hcompl : TopPair.IsCompl f g)
    (hU : closure (Set.range (Hom.fst f)) ⊆ interior (Set.range X.map)) :
      Function.Surjective U.map := by
  rw [← Set.range_eq_univ, Set.Subset.antisymm_iff]
  use (by simp)
  rw [← Set.image_subset_image_iff hf.fst.injective]
  have h₀ : Set.range (Hom.fst f) ⊆ Hom.fst f '' Set.range U.map ∪ Hom.fst g '' Set.range V.map :=
    by
    simp only [← Set.range_comp, ← CategoryTheory.hom_comp]
    simp only [← Arrow.w, CategoryTheory.hom_comp, Set.range_comp, ← Set.image_union,
      ← Set.sup_eq_union, codisjoint_iff.mp hcompl.snd.codisjoint, Set.top_eq_univ, Set.image_univ]
    calc
      Set.range (Hom.fst f) ⊆ closure (Set.range (Hom.fst f)) := subset_closure
      _ ⊆ interior (Set.range X.map) := hU
      _ ⊆ Set.range X.map := interior_subset
  have h₁ : Disjoint (Set.range (Hom.fst f)) (Hom.fst g '' Set.range V.map) := by
    rw [Set.disjoint_iff, ← Set.disjoint_iff_inter_eq_empty.mp hcompl.fst.disjoint]
    grind
  simp [Disjoint.subset_left_of_subset_union h₀ h₁]

set_option backward.isDefEq.respectTransparency false in
/-- Under the assumptions of excision, the map of the pair `U` is an isomorphism. -/
lemma isIso_of_isCompl_closure ⦃X U V : TopPair⦄ (f : U ⟶ X) (g : V ⟶ X) (hf : IsEmbedding f)
    (hcompl : TopPair.IsCompl f g)
    (hU : closure (Set.range (Hom.fst f)) ⊆ interior (Set.range X.map)) : IsIso U.map := by
  apply TopCat.isIso_of_bijective_of_isOpenMap _
    ⟨U.prop.injective, surjective_of_isCompl_closure f g hf hcompl hU⟩
  apply Topology.IsInducing.isOpenMap U.prop.isInducing
  simp [Function.Surjective.range_eq (surjective_of_isCompl_closure f g hf hcompl hU)]

end TopPair

namespace EilenbergSteenrod

open HomologyPretheory

variable {C : Type v} [Category C] [Limits.HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
  (HP HP' : HomologyPretheory.{u} C c)

/-- A `HomologyPretheory` is homotopy-invariant if its homology functor `Hₚ` takes homotopic maps to
the same map in homology -/
class IsHomotopyInvariant where
  homotopy ⦃X Y : TopPair⦄ (f g : X ⟶ Y) (hfg : Homotopic f g) :
      ∀ (i : ι), (HP.Hₚ i).map f = (HP.Hₚ i).map g := by cat_disch

instance : IsClosedUnderIsomorphisms (C := HomologyPretheory C c) IsHomotopyInvariant where
  of_iso {HP HP'} e hHP := ⟨by
    intro _ _ _ _ hfg _
    have := hHP.homotopy _ _ hfg
    apply (((Iso.hom e _).app _).cancel_iso_hom_left ((HP'.Hₚ _).map _) ((HP'.Hₚ _).map _)).mp
    simp only [CategoryTheory.Iso.app_hom, ← (Iso.hom _ _).hom.naturality]
    cat_disch⟩

/-- A `HomologyPretheory` has the excision-isomorphism, if cutting out a sufficiently nice subspace
`U` from a space `X`, yields an isomorphism `Hₚ i X ≅ Hₚ i (X \ U)`. -/
class HasExcisionIso where
  excision ⦃X U V : TopPair⦄ (f : U ⟶ X) (g : V ⟶ X) (hf : IsEmbedding f) (hg : IsEmbedding g)
      (hcompl : TopPair.IsCompl f g)
      (hU : closure (Set.range (Hom.fst f)) ⊆ interior (Set.range X.map)) :
        ∀ i : ι, IsIso ((HP.Hₚ i).map g) := by intro i; infer_instance

instance : IsClosedUnderIsomorphisms (C := HomologyPretheory C c) HasExcisionIso where
  of_iso e hHP := ⟨fun _ _ _ _ _ hf hg hcompl hU _ ↦ (NatIso.isIso_map_iff (Iso.hom e _) _).mp
    (hHP.excision _ _ hf hg hcompl hU _)⟩

/-- A `HomologyPretheory` is additive if its homology functor preserves coproducts. -/
class IsAdditive where
  /-- An extraordinary Eilenberg-Steenrod homology functor preserves colimits. -/
  additive (J : Type u) : ∀ (i : ι), Limits.PreservesColimitsOfShape (Discrete J) (HP.H i) := by
    intro i
    infer_instance

instance : IsClosedUnderIsomorphisms (C := HomologyPretheory C c) IsAdditive where
  of_iso {HP HP'} e h := ⟨fun _ _ ↦ @Limits.preservesColimitsOfShape_of_natIso _ _ _ _ _ _ _ _
    ((HP.iso _) ≪≫ Functor.isoWhiskerLeft incl (Iso.hom e _) ≪≫ (HP'.iso _).symm)
    (h.additive _ _)⟩

/-- This imposes that a `HomologyPretheory` has the long exact sequence of topological pairs
`⋯ ⟶ H (c.next i) X.fst ⟶ Hₚ (c.next i) X) ⟶  H i X.snd ⟶ H i X.fst ⟶ ⋯`. -/
class HasPairSequence where
  exact (X : TopPair) : ∀ (i : ι), (ComposableArrows.mk₄ ((HP.Hₚ (c.next i)).map X.j)
      ((HP.δ (c.next i) i).app X) ((HP.H i).map X.map)
      ((HP.iso i).hom.app X.fst ≫ (HP.Hₚ i).map X.j)).Exact := by cat_disch

set_option backward.isDefEq.respectTransparency false in
instance : IsClosedUnderIsomorphisms (C := HomologyPretheory C c) HasPairSequence where
  of_iso {HP HP'} e h := ⟨by
    intro X i
    let pairSeq := ComposableArrows.mk₄ ((HP.Hₚ (c.next i)).map X.j) ((HP.δ (c.next i) i).app X)
      ((HP.H i).map X.map) ((HP.iso i).hom.app X.fst ≫ (HP.Hₚ i).map X.j)
    let pairSeq' := ComposableArrows.mk₄ ((HP'.Hₚ (c.next i)).map X.j) ((HP'.δ (c.next i) i).app X)
      ((HP'.H i).map X.map) ((HP'.iso i).hom.app X.fst ≫ (HP'.Hₚ i).map X.j)
    have pairSeqIso : pairSeq ≅ pairSeq' :=
      ComposableArrows.isoMk₄
        ((Iso.hom e _).app _)
        ((Iso.hom e _).app _)
        ((proj₂.isoWhiskerLeft ((HP.iso _) ≪≫ incl.isoWhiskerLeft (Iso.hom e _) ≪≫
          (HP'.iso _).symm)).app _)
        (((HP.iso _) ≪≫ incl.isoWhiskerLeft (Iso.hom e _) ≪≫ (HP'.iso _).symm).app _)
        ((Iso.hom e _).app _)
        (by cat_disch)
        (by simp [pairSeq, pairSeq', e.hom.w_congr_app, ComposableArrows.Precomp.map])
        (by simp [pairSeq, pairSeq', ComposableArrows.Precomp.map,
          ← (HP'.iso i).inv.naturality])
        (by simp [pairSeq, pairSeq', ComposableArrows.Precomp.map])
    exact ComposableArrows.exact_of_iso pairSeqIso (h.exact _ _)⟩

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
      instIsClosedUnderIsomorphismsHomologyPretheoryIsHomotopyInvariant.of_iso e h.homotopy
    excision := instIsClosedUnderIsomorphismsHomologyPretheoryHasExcisionIso.of_iso e h.excision
    additive := instIsClosedUnderIsomorphismsHomologyPretheoryIsAdditive.of_iso e h.additive
    exact := instIsClosedUnderIsomorphismsHomologyPretheoryHasPairSequence.of_iso e h.exact
  }

variable (HP HP' : HomologyPretheory.{u} C (ComplexShape.down ℕ))

/-- A `HomologyPretheory` on `ComplexShape.down ℕ` has the dimension axiom if it is trivial on the
terminal space for `n > 0`. -/
class HasDimensionAxiom where
  dimension : ∀ (n : ℕ) (_ : n ≠ 0), Limits.IsZero ((HP.H n).obj (TopCat.of PUnit)) := by cat_disch

instance : IsClosedUnderIsomorphisms (C := HomologyPretheory C (ComplexShape.down ℕ))
    HasDimensionAxiom where
  of_iso {HP HP'} e h := ⟨fun n hn ↦ (Iso.isZero_iff (((HP.iso _) ≪≫ Functor.isoWhiskerLeft incl
    (Iso.hom e _) ≪≫ (HP'.iso _).symm).app
    (TopCat.of PUnit))).mp (h.dimension n hn)⟩

/-- An Eilenberg-Steenrod homology theory is an extraordinary Eilenberg-Steenrod homology theory
which additionally satisfies the dimension axiom. -/
class IsEilenbergSteenrod extends IsExtraordinaryEilenbergSteenrod.{u} HP where
  /-- An Eilenberg-Steenrod homology theory is trivial on the terminal space for `n > 0`. -/
  [dimension : HasDimensionAxiom HP]

instance : IsClosedUnderIsomorphisms (C := HomologyPretheory C (ComplexShape.down ℕ))
    IsEilenbergSteenrod where
  of_iso e h := {
    1 := instIsClosedUnderIsomorphismsHomologyPretheoryIsExtraordinaryEilenbergSteenrod.of_iso e h.1
    dimension :=
      instIsClosedUnderIsomorphismsHomologyPretheoryNatDownHasDimensionAxiom.of_iso e h.dimension
  }

end EilenbergSteenrod
