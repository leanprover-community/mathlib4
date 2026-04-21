/-
Copyright (c) 2026 Jakob Scharmberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scharmberg
-/

module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.BourbakiWitt
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Category.TopPair

/-!
# Eilenberg-Steenrod homology theories

In this file we introduce the Eilenberg-Steenrod axioms for homology theories.

We provide a predicate structure `IsExtraordinaryEilenbergSteenrod` with the homotopy, excision,
additivity, and exactness axioms and `IsEilenbergSteenrod` which extends it by the dimension axiom.

Both apply to functors `Hₚ : TopPair ⥤ Ab` and `H : TopCat ⥤ Ab` for every `n : ℕ` which represent
relative and regular homology, respectively, and a proof that they agree on `TopCat`. They also
require a boundary morphisms `δₙ : (Hₚ)ₙ(X, A) → H₍ₙ₋₁₎(A)` for the long exact sequence of
topological pairs. For type-theoretical reasons, we require `δₘₙ : (Hₚ)ₘ(X, A) → Hₙ(A)` for all
`m n : ℕ` with a proof that these are zero if `m ≠ n + 1`.

In addition, we provide abbreviations `IsExtraordinaryEilenbergSteenrodₚ` and `IsEilenbergSteenrodₚ`
purely on topological pairs, which use `TopPair.incl ⋙ Hₚ` for `H`.

Excision is formulated in terms of complements of topological pairs: Suppose `U` and `V` are
complements of a topological pair `X` with embeddings `f : U ⟶ X` and `g : V ⟶ X`. Suppose further
that the closure of `f₁(U₁)` is a subset of the interior of the image of `X₂` in `X₁`. Then the
excision axiom postulates that the homology of `X` is isomorphic to that of `V`. Note that this
closure condition a priori seems weaker than in the literature. However, we prove that under the
assumptions for excision above, `U` is actually an isomorphism.
-/


@[expose] public section

open CategoryTheory TopPair

namespace TopPair

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
lemma isIso_of_isCompl_closure ⦃X U V : TopPair⦄ (f : U ⟶ X) (g : V ⟶ X) (hf : IsEmbedding f)
    (hcompl : TopPair.IsCompl f g)
    (hU : closure (Set.range (Hom.fst f)) ⊆ interior (Set.range X.map)) : IsIso U.map := by
  apply TopCat.isIso_of_bijective_of_isOpenMap _
    ⟨U.prop.injective, surjective_of_isCompl_closure f g hf hcompl hU⟩
  apply Topology.IsInducing.isOpenMap U.prop.isInducing
  simp [Function.Surjective.range_eq (surjective_of_isCompl_closure f g hf hcompl hU)]

end TopPair

universe u

variable {Hₚ Hₚ' : ℕ → TopPair.{u} ⥤ Ab.{u}} {H H' : ℕ → TopCat.{u} ⥤ Ab.{u}}
  (H_incl_Hₚ : ∀ n : ℕ, H n ≅ incl ⋙ Hₚ n) (H'_incl_Hₚ' : ∀ n : ℕ, H' n ≅ incl ⋙ Hₚ' n)
  {δ : (Π m n, (Hₚ m) ⟶ proj₂ ⋙ H n)}

/-- An extraordinary Eilenberg-Steenrod homology theory requires the homotopy, excision, additivity,
and exactness axioms. -/
structure IsExtraordinaryEilenbergSteenrod
    (δ_zero : ∀ n m : ℕ, m ≠ n + 1 → δ m n = 0 := by cat_disch) where
  /-- Invariance of an extraordinary Eilenberg-Steenrod homology theory on homotopic maps. -/
  homotopy ⦃X Y : TopPair⦄ (f g : X ⟶ Y) (hfg : Homotopic f g) :
      ∀ (n : ℕ), (Hₚ n).map f = (Hₚ n).map g := by cat_disch
  /-- Excision axiom of an extraordinary Eilenberg-Steenrod homology theory. -/
  excision ⦃X U V : TopPair⦄ (f : U ⟶ X) (g : V ⟶ X) (hf : IsEmbedding f) (hg : IsEmbedding g)
      (hcompl : TopPair.IsCompl f g)
      (hU : closure (Set.range (Hom.fst f)) ⊆ interior (Set.range X.map)) :
        ∀ n : ℕ, IsIso ((Hₚ n).map g) := by intro n; infer_instance
  /-- An extraordinary Eilenberg-Steenrod homology functor preserves colimits. -/
  additive (J : Type u) : ∀ (n : ℕ), Limits.PreservesColimitsOfShape (Discrete J) (H n) := by
    intro n
    infer_instance
  /-- The long exact sequence of topological pairs in an extraordinary Eilenberg-Steenrod homology
  theory. -/
  exact (X : TopPair) : ∀ (n : ℕ),
      (ComposableArrows.mk₄ ((Hₚ (n + 1)).map X.j) ((δ (n + 1) n).app X) ((H n).map X.map)
        ((H_incl_Hₚ n).hom.app X.fst ≫ (Hₚ n).map X.j)).Exact := by cat_disch

/-- An Eilenberg-Steenrod homology theory is an extraordinary Eilenberg-Steenrod homology theory
which additionally satisfies the dimension axiom. -/
structure IsEilenbergSteenrod (δ_zero : ∀ n m : ℕ, m ≠ n + 1 → δ m n = 0 := by cat_disch)
    extends IsExtraordinaryEilenbergSteenrod.{u} H_incl_Hₚ δ_zero where
  /-- An Eilenberg-Steenrod homology theory is trivial on the terminal space for `n > 0`. -/
  dimension : ∀ (n : ℕ) (_ : n ≠ 0), Limits.IsZero ((H n).obj (TopCat.of PUnit)) := by cat_disch

section

variable {δ : (Π m n, (Hₚ m) ⟶ proj₂ ⋙ incl ⋙ Hₚ n)}

/-- An extraordinary Eilenberg-Steenrod homology theory purely on pairs is an an extraordinary
Eilenberg-Steenrod homology theory where `H = TopPair.incl ⋙ Hₚ`. -/
abbrev IsExtraordinaryEilenbergSteenrodₚ
    (δ_zero : ∀ n m : ℕ, m ≠ n + 1 → δ m n = 0 := by cat_disch) :=
  IsExtraordinaryEilenbergSteenrod.{u} (fun _ ↦ Iso.refl _) (δ := δ) δ_zero

/-- An Eilenberg-Steenrod homology theory purely on pairs is an extraordinary Eilenberg-Steenrod
homology theory purely on pairs which additionally satisfies the dimension axiom. -/
abbrev IsEilenbergSteenrodₚ (δ_zero : ∀ n m : ℕ, m ≠ n + 1 → δ m n = 0 := by cat_disch) :=
  IsEilenbergSteenrod.{u} (fun _ ↦ Iso.refl _) δ_zero

end

set_option backward.isDefEq.respectTransparency false in
lemma isExtraordinaryEilenbergSteenrod_iff_of_iso (HₚIso : ∀ n : ℕ,  (Hₚ n) ≅ (Hₚ' n))
    (δ_zero : ∀ n m : ℕ, m ≠ n + 1 → δ m n = 0) :
      IsExtraordinaryEilenbergSteenrod.{u} H_incl_Hₚ δ_zero ↔
      IsExtraordinaryEilenbergSteenrod.{u} H'_incl_Hₚ'
        (δ := (fun m n ↦ (HₚIso m).inv ≫ δ m n ≫ Functor.whiskerLeft proj₂ (H_incl_Hₚ n).hom ≫
          Functor.whiskerLeft proj₂ (Functor.whiskerLeft incl (HₚIso n).hom) ≫
          Functor.whiskerLeft proj₂ (H'_incl_Hₚ' n).inv))
        (by cat_disch) where
  mp hEES := {
    homotopy X Y f g hfg n := by
      have := hEES.homotopy f g hfg n
      apply (((HₚIso n).app X).cancel_iso_hom_left ((Hₚ' n).map f) ((Hₚ' n).map g)).mp
      simp only [CategoryTheory.Iso.app_hom, ← (HₚIso n).hom.naturality]
      cat_disch
    excision _ _ _ _ _ hf hg hcompl hU _ :=
      (NatIso.isIso_map_iff (HₚIso _) _).mp (hEES.excision _ _ hf hg hcompl hU _)
    additive _ _ := @Limits.preservesColimitsOfShape_of_natIso _ _ _ _ _ _ _ _
      ((H_incl_Hₚ _) ≪≫
        (Cat.Hom.toNatIso (Bicategory.whiskerLeftIso (incl.toCatHom) (Cat.Hom.isoMk (HₚIso _)))) ≪≫
        (H'_incl_Hₚ' _).symm) (hEES.additive _ _)
    exact X n := by
      let pairSeq := ComposableArrows.mk₄ ((Hₚ (n + 1)).map X.j)
        ((δ (n + 1) n).app X) ((H n).map X.map) ((H_incl_Hₚ n).hom.app X.fst ≫ (Hₚ n).map X.j)
      let δ' : (Π m n, (Hₚ' m) ⟶ proj₂ ⋙ H' n) :=
        (fun m n ↦ (HₚIso m).inv ≫ δ m n ≫ Functor.whiskerLeft proj₂ (H_incl_Hₚ n).hom ≫
          Functor.whiskerLeft proj₂ (Functor.whiskerLeft incl (HₚIso n).hom) ≫
          Functor.whiskerLeft proj₂ (H'_incl_Hₚ' n).inv)
      let pairSeq' := ComposableArrows.mk₄ ((Hₚ' (n + 1)).map X.j) ((δ' (n + 1) n).app X)
        ((H' n).map X.map) ((H'_incl_Hₚ' n).hom.app X.fst ≫ (Hₚ' n).map X.j)
      have pairSeqIso : pairSeq ≅ pairSeq' :=
        ComposableArrows.isoMk₄
          ((HₚIso (n + 1)).app _)
          ((HₚIso (n + 1)).app _)
          (((H_incl_Hₚ n) ≪≫ (Cat.Hom.toNatIso (Bicategory.whiskerLeftIso (incl.toCatHom)
            (Cat.Hom.isoMk (HₚIso n)))) ≪≫ (H'_incl_Hₚ' n).symm).app _)
          (((H_incl_Hₚ n) ≪≫ (Cat.Hom.toNatIso (Bicategory.whiskerLeftIso (incl.toCatHom)
            (Cat.Hom.isoMk (HₚIso n)))) ≪≫ (H'_incl_Hₚ' n).symm).app _)
          ((HₚIso n).app _)
          (by cat_disch)
          (by simp [pairSeq, pairSeq', δ', ComposableArrows.Precomp.map])
          (by simp [pairSeq, pairSeq', ComposableArrows.Precomp.map,
            ← (H'_incl_Hₚ' n).inv.naturality])
          (by simp [pairSeq, pairSeq', ComposableArrows.Precomp.map])
      exact ComposableArrows.exact_of_iso pairSeqIso (hEES.exact _ _)
  }
  mpr hEES := {
    homotopy X Y f g hfg n := by
      have := hEES.homotopy f g hfg n
      apply (((HₚIso n).symm.app X).cancel_iso_hom_left ((Hₚ n).map f) ((Hₚ n).map g)).mp
      simp only [CategoryTheory.Iso.app_hom, ← (HₚIso n).symm.hom.naturality]
      cat_disch
    excision _ _ _ _ _ hf hg hcompl hU _ :=
      (NatIso.isIso_map_iff (HₚIso _).symm _).mp (hEES.excision _ _ hf hg hcompl hU _)
    additive _ _ := @Limits.preservesColimitsOfShape_of_natIso _ _ _ _ _ _ _ _
      ((H'_incl_Hₚ' _) ≪≫
        (Cat.Hom.toNatIso (Bicategory.whiskerLeftIso (incl.toCatHom)
          (Cat.Hom.isoMk (HₚIso _).symm))) ≪≫
        (H_incl_Hₚ _).symm) (hEES.additive _ _)
    exact X n := by
      let pairSeq := ComposableArrows.mk₄ ((Hₚ (n + 1)).map X.j) ((δ (n + 1) n).app X)
        ((H n).map X.map) ((H_incl_Hₚ n).hom.app X.fst ≫ (Hₚ n).map X.j)
      let δ' : (Π m n, (Hₚ' m) ⟶ proj₂ ⋙ H' n) := (fun m n ↦ (HₚIso m).inv ≫ δ m n ≫
        Functor.whiskerLeft proj₂ (H_incl_Hₚ n).hom ≫
        Functor.whiskerLeft proj₂ (Functor.whiskerLeft incl (HₚIso n).hom) ≫
        Functor.whiskerLeft proj₂ (H'_incl_Hₚ' n).inv)
      let pairSeq' := ComposableArrows.mk₄ ((Hₚ' (n + 1)).map X.j) ((δ' (n + 1) n).app X)
        ((H' n).map X.map) ((H'_incl_Hₚ' n).hom.app X.fst ≫ (Hₚ' n).map X.j)
      have pairSeqIso : pairSeq ≅ pairSeq' :=
        ComposableArrows.isoMk₄
          ((HₚIso (n + 1)).app _)
          ((HₚIso (n + 1)).app _)
          (((H_incl_Hₚ n) ≪≫ (Cat.Hom.toNatIso (Bicategory.whiskerLeftIso (incl.toCatHom)
            (Cat.Hom.isoMk (HₚIso n)))) ≪≫ (H'_incl_Hₚ' n).symm).app _)
          (((H_incl_Hₚ n) ≪≫ (Cat.Hom.toNatIso (Bicategory.whiskerLeftIso (incl.toCatHom)
            (Cat.Hom.isoMk (HₚIso n)))) ≪≫ (H'_incl_Hₚ' n).symm).app _)
          ((HₚIso n).app _)
          (by cat_disch)
          (by simp [pairSeq, pairSeq', δ', ComposableArrows.Precomp.map])
          (by simp [pairSeq, pairSeq', ComposableArrows.Precomp.map,
            ← (H'_incl_Hₚ' n).inv.naturality])
          (by simp [pairSeq, pairSeq', ComposableArrows.Precomp.map])
      exact ComposableArrows.exact_of_iso pairSeqIso.symm (hEES.exact _ _)
  }

lemma isEilenbergSteenrod_iff_of_iso (HₚIso : ∀ n : ℕ,  (Hₚ n) ≅ (Hₚ' n))
    (δ_zero : ∀ n m : ℕ, m ≠ n + 1 → δ m n = 0) : IsEilenbergSteenrod H_incl_Hₚ δ_zero ↔
      IsEilenbergSteenrod H'_incl_Hₚ'
        (δ := (fun m n ↦ (HₚIso m).inv ≫ δ m n ≫ Functor.whiskerLeft proj₂ (H_incl_Hₚ n).hom ≫
          Functor.whiskerLeft proj₂ (Functor.whiskerLeft incl (HₚIso n).hom) ≫
          Functor.whiskerLeft proj₂ (H'_incl_Hₚ' n).inv))
        (by cat_disch) where
  mp hES := {
    1 := (isExtraordinaryEilenbergSteenrod_iff_of_iso H_incl_Hₚ H'_incl_Hₚ' HₚIso δ_zero).mp hES.1
    dimension n hn := (Iso.isZero_iff (((H_incl_Hₚ _) ≪≫
      (Cat.Hom.toNatIso (Bicategory.whiskerLeftIso (incl.toCatHom) (Cat.Hom.isoMk (HₚIso _)))) ≪≫
        (H'_incl_Hₚ' _).symm).app (TopCat.of PUnit))).mp (hES.dimension n hn)
  }
  mpr hES := {
    1 := (isExtraordinaryEilenbergSteenrod_iff_of_iso H_incl_Hₚ H'_incl_Hₚ' HₚIso δ_zero).mpr hES.1
    dimension n hn := (Iso.isZero_iff (((H'_incl_Hₚ' _) ≪≫
      (Cat.Hom.toNatIso (Bicategory.whiskerLeftIso (incl.toCatHom)
      (Cat.Hom.isoMk (HₚIso _).symm))) ≪≫
      (H_incl_Hₚ _).symm).app (TopCat.of PUnit))).mp (hES.dimension n hn)
  }
