/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RankNat
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RelativeCellComplex
public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.CategoryTheory.SmallObject.Basic

/-!
# Inner anodyne extensions

Much of this file is mirrored from
`Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic`.

*Inner* anodyne extensions form a property of morphisms in the category of simplicial
sets. It contains *inner* horn inclusions and it is closed under coproducts, pushouts,
transfinite compositions and retracts. Equivalently, using the small
object argument, inner anodyne extensions can be defined (and are defined here)
as the class of morphisms that satisfy the left lifting property with respect
to the class of inner fibrations.

-/

@[expose] public section

universe u

open CategoryTheory HomotopicalAlgebra Simplicial

namespace SSet

open MorphismProperty

/-- In the category of simplicial sets, an *inner* anodyne extension is a morphism
that has the left lifting property with respect to *inner* fibrations, where
an inner fibration is a morphism that has the right lifting property with respect
to inner horn inclusions. -/
def innerAnodyneExtensions : MorphismProperty SSet.{u} := innerFibrations.llp
deriving IsMultiplicative, RespectsIso, IsStableUnderCobaseChange,
  IsStableUnderRetracts, IsStableUnderTransfiniteComposition,
  IsStableUnderCoproducts

lemma innerAnodyneExtensions.of_isIso {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f] :
    innerAnodyneExtensions f :=
  MorphismProperty.of_isIso innerAnodyneExtensions f

lemma innerAnodyneExtensions_eq_llp_rlp :
    innerAnodyneExtensions.{u} = innerHornInclusions.rlp.llp :=
  rfl

lemma innerAnodyneExtensions.horn_ι {n : ℕ} {i : Fin (n + 3)}
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) :
    innerAnodyneExtensions.{u} Λ[n + 2, i].ι := by
  rw [innerAnodyneExtensions_eq_llp_rlp]
  exact le_llp_rlp _ _ (horn_ι_mem_innerHornInclusions h0 hn)

lemma innerAnodyneExtensions.horn_ι' {n : ℕ} [NeZero n] {i : Fin (n + 2)}
    (h0 : 0 < i) (hn : i < Fin.last (n + 1)) :
    innerAnodyneExtensions.{u} Λ[n + 1, i].ι := by
  rw [innerAnodyneExtensions_eq_llp_rlp]
  exact le_llp_rlp _ _ (horn_ι_mem_innerHornInclusions' h0 hn)

lemma innerAnodyneExtensions_le : innerAnodyneExtensions ≤ anodyneExtensions.{u} := by
  rw [anodyneExtensions_eq_llp_rlp, innerAnodyneExtensions_eq_llp_rlp, le_llp_iff_le_rlp,
    rlp_llp_rlp]
  exact antitone_rlp innerHornInclusions_le_J

attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType

instance (n : ℕ) : MorphismProperty.IsSmall.{u}
    (MorphismProperty.ofHoms.{u}
      (fun p : {p : Fin (n + 3) // 0 < p ∧ p < Fin.last (n + 2)} ↦ Λ[n + 2, p].ι)) :=
  isSmall_ofHoms ..

instance : MorphismProperty.IsSmall.{u} innerHornInclusions.{u} :=
  isSmall_iSup ..

instance : IsCardinalForSmallObjectArgument innerHornInclusions.{u} Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      simp only [innerHornInclusions, iSup_iff] at hi
      obtain ⟨n, ⟨i⟩⟩ := hi
      infer_instance
    infer_instance

instance : HasSmallObjectArgument.{u} innerHornInclusions.{u} :=
  ⟨.aleph0, inferInstance, inferInstance, inferInstance⟩

lemma innerAnodyneExtensions_eq_retracts_transfiniteCompositions :
    innerAnodyneExtensions = (transfiniteCompositions.{u}
      (coproducts.{u} innerHornInclusions.{u}).pushouts).retracts := by
  rw [innerAnodyneExtensions_eq_llp_rlp, llp_rlp_of_hasSmallObjectArgument]

lemma innerAnodyneExtensions_eq_retracts_transfiniteCompositionsOfShape :
    innerAnodyneExtensions = (transfiniteCompositionsOfShape
      (coproducts.{u} innerHornInclusions.{u}).pushouts ℕ).retracts := by
  rw [innerAnodyneExtensions_eq_llp_rlp,
    SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0]

def strongInnerAnodyneExtensions : MorphismProperty SSet.{u} :=
  fun _ _ f ↦ Mono f ∧ ∃ (P : (Subcomplex.range f).Pairing) (_ : P.IsRegular), P.IsInner

lemma Subcomplex.Pairing.innerAnodyneExtensions {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsRegular] [P.IsInner] :
    innerAnodyneExtensions A.ι :=
  transfiniteCompositionsOfShape_le _ _ _
    ⟨P.rankFunction.relativeCellComplex.toTransfiniteCompositionOfShape, fun j hj ↦ by
      refine (?_ : (_ : MorphismProperty _) ≤ _ ) _
        (P.rankFunction.relativeCellComplex.attachCells j hj).pushouts_coproducts
      simp only [pushouts_le_iff, coproducts_le_iff]
      rintro _ _ _ ⟨c⟩
      have h0 := Fin.pos_iff_ne_zero.mpr (IsInner.ne_zero c.s rfl)
      have hn := Fin.lt_last_iff_ne_last.mpr (IsInner.ne_last c.s rfl)
      have : NeZero c.dim := ⟨by grind⟩
      exact .horn_ι' h0 hn⟩

lemma Subcomplex.Pairing.strongInnerAnodyneExtensions {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsRegular] [P.IsInner] :
    strongInnerAnodyneExtensions A.ι :=
  ⟨inferInstance, by

    sorry
    /-
    generalize h : Subcomplex.range A.ι = B
    obtain rfl : B = A := by simpa using h.symm
    exact ⟨P, inferInstance⟩⟩, P.innerAnodyneExtensions
    -/

    ⟩

lemma strongInnerAnodyneExtensions_ι_iff {X : SSet.{u}} (A : X.Subcomplex) :
    strongInnerAnodyneExtensions A.ι ↔ ∃ (P : A.Pairing) (_ : P.IsRegular), P.IsInner :=
  ⟨fun hA ↦ by
    obtain ⟨_, P, _, ⟨_, rfl⟩⟩ :
        ∃ (B : X.Subcomplex) (P : B.Pairing) (h : P.IsRegular), P.IsInner ∧ B = A := by
      obtain ⟨⟨_, P₁, _⟩, P₂⟩ := hA
      exact ⟨_, P₁, inferInstance, ⟨sorry, by simp⟩⟩
    refine ⟨P, ⟨inferInstance, inferInstance⟩⟩,
  fun ⟨P, ⟨_, _⟩⟩ ↦ P.strongInnerAnodyneExtensions⟩

end SSet
