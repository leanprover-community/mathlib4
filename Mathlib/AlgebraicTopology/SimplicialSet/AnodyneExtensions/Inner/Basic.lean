/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic

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

public section

universe u

open CategoryTheory HomotopicalAlgebra Simplicial

namespace SSet

open MorphismProperty

/-- In the category of simplicial sets, an *inner* anodyne extension is a morphism
that has the left lifting property with respect to *inner* fibrations, where
an inner fibration is a morphism that has the right lifting property with respect
to inner horn inclusions. -/
@[expose, kerodon 01BR]
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

lemma innerAnodyneExtensions.horn_ι {n : ℕ} {i : Fin (n + 1)}
    (h0 : 0 < i) (hn : i < Fin.last n) :
    innerAnodyneExtensions.{u} Λ[n, i].ι := by
  rw [innerAnodyneExtensions_eq_llp_rlp]
  exact le_llp_rlp _ _ (horn_ι_mem_innerHornInclusions h0 hn)

lemma innerAnodyneExtensions_le : innerAnodyneExtensions ≤ anodyneExtensions.{u} := by
  rw [anodyneExtensions_eq_llp_rlp, innerAnodyneExtensions_eq_llp_rlp, le_llp_iff_le_rlp,
    rlp_llp_rlp]
  exact antitone_rlp innerHornInclusions_le_J

attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType

instance : MorphismProperty.IsSmall.{u} innerHornInclusions.{u} := by
  rw [innerHornInclusions_eq_iSup]
  have (n : ℕ) : MorphismProperty.IsSmall.{u}
    (MorphismProperty.ofHoms.{u}
      fun p : {p : Fin (n + 3) // 0 < p ∧ p < Fin.last (n + 2)} ↦ Λ[n + 2, p].ι) :=
    isSmall_ofHoms ..
  exact isSmall_iSup _

instance : IsCardinalForSmallObjectArgument innerHornInclusions.{u} Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      simp only [innerHornInclusions_eq_iSup, iSup_iff] at hi
      obtain ⟨n, ⟨i⟩⟩ := hi
      infer_instance
    infer_instance

instance : HasSmallObjectArgument.{u} innerHornInclusions.{u} where
  exists_cardinal := ⟨.aleph0, inferInstance, inferInstance, inferInstance⟩

lemma innerAnodyneExtensions_eq_retracts_transfiniteCompositions :
    innerAnodyneExtensions = (transfiniteCompositions.{u}
      (coproducts.{u} innerHornInclusions.{u}).pushouts).retracts := by
  rw [innerAnodyneExtensions_eq_llp_rlp, llp_rlp_of_hasSmallObjectArgument]

lemma innerAnodyneExtensions_eq_retracts_transfiniteCompositionsOfShape :
    innerAnodyneExtensions = (transfiniteCompositionsOfShape
      (coproducts.{u} innerHornInclusions.{u}).pushouts ℕ).retracts := by
  rw [innerAnodyneExtensions_eq_llp_rlp,
    SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0]

/-- In the category of simplicial sets, a strong *inner* anodyne extension is a morphism
which belongs to the closure of *inner* horn inclusions by pushouts, coproducts,
transfinite compositions (but not by retracts). We define this class here
by saying that `f : X ⟶ Y` is a strong inner anodyne extension if `f` is a monomorphism
and there exists a regular, *inner* pairing (in the sense of Moss) for the subcomplex
`Subcomplex.range f` of `Y`. -/
def strongInnerAnodyneExtensions : MorphismProperty SSet.{u} :=
  fun _ _ f ↦ Mono f ∧ ∃ (P : (Subcomplex.range f).Pairing) (_ : P.IsRegular), P.IsInner

lemma strongInnerAnodyneExtensions.mono {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : strongInnerAnodyneExtensions f) : Mono f := hf.1

lemma strongInnerAnodyneExtensions_le_strongAnodyneExtensions :
    strongInnerAnodyneExtensions.{u} ≤ strongAnodyneExtensions :=
  fun _ _ _ ⟨_, P, _, _⟩ ↦ ⟨inferInstance, P, inferInstance⟩

lemma Subcomplex.Pairing.strongInnerAnodyneExtensions {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [h₁ : P.IsRegular] [h₂ : P.IsInner] :
    strongInnerAnodyneExtensions A.ι :=
  ⟨inferInstance, Pairing.ofIso P (Iso.refl _)
    (by simp only [Iso.refl_hom, preimage_id, Subfunctor.range_ι]), inferInstance, inferInstance⟩

lemma strongInnerAnodyneExtensions_ι_iff {X : SSet.{u}} (A : X.Subcomplex) :
    strongInnerAnodyneExtensions A.ι ↔ ∃ (P : A.Pairing) (_ : P.IsRegular), P.IsInner :=
  ⟨fun hA ↦ by
    obtain ⟨_, P, _, ⟨_, rfl⟩⟩ :
        ∃ (B : X.Subcomplex) (P : B.Pairing) (h : P.IsRegular), P.IsInner ∧ B = A := by
      obtain ⟨_, P₁, _, P₂⟩ := hA
      exact ⟨_, P₁, inferInstance, ⟨P₂, by simp⟩⟩
    exact ⟨P, ⟨inferInstance, inferInstance⟩⟩,
  fun ⟨P, ⟨_, _⟩⟩ ↦ P.strongInnerAnodyneExtensions⟩

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
      exact .horn_ι h0 hn⟩

instance : strongInnerAnodyneExtensions.{u}.RespectsIso where
  precomp e _ f hf := by
    obtain ⟨_, P, hP, hP'⟩ := hf
    refine ⟨inferInstance, P.ofIso (Iso.refl _) ?_, inferInstance, inferInstance⟩
    simp [Subcomplex.range_comp, Subcomplex.range_eq_top e, Subcomplex.image_top]
  postcomp e _ f hf := by
    obtain ⟨_, P, hP, hP'⟩ := hf
    refine ⟨inferInstance, P.ofIso (asIso e).symm ?_, inferInstance, inferInstance⟩
    simp [Subcomplex.preimage_inv, Subcomplex.range_comp]

lemma strongInnerAnodyneExtensions_le_innerAnodyneExtensions :
    strongInnerAnodyneExtensions.{u} ≤ innerAnodyneExtensions := by
  rintro X Y f ⟨_, P, _, _⟩
  rw [← Subfunctor.toRange_ι f]
  exact comp_mem _ _ _ (.of_isIso _) P.innerAnodyneExtensions

end SSet
