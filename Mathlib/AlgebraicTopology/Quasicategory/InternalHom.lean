/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms
public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
public import Mathlib.CategoryTheory.LiftingProperties.PushoutProduct
public import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying
public import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# Functor Quasi-categories

-/

public section

open CategoryTheory Simplicial MorphismProperty MonoidalCategory Arrow

universe v u

namespace SSet

open modelCategoryQuillen

abbrev BdryHornPushouts :=
  (I.{u}.arrowObj.map (pushoutProduct.obj Λ[2, 1].ι)).arrowMorphism

open CartesianMonoidalCategory in
local instance {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] (X : C) :
    (tensorLeft X).PreservesMonomorphisms where
  preserves f hf := {
    right_cancellation _ _ w := by
      apply CartesianMonoidalCategory.hom_ext
      · simpa using w =≫ fst _ _
      · simpa [cancel_mono_assoc_iff] using w =≫ snd _ _}

lemma BdryTensorS_le_monomorphisms (S : SSet) : I.{u}.map (tensorLeft S) ≤ monomorphisms SSet := by
  intro X Y f ⟨_, _, ⟨_, ⟨hg⟩, ⟨e⟩⟩⟩
  rw [← arrow_mk_iso_iff (monomorphisms SSet) e]
  infer_instance

lemma innerAnodyneExtensions_eq_retracts_transfiniteCompositions' :
    innerAnodyneExtensions = (transfiniteCompositions.{u}
      (coproducts.{u} BdryHornPushouts.{u}).pushouts).retracts := by
  sorry

section ULift

-- From topcat-model-category

variable (α : Type u)

def orderIsoULift [Preorder α] : α ≃o ULift.{v} α where
  toEquiv := Equiv.ulift.symm
  map_rel_iff' := by rfl

instance [Preorder α] [SuccOrder α] : SuccOrder (ULift.{v} α) :=
  SuccOrder.ofOrderIso (orderIsoULift α)

instance [Preorder α] [WellFoundedLT α] : WellFoundedLT (ULift.{v} α) where
  wf := (orderIsoULift.{v} α).symm.toRelIsoLT.toRelEmbedding.isWellFounded.wf

end ULift

section Mono

-- From topcat-model-category

noncomputable def transfiniteCompositionOfMono {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    (coproducts.{u} I).pushouts.TransfiniteCompositionOfShape ℕ i where
  toTransfiniteCompositionOfShape :=
    (relativeCellComplexOfMono i).toTransfiniteCompositionOfShape
  map_mem d hd := by
    apply pushouts_monotone _ _
      ((relativeCellComplexOfMono i).attachCells d hd).pushouts_coproducts
    apply coproducts_monotone
    rintro _ _ _ ⟨⟩
    exact boundary_ι_mem_I d

lemma transfiniteCompositions_pushouts_coproducts :
    transfiniteCompositions.{u} (coproducts.{u} I).pushouts = monomorphisms SSet.{u} := by
  apply le_antisymm
  · rw [transfiniteCompositions_le_iff, pushouts_le_iff, coproducts_le_iff]
    exact I_le_monomorphisms
  · intro _ _ i (_ : Mono i)
    apply transfiniteCompositionsOfShape_le_transfiniteCompositions _ (ULift ℕ)
    exact ⟨(transfiniteCompositionOfMono i).ofOrderIso (orderIsoULift.{u} ℕ).symm⟩

end Mono

instance ihom_isQuasicategory {S T : SSet.{u}} [hT : Quasicategory T] :
    Quasicategory ((ihom S).obj T) := by
  rw [quasicategory_iff_from_innerFibration _ stdSimplex.isTerminalObj₀, innerFibration_iff,
    ← innerFibrations.single_le_iff, innerFibrations, ← MorphismProperty.le_llp_iff_le_rlp,
    ← coproducts_le_iff.{u}, ← pushouts_le_iff, ← transfiniteCompositions_le_iff.{u},
    ← retracts_le_iff, ← innerAnodyneExtensions_eq_retracts_transfiniteCompositions,
    innerAnodyneExtensions_eq_retracts_transfiniteCompositions', retracts_le_iff,
    transfiniteCompositions_le_iff, pushouts_le_iff, coproducts_le_iff] at hT ⊢
  ---
  have h₁ : I ≤ (single ((MonoidalClosed.pre Λ[2, 1].ι).app T)).llp := by
    · intro _ _ f ⟨n⟩
      rw [single, llp_ofHoms_iff_hasLiftingProperty,
        ← PushoutProduct.hasLiftingProperty_mk_isTerminal_iff (X := T) stdSimplex.isTerminalObj₀]
      apply hT
      · exact ⟨Arrow.mk ∂Δ[n].ι, boundary_ι_mem_I n, ⟨Iso.refl _⟩⟩
      · exact prop_single (stdSimplex.isTerminalObj₀.from T)
  ---
  rw [← coproducts_le_iff.{u}, ← pushouts_le_iff, ← transfiniteCompositions_le_iff.{u},
    transfiniteCompositions_pushouts_coproducts] at h₁
  ---
  have h₄ : I ≤
      (single ((ihom S).map ((MonoidalClosed.pre Λ[2, 1].ι).app T))).llp := by
    intro _ _ _ ⟨n⟩
    rw [single, llp_ofHoms_iff_hasLiftingProperty, ← (ihom.adjunction S).hasLiftingProperty_iff]
    apply (BdryTensorS_le_monomorphisms S).trans h₁
    · refine ⟨_, _, ⟨∂Δ[n].ι, ⟨boundary_ι_mem_I n, ⟨Iso.refl _⟩⟩⟩⟩
    · exact prop_single ((MonoidalClosed.pre Λ[2, 1].ι).app T)
  ---
  suffices I ≤ (single ((MonoidalClosed.pre Λ[2, 1].ι).app ((ihom S).obj T))).llp by
    intro _ _ f ⟨⟨_, _, _⟩, ⟨n⟩, ⟨e⟩⟩
    have := this ∂Δ[n].ι (boundary_ι_mem_I n)
    rw [llp_ofHoms_iff_hasLiftingProperty] at this ⊢
    rw [← PushoutProduct.hasLiftingProperty_mk_isTerminal_iff
      (X := (ihom S).obj T) stdSimplex.isTerminalObj₀] at this
    rwa [← HasLiftingProperty.iff_of_arrow_iso_left e]
  ---
  intro _ _ _ ⟨n⟩
  have := h₄ ∂Δ[n].ι (boundary_ι_mem_I n)
  rw [llp_ofHoms_iff_hasLiftingProperty] at this ⊢
  ---
  refine (HasLiftingProperty.iff_of_arrow_iso_right _ ?_).1 this
  refine Arrow.isoMk' _ _ ?_ ?_ ?_
  · refine (MonoidalClosed.ihomCurryIso Δ[2] S T).symm ≪≫ ?_ ≪≫
      (MonoidalClosed.ihomCurryIso S Δ[2] T)
    refine Iso.app ?_ T
    exact asIso ((conjugateEquiv (ihom.adjunction _) (ihom.adjunction _))
      ((curriedTensor _).map (β_ _ _).hom))
  · refine (MonoidalClosed.ihomCurryIso Λ[2, 1].toSSet S T).symm ≪≫ ?_ ≪≫
      (MonoidalClosed.ihomCurryIso S Λ[2, 1].toSSet T)
    refine Iso.app ?_ T
    exact asIso ((conjugateEquiv (ihom.adjunction _) (ihom.adjunction _))
      ((curriedTensor _).map (β_ _ _).hom))
  · rfl

end SSet
