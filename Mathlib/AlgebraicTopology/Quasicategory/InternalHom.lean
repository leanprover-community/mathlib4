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

abbrev bdryHornPushouts := I.{u}.strictMapArrow (pushoutProduct.obj Λ[2, 1].ι)

lemma temp {A B : SSet.{u}} (f : A ⟶ B) (X : SSet.{u}) {T : SSet.{u}} (t : Limits.IsTerminal T) :
    I.{u} ≤
      (single ((MonoidalClosed.pre f).app X)).llp ↔
    I.{u}.strictMapArrow (pushoutProduct.obj f) ≤
      (single (t.from X)).llp := by
  simp only [le_llp_iff_le_rlp, single_le_iff]
  constructor
  · rintro h _ _ g ⟨⟨_, _, _⟩, ⟨n⟩⟩
    erw [PushoutProduct.hasLiftingProperty_mk_isTerminal_iff t]
    exact h _ (boundary_ι_mem_I n)
  · intro h _ _ _ ⟨n⟩
    rw [← PushoutProduct.hasLiftingProperty_mk_isTerminal_iff t]
    apply h (Arrow.mk f □ ∂Δ[n].ι).hom
    constructor
    exact boundary_ι_mem_I n

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
      (coproducts.{u} bdryHornPushouts.{u}).pushouts).retracts := by
  apply le_antisymm
  ·
    rw [innerAnodyneExtensions_eq_retracts_transfiniteCompositions]
    /-
    rw [retracts_le_iff, transfiniteCompositions_le_iff, pushouts_le_iff, coproducts_le_iff,
      innerAnodyneExtensions_eq_llp_rlp]
    refine le_trans ?_ (retracts_le_llp_rlp _)
    -/

    let : (transfiniteCompositions.{u, u}
        (coproducts.{u} bdryHornPushouts).pushouts).retracts.IsStableUnderRetracts := by
      sorry
    rw [retracts_le_iff]
    --rw [← llp_rlp_of_hasSmallObjectArgument]

    sorry
  ·

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

lemma quasicategory_iff_trivialFibration (T : SSet.{u}) :
    Quasicategory T ↔ I.rlp ((MonoidalClosed.pre Λ[2, 1].ι).app T) := by
  rw [quasicategory_iff_from_innerFibration _ stdSimplex.isTerminalObj₀, innerFibration_iff,
    ← innerFibrations.single_le_iff, innerFibrations, ← MorphismProperty.le_llp_iff_le_rlp,
    ← coproducts_le_iff.{u}, ← pushouts_le_iff, ← transfiniteCompositions_le_iff.{u},
    ← retracts_le_iff, ← innerAnodyneExtensions_eq_retracts_transfiniteCompositions,
    innerAnodyneExtensions_eq_retracts_transfiniteCompositions', retracts_le_iff,
    transfiniteCompositions_le_iff, pushouts_le_iff, coproducts_le_iff, ← temp, le_llp_iff_le_rlp,
    single_le_iff]

instance ihom_isQuasicategory {S T : SSet.{u}} [hT : Quasicategory T] :
    Quasicategory ((ihom S).obj T) := by
  rw [quasicategory_iff_trivialFibration, ← I.rlp.single_le_iff, ← le_llp_iff_le_rlp] at hT ⊢
  rw [← coproducts_le_iff.{u}, ← pushouts_le_iff, ← transfiniteCompositions_le_iff.{u},
    transfiniteCompositions_pushouts_coproducts] at hT
  ---
  have h : I ≤ (single ((ihom S).map ((MonoidalClosed.pre Λ[2, 1].ι).app T))).llp := by
    rw [le_llp_iff_le_rlp, single_le_iff]
    intro _ _ _ ⟨n⟩
    rw [← (ihom.adjunction S).hasLiftingProperty_iff]
    apply (BdryTensorS_le_monomorphisms S).trans hT
    · refine ⟨_, _, ⟨∂Δ[n].ι, ⟨boundary_ι_mem_I n, ⟨Iso.refl _⟩⟩⟩⟩
    · exact prop_single _
  ---
  intro _ _ _ ⟨n⟩
  have := h ∂Δ[n].ι (boundary_ι_mem_I n)
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
