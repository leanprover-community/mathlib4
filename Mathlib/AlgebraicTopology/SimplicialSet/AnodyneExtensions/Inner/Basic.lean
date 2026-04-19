/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.CategoryTheory.SmallObject.Basic

@[expose] public section

universe u

open CategoryTheory HomotopicalAlgebra Simplicial

namespace SSet

open MorphismProperty

def innerAnodyneExtensions : MorphismProperty SSet.{u} := innerFibrations.llp
deriving IsMultiplicative, RespectsIso, IsStableUnderCobaseChange,
  IsStableUnderRetracts--, IsStableUnderTransfiniteComposition,
  --IsStableUnderCoproducts

lemma anodyneExtensions.of_isIso {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f] :
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

attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType

instance (n : ℕ) : MorphismProperty.IsSmall.{u}
    (MorphismProperty.ofHoms.{u} (fun (i : Fin (n + 2)) ↦ Λ[n + 1, i].ι)) :=
  isSmall_ofHoms ..

instance : MorphismProperty.IsSmall.{u} modelCategoryQuillen.J.{u} :=
  isSmall_iSup ..

instance : IsCardinalForSmallObjectArgument modelCategoryQuillen.J.{u} Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      simp only [modelCategoryQuillen.J, iSup_iff] at hi
      obtain ⟨n, ⟨i⟩⟩ := hi
      infer_instance
    infer_instance

instance : HasSmallObjectArgument.{u} modelCategoryQuillen.J.{u} :=
  ⟨.aleph0, inferInstance, inferInstance, inferInstance⟩

lemma anodyneExtensions_eq_retracts_transfiniteCompositions :
    anodyneExtensions = (transfiniteCompositions.{u}
      (coproducts.{u} modelCategoryQuillen.J.{u}).pushouts).retracts := by
  rw [anodyneExtensions_eq_llp_rlp, llp_rlp_of_hasSmallObjectArgument]

lemma anodyneExtensions_eq_retracts_transfiniteCompositionsOfShape :
    anodyneExtensions = (transfiniteCompositionsOfShape
      (coproducts.{u} modelCategoryQuillen.J.{u}).pushouts ℕ).retracts := by
  rw [anodyneExtensions_eq_llp_rlp,
    SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0]

end SSet
