/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

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

end SSet
