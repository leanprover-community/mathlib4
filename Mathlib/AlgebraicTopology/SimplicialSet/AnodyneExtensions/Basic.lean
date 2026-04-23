/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.CategoryTheory.SmallObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Pairing
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RankNat
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RelativeCellComplex
import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Anodyne extensions

Anodyne extensions form a property of morphisms in the category of simplicial
sets. It contains horn inclusions and it is closed under coproducts, pushouts,
transfinite compositions and retracts. Equivalently, using the small
object argument, anodyne extensions can be defined (and are defined here)
as the class of morphisms that satisfy the left lifting property with respect
to the class of fibrations (for the Quillen model category structure:
fibrations are morphisms that have the right lifting property with respect
to horn inclusions). When the Quillen model category structure is fully
upstreamed (TODO @joelriou), it can be shown that a morphism `f` is an
anodyne extension iff `f` is a cofibration that is also a weak equivalence.

We also introduce the class of strong anodyne extensions that could be defined
as a closure similarly as anodyne extensions, but without taking the closure
under retracts. Sean Moss has given a combinatorial description of these
strong anodyne extensions: the inclusion `A.ι : A ⟶ X` of a subcomplex `A`
of a simplicial set `X` is a strong anodyne extension iff there exists
a regular pairing for `A`. In this file, we define strong anodyne extensions
in terms of such regular pairings, and using the main result of the file
`Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/RelativeCellComplex.lean`
we show that a strong anodyne extension is an anodyne extension.

## TODO
* introduce inner variants of these definitions
* show that strong anodyne extensions are indeed stable under coproducts,
  transfinite compositions and pushouts (the proof should reduce to the
  construction of pairings)
* study the interaction between anodyne extension and binary products:
  the critical case consists in showing that inclusions
  `Λ[m, i] ⊗ Δ[n] ∪ Δ[m] ⊗ ∂Δ[n] ⟶ Δ[m] ⊗ Δ[n]` are strong anodyne extensions (@joelriou)
* show that anodyne extensions are stable under the subdivision functor (@joelriou)

## References
* [P. Gabriel, M. Zisman, *Calculus of fractions and homotopy theory*, IV.2][gabriel-zisman-1967]
* [Sean Moss, *Another approach to the Kan-Quillen model structure*][moss-2020]

-/

@[expose] public section

universe u

open CategoryTheory HomotopicalAlgebra Simplicial

namespace SSet

open MorphismProperty

open modelCategoryQuillen in
/-- In the category of simplicial sets, an anodyne extension is a morphism
that has the left lifting property with respect to fibrations, where
a fibration is a morphism that has the right lifting property with respect
to horn inclusions. We do not introduce a typeclass for anodyne extensions
because when the Quillen model structure is fully upstreamed (TODO @joelriou),
the assumption `anodyneExtensions f` can be spelled as
`[Cofibration f] [WeakEquivalence f]`. -/
def anodyneExtensions : MorphismProperty SSet.{u} := (fibrations _).llp
deriving IsMultiplicative, RespectsIso, IsStableUnderCobaseChange,
  IsStableUnderRetracts, IsStableUnderTransfiniteComposition,
  IsStableUnderCoproducts

lemma anodyneExtensions.of_isIso {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f] :
    anodyneExtensions f :=
  MorphismProperty.of_isIso anodyneExtensions f

lemma anodyneExtensions_eq_llp_rlp :
    anodyneExtensions.{u} = modelCategoryQuillen.J.rlp.llp :=
  rfl

lemma anodyneExtensions.horn_ι {n : ℕ} [NeZero n] (i : Fin (n + 1)) :
    anodyneExtensions.{u} Λ[n, i].ι := by
  rw [anodyneExtensions_eq_llp_rlp]
  exact le_llp_rlp _ _ (modelCategoryQuillen.horn_ι_mem_J n i)

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

/-- In the category of simplicial sets, a strong anodyne extension is a morphism
which belongs to the closure of horn inclusions by pushouts, coproducts,
transfinite compositions (but not by retracts). We define this class here
by saying that `f : X ⟶ Y` is a strong anodyne extension if `f` is a monomorphism
and there exists a regular pairing (in the sense of Moss) for the subcomplex
`Subcomplex.range f` of `Y`. -/
def strongAnodyneExtensions : MorphismProperty SSet.{u} :=
  fun _ _ f ↦ Mono f ∧ ∃ (P : (Subcomplex.range f).Pairing), P.IsRegular

lemma Subcomplex.Pairing.strongAnodyneExtensions {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsRegular] :
    strongAnodyneExtensions A.ι :=
  ⟨inferInstance, by
    generalize h : Subcomplex.range A.ι = B
    obtain rfl : B = A := by simpa using h.symm
    exact ⟨P, inferInstance⟩⟩

lemma strongAnodyneExtensions_ι_iff {X : SSet.{u}} (A : X.Subcomplex) :
    strongAnodyneExtensions A.ι ↔ ∃ (P : A.Pairing), P.IsRegular :=
  ⟨fun hA ↦ by
    obtain ⟨_, P, _, rfl⟩ :
        ∃ (B : X.Subcomplex) (P : B.Pairing), P.IsRegular ∧ B = A := by
      obtain ⟨_, P, _⟩ := hA
      exact ⟨_, P, inferInstance, by simp⟩
    exact ⟨P, inferInstance⟩,
  fun ⟨P, _⟩ ↦ P.strongAnodyneExtensions⟩

lemma Subcomplex.Pairing.anodyneExtensions {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsRegular] :
    anodyneExtensions A.ι :=
  transfiniteCompositionsOfShape_le _ _ _
    ⟨P.rankFunction.relativeCellComplex.toTransfiniteCompositionOfShape, fun j hj ↦ by
      refine (?_ : (_ : MorphismProperty _) ≤ _ ) _
        (P.rankFunction.relativeCellComplex.attachCells j hj).pushouts_coproducts
      simp only [pushouts_le_iff, coproducts_le_iff]
      rintro _ _ _ ⟨c⟩
      exact .horn_ι c.index⟩

lemma strongAnodyneExtensions_le_anodyneExtensions :
    strongAnodyneExtensions.{u} ≤ anodyneExtensions := by
  rintro X Y f ⟨_, P, _⟩
  rw [← Subfunctor.toRange_ι f]
  exact comp_mem _ _ _ (.of_isIso _) P.anodyneExtensions

end SSet
