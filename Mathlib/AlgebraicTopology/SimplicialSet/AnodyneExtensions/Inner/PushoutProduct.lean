/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.UnionProd
public import Mathlib.AlgebraicTopology.SimplicialSet.PushoutProduct
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import Mathlib.CategoryTheory.Monoidal.Braided.PushoutObjObj
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Inner anodyne extensions and pushout-products, inner fibrations and pullbacks

This file is mirrored from `SSet/AnodyneExtensions/PushoutProduct`.

The main result in this file is that if `i : X₁ ⟶ Y₁` is a monomorphism in `SSet`
and `j : X₂ ⟶ Y₂` is an inner anodyne extension, then the pushout-product
of `i` and `j` is an inner anodyne extension
(`SSet.innerAnodyneExtensions_pushoutObjObjι`). This is closely related to the lemma
`SSet.innerFibration_pullbackObjObjπ` which says that if `i : X₁ ⟶ Y₁` is a monomorphism
and `p : E ⟶ B` is an inner fibration, then the canonical morphism
from `Y₁ ⟶[SSet] E` to the pullback of `X₁ ⟶[SSet] E` and `Y₁ ⟶[SSet] B`
over `X₁ ⟶[SSet] B` is also an inner fibration. In particular, if `A : SSet`
and `X` is a quasi-category, then the internal hom `A ⟶[SSet] X` is also a quasi-category.

For implementation details, see `SSet/AnodyneExtensions/PushoutProduct`.

## References

- [Jack McKoen, *A Formalization of Functor Quasi-Categories in Lean 4*][mckoen2026]

## Note

The result that the internal hom into a quasi-category is also a quasi-category was first
formalized by Jack McKoen for his master's thesis, following an approach outlined on
Kerodon (https://kerodon.net/tag/0066). Specifically, this approach hinges on the lemma
https://kerodon.net/tag/0079 which is avoided in the mathlib implementation.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Simplicial HomotopicalAlgebra Limits

namespace SSet

namespace prodStdSimplex

lemma innerAnodyneExtensions_unionProd_ι {m : ℕ} (k : Fin (m + 2)) (h0 : 0 < k)
    (hn : k < Fin.last (m + 1)) (n : ℕ) :
    innerAnodyneExtensions (Subcomplex.unionProd.{u} Λ[m + 1, k] ∂Δ[n]).ι := by
  obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hn)
  obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero
    (Fin.ne_zero_of_lt (show 0 < k from Fin.val_pos_iff.mp h0))
  exact (pairing k.castSucc.succ n).innerAnodyneExtensions

end prodStdSimplex

section

variable {X₁ X₂ Y₁ Y₂ E B : SSet.{u}}
  {i : X₁ ⟶ Y₁} {j : X₂ ⟶ Y₂} {p : E ⟶ B}

lemma innerFibration_pullbackObjObjπ [Mono i] [InnerFibration p]
    (sq₁₃ : MonoidalClosed.internalHom.PullbackObjObj i p) :
    InnerFibration sq₁₃.π := by
  rw [innerFibration_iff]
  intro _ _ _ ⟨k, h0, hn⟩
  let sq₁₂ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i Λ[_, k].ι
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq₁₂]
  suffices innerAnodyneExtensions sq₁₂.ι from
    this _ (by rwa [← innerFibration_iff])
  intro E B p hp
  rw [HasLiftingProperty.iff_of_arrow_iso_left
    (show Arrow.mk sq₁₂.ι ≅ Arrow.mk sq₁₂.flipTensor.ι from
      Arrow.isoMk (Iso.refl _) (β_ _ _))]
  let sq₁₃' := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom Λ[_, k].ι p
  rw [internalHomAdjunction₂.hasLiftingProperty_iff _ sq₁₃']
  suffices (MorphismProperty.monomorphisms _).rlp sq₁₃'.π from this _ inferInstance
  rw [rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff
    (Subcomplex.unionProd.pushoutObjObj.{u} _ _),
    Subcomplex.unionProd.pushoutObjObj_ι]
  exact prodStdSimplex.innerAnodyneExtensions_unionProd_ι k h0 hn n _ hp

lemma innerAnodyneExtensions_pushoutObjObjι
    (sq₁₂ : (curriedTensor _).PushoutObjObj i j) [Mono i] (hj : innerAnodyneExtensions j) :
    innerAnodyneExtensions sq₁₂.ι := by
  intro E B p hp
  let sq₁₃ := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom i p
  rw [internalHomAdjunction₂.hasLiftingProperty_iff _ sq₁₃]
  apply hj
  rw [← innerFibration_iff] at hp ⊢
  exact innerFibration_pullbackObjObjπ sq₁₃

lemma innerAnodyneExtensions_pushoutObjObjι'
    (sq₁₂ : (curriedTensor _).PushoutObjObj i j)
    [Mono j] (hi : innerAnodyneExtensions i) :
    innerAnodyneExtensions sq₁₂.ι := by
  refine (innerAnodyneExtensions.arrow_mk_iso_iff ?_).1
    (innerAnodyneExtensions_pushoutObjObjι sq₁₂.flipTensor hi)
  exact Arrow.isoMk (Iso.refl _) (β_ _ _)

end

lemma innerAnodyneExtensions_unionProd_ι
    {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
    (hB : innerAnodyneExtensions B.ι) :
    innerAnodyneExtensions (A.unionProd B).ι :=
  innerAnodyneExtensions_pushoutObjObjι (Subcomplex.unionProd.pushoutObjObj A B) hB

lemma innerAnodyneExtensions_unionProd_ι'
    {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
    (hA : innerAnodyneExtensions A.ι) :
    innerAnodyneExtensions (A.unionProd B).ι :=
  innerAnodyneExtensions_pushoutObjObjι' (Subcomplex.unionProd.pushoutObjObj A B) hA

lemma innerAnodyneExtensions.whiskerRight
    {X Y : SSet.{u}} {f : X ⟶ Y} (hf : innerAnodyneExtensions f) (Z : SSet.{u}) :
    innerAnodyneExtensions (f ▷ Z) :=
  innerAnodyneExtensions_pushoutObjObjι'
    (.ofIsInitialRight (curriedTensor _) f (initial.to Z) initialIsInitial) hf

lemma innerAnodyneExtensions.whiskerLeft
    {X Y : SSet.{u}} {f : X ⟶ Y} (hf : innerAnodyneExtensions f) (Z : SSet.{u}) :
    innerAnodyneExtensions (Z ◁ f) :=
  innerAnodyneExtensions_pushoutObjObjι
    (.ofIsInitialLeft (curriedTensor _) (initial.to Z) f initialIsInitial) hf

instance {E B X : SSet.{u}} (p : E ⟶ B) [InnerFibration p] :
    InnerFibration ((ihom X).map p) :=
  innerFibration_pullbackObjObjπ (Functor.PullbackObjObj.ofIsInitial
    MonoidalClosed.internalHom (initial.to X) p initialIsInitial)

instance {A B : SSet.{u}} (i : A ⟶ B) [Mono i] (X : SSet.{u}) [Quasicategory X] :
    InnerFibration ((MonoidalClosed.pre i).app X) :=
  innerFibration_pullbackObjObjπ (Functor.PullbackObjObj.ofIsTerminal
    MonoidalClosed.internalHom i (terminal.from X) terminalIsTerminal)

instance (A : SSet.{u}) : Quasicategory ((ihom A).obj (⊤_ _)) := by
  have : IsIso (terminal.from ((ihom A).obj (⊤_ _))) :=
    isIso_of_isTerminal (IsTerminal.isTerminalObj _ _ terminalIsTerminal)
      terminalIsTerminal _
  infer_instance

instance {A X : SSet.{u}} [Quasicategory X] : Quasicategory ((ihom A).obj X) :=
  quasicategory_of_innerFibration ((ihom A).map (terminal.from X))

end SSet
