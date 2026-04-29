/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Path objects

We introduce a notion of path object for an object `A : C` in a model category.
It consists of an object `P`, a weak equivalence `ι : A ⟶ P` equipped with two retractions
`p₀` and `p₁`. This notion shall be important in the definition of "right homotopies"
in model categories.

This file dualizes the definitions in the file
`Mathlib/AlgebraicTopology/ModelCategory/Cylinder.lean`.

## Implementation notes

The most important definition in this file is `PathObject A`. This structure
extends another structure `PrepathObject A` (which does not assume that `C`
has a notion of weak equivalences, which can be interesting in situations
where we have not yet obtained the model category axioms).

The good properties of path objects are stated as typeclasses `PathObject.IsGood`
and `PathObject.IsVeryGood`.

The existence of very good path objects in model categories is stated
in the lemma `PathObject.exists_very_good`.

## References
* [Daniel G. Quillen, Homotopical algebra][Quillen1967]
* https://ncatlab.org/nlab/show/path+space+object

-/

@[expose] public section

universe v u

open CategoryTheory Category Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

/-- A pre-path object for `A : C` is the data of a morphism
`ι : A ⟶ P` equipped with two retractions. -/
structure PrepathObject (A : C) where
  /-- the underlying object of a (pre)path object -/
  P : C
  /-- the first "projection" from the (pre)path object -/
  p₀ : P ⟶ A
  /-- the second "projection" from the (pre)path object -/
  p₁ : P ⟶ A
  /-- the diagonal of the (pre)path object -/
  ι : A ⟶ P
  ι_p₀ : ι ≫ p₀ = 𝟙 A := by aesop_cat
  ι_p₁ : ι ≫ p₁ = 𝟙 A := by aesop_cat

namespace PrepathObject

attribute [reassoc (attr := simp)] ι_p₀ ι_p₁

variable {A : C} (P : PrepathObject A)

/-- The pre-path object obtained by switching the two projections. -/
@[simps]
def symm : PrepathObject A where
  P := P.P
  p₀ := P.p₁
  p₁ := P.p₀
  ι := P.ι

set_option backward.isDefEq.respectTransparency false in
/-- The gluing of two pre-path objects. -/
@[simps]
noncomputable def trans (P' : PrepathObject A) [HasPullback P.p₁ P'.p₀] :
    PrepathObject A where
  P := pullback P.p₁ P'.p₀
  p₀ := pullback.fst _ _ ≫ P.p₀
  p₁ := pullback.snd _ _ ≫ P'.p₁
  ι := pullback.lift P.ι P'.ι (by simp)

section

variable [HasBinaryProduct A A]

/-- The map from `P.P` to the product of two copies of `A`, when `P` is
a pre-path object for `A`. `P` shall be a *good* path object
when this morphism is a fibration. -/
noncomputable def p : P.P ⟶ A ⨯ A := prod.lift P.p₀ P.p₁

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma p_fst : P.p ≫ prod.fst = P.p₀ := by simp [p]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma p_snd : P.p ≫ prod.snd = P.p₁ := by simp [p]

end

@[simp, reassoc]
lemma symm_p [HasBinaryProducts C] :
    P.symm.p = P.p ≫ (prod.braiding A A).hom := by aesop_cat

end PrepathObject

/-- In a category with weak equivalences, a path object is the
data of a weak equivalence `ι : A ⟶ P` equipped with two retractions. -/
structure PathObject [CategoryWithWeakEquivalences C] (A : C) extends PrepathObject A where
  weakEquivalence_ι : WeakEquivalence ι := by infer_instance

namespace PathObject

attribute [instance] weakEquivalence_ι

section

variable {A : C} [CategoryWithWeakEquivalences C] (P : PathObject A)

set_option backward.defeqAttrib.useBackward true in
/-- The path object obtained by switching the two projections. -/
@[simps!]
def symm : PathObject A where
  __ := P.toPrepathObject.symm
  weakEquivalence_ι := by dsimp; infer_instance

@[simp, reassoc]
lemma symm_p [HasBinaryProducts C] :
    P.symm.p = P.p ≫ (prod.braiding A A).hom :=
  P.toPrepathObject.symm_p

section

variable [(weakEquivalences C).HasTwoOutOfThreeProperty]
  [(weakEquivalences C).ContainsIdentities]

instance : WeakEquivalence P.p₀ :=
  weakEquivalence_of_precomp_of_fac P.ι_p₀

instance : WeakEquivalence P.p₁ :=
  weakEquivalence_of_precomp_of_fac P.ι_p₁

end

/-- A path object `P` is good if the morphism
`P.p : P.P ⟶ A ⨯ A` is a fibration. -/
class IsGood [HasBinaryProduct A A] [CategoryWithFibrations C] : Prop where
  fibration_p : Fibration P.p := by infer_instance

/-- A good path object `P` is very good if `P.ι` is a (trivial) cofibration. -/
class IsVeryGood [HasBinaryProduct A A] [CategoryWithFibrations C]
    [CategoryWithCofibrations C] : Prop extends P.IsGood where
  cofibration_ι : Cofibration P.ι := by infer_instance

attribute [instance] IsGood.fibration_p IsVeryGood.cofibration_ι

section

variable [HasBinaryProduct A A] [CategoryWithFibrations C]
  [HasTerminal C] [(fibrations C).IsStableUnderComposition]
  [(fibrations C).IsStableUnderBaseChange]
  [IsFibrant A] [P.IsGood]

instance : Fibration P.p₀ := by
  rw [← P.p_fst]
  infer_instance

instance : Fibration P.p₁ := by
  rw [← P.p_snd]
  infer_instance

instance : IsFibrant P.P :=
  isFibrant_of_fibration P.p₀

end

set_option backward.isDefEq.respectTransparency false in
instance [HasBinaryProducts C] [CategoryWithFibrations C] [P.IsGood]
    [(fibrations C).RespectsIso] : P.symm.IsGood where
  fibration_p := by
    have hp : fibrations C P.p := by rw [← fibration_iff]; infer_instance
    rw [P.symm_p, fibration_iff]
    refine ((fibrations C).arrow_mk_iso_iff ?_).2 hp
    exact Arrow.isoMk (Iso.refl _) (prod.braiding A A)

section

variable [CategoryWithFibrations C] [CategoryWithCofibrations C]
  [(cofibrations C).IsStableUnderComposition]

instance [HasBinaryProduct A A] [HasInitial C] [IsCofibrant A] [P.IsVeryGood] : IsCofibrant P.P :=
  isCofibrant_of_cofibration P.ι

set_option backward.defeqAttrib.useBackward true in
instance [(fibrations C).RespectsIso] [HasBinaryProducts C] [P.IsVeryGood] :
    P.symm.IsVeryGood where
  cofibration_ι := by dsimp; infer_instance

end

end

variable [ModelCategory C] {A : C} (P : PathObject A)

section

variable (h : MorphismProperty.MapFactorizationData
  (trivialCofibrations C) (fibrations C) (diag A))

set_option backward.isDefEq.respectTransparency false in
/-- A path object for `A` can be obtained from a factorization of the obvious
map `A ⟶ A ⨯ A` as a trivial cofibration followed by a fibration. -/
@[simps]
noncomputable def ofFactorizationData : PathObject A where
  P := h.Z
  p₀ := h.p ≫ prod.fst
  p₁ := h.p ≫ prod.snd
  ι := h.i

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma ofFactorizationData_p : (ofFactorizationData h).p = h.p := by aesop_cat

set_option backward.defeqAttrib.useBackward true in
instance : (ofFactorizationData h).IsVeryGood where
  fibration_p := by simpa using inferInstanceAs (Fibration h.p)
  cofibration_ι := by dsimp; infer_instance

instance [HasInitial C] [IsCofibrant A] [(cofibrations C).IsStableUnderComposition] :
    IsCofibrant (ofFactorizationData h).P :=
  isCofibrant_of_cofibration (ofFactorizationData h).ι

end

variable (A) in
lemma exists_very_good :
    ∃ (P : PathObject A), P.IsVeryGood :=
  ⟨ofFactorizationData (MorphismProperty.factorizationData _ _ _),
    inferInstance⟩

instance : Nonempty (PathObject A) := ⟨(exists_very_good A).choose⟩

set_option backward.defeqAttrib.useBackward true in
/-- The gluing of two good path objects. -/
@[simps!]
noncomputable def trans [IsFibrant A] (P P' : PathObject A) [P'.IsGood] :
    PathObject A where
  __ := P.toPrepathObject.trans P'.toPrepathObject
  weakEquivalence_ι := by
    have : WeakEquivalence (pullback.lift P.ι P'.ι (by simp) ≫
        pullback.fst P.p₁ P'.p₀ ≫ P.p₀) := by
      rw [pullback.lift_fst_assoc, PrepathObject.ι_p₀]
      infer_instance
    dsimp
    apply weakEquivalence_of_postcomp _ (pullback.fst P.p₁ P'.p₀ ≫ P.p₀)

set_option backward.isDefEq.respectTransparency false in
instance [IsFibrant A] (P P' : PathObject A) [P.IsGood] [P'.IsGood] :
    (P.trans P').IsGood where
  fibration_p := by
    let ψ : (P.trans P').P ⟶ P.P ⨯ A := prod.lift (pullback.fst _ _) (pullback.snd _ _ ≫ P'.p₁)
    rw [show (P.trans P').p = ψ ≫ prod.map P.p₀ (𝟙 A) by simp [PrepathObject.p, ψ]]
    have fac : ψ ≫ prod.map P.p₁ (𝟙 A) = pullback.snd _ _ ≫ P'.p := by
      ext
      · simp [ψ, pullback.condition]
      · simp [ψ]
    have sq : IsPullback (ψ ≫ prod.fst) (pullback.snd P.p₁ P'.p₀) P.p₁ (P'.p ≫ prod.fst) := by
      simpa [ψ] using IsPullback.of_hasPullback P.p₁ P'.p₀
    have : Fibration ψ := by
      rw [fibration_iff]
      exact (fibrations C).of_isPullback
        (IsPullback.of_right sq fac (IsPullback.of_prod_fst_with_id P.p₁ A)).flip
          (by rw [← fibration_iff]; infer_instance)
    infer_instance

end PathObject

end HomotopicalAlgebra
