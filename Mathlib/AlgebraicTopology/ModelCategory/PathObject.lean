/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Path objects

We introduce a notion of path object for an object `A : C` in a model category.
It consists of an object `P`, a weak equivalence `σ : P ⟶ A` equipped with two retractions
`p₀` and `p₁`. This notion shall be important in the definition of "right homotopies"
in model categories.

This files dualizes the content of the file `ModelCategory.Cylinder`.

## References
* [Daniel G. Quillen, Homotopical algebra][Quillen1967]
* https://ncatlab.org/nlab/show/cylinder+object

-/

universe v u

open CategoryTheory Category Limits

namespace CategoryTheory

/--
In a category, given a morphism `f : A ⟶ B` and an object `X`,
this is the obvious pullback diagram:
```
A ⨯ X ⟶ A
|       |
v       v
B ⨯ X ⟶ B
```
-/
lemma IsPullback.of_prod_fst_with_ind {C : Type*} [Category C]
    {A B : C} (f : A ⟶ B) (X : C) [HasBinaryProduct A X]
    [HasBinaryProduct B X] :
    IsPullback prod.fst (prod.map f (𝟙 X)) f prod.fst where
  w := by simp
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun s ↦ by
    refine ⟨prod.lift s.fst (s.snd ≫ prod.snd), ?_, ?_, ?_⟩
    · simp
    · ext
      · simp [PullbackCone.condition]
      · simp
    · intro m h₁ h₂
      dsimp at m h₁ h₂ ⊢
      ext
      · simpa using h₁
      · simp [← h₂])⟩

end CategoryTheory

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- In a model category `C`, a cylinder for `A : C` is the data of
a weak equivalence `σ : I ⟶ A` equipped with two sections. -/
structure PathObject (A : C) where
  /-- the underlying object of a path object -/
  P : C
  /-- the first "projection" from the path object -/
  p₀ : P ⟶ A
  /-- the second "projection" from the path object -/
  p₁ : P ⟶ A
  /-- the weak equivalence of the path object -/
  ι : A ⟶ P
  ι_p₀ : ι ≫ p₀ = 𝟙 A := by aesop_cat
  ι_p₁ : ι ≫ p₁ = 𝟙 A := by aesop_cat
  weakEquivalence_ι : WeakEquivalence ι := by infer_instance

namespace PathObject

attribute [instance] weakEquivalence_ι
attribute [reassoc (attr := simp)] ι_p₀ ι_p₁

variable {A : C} (P : PathObject A)

instance : WeakEquivalence P.p₀ :=
  weakEquivalence_of_precomp_of_fac P.ι_p₀

instance : WeakEquivalence P.p₁ :=
  weakEquivalence_of_precomp_of_fac P.ι_p₁

/-- the map from `P.P` to the product of two copies of `A`, when `P` is
a path object object for `A`. `P` shall be a *good* path object
when this morphism is a fibration. -/
noncomputable def p : P.P ⟶ A ⨯ A := prod.lift P.p₀ P.p₁

@[reassoc (attr := simp)]
lemma p_fst : P.p ≫ prod.fst = P.p₀ := by simp [p]

@[reassoc (attr := simp)]
lemma p_snd : P.p ≫ prod.snd = P.p₁ := by simp [p]

/-- The cylinder object obtained by switching the two inclusions. -/
@[simps]
def symm : PathObject A where
  P := P.P
  p₀ := P.p₁
  p₁ := P.p₀
  ι := P.ι

@[simp, reassoc]
lemma symm_p : P.symm.p =
  P.p ≫ (prod.braiding A A).hom := by aesop_cat

/-- A path object `P` is good if the morphism
`P.p : P.P ⟶ A ⨯ A` is a fibration. -/
class IsGood : Prop where
  fibration_p : Fibration P.p := by infer_instance

/-- A good path object `P` is very good if `P.ι` is a (trivial) cofibration. -/
class IsVeryGood : Prop extends P.IsGood where
  cofibration_ι : Cofibration P.ι := by infer_instance

attribute [instance] IsGood.fibration_p IsVeryGood.cofibration_ι

instance [IsFibrant A] [P.IsGood] : Fibration P.p₀ := by
  rw [← P.p_fst]
  infer_instance

instance [IsFibrant A] [P.IsGood] : Fibration P.p₁ := by
  rw [← P.p_snd]
  infer_instance

instance [IsFibrant A] [P.IsGood] : IsFibrant P.P :=
  isFibrant_of_fibration P.p₀

instance [P.IsGood] : P.symm.IsGood where
  fibration_p := by
    dsimp
    rw [symm_p]
    infer_instance

instance [P.IsVeryGood] : P.symm.IsVeryGood where
  cofibration_ι := by
    dsimp
    infer_instance

section

variable (h : MorphismProperty.MapFactorizationData (trivialCofibrations C) (fibrations C)
    (prod.lift (𝟙 A) (𝟙 A)))

/-- A path object for `A` can be obtained from a factorization of the obvious
map `A ⟶ A ⨯ A` as a trivial cofibration followed by a fibration. -/
@[simps]
noncomputable def ofFactorizationData : PathObject A where
  P := h.Z
  p₀ := h.p ≫ prod.fst
  p₁ := h.p ≫ prod.snd
  ι := h.i

@[simp]
lemma ofFactorizationData_p : (ofFactorizationData h).p = h.p := by aesop_cat

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

/-- The gluing of two good path objects. -/
@[simps]
noncomputable def trans [IsFibrant A] (P P' : PathObject A) [P'.IsGood] :
    PathObject A where
  P := pullback P.p₁ P'.p₀
  p₀ := pullback.fst _ _ ≫ P.p₀
  p₁ := pullback.snd _ _ ≫ P'.p₁
  ι := pullback.lift P.ι P'.ι (by simp)
  weakEquivalence_ι := by
    have : WeakEquivalence (pullback.lift P.ι P'.ι (by simp) ≫ pullback.fst P.p₁ P'.p₀ ≫ P.p₀) := by
      rw [pullback.lift_fst_assoc, ι_p₀]
      infer_instance
    apply weakEquivalence_of_postcomp _ (pullback.fst _ _ ≫ P.p₀)

instance [IsFibrant A] (P P' : PathObject A) [P.IsGood] [P'.IsGood] :
    (P.trans P').IsGood where
  fibration_p := by
    let ψ : (P.trans P').P ⟶ P.P ⨯ A := prod.lift (pullback.fst _ _) (pullback.snd _ _ ≫ P'.p₁)
    rw [show (P.trans P').p = ψ ≫ prod.map P.p₀ (𝟙 A) by simp [PathObject.p, ψ]]
    have fac : ψ ≫ prod.map P.p₁ (𝟙 A) = pullback.snd _ _ ≫ P'.p := by
      ext
      · simp [ψ, pullback.condition]
      · simp [ψ]
    have sq : IsPullback (ψ ≫ prod.fst) (pullback.snd _ _) P.p₁ (P'.p ≫ prod.fst) := by
      simpa [ψ] using IsPullback.of_hasPullback P.p₁ P'.p₀
    have : Fibration ψ := by
      rw [fibration_iff]
      exact (fibrations C).of_isPullback (IsPullback.of_right sq fac
        (IsPullback.of_prod_fst_with_ind P.p₁ A)).flip
        (by rw [← fibration_iff]; infer_instance)
    infer_instance

end PathObject

end HomotopicalAlgebra
