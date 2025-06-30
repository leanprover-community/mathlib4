/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Cylinders

We introduce a notion of cylinder for an object `A : C` in a model category.
It consists of an object `I`, a weak equivalence `σ : I ⟶ A` equipped with two sections
`i₀` and `i₁`. This notion shall be important in the definition of "left homotopies"
in model categories.

## References
* [Daniel G. Quillen, Homotopical algebra][Quillen1967]
* https://ncatlab.org/nlab/show/cylinder+object

-/

universe v u

open CategoryTheory Category Limits

namespace CategoryTheory

/--
In a category, given a morphism `f : A ⟶ B` and an object `X`,
this is the obvious pushout diagram:
```
A ⟶ A ⨿ X
|     |
v     v
B ⟶ B ⨿ X
```
-/
lemma IsPushout.of_coprod_inl_with_id {C : Type*} [Category C]
    {A B : C} (f : A ⟶ B) (X : C) [HasBinaryCoproduct A X]
    [HasBinaryCoproduct B X] :
    IsPushout coprod.inl f (coprod.map f (𝟙 X)) coprod.inl where
  w := by simp
  isColimit' := ⟨PushoutCocone.isColimitAux' _ (fun s ↦ by
    refine ⟨coprod.desc s.inr (coprod.inr ≫ s.inl), ?_, ?_, ?_⟩
    · ext
      · simp [PushoutCocone.condition]
      · simp
    · simp
    · intro m h₁ h₂
      dsimp at m h₁ h₂ ⊢
      ext
      · simpa using h₂
      · simp [← h₁])⟩

end CategoryTheory

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- In a model category `C`, a cylinder for `A : C` is the data of
a weak equivalence `σ : I ⟶ A` equipped with two sections. -/
structure Cylinder (A : C) where
  /-- the underlying object of a cylinder -/
  I : C
  /-- the first "inclusion" in the cylinder -/
  i₀ : A ⟶ I
  /-- the second "inclusion" in the cylinder -/
  i₁ : A ⟶ I
  /-- the weak equivalence of the cylinder -/
  π : I ⟶ A
  i₀_π : i₀ ≫ π = 𝟙 A := by aesop_cat
  i₁_π : i₁ ≫ π = 𝟙 A := by aesop_cat
  weakEquivalence_π : WeakEquivalence π := by infer_instance

namespace Cylinder

attribute [instance] weakEquivalence_π
attribute [reassoc (attr := simp)] i₀_π i₁_π

variable {A : C} (P : Cylinder A)

instance : WeakEquivalence P.i₀ :=
  weakEquivalence_of_postcomp_of_fac P.i₀_π

instance : WeakEquivalence P.i₁ :=
  weakEquivalence_of_postcomp_of_fac P.i₁_π

/-- the map from the coproduct of two copies of `A` to `P.I`, when `P` is
a cylinder object for `A`. `P` shall be a *good* cylinder object
when this morphism is a cofibration. -/
noncomputable def i : A ⨿ A ⟶ P.I := coprod.desc P.i₀ P.i₁

@[reassoc (attr := simp)]
lemma inl_i : coprod.inl ≫ P.i = P.i₀ := by simp [i]

@[reassoc (attr := simp)]
lemma inr_i : coprod.inr ≫ P.i = P.i₁ := by simp [i]

/-- The cylinder object obtained by switching the two inclusions. -/
@[simps]
def symm : Cylinder A where
  I := P.I
  i₀ := P.i₁
  i₁ := P.i₀
  π := P.π

@[simp, reassoc]
lemma symm_i : P.symm.i =
  (coprod.braiding A A).hom ≫ P.i := by aesop_cat

/-- A cylinder object `P` is good if the morphism
`P.i : A ⨿ A ⟶ P.I` is a cofibration. -/
class IsGood : Prop where
  cofibration_i : Cofibration P.i := by infer_instance

/-- A good cylinder object `P` is very good if `P.π` is a (trivial) fibration. -/
class IsVeryGood : Prop extends P.IsGood where
  fibration_π : Fibration P.π := by infer_instance

attribute [instance] IsGood.cofibration_i IsVeryGood.fibration_π

instance [IsCofibrant A] [P.IsGood] : Cofibration P.i₀ := by
  rw [← P.inl_i]
  infer_instance

instance [IsCofibrant A] [P.IsGood] : Cofibration P.i₁ := by
  rw [← P.inr_i]
  infer_instance

instance [IsCofibrant A] [P.IsGood] : IsCofibrant P.I :=
  isCofibrant_of_cofibration P.i₀

instance [IsFibrant A] [P.IsVeryGood] : IsFibrant P.I :=
  isFibrant_of_fibration P.π

instance [P.IsGood] : P.symm.IsGood where
  cofibration_i := by
    dsimp
    rw [symm_i]
    infer_instance

instance [P.IsVeryGood] : P.symm.IsVeryGood where
  fibration_π := by
    dsimp
    infer_instance

section

variable (h : MorphismProperty.MapFactorizationData (cofibrations C) (trivialFibrations C)
    (coprod.desc (𝟙 A) (𝟙 A)))

/-- A cylinder object for `A` can be obtained from a factorization of the obvious
map `A ⨿ A ⟶ A` as a cofibration followed by a trivial fibration. -/
@[simps]
noncomputable def ofFactorizationData : Cylinder A where
  I := h.Z
  i₀ := coprod.inl ≫ h.i
  i₁ := coprod.inr ≫ h.i
  π := h.p

@[simp]
lemma ofFactorizationData_i : (ofFactorizationData h).i = h.i := by aesop_cat

instance : (ofFactorizationData h).IsVeryGood where
  cofibration_i := by simpa using inferInstanceAs (Cofibration h.i)
  fibration_π := by dsimp; infer_instance

instance [HasTerminal C] [IsFibrant A] [(fibrations C).IsStableUnderComposition] :
    IsFibrant (ofFactorizationData h).I :=
  isFibrant_of_fibration (ofFactorizationData h).π

end

variable (A) in
lemma exists_very_good :
    ∃ (P : Cylinder A), P.IsVeryGood :=
  ⟨ofFactorizationData (MorphismProperty.factorizationData _ _ _),
    inferInstance⟩

instance : Nonempty (Cylinder A) := ⟨(exists_very_good A).choose⟩

/-- The gluing of two good cylinders. -/
@[simps]
noncomputable def trans [IsCofibrant A] (P P' : Cylinder A) [P'.IsGood] :
    Cylinder A where
  I := pushout P.i₁ P'.i₀
  i₀ := P.i₀ ≫ pushout.inl _ _
  i₁ := P'.i₁ ≫ pushout.inr _ _
  π := pushout.desc P.π P'.π (by simp)
  weakEquivalence_π := by
    have : WeakEquivalence ((P.i₀ ≫ pushout.inl P.i₁ P'.i₀) ≫
        pushout.desc P.π P'.π (by simp)) := by
      simp only [assoc, colimit.ι_desc, PushoutCocone.mk_ι_app,
        Cylinder.i₀_π]
      infer_instance
    apply weakEquivalence_of_precomp (P.i₀ ≫ pushout.inl _ _)

instance [IsCofibrant A] (P P' : Cylinder A) [P.IsGood] [P'.IsGood] :
    (P.trans P').IsGood where
  cofibration_i := by
    let ψ : P.I ⨿ A ⟶ (P.trans P').I := coprod.desc (pushout.inl _ _) (P'.i₁ ≫ pushout.inr _ _)
    rw [show (P.trans P').i = coprod.map P.i₀ (𝟙 A) ≫ ψ by simp [Cylinder.i, ψ]]
    have fac : coprod.map P.i₁ (𝟙 A) ≫ ψ = P'.i ≫ pushout.inr _ _ := by
      ext
      · simp [ψ, pushout.condition]
      · simp [ψ]
    have sq : IsPushout P.i₁ (coprod.inl ≫ P'.i) (coprod.inl ≫ ψ) (pushout.inr _ _) := by
      simpa [ψ] using IsPushout.of_hasPushout P.i₁ P'.i₀
    have : Cofibration ψ := by
      rw [cofibration_iff]
      exact (cofibrations C).of_isPushout
        (IsPushout.of_top sq fac (IsPushout.of_coprod_inl_with_id P.i₁ A).flip)
        (by rw [← cofibration_iff]; infer_instance)
    infer_instance

end Cylinder

end HomotopicalAlgebra
