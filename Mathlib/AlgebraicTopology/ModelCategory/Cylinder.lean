/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.AlgebraicTopology.ModelCategory.IsFibrant

/-!
# Cylinders

We first introduce a notion of "precylinder" for an object `A : C` in a model category.
It consists of an object `I`, a weak equivalence `σ : I ⟶ A` equipped with two sections
`i₀` and `i₁`. When the morphism `A ⨿ A ⟶ I` induced by both sections is a cofibration,
we say that this is a cylinder object for `A`. These notions shall be important in
the definition of "left homotopies" in model categories.

## References
* [Daniel G. Quillen, Homotopical algebra][Quillen1967]

-/

universe v u

open CategoryTheory Category Limits

namespace CategoryTheory

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

/-- In a model category `C`, a precylinder for `A : C` is the data of
a weak equivalence `σ : I ⟶ A` equipped with two sections. `-/
structure Precylinder (A : C) where
  /-- the underlying object of a precylinder -/
  I : C
  /-- the first "inclusion" in the precylinder -/
  i₀ : A ⟶ I
  /-- the second "inclusion" in the precylinder -/
  i₁ : A ⟶ I
  /-- the weak equivalence of the precylinder -/
  σ : I ⟶ A
  i₀_σ : i₀ ≫ σ = 𝟙 A := by aesop_cat
  i₁_σ : i₁ ≫ σ = 𝟙 A := by aesop_cat
  weakEquivalence_σ : WeakEquivalence σ := by infer_instance

namespace Precylinder

attribute [instance] weakEquivalence_σ
attribute [reassoc (attr := simp)] i₀_σ i₁_σ

variable {A : C} (P : Precylinder A)

instance : WeakEquivalence P.i₀ :=
  weakEquivalence_of_postcomp_of_fac (P.i₀_σ)

instance : WeakEquivalence P.i₁ :=
  weakEquivalence_of_postcomp_of_fac (P.i₁_σ)

/-- the map from the coproduct of two copies of `A` to `P.I`, when `P` is a precylinder
object for `A`. `P` shall be a cylinder object when this morphism is a cofibration. -/
noncomputable def i : A ⨿ A ⟶ P.I := coprod.desc P.i₀ P.i₁

@[reassoc (attr := simp)]
lemma inl_i : coprod.inl ≫ P.i = P.i₀ := by simp [i]

@[reassoc (attr := simp)]
lemma inr_i : coprod.inr ≫ P.i = P.i₁ := by simp [i]

/-- The precylinder object obtained by switching the two inclusions. -/
@[simps]
def symm : Precylinder A where
  I := P.I
  i₀ := P.i₁
  i₁ := P.i₀
  σ := P.σ

@[simp, reassoc]
lemma symm_i [HasBinaryCoproducts C] : P.symm.i =
  (coprod.braiding A A).hom ≫ P.i := by aesop_cat

end Precylinder

/-- A cylinder object for `A` is a precylinder object `P` such that the
morphism `P.i : A ⨿ A ⟶ P.I` is a cofibration. -/
structure Cylinder (A : C) extends Precylinder A where
  cofibration_i : Cofibration toPrecylinder.i := by infer_instance

namespace Cylinder

attribute [instance] cofibration_i

variable {A : C}

/-- The cylinder object obtained by switching the two inclusions. -/
def symm (P : Cylinder A) : Cylinder A where
  toPrecylinder := P.toPrecylinder.symm
  cofibration_i := by
    dsimp
    rw [Precylinder.symm_i]
    infer_instance

instance [IsCofibrant A] (P : Cylinder A) : Cofibration P.i₀ := by
  rw [← P.inl_i]
  infer_instance

instance [IsCofibrant A] (P : Cylinder A) : Cofibration P.i₁ := by
  rw [← P.inr_i]
  infer_instance

instance [IsCofibrant A] (P : Cylinder A) : IsCofibrant P.I :=
  isCofibrant_of_cofibration P.i₀

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
  σ := h.p
  cofibration_i := by
    convert inferInstanceAs (Cofibration h.i)
    aesop_cat

@[simp]
lemma ofFactorizationData_i : (ofFactorizationData h).i = h.i := by aesop_cat

@[simp]
lemma ofFactorizationData_p : (ofFactorizationData h).σ = h.p := rfl

instance : Fibration (ofFactorizationData h).σ := by
  dsimp
  infer_instance

instance [HasTerminal C] [IsFibrant A] [(fibrations C).IsStableUnderComposition] :
    IsFibrant (ofFactorizationData h).I :=
  isFibrant_of_fibration (ofFactorizationData h).σ

end

instance : Nonempty (Cylinder A) :=
  ⟨ofFactorizationData (MorphismProperty.factorizationData _ _ _)⟩

/-- The gluing of two cylinders. -/
@[simps]
noncomputable def trans [IsCofibrant A] (P P' : Cylinder A) : Cylinder A := by
  let Q : Precylinder A :=
    { I := pushout P.i₁ P'.i₀
      i₀ := P.i₀ ≫ pushout.inl _ _
      i₁ := P'.i₁ ≫ pushout.inr _ _
      σ := pushout.desc P.σ P'.σ (by simp)
      weakEquivalence_σ := by
        have : WeakEquivalence ((P.i₀ ≫ pushout.inl P.i₁ P'.i₀) ≫
            pushout.desc P.σ P'.σ (by simp)) := by
          simp only [assoc, colimit.ι_desc, PushoutCocone.mk_ι_app,
            Precylinder.i₀_σ]
          infer_instance
        apply weakEquivalence_of_precomp (P.i₀ ≫ pushout.inl _ _) }
  have : Cofibration Q.i := by
    let ψ : P.I ⨿ A ⟶ Q.I := coprod.desc (pushout.inl _ _) (P'.i₁ ≫ pushout.inr _ _)
    rw [show Q.i = coprod.map P.i₀ (𝟙 A) ≫ ψ by simp [Precylinder.i, ψ, Q]]
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
  exact { toPrecylinder := Q }

end Cylinder

end HomotopicalAlgebra
