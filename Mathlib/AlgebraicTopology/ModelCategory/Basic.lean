/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Factorization
import Mathlib.CategoryTheory.MorphismProperty.RetractArgument
import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations

/-!
# Model categories

We introduce a typeclass `ModelCategory C` expressing that `C` is equipped with
classes of morphisms named "fibrations", "cofibrations" and "weak equivalences"
with satisfy the axioms of (closed) model categories.

As a given category `C` may have several model category structures, it is advisable
to define only local instances of `ModelCategory`, or to set these instances on type synonyms.

## References
* [Daniel G. Quillen, Homotopical algebra][Quillen1967]
* [Paul G. Goerss, John F. Jardine, Simplicial Homotopy Theory][goerss-jardine-2009]

-/

universe w v u

namespace HomotopicalAlgebra

open CategoryTheory Limits

variable (C : Type u) [Category.{v} C]

/-- A model category is a category equipped with classes of morphisms named cofibrations,
fibrations and weak equivalences which satisfies the axioms CM1/CM2/CM3/CM4/CM5
of (closed) model categories. -/
class ModelCategory where
  categoryWithFibrations : CategoryWithFibrations C := by infer_instance
  categoryWithCofibrations : CategoryWithCofibrations C := by infer_instance
  categoryWithWeakEquivalences : CategoryWithWeakEquivalences C := by infer_instance
  cm1a : HasFiniteLimits C := by infer_instance
  cm1b : HasFiniteColimits C := by infer_instance
  cm2 : (weakEquivalences C).HasTwoOutOfThreeProperty := by infer_instance
  cm3a : (weakEquivalences C).IsStableUnderRetracts := by infer_instance
  cm3b : (fibrations C).IsStableUnderRetracts := by infer_instance
  cm3c : (cofibrations C).IsStableUnderRetracts := by infer_instance
  cm4a {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) [Cofibration i] [WeakEquivalence i] [Fibration p] :
      HasLiftingProperty i p := by intros; infer_instance
  cm4b {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) [Cofibration i] [Fibration p] [WeakEquivalence p] :
      HasLiftingProperty i p := by intros; infer_instance
  cm5a : MorphismProperty.HasFactorization (trivialCofibrations C) (fibrations C) := by
    infer_instance
  cm5b : MorphismProperty.HasFactorization (cofibrations C) (trivialFibrations C) := by
    infer_instance

namespace ModelCategory

attribute [instance] categoryWithFibrations categoryWithCofibrations categoryWithWeakEquivalences
  cm1a cm1b cm2 cm3a cm3b cm3c cm4a cm4b cm5a cm5b

variable [ModelCategory C]

instance : (trivialCofibrations C).IsStableUnderRetracts := by
  dsimp [trivialCofibrations]
  infer_instance

instance : (trivialFibrations C).IsStableUnderRetracts := by
  dsimp [trivialFibrations]
  infer_instance

lemma fibrations_llp :
    (fibrations C).llp = trivialCofibrations C := by
  apply MorphismProperty.llp_eq_of_le_llp_of_hasFactorization_of_isStableUnderRetracts
  intro A B i hi X Y p hp
  rw [mem_trivialCofibrations_iff] at hi
  rw [← fibration_iff] at hp
  have := hi.1
  have := hi.2
  infer_instance

lemma trivialCofibrations_rlp :
    (trivialCofibrations C).rlp = fibrations C := by
  apply MorphismProperty.rlp_eq_of_le_rlp_of_hasFactorization_of_isStableUnderRetracts
  rw [← MorphismProperty.le_llp_iff_le_rlp, fibrations_llp]

lemma trivialFibrations_llp :
    (trivialFibrations C).llp = cofibrations C := by
  apply MorphismProperty.llp_eq_of_le_llp_of_hasFactorization_of_isStableUnderRetracts
  intro A B i hi X Y p hp
  rw [mem_trivialFibrations_iff] at hp
  rw [← cofibration_iff] at hi
  have := hp.1
  have := hp.2
  infer_instance

lemma cofibrations_rlp :
    (cofibrations C).rlp = trivialFibrations C := by
  apply MorphismProperty.rlp_eq_of_le_rlp_of_hasFactorization_of_isStableUnderRetracts
  rw [← MorphismProperty.le_llp_iff_le_rlp, trivialFibrations_llp]

section Pullbacks

instance : (cofibrations C).IsStableUnderCobaseChange := by
  rw [← trivialFibrations_llp]
  infer_instance

instance : (fibrations C).IsStableUnderBaseChange := by
  rw [← trivialCofibrations_rlp]
  infer_instance

instance : (trivialCofibrations C).IsStableUnderCobaseChange := by
  rw [← fibrations_llp]
  infer_instance

instance : (trivialFibrations C).IsStableUnderBaseChange := by
  rw [← cofibrations_rlp]
  infer_instance

section

variable {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)

instance [hg : Cofibration g] : Cofibration (pushout.inl f g) := by
  rw [cofibration_iff] at hg ⊢
  exact MorphismProperty.of_isPushout (IsPushout.of_hasPushout f g) hg

instance [hf : Cofibration f] : Cofibration (pushout.inr f g) := by
  rw [cofibration_iff] at hf ⊢
  exact MorphismProperty.of_isPushout (IsPushout.of_hasPushout f g).flip hf

instance [Cofibration g] [WeakEquivalence g] : WeakEquivalence (pushout.inl f g) := by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.of_isPushout (IsPushout.of_hasPushout f g)
    (mem_trivialCofibrations g)).2

instance [Cofibration f] [WeakEquivalence f] : WeakEquivalence (pushout.inr f g) := by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.of_isPushout (IsPushout.of_hasPushout f g).flip
    (mem_trivialCofibrations f)).2

end

section

variable {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)

instance [hf : Fibration f] : Fibration (pullback.snd f g) := by
  rw [fibration_iff] at hf ⊢
  exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g) hf

instance [hg : Fibration g] : Fibration (pullback.fst f g) := by
  rw [fibration_iff] at hg ⊢
  exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g).flip hg

instance [Fibration f] [WeakEquivalence f] : WeakEquivalence (pullback.snd f g) := by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g)
    (mem_trivialFibrations f)).2

instance [Fibration g] [WeakEquivalence g] : WeakEquivalence (pullback.fst f g) := by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g).flip
    (mem_trivialFibrations g)).2

end

end Pullbacks

section Products

variable (J : Type w)

lemma cofibrations_isStableUnderCoproductsOfShape :
    (cofibrations C).IsStableUnderCoproductsOfShape J := by
  rw [← trivialFibrations_llp]
  apply MorphismProperty.llp_IsStableUnderCoproductsOfShape

lemma trivialCofibrations_isStableUnderCoproductsOfShape :
    (trivialCofibrations C).IsStableUnderCoproductsOfShape J := by
  rw [← fibrations_llp]
  apply MorphismProperty.llp_IsStableUnderCoproductsOfShape

lemma fibrations_isStableUnderProductsOfShape :
    (fibrations C).IsStableUnderProductsOfShape J := by
  rw [← trivialCofibrations_rlp]
  apply MorphismProperty.rlp_IsStableUnderProductsOfShape

lemma trivialFibrations_isStableUnderProductsOfShape :
    (trivialFibrations C).IsStableUnderProductsOfShape J := by
  rw [← cofibrations_rlp]
  apply MorphismProperty.rlp_IsStableUnderProductsOfShape

variable {C J} {X Y : J → C} (f : ∀ i, X i ⟶ Y i)

section

variable [HasCoproduct X] [HasCoproduct Y] [h : ∀ i, Cofibration (f i)]

instance : Cofibration (Limits.Sigma.map f) := by
  simp only [cofibration_iff] at h ⊢
  exact (cofibrations_isStableUnderCoproductsOfShape C J).colimMap _ (fun ⟨i⟩ ↦ h i)

instance [∀ i, WeakEquivalence (f i)] :
    WeakEquivalence (Limits.Sigma.map f) := by
  rw [weakEquivalence_iff]
  exact ((trivialCofibrations_isStableUnderCoproductsOfShape C J).colimMap _
    (fun ⟨i⟩ ↦ mem_trivialCofibrations (f i))).2

end

section

variable [HasProduct X] [HasProduct Y] [h : ∀ i, Fibration (f i)]

instance : Fibration (Limits.Pi.map f) := by
  simp only [fibration_iff] at h ⊢
  exact (fibrations_isStableUnderProductsOfShape C J).limMap _ (fun ⟨i⟩ ↦ h i)

instance [∀ i, WeakEquivalence (f i)] :
    WeakEquivalence (Limits.Pi.map f) := by
  rw [weakEquivalence_iff]
  exact ((trivialFibrations_isStableUnderProductsOfShape C J).limMap _
    (fun ⟨i⟩ ↦ mem_trivialFibrations (f i))).2

end

end Products

section BinaryProducts

variable {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)

instance [h₁ : Cofibration f₁] [h₂ : Cofibration f₂] : Cofibration (coprod.map f₁ f₂) := by
  rw [cofibration_iff] at h₁ h₂ ⊢
  apply (cofibrations_isStableUnderCoproductsOfShape C WalkingPair).colimMap
  rintro (_ | _) <;> assumption

instance [h₁ : Fibration f₁] [h₂ : Fibration f₂] : Fibration (prod.map f₁ f₂) := by
  rw [fibration_iff] at h₁ h₂ ⊢
  apply (fibrations_isStableUnderProductsOfShape C WalkingPair).limMap
  rintro (_ | _) <;> assumption

end BinaryProducts

section IsMultiplicative

instance : (cofibrations C).IsMultiplicative := by
  rw [← trivialFibrations_llp]
  infer_instance

instance : (fibrations C).IsMultiplicative := by
  rw [← trivialCofibrations_rlp]
  infer_instance

instance : (trivialCofibrations C).IsMultiplicative := by
  rw [← fibrations_llp]
  infer_instance

instance : (trivialFibrations C).IsMultiplicative := by
  rw [← cofibrations_rlp]
  infer_instance

variable {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

instance [hf : Cofibration f] [hg : Cofibration g] : Cofibration (f ≫ g) := by
  rw [cofibration_iff] at hf hg ⊢
  apply MorphismProperty.comp_mem <;> assumption

instance [hf : Fibration f] [hg : Fibration g] : Fibration (f ≫ g) := by
  rw [fibration_iff] at hf hg ⊢
  apply MorphismProperty.comp_mem <;> assumption

instance [hf : WeakEquivalence f] [hg : WeakEquivalence g] : WeakEquivalence (f ≫ g) := by
  rw [weakEquivalence_iff] at hf hg ⊢
  apply MorphismProperty.comp_mem <;> assumption

end IsMultiplicative

section IsIso

variable {X Y : C} (f : X ⟶ Y)

instance [IsIso f] : Cofibration f := by
  have := (fibrations C).llp_of_isIso f
  rw [fibrations_llp] at this
  simpa only [cofibration_iff] using this.1

instance [IsIso f] : Fibration f := by
  have := (cofibrations C).rlp_of_isIso f
  rw [cofibrations_rlp] at this
  simpa only [fibration_iff] using this.1

instance [IsIso f] : WeakEquivalence f := by
  have h := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C) f
  rw [weakEquivalence_iff]
  exact MorphismProperty.of_retract (RetractArrow.ofLeftLiftingProperty h.fac) h.hi.2

end IsIso

instance : (weakEquivalences C).IsMultiplicative where
  id_mem _ := by
    rw [← weakEquivalence_iff]
    infer_instance

instance : (weakEquivalences C).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition (fun _ _ _ (_ : IsIso _) ↦ by
    rw [← weakEquivalence_iff]
    infer_instance)

end ModelCategory

end HomotopicalAlgebra
