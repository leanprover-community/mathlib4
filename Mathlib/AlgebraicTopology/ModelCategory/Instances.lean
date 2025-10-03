/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem
import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations

/-!
# Consequences of model category axioms

In this file, we deduce basic properties of fibrations, cofibrations,
and weak equivalences from the axioms of model categories.

-/


universe w v u

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable (C : Type u) [Category.{v} C]

instance [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C]
    [(cofibrations C).IsStableUnderRetracts]
    [(weakEquivalences C).IsStableUnderRetracts] :
    (trivialCofibrations C).IsStableUnderRetracts := by
  dsimp [trivialCofibrations]
  infer_instance

instance [CategoryWithWeakEquivalences C] [CategoryWithFibrations C]
    [(fibrations C).IsStableUnderRetracts]
    [(weakEquivalences C).IsStableUnderRetracts] :
    (trivialFibrations C).IsStableUnderRetracts := by
  dsimp [trivialFibrations]
  infer_instance

section IsStableUnderComposition

variable {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

instance [CategoryWithCofibrations C] [(cofibrations C).IsStableUnderComposition]
    [hf : Cofibration f] [hg : Cofibration g] : Cofibration (f ≫ g) :=
  (cofibration_iff _).2 ((cofibrations C).comp_mem _ _ hf.mem hg.mem)

instance [CategoryWithFibrations C] [(fibrations C).IsStableUnderComposition]
    [hf : Fibration f] [hg : Fibration g] : Fibration (f ≫ g) :=
  (fibration_iff _).2 ((fibrations C).comp_mem _ _ hf.mem hg.mem)

instance [CategoryWithWeakEquivalences C] [(weakEquivalences C).IsStableUnderComposition]
    [hf : WeakEquivalence f] [hg : WeakEquivalence g] : WeakEquivalence (f ≫ g) :=
  (weakEquivalence_iff _).2 ((weakEquivalences C).comp_mem _ _ hf.mem hg.mem)

end IsStableUnderComposition

variable [CategoryWithWeakEquivalences C]

section HasTwoOutOfThreeProperty

variable [(weakEquivalences C).HasTwoOutOfThreeProperty]
  {C} {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

lemma weakEquivalence_of_postcomp
    [hg : WeakEquivalence g] [hfg : WeakEquivalence (f ≫ g)] :
    WeakEquivalence f := by
  rw [weakEquivalence_iff] at hg hfg ⊢
  exact of_postcomp _ _ _ hg hfg

lemma weakEquivalence_of_precomp
    [hf : WeakEquivalence f] [hfg : WeakEquivalence (f ≫ g)] :
    WeakEquivalence g := by
  rw [weakEquivalence_iff] at hf hfg ⊢
  exact of_precomp _ _ _ hf hfg

lemma weakEquivalence_postcomp_iff [WeakEquivalence g] :
    WeakEquivalence (f ≫ g) ↔ WeakEquivalence f :=
  ⟨fun _ ↦ weakEquivalence_of_postcomp f g, fun _ ↦ inferInstance⟩

lemma weakEquivalence_precomp_iff [WeakEquivalence f] :
    WeakEquivalence (f ≫ g) ↔ WeakEquivalence g :=
  ⟨fun _ ↦ weakEquivalence_of_precomp f g, fun _ ↦ inferInstance⟩

variable {f g} {fg : X ⟶ Z}

lemma weakEquivalence_of_postcomp_of_fac (fac : f ≫ g = fg)
    [WeakEquivalence g] [hfg : WeakEquivalence fg] :
    WeakEquivalence f := by
  subst fac
  exact weakEquivalence_of_postcomp f g

lemma weakEquivalence_of_precomp_of_fac (fac : f ≫ g = fg)
    [WeakEquivalence f] [WeakEquivalence fg] :
    WeakEquivalence g := by
  subst fac
  exact weakEquivalence_of_precomp f g

end HasTwoOutOfThreeProperty

variable [CategoryWithCofibrations C] [CategoryWithFibrations C]

section

variable [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)]

lemma fibrations_llp :
    (fibrations C).llp = trivialCofibrations C :=
  llp_eq_of_wfs _ _

lemma trivialCofibrations_rlp :
    (trivialCofibrations C).rlp = fibrations C :=
  rlp_eq_of_wfs _ _

instance : (trivialCofibrations C).IsStableUnderCobaseChange := by
  rw [← fibrations_llp]
  infer_instance

instance : (fibrations C).IsStableUnderBaseChange := by
  rw [← trivialCofibrations_rlp]
  infer_instance

instance : (trivialCofibrations C).IsMultiplicative := by
  rw [← fibrations_llp]
  infer_instance

instance : (fibrations C).IsMultiplicative := by
  rw [← trivialCofibrations_rlp]
  infer_instance

variable (J : Type w)

instance isStableUnderCoproductsOfShape_trivialCofibrations :
    (trivialCofibrations C).IsStableUnderCoproductsOfShape J := by
  rw [← fibrations_llp]
  apply MorphismProperty.llp_isStableUnderCoproductsOfShape

instance isStableUnderProductsOfShape_fibrations :
    (fibrations C).IsStableUnderProductsOfShape J := by
  rw [← trivialCofibrations_rlp]
  apply MorphismProperty.rlp_isStableUnderProductsOfShape

end

section

variable [IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C)]

lemma trivialFibrations_llp :
    (trivialFibrations C).llp = cofibrations C :=
  llp_eq_of_wfs _ _

lemma cofibrations_rlp :
    (cofibrations C).rlp = trivialFibrations C :=
  rlp_eq_of_wfs _ _

instance : (cofibrations C).IsStableUnderCobaseChange := by
  rw [← trivialFibrations_llp]
  infer_instance

instance : (trivialFibrations C).IsStableUnderBaseChange := by
  rw [← cofibrations_rlp]
  infer_instance

instance : (cofibrations C).IsMultiplicative := by
  rw [← trivialFibrations_llp]
  infer_instance

instance : (trivialFibrations C).IsMultiplicative := by
  rw [← cofibrations_rlp]
  infer_instance


variable (J : Type w)

instance isStableUnderCoproductsOfShape_cofibrations :
    (cofibrations C).IsStableUnderCoproductsOfShape J := by
  rw [← trivialFibrations_llp]
  apply MorphismProperty.llp_isStableUnderCoproductsOfShape

instance isStableUnderProductsOfShape_trivialFibrations :
    (trivialFibrations C).IsStableUnderProductsOfShape J := by
  rw [← cofibrations_rlp]
  apply MorphismProperty.rlp_isStableUnderProductsOfShape

end

section Pullbacks

section

variable {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]

instance [(cofibrations C).IsStableUnderCobaseChange] [hg : Cofibration g] :
    Cofibration (pushout.inl f g) := by
  rw [cofibration_iff] at hg ⊢
  exact MorphismProperty.of_isPushout (IsPushout.of_hasPushout f g) hg

instance [(cofibrations C).IsStableUnderCobaseChange] [hf : Cofibration f] :
    Cofibration (pushout.inr f g) := by
  rw [cofibration_iff] at hf ⊢
  exact MorphismProperty.of_isPushout (IsPushout.of_hasPushout f g).flip hf

instance [(trivialCofibrations C).IsStableUnderCobaseChange]
    [Cofibration g] [WeakEquivalence g] : WeakEquivalence (pushout.inl f g) := by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.of_isPushout (IsPushout.of_hasPushout f g)
    (mem_trivialCofibrations g)).2

instance [(trivialCofibrations C).IsStableUnderCobaseChange]
    [Cofibration f] [WeakEquivalence f] : WeakEquivalence (pushout.inr f g) := by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.of_isPushout (IsPushout.of_hasPushout f g).flip
    (mem_trivialCofibrations f)).2

end

section

variable {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]

instance [(fibrations C).IsStableUnderBaseChange]
    [hf : Fibration f] : Fibration (pullback.snd f g) := by
  rw [fibration_iff] at hf ⊢
  exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g) hf

instance [(fibrations C).IsStableUnderBaseChange]
    [hg : Fibration g] : Fibration (pullback.fst f g) := by
  rw [fibration_iff] at hg ⊢
  exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g).flip hg

instance [(trivialFibrations C).IsStableUnderBaseChange]
    [Fibration f] [WeakEquivalence f] : WeakEquivalence (pullback.snd f g) := by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g)
    (mem_trivialFibrations f)).2

instance [(trivialFibrations C).IsStableUnderBaseChange]
    [Fibration g] [WeakEquivalence g] : WeakEquivalence (pullback.fst f g) := by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g).flip
    (mem_trivialFibrations g)).2

end

end Pullbacks

section Products

variable (J : Type w) {C J} {X Y : J → C} (f : ∀ i, X i ⟶ Y i)

section

variable [HasCoproduct X] [HasCoproduct Y] [h : ∀ i, Cofibration (f i)]

instance [IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C)] :
    Cofibration (Limits.Sigma.map f) := by
  simp only [cofibration_iff] at h ⊢
  exact MorphismProperty.colimMap _ (fun ⟨i⟩ ↦ h i)

instance [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)]
    [∀ i, WeakEquivalence (f i)] :
    WeakEquivalence (Limits.Sigma.map f) := by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.colimMap (W := (trivialCofibrations C)) _
    (fun ⟨i⟩ ↦ mem_trivialCofibrations (f i))).2

end

section

variable [HasProduct X] [HasProduct Y] [h : ∀ i, Fibration (f i)]

instance [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)] :
    Fibration (Limits.Pi.map f) := by
  simp only [fibration_iff] at h ⊢
  exact MorphismProperty.limMap _ (fun ⟨i⟩ ↦ h i)

instance [IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C)]
    [∀ i, WeakEquivalence (f i)] :
    WeakEquivalence (Limits.Pi.map f) := by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.limMap (W := (trivialFibrations C)) _
    (fun ⟨i⟩ ↦ mem_trivialFibrations (f i))).2

end

end Products

section BinaryProducts

variable {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)

instance [IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C)]
    [h₁ : Cofibration f₁] [h₂ : Cofibration f₂] [HasBinaryCoproduct X₁ X₂]
    [HasBinaryCoproduct Y₁ Y₂] : Cofibration (coprod.map f₁ f₂) := by
  rw [cofibration_iff] at h₁ h₂ ⊢
  apply MorphismProperty.colimMap
  rintro (_ | _) <;> assumption

instance [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)]
    [h₁ : Fibration f₁] [h₂ : Fibration f₂] [HasBinaryProduct X₁ X₂]
    [HasBinaryProduct Y₁ Y₂] : Fibration (prod.map f₁ f₂) := by
  rw [fibration_iff] at h₁ h₂ ⊢
  apply MorphismProperty.limMap
  rintro (_ | _) <;> assumption

end BinaryProducts

section IsIso

variable {X Y : C} (f : X ⟶ Y)

instance [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)] [IsIso f] :
    Cofibration f := by
  have := (fibrations C).llp_of_isIso f
  rw [fibrations_llp] at this
  simpa only [cofibration_iff] using this.1

instance [IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C)] [IsIso f] :
    Fibration f := by
  have := (cofibrations C).rlp_of_isIso f
  rw [cofibrations_rlp] at this
  simpa only [fibration_iff] using this.1

instance [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)]
    [(weakEquivalences C).IsStableUnderRetracts] [IsIso f] :
    WeakEquivalence f := by
  have h := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C) f
  rw [weakEquivalence_iff]
  exact MorphismProperty.of_retract (RetractArrow.ofLeftLiftingProperty h.fac) h.hi.2

end IsIso

instance [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)]
    [(weakEquivalences C).IsStableUnderRetracts]
    [(weakEquivalences C).IsStableUnderComposition] :
    (weakEquivalences C).IsMultiplicative where
  id_mem _ := by
    rw [← weakEquivalence_iff]
    infer_instance

instance [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)]
    [(weakEquivalences C).IsStableUnderRetracts]
    [(weakEquivalences C).IsStableUnderComposition] :
    (weakEquivalences C).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition (fun _ _ _ (_ : IsIso _) ↦ by
    rw [← weakEquivalence_iff]
    infer_instance)

instance [(weakEquivalences C).ContainsIdentities] (X : C) :
    WeakEquivalence (𝟙 X) := by
  rw [weakEquivalence_iff]
  apply id_mem

section MapFactorizationData

variable {X Y : C} (f : X ⟶ Y)

section

variable (h : MapFactorizationData (cofibrations C) (trivialFibrations C) f)

instance : Cofibration h.i := by
  simpa only [cofibration_iff] using h.hi

instance : Fibration h.p := by
  simpa only [fibration_iff] using h.hp.1

instance : WeakEquivalence h.p := by
  simpa only [weakEquivalence_iff] using h.hp.2

end

section

variable (h : MapFactorizationData (trivialCofibrations C) (fibrations C) f)

instance : Cofibration h.i := by
  simpa only [cofibration_iff] using h.hi.1

instance : WeakEquivalence h.i := by
  simpa only [weakEquivalence_iff] using h.hi.2

instance : Fibration h.p := by
  simpa only [fibration_iff] using h.hp

end

end MapFactorizationData

end HomotopicalAlgebra
