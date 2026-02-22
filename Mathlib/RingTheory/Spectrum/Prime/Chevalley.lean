/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Spectrum.Prime.ChevalleyComplexity

/-!
# Chevalley's theorem

In this file we provide the usual (algebraic) version of Chevalley's theorem.
For the proof see `Mathlib/RingTheory/Spectrum/Prime/ChevalleyComplexity.lean`.
-/

public section

variable {R S : Type*} [CommRing R] [CommRing S]

open Function Localization MvPolynomial Polynomial TensorProduct PrimeSpectrum Topology
open scoped Pointwise

namespace PrimeSpectrum

lemma isConstructible_comap_C
    {s : Set (PrimeSpectrum (Polynomial R))} (hs : IsConstructible s) :
    IsConstructible (comap Polynomial.C '' s) := by
  obtain ⟨S, rfl⟩ := exists_constructibleSetData_iff.mpr hs
  obtain ⟨T, hT, -⟩ := ChevalleyThm.chevalley_polynomialC _ Submodule.mem_top S (by simp)
  rw [hT]
  exact T.isConstructible_toSet

/-- **Chevalley's theorem**: If `f` is of finite presentation,
then the image of a constructible set under `Spec(f)` is constructible. -/
lemma isConstructible_comap_image
    {f : R →+* S} (hf : f.FinitePresentation)
    {s : Set (PrimeSpectrum S)} (hs : IsConstructible s) :
    IsConstructible (comap f '' s) := by
  refine hf.polynomial_induction
    (fun _ _ _ _ f ↦ ∀ s, IsConstructible s → IsConstructible (comap f '' s))
    (fun _ _ _ _ f ↦ ∀ s, IsConstructible s → IsConstructible (comap f '' s))
    (fun _ _ _ ↦ isConstructible_comap_C) ?_ ?_ f s hs
  · intro R _ S _ f hf hf' s hs
    refine hs.image_of_isClosedEmbedding (isClosedEmbedding_comap_of_surjective _ f hf) ?_
    rw [range_comap_of_surjective _ f hf]
    exact isRetrocompact_zeroLocus_compl_of_fg hf'
  · intro R _ S _ T _ f g H₁ H₂ s hs
    simp only [comap_comp, Set.image_comp]
    exact H₁ _ (H₂ _ hs)

lemma isConstructible_range_comap {f : R →+* S} (hf : f.FinitePresentation) :
    IsConstructible (Set.range <| comap f) :=
  Set.image_univ ▸ isConstructible_comap_image hf .univ

@[stacks 00I1]
lemma isOpenMap_comap_of_hasGoingDown_of_finitePresentation
    [Algebra R S] [Algebra.HasGoingDown R S] [Algebra.FinitePresentation R S] :
    IsOpenMap (comap (algebraMap R S)) := by
  rw [isBasis_basic_opens.isOpenMap_iff]
  rintro _ ⟨_, ⟨f, rfl⟩, rfl⟩
  exact isOpen_of_stableUnderGeneralization_of_isConstructible
    ((basicOpen f).2.stableUnderGeneralization.image
      (Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp ‹_›))
    (isConstructible_comap_image (RingHom.finitePresentation_algebraMap.mpr ‹_›)
      isConstructible_basicOpen)

set_option backward.isDefEq.respectTransparency false in
open TensorProduct in
@[stacks 037G]
theorem isOpenMap_comap_algebraMap_tensorProduct_of_field
    {K A B : Type*} [Field K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B] :
    IsOpenMap (PrimeSpectrum.comap (algebraMap A (A ⊗[K] B))) := by
  intro U hU
  wlog hU' : ∃ f, U = SetLike.coe (basicOpen f) generalizing U
  · rw [eq_biUnion_of_isOpen hU, Set.image_iUnion₂]
    exact isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ this _ (basicOpen _).isOpen ⟨_, rfl⟩
  obtain ⟨f, rfl⟩ := hU'
  obtain ⟨B', hB, f, rfl⟩ := exists_fg_and_mem_baseChange f
  have : Algebra.FinitePresentation K B' :=
    Algebra.FinitePresentation.of_finiteType.mp ⟨B'.fg_top.mpr hB⟩
  convert isOpenMap_comap_of_hasGoingDown_of_finitePresentation (R := A) (S := A ⊗[K] B') _
    (basicOpen f).isOpen using 1
  ext x
  rw [PrimeSpectrum.mem_image_comap_basicOpen, PrimeSpectrum.mem_image_comap_basicOpen,
    not_iff_not]
  let ψ := Algebra.TensorProduct.map
    (Algebra.TensorProduct.map (.id A A) B'.val) (.id A x.asIdeal.ResidueField)
  have hψeq : ψ = (Algebra.TensorProduct.comm _ _ _ |>.toAlgHom.comp <|
    Algebra.TensorProduct.cancelBaseChange K A A _ B |>.symm.toAlgHom.comp <|
    Algebra.TensorProduct.map (.id _ _) B'.val |>.comp <|
    Algebra.TensorProduct.cancelBaseChange K A A _ B' |>.toAlgHom.comp <|
    (Algebra.TensorProduct.comm _ _ _).toAlgHom) := by ext; simp [ψ]
  have hψ : Function.Injective ψ := by
    rw [hψeq]
    dsimp
    simp_rw [EmbeddingLike.comp_injective, ← Function.comp_assoc, EquivLike.injective_comp]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  rw [← IsNilpotent.map_iff hψ]
  rfl

end PrimeSpectrum
