/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Coherent.Comparison
import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveSheaves
import Mathlib.CategoryTheory.Sites.Coherent.ReflectsPrecoherent
import Mathlib.CategoryTheory.Sites.Coherent.ReflectsPreregular
import Mathlib.CategoryTheory.Sites.InducedTopology
import Mathlib.CategoryTheory.Sites.Whiskering
/-!

# Categories of coherent sheaves

Given a fully faithful functor `F : C ⥤ D` into a precoherent category, which preserves and reflects
finite effective epi families, and satisfies the property `F.EffectivelyEnough` (meaning that to
every object in `C` there is an effective epi from an object in the image of `F`), the categories
of coherent sheaves on `C` and `D` are equivalent (see
`CategoryTheory.coherentTopology.equivalence`).

The main application of this equivalence is the characterisation of condensed sets as coherent
sheaves on either `CompHaus`, `Profinite` or `Stonean`. See the file `Condensed/Equivalence.lean`

We give the corresonding result for the regular topology as well (see
`CategoryTheory.regularTopology.equivalence`).
-/


universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open Limits Functor regularTopology

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

namespace coherentTopology

variable [F.PreservesFiniteEffectiveEpiFamilies] [F.ReflectsFiniteEffectiveEpiFamilies]
  [F.Full] [F.Faithful] [F.EffectivelyEnough] [Precoherent D]

instance : F.IsCoverDense (coherentTopology _) := by
  refine F.isCoverDense_of_generate_singleton_functor_π_mem _ fun B ↦ ⟨_, F.effectiveEpiOver B, ?_⟩
  apply Coverage.saturate.of
  refine ⟨Unit, inferInstance, fun _ => F.effectiveEpiOverObj B,
    fun _ => F.effectiveEpiOver B, ?_ , ?_⟩
  · funext; ext -- Do we want `Presieve.ext`?
    refine ⟨fun ⟨⟩ ↦ ⟨()⟩, ?_⟩
    rintro ⟨⟩
    simp
  · rw [← effectiveEpi_iff_effectiveEpiFamily]
    infer_instance

theorem exists_effectiveEpiFamily_iff_mem_induced (X : C) (S : Sieve X) :
    (∃ (α : Type) (_ : Finite α) (Y : α → C) (π : (a : α) → (Y a ⟶ X)),
      EffectiveEpiFamily Y π ∧ (∀ a : α, (S.arrows) (π a)) ) ↔
    (S ∈ F.inducedTopologyOfIsCoverDense (coherentTopology _) X) := by
  refine ⟨fun ⟨α, _, Y, π, ⟨H₁, H₂⟩⟩ ↦ ?_, fun hS ↦ ?_⟩
  · apply (mem_sieves_iff_hasEffectiveEpiFamily (Sieve.functorPushforward _ S)).mpr
    refine ⟨α, inferInstance, fun i => F.obj (Y i),
      fun i => F.map (π i), ⟨?_,
      fun a => Sieve.image_mem_functorPushforward F S (H₂ a)⟩⟩
    exact F.map_finite_effectiveEpiFamily _ _
  · obtain ⟨α, _, Y, π, ⟨H₁, H₂⟩⟩ := (mem_sieves_iff_hasEffectiveEpiFamily _).mp hS
    refine ⟨α, inferInstance, ?_⟩
    let Z : α → C := fun a ↦ (Functor.EffectivelyEnough.presentation (F := F) (Y a)).some.p
    let g₀ : (a : α) → F.obj (Z a) ⟶ Y a := fun a ↦ F.effectiveEpiOver (Y a)
    have : EffectiveEpiFamily _ (fun a ↦ g₀ a ≫ π a) := inferInstance
    refine ⟨Z , fun a ↦ F.preimage (g₀ a ≫ π a), ?_, fun a ↦ (?_ : S.arrows (F.preimage _))⟩
    · refine F.finite_effectiveEpiFamily_of_map _ _ ?_
      simpa using this
    · obtain ⟨W, g₁, g₂, h₁, h₂⟩ := H₂ a
      rw [h₂]
      convert S.downward_closed h₁ (F.preimage (g₀ a ≫ g₂))
      exact F.map_injective (by simp)

lemma eq_induced : haveI := F.reflects_precoherent
    coherentTopology C =
      F.inducedTopologyOfIsCoverDense (coherentTopology _) := by
  ext X S
  have := F.reflects_precoherent
  rw [← exists_effectiveEpiFamily_iff_mem_induced F X]
  rw [← coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily S]

lemma coverPreserving : haveI := F.reflects_precoherent
    CoverPreserving (coherentTopology _) (coherentTopology _) F := by
  rw [eq_induced F]
  apply LocallyCoverDense.inducedTopology_coverPreserving

instance coverLifting : haveI := F.reflects_precoherent
    F.IsCocontinuous (coherentTopology _) (coherentTopology _) := by
  rw [eq_induced F]
  apply LocallyCoverDense.inducedTopology_isCocontinuous

instance isContinuous : haveI := F.reflects_precoherent
    F.IsContinuous (coherentTopology _) (coherentTopology _) :=
  Functor.IsCoverDense.isContinuous _ _ _ (coverPreserving F)

section SheafEquiv

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D)
  [F.PreservesFiniteEffectiveEpiFamilies] [F.ReflectsFiniteEffectiveEpiFamilies]
  [F.Full] [F.Faithful]
  [Precoherent D]
  [F.EffectivelyEnough]

/--
The equivalence from coherent sheaves on `C` to coherent sheaves on `D`, given a fully faithful
functor `F : C ⥤ D` to a precoherent category, which preserves and reflects effective epimorphic
families, and satisfies `F.EffectivelyEnough`.
-/
noncomputable
def equivalence (A : Type u₃) [Category.{v₃} A] [∀ X, HasLimitsOfShape (StructuredArrow X F.op) A] :
    haveI := F.reflects_precoherent
    Sheaf (coherentTopology C) A ≌ Sheaf (coherentTopology D) A :=
  Functor.IsCoverDense.sheafEquivOfCoverPreservingCoverLifting F _ _ _

end SheafEquiv

section RegularExtensive

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D)
  [F.PreservesEffectiveEpis] [F.ReflectsEffectiveEpis]
  [F.Full] [F.Faithful]
  [FinitaryExtensive D] [Preregular D]
  [FinitaryPreExtensive C]
  [PreservesFiniteCoproducts F]
  [F.EffectivelyEnough]

/--
The equivalence from coherent sheaves on `C` to coherent sheaves on `D`, given a fully faithful
functor `F : C ⥤ D` to an extensive preregular category, which preserves and reflects effective
epimorphisms and satisfies `F.EffectivelyEnough`.
-/
noncomputable
def equivalence' (A : Type u₃) [Category.{v₃} A]
    [∀ X, HasLimitsOfShape (StructuredArrow X F.op) A] :
    haveI := F.reflects_precoherent
    Sheaf (coherentTopology C) A ≌ Sheaf (coherentTopology D) A :=
  Functor.IsCoverDense.sheafEquivOfCoverPreservingCoverLifting F _ _ _

end RegularExtensive

end coherentTopology

namespace regularTopology

variable [F.PreservesEffectiveEpis] [F.ReflectsEffectiveEpis] [F.Full] [F.Faithful]
  [F.EffectivelyEnough] [Preregular D]

instance : F.IsCoverDense (regularTopology _) := by
  refine F.isCoverDense_of_generate_singleton_functor_π_mem _ fun B ↦ ⟨_, F.effectiveEpiOver B, ?_⟩
  apply Coverage.saturate.of
  refine ⟨F.effectiveEpiOverObj B, F.effectiveEpiOver B, ?_, inferInstance⟩
  funext; ext -- Do we want `Presieve.ext`?
  refine ⟨fun ⟨⟩ ↦ ⟨()⟩, ?_⟩
  rintro ⟨⟩
  simp

theorem exists_effectiveEpi_iff_mem_induced (X : C) (S : Sieve X) :
    (∃ (Y : C) (π : Y ⟶ X),
      EffectiveEpi π ∧ S.arrows π) ↔
    (S ∈ F.inducedTopologyOfIsCoverDense (regularTopology _) X) := by
  refine ⟨fun ⟨Y, π, ⟨H₁, H₂⟩⟩ ↦ ?_, fun hS ↦ ?_⟩
  · apply (mem_sieves_iff_hasEffectiveEpi (Sieve.functorPushforward _ S)).mpr
    refine ⟨F.obj Y, F.map π, ⟨?_, Sieve.image_mem_functorPushforward F S H₂⟩⟩
    exact F.map_effectiveEpi _
  · obtain ⟨Y, π, ⟨H₁, H₂⟩⟩ := (mem_sieves_iff_hasEffectiveEpi _).mp hS
    let g₀ := F.effectiveEpiOver Y
    refine ⟨_, F.preimage (g₀ ≫ π), ?_, (?_ : S.arrows (F.preimage _))⟩
    · refine F.effectiveEpi_of_map _ ?_
      simp only [map_preimage]
      infer_instance
    · obtain ⟨W, g₁, g₂, h₁, h₂⟩ := H₂
      rw [h₂]
      convert S.downward_closed h₁ (F.preimage (g₀ ≫ g₂))
      exact F.map_injective (by simp)

lemma eq_induced : haveI := F.reflects_preregular
    regularTopology C =
      F.inducedTopologyOfIsCoverDense (regularTopology _) := by
  ext X S
  have := F.reflects_preregular
  rw [← exists_effectiveEpi_iff_mem_induced F X]
  rw [← mem_sieves_iff_hasEffectiveEpi S]

lemma coverPreserving : haveI := F.reflects_preregular
    CoverPreserving (regularTopology _) (regularTopology _) F := by
  rw [eq_induced F]
  apply LocallyCoverDense.inducedTopology_coverPreserving

instance coverLifting : haveI := F.reflects_preregular
    F.IsCocontinuous (regularTopology _) (regularTopology _) := by
  rw [eq_induced F]
  apply LocallyCoverDense.inducedTopology_isCocontinuous

instance isContinuous : haveI := F.reflects_preregular
    F.IsContinuous (regularTopology _) (regularTopology _) :=
  Functor.IsCoverDense.isContinuous _ _ _ (coverPreserving F)

section SheafEquiv

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D)
  [F.PreservesEffectiveEpis] [F.ReflectsEffectiveEpis]
  [F.Full] [F.Faithful]
  [Preregular D]
  [F.EffectivelyEnough]

/--
The equivalence from regular sheaves on `C` to regular sheaves on `D`, given a fully faithful
functor `F : C ⥤ D` to a preregular category, which preserves and reflects effective
epimorphisms and satisfies `F.EffectivelyEnough`.
-/
noncomputable
def equivalence (A : Type u₃) [Category.{v₃} A] [∀ X, HasLimitsOfShape (StructuredArrow X F.op) A] :
    haveI := F.reflects_preregular
    Sheaf (regularTopology C) A ≌ Sheaf (regularTopology D) A :=
  Functor.IsCoverDense.sheafEquivOfCoverPreservingCoverLifting F _ _ _

end SheafEquiv

end regularTopology

namespace Presheaf

variable {A : Type u₃} [Category.{v₃} A] (F : Cᵒᵖ ⥤ A)

theorem isSheaf_coherent_iff_regular_and_extensive [Preregular C] [FinitaryPreExtensive C] :
    IsSheaf (coherentTopology C) F ↔
    IsSheaf (extensiveTopology C) F ∧ IsSheaf (regularTopology C) F := by
  rw [← extensive_regular_generate_coherent]
  exact isSheaf_sup (extensiveCoverage C) (regularCoverage C) F

theorem isSheaf_iff_preservesFiniteProducts_and_equalizerCondition
    [Preregular C] [FinitaryExtensive C]
    [h : ∀ {Y X : C} (f : Y ⟶ X) [EffectiveEpi f], HasPullback f f] :
    IsSheaf (coherentTopology C) F ↔ Nonempty (PreservesFiniteProducts F) ∧
      EqualizerCondition F := by
  rw [isSheaf_coherent_iff_regular_and_extensive]
  exact and_congr (isSheaf_iff_preservesFiniteProducts _)
    (@equalizerCondition_iff_isSheaf _ _ _ _ F _ h).symm

theorem isSheaf_iff_preservesFiniteProducts_of_projective [Preregular C] [FinitaryExtensive C]
    [∀ (X : C), Projective X] :
    IsSheaf (coherentTopology C) F ↔ Nonempty (PreservesFiniteProducts F) := by
  rw [isSheaf_coherent_iff_regular_and_extensive, and_iff_left (isSheaf_of_projective F),
    isSheaf_iff_preservesFiniteProducts]

variable {B : Type u₄} [Category.{v₄} B]
variable (s : A ⥤ B)

lemma isSheaf_coherent_of_hasPullbacks_comp [Preregular C] [FinitaryExtensive C]
    [h : ∀ {Y X : C} (f : Y ⟶ X) [EffectiveEpi f], HasPullback f f] [PreservesFiniteLimits s]
    (hF : IsSheaf (coherentTopology C) F) : IsSheaf (coherentTopology C) (F ⋙ s) := by
  rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition (h := h)] at hF ⊢
  have := hF.1.some
  refine ⟨⟨inferInstance⟩, fun _ _ π _ c hc ↦ ⟨?_⟩⟩
  exact isLimitForkMapOfIsLimit s _ (hF.2 π c hc).some

lemma isSheaf_coherent_of_hasPullbacks_of_comp [Preregular C] [FinitaryExtensive C]
    [h : ∀ {Y X : C} (f : Y ⟶ X) [EffectiveEpi f], HasPullback f f]
    [ReflectsFiniteLimits s]
    (hF : IsSheaf (coherentTopology C) (F ⋙ s)) : IsSheaf (coherentTopology C) F := by
  rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition (h := h)] at hF ⊢
  refine ⟨⟨⟨fun J _ ↦ ⟨fun {K} ↦ ⟨fun {c} hc ↦ ?_⟩⟩⟩⟩, fun _ _ π _ c hc ↦ ⟨?_⟩⟩
  · exact isLimitOfReflects s ((hF.1.some.1 J).1.1 hc)
  · exact isLimitOfIsLimitForkMap s _ (hF.2 π c hc).some

lemma isSheaf_coherent_of_projective_comp [Preregular C] [FinitaryExtensive C]
    [∀ (X : C), Projective X] [PreservesFiniteProducts s]
    (hF : IsSheaf (coherentTopology C) F) : IsSheaf (coherentTopology C) (F ⋙ s) := by
  rw [isSheaf_iff_preservesFiniteProducts_of_projective] at hF ⊢
  have := hF.some
  exact ⟨inferInstance⟩

lemma isSheaf_coherent_of_projective_of_comp [Preregular C] [FinitaryExtensive C]
    [∀ (X : C), Projective X]
    [ReflectsFiniteProducts s]
    (hF : IsSheaf (coherentTopology C) (F ⋙ s)) : IsSheaf (coherentTopology C) F := by
  rw [isSheaf_iff_preservesFiniteProducts_of_projective] at hF ⊢
  refine ⟨⟨fun J _ ↦ ⟨fun {K} ↦ ⟨fun {c} hc ↦ ?_⟩⟩⟩⟩
  exact isLimitOfReflects s ((hF.some.1 J).1.1 hc)

instance [Preregular C] [FinitaryExtensive C]
    [h : ∀ {Y X : C} (f : Y ⟶ X) [EffectiveEpi f], HasPullback f f]
    [PreservesFiniteLimits s] : (coherentTopology C).HasSheafCompose s where
      isSheaf F hF := isSheaf_coherent_of_hasPullbacks_comp (h := h) F s hF

instance [Preregular C] [FinitaryExtensive C] [∀ (X : C), Projective X]
    [PreservesFiniteProducts s] : (coherentTopology C).HasSheafCompose s where
  isSheaf F hF := isSheaf_coherent_of_projective_comp F s hF

end CategoryTheory.Presheaf
