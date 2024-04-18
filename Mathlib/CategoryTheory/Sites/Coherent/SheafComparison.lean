/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Coherent.Comparison
import Mathlib.CategoryTheory.Sites.InducedTopology
import Mathlib.CategoryTheory.Sites.Coherent.ReflectsPrecoherent
import Mathlib.CategoryTheory.Sites.Coherent.ReflectsPreregular
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


namespace CategoryTheory

open Limits Functor

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
    refine ⟨Z , fun a ↦ Full.preimage (g₀ a ≫ π a), ?_, fun a ↦ (?_ : S.arrows (Full.preimage _))⟩
    · refine F.finite_effectiveEpiFamily_of_map _ _ ?_
      simpa using this
    · obtain ⟨W, g₁, g₂, h₁, h₂⟩ := H₂ a
      rw [h₂]
      have : Full.preimage (g₀ a ≫ g₂ ≫ F.map g₁) = (Full.preimage (g₀ a ≫ g₂)) ≫ g₁ := by
        apply Faithful.map_injective (F := F)
        simp
      rw [this]
      exact S.downward_closed h₁ _

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

universe u

variable {C D : Type (u+1)} [LargeCategory C] [LargeCategory D] (F : C ⥤ D)
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
def equivalence (A : Type _) [Category.{u+1} A] [HasLimits A] : haveI := F.reflects_precoherent
    Sheaf (coherentTopology C) A ≌ Sheaf (coherentTopology D) A :=
  Functor.IsCoverDense.sheafEquivOfCoverPreservingCoverLifting F _ _ _

end SheafEquiv

section RegularExtensive

universe u

variable {C D : Type (u+1)} [LargeCategory C] [LargeCategory D] (F : C ⥤ D)
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
def equivalence' (A : Type _) [Category.{u+1} A] [HasLimits A] :
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
    refine ⟨_, Full.preimage (g₀ ≫ π), ?_, (?_ : S.arrows (Full.preimage _))⟩
    · refine F.effectiveEpi_of_map _ ?_
      simp only [Full.witness]
      infer_instance
    · obtain ⟨W, g₁, g₂, h₁, h₂⟩ := H₂
      rw [h₂]
      have : Full.preimage (g₀ ≫ g₂ ≫ F.map g₁) = (Full.preimage (g₀ ≫ g₂)) ≫ g₁ := by
        apply Faithful.map_injective (F := F)
        simp
      rw [this]
      exact S.downward_closed h₁ _

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

universe u

variable {C D : Type (u+1)} [LargeCategory C] [LargeCategory D] (F : C ⥤ D)
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
def equivalence (A : Type _) [Category.{u+1} A] [HasLimits A] : haveI := F.reflects_preregular
    Sheaf (regularTopology C) A ≌ Sheaf (regularTopology D) A :=
  Functor.IsCoverDense.sheafEquivOfCoverPreservingCoverLifting F _ _ _

end SheafEquiv

end regularTopology
