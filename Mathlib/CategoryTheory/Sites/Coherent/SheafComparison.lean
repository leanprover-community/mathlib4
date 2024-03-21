/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Coherent.Comparison
import Mathlib.CategoryTheory.Sites.InducedTopology
import Mathlib.CategoryTheory.Sites.Coherent.ReflectCoherent
import Mathlib.CategoryTheory.Sites.Coherent.ReflectRegular
/-!

# Categories of coherent sheaves

Given a fully faithful functor `F : C ⥤ D` into a precoherent category, which preserves and reflects
finite effective epi families, satisfies the property `F.EffectivelyEnough` (meaning that to every
object in `C` there is an effective epi from an object in the image of `F`), and
`F.IsCoverDense (coherentTopology _)` (which holds e.g. if every object in the image of `F` is
projective, see `CategoryTheory/Sites/Coherent/Projective`, or if `F` is an equivalence, see
`CategoryTheory/Sites/Equivalence`), the categories of coherent sheaves on `C` and `D` are
equivalent.

We give the corresonding result for the regular topology as well.
-/


namespace CategoryTheory

open Limits

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

namespace coherentTopology

variable [F.PreservesFiniteEffectiveEpiFamilies] [F.ReflectsFiniteEffectiveEpiFamilies]
  [Full F] [Faithful F]
  [Precoherent D]
  [F.EffectivelyEnough] [F.IsCoverDense (coherentTopology _)]

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
    let g₀ : (a : α) → F.obj (Z a) ⟶ Y a := fun a ↦ F.π (Y a)
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

lemma eq_induced : haveI := reflects_precoherent F
    coherentTopology C =
      F.inducedTopologyOfIsCoverDense (coherentTopology _) := by
  ext X S
  have := reflects_precoherent F
  rw [← exists_effectiveEpiFamily_iff_mem_induced F X]
  rw [← coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily S]

lemma coverPreserving : haveI := reflects_precoherent F
    CoverPreserving (coherentTopology _) (coherentTopology _) F := by
  rw [eq_induced F]
  apply LocallyCoverDense.inducedTopology_coverPreserving

instance coverLifting : haveI := reflects_precoherent F
    F.IsCocontinuous (coherentTopology _) (coherentTopology _) := by
  rw [eq_induced F]
  apply LocallyCoverDense.inducedTopology_isCocontinuous

instance isContinuous : haveI := reflects_precoherent F
    F.IsContinuous (coherentTopology _) (coherentTopology _) :=
  Functor.IsCoverDense.isContinuous _ _ _ (coverPreserving F)

section SheafEquiv

universe u

variable {C D : Type (u+1)} [LargeCategory C] [LargeCategory D] (F : C ⥤ D)
  [F.PreservesFiniteEffectiveEpiFamilies] [F.ReflectsFiniteEffectiveEpiFamilies]
  [Full F] [Faithful F]
  [Precoherent D]
  [F.EffectivelyEnough] [F.IsCoverDense (coherentTopology _)]

/--
The equivalence from coherent sheaves on `Stonean` to coherent sheaves on `CompHaus`
(i.e. condensed sets).
-/
noncomputable
def equivalence (A : Type _) [Category.{u+1} A] [HasLimits A] : haveI := reflects_precoherent F
    Sheaf (coherentTopology C) A ≌ Sheaf (coherentTopology D) A :=
  Functor.IsCoverDense.sheafEquivOfCoverPreservingCoverLifting F _ _ _

end SheafEquiv

section RegularExtensive

universe u

variable {C D : Type (u+1)} [LargeCategory C] [LargeCategory D] (F : C ⥤ D)
  [F.PreservesEffectiveEpis] [F.ReflectsEffectiveEpis]
  [Full F] [Faithful F]
  [FinitaryExtensive D] [Preregular D]
  [PreservesFiniteCoproducts F]
  [HasFiniteCoproducts C] [HasPullbacksOfInclusions C]
  [PreservesPullbacksOfInclusions F]
  [ReflectsLimitsOfShape WalkingCospan F]
  [ReflectsColimitsOfShape (Discrete WalkingPair) F]
  [F.EffectivelyEnough] [F.IsCoverDense (coherentTopology _)]

/--
The equivalence from coherent sheaves on `Stonean` to coherent sheaves on `CompHaus`
(i.e. condensed sets).
-/
noncomputable
def equivalence' (A : Type _) [Category.{u+1} A] [HasLimits A] :
    haveI := finitaryExtensive_of_preserves_and_reflects F
    haveI := reflects_precoherent F
    Sheaf (coherentTopology C) A ≌ Sheaf (coherentTopology D) A :=
  have := finitaryExtensive_of_preserves_and_reflects F
  Functor.IsCoverDense.sheafEquivOfCoverPreservingCoverLifting F _ _ _

end RegularExtensive

end coherentTopology

namespace regularTopology

variable [F.PreservesEffectiveEpis] [F.ReflectsEffectiveEpis]
  [Full F] [Faithful F]
  [Preregular D]
  [F.EffectivelyEnough] [F.IsCoverDense (regularTopology _)]

theorem exists_effectiveEpi_iff_mem_induced (X : C) (S : Sieve X) :
    (∃ (Y : C) (π : Y ⟶ X),
      EffectiveEpi π ∧ S.arrows π) ↔
    (S ∈ F.inducedTopologyOfIsCoverDense (regularTopology _) X) := by
  refine ⟨fun ⟨Y, π, ⟨H₁, H₂⟩⟩ ↦ ?_, fun hS ↦ ?_⟩
  · apply (mem_sieves_iff_hasEffectiveEpi (Sieve.functorPushforward _ S)).mpr
    refine ⟨F.obj Y, F.map π, ⟨?_, Sieve.image_mem_functorPushforward F S H₂⟩⟩
    exact F.map_effectiveEpi _
  · obtain ⟨Y, π, ⟨H₁, H₂⟩⟩ := (mem_sieves_iff_hasEffectiveEpi _).mp hS
    let g₀ := F.π Y
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

lemma eq_induced : haveI := reflects_preregular F
    regularTopology C =
      F.inducedTopologyOfIsCoverDense (regularTopology _) := by
  ext X S
  have := reflects_preregular F
  rw [← exists_effectiveEpi_iff_mem_induced F X]
  rw [← mem_sieves_iff_hasEffectiveEpi S]

lemma coverPreserving : haveI := reflects_preregular F
    CoverPreserving (regularTopology _) (regularTopology _) F := by
  rw [eq_induced F]
  apply LocallyCoverDense.inducedTopology_coverPreserving

instance coverLifting : haveI := reflects_preregular F
    F.IsCocontinuous (regularTopology _) (regularTopology _) := by
  rw [eq_induced F]
  apply LocallyCoverDense.inducedTopology_isCocontinuous

instance isContinuous : haveI := reflects_preregular F
    F.IsContinuous (regularTopology _) (regularTopology _) :=
  Functor.IsCoverDense.isContinuous _ _ _ (coverPreserving F)

section SheafEquiv

universe u

variable {C D : Type (u+1)} [LargeCategory C] [LargeCategory D] (F : C ⥤ D)
  [F.PreservesEffectiveEpis] [F.ReflectsEffectiveEpis]
  [Full F] [Faithful F]
  [Preregular D]
  [F.EffectivelyEnough] [F.IsCoverDense (regularTopology _)]

/--
The equivalence from coherent sheaves on `Stonean` to coherent sheaves on `CompHaus`
(i.e. condensed sets).
-/
noncomputable
def equivalence (A : Type _) [Category.{u+1} A] [HasLimits A] : haveI := reflects_preregular F
    Sheaf (regularTopology C) A ≌ Sheaf (regularTopology D) A :=
  Functor.IsCoverDense.sheafEquivOfCoverPreservingCoverLifting F _ _ _

end SheafEquiv

end regularTopology
