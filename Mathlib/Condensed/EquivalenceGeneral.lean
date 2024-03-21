/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.EffectiveEpi.Extensive
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.CategoryTheory.Sites.Coherent.CoherentTopology
import Mathlib.CategoryTheory.Sites.Coherent.Comparison
import Mathlib.CategoryTheory.Sites.InducedTopology
import Mathlib.CategoryTheory.Sites.Coherent.ReflectCoherent
import Mathlib.CategoryTheory.Sites.Coherent.ReflectRegular
/-!

# Categories of coherent sheaves

Given a fully faithful functor `F : C ⥤ D` into a precoherent category, which preserves and reflects
finite effective epi families, satisfies the property `F.EffectivelyEnough` (meaning that to every
object in `C` there is an effective epi from an object in the image of `F`), and that every object
in its image is projective, the categories of coherent sheaves on `C` and `D` are equivalent.
-/


namespace CategoryTheory

open Limits

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

variable [F.PreservesFiniteEffectiveEpiFamilies] [F.ReflectsFiniteEffectiveEpiFamilies]
  [Full F] [Faithful F]
  [Precoherent D]
  [F.EffectivelyEnough] [∀ (X : C), Projective (F.obj X)]

namespace coherentTopology

lemma generate_singleton_functor_π_mem (B : D) :
    Sieve.generate (Presieve.singleton (F.π B)) ∈ coherentTopology D B := by
  apply Coverage.saturate.of
  refine ⟨Unit, inferInstance, fun _ => F.over B,
    fun _ => F.π B, ?_ , ?_⟩
  · funext X f
    ext
    refine ⟨fun ⟨⟩ ↦ ⟨()⟩, ?_⟩
    rintro ⟨⟩
    simp only [Presieve.singleton_eq_iff_domain]
  · rw [← effectiveEpi_iff_effectiveEpiFamily]
    infer_instance

instance : F.IsCoverDense (coherentTopology _) := by
  constructor
  intro B
  convert generate_singleton_functor_π_mem F B
  ext Y f
  refine ⟨fun ⟨⟨obj, lift, map, fact⟩⟩ ↦ ?_, fun ⟨Z, h, g, hypo1, hf⟩ ↦ ?_⟩
  · obtain ⟨p, p_factors⟩ := Projective.factors map (F.π B)
    refine ⟨_, ⟨lift ≫ p, ⟨(F.π B),
      ⟨Presieve.singleton.mk, by rw [← fact, ← p_factors, Category.assoc]⟩⟩⟩⟩
  · cases hypo1
    exact ⟨⟨_, h, F.π B, hf⟩⟩

theorem exists_effectiveEpiFamily_iff_mem_induced (X : C) (S : Sieve X) :
    (∃ (α : Type) (_ : Finite α) (Y : α → C) (π : (a : α) → (Y a ⟶ X)),
      EffectiveEpiFamily Y π ∧ (∀ a : α, (S.arrows) (π a)) ) ↔
    (S ∈ F.inducedTopologyOfIsCoverDense (coherentTopology _) X) := by
  refine ⟨fun ⟨α, _, Y, π, ⟨H₁, H₂⟩⟩ ↦ ?_, fun hS ↦ ?_⟩
  · apply (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily (Sieve.functorPushforward _ S)).mpr
    refine ⟨α, inferInstance, fun i => F.obj (Y i),
      fun i => F.map (π i), ⟨?_,
      fun a => Sieve.image_mem_functorPushforward F S (H₂ a)⟩⟩
    exact F.map_finite_effectiveEpiFamily _ _
  · obtain ⟨α, _, Y, π, ⟨H₁, H₂⟩⟩ := (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily _).mp hS
    refine ⟨α, inferInstance, ?_⟩
    let Z : α → C := fun a ↦ (Functor.EffectivelyEnough.presentation (F := F) (Y a)).some.p
    let g₀ : (a : α) → F.obj (Z a) ⟶ Y a := fun a ↦ F.π (Y a)
    have : ∀ a, EffectiveEpi (g₀ a) := inferInstance
    simp_rw [effectiveEpi_iff_effectiveEpiFamily] at this
    have : EffectiveEpiFamily _ (fun a ↦ g₀ a ≫ π a) := by
      have := EffectiveEpiFamily.transitive_of_finite (β := fun _ ↦ Unit) _ H₁ _ this
      exact EffectiveEpiFamily.reindex (e := Equiv.sigmaPUnit α) _ _ this
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
  -- [F.PreservesEffectiveEpis] [F.ReflectsEffectiveEpis]
  [F.PreservesFiniteEffectiveEpiFamilies] [F.ReflectsFiniteEffectiveEpiFamilies]
  [Full F] [Faithful F]
  [Precoherent D]
  [F.EffectivelyEnough] [∀ (X : D), Projective X]

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
  [F.EffectivelyEnough] [∀ (X : D), Projective X]

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
