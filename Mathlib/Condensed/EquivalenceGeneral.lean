import Mathlib.CategoryTheory.EffectiveEpi.Extensive
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.CategoryTheory.Sites.Coherent.CoherentTopology
import Mathlib.CategoryTheory.Sites.Coherent.Comparison
import Mathlib.CategoryTheory.Sites.InducedTopology
import Mathlib.CategoryTheory.Sites.Coherent.ReflectRegular


namespace CategoryTheory

open Limits

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

noncomputable section EffectivePresentation

structure Functor.EffectivePresentation (X : D) where
  p : C
  f : F.obj p ⟶ X
  effectiveEpi : IsSplitEpi f

class Functor.EffectivelyEnough : Prop where
  presentation : ∀ (X : D), Nonempty (F.EffectivePresentation X)

namespace Projective'

variable [F.EffectivelyEnough]

open Functor

/-- `Projective.over X` provides an arbitrarily chosen projective object equipped with
an epimorphism `Projective.π : Projective.over X ⟶ X`.
-/
def over (X : D) : D :=
  F.obj (EffectivelyEnough.presentation (F := F) X).some.p

/-- The epimorphism `projective.π : projective.over X ⟶ X`
from the arbitrarily chosen projective object over `X`.
-/
def π (X : D) : over F X ⟶ X :=
  (EffectivelyEnough.presentation (F := F) X).some.f

instance π_isSplitEpi (X : D) : IsSplitEpi (π F X) :=
  (EffectivelyEnough.presentation X).some.effectiveEpi

instance π_effectiveEpi (X : D) : EffectiveEpi (π F X) := by
  rw [← Category.comp_id (π F X)]
  infer_instance
  -- todo: add general split epi -> effective epi instance

end Projective'

end EffectivePresentation

variable [F.PreservesEffectiveEpis] [F.ReflectsEffectiveEpis]
  [Preregular D] [Full F] [Faithful F]
  [FinitaryExtensive D] [Preregular D]
  [HasFiniteCoproducts C]
  [HasPullbacksOfInclusions C]
  [PreservesFiniteCoproducts F]
  [PreservesPullbacksOfInclusions F]
  [F.EffectivelyEnough] [∀ (X : D), Projective X]

open Projective'

namespace ProjectiveSheafEquiv

lemma generate_singleton_mem_coherentTopology (B : D) :
    Sieve.generate (Presieve.singleton (π F B)) ∈ coherentTopology D B := by
  apply Coverage.saturate.of
  refine ⟨Unit, inferInstance, fun _ => over F B,
    fun _ => π F B, ?_ , ?_⟩
  · funext X f
    ext
    refine ⟨fun ⟨⟩ ↦ ⟨()⟩, ?_⟩
    rintro ⟨⟩
    simp only [Presieve.singleton_eq_iff_domain]
  · rw [← effectiveEpi_iff_effectiveEpiFamily]
    infer_instance

instance isCoverDense : F.IsCoverDense (coherentTopology _) := by
  constructor
  intro B
  convert generate_singleton_mem_coherentTopology F B
  ext Y f
  refine ⟨fun ⟨⟨obj, lift, map, fact⟩⟩ ↦ ?_, fun ⟨Z, h, g, hypo1, hf⟩ ↦ ?_⟩
  · obtain ⟨p, p_factors⟩ := Projective.factors map (π F B)
    refine ⟨_, ⟨lift ≫ p, ⟨(π F B),
      ⟨Presieve.singleton.mk, by rw [← fact, ← p_factors, Category.assoc]⟩⟩⟩⟩
  · cases hypo1
    exact ⟨⟨_, h, π F B, hf⟩⟩

theorem coverDense.inducedTopology_Sieve_iff_EffectiveEpiFamily (X : C) (S : Sieve X) :
    (∃ (α : Type) (_ : Finite α) (Y : α → C) (π : (a : α) → (Y a ⟶ X)),
      EffectiveEpiFamily Y π ∧ (∀ a : α, (S.arrows) (π a)) ) ↔
    (S ∈ F.inducedTopologyOfIsCoverDense (coherentTopology _) X) := by
  have := finitaryExtensive_of_preserves_and_reflects F
  refine ⟨fun ⟨α, _, Y, π, ⟨H₁, H₂⟩⟩ ↦ ?_, fun hS ↦ ?_⟩
  · apply (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily (Sieve.functorPushforward _ S)).mpr
    refine ⟨α, inferInstance, fun i => F.obj (Y i),
      fun i => F.map (π i), ⟨?_,
      fun a => Sieve.image_mem_functorPushforward F S (H₂ a)⟩⟩
    exact F.map_finite_effectiveEpiFamily _ _
  · obtain ⟨α, _, Y, π, ⟨H₁, H₂⟩⟩ := (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily _).mp hS
    refine ⟨α, inferInstance, ?_⟩
    let Z : α → C := fun a ↦ (Functor.EffectivelyEnough.presentation (F := F) (Y a)).some.p
    let g₀ : (a : α) → F.obj (Z a) ⟶ Y a := fun a ↦ Projective'.π F (Y a)
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

lemma coherentTopology_is_induced : haveI := finitaryExtensive_of_preserves_and_reflects F
    haveI : Preregular C := reflects_preregular F (fun X ↦ ⟨_, π F X, inferInstance⟩)
    coherentTopology C =
      F.inducedTopologyOfIsCoverDense (coherentTopology _) := by
  ext X S
  haveI := finitaryExtensive_of_preserves_and_reflects F
  haveI : Preregular C := reflects_preregular F (fun X ↦ ⟨_, π F X, inferInstance⟩)
  rw [← coverDense.inducedTopology_Sieve_iff_EffectiveEpiFamily F X]
  rw [← coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily S]

lemma coverPreserving : haveI := finitaryExtensive_of_preserves_and_reflects F
    haveI : Preregular C := reflects_preregular F (fun X ↦ ⟨_, π F X, inferInstance⟩)
    CoverPreserving (coherentTopology _) (coherentTopology _) F := by
  rw [coherentTopology_is_induced F]
  apply LocallyCoverDense.inducedTopology_coverPreserving

instance coverLifting : haveI := finitaryExtensive_of_preserves_and_reflects F
    haveI : Preregular C := reflects_preregular F (fun X ↦ ⟨_, π F X, inferInstance⟩)
    F.IsCocontinuous (coherentTopology _) (coherentTopology _) := by
  rw [coherentTopology_is_induced F]
  apply LocallyCoverDense.inducedTopology_isCocontinuous

instance : haveI := finitaryExtensive_of_preserves_and_reflects F
    haveI : Preregular C := reflects_preregular F (fun X ↦ ⟨_, π F X, inferInstance⟩)
    F.IsContinuous (coherentTopology _) (coherentTopology _) :=
  Functor.IsCoverDense.isContinuous _ _ _ (coverPreserving F)

section SheafEquiv

universe u

variable {C D : Type (u+1)} [LargeCategory C] [LargeCategory D] (F : C ⥤ D)
  [F.PreservesEffectiveEpis] [F.ReflectsEffectiveEpis]
  [Preregular D] [Full F] [Faithful F]
  [FinitaryExtensive D] [Preregular D]
  [PreservesFiniteCoproducts F]
  [HasFiniteCoproducts C] [HasPullbacksOfInclusions C]
  [PreservesPullbacksOfInclusions F]
  [ReflectsLimitsOfShape WalkingCospan F]
  [ReflectsColimitsOfShape (Discrete WalkingPair) F]
  [F.EffectivelyEnough] [∀ (X : D), Projective X]

/-- The equivalence from coherent sheaves on `Stonean` to coherent sheaves on `CompHaus`
    (i.e. condensed sets). -/
noncomputable
def equivalence (A : Type _) [Category.{u+1} A] [HasLimits A] :
    haveI := finitaryExtensive_of_preserves_and_reflects F
    haveI : Preregular C := reflects_preregular F (fun X ↦ ⟨_, π F X, inferInstance⟩)
    Sheaf (coherentTopology C) A ≌ Sheaf (coherentTopology D) A :=
  Functor.IsCoverDense.sheafEquivOfCoverPreservingCoverLifting F _ _ _
