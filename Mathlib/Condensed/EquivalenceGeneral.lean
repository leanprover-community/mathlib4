import Mathlib.CategoryTheory.EffectiveEpi.Extensive
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.CategoryTheory.Sites.Coherent.CoherentTopology
import Mathlib.CategoryTheory.Sites.Coherent.Comparison
import Mathlib.CategoryTheory.Sites.InducedTopology
import Mathlib.CategoryTheory.Sites.Coherent.ReflectRegular


namespace CategoryTheory

open Limits

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
  [F.PreservesEffectiveEpis] [F.ReflectsEffectiveEpis]
  (h : ∀ (X : D), ∃ (W : C) (π : F.obj W ⟶ X), EffectiveEpi π)
  [Preregular D] [Full F] [Faithful F]
  [FinitaryExtensive D] [Preregular D]
  [PreservesFiniteCoproducts F]
  [HasFiniteCoproducts C] [HasPullbacksOfInclusions C]
  [PreservesPullbacksOfInclusions F]
  [ReflectsLimitsOfShape WalkingCospan F]
  [ReflectsColimitsOfShape (Discrete WalkingPair) F]

noncomputable section EffectivePresentation

structure Functor.EffectivePresentation (X : D) where
  p : C
  f : F.obj p ⟶ X
  effectiveEpi : EffectiveEpi f

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

instance π_effectiveEpi (X : D) : EffectiveEpi (π F X) :=
  (EffectivelyEnough.presentation X).some.effectiveEpi

end Projective'

end EffectivePresentation

variable [F.EffectivelyEnough] [∀ (X : D), Projective X]
-- variable [FinitaryExtensive (Projs C)] [Preregular (Projs C)]

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

-- Need the additional property that if a composition is effective epi, then the second map in
-- the composition is effective epi
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
    obtain ⟨Y₀, H₂⟩ := Classical.skolem.mp H₂
    obtain ⟨π₀, H₂⟩ := Classical.skolem.mp H₂
    obtain ⟨f₀, H₂⟩ := Classical.skolem.mp H₂
    refine ⟨Y₀ , π₀, ?_, fun i ↦ (H₂ i).1⟩
    refine F.finite_effectiveEpiFamily_of_map _ _ ?_
    sorry

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

-- Need to figure out the universes here
-- /-- The equivalence from coherent sheaves on `Stonean` to coherent sheaves on `CompHaus`
--     (i.e. condensed sets). -/
-- noncomputable
-- def equivalence (A : Type _) [Category A] [HasLimits A] :
--     haveI := finitaryExtensive_of_preserves_and_reflects F
--     haveI : Preregular C := sorry
--     Sheaf (coherentTopology C) A ≌ Sheaf (coherentTopology D) A :=
--   Functor.IsCoverDense.sheafEquivOfCoverPreservingCoverLifting F _ _ _
