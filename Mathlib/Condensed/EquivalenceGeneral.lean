import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.CategoryTheory.Sites.Coherent.CoherentTopology
import Mathlib.CategoryTheory.Sites.Coherent.Comparison
import Mathlib.CategoryTheory.Sites.InducedTopology

namespace CategoryTheory

variable {C : Type*} [Category C] [FinitaryExtensive C] [Preregular C]

noncomputable section EffectivelyEnoughProjectives

structure EffectiveProjectivePresentation (X : C) where
  p : C
  projective : Projective p
  f : p ⟶ X
  effectiveEpi : EffectiveEpi f

variable (C) in
class EffectivelyEnoughProjectives : Prop where
  presentation : ∀ (X : C), Nonempty (EffectiveProjectivePresentation X)

namespace Projective'

variable [EffectivelyEnoughProjectives C]

/-- `Projective.over X` provides an arbitrarily chosen projective object equipped with
an epimorphism `Projective.π : Projective.over X ⟶ X`.
-/
def over (X : C) : C :=
  (EffectivelyEnoughProjectives.presentation X).some.p

instance projective_over (X : C) : Projective (over X) :=
  (EffectivelyEnoughProjectives.presentation X).some.projective

/-- The epimorphism `projective.π : projective.over X ⟶ X`
from the arbitrarily chosen projective object over `X`.
-/
def π (X : C) : over X ⟶ X :=
  (EffectivelyEnoughProjectives.presentation X).some.f

instance π_effectiveEpi (X : C) : EffectiveEpi (π X) :=
  (EffectivelyEnoughProjectives.presentation X).some.effectiveEpi

end Projective'

end EffectivelyEnoughProjectives

local notation "Projs" C => FullSubcategory (fun (X : C) ↦ Projective X)
local notation "projsIncl" C => fullSubcategoryInclusion (fun (X : C) ↦ Projective X)

variable [EffectivelyEnoughProjectives C]
variable [FinitaryExtensive (Projs C)] [Preregular (Projs C)]

open Projective'

namespace Ciao

lemma generate_singleton_mem_coherentTopology (B : C) :
    Sieve.generate (Presieve.singleton (π B)) ∈ coherentTopology C B := by
  apply Coverage.saturate.of
  refine ⟨Unit, inferInstance, fun _ => over B,
    fun _ => π B, ?_ , ?_⟩
  · funext X f
    ext
    refine ⟨fun ⟨⟩ ↦ ⟨()⟩, ?_⟩
    rintro ⟨⟩
    simp only [Presieve.singleton_eq_iff_domain]
  · rw [← effectiveEpi_iff_effectiveEpiFamily]
    exact π_effectiveEpi _

instance isCoverDense : (projsIncl C).IsCoverDense (coherentTopology _) := by
  constructor
  intro B
  convert generate_singleton_mem_coherentTopology B
  ext Y f
  refine ⟨fun ⟨⟨obj, lift, map, fact⟩⟩ ↦ ?_, fun ⟨Z, h, g, hypo1, hf⟩ ↦ ?_⟩
  · have : Projective ((projsIncl C).obj obj) := obj.property
    obtain ⟨p, p_factors⟩ := Projective.factors map (π B)
    refine ⟨((projsIncl C).obj (⟨over B, inferInstance⟩)), ⟨lift ≫ p, ⟨(π B),
      ⟨Presieve.singleton.mk, by rw [← fact, ← p_factors, Category.assoc]⟩⟩⟩⟩
  · cases hypo1
    exact ⟨⟨⟨over B, inferInstance⟩, h, π B, hf⟩⟩

-- theorem coverDense.inducedTopology_Sieve_iff_EffectiveEpiFamily (X : Projs C) (S : Sieve X) :
--     (∃ (α : Type) (_ : Finite α) (Y : α → Projs C) (π : (a : α) → (Y a ⟶ X)),
--       EffectiveEpiFamily Y π ∧ (∀ a : α, (S.arrows) (π a)) ) ↔
--     (S ∈ (projsIncl C).inducedTopologyOfIsCoverDense (coherentTopology _) X) := by
--   refine ⟨fun ⟨α, _, Y, π, ⟨H₁, H₂⟩⟩ ↦ ?_, fun hS ↦ ?_⟩
--   · apply (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily (Sieve.functorPushforward _ S)).mpr
--     refine ⟨α, inferInstance, fun i => (projsIncl C).obj (Y i),
--       fun i => (projsIncl C).map (π i), ⟨?_,
--       fun a => Sieve.image_mem_functorPushforward (projsIncl C) S (H₂ a)⟩⟩
--     simp only [(Stonean.effectiveEpiFamily_tfae _ _).out 0 2] at H₁
--     exact CompHaus.effectiveEpiFamily_of_jointly_surjective
--         (fun i => Stonean.toCompHaus.obj (Y i)) (fun i => Stonean.toCompHaus.map (π i)) H₁
--   · obtain ⟨α, _, Y, π, ⟨H₁, H₂⟩⟩ := (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily _).mp hS
--     refine ⟨α, inferInstance, ?_⟩
--     obtain ⟨Y₀, H₂⟩ := Classical.skolem.mp H₂
--     obtain ⟨π₀, H₂⟩ := Classical.skolem.mp H₂
--     obtain ⟨f₀, H₂⟩ := Classical.skolem.mp H₂
--     refine ⟨Y₀ , π₀, ⟨?_, fun i ↦ (H₂ i).1⟩⟩
--     simp only [(Stonean.effectiveEpiFamily_tfae _ _).out 0 2]
--     simp only [(CompHaus.effectiveEpiFamily_tfae _ _).out 0 2] at H₁
--     intro b
--     obtain ⟨i, x, H₁⟩ := H₁ b
--     refine ⟨i, f₀ i x, ?_⟩
--     rw [← H₁, (H₂ i).2]
--     rfl

-- lemma coherentTopology_is_induced :
--     coherentTopology Stonean.{u} =
--       Stonean.toCompHaus.inducedTopologyOfIsCoverDense (coherentTopology _) := by
--   ext X S
--   rw [← coverDense.inducedTopology_Sieve_iff_EffectiveEpiFamily X]
--   rw [← coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily S]

-- lemma coverPreserving :
--     CoverPreserving (coherentTopology _) (coherentTopology _) Stonean.toCompHaus := by
--   rw [coherentTopology_is_induced]
--   apply LocallyCoverDense.inducedTopology_coverPreserving

-- instance coverLifting :
--     Stonean.toCompHaus.IsCocontinuous (coherentTopology _) (coherentTopology _) := by
--   rw [coherentTopology_is_induced]
--   apply LocallyCoverDense.inducedTopology_isCocontinuous

-- instance : Stonean.toCompHaus.IsContinuous (coherentTopology _) (coherentTopology _) :=
--   Functor.IsCoverDense.isContinuous _ _ _ coverPreserving

-- /-- The equivalence from coherent sheaves on `Stonean` to coherent sheaves on `CompHaus`
--     (i.e. condensed sets). -/
-- noncomputable
-- def equivalence (A : Type _) [Category.{u+1} A] [HasLimits A] :
--     Sheaf (coherentTopology Stonean) A ≌ Condensed.{u} A :=
--   Functor.IsCoverDense.sheafEquivOfCoverPreservingCoverLifting Stonean.toCompHaus _ _ _
