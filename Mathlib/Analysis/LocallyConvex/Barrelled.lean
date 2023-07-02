/-
Copyright (c) 2023 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Semicontinuous

/-!
# Barrelled spaces
-/

open Bornology Set ContinuousLinearMap

section GeneralField

class BarrelledSpace (𝕜 E : Type _) [SeminormedRing 𝕜] [AddGroup E] [SMul 𝕜 E]
    [TopologicalSpace E] : Prop where
  continuous_of_lowerSemicontinuous : ∀ p : Seminorm 𝕜 E, LowerSemicontinuous p → Continuous p

theorem Seminorm.continuous_of_lowerSemicontinuous {𝕜 E : Type _} [AddGroup E] [SMul 𝕜 E]
    [SeminormedRing 𝕜] [TopologicalSpace E] [BarrelledSpace 𝕜 E] (p : Seminorm 𝕜 E)
    (hp : LowerSemicontinuous p) : Continuous p :=
  BarrelledSpace.continuous_of_lowerSemicontinuous p hp

theorem Seminorm.continuous_iSup {ι 𝕜 E : Type _} [NormedField 𝕜]  [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [BarrelledSpace 𝕜 E] (p : ι → Seminorm 𝕜 E)
    (hp : ∀ i, Continuous (p i)) (bdd : BddAbove (range p)) :
    Continuous (⨆ i, p i : Seminorm 𝕜 E) := by
  refine Seminorm.continuous_of_lowerSemicontinuous _ ?_
  rw [Seminorm.coe_iSup_eq bdd]
  rw [Seminorm.bddAbove_range_iff] at bdd
  convert lowerSemicontinuous_ciSup (f := fun i x ↦ p i x) bdd (fun i ↦ (hp i).lowerSemicontinuous)
  exact iSup_apply

theorem WithSeminorms.banach_steinhaus {ι κ 𝕜₁ 𝕜₂ E F : Type _} [Nonempty κ]
    [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
    {σ₁₂ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ₁₂]
    [AddCommGroup E] [AddCommGroup F] [Module 𝕜₁ E] [Module 𝕜₂ F] [UniformSpace E]
    [UniformSpace F] [UniformAddGroup E] [UniformAddGroup F] [ContinuousSMul 𝕜₁ E]
    [ContinuousSMul 𝕜₂ F] [BarrelledSpace 𝕜₁ E]
    {q : SeminormFamily 𝕜₂ F κ} {𝓕 : ι → E →SL[σ₁₂] F}
    (hq : WithSeminorms q) (H : ∀ k x, BddAbove (range fun i ↦ q k (𝓕 i x))) :
    UniformEquicontinuous ((↑) ∘ 𝓕) := by
  refine (hq.uniformEquicontinuous_iff_bddAbove_and_continuous_iSup ((toLinearMap) ∘ 𝓕)).mpr ?_
  intro k
  have : BddAbove (range fun i ↦ (q k).comp (𝓕 i).toLinearMap) := by
    rw [Seminorm.bddAbove_range_iff]
    exact H k
  exact ⟨this, Seminorm.continuous_iSup _
    (fun i ↦ (hq.continuous_seminorm k).comp (𝓕 i).continuous) this⟩

end GeneralField
