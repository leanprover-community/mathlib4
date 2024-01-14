/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Nick Kuhn, Dagur Asgeirsson
-/
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Mathlib.Topology.Category.Stonean.EffectiveEpi
import Mathlib.Condensed.Basic
import Mathlib.CategoryTheory.Sites.DenseSubsite
import Mathlib.CategoryTheory.Sites.InducedTopology
import Mathlib.CategoryTheory.Sites.Closed
/-!
# Sheaves on CompHaus are equivalent to sheaves on Stonean

The forgetful functor from extremally disconnected spaces `Stonean` to compact
Hausdorff spaces `CompHaus` has the marvellous property that it induces an equivalence of categories
between sheaves on these two sites. With the terminology of nLab, `Stonean` is a
*dense subsite* of `CompHaus`: see https://ncatlab.org/nlab/show/dense+sub-site

Mathlib has isolated three properties called `CoverDense`, `CoverPreserving` and `CoverLifting`,
which between them imply that `Stonean` is a dense subsite, and it also has the
construction of the equivalence of the categories of sheaves, given these three properties.

## Main theorems

* `Condensed.StoneanCompHaus.isCoverDense`, `Condensed.StoneanCompHaus.coverPreserving`,
  `Condensed.StoneanCompHaus.coverLifting`: the three conditions needed to guarantee the equivalence
  of the categories of sheaves on the coherent site on `Stonean` on the one hand and `CompHaus` on
  the other.
* `Condensed.StoneanProfinite.coverDense`, `Condensed.StoneanProfinite.coverPreserving`,
  `Condensed.StoneanProfinite.coverLifting`: the corresponding conditions comparing the coherent
  sites on `Stonean` and `Profinite`.
* `Condensed.StoneanCompHaus.equivalence`: the equivalence from coherent sheaves on `Stonean` to
  coherent sheaves on `CompHaus` (i.e. condensed sets).
* `Condensed.StoneanProfinite.equivalence`: the equivalence from coherent sheaves on `Stonean` to
  coherent sheaves on `Profinite`.
* `Condensed.ProfiniteCompHaus.equivalence`: the equivalence from coherent sheaves on `Profinite` to
  coherent sheaves on `CompHaus` (i.e. condensed sets).
-/

open CategoryTheory Limits

namespace Condensed

universe u w

namespace StoneanCompHaus

open CompHaus in
lemma generate_singleton_mem_coherentTopology (B : CompHaus) :
    Sieve.generate (Presieve.singleton (presentation.π B)) ∈ coherentTopology CompHaus B := by
  apply Coverage.saturate.of
  refine ⟨Unit, inferInstance, fun _ => (Stonean.toCompHaus.obj B.presentation),
    fun _ => (presentation.π B), ?_ , ?_⟩
  · funext X f
    ext
    refine ⟨fun ⟨⟩ ↦ ⟨()⟩, ?_⟩
    rintro ⟨⟩
    simp only [Presieve.singleton_eq_iff_domain]
  · apply ((effectiveEpiFamily_tfae
      (fun (_ : Unit) => (Stonean.toCompHaus.obj B.presentation))
      (fun (_ : Unit) => (CompHaus.presentation.π B))).out 0 2).mpr
    intro b
    exact ⟨(), (CompHaus.epi_iff_surjective (presentation.π B)).mp (presentation.epi_π B) b⟩

open CompHaus in
instance isCoverDense : Stonean.toCompHaus.IsCoverDense (coherentTopology _)  := by
  constructor
  intro B
  convert generate_singleton_mem_coherentTopology B
  ext Y f
  refine ⟨fun ⟨⟨obj, lift, map, fact⟩⟩ ↦ ?_, fun ⟨Z, h, g, hypo1, hf⟩ ↦ ?_⟩
  · have : Projective (Stonean.toCompHaus.obj obj) -- Lean should find this instance?
    · simp only [Stonean.toCompHaus, inducedFunctor_obj]
      exact inferInstance
    obtain ⟨p, p_factors⟩ := Projective.factors map (CompHaus.presentation.π B)
    exact ⟨(Stonean.toCompHaus.obj (presentation B)), ⟨lift ≫ p, ⟨(presentation.π B),
      ⟨Presieve.singleton.mk, by rw [Category.assoc, p_factors, fact]⟩⟩⟩⟩
  · cases hypo1
    exact ⟨⟨presentation B, h, presentation.π B, hf⟩⟩

theorem coverDense.inducedTopology_Sieve_iff_EffectiveEpiFamily (X : Stonean) (S : Sieve X) :
    (∃ (α : Type) (_ : Fintype α) (Y : α → Stonean) (π : (a : α) → (Y a ⟶ X)),
    EffectiveEpiFamily Y π ∧ (∀ a : α, (S.arrows) (π a)) ) ↔
    (S ∈ Stonean.toCompHaus.inducedTopologyOfIsCoverDense (coherentTopology _) X) := by
  refine ⟨fun ⟨α, _, Y, π, ⟨H₁, H₂⟩⟩ ↦ ?_, fun hS ↦ ?_⟩
  · apply (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily (Sieve.functorPushforward _ S)).mpr
    refine ⟨α, inferInstance, fun i => Stonean.toCompHaus.obj (Y i),
      fun i => Stonean.toProfinite.map (π i), ⟨?_,
      fun a => Sieve.image_mem_functorPushforward Stonean.toCompHaus S (H₂ a)⟩⟩
    simp only [(Stonean.effectiveEpiFamily_tfae _ _).out 0 2] at H₁
    exact CompHaus.effectiveEpiFamily_of_jointly_surjective
        (fun i => Stonean.toCompHaus.obj (Y i)) (fun i => Stonean.toCompHaus.map (π i)) H₁
  · obtain ⟨α, _, Y, π, ⟨H₁, H₂⟩⟩ := (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily _).mp hS
    refine ⟨α, inferInstance, ?_⟩
    obtain ⟨Y₀, H₂⟩ := Classical.skolem.mp H₂
    obtain ⟨π₀, H₂⟩ := Classical.skolem.mp H₂
    obtain ⟨f₀, H₂⟩ := Classical.skolem.mp H₂
    refine ⟨Y₀ , π₀, ⟨?_, fun i ↦ (H₂ i).1⟩⟩
    simp only [(Stonean.effectiveEpiFamily_tfae _ _).out 0 2]
    simp only [(CompHaus.effectiveEpiFamily_tfae _ _).out 0 2] at H₁
    intro b
    obtain ⟨i, x, H₁⟩ := H₁ b
    refine ⟨i, f₀ i x, ?_⟩
    rw [← H₁, (H₂ i).2]
    rfl

lemma coherentTopology_is_induced :
    coherentTopology Stonean.{u} =
      Stonean.toCompHaus.inducedTopologyOfIsCoverDense (coherentTopology _) := by
  ext X S
  rw [← coverDense.inducedTopology_Sieve_iff_EffectiveEpiFamily X]
  rw [← coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily S]

lemma coverPreserving :
    CoverPreserving (coherentTopology _) (coherentTopology _) Stonean.toCompHaus := by
  rw [coherentTopology_is_induced]
  apply LocallyCoverDense.inducedTopology_coverPreserving

instance coverLifting :
    Stonean.toCompHaus.IsCocontinuous (coherentTopology _) (coherentTopology _) := by
  rw [coherentTopology_is_induced]
  apply LocallyCoverDense.inducedTopology_isCocontinuous

instance : Stonean.toCompHaus.IsContinuous (coherentTopology _) (coherentTopology _) :=
  Functor.IsCoverDense.isContinuous _ _ _ coverPreserving

/-- The equivalence from coherent sheaves on `Stonean` to coherent sheaves on `CompHaus`
    (i.e. condensed sets). -/
noncomputable
def equivalence (A : Type _) [Category.{u+1} A] [HasLimits A] :
    Sheaf (coherentTopology Stonean) A ≌ Condensed.{u} A :=
  Functor.IsCoverDense.sheafEquivOfCoverPreservingCoverLifting Stonean.toCompHaus _ _ _

end StoneanCompHaus

end Condensed

namespace Condensed

universe u w

namespace StoneanProfinite

open Profinite in
lemma generate_singleton_mem_coherentTopology (B : Profinite) :
    Sieve.generate (Presieve.singleton (presentation.π B)) ∈ coherentTopology Profinite B := by
  apply Coverage.saturate.of
  refine ⟨Unit, inferInstance, fun _ => (Stonean.toProfinite.obj B.presentation),
    fun _ => (presentation.π B), ?_ , ?_⟩
  · funext X f
    ext
    refine ⟨fun ⟨⟩ ↦ ⟨()⟩, ?_⟩
    rintro ⟨⟩
    simp only [Presieve.singleton_eq_iff_domain]
  · apply ((effectiveEpiFamily_tfae
      (fun (_ : Unit) => (Stonean.toProfinite.obj B.presentation))
      (fun (_ : Unit) => (Profinite.presentation.π B))).out 0 2).mpr
    intro b
    exact ⟨(), (Profinite.epi_iff_surjective (presentation.π B)).mp (presentation.epi_π B) b⟩

open Profinite in
instance coverDense : Stonean.toProfinite.IsCoverDense (coherentTopology _) := by
  constructor
  intro B
  convert generate_singleton_mem_coherentTopology B
  ext Y f
  refine ⟨fun ⟨⟨obj, lift, map, fact⟩⟩ ↦ ?_, fun ⟨Z, h, g, hypo1, hf⟩ ↦ ?_⟩
  · obtain ⟨p, p_factors⟩ := Projective.factors map (Profinite.presentation.π B)
    exact ⟨(Stonean.toProfinite.obj (presentation B)), ⟨lift ≫ p, ⟨(presentation.π B),
      ⟨Presieve.singleton.mk, by rw [Category.assoc, p_factors, fact]⟩⟩⟩⟩
  · cases hypo1
    exact ⟨⟨presentation B, h, presentation.π B, hf⟩⟩

theorem coverDense.inducedTopology_Sieve_iff_EffectiveEpiFamily (X : Stonean) (S : Sieve X) :
    (∃ (α : Type) (_ : Fintype α) (Y : α → Stonean) (π : (a : α) → (Y a ⟶ X)),
    EffectiveEpiFamily Y π ∧ (∀ a : α, (S.arrows) (π a)) ) ↔
    (S ∈ Stonean.toProfinite.inducedTopologyOfIsCoverDense (coherentTopology _) X) := by
  refine ⟨fun ⟨α, _, Y, π, ⟨H₁, H₂⟩⟩ ↦ ?_, fun hS ↦ ?_⟩
  · apply (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily (Sieve.functorPushforward _ S)).mpr
    refine ⟨α, inferInstance, fun i => Stonean.toProfinite.obj (Y i),
      fun i => Stonean.toProfinite.map (π i), ⟨?_,
      fun a => Sieve.image_mem_functorPushforward Stonean.toCompHaus S (H₂ a)⟩⟩
    simp only [(Stonean.effectiveEpiFamily_tfae _ _).out 0 2] at H₁
    exact Profinite.effectiveEpiFamily_of_jointly_surjective
        (fun i => Stonean.toProfinite.obj (Y i)) (fun i => Stonean.toProfinite.map (π i)) H₁
  · obtain ⟨α, _, Y, π, ⟨H₁, H₂⟩⟩ := (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily _).mp hS
    refine ⟨α, inferInstance, ?_⟩
    obtain ⟨Y₀, H₂⟩ := Classical.skolem.mp H₂
    obtain ⟨π₀, H₂⟩ := Classical.skolem.mp H₂
    obtain ⟨f₀, H₂⟩ := Classical.skolem.mp H₂
    refine ⟨Y₀ , π₀, ⟨?_, fun i ↦ (H₂ i).1⟩⟩
    simp only [(Stonean.effectiveEpiFamily_tfae _ _).out 0 2]
    simp only [(Profinite.effectiveEpiFamily_tfae _ _).out 0 2] at H₁
    intro b
    obtain ⟨i, x, H₁⟩ := H₁ b
    refine ⟨i, f₀ i x, ?_⟩
    rw [← H₁, (H₂ i).2]
    rfl

lemma coherentTopology_is_induced :
    coherentTopology Stonean.{u} =
      Stonean.toProfinite.inducedTopologyOfIsCoverDense (coherentTopology _) := by
  ext X S
  rw [← coverDense.inducedTopology_Sieve_iff_EffectiveEpiFamily X,
    ← coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily S]

lemma coverPreserving :
    CoverPreserving (coherentTopology _) (coherentTopology _) Stonean.toProfinite := by
  rw [coherentTopology_is_induced]
  apply LocallyCoverDense.inducedTopology_coverPreserving

instance isCocontinuous :
    Stonean.toProfinite.IsCocontinuous (coherentTopology _) (coherentTopology _) := by
  rw [coherentTopology_is_induced]
  apply LocallyCoverDense.inducedTopology_isCocontinuous

instance : Stonean.toProfinite.IsContinuous (coherentTopology _) (coherentTopology _) :=
  Functor.IsCoverDense.isContinuous _ _ _ coverPreserving

/-- The equivalence from coherent sheaves on `Stonean` to coherent sheaves on `Profinite`. -/
noncomputable
def equivalence (A : Type _) [Category.{u+1} A] [HasLimits A] :
    Sheaf (coherentTopology Stonean) A ≌ Sheaf (coherentTopology Profinite) A :=
  Functor.IsCoverDense.sheafEquivOfCoverPreservingCoverLifting Stonean.toProfinite _ _ _

end StoneanProfinite

/-- The equivalence from coherent sheaves on `Profinite` to coherent sheaves on `CompHaus`
    (i.e. condensed sets). -/
noncomputable
def ProfiniteCompHaus.equivalence (A : Type _) [Category.{u+1} A] [HasLimits A] :
    Sheaf (coherentTopology Profinite) A ≌ Condensed.{u} A :=
  (StoneanProfinite.equivalence A).symm.trans (StoneanCompHaus.equivalence A)

end Condensed
