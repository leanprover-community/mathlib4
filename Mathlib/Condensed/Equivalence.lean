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

* `Condensed.coverDense`, `Condensed.coverPreserving`, `Condensed.coverLifting`: the
three conditions needed to guarantee the equivalence of the categories of sheaves
on the two sites.
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
lemma coverDense : CoverDense (coherentTopology _) Stonean.toCompHaus := by
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
    (S ∈ coverDense.inducedTopology X) := by
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
    coherentTopology Stonean.{u} = coverDense.inducedTopology := by
  ext X S
  rw [← coverDense.inducedTopology_Sieve_iff_EffectiveEpiFamily X]
  rw [← coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily S]

lemma coverPreserving :
    CoverPreserving (coherentTopology _) (coherentTopology _) Stonean.toCompHaus := by
  rw [coherentTopology_is_induced]
  exact LocallyCoverDense.inducedTopology_coverPreserving (CoverDense.locallyCoverDense coverDense)

lemma coverLifting :
  CoverLifting (coherentTopology _) (coherentTopology _) Stonean.toCompHaus := by
  rw [coherentTopology_is_induced]
  exact LocallyCoverDense.inducedTopology_coverLifting (CoverDense.locallyCoverDense coverDense)

noncomputable
def equivalence (A : Type _) [Category.{u+1} A] [HasLimits A] :
    Sheaf (coherentTopology Stonean) A ≌ Condensed.{u} A :=
  CoverDense.sheafEquivOfCoverPreservingCoverLifting coverDense coverPreserving coverLifting

end StoneanCompHaus

end Condensed

namespace Stonean

/-- Every Stonean space is projective in `Profinite` -/
instance (X : Stonean) : Projective (toProfinite.obj X) where
  factors := by
    intro B C φ f _
    haveI : ExtremallyDisconnected (toProfinite.obj X) := X.extrDisc
    have hf : f.1.Surjective
    · rwa [Profinite.epi_iff_surjective] at *
    obtain ⟨f', h⟩ := CompactT2.ExtremallyDisconnected.projective φ.continuous f.continuous hf
    use ⟨f', h.left⟩
    ext
    exact congr_fun h.right _

end Stonean

namespace Profinite

instance {X Y : Profinite} (f : X ⟶ Y) [Epi f] : @Epi CompHaus _ _ _ f := by
  rwa [CompHaus.epi_iff_surjective, ← epi_iff_surjective]

instance {X Y : Profinite} (f : X ⟶ Y) [@Epi CompHaus _ _ _ f] : Epi f := by
  rwa [epi_iff_surjective, ← CompHaus.epi_iff_surjective]

/-- If `X` is compact Hausdorff, `presentation X` is an extremally disconnected space
  equipped with an epimorphism down to `X`. It is a "constructive" witness to the
  fact that `CompHaus` has enough projectives.  -/
noncomputable
def presentation (X : Profinite) : Stonean where
  compHaus := X.toCompHaus.projectivePresentation.p
  extrDisc := X.toCompHaus.presentation.extrDisc

/-- The morphism from `presentation X` to `X`. -/
noncomputable
def presentation.π (X : Profinite) : Stonean.toProfinite.obj X.presentation ⟶ X :=
  X.toCompHaus.projectivePresentation.f

/-- The morphism from `presentation X` to `X` is an epimorphism. -/
noncomputable
instance presentation.epi_π (X : Profinite) : Epi (π X) := by
  have := X.toCompHaus.projectivePresentation.epi
  rw [CompHaus.epi_iff_surjective] at this
  rw [Profinite.epi_iff_surjective]
  exact this

/--
```
               X
               |
              (f)
               |
               \/
  Z ---(e)---> Y
```
If `Z` is extremally disconnected, X, Y are profinite, if `f : X ⟶ Y` is an epi and
`e : Z ⟶ Y` is arbitrary, then `lift e f` is a fixed (but arbitrary) lift of `e` to a morphism
`Z ⟶ X`. It exists because `Z` is a projective object in `CompHaus`.
-/
noncomputable
def lift {X Y : Profinite} {Z : Stonean} (e : Stonean.toProfinite.obj Z ⟶ Y) (f : X ⟶ Y) [Epi f] :
    Stonean.toProfinite.obj Z ⟶ X := CompHaus.lift e f

@[simp, reassoc]
lemma lift_lifts {X Y : Profinite} {Z : Stonean} (e : Stonean.toProfinite.obj Z ⟶ Y) (f : X ⟶ Y)
    [Epi f] : lift e f ≫ f = e := CompHaus.lift_lifts _ _

lemma projective_of_extrDisc {X : Profinite} (hX : ExtremallyDisconnected X) :
    Projective X:= by
  let X' : Stonean := ⟨X.toCompHaus⟩
  show Projective (Stonean.toProfinite.obj X')
  exact inferInstance

end Profinite

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
lemma coverDense : CoverDense (coherentTopology _) Stonean.toProfinite := by
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
    (S ∈ coverDense.inducedTopology X) := by
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
    coherentTopology Stonean.{u} = coverDense.inducedTopology := by
  ext X S
  rw [← coverDense.inducedTopology_Sieve_iff_EffectiveEpiFamily X,
    ← coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily S]

lemma coverPreserving :
    CoverPreserving (coherentTopology _) (coherentTopology _) Stonean.toProfinite := by
  rw [coherentTopology_is_induced]
  exact LocallyCoverDense.inducedTopology_coverPreserving (CoverDense.locallyCoverDense coverDense)

lemma coverLifting :
    CoverLifting (coherentTopology _) (coherentTopology _) Stonean.toProfinite := by
  rw [coherentTopology_is_induced]
  exact LocallyCoverDense.inducedTopology_coverLifting (CoverDense.locallyCoverDense coverDense)

noncomputable
def equivalence (A : Type _) [Category.{u+1} A] [HasLimits A] :
    Sheaf (coherentTopology Stonean) A ≌ Sheaf (coherentTopology Profinite) A :=
  CoverDense.sheafEquivOfCoverPreservingCoverLifting coverDense coverPreserving coverLifting

end StoneanProfinite

noncomputable
def ProfiniteCompHaus.equivalence (A : Type _) [Category.{u+1} A] [HasLimits A] :
    Sheaf (coherentTopology Profinite) A ≌ Condensed.{u} A :=
  (StoneanProfinite.equivalence A).symm.trans (StoneanCompHaus.equivalence A)

end Condensed
