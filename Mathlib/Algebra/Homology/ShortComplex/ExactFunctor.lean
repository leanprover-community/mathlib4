/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Jujian Zhang
-/
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Exact functors

In this file, it is shown that additive functors which preserves homology
also preserves finite limits and finite colimits.

-/

namespace CategoryTheory

open Limits ZeroObject

namespace Functor

section

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology] [HasZeroObject C]

/-- An additive functor which preserves homology preserves finite limits. -/
noncomputable def preservesFiniteLimitsOfPreservesHomology
    [HasFiniteProducts C] [HasKernels C] : PreservesFiniteLimits F := by
  have := fun {X Y : C} (f : X ⟶ Y) => PreservesHomology.preservesKernel F f
  have : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryProducts
  have : HasEqualizers C := Preadditive.hasEqualizers_of_hasKernels
  have : HasZeroObject D :=
    ⟨F.obj 0, by rw [IsZero.iff_id_eq_zero, ← F.map_id, id_zero, F.map_zero]⟩
  exact preservesFiniteLimitsOfPreservesKernels F

/-- An additive which preserves homology preserves finite colimits. -/
noncomputable def preservesFiniteColimitsOfPreservesHomology
    [HasFiniteCoproducts C] [HasCokernels C] : PreservesFiniteColimits F := by
  have := fun {X Y : C} (f : X ⟶ Y) => PreservesHomology.preservesCokernel F f
  have : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryCoproducts
  have : HasCoequalizers C := Preadditive.hasCoequalizers_of_hasCokernels
  have : HasZeroObject D :=
    ⟨F.obj 0, by rw [IsZero.iff_id_eq_zero, ← F.map_id, id_zero, F.map_zero]⟩
  exact preservesFiniteColimitsOfPreservesCokernels F

end


section

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
variable (F : C ⥤ D) [F.Additive]

/--
If a functor `F : C ⥤ D` preserves exact sequences, then it preserves monomorphism.
-/
lemma preservesMonomorphisms_of_preserves_shortExact_left
    (h : ∀ (S : ShortComplex C), S.ShortExact → (S.map F).Exact ∧ Mono (F.map S.f)) :
    F.PreservesMonomorphisms where
  preserves {X Y} f m := by
    let S : ShortComplex C := .mk f (cokernel.π f) $ by simp
    have e : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ $ cokernelIsCokernel _
      mono_f := inferInstance
      epi_g := inferInstance }
    exact h S e |>.2

lemma preserves_finite_limits_tfae : List.TFAE
    [
      ∀ (S : ShortComplex C), S.ShortExact → (S.map F).Exact ∧ Mono (F.map S.f),
      ∀ (S : ShortComplex C), S.Exact ∧ Mono S.f → (S.map F).Exact ∧ Mono (F.map S.f),
      ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Nonempty $ PreservesLimit (parallelPair f 0) F,
      Nonempty $ PreservesFiniteLimits F
    ] := by
  tfae_have 1 → 2
  · rintro h S ⟨e1, m1⟩
    haveI := preservesMonomorphisms_of_preserves_shortExact_left F h
    refine ⟨?_, inferInstance⟩

    let s : ShortComplex C := .mk S.f (factorThruImage S.g) $
      by simp [← cancel_mono (image.ι S.g)]

    have se : s.ShortExact :=
    { exact := (by
        rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero] at e1 ⊢
        rw [show S.g = _ from image.fac S.g |>.symm] at e1
        simpa using ((kernelCompMono _ _).inv) ≫= e1)
      mono_f := inferInstance
      epi_g := inferInstance }

    have := (s.map F).exact_and_mono_f_iff_f_is_kernel.1 (h _ se) |>.some
    apply ShortComplex.exact_of_f_is_kernel
    simp only [ShortComplex.map_X₂, ShortComplex.map_X₃, ShortComplex.map_g, ShortComplex.map_X₁,
      ShortComplex.map_f] at this ⊢
    apply isKernelCompMono (i := this) (g := F.map $ image.ι S.g)
    simp [← F.map_comp]

  tfae_have 2 → 3
  · intro h X Y f
    refine ⟨⟨fun {c} hc => ?_⟩⟩
    have mono0 : Mono (c.π.app .zero) := mono_of_isLimit_fork hc
    let s : ShortComplex C := .mk (c.π.app .zero) f $ by simp
    have exact0 : s.Exact := by
      refine ShortComplex.exact_of_f_is_kernel _ $
        Limits.IsLimit.equivOfNatIsoOfIso (Iso.refl _) _ _ ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ hc
      · exact 𝟙 c.pt
      · rintro (⟨⟩|⟨⟩) <;> simp
      · exact 𝟙 c.pt
      · rintro (⟨⟩|⟨⟩) <;> simp
      · ext; simp
      · ext; simp

    refine Limits.IsLimit.equivOfNatIsoOfIso
      ⟨⟨fun | .zero => 𝟙 _ | .one => 𝟙 _, ?_⟩,
        ⟨fun | .zero => 𝟙 _ | .one => 𝟙 _, ?_⟩, ?_, ?_⟩ _ _
        ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ $
        ShortComplex.exact_and_mono_f_iff_f_is_kernel (s.map F) |>.1
          (h s ⟨exact0, mono0⟩) |>.some
    · rintro _ _ (⟨⟩ | ⟨⟩ | ⟨_⟩) <;> simp
    · rintro _ _ (⟨⟩ | ⟨⟩ | ⟨_⟩) <;> simp
    · ext (⟨⟩|⟨⟩) <;> simp
    · ext (⟨⟩|⟨⟩) <;> simp
    · exact 𝟙 _
    · rintro (⟨⟩ | ⟨⟩) <;> simp
    · exact 𝟙 _
    · rintro (⟨⟩ | ⟨⟩) <;> simp
    · ext; simp
    · ext; simp

  tfae_have 3 → 4
  · intro h; refine ⟨?_⟩
    apply (config := {allowSynthFailures := true}) preservesFiniteLimitsOfPreservesKernels
    exact fun {X Y} f => (h f).some

  tfae_have 4 → 1
  · rintro ⟨inst⟩ S hS
    refine (S.map F).exact_and_mono_f_iff_f_is_kernel |>.2 ⟨?_⟩
    have := S.exact_and_mono_f_iff_f_is_kernel.1 ⟨hS.exact, hS.mono_f⟩ |>.some
    have := isLimitOfPreserves F this
    refine Limits.IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ this
    · refine NatIso.ofComponents (fun
      | .zero => Iso.refl _
      | .one => Iso.refl _) ?_
      · rintro (_|_) (_|_) (_|_|_) <;> simp
    · refine ⟨?_, ?_, ?_, ?_⟩
      · refine ⟨𝟙 _, ?_⟩
        rintro (_|_) <;> simp [← F.map_comp]
      · refine ⟨𝟙 _, ?_⟩
        rintro (_|_) <;> simp [← F.map_comp]
      · ext; simp
      · ext; simp

  tfae_finish


/--
If a functor `F : C ⥤ D` preserves exact sequences, then it preserves monomorphism.
-/
lemma preservesEpimorphism_of_preserves_shortExact_right
    (h : ∀ (S : ShortComplex C), S.ShortExact → (S.map F).Exact ∧ Epi (F.map S.g)) :
    F.PreservesEpimorphisms where
  preserves {X Y} f e := by
    let S : ShortComplex C := .mk (kernel.ι f) f $ by simp
    have e : S.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ $ kernelIsKernel _
      mono_f := inferInstance
      epi_g := inferInstance }
    exact h S e |>.2

lemma preserves_finite_colimits_tfae : List.TFAE
    [
      ∀ (S : ShortComplex C), S.ShortExact → (S.map F).Exact ∧ Epi (F.map S.g),
      ∀ (S : ShortComplex C), S.Exact ∧ Epi S.g → (S.map F).Exact ∧ Epi (F.map S.g),
      ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Nonempty $ PreservesColimit (parallelPair f 0) F,
      Nonempty $ PreservesFiniteColimits F
    ] := by
  tfae_have 1 → 2
  · rintro h S ⟨e1, epi1⟩
    haveI := preservesEpimorphism_of_preserves_shortExact_right F h
    refine ⟨?_, inferInstance⟩
    have := factorThruImage S.g
    let s : ShortComplex C := .mk (image.ι S.f : image S.f ⟶ S.X₂) S.g $ by
      simp [← cancel_epi (factorThruImage S.f)]

    have se : s.ShortExact :=
    { exact := (by

        rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero] at e1 ⊢
        rw [show S.f = _ from image.fac S.f |>.symm] at e1
        simpa using e1 =≫ (cokernelEpiComp _ _).hom)
      mono_f := inferInstance
      epi_g := inferInstance }
    have := (s.map F).exact_and_epi_g_iff_g_is_cokernel.1 (h _ se) |>.some
    apply ShortComplex.exact_of_g_is_cokernel
    simp only [ShortComplex.map_X₂, ShortComplex.map_X₃, ShortComplex.map_g, ShortComplex.map_X₁,
      ShortComplex.map_f] at this ⊢
    apply isCokernelEpiComp (i := this) (g := F.map $ factorThruImage S.f)
    simp [← F.map_comp]

  tfae_have 2 → 3
  · intro h X Y f
    refine ⟨⟨fun {c} hc => ?_⟩⟩

    have epi0 : Epi (c.ι.app .one) := epi_of_isColimit_cofork hc
    let s : ShortComplex C := .mk f (c.ι.app .one) $ by simp
    have exact0 : s.Exact := by
      refine ShortComplex.exact_of_g_is_cokernel _ $
        Limits.IsColimit.equivOfNatIsoOfIso (Iso.refl _) _ _ ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ hc
      · exact 𝟙 c.pt
      · rintro (⟨⟩|⟨⟩) <;> simp
      · exact 𝟙 c.pt
      · rintro (⟨⟩|⟨⟩) <;> simp
      · ext; simp
      · ext; simp

    refine Limits.IsColimit.equivOfNatIsoOfIso
      ⟨⟨fun | .zero => 𝟙 _ | .one => 𝟙 _, ?_⟩,
        ⟨fun | .zero => 𝟙 _ | .one => 𝟙 _, ?_⟩, ?_, ?_⟩ _ _
        ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ $
        ShortComplex.exact_and_epi_g_iff_g_is_cokernel (s.map F) |>.1
          (h s ⟨exact0, epi0⟩) |>.some
    · rintro _ _ (⟨⟩ | ⟨⟩ | ⟨_⟩) <;> simp
    · rintro _ _ (⟨⟩ | ⟨⟩ | ⟨_⟩) <;> simp
    · ext (⟨⟩|⟨⟩) <;> simp
    · ext (⟨⟩|⟨⟩) <;> simp
    · exact 𝟙 _
    · rintro (⟨⟩ | ⟨⟩) <;> simp
    · exact 𝟙 _
    · rintro (⟨⟩ | ⟨⟩) <;> simp
    · ext; simp
    · ext; simp

  tfae_have 3 → 4
  · intro h; refine ⟨?_⟩
    apply (config := {allowSynthFailures := true}) preservesFiniteColimitsOfPreservesCokernels
    exact fun {X Y} f => (h f).some

  tfae_have 4 → 1
  · rintro ⟨inst⟩ S hS
    refine (S.map F).exact_and_epi_g_iff_g_is_cokernel |>.2 ⟨?_⟩
    have := S.exact_and_epi_g_iff_g_is_cokernel.1 ⟨hS.exact, hS.epi_g⟩ |>.some
    have := isColimitOfPreserves F this
    refine Limits.IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_ this
    · refine NatIso.ofComponents (fun
      | .zero => Iso.refl _
      | .one => Iso.refl _) ?_
      · rintro (_|_) (_|_) (_|_|_) <;> simp
    · refine ⟨?_, ?_, ?_, ?_⟩
      · refine ⟨𝟙 _, ?_⟩
        rintro (_|_) <;> simp [← F.map_comp]
      · refine ⟨𝟙 _, ?_⟩
        rintro (_|_) <;> simp [← F.map_comp]
      · ext; simp
      · ext; simp

  tfae_finish

open ZeroObject in
lemma preserves_shortComplex_shortExact_iff_preserves_finite_limit_colimit :
    (∀ (S : ShortComplex C), S.Exact → (S.map F).Exact) ↔
    Nonempty (PreservesFiniteLimits F) ∧ Nonempty (PreservesFiniteColimits F) := by
  constructor
  · intro h
    refine ⟨preserves_finite_limits_tfae F |>.out 1 3 |>.1 ?_,
      preserves_finite_colimits_tfae F |>.out 1 3 |>.1 ?_⟩
    · intro S ⟨hS1, hS2⟩
      refine ⟨h _ hS1, ?_⟩
      let s : ShortComplex C := .mk (0 : 0 ⟶ S.X₁) S.f $ by simp
      exact (s.map F).exact_iff_mono (by simp) |>.1 $ h s (s.exact_iff_mono rfl |>.2 hS2)
    · intro S ⟨hS1, hS2⟩
      refine ⟨h _ hS1, ?_⟩
      let s : ShortComplex C := .mk S.g (0 : S.X₃ ⟶ 0) $ by simp
      exact (s.map F).exact_iff_epi (by simp) |>.1 $ h s (s.exact_iff_epi rfl |>.2 hS2)
  · rintro ⟨⟨h1⟩, ⟨h2⟩⟩
    haveI : PreservesHomology F := inferInstance
    exact fun S hS => hS.map F

end

end Functor

end CategoryTheory
