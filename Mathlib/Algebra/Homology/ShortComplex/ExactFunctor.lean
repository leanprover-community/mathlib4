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
def preservesMonomorphismsOfPreservesShortComplexExact
    (h : ∀ (S : ShortComplex C), S.Exact → (S.map F).Exact) :
    F.PreservesMonomorphisms where
  preserves {X Y} f m :=
    ShortComplex.exact_iff_mono (hf := by simp) |>.1 $ h _ $
      ShortComplex.exact_iff_mono (.mk (0 : 0 ⟶ X) f (by simp)) rfl |>.2 m

/--
If a functor `F : C ⥤ D` preserves exact sequences, then it preserves epimorphism.
-/
def preservesEpimorphismsOfPreservesShortComplexExact
    (h : ∀ (S : ShortComplex C), S.Exact → (S.map F).Exact) :
    F.PreservesEpimorphisms where
  preserves {X Y} f e :=
    ShortComplex.exact_iff_epi (hg := by simp) |>.1 $ h _ $
      ShortComplex.exact_iff_epi (.mk f (0 : Y ⟶ 0) (by simp)) rfl |>.2 e

/--
If a functor `F : C ⥤ D` preserves exact sequences, then it preserves short exact sequences.
-/
lemma preserves_shortComplex_shortExact_of_preserves_shortComplex_exact
    (h : ∀ (S : ShortComplex C), S.Exact → (S.map F).Exact)
    (S : ShortComplex C) (hS : S.ShortExact) : (S.map F).ShortExact where
  exact := h _ hS.exact
  mono_f :=
    letI := F.preservesMonomorphismsOfPreservesShortComplexExact h
    letI : Mono S.f := hS.mono_f
    map_mono _ _
  epi_g :=
    letI := F.preservesEpimorphismsOfPreservesShortComplexExact h
    letI : Epi S.g := hS.epi_g
    map_epi _ _

set_option maxHeartbeats 500000 in
/--
If a functor `F : C ⥤ D` preserves exact sequences, then it preserves kernels.
-/
noncomputable def preservesKernelsOfPreservesShortComplexExact
    (h : ∀ (S : ShortComplex C), S.Exact → (S.map F).Exact)
    (X Y : C) (f : X ⟶ Y) : PreservesLimit (parallelPair f 0) F where
  preserves {c} hc := by
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

    have : F.PreservesMonomorphisms := F.preservesMonomorphismsOfPreservesShortComplexExact h
    have exact1 : (s.map F).Exact := h s exact0
    have mono1 : Mono (F.map $ c.π.app .zero) := inferInstance

    refine Limits.IsLimit.equivOfNatIsoOfIso
      ⟨⟨fun | .zero => 𝟙 _ | .one => 𝟙 _, ?_⟩,
        ⟨fun | .zero => 𝟙 _ | .one => 𝟙 _, ?_⟩, ?_, ?_⟩ _ _
        ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ $
        ShortComplex.exact_and_mono_f_iff_f_is_kernel (s.map F) |>.1
          ⟨exact1, mono1⟩ |>.some
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

/--
If a functor `F : C ⥤ D` preserves exact sequences, then it preserves finite limits.
-/
noncomputable def preservesFiniteLimitOfPreservesShortComplexExact
    (h : ∀ (S : ShortComplex C), S.Exact → (S.map F).Exact) : PreservesFiniteLimits F := by
  apply (config := {allowSynthFailures := true}) preservesFiniteLimitsOfPreservesKernels
  apply preservesKernelsOfPreservesShortComplexExact
  assumption

set_option maxHeartbeats 500000 in
/--
If a functor `F : C ⥤ D` preserves exact sequences, then it preserves cokernels.
-/
noncomputable def preservesCokernelsOfPreservesShortComplexExact
    (h : ∀ (S : ShortComplex C), S.Exact → (S.map F).Exact)
    (X Y : C) (f : X ⟶ Y) :
    PreservesColimit (parallelPair f 0) F where
  preserves {c} hc := by
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

    have : F.PreservesEpimorphisms := F.preservesEpimorphismsOfPreservesShortComplexExact h
    have exact1 : (s.map F).Exact := h s exact0
    have epi1 : Epi (F.map $ c.ι.app .one) := inferInstance
    refine IsColimit.equivOfNatIsoOfIso
      ⟨⟨fun | .zero => 𝟙 _ | .one => 𝟙 _, ?_⟩,
        ⟨fun | .zero => 𝟙 _ | .one => 𝟙 _, ?_⟩, ?_, ?_⟩ _ _
        ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ $
        ShortComplex.exact_and_epi_g_iff_g_is_cokernel (s.map F) |>.1
          ⟨exact1, epi1⟩ |>.some
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

/--
If a functor `F : C ⥤ D` preserves exact sequences, then it preserves finite colimits.
-/
noncomputable def preservesFiniteColimitOfPreservesShortComplexExact
    (h : ∀ (S : ShortComplex C), S.Exact → (S.map F).Exact) : PreservesFiniteColimits F := by
  apply (config := {allowSynthFailures := true}) preservesFiniteColimitsOfPreservesCokernels
  apply preservesCokernelsOfPreservesShortComplexExact
  assumption

/--
If a functor `F : C ⥤ D` preserves exact sequences, then it preserves homology.
-/
noncomputable def preservesHomologyOfPreservesShortComplexExact
    (h : ∀ (S : ShortComplex C), S.Exact → (S.map F).Exact) : F.PreservesHomology :=
  ⟨preservesKernelsOfPreservesShortComplexExact F h,
    preservesCokernelsOfPreservesShortComplexExact F h⟩

lemma preserves_shortComplexExact_iff_preserves_homology :
    (∀ (S : ShortComplex C), S.Exact → (S.map F).Exact) ↔ Nonempty F.PreservesHomology :=
  ⟨fun h => ⟨preservesHomologyOfPreservesShortComplexExact F h⟩, fun ⟨_⟩ _ h =>
    ShortComplex.Exact.map_of_preservesRightHomologyOf h _⟩

lemma preserves_shortComplex_shortExact_iff_preserves_finite_limit_colimit :
    (∀ (S : ShortComplex C), S.Exact → (S.map F).Exact) ↔
    Nonempty (PreservesFiniteLimits F) ∧ Nonempty (PreservesFiniteColimits F) :=
  ⟨fun h => ⟨⟨preservesFiniteLimitOfPreservesShortComplexExact F h⟩,
    ⟨preservesFiniteColimitOfPreservesShortComplexExact F h⟩⟩,
    fun ⟨⟨_⟩, ⟨_⟩⟩ => preserves_shortComplexExact_iff_preserves_homology F |>.2
      ⟨inferInstance⟩⟩

end

end Functor

end CategoryTheory
