/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Jujian Zhang
-/
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Exact functors

In this file, it is shown that additive functors which preserves homology
also preserves finite limits and finite colimits.

## Main results

Let `F : C ⥤ D` be an additive functor:

- `Functor.preservesFiniteLimitsOfPreservesHomology`: if `F` preserves homology, then `F` preserves
  finite limits.
- `Functor.preservesFiniteColimitsOfPreservesHomology`: if `F` preserves homology, then `F`
  preserves finite colimits.

If we further assume that `C` and `D` are abelian categories, then we have:

- `Functor.preservesFiniteLimits_tfae`: the following are equivalent:
  1. for every short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0`,
    `0 ⟶ F(A) ⟶ F(B) ⟶ F(C) ⟶ 0` is exact.
  2. for every exact sequence `A ⟶ B ⟶ C` where `A ⟶ B` is mono,
    `F(A) ⟶ F(B) ⟶ F(C)` is exact and `F(A) ⟶ F(B)` is mono.
  3. `F` preserves kernels.
  4. `F` preserves finite limits.

- `Functor.preservesFiniteColimits_tfae`: the following are equivalent:
  1. for every short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0`,
    `F(A) ⟶ F(B) ⟶ F(C) ⟶ 0` is exact.
  2. for every exact sequence `A ⟶ B ⟶ C` where `B ⟶ C` is epi,
    `F(A) ⟶ F(B) ⟶ F(C)` is exact and `F(B) ⟶ F(C)` is epi.
  3. `F` preserves cokernels.
  4. `F` preserves finite colimits.

- `Functor.exact_tfae`: the following are equivalent:
  1. for every short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0`,
    `0 ⟶ F(A) ⟶ F(B) ⟶ F(C) ⟶ 0` is exact.
  2. for every exact sequence `A ⟶ B ⟶ C`, `F(A) ⟶ F(B) ⟶ F(C)` is exact.
  3. `F` preserves both finite limits and finite colimits.
  4. `F` preserves homology.

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
If a functor `F : C ⥤ D` preserves short exact sequences on the left hand side, (i.e.
if `0 ⟶ A ⟶ B ⟶ C ⟶ 0` is exact then `0 ⟶ F(A) ⟶ F(B) ⟶ F(C)` is exact)
then it preserves
monomorphism.
-/
lemma preservesMonomorphisms_of_preserves_shortExact_left
    (h : ∀ (S : ShortComplex C), S.ShortExact → (S.map F).Exact ∧ Mono (F.map S.f)) :
    F.PreservesMonomorphisms where
  preserves f := h _ { exact := ShortComplex.exact_cokernel f } |>.2

/--
For an addivite functor `F : C ⥤ D` between abelian categories, the following are equivalent:
- `F` preserves short exact sequences on the left hand side, i.e. if `0 ⟶ A ⟶ B ⟶ C ⟶ 0` is exact
  then `0 ⟶ F(A) ⟶ F(B) ⟶ F(C)` is exact.
- `F` preserves exact sequences on the left hand side, i.e. if `A ⟶ B ⟶ C` is exact where `A ⟶ B`
  is mono, then `F(A) ⟶ F(B) ⟶ F(C)` is exact and `F(A) ⟶ F(B)` is mono as well.
- `F` preserves kernels.
- `F` preserves finite limits.
-/
lemma preservesFiniteLimits_tfae : List.TFAE
    [
      ∀ (S : ShortComplex C), S.ShortExact → (S.map F).Exact ∧ Mono (F.map S.f),
      ∀ (S : ShortComplex C), S.Exact ∧ Mono S.f → (S.map F).Exact ∧ Mono (F.map S.f),
      ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Nonempty $ PreservesLimit (parallelPair f 0) F,
      Nonempty $ PreservesFiniteLimits F
    ] := by
  tfae_have 1 → 2
  · rintro hF S ⟨hS, hf⟩
    have := preservesMonomorphisms_of_preserves_shortExact_left F hF
    refine ⟨?_, inferInstance⟩
    let T := ShortComplex.mk S.f (Abelian.coimage.π S.g) (Abelian.comp_coimage_π_eq_zero S.zero)
    let φ : T.map F ⟶ S.map F :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := F.map (Abelian.factorThruCoimage S.g)
        comm₂₃ := by
          dsimp
          rw [Category.id_comp, ← F.map_comp, cokernel.π_desc] }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1
      (hF T { exact := (S.exact_iff_exact_coimage_π).1 hS }).1

  tfae_have 2 → 3
  · intro hF X Y f
    refine ⟨preservesLimitOfPreservesLimitCone (kernelIsKernel f) ?_⟩
    apply (KernelFork.isLimitMapConeEquiv _ F).2
    let S := ShortComplex.mk _ _ (kernel.condition f)
    let hS := hF S ⟨ShortComplex.exact_kernel f, by infer_instance⟩
    have : Mono (S.map F).f := hS.2
    exact hS.1.fIsKernel

  tfae_have 3 → 4
  · intro hF
    have := fun X Y (f : X ⟶ Y) ↦ (hF f).some
    exact ⟨by apply preservesFiniteLimitsOfPreservesKernels⟩

  tfae_have 4 → 1
  · rintro ⟨_⟩ S hS
    exact (S.map F).exact_and_mono_f_iff_f_is_kernel |>.2
      ⟨KernelFork.mapIsLimit _ hS.fIsKernel F⟩

  tfae_finish

/--
If a functor `F : C ⥤ D` preserves exact sequences on the right hand side (i.e.
if `0 ⟶ A ⟶ B ⟶ C ⟶ 0` is exact then `F(A) ⟶ F(B) ⟶ F(C) ⟶ 0` is exact),
then it preserves epimorphisms.
-/
lemma preservesEpimorphism_of_preserves_shortExact_right
    (h : ∀ (S : ShortComplex C), S.ShortExact → (S.map F).Exact ∧ Epi (F.map S.g)) :
    F.PreservesEpimorphisms where
  preserves f := h _ { exact := ShortComplex.exact_kernel f } |>.2

/--
For an addivite functor `F : C ⥤ D` between abelian categories, the following are equivalent:
- `F` preserves short exact sequences on the right hand side, i.e. if `0 ⟶ A ⟶ B ⟶ C ⟶ 0` is
  exact then `F(A) ⟶ F(B) ⟶ F(C) ⟶ 0` is exact.
- `F` preserves exact sequences on the right hand side, i.e. if `A ⟶ B ⟶ C` is exact where `B ⟶ C`
  is epi, then `F(A) ⟶ F(B) ⟶ F(C) ⟶ 0` is exact and `F(B) ⟶ F(C)` is epi as well.
- `F` preserves cokernels.
- `F` preserves finite colimits.
-/
lemma preservesFiniteColimits_tfae : List.TFAE
    [
      ∀ (S : ShortComplex C), S.ShortExact → (S.map F).Exact ∧ Epi (F.map S.g),
      ∀ (S : ShortComplex C), S.Exact ∧ Epi S.g → (S.map F).Exact ∧ Epi (F.map S.g),
      ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Nonempty $ PreservesColimit (parallelPair f 0) F,
      Nonempty $ PreservesFiniteColimits F
    ] := by
  tfae_have 1 → 2
  · rintro hF S ⟨hS, hf⟩
    have := preservesEpimorphism_of_preserves_shortExact_right F hF
    refine ⟨?_, inferInstance⟩
    let T := ShortComplex.mk (Abelian.image.ι S.f) S.g (Abelian.image_ι_comp_eq_zero S.zero)
    let φ : S.map F ⟶ T.map F :=
      { τ₁ := F.map $ (Abelian.factorThruImage S.f)
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by
          dsimp
          rw [← F.map_comp, Abelian.image.fac, Category.comp_id] }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
      (hF T { exact := (S.exact_iff_exact_image_ι).1 hS }).1

  tfae_have 2 → 3
  · intro hF X Y f
    refine ⟨preservesColimitOfPreservesColimitCocone (cokernelIsCokernel f) ?_⟩
    apply (CokernelCofork.isColimitMapCoconeEquiv _ F).2
    let S := ShortComplex.mk _ _ (cokernel.condition f)
    let hS := hF S ⟨ShortComplex.exact_cokernel f, by infer_instance⟩
    have : Epi (S.map F).g := hS.2
    exact hS.1.gIsCokernel

  tfae_have 3 → 4
  · intro hF
    have := fun X Y (f : X ⟶ Y) ↦ (hF f).some
    exact ⟨by apply preservesFiniteColimitsOfPreservesCokernels⟩

  tfae_have 4 → 1
  · rintro ⟨_⟩ S hS
    exact (S.map F).exact_and_epi_g_iff_g_is_cokernel |>.2
      ⟨CokernelCofork.mapIsColimit _ hS.gIsCokernel F⟩

  tfae_finish

open ZeroObject in
/--
For an additive functor `F : C ⥤ D` between abelian categories, the following are equivalent:
- `F` preserves short exact sequences, i.e. if `0 ⟶ A ⟶ B ⟶ C ⟶ 0` is exact then
  `0 ⟶ F(A) ⟶ F(B) ⟶ F(C) ⟶ 0` is exact.
- `F` preserves exact sequences, i.e. if `A ⟶ B ⟶ C` is exact then `F(A) ⟶ F(B) ⟶ F(C)` is exact.
- `F` preserves both finite limits and finite colimits.
- `F` preserves homology.
-/
lemma exact_tfae : List.TFAE
    [
      ∀ (S : ShortComplex C), S.ShortExact → (S.map F).ShortExact,
      ∀ (S : ShortComplex C), S.Exact → (S.map F).Exact,
      Nonempty (PreservesFiniteLimits F) ∧ Nonempty (PreservesFiniteColimits F),
      Nonempty (PreservesHomology F)
    ] := by
  tfae_have 1 → 4
  · intro hF
    refine ⟨fun {X Y} f => ?_, fun {X Y} f => ?_⟩
    · have h := (preservesFiniteLimits_tfae F |>.out 0 2 |>.1 fun S hS =>
        And.intro (hF S hS).exact (hF S hS).mono_f)
      exact h f |>.some
    · have h := (preservesFiniteColimits_tfae F |>.out 0 2 |>.1 fun S hS =>
        And.intro (hF S hS).exact (hF S hS).epi_g)
      exact h f |>.some

  tfae_have 2 → 1
  · intro hF S hS
    have : Mono (S.map F).f := ShortComplex.exact_iff_mono _ (by simp) |>.1 $
        hF (.mk (0 : 0 ⟶ S.X₁) S.f $ by simp)
          (ShortComplex.exact_iff_mono _ (by simp) |>.2 hS.mono_f)
    have : Epi (S.map F).g := ShortComplex.exact_iff_epi _ (by simp) |>.1 $
        hF (.mk S.g (0 : S.X₃ ⟶ 0) $ by simp)
          (ShortComplex.exact_iff_epi _ (by simp) |>.2 hS.epi_g)
    exact ⟨hF S hS.exact⟩

  tfae_have 2 → 3
  · intro hF
    refine ⟨preservesFiniteLimits_tfae F |>.out 1 3 |>.1 ?_,
      preservesFiniteColimits_tfae F |>.out 1 3 |>.1 ?_⟩
    · intro S ⟨hS1, hS2⟩
      refine ⟨hF _ hS1, ?_⟩
      let s : ShortComplex C := .mk (0 : 0 ⟶ S.X₁) S.f $ by simp
      exact (s.map F).exact_iff_mono (by simp) |>.1 $ hF s (s.exact_iff_mono rfl |>.2 hS2)
    · intro S ⟨hS1, hS2⟩
      refine ⟨hF _ hS1, ?_⟩
      let s : ShortComplex C := .mk S.g (0 : S.X₃ ⟶ 0) $ by simp
      exact (s.map F).exact_iff_epi (by simp) |>.1 $ hF s (s.exact_iff_epi rfl |>.2 hS2)

  tfae_have 3 → 4
  · rintro ⟨⟨_⟩, ⟨_⟩⟩
    exact ⟨inferInstance⟩
  tfae_have 4 → 3
  · rintro ⟨h⟩
    exact ⟨⟨preservesFiniteLimitsOfPreservesHomology F⟩,
      ⟨preservesFiniteColimitsOfPreservesHomology F⟩⟩

  tfae_have 3 → 2
  · rintro ⟨⟨h1⟩, ⟨h2⟩⟩
    haveI : PreservesHomology F := inferInstance
    exact fun _ h => h.map F

  tfae_finish

end

end Functor

end CategoryTheory
