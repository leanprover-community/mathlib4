/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Monoidal.Tor

/-!
# Tensoring with a flat module is an exact functor

In this file we prove that tensoring with a flat module is an exact functor.

## Main results
- `Module.Flat.iff_tensorLeft_preservesFiniteLimits`: an `R`-module `M` is flat if and only if
  left tensoring with `M` preserves finite limits, i.e. the functor `- ⊗ M` is left exact.

- `Module.Flat.iff_tensorRight_preservesFiniteLimits`: an `R`-module `M` is flat if and only if
  right tensoring with `M` preserves finite limits, i.e. the functor `M ⊗ -` is left exact.

- `Module.Flat.higherTorIsoZero`: if an `R`-module `M` is flat, then `Torⁿ(M, N) ≅ 0` for all `N`
  and all `n ≥ 1`.

## TODO

- Prove that vanishing `Tor`-groups implies flat.

-/

universe u

open CategoryTheory MonoidalCategory Abelian

namespace Module.Flat

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R)

open scoped MonoidalCategory in
set_option maxHeartbeats 400000 in
-- In two goals, we need to use `simpa` in one; and `simp` in the other.
set_option linter.unnecessarySimpa false in
noncomputable instance [flat : Flat R M] {X Y : ModuleCat.{u} R} (f : X ⟶ Y) :
    Limits.PreservesLimit (Limits.parallelPair f 0) (tensorLeft M) where
  preserves {c} hc := by
    let ι : c.pt ⟶ X := c.π.app .zero
    have mono0 : Mono ι :=
      { right_cancellation := fun {Z} g h H => by
          let c' : Limits.Cone (Limits.parallelPair f 0) :=
          ⟨Z, ⟨fun | .zero => h ≫ ι | .one => 0, by rintro _ _ (⟨j⟩|⟨j⟩) <;> simpa [ι] using H⟩⟩

          rw [hc.uniq c' g, hc.uniq c' h] <;>
          rintro (⟨j⟩|⟨j⟩) <;> simpa [ι] using H }
    have exact0 : Exact ι f := by
      refine Abelian.exact_of_is_kernel (w := by simp [ι])
        (h := Limits.IsLimit.equivOfNatIsoOfIso (Iso.refl _) _ _
          ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ hc)
      · exact 𝟙 c.pt
      · rintro (⟨⟩|⟨⟩) <;> simp [ι]
      · exact 𝟙 c.pt
      · rintro (⟨⟩|⟨⟩) <;> simp [ι]
      · rfl
      · rfl

    let f' := M ◁ f; let ι' := M ◁ ι
    have exact1 : Exact ι' f' := by
      rw [ModuleCat.exact_iff, Eq.comm, ← LinearMap.exact_iff] at exact0 ⊢
      exact lTensor_exact M exact0
    have mono1 : Mono ι' := by
      rw [ModuleCat.mono_iff_injective] at mono0 ⊢
      exact lTensor_preserves_injective_linearMap _ mono0

    refine Limits.IsLimit.equivOfNatIsoOfIso
      ⟨⟨fun | .zero => 𝟙 _ | .one => 𝟙 _, ?_⟩,
        ⟨fun | .zero => 𝟙 _ | .one => 𝟙 _, ?_⟩, ?_, ?_⟩ _ _ ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ $
        Abelian.isLimitOfExactOfMono ι' f' exact1
    · rintro _ _ (⟨⟩ | ⟨⟩ | ⟨_⟩) <;> simp
    · rintro _ _ (⟨⟩ | ⟨⟩ | ⟨_⟩) <;> simp
    · ext (⟨⟩|⟨⟩) <;> simp
    · ext (⟨⟩|⟨⟩) <;> simp
    · exact 𝟙 _
    · rintro (⟨⟩ | ⟨⟩) <;> simpa [ι', ι, f', Eq.comm] using exact1.w
    · exact 𝟙 _
    · rintro (⟨⟩ | ⟨⟩) <;> simpa [ι', ι, f', Eq.comm] using exact1.w
    · ext (⟨⟩ | ⟨⟩); simp [ι', ι, f']
    · ext (⟨⟩ | ⟨⟩); simp [ι', ι, f']

noncomputable instance tensorLeft_preservesFiniteLimits [Flat R M] :
    Limits.PreservesFiniteLimits (tensorLeft M) :=
  (tensorLeft M).preservesFiniteLimitsOfPreservesKernels

noncomputable instance tensorRight_preservesFiniteLimits [Flat R M] :
    Limits.PreservesFiniteLimits (tensorRight M) where
  preservesFiniteLimits J _ _ :=
  { preservesLimit := fun {K} => by
      letI : Limits.PreservesLimit K (tensorLeft M) := inferInstance
      apply Limits.preservesLimitOfNatIso (F := tensorLeft M)
      exact ⟨⟨fun X => β_ _ _ |>.hom, by aesop_cat⟩, ⟨fun X => β_ _ _ |>.inv, by aesop_cat⟩,
        by aesop_cat, by aesop_cat⟩ }

lemma iff_tensorLeft_preservesFiniteLimits :
    Flat R M ↔
    Nonempty (Limits.PreservesFiniteLimits (tensorLeft M)) :=
  ⟨fun _ => ⟨inferInstance⟩, fun ⟨_⟩ => iff_lTensor_preserves_injective_linearMap _ _ |>.2
    fun N N' _ _ _ _ L hL => by
      haveI : Mono (ModuleCat.ofHom L) := by rwa [ModuleCat.mono_iff_injective]
      have inj : Mono <| (tensorLeft M).map (ModuleCat.ofHom L) :=
        preserves_mono_of_preservesLimit (tensorLeft M) (ModuleCat.ofHom L)
      rwa [ModuleCat.mono_iff_injective] at inj⟩

lemma iff_tensorRight_preservesFiniteLimits :
    Flat R M ↔
    Nonempty (Limits.PreservesFiniteLimits (tensorRight M)) :=
  ⟨fun _ => ⟨inferInstance⟩, fun ⟨_⟩ => iff_rTensor_preserves_injective_linearMap _ _ |>.2
    fun N N' _ _ _ _ L hL => by
    haveI : Mono (ModuleCat.ofHom L) := by rwa [ModuleCat.mono_iff_injective]
    have inj : Mono <| (tensorRight M).map (ModuleCat.ofHom L) :=
      preserves_mono_of_preservesLimit (tensorRight M) (ModuleCat.ofHom L)
    rwa [ModuleCat.mono_iff_injective] at inj⟩

section Tor

open scoped ZeroObject

/--
For a flat module `M`, higher tor groups vanish.
-/
noncomputable def higherTorIsoZero [flat : Flat R M] (n : ℕ) (N : ModuleCat.{u} R) :
    ((Tor' _ (n + 1)).obj N).obj M ≅ 0 := by
  dsimp [Tor', Functor.flip]
  let pN := ProjectiveResolution.of N
  refine' pN.isoLeftDerivedObj (tensorRight M) (n + 1) ≪≫ ?_
  refine Limits.IsZero.isoZero ?_
  dsimp only [HomologicalComplex.homologyFunctor_obj]
  rw [← HomologicalComplex.exactAt_iff_isZero_homology, HomologicalComplex.exactAt_iff,
    ← exact_iff_shortComplex_exact, ModuleCat.exact_iff, Eq.comm, ← LinearMap.exact_iff]
  refine iff_rTensor_exact |>.1 flat ?_
  rw [LinearMap.exact_iff, Eq.comm, ← ModuleCat.exact_iff]
  have := pN.complex_exactAt_succ n
  rw [HomologicalComplex.exactAt_iff, ← exact_iff_shortComplex_exact] at this
  exact this

end Tor

end Module.Flat
