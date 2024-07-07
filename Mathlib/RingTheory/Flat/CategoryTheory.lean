/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Homology.ShortComplex.Exact

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

lemma lTensor_shortComplex_exact [Flat R M] (C : ShortComplex $ ModuleCat R) (hC : C.Exact) :
    C.map (tensorLeft M) |>.Exact := by
  rw [ModuleCat.iff_shortComplex_exact, Eq.comm, ← LinearMap.exact_iff]
  exact lTensor_exact M $ LinearMap.exact_iff.2 $ Eq.symm $
    ModuleCat.iff_shortComplex_exact _ _ C.zero |>.1 hC

lemma rTensor_shortComplex_exact [Flat R M] (C : ShortComplex $ ModuleCat R) (hC : C.Exact) :
    C.map (tensorRight M) |>.Exact := by
  rw [ModuleCat.iff_shortComplex_exact, Eq.comm, ← LinearMap.exact_iff]
  exact rTensor_exact M $ LinearMap.exact_iff.2 $ Eq.symm $
    ModuleCat.iff_shortComplex_exact _ _ C.zero |>.1 hC

lemma iff_lTensor_preserves_shortComplex_exact :
    Flat R M ↔
    ∀ (C : ShortComplex $ ModuleCat R) (_ : C.Exact), (C.map (tensorLeft M) |>.Exact) :=
  ⟨fun _ _=> lTensor_shortComplex_exact _ _, fun H => by
    rw [iff_lTensor_exact]
    intro N N' N'' _ _ _ _ _ _ f g h
    specialize H (.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
      (DFunLike.ext _ _ h.apply_apply_eq_zero)) (ModuleCat.shortComplex_exact _ _ $ Eq.symm $
        LinearMap.exact_iff |>.1 $ h)
    rw [LinearMap.exact_iff, Eq.comm]
    rw [ModuleCat.iff_shortComplex_exact] at H
    convert H⟩

lemma iff_rTensor_preserves_shortComplex_exact :
    Flat R M ↔
    ∀ (C : ShortComplex $ ModuleCat R) (_ : C.Exact), (C.map (tensorRight M) |>.Exact) :=
  ⟨fun _ _=> rTensor_shortComplex_exact _ _, fun H => by
    rw [iff_rTensor_exact]
    intro N N' N'' _ _ _ _ _ _ f g h
    specialize H (.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
      (DFunLike.ext _ _ h.apply_apply_eq_zero)) (ModuleCat.shortComplex_exact _ _ $ Eq.symm $
        LinearMap.exact_iff |>.1 $ h)
    rw [LinearMap.exact_iff, Eq.comm]
    rw [ModuleCat.iff_shortComplex_exact] at H
    convert H⟩

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
    let s : ShortComplex (ModuleCat R) := .mk ι f $ by simp [ι]
    have exact0 : s.Exact:= by
      refine ShortComplex.exact_of_f_is_kernel _ $
        Limits.IsLimit.equivOfNatIsoOfIso (Iso.refl _) _ _ ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ hc
      · exact 𝟙 c.pt
      · rintro (⟨⟩|⟨⟩) <;> simp [ι]
      · exact 𝟙 c.pt
      · rintro (⟨⟩|⟨⟩) <;> simp [ι]
      · rfl
      · rfl

    let s' := s.map (tensorLeft M)
    let f' := M ◁ f; let ι' := M ◁ ι
    have exact1 : s'.Exact := by
      apply lTensor_shortComplex_exact; assumption

    have mono1 : Mono ι' := by

      rw [ModuleCat.mono_iff_injective] at mono0 ⊢
      exact lTensor_preserves_injective_linearMap _ mono0

    have := ShortComplex.exact_and_mono_f_iff_f_is_kernel s' |>.1 ⟨exact1, mono1⟩ |>.some
    -- convert this
    -- simp? [s']
    refine Limits.IsLimit.equivOfNatIsoOfIso
      ⟨⟨fun | .zero => 𝟙 _ | .one => 𝟙 _, ?_⟩,
        ⟨fun | .zero => 𝟙 _ | .one => 𝟙 _, ?_⟩, ?_, ?_⟩ _ _ ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ $
        this
        -- Abelian.isLimitOfExactOfMono ι' f' exact1
    · rintro _ _ (⟨⟩ | ⟨⟩ | ⟨_⟩) <;> simp [s']
    · rintro _ _ (⟨⟩ | ⟨⟩ | ⟨_⟩) <;> simp [s']
    · ext (⟨⟩|⟨⟩) <;> simp [s']
    · ext (⟨⟩|⟨⟩) <;> simp [s']
    · exact 𝟙 _
    · rintro (⟨⟩ | ⟨⟩) <;>

      simp only [ShortComplex.map_X₂, tensorLeft_obj, ShortComplex.map_X₃, ShortComplex.map_g,
        tensorLeft_map, Functor.comp_obj, Limits.parallelPair_obj_zero, Limits.parallelPair_obj_one,
        Functor.comp_map, Limits.walkingParallelPairHom_id, NatTrans.comp_app, NatTrans.id_app,
        ModuleCat.coe_comp, Function.comp_apply, ModuleCat.id_apply, ShortComplex.map_X₁,
        ShortComplex.map_f, Limits.Fork.app_zero_eq_ι, Limits.Cones.postcompose_obj_pt,
        Limits.Fork.ofι_pt, Functor.mapCone_pt, Functor.mapCone_π_app, Category.id_comp,
        Limits.Cones.postcompose_obj_π, Functor.const_obj_obj, Limits.Fork.ofι_π_app,
        Category.comp_id, s', ι]
      rw [← MonoidalCategory.whiskerLeft_comp]
      congr
      simp
  #exit
       -- [c]
      -- <;> simpa [ι', ι, f', Eq.comm] using exact1.w
    -- · exact 𝟙 _
    -- · rintro (⟨⟩ | ⟨⟩) <;> simpa [ι', ι, f', Eq.comm] using exact1.w
    -- · ext (⟨⟩ | ⟨⟩); simp [ι', ι, f']
    -- · ext (⟨⟩ | ⟨⟩); simp [ι', ι, f']

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
