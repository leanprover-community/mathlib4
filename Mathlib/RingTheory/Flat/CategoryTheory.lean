/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Monoidal.RightExact

/-!
# Tensoring with a flat module is an exact functor

In this file we prove that tensoring with a flat module is an exact functor.

## Main results

- `Module.Flat.iff_lTensor_preserves_shortComplex_exact`: an `R`-module `M` is flat if and only if
  for every exact sequence `A ⟶ B ⟶ C`, `M ⊗ A ⟶ M ⊗ B ⟶ M ⊗ C` is also exact.

- `Module.Flat.iff_rTensor_preserves_shortComplex_exact`: an `R`-module `M` is flat if and only if
  for every short exact sequence `A ⟶ B ⟶ C`, `A ⊗ M ⟶ B ⊗ M ⟶ C ⊗ M` is also exact.

- `Module.Flat.iff_lTensor_preservesFiniteLimits`: an `R`-module `M` is flat if and only if
  tensoring with `M` on the left preserves finite limits.

- `Module.Flat.iff_rTensor_preservesFiniteLimits`: an `R`-module `M` is flat if and only if
  tensoring with `M` on the right preserves finite limits.

## TODO

- Prove that tensoring with a flat module is an exact functor in the sense that it preserves both
  finite limits and colimits.
- Relate flatness with `Tor`

-/

universe u

open CategoryTheory MonoidalCategory ShortComplex.ShortExact

namespace Module.Flat

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R)

lemma lTensor_shortComplex_exact [Flat R M] (C : ShortComplex $ ModuleCat R) (hC : C.Exact) :
    C.map (tensorLeft M) |>.Exact := by
  rw [moduleCat_exact_iff_function_exact] at hC ⊢
  exact lTensor_exact M hC

lemma rTensor_shortComplex_exact [Flat R M] (C : ShortComplex $ ModuleCat R) (hC : C.Exact) :
    C.map (tensorRight M) |>.Exact := by
  rw [moduleCat_exact_iff_function_exact] at hC ⊢
  exact rTensor_exact M hC

lemma iff_lTensor_preserves_shortComplex_exact :
    Flat R M ↔
    ∀ (C : ShortComplex $ ModuleCat R) (_ : C.Exact), (C.map (tensorLeft M) |>.Exact) :=
  ⟨fun _ _ ↦ lTensor_shortComplex_exact _ _, fun H ↦ iff_lTensor_exact.2 $
    fun _ _ _ _ _ _ _ _ _ f g h ↦
      moduleCat_exact_iff_function_exact _ |>.1 $
      H (.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
        (DFunLike.ext _ _ h.apply_apply_eq_zero))
          (moduleCat_exact_iff_function_exact _ |>.2 h)⟩

lemma iff_rTensor_preserves_shortComplex_exact :
    Flat R M ↔
    ∀ (C : ShortComplex $ ModuleCat R) (_ : C.Exact), (C.map (tensorRight M) |>.Exact) :=
  ⟨fun _ _ ↦ rTensor_shortComplex_exact _ _, fun H ↦ iff_rTensor_exact.2 $
    fun _ _ _ _ _ _ _ _ _ f g h ↦
      moduleCat_exact_iff_function_exact _ |>.1 $
      H (.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
        (DFunLike.ext _ _ h.apply_apply_eq_zero))
          (moduleCat_exact_iff_function_exact _ |>.2 h)⟩

lemma iff_lTensor_preservesFiniteLimits :
    Flat R M ↔
    Nonempty (Limits.PreservesFiniteLimits (tensorLeft M)) := by
  have : Nonempty (Limits.PreservesFiniteColimits (tensorLeft M)) := ⟨inferInstance⟩
  have := Functor.exact_tfae (tensorLeft M) |>.out 1 3
  rw [iff_lTensor_preserves_shortComplex_exact, this]
  aesop

lemma iff_rTensor_preservesFiniteLimits :
    Flat R M ↔
    Nonempty (Limits.PreservesFiniteLimits (tensorRight M)) := by
  have : Nonempty (Limits.PreservesFiniteColimits (tensorRight M)) := ⟨inferInstance⟩
  have := Functor.exact_tfae (tensorRight M) |>.out 1 3
  rw [iff_rTensor_preserves_shortComplex_exact, this]
  aesop

end Module.Flat
