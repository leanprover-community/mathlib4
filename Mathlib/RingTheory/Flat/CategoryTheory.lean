/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Tensoring with a flat module is an exact functor

In this file we prove that tensoring with a flat module is an exact functor.

## Main results

- `Module.Flat.iff_lTensor_preserves_shortComplex_exact`: an `R`-module `M` is flat if and only if
  for every exact sequence `A ⟶ B ⟶ C`, `M ⊗ A ⟶ M ⊗ B ⟶ M ⊗ C` is also exact.

- `Module.Flat.iff_rTensor_preserves_shortComplex_exact`: an `R`-module `M` is flat if and only if
  for every short exact sequence `A ⟶ B ⟶ C`, `A ⊗ M ⟶ B ⊗ M ⟶ C ⊗ M` is also exact.

- `Module.Flat.higherTorIsoZero`: if an `R`-module `M` is flat, then `Torⁿ(M, N) ≅ 0` for all `N`
  and all `n ≥ 1`.

- `Module.Flat.higherTor'IsoZero`: if an `R`-module `M` is flat, then `Torⁿ(N, M) ≅ 0` for all `N`
  and all `n ≥ 1`.


## TODO

- Prove that tensoring with a flat module is an exact functor in the sense that it preserves both
  finite limits and colimits.
- Prove that higher vanishing Tor group implies flatness

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

section Tor

open scoped ZeroObject

/-
For a flat module `M`, higher tor groups vanish.
-/
noncomputable def higherTorIsoZero [Flat R M] (n : ℕ) (N : ModuleCat.{u} R) :
    ((Tor _ (n + 1)).obj M).obj N ≅ 0 :=
  let pN := ProjectiveResolution.of N
  pN.isoLeftDerivedObj (tensorLeft M) (n + 1) ≪≫
    (Limits.IsZero.isoZero $ HomologicalComplex.exactAt_iff_isZero_homology _ _ |>.1 $
      lTensor_shortComplex_exact M (pN.complex.sc (n + 1)) (pN.complex_exactAt_succ n))


/--
For a flat module `M`, higher tor groups vanish.
-/
noncomputable def higherTor'IsoZero [Flat R M] (n : ℕ) (N : ModuleCat.{u} R) :
    ((Tor' _ (n + 1)).obj N).obj M ≅ 0 :=
  let pN := ProjectiveResolution.of N
  pN.isoLeftDerivedObj (tensorRight M) (n + 1) ≪≫
    (Limits.IsZero.isoZero $ HomologicalComplex.exactAt_iff_isZero_homology _ _ |>.1 $
      rTensor_shortComplex_exact M (pN.complex.sc (n + 1)) (pN.complex_exactAt_succ n))

end Tor

end Module.Flat
