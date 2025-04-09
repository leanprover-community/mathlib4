/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Constructor for abelian categories

-/

namespace CategoryTheory

open Category Limits

namespace Abelian

variable (C : Type*) [Category C] [Preadditive C] [HasFiniteProducts C]
  (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), ∃ (K : C) (i : K ⟶ X) (wi : i ≫ f = 0)
    (_hi : IsLimit (KernelFork.ofι _ wi))
    (Q : C) (p : Y ⟶ Q) (wp : f ≫ p = 0) (_hp : IsColimit (CokernelCofork.ofπ _ wp))
    (I : C) (π : X ⟶ I) (wπ : i ≫ π = 0) (_hπ : IsColimit (CokernelCofork.ofπ _ wπ))
    (ι : I ⟶ Y) (wι : ι ≫ p = 0) (_hι : IsLimit (KernelFork.ofι _ wι)), f = π ≫ ι)

/-- Constructor for abelian categories. -/
noncomputable def mk' : Abelian C where
  toPreadditive := inferInstance
  has_kernels := ⟨fun {X Y} f => by
    obtain ⟨K, i, wi, hi, _⟩ := h f
    exact ⟨_, hi⟩⟩
  has_cokernels := ⟨fun {X Y} f => by
    obtain ⟨_, _, _, _, Q, p, wp, hp, _⟩ := h f
    exact ⟨_, hp⟩⟩
  normalMonoOfMono {X Y} f _ := by
    apply Nonempty.some
    obtain ⟨K, i, wi, _, Q, p, wp, _, I, π, wπ, hπ, ι, wι, hι, fac⟩ := h f
    refine Nonempty.intro (Nonempty.intro ?_)
    refine
      { Z := Q
        g := p
        w := by rw [fac, assoc, wι, comp_zero]
        isLimit := by
          have : IsIso π := CokernelCofork.IsColimit.isIso_π _ hπ (by
            rw [← cancel_mono f, zero_comp, wi])
          exact IsLimit.ofIsoLimit hι (Fork.ext (by exact asIso π)
            (by exact fac.symm)).symm }
  normalEpiOfEpi {X Y} f _ := by
    apply Nonempty.some
    obtain ⟨K, i, wi, _, Q, p, wp, _, I, π, wπ, hπ, ι, wι, hι, fac⟩ := h f
    apply Nonempty.intro
    refine
     ⟨{ W := K
        g := i
        w := by rw [fac, reassoc_of% wπ, zero_comp]
        isColimit := by
          have : IsIso ι := KernelFork.IsLimit.isIso_ι _ hι (by
            rw [← cancel_epi f, comp_zero, wp])
          exact IsColimit.ofIsoColimit hπ (Cofork.ext (asIso ι) fac.symm) }⟩

end Abelian

end CategoryTheory
