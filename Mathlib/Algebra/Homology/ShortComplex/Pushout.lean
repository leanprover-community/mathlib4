/-
Copyright (c) 2026 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Blake Farman
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Pushing out a short complex

Given a short complex `S` and a morphism `f : S.X₁ ⟶ Y`, we construct the short complex
`S.push f`, which is `Y ⟶ pushout S.f f ⟶ S.X₃`, and show that it is short exact when `S` is,
if the ambient category is abelian.

This is dual to `ShortComplex.pull`, see `Mathlib/Algebra/Homology/ShortComplex/Pullback.lean`.

-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]

/-- The pushout of a short complex `S` along a morphism `f : S.X₁ ⟶ Y`: the short complex
`Y ⟶ pushout S.f f ⟶ S.X₃`, whose first map is `pushout.inr` and whose second map is induced
by `S.g` and `0`. -/
@[simps, implicit_reducible]
noncomputable def ShortComplex.push
    [HasZeroMorphisms C] (S : ShortComplex C) {Y : C} (f : S.X₁ ⟶ Y) [HasPushout S.f f] :
    ShortComplex C where
  X₁ := Y
  X₂ := pushout S.f f
  X₃ := S.X₃
  f := pushout.inr _ _
  g := pushout.desc S.g 0 (by simp)

instance [Abelian C] (S : ShortComplex C) {Y : C} (f : S.X₁ ⟶ Y) [Mono S.f] :
    Mono (S.push f).f := by
  dsimp
  infer_instance

instance [HasZeroMorphisms C] (S : ShortComplex C) {Y : C} (f : S.X₁ ⟶ Y)
    [HasPushout S.f f] [Epi S.g] :
    Epi (S.push f).g := by
  have : pushout.inl _ _ ≫ (S.push f).g = S.g := by simp
  exact epi_of_epi_fac this

/-- The pushout of a short exact short complex along any morphism `f : S.X₁ ⟶ Y` is
short exact. -/
lemma ShortComplex.ShortExact.push
    [Abelian C] {S : ShortComplex C} (hS : S.ShortExact) {Y : C} (f : S.X₁ ⟶ Y) :
    (S.push f).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  obtain ⟨h, _⟩ := (S.push f).exact_and_epi_g_iff_g_is_cokernel.2 ⟨by
    refine Cofork.IsColimit.mk' _ (fun s ↦ ?_)
    obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc' hS.gIsCokernel (pushout.inl _ _ ≫ s.π)
      (by simp [pushout.condition_assoc])
    refine ⟨l, by cat_disch, fun {m} hm ↦ ?_⟩
    dsimp at m hm hl
    simp [← cancel_epi S.g, hl, ← hm]⟩
  exact { exact := h }

end CategoryTheory
