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
`S.push f`, which is `Y ⟶ pushout f S.f ⟶ S.X₃`, and show that it is short exact when `S` is,
if the ambient category is abelian.

This is dual to `ShortComplex.pull`, see `Mathlib/Algebra/Homology/ShortComplex/Pullback.lean`.

-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]

/-- The pushout of a short complex `S` along a morphism `f : S.X₁ ⟶ Y`: the short complex
`Y ⟶ pushout f S.f ⟶ S.X₃`, whose first map is `pushout.inl` and whose second map is induced
by `0` and `S.g`. -/
@[simps, implicit_reducible]
noncomputable def ShortComplex.push
    [HasZeroMorphisms C] (S : ShortComplex C) {Y : C} (f : S.X₁ ⟶ Y) [HasPushout f S.f] :
    ShortComplex C where
  X₁ := Y
  X₂ := pushout f S.f
  X₃ := S.X₃
  f := pushout.inl _ _
  g := pushout.desc 0 S.g (by simp)

instance [Abelian C] (S : ShortComplex C) {Y : C} (f : S.X₁ ⟶ Y) [Mono S.f] :
    Mono (S.push f).f := by
  dsimp
  infer_instance

instance [HasZeroMorphisms C] (S : ShortComplex C) {Y : C} (f : S.X₁ ⟶ Y)
    [HasPushout f S.f] [Epi S.g] :
    Epi (S.push f).g := by
  have : pushout.inr _ _ ≫ (S.push f).g = S.g := by simp
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
    obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc' hS.gIsCokernel (pushout.inr _ _ ≫ s.π)
      (by simp [← pushout.condition_assoc])
    refine ⟨l, by cat_disch, fun {m} hm ↦ ?_⟩
    rw [← cancel_epi S.g]
    dsimp at m hm hl
    simp [hl, ← hm]⟩
  exact { exact := h }

end CategoryTheory
