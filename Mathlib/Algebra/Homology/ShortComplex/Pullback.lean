/-
Copyright (c) 2026 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Blake Farman
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Pulling back a short complex

Given a short complex `S` and a morphism `f : Y ⟶ S.X₃`, we construct the short complex
`S.pull f`, which is `S.X₁ ⟶ pullback f S.g ⟶ Y`, and show that it is short exact when `S` is,
if the ambient category is abelian.

This is dual to `ShortComplex.push`, see `Mathlib/Algebra/Homology/ShortComplex/Pushout.lean`.

-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]

/-- The pullback of a short complex `S` along a morphism `f : Y ⟶ S.X₃`: the short complex
`S.X₁ ⟶ pullback f S.g ⟶ Y`, whose first map is induced by `0` and `S.f` and whose second map
is `pullback.fst`. -/
@[simps, implicit_reducible]
noncomputable def ShortComplex.pull
    [HasZeroMorphisms C] (S : ShortComplex C) {Y : C} (f : Y ⟶ S.X₃) [HasPullback f S.g] :
    ShortComplex C where
  X₁ := S.X₁
  X₂ := pullback f S.g
  X₃ := Y
  f := pullback.lift 0 S.f
  g := pullback.fst _ _

instance [Abelian C] (S : ShortComplex C) {Y : C} (f : Y ⟶ S.X₃) [Epi S.g] :
    Epi (S.pull f).g := by
  dsimp
  infer_instance

instance [HasZeroMorphisms C] (S : ShortComplex C) {Y : C} (f : Y ⟶ S.X₃)
    [HasPullback f S.g] [Mono S.f] :
    Mono (S.pull f).f := by
  have : (S.pull f).f ≫ pullback.snd _ _ = S.f := by simp
  exact mono_of_mono_fac this

/-- The pullback of a short exact short complex along any morphism `f : Y ⟶ S.X₃` is
short exact. -/
lemma ShortComplex.ShortExact.pull
    [Abelian C] {S : ShortComplex C} (hS : S.ShortExact) {Y : C} (f : Y ⟶ S.X₃) :
    (S.pull f).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  obtain ⟨h, _⟩ := (S.pull f).exact_and_mono_f_iff_f_is_kernel.2 ⟨by
    refine Fork.IsLimit.mk' _ (fun s ↦ ?_)
    obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hS.fIsKernel (s.ι ≫ pullback.snd _ _)
      (by simp [← pullback.condition])
    refine ⟨l, by cat_disch, fun {m} hm ↦ ?_⟩
    dsimp at m hm hl
    simp [← cancel_mono S.f, hl, ← hm]⟩
  exact { exact := h }

end CategoryTheory
