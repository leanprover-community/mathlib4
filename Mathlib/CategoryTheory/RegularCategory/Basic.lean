/-
Copyright (c) 2025 Fernando Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Chu
-/
import Mathlib.CategoryTheory.EffectiveEpi.Basic
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair

/-!
# Regular categories

A regular category is category with finite limits such that each kernel pair has a coequalizer
and such that regular epimorphisms are stable under pullback.

These categories provide a good ground to develop the calculus of relations, as well as being the
semantics for regular logic.

## Main results

* We show that every regular category has strong-epi-mono factorisations, following Theorem 1.11
  in [Gran2021].

## Future work
* Show Frobenius reciprocity
* Show that every topos is regular
* Define the regular topology on regular categories
* Show that regular logic has an interpretation in regular categories

## References
* [Marino Gran, An Introduction to Regular Categories][Gran2021]
* <https://ncatlab.org/nlab/show/regular+category>
-/

open CategoryTheory Limits

universe u v

namespace CategoryTheory

section

variable (C : Type u) [Category.{v} C]

class Regular extends HasFiniteLimits C where
  hasCoequalizer_of_isKernelPair {a b c : C} {f : a ⟶ b} {g1 g2 : c ⟶ a} :
    IsKernelPair f g1 g2 → HasCoequalizer g1 g2
  regularEpiIsStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange (.regularEpi C)

end

variable {C : Type u} [Category.{v} C] [Regular C]
variable {X Y : C} (f : X ⟶ Y)

noncomputable section
namespace Regular.Limits

local instance : HasCoequalizer (pullback.fst f f) (pullback.snd f f) :=
  Regular.hasCoequalizer_of_isKernelPair <| IsKernelPair.of_hasPullback f

def I : C :=
  coequalizer (pullback.fst f f) (pullback.snd f f)

def e : X ⟶ (I f) :=
  coequalizer.π (pullback.fst f f) (pullback.snd f f)

instance e_isRegularEpi : IsRegularEpi (e f) := by
  dsimp [e]; infer_instance

def m : (I f) ⟶ Y :=
  coequalizer.desc f (IsKernelPair.of_hasPullback f).w

@[reassoc (attr := simp)]
lemma fac : (e f) ≫ (m f) = f :=
  coequalizer.π_desc f _

instance m_mono : Mono (m f) := by
  apply (IsKernelPair.of_hasPullback (m f)).mono_of_eq_fst_snd
  set k₁ := pullback.fst (m f) (m f)
  set k₂ := pullback.snd (m f) (m f)
  set d : _ ⟶ (pullback (m f) (m f)) :=
    pullback.lift (pullback.fst f f ≫ e f) (pullback.snd f f ≫ e f)
      (by simp; rw [pullback.condition])
  set g₁ : _ ⟶ (pullback (e f) k₁) := pullback.lift (pullback.fst f f) d (by simp [d, k₁])
  set g₂ : _ ⟶ (pullback k₂ (e f)) := pullback.lift d (pullback.snd f f) (by simp [d, k₂])
  set sq₁ := IsPullback.of_hasPullback (e f) k₁
  let sq₂ := IsPullback.of_hasPullback k₂ (e f)
  have ispbsq : IsPullback (g₁ ≫ pullback.fst (e f) k₁) (g₂ ≫ pullback.snd k₂ (e f))
      (e f ≫ m f) (e f ≫ m f) := by
    rw [fac, pullback.lift_fst, pullback.lift_snd]
    simpa [g₁, g₂] using IsPullback.of_hasPullback f f
  have sq1 : IsPullback g₁ g₂ (pullback.snd (e f) k₁) (pullback.fst k₂ (e f)) := by
    apply IsPullback.of_right ?_ (by simp [g₂, g₁]) sq₁
    apply IsPullback.of_bot ispbsq (by simp [g₂, g₁, k₁, d])
    exact IsPullback.paste_horiz sq₂ (IsPullback.of_hasPullback (m f) (m f))
  have reβ1 : IsRegularEpi (pullback.snd (e f) k₁) := by
    apply Regular.regularEpiIsStableUnderBaseChange.of_isPullback sq₁ (e_isRegularEpi f)
  have reα2 : IsRegularEpi (pullback.fst k₂ (e f)) := by
    apply Regular.regularEpiIsStableUnderBaseChange.of_isPullback sq₂.flip (e_isRegularEpi f)
  have reb : IsRegularEpi g₁ := by
    apply Regular.regularEpiIsStableUnderBaseChange.of_isPullback sq1.flip reα2
  rw [← cancel_epi (g₁ ≫ pullback.snd (e f) k₁)]
  convert coequalizer.condition (pullback.fst f f) (pullback.snd f f) using 1
  · rw [Category.assoc, sq₁.w.symm, pullback.lift_fst_assoc, e]
  · rw [sq1.w, Category.assoc, sq₂.w, pullback.lift_snd_assoc, e]

def monoFactorisation : MonoFactorisation f where
  I := I f
  m := m f
  e := e f
  fac := fac f

def strongEpiMonoFactorisation : StrongEpiMonoFactorisation f where
  __ := monoFactorisation f
  e_strong_epi := by
    dsimp [monoFactorisation]
    apply strongEpi_of_regularEpi

instance hasStrongEpiMonoFactorisations : HasStrongEpiMonoFactorisations C where
  has_fac f := ⟨strongEpiMonoFactorisation f⟩

variable {f} in
instance regularEpiOfExtremalEpi (s : ExtremalEpi f) : RegularEpi f :=
  have := s.isIso (e f) (m f) (by simp)
  RegularEpi.ofArrowIso <| Arrow.isoMk (f := .mk (e f)) (Iso.refl _) (asIso (m f))

end Regular.Limits
end

end CategoryTheory
