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

variable {C : Type u} [Category.{v} C]
variable [Regular C]

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

/--
The following lemma states that if whole square is a pullback and squares 2, 3 and 4 are pullbacks,
then square 1 is a pullback too.
```
X₁₁ - h₁₁ -> X₁₂ - h₁₂ -> X₁₃
|            |            |
v₁₁    1     v₁₂    2     v₁₃
↓            ↓            ↓
X₂₁ - h₂₁ -> X₂₂ - h₂₂ -> X₂₃
|            |            |
v₂₁    3     v₂₂    4     v₂₃
↓            ↓            ↓
X₃₁ - h₃₁ -> X₃₂ - h₃₂ -> X₃₃
```
-/
lemma pb {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ X₃₁ X₃₂ X₃₃ : C}
    {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂} {v₂₃ : X₂₃ ⟶ X₃₃}
    {h₃₁ : X₃₁ ⟶ X₃₂} {h₃₂ : X₃₂ ⟶ X₃₃} (w : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁)
    (h : IsPullback (h₁₁ ≫ h₁₂) (v₁₁ ≫ v₂₁) (v₁₃ ≫ v₂₃) (h₃₁ ≫ h₃₂))
    (h2 : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) (h3 : IsPullback h₂₁ v₂₁ v₂₂ h₃₁)
    (h4 : IsPullback h₂₂ v₂₂ v₂₃ h₃₂) :
    IsPullback h₁₁ v₁₁ v₁₂ h₂₁ := by
  apply IsPullback.of_right ?_ w h2
  apply IsPullback.of_bot h (by rw [← reassoc_of% w, ← h2.w, Category.assoc])
  exact IsPullback.paste_horiz h3 h4

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
  have sq1 := pb (by simp [g₂, g₁]) ispbsq sq₁ sq₂ <|
    IsPullback.of_hasPullback (m f) (m f)
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

instance m_mono' : Mono (m f) := by
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
  have sq1 := pb (by simp [g₂, g₁]) ispbsq sq₁ sq₂ <|
    IsPullback.of_hasPullback (m f) (m f)
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

def strongEpi : StrongEpiMonoFactorisation f where
  __ := monoFactorisation f
  e_strong_epi := by
    dsimp [monoFactorisation]
    apply strongEpi_of_regularEpi

instance hasStrongEpiMonoFactorisations : HasStrongEpiMonoFactorisations C where
  has_fac f := ⟨strongEpi f⟩

instance regularEpiOfExtremalEpi (s : ExtremalEpi f) : RegularEpi f :=
  have := s.isIso (e f) (m f) (by simp)
  fac f ▸ RegularEpi.ofRegularEpiCompIso (e f) (m f)

end Regular.Limits
end

end CategoryTheory
