/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.CategoryTheory.ObjectProperty.HasFiniteResolution.Basic

/-!
# `X` has a projective resolution of length `n` if and only if `X` has projective dimension `≤ n`
-/

public section

universe v u

namespace CategoryTheory.ObjectProperty.HasFiniteResolutionOfLength

open Limits

variable {A : Type u} [Category.{v} A] [Abelian A] {X : A} {n : ℕ}

theorem hasProjectiveDimensionLE (hX : (isProjective A).HasFiniteResolutionOfLength X n) :
    HasProjectiveDimensionLE X n := by
  induction hX with
  | zero X hX => infer_instance
  | succ S n hS h₂ _ ih => exact (hS.hasProjectiveDimensionLT_X₃_iff n h₂).2 ih

theorem iff_hasProjectiveDimensionLE_of_enoughProjectives [EnoughProjectives A] :
    (isProjective A).HasFiniteResolutionOfLength X n ↔ HasProjectiveDimensionLE X n := by
  refine ⟨fun hX ↦ hX.hasProjectiveDimensionLE, fun hX ↦ ?_⟩
  induction n generalizing X with
  | zero =>
      rw [← projective_iff_hasProjectiveDimensionLE_zero X] at hX
      exact HasFiniteResolutionOfLength.zero X hX
  | succ n ih =>
      let f : Projective.over X ⟶ X := Projective.π X
      let S : ShortComplex A := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
      have hS : S.ShortExact := ShortComplex.ShortExact.mk (ShortComplex.exact_kernel f)
      exact HasFiniteResolutionOfLength.succ S n hS inferInstance <| ih <|
        (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).1 hX

end CategoryTheory.ObjectProperty.HasFiniteResolutionOfLength
