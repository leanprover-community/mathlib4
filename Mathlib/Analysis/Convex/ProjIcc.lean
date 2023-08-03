/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Set.Intervals.ProjIcc

#align_import analysis.convex.proj_Icc from "leanprover-community/mathlib"@"3ba15165bd6927679be7c22d6091a87337e3cd0c"

/-!
# Convexity of extension from intervals

This file proves that constantly extending monotone/antitone functions preserves their convexity.

## TODO

We could deduplicate the proofs if we had a typeclass stating that `segment 𝕜 x y = [x -[𝕜] y]` as
`𝕜ᵒᵈ` respects it if `𝕜` does, while `𝕜ᵒᵈ` isn't a `LinearOrderedField` if `𝕜` is.
-/

open Set

variable {𝕜 β : Type _} [LinearOrderedField 𝕜] [LinearOrderedAddCommMonoid β] [SMul 𝕜 β] {s : Set 𝕜}
  {f : 𝕜 → β} {z : 𝕜}

/-- A convex set extended towards minus infinity is convex. -/
protected theorem Convex.IciExtend (hf : Convex 𝕜 s) :
    Convex 𝕜 {x | IciExtend (restrict (Ici z) (· ∈ s)) x} := by
  rw [convex_iff_ordConnected] at hf ⊢; exact hf.restrict.Ici_extend
#align convex.Ici_extend Convex.IciExtend

/-- A convex set extended towards infinity is convex. -/
protected theorem Convex.IicExtend (hf : Convex 𝕜 s) :
    Convex 𝕜 {x | IicExtend (restrict (Iic z) (· ∈ s)) x} := by
  rw [convex_iff_ordConnected] at hf ⊢; exact hf.restrict.Iic_extend
#align convex.Iic_extend Convex.IicExtend

/-- A convex monotone function extended constantly towards minus infinity is convex. -/
protected theorem ConvexOn.IciExtend (hf : ConvexOn 𝕜 s f) (hf' : MonotoneOn f s) :
    ConvexOn 𝕜 {x | IciExtend (restrict (Ici z) (· ∈ s)) x} (IciExtend $ restrict (Ici z) f) := by
  refine' ⟨hf.1.IciExtend, λ x hx y hy a b ha hb hab ↦ _⟩
  dsimp [Ici_extend_apply] at hx hy ⊢
  refine' (hf' (hf.1.OrdConnected.uIcc_subset hx hy $ (Monotone.image_uIcc_subset λ _ _ ↦
    max_le_max le_rfl) $ mem_image_of_mem _ $ convex_uIcc _ _
    left_mem_uIcc right_mem_uIcc ha hb hab) (hf.1 hx hy ha hb hab) _).trans (hf.2 hx hy ha hb hab)
  rw [smul_max ha z, smul_max hb z]
  refine' le_trans _ max_add_add_le_max_add_max
  rw [Convex.combo_self hab, smul_eq_mul, smul_eq_mul]
#align convex_on.Ici_extend ConvexOn.IciExtend

/-- A convex antitone function extended constantly towards infinity is convex. -/
protected theorem ConvexOn.IicExtend (hf : ConvexOn 𝕜 s f) (hf' : AntitoneOn f s) :
    ConvexOn 𝕜 {x | IicExtend (restrict (Iic z) (· ∈ s)) x} (IicExtend $ restrict (Iic z) f) := by
  refine' ⟨hf.1.IicExtend, λ x hx y hy a b ha hb hab ↦ _⟩
  dsimp [Iic_extend_apply] at hx hy ⊢
  refine' (hf' (hf.1 hx hy ha hb hab) (hf.1.OrdConnected.uIcc_subset hx hy $
    (Monotone.image_uIcc_subset λ _ _ ↦ min_le_min le_rfl) $ mem_image_of_mem _ $ convex_uIcc _ _
    left_mem_uIcc right_mem_uIcc ha hb hab) _).trans (hf.2 hx hy ha hb hab)
  rw [smul_min ha z, smul_min hb z]
  refine' min_add_min_le_min_add_add.trans _
  rw [Convex.combo_self hab, smul_eq_mul, smul_eq_mul]
#align convex_on.Iic_extend ConvexOn.IicExtend

/-- A concave antitone function extended constantly minus towards infinity is concave. -/
protected theorem ConcaveOn.IciExtend (hf : ConcaveOn 𝕜 s f) (hf' : AntitoneOn f s) :
    ConcaveOn 𝕜 {x | IciExtend (restrict (Ici z) (· ∈ s)) x} (IciExtend $ restrict (Ici z) f) :=
  hf.dual.IciExtend hf'.dual_right
#align concave_on.Ici_extend ConcaveOn.IciExtend

/-- A concave monotone function extended constantly towards infinity is concave. -/
protected theorem ConcaveOn.IicExtend (hf : ConcaveOn 𝕜 s f) (hf' : MonotoneOn f s) :
    ConcaveOn 𝕜 {x | IicExtend (restrict (Iic z) (· ∈ s)) x} (IicExtend $ restrict (Iic z) f) :=
  hf.dual.IicExtend hf'.dual_right
#align concave_on.Iic_extend ConcaveOn.IicExtend

/-- A convex monotone function extended constantly towards minus infinity is convex. -/
protected theorem ConvexOn.IciExtend_of_monotone (hf : ConvexOn 𝕜 univ f) (hf' : Monotone f) :
    ConvexOn 𝕜 univ (IciExtend $ restrict (Ici z) f) :=
  hf.IciExtend $ hf'.MonotoneOn _
#align convex_on.Ici_extend_of_monotone ConvexOn.IciExtend_of_monotone

/-- A convex antitone function extended constantly towards infinity is convex. -/
protected theorem ConvexOn.IicExtend_of_antitone (hf : ConvexOn 𝕜 univ f) (hf' : Antitone f) :
    ConvexOn 𝕜 univ (IicExtend $ restrict (Iic z) f) :=
  hf.IicExtend $ hf'.AntitoneOn _
#align convex_on.Iic_extend_of_antitone ConvexOn.IicExtend_of_antitone

/-- A concave antitone function extended constantly minus towards infinity is concave. -/
protected theorem ConcaveOn.IciExtend_of_antitone (hf : ConcaveOn 𝕜 univ f) (hf' : Antitone f) :
    ConcaveOn 𝕜 univ (IciExtend $ restrict (Ici z) f) :=
  hf.IciExtend $ hf'.AntitoneOn _
#align concave_on.Ici_extend_of_antitone ConcaveOn.IciExtend_of_antitone

/-- A concave monotone function extended constantly towards infinity is concave. -/
protected theorem ConcaveOn.IicExtend_of_monotone (hf : ConcaveOn 𝕜 univ f) (hf' : Monotone f) :
    ConcaveOn 𝕜 univ (IicExtend $ restrict (Iic z) f) :=
  hf.IicExtend $ hf'.MonotoneOn _
#align concave_on.Iic_extend_of_monotone ConcaveOn.IicExtend_of_monotone
