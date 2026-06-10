/-
Copyright (c) 2026 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/

import Mathlib

/-!
# Manifold derivatives of multiplication on the units of a normed algebra

The group of units `Fˣ` of a complete normed `ℝ`-algebra `F` is a Lie group modelled on `F`
(via the open embedding `Units.val`).  This file computes the manifold derivatives of left
multiplication and of two-sided multiplication (conjugation) on `Fˣ`, which specialise to the
Maurer–Cartan form and the adjoint representation for the frame bundle.
-/

open scoped Manifold ContDiff
open ContinuousLinearMap

section Units

variable {F : Type*} [NormedRing F] [CompleteSpace F] [NormedAlgebra ℝ F]

/-- The manifold derivative of left multiplication `h ↦ a * h` on `Fˣ`, computed at any point
`g`, is left multiplication by `a.val` on the model space `F`. -/
lemma mfderiv_units_mulLeft (a g : Fˣ) (v : F) :
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun h : Fˣ => a * h) g v = (a : F) * v := by
  have h_eq : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun h : Fˣ => a * h) g = ContinuousLinearMap.mul ℝ F a := by
    apply HasMFDerivAt.mfderiv _;
    constructor;
    · fun_prop;
    · simp +decide only [ hasFDerivWithinAt_iff_tendsto, writtenInExtChartAt ];
      simp?
      apply tendsto_const_nhds.congr' _;
      filter_upwards [ IsOpen.mem_nhds ( show IsOpen ( Set.range ( Units.val : Fˣ → F ) ) from by
        exact Units.isOpenEmbedding_val.isOpen_range ) ( Set.mem_range_self g ) ] with x hx;
      obtain ⟨ y, rfl ⟩ := hx; simp +decide [ ← mul_sub ] ;
      simp +decide [ Topology.IsOpenEmbedding.toOpenPartialHomeomorph ];
      simp +decide [ Function.invFunOn ];
      grind;
  exact h_eq.symm ▸ rfl

/-- The manifold derivative of the two-sided multiplication `h ↦ a * h * b` on `Fˣ`, computed at
the identity, is `v ↦ a.val * v * b.val` on the model space `F`. -/
lemma mfderiv_units_mul_mul (a b : Fˣ) (A : F) :
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun h : Fˣ => a * h * b) 1 A = (a : F) * A * (b : F) := by
  rw [ mfderiv ];
  simp +decide only [ writtenInExtChartAt ];
  simp?
  split_ifs with h;
  · have h_deriv : HasFDerivAt (fun h : F => (a : F) * h * (b : F))
      (ContinuousLinearMap.mul ℝ F (a : F) ∘L (ContinuousLinearMap.mul ℝ F).flip (b : F)) 1 := by
      simp +decide [ hasFDerivAt_iff_isLittleO_nhds_zero ];
      simp +decide [ mul_add, add_mul, mul_assoc ];
    convert HasFDerivAt.fderiv ( h_deriv.congr_of_eventuallyEq _ ) |> congr_arg ( fun f => f A )
      using 1;
    · simp +decide [ mul_assoc ];
    · filter_upwards
        [ ( Units.isOpenEmbedding_val.isOpen_range.mem_nhds <| Set.mem_range_self 1 ) ] with x hx;
      obtain ⟨ y, rfl ⟩ := hx; simp +decide only [ mul_assoc ] ;
      simp [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv (Units.val : Fˣ → F)
        Units.instChartedSpace._proof_2]
  · contrapose! h;
    apply_rules [ ContMDiffAt.mdifferentiableAt ];
    any_goals exact ⊤;
    · apply_rules [ ContMDiffAt.mul, contMDiffAt_const ];
      exact contMDiffAt_id;
    · exact WithTop.top_ne_zero

end Units
