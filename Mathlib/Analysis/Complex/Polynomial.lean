/-
Copyright (c) 2019 Chris Hughes All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu
-/
import Mathlib.Analysis.Complex.Liouville
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial

#align_import analysis.complex.polynomial from "leanprover-community/mathlib"@"17ef379e997badd73e5eabb4d38f11919ab3c4b3"

/-!
# The fundamental theorem of algebra

This file proves that every nonconstant complex polynomial has a root using Liouville's theorem.

As a consequence, the complex numbers are algebraically closed.
-/

open Polynomial

open scoped Polynomial

namespace Complex

/-- **Fundamental theorem of algebra**: every non constant complex polynomial
  has a root -/
theorem exists_root {f : ℂ[X]} (hf : 0 < degree f) : ∃ z : ℂ, IsRoot f z := by
  contrapose! hf
  -- ⊢ degree f ≤ 0
  have : Metric.Bounded (Set.range (eval · f)⁻¹)
  -- ⊢ Metric.Bounded (Set.range (fun x => eval x f)⁻¹)
  · obtain ⟨z₀, h₀⟩ := f.exists_forall_norm_le
    -- ⊢ Metric.Bounded (Set.range (fun x => eval x f)⁻¹)
    simp only [Pi.inv_apply, bounded_iff_forall_norm_le, Set.forall_range_iff, norm_inv]
    -- ⊢ ∃ C, ∀ (i : ℂ), ‖eval i f‖⁻¹ ≤ C
    exact ⟨‖eval z₀ f‖⁻¹, fun z => inv_le_inv_of_le (norm_pos_iff.2 <| hf z₀) (h₀ z)⟩
    -- 🎉 no goals
  obtain ⟨c, hc⟩ := (f.differentiable.inv hf).exists_const_forall_eq_of_bounded this
  -- ⊢ degree f ≤ 0
  · obtain rfl : f = C c⁻¹ := Polynomial.funext fun z => by rw [eval_C, ← hc z, inv_inv]
    -- ⊢ degree (↑C c⁻¹) ≤ 0
    exact degree_C_le
    -- 🎉 no goals
#align complex.exists_root Complex.exists_root

instance isAlgClosed : IsAlgClosed ℂ :=
  IsAlgClosed.of_exists_root _ fun _p _ hp => Complex.exists_root <| degree_pos_of_irreducible hp
#align complex.is_alg_closed Complex.isAlgClosed

end Complex
