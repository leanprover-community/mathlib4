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

open Polynomial Bornology

open scoped Polynomial

namespace Complex

/-- **Fundamental theorem of algebra**: every non constant complex polynomial
  has a root -/
theorem exists_root {f : ℂ[X]} (hf : 0 < degree f) : ∃ z : ℂ, IsRoot f z := by
  by_contra! hf'
  /- Since `f` has no roots, `f⁻¹` is differentiable. And since `f` is a polynomial, it tends to
  infinity at infinity, thus `f⁻¹` tends to zero at infinity. By Liouville's theorem, `f⁻¹ = 0`. -/
  have (z : ℂ) : (f.eval z)⁻¹ = 0 :=
    (f.differentiable.inv hf').apply_eq_of_tendsto_cocompact z <|
      Metric.cobounded_eq_cocompact (α := ℂ) ▸ (Filter.tendsto_inv₀_cobounded.comp <| by
        simpa only [tendsto_norm_atTop_iff_cobounded]
          using f.tendsto_norm_atTop hf tendsto_norm_cobounded_atTop)
  -- Thus `f = 0`, contradicting the fact that `0 < degree f`.
  obtain rfl : f = C 0 := Polynomial.funext fun z ↦ inv_injective <| by simp [this]
  simp at hf
#align complex.exists_root Complex.exists_root

instance isAlgClosed : IsAlgClosed ℂ :=
  IsAlgClosed.of_exists_root _ fun _p _ hp => Complex.exists_root <| degree_pos_of_irreducible hp
#align complex.is_alg_closed Complex.isAlgClosed

end Complex
