/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir
-/
import Mathlib.Algebra.Order.CauSeq.BigOperators
import Mathlib.Data.Complex.Abs

/-!
# Exponential, trigonometric and hyperbolic trigonometric functions

This file contains the definitions of the real and complex exponential, sine, cosine, tangent,
hyperbolic sine, hyperbolic cosine, and hyperbolic tangent functions.

-/

open CauSeq Finset IsAbsoluteValue
open scoped ComplexConjugate

namespace Complex

theorem isCauSeq_abs_exp (z : ℂ) :
    IsCauSeq _root_.abs fun n => ∑ m ∈ range n, abs (z ^ m / m.factorial) :=
  let ⟨n, hn⟩ := exists_nat_gt (abs z)
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (abs.nonneg _) hn
  IsCauSeq.series_ratio_test n (abs z / n) (div_nonneg (abs.nonneg _) (le_of_lt hn0))
    (by rwa [div_lt_iff₀ hn0, one_mul]) fun m hm => by
      rw [abs_abs, abs_abs, Nat.factorial_succ, pow_succ', mul_comm m.succ, Nat.cast_mul, ← div_div,
        mul_div_assoc, mul_div_right_comm, map_mul, map_div₀, abs_natCast]
      gcongr
      exact le_trans hm (Nat.le_succ _)

noncomputable section

theorem isCauSeq_exp (z : ℂ) : IsCauSeq abs fun n => ∑ m ∈ range n, z ^ m / m.factorial :=
  (isCauSeq_abs_exp z).of_abv

/-- The Cauchy sequence consisting of partial sums of the Taylor series of
the complex exponential function -/
@[pp_nodot]
def exp' (z : ℂ) : CauSeq ℂ Complex.abs :=
  ⟨fun n => ∑ m ∈ range n, z ^ m / m.factorial, isCauSeq_exp z⟩

/-- The complex exponential function, defined via its Taylor series -/
-- Porting note: removed `irreducible` attribute, so I can prove things
@[pp_nodot]
def exp (z : ℂ) : ℂ :=
  CauSeq.lim (exp' z)

/-- The complex sine function, defined via `exp` -/
@[pp_nodot]
def sin (z : ℂ) : ℂ :=
  (exp (-z * I) - exp (z * I)) * I / 2

/-- The complex cosine function, defined via `exp` -/
@[pp_nodot]
def cos (z : ℂ) : ℂ :=
  (exp (z * I) + exp (-z * I)) / 2

/-- The complex tangent function, defined as `sin z / cos z` -/
@[pp_nodot]
def tan (z : ℂ) : ℂ :=
  sin z / cos z

/-- The complex cotangent function, defined as `cos z / sin z` -/
def cot (z : ℂ) : ℂ :=
  cos z / sin z

/-- The complex hyperbolic sine function, defined via `exp` -/
@[pp_nodot]
def sinh (z : ℂ) : ℂ :=
  (exp z - exp (-z)) / 2

/-- The complex hyperbolic cosine function, defined via `exp` -/
@[pp_nodot]
def cosh (z : ℂ) : ℂ :=
  (exp z + exp (-z)) / 2

/-- The complex hyperbolic tangent function, defined as `sinh z / cosh z` -/
@[pp_nodot]
def tanh (z : ℂ) : ℂ :=
  sinh z / cosh z

/-- scoped notation for the complex exponential function -/
scoped notation "cexp" => Complex.exp

end

end Complex

namespace Real

open Complex

noncomputable section

/-- The real exponential function, defined as the real part of the complex exponential -/
@[pp_nodot]
nonrec def exp (x : ℝ) : ℝ :=
  (exp x).re

/-- The real sine function, defined as the real part of the complex sine -/
@[pp_nodot]
nonrec def sin (x : ℝ) : ℝ :=
  (sin x).re

/-- The real cosine function, defined as the real part of the complex cosine -/
@[pp_nodot]
nonrec def cos (x : ℝ) : ℝ :=
  (cos x).re

/-- The real tangent function, defined as the real part of the complex tangent -/
@[pp_nodot]
nonrec def tan (x : ℝ) : ℝ :=
  (tan x).re

/-- The real cotangent function, defined as the real part of the complex cotangent -/
nonrec def cot (x : ℝ) : ℝ :=
  (cot x).re

/-- The real hypebolic sine function, defined as the real part of the complex hyperbolic sine -/
@[pp_nodot]
nonrec def sinh (x : ℝ) : ℝ :=
  (sinh x).re

/-- The real hypebolic cosine function, defined as the real part of the complex hyperbolic cosine -/
@[pp_nodot]
nonrec def cosh (x : ℝ) : ℝ :=
  (cosh x).re

/-- The real hypebolic tangent function, defined as the real part of
the complex hyperbolic tangent -/
@[pp_nodot]
nonrec def tanh (x : ℝ) : ℝ :=
  (tanh x).re

/-- scoped notation for the real exponential function -/
scoped notation "rexp" => Real.exp

end

end Real

#min_imports
