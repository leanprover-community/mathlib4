/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import Lean

/-!
# Declare `integral_simps` simp attribute.

Has to be in a separate file from `MeasureTheory.Integral.Bochner`, since simp attributes cannot be
used directly in the file that declares them.
-/

/-- Simp set for integral rules. -/
register_simp_attr integral_simps
