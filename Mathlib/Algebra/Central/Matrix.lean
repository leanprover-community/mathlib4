/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Yunzhou Xie
-/
import Mathlib.Algebra.Central.Basic
import Mathlib.Data.Matrix.Basis

/-!
# The matrix algebra is a central algebra
-/

namespace Algebra.IsCentral

variable (K D : Type*) [CommSemiring K] [Semiring D] [Algebra K D] [IsCentral K D]

open Matrix in
instance matrix (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Algebra.IsCentral K (Matrix ι ι D) where
  out m h := by
    refine isEmpty_or_nonempty ι |>.recOn
      (fun h => Algebra.mem_bot.2 ⟨0, Matrix.ext fun i _ => h.elim i⟩) fun ⟨i⟩ => ?_
    obtain ⟨d, rfl⟩ := mem_range_scalar_of_commute_single (M := m) (fun _ _ _ =>
      Subalgebra.mem_center_iff.mp h _)
    have mem : d ∈ Subalgebra.center K D := by
      rw [Subalgebra.mem_center_iff] at h ⊢
      intro d'
      simpa using Matrix.ext_iff.2 (h (scalar ι d')) i i
    rw [center_eq_bot, Algebra.mem_bot] at mem
    obtain ⟨r, rfl⟩ := mem
    rw [Algebra.mem_bot]
    exact ⟨r, rfl⟩

end Algebra.IsCentral
