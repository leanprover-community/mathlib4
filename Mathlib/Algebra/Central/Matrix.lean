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
    refine (isEmpty_or_nonempty ι).elim (fun _ => ⟨0, by simp [nontriviality]⟩) fun ⟨i⟩ => ?_
    obtain ⟨d, hd, rfl⟩ : m ∈ _ '' _ := by rw [← center_eq_scalar_image]; exact_mod_cast h
    obtain ⟨r, rfl⟩ : d ∈ (⊥ : Subalgebra K D) := by
      rw [← center_eq_bot K D, Subalgebra.mem_center_iff]
      intro d'
      simpa using ext_iff.2 (Subalgebra.mem_center_iff.mp h (scalar ι d')) i i
    exact ⟨r, rfl⟩

end Algebra.IsCentral
