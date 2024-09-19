/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang, Kevin Buzzard
-/

import Mathlib.Algebra.CentralSimple.Defs
import Mathlib.RingTheory.SimpleRing.Basic

universe u v

namespace Algebra.IsCentralSimple

variable (K : Type u) [Field K] (D : Type v) [Ring D] [Algebra K D] [IsCentralSimple K D]

@[simp]
lemma center_eq_bot : Subalgebra.center K D = ⊥ := eq_bot_iff.2 IsCentralSimple.is_central

variable {D} in
lemma mem_center_iff {x : D} : x ∈ Subalgebra.center K D ↔ ∃ (a : K), x = algebraMap K D a := by
  rw [center_eq_bot, Algebra.mem_bot]
  simp [eq_comm]

instance self : IsCentralSimple K K where
  is_central x := by simp [Algebra.mem_bot]

end Algebra.IsCentralSimple
