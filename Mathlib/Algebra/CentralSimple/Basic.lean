/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang, Kevin Buzzard
-/

import Mathlib.Algebra.CentralSimple.Defs
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Central Simple Algebras

In this file, we prove some basic results about central simple algebras over a field.

## Main results

- `Algebra.IsCentralSimple.center_eq_bot`: the center of a central simple algebra over a field `K`
  is equal to `K`.
- `Algebra.IsCentralSimple.self`: a field is a central simple algebra over itself.
- `Algebra.IsCentralSimple.tower`: being central simple is stable under field extensions, i.e. if
  `K/k` is a field extension and `D` is a central simple algebra over `k`, then `D` is a central
  simple algebra over `K`.
-/

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

lemma tower {k K D : Type*} [Field k] [Field K] [Ring D]
    [Algebra k K] [Algebra K D] [Algebra k D] [IsScalarTower k K D] [IsCentralSimple k D] :
    IsCentralSimple K D where
  is_central x := by
    change x ∈ Subalgebra.center k D → _
    rw [center_eq_bot k D, Algebra.mem_bot, Algebra.mem_bot]
    simp only [Set.mem_range, forall_exists_index]
    rintro x rfl
    refine ⟨algebraMap k K x, by simp only [algebraMap_eq_smul_one, smul_assoc, one_smul]⟩
  is_simple := IsCentralSimple.is_simple k

end Algebra.IsCentralSimple
