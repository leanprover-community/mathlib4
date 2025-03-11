/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.MetricSpace.PiNat

/-!
# Normed spaces `Π (n : ℕ), E n`

When `E n` are topological spaces, the space `Π (n : ℕ), E n` is naturally a topological space
(with the product topology). When `E n` are uniform spaces, it also inherits a uniform structure.
However, it does not inherit a canonical metric space structure of the `E n`. Nevertheless, one
can put a noncanonical metric space structure (or rather, several of them).
This is handled in `Mathlib/Topology/MetricSpace/PiNat/Basic.lean`.
Here, we extend the result to the normed additive group structure.

## Main definitions and results

* `PiCountable.normedAddCommGroup`

-/

noncomputable section

namespace PiCountable

variable {ι : Type*} [Encodable ι] {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)]

attribute [local instance] PiCountable.metricSpace

/-- Given a countable family of normed additive groups, one may put a norm on their product
`Π i, E i`, defining the right topology and uniform structure and matching the metric space.
It is highly non-canonical, though, and therefore not registered as a global instance.
The distance we use here is `dist x y = ∑' n, min (1/2)^(encode i) (dist (x n) (y n))`. -/
protected def normedAddCommGroup : NormedAddCommGroup (Π i, F i) where
  __ := PiCountable.metricSpace
  norm x := dist x 0
  dist_eq x y := by
    have key : ∀ (x y c : Π i, F i), dist (x + c) (y + c) = dist x y := by
      simp [dist_eq_tsum]
    simpa [← sub_eq_add_neg] using (key x y (-y)).symm

attribute [local instance] PiCountable.normedAddCommGroup

open Encodable

lemma norm_def (f : Π i, F i) :
    ‖f‖ = ∑' i, min ((1 / 2) ^ encode i) ‖f i‖ := by
  rw [← sub_zero f, ← dist_eq_norm, dist_eq_tsum]
  simp

lemma norm_single [DecidableEq ι] (i : ι) (r : F i) :
    ‖(Pi.single i r : Π i, F i)‖ = (2 ^ encode i)⁻¹ ⊓ ‖r‖ := by
  rw [norm_def, tsum_eq_single i]
  · simp
  · simp +contextual [Pi.single_apply]

end PiCountable

namespace PiNat

variable {F : ℕ → Type*} [∀ i, NormedAddCommGroup (F i)]

/-- Given a countable family of normed additive groups, one may put a norm on their product
`Π i, E i`, defining the right topology and uniform structure and matching the metric space.
It is highly non-canonical, though, and therefore not registered as a global instance.
The distance we use here is `dist x y = ∑' n, min (1/2)^(encode i) (dist (x n) (y n))`. -/
protected def normedAddCommGroup : NormedAddCommGroup (Π i : ℕ, F i) :=
  PiCountable.normedAddCommGroup

end PiNat
