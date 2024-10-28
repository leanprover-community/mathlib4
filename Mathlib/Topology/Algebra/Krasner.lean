/-
Copyright (c) 2024 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/

import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Krasner's Lemma

In this file, we prove Krasner's lemma. Instead of state and prove the Krasner's lemma directly,
we define a predicate `IsKrasner K L` for arbitary field extensions `L / K` with a normed/valued
instance on `L` as the abstraction of the conclusion of the Krasner's lemma. Then we prove the
Krasner's lemma holds for `L / K` if `K` is a complete normed/valued field and the norm/valuation
on `L` is compatible with the one on `K`.

## Main definitions

## Main results

## Tags

## TODO

-/

variable (K L: Type*) {ΓL : Type*} [LinearOrderedCommGroupWithZero ΓL]
    [Field K] [Field L] [Algebra K L] [vL : Valued L ΓL]

class IsKrasner : Prop where
  krasner' : ∀ {x y : L}, IsSeparable K x → (minpoly K x).Splits (algebraMap K L) →
    IsIntegral K y → (∀ x' : L, IsConjRoot K x x' → x ≠ x' → vL.v (x - y) < vL.v (x - x')) →
      x ∈ K⟮y⟯
-- `As an application of IsKrasner, prove that C_p is algebraically closed,`
-- ` accelerating integrating into mathlib`
class IsKrasnerNorm (K L : Type*) [Field K] [NormedField L] [Algebra K L] : Prop where
  krasner_norm' : ∀ {x y : L}, IsSeparable K x → (minpoly K x).Splits (algebraMap K L) →
    IsIntegral K y → (∀ x' : L, IsConjRoot K x x' →  x ≠ x' → ‖x - y‖ < ‖x - x'‖) →
      x ∈ K⟮y⟯
