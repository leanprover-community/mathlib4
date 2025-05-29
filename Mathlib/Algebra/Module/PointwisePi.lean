/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Scalar

/-!
# Pointwise actions on sets in Pi types

This file contains lemmas about pointwise actions on sets in Pi types.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication, pi

-/

open Pointwise

open Set

variable {K ι : Type*} {R : ι → Type*}

@[to_additive]
theorem smul_pi_subset [∀ i, SMul K (R i)] (r : K) (s : Set ι) (t : ∀ i, Set (R i)) :
    r • pi s t ⊆ pi s (r • t) :=
  piMap_image_pi_subset _

@[to_additive]
theorem smul_univ_pi [∀ i, SMul K (R i)] (r : K) (t : ∀ i, Set (R i)) :
    r • pi (univ : Set ι) t = pi (univ : Set ι) (r • t) :=
  piMap_image_univ_pi _ _

@[to_additive]
theorem smul_pi [Group K] [∀ i, MulAction K (R i)] (r : K) (S : Set ι) (t : ∀ i, Set (R i)) :
    r • S.pi t = S.pi (r • t) :=
  piMap_image_pi (fun _ _ => MulAction.surjective _) _

theorem smul_pi₀ [GroupWithZero K] [∀ i, MulAction K (R i)] {r : K} (S : Set ι) (t : ∀ i, Set (R i))
    (hr : r ≠ 0) : r • S.pi t = S.pi (r • t) :=
  smul_pi (Units.mk0 r hr) S t
