/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Lemmas about pointwise operations in the presence of `Multiplicative` and `Additive`.
-/

public section

open Pointwise

variable {M : Type*}

namespace Multiplicative

variable [AddMonoid M]

@[simp]
lemma ofAdd_image_setAdd (s t : Set M) :
    ofAdd '' (s + t) = ofAdd '' s * ofAdd '' t := by
  rw [← Set.image2_add, Set.image_image2_distrib ofAdd_add, Set.image2_mul]

@[simp]
lemma ofAdd_image_nsmul (n : ℕ) (s : Set M) :
    ofAdd '' (n • s) = (ofAdd '' s) ^ n := by
  induction n with
  | zero => simp; rfl
  | succ n IH => simp [succ_nsmul, pow_succ, IH]

@[simp]
lemma toAdd_image_setMul (s t : Set (Multiplicative M)) :
    toAdd '' (s * t) = (toAdd '' s) + (toAdd '' t) := by
  rw [← Set.image2_mul, Set.image_image2_distrib toAdd_mul, Set.image2_add]

@[simp]
lemma toAdd_image_nsmul (n : ℕ) (s : Set (Multiplicative M)) :
    toAdd '' (s ^ n) = n • (toAdd '' s) := by
  induction n with
  | zero => simp; rfl
  | succ n IH => simp [succ_nsmul, pow_succ, IH]

end Multiplicative
