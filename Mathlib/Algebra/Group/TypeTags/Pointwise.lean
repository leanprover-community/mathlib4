/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Bingyu Xia
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Lemmas about pointwise operations in the presence of `Multiplicative` and `Additive`.
-/

@[expose] public section


open Pointwise

variable {M : Type*}

namespace Multiplicative

variable [AddMonoid M]

@[simp]
lemma ofAdd_image_setAdd (s t : Set M) :
    Multiplicative.ofAdd '' (s + t) = Multiplicative.ofAdd '' s * Multiplicative.ofAdd '' t := by
  rw [← Set.image2_add, Set.image_image2_distrib ofAdd_add, Set.image2_mul]

@[simp]
lemma ofAdd_image_nsmul (n : ℕ) (s : Set M) :
    Multiplicative.ofAdd '' (n • s) = (Multiplicative.ofAdd '' s) ^ n := by
  induction n with
  | zero => simp; rfl
  | succ n IH => simp [succ_nsmul, pow_succ, IH]

end Multiplicative

namespace Additive

variable [Monoid M]

@[simp]
lemma ofMul_image_setMul (s t : Set M) :
    Additive.ofMul '' (s * t) = Additive.ofMul '' s + Additive.ofMul '' t := by
  rw [← Set.image2_mul, Set.image_image2_distrib ofMul_mul, Set.image2_add]

@[simp]
lemma ofMul_image_pow (n : ℕ) (s : Set M) :
    Additive.ofMul '' (s ^ n) = n • (Additive.ofMul '' s) := by
  induction n with
  | zero => simp; rfl
  | succ n IH => simp [succ_nsmul, pow_succ, IH]

end Additive
