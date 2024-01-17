/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Prod
import Std.Classes.Dvd

/-!
# Lemmas about the divisibility relation in product (semi)groups
-/

variable {G₁ : Type*} {G₂ : Type*} [Semigroup G₁] [Semigroup G₂]

theorem prod_dvd_iff {x y : G₁ × G₂} :
    x ∣ y ↔ x.1 ∣ y.1 ∧ x.2 ∣ y.2 := by
  cases x; cases y
  simp only [dvd_def, Prod.exists, Prod.mk_mul_mk, Prod.mk.injEq,
    exists_and_left, exists_and_right, and_self, true_and]

@[simp]
theorem Prod.mk_dvd_mk {x₁ y₁ : G₁} {x₂ y₂ : G₂} :
    (x₁, x₂) ∣ (y₁, y₂) ↔ x₁ ∣ y₁ ∧ x₂ ∣ y₂ :=
  prod_dvd_iff
