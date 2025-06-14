/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Jireh Loreaux
-/
import Mathlib.Algebra.Group.Center
import Mathlib.Algebra.Ring.Defs

/-!
# Centralizers of rings
-/

assert_not_exists RelIso

variable {M : Type*} {S : Set M}

namespace Set

variable {a b}

@[simp]
theorem add_mem_centralizer [Distrib M] (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
    a + b ∈ centralizer S := fun c hc => by rw [add_mul, mul_add, ha c hc, hb c hc]

@[simp]
theorem neg_mem_centralizer [Mul M] [HasDistribNeg M] (ha : a ∈ centralizer S) :
    -a ∈ centralizer S := fun c hc => by rw [mul_neg, ha c hc, neg_mul]

end Set
