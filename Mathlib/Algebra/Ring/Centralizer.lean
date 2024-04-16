/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Jireh Loreaux
-/
import Mathlib.Algebra.Group.Centralizer
import Mathlib.Algebra.Ring.Defs

#align_import group_theory.subsemigroup.centralizer from "leanprover-community/mathlib"@"cc67cd75b4e54191e13c2e8d722289a89e67e4fa"

/-!
# Centralizers of rings
-/


variable {M : Type*} {S T : Set M}

namespace Set

variable {a b}

@[simp]
theorem add_mem_centralizer [Distrib M] (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
    a + b ∈ centralizer S := fun c hc => by rw [add_mul, mul_add, ha c hc, hb c hc]
#align set.add_mem_centralizer Set.add_mem_centralizer

@[simp]
theorem neg_mem_centralizer [Mul M] [HasDistribNeg M] (ha : a ∈ centralizer S) :
    -a ∈ centralizer S := fun c hc => by rw [mul_neg, ha c hc, neg_mul]
#align set.neg_mem_centralizer Set.neg_mem_centralizer

end Set
