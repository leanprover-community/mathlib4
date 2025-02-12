/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker
-/
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.Ring.Units

/-!
# Associated elements in rings
-/

assert_not_exists OrderedCommMonoid Multiset Field

namespace Associated
variable {M : Type*} [Monoid M] [HasDistribNeg M] {a b : M}

lemma neg_left (h : Associated a b) : Associated (-a) b := let ⟨u, hu⟩ := h; ⟨-u, by simp [hu]⟩
lemma neg_right (h : Associated a b) : Associated a (-b) := h.symm.neg_left.symm
lemma neg_neg (h : Associated a b) : Associated (-a) (-b) := h.neg_left.neg_right

end Associated
