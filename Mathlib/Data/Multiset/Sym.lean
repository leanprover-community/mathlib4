/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Data.List.Sym

/-! # Unordered tuples of elements of a multiset

Defines `Multiset.sym` and the specialized `Multiset.sym2` for computing multisets of all
unordered n-tuples from a given multiset. These are multiset versions of `Nat.multichoose`.

## Main declarations

* `Multiset.sym`: `xs.sym n` is the multiset of all unordered n-tuples of elements from `xs`,
  with multiplicity. The multiset's values are in `Sym α n`.
* `Multiset.sym2`: `xs.sym2` is the multiset of all unordered pairs of elements from `xs`,
  with multiplicity. The multiset's values are in `Sym2 α`.

-/

namespace Multiset

variable {α : Type*}

section Sym

-- /-- `xs.sym n` is all unordered `n`-tuples from the multiset `xs`. -/
-- protected def sym (n : Nat) (m : Multiset α) : Multiset (Sym α n) :=
--   m.liftOn (fun xs => xs.sym n) sorry

end Sym

section Sym2

/-- `m.sym2` is the multiset of all unordered pairs of elements from `m`, with multiplicity.
If `m` has no duplicates then neither does `m.sym2`. -/
protected def sym2 (m : Multiset α) : Multiset (Sym2 α) :=
  m.liftOn (fun xs => xs.sym2) fun _ _ h => by rw [coe_eq_coe]; exact h.sym2

@[simp] theorem sym2_coe (xs : List α) : (xs : Multiset α).sym2 = xs.sym2 := rfl

theorem mk_mem_sym2_iff {m : Multiset α} {a b : α} :
    Quotient.mk _ (a, b) ∈ m.sym2 ↔ a ∈ m ∧ b ∈ m :=
  m.recOnSubsingleton fun xs => by simp [List.mk_mem_sym2_iff]

protected theorem Nodup.sym2 {m : Multiset α} (h : m.Nodup) : m.sym2.Nodup :=
  Quotient.recOnSubsingleton m (fun _ h => List.Nodup.sym2 h) h

@[simp]
theorem sym2_eq_zero {m : Multiset α} : m.sym2 = 0 ↔ m = 0 :=
  m.recOnSubsingleton fun xs => by simp

end Sym2

end Multiset
