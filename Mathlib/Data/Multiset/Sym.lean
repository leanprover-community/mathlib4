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

* `Multiset.sym2`: `xs.sym2` is the multiset of all unordered pairs of elements from `xs`,
  with multiplicity. The multiset's values are in `Sym2 α`.

## TODO

* Once `List.Perm.sym` is defined, define
  ```lean
  protected def sym (n : Nat) (m : Multiset α) : Multiset (Sym α n) :=
    m.liftOn (fun xs => xs.sym n) (List.perm.sym n)
  ```
  and then use this to remove the `DecidableEq` assumption from `Finset.sym`.

* `theorem injective_sym2 : Function.Injective (Multiset.sym2 : Multiset α → _)`

* `theorem strictMono_sym2 : StrictMono (Multiset.sym2 : Multiset α → _)`

-/

namespace Multiset

variable {α : Type*}

section Sym2

/-- `m.sym2` is the multiset of all unordered pairs of elements from `m`, with multiplicity.
If `m` has no duplicates then neither does `m.sym2`. -/
protected def sym2 (m : Multiset α) : Multiset (Sym2 α) :=
  m.liftOn (fun xs => xs.sym2) fun _ _ h => by rw [coe_eq_coe]; exact h.sym2

@[simp] theorem sym2_coe (xs : List α) : (xs : Multiset α).sym2 = xs.sym2 := rfl

@[simp]
theorem sym2_eq_zero_iff {m : Multiset α} : m.sym2 = 0 ↔ m = 0 :=
  m.inductionOn fun xs => by simp

theorem mk_mem_sym2_iff {m : Multiset α} {a b : α} :
    s(a, b) ∈ m.sym2 ↔ a ∈ m ∧ b ∈ m :=
  m.inductionOn fun xs => by simp [List.mk_mem_sym2_iff]

theorem mem_sym2_iff {m : Multiset α} {z : Sym2 α} :
    z ∈ m.sym2 ↔ ∀ y ∈ z, y ∈ m :=
  m.inductionOn fun xs => by simp [List.mem_sym2_iff]

protected theorem Nodup.sym2 {m : Multiset α} (h : m.Nodup) : m.sym2.Nodup :=
  m.inductionOn (fun _ h => List.Nodup.sym2 h) h

open scoped List in
@[simp, mono]
theorem sym2_mono {m m' : Multiset α} (h : m ≤ m') : m.sym2 ≤ m'.sym2 := by
  refine Quotient.inductionOn₂ m m' (fun xs ys h => ?_) h
  suffices xs <+~ ys from this.sym2
  simpa only [quot_mk_to_coe, coe_le, sym2_coe] using h

theorem monotone_sym2 : Monotone (Multiset.sym2 : Multiset α → _) := fun _ _ => sym2_mono

theorem card_sym2 {m : Multiset α} :
    Multiset.card m.sym2 = Nat.choose (Multiset.card m + 1) 2 := by
  refine m.inductionOn fun xs => ?_
  simp [List.length_sym2]

end Sym2

end Multiset
