/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module algebra.free_monoid.count
! leanprover-community/mathlib commit a2d2e18906e2b62627646b5d5be856e6a642062f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.FreeMonoid.Basic
import Mathbin.Data.List.Count

/-!
# `list.count` as a bundled homomorphism

In this file we define `free_monoid.countp`, `free_monoid.count`, `free_add_monoid.countp`, and
`free_add_monoid.count`. These are `list.countp` and `list.count` bundled as multiplicative and
additive homomorphisms from `free_monoid` and `free_add_monoid`.

We do not use `to_additive` because it can't map `multiplicative ℕ` to `ℕ`.
-/


variable {α : Type _} (p : α → Prop) [DecidablePred p]

namespace FreeAddMonoid

/-- `list.countp` as a bundled additive monoid homomorphism. -/
def countp (p : α → Prop) [DecidablePred p] : FreeAddMonoid α →+ ℕ :=
  ⟨List.countp p, List.countp_nil p, List.countp_append _⟩
#align free_add_monoid.countp FreeAddMonoid.countp

theorem countp_of (x : α) : countp p (of x) = if p x then 1 else 0 :=
  rfl
#align free_add_monoid.countp_of FreeAddMonoid.countp_of

theorem countp_apply (l : FreeAddMonoid α) : countp p l = List.countp p l :=
  rfl
#align free_add_monoid.countp_apply FreeAddMonoid.countp_apply

/-- `list.count` as a bundled additive monoid homomorphism. -/
def count [DecidableEq α] (x : α) : FreeAddMonoid α →+ ℕ :=
  countp (Eq x)
#align free_add_monoid.count FreeAddMonoid.count

theorem count_of [DecidableEq α] (x y : α) : count x (of y) = Pi.single x 1 y := by
  simp only [count, countp_of, Pi.single_apply, eq_comm]
#align free_add_monoid.count_of FreeAddMonoid.count_of

theorem count_apply [DecidableEq α] (x : α) (l : FreeAddMonoid α) : count x l = List.count x l :=
  rfl
#align free_add_monoid.count_apply FreeAddMonoid.count_apply

end FreeAddMonoid

namespace FreeMonoid

/-- `list.countp` as a bundled multiplicative monoid homomorphism. -/
def countp (p : α → Prop) [DecidablePred p] : FreeMonoid α →* Multiplicative ℕ :=
  (FreeAddMonoid.countp p).toMultiplicative
#align free_monoid.countp FreeMonoid.countp

theorem countp_of' (x : α) :
    countp p (of x) = if p x then Multiplicative.ofAdd 1 else Multiplicative.ofAdd 0 :=
  rfl
#align free_monoid.countp_of' FreeMonoid.countp_of'

theorem countp_of (x : α) : countp p (of x) = if p x then Multiplicative.ofAdd 1 else 1 := by
  rw [countp_of', ofAdd_zero]
#align free_monoid.countp_of FreeMonoid.countp_of

-- `rfl` is not transitive
theorem countp_apply (l : FreeAddMonoid α) : countp p l = Multiplicative.ofAdd (List.countp p l) :=
  rfl
#align free_monoid.countp_apply FreeMonoid.countp_apply

/-- `list.count` as a bundled additive monoid homomorphism. -/
def count [DecidableEq α] (x : α) : FreeMonoid α →* Multiplicative ℕ :=
  countp (Eq x)
#align free_monoid.count FreeMonoid.count

theorem count_apply [DecidableEq α] (x : α) (l : FreeAddMonoid α) :
    count x l = Multiplicative.ofAdd (List.count x l) :=
  rfl
#align free_monoid.count_apply FreeMonoid.count_apply

theorem count_of [DecidableEq α] (x y : α) :
    count x (of y) = @Pi.mulSingle α (fun _ => Multiplicative ℕ) _ _ x (Multiplicative.ofAdd 1) y :=
  by simp only [count, countp_of, Pi.mulSingle_apply, eq_comm]
#align free_monoid.count_of FreeMonoid.count_of

end FreeMonoid

