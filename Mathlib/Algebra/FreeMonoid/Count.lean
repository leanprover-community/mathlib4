/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.List.Count

#align_import algebra.free_monoid.count from "leanprover-community/mathlib"@"a2d2e18906e2b62627646b5d5be856e6a642062f"

/-!
# `List.count` as a bundled homomorphism

In this file we define `FreeMonoid.countp`, `FreeMonoid.count`, `FreeAddMonoid.countp`, and
`FreeAddMonoid.count`. These are `List.countp` and `List.count` bundled as multiplicative and
additive homomorphisms from `FreeMonoid` and `FreeAddMonoid`.

We do not use `to_additive` because it can't map `Multiplicative ℕ` to `ℕ`.
-/

variable {α : Type*} (p : α → Prop) [DecidablePred p]

namespace FreeAddMonoid

/-- `List.countp` as a bundled additive monoid homomorphism. -/
def countp : FreeAddMonoid α →+ ℕ where
  toFun := List.countp p
  map_zero' := List.countp_nil _
  map_add' := List.countp_append _
#align free_add_monoid.countp FreeAddMonoid.countp

theorem countp_of (x : α) : countp p (of x) = if p x = true then 1 else 0 := by
  simp [countp, List.countp, List.countp.go]
#align free_add_monoid.countp_of FreeAddMonoid.countp_of

theorem countp_apply (l : FreeAddMonoid α) : countp p l = List.countp p l := rfl
#align free_add_monoid.countp_apply FreeAddMonoid.countp_apply

/-- `List.count` as a bundled additive monoid homomorphism. -/
-- Porting note: was (x = ·)
def count [DecidableEq α] (x : α) : FreeAddMonoid α →+ ℕ := countp (· = x)
#align free_add_monoid.count FreeAddMonoid.count

theorem count_of [DecidableEq α] (x y : α) : count x (of y) = (Pi.single x 1 : α → ℕ) y := by
  simp [Pi.single, Function.update, count, countp, List.countp, List.countp.go,
    Bool.beq_eq_decide_eq]
#align free_add_monoid.count_of FreeAddMonoid.count_of

theorem count_apply [DecidableEq α] (x : α) (l : FreeAddMonoid α) : count x l = List.count x l :=
  rfl
#align free_add_monoid.count_apply FreeAddMonoid.count_apply

end FreeAddMonoid

namespace FreeMonoid

/-- `List.countp` as a bundled multiplicative monoid homomorphism. -/
def countp : FreeMonoid α →* Multiplicative ℕ :=
    AddMonoidHom.toMultiplicative (FreeAddMonoid.countp p)
#align free_monoid.countp FreeMonoid.countp

theorem countp_of' (x : α) :
    countp p (of x) = if p x then Multiplicative.ofAdd 1 else Multiplicative.ofAdd 0 := by
    erw [FreeAddMonoid.countp_of]
    simp only [eq_iff_iff, iff_true, ofAdd_zero]; rfl
#align free_monoid.countp_of' FreeMonoid.countp_of'

theorem countp_of (x : α) : countp p (of x) = if p x then Multiplicative.ofAdd 1 else 1 := by
  rw [countp_of', ofAdd_zero]
#align free_monoid.countp_of FreeMonoid.countp_of

-- `rfl` is not transitive
theorem countp_apply (l : FreeAddMonoid α) : countp p l = Multiplicative.ofAdd (List.countp p l) :=
  rfl
#align free_monoid.countp_apply FreeMonoid.countp_apply

/-- `List.count` as a bundled additive monoid homomorphism. -/
def count [DecidableEq α] (x : α) : FreeMonoid α →* Multiplicative ℕ := countp (· = x)
#align free_monoid.count FreeMonoid.count

theorem count_apply [DecidableEq α] (x : α) (l : FreeAddMonoid α) :
    count x l = Multiplicative.ofAdd (List.count x l) := rfl
#align free_monoid.count_apply FreeMonoid.count_apply

theorem count_of [DecidableEq α] (x y : α) :
    count x (of y) = @Pi.mulSingle α (fun _ => Multiplicative ℕ) _ _ x (Multiplicative.ofAdd 1) y :=
  by simp [count, countp_of, Pi.mulSingle_apply, eq_comm, Bool.beq_eq_decide_eq]
#align free_monoid.count_of FreeMonoid.count_of

end FreeMonoid
