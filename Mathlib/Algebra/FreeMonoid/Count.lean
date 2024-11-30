/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Group.TypeTags.Hom

/-!
# `List.count` as a bundled homomorphism

In this file we define `FreeMonoid.countP`, `FreeMonoid.count`, `FreeAddMonoid.countP`, and
`FreeAddMonoid.count`. These are `List.countP` and `List.count` bundled as multiplicative and
additive homomorphisms from `FreeMonoid` and `FreeAddMonoid`.

We do not use `to_additive` because it can't map `Multiplicative ℕ` to `ℕ`.
-/

variable {α : Type*} (p : α → Prop) [DecidablePred p]

namespace FreeAddMonoid

/-- `List.countP` as a bundled additive monoid homomorphism. -/
def countP : FreeAddMonoid α →+ ℕ where
  toFun := List.countP p
  map_zero' := List.countP_nil _
  map_add' := List.countP_append _

theorem countP_of (x : α) : countP p (of x) = if p x = true then 1 else 0 := by
  simp [countP, List.countP, List.countP.go]

theorem countP_apply (l : FreeAddMonoid α) : countP p l = List.countP p l := rfl

/-- `List.count` as a bundled additive monoid homomorphism. -/
-- Porting note: was (x = ·)
def count [DecidableEq α] (x : α) : FreeAddMonoid α →+ ℕ := countP (· = x)

theorem count_of [DecidableEq α] (x y : α) : count x (of y) = (Pi.single x 1 : α → ℕ) y := by
  simp [Pi.single, Function.update, count, countP, List.countP, List.countP.go,
    Bool.beq_eq_decide_eq]

theorem count_apply [DecidableEq α] (x : α) (l : FreeAddMonoid α) : count x l = List.count x l :=
  rfl

end FreeAddMonoid

namespace FreeMonoid

/-- `List.countP` as a bundled multiplicative monoid homomorphism. -/
def countP : FreeMonoid α →* Multiplicative ℕ :=
    AddMonoidHom.toMultiplicative (FreeAddMonoid.countP p)

theorem countP_of' (x : α) :
    countP p (of x) = if p x then Multiplicative.ofAdd 1 else Multiplicative.ofAdd 0 := by
    erw [FreeAddMonoid.countP_of]
    simp only [eq_iff_iff, iff_true, ofAdd_zero]; rfl

theorem countP_of (x : α) : countP p (of x) = if p x then Multiplicative.ofAdd 1 else 1 := by
  rw [countP_of', ofAdd_zero]

-- `rfl` is not transitive
theorem countP_apply (l : FreeAddMonoid α) : countP p l = Multiplicative.ofAdd (List.countP p l) :=
  rfl

/-- `List.count` as a bundled additive monoid homomorphism. -/
def count [DecidableEq α] (x : α) : FreeMonoid α →* Multiplicative ℕ := countP (· = x)

theorem count_apply [DecidableEq α] (x : α) (l : FreeAddMonoid α) :
    count x l = Multiplicative.ofAdd (List.count x l) := rfl

theorem count_of [DecidableEq α] (x y : α) :
    count x (of y) = @Pi.mulSingle α (fun _ => Multiplicative ℕ) _ _ x (Multiplicative.ofAdd 1) y :=
  by simp [count, countP_of, Pi.mulSingle_apply, eq_comm, Bool.beq_eq_decide_eq]

end FreeMonoid
