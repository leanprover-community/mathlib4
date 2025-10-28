/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Wanyi He, Jiedong Jiang
-/
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.RingTheory.FilteredAlgebra.Basic
/-!
# The Associated Graded Structure

In this file we define `GradedPiece` for `IsFiltration F F_lt` on abelian groups with every `F j`
`AddSubgroup`s, and their direct sum `AssociatedGraded`.

# Main definitions and results

* `GradedPiece` : Direct summand of the associated graded abelian group to `IsFiltration F F_lt`
  with every `F i` of some `AddSubgroupClass`, defined as `F i` quotient by `F_lt i`.
1
* `AssociatedGraded` : The direct sum of `GradedPiece`s.

-/

section GeneralGraded

variable {ι : Type*}

variable {A : Type*} [AddCommGroup A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]

variable (F : ι → σ) (F_lt : outParam <| ι → σ)

@[nolint unusedArguments]
instance [Preorder ι] [IsFiltration F F_lt] (i : ι) : Setoid (AddSubgroup.ofClass (F i)) :=
  QuotientAddGroup.leftRel
    ((AddSubgroup.ofClass (F_lt i)).addSubgroupOf (AddSubgroup.ofClass (F i)))

/-- Direct summand of the associated graded abelian group to `IsFiltration F F_lt`
  with every `F i` of some `AddSubgroupClass`, defined as `F i` quotient by `F_lt i`. -/
abbrev GradedPiece (i : ι) :=
  (AddSubgroup.ofClass (F i)) ⧸
    (AddSubgroup.ofClass (F_lt i)).addSubgroupOf (AddSubgroup.ofClass (F i))

/-- Direct sum of `GradedPiece`s. -/
abbrev AssociatedGraded := DirectSum ι (GradedPiece F F_lt)

namespace AssociatedGraded

/-- `AssociatedGraded.mk F F_lt s x` is the element of `AssociatedGraded F F_lt` that is zero
outside `s` and has coefficient `x i` for `i` in `s`. -/
abbrev mk [DecidableEq ι] (s : Finset ι) :
    (∀ i : (s : Set ι), GradedPiece F F_lt i.val) →+ AssociatedGraded F F_lt :=
  DirectSum.mk (GradedPiece F F_lt) s

variable {F F_lt}

/-- The natural inclusion map from `GradedPiece F F_lt i` to `AssociatedGraded F F_lt`. -/
abbrev of [DecidableEq ι] {i : ι} : GradedPiece F F_lt i →+ AssociatedGraded F F_lt :=
  DirectSum.of (GradedPiece F F_lt) i

@[ext]
theorem ext {x y : AssociatedGraded F F_lt} (w : ∀ i, x i = y i) : x = y :=
  DirectSum.ext (GradedPiece F F_lt) w

variable [DecidableEq ι]

theorem of_eq_of_ne (i j : ι) (x : GradedPiece F F_lt i) (h : j ≠ i) : (of x) j = 0 :=
  DirectSum.of_eq_of_ne i j x h

@[simp]
theorem of_eq_self (i : ι) (x : GradedPiece F F_lt i) : (of x) i = x :=
  DirectSum.of_eq_same i x

lemma of_apply {i : ι} (j : ι) (x : GradedPiece F F_lt i) :
    of x j = if h : i = j then Eq.recOn h x else 0 :=
  DirectSum.of_apply j x

theorem mk_apply_of_mem {s : Finset ι} {f : ∀ i : (s : Set ι), GradedPiece F F_lt i.val}
    {n : ι} (hn : n ∈ s) : mk F F_lt s f n = f ⟨n, hn⟩ := by
  simp [DirectSum.mk, dif_pos hn]

theorem mk_apply_of_not_mem {s : Finset ι} {f : ∀ i : (s : Set ι), GradedPiece F F_lt i.val}
    {n : ι} (hn : n ∉ s) : mk F F_lt s f n = 0 := by
  simp [DirectSum.mk, dif_neg hn]

section support

theorem support_of (i : ι) (x : GradedPiece F F_lt i) (h : x ≠ 0)
    [(i : ι) → (x : GradedPiece F F_lt i) → Decidable (x ≠ 0)] : (of x).support = {i} :=
  DirectSum.support_of i x h

theorem support_of_subset {i : ι} {b : GradedPiece F F_lt i}
    [(i : ι) → (x : GradedPiece F F_lt i) → Decidable (x ≠ 0)] : (of b).support ⊆ {i} :=
  DirectSum.support_of_subset

theorem sum_support_of (x : AssociatedGraded F F_lt)
    [(i : ι) → (x : GradedPiece F F_lt i) → Decidable (x ≠ 0)] : (∑ i ∈ x.support, of (x i)) = x :=
  DirectSum.sum_support_of x

end support

theorem sum_univ_of [Fintype ι] (x : AssociatedGraded F F_lt) :
    ∑ i ∈ Finset.univ, of (x i) = x := by
  apply DFinsupp.ext (fun i ↦ ?_)
  rw [DFinsupp.finset_sum_apply]
  simp [of_apply]

theorem mk_injective (s : Finset ι) : Function.Injective (mk F F_lt s) :=
  DirectSum.mk_injective s

theorem of_injective (i : ι) : Function.Injective (of (i := i) (F := F) (F_lt := F_lt)) :=
  DirectSum.of_injective i

end AssociatedGraded

open AddSubgroup

namespace GradedPiece

/-- Obtaining an element of `GradedPiece i` from an element of `F i`. -/
def mk {i : ι} : (ofClass (F i)) →+ GradedPiece F F_lt i :=
  QuotientAddGroup.mk' ((ofClass (F_lt i)).addSubgroupOf (ofClass (F i)))

section

lemma induction_on {i : ι} {C : GradedPiece F F_lt i → Prop} (x : GradedPiece F F_lt i)
    (H : ∀ z, C (GradedPiece.mk F F_lt z)) : C x :=
  QuotientAddGroup.induction_on x H

lemma mk_eq {i : ι} (x : F i) : mk F F_lt x = ⟦x⟧ := rfl

end

end GradedPiece

end GeneralGraded
