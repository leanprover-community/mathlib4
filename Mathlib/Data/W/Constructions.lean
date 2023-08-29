/-
Copyright (c) 2015 Joseph Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Hua
-/
import Mathlib.Data.W.Basic

#align_import data.W.constructions from "leanprover-community/mathlib"@"861a26926586cd46ff80264d121cdb6fa0e35cc1"

/-!
# Examples of W-types

We take the view of W types as inductive types.
Given `α : Type` and `β : α → Type`, the W type determined by this data, `WType β`, is the
inductively with constructors from `α` and arities of each constructor `a : α` given by `β a`.

This file contains `Nat` and `List` as examples of W types.

## Main results
* `WType.equivNat`: the construction of the naturals as a W-type is equivalent to `Nat`
* `WType.equivList`: the construction of lists on a type `γ` as a W-type is equivalent to `List γ`
-/


universe u v

namespace WType

-- For "W_type"
set_option linter.uppercaseLean3 false

section Nat

/-- The constructors for the naturals -/
inductive Natα : Type
  | zero : Natα
  | succ : Natα
#align W_type.nat_α WType.Natα

instance : Inhabited Natα :=
  ⟨Natα.zero⟩

/-- The arity of the constructors for the naturals, `zero` takes no arguments, `succ` takes one -/
def Natβ : Natα → Type
  | Natα.zero => Empty
  | Natα.succ => Unit
#align W_type.nat_β WType.Natβ

instance : Inhabited (Natβ Natα.succ) :=
  ⟨()⟩

/-- The isomorphism from the naturals to its corresponding `WType` -/
@[simp]
def ofNat : ℕ → WType Natβ
  | Nat.zero => ⟨Natα.zero, Empty.elim⟩
  | Nat.succ n => ⟨Natα.succ, fun _ ↦ ofNat n⟩
#align W_type.of_nat WType.ofNat

/-- The isomorphism from the `WType` of the naturals to the naturals -/
@[simp]
def toNat : WType Natβ → ℕ
  | WType.mk Natα.zero _ => 0
  | WType.mk Natα.succ f => (f ()).toNat.succ
#align W_type.to_nat WType.toNat

theorem leftInverse_nat : Function.LeftInverse ofNat toNat
  | WType.mk Natα.zero f => by
    rw [toNat, ofNat]
    -- ⊢ mk Natα.zero Empty.elim = mk Natα.zero f
    congr
    -- ⊢ Empty.elim = f
    ext x
    -- ⊢ Empty.elim x = f x
    cases x
    -- 🎉 no goals
  | WType.mk Natα.succ f => by
    simp only [toNat, ofNat, leftInverse_nat (f ()), mk.injEq, heq_eq_eq, true_and]
    -- ⊢ (fun x => f ()) = f
    rfl
    -- 🎉 no goals
#align W_type.left_inv_nat WType.leftInverse_nat

theorem rightInverse_nat : Function.RightInverse ofNat toNat
  | Nat.zero => rfl
  | Nat.succ n => by rw [ofNat, toNat, rightInverse_nat n]
                     -- 🎉 no goals
#align W_type.right_inv_nat WType.rightInverse_nat

/-- The naturals are equivalent to their associated `WType` -/
def equivNat : WType Natβ ≃ ℕ where
  toFun := toNat
  invFun := ofNat
  left_inv := leftInverse_nat
  right_inv := rightInverse_nat
#align W_type.equiv_nat WType.equivNat

open Sum PUnit

/-- `WType.Natα` is equivalent to `PUnit ⊕ PUnit`.
This is useful when considering the associated polynomial endofunctor.
-/
@[simps]
def NatαEquivPUnitSumPUnit : Natα ≃ Sum PUnit.{u + 1} PUnit
    where
  toFun c :=
    match c with
    | Natα.zero => inl unit
    | Natα.succ => inr unit
  invFun b :=
    match b with
    | inl _ => Natα.zero
    | inr _ => Natα.succ
  left_inv c :=
    match c with
    | Natα.zero => rfl
    | Natα.succ => rfl
  right_inv b :=
    match b with
    | inl _ => rfl
    | inr _ => rfl
#align W_type.nat_α_equiv_punit_sum_punit WType.NatαEquivPUnitSumPUnit

end Nat

section List

variable (γ : Type u)

/-- The constructors for lists.
There is "one constructor `cons x` for each `x : γ`",
since we view `List γ` as
```
| nil : List γ
| cons x₀ : List γ → List γ
| cons x₁ : List γ → List γ
|   ⋮      γ many times
```
-/
inductive Listα : Type u
  | nil : Listα
  | cons : γ → Listα
#align W_type.list_α WType.Listα

instance : Inhabited (Listα γ) :=
  ⟨Listα.nil⟩

/-- The arities of each constructor for lists, `nil` takes no arguments, `cons hd` takes one -/
def Listβ : Listα γ → Type u
  | Listα.nil => PEmpty
  | Listα.cons _ => PUnit
#align W_type.list_β WType.Listβ

instance (hd : γ) : Inhabited (Listβ γ (Listα.cons hd)) :=
  ⟨PUnit.unit⟩

/-- The isomorphism from lists to the `WType` construction of lists -/
@[simp]
def ofList : List γ → WType (Listβ γ)
  | List.nil => ⟨Listα.nil, PEmpty.elim⟩
  | List.cons hd tl => ⟨Listα.cons hd, fun _ ↦ ofList tl⟩
#align W_type.of_list WType.ofList

/-- The isomorphism from the `WType` construction of lists to lists -/
@[simp]
def toList : WType (Listβ γ) → List γ
  | WType.mk Listα.nil _ => []
  | WType.mk (Listα.cons hd) f => hd :: (f PUnit.unit).toList
#align W_type.to_list WType.toList

theorem leftInverse_list : Function.LeftInverse (ofList γ) (toList _)
  | WType.mk Listα.nil f => by
    simp only [toList, ofList, mk.injEq, heq_eq_eq, true_and]
    -- ⊢ PEmpty.elim = f
    ext x
    -- ⊢ PEmpty.elim x = f x
    cases x
    -- 🎉 no goals
  | WType.mk (Listα.cons x) f => by
    simp only [ofList, leftInverse_list (f PUnit.unit), mk.injEq, heq_eq_eq, true_and]
    -- ⊢ (fun x => f PUnit.unit) = f
    rfl
    -- 🎉 no goals
#align W_type.left_inv_list WType.leftInverse_list

theorem rightInverse_list : Function.RightInverse (ofList γ) (toList _)
  | List.nil => rfl
  | List.cons hd tl => by simp only [toList, rightInverse_list tl]
                          -- 🎉 no goals
#align W_type.right_inv_list WType.rightInverse_list

/-- Lists are equivalent to their associated `WType` -/
def equivList : WType (Listβ γ) ≃ List γ
    where
  toFun := toList _
  invFun := ofList _
  left_inv := leftInverse_list _
  right_inv := rightInverse_list _
#align W_type.equiv_list WType.equivList

/-- `WType.Listα` is equivalent to `γ` with an extra point.
This is useful when considering the associated polynomial endofunctor
-/
def ListαEquivPUnitSum : Listα γ ≃ Sum PUnit.{v + 1} γ
    where
  toFun c :=
    match c with
    | Listα.nil => Sum.inl PUnit.unit
    | Listα.cons x => Sum.inr x
  invFun := Sum.elim (fun _ ↦ Listα.nil) Listα.cons
  left_inv c :=
    match c with
    | Listα.nil => rfl
    | Listα.cons _ => rfl
  right_inv x :=
    match x with
    | Sum.inl PUnit.unit => rfl
    | Sum.inr _ => rfl
#align W_type.list_α_equiv_punit_sum WType.ListαEquivPUnitSum

end List

end WType
