/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.Data.Sum.Order

/-!
# Extending a well-order by a final block

This file contains the order-theoretic device used to keep successive
constructible-stage orders coherent.  A carrier is split into an old part
and its complement.  The old part is ordered first, the new part second.
Thus the old part is an initial segment by construction.
-/

@[expose] public section

universe u

namespace Constructible

noncomputable section

/-- Split a type into the subtype satisfying `p` and its complement. -/
def partitionEquiv {A : Type u} (p : A -> Prop) :
    A ≃ ({x : A // p x} ⊕ {x : A // Not (p x)}) := by
  classical
  refine
    { toFun := fun x =>
        if hx : p x then Sum.inl ⟨x, hx⟩ else Sum.inr ⟨x, hx⟩
      invFun := fun
        | Sum.inl x => x.1
        | Sum.inr x => x.1
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    by_cases hx : p x <;> simp [hx]
  · intro x
    cases x with
    | inl x => simp [x.2]
    | inr x => simp [x.2]

/--
Lexicographically order the `p`-part before its complement, using the two
given relations inside the respective blocks.
-/
def partitionLexRel {A : Type u} (p : A -> Prop)
    (oldRel : {x : A // p x} -> {x : A // p x} -> Prop)
    (newRel : {x : A // Not (p x)} ->
      {x : A // Not (p x)} -> Prop) :
    A -> A -> Prop :=
  InvImage (Sum.Lex oldRel newRel) (partitionEquiv p)

theorem partitionLexRel_isWellOrder {A : Type u} (p : A -> Prop)
    (oldRel : {x : A // p x} -> {x : A // p x} -> Prop)
    (newRel : {x : A // Not (p x)} ->
      {x : A // Not (p x)} -> Prop)
    [IsWellOrder {x : A // p x} oldRel]
    [IsWellOrder {x : A // Not (p x)} newRel] :
    IsWellOrder A (partitionLexRel p oldRel newRel) := by
  letI : IsWellOrder
      ({x : A // p x} ⊕ {x : A // Not (p x)})
      (Sum.Lex oldRel newRel) := by
    infer_instance
  exact
    { wf := InvImage.wf (partitionEquiv p)
        (IsWellFounded.wf : WellFounded (Sum.Lex oldRel newRel))
      trichotomous :=
        (InvImage.trichotomous (r := Sum.Lex oldRel newRel)
          (partitionEquiv p).injective).trichotomous }

@[simp]
theorem partitionLexRel_old_old {A : Type u} (p : A -> Prop)
    (oldRel : {x : A // p x} -> {x : A // p x} -> Prop)
    (newRel : {x : A // Not (p x)} ->
      {x : A // Not (p x)} -> Prop)
    {x y : A} (hx : p x) (hy : p y) :
    partitionLexRel p oldRel newRel x y <->
      oldRel ⟨x, hx⟩ ⟨y, hy⟩ := by
  simp [partitionLexRel, partitionEquiv, hx, hy, InvImage]

@[simp]
theorem partitionLexRel_old_new {A : Type u} (p : A -> Prop)
    (oldRel : {x : A // p x} -> {x : A // p x} -> Prop)
    (newRel : {x : A // Not (p x)} ->
      {x : A // Not (p x)} -> Prop)
    {x y : A} (hx : p x) (hy : Not (p y)) :
    partitionLexRel p oldRel newRel x y := by
  simp [partitionLexRel, partitionEquiv, hx, hy, InvImage]

@[simp]
theorem partitionLexRel_new_old {A : Type u} (p : A -> Prop)
    (oldRel : {x : A // p x} -> {x : A // p x} -> Prop)
    (newRel : {x : A // Not (p x)} ->
      {x : A // Not (p x)} -> Prop)
    {x y : A} (hx : Not (p x)) (hy : p y) :
    Not (partitionLexRel p oldRel newRel x y) := by
  simp [partitionLexRel, partitionEquiv, hx, hy, InvImage]

@[simp]
theorem partitionLexRel_new_new {A : Type u} (p : A -> Prop)
    (oldRel : {x : A // p x} -> {x : A // p x} -> Prop)
    (newRel : {x : A // Not (p x)} ->
      {x : A // Not (p x)} -> Prop)
    {x y : A} (hx : Not (p x)) (hy : Not (p y)) :
    partitionLexRel p oldRel newRel x y <->
      newRel ⟨x, hx⟩ ⟨y, hy⟩ := by
  simp [partitionLexRel, partitionEquiv, hx, hy, InvImage]

end

end Constructible
