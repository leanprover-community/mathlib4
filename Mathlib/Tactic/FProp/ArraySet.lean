/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Std.Data.Array.Merge
import Std.Data.List.Basic
import Std.Classes.SetNotation

namespace Mathlib

namespace Meta.FProp
/--
  `Array α` that is guaranteed to be sorted based on `[Ord α]` and has no duplicates.

  WARRNING: `Ord α` is assumed to be lawful, currently there is no typeclass for it.
  -/
structure ArraySet (α : Type _) [ord : Ord α] where
  data : Array α
  isSet : data.sortAndDeduplicate = data
deriving Hashable

namespace ArraySet 

  variable {α} [ord : Ord α]

  def size (as : ArraySet α) : Nat := as.data.size

  instance : GetElem (ArraySet α) Nat α (λ as i => i < as.size) where
    getElem as i h := as.data.get ⟨i, h⟩

  def toArray (as : ArraySet α) : Array α := as.data
  def toList (as : ArraySet α) : List α := as.data.toList

  instance : Coe (ArraySet α) (Array α) := ⟨λ as => as.data⟩
  instance [ToString α] : ToString (ArraySet α) := ⟨λ as => toString as.data⟩

  def _root_.Array.toArraySet (as : Array α) : ArraySet α where
    data := as.sortAndDeduplicate
    isSet := sorry

  def mem (as : ArraySet α) (a : α) [DecidableEq α] : Bool := Id.run do
    for a' in as.toArray do
      if a' = a then
        return true
    return false

  instance [DecidableEq α] : Membership α (ArraySet α) where
    mem a as := as.mem a

  instance [DecidableEq α] (a : α) (as : ArraySet α) : Decidable (a ∈ as) := 
    if h : as.mem a then
      .isTrue h
    else
      .isFalse h
  
  instance : HasSubset (ArraySet α) where
    Subset as bs := (List.Subset as.toList bs.toList)

  -- TODO: This needs lawful Ord
  instance (a b : ArraySet α) : Decidable (a ⊆ b) := Id.run do
    let mut j := 0
    for h : i in [0:b.size] do
      if h' : (a.size - j) > (b.size - i) then
        return isFalse sorry
      if h' : j < a.size then
        have _ := h.2
        match compare b[i] a[j] with
        | .eq => 
          j := j + 1
          continue
        | .lt => 
          continue
        | .gt => 
          return isFalse sorry
      else
        -- we have exhausted whole as
        return isTrue sorry

    if j = a.size then
      isTrue sorry
    else
      isFalse sorry

  instance (a b : ArraySet α) [DecidableEq α] : Decidable (a = b) := Id.run do
    if h : a.size = b.size then
      for h' : i in [0:a.size] do
        have : i < a.size := h'.2
        have : i < b.size := h ▸ h'.2
        if a[i] ≠ b[i] then
          return isFalse sorry
      return isTrue sorry
    else
      return isFalse sorry

  -- def lexOrd [Ord α] (a b : ArraySet α) : Ordering := a.data.lexOrd b.data 
      
  -- def a := #[1,2,3,4].toArraySet
  -- def b := #[4,3,2].toArraySet

  -- #eval (b ⊆ a)

  -- #exit 
