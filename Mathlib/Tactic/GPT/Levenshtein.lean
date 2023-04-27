/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki, Zach Battleman, Scott Morrison
-/
import Std.Data.List.Basic

/-!
# Levenshtein Distance
-/

namespace List

/-- Implementation of `levenshtein`. Assumes the first list is not longer than the second list. -/
def levenshtein' [BEq α] (s₀ : List α) (s₁ : List α) : Nat :=
  let v₀ := List.range (s₁.length + 1) |>.toArray
  let v₁ := Array.mkArray (s₁.length + 1) 0

  let ⟨v₀, _⟩ : Array Nat × Array Nat :=
    s₀.foldlIdx (fun i ⟨v₀, v₁⟩ c₀ =>
      let v₁ := v₁.set! 0 (i + 1)

      let v₁ : Array Nat :=
        s₁.foldlIdx (fun j v₁ c₁ =>
          let delCost := (v₀.get! (j + 1)) + 1
          let insCost := (v₁.get! j) + 1
          let subCost :=
            if c₀ == c₁ then v₀.get! j else (v₀.get! j) + 1
          v₁.set! (j + 1) (min (min delCost insCost) subCost))
        v₁

      ⟨v₁, v₀⟩)
    ⟨v₀, v₁⟩

  v₀.get! s₁.length

/-- Levenshtein distance between two lists. -/
def levenshtein [BEq α] (s₀ : List α) (s₁ : List α) : Nat :=
  if s₀.length ≤ s₁.length then levenshtein' s₀ s₁
  else levenshtein' s₁ s₀

end List

namespace String

/-- Levenshtein distance between two strings. -/
def levenshtein (s₀ : String) (s₁ : String) : Nat :=
  s₀.toList.levenshtein s₁.toList

end String

#eval "sitting".levenshtein "kitten" = 3
#eval "guard".levenshtein "lords" = 4
