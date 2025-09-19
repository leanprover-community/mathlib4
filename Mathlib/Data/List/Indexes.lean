/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Mathlib.Util.AssertExists
import Mathlib.Data.List.Defs

/-!
# Lemmas about List.*Idx functions.

Some specification lemmas for `List.mapIdx`, `List.mapIdxM`, `List.foldlIdx` and `List.foldrIdx`.

As of 2025-01-29, these are not used anywhere in Mathlib. Moreover, with
`List.enum` and `List.enumFrom` being replaced by `List.zipIdx`
in Lean's `nightly-2025-01-29` release, they now use deprecated functions and theorems.
Rather than updating this unused material, we are deprecating it.
Anyone wanting to restore this material is welcome to do so, but will need to update uses of
`List.enum` and `List.enumFrom` to use `List.zipIdx` instead.
However, note that this material will later be implemented in the Lean standard library.
-/

assert_not_exists MonoidWithZero

universe u v

open Function

namespace List

variable {α : Type u} {β : Type v}

section MapIdx

theorem mapIdx_append_one : ∀ {f : ℕ → α → β} {l : List α} {e : α},
    mapIdx f (l ++ [e]) = mapIdx f l ++ [f l.length e] :=
  mapIdx_concat

theorem mapIdx_eq_ofFn (l : List α) (f : ℕ → α → β) :
    l.mapIdx f = ofFn fun i : Fin l.length ↦ f (i : ℕ) (l.get i) := by
  induction l generalizing f with
  | nil => simp
  | cons _ _ IH => simp [IH]

end MapIdx

section MapIdxM'

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]

theorem mapIdxMAux'_eq_mapIdxMGo {α} (f : ℕ → α → m PUnit) (as : List α) (arr : Array PUnit) :
    mapIdxMAux' f arr.size as = mapIdxM.go f as arr *> pure PUnit.unit := by
  induction as generalizing arr with
  | nil => simp only [mapIdxMAux', mapIdxM.go, seqRight_eq, map_pure, seq_pure]
  | cons head tail ih =>
    simp only [mapIdxMAux', seqRight_eq, map_eq_pure_bind, seq_eq_bind, bind_pure_unit,
      LawfulMonad.bind_assoc, pure_bind, mapIdxM.go]
    generalize (f (Array.size arr) head) = head
    have : (arr.push ⟨⟩).size = arr.size + 1 := Array.size_push _
    rw [← this, ih]
    simp only [seqRight_eq, map_eq_pure_bind, seq_pure, LawfulMonad.bind_assoc, pure_bind]

theorem mapIdxM'_eq_mapIdxM {α} (f : ℕ → α → m PUnit) (as : List α) :
    mapIdxM' f as = mapIdxM f as *> pure PUnit.unit :=
  mapIdxMAux'_eq_mapIdxMGo f as #[]

end MapIdxM'

end List
