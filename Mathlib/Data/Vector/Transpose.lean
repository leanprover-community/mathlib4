/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
import Mathlib.Data.Vector.MapLemmas
import Mathlib.Data.List.Transpose

open Mathlib

def List.vectorTranspose {α : Type*} {n : ℕ} (l : List (Vector α n)) : Vector (List α) n :=
  if hl : l.length = 0 then ⟨List.replicate n [], by simp⟩ else
  ⟨(l.map Vector.toList).ttranspose, by
    conv_lhs =>
      rw [length_ttranspose]
      lhs
      tactic =>
        convert List.minimum?_replicate_of_pos (by simp : min n n = n) (Nat.pos_of_ne_zero hl)
        simp only [map_map, eq_replicate, length_map, mem_map, Function.comp_apply,
          Vector.toList_length, exists_and_right, and_imp, forall_exists_index,
          forall_apply_eq_imp_iff₂, implies_true, and_self]
    rfl⟩

lemma List.vectorTranspose_getElem {α : Type*} {n i : ℕ} (l : List (Vector α n)) (hi : i < n) :
    l.vectorTranspose[i] = l.map (·[i]) := by
  simp only [vectorTranspose, length_eq_zero]
  split
  · simpa [Vector.getElem_def, ← List.length_eq_zero]
  simp only [Vector.getElem_def, Vector.toList_mk, ttranspose_getElem, pmap_map]
  change l.pmap (fun a h ↦ a.toList[i]'(by simpa)) _ = _
  simp

namespace Mathlib.Vector

def listTranspose {α : Type*} {n : ℕ} (l : Vector (List α) n) : List (Vector α n) :=
  l.toList.ttranspose.pmap Subtype.mk (fun _ b ↦ by simp [List.length_of_mem_ttranspose _ _ b])

lemma map_getElem_listTranspose {α : Type*} {n i : ℕ}
    (l : Vector (List α) n) (h : i < n) (hl : ∀ x ∈ l.toList, l[i].length ≤ x.length) :
    l.listTranspose.map (·[i]) = l[i] := by
  simp [listTranspose, List.map_pmap]
  conv_lhs => simp [Vector.getElem_def]
  conv_rhs => apply (List.ttranspose_pmap_getElem l.toList _ _ hl).symm
  apply List.pmap_congr
  simp

def vectorTranspose {α : Type*} {n m : ℕ} (l : Vector (Vector α m) n) : Vector (Vector α n) m :=
  l.toList.vectorTranspose.pmap Subtype.mk (fun _ b ↦ by
    unfold List.vectorTranspose at b
    split at b
    · simp_all
    · simp [List.length_of_mem_ttranspose _ _ b]
  )

@[simp]
def vectorTranspose_list_eq_listTranpose {α : Type*} {n m : ℕ} [NeZero n]
    (l : Vector (Vector α m) n) : l.vectorTranspose.toList = (l.map toList).listTranspose := by
  simp [vectorTranspose, listTranspose, List.vectorTranspose, NeZero.ne n]

lemma map_getElem_vectorTranspose {α : Type*} {n m i : ℕ}
    (l : Vector (Vector α m) n) (h : i < n) :
    l.vectorTranspose.map (·[i]) = l[i] := by
  apply toList_injective
  have : NeZero n := ⟨Nat.not_eq_zero_of_lt h⟩
  simp [map_getElem_listTranspose]

end Mathlib.Vector
