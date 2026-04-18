/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Kim Morrison, Alex Keizer
-/
module

public import Mathlib.Data.List.OfFn
public import Batteries.Data.List.Perm
public import Mathlib.Data.List.Nodup

/-!
# Lists of elements of `Fin n`

This file develops some results on `finRange n`.
-/

public section

assert_not_exists Monoid

universe u

namespace List

variable {α : Type u}


@[simp]
lemma count_finRange {n : ℕ} (a : Fin n) : count a (finRange n) = 1 := by
  simp [List.Nodup.count (nodup_finRange n)]

@[simp] theorem idxOf_finRange {k : ℕ} (i : Fin k) : (finRange k).idxOf i = i := by
  simpa using (nodup_finRange k).idxOf_getElem i

@[deprecated finRange_eq_nil_iff (since := "2025-11-04")]
alias finRange_eq_nil := finRange_eq_nil_iff

@[deprecated (since := "2025-11-04")]
alias finRange_map_get := map_get_finRange

@[deprecated (since := "2025-11-04")]
alias finRange_map_getElem := map_getElem_finRange

@[deprecated (since := "2025-11-04")]
alias map_coe_finRange := map_coe_finRange_eq_range

@[deprecated finRange_succ (since := "2025-10-10")]
theorem finRange_succ_eq_map (n : ℕ) : finRange n.succ = 0 :: (finRange n).map Fin.succ :=
  finRange_succ

theorem ofFn_eq_pmap {n} {f : Fin n → α} :
    ofFn f = pmap (fun i hi => f ⟨i, hi⟩) (range n) fun _ => mem_range.1 := by
  ext
  grind

theorem ofFn_id (n) : ofFn id = finRange n :=
  (rfl)

theorem ofFn_eq_map {n} {f : Fin n → α} : ofFn f = (finRange n).map f := by
  rw [← ofFn_id, map_ofFn, Function.comp_id]

theorem nodup_ofFn_ofInjective {n} {f : Fin n → α} (hf : Function.Injective f) :
    Nodup (ofFn f) := by
  rw [ofFn_eq_pmap]
  exact nodup_range.pmap fun _ _ _ _ H => Fin.val_eq_of_eq <| hf H

theorem nodup_ofFn {n} {f : Fin n → α} : Nodup (ofFn f) ↔ Function.Injective f := by
  refine ⟨?_, nodup_ofFn_ofInjective⟩
  refine Fin.consInduction ?_ (fun x₀ xs ih => ?_) f
  · intro _
    exact Function.injective_of_subsingleton _
  · intro h
    rw [Fin.cons_injective_iff]
    simp_rw [ofFn_succ, Fin.cons_succ, nodup_cons, Fin.cons_zero, mem_ofFn] at h
    exact h.imp_right ih

end List

open List

theorem Equiv.Perm.map_finRange_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    map σ (finRange n) ~ finRange n := by
  rw [perm_ext_iff_of_nodup ((nodup_finRange n).map σ.injective) <| nodup_finRange n]
  simpa [mem_map, mem_finRange] using σ.surjective

/-- The list obtained from a permutation of a tuple `f` is permutation equivalent to
the list obtained from `f`. -/
theorem Equiv.Perm.ofFn_comp_perm {n : ℕ} {α : Type u} (σ : Equiv.Perm (Fin n)) (f : Fin n → α) :
    ofFn (f ∘ σ) ~ ofFn f := by
  rw [ofFn_eq_map, ofFn_eq_map, ← map_map]
  exact σ.map_finRange_perm.map f
