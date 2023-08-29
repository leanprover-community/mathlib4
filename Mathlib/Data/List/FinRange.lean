/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Scott Morrison
-/
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Perm

#align_import data.list.fin_range from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# Lists of elements of `Fin n`

This file develops some results on `finRange n`.
-/


universe u

namespace List

variable {α : Type u}

@[simp]
theorem map_coe_finRange (n : ℕ) : ((finRange n) : List (Fin n)).map (Fin.val) = List.range n := by
  simp_rw [finRange, map_pmap, pmap_eq_map]
  -- ⊢ map (fun a => a) (range n) = range n
  exact List.map_id _
  -- 🎉 no goals
#align list.map_coe_fin_range List.map_coe_finRange

theorem finRange_succ_eq_map (n : ℕ) : finRange n.succ = 0 :: (finRange n).map Fin.succ := by
  apply map_injective_iff.mpr Fin.val_injective
  -- ⊢ map Fin.val (finRange (Nat.succ n)) = map Fin.val (0 :: map Fin.succ (finRan …
  rw [map_cons, map_coe_finRange, range_succ_eq_map, Fin.val_zero, ← map_coe_finRange, map_map,
    map_map]
  simp only [Function.comp, Fin.val_succ]
  -- 🎉 no goals
#align list.fin_range_succ_eq_map List.finRange_succ_eq_map

-- Porting note : `map_nth_le` moved to `List.finRange_map_get` in Data.List.Range

theorem ofFn_eq_pmap {α n} {f : Fin n → α} :
    ofFn f = pmap (fun i hi => f ⟨i, hi⟩) (range n) fun _ => mem_range.1 := by
  rw [pmap_eq_map_attach]
  -- ⊢ ofFn f = map (fun x => f { val := ↑x, isLt := (_ : ↑x < n) }) (attach (range …
  exact ext_get (by simp) fun i hi1 hi2 => by simp [get_ofFn f ⟨i, hi1⟩]
  -- 🎉 no goals
#align list.of_fn_eq_pmap List.ofFn_eq_pmap

theorem ofFn_id (n) : ofFn id = finRange n :=
  ofFn_eq_pmap
#align list.of_fn_id List.ofFn_id

theorem ofFn_eq_map {α n} {f : Fin n → α} : ofFn f = (finRange n).map f := by
  rw [← ofFn_id, map_ofFn, Function.right_id]
  -- 🎉 no goals
#align list.of_fn_eq_map List.ofFn_eq_map

theorem nodup_ofFn_ofInjective {α n} {f : Fin n → α} (hf : Function.Injective f) :
    Nodup (ofFn f) := by
  rw [ofFn_eq_pmap]
  -- ⊢ Nodup (pmap (fun i hi => f { val := i, isLt := hi }) (range n) (_ : ∀ (x : ℕ …
  exact (nodup_range n).pmap fun _ _ _ _ H => Fin.veq_of_eq <| hf H
  -- 🎉 no goals
#align list.nodup_of_fn_of_injective List.nodup_ofFn_ofInjective

theorem nodup_ofFn {α n} {f : Fin n → α} : Nodup (ofFn f) ↔ Function.Injective f := by
  refine' ⟨_, nodup_ofFn_ofInjective⟩
  -- ⊢ Nodup (ofFn f) → Function.Injective f
  refine' Fin.consInduction _ (fun x₀ xs ih => _) f
  -- ⊢ Nodup (ofFn Fin.elim0) → Function.Injective Fin.elim0
  · intro _
    -- ⊢ Function.Injective Fin.elim0
    exact Function.injective_of_subsingleton _
    -- 🎉 no goals
  · intro h
    -- ⊢ Function.Injective (Fin.cons x₀ xs)
    rw [Fin.cons_injective_iff]
    -- ⊢ ¬x₀ ∈ Set.range xs ∧ Function.Injective xs
    simp_rw [ofFn_succ, Fin.cons_succ, nodup_cons, Fin.cons_zero, mem_ofFn] at h
    -- ⊢ ¬x₀ ∈ Set.range xs ∧ Function.Injective xs
    exact h.imp_right ih
    -- 🎉 no goals
#align list.nodup_of_fn List.nodup_ofFn

end List

open List

theorem Equiv.Perm.map_finRange_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    map σ (finRange n) ~ finRange n := by
  rw [perm_ext ((nodup_finRange n).map σ.injective) <| nodup_finRange n]
  -- ⊢ ∀ (a : Fin n), a ∈ map (↑σ) (finRange n) ↔ a ∈ finRange n
  simpa [mem_map, mem_finRange, true_and_iff, iff_true_iff] using σ.surjective
  -- 🎉 no goals
#align equiv.perm.map_fin_range_perm Equiv.Perm.map_finRange_perm

/-- The list obtained from a permutation of a tuple `f` is permutation equivalent to
the list obtained from `f`. -/
theorem Equiv.Perm.ofFn_comp_perm {n : ℕ} {α : Type u} (σ : Equiv.Perm (Fin n)) (f : Fin n → α) :
    ofFn (f ∘ σ) ~ ofFn f := by
  rw [ofFn_eq_map, ofFn_eq_map, ← map_map]
  -- ⊢ map f (map (↑σ) (finRange n)) ~ map f (finRange n)
  exact σ.map_finRange_perm.map f
  -- 🎉 no goals
#align equiv.perm.of_fn_comp_perm Equiv.Perm.ofFn_comp_perm
