/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Scott Morrison, Alex Keizer
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
  exact List.map_id _
#align list.map_coe_fin_range List.map_coe_finRange

theorem finRange_succ_eq_map (n : ℕ) : finRange n.succ = 0 :: (finRange n).map Fin.succ := by
  apply map_injective_iff.mpr Fin.val_injective
  rw [map_cons, map_coe_finRange, range_succ_eq_map, Fin.val_zero, ← map_coe_finRange, map_map,
    map_map]
  simp only [Function.comp, Fin.val_succ]
#align list.fin_range_succ_eq_map List.finRange_succ_eq_map

theorem finRange_succ (n : ℕ) :
    finRange n.succ = (finRange n |>.map Fin.castSucc |>.concat ⟨n, Nat.lt.base _⟩) := by
  apply map_injective_iff.mpr Fin.val_injective
  simp [range_succ, show Fin.val ∘ Fin.castSucc = @Fin.val n from rfl]

-- Porting note : `map_nth_le` moved to `List.finRange_map_get` in Data.List.Range

theorem ofFn_eq_pmap {α n} {f : Fin n → α} :
    ofFn f = pmap (fun i hi => f ⟨i, hi⟩) (range n) fun _ => mem_range.1 := by
  rw [pmap_eq_map_attach]
  exact ext_get (by simp) fun i hi1 hi2 => by simp [get_ofFn f ⟨i, hi1⟩]
#align list.of_fn_eq_pmap List.ofFn_eq_pmap

theorem ofFn_id (n) : ofFn id = finRange n :=
  ofFn_eq_pmap
#align list.of_fn_id List.ofFn_id

theorem ofFn_eq_map {α n} {f : Fin n → α} : ofFn f = (finRange n).map f := by
  rw [← ofFn_id, map_ofFn, Function.right_id]
#align list.of_fn_eq_map List.ofFn_eq_map

theorem nodup_ofFn_ofInjective {α n} {f : Fin n → α} (hf : Function.Injective f) :
    Nodup (ofFn f) := by
  rw [ofFn_eq_pmap]
  exact (nodup_range n).pmap fun _ _ _ _ H => Fin.veq_of_eq <| hf H
#align list.nodup_of_fn_of_injective List.nodup_ofFn_ofInjective

theorem nodup_ofFn {α n} {f : Fin n → α} : Nodup (ofFn f) ↔ Function.Injective f := by
  refine' ⟨_, nodup_ofFn_ofInjective⟩
  refine' Fin.consInduction _ (fun x₀ xs ih => _) f
  · intro _
    exact Function.injective_of_subsingleton _
  · intro h
    rw [Fin.cons_injective_iff]
    simp_rw [ofFn_succ, Fin.cons_succ, nodup_cons, Fin.cons_zero, mem_ofFn] at h
    exact h.imp_right ih
#align list.nodup_of_fn List.nodup_ofFn

/-- Folding over a list obtained from a function `g : Fin n → α` is equivalent to
    folding over the list of indices `0, 1, ..., n-1` and invoking `g` for each index -/
theorem List.foldl_ofFn {α β n} (f : α → β → α) (init : α) (g : Fin n → β) :
    (List.ofFn g).foldl f init = (List.finRange n).foldl (fun a i => f a (g i)) init := by
  induction' n with n ih generalizing init
  · rfl
  · simp [List.finRange_succ_eq_map, List.foldl_map, ih]

/-- Folding over a list obtained from a function `g : Fin n → α` is equivalent to
    folding over the list of indices `0, 1, ..., n-1` and invoking `g` for each index -/
theorem List.foldr_ofFn {α β n} (f : β → α → α) (init : α) (g : Fin n → β) :
    (List.ofFn g).foldr f init = (List.finRange n).foldr (fun i a => f (g i) a) init := by
  suffices ∀ {m} (h : n ≤ m) (g : Fin m → β),
      (ofFn fun i ↦ g (i.castLE h)).foldr f init  =
      (finRange n |>.map (Fin.castLE h)).foldr (fun i a ↦ f (g i) a) init by
    specialize this (Nat.le.refl) g
    simp at this
    exact this
  clear g
  intro m h g
  induction' n with n ih generalizing init
  · rfl
  · simp only [ofFn_succ', Fin.castLE_castSucc, concat_eq_append, foldr_append, foldr_cons,
      foldr_nil, ih, finRange_succ, map_append, map_map, Fin.castLE_comp_castSucc, map_cons,
      Fin.castLE_mk, map_nil]
    rfl

end List

open List

theorem Equiv.Perm.map_finRange_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    map σ (finRange n) ~ finRange n := by
  rw [perm_ext ((nodup_finRange n).map σ.injective) <| nodup_finRange n]
  simpa [mem_map, mem_finRange, true_and_iff, iff_true_iff] using σ.surjective
#align equiv.perm.map_fin_range_perm Equiv.Perm.map_finRange_perm

/-- The list obtained from a permutation of a tuple `f` is permutation equivalent to
the list obtained from `f`. -/
theorem Equiv.Perm.ofFn_comp_perm {n : ℕ} {α : Type u} (σ : Equiv.Perm (Fin n)) (f : Fin n → α) :
    ofFn (f ∘ σ) ~ ofFn f := by
  rw [ofFn_eq_map, ofFn_eq_map, ← map_map]
  exact σ.map_finRange_perm.map f
#align equiv.perm.of_fn_comp_perm Equiv.Perm.ofFn_comp_perm
