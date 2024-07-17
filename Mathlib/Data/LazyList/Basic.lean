/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Control.Traversable.Equiv
import Mathlib.Control.Traversable.Instances
import Batteries.Data.LazyList
import Mathlib.Lean.Thunk

#align_import data.lazy_list.basic from "leanprover-community/mathlib"@"1f0096e6caa61e9c849ec2adbd227e960e9dff58"

/-!
## Definitions on lazy lists

This file contains various definitions and proofs on lazy lists.

TODO: This file will soon be deprecated.
-/


universe u

namespace LazyList

open Function

/-- Isomorphism between strict and lazy lists. -/
def listEquivLazyList (α : Type*) : List α ≃ LazyList α where
  toFun := LazyList.ofList
  invFun := LazyList.toList
  right_inv := by
    intro xs
    induction xs using toList.induct
    · simp [toList, ofList]
    · simp [toList, ofList, *]; rfl
  left_inv := by
    intro xs
    induction xs
    · simp [toList, ofList]
    · simpa [ofList, toList]
#align lazy_list.list_equiv_lazy_list LazyList.listEquivLazyList

#align lazy_list.traverse LazyList.traverse

instance : Traversable LazyList where
  map := @LazyList.traverse Id _
  traverse := @LazyList.traverse

instance : LawfulTraversable LazyList := by
  apply Equiv.isLawfulTraversable' listEquivLazyList <;> intros <;> ext <;> rename_i f xs
  · induction' xs using LazyList.rec with _ _ _ _ ih
    · simp only [Functor.map, LazyList.traverse, pure, Equiv.map, listEquivLazyList,
        Equiv.coe_fn_symm_mk, toList, Equiv.coe_fn_mk, ofList]
    · simpa only [Equiv.map, Functor.map, listEquivLazyList, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk,
        LazyList.traverse, Seq.seq, toList, ofList, cons.injEq, true_and]
    · ext; apply ih
  · simp only [Equiv.map, listEquivLazyList, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, comp,
      Functor.mapConst]
    induction' xs using LazyList.rec with _ _ _ _ ih
    · simp only [LazyList.traverse, pure, Functor.map, toList, ofList]
    · simpa only [toList, ofList, LazyList.traverse, Seq.seq, Functor.map, cons.injEq, true_and]
    · congr; apply ih
  · simp only [traverse, Equiv.traverse, listEquivLazyList, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
    induction' xs using LazyList.rec with _ tl ih _ ih
    · simp only [LazyList.traverse, toList, List.traverse, map_pure, ofList]
    · replace ih : tl.get.traverse f = ofList <$> tl.get.toList.traverse f := ih
      simp [traverse.eq_2, ih, Functor.map_map, seq_map_assoc, toList, List.traverse, map_seq,
        Function.comp, Thunk.pure, ofList]
    · apply ih

#align lazy_list.init LazyList.init
#align lazy_list.find LazyList.find
#align lazy_list.interleave LazyList.interleave
#align lazy_list.interleave_all LazyList.interleaveAll
#align lazy_list.bind LazyList.bind
#align lazy_list.reverse LazyList.reverse
#align lazy_list.append_nil LazyList.append_nil
#align lazy_list.append_assoc LazyList.append_assoc
#align lazy_list.append_bind LazyList.append_bind

@[simp] theorem bind_singleton {α} (x : LazyList α) : x.bind singleton = x := by
  induction x using LazyList.rec (motive_2 := fun xs => xs.get.bind singleton = xs.get) with
  | nil => simp [LazyList.bind]
  | cons h t ih =>
    simp only [LazyList.bind, singleton, append, Thunk.get_pure, Thunk.get_mk, cons.injEq, true_and]
    ext
    simp [ih]
  | mk f ih => simp_all

instance : LawfulMonad LazyList := LawfulMonad.mk'
  (id_map := by
    intro α xs
    induction xs using LazyList.rec (motive_2 := fun xs => id <$> xs.get = xs) with
    | nil => simp only [Functor.map, comp_id, LazyList.bind]
    | cons h t _ => simp only [Functor.map, comp_id, bind_singleton]
    | mk f _ => ext; simp_all)
  (pure_bind := by
    intros
    simp only [bind, pure, singleton, LazyList.bind, append, Thunk.pure, Thunk.get]
    apply append_nil)
  (bind_assoc := by
    intro _ _ _ xs _ _
    induction' xs using LazyList.rec with _ _ _ _ ih
    · simp only [bind, LazyList.bind]
    · simp only [bind, LazyList.bind, append_bind]; congr
    · congr; funext; apply ih)
  (bind_pure_comp := by
    intro _ _ f xs
    simp only [bind, Functor.map, pure, singleton]
    induction xs using LazyList.traverse.induct (m := @Id) (f := f) with
    | case1 =>
      simp only [Thunk.pure, LazyList.bind, LazyList.traverse, Id.pure_eq]
    | case2 _ _ ih =>
      simp [LazyList.bind, LazyList.traverse, Seq.seq, Id.map_eq, append, Thunk.pure]
      rw [← ih]
      simp only [Thunk.get, append, singleton, Thunk.pure])

#align lazy_list.mfirst LazyList.mfirstₓ
#align lazy_list.mem LazyList.Mem
#align lazy_list.mem.decidable LazyList.Mem.decidable
#align lazy_list.mem_nil LazyList.mem_nil
#align lazy_list.mem_cons LazyList.mem_cons
#align lazy_list.forall_mem_cons LazyList.forall_mem_cons
#align lazy_list.pmap LazyList.pmap
#align lazy_list.attach LazyList.attach

end LazyList
