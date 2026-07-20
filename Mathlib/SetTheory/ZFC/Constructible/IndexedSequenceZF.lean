/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.Data.List.Shortlex
public import Mathlib.SetTheory.ZFC.Constructible.FiniteSequenceZF

/-!
# Indexed finite-sequence codes

The structural list code in `FiniteSequenceZF` is convenient for recursion.
For first-order definitions of lexicographic order, however, direct access to
the entry at an internal natural-number index is more useful.  This file codes
a list by the finite graph

`{ <xs[i], i> | i < xs.length }`

and stores its length alongside that graph.  The graph convention agrees with
Mathlib's convention that a function graph contains `<output,input>`.
-/

@[expose] public section

universe u

namespace Constructible

/--
For lists of equal length, lexicographic comparison occurs at a first index:
the prefixes before that index agree and the entries there satisfy `r`.
-/
theorem listLex_iff_exists_index {α : Type u} {r : α → α → Prop}
    {xs ys : List α} (hlength : xs.length = ys.length) :
    List.Lex r xs ys ↔
      ∃ k : Nat, ∃ hx : k < xs.length, ∃ hy : k < ys.length,
        xs.take k = ys.take k ∧
          r (xs.get ⟨k, hx⟩) (ys.get ⟨k, hy⟩) := by
  induction xs generalizing ys with
  | nil =>
      have hys : ys = [] := List.length_eq_zero_iff.mp hlength.symm
      subst ys
      simp
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlength
      | cons y ys =>
          have htail : xs.length = ys.length := Nat.succ.inj hlength
          constructor
          · intro hlex
            cases hlex with
            | rel hxy =>
                exact ⟨0, by simp, by simp, by simp [hxy]⟩
            | cons hrest =>
                rcases (ih htail).mp hrest with
                  ⟨k, hkx, hky, htake, hk⟩
                refine ⟨k + 1, by simp [hkx], by simp [hky], ?_, ?_⟩
                · simp [htake]
                · simpa using hk
          · rintro ⟨k, hkx, hky, htake, hk⟩
            cases k with
            | zero =>
                exact List.Lex.rel (by simpa using hk)
            | succ k =>
                have hcons : x = y ∧ xs.take k = ys.take k := by
                  simpa using List.cons.inj htake
                rcases hcons with ⟨rfl, htakeTail⟩
                apply List.Lex.cons
                apply (ih htail).mpr
                refine ⟨k, ?_, ?_, htakeTail, ?_⟩
                · simpa using hkx
                · simpa using hky
                · simpa using hk

namespace IndexedSequenceZF

open FiniteSequenceZF

/-- The indexed graph of a list, with indices beginning at `start`. -/
noncomputable def graphFrom (start : Nat) : List ZFSet.{u} → ZFSet.{u}
  | [] => ∅
  | x :: xs =>
      insert (ZFSet.pair x (natCode start)) (graphFrom (start + 1) xs)

@[simp]
theorem graphFrom_nil (start : Nat) :
    graphFrom start ([] : List ZFSet.{u}) = ∅ :=
  rfl

@[simp]
theorem graphFrom_cons (start : Nat) (x : ZFSet.{u})
    (xs : List ZFSet.{u}) :
    graphFrom start (x :: xs) =
      insert (ZFSet.pair x (natCode start)) (graphFrom (start + 1) xs) :=
  rfl

/-- Exact membership description of the indexed graph. -/
@[simp]
theorem mem_graphFrom_iff (start : Nat) (xs : List ZFSet.{u})
    (q : ZFSet.{u}) :
    q ∈ graphFrom start xs ↔
      ∃ i : Fin xs.length,
        q = ZFSet.pair (xs.get i) (natCode (start + i.1)) := by
  induction xs generalizing start with
  | nil =>
      simp [graphFrom]
  | cons x xs ih =>
      rw [graphFrom_cons, ZFSet.mem_insert_iff, ih]
      constructor
      · rintro (rfl | ⟨i, rfl⟩)
        · refine ⟨0, ?_⟩
          simp
        · refine ⟨i.succ, ?_⟩
          simp [Nat.add_comm, Nat.add_left_comm]
      · rintro ⟨i, rfl⟩
        refine Fin.cases ?_ (fun j => ?_) i
        · left
          simp
        · right
          refine ⟨j, ?_⟩
          simp [Nat.add_comm, Nat.add_left_comm]

/-- The indexed graph itself is constructible when all entries are. -/
theorem graphFrom_mem_L {xs : List ZFSet.{u}}
    (hxs : ∀ x ∈ xs, x ∈ L) (start : Nat) :
    graphFrom start xs ∈ L := by
  induction xs generalizing start with
  | nil =>
      exact empty_mem_L
  | cons x xs ih =>
      rw [graphFrom_cons, ZFSet.insert_eq]
      apply union_mem_L
      · apply singleton_mem_L
        exact orderedPair_mem_L
          (hxs x (by simp)) (natCode_mem_L start)
      · apply ih
        intro y hy
        exact hxs y (by simp [hy])

/-- The graph of a list, indexed from zero. -/
noncomputable def graph (xs : List ZFSet.{u}) : ZFSet.{u} :=
  graphFrom 0 xs

@[simp]
theorem mem_graph_iff (xs : List ZFSet.{u}) (q : ZFSet.{u}) :
    q ∈ graph xs ↔
      ∃ i : Fin xs.length,
        q = ZFSet.pair (xs.get i) (natCode i.1) := by
  simp [graph]

/-- A sequence code consists of its length and its indexed graph. -/
noncomputable def sequenceCode (xs : List ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pair (natCode xs.length) (graph xs)

/-- The indexed graph together with its length determines the list. -/
theorem sequenceCode_injective :
    Function.Injective (sequenceCode : List ZFSet.{u} → ZFSet.{u}) := by
  intro xs ys hcode
  have hparts := ZFSet.pair_inj.mp hcode
  have hlength : xs.length = ys.length :=
    natCode_injective hparts.1
  apply List.ext_get hlength
  intro k hkx hky
  let i : Fin xs.length := ⟨k, hkx⟩
  have hmemX :
      ZFSet.pair (xs.get i) (natCode k) ∈ graph xs := by
    apply (mem_graph_iff xs _).mpr
    exact ⟨i, rfl⟩
  have hmemY :
      ZFSet.pair (xs.get i) (natCode k) ∈ graph ys := by
    rw [← hparts.2]
    exact hmemX
  rcases (mem_graph_iff ys _).mp hmemY with ⟨j, hpair⟩
  have hpairParts := ZFSet.pair_inj.mp hpair
  have hindex : k = j.1 := natCode_injective hpairParts.2
  simpa only [i, hindex] using hpairParts.1

@[simp]
theorem sequenceCode_inj {xs ys : List ZFSet.{u}} :
    sequenceCode xs = sequenceCode ys ↔ xs = ys :=
  sequenceCode_injective.eq_iff

/-- Indexed sequence codes of constructible entries are constructible. -/
theorem sequenceCode_mem_L {xs : List ZFSet.{u}}
    (hxs : ∀ x ∈ xs, x ∈ L) : sequenceCode xs ∈ L := by
  exact orderedPair_mem_L (natCode_mem_L xs.length)
    (graphFrom_mem_L hxs 0)

end IndexedSequenceZF

end Constructible
