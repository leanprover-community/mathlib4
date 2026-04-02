/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Data.List.SplitBy
public import Mathlib.Data.PNat.Defs

/-!
# Run-length encoding
-/

public section

variable {α : Type*}

namespace List

variable [DecidableEq α]

/-- Run-length encoding of a list. Returns a list of pairs `(n, a)` representing consecutive groups
of `a` of length `n`. -/
@[expose]
def runLength (l : List α) : List (ℕ+ × α) :=
  (l.splitBy (· == ·)).pmap
    (fun m hm ↦ (⟨m.length, length_pos_of_ne_nil hm⟩, m.head hm))
    (fun _ ↦ ne_nil_of_mem_splitBy)

@[simp]
theorem runLength_nil : runLength ([] : List α) = [] :=
  rfl

@[simp]
theorem runLength_eq_nil {l : List α} : runLength l = [] ↔ l = [] := by
  rw [runLength, pmap_eq_nil_iff, splitBy_eq_nil]

theorem runLength_append {n : ℕ} (hn : 0 < n) {a : α} {l : List α} (ha : a ∉ l.head?) :
    (replicate n a ++ l).runLength = (⟨n, hn⟩, a) :: l.runLength := by
  suffices splitBy (· == ·) (replicate n a ++ l) = replicate n a :: l.splitBy (· == ·) by
    simp [this, runLength]
  apply (splitBy_append ..).trans
  · rw [splitBy_beq_replicate hn.ne', singleton_append]
  · grind

@[simp]
theorem runLength_replicate {n : ℕ} (hn : 0 < n) (a : α) :
    runLength (replicate n a) = [(⟨n, hn⟩, a)] := by
  convert runLength_append hn (a := a) (l := []) _ <;> simp

theorem runLength_append_cons {n : ℕ} (hn : 0 < n) {a b : α} {l : List α} (h : a ≠ b) :
    runLength (replicate n a ++ b :: l) = (⟨n, hn⟩, a) :: (b :: l).runLength := by
  apply runLength_append hn
  rwa [head?_cons, Option.mem_some_iff, eq_comm]

@[simp]
theorem flatten_map_runLength (l : List α) :
    (l.runLength.map fun x ↦ replicate x.1 x.2).flatten = l := by
  rw [runLength, map_pmap, pmap_eq_self.2, flatten_splitBy]
  intro m hm
  have := isChain_of_mem_splitBy hm
  simp_rw [beq_iff_eq, isChain_eq_iff_eq_replicate] at this
  exact (this _ (head_mem_head? _)).symm

theorem runLength_injective : Function.Injective (List.runLength (α := α)) := by
  intro l m h
  have := flatten_map_runLength m
  rwa [← h, flatten_map_runLength] at this

@[simp]
theorem runLength_inj {l m : List α} : l.runLength = m.runLength ↔ l = m :=
  runLength_injective.eq_iff

theorem runLength_flatten_map {l : List (ℕ+ × α)} (hl : l.IsChain fun x y ↦ x.2 ≠ y.2) :
    (l.map fun x ↦ replicate x.1 x.2).flatten.runLength = l := by
  induction l with
  | nil => rfl
  | cons x l IH =>
    rw [isChain_cons] at hl
    rw [map_cons, flatten_cons, runLength_append, IH hl.2]
    · rfl
    · cases l with
      | nil => simp
      | cons y l => simpa [head?_replicate] using (hl.1 y head?_cons).symm

private theorem isChain_runLengthAux {α : Type*} {l : List (List α)} (hn : ∀ m ∈ l, m ≠ [])
    (h : ∀ m (hm : m ∈ l), m.head (hn m hm) = m.getLast (hn m hm))
    (hl : l.IsChain fun a b ↦ ∃ ha hb, a.getLast ha ≠ b.head hb) :
    (l.pmap List.head hn).IsChain Ne := by
  induction l with
  | nil => exact isChain_nil
  | cons a l IH => cases l with grind

theorem isChain_runLength (l : List α) : l.runLength.IsChain fun x y ↦ x.2 ≠ y.2 := by
  rw [runLength]
  apply (List.isChain_map (β := ℕ+ × α) Prod.snd).1
  rw [map_pmap]
  apply isChain_runLengthAux
  · intro m hm
    have := isChain_of_mem_splitBy hm
    simp_rw [beq_iff_eq, isChain_eq_iff_eq_replicate] at this
    generalize_proofs hm
    obtain ⟨n, a, hm'⟩ : ∃ n a, m = replicate n a := ⟨_, _, this _ (head_mem_head? hm)⟩
    simp [hm']
  · simpa using isChain_getLast_head_splitBy (· == ·) l

private def runLengthRecOnAux (l : List (ℕ+ × α)) {p : List α → Sort*}
    (hc : l.IsChain fun x y ↦ x.2 ≠ y.2) (hn : p [])
    (hi : ∀ (n : ℕ+) {a l}, a ∉ l.head? → p l → p (replicate n a ++ l)) :
    p (l.map fun x ↦ replicate x.1 x.2).flatten :=
  match l with
  | [] => hn
  | (n, a) :: l => by
    rw [isChain_cons] at hc
    apply hi _ _ (runLengthRecOnAux l hc.2 hn hi)
    cases l with
    | nil => simp
    | cons x l => simpa [head?_replicate] using (hc.1 x head?_cons).symm

/-- Recursion on the run-length encoding of a list. -/
@[elab_as_elim]
def runLengthRecOn (l : List α) {p : List α → Sort*} (nil : p [])
    (append : ∀ (n : ℕ+) (a l), a ∉ l.head? → p l → p (replicate n a ++ l)) : p l :=
  cast (congr_arg p (flatten_map_runLength l))
    (runLengthRecOnAux l.runLength (isChain_runLength _) nil append)

@[simp]
theorem runLengthRecOn_nil {p : List α → Sort*} (nil : p [])
    (append : ∀ (n : ℕ+) (a l), a ∉ l.head? → p l → p (replicate n a ++ l)) :
    runLengthRecOn [] nil append = nil :=
  (rfl)

set_option backward.isDefEq.respectTransparency false in
theorem runLengthRecOn_append {p : List α → Sort*} {n : ℕ} (h : 0 < n) {a : α} {l : List α}
    (hl : a ∉ l.head?) (nil : p [])
    (append : ∀ (n : ℕ+) (a l), a ∉ l.head? → p l → p (replicate n a ++ l)) :
    runLengthRecOn (replicate n a ++ l) nil append =
      append ⟨n, h⟩ _ _ hl (runLengthRecOn l nil append) := by
  rw [runLengthRecOn, runLengthRecOn, cast_eq_iff_heq]
  have H := runLength_append h hl
  trans runLengthRecOnAux _ (H ▸ isChain_runLength _) nil append
  · congr!
  · rw [runLengthRecOnAux]
    congr! <;> simp

theorem splitBy_beq (l : List α) :
    l.splitBy (· == ·) = l.runLength.map fun x ↦ replicate x.1 x.2 := by
  induction l using runLengthRecOn with
  | nil => rfl
  | append n a l ha IH =>
    rw [splitBy_append, runLength_append _ ha, map_cons, IH]
    · simp
    · simp
    · grind

end List
