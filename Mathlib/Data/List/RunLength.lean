/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Data.List.SplitBy
import Mathlib.Data.PNat.Defs
import Mathlib.Order.TypeTags

/-!
# Run-length encoding
-/

variable {α : Type*}

namespace List

variable [DecidableEq α]

/-- Run-length encoding of a list. Returns a list of pairs `(n, a)` representing consecutive groups
of `a` of length `n`. -/
def RunLength (l : List α) : List (ℕ+ × α) :=
  (l.splitBy (· == ·)).pmap
    (fun m hm ↦ (⟨m.length, length_pos_of_ne_nil hm⟩, m.head hm))
    (fun _ ↦ ne_nil_of_mem_splitBy _)

@[simp]
theorem runLength_nil : RunLength ([] : List α) = [] :=
  rfl

@[simp]
theorem runLength_eq_nil {l : List α} : RunLength l = [] ↔ l = [] := by
  rw [RunLength, pmap_eq_nil_iff, splitBy_eq_nil]

theorem runLength_append {n : ℕ} (hn : 0 < n) {a : α} {l : List α} (ha : a ∉ l.head?) :
    (replicate n a ++ l).RunLength = (⟨n, hn⟩, a) :: l.RunLength := by
  suffices splitBy (· == ·) (replicate n a ++ l) = replicate n a :: l.splitBy (· == ·) by
    simp [this, RunLength, attachWith]
  apply splitBy_append
  case hn => simpa using hn.ne'
  · simp_rw [beq_iff_eq]
    exact chain'_replicate_of_rel n rfl
  · cases l with
    | nil => simp
    | cons b l =>
      rw [Option.mem_def, eq_comm] at ha
      simpa using ha

@[simp]
theorem runLength_replicate {n : ℕ} (hn : 0 < n) (a : α) :
    RunLength (replicate n a) = [(⟨n, hn⟩, a)] := by
  convert runLength_append hn (a := a) (l := []) _ <;> simp

theorem runLength_append_cons {n : ℕ} (hn : 0 < n) {a b : α} {l : List α} (h : a ≠ b) :
    RunLength (replicate n a ++ b::l) = (⟨n, hn⟩, a) :: (b::l).RunLength := by
  apply runLength_append hn
  rwa [head?_cons, Option.mem_some_iff, eq_comm]

theorem flatten_map_runLength (l : List α) :
    (l.RunLength.map fun x ↦ replicate x.1 x.2).flatten = l := by
  rw [RunLength, map_pmap, pmap_eq_self, flatten_splitBy]
  intro m hm
  have := chain'_of_mem_splitBy hm
  simp_rw [beq_iff_eq, chain'_eq_iff_eq_replicate] at this
  exact (this _ (head_mem_head? _)).symm

theorem runLength_injective : Function.Injective (List.RunLength (α := α)) := by
  intro l m h
  have := flatten_map_runLength m
  rwa [← h, flatten_map_runLength] at this

@[simp]
theorem runLength_inj {l m : List α} : l.RunLength = m.RunLength ↔ l = m :=
  runLength_injective.eq_iff

theorem runLength_flatten_map {l : List (ℕ+ × α)} (hl : l.Chain' fun x y ↦ x.2 ≠ y.2) :
    (l.map fun x ↦ replicate x.1 x.2).flatten.RunLength = l := by
  induction l with
  | nil => rfl
  | cons x l IH =>
    rw [chain'_cons'] at hl
    rw [map_cons, flatten_cons, runLength_append, IH hl.2]
    · rfl
    · cases l with
      | nil => simp
      | cons y l => simpa [head?_replicate] using (hl.1 y head?_cons).symm

private theorem chain'_runLengthAux {α : Type*} {l : List (List α)} (hn : ∀ m ∈ l, m ≠ [])
    (h : ∀ m (hm : m ∈ l), m.head (hn m hm) = m.getLast (hn m hm))
    (hl : l.Chain' fun a b ↦ ∃ ha hb, a.getLast ha ≠ b.head hb) :
    (l.pmap List.head hn).Chain' Ne := by
  induction l with
  | nil => exact chain'_nil
  | cons a l IH =>
    cases l with
    | nil => simp
    | cons b l =>
      rw [chain'_cons] at hl
      rw [pmap, pmap, chain'_cons]
      refine ⟨?_, IH (fun m hm ↦ hn _ (mem_cons_of_mem _ hm))
        (fun m hm ↦ h _ (mem_cons_of_mem _ hm)) hl.2⟩
      rw [h _ (mem_cons_self _ _)]
      obtain ⟨_, _, H⟩ := hl.1
      exact H

theorem chain'_runLength (l : List α) : l.RunLength.Chain' fun x y ↦ x.2 ≠ y.2 := by
  rw [RunLength]
  apply (List.chain'_map (β := ℕ+ × α) Prod.snd).1
  rw [map_pmap]
  apply chain'_runLengthAux
  · intro m hm
    have := chain'_of_mem_splitBy hm
    simp_rw [beq_iff_eq, chain'_eq_iff_eq_replicate] at this
    generalize_proofs hm
    obtain ⟨n, a, hm'⟩ : ∃ n a, m = replicate n a := ⟨_, _, this _ (head_mem_head? hm)⟩
    simp [hm']
  · simpa using chain'_getLast_head_splitBy (· == ·) l

private def runLengthRecOnAux (l : List (ℕ+ × α)) {p : List α → Sort*}
    (hc : l.Chain' fun x y ↦ x.2 ≠ y.2) (hn : p [])
    (hi : ∀ (n : ℕ+) {a l}, a ∉ l.head? → p l → p (replicate n a ++ l)) :
    p (l.map fun x ↦ replicate x.1 x.2).flatten :=
  match l with
  | [] => hn
  | (n, a)::l => by
    rw [chain'_cons'] at hc
    apply hi _ _ (runLengthRecOnAux l hc.2 hn hi)
    cases l with
    | nil => simp
    | cons x l => simpa [head?_replicate] using (hc.1 x head?_cons).symm

/-- Recursion on the run-length encoding of a list. -/
def runLengthRecOn (l : List α) {p : List α → Sort*} (hn : p [])
    (hi : ∀ (n : ℕ+) {a l}, a ∉ l.head? → p l → p (replicate n a ++ l)) : p l :=
  cast (congr_arg p (flatten_map_runLength l))
    (runLengthRecOnAux l.RunLength (chain'_runLength _) hn hi)

@[simp]
theorem runLengthRecOn_nil {p : List α → Sort*} (hn : p [])
    (hi : ∀ (n : ℕ+) {a l}, a ∉ l.head? → p l → p (replicate n a ++ l)) :
    runLengthRecOn [] hn hi = hn :=
  rfl

theorem runLengthRecOn_append {p : List α → Sort*} {n : ℕ} (h : 0 < n) {a : α} {l : List α}
    (hl : a ∉ l.head?) (hn : p [])
    (hi : ∀ (n : ℕ+) {a l}, a ∉ l.head? → p l → p (replicate n a ++ l)) :
    runLengthRecOn (replicate n a ++ l) hn hi = hi ⟨n, h⟩ hl (runLengthRecOn l hn hi) := by
  rw [runLengthRecOn, runLengthRecOn, cast_eq_iff_heq]
  have := runLength_append h hl
  have H : HEq (List.runLengthRecOnAux (replicate n a ++ l).RunLength
      (chain'_runLength _) hn hi) (List.runLengthRecOnAux ((⟨n, h⟩, a)::l.RunLength)
      (this ▸ chain'_runLength _) hn hi) := by
    congr
    exact proof_irrel_heq _ _
  apply H.trans
  rw [runLengthRecOnAux]
  congr
  · exact flatten_map_runLength _
  · exact proof_irrel_heq _ _
  · exact (cast_heq _ _).symm

theorem splitBy_beq (l : List α) :
    l.splitBy (· == ·) = l.RunLength.map fun x ↦ replicate x.1 x.2 := by
  apply runLengthRecOn l
  · rfl
  · intro n a l ha IH
    rw [splitBy_append, runLength_append _ ha, map_cons, IH]
    · rfl
    · simp
    · simp_rw [beq_iff_eq]
      exact chain'_replicate_of_rel _ rfl
    · intro h
      rw [getLast_replicate, beq_eq_false_iff_ne]
      rintro rfl
      exact ha (head_mem_head? _)

end List
