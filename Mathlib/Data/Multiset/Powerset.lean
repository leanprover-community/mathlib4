/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Zip
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Range

/-!
# The powerset of a multiset
-/

namespace Multiset

open List

variable {α : Type*}

/-! ### powerset -/

-- TODO: Write a more efficient version (this is slightly slower due to the `map (↑)`).
/-- A helper function for the powerset of a multiset. Given a list `l`, returns a list
of sublists of `l` as multisets. -/
def powersetAux (l : List α) : List (Multiset α) :=
  (sublists l).map (↑)

theorem powersetAux_eq_map_coe {l : List α} : powersetAux l = (sublists l).map (↑) :=
  rfl

@[simp]
theorem mem_powersetAux {l : List α} {s} : s ∈ powersetAux l ↔ s ≤ ↑l :=
  Quotient.inductionOn s <| by simp [powersetAux_eq_map_coe, Subperm, and_comm]

/-- Helper function for the powerset of a multiset. Given a list `l`, returns a list
of sublists of `l` (using `sublists'`), as multisets. -/
def powersetAux' (l : List α) : List (Multiset α) :=
  (sublists' l).map (↑)

theorem powersetAux_perm_powersetAux' {l : List α} : powersetAux l ~ powersetAux' l := by
  rw [powersetAux_eq_map_coe]; exact (sublists_perm_sublists' _).map _

@[simp]
theorem powersetAux'_nil : powersetAux' (@nil α) = [0] :=
  rfl

@[simp]
theorem powersetAux'_cons (a : α) (l : List α) :
    powersetAux' (a :: l) = powersetAux' l ++ List.map (cons a) (powersetAux' l) := by
  simp [powersetAux']

theorem powerset_aux'_perm {l₁ l₂ : List α} (p : l₁ ~ l₂) : powersetAux' l₁ ~ powersetAux' l₂ := by
  induction p with
  | nil => simp
  | cons _ _ IH =>
    simp only [powersetAux'_cons]
    exact IH.append (IH.map _)
  | swap a b =>
    simp only [powersetAux'_cons, map_append, List.map_map, append_assoc]
    apply Perm.append_left
    rw [← append_assoc, ← append_assoc,
      (by funext s; simp [cons_swap] : cons b ∘ cons a = cons a ∘ cons b)]
    exact perm_append_comm.append_right _
  | trans _ _ IH₁ IH₂ => exact IH₁.trans IH₂

theorem powersetAux_perm {l₁ l₂ : List α} (p : l₁ ~ l₂) : powersetAux l₁ ~ powersetAux l₂ :=
  powersetAux_perm_powersetAux'.trans <|
    (powerset_aux'_perm p).trans powersetAux_perm_powersetAux'.symm

/-- The power set of a multiset. -/
def powerset (s : Multiset α) : Multiset (Multiset α) :=
  Quot.liftOn s
    (fun l => (powersetAux l : Multiset (Multiset α)))
    (fun _ _ h => Quot.sound (powersetAux_perm h))

theorem powerset_coe (l : List α) : @powerset α l = ((sublists l).map (↑) : List (Multiset α)) :=
  congr_arg ((↑) : List (Multiset α) → Multiset (Multiset α)) powersetAux_eq_map_coe

@[simp]
theorem powerset_coe' (l : List α) : @powerset α l = ((sublists' l).map (↑) : List (Multiset α)) :=
  Quot.sound powersetAux_perm_powersetAux'

@[simp]
theorem powerset_zero : @powerset α 0 = {0} :=
  rfl

@[simp]
theorem powerset_cons (a : α) (s) : powerset (a ::ₘ s) = powerset s + map (cons a) (powerset s) :=
  Quotient.inductionOn s fun l => by simp [Function.comp_def]

@[simp]
theorem mem_powerset {s t : Multiset α} : s ∈ powerset t ↔ s ≤ t :=
  Quotient.inductionOn₂ s t <| by simp [Subperm, and_comm]

theorem map_single_le_powerset (s : Multiset α) : s.map singleton ≤ powerset s :=
  Quotient.inductionOn s fun l => by
    simp only [powerset_coe, quot_mk_to_coe, coe_le, map_coe]
    change l.map (((↑) : List α → Multiset α) ∘ pure) <+~ (sublists l).map (↑)
    rw [← List.map_map]
    exact ((map_pure_sublist_sublists _).map _).subperm

@[simp]
theorem card_powerset (s : Multiset α) : card (powerset s) = 2 ^ card s :=
  Quotient.inductionOn s <| by simp

theorem revzip_powersetAux {l : List α} ⦃x⦄ (h : x ∈ revzip (powersetAux l)) : x.1 + x.2 = ↑l := by
  rw [revzip, powersetAux_eq_map_coe, ← map_reverse, zip_map, ← revzip, List.mem_map] at h
  simp only [Prod.map_apply, Prod.exists] at h
  rcases h with ⟨l₁, l₂, h, rfl, rfl⟩
  exact Quot.sound (revzip_sublists _ _ _ h)

theorem revzip_powersetAux' {l : List α} ⦃x⦄ (h : x ∈ revzip (powersetAux' l)) :
    x.1 + x.2 = ↑l := by
  rw [revzip, powersetAux', ← map_reverse, zip_map, ← revzip, List.mem_map] at h
  simp only [Prod.map_apply, Prod.exists] at h
  rcases h with ⟨l₁, l₂, h, rfl, rfl⟩
  exact Quot.sound (revzip_sublists' _ _ _ h)

theorem revzip_powersetAux_lemma {α : Type*} [DecidableEq α] (l : List α) {l' : List (Multiset α)}
    (H : ∀ ⦃x : _ × _⦄, x ∈ revzip l' → x.1 + x.2 = ↑l) :
    revzip l' = l'.map fun x => (x, (l : Multiset α) - x) := by
  have :
    Forall₂ (fun (p : Multiset α × Multiset α) (s : Multiset α) => p = (s, ↑l - s)) (revzip l')
      ((revzip l').map Prod.fst) := by
    rw [forall₂_map_right_iff, forall₂_same]
    rintro ⟨s, t⟩ h
    dsimp
    rw [← H h, add_tsub_cancel_left]
  rw [← forall₂_eq_eq_eq, forall₂_map_right_iff]
  simpa using this

theorem revzip_powersetAux_perm_aux' {l : List α} :
    revzip (powersetAux l) ~ revzip (powersetAux' l) := by
  haveI := Classical.decEq α
  rw [revzip_powersetAux_lemma l revzip_powersetAux, revzip_powersetAux_lemma l revzip_powersetAux']
  exact powersetAux_perm_powersetAux'.map _

theorem revzip_powersetAux_perm {l₁ l₂ : List α} (p : l₁ ~ l₂) :
    revzip (powersetAux l₁) ~ revzip (powersetAux l₂) := by
  haveI := Classical.decEq α
  simp only [fun l : List α => revzip_powersetAux_lemma l revzip_powersetAux, coe_eq_coe.2 p]
  exact (powersetAux_perm p).map _

/-! ### powersetCard -/


/-- Helper function for `powersetCard`. Given a list `l`, `powersetCardAux n l` is the list
of sublists of length `n`, as multisets. -/
def powersetCardAux (n : ℕ) (l : List α) : List (Multiset α) :=
  sublistsLenAux n l (↑) []

theorem powersetCardAux_eq_map_coe {n} {l : List α} :
    powersetCardAux n l = (sublistsLen n l).map (↑) := by
  rw [powersetCardAux, sublistsLenAux_eq, append_nil]

@[simp]
theorem mem_powersetCardAux {n} {l : List α} {s} : s ∈ powersetCardAux n l ↔ s ≤ ↑l ∧ card s = n :=
  Quotient.inductionOn s <| by
    simp only [quot_mk_to_coe, powersetCardAux_eq_map_coe, List.mem_map, mem_sublistsLen,
      coe_eq_coe, coe_le, Subperm, coe_card]
    exact fun l₁ =>
      ⟨fun ⟨l₂, ⟨s, e⟩, p⟩ => ⟨⟨_, p, s⟩, p.symm.length_eq.trans e⟩,
       fun ⟨⟨l₂, p, s⟩, e⟩ => ⟨_, ⟨s, p.length_eq.trans e⟩, p⟩⟩

@[simp]
theorem powersetCardAux_zero (l : List α) : powersetCardAux 0 l = [0] := by
  simp [powersetCardAux_eq_map_coe]

@[simp]
theorem powersetCardAux_nil (n : ℕ) : powersetCardAux (n + 1) (@nil α) = [] :=
  rfl

@[simp]
theorem powersetCardAux_cons (n : ℕ) (a : α) (l : List α) :
    powersetCardAux (n + 1) (a :: l) =
      powersetCardAux (n + 1) l ++ List.map (cons a) (powersetCardAux n l) := by
  simp [powersetCardAux_eq_map_coe]

theorem powersetCardAux_perm {n} {l₁ l₂ : List α} (p : l₁ ~ l₂) :
    powersetCardAux n l₁ ~ powersetCardAux n l₂ := by
  induction n generalizing l₁ l₂ with | zero => simp | succ n IHn => ?_
  induction p with
  | nil => rfl
  | cons _ p IH =>
    simp only [powersetCardAux_cons]
    exact IH.append ((IHn p).map _)
  | swap a b =>
    simp only [powersetCardAux_cons, append_assoc]
    apply Perm.append_left
    cases n
    · simp [Perm.swap]
    simp only [powersetCardAux_cons, map_append, List.map_map]
    rw [← append_assoc, ← append_assoc,
      (by funext s; simp [cons_swap] : cons b ∘ cons a = cons a ∘ cons b)]
    exact perm_append_comm.append_right _
  | trans _ _ IH₁ IH₂ => exact IH₁.trans IH₂

/-- `powersetCard n s` is the multiset of all submultisets of `s` of length `n`. -/
def powersetCard (n : ℕ) (s : Multiset α) : Multiset (Multiset α) :=
  Quot.liftOn s (fun l => (powersetCardAux n l : Multiset (Multiset α))) fun _ _ h =>
    Quot.sound (powersetCardAux_perm h)

theorem powersetCard_coe' (n) (l : List α) : @powersetCard α n l = powersetCardAux n l :=
  rfl

theorem powersetCard_coe (n) (l : List α) :
    @powersetCard α n l = ((sublistsLen n l).map (↑) : List (Multiset α)) :=
  congr_arg ((↑) : List (Multiset α) → Multiset (Multiset α)) powersetCardAux_eq_map_coe

@[simp]
theorem powersetCard_zero_left (s : Multiset α) : powersetCard 0 s = {0} :=
  Quotient.inductionOn s fun l => by simp [powersetCard_coe']

theorem powersetCard_zero_right (n : ℕ) : @powersetCard α (n + 1) 0 = 0 :=
  rfl

@[simp]
theorem powersetCard_cons (n : ℕ) (a : α) (s) :
    powersetCard (n + 1) (a ::ₘ s) = powersetCard (n + 1) s + map (cons a) (powersetCard n s) :=
  Quotient.inductionOn s fun l => by simp [powersetCard_coe']

theorem powersetCard_one (s : Multiset α) : powersetCard 1 s = s.map singleton :=
  Quotient.inductionOn s fun l ↦ by
    simp [powersetCard_coe, sublistsLen_one, map_reverse, Function.comp_def]

@[simp]
theorem mem_powersetCard {n : ℕ} {s t : Multiset α} : s ∈ powersetCard n t ↔ s ≤ t ∧ card s = n :=
  Quotient.inductionOn t fun l => by simp [powersetCard_coe']

@[simp]
theorem card_powersetCard (n : ℕ) (s : Multiset α) :
    card (powersetCard n s) = Nat.choose (card s) n :=
  Quotient.inductionOn s <| by simp [powersetCard_coe]

theorem powersetCard_le_powerset (n : ℕ) (s : Multiset α) : powersetCard n s ≤ powerset s :=
  Quotient.inductionOn s fun l => by
    simp only [quot_mk_to_coe, powersetCard_coe, powerset_coe', coe_le]
    exact ((sublistsLen_sublist_sublists' _ _).map _).subperm

theorem powersetCard_mono (n : ℕ) {s t : Multiset α} (h : s ≤ t) :
    powersetCard n s ≤ powersetCard n t :=
  leInductionOn h fun {l₁ l₂} h => by
    simp only [powersetCard_coe, coe_le]
    exact ((sublistsLen_sublist_of_sublist _ h).map _).subperm

@[simp]
theorem powersetCard_eq_empty {α : Type*} (n : ℕ) {s : Multiset α} (h : card s < n) :
    powersetCard n s = 0 :=
  card_eq_zero.mp (Nat.choose_eq_zero_of_lt h ▸ card_powersetCard _ _)

theorem powersetCard_card_add (s : Multiset α) {i : ℕ} (hi : 0 < i) :
    s.powersetCard (card s + i) = 0 := by
  simp [hi]

theorem powersetCard_map {β : Type*} (f : α → β) (n : ℕ) (s : Multiset α) :
    powersetCard n (s.map f) = (powersetCard n s).map (map f) := by
  induction s using Multiset.induction generalizing n with
  | empty => cases n <;> simp [powersetCard_zero_left]
  | cons t s ih => cases n <;> simp [ih]

theorem pairwise_disjoint_powersetCard (s : Multiset α) :
    _root_.Pairwise fun i j => Disjoint (s.powersetCard i) (s.powersetCard j) :=
  fun _ _ h ↦ disjoint_left.mpr fun hi hj ↦
    h ((Multiset.mem_powersetCard.mp hi).2.symm.trans (Multiset.mem_powersetCard.mp hj).2)

theorem bind_powerset_len {α : Type*} (S : Multiset α) :
    (bind (Multiset.range (card S + 1)) fun k => S.powersetCard k) = S.powerset := by
  induction S using Quotient.inductionOn
  simp_rw [quot_mk_to_coe, powerset_coe', powersetCard_coe, ← coe_range, coe_bind,
    ← List.map_flatMap, coe_card]
  exact coe_eq_coe.mpr ((List.range_bind_sublistsLen_perm _).map _)

@[simp]
theorem nodup_powerset {s : Multiset α} : Nodup (powerset s) ↔ Nodup s :=
  ⟨fun h => (nodup_of_le (map_single_le_powerset _) h).of_map _,
    Quotient.inductionOn s fun l h => by
      simp only [quot_mk_to_coe, powerset_coe', coe_nodup]
      refine (nodup_sublists'.2 h).map_on ?_
      exact fun x sx y sy e =>
        (h.perm_iff_eq_of_sublist (mem_sublists'.1 sx) (mem_sublists'.1 sy)).1 (Quotient.exact e)⟩

alias ⟨Nodup.ofPowerset, Nodup.powerset⟩ := nodup_powerset

protected theorem Nodup.powersetCard {n : ℕ} {s : Multiset α} (h : Nodup s) :
    Nodup (powersetCard n s) :=
  nodup_of_le (powersetCard_le_powerset _ _) (nodup_powerset.2 h)

end Multiset
