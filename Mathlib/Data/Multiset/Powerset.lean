/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.multiset.powerset
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Sublists
import Mathbin.Data.Multiset.Nodup

/-!
# The powerset of a multiset
-/


namespace Multiset

open List

variable {α : Type _}

/-! ### powerset -/


/-- A helper function for the powerset of a multiset. Given a list `l`, returns a list
of sublists of `l` (using `sublists_aux`), as multisets. -/
def powersetAux (l : List α) : List (Multiset α) :=
  0 :: sublistsAux l fun x y => x :: y
#align multiset.powerset_aux Multiset.powersetAux

theorem powerset_aux_eq_map_coe {l : List α} : powersetAux l = (sublists l).map coe := by
  simp [powerset_aux, sublists] <;>
      rw [←
        show (@sublists_aux₁ α (Multiset α) l fun x => [↑x]) = sublists_aux l fun x => List.cons ↑x
          from sublists_aux₁_eq_sublists_aux _ _,
        sublists_aux_cons_eq_sublists_aux₁, ← bind_ret_eq_map, sublists_aux₁_bind] <;>
    rfl
#align multiset.powerset_aux_eq_map_coe Multiset.powerset_aux_eq_map_coe

@[simp]
theorem mem_powerset_aux {l : List α} {s} : s ∈ powersetAux l ↔ s ≤ ↑l :=
  Quotient.induction_on s <| by simp [powerset_aux_eq_map_coe, subperm, and_comm]
#align multiset.mem_powerset_aux Multiset.mem_powerset_aux

/-- Helper function for the powerset of a multiset. Given a list `l`, returns a list
of sublists of `l` (using `sublists'`), as multisets. -/
def powersetAux' (l : List α) : List (Multiset α) :=
  (sublists' l).map coe
#align multiset.powerset_aux' Multiset.powersetAux'

theorem powerset_aux_perm_powerset_aux' {l : List α} : powersetAux l ~ powersetAux' l := by
  rw [powerset_aux_eq_map_coe] <;> exact (sublists_perm_sublists' _).map _
#align multiset.powerset_aux_perm_powerset_aux' Multiset.powerset_aux_perm_powerset_aux'

@[simp]
theorem powerset_aux'_nil : powersetAux' (@nil α) = [0] :=
  rfl
#align multiset.powerset_aux'_nil Multiset.powerset_aux'_nil

@[simp]
theorem powerset_aux'_cons (a : α) (l : List α) :
    powersetAux' (a :: l) = powersetAux' l ++ List.map (cons a) (powersetAux' l) := by
  simp [powerset_aux'] <;> rfl
#align multiset.powerset_aux'_cons Multiset.powerset_aux'_cons

theorem powerset_aux'_perm {l₁ l₂ : List α} (p : l₁ ~ l₂) : powersetAux' l₁ ~ powersetAux' l₂ :=
  by
  induction' p with a l₁ l₂ p IH a b l l₁ l₂ l₃ p₁ p₂ IH₁ IH₂; · simp
  · simp
    exact IH.append (IH.map _)
  · simp
    apply perm.append_left
    rw [← append_assoc, ← append_assoc,
      (by funext s <;> simp [cons_swap] : cons b ∘ cons a = cons a ∘ cons b)]
    exact perm_append_comm.append_right _
  · exact IH₁.trans IH₂
#align multiset.powerset_aux'_perm Multiset.powerset_aux'_perm

theorem powerset_aux_perm {l₁ l₂ : List α} (p : l₁ ~ l₂) : powersetAux l₁ ~ powersetAux l₂ :=
  powerset_aux_perm_powerset_aux'.trans <|
    (powerset_aux'_perm p).trans powerset_aux_perm_powerset_aux'.symm
#align multiset.powerset_aux_perm Multiset.powerset_aux_perm

/-- The power set of a multiset. -/
def powerset (s : Multiset α) : Multiset (Multiset α) :=
  Quot.liftOn s (fun l => (powersetAux l : Multiset (Multiset α))) fun l₁ l₂ h =>
    Quot.sound (powerset_aux_perm h)
#align multiset.powerset Multiset.powerset

theorem powerset_coe (l : List α) : @powerset α l = ((sublists l).map coe : List (Multiset α)) :=
  congr_arg coe powerset_aux_eq_map_coe
#align multiset.powerset_coe Multiset.powerset_coe

@[simp]
theorem powerset_coe' (l : List α) : @powerset α l = ((sublists' l).map coe : List (Multiset α)) :=
  Quot.sound powerset_aux_perm_powerset_aux'
#align multiset.powerset_coe' Multiset.powerset_coe'

@[simp]
theorem powerset_zero : @powerset α 0 = {0} :=
  rfl
#align multiset.powerset_zero Multiset.powerset_zero

@[simp]
theorem powerset_cons (a : α) (s) : powerset (a ::ₘ s) = powerset s + map (cons a) (powerset s) :=
  (Quotient.induction_on s) fun l => by simp <;> rfl
#align multiset.powerset_cons Multiset.powerset_cons

@[simp]
theorem mem_powerset {s t : Multiset α} : s ∈ powerset t ↔ s ≤ t :=
  Quotient.induction_on₂ s t <| by simp [subperm, and_comm]
#align multiset.mem_powerset Multiset.mem_powerset

theorem map_single_le_powerset (s : Multiset α) : s.map singleton ≤ powerset s :=
  (Quotient.induction_on s) fun l =>
    by
    simp only [powerset_coe, quot_mk_to_coe, coe_le, coe_map]
    show l.map (coe ∘ List.ret) <+~ (sublists l).map coe
    rw [← List.map_map]
    exact ((map_ret_sublist_sublists _).map _).Subperm
#align multiset.map_single_le_powerset Multiset.map_single_le_powerset

@[simp]
theorem card_powerset (s : Multiset α) : card (powerset s) = 2 ^ card s :=
  Quotient.induction_on s <| by simp
#align multiset.card_powerset Multiset.card_powerset

theorem revzip_powerset_aux {l : List α} ⦃x⦄ (h : x ∈ revzip (powersetAux l)) : x.1 + x.2 = ↑l :=
  by
  rw [revzip, powerset_aux_eq_map_coe, ← map_reverse, zip_map, ← revzip] at h
  simp at h; rcases h with ⟨l₁, l₂, h, rfl, rfl⟩
  exact Quot.sound (revzip_sublists _ _ _ h)
#align multiset.revzip_powerset_aux Multiset.revzip_powerset_aux

theorem revzip_powerset_aux' {l : List α} ⦃x⦄ (h : x ∈ revzip (powersetAux' l)) : x.1 + x.2 = ↑l :=
  by
  rw [revzip, powerset_aux', ← map_reverse, zip_map, ← revzip] at h
  simp at h; rcases h with ⟨l₁, l₂, h, rfl, rfl⟩
  exact Quot.sound (revzip_sublists' _ _ _ h)
#align multiset.revzip_powerset_aux' Multiset.revzip_powerset_aux'

theorem revzip_powerset_aux_lemma [DecidableEq α] (l : List α) {l' : List (Multiset α)}
    (H : ∀ ⦃x : _ × _⦄, x ∈ revzip l' → x.1 + x.2 = ↑l) : revzip l' = l'.map fun x => (x, ↑l - x) :=
  by
  have :
    forall₂ (fun (p : Multiset α × Multiset α) (s : Multiset α) => p = (s, ↑l - s)) (revzip l')
      ((revzip l').map Prod.fst) :=
    by
    rw [forall₂_map_right_iff, forall₂_same]
    rintro ⟨s, t⟩ h
    dsimp
    rw [← H h, add_tsub_cancel_left]
  rw [← forall₂_eq_eq_eq, forall₂_map_right_iff]
  simpa
#align multiset.revzip_powerset_aux_lemma Multiset.revzip_powerset_aux_lemma

theorem revzip_powerset_aux_perm_aux' {l : List α} :
    revzip (powersetAux l) ~ revzip (powersetAux' l) :=
  by
  haveI := Classical.decEq α
  rw [revzip_powerset_aux_lemma l revzip_powerset_aux,
    revzip_powerset_aux_lemma l revzip_powerset_aux']
  exact powerset_aux_perm_powerset_aux'.map _
#align multiset.revzip_powerset_aux_perm_aux' Multiset.revzip_powerset_aux_perm_aux'

theorem revzip_powerset_aux_perm {l₁ l₂ : List α} (p : l₁ ~ l₂) :
    revzip (powersetAux l₁) ~ revzip (powersetAux l₂) :=
  by
  haveI := Classical.decEq α
  simp [fun l : List α => revzip_powerset_aux_lemma l revzip_powerset_aux, coe_eq_coe.2 p]
  exact (powerset_aux_perm p).map _
#align multiset.revzip_powerset_aux_perm Multiset.revzip_powerset_aux_perm

/-! ### powerset_len -/


/-- Helper function for `powerset_len`. Given a list `l`, `powerset_len_aux n l` is the list
of sublists of length `n`, as multisets. -/
def powersetLenAux (n : ℕ) (l : List α) : List (Multiset α) :=
  sublistsLenAux n l coe []
#align multiset.powerset_len_aux Multiset.powersetLenAux

theorem powerset_len_aux_eq_map_coe {n} {l : List α} :
    powersetLenAux n l = (sublistsLen n l).map coe := by
  rw [powerset_len_aux, sublists_len_aux_eq, append_nil]
#align multiset.powerset_len_aux_eq_map_coe Multiset.powerset_len_aux_eq_map_coe

@[simp]
theorem mem_powerset_len_aux {n} {l : List α} {s} : s ∈ powersetLenAux n l ↔ s ≤ ↑l ∧ card s = n :=
  Quotient.induction_on s <| by
    simp [powerset_len_aux_eq_map_coe, subperm] <;>
      exact fun l₁ =>
        ⟨fun ⟨l₂, ⟨s, e⟩, p⟩ => ⟨⟨_, p, s⟩, p.symm.length_eq.trans e⟩, fun ⟨⟨l₂, p, s⟩, e⟩ =>
          ⟨_, ⟨s, p.length_eq.trans e⟩, p⟩⟩
#align multiset.mem_powerset_len_aux Multiset.mem_powerset_len_aux

@[simp]
theorem powerset_len_aux_zero (l : List α) : powersetLenAux 0 l = [0] := by
  simp [powerset_len_aux_eq_map_coe]
#align multiset.powerset_len_aux_zero Multiset.powerset_len_aux_zero

@[simp]
theorem powerset_len_aux_nil (n : ℕ) : powersetLenAux (n + 1) (@nil α) = [] :=
  rfl
#align multiset.powerset_len_aux_nil Multiset.powerset_len_aux_nil

@[simp]
theorem powerset_len_aux_cons (n : ℕ) (a : α) (l : List α) :
    powersetLenAux (n + 1) (a :: l) =
      powersetLenAux (n + 1) l ++ List.map (cons a) (powersetLenAux n l) :=
  by simp [powerset_len_aux_eq_map_coe] <;> rfl
#align multiset.powerset_len_aux_cons Multiset.powerset_len_aux_cons

theorem powerset_len_aux_perm {n} {l₁ l₂ : List α} (p : l₁ ~ l₂) :
    powersetLenAux n l₁ ~ powersetLenAux n l₂ :=
  by
  induction' n with n IHn generalizing l₁ l₂; · simp
  induction' p with a l₁ l₂ p IH a b l l₁ l₂ l₃ p₁ p₂ IH₁ IH₂; · rfl
  · simp
    exact IH.append ((IHn p).map _)
  · simp
    apply perm.append_left
    cases n
    · simp
      apply perm.swap
    simp
    rw [← append_assoc, ← append_assoc,
      (by funext s <;> simp [cons_swap] : cons b ∘ cons a = cons a ∘ cons b)]
    exact perm_append_comm.append_right _
  · exact IH₁.trans IH₂
#align multiset.powerset_len_aux_perm Multiset.powerset_len_aux_perm

/-- `powerset_len n s` is the multiset of all submultisets of `s` of length `n`. -/
def powersetLen (n : ℕ) (s : Multiset α) : Multiset (Multiset α) :=
  Quot.liftOn s (fun l => (powersetLenAux n l : Multiset (Multiset α))) fun l₁ l₂ h =>
    Quot.sound (powerset_len_aux_perm h)
#align multiset.powerset_len Multiset.powersetLen

theorem powerset_len_coe' (n) (l : List α) : @powersetLen α n l = powersetLenAux n l :=
  rfl
#align multiset.powerset_len_coe' Multiset.powerset_len_coe'

theorem powerset_len_coe (n) (l : List α) :
    @powersetLen α n l = ((sublistsLen n l).map coe : List (Multiset α)) :=
  congr_arg coe powerset_len_aux_eq_map_coe
#align multiset.powerset_len_coe Multiset.powerset_len_coe

@[simp]
theorem powerset_len_zero_left (s : Multiset α) : powersetLen 0 s = {0} :=
  (Quotient.induction_on s) fun l => by simp [powerset_len_coe'] <;> rfl
#align multiset.powerset_len_zero_left Multiset.powerset_len_zero_left

theorem powerset_len_zero_right (n : ℕ) : @powersetLen α (n + 1) 0 = 0 :=
  rfl
#align multiset.powerset_len_zero_right Multiset.powerset_len_zero_right

@[simp]
theorem powerset_len_cons (n : ℕ) (a : α) (s) :
    powersetLen (n + 1) (a ::ₘ s) = powersetLen (n + 1) s + map (cons a) (powersetLen n s) :=
  (Quotient.induction_on s) fun l => by simp [powerset_len_coe'] <;> rfl
#align multiset.powerset_len_cons Multiset.powerset_len_cons

@[simp]
theorem mem_powerset_len {n : ℕ} {s t : Multiset α} : s ∈ powersetLen n t ↔ s ≤ t ∧ card s = n :=
  (Quotient.induction_on t) fun l => by simp [powerset_len_coe']
#align multiset.mem_powerset_len Multiset.mem_powerset_len

@[simp]
theorem card_powerset_len (n : ℕ) (s : Multiset α) :
    card (powersetLen n s) = Nat.choose (card s) n :=
  Quotient.induction_on s <| by simp [powerset_len_coe]
#align multiset.card_powerset_len Multiset.card_powerset_len

theorem powerset_len_le_powerset (n : ℕ) (s : Multiset α) : powersetLen n s ≤ powerset s :=
  (Quotient.induction_on s) fun l => by
    simp [powerset_len_coe] <;> exact ((sublists_len_sublist_sublists' _ _).map _).Subperm
#align multiset.powerset_len_le_powerset Multiset.powerset_len_le_powerset

theorem powerset_len_mono (n : ℕ) {s t : Multiset α} (h : s ≤ t) :
    powersetLen n s ≤ powersetLen n t :=
  (le_induction_on h) fun l₁ l₂ h => by
    simp [powerset_len_coe] <;> exact ((sublists_len_sublist_of_sublist _ h).map _).Subperm
#align multiset.powerset_len_mono Multiset.powerset_len_mono

@[simp]
theorem powerset_len_empty {α : Type _} (n : ℕ) {s : Multiset α} (h : s.card < n) :
    powersetLen n s = 0 :=
  card_eq_zero.mp (Nat.choose_eq_zero_of_lt h ▸ card_powerset_len _ _)
#align multiset.powerset_len_empty Multiset.powerset_len_empty

@[simp]
theorem powerset_len_card_add (s : Multiset α) {i : ℕ} (hi : 0 < i) :
    s.powersetLen (s.card + i) = 0 :=
  powerset_len_empty _ (lt_add_of_pos_right (card s) hi)
#align multiset.powerset_len_card_add Multiset.powerset_len_card_add

theorem powerset_len_map {β : Type _} (f : α → β) (n : ℕ) (s : Multiset α) :
    powersetLen n (s.map f) = (powersetLen n s).map (map f) :=
  by
  induction' s using Multiset.induction with t s ih generalizing n
  · cases n <;> simp [powerset_len_zero_left, powerset_len_zero_right]
  · cases n <;> simp [ih, map_comp_cons]
#align multiset.powerset_len_map Multiset.powerset_len_map

theorem pairwise_disjoint_powerset_len (s : Multiset α) :
    Pairwise fun i j => Multiset.Disjoint (s.powersetLen i) (s.powersetLen j) :=
  fun i j h x hi hj =>
  h (Eq.trans (Multiset.mem_powerset_len.mp hi).right.symm (Multiset.mem_powerset_len.mp hj).right)
#align multiset.pairwise_disjoint_powerset_len Multiset.pairwise_disjoint_powerset_len

theorem bind_powerset_len {α : Type _} (S : Multiset α) :
    (bind (Multiset.range (S.card + 1)) fun k => S.powersetLen k) = S.powerset :=
  by
  induction S using Quotient.induction_on
  simp_rw [quot_mk_to_coe, powerset_coe', powerset_len_coe, ← coe_range, coe_bind, ← List.bind_map,
    coe_card]
  exact coe_eq_coe.mpr ((List.range_bind_sublists_len_perm S).map _)
#align multiset.bind_powerset_len Multiset.bind_powerset_len

@[simp]
theorem nodup_powerset {s : Multiset α} : Nodup (powerset s) ↔ Nodup s :=
  ⟨fun h => (nodup_of_le (map_single_le_powerset _) h).of_map _,
    (Quotient.induction_on s) fun l h => by
      simp <;> refine' (nodup_sublists'.2 h).map_on _ <;>
        exact fun x sx y sy e =>
          (h.sublist_ext (mem_sublists'.1 sx) (mem_sublists'.1 sy)).1 (Quotient.exact e)⟩
#align multiset.nodup_powerset Multiset.nodup_powerset

alias nodup_powerset ↔ nodup.of_powerset nodup.powerset
#align multiset.nodup.of_powerset Multiset.Nodup.of_powerset
#align multiset.nodup.powerset Multiset.Nodup.powerset

protected theorem Nodup.powerset_len {n : ℕ} {s : Multiset α} (h : Nodup s) :
    Nodup (powersetLen n s) :=
  nodup_of_le (powerset_len_le_powerset _ _) (nodup_powerset.2 h)
#align multiset.nodup.powerset_len Multiset.Nodup.powerset_len

end Multiset

