/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Sublists
import Mathlib.Data.Multiset.Nodup

#align_import data.multiset.powerset from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# The powerset of a multiset
-/

set_option autoImplicit true


namespace Multiset

open List

variable {α : Type*}

/-! ### powerset -/

--Porting note: TODO: Write a more efficient version
/-- A helper function for the powerset of a multiset. Given a list `l`, returns a list
of sublists of `l` as multisets. -/
def powersetAux (l : List α) : List (Multiset α) :=
  (sublists l).map (↑)
#align multiset.powerset_aux Multiset.powersetAux

theorem powersetAux_eq_map_coe {l : List α} : powersetAux l = (sublists l).map (↑) :=
  rfl
#align multiset.powerset_aux_eq_map_coe Multiset.powersetAux_eq_map_coe

@[simp]
theorem mem_powersetAux {l : List α} {s} : s ∈ powersetAux l ↔ s ≤ ↑l :=
  Quotient.inductionOn s <| by simp [powersetAux_eq_map_coe, Subperm, and_comm]
                               -- 🎉 no goals
#align multiset.mem_powerset_aux Multiset.mem_powersetAux

/-- Helper function for the powerset of a multiset. Given a list `l`, returns a list
of sublists of `l` (using `sublists'`), as multisets. -/
def powersetAux' (l : List α) : List (Multiset α) :=
  (sublists' l).map (↑)
#align multiset.powerset_aux' Multiset.powersetAux'

theorem powersetAux_perm_powersetAux' {l : List α} : powersetAux l ~ powersetAux' l := by
  rw [powersetAux_eq_map_coe]; exact (sublists_perm_sublists' _).map _
  -- ⊢ List.map ofList (sublists l) ~ powersetAux' l
                               -- 🎉 no goals
#align multiset.powerset_aux_perm_powerset_aux' Multiset.powersetAux_perm_powersetAux'

@[simp]
theorem powersetAux'_nil : powersetAux' (@nil α) = [0] :=
  rfl
#align multiset.powerset_aux'_nil Multiset.powersetAux'_nil

@[simp]
theorem powersetAux'_cons (a : α) (l : List α) :
    powersetAux' (a :: l) = powersetAux' l ++ List.map (cons a) (powersetAux' l) := by
  simp [powersetAux']; rfl
  -- ⊢ List.map (ofList ∘ List.cons a) (sublists' l) = List.map (cons a ∘ ofList) ( …
                       -- 🎉 no goals
#align multiset.powerset_aux'_cons Multiset.powersetAux'_cons

theorem powerset_aux'_perm {l₁ l₂ : List α} (p : l₁ ~ l₂) : powersetAux' l₁ ~ powersetAux' l₂ := by
  induction' p with a l₁ l₂ p IH a b l l₁ l₂ l₃ _ _ IH₁ IH₂
  · simp
    -- 🎉 no goals
  · simp only [powersetAux'_cons]
    -- ⊢ powersetAux' l₁ ++ List.map (cons a) (powersetAux' l₁) ~ powersetAux' l₂ ++  …
    exact IH.append (IH.map _)
    -- 🎉 no goals
  · simp only [powersetAux'_cons, map_append, List.map_map, append_assoc]
    -- ⊢ powersetAux' l ++ (List.map (cons a) (powersetAux' l) ++ (List.map (cons b)  …
    apply Perm.append_left
    -- ⊢ List.map (cons a) (powersetAux' l) ++ (List.map (cons b) (powersetAux' l) ++ …
    rw [← append_assoc, ← append_assoc,
      (by funext s; simp [cons_swap] : cons b ∘ cons a = cons a ∘ cons b)]
    exact perm_append_comm.append_right _
    -- 🎉 no goals
  · exact IH₁.trans IH₂
    -- 🎉 no goals
#align multiset.powerset_aux'_perm Multiset.powerset_aux'_perm

theorem powersetAux_perm {l₁ l₂ : List α} (p : l₁ ~ l₂) : powersetAux l₁ ~ powersetAux l₂ :=
  powersetAux_perm_powersetAux'.trans <|
    (powerset_aux'_perm p).trans powersetAux_perm_powersetAux'.symm
#align multiset.powerset_aux_perm Multiset.powersetAux_perm

--Porting note: slightly slower implementation due to `map ofList`
/-- The power set of a multiset. -/
def powerset (s : Multiset α) : Multiset (Multiset α) :=
  Quot.liftOn s
    (fun l => (powersetAux l : Multiset (Multiset α)))
    (fun _ _ h => Quot.sound (powersetAux_perm h))
#align multiset.powerset Multiset.powerset

theorem powerset_coe (l : List α) : @powerset α l = ((sublists l).map (↑) : List (Multiset α)) :=
  congr_arg ((↑) : List (Multiset α) → Multiset (Multiset α)) powersetAux_eq_map_coe
#align multiset.powerset_coe Multiset.powerset_coe

@[simp]
theorem powerset_coe' (l : List α) : @powerset α l = ((sublists' l).map (↑) : List (Multiset α)) :=
  Quot.sound powersetAux_perm_powersetAux'
#align multiset.powerset_coe' Multiset.powerset_coe'

@[simp]
theorem powerset_zero : @powerset α 0 = {0} :=
  rfl
#align multiset.powerset_zero Multiset.powerset_zero

@[simp]
theorem powerset_cons (a : α) (s) : powerset (a ::ₘ s) = powerset s + map (cons a) (powerset s) :=
  Quotient.inductionOn s fun l => by simp; rfl
                                     -- ⊢ List.map ofList (sublists' l) ++ List.map (ofList ∘ List.cons a) (sublists'  …
                                           -- 🎉 no goals
#align multiset.powerset_cons Multiset.powerset_cons

@[simp]
theorem mem_powerset {s t : Multiset α} : s ∈ powerset t ↔ s ≤ t :=
  Quotient.inductionOn₂ s t <| by simp [Subperm, and_comm]
                                  -- 🎉 no goals
#align multiset.mem_powerset Multiset.mem_powerset

theorem map_single_le_powerset (s : Multiset α) : s.map singleton ≤ powerset s :=
  Quotient.inductionOn s fun l => by
    simp only [powerset_coe, quot_mk_to_coe, coe_le, coe_map]
    -- ⊢ List.map singleton l <+~ List.map ofList (sublists l)
    show l.map (((↑) : List α → Multiset α) ∘ List.ret) <+~ (sublists l).map (↑)
    -- ⊢ List.map (ofList ∘ List.ret) l <+~ List.map ofList (sublists l)
    rw [← List.map_map]
    -- ⊢ List.map ofList (List.map List.ret l) <+~ List.map ofList (sublists l)
    exact ((map_ret_sublist_sublists _).map _).subperm
    -- 🎉 no goals
#align multiset.map_single_le_powerset Multiset.map_single_le_powerset

@[simp]
theorem card_powerset (s : Multiset α) : card (powerset s) = 2 ^ card s :=
  Quotient.inductionOn s <| by simp
                               -- 🎉 no goals
#align multiset.card_powerset Multiset.card_powerset

theorem revzip_powersetAux {l : List α} ⦃x⦄ (h : x ∈ revzip (powersetAux l)) : x.1 + x.2 = ↑l := by
  rw [revzip, powersetAux_eq_map_coe, ← map_reverse, zip_map, ← revzip, List.mem_map] at h
  -- ⊢ x.fst + x.snd = ↑l
  simp only [Prod_map, Prod.exists] at h
  -- ⊢ x.fst + x.snd = ↑l
  rcases h with ⟨l₁, l₂, h, rfl, rfl⟩
  -- ⊢ (↑l₁, ↑l₂).fst + (↑l₁, ↑l₂).snd = ↑l
  exact Quot.sound (revzip_sublists _ _ _ h)
  -- 🎉 no goals
#align multiset.revzip_powerset_aux Multiset.revzip_powersetAux

theorem revzip_powersetAux' {l : List α} ⦃x⦄ (h : x ∈ revzip (powersetAux' l)) :
    x.1 + x.2 = ↑l := by
  rw [revzip, powersetAux', ← map_reverse, zip_map, ← revzip, List.mem_map] at h
  -- ⊢ x.fst + x.snd = ↑l
  simp only [Prod_map, Prod.exists] at h
  -- ⊢ x.fst + x.snd = ↑l
  rcases h with ⟨l₁, l₂, h, rfl, rfl⟩
  -- ⊢ (↑l₁, ↑l₂).fst + (↑l₁, ↑l₂).snd = ↑l
  exact Quot.sound (revzip_sublists' _ _ _ h)
  -- 🎉 no goals
#align multiset.revzip_powerset_aux' Multiset.revzip_powersetAux'

--Porting note: I don't understand why `{α : Type u}` is necessary here
theorem revzip_powersetAux_lemma {α : Type u} [DecidableEq α] (l : List α) {l' : List (Multiset α)}
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
  -- ⊢ Forall₂ (fun a c => a = (c, ↑l - c)) (revzip l') l'
  simpa using this
  -- 🎉 no goals
#align multiset.revzip_powerset_aux_lemma Multiset.revzip_powersetAux_lemma

theorem revzip_powersetAux_perm_aux' {l : List α} :
    revzip (powersetAux l) ~ revzip (powersetAux' l) := by
  haveI := Classical.decEq α
  -- ⊢ revzip (powersetAux l) ~ revzip (powersetAux' l)
  rw [revzip_powersetAux_lemma l revzip_powersetAux, revzip_powersetAux_lemma l revzip_powersetAux']
  -- ⊢ List.map (fun x => (x, ↑l - x)) (powersetAux l) ~ List.map (fun x => (x, ↑l  …
  exact powersetAux_perm_powersetAux'.map _
  -- 🎉 no goals
#align multiset.revzip_powerset_aux_perm_aux' Multiset.revzip_powersetAux_perm_aux'

theorem revzip_powersetAux_perm {l₁ l₂ : List α} (p : l₁ ~ l₂) :
    revzip (powersetAux l₁) ~ revzip (powersetAux l₂) := by
  haveI := Classical.decEq α
  -- ⊢ revzip (powersetAux l₁) ~ revzip (powersetAux l₂)
  simp [fun l : List α => revzip_powersetAux_lemma l revzip_powersetAux, coe_eq_coe.2 p]
  -- ⊢ List.map (fun x => (x, ↑l₂ - x)) (powersetAux l₁) ~ List.map (fun x => (x, ↑ …
  exact (powersetAux_perm p).map _
  -- 🎉 no goals
#align multiset.revzip_powerset_aux_perm Multiset.revzip_powersetAux_perm

/-! ### powersetLen -/


/-- Helper function for `powersetLen`. Given a list `l`, `powersetLenAux n l` is the list
of sublists of length `n`, as multisets. -/
def powersetLenAux (n : ℕ) (l : List α) : List (Multiset α) :=
  sublistsLenAux n l (↑) []
#align multiset.powerset_len_aux Multiset.powersetLenAux

theorem powersetLenAux_eq_map_coe {n} {l : List α} :
    powersetLenAux n l = (sublistsLen n l).map (↑) := by
  rw [powersetLenAux, sublistsLenAux_eq, append_nil]
  -- 🎉 no goals
#align multiset.powerset_len_aux_eq_map_coe Multiset.powersetLenAux_eq_map_coe

@[simp]
theorem mem_powersetLenAux {n} {l : List α} {s} : s ∈ powersetLenAux n l ↔ s ≤ ↑l ∧ card s = n :=
  Quotient.inductionOn s <| by
    simp [powersetLenAux_eq_map_coe, Subperm]
    -- ⊢ ∀ (a : List α), (∃ a_1, (a_1 <+ l ∧ length a_1 = n) ∧ a_1 ~ a) ↔ (∃ l_1, l_1 …
    exact fun l₁ =>
      ⟨fun ⟨l₂, ⟨s, e⟩, p⟩ => ⟨⟨_, p, s⟩, p.symm.length_eq.trans e⟩,
       fun ⟨⟨l₂, p, s⟩, e⟩ => ⟨_, ⟨s, p.length_eq.trans e⟩, p⟩⟩
#align multiset.mem_powerset_len_aux Multiset.mem_powersetLenAux

@[simp]
theorem powersetLenAux_zero (l : List α) : powersetLenAux 0 l = [0] := by
  simp [powersetLenAux_eq_map_coe]
  -- 🎉 no goals
#align multiset.powerset_len_aux_zero Multiset.powersetLenAux_zero

@[simp]
theorem powersetLenAux_nil (n : ℕ) : powersetLenAux (n + 1) (@nil α) = [] :=
  rfl
#align multiset.powerset_len_aux_nil Multiset.powersetLenAux_nil

@[simp]
theorem powersetLenAux_cons (n : ℕ) (a : α) (l : List α) :
    powersetLenAux (n + 1) (a :: l) =
      powersetLenAux (n + 1) l ++ List.map (cons a) (powersetLenAux n l) := by
  simp [powersetLenAux_eq_map_coe]; rfl
  -- ⊢ List.map (ofList ∘ List.cons a) (sublistsLen n l) = List.map (cons a ∘ ofLis …
                                    -- 🎉 no goals
#align multiset.powerset_len_aux_cons Multiset.powersetLenAux_cons

theorem powersetLenAux_perm {n} {l₁ l₂ : List α} (p : l₁ ~ l₂) :
    powersetLenAux n l₁ ~ powersetLenAux n l₂ := by
  induction' n with n IHn generalizing l₁ l₂
  -- ⊢ powersetLenAux Nat.zero l₁ ~ powersetLenAux Nat.zero l₂
  · simp
    -- 🎉 no goals
  induction' p with a l₁ l₂ p IH a b l l₁ l₂ l₃ _ _ IH₁ IH₂
  · rfl
    -- 🎉 no goals
  · simp only [powersetLenAux_cons]
    -- ⊢ powersetLenAux (n + 1) l₁ ++ List.map (cons a) (powersetLenAux n l₁) ~ power …
    exact IH.append ((IHn p).map _)
    -- 🎉 no goals
  · simp only [powersetLenAux_cons, append_assoc]
    -- ⊢ powersetLenAux (n + 1) l ++ (List.map (cons a) (powersetLenAux n l) ++ List. …
    apply Perm.append_left
    -- ⊢ List.map (cons a) (powersetLenAux n l) ++ List.map (cons b) (powersetLenAux  …
    cases n
    -- ⊢ List.map (cons a) (powersetLenAux Nat.zero l) ++ List.map (cons b) (powerset …
    · simp [Perm.swap]
      -- 🎉 no goals
    simp only [powersetLenAux_cons, map_append, List.map_map]
    -- ⊢ List.map (cons a) (powersetLenAux (Nat.succ n✝) l) ++ (List.map (cons b) (po …
    rw [← append_assoc, ← append_assoc,
      (by funext s; simp [cons_swap] : cons b ∘ cons a = cons a ∘ cons b)]
    exact perm_append_comm.append_right _
    -- 🎉 no goals
  · exact IH₁.trans IH₂
    -- 🎉 no goals
#align multiset.powerset_len_aux_perm Multiset.powersetLenAux_perm

/-- `powersetLen n s` is the multiset of all submultisets of `s` of length `n`. -/
def powersetLen (n : ℕ) (s : Multiset α) : Multiset (Multiset α) :=
  Quot.liftOn s (fun l => (powersetLenAux n l : Multiset (Multiset α))) fun _ _ h =>
    Quot.sound (powersetLenAux_perm h)
#align multiset.powerset_len Multiset.powersetLen

theorem powersetLen_coe' (n) (l : List α) : @powersetLen α n l = powersetLenAux n l :=
  rfl
#align multiset.powerset_len_coe' Multiset.powersetLen_coe'

theorem powersetLen_coe (n) (l : List α) :
    @powersetLen α n l = ((sublistsLen n l).map (↑) : List (Multiset α)) :=
  congr_arg ((↑) : List (Multiset α) → Multiset (Multiset α)) powersetLenAux_eq_map_coe
#align multiset.powerset_len_coe Multiset.powersetLen_coe

@[simp]
theorem powersetLen_zero_left (s : Multiset α) : powersetLen 0 s = {0} :=
  Quotient.inductionOn s fun l => by simp [powersetLen_coe']
                                     -- 🎉 no goals
#align multiset.powerset_len_zero_left Multiset.powersetLen_zero_left

theorem powersetLen_zero_right (n : ℕ) : @powersetLen α (n + 1) 0 = 0 :=
  rfl
#align multiset.powerset_len_zero_right Multiset.powersetLen_zero_right

@[simp]
theorem powersetLen_cons (n : ℕ) (a : α) (s) :
    powersetLen (n + 1) (a ::ₘ s) = powersetLen (n + 1) s + map (cons a) (powersetLen n s) :=
  Quotient.inductionOn s fun l => by simp [powersetLen_coe']
                                     -- 🎉 no goals
#align multiset.powerset_len_cons Multiset.powersetLen_cons

@[simp]
theorem mem_powersetLen {n : ℕ} {s t : Multiset α} : s ∈ powersetLen n t ↔ s ≤ t ∧ card s = n :=
  Quotient.inductionOn t fun l => by simp [powersetLen_coe']
                                     -- 🎉 no goals
#align multiset.mem_powerset_len Multiset.mem_powersetLen

@[simp]
theorem card_powersetLen (n : ℕ) (s : Multiset α) :
    card (powersetLen n s) = Nat.choose (card s) n :=
  Quotient.inductionOn s <| by simp [powersetLen_coe]
                               -- 🎉 no goals
#align multiset.card_powerset_len Multiset.card_powersetLen

theorem powersetLen_le_powerset (n : ℕ) (s : Multiset α) : powersetLen n s ≤ powerset s :=
  Quotient.inductionOn s fun l => by
    simp only [quot_mk_to_coe, powersetLen_coe, powerset_coe', coe_le]
    -- ⊢ List.map ofList (sublistsLen n l) <+~ List.map ofList (sublists' l)
    exact ((sublistsLen_sublist_sublists' _ _).map _).subperm
    -- 🎉 no goals
#align multiset.powerset_len_le_powerset Multiset.powersetLen_le_powerset

theorem powersetLen_mono (n : ℕ) {s t : Multiset α} (h : s ≤ t) :
    powersetLen n s ≤ powersetLen n t :=
  leInductionOn h fun {l₁ l₂} h => by
    simp only [powersetLen_coe, coe_le]
    -- ⊢ List.map ofList (sublistsLen n l₁) <+~ List.map ofList (sublistsLen n l₂)
    exact ((sublistsLen_sublist_of_sublist _ h).map _).subperm
    -- 🎉 no goals
#align multiset.powerset_len_mono Multiset.powersetLen_mono

@[simp]
theorem powersetLen_empty {α : Type*} (n : ℕ) {s : Multiset α} (h : card s < n) :
    powersetLen n s = 0 :=
  card_eq_zero.mp (Nat.choose_eq_zero_of_lt h ▸ card_powersetLen _ _)
#align multiset.powerset_len_empty Multiset.powersetLen_empty

@[simp]
theorem powersetLen_card_add (s : Multiset α) {i : ℕ} (hi : 0 < i) :
    s.powersetLen (card s + i) = 0 :=
  powersetLen_empty _ (lt_add_of_pos_right (card s) hi)
#align multiset.powerset_len_card_add Multiset.powersetLen_card_add

theorem powersetLen_map {β : Type*} (f : α → β) (n : ℕ) (s : Multiset α) :
    powersetLen n (s.map f) = (powersetLen n s).map (map f) := by
  induction' s using Multiset.induction with t s ih generalizing n
  -- ⊢ powersetLen n (map f 0) = map (map f) (powersetLen n 0)
  · cases n <;> simp [powersetLen_zero_left, powersetLen_zero_right]
    -- ⊢ powersetLen Nat.zero (map f 0) = map (map f) (powersetLen Nat.zero 0)
                -- 🎉 no goals
                -- 🎉 no goals
  · cases n <;> simp [ih, map_comp_cons]
    -- ⊢ powersetLen Nat.zero (map f (t ::ₘ s)) = map (map f) (powersetLen Nat.zero ( …
                -- 🎉 no goals
                -- 🎉 no goals
#align multiset.powerset_len_map Multiset.powersetLen_map

theorem pairwise_disjoint_powersetLen (s : Multiset α) :
    _root_.Pairwise fun i j => Multiset.Disjoint (s.powersetLen i) (s.powersetLen j) :=
  fun _ _ h _ hi hj =>
  h (Eq.trans (Multiset.mem_powersetLen.mp hi).right.symm (Multiset.mem_powersetLen.mp hj).right)
#align multiset.pairwise_disjoint_powerset_len Multiset.pairwise_disjoint_powersetLen

theorem bind_powerset_len {α : Type*} (S : Multiset α) :
    (bind (Multiset.range (card S + 1)) fun k => S.powersetLen k) = S.powerset := by
  induction S using Quotient.inductionOn
  -- ⊢ (bind (range (↑card (Quotient.mk (isSetoid α) a✝) + 1)) fun k => powersetLen …
  simp_rw [quot_mk_to_coe, powerset_coe', powersetLen_coe, ← coe_range, coe_bind, ← List.bind_map,
    coe_card]
  exact coe_eq_coe.mpr ((List.range_bind_sublistsLen_perm _).map _)
  -- 🎉 no goals
#align multiset.bind_powerset_len Multiset.bind_powerset_len

@[simp]
theorem nodup_powerset {s : Multiset α} : Nodup (powerset s) ↔ Nodup s :=
  ⟨fun h => (nodup_of_le (map_single_le_powerset _) h).of_map _,
    Quotient.inductionOn s fun l h => by
      simp only [quot_mk_to_coe, powerset_coe', coe_nodup]
      -- ⊢ List.Nodup (List.map ofList (sublists' l))
      refine' (nodup_sublists'.2 h).map_on _
      -- ⊢ ∀ (x : List α), x ∈ sublists' l → ∀ (y : List α), y ∈ sublists' l → ↑x = ↑y  …
      exact fun x sx y sy e =>
        (h.sublist_ext (mem_sublists'.1 sx) (mem_sublists'.1 sy)).1 (Quotient.exact e)⟩
#align multiset.nodup_powerset Multiset.nodup_powerset

alias ⟨Nodup.ofPowerset, Nodup.powerset⟩ := nodup_powerset
#align multiset.nodup.of_powerset Multiset.Nodup.ofPowerset
#align multiset.nodup.powerset Multiset.Nodup.powerset

protected theorem Nodup.powersetLen {n : ℕ} {s : Multiset α} (h : Nodup s) :
    Nodup (powersetLen n s) :=
  nodup_of_le (powersetLen_le_powerset _ _) (nodup_powerset.2 h)
#align multiset.nodup.powerset_len Multiset.Nodup.powersetLen

end Multiset
