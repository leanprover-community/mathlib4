/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Multiset.Powerset

#align_import data.finset.powerset from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# The powerset of a finset
-/


namespace Finset

open Function Multiset

variable {α : Type*} {s t : Finset α}

/-! ### powerset -/


section Powerset

/-- When `s` is a finset, `s.powerset` is the finset of all subsets of `s` (seen as finsets). -/
def powerset (s : Finset α) : Finset (Finset α) :=
  ⟨(s.1.powerset.pmap Finset.mk) fun _t h => nodup_of_le (mem_powerset.1 h) s.nodup,
    s.nodup.powerset.pmap fun _a _ha _b _hb => congr_arg Finset.val⟩
#align finset.powerset Finset.powerset

@[simp]
theorem mem_powerset {s t : Finset α} : s ∈ powerset t ↔ s ⊆ t := by
  cases s
  -- ⊢ { val := val✝, nodup := nodup✝ } ∈ powerset t ↔ { val := val✝, nodup := nodu …
  simp [powerset, mem_mk, mem_pmap, mk.injEq, mem_powerset, exists_prop, exists_eq_right,
    ← val_le_iff]
#align finset.mem_powerset Finset.mem_powerset

@[simp, norm_cast]
theorem coe_powerset (s : Finset α) :
    (s.powerset : Set (Finset α)) = ((↑) : Finset α → Set α) ⁻¹' (s : Set α).powerset := by
  ext
  -- ⊢ x✝ ∈ ↑(powerset s) ↔ x✝ ∈ toSet ⁻¹' 𝒫↑s
  simp
  -- 🎉 no goals
#align finset.coe_powerset Finset.coe_powerset

--Porting note: remove @[simp], simp can prove it
theorem empty_mem_powerset (s : Finset α) : ∅ ∈ powerset s :=
  mem_powerset.2 (empty_subset _)
#align finset.empty_mem_powerset Finset.empty_mem_powerset

--Porting note: remove @[simp], simp can prove it
theorem mem_powerset_self (s : Finset α) : s ∈ powerset s :=
  mem_powerset.2 Subset.rfl
#align finset.mem_powerset_self Finset.mem_powerset_self

theorem powerset_nonempty (s : Finset α) : s.powerset.Nonempty :=
  ⟨∅, empty_mem_powerset _⟩
#align finset.powerset_nonempty Finset.powerset_nonempty

@[simp]
theorem powerset_mono {s t : Finset α} : powerset s ⊆ powerset t ↔ s ⊆ t :=
  ⟨fun h => mem_powerset.1 <| h <| mem_powerset_self _, fun st _u h =>
    mem_powerset.2 <| Subset.trans (mem_powerset.1 h) st⟩
#align finset.powerset_mono Finset.powerset_mono

theorem powerset_injective : Injective (powerset : Finset α → Finset (Finset α)) :=
  (injective_of_le_imp_le _) powerset_mono.1
#align finset.powerset_injective Finset.powerset_injective

@[simp]
theorem powerset_inj : powerset s = powerset t ↔ s = t :=
  powerset_injective.eq_iff
#align finset.powerset_inj Finset.powerset_inj

@[simp]
theorem powerset_empty : (∅ : Finset α).powerset = {∅} :=
  rfl
#align finset.powerset_empty Finset.powerset_empty

@[simp]
theorem powerset_eq_singleton_empty : s.powerset = {∅} ↔ s = ∅ := by
  rw [← powerset_empty, powerset_inj]
  -- 🎉 no goals
#align finset.powerset_eq_singleton_empty Finset.powerset_eq_singleton_empty

/-- **Number of Subsets of a Set** -/
@[simp]
theorem card_powerset (s : Finset α) : card (powerset s) = 2 ^ card s :=
  (card_pmap _ _ _).trans (Multiset.card_powerset s.1)
#align finset.card_powerset Finset.card_powerset

theorem not_mem_of_mem_powerset_of_not_mem {s t : Finset α} {a : α} (ht : t ∈ s.powerset)
    (h : a ∉ s) : a ∉ t := by
  apply mt _ h
  -- ⊢ a ∈ t → a ∈ s
  apply mem_powerset.1 ht
  -- 🎉 no goals
#align finset.not_mem_of_mem_powerset_of_not_mem Finset.not_mem_of_mem_powerset_of_not_mem

theorem powerset_insert [DecidableEq α] (s : Finset α) (a : α) :
    powerset (insert a s) = s.powerset ∪ s.powerset.image (insert a) := by
  ext t
  -- ⊢ t ∈ powerset (insert a s) ↔ t ∈ powerset s ∪ image (insert a) (powerset s)
  simp only [exists_prop, mem_powerset, mem_image, mem_union, subset_insert_iff]
  -- ⊢ erase t a ⊆ s ↔ t ⊆ s ∨ ∃ a_1, a_1 ⊆ s ∧ insert a a_1 = t
  by_cases h : a ∈ t
  -- ⊢ erase t a ⊆ s ↔ t ⊆ s ∨ ∃ a_1, a_1 ⊆ s ∧ insert a a_1 = t
  · constructor
    -- ⊢ erase t a ⊆ s → t ⊆ s ∨ ∃ a_2, a_2 ⊆ s ∧ insert a a_2 = t
    · exact fun H => Or.inr ⟨_, H, insert_erase h⟩
      -- 🎉 no goals
    · intro H
      -- ⊢ erase t a ⊆ s
      cases' H with H H
      -- ⊢ erase t a ⊆ s
      · exact Subset.trans (erase_subset a t) H
        -- 🎉 no goals
      · rcases H with ⟨u, hu⟩
        -- ⊢ erase t a ⊆ s
        rw [← hu.2]
        -- ⊢ erase (insert a u) a ⊆ s
        exact Subset.trans (erase_insert_subset a u) hu.1
        -- 🎉 no goals
  · have : ¬∃ u : Finset α, u ⊆ s ∧ insert a u = t := by simp [Ne.symm (ne_insert_of_not_mem _ _ h)]
    -- ⊢ erase t a ⊆ s ↔ t ⊆ s ∨ ∃ a_1, a_1 ⊆ s ∧ insert a a_1 = t
    simp [Finset.erase_eq_of_not_mem h, this]
    -- 🎉 no goals
#align finset.powerset_insert Finset.powerset_insert

/-- For predicate `p` decidable on subsets, it is decidable whether `p` holds for any subset. -/
instance decidableExistsOfDecidableSubsets {s : Finset α} {p : ∀ (t) (_ : t ⊆ s), Prop}
    [∀ (t) (h : t ⊆ s), Decidable (p t h)] : Decidable (∃ (t : _) (h : t ⊆ s), p t h) :=
  decidable_of_iff (∃ (t : _) (hs : t ∈ s.powerset), p t (mem_powerset.1 hs))
    ⟨fun ⟨t, _, hp⟩ => ⟨t, _, hp⟩, fun ⟨t, hs, hp⟩ => ⟨t, mem_powerset.2 hs, hp⟩⟩
#align finset.decidable_exists_of_decidable_subsets Finset.decidableExistsOfDecidableSubsets

/-- For predicate `p` decidable on subsets, it is decidable whether `p` holds for every subset. -/
instance decidableForallOfDecidableSubsets {s : Finset α} {p : ∀ (t) (_ : t ⊆ s), Prop}
    [∀ (t) (h : t ⊆ s), Decidable (p t h)] : Decidable (∀ (t) (h : t ⊆ s), p t h) :=
  decidable_of_iff (∀ (t) (h : t ∈ s.powerset), p t (mem_powerset.1 h))
    ⟨fun h t hs => h t (mem_powerset.2 hs), fun h _ _ => h _ _⟩
#align finset.decidable_forall_of_decidable_subsets Finset.decidableForallOfDecidableSubsets

/-- A version of `Finset.decidableExistsOfDecidableSubsets` with a non-dependent `p`.
Typeclass inference cannot find `hu` here, so this is not an instance. -/
def decidableExistsOfDecidableSubsets' {s : Finset α} {p : Finset α → Prop}
    (hu : ∀ (t) (_h : t ⊆ s), Decidable (p t)) : Decidable (∃ (t : _) (_h : t ⊆ s), p t) :=
  @Finset.decidableExistsOfDecidableSubsets _ _ _ hu
#align finset.decidable_exists_of_decidable_subsets' Finset.decidableExistsOfDecidableSubsets'

/-- A version of `Finset.decidableForallOfDecidableSubsets` with a non-dependent `p`.
Typeclass inference cannot find `hu` here, so this is not an instance. -/
def decidableForallOfDecidableSubsets' {s : Finset α} {p : Finset α → Prop}
    (hu : ∀ (t) (_h : t ⊆ s), Decidable (p t)) : Decidable (∀ (t) (_h : t ⊆ s), p t) :=
  @Finset.decidableForallOfDecidableSubsets _ _ _ hu
#align finset.decidable_forall_of_decidable_subsets' Finset.decidableForallOfDecidableSubsets'

end Powerset

section SSubsets

variable [DecidableEq α]

/-- For `s` a finset, `s.ssubsets` is the finset comprising strict subsets of `s`. -/
def ssubsets (s : Finset α) : Finset (Finset α) :=
  erase (powerset s) s
#align finset.ssubsets Finset.ssubsets

@[simp]
theorem mem_ssubsets {s t : Finset α} : t ∈ s.ssubsets ↔ t ⊂ s := by
  rw [ssubsets, mem_erase, mem_powerset, ssubset_iff_subset_ne, and_comm]
  -- 🎉 no goals
#align finset.mem_ssubsets Finset.mem_ssubsets

theorem empty_mem_ssubsets {s : Finset α} (h : s.Nonempty) : ∅ ∈ s.ssubsets := by
  rw [mem_ssubsets, ssubset_iff_subset_ne]
  -- ⊢ ∅ ⊆ s ∧ ∅ ≠ s
  exact ⟨empty_subset s, h.ne_empty.symm⟩
  -- 🎉 no goals
#align finset.empty_mem_ssubsets Finset.empty_mem_ssubsets
/-- For predicate `p` decidable on ssubsets, it is decidable whether `p` holds for any ssubset. -/
instance decidableExistsOfDecidableSSubsets {s : Finset α} {p : ∀ (t) (_ : t ⊂ s), Prop}
    [∀ (t) (h : t ⊂ s), Decidable (p t h)] : Decidable (∃ t h, p t h) :=
  decidable_of_iff (∃ (t : _) (hs : t ∈ s.ssubsets), p t (mem_ssubsets.1 hs))
    ⟨fun ⟨t, _, hp⟩ => ⟨t, _, hp⟩, fun ⟨t, hs, hp⟩ => ⟨t, mem_ssubsets.2 hs, hp⟩⟩
#align finset.decidable_exists_of_decidable_ssubsets Finset.decidableExistsOfDecidableSSubsets

/-- For predicate `p` decidable on ssubsets, it is decidable whether `p` holds for every ssubset. -/
instance decidableForallOfDecidableSSubsets {s : Finset α} {p : ∀ (t) (_ : t ⊂ s), Prop}
    [∀ (t) (h : t ⊂ s), Decidable (p t h)] : Decidable (∀ t h, p t h) :=
  decidable_of_iff (∀ (t) (h : t ∈ s.ssubsets), p t (mem_ssubsets.1 h))
    ⟨fun h t hs => h t (mem_ssubsets.2 hs), fun h _ _ => h _ _⟩
#align finset.decidable_forall_of_decidable_ssubsets Finset.decidableForallOfDecidableSSubsets

/-- A version of `Finset.decidableExistsOfDecidableSSubsets` with a non-dependent `p`.
Typeclass inference cannot find `hu` here, so this is not an instance. -/
def decidableExistsOfDecidableSSubsets' {s : Finset α} {p : Finset α → Prop}
    (hu : ∀ (t) (_h : t ⊂ s), Decidable (p t)) : Decidable (∃ (t : _) (_h : t ⊂ s), p t) :=
  @Finset.decidableExistsOfDecidableSSubsets _ _ _ _ hu
#align finset.decidable_exists_of_decidable_ssubsets' Finset.decidableExistsOfDecidableSSubsets'

/-- A version of `Finset.decidableForallOfDecidableSSubsets` with a non-dependent `p`.
Typeclass inference cannot find `hu` here, so this is not an instance. -/
def decidableForallOfDecidableSSubsets' {s : Finset α} {p : Finset α → Prop}
    (hu : ∀ (t) (_h : t ⊂ s), Decidable (p t)) : Decidable (∀ (t) (_h : t ⊂ s), p t) :=
  @Finset.decidableForallOfDecidableSSubsets _ _ _ _ hu
#align finset.decidable_forall_of_decidable_ssubsets' Finset.decidableForallOfDecidableSSubsets'

end SSubsets

section PowersetLen

/-- Given an integer `n` and a finset `s`, then `powersetLen n s` is the finset of subsets of `s`
of cardinality `n`. -/
def powersetLen (n : ℕ) (s : Finset α) : Finset (Finset α) :=
  ⟨((s.1.powersetLen n).pmap Finset.mk) fun _t h => nodup_of_le (mem_powersetLen.1 h).1 s.2,
    s.2.powersetLen.pmap fun _a _ha _b _hb => congr_arg Finset.val⟩
#align finset.powerset_len Finset.powersetLen

/-- **Formula for the Number of Combinations** -/
theorem mem_powersetLen {n} {s t : Finset α} : s ∈ powersetLen n t ↔ s ⊆ t ∧ card s = n := by
  cases s; simp [powersetLen, val_le_iff.symm]
  -- ⊢ { val := val✝, nodup := nodup✝ } ∈ powersetLen n t ↔ { val := val✝, nodup := …
           -- 🎉 no goals
#align finset.mem_powerset_len Finset.mem_powersetLen

@[simp]
theorem powersetLen_mono {n} {s t : Finset α} (h : s ⊆ t) : powersetLen n s ⊆ powersetLen n t :=
  fun _u h' => mem_powersetLen.2 <| And.imp (fun h₂ => Subset.trans h₂ h) id (mem_powersetLen.1 h')
#align finset.powerset_len_mono Finset.powersetLen_mono

/-- **Formula for the Number of Combinations** -/
@[simp]
theorem card_powersetLen (n : ℕ) (s : Finset α) : card (powersetLen n s) = Nat.choose (card s) n :=
  (card_pmap _ _ _).trans (Multiset.card_powersetLen n s.1)
#align finset.card_powerset_len Finset.card_powersetLen

@[simp]
theorem powersetLen_zero (s : Finset α) : Finset.powersetLen 0 s = {∅} := by
  ext; rw [mem_powersetLen, mem_singleton, card_eq_zero]
  -- ⊢ a✝ ∈ powersetLen 0 s ↔ a✝ ∈ {∅}
       -- ⊢ a✝ ⊆ s ∧ a✝ = ∅ ↔ a✝ = ∅
  refine'
    ⟨fun h => h.2, fun h => by
      rw [h]
      exact ⟨empty_subset s, rfl⟩⟩
#align finset.powerset_len_zero Finset.powersetLen_zero

@[simp]
theorem powersetLen_empty (n : ℕ) {s : Finset α} (h : s.card < n) : powersetLen n s = ∅ :=
  Finset.card_eq_zero.mp (by rw [card_powersetLen, Nat.choose_eq_zero_of_lt h])
                             -- 🎉 no goals
#align finset.powerset_len_empty Finset.powersetLen_empty

theorem powersetLen_eq_filter {n} {s : Finset α} :
    powersetLen n s = (powerset s).filter fun x => x.card = n := by
  ext
  -- ⊢ a✝ ∈ powersetLen n s ↔ a✝ ∈ filter (fun x => card x = n) (powerset s)
  simp [mem_powersetLen]
  -- 🎉 no goals
#align finset.powerset_len_eq_filter Finset.powersetLen_eq_filter

theorem powersetLen_succ_insert [DecidableEq α] {x : α} {s : Finset α} (h : x ∉ s) (n : ℕ) :
    powersetLen n.succ (insert x s) =
    powersetLen n.succ s ∪ (powersetLen n s).image (insert x) := by
  rw [powersetLen_eq_filter, powerset_insert, filter_union, ← powersetLen_eq_filter]
  -- ⊢ powersetLen (Nat.succ n) s ∪ filter (fun x => card x = Nat.succ n) (image (i …
  congr
  -- ⊢ filter (fun x => card x = Nat.succ n) (image (insert x) (powerset s)) = imag …
  rw [powersetLen_eq_filter, image_filter]
  -- ⊢ image (insert x) (filter ((fun x => card x = Nat.succ n) ∘ insert x) (powers …
  congr 1
  -- ⊢ filter ((fun x => card x = Nat.succ n) ∘ insert x) (powerset s) = filter (fu …
  ext t
  -- ⊢ t ∈ filter ((fun x => card x = Nat.succ n) ∘ insert x) (powerset s) ↔ t ∈ fi …
  simp only [mem_powerset, mem_filter, Function.comp_apply, and_congr_right_iff]
  -- ⊢ t ⊆ s → (card (insert x t) = Nat.succ n ↔ card t = n)
  intro ht
  -- ⊢ card (insert x t) = Nat.succ n ↔ card t = n
  have : x ∉ t := fun H => h (ht H)
  -- ⊢ card (insert x t) = Nat.succ n ↔ card t = n
  simp [card_insert_of_not_mem this, Nat.succ_inj']
  -- 🎉 no goals
#align finset.powerset_len_succ_insert Finset.powersetLen_succ_insert

theorem powersetLen_nonempty {n : ℕ} {s : Finset α} (h : n ≤ s.card) :
    (powersetLen n s).Nonempty := by
  classical
    induction' s using Finset.induction_on with x s hx IH generalizing n
    · rw [card_empty, le_zero_iff] at h
      rw [h, powersetLen_zero]
      exact Finset.singleton_nonempty _
    · cases n
      · simp
      · rw [card_insert_of_not_mem hx, Nat.succ_le_succ_iff] at h
        rw [powersetLen_succ_insert hx]
        refine' Nonempty.mono _ ((IH h).image (insert x))
        exact subset_union_right _ _
#align finset.powerset_len_nonempty Finset.powersetLen_nonempty

@[simp]
theorem powersetLen_self (s : Finset α) : powersetLen s.card s = {s} := by
  ext
  -- ⊢ a✝ ∈ powersetLen (card s) s ↔ a✝ ∈ {s}
  rw [mem_powersetLen, mem_singleton]
  -- ⊢ a✝ ⊆ s ∧ card a✝ = card s ↔ a✝ = s
  constructor
  -- ⊢ a✝ ⊆ s ∧ card a✝ = card s → a✝ = s
  · exact fun ⟨hs, hc⟩ => eq_of_subset_of_card_le hs hc.ge
    -- 🎉 no goals
  · rintro rfl
    -- ⊢ a✝ ⊆ a✝ ∧ card a✝ = card a✝
    simp
    -- 🎉 no goals
#align finset.powerset_len_self Finset.powersetLen_self

theorem pairwise_disjoint_powersetLen (s : Finset α) :
    Pairwise fun i j => Disjoint (s.powersetLen i) (s.powersetLen j) := fun _i _j hij =>
  Finset.disjoint_left.mpr fun _x hi hj =>
    hij <| (mem_powersetLen.mp hi).2.symm.trans (mem_powersetLen.mp hj).2
#align finset.pairwise_disjoint_powerset_len Finset.pairwise_disjoint_powersetLen

theorem powerset_card_disjiUnion (s : Finset α) :
    Finset.powerset s =
      (range (s.card + 1)).disjiUnion (fun i => powersetLen i s)
        (s.pairwise_disjoint_powersetLen.set_pairwise _) := by
  refine' ext fun a => ⟨fun ha => _, fun ha => _⟩
  -- ⊢ a ∈ disjiUnion (range (card s + 1)) (fun i => powersetLen i s) (_ : Set.Pair …
  · rw [mem_disjiUnion]
    -- ⊢ ∃ a_1, a_1 ∈ range (card s + 1) ∧ a ∈ powersetLen a_1 s
    exact
      ⟨a.card, mem_range.mpr (Nat.lt_succ_of_le (card_le_of_subset (mem_powerset.mp ha))),
        mem_powersetLen.mpr ⟨mem_powerset.mp ha, rfl⟩⟩
  · rcases mem_disjiUnion.mp ha with ⟨i, _hi, ha⟩
    -- ⊢ a ∈ powerset s
    exact mem_powerset.mpr (mem_powersetLen.mp ha).1
    -- 🎉 no goals
#align finset.powerset_card_disj_Union Finset.powerset_card_disjiUnion

theorem powerset_card_biUnion [DecidableEq (Finset α)] (s : Finset α) :
    Finset.powerset s = (range (s.card + 1)).biUnion fun i => powersetLen i s := by
  simpa only [disjiUnion_eq_biUnion] using powerset_card_disjiUnion s
  -- 🎉 no goals
#align finset.powerset_card_bUnion Finset.powerset_card_biUnion

theorem powersetLen_sup [DecidableEq α] (u : Finset α) (n : ℕ) (hn : n < u.card) :
    (powersetLen n.succ u).sup id = u := by
  apply le_antisymm
  -- ⊢ sup (powersetLen (Nat.succ n) u) id ≤ u
  · simp_rw [Finset.sup_le_iff, mem_powersetLen]
    -- ⊢ ∀ (b : Finset α), b ⊆ u ∧ card b = Nat.succ n → id b ≤ u
    rintro x ⟨h, -⟩
    -- ⊢ id x ≤ u
    exact h
    -- 🎉 no goals
  · rw [sup_eq_biUnion, le_iff_subset, subset_iff]
    -- ⊢ ∀ ⦃x : α⦄, x ∈ u → x ∈ Finset.biUnion (powersetLen (Nat.succ n) u) id
    cases' (Nat.succ_le_of_lt hn).eq_or_lt with h' h'
    -- ⊢ ∀ ⦃x : α⦄, x ∈ u → x ∈ Finset.biUnion (powersetLen (Nat.succ n) u) id
    · simp [h']
      -- 🎉 no goals
    · intro x hx
      -- ⊢ x ∈ Finset.biUnion (powersetLen (Nat.succ n) u) id
      simp only [mem_biUnion, exists_prop, id.def]
      -- ⊢ ∃ a, a ∈ powersetLen (Nat.succ n) u ∧ x ∈ a
      obtain ⟨t, ht⟩ : ∃ t, t ∈ powersetLen n (u.erase x) := powersetLen_nonempty
        (le_trans (Nat.le_pred_of_lt hn) pred_card_le_card_erase)
      · refine' ⟨insert x t, _, mem_insert_self _ _⟩
        -- ⊢ insert x t ∈ powersetLen (Nat.succ n) u
        rw [← insert_erase hx, powersetLen_succ_insert (not_mem_erase _ _)]
        -- ⊢ insert x t ∈ powersetLen (Nat.succ n) (erase u x) ∪ image (insert x) (powers …
        exact mem_union_right _ (mem_image_of_mem _ ht)
        -- 🎉 no goals
#align finset.powerset_len_sup Finset.powersetLen_sup

@[simp]
theorem powersetLen_card_add (s : Finset α) {i : ℕ} (hi : 0 < i) :
    s.powersetLen (s.card + i) = ∅ :=
  Finset.powersetLen_empty _ (lt_add_of_pos_right (Finset.card s) hi)
#align finset.powerset_len_card_add Finset.powersetLen_card_add

@[simp]
theorem map_val_val_powersetLen (s : Finset α) (i : ℕ) :
    (s.powersetLen i).val.map Finset.val = s.1.powersetLen i := by
  simp [Finset.powersetLen, map_pmap, pmap_eq_map, map_id']
  -- 🎉 no goals
#align finset.map_val_val_powerset_len Finset.map_val_val_powersetLen

theorem powersetLen_map {β : Type*} (f : α ↪ β) (n : ℕ) (s : Finset α) :
    powersetLen n (s.map f) = (powersetLen n s).map (mapEmbedding f).toEmbedding :=
  ext <| fun t => by
    simp only [card_map, mem_powersetLen, le_eq_subset, gt_iff_lt, mem_map, mapEmbedding_apply]
    -- ⊢ t ⊆ map f s ∧ card t = n ↔ ∃ a, (a ⊆ s ∧ card a = n) ∧ ↑(mapEmbedding f).toE …
    constructor
    -- ⊢ t ⊆ map f s ∧ card t = n → ∃ a, (a ⊆ s ∧ card a = n) ∧ ↑(mapEmbedding f).toE …
    · classical
      intro h
      have : map f (filter (fun x => (f x ∈ t)) s) = t := by
        ext x
        simp only [mem_map, mem_filter, decide_eq_true_eq]
        exact ⟨fun ⟨_y, ⟨_hy₁, hy₂⟩, hy₃⟩ => hy₃ ▸ hy₂,
          fun hx => let ⟨y, hy⟩ := mem_map.1 (h.1 hx); ⟨y, ⟨hy.1, hy.2 ▸ hx⟩, hy.2⟩⟩
      refine' ⟨_, _, this⟩
      rw [← card_map f, this, h.2]; simp
    · rintro ⟨a, ⟨has, rfl⟩, rfl⟩
      -- ⊢ ↑(mapEmbedding f).toEmbedding a ⊆ map f s ∧ card (↑(mapEmbedding f).toEmbedd …
      dsimp [RelEmbedding.coe_toEmbedding]
      -- ⊢ ↑(mapEmbedding f) a ⊆ map f s ∧ card (↑(mapEmbedding f) a) = card a
      --Porting note: Why is `rw` required here and not `simp`?
      rw [mapEmbedding_apply]
      -- ⊢ map f a ⊆ map f s ∧ card (map f a) = card a
      simp [has]
      -- 🎉 no goals
#align finset.powerset_len_map Finset.powersetLen_map

end PowersetLen

end Finset
