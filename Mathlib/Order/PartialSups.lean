/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.Finset.Lattice
import Mathlib.Order.Hom.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset

#align_import order.partial_sups from "leanprover-community/mathlib"@"d6fad0e5bf2d6f48da9175d25c3dc5706b3834ce"

/-!
# The monotone sequence of partial supremums of a sequence

We define `partialSups : (ℕ → α) → ℕ →o α` inductively. For `f : ℕ → α`, `partialSups f` is
the sequence `f 0 `, `f 0 ⊔ f 1`, `f 0 ⊔ f 1 ⊔ f 2`, ... The point of this definition is that
* it doesn't need a `⨆`, as opposed to `⨆ (i ≤ n), f i` (which also means the wrong thing on
  `ConditionallyCompleteLattice`s).
* it doesn't need a `⊥`, as opposed to `(Finset.range (n + 1)).sup f`.
* it avoids needing to prove that `Finset.range (n + 1)` is nonempty to use `Finset.sup'`.

Equivalence with those definitions is shown by `partialSups_eq_biSup`, `partialSups_eq_sup_range`,
and `partialSups_eq_sup'_range` respectively.

## Notes

One might dispute whether this sequence should start at `f 0` or `⊥`. We choose the former because :
* Starting at `⊥` requires... having a bottom element.
* `fun f n ↦ (Finset.range n).sup f` is already effectively the sequence starting at `⊥`.
* If we started at `⊥` we wouldn't have the Galois insertion. See `partialSups.gi`.

## TODO

One could generalize `partialSups` to any locally finite bot preorder domain, in place of `ℕ`.
Necessary for the TODO in the module docstring of `Order.disjointed`.
-/


variable {α : Type*}

section SemilatticeSup

variable [SemilatticeSup α]

/-- The monotone sequence whose value at `n` is the supremum of the `f m` where `m ≤ n`. -/
def partialSups (f : ℕ → α) : ℕ →o α :=
  ⟨@Nat.rec (fun _ => α) (f 0) fun (n : ℕ) (a : α) => a ⊔ f (n + 1),
    monotone_nat_of_le_succ fun _ => le_sup_left⟩
#align partial_sups partialSups

@[simp]
theorem partialSups_zero (f : ℕ → α) : partialSups f 0 = f 0 :=
  rfl
#align partial_sups_zero partialSups_zero

@[simp]
theorem partialSups_succ (f : ℕ → α) (n : ℕ) :
    partialSups f (n + 1) = partialSups f n ⊔ f (n + 1) :=
  rfl
#align partial_sups_succ partialSups_succ

theorem le_partialSups_of_le (f : ℕ → α) {m n : ℕ} (h : m ≤ n) : f m ≤ partialSups f n := by
  induction' n with n ih
  -- ⊢ f m ≤ ↑(partialSups f) Nat.zero
  · rw [nonpos_iff_eq_zero.mp h, partialSups_zero]
    -- 🎉 no goals
  · cases' h with h h
    -- ⊢ f (Nat.succ n) ≤ ↑(partialSups f) (Nat.succ n)
    · exact le_sup_right
      -- 🎉 no goals
    · exact (ih h).trans le_sup_left
      -- 🎉 no goals
#align le_partial_sups_of_le le_partialSups_of_le

theorem le_partialSups (f : ℕ → α) : f ≤ partialSups f := fun _n => le_partialSups_of_le f le_rfl
#align le_partial_sups le_partialSups

theorem partialSups_le (f : ℕ → α) (n : ℕ) (a : α) (w : ∀ m, m ≤ n → f m ≤ a) :
    partialSups f n ≤ a := by
  induction' n with n ih
  -- ⊢ ↑(partialSups f) Nat.zero ≤ a
  · apply w 0 le_rfl
    -- 🎉 no goals
  · exact sup_le (ih fun m p => w m (Nat.le_succ_of_le p)) (w (n + 1) le_rfl)
    -- 🎉 no goals
#align partial_sups_le partialSups_le

@[simp]
theorem bddAbove_range_partialSups {f : ℕ → α} :
    BddAbove (Set.range (partialSups f)) ↔ BddAbove (Set.range f) := by
  apply exists_congr fun a => _
  -- ⊢ ∀ (a : α), a ∈ upperBounds (Set.range ↑(partialSups f)) ↔ a ∈ upperBounds (S …
  intro a
  -- ⊢ a ∈ upperBounds (Set.range ↑(partialSups f)) ↔ a ∈ upperBounds (Set.range f)
  constructor
  -- ⊢ a ∈ upperBounds (Set.range ↑(partialSups f)) → a ∈ upperBounds (Set.range f)
  · rintro h b ⟨i, rfl⟩
    -- ⊢ f i ≤ a
    exact (le_partialSups _ _).trans (h (Set.mem_range_self i))
    -- 🎉 no goals
  · rintro h b ⟨i, rfl⟩
    -- ⊢ ↑(partialSups f) i ≤ a
    exact partialSups_le _ _ _ fun _ _ => h (Set.mem_range_self _)
    -- 🎉 no goals
#align bdd_above_range_partial_sups bddAbove_range_partialSups

theorem Monotone.partialSups_eq {f : ℕ → α} (hf : Monotone f) : (partialSups f : ℕ → α) = f := by
  ext n
  -- ⊢ ↑(partialSups f) n = f n
  induction' n with n ih
  -- ⊢ ↑(partialSups f) Nat.zero = f Nat.zero
  · rfl
    -- 🎉 no goals
  · rw [partialSups_succ, ih, sup_eq_right.2 (hf (Nat.le_succ _))]
    -- 🎉 no goals
#align monotone.partial_sups_eq Monotone.partialSups_eq

theorem partialSups_mono : Monotone (partialSups : (ℕ → α) → ℕ →o α) := by
  rintro f g h n
  -- ⊢ OrderHom.toFun (partialSups f) n ≤ OrderHom.toFun (partialSups g) n
  induction' n with n ih
  -- ⊢ OrderHom.toFun (partialSups f) Nat.zero ≤ OrderHom.toFun (partialSups g) Nat …
  · exact h 0
    -- 🎉 no goals
  · exact sup_le_sup ih (h _)
    -- 🎉 no goals
#align partial_sups_mono partialSups_mono

/-- `partialSups` forms a Galois insertion with the coercion from monotone functions to functions.
-/
def partialSups.gi : GaloisInsertion (partialSups : (ℕ → α) → ℕ →o α) (↑) where
  choice f h :=
    ⟨f, by convert (partialSups f).monotone using 1; exact (le_partialSups f).antisymm h⟩
           -- ⊢ f = ↑(partialSups f)
                                                     -- 🎉 no goals
  gc f g := by
    refine' ⟨(le_partialSups f).trans, fun h => _⟩
    -- ⊢ partialSups f ≤ g
    convert partialSups_mono h
    -- ⊢ g = partialSups ↑g
    exact OrderHom.ext _ _ g.monotone.partialSups_eq.symm
    -- 🎉 no goals
  le_l_u f := le_partialSups f
  choice_eq f h := OrderHom.ext _ _ ((le_partialSups f).antisymm h)
#align partial_sups.gi partialSups.gi

theorem partialSups_eq_sup'_range (f : ℕ → α) (n : ℕ) :
    partialSups f n = (Finset.range (n + 1)).sup' ⟨n, Finset.self_mem_range_succ n⟩ f := by
  induction' n with n ih
  -- ⊢ ↑(partialSups f) Nat.zero = Finset.sup' (Finset.range (Nat.zero + 1)) (_ : ∃ …
  · simp
    -- 🎉 no goals
  · dsimp [partialSups] at ih ⊢
    -- ⊢ Nat.rec (f 0) (fun n a => a ⊔ f (n + 1)) n ⊔ f (n + 1) = Finset.sup' (Finset …
    simp_rw [@Finset.range_succ n.succ]
    -- ⊢ Nat.rec (f 0) (fun n a => a ⊔ f (n + 1)) n ⊔ f (n + 1) = Finset.sup' (insert …
    rw [ih, Finset.sup'_insert, sup_comm]
    -- 🎉 no goals
#align partial_sups_eq_sup'_range partialSups_eq_sup'_range

end SemilatticeSup

theorem partialSups_eq_sup_range [SemilatticeSup α] [OrderBot α] (f : ℕ → α) (n : ℕ) :
    partialSups f n = (Finset.range (n + 1)).sup f := by
  induction' n with n ih
  -- ⊢ ↑(partialSups f) Nat.zero = Finset.sup (Finset.range (Nat.zero + 1)) f
  · simp
    -- 🎉 no goals
  · dsimp [partialSups] at ih ⊢
    -- ⊢ Nat.rec (f 0) (fun n a => a ⊔ f (n + 1)) n ⊔ f (n + 1) = Finset.sup (Finset. …
    rw [Finset.range_succ, Finset.sup_insert, sup_comm, ih]
    -- 🎉 no goals
#align partial_sups_eq_sup_range partialSups_eq_sup_range

/- Note this lemma requires a distributive lattice, so is not useful (or true) in situations such as
submodules. -/
theorem partialSups_disjoint_of_disjoint [DistribLattice α] [OrderBot α] (f : ℕ → α)
    (h : Pairwise (Disjoint on f)) {m n : ℕ} (hmn : m < n) : Disjoint (partialSups f m) (f n) := by
  induction' m with m ih
  -- ⊢ Disjoint (↑(partialSups f) Nat.zero) (f n)
  · exact h hmn.ne
    -- 🎉 no goals
  · rw [partialSups_succ, disjoint_sup_left]
    -- ⊢ Disjoint (↑(partialSups f) m) (f n) ∧ Disjoint (f (m + 1)) (f n)
    exact ⟨ih (Nat.lt_of_succ_lt hmn), h hmn.ne⟩
    -- 🎉 no goals
#align partial_sups_disjoint_of_disjoint partialSups_disjoint_of_disjoint

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α]

theorem partialSups_eq_ciSup_Iic (f : ℕ → α) (n : ℕ) : partialSups f n = ⨆ i : Set.Iic n, f i := by
  have : Set.Iio (n + 1) = Set.Iic n := Set.ext fun _ => Nat.lt_succ_iff
  -- ⊢ ↑(partialSups f) n = ⨆ (i : ↑(Set.Iic n)), f ↑i
  rw [partialSups_eq_sup'_range, Finset.sup'_eq_csSup_image, Finset.coe_range, iSup, this]
  -- ⊢ sSup (f '' Set.Iic n) = sSup (Set.range fun i => f ↑i)
  simp only [Set.range, Subtype.exists, Set.mem_Iic, exists_prop, (· '' ·)]
  -- 🎉 no goals
#align partial_sups_eq_csupr_Iic partialSups_eq_ciSup_Iic

@[simp]
theorem ciSup_partialSups_eq {f : ℕ → α} (h : BddAbove (Set.range f)) :
    ⨆ n, partialSups f n = ⨆ n, f n := by
  refine' (ciSup_le fun n => _).antisymm (ciSup_mono _ <| le_partialSups f)
  -- ⊢ ↑(partialSups f) n ≤ ⨆ (n : ℕ), f n
  · rw [partialSups_eq_ciSup_Iic]
    -- ⊢ ⨆ (i : ↑(Set.Iic n)), f ↑i ≤ ⨆ (n : ℕ), f n
    exact ciSup_le fun i => le_ciSup h _
    -- 🎉 no goals
  · rwa [bddAbove_range_partialSups]
    -- 🎉 no goals
#align csupr_partial_sups_eq ciSup_partialSups_eq

end ConditionallyCompleteLattice

section CompleteLattice

variable [CompleteLattice α]

theorem partialSups_eq_biSup (f : ℕ → α) (n : ℕ) : partialSups f n = ⨆ i ≤ n, f i := by
  simpa only [iSup_subtype] using partialSups_eq_ciSup_Iic f n
  -- 🎉 no goals
#align partial_sups_eq_bsupr partialSups_eq_biSup

-- Porting note: simp can prove this @[simp]
theorem iSup_partialSups_eq (f : ℕ → α) : ⨆ n, partialSups f n = ⨆ n, f n :=
  ciSup_partialSups_eq <| OrderTop.bddAbove _
#align supr_partial_sups_eq iSup_partialSups_eq

theorem iSup_le_iSup_of_partialSups_le_partialSups {f g : ℕ → α}
    (h : partialSups f ≤ partialSups g) : ⨆ n, f n ≤ ⨆ n, g n := by
  rw [← iSup_partialSups_eq f, ← iSup_partialSups_eq g]
  -- ⊢ ⨆ (n : ℕ), ↑(partialSups f) n ≤ ⨆ (n : ℕ), ↑(partialSups g) n
  exact iSup_mono h
  -- 🎉 no goals
#align supr_le_supr_of_partial_sups_le_partial_sups iSup_le_iSup_of_partialSups_le_partialSups

theorem iSup_eq_iSup_of_partialSups_eq_partialSups {f g : ℕ → α}
    (h : partialSups f = partialSups g) : ⨆ n, f n = ⨆ n, g n := by
  simp_rw [← iSup_partialSups_eq f, ← iSup_partialSups_eq g, h]
  -- 🎉 no goals
#align supr_eq_supr_of_partial_sups_eq_partial_sups iSup_eq_iSup_of_partialSups_eq_partialSups

end CompleteLattice
