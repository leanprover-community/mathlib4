/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Order.Interval.Finset.Nat

/-!
# The monotone sequence of partial supremums of a sequence

For `β` a preorder in which all bounded-above intervals are finite (such as `ℕ`), and `α` a
`⊔`-semilattice, we define `partialSups : (β → α) → β →o α` by the formula
`partialSups f n = (Finset.Iic n).sup' ⋯ f`, where the `⋯` denotes a proof that `Finset.Iic n` is
nonempty. This is a way of spelling `⊔ k ≤ n, f k` which does not require a `α` to have a bottom
element, and makes sense in conditionally-complete lattices (where indexed suprema over sets are
badly-behaved).

Under stronger hypotheses on `α` and `β`, we show that this coincides with other candidate
definitions, see e.g. `partialSups_eq_biSup`, `partialSups_eq_sup_range`,
and `partialSups_eq_sup'_range`.

We show this construction gives a Galois insertion between functions `β → α` and monotone functions
`β →o α`, see `partialSups.gi`.

## Notes

One might dispute whether this sequence should start at `f 0` or `⊥`. We choose the former because:
* Starting at `⊥` requires... having a bottom element.
* `fun f n ↦ (Finset.range n).sup f` is already effectively the sequence starting at `⊥`.
* If we started at `⊥` we wouldn't have the Galois insertion. See `partialSups.gi`.

-/

open Finset

variable {α β : Type*}

section SemilatticeSup

variable [SemilatticeSup α]

section Preorder

variable [Preorder β] [LocallyFiniteOrderBot β]

/-- The monotone sequence whose value at `n` is the supremum of the `f m` where `m ≤ n`. -/
def partialSups (f : β → α) : β →o α where
  toFun n := (Iic n).sup' nonempty_Iic f
  monotone' _ _ hmn := sup'_mono f (Iic_subset_Iic.mpr hmn) nonempty_Iic

lemma partialSups_apply (f : β → α) (n : β) :
    partialSups f n = (Iic n).sup' nonempty_Iic f :=
  rfl

lemma partialSups_iff_forall {f : β → α} (p : α → Prop)
    (hp : ∀ {a b}, p (a ⊔ b) ↔ p a ∧ p b) {n : β} :
    p (partialSups f n) ↔ ∀ k ≤ n, p (f k) := by
  classical
  rw [partialSups_apply, comp_sup'_eq_sup'_comp (γ := Propᵒᵈ) _ p, sup'_eq_sup]
  · show (Iic n).inf (p ∘ f) ↔ _
    simp [Finset.inf_eq_iInf]
  · intro x y
    rw [hp]
    rfl

@[simp]
lemma partialSups_le_iff {f : β → α} {n : β} {a : α} :
    partialSups f n ≤ a ↔ ∀ k ≤ n, f k ≤ a :=
  partialSups_iff_forall (· ≤ a) sup_le_iff

theorem le_partialSups_of_le (f : β → α) {m n : β} (h : m ≤ n) :
    f m ≤ partialSups f n :=
  partialSups_le_iff.1 le_rfl m h

theorem le_partialSups (f : β → α) :
    f ≤ partialSups f :=
  fun _n => le_partialSups_of_le f le_rfl

theorem partialSups_le (f : β → α) (n : β) (a : α) (w : ∀ m, m ≤ n → f m ≤ a) :
    partialSups f n ≤ a :=
  partialSups_le_iff.2 w

@[simp]
lemma upperBounds_range_partialSups (f : β → α) :
    upperBounds (Set.range (partialSups f)) = upperBounds (Set.range f) := by
  ext a
  simp only [mem_upperBounds, Set.forall_mem_range, partialSups_le_iff]
  exact ⟨fun h _ ↦ h _ _ le_rfl, fun h _ _ _ ↦ h _⟩

@[simp]
theorem bddAbove_range_partialSups {f : β → α} :
    BddAbove (Set.range (partialSups f)) ↔ BddAbove (Set.range f) :=
  .of_eq <| congr_arg Set.Nonempty <| upperBounds_range_partialSups f

theorem Monotone.partialSups_eq {f : β → α} (hf : Monotone f) :
    partialSups f = f :=
  funext fun n ↦ le_antisymm (partialSups_le _ _ _ (@hf · n)) (le_partialSups _ _)

theorem partialSups_mono :
    Monotone (partialSups : (β → α) → β →o α) :=
  fun _f _g h _n ↦ partialSups_le_iff.2 fun k hk ↦ (h k).trans (le_partialSups_of_le _ hk)

lemma partialSups_monotone (f : β → α) :
    Monotone (partialSups f) :=
  fun n _ hnm ↦ partialSups_le f n _ (fun _ hm'n ↦ le_partialSups_of_le _ (hm'n.trans hnm))

/--
`partialSups` forms a Galois insertion with the coercion from monotone functions to functions.
-/
def partialSups.gi :
    GaloisInsertion (partialSups : (β → α) → β →o α) (↑) where
  choice f h :=
    ⟨f, by convert (partialSups f).monotone using 1; exact (le_partialSups f).antisymm h⟩
  gc f g := by
    refine ⟨(le_partialSups f).trans, fun h => ?_⟩
    convert partialSups_mono h
    exact OrderHom.ext _ _ g.monotone.partialSups_eq.symm
  le_l_u f := le_partialSups f
  choice_eq f h := OrderHom.ext _ _ ((le_partialSups f).antisymm h)

protected lemma Pi.partialSups_apply {ι : Type*} {π : ι → Type*} [(i : ι) → SemilatticeSup (π i)]
    (f : β → (i : ι) → π i) (n : β) (i : ι) :
    partialSups f n i = partialSups (f · i) n := by
  simp only [partialSups_apply, Finset.sup'_apply]

end Preorder

@[simp]
theorem partialSups_succ [LinearOrder β] [LocallyFiniteOrderBot β] [SuccOrder β]
    (f : β → α) (n : β) :
    partialSups f (Order.succ n) = partialSups f n ⊔ f (Order.succ n) := by
  suffices Iic (Order.succ n) = Iic n ∪ {Order.succ n} by simp only [partialSups_apply, this,
    sup'_union nonempty_Iic ⟨_, mem_singleton_self _⟩ f, sup'_singleton]
  ext m
  simp only [mem_Iic, mem_union, mem_singleton]
  constructor
  · exact fun h ↦ (Order.le_succ_iff_eq_or_le.mp h).symm
  · exact fun h ↦ h.elim (le_trans · <| Order.le_succ _) le_of_eq

@[simp]
lemma partialSups_add_one [Add β] [One β] [LinearOrder β] [LocallyFiniteOrderBot β] [SuccAddOrder β]
    (f : β → α) (n : β) : partialSups f (n + 1) = partialSups f n ⊔ f (n + 1) :=
  Order.succ_eq_add_one n ▸ partialSups_succ f n

@[simp]
theorem partialSups_bot [PartialOrder β] [LocallyFiniteOrder β] [OrderBot β]
    (f : β → α) : partialSups f ⊥ = f ⊥ := by
  simp only [partialSups_apply]
  -- should we add a lemma `Finset.Iic_bot`?
  suffices Iic (⊥ : β) = {⊥} by simp only [this, sup'_singleton]
  simp only [← coe_eq_singleton, coe_Iic, Set.Iic_bot]

/-!
### Functions out of `ℕ`
-/

@[simp]
theorem partialSups_zero (f : ℕ → α) : partialSups f 0 = f 0 :=
  partialSups_bot f

theorem partialSups_eq_sup'_range (f : ℕ → α) (n : ℕ) :
    partialSups f n = (Finset.range (n + 1)).sup' nonempty_range_succ f :=
  eq_of_forall_ge_iff fun _ ↦ by simp [Nat.lt_succ_iff]

theorem partialSups_eq_sup_range [OrderBot α] (f : ℕ → α) (n : ℕ) :
    partialSups f n = (Finset.range (n + 1)).sup f :=
  eq_of_forall_ge_iff fun _ ↦ by simp [Nat.lt_succ_iff]

end SemilatticeSup

section DistribLattice

/-!
### Functions valued in a distributive lattice

These lemmas require the target to be a distributive lattice, so they are not useful (or true) in
situations such as submodules.
-/

variable [Preorder β] [LocallyFiniteOrderBot β] [DistribLattice α] [OrderBot α]

@[simp]
lemma disjoint_partialSups_left {f : β → α} {n : β} {x : α} :
    Disjoint (partialSups f n) x ↔ ∀ k ≤ n, Disjoint (f k) x :=
  partialSups_iff_forall (Disjoint · x) disjoint_sup_left

@[simp]
lemma disjoint_partialSups_right {f : β → α} {n : β} {x : α} :
    Disjoint x (partialSups f n) ↔ ∀ k ≤ n, Disjoint x (f k) :=
  partialSups_iff_forall (Disjoint x) disjoint_sup_right

open scoped Function in -- required for scoped `on` notation
/- Note this lemma requires a distributive lattice, so is not useful (or true) in situations such as
submodules. -/
theorem partialSups_disjoint_of_disjoint (f : β → α) (h : Pairwise (Disjoint on f))
    {m n : β} (hmn : m < n) :
    Disjoint (partialSups f m) (f n) :=
  disjoint_partialSups_left.2 fun _k hk ↦ h <| (hk.trans_lt hmn).ne

end DistribLattice

section ConditionallyCompleteLattice

/-!
### Lemmas about the supremum over the whole domain

These lemmas require some completeness assumptions on the target space.
-/
variable [Preorder β] [LocallyFiniteOrderBot β]

theorem partialSups_eq_ciSup_Iic [ConditionallyCompleteLattice α] (f : β → α) (n : β) :
    partialSups f n = ⨆ i : Set.Iic n, f i := by
  simp only [partialSups_apply]
  apply le_antisymm
  · exact sup'_le _ _ fun b hb ↦ le_ciSup_of_le (Set.finite_range _).bddAbove
      ⟨b, by simpa only [Set.mem_Iic, mem_Iic] using hb⟩ le_rfl
  · exact ciSup_le fun ⟨b, hb⟩ ↦ le_sup' f (by simpa only [mem_Iic, Set.mem_Iic] using hb)

@[simp]
theorem ciSup_partialSups_eq [ConditionallyCompleteLattice α]
    {f : β → α} (h : BddAbove (Set.range f)) :
    ⨆ n, partialSups f n = ⨆ n, f n := by
  by_cases hβ : Nonempty β
  · refine (ciSup_le fun n ↦ ?_).antisymm (ciSup_mono ?_ <| le_partialSups f)
    · simpa only [partialSups_eq_ciSup_Iic] using ciSup_le fun i ↦ le_ciSup h _
    · rwa [bddAbove_range_partialSups]
  · exact congr_arg _ (funext (not_nonempty_iff.mp hβ).elim)

/-- Version of `ciSup_partialSups_eq` without boundedness assumptions, but requiring a
`ConditionallyCompleteLinearOrder` rather than just a `ConditionallyCompleteLattice`. -/
@[simp]
theorem ciSup_partialSups_eq' [ConditionallyCompleteLinearOrder α] (f : β → α) :
    ⨆ n, partialSups f n = ⨆ n, f n := by
  by_cases h : BddAbove (Set.range f)
  · exact ciSup_partialSups_eq h
  · rw [iSup, iSup, ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove _ h,
      ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove _
        (bddAbove_range_partialSups.not.mpr h)]

end ConditionallyCompleteLattice

section CompleteLattice

variable [Preorder β] [LocallyFiniteOrderBot β] [CompleteLattice α]

/-- Version of `ciSup_partialSups_eq` without boundedness assumptions, but requiring a
`CompleteLattice` rather than just a `ConditionallyCompleteLattice`. -/
theorem iSup_partialSups_eq (f : β → α) :
    ⨆ n, partialSups f n = ⨆ n, f n :=
  ciSup_partialSups_eq <| OrderTop.bddAbove _

theorem partialSups_eq_biSup (f : β → α) (n : β) :
    partialSups f n = ⨆ i ≤ n, f i := by
  simpa only [iSup_subtype] using partialSups_eq_ciSup_Iic f n

theorem iSup_le_iSup_of_partialSups_le_partialSups {f g : β → α}
    (h : partialSups f ≤ partialSups g) : ⨆ n, f n ≤ ⨆ n, g n := by
  rw [← iSup_partialSups_eq f, ← iSup_partialSups_eq g]
  exact iSup_mono h

theorem iSup_eq_iSup_of_partialSups_eq_partialSups {f g : β → α}
    (h : partialSups f = partialSups g) : ⨆ n, f n = ⨆ n, g n := by
  simp_rw [← iSup_partialSups_eq f, ← iSup_partialSups_eq g, h]

end CompleteLattice

section Set
/-!
### Functions into `Set α`
-/

lemma partialSups_eq_sUnion_image [DecidableEq (Set α)] (s : ℕ → Set α) (n : ℕ) :
    partialSups s n = ⋃₀ ↑((Finset.range (n + 1)).image s) := by
  ext; simp [partialSups_eq_biSup, Nat.lt_succ_iff]

lemma partialSups_eq_biUnion_range (s : ℕ → Set α) (n : ℕ) :
    partialSups s n = ⋃ i ∈ Finset.range (n + 1), s i := by
  ext; simp [partialSups_eq_biSup, Nat.lt_succ]

end Set
