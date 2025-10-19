/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.SuccPred.Basic

/-!
# The monotone sequence of partial supremums of a sequence

For `ι` a preorder in which all bounded-above intervals are finite (such as `ℕ`), and `α` a
`⊔`-semilattice, we define `partialSups : (ι → α) → ι →o α` by the formula
`partialSups f i = (Finset.Iic i).sup' ⋯ f`, where the `⋯` denotes a proof that `Finset.Iic i` is
nonempty. This is a way of spelling `⊔ k ≤ i, f k` which does not require a `α` to have a bottom
element, and makes sense in conditionally-complete lattices (where indexed suprema over sets are
badly-behaved).

Under stronger hypotheses on `α` and `ι`, we show that this coincides with other candidate
definitions, see e.g. `partialSups_eq_biSup`, `partialSups_eq_sup_range`,
and `partialSups_eq_sup'_range`.

We show this construction gives a Galois insertion between functions `ι → α` and monotone functions
`ι →o α`, see `partialSups.gi`.

## Notes

One might dispute whether this sequence should start at `f 0` or `⊥`. We choose the former because:
* Starting at `⊥` requires... having a bottom element.
* `fun f i ↦ (Finset.Iio i).sup f` is already effectively the sequence starting at `⊥`.
* If we started at `⊥` we wouldn't have the Galois insertion. See `partialSups.gi`.

-/

open Finset

variable {α β ι : Type*}

section SemilatticeSup

variable [SemilatticeSup α] [SemilatticeSup β]

section Preorder

variable [Preorder ι] [LocallyFiniteOrderBot ι]

/-- The monotone sequence whose value at `i` is the supremum of the `f j` where `j ≤ i`. -/
def partialSups (f : ι → α) : ι →o α where
  toFun i := (Iic i).sup' nonempty_Iic f
  monotone' _ _ hmn := sup'_mono f (Iic_subset_Iic.mpr hmn) nonempty_Iic

lemma partialSups_apply (f : ι → α) (i : ι) :
    partialSups f i = (Iic i).sup' nonempty_Iic f :=
  rfl

lemma partialSups_iff_forall {f : ι → α} (p : α → Prop)
    (hp : ∀ {a b}, p (a ⊔ b) ↔ p a ∧ p b) {i : ι} :
    p (partialSups f i) ↔ ∀ j ≤ i, p (f j) := by
  classical
  rw [partialSups_apply, comp_sup'_eq_sup'_comp (γ := Propᵒᵈ) _ p, sup'_eq_sup]
  · change (Iic i).inf (p ∘ f) ↔ _
    simp [Finset.inf_eq_iInf]
  · intro x y
    rw [hp]
    rfl

@[simp]
lemma partialSups_le_iff {f : ι → α} {i : ι} {a : α} :
    partialSups f i ≤ a ↔ ∀ j ≤ i, f j ≤ a :=
  partialSups_iff_forall (· ≤ a) sup_le_iff

theorem le_partialSups_of_le (f : ι → α) {i j : ι} (h : i ≤ j) :
    f i ≤ partialSups f j :=
  partialSups_le_iff.1 le_rfl i h

theorem le_partialSups (f : ι → α) :
    f ≤ partialSups f :=
  fun _ => le_partialSups_of_le f le_rfl

theorem partialSups_le (f : ι → α) (i : ι) (a : α) (w : ∀ j ≤ i, f j ≤ a) :
    partialSups f i ≤ a :=
  partialSups_le_iff.2 w

@[simp]
lemma upperBounds_range_partialSups (f : ι → α) :
    upperBounds (Set.range (partialSups f)) = upperBounds (Set.range f) := by
  ext a
  simp only [mem_upperBounds, Set.forall_mem_range, partialSups_le_iff]
  exact ⟨fun h _ ↦ h _ _ le_rfl, fun h _ _ _ ↦ h _⟩

@[simp]
theorem bddAbove_range_partialSups {f : ι → α} :
    BddAbove (Set.range (partialSups f)) ↔ BddAbove (Set.range f) :=
  .of_eq <| congr_arg Set.Nonempty <| upperBounds_range_partialSups f

theorem Monotone.partialSups_eq {f : ι → α} (hf : Monotone f) :
    partialSups f = f :=
  funext fun i ↦ le_antisymm (partialSups_le _ _ _ (@hf · i)) (le_partialSups _ _)

theorem partialSups_mono :
    Monotone (partialSups : (ι → α) → ι →o α) :=
  fun _ _ h _ ↦ partialSups_le_iff.2 fun j hj ↦ (h j).trans (le_partialSups_of_le _ hj)

lemma partialSups_monotone (f : ι → α) :
    Monotone (partialSups f) :=
  fun i _ hnm ↦ partialSups_le f i _ (fun _ hm'n ↦ le_partialSups_of_le _ (hm'n.trans hnm))

/-- `partialSups` forms a Galois insertion with the coercion from monotone functions to functions.
-/
def partialSups.gi :
    GaloisInsertion (partialSups : (ι → α) → ι →o α) (↑) where
  choice f h :=
    ⟨f, by convert (partialSups f).monotone using 1; exact (le_partialSups f).antisymm h⟩
  gc f g := by
    refine ⟨(le_partialSups f).trans, fun h ↦ ?_⟩
    convert partialSups_mono h
    exact OrderHom.ext _ _ g.monotone.partialSups_eq.symm
  le_l_u f := le_partialSups f
  choice_eq f h := OrderHom.ext _ _ ((le_partialSups f).antisymm h)

protected lemma Pi.partialSups_apply {τ : Type*} {π : τ → Type*} [∀ t, SemilatticeSup (π t)]
    (f : ι → (t : τ) → π t) (i : ι) (t : τ) :
    partialSups f i t = partialSups (f · t) i := by
  simp only [partialSups_apply, Finset.sup'_apply]

lemma comp_partialSups {F : Type*} [FunLike F α β] [SupHomClass F α β] (f : ι → α) (g : F) :
    partialSups (g ∘ f) = g ∘ partialSups f := by
  funext _; simp [partialSups]

lemma map_partialSups {F : Type*} [FunLike F α β] [SupHomClass F α β] (f : F) (g : ι → α) (i : ι) :
    partialSups (fun j ↦ f (g j)) i = f (partialSups g i) := congr($(comp_partialSups ..) i)

end Preorder

@[simp]
theorem partialSups_succ [LinearOrder ι] [LocallyFiniteOrderBot ι] [SuccOrder ι]
    (f : ι → α) (i : ι) :
    partialSups f (Order.succ i) = partialSups f i ⊔ f (Order.succ i) := by
  suffices Iic (Order.succ i) = Iic i ∪ {Order.succ i} by simp only [partialSups_apply, this,
    sup'_union nonempty_Iic ⟨_, mem_singleton_self _⟩ f, sup'_singleton]
  ext
  simp only [mem_Iic, mem_union, mem_singleton]
  constructor
  · exact fun h ↦ (Order.le_succ_iff_eq_or_le.mp h).symm
  · exact fun h ↦ h.elim (le_trans · <| Order.le_succ _) le_of_eq

@[simp]
theorem partialSups_bot [PartialOrder ι] [LocallyFiniteOrder ι] [OrderBot ι]
    (f : ι → α) : partialSups f ⊥ = f ⊥ := by
  simp only [partialSups_apply]
  -- should we add a lemma `Finset.Iic_bot`?
  suffices Iic (⊥ : ι) = {⊥} by simp only [this, sup'_singleton]
  simp only [← coe_eq_singleton, coe_Iic, Set.Iic_bot]

/-!
### Functions out of `ℕ`
-/

@[simp]
theorem partialSups_zero (f : ℕ → α) : partialSups f 0 = f 0 :=
  partialSups_bot f

theorem partialSups_eq_sup'_range (f : ℕ → α) (n : ℕ) :
    partialSups f n = (Finset.range (n + 1)).sup' nonempty_range_add_one f :=
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

variable [Preorder ι] [LocallyFiniteOrderBot ι] [DistribLattice α] [OrderBot α]

@[simp]
lemma disjoint_partialSups_left {f : ι → α} {i : ι} {x : α} :
    Disjoint (partialSups f i) x ↔ ∀ j ≤ i, Disjoint (f j) x :=
  partialSups_iff_forall (Disjoint · x) disjoint_sup_left

@[simp]
lemma disjoint_partialSups_right {f : ι → α} {i : ι} {x : α} :
    Disjoint x (partialSups f i) ↔ ∀ j ≤ i, Disjoint x (f j) :=
  partialSups_iff_forall (Disjoint x) disjoint_sup_right

open scoped Function in -- required for scoped `on` notation
/- Note this lemma requires a distributive lattice, so is not useful (or true) in situations such as
submodules. -/
theorem partialSups_disjoint_of_disjoint (f : ι → α) (h : Pairwise (Disjoint on f))
    {i j : ι} (hij : i < j) :
    Disjoint (partialSups f i) (f j) :=
  disjoint_partialSups_left.2 fun _ hk ↦ h (hk.trans_lt hij).ne

end DistribLattice

section ConditionallyCompleteLattice

/-!
### Lemmas about the supremum over the whole domain

These lemmas require some completeness assumptions on the target space.
-/
variable [Preorder ι] [LocallyFiniteOrderBot ι]

theorem partialSups_eq_ciSup_Iic [ConditionallyCompleteLattice α] (f : ι → α) (i : ι) :
    partialSups f i = ⨆ i : Set.Iic i, f i := by
  simp only [partialSups_apply]
  apply le_antisymm
  · exact sup'_le _ _ fun j hj ↦ le_ciSup_of_le (Set.finite_range _).bddAbove
      ⟨j, by simpa only [Set.mem_Iic, mem_Iic] using hj⟩ le_rfl
  · exact ciSup_le fun ⟨j, hj⟩ ↦ le_sup' f (by simpa only [mem_Iic, Set.mem_Iic] using hj)

@[simp]
theorem ciSup_partialSups_eq [ConditionallyCompleteLattice α]
    {f : ι → α} (h : BddAbove (Set.range f)) :
    ⨆ i, partialSups f i = ⨆ i, f i := by
  by_cases hι : Nonempty ι
  · refine (ciSup_le fun i ↦ ?_).antisymm (ciSup_mono ?_ <| le_partialSups f)
    · simpa only [partialSups_eq_ciSup_Iic] using ciSup_le fun i ↦ le_ciSup h _
    · rwa [bddAbove_range_partialSups]
  · exact congr_arg _ (funext (not_nonempty_iff.mp hι).elim)

/-- Version of `ciSup_partialSups_eq` without boundedness assumptions, but requiring a
`ConditionallyCompleteLinearOrder` rather than just a `ConditionallyCompleteLattice`. -/
@[simp]
theorem ciSup_partialSups_eq' [ConditionallyCompleteLinearOrder α] (f : ι → α) :
    ⨆ i, partialSups f i = ⨆ i, f i := by
  by_cases h : BddAbove (Set.range f)
  · exact ciSup_partialSups_eq h
  · rw [iSup, iSup, ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove _ h,
      ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove _
        (bddAbove_range_partialSups.not.mpr h)]

end ConditionallyCompleteLattice

section CompleteLattice

variable [Preorder ι] [LocallyFiniteOrderBot ι] [CompleteLattice α]

/-- Version of `ciSup_partialSups_eq` without boundedness assumptions, but requiring a
`CompleteLattice` rather than just a `ConditionallyCompleteLattice`. -/
theorem iSup_partialSups_eq (f : ι → α) :
    ⨆ i, partialSups f i = ⨆ i, f i :=
  ciSup_partialSups_eq <| OrderTop.bddAbove _

theorem partialSups_eq_biSup (f : ι → α) (i : ι) :
    partialSups f i = ⨆ j ≤ i, f j := by
  simpa only [iSup_subtype] using partialSups_eq_ciSup_Iic f i

theorem iSup_le_iSup_of_partialSups_le_partialSups {f g : ι → α}
    (h : partialSups f ≤ partialSups g) : ⨆ i, f i ≤ ⨆ i, g i := by
  rw [← iSup_partialSups_eq f, ← iSup_partialSups_eq g]
  exact iSup_mono h

theorem iSup_eq_iSup_of_partialSups_eq_partialSups {f g : ι → α}
    (h : partialSups f = partialSups g) : ⨆ i, f i = ⨆ i, g i := by
  simp_rw [← iSup_partialSups_eq f, ← iSup_partialSups_eq g, h]

end CompleteLattice

section Set
/-!
### Functions into `Set α`
-/

lemma partialSups_eq_sUnion_image [DecidableEq (Set α)] (s : ℕ → Set α) (n : ℕ) :
    partialSups s n = ⋃₀ ↑((Finset.range (n + 1)).image s) := by
  simp [partialSups_eq_biSup, Nat.lt_succ_iff]

lemma partialSups_eq_biUnion_range (s : ℕ → Set α) (n : ℕ) :
    partialSups s n = ⋃ i ∈ Finset.range (n + 1), s i := by
  simp [partialSups_eq_biSup, Nat.lt_succ]

end Set
