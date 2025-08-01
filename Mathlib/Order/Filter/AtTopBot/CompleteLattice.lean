/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Order.Filter.AtTopBot.Tendsto

/-!
# `Filter.atTop` and `Filter.atBot` in (conditionally) complete lattices
-/

assert_not_exists Finset

variable {ι ι' α β γ : Type*}

open Set

namespace Filter

@[nontriviality]
theorem Subsingleton.atTop_eq (α) [Subsingleton α] [Preorder α] : (atTop : Filter α) = ⊤ := by
  refine top_unique fun s hs x => ?_
  rw [atTop, ciInf_subsingleton x, mem_principal] at hs
  exact hs left_mem_Ici

@[nontriviality]
theorem Subsingleton.atBot_eq (α) [Subsingleton α] [Preorder α] : (atBot : Filter α) = ⊤ :=
  @Subsingleton.atTop_eq αᵒᵈ _ _

/-- If `f` is a monotone function with bounded range
and `g` tends to `atTop` along a nontrivial filter,
then the indexed supremum of `f ∘ g` is equal to the indexed supremum of `f`.

The assumption `BddAbove (range f)` can be omitted,
if the codomain of `f` is a conditionally complete linear order or a complete lattice, see below.
-/
theorem _root_.Monotone.ciSup_comp_tendsto_atTop [Preorder β] [ConditionallyCompleteLattice γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Monotone f) (hb : BddAbove (range f))
    {g : α → β} (hg : Tendsto g l atTop) : ⨆ a, f (g a) = ⨆ b, f b := by
  have : Nonempty α := nonempty_of_neBot l
  have : Nonempty β := .map g ‹_›
  rw [← csInf_upperBounds_range, ← csInf_upperBounds_range,
    ← hf.upperBounds_range_comp_tendsto_atTop hg, Function.comp_def]
  exacts [hb, hb.mono <| range_comp_subset_range _ _]

/-- If `f` is a monotone function with bounded range
and `g` tends to `atBot` along a nontrivial filter,
then the indexed infimum of `f ∘ g` is equal to the indexed infimum of `f`.

The assumption `BddBelow (range f)` can be omitted,
if the codomain of `f` is a conditionally complete linear order or a complete lattice, see below.
-/
theorem _root_.Monotone.ciInf_comp_tendsto_atBot [Preorder β] [ConditionallyCompleteLattice γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Monotone f) (hb : BddBelow (range f))
    {g : α → β} (hg : Tendsto g l atBot) : ⨅ a, f (g a) = ⨅ b, f b :=
  hf.dual.ciSup_comp_tendsto_atTop hb hg

/-- If `f` is an antitone function with bounded range
and `g` tends to `atBot` along a nontrivial filter,
then the indexed supremum of `f ∘ g` is equal to the indexed supremum of `f`.

The assumption `BddAbove (range f)` can be omitted,
if the codomain of `f` is a conditionally complete linear order or a complete lattice, see below.
-/
theorem _root_.Antitone.ciSup_comp_tendsto_atBot [Preorder β] [ConditionallyCompleteLattice γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Antitone f) (hb : BddAbove (range f))
    {g : α → β} (hg : Tendsto g l atBot) : ⨆ a, f (g a) = ⨆ b, f b :=
  hf.dual_left.ciSup_comp_tendsto_atTop hb hg

/-- If `f` is an antitone function with bounded range
and `g` tends to `atTop` along a nontrivial filter,
then the indexed infimum of `f ∘ g` is equal to the indexed infimum of `f`.

The assumption `BddBelow (range f)` can be omitted,
if the codomain of `f` is a conditionally complete linear order or a complete lattice, see below.
-/
theorem _root_.Antitone.ciInf_comp_tendsto_atTop [Preorder β] [ConditionallyCompleteLattice γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Antitone f) (hb : BddBelow (range f))
    {g : α → β} (hg : Tendsto g l atTop) : ⨅ a, f (g a) = ⨅ b, f b :=
  hf.dual.ciSup_comp_tendsto_atBot hb hg

/-- If `f` is a monotone function taking values in a conditionally complete linear order
and `g` tends to `atTop` along a nontrivial filter,
then the indexed supremum of `f ∘ g` is equal to the indexed supremum of `f`. -/
theorem _root_.Monotone.ciSup_comp_tendsto_atTop_of_linearOrder [Preorder β]
    [ConditionallyCompleteLinearOrder γ] {l : Filter α} [l.NeBot] {f : β → γ} (hf : Monotone f)
    {g : α → β} (hg : Tendsto g l atTop) : ⨆ a, f (g a) = ⨆ b, f b := by
  if hb : BddAbove (range f) then
    exact hf.ciSup_comp_tendsto_atTop hb hg
  else
    rw [iSup, iSup, csSup_of_not_bddAbove, csSup_of_not_bddAbove hb]
    rwa [BddAbove, ← Function.comp_def f g, hf.upperBounds_range_comp_tendsto_atTop hg]

/-- If `f` is a monotone function taking values in a conditionally complete linear order
and `g` tends to `atBot` along a nontrivial filter,
then the indexed infimum of `f ∘ g` is equal to the indexed infimum of `f`. -/
theorem _root_.Monotone.ciInf_comp_tendsto_atBot_of_linearOrder [Preorder β]
    [ConditionallyCompleteLinearOrder γ] {l : Filter α} [l.NeBot] {f : β → γ} (hf : Monotone f)
    {g : α → β} (hg : Tendsto g l atBot) : ⨅ a, f (g a) = ⨅ b, f b :=
  hf.dual.ciSup_comp_tendsto_atTop_of_linearOrder hg

/-- If `f` is an antitone function taking values in a conditionally complete linear order
and `g` tends to `atTop` along a nontrivial filter,
then the indexed infimum of `f ∘ g` is equal to the indexed infimum of `f`. -/
theorem _root_.Antitone.ciInf_comp_tendsto_atTop_of_linearOrder [Preorder β]
    [ConditionallyCompleteLinearOrder γ] {l : Filter α} [l.NeBot] {f : β → γ} (hf : Antitone f)
    {g : α → β} (hg : Tendsto g l atTop) : ⨅ a, f (g a) = ⨅ b, f b :=
  hf.dual_left.ciInf_comp_tendsto_atBot_of_linearOrder hg

/-- If `f` is an antitone function taking values in a conditionally complete linear order
and `g` tends to `atBot` along a nontrivial filter,
then the indexed supremum of `f ∘ g` is equal to the indexed supremum of `f`. -/
theorem _root_.Antitone.ciSup_comp_tendsto_atBot_of_linearOrder [Preorder β]
    [ConditionallyCompleteLinearOrder γ] {l : Filter α} [l.NeBot] {f : β → γ} (hf : Antitone f)
    {g : α → β} (hg : Tendsto g l atBot) : ⨆ a, f (g a) = ⨆ b, f b :=
  hf.dual_left.ciSup_comp_tendsto_atTop_of_linearOrder hg

/-- If `f` is a monotone function taking values in a complete lattice
and `g` tends to `atTop` along a nontrivial filter,
then the indexed supremum of `f ∘ g` is equal to the indexed supremum of `f`. -/
theorem _root_.Monotone.iSup_comp_tendsto_atTop
    [Preorder β] [ConditionallyCompleteLattice γ] [OrderTop γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Monotone f) {g : α → β} (hg : Tendsto g l atTop) :
    ⨆ a, f (g a) = ⨆ b, f b :=
  hf.ciSup_comp_tendsto_atTop (OrderTop.bddAbove _) hg

/-- If `f` is a monotone function taking values in a complete lattice
and `g` tends to `atBot` along a nontrivial filter,
then the indexed infimum of `f ∘ g` is equal to the indexed infimum of `f`. -/
theorem _root_.Monotone.iInf_comp_tendsto_atBot
    [Preorder β] [ConditionallyCompleteLattice γ] [OrderBot γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Monotone f) {g : α → β} (hg : Tendsto g l atBot) :
    ⨅ a, f (g a) = ⨅ b, f b :=
  hf.ciInf_comp_tendsto_atBot (OrderBot.bddBelow _) hg

/-- If `f` is an antitone function taking values in a complete lattice
and `g` tends to `atBot` along a nontrivial filter,
then the indexed supremum of `f ∘ g` is equal to the indexed supremum of `f`. -/
theorem _root_.Antitone.iSup_comp_tendsto_atBot
    [Preorder β] [ConditionallyCompleteLattice γ] [OrderTop γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Antitone f) {g : α → β} (hg : Tendsto g l atBot) :
    ⨆ a, f (g a) = ⨆ b, f b :=
  hf.ciSup_comp_tendsto_atBot (OrderTop.bddAbove _) hg

/-- If `f` is an antitone function taking values in a complete lattice
and `g` tends to `atTop` along a nontrivial filter,
then the indexed infimum of `f ∘ g` is equal to the indexed infimum of `f`. -/
theorem _root_.Antitone.iInf_comp_tendsto_atTop
    [Preorder β] [ConditionallyCompleteLattice γ] [OrderBot γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Antitone f) {g : α → β} (hg : Tendsto g l atTop) :
    ⨅ a, f (g a) = ⨅ b, f b :=
  hf.ciInf_comp_tendsto_atTop (OrderBot.bddBelow _) hg

/-- If `s` is a monotone family of sets and `f` tends to `atTop` along a nontrivial filter,
then the indexed union of `s ∘ f` is equal to the indexed union of `s`. -/
theorem _root_.Monotone.iUnion_comp_tendsto_atTop [Preorder β] {l : Filter α} [l.NeBot]
    {s : β → Set γ} (hs : Monotone s) {f : α → β} (hf : Tendsto f l atTop) :
    ⋃ a, s (f a) = ⋃ b, s b :=
  hs.iSup_comp_tendsto_atTop hf

/-- If `s` is a monotone family of sets and `f` tends to `atBot` along a nontrivial filter,
then the indexed intersection of `s ∘ f` is equal to the indexed intersection of `s`. -/
theorem _root_.Monotone.iInter_comp_tendsto_atBot [Preorder β] {l : Filter α} [l.NeBot]
    {s : β → Set γ} (hs : Monotone s) {f : α → β} (hf : Tendsto f l atBot) :
    ⋂ a, s (f a) = ⋂ b, s b :=
  hs.iInf_comp_tendsto_atBot hf

/-- If `s` is an antitone family of sets and `f` tends to `atTop` along a nontrivial filter,
then the indexed intersection of `s ∘ f` is equal to the indexed intersection of `s`. -/
theorem _root_.Antitone.iInter_comp_tendsto_atTop [Preorder β] {l : Filter α} [l.NeBot]
    {s : β → Set γ} (hs : Antitone s) {f : α → β} (hf : Tendsto f l atTop) :
    ⋂ a, s (f a) = ⋂ b, s b :=
  hs.iInf_comp_tendsto_atTop hf

/-- If `s` is a monotone family of sets and `f` tends to `atBot` along a nontrivial filter,
then the indexed union of `s ∘ f` is equal to the indexed union of `s`. -/
theorem _root_.Antitone.iUnion_comp_tendsto_atBot [Preorder β] {l : Filter α} [l.NeBot]
    {s : β → Set γ} (hs : Antitone s) {f : α → β} (hf : Tendsto f l atBot) :
    ⋃ a, s (f a) = ⋃ b, s b :=
  hs.iSup_comp_tendsto_atBot hf

end Filter
