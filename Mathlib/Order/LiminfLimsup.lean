/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Johannes Hölzl, Rémy Degenne
-/
import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Hom.CompleteLattice

#align_import order.liminf_limsup from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"

/-!
# liminfs and limsups of functions and filters

Defines the liminf/limsup of a function taking values in a conditionally complete lattice, with
respect to an arbitrary filter.

We define `limsSup f` (`limsInf f`) where `f` is a filter taking values in a conditionally complete
lattice. `limsSup f` is the smallest element `a` such that, eventually, `u ≤ a` (and vice versa for
`limsInf f`). To work with the Limsup along a function `u` use `limsSup (map u f)`.

Usually, one defines the Limsup as `inf (sup s)` where the Inf is taken over all sets in the filter.
For instance, in ℕ along a function `u`, this is `inf_n (sup_{k ≥ n} u k)` (and the latter quantity
decreases with `n`, so this is in fact a limit.). There is however a difficulty: it is well possible
that `u` is not bounded on the whole space, only eventually (think of `limsup (fun x ↦ 1/x)` on ℝ.
Then there is no guarantee that the quantity above really decreases (the value of the `sup`
beforehand is not really well defined, as one can not use ∞), so that the Inf could be anything.
So one can not use this `inf sup ...` definition in conditionally complete lattices, and one has
to use a less tractable definition.

In conditionally complete lattices, the definition is only useful for filters which are eventually
bounded above (otherwise, the Limsup would morally be +∞, which does not belong to the space) and
which are frequently bounded below (otherwise, the Limsup would morally be -∞, which is not in the
space either). We start with definitions of these concepts for arbitrary filters, before turning to
the definitions of Limsup and Liminf.

In complete lattices, however, it coincides with the `Inf Sup` definition.
-/

set_option autoImplicit true


open Filter Set Function

variable {α β γ ι : Type*}

namespace Filter

section Relation

/-- `f.IsBounded (≺)`: the filter `f` is eventually bounded w.r.t. the relation `≺`, i.e.
eventually, it is bounded by some uniform bound.
`r` will be usually instantiated with `≤` or `≥`. -/
def IsBounded (r : α → α → Prop) (f : Filter α) :=
  ∃ b, ∀ᶠ x in f, r x b
#align filter.is_bounded Filter.IsBounded

/-- `f.IsBoundedUnder (≺) u`: the image of the filter `f` under `u` is eventually bounded w.r.t.
the relation `≺`, i.e. eventually, it is bounded by some uniform bound. -/
def IsBoundedUnder (r : α → α → Prop) (f : Filter β) (u : β → α) :=
  (map u f).IsBounded r
#align filter.is_bounded_under Filter.IsBoundedUnder

variable {r : α → α → Prop} {f g : Filter α}

/-- `f` is eventually bounded if and only if, there exists an admissible set on which it is
bounded. -/
theorem isBounded_iff : f.IsBounded r ↔ ∃ s ∈ f.sets, ∃ b, s ⊆ { x | r x b } :=
  Iff.intro (fun ⟨b, hb⟩ => ⟨{ a | r a b }, hb, b, Subset.refl _⟩) fun ⟨_, hs, b, hb⟩ =>
    ⟨b, mem_of_superset hs hb⟩
#align filter.is_bounded_iff Filter.isBounded_iff

/-- A bounded function `u` is in particular eventually bounded. -/
theorem isBoundedUnder_of {f : Filter β} {u : β → α} : (∃ b, ∀ x, r (u x) b) → f.IsBoundedUnder r u
  | ⟨b, hb⟩ => ⟨b, show ∀ᶠ x in f, r (u x) b from eventually_of_forall hb⟩
#align filter.is_bounded_under_of Filter.isBoundedUnder_of

theorem isBounded_bot : IsBounded r ⊥ ↔ Nonempty α := by simp [IsBounded, exists_true_iff_nonempty]
                                                         -- 🎉 no goals
#align filter.is_bounded_bot Filter.isBounded_bot

theorem isBounded_top : IsBounded r ⊤ ↔ ∃ t, ∀ x, r x t := by simp [IsBounded, eq_univ_iff_forall]
                                                              -- 🎉 no goals
#align filter.is_bounded_top Filter.isBounded_top

theorem isBounded_principal (s : Set α) : IsBounded r (𝓟 s) ↔ ∃ t, ∀ x ∈ s, r x t := by
  simp [IsBounded, subset_def]
  -- 🎉 no goals
#align filter.is_bounded_principal Filter.isBounded_principal

theorem isBounded_sup [IsTrans α r] [IsDirected α r] :
    IsBounded r f → IsBounded r g → IsBounded r (f ⊔ g)
  | ⟨b₁, h₁⟩, ⟨b₂, h₂⟩ =>
    let ⟨b, rb₁b, rb₂b⟩ := directed_of r b₁ b₂
    ⟨b, eventually_sup.mpr
      ⟨h₁.mono fun _ h => _root_.trans h rb₁b, h₂.mono fun _ h => _root_.trans h rb₂b⟩⟩
#align filter.is_bounded_sup Filter.isBounded_sup

theorem IsBounded.mono (h : f ≤ g) : IsBounded r g → IsBounded r f
  | ⟨b, hb⟩ => ⟨b, h hb⟩
#align filter.is_bounded.mono Filter.IsBounded.mono

theorem IsBoundedUnder.mono {f g : Filter β} {u : β → α} (h : f ≤ g) :
    g.IsBoundedUnder r u → f.IsBoundedUnder r u := fun hg => IsBounded.mono (map_mono h) hg
#align filter.is_bounded_under.mono Filter.IsBoundedUnder.mono

theorem IsBoundedUnder.mono_le [Preorder β] {l : Filter α} {u v : α → β}
    (hu : IsBoundedUnder (· ≤ ·) l u) (hv : v ≤ᶠ[l] u) : IsBoundedUnder (· ≤ ·) l v := by
  apply hu.imp
  -- ⊢ ∀ (a : β), (∀ᶠ (x : β) in map u l, (fun x x_1 => x ≤ x_1) x a) → ∀ᶠ (x : β)  …
  exact fun b hb => (eventually_map.1 hb).mp <| hv.mono fun x => le_trans
  -- 🎉 no goals
#align filter.is_bounded_under.mono_le Filter.IsBoundedUnder.mono_le

theorem IsBoundedUnder.mono_ge [Preorder β] {l : Filter α} {u v : α → β}
    (hu : IsBoundedUnder (· ≥ ·) l u) (hv : u ≤ᶠ[l] v) : IsBoundedUnder (· ≥ ·) l v :=
  IsBoundedUnder.mono_le (β := βᵒᵈ) hu hv
#align filter.is_bounded_under.mono_ge Filter.IsBoundedUnder.mono_ge

theorem isBoundedUnder_const [IsRefl α r] {l : Filter β} {a : α} : IsBoundedUnder r l fun _ => a :=
  ⟨a, eventually_map.2 <| eventually_of_forall fun _ => refl _⟩
#align filter.is_bounded_under_const Filter.isBoundedUnder_const

theorem IsBounded.isBoundedUnder {q : β → β → Prop} {u : α → β}
    (hu : ∀ a₀ a₁, r a₀ a₁ → q (u a₀) (u a₁)) : f.IsBounded r → f.IsBoundedUnder q u
  | ⟨b, h⟩ => ⟨u b, show ∀ᶠ x in f, q (u x) (u b) from h.mono fun x => hu x b⟩
#align filter.is_bounded.is_bounded_under Filter.IsBounded.isBoundedUnder

theorem IsBoundedUnder.comp {l : Filter γ} {q : β → β → Prop} {u : γ → α} {v : α → β}
    (hv : ∀ a₀ a₁, r a₀ a₁ → q (v a₀) (v a₁)) : l.IsBoundedUnder r u → l.IsBoundedUnder q (v ∘ u)
  | ⟨a, h⟩ => ⟨v a, show ∀ᶠ x in map u l, q (v x) (v a) from h.mono fun x => hv x a⟩

theorem _root_.Monotone.isBoundedUnder_le_comp [Preorder α] [Preorder β] {l : Filter γ} {u : γ → α}
    {v : α → β} (hv : Monotone v) (hl : l.IsBoundedUnder (· ≤ ·) u) :
    l.IsBoundedUnder (· ≤ ·) (v ∘ u) :=
  hl.comp hv

theorem _root_.Monotone.isBoundedUnder_ge_comp [Preorder α] [Preorder β] {l : Filter γ} {u : γ → α}
    {v : α → β} (hv : Monotone v) (hl : l.IsBoundedUnder (· ≥ ·) u) :
    l.IsBoundedUnder (· ≥ ·) (v ∘ u) :=
  hl.comp (swap hv)

theorem _root_.Antitone.isBoundedUnder_le_comp [Preorder α] [Preorder β] {l : Filter γ} {u : γ → α}
    {v : α → β} (hv : Antitone v) (hl : l.IsBoundedUnder (· ≥ ·) u) :
    l.IsBoundedUnder (· ≤ ·) (v ∘ u) :=
  hl.comp (swap hv)

theorem _root_.Antitone.isBoundedUnder_ge_comp [Preorder α] [Preorder β] {l : Filter γ} {u : γ → α}
    {v : α → β} (hv : Antitone v) (hl : l.IsBoundedUnder (· ≤ ·) u) :
    l.IsBoundedUnder (· ≥ ·) (v ∘ u) :=
  hl.comp hv

theorem not_isBoundedUnder_of_tendsto_atTop [Preorder β] [NoMaxOrder β] {f : α → β} {l : Filter α}
    [l.NeBot] (hf : Tendsto f l atTop) : ¬IsBoundedUnder (· ≤ ·) l f := by
  rintro ⟨b, hb⟩
  -- ⊢ False
  rw [eventually_map] at hb
  -- ⊢ False
  obtain ⟨b', h⟩ := exists_gt b
  -- ⊢ False
  have hb' := (tendsto_atTop.mp hf) b'
  -- ⊢ False
  have : { x : α | f x ≤ b } ∩ { x : α | b' ≤ f x } = ∅ :=
    eq_empty_of_subset_empty fun x hx => (not_le_of_lt h) (le_trans hx.2 hx.1)
  exact (nonempty_of_mem (hb.and hb')).ne_empty this
  -- 🎉 no goals
#align filter.not_is_bounded_under_of_tendsto_at_top Filter.not_isBoundedUnder_of_tendsto_atTop

theorem not_isBoundedUnder_of_tendsto_atBot [Preorder β] [NoMinOrder β] {f : α → β} {l : Filter α}
    [l.NeBot] (hf : Tendsto f l atBot) : ¬IsBoundedUnder (· ≥ ·) l f :=
  not_isBoundedUnder_of_tendsto_atTop (β := βᵒᵈ) hf
#align filter.not_is_bounded_under_of_tendsto_at_bot Filter.not_isBoundedUnder_of_tendsto_atBot

theorem IsBoundedUnder.bddAbove_range_of_cofinite [SemilatticeSup β] {f : α → β}
    (hf : IsBoundedUnder (· ≤ ·) cofinite f) : BddAbove (range f) := by
  rcases hf with ⟨b, hb⟩
  -- ⊢ BddAbove (range f)
  haveI : Nonempty β := ⟨b⟩
  -- ⊢ BddAbove (range f)
  rw [← image_univ, ← union_compl_self { x | f x ≤ b }, image_union, bddAbove_union]
  -- ⊢ BddAbove (f '' {x | f x ≤ b}) ∧ BddAbove (f '' {x | f x ≤ b}ᶜ)
  exact ⟨⟨b, ball_image_iff.2 fun x => id⟩, (hb.image f).bddAbove⟩
  -- 🎉 no goals
#align filter.is_bounded_under.bdd_above_range_of_cofinite Filter.IsBoundedUnder.bddAbove_range_of_cofinite

theorem IsBoundedUnder.bddBelow_range_of_cofinite [SemilatticeInf β] {f : α → β}
    (hf : IsBoundedUnder (· ≥ ·) cofinite f) : BddBelow (range f) :=
  IsBoundedUnder.bddAbove_range_of_cofinite (β := βᵒᵈ) hf
#align filter.is_bounded_under.bdd_below_range_of_cofinite Filter.IsBoundedUnder.bddBelow_range_of_cofinite

theorem IsBoundedUnder.bddAbove_range [SemilatticeSup β] {f : ℕ → β}
    (hf : IsBoundedUnder (· ≤ ·) atTop f) : BddAbove (range f) := by
  rw [← Nat.cofinite_eq_atTop] at hf
  -- ⊢ BddAbove (range f)
  exact hf.bddAbove_range_of_cofinite
  -- 🎉 no goals
#align filter.is_bounded_under.bdd_above_range Filter.IsBoundedUnder.bddAbove_range

theorem IsBoundedUnder.bddBelow_range [SemilatticeInf β] {f : ℕ → β}
    (hf : IsBoundedUnder (· ≥ ·) atTop f) : BddBelow (range f) :=
  IsBoundedUnder.bddAbove_range (β := βᵒᵈ) hf
#align filter.is_bounded_under.bdd_below_range Filter.IsBoundedUnder.bddBelow_range

/-- `IsCobounded (≺) f` states that the filter `f` does not tend to infinity w.r.t. `≺`. This is
also called frequently bounded. Will be usually instantiated with `≤` or `≥`.

There is a subtlety in this definition: we want `f.IsCobounded` to hold for any `f` in the case of
complete lattices. This will be relevant to deduce theorems on complete lattices from their
versions on conditionally complete lattices with additional assumptions. We have to be careful in
the edge case of the trivial filter containing the empty set: the other natural definition
  `¬ ∀ a, ∀ᶠ n in f, a ≤ n`
would not work as well in this case.
-/
def IsCobounded (r : α → α → Prop) (f : Filter α) :=
  ∃ b, ∀ a, (∀ᶠ x in f, r x a) → r b a
#align filter.is_cobounded Filter.IsCobounded

/-- `IsCoboundedUnder (≺) f u` states that the image of the filter `f` under the map `u` does not
tend to infinity w.r.t. `≺`. This is also called frequently bounded. Will be usually instantiated
with `≤` or `≥`. -/
def IsCoboundedUnder (r : α → α → Prop) (f : Filter β) (u : β → α) :=
  (map u f).IsCobounded r
#align filter.is_cobounded_under Filter.IsCoboundedUnder

/-- To check that a filter is frequently bounded, it suffices to have a witness
which bounds `f` at some point for every admissible set.

This is only an implication, as the other direction is wrong for the trivial filter.-/
theorem IsCobounded.mk [IsTrans α r] (a : α) (h : ∀ s ∈ f, ∃ x ∈ s, r a x) : f.IsCobounded r :=
  ⟨a, fun _ s =>
    let ⟨_, h₁, h₂⟩ := h _ s
    _root_.trans h₂ h₁⟩
#align filter.is_cobounded.mk Filter.IsCobounded.mk

/-- A filter which is eventually bounded is in particular frequently bounded (in the opposite
direction). At least if the filter is not trivial. -/
theorem IsBounded.isCobounded_flip [IsTrans α r] [NeBot f] : f.IsBounded r → f.IsCobounded (flip r)
  | ⟨a, ha⟩ =>
    ⟨a, fun b hb =>
      let ⟨_, rxa, rbx⟩ := (ha.and hb).exists
      show r b a from _root_.trans rbx rxa⟩
#align filter.is_bounded.is_cobounded_flip Filter.IsBounded.isCobounded_flip

theorem IsBounded.isCobounded_ge [Preorder α] [NeBot f] (h : f.IsBounded (· ≤ ·)) :
    f.IsCobounded (· ≥ ·) :=
  h.isCobounded_flip
#align filter.is_bounded.is_cobounded_ge Filter.IsBounded.isCobounded_ge

theorem IsBounded.isCobounded_le [Preorder α] [NeBot f] (h : f.IsBounded (· ≥ ·)) :
    f.IsCobounded (· ≤ ·) :=
  h.isCobounded_flip
#align filter.is_bounded.is_cobounded_le Filter.IsBounded.isCobounded_le

theorem IsBoundedUnder.isCoboundedUnder_flip {l : Filter γ} [IsTrans α r] [NeBot l]
    (h : l.IsBoundedUnder r u) : l.IsCoboundedUnder (flip r) u :=
  h.isCobounded_flip

theorem IsBoundedUnder.isCoboundedUnder_le {u : γ → α} {l : Filter γ} [Preorder α] [NeBot l]
    (h : l.IsBoundedUnder (· ≥ ·) u) : l.IsCoboundedUnder (· ≤ ·) u :=
  h.isCoboundedUnder_flip

theorem IsBoundedUnder.isCoboundedUnder_ge {u : γ → α} {l : Filter γ} [Preorder α] [NeBot l]
    (h : l.IsBoundedUnder (· ≤ ·) u) : l.IsCoboundedUnder (· ≥ ·) u :=
  h.isCoboundedUnder_flip

theorem isCobounded_bot : IsCobounded r ⊥ ↔ ∃ b, ∀ x, r b x := by simp [IsCobounded]
                                                                  -- 🎉 no goals
#align filter.is_cobounded_bot Filter.isCobounded_bot

theorem isCobounded_top : IsCobounded r ⊤ ↔ Nonempty α := by
  simp (config := { contextual := true }) [IsCobounded, eq_univ_iff_forall,
    exists_true_iff_nonempty]
#align filter.is_cobounded_top Filter.isCobounded_top

theorem isCobounded_principal (s : Set α) :
    (𝓟 s).IsCobounded r ↔ ∃ b, ∀ a, (∀ x ∈ s, r x a) → r b a := by simp [IsCobounded, subset_def]
                                                                   -- 🎉 no goals
#align filter.is_cobounded_principal Filter.isCobounded_principal

theorem IsCobounded.mono (h : f ≤ g) : f.IsCobounded r → g.IsCobounded r
  | ⟨b, hb⟩ => ⟨b, fun a ha => hb a (h ha)⟩
#align filter.is_cobounded.mono Filter.IsCobounded.mono

end Relation

theorem isCobounded_le_of_bot [Preorder α] [OrderBot α] {f : Filter α} : f.IsCobounded (· ≤ ·) :=
  ⟨⊥, fun _ _ => bot_le⟩
#align filter.is_cobounded_le_of_bot Filter.isCobounded_le_of_bot

theorem isCobounded_ge_of_top [Preorder α] [OrderTop α] {f : Filter α} : f.IsCobounded (· ≥ ·) :=
  ⟨⊤, fun _ _ => le_top⟩
#align filter.is_cobounded_ge_of_top Filter.isCobounded_ge_of_top

theorem isBounded_le_of_top [Preorder α] [OrderTop α] {f : Filter α} : f.IsBounded (· ≤ ·) :=
  ⟨⊤, eventually_of_forall fun _ => le_top⟩
#align filter.is_bounded_le_of_top Filter.isBounded_le_of_top

theorem isBounded_ge_of_bot [Preorder α] [OrderBot α] {f : Filter α} : f.IsBounded (· ≥ ·) :=
  ⟨⊥, eventually_of_forall fun _ => bot_le⟩
#align filter.is_bounded_ge_of_bot Filter.isBounded_ge_of_bot

@[simp]
theorem _root_.OrderIso.isBoundedUnder_le_comp [Preorder α] [Preorder β] (e : α ≃o β) {l : Filter γ}
    {u : γ → α} : (IsBoundedUnder (· ≤ ·) l fun x => e (u x)) ↔ IsBoundedUnder (· ≤ ·) l u :=
  (Function.Surjective.exists e.surjective).trans <|
    exists_congr fun a => by simp only [eventually_map, e.le_iff_le]
                             -- 🎉 no goals
#align order_iso.is_bounded_under_le_comp OrderIso.isBoundedUnder_le_comp

@[simp]
theorem _root_.OrderIso.isBoundedUnder_ge_comp [Preorder α] [Preorder β] (e : α ≃o β) {l : Filter γ}
    {u : γ → α} : (IsBoundedUnder (· ≥ ·) l fun x => e (u x)) ↔ IsBoundedUnder (· ≥ ·) l u :=
  OrderIso.isBoundedUnder_le_comp e.dual
#align order_iso.is_bounded_under_ge_comp OrderIso.isBoundedUnder_ge_comp

@[to_additive (attr := simp)]
theorem isBoundedUnder_le_inv [OrderedCommGroup α] {l : Filter β} {u : β → α} :
    (IsBoundedUnder (· ≤ ·) l fun x => (u x)⁻¹) ↔ IsBoundedUnder (· ≥ ·) l u :=
  (OrderIso.inv α).isBoundedUnder_ge_comp
#align filter.is_bounded_under_le_inv Filter.isBoundedUnder_le_inv
#align filter.is_bounded_under_le_neg Filter.isBoundedUnder_le_neg

@[to_additive (attr := simp)]
theorem isBoundedUnder_ge_inv [OrderedCommGroup α] {l : Filter β} {u : β → α} :
    (IsBoundedUnder (· ≥ ·) l fun x => (u x)⁻¹) ↔ IsBoundedUnder (· ≤ ·) l u :=
  (OrderIso.inv α).isBoundedUnder_le_comp
#align filter.is_bounded_under_ge_inv Filter.isBoundedUnder_ge_inv
#align filter.is_bounded_under_ge_neg Filter.isBoundedUnder_ge_neg

theorem IsBoundedUnder.sup [SemilatticeSup α] {f : Filter β} {u v : β → α} :
    f.IsBoundedUnder (· ≤ ·) u →
      f.IsBoundedUnder (· ≤ ·) v → f.IsBoundedUnder (· ≤ ·) fun a => u a ⊔ v a
  | ⟨bu, (hu : ∀ᶠ x in f, u x ≤ bu)⟩, ⟨bv, (hv : ∀ᶠ x in f, v x ≤ bv)⟩ =>
    ⟨bu ⊔ bv, show ∀ᶠ x in f, u x ⊔ v x ≤ bu ⊔ bv by filter_upwards [hu, hv]with _ using sup_le_sup⟩
                                                     -- 🎉 no goals
#align filter.is_bounded_under.sup Filter.IsBoundedUnder.sup

@[simp]
theorem isBoundedUnder_le_sup [SemilatticeSup α] {f : Filter β} {u v : β → α} :
    (f.IsBoundedUnder (· ≤ ·) fun a => u a ⊔ v a) ↔
      f.IsBoundedUnder (· ≤ ·) u ∧ f.IsBoundedUnder (· ≤ ·) v :=
  ⟨fun h =>
    ⟨h.mono_le <| eventually_of_forall fun _ => le_sup_left,
      h.mono_le <| eventually_of_forall fun _ => le_sup_right⟩,
    fun h => h.1.sup h.2⟩
#align filter.is_bounded_under_le_sup Filter.isBoundedUnder_le_sup

theorem IsBoundedUnder.inf [SemilatticeInf α] {f : Filter β} {u v : β → α} :
    f.IsBoundedUnder (· ≥ ·) u →
      f.IsBoundedUnder (· ≥ ·) v → f.IsBoundedUnder (· ≥ ·) fun a => u a ⊓ v a :=
  IsBoundedUnder.sup (α := αᵒᵈ)
#align filter.is_bounded_under.inf Filter.IsBoundedUnder.inf

@[simp]
theorem isBoundedUnder_ge_inf [SemilatticeInf α] {f : Filter β} {u v : β → α} :
    (f.IsBoundedUnder (· ≥ ·) fun a => u a ⊓ v a) ↔
      f.IsBoundedUnder (· ≥ ·) u ∧ f.IsBoundedUnder (· ≥ ·) v :=
  isBoundedUnder_le_sup (α := αᵒᵈ)
#align filter.is_bounded_under_ge_inf Filter.isBoundedUnder_ge_inf

theorem isBoundedUnder_le_abs [LinearOrderedAddCommGroup α] {f : Filter β} {u : β → α} :
    (f.IsBoundedUnder (· ≤ ·) fun a => |u a|) ↔
      f.IsBoundedUnder (· ≤ ·) u ∧ f.IsBoundedUnder (· ≥ ·) u :=
  isBoundedUnder_le_sup.trans <| and_congr Iff.rfl isBoundedUnder_le_neg
#align filter.is_bounded_under_le_abs Filter.isBoundedUnder_le_abs

/-- Filters are automatically bounded or cobounded in complete lattices. To use the same statements
in complete and conditionally complete lattices but let automation fill automatically the
boundedness proofs in complete lattices, we use the tactic `isBoundedDefault` in the statements,
in the form `(hf : f.IsBounded (≥) := by isBoundedDefault)`. -/

macro "isBoundedDefault" : tactic =>
  `(tactic| first
    | apply isCobounded_le_of_bot
    | apply isCobounded_ge_of_top
    | apply isBounded_le_of_top
    | apply isBounded_ge_of_bot)

-- Porting note: The above is a lean 4 reconstruction of (note that applyc is not available (yet?)):
-- unsafe def is_bounded_default : tactic Unit :=
--   tactic.applyc `` is_cobounded_le_of_bot <|>
--     tactic.applyc `` is_cobounded_ge_of_top <|>
--       tactic.applyc `` is_bounded_le_of_top <|> tactic.applyc `` is_bounded_ge_of_bot
-- #align filter.is_bounded_default filter.IsBounded_default


section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α]

-- Porting note: Renamed from Limsup and Liminf to limsSup and limsInf
/-- The `limsSup` of a filter `f` is the infimum of the `a` such that, eventually for `f`,
holds `x ≤ a`. -/
def limsSup (f : Filter α) : α :=
  sInf { a | ∀ᶠ n in f, n ≤ a }
set_option linter.uppercaseLean3 false in
#align filter.Limsup Filter.limsSup

set_option linter.uppercaseLean3 false in
/-- The `limsInf` of a filter `f` is the supremum of the `a` such that, eventually for `f`,
holds `x ≥ a`. -/
def limsInf (f : Filter α) : α :=
  sSup { a | ∀ᶠ n in f, a ≤ n }
set_option linter.uppercaseLean3 false in
#align filter.Liminf Filter.limsInf

/-- The `limsup` of a function `u` along a filter `f` is the infimum of the `a` such that,
eventually for `f`, holds `u x ≤ a`. -/
def limsup (u : β → α) (f : Filter β) : α :=
  limsSup (map u f)
#align filter.limsup Filter.limsup

/-- The `liminf` of a function `u` along a filter `f` is the supremum of the `a` such that,
eventually for `f`, holds `u x ≥ a`. -/
def liminf (u : β → α) (f : Filter β) : α :=
  limsInf (map u f)
#align filter.liminf Filter.liminf

/-- The `blimsup` of a function `u` along a filter `f`, bounded by a predicate `p`, is the infimum
of the `a` such that, eventually for `f`, `u x ≤ a` whenever `p x` holds. -/
def blimsup (u : β → α) (f : Filter β) (p : β → Prop) :=
  sInf { a | ∀ᶠ x in f, p x → u x ≤ a }
#align filter.blimsup Filter.blimsup

/-- The `bliminf` of a function `u` along a filter `f`, bounded by a predicate `p`, is the supremum
of the `a` such that, eventually for `f`, `a ≤ u x` whenever `p x` holds. -/
def bliminf (u : β → α) (f : Filter β) (p : β → Prop) :=
  sSup { a | ∀ᶠ x in f, p x → a ≤ u x }
#align filter.bliminf Filter.bliminf

section

variable {f : Filter β} {u : β → α} {p : β → Prop}

theorem limsup_eq : limsup u f = sInf { a | ∀ᶠ n in f, u n ≤ a } :=
  rfl
#align filter.limsup_eq Filter.limsup_eq

theorem liminf_eq : liminf u f = sSup { a | ∀ᶠ n in f, a ≤ u n } :=
  rfl
#align filter.liminf_eq Filter.liminf_eq

theorem blimsup_eq : blimsup u f p = sInf { a | ∀ᶠ x in f, p x → u x ≤ a } :=
  rfl
#align filter.blimsup_eq Filter.blimsup_eq

theorem bliminf_eq : bliminf u f p = sSup { a | ∀ᶠ x in f, p x → a ≤ u x } :=
  rfl
#align filter.bliminf_eq Filter.bliminf_eq

end

@[simp]
theorem blimsup_true (f : Filter β) (u : β → α) : (blimsup u f fun _ => True) = limsup u f := by
  simp [blimsup_eq, limsup_eq]
  -- 🎉 no goals
#align filter.blimsup_true Filter.blimsup_true

@[simp]
theorem bliminf_true (f : Filter β) (u : β → α) : (bliminf u f fun _ => True) = liminf u f := by
  simp [bliminf_eq, liminf_eq]
  -- 🎉 no goals
#align filter.bliminf_true Filter.bliminf_true

theorem blimsup_eq_limsup_subtype {f : Filter β} {u : β → α} {p : β → Prop} :
    blimsup u f p = limsup (u ∘ ((↑) : { x | p x } → β)) (comap (↑) f) := by
  simp only [blimsup_eq, limsup_eq, Function.comp_apply, eventually_comap, SetCoe.forall,
    Subtype.coe_mk, mem_setOf_eq]
  congr
  -- ⊢ {a | ∀ᶠ (x : β) in f, p x → u x ≤ a} = {a | ∀ᶠ (b : β) in f, ∀ (a_1 : { x // …
  ext a
  -- ⊢ a ∈ {a | ∀ᶠ (x : β) in f, p x → u x ≤ a} ↔ a ∈ {a | ∀ᶠ (b : β) in f, ∀ (a_1  …
  simp_rw [Subtype.forall]
  -- ⊢ a ∈ {a | ∀ᶠ (x : β) in f, p x → u x ≤ a} ↔ a ∈ {a | ∀ᶠ (b : β) in f, ∀ (a_1  …
  exact eventually_congr (
       eventually_of_forall
        fun x => ⟨fun hx y hy hxy => hxy.symm ▸ hx (hxy ▸ hy), fun hx hx' => hx x hx' rfl⟩)
#align filter.blimsup_eq_limsup_subtype Filter.blimsup_eq_limsup_subtype

theorem bliminf_eq_liminf_subtype {f : Filter β} {u : β → α} {p : β → Prop} :
    bliminf u f p = liminf (u ∘ ((↑) : { x | p x } → β)) (comap (↑) f) :=
  blimsup_eq_limsup_subtype (α := αᵒᵈ)
#align filter.bliminf_eq_liminf_subtype Filter.bliminf_eq_liminf_subtype

theorem limsSup_le_of_le {f : Filter α} {a}
    (hf : f.IsCobounded (· ≤ ·) := by isBoundedDefault)
    (h : ∀ᶠ n in f, n ≤ a) : limsSup f ≤ a :=
  csInf_le hf h
set_option linter.uppercaseLean3 false in
#align filter.Limsup_le_of_le Filter.limsSup_le_of_le

theorem le_limsInf_of_le {f : Filter α} {a}
    (hf : f.IsCobounded (· ≥ ·) := by isBoundedDefault)
    (h : ∀ᶠ n in f, a ≤ n) : a ≤ limsInf f :=
  le_csSup hf h
set_option linter.uppercaseLean3 false in
#align filter.le_Liminf_of_le Filter.le_limsInf_of_le

theorem limsup_le_of_le {f : Filter β} {u : β → α} {a}
    (hf : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h : ∀ᶠ n in f, u n ≤ a) : limsup u f ≤ a :=
  csInf_le hf h
#align filter.limsup_le_of_le Filter.limsSup_le_of_le

theorem le_liminf_of_le {f : Filter β} {u : β → α} {a}
    (hf : f.IsCoboundedUnder (· ≥ ·) u := by isBoundedDefault)
    (h : ∀ᶠ n in f, a ≤ u n) : a ≤ liminf u f :=
  le_csSup hf h
#align filter.le_liminf_of_le Filter.le_liminf_of_le

theorem le_limsSup_of_le {f : Filter α} {a}
    (hf : f.IsBounded (· ≤ ·) := by isBoundedDefault)
    (h : ∀ b, (∀ᶠ n in f, n ≤ b) → a ≤ b) : a ≤ limsSup f :=
  le_csInf hf h
set_option linter.uppercaseLean3 false in
#align filter.le_Limsup_of_le Filter.le_limsSup_of_le

theorem limsInf_le_of_le {f : Filter α} {a}
    (hf : f.IsBounded (· ≥ ·) := by isBoundedDefault)
    (h : ∀ b, (∀ᶠ n in f, b ≤ n) → b ≤ a) : limsInf f ≤ a :=
  csSup_le hf h
set_option linter.uppercaseLean3 false in
#align filter.Liminf_le_of_le Filter.limsInf_le_of_le

theorem le_limsup_of_le {f : Filter β} {u : β → α} {a}
    (hf : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h : ∀ b, (∀ᶠ n in f, u n ≤ b) → a ≤ b) : a ≤ limsup u f :=
  le_csInf hf h
#align filter.le_limsup_of_le Filter.le_limsup_of_le

theorem liminf_le_of_le {f : Filter β} {u : β → α} {a}
    (hf : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault)
    (h : ∀ b, (∀ᶠ n in f, b ≤ u n) → b ≤ a) : liminf u f ≤ a :=
  csSup_le hf h
#align filter.liminf_le_of_le Filter.liminf_le_of_le

theorem limsInf_le_limsSup {f : Filter α} [NeBot f]
    (h₁ : f.IsBounded (· ≤ ·) := by isBoundedDefault)
    (h₂ : f.IsBounded (· ≥ ·) := by isBoundedDefault):
    limsInf f ≤ limsSup f :=
  liminf_le_of_le h₂ fun a₀ ha₀ =>
    le_limsup_of_le h₁ fun a₁ ha₁ =>
      show a₀ ≤ a₁ from
        let ⟨_, hb₀, hb₁⟩ := (ha₀.and ha₁).exists
        le_trans hb₀ hb₁
set_option linter.uppercaseLean3 false in
#align filter.Liminf_le_Limsup Filter.limsInf_le_limsSup

theorem liminf_le_limsup {f : Filter β} [NeBot f] {u : β → α}
    (h : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h' : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault):
    liminf u f ≤ limsup u f :=
  limsInf_le_limsSup h h'
#align filter.liminf_le_limsup Filter.liminf_le_limsup

theorem limsSup_le_limsSup {f g : Filter α}
    (hf : f.IsCobounded (· ≤ ·) := by isBoundedDefault)
    (hg : g.IsBounded (· ≤ ·) := by isBoundedDefault)
    (h : ∀ a, (∀ᶠ n in g, n ≤ a) → ∀ᶠ n in f, n ≤ a) : limsSup f ≤ limsSup g :=
  csInf_le_csInf hf hg h
set_option linter.uppercaseLean3 false in
#align filter.Limsup_le_Limsup Filter.limsSup_le_limsSup

theorem limsInf_le_limsInf {f g : Filter α}
    (hf : f.IsBounded (· ≥ ·) := by isBoundedDefault)
    (hg : g.IsCobounded (· ≥ ·) := by isBoundedDefault)
    (h : ∀ a, (∀ᶠ n in f, a ≤ n) → ∀ᶠ n in g, a ≤ n) : limsInf f ≤ limsInf g :=
  csSup_le_csSup hg hf h
set_option linter.uppercaseLean3 false in
#align filter.Liminf_le_Liminf Filter.limsInf_le_limsInf

theorem limsup_le_limsup {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α → β}
    (h : u ≤ᶠ[f] v)
    (hu : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault)
    (hv : f.IsBoundedUnder (· ≤ ·) v := by isBoundedDefault) :
    limsup u f ≤ limsup v f :=
  limsSup_le_limsSup hu hv fun _ => h.trans
#align filter.limsup_le_limsup Filter.limsup_le_limsup

theorem liminf_le_liminf {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α → β}
    (h : ∀ᶠ a in f, u a ≤ v a)
    (hu : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault)
    (hv : f.IsCoboundedUnder (· ≥ ·) v := by isBoundedDefault) :
    liminf u f ≤ liminf v f :=
  limsup_le_limsup (β := βᵒᵈ) h hv hu
#align filter.liminf_le_liminf Filter.liminf_le_liminf

theorem limsSup_le_limsSup_of_le {f g : Filter α} (h : f ≤ g)
    (hf : f.IsCobounded (· ≤ ·) := by isBoundedDefault)
    (hg : g.IsBounded (· ≤ ·) := by isBoundedDefault) :
    limsSup f ≤ limsSup g :=
  limsSup_le_limsSup hf hg fun _ ha => h ha
set_option linter.uppercaseLean3 false in
#align filter.Limsup_le_Limsup_of_le Filter.limsSup_le_limsSup_of_le

theorem limsInf_le_limsInf_of_le {f g : Filter α} (h : g ≤ f)
    (hf : f.IsBounded (· ≥ ·) := by isBoundedDefault)
    (hg : g.IsCobounded (· ≥ ·) := by isBoundedDefault) :
    limsInf f ≤ limsInf g :=
  limsInf_le_limsInf hf hg fun _ ha => h ha
set_option linter.uppercaseLean3 false in
#align filter.Liminf_le_Liminf_of_le Filter.limsInf_le_limsInf_of_le

theorem limsup_le_limsup_of_le {α β} [ConditionallyCompleteLattice β] {f g : Filter α} (h : f ≤ g)
    {u : α → β}
    (hf : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault)
    (hg : g.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault) :
    limsup u f ≤ limsup u g :=
  limsSup_le_limsSup_of_le (map_mono h) hf hg
#align filter.limsup_le_limsup_of_le Filter.limsup_le_limsup_of_le

theorem liminf_le_liminf_of_le {α β} [ConditionallyCompleteLattice β] {f g : Filter α} (h : g ≤ f)
    {u : α → β}
    (hf : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault)
    (hg : g.IsCoboundedUnder (· ≥ ·) u := by isBoundedDefault) :
    liminf u f ≤ liminf u g :=
  limsInf_le_limsInf_of_le (map_mono h) hf hg
#align filter.liminf_le_liminf_of_le Filter.liminf_le_liminf_of_le

theorem limsSup_principal {s : Set α} (h : BddAbove s) (hs : s.Nonempty) : limsSup (𝓟 s) = sSup s :=
  by simp only [limsSup, eventually_principal]; exact csInf_upper_bounds_eq_csSup h hs
     -- ⊢ sInf {a | ∀ (x : α), x ∈ s → x ≤ a} = sSup s
                                                -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align filter.Limsup_principal Filter.limsSup_principal

theorem limsInf_principal {s : Set α} (h : BddBelow s) (hs : s.Nonempty) : limsInf (𝓟 s) = sInf s :=
  limsSup_principal (α := αᵒᵈ) h hs
set_option linter.uppercaseLean3 false in
#align filter.Liminf_principal Filter.limsInf_principal

theorem limsup_congr {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α → β}
    (h : ∀ᶠ a in f, u a = v a) : limsup u f = limsup v f := by
  rw [limsup_eq]
  -- ⊢ sInf {a | ∀ᶠ (n : α) in f, u n ≤ a} = limsup v f
  congr with b
  -- ⊢ b ∈ {a | ∀ᶠ (n : α) in f, u n ≤ a} ↔ b ∈ {a | ∀ᶠ (n : β) in map v f, n ≤ a}
  exact eventually_congr (h.mono fun x hx => by simp [hx])
  -- 🎉 no goals
#align filter.limsup_congr Filter.limsup_congr

theorem blimsup_congr {f : Filter β} {u v : β → α} {p : β → Prop} (h : ∀ᶠ a in f, p a → u a = v a) :
    blimsup u f p = blimsup v f p := by
  rw [blimsup_eq]
  -- ⊢ sInf {a | ∀ᶠ (x : β) in f, p x → u x ≤ a} = blimsup v f p
  congr with b
  -- ⊢ b ∈ {a | ∀ᶠ (x : β) in f, p x → u x ≤ a} ↔ b ∈ {a | ∀ᶠ (x : β) in f, p x → v …
  refine' eventually_congr (h.mono fun x hx => ⟨fun h₁ h₂ => _, fun h₁ h₂ => _⟩)
  -- ⊢ v x ≤ b
  · rw [← hx h₂]
    -- ⊢ u x ≤ b
    exact h₁ h₂
    -- 🎉 no goals
  · rw [hx h₂]
    -- ⊢ v x ≤ b
    exact h₁ h₂
    -- 🎉 no goals
#align filter.blimsup_congr Filter.blimsup_congr

theorem bliminf_congr {f : Filter β} {u v : β → α} {p : β → Prop} (h : ∀ᶠ a in f, p a → u a = v a) :
    bliminf u f p = bliminf v f p :=
  blimsup_congr (α := αᵒᵈ) h
#align filter.bliminf_congr Filter.bliminf_congr

theorem liminf_congr {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α → β}
    (h : ∀ᶠ a in f, u a = v a) : liminf u f = liminf v f :=
  limsup_congr (β := βᵒᵈ) h
#align filter.liminf_congr Filter.liminf_congr

theorem limsup_const {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} [NeBot f]
    (b : β) : limsup (fun _ => b) f = b := by
  simpa only [limsup_eq, eventually_const] using csInf_Ici
  -- 🎉 no goals
#align filter.limsup_const Filter.limsup_const

theorem liminf_const {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} [NeBot f]
    (b : β) : liminf (fun _ => b) f = b :=
  limsup_const (β := βᵒᵈ) b
#align filter.liminf_const Filter.liminf_const

end ConditionallyCompleteLattice

section CompleteLattice

variable [CompleteLattice α]

@[simp]
theorem limsSup_bot : limsSup (⊥ : Filter α) = ⊥ :=
  bot_unique <| sInf_le <| by simp
                              -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align filter.Limsup_bot Filter.limsSup_bot

@[simp] theorem limsup_bot (f : β → α) : limsup f ⊥ = ⊥ := by simp [limsup]
                                                              -- 🎉 no goals

@[simp]
theorem limsInf_bot : limsInf (⊥ : Filter α) = ⊤ :=
  top_unique <| le_sSup <| by simp
                              -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align filter.Liminf_bot Filter.limsInf_bot

@[simp] theorem liminf_bot (f : β → α) : liminf f ⊥ = ⊤ := by simp [liminf]
                                                              -- 🎉 no goals

@[simp]
theorem limsSup_top : limsSup (⊤ : Filter α) = ⊤ :=
  top_unique <| le_sInf <| by simp [eq_univ_iff_forall]; exact fun b hb => top_unique <| hb _
                              -- ⊢ ∀ (b : α), (∀ (x : α), x ≤ b) → b = ⊤
                                                         -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align filter.Limsup_top Filter.limsSup_top

@[simp]
theorem limsInf_top : limsInf (⊤ : Filter α) = ⊥ :=
  bot_unique <| sSup_le <| by simp [eq_univ_iff_forall]; exact fun b hb => bot_unique <| hb _
                              -- ⊢ ∀ (b : α), (∀ (x : α), b ≤ x) → b = ⊥
                                                         -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align filter.Liminf_top Filter.limsInf_top

@[simp]
theorem blimsup_false {f : Filter β} {u : β → α} : (blimsup u f fun _ => False) = ⊥ := by
  simp [blimsup_eq]
  -- 🎉 no goals
#align filter.blimsup_false Filter.blimsup_false

@[simp]
theorem bliminf_false {f : Filter β} {u : β → α} : (bliminf u f fun _ => False) = ⊤ := by
  simp [bliminf_eq]
  -- 🎉 no goals
#align filter.bliminf_false Filter.bliminf_false

/-- Same as limsup_const applied to `⊥` but without the `NeBot f` assumption -/
theorem limsup_const_bot {f : Filter β} : limsup (fun _ : β => (⊥ : α)) f = (⊥ : α) := by
  rw [limsup_eq, eq_bot_iff]
  -- ⊢ sInf {a | ∀ᶠ (n : β) in f, ⊥ ≤ a} ≤ ⊥
  exact sInf_le (eventually_of_forall fun _ => le_rfl)
  -- 🎉 no goals
#align filter.limsup_const_bot Filter.limsup_const_bot

/-- Same as limsup_const applied to `⊤` but without the `NeBot f` assumption -/
theorem liminf_const_top {f : Filter β} : liminf (fun _ : β => (⊤ : α)) f = (⊤ : α) :=
  limsup_const_bot (α := αᵒᵈ)
#align filter.liminf_const_top Filter.liminf_const_top

theorem HasBasis.limsSup_eq_iInf_sSup {ι} {p : ι → Prop} {s} {f : Filter α} (h : f.HasBasis p s) :
    limsSup f = ⨅ (i) (_ : p i), sSup (s i) :=
  le_antisymm (le_iInf₂ fun i hi => sInf_le <| h.eventually_iff.2 ⟨i, hi, fun _ => le_sSup⟩)
    (le_sInf fun _ ha =>
      let ⟨_, hi, ha⟩ := h.eventually_iff.1 ha
      iInf₂_le_of_le _ hi <| sSup_le ha)
set_option linter.uppercaseLean3 false in
#align filter.has_basis.Limsup_eq_infi_Sup Filter.HasBasis.limsSup_eq_iInf_sSup

theorem HasBasis.limsInf_eq_iSup_sInf {p : ι → Prop} {s : ι → Set α} {f : Filter α}
    (h : f.HasBasis p s) : limsInf f = ⨆ (i) (_ : p i), sInf (s i) :=
  HasBasis.limsSup_eq_iInf_sSup (α := αᵒᵈ) h
set_option linter.uppercaseLean3 false in
#align filter.has_basis.Liminf_eq_supr_Inf Filter.HasBasis.limsInf_eq_iSup_sInf

theorem limsSup_eq_iInf_sSup {f : Filter α} : limsSup f = ⨅ s ∈ f, sSup s :=
  f.basis_sets.limsSup_eq_iInf_sSup
set_option linter.uppercaseLean3 false in
#align filter.Limsup_eq_infi_Sup Filter.limsSup_eq_iInf_sSup

theorem limsInf_eq_iSup_sInf {f : Filter α} : limsInf f = ⨆ s ∈ f, sInf s :=
  limsSup_eq_iInf_sSup (α := αᵒᵈ)
set_option linter.uppercaseLean3 false in
#align filter.Liminf_eq_supr_Inf Filter.limsInf_eq_iSup_sInf

theorem limsup_le_iSup {f : Filter β} {u : β → α} : limsup u f ≤ ⨆ n, u n :=
  limsup_le_of_le (by isBoundedDefault) (eventually_of_forall (le_iSup u))
                      -- 🎉 no goals
#align filter.limsup_le_supr Filter.limsup_le_iSup

theorem iInf_le_liminf {f : Filter β} {u : β → α} : ⨅ n, u n ≤ liminf u f :=
  le_liminf_of_le (by isBoundedDefault) (eventually_of_forall (iInf_le u))
                      -- 🎉 no goals
#align filter.infi_le_liminf Filter.iInf_le_liminf

/-- In a complete lattice, the limsup of a function is the infimum over sets `s` in the filter
of the supremum of the function over `s` -/
theorem limsup_eq_iInf_iSup {f : Filter β} {u : β → α} : limsup u f = ⨅ s ∈ f, ⨆ a ∈ s, u a :=
  (f.basis_sets.map u).limsSup_eq_iInf_sSup.trans <| by simp only [sSup_image, id]
                                                        -- 🎉 no goals
#align filter.limsup_eq_infi_supr Filter.limsup_eq_iInf_iSup

theorem limsup_eq_iInf_iSup_of_nat {u : ℕ → α} : limsup u atTop = ⨅ n : ℕ, ⨆ i ≥ n, u i :=
  (atTop_basis.map u).limsSup_eq_iInf_sSup.trans <| by simp only [sSup_image, iInf_const]; rfl
                                                       -- ⊢ ⨅ (i : ℕ), ⨆ (a : ℕ) (_ : a ∈ Ici i), u a = ⨅ (n : ℕ), ⨆ (i : ℕ) (_ : i ≥ n) …
                                                                                           -- 🎉 no goals
#align filter.limsup_eq_infi_supr_of_nat Filter.limsup_eq_iInf_iSup_of_nat

theorem limsup_eq_iInf_iSup_of_nat' {u : ℕ → α} : limsup u atTop = ⨅ n : ℕ, ⨆ i : ℕ, u (i + n) := by
  simp only [limsup_eq_iInf_iSup_of_nat, iSup_ge_eq_iSup_nat_add]
  -- 🎉 no goals
#align filter.limsup_eq_infi_supr_of_nat' Filter.limsup_eq_iInf_iSup_of_nat'

theorem HasBasis.limsup_eq_iInf_iSup {p : ι → Prop} {s : ι → Set β} {f : Filter β} {u : β → α}
    (h : f.HasBasis p s) : limsup u f = ⨅ (i) (_ : p i), ⨆ a ∈ s i, u a :=
  (h.map u).limsSup_eq_iInf_sSup.trans <| by simp only [sSup_image, id]
                                             -- 🎉 no goals
#align filter.has_basis.limsup_eq_infi_supr Filter.HasBasis.limsup_eq_iInf_iSup

theorem blimsup_congr' {f : Filter β} {p q : β → Prop} {u : β → α}
    (h : ∀ᶠ x in f, u x ≠ ⊥ → (p x ↔ q x)) : blimsup u f p = blimsup u f q := by
  simp only [blimsup_eq]
  -- ⊢ sInf {a | ∀ᶠ (x : β) in f, p x → u x ≤ a} = sInf {a | ∀ᶠ (x : β) in f, q x → …
  congr
  -- ⊢ {a | ∀ᶠ (x : β) in f, p x → u x ≤ a} = {a | ∀ᶠ (x : β) in f, q x → u x ≤ a}
  ext a
  -- ⊢ a ∈ {a | ∀ᶠ (x : β) in f, p x → u x ≤ a} ↔ a ∈ {a | ∀ᶠ (x : β) in f, q x → u …
  refine' eventually_congr (h.mono fun b hb => _)
  -- ⊢ p b → u b ≤ a ↔ q b → u b ≤ a
  cases' eq_or_ne (u b) ⊥ with hu hu; · simp [hu]
  -- ⊢ p b → u b ≤ a ↔ q b → u b ≤ a
                                        -- 🎉 no goals
  rw [hb hu]
  -- 🎉 no goals
#align filter.blimsup_congr' Filter.blimsup_congr'

theorem bliminf_congr' {f : Filter β} {p q : β → Prop} {u : β → α}
    (h : ∀ᶠ x in f, u x ≠ ⊤ → (p x ↔ q x)) : bliminf u f p = bliminf u f q :=
  blimsup_congr' (α := αᵒᵈ) h
#align filter.bliminf_congr' Filter.bliminf_congr'

theorem blimsup_eq_iInf_biSup {f : Filter β} {p : β → Prop} {u : β → α} :
    blimsup u f p = ⨅ s ∈ f, ⨆ (b) (_ : p b ∧ b ∈ s), u b := by
  refine' le_antisymm (sInf_le_sInf _) (iInf_le_iff.mpr fun a ha => le_sInf_iff.mpr fun a' ha' => _)
  -- ⊢ (range fun s => ⨅ (_ : s ∈ f), ⨆ (b : β) (_ : p b ∧ b ∈ s), u b) ⊆ {a | ∀ᶠ ( …
  · rintro - ⟨s, rfl⟩
    -- ⊢ (fun s => ⨅ (_ : s ∈ f), ⨆ (b : β) (_ : p b ∧ b ∈ s), u b) s ∈ {a | ∀ᶠ (x :  …
    simp only [mem_setOf_eq, le_iInf_iff]
    -- ⊢ ∀ᶠ (x : β) in f, p x → s ∈ f → u x ≤ ⨆ (b : β) (_ : p b ∧ b ∈ s), u b
    conv =>
      congr
      ext
      rw [Imp.swap]
    refine'
      eventually_imp_distrib_left.mpr fun h => eventually_iff_exists_mem.2 ⟨s, h, fun x h₁ h₂ => _⟩
    exact @le_iSup₂ α β (fun b => p b ∧ b ∈ s) _ (fun b _ => u b) x ⟨h₂, h₁⟩
    -- 🎉 no goals
  · obtain ⟨s, hs, hs'⟩ := eventually_iff_exists_mem.mp ha'
    -- ⊢ a ≤ a'
    have : ∀ (y : β), p y → y ∈ s → u y ≤ a' := fun y ↦ by rw [Imp.swap]; exact hs' y
    -- ⊢ a ≤ a'
    exact (le_iInf_iff.mp (ha s) hs).trans (by simpa only [iSup₂_le_iff, and_imp] )
    -- 🎉 no goals
#align filter.blimsup_eq_infi_bsupr Filter.blimsup_eq_iInf_biSup

theorem blimsup_eq_iInf_biSup_of_nat {p : ℕ → Prop} {u : ℕ → α} :
    blimsup u atTop p = ⨅ i, ⨆ (j) (_ : p j ∧ i ≤ j), u j := by
  -- Porting note: Making this into a single simp only does not work?
  simp only [blimsup_eq_limsup_subtype, Function.comp,
    (atTop_basis.comap ((↑) : { x | p x } → ℕ)).limsup_eq_iInf_iSup, iSup_subtype, iSup_and]
  simp only [mem_setOf_eq, mem_preimage, mem_Ici, not_le, iInf_pos]
  -- 🎉 no goals
#align filter.blimsup_eq_infi_bsupr_of_nat Filter.blimsup_eq_iInf_biSup_of_nat

/-- In a complete lattice, the liminf of a function is the infimum over sets `s` in the filter
of the supremum of the function over `s` -/
theorem liminf_eq_iSup_iInf {f : Filter β} {u : β → α} : liminf u f = ⨆ s ∈ f, ⨅ a ∈ s, u a :=
  limsup_eq_iInf_iSup (α := αᵒᵈ)
#align filter.liminf_eq_supr_infi Filter.liminf_eq_iSup_iInf

theorem liminf_eq_iSup_iInf_of_nat {u : ℕ → α} : liminf u atTop = ⨆ n : ℕ, ⨅ i ≥ n, u i :=
  @limsup_eq_iInf_iSup_of_nat αᵒᵈ _ u
#align filter.liminf_eq_supr_infi_of_nat Filter.liminf_eq_iSup_iInf_of_nat

theorem liminf_eq_iSup_iInf_of_nat' {u : ℕ → α} : liminf u atTop = ⨆ n : ℕ, ⨅ i : ℕ, u (i + n) :=
  @limsup_eq_iInf_iSup_of_nat' αᵒᵈ _ _
#align filter.liminf_eq_supr_infi_of_nat' Filter.liminf_eq_iSup_iInf_of_nat'

theorem HasBasis.liminf_eq_iSup_iInf {p : ι → Prop} {s : ι → Set β} {f : Filter β} {u : β → α}
    (h : f.HasBasis p s) : liminf u f = ⨆ (i) (_ : p i), ⨅ a ∈ s i, u a :=
  HasBasis.limsup_eq_iInf_iSup (α := αᵒᵈ) h
#align filter.has_basis.liminf_eq_supr_infi Filter.HasBasis.liminf_eq_iSup_iInf

theorem bliminf_eq_iSup_biInf {f : Filter β} {p : β → Prop} {u : β → α} :
    bliminf u f p = ⨆ s ∈ f, ⨅ (b) (_ : p b ∧ b ∈ s), u b :=
  @blimsup_eq_iInf_biSup αᵒᵈ β _ f p u
#align filter.bliminf_eq_supr_binfi Filter.bliminf_eq_iSup_biInf

theorem bliminf_eq_iSup_biInf_of_nat {p : ℕ → Prop} {u : ℕ → α} :
    bliminf u atTop p = ⨆ i, ⨅ (j) (_ : p j ∧ i ≤ j), u j :=
  @blimsup_eq_iInf_biSup_of_nat αᵒᵈ _ p u
#align filter.bliminf_eq_supr_binfi_of_nat Filter.bliminf_eq_iSup_biInf_of_nat

theorem limsup_eq_sInf_sSup {ι R : Type*} (F : Filter ι) [CompleteLattice R] (a : ι → R) :
    limsup a F = sInf ((fun I => sSup (a '' I)) '' F.sets) := by
  refine' le_antisymm _ _
  -- ⊢ limsup a F ≤ sInf ((fun I => sSup (a '' I)) '' F.sets)
  · rw [limsup_eq]
    -- ⊢ sInf {a_1 | ∀ᶠ (n : ι) in F, a n ≤ a_1} ≤ sInf ((fun I => sSup (a '' I)) ''  …
    refine' sInf_le_sInf fun x hx => _
    -- ⊢ x ∈ {a_1 | ∀ᶠ (n : ι) in F, a n ≤ a_1}
    rcases(mem_image _ F.sets x).mp hx with ⟨I, ⟨I_mem_F, hI⟩⟩
    -- ⊢ x ∈ {a_1 | ∀ᶠ (n : ι) in F, a n ≤ a_1}
    filter_upwards [I_mem_F]with i hi
    -- ⊢ a i ≤ x
    exact hI ▸ le_sSup (mem_image_of_mem _ hi)
    -- 🎉 no goals
  · refine'
      le_sInf_iff.mpr fun b hb =>
        sInf_le_of_le (mem_image_of_mem _ <| Filter.mem_sets.mpr hb) <| sSup_le _
    rintro _ ⟨_, h, rfl⟩
    -- ⊢ a w✝ ≤ b
    exact h
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align filter.limsup_eq_Inf_Sup Filter.limsup_eq_sInf_sSup

theorem liminf_eq_sSup_sInf {ι R : Type*} (F : Filter ι) [CompleteLattice R] (a : ι → R) :
    liminf a F = sSup ((fun I => sInf (a '' I)) '' F.sets) :=
  @Filter.limsup_eq_sInf_sSup ι (OrderDual R) _ _ a
set_option linter.uppercaseLean3 false in
#align filter.liminf_eq_Sup_Inf Filter.liminf_eq_sSup_sInf

-- Porting note: simp_nf linter incorrectly says: lhs does not simplify when using simp on itself.
@[simp, nolint simpNF]
theorem liminf_nat_add (f : ℕ → α) (k : ℕ) :
    liminf (fun i => f (i + k)) atTop = liminf f atTop := by
  simp_rw [liminf_eq_iSup_iInf_of_nat]
  -- ⊢ ⨆ (n : ℕ), ⨅ (i : ℕ) (_ : i ≥ n), f (i + k) = ⨆ (n : ℕ), ⨅ (i : ℕ) (_ : i ≥  …
  exact iSup_iInf_ge_nat_add f k
  -- 🎉 no goals
#align filter.liminf_nat_add Filter.liminf_nat_add

-- Porting note: simp_nf linter incorrectly says: lhs does not simplify when using simp on itself.
@[simp, nolint simpNF]
theorem limsup_nat_add (f : ℕ → α) (k : ℕ) : limsup (fun i => f (i + k)) atTop = limsup f atTop :=
  @liminf_nat_add αᵒᵈ _ f k
#align filter.limsup_nat_add Filter.limsup_nat_add

theorem liminf_le_of_frequently_le' {α β} [CompleteLattice β] {f : Filter α} {u : α → β} {x : β}
    (h : ∃ᶠ a in f, u a ≤ x) : liminf u f ≤ x := by
  rw [liminf_eq]
  -- ⊢ sSup {a | ∀ᶠ (n : α) in f, a ≤ u n} ≤ x
  refine' sSup_le fun b hb => _
  -- ⊢ b ≤ x
  have hbx : ∃ᶠ _ in f, b ≤ x := by
    revert h
    rw [← not_imp_not, not_frequently, not_frequently]
    exact fun h => hb.mp (h.mono fun a hbx hba hax => hbx (hba.trans hax))
  exact hbx.exists.choose_spec
  -- 🎉 no goals
#align filter.liminf_le_of_frequently_le' Filter.liminf_le_of_frequently_le'

theorem le_limsup_of_frequently_le' {α β} [CompleteLattice β] {f : Filter α} {u : α → β} {x : β}
    (h : ∃ᶠ a in f, x ≤ u a) : x ≤ limsup u f :=
  liminf_le_of_frequently_le' (β := βᵒᵈ) h
#align filter.le_limsup_of_frequently_le' Filter.le_limsup_of_frequently_le'

/-- If `f : α → α` is a morphism of complete lattices, then the limsup of its iterates of any
`a : α` is a fixed point. -/
@[simp]
theorem CompleteLatticeHom.apply_limsup_iterate (f : CompleteLatticeHom α α) (a : α) :
    f (limsup (fun n => f^[n] a) atTop) = limsup (fun n => f^[n] a) atTop := by
  rw [limsup_eq_iInf_iSup_of_nat', map_iInf]
  -- ⊢ ⨅ (i : ℕ), ↑f (⨆ (i_1 : ℕ), (↑f)^[i_1 + i] a) = ⨅ (n : ℕ), ⨆ (i : ℕ), (↑f)^[ …
  simp_rw [_root_.map_iSup, ← Function.comp_apply (f := f), ← Function.iterate_succ' f,
    ← Nat.add_succ]
  conv_rhs => rw [iInf_split _ ((· < ·) (0 : ℕ))]
  -- ⊢ ⨅ (i : ℕ), ⨆ (i_1 : ℕ), (↑f)^[i_1 + Nat.succ i] a = (⨅ (i : ℕ) (_ : (fun x x …
  simp only [not_lt, le_zero_iff, iInf_iInf_eq_left, add_zero, iInf_nat_gt_zero_eq, left_eq_inf]
  -- ⊢ ⨅ (i : ℕ), ⨆ (i_1 : ℕ), (↑f)^[i_1 + Nat.succ i] a ≤ ⨆ (i : ℕ), (↑f)^[i] a
  refine' (iInf_le (fun i => ⨆ j, f^[j + (i + 1)] a) 0).trans _
  -- ⊢ ⨆ (j : ℕ), (↑f)^[j + (0 + 1)] a ≤ ⨆ (i : ℕ), (↑f)^[i] a
  simp only [zero_add, Function.comp_apply, iSup_le_iff]
  -- ⊢ ∀ (i : ℕ), (↑f)^[i + 1] a ≤ ⨆ (i : ℕ), (↑f)^[i] a
  exact fun i => le_iSup (fun i => f^[i] a) (i + 1)
  -- 🎉 no goals
#align filter.complete_lattice_hom.apply_limsup_iterate Filter.CompleteLatticeHom.apply_limsup_iterate

/-- If `f : α → α` is a morphism of complete lattices, then the liminf of its iterates of any
`a : α` is a fixed point. -/
theorem CompleteLatticeHom.apply_liminf_iterate (f : CompleteLatticeHom α α) (a : α) :
    f (liminf (fun n => f^[n] a) atTop) = liminf (fun n => f^[n] a) atTop :=
  apply_limsup_iterate (CompleteLatticeHom.dual f) _
#align filter.complete_lattice_hom.apply_liminf_iterate Filter.CompleteLatticeHom.apply_liminf_iterate

variable {f g : Filter β} {p q : β → Prop} {u v : β → α}

theorem blimsup_mono (h : ∀ x, p x → q x) : blimsup u f p ≤ blimsup u f q :=
  sInf_le_sInf fun a ha => ha.mono <| by tauto
                                         -- 🎉 no goals
#align filter.blimsup_mono Filter.blimsup_mono

theorem bliminf_antitone (h : ∀ x, p x → q x) : bliminf u f q ≤ bliminf u f p :=
  sSup_le_sSup fun a ha => ha.mono <| by tauto
                                         -- 🎉 no goals
#align filter.bliminf_antitone Filter.bliminf_antitone

theorem mono_blimsup' (h : ∀ᶠ x in f, p x → u x ≤ v x) : blimsup u f p ≤ blimsup v f p :=
  sInf_le_sInf fun _ ha => (ha.and h).mono fun _ hx hx' => (hx.2 hx').trans (hx.1 hx')
#align filter.mono_blimsup' Filter.mono_blimsup'

theorem mono_blimsup (h : ∀ x, p x → u x ≤ v x) : blimsup u f p ≤ blimsup v f p :=
  mono_blimsup' <| eventually_of_forall h
#align filter.mono_blimsup Filter.mono_blimsup

theorem mono_bliminf' (h : ∀ᶠ x in f, p x → u x ≤ v x) : bliminf u f p ≤ bliminf v f p :=
  sSup_le_sSup fun _ ha => (ha.and h).mono fun _ hx hx' => (hx.1 hx').trans (hx.2 hx')
#align filter.mono_bliminf' Filter.mono_bliminf'

theorem mono_bliminf (h : ∀ x, p x → u x ≤ v x) : bliminf u f p ≤ bliminf v f p :=
  mono_bliminf' <| eventually_of_forall h
#align filter.mono_bliminf Filter.mono_bliminf

theorem bliminf_antitone_filter (h : f ≤ g) : bliminf u g p ≤ bliminf u f p :=
  sSup_le_sSup fun _ ha => ha.filter_mono h
#align filter.bliminf_antitone_filter Filter.bliminf_antitone_filter

theorem blimsup_monotone_filter (h : f ≤ g) : blimsup u f p ≤ blimsup u g p :=
  sInf_le_sInf fun _ ha => ha.filter_mono h
#align filter.blimsup_monotone_filter Filter.blimsup_monotone_filter


-- @[simp] -- Porting note: simp_nf linter, lhs simplifies, added _aux versions below
theorem blimsup_and_le_inf : (blimsup u f fun x => p x ∧ q x) ≤ blimsup u f p ⊓ blimsup u f q :=
  le_inf (blimsup_mono <| by tauto) (blimsup_mono <| by tauto)
                             -- 🎉 no goals
                                                        -- 🎉 no goals
#align filter.blimsup_and_le_inf Filter.blimsup_and_le_inf

@[simp]
theorem bliminf_sup_le_inf_aux_left :
  (blimsup u f fun x => p x ∧ q x) ≤ blimsup u f p :=
  blimsup_and_le_inf.trans inf_le_left

@[simp]
theorem bliminf_sup_le_inf_aux_right :
    (blimsup u f fun x => p x ∧ q x) ≤ blimsup u f q :=
  blimsup_and_le_inf.trans inf_le_right

-- @[simp] -- Porting note: simp_nf linter, lhs simplifies, added _aux simp version below
theorem bliminf_sup_le_and : bliminf u f p ⊔ bliminf u f q ≤ bliminf u f fun x => p x ∧ q x :=
  blimsup_and_le_inf (α := αᵒᵈ)
#align filter.bliminf_sup_le_and Filter.bliminf_sup_le_and

@[simp]
theorem bliminf_sup_le_and_aux_left : bliminf u f p ≤ bliminf u f fun x => p x ∧ q x :=
  le_sup_left.trans bliminf_sup_le_and

@[simp]
theorem bliminf_sup_le_and_aux_right : bliminf u f q ≤ bliminf u f fun x => p x ∧ q x :=
  le_sup_right.trans bliminf_sup_le_and

/-- See also `Filter.blimsup_or_eq_sup`. -/
-- @[simp] -- Porting note: simp_nf linter, lhs simplifies, added _aux simp versions below
theorem blimsup_sup_le_or : blimsup u f p ⊔ blimsup u f q ≤ blimsup u f fun x => p x ∨ q x :=
  sup_le (blimsup_mono <| by tauto) (blimsup_mono <| by tauto)
                             -- 🎉 no goals
                                                        -- 🎉 no goals
#align filter.blimsup_sup_le_or Filter.blimsup_sup_le_or

@[simp]
theorem bliminf_sup_le_or_aux_left : blimsup u f p ≤ blimsup u f fun x => p x ∨ q x :=
  le_sup_left.trans blimsup_sup_le_or

@[simp]
theorem bliminf_sup_le_or_aux_right : blimsup u f q ≤ blimsup u f fun x => p x ∨ q x :=
  le_sup_right.trans blimsup_sup_le_or

/-- See also `Filter.bliminf_or_eq_inf`. -/
--@[simp] -- Porting note: simp_nf linter, lhs simplifies, added _aux simp versions below
theorem bliminf_or_le_inf : (bliminf u f fun x => p x ∨ q x) ≤ bliminf u f p ⊓ bliminf u f q :=
  blimsup_sup_le_or (α := αᵒᵈ)
#align filter.bliminf_or_le_inf Filter.bliminf_or_le_inf

@[simp]
theorem bliminf_or_le_inf_aux_left : (bliminf u f fun x => p x ∨ q x) ≤ bliminf u f p :=
  bliminf_or_le_inf.trans inf_le_left

@[simp]
theorem bliminf_or_le_inf_aux_right : (bliminf u f fun x => p x ∨ q x) ≤ bliminf u f q :=
  bliminf_or_le_inf.trans inf_le_right

/- Porting note: Replaced `e` with `FunLike.coe e` to override the strange
 coercion to `↑(RelIso.toRelEmbedding e).toEmbedding`.-/
theorem OrderIso.apply_blimsup [CompleteLattice γ] (e : α ≃o γ) :
    FunLike.coe e (blimsup u f p) = blimsup ((FunLike.coe e) ∘ u) f p := by
  simp only [blimsup_eq, map_sInf, Function.comp_apply]
  -- ⊢ sInf ((fun a => ↑e a) '' {a | ∀ᶠ (x : β) in f, p x → u x ≤ a}) = sInf {a | ∀ …
  congr
  -- ⊢ (fun a => ↑e a) '' {a | ∀ᶠ (x : β) in f, p x → u x ≤ a} = {a | ∀ᶠ (x : β) in …
  ext c
  -- ⊢ c ∈ (fun a => ↑e a) '' {a | ∀ᶠ (x : β) in f, p x → u x ≤ a} ↔ c ∈ {a | ∀ᶠ (x …
  obtain ⟨a, rfl⟩ := e.surjective c
  -- ⊢ ↑e a ∈ (fun a => ↑e a) '' {a | ∀ᶠ (x : β) in f, p x → u x ≤ a} ↔ ↑e a ∈ {a | …
  simp
  -- 🎉 no goals
#align filter.order_iso.apply_blimsup Filter.OrderIso.apply_blimsup

theorem OrderIso.apply_bliminf [CompleteLattice γ] (e : α ≃o γ) :
    e (bliminf u f p) = bliminf (e ∘ u) f p :=
  OrderIso.apply_blimsup (α := αᵒᵈ) (γ := γᵒᵈ) e.dual
#align filter.order_iso.apply_bliminf Filter.OrderIso.apply_bliminf

theorem SupHom.apply_blimsup_le [CompleteLattice γ] (g : sSupHom α γ) :
    g (blimsup u f p) ≤ blimsup (g ∘ u) f p := by
  simp only [blimsup_eq_iInf_biSup, Function.comp]
  -- ⊢ ↑g (⨅ (s : Set β) (_ : s ∈ f), ⨆ (b : β) (_ : p b ∧ b ∈ s), u b) ≤ ⨅ (s : Se …
  refine' ((OrderHomClass.mono g).map_iInf₂_le _).trans _
  -- ⊢ ⨅ (i : Set β) (_ : i ∈ f), ↑g (⨆ (b : β) (_ : p b ∧ b ∈ i), u b) ≤ ⨅ (s : Se …
  simp only [_root_.map_iSup, le_refl]
  -- 🎉 no goals
#align filter.Sup_hom.apply_blimsup_le Filter.SupHom.apply_blimsup_le

theorem InfHom.le_apply_bliminf [CompleteLattice γ] (g : sInfHom α γ) :
    bliminf (g ∘ u) f p ≤ g (bliminf u f p) :=
  SupHom.apply_blimsup_le (α := αᵒᵈ) (γ := γᵒᵈ) (sInfHom.dual g)
#align filter.Inf_hom.le_apply_bliminf Filter.InfHom.le_apply_bliminf

end CompleteLattice

section CompleteDistribLattice

variable [CompleteDistribLattice α] {f : Filter β} {p q : β → Prop} {u : β → α}

@[simp]
theorem blimsup_or_eq_sup : (blimsup u f fun x => p x ∨ q x) = blimsup u f p ⊔ blimsup u f q := by
  refine' le_antisymm _ blimsup_sup_le_or
  -- ⊢ (blimsup u f fun x => p x ∨ q x) ≤ blimsup u f p ⊔ blimsup u f q
  simp only [blimsup_eq, sInf_sup_eq, sup_sInf_eq, le_iInf₂_iff, mem_setOf_eq]
  -- ⊢ ∀ (i : α), (∀ᶠ (x : β) in f, q x → u x ≤ i) → ∀ (i_1 : α), (∀ᶠ (x : β) in f, …
  refine' fun a' ha' a ha => sInf_le ((ha.and ha').mono fun b h hb => _)
  -- ⊢ u b ≤ a ⊔ a'
  exact Or.elim hb (fun hb => le_sup_of_le_left <| h.1 hb) fun hb => le_sup_of_le_right <| h.2 hb
  -- 🎉 no goals
#align filter.blimsup_or_eq_sup Filter.blimsup_or_eq_sup

@[simp]
theorem bliminf_or_eq_inf : (bliminf u f fun x => p x ∨ q x) = bliminf u f p ⊓ bliminf u f q :=
  blimsup_or_eq_sup (α := αᵒᵈ)
#align filter.bliminf_or_eq_inf Filter.bliminf_or_eq_inf

theorem sup_limsup [NeBot f] (a : α) : a ⊔ limsup u f = limsup (fun x => a ⊔ u x) f := by
  simp only [limsup_eq_iInf_iSup, iSup_sup_eq, sup_iInf₂_eq]
  -- ⊢ ⨅ (i : Set β) (_ : i ∈ f), a ⊔ ⨆ (a : β) (_ : a ∈ i), u a = ⨅ (s : Set β) (_ …
  congr; ext s; congr; ext hs; congr
  -- ⊢ (fun i => ⨅ (_ : i ∈ f), a ⊔ ⨆ (a : β) (_ : a ∈ i), u a) = fun s => ⨅ (_ : s …
         -- ⊢ ⨅ (_ : s ∈ f), a ⊔ ⨆ (a : β) (_ : a ∈ s), u a = ⨅ (_ : s ∈ f), (⨆ (x : β) (_ …
                -- ⊢ (fun j => a ⊔ ⨆ (a : β) (_ : a ∈ s), u a) = fun x => (⨆ (x : β) (_ : x ∈ s), …
                       -- ⊢ a ⊔ ⨆ (a : β) (_ : a ∈ s), u a = (⨆ (x : β) (_ : x ∈ s), a) ⊔ ⨆ (x : β) (_ : …
                               -- ⊢ a = ⨆ (x : β) (_ : x ∈ s), a
  exact (biSup_const (nonempty_of_mem hs)).symm
  -- 🎉 no goals
#align filter.sup_limsup Filter.sup_limsup

theorem inf_liminf [NeBot f] (a : α) : a ⊓ liminf u f = liminf (fun x => a ⊓ u x) f :=
  sup_limsup (α := αᵒᵈ) a
#align filter.inf_liminf Filter.inf_liminf

theorem sup_liminf (a : α) : a ⊔ liminf u f = liminf (fun x => a ⊔ u x) f := by
  simp only [liminf_eq_iSup_iInf]
  -- ⊢ a ⊔ ⨆ (s : Set β) (_ : s ∈ f), ⨅ (a : β) (_ : a ∈ s), u a = ⨆ (s : Set β) (_ …
  rw [sup_comm, biSup_sup (⟨univ, univ_mem⟩ : ∃ i : Set β, i ∈ f)]
  -- ⊢ ⨆ (i : Set β) (_ : i ∈ f), (⨅ (a : β) (_ : a ∈ i), u a) ⊔ a = ⨆ (s : Set β)  …
  simp_rw [iInf₂_sup_eq, sup_comm (a := a)]
  -- 🎉 no goals
#align filter.sup_liminf Filter.sup_liminf

theorem inf_limsup (a : α) : a ⊓ limsup u f = limsup (fun x => a ⊓ u x) f :=
  sup_liminf (α := αᵒᵈ) a
#align filter.inf_limsup Filter.inf_limsup

end CompleteDistribLattice

section CompleteBooleanAlgebra

variable [CompleteBooleanAlgebra α] (f : Filter β) (u : β → α)

theorem limsup_compl : (limsup u f)ᶜ = liminf (compl ∘ u) f := by
  simp only [limsup_eq_iInf_iSup, compl_iInf, compl_iSup, liminf_eq_iSup_iInf, Function.comp_apply]
  -- 🎉 no goals
#align filter.limsup_compl Filter.limsup_compl

theorem liminf_compl : (liminf u f)ᶜ = limsup (compl ∘ u) f := by
  simp only [limsup_eq_iInf_iSup, compl_iInf, compl_iSup, liminf_eq_iSup_iInf, Function.comp_apply]
  -- 🎉 no goals
#align filter.liminf_compl Filter.liminf_compl

theorem limsup_sdiff (a : α) : limsup u f \ a = limsup (fun b => u b \ a) f := by
  simp only [limsup_eq_iInf_iSup, sdiff_eq]
  -- ⊢ (⨅ (s : Set β) (_ : s ∈ f), ⨆ (a : β) (_ : a ∈ s), u a) ⊓ aᶜ = ⨅ (s : Set β) …
  rw [biInf_inf (⟨univ, univ_mem⟩ : ∃ i : Set β, i ∈ f)]
  -- ⊢ ⨅ (i : Set β) (_ : i ∈ f), (⨆ (a : β) (_ : a ∈ i), u a) ⊓ aᶜ = ⨅ (s : Set β) …
  simp_rw [inf_comm, inf_iSup₂_eq, inf_comm]
  -- 🎉 no goals
#align filter.limsup_sdiff Filter.limsup_sdiff

theorem liminf_sdiff [NeBot f] (a : α) : liminf u f \ a = liminf (fun b => u b \ a) f := by
  simp only [sdiff_eq, inf_comm (b := aᶜ), inf_liminf]
  -- 🎉 no goals
#align filter.liminf_sdiff Filter.liminf_sdiff

theorem sdiff_limsup [NeBot f] (a : α) : a \ limsup u f = liminf (fun b => a \ u b) f := by
  rw [← compl_inj_iff]
  -- ⊢ (a \ limsup u f)ᶜ = (liminf (fun b => a \ u b) f)ᶜ
  simp only [sdiff_eq, liminf_compl, (· ∘ ·), compl_inf, compl_compl, sup_limsup]
  -- 🎉 no goals
#align filter.sdiff_limsup Filter.sdiff_limsup

theorem sdiff_liminf (a : α) : a \ liminf u f = limsup (fun b => a \ u b) f := by
  rw [← compl_inj_iff]
  -- ⊢ (a \ liminf u f)ᶜ = (limsup (fun b => a \ u b) f)ᶜ
  simp only [sdiff_eq, limsup_compl, (· ∘ ·), compl_inf, compl_compl, sup_liminf]
  -- 🎉 no goals
#align filter.sdiff_liminf Filter.sdiff_liminf

end CompleteBooleanAlgebra

section SetLattice

variable {p : ι → Prop} {s : ι → Set α}

theorem cofinite.blimsup_set_eq :
    blimsup s cofinite p = { x | { n | p n ∧ x ∈ s n }.Infinite } := by
  simp only [blimsup_eq, le_eq_subset, eventually_cofinite, not_forall, sInf_eq_sInter, exists_prop]
  -- ⊢ ⋂₀ {a | Set.Finite {x | p x ∧ ¬s x ⊆ a}} = {x | Set.Infinite {n | p n ∧ x ∈  …
  ext x
  -- ⊢ x ∈ ⋂₀ {a | Set.Finite {x | p x ∧ ¬s x ⊆ a}} ↔ x ∈ {x | Set.Infinite {n | p  …
  refine' ⟨fun h => _, fun hx t h => _⟩ <;> contrapose! h
  -- ⊢ x ∈ {x | Set.Infinite {n | p n ∧ x ∈ s n}}
                                            -- ⊢ ¬x ∈ ⋂₀ {a | Set.Finite {x | p x ∧ ¬s x ⊆ a}}
                                            -- ⊢ ¬t ∈ {a | Set.Finite {x | p x ∧ ¬s x ⊆ a}}
  · simp only [mem_sInter, mem_setOf_eq, not_forall, exists_prop]
    -- ⊢ ∃ x_1, Set.Finite {x | p x ∧ ¬s x ⊆ x_1} ∧ ¬x ∈ x_1
    exact ⟨{x}ᶜ, by simpa using h, by simp⟩
    -- 🎉 no goals
  · exact hx.mono fun i hi => ⟨hi.1, fun hit => h (hit hi.2)⟩
    -- 🎉 no goals
#align filter.cofinite.blimsup_set_eq Filter.cofinite.blimsup_set_eq

theorem cofinite.bliminf_set_eq : bliminf s cofinite p = { x | { n | p n ∧ x ∉ s n }.Finite } := by
  rw [← compl_inj_iff]
  -- ⊢ (bliminf s cofinite p)ᶜ = {x | Set.Finite {n | p n ∧ ¬x ∈ s n}}ᶜ
  simp only [bliminf_eq_iSup_biInf, compl_iInf, compl_iSup, ← blimsup_eq_iInf_biSup,
    cofinite.blimsup_set_eq]
  rfl
  -- 🎉 no goals
#align filter.cofinite.bliminf_set_eq Filter.cofinite.bliminf_set_eq

/-- In other words, `limsup cofinite s` is the set of elements lying inside the family `s`
infinitely often. -/
theorem cofinite.limsup_set_eq : limsup s cofinite = { x | { n | x ∈ s n }.Infinite } := by
  simp only [← cofinite.blimsup_true s, cofinite.blimsup_set_eq, true_and_iff]
  -- 🎉 no goals
#align filter.cofinite.limsup_set_eq Filter.cofinite.limsup_set_eq

/-- In other words, `liminf cofinite s` is the set of elements lying outside the family `s`
finitely often. -/
theorem cofinite.liminf_set_eq : liminf s cofinite = { x | { n | x ∉ s n }.Finite } := by
  simp only [← cofinite.bliminf_true s, cofinite.bliminf_set_eq, true_and_iff]
  -- 🎉 no goals
#align filter.cofinite.liminf_set_eq Filter.cofinite.liminf_set_eq

theorem exists_forall_mem_of_hasBasis_mem_blimsup {l : Filter β} {b : ι → Set β} {q : ι → Prop}
    (hl : l.HasBasis q b) {u : β → Set α} {p : β → Prop} {x : α} (hx : x ∈ blimsup u l p) :
    ∃ f : { i | q i } → β, ∀ i, x ∈ u (f i) ∧ p (f i) ∧ f i ∈ b i := by
  rw [blimsup_eq_iInf_biSup] at hx
  -- ⊢ ∃ f, ∀ (i : ↑{i | q i}), x ∈ u (f i) ∧ p (f i) ∧ f i ∈ b ↑i
  simp only [iSup_eq_iUnion, iInf_eq_iInter, mem_iInter, mem_iUnion, exists_prop] at hx
  -- ⊢ ∃ f, ∀ (i : ↑{i | q i}), x ∈ u (f i) ∧ p (f i) ∧ f i ∈ b ↑i
  choose g hg hg' using hx
  -- ⊢ ∃ f, ∀ (i : ↑{i | q i}), x ∈ u (f i) ∧ p (f i) ∧ f i ∈ b ↑i
  refine' ⟨fun i : { i | q i } => g (b i) (hl.mem_of_mem i.2), fun i => ⟨_, _⟩⟩
  -- ⊢ x ∈ u ((fun i => g (b ↑i) (_ : b ↑i ∈ l)) i)
  · exact hg' (b i) (hl.mem_of_mem i.2)
    -- 🎉 no goals
  · exact hg (b i) (hl.mem_of_mem i.2)
    -- 🎉 no goals
#align filter.exists_forall_mem_of_has_basis_mem_blimsup Filter.exists_forall_mem_of_hasBasis_mem_blimsup

theorem exists_forall_mem_of_hasBasis_mem_blimsup' {l : Filter β} {b : ι → Set β}
    (hl : l.HasBasis (fun _ => True) b) {u : β → Set α} {p : β → Prop} {x : α}
    (hx : x ∈ blimsup u l p) : ∃ f : ι → β, ∀ i, x ∈ u (f i) ∧ p (f i) ∧ f i ∈ b i := by
  obtain ⟨f, hf⟩ := exists_forall_mem_of_hasBasis_mem_blimsup hl hx
  -- ⊢ ∃ f, ∀ (i : ι), x ∈ u (f i) ∧ p (f i) ∧ f i ∈ b i
  exact ⟨fun i => f ⟨i, trivial⟩, fun i => hf ⟨i, trivial⟩⟩
  -- 🎉 no goals
#align filter.exists_forall_mem_of_has_basis_mem_blimsup' Filter.exists_forall_mem_of_hasBasis_mem_blimsup'

end SetLattice

section ConditionallyCompleteLinearOrder

theorem frequently_lt_of_lt_limsSup {f : Filter α} [ConditionallyCompleteLinearOrder α] {a : α}
    (hf : f.IsCobounded (· ≤ ·) := by isBoundedDefault)
    (h : a < limsSup f) : ∃ᶠ n in f, a < n := by
  contrapose! h
  -- ⊢ limsSup f ≤ a
  simp only [not_frequently, not_lt] at h
  -- ⊢ limsSup f ≤ a
  exact limsSup_le_of_le hf h
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align filter.frequently_lt_of_lt_Limsup Filter.frequently_lt_of_lt_limsSup

theorem frequently_lt_of_limsInf_lt {f : Filter α} [ConditionallyCompleteLinearOrder α] {a : α}
    (hf : f.IsCobounded (· ≥ ·) := by isBoundedDefault)
    (h : limsInf f < a) : ∃ᶠ n in f, n < a :=
  frequently_lt_of_lt_limsSup (α := OrderDual α) hf h
set_option linter.uppercaseLean3 false in
#align filter.frequently_lt_of_Liminf_lt Filter.frequently_lt_of_limsInf_lt

theorem eventually_lt_of_lt_liminf {f : Filter α} [ConditionallyCompleteLinearOrder β] {u : α → β}
    {b : β} (h : b < liminf u f)
    (hu : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) :
    ∀ᶠ a in f, b < u a := by
  obtain ⟨c, hc, hbc⟩ : ∃ (c : β) (_ : c ∈ { c : β | ∀ᶠ n : α in f, c ≤ u n }), b < c := by
    simp_rw [exists_prop]
    exact exists_lt_of_lt_csSup hu h
  exact hc.mono fun x hx => lt_of_lt_of_le hbc hx
  -- 🎉 no goals
#align filter.eventually_lt_of_lt_liminf Filter.eventually_lt_of_lt_liminf

theorem eventually_lt_of_limsup_lt {f : Filter α} [ConditionallyCompleteLinearOrder β] {u : α → β}
    {b : β} (h : limsup u f < b)
    (hu : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault) :
    ∀ᶠ a in f, u a < b :=
  eventually_lt_of_lt_liminf (β := βᵒᵈ) h hu
#align filter.eventually_lt_of_limsup_lt Filter.eventually_lt_of_limsup_lt

theorem le_limsup_of_frequently_le {α β} [ConditionallyCompleteLinearOrder β] {f : Filter α}
    {u : α → β} {b : β} (hu_le : ∃ᶠ x in f, b ≤ u x)
    (hu : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault) :
    b ≤ limsup u f := by
  revert hu_le
  -- ⊢ (∃ᶠ (x : α) in f, b ≤ u x) → b ≤ limsup u f
  rw [← not_imp_not, not_frequently]
  -- ⊢ ¬b ≤ limsup u f → ∀ᶠ (x : α) in f, ¬b ≤ u x
  simp_rw [← lt_iff_not_ge]
  -- ⊢ limsup u f < b → ∀ᶠ (x : α) in f, u x < b
  exact fun h => eventually_lt_of_limsup_lt h hu
  -- 🎉 no goals
#align filter.le_limsup_of_frequently_le Filter.le_limsup_of_frequently_le

theorem liminf_le_of_frequently_le {α β} [ConditionallyCompleteLinearOrder β] {f : Filter α}
    {u : α → β} {b : β} (hu_le : ∃ᶠ x in f, u x ≤ b)
    (hu : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) :
    liminf u f ≤ b :=
  le_limsup_of_frequently_le (β := βᵒᵈ) hu_le hu
#align filter.liminf_le_of_frequently_le Filter.liminf_le_of_frequently_le

theorem frequently_lt_of_lt_limsup {α β} [ConditionallyCompleteLinearOrder β] {f : Filter α}
    {u : α → β} {b : β}
    (hu : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h : b < limsup u f) : ∃ᶠ x in f, b < u x := by
  contrapose! h
  -- ⊢ limsup u f ≤ b
  apply limsSup_le_of_le hu
  -- ⊢ ∀ᶠ (n : β) in map u f, n ≤ b
  simpa using h
  -- 🎉 no goals
#align filter.frequently_lt_of_lt_limsup Filter.frequently_lt_of_lt_limsup

theorem frequently_lt_of_liminf_lt {α β} [ConditionallyCompleteLinearOrder β] {f : Filter α}
    {u : α → β} {b : β}
    (hu : f.IsCoboundedUnder (· ≥ ·) u := by isBoundedDefault)
    (h : liminf u f < b) : ∃ᶠ x in f, u x < b :=
  frequently_lt_of_lt_limsup (β := βᵒᵈ) hu h
#align filter.frequently_lt_of_liminf_lt Filter.frequently_lt_of_liminf_lt

end ConditionallyCompleteLinearOrder

end Filter

section Order

open Filter

theorem Monotone.isBoundedUnder_le_comp_iff [Nonempty β] [LinearOrder β] [Preorder γ] [NoMaxOrder γ]
    {g : β → γ} {f : α → β} {l : Filter α} (hg : Monotone g) (hg' : Tendsto g atTop atTop) :
    IsBoundedUnder (· ≤ ·) l (g ∘ f) ↔ IsBoundedUnder (· ≤ ·) l f := by
  refine' ⟨_, fun h => h.isBoundedUnder (α := β) hg⟩
  -- ⊢ IsBoundedUnder (fun x x_1 => x ≤ x_1) l (g ∘ f) → IsBoundedUnder (fun x x_1  …
  rintro ⟨c, hc⟩; rw [eventually_map] at hc
  -- ⊢ IsBoundedUnder (fun x x_1 => x ≤ x_1) l f
                  -- ⊢ IsBoundedUnder (fun x x_1 => x ≤ x_1) l f
  obtain ⟨b, hb⟩ : ∃ b, ∀ a ≥ b, c < g a := eventually_atTop.1 (hg'.eventually_gt_atTop c)
  -- ⊢ IsBoundedUnder (fun x x_1 => x ≤ x_1) l f
  exact ⟨b, hc.mono fun x hx => not_lt.1 fun h => (hb _ h.le).not_le hx⟩
  -- 🎉 no goals
#align monotone.is_bounded_under_le_comp Monotone.isBoundedUnder_le_comp_iff

theorem Monotone.isBoundedUnder_ge_comp_iff [Nonempty β] [LinearOrder β] [Preorder γ] [NoMinOrder γ]
    {g : β → γ} {f : α → β} {l : Filter α} (hg : Monotone g) (hg' : Tendsto g atBot atBot) :
    IsBoundedUnder (· ≥ ·) l (g ∘ f) ↔ IsBoundedUnder (· ≥ ·) l f :=
  hg.dual.isBoundedUnder_le_comp_iff hg'
#align monotone.is_bounded_under_ge_comp Monotone.isBoundedUnder_ge_comp_iff

theorem Antitone.isBoundedUnder_le_comp_iff [Nonempty β] [LinearOrder β] [Preorder γ] [NoMaxOrder γ]
    {g : β → γ} {f : α → β} {l : Filter α} (hg : Antitone g) (hg' : Tendsto g atBot atTop) :
    IsBoundedUnder (· ≤ ·) l (g ∘ f) ↔ IsBoundedUnder (· ≥ ·) l f :=
  hg.dual_right.isBoundedUnder_ge_comp_iff hg'
#align antitone.is_bounded_under_le_comp Antitone.isBoundedUnder_le_comp_iff

theorem Antitone.isBoundedUnder_ge_comp_iff [Nonempty β] [LinearOrder β] [Preorder γ] [NoMinOrder γ]
    {g : β → γ} {f : α → β} {l : Filter α} (hg : Antitone g) (hg' : Tendsto g atTop atBot) :
    IsBoundedUnder (· ≥ ·) l (g ∘ f) ↔ IsBoundedUnder (· ≤ ·) l f :=
  hg.dual_right.isBoundedUnder_le_comp_iff hg'
#align antitone.is_bounded_under_ge_comp Antitone.isBoundedUnder_ge_comp_iff

theorem GaloisConnection.l_limsup_le [ConditionallyCompleteLattice β]
    [ConditionallyCompleteLattice γ] {f : Filter α} {v : α → β} {l : β → γ} {u : γ → β}
    (gc : GaloisConnection l u)
    (hlv : f.IsBoundedUnder (· ≤ ·) fun x => l (v x) := by isBoundedDefault)
    (hv_co : f.IsCoboundedUnder (· ≤ ·) v := by isBoundedDefault) :
    l (limsup v f) ≤ limsup (fun x => l (v x)) f := by
  refine' le_limsSup_of_le hlv fun c hc => _
  -- ⊢ l (limsup v f) ≤ c
  rw [Filter.eventually_map] at hc
  -- ⊢ l (limsup v f) ≤ c
  simp_rw [gc _ _] at hc ⊢
  -- ⊢ limsup v f ≤ u c
  exact limsSup_le_of_le hv_co hc
  -- 🎉 no goals
#align galois_connection.l_limsup_le GaloisConnection.l_limsup_le

theorem OrderIso.limsup_apply {γ} [ConditionallyCompleteLattice β] [ConditionallyCompleteLattice γ]
    {f : Filter α} {u : α → β} (g : β ≃o γ)
    (hu : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault)
    (hu_co : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault)
    (hgu : f.IsBoundedUnder (· ≤ ·) fun x => g (u x) := by isBoundedDefault)
    (hgu_co : f.IsCoboundedUnder (· ≤ ·) fun x => g (u x) := by isBoundedDefault) :
    g (limsup u f) = limsup (fun x => g (u x)) f := by
  refine' le_antisymm ((OrderIso.to_galoisConnection g).l_limsup_le hgu hu_co) _
  -- ⊢ limsup (fun x => ↑g (u x)) f ≤ ↑g (limsup u f)
  rw [← g.symm.symm_apply_apply <| limsup (fun x => g (u x)) f, g.symm_symm]
  -- ⊢ ↑g (↑(symm g) (limsup (fun x => ↑g (u x)) f)) ≤ ↑g (limsup u f)
  refine' g.monotone _
  -- ⊢ ↑(symm g) (limsup (fun x => ↑g (u x)) f) ≤ limsup u f
  have hf : u = fun i => g.symm (g (u i)) := funext fun i => (g.symm_apply_apply (u i)).symm
  -- ⊢ ↑(symm g) (limsup (fun x => ↑g (u x)) f) ≤ limsup u f
  -- Porting note: nth_rw 1 to nth_rw 2
  nth_rw 2 [hf]
  -- ⊢ ↑(symm g) (limsup (fun x => ↑g (u x)) f) ≤ limsup (fun i => ↑(symm g) (↑g (u …
  refine' (OrderIso.to_galoisConnection g.symm).l_limsup_le _ hgu_co
  -- ⊢ IsBoundedUnder (fun x x_1 => x ≤ x_1) f fun x => ↑(symm g) (↑g (u x))
  simp_rw [g.symm_apply_apply]
  -- ⊢ IsBoundedUnder (fun x x_1 => x ≤ x_1) f fun x => u x
  exact hu
  -- 🎉 no goals
#align order_iso.limsup_apply OrderIso.limsup_apply

theorem OrderIso.liminf_apply {γ} [ConditionallyCompleteLattice β] [ConditionallyCompleteLattice γ]
    {f : Filter α} {u : α → β} (g : β ≃o γ)
    (hu : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault)
    (hu_co : f.IsCoboundedUnder (· ≥ ·) u := by isBoundedDefault)
    (hgu : f.IsBoundedUnder (· ≥ ·) fun x => g (u x) := by isBoundedDefault)
    (hgu_co : f.IsCoboundedUnder (· ≥ ·) fun x => g (u x) := by isBoundedDefault) :
    g (liminf u f) = liminf (fun x => g (u x)) f :=
  OrderIso.limsup_apply (β := βᵒᵈ) (γ := γᵒᵈ) g.dual hu hu_co hgu hgu_co
#align order_iso.liminf_apply OrderIso.liminf_apply

end Order
