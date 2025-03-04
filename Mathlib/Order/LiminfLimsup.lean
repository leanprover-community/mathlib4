/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Johannes Hölzl, Rémy Degenne
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Unbundled
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

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

open Filter Set Function

variable {α β γ ι ι' : Type*}

namespace Filter

section Relation

variable {r : α → α → Prop} {f g : Filter α}

/-- `f` is eventually bounded if and only if, there exists an admissible set on which it is
bounded. -/
theorem isBounded_iff : f.IsBounded r ↔ ∃ s ∈ f.sets, ∃ b, s ⊆ { x | r x b } :=
  Iff.intro (fun ⟨b, hb⟩ => ⟨{ a | r a b }, hb, b, Subset.refl _⟩) fun ⟨_, hs, b, hb⟩ =>
    ⟨b, mem_of_superset hs hb⟩

/-- A bounded function `u` is in particular eventually bounded. -/
theorem isBoundedUnder_of {f : Filter β} {u : β → α} : (∃ b, ∀ x, r (u x) b) → f.IsBoundedUnder r u
  | ⟨b, hb⟩ => ⟨b, show ∀ᶠ x in f, r (u x) b from Eventually.of_forall hb⟩

theorem isBounded_bot : IsBounded r ⊥ ↔ Nonempty α := by simp [IsBounded, exists_true_iff_nonempty]

theorem isBounded_top : IsBounded r ⊤ ↔ ∃ t, ∀ x, r x t := by simp [IsBounded, eq_univ_iff_forall]

theorem isBounded_principal (s : Set α) : IsBounded r (𝓟 s) ↔ ∃ t, ∀ x ∈ s, r x t := by
  simp [IsBounded, subset_def]

theorem isBounded_sup [IsTrans α r] [IsDirected α r] :
    IsBounded r f → IsBounded r g → IsBounded r (f ⊔ g)
  | ⟨b₁, h₁⟩, ⟨b₂, h₂⟩ =>
    let ⟨b, rb₁b, rb₂b⟩ := directed_of r b₁ b₂
    ⟨b, eventually_sup.mpr
      ⟨h₁.mono fun _ h => _root_.trans h rb₁b, h₂.mono fun _ h => _root_.trans h rb₂b⟩⟩

theorem IsBounded.mono (h : f ≤ g) : IsBounded r g → IsBounded r f
  | ⟨b, hb⟩ => ⟨b, h hb⟩

theorem IsBoundedUnder.mono {f g : Filter β} {u : β → α} (h : f ≤ g) :
    g.IsBoundedUnder r u → f.IsBoundedUnder r u := fun hg => IsBounded.mono (map_mono h) hg

theorem IsBoundedUnder.mono_le [Preorder β] {l : Filter α} {u v : α → β}
    (hu : IsBoundedUnder (· ≤ ·) l u) (hv : v ≤ᶠ[l] u) : IsBoundedUnder (· ≤ ·) l v := by
  apply hu.imp
  exact fun b hb => (eventually_map.1 hb).mp <| hv.mono fun x => le_trans

theorem IsBoundedUnder.mono_ge [Preorder β] {l : Filter α} {u v : α → β}
    (hu : IsBoundedUnder (· ≥ ·) l u) (hv : u ≤ᶠ[l] v) : IsBoundedUnder (· ≥ ·) l v :=
  IsBoundedUnder.mono_le (β := βᵒᵈ) hu hv

theorem isBoundedUnder_const [IsRefl α r] {l : Filter β} {a : α} : IsBoundedUnder r l fun _ => a :=
  ⟨a, eventually_map.2 <| Eventually.of_forall fun _ => refl _⟩

theorem IsBounded.isBoundedUnder {q : β → β → Prop} {u : α → β}
    (hu : ∀ a₀ a₁, r a₀ a₁ → q (u a₀) (u a₁)) : f.IsBounded r → f.IsBoundedUnder q u
  | ⟨b, h⟩ => ⟨u b, show ∀ᶠ x in f, q (u x) (u b) from h.mono fun x => hu x b⟩

theorem IsBoundedUnder.comp {l : Filter γ} {q : β → β → Prop} {u : γ → α} {v : α → β}
    (hv : ∀ a₀ a₁, r a₀ a₁ → q (v a₀) (v a₁)) : l.IsBoundedUnder r u → l.IsBoundedUnder q (v ∘ u)
  | ⟨a, h⟩ => ⟨v a, show ∀ᶠ x in map u l, q (v x) (v a) from h.mono fun x => hv x a⟩

lemma isBoundedUnder_map_iff {ι κ X : Type*} {r : X → X → Prop} {f : ι → X} {φ : κ → ι}
    {𝓕 : Filter κ} :
    (map φ 𝓕).IsBoundedUnder r f ↔ 𝓕.IsBoundedUnder r (f ∘ φ) :=
  Iff.rfl

lemma Tendsto.isBoundedUnder_comp {ι κ X : Type*} {r : X → X → Prop} {f : ι → X} {φ : κ → ι}
    {𝓕 : Filter ι} {𝓖 : Filter κ} (φ_tendsto : Tendsto φ 𝓖 𝓕) (𝓕_bounded : 𝓕.IsBoundedUnder r f) :
    𝓖.IsBoundedUnder r (f ∘ φ) :=
  isBoundedUnder_map_iff.mp (𝓕_bounded.mono φ_tendsto)

section Preorder
variable [Preorder α] {f : Filter β} {u : β → α} {s : Set β}

lemma IsBoundedUnder.eventually_le (h : IsBoundedUnder (· ≤ ·) f u) :
    ∃ a, ∀ᶠ x in f, u x ≤ a := by
  obtain ⟨a, ha⟩ := h
  use a
  exact eventually_map.1 ha

lemma IsBoundedUnder.eventually_ge (h : IsBoundedUnder (· ≥ ·) f u) :
    ∃ a, ∀ᶠ x in f, a ≤ u x :=
  IsBoundedUnder.eventually_le (α := αᵒᵈ) h

lemma isBoundedUnder_of_eventually_le {a : α} (h : ∀ᶠ x in f, u x ≤ a) :
    IsBoundedUnder (· ≤ ·) f u := ⟨a, h⟩

lemma isBoundedUnder_of_eventually_ge {a : α} (h : ∀ᶠ x in f, a ≤ u x) :
    IsBoundedUnder (· ≥ ·) f u := ⟨a, h⟩

lemma isBoundedUnder_iff_eventually_bddAbove :
    f.IsBoundedUnder (· ≤ ·) u ↔ ∃ s, BddAbove (u '' s) ∧ ∀ᶠ x in f, x ∈ s := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨{a | u a ≤ b}, ⟨b, by rintro _ ⟨a, ha, rfl⟩; exact ha⟩, hb⟩
  · rintro ⟨s, ⟨b, hb⟩, hs⟩
    exact ⟨b, hs.mono <| by simpa [upperBounds] using hb⟩

lemma isBoundedUnder_iff_eventually_bddBelow :
    f.IsBoundedUnder (· ≥ ·) u ↔ ∃ s, BddBelow (u '' s) ∧ ∀ᶠ x in f, x ∈ s :=
  isBoundedUnder_iff_eventually_bddAbove (α := αᵒᵈ)

lemma _root_.BddAbove.isBoundedUnder (hs : s ∈ f) (hu : BddAbove (u '' s)) :
    f.IsBoundedUnder (· ≤ ·) u := isBoundedUnder_iff_eventually_bddAbove.2 ⟨_, hu, hs⟩

/-- A bounded above function `u` is in particular eventually bounded above. -/
lemma _root_.BddAbove.isBoundedUnder_of_range (hu : BddAbove (Set.range u)) :
    f.IsBoundedUnder (· ≤ ·) u := BddAbove.isBoundedUnder (s := univ) f.univ_mem (by simpa)

lemma _root_.BddBelow.isBoundedUnder (hs : s ∈ f) (hu : BddBelow (u '' s)) :
    f.IsBoundedUnder (· ≥ ·) u := isBoundedUnder_iff_eventually_bddBelow.2 ⟨_, hu, hs⟩

/-- A bounded below function `u` is in particular eventually bounded below. -/
lemma _root_.BddBelow.isBoundedUnder_of_range (hu : BddBelow (Set.range u)) :
    f.IsBoundedUnder (· ≥ ·) u := BddBelow.isBoundedUnder (s := univ) f.univ_mem (by simpa)

lemma IsBoundedUnder.le_of_finite [Nonempty α] [IsDirected α (· ≤ ·)] [Finite β]
    {f : Filter β} {u : β → α} : IsBoundedUnder (· ≤ ·) f u :=
  (Set.toFinite _).bddAbove.isBoundedUnder_of_range

lemma IsBoundedUnder.ge_of_finite [Nonempty α] [IsDirected α (· ≥ ·)] [Finite β]
    {f : Filter β} {u : β → α} : IsBoundedUnder (· ≥ ·) f u :=
  (Set.toFinite _).bddBelow.isBoundedUnder_of_range

end Preorder

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
  rw [eventually_map] at hb
  obtain ⟨b', h⟩ := exists_gt b
  have hb' := (tendsto_atTop.mp hf) b'
  have : { x : α | f x ≤ b } ∩ { x : α | b' ≤ f x } = ∅ :=
    eq_empty_of_subset_empty fun x hx => (not_le_of_lt h) (le_trans hx.2 hx.1)
  exact (nonempty_of_mem (hb.and hb')).ne_empty this

theorem not_isBoundedUnder_of_tendsto_atBot [Preorder β] [NoMinOrder β] {f : α → β} {l : Filter α}
    [l.NeBot] (hf : Tendsto f l atBot) : ¬IsBoundedUnder (· ≥ ·) l f :=
  not_isBoundedUnder_of_tendsto_atTop (β := βᵒᵈ) hf

theorem IsBoundedUnder.bddAbove_range_of_cofinite [Preorder β] [IsDirected β (· ≤ ·)] {f : α → β}
    (hf : IsBoundedUnder (· ≤ ·) cofinite f) : BddAbove (range f) := by
  rcases hf with ⟨b, hb⟩
  haveI : Nonempty β := ⟨b⟩
  rw [← image_univ, ← union_compl_self { x | f x ≤ b }, image_union, bddAbove_union]
  exact ⟨⟨b, forall_mem_image.2 fun x => id⟩, (hb.image f).bddAbove⟩

theorem IsBoundedUnder.bddBelow_range_of_cofinite [Preorder β] [IsDirected β (· ≥ ·)] {f : α → β}
    (hf : IsBoundedUnder (· ≥ ·) cofinite f) : BddBelow (range f) :=
  IsBoundedUnder.bddAbove_range_of_cofinite (β := βᵒᵈ) hf

theorem IsBoundedUnder.bddAbove_range [Preorder β] [IsDirected β (· ≤ ·)] {f : ℕ → β}
    (hf : IsBoundedUnder (· ≤ ·) atTop f) : BddAbove (range f) := by
  rw [← Nat.cofinite_eq_atTop] at hf
  exact hf.bddAbove_range_of_cofinite

theorem IsBoundedUnder.bddBelow_range [Preorder β] [IsDirected β (· ≥ ·)] {f : ℕ → β}
    (hf : IsBoundedUnder (· ≥ ·) atTop f) : BddBelow (range f) :=
  IsBoundedUnder.bddAbove_range (β := βᵒᵈ) hf

/-- To check that a filter is frequently bounded, it suffices to have a witness
which bounds `f` at some point for every admissible set.

This is only an implication, as the other direction is wrong for the trivial filter. -/
theorem IsCobounded.mk [IsTrans α r] (a : α) (h : ∀ s ∈ f, ∃ x ∈ s, r a x) : f.IsCobounded r :=
  ⟨a, fun _ s =>
    let ⟨_, h₁, h₂⟩ := h _ s
    _root_.trans h₂ h₁⟩

/-- A filter which is eventually bounded is in particular frequently bounded (in the opposite
direction). At least if the filter is not trivial. -/
theorem IsBounded.isCobounded_flip [IsTrans α r] [NeBot f] : f.IsBounded r → f.IsCobounded (flip r)
  | ⟨a, ha⟩ =>
    ⟨a, fun b hb =>
      let ⟨_, rxa, rbx⟩ := (ha.and hb).exists
      show r b a from _root_.trans rbx rxa⟩

theorem IsBounded.isCobounded_ge [Preorder α] [NeBot f] (h : f.IsBounded (· ≤ ·)) :
    f.IsCobounded (· ≥ ·) :=
  h.isCobounded_flip

theorem IsBounded.isCobounded_le [Preorder α] [NeBot f] (h : f.IsBounded (· ≥ ·)) :
    f.IsCobounded (· ≤ ·) :=
  h.isCobounded_flip

theorem IsBoundedUnder.isCoboundedUnder_flip {u : γ → α} {l : Filter γ} [IsTrans α r] [NeBot l]
    (h : l.IsBoundedUnder r u) : l.IsCoboundedUnder (flip r) u :=
  h.isCobounded_flip

theorem IsBoundedUnder.isCoboundedUnder_le {u : γ → α} {l : Filter γ} [Preorder α] [NeBot l]
    (h : l.IsBoundedUnder (· ≥ ·) u) : l.IsCoboundedUnder (· ≤ ·) u :=
  h.isCoboundedUnder_flip

theorem IsBoundedUnder.isCoboundedUnder_ge {u : γ → α} {l : Filter γ} [Preorder α] [NeBot l]
    (h : l.IsBoundedUnder (· ≤ ·) u) : l.IsCoboundedUnder (· ≥ ·) u :=
  h.isCoboundedUnder_flip

lemma isCoboundedUnder_le_of_eventually_le [Preorder α] (l : Filter ι) [NeBot l] {f : ι → α} {x : α}
    (hf : ∀ᶠ i in l, x ≤ f i) :
    IsCoboundedUnder (· ≤ ·) l f :=
  IsBoundedUnder.isCoboundedUnder_le ⟨x, hf⟩

lemma isCoboundedUnder_ge_of_eventually_le [Preorder α] (l : Filter ι) [NeBot l] {f : ι → α} {x : α}
    (hf : ∀ᶠ i in l, f i ≤ x) :
    IsCoboundedUnder (· ≥ ·) l f :=
  IsBoundedUnder.isCoboundedUnder_ge ⟨x, hf⟩

lemma isCoboundedUnder_le_of_le [Preorder α] (l : Filter ι) [NeBot l] {f : ι → α} {x : α}
    (hf : ∀ i, x ≤ f i) :
    IsCoboundedUnder (· ≤ ·) l f :=
  isCoboundedUnder_le_of_eventually_le l (Eventually.of_forall hf)

lemma isCoboundedUnder_ge_of_le [Preorder α] (l : Filter ι) [NeBot l] {f : ι → α} {x : α}
    (hf : ∀ i, f i ≤ x) :
    IsCoboundedUnder (· ≥ ·) l f :=
  isCoboundedUnder_ge_of_eventually_le l (Eventually.of_forall hf)

theorem isCobounded_bot : IsCobounded r ⊥ ↔ ∃ b, ∀ x, r b x := by simp [IsCobounded]

theorem isCobounded_top : IsCobounded r ⊤ ↔ Nonempty α := by
  simp +contextual [IsCobounded, eq_univ_iff_forall,
    exists_true_iff_nonempty]

theorem isCobounded_principal (s : Set α) :
    (𝓟 s).IsCobounded r ↔ ∃ b, ∀ a, (∀ x ∈ s, r x a) → r b a := by simp [IsCobounded, subset_def]

theorem IsCobounded.mono (h : f ≤ g) : f.IsCobounded r → g.IsCobounded r
  | ⟨b, hb⟩ => ⟨b, fun a ha => hb a (h ha)⟩

/-- For nontrivial filters in linear orders, coboundedness for `≤` implies frequent boundedness
from below. -/
lemma IsCobounded.frequently_ge [LinearOrder α] [NeBot f] (cobdd : IsCobounded (· ≤ ·) f) :
    ∃ l, ∃ᶠ x in f, l ≤ x := by
  obtain ⟨t, ht⟩ := cobdd
  rcases isBot_or_exists_lt t with tbot | ⟨t', ht'⟩
  · exact ⟨t, .of_forall fun r ↦ tbot r⟩
  refine ⟨t', fun ev ↦ ?_⟩
  specialize ht t' (by filter_upwards [ev] with _ h using (not_le.mp h).le)
  exact not_lt_of_le ht ht'

/-- For nontrivial filters in linear orders, coboundedness for `≥` implies frequent boundedness
from above. -/
lemma IsCobounded.frequently_le [LinearOrder α] [NeBot f] (cobdd : IsCobounded (· ≥ ·) f) :
    ∃ u, ∃ᶠ x in f, x ≤ u :=
  cobdd.frequently_ge (α := αᵒᵈ)

/-- In linear orders, frequent boundedness from below implies coboundedness for `≤`. -/
lemma IsCobounded.of_frequently_ge [LinearOrder α] {l : α} (freq_ge : ∃ᶠ x in f, l ≤ x) :
    IsCobounded (· ≤ ·) f := by
  rcases isBot_or_exists_lt l with lbot | ⟨l', hl'⟩
  · exact ⟨l, fun x _ ↦ lbot x⟩
  refine ⟨l', fun u hu ↦ ?_⟩
  obtain ⟨w, l_le_w, w_le_u⟩ := (freq_ge.and_eventually hu).exists
  exact hl'.le.trans (l_le_w.trans w_le_u)

/-- In linear orders, frequent boundedness from above implies coboundedness for `≥`. -/
lemma IsCobounded.of_frequently_le [LinearOrder α] {u : α} (freq_le : ∃ᶠ r in f, r ≤ u) :
    IsCobounded (· ≥ ·) f :=
  IsCobounded.of_frequently_ge (α := αᵒᵈ) freq_le

lemma IsCoboundedUnder.frequently_ge [LinearOrder α] {f : Filter ι} [NeBot f] {u : ι → α}
    (h : IsCoboundedUnder (· ≤ ·) f u) :
    ∃ a, ∃ᶠ x in f, a ≤ u x :=
  IsCobounded.frequently_ge h

lemma IsCoboundedUnder.frequently_le [LinearOrder α] {f : Filter ι} [NeBot f] {u : ι → α}
    (h : IsCoboundedUnder (· ≥ ·) f u) :
    ∃ a, ∃ᶠ x in f, u x ≤ a :=
  IsCobounded.frequently_le h

lemma IsCoboundedUnder.of_frequently_ge [LinearOrder α] {f : Filter ι} {u : ι → α}
    {a : α} (freq_ge : ∃ᶠ x in f, a ≤ u x) :
    IsCoboundedUnder (· ≤ ·) f u :=
  IsCobounded.of_frequently_ge freq_ge

lemma IsCoboundedUnder.of_frequently_le [LinearOrder α] {f : Filter ι} {u : ι → α}
    {a : α} (freq_le : ∃ᶠ x in f, u x ≤ a) :
    IsCoboundedUnder (· ≥ ·) f u :=
  IsCobounded.of_frequently_le freq_le

end Relation

section add_and_sum

open Filter Set

variable {α : Type*} {f : Filter α}
variable {R : Type*}

lemma isBoundedUnder_sum {κ : Type*} [AddCommMonoid R] {r : R → R → Prop}
    (hr : ∀ (v₁ v₂ : α → R), f.IsBoundedUnder r v₁ → f.IsBoundedUnder r v₂
      → f.IsBoundedUnder r (v₁ + v₂)) (hr₀ : r 0 0)
    {u : κ → α → R} (s : Finset κ) (h : ∀ k ∈ s, f.IsBoundedUnder r (u k)) :
    f.IsBoundedUnder r (∑ k ∈ s, u k) := by
  induction s using Finset.cons_induction
  case empty =>
    rw [Finset.sum_empty]
    exact ⟨0, by simp_all only [eventually_map, Pi.zero_apply, eventually_true]⟩
  case cons k₀ s k₀_notin_s ih =>
    simp only [Finset.forall_mem_cons] at *
    simpa only [Finset.sum_cons] using hr _ _ h.1 (ih h.2)

variable [Preorder R]

lemma isBoundedUnder_ge_add [Add R] [AddLeftMono R] [AddRightMono R]
    {u v : α → R} (u_bdd_ge : f.IsBoundedUnder (· ≥ ·) u) (v_bdd_ge : f.IsBoundedUnder (· ≥ ·) v) :
    f.IsBoundedUnder (· ≥ ·) (u + v) := by
  obtain ⟨U, hU⟩ := u_bdd_ge
  obtain ⟨V, hV⟩ := v_bdd_ge
  use U + V
  simp only [eventually_map, Pi.add_apply] at hU hV ⊢
  filter_upwards [hU, hV] with a hu hv using add_le_add hu hv

lemma isBoundedUnder_le_add [Add R] [AddLeftMono R] [AddRightMono R]
    {u v : α → R} (u_bdd_le : f.IsBoundedUnder (· ≤ ·) u) (v_bdd_le : f.IsBoundedUnder (· ≤ ·) v) :
    f.IsBoundedUnder (· ≤ ·) (u + v) := by
  obtain ⟨U, hU⟩ := u_bdd_le
  obtain ⟨V, hV⟩ := v_bdd_le
  use U + V
  simp only [eventually_map, Pi.add_apply] at hU hV ⊢
  filter_upwards [hU, hV] with a hu hv using add_le_add hu hv

lemma isBoundedUnder_le_sum {κ : Type*} [AddCommMonoid R] [AddLeftMono R] [AddRightMono R]
    {u : κ → α → R} (s : Finset κ) :
    (∀ k ∈ s, f.IsBoundedUnder (· ≤ ·) (u k)) → f.IsBoundedUnder (· ≤ ·) (∑ k ∈ s, u k) :=
  fun h ↦ isBoundedUnder_sum (fun _ _ ↦ isBoundedUnder_le_add) le_rfl s h

lemma isBoundedUnder_ge_sum {κ : Type*} [AddCommMonoid R] [AddLeftMono R] [AddRightMono R]
    {u : κ → α → R} (s : Finset κ) :
    (∀ k ∈ s, f.IsBoundedUnder (· ≥ ·) (u k)) →
      f.IsBoundedUnder (· ≥ ·) (∑ k ∈ s, u k) :=
  fun h ↦ isBoundedUnder_sum (fun _ _ ↦ isBoundedUnder_ge_add) le_rfl s h

end add_and_sum

section add_and_sum

variable {α : Type*} {R : Type*} [LinearOrder R] [Add R] {f : Filter α} [f.NeBot]
  [CovariantClass R R (fun a b ↦ a + b) (· ≤ ·)] [CovariantClass R R (fun a b ↦ b + a) (· ≤ ·)]
  {u v : α → R}

lemma isCoboundedUnder_ge_add (hu : f.IsBoundedUnder (· ≤ ·) u)
    (hv : f.IsCoboundedUnder (· ≥ ·) v) :
    f.IsCoboundedUnder (· ≥ ·) (u + v) := by
  obtain ⟨U, hU⟩ := hu.eventually_le
  obtain ⟨V, hV⟩ := hv.frequently_le
  apply IsCoboundedUnder.of_frequently_le (a := U + V)
  exact (hV.and_eventually hU).mono fun x hx ↦ add_le_add hx.2 hx.1

lemma isCoboundedUnder_le_add (hu : f.IsBoundedUnder (· ≥ ·) u)
    (hv : f.IsCoboundedUnder (· ≤ ·) v) :
    f.IsCoboundedUnder (· ≤ ·) (u + v) := by
  obtain ⟨U, hU⟩ := hu.eventually_ge
  obtain ⟨V, hV⟩ := hv.frequently_ge
  apply IsCoboundedUnder.of_frequently_ge (a := U + V)
  exact (hV.and_eventually hU).mono fun x hx ↦ add_le_add hx.2 hx.1

end add_and_sum

section mul

lemma isBoundedUnder_le_mul_of_nonneg [Mul α] [Zero α] [Preorder α] [PosMulMono α]
    [MulPosMono α] {f : Filter ι} {u v : ι → α} (h₁ : 0 ≤ᶠ[f] u)
    (h₂ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f u)
    (h₃ : 0 ≤ᶠ[f] v)
    (h₄ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f v) :
    IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f (u * v) := by
  obtain ⟨U, hU⟩ := h₂.eventually_le
  obtain ⟨V, hV⟩ := h₄.eventually_le
  refine isBoundedUnder_of_eventually_le (a := U * V) ?_
  filter_upwards [hU, hV, h₁, h₃] with x x_U x_V u_0 v_0
  exact mul_le_mul x_U x_V v_0 (u_0.trans x_U)

lemma isCoboundedUnder_ge_mul_of_nonneg [Mul α] [Zero α] [LinearOrder α] [PosMulMono α]
    [MulPosMono α] {f : Filter ι} [f.NeBot] {u v : ι → α} (h₁ : 0 ≤ᶠ[f] u)
    (h₂ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f u)
    (h₃ : 0 ≤ᶠ[f] v)
    (h₄ : IsCoboundedUnder (fun x1 x2 ↦ x1 ≥ x2) f v) :
    IsCoboundedUnder (fun x1 x2 ↦ x1 ≥ x2) f (u * v) := by
  obtain ⟨U, hU⟩ := h₂.eventually_le
  obtain ⟨V, hV⟩ := h₄.frequently_le
  exact IsCoboundedUnder.of_frequently_le (a := U * V)
    <| (hV.and_eventually (hU.and (h₁.and h₃))).mono fun x ⟨x_V, x_U, u_0, v_0⟩ ↦
    mul_le_mul x_U x_V v_0 (u_0.trans x_U)

end mul

section Nonempty
variable [Preorder α] [Nonempty α] {f : Filter β} {u : β → α}

theorem isBounded_le_atBot : (atBot : Filter α).IsBounded (· ≤ ·) :=
  ‹Nonempty α›.elim fun a => ⟨a, eventually_le_atBot _⟩

theorem isBounded_ge_atTop : (atTop : Filter α).IsBounded (· ≥ ·) :=
  ‹Nonempty α›.elim fun a => ⟨a, eventually_ge_atTop _⟩

theorem Tendsto.isBoundedUnder_le_atBot (h : Tendsto u f atBot) : f.IsBoundedUnder (· ≤ ·) u :=
  isBounded_le_atBot.mono h

theorem Tendsto.isBoundedUnder_ge_atTop (h : Tendsto u f atTop) : f.IsBoundedUnder (· ≥ ·) u :=
  isBounded_ge_atTop.mono h

theorem bddAbove_range_of_tendsto_atTop_atBot [IsDirected α (· ≤ ·)] {u : ℕ → α}
    (hx : Tendsto u atTop atBot) : BddAbove (Set.range u) :=
  hx.isBoundedUnder_le_atBot.bddAbove_range

theorem bddBelow_range_of_tendsto_atTop_atTop [IsDirected α (· ≥ ·)] {u : ℕ → α}
    (hx : Tendsto u atTop atTop) : BddBelow (Set.range u) :=
  hx.isBoundedUnder_ge_atTop.bddBelow_range

end Nonempty

theorem isCobounded_le_of_bot [LE α] [OrderBot α] {f : Filter α} : f.IsCobounded (· ≤ ·) :=
  ⟨⊥, fun _ _ => bot_le⟩

theorem isCobounded_ge_of_top [LE α] [OrderTop α] {f : Filter α} : f.IsCobounded (· ≥ ·) :=
  ⟨⊤, fun _ _ => le_top⟩

theorem isBounded_le_of_top [LE α] [OrderTop α] {f : Filter α} : f.IsBounded (· ≤ ·) :=
  ⟨⊤, Eventually.of_forall fun _ => le_top⟩

theorem isBounded_ge_of_bot [LE α] [OrderBot α] {f : Filter α} : f.IsBounded (· ≥ ·) :=
  ⟨⊥, Eventually.of_forall fun _ => bot_le⟩

@[simp]
theorem _root_.OrderIso.isBoundedUnder_le_comp [LE α] [LE β] (e : α ≃o β) {l : Filter γ}
    {u : γ → α} : (IsBoundedUnder (· ≤ ·) l fun x => e (u x)) ↔ IsBoundedUnder (· ≤ ·) l u :=
  (Function.Surjective.exists e.surjective).trans <|
    exists_congr fun a => by simp only [eventually_map, e.le_iff_le]

@[simp]
theorem _root_.OrderIso.isBoundedUnder_ge_comp [Preorder α] [Preorder β] (e : α ≃o β) {l : Filter γ}
    {u : γ → α} : (IsBoundedUnder (· ≥ ·) l fun x => e (u x)) ↔ IsBoundedUnder (· ≥ ·) l u :=
  OrderIso.isBoundedUnder_le_comp e.dual

@[to_additive (attr := simp)]
theorem isBoundedUnder_le_inv [OrderedCommGroup α] {l : Filter β} {u : β → α} :
    (IsBoundedUnder (· ≤ ·) l fun x => (u x)⁻¹) ↔ IsBoundedUnder (· ≥ ·) l u :=
  (OrderIso.inv α).isBoundedUnder_ge_comp

@[to_additive (attr := simp)]
theorem isBoundedUnder_ge_inv [OrderedCommGroup α] {l : Filter β} {u : β → α} :
    (IsBoundedUnder (· ≥ ·) l fun x => (u x)⁻¹) ↔ IsBoundedUnder (· ≤ ·) l u :=
  (OrderIso.inv α).isBoundedUnder_le_comp

theorem IsBoundedUnder.sup [SemilatticeSup α] {f : Filter β} {u v : β → α} :
    f.IsBoundedUnder (· ≤ ·) u →
      f.IsBoundedUnder (· ≤ ·) v → f.IsBoundedUnder (· ≤ ·) fun a => u a ⊔ v a
  | ⟨bu, (hu : ∀ᶠ x in f, u x ≤ bu)⟩, ⟨bv, (hv : ∀ᶠ x in f, v x ≤ bv)⟩ =>
    ⟨bu ⊔ bv, show ∀ᶠ x in f, u x ⊔ v x ≤ bu ⊔ bv
      by filter_upwards [hu, hv] with _ using sup_le_sup⟩

@[simp]
theorem isBoundedUnder_le_sup [SemilatticeSup α] {f : Filter β} {u v : β → α} :
    (f.IsBoundedUnder (· ≤ ·) fun a => u a ⊔ v a) ↔
      f.IsBoundedUnder (· ≤ ·) u ∧ f.IsBoundedUnder (· ≤ ·) v :=
  ⟨fun h =>
    ⟨h.mono_le <| Eventually.of_forall fun _ => le_sup_left,
      h.mono_le <| Eventually.of_forall fun _ => le_sup_right⟩,
    fun h => h.1.sup h.2⟩

theorem IsBoundedUnder.inf [SemilatticeInf α] {f : Filter β} {u v : β → α} :
    f.IsBoundedUnder (· ≥ ·) u →
      f.IsBoundedUnder (· ≥ ·) v → f.IsBoundedUnder (· ≥ ·) fun a => u a ⊓ v a :=
  IsBoundedUnder.sup (α := αᵒᵈ)

@[simp]
theorem isBoundedUnder_ge_inf [SemilatticeInf α] {f : Filter β} {u v : β → α} :
    (f.IsBoundedUnder (· ≥ ·) fun a => u a ⊓ v a) ↔
      f.IsBoundedUnder (· ≥ ·) u ∧ f.IsBoundedUnder (· ≥ ·) v :=
  isBoundedUnder_le_sup (α := αᵒᵈ)

theorem isBoundedUnder_le_abs [LinearOrderedAddCommGroup α] {f : Filter β} {u : β → α} :
    (f.IsBoundedUnder (· ≤ ·) fun a => |u a|) ↔
      f.IsBoundedUnder (· ≤ ·) u ∧ f.IsBoundedUnder (· ≥ ·) u :=
  isBoundedUnder_le_sup.trans <| and_congr Iff.rfl isBoundedUnder_le_neg

/-- Filters are automatically bounded or cobounded in complete lattices. To use the same statements
in complete and conditionally complete lattices but let automation fill automatically the
boundedness proofs in complete lattices, we use the tactic `isBoundedDefault` in the statements,
in the form `(hf : f.IsBounded (≥) := by isBoundedDefault)`. -/

macro "isBoundedDefault" : tactic =>
  `(tactic| first
    | apply isCobounded_le_of_bot
    | apply isCobounded_ge_of_top
    | apply isBounded_le_of_top
    | apply isBounded_ge_of_bot
    | assumption)

-- Porting note: The above is a lean 4 reconstruction of (note that applyc is not available (yet?)):
-- unsafe def is_bounded_default : tactic Unit :=
--   tactic.applyc `` is_cobounded_le_of_bot <|>
--     tactic.applyc `` is_cobounded_ge_of_top <|>
--       tactic.applyc `` is_bounded_le_of_top <|> tactic.applyc `` is_bounded_ge_of_bot


section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] {s : Set α} {u : β → α}

-- Porting note: Renamed from Limsup and Liminf to limsSup and limsInf
/-- The `limsSup` of a filter `f` is the infimum of the `a` such that, eventually for `f`,
holds `x ≤ a`. -/
def limsSup (f : Filter α) : α :=
  sInf { a | ∀ᶠ n in f, n ≤ a }

/-- The `limsInf` of a filter `f` is the supremum of the `a` such that, eventually for `f`,
holds `x ≥ a`. -/
def limsInf (f : Filter α) : α :=
  sSup { a | ∀ᶠ n in f, a ≤ n }

/-- The `limsup` of a function `u` along a filter `f` is the infimum of the `a` such that,
eventually for `f`, holds `u x ≤ a`. -/
def limsup (u : β → α) (f : Filter β) : α :=
  limsSup (map u f)

/-- The `liminf` of a function `u` along a filter `f` is the supremum of the `a` such that,
eventually for `f`, holds `u x ≥ a`. -/
def liminf (u : β → α) (f : Filter β) : α :=
  limsInf (map u f)

/-- The `blimsup` of a function `u` along a filter `f`, bounded by a predicate `p`, is the infimum
of the `a` such that, eventually for `f`, `u x ≤ a` whenever `p x` holds. -/
def blimsup (u : β → α) (f : Filter β) (p : β → Prop) :=
  sInf { a | ∀ᶠ x in f, p x → u x ≤ a }

/-- The `bliminf` of a function `u` along a filter `f`, bounded by a predicate `p`, is the supremum
of the `a` such that, eventually for `f`, `a ≤ u x` whenever `p x` holds. -/
def bliminf (u : β → α) (f : Filter β) (p : β → Prop) :=
  sSup { a | ∀ᶠ x in f, p x → a ≤ u x }

section

variable {f : Filter β} {u : β → α} {p : β → Prop}

theorem limsup_eq : limsup u f = sInf { a | ∀ᶠ n in f, u n ≤ a } :=
  rfl

theorem liminf_eq : liminf u f = sSup { a | ∀ᶠ n in f, a ≤ u n } :=
  rfl

theorem blimsup_eq : blimsup u f p = sInf { a | ∀ᶠ x in f, p x → u x ≤ a } :=
  rfl

theorem bliminf_eq : bliminf u f p = sSup { a | ∀ᶠ x in f, p x → a ≤ u x } :=
  rfl

lemma liminf_comp (u : β → α) (v : γ → β) (f : Filter γ) :
    liminf (u ∘ v) f = liminf u (map v f) := rfl

lemma limsup_comp (u : β → α) (v : γ → β) (f : Filter γ) :
    limsup (u ∘ v) f = limsup u (map v f) := rfl

end

@[simp]
theorem blimsup_true (f : Filter β) (u : β → α) : (blimsup u f fun _ => True) = limsup u f := by
  simp [blimsup_eq, limsup_eq]

@[simp]
theorem bliminf_true (f : Filter β) (u : β → α) : (bliminf u f fun _ => True) = liminf u f := by
  simp [bliminf_eq, liminf_eq]

lemma blimsup_eq_limsup {f : Filter β} {u : β → α} {p : β → Prop} :
    blimsup u f p = limsup u (f ⊓ 𝓟 {x | p x}) := by
  simp only [blimsup_eq, limsup_eq, eventually_inf_principal, mem_setOf_eq]

lemma bliminf_eq_liminf {f : Filter β} {u : β → α} {p : β → Prop} :
    bliminf u f p = liminf u (f ⊓ 𝓟 {x | p x}) :=
  blimsup_eq_limsup (α := αᵒᵈ)

theorem blimsup_eq_limsup_subtype {f : Filter β} {u : β → α} {p : β → Prop} :
    blimsup u f p = limsup (u ∘ ((↑) : { x | p x } → β)) (comap (↑) f) := by
  rw [blimsup_eq_limsup, limsup, limsup, ← map_map, map_comap_setCoe_val]

theorem bliminf_eq_liminf_subtype {f : Filter β} {u : β → α} {p : β → Prop} :
    bliminf u f p = liminf (u ∘ ((↑) : { x | p x } → β)) (comap (↑) f) :=
  blimsup_eq_limsup_subtype (α := αᵒᵈ)

theorem limsSup_le_of_le {f : Filter α} {a}
    (hf : f.IsCobounded (· ≤ ·) := by isBoundedDefault)
    (h : ∀ᶠ n in f, n ≤ a) : limsSup f ≤ a :=
  csInf_le hf h

theorem le_limsInf_of_le {f : Filter α} {a}
    (hf : f.IsCobounded (· ≥ ·) := by isBoundedDefault)
    (h : ∀ᶠ n in f, a ≤ n) : a ≤ limsInf f :=
  le_csSup hf h

theorem limsup_le_of_le {f : Filter β} {u : β → α} {a}
    (hf : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h : ∀ᶠ n in f, u n ≤ a) : limsup u f ≤ a :=
  csInf_le hf h

theorem le_liminf_of_le {f : Filter β} {u : β → α} {a}
    (hf : f.IsCoboundedUnder (· ≥ ·) u := by isBoundedDefault)
    (h : ∀ᶠ n in f, a ≤ u n) : a ≤ liminf u f :=
  le_csSup hf h

theorem le_limsSup_of_le {f : Filter α} {a}
    (hf : f.IsBounded (· ≤ ·) := by isBoundedDefault)
    (h : ∀ b, (∀ᶠ n in f, n ≤ b) → a ≤ b) : a ≤ limsSup f :=
  le_csInf hf h

theorem limsInf_le_of_le {f : Filter α} {a}
    (hf : f.IsBounded (· ≥ ·) := by isBoundedDefault)
    (h : ∀ b, (∀ᶠ n in f, b ≤ n) → b ≤ a) : limsInf f ≤ a :=
  csSup_le hf h

theorem le_limsup_of_le {f : Filter β} {u : β → α} {a}
    (hf : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h : ∀ b, (∀ᶠ n in f, u n ≤ b) → a ≤ b) : a ≤ limsup u f :=
  le_csInf hf h

theorem liminf_le_of_le {f : Filter β} {u : β → α} {a}
    (hf : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault)
    (h : ∀ b, (∀ᶠ n in f, b ≤ u n) → b ≤ a) : liminf u f ≤ a :=
  csSup_le hf h

theorem limsInf_le_limsSup {f : Filter α} [NeBot f]
    (h₁ : f.IsBounded (· ≤ ·) := by isBoundedDefault)
    (h₂ : f.IsBounded (· ≥ ·) := by isBoundedDefault) :
    limsInf f ≤ limsSup f :=
  liminf_le_of_le h₂ fun a₀ ha₀ =>
    le_limsup_of_le h₁ fun a₁ ha₁ =>
      show a₀ ≤ a₁ from
        let ⟨_, hb₀, hb₁⟩ := (ha₀.and ha₁).exists
        le_trans hb₀ hb₁

theorem liminf_le_limsup {f : Filter β} [NeBot f] {u : β → α}
    (h : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h' : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) :
    liminf u f ≤ limsup u f :=
  limsInf_le_limsSup h h'

theorem limsSup_le_limsSup {f g : Filter α}
    (hf : f.IsCobounded (· ≤ ·) := by isBoundedDefault)
    (hg : g.IsBounded (· ≤ ·) := by isBoundedDefault)
    (h : ∀ a, (∀ᶠ n in g, n ≤ a) → ∀ᶠ n in f, n ≤ a) : limsSup f ≤ limsSup g :=
  csInf_le_csInf hf hg h

theorem limsInf_le_limsInf {f g : Filter α}
    (hf : f.IsBounded (· ≥ ·) := by isBoundedDefault)
    (hg : g.IsCobounded (· ≥ ·) := by isBoundedDefault)
    (h : ∀ a, (∀ᶠ n in f, a ≤ n) → ∀ᶠ n in g, a ≤ n) : limsInf f ≤ limsInf g :=
  csSup_le_csSup hg hf h

theorem limsup_le_limsup {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α → β}
    (h : u ≤ᶠ[f] v)
    (hu : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault)
    (hv : f.IsBoundedUnder (· ≤ ·) v := by isBoundedDefault) :
    limsup u f ≤ limsup v f :=
  limsSup_le_limsSup hu hv fun _ => h.trans

theorem liminf_le_liminf {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α → β}
    (h : ∀ᶠ a in f, u a ≤ v a)
    (hu : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault)
    (hv : f.IsCoboundedUnder (· ≥ ·) v := by isBoundedDefault) :
    liminf u f ≤ liminf v f :=
  limsup_le_limsup (β := βᵒᵈ) h hv hu

theorem limsSup_le_limsSup_of_le {f g : Filter α} (h : f ≤ g)
    (hf : f.IsCobounded (· ≤ ·) := by isBoundedDefault)
    (hg : g.IsBounded (· ≤ ·) := by isBoundedDefault) :
    limsSup f ≤ limsSup g :=
  limsSup_le_limsSup hf hg fun _ ha => h ha

theorem limsInf_le_limsInf_of_le {f g : Filter α} (h : g ≤ f)
    (hf : f.IsBounded (· ≥ ·) := by isBoundedDefault)
    (hg : g.IsCobounded (· ≥ ·) := by isBoundedDefault) :
    limsInf f ≤ limsInf g :=
  limsInf_le_limsInf hf hg fun _ ha => h ha

theorem limsup_le_limsup_of_le {α β} [ConditionallyCompleteLattice β] {f g : Filter α} (h : f ≤ g)
    {u : α → β}
    (hf : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault)
    (hg : g.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault) :
    limsup u f ≤ limsup u g :=
  limsSup_le_limsSup_of_le (map_mono h) hf hg

theorem liminf_le_liminf_of_le {α β} [ConditionallyCompleteLattice β] {f g : Filter α} (h : g ≤ f)
    {u : α → β}
    (hf : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault)
    (hg : g.IsCoboundedUnder (· ≥ ·) u := by isBoundedDefault) :
    liminf u f ≤ liminf u g :=
  limsInf_le_limsInf_of_le (map_mono h) hf hg

lemma limsSup_principal_eq_csSup (h : BddAbove s) (hs : s.Nonempty) : limsSup (𝓟 s) = sSup s := by
  simp only [limsSup, eventually_principal]; exact csInf_upperBounds_eq_csSup h hs

lemma limsInf_principal_eq_csSup (h : BddBelow s) (hs : s.Nonempty) : limsInf (𝓟 s) = sInf s :=
  limsSup_principal_eq_csSup (α := αᵒᵈ) h hs

lemma limsup_top_eq_ciSup [Nonempty β] (hu : BddAbove (range u)) : limsup u ⊤ = ⨆ i, u i := by
  rw [limsup, map_top, limsSup_principal_eq_csSup hu (range_nonempty _), sSup_range]

lemma liminf_top_eq_ciInf [Nonempty β] (hu : BddBelow (range u)) : liminf u ⊤ = ⨅ i, u i := by
  rw [liminf, map_top, limsInf_principal_eq_csSup hu (range_nonempty _), sInf_range]

theorem limsup_congr {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α → β}
    (h : ∀ᶠ a in f, u a = v a) : limsup u f = limsup v f := by
  rw [limsup_eq]
  congr with b
  exact eventually_congr (h.mono fun x hx => by simp [hx])

theorem blimsup_congr {f : Filter β} {u v : β → α} {p : β → Prop} (h : ∀ᶠ a in f, p a → u a = v a) :
    blimsup u f p = blimsup v f p := by
  simpa only [blimsup_eq_limsup] using limsup_congr <| eventually_inf_principal.2 h

theorem bliminf_congr {f : Filter β} {u v : β → α} {p : β → Prop} (h : ∀ᶠ a in f, p a → u a = v a) :
    bliminf u f p = bliminf v f p :=
  blimsup_congr (α := αᵒᵈ) h

theorem liminf_congr {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α → β}
    (h : ∀ᶠ a in f, u a = v a) : liminf u f = liminf v f :=
  limsup_congr (β := βᵒᵈ) h

@[simp]
theorem limsup_const {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} [NeBot f]
    (b : β) : limsup (fun _ => b) f = b := by
  simpa only [limsup_eq, eventually_const] using csInf_Ici

@[simp]
theorem liminf_const {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} [NeBot f]
    (b : β) : liminf (fun _ => b) f = b :=
  limsup_const (β := βᵒᵈ) b

theorem HasBasis.liminf_eq_sSup_iUnion_iInter {ι ι' : Type*} {f : ι → α} {v : Filter ι}
    {p : ι' → Prop} {s : ι' → Set ι} (hv : v.HasBasis p s) :
    liminf f v = sSup (⋃ (j : Subtype p), ⋂ (i : s j), Iic (f i)) := by
  simp_rw [liminf_eq, hv.eventually_iff]
  congr
  ext x
  simp only [mem_setOf_eq, iInter_coe_set, mem_iUnion, mem_iInter, mem_Iic, Subtype.exists,
    exists_prop]

theorem HasBasis.liminf_eq_sSup_univ_of_empty {f : ι → α} {v : Filter ι}
    {p : ι' → Prop} {s : ι' → Set ι} (hv : v.HasBasis p s) (i : ι') (hi : p i) (h'i : s i = ∅) :
    liminf f v = sSup univ := by
  simp [hv.eq_bot_iff.2 ⟨i, hi, h'i⟩, liminf_eq]

theorem HasBasis.limsup_eq_sInf_iUnion_iInter {ι ι' : Type*} {f : ι → α} {v : Filter ι}
    {p : ι' → Prop} {s : ι' → Set ι} (hv : v.HasBasis p s) :
    limsup f v = sInf (⋃ (j : Subtype p), ⋂ (i : s j), Ici (f i)) :=
  HasBasis.liminf_eq_sSup_iUnion_iInter (α := αᵒᵈ) hv

theorem HasBasis.limsup_eq_sInf_univ_of_empty {f : ι → α} {v : Filter ι}
    {p : ι' → Prop} {s : ι' → Set ι} (hv : v.HasBasis p s) (i : ι') (hi : p i) (h'i : s i = ∅) :
    limsup f v = sInf univ :=
  HasBasis.liminf_eq_sSup_univ_of_empty (α := αᵒᵈ) hv i hi h'i

@[simp]
theorem liminf_nat_add (f : ℕ → α) (k : ℕ) :
    liminf (fun i => f (i + k)) atTop = liminf f atTop := by
  change liminf (f ∘ (· + k)) atTop = liminf f atTop
  rw [liminf, liminf, ← map_map, map_add_atTop_eq_nat]

@[simp]
theorem limsup_nat_add (f : ℕ → α) (k : ℕ) : limsup (fun i => f (i + k)) atTop = limsup f atTop :=
  @liminf_nat_add αᵒᵈ _ f k

end ConditionallyCompleteLattice

section CompleteLattice

variable [CompleteLattice α]

@[simp]
theorem limsSup_bot : limsSup (⊥ : Filter α) = ⊥ :=
  bot_unique <| sInf_le <| by simp

@[simp] theorem limsup_bot (f : β → α) : limsup f ⊥ = ⊥ := by simp [limsup]

@[simp]
theorem limsInf_bot : limsInf (⊥ : Filter α) = ⊤ :=
  top_unique <| le_sSup <| by simp

@[simp] theorem liminf_bot (f : β → α) : liminf f ⊥ = ⊤ := by simp [liminf]

@[simp]
theorem limsSup_top : limsSup (⊤ : Filter α) = ⊤ :=
  top_unique <| le_sInf <| by simpa [eq_univ_iff_forall] using fun b hb => top_unique <| hb _

@[simp]
theorem limsInf_top : limsInf (⊤ : Filter α) = ⊥ :=
  bot_unique <| sSup_le <| by simpa [eq_univ_iff_forall] using fun b hb => bot_unique <| hb _

@[simp]
theorem blimsup_false {f : Filter β} {u : β → α} : (blimsup u f fun _ => False) = ⊥ := by
  simp [blimsup_eq]

@[simp]
theorem bliminf_false {f : Filter β} {u : β → α} : (bliminf u f fun _ => False) = ⊤ := by
  simp [bliminf_eq]

/-- Same as limsup_const applied to `⊥` but without the `NeBot f` assumption -/
@[simp]
theorem limsup_const_bot {f : Filter β} : limsup (fun _ : β => (⊥ : α)) f = (⊥ : α) := by
  rw [limsup_eq, eq_bot_iff]
  exact sInf_le (Eventually.of_forall fun _ => le_rfl)

/-- Same as limsup_const applied to `⊤` but without the `NeBot f` assumption -/
@[simp]
theorem liminf_const_top {f : Filter β} : liminf (fun _ : β => (⊤ : α)) f = (⊤ : α) :=
  limsup_const_bot (α := αᵒᵈ)

theorem HasBasis.limsSup_eq_iInf_sSup {ι} {p : ι → Prop} {s} {f : Filter α} (h : f.HasBasis p s) :
    limsSup f = ⨅ (i) (_ : p i), sSup (s i) :=
  le_antisymm (le_iInf₂ fun i hi => sInf_le <| h.eventually_iff.2 ⟨i, hi, fun _ => le_sSup⟩)
    (le_sInf fun _ ha =>
      let ⟨_, hi, ha⟩ := h.eventually_iff.1 ha
      iInf₂_le_of_le _ hi <| sSup_le ha)

theorem HasBasis.limsInf_eq_iSup_sInf {p : ι → Prop} {s : ι → Set α} {f : Filter α}
    (h : f.HasBasis p s) : limsInf f = ⨆ (i) (_ : p i), sInf (s i) :=
  HasBasis.limsSup_eq_iInf_sSup (α := αᵒᵈ) h

theorem limsSup_eq_iInf_sSup {f : Filter α} : limsSup f = ⨅ s ∈ f, sSup s :=
  f.basis_sets.limsSup_eq_iInf_sSup

theorem limsInf_eq_iSup_sInf {f : Filter α} : limsInf f = ⨆ s ∈ f, sInf s :=
  limsSup_eq_iInf_sSup (α := αᵒᵈ)

theorem limsup_le_iSup {f : Filter β} {u : β → α} : limsup u f ≤ ⨆ n, u n :=
  limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall (le_iSup u))

theorem iInf_le_liminf {f : Filter β} {u : β → α} : ⨅ n, u n ≤ liminf u f :=
  le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall (iInf_le u))

/-- In a complete lattice, the limsup of a function is the infimum over sets `s` in the filter
of the supremum of the function over `s` -/
theorem limsup_eq_iInf_iSup {f : Filter β} {u : β → α} : limsup u f = ⨅ s ∈ f, ⨆ a ∈ s, u a :=
  (f.basis_sets.map u).limsSup_eq_iInf_sSup.trans <| by simp only [sSup_image, id]

theorem limsup_eq_iInf_iSup_of_nat {u : ℕ → α} : limsup u atTop = ⨅ n : ℕ, ⨆ i ≥ n, u i :=
  (atTop_basis.map u).limsSup_eq_iInf_sSup.trans <| by simp only [sSup_image, iInf_const]; rfl

theorem limsup_eq_iInf_iSup_of_nat' {u : ℕ → α} : limsup u atTop = ⨅ n : ℕ, ⨆ i : ℕ, u (i + n) := by
  simp only [limsup_eq_iInf_iSup_of_nat, iSup_ge_eq_iSup_nat_add]

theorem HasBasis.limsup_eq_iInf_iSup {p : ι → Prop} {s : ι → Set β} {f : Filter β} {u : β → α}
    (h : f.HasBasis p s) : limsup u f = ⨅ (i) (_ : p i), ⨆ a ∈ s i, u a :=
  (h.map u).limsSup_eq_iInf_sSup.trans <| by simp only [sSup_image, id]

lemma limsSup_principal_eq_sSup (s : Set α) : limsSup (𝓟 s) = sSup s := by
  simpa only [limsSup, eventually_principal] using sInf_upperBounds_eq_csSup s

lemma limsInf_principal_eq_sInf (s : Set α) : limsInf (𝓟 s) = sInf s := by
  simpa only [limsInf, eventually_principal] using sSup_lowerBounds_eq_sInf s

@[simp] lemma limsup_top_eq_iSup (u : β → α) : limsup u ⊤ = ⨆ i, u i := by
  rw [limsup, map_top, limsSup_principal_eq_sSup, sSup_range]

@[simp] lemma liminf_top_eq_iInf (u : β → α) : liminf u ⊤ = ⨅ i, u i := by
  rw [liminf, map_top, limsInf_principal_eq_sInf, sInf_range]

theorem blimsup_congr' {f : Filter β} {p q : β → Prop} {u : β → α}
    (h : ∀ᶠ x in f, u x ≠ ⊥ → (p x ↔ q x)) : blimsup u f p = blimsup u f q := by
  simp only [blimsup_eq]
  congr with a
  refine eventually_congr (h.mono fun b hb => ?_)
  rcases eq_or_ne (u b) ⊥ with hu | hu; · simp [hu]
  rw [hb hu]

theorem bliminf_congr' {f : Filter β} {p q : β → Prop} {u : β → α}
    (h : ∀ᶠ x in f, u x ≠ ⊤ → (p x ↔ q x)) : bliminf u f p = bliminf u f q :=
  blimsup_congr' (α := αᵒᵈ) h

lemma HasBasis.blimsup_eq_iInf_iSup {p : ι → Prop} {s : ι → Set β} {f : Filter β} {u : β → α}
    (hf : f.HasBasis p s) {q : β → Prop} :
    blimsup u f q = ⨅ (i) (_ : p i), ⨆ a ∈ s i, ⨆ (_ : q a), u a := by
  simp only [blimsup_eq_limsup, (hf.inf_principal _).limsup_eq_iInf_iSup, mem_inter_iff, iSup_and,
    mem_setOf_eq]

theorem blimsup_eq_iInf_biSup {f : Filter β} {p : β → Prop} {u : β → α} :
    blimsup u f p = ⨅ s ∈ f, ⨆ (b) (_ : p b ∧ b ∈ s), u b := by
  simp only [f.basis_sets.blimsup_eq_iInf_iSup, iSup_and', id, and_comm]

theorem blimsup_eq_iInf_biSup_of_nat {p : ℕ → Prop} {u : ℕ → α} :
    blimsup u atTop p = ⨅ i, ⨆ (j) (_ : p j ∧ i ≤ j), u j := by
  simp only [atTop_basis.blimsup_eq_iInf_iSup, @and_comm (p _), iSup_and, mem_Ici, iInf_true]

/-- In a complete lattice, the liminf of a function is the infimum over sets `s` in the filter
of the supremum of the function over `s` -/
theorem liminf_eq_iSup_iInf {f : Filter β} {u : β → α} : liminf u f = ⨆ s ∈ f, ⨅ a ∈ s, u a :=
  limsup_eq_iInf_iSup (α := αᵒᵈ)

theorem liminf_eq_iSup_iInf_of_nat {u : ℕ → α} : liminf u atTop = ⨆ n : ℕ, ⨅ i ≥ n, u i :=
  @limsup_eq_iInf_iSup_of_nat αᵒᵈ _ u

theorem liminf_eq_iSup_iInf_of_nat' {u : ℕ → α} : liminf u atTop = ⨆ n : ℕ, ⨅ i : ℕ, u (i + n) :=
  @limsup_eq_iInf_iSup_of_nat' αᵒᵈ _ _

theorem HasBasis.liminf_eq_iSup_iInf {p : ι → Prop} {s : ι → Set β} {f : Filter β} {u : β → α}
    (h : f.HasBasis p s) : liminf u f = ⨆ (i) (_ : p i), ⨅ a ∈ s i, u a :=
  HasBasis.limsup_eq_iInf_iSup (α := αᵒᵈ) h

theorem bliminf_eq_iSup_biInf {f : Filter β} {p : β → Prop} {u : β → α} :
    bliminf u f p = ⨆ s ∈ f, ⨅ (b) (_ : p b ∧ b ∈ s), u b :=
  @blimsup_eq_iInf_biSup αᵒᵈ β _ f p u

theorem bliminf_eq_iSup_biInf_of_nat {p : ℕ → Prop} {u : ℕ → α} :
    bliminf u atTop p = ⨆ i, ⨅ (j) (_ : p j ∧ i ≤ j), u j :=
  @blimsup_eq_iInf_biSup_of_nat αᵒᵈ _ p u

theorem limsup_eq_sInf_sSup {ι R : Type*} (F : Filter ι) [CompleteLattice R] (a : ι → R) :
    limsup a F = sInf ((fun I => sSup (a '' I)) '' F.sets) := by
  apply le_antisymm
  · rw [limsup_eq]
    refine sInf_le_sInf fun x hx => ?_
    rcases (mem_image _ F.sets x).mp hx with ⟨I, ⟨I_mem_F, hI⟩⟩
    filter_upwards [I_mem_F] with i hi
    exact hI ▸ le_sSup (mem_image_of_mem _ hi)
  · refine le_sInf fun b hb => sInf_le_of_le (mem_image_of_mem _ hb) <| sSup_le ?_
    rintro _ ⟨_, h, rfl⟩
    exact h

theorem liminf_eq_sSup_sInf {ι R : Type*} (F : Filter ι) [CompleteLattice R] (a : ι → R) :
    liminf a F = sSup ((fun I => sInf (a '' I)) '' F.sets) :=
  @Filter.limsup_eq_sInf_sSup ι (OrderDual R) _ _ a

theorem liminf_le_of_frequently_le' {α β} [CompleteLattice β] {f : Filter α} {u : α → β} {x : β}
    (h : ∃ᶠ a in f, u a ≤ x) : liminf u f ≤ x := by
  rw [liminf_eq]
  refine sSup_le fun b hb => ?_
  have hbx : ∃ᶠ _ in f, b ≤ x := by
    revert h
    rw [← not_imp_not, not_frequently, not_frequently]
    exact fun h => hb.mp (h.mono fun a hbx hba hax => hbx (hba.trans hax))
  exact hbx.exists.choose_spec

theorem le_limsup_of_frequently_le' {α β} [CompleteLattice β] {f : Filter α} {u : α → β} {x : β}
    (h : ∃ᶠ a in f, x ≤ u a) : x ≤ limsup u f :=
  liminf_le_of_frequently_le' (β := βᵒᵈ) h

/-- If `f : α → α` is a morphism of complete lattices, then the limsup of its iterates of any
`a : α` is a fixed point. -/
@[simp]
theorem _root_.CompleteLatticeHom.apply_limsup_iterate (f : CompleteLatticeHom α α) (a : α) :
    f (limsup (fun n => f^[n] a) atTop) = limsup (fun n => f^[n] a) atTop := by
  rw [limsup_eq_iInf_iSup_of_nat', map_iInf]
  simp_rw [_root_.map_iSup, ← Function.comp_apply (f := f), ← Function.iterate_succ' f,
    ← Nat.add_succ]
  conv_rhs => rw [iInf_split _ (0 < ·)]
  simp only [not_lt, Nat.le_zero, iInf_iInf_eq_left, add_zero, iInf_nat_gt_zero_eq, left_eq_inf]
  refine (iInf_le (fun i => ⨆ j, f^[j + (i + 1)] a) 0).trans ?_
  simp only [zero_add, Function.comp_apply, iSup_le_iff]
  exact fun i => le_iSup (fun i => f^[i] a) (i + 1)

/-- If `f : α → α` is a morphism of complete lattices, then the liminf of its iterates of any
`a : α` is a fixed point. -/
theorem _root_.CompleteLatticeHom.apply_liminf_iterate (f : CompleteLatticeHom α α) (a : α) :
    f (liminf (fun n => f^[n] a) atTop) = liminf (fun n => f^[n] a) atTop :=
  (CompleteLatticeHom.dual f).apply_limsup_iterate _

variable {f g : Filter β} {p q : β → Prop} {u v : β → α}

theorem blimsup_mono (h : ∀ x, p x → q x) : blimsup u f p ≤ blimsup u f q :=
  sInf_le_sInf fun a ha => ha.mono <| by tauto

theorem bliminf_antitone (h : ∀ x, p x → q x) : bliminf u f q ≤ bliminf u f p :=
  sSup_le_sSup fun a ha => ha.mono <| by tauto

theorem mono_blimsup' (h : ∀ᶠ x in f, p x → u x ≤ v x) : blimsup u f p ≤ blimsup v f p :=
  sInf_le_sInf fun _ ha => (ha.and h).mono fun _ hx hx' => (hx.2 hx').trans (hx.1 hx')

theorem mono_blimsup (h : ∀ x, p x → u x ≤ v x) : blimsup u f p ≤ blimsup v f p :=
  mono_blimsup' <| Eventually.of_forall h

theorem mono_bliminf' (h : ∀ᶠ x in f, p x → u x ≤ v x) : bliminf u f p ≤ bliminf v f p :=
  sSup_le_sSup fun _ ha => (ha.and h).mono fun _ hx hx' => (hx.1 hx').trans (hx.2 hx')

theorem mono_bliminf (h : ∀ x, p x → u x ≤ v x) : bliminf u f p ≤ bliminf v f p :=
  mono_bliminf' <| Eventually.of_forall h

theorem bliminf_antitone_filter (h : f ≤ g) : bliminf u g p ≤ bliminf u f p :=
  sSup_le_sSup fun _ ha => ha.filter_mono h

theorem blimsup_monotone_filter (h : f ≤ g) : blimsup u f p ≤ blimsup u g p :=
  sInf_le_sInf fun _ ha => ha.filter_mono h

-- @[simp] -- Porting note: simp_nf linter, lhs simplifies, added _aux versions below
theorem blimsup_and_le_inf : (blimsup u f fun x => p x ∧ q x) ≤ blimsup u f p ⊓ blimsup u f q :=
  le_inf (blimsup_mono <| by tauto) (blimsup_mono <| by tauto)

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

@[simp]
theorem bliminf_or_le_inf_aux_left : (bliminf u f fun x => p x ∨ q x) ≤ bliminf u f p :=
  bliminf_or_le_inf.trans inf_le_left

@[simp]
theorem bliminf_or_le_inf_aux_right : (bliminf u f fun x => p x ∨ q x) ≤ bliminf u f q :=
  bliminf_or_le_inf.trans inf_le_right

theorem _root_.OrderIso.apply_blimsup [CompleteLattice γ] (e : α ≃o γ) :
    e (blimsup u f p) = blimsup (e ∘ u) f p := by
  simp only [blimsup_eq, map_sInf, Function.comp_apply, e.image_eq_preimage,
    Set.preimage_setOf_eq, e.le_symm_apply]

theorem _root_.OrderIso.apply_bliminf [CompleteLattice γ] (e : α ≃o γ) :
    e (bliminf u f p) = bliminf (e ∘ u) f p :=
  e.dual.apply_blimsup

theorem _root_.sSupHom.apply_blimsup_le [CompleteLattice γ] (g : sSupHom α γ) :
    g (blimsup u f p) ≤ blimsup (g ∘ u) f p := by
  simp only [blimsup_eq_iInf_biSup, Function.comp]
  refine ((OrderHomClass.mono g).map_iInf₂_le _).trans ?_
  simp only [_root_.map_iSup, le_refl]

theorem _root_.sInfHom.le_apply_bliminf [CompleteLattice γ] (g : sInfHom α γ) :
    bliminf (g ∘ u) f p ≤ g (bliminf u f p) :=
  (sInfHom.dual g).apply_blimsup_le

end CompleteLattice

section CompleteDistribLattice

variable [CompleteDistribLattice α] {f : Filter β} {p q : β → Prop} {u : β → α}

lemma limsup_sup_filter {g} : limsup u (f ⊔ g) = limsup u f ⊔ limsup u g := by
  refine le_antisymm ?_
    (sup_le (limsup_le_limsup_of_le le_sup_left) (limsup_le_limsup_of_le le_sup_right))
  simp_rw [limsup_eq, sInf_sup_eq, sup_sInf_eq, mem_setOf_eq, le_iInf₂_iff]
  intro a ha b hb
  exact sInf_le ⟨ha.mono fun _ h ↦ h.trans le_sup_left, hb.mono fun _ h ↦ h.trans le_sup_right⟩

lemma liminf_sup_filter {g} : liminf u (f ⊔ g) = liminf u f ⊓ liminf u g :=
  limsup_sup_filter (α := αᵒᵈ)

@[simp]
theorem blimsup_or_eq_sup : (blimsup u f fun x => p x ∨ q x) = blimsup u f p ⊔ blimsup u f q := by
  simp only [blimsup_eq_limsup, ← limsup_sup_filter, ← inf_sup_left, sup_principal, setOf_or]

@[simp]
theorem bliminf_or_eq_inf : (bliminf u f fun x => p x ∨ q x) = bliminf u f p ⊓ bliminf u f q :=
  blimsup_or_eq_sup (α := αᵒᵈ)

@[simp]
lemma blimsup_sup_not : blimsup u f p ⊔ blimsup u f (¬p ·) = limsup u f := by
  simp_rw [← blimsup_or_eq_sup, or_not, blimsup_true]

@[simp]
lemma bliminf_inf_not : bliminf u f p ⊓ bliminf u f (¬p ·) = liminf u f :=
  blimsup_sup_not (α := αᵒᵈ)

@[simp]
lemma blimsup_not_sup : blimsup u f (¬p ·) ⊔ blimsup u f p = limsup u f := by
  simpa only [not_not] using blimsup_sup_not (p := (¬p ·))

@[simp]
lemma bliminf_not_inf : bliminf u f (¬p ·) ⊓ bliminf u f p = liminf u f :=
  blimsup_not_sup (α := αᵒᵈ)

lemma limsup_piecewise {s : Set β} [DecidablePred (· ∈ s)] {v} :
    limsup (s.piecewise u v) f = blimsup u f (· ∈ s) ⊔ blimsup v f (· ∉ s) := by
  rw [← blimsup_sup_not (p := (· ∈ s))]
  refine congr_arg₂ _ (blimsup_congr ?_) (blimsup_congr ?_) <;>
    filter_upwards with _ h using by simp [h]

lemma liminf_piecewise {s : Set β} [DecidablePred (· ∈ s)] {v} :
    liminf (s.piecewise u v) f = bliminf u f (· ∈ s) ⊓ bliminf v f (· ∉ s) :=
  limsup_piecewise (α := αᵒᵈ)

theorem sup_limsup [NeBot f] (a : α) : a ⊔ limsup u f = limsup (fun x => a ⊔ u x) f := by
  simp only [limsup_eq_iInf_iSup, iSup_sup_eq, sup_iInf₂_eq]
  congr; ext s; congr; ext hs; congr
  exact (biSup_const (nonempty_of_mem hs)).symm

theorem inf_liminf [NeBot f] (a : α) : a ⊓ liminf u f = liminf (fun x => a ⊓ u x) f :=
  sup_limsup (α := αᵒᵈ) a

theorem sup_liminf (a : α) : a ⊔ liminf u f = liminf (fun x => a ⊔ u x) f := by
  simp only [liminf_eq_iSup_iInf]
  rw [sup_comm, biSup_sup (⟨univ, univ_mem⟩ : ∃ i : Set β, i ∈ f)]
  simp_rw [iInf₂_sup_eq, sup_comm (a := a)]

theorem inf_limsup (a : α) : a ⊓ limsup u f = limsup (fun x => a ⊓ u x) f :=
  sup_liminf (α := αᵒᵈ) a

end CompleteDistribLattice

section CompleteBooleanAlgebra

variable [CompleteBooleanAlgebra α] (f : Filter β) (u : β → α)

theorem limsup_compl : (limsup u f)ᶜ = liminf (compl ∘ u) f := by
  simp only [limsup_eq_iInf_iSup, compl_iInf, compl_iSup, liminf_eq_iSup_iInf, Function.comp_apply]

theorem liminf_compl : (liminf u f)ᶜ = limsup (compl ∘ u) f := by
  simp only [limsup_eq_iInf_iSup, compl_iInf, compl_iSup, liminf_eq_iSup_iInf, Function.comp_apply]

theorem limsup_sdiff (a : α) : limsup u f \ a = limsup (fun b => u b \ a) f := by
  simp only [limsup_eq_iInf_iSup, sdiff_eq]
  rw [biInf_inf (⟨univ, univ_mem⟩ : ∃ i : Set β, i ∈ f)]
  simp_rw [inf_comm, inf_iSup₂_eq, inf_comm]

theorem liminf_sdiff [NeBot f] (a : α) : liminf u f \ a = liminf (fun b => u b \ a) f := by
  simp only [sdiff_eq, inf_comm _ aᶜ, inf_liminf]

theorem sdiff_limsup [NeBot f] (a : α) : a \ limsup u f = liminf (fun b => a \ u b) f := by
  rw [← compl_inj_iff]
  simp only [sdiff_eq, liminf_compl, comp_def, compl_inf, compl_compl, sup_limsup]

theorem sdiff_liminf (a : α) : a \ liminf u f = limsup (fun b => a \ u b) f := by
  rw [← compl_inj_iff]
  simp only [sdiff_eq, limsup_compl, comp_def, compl_inf, compl_compl, sup_liminf]

end CompleteBooleanAlgebra

section SetLattice

variable {p : ι → Prop} {s : ι → Set α} {𝓕 : Filter ι} {a : α}

lemma mem_liminf_iff_eventually_mem : (a ∈ liminf s 𝓕) ↔ (∀ᶠ i in 𝓕, a ∈ s i) := by
  simpa only [liminf_eq_iSup_iInf, iSup_eq_iUnion, iInf_eq_iInter, mem_iUnion, mem_iInter]
    using ⟨fun ⟨S, hS, hS'⟩ ↦ mem_of_superset hS (by tauto), fun h ↦ ⟨{i | a ∈ s i}, h, by tauto⟩⟩

lemma mem_limsup_iff_frequently_mem : (a ∈ limsup s 𝓕) ↔ (∃ᶠ i in 𝓕, a ∈ s i) := by
  simp only [Filter.Frequently, iff_not_comm, ← mem_compl_iff, limsup_compl, comp_apply,
    mem_liminf_iff_eventually_mem]

theorem cofinite.blimsup_set_eq :
    blimsup s cofinite p = { x | { n | p n ∧ x ∈ s n }.Infinite } := by
  simp only [blimsup_eq, le_eq_subset, eventually_cofinite, not_forall, sInf_eq_sInter, exists_prop]
  ext x
  refine ⟨fun h => ?_, fun hx t h => ?_⟩ <;> contrapose! h
  · simp only [mem_sInter, mem_setOf_eq, not_forall, exists_prop]
    exact ⟨{x}ᶜ, by simpa using h, by simp⟩
  · exact hx.mono fun i hi => ⟨hi.1, fun hit => h (hit hi.2)⟩

theorem cofinite.bliminf_set_eq : bliminf s cofinite p = { x | { n | p n ∧ x ∉ s n }.Finite } := by
  rw [← compl_inj_iff]
  simp only [bliminf_eq_iSup_biInf, compl_iInf, compl_iSup, ← blimsup_eq_iInf_biSup,
    cofinite.blimsup_set_eq]
  rfl

/-- In other words, `limsup cofinite s` is the set of elements lying inside the family `s`
infinitely often. -/
theorem cofinite.limsup_set_eq : limsup s cofinite = { x | { n | x ∈ s n }.Infinite } := by
  simp only [← cofinite.blimsup_true s, cofinite.blimsup_set_eq, true_and]

/-- In other words, `liminf cofinite s` is the set of elements lying outside the family `s`
finitely often. -/
theorem cofinite.liminf_set_eq : liminf s cofinite = { x | { n | x ∉ s n }.Finite } := by
  simp only [← cofinite.bliminf_true s, cofinite.bliminf_set_eq, true_and]

theorem exists_forall_mem_of_hasBasis_mem_blimsup {l : Filter β} {b : ι → Set β} {q : ι → Prop}
    (hl : l.HasBasis q b) {u : β → Set α} {p : β → Prop} {x : α} (hx : x ∈ blimsup u l p) :
    ∃ f : { i | q i } → β, ∀ i, x ∈ u (f i) ∧ p (f i) ∧ f i ∈ b i := by
  rw [blimsup_eq_iInf_biSup] at hx
  simp only [iSup_eq_iUnion, iInf_eq_iInter, mem_iInter, mem_iUnion, exists_prop] at hx
  choose g hg hg' using hx
  refine ⟨fun i : { i | q i } => g (b i) (hl.mem_of_mem i.2), fun i => ⟨?_, ?_⟩⟩
  · exact hg' (b i) (hl.mem_of_mem i.2)
  · exact hg (b i) (hl.mem_of_mem i.2)

theorem exists_forall_mem_of_hasBasis_mem_blimsup' {l : Filter β} {b : ι → Set β}
    (hl : l.HasBasis (fun _ => True) b) {u : β → Set α} {p : β → Prop} {x : α}
    (hx : x ∈ blimsup u l p) : ∃ f : ι → β, ∀ i, x ∈ u (f i) ∧ p (f i) ∧ f i ∈ b i := by
  obtain ⟨f, hf⟩ := exists_forall_mem_of_hasBasis_mem_blimsup hl hx
  exact ⟨fun i => f ⟨i, trivial⟩, fun i => hf ⟨i, trivial⟩⟩

end SetLattice

section ConditionallyCompleteLinearOrder

theorem frequently_lt_of_lt_limsSup {f : Filter α} [ConditionallyCompleteLinearOrder α] {a : α}
    (hf : f.IsCobounded (· ≤ ·) := by isBoundedDefault)
    (h : a < limsSup f) : ∃ᶠ n in f, a < n := by
  contrapose! h
  simp only [not_frequently, not_lt] at h
  exact limsSup_le_of_le hf h

theorem frequently_lt_of_limsInf_lt {f : Filter α} [ConditionallyCompleteLinearOrder α] {a : α}
    (hf : f.IsCobounded (· ≥ ·) := by isBoundedDefault)
    (h : limsInf f < a) : ∃ᶠ n in f, n < a :=
  frequently_lt_of_lt_limsSup (α := OrderDual α) hf h

theorem eventually_lt_of_lt_liminf {f : Filter α} [ConditionallyCompleteLinearOrder β] {u : α → β}
    {b : β} (h : b < liminf u f)
    (hu : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) :
    ∀ᶠ a in f, b < u a := by
  obtain ⟨c, hc, hbc⟩ : ∃ (c : β) (_ : c ∈ { c : β | ∀ᶠ n : α in f, c ≤ u n }), b < c := by
    simp_rw [exists_prop]
    exact exists_lt_of_lt_csSup hu h
  exact hc.mono fun x hx => lt_of_lt_of_le hbc hx

theorem eventually_lt_of_limsup_lt {f : Filter α} [ConditionallyCompleteLinearOrder β] {u : α → β}
    {b : β} (h : limsup u f < b)
    (hu : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault) :
    ∀ᶠ a in f, u a < b :=
  eventually_lt_of_lt_liminf (β := βᵒᵈ) h hu

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α]

/-- If `Filter.limsup u atTop ≤ x`, then for all `ε > 0`, eventually we have `u b < x + ε`. -/
theorem eventually_lt_add_pos_of_limsup_le [Preorder β] [AddZeroClass α] [AddLeftStrictMono α]
    {x ε : α} {u : β → α} (hu_bdd : IsBoundedUnder LE.le atTop u) (hu : Filter.limsup u atTop ≤ x)
    (hε : 0 < ε) :
    ∀ᶠ b : β in atTop, u b < x + ε :=
  eventually_lt_of_limsup_lt (lt_of_le_of_lt hu (lt_add_of_pos_right x hε)) hu_bdd

/-- If `x ≤ Filter.liminf u atTop`, then for all `ε < 0`, eventually we have `x + ε < u b`. -/
theorem eventually_add_neg_lt_of_le_liminf [Preorder β] [AddZeroClass α] [AddLeftStrictMono α]
    {x ε : α} {u : β → α} (hu_bdd : IsBoundedUnder GE.ge atTop u) (hu : x ≤ Filter.liminf u atTop )
    (hε : ε < 0) :
    ∀ᶠ b : β in atTop, x + ε < u b :=
  eventually_lt_of_lt_liminf (lt_of_lt_of_le (add_lt_of_neg_right x hε) hu) hu_bdd

/-- If `Filter.limsup u atTop ≤ x`, then for all `ε > 0`, there exists a positive natural
number `n` such that `u n < x + ε`. -/
theorem exists_lt_of_limsup_le [AddMonoid α] [AddLeftStrictMono α] {x ε : α} {u : ℕ → α}
    (hu_bdd : IsBoundedUnder LE.le atTop u) (hu : Filter.limsup u atTop ≤ x) (hε : 0 < ε) :
    ∃ n : PNat, u n < x + ε := by
  have h : ∀ᶠ n : ℕ in atTop, u n < x + ε := eventually_lt_add_pos_of_limsup_le hu_bdd hu hε
  simp only [eventually_atTop] at h
  obtain ⟨n, hn⟩ := h
  exact ⟨⟨n + 1, Nat.succ_pos _⟩, hn (n + 1) (Nat.le_succ _)⟩

/-- If `x ≤ Filter.liminf u atTop`, then for all `ε < 0`, there exists a positive natural
number `n` such that ` x + ε < u n`. -/
theorem exists_lt_of_le_liminf [AddMonoid α] [AddLeftStrictMono α] {x ε : α} {u : ℕ → α}
    (hu_bdd : IsBoundedUnder GE.ge atTop u) (hu : x ≤ Filter.liminf u atTop) (hε : ε < 0) :
    ∃ n : PNat, x + ε < u n := by
  have h : ∀ᶠ n : ℕ in atTop, x + ε < u n := eventually_add_neg_lt_of_le_liminf hu_bdd hu hε
  simp only [eventually_atTop] at h
  obtain ⟨n, hn⟩ := h
  exact ⟨⟨n + 1, Nat.succ_pos _⟩, hn (n + 1) (Nat.le_succ _)⟩
end ConditionallyCompleteLinearOrder

theorem le_limsup_of_frequently_le {α β} [ConditionallyCompleteLinearOrder β] {f : Filter α}
    {u : α → β} {b : β} (hu_le : ∃ᶠ x in f, b ≤ u x)
    (hu : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault) :
    b ≤ limsup u f := by
  revert hu_le
  rw [← not_imp_not, not_frequently]
  simp_rw [← lt_iff_not_ge]
  exact fun h => eventually_lt_of_limsup_lt h hu

theorem liminf_le_of_frequently_le {α β} [ConditionallyCompleteLinearOrder β] {f : Filter α}
    {u : α → β} {b : β} (hu_le : ∃ᶠ x in f, u x ≤ b)
    (hu : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) :
    liminf u f ≤ b :=
  le_limsup_of_frequently_le (β := βᵒᵈ) hu_le hu

theorem frequently_lt_of_lt_limsup {α β} [ConditionallyCompleteLinearOrder β] {f : Filter α}
    {u : α → β} {b : β}
    (hu : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h : b < limsup u f) : ∃ᶠ x in f, b < u x := by
  contrapose! h
  apply limsSup_le_of_le hu
  simpa using h

theorem frequently_lt_of_liminf_lt {α β} [ConditionallyCompleteLinearOrder β] {f : Filter α}
    {u : α → β} {b : β}
    (hu : f.IsCoboundedUnder (· ≥ ·) u := by isBoundedDefault)
    (h : liminf u f < b) : ∃ᶠ x in f, u x < b :=
  frequently_lt_of_lt_limsup (β := βᵒᵈ) hu h

theorem limsup_le_iff {α β} [ConditionallyCompleteLinearOrder β] {f : Filter α} {u : α → β} {x : β}
    (h₁ : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h₂ : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault) :
    limsup u f ≤ x ↔ ∀ y > x, ∀ᶠ a in f, u a < y := by
  refine ⟨fun h _ h' ↦ eventually_lt_of_limsup_lt (lt_of_le_of_lt h h') h₂, fun h ↦ ?_⟩
  --Two cases: Either `x` is a cluster point from above, or it is not.
  --In the first case, we use `forall_lt_iff_le'` and split an interval.
  --In the second case, the function `u` must eventually be smaller or equal to `x`.
  by_cases h' : ∀ y > x, ∃ z, x < z ∧ z < y
  · rw [← forall_lt_iff_le']
    intro y x_y
    rcases h' y x_y with ⟨z, x_z, z_y⟩
    exact lt_of_le_of_lt (limsup_le_of_le h₁ ((h z x_z).mono (fun _ ↦ le_of_lt))) z_y
  · apply limsup_le_of_le h₁
    set_option push_neg.use_distrib true in push_neg at h'
    rcases h' with ⟨z, x_z, hz⟩
    exact (h z x_z).mono  <| fun w hw ↦ (or_iff_left (not_le_of_lt hw)).1 (hz (u w))

theorem le_limsup_iff {α β} [ConditionallyCompleteLinearOrder β] {f : Filter α} {u : α → β} {x : β}
    (h₁ : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h₂ : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault) :
    x ≤ limsup u f ↔ ∀ y < x, ∃ᶠ a in f, y < u a := by
  refine ⟨fun h _ h' ↦ frequently_lt_of_lt_limsup h₁ (lt_of_lt_of_le h' h), fun h ↦ ?_⟩
  --Two cases: Either `x` is a cluster point from below, or it is not.
  --In the first case, we use `forall_lt_iff_le` and split an interval.
  --In the second case, the function `u` must frequently be larger or equal to `x`.
  by_cases h' : ∀ y < x, ∃ z, y < z ∧ z < x
  · rw [← forall_lt_iff_le]
    intro y y_x
    rcases h' y y_x with ⟨z, y_z, z_x⟩
    exact lt_of_lt_of_le y_z (le_limsup_of_frequently_le ((h z z_x).mono (fun _ ↦ le_of_lt)) h₂)
  · apply le_limsup_of_frequently_le _ h₂
    set_option push_neg.use_distrib true in push_neg at h'
    rcases h' with ⟨z, z_x, hz⟩
    exact (h z z_x).mono <| fun w hw ↦ (or_iff_right (not_le_of_lt hw)).1 (hz (u w))

theorem le_liminf_iff {α β} [ConditionallyCompleteLinearOrder β] {f : Filter α} {u : α → β} {x : β}
    (h₁ : f.IsCoboundedUnder (· ≥ ·) u := by isBoundedDefault)
    (h₂ : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) :
    x ≤ liminf u f ↔ ∀ y < x, ∀ᶠ a in f, y < u a := limsup_le_iff (β := βᵒᵈ) h₁ h₂

theorem liminf_le_iff {α β} [ConditionallyCompleteLinearOrder β] {f : Filter α} {u : α → β} {x : β}
    (h₁ : f.IsCoboundedUnder (· ≥ ·) u := by isBoundedDefault)
    (h₂ : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) :
    liminf u f ≤ x ↔ ∀ y > x, ∃ᶠ a in f, u a < y := le_limsup_iff (β := βᵒᵈ) h₁ h₂

variable [ConditionallyCompleteLinearOrder α] {f : Filter α} {b : α}

-- The linter erroneously claims that I'm not referring to `c`
set_option linter.unusedVariables false in
theorem lt_mem_sets_of_limsSup_lt (h : f.IsBounded (· ≤ ·)) (l : f.limsSup < b) :
    ∀ᶠ a in f, a < b :=
  let ⟨c, (h : ∀ᶠ a in f, a ≤ c), hcb⟩ := exists_lt_of_csInf_lt h l
  mem_of_superset h fun _a => hcb.trans_le'

theorem gt_mem_sets_of_limsInf_gt : f.IsBounded (· ≥ ·) → b < f.limsInf → ∀ᶠ a in f, b < a :=
  @lt_mem_sets_of_limsSup_lt αᵒᵈ _ _ _

section Classical

open Classical in
/-- Given an indexed family of sets `s j` over `j : Subtype p` and a function `f`, then
`liminf_reparam j` is equal to `j` if `f` is bounded below on `s j`, and otherwise to some
index `k` such that `f` is bounded below on `s k` (if there exists one).
To ensure good measurability behavior, this index `k` is chosen as the minimal suitable index.
This function is used to write down a liminf in a measurable way,
in `Filter.HasBasis.liminf_eq_ciSup_ciInf` and `Filter.HasBasis.liminf_eq_ite`. -/
noncomputable def liminf_reparam
    (f : ι → α) (s : ι' → Set ι) (p : ι' → Prop) [Countable (Subtype p)] [Nonempty (Subtype p)]
    (j : Subtype p) : Subtype p :=
  let m : Set (Subtype p) := {j | BddBelow (range (fun (i : s j) ↦ f i))}
  let g : ℕ → Subtype p := (exists_surjective_nat _).choose
  have Z : ∃ n, g n ∈ m ∨ ∀ j, j ∉ m := by
    by_cases H : ∃ j, j ∈ m
    · rcases H with ⟨j, hj⟩
      rcases (exists_surjective_nat (Subtype p)).choose_spec j with ⟨n, rfl⟩
      exact ⟨n, Or.inl hj⟩
    · push_neg at H
      exact ⟨0, Or.inr H⟩
  if j ∈ m then j else g (Nat.find Z)

/-- Writing a liminf as a supremum of infimum, in a (possibly non-complete) conditionally complete
linear order. A reparametrization trick is needed to avoid taking the infimum of sets which are
not bounded below. -/
theorem HasBasis.liminf_eq_ciSup_ciInf {v : Filter ι}
    {p : ι' → Prop} {s : ι' → Set ι} [Countable (Subtype p)] [Nonempty (Subtype p)]
    (hv : v.HasBasis p s) {f : ι → α} (hs : ∀ (j : Subtype p), (s j).Nonempty)
    (H : ∃ (j : Subtype p), BddBelow (range (fun (i : s j) ↦ f i))) :
    liminf f v = ⨆ (j : Subtype p), ⨅ (i : s (liminf_reparam f s p j)), f i := by
  classical
  rcases H with ⟨j0, hj0⟩
  let m : Set (Subtype p) := {j | BddBelow (range (fun (i : s j) ↦ f i))}
  have : ∀ (j : Subtype p), Nonempty (s j) := fun j ↦ Nonempty.coe_sort (hs j)
  have A : ⋃ (j : Subtype p), ⋂ (i : s j), Iic (f i) =
         ⋃ (j : Subtype p), ⋂ (i : s (liminf_reparam f s p j)), Iic (f i) := by
    apply Subset.antisymm
    · apply iUnion_subset (fun j ↦ ?_)
      by_cases hj : j ∈ m
      · have : j = liminf_reparam f s p j := by simp only [m, liminf_reparam, hj, ite_true]
        conv_lhs => rw [this]
        apply subset_iUnion _ j
      · simp only [m, mem_setOf_eq, ← nonempty_iInter_Iic_iff, not_nonempty_iff_eq_empty] at hj
        simp only [hj, empty_subset]
    · apply iUnion_subset (fun j ↦ ?_)
      exact subset_iUnion (fun (k : Subtype p) ↦ (⋂ (i : s k), Iic (f i))) (liminf_reparam f s p j)
  have B : ∀ (j : Subtype p), ⋂ (i : s (liminf_reparam f s p j)), Iic (f i) =
                                Iic (⨅ (i : s (liminf_reparam f s p j)), f i) := by
    intro j
    apply (Iic_ciInf _).symm
    change liminf_reparam f s p j ∈ m
    by_cases Hj : j ∈ m
    · simpa only [m, liminf_reparam, if_pos Hj] using Hj
    · simp only [m, liminf_reparam, if_neg Hj]
      have Z : ∃ n, (exists_surjective_nat (Subtype p)).choose n ∈ m ∨ ∀ j, j ∉ m := by
        rcases (exists_surjective_nat (Subtype p)).choose_spec j0 with ⟨n, rfl⟩
        exact ⟨n, Or.inl hj0⟩
      rcases Nat.find_spec Z with hZ|hZ
      · exact hZ
      · exact (hZ j0 hj0).elim
  simp_rw [hv.liminf_eq_sSup_iUnion_iInter, A, B, sSup_iUnion_Iic]

open Classical in
/-- Writing a liminf as a supremum of infimum, in a (possibly non-complete) conditionally complete
linear order. A reparametrization trick is needed to avoid taking the infimum of sets which are
not bounded below. -/
theorem HasBasis.liminf_eq_ite {v : Filter ι} {p : ι' → Prop} {s : ι' → Set ι}
    [Countable (Subtype p)] [Nonempty (Subtype p)] (hv : v.HasBasis p s) (f : ι → α) :
    liminf f v = if ∃ (j : Subtype p), s j = ∅ then sSup univ else
      if ∀ (j : Subtype p), ¬BddBelow (range (fun (i : s j) ↦ f i)) then sSup ∅
      else ⨆ (j : Subtype p), ⨅ (i : s (liminf_reparam f s p j)), f i := by
  by_cases H : ∃ (j : Subtype p), s j = ∅
  · rw [if_pos H]
    rcases H with ⟨j, hj⟩
    simp [hv.liminf_eq_sSup_univ_of_empty j j.2 hj]
  rw [if_neg H]
  by_cases H' : ∀ (j : Subtype p), ¬BddBelow (range (fun (i : s j) ↦ f i))
  · have A : ∀ (j : Subtype p), ⋂ (i : s j), Iic (f i) = ∅ := by
      simp_rw [← not_nonempty_iff_eq_empty, nonempty_iInter_Iic_iff]
      exact H'
    simp_rw [if_pos H', hv.liminf_eq_sSup_iUnion_iInter, A, iUnion_empty]
  rw [if_neg H']
  apply hv.liminf_eq_ciSup_ciInf
  · push_neg at H
    simpa only [nonempty_iff_ne_empty] using H
  · push_neg at H'
    exact H'

/-- Given an indexed family of sets `s j` and a function `f`, then `limsup_reparam j` is equal
to `j` if `f` is bounded above on `s j`, and otherwise to some index `k` such that `f` is bounded
above on `s k` (if there exists one). To ensure good measurability behavior, this index `k` is
chosen as the minimal suitable index. This function is used to write down a limsup in a measurable
way, in `Filter.HasBasis.limsup_eq_ciInf_ciSup` and `Filter.HasBasis.limsup_eq_ite`. -/
noncomputable def limsup_reparam
    (f : ι → α) (s : ι' → Set ι) (p : ι' → Prop) [Countable (Subtype p)] [Nonempty (Subtype p)]
    (j : Subtype p) : Subtype p :=
  liminf_reparam (α := αᵒᵈ) f s p j

/-- Writing a limsup as an infimum of supremum, in a (possibly non-complete) conditionally complete
linear order. A reparametrization trick is needed to avoid taking the supremum of sets which are
not bounded above. -/
theorem HasBasis.limsup_eq_ciInf_ciSup {v : Filter ι}
    {p : ι' → Prop} {s : ι' → Set ι} [Countable (Subtype p)] [Nonempty (Subtype p)]
    (hv : v.HasBasis p s) {f : ι → α} (hs : ∀ (j : Subtype p), (s j).Nonempty)
    (H : ∃ (j : Subtype p), BddAbove (range (fun (i : s j) ↦ f i))) :
    limsup f v = ⨅ (j : Subtype p), ⨆ (i : s (limsup_reparam f s p j)), f i :=
  HasBasis.liminf_eq_ciSup_ciInf (α := αᵒᵈ) hv hs H

open Classical in
/-- Writing a limsup as an infimum of supremum, in a (possibly non-complete) conditionally complete
linear order. A reparametrization trick is needed to avoid taking the supremum of sets which are
not bounded below. -/
theorem HasBasis.limsup_eq_ite {v : Filter ι} {p : ι' → Prop} {s : ι' → Set ι}
    [Countable (Subtype p)] [Nonempty (Subtype p)] (hv : v.HasBasis p s) (f : ι → α) :
    limsup f v = if ∃ (j : Subtype p), s j = ∅ then sInf univ else
      if ∀ (j : Subtype p), ¬BddAbove (range (fun (i : s j) ↦ f i)) then sInf ∅
      else ⨅ (j : Subtype p), ⨆ (i : s (limsup_reparam f s p j)), f i :=
  HasBasis.liminf_eq_ite (α := αᵒᵈ) hv f

end Classical

end ConditionallyCompleteLinearOrder

end Filter

section Order

open Filter

theorem Monotone.isBoundedUnder_le_comp_iff [Nonempty β] [LinearOrder β] [Preorder γ] [NoMaxOrder γ]
    {g : β → γ} {f : α → β} {l : Filter α} (hg : Monotone g) (hg' : Tendsto g atTop atTop) :
    IsBoundedUnder (· ≤ ·) l (g ∘ f) ↔ IsBoundedUnder (· ≤ ·) l f := by
  refine ⟨?_, fun h => h.isBoundedUnder (α := β) hg⟩
  rintro ⟨c, hc⟩; rw [eventually_map] at hc
  obtain ⟨b, hb⟩ : ∃ b, ∀ a ≥ b, c < g a := eventually_atTop.1 (hg'.eventually_gt_atTop c)
  exact ⟨b, hc.mono fun x hx => not_lt.1 fun h => (hb _ h.le).not_le hx⟩

theorem Monotone.isBoundedUnder_ge_comp_iff [Nonempty β] [LinearOrder β] [Preorder γ] [NoMinOrder γ]
    {g : β → γ} {f : α → β} {l : Filter α} (hg : Monotone g) (hg' : Tendsto g atBot atBot) :
    IsBoundedUnder (· ≥ ·) l (g ∘ f) ↔ IsBoundedUnder (· ≥ ·) l f :=
  hg.dual.isBoundedUnder_le_comp_iff hg'

theorem Antitone.isBoundedUnder_le_comp_iff [Nonempty β] [LinearOrder β] [Preorder γ] [NoMaxOrder γ]
    {g : β → γ} {f : α → β} {l : Filter α} (hg : Antitone g) (hg' : Tendsto g atBot atTop) :
    IsBoundedUnder (· ≤ ·) l (g ∘ f) ↔ IsBoundedUnder (· ≥ ·) l f :=
  hg.dual_right.isBoundedUnder_ge_comp_iff hg'

theorem Antitone.isBoundedUnder_ge_comp_iff [Nonempty β] [LinearOrder β] [Preorder γ] [NoMinOrder γ]
    {g : β → γ} {f : α → β} {l : Filter α} (hg : Antitone g) (hg' : Tendsto g atTop atBot) :
    IsBoundedUnder (· ≥ ·) l (g ∘ f) ↔ IsBoundedUnder (· ≤ ·) l f :=
  hg.dual_right.isBoundedUnder_le_comp_iff hg'

theorem GaloisConnection.l_limsup_le [ConditionallyCompleteLattice β]
    [ConditionallyCompleteLattice γ] {f : Filter α} {v : α → β} {l : β → γ} {u : γ → β}
    (gc : GaloisConnection l u)
    (hlv : f.IsBoundedUnder (· ≤ ·) fun x => l (v x) := by isBoundedDefault)
    (hv_co : f.IsCoboundedUnder (· ≤ ·) v := by isBoundedDefault) :
    l (limsup v f) ≤ limsup (fun x => l (v x)) f := by
  refine le_limsSup_of_le hlv fun c hc => ?_
  rw [Filter.eventually_map] at hc
  simp_rw [gc _ _] at hc ⊢
  exact limsSup_le_of_le hv_co hc

theorem OrderIso.limsup_apply {γ} [ConditionallyCompleteLattice β] [ConditionallyCompleteLattice γ]
    {f : Filter α} {u : α → β} (g : β ≃o γ)
    (hu : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault)
    (hu_co : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault)
    (hgu : f.IsBoundedUnder (· ≤ ·) fun x => g (u x) := by isBoundedDefault)
    (hgu_co : f.IsCoboundedUnder (· ≤ ·) fun x => g (u x) := by isBoundedDefault) :
    g (limsup u f) = limsup (fun x => g (u x)) f := by
  refine le_antisymm ((OrderIso.to_galoisConnection g).l_limsup_le hgu hu_co) ?_
  rw [← g.symm.symm_apply_apply <| limsup (fun x => g (u x)) f, g.symm_symm]
  refine g.monotone ?_
  have hf : u = fun i => g.symm (g (u i)) := funext fun i => (g.symm_apply_apply (u i)).symm
  -- Porting note: nth_rw 1 to nth_rw 2
  nth_rw 2 [hf]
  refine (OrderIso.to_galoisConnection g.symm).l_limsup_le ?_ hgu_co
  simp_rw [g.symm_apply_apply]
  exact hu

theorem OrderIso.liminf_apply {γ} [ConditionallyCompleteLattice β] [ConditionallyCompleteLattice γ]
    {f : Filter α} {u : α → β} (g : β ≃o γ)
    (hu : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault)
    (hu_co : f.IsCoboundedUnder (· ≥ ·) u := by isBoundedDefault)
    (hgu : f.IsBoundedUnder (· ≥ ·) fun x => g (u x) := by isBoundedDefault)
    (hgu_co : f.IsCoboundedUnder (· ≥ ·) fun x => g (u x) := by isBoundedDefault) :
    g (liminf u f) = liminf (fun x => g (u x)) f :=
  OrderIso.limsup_apply (β := βᵒᵈ) (γ := γᵒᵈ) g.dual hu hu_co hgu hgu_co

end Order

section MinMax

open Filter

theorem isCoboundedUnder_le_max [LinearOrder β] {f : Filter α} {u v : α → β}
    (h : f.IsCoboundedUnder (· ≤ ·) u ∨ f.IsCoboundedUnder (· ≤ ·) v) :
    f.IsCoboundedUnder (· ≤ ·) (fun a ↦ max (u a) (v a)) := by
  rcases h with (h' | h') <;>
  · rcases h' with ⟨b, hb⟩
    use b
    intro c hc
    apply hb c
    rw [eventually_map] at hc ⊢
    refine hc.mono (fun _ ↦ ?_)
    simp +contextual only [implies_true, max_le_iff, and_imp]

theorem limsup_max [ConditionallyCompleteLinearOrder β] {f : Filter α} {u v : α → β}
    (h₁ : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h₂ : f.IsCoboundedUnder (· ≤ ·) v := by isBoundedDefault)
    (h₃ : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h₄ : f.IsBoundedUnder (· ≤ ·) v := by isBoundedDefault) :
    limsup (fun a ↦ max (u a) (v a)) f = max (limsup u f) (limsup v f) := by
  have bddmax := IsBoundedUnder.sup h₃ h₄
  have cobddmax := isCoboundedUnder_le_max (v := v) (Or.inl h₁)
  apply le_antisymm
  · refine (limsup_le_iff cobddmax bddmax).2 (fun b hb ↦ ?_)
    have hu := eventually_lt_of_limsup_lt (lt_of_le_of_lt (le_max_left _ _) hb) h₃
    have hv := eventually_lt_of_limsup_lt (lt_of_le_of_lt (le_max_right _ _) hb) h₄
    refine mem_of_superset (inter_mem hu hv) (fun _ ↦ by simp)
  · exact max_le (c := limsup (fun a ↦ max (u a) (v a)) f)
      (limsup_le_limsup (Eventually.of_forall (fun a : α ↦ le_max_left (u a) (v a))) h₁ bddmax)
      (limsup_le_limsup (Eventually.of_forall (fun a : α ↦ le_max_right (u a) (v a))) h₂ bddmax)

theorem liminf_min [ConditionallyCompleteLinearOrder β] {f : Filter α} {u v : α → β}
    (h₁ : f.IsCoboundedUnder (· ≥ ·) u := by isBoundedDefault)
    (h₂ : f.IsCoboundedUnder (· ≥ ·) v := by isBoundedDefault)
    (h₃ : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault)
    (h₄ : f.IsBoundedUnder (· ≥ ·) v := by isBoundedDefault) :
    liminf (fun a ↦ min (u a) (v a)) f = min (liminf u f) (liminf v f) :=
  limsup_max (β := βᵒᵈ) h₁ h₂ h₃ h₄

open Finset

theorem isBoundedUnder_le_finset_sup' [LinearOrder β] [Nonempty β] {f : Filter α} {F : ι → α → β}
    {s : Finset ι} (hs : s.Nonempty) (h : ∀ i ∈ s, f.IsBoundedUnder (· ≤ ·) (F i)) :
    f.IsBoundedUnder (· ≤ ·) (fun a ↦ sup' s hs (fun i ↦ F i a)) := by
  choose! m hm using h
  use sup' s hs m
  simp only [eventually_map] at hm ⊢
  rw [← eventually_all_finset s] at hm
  refine hm.mono fun a h ↦ ?_
  simp only [Finset.sup'_apply, sup'_le_iff]
  exact fun i i_s ↦ le_trans (h i i_s) (le_sup' m i_s)

theorem isCoboundedUnder_le_finset_sup' [LinearOrder β] {f : Filter α} {F : ι → α → β}
    {s : Finset ι} (hs : s.Nonempty) (h : ∃ i ∈ s, f.IsCoboundedUnder (· ≤ ·) (F i)) :
    f.IsCoboundedUnder (· ≤ ·) (fun a ↦ sup' s hs (fun i ↦ F i a)) := by
  rcases h with ⟨i, i_s, b, hb⟩
  use b
  refine fun c hc ↦ hb c ?_
  rw [eventually_map] at hc ⊢
  refine hc.mono fun a h ↦ ?_
  simp only [Finset.sup'_apply, sup'_le_iff] at h ⊢
  exact h i i_s

theorem isBoundedUnder_le_finset_sup [LinearOrder β] [OrderBot β] {f : Filter α} {F : ι → α → β}
    {s : Finset ι} (h : ∀ i ∈ s, f.IsBoundedUnder (· ≤ ·) (F i)) :
    f.IsBoundedUnder (· ≤ ·) (fun a ↦ sup s (fun i ↦ F i a)) := by
  choose! m hm using h
  use sup s m
  simp only [eventually_map] at hm ⊢
  rw [← eventually_all_finset s] at hm
  exact hm.mono fun _ h ↦ sup_mono_fun h

theorem isBoundedUnder_ge_finset_inf' [LinearOrder β] [Nonempty β] {f : Filter α} {F : ι → α → β}
    {s : Finset ι} (hs : s.Nonempty) (h : ∀ i ∈ s, f.IsBoundedUnder (· ≥ ·) (F i)) :
    f.IsBoundedUnder (· ≥ ·) (fun a ↦ inf' s hs (fun i ↦ F i a)) :=
  isBoundedUnder_le_finset_sup' (β := βᵒᵈ) hs h

theorem isCoboundedUnder_ge_finset_inf' [LinearOrder β] {f : Filter α} {F : ι → α → β}
    {s : Finset ι} (hs : s.Nonempty) (h : ∃ i ∈ s, f.IsCoboundedUnder (· ≥ ·) (F i)) :
    f.IsCoboundedUnder (· ≥ ·) (fun a ↦ inf' s hs (fun i ↦ F i a)) :=
  isCoboundedUnder_le_finset_sup' (β := βᵒᵈ) hs h

theorem isBoundedUnder_ge_finset_inf [LinearOrder β] [OrderTop β] {f : Filter α} {F : ι → α → β}
    {s : Finset ι} (h : ∀ i ∈ s, f.IsBoundedUnder (· ≥ ·) (F i)) :
    f.IsBoundedUnder (· ≥ ·) (fun a ↦ inf s (fun i ↦ F i a)) :=
  isBoundedUnder_le_finset_sup (β := βᵒᵈ) h

theorem limsup_finset_sup' [ConditionallyCompleteLinearOrder β] {f : Filter α}
    {F : ι → α → β} {s : Finset ι} (hs : s.Nonempty)
    (h₁ : ∀ i ∈ s, f.IsCoboundedUnder (· ≤ ·) (F i) := by exact fun _ _ ↦ by isBoundedDefault)
    (h₂ : ∀ i ∈ s, f.IsBoundedUnder (· ≤ ·) (F i) := by exact fun _ _ ↦ by isBoundedDefault) :
    limsup (fun a ↦ sup' s hs (fun i ↦ F i a)) f = sup' s hs (fun i ↦ limsup (F i) f) := by
  have bddsup := isBoundedUnder_le_finset_sup' hs h₂
  apply le_antisymm
  · have h₃ : ∃ i ∈ s, f.IsCoboundedUnder (· ≤ ·) (F i) := by
      rcases hs with ⟨i, i_s⟩
      use i, i_s
      exact h₁ i i_s
    have cobddsup := isCoboundedUnder_le_finset_sup' hs h₃
    refine (limsup_le_iff cobddsup bddsup).2 (fun b hb ↦ ?_)
    rw [eventually_iff_exists_mem]
    use ⋂ i ∈ s, {a | F i a < b}
    split_ands
    · rw [biInter_finset_mem]
      suffices key : ∀ i ∈ s, ∀ᶠ a in f, F i a < b from fun i i_s ↦ eventually_iff.1 (key i i_s)
      intro i i_s
      apply eventually_lt_of_limsup_lt _ (h₂ i i_s)
      exact lt_of_le_of_lt (Finset.le_sup' (f := fun i ↦ limsup (F i) f) i_s) hb
    · simp only [mem_iInter, mem_setOf_eq, Finset.sup'_apply, sup'_lt_iff, imp_self, implies_true]
  · apply Finset.sup'_le hs (fun i ↦ limsup (F i) f)
    refine fun i i_s ↦ limsup_le_limsup (Eventually.of_forall (fun a ↦ ?_)) (h₁ i i_s) bddsup
    simp only [Finset.sup'_apply, le_sup'_iff]
    use i, i_s

theorem limsup_finset_sup [ConditionallyCompleteLinearOrder β] [OrderBot β] {f : Filter α}
    {F : ι → α → β} {s : Finset ι}
    (h₁ : ∀ i ∈ s, f.IsCoboundedUnder (· ≤ ·) (F i) := by exact fun _ _ ↦ by isBoundedDefault)
    (h₂ : ∀ i ∈ s, f.IsBoundedUnder (· ≤ ·) (F i) := by exact fun _ _ ↦ by isBoundedDefault) :
    limsup (fun a ↦ sup s (fun i ↦ F i a)) f = sup s (fun i ↦ limsup (F i) f) := by
  rcases eq_or_neBot f with (rfl | _)
  · simp [limsup_eq, csInf_univ]
  rcases Finset.eq_empty_or_nonempty s with (rfl | s_nemp)
  · simp only [Finset.sup_apply, sup_empty, limsup_const]
  rw [← Finset.sup'_eq_sup s_nemp fun i ↦ limsup (F i) f, ← limsup_finset_sup' s_nemp h₁ h₂]
  congr
  ext a
  exact Eq.symm (Finset.sup'_eq_sup s_nemp (fun i ↦ F i a))

theorem liminf_finset_inf' [ConditionallyCompleteLinearOrder β] {f : Filter α}
    {F : ι → α → β} {s : Finset ι} (hs : s.Nonempty)
    (h₁ : ∀ i ∈ s, f.IsCoboundedUnder (· ≥ ·) (F i) := by exact fun _ _ ↦ by isBoundedDefault)
    (h₂ : ∀ i ∈ s, f.IsBoundedUnder (· ≥ ·) (F i) := by exact fun _ _ ↦ by isBoundedDefault) :
    liminf (fun a ↦ inf' s hs (fun i ↦ F i a)) f = inf' s hs (fun i ↦ liminf (F i) f) :=
  limsup_finset_sup' (β := βᵒᵈ) hs h₁ h₂

theorem liminf_finset_inf [ConditionallyCompleteLinearOrder β] [OrderTop β] {f : Filter α}
    {F : ι → α → β} {s : Finset ι}
    (h₁ : ∀ i ∈ s, f.IsCoboundedUnder (· ≥ ·) (F i) := by exact fun _ _ ↦ by isBoundedDefault)
    (h₂ : ∀ i ∈ s, f.IsBoundedUnder (· ≥ ·) (F i) := by exact fun _ _ ↦ by isBoundedDefault) :
    liminf (fun a ↦ inf s (fun i ↦ F i a)) f = inf s (fun i ↦ liminf (F i) f) :=
  limsup_finset_sup (β := βᵒᵈ) h₁ h₂

end MinMax

section frequently_bounded

variable {R S : Type*} {F : Filter R} [LinearOrder R] [LinearOrder S]

lemma Monotone.frequently_ge_map_of_frequently_ge {f : R → S} (f_incr : Monotone f)
    {l : R} (freq_ge : ∃ᶠ x in F, l ≤ x) :
    ∃ᶠ x' in F.map f, f l ≤ x' := by
  refine fun ev ↦ freq_ge ?_
  simp only [not_le, not_lt] at ev freq_ge ⊢
  filter_upwards [ev] with z hz
  by_contra con
  exact lt_irrefl (f l) <| lt_of_le_of_lt (f_incr <| not_lt.mp con) hz

lemma Monotone.frequently_le_map_of_frequently_le {f : R → S} (f_incr : Monotone f)
    {u : R} (freq_le : ∃ᶠ x in F, x ≤ u) :
    ∃ᶠ y in F.map f, y ≤ f u := by
  refine fun ev ↦ freq_le ?_
  simp only [not_le, not_lt] at ev freq_le ⊢
  filter_upwards [ev] with z hz
  by_contra con
  apply lt_irrefl (f u) <| lt_of_lt_of_le hz <| f_incr (not_lt.mp con)

lemma Antitone.frequently_le_map_of_frequently_ge {f : R → S} (f_decr : Antitone f)
    {l : R} (frbdd : ∃ᶠ x in F, l ≤ x) :
    ∃ᶠ y in F.map f, y ≤ f l :=
  Monotone.frequently_ge_map_of_frequently_ge (S := Sᵒᵈ) f_decr frbdd

lemma Antitone.frequently_ge_map_of_frequently_le {f : R → S} (f_decr : Antitone f)
    {u : R} (frbdd : ∃ᶠ x in F, x ≤ u) :
    ∃ᶠ y in F.map f, f u ≤ y :=
  Monotone.frequently_le_map_of_frequently_le (S := Sᵒᵈ) f_decr frbdd

lemma Monotone.isCoboundedUnder_le_of_isCobounded {f : R → S} (f_incr : Monotone f)
    [NeBot F] (cobdd : IsCobounded (· ≤ ·) F) :
    F.IsCoboundedUnder (· ≤ ·) f := by
  obtain ⟨l, hl⟩ := IsCobounded.frequently_ge cobdd
  exact IsCobounded.of_frequently_ge <| f_incr.frequently_ge_map_of_frequently_ge hl

lemma Monotone.isCoboundedUnder_ge_of_isCobounded {f : R → S} (f_incr : Monotone f)
    [NeBot F] (cobdd : IsCobounded (· ≥ ·) F) :
    F.IsCoboundedUnder (· ≥ ·) f :=
  Monotone.isCoboundedUnder_le_of_isCobounded (R := Rᵒᵈ) (S := Sᵒᵈ) f_incr.dual cobdd

lemma Antitone.isCoboundedUnder_le_of_isCobounded {f : R → S} (f_decr : Antitone f)
    [NeBot F] (cobdd : IsCobounded (· ≥ ·) F) :
    F.IsCoboundedUnder (· ≤ ·) f :=
  Monotone.isCoboundedUnder_le_of_isCobounded (R := Rᵒᵈ) f_decr.dual cobdd

lemma Antitone.isCoboundedUnder_ge_of_isCobounded {f : R → S} (f_decr : Antitone f)
    [NeBot F] (cobdd : IsCobounded (· ≤ ·) F) :
    F.IsCoboundedUnder (· ≥ ·) f :=
  Monotone.isCoboundedUnder_le_of_isCobounded (S := Sᵒᵈ) f_decr cobdd

end frequently_bounded

set_option linter.style.longFile 1900
