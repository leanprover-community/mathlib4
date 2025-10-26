/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Johannes Hölzl, Rémy Degenne
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Order.Filter.Cofinite

/-!
# Lemmas about `Is(Co)Bounded(Under)`

This file proves several lemmas about
`IsBounded`, `IsBoundedUnder`, `IsCobounded` and `IsCoboundedUnder`.
-/

open Set Function

variable {α β γ ι : Type*}

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

theorem isBounded_top : IsBounded r ⊤ ↔ ∃ t, ∀ x, r x t := by simp [IsBounded]

theorem isBounded_principal (s : Set α) : IsBounded r (𝓟 s) ↔ ∃ t, ∀ x ∈ s, r x t := by
  simp [IsBounded]

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
  tauto

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
    eq_empty_of_subset_empty fun x hx => (not_le_of_gt h) (le_trans hx.2 hx.1)
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
  simp +contextual [IsCobounded,
    exists_true_iff_nonempty]

theorem isCobounded_principal (s : Set α) :
    (𝓟 s).IsCobounded r ↔ ∃ b, ∀ a, (∀ x ∈ s, r x a) → r b a := by simp [IsCobounded]

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
  exact not_lt_of_ge ht ht'

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
  [AddLeftMono R] [AddRightMono R]
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

lemma isBoundedUnder_le_mul_of_nonneg [Preorder α] [Mul α] [Zero α] [PosMulMono α]
    [MulPosMono α] {f : Filter ι} {u v : ι → α} (h₁ : ∃ᶠ x in f, 0 ≤ u x)
    (h₂ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f u) (h₃ : 0 ≤ᶠ[f] v)
    (h₄ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f v) :
    IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f (u * v) := by
  obtain ⟨U, hU⟩ := h₂.eventually_le
  obtain ⟨V, hV⟩ := h₄.eventually_le
  refine isBoundedUnder_of_eventually_le (a := U * V) ?_
  filter_upwards [hU, hV, h₃] with x x_U x_V v_0
  have U_0 : 0 ≤ U := by
    obtain ⟨y, y_0, y_U⟩ := (h₁.and_eventually hU).exists
    exact y_0.trans y_U
  exact (mul_le_mul_of_nonneg_right x_U v_0).trans (mul_le_mul_of_nonneg_left x_V U_0)

lemma isCoboundedUnder_ge_mul_of_nonneg [LinearOrder α] [Mul α] [Zero α] [PosMulMono α]
    [MulPosMono α] {f : Filter ι} [f.NeBot] {u v : ι → α} (h₁ : 0 ≤ᶠ[f] u)
    (h₂ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f u)
    (h₃ : 0 ≤ᶠ[f] v)
    (h₄ : IsCoboundedUnder (fun x1 x2 ↦ x1 ≥ x2) f v) :
    IsCoboundedUnder (fun x1 x2 ↦ x1 ≥ x2) f (u * v) := by
  obtain ⟨U, hU⟩ := h₂.eventually_le
  obtain ⟨V, hV⟩ := h₄.frequently_le
  refine IsCoboundedUnder.of_frequently_le (a := U * V) ?_
  apply (hV.and_eventually (hU.and (h₁.and h₃))).mono
  intro x ⟨x_V, x_U, u_0, v_0⟩
  exact (mul_le_mul_of_nonneg_right x_U v_0).trans (mul_le_mul_of_nonneg_left x_V (u_0.trans x_U))

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
theorem _root_.OrderIso.isBoundedUnder_ge_comp [LE α] [LE β] (e : α ≃o β) {l : Filter γ}
    {u : γ → α} : (IsBoundedUnder (· ≥ ·) l fun x => e (u x)) ↔ IsBoundedUnder (· ≥ ·) l u :=
  OrderIso.isBoundedUnder_le_comp e.dual

@[to_additive (attr := simp)]
theorem isBoundedUnder_le_inv [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]
    {l : Filter β} {u : β → α} :
    (IsBoundedUnder (· ≤ ·) l fun x => (u x)⁻¹) ↔ IsBoundedUnder (· ≥ ·) l u :=
  (OrderIso.inv α).isBoundedUnder_ge_comp

@[to_additive (attr := simp)]
theorem isBoundedUnder_ge_inv [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]
    {l : Filter β} {u : β → α} :
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

theorem isBoundedUnder_le_abs [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    {f : Filter β} {u : β → α} :
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

end Filter

open Filter

section Order

theorem Monotone.isBoundedUnder_le_comp_iff [Nonempty β] [LinearOrder β] [Preorder γ] [NoMaxOrder γ]
    {g : β → γ} {f : α → β} {l : Filter α} (hg : Monotone g) (hg' : Tendsto g atTop atTop) :
    IsBoundedUnder (· ≤ ·) l (g ∘ f) ↔ IsBoundedUnder (· ≤ ·) l f := by
  refine ⟨?_, fun h => h.isBoundedUnder (α := β) hg⟩
  rintro ⟨c, hc⟩; rw [eventually_map] at hc
  obtain ⟨b, hb⟩ : ∃ b, ∀ a ≥ b, c < g a := eventually_atTop.1 (hg'.eventually_gt_atTop c)
  exact ⟨b, hc.mono fun x hx => not_lt.1 fun h => (hb _ h.le).not_ge hx⟩

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

end Order

section MinMax

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
    simp +contextual only [implies_true, max_le_iff]

open Finset

theorem isBoundedUnder_le_finset_sup' [LinearOrder β] [Nonempty β] {f : Filter α} {F : ι → α → β}
    {s : Finset ι} (hs : s.Nonempty) (h : ∀ i ∈ s, f.IsBoundedUnder (· ≤ ·) (F i)) :
    f.IsBoundedUnder (· ≤ ·) (fun a ↦ sup' s hs (fun i ↦ F i a)) := by
  choose! m hm using h
  use sup' s hs m
  simp only [eventually_map] at hm ⊢
  rw [← eventually_all_finset s] at hm
  refine hm.mono fun a h ↦ ?_
  simp only [sup'_le_iff]
  exact fun i i_s ↦ le_trans (h i i_s) (le_sup' m i_s)

theorem isCoboundedUnder_le_finset_sup' [LinearOrder β] {f : Filter α} {F : ι → α → β}
    {s : Finset ι} (hs : s.Nonempty) (h : ∃ i ∈ s, f.IsCoboundedUnder (· ≤ ·) (F i)) :
    f.IsCoboundedUnder (· ≤ ·) (fun a ↦ sup' s hs (fun i ↦ F i a)) := by
  rcases h with ⟨i, i_s, b, hb⟩
  use b
  refine fun c hc ↦ hb c ?_
  rw [eventually_map] at hc ⊢
  refine hc.mono fun a h ↦ ?_
  simp only [sup'_le_iff] at h ⊢
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

end MinMax

section FrequentlyBounded

variable {R S : Type*} {F : Filter R} [LinearOrder R] [LinearOrder S]

lemma Monotone.frequently_ge_map_of_frequently_ge {f : R → S} (f_incr : Monotone f)
    {l : R} (freq_ge : ∃ᶠ x in F, l ≤ x) :
    ∃ᶠ x' in F.map f, f l ≤ x' := by
  refine fun ev ↦ freq_ge ?_
  simp only [not_le] at ev freq_ge ⊢
  filter_upwards [ev] with z hz
  by_contra con
  exact lt_irrefl (f l) <| lt_of_le_of_lt (f_incr <| not_lt.mp con) hz

lemma Monotone.frequently_le_map_of_frequently_le {f : R → S} (f_incr : Monotone f)
    {u : R} (freq_le : ∃ᶠ x in F, x ≤ u) :
    ∃ᶠ y in F.map f, y ≤ f u := by
  refine fun ev ↦ freq_le ?_
  simp only [not_le] at ev freq_le ⊢
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

end FrequentlyBounded
