/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Order.Filter.AtTopBot.Disjoint
public import Mathlib.Order.Filter.Tendsto

/-!
# Limits of `Filter.atTop` and `Filter.atBot`

In this file we prove many lemmas on the combination of `Filter.atTop` and `Filter.atBot`
and `Tendsto`.
-/
set_option backward.defeqAttrib.useBackward true

public section

assert_not_exists Finset

variable {ι ι' α β γ : Type*}

open Set

namespace Filter

@[to_dual]
theorem not_tendsto_const_atTop [Preorder α] [NoTopOrder α] (x : α) (l : Filter β) [l.NeBot] :
    ¬Tendsto (fun _ => x) l atTop :=
  tendsto_const_pure.not_tendsto (disjoint_pure_atTop x)

@[to_dual eventually_lt_atBot]
protected theorem Tendsto.eventually_gt_atTop [Preorder β] [NoTopOrder β] {f : α → β} {l : Filter α}
    (hf : Tendsto f l atTop) (c : β) : ∀ᶠ x in l, c < f x :=
  hf.eventually (eventually_gt_atTop c)

@[to_dual eventually_le_atBot]
protected theorem Tendsto.eventually_ge_atTop [Preorder β] {f : α → β} {l : Filter α}
    (hf : Tendsto f l atTop) (c : β) : ∀ᶠ x in l, c ≤ f x :=
  hf.eventually (eventually_ge_atTop c)

@[to_dual]
protected theorem Tendsto.eventually_ne_atTop [Preorder β] [NoTopOrder β] {f : α → β} {l : Filter α}
    (hf : Tendsto f l atTop) (c : β) : ∀ᶠ x in l, f x ≠ c :=
  hf.eventually (eventually_ne_atTop c)

protected theorem Tendsto.eventually_ne_atTop' [Preorder β] [NoTopOrder β] {f : α → β}
    {l : Filter α} (hf : Tendsto f l atTop) (c : α) : ∀ᶠ x in l, x ≠ c :=
  (hf.eventually_ne_atTop (f c)).mono fun _ => ne_of_apply_ne f

@[to_dual OrderBot.atBot_eq]
theorem OrderTop.atTop_eq (α) [PartialOrder α] [OrderTop α] : (atTop : Filter α) = pure ⊤ := by
  rw [isTop_top.atTop_eq, Ici_top, principal_singleton]

@[to_dual]
theorem tendsto_atTop_pure [PartialOrder α] [OrderTop α] (f : α → β) :
    Tendsto f atTop (pure <| f ⊤) :=
  (OrderTop.atTop_eq α).symm ▸ tendsto_pure_pure _ _

@[to_dual]
theorem tendsto_atTop [Preorder β] {m : α → β} {f : Filter α} :
    Tendsto m f atTop ↔ ∀ b, ∀ᶠ a in f, b ≤ m a := by
  simp only [atTop, tendsto_iInf, tendsto_principal, mem_Ici]

@[to_dual]
theorem tendsto_atTop_mono' [Preorder β] (l : Filter α) ⦃f₁ f₂ : α → β⦄ (h : f₁ ≤ᶠ[l] f₂)
    (h₁ : Tendsto f₁ l atTop) : Tendsto f₂ l atTop :=
  tendsto_atTop.2 fun b => by filter_upwards [tendsto_atTop.1 h₁ b, h] with x using le_trans

@[to_dual]
theorem tendsto_atTop_mono [Preorder β] {l : Filter α} {f g : α → β} (h : ∀ n, f n ≤ g n) :
    Tendsto f l atTop → Tendsto g l atTop :=
  tendsto_atTop_mono' l <| Eventually.of_forall h

end Filter

namespace Filter

/-!
### Sequences
-/

theorem _root_.StrictMono.tendsto_atTop {φ : ℕ → ℕ} (h : StrictMono φ) : Tendsto φ atTop atTop :=
  tendsto_atTop_mono h.id_le tendsto_id

/-- If `f` is a monotone function and `g` tends to `atTop` along a nontrivial filter.
then the upper bounds of the range of `f ∘ g`
are the same as the upper bounds of the range of `f`.

This lemma together with `exists_seq_monotone_tendsto_atTop_atTop` below
is useful to reduce a statement
about a monotone family indexed by a type with countably generated `atTop` (e.g., `ℝ`)
to the case of a family indexed by natural numbers. -/
@[to_dual
/-- If `f` is a monotone function and `g` tends to `atBot` along a nontrivial filter.
then the lower bounds of the range of `f ∘ g`
are the same as the lower bounds of the range of `f`. -/]
theorem _root_.Monotone.upperBounds_range_comp_tendsto_atTop [Preorder β] [Preorder γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Monotone f) {g : α → β} (hg : Tendsto g l atTop) :
    upperBounds (range (f ∘ g)) = upperBounds (range f) := by
  refine Subset.antisymm ?_ (upperBounds_mono_set <| range_comp_subset_range _ _)
  rintro c hc _ ⟨b, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, b ≤ g a := (hg.eventually_ge_atTop b).exists
  exact (hf ha).trans <| hc <| mem_range_self _

/-- If `f` is an antitone function and `g` tends to `atTop` along a nontrivial filter.
then the upper bounds of the range of `f ∘ g`
are the same as the upper bounds of the range of `f`. -/
@[to_dual
/-- If `f` is an antitone function and `g` tends to `atBot` along a nontrivial filter.
then the upper bounds of the range of `f ∘ g`
are the same as the upper bounds of the range of `f`. -/]
theorem _root_.Antitone.lowerBounds_range_comp_tendsto_atTop [Preorder β] [Preorder γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Antitone f) {g : α → β} (hg : Tendsto g l atTop) :
    lowerBounds (range (f ∘ g)) = lowerBounds (range f) :=
  hf.dual_left.lowerBounds_range_comp_tendsto_atBot hg

@[to_dual]
theorem tendsto_atTop_atTop_of_monotone [Preorder α] [Preorder β] {f : α → β} (hf : Monotone f)
    (h : ∀ b, ∃ a, b ≤ f a) : Tendsto f atTop atTop :=
  tendsto_iInf.2 fun b =>
    tendsto_principal.2 <|
      let ⟨a, ha⟩ := h b
      mem_of_superset (mem_atTop a) fun _a' ha' => le_trans ha (hf ha')

@[to_dual]
theorem tendsto_atTop_atBot_of_antitone [Preorder α] [Preorder β] {f : α → β} (hf : Antitone f)
    (h : ∀ b, ∃ a, f a ≤ b) : Tendsto f atTop atBot :=
  @tendsto_atTop_atTop_of_monotone _ βᵒᵈ _ _ _ hf h

@[to_dual]
alias _root_.Monotone.tendsto_atTop_atTop := tendsto_atTop_atTop_of_monotone

@[to_dual]
theorem comap_embedding_atTop [Preorder β] [Preorder γ] {e : β → γ}
    (hm : ∀ b₁ b₂, e b₁ ≤ e b₂ ↔ b₁ ≤ b₂) (hu : ∀ c, ∃ b, c ≤ e b) : comap e atTop = atTop :=
  le_antisymm
    (le_iInf fun b =>
      le_principal_iff.2 <| mem_comap.2 ⟨Ici (e b), mem_atTop _, fun _ => (hm _ _).1⟩)
    (tendsto_atTop_atTop_of_monotone (fun _ _ => (hm _ _).2) hu).le_comap

/-- A function `f` goes to `∞` independent of an order-preserving embedding `e`. -/
@[to_dual (reorder := hm (b₁ b₂))
/-- A function `f` goes to `-∞` independent of an order-preserving embedding `e`. -/]
theorem tendsto_atTop_embedding [Preorder β] [Preorder γ] {f : α → β} {e : β → γ} {l : Filter α}
    (hm : ∀ b₁ b₂, e b₁ ≤ e b₂ ↔ b₁ ≤ b₂) (hu : ∀ c, ∃ b, c ≤ e b) :
    Tendsto (e ∘ f) l atTop ↔ Tendsto f l atTop := by
  rw [← comap_embedding_atTop hm hu, tendsto_comap_iff]

/-- If `u` is a monotone function with linear ordered codomain and the range of `u` is not bounded
above, then `Tendsto u atTop atTop`. -/
@[to_dual
/-- If `u` is a monotone function with linear ordered codomain and the range of `u` is not bounded
below, then `Tendsto u atBot atBot`. -/]
theorem tendsto_atTop_atTop_of_monotone' [Preorder ι] [LinearOrder α] {u : ι → α} (h : Monotone u)
    (H : ¬BddAbove (range u)) : Tendsto u atTop atTop := by
  apply h.tendsto_atTop_atTop
  intro b
  rcases not_bddAbove_iff.1 H b with ⟨_, ⟨N, rfl⟩, hN⟩
  exact ⟨N, le_of_lt hN⟩

/-- If a monotone function `u : ι → α` tends to `atTop` along *some* non-trivial filter `l`, then
it tends to `atTop` along `atTop`. -/
@[to_dual
/-- If a monotone function `u : ι → α` tends to `atBot` along *some* non-trivial filter `l`, then
it tends to `atBot` along `atBot`. -/]
theorem tendsto_atTop_of_monotone_of_filter [Preorder ι] [Preorder α] {l : Filter ι} {u : ι → α}
    (h : Monotone u) [NeBot l] (hu : Tendsto u l atTop) : Tendsto u atTop atTop :=
  h.tendsto_atTop_atTop fun b => (hu.eventually (mem_atTop b)).exists

@[to_dual]
theorem tendsto_atTop_of_monotone_of_subseq [Preorder ι] [Preorder α] {u : ι → α} {φ : ι' → ι}
    (h : Monotone u) {l : Filter ι'} [NeBot l] (H : Tendsto (u ∘ φ) l atTop) :
    Tendsto u atTop atTop :=
  tendsto_atTop_of_monotone_of_filter h (tendsto_map' H)

end Filter
