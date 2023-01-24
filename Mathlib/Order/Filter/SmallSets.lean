/-
Copyright (c) 2022 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Floris van Doorn, Yury Kudryashov

! This file was ported from Lean 3 source module order.filter.small_sets
! leanprover-community/mathlib commit 8631e2d5ea77f6c13054d9151d82b83069680cb1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Filter.Lift
import Mathbin.Order.Filter.AtTopBot

/-!
# The filter of small sets

This file defines the filter of small sets w.r.t. a filter `f`, which is the largest filter
containing all powersets of members of `f`.

`g` converges to `f.small_sets` if for all `s ∈ f`, eventually we have `g x ⊆ s`.

An example usage is that if `f : ι → E → ℝ` is a family of nonnegative functions with integral 1,
then saying that `λ i, support (f i)` tendsto `(𝓝 0).small_sets` is a way of saying that
`f` tends to the Dirac delta distribution.
-/


open Filter

open Filter Set

variable {α β : Type _} {ι : Sort _}

namespace Filter

variable {l l' la : Filter α} {lb : Filter β}

/-- The filter `l.small_sets` is the largest filter containing all powersets of members of `l`. -/
def smallSets (l : Filter α) : Filter (Set α) :=
  l.lift' powerset
#align filter.small_sets Filter.smallSets

theorem smallSets_eq_generate {f : Filter α} : f.smallSets = generate (powerset '' f.sets) :=
  by
  simp_rw [generate_eq_binfi, small_sets, infᵢ_image]
  rfl
#align filter.small_sets_eq_generate Filter.smallSets_eq_generate

theorem HasBasis.smallSets {p : ι → Prop} {s : ι → Set α} (h : HasBasis l p s) :
    HasBasis l.smallSets p fun i => 𝒫 s i :=
  h.lift' monotone_powerset
#align filter.has_basis.small_sets Filter.HasBasis.smallSets

theorem hasBasis_smallSets (l : Filter α) :
    HasBasis l.smallSets (fun t : Set α => t ∈ l) powerset :=
  l.basis_sets.smallSets
#align filter.has_basis_small_sets Filter.hasBasis_smallSets

/-- `g` converges to `f.small_sets` if for all `s ∈ f`, eventually we have `g x ⊆ s`. -/
theorem tendsto_smallSets_iff {f : α → Set β} :
    Tendsto f la lb.smallSets ↔ ∀ t ∈ lb, ∀ᶠ x in la, f x ⊆ t :=
  (hasBasis_smallSets lb).tendsto_right_iff
#align filter.tendsto_small_sets_iff Filter.tendsto_smallSets_iff

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (t «expr ⊆ » s) -/
theorem eventually_smallSets {p : Set α → Prop} :
    (∀ᶠ s in l.smallSets, p s) ↔ ∃ s ∈ l, ∀ (t) (_ : t ⊆ s), p t :=
  eventually_lift'_iff monotone_powerset
#align filter.eventually_small_sets Filter.eventually_smallSets

theorem eventually_small_sets' {p : Set α → Prop} (hp : ∀ ⦃s t⦄, s ⊆ t → p t → p s) :
    (∀ᶠ s in l.smallSets, p s) ↔ ∃ s ∈ l, p s :=
  eventually_smallSets.trans <|
    exists₂_congr fun s hsf => ⟨fun H => H s Subset.rfl, fun hs t ht => hp ht hs⟩
#align filter.eventually_small_sets' Filter.eventually_small_sets'

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (s «expr ⊆ » t) -/
theorem frequently_smallSets {p : Set α → Prop} :
    (∃ᶠ s in l.smallSets, p s) ↔ ∀ t ∈ l, ∃ (s : _)(_ : s ⊆ t), p s :=
  l.has_basis_small_sets.frequently_iff
#align filter.frequently_small_sets Filter.frequently_smallSets

theorem frequently_smallSets_mem (l : Filter α) : ∃ᶠ s in l.smallSets, s ∈ l :=
  frequently_smallSets.2 fun t ht => ⟨t, Subset.rfl, ht⟩
#align filter.frequently_small_sets_mem Filter.frequently_smallSets_mem

theorem HasAntitoneBasis.tendsto_smallSets {ι} [Preorder ι] {s : ι → Set α}
    (hl : l.HasAntitoneBasis s) : Tendsto s atTop l.smallSets :=
  tendsto_smallSets_iff.2 fun t ht => hl.eventually_subset ht
#align filter.has_antitone_basis.tendsto_small_sets Filter.HasAntitoneBasis.tendsto_smallSets

@[mono]
theorem monotone_smallSets : Monotone (@smallSets α) :=
  monotone_lift' monotone_id monotone_const
#align filter.monotone_small_sets Filter.monotone_smallSets

@[simp]
theorem smallSets_bot : (⊥ : Filter α).smallSets = pure ∅ := by
  rw [small_sets, lift'_bot monotone_powerset, powerset_empty, principal_singleton]
#align filter.small_sets_bot Filter.smallSets_bot

@[simp]
theorem smallSets_top : (⊤ : Filter α).smallSets = ⊤ := by
  rw [small_sets, lift'_top, powerset_univ, principal_univ]
#align filter.small_sets_top Filter.smallSets_top

@[simp]
theorem smallSets_principal (s : Set α) : (𝓟 s).smallSets = 𝓟 (𝒫 s) :=
  lift'_principal monotone_powerset
#align filter.small_sets_principal Filter.smallSets_principal

theorem smallSets_comap (l : Filter β) (f : α → β) :
    (comap f l).smallSets = l.lift' (powerset ∘ preimage f) :=
  comap_lift'_eq2 monotone_powerset
#align filter.small_sets_comap Filter.smallSets_comap

theorem comap_smallSets (l : Filter β) (f : α → Set β) :
    comap f l.smallSets = l.lift' (preimage f ∘ powerset) :=
  comap_lift'_eq
#align filter.comap_small_sets Filter.comap_smallSets

theorem smallSets_infᵢ {f : ι → Filter α} : (infᵢ f).smallSets = ⨅ i, (f i).smallSets :=
  lift'_infᵢ_of_map_univ powerset_inter powerset_univ
#align filter.small_sets_infi Filter.smallSets_infᵢ

theorem smallSets_inf (l₁ l₂ : Filter α) : (l₁ ⊓ l₂).smallSets = l₁.smallSets ⊓ l₂.smallSets :=
  lift'_inf _ _ powerset_inter
#align filter.small_sets_inf Filter.smallSets_inf

instance smallSets_neBot (l : Filter α) : NeBot l.smallSets :=
  (lift'_neBot_iff monotone_powerset).2 fun _ _ => powerset_nonempty
#align filter.small_sets_ne_bot Filter.smallSets_neBot

theorem Tendsto.smallSets_mono {s t : α → Set β} (ht : Tendsto t la lb.smallSets)
    (hst : ∀ᶠ x in la, s x ⊆ t x) : Tendsto s la lb.smallSets :=
  by
  rw [tendsto_small_sets_iff] at ht⊢
  exact fun u hu => (ht u hu).mp (hst.mono fun a hst ht => subset.trans hst ht)
#align filter.tendsto.small_sets_mono Filter.Tendsto.smallSets_mono

/-- Generalized **squeeze theorem** (also known as **sandwich theorem**). If `s : α → set β` is a
family of sets that tends to `filter.small_sets lb` along `la` and `f : α → β` is a function such
that `f x ∈ s x` eventually along `la`, then `f` tends to `lb` along `la`.

If `s x` is the closed interval `[g x, h x]` for some functions `g`, `h` that tend to the same limit
`𝓝 y`, then we obtain the standard squeeze theorem, see
`tendsto_of_tendsto_of_tendsto_of_le_of_le'`. -/
theorem Tendsto.of_smallSets {s : α → Set β} {f : α → β} (hs : Tendsto s la lb.smallSets)
    (hf : ∀ᶠ x in la, f x ∈ s x) : Tendsto f la lb := fun t ht =>
  hf.mp <| (tendsto_smallSets_iff.mp hs t ht).mono fun x h₁ h₂ => h₁ h₂
#align filter.tendsto.of_small_sets Filter.Tendsto.of_smallSets

@[simp]
theorem eventually_smallSets_eventually {p : α → Prop} :
    (∀ᶠ s in l.smallSets, ∀ᶠ x in l', x ∈ s → p x) ↔ ∀ᶠ x in l ⊓ l', p x :=
  calc
    _ ↔ ∃ s ∈ l, ∀ᶠ x in l', x ∈ s → p x :=
      eventually_small_sets' fun s t hst ht => ht.mono fun x hx hs => hx (hst hs)
    _ ↔ ∃ s ∈ l, ∃ t ∈ l', ∀ x, x ∈ t → x ∈ s → p x := by simp only [eventually_iff_exists_mem]
    _ ↔ ∀ᶠ x in l ⊓ l', p x := by simp only [eventually_inf, and_comm', mem_inter_iff, ← and_imp]
    
#align filter.eventually_small_sets_eventually Filter.eventually_smallSets_eventually

@[simp]
theorem eventually_smallSets_forall {p : α → Prop} :
    (∀ᶠ s in l.smallSets, ∀ x ∈ s, p x) ↔ ∀ᶠ x in l, p x := by
  simpa only [inf_top_eq, eventually_top] using @eventually_small_sets_eventually α l ⊤ p
#align filter.eventually_small_sets_forall Filter.eventually_smallSets_forall

alias eventually_small_sets_forall ↔ eventually.of_small_sets eventually.small_sets
#align filter.eventually.of_small_sets Filter.Eventually.of_smallSets
#align filter.eventually.small_sets Filter.Eventually.smallSets

@[simp]
theorem eventually_smallSets_subset {s : Set α} : (∀ᶠ t in l.smallSets, t ⊆ s) ↔ s ∈ l :=
  eventually_small_sets_forall
#align filter.eventually_small_sets_subset Filter.eventually_smallSets_subset

end Filter

