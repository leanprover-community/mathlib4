/-
Copyright (c) 2022 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Floris van Doorn, Yury Kudryashov
-/
import Mathlib.Order.Filter.Lift
import Mathlib.Order.Filter.AtTopBot

#align_import order.filter.small_sets from "leanprover-community/mathlib"@"8631e2d5ea77f6c13054d9151d82b83069680cb1"

/-!
# The filter of small sets

This file defines the filter of small sets w.r.t. a filter `f`, which is the largest filter
containing all powersets of members of `f`.

`g` converges to `f.smallSets` if for all `s ∈ f`, eventually we have `g x ⊆ s`.

An example usage is that if `f : ι → E → ℝ` is a family of nonnegative functions with integral 1,
then saying that `fun i ↦ support (f i)` tendsto `(𝓝 0).smallSets` is a way of saying that
`f` tends to the Dirac delta distribution.
-/


open Filter

open Filter Set

variable {α β : Type*} {ι : Sort*}

namespace Filter

variable {l l' la : Filter α} {lb : Filter β}

/-- The filter `l.smallSets` is the largest filter containing all powersets of members of `l`. -/
def smallSets (l : Filter α) : Filter (Set α) :=
  l.lift' powerset
#align filter.small_sets Filter.smallSets

theorem smallSets_eq_generate {f : Filter α} : f.smallSets = generate (powerset '' f.sets) := by
  simp_rw [generate_eq_biInf, smallSets, iInf_image]
  rfl
#align filter.small_sets_eq_generate Filter.smallSets_eq_generate

-- TODO: get more properties from the adjunction?
-- TODO: is there a general way to get a lower adjoint for the lift of an upper adjoint?
theorem bind_smallSets_gc :
    GaloisConnection (fun L : Filter (Set α) ↦ L.bind principal) smallSets := by
  intro L l
  simp_rw [smallSets_eq_generate, le_generate_iff, image_subset_iff]
  rfl

protected theorem HasBasis.smallSets {p : ι → Prop} {s : ι → Set α} (h : HasBasis l p s) :
    HasBasis l.smallSets p fun i => 𝒫 s i :=
  h.lift' monotone_powerset
#align filter.has_basis.small_sets Filter.HasBasis.smallSets

theorem hasBasis_smallSets (l : Filter α) :
    HasBasis l.smallSets (fun t : Set α => t ∈ l) powerset :=
  l.basis_sets.smallSets
#align filter.has_basis_small_sets Filter.hasBasis_smallSets

/-- `g` converges to `f.smallSets` if for all `s ∈ f`, eventually we have `g x ⊆ s`. -/
theorem tendsto_smallSets_iff {f : α → Set β} :
    Tendsto f la lb.smallSets ↔ ∀ t ∈ lb, ∀ᶠ x in la, f x ⊆ t :=
  (hasBasis_smallSets lb).tendsto_right_iff
#align filter.tendsto_small_sets_iff Filter.tendsto_smallSets_iff

theorem eventually_smallSets {p : Set α → Prop} :
    (∀ᶠ s in l.smallSets, p s) ↔ ∃ s ∈ l, ∀ t, t ⊆ s → p t :=
  eventually_lift'_iff monotone_powerset
#align filter.eventually_small_sets Filter.eventually_smallSets

theorem eventually_smallSets' {p : Set α → Prop} (hp : ∀ ⦃s t⦄, s ⊆ t → p t → p s) :
    (∀ᶠ s in l.smallSets, p s) ↔ ∃ s ∈ l, p s :=
  eventually_smallSets.trans <|
    exists_congr fun s => Iff.rfl.and ⟨fun H => H s Subset.rfl, fun hs _t ht => hp ht hs⟩
#align filter.eventually_small_sets' Filter.eventually_smallSets'

theorem frequently_smallSets {p : Set α → Prop} :
    (∃ᶠ s in l.smallSets, p s) ↔ ∀ t ∈ l, ∃ s, s ⊆ t ∧ p s :=
  l.hasBasis_smallSets.frequently_iff
#align filter.frequently_small_sets Filter.frequently_smallSets

theorem frequently_smallSets_mem (l : Filter α) : ∃ᶠ s in l.smallSets, s ∈ l :=
  frequently_smallSets.2 fun t ht => ⟨t, Subset.rfl, ht⟩
#align filter.frequently_small_sets_mem Filter.frequently_smallSets_mem

@[simp]
lemma tendsto_image_smallSets {f : α → β} :
    Tendsto (f '' ·) la.smallSets lb.smallSets ↔ Tendsto f la lb := by
  rw [tendsto_smallSets_iff]
  refine forall₂_congr fun u hu ↦ ?_
  rw [eventually_smallSets' fun s t hst ht ↦ (image_subset _ hst).trans ht]
  simp only [image_subset_iff, exists_mem_subset_iff, mem_map]

alias ⟨_, Tendsto.image_smallSets⟩ := tendsto_image_smallSets

theorem HasAntitoneBasis.tendsto_smallSets {ι} [Preorder ι] {s : ι → Set α}
    (hl : l.HasAntitoneBasis s) : Tendsto s atTop l.smallSets :=
  tendsto_smallSets_iff.2 fun _t ht => hl.eventually_subset ht
#align filter.has_antitone_basis.tendsto_small_sets Filter.HasAntitoneBasis.tendsto_smallSets

@[mono]
theorem monotone_smallSets : Monotone (@smallSets α) :=
  monotone_lift' monotone_id monotone_const
#align filter.monotone_small_sets Filter.monotone_smallSets

@[simp]
theorem smallSets_bot : (⊥ : Filter α).smallSets = pure ∅ := by
  rw [smallSets, lift'_bot, powerset_empty, principal_singleton]
  exact monotone_powerset
#align filter.small_sets_bot Filter.smallSets_bot

@[simp]
theorem smallSets_top : (⊤ : Filter α).smallSets = ⊤ := by
  rw [smallSets, lift'_top, powerset_univ, principal_univ]
#align filter.small_sets_top Filter.smallSets_top

@[simp]
theorem smallSets_principal (s : Set α) : (𝓟 s).smallSets = 𝓟 (𝒫 s) :=
  lift'_principal monotone_powerset
#align filter.small_sets_principal Filter.smallSets_principal

theorem smallSets_comap_eq_comap_image (l : Filter β) (f : α → β) :
    (comap f l).smallSets = comap (image f) l.smallSets := by
  refine (gc_map_comap _).u_comm_of_l_comm (gc_map_comap _) bind_smallSets_gc bind_smallSets_gc ?_
  simp [Function.comp, map_bind, bind_map]

theorem smallSets_comap (l : Filter β) (f : α → β) :
    (comap f l).smallSets = l.lift' (powerset ∘ preimage f) :=
  comap_lift'_eq2 monotone_powerset
#align filter.small_sets_comap Filter.smallSets_comap

theorem comap_smallSets (l : Filter β) (f : α → Set β) :
    comap f l.smallSets = l.lift' (preimage f ∘ powerset) :=
  comap_lift'_eq
#align filter.comap_small_sets Filter.comap_smallSets

theorem smallSets_iInf {f : ι → Filter α} : (iInf f).smallSets = ⨅ i, (f i).smallSets :=
  lift'_iInf_of_map_univ (powerset_inter _ _) powerset_univ
#align filter.small_sets_infi Filter.smallSets_iInf

theorem smallSets_inf (l₁ l₂ : Filter α) : (l₁ ⊓ l₂).smallSets = l₁.smallSets ⊓ l₂.smallSets :=
  lift'_inf _ _ powerset_inter
#align filter.small_sets_inf Filter.smallSets_inf

instance smallSets_neBot (l : Filter α) : NeBot l.smallSets := by
  refine (lift'_neBot_iff ?_).2 fun _ _ => powerset_nonempty
  exact monotone_powerset
#align filter.small_sets_ne_bot Filter.smallSets_neBot

theorem Tendsto.smallSets_mono {s t : α → Set β} (ht : Tendsto t la lb.smallSets)
    (hst : ∀ᶠ x in la, s x ⊆ t x) : Tendsto s la lb.smallSets := by
  rw [tendsto_smallSets_iff] at ht ⊢
  exact fun u hu => (ht u hu).mp (hst.mono fun _ hst ht => hst.trans ht)
#align filter.tendsto.small_sets_mono Filter.Tendsto.smallSets_mono

/-- Generalized **squeeze theorem** (also known as **sandwich theorem**). If `s : α → Set β` is a
family of sets that tends to `Filter.smallSets lb` along `la` and `f : α → β` is a function such
that `f x ∈ s x` eventually along `la`, then `f` tends to `lb` along `la`.

If `s x` is the closed interval `[g x, h x]` for some functions `g`, `h` that tend to the same limit
`𝓝 y`, then we obtain the standard squeeze theorem, see
`tendsto_of_tendsto_of_tendsto_of_le_of_le'`. -/
theorem Tendsto.of_smallSets {s : α → Set β} {f : α → β} (hs : Tendsto s la lb.smallSets)
    (hf : ∀ᶠ x in la, f x ∈ s x) : Tendsto f la lb := fun t ht =>
  hf.mp <| (tendsto_smallSets_iff.mp hs t ht).mono fun _ h₁ h₂ => h₁ h₂
#align filter.tendsto.of_small_sets Filter.Tendsto.of_smallSets

@[simp]
theorem eventually_smallSets_eventually {p : α → Prop} :
    (∀ᶠ s in l.smallSets, ∀ᶠ x in l', x ∈ s → p x) ↔ ∀ᶠ x in l ⊓ l', p x :=
  calc
    _ ↔ ∃ s ∈ l, ∀ᶠ x in l', x ∈ s → p x :=
      eventually_smallSets' fun s t hst ht => ht.mono fun x hx hs => hx (hst hs)
    _ ↔ ∃ s ∈ l, ∃ t ∈ l', ∀ x, x ∈ t → x ∈ s → p x := by simp only [eventually_iff_exists_mem]
    _ ↔ ∀ᶠ x in l ⊓ l', p x := by simp only [eventually_inf, and_comm, mem_inter_iff, ← and_imp]
#align filter.eventually_small_sets_eventually Filter.eventually_smallSets_eventually

@[simp]
theorem eventually_smallSets_forall {p : α → Prop} :
    (∀ᶠ s in l.smallSets, ∀ x ∈ s, p x) ↔ ∀ᶠ x in l, p x := by
  simpa only [inf_top_eq, eventually_top] using @eventually_smallSets_eventually α l ⊤ p
#align filter.eventually_small_sets_forall Filter.eventually_smallSets_forall

alias ⟨Eventually.of_smallSets, Eventually.smallSets⟩ := eventually_smallSets_forall
#align filter.eventually.of_small_sets Filter.Eventually.of_smallSets
#align filter.eventually.small_sets Filter.Eventually.smallSets

@[simp]
theorem eventually_smallSets_subset {s : Set α} : (∀ᶠ t in l.smallSets, t ⊆ s) ↔ s ∈ l :=
  eventually_smallSets_forall
#align filter.eventually_small_sets_subset Filter.eventually_smallSets_subset

end Filter
