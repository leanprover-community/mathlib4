/-
Copyright (c) 2022 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Floris van Doorn, Yury Kudryashov
-/
import Mathlib.Order.Filter.Lift
import Mathlib.Order.Filter.AtTopBot.Basic

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

open Set

variable {α β : Type*} {ι : Sort*}

namespace Filter

variable {l l' la : Filter α} {lb : Filter β}

/-- The filter `l.smallSets` is the largest filter containing all powersets of members of `l`. -/
def smallSets (l : Filter α) : Filter (Set α) :=
  l.lift' powerset

theorem smallSets_eq_generate {f : Filter α} : f.smallSets = generate (powerset '' f.sets) := by
  simp_rw [generate_eq_biInf, smallSets, iInf_image, Filter.lift', Filter.lift, Function.comp_apply,
    Filter.mem_sets]

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

theorem hasBasis_smallSets (l : Filter α) :
    HasBasis l.smallSets (fun t : Set α => t ∈ l) powerset :=
  l.basis_sets.smallSets

theorem Eventually.exists_mem_basis_of_smallSets {p : ι → Prop} {s : ι → Set α} {P : Set α → Prop}
    (h₁ : ∀ᶠ t in l.smallSets, P t) (h₂ : HasBasis l p s) : ∃ i, p i ∧ P (s i) :=
  (h₂.smallSets.eventually_iff.mp h₁).imp fun _i ⟨hpi, hi⟩ ↦ ⟨hpi, hi Subset.rfl⟩

theorem Frequently.smallSets_of_forall_mem_basis {p : ι → Prop} {s : ι → Set α} {P : Set α → Prop}
    (h₁ : ∀ i, p i → P (s i)) (h₂ : HasBasis l p s) : ∃ᶠ t in l.smallSets, P t :=
  h₂.smallSets.frequently_iff.mpr fun _ hi => ⟨_, Subset.rfl, h₁ _ hi⟩

theorem Eventually.exists_mem_of_smallSets {p : Set α → Prop}
    (h : ∀ᶠ t in l.smallSets, p t) : ∃ s ∈ l, p s :=
  h.exists_mem_basis_of_smallSets l.basis_sets

/-! No `Frequently.smallSets_of_forall_mem (h : ∀ s ∈ l, p s) : ∃ᶠ t in l.smallSets, p t` as
`Filter.frequently_smallSets_mem : ∃ᶠ t in l.smallSets, t ∈ l` is preferred. -/

/-- `g` converges to `f.smallSets` if for all `s ∈ f`, eventually we have `g x ⊆ s`. -/
theorem tendsto_smallSets_iff {f : α → Set β} :
    Tendsto f la lb.smallSets ↔ ∀ t ∈ lb, ∀ᶠ x in la, f x ⊆ t :=
  (hasBasis_smallSets lb).tendsto_right_iff

theorem eventually_smallSets {p : Set α → Prop} :
    (∀ᶠ s in l.smallSets, p s) ↔ ∃ s ∈ l, ∀ t, t ⊆ s → p t :=
  eventually_lift'_iff monotone_powerset

theorem eventually_smallSets' {p : Set α → Prop} (hp : ∀ ⦃s t⦄, s ⊆ t → p t → p s) :
    (∀ᶠ s in l.smallSets, p s) ↔ ∃ s ∈ l, p s :=
  eventually_smallSets.trans <|
    exists_congr fun s => Iff.rfl.and ⟨fun H => H s Subset.rfl, fun hs _t ht => hp ht hs⟩

theorem frequently_smallSets {p : Set α → Prop} :
    (∃ᶠ s in l.smallSets, p s) ↔ ∀ t ∈ l, ∃ s, s ⊆ t ∧ p s :=
  l.hasBasis_smallSets.frequently_iff

theorem frequently_smallSets_mem (l : Filter α) : ∃ᶠ s in l.smallSets, s ∈ l :=
  frequently_smallSets.2 fun t ht => ⟨t, Subset.rfl, ht⟩

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

@[mono]
theorem monotone_smallSets : Monotone (@smallSets α) :=
  monotone_lift' monotone_id monotone_const

@[simp]
theorem smallSets_bot : (⊥ : Filter α).smallSets = pure ∅ := by
  rw [smallSets, lift'_bot, powerset_empty, principal_singleton]
  exact monotone_powerset

@[simp]
theorem smallSets_top : (⊤ : Filter α).smallSets = ⊤ := by
  rw [smallSets, lift'_top, powerset_univ, principal_univ]

@[simp]
theorem smallSets_principal (s : Set α) : (𝓟 s).smallSets = 𝓟 (𝒫 s) :=
  lift'_principal monotone_powerset

theorem smallSets_comap_eq_comap_image (l : Filter β) (f : α → β) :
    (comap f l).smallSets = comap (image f) l.smallSets := by
  refine (gc_map_comap _).u_comm_of_l_comm (gc_map_comap _) bind_smallSets_gc bind_smallSets_gc ?_
  simp [Function.comp_def, map_bind, bind_map]

theorem smallSets_comap (l : Filter β) (f : α → β) :
    (comap f l).smallSets = l.lift' (powerset ∘ preimage f) :=
  comap_lift'_eq2 monotone_powerset

theorem comap_smallSets (l : Filter β) (f : α → Set β) :
    comap f l.smallSets = l.lift' (preimage f ∘ powerset) :=
  comap_lift'_eq

theorem smallSets_iInf {f : ι → Filter α} : (iInf f).smallSets = ⨅ i, (f i).smallSets :=
  lift'_iInf_of_map_univ (powerset_inter _ _) powerset_univ

theorem smallSets_inf (l₁ l₂ : Filter α) : (l₁ ⊓ l₂).smallSets = l₁.smallSets ⊓ l₂.smallSets :=
  lift'_inf _ _ powerset_inter

instance smallSets_neBot (l : Filter α) : NeBot l.smallSets := by
  refine (lift'_neBot_iff ?_).2 fun _ _ => powerset_nonempty
  exact monotone_powerset

theorem Tendsto.smallSets_mono {s t : α → Set β} (ht : Tendsto t la lb.smallSets)
    (hst : ∀ᶠ x in la, s x ⊆ t x) : Tendsto s la lb.smallSets := by
  rw [tendsto_smallSets_iff] at ht ⊢
  exact fun u hu => (ht u hu).mp (hst.mono fun _ hst ht => hst.trans ht)

/-- Generalized **squeeze theorem** (also known as **sandwich theorem**). If `s : α → Set β` is a
family of sets that tends to `Filter.smallSets lb` along `la` and `f : α → β` is a function such
that `f x ∈ s x` eventually along `la`, then `f` tends to `lb` along `la`.

If `s x` is the closed interval `[g x, h x]` for some functions `g`, `h` that tend to the same limit
`𝓝 y`, then we obtain the standard squeeze theorem, see
`tendsto_of_tendsto_of_tendsto_of_le_of_le'`. -/
theorem Tendsto.of_smallSets {s : α → Set β} {f : α → β} (hs : Tendsto s la lb.smallSets)
    (hf : ∀ᶠ x in la, f x ∈ s x) : Tendsto f la lb := fun t ht =>
  hf.mp <| (tendsto_smallSets_iff.mp hs t ht).mono fun _ h₁ h₂ => h₁ h₂

@[simp]
theorem eventually_smallSets_eventually {p : α → Prop} :
    (∀ᶠ s in l.smallSets, ∀ᶠ x in l', x ∈ s → p x) ↔ ∀ᶠ x in l ⊓ l', p x :=
  calc
    _ ↔ ∃ s ∈ l, ∀ᶠ x in l', x ∈ s → p x :=
      eventually_smallSets' fun _ _ hst ht => ht.mono fun _ hx hs => hx (hst hs)
    _ ↔ ∃ s ∈ l, ∃ t ∈ l', ∀ x, x ∈ t → x ∈ s → p x := by simp only [eventually_iff_exists_mem]
    _ ↔ ∀ᶠ x in l ⊓ l', p x := by simp only [eventually_inf, and_comm, mem_inter_iff, ← and_imp]

@[simp]
theorem eventually_smallSets_forall {p : α → Prop} :
    (∀ᶠ s in l.smallSets, ∀ x ∈ s, p x) ↔ ∀ᶠ x in l, p x := by
  simpa only [inf_top_eq, eventually_top] using @eventually_smallSets_eventually α l ⊤ p

alias ⟨Eventually.of_smallSets, Eventually.smallSets⟩ := eventually_smallSets_forall

@[simp]
theorem eventually_smallSets_subset {s : Set α} : (∀ᶠ t in l.smallSets, t ⊆ s) ↔ s ∈ l :=
  eventually_smallSets_forall

end Filter
