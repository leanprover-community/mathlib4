/-
Copyright (c) 2020 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo
-/
import Mathlib.Dynamics.Flow
import Mathlib.Tactic.Monotonicity

/-!
# ω-limits

For a function `ϕ : τ → α → β` where `β` is a topological space, we
define the ω-limit under `ϕ` of a set `s` in `α` with respect to
filter `f` on `τ`: an element `y : β` is in the ω-limit of `s` if the
forward images of `s` intersect arbitrarily small neighbourhoods of
`y` frequently "in the direction of `f`".

In practice `ϕ` is often a continuous monoid-act, but the definition
requires only that `ϕ` has a coercion to the appropriate function
type. In the case where `τ` is `ℕ` or `ℝ` and `f` is `atTop`, we
recover the usual definition of the ω-limit set as the set of all `y`
such that there exist sequences `(tₙ)`, `(xₙ)` such that `ϕ tₙ xₙ ⟶ y`
as `n ⟶ ∞`.

## Notation

The `omegaLimit` scope provides the localised notation `ω` for
`omegaLimit`, as well as `ω⁺` and `ω⁻` for `omegaLimit atTop` and
`omegaLimit atBot` respectively for when the acting monoid is
endowed with an order.
-/


open Set Function Filter Topology

/-!
### Definition and notation
-/
section omegaLimit

variable {τ : Type*} {α : Type*} {β : Type*} {ι : Type*}

/-- The ω-limit of a set `s` under `ϕ` with respect to a filter `f` is `⋂ u ∈ f, cl (ϕ u s)`. -/
def omegaLimit [TopologicalSpace β] (f : Filter τ) (ϕ : τ → α → β) (s : Set α) : Set β :=
  ⋂ u ∈ f, closure (image2 ϕ u s)

@[inherit_doc]
scoped[omegaLimit] notation "ω" => omegaLimit

/-- The ω-limit w.r.t. `Filter.atTop`. -/
scoped[omegaLimit] notation "ω⁺" => omegaLimit Filter.atTop

/-- The ω-limit w.r.t. `Filter.atBot`. -/
scoped[omegaLimit] notation "ω⁻" => omegaLimit Filter.atBot

variable [TopologicalSpace β]
variable (f : Filter τ) (ϕ : τ → α → β) (s s₁ s₂ : Set α)

/-!
### Elementary properties
-/
open omegaLimit

theorem omegaLimit_def : ω f ϕ s = ⋂ u ∈ f, closure (image2 ϕ u s) := rfl

theorem omegaLimit_subset_of_tendsto {m : τ → τ} {f₁ f₂ : Filter τ} (hf : Tendsto m f₁ f₂) :
    ω f₁ (fun t x ↦ ϕ (m t) x) s ⊆ ω f₂ ϕ s := by
  refine iInter₂_mono' fun u hu ↦ ⟨m ⁻¹' u, tendsto_def.mp hf _ hu, ?_⟩
  rw [← image2_image_left]
  exact closure_mono (image2_subset (image_preimage_subset _ _) Subset.rfl)

theorem omegaLimit_mono_left {f₁ f₂ : Filter τ} (hf : f₁ ≤ f₂) : ω f₁ ϕ s ⊆ ω f₂ ϕ s :=
  omegaLimit_subset_of_tendsto ϕ s (tendsto_id'.2 hf)

theorem omegaLimit_mono_right {s₁ s₂ : Set α} (hs : s₁ ⊆ s₂) : ω f ϕ s₁ ⊆ ω f ϕ s₂ :=
  iInter₂_mono fun _u _hu ↦ closure_mono (image2_subset Subset.rfl hs)

theorem isClosed_omegaLimit : IsClosed (ω f ϕ s) :=
  isClosed_iInter fun _u ↦ isClosed_iInter fun _hu ↦ isClosed_closure

theorem mapsTo_omegaLimit' {α' β' : Type*} [TopologicalSpace β'] {f : Filter τ} {ϕ : τ → α → β}
    {ϕ' : τ → α' → β'} {ga : α → α'} {s' : Set α'} (hs : MapsTo ga s s') {gb : β → β'}
    (hg : ∀ᶠ t in f, EqOn (gb ∘ ϕ t) (ϕ' t ∘ ga) s) (hgc : Continuous gb) :
    MapsTo gb (ω f ϕ s) (ω f ϕ' s') := by
  simp only [omegaLimit_def, mem_iInter, MapsTo]
  intro y hy u hu
  refine map_mem_closure hgc (hy _ (inter_mem hu hg)) (forall_mem_image2.2 fun t ht x hx ↦ ?_)
  calc
    ϕ' t (ga x) ∈ image2 ϕ' u s' := mem_image2_of_mem ht.1 (hs hx)
    _ = gb (ϕ t x) := ht.2 hx |>.symm

theorem mapsTo_omegaLimit {α' β' : Type*} [TopologicalSpace β'] {f : Filter τ} {ϕ : τ → α → β}
    {ϕ' : τ → α' → β'} {ga : α → α'} {s' : Set α'} (hs : MapsTo ga s s') {gb : β → β'}
    (hg : ∀ t x, gb (ϕ t x) = ϕ' t (ga x)) (hgc : Continuous gb) :
    MapsTo gb (ω f ϕ s) (ω f ϕ' s') :=
  mapsTo_omegaLimit' _ hs (Eventually.of_forall fun t x _hx ↦ hg t x) hgc

theorem omegaLimit_image_eq {α' : Type*} (ϕ : τ → α' → β) (f : Filter τ) (g : α → α') :
    ω f ϕ (g '' s) = ω f (fun t x ↦ ϕ t (g x)) s := by simp only [omegaLimit, image2_image_right]

theorem omegaLimit_preimage_subset {α' : Type*} (ϕ : τ → α' → β) (s : Set α') (f : Filter τ)
    (g : α → α') : ω f (fun t x ↦ ϕ t (g x)) (g ⁻¹' s) ⊆ ω f ϕ s :=
  mapsTo_omegaLimit _ (mapsTo_preimage _ _) (fun _t _x ↦ rfl) continuous_id

/-!
### Equivalent definitions of the omega limit

The next few lemmas are various versions of the property
characterising ω-limits:
-/

/-- An element `y` is in the ω-limit set of `s` w.r.t. `f` if the
preimages of an arbitrary neighbourhood of `y` frequently (w.r.t. `f`) intersects of `s`. -/
theorem mem_omegaLimit_iff_frequently (y : β) :
    y ∈ ω f ϕ s ↔ ∀ n ∈ 𝓝 y, ∃ᶠ t in f, (s ∩ ϕ t ⁻¹' n).Nonempty := by
  simp_rw [frequently_iff, omegaLimit_def, mem_iInter, mem_closure_iff_nhds]
  constructor
  · intro h _ hn _ hu
    rcases h _ hu _ hn with ⟨_, _, _, ht, _, hx, rfl⟩
    exact ⟨_, ht, _, hx, by rwa [mem_preimage]⟩
  · intro h _ hu _ hn
    rcases h _ hn hu with ⟨_, ht, _, hx, hϕtx⟩
    exact ⟨_, hϕtx, _, ht, _, hx, rfl⟩

/-- An element `y` is in the ω-limit set of `s` w.r.t. `f` if the forward images of `s`
frequently (w.r.t. `f`) intersect arbitrary neighbourhoods of `y`. -/
theorem mem_omegaLimit_iff_frequently₂ (y : β) :
    y ∈ ω f ϕ s ↔ ∀ n ∈ 𝓝 y, ∃ᶠ t in f, (ϕ t '' s ∩ n).Nonempty := by
  simp_rw [mem_omegaLimit_iff_frequently, image_inter_nonempty_iff]

/-- An element `y` is in the ω-limit of `x` w.r.t. `f` if the forward
images of `x` frequently (w.r.t. `f`) falls within an arbitrary neighbourhood of `y`. -/
theorem mem_omegaLimit_singleton_iff_map_cluster_point (x : α) (y : β) :
    y ∈ ω f ϕ {x} ↔ MapClusterPt y f fun t ↦ ϕ t x := by
  simp_rw [mem_omegaLimit_iff_frequently, mapClusterPt_iff_frequently, singleton_inter_nonempty,
    mem_preimage]

/-!
### Set operations and omega limits
-/

theorem omegaLimit_inter : ω f ϕ (s₁ ∩ s₂) ⊆ ω f ϕ s₁ ∩ ω f ϕ s₂ :=
  subset_inter (omegaLimit_mono_right _ _ inter_subset_left)
    (omegaLimit_mono_right _ _ inter_subset_right)

theorem omegaLimit_iInter (p : ι → Set α) : ω f ϕ (⋂ i, p i) ⊆ ⋂ i, ω f ϕ (p i) :=
  subset_iInter fun _i ↦ omegaLimit_mono_right _ _ (iInter_subset _ _)

theorem omegaLimit_union : ω f ϕ (s₁ ∪ s₂) = ω f ϕ s₁ ∪ ω f ϕ s₂ := by
  ext y; constructor
  · simp only [mem_union, mem_omegaLimit_iff_frequently, union_inter_distrib_right, union_nonempty,
      frequently_or_distrib]
    contrapose!
    simp only [not_frequently, not_nonempty_iff_eq_empty, ← subset_empty_iff]
    rintro ⟨⟨n₁, hn₁, h₁⟩, ⟨n₂, hn₂, h₂⟩⟩
    refine ⟨n₁ ∩ n₂, inter_mem hn₁ hn₂, h₁.mono fun t ↦ ?_, h₂.mono fun t ↦ ?_⟩
    exacts [Subset.trans <| inter_subset_inter_right _ <| preimage_mono inter_subset_left,
      Subset.trans <| inter_subset_inter_right _ <| preimage_mono inter_subset_right]
  · rintro (hy | hy)
    exacts [omegaLimit_mono_right _ _ subset_union_left hy,
      omegaLimit_mono_right _ _ subset_union_right hy]

theorem omegaLimit_iUnion (p : ι → Set α) : ⋃ i, ω f ϕ (p i) ⊆ ω f ϕ (⋃ i, p i) := by
  rw [iUnion_subset_iff]
  exact fun i ↦ omegaLimit_mono_right _ _ (subset_iUnion _ _)

/-!
Different expressions for omega limits, useful for rewrites. In
particular, one may restrict the intersection to sets in `f` which are
subsets of some set `v` also in `f`.
-/

theorem omegaLimit_eq_iInter : ω f ϕ s = ⋂ u : ↥f.sets, closure (image2 ϕ u s) :=
  biInter_eq_iInter _ _

theorem omegaLimit_eq_biInter_inter {v : Set τ} (hv : v ∈ f) :
    ω f ϕ s = ⋂ u ∈ f, closure (image2 ϕ (u ∩ v) s) :=
  Subset.antisymm (iInter₂_mono' fun u hu ↦ ⟨u ∩ v, inter_mem hu hv, Subset.rfl⟩)
    (iInter₂_mono fun _u _hu ↦ closure_mono <| image2_subset inter_subset_left Subset.rfl)

theorem omegaLimit_eq_iInter_inter {v : Set τ} (hv : v ∈ f) :
    ω f ϕ s = ⋂ u : ↥f.sets, closure (image2 ϕ (u ∩ v) s) := by
  rw [omegaLimit_eq_biInter_inter _ _ _ hv]
  apply biInter_eq_iInter

theorem omegaLimit_subset_closure_fw_image {u : Set τ} (hu : u ∈ f) :
    ω f ϕ s ⊆ closure (image2 ϕ u s) := by
  rw [omegaLimit_eq_iInter]
  intro _ hx
  rw [mem_iInter] at hx
  exact hx ⟨u, hu⟩

-- An instance with better keys
instance : Inhabited f.sets := Filter.inhabitedMem

/-!
### ω-limits and compactness
-/

/-- A set is eventually carried into any open neighbourhood of its ω-limit:
if `c` is a compact set such that `closure {ϕ t x | t ∈ v, x ∈ s} ⊆ c` for some `v ∈ f`
and `n` is an open neighbourhood of `ω f ϕ s`, then for some `u ∈ f` we have
`closure {ϕ t x | t ∈ u, x ∈ s} ⊆ n`. -/
theorem eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset' {c : Set β}
    (hc₁ : IsCompact c) (hc₂ : ∃ v ∈ f, closure (image2 ϕ v s) ⊆ c) {n : Set β} (hn₁ : IsOpen n)
    (hn₂ : ω f ϕ s ⊆ n) : ∃ u ∈ f, closure (image2 ϕ u s) ⊆ n := by
  rcases hc₂ with ⟨v, hv₁, hv₂⟩
  let k := closure (image2 ϕ v s)
  have hk : IsCompact (k \ n) :=
    (hc₁.of_isClosed_subset isClosed_closure hv₂).diff hn₁
  let j u := (closure (image2 ϕ (u ∩ v) s))ᶜ
  have hj₁ : ∀ u ∈ f, IsOpen (j u) := fun _ _ ↦ isOpen_compl_iff.mpr isClosed_closure
  have hj₂ : k \ n ⊆ ⋃ u ∈ f, j u := by
    have : ⋃ u ∈ f, j u = ⋃ u : (↥f.sets), j u := biUnion_eq_iUnion _ _
    rw [this, diff_subset_comm, diff_iUnion]
    rw [omegaLimit_eq_iInter_inter _ _ _ hv₁] at hn₂
    simp_rw [j, diff_compl]
    rw [← inter_iInter]
    exact Subset.trans inter_subset_right hn₂
  rcases hk.elim_finite_subcover_image hj₁ hj₂ with ⟨g, hg₁ : ∀ u ∈ g, u ∈ f, hg₂, hg₃⟩
  let w := (⋂ u ∈ g, u) ∩ v
  have hw₂ : w ∈ f := by simpa [w, *]
  have hw₃ : k \ n ⊆ (closure (image2 ϕ w s))ᶜ := by
    apply Subset.trans hg₃
    simp only [j, iUnion_subset_iff, compl_subset_compl]
    intro u hu
    unfold w
    gcongr
    refine iInter_subset_of_subset u (iInter_subset_of_subset hu ?_)
    all_goals exact Subset.rfl
  have hw₄ : kᶜ ⊆ (closure (image2 ϕ w s))ᶜ := by
    simp only [compl_subset_compl]
    exact closure_mono (image2_subset inter_subset_right Subset.rfl)
  have hnc : nᶜ ⊆ k \ n ∪ kᶜ := by rw [union_comm, ← inter_subset, diff_eq, inter_comm]
  have hw : closure (image2 ϕ w s) ⊆ n :=
    compl_subset_compl.mp (Subset.trans hnc (union_subset hw₃ hw₄))
  exact ⟨_, hw₂, hw⟩

/-- A set is eventually carried into any open neighbourhood of its ω-limit:
if `c` is a compact set such that `closure {ϕ t x | t ∈ v, x ∈ s} ⊆ c` for some `v ∈ f`
and `n` is an open neighbourhood of `ω f ϕ s`, then for some `u ∈ f` we have
`closure {ϕ t x | t ∈ u, x ∈ s} ⊆ n`. -/
theorem eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset [T2Space β]
    {c : Set β} (hc₁ : IsCompact c) (hc₂ : ∀ᶠ t in f, MapsTo (ϕ t) s c) {n : Set β} (hn₁ : IsOpen n)
    (hn₂ : ω f ϕ s ⊆ n) : ∃ u ∈ f, closure (image2 ϕ u s) ⊆ n :=
  eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset' f ϕ _ hc₁
    ⟨_, hc₂, closure_minimal (image2_subset_iff.2 fun _t ↦ id) hc₁.isClosed⟩ hn₁ hn₂

theorem eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset [T2Space β]
    {c : Set β} (hc₁ : IsCompact c) (hc₂ : ∀ᶠ t in f, MapsTo (ϕ t) s c) {n : Set β} (hn₁ : IsOpen n)
    (hn₂ : ω f ϕ s ⊆ n) : ∀ᶠ t in f, MapsTo (ϕ t) s n := by
  rcases eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset f ϕ s hc₁
      hc₂ hn₁ hn₂ with
    ⟨u, hu_mem, hu⟩
  refine mem_of_superset hu_mem fun t ht x hx ↦ ?_
  exact hu (subset_closure <| mem_image2_of_mem ht hx)

theorem eventually_closure_subset_of_isOpen_of_omegaLimit_subset [CompactSpace β] {v : Set β}
    (hv₁ : IsOpen v) (hv₂ : ω f ϕ s ⊆ v) : ∃ u ∈ f, closure (image2 ϕ u s) ⊆ v :=
  eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset' _ _ _
    isCompact_univ ⟨univ, univ_mem, subset_univ _⟩ hv₁ hv₂

theorem eventually_mapsTo_of_isOpen_of_omegaLimit_subset [CompactSpace β] {v : Set β}
    (hv₁ : IsOpen v) (hv₂ : ω f ϕ s ⊆ v) : ∀ᶠ t in f, MapsTo (ϕ t) s v := by
  rcases eventually_closure_subset_of_isOpen_of_omegaLimit_subset f ϕ s hv₁ hv₂ with ⟨u, hu_mem, hu⟩
  refine mem_of_superset hu_mem fun t ht x hx ↦ ?_
  exact hu (subset_closure <| mem_image2_of_mem ht hx)

/-- The ω-limit of a nonempty set w.r.t. a nontrivial filter is nonempty. -/
theorem nonempty_omegaLimit_of_isCompact_absorbing [NeBot f] {c : Set β} (hc₁ : IsCompact c)
    (hc₂ : ∃ v ∈ f, closure (image2 ϕ v s) ⊆ c) (hs : s.Nonempty) : (ω f ϕ s).Nonempty := by
  rcases hc₂ with ⟨v, hv₁, hv₂⟩
  rw [omegaLimit_eq_iInter_inter _ _ _ hv₁]
  apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
  · rintro ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩
    use ⟨u₁ ∩ u₂, inter_mem hu₁ hu₂⟩
    constructor
    all_goals exact closure_mono (image2_subset (inter_subset_inter_left _ (by simp)) Subset.rfl)
  · intro u
    have hn : (image2 ϕ (u ∩ v) s).Nonempty :=
      Nonempty.image2 (Filter.nonempty_of_mem (inter_mem u.prop hv₁)) hs
    exact hn.mono subset_closure
  · intro
    apply hc₁.of_isClosed_subset isClosed_closure
    calc
      _ ⊆ closure (image2 ϕ v s) := closure_mono (image2_subset inter_subset_right Subset.rfl)
      _ ⊆ c := hv₂
  · exact fun _ ↦ isClosed_closure

theorem nonempty_omegaLimit [CompactSpace β] [NeBot f] (hs : s.Nonempty) : (ω f ϕ s).Nonempty :=
  nonempty_omegaLimit_of_isCompact_absorbing _ _ _ isCompact_univ ⟨univ, univ_mem, subset_univ _⟩ hs

end omegaLimit

/-!
### ω-limits of flows by a monoid
-/
namespace Flow

variable {τ : Type*} [TopologicalSpace τ] [AddMonoid τ] [ContinuousAdd τ] {α : Type*}
  [TopologicalSpace α] (f : Filter τ) (ϕ : Flow τ α) (s : Set α)

open omegaLimit

theorem isInvariant_omegaLimit (hf : ∀ t, Tendsto (t + ·) f f) : IsInvariant ϕ (ω f ϕ s) := by
  refine fun t ↦ MapsTo.mono_right ?_ (omegaLimit_subset_of_tendsto ϕ s (hf t))
  exact
    mapsTo_omegaLimit _ (mapsTo_id _) (fun t' x ↦ (ϕ.map_add _ _ _).symm)
      (continuous_const.flow ϕ continuous_id)

theorem omegaLimit_image_subset (t : τ) (ht : Tendsto (· + t) f f) :
    ω f ϕ (ϕ t '' s) ⊆ ω f ϕ s := by
  simp only [omegaLimit_image_eq, ← map_add]
  exact omegaLimit_subset_of_tendsto ϕ s ht

end Flow

/-!
### ω-limits of flows by a group
-/
namespace Flow

variable {τ : Type*} [TopologicalSpace τ] [AddCommGroup τ] [IsTopologicalAddGroup τ] {α : Type*}
  [TopologicalSpace α] (f : Filter τ) (ϕ : Flow τ α) (s : Set α)

open omegaLimit

/-- the ω-limit of a forward image of `s` is the same as the ω-limit of `s`. -/
@[simp]
theorem omegaLimit_image_eq (hf : ∀ t, Tendsto (· + t) f f) (t : τ) : ω f ϕ (ϕ t '' s) = ω f ϕ s :=
  Subset.antisymm (omegaLimit_image_subset _ _ _ _ (hf t)) <|
    calc
      ω f ϕ s = ω f ϕ (ϕ (-t) '' (ϕ t '' s)) := by simp [image_image, ← map_add]
      _ ⊆ ω f ϕ (ϕ t '' s) := omegaLimit_image_subset _ _ _ _ (hf _)

theorem omegaLimit_omegaLimit (hf : ∀ t, Tendsto (t + ·) f f) : ω f ϕ (ω f ϕ s) ⊆ ω f ϕ s := by
  simp only [subset_def, mem_omegaLimit_iff_frequently₂, frequently_iff]
  intro _ h
  rintro n hn u hu
  rcases mem_nhds_iff.mp hn with ⟨o, ho₁, ho₂, ho₃⟩
  rcases h o (IsOpen.mem_nhds ho₂ ho₃) hu with ⟨t, _ht₁, ht₂⟩
  have l₁ : (ω f ϕ s ∩ o).Nonempty :=
    ht₂.mono
      (inter_subset_inter_left _
        ((isInvariant_iff_image _ _).mp (isInvariant_omegaLimit _ _ _ hf) _))
  have l₂ : (closure (image2 ϕ u s) ∩ o).Nonempty :=
    l₁.mono fun b hb ↦ ⟨omegaLimit_subset_closure_fw_image _ _ _ hu hb.1, hb.2⟩
  have l₃ : (o ∩ image2 ϕ u s).Nonempty := by
    rcases l₂ with ⟨b, hb₁, hb₂⟩
    exact mem_closure_iff_nhds.mp hb₁ o (IsOpen.mem_nhds ho₂ hb₂)
  rcases l₃ with ⟨ϕra, ho, ⟨_, hr, _, ha, hϕra⟩⟩
  exact ⟨_, hr, ϕra, ⟨_, ha, hϕra⟩, ho₁ ho⟩

end Flow
