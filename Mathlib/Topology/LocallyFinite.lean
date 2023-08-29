/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.ContinuousOn
import Mathlib.Order.Filter.SmallSets

#align_import topology.locally_finite from "leanprover-community/mathlib"@"55d771df074d0dd020139ee1cd4b95521422df9f"

/-!
### Locally finite families of sets

We say that a family of sets in a topological space is *locally finite* if at every point `x : X`,
there is a neighborhood of `x` which meets only finitely many sets in the family.

In this file we give the definition and prove basic properties of locally finite families of sets.
-/

-- locally finite family [General Topology (Bourbaki, 1995)]
open Set Function Filter Topology

variable {ι ι' α X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f g : ι → Set X}

/-- A family of sets in `Set X` is locally finite if at every point `x : X`,
there is a neighborhood of `x` which meets only finitely many sets in the family. -/
def LocallyFinite (f : ι → Set X) :=
  ∀ x : X, ∃ t ∈ 𝓝 x, { i | (f i ∩ t).Nonempty }.Finite
#align locally_finite LocallyFinite

theorem locallyFinite_of_finite [Finite ι] (f : ι → Set X) : LocallyFinite f := fun _ =>
  ⟨univ, univ_mem, toFinite _⟩
#align locally_finite_of_finite locallyFinite_of_finite

namespace LocallyFinite

theorem point_finite (hf : LocallyFinite f) (x : X) : { b | x ∈ f b }.Finite :=
  let ⟨_t, hxt, ht⟩ := hf x
  ht.subset fun _b hb => ⟨x, hb, mem_of_mem_nhds hxt⟩
#align locally_finite.point_finite LocallyFinite.point_finite

protected theorem subset (hf : LocallyFinite f) (hg : ∀ i, g i ⊆ f i) : LocallyFinite g := fun a =>
  let ⟨t, ht₁, ht₂⟩ := hf a
  ⟨t, ht₁, ht₂.subset fun i hi => hi.mono <| inter_subset_inter (hg i) Subset.rfl⟩
#align locally_finite.subset LocallyFinite.subset

theorem comp_injOn {g : ι' → ι} (hf : LocallyFinite f) (hg : InjOn g { i | (f (g i)).Nonempty }) :
    LocallyFinite (f ∘ g) := fun x => by
  let ⟨t, htx, htf⟩ := hf x
  -- ⊢ ∃ t, t ∈ 𝓝 x ∧ Set.Finite {i | Set.Nonempty ((f ∘ g) i ∩ t)}
  refine ⟨t, htx, htf.preimage <| ?_⟩
  -- ⊢ InjOn (fun i => g i) ((fun i => g i) ⁻¹' {i | Set.Nonempty (f i ∩ t)})
  exact hg.mono fun i (hi : Set.Nonempty _) => hi.left
  -- 🎉 no goals
#align locally_finite.comp_inj_on LocallyFinite.comp_injOn

theorem comp_injective {g : ι' → ι} (hf : LocallyFinite f) (hg : Injective g) :
    LocallyFinite (f ∘ g) :=
  hf.comp_injOn (hg.injOn _)
#align locally_finite.comp_injective LocallyFinite.comp_injective

theorem _root_.locallyFinite_iff_smallSets :
    LocallyFinite f ↔ ∀ x, ∀ᶠ s in (𝓝 x).smallSets, { i | (f i ∩ s).Nonempty }.Finite :=
  forall_congr' fun _ => Iff.symm <|
    eventually_smallSets' fun _s _t hst ht =>
      ht.subset fun _i hi => hi.mono <| inter_subset_inter_right _ hst
#align locally_finite_iff_small_sets locallyFinite_iff_smallSets

protected theorem eventually_smallSets (hf : LocallyFinite f) (x : X) :
    ∀ᶠ s in (𝓝 x).smallSets, { i | (f i ∩ s).Nonempty }.Finite :=
  locallyFinite_iff_smallSets.mp hf x
#align locally_finite.eventually_small_sets LocallyFinite.eventually_smallSets

theorem exists_mem_basis {ι' : Sort*} (hf : LocallyFinite f) {p : ι' → Prop} {s : ι' → Set X}
    {x : X} (hb : (𝓝 x).HasBasis p s) : ∃ i, p i ∧ { j | (f j ∩ s i).Nonempty }.Finite :=
  let ⟨i, hpi, hi⟩ := hb.smallSets.eventually_iff.mp (hf.eventually_smallSets x)
  ⟨i, hpi, hi Subset.rfl⟩
#align locally_finite.exists_mem_basis LocallyFinite.exists_mem_basis

protected theorem nhdsWithin_iUnion (hf : LocallyFinite f) (a : X) :
    𝓝[⋃ i, f i] a = ⨆ i, 𝓝[f i] a := by
  rcases hf a with ⟨U, haU, hfin⟩
  -- ⊢ 𝓝[⋃ (i : ι), f i] a = ⨆ (i : ι), 𝓝[f i] a
  refine le_antisymm ?_ (Monotone.le_map_iSup fun _ _ ↦ nhdsWithin_mono _)
  -- ⊢ 𝓝[⋃ (i : ι), f i] a ≤ ⨆ (i : ι), 𝓝[f i] a
  calc
    𝓝[⋃ i, f i] a = 𝓝[⋃ i, f i ∩ U] a := by
      rw [← iUnion_inter, ← nhdsWithin_inter_of_mem' (nhdsWithin_le_nhds haU)]
    _ = 𝓝[⋃ i ∈ {j | (f j ∩ U).Nonempty}, (f i ∩ U)] a := by
      simp only [mem_setOf_eq, iUnion_nonempty_self]
    _ = ⨆ i ∈ {j | (f j ∩ U).Nonempty}, 𝓝[f i ∩ U] a := nhdsWithin_biUnion hfin _ _
    _ ≤ ⨆ i, 𝓝[f i ∩ U] a := iSup₂_le_iSup _ _
    _ ≤ ⨆ i, 𝓝[f i] a := iSup_mono fun i ↦ nhdsWithin_mono _ <| inter_subset_left _ _
#align locally_finite.nhds_within_Union LocallyFinite.nhdsWithin_iUnion

theorem continuousOn_iUnion' {g : X → Y} (hf : LocallyFinite f)
    (hc : ∀ i x, x ∈ closure (f i) → ContinuousWithinAt g (f i) x) :
    ContinuousOn g (⋃ i, f i) := by
  rintro x -
  -- ⊢ ContinuousWithinAt g (⋃ (i : ι), f i) x
  rw [ContinuousWithinAt, hf.nhdsWithin_iUnion, tendsto_iSup]
  -- ⊢ ∀ (i : ι), Tendsto g (𝓝[f i] x) (𝓝 (g x))
  intro i
  -- ⊢ Tendsto g (𝓝[f i] x) (𝓝 (g x))
  by_cases hx : x ∈ closure (f i)
  -- ⊢ Tendsto g (𝓝[f i] x) (𝓝 (g x))
  · exact hc i _ hx
    -- 🎉 no goals
  · rw [mem_closure_iff_nhdsWithin_neBot, not_neBot] at hx
    -- ⊢ Tendsto g (𝓝[f i] x) (𝓝 (g x))
    rw [hx]
    -- ⊢ Tendsto g ⊥ (𝓝 (g x))
    exact tendsto_bot
    -- 🎉 no goals
#align locally_finite.continuous_on_Union' LocallyFinite.continuousOn_iUnion'

theorem continuousOn_iUnion {g : X → Y} (hf : LocallyFinite f) (h_cl : ∀ i, IsClosed (f i))
    (h_cont : ∀ i, ContinuousOn g (f i)) : ContinuousOn g (⋃ i, f i) :=
  hf.continuousOn_iUnion' fun i x hx ↦ h_cont i x <| (h_cl i).closure_subset hx
#align locally_finite.continuous_on_Union LocallyFinite.continuousOn_iUnion

protected theorem continuous' {g : X → Y} (hf : LocallyFinite f) (h_cov : ⋃ i, f i = univ)
    (hc : ∀ i x, x ∈ closure (f i) → ContinuousWithinAt g (f i) x) :
    Continuous g :=
  continuous_iff_continuousOn_univ.2 <| h_cov ▸ hf.continuousOn_iUnion' hc
#align locally_finite.continuous' LocallyFinite.continuous'

protected theorem continuous {g : X → Y} (hf : LocallyFinite f) (h_cov : ⋃ i, f i = univ)
    (h_cl : ∀ i, IsClosed (f i)) (h_cont : ∀ i, ContinuousOn g (f i)) :
    Continuous g :=
  continuous_iff_continuousOn_univ.2 <| h_cov ▸ hf.continuousOn_iUnion h_cl h_cont
#align locally_finite.continuous LocallyFinite.continuous

protected theorem closure (hf : LocallyFinite f) : LocallyFinite fun i => closure (f i) := by
  intro x
  -- ⊢ ∃ t, t ∈ 𝓝 x ∧ Set.Finite {i | Set.Nonempty ((fun i => closure (f i)) i ∩ t)}
  rcases hf x with ⟨s, hsx, hsf⟩
  -- ⊢ ∃ t, t ∈ 𝓝 x ∧ Set.Finite {i | Set.Nonempty ((fun i => closure (f i)) i ∩ t)}
  refine' ⟨interior s, interior_mem_nhds.2 hsx, hsf.subset fun i hi => _⟩
  -- ⊢ i ∈ {i | Set.Nonempty (f i ∩ s)}
  exact (hi.mono isOpen_interior.closure_inter).of_closure.mono
    (inter_subset_inter_right _ interior_subset)
#align locally_finite.closure LocallyFinite.closure

theorem closure_iUnion (h : LocallyFinite f) : closure (⋃ i, f i) = ⋃ i, closure (f i) := by
  ext x
  -- ⊢ x ∈ closure (⋃ (i : ι), f i) ↔ x ∈ ⋃ (i : ι), closure (f i)
  simp only [mem_closure_iff_nhdsWithin_neBot, h.nhdsWithin_iUnion, iSup_neBot, mem_iUnion]
  -- 🎉 no goals
#align locally_finite.closure_Union LocallyFinite.closure_iUnion

theorem isClosed_iUnion (hf : LocallyFinite f) (hc : ∀ i, IsClosed (f i)) :
    IsClosed (⋃ i, f i) := by
  simp only [← closure_eq_iff_isClosed, hf.closure_iUnion, (hc _).closure_eq]
  -- 🎉 no goals
#align locally_finite.is_closed_Union LocallyFinite.isClosed_iUnion

/-- If `f : β → Set α` is a locally finite family of closed sets, then for any `x : α`, the
intersection of the complements to `f i`, `x ∉ f i`, is a neighbourhood of `x`. -/
theorem iInter_compl_mem_nhds (hf : LocallyFinite f) (hc : ∀ i, IsClosed (f i)) (x : X) :
    (⋂ (i) (_ : x ∉ f i), (f i)ᶜ) ∈ 𝓝 x := by
  refine' IsOpen.mem_nhds _ (mem_iInter₂.2 fun i => id)
  -- ⊢ IsOpen (⋂ (i : ι) (_ : ¬x ∈ f i), (f i)ᶜ)
  suffices IsClosed (⋃ i : { i // x ∉ f i }, f i) by
    rwa [← isOpen_compl_iff, compl_iUnion, iInter_subtype] at this
  exact (hf.comp_injective Subtype.val_injective).isClosed_iUnion fun i => hc _
  -- 🎉 no goals
#align locally_finite.Inter_compl_mem_nhds LocallyFinite.iInter_compl_mem_nhds

/-- Let `f : ℕ → Π a, β a` be a sequence of (dependent) functions on a topological space. Suppose
that the family of sets `s n = {x | f (n + 1) x ≠ f n x}` is locally finite. Then there exists a
function `F : Π a, β a` such that for any `x`, we have `f n x = F x` on the product of an infinite
interval `[N, +∞)` and a neighbourhood of `x`.

We formulate the conclusion in terms of the product of filter `Filter.atTop` and `𝓝 x`. -/
theorem exists_forall_eventually_eq_prod {π : X → Sort*} {f : ℕ → ∀ x : X, π x}
    (hf : LocallyFinite fun n => { x | f (n + 1) x ≠ f n x }) :
    ∃ F : ∀ x : X, π x, ∀ x, ∀ᶠ p : ℕ × X in atTop ×ˢ 𝓝 x, f p.1 p.2 = F p.2 := by
  choose U hUx hU using hf
  -- ⊢ ∃ F, ∀ (x : X), ∀ᶠ (p : ℕ × X) in atTop ×ˢ 𝓝 x, f p.fst p.snd = F p.snd
  choose N hN using fun x => (hU x).bddAbove
  -- ⊢ ∃ F, ∀ (x : X), ∀ᶠ (p : ℕ × X) in atTop ×ˢ 𝓝 x, f p.fst p.snd = F p.snd
  replace hN : ∀ (x), ∀ n > N x, ∀ y ∈ U x, f (n + 1) y = f n y
  -- ⊢ ∀ (x : X) (n : ℕ), n > N x → ∀ (y : X), y ∈ U x → f (n + 1) y = f n y
  exact fun x n hn y hy => by_contra fun hne => hn.lt.not_le <| hN x ⟨y, hne, hy⟩
  -- ⊢ ∃ F, ∀ (x : X), ∀ᶠ (p : ℕ × X) in atTop ×ˢ 𝓝 x, f p.fst p.snd = F p.snd
  replace hN : ∀ (x), ∀ n ≥ N x + 1, ∀ y ∈ U x, f n y = f (N x + 1) y
  -- ⊢ ∀ (x : X) (n : ℕ), n ≥ N x + 1 → ∀ (y : X), y ∈ U x → f n y = f (N x + 1) y
  exact fun x n hn y hy => Nat.le_induction rfl (fun k hle => (hN x _ hle _ hy).trans) n hn
  -- ⊢ ∃ F, ∀ (x : X), ∀ᶠ (p : ℕ × X) in atTop ×ˢ 𝓝 x, f p.fst p.snd = F p.snd
  refine ⟨fun x => f (N x + 1) x, fun x => ?_⟩
  -- ⊢ ∀ᶠ (p : ℕ × X) in atTop ×ˢ 𝓝 x, f p.fst p.snd = (fun x => f (N x + 1) x) p.snd
  filter_upwards [Filter.prod_mem_prod (eventually_gt_atTop (N x)) (hUx x)]
  -- ⊢ ∀ (a : ℕ × X), a ∈ {x_1 | N x < x_1} ×ˢ U x → f a.fst a.snd = f (N a.snd + 1 …
  rintro ⟨n, y⟩ ⟨hn : N x < n, hy : y ∈ U x⟩
  -- ⊢ f (n, y).fst (n, y).snd = f (N (n, y).snd + 1) (n, y).snd
  calc
    f n y = f (N x + 1) y := hN _ _ hn _ hy
    _ = f (max (N x + 1) (N y + 1)) y := (hN _ _ (le_max_left _ _) _ hy).symm
    _ = f (N y + 1) y := hN _ _ (le_max_right _ _) _ (mem_of_mem_nhds <| hUx y)
#align locally_finite.exists_forall_eventually_eq_prod LocallyFinite.exists_forall_eventually_eq_prod

/-- Let `f : ℕ → Π a, β a` be a sequence of (dependent) functions on a topological space. Suppose
that the family of sets `s n = {x | f (n + 1) x ≠ f n x}` is locally finite. Then there exists a
function `F : Π a, β a` such that for any `x`, for sufficiently large values of `n`, we have
`f n y = F y` in a neighbourhood of `x`. -/
theorem exists_forall_eventually_atTop_eventually_eq' {π : X → Sort*} {f : ℕ → ∀ x : X, π x}
    (hf : LocallyFinite fun n => { x | f (n + 1) x ≠ f n x }) :
    ∃ F : ∀ x : X, π x, ∀ x, ∀ᶠ n : ℕ in atTop, ∀ᶠ y : X in 𝓝 x, f n y = F y :=
  hf.exists_forall_eventually_eq_prod.imp fun _F hF x => (hF x).curry
#align locally_finite.exists_forall_eventually_at_top_eventually_eq' LocallyFinite.exists_forall_eventually_atTop_eventually_eq'

/-- Let `f : ℕ → α → β` be a sequence of functions on a topological space. Suppose
that the family of sets `s n = {x | f (n + 1) x ≠ f n x}` is locally finite. Then there exists a
function `F :  α → β` such that for any `x`, for sufficiently large values of `n`, we have
`f n =ᶠ[𝓝 x] F`. -/
theorem exists_forall_eventually_atTop_eventuallyEq {f : ℕ → X → α}
    (hf : LocallyFinite fun n => { x | f (n + 1) x ≠ f n x }) :
    ∃ F : X → α, ∀ x, ∀ᶠ n : ℕ in atTop, f n =ᶠ[𝓝 x] F :=
  hf.exists_forall_eventually_atTop_eventually_eq'
#align locally_finite.exists_forall_eventually_at_top_eventually_eq LocallyFinite.exists_forall_eventually_atTop_eventuallyEq

theorem preimage_continuous {g : Y → X} (hf : LocallyFinite f) (hg : Continuous g) :
    LocallyFinite (g ⁻¹' f ·) := fun x =>
  let ⟨s, hsx, hs⟩ := hf (g x)
  ⟨g ⁻¹' s, hg.continuousAt hsx, hs.subset fun _ ⟨y, hy⟩ => ⟨g y, hy⟩⟩
#align locally_finite.preimage_continuous LocallyFinite.preimage_continuous

theorem prod_right (hf : LocallyFinite f) (g : ι → Set Y) : LocallyFinite (fun i ↦ f i ×ˢ g i) :=
  (hf.preimage_continuous continuous_fst).subset fun _ ↦ prod_subset_preimage_fst _ _

theorem prod_left {g : ι → Set Y} (hg : LocallyFinite g) (f : ι → Set X) :
    LocallyFinite (fun i ↦ f i ×ˢ g i) :=
  (hg.preimage_continuous continuous_snd).subset fun _ ↦ prod_subset_preimage_snd _ _

end LocallyFinite

@[simp]
theorem Equiv.locallyFinite_comp_iff (e : ι' ≃ ι) : LocallyFinite (f ∘ e) ↔ LocallyFinite f :=
  ⟨fun h => by simpa only [(· ∘ ·), e.apply_symm_apply] using h.comp_injective e.symm.injective,
               -- 🎉 no goals
    fun h => h.comp_injective e.injective⟩
#align equiv.locally_finite_comp_iff Equiv.locallyFinite_comp_iff

theorem locallyFinite_sum {f : Sum ι ι' → Set X} :
    LocallyFinite f ↔ LocallyFinite (f ∘ Sum.inl) ∧ LocallyFinite (f ∘ Sum.inr) := by
  simp only [locallyFinite_iff_smallSets, ← forall_and, ← finite_preimage_inl_and_inr,
    preimage_setOf_eq, (· ∘ ·), eventually_and]
#align locally_finite_sum locallyFinite_sum

theorem LocallyFinite.sum_elim {g : ι' → Set X} (hf : LocallyFinite f) (hg : LocallyFinite g) :
    LocallyFinite (Sum.elim f g) :=
  locallyFinite_sum.mpr ⟨hf, hg⟩
#align locally_finite.sum_elim LocallyFinite.sum_elim

theorem locallyFinite_option {f : Option ι → Set X} :
    LocallyFinite f ↔ LocallyFinite (f ∘ some) := by
  rw [← (Equiv.optionEquivSumPUnit.{_, 0} ι).symm.locallyFinite_comp_iff, locallyFinite_sum]
  -- ⊢ LocallyFinite ((f ∘ ↑(Equiv.optionEquivSumPUnit ι).symm) ∘ Sum.inl) ∧ Locall …
  simp only [locallyFinite_of_finite, and_true]
  -- ⊢ LocallyFinite ((f ∘ ↑(Equiv.optionEquivSumPUnit ι).symm) ∘ Sum.inl) ↔ Locall …
  rfl
  -- 🎉 no goals
#align locally_finite_option locallyFinite_option

theorem LocallyFinite.option_elim' (hf : LocallyFinite f) (s : Set X) :
    LocallyFinite (Option.elim' s f) :=
  locallyFinite_option.2 hf
#align locally_finite.option_elim LocallyFinite.option_elim'
