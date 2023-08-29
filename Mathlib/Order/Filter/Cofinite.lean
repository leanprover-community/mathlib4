/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov
-/
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Order.Filter.Pi

#align_import order.filter.cofinite from "leanprover-community/mathlib"@"8631e2d5ea77f6c13054d9151d82b83069680cb1"

/-!
# The cofinite filter

In this file we define

`Filter.cofinite`: the filter of sets with finite complement

and prove its basic properties. In particular, we prove that for `ℕ` it is equal to `Filter.atTop`.

## TODO

Define filters for other cardinalities of the complement.
-/

open Set Function

variable {ι α β : Type*} {l : Filter α}

namespace Filter

/-- The cofinite filter is the filter of subsets whose complements are finite. -/
def cofinite : Filter α where
  sets := { s | sᶜ.Finite }
  univ_sets := by simp only [compl_univ, finite_empty, mem_setOf_eq]
                  -- 🎉 no goals
  sets_of_superset hs st := hs.subset <| compl_subset_compl.2 st
  inter_sets hs ht := by simpa only [compl_inter, mem_setOf_eq] using hs.union ht
                         -- 🎉 no goals
#align filter.cofinite Filter.cofinite

@[simp]
theorem mem_cofinite {s : Set α} : s ∈ @cofinite α ↔ sᶜ.Finite :=
  Iff.rfl
#align filter.mem_cofinite Filter.mem_cofinite

@[simp]
theorem eventually_cofinite {p : α → Prop} : (∀ᶠ x in cofinite, p x) ↔ { x | ¬p x }.Finite :=
  Iff.rfl
#align filter.eventually_cofinite Filter.eventually_cofinite

theorem hasBasis_cofinite : HasBasis cofinite (fun s : Set α => s.Finite) compl :=
  ⟨fun s =>
    ⟨fun h => ⟨sᶜ, h, (compl_compl s).subset⟩, fun ⟨_t, htf, hts⟩ =>
      htf.subset <| compl_subset_comm.2 hts⟩⟩
#align filter.has_basis_cofinite Filter.hasBasis_cofinite

instance cofinite_neBot [Infinite α] : NeBot (@cofinite α) :=
  hasBasis_cofinite.neBot_iff.2 fun hs => hs.infinite_compl.nonempty
#align filter.cofinite_ne_bot Filter.cofinite_neBot

@[simp]
theorem cofinite_eq_bot_iff : @cofinite α = ⊥ ↔ Finite α := by
  simp [← empty_mem_iff_bot, finite_univ_iff]
  -- 🎉 no goals

@[simp]
theorem cofinite_eq_bot [Finite α] : @cofinite α = ⊥ := cofinite_eq_bot_iff.2 ‹_›

theorem frequently_cofinite_iff_infinite {p : α → Prop} :
    (∃ᶠ x in cofinite, p x) ↔ Set.Infinite { x | p x } := by
  simp only [Filter.Frequently, Filter.Eventually, mem_cofinite, compl_setOf, not_not,
    Set.Infinite]
#align filter.frequently_cofinite_iff_infinite Filter.frequently_cofinite_iff_infinite

theorem _root_.Set.Finite.compl_mem_cofinite {s : Set α} (hs : s.Finite) : sᶜ ∈ @cofinite α :=
  mem_cofinite.2 <| (compl_compl s).symm ▸ hs
#align set.finite.compl_mem_cofinite Set.Finite.compl_mem_cofinite

theorem _root_.Set.Finite.eventually_cofinite_nmem {s : Set α} (hs : s.Finite) :
    ∀ᶠ x in cofinite, x ∉ s :=
  hs.compl_mem_cofinite
#align set.finite.eventually_cofinite_nmem Set.Finite.eventually_cofinite_nmem

theorem _root_.Finset.eventually_cofinite_nmem (s : Finset α) : ∀ᶠ x in cofinite, x ∉ s :=
  s.finite_toSet.eventually_cofinite_nmem
#align finset.eventually_cofinite_nmem Finset.eventually_cofinite_nmem

theorem _root_.Set.infinite_iff_frequently_cofinite {s : Set α} :
    Set.Infinite s ↔ ∃ᶠ x in cofinite, x ∈ s :=
  frequently_cofinite_iff_infinite.symm
#align set.infinite_iff_frequently_cofinite Set.infinite_iff_frequently_cofinite

theorem eventually_cofinite_ne (x : α) : ∀ᶠ a in cofinite, a ≠ x :=
  (Set.finite_singleton x).eventually_cofinite_nmem
#align filter.eventually_cofinite_ne Filter.eventually_cofinite_ne

theorem le_cofinite_iff_compl_singleton_mem : l ≤ cofinite ↔ ∀ x, {x}ᶜ ∈ l := by
  refine' ⟨fun h x => h (finite_singleton x).compl_mem_cofinite, fun h s (hs : sᶜ.Finite) => _⟩
  -- ⊢ s ∈ l
  rw [← compl_compl s, ← biUnion_of_singleton sᶜ, compl_iUnion₂, Filter.biInter_mem hs]
  -- ⊢ ∀ (i : α), i ∈ sᶜ → {i}ᶜ ∈ l
  exact fun x _ => h x
  -- 🎉 no goals
#align filter.le_cofinite_iff_compl_singleton_mem Filter.le_cofinite_iff_compl_singleton_mem

theorem le_cofinite_iff_eventually_ne : l ≤ cofinite ↔ ∀ x, ∀ᶠ y in l, y ≠ x :=
  le_cofinite_iff_compl_singleton_mem
#align filter.le_cofinite_iff_eventually_ne Filter.le_cofinite_iff_eventually_ne

/-- If `α` is a preorder with no maximal element, then `atTop ≤ cofinite`. -/
theorem atTop_le_cofinite [Preorder α] [NoMaxOrder α] : (atTop : Filter α) ≤ cofinite :=
  le_cofinite_iff_eventually_ne.mpr eventually_ne_atTop
#align filter.at_top_le_cofinite Filter.atTop_le_cofinite

theorem comap_cofinite_le (f : α → β) : comap f cofinite ≤ cofinite :=
  le_cofinite_iff_eventually_ne.mpr fun x =>
    mem_comap.2 ⟨{f x}ᶜ, (finite_singleton _).compl_mem_cofinite, fun _ => ne_of_apply_ne f⟩
#align filter.comap_cofinite_le Filter.comap_cofinite_le

/-- The coproduct of the cofinite filters on two types is the cofinite filter on their product. -/
theorem coprod_cofinite : (cofinite : Filter α).coprod (cofinite : Filter β) = cofinite :=
  Filter.coext fun s => by
    simp only [compl_mem_coprod, mem_cofinite, compl_compl, finite_image_fst_and_snd_iff]
    -- 🎉 no goals
#align filter.coprod_cofinite Filter.coprod_cofinite

theorem coprodᵢ_cofinite {α : ι → Type*} [Finite ι] :
    (Filter.coprodᵢ fun i => (cofinite : Filter (α i))) = cofinite :=
  Filter.coext fun s => by
    simp only [compl_mem_coprodᵢ, mem_cofinite, compl_compl, forall_finite_image_eval_iff]
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align filter.Coprod_cofinite Filter.coprodᵢ_cofinite

@[simp]
theorem disjoint_cofinite_left : Disjoint cofinite l ↔ ∃ s ∈ l, Set.Finite s := by
  simp only [hasBasis_cofinite.disjoint_iff l.basis_sets, id, disjoint_compl_left_iff_subset]
  -- ⊢ (∃ i, Set.Finite i ∧ ∃ i', i' ∈ l ∧ i' ⊆ i) ↔ ∃ s, s ∈ l ∧ Set.Finite s
  exact ⟨fun ⟨s, hs, t, ht, hts⟩ => ⟨t, ht, hs.subset hts⟩,
    fun ⟨s, hs, hsf⟩ => ⟨s, hsf, s, hs, Subset.rfl⟩⟩
#align filter.disjoint_cofinite_left Filter.disjoint_cofinite_left

@[simp]
theorem disjoint_cofinite_right : Disjoint l cofinite ↔ ∃ s ∈ l, Set.Finite s :=
  disjoint_comm.trans disjoint_cofinite_left
#align filter.disjoint_cofinite_right Filter.disjoint_cofinite_right

/-- If `l ≥ Filter.cofinite` is a countably generated filter, then `⋂₀ l.sets` is cocountable. -/
theorem countable_compl_sInter_sets [l.IsCountablyGenerated] (h : cofinite ≤ l) :
    Set.Countable (⋂₀ l.sets)ᶜ := by
  rcases exists_antitone_basis l with ⟨s, hs⟩
  -- ⊢ Set.Countable (⋂₀ l.sets)ᶜ
  simp only [hs.sInter_sets, iInter_true, compl_iInter]
  -- ⊢ Set.Countable (⋃ (i : ℕ), (s i)ᶜ)
  exact countable_iUnion fun n ↦ Set.Finite.countable <| h <| hs.mem _
  -- 🎉 no goals

/-- If `f` tends to a countably generated filter `l` along `Filter.cofinite`,
then for all but countably many elements, `f x ∈ ⋂₀ l.sets`. -/
theorem Tendsto.countable_compl_preimage_sInter_sets {f : α → β}
    {l : Filter β} [l.IsCountablyGenerated] (h : Tendsto f cofinite l) :
    Set.Countable (f ⁻¹' (⋂₀ l.sets))ᶜ := by
  erw [preimage_sInter, ← sInter_comap_sets]
  -- ⊢ Set.Countable (⋂₀ (comap f l).sets)ᶜ
  exact countable_compl_sInter_sets h.le_comap
  -- 🎉 no goals

end Filter

open Filter

/-- For natural numbers the filters `Filter.cofinite` and `Filter.atTop` coincide. -/
theorem Nat.cofinite_eq_atTop : @cofinite ℕ = atTop := by
  refine' le_antisymm _ atTop_le_cofinite
  -- ⊢ cofinite ≤ atTop
  refine' atTop_basis.ge_iff.2 fun N _ => _
  -- ⊢ Ici N ∈ cofinite
  simpa only [mem_cofinite, compl_Ici] using finite_lt_nat N
  -- 🎉 no goals
#align nat.cofinite_eq_at_top Nat.cofinite_eq_atTop

theorem Nat.frequently_atTop_iff_infinite {p : ℕ → Prop} :
    (∃ᶠ n in atTop, p n) ↔ Set.Infinite { n | p n } := by
  rw [← Nat.cofinite_eq_atTop, frequently_cofinite_iff_infinite]
  -- 🎉 no goals
#align nat.frequently_at_top_iff_infinite Nat.frequently_atTop_iff_infinite

theorem Filter.Tendsto.exists_within_forall_le {α β : Type*} [LinearOrder β] {s : Set α}
    (hs : s.Nonempty) {f : α → β} (hf : Filter.Tendsto f Filter.cofinite Filter.atTop) :
    ∃ a₀ ∈ s, ∀ a ∈ s, f a₀ ≤ f a := by
  rcases em (∃ y ∈ s, ∃ x, f y < x) with (⟨y, hys, x, hx⟩ | not_all_top)
  -- ⊢ ∃ a₀, a₀ ∈ s ∧ ∀ (a : α), a ∈ s → f a₀ ≤ f a
  · -- the set of points `{y | f y < x}` is nonempty and finite, so we take `min` over this set
    have : { y | ¬x ≤ f y }.Finite := Filter.eventually_cofinite.mp (tendsto_atTop.1 hf x)
    -- ⊢ ∃ a₀, a₀ ∈ s ∧ ∀ (a : α), a ∈ s → f a₀ ≤ f a
    simp only [not_le] at this
    -- ⊢ ∃ a₀, a₀ ∈ s ∧ ∀ (a : α), a ∈ s → f a₀ ≤ f a
    obtain ⟨a₀, ⟨ha₀ : f a₀ < x, ha₀s⟩, others_bigger⟩ :=
      exists_min_image _ f (this.inter_of_left s) ⟨y, hx, hys⟩
    refine' ⟨a₀, ha₀s, fun a has => (lt_or_le (f a) x).elim _ (le_trans ha₀.le)⟩
    -- ⊢ f a < x → f a₀ ≤ f a
    exact fun h => others_bigger a ⟨h, has⟩
    -- 🎉 no goals
  · -- in this case, f is constant because all values are at top
    push_neg at not_all_top
    -- ⊢ ∃ a₀, a₀ ∈ s ∧ ∀ (a : α), a ∈ s → f a₀ ≤ f a
    obtain ⟨a₀, ha₀s⟩ := hs
    -- ⊢ ∃ a₀, a₀ ∈ s ∧ ∀ (a : α), a ∈ s → f a₀ ≤ f a
    exact ⟨a₀, ha₀s, fun a ha => not_all_top a ha (f a₀)⟩
    -- 🎉 no goals
#align filter.tendsto.exists_within_forall_le Filter.Tendsto.exists_within_forall_le

theorem Filter.Tendsto.exists_forall_le [Nonempty α] [LinearOrder β] {f : α → β}
    (hf : Tendsto f cofinite atTop) : ∃ a₀, ∀ a, f a₀ ≤ f a :=
  let ⟨a₀, _, ha₀⟩ := hf.exists_within_forall_le univ_nonempty
  ⟨a₀, fun a => ha₀ a (mem_univ _)⟩
#align filter.tendsto.exists_forall_le Filter.Tendsto.exists_forall_le

theorem Filter.Tendsto.exists_within_forall_ge [LinearOrder β] {s : Set α} (hs : s.Nonempty)
    {f : α → β} (hf : Filter.Tendsto f Filter.cofinite Filter.atBot) :
    ∃ a₀ ∈ s, ∀ a ∈ s, f a ≤ f a₀ :=
  @Filter.Tendsto.exists_within_forall_le _ βᵒᵈ _ _ hs _ hf
#align filter.tendsto.exists_within_forall_ge Filter.Tendsto.exists_within_forall_ge

theorem Filter.Tendsto.exists_forall_ge [Nonempty α] [LinearOrder β] {f : α → β}
    (hf : Tendsto f cofinite atBot) : ∃ a₀, ∀ a, f a ≤ f a₀ :=
  @Filter.Tendsto.exists_forall_le _ βᵒᵈ _ _ _ hf
#align filter.tendsto.exists_forall_ge Filter.Tendsto.exists_forall_ge

theorem Function.Surjective.le_map_cofinite {f : α → β} (hf : Surjective f) :
    cofinite ≤ map f cofinite := fun _ h => .of_preimage h hf

/-- For an injective function `f`, inverse images of finite sets are finite. See also
`Filter.comap_cofinite_le` and `Function.Injective.comap_cofinite_eq`. -/
theorem Function.Injective.tendsto_cofinite {f : α → β} (hf : Injective f) :
    Tendsto f cofinite cofinite := fun _ h => h.preimage (hf.injOn _)
#align function.injective.tendsto_cofinite Function.Injective.tendsto_cofinite

/-- The pullback of the `Filter.cofinite` under an injective function is equal to `Filter.cofinite`.
See also `Filter.comap_cofinite_le` and `Function.Injective.tendsto_cofinite`. -/
theorem Function.Injective.comap_cofinite_eq {f : α → β} (hf : Injective f) :
    comap f cofinite = cofinite :=
  (comap_cofinite_le f).antisymm hf.tendsto_cofinite.le_comap
#align function.injective.comap_cofinite_eq Function.Injective.comap_cofinite_eq

/-- An injective sequence `f : ℕ → ℕ` tends to infinity at infinity. -/
theorem Function.Injective.nat_tendsto_atTop {f : ℕ → ℕ} (hf : Injective f) :
    Tendsto f atTop atTop :=
  Nat.cofinite_eq_atTop ▸ hf.tendsto_cofinite
#align function.injective.nat_tendsto_at_top Function.Injective.nat_tendsto_atTop
