/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov
-/
module

public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Filter.CountablyGenerated
public import Mathlib.Order.Filter.Ker
public import Mathlib.Order.Filter.Pi
public import Mathlib.Order.Filter.Prod
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The cofinite filter

In this file we define

`Filter.cofinite`: the filter of sets with finite complement

and prove its basic properties. In particular, we prove that for `ℕ` it is equal to `Filter.atTop`.

## TODO

Define filters for other cardinalities of the complement.
-/

@[expose] public section

open Set Function

variable {ι α β : Type*} {l : Filter α}

namespace Filter

/-- The cofinite filter is the filter of subsets whose complements are finite. -/
def cofinite : Filter α :=
  comk Set.Finite finite_empty (fun _t ht _s hsub ↦ ht.subset hsub) fun _ h _ ↦ h.union

@[simp]
theorem mem_cofinite {s : Set α} : s ∈ @cofinite α ↔ sᶜ.Finite :=
  Iff.rfl

@[simp]
theorem eventually_cofinite {p : α → Prop} : (∀ᶠ x in cofinite, p x) ↔ { x | ¬p x }.Finite :=
  Iff.rfl

theorem hasBasis_cofinite : HasBasis cofinite (fun s : Set α => s.Finite) compl :=
  ⟨fun s =>
    ⟨fun h => ⟨sᶜ, h, (compl_compl s).subset⟩, fun ⟨_t, htf, hts⟩ =>
      htf.subset <| compl_subset_comm.2 hts⟩⟩

instance cofinite_neBot [Infinite α] : NeBot (@cofinite α) :=
  hasBasis_cofinite.neBot_iff.2 fun hs => hs.infinite_compl.nonempty

@[simp]
theorem cofinite_eq_bot_iff : @cofinite α = ⊥ ↔ Finite α := by
  simp [← empty_mem_iff_bot, finite_univ_iff]

@[simp]
theorem cofinite_eq_bot [Finite α] : @cofinite α = ⊥ := cofinite_eq_bot_iff.2 ‹_›

theorem frequently_cofinite_iff_infinite {p : α → Prop} :
    (∃ᶠ x in cofinite, p x) ↔ Set.Infinite { x | p x } := by
  simp only [Filter.Frequently, eventually_cofinite, not_not, Set.Infinite]

lemma frequently_cofinite_mem_iff_infinite {s : Set α} : (∃ᶠ x in cofinite, x ∈ s) ↔ s.Infinite :=
  frequently_cofinite_iff_infinite

alias ⟨_, _root_.Set.Infinite.frequently_cofinite⟩ := frequently_cofinite_mem_iff_infinite

@[simp]
lemma cofinite_inf_principal_neBot_iff {s : Set α} : (cofinite ⊓ 𝓟 s).NeBot ↔ s.Infinite :=
  frequently_mem_iff_neBot.symm.trans frequently_cofinite_mem_iff_infinite

alias ⟨_, _root_.Set.Infinite.cofinite_inf_principal_neBot⟩ := cofinite_inf_principal_neBot_iff

theorem _root_.Set.Finite.compl_mem_cofinite {s : Set α} (hs : s.Finite) : sᶜ ∈ @cofinite α :=
  mem_cofinite.2 <| (compl_compl s).symm ▸ hs

theorem _root_.Set.Finite.eventually_cofinite_notMem {s : Set α} (hs : s.Finite) :
    ∀ᶠ x in cofinite, x ∉ s :=
  hs.compl_mem_cofinite

@[deprecated (since := "2025-05-24")]
alias _root_.Set.Finite.eventually_cofinite_nmem := _root_.Set.Finite.eventually_cofinite_notMem

theorem _root_.Finset.eventually_cofinite_notMem (s : Finset α) : ∀ᶠ x in cofinite, x ∉ s :=
  s.finite_toSet.eventually_cofinite_notMem

@[deprecated (since := "2025-05-24")]
alias _root_.Finset.eventually_cofinite_nmem := _root_.Finset.eventually_cofinite_notMem

theorem _root_.Set.infinite_iff_frequently_cofinite {s : Set α} :
    Set.Infinite s ↔ ∃ᶠ x in cofinite, x ∈ s :=
  frequently_cofinite_iff_infinite.symm

theorem eventually_cofinite_ne (x : α) : ∀ᶠ a in cofinite, a ≠ x :=
  (Set.finite_singleton x).eventually_cofinite_notMem

theorem le_cofinite_iff_compl_singleton_mem : l ≤ cofinite ↔ ∀ x, {x}ᶜ ∈ l := by
  refine ⟨fun h x => h (finite_singleton x).compl_mem_cofinite, fun h s (hs : sᶜ.Finite) => ?_⟩
  rw [← compl_compl s, ← biUnion_of_singleton sᶜ, compl_iUnion₂, Filter.biInter_mem hs]
  exact fun x _ => h x

theorem le_cofinite_iff_eventually_ne : l ≤ cofinite ↔ ∀ x, ∀ᶠ y in l, y ≠ x :=
  le_cofinite_iff_compl_singleton_mem

/-- If `α` is a preorder with no top element, then `atTop ≤ cofinite`. -/
theorem atTop_le_cofinite [Preorder α] [NoTopOrder α] : (atTop : Filter α) ≤ cofinite :=
  le_cofinite_iff_eventually_ne.mpr eventually_ne_atTop

/-- If `α` is a preorder with no bottom element, then `atBot ≤ cofinite`. -/
theorem atBot_le_cofinite [Preorder α] [NoBotOrder α] : (atBot : Filter α) ≤ cofinite :=
  le_cofinite_iff_eventually_ne.mpr eventually_ne_atBot

theorem comap_cofinite_le (f : α → β) : comap f cofinite ≤ cofinite :=
  le_cofinite_iff_eventually_ne.mpr fun x =>
    mem_comap.2 ⟨{f x}ᶜ, (finite_singleton _).compl_mem_cofinite, fun _ => ne_of_apply_ne f⟩

/-- The coproduct of the cofinite filters on two types is the cofinite filter on their product. -/
theorem coprod_cofinite : (cofinite : Filter α).coprod (cofinite : Filter β) = cofinite :=
  Filter.coext fun s => by
    simp only [compl_mem_coprod, mem_cofinite, compl_compl, finite_image_fst_and_snd_iff]

theorem coprodᵢ_cofinite {α : ι → Type*} [Finite ι] :
    (Filter.coprodᵢ fun i => (cofinite : Filter (α i))) = cofinite :=
  Filter.coext fun s => by
    simp only [compl_mem_coprodᵢ, mem_cofinite, compl_compl, forall_finite_image_eval_iff]

theorem disjoint_cofinite_left : Disjoint cofinite l ↔ ∃ s ∈ l, Set.Finite s := by
  simp [l.basis_sets.disjoint_iff_right]

theorem disjoint_cofinite_right : Disjoint l cofinite ↔ ∃ s ∈ l, Set.Finite s :=
  disjoint_comm.trans disjoint_cofinite_left

/-- If `l ≥ Filter.cofinite` is a countably generated filter, then `l.ker` is cocountable. -/
theorem countable_compl_ker [l.IsCountablyGenerated] (h : cofinite ≤ l) : Set.Countable l.kerᶜ := by
  rcases exists_antitone_basis l with ⟨s, hs⟩
  simp only [hs.ker, iInter_true, compl_iInter]
  exact countable_iUnion fun n ↦ Set.Finite.countable <| h <| hs.mem _

/-- If `f` tends to a countably generated filter `l` along `Filter.cofinite`,
then for all but countably many elements, `f x ∈ l.ker`. -/
theorem Tendsto.countable_compl_preimage_ker {f : α → β}
    {l : Filter β} [l.IsCountablyGenerated] (h : Tendsto f cofinite l) :
    Set.Countable (f ⁻¹' l.ker)ᶜ := by rw [← ker_comap]; exact countable_compl_ker h.le_comap

/-- Given a collection of filters `l i : Filter (α i)` and sets `s i ∈ l i`,
if all but finitely many of `s i` are the whole space,
then their indexed product `Set.pi Set.univ s` belongs to the filter `Filter.pi l`. -/
theorem univ_pi_mem_pi {α : ι → Type*} {s : ∀ i, Set (α i)} {l : ∀ i, Filter (α i)}
    (h : ∀ i, s i ∈ l i) (hfin : ∀ᶠ i in cofinite, s i = univ) : univ.pi s ∈ pi l := by
  filter_upwards [pi_mem_pi hfin fun i _ ↦ h i] with a ha i _
  if hi : s i = univ then
    simp [hi]
  else
    exact ha i hi

/-- Given a family of maps `f i : α i → β i` and a family of filters `l i : Filter (α i)`,
if all but finitely many of `f i` are surjective,
then the indexed product of `f i`s maps the indexed product of the filters `l i`
to the indexed products of their pushforwards under individual `f i`s.

See also `map_piMap_pi_finite` for the case of a finite index type.
-/
theorem map_piMap_pi {α β : ι → Type*} {f : ∀ i, α i → β i}
    (hf : ∀ᶠ i in cofinite, Surjective (f i)) (l : ∀ i, Filter (α i)) :
    map (Pi.map f) (pi l) = pi fun i ↦ map (f i) (l i) := by
  refine le_antisymm (tendsto_piMap_pi fun _ ↦ tendsto_map) ?_
  refine ((hasBasis_pi fun i ↦ (l i).basis_sets).map _).ge_iff.2 ?_
  rintro ⟨I, s⟩ ⟨hI : I.Finite, hs : ∀ i ∈ I, s i ∈ l i⟩
  classical
  rw [← univ_pi_piecewise_univ, piMap_image_univ_pi]
  refine univ_pi_mem_pi (fun i ↦ ?_) ?_
  · by_cases hi : i ∈ I
    · simpa [hi] using image_mem_map (hs i hi)
    · simp [hi]
  · filter_upwards [hf, hI.compl_mem_cofinite] with i hsurj (hiI : i ∉ I)
    simp [hiI, hsurj.range_eq]

/-- Given finite families of maps `f i : α i → β i` and of filters `l i : Filter (α i)`,
the indexed product of `f i`s maps the indexed product of the filters `l i`
to the indexed products of their pushforwards under individual `f i`s.

See also `map_piMap_pi` for a more general case.
-/
theorem map_piMap_pi_finite {α β : ι → Type*} [Finite ι]
    (f : ∀ i, α i → β i) (l : ∀ i, Filter (α i)) :
    map (Pi.map f) (pi l) = pi fun i ↦ map (f i) (l i) :=
  map_piMap_pi (by simp) l

end Filter

open Filter

lemma Set.Finite.cofinite_inf_principal_compl {s : Set α} (hs : s.Finite) :
    cofinite ⊓ 𝓟 sᶜ = cofinite := by
  simpa using hs.compl_mem_cofinite

lemma Set.Finite.cofinite_inf_principal_diff {s t : Set α} (ht : t.Finite) :
    cofinite ⊓ 𝓟 (s \ t) = cofinite ⊓ 𝓟 s := by
  rw [diff_eq, ← inf_principal, ← inf_assoc, inf_right_comm, ht.cofinite_inf_principal_compl]

/-- For natural numbers the filters `Filter.cofinite` and `Filter.atTop` coincide. -/
theorem Nat.cofinite_eq_atTop : @cofinite ℕ = atTop := by
  refine le_antisymm ?_ atTop_le_cofinite
  refine atTop_basis.ge_iff.2 fun N _ => ?_
  simpa only [mem_cofinite, compl_Ici] using finite_lt_nat N

theorem Nat.frequently_atTop_iff_infinite {p : ℕ → Prop} :
    (∃ᶠ n in atTop, p n) ↔ Set.Infinite { n | p n } := by
  rw [← Nat.cofinite_eq_atTop, frequently_cofinite_iff_infinite]

lemma Nat.eventually_pos : ∀ᶠ (k : ℕ) in Filter.atTop, 0 < k :=
  Filter.eventually_of_mem (Filter.mem_atTop_sets.mpr ⟨1, fun _ hx ↦ hx⟩) (fun _ hx ↦ hx)

theorem Filter.Tendsto.exists_within_forall_le {α β : Type*} [LinearOrder β] {s : Set α}
    (hs : s.Nonempty) {f : α → β} (hf : Filter.Tendsto f Filter.cofinite Filter.atTop) :
    ∃ a₀ ∈ s, ∀ a ∈ s, f a₀ ≤ f a := by
  by_cases! all_top : ∃ y ∈ s, ∃ x, f y < x
  · -- the set of points `{y | f y < x}` is nonempty and finite, so we take `min` over this set
    rcases all_top with ⟨y, hys, x, hx⟩
    have : { y | ¬x ≤ f y }.Finite := Filter.eventually_cofinite.mp (tendsto_atTop.1 hf x)
    simp only [not_le] at this
    obtain ⟨a₀, ⟨ha₀ : f a₀ < x, ha₀s⟩, others_bigger⟩ :=
      exists_min_image _ f (this.inter_of_left s) ⟨y, hx, hys⟩
    refine ⟨a₀, ha₀s, fun a has => (lt_or_ge (f a) x).elim ?_ (le_trans ha₀.le)⟩
    exact fun h => others_bigger a ⟨h, has⟩
  · -- in this case, f is constant because all values are at top
    obtain ⟨a₀, ha₀s⟩ := hs
    exact ⟨a₀, ha₀s, fun a ha => all_top a ha (f a₀)⟩

theorem Filter.Tendsto.exists_forall_le [Nonempty α] [LinearOrder β] {f : α → β}
    (hf : Tendsto f cofinite atTop) : ∃ a₀, ∀ a, f a₀ ≤ f a :=
  let ⟨a₀, _, ha₀⟩ := hf.exists_within_forall_le univ_nonempty
  ⟨a₀, fun a => ha₀ a (mem_univ _)⟩

theorem Filter.Tendsto.exists_within_forall_ge [LinearOrder β] {s : Set α} (hs : s.Nonempty)
    {f : α → β} (hf : Filter.Tendsto f Filter.cofinite Filter.atBot) :
    ∃ a₀ ∈ s, ∀ a ∈ s, f a ≤ f a₀ :=
  @Filter.Tendsto.exists_within_forall_le _ βᵒᵈ _ _ hs _ hf

theorem Filter.Tendsto.exists_forall_ge [Nonempty α] [LinearOrder β] {f : α → β}
    (hf : Tendsto f cofinite atBot) : ∃ a₀, ∀ a, f a ≤ f a₀ :=
  @Filter.Tendsto.exists_forall_le _ βᵒᵈ _ _ _ hf

theorem Function.Surjective.le_map_cofinite {f : α → β} (hf : Surjective f) :
    cofinite ≤ map f cofinite := fun _ h => .of_preimage h hf

/-- For an injective function `f`, inverse images of finite sets are finite. See also
`Filter.comap_cofinite_le` and `Function.Injective.comap_cofinite_eq`. -/
theorem Function.Injective.tendsto_cofinite {f : α → β} (hf : Injective f) :
    Tendsto f cofinite cofinite := fun _ h => h.preimage hf.injOn

/-- For a function with finite fibres, inverse images of finite sets are finite. -/
theorem Filter.Tendsto.cofinite_of_finite_preimage_singleton {f : α → β}
    (hf : ∀ b, Finite (f ⁻¹' {b})) : Tendsto f cofinite cofinite :=
  fun _ h => h.preimage' fun b _ ↦ hf b

/-- The pullback of the `Filter.cofinite` under an injective function is equal to `Filter.cofinite`.
See also `Filter.comap_cofinite_le` and `Function.Injective.tendsto_cofinite`. -/
theorem Function.Injective.comap_cofinite_eq {f : α → β} (hf : Injective f) :
    comap f cofinite = cofinite :=
  (comap_cofinite_le f).antisymm hf.tendsto_cofinite.le_comap

/-- An injective sequence `f : ℕ → ℕ` tends to infinity at infinity. -/
theorem Function.Injective.nat_tendsto_atTop {f : ℕ → ℕ} (hf : Injective f) :
    Tendsto f atTop atTop :=
  Nat.cofinite_eq_atTop ▸ hf.tendsto_cofinite

lemma Function.update_eventuallyEq [DecidableEq α] (f : α → β) (a : α) (b : β) :
    Function.update f a b =ᶠ[𝓟 {a}ᶜ] f := by
  filter_upwards [mem_principal_self _] with u hu using Function.update_of_ne hu _ _

lemma Function.update_eventuallyEq_cofinite [DecidableEq α] (f : α → β) (a : α) (b : β) :
    Function.update f a b =ᶠ[cofinite] f :=
  (Function.update_eventuallyEq f a b).filter_mono (by simp)

/--
A filter is free iff it is smaller than the cofinite filter.
-/
theorem le_cofinite_iff_ker (f : Filter α) : f ≤ cofinite ↔ f.ker = ∅ := by
  rw [le_cofinite_iff_compl_singleton_mem, ker_def, iInter₂_eq_empty_iff]
  exact forall_congr' fun x => ⟨fun h => ⟨{x}ᶜ, h, by simp⟩,
    fun ⟨s, hs, hx⟩ => mem_of_superset hs (by simpa using hx)⟩

lemma eq_principal_ker_sup_inf_principal_ker_compl (f : Filter α) :
    f = 𝓟 f.ker ⊔ (f ⊓ 𝓟 f.kerᶜ) := by
  rw [sup_inf_left]
  simpa using gi_principal_ker.gc.l_u_le f

lemma inf_principal_ker_compl_le_cofinite (f : Filter α) : f ⊓ 𝓟 f.kerᶜ ≤ cofinite := by
  rw [le_cofinite_iff_ker, ker_inf, ker_principal, inter_compl_self]

/--
Every filter is the disjoint supremum of a principal filter and a free filter in a unique way.
-/
theorem existsUnique_eq_principal_sup_free (f : Filter α) :
    ∃! p : Set α × Filter α, p.2 ≤ cofinite ∧ Disjoint (𝓟 p.1) p.2 ∧ f = 𝓟 p.1 ⊔ p.2 := by
  refine ⟨(f.ker, f ⊓ 𝓟 f.kerᶜ), ⟨?_, ?_, ?_⟩, fun q hq => ?_⟩
  · exact inf_principal_ker_compl_le_cofinite f
  · rw [disjoint_principal_left]
    exact mem_inf_of_right (mem_principal_self f.kerᶜ)
  · exact eq_principal_ker_sup_inf_principal_ker_compl f
  · have hqk := congrArg Filter.ker hq.2.2
    rw [ker_sup, ker_principal, (le_cofinite_iff_ker q.2).mp hq.1, union_empty] at hqk
    refine congrArg₂ Prod.mk hqk.symm (le_antisymm (le_inf ?_ ?_) ?_)
    · rw [hq.2.2]
      exact le_sup_right
    · rw [le_principal_iff, hqk, ← disjoint_principal_left]
      exact hq.2.1
    · rw [hqk, hq.2.2, inf_sup_right, inf_principal, inter_compl_self, principal_empty, bot_sup_eq]
      exact inf_le_left

/--
Every filter is the disjoint supremum of a principal filter and a free filter.
-/
theorem exists_eq_principal_sup_free (f : Filter α) :
    ∃ s g, g ≤ cofinite ∧ Disjoint (𝓟 s) g ∧ f = 𝓟 s ⊔ g :=
  Prod.exists.mp (existsUnique_eq_principal_sup_free f).exists
