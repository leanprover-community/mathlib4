/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.Data.Set.Sigma
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.Map
import Mathlib.Order.Interval.Set.Basic

/-!
# Basic results on filter bases

A filter basis `B : FilterBasis α` on a type `α` is a nonempty collection of sets of `α`
such that the intersection of two elements of this collection contains some element of
the collection. Compared to filters, filter bases do not require that any set containing
an element of `B` belongs to `B`.
A filter basis `B` can be used to construct `B.filter : Filter α` such that a set belongs
to `B.filter` if and only if it contains an element of `B`.

Given an indexing type `ι`, a predicate `p : ι → Prop`, and a map `s : ι → Set α`,
the proposition `h : Filter.IsBasis p s` makes sure the range of `s` bounded by `p`
(ie. `s '' setOf p`) defines a filter basis `h.filterBasis`.

If one already has a filter `l` on `α`, `Filter.HasBasis l p s` (where `p : ι → Prop`
and `s : ι → Set α` as above) means that a set belongs to `l` if and
only if it contains some `s i` with `p i`. It implies `h : Filter.IsBasis p s`, and
`l = h.filterBasis.filter`. The point of this definition is that checking statements
involving elements of `l` often reduces to checking them on the basis elements.

We define a function `HasBasis.index (h : Filter.HasBasis l p s) (t) (ht : t ∈ l)` that returns
some index `i` such that `p i` and `s i ⊆ t`. This function can be useful to avoid manual
destruction of `h.mem_iff.mpr ht` using `cases` or `let`.

## Main statements

* `Filter.HasBasis.mem_iff`, `HasBasis.mem_of_superset`, `HasBasis.mem_of_mem` : restate `t ∈ f` in
  terms of a basis;

* `Filter.HasBasis.le_iff`, `Filter.HasBasis.ge_iff`, `Filter.HasBasis.le_basis_iff` : restate
  `l ≤ l'` in terms of bases.

* `Filter.basis_sets` : all sets of a filter form a basis;

* `Filter.HasBasis.inf`, `Filter.HasBasis.inf_principal`, `Filter.HasBasis.prod`,
  `Filter.HasBasis.prod_self`, `Filter.HasBasis.map`, `Filter.HasBasis.comap` : combinators to
  construct filters of `l ⊓ l'`, `l ⊓ 𝓟 t`, `l ×ˢ l'`, `l ×ˢ l`, `l.map f`, `l.comap f`
  respectively;

* `Filter.HasBasis.tendsto_right_iff`, `Filter.HasBasis.tendsto_left_iff`,
  `Filter.HasBasis.tendsto_iff` : restate `Tendsto f l l'` in terms of bases.

## Implementation notes

As with `Set.iUnion`/`biUnion`/`Set.sUnion`, there are three different approaches to filter bases:

* `Filter.HasBasis l s`, `s : Set (Set α)`;
* `Filter.HasBasis l s`, `s : ι → Set α`;
* `Filter.HasBasis l p s`, `p : ι → Prop`, `s : ι → Set α`.

We use the latter one because, e.g., `𝓝 x` in an `EMetricSpace` or in a `MetricSpace` has a basis
of this form. The other two can be emulated using `s = id` or `p = fun _ ↦ True`.

With this approach sometimes one needs to `simp` the statement provided by the `Filter.HasBasis`
machinery, e.g., `simp only [true_and_iff]` or `simp only [forall_const]` can help with the case
`p = fun _ ↦ True`.

## Main statements
-/

assert_not_exists Finset

open Set Filter

variable {α β γ : Type*} {ι ι' : Sort*}

/-- A filter basis `B` on a type `α` is a nonempty collection of sets of `α`
such that the intersection of two elements of this collection contains some element
of the collection. -/
structure FilterBasis (α : Type*) where
  /-- Sets of a filter basis. -/
  sets : Set (Set α)
  /-- The set of filter basis sets is nonempty. -/
  nonempty : sets.Nonempty
  /-- The set of filter basis sets is directed downwards. -/
  inter_sets {x y} : x ∈ sets → y ∈ sets → ∃ z ∈ sets, z ⊆ x ∩ y

instance FilterBasis.nonempty_sets (B : FilterBasis α) : Nonempty B.sets :=
  B.nonempty.to_subtype

/-- If `B` is a filter basis on `α`, and `U` a subset of `α` then we can write `U ∈ B` as
on paper. -/
instance {α : Type*} : Membership (Set α) (FilterBasis α) :=
  ⟨fun B U => U ∈ B.sets⟩

@[simp] theorem FilterBasis.mem_sets {s : Set α} {B : FilterBasis α} : s ∈ B.sets ↔ s ∈ B := Iff.rfl

-- For illustration purposes, the filter basis defining `(atTop : Filter ℕ)`
instance : Inhabited (FilterBasis ℕ) :=
  ⟨{  sets := range Ici
      nonempty := ⟨Ici 0, mem_range_self 0⟩
      inter_sets := by
        rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
        exact ⟨Ici (max n m), mem_range_self _, Ici_inter_Ici.symm.subset⟩ }⟩

/-- View a filter as a filter basis. -/
def Filter.asBasis (f : Filter α) : FilterBasis α :=
  ⟨f.sets, ⟨univ, univ_mem⟩, fun {x y} hx hy => ⟨x ∩ y, inter_mem hx hy, subset_rfl⟩⟩

-- TODO: consider adding `protected`?
/-- `IsBasis p s` means the image of `s` bounded by `p` is a filter basis. -/
structure Filter.IsBasis (p : ι → Prop) (s : ι → Set α) : Prop where
  /-- There exists at least one `i` that satisfies `p`. -/
  nonempty : ∃ i, p i
  /-- `s` is directed downwards on `i` such that `p i`. -/
  inter : ∀ {i j}, p i → p j → ∃ k, p k ∧ s k ⊆ s i ∩ s j

namespace Filter

namespace IsBasis

/-- Constructs a filter basis from an indexed family of sets satisfying `IsBasis`. -/
protected def filterBasis {p : ι → Prop} {s : ι → Set α} (h : IsBasis p s) : FilterBasis α where
  sets := { t | ∃ i, p i ∧ s i = t }
  nonempty :=
    let ⟨i, hi⟩ := h.nonempty
    ⟨s i, ⟨i, hi, rfl⟩⟩
  inter_sets := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    rcases h.inter hi hj with ⟨k, hk, hk'⟩
    exact ⟨_, ⟨k, hk, rfl⟩, hk'⟩

variable {p : ι → Prop} {s : ι → Set α} (h : IsBasis p s)

theorem mem_filterBasis_iff {U : Set α} : U ∈ h.filterBasis ↔ ∃ i, p i ∧ s i = U :=
  Iff.rfl

end IsBasis

end Filter

namespace FilterBasis

/-- The filter associated to a filter basis. -/
protected def filter (B : FilterBasis α) : Filter α where
  sets := { s | ∃ t ∈ B, t ⊆ s }
  univ_sets := B.nonempty.imp fun s s_in => ⟨s_in, s.subset_univ⟩
  sets_of_superset := fun ⟨s, s_in, h⟩ hxy => ⟨s, s_in, Set.Subset.trans h hxy⟩
  inter_sets := fun ⟨_s, s_in, hs⟩ ⟨_t, t_in, ht⟩ =>
    let ⟨u, u_in, u_sub⟩ := B.inter_sets s_in t_in
    ⟨u, u_in, u_sub.trans (inter_subset_inter hs ht)⟩

theorem mem_filter_iff (B : FilterBasis α) {U : Set α} : U ∈ B.filter ↔ ∃ s ∈ B, s ⊆ U :=
  Iff.rfl

theorem mem_filter_of_mem (B : FilterBasis α) {U : Set α} : U ∈ B → U ∈ B.filter := fun U_in =>
  ⟨U, U_in, Subset.refl _⟩

theorem eq_iInf_principal (B : FilterBasis α) : B.filter = ⨅ s : B.sets, 𝓟 s := by
  have : Directed (· ≥ ·) fun s : B.sets => 𝓟 (s : Set α) := by
    rintro ⟨U, U_in⟩ ⟨V, V_in⟩
    rcases B.inter_sets U_in V_in with ⟨W, W_in, W_sub⟩
    use ⟨W, W_in⟩
    simp only [le_principal_iff, mem_principal]
    exact subset_inter_iff.mp W_sub
  ext U
  simp [mem_filter_iff, mem_iInf_of_directed this]

protected theorem generate (B : FilterBasis α) : generate B.sets = B.filter := by
  apply le_antisymm
  · intro U U_in
    rcases B.mem_filter_iff.mp U_in with ⟨V, V_in, h⟩
    exact GenerateSets.superset (GenerateSets.basic V_in) h
  · rw [le_generate_iff]
    apply mem_filter_of_mem

end FilterBasis

namespace Filter

namespace IsBasis

variable {p : ι → Prop} {s : ι → Set α}

/-- Constructs a filter from an indexed family of sets satisfying `IsBasis`. -/
protected def filter (h : IsBasis p s) : Filter α :=
  h.filterBasis.filter

protected theorem mem_filter_iff (h : IsBasis p s) {U : Set α} :
    U ∈ h.filter ↔ ∃ i, p i ∧ s i ⊆ U := by
  simp only [IsBasis.filter, FilterBasis.mem_filter_iff, mem_filterBasis_iff,
    exists_exists_and_eq_and]

theorem filter_eq_generate (h : IsBasis p s) : h.filter = generate { U | ∃ i, p i ∧ s i = U } := by
  rw [IsBasis.filter, ← h.filterBasis.generate, IsBasis.filterBasis]

end IsBasis

-- TODO: consider adding `protected`?
/-- We say that a filter `l` has a basis `s : ι → Set α` bounded by `p : ι → Prop`,
if `t ∈ l` if and only if `t` includes `s i` for some `i` such that `p i`. -/
structure HasBasis (l : Filter α) (p : ι → Prop) (s : ι → Set α) : Prop where
  /-- A set `t` belongs to a filter `l` iff it includes an element of the basis. -/
  mem_iff' : ∀ t : Set α, t ∈ l ↔ ∃ i, p i ∧ s i ⊆ t

section SameType

variable {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {t : Set α} {i : ι} {p' : ι' → Prop}
  {s' : ι' → Set α} {i' : ι'}

/-- Definition of `HasBasis` unfolded with implicit set argument. -/
theorem HasBasis.mem_iff (hl : l.HasBasis p s) : t ∈ l ↔ ∃ i, p i ∧ s i ⊆ t :=
  hl.mem_iff' t

theorem HasBasis.eq_of_same_basis (hl : l.HasBasis p s) (hl' : l'.HasBasis p s) : l = l' := by
  ext t
  rw [hl.mem_iff, hl'.mem_iff]

theorem hasBasis_iff : l.HasBasis p s ↔ ∀ t, t ∈ l ↔ ∃ i, p i ∧ s i ⊆ t :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

theorem HasBasis.ex_mem (h : l.HasBasis p s) : ∃ i, p i :=
  (h.mem_iff.mp univ_mem).imp fun _ => And.left

protected theorem HasBasis.nonempty (h : l.HasBasis p s) : Nonempty ι :=
  h.ex_mem.nonempty

protected theorem IsBasis.hasBasis (h : IsBasis p s) : HasBasis h.filter p s :=
  ⟨fun t => by simp only [h.mem_filter_iff]⟩

protected theorem HasBasis.mem_of_superset (hl : l.HasBasis p s) (hi : p i) (ht : s i ⊆ t) :
    t ∈ l :=
  hl.mem_iff.2 ⟨i, hi, ht⟩

theorem HasBasis.mem_of_mem (hl : l.HasBasis p s) (hi : p i) : s i ∈ l :=
  hl.mem_of_superset hi Subset.rfl

/-- Index of a basis set such that `s i ⊆ t` as an element of `Subtype p`. -/
noncomputable def HasBasis.index (h : l.HasBasis p s) (t : Set α) (ht : t ∈ l) : { i : ι // p i } :=
  ⟨(h.mem_iff.1 ht).choose, (h.mem_iff.1 ht).choose_spec.1⟩

theorem HasBasis.property_index (h : l.HasBasis p s) (ht : t ∈ l) : p (h.index t ht) :=
  (h.index t ht).2

theorem HasBasis.set_index_mem (h : l.HasBasis p s) (ht : t ∈ l) : s (h.index t ht) ∈ l :=
  h.mem_of_mem <| h.property_index _

theorem HasBasis.set_index_subset (h : l.HasBasis p s) (ht : t ∈ l) : s (h.index t ht) ⊆ t :=
  (h.mem_iff.1 ht).choose_spec.2

theorem HasBasis.isBasis (h : l.HasBasis p s) : IsBasis p s where
  nonempty := h.ex_mem
  inter hi hj := by
    simpa only [h.mem_iff] using inter_mem (h.mem_of_mem hi) (h.mem_of_mem hj)

theorem HasBasis.filter_eq (h : l.HasBasis p s) : h.isBasis.filter = l := by
  ext U
  simp [h.mem_iff, IsBasis.mem_filter_iff]

theorem HasBasis.eq_generate (h : l.HasBasis p s) : l = generate { U | ∃ i, p i ∧ s i = U } := by
  rw [← h.isBasis.filter_eq_generate, h.filter_eq]

protected theorem _root_.FilterBasis.hasBasis (B : FilterBasis α) :
    HasBasis B.filter (fun s : Set α => s ∈ B) id :=
  ⟨fun _ => B.mem_filter_iff⟩

theorem HasBasis.to_hasBasis' (hl : l.HasBasis p s) (h : ∀ i, p i → ∃ i', p' i' ∧ s' i' ⊆ s i)
    (h' : ∀ i', p' i' → s' i' ∈ l) : l.HasBasis p' s' := by
  refine ⟨fun t => ⟨fun ht => ?_, fun ⟨i', hi', ht⟩ => mem_of_superset (h' i' hi') ht⟩⟩
  rcases hl.mem_iff.1 ht with ⟨i, hi, ht⟩
  rcases h i hi with ⟨i', hi', hs's⟩
  exact ⟨i', hi', hs's.trans ht⟩

theorem HasBasis.to_hasBasis (hl : l.HasBasis p s) (h : ∀ i, p i → ∃ i', p' i' ∧ s' i' ⊆ s i)
    (h' : ∀ i', p' i' → ∃ i, p i ∧ s i ⊆ s' i') : l.HasBasis p' s' :=
  hl.to_hasBasis' h fun i' hi' =>
    let ⟨i, hi, hss'⟩ := h' i' hi'
    hl.mem_iff.2 ⟨i, hi, hss'⟩

protected lemma HasBasis.congr (hl : l.HasBasis p s) {p' s'} (hp : ∀ i, p i ↔ p' i)
    (hs : ∀ i, p i → s i = s' i) : l.HasBasis p' s' :=
  ⟨fun t ↦ by simp only [hl.mem_iff, ← hp]; exact exists_congr fun i ↦
    and_congr_right fun hi ↦ hs i hi ▸ Iff.rfl⟩

theorem HasBasis.to_subset (hl : l.HasBasis p s) {t : ι → Set α} (h : ∀ i, p i → t i ⊆ s i)
    (ht : ∀ i, p i → t i ∈ l) : l.HasBasis p t :=
  hl.to_hasBasis' (fun i hi => ⟨i, hi, h i hi⟩) ht

theorem HasBasis.eventually_iff (hl : l.HasBasis p s) {q : α → Prop} :
    (∀ᶠ x in l, q x) ↔ ∃ i, p i ∧ ∀ ⦃x⦄, x ∈ s i → q x := by simpa using hl.mem_iff

theorem HasBasis.frequently_iff (hl : l.HasBasis p s) {q : α → Prop} :
    (∃ᶠ x in l, q x) ↔ ∀ i, p i → ∃ x ∈ s i, q x := by
  simp only [Filter.Frequently, hl.eventually_iff]; push_neg; rfl

theorem HasBasis.exists_iff (hl : l.HasBasis p s) {P : Set α → Prop}
    (mono : ∀ ⦃s t⦄, s ⊆ t → P t → P s) : (∃ s ∈ l, P s) ↔ ∃ i, p i ∧ P (s i) :=
  ⟨fun ⟨_s, hs, hP⟩ =>
    let ⟨i, hi, his⟩ := hl.mem_iff.1 hs
    ⟨i, hi, mono his hP⟩,
    fun ⟨i, hi, hP⟩ => ⟨s i, hl.mem_of_mem hi, hP⟩⟩

theorem HasBasis.forall_iff (hl : l.HasBasis p s) {P : Set α → Prop}
    (mono : ∀ ⦃s t⦄, s ⊆ t → P s → P t) : (∀ s ∈ l, P s) ↔ ∀ i, p i → P (s i) :=
  ⟨fun H i hi => H (s i) <| hl.mem_of_mem hi, fun H _s hs =>
    let ⟨i, hi, his⟩ := hl.mem_iff.1 hs
    mono his (H i hi)⟩

protected theorem HasBasis.neBot_iff (hl : l.HasBasis p s) :
    NeBot l ↔ ∀ {i}, p i → (s i).Nonempty :=
  forall_mem_nonempty_iff_neBot.symm.trans <| hl.forall_iff fun _ _ => Nonempty.mono

theorem HasBasis.eq_bot_iff (hl : l.HasBasis p s) : l = ⊥ ↔ ∃ i, p i ∧ s i = ∅ :=
  not_iff_not.1 <| neBot_iff.symm.trans <|
    hl.neBot_iff.trans <| by simp only [not_exists, not_and, nonempty_iff_ne_empty]

theorem basis_sets (l : Filter α) : l.HasBasis (fun s : Set α => s ∈ l) id :=
  ⟨fun _ => exists_mem_subset_iff.symm⟩

theorem asBasis_filter (f : Filter α) : f.asBasis.filter = f :=
  Filter.ext fun _ => exists_mem_subset_iff

theorem hasBasis_self {l : Filter α} {P : Set α → Prop} :
    HasBasis l (fun s => s ∈ l ∧ P s) id ↔ ∀ t ∈ l, ∃ r ∈ l, P r ∧ r ⊆ t := by
  simp only [hasBasis_iff, id, and_assoc]
  exact forall_congr' fun s =>
    ⟨fun h => h.1, fun h => ⟨h, fun ⟨t, hl, _, hts⟩ => mem_of_superset hl hts⟩⟩

theorem HasBasis.comp_surjective (h : l.HasBasis p s) {g : ι' → ι} (hg : Function.Surjective g) :
    l.HasBasis (p ∘ g) (s ∘ g) :=
  ⟨fun _ => h.mem_iff.trans hg.exists⟩

theorem HasBasis.comp_equiv (h : l.HasBasis p s) (e : ι' ≃ ι) : l.HasBasis (p ∘ e) (s ∘ e) :=
  h.comp_surjective e.surjective

theorem HasBasis.to_image_id' (h : l.HasBasis p s) : l.HasBasis (fun t ↦ ∃ i, p i ∧ s i = t) id :=
  ⟨fun _ ↦ by simp [h.mem_iff]⟩

theorem HasBasis.to_image_id {ι : Type*} {p : ι → Prop} {s : ι → Set α} (h : l.HasBasis p s) :
    l.HasBasis (· ∈ s '' {i | p i}) id :=
  h.to_image_id'

/-- If `{s i | p i}` is a basis of a filter `l` and each `s i` includes `s j` such that
`p j ∧ q j`, then `{s j | p j ∧ q j}` is a basis of `l`. -/
theorem HasBasis.restrict (h : l.HasBasis p s) {q : ι → Prop}
    (hq : ∀ i, p i → ∃ j, p j ∧ q j ∧ s j ⊆ s i) : l.HasBasis (fun i => p i ∧ q i) s := by
  refine ⟨fun t => ⟨fun ht => ?_, fun ⟨i, hpi, hti⟩ => h.mem_iff.2 ⟨i, hpi.1, hti⟩⟩⟩
  rcases h.mem_iff.1 ht with ⟨i, hpi, hti⟩
  rcases hq i hpi with ⟨j, hpj, hqj, hji⟩
  exact ⟨j, ⟨hpj, hqj⟩, hji.trans hti⟩

/-- If `{s i | p i}` is a basis of a filter `l` and `V ∈ l`, then `{s i | p i ∧ s i ⊆ V}`
is a basis of `l`. -/
theorem HasBasis.restrict_subset (h : l.HasBasis p s) {V : Set α} (hV : V ∈ l) :
    l.HasBasis (fun i => p i ∧ s i ⊆ V) s :=
  h.restrict fun _i hi => (h.mem_iff.1 (inter_mem hV (h.mem_of_mem hi))).imp fun _j hj =>
    ⟨hj.1, subset_inter_iff.1 hj.2⟩

theorem HasBasis.hasBasis_self_subset {p : Set α → Prop} (h : l.HasBasis (fun s => s ∈ l ∧ p s) id)
    {V : Set α} (hV : V ∈ l) : l.HasBasis (fun s => s ∈ l ∧ p s ∧ s ⊆ V) id := by
  simpa only [and_assoc] using h.restrict_subset hV

theorem HasBasis.ge_iff (hl' : l'.HasBasis p' s') : l ≤ l' ↔ ∀ i', p' i' → s' i' ∈ l :=
  ⟨fun h _i' hi' => h <| hl'.mem_of_mem hi', fun h _s hs =>
    let ⟨_i', hi', hs⟩ := hl'.mem_iff.1 hs
    mem_of_superset (h _ hi') hs⟩

theorem HasBasis.le_iff (hl : l.HasBasis p s) : l ≤ l' ↔ ∀ t ∈ l', ∃ i, p i ∧ s i ⊆ t := by
  simp only [le_def, hl.mem_iff]

theorem HasBasis.le_basis_iff (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    l ≤ l' ↔ ∀ i', p' i' → ∃ i, p i ∧ s i ⊆ s' i' := by
  simp only [hl'.ge_iff, hl.mem_iff]

theorem HasBasis.ext (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s')
    (h : ∀ i, p i → ∃ i', p' i' ∧ s' i' ⊆ s i) (h' : ∀ i', p' i' → ∃ i, p i ∧ s i ⊆ s' i') :
    l = l' := by
  apply le_antisymm
  · rw [hl.le_basis_iff hl']
    simpa using h'
  · rw [hl'.le_basis_iff hl]
    simpa using h

theorem HasBasis.inf' (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    (l ⊓ l').HasBasis (fun i : PProd ι ι' => p i.1 ∧ p' i.2) fun i => s i.1 ∩ s' i.2 :=
  ⟨by
    intro t
    constructor
    · simp only [mem_inf_iff, hl.mem_iff, hl'.mem_iff]
      rintro ⟨t, ⟨i, hi, ht⟩, t', ⟨i', hi', ht'⟩, rfl⟩
      exact ⟨⟨i, i'⟩, ⟨hi, hi'⟩, inter_subset_inter ht ht'⟩
    · rintro ⟨⟨i, i'⟩, ⟨hi, hi'⟩, H⟩
      exact mem_inf_of_inter (hl.mem_of_mem hi) (hl'.mem_of_mem hi') H⟩

theorem HasBasis.inf {ι ι' : Type*} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}
    {s' : ι' → Set α} (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    (l ⊓ l').HasBasis (fun i : ι × ι' => p i.1 ∧ p' i.2) fun i => s i.1 ∩ s' i.2 :=
  (hl.inf' hl').comp_equiv Equiv.pprodEquivProd.symm

theorem hasBasis_iInf_of_directed' {ι : Type*} {ι' : ι → Sort _} [Nonempty ι] {l : ι → Filter α}
    (s : ∀ i, ι' i → Set α) (p : ∀ i, ι' i → Prop) (hl : ∀ i, (l i).HasBasis (p i) (s i))
    (h : Directed (· ≥ ·) l) :
    (⨅ i, l i).HasBasis (fun ii' : Σ i, ι' i => p ii'.1 ii'.2) fun ii' => s ii'.1 ii'.2 := by
  refine ⟨fun t => ?_⟩
  rw [mem_iInf_of_directed h, Sigma.exists]
  exact exists_congr fun i => (hl i).mem_iff

theorem hasBasis_iInf_of_directed {ι : Type*} {ι' : Sort _} [Nonempty ι] {l : ι → Filter α}
    (s : ι → ι' → Set α) (p : ι → ι' → Prop) (hl : ∀ i, (l i).HasBasis (p i) (s i))
    (h : Directed (· ≥ ·) l) :
    (⨅ i, l i).HasBasis (fun ii' : ι × ι' => p ii'.1 ii'.2) fun ii' => s ii'.1 ii'.2 := by
  refine ⟨fun t => ?_⟩
  rw [mem_iInf_of_directed h, Prod.exists]
  exact exists_congr fun i => (hl i).mem_iff

theorem hasBasis_biInf_of_directed' {ι : Type*} {ι' : ι → Sort _} {dom : Set ι}
    (hdom : dom.Nonempty) {l : ι → Filter α} (s : ∀ i, ι' i → Set α) (p : ∀ i, ι' i → Prop)
    (hl : ∀ i ∈ dom, (l i).HasBasis (p i) (s i)) (h : DirectedOn (l ⁻¹'o GE.ge) dom) :
    (⨅ i ∈ dom, l i).HasBasis (fun ii' : Σ i, ι' i => ii'.1 ∈ dom ∧ p ii'.1 ii'.2) fun ii' =>
      s ii'.1 ii'.2 := by
  refine ⟨fun t => ?_⟩
  rw [mem_biInf_of_directed h hdom, Sigma.exists]
  refine exists_congr fun i => ⟨?_, ?_⟩
  · rintro ⟨hi, hti⟩
    rcases (hl i hi).mem_iff.mp hti with ⟨b, hb, hbt⟩
    exact ⟨b, ⟨hi, hb⟩, hbt⟩
  · rintro ⟨b, ⟨hi, hb⟩, hibt⟩
    exact ⟨hi, (hl i hi).mem_iff.mpr ⟨b, hb, hibt⟩⟩

theorem hasBasis_biInf_of_directed {ι : Type*} {ι' : Sort _} {dom : Set ι} (hdom : dom.Nonempty)
    {l : ι → Filter α} (s : ι → ι' → Set α) (p : ι → ι' → Prop)
    (hl : ∀ i ∈ dom, (l i).HasBasis (p i) (s i)) (h : DirectedOn (l ⁻¹'o GE.ge) dom) :
    (⨅ i ∈ dom, l i).HasBasis (fun ii' : ι × ι' => ii'.1 ∈ dom ∧ p ii'.1 ii'.2) fun ii' =>
      s ii'.1 ii'.2 := by
  refine ⟨fun t => ?_⟩
  rw [mem_biInf_of_directed h hdom, Prod.exists]
  refine exists_congr fun i => ⟨?_, ?_⟩
  · rintro ⟨hi, hti⟩
    rcases (hl i hi).mem_iff.mp hti with ⟨b, hb, hbt⟩
    exact ⟨b, ⟨hi, hb⟩, hbt⟩
  · rintro ⟨b, ⟨hi, hb⟩, hibt⟩
    exact ⟨hi, (hl i hi).mem_iff.mpr ⟨b, hb, hibt⟩⟩

lemma hasBasis_top :
    (⊤ : Filter α).HasBasis (fun _ : Unit ↦ True) (fun _ ↦ Set.univ) :=
  ⟨fun U => by simp⟩

theorem hasBasis_principal (t : Set α) : (𝓟 t).HasBasis (fun _ : Unit => True) fun _ => t :=
  ⟨fun U => by simp⟩

theorem hasBasis_pure (x : α) :
    (pure x : Filter α).HasBasis (fun _ : Unit => True) fun _ => {x} := by
  simp only [← principal_singleton, hasBasis_principal]

theorem HasBasis.sup' (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    (l ⊔ l').HasBasis (fun i : PProd ι ι' => p i.1 ∧ p' i.2) fun i => s i.1 ∪ s' i.2 :=
  ⟨by
    intro t
    simp_rw [mem_sup, hl.mem_iff, hl'.mem_iff, PProd.exists, union_subset_iff,
       ← exists_and_right, ← exists_and_left]
    simp only [and_assoc, and_left_comm]⟩

theorem HasBasis.sup {ι ι' : Type*} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}
    {s' : ι' → Set α} (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    (l ⊔ l').HasBasis (fun i : ι × ι' => p i.1 ∧ p' i.2) fun i => s i.1 ∪ s' i.2 :=
  (hl.sup' hl').comp_equiv Equiv.pprodEquivProd.symm

theorem hasBasis_iSup {ι : Sort*} {ι' : ι → Type*} {l : ι → Filter α} {p : ∀ i, ι' i → Prop}
    {s : ∀ i, ι' i → Set α} (hl : ∀ i, (l i).HasBasis (p i) (s i)) :
    (⨆ i, l i).HasBasis (fun f : ∀ i, ι' i => ∀ i, p i (f i)) fun f : ∀ i, ι' i => ⋃ i, s i (f i) :=
  hasBasis_iff.mpr fun t => by
    simp only [(hl _).mem_iff, Classical.skolem, forall_and, iUnion_subset_iff,
      mem_iSup]

theorem HasBasis.sup_principal (hl : l.HasBasis p s) (t : Set α) :
    (l ⊔ 𝓟 t).HasBasis p fun i => s i ∪ t :=
  ⟨fun u => by
    simp only [(hl.sup' (hasBasis_principal t)).mem_iff, PProd.exists, and_true,
      Unique.exists_iff]⟩

theorem HasBasis.sup_pure (hl : l.HasBasis p s) (x : α) :
    (l ⊔ pure x).HasBasis p fun i => s i ∪ {x} := by
  simp only [← principal_singleton, hl.sup_principal]

theorem HasBasis.inf_principal (hl : l.HasBasis p s) (s' : Set α) :
    (l ⊓ 𝓟 s').HasBasis p fun i => s i ∩ s' :=
  ⟨fun t => by
    simp only [mem_inf_principal, hl.mem_iff, subset_def, mem_setOf_eq, mem_inter_iff, and_imp]⟩

theorem HasBasis.principal_inf (hl : l.HasBasis p s) (s' : Set α) :
    (𝓟 s' ⊓ l).HasBasis p fun i => s' ∩ s i := by
  simpa only [inf_comm, inter_comm] using hl.inf_principal s'

theorem HasBasis.inf_basis_neBot_iff (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    NeBot (l ⊓ l') ↔ ∀ ⦃i⦄, p i → ∀ ⦃i'⦄, p' i' → (s i ∩ s' i').Nonempty :=
  (hl.inf' hl').neBot_iff.trans <| by simp [@forall_swap _ ι']

theorem HasBasis.inf_neBot_iff (hl : l.HasBasis p s) :
    NeBot (l ⊓ l') ↔ ∀ ⦃i⦄, p i → ∀ ⦃s'⦄, s' ∈ l' → (s i ∩ s').Nonempty :=
  hl.inf_basis_neBot_iff l'.basis_sets

theorem HasBasis.inf_principal_neBot_iff (hl : l.HasBasis p s) {t : Set α} :
    NeBot (l ⊓ 𝓟 t) ↔ ∀ ⦃i⦄, p i → (s i ∩ t).Nonempty :=
  (hl.inf_principal t).neBot_iff

theorem HasBasis.disjoint_iff (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    Disjoint l l' ↔ ∃ i, p i ∧ ∃ i', p' i' ∧ Disjoint (s i) (s' i') :=
  not_iff_not.mp <| by simp only [_root_.disjoint_iff, ← Ne.eq_def, ← neBot_iff, inf_eq_inter,
    hl.inf_basis_neBot_iff hl', not_exists, not_and, bot_eq_empty, ← nonempty_iff_ne_empty]

theorem _root_.Disjoint.exists_mem_filter_basis (h : Disjoint l l') (hl : l.HasBasis p s)
    (hl' : l'.HasBasis p' s') : ∃ i, p i ∧ ∃ i', p' i' ∧ Disjoint (s i) (s' i') :=
  (hl.disjoint_iff hl').1 h

theorem inf_neBot_iff :
    NeBot (l ⊓ l') ↔ ∀ ⦃s : Set α⦄, s ∈ l → ∀ ⦃s'⦄, s' ∈ l' → (s ∩ s').Nonempty :=
  l.basis_sets.inf_neBot_iff

theorem inf_principal_neBot_iff {s : Set α} : NeBot (l ⊓ 𝓟 s) ↔ ∀ U ∈ l, (U ∩ s).Nonempty :=
  l.basis_sets.inf_principal_neBot_iff

theorem mem_iff_inf_principal_compl {f : Filter α} {s : Set α} : s ∈ f ↔ f ⊓ 𝓟 sᶜ = ⊥ := by
  refine not_iff_not.1 ((inf_principal_neBot_iff.trans ?_).symm.trans neBot_iff)
  exact
    ⟨fun h hs => by simpa [Set.not_nonempty_empty] using h s hs, fun hs t ht =>
      inter_compl_nonempty_iff.2 fun hts => hs <| mem_of_superset ht hts⟩

theorem notMem_iff_inf_principal_compl {f : Filter α} {s : Set α} : s ∉ f ↔ NeBot (f ⊓ 𝓟 sᶜ) :=
  (not_congr mem_iff_inf_principal_compl).trans neBot_iff.symm

@[deprecated (since := "2025-05-23")]
alias not_mem_iff_inf_principal_compl := notMem_iff_inf_principal_compl

@[simp]
theorem disjoint_principal_right {f : Filter α} {s : Set α} : Disjoint f (𝓟 s) ↔ sᶜ ∈ f := by
  rw [mem_iff_inf_principal_compl, compl_compl, disjoint_iff]

@[simp]
theorem disjoint_principal_left {f : Filter α} {s : Set α} : Disjoint (𝓟 s) f ↔ sᶜ ∈ f := by
  rw [disjoint_comm, disjoint_principal_right]

@[simp 1100] -- Porting note: higher priority for linter
theorem disjoint_principal_principal {s t : Set α} : Disjoint (𝓟 s) (𝓟 t) ↔ Disjoint s t := by
  rw [← subset_compl_iff_disjoint_left, disjoint_principal_left, mem_principal]

alias ⟨_, _root_.Disjoint.filter_principal⟩ := disjoint_principal_principal

@[simp]
theorem disjoint_pure_pure {x y : α} : Disjoint (pure x : Filter α) (pure y) ↔ x ≠ y := by
  simp only [← principal_singleton, disjoint_principal_principal, disjoint_singleton]

theorem HasBasis.disjoint_iff_left (h : l.HasBasis p s) :
    Disjoint l l' ↔ ∃ i, p i ∧ (s i)ᶜ ∈ l' := by
  simp only [h.disjoint_iff l'.basis_sets, id, ← disjoint_principal_left,
    (hasBasis_principal _).disjoint_iff l'.basis_sets, true_and, Unique.exists_iff]

theorem HasBasis.disjoint_iff_right (h : l.HasBasis p s) :
    Disjoint l' l ↔ ∃ i, p i ∧ (s i)ᶜ ∈ l' :=
  disjoint_comm.trans h.disjoint_iff_left

theorem le_iff_forall_inf_principal_compl {f g : Filter α} : f ≤ g ↔ ∀ V ∈ g, f ⊓ 𝓟 Vᶜ = ⊥ :=
  forall₂_congr fun _ _ => mem_iff_inf_principal_compl

theorem inf_neBot_iff_frequently_left {f g : Filter α} :
    NeBot (f ⊓ g) ↔ ∀ {p : α → Prop}, (∀ᶠ x in f, p x) → ∃ᶠ x in g, p x := by
  simp only [inf_neBot_iff, frequently_iff, and_comm]; rfl

theorem inf_neBot_iff_frequently_right {f g : Filter α} :
    NeBot (f ⊓ g) ↔ ∀ {p : α → Prop}, (∀ᶠ x in g, p x) → ∃ᶠ x in f, p x := by
  rw [inf_comm]
  exact inf_neBot_iff_frequently_left

theorem HasBasis.eq_biInf (h : l.HasBasis p s) : l = ⨅ (i) (_ : p i), 𝓟 (s i) :=
  eq_biInf_of_mem_iff_exists_mem fun {_} => by simp only [h.mem_iff, mem_principal]

theorem HasBasis.eq_iInf (h : l.HasBasis (fun _ => True) s) : l = ⨅ i, 𝓟 (s i) := by
  simpa only [iInf_true] using h.eq_biInf

theorem hasBasis_iInf_principal {s : ι → Set α} (h : Directed (· ≥ ·) s) [Nonempty ι] :
    (⨅ i, 𝓟 (s i)).HasBasis (fun _ => True) s :=
  ⟨fun t => by
    simpa only [true_and] using mem_iInf_of_directed (h.mono_comp _ monotone_principal.dual) t⟩

theorem hasBasis_biInf_principal {s : β → Set α} {S : Set β} (h : DirectedOn (s ⁻¹'o (· ≥ ·)) S)
    (ne : S.Nonempty) : (⨅ i ∈ S, 𝓟 (s i)).HasBasis (fun i => i ∈ S) s :=
  ⟨fun t => by
    refine mem_biInf_of_directed ?_ ne
    rw [directedOn_iff_directed, ← directed_comp] at h ⊢
    refine h.mono_comp _ ?_
    exact fun _ _ => principal_mono.2⟩

theorem hasBasis_biInf_principal' {ι : Type*} {p : ι → Prop} {s : ι → Set α}
    (h : ∀ i, p i → ∀ j, p j → ∃ k, p k ∧ s k ⊆ s i ∧ s k ⊆ s j) (ne : ∃ i, p i) :
    (⨅ (i) (_ : p i), 𝓟 (s i)).HasBasis p s :=
  Filter.hasBasis_biInf_principal h ne

theorem HasBasis.map (f : α → β) (hl : l.HasBasis p s) : (l.map f).HasBasis p fun i => f '' s i :=
  ⟨fun t => by simp only [mem_map, image_subset_iff, hl.mem_iff, preimage]⟩

theorem HasBasis.comap (f : β → α) (hl : l.HasBasis p s) :
    (l.comap f).HasBasis p fun i => f ⁻¹' s i :=
  ⟨fun t => by
    simp only [mem_comap', hl.mem_iff]
    refine exists_congr (fun i => Iff.rfl.and ?_)
    exact ⟨fun h x hx => h hx rfl, fun h y hy x hx => h <| by rwa [mem_preimage, hx]⟩⟩

theorem comap_hasBasis (f : α → β) (l : Filter β) :
    HasBasis (comap f l) (fun s : Set β => s ∈ l) fun s => f ⁻¹' s :=
  ⟨fun _ => mem_comap⟩

theorem HasBasis.forall_mem_mem (h : HasBasis l p s) {x : α} :
    (∀ t ∈ l, x ∈ t) ↔ ∀ i, p i → x ∈ s i := by
  simp only [h.mem_iff, exists_imp, and_imp]
  exact ⟨fun h i hi => h (s i) i hi Subset.rfl, fun h t i hi ht => ht (h i hi)⟩

protected theorem HasBasis.biInf_mem [CompleteLattice β] {f : Set α → β} (h : HasBasis l p s)
    (hf : Monotone f) : ⨅ t ∈ l, f t = ⨅ (i) (_ : p i), f (s i) :=
  le_antisymm (le_iInf₂ fun i hi => iInf₂_le (s i) (h.mem_of_mem hi)) <|
    le_iInf₂ fun _t ht =>
      let ⟨i, hpi, hi⟩ := h.mem_iff.1 ht
      iInf₂_le_of_le i hpi (hf hi)

protected theorem HasBasis.biInter_mem {f : Set α → Set β} (h : HasBasis l p s) (hf : Monotone f) :
    ⋂ t ∈ l, f t = ⋂ (i) (_ : p i), f (s i) :=
  h.biInf_mem hf

protected theorem HasBasis.ker (h : HasBasis l p s) : l.ker = ⋂ (i) (_ : p i), s i :=
  sInter_eq_biInter.trans <| h.biInter_mem monotone_id

variable {ι'' : Type*} [Preorder ι''] (l) (s'' : ι'' → Set α)

/-- `IsAntitoneBasis s` means the image of `s` is a filter basis such that `s` is decreasing. -/
structure IsAntitoneBasis : Prop extends IsBasis (fun _ => True) s'' where
  /-- The sequence of sets is antitone. -/
  protected antitone : Antitone s''

/-- We say that a filter `l` has an antitone basis `s : ι → Set α`, if `t ∈ l` if and only if `t`
includes `s i` for some `i`, and `s` is decreasing. -/
structure HasAntitoneBasis (l : Filter α) (s : ι'' → Set α) : Prop
    extends HasBasis l (fun _ => True) s where
  /-- The sequence of sets is antitone. -/
  protected antitone : Antitone s

protected theorem HasAntitoneBasis.map {l : Filter α} {s : ι'' → Set α}
    (hf : HasAntitoneBasis l s) (m : α → β) : HasAntitoneBasis (map m l) (m '' s ·) :=
  ⟨HasBasis.map _ hf.toHasBasis, fun _ _ h => image_mono <| hf.2 h⟩

protected theorem HasAntitoneBasis.comap {l : Filter α} {s : ι'' → Set α}
    (hf : HasAntitoneBasis l s) (m : β → α) : HasAntitoneBasis (comap m l) (m ⁻¹' s ·) :=
  ⟨hf.1.comap _, fun _ _ h ↦ preimage_mono (hf.2 h)⟩

lemma HasAntitoneBasis.iInf_principal {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {s : ι → Set α} (hs : Antitone s) : (⨅ i, 𝓟 (s i)).HasAntitoneBasis s :=
  ⟨hasBasis_iInf_principal hs.directed_ge, hs⟩

end SameType

section TwoTypes

variable {la : Filter α} {pa : ι → Prop} {sa : ι → Set α} {lb : Filter β} {pb : ι' → Prop}
  {sb : ι' → Set β} {f : α → β}

theorem HasBasis.tendsto_left_iff (hla : la.HasBasis pa sa) :
    Tendsto f la lb ↔ ∀ t ∈ lb, ∃ i, pa i ∧ MapsTo f (sa i) t := by
  simp only [Tendsto, (hla.map f).le_iff, image_subset_iff]
  rfl

theorem HasBasis.tendsto_right_iff (hlb : lb.HasBasis pb sb) :
    Tendsto f la lb ↔ ∀ i, pb i → ∀ᶠ x in la, f x ∈ sb i := by
  simp only [Tendsto, hlb.ge_iff, mem_map', Filter.Eventually]

theorem HasBasis.tendsto_iff (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    Tendsto f la lb ↔ ∀ ib, pb ib → ∃ ia, pa ia ∧ ∀ x ∈ sa ia, f x ∈ sb ib := by
  simp [hlb.tendsto_right_iff, hla.eventually_iff]

theorem Tendsto.basis_left (H : Tendsto f la lb) (hla : la.HasBasis pa sa) :
    ∀ t ∈ lb, ∃ i, pa i ∧ MapsTo f (sa i) t :=
  hla.tendsto_left_iff.1 H

theorem Tendsto.basis_right (H : Tendsto f la lb) (hlb : lb.HasBasis pb sb) :
    ∀ i, pb i → ∀ᶠ x in la, f x ∈ sb i :=
  hlb.tendsto_right_iff.1 H

theorem Tendsto.basis_both (H : Tendsto f la lb) (hla : la.HasBasis pa sa)
    (hlb : lb.HasBasis pb sb) :
    ∀ ib, pb ib → ∃ ia, pa ia ∧ MapsTo f (sa ia) (sb ib) :=
  (hla.tendsto_iff hlb).1 H

theorem HasBasis.prod_pprod (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    (la ×ˢ lb).HasBasis (fun i : PProd ι ι' => pa i.1 ∧ pb i.2) fun i => sa i.1 ×ˢ sb i.2 :=
  (hla.comap Prod.fst).inf' (hlb.comap Prod.snd)

theorem HasBasis.prod {ι ι' : Type*} {pa : ι → Prop} {sa : ι → Set α} {pb : ι' → Prop}
    {sb : ι' → Set β} (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    (la ×ˢ lb).HasBasis (fun i : ι × ι' => pa i.1 ∧ pb i.2) fun i => sa i.1 ×ˢ sb i.2 :=
  (hla.comap Prod.fst).inf (hlb.comap Prod.snd)

protected theorem HasBasis.principal_prod (sa : Set α) (h : lb.HasBasis pb sb) :
    (𝓟 sa ×ˢ lb).HasBasis pb (sa ×ˢ sb ·) := by
  simpa only [prod_eq_inf, comap_principal, prod_eq] using (h.comap Prod.snd).principal_inf _

protected theorem HasBasis.prod_principal (h : la.HasBasis pa sa) (sb : Set β) :
    (la ×ˢ 𝓟 sb).HasBasis pa (sa · ×ˢ sb) := by
  simpa only [prod_eq_inf, comap_principal, prod_eq] using (h.comap Prod.fst).inf_principal _

protected theorem HasBasis.top_prod (h : lb.HasBasis pb sb) :
    (⊤ ×ˢ lb : Filter (α × β)).HasBasis pb (univ ×ˢ sb ·) := by
  simpa only [principal_univ] using h.principal_prod univ

protected theorem HasBasis.prod_top (h : la.HasBasis pa sa) :
    (la ×ˢ ⊤ : Filter (α × β)).HasBasis pa (sa · ×ˢ univ) := by
  simpa only [principal_univ] using h.prod_principal univ

theorem HasBasis.prod_same_index {p : ι → Prop} {sb : ι → Set β} (hla : la.HasBasis p sa)
    (hlb : lb.HasBasis p sb) (h_dir : ∀ {i j}, p i → p j → ∃ k, p k ∧ sa k ⊆ sa i ∧ sb k ⊆ sb j) :
    (la ×ˢ lb).HasBasis p fun i => sa i ×ˢ sb i := by
  simp only [hasBasis_iff, (hla.prod_pprod hlb).mem_iff]
  refine fun t => ⟨?_, ?_⟩
  · rintro ⟨⟨i, j⟩, ⟨hi, hj⟩, hsub : sa i ×ˢ sb j ⊆ t⟩
    rcases h_dir hi hj with ⟨k, hk, ki, kj⟩
    exact ⟨k, hk, (Set.prod_mono ki kj).trans hsub⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨⟨i, i⟩, ⟨hi, hi⟩, h⟩

theorem HasBasis.prod_same_index_mono {ι : Type*} [LinearOrder ι] {p : ι → Prop} {sa : ι → Set α}
    {sb : ι → Set β} (hla : la.HasBasis p sa) (hlb : lb.HasBasis p sb)
    (hsa : MonotoneOn sa { i | p i }) (hsb : MonotoneOn sb { i | p i }) :
    (la ×ˢ lb).HasBasis p fun i => sa i ×ˢ sb i :=
  hla.prod_same_index hlb fun {i j} hi hj =>
    have : p (min i j) := min_rec' _ hi hj
    ⟨min i j, this, hsa this hi <| min_le_left _ _, hsb this hj <| min_le_right _ _⟩

theorem HasBasis.prod_same_index_anti {ι : Type*} [LinearOrder ι] {p : ι → Prop} {sa : ι → Set α}
    {sb : ι → Set β} (hla : la.HasBasis p sa) (hlb : lb.HasBasis p sb)
    (hsa : AntitoneOn sa { i | p i }) (hsb : AntitoneOn sb { i | p i }) :
    (la ×ˢ lb).HasBasis p fun i => sa i ×ˢ sb i :=
  @HasBasis.prod_same_index_mono _ _ _ _ ιᵒᵈ _ _ _ _ hla hlb hsa.dual_left hsb.dual_left

theorem HasBasis.prod_self (hl : la.HasBasis pa sa) :
    (la ×ˢ la).HasBasis pa fun i => sa i ×ˢ sa i :=
  hl.prod_same_index hl fun {i j} hi hj => by
    simpa only [exists_prop, subset_inter_iff] using
      hl.mem_iff.1 (inter_mem (hl.mem_of_mem hi) (hl.mem_of_mem hj))

theorem mem_prod_self_iff {s} : s ∈ la ×ˢ la ↔ ∃ t ∈ la, t ×ˢ t ⊆ s :=
  la.basis_sets.prod_self.mem_iff

lemma eventually_prod_self_iff {r : α → α → Prop} :
    (∀ᶠ x in la ×ˢ la, r x.1 x.2) ↔ ∃ t ∈ la, ∀ x ∈ t, ∀ y ∈ t, r x y :=
  mem_prod_self_iff.trans <| by simp only [prod_subset_iff, mem_setOf_eq]

/-- A version of `eventually_prod_self_iff` that is more suitable for forward rewriting. -/
lemma eventually_prod_self_iff' {r : α × α → Prop} :
    (∀ᶠ x in la ×ˢ la, r x) ↔ ∃ t ∈ la, ∀ x ∈ t, ∀ y ∈ t, r (x, y) :=
  Iff.symm eventually_prod_self_iff.symm

theorem HasAntitoneBasis.prod {ι : Type*} [LinearOrder ι] {f : Filter α} {g : Filter β}
    {s : ι → Set α} {t : ι → Set β} (hf : HasAntitoneBasis f s) (hg : HasAntitoneBasis g t) :
    HasAntitoneBasis (f ×ˢ g) fun n => s n ×ˢ t n :=
  ⟨hf.1.prod_same_index_anti hg.1 (hf.2.antitoneOn _) (hg.2.antitoneOn _), hf.2.set_prod hg.2⟩

theorem HasBasis.coprod {ι ι' : Type*} {pa : ι → Prop} {sa : ι → Set α} {pb : ι' → Prop}
    {sb : ι' → Set β} (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    (la.coprod lb).HasBasis (fun i : ι × ι' => pa i.1 ∧ pb i.2) fun i =>
      Prod.fst ⁻¹' sa i.1 ∪ Prod.snd ⁻¹' sb i.2 :=
  (hla.comap Prod.fst).sup (hlb.comap Prod.snd)

end TwoTypes

theorem map_sigma_mk_comap {π : α → Type*} {π' : β → Type*} {f : α → β}
    (hf : Function.Injective f) (g : ∀ a, π a → π' (f a)) (a : α) (l : Filter (π' (f a))) :
    map (Sigma.mk a) (comap (g a) l) = comap (Sigma.map f g) (map (Sigma.mk (f a)) l) := by
  refine (((basis_sets _).comap _).map _).eq_of_same_basis ?_
  convert ((basis_sets l).map (Sigma.mk (f a))).comap (Sigma.map f g)
  apply image_sigmaMk_preimage_sigmaMap hf

end Filter
