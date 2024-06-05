/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.Data.Prod.PProd
import Mathlib.Data.Set.Countable
import Mathlib.Order.Filter.Prod
import Mathlib.Order.Filter.Ker

#align_import order.filter.bases from "leanprover-community/mathlib"@"996b0ff959da753a555053a480f36e5f264d4207"

/-!
# Filter bases

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

This file also introduces more restricted classes of bases, involving monotonicity or
countability. In particular, for `l : Filter α`, `l.IsCountablyGenerated` means
there is a countable set of sets which generates `s`. This is reformulated in term of bases,
and consequences are derived.

## Main statements

* `Filter.HasBasis.mem_iff`, `HasBasis.mem_of_superset`, `HasBasis.mem_of_mem` : restate `t ∈ f` in
  terms of a basis;

* `Filter.basis_sets` : all sets of a filter form a basis;

* `Filter.HasBasis.inf`, `Filter.HasBasis.inf_principal`, `Filter.HasBasis.prod`,
  `Filter.HasBasis.prod_self`, `Filter.HasBasis.map`, `Filter.HasBasis.comap` : combinators to
  construct filters of `l ⊓ l'`, `l ⊓ 𝓟 t`, `l ×ˢ l'`, `l ×ˢ l`, `l.map f`, `l.comap f`
  respectively;

* `Filter.HasBasis.le_iff`, `Filter.HasBasis.ge_iff`, `Filter.HasBasis.le_basis_iff` : restate
  `l ≤ l'` in terms of bases.

* `Filter.HasBasis.tendsto_right_iff`, `Filter.HasBasis.tendsto_left_iff`,
  `Filter.HasBasis.tendsto_iff` : restate `Tendsto f l l'` in terms of bases.

* `isCountablyGenerated_iff_exists_antitone_basis` : proves a filter is countably generated if and
  only if it admits a basis parametrized by a decreasing sequence of sets indexed by `ℕ`.

* `tendsto_iff_seq_tendsto` : an abstract version of "sequentially continuous implies continuous".

## Implementation notes

As with `Set.iUnion`/`biUnion`/`Set.sUnion`, there are three different approaches to filter bases:

* `Filter.HasBasis l s`, `s : Set (Set α)`;
* `Filter.HasBasis l s`, `s : ι → Set α`;
* `Filter.HasBasis l p s`, `p : ι → Prop`, `s : ι → Set α`.

We use the latter one because, e.g., `𝓝 x` in an `EMetricSpace` or in a `MetricSpace` has a basis
of this form. The other two can be emulated using `s = id` or `p = fun _ ↦ True`.

With this approach sometimes one needs to `simp` the statement provided by the `Filter.HasBasis`
machinery, e.g., `simp only [true_and]` or `simp only [forall_const]` can help with the case
`p = fun _ ↦ True`.
-/

set_option autoImplicit true


open Set Filter

open scoped Classical
open Filter

section sort

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
#align filter_basis FilterBasis

instance FilterBasis.nonempty_sets (B : FilterBasis α) : Nonempty B.sets :=
  B.nonempty.to_subtype
#align filter_basis.nonempty_sets FilterBasis.nonempty_sets

-- Porting note: this instance was reducible but it doesn't work the same way in Lean 4
/-- If `B` is a filter basis on `α`, and `U` a subset of `α` then we can write `U ∈ B` as
on paper. -/
instance {α : Type*} : Membership (Set α) (FilterBasis α) :=
  ⟨fun U B => U ∈ B.sets⟩

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
#align filter.as_basis Filter.asBasis

-- Porting note: was `protected` in Lean 3 but `protected` didn't work; removed
/-- `is_basis p s` means the image of `s` bounded by `p` is a filter basis. -/
structure Filter.IsBasis (p : ι → Prop) (s : ι → Set α) : Prop where
  /-- There exists at least one `i` that satisfies `p`. -/
  nonempty : ∃ i, p i
  /-- `s` is directed downwards on `i` such that `p i`. -/
  inter : ∀ {i j}, p i → p j → ∃ k, p k ∧ s k ⊆ s i ∩ s j
#align filter.is_basis Filter.IsBasis

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
#align filter.is_basis.filter_basis Filter.IsBasis.filterBasis

variable {p : ι → Prop} {s : ι → Set α} (h : IsBasis p s)

theorem mem_filterBasis_iff {U : Set α} : U ∈ h.filterBasis ↔ ∃ i, p i ∧ s i = U :=
  Iff.rfl
#align filter.is_basis.mem_filter_basis_iff Filter.IsBasis.mem_filterBasis_iff

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
#align filter_basis.filter FilterBasis.filter

theorem mem_filter_iff (B : FilterBasis α) {U : Set α} : U ∈ B.filter ↔ ∃ s ∈ B, s ⊆ U :=
  Iff.rfl
#align filter_basis.mem_filter_iff FilterBasis.mem_filter_iff

theorem mem_filter_of_mem (B : FilterBasis α) {U : Set α} : U ∈ B → U ∈ B.filter := fun U_in =>
  ⟨U, U_in, Subset.refl _⟩
#align filter_basis.mem_filter_of_mem FilterBasis.mem_filter_of_mem

theorem eq_iInf_principal (B : FilterBasis α) : B.filter = ⨅ s : B.sets, 𝓟 s := by
  have : Directed (· ≥ ·) fun s : B.sets => 𝓟 (s : Set α) := by
    rintro ⟨U, U_in⟩ ⟨V, V_in⟩
    rcases B.inter_sets U_in V_in with ⟨W, W_in, W_sub⟩
    use ⟨W, W_in⟩
    simp only [ge_iff_le, le_principal_iff, mem_principal, Subtype.coe_mk]
    exact subset_inter_iff.mp W_sub
  ext U
  simp [mem_filter_iff, mem_iInf_of_directed this]
#align filter_basis.eq_infi_principal FilterBasis.eq_iInf_principal

protected theorem generate (B : FilterBasis α) : generate B.sets = B.filter := by
  apply le_antisymm
  · intro U U_in
    rcases B.mem_filter_iff.mp U_in with ⟨V, V_in, h⟩
    exact GenerateSets.superset (GenerateSets.basic V_in) h
  · rw [le_generate_iff]
    apply mem_filter_of_mem
#align filter_basis.generate FilterBasis.generate

end FilterBasis

namespace Filter

namespace IsBasis

variable {p : ι → Prop} {s : ι → Set α}

/-- Constructs a filter from an indexed family of sets satisfying `IsBasis`. -/
protected def filter (h : IsBasis p s) : Filter α :=
  h.filterBasis.filter
#align filter.is_basis.filter Filter.IsBasis.filter

protected theorem mem_filter_iff (h : IsBasis p s) {U : Set α} :
    U ∈ h.filter ↔ ∃ i, p i ∧ s i ⊆ U := by
  simp only [IsBasis.filter, FilterBasis.mem_filter_iff, mem_filterBasis_iff,
    exists_exists_and_eq_and]
#align filter.is_basis.mem_filter_iff Filter.IsBasis.mem_filter_iff

theorem filter_eq_generate (h : IsBasis p s) : h.filter = generate { U | ∃ i, p i ∧ s i = U } := by
  erw [h.filterBasis.generate]; rfl
#align filter.is_basis.filter_eq_generate Filter.IsBasis.filter_eq_generate

end IsBasis

-- Porting note: was `protected` in Lean 3 but `protected` didn't work; removed
/-- We say that a filter `l` has a basis `s : ι → Set α` bounded by `p : ι → Prop`,
if `t ∈ l` if and only if `t` includes `s i` for some `i` such that `p i`. -/
structure HasBasis (l : Filter α) (p : ι → Prop) (s : ι → Set α) : Prop where
  /-- A set `t` belongs to a filter `l` iff it includes an element of the basis. -/
  mem_iff' : ∀ t : Set α, t ∈ l ↔ ∃ i, p i ∧ s i ⊆ t
#align filter.has_basis Filter.HasBasis

section SameType

variable {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {t : Set α} {i : ι} {p' : ι' → Prop}
  {s' : ι' → Set α} {i' : ι'}

theorem hasBasis_generate (s : Set (Set α)) :
    (generate s).HasBasis (fun t => Set.Finite t ∧ t ⊆ s) fun t => ⋂₀ t :=
  ⟨fun U => by simp only [mem_generate_iff, exists_prop, and_assoc, and_left_comm]⟩
#align filter.has_basis_generate Filter.hasBasis_generate

/-- The smallest filter basis containing a given collection of sets. -/
def FilterBasis.ofSets (s : Set (Set α)) : FilterBasis α where
  sets := sInter '' { t | Set.Finite t ∧ t ⊆ s }
  nonempty := ⟨univ, ∅, ⟨⟨finite_empty, empty_subset s⟩, sInter_empty⟩⟩
  inter_sets := by
    rintro _ _ ⟨a, ⟨fina, suba⟩, rfl⟩ ⟨b, ⟨finb, subb⟩, rfl⟩
    exact ⟨⋂₀ (a ∪ b), mem_image_of_mem _ ⟨fina.union finb, union_subset suba subb⟩,
        (sInter_union _ _).subset⟩
#align filter.filter_basis.of_sets Filter.FilterBasis.ofSets

lemma FilterBasis.ofSets_sets (s : Set (Set α)) :
    (FilterBasis.ofSets s).sets = sInter '' { t | Set.Finite t ∧ t ⊆ s } :=
  rfl

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
/-- Definition of `HasBasis` unfolded with implicit set argument. -/
theorem HasBasis.mem_iff (hl : l.HasBasis p s) : t ∈ l ↔ ∃ i, p i ∧ s i ⊆ t :=
  hl.mem_iff' t
#align filter.has_basis.mem_iff Filter.HasBasis.mem_iffₓ

theorem HasBasis.eq_of_same_basis (hl : l.HasBasis p s) (hl' : l'.HasBasis p s) : l = l' := by
  ext t
  rw [hl.mem_iff, hl'.mem_iff]
#align filter.has_basis.eq_of_same_basis Filter.HasBasis.eq_of_same_basis

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
theorem hasBasis_iff : l.HasBasis p s ↔ ∀ t, t ∈ l ↔ ∃ i, p i ∧ s i ⊆ t :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩
#align filter.has_basis_iff Filter.hasBasis_iffₓ

theorem HasBasis.ex_mem (h : l.HasBasis p s) : ∃ i, p i :=
  (h.mem_iff.mp univ_mem).imp fun _ => And.left
#align filter.has_basis.ex_mem Filter.HasBasis.ex_mem

protected theorem HasBasis.nonempty (h : l.HasBasis p s) : Nonempty ι :=
  nonempty_of_exists h.ex_mem
#align filter.has_basis.nonempty Filter.HasBasis.nonempty

protected theorem IsBasis.hasBasis (h : IsBasis p s) : HasBasis h.filter p s :=
  ⟨fun t => by simp only [h.mem_filter_iff, exists_prop]⟩
#align filter.is_basis.has_basis Filter.IsBasis.hasBasis

protected theorem HasBasis.mem_of_superset (hl : l.HasBasis p s) (hi : p i) (ht : s i ⊆ t) :
    t ∈ l :=
  hl.mem_iff.2 ⟨i, hi, ht⟩
#align filter.has_basis.mem_of_superset Filter.HasBasis.mem_of_superset

theorem HasBasis.mem_of_mem (hl : l.HasBasis p s) (hi : p i) : s i ∈ l :=
  hl.mem_of_superset hi Subset.rfl
#align filter.has_basis.mem_of_mem Filter.HasBasis.mem_of_mem

/-- Index of a basis set such that `s i ⊆ t` as an element of `Subtype p`. -/
noncomputable def HasBasis.index (h : l.HasBasis p s) (t : Set α) (ht : t ∈ l) : { i : ι // p i } :=
  ⟨(h.mem_iff.1 ht).choose, (h.mem_iff.1 ht).choose_spec.1⟩
#align filter.has_basis.index Filter.HasBasis.index

theorem HasBasis.property_index (h : l.HasBasis p s) (ht : t ∈ l) : p (h.index t ht) :=
  (h.index t ht).2
#align filter.has_basis.property_index Filter.HasBasis.property_index

theorem HasBasis.set_index_mem (h : l.HasBasis p s) (ht : t ∈ l) : s (h.index t ht) ∈ l :=
  h.mem_of_mem <| h.property_index _
#align filter.has_basis.set_index_mem Filter.HasBasis.set_index_mem

theorem HasBasis.set_index_subset (h : l.HasBasis p s) (ht : t ∈ l) : s (h.index t ht) ⊆ t :=
  (h.mem_iff.1 ht).choose_spec.2
#align filter.has_basis.set_index_subset Filter.HasBasis.set_index_subset

theorem HasBasis.isBasis (h : l.HasBasis p s) : IsBasis p s where
  nonempty := h.ex_mem
  inter hi hj := by
    simpa only [h.mem_iff] using inter_mem (h.mem_of_mem hi) (h.mem_of_mem hj)
#align filter.has_basis.is_basis Filter.HasBasis.isBasis

theorem HasBasis.filter_eq (h : l.HasBasis p s) : h.isBasis.filter = l := by
  ext U
  simp [h.mem_iff, IsBasis.mem_filter_iff]
#align filter.has_basis.filter_eq Filter.HasBasis.filter_eq

theorem HasBasis.eq_generate (h : l.HasBasis p s) : l = generate { U | ∃ i, p i ∧ s i = U } := by
  rw [← h.isBasis.filter_eq_generate, h.filter_eq]
#align filter.has_basis.eq_generate Filter.HasBasis.eq_generate

theorem generate_eq_generate_inter (s : Set (Set α)) :
    generate s = generate (sInter '' { t | Set.Finite t ∧ t ⊆ s }) := by
  rw [← FilterBasis.ofSets_sets, FilterBasis.generate, ← (hasBasis_generate s).filter_eq]; rfl
#align filter.generate_eq_generate_inter Filter.generate_eq_generate_inter

theorem ofSets_filter_eq_generate (s : Set (Set α)) :
    (FilterBasis.ofSets s).filter = generate s := by
  rw [← (FilterBasis.ofSets s).generate, FilterBasis.ofSets_sets, ← generate_eq_generate_inter]
#align filter.of_sets_filter_eq_generate Filter.ofSets_filter_eq_generate

protected theorem _root_.FilterBasis.hasBasis (B : FilterBasis α) :
    HasBasis B.filter (fun s : Set α => s ∈ B) id :=
  ⟨fun _ => B.mem_filter_iff⟩
#align filter_basis.has_basis FilterBasis.hasBasis

theorem HasBasis.to_hasBasis' (hl : l.HasBasis p s) (h : ∀ i, p i → ∃ i', p' i' ∧ s' i' ⊆ s i)
    (h' : ∀ i', p' i' → s' i' ∈ l) : l.HasBasis p' s' := by
  refine ⟨fun t => ⟨fun ht => ?_, fun ⟨i', hi', ht⟩ => mem_of_superset (h' i' hi') ht⟩⟩
  rcases hl.mem_iff.1 ht with ⟨i, hi, ht⟩
  rcases h i hi with ⟨i', hi', hs's⟩
  exact ⟨i', hi', hs's.trans ht⟩
#align filter.has_basis.to_has_basis' Filter.HasBasis.to_hasBasis'

theorem HasBasis.to_hasBasis (hl : l.HasBasis p s) (h : ∀ i, p i → ∃ i', p' i' ∧ s' i' ⊆ s i)
    (h' : ∀ i', p' i' → ∃ i, p i ∧ s i ⊆ s' i') : l.HasBasis p' s' :=
  hl.to_hasBasis' h fun i' hi' =>
    let ⟨i, hi, hss'⟩ := h' i' hi'
    hl.mem_iff.2 ⟨i, hi, hss'⟩
#align filter.has_basis.to_has_basis Filter.HasBasis.to_hasBasis

protected lemma HasBasis.congr (hl : l.HasBasis p s) {p' s'} (hp : ∀ i, p i ↔ p' i)
    (hs : ∀ i, p i → s i = s' i) : l.HasBasis p' s' :=
  ⟨fun t ↦ by simp only [hl.mem_iff, ← hp]; exact exists_congr fun i ↦
    and_congr_right fun hi ↦ hs i hi ▸ Iff.rfl⟩

theorem HasBasis.to_subset (hl : l.HasBasis p s) {t : ι → Set α} (h : ∀ i, p i → t i ⊆ s i)
    (ht : ∀ i, p i → t i ∈ l) : l.HasBasis p t :=
  hl.to_hasBasis' (fun i hi => ⟨i, hi, h i hi⟩) ht
#align filter.has_basis.to_subset Filter.HasBasis.to_subset

theorem HasBasis.eventually_iff (hl : l.HasBasis p s) {q : α → Prop} :
    (∀ᶠ x in l, q x) ↔ ∃ i, p i ∧ ∀ ⦃x⦄, x ∈ s i → q x := by simpa using hl.mem_iff
#align filter.has_basis.eventually_iff Filter.HasBasis.eventually_iff

theorem HasBasis.frequently_iff (hl : l.HasBasis p s) {q : α → Prop} :
    (∃ᶠ x in l, q x) ↔ ∀ i, p i → ∃ x ∈ s i, q x := by
  simp only [Filter.Frequently, hl.eventually_iff]; push_neg; rfl
#align filter.has_basis.frequently_iff Filter.HasBasis.frequently_iff

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
theorem HasBasis.exists_iff (hl : l.HasBasis p s) {P : Set α → Prop}
    (mono : ∀ ⦃s t⦄, s ⊆ t → P t → P s) : (∃ s ∈ l, P s) ↔ ∃ i, p i ∧ P (s i) :=
  ⟨fun ⟨_s, hs, hP⟩ =>
    let ⟨i, hi, his⟩ := hl.mem_iff.1 hs
    ⟨i, hi, mono his hP⟩,
    fun ⟨i, hi, hP⟩ => ⟨s i, hl.mem_of_mem hi, hP⟩⟩
#align filter.has_basis.exists_iff Filter.HasBasis.exists_iffₓ

theorem HasBasis.forall_iff (hl : l.HasBasis p s) {P : Set α → Prop}
    (mono : ∀ ⦃s t⦄, s ⊆ t → P s → P t) : (∀ s ∈ l, P s) ↔ ∀ i, p i → P (s i) :=
  ⟨fun H i hi => H (s i) <| hl.mem_of_mem hi, fun H _s hs =>
    let ⟨i, hi, his⟩ := hl.mem_iff.1 hs
    mono his (H i hi)⟩
#align filter.has_basis.forall_iff Filter.HasBasis.forall_iff

protected theorem HasBasis.neBot_iff (hl : l.HasBasis p s) :
    NeBot l ↔ ∀ {i}, p i → (s i).Nonempty :=
  forall_mem_nonempty_iff_neBot.symm.trans <| hl.forall_iff fun _ _ => Nonempty.mono
#align filter.has_basis.ne_bot_iff Filter.HasBasis.neBot_iff

theorem HasBasis.eq_bot_iff (hl : l.HasBasis p s) : l = ⊥ ↔ ∃ i, p i ∧ s i = ∅ :=
  not_iff_not.1 <| neBot_iff.symm.trans <|
    hl.neBot_iff.trans <| by simp only [not_exists, not_and, nonempty_iff_ne_empty]
#align filter.has_basis.eq_bot_iff Filter.HasBasis.eq_bot_iff

theorem generate_neBot_iff {s : Set (Set α)} :
    NeBot (generate s) ↔ ∀ t, t ⊆ s → t.Finite → (⋂₀ t).Nonempty :=
  (hasBasis_generate s).neBot_iff.trans <| by simp only [← and_imp, and_comm]
#align filter.generate_ne_bot_iff Filter.generate_neBot_iff

theorem basis_sets (l : Filter α) : l.HasBasis (fun s : Set α => s ∈ l) id :=
  ⟨fun _ => exists_mem_subset_iff.symm⟩
#align filter.basis_sets Filter.basis_sets

theorem asBasis_filter (f : Filter α) : f.asBasis.filter = f :=
  Filter.ext fun _ => exists_mem_subset_iff
#align filter.as_basis_filter Filter.asBasis_filter

theorem hasBasis_self {l : Filter α} {P : Set α → Prop} :
    HasBasis l (fun s => s ∈ l ∧ P s) id ↔ ∀ t ∈ l, ∃ r ∈ l, P r ∧ r ⊆ t := by
  simp only [hasBasis_iff, id, and_assoc]
  exact forall_congr' fun s =>
    ⟨fun h => h.1, fun h => ⟨h, fun ⟨t, hl, _, hts⟩ => mem_of_superset hl hts⟩⟩
#align filter.has_basis_self Filter.hasBasis_self

theorem HasBasis.comp_surjective (h : l.HasBasis p s) {g : ι' → ι} (hg : Function.Surjective g) :
    l.HasBasis (p ∘ g) (s ∘ g) :=
  ⟨fun _ => h.mem_iff.trans hg.exists⟩
#align filter.has_basis.comp_surjective Filter.HasBasis.comp_surjective

theorem HasBasis.comp_equiv (h : l.HasBasis p s) (e : ι' ≃ ι) : l.HasBasis (p ∘ e) (s ∘ e) :=
  h.comp_surjective e.surjective
#align filter.has_basis.comp_equiv Filter.HasBasis.comp_equiv

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
#align filter.has_basis.restrict Filter.HasBasis.restrict

/-- If `{s i | p i}` is a basis of a filter `l` and `V ∈ l`, then `{s i | p i ∧ s i ⊆ V}`
is a basis of `l`. -/
theorem HasBasis.restrict_subset (h : l.HasBasis p s) {V : Set α} (hV : V ∈ l) :
    l.HasBasis (fun i => p i ∧ s i ⊆ V) s :=
  h.restrict fun _i hi => (h.mem_iff.1 (inter_mem hV (h.mem_of_mem hi))).imp fun _j hj =>
    ⟨hj.1, subset_inter_iff.1 hj.2⟩
#align filter.has_basis.restrict_subset Filter.HasBasis.restrict_subset

theorem HasBasis.hasBasis_self_subset {p : Set α → Prop} (h : l.HasBasis (fun s => s ∈ l ∧ p s) id)
    {V : Set α} (hV : V ∈ l) : l.HasBasis (fun s => s ∈ l ∧ p s ∧ s ⊆ V) id := by
  simpa only [and_assoc] using h.restrict_subset hV
#align filter.has_basis.has_basis_self_subset Filter.HasBasis.hasBasis_self_subset

theorem HasBasis.ge_iff (hl' : l'.HasBasis p' s') : l ≤ l' ↔ ∀ i', p' i' → s' i' ∈ l :=
  ⟨fun h _i' hi' => h <| hl'.mem_of_mem hi', fun h _s hs =>
    let ⟨_i', hi', hs⟩ := hl'.mem_iff.1 hs
    mem_of_superset (h _ hi') hs⟩
#align filter.has_basis.ge_iff Filter.HasBasis.ge_iff

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
theorem HasBasis.le_iff (hl : l.HasBasis p s) : l ≤ l' ↔ ∀ t ∈ l', ∃ i, p i ∧ s i ⊆ t := by
  simp only [le_def, hl.mem_iff]
#align filter.has_basis.le_iff Filter.HasBasis.le_iffₓ

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
theorem HasBasis.le_basis_iff (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    l ≤ l' ↔ ∀ i', p' i' → ∃ i, p i ∧ s i ⊆ s' i' := by
  simp only [hl'.ge_iff, hl.mem_iff]
#align filter.has_basis.le_basis_iff Filter.HasBasis.le_basis_iffₓ

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
theorem HasBasis.ext (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s')
    (h : ∀ i, p i → ∃ i', p' i' ∧ s' i' ⊆ s i) (h' : ∀ i', p' i' → ∃ i, p i ∧ s i ⊆ s' i') :
    l = l' := by
  apply le_antisymm
  · rw [hl.le_basis_iff hl']
    simpa using h'
  · rw [hl'.le_basis_iff hl]
    simpa using h
#align filter.has_basis.ext Filter.HasBasis.extₓ

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
#align filter.has_basis.inf' Filter.HasBasis.inf'

theorem HasBasis.inf {ι ι' : Type*} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}
    {s' : ι' → Set α} (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    (l ⊓ l').HasBasis (fun i : ι × ι' => p i.1 ∧ p' i.2) fun i => s i.1 ∩ s' i.2 :=
  (hl.inf' hl').comp_equiv Equiv.pprodEquivProd.symm
#align filter.has_basis.inf Filter.HasBasis.inf

theorem hasBasis_iInf' {ι : Type*} {ι' : ι → Type*} {l : ι → Filter α} {p : ∀ i, ι' i → Prop}
    {s : ∀ i, ι' i → Set α} (hl : ∀ i, (l i).HasBasis (p i) (s i)) :
    (⨅ i, l i).HasBasis (fun If : Set ι × ∀ i, ι' i => If.1.Finite ∧ ∀ i ∈ If.1, p i (If.2 i))
      fun If : Set ι × ∀ i, ι' i => ⋂ i ∈ If.1, s i (If.2 i) :=
  ⟨by
    intro t
    constructor
    · simp only [mem_iInf', (hl _).mem_iff]
      rintro ⟨I, hI, V, hV, -, rfl, -⟩
      choose u hu using hV
      exact ⟨⟨I, u⟩, ⟨hI, fun i _ => (hu i).1⟩, iInter₂_mono fun i _ => (hu i).2⟩
    · rintro ⟨⟨I, f⟩, ⟨hI₁, hI₂⟩, hsub⟩
      refine mem_of_superset ?_ hsub
      exact (biInter_mem hI₁).mpr fun i hi => mem_iInf_of_mem i <| (hl i).mem_of_mem <| hI₂ _ hi⟩
#align filter.has_basis_infi' Filter.hasBasis_iInf'

theorem hasBasis_iInf {ι : Type*} {ι' : ι → Type*} {l : ι → Filter α} {p : ∀ i, ι' i → Prop}
    {s : ∀ i, ι' i → Set α} (hl : ∀ i, (l i).HasBasis (p i) (s i)) :
    (⨅ i, l i).HasBasis
      (fun If : Σ I : Set ι, ∀ i : I, ι' i => If.1.Finite ∧ ∀ i : If.1, p i (If.2 i)) fun If =>
      ⋂ i : If.1, s i (If.2 i) := by
  refine ⟨fun t => ⟨fun ht => ?_, ?_⟩⟩
  · rcases (hasBasis_iInf' hl).mem_iff.mp ht with ⟨⟨I, f⟩, ⟨hI, hf⟩, hsub⟩
    exact ⟨⟨I, fun i => f i⟩, ⟨hI, Subtype.forall.mpr hf⟩, trans (iInter_subtype _ _) hsub⟩
  · rintro ⟨⟨I, f⟩, ⟨hI, hf⟩, hsub⟩
    refine mem_of_superset ?_ hsub
    cases hI.nonempty_fintype
    exact iInter_mem.2 fun i => mem_iInf_of_mem ↑i <| (hl i).mem_of_mem <| hf _
#align filter.has_basis_infi Filter.hasBasis_iInf

theorem hasBasis_iInf_of_directed' {ι : Type*} {ι' : ι → Sort _} [Nonempty ι] {l : ι → Filter α}
    (s : ∀ i, ι' i → Set α) (p : ∀ i, ι' i → Prop) (hl : ∀ i, (l i).HasBasis (p i) (s i))
    (h : Directed (· ≥ ·) l) :
    (⨅ i, l i).HasBasis (fun ii' : Σi, ι' i => p ii'.1 ii'.2) fun ii' => s ii'.1 ii'.2 := by
  refine ⟨fun t => ?_⟩
  rw [mem_iInf_of_directed h, Sigma.exists]
  exact exists_congr fun i => (hl i).mem_iff
#align filter.has_basis_infi_of_directed' Filter.hasBasis_iInf_of_directed'

theorem hasBasis_iInf_of_directed {ι : Type*} {ι' : Sort _} [Nonempty ι] {l : ι → Filter α}
    (s : ι → ι' → Set α) (p : ι → ι' → Prop) (hl : ∀ i, (l i).HasBasis (p i) (s i))
    (h : Directed (· ≥ ·) l) :
    (⨅ i, l i).HasBasis (fun ii' : ι × ι' => p ii'.1 ii'.2) fun ii' => s ii'.1 ii'.2 := by
  refine ⟨fun t => ?_⟩
  rw [mem_iInf_of_directed h, Prod.exists]
  exact exists_congr fun i => (hl i).mem_iff
#align filter.has_basis_infi_of_directed Filter.hasBasis_iInf_of_directed

theorem hasBasis_biInf_of_directed' {ι : Type*} {ι' : ι → Sort _} {dom : Set ι}
    (hdom : dom.Nonempty) {l : ι → Filter α} (s : ∀ i, ι' i → Set α) (p : ∀ i, ι' i → Prop)
    (hl : ∀ i ∈ dom, (l i).HasBasis (p i) (s i)) (h : DirectedOn (l ⁻¹'o GE.ge) dom) :
    (⨅ i ∈ dom, l i).HasBasis (fun ii' : Σi, ι' i => ii'.1 ∈ dom ∧ p ii'.1 ii'.2) fun ii' =>
      s ii'.1 ii'.2 := by
  refine ⟨fun t => ?_⟩
  rw [mem_biInf_of_directed h hdom, Sigma.exists]
  refine exists_congr fun i => ⟨?_, ?_⟩
  · rintro ⟨hi, hti⟩
    rcases (hl i hi).mem_iff.mp hti with ⟨b, hb, hbt⟩
    exact ⟨b, ⟨hi, hb⟩, hbt⟩
  · rintro ⟨b, ⟨hi, hb⟩, hibt⟩
    exact ⟨hi, (hl i hi).mem_iff.mpr ⟨b, hb, hibt⟩⟩
#align filter.has_basis_binfi_of_directed' Filter.hasBasis_biInf_of_directed'

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
#align filter.has_basis_binfi_of_directed Filter.hasBasis_biInf_of_directed

theorem hasBasis_principal (t : Set α) : (𝓟 t).HasBasis (fun _ : Unit => True) fun _ => t :=
  ⟨fun U => by simp⟩
#align filter.has_basis_principal Filter.hasBasis_principal

theorem hasBasis_pure (x : α) :
    (pure x : Filter α).HasBasis (fun _ : Unit => True) fun _ => {x} := by
  simp only [← principal_singleton, hasBasis_principal]
#align filter.has_basis_pure Filter.hasBasis_pure

theorem HasBasis.sup' (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    (l ⊔ l').HasBasis (fun i : PProd ι ι' => p i.1 ∧ p' i.2) fun i => s i.1 ∪ s' i.2 :=
  ⟨by
    intro t
    simp_rw [mem_sup, hl.mem_iff, hl'.mem_iff, PProd.exists, union_subset_iff,
       ← exists_and_right, ← exists_and_left]
    simp only [and_assoc, and_left_comm]⟩
#align filter.has_basis.sup' Filter.HasBasis.sup'

theorem HasBasis.sup {ι ι' : Type*} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}
    {s' : ι' → Set α} (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    (l ⊔ l').HasBasis (fun i : ι × ι' => p i.1 ∧ p' i.2) fun i => s i.1 ∪ s' i.2 :=
  (hl.sup' hl').comp_equiv Equiv.pprodEquivProd.symm
#align filter.has_basis.sup Filter.HasBasis.sup

theorem hasBasis_iSup {ι : Sort*} {ι' : ι → Type*} {l : ι → Filter α} {p : ∀ i, ι' i → Prop}
    {s : ∀ i, ι' i → Set α} (hl : ∀ i, (l i).HasBasis (p i) (s i)) :
    (⨆ i, l i).HasBasis (fun f : ∀ i, ι' i => ∀ i, p i (f i)) fun f : ∀ i, ι' i => ⋃ i, s i (f i) :=
  hasBasis_iff.mpr fun t => by
    simp only [hasBasis_iff, (hl _).mem_iff, Classical.skolem, forall_and, iUnion_subset_iff,
      mem_iSup]
#align filter.has_basis_supr Filter.hasBasis_iSup

theorem HasBasis.sup_principal (hl : l.HasBasis p s) (t : Set α) :
    (l ⊔ 𝓟 t).HasBasis p fun i => s i ∪ t :=
  ⟨fun u => by
    simp only [(hl.sup' (hasBasis_principal t)).mem_iff, PProd.exists, exists_prop, and_true_iff,
      Unique.exists_iff]⟩
#align filter.has_basis.sup_principal Filter.HasBasis.sup_principal

theorem HasBasis.sup_pure (hl : l.HasBasis p s) (x : α) :
    (l ⊔ pure x).HasBasis p fun i => s i ∪ {x} := by
  simp only [← principal_singleton, hl.sup_principal]
#align filter.has_basis.sup_pure Filter.HasBasis.sup_pure

theorem HasBasis.inf_principal (hl : l.HasBasis p s) (s' : Set α) :
    (l ⊓ 𝓟 s').HasBasis p fun i => s i ∩ s' :=
  ⟨fun t => by
    simp only [mem_inf_principal, hl.mem_iff, subset_def, mem_setOf_eq, mem_inter_iff, and_imp]⟩
#align filter.has_basis.inf_principal Filter.HasBasis.inf_principal

theorem HasBasis.principal_inf (hl : l.HasBasis p s) (s' : Set α) :
    (𝓟 s' ⊓ l).HasBasis p fun i => s' ∩ s i := by
  simpa only [inf_comm, inter_comm] using hl.inf_principal s'
#align filter.has_basis.principal_inf Filter.HasBasis.principal_inf

theorem HasBasis.inf_basis_neBot_iff (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    NeBot (l ⊓ l') ↔ ∀ ⦃i⦄, p i → ∀ ⦃i'⦄, p' i' → (s i ∩ s' i').Nonempty :=
  (hl.inf' hl').neBot_iff.trans <| by simp [@forall_swap _ ι']
#align filter.has_basis.inf_basis_ne_bot_iff Filter.HasBasis.inf_basis_neBot_iff

theorem HasBasis.inf_neBot_iff (hl : l.HasBasis p s) :
    NeBot (l ⊓ l') ↔ ∀ ⦃i⦄, p i → ∀ ⦃s'⦄, s' ∈ l' → (s i ∩ s').Nonempty :=
  hl.inf_basis_neBot_iff l'.basis_sets
#align filter.has_basis.inf_ne_bot_iff Filter.HasBasis.inf_neBot_iff

theorem HasBasis.inf_principal_neBot_iff (hl : l.HasBasis p s) {t : Set α} :
    NeBot (l ⊓ 𝓟 t) ↔ ∀ ⦃i⦄, p i → (s i ∩ t).Nonempty :=
  (hl.inf_principal t).neBot_iff
#align filter.has_basis.inf_principal_ne_bot_iff Filter.HasBasis.inf_principal_neBot_iff

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
theorem HasBasis.disjoint_iff (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    Disjoint l l' ↔ ∃ i, p i ∧ ∃ i', p' i' ∧ Disjoint (s i) (s' i') :=
  not_iff_not.mp <| by simp only [_root_.disjoint_iff, ← Ne.eq_def, ← neBot_iff, inf_eq_inter,
    hl.inf_basis_neBot_iff hl', not_exists, not_and, bot_eq_empty, ← nonempty_iff_ne_empty]
#align filter.has_basis.disjoint_iff Filter.HasBasis.disjoint_iffₓ

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
theorem _root_.Disjoint.exists_mem_filter_basis (h : Disjoint l l') (hl : l.HasBasis p s)
    (hl' : l'.HasBasis p' s') : ∃ i, p i ∧ ∃ i', p' i' ∧ Disjoint (s i) (s' i') :=
  (hl.disjoint_iff hl').1 h
#align disjoint.exists_mem_filter_basis Disjoint.exists_mem_filter_basisₓ

theorem _root_.Pairwise.exists_mem_filter_basis_of_disjoint {I} [Finite I] {l : I → Filter α}
    {ι : I → Sort*} {p : ∀ i, ι i → Prop} {s : ∀ i, ι i → Set α} (hd : Pairwise (Disjoint on l))
    (h : ∀ i, (l i).HasBasis (p i) (s i)) :
    ∃ ind : ∀ i, ι i, (∀ i, p i (ind i)) ∧ Pairwise (Disjoint on fun i => s i (ind i)) := by
  rcases hd.exists_mem_filter_of_disjoint with ⟨t, htl, hd⟩
  choose ind hp ht using fun i => (h i).mem_iff.1 (htl i)
  exact ⟨ind, hp, hd.mono fun i j hij => hij.mono (ht _) (ht _)⟩
#align pairwise.exists_mem_filter_basis_of_disjoint Pairwise.exists_mem_filter_basis_of_disjoint

theorem _root_.Set.PairwiseDisjoint.exists_mem_filter_basis {I : Type*} {l : I → Filter α}
    {ι : I → Sort*} {p : ∀ i, ι i → Prop} {s : ∀ i, ι i → Set α} {S : Set I}
    (hd : S.PairwiseDisjoint l) (hS : S.Finite) (h : ∀ i, (l i).HasBasis (p i) (s i)) :
    ∃ ind : ∀ i, ι i, (∀ i, p i (ind i)) ∧ S.PairwiseDisjoint fun i => s i (ind i) := by
  rcases hd.exists_mem_filter hS with ⟨t, htl, hd⟩
  choose ind hp ht using fun i => (h i).mem_iff.1 (htl i)
  exact ⟨ind, hp, hd.mono ht⟩
#align set.pairwise_disjoint.exists_mem_filter_basis Set.PairwiseDisjoint.exists_mem_filter_basis

theorem inf_neBot_iff :
    NeBot (l ⊓ l') ↔ ∀ ⦃s : Set α⦄, s ∈ l → ∀ ⦃s'⦄, s' ∈ l' → (s ∩ s').Nonempty :=
  l.basis_sets.inf_neBot_iff
#align filter.inf_ne_bot_iff Filter.inf_neBot_iff

theorem inf_principal_neBot_iff {s : Set α} : NeBot (l ⊓ 𝓟 s) ↔ ∀ U ∈ l, (U ∩ s).Nonempty :=
  l.basis_sets.inf_principal_neBot_iff
#align filter.inf_principal_ne_bot_iff Filter.inf_principal_neBot_iff

theorem mem_iff_inf_principal_compl {f : Filter α} {s : Set α} : s ∈ f ↔ f ⊓ 𝓟 sᶜ = ⊥ := by
  refine not_iff_not.1 ((inf_principal_neBot_iff.trans ?_).symm.trans neBot_iff)
  exact
    ⟨fun h hs => by simpa [Set.not_nonempty_empty] using h s hs, fun hs t ht =>
      inter_compl_nonempty_iff.2 fun hts => hs <| mem_of_superset ht hts⟩
#align filter.mem_iff_inf_principal_compl Filter.mem_iff_inf_principal_compl

theorem not_mem_iff_inf_principal_compl {f : Filter α} {s : Set α} : s ∉ f ↔ NeBot (f ⊓ 𝓟 sᶜ) :=
  (not_congr mem_iff_inf_principal_compl).trans neBot_iff.symm
#align filter.not_mem_iff_inf_principal_compl Filter.not_mem_iff_inf_principal_compl

@[simp]
theorem disjoint_principal_right {f : Filter α} {s : Set α} : Disjoint f (𝓟 s) ↔ sᶜ ∈ f := by
  rw [mem_iff_inf_principal_compl, compl_compl, disjoint_iff]
#align filter.disjoint_principal_right Filter.disjoint_principal_right

@[simp]
theorem disjoint_principal_left {f : Filter α} {s : Set α} : Disjoint (𝓟 s) f ↔ sᶜ ∈ f := by
  rw [disjoint_comm, disjoint_principal_right]
#align filter.disjoint_principal_left Filter.disjoint_principal_left

@[simp 1100] -- Porting note: higher priority for linter
theorem disjoint_principal_principal {s t : Set α} : Disjoint (𝓟 s) (𝓟 t) ↔ Disjoint s t := by
  rw [← subset_compl_iff_disjoint_left, disjoint_principal_left, mem_principal]
#align filter.disjoint_principal_principal Filter.disjoint_principal_principal

alias ⟨_, _root_.Disjoint.filter_principal⟩ := disjoint_principal_principal
#align disjoint.filter_principal Disjoint.filter_principal

@[simp]
theorem disjoint_pure_pure {x y : α} : Disjoint (pure x : Filter α) (pure y) ↔ x ≠ y := by
  simp only [← principal_singleton, disjoint_principal_principal, disjoint_singleton]
#align filter.disjoint_pure_pure Filter.disjoint_pure_pure

@[simp]
theorem compl_diagonal_mem_prod {l₁ l₂ : Filter α} : (diagonal α)ᶜ ∈ l₁ ×ˢ l₂ ↔ Disjoint l₁ l₂ := by
  simp only [mem_prod_iff, Filter.disjoint_iff, prod_subset_compl_diagonal_iff_disjoint]
#align filter.compl_diagonal_mem_prod Filter.compl_diagonal_mem_prod

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
theorem HasBasis.disjoint_iff_left (h : l.HasBasis p s) :
    Disjoint l l' ↔ ∃ i, p i ∧ (s i)ᶜ ∈ l' := by
  simp only [h.disjoint_iff l'.basis_sets, id, ← disjoint_principal_left,
    (hasBasis_principal _).disjoint_iff l'.basis_sets, true_and, Unique.exists_iff]
#align filter.has_basis.disjoint_iff_left Filter.HasBasis.disjoint_iff_leftₓ

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
theorem HasBasis.disjoint_iff_right (h : l.HasBasis p s) :
    Disjoint l' l ↔ ∃ i, p i ∧ (s i)ᶜ ∈ l' :=
  disjoint_comm.trans h.disjoint_iff_left
#align filter.has_basis.disjoint_iff_right Filter.HasBasis.disjoint_iff_rightₓ

theorem le_iff_forall_inf_principal_compl {f g : Filter α} : f ≤ g ↔ ∀ V ∈ g, f ⊓ 𝓟 Vᶜ = ⊥ :=
  forall₂_congr fun _ _ => mem_iff_inf_principal_compl
#align filter.le_iff_forall_inf_principal_compl Filter.le_iff_forall_inf_principal_compl

theorem inf_neBot_iff_frequently_left {f g : Filter α} :
    NeBot (f ⊓ g) ↔ ∀ {p : α → Prop}, (∀ᶠ x in f, p x) → ∃ᶠ x in g, p x := by
  simp only [inf_neBot_iff, frequently_iff, and_comm]; rfl
#align filter.inf_ne_bot_iff_frequently_left Filter.inf_neBot_iff_frequently_left

theorem inf_neBot_iff_frequently_right {f g : Filter α} :
    NeBot (f ⊓ g) ↔ ∀ {p : α → Prop}, (∀ᶠ x in g, p x) → ∃ᶠ x in f, p x := by
  rw [inf_comm]
  exact inf_neBot_iff_frequently_left
#align filter.inf_ne_bot_iff_frequently_right Filter.inf_neBot_iff_frequently_right

theorem HasBasis.eq_biInf (h : l.HasBasis p s) : l = ⨅ (i) (_ : p i), 𝓟 (s i) :=
  eq_biInf_of_mem_iff_exists_mem fun {_} => by simp only [h.mem_iff, mem_principal, exists_prop]
#align filter.has_basis.eq_binfi Filter.HasBasis.eq_biInf

theorem HasBasis.eq_iInf (h : l.HasBasis (fun _ => True) s) : l = ⨅ i, 𝓟 (s i) := by
  simpa only [iInf_true] using h.eq_biInf
#align filter.has_basis.eq_infi Filter.HasBasis.eq_iInf

theorem hasBasis_iInf_principal {s : ι → Set α} (h : Directed (· ≥ ·) s) [Nonempty ι] :
    (⨅ i, 𝓟 (s i)).HasBasis (fun _ => True) s :=
  ⟨fun t => by
    simpa only [true_and] using mem_iInf_of_directed (h.mono_comp monotone_principal.dual) t⟩
#align filter.has_basis_infi_principal Filter.hasBasis_iInf_principal

/-- If `s : ι → Set α` is an indexed family of sets, then finite intersections of `s i` form a basis
of `⨅ i, 𝓟 (s i)`.  -/
theorem hasBasis_iInf_principal_finite {ι : Type*} (s : ι → Set α) :
    (⨅ i, 𝓟 (s i)).HasBasis (fun t : Set ι => t.Finite) fun t => ⋂ i ∈ t, s i := by
  refine ⟨fun U => (mem_iInf_finite _).trans ?_⟩
  simp only [iInf_principal_finset, mem_iUnion, mem_principal, exists_prop,
    exists_finite_iff_finset, Finset.set_biInter_coe]
#align filter.has_basis_infi_principal_finite Filter.hasBasis_iInf_principal_finite

theorem hasBasis_biInf_principal {s : β → Set α} {S : Set β} (h : DirectedOn (s ⁻¹'o (· ≥ ·)) S)
    (ne : S.Nonempty) : (⨅ i ∈ S, 𝓟 (s i)).HasBasis (fun i => i ∈ S) s :=
  ⟨fun t => by
    refine mem_biInf_of_directed ?_ ne
    rw [directedOn_iff_directed, ← directed_comp] at h ⊢
    refine h.mono_comp ?_
    exact fun _ _ => principal_mono.2⟩
#align filter.has_basis_binfi_principal Filter.hasBasis_biInf_principal

theorem hasBasis_biInf_principal' {ι : Type*} {p : ι → Prop} {s : ι → Set α}
    (h : ∀ i, p i → ∀ j, p j → ∃ k, p k ∧ s k ⊆ s i ∧ s k ⊆ s j) (ne : ∃ i, p i) :
    (⨅ (i) (_ : p i), 𝓟 (s i)).HasBasis p s :=
  Filter.hasBasis_biInf_principal h ne
#align filter.has_basis_binfi_principal' Filter.hasBasis_biInf_principal'

theorem HasBasis.map (f : α → β) (hl : l.HasBasis p s) : (l.map f).HasBasis p fun i => f '' s i :=
  ⟨fun t => by simp only [mem_map, image_subset_iff, hl.mem_iff, preimage]⟩
#align filter.has_basis.map Filter.HasBasis.map

theorem HasBasis.comap (f : β → α) (hl : l.HasBasis p s) :
    (l.comap f).HasBasis p fun i => f ⁻¹' s i :=
  ⟨fun t => by
    simp only [mem_comap', hl.mem_iff]
    refine exists_congr (fun i => Iff.rfl.and ?_)
    exact ⟨fun h x hx => h hx rfl, fun h y hy x hx => h <| by rwa [mem_preimage, hx]⟩⟩
#align filter.has_basis.comap Filter.HasBasis.comap

theorem comap_hasBasis (f : α → β) (l : Filter β) :
    HasBasis (comap f l) (fun s : Set β => s ∈ l) fun s => f ⁻¹' s :=
  ⟨fun _ => mem_comap⟩
#align filter.comap_has_basis Filter.comap_hasBasis

theorem HasBasis.forall_mem_mem (h : HasBasis l p s) {x : α} :
    (∀ t ∈ l, x ∈ t) ↔ ∀ i, p i → x ∈ s i := by
  simp only [h.mem_iff, exists_imp, and_imp]
  exact ⟨fun h i hi => h (s i) i hi Subset.rfl, fun h t i hi ht => ht (h i hi)⟩
#align filter.has_basis.forall_mem_mem Filter.HasBasis.forall_mem_mem

protected theorem HasBasis.biInf_mem [CompleteLattice β] {f : Set α → β} (h : HasBasis l p s)
    (hf : Monotone f) : ⨅ t ∈ l, f t = ⨅ (i) (_ : p i), f (s i) :=
  le_antisymm (le_iInf₂ fun i hi => iInf₂_le (s i) (h.mem_of_mem hi)) <|
    le_iInf₂ fun _t ht =>
      let ⟨i, hpi, hi⟩ := h.mem_iff.1 ht
      iInf₂_le_of_le i hpi (hf hi)
#align filter.has_basis.binfi_mem Filter.HasBasis.biInf_mem

protected theorem HasBasis.biInter_mem {f : Set α → Set β} (h : HasBasis l p s) (hf : Monotone f) :
    ⋂ t ∈ l, f t = ⋂ (i) (_ : p i), f (s i) :=
  h.biInf_mem hf
#align filter.has_basis.bInter_mem Filter.HasBasis.biInter_mem

protected theorem HasBasis.ker (h : HasBasis l p s) : l.ker = ⋂ (i) (_ : p i), s i :=
  l.ker_def.trans <| h.biInter_mem monotone_id
#align filter.has_basis.sInter_sets Filter.HasBasis.ker

variable {ι'' : Type*} [Preorder ι''] (l) (s'' : ι'' → Set α)

/-- `IsAntitoneBasis s` means the image of `s` is a filter basis such that `s` is decreasing. -/
structure IsAntitoneBasis extends IsBasis (fun _ => True) s'' : Prop where
  /-- The sequence of sets is antitone. -/
  protected antitone : Antitone s''
#align filter.is_antitone_basis Filter.IsAntitoneBasis

/-- We say that a filter `l` has an antitone basis `s : ι → Set α`, if `t ∈ l` if and only if `t`
includes `s i` for some `i`, and `s` is decreasing. -/
structure HasAntitoneBasis (l : Filter α) (s : ι'' → Set α)
    extends HasBasis l (fun _ => True) s : Prop where
  /-- The sequence of sets is antitone. -/
  protected antitone : Antitone s
#align filter.has_antitone_basis Filter.HasAntitoneBasis

protected theorem HasAntitoneBasis.map {l : Filter α} {s : ι'' → Set α}
    (hf : HasAntitoneBasis l s) (m : α → β) : HasAntitoneBasis (map m l) (m '' s ·) :=
  ⟨HasBasis.map _ hf.toHasBasis, fun _ _ h => image_subset _ <| hf.2 h⟩
#align filter.has_antitone_basis.map Filter.HasAntitoneBasis.map

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

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
theorem HasBasis.tendsto_left_iff (hla : la.HasBasis pa sa) :
    Tendsto f la lb ↔ ∀ t ∈ lb, ∃ i, pa i ∧ MapsTo f (sa i) t := by
  simp only [Tendsto, (hla.map f).le_iff, image_subset_iff]
  rfl
#align filter.has_basis.tendsto_left_iff Filter.HasBasis.tendsto_left_iffₓ

theorem HasBasis.tendsto_right_iff (hlb : lb.HasBasis pb sb) :
    Tendsto f la lb ↔ ∀ i, pb i → ∀ᶠ x in la, f x ∈ sb i := by
  simp only [Tendsto, hlb.ge_iff, mem_map', Filter.Eventually]
#align filter.has_basis.tendsto_right_iff Filter.HasBasis.tendsto_right_iff

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
theorem HasBasis.tendsto_iff (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    Tendsto f la lb ↔ ∀ ib, pb ib → ∃ ia, pa ia ∧ ∀ x ∈ sa ia, f x ∈ sb ib := by
  simp [hlb.tendsto_right_iff, hla.eventually_iff]
#align filter.has_basis.tendsto_iff Filter.HasBasis.tendsto_iffₓ

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
theorem Tendsto.basis_left (H : Tendsto f la lb) (hla : la.HasBasis pa sa) :
    ∀ t ∈ lb, ∃ i, pa i ∧ MapsTo f (sa i) t :=
  hla.tendsto_left_iff.1 H
#align filter.tendsto.basis_left Filter.Tendsto.basis_leftₓ

theorem Tendsto.basis_right (H : Tendsto f la lb) (hlb : lb.HasBasis pb sb) :
    ∀ i, pb i → ∀ᶠ x in la, f x ∈ sb i :=
  hlb.tendsto_right_iff.1 H
#align filter.tendsto.basis_right Filter.Tendsto.basis_right

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
theorem Tendsto.basis_both (H : Tendsto f la lb) (hla : la.HasBasis pa sa)
    (hlb : lb.HasBasis pb sb) :
    ∀ ib, pb ib → ∃ ia, pa ia ∧ MapsTo f (sa ia) (sb ib) :=
  (hla.tendsto_iff hlb).1 H
#align filter.tendsto.basis_both Filter.Tendsto.basis_bothₓ

theorem HasBasis.prod_pprod (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    (la ×ˢ lb).HasBasis (fun i : PProd ι ι' => pa i.1 ∧ pb i.2) fun i => sa i.1 ×ˢ sb i.2 :=
  (hla.comap Prod.fst).inf' (hlb.comap Prod.snd)
#align filter.has_basis.prod_pprod Filter.HasBasis.prod_pprod

theorem HasBasis.prod {ι ι' : Type*} {pa : ι → Prop} {sa : ι → Set α} {pb : ι' → Prop}
    {sb : ι' → Set β} (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    (la ×ˢ lb).HasBasis (fun i : ι × ι' => pa i.1 ∧ pb i.2) fun i => sa i.1 ×ˢ sb i.2 :=
  (hla.comap Prod.fst).inf (hlb.comap Prod.snd)
#align filter.has_basis.prod Filter.HasBasis.prod

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
#align filter.has_basis.prod_same_index Filter.HasBasis.prod_same_index

theorem HasBasis.prod_same_index_mono {ι : Type*} [LinearOrder ι] {p : ι → Prop} {sa : ι → Set α}
    {sb : ι → Set β} (hla : la.HasBasis p sa) (hlb : lb.HasBasis p sb)
    (hsa : MonotoneOn sa { i | p i }) (hsb : MonotoneOn sb { i | p i }) :
    (la ×ˢ lb).HasBasis p fun i => sa i ×ˢ sb i :=
  hla.prod_same_index hlb fun {i j} hi hj =>
    have : p (min i j) := min_rec' _ hi hj
    ⟨min i j, this, hsa this hi <| min_le_left _ _, hsb this hj <| min_le_right _ _⟩
#align filter.has_basis.prod_same_index_mono Filter.HasBasis.prod_same_index_mono

theorem HasBasis.prod_same_index_anti {ι : Type*} [LinearOrder ι] {p : ι → Prop} {sa : ι → Set α}
    {sb : ι → Set β} (hla : la.HasBasis p sa) (hlb : lb.HasBasis p sb)
    (hsa : AntitoneOn sa { i | p i }) (hsb : AntitoneOn sb { i | p i }) :
    (la ×ˢ lb).HasBasis p fun i => sa i ×ˢ sb i :=
  @HasBasis.prod_same_index_mono _ _ _ _ ιᵒᵈ _ _ _ _ hla hlb hsa.dual_left hsb.dual_left
#align filter.has_basis.prod_same_index_anti Filter.HasBasis.prod_same_index_anti

theorem HasBasis.prod_self (hl : la.HasBasis pa sa) :
    (la ×ˢ la).HasBasis pa fun i => sa i ×ˢ sa i :=
  hl.prod_same_index hl fun {i j} hi hj => by
    simpa only [exists_prop, subset_inter_iff] using
      hl.mem_iff.1 (inter_mem (hl.mem_of_mem hi) (hl.mem_of_mem hj))
#align filter.has_basis.prod_self Filter.HasBasis.prod_self

theorem mem_prod_self_iff {s} : s ∈ la ×ˢ la ↔ ∃ t ∈ la, t ×ˢ t ⊆ s :=
  la.basis_sets.prod_self.mem_iff
#align filter.mem_prod_self_iff Filter.mem_prod_self_iff

lemma eventually_prod_self_iff {r : α → α → Prop} :
    (∀ᶠ x in la ×ˢ la, r x.1 x.2) ↔ ∃ t ∈ la, ∀ x ∈ t, ∀ y ∈ t, r x y :=
  mem_prod_self_iff.trans <| by simp only [prod_subset_iff, mem_setOf_eq]

theorem HasAntitoneBasis.prod {ι : Type*} [LinearOrder ι] {f : Filter α} {g : Filter β}
    {s : ι → Set α} {t : ι → Set β} (hf : HasAntitoneBasis f s) (hg : HasAntitoneBasis g t) :
    HasAntitoneBasis (f ×ˢ g) fun n => s n ×ˢ t n :=
  ⟨hf.1.prod_same_index_anti hg.1 (hf.2.antitoneOn _) (hg.2.antitoneOn _), hf.2.set_prod hg.2⟩
#align filter.has_antitone_basis.prod Filter.HasAntitoneBasis.prod

theorem HasBasis.coprod {ι ι' : Type*} {pa : ι → Prop} {sa : ι → Set α} {pb : ι' → Prop}
    {sb : ι' → Set β} (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    (la.coprod lb).HasBasis (fun i : ι × ι' => pa i.1 ∧ pb i.2) fun i =>
      Prod.fst ⁻¹' sa i.1 ∪ Prod.snd ⁻¹' sb i.2 :=
  (hla.comap Prod.fst).sup (hlb.comap Prod.snd)
#align filter.has_basis.coprod Filter.HasBasis.coprod

end TwoTypes

theorem map_sigma_mk_comap {π : α → Type*} {π' : β → Type*} {f : α → β}
    (hf : Function.Injective f) (g : ∀ a, π a → π' (f a)) (a : α) (l : Filter (π' (f a))) :
    map (Sigma.mk a) (comap (g a) l) = comap (Sigma.map f g) (map (Sigma.mk (f a)) l) := by
  refine (((basis_sets _).comap _).map _).eq_of_same_basis ?_
  convert ((basis_sets l).map (Sigma.mk (f a))).comap (Sigma.map f g)
  apply image_sigmaMk_preimage_sigmaMap hf
#align filter.map_sigma_mk_comap Filter.map_sigma_mk_comap

end Filter

end sort

namespace Filter

variable {α β γ ι : Type*} {ι' : Sort*}

/-- `IsCountablyGenerated f` means `f = generate s` for some countable `s`. -/
class IsCountablyGenerated (f : Filter α) : Prop where
  /-- There exists a countable set that generates the filter. -/
  out : ∃ s : Set (Set α), s.Countable ∧ f = generate s
#align filter.is_countably_generated Filter.IsCountablyGenerated

/-- `IsCountableBasis p s` means the image of `s` bounded by `p` is a countable filter basis. -/
structure IsCountableBasis (p : ι → Prop) (s : ι → Set α) extends IsBasis p s : Prop where
  /-- The set of `i` that satisfy the predicate `p` is countable. -/
  countable : (setOf p).Countable
#align filter.is_countable_basis Filter.IsCountableBasis

/-- We say that a filter `l` has a countable basis `s : ι → Set α` bounded by `p : ι → Prop`,
if `t ∈ l` if and only if `t` includes `s i` for some `i` such that `p i`, and the set
defined by `p` is countable. -/
structure HasCountableBasis (l : Filter α) (p : ι → Prop) (s : ι → Set α)
    extends HasBasis l p s : Prop where
  /-- The set of `i` that satisfy the predicate `p` is countable. -/
  countable : (setOf p).Countable
#align filter.has_countable_basis Filter.HasCountableBasis

/-- A countable filter basis `B` on a type `α` is a nonempty countable collection of sets of `α`
such that the intersection of two elements of this collection contains some element
of the collection. -/
structure CountableFilterBasis (α : Type*) extends FilterBasis α where
  /-- The set of sets of the filter basis is countable. -/
  countable : sets.Countable
#align filter.countable_filter_basis Filter.CountableFilterBasis

-- For illustration purposes, the countable filter basis defining `(atTop : Filter ℕ)`
instance Nat.inhabitedCountableFilterBasis : Inhabited (CountableFilterBasis ℕ) :=
  ⟨⟨default, countable_range fun n => Ici n⟩⟩
#align filter.nat.inhabited_countable_filter_basis Filter.Nat.inhabitedCountableFilterBasis

theorem HasCountableBasis.isCountablyGenerated {f : Filter α} {p : ι → Prop} {s : ι → Set α}
    (h : f.HasCountableBasis p s) : f.IsCountablyGenerated :=
  ⟨⟨{ t | ∃ i, p i ∧ s i = t }, h.countable.image s, h.toHasBasis.eq_generate⟩⟩
#align filter.has_countable_basis.is_countably_generated Filter.HasCountableBasis.isCountablyGenerated

theorem HasBasis.isCountablyGenerated [Countable ι] {f : Filter α} {p : ι → Prop} {s : ι → Set α}
    (h : f.HasBasis p s) : f.IsCountablyGenerated :=
  HasCountableBasis.isCountablyGenerated ⟨h, to_countable _⟩

theorem antitone_seq_of_seq (s : ℕ → Set α) :
    ∃ t : ℕ → Set α, Antitone t ∧ ⨅ i, 𝓟 (s i) = ⨅ i, 𝓟 (t i) := by
  use fun n => ⋂ m ≤ n, s m; constructor
  · exact fun i j hij => biInter_mono (Iic_subset_Iic.2 hij) fun n _ => Subset.rfl
  apply le_antisymm <;> rw [le_iInf_iff] <;> intro i
  · rw [le_principal_iff]
    refine (biInter_mem (finite_le_nat _)).2 fun j _ => ?_
    exact mem_iInf_of_mem j (mem_principal_self _)
  · refine iInf_le_of_le i (principal_mono.2 <| iInter₂_subset i ?_)
    rfl
#align filter.antitone_seq_of_seq Filter.antitone_seq_of_seq

theorem countable_biInf_eq_iInf_seq [CompleteLattice α] {B : Set ι} (Bcbl : B.Countable)
    (Bne : B.Nonempty) (f : ι → α) : ∃ x : ℕ → ι, ⨅ t ∈ B, f t = ⨅ i, f (x i) :=
  let ⟨g, hg⟩ := Bcbl.exists_eq_range Bne
  ⟨g, hg.symm ▸ iInf_range⟩
#align filter.countable_binfi_eq_infi_seq Filter.countable_biInf_eq_iInf_seq

theorem countable_biInf_eq_iInf_seq' [CompleteLattice α] {B : Set ι} (Bcbl : B.Countable)
    (f : ι → α) {i₀ : ι} (h : f i₀ = ⊤) : ∃ x : ℕ → ι, ⨅ t ∈ B, f t = ⨅ i, f (x i) := by
  rcases B.eq_empty_or_nonempty with hB | Bnonempty
  · rw [hB, iInf_emptyset]
    use fun _ => i₀
    simp [h]
  · exact countable_biInf_eq_iInf_seq Bcbl Bnonempty f
#align filter.countable_binfi_eq_infi_seq' Filter.countable_biInf_eq_iInf_seq'

theorem countable_biInf_principal_eq_seq_iInf {B : Set (Set α)} (Bcbl : B.Countable) :
    ∃ x : ℕ → Set α, ⨅ t ∈ B, 𝓟 t = ⨅ i, 𝓟 (x i) :=
  countable_biInf_eq_iInf_seq' Bcbl 𝓟 principal_univ
#align filter.countable_binfi_principal_eq_seq_infi Filter.countable_biInf_principal_eq_seq_iInf

section IsCountablyGenerated

protected theorem HasAntitoneBasis.mem_iff [Preorder ι] {l : Filter α} {s : ι → Set α}
    (hs : l.HasAntitoneBasis s) {t : Set α} : t ∈ l ↔ ∃ i, s i ⊆ t :=
  hs.toHasBasis.mem_iff.trans <| by simp only [exists_prop, true_and]
#align filter.has_antitone_basis.mem_iff Filter.HasAntitoneBasis.mem_iff

protected theorem HasAntitoneBasis.mem [Preorder ι] {l : Filter α} {s : ι → Set α}
    (hs : l.HasAntitoneBasis s) (i : ι) : s i ∈ l :=
  hs.toHasBasis.mem_of_mem trivial
#align filter.has_antitone_basis.mem Filter.HasAntitoneBasis.mem

theorem HasAntitoneBasis.hasBasis_ge [Preorder ι] [IsDirected ι (· ≤ ·)] {l : Filter α}
    {s : ι → Set α} (hs : l.HasAntitoneBasis s) (i : ι) : l.HasBasis (fun j => i ≤ j) s :=
  hs.1.to_hasBasis (fun j _ => (exists_ge_ge i j).imp fun _k hk => ⟨hk.1, hs.2 hk.2⟩) fun j _ =>
    ⟨j, trivial, Subset.rfl⟩
#align filter.has_antitone_basis.has_basis_ge Filter.HasAntitoneBasis.hasBasis_ge

/-- If `f` is countably generated and `f.HasBasis p s`, then `f` admits a decreasing basis
enumerated by natural numbers such that all sets have the form `s i`. More precisely, there is a
sequence `i n` such that `p (i n)` for all `n` and `s (i n)` is a decreasing sequence of sets which
forms a basis of `f`-/
theorem HasBasis.exists_antitone_subbasis {f : Filter α} [h : f.IsCountablyGenerated]
    {p : ι' → Prop} {s : ι' → Set α} (hs : f.HasBasis p s) :
    ∃ x : ℕ → ι', (∀ i, p (x i)) ∧ f.HasAntitoneBasis fun i => s (x i) := by
  obtain ⟨x', hx'⟩ : ∃ x : ℕ → Set α, f = ⨅ i, 𝓟 (x i) := by
    rcases h with ⟨s, hsc, rfl⟩
    rw [generate_eq_biInf]
    exact countable_biInf_principal_eq_seq_iInf hsc
  have : ∀ i, x' i ∈ f := fun i => hx'.symm ▸ (iInf_le (fun i => 𝓟 (x' i)) i) (mem_principal_self _)
  let x : ℕ → { i : ι' // p i } := fun n =>
    Nat.recOn n (hs.index _ <| this 0) fun n xn =>
      hs.index _ <| inter_mem (this <| n + 1) (hs.mem_of_mem xn.2)
  have x_anti : Antitone fun i => s (x i).1 :=
    antitone_nat_of_succ_le fun i => (hs.set_index_subset _).trans (inter_subset_right _ _)
  have x_subset : ∀ i, s (x i).1 ⊆ x' i := by
    rintro (_ | i)
    exacts [hs.set_index_subset _, (hs.set_index_subset _).trans (inter_subset_left _ _)]
  refine ⟨fun i => (x i).1, fun i => (x i).2, ?_⟩
  have : (⨅ i, 𝓟 (s (x i).1)).HasAntitoneBasis fun i => s (x i).1 := .iInf_principal x_anti
  convert this
  exact
    le_antisymm (le_iInf fun i => le_principal_iff.2 <| by cases i <;> apply hs.set_index_mem)
      (hx'.symm ▸
        le_iInf fun i => le_principal_iff.2 <| this.1.mem_iff.2 ⟨i, trivial, x_subset i⟩)
#align filter.has_basis.exists_antitone_subbasis Filter.HasBasis.exists_antitone_subbasis

/-- A countably generated filter admits a basis formed by an antitone sequence of sets. -/
theorem exists_antitone_basis (f : Filter α) [f.IsCountablyGenerated] :
    ∃ x : ℕ → Set α, f.HasAntitoneBasis x :=
  let ⟨x, _, hx⟩ := f.basis_sets.exists_antitone_subbasis
  ⟨x, hx⟩
#align filter.exists_antitone_basis Filter.exists_antitone_basis

theorem exists_antitone_seq (f : Filter α) [f.IsCountablyGenerated] :
    ∃ x : ℕ → Set α, Antitone x ∧ ∀ {s}, s ∈ f ↔ ∃ i, x i ⊆ s :=
  let ⟨x, hx⟩ := f.exists_antitone_basis
  ⟨x, hx.antitone, by simp [hx.1.mem_iff]⟩
#align filter.exists_antitone_seq Filter.exists_antitone_seq

instance Inf.isCountablyGenerated (f g : Filter α) [IsCountablyGenerated f]
    [IsCountablyGenerated g] : IsCountablyGenerated (f ⊓ g) := by
  rcases f.exists_antitone_basis with ⟨s, hs⟩
  rcases g.exists_antitone_basis with ⟨t, ht⟩
  exact HasCountableBasis.isCountablyGenerated ⟨hs.1.inf ht.1, Set.to_countable _⟩
#align filter.inf.is_countably_generated Filter.Inf.isCountablyGenerated

instance map.isCountablyGenerated (l : Filter α) [l.IsCountablyGenerated] (f : α → β) :
    (map f l).IsCountablyGenerated :=
  let ⟨_x, hxl⟩ := l.exists_antitone_basis
  (hxl.map _).isCountablyGenerated
#align filter.map.is_countably_generated Filter.map.isCountablyGenerated

instance comap.isCountablyGenerated (l : Filter β) [l.IsCountablyGenerated] (f : α → β) :
    (comap f l).IsCountablyGenerated :=
  let ⟨_x, hxl⟩ := l.exists_antitone_basis
  (hxl.comap _).isCountablyGenerated
#align filter.comap.is_countably_generated Filter.comap.isCountablyGenerated

instance Sup.isCountablyGenerated (f g : Filter α) [IsCountablyGenerated f]
    [IsCountablyGenerated g] : IsCountablyGenerated (f ⊔ g) := by
  rcases f.exists_antitone_basis with ⟨s, hs⟩
  rcases g.exists_antitone_basis with ⟨t, ht⟩
  exact HasCountableBasis.isCountablyGenerated ⟨hs.1.sup ht.1, Set.to_countable _⟩
#align filter.sup.is_countably_generated Filter.Sup.isCountablyGenerated

instance prod.isCountablyGenerated (la : Filter α) (lb : Filter β) [IsCountablyGenerated la]
    [IsCountablyGenerated lb] : IsCountablyGenerated (la ×ˢ lb) :=
  Filter.Inf.isCountablyGenerated _ _
#align filter.prod.is_countably_generated Filter.prod.isCountablyGenerated

instance coprod.isCountablyGenerated (la : Filter α) (lb : Filter β) [IsCountablyGenerated la]
    [IsCountablyGenerated lb] : IsCountablyGenerated (la.coprod lb) :=
  Filter.Sup.isCountablyGenerated _ _
#align filter.coprod.is_countably_generated Filter.coprod.isCountablyGenerated

end IsCountablyGenerated

theorem isCountablyGenerated_seq [Countable ι'] (x : ι' → Set α) :
    IsCountablyGenerated (⨅ i, 𝓟 (x i)) := by
  use range x, countable_range x
  rw [generate_eq_biInf, iInf_range]
#align filter.is_countably_generated_seq Filter.isCountablyGenerated_seq

theorem isCountablyGenerated_of_seq {f : Filter α} (h : ∃ x : ℕ → Set α, f = ⨅ i, 𝓟 (x i)) :
    f.IsCountablyGenerated := by
  rcases h with ⟨x, rfl⟩
  apply isCountablyGenerated_seq
#align filter.is_countably_generated_of_seq Filter.isCountablyGenerated_of_seq

theorem isCountablyGenerated_biInf_principal {B : Set (Set α)} (h : B.Countable) :
    IsCountablyGenerated (⨅ s ∈ B, 𝓟 s) :=
  isCountablyGenerated_of_seq (countable_biInf_principal_eq_seq_iInf h)
#align filter.is_countably_generated_binfi_principal Filter.isCountablyGenerated_biInf_principal

theorem isCountablyGenerated_iff_exists_antitone_basis {f : Filter α} :
    IsCountablyGenerated f ↔ ∃ x : ℕ → Set α, f.HasAntitoneBasis x := by
  constructor
  · intro h
    exact f.exists_antitone_basis
  · rintro ⟨x, h⟩
    rw [h.1.eq_iInf]
    exact isCountablyGenerated_seq x
#align filter.is_countably_generated_iff_exists_antitone_basis Filter.isCountablyGenerated_iff_exists_antitone_basis

@[instance]
theorem isCountablyGenerated_principal (s : Set α) : IsCountablyGenerated (𝓟 s) :=
  isCountablyGenerated_of_seq ⟨fun _ => s, iInf_const.symm⟩
#align filter.is_countably_generated_principal Filter.isCountablyGenerated_principal

@[instance]
theorem isCountablyGenerated_pure (a : α) : IsCountablyGenerated (pure a) := by
  rw [← principal_singleton]
  exact isCountablyGenerated_principal _
#align filter.is_countably_generated_pure Filter.isCountablyGenerated_pure

@[instance]
theorem isCountablyGenerated_bot : IsCountablyGenerated (⊥ : Filter α) :=
  @principal_empty α ▸ isCountablyGenerated_principal _
#align filter.is_countably_generated_bot Filter.isCountablyGenerated_bot

@[instance]
theorem isCountablyGenerated_top : IsCountablyGenerated (⊤ : Filter α) :=
  @principal_univ α ▸ isCountablyGenerated_principal _
#align filter.is_countably_generated_top Filter.isCountablyGenerated_top

-- Porting note: without explicit `Sort u` and `Type v`, Lean 4 uses `ι : Prop`
universe u v

instance iInf.isCountablyGenerated {ι : Sort u} {α : Type v} [Countable ι] (f : ι → Filter α)
    [∀ i, IsCountablyGenerated (f i)] : IsCountablyGenerated (⨅ i, f i) := by
  choose s hs using fun i => exists_antitone_basis (f i)
  rw [← PLift.down_surjective.iInf_comp]
  refine HasCountableBasis.isCountablyGenerated ⟨hasBasis_iInf fun n => (hs _).1, ?_⟩
  refine (countable_range <| Sigma.map ((↑) : Finset (PLift ι) → Set (PLift ι)) fun _ => id).mono ?_
  rintro ⟨I, f⟩ ⟨hI, -⟩
  lift I to Finset (PLift ι) using hI
  exact ⟨⟨I, f⟩, rfl⟩
#align filter.infi.is_countably_generated Filter.iInf.isCountablyGenerated

end Filter
