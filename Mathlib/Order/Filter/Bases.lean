/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Johannes Hölzl, Mario Carneiro, Patrick Massot

! This file was ported from Lean 3 source module order.filter.bases
! leanprover-community/mathlib commit d6fad0e5bf2d6f48da9175d25c3dc5706b3834ce
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Prod.Pprod
import Mathbin.Data.Set.Countable
import Mathbin.Order.Filter.Prod

/-!
# Filter bases

A filter basis `B : filter_basis α` on a type `α` is a nonempty collection of sets of `α`
such that the intersection of two elements of this collection contains some element of
the collection. Compared to filters, filter bases do not require that any set containing
an element of `B` belongs to `B`.
A filter basis `B` can be used to construct `B.filter : filter α` such that a set belongs
to `B.filter` if and only if it contains an element of `B`.

Given an indexing type `ι`, a predicate `p : ι → Prop`, and a map `s : ι → set α`,
the proposition `h : filter.is_basis p s` makes sure the range of `s` bounded by `p`
(ie. `s '' set_of p`) defines a filter basis `h.filter_basis`.

If one already has a filter `l` on `α`, `filter.has_basis l p s` (where `p : ι → Prop`
and `s : ι → set α` as above) means that a set belongs to `l` if and
only if it contains some `s i` with `p i`. It implies `h : filter.is_basis p s`, and
`l = h.filter_basis.filter`. The point of this definition is that checking statements
involving elements of `l` often reduces to checking them on the basis elements.

We define a function `has_basis.index (h : filter.has_basis l p s) (t) (ht : t ∈ l)` that returns
some index `i` such that `p i` and `s i ⊆ t`. This function can be useful to avoid manual
destruction of `h.mem_iff.mpr ht` using `cases` or `let`.

This file also introduces more restricted classes of bases, involving monotonicity or
countability. In particular, for `l : filter α`, `l.is_countably_generated` means
there is a countable set of sets which generates `s`. This is reformulated in term of bases,
and consequences are derived.

## Main statements

* `has_basis.mem_iff`, `has_basis.mem_of_superset`, `has_basis.mem_of_mem` : restate `t ∈ f`
  in terms of a basis;
* `basis_sets` : all sets of a filter form a basis;
* `has_basis.inf`, `has_basis.inf_principal`, `has_basis.prod`, `has_basis.prod_self`,
  `has_basis.map`, `has_basis.comap` : combinators to construct filters of `l ⊓ l'`,
  `l ⊓ 𝓟 t`, `l ×ᶠ l'`, `l ×ᶠ l`, `l.map f`, `l.comap f` respectively;
* `has_basis.le_iff`, `has_basis.ge_iff`, has_basis.le_basis_iff` : restate `l ≤ l'` in terms
  of bases.
* `has_basis.tendsto_right_iff`, `has_basis.tendsto_left_iff`, `has_basis.tendsto_iff` : restate
  `tendsto f l l'` in terms of bases.
* `is_countably_generated_iff_exists_antitone_basis` : proves a filter is
  countably generated if and only if it admits a basis parametrized by a
  decreasing sequence of sets indexed by `ℕ`.
* `tendsto_iff_seq_tendsto ` : an abstract version of "sequentially continuous implies continuous".

## Implementation notes

As with `Union`/`bUnion`/`sUnion`, there are three different approaches to filter bases:

* `has_basis l s`, `s : set (set α)`;
* `has_basis l s`, `s : ι → set α`;
* `has_basis l p s`, `p : ι → Prop`, `s : ι → set α`.

We use the latter one because, e.g., `𝓝 x` in an `emetric_space` or in a `metric_space` has a basis
of this form. The other two can be emulated using `s = id` or `p = λ _, true`.

With this approach sometimes one needs to `simp` the statement provided by the `has_basis`
machinery, e.g., `simp only [exists_prop, true_and]` or `simp only [forall_const]` can help
with the case `p = λ _, true`.
-/


open Set Filter

open Filter Classical

section Sort

variable {α β γ : Type _} {ι ι' : Sort _}

/-- A filter basis `B` on a type `α` is a nonempty collection of sets of `α`
such that the intersection of two elements of this collection contains some element
of the collection. -/
structure FilterBasis (α : Type _) where
  sets : Set (Set α)
  Nonempty : sets.Nonempty
  inter_sets {x y} : x ∈ sets → y ∈ sets → ∃ z ∈ sets, z ⊆ x ∩ y
#align filter_basis FilterBasis

instance FilterBasis.nonempty_sets (B : FilterBasis α) : Nonempty B.sets :=
  B.Nonempty.to_subtype
#align filter_basis.nonempty_sets FilterBasis.nonempty_sets

/-- If `B` is a filter basis on `α`, and `U` a subset of `α` then we can write `U ∈ B` as
on paper. -/
@[reducible]
instance {α : Type _} : Membership (Set α) (FilterBasis α) :=
  ⟨fun U B => U ∈ B.sets⟩

-- For illustration purposes, the filter basis defining (at_top : filter ℕ)
instance : Inhabited (FilterBasis ℕ) :=
  ⟨{  sets := range Ici
      Nonempty := ⟨Ici 0, mem_range_self 0⟩
      inter_sets := by
        rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
        refine' ⟨Ici (max n m), mem_range_self _, _⟩
        rintro p p_in
        constructor <;> rw [mem_Ici] at *
        exact le_of_max_le_left p_in
        exact le_of_max_le_right p_in }⟩

/-- View a filter as a filter basis. -/
def Filter.asBasis (f : Filter α) : FilterBasis α :=
  ⟨f.sets, ⟨univ, univ_mem⟩, fun x y hx hy => ⟨x ∩ y, inter_mem hx hy, subset_rfl⟩⟩
#align filter.as_basis Filter.asBasis

/-- `is_basis p s` means the image of `s` bounded by `p` is a filter basis. -/
protected structure Filter.IsBasis (p : ι → Prop) (s : ι → Set α) : Prop where
  Nonempty : ∃ i, p i
  inter : ∀ {i j}, p i → p j → ∃ k, p k ∧ s k ⊆ s i ∩ s j
#align filter.is_basis Filter.IsBasis

namespace Filter

namespace IsBasis

/-- Constructs a filter basis from an indexed family of sets satisfying `is_basis`. -/
protected def filterBasis {p : ι → Prop} {s : ι → Set α} (h : IsBasis p s) : FilterBasis α
    where
  sets := { t | ∃ i, p i ∧ s i = t }
  Nonempty :=
    let ⟨i, hi⟩ := h.Nonempty
    ⟨s i, ⟨i, hi, rfl⟩⟩
  inter_sets := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    rcases h.inter hi hj with ⟨k, hk, hk'⟩
    exact ⟨_, ⟨k, hk, rfl⟩, hk'⟩
#align filter.is_basis.filter_basis Filter.IsBasis.filterBasis

variable {p : ι → Prop} {s : ι → Set α} (h : IsBasis p s)

theorem mem_filterBasis_iff {U : Set α} : U ∈ h.FilterBasis ↔ ∃ i, p i ∧ s i = U :=
  Iff.rfl
#align filter.is_basis.mem_filter_basis_iff Filter.IsBasis.mem_filterBasis_iff

end IsBasis

end Filter

namespace FilterBasis

/-- The filter associated to a filter basis. -/
protected def filter (B : FilterBasis α) : Filter α
    where
  sets := { s | ∃ t ∈ B, t ⊆ s }
  univ_sets :=
    let ⟨s, s_in⟩ := B.Nonempty
    ⟨s, s_in, s.subset_univ⟩
  sets_of_superset := fun x y ⟨s, s_in, h⟩ hxy => ⟨s, s_in, Set.Subset.trans h hxy⟩
  inter_sets := fun x y ⟨s, s_in, hs⟩ ⟨t, t_in, ht⟩ =>
    let ⟨u, u_in, u_sub⟩ := B.inter_sets s_in t_in
    ⟨u, u_in, Set.Subset.trans u_sub <| Set.inter_subset_inter hs ht⟩
#align filter_basis.filter FilterBasis.filter

theorem mem_filter_iff (B : FilterBasis α) {U : Set α} : U ∈ B.filter ↔ ∃ s ∈ B, s ⊆ U :=
  Iff.rfl
#align filter_basis.mem_filter_iff FilterBasis.mem_filter_iff

theorem mem_filter_of_mem (B : FilterBasis α) {U : Set α} : U ∈ B → U ∈ B.filter := fun U_in =>
  ⟨U, U_in, Subset.refl _⟩
#align filter_basis.mem_filter_of_mem FilterBasis.mem_filter_of_mem

theorem eq_infᵢ_principal (B : FilterBasis α) : B.filter = ⨅ s : B.sets, 𝓟 s :=
  by
  have : Directed (· ≥ ·) fun s : B.sets => 𝓟 (s : Set α) :=
    by
    rintro ⟨U, U_in⟩ ⟨V, V_in⟩
    rcases B.inter_sets U_in V_in with ⟨W, W_in, W_sub⟩
    use W, W_in
    simp only [ge_iff_le, le_principal_iff, mem_principal, Subtype.coe_mk]
    exact subset_inter_iff.mp W_sub
  ext U
  simp [mem_filter_iff, mem_infi_of_directed this]
#align filter_basis.eq_infi_principal FilterBasis.eq_infᵢ_principal

protected theorem generate (B : FilterBasis α) : generate B.sets = B.filter :=
  by
  apply le_antisymm
  · intro U U_in
    rcases B.mem_filter_iff.mp U_in with ⟨V, V_in, h⟩
    exact generate_sets.superset (generate_sets.basic V_in) h
  · rw [sets_iff_generate]
    apply mem_filter_of_mem
#align filter_basis.generate FilterBasis.generate

end FilterBasis

namespace Filter

namespace IsBasis

variable {p : ι → Prop} {s : ι → Set α}

/-- Constructs a filter from an indexed family of sets satisfying `is_basis`. -/
protected def filter (h : IsBasis p s) : Filter α :=
  h.FilterBasis.filter
#align filter.is_basis.filter Filter.IsBasis.filter

protected theorem mem_filter_iff (h : IsBasis p s) {U : Set α} :
    U ∈ h.filter ↔ ∃ i, p i ∧ s i ⊆ U :=
  by
  erw [h.filter_basis.mem_filter_iff]
  simp only [mem_filter_basis_iff h, exists_prop]
  constructor
  · rintro ⟨_, ⟨i, pi, rfl⟩, h⟩
    tauto
  · tauto
#align filter.is_basis.mem_filter_iff Filter.IsBasis.mem_filter_iff

theorem filter_eq_generate (h : IsBasis p s) : h.filter = generate { U | ∃ i, p i ∧ s i = U } := by
  erw [h.filter_basis.generate] <;> rfl
#align filter.is_basis.filter_eq_generate Filter.IsBasis.filter_eq_generate

end IsBasis

/-- We say that a filter `l` has a basis `s : ι → set α` bounded by `p : ι → Prop`,
if `t ∈ l` if and only if `t` includes `s i` for some `i` such that `p i`. -/
protected structure HasBasis (l : Filter α) (p : ι → Prop) (s : ι → Set α) : Prop where
  mem_iff' : ∀ t : Set α, t ∈ l ↔ ∃ (i : _)(hi : p i), s i ⊆ t
#align filter.has_basis Filter.HasBasis

section SameType

variable {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {t : Set α} {i : ι} {p' : ι' → Prop}
  {s' : ι' → Set α} {i' : ι'}

theorem hasBasis_generate (s : Set (Set α)) :
    (generate s).HasBasis (fun t => Set.Finite t ∧ t ⊆ s) fun t => ⋂₀ t :=
  ⟨fun U => by simp only [mem_generate_iff, exists_prop, and_assoc, and_left_comm]⟩
#align filter.has_basis_generate Filter.hasBasis_generate

/-- The smallest filter basis containing a given collection of sets. -/
def FilterBasis.ofSets (s : Set (Set α)) : FilterBasis α
    where
  sets := sInter '' { t | Set.Finite t ∧ t ⊆ s }
  Nonempty := ⟨univ, ∅, ⟨⟨finite_empty, empty_subset s⟩, interₛ_empty⟩⟩
  inter_sets := by
    rintro _ _ ⟨a, ⟨fina, suba⟩, rfl⟩ ⟨b, ⟨finb, subb⟩, rfl⟩
    exact
      ⟨⋂₀ (a ∪ b), mem_image_of_mem _ ⟨fina.union finb, union_subset suba subb⟩, by
        rw [sInter_union]⟩
#align filter.filter_basis.of_sets Filter.FilterBasis.ofSets

/-- Definition of `has_basis` unfolded with implicit set argument. -/
theorem HasBasis.mem_iff (hl : l.HasBasis p s) : t ∈ l ↔ ∃ (i : _)(hi : p i), s i ⊆ t :=
  hl.mem_iff' t
#align filter.has_basis.mem_iff Filter.HasBasis.mem_iff

theorem HasBasis.eq_of_same_basis (hl : l.HasBasis p s) (hl' : l'.HasBasis p s) : l = l' :=
  by
  ext t
  rw [hl.mem_iff, hl'.mem_iff]
#align filter.has_basis.eq_of_same_basis Filter.HasBasis.eq_of_same_basis

theorem hasBasis_iff : l.HasBasis p s ↔ ∀ t, t ∈ l ↔ ∃ (i : _)(hi : p i), s i ⊆ t :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩
#align filter.has_basis_iff Filter.hasBasis_iff

theorem HasBasis.ex_mem (h : l.HasBasis p s) : ∃ i, p i :=
  let ⟨i, pi, h⟩ := h.mem_iff.mp univ_mem
  ⟨i, pi⟩
#align filter.has_basis.ex_mem Filter.HasBasis.ex_mem

protected theorem HasBasis.nonempty (h : l.HasBasis p s) : Nonempty ι :=
  nonempty_of_exists h.ex_mem
#align filter.has_basis.nonempty Filter.HasBasis.nonempty

protected theorem IsBasis.hasBasis (h : IsBasis p s) : HasBasis h.filter p s :=
  ⟨fun t => by simp only [h.mem_filter_iff, exists_prop]⟩
#align filter.is_basis.has_basis Filter.IsBasis.hasBasis

theorem HasBasis.mem_of_superset (hl : l.HasBasis p s) (hi : p i) (ht : s i ⊆ t) : t ∈ l :=
  hl.mem_iff.2 ⟨i, hi, ht⟩
#align filter.has_basis.mem_of_superset Filter.HasBasis.mem_of_superset

theorem HasBasis.mem_of_mem (hl : l.HasBasis p s) (hi : p i) : s i ∈ l :=
  hl.mem_of_superset hi <| Subset.refl _
#align filter.has_basis.mem_of_mem Filter.HasBasis.mem_of_mem

/-- Index of a basis set such that `s i ⊆ t` as an element of `subtype p`. -/
noncomputable def HasBasis.index (h : l.HasBasis p s) (t : Set α) (ht : t ∈ l) : { i : ι // p i } :=
  ⟨(h.mem_iff.1 ht).some, (h.mem_iff.1 ht).some_spec.fst⟩
#align filter.has_basis.index Filter.HasBasis.index

theorem HasBasis.property_index (h : l.HasBasis p s) (ht : t ∈ l) : p (h.index t ht) :=
  (h.index t ht).2
#align filter.has_basis.property_index Filter.HasBasis.property_index

theorem HasBasis.set_index_mem (h : l.HasBasis p s) (ht : t ∈ l) : s (h.index t ht) ∈ l :=
  h.mem_of_mem <| h.property_index _
#align filter.has_basis.set_index_mem Filter.HasBasis.set_index_mem

theorem HasBasis.set_index_subset (h : l.HasBasis p s) (ht : t ∈ l) : s (h.index t ht) ⊆ t :=
  (h.mem_iff.1 ht).some_spec.snd
#align filter.has_basis.set_index_subset Filter.HasBasis.set_index_subset

theorem HasBasis.isBasis (h : l.HasBasis p s) : IsBasis p s :=
  { Nonempty :=
      let ⟨i, hi, H⟩ := h.mem_iff.mp univ_mem
      ⟨i, hi⟩
    inter := fun i j hi hj => by
      simpa [h.mem_iff] using l.inter_sets (h.mem_of_mem hi) (h.mem_of_mem hj) }
#align filter.has_basis.is_basis Filter.HasBasis.isBasis

theorem HasBasis.filter_eq (h : l.HasBasis p s) : h.IsBasis.filter = l :=
  by
  ext U
  simp [h.mem_iff, is_basis.mem_filter_iff]
#align filter.has_basis.filter_eq Filter.HasBasis.filter_eq

theorem HasBasis.eq_generate (h : l.HasBasis p s) : l = generate { U | ∃ i, p i ∧ s i = U } := by
  rw [← h.is_basis.filter_eq_generate, h.filter_eq]
#align filter.has_basis.eq_generate Filter.HasBasis.eq_generate

theorem generate_eq_generate_inter (s : Set (Set α)) :
    generate s = generate (sInter '' { t | Set.Finite t ∧ t ⊆ s }) := by
  erw [(filter_basis.of_sets s).generate, ← (has_basis_generate s).filter_eq] <;> rfl
#align filter.generate_eq_generate_inter Filter.generate_eq_generate_inter

theorem ofSets_filter_eq_generate (s : Set (Set α)) : (FilterBasis.ofSets s).filter = generate s :=
  by rw [← (filter_basis.of_sets s).generate, generate_eq_generate_inter s] <;> rfl
#align filter.of_sets_filter_eq_generate Filter.ofSets_filter_eq_generate

protected theorem FilterBasis.hasBasis {α : Type _} (B : FilterBasis α) :
    HasBasis B.filter (fun s : Set α => s ∈ B) id :=
  ⟨fun t => B.mem_filter_iff⟩
#align filter_basis.has_basis FilterBasis.hasBasis

theorem HasBasis.to_has_basis' (hl : l.HasBasis p s) (h : ∀ i, p i → ∃ i', p' i' ∧ s' i' ⊆ s i)
    (h' : ∀ i', p' i' → s' i' ∈ l) : l.HasBasis p' s' :=
  by
  refine' ⟨fun t => ⟨fun ht => _, fun ⟨i', hi', ht⟩ => mem_of_superset (h' i' hi') ht⟩⟩
  rcases hl.mem_iff.1 ht with ⟨i, hi, ht⟩
  rcases h i hi with ⟨i', hi', hs's⟩
  exact ⟨i', hi', subset.trans hs's ht⟩
#align filter.has_basis.to_has_basis' Filter.HasBasis.to_has_basis'

theorem HasBasis.to_hasBasis (hl : l.HasBasis p s) (h : ∀ i, p i → ∃ i', p' i' ∧ s' i' ⊆ s i)
    (h' : ∀ i', p' i' → ∃ i, p i ∧ s i ⊆ s' i') : l.HasBasis p' s' :=
  hl.to_has_basis' h fun i' hi' =>
    let ⟨i, hi, hss'⟩ := h' i' hi'
    hl.mem_iff.2 ⟨i, hi, hss'⟩
#align filter.has_basis.to_has_basis Filter.HasBasis.to_hasBasis

theorem HasBasis.to_subset (hl : l.HasBasis p s) {t : ι → Set α} (h : ∀ i, p i → t i ⊆ s i)
    (ht : ∀ i, p i → t i ∈ l) : l.HasBasis p t :=
  hl.to_has_basis' (fun i hi => ⟨i, hi, h i hi⟩) ht
#align filter.has_basis.to_subset Filter.HasBasis.to_subset

theorem HasBasis.eventually_iff (hl : l.HasBasis p s) {q : α → Prop} :
    (∀ᶠ x in l, q x) ↔ ∃ i, p i ∧ ∀ ⦃x⦄, x ∈ s i → q x := by simpa using hl.mem_iff
#align filter.has_basis.eventually_iff Filter.HasBasis.eventually_iff

theorem HasBasis.frequently_iff (hl : l.HasBasis p s) {q : α → Prop} :
    (∃ᶠ x in l, q x) ↔ ∀ i, p i → ∃ x ∈ s i, q x := by simp [Filter.Frequently, hl.eventually_iff]
#align filter.has_basis.frequently_iff Filter.HasBasis.frequently_iff

theorem HasBasis.exists_iff (hl : l.HasBasis p s) {P : Set α → Prop}
    (mono : ∀ ⦃s t⦄, s ⊆ t → P t → P s) : (∃ s ∈ l, P s) ↔ ∃ (i : _)(hi : p i), P (s i) :=
  ⟨fun ⟨s, hs, hP⟩ =>
    let ⟨i, hi, his⟩ := hl.mem_iff.1 hs
    ⟨i, hi, mono his hP⟩,
    fun ⟨i, hi, hP⟩ => ⟨s i, hl.mem_of_mem hi, hP⟩⟩
#align filter.has_basis.exists_iff Filter.HasBasis.exists_iff

theorem HasBasis.forall_iff (hl : l.HasBasis p s) {P : Set α → Prop}
    (mono : ∀ ⦃s t⦄, s ⊆ t → P s → P t) : (∀ s ∈ l, P s) ↔ ∀ i, p i → P (s i) :=
  ⟨fun H i hi => H (s i) <| hl.mem_of_mem hi, fun H s hs =>
    let ⟨i, hi, his⟩ := hl.mem_iff.1 hs
    mono his (H i hi)⟩
#align filter.has_basis.forall_iff Filter.HasBasis.forall_iff

theorem HasBasis.neBot_iff (hl : l.HasBasis p s) : NeBot l ↔ ∀ {i}, p i → (s i).Nonempty :=
  forall_mem_nonempty_iff_neBot.symm.trans <| hl.forall_iff fun _ _ => Nonempty.mono
#align filter.has_basis.ne_bot_iff Filter.HasBasis.neBot_iff

theorem HasBasis.eq_bot_iff (hl : l.HasBasis p s) : l = ⊥ ↔ ∃ i, p i ∧ s i = ∅ :=
  not_iff_not.1 <|
    neBot_iff.symm.trans <|
      hl.ne_bot_iff.trans <| by simp only [not_exists, not_and, nonempty_iff_ne_empty]
#align filter.has_basis.eq_bot_iff Filter.HasBasis.eq_bot_iff

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (t «expr ⊆ » s) -/
theorem generate_neBot_iff {s : Set (Set α)} :
    NeBot (generate s) ↔ ∀ (t) (_ : t ⊆ s), t.Finite → (⋂₀ t).Nonempty :=
  (hasBasis_generate s).ne_bot_iff.trans <| by simp only [← and_imp, and_comm']
#align filter.generate_ne_bot_iff Filter.generate_neBot_iff

theorem basis_sets (l : Filter α) : l.HasBasis (fun s : Set α => s ∈ l) id :=
  ⟨fun t => exists_mem_subset_iff.symm⟩
#align filter.basis_sets Filter.basis_sets

theorem asBasis_filter (f : Filter α) : f.asBasis.filter = f := by
  ext t <;> exact exists_mem_subset_iff
#align filter.as_basis_filter Filter.asBasis_filter

theorem hasBasis_self {l : Filter α} {P : Set α → Prop} :
    HasBasis l (fun s => s ∈ l ∧ P s) id ↔ ∀ t ∈ l, ∃ r ∈ l, P r ∧ r ⊆ t :=
  by
  simp only [has_basis_iff, exists_prop, id, and_assoc']
  exact
    forall_congr' fun s =>
      ⟨fun h => h.1, fun h => ⟨h, fun ⟨t, hl, hP, hts⟩ => mem_of_superset hl hts⟩⟩
#align filter.has_basis_self Filter.hasBasis_self

theorem HasBasis.comp_of_surjective (h : l.HasBasis p s) {g : ι' → ι} (hg : Function.Surjective g) :
    l.HasBasis (p ∘ g) (s ∘ g) :=
  ⟨fun t => h.mem_iff.trans hg.exists⟩
#align filter.has_basis.comp_of_surjective Filter.HasBasis.comp_of_surjective

theorem HasBasis.comp_equiv (h : l.HasBasis p s) (e : ι' ≃ ι) : l.HasBasis (p ∘ e) (s ∘ e) :=
  h.comp_of_surjective e.Surjective
#align filter.has_basis.comp_equiv Filter.HasBasis.comp_equiv

/-- If `{s i | p i}` is a basis of a filter `l` and each `s i` includes `s j` such that
`p j ∧ q j`, then `{s j | p j ∧ q j}` is a basis of `l`. -/
theorem HasBasis.restrict (h : l.HasBasis p s) {q : ι → Prop}
    (hq : ∀ i, p i → ∃ j, p j ∧ q j ∧ s j ⊆ s i) : l.HasBasis (fun i => p i ∧ q i) s :=
  by
  refine' ⟨fun t => ⟨fun ht => _, fun ⟨i, hpi, hti⟩ => h.mem_iff.2 ⟨i, hpi.1, hti⟩⟩⟩
  rcases h.mem_iff.1 ht with ⟨i, hpi, hti⟩
  rcases hq i hpi with ⟨j, hpj, hqj, hji⟩
  exact ⟨j, ⟨hpj, hqj⟩, subset.trans hji hti⟩
#align filter.has_basis.restrict Filter.HasBasis.restrict

/-- If `{s i | p i}` is a basis of a filter `l` and `V ∈ l`, then `{s i | p i ∧ s i ⊆ V}`
is a basis of `l`. -/
theorem HasBasis.restrict_subset (h : l.HasBasis p s) {V : Set α} (hV : V ∈ l) :
    l.HasBasis (fun i => p i ∧ s i ⊆ V) s :=
  h.restrict fun i hi =>
    (h.mem_iff.1 (inter_mem hV (h.mem_of_mem hi))).imp fun j hj =>
      ⟨hj.fst, subset_inter_iff.1 hj.snd⟩
#align filter.has_basis.restrict_subset Filter.HasBasis.restrict_subset

theorem HasBasis.hasBasis_self_subset {p : Set α → Prop} (h : l.HasBasis (fun s => s ∈ l ∧ p s) id)
    {V : Set α} (hV : V ∈ l) : l.HasBasis (fun s => s ∈ l ∧ p s ∧ s ⊆ V) id := by
  simpa only [and_assoc'] using h.restrict_subset hV
#align filter.has_basis.has_basis_self_subset Filter.HasBasis.hasBasis_self_subset

theorem HasBasis.ge_iff (hl' : l'.HasBasis p' s') : l ≤ l' ↔ ∀ i', p' i' → s' i' ∈ l :=
  ⟨fun h i' hi' => h <| hl'.mem_of_mem hi', fun h s hs =>
    let ⟨i', hi', hs⟩ := hl'.mem_iff.1 hs
    mem_of_superset (h _ hi') hs⟩
#align filter.has_basis.ge_iff Filter.HasBasis.ge_iff

theorem HasBasis.le_iff (hl : l.HasBasis p s) : l ≤ l' ↔ ∀ t ∈ l', ∃ (i : _)(hi : p i), s i ⊆ t :=
  by simp only [le_def, hl.mem_iff]
#align filter.has_basis.le_iff Filter.HasBasis.le_iff

theorem HasBasis.le_basis_iff (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    l ≤ l' ↔ ∀ i', p' i' → ∃ (i : _)(hi : p i), s i ⊆ s' i' := by simp only [hl'.ge_iff, hl.mem_iff]
#align filter.has_basis.le_basis_iff Filter.HasBasis.le_basis_iff

theorem HasBasis.ext (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s')
    (h : ∀ i, p i → ∃ i', p' i' ∧ s' i' ⊆ s i) (h' : ∀ i', p' i' → ∃ i, p i ∧ s i ⊆ s' i') :
    l = l' := by
  apply le_antisymm
  · rw [hl.le_basis_iff hl']
    simpa using h'
  · rw [hl'.le_basis_iff hl]
    simpa using h
#align filter.has_basis.ext Filter.HasBasis.ext

theorem HasBasis.inf' (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    (l ⊓ l').HasBasis (fun i : PProd ι ι' => p i.1 ∧ p' i.2) fun i => s i.1 ∩ s' i.2 :=
  ⟨by
    intro t
    constructor
    · simp only [mem_inf_iff, exists_prop, hl.mem_iff, hl'.mem_iff]
      rintro ⟨t, ⟨i, hi, ht⟩, t', ⟨i', hi', ht'⟩, rfl⟩
      use ⟨i, i'⟩, ⟨hi, hi'⟩, inter_subset_inter ht ht'
    · rintro ⟨⟨i, i'⟩, ⟨hi, hi'⟩, H⟩
      exact mem_inf_of_inter (hl.mem_of_mem hi) (hl'.mem_of_mem hi') H⟩
#align filter.has_basis.inf' Filter.HasBasis.inf'

theorem HasBasis.inf {ι ι' : Type _} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}
    {s' : ι' → Set α} (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    (l ⊓ l').HasBasis (fun i : ι × ι' => p i.1 ∧ p' i.2) fun i => s i.1 ∩ s' i.2 :=
  (hl.inf' hl').to_has_basis (fun i hi => ⟨⟨i.1, i.2⟩, hi, Subset.rfl⟩) fun i hi =>
    ⟨⟨i.1, i.2⟩, hi, Subset.rfl⟩
#align filter.has_basis.inf Filter.HasBasis.inf

theorem hasBasis_infi' {ι : Type _} {ι' : ι → Type _} {l : ι → Filter α} {p : ∀ i, ι' i → Prop}
    {s : ∀ i, ι' i → Set α} (hl : ∀ i, (l i).HasBasis (p i) (s i)) :
    (⨅ i, l i).HasBasis (fun If : Set ι × ∀ i, ι' i => If.1.Finite ∧ ∀ i ∈ If.1, p i (If.2 i))
      fun If : Set ι × ∀ i, ι' i => ⋂ i ∈ If.1, s i (If.2 i) :=
  ⟨by
    intro t
    constructor
    · simp only [mem_infi', (hl _).mem_iff]
      rintro ⟨I, hI, V, hV, -, rfl, -⟩
      choose u hu using hV
      exact ⟨⟨I, u⟩, ⟨hI, fun i _ => (hu i).1⟩, Inter_mono fun i => Inter_mono fun hi => (hu i).2⟩
    · rintro ⟨⟨I, f⟩, ⟨hI₁, hI₂⟩, hsub⟩
      refine' mem_of_superset _ hsub
      exact (bInter_mem hI₁).mpr fun i hi => mem_infi_of_mem i <| (hl i).mem_of_mem <| hI₂ _ hi⟩
#align filter.has_basis_infi' Filter.hasBasis_infi'

theorem hasBasis_infᵢ {ι : Type _} {ι' : ι → Type _} {l : ι → Filter α} {p : ∀ i, ι' i → Prop}
    {s : ∀ i, ι' i → Set α} (hl : ∀ i, (l i).HasBasis (p i) (s i)) :
    (⨅ i, l i).HasBasis
      (fun If : ΣI : Set ι, ∀ i : I, ι' i => If.1.Finite ∧ ∀ i : If.1, p i (If.2 i)) fun If =>
      ⋂ i : If.1, s i (If.2 i) :=
  by
  refine' ⟨fun t => ⟨fun ht => _, _⟩⟩
  · rcases(has_basis_infi' hl).mem_iff.mp ht with ⟨⟨I, f⟩, ⟨hI, hf⟩, hsub⟩
    exact
      ⟨⟨I, fun i => f i⟩, ⟨hI, subtype.forall.mpr hf⟩, trans_rel_right _ (Inter_subtype _ _) hsub⟩
  · rintro ⟨⟨I, f⟩, ⟨hI, hf⟩, hsub⟩
    refine' mem_of_superset _ hsub
    cases hI.nonempty_fintype
    exact Inter_mem.2 fun i => mem_infi_of_mem i <| (hl i).mem_of_mem <| hf _
#align filter.has_basis_infi Filter.hasBasis_infᵢ

theorem hasBasis_infᵢ_of_directed' {ι : Type _} {ι' : ι → Sort _} [Nonempty ι] {l : ι → Filter α}
    (s : ∀ i, ι' i → Set α) (p : ∀ i, ι' i → Prop) (hl : ∀ i, (l i).HasBasis (p i) (s i))
    (h : Directed (· ≥ ·) l) :
    (⨅ i, l i).HasBasis (fun ii' : Σi, ι' i => p ii'.1 ii'.2) fun ii' => s ii'.1 ii'.2 :=
  by
  refine' ⟨fun t => _⟩
  rw [mem_infi_of_directed h, Sigma.exists]
  exact exists_congr fun i => (hl i).mem_iff
#align filter.has_basis_infi_of_directed' Filter.hasBasis_infᵢ_of_directed'

theorem hasBasis_infᵢ_of_directed {ι : Type _} {ι' : Sort _} [Nonempty ι] {l : ι → Filter α}
    (s : ι → ι' → Set α) (p : ι → ι' → Prop) (hl : ∀ i, (l i).HasBasis (p i) (s i))
    (h : Directed (· ≥ ·) l) :
    (⨅ i, l i).HasBasis (fun ii' : ι × ι' => p ii'.1 ii'.2) fun ii' => s ii'.1 ii'.2 :=
  by
  refine' ⟨fun t => _⟩
  rw [mem_infi_of_directed h, Prod.exists]
  exact exists_congr fun i => (hl i).mem_iff
#align filter.has_basis_infi_of_directed Filter.hasBasis_infᵢ_of_directed

theorem hasBasis_binfi_of_directed' {ι : Type _} {ι' : ι → Sort _} {dom : Set ι}
    (hdom : dom.Nonempty) {l : ι → Filter α} (s : ∀ i, ι' i → Set α) (p : ∀ i, ι' i → Prop)
    (hl : ∀ i ∈ dom, (l i).HasBasis (p i) (s i)) (h : DirectedOn (l ⁻¹'o GE.ge) dom) :
    (⨅ i ∈ dom, l i).HasBasis (fun ii' : Σi, ι' i => ii'.1 ∈ dom ∧ p ii'.1 ii'.2) fun ii' =>
      s ii'.1 ii'.2 :=
  by
  refine' ⟨fun t => _⟩
  rw [mem_binfi_of_directed h hdom, Sigma.exists]
  refine' exists_congr fun i => ⟨_, _⟩
  · rintro ⟨hi, hti⟩
    rcases(hl i hi).mem_iff.mp hti with ⟨b, hb, hbt⟩
    exact ⟨b, ⟨hi, hb⟩, hbt⟩
  · rintro ⟨b, ⟨hi, hb⟩, hibt⟩
    exact ⟨hi, (hl i hi).mem_iff.mpr ⟨b, hb, hibt⟩⟩
#align filter.has_basis_binfi_of_directed' Filter.hasBasis_binfi_of_directed'

theorem hasBasis_binfi_of_directed {ι : Type _} {ι' : Sort _} {dom : Set ι} (hdom : dom.Nonempty)
    {l : ι → Filter α} (s : ι → ι' → Set α) (p : ι → ι' → Prop)
    (hl : ∀ i ∈ dom, (l i).HasBasis (p i) (s i)) (h : DirectedOn (l ⁻¹'o GE.ge) dom) :
    (⨅ i ∈ dom, l i).HasBasis (fun ii' : ι × ι' => ii'.1 ∈ dom ∧ p ii'.1 ii'.2) fun ii' =>
      s ii'.1 ii'.2 :=
  by
  refine' ⟨fun t => _⟩
  rw [mem_binfi_of_directed h hdom, Prod.exists]
  refine' exists_congr fun i => ⟨_, _⟩
  · rintro ⟨hi, hti⟩
    rcases(hl i hi).mem_iff.mp hti with ⟨b, hb, hbt⟩
    exact ⟨b, ⟨hi, hb⟩, hbt⟩
  · rintro ⟨b, ⟨hi, hb⟩, hibt⟩
    exact ⟨hi, (hl i hi).mem_iff.mpr ⟨b, hb, hibt⟩⟩
#align filter.has_basis_binfi_of_directed Filter.hasBasis_binfi_of_directed

theorem hasBasis_principal (t : Set α) : (𝓟 t).HasBasis (fun i : Unit => True) fun i => t :=
  ⟨fun U => by simp⟩
#align filter.has_basis_principal Filter.hasBasis_principal

theorem hasBasis_pure (x : α) : (pure x : Filter α).HasBasis (fun i : Unit => True) fun i => {x} :=
  by simp only [← principal_singleton, has_basis_principal]
#align filter.has_basis_pure Filter.hasBasis_pure

theorem HasBasis.sup' (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    (l ⊔ l').HasBasis (fun i : PProd ι ι' => p i.1 ∧ p' i.2) fun i => s i.1 ∪ s' i.2 :=
  ⟨by
    intro t
    simp only [mem_sup, hl.mem_iff, hl'.mem_iff, PProd.exists, union_subset_iff, exists_prop,
      and_assoc', exists_and_left]
    simp only [← and_assoc', exists_and_right, and_comm']⟩
#align filter.has_basis.sup' Filter.HasBasis.sup'

theorem HasBasis.sup {ι ι' : Type _} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}
    {s' : ι' → Set α} (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    (l ⊔ l').HasBasis (fun i : ι × ι' => p i.1 ∧ p' i.2) fun i => s i.1 ∪ s' i.2 :=
  (hl.sup' hl').to_has_basis (fun i hi => ⟨⟨i.1, i.2⟩, hi, Subset.rfl⟩) fun i hi =>
    ⟨⟨i.1, i.2⟩, hi, Subset.rfl⟩
#align filter.has_basis.sup Filter.HasBasis.sup

theorem hasBasis_supᵢ {ι : Sort _} {ι' : ι → Type _} {l : ι → Filter α} {p : ∀ i, ι' i → Prop}
    {s : ∀ i, ι' i → Set α} (hl : ∀ i, (l i).HasBasis (p i) (s i)) :
    (⨆ i, l i).HasBasis (fun f : ∀ i, ι' i => ∀ i, p i (f i)) fun f : ∀ i, ι' i => ⋃ i, s i (f i) :=
  hasBasis_iff.mpr fun t => by
    simp only [has_basis_iff, (hl _).mem_iff, Classical.skolem, forall_and, Union_subset_iff,
      mem_supr]
#align filter.has_basis_supr Filter.hasBasis_supᵢ

theorem HasBasis.sup_principal (hl : l.HasBasis p s) (t : Set α) :
    (l ⊔ 𝓟 t).HasBasis p fun i => s i ∪ t :=
  ⟨fun u => by
    simp only [(hl.sup' (has_basis_principal t)).mem_iff, PProd.exists, exists_prop, and_true_iff,
      Unique.exists_iff]⟩
#align filter.has_basis.sup_principal Filter.HasBasis.sup_principal

theorem HasBasis.sup_pure (hl : l.HasBasis p s) (x : α) :
    (l ⊔ pure x).HasBasis p fun i => s i ∪ {x} := by
  simp only [← principal_singleton, hl.sup_principal]
#align filter.has_basis.sup_pure Filter.HasBasis.sup_pure

theorem HasBasis.inf_principal (hl : l.HasBasis p s) (s' : Set α) :
    (l ⊓ 𝓟 s').HasBasis p fun i => s i ∩ s' :=
  ⟨fun t => by
    simp only [mem_inf_principal, hl.mem_iff, subset_def, mem_set_of_eq, mem_inter_iff, and_imp]⟩
#align filter.has_basis.inf_principal Filter.HasBasis.inf_principal

theorem HasBasis.principal_inf (hl : l.HasBasis p s) (s' : Set α) :
    (𝓟 s' ⊓ l).HasBasis p fun i => s' ∩ s i := by
  simpa only [inf_comm, inter_comm] using hl.inf_principal s'
#align filter.has_basis.principal_inf Filter.HasBasis.principal_inf

theorem HasBasis.inf_basis_neBot_iff (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    NeBot (l ⊓ l') ↔ ∀ ⦃i⦄ (hi : p i) ⦃i'⦄ (hi' : p' i'), (s i ∩ s' i').Nonempty :=
  (hl.inf' hl').ne_bot_iff.trans <| by simp [@forall_swap _ ι']
#align filter.has_basis.inf_basis_ne_bot_iff Filter.HasBasis.inf_basis_neBot_iff

theorem HasBasis.inf_neBot_iff (hl : l.HasBasis p s) :
    NeBot (l ⊓ l') ↔ ∀ ⦃i⦄ (hi : p i) ⦃s'⦄ (hs' : s' ∈ l'), (s i ∩ s').Nonempty :=
  hl.inf_basis_ne_bot_iff l'.basis_sets
#align filter.has_basis.inf_ne_bot_iff Filter.HasBasis.inf_neBot_iff

theorem HasBasis.inf_principal_neBot_iff (hl : l.HasBasis p s) {t : Set α} :
    NeBot (l ⊓ 𝓟 t) ↔ ∀ ⦃i⦄ (hi : p i), (s i ∩ t).Nonempty :=
  (hl.inf_principal t).ne_bot_iff
#align filter.has_basis.inf_principal_ne_bot_iff Filter.HasBasis.inf_principal_neBot_iff

theorem HasBasis.disjoint_iff (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    Disjoint l l' ↔ ∃ (i : _)(hi : p i)(i' : _)(hi' : p' i'), Disjoint (s i) (s' i') :=
  not_iff_not.mp <| by
    simp only [disjoint_iff, ← Ne.def, ← ne_bot_iff, hl.inf_basis_ne_bot_iff hl', not_exists,
      bot_eq_empty, ← nonempty_iff_ne_empty, inf_eq_inter]
#align filter.has_basis.disjoint_iff Filter.HasBasis.disjoint_iff

theorem Disjoint.exists_mem_filter_basis (h : Disjoint l l') (hl : l.HasBasis p s)
    (hl' : l'.HasBasis p' s') : ∃ (i : _)(hi : p i)(i' : _)(hi' : p' i'), Disjoint (s i) (s' i') :=
  (hl.disjoint_iff hl').1 h
#align disjoint.exists_mem_filter_basis Disjoint.exists_mem_filter_basis

theorem Pairwise.exists_mem_filter_basis_of_disjoint {I : Type _} [Finite I] {l : I → Filter α}
    {ι : I → Sort _} {p : ∀ i, ι i → Prop} {s : ∀ i, ι i → Set α} (hd : Pairwise (Disjoint on l))
    (h : ∀ i, (l i).HasBasis (p i) (s i)) :
    ∃ ind : ∀ i, ι i, (∀ i, p i (ind i)) ∧ Pairwise (Disjoint on fun i => s i (ind i)) :=
  by
  rcases hd.exists_mem_filter_of_disjoint with ⟨t, htl, hd⟩
  choose ind hp ht using fun i => (h i).mem_iff.1 (htl i)
  exact ⟨ind, hp, hd.mono fun i j hij => hij.mono (ht _) (ht _)⟩
#align pairwise.exists_mem_filter_basis_of_disjoint Pairwise.exists_mem_filter_basis_of_disjoint

theorem Set.PairwiseDisjoint.exists_mem_filter_basis {I : Type _} {l : I → Filter α}
    {ι : I → Sort _} {p : ∀ i, ι i → Prop} {s : ∀ i, ι i → Set α} {S : Set I}
    (hd : S.PairwiseDisjoint l) (hS : S.Finite) (h : ∀ i, (l i).HasBasis (p i) (s i)) :
    ∃ ind : ∀ i, ι i, (∀ i, p i (ind i)) ∧ S.PairwiseDisjoint fun i => s i (ind i) :=
  by
  rcases hd.exists_mem_filter hS with ⟨t, htl, hd⟩
  choose ind hp ht using fun i => (h i).mem_iff.1 (htl i)
  exact ⟨ind, hp, hd.mono ht⟩
#align set.pairwise_disjoint.exists_mem_filter_basis Set.PairwiseDisjoint.exists_mem_filter_basis

theorem inf_neBot_iff :
    NeBot (l ⊓ l') ↔ ∀ ⦃s : Set α⦄ (hs : s ∈ l) ⦃s'⦄ (hs' : s' ∈ l'), (s ∩ s').Nonempty :=
  l.basis_sets.inf_ne_bot_iff
#align filter.inf_ne_bot_iff Filter.inf_neBot_iff

theorem inf_principal_neBot_iff {s : Set α} : NeBot (l ⊓ 𝓟 s) ↔ ∀ U ∈ l, (U ∩ s).Nonempty :=
  l.basis_sets.inf_principal_ne_bot_iff
#align filter.inf_principal_ne_bot_iff Filter.inf_principal_neBot_iff

theorem mem_iff_inf_principal_compl {f : Filter α} {s : Set α} : s ∈ f ↔ f ⊓ 𝓟 (sᶜ) = ⊥ :=
  by
  refine' not_iff_not.1 ((inf_principal_ne_bot_iff.trans _).symm.trans ne_bot_iff)
  exact
    ⟨fun h hs => by simpa [not_nonempty_empty] using h s hs, fun hs t ht =>
      inter_compl_nonempty_iff.2 fun hts => hs <| mem_of_superset ht hts⟩
#align filter.mem_iff_inf_principal_compl Filter.mem_iff_inf_principal_compl

theorem not_mem_iff_inf_principal_compl {f : Filter α} {s : Set α} : s ∉ f ↔ NeBot (f ⊓ 𝓟 (sᶜ)) :=
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

@[simp]
theorem disjoint_principal_principal {s t : Set α} : Disjoint (𝓟 s) (𝓟 t) ↔ Disjoint s t := by
  simp [← subset_compl_iff_disjoint_left]
#align filter.disjoint_principal_principal Filter.disjoint_principal_principal

alias disjoint_principal_principal ↔ _ _root_.disjoint.filter_principal
#align disjoint.filter_principal Disjoint.filter_principal

@[simp]
theorem disjoint_pure_pure {x y : α} : Disjoint (pure x : Filter α) (pure y) ↔ x ≠ y := by
  simp only [← principal_singleton, disjoint_principal_principal, disjoint_singleton]
#align filter.disjoint_pure_pure Filter.disjoint_pure_pure

@[simp]
theorem compl_diagonal_mem_prod {l₁ l₂ : Filter α} : diagonal αᶜ ∈ l₁ ×ᶠ l₂ ↔ Disjoint l₁ l₂ := by
  simp only [mem_prod_iff, Filter.disjoint_iff, prod_subset_compl_diagonal_iff_disjoint]
#align filter.compl_diagonal_mem_prod Filter.compl_diagonal_mem_prod

theorem HasBasis.disjoint_iff_left (h : l.HasBasis p s) :
    Disjoint l l' ↔ ∃ (i : _)(hi : p i), s iᶜ ∈ l' := by
  simp only [h.disjoint_iff l'.basis_sets, exists_prop, id, ← disjoint_principal_left,
    (has_basis_principal _).disjoint_iff l'.basis_sets, Unique.exists_iff]
#align filter.has_basis.disjoint_iff_left Filter.HasBasis.disjoint_iff_left

theorem HasBasis.disjoint_iff_right (h : l.HasBasis p s) :
    Disjoint l' l ↔ ∃ (i : _)(hi : p i), s iᶜ ∈ l' :=
  disjoint_comm.trans h.disjoint_iff_left
#align filter.has_basis.disjoint_iff_right Filter.HasBasis.disjoint_iff_right

theorem le_iff_forall_inf_principal_compl {f g : Filter α} : f ≤ g ↔ ∀ V ∈ g, f ⊓ 𝓟 (Vᶜ) = ⊥ :=
  forall₂_congr fun _ _ => mem_iff_inf_principal_compl
#align filter.le_iff_forall_inf_principal_compl Filter.le_iff_forall_inf_principal_compl

theorem inf_neBot_iff_frequently_left {f g : Filter α} :
    NeBot (f ⊓ g) ↔ ∀ {p : α → Prop}, (∀ᶠ x in f, p x) → ∃ᶠ x in g, p x := by
  simpa only [inf_ne_bot_iff, frequently_iff, exists_prop, and_comm']
#align filter.inf_ne_bot_iff_frequently_left Filter.inf_neBot_iff_frequently_left

theorem inf_neBot_iff_frequently_right {f g : Filter α} :
    NeBot (f ⊓ g) ↔ ∀ {p : α → Prop}, (∀ᶠ x in g, p x) → ∃ᶠ x in f, p x :=
  by
  rw [inf_comm]
  exact inf_ne_bot_iff_frequently_left
#align filter.inf_ne_bot_iff_frequently_right Filter.inf_neBot_iff_frequently_right

theorem HasBasis.eq_binfi (h : l.HasBasis p s) : l = ⨅ (i) (_ : p i), 𝓟 (s i) :=
  eq_binfi_of_mem_iff_exists_mem fun t => by simp only [h.mem_iff, mem_principal]
#align filter.has_basis.eq_binfi Filter.HasBasis.eq_binfi

theorem HasBasis.eq_infᵢ (h : l.HasBasis (fun _ => True) s) : l = ⨅ i, 𝓟 (s i) := by
  simpa only [infᵢ_true] using h.eq_binfi
#align filter.has_basis.eq_infi Filter.HasBasis.eq_infᵢ

theorem hasBasis_infᵢ_principal {s : ι → Set α} (h : Directed (· ≥ ·) s) [Nonempty ι] :
    (⨅ i, 𝓟 (s i)).HasBasis (fun _ => True) s :=
  ⟨by
    refine' fun t =>
      (mem_infi_of_directed (h.mono_comp _ _) t).trans <| by
        simp only [exists_prop, true_and_iff, mem_principal]
    exact fun _ _ => principal_mono.2⟩
#align filter.has_basis_infi_principal Filter.hasBasis_infᵢ_principal

/-- If `s : ι → set α` is an indexed family of sets, then finite intersections of `s i` form a basis
of `⨅ i, 𝓟 (s i)`.  -/
theorem hasBasis_infᵢ_principal_finite {ι : Type _} (s : ι → Set α) :
    (⨅ i, 𝓟 (s i)).HasBasis (fun t : Set ι => t.Finite) fun t => ⋂ i ∈ t, s i :=
  by
  refine' ⟨fun U => (mem_infi_finite _).trans _⟩
  simp only [infi_principal_finset, mem_Union, mem_principal, exists_prop, exists_finite_iff_finset,
    Finset.set_binterᵢ_coe]
#align filter.has_basis_infi_principal_finite Filter.hasBasis_infᵢ_principal_finite

theorem hasBasis_binfi_principal {s : β → Set α} {S : Set β} (h : DirectedOn (s ⁻¹'o (· ≥ ·)) S)
    (ne : S.Nonempty) : (⨅ i ∈ S, 𝓟 (s i)).HasBasis (fun i => i ∈ S) s :=
  ⟨by
    refine' fun t => (mem_binfi_of_directed _ Ne).trans <| by simp only [mem_principal]
    rw [directedOn_iff_directed, ← directed_comp, (· ∘ ·)] at h⊢
    apply h.mono_comp _ _
    exact fun _ _ => principal_mono.2⟩
#align filter.has_basis_binfi_principal Filter.hasBasis_binfi_principal

theorem hasBasis_binfi_principal' {ι : Type _} {p : ι → Prop} {s : ι → Set α}
    (h : ∀ i, p i → ∀ j, p j → ∃ (k : _)(h : p k), s k ⊆ s i ∧ s k ⊆ s j) (ne : ∃ i, p i) :
    (⨅ (i) (h : p i), 𝓟 (s i)).HasBasis p s :=
  Filter.hasBasis_binfi_principal h Ne
#align filter.has_basis_binfi_principal' Filter.hasBasis_binfi_principal'

theorem HasBasis.map (f : α → β) (hl : l.HasBasis p s) : (l.map f).HasBasis p fun i => f '' s i :=
  ⟨fun t => by simp only [mem_map, image_subset_iff, hl.mem_iff, preimage]⟩
#align filter.has_basis.map Filter.HasBasis.map

theorem HasBasis.comap (f : β → α) (hl : l.HasBasis p s) :
    (l.comap f).HasBasis p fun i => f ⁻¹' s i :=
  ⟨by
    intro t
    simp only [mem_comap, exists_prop, hl.mem_iff]
    constructor
    · rintro ⟨t', ⟨i, hi, ht'⟩, H⟩
      exact ⟨i, hi, subset.trans (preimage_mono ht') H⟩
    · rintro ⟨i, hi, H⟩
      exact ⟨s i, ⟨i, hi, subset.refl _⟩, H⟩⟩
#align filter.has_basis.comap Filter.HasBasis.comap

theorem comap_hasBasis (f : α → β) (l : Filter β) :
    HasBasis (comap f l) (fun s : Set β => s ∈ l) fun s => f ⁻¹' s :=
  ⟨fun t => mem_comap⟩
#align filter.comap_has_basis Filter.comap_hasBasis

theorem HasBasis.forall_mem_mem (h : HasBasis l p s) {x : α} :
    (∀ t ∈ l, x ∈ t) ↔ ∀ i, p i → x ∈ s i :=
  by
  simp only [h.mem_iff, exists_imp]
  exact ⟨fun h i hi => h (s i) i hi subset.rfl, fun h t i hi ht => ht (h i hi)⟩
#align filter.has_basis.forall_mem_mem Filter.HasBasis.forall_mem_mem

protected theorem HasBasis.binfi_mem [CompleteLattice β] {f : Set α → β} (h : HasBasis l p s)
    (hf : Monotone f) : (⨅ t ∈ l, f t) = ⨅ (i) (hi : p i), f (s i) :=
  le_antisymm (le_infᵢ₂ fun i hi => infᵢ₂_le (s i) (h.mem_of_mem hi)) <|
    le_infᵢ₂ fun t ht =>
      let ⟨i, hpi, hi⟩ := h.mem_iff.1 ht
      infᵢ₂_le_of_le i hpi (hf hi)
#align filter.has_basis.binfi_mem Filter.HasBasis.binfi_mem

protected theorem HasBasis.bInter_mem {f : Set α → Set β} (h : HasBasis l p s) (hf : Monotone f) :
    (⋂ t ∈ l, f t) = ⋂ (i) (hi : p i), f (s i) :=
  h.binfi_mem hf
#align filter.has_basis.bInter_mem Filter.HasBasis.bInter_mem

theorem HasBasis.interₛ_sets (h : HasBasis l p s) : ⋂₀ l.sets = ⋂ (i) (hi : p i), s i :=
  by
  rw [sInter_eq_bInter]
  exact h.bInter_mem monotone_id
#align filter.has_basis.sInter_sets Filter.HasBasis.interₛ_sets

variable {ι'' : Type _} [Preorder ι''] (l) (s'' : ι'' → Set α)

/-- `is_antitone_basis s` means the image of `s` is a filter basis such that `s` is decreasing. -/
@[protect_proj]
structure IsAntitoneBasis extends IsBasis (fun _ => True) s'' : Prop where
  Antitone : Antitone s''
#align filter.is_antitone_basis Filter.IsAntitoneBasis

/-- We say that a filter `l` has an antitone basis `s : ι → set α`, if `t ∈ l` if and only if `t`
includes `s i` for some `i`, and `s` is decreasing. -/
@[protect_proj]
structure HasAntitoneBasis (l : Filter α) (s : ι'' → Set α) extends HasBasis l (fun _ => True) s :
  Prop where
  Antitone : Antitone s
#align filter.has_antitone_basis Filter.HasAntitoneBasis

theorem HasAntitoneBasis.map {l : Filter α} {s : ι'' → Set α} {m : α → β}
    (hf : HasAntitoneBasis l s) : HasAntitoneBasis (map m l) fun n => m '' s n :=
  ⟨HasBasis.map _ hf.to_has_basis, fun i j hij => image_subset _ <| hf.2 hij⟩
#align filter.has_antitone_basis.map Filter.HasAntitoneBasis.map

end SameType

section TwoTypes

variable {la : Filter α} {pa : ι → Prop} {sa : ι → Set α} {lb : Filter β} {pb : ι' → Prop}
  {sb : ι' → Set β} {f : α → β}

theorem HasBasis.tendsto_left_iff (hla : la.HasBasis pa sa) :
    Tendsto f la lb ↔ ∀ t ∈ lb, ∃ (i : _)(hi : pa i), MapsTo f (sa i) t :=
  by
  simp only [tendsto, (hla.map f).le_iff, image_subset_iff]
  rfl
#align filter.has_basis.tendsto_left_iff Filter.HasBasis.tendsto_left_iff

theorem HasBasis.tendsto_right_iff (hlb : lb.HasBasis pb sb) :
    Tendsto f la lb ↔ ∀ (i) (hi : pb i), ∀ᶠ x in la, f x ∈ sb i := by
  simpa only [tendsto, hlb.ge_iff, mem_map, Filter.Eventually]
#align filter.has_basis.tendsto_right_iff Filter.HasBasis.tendsto_right_iff

theorem HasBasis.tendsto_iff (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    Tendsto f la lb ↔ ∀ (ib) (hib : pb ib), ∃ (ia : _)(hia : pa ia), ∀ x ∈ sa ia, f x ∈ sb ib := by
  simp [hlb.tendsto_right_iff, hla.eventually_iff]
#align filter.has_basis.tendsto_iff Filter.HasBasis.tendsto_iff

theorem Tendsto.basis_left (H : Tendsto f la lb) (hla : la.HasBasis pa sa) :
    ∀ t ∈ lb, ∃ (i : _)(hi : pa i), MapsTo f (sa i) t :=
  hla.tendsto_left_iff.1 H
#align filter.tendsto.basis_left Filter.Tendsto.basis_left

theorem Tendsto.basis_right (H : Tendsto f la lb) (hlb : lb.HasBasis pb sb) :
    ∀ (i) (hi : pb i), ∀ᶠ x in la, f x ∈ sb i :=
  hlb.tendsto_right_iff.1 H
#align filter.tendsto.basis_right Filter.Tendsto.basis_right

theorem Tendsto.basis_both (H : Tendsto f la lb) (hla : la.HasBasis pa sa)
    (hlb : lb.HasBasis pb sb) :
    ∀ (ib) (hib : pb ib), ∃ (ia : _)(hia : pa ia), ∀ x ∈ sa ia, f x ∈ sb ib :=
  (hla.tendsto_iff hlb).1 H
#align filter.tendsto.basis_both Filter.Tendsto.basis_both

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem HasBasis.prod_pProd (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    (la ×ᶠ lb).HasBasis (fun i : PProd ι ι' => pa i.1 ∧ pb i.2) fun i => sa i.1 ×ˢ sb i.2 :=
  (hla.comap Prod.fst).inf' (hlb.comap Prod.snd)
#align filter.has_basis.prod_pprod Filter.HasBasis.prod_pProd

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem HasBasis.prod {ι ι' : Type _} {pa : ι → Prop} {sa : ι → Set α} {pb : ι' → Prop}
    {sb : ι' → Set β} (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    (la ×ᶠ lb).HasBasis (fun i : ι × ι' => pa i.1 ∧ pb i.2) fun i => sa i.1 ×ˢ sb i.2 :=
  (hla.comap Prod.fst).inf (hlb.comap Prod.snd)
#align filter.has_basis.prod Filter.HasBasis.prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem HasBasis.prod_same_index {p : ι → Prop} {sb : ι → Set β} (hla : la.HasBasis p sa)
    (hlb : lb.HasBasis p sb) (h_dir : ∀ {i j}, p i → p j → ∃ k, p k ∧ sa k ⊆ sa i ∧ sb k ⊆ sb j) :
    (la ×ᶠ lb).HasBasis p fun i => sa i ×ˢ sb i :=
  by
  simp only [has_basis_iff, (hla.prod_pprod hlb).mem_iff]
  refine' fun t => ⟨_, _⟩
  · rintro ⟨⟨i, j⟩, ⟨hi, hj⟩, hsub : sa i ×ˢ sb j ⊆ t⟩
    rcases h_dir hi hj with ⟨k, hk, ki, kj⟩
    exact ⟨k, hk, (Set.prod_mono ki kj).trans hsub⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨⟨i, i⟩, ⟨hi, hi⟩, h⟩
#align filter.has_basis.prod_same_index Filter.HasBasis.prod_same_index

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem HasBasis.prod_same_index_mono {ι : Type _} [LinearOrder ι] {p : ι → Prop} {sa : ι → Set α}
    {sb : ι → Set β} (hla : la.HasBasis p sa) (hlb : lb.HasBasis p sb)
    (hsa : MonotoneOn sa { i | p i }) (hsb : MonotoneOn sb { i | p i }) :
    (la ×ᶠ lb).HasBasis p fun i => sa i ×ˢ sb i :=
  hla.prod_same_index hlb fun i j hi hj =>
    have : p (min i j) := min_rec' _ hi hj
    ⟨min i j, this, hsa this hi <| min_le_left _ _, hsb this hj <| min_le_right _ _⟩
#align filter.has_basis.prod_same_index_mono Filter.HasBasis.prod_same_index_mono

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem HasBasis.prod_same_index_anti {ι : Type _} [LinearOrder ι] {p : ι → Prop} {sa : ι → Set α}
    {sb : ι → Set β} (hla : la.HasBasis p sa) (hlb : lb.HasBasis p sb)
    (hsa : AntitoneOn sa { i | p i }) (hsb : AntitoneOn sb { i | p i }) :
    (la ×ᶠ lb).HasBasis p fun i => sa i ×ˢ sb i :=
  @HasBasis.prod_same_index_mono _ _ _ _ ιᵒᵈ _ _ _ _ hla hlb hsa.dual_left hsb.dual_left
#align filter.has_basis.prod_same_index_anti Filter.HasBasis.prod_same_index_anti

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem HasBasis.prod_self (hl : la.HasBasis pa sa) :
    (la ×ᶠ la).HasBasis pa fun i => sa i ×ˢ sa i :=
  hl.prod_same_index hl fun i j hi hj => by
    simpa only [exists_prop, subset_inter_iff] using
      hl.mem_iff.1 (inter_mem (hl.mem_of_mem hi) (hl.mem_of_mem hj))
#align filter.has_basis.prod_self Filter.HasBasis.prod_self

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mem_prod_self_iff {s} : s ∈ la ×ᶠ la ↔ ∃ t ∈ la, t ×ˢ t ⊆ s :=
  la.basis_sets.prod_self.mem_iff
#align filter.mem_prod_self_iff Filter.mem_prod_self_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem HasAntitoneBasis.prod {ι : Type _} [LinearOrder ι] {f : Filter α} {g : Filter β}
    {s : ι → Set α} {t : ι → Set β} (hf : HasAntitoneBasis f s) (hg : HasAntitoneBasis g t) :
    HasAntitoneBasis (f ×ᶠ g) fun n => s n ×ˢ t n :=
  ⟨hf.1.prod_same_index_anti hg.1 (hf.2.AntitoneOn _) (hg.2.AntitoneOn _), hf.2.set_prod hg.2⟩
#align filter.has_antitone_basis.prod Filter.HasAntitoneBasis.prod

theorem HasBasis.coprod {ι ι' : Type _} {pa : ι → Prop} {sa : ι → Set α} {pb : ι' → Prop}
    {sb : ι' → Set β} (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    (la.coprod lb).HasBasis (fun i : ι × ι' => pa i.1 ∧ pb i.2) fun i =>
      Prod.fst ⁻¹' sa i.1 ∪ Prod.snd ⁻¹' sb i.2 :=
  (hla.comap Prod.fst).sup (hlb.comap Prod.snd)
#align filter.has_basis.coprod Filter.HasBasis.coprod

end TwoTypes

theorem map_sigma_mk_comap {π : α → Type _} {π' : β → Type _} {f : α → β}
    (hf : Function.Injective f) (g : ∀ a, π a → π' (f a)) (a : α) (l : Filter (π' (f a))) :
    map (Sigma.mk a) (comap (g a) l) = comap (Sigma.map f g) (map (Sigma.mk (f a)) l) :=
  by
  refine' (((basis_sets _).comap _).map _).eq_of_same_basis _
  convert ((basis_sets _).map _).comap _
  ext1 s
  apply image_sigma_mk_preimage_sigma_map hf
#align filter.map_sigma_mk_comap Filter.map_sigma_mk_comap

end Filter

end Sort

namespace Filter

variable {α β γ ι : Type _} {ι' : Sort _}

/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`out] [] -/
/-- `is_countably_generated f` means `f = generate s` for some countable `s`. -/
class IsCountablyGenerated (f : Filter α) : Prop where
  out : ∃ s : Set (Set α), s.Countable ∧ f = generate s
#align filter.is_countably_generated Filter.IsCountablyGenerated

/-- `is_countable_basis p s` means the image of `s` bounded by `p` is a countable filter basis. -/
structure IsCountableBasis (p : ι → Prop) (s : ι → Set α) extends IsBasis p s : Prop where
  Countable : (setOf p).Countable
#align filter.is_countable_basis Filter.IsCountableBasis

/-- We say that a filter `l` has a countable basis `s : ι → set α` bounded by `p : ι → Prop`,
if `t ∈ l` if and only if `t` includes `s i` for some `i` such that `p i`, and the set
defined by `p` is countable. -/
structure HasCountableBasis (l : Filter α) (p : ι → Prop) (s : ι → Set α) extends HasBasis l p s :
  Prop where
  Countable : (setOf p).Countable
#align filter.has_countable_basis Filter.HasCountableBasis

/-- A countable filter basis `B` on a type `α` is a nonempty countable collection of sets of `α`
such that the intersection of two elements of this collection contains some element
of the collection. -/
structure CountableFilterBasis (α : Type _) extends FilterBasis α where
  Countable : sets.Countable
#align filter.countable_filter_basis Filter.CountableFilterBasis

-- For illustration purposes, the countable filter basis defining (at_top : filter ℕ)
instance Nat.inhabitedCountableFilterBasis : Inhabited (CountableFilterBasis ℕ) :=
  ⟨{ (default : FilterBasis ℕ) with Countable := countable_range fun n => Ici n }⟩
#align filter.nat.inhabited_countable_filter_basis Filter.Nat.inhabitedCountableFilterBasis

theorem HasCountableBasis.isCountablyGenerated {f : Filter α} {p : ι → Prop} {s : ι → Set α}
    (h : f.HasCountableBasis p s) : f.IsCountablyGenerated :=
  ⟨⟨{ t | ∃ i, p i ∧ s i = t }, h.Countable.image s, h.to_has_basis.eq_generate⟩⟩
#align filter.has_countable_basis.is_countably_generated Filter.HasCountableBasis.isCountablyGenerated

theorem antitone_seq_of_seq (s : ℕ → Set α) :
    ∃ t : ℕ → Set α, Antitone t ∧ (⨅ i, 𝓟 <| s i) = ⨅ i, 𝓟 (t i) :=
  by
  use fun n => ⋂ m ≤ n, s m; constructor
  · exact fun i j hij => bInter_mono (Iic_subset_Iic.2 hij) fun n hn => subset.refl _
  apply le_antisymm <;> rw [le_infᵢ_iff] <;> intro i
  · rw [le_principal_iff]
    refine' (bInter_mem (finite_le_nat _)).2 fun j hji => _
    rw [← le_principal_iff]
    apply infᵢ_le_of_le j _
    exact le_rfl
  · apply infᵢ_le_of_le i _
    rw [principal_mono]
    intro a
    simp
    intro h
    apply h
    rfl
#align filter.antitone_seq_of_seq Filter.antitone_seq_of_seq

theorem countable_binfi_eq_infᵢ_seq [CompleteLattice α] {B : Set ι} (Bcbl : B.Countable)
    (Bne : B.Nonempty) (f : ι → α) : ∃ x : ℕ → ι, (⨅ t ∈ B, f t) = ⨅ i, f (x i) :=
  let ⟨g, hg⟩ := Bcbl.exists_eq_range Bne
  ⟨g, hg.symm ▸ infᵢ_range⟩
#align filter.countable_binfi_eq_infi_seq Filter.countable_binfi_eq_infᵢ_seq

theorem countable_binfi_eq_infᵢ_seq' [CompleteLattice α] {B : Set ι} (Bcbl : B.Countable)
    (f : ι → α) {i₀ : ι} (h : f i₀ = ⊤) : ∃ x : ℕ → ι, (⨅ t ∈ B, f t) = ⨅ i, f (x i) :=
  by
  cases' B.eq_empty_or_nonempty with hB Bnonempty
  · rw [hB, infᵢ_emptyset]
    use fun n => i₀
    simp [h]
  · exact countable_binfi_eq_infi_seq Bcbl Bnonempty f
#align filter.countable_binfi_eq_infi_seq' Filter.countable_binfi_eq_infᵢ_seq'

theorem countable_binfi_principal_eq_seq_infᵢ {B : Set (Set α)} (Bcbl : B.Countable) :
    ∃ x : ℕ → Set α, (⨅ t ∈ B, 𝓟 t) = ⨅ i, 𝓟 (x i) :=
  countable_binfi_eq_infᵢ_seq' Bcbl 𝓟 principal_univ
#align filter.countable_binfi_principal_eq_seq_infi Filter.countable_binfi_principal_eq_seq_infᵢ

section IsCountablyGenerated

protected theorem HasAntitoneBasis.mem_iff [Preorder ι] {l : Filter α} {s : ι → Set α}
    (hs : l.HasAntitoneBasis s) {t : Set α} : t ∈ l ↔ ∃ i, s i ⊆ t :=
  hs.to_has_basis.mem_iff.trans <| by simp only [exists_prop, true_and_iff]
#align filter.has_antitone_basis.mem_iff Filter.HasAntitoneBasis.mem_iff

protected theorem HasAntitoneBasis.mem [Preorder ι] {l : Filter α} {s : ι → Set α}
    (hs : l.HasAntitoneBasis s) (i : ι) : s i ∈ l :=
  hs.to_has_basis.mem_of_mem trivial
#align filter.has_antitone_basis.mem Filter.HasAntitoneBasis.mem

theorem HasAntitoneBasis.hasBasis_ge [Preorder ι] [IsDirected ι (· ≤ ·)] {l : Filter α}
    {s : ι → Set α} (hs : l.HasAntitoneBasis s) (i : ι) : l.HasBasis (fun j => i ≤ j) s :=
  hs.1.to_has_basis (fun j _ => (exists_ge_ge i j).imp fun k hk => ⟨hk.1, hs.2 hk.2⟩) fun j hj =>
    ⟨j, trivial, Subset.rfl⟩
#align filter.has_antitone_basis.has_basis_ge Filter.HasAntitoneBasis.hasBasis_ge

/-- If `f` is countably generated and `f.has_basis p s`, then `f` admits a decreasing basis
enumerated by natural numbers such that all sets have the form `s i`. More precisely, there is a
sequence `i n` such that `p (i n)` for all `n` and `s (i n)` is a decreasing sequence of sets which
forms a basis of `f`-/
theorem HasBasis.exists_antitone_subbasis {f : Filter α} [h : f.IsCountablyGenerated]
    {p : ι' → Prop} {s : ι' → Set α} (hs : f.HasBasis p s) :
    ∃ x : ℕ → ι', (∀ i, p (x i)) ∧ f.HasAntitoneBasis fun i => s (x i) :=
  by
  obtain ⟨x', hx'⟩ : ∃ x : ℕ → Set α, f = ⨅ i, 𝓟 (x i) :=
    by
    rcases h with ⟨s, hsc, rfl⟩
    rw [generate_eq_binfi]
    exact countable_binfi_principal_eq_seq_infi hsc
  have : ∀ i, x' i ∈ f := fun i => hx'.symm ▸ (infᵢ_le (fun i => 𝓟 (x' i)) i) (mem_principal_self _)
  let x : ℕ → { i : ι' // p i } := fun n =>
    Nat.recOn n (hs.index _ <| this 0) fun n xn =>
      hs.index _ <| inter_mem (this <| n + 1) (hs.mem_of_mem xn.2)
  have x_mono : Antitone fun i => s (x i) :=
    by
    refine' antitone_nat_of_succ_le fun i => _
    exact (hs.set_index_subset _).trans (inter_subset_right _ _)
  have x_subset : ∀ i, s (x i) ⊆ x' i := by
    rintro (_ | i)
    exacts[hs.set_index_subset _, subset.trans (hs.set_index_subset _) (inter_subset_left _ _)]
  refine' ⟨fun i => x i, fun i => (x i).2, _⟩
  have : (⨅ i, 𝓟 (s (x i))).HasAntitoneBasis fun i => s (x i) :=
    ⟨has_basis_infi_principal (directed_of_sup x_mono), x_mono⟩
  convert this
  exact
    le_antisymm (le_infᵢ fun i => le_principal_iff.2 <| by cases i <;> apply hs.set_index_mem)
      (hx'.symm ▸
        le_infᵢ fun i => le_principal_iff.2 <| this.to_has_basis.mem_iff.2 ⟨i, trivial, x_subset i⟩)
#align filter.has_basis.exists_antitone_subbasis Filter.HasBasis.exists_antitone_subbasis

/-- A countably generated filter admits a basis formed by an antitone sequence of sets. -/
theorem exists_antitone_basis (f : Filter α) [f.IsCountablyGenerated] :
    ∃ x : ℕ → Set α, f.HasAntitoneBasis x :=
  let ⟨x, hxf, hx⟩ := f.basis_sets.exists_antitone_subbasis
  ⟨x, hx⟩
#align filter.exists_antitone_basis Filter.exists_antitone_basis

theorem exists_antitone_seq (f : Filter α) [f.IsCountablyGenerated] :
    ∃ x : ℕ → Set α, Antitone x ∧ ∀ {s}, s ∈ f ↔ ∃ i, x i ⊆ s :=
  let ⟨x, hx⟩ := f.exists_antitone_basis
  ⟨x, hx.Antitone, fun s => by simp [hx.to_has_basis.mem_iff]⟩
#align filter.exists_antitone_seq Filter.exists_antitone_seq

instance Inf.isCountablyGenerated (f g : Filter α) [IsCountablyGenerated f]
    [IsCountablyGenerated g] : IsCountablyGenerated (f ⊓ g) :=
  by
  rcases f.exists_antitone_basis with ⟨s, hs⟩
  rcases g.exists_antitone_basis with ⟨t, ht⟩
  exact
    has_countable_basis.is_countably_generated
      ⟨hs.to_has_basis.inf ht.to_has_basis, Set.to_countable _⟩
#align filter.inf.is_countably_generated Filter.Inf.isCountablyGenerated

instance map.isCountablyGenerated (l : Filter α) [l.IsCountablyGenerated] (f : α → β) :
    (map f l).IsCountablyGenerated :=
  let ⟨x, hxl⟩ := l.exists_antitone_basis
  HasCountableBasis.isCountablyGenerated ⟨hxl.map.to_has_basis, to_countable _⟩
#align filter.map.is_countably_generated Filter.map.isCountablyGenerated

instance comap.isCountablyGenerated (l : Filter β) [l.IsCountablyGenerated] (f : α → β) :
    (comap f l).IsCountablyGenerated :=
  let ⟨x, hxl⟩ := l.exists_antitone_basis
  HasCountableBasis.isCountablyGenerated ⟨hxl.to_has_basis.comap _, to_countable _⟩
#align filter.comap.is_countably_generated Filter.comap.isCountablyGenerated

instance Sup.isCountablyGenerated (f g : Filter α) [IsCountablyGenerated f]
    [IsCountablyGenerated g] : IsCountablyGenerated (f ⊔ g) :=
  by
  rcases f.exists_antitone_basis with ⟨s, hs⟩
  rcases g.exists_antitone_basis with ⟨t, ht⟩
  exact
    has_countable_basis.is_countably_generated
      ⟨hs.to_has_basis.sup ht.to_has_basis, Set.to_countable _⟩
#align filter.sup.is_countably_generated Filter.Sup.isCountablyGenerated

instance prod.isCountablyGenerated (la : Filter α) (lb : Filter β) [IsCountablyGenerated la]
    [IsCountablyGenerated lb] : IsCountablyGenerated (la ×ᶠ lb) :=
  Filter.Inf.isCountablyGenerated _ _
#align filter.prod.is_countably_generated Filter.prod.isCountablyGenerated

instance coprod.isCountablyGenerated (la : Filter α) (lb : Filter β) [IsCountablyGenerated la]
    [IsCountablyGenerated lb] : IsCountablyGenerated (la.coprod lb) :=
  Filter.Sup.isCountablyGenerated _ _
#align filter.coprod.is_countably_generated Filter.coprod.isCountablyGenerated

end IsCountablyGenerated

theorem isCountablyGenerated_seq [Countable β] (x : β → Set α) :
    IsCountablyGenerated (⨅ i, 𝓟 <| x i) :=
  by
  use range x, countable_range x
  rw [generate_eq_binfi, infᵢ_range]
#align filter.is_countably_generated_seq Filter.isCountablyGenerated_seq

theorem isCountablyGenerated_of_seq {f : Filter α} (h : ∃ x : ℕ → Set α, f = ⨅ i, 𝓟 <| x i) :
    f.IsCountablyGenerated := by
  let ⟨x, h⟩ := h
  rw [h] <;> apply is_countably_generated_seq
#align filter.is_countably_generated_of_seq Filter.isCountablyGenerated_of_seq

theorem isCountablyGenerated_binfi_principal {B : Set <| Set α} (h : B.Countable) :
    IsCountablyGenerated (⨅ s ∈ B, 𝓟 s) :=
  isCountablyGenerated_of_seq (countable_binfi_principal_eq_seq_infᵢ h)
#align filter.is_countably_generated_binfi_principal Filter.isCountablyGenerated_binfi_principal

theorem isCountablyGenerated_iff_exists_antitone_basis {f : Filter α} :
    IsCountablyGenerated f ↔ ∃ x : ℕ → Set α, f.HasAntitoneBasis x :=
  by
  constructor
  · intro h
    exact f.exists_antitone_basis
  · rintro ⟨x, h⟩
    rw [h.to_has_basis.eq_infi]
    exact is_countably_generated_seq x
#align filter.is_countably_generated_iff_exists_antitone_basis Filter.isCountablyGenerated_iff_exists_antitone_basis

@[instance]
theorem isCountablyGenerated_principal (s : Set α) : IsCountablyGenerated (𝓟 s) :=
  isCountablyGenerated_of_seq ⟨fun _ => s, infᵢ_const.symm⟩
#align filter.is_countably_generated_principal Filter.isCountablyGenerated_principal

@[instance]
theorem isCountablyGenerated_pure (a : α) : IsCountablyGenerated (pure a) :=
  by
  rw [← principal_singleton]
  exact is_countably_generated_principal _
#align filter.is_countably_generated_pure Filter.isCountablyGenerated_pure

@[instance]
theorem isCountablyGenerated_bot : IsCountablyGenerated (⊥ : Filter α) :=
  @principal_empty α ▸ isCountablyGenerated_principal _
#align filter.is_countably_generated_bot Filter.isCountablyGenerated_bot

@[instance]
theorem isCountablyGenerated_top : IsCountablyGenerated (⊤ : Filter α) :=
  @principal_univ α ▸ isCountablyGenerated_principal _
#align filter.is_countably_generated_top Filter.isCountablyGenerated_top

instance Infi.isCountablyGenerated {ι : Sort _} [Countable ι] (f : ι → Filter α)
    [∀ i, IsCountablyGenerated (f i)] : IsCountablyGenerated (⨅ i, f i) :=
  by
  choose s hs using fun i => exists_antitone_basis (f i)
  rw [← plift.down_surjective.infi_comp]
  refine'
    has_countable_basis.is_countably_generated ⟨has_basis_infi fun n => (hs _).to_has_basis, _⟩
  refine' (countable_range <| Sigma.map (coe : Finset (PLift ι) → Set (PLift ι)) fun _ => id).mono _
  rintro ⟨I, f⟩ ⟨hI, -⟩
  lift I to Finset (PLift ι) using hI
  exact ⟨⟨I, f⟩, rfl⟩
#align filter.infi.is_countably_generated Filter.Infi.isCountablyGenerated

end Filter

