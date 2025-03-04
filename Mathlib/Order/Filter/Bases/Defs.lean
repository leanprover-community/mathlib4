/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Interval.Set.Basic

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

## Main statements

* `Filter.HasBasis.mem_iff`, `HasBasis.mem_of_superset`, `HasBasis.mem_of_mem` : restate `t ∈ f` in
  terms of a basis;

* `Filter.HasBasis.le_iff`, `Filter.HasBasis.ge_iff`, `Filter.HasBasis.le_basis_iff` : restate
  `l ≤ l'` in terms of bases.

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

-- Porting note: this instance was reducible but it doesn't work the same way in Lean 4
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

-- Porting note: was `protected` in Lean 3 but `protected` didn't work; removed
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

end IsBasis

-- Porting note: was `protected` in Lean 3 but `protected` didn't work; removed
/-- We say that a filter `l` has a basis `s : ι → Set α` bounded by `p : ι → Prop`,
if `t ∈ l` if and only if `t` includes `s i` for some `i` such that `p i`. -/
structure HasBasis (l : Filter α) (p : ι → Prop) (s : ι → Set α) : Prop where
  /-- A set `t` belongs to a filter `l` iff it includes an element of the basis. -/
  mem_iff' : ∀ t : Set α, t ∈ l ↔ ∃ i, p i ∧ s i ⊆ t

section SameType

variable {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {t : Set α} {i : ι} {p' : ι' → Prop}
  {s' : ι' → Set α} {i' : ι'}

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
/-- Definition of `HasBasis` unfolded with implicit set argument. -/
theorem HasBasis.mem_iff (hl : l.HasBasis p s) : t ∈ l ↔ ∃ i, p i ∧ s i ⊆ t :=
  hl.mem_iff' t

theorem HasBasis.eq_of_same_basis (hl : l.HasBasis p s) (hl' : l'.HasBasis p s) : l = l' := by
  ext t
  rw [hl.mem_iff, hl'.mem_iff]

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
theorem hasBasis_iff : l.HasBasis p s ↔ ∀ t, t ∈ l ↔ ∃ i, p i ∧ s i ⊆ t :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

theorem HasBasis.ex_mem (h : l.HasBasis p s) : ∃ i, p i :=
  (h.mem_iff.mp univ_mem).imp fun _ => And.left

protected theorem HasBasis.nonempty (h : l.HasBasis p s) : Nonempty ι :=
  nonempty_of_exists h.ex_mem

protected theorem IsBasis.hasBasis (h : IsBasis p s) : HasBasis h.filter p s :=
  ⟨fun t => by simp only [h.mem_filter_iff, exists_prop]⟩

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

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
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

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
theorem HasBasis.le_iff (hl : l.HasBasis p s) : l ≤ l' ↔ ∀ t ∈ l', ∃ i, p i ∧ s i ⊆ t := by
  simp only [le_def, hl.mem_iff]

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
theorem HasBasis.le_basis_iff (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    l ≤ l' ↔ ∀ i', p' i' → ∃ i, p i ∧ s i ⊆ s' i' := by
  simp only [hl'.ge_iff, hl.mem_iff]

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
theorem HasBasis.ext (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s')
    (h : ∀ i, p i → ∃ i', p' i' ∧ s' i' ⊆ s i) (h' : ∀ i', p' i' → ∃ i, p i ∧ s i ⊆ s' i') :
    l = l' := by
  apply le_antisymm
  · rw [hl.le_basis_iff hl']
    simpa using h'
  · rw [hl'.le_basis_iff hl]
    simpa using h

theorem hasBasis_principal (t : Set α) : (𝓟 t).HasBasis (fun _ : Unit => True) fun _ => t :=
  ⟨fun U => by simp⟩

theorem HasBasis.forall_mem_mem (h : HasBasis l p s) {x : α} :
    (∀ t ∈ l, x ∈ t) ↔ ∀ i, p i → x ∈ s i := by
  simp only [h.mem_iff, exists_imp, and_imp]
  exact ⟨fun h i hi => h (s i) i hi Subset.rfl, fun h t i hi ht => ht (h i hi)⟩

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

end SameType

end Filter
