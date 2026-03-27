/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Logic.Pairwise
public import Mathlib.Data.Set.BooleanAlgebra

/-!
# The set lattice

This file is a collection of results on the complete atomic Boolean algebra structure of `Set α`.
Notation for the complete lattice operations can be found in `Mathlib/Order/SetNotation.lean`.

## Main declarations
* `Set.sInter_eq_biInter`, `Set.sUnion_eq_biInter`: Shows that `⋂₀ s = ⋂ x ∈ s, x` and
  `⋃₀ s = ⋃ x ∈ s, x`.
* `Set.completeAtomicBooleanAlgebra`: `Set α` is a `CompleteAtomicBooleanAlgebra` with `≤ = ⊆`,
  `< = ⊂`, `⊓ = ∩`, `⊔ = ∪`, `⨅ = ⋂`, `⨆ = ⋃` and `\` as the set difference.
  See `Set.instBooleanAlgebra`.
* `Set.unionEqSigmaOfDisjoint`: Equivalence between `⋃ i, t i` and `Σ i, t i`, where `t` is an
  indexed family of disjoint sets.

## Naming convention

In lemma names,
* `⋃ i, s i` is called `iUnion`
* `⋂ i, s i` is called `iInter`
* `⋃ i j, s i j` is called `iUnion₂`. This is an `iUnion` inside an `iUnion`.
* `⋂ i j, s i j` is called `iInter₂`. This is an `iInter` inside an `iInter`.
* `⋃ i ∈ s, t i` is called `biUnion` for "bounded `iUnion`". This is the special case of `iUnion₂`
  where `j : i ∈ s`.
* `⋂ i ∈ s, t i` is called `biInter` for "bounded `iInter`". This is the special case of `iInter₂`
  where `j : i ∈ s`.

## Notation

* `⋃`: `Set.iUnion`
* `⋂`: `Set.iInter`
* `⋃₀`: `Set.sUnion`
* `⋂₀`: `Set.sInter`
-/

@[expose] public section

open Function Set

universe u

variable {α β γ δ : Type*} {ι ι' ι₂ : Sort*} {κ κ₁ κ₂ : ι → Sort*} {κ' : ι' → Sort*}

namespace Set

/-! ### Complete lattice and complete Boolean algebra instances -/

theorem mem_iUnion₂ {x : γ} {s : ∀ i, κ i → Set γ} : (x ∈ ⋃ (i) (j), s i j) ↔ ∃ i j, x ∈ s i j := by
  simp_rw [mem_iUnion]

theorem mem_iInter₂ {x : γ} {s : ∀ i, κ i → Set γ} : (x ∈ ⋂ (i) (j), s i j) ↔ ∀ i j, x ∈ s i j := by
  simp_rw [mem_iInter]

theorem mem_iUnion_of_mem {s : ι → Set α} {a : α} (i : ι) (ha : a ∈ s i) : a ∈ ⋃ i, s i :=
  mem_iUnion.2 ⟨i, ha⟩

theorem mem_iUnion₂_of_mem {s : ∀ i, κ i → Set α} {a : α} {i : ι} (j : κ i) (ha : a ∈ s i j) :
    a ∈ ⋃ (i) (j), s i j :=
  mem_iUnion₂.2 ⟨i, j, ha⟩

theorem mem_iInter_of_mem {s : ι → Set α} {a : α} (h : ∀ i, a ∈ s i) : a ∈ ⋂ i, s i :=
  mem_iInter.2 h

theorem mem_iInter₂_of_mem {s : ∀ i, κ i → Set α} {a : α} (h : ∀ i j, a ∈ s i j) :
    a ∈ ⋂ (i) (j), s i j :=
  mem_iInter₂.2 h

/-! ### Union and intersection over an indexed family of sets -/

@[congr]
theorem iUnion_congr_Prop {p q : Prop} {f₁ : p → Set α} {f₂ : q → Set α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ = iUnion f₂ :=
  iSup_congr_Prop pq f

@[congr]
theorem iInter_congr_Prop {p q : Prop} {f₁ : p → Set α} {f₂ : q → Set α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ = iInter f₂ :=
  iInf_congr_Prop pq f

theorem iUnion_plift_up (f : PLift ι → Set α) : ⋃ i, f (PLift.up i) = ⋃ i, f i :=
  iSup_plift_up _

theorem iUnion_plift_down (f : ι → Set α) : ⋃ i, f (PLift.down i) = ⋃ i, f i :=
  iSup_plift_down _

theorem iInter_plift_up (f : PLift ι → Set α) : ⋂ i, f (PLift.up i) = ⋂ i, f i :=
  iInf_plift_up _

theorem iInter_plift_down (f : ι → Set α) : ⋂ i, f (PLift.down i) = ⋂ i, f i :=
  iInf_plift_down _

theorem iUnion_eq_if {p : Prop} [Decidable p] (s : Set α) : ⋃ _ : p, s = if p then s else ∅ :=
  iSup_eq_if _

theorem iUnion_eq_dif {p : Prop} [Decidable p] (s : p → Set α) :
    ⋃ h : p, s h = if h : p then s h else ∅ :=
  iSup_eq_dif _

theorem iInter_eq_if {p : Prop} [Decidable p] (s : Set α) : ⋂ _ : p, s = if p then s else univ :=
  iInf_eq_if _

theorem iInf_eq_dif {p : Prop} [Decidable p] (s : p → Set α) :
    ⋂ h : p, s h = if h : p then s h else univ :=
  _root_.iInf_eq_dif _

theorem exists_set_mem_of_union_eq_top {ι : Type*} (t : Set ι) (s : ι → Set β)
    (w : ⋃ i ∈ t, s i = ⊤) (x : β) : ∃ i ∈ t, x ∈ s i := by
  have p : x ∈ ⊤ := Set.mem_univ x
  rw [← w, Set.mem_iUnion] at p
  simpa using p

theorem nonempty_of_union_eq_top_of_nonempty {ι : Type*} (t : Set ι) (s : ι → Set α)
    (H : Nonempty α) (w : ⋃ i ∈ t, s i = ⊤) : t.Nonempty := by
  obtain ⟨x, m, -⟩ := exists_set_mem_of_union_eq_top t s w H.some
  exact ⟨x, m⟩

theorem nonempty_of_nonempty_iUnion
    {s : ι → Set α} (h_Union : (⋃ i, s i).Nonempty) : Nonempty ι := by
  obtain ⟨x, hx⟩ := h_Union
  exact ⟨Classical.choose <| mem_iUnion.mp hx⟩

theorem nonempty_of_nonempty_iUnion_eq_univ
    {s : ι → Set α} [Nonempty α] (h_Union : ⋃ i, s i = univ) : Nonempty ι :=
  nonempty_of_nonempty_iUnion (s := s) (by simpa only [h_Union] using univ_nonempty)

theorem setOf_exists (p : ι → β → Prop) : { x | ∃ i, p i x } = ⋃ i, { x | p i x } :=
  ext fun _ => .symm <| mem_iUnion

theorem setOf_forall (p : ι → β → Prop) : { x | ∀ i, p i x } = ⋂ i, { x | p i x } :=
  ext fun _ => .symm <| mem_iInter

theorem iUnion_subset {s : ι → Set α} {t : Set α} (h : ∀ i, s i ⊆ t) : ⋃ i, s i ⊆ t :=
  iSup_le h

theorem iUnion₂_subset {s : ∀ i, κ i → Set α} {t : Set α} (h : ∀ i j, s i j ⊆ t) :
    ⋃ (i) (j), s i j ⊆ t :=
  iUnion_subset fun x => iUnion_subset (h x)

theorem subset_iInter {t : Set β} {s : ι → Set β} (h : ∀ i, t ⊆ s i) : t ⊆ ⋂ i, s i :=
  le_iInf h

theorem subset_iInter₂ {s : Set α} {t : ∀ i, κ i → Set α} (h : ∀ i j, s ⊆ t i j) :
    s ⊆ ⋂ (i) (j), t i j :=
  subset_iInter fun x => subset_iInter <| h x

@[simp]
theorem iUnion_subset_iff {s : ι → Set α} {t : Set α} : ⋃ i, s i ⊆ t ↔ ∀ i, s i ⊆ t :=
  ⟨fun h _ => Subset.trans (le_iSup s _) h, iUnion_subset⟩

theorem iUnion₂_subset_iff {s : ∀ i, κ i → Set α} {t : Set α} :
    ⋃ (i) (j), s i j ⊆ t ↔ ∀ i j, s i j ⊆ t := by simp_rw [iUnion_subset_iff]

@[simp]
theorem subset_iInter_iff {s : Set α} {t : ι → Set α} : (s ⊆ ⋂ i, t i) ↔ ∀ i, s ⊆ t i :=
  le_iInf_iff

theorem subset_iInter₂_iff {s : Set α} {t : ∀ i, κ i → Set α} :
    (s ⊆ ⋂ (i) (j), t i j) ↔ ∀ i j, s ⊆ t i j := by simp_rw [subset_iInter_iff]

theorem subset_iUnion : ∀ (s : ι → Set β) (i : ι), s i ⊆ ⋃ i, s i :=
  le_iSup

theorem iInter_subset : ∀ (s : ι → Set β) (i : ι), ⋂ i, s i ⊆ s i :=
  iInf_le

lemma iInter_subset_iUnion [Nonempty ι] {s : ι → Set α} : ⋂ i, s i ⊆ ⋃ i, s i := iInf_le_iSup

theorem subset_iUnion₂ {s : ∀ i, κ i → Set α} (i : ι) (j : κ i) : s i j ⊆ ⋃ (i') (j'), s i' j' :=
  le_iSup₂ i j

theorem iInter₂_subset {s : ∀ i, κ i → Set α} (i : ι) (j : κ i) : ⋂ (i) (j), s i j ⊆ s i j :=
  iInf₂_le i j

/-- This rather trivial consequence of `subset_iUnion` is convenient with `apply`, and has `i`
explicit for this purpose. -/
theorem subset_iUnion_of_subset {s : Set α} {t : ι → Set α} (i : ι) (h : s ⊆ t i) : s ⊆ ⋃ i, t i :=
  le_iSup_of_le i h

/-- This rather trivial consequence of `iInter_subset` is convenient with `apply`, and has `i`
explicit for this purpose. -/
theorem iInter_subset_of_subset {s : ι → Set α} {t : Set α} (i : ι) (h : s i ⊆ t) :
    ⋂ i, s i ⊆ t :=
  iInf_le_of_le i h

/-- This rather trivial consequence of `subset_iUnion₂` is convenient with `apply`, and has `i` and
`j` explicit for this purpose. -/
theorem subset_iUnion₂_of_subset {s : Set α} {t : ∀ i, κ i → Set α} (i : ι) (j : κ i)
    (h : s ⊆ t i j) : s ⊆ ⋃ (i) (j), t i j :=
  le_iSup₂_of_le i j h

/-- This rather trivial consequence of `iInter₂_subset` is convenient with `apply`, and has `i` and
`j` explicit for this purpose. -/
theorem iInter₂_subset_of_subset {s : ∀ i, κ i → Set α} {t : Set α} (i : ι) (j : κ i)
    (h : s i j ⊆ t) : ⋂ (i) (j), s i j ⊆ t :=
  iInf₂_le_of_le i j h

theorem iUnion_mono {s t : ι → Set α} (h : ∀ i, s i ⊆ t i) : ⋃ i, s i ⊆ ⋃ i, t i :=
  iSup_mono h

@[gcongr]
theorem iUnion_mono'' {s t : ι → Set α} (h : ∀ i, s i ⊆ t i) : iUnion s ⊆ iUnion t :=
  iSup_mono h

theorem iUnion₂_mono {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j ⊆ t i j) :
    ⋃ (i) (j), s i j ⊆ ⋃ (i) (j), t i j :=
  iSup₂_mono h

theorem iInter_mono {s t : ι → Set α} (h : ∀ i, s i ⊆ t i) : ⋂ i, s i ⊆ ⋂ i, t i :=
  iInf_mono h

@[gcongr]
theorem iInter_mono'' {s t : ι → Set α} (h : ∀ i, s i ⊆ t i) : iInter s ⊆ iInter t :=
  iInf_mono h

theorem iInter₂_mono {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j ⊆ t i j) :
    ⋂ (i) (j), s i j ⊆ ⋂ (i) (j), t i j :=
  iInf₂_mono h

theorem iUnion_mono' {s : ι → Set α} {t : ι₂ → Set α} (h : ∀ i, ∃ j, s i ⊆ t j) :
    ⋃ i, s i ⊆ ⋃ i, t i :=
  iSup_mono' h

theorem iUnion₂_mono' {s : ∀ i, κ i → Set α} {t : ∀ i', κ' i' → Set α}
    (h : ∀ i j, ∃ i' j', s i j ⊆ t i' j') : ⋃ (i) (j), s i j ⊆ ⋃ (i') (j'), t i' j' :=
  iSup₂_mono' h

theorem iInter_mono' {s : ι → Set α} {t : ι' → Set α} (h : ∀ j, ∃ i, s i ⊆ t j) :
    ⋂ i, s i ⊆ ⋂ j, t j :=
  Set.subset_iInter fun j =>
    let ⟨i, hi⟩ := h j
    iInter_subset_of_subset i hi

theorem iInter₂_mono' {s : ∀ i, κ i → Set α} {t : ∀ i', κ' i' → Set α}
    (h : ∀ i' j', ∃ i j, s i j ⊆ t i' j') : ⋂ (i) (j), s i j ⊆ ⋂ (i') (j'), t i' j' :=
  subset_iInter₂_iff.2 fun i' j' =>
    let ⟨_, _, hst⟩ := h i' j'
    (iInter₂_subset _ _).trans hst

theorem iUnion₂_subset_iUnion (κ : ι → Sort*) (s : ι → Set α) :
    ⋃ (i) (_ : κ i), s i ⊆ ⋃ i, s i :=
  iUnion_mono fun _ => iUnion_subset fun _ => Subset.rfl

theorem iInter_subset_iInter₂ (κ : ι → Sort*) (s : ι → Set α) :
    ⋂ i, s i ⊆ ⋂ (i) (_ : κ i), s i :=
  iInter_mono fun _ => subset_iInter fun _ => Subset.rfl

theorem iUnion_setOf (P : ι → α → Prop) : ⋃ i, { x : α | P i x } = { x : α | ∃ i, P i x } := by
  ext
  exact mem_iUnion

theorem iInter_setOf (P : ι → α → Prop) : ⋂ i, { x : α | P i x } = { x : α | ∀ i, P i x } := by
  ext
  exact mem_iInter

theorem iUnion_congr_of_surjective {f : ι → Set α} {g : ι₂ → Set α} (h : ι → ι₂) (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : ⋃ x, f x = ⋃ y, g y :=
  h1.iSup_congr h h2

theorem iInter_congr_of_surjective {f : ι → Set α} {g : ι₂ → Set α} (h : ι → ι₂) (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : ⋂ x, f x = ⋂ y, g y :=
  h1.iInf_congr h h2

lemma iUnion_congr {s t : ι → Set α} (h : ∀ i, s i = t i) : ⋃ i, s i = ⋃ i, t i := iSup_congr h
lemma iInter_congr {s t : ι → Set α} (h : ∀ i, s i = t i) : ⋂ i, s i = ⋂ i, t i := iInf_congr h

lemma iUnion₂_congr {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j = t i j) :
    ⋃ (i) (j), s i j = ⋃ (i) (j), t i j :=
  iUnion_congr fun i => iUnion_congr <| h i

lemma iInter₂_congr {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j = t i j) :
    ⋂ (i) (j), s i j = ⋂ (i) (j), t i j :=
  iInter_congr fun i => iInter_congr <| h i

theorem BijOn.iUnion_comp {s : Set β} {t : Set γ} {f : β → γ} (g : γ → Set α)
    (hf : Set.BijOn f s t) : ⋃ x ∈ s, g (f x) = ⋃ y ∈ t, g y := hf.iSup_comp g

theorem BijOn.iInter_comp {s : Set β} {t : Set γ} {f : β → γ} (g : γ → Set α)
    (hf : Set.BijOn f s t) : ⋂ x ∈ s, g (f x) = ⋂ y ∈ t, g y := hf.iInf_comp g

theorem BijOn.iUnion_congr {s : Set β} {t : Set γ} (f : β → Set α) (g : γ → Set α) {h : β → γ}
    (h1 : Set.BijOn h s t) (h2 : ∀ x, g (h x) = f x) : ⋃ x ∈ s, f x = ⋃ y ∈ t, g y :=
  h1.iSup_congr f g h2

theorem BijOn.iInter_congr {s : Set β} {t : Set γ} (f : β → Set α) (g : γ → Set α) {h : β → γ}
    (h1 : Set.BijOn h s t) (h2 : ∀ x, g (h x) = f x) : ⋂ x ∈ s, f x = ⋂ y ∈ t, g y :=
  h1.iInf_congr f g h2

section Nonempty
variable [Nonempty ι] {f : ι → Set α} {s : Set α}

lemma iUnion_const (s : Set β) : ⋃ _ : ι, s = s := iSup_const
lemma iInter_const (s : Set β) : ⋂ _ : ι, s = s := iInf_const

lemma iUnion_eq_const (hf : ∀ i, f i = s) : ⋃ i, f i = s :=
  (iUnion_congr hf).trans <| iUnion_const _

lemma iInter_eq_const (hf : ∀ i, f i = s) : ⋂ i, f i = s :=
  (iInter_congr hf).trans <| iInter_const _

end Nonempty

@[simp]
theorem compl_iUnion (s : ι → Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s i)ᶜ :=
  compl_iSup

theorem compl_iUnion₂ (s : ∀ i, κ i → Set α) : (⋃ (i) (j), s i j)ᶜ = ⋂ (i) (j), (s i j)ᶜ := by
  simp_rw [compl_iUnion]

@[simp]
theorem compl_iInter (s : ι → Set β) : (⋂ i, s i)ᶜ = ⋃ i, (s i)ᶜ :=
  compl_iInf

theorem compl_iInter₂ (s : ∀ i, κ i → Set α) : (⋂ (i) (j), s i j)ᶜ = ⋃ (i) (j), (s i j)ᶜ := by
  simp_rw [compl_iInter]

-- classical -- complete_boolean_algebra
theorem iUnion_eq_compl_iInter_compl (s : ι → Set β) : ⋃ i, s i = (⋂ i, (s i)ᶜ)ᶜ := by
  simp only [compl_iInter, compl_compl]

-- classical -- complete_boolean_algebra
theorem iInter_eq_compl_iUnion_compl (s : ι → Set β) : ⋂ i, s i = (⋃ i, (s i)ᶜ)ᶜ := by
  simp only [compl_iUnion, compl_compl]

theorem inter_iUnion (s : Set β) (t : ι → Set β) : (s ∩ ⋃ i, t i) = ⋃ i, s ∩ t i :=
  inf_iSup_eq _ _

theorem iUnion_inter (s : Set β) (t : ι → Set β) : (⋃ i, t i) ∩ s = ⋃ i, t i ∩ s :=
  iSup_inf_eq _ _

theorem iUnion_union_distrib (s : ι → Set β) (t : ι → Set β) :
    ⋃ i, s i ∪ t i = (⋃ i, s i) ∪ ⋃ i, t i :=
  iSup_sup_eq

theorem iInter_inter_distrib (s : ι → Set β) (t : ι → Set β) :
    ⋂ i, s i ∩ t i = (⋂ i, s i) ∩ ⋂ i, t i :=
  iInf_inf_eq

theorem union_iUnion [Nonempty ι] (s : Set β) (t : ι → Set β) : (s ∪ ⋃ i, t i) = ⋃ i, s ∪ t i :=
  sup_iSup

theorem iUnion_union [Nonempty ι] (s : Set β) (t : ι → Set β) : (⋃ i, t i) ∪ s = ⋃ i, t i ∪ s :=
  iSup_sup

theorem inter_iInter [Nonempty ι] (s : Set β) (t : ι → Set β) : (s ∩ ⋂ i, t i) = ⋂ i, s ∩ t i :=
  inf_iInf

theorem iInter_inter [Nonempty ι] (s : Set β) (t : ι → Set β) : (⋂ i, t i) ∩ s = ⋂ i, t i ∩ s :=
  iInf_inf

theorem insert_iUnion [Nonempty ι] (x : β) (t : ι → Set β) :
    insert x (⋃ i, t i) = ⋃ i, insert x (t i) := by
  simp_rw [← union_singleton, iUnion_union]

-- classical
theorem union_iInter (s : Set β) (t : ι → Set β) : (s ∪ ⋂ i, t i) = ⋂ i, s ∪ t i :=
  sup_iInf_eq _ _

theorem iInter_union (s : ι → Set β) (t : Set β) : (⋂ i, s i) ∪ t = ⋂ i, s i ∪ t :=
  iInf_sup_eq _ _

theorem insert_iInter (x : β) (t : ι → Set β) : insert x (⋂ i, t i) = ⋂ i, insert x (t i) := by
  simp_rw [← union_singleton, iInter_union]

theorem iUnion_diff (s : Set β) (t : ι → Set β) : (⋃ i, t i) \ s = ⋃ i, t i \ s := by
  simp only [diff_eq, iUnion_inter]

theorem diff_iUnion [Nonempty ι] (s : Set β) (t : ι → Set β) : (s \ ⋃ i, t i) = ⋂ i, s \ t i := by
  simp only [diff_eq, compl_iUnion, inter_iInter]

theorem diff_iInter (s : Set β) (t : ι → Set β) : (s \ ⋂ i, t i) = ⋃ i, s \ t i := by
  simp only [diff_eq, compl_iInter, inter_iUnion]

theorem iUnion_inter_subset {ι α} {s t : ι → Set α} : ⋃ i, s i ∩ t i ⊆ (⋃ i, s i) ∩ ⋃ i, t i :=
  le_iSup_inf_iSup s t

theorem iUnion_inter_of_monotone {ι α} [Preorder ι] [IsDirectedOrder ι] {s t : ι → Set α}
    (hs : Monotone s) (ht : Monotone t) : ⋃ i, s i ∩ t i = (⋃ i, s i) ∩ ⋃ i, t i :=
  iSup_inf_of_monotone hs ht

theorem iUnion_inter_of_antitone {ι α} [Preorder ι] [IsCodirectedOrder ι] {s t : ι → Set α}
    (hs : Antitone s) (ht : Antitone t) : ⋃ i, s i ∩ t i = (⋃ i, s i) ∩ ⋃ i, t i :=
  iSup_inf_of_antitone hs ht

theorem iInter_union_of_monotone {ι α} [Preorder ι] [IsCodirectedOrder ι] {s t : ι → Set α}
    (hs : Monotone s) (ht : Monotone t) : ⋂ i, s i ∪ t i = (⋂ i, s i) ∪ ⋂ i, t i :=
  iInf_sup_of_monotone hs ht

theorem iInter_union_of_antitone {ι α} [Preorder ι] [IsDirectedOrder ι] {s t : ι → Set α}
    (hs : Antitone s) (ht : Antitone t) : ⋂ i, s i ∪ t i = (⋂ i, s i) ∪ ⋂ i, t i :=
  iInf_sup_of_antitone hs ht

/-- An equality version of this lemma is `iUnion_iInter_of_monotone` in `Data.Set.Finite`. -/
theorem iUnion_iInter_subset {s : ι → ι' → Set α} : (⋃ j, ⋂ i, s i j) ⊆ ⋂ i, ⋃ j, s i j :=
  iSup_iInf_le_iInf_iSup (flip s)

theorem iUnion_option {ι} (s : Option ι → Set α) : ⋃ o, s o = s none ∪ ⋃ i, s (some i) :=
  iSup_option s

theorem iInter_option {ι} (s : Option ι → Set α) : ⋂ o, s o = s none ∩ ⋂ i, s (some i) :=
  iInf_option s

section

variable (p : ι → Prop) [DecidablePred p]

theorem iUnion_dite (f : ∀ i, p i → Set α) (g : ∀ i, ¬p i → Set α) :
    ⋃ i, (if h : p i then f i h else g i h) = (⋃ (i) (h : p i), f i h) ∪ ⋃ (i) (h : ¬p i), g i h :=
  iSup_dite _ _ _

theorem iUnion_ite (f g : ι → Set α) :
    ⋃ i, (if p i then f i else g i) = (⋃ (i) (_ : p i), f i) ∪ ⋃ (i) (_ : ¬p i), g i :=
  iUnion_dite _ _ _

theorem iInter_dite (f : ∀ i, p i → Set α) (g : ∀ i, ¬p i → Set α) :
    ⋂ i, (if h : p i then f i h else g i h) = (⋂ (i) (h : p i), f i h) ∩ ⋂ (i) (h : ¬p i), g i h :=
  iInf_dite _ _ _

theorem iInter_ite (f g : ι → Set α) :
    ⋂ i, (if p i then f i else g i) = (⋂ (i) (_ : p i), f i) ∩ ⋂ (i) (_ : ¬p i), g i :=
  iInter_dite _ _ _

end

/-! ### Unions and intersections indexed by `Prop` -/


theorem iInter_false {s : False → Set α} : iInter s = univ :=
  iInf_false

theorem iUnion_false {s : False → Set α} : iUnion s = ∅ :=
  iSup_false

@[simp]
theorem iInter_true {s : True → Set α} : iInter s = s trivial :=
  iInf_true

@[simp]
theorem iUnion_true {s : True → Set α} : iUnion s = s trivial :=
  iSup_true

@[simp]
theorem iInter_exists {p : ι → Prop} {f : Exists p → Set α} :
    ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩ :=
  iInf_exists

@[simp]
theorem iUnion_exists {p : ι → Prop} {f : Exists p → Set α} :
    ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩ :=
  iSup_exists

@[simp]
theorem iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅ :=
  iSup_bot

@[simp]
theorem iInter_univ : (⋂ _ : ι, univ : Set α) = univ :=
  iInf_top

section

variable {s : ι → Set α}

@[simp]
theorem iUnion_eq_empty : ⋃ i, s i = ∅ ↔ ∀ i, s i = ∅ :=
  iSup_eq_bot

@[simp]
theorem iInter_eq_univ : ⋂ i, s i = univ ↔ ∀ i, s i = univ :=
  iInf_eq_top

@[simp]
theorem nonempty_iUnion : (⋃ i, s i).Nonempty ↔ ∃ i, (s i).Nonempty := by
  simp [nonempty_iff_ne_empty]

theorem nonempty_biUnion {t : Set α} {s : α → Set β} :
    (⋃ i ∈ t, s i).Nonempty ↔ ∃ i ∈ t, (s i).Nonempty := by simp

theorem iUnion_nonempty_index (s : Set α) (t : s.Nonempty → Set β) :
    ⋃ h, t h = ⋃ x ∈ s, t ⟨x, ‹_›⟩ :=
  iSup_exists

end

@[simp]
theorem iInter_iInter_eq_left {b : β} {s : ∀ x : β, x = b → Set α} :
    ⋂ (x) (h : x = b), s x h = s b rfl :=
  iInf_iInf_eq_left

@[simp]
theorem iInter_iInter_eq_right {b : β} {s : ∀ x : β, b = x → Set α} :
    ⋂ (x) (h : b = x), s x h = s b rfl :=
  iInf_iInf_eq_right

@[simp]
theorem iUnion_iUnion_eq_left {b : β} {s : ∀ x : β, x = b → Set α} :
    ⋃ (x) (h : x = b), s x h = s b rfl :=
  iSup_iSup_eq_left

@[simp]
theorem iUnion_iUnion_eq_right {b : β} {s : ∀ x : β, b = x → Set α} :
    ⋃ (x) (h : b = x), s x h = s b rfl :=
  iSup_iSup_eq_right

theorem iInter_or {p q : Prop} (s : p ∨ q → Set α) :
    ⋂ h, s h = (⋂ h : p, s (Or.inl h)) ∩ ⋂ h : q, s (Or.inr h) :=
  iInf_or

theorem iUnion_or {p q : Prop} (s : p ∨ q → Set α) :
    ⋃ h, s h = (⋃ i, s (Or.inl i)) ∪ ⋃ j, s (Or.inr j) :=
  iSup_or

theorem iUnion_and {p q : Prop} (s : p ∧ q → Set α) : ⋃ h, s h = ⋃ (hp) (hq), s ⟨hp, hq⟩ :=
  iSup_and

theorem iInter_and {p q : Prop} (s : p ∧ q → Set α) : ⋂ h, s h = ⋂ (hp) (hq), s ⟨hp, hq⟩ :=
  iInf_and

theorem iUnion_comm (s : ι → ι' → Set α) : ⋃ (i) (i'), s i i' = ⋃ (i') (i), s i i' :=
  iSup_comm

theorem iInter_comm (s : ι → ι' → Set α) : ⋂ (i) (i'), s i i' = ⋂ (i') (i), s i i' :=
  iInf_comm

theorem iUnion_sigma {γ : α → Type*} (s : Sigma γ → Set β) : ⋃ ia, s ia = ⋃ i, ⋃ a, s ⟨i, a⟩ :=
  iSup_sigma

theorem iUnion_sigma' {γ : α → Type*} (s : ∀ i, γ i → Set β) :
    ⋃ i, ⋃ a, s i a = ⋃ ia : Sigma γ, s ia.1 ia.2 :=
  iSup_sigma' _

theorem iInter_sigma {γ : α → Type*} (s : Sigma γ → Set β) : ⋂ ia, s ia = ⋂ i, ⋂ a, s ⟨i, a⟩ :=
  iInf_sigma

theorem iInter_sigma' {γ : α → Type*} (s : ∀ i, γ i → Set β) :
    ⋂ i, ⋂ a, s i a = ⋂ ia : Sigma γ, s ia.1 ia.2 :=
  iInf_sigma' _

theorem iUnion₂_comm (s : ∀ i, κ i → ∀ i', κ' i' → Set α) :
    ⋃ (i) (j) (i') (j'), s i j i' j' = ⋃ (i') (j') (i) (j), s i j i' j' :=
  iSup₂_comm _

theorem iInter₂_comm (s : ∀ i, κ i → ∀ i', κ' i' → Set α) :
    ⋂ (i) (j) (i') (j'), s i j i' j' = ⋂ (i') (j') (i) (j), s i j i' j' :=
  iInf₂_comm _

@[simp]
theorem biUnion_and (p : ι → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p x ∧ q x y → Set α) :
    ⋃ (x : ι) (y : ι') (h : p x ∧ q x y), s x y h =
      ⋃ (x : ι) (hx : p x) (y : ι') (hy : q x y), s x y ⟨hx, hy⟩ := by
  simp only [iUnion_and, @iUnion_comm _ ι']

@[simp]
theorem biUnion_and' (p : ι' → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p y ∧ q x y → Set α) :
    ⋃ (x : ι) (y : ι') (h : p y ∧ q x y), s x y h =
      ⋃ (y : ι') (hy : p y) (x : ι) (hx : q x y), s x y ⟨hy, hx⟩ := by
  simp only [iUnion_and, @iUnion_comm _ ι]

@[simp]
theorem biInter_and (p : ι → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p x ∧ q x y → Set α) :
    ⋂ (x : ι) (y : ι') (h : p x ∧ q x y), s x y h =
      ⋂ (x : ι) (hx : p x) (y : ι') (hy : q x y), s x y ⟨hx, hy⟩ := by
  simp only [iInter_and, @iInter_comm _ ι']

@[simp]
theorem biInter_and' (p : ι' → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p y ∧ q x y → Set α) :
    ⋂ (x : ι) (y : ι') (h : p y ∧ q x y), s x y h =
      ⋂ (y : ι') (hy : p y) (x : ι) (hx : q x y), s x y ⟨hy, hx⟩ := by
  simp only [iInter_and, @iInter_comm _ ι]

@[simp]
theorem iUnion_iUnion_eq_or_left {b : β} {p : β → Prop} {s : ∀ x : β, x = b ∨ p x → Set α} :
    ⋃ (x) (h), s x h = s b (Or.inl rfl) ∪ ⋃ (x) (h : p x), s x (Or.inr h) := by
  simp only [iUnion_or, iUnion_union_distrib, iUnion_iUnion_eq_left]

@[simp]
theorem iInter_iInter_eq_or_left {b : β} {p : β → Prop} {s : ∀ x : β, x = b ∨ p x → Set α} :
    ⋂ (x) (h), s x h = s b (Or.inl rfl) ∩ ⋂ (x) (h : p x), s x (Or.inr h) := by
  simp only [iInter_or, iInter_inter_distrib, iInter_iInter_eq_left]

lemma iUnion_sum {s : α ⊕ β → Set γ} : ⋃ x, s x = (⋃ x, s (.inl x)) ∪ ⋃ x, s (.inr x) := iSup_sum

lemma iInter_sum {s : α ⊕ β → Set γ} : ⋂ x, s x = (⋂ x, s (.inl x)) ∩ ⋂ x, s (.inr x) := iInf_sum

theorem iUnion_psigma {γ : α → Type*} (s : PSigma γ → Set β) : ⋃ ia, s ia = ⋃ i, ⋃ a, s ⟨i, a⟩ :=
  iSup_psigma _

/-- A reversed version of `iUnion_psigma` with a curried map. -/
theorem iUnion_psigma' {γ : α → Type*} (s : ∀ i, γ i → Set β) :
    ⋃ i, ⋃ a, s i a = ⋃ ia : PSigma γ, s ia.1 ia.2 :=
  iSup_psigma' _

theorem iInter_psigma {γ : α → Type*} (s : PSigma γ → Set β) : ⋂ ia, s ia = ⋂ i, ⋂ a, s ⟨i, a⟩ :=
  iInf_psigma _

/-- A reversed version of `iInter_psigma` with a curried map. -/
theorem iInter_psigma' {γ : α → Type*} (s : ∀ i, γ i → Set β) :
    ⋂ i, ⋂ a, s i a = ⋂ ia : PSigma γ, s ia.1 ia.2 :=
  iInf_psigma' _

/-! ### Bounded unions and intersections -/


/-- A specialization of `mem_iUnion₂`. -/
theorem mem_biUnion {s : Set α} {t : α → Set β} {x : α} {y : β} (xs : x ∈ s) (ytx : y ∈ t x) :
    y ∈ ⋃ x ∈ s, t x :=
  mem_iUnion₂_of_mem xs ytx

/-- A specialization of `mem_iInter₂`. -/
theorem mem_biInter {s : Set α} {t : α → Set β} {y : β} (h : ∀ x ∈ s, y ∈ t x) :
    y ∈ ⋂ x ∈ s, t x :=
  mem_iInter₂_of_mem h

/-- A specialization of `subset_iUnion₂`. -/
theorem subset_biUnion_of_mem {s : Set α} {u : α → Set β} {x : α} (xs : x ∈ s) :
    u x ⊆ ⋃ x ∈ s, u x :=
  subset_iUnion₂ (s := fun i _ => u i) x xs

/-- A specialization of `iInter₂_subset`. -/
theorem biInter_subset_of_mem {s : Set α} {t : α → Set β} {x : α} (xs : x ∈ s) :
    ⋂ x ∈ s, t x ⊆ t x :=
  iInter₂_subset x xs

lemma biInter_subset_biUnion {s : Set α} (hs : s.Nonempty) {t : α → Set β} :
    ⋂ x ∈ s, t x ⊆ ⋃ x ∈ s, t x := biInf_le_biSup hs

theorem biUnion_subset_biUnion_left {s s' : Set α} {t : α → Set β} (h : s ⊆ s') :
    ⋃ x ∈ s, t x ⊆ ⋃ x ∈ s', t x :=
  iUnion₂_subset fun _ hx => subset_biUnion_of_mem <| h hx

theorem biInter_subset_biInter_left {s s' : Set α} {t : α → Set β} (h : s' ⊆ s) :
    ⋂ x ∈ s, t x ⊆ ⋂ x ∈ s', t x :=
  subset_iInter₂ fun _ hx => biInter_subset_of_mem <| h hx

theorem biUnion_mono {s s' : Set α} {t t' : α → Set β} (hs : s' ⊆ s) (h : ∀ x ∈ s, t x ⊆ t' x) :
    ⋃ x ∈ s', t x ⊆ ⋃ x ∈ s, t' x :=
  (biUnion_subset_biUnion_left hs).trans <| iUnion₂_mono h

theorem biInter_mono {s s' : Set α} {t t' : α → Set β} (hs : s ⊆ s') (h : ∀ x ∈ s, t x ⊆ t' x) :
    ⋂ x ∈ s', t x ⊆ ⋂ x ∈ s, t' x :=
  (biInter_subset_biInter_left hs).trans <| iInter₂_mono h

theorem biUnion_eq_iUnion (s : Set α) (t : ∀ x ∈ s, Set β) :
    ⋃ x ∈ s, t x ‹_› = ⋃ x : s, t x x.2 :=
  iSup_subtype'

theorem biInter_eq_iInter (s : Set α) (t : ∀ x ∈ s, Set β) :
    ⋂ x ∈ s, t x ‹_› = ⋂ x : s, t x x.2 :=
  iInf_subtype'

@[simp] lemma biUnion_const {s : Set α} (hs : s.Nonempty) (t : Set β) : ⋃ a ∈ s, t = t :=
  biSup_const hs

@[simp] lemma biInter_const {s : Set α} (hs : s.Nonempty) (t : Set β) : ⋂ a ∈ s, t = t :=
  biInf_const hs

theorem iUnion_subtype (p : α → Prop) (s : { x // p x } → Set β) :
    ⋃ x : { x // p x }, s x = ⋃ (x) (hx : p x), s ⟨x, hx⟩ :=
  iSup_subtype

theorem iInter_subtype (p : α → Prop) (s : { x // p x } → Set β) :
    ⋂ x : { x // p x }, s x = ⋂ (x) (hx : p x), s ⟨x, hx⟩ :=
  iInf_subtype

theorem biInter_empty (u : α → Set β) : ⋂ x ∈ (∅ : Set α), u x = univ :=
  iInf_emptyset

theorem biInter_univ (u : α → Set β) : ⋂ x ∈ @univ α, u x = ⋂ x, u x :=
  iInf_univ

@[simp]
theorem biUnion_self (s : Set α) : ⋃ x ∈ s, s = s :=
  Subset.antisymm (iUnion₂_subset fun _ _ => Subset.refl s) fun _ hx => mem_biUnion hx hx

@[simp]
theorem iUnion_nonempty_self (s : Set α) : ⋃ _ : s.Nonempty, s = s := by
  rw [iUnion_nonempty_index, biUnion_self]

theorem biInter_singleton (a : α) (s : α → Set β) : ⋂ x ∈ ({a} : Set α), s x = s a :=
  iInf_singleton

theorem biInter_union (s t : Set α) (u : α → Set β) :
    ⋂ x ∈ s ∪ t, u x = (⋂ x ∈ s, u x) ∩ ⋂ x ∈ t, u x :=
  iInf_union

theorem biInter_insert (a : α) (s : Set α) (t : α → Set β) :
    ⋂ x ∈ insert a s, t x = t a ∩ ⋂ x ∈ s, t x := by simp

theorem biInter_pair (a b : α) (s : α → Set β) : ⋂ x ∈ ({a, b} : Set α), s x = s a ∩ s b := by
  rw [biInter_insert, biInter_singleton]

theorem biInter_inter {ι α : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι → Set α) (t : Set α) :
    ⋂ i ∈ s, f i ∩ t = (⋂ i ∈ s, f i) ∩ t := by
  haveI : Nonempty s := hs.to_subtype
  simp [biInter_eq_iInter, ← iInter_inter]

theorem inter_biInter {ι α : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι → Set α) (t : Set α) :
    ⋂ i ∈ s, t ∩ f i = t ∩ ⋂ i ∈ s, f i := by
  rw [inter_comm, ← biInter_inter hs]
  simp [inter_comm]

theorem biUnion_empty (s : α → Set β) : ⋃ x ∈ (∅ : Set α), s x = ∅ :=
  iSup_emptyset

theorem biUnion_univ (s : α → Set β) : ⋃ x ∈ @univ α, s x = ⋃ x, s x :=
  iSup_univ

theorem biUnion_singleton (a : α) (s : α → Set β) : ⋃ x ∈ ({a} : Set α), s x = s a :=
  iSup_singleton

@[simp]
theorem biUnion_of_singleton (s : Set α) : ⋃ x ∈ s, {x} = s :=
  ext <| by simp

theorem biUnion_union (s t : Set α) (u : α → Set β) :
    ⋃ x ∈ s ∪ t, u x = (⋃ x ∈ s, u x) ∪ ⋃ x ∈ t, u x :=
  iSup_union

@[simp]
theorem iUnion_coe_set {α β : Type*} (s : Set α) (f : s → Set β) :
    ⋃ i, f i = ⋃ i ∈ s, f ⟨i, ‹i ∈ s›⟩ :=
  iUnion_subtype _ _

@[simp]
theorem iInter_coe_set {α β : Type*} (s : Set α) (f : s → Set β) :
    ⋂ i, f i = ⋂ i ∈ s, f ⟨i, ‹i ∈ s›⟩ :=
  iInter_subtype _ _

theorem biUnion_insert (a : α) (s : Set α) (t : α → Set β) :
    ⋃ x ∈ insert a s, t x = t a ∪ ⋃ x ∈ s, t x := by simp

theorem biUnion_pair (a b : α) (s : α → Set β) : ⋃ x ∈ ({a, b} : Set α), s x = s a ∪ s b := by
  simp

theorem inter_iUnion₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s ∩ ⋃ (i) (j), t i j) = ⋃ (i) (j), s ∩ t i j := by simp only [inter_iUnion]

theorem iUnion₂_inter (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋃ (i) (j), s i j) ∩ t = ⋃ (i) (j), s i j ∩ t := by simp_rw [iUnion_inter]

theorem union_iInter₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s ∪ ⋂ (i) (j), t i j) = ⋂ (i) (j), s ∪ t i j := by simp_rw [union_iInter]

theorem iInter₂_union (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) ∪ t = ⋂ (i) (j), s i j ∪ t := by simp_rw [iInter_union]

theorem mem_sUnion_of_mem {x : α} {t : Set α} {S : Set (Set α)} (hx : x ∈ t) (ht : t ∈ S) :
    x ∈ ⋃₀ S :=
  ⟨t, ht, hx⟩

-- is this theorem really necessary?
theorem notMem_of_notMem_sUnion {x : α} {t : Set α} {S : Set (Set α)} (hx : x ∉ ⋃₀ S)
    (ht : t ∈ S) : x ∉ t := fun h => hx ⟨t, ht, h⟩

theorem sInter_subset_of_mem {S : Set (Set α)} {t : Set α} (tS : t ∈ S) : ⋂₀ S ⊆ t :=
  sInf_le tS

theorem subset_sUnion_of_mem {S : Set (Set α)} {t : Set α} (tS : t ∈ S) : t ⊆ ⋃₀ S :=
  le_sSup tS

theorem subset_sUnion_of_subset {s : Set α} (t : Set (Set α)) (u : Set α) (h₁ : s ⊆ u)
    (h₂ : u ∈ t) : s ⊆ ⋃₀ t :=
  Subset.trans h₁ (subset_sUnion_of_mem h₂)

theorem sUnion_subset {S : Set (Set α)} {t : Set α} (h : ∀ t' ∈ S, t' ⊆ t) : ⋃₀ S ⊆ t :=
  sSup_le h

@[simp]
theorem sUnion_subset_iff {s : Set (Set α)} {t : Set α} : ⋃₀ s ⊆ t ↔ ∀ t' ∈ s, t' ⊆ t :=
  sSup_le_iff

/-- `sUnion` is monotone under taking a subset of each set. -/
lemma sUnion_mono_subsets {s : Set (Set α)} {f : Set α → Set α} (hf : ∀ t : Set α, t ⊆ f t) :
    ⋃₀ s ⊆ ⋃₀ (f '' s) :=
  fun _ ⟨t, htx, hxt⟩ ↦ ⟨f t, mem_image_of_mem f htx, hf t hxt⟩

/-- `sUnion` is monotone under taking a superset of each set. -/
lemma sUnion_mono_supsets {s : Set (Set α)} {f : Set α → Set α} (hf : ∀ t : Set α, f t ⊆ t) :
    ⋃₀ (f '' s) ⊆ ⋃₀ s :=
  -- If t ∈ f '' s is arbitrary; t = f u for some u : Set α.
  fun _ ⟨_, ⟨u, hus, hut⟩, hxt⟩ ↦ ⟨u, hus, (hut ▸ hf u) hxt⟩

theorem subset_sInter {S : Set (Set α)} {t : Set α} (h : ∀ t' ∈ S, t ⊆ t') : t ⊆ ⋂₀ S :=
  le_sInf h

@[simp]
theorem subset_sInter_iff {S : Set (Set α)} {t : Set α} : t ⊆ ⋂₀ S ↔ ∀ t' ∈ S, t ⊆ t' :=
  le_sInf_iff

@[gcongr]
theorem sUnion_subset_sUnion {S T : Set (Set α)} (h : S ⊆ T) : ⋃₀ S ⊆ ⋃₀ T :=
  sUnion_subset fun _ hs => subset_sUnion_of_mem (h hs)

@[gcongr]
theorem sInter_subset_sInter {S T : Set (Set α)} (h : S ⊆ T) : ⋂₀ T ⊆ ⋂₀ S :=
  subset_sInter fun _ hs => sInter_subset_of_mem (h hs)

@[simp]
theorem sUnion_empty : ⋃₀ ∅ = (∅ : Set α) :=
  sSup_empty

@[simp]
theorem sInter_empty : ⋂₀ ∅ = (univ : Set α) :=
  sInf_empty

@[simp]
theorem sUnion_singleton (s : Set α) : ⋃₀ {s} = s :=
  sSup_singleton

@[simp]
theorem sInter_singleton (s : Set α) : ⋂₀ {s} = s :=
  sInf_singleton

@[simp]
theorem sUnion_eq_empty {S : Set (Set α)} : ⋃₀ S = ∅ ↔ ∀ s ∈ S, s = ∅ :=
  sSup_eq_bot

@[simp]
theorem sInter_eq_univ {S : Set (Set α)} : ⋂₀ S = univ ↔ ∀ s ∈ S, s = univ :=
  sInf_eq_top

theorem subset_powerset_iff {s : Set (Set α)} {t : Set α} : s ⊆ 𝒫 t ↔ ⋃₀ s ⊆ t :=
  sUnion_subset_iff.symm

/-- `⋃₀` and `𝒫` form a Galois connection. -/
theorem sUnion_powerset_gc :
    GaloisConnection (⋃₀ · : Set (Set α) → Set α) (𝒫 · : Set α → Set (Set α)) :=
  gc_sSup_Iic

/-- `⋃₀` and `𝒫` form a Galois insertion. -/
def sUnionPowersetGI :
    GaloisInsertion (⋃₀ · : Set (Set α) → Set α) (𝒫 · : Set α → Set (Set α)) :=
  gi_sSup_Iic

/-- If all sets in a collection are either `∅` or `Set.univ`, then so is their union. -/
theorem sUnion_mem_empty_univ {S : Set (Set α)} (h : S ⊆ {∅, univ}) :
    ⋃₀ S ∈ ({∅, univ} : Set (Set α)) := by
  grind

@[simp]
theorem nonempty_sUnion {S : Set (Set α)} : (⋃₀ S).Nonempty ↔ ∃ s ∈ S, Set.Nonempty s := by
  simp [nonempty_iff_ne_empty]

theorem Nonempty.of_sUnion {s : Set (Set α)} (h : (⋃₀ s).Nonempty) : s.Nonempty :=
  let ⟨s, hs, _⟩ := nonempty_sUnion.1 h
  ⟨s, hs⟩

theorem Nonempty.of_sUnion_eq_univ [Nonempty α] {s : Set (Set α)} (h : ⋃₀ s = univ) : s.Nonempty :=
  Nonempty.of_sUnion <| h.symm ▸ univ_nonempty

theorem sUnion_union (S T : Set (Set α)) : ⋃₀ (S ∪ T) = ⋃₀ S ∪ ⋃₀ T :=
  sSup_union

theorem sInter_union (S T : Set (Set α)) : ⋂₀ (S ∪ T) = ⋂₀ S ∩ ⋂₀ T :=
  sInf_union

@[simp]
theorem sUnion_insert (s : Set α) (T : Set (Set α)) : ⋃₀ insert s T = s ∪ ⋃₀ T :=
  sSup_insert

@[simp]
theorem sInter_insert (s : Set α) (T : Set (Set α)) : ⋂₀ insert s T = s ∩ ⋂₀ T :=
  sInf_insert

@[simp]
theorem sUnion_diff_singleton_empty (s : Set (Set α)) : ⋃₀ (s \ {∅}) = ⋃₀ s :=
  sSup_diff_singleton_bot s

@[simp]
theorem sInter_diff_singleton_univ (s : Set (Set α)) : ⋂₀ (s \ {univ}) = ⋂₀ s :=
  sInf_diff_singleton_top s

theorem sUnion_pair (s t : Set α) : ⋃₀ {s, t} = s ∪ t :=
  sSup_pair

theorem sInter_pair (s t : Set α) : ⋂₀ {s, t} = s ∩ t :=
  sInf_pair

@[simp]
theorem sUnion_image (f : α → Set β) (s : Set α) : ⋃₀ (f '' s) = ⋃ a ∈ s, f a :=
  sSup_image

@[simp]
theorem sInter_image (f : α → Set β) (s : Set α) : ⋂₀ (f '' s) = ⋂ a ∈ s, f a :=
  sInf_image

@[simp]
lemma sUnion_image2 (f : α → β → Set γ) (s : Set α) (t : Set β) :
    ⋃₀ (image2 f s t) = ⋃ (a ∈ s) (b ∈ t), f a b := sSup_image2

@[simp]
lemma sInter_image2 (f : α → β → Set γ) (s : Set α) (t : Set β) :
    ⋂₀ (image2 f s t) = ⋂ (a ∈ s) (b ∈ t), f a b := sInf_image2

@[simp]
theorem sUnion_range (f : ι → Set β) : ⋃₀ range f = ⋃ x, f x :=
  rfl

@[simp]
theorem sInter_range (f : ι → Set β) : ⋂₀ range f = ⋂ x, f x :=
  rfl

theorem iUnion_eq_univ_iff {f : ι → Set α} : ⋃ i, f i = univ ↔ ∀ x, ∃ i, x ∈ f i := by
  simp only [eq_univ_iff_forall, mem_iUnion]

theorem iUnion₂_eq_univ_iff {s : ∀ i, κ i → Set α} :
    ⋃ (i) (j), s i j = univ ↔ ∀ a, ∃ i j, a ∈ s i j := by
  simp only [iUnion_eq_univ_iff, mem_iUnion]

theorem sUnion_eq_univ_iff {c : Set (Set α)} : ⋃₀ c = univ ↔ ∀ a, ∃ b ∈ c, a ∈ b := by
  simp only [eq_univ_iff_forall, mem_sUnion]

-- classical
theorem iInter_eq_empty_iff {f : ι → Set α} : ⋂ i, f i = ∅ ↔ ∀ x, ∃ i, x ∉ f i := by
  simp [Set.eq_empty_iff_forall_notMem]

-- classical
theorem iInter₂_eq_empty_iff {s : ∀ i, κ i → Set α} :
    ⋂ (i) (j), s i j = ∅ ↔ ∀ a, ∃ i j, a ∉ s i j := by
  simp only [eq_empty_iff_forall_notMem, mem_iInter, not_forall]

-- classical
theorem sInter_eq_empty_iff {c : Set (Set α)} : ⋂₀ c = ∅ ↔ ∀ a, ∃ b ∈ c, a ∉ b := by
  simp [Set.eq_empty_iff_forall_notMem]

-- classical
@[simp]
theorem nonempty_iInter {f : ι → Set α} : (⋂ i, f i).Nonempty ↔ ∃ x, ∀ i, x ∈ f i := by
  simp [nonempty_iff_ne_empty, iInter_eq_empty_iff]

-- classical
theorem nonempty_iInter₂ {s : ∀ i, κ i → Set α} :
    (⋂ (i) (j), s i j).Nonempty ↔ ∃ a, ∀ i j, a ∈ s i j := by
  simp

-- classical
@[simp]
theorem nonempty_sInter {c : Set (Set α)} : (⋂₀ c).Nonempty ↔ ∃ a, ∀ b ∈ c, a ∈ b := by
  simp [nonempty_iff_ne_empty, sInter_eq_empty_iff]

-- classical
theorem compl_sUnion (S : Set (Set α)) : (⋃₀ S)ᶜ = ⋂₀ (compl '' S) :=
  ext fun x => by simp

-- classical
theorem sUnion_eq_compl_sInter_compl (S : Set (Set α)) : ⋃₀ S = (⋂₀ (compl '' S))ᶜ := by
  rw [← compl_compl (⋃₀ S), compl_sUnion]

-- classical
theorem compl_sInter (S : Set (Set α)) : (⋂₀ S)ᶜ = ⋃₀ (compl '' S) := by
  rw [sUnion_eq_compl_sInter_compl, compl_compl_image]

-- classical
theorem sInter_eq_compl_sUnion_compl (S : Set (Set α)) : ⋂₀ S = (⋃₀ (compl '' S))ᶜ := by
  rw [← compl_compl (⋂₀ S), compl_sInter]

theorem inter_empty_of_inter_sUnion_empty {s t : Set α} {S : Set (Set α)} (hs : t ∈ S)
    (h : s ∩ ⋃₀ S = ∅) : s ∩ t = ∅ :=
  eq_empty_of_subset_empty <| by
    rw [← h]; exact inter_subset_inter_right _ (subset_sUnion_of_mem hs)

theorem range_sigma_eq_iUnion_range {γ : α → Type*} (f : Sigma γ → β) :
    range f = ⋃ a, range fun b => f ⟨a, b⟩ :=
  Set.ext <| by simp

theorem iUnion_eq_range_sigma (s : α → Set β) : ⋃ i, s i = range fun a : Σ i, s i => a.2 := by
  simp [Set.ext_iff]

theorem iUnion_eq_range_psigma (s : ι → Set β) : ⋃ i, s i = range fun a : Σ' i, s i => a.2 := by
  simp [Set.ext_iff]

theorem iUnion_image_preimage_sigma_mk_eq_self {ι : Type*} {σ : ι → Type*} (s : Set (Sigma σ)) :
    ⋃ i, Sigma.mk i '' (Sigma.mk i ⁻¹' s) = s := by
  ext x
  simp only [mem_iUnion, mem_image, mem_preimage]
  grind

theorem Sigma.univ (X : α → Type*) : (Set.univ : Set (Σ a, X a)) = ⋃ a, range (Sigma.mk a) :=
  Set.ext fun x =>
    iff_of_true trivial ⟨range (Sigma.mk x.1), Set.mem_range_self _, x.2, Sigma.eta x⟩

alias sUnion_mono := sUnion_subset_sUnion

alias sInter_mono := sInter_subset_sInter

theorem iUnion_subset_iUnion_const {s : Set α} (h : ι → ι₂) : ⋃ _ : ι, s ⊆ ⋃ _ : ι₂, s :=
  iSup_const_mono (α := Set α) h

@[simp]
theorem iUnion_singleton_eq_range (f : α → β) : ⋃ x : α, {f x} = range f := by
  ext x
  simp [@eq_comm _ x]

theorem iUnion_insert_eq_range_union_iUnion {ι : Type*} (x : ι → β) (t : ι → Set β) :
    ⋃ i, insert (x i) (t i) = range x ∪ ⋃ i, t i := by
  simp_rw [← union_singleton, iUnion_union_distrib, union_comm, iUnion_singleton_eq_range]

theorem iUnion_of_singleton (α : Type*) : (⋃ x, {x} : Set α) = univ := by simp [Set.ext_iff]

theorem iUnion_of_singleton_coe (s : Set α) : ⋃ i : s, ({(i : α)} : Set α) = s := by simp

theorem sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i : Set α) (_ : i ∈ s), i := by
  rw [← sUnion_image, image_id']

theorem sInter_eq_biInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i : Set α) (_ : i ∈ s), i := by
  rw [← sInter_image, image_id']

theorem sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : s, i := by
  simp only [← sUnion_range, Subtype.range_coe]

theorem sInter_eq_iInter {s : Set (Set α)} : ⋂₀ s = ⋂ i : s, i := by
  simp only [← sInter_range, Subtype.range_coe]

@[simp]
theorem iUnion_of_empty [IsEmpty ι] (s : ι → Set α) : ⋃ i, s i = ∅ :=
  iSup_of_empty _

@[simp]
theorem iInter_of_empty [IsEmpty ι] (s : ι → Set α) : ⋂ i, s i = univ :=
  iInf_of_empty _

theorem union_eq_iUnion {s₁ s₂ : Set α} : s₁ ∪ s₂ = ⋃ b : Bool, cond b s₁ s₂ :=
  sup_eq_iSup s₁ s₂

theorem inter_eq_iInter {s₁ s₂ : Set α} : s₁ ∩ s₂ = ⋂ b : Bool, cond b s₁ s₂ :=
  inf_eq_iInf s₁ s₂

theorem sInter_union_sInter {S T : Set (Set α)} :
    ⋂₀ S ∪ ⋂₀ T = ⋂ p ∈ S ×ˢ T, (p : Set α × Set α).1 ∪ p.2 :=
  sInf_sup_sInf

theorem sUnion_inter_sUnion {s t : Set (Set α)} :
    ⋃₀ s ∩ ⋃₀ t = ⋃ p ∈ s ×ˢ t, (p : Set α × Set α).1 ∩ p.2 :=
  sSup_inf_sSup

theorem biUnion_iUnion (s : ι → Set α) (t : α → Set β) :
    ⋃ x ∈ ⋃ i, s i, t x = ⋃ (i) (x ∈ s i), t x := by simp [@iUnion_comm _ ι]

theorem biInter_iUnion (s : ι → Set α) (t : α → Set β) :
    ⋂ x ∈ ⋃ i, s i, t x = ⋂ (i) (x ∈ s i), t x := by simp [@iInter_comm _ ι]

theorem sUnion_iUnion (s : ι → Set (Set α)) : ⋃₀ ⋃ i, s i = ⋃ i, ⋃₀ s i := by
  simp only [sUnion_eq_biUnion, biUnion_iUnion]

theorem sInter_iUnion (s : ι → Set (Set α)) : ⋂₀ ⋃ i, s i = ⋂ i, ⋂₀ s i := by
  simp only [sInter_eq_biInter, biInter_iUnion]

theorem iUnion_range_eq_sUnion {α β : Type*} (C : Set (Set α)) {f : ∀ s : C, β → (s : Type _)}
    (hf : ∀ s : C, Surjective (f s)) : ⋃ y : β, range (fun s : C => (f s y).val) = ⋃₀ C := by
  ext x; constructor
  · rintro ⟨s, ⟨y, rfl⟩, ⟨s, hs⟩, rfl⟩
    refine ⟨_, hs, ?_⟩
    exact (f ⟨s, hs⟩ y).2
  · rintro ⟨s, hs, hx⟩
    obtain ⟨y, hy⟩ := hf ⟨s, hs⟩ ⟨x, hx⟩
    refine ⟨_, ⟨y, rfl⟩, ⟨s, hs⟩, ?_⟩
    exact congr_arg Subtype.val hy

theorem iUnion_range_eq_iUnion (C : ι → Set α) {f : ∀ x : ι, β → C x}
    (hf : ∀ x : ι, Surjective (f x)) : ⋃ y : β, range (fun x : ι => (f x y).val) = ⋃ x, C x := by
  ext x; rw [mem_iUnion, mem_iUnion]; constructor
  · rintro ⟨y, i, rfl⟩
    exact ⟨i, (f i y).2⟩
  · rintro ⟨i, hx⟩
    obtain ⟨y, hy⟩ := hf i ⟨x, hx⟩
    exact ⟨y, i, congr_arg Subtype.val hy⟩

lemma iUnion_sumElim {ι σ : Type*} (s : ι → Set α) (t : σ → Set α) :
    ⋃ x, Sum.elim s t x = (⋃ x, s x) ∪ ⋃ x, t x := by
  ext
  simp

theorem union_distrib_iInter_left (s : ι → Set α) (t : Set α) : (t ∪ ⋂ i, s i) = ⋂ i, t ∪ s i :=
  sup_iInf_eq _ _

theorem union_distrib_iInter₂_left (s : Set α) (t : ∀ i, κ i → Set α) :
    (s ∪ ⋂ (i) (j), t i j) = ⋂ (i) (j), s ∪ t i j := by simp_rw [union_distrib_iInter_left]

theorem union_distrib_iInter_right (s : ι → Set α) (t : Set α) : (⋂ i, s i) ∪ t = ⋂ i, s i ∪ t :=
  iInf_sup_eq _ _

theorem union_distrib_iInter₂_right (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) ∪ t = ⋂ (i) (j), s i j ∪ t := by simp_rw [union_distrib_iInter_right]

lemma biUnion_lt_eq_iUnion [LT α] [NoMaxOrder α] {s : α → Set β} :
    ⋃ (n) (m < n), s m = ⋃ n, s n := biSup_lt_eq_iSup

lemma biUnion_le_eq_iUnion [Preorder α] {s : α → Set β} :
    ⋃ (n) (m ≤ n), s m = ⋃ n, s n := biSup_le_eq_iSup

lemma biInter_lt_eq_iInter [LT α] [NoMaxOrder α] {s : α → Set β} :
    ⋂ (n) (m < n), s m = ⋂ (n), s n := biInf_lt_eq_iInf

lemma biInter_le_eq_iInter [Preorder α] {s : α → Set β} :
    ⋂ (n) (m ≤ n), s m = ⋂ (n), s n := biInf_le_eq_iInf

lemma biUnion_gt_eq_iUnion [LT α] [NoMinOrder α] {s : α → Set β} :
    ⋃ (n) (m > n), s m = ⋃ n, s n := biSup_gt_eq_iSup

lemma biUnion_ge_eq_iUnion [Preorder α] {s : α → Set β} :
    ⋃ (n) (m ≥ n), s m = ⋃ n, s n := biSup_ge_eq_iSup

lemma biInter_gt_eq_iInf [LT α] [NoMinOrder α] {s : α → Set β} :
    ⋂ (n) (m > n), s m = ⋂ n, s n := biInf_gt_eq_iInf

lemma biInter_ge_eq_iInf [Preorder α] {s : α → Set β} :
    ⋂ (n) (m ≥ n), s m = ⋂ n, s n := biInf_ge_eq_iInf

section le

variable {ι : Type*} [PartialOrder ι] (s : ι → Set α) (i : ι)

theorem biUnion_le : (⋃ j ≤ i, s j) = (⋃ j < i, s j) ∪ s i :=
  biSup_le_eq_sup s i

theorem biInter_le : (⋂ j ≤ i, s j) = (⋂ j < i, s j) ∩ s i :=
  biInf_le_eq_inf s i

theorem biUnion_ge : (⋃ j ≥ i, s j) = s i ∪ ⋃ j > i, s j :=
  biSup_ge_eq_sup s i

theorem biInter_ge : (⋂ j ≥ i, s j) = s i ∩ ⋂ j > i, s j :=
  biInf_ge_eq_inf s i

end le

section Pi

variable {π : α → Type*}

theorem pi_def (i : Set α) (s : ∀ a, Set (π a)) : pi i s = ⋂ a ∈ i, eval a ⁻¹' s a := by
  ext
  simp

theorem univ_pi_eq_iInter (t : ∀ i, Set (π i)) : pi univ t = ⋂ i, eval i ⁻¹' t i := by
  simp only [pi_def, iInter_true, mem_univ]

theorem pi_diff_pi_subset (i : Set α) (s t : ∀ a, Set (π a)) :
    pi i s \ pi i t ⊆ ⋃ a ∈ i, eval a ⁻¹' (s a \ t a) := by
  refine diff_subset_comm.2 fun x hx a ha => ?_
  simp only [mem_diff, mem_pi, mem_iUnion, not_exists, mem_preimage, not_and, not_not] at hx
  exact hx.2 _ ha (hx.1 _ ha)

theorem iUnion_univ_pi {ι : α → Type*} (t : (a : α) → ι a → Set (π a)) :
    ⋃ x : (a : α) → ι a, pi univ (fun a => t a (x a)) = pi univ fun a => ⋃ j : ι a, t a j := by
  ext
  simp [Classical.skolem]

theorem biUnion_univ_pi {ι : α → Type*} (s : (a : α) → Set (ι a)) (t : (a : α) → ι a → Set (π a)) :
    ⋃ x ∈ univ.pi s, pi univ (fun a => t a (x a)) = pi univ fun a => ⋃ j ∈ s a, t a j := by
  ext
  simp [Classical.skolem, forall_and]

theorem pi_iUnion_eq_iInter_pi {α' : Type*} (s : α' → Set α) (t : (a : α) → Set (π a)) :
    (⋃ i, s i).pi t = ⋂ i, (s i).pi t := by
  ext f
  simp
  grind

end Pi

section Directed

theorem directedOn_iUnion {r} {f : ι → Set α} (hd : Directed (· ⊆ ·) f)
    (h : ∀ x, DirectedOn r (f x)) : DirectedOn r (⋃ x, f x) := by
  simp only [DirectedOn, mem_iUnion, exists_imp]
  exact fun a₁ b₁ fb₁ a₂ b₂ fb₂ =>
    let ⟨z, zb₁, zb₂⟩ := hd b₁ b₂
    let ⟨x, xf, xa₁, xa₂⟩ := h z a₁ (zb₁ fb₁) a₂ (zb₂ fb₂)
    ⟨x, ⟨z, xf⟩, xa₁, xa₂⟩

theorem directedOn_sUnion {r} {S : Set (Set α)} (hd : DirectedOn (· ⊆ ·) S)
    (h : ∀ x ∈ S, DirectedOn r x) : DirectedOn r (⋃₀ S) := by
  rw [sUnion_eq_iUnion]
  exact directedOn_iUnion (directedOn_iff_directed.mp hd) (fun i ↦ h i.1 i.2)
end Directed

end Set

namespace Function

namespace Surjective

theorem iUnion_comp {f : ι → ι₂} (hf : Surjective f) (g : ι₂ → Set α) : ⋃ x, g (f x) = ⋃ y, g y :=
  hf.iSup_comp g

theorem iInter_comp {f : ι → ι₂} (hf : Surjective f) (g : ι₂ → Set α) : ⋂ x, g (f x) = ⋂ y, g y :=
  hf.iInf_comp g

end Surjective

end Function

/-!
### Disjoint sets
-/


section Disjoint

variable {s t : Set α}

namespace Set

@[simp]
theorem disjoint_iUnion_left {ι : Sort*} {s : ι → Set α} :
    Disjoint (⋃ i, s i) t ↔ ∀ i, Disjoint (s i) t :=
  iSup_disjoint_iff

@[simp]
theorem disjoint_iUnion_right {ι : Sort*} {s : ι → Set α} :
    Disjoint t (⋃ i, s i) ↔ ∀ i, Disjoint t (s i) :=
  disjoint_iSup_iff

theorem disjoint_iUnion₂_left {s : ∀ i, κ i → Set α} {t : Set α} :
    Disjoint (⋃ (i) (j), s i j) t ↔ ∀ i j, Disjoint (s i j) t :=
  iSup₂_disjoint_iff

theorem disjoint_iUnion₂_right {s : Set α} {t : ∀ i, κ i → Set α} :
    Disjoint s (⋃ (i) (j), t i j) ↔ ∀ i j, Disjoint s (t i j) :=
  disjoint_iSup₂_iff

@[simp]
theorem disjoint_sUnion_left {S : Set (Set α)} {t : Set α} :
    Disjoint (⋃₀ S) t ↔ ∀ s ∈ S, Disjoint s t :=
  sSup_disjoint_iff

@[simp]
theorem disjoint_sUnion_right {s : Set α} {S : Set (Set α)} :
    Disjoint s (⋃₀ S) ↔ ∀ t ∈ S, Disjoint s t :=
  disjoint_sSup_iff

lemma biUnion_compl_eq_of_pairwise_disjoint_of_iUnion_eq_univ {ι : Type*} {Es : ι → Set α}
    (Es_union : ⋃ i, Es i = univ) (Es_disj : Pairwise fun i j ↦ Disjoint (Es i) (Es j))
    (I : Set ι) :
    (⋃ i ∈ I, Es i)ᶜ = ⋃ i ∈ Iᶜ, Es i := by
  ext x
  obtain ⟨i, hix⟩ : ∃ i, x ∈ Es i := by simp [← mem_iUnion, Es_union]
  have obs : ∀ (J : Set ι), x ∈ ⋃ j ∈ J, Es j ↔ i ∈ J := by
    refine fun J ↦ ⟨?_, fun i_in_J ↦ by simpa only [mem_iUnion, exists_prop] using ⟨i, i_in_J, hix⟩⟩
    intro x_in_U
    simp only [mem_iUnion, exists_prop] at x_in_U
    obtain ⟨j, j_in_J, hjx⟩ := x_in_U
    rwa [show i = j by by_contra i_ne_j; exact Disjoint.ne_of_mem (Es_disj i_ne_j) hix hjx rfl]
  have obs' : ∀ (J : Set ι), x ∈ (⋃ j ∈ J, Es j)ᶜ ↔ i ∉ J :=
    fun J ↦ by simpa only [mem_compl_iff, not_iff_not] using obs J
  rw [obs, obs', mem_compl_iff]

end Set

end Disjoint

/-! ### Intervals -/

namespace Set

lemma nonempty_iInter_Iic_iff [Preorder α] {f : ι → α} :
    (⋂ i, Iic (f i)).Nonempty ↔ BddBelow (range f) := by
  have : (⋂ (i : ι), Iic (f i)) = lowerBounds (range f) := by
    ext c; simp [lowerBounds]
  simp [this, BddBelow]

lemma nonempty_iInter_Ici_iff [Preorder α] {f : ι → α} :
    (⋂ i, Ici (f i)).Nonempty ↔ BddAbove (range f) :=
  nonempty_iInter_Iic_iff (α := αᵒᵈ)

variable [CompleteLattice α]

theorem Ici_iSup (f : ι → α) : Ici (⨆ i, f i) = ⋂ i, Ici (f i) :=
  ext fun _ => by simp only [mem_Ici, iSup_le_iff, mem_iInter]

theorem Iic_iInf (f : ι → α) : Iic (⨅ i, f i) = ⋂ i, Iic (f i) :=
  ext fun _ => by simp only [mem_Iic, le_iInf_iff, mem_iInter]

theorem Ici_iSup₂ (f : ∀ i, κ i → α) : Ici (⨆ (i) (j), f i j) = ⋂ (i) (j), Ici (f i j) := by
  simp_rw [Ici_iSup]

theorem Iic_iInf₂ (f : ∀ i, κ i → α) : Iic (⨅ (i) (j), f i j) = ⋂ (i) (j), Iic (f i j) := by
  simp_rw [Iic_iInf]

theorem Ici_sSup (s : Set α) : Ici (sSup s) = ⋂ a ∈ s, Ici a := by rw [sSup_eq_iSup, Ici_iSup₂]

theorem Iic_sInf (s : Set α) : Iic (sInf s) = ⋂ a ∈ s, Iic a := by rw [sInf_eq_iInf, Iic_iInf₂]

end Set

namespace Set

variable (t : α → Set β)

theorem biUnion_diff_biUnion_subset (s₁ s₂ : Set α) :
    ((⋃ x ∈ s₁, t x) \ ⋃ x ∈ s₂, t x) ⊆ ⋃ x ∈ s₁ \ s₂, t x := by
  simp only [diff_subset_iff, ← biUnion_union]
  apply biUnion_subset_biUnion_left
  rw [union_diff_self]
  apply subset_union_right

/-- If `t` is an indexed family of sets, then there is a natural map from `Σ i, t i` to `⋃ i, t i`
sending `⟨i, x⟩` to `x`. -/
def sigmaToiUnion (x : Σ i, t i) : ⋃ i, t i :=
  ⟨x.2, mem_iUnion.2 ⟨x.1, x.2.2⟩⟩

theorem sigmaToiUnion_surjective : Surjective (sigmaToiUnion t)
  | ⟨b, hb⟩ =>
    have : ∃ a, b ∈ t a := by simpa using hb
    let ⟨a, hb⟩ := this
    ⟨⟨a, b, hb⟩, rfl⟩

theorem sigmaToiUnion_injective (h : Pairwise (Disjoint on t)) :
    Injective (sigmaToiUnion t)
  | ⟨a₁, b₁, h₁⟩, ⟨a₂, b₂, h₂⟩, eq =>
    have b_eq : b₁ = b₂ := congr_arg Subtype.val eq
    have a_eq : a₁ = a₂ :=
      by_contradiction fun ne =>
        have : b₁ ∈ t a₁ ∩ t a₂ := ⟨h₁, b_eq.symm ▸ h₂⟩
        (h ne).le_bot this
    Sigma.eq a_eq <| Subtype.ext <| by subst b_eq; subst a_eq; rfl

theorem sigmaToiUnion_bijective (h : Pairwise (Disjoint on t)) :
    Bijective (sigmaToiUnion t) :=
  ⟨sigmaToiUnion_injective t h, sigmaToiUnion_surjective t⟩

/-- Equivalence from the disjoint union of a family of sets forming a partition of `β`, to `β`
itself. -/
noncomputable def sigmaEquiv (s : α → Set β) (hs : ∀ b, ∃! i, b ∈ s i) :
    (Σ i, s i) ≃ β where
  toFun | ⟨_, b⟩ => b
  invFun b := ⟨(hs b).choose, b, (hs b).choose_spec.1⟩
  left_inv | ⟨i, b, hb⟩ => Sigma.subtype_ext ((hs b).choose_spec.2 i hb).symm rfl

/-- Equivalence between a disjoint union and a dependent sum. -/
noncomputable def unionEqSigmaOfDisjoint {t : α → Set β}
    (h : Pairwise (Disjoint on t)) :
    (⋃ i, t i) ≃ Σ i, t i :=
  (Equiv.ofBijective _ <| sigmaToiUnion_bijective t h).symm

@[simp]
lemma coe_unionEqSigmaOfDisjoint_symm_apply {α β : Type*} {t : α → Set β}
    (h : Pairwise (Disjoint on t)) (x : (i : α) × t i) :
    ((Set.unionEqSigmaOfDisjoint h).symm x : β) = x.2 := by
  rfl

@[simp]
lemma coe_snd_unionEqSigmaOfDisjoint {α β : Type*} {t : α → Set β}
    (h : Pairwise (Disjoint on t)) (x : ⋃ (i : α), t i) :
    ((Set.unionEqSigmaOfDisjoint h x).snd : β) = x := by
  conv => right; rw [← unionEqSigmaOfDisjoint h |>.symm_apply_apply x]
  rfl

theorem iUnion_ge_eq_iUnion_nat_add (u : ℕ → Set α) (n : ℕ) : ⋃ i ≥ n, u i = ⋃ i, u (i + n) :=
  iSup_ge_eq_iSup_nat_add u n

theorem iInter_ge_eq_iInter_nat_add (u : ℕ → Set α) (n : ℕ) : ⋂ i ≥ n, u i = ⋂ i, u (i + n) :=
  iInf_ge_eq_iInf_nat_add u n

theorem _root_.Monotone.iUnion_nat_add {f : ℕ → Set α} (hf : Monotone f) (k : ℕ) :
    ⋃ n, f (n + k) = ⋃ n, f n :=
  hf.iSup_nat_add k

theorem _root_.Antitone.iInter_nat_add {f : ℕ → Set α} (hf : Antitone f) (k : ℕ) :
    ⋂ n, f (n + k) = ⋂ n, f n :=
  hf.iInf_nat_add k

@[simp]
theorem iUnion_iInter_ge_nat_add (f : ℕ → Set α) (k : ℕ) :
    ⋃ n, ⋂ i ≥ n, f (i + k) = ⋃ n, ⋂ i ≥ n, f i :=
  iSup_iInf_ge_nat_add f k

theorem union_iUnion_nat_succ (u : ℕ → Set α) : (u 0 ∪ ⋃ i, u (i + 1)) = ⋃ i, u i :=
  sup_iSup_nat_succ u

theorem inter_iInter_nat_succ (u : ℕ → Set α) : (u 0 ∩ ⋂ i, u (i + 1)) = ⋂ i, u i :=
  inf_iInf_nat_succ u

theorem iUnion_le_nat : ⋃ n : ℕ, {i | i ≤ n} = Set.univ :=
  subset_antisymm (Set.subset_univ _)
    (fun i _ ↦ Set.mem_iUnion_of_mem i (Set.mem_setOf.mpr (le_refl _)))

end Set

open Set

variable [CompleteLattice β]

theorem iSup_iUnion (s : ι → Set α) (f : α → β) : ⨆ a ∈ ⋃ i, s i, f a = ⨆ (i) (a ∈ s i), f a := by
  rw [iSup_comm]
  simp_rw [mem_iUnion, iSup_exists]

theorem iInf_iUnion (s : ι → Set α) (f : α → β) : ⨅ a ∈ ⋃ i, s i, f a = ⨅ (i) (a ∈ s i), f a :=
  iSup_iUnion (β := βᵒᵈ) s f

theorem sSup_iUnion (t : ι → Set β) : sSup (⋃ i, t i) = ⨆ i, sSup (t i) := by
  simp_rw [sSup_eq_iSup, iSup_iUnion]

theorem sSup_sUnion (s : Set (Set β)) : sSup (⋃₀ s) = ⨆ t ∈ s, sSup t := by
  simp only [sUnion_eq_biUnion, sSup_eq_iSup, iSup_iUnion]

theorem sInf_sUnion (s : Set (Set β)) : sInf (⋃₀ s) = ⨅ t ∈ s, sInf t :=
  sSup_sUnion (β := βᵒᵈ) s

lemma iSup_sUnion (S : Set (Set α)) (f : α → β) :
    (⨆ x ∈ ⋃₀ S, f x) = ⨆ (s ∈ S) (x ∈ s), f x := by
  rw [sUnion_eq_iUnion, iSup_iUnion, ← iSup_subtype'']

lemma iInf_sUnion (S : Set (Set α)) (f : α → β) :
    (⨅ x ∈ ⋃₀ S, f x) = ⨅ (s ∈ S) (x ∈ s), f x := by
  rw [sUnion_eq_iUnion, iInf_iUnion, ← iInf_subtype'']

lemma forall_sUnion {S : Set (Set α)} {p : α → Prop} :
    (∀ x ∈ ⋃₀ S, p x) ↔ ∀ s ∈ S, ∀ x ∈ s, p x := by
  simp_rw [← iInf_Prop_eq, iInf_sUnion]

lemma exists_sUnion {S : Set (Set α)} {p : α → Prop} :
    (∃ x ∈ ⋃₀ S, p x) ↔ ∃ s ∈ S, ∃ x ∈ s, p x := by
  simp_rw [← exists_prop, ← iSup_Prop_eq, iSup_sUnion]
