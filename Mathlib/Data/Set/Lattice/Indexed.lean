/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Set.BooleanAlgebra

/-!
# Indexed unions and intersections of sets

This file develops the basic theory of indexed unions and intersections of sets. It includes
membership and inclusion lemmas, congruence and monotonicity results, interaction with complements
and Boolean operations, unions and intersections indexed by propositions, and reindexing results
for sums and dependent sums.

In lemma names, `iUnion₂` and `iInter₂` refer to two nested indexed unions or intersections,
while `biUnion` and `biInter` refer to the special case in which the inner index is a membership
proof.
-/

public section

open Function

variable {α β γ : Type*} {ι ι' ι₂ : Sort*} {κ : ι → Sort*} {κ' : ι' → Sort*}

namespace Set

/-! ### Basic membership lemmas -/

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

theorem ofPred_exists (p : ι → β → Prop) : { x | ∃ i, p i x } = ⋃ i, { x | p i x } :=
  ext fun _ => .symm <| mem_iUnion

@[deprecated (since := "2026-07-09")] alias setOf_exists := ofPred_exists

theorem ofPred_forall (p : ι → β → Prop) : { x | ∀ i, p i x } = ⋂ i, { x | p i x } :=
  ext fun _ => .symm <| mem_iInter

@[deprecated (since := "2026-07-09")] alias setOf_forall := ofPred_forall

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

theorem iUnion_ofPred (P : ι → α → Prop) : ⋃ i, { x : α | P i x } = { x : α | ∃ i, P i x } := by
  ext
  exact mem_iUnion

@[deprecated (since := "2026-07-09")] alias iUnion_setOf := iUnion_ofPred

theorem iInter_ofPred (P : ι → α → Prop) : ⋂ i, { x : α | P i x } = { x : α | ∀ i, P i x } := by
  ext
  exact mem_iInter

@[deprecated (since := "2026-07-09")] alias iInter_setOf := iInter_ofPred

theorem forall_mem_iUnion {p : α → Prop} {f : ι → Set α} :
    (∀ x ∈ ⋃ i, f i, p x) ↔ (∀ i, ∀ x ∈ f i, p x) := by
  simp_rw [mem_iUnion, forall_exists_index]
  apply forall_comm

theorem exists_mem_iUnion {p : α → Prop} {f : ι → Set α} :
    (∃ x ∈ ⋃ i, f i, p x) ↔ (∃ i, ∃ x ∈ f i, p x) := by
  grind [mem_iUnion]

theorem forall_mem_iUnion₂ {p : α → Prop} {f : (i : ι) → κ i → Set α} :
    (∀ x ∈ ⋃ (i) (j), f i j, p x) ↔ (∀ i j, ∀ x ∈ f i j, p x) := by
  simp_rw [forall_mem_iUnion]

theorem exists_mem_iUnion₂ {p : α → Prop} {f : (i : ι) → κ i → Set α} :
    (∃ x ∈ ⋃ (i) (j), f i j, p x) ↔ (∃ i j, ∃ x ∈ f i j, p x) := by
  simp_rw [exists_mem_iUnion]

theorem forall_mem_biUnion {p : α → Prop} {f : ι → Set α} {q : ι → Prop} :
    (∀ x ∈ ⋃ (i : ι) (_ : q i), f i, p x) ↔ (∀ i, q i → ∀ x ∈ f i, p x) :=
  forall_mem_iUnion₂

theorem exists_mem_biUnion {p : α → Prop} {f : (i : ι) → Set α} {q : ι → Prop} :
    (∃ x ∈ ⋃ (i : ι) (_ : q i), f i, p x) ↔ (∃ i, q i ∧ ∃ x ∈ f i, p x) := by
  rw [exists_mem_iUnion₂]
  simp_rw [exists_prop]

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

theorem iUnion_sdiff (s : Set β) (t : ι → Set β) : (⋃ i, t i) \ s = ⋃ i, t i \ s := by
  simp only [sdiff_eq, iUnion_inter]

@[deprecated (since := "2026-06-03")] alias iUnion_diff := iUnion_sdiff

theorem sdiff_iUnion [Nonempty ι] (s : Set β) (t : ι → Set β) : (s \ ⋃ i, t i) = ⋂ i, s \ t i := by
  simp only [sdiff_eq, compl_iUnion, inter_iInter]

@[deprecated (since := "2026-06-03")] alias diff_iUnion := sdiff_iUnion

theorem sdiff_iInter (s : Set β) (t : ι → Set β) : (s \ ⋂ i, t i) = ⋃ i, s \ t i := by
  simp only [sdiff_eq, compl_iInter, inter_iUnion]

@[deprecated (since := "2026-06-03")] alias diff_iInter := sdiff_iInter

section SymmDiff

open scoped symmDiff

lemma iUnion_symmDiff_subset {s : Set α} [Nonempty ι] {f : ι → Set α} :
    (⋃ n, f n) ∆ s ⊆ ⋃ n, f n ∆ s :=
  iSup_symmDiff_le

lemma symmDiff_iUnion_subset {s : Set α} [Nonempty ι] {f : ι → Set α} :
    s ∆ (⋃ n, f n) ⊆ ⋃ n, s ∆ f n :=
  symmDiff_iSup_le

lemma iUnion_symmDiff_iUnion_subset {f g : ι → Set α} :
    (⋃ n, f n) ∆ ⋃ n, g n ⊆ ⋃ n, f n ∆ g n :=
  iSup_symmDiff_iSup_le

lemma sUnion_symmDiff_subset {s : Set α} {S : Set (Set α)} (hS : S.Nonempty) :
    (⋃₀ S) ∆ s ⊆ ⋃₀ ((· ∆ s) '' S) :=
  sSup_symmDiff_le hS

lemma symmDiff_sUnion_subset {s : Set α} {S : Set (Set α)} (hS : S.Nonempty) :
    s ∆ (⋃₀ S) ⊆ ⋃₀ ((s ∆ ·) '' S) :=
  symmDiff_sSup_le hS

lemma sUnion_symmDiff_sUnion_subset {S T : Set (Set α)} (hS : S.Nonempty)
    (hT : T.Nonempty) :
    (⋃₀ S) ∆ ⋃₀ T ⊆  ⋃₀ (image2 (· ∆ ·) S T) :=
  sSup_symmDiff_sSup_le hS hT

end SymmDiff

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

end Set
