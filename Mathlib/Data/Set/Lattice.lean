/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Logic.Pairwise
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Directed
import Mathlib.Order.GaloisConnection

#align_import data.set.lattice from "leanprover-community/mathlib"@"b86832321b586c6ac23ef8cdef6a7a27e42b13bd"

/-!
# The set lattice

This file provides usual set notation for unions and intersections, a `CompleteLattice` instance
for `Set α`, and some more set constructions.

## Main declarations

* `Set.iUnion`: **i**ndexed **union**. Union of an indexed family of sets.
* `Set.iInter`: **i**ndexed **inter**section. Intersection of an indexed family of sets.
* `Set.sInter`: **s**et **inter**section. Intersection of sets belonging to a set of sets.
* `Set.sUnion`: **s**et **union**. Union of sets belonging to a set of sets.
* `Set.sInter_eq_biInter`, `Set.sUnion_eq_biInter`: Shows that `⋂₀ s = ⋂ x ∈ s, x` and
  `⋃₀ s = ⋃ x ∈ s, x`.
* `Set.completeAtomicBooleanAlgebra`: `Set α` is a `CompleteAtomicBooleanAlgebra` with `≤ = ⊆`,
  `< = ⊂`, `⊓ = ∩`, `⊔ = ∪`, `⨅ = ⋂`, `⨆ = ⋃` and `\` as the set difference.
  See `Set.BooleanAlgebra`.
* `Set.kernImage`: For a function `f : α → β`, `s.kernImage f` is the set of `y` such that
  `f ⁻¹ y ⊆ s`.
* `Set.seq`: Union of the image of a set under a **seq**uence of functions. `seq s t` is the union
  of `f '' t` over all `f ∈ s`, where `t : Set α` and `s : Set (α → β)`.
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

open Function Set

universe u

variable {α β γ : Type*} {ι ι' ι₂ : Sort*} {κ κ₁ κ₂ : ι → Sort*} {κ' : ι' → Sort*}

namespace Set

/-! ### Complete lattice and complete Boolean algebra instances -/

theorem mem_iUnion₂ {x : γ} {s : ∀ i, κ i → Set γ} : (x ∈ ⋃ (i) (j), s i j) ↔ ∃ i j, x ∈ s i j := by
  simp_rw [mem_iUnion]
#align set.mem_Union₂ Set.mem_iUnion₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem mem_iInter₂ {x : γ} {s : ∀ i, κ i → Set γ} : (x ∈ ⋂ (i) (j), s i j) ↔ ∀ i j, x ∈ s i j := by
  simp_rw [mem_iInter]
#align set.mem_Inter₂ Set.mem_iInter₂

theorem mem_iUnion_of_mem {s : ι → Set α} {a : α} (i : ι) (ha : a ∈ s i) : a ∈ ⋃ i, s i :=
  mem_iUnion.2 ⟨i, ha⟩
#align set.mem_Union_of_mem Set.mem_iUnion_of_mem

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem mem_iUnion₂_of_mem {s : ∀ i, κ i → Set α} {a : α} {i : ι} (j : κ i) (ha : a ∈ s i j) :
    a ∈ ⋃ (i) (j), s i j :=
  mem_iUnion₂.2 ⟨i, j, ha⟩
#align set.mem_Union₂_of_mem Set.mem_iUnion₂_of_mem

theorem mem_iInter_of_mem {s : ι → Set α} {a : α} (h : ∀ i, a ∈ s i) : a ∈ ⋂ i, s i :=
  mem_iInter.2 h
#align set.mem_Inter_of_mem Set.mem_iInter_of_mem

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem mem_iInter₂_of_mem {s : ∀ i, κ i → Set α} {a : α} (h : ∀ i j, a ∈ s i j) :
    a ∈ ⋂ (i) (j), s i j :=
  mem_iInter₂.2 h
#align set.mem_Inter₂_of_mem Set.mem_iInter₂_of_mem

instance completeAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra (Set α) :=
  { instBooleanAlgebraSet with
    le_sSup := fun s t t_in a a_in => ⟨t, t_in, a_in⟩
    sSup_le := fun s t h a ⟨t', ⟨t'_in, a_in⟩⟩ => h t' t'_in a_in
    le_sInf := fun s t h a a_in t' t'_in => h t' t'_in a_in
    sInf_le := fun s t t_in a h => h _ t_in
    iInf_iSup_eq := by intros; ext; simp [Classical.skolem] }

section GaloisConnection

variable {f : α → β}

protected theorem image_preimage : GaloisConnection (image f) (preimage f) := fun _ _ =>
  image_subset_iff
#align set.image_preimage Set.image_preimage

protected theorem preimage_kernImage : GaloisConnection (preimage f) (kernImage f) := fun _ _ =>
  subset_kernImage_iff.symm
#align set.preimage_kern_image Set.preimage_kernImage

end GaloisConnection

section kernImage

variable {f : α → β}

lemma kernImage_mono : Monotone (kernImage f) :=
  Set.preimage_kernImage.monotone_u

lemma kernImage_eq_compl {s : Set α} : kernImage f s = (f '' sᶜ)ᶜ :=
  Set.preimage_kernImage.u_unique (Set.image_preimage.compl)
    (fun t ↦ compl_compl (f ⁻¹' t) ▸ Set.preimage_compl)

lemma kernImage_compl {s : Set α} : kernImage f (sᶜ) = (f '' s)ᶜ := by
  rw [kernImage_eq_compl, compl_compl]

lemma kernImage_empty : kernImage f ∅ = (range f)ᶜ := by
  rw [kernImage_eq_compl, compl_empty, image_univ]

lemma kernImage_preimage_eq_iff {s : Set β} : kernImage f (f ⁻¹' s) = s ↔ (range f)ᶜ ⊆ s := by
  rw [kernImage_eq_compl, ← preimage_compl, compl_eq_comm, eq_comm, image_preimage_eq_iff,
      compl_subset_comm]

lemma compl_range_subset_kernImage {s : Set α} : (range f)ᶜ ⊆ kernImage f s := by
  rw [← kernImage_empty]
  exact kernImage_mono (empty_subset _)

lemma kernImage_union_preimage {s : Set α} {t : Set β} :
    kernImage f (s ∪ f ⁻¹' t) = kernImage f s ∪ t := by
  rw [kernImage_eq_compl, kernImage_eq_compl, compl_union, ← preimage_compl, image_inter_preimage,
      compl_inter, compl_compl]

lemma kernImage_preimage_union {s : Set α} {t : Set β} :
    kernImage f (f ⁻¹' t ∪ s) = t ∪ kernImage f s := by
  rw [union_comm, kernImage_union_preimage, union_comm]

end kernImage

/-! ### Union and intersection over an indexed family of sets -/


instance : OrderTop (Set α) where
  top := univ
  le_top := by simp

@[congr]
theorem iUnion_congr_Prop {p q : Prop} {f₁ : p → Set α} {f₂ : q → Set α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ = iUnion f₂ :=
  iSup_congr_Prop pq f
#align set.Union_congr_Prop Set.iUnion_congr_Prop

@[congr]
theorem iInter_congr_Prop {p q : Prop} {f₁ : p → Set α} {f₂ : q → Set α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ = iInter f₂ :=
  iInf_congr_Prop pq f
#align set.Inter_congr_Prop Set.iInter_congr_Prop

theorem iUnion_plift_up (f : PLift ι → Set α) : ⋃ i, f (PLift.up i) = ⋃ i, f i :=
  iSup_plift_up _
#align set.Union_plift_up Set.iUnion_plift_up

theorem iUnion_plift_down (f : ι → Set α) : ⋃ i, f (PLift.down i) = ⋃ i, f i :=
  iSup_plift_down _
#align set.Union_plift_down Set.iUnion_plift_down

theorem iInter_plift_up (f : PLift ι → Set α) : ⋂ i, f (PLift.up i) = ⋂ i, f i :=
  iInf_plift_up _
#align set.Inter_plift_up Set.iInter_plift_up

theorem iInter_plift_down (f : ι → Set α) : ⋂ i, f (PLift.down i) = ⋂ i, f i :=
  iInf_plift_down _
#align set.Inter_plift_down Set.iInter_plift_down

theorem iUnion_eq_if {p : Prop} [Decidable p] (s : Set α) : ⋃ _ : p, s = if p then s else ∅ :=
  iSup_eq_if _
#align set.Union_eq_if Set.iUnion_eq_if

theorem iUnion_eq_dif {p : Prop} [Decidable p] (s : p → Set α) :
    ⋃ h : p, s h = if h : p then s h else ∅ :=
  iSup_eq_dif _
#align set.Union_eq_dif Set.iUnion_eq_dif

theorem iInter_eq_if {p : Prop} [Decidable p] (s : Set α) : ⋂ _ : p, s = if p then s else univ :=
  iInf_eq_if _
#align set.Inter_eq_if Set.iInter_eq_if

theorem iInf_eq_dif {p : Prop} [Decidable p] (s : p → Set α) :
    ⋂ h : p, s h = if h : p then s h else univ :=
  _root_.iInf_eq_dif _
#align set.Infi_eq_dif Set.iInf_eq_dif

theorem exists_set_mem_of_union_eq_top {ι : Type*} (t : Set ι) (s : ι → Set β)
    (w : ⋃ i ∈ t, s i = ⊤) (x : β) : ∃ i ∈ t, x ∈ s i := by
  have p : x ∈ ⊤ := Set.mem_univ x
  rw [← w, Set.mem_iUnion] at p
  simpa using p
#align set.exists_set_mem_of_union_eq_top Set.exists_set_mem_of_union_eq_top

theorem nonempty_of_union_eq_top_of_nonempty {ι : Type*} (t : Set ι) (s : ι → Set α)
    (H : Nonempty α) (w : ⋃ i ∈ t, s i = ⊤) : t.Nonempty := by
  obtain ⟨x, m, -⟩ := exists_set_mem_of_union_eq_top t s w H.some
  exact ⟨x, m⟩
#align set.nonempty_of_union_eq_top_of_nonempty Set.nonempty_of_union_eq_top_of_nonempty

theorem nonempty_of_nonempty_iUnion
    {s : ι → Set α} (h_Union : (⋃ i, s i).Nonempty) : Nonempty ι := by
  obtain ⟨x, hx⟩ := h_Union
  exact ⟨Classical.choose <| mem_iUnion.mp hx⟩

theorem nonempty_of_nonempty_iUnion_eq_univ
    {s : ι → Set α} [Nonempty α] (h_Union : ⋃ i, s i = univ) : Nonempty ι :=
  nonempty_of_nonempty_iUnion (s := s) (by simpa only [h_Union] using univ_nonempty)

theorem setOf_exists (p : ι → β → Prop) : { x | ∃ i, p i x } = ⋃ i, { x | p i x } :=
  ext fun _ => mem_iUnion.symm
#align set.set_of_exists Set.setOf_exists

theorem setOf_forall (p : ι → β → Prop) : { x | ∀ i, p i x } = ⋂ i, { x | p i x } :=
  ext fun _ => mem_iInter.symm
#align set.set_of_forall Set.setOf_forall

theorem iUnion_subset {s : ι → Set α} {t : Set α} (h : ∀ i, s i ⊆ t) : ⋃ i, s i ⊆ t :=
  iSup_le h
#align set.Union_subset Set.iUnion_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iUnion₂_subset {s : ∀ i, κ i → Set α} {t : Set α} (h : ∀ i j, s i j ⊆ t) :
    ⋃ (i) (j), s i j ⊆ t :=
  iUnion_subset fun x => iUnion_subset (h x)
#align set.Union₂_subset Set.iUnion₂_subset

theorem subset_iInter {t : Set β} {s : ι → Set β} (h : ∀ i, t ⊆ s i) : t ⊆ ⋂ i, s i :=
  le_iInf h
#align set.subset_Inter Set.subset_iInter

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem subset_iInter₂ {s : Set α} {t : ∀ i, κ i → Set α} (h : ∀ i j, s ⊆ t i j) :
    s ⊆ ⋂ (i) (j), t i j :=
  subset_iInter fun x => subset_iInter <| h x
#align set.subset_Inter₂ Set.subset_iInter₂

@[simp]
theorem iUnion_subset_iff {s : ι → Set α} {t : Set α} : ⋃ i, s i ⊆ t ↔ ∀ i, s i ⊆ t :=
  ⟨fun h _ => Subset.trans (le_iSup s _) h, iUnion_subset⟩
#align set.Union_subset_iff Set.iUnion_subset_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iUnion₂_subset_iff {s : ∀ i, κ i → Set α} {t : Set α} :
    ⋃ (i) (j), s i j ⊆ t ↔ ∀ i j, s i j ⊆ t := by simp_rw [iUnion_subset_iff]
#align set.Union₂_subset_iff Set.iUnion₂_subset_iff

@[simp]
theorem subset_iInter_iff {s : Set α} {t : ι → Set α} : (s ⊆ ⋂ i, t i) ↔ ∀ i, s ⊆ t i :=
  le_iInf_iff
#align set.subset_Inter_iff Set.subset_iInter_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
-- Porting note (#10618): removing `simp`. `simp` can prove it
theorem subset_iInter₂_iff {s : Set α} {t : ∀ i, κ i → Set α} :
    (s ⊆ ⋂ (i) (j), t i j) ↔ ∀ i j, s ⊆ t i j := by simp_rw [subset_iInter_iff]
#align set.subset_Inter₂_iff Set.subset_iInter₂_iff

theorem subset_iUnion : ∀ (s : ι → Set β) (i : ι), s i ⊆ ⋃ i, s i :=
  le_iSup
#align set.subset_Union Set.subset_iUnion

theorem iInter_subset : ∀ (s : ι → Set β) (i : ι), ⋂ i, s i ⊆ s i :=
  iInf_le
#align set.Inter_subset Set.iInter_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem subset_iUnion₂ {s : ∀ i, κ i → Set α} (i : ι) (j : κ i) : s i j ⊆ ⋃ (i') (j'), s i' j' :=
  le_iSup₂ i j
#align set.subset_Union₂ Set.subset_iUnion₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iInter₂_subset {s : ∀ i, κ i → Set α} (i : ι) (j : κ i) : ⋂ (i) (j), s i j ⊆ s i j :=
  iInf₂_le i j
#align set.Inter₂_subset Set.iInter₂_subset

/-- This rather trivial consequence of `subset_iUnion`is convenient with `apply`, and has `i`
explicit for this purpose. -/
theorem subset_iUnion_of_subset {s : Set α} {t : ι → Set α} (i : ι) (h : s ⊆ t i) : s ⊆ ⋃ i, t i :=
  le_iSup_of_le i h
#align set.subset_Union_of_subset Set.subset_iUnion_of_subset

/-- This rather trivial consequence of `iInter_subset`is convenient with `apply`, and has `i`
explicit for this purpose. -/
theorem iInter_subset_of_subset {s : ι → Set α} {t : Set α} (i : ι) (h : s i ⊆ t) :
    ⋂ i, s i ⊆ t :=
  iInf_le_of_le i h
#align set.Inter_subset_of_subset Set.iInter_subset_of_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/-- This rather trivial consequence of `subset_iUnion₂` is convenient with `apply`, and has `i` and
`j` explicit for this purpose. -/
theorem subset_iUnion₂_of_subset {s : Set α} {t : ∀ i, κ i → Set α} (i : ι) (j : κ i)
    (h : s ⊆ t i j) : s ⊆ ⋃ (i) (j), t i j :=
  le_iSup₂_of_le i j h
#align set.subset_Union₂_of_subset Set.subset_iUnion₂_of_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/-- This rather trivial consequence of `iInter₂_subset` is convenient with `apply`, and has `i` and
`j` explicit for this purpose. -/
theorem iInter₂_subset_of_subset {s : ∀ i, κ i → Set α} {t : Set α} (i : ι) (j : κ i)
    (h : s i j ⊆ t) : ⋂ (i) (j), s i j ⊆ t :=
  iInf₂_le_of_le i j h
#align set.Inter₂_subset_of_subset Set.iInter₂_subset_of_subset

theorem iUnion_mono {s t : ι → Set α} (h : ∀ i, s i ⊆ t i) : ⋃ i, s i ⊆ ⋃ i, t i :=
  iSup_mono h
#align set.Union_mono Set.iUnion_mono

@[gcongr]
theorem iUnion_mono'' {s t : ι → Set α} (h : ∀ i, s i ⊆ t i) : iUnion s ⊆ iUnion t :=
  iSup_mono h

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iUnion₂_mono {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j ⊆ t i j) :
    ⋃ (i) (j), s i j ⊆ ⋃ (i) (j), t i j :=
  iSup₂_mono h
#align set.Union₂_mono Set.iUnion₂_mono

theorem iInter_mono {s t : ι → Set α} (h : ∀ i, s i ⊆ t i) : ⋂ i, s i ⊆ ⋂ i, t i :=
  iInf_mono h
#align set.Inter_mono Set.iInter_mono

@[gcongr]
theorem iInter_mono'' {s t : ι → Set α} (h : ∀ i, s i ⊆ t i) : iInter s ⊆ iInter t :=
  iInf_mono h

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iInter₂_mono {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j ⊆ t i j) :
    ⋂ (i) (j), s i j ⊆ ⋂ (i) (j), t i j :=
  iInf₂_mono h
#align set.Inter₂_mono Set.iInter₂_mono

theorem iUnion_mono' {s : ι → Set α} {t : ι₂ → Set α} (h : ∀ i, ∃ j, s i ⊆ t j) :
    ⋃ i, s i ⊆ ⋃ i, t i :=
  iSup_mono' h
#align set.Union_mono' Set.iUnion_mono'

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i' j') -/
theorem iUnion₂_mono' {s : ∀ i, κ i → Set α} {t : ∀ i', κ' i' → Set α}
    (h : ∀ i j, ∃ i' j', s i j ⊆ t i' j') : ⋃ (i) (j), s i j ⊆ ⋃ (i') (j'), t i' j' :=
  iSup₂_mono' h
#align set.Union₂_mono' Set.iUnion₂_mono'

theorem iInter_mono' {s : ι → Set α} {t : ι' → Set α} (h : ∀ j, ∃ i, s i ⊆ t j) :
    ⋂ i, s i ⊆ ⋂ j, t j :=
  Set.subset_iInter fun j =>
    let ⟨i, hi⟩ := h j
    iInter_subset_of_subset i hi
#align set.Inter_mono' Set.iInter_mono'

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i' j') -/
theorem iInter₂_mono' {s : ∀ i, κ i → Set α} {t : ∀ i', κ' i' → Set α}
    (h : ∀ i' j', ∃ i j, s i j ⊆ t i' j') : ⋂ (i) (j), s i j ⊆ ⋂ (i') (j'), t i' j' :=
  subset_iInter₂_iff.2 fun i' j' =>
    let ⟨_, _, hst⟩ := h i' j'
    (iInter₂_subset _ _).trans hst
#align set.Inter₂_mono' Set.iInter₂_mono'

theorem iUnion₂_subset_iUnion (κ : ι → Sort*) (s : ι → Set α) :
    ⋃ (i) (_ : κ i), s i ⊆ ⋃ i, s i :=
  iUnion_mono fun _ => iUnion_subset fun _ => Subset.rfl
#align set.Union₂_subset_Union Set.iUnion₂_subset_iUnion

theorem iInter_subset_iInter₂ (κ : ι → Sort*) (s : ι → Set α) :
    ⋂ i, s i ⊆ ⋂ (i) (_ : κ i), s i :=
  iInter_mono fun _ => subset_iInter fun _ => Subset.rfl
#align set.Inter_subset_Inter₂ Set.iInter_subset_iInter₂

theorem iUnion_setOf (P : ι → α → Prop) : ⋃ i, { x : α | P i x } = { x : α | ∃ i, P i x } := by
  ext
  exact mem_iUnion
#align set.Union_set_of Set.iUnion_setOf

theorem iInter_setOf (P : ι → α → Prop) : ⋂ i, { x : α | P i x } = { x : α | ∀ i, P i x } := by
  ext
  exact mem_iInter
#align set.Inter_set_of Set.iInter_setOf

theorem iUnion_congr_of_surjective {f : ι → Set α} {g : ι₂ → Set α} (h : ι → ι₂) (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : ⋃ x, f x = ⋃ y, g y :=
  h1.iSup_congr h h2
#align set.Union_congr_of_surjective Set.iUnion_congr_of_surjective

theorem iInter_congr_of_surjective {f : ι → Set α} {g : ι₂ → Set α} (h : ι → ι₂) (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : ⋂ x, f x = ⋂ y, g y :=
  h1.iInf_congr h h2
#align set.Inter_congr_of_surjective Set.iInter_congr_of_surjective

lemma iUnion_congr {s t : ι → Set α} (h : ∀ i, s i = t i) : ⋃ i, s i = ⋃ i, t i := iSup_congr h
#align set.Union_congr Set.iUnion_congr
lemma iInter_congr {s t : ι → Set α} (h : ∀ i, s i = t i) : ⋂ i, s i = ⋂ i, t i := iInf_congr h
#align set.Inter_congr Set.iInter_congr

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
lemma iUnion₂_congr {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j = t i j) :
    ⋃ (i) (j), s i j = ⋃ (i) (j), t i j :=
  iUnion_congr fun i => iUnion_congr <| h i
#align set.Union₂_congr Set.iUnion₂_congr

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
lemma iInter₂_congr {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j = t i j) :
    ⋂ (i) (j), s i j = ⋂ (i) (j), t i j :=
  iInter_congr fun i => iInter_congr <| h i
#align set.Inter₂_congr Set.iInter₂_congr

section Nonempty
variable [Nonempty ι] {f : ι → Set α} {s : Set α}

lemma iUnion_const (s : Set β) : ⋃ _ : ι, s = s := iSup_const
#align set.Union_const Set.iUnion_const
lemma iInter_const (s : Set β) : ⋂ _ : ι, s = s := iInf_const
#align set.Inter_const Set.iInter_const

lemma iUnion_eq_const (hf : ∀ i, f i = s) : ⋃ i, f i = s :=
  (iUnion_congr hf).trans <| iUnion_const _
#align set.Union_eq_const Set.iUnion_eq_const

lemma iInter_eq_const (hf : ∀ i, f i = s) : ⋂ i, f i = s :=
  (iInter_congr hf).trans <| iInter_const _
#align set.Inter_eq_const Set.iInter_eq_const

end Nonempty

@[simp]
theorem compl_iUnion (s : ι → Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s i)ᶜ :=
  compl_iSup
#align set.compl_Union Set.compl_iUnion

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem compl_iUnion₂ (s : ∀ i, κ i → Set α) : (⋃ (i) (j), s i j)ᶜ = ⋂ (i) (j), (s i j)ᶜ := by
  simp_rw [compl_iUnion]
#align set.compl_Union₂ Set.compl_iUnion₂

@[simp]
theorem compl_iInter (s : ι → Set β) : (⋂ i, s i)ᶜ = ⋃ i, (s i)ᶜ :=
  compl_iInf
#align set.compl_Inter Set.compl_iInter

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem compl_iInter₂ (s : ∀ i, κ i → Set α) : (⋂ (i) (j), s i j)ᶜ = ⋃ (i) (j), (s i j)ᶜ := by
  simp_rw [compl_iInter]
#align set.compl_Inter₂ Set.compl_iInter₂

-- classical -- complete_boolean_algebra
theorem iUnion_eq_compl_iInter_compl (s : ι → Set β) : ⋃ i, s i = (⋂ i, (s i)ᶜ)ᶜ := by
  simp only [compl_iInter, compl_compl]
#align set.Union_eq_compl_Inter_compl Set.iUnion_eq_compl_iInter_compl

-- classical -- complete_boolean_algebra
theorem iInter_eq_compl_iUnion_compl (s : ι → Set β) : ⋂ i, s i = (⋃ i, (s i)ᶜ)ᶜ := by
  simp only [compl_iUnion, compl_compl]
#align set.Inter_eq_compl_Union_compl Set.iInter_eq_compl_iUnion_compl

theorem inter_iUnion (s : Set β) (t : ι → Set β) : (s ∩ ⋃ i, t i) = ⋃ i, s ∩ t i :=
  inf_iSup_eq _ _
#align set.inter_Union Set.inter_iUnion

theorem iUnion_inter (s : Set β) (t : ι → Set β) : (⋃ i, t i) ∩ s = ⋃ i, t i ∩ s :=
  iSup_inf_eq _ _
#align set.Union_inter Set.iUnion_inter

theorem iUnion_union_distrib (s : ι → Set β) (t : ι → Set β) :
    ⋃ i, s i ∪ t i = (⋃ i, s i) ∪ ⋃ i, t i :=
  iSup_sup_eq
#align set.Union_union_distrib Set.iUnion_union_distrib

theorem iInter_inter_distrib (s : ι → Set β) (t : ι → Set β) :
    ⋂ i, s i ∩ t i = (⋂ i, s i) ∩ ⋂ i, t i :=
  iInf_inf_eq
#align set.Inter_inter_distrib Set.iInter_inter_distrib

theorem union_iUnion [Nonempty ι] (s : Set β) (t : ι → Set β) : (s ∪ ⋃ i, t i) = ⋃ i, s ∪ t i :=
  sup_iSup
#align set.union_Union Set.union_iUnion

theorem iUnion_union [Nonempty ι] (s : Set β) (t : ι → Set β) : (⋃ i, t i) ∪ s = ⋃ i, t i ∪ s :=
  iSup_sup
#align set.Union_union Set.iUnion_union

theorem inter_iInter [Nonempty ι] (s : Set β) (t : ι → Set β) : (s ∩ ⋂ i, t i) = ⋂ i, s ∩ t i :=
  inf_iInf
#align set.inter_Inter Set.inter_iInter

theorem iInter_inter [Nonempty ι] (s : Set β) (t : ι → Set β) : (⋂ i, t i) ∩ s = ⋂ i, t i ∩ s :=
  iInf_inf
#align set.Inter_inter Set.iInter_inter

-- classical
theorem union_iInter (s : Set β) (t : ι → Set β) : (s ∪ ⋂ i, t i) = ⋂ i, s ∪ t i :=
  sup_iInf_eq _ _
#align set.union_Inter Set.union_iInter

theorem iInter_union (s : ι → Set β) (t : Set β) : (⋂ i, s i) ∪ t = ⋂ i, s i ∪ t :=
  iInf_sup_eq _ _
#align set.Inter_union Set.iInter_union

theorem iUnion_diff (s : Set β) (t : ι → Set β) : (⋃ i, t i) \ s = ⋃ i, t i \ s :=
  iUnion_inter _ _
#align set.Union_diff Set.iUnion_diff

theorem diff_iUnion [Nonempty ι] (s : Set β) (t : ι → Set β) : (s \ ⋃ i, t i) = ⋂ i, s \ t i := by
  rw [diff_eq, compl_iUnion, inter_iInter]; rfl
#align set.diff_Union Set.diff_iUnion

theorem diff_iInter (s : Set β) (t : ι → Set β) : (s \ ⋂ i, t i) = ⋃ i, s \ t i := by
  rw [diff_eq, compl_iInter, inter_iUnion]; rfl
#align set.diff_Inter Set.diff_iInter

theorem iUnion_inter_subset {ι α} {s t : ι → Set α} : ⋃ i, s i ∩ t i ⊆ (⋃ i, s i) ∩ ⋃ i, t i :=
  le_iSup_inf_iSup s t
#align set.Union_inter_subset Set.iUnion_inter_subset

theorem iUnion_inter_of_monotone {ι α} [Preorder ι] [IsDirected ι (· ≤ ·)] {s t : ι → Set α}
    (hs : Monotone s) (ht : Monotone t) : ⋃ i, s i ∩ t i = (⋃ i, s i) ∩ ⋃ i, t i :=
  iSup_inf_of_monotone hs ht
#align set.Union_inter_of_monotone Set.iUnion_inter_of_monotone

theorem iUnion_inter_of_antitone {ι α} [Preorder ι] [IsDirected ι (swap (· ≤ ·))] {s t : ι → Set α}
    (hs : Antitone s) (ht : Antitone t) : ⋃ i, s i ∩ t i = (⋃ i, s i) ∩ ⋃ i, t i :=
  iSup_inf_of_antitone hs ht
#align set.Union_inter_of_antitone Set.iUnion_inter_of_antitone

theorem iInter_union_of_monotone {ι α} [Preorder ι] [IsDirected ι (swap (· ≤ ·))] {s t : ι → Set α}
    (hs : Monotone s) (ht : Monotone t) : ⋂ i, s i ∪ t i = (⋂ i, s i) ∪ ⋂ i, t i :=
  iInf_sup_of_monotone hs ht
#align set.Inter_union_of_monotone Set.iInter_union_of_monotone

theorem iInter_union_of_antitone {ι α} [Preorder ι] [IsDirected ι (· ≤ ·)] {s t : ι → Set α}
    (hs : Antitone s) (ht : Antitone t) : ⋂ i, s i ∪ t i = (⋂ i, s i) ∪ ⋂ i, t i :=
  iInf_sup_of_antitone hs ht
#align set.Inter_union_of_antitone Set.iInter_union_of_antitone

/-- An equality version of this lemma is `iUnion_iInter_of_monotone` in `Data.Set.Finite`. -/
theorem iUnion_iInter_subset {s : ι → ι' → Set α} : (⋃ j, ⋂ i, s i j) ⊆ ⋂ i, ⋃ j, s i j :=
  iSup_iInf_le_iInf_iSup (flip s)
#align set.Union_Inter_subset Set.iUnion_iInter_subset

theorem iUnion_option {ι} (s : Option ι → Set α) : ⋃ o, s o = s none ∪ ⋃ i, s (some i) :=
  iSup_option s
#align set.Union_option Set.iUnion_option

theorem iInter_option {ι} (s : Option ι → Set α) : ⋂ o, s o = s none ∩ ⋂ i, s (some i) :=
  iInf_option s
#align set.Inter_option Set.iInter_option

section

variable (p : ι → Prop) [DecidablePred p]

theorem iUnion_dite (f : ∀ i, p i → Set α) (g : ∀ i, ¬p i → Set α) :
    ⋃ i, (if h : p i then f i h else g i h) = (⋃ (i) (h : p i), f i h) ∪ ⋃ (i) (h : ¬p i), g i h :=
  iSup_dite _ _ _
#align set.Union_dite Set.iUnion_dite

theorem iUnion_ite (f g : ι → Set α) :
    ⋃ i, (if p i then f i else g i) = (⋃ (i) (_ : p i), f i) ∪ ⋃ (i) (_ : ¬p i), g i :=
  iUnion_dite _ _ _
#align set.Union_ite Set.iUnion_ite

theorem iInter_dite (f : ∀ i, p i → Set α) (g : ∀ i, ¬p i → Set α) :
    ⋂ i, (if h : p i then f i h else g i h) = (⋂ (i) (h : p i), f i h) ∩ ⋂ (i) (h : ¬p i), g i h :=
  iInf_dite _ _ _
#align set.Inter_dite Set.iInter_dite

theorem iInter_ite (f g : ι → Set α) :
    ⋂ i, (if p i then f i else g i) = (⋂ (i) (_ : p i), f i) ∩ ⋂ (i) (_ : ¬p i), g i :=
  iInter_dite _ _ _
#align set.Inter_ite Set.iInter_ite

end

theorem image_projection_prod {ι : Type*} {α : ι → Type*} {v : ∀ i : ι, Set (α i)}
    (hv : (pi univ v).Nonempty) (i : ι) :
    ((fun x : ∀ i : ι, α i => x i) '' ⋂ k, (fun x : ∀ j : ι, α j => x k) ⁻¹' v k) = v i := by
  classical
    apply Subset.antisymm
    · simp [iInter_subset]
    · intro y y_in
      simp only [mem_image, mem_iInter, mem_preimage]
      rcases hv with ⟨z, hz⟩
      refine ⟨Function.update z i y, ?_, update_same i y z⟩
      rw [@forall_update_iff ι α _ z i y fun i t => t ∈ v i]
      exact ⟨y_in, fun j _ => by simpa using hz j⟩
#align set.image_projection_prod Set.image_projection_prod

/-! ### Unions and intersections indexed by `Prop` -/


theorem iInter_false {s : False → Set α} : iInter s = univ :=
  iInf_false
#align set.Inter_false Set.iInter_false

theorem iUnion_false {s : False → Set α} : iUnion s = ∅ :=
  iSup_false
#align set.Union_false Set.iUnion_false

@[simp]
theorem iInter_true {s : True → Set α} : iInter s = s trivial :=
  iInf_true
#align set.Inter_true Set.iInter_true

@[simp]
theorem iUnion_true {s : True → Set α} : iUnion s = s trivial :=
  iSup_true
#align set.Union_true Set.iUnion_true

@[simp]
theorem iInter_exists {p : ι → Prop} {f : Exists p → Set α} :
    ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩ :=
  iInf_exists
#align set.Inter_exists Set.iInter_exists

@[simp]
theorem iUnion_exists {p : ι → Prop} {f : Exists p → Set α} :
    ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩ :=
  iSup_exists
#align set.Union_exists Set.iUnion_exists

@[simp]
theorem iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅ :=
  iSup_bot
#align set.Union_empty Set.iUnion_empty

@[simp]
theorem iInter_univ : (⋂ _ : ι, univ : Set α) = univ :=
  iInf_top
#align set.Inter_univ Set.iInter_univ

section

variable {s : ι → Set α}

@[simp]
theorem iUnion_eq_empty : ⋃ i, s i = ∅ ↔ ∀ i, s i = ∅ :=
  iSup_eq_bot
#align set.Union_eq_empty Set.iUnion_eq_empty

@[simp]
theorem iInter_eq_univ : ⋂ i, s i = univ ↔ ∀ i, s i = univ :=
  iInf_eq_top
#align set.Inter_eq_univ Set.iInter_eq_univ

@[simp]
theorem nonempty_iUnion : (⋃ i, s i).Nonempty ↔ ∃ i, (s i).Nonempty := by
  simp [nonempty_iff_ne_empty]
#align set.nonempty_Union Set.nonempty_iUnion

-- Porting note (#10618): removing `simp`. `simp` can prove it
theorem nonempty_biUnion {t : Set α} {s : α → Set β} :
    (⋃ i ∈ t, s i).Nonempty ↔ ∃ i ∈ t, (s i).Nonempty := by simp
#align set.nonempty_bUnion Set.nonempty_biUnion

theorem iUnion_nonempty_index (s : Set α) (t : s.Nonempty → Set β) :
    ⋃ h, t h = ⋃ x ∈ s, t ⟨x, ‹_›⟩ :=
  iSup_exists
#align set.Union_nonempty_index Set.iUnion_nonempty_index

end

@[simp]
theorem iInter_iInter_eq_left {b : β} {s : ∀ x : β, x = b → Set α} :
    ⋂ (x) (h : x = b), s x h = s b rfl :=
  iInf_iInf_eq_left
#align set.Inter_Inter_eq_left Set.iInter_iInter_eq_left

@[simp]
theorem iInter_iInter_eq_right {b : β} {s : ∀ x : β, b = x → Set α} :
    ⋂ (x) (h : b = x), s x h = s b rfl :=
  iInf_iInf_eq_right
#align set.Inter_Inter_eq_right Set.iInter_iInter_eq_right

@[simp]
theorem iUnion_iUnion_eq_left {b : β} {s : ∀ x : β, x = b → Set α} :
    ⋃ (x) (h : x = b), s x h = s b rfl :=
  iSup_iSup_eq_left
#align set.Union_Union_eq_left Set.iUnion_iUnion_eq_left

@[simp]
theorem iUnion_iUnion_eq_right {b : β} {s : ∀ x : β, b = x → Set α} :
    ⋃ (x) (h : b = x), s x h = s b rfl :=
  iSup_iSup_eq_right
#align set.Union_Union_eq_right Set.iUnion_iUnion_eq_right

theorem iInter_or {p q : Prop} (s : p ∨ q → Set α) :
    ⋂ h, s h = (⋂ h : p, s (Or.inl h)) ∩ ⋂ h : q, s (Or.inr h) :=
  iInf_or
#align set.Inter_or Set.iInter_or

theorem iUnion_or {p q : Prop} (s : p ∨ q → Set α) :
    ⋃ h, s h = (⋃ i, s (Or.inl i)) ∪ ⋃ j, s (Or.inr j) :=
  iSup_or
#align set.Union_or Set.iUnion_or

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (hp hq) -/
theorem iUnion_and {p q : Prop} (s : p ∧ q → Set α) : ⋃ h, s h = ⋃ (hp) (hq), s ⟨hp, hq⟩ :=
  iSup_and
#align set.Union_and Set.iUnion_and

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (hp hq) -/
theorem iInter_and {p q : Prop} (s : p ∧ q → Set α) : ⋂ h, s h = ⋂ (hp) (hq), s ⟨hp, hq⟩ :=
  iInf_and
#align set.Inter_and Set.iInter_and

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i i') -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i' i) -/
theorem iUnion_comm (s : ι → ι' → Set α) : ⋃ (i) (i'), s i i' = ⋃ (i') (i), s i i' :=
  iSup_comm
#align set.Union_comm Set.iUnion_comm

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i i') -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i' i) -/
theorem iInter_comm (s : ι → ι' → Set α) : ⋂ (i) (i'), s i i' = ⋂ (i') (i), s i i' :=
  iInf_comm
#align set.Inter_comm Set.iInter_comm

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

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₁ j₁ i₂ j₂) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₂ j₂ i₁ j₁) -/
theorem iUnion₂_comm (s : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Set α) :
    ⋃ (i₁) (j₁) (i₂) (j₂), s i₁ j₁ i₂ j₂ = ⋃ (i₂) (j₂) (i₁) (j₁), s i₁ j₁ i₂ j₂ :=
  iSup₂_comm _
#align set.Union₂_comm Set.iUnion₂_comm

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₁ j₁ i₂ j₂) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₂ j₂ i₁ j₁) -/
theorem iInter₂_comm (s : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Set α) :
    ⋂ (i₁) (j₁) (i₂) (j₂), s i₁ j₁ i₂ j₂ = ⋂ (i₂) (j₂) (i₁) (j₁), s i₁ j₁ i₂ j₂ :=
  iInf₂_comm _
#align set.Inter₂_comm Set.iInter₂_comm

@[simp]
theorem biUnion_and (p : ι → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p x ∧ q x y → Set α) :
    ⋃ (x : ι) (y : ι') (h : p x ∧ q x y), s x y h =
      ⋃ (x : ι) (hx : p x) (y : ι') (hy : q x y), s x y ⟨hx, hy⟩ := by
  simp only [iUnion_and, @iUnion_comm _ ι']
#align set.bUnion_and Set.biUnion_and

@[simp]
theorem biUnion_and' (p : ι' → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p y ∧ q x y → Set α) :
    ⋃ (x : ι) (y : ι') (h : p y ∧ q x y), s x y h =
      ⋃ (y : ι') (hy : p y) (x : ι) (hx : q x y), s x y ⟨hy, hx⟩ := by
  simp only [iUnion_and, @iUnion_comm _ ι]
#align set.bUnion_and' Set.biUnion_and'

@[simp]
theorem biInter_and (p : ι → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p x ∧ q x y → Set α) :
    ⋂ (x : ι) (y : ι') (h : p x ∧ q x y), s x y h =
      ⋂ (x : ι) (hx : p x) (y : ι') (hy : q x y), s x y ⟨hx, hy⟩ := by
  simp only [iInter_and, @iInter_comm _ ι']
#align set.bInter_and Set.biInter_and

@[simp]
theorem biInter_and' (p : ι' → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p y ∧ q x y → Set α) :
    ⋂ (x : ι) (y : ι') (h : p y ∧ q x y), s x y h =
      ⋂ (y : ι') (hy : p y) (x : ι) (hx : q x y), s x y ⟨hy, hx⟩ := by
  simp only [iInter_and, @iInter_comm _ ι]
#align set.bInter_and' Set.biInter_and'

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x h) -/
@[simp]
theorem iUnion_iUnion_eq_or_left {b : β} {p : β → Prop} {s : ∀ x : β, x = b ∨ p x → Set α} :
    ⋃ (x) (h), s x h = s b (Or.inl rfl) ∪ ⋃ (x) (h : p x), s x (Or.inr h) := by
  simp only [iUnion_or, iUnion_union_distrib, iUnion_iUnion_eq_left]
#align set.Union_Union_eq_or_left Set.iUnion_iUnion_eq_or_left

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x h) -/
@[simp]
theorem iInter_iInter_eq_or_left {b : β} {p : β → Prop} {s : ∀ x : β, x = b ∨ p x → Set α} :
    ⋂ (x) (h), s x h = s b (Or.inl rfl) ∩ ⋂ (x) (h : p x), s x (Or.inr h) := by
  simp only [iInter_or, iInter_inter_distrib, iInter_iInter_eq_left]
#align set.Inter_Inter_eq_or_left Set.iInter_iInter_eq_or_left

/-! ### Bounded unions and intersections -/


/-- A specialization of `mem_iUnion₂`. -/
theorem mem_biUnion {s : Set α} {t : α → Set β} {x : α} {y : β} (xs : x ∈ s) (ytx : y ∈ t x) :
    y ∈ ⋃ x ∈ s, t x :=
  mem_iUnion₂_of_mem xs ytx
#align set.mem_bUnion Set.mem_biUnion

/-- A specialization of `mem_iInter₂`. -/
theorem mem_biInter {s : Set α} {t : α → Set β} {y : β} (h : ∀ x ∈ s, y ∈ t x) :
    y ∈ ⋂ x ∈ s, t x :=
  mem_iInter₂_of_mem h
#align set.mem_bInter Set.mem_biInter

/-- A specialization of `subset_iUnion₂`. -/
theorem subset_biUnion_of_mem {s : Set α} {u : α → Set β} {x : α} (xs : x ∈ s) :
    u x ⊆ ⋃ x ∈ s, u x :=
-- Porting note: Why is this not just `subset_iUnion₂ x xs`?
  @subset_iUnion₂ β α (· ∈ s) (fun i _ => u i) x xs
#align set.subset_bUnion_of_mem Set.subset_biUnion_of_mem

/-- A specialization of `iInter₂_subset`. -/
theorem biInter_subset_of_mem {s : Set α} {t : α → Set β} {x : α} (xs : x ∈ s) :
    ⋂ x ∈ s, t x ⊆ t x :=
  iInter₂_subset x xs
#align set.bInter_subset_of_mem Set.biInter_subset_of_mem

theorem biUnion_subset_biUnion_left {s s' : Set α} {t : α → Set β} (h : s ⊆ s') :
    ⋃ x ∈ s, t x ⊆ ⋃ x ∈ s', t x :=
  iUnion₂_subset fun _ hx => subset_biUnion_of_mem <| h hx
#align set.bUnion_subset_bUnion_left Set.biUnion_subset_biUnion_left

theorem biInter_subset_biInter_left {s s' : Set α} {t : α → Set β} (h : s' ⊆ s) :
    ⋂ x ∈ s, t x ⊆ ⋂ x ∈ s', t x :=
  subset_iInter₂ fun _ hx => biInter_subset_of_mem <| h hx
#align set.bInter_subset_bInter_left Set.biInter_subset_biInter_left

theorem biUnion_mono {s s' : Set α} {t t' : α → Set β} (hs : s' ⊆ s) (h : ∀ x ∈ s, t x ⊆ t' x) :
    ⋃ x ∈ s', t x ⊆ ⋃ x ∈ s, t' x :=
  (biUnion_subset_biUnion_left hs).trans <| iUnion₂_mono h
#align set.bUnion_mono Set.biUnion_mono

theorem biInter_mono {s s' : Set α} {t t' : α → Set β} (hs : s ⊆ s') (h : ∀ x ∈ s, t x ⊆ t' x) :
    ⋂ x ∈ s', t x ⊆ ⋂ x ∈ s, t' x :=
  (biInter_subset_biInter_left hs).trans <| iInter₂_mono h
#align set.bInter_mono Set.biInter_mono

theorem biUnion_eq_iUnion (s : Set α) (t : ∀ x ∈ s, Set β) :
    ⋃ x ∈ s, t x ‹_› = ⋃ x : s, t x x.2 :=
  iSup_subtype'
#align set.bUnion_eq_Union Set.biUnion_eq_iUnion

theorem biInter_eq_iInter (s : Set α) (t : ∀ x ∈ s, Set β) :
    ⋂ x ∈ s, t x ‹_› = ⋂ x : s, t x x.2 :=
  iInf_subtype'
#align set.bInter_eq_Inter Set.biInter_eq_iInter

theorem iUnion_subtype (p : α → Prop) (s : { x // p x } → Set β) :
    ⋃ x : { x // p x }, s x = ⋃ (x) (hx : p x), s ⟨x, hx⟩ :=
  iSup_subtype
#align set.Union_subtype Set.iUnion_subtype

theorem iInter_subtype (p : α → Prop) (s : { x // p x } → Set β) :
    ⋂ x : { x // p x }, s x = ⋂ (x) (hx : p x), s ⟨x, hx⟩ :=
  iInf_subtype
#align set.Inter_subtype Set.iInter_subtype

theorem biInter_empty (u : α → Set β) : ⋂ x ∈ (∅ : Set α), u x = univ :=
  iInf_emptyset
#align set.bInter_empty Set.biInter_empty

theorem biInter_univ (u : α → Set β) : ⋂ x ∈ @univ α, u x = ⋂ x, u x :=
  iInf_univ
#align set.bInter_univ Set.biInter_univ

@[simp]
theorem biUnion_self (s : Set α) : ⋃ x ∈ s, s = s :=
  Subset.antisymm (iUnion₂_subset fun _ _ => Subset.refl s) fun _ hx => mem_biUnion hx hx
#align set.bUnion_self Set.biUnion_self

@[simp]
theorem iUnion_nonempty_self (s : Set α) : ⋃ _ : s.Nonempty, s = s := by
  rw [iUnion_nonempty_index, biUnion_self]
#align set.Union_nonempty_self Set.iUnion_nonempty_self

theorem biInter_singleton (a : α) (s : α → Set β) : ⋂ x ∈ ({a} : Set α), s x = s a :=
  iInf_singleton
#align set.bInter_singleton Set.biInter_singleton

theorem biInter_union (s t : Set α) (u : α → Set β) :
    ⋂ x ∈ s ∪ t, u x = (⋂ x ∈ s, u x) ∩ ⋂ x ∈ t, u x :=
  iInf_union
#align set.bInter_union Set.biInter_union

theorem biInter_insert (a : α) (s : Set α) (t : α → Set β) :
    ⋂ x ∈ insert a s, t x = t a ∩ ⋂ x ∈ s, t x := by simp
#align set.bInter_insert Set.biInter_insert

theorem biInter_pair (a b : α) (s : α → Set β) : ⋂ x ∈ ({a, b} : Set α), s x = s a ∩ s b := by
  rw [biInter_insert, biInter_singleton]
#align set.bInter_pair Set.biInter_pair

theorem biInter_inter {ι α : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι → Set α) (t : Set α) :
    ⋂ i ∈ s, f i ∩ t = (⋂ i ∈ s, f i) ∩ t := by
  haveI : Nonempty s := hs.to_subtype
  simp [biInter_eq_iInter, ← iInter_inter]
#align set.bInter_inter Set.biInter_inter

theorem inter_biInter {ι α : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι → Set α) (t : Set α) :
    ⋂ i ∈ s, t ∩ f i = t ∩ ⋂ i ∈ s, f i := by
  rw [inter_comm, ← biInter_inter hs]
  simp [inter_comm]
#align set.inter_bInter Set.inter_biInter

theorem biUnion_empty (s : α → Set β) : ⋃ x ∈ (∅ : Set α), s x = ∅ :=
  iSup_emptyset
#align set.bUnion_empty Set.biUnion_empty

theorem biUnion_univ (s : α → Set β) : ⋃ x ∈ @univ α, s x = ⋃ x, s x :=
  iSup_univ
#align set.bUnion_univ Set.biUnion_univ

theorem biUnion_singleton (a : α) (s : α → Set β) : ⋃ x ∈ ({a} : Set α), s x = s a :=
  iSup_singleton
#align set.bUnion_singleton Set.biUnion_singleton

@[simp]
theorem biUnion_of_singleton (s : Set α) : ⋃ x ∈ s, {x} = s :=
  ext <| by simp
#align set.bUnion_of_singleton Set.biUnion_of_singleton

theorem biUnion_union (s t : Set α) (u : α → Set β) :
    ⋃ x ∈ s ∪ t, u x = (⋃ x ∈ s, u x) ∪ ⋃ x ∈ t, u x :=
  iSup_union
#align set.bUnion_union Set.biUnion_union

@[simp]
theorem iUnion_coe_set {α β : Type*} (s : Set α) (f : s → Set β) :
    ⋃ i, f i = ⋃ i ∈ s, f ⟨i, ‹i ∈ s›⟩ :=
  iUnion_subtype _ _
#align set.Union_coe_set Set.iUnion_coe_set

@[simp]
theorem iInter_coe_set {α β : Type*} (s : Set α) (f : s → Set β) :
    ⋂ i, f i = ⋂ i ∈ s, f ⟨i, ‹i ∈ s›⟩ :=
  iInter_subtype _ _
#align set.Inter_coe_set Set.iInter_coe_set

theorem biUnion_insert (a : α) (s : Set α) (t : α → Set β) :
    ⋃ x ∈ insert a s, t x = t a ∪ ⋃ x ∈ s, t x := by simp
#align set.bUnion_insert Set.biUnion_insert

theorem biUnion_pair (a b : α) (s : α → Set β) : ⋃ x ∈ ({a, b} : Set α), s x = s a ∪ s b := by
  simp
#align set.bUnion_pair Set.biUnion_pair

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem inter_iUnion₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s ∩ ⋃ (i) (j), t i j) = ⋃ (i) (j), s ∩ t i j := by simp only [inter_iUnion]
#align set.inter_Union₂ Set.inter_iUnion₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iUnion₂_inter (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋃ (i) (j), s i j) ∩ t = ⋃ (i) (j), s i j ∩ t := by simp_rw [iUnion_inter]
#align set.Union₂_inter Set.iUnion₂_inter

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem union_iInter₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s ∪ ⋂ (i) (j), t i j) = ⋂ (i) (j), s ∪ t i j := by simp_rw [union_iInter]
#align set.union_Inter₂ Set.union_iInter₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iInter₂_union (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) ∪ t = ⋂ (i) (j), s i j ∪ t := by simp_rw [iInter_union]
#align set.Inter₂_union Set.iInter₂_union

theorem mem_sUnion_of_mem {x : α} {t : Set α} {S : Set (Set α)} (hx : x ∈ t) (ht : t ∈ S) :
    x ∈ ⋃₀S :=
  ⟨t, ht, hx⟩
#align set.mem_sUnion_of_mem Set.mem_sUnion_of_mem

-- is this theorem really necessary?
theorem not_mem_of_not_mem_sUnion {x : α} {t : Set α} {S : Set (Set α)} (hx : x ∉ ⋃₀S)
    (ht : t ∈ S) : x ∉ t := fun h => hx ⟨t, ht, h⟩
#align set.not_mem_of_not_mem_sUnion Set.not_mem_of_not_mem_sUnion

theorem sInter_subset_of_mem {S : Set (Set α)} {t : Set α} (tS : t ∈ S) : ⋂₀ S ⊆ t :=
  sInf_le tS
#align set.sInter_subset_of_mem Set.sInter_subset_of_mem

theorem subset_sUnion_of_mem {S : Set (Set α)} {t : Set α} (tS : t ∈ S) : t ⊆ ⋃₀S :=
  le_sSup tS
#align set.subset_sUnion_of_mem Set.subset_sUnion_of_mem

theorem subset_sUnion_of_subset {s : Set α} (t : Set (Set α)) (u : Set α) (h₁ : s ⊆ u)
    (h₂ : u ∈ t) : s ⊆ ⋃₀t :=
  Subset.trans h₁ (subset_sUnion_of_mem h₂)
#align set.subset_sUnion_of_subset Set.subset_sUnion_of_subset

theorem sUnion_subset {S : Set (Set α)} {t : Set α} (h : ∀ t' ∈ S, t' ⊆ t) : ⋃₀S ⊆ t :=
  sSup_le h
#align set.sUnion_subset Set.sUnion_subset

@[simp]
theorem sUnion_subset_iff {s : Set (Set α)} {t : Set α} : ⋃₀s ⊆ t ↔ ∀ t' ∈ s, t' ⊆ t :=
  sSup_le_iff
#align set.sUnion_subset_iff Set.sUnion_subset_iff

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
#align set.subset_sInter Set.subset_sInter

@[simp]
theorem subset_sInter_iff {S : Set (Set α)} {t : Set α} : t ⊆ ⋂₀ S ↔ ∀ t' ∈ S, t ⊆ t' :=
  le_sInf_iff
#align set.subset_sInter_iff Set.subset_sInter_iff

@[gcongr]
theorem sUnion_subset_sUnion {S T : Set (Set α)} (h : S ⊆ T) : ⋃₀S ⊆ ⋃₀T :=
  sUnion_subset fun _ hs => subset_sUnion_of_mem (h hs)
#align set.sUnion_subset_sUnion Set.sUnion_subset_sUnion

@[gcongr]
theorem sInter_subset_sInter {S T : Set (Set α)} (h : S ⊆ T) : ⋂₀ T ⊆ ⋂₀ S :=
  subset_sInter fun _ hs => sInter_subset_of_mem (h hs)
#align set.sInter_subset_sInter Set.sInter_subset_sInter

@[simp]
theorem sUnion_empty : ⋃₀∅ = (∅ : Set α) :=
  sSup_empty
#align set.sUnion_empty Set.sUnion_empty

@[simp]
theorem sInter_empty : ⋂₀ ∅ = (univ : Set α) :=
  sInf_empty
#align set.sInter_empty Set.sInter_empty

@[simp]
theorem sUnion_singleton (s : Set α) : ⋃₀{s} = s :=
  sSup_singleton
#align set.sUnion_singleton Set.sUnion_singleton

@[simp]
theorem sInter_singleton (s : Set α) : ⋂₀ {s} = s :=
  sInf_singleton
#align set.sInter_singleton Set.sInter_singleton

@[simp]
theorem sUnion_eq_empty {S : Set (Set α)} : ⋃₀S = ∅ ↔ ∀ s ∈ S, s = ∅ :=
  sSup_eq_bot
#align set.sUnion_eq_empty Set.sUnion_eq_empty

@[simp]
theorem sInter_eq_univ {S : Set (Set α)} : ⋂₀ S = univ ↔ ∀ s ∈ S, s = univ :=
  sInf_eq_top
#align set.sInter_eq_univ Set.sInter_eq_univ

theorem subset_powerset_iff {s : Set (Set α)} {t : Set α} : s ⊆ 𝒫 t ↔ ⋃₀ s ⊆ t :=
  sUnion_subset_iff.symm

/-- `⋃₀` and `𝒫` form a Galois connection. -/
theorem sUnion_powerset_gc :
    GaloisConnection (⋃₀ · : Set (Set α) → Set α) (𝒫 · : Set α → Set (Set α)) :=
  gc_sSup_Iic

/-- `⋃₀` and `𝒫` form a Galois insertion. -/
def sUnion_powerset_gi :
    GaloisInsertion (⋃₀ · : Set (Set α) → Set α) (𝒫 · : Set α → Set (Set α)) :=
  gi_sSup_Iic

/-- If all sets in a collection are either `∅` or `Set.univ`, then so is their union. -/
theorem sUnion_mem_empty_univ {S : Set (Set α)} (h : S ⊆ {∅, univ}) :
    ⋃₀ S ∈ ({∅, univ} : Set (Set α)) := by
  simp only [mem_insert_iff, mem_singleton_iff, or_iff_not_imp_left, sUnion_eq_empty, not_forall]
  rintro ⟨s, hs, hne⟩
  obtain rfl : s = univ := (h hs).resolve_left hne
  exact univ_subset_iff.1 <| subset_sUnion_of_mem hs

@[simp]
theorem nonempty_sUnion {S : Set (Set α)} : (⋃₀S).Nonempty ↔ ∃ s ∈ S, Set.Nonempty s := by
  simp [nonempty_iff_ne_empty]
#align set.nonempty_sUnion Set.nonempty_sUnion

theorem Nonempty.of_sUnion {s : Set (Set α)} (h : (⋃₀s).Nonempty) : s.Nonempty :=
  let ⟨s, hs, _⟩ := nonempty_sUnion.1 h
  ⟨s, hs⟩
#align set.nonempty.of_sUnion Set.Nonempty.of_sUnion

theorem Nonempty.of_sUnion_eq_univ [Nonempty α] {s : Set (Set α)} (h : ⋃₀s = univ) : s.Nonempty :=
  Nonempty.of_sUnion <| h.symm ▸ univ_nonempty
#align set.nonempty.of_sUnion_eq_univ Set.Nonempty.of_sUnion_eq_univ

theorem sUnion_union (S T : Set (Set α)) : ⋃₀(S ∪ T) = ⋃₀S ∪ ⋃₀T :=
  sSup_union
#align set.sUnion_union Set.sUnion_union

theorem sInter_union (S T : Set (Set α)) : ⋂₀ (S ∪ T) = ⋂₀ S ∩ ⋂₀ T :=
  sInf_union
#align set.sInter_union Set.sInter_union

@[simp]
theorem sUnion_insert (s : Set α) (T : Set (Set α)) : ⋃₀insert s T = s ∪ ⋃₀T :=
  sSup_insert
#align set.sUnion_insert Set.sUnion_insert

@[simp]
theorem sInter_insert (s : Set α) (T : Set (Set α)) : ⋂₀ insert s T = s ∩ ⋂₀ T :=
  sInf_insert
#align set.sInter_insert Set.sInter_insert

@[simp]
theorem sUnion_diff_singleton_empty (s : Set (Set α)) : ⋃₀(s \ {∅}) = ⋃₀s :=
  sSup_diff_singleton_bot s
#align set.sUnion_diff_singleton_empty Set.sUnion_diff_singleton_empty

@[simp]
theorem sInter_diff_singleton_univ (s : Set (Set α)) : ⋂₀ (s \ {univ}) = ⋂₀ s :=
  sInf_diff_singleton_top s
#align set.sInter_diff_singleton_univ Set.sInter_diff_singleton_univ

theorem sUnion_pair (s t : Set α) : ⋃₀{s, t} = s ∪ t :=
  sSup_pair
#align set.sUnion_pair Set.sUnion_pair

theorem sInter_pair (s t : Set α) : ⋂₀ {s, t} = s ∩ t :=
  sInf_pair
#align set.sInter_pair Set.sInter_pair

@[simp]
theorem sUnion_image (f : α → Set β) (s : Set α) : ⋃₀(f '' s) = ⋃ x ∈ s, f x :=
  sSup_image
#align set.sUnion_image Set.sUnion_image

@[simp]
theorem sInter_image (f : α → Set β) (s : Set α) : ⋂₀ (f '' s) = ⋂ x ∈ s, f x :=
  sInf_image
#align set.sInter_image Set.sInter_image

@[simp]
theorem sUnion_range (f : ι → Set β) : ⋃₀range f = ⋃ x, f x :=
  rfl
#align set.sUnion_range Set.sUnion_range

@[simp]
theorem sInter_range (f : ι → Set β) : ⋂₀ range f = ⋂ x, f x :=
  rfl
#align set.sInter_range Set.sInter_range

theorem iUnion_eq_univ_iff {f : ι → Set α} : ⋃ i, f i = univ ↔ ∀ x, ∃ i, x ∈ f i := by
  simp only [eq_univ_iff_forall, mem_iUnion]
#align set.Union_eq_univ_iff Set.iUnion_eq_univ_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iUnion₂_eq_univ_iff {s : ∀ i, κ i → Set α} :
    ⋃ (i) (j), s i j = univ ↔ ∀ a, ∃ i j, a ∈ s i j := by
  simp only [iUnion_eq_univ_iff, mem_iUnion]
#align set.Union₂_eq_univ_iff Set.iUnion₂_eq_univ_iff

theorem sUnion_eq_univ_iff {c : Set (Set α)} : ⋃₀c = univ ↔ ∀ a, ∃ b ∈ c, a ∈ b := by
  simp only [eq_univ_iff_forall, mem_sUnion]
#align set.sUnion_eq_univ_iff Set.sUnion_eq_univ_iff

-- classical
theorem iInter_eq_empty_iff {f : ι → Set α} : ⋂ i, f i = ∅ ↔ ∀ x, ∃ i, x ∉ f i := by
  simp [Set.eq_empty_iff_forall_not_mem]
#align set.Inter_eq_empty_iff Set.iInter_eq_empty_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
-- classical
theorem iInter₂_eq_empty_iff {s : ∀ i, κ i → Set α} :
    ⋂ (i) (j), s i j = ∅ ↔ ∀ a, ∃ i j, a ∉ s i j := by
  simp only [eq_empty_iff_forall_not_mem, mem_iInter, not_forall]
#align set.Inter₂_eq_empty_iff Set.iInter₂_eq_empty_iff

-- classical
theorem sInter_eq_empty_iff {c : Set (Set α)} : ⋂₀ c = ∅ ↔ ∀ a, ∃ b ∈ c, a ∉ b := by
  simp [Set.eq_empty_iff_forall_not_mem]
#align set.sInter_eq_empty_iff Set.sInter_eq_empty_iff

-- classical
@[simp]
theorem nonempty_iInter {f : ι → Set α} : (⋂ i, f i).Nonempty ↔ ∃ x, ∀ i, x ∈ f i := by
  simp [nonempty_iff_ne_empty, iInter_eq_empty_iff]
#align set.nonempty_Inter Set.nonempty_iInter

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
-- classical
-- Porting note (#10618): removing `simp`. `simp` can prove it
theorem nonempty_iInter₂ {s : ∀ i, κ i → Set α} :
    (⋂ (i) (j), s i j).Nonempty ↔ ∃ a, ∀ i j, a ∈ s i j := by
  simp
#align set.nonempty_Inter₂ Set.nonempty_iInter₂

-- classical
@[simp]
theorem nonempty_sInter {c : Set (Set α)} : (⋂₀ c).Nonempty ↔ ∃ a, ∀ b ∈ c, a ∈ b := by
  simp [nonempty_iff_ne_empty, sInter_eq_empty_iff]
#align set.nonempty_sInter Set.nonempty_sInter

-- classical
theorem compl_sUnion (S : Set (Set α)) : (⋃₀S)ᶜ = ⋂₀ (compl '' S) :=
  ext fun x => by simp
#align set.compl_sUnion Set.compl_sUnion

-- classical
theorem sUnion_eq_compl_sInter_compl (S : Set (Set α)) : ⋃₀S = (⋂₀ (compl '' S))ᶜ := by
  rw [← compl_compl (⋃₀S), compl_sUnion]
#align set.sUnion_eq_compl_sInter_compl Set.sUnion_eq_compl_sInter_compl

-- classical
theorem compl_sInter (S : Set (Set α)) : (⋂₀ S)ᶜ = ⋃₀(compl '' S) := by
  rw [sUnion_eq_compl_sInter_compl, compl_compl_image]
#align set.compl_sInter Set.compl_sInter

-- classical
theorem sInter_eq_compl_sUnion_compl (S : Set (Set α)) : ⋂₀ S = (⋃₀(compl '' S))ᶜ := by
  rw [← compl_compl (⋂₀ S), compl_sInter]
#align set.sInter_eq_compl_sUnion_compl Set.sInter_eq_compl_sUnion_compl

theorem inter_empty_of_inter_sUnion_empty {s t : Set α} {S : Set (Set α)} (hs : t ∈ S)
    (h : s ∩ ⋃₀S = ∅) : s ∩ t = ∅ :=
  eq_empty_of_subset_empty <| by
    rw [← h]; exact inter_subset_inter_right _ (subset_sUnion_of_mem hs)
#align set.inter_empty_of_inter_sUnion_empty Set.inter_empty_of_inter_sUnion_empty

theorem range_sigma_eq_iUnion_range {γ : α → Type*} (f : Sigma γ → β) :
    range f = ⋃ a, range fun b => f ⟨a, b⟩ :=
  Set.ext <| by simp
#align set.range_sigma_eq_Union_range Set.range_sigma_eq_iUnion_range

theorem iUnion_eq_range_sigma (s : α → Set β) : ⋃ i, s i = range fun a : Σi, s i => a.2 := by
  simp [Set.ext_iff]
#align set.Union_eq_range_sigma Set.iUnion_eq_range_sigma

theorem iUnion_eq_range_psigma (s : ι → Set β) : ⋃ i, s i = range fun a : Σ'i, s i => a.2 := by
  simp [Set.ext_iff]
#align set.Union_eq_range_psigma Set.iUnion_eq_range_psigma

theorem iUnion_image_preimage_sigma_mk_eq_self {ι : Type*} {σ : ι → Type*} (s : Set (Sigma σ)) :
    ⋃ i, Sigma.mk i '' (Sigma.mk i ⁻¹' s) = s := by
  ext x
  simp only [mem_iUnion, mem_image, mem_preimage]
  constructor
  · rintro ⟨i, a, h, rfl⟩
    exact h
  · intro h
    cases' x with i a
    exact ⟨i, a, h, rfl⟩
#align set.Union_image_preimage_sigma_mk_eq_self Set.iUnion_image_preimage_sigma_mk_eq_self

theorem Sigma.univ (X : α → Type*) : (Set.univ : Set (Σa, X a)) = ⋃ a, range (Sigma.mk a) :=
  Set.ext fun x =>
    iff_of_true trivial ⟨range (Sigma.mk x.1), Set.mem_range_self _, x.2, Sigma.eta x⟩
#align set.sigma.univ Set.Sigma.univ

alias sUnion_mono := sUnion_subset_sUnion
#align set.sUnion_mono Set.sUnion_mono

theorem iUnion_subset_iUnion_const {s : Set α} (h : ι → ι₂) : ⋃ _ : ι, s ⊆ ⋃ _ : ι₂, s :=
  iSup_const_mono (α := Set α) h
#align set.Union_subset_Union_const Set.iUnion_subset_iUnion_const

@[simp]
theorem iUnion_singleton_eq_range {α β : Type*} (f : α → β) : ⋃ x : α, {f x} = range f := by
  ext x
  simp [@eq_comm _ x]
#align set.Union_singleton_eq_range Set.iUnion_singleton_eq_range

theorem iUnion_of_singleton (α : Type*) : (⋃ x, {x} : Set α) = univ := by simp [Set.ext_iff]
#align set.Union_of_singleton Set.iUnion_of_singleton

theorem iUnion_of_singleton_coe (s : Set α) : ⋃ i : s, ({(i : α)} : Set α) = s := by simp
#align set.Union_of_singleton_coe Set.iUnion_of_singleton_coe

theorem sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀s = ⋃ (i : Set α) (_ : i ∈ s), i := by
  rw [← sUnion_image, image_id']
#align set.sUnion_eq_bUnion Set.sUnion_eq_biUnion

theorem sInter_eq_biInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i : Set α) (_ : i ∈ s), i := by
  rw [← sInter_image, image_id']
#align set.sInter_eq_bInter Set.sInter_eq_biInter

theorem sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀s = ⋃ i : s, i := by
  simp only [← sUnion_range, Subtype.range_coe]
#align set.sUnion_eq_Union Set.sUnion_eq_iUnion

theorem sInter_eq_iInter {s : Set (Set α)} : ⋂₀ s = ⋂ i : s, i := by
  simp only [← sInter_range, Subtype.range_coe]
#align set.sInter_eq_Inter Set.sInter_eq_iInter

@[simp]
theorem iUnion_of_empty [IsEmpty ι] (s : ι → Set α) : ⋃ i, s i = ∅ :=
  iSup_of_empty _
#align set.Union_of_empty Set.iUnion_of_empty

@[simp]
theorem iInter_of_empty [IsEmpty ι] (s : ι → Set α) : ⋂ i, s i = univ :=
  iInf_of_empty _
#align set.Inter_of_empty Set.iInter_of_empty

theorem union_eq_iUnion {s₁ s₂ : Set α} : s₁ ∪ s₂ = ⋃ b : Bool, cond b s₁ s₂ :=
  sup_eq_iSup s₁ s₂
#align set.union_eq_Union Set.union_eq_iUnion

theorem inter_eq_iInter {s₁ s₂ : Set α} : s₁ ∩ s₂ = ⋂ b : Bool, cond b s₁ s₂ :=
  inf_eq_iInf s₁ s₂
#align set.inter_eq_Inter Set.inter_eq_iInter

theorem sInter_union_sInter {S T : Set (Set α)} :
    ⋂₀ S ∪ ⋂₀ T = ⋂ p ∈ S ×ˢ T, (p : Set α × Set α).1 ∪ p.2 :=
  sInf_sup_sInf
#align set.sInter_union_sInter Set.sInter_union_sInter

theorem sUnion_inter_sUnion {s t : Set (Set α)} :
    ⋃₀s ∩ ⋃₀t = ⋃ p ∈ s ×ˢ t, (p : Set α × Set α).1 ∩ p.2 :=
  sSup_inf_sSup
#align set.sUnion_inter_sUnion Set.sUnion_inter_sUnion

theorem biUnion_iUnion (s : ι → Set α) (t : α → Set β) :
    ⋃ x ∈ ⋃ i, s i, t x = ⋃ (i) (x ∈ s i), t x := by simp [@iUnion_comm _ ι]
#align set.bUnion_Union Set.biUnion_iUnion

theorem biInter_iUnion (s : ι → Set α) (t : α → Set β) :
    ⋂ x ∈ ⋃ i, s i, t x = ⋂ (i) (x ∈ s i), t x := by simp [@iInter_comm _ ι]
#align set.bInter_Union Set.biInter_iUnion

theorem sUnion_iUnion (s : ι → Set (Set α)) : ⋃₀⋃ i, s i = ⋃ i, ⋃₀s i := by
  simp only [sUnion_eq_biUnion, biUnion_iUnion]
#align set.sUnion_Union Set.sUnion_iUnion

theorem sInter_iUnion (s : ι → Set (Set α)) : ⋂₀ ⋃ i, s i = ⋂ i, ⋂₀ s i := by
  simp only [sInter_eq_biInter, biInter_iUnion]
#align set.sInter_Union Set.sInter_iUnion

theorem iUnion_range_eq_sUnion {α β : Type*} (C : Set (Set α)) {f : ∀ s : C, β → (s : Type _)}
    (hf : ∀ s : C, Surjective (f s)) : ⋃ y : β, range (fun s : C => (f s y).val) = ⋃₀C := by
  ext x; constructor
  · rintro ⟨s, ⟨y, rfl⟩, ⟨s, hs⟩, rfl⟩
    refine ⟨_, hs, ?_⟩
    exact (f ⟨s, hs⟩ y).2
  · rintro ⟨s, hs, hx⟩
    cases' hf ⟨s, hs⟩ ⟨x, hx⟩ with y hy
    refine ⟨_, ⟨y, rfl⟩, ⟨s, hs⟩, ?_⟩
    exact congr_arg Subtype.val hy
#align set.Union_range_eq_sUnion Set.iUnion_range_eq_sUnion

theorem iUnion_range_eq_iUnion (C : ι → Set α) {f : ∀ x : ι, β → C x}
    (hf : ∀ x : ι, Surjective (f x)) : ⋃ y : β, range (fun x : ι => (f x y).val) = ⋃ x, C x := by
  ext x; rw [mem_iUnion, mem_iUnion]; constructor
  · rintro ⟨y, i, rfl⟩
    exact ⟨i, (f i y).2⟩
  · rintro ⟨i, hx⟩
    cases' hf i ⟨x, hx⟩ with y hy
    exact ⟨y, i, congr_arg Subtype.val hy⟩
#align set.Union_range_eq_Union Set.iUnion_range_eq_iUnion

theorem union_distrib_iInter_left (s : ι → Set α) (t : Set α) : (t ∪ ⋂ i, s i) = ⋂ i, t ∪ s i :=
  sup_iInf_eq _ _
#align set.union_distrib_Inter_left Set.union_distrib_iInter_left

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem union_distrib_iInter₂_left (s : Set α) (t : ∀ i, κ i → Set α) :
    (s ∪ ⋂ (i) (j), t i j) = ⋂ (i) (j), s ∪ t i j := by simp_rw [union_distrib_iInter_left]
#align set.union_distrib_Inter₂_left Set.union_distrib_iInter₂_left

theorem union_distrib_iInter_right (s : ι → Set α) (t : Set α) : (⋂ i, s i) ∪ t = ⋂ i, s i ∪ t :=
  iInf_sup_eq _ _
#align set.union_distrib_Inter_right Set.union_distrib_iInter_right

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem union_distrib_iInter₂_right (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) ∪ t = ⋂ (i) (j), s i j ∪ t := by simp_rw [union_distrib_iInter_right]
#align set.union_distrib_Inter₂_right Set.union_distrib_iInter₂_right

section Function

/-! ### Lemmas about `Set.MapsTo`

Porting note: some lemmas in this section were upgraded from implications to `iff`s.
-/

@[simp]
theorem mapsTo_sUnion {S : Set (Set α)} {t : Set β} {f : α → β} :
    MapsTo f (⋃₀ S) t ↔ ∀ s ∈ S, MapsTo f s t :=
  sUnion_subset_iff
#align set.maps_to_sUnion Set.mapsTo_sUnion

@[simp]
theorem mapsTo_iUnion {s : ι → Set α} {t : Set β} {f : α → β} :
    MapsTo f (⋃ i, s i) t ↔ ∀ i, MapsTo f (s i) t :=
  iUnion_subset_iff
#align set.maps_to_Union Set.mapsTo_iUnion

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem mapsTo_iUnion₂ {s : ∀ i, κ i → Set α} {t : Set β} {f : α → β} :
    MapsTo f (⋃ (i) (j), s i j) t ↔ ∀ i j, MapsTo f (s i j) t :=
  iUnion₂_subset_iff
#align set.maps_to_Union₂ Set.mapsTo_iUnion₂

theorem mapsTo_iUnion_iUnion {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, MapsTo f (s i) (t i)) : MapsTo f (⋃ i, s i) (⋃ i, t i) :=
  mapsTo_iUnion.2 fun i ↦ (H i).mono_right (subset_iUnion t i)
#align set.maps_to_Union_Union Set.mapsTo_iUnion_iUnion

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem mapsTo_iUnion₂_iUnion₂ {s : ∀ i, κ i → Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, MapsTo f (s i j) (t i j)) : MapsTo f (⋃ (i) (j), s i j) (⋃ (i) (j), t i j) :=
  mapsTo_iUnion_iUnion fun i => mapsTo_iUnion_iUnion (H i)
#align set.maps_to_Union₂_Union₂ Set.mapsTo_iUnion₂_iUnion₂

@[simp]
theorem mapsTo_sInter {s : Set α} {T : Set (Set β)} {f : α → β} :
    MapsTo f s (⋂₀ T) ↔ ∀ t ∈ T, MapsTo f s t :=
  forall₂_swap
#align set.maps_to_sInter Set.mapsTo_sInter

@[simp]
theorem mapsTo_iInter {s : Set α} {t : ι → Set β} {f : α → β} :
    MapsTo f s (⋂ i, t i) ↔ ∀ i, MapsTo f s (t i) :=
  mapsTo_sInter.trans forall_mem_range
#align set.maps_to_Inter Set.mapsTo_iInter

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem mapsTo_iInter₂ {s : Set α} {t : ∀ i, κ i → Set β} {f : α → β} :
    MapsTo f s (⋂ (i) (j), t i j) ↔ ∀ i j, MapsTo f s (t i j) := by
  simp only [mapsTo_iInter]
#align set.maps_to_Inter₂ Set.mapsTo_iInter₂

theorem mapsTo_iInter_iInter {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, MapsTo f (s i) (t i)) : MapsTo f (⋂ i, s i) (⋂ i, t i) :=
  mapsTo_iInter.2 fun i => (H i).mono_left (iInter_subset s i)
#align set.maps_to_Inter_Inter Set.mapsTo_iInter_iInter

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem mapsTo_iInter₂_iInter₂ {s : ∀ i, κ i → Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, MapsTo f (s i j) (t i j)) : MapsTo f (⋂ (i) (j), s i j) (⋂ (i) (j), t i j) :=
  mapsTo_iInter_iInter fun i => mapsTo_iInter_iInter (H i)
#align set.maps_to_Inter₂_Inter₂ Set.mapsTo_iInter₂_iInter₂

theorem image_iInter_subset (s : ι → Set α) (f : α → β) : (f '' ⋂ i, s i) ⊆ ⋂ i, f '' s i :=
  (mapsTo_iInter_iInter fun i => mapsTo_image f (s i)).image_subset
#align set.image_Inter_subset Set.image_iInter_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image_iInter₂_subset (s : ∀ i, κ i → Set α) (f : α → β) :
    (f '' ⋂ (i) (j), s i j) ⊆ ⋂ (i) (j), f '' s i j :=
  (mapsTo_iInter₂_iInter₂ fun i hi => mapsTo_image f (s i hi)).image_subset
#align set.image_Inter₂_subset Set.image_iInter₂_subset

theorem image_sInter_subset (S : Set (Set α)) (f : α → β) : f '' ⋂₀ S ⊆ ⋂ s ∈ S, f '' s := by
  rw [sInter_eq_biInter]
  apply image_iInter₂_subset
#align set.image_sInter_subset Set.image_sInter_subset

/-! ### `restrictPreimage` -/


section

open Function

variable (s : Set β) {f : α → β} {U : ι → Set β} (hU : iUnion U = univ)

theorem injective_iff_injective_of_iUnion_eq_univ :
    Injective f ↔ ∀ i, Injective ((U i).restrictPreimage f) := by
  refine ⟨fun H i => (U i).restrictPreimage_injective H, fun H x y e => ?_⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      (show f x ∈ Set.iUnion U by rw [hU]; trivial)
  injection @H i ⟨x, hi⟩ ⟨y, show f y ∈ U i from e ▸ hi⟩ (Subtype.ext e)
#align set.injective_iff_injective_of_Union_eq_univ Set.injective_iff_injective_of_iUnion_eq_univ

theorem surjective_iff_surjective_of_iUnion_eq_univ :
    Surjective f ↔ ∀ i, Surjective ((U i).restrictPreimage f) := by
  refine ⟨fun H i => (U i).restrictPreimage_surjective H, fun H x => ?_⟩
  obtain ⟨i, hi⟩ :=
    Set.mem_iUnion.mp
      (show x ∈ Set.iUnion U by rw [hU]; trivial)
  exact ⟨_, congr_arg Subtype.val (H i ⟨x, hi⟩).choose_spec⟩
#align set.surjective_iff_surjective_of_Union_eq_univ Set.surjective_iff_surjective_of_iUnion_eq_univ

theorem bijective_iff_bijective_of_iUnion_eq_univ :
    Bijective f ↔ ∀ i, Bijective ((U i).restrictPreimage f) := by
  rw [Bijective, injective_iff_injective_of_iUnion_eq_univ hU,
    surjective_iff_surjective_of_iUnion_eq_univ hU]
  simp [Bijective, forall_and]
#align set.bijective_iff_bijective_of_Union_eq_univ Set.bijective_iff_bijective_of_iUnion_eq_univ

end

/-! ### `InjOn` -/


theorem InjOn.image_iInter_eq [Nonempty ι] {s : ι → Set α} {f : α → β} (h : InjOn f (⋃ i, s i)) :
    (f '' ⋂ i, s i) = ⋂ i, f '' s i := by
  inhabit ι
  refine Subset.antisymm (image_iInter_subset s f) fun y hy => ?_
  simp only [mem_iInter, mem_image] at hy
  choose x hx hy using hy
  refine ⟨x default, mem_iInter.2 fun i => ?_, hy _⟩
  suffices x default = x i by
    rw [this]
    apply hx
  replace hx : ∀ i, x i ∈ ⋃ j, s j := fun i => (subset_iUnion _ _) (hx i)
  apply h (hx _) (hx _)
  simp only [hy]
#align set.inj_on.image_Inter_eq Set.InjOn.image_iInter_eq

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i hi) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i hi) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i hi) -/
theorem InjOn.image_biInter_eq {p : ι → Prop} {s : ∀ i, p i → Set α} (hp : ∃ i, p i)
    {f : α → β} (h : InjOn f (⋃ (i) (hi), s i hi)) :
    (f '' ⋂ (i) (hi), s i hi) = ⋂ (i) (hi), f '' s i hi := by
  simp only [iInter, iInf_subtype']
  haveI : Nonempty { i // p i } := nonempty_subtype.2 hp
  apply InjOn.image_iInter_eq
  simpa only [iUnion, iSup_subtype'] using h
#align set.inj_on.image_bInter_eq Set.InjOn.image_biInter_eq

theorem image_iInter {f : α → β} (hf : Bijective f) (s : ι → Set α) :
    (f '' ⋂ i, s i) = ⋂ i, f '' s i := by
  cases isEmpty_or_nonempty ι
  · simp_rw [iInter_of_empty, image_univ_of_surjective hf.surjective]
  · exact hf.injective.injOn.image_iInter_eq
#align set.image_Inter Set.image_iInter

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image_iInter₂ {f : α → β} (hf : Bijective f) (s : ∀ i, κ i → Set α) :
    (f '' ⋂ (i) (j), s i j) = ⋂ (i) (j), f '' s i j := by simp_rw [image_iInter hf]
#align set.image_Inter₂ Set.image_iInter₂

theorem inj_on_iUnion_of_directed {s : ι → Set α} (hs : Directed (· ⊆ ·) s) {f : α → β}
    (hf : ∀ i, InjOn f (s i)) : InjOn f (⋃ i, s i) := by
  intro x hx y hy hxy
  rcases mem_iUnion.1 hx with ⟨i, hx⟩
  rcases mem_iUnion.1 hy with ⟨j, hy⟩
  rcases hs i j with ⟨k, hi, hj⟩
  exact hf k (hi hx) (hj hy) hxy
#align set.inj_on_Union_of_directed Set.inj_on_iUnion_of_directed

/-! ### `SurjOn` -/


theorem surjOn_sUnion {s : Set α} {T : Set (Set β)} {f : α → β} (H : ∀ t ∈ T, SurjOn f s t) :
    SurjOn f s (⋃₀T) := fun _ ⟨t, ht, hx⟩ => H t ht hx
#align set.surj_on_sUnion Set.surjOn_sUnion

theorem surjOn_iUnion {s : Set α} {t : ι → Set β} {f : α → β} (H : ∀ i, SurjOn f s (t i)) :
    SurjOn f s (⋃ i, t i) :=
  surjOn_sUnion <| forall_mem_range.2 H
#align set.surj_on_Union Set.surjOn_iUnion

theorem surjOn_iUnion_iUnion {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, SurjOn f (s i) (t i)) : SurjOn f (⋃ i, s i) (⋃ i, t i) :=
  surjOn_iUnion fun i => (H i).mono (subset_iUnion _ _) (Subset.refl _)
#align set.surj_on_Union_Union Set.surjOn_iUnion_iUnion

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem surjOn_iUnion₂ {s : Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, SurjOn f s (t i j)) : SurjOn f s (⋃ (i) (j), t i j) :=
  surjOn_iUnion fun i => surjOn_iUnion (H i)
#align set.surj_on_Union₂ Set.surjOn_iUnion₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem surjOn_iUnion₂_iUnion₂ {s : ∀ i, κ i → Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, SurjOn f (s i j) (t i j)) : SurjOn f (⋃ (i) (j), s i j) (⋃ (i) (j), t i j) :=
  surjOn_iUnion_iUnion fun i => surjOn_iUnion_iUnion (H i)
#align set.surj_on_Union₂_Union₂ Set.surjOn_iUnion₂_iUnion₂

theorem surjOn_iInter [Nonempty ι] {s : ι → Set α} {t : Set β} {f : α → β}
    (H : ∀ i, SurjOn f (s i) t) (Hinj : InjOn f (⋃ i, s i)) : SurjOn f (⋂ i, s i) t := by
  intro y hy
  rw [Hinj.image_iInter_eq, mem_iInter]
  exact fun i => H i hy
#align set.surj_on_Inter Set.surjOn_iInter

theorem surjOn_iInter_iInter [Nonempty ι] {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, SurjOn f (s i) (t i)) (Hinj : InjOn f (⋃ i, s i)) : SurjOn f (⋂ i, s i) (⋂ i, t i) :=
  surjOn_iInter (fun i => (H i).mono (Subset.refl _) (iInter_subset _ _)) Hinj
#align set.surj_on_Inter_Inter Set.surjOn_iInter_iInter

/-! ### `BijOn` -/


theorem bijOn_iUnion {s : ι → Set α} {t : ι → Set β} {f : α → β} (H : ∀ i, BijOn f (s i) (t i))
    (Hinj : InjOn f (⋃ i, s i)) : BijOn f (⋃ i, s i) (⋃ i, t i) :=
  ⟨mapsTo_iUnion_iUnion fun i => (H i).mapsTo, Hinj, surjOn_iUnion_iUnion fun i => (H i).surjOn⟩
#align set.bij_on_Union Set.bijOn_iUnion

theorem bijOn_iInter [hi : Nonempty ι] {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, BijOn f (s i) (t i)) (Hinj : InjOn f (⋃ i, s i)) : BijOn f (⋂ i, s i) (⋂ i, t i) :=
  ⟨mapsTo_iInter_iInter fun i => (H i).mapsTo,
    hi.elim fun i => (H i).injOn.mono (iInter_subset _ _),
    surjOn_iInter_iInter (fun i => (H i).surjOn) Hinj⟩
#align set.bij_on_Inter Set.bijOn_iInter

theorem bijOn_iUnion_of_directed {s : ι → Set α} (hs : Directed (· ⊆ ·) s) {t : ι → Set β}
    {f : α → β} (H : ∀ i, BijOn f (s i) (t i)) : BijOn f (⋃ i, s i) (⋃ i, t i) :=
  bijOn_iUnion H <| inj_on_iUnion_of_directed hs fun i => (H i).injOn
#align set.bij_on_Union_of_directed Set.bijOn_iUnion_of_directed

theorem bijOn_iInter_of_directed [Nonempty ι] {s : ι → Set α} (hs : Directed (· ⊆ ·) s)
    {t : ι → Set β} {f : α → β} (H : ∀ i, BijOn f (s i) (t i)) : BijOn f (⋂ i, s i) (⋂ i, t i) :=
  bijOn_iInter H <| inj_on_iUnion_of_directed hs fun i => (H i).injOn
#align set.bij_on_Inter_of_directed Set.bijOn_iInter_of_directed

end Function

/-! ### `image`, `preimage` -/


section Image

theorem image_iUnion {f : α → β} {s : ι → Set α} : (f '' ⋃ i, s i) = ⋃ i, f '' s i := by
  ext1 x
  simp only [mem_image, mem_iUnion, ← exists_and_right, ← exists_and_left]
  -- Porting note: `exists_swap` causes a `simp` loop in Lean4 so we use `rw` instead.
  rw [exists_swap]
#align set.image_Union Set.image_iUnion

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image_iUnion₂ (f : α → β) (s : ∀ i, κ i → Set α) :
    (f '' ⋃ (i) (j), s i j) = ⋃ (i) (j), f '' s i j := by simp_rw [image_iUnion]
#align set.image_Union₂ Set.image_iUnion₂

theorem univ_subtype {p : α → Prop} : (univ : Set (Subtype p)) = ⋃ (x) (h : p x), {⟨x, h⟩} :=
  Set.ext fun ⟨x, h⟩ => by simp [h]
#align set.univ_subtype Set.univ_subtype

theorem range_eq_iUnion {ι} (f : ι → α) : range f = ⋃ i, {f i} :=
  Set.ext fun a => by simp [@eq_comm α a]
#align set.range_eq_Union Set.range_eq_iUnion

theorem image_eq_iUnion (f : α → β) (s : Set α) : f '' s = ⋃ i ∈ s, {f i} :=
  Set.ext fun b => by simp [@eq_comm β b]
#align set.image_eq_Union Set.image_eq_iUnion

theorem biUnion_range {f : ι → α} {g : α → Set β} : ⋃ x ∈ range f, g x = ⋃ y, g (f y) :=
  iSup_range
#align set.bUnion_range Set.biUnion_range

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x y) -/
@[simp]
theorem iUnion_iUnion_eq' {f : ι → α} {g : α → Set β} :
    ⋃ (x) (y) (_ : f y = x), g x = ⋃ y, g (f y) := by simpa using biUnion_range
#align set.Union_Union_eq' Set.iUnion_iUnion_eq'

theorem biInter_range {f : ι → α} {g : α → Set β} : ⋂ x ∈ range f, g x = ⋂ y, g (f y) :=
  iInf_range
#align set.bInter_range Set.biInter_range

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x y) -/
@[simp]
theorem iInter_iInter_eq' {f : ι → α} {g : α → Set β} :
    ⋂ (x) (y) (_ : f y = x), g x = ⋂ y, g (f y) := by simpa using biInter_range
#align set.Inter_Inter_eq' Set.iInter_iInter_eq'

variable {s : Set γ} {f : γ → α} {g : α → Set β}

theorem biUnion_image : ⋃ x ∈ f '' s, g x = ⋃ y ∈ s, g (f y) :=
  iSup_image
#align set.bUnion_image Set.biUnion_image

theorem biInter_image : ⋂ x ∈ f '' s, g x = ⋂ y ∈ s, g (f y) :=
  iInf_image
#align set.bInter_image Set.biInter_image

end Image

section Preimage

theorem monotone_preimage {f : α → β} : Monotone (preimage f) := fun _ _ h => preimage_mono h
#align set.monotone_preimage Set.monotone_preimage

@[simp]
theorem preimage_iUnion {f : α → β} {s : ι → Set β} : (f ⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i :=
  Set.ext <| by simp [preimage]
#align set.preimage_Union Set.preimage_iUnion

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem preimage_iUnion₂ {f : α → β} {s : ∀ i, κ i → Set β} :
    (f ⁻¹' ⋃ (i) (j), s i j) = ⋃ (i) (j), f ⁻¹' s i j := by simp_rw [preimage_iUnion]
#align set.preimage_Union₂ Set.preimage_iUnion₂

theorem image_sUnion {f : α → β} {s : Set (Set α)} : (f '' ⋃₀ s) = ⋃₀ (image f '' s) := by
  ext b
  simp only [mem_image, mem_sUnion, exists_prop, sUnion_image, mem_iUnion]
  constructor
  · rintro ⟨a, ⟨t, ht₁, ht₂⟩, rfl⟩
    exact ⟨t, ht₁, a, ht₂, rfl⟩
  · rintro ⟨t, ht₁, a, ht₂, rfl⟩
    exact ⟨a, ⟨t, ht₁, ht₂⟩, rfl⟩

@[simp]
theorem preimage_sUnion {f : α → β} {s : Set (Set β)} : f ⁻¹' ⋃₀s = ⋃ t ∈ s, f ⁻¹' t := by
  rw [sUnion_eq_biUnion, preimage_iUnion₂]
#align set.preimage_sUnion Set.preimage_sUnion

theorem preimage_iInter {f : α → β} {s : ι → Set β} : (f ⁻¹' ⋂ i, s i) = ⋂ i, f ⁻¹' s i := by
  ext; simp
#align set.preimage_Inter Set.preimage_iInter

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem preimage_iInter₂ {f : α → β} {s : ∀ i, κ i → Set β} :
    (f ⁻¹' ⋂ (i) (j), s i j) = ⋂ (i) (j), f ⁻¹' s i j := by simp_rw [preimage_iInter]
#align set.preimage_Inter₂ Set.preimage_iInter₂

@[simp]
theorem preimage_sInter {f : α → β} {s : Set (Set β)} : f ⁻¹' ⋂₀ s = ⋂ t ∈ s, f ⁻¹' t := by
  rw [sInter_eq_biInter, preimage_iInter₂]
#align set.preimage_sInter Set.preimage_sInter

@[simp]
theorem biUnion_preimage_singleton (f : α → β) (s : Set β) : ⋃ y ∈ s, f ⁻¹' {y} = f ⁻¹' s := by
  rw [← preimage_iUnion₂, biUnion_of_singleton]
#align set.bUnion_preimage_singleton Set.biUnion_preimage_singleton

theorem biUnion_range_preimage_singleton (f : α → β) : ⋃ y ∈ range f, f ⁻¹' {y} = univ := by
  rw [biUnion_preimage_singleton, preimage_range]
#align set.bUnion_range_preimage_singleton Set.biUnion_range_preimage_singleton

end Preimage

section Prod

theorem prod_iUnion {s : Set α} {t : ι → Set β} : (s ×ˢ ⋃ i, t i) = ⋃ i, s ×ˢ t i := by
  ext
  simp
#align set.prod_Union Set.prod_iUnion

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem prod_iUnion₂ {s : Set α} {t : ∀ i, κ i → Set β} :
    (s ×ˢ ⋃ (i) (j), t i j) = ⋃ (i) (j), s ×ˢ t i j := by simp_rw [prod_iUnion]
#align set.prod_Union₂ Set.prod_iUnion₂

theorem prod_sUnion {s : Set α} {C : Set (Set β)} : s ×ˢ ⋃₀C = ⋃₀((fun t => s ×ˢ t) '' C) := by
  simp_rw [sUnion_eq_biUnion, biUnion_image, prod_iUnion₂]
#align set.prod_sUnion Set.prod_sUnion

theorem iUnion_prod_const {s : ι → Set α} {t : Set β} : (⋃ i, s i) ×ˢ t = ⋃ i, s i ×ˢ t := by
  ext
  simp
#align set.Union_prod_const Set.iUnion_prod_const

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iUnion₂_prod_const {s : ∀ i, κ i → Set α} {t : Set β} :
    (⋃ (i) (j), s i j) ×ˢ t = ⋃ (i) (j), s i j ×ˢ t := by simp_rw [iUnion_prod_const]
#align set.Union₂_prod_const Set.iUnion₂_prod_const

theorem sUnion_prod_const {C : Set (Set α)} {t : Set β} :
    ⋃₀C ×ˢ t = ⋃₀((fun s : Set α => s ×ˢ t) '' C) := by
  simp only [sUnion_eq_biUnion, iUnion₂_prod_const, biUnion_image]
#align set.sUnion_prod_const Set.sUnion_prod_const

theorem iUnion_prod {ι ι' α β} (s : ι → Set α) (t : ι' → Set β) :
    ⋃ x : ι × ι', s x.1 ×ˢ t x.2 = (⋃ i : ι, s i) ×ˢ ⋃ i : ι', t i := by
  ext
  simp
#align set.Union_prod Set.iUnion_prod

/-- Analogue of `iSup_prod` for sets. -/
lemma iUnion_prod' (f : β × γ → Set α) : ⋃ x : β × γ, f x = ⋃ (i : β) (j : γ), f (i, j) :=
  iSup_prod

theorem iUnion_prod_of_monotone [SemilatticeSup α] {s : α → Set β} {t : α → Set γ} (hs : Monotone s)
    (ht : Monotone t) : ⋃ x, s x ×ˢ t x = (⋃ x, s x) ×ˢ ⋃ x, t x := by
  ext ⟨z, w⟩; simp only [mem_prod, mem_iUnion, exists_imp, and_imp, iff_def]; constructor
  · intro x hz hw
    exact ⟨⟨x, hz⟩, x, hw⟩
  · intro x hz x' hw
    exact ⟨x ⊔ x', hs le_sup_left hz, ht le_sup_right hw⟩
#align set.Union_prod_of_monotone Set.iUnion_prod_of_monotone

theorem sInter_prod_sInter_subset (S : Set (Set α)) (T : Set (Set β)) :
    ⋂₀ S ×ˢ ⋂₀ T ⊆ ⋂ r ∈ S ×ˢ T, r.1 ×ˢ r.2 :=
  subset_iInter₂ fun x hx _ hy => ⟨hy.1 x.1 hx.1, hy.2 x.2 hx.2⟩
#align set.sInter_prod_sInter_subset Set.sInter_prod_sInter_subset

theorem sInter_prod_sInter {S : Set (Set α)} {T : Set (Set β)} (hS : S.Nonempty) (hT : T.Nonempty) :
    ⋂₀ S ×ˢ ⋂₀ T = ⋂ r ∈ S ×ˢ T, r.1 ×ˢ r.2 := by
  obtain ⟨s₁, h₁⟩ := hS
  obtain ⟨s₂, h₂⟩ := hT
  refine Set.Subset.antisymm (sInter_prod_sInter_subset S T) fun x hx => ?_
  rw [mem_iInter₂] at hx
  exact ⟨fun s₀ h₀ => (hx (s₀, s₂) ⟨h₀, h₂⟩).1, fun s₀ h₀ => (hx (s₁, s₀) ⟨h₁, h₀⟩).2⟩
#align set.sInter_prod_sInter Set.sInter_prod_sInter

theorem sInter_prod {S : Set (Set α)} (hS : S.Nonempty) (t : Set β) :
    ⋂₀ S ×ˢ t = ⋂ s ∈ S, s ×ˢ t := by
  rw [← sInter_singleton t, sInter_prod_sInter hS (singleton_nonempty t), sInter_singleton]
  simp_rw [prod_singleton, mem_image, iInter_exists, biInter_and', iInter_iInter_eq_right]
#align set.sInter_prod Set.sInter_prod

theorem prod_sInter {T : Set (Set β)} (hT : T.Nonempty) (s : Set α) :
    s ×ˢ ⋂₀ T = ⋂ t ∈ T, s ×ˢ t := by
  rw [← sInter_singleton s, sInter_prod_sInter (singleton_nonempty s) hT, sInter_singleton]
  simp_rw [singleton_prod, mem_image, iInter_exists, biInter_and', iInter_iInter_eq_right]
#align set.prod_sInter Set.prod_sInter

theorem prod_iInter {s : Set α} {t : ι → Set β} [hι : Nonempty ι] :
    (s ×ˢ ⋂ i, t i) = ⋂ i, s ×ˢ t i := by
  ext x
  simp only [mem_prod, mem_iInter]
  exact ⟨fun h i => ⟨h.1, h.2 i⟩, fun h => ⟨(h hι.some).1, fun i => (h i).2⟩⟩
#align prod_Inter Set.prod_iInter

end Prod

section Image2

variable (f : α → β → γ) {s : Set α} {t : Set β}

/-- The `Set.image2` version of `Set.image_eq_iUnion` -/
theorem image2_eq_iUnion (s : Set α) (t : Set β) : image2 f s t = ⋃ (i ∈ s) (j ∈ t), {f i j} := by
  ext; simp [eq_comm]
#align set.image2_eq_Union Set.image2_eq_iUnion

theorem iUnion_image_left : ⋃ a ∈ s, f a '' t = image2 f s t := by
  simp only [image2_eq_iUnion, image_eq_iUnion]
#align set.Union_image_left Set.iUnion_image_left

theorem iUnion_image_right : ⋃ b ∈ t, (f · b) '' s = image2 f s t := by
  rw [image2_swap, iUnion_image_left]
#align set.Union_image_right Set.iUnion_image_right

theorem image2_iUnion_left (s : ι → Set α) (t : Set β) :
    image2 f (⋃ i, s i) t = ⋃ i, image2 f (s i) t := by
  simp only [← image_prod, iUnion_prod_const, image_iUnion]
#align set.image2_Union_left Set.image2_iUnion_left

theorem image2_iUnion_right (s : Set α) (t : ι → Set β) :
    image2 f s (⋃ i, t i) = ⋃ i, image2 f s (t i) := by
  simp only [← image_prod, prod_iUnion, image_iUnion]
#align set.image2_Union_right Set.image2_iUnion_right

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image2_iUnion₂_left (s : ∀ i, κ i → Set α) (t : Set β) :
    image2 f (⋃ (i) (j), s i j) t = ⋃ (i) (j), image2 f (s i j) t := by simp_rw [image2_iUnion_left]
#align set.image2_Union₂_left Set.image2_iUnion₂_left

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image2_iUnion₂_right (s : Set α) (t : ∀ i, κ i → Set β) :
    image2 f s (⋃ (i) (j), t i j) = ⋃ (i) (j), image2 f s (t i j) := by
  simp_rw [image2_iUnion_right]
#align set.image2_Union₂_right Set.image2_iUnion₂_right

theorem image2_iInter_subset_left (s : ι → Set α) (t : Set β) :
    image2 f (⋂ i, s i) t ⊆ ⋂ i, image2 f (s i) t := by
  simp_rw [image2_subset_iff, mem_iInter]
  exact fun x hx y hy i => mem_image2_of_mem (hx _) hy
#align set.image2_Inter_subset_left Set.image2_iInter_subset_left

theorem image2_iInter_subset_right (s : Set α) (t : ι → Set β) :
    image2 f s (⋂ i, t i) ⊆ ⋂ i, image2 f s (t i) := by
  simp_rw [image2_subset_iff, mem_iInter]
  exact fun x hx y hy i => mem_image2_of_mem hx (hy _)
#align set.image2_Inter_subset_right Set.image2_iInter_subset_right

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image2_iInter₂_subset_left (s : ∀ i, κ i → Set α) (t : Set β) :
    image2 f (⋂ (i) (j), s i j) t ⊆ ⋂ (i) (j), image2 f (s i j) t := by
  simp_rw [image2_subset_iff, mem_iInter]
  exact fun x hx y hy i j => mem_image2_of_mem (hx _ _) hy
#align set.image2_Inter₂_subset_left Set.image2_iInter₂_subset_left

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image2_iInter₂_subset_right (s : Set α) (t : ∀ i, κ i → Set β) :
    image2 f s (⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), image2 f s (t i j) := by
  simp_rw [image2_subset_iff, mem_iInter]
  exact fun x hx y hy i j => mem_image2_of_mem hx (hy _ _)
#align set.image2_Inter₂_subset_right Set.image2_iInter₂_subset_right

theorem prod_eq_biUnion_left : s ×ˢ t = ⋃ a ∈ s, (fun b => (a, b)) '' t := by
  rw [iUnion_image_left, image2_mk_eq_prod]
#align set.prod_eq_bUnion_left Set.prod_eq_biUnion_left

theorem prod_eq_biUnion_right : s ×ˢ t = ⋃ b ∈ t, (fun a => (a, b)) '' s := by
  rw [iUnion_image_right, image2_mk_eq_prod]
#align set.prod_eq_bUnion_right Set.prod_eq_biUnion_right

end Image2

section Seq

theorem seq_def {s : Set (α → β)} {t : Set α} : seq s t = ⋃ f ∈ s, f '' t := by
  rw [seq_eq_image2, iUnion_image_left]
#align set.seq_def Set.seq_def

theorem seq_subset {s : Set (α → β)} {t : Set α} {u : Set β} :
    seq s t ⊆ u ↔ ∀ f ∈ s, ∀ a ∈ t, (f : α → β) a ∈ u :=
  image2_subset_iff
#align set.seq_subset Set.seq_subset

@[gcongr]
theorem seq_mono {s₀ s₁ : Set (α → β)} {t₀ t₁ : Set α} (hs : s₀ ⊆ s₁) (ht : t₀ ⊆ t₁) :
    seq s₀ t₀ ⊆ seq s₁ t₁ := image2_subset hs ht
#align set.seq_mono Set.seq_mono

theorem singleton_seq {f : α → β} {t : Set α} : Set.seq ({f} : Set (α → β)) t = f '' t :=
  image2_singleton_left
#align set.singleton_seq Set.singleton_seq

theorem seq_singleton {s : Set (α → β)} {a : α} : Set.seq s {a} = (fun f : α → β => f a) '' s :=
  image2_singleton_right
#align set.seq_singleton Set.seq_singleton

theorem seq_seq {s : Set (β → γ)} {t : Set (α → β)} {u : Set α} :
    seq s (seq t u) = seq (seq ((· ∘ ·) '' s) t) u := by
  simp only [seq_eq_image2, image2_image_left]
  exact .symm <| image2_assoc fun _ _ _ ↦ rfl
#align set.seq_seq Set.seq_seq

theorem image_seq {f : β → γ} {s : Set (α → β)} {t : Set α} :
    f '' seq s t = seq ((f ∘ ·) '' s) t := by
  simp only [seq, image_image2, image2_image_left, comp_apply]
#align set.image_seq Set.image_seq

theorem prod_eq_seq {s : Set α} {t : Set β} : s ×ˢ t = (Prod.mk '' s).seq t := by
  rw [seq_eq_image2, image2_image_left, image2_mk_eq_prod]
#align set.prod_eq_seq Set.prod_eq_seq

theorem prod_image_seq_comm (s : Set α) (t : Set β) :
    (Prod.mk '' s).seq t = seq ((fun b a => (a, b)) '' t) s := by
  rw [← prod_eq_seq, ← image_swap_prod, prod_eq_seq, image_seq, ← image_comp]; rfl
#align set.prod_image_seq_comm Set.prod_image_seq_comm

theorem image2_eq_seq (f : α → β → γ) (s : Set α) (t : Set β) : image2 f s t = seq (f '' s) t := by
  rw [seq_eq_image2, image2_image_left]
#align set.image2_eq_seq Set.image2_eq_seq

end Seq

section Pi

variable {π : α → Type*}

theorem pi_def (i : Set α) (s : ∀ a, Set (π a)) : pi i s = ⋂ a ∈ i, eval a ⁻¹' s a := by
  ext
  simp
#align set.pi_def Set.pi_def

theorem univ_pi_eq_iInter (t : ∀ i, Set (π i)) : pi univ t = ⋂ i, eval i ⁻¹' t i := by
  simp only [pi_def, iInter_true, mem_univ]
#align set.univ_pi_eq_Inter Set.univ_pi_eq_iInter

theorem pi_diff_pi_subset (i : Set α) (s t : ∀ a, Set (π a)) :
    pi i s \ pi i t ⊆ ⋃ a ∈ i, eval a ⁻¹' (s a \ t a) := by
  refine diff_subset_comm.2 fun x hx a ha => ?_
  simp only [mem_diff, mem_pi, mem_iUnion, not_exists, mem_preimage, not_and, not_not,
    eval_apply] at hx
  exact hx.2 _ ha (hx.1 _ ha)
#align set.pi_diff_pi_subset Set.pi_diff_pi_subset

theorem iUnion_univ_pi {ι : α → Type*} (t : (a : α) → ι a → Set (π a)) :
    ⋃ x : (a : α) → ι a, pi univ (fun a => t a (x a)) = pi univ fun a => ⋃ j : ι a, t a j := by
  ext
  simp [Classical.skolem]
#align set.Union_univ_pi Set.iUnion_univ_pi

end Pi

section Directed

theorem directedOn_iUnion {r} {f : ι → Set α} (hd : Directed (· ⊆ ·) f)
    (h : ∀ x, DirectedOn r (f x)) : DirectedOn r (⋃ x, f x) := by
  simp only [DirectedOn, exists_prop, mem_iUnion, exists_imp]
  exact fun a₁ b₁ fb₁ a₂ b₂ fb₂ =>
    let ⟨z, zb₁, zb₂⟩ := hd b₁ b₂
    let ⟨x, xf, xa₁, xa₂⟩ := h z a₁ (zb₁ fb₁) a₂ (zb₂ fb₂)
    ⟨x, ⟨z, xf⟩, xa₁, xa₂⟩
#align set.directed_on_Union Set.directedOn_iUnion

@[deprecated (since := "2024-05-05")]
alias directed_on_iUnion := directedOn_iUnion

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
#align function.surjective.Union_comp Function.Surjective.iUnion_comp

theorem iInter_comp {f : ι → ι₂} (hf : Surjective f) (g : ι₂ → Set α) : ⋂ x, g (f x) = ⋂ y, g y :=
  hf.iInf_comp g
#align function.surjective.Inter_comp Function.Surjective.iInter_comp

end Surjective

end Function

/-!
### Disjoint sets
-/


section Disjoint

variable {s t u : Set α} {f : α → β}

namespace Set

@[simp]
theorem disjoint_iUnion_left {ι : Sort*} {s : ι → Set α} :
    Disjoint (⋃ i, s i) t ↔ ∀ i, Disjoint (s i) t :=
  iSup_disjoint_iff
#align set.disjoint_Union_left Set.disjoint_iUnion_left

@[simp]
theorem disjoint_iUnion_right {ι : Sort*} {s : ι → Set α} :
    Disjoint t (⋃ i, s i) ↔ ∀ i, Disjoint t (s i) :=
  disjoint_iSup_iff
#align set.disjoint_Union_right Set.disjoint_iUnion_right

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
-- Porting note (#10618): removing `simp`. `simp` can prove it
theorem disjoint_iUnion₂_left {s : ∀ i, κ i → Set α} {t : Set α} :
    Disjoint (⋃ (i) (j), s i j) t ↔ ∀ i j, Disjoint (s i j) t :=
  iSup₂_disjoint_iff
#align set.disjoint_Union₂_left Set.disjoint_iUnion₂_left

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
-- Porting note (#10618): removing `simp`. `simp` can prove it
theorem disjoint_iUnion₂_right {s : Set α} {t : ∀ i, κ i → Set α} :
    Disjoint s (⋃ (i) (j), t i j) ↔ ∀ i j, Disjoint s (t i j) :=
  disjoint_iSup₂_iff
#align set.disjoint_Union₂_right Set.disjoint_iUnion₂_right

@[simp]
theorem disjoint_sUnion_left {S : Set (Set α)} {t : Set α} :
    Disjoint (⋃₀S) t ↔ ∀ s ∈ S, Disjoint s t :=
  sSup_disjoint_iff
#align set.disjoint_sUnion_left Set.disjoint_sUnion_left

@[simp]
theorem disjoint_sUnion_right {s : Set α} {S : Set (Set α)} :
    Disjoint s (⋃₀S) ↔ ∀ t ∈ S, Disjoint s t :=
  disjoint_sSup_iff
#align set.disjoint_sUnion_right Set.disjoint_sUnion_right

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
#align set.Ici_supr Set.Ici_iSup

theorem Iic_iInf (f : ι → α) : Iic (⨅ i, f i) = ⋂ i, Iic (f i) :=
  ext fun _ => by simp only [mem_Iic, le_iInf_iff, mem_iInter]
#align set.Iic_infi Set.Iic_iInf

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Ici_iSup₂ (f : ∀ i, κ i → α) : Ici (⨆ (i) (j), f i j) = ⋂ (i) (j), Ici (f i j) := by
  simp_rw [Ici_iSup]
#align set.Ici_supr₂ Set.Ici_iSup₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Iic_iInf₂ (f : ∀ i, κ i → α) : Iic (⨅ (i) (j), f i j) = ⋂ (i) (j), Iic (f i j) := by
  simp_rw [Iic_iInf]
#align set.Iic_infi₂ Set.Iic_iInf₂

theorem Ici_sSup (s : Set α) : Ici (sSup s) = ⋂ a ∈ s, Ici a := by rw [sSup_eq_iSup, Ici_iSup₂]
#align set.Ici_Sup Set.Ici_sSup

theorem Iic_sInf (s : Set α) : Iic (sInf s) = ⋂ a ∈ s, Iic a := by rw [sInf_eq_iInf, Iic_iInf₂]
#align set.Iic_Inf Set.Iic_sInf

end Set

namespace Set

variable (t : α → Set β)

theorem biUnion_diff_biUnion_subset (s₁ s₂ : Set α) :
    ((⋃ x ∈ s₁, t x) \ ⋃ x ∈ s₂, t x) ⊆ ⋃ x ∈ s₁ \ s₂, t x := by
  simp only [diff_subset_iff, ← biUnion_union]
  apply biUnion_subset_biUnion_left
  rw [union_diff_self]
  apply subset_union_right
#align set.bUnion_diff_bUnion_subset Set.biUnion_diff_biUnion_subset

/-- If `t` is an indexed family of sets, then there is a natural map from `Σ i, t i` to `⋃ i, t i`
sending `⟨i, x⟩` to `x`. -/
def sigmaToiUnion (x : Σi, t i) : ⋃ i, t i :=
  ⟨x.2, mem_iUnion.2 ⟨x.1, x.2.2⟩⟩
#align set.sigma_to_Union Set.sigmaToiUnion

theorem sigmaToiUnion_surjective : Surjective (sigmaToiUnion t)
  | ⟨b, hb⟩ =>
    have : ∃ a, b ∈ t a := by simpa using hb
    let ⟨a, hb⟩ := this
    ⟨⟨a, b, hb⟩, rfl⟩
#align set.sigma_to_Union_surjective Set.sigmaToiUnion_surjective

theorem sigmaToiUnion_injective (h : Pairwise fun i j => Disjoint (t i) (t j)) :
    Injective (sigmaToiUnion t)
  | ⟨a₁, b₁, h₁⟩, ⟨a₂, b₂, h₂⟩, eq =>
    have b_eq : b₁ = b₂ := congr_arg Subtype.val eq
    have a_eq : a₁ = a₂ :=
      by_contradiction fun ne =>
        have : b₁ ∈ t a₁ ∩ t a₂ := ⟨h₁, b_eq.symm ▸ h₂⟩
        (h ne).le_bot this
    Sigma.eq a_eq <| Subtype.eq <| by subst b_eq; subst a_eq; rfl
#align set.sigma_to_Union_injective Set.sigmaToiUnion_injective

theorem sigmaToiUnion_bijective (h : Pairwise fun i j => Disjoint (t i) (t j)) :
    Bijective (sigmaToiUnion t) :=
  ⟨sigmaToiUnion_injective t h, sigmaToiUnion_surjective t⟩
#align set.sigma_to_Union_bijective Set.sigmaToiUnion_bijective

/-- Equivalence from the disjoint union of a family of sets forming a partition of `β`, to `β`
itself. -/
noncomputable def sigmaEquiv (s : α → Set β) (hs : ∀ b, ∃! i, b ∈ s i) :
    (Σ i, s i) ≃ β where
  toFun | ⟨_, b⟩ => b
  invFun b := ⟨(hs b).choose, b, (hs b).choose_spec.1⟩
  left_inv | ⟨i, b, hb⟩ => Sigma.subtype_ext ((hs b).choose_spec.2 i hb).symm rfl
  right_inv _ := rfl

/-- Equivalence between a disjoint union and a dependent sum. -/
noncomputable def unionEqSigmaOfDisjoint {t : α → Set β}
    (h : Pairwise fun i j => Disjoint (t i) (t j)) :
    (⋃ i, t i) ≃ Σi, t i :=
  (Equiv.ofBijective _ <| sigmaToiUnion_bijective t h).symm
#align set.Union_eq_sigma_of_disjoint Set.unionEqSigmaOfDisjoint

theorem iUnion_ge_eq_iUnion_nat_add (u : ℕ → Set α) (n : ℕ) : ⋃ i ≥ n, u i = ⋃ i, u (i + n) :=
  iSup_ge_eq_iSup_nat_add u n
#align set.Union_ge_eq_Union_nat_add Set.iUnion_ge_eq_iUnion_nat_add

theorem iInter_ge_eq_iInter_nat_add (u : ℕ → Set α) (n : ℕ) : ⋂ i ≥ n, u i = ⋂ i, u (i + n) :=
  iInf_ge_eq_iInf_nat_add u n
#align set.Inter_ge_eq_Inter_nat_add Set.iInter_ge_eq_iInter_nat_add

theorem _root_.Monotone.iUnion_nat_add {f : ℕ → Set α} (hf : Monotone f) (k : ℕ) :
    ⋃ n, f (n + k) = ⋃ n, f n :=
  hf.iSup_nat_add k
#align monotone.Union_nat_add Monotone.iUnion_nat_add

theorem _root_.Antitone.iInter_nat_add {f : ℕ → Set α} (hf : Antitone f) (k : ℕ) :
    ⋂ n, f (n + k) = ⋂ n, f n :=
  hf.iInf_nat_add k
#align antitone.Inter_nat_add Antitone.iInter_nat_add

/- Porting note: removing `simp`. LHS does not simplify. Possible linter bug. Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/complete_lattice.20and.20has_sup/near/316497982
-/
theorem iUnion_iInter_ge_nat_add (f : ℕ → Set α) (k : ℕ) :
    ⋃ n, ⋂ i ≥ n, f (i + k) = ⋃ n, ⋂ i ≥ n, f i :=
  iSup_iInf_ge_nat_add f k
#align set.Union_Inter_ge_nat_add Set.iUnion_iInter_ge_nat_add

theorem union_iUnion_nat_succ (u : ℕ → Set α) : (u 0 ∪ ⋃ i, u (i + 1)) = ⋃ i, u i :=
  sup_iSup_nat_succ u
#align set.union_Union_nat_succ Set.union_iUnion_nat_succ

theorem inter_iInter_nat_succ (u : ℕ → Set α) : (u 0 ∩ ⋂ i, u (i + 1)) = ⋂ i, u i :=
  inf_iInf_nat_succ u
#align set.inter_Inter_nat_succ Set.inter_iInter_nat_succ

end Set

open Set

variable [CompleteLattice β]

theorem iSup_iUnion (s : ι → Set α) (f : α → β) : ⨆ a ∈ ⋃ i, s i, f a = ⨆ (i) (a ∈ s i), f a := by
  rw [iSup_comm]
  simp_rw [mem_iUnion, iSup_exists]
#align supr_Union iSup_iUnion

theorem iInf_iUnion (s : ι → Set α) (f : α → β) : ⨅ a ∈ ⋃ i, s i, f a = ⨅ (i) (a ∈ s i), f a :=
  iSup_iUnion (β := βᵒᵈ) s f
#align infi_Union iInf_iUnion

theorem sSup_iUnion (t : ι → Set β) : sSup (⋃ i, t i) = ⨆ i, sSup (t i) := by
  simp_rw [sSup_eq_iSup, iSup_iUnion]

theorem sSup_sUnion (s : Set (Set β)) : sSup (⋃₀ s) = ⨆ t ∈ s, sSup t := by
  simp only [sUnion_eq_biUnion, sSup_eq_iSup, iSup_iUnion]
#align Sup_sUnion sSup_sUnion

theorem sInf_sUnion (s : Set (Set β)) : sInf (⋃₀ s) = ⨅ t ∈ s, sInf t :=
  sSup_sUnion (β := βᵒᵈ) s
#align Inf_sUnion sInf_sUnion

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
