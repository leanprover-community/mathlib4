/-
Copyright (c) 2021 Aaron Anderson, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Kevin Buzzard, Yaël Dillies, Eric Wieser
-/
import Mathlib.Data.Finset.Lattice.Union
import Mathlib.Data.Finset.Pairwise
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.CompleteLatticeIntervals

/-!
# Supremum independence

In this file, we define supremum independence of indexed sets. An indexed family `f : ι → α` is
sup-independent if, for all `a`, `f a` and the supremum of the rest are disjoint.

## Main definitions

* `Finset.SupIndep s f`: a family of elements `f` are supremum independent on the finite set `s`.
* `sSupIndep s`: a set of elements are supremum independent.
* `iSupIndep f`: a family of elements are supremum independent.

## Main statements

* In a distributive lattice, supremum independence is equivalent to pairwise disjointness:
  * `Finset.supIndep_iff_pairwiseDisjoint`
  * `CompleteLattice.sSupIndep_iff_pairwiseDisjoint`
  * `CompleteLattice.iSupIndep_iff_pairwiseDisjoint`
* Otherwise, supremum independence is stronger than pairwise disjointness:
  * `Finset.SupIndep.pairwiseDisjoint`
  * `sSupIndep.pairwiseDisjoint`
  * `iSupIndep.pairwiseDisjoint`

## Implementation notes

For the finite version, we avoid the "obvious" definition
`∀ i ∈ s, Disjoint (f i) ((s.erase i).sup f)` because `erase` would require decidable equality on
`ι`.
-/


variable {α β ι ι' : Type*}

/-! ### On lattices with a bottom element, via `Finset.sup` -/


namespace Finset

section Lattice

variable [Lattice α] [OrderBot α]

/-- Supremum independence of finite sets. We avoid the "obvious" definition using `s.erase i`
because `erase` would require decidable equality on `ι`. -/
def SupIndep (s : Finset ι) (f : ι → α) : Prop :=
  ∀ ⦃t⦄, t ⊆ s → ∀ ⦃i⦄, i ∈ s → i ∉ t → Disjoint (f i) (t.sup f)

variable {s t : Finset ι} {f : ι → α} {i : ι}

/-- The RHS looks like the definition of `iSupIndep`. -/
theorem supIndep_iff_disjoint_erase [DecidableEq ι] :
    s.SupIndep f ↔ ∀ i ∈ s, Disjoint (f i) ((s.erase i).sup f) :=
  ⟨fun hs _ hi => hs (erase_subset _ _) hi (notMem_erase _ _), fun hs _ ht i hi hit =>
    (hs i hi).mono_right (sup_mono fun _ hj => mem_erase.2 ⟨ne_of_mem_of_not_mem hj hit, ht hj⟩)⟩

/-- If both the index type and the lattice have decidable equality,
then the `SupIndep` predicate is decidable.

TODO: speedup the definition and drop the `[DecidableEq ι]` assumption
by iterating over the pairs `(a, t)` such that `s = Finset.cons a t _`
using something like `List.eraseIdx`
or by generating both `f i` and `(s.erase i).sup f` in one loop over `s`.
Yet another possible optimization is to precompute partial suprema of `f`
over the inits and tails of the list representing `s`,
store them in 2 `Array`s,
then compute each `sup` in 1 operation. -/
instance [DecidableEq ι] [DecidableEq α] : Decidable (SupIndep s f) :=
  have : ∀ i, Decidable (Disjoint (f i) ((s.erase i).sup f)) := fun _ ↦
    decidable_of_iff _ disjoint_iff.symm
  decidable_of_iff _ supIndep_iff_disjoint_erase.symm

theorem SupIndep.subset (ht : t.SupIndep f) (h : s ⊆ t) : s.SupIndep f := fun _ hu _ hi =>
  ht (hu.trans h) (h hi)

@[simp]
theorem supIndep_empty (f : ι → α) : (∅ : Finset ι).SupIndep f := fun _ _ a ha =>
  (notMem_empty a ha).elim

@[simp]
theorem supIndep_singleton (i : ι) (f : ι → α) : ({i} : Finset ι).SupIndep f :=
  fun s hs j hji hj => by
    rw [eq_empty_of_ssubset_singleton ⟨hs, fun h => hj (h hji)⟩, sup_empty]
    exact disjoint_bot_right

theorem SupIndep.pairwiseDisjoint (hs : s.SupIndep f) : (s : Set ι).PairwiseDisjoint f :=
  fun _ ha _ hb hab =>
    sup_singleton.subst <| hs (singleton_subset_iff.2 hb) ha <| notMem_singleton.2 hab

@[deprecated (since := "2025-01-17")] alias sup_indep.pairwise_disjoint := SupIndep.pairwiseDisjoint

theorem SupIndep.le_sup_iff (hs : s.SupIndep f) (hts : t ⊆ s) (hi : i ∈ s) (hf : ∀ i, f i ≠ ⊥) :
    f i ≤ t.sup f ↔ i ∈ t := by
  refine ⟨fun h => ?_, le_sup⟩
  by_contra hit
  exact hf i (disjoint_self.1 <| (hs hts hi hit).mono_right h)

theorem SupIndep.antitone_fun {g : ι → α} (hle : ∀ x ∈ s, f x ≤ g x) (h : s.SupIndep g) :
    s.SupIndep f := fun _t hts i his hit ↦
  (h hts his hit).mono (hle i his) <| Finset.sup_mono_fun fun x hx ↦ hle x <| hts hx

@[deprecated (since := "2025-01-17")]
alias supIndep_antimono_fun := SupIndep.antitone_fun

protected theorem SupIndep.image [DecidableEq ι] {s : Finset ι'} {g : ι' → ι}
    (hs : s.SupIndep (f ∘ g)) : (s.image g).SupIndep f := by
  intro t ht i hi hit
  rcases subset_image_iff.mp ht with ⟨t, hts, rfl⟩
  rcases mem_image.mp hi with ⟨i, his, rfl⟩
  rw [sup_image]
  exact hs hts his (hit <| mem_image_of_mem _ ·)

theorem supIndep_map {s : Finset ι'} {g : ι' ↪ ι} : (s.map g).SupIndep f ↔ s.SupIndep (f ∘ g) := by
  refine ⟨fun hs t ht i hi hit => ?_, fun hs => ?_⟩
  · rw [← sup_map]
    exact hs (map_subset_map.2 ht) ((mem_map' _).2 hi) (by rwa [mem_map'])
  · classical
    rw [map_eq_image]
    exact hs.image

@[simp]
theorem supIndep_pair [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    ({i, j} : Finset ι).SupIndep f ↔ Disjoint (f i) (f j) := by
  suffices Disjoint (f i) (f j) → Disjoint (f j) ((Finset.erase {i, j} j).sup f) by
    simpa [supIndep_iff_disjoint_erase, hij]
  rw [pair_comm]
  simp [hij.symm, disjoint_comm]

theorem supIndep_univ_bool (f : Bool → α) :
    (Finset.univ : Finset Bool).SupIndep f ↔ Disjoint (f false) (f true) :=
  haveI : true ≠ false := by simp only [Ne, not_false_iff, reduceCtorEq]
  (supIndep_pair this).trans disjoint_comm

@[simp]
theorem supIndep_univ_fin_two (f : Fin 2 → α) :
    (Finset.univ : Finset (Fin 2)).SupIndep f ↔ Disjoint (f 0) (f 1) :=
  have : (0 : Fin 2) ≠ 1 := by simp
  supIndep_pair this

@[simp]
theorem supIndep_attach : (s.attach.SupIndep fun a => f a) ↔ s.SupIndep f := by
  simpa [Finset.attach_map_val] using (supIndep_map (s := s.attach) (g := .subtype _)).symm

alias ⟨_, SupIndep.attach⟩ := supIndep_attach

end Lattice

section DistribLattice

variable [DistribLattice α] [OrderBot α] {s : Finset ι} {f : ι → α}

theorem supIndep_iff_pairwiseDisjoint : s.SupIndep f ↔ (s : Set ι).PairwiseDisjoint f :=
  ⟨SupIndep.pairwiseDisjoint, fun hs _ ht _ hi hit =>
    Finset.disjoint_sup_right.2 fun _ hj => hs hi (ht hj) (ne_of_mem_of_not_mem hj hit).symm⟩

alias ⟨_, _root_.Set.PairwiseDisjoint.supIndep⟩ := supIndep_iff_pairwiseDisjoint

/-- Bind operation for `SupIndep`. -/
protected theorem SupIndep.sup [DecidableEq ι] {s : Finset ι'} {g : ι' → Finset ι} {f : ι → α}
    (hs : s.SupIndep fun i => (g i).sup f) (hg : ∀ i' ∈ s, (g i').SupIndep f) :
    (s.sup g).SupIndep f := by
  simp_rw [supIndep_iff_pairwiseDisjoint] at hs hg ⊢
  rw [sup_eq_biUnion, coe_biUnion]
  exact hs.biUnion_finset hg

/-- Bind operation for `SupIndep`. -/
protected theorem SupIndep.biUnion [DecidableEq ι] {s : Finset ι'} {g : ι' → Finset ι} {f : ι → α}
    (hs : s.SupIndep fun i => (g i).sup f) (hg : ∀ i' ∈ s, (g i').SupIndep f) :
    (s.biUnion g).SupIndep f := by
  rw [← sup_eq_biUnion]
  exact hs.sup hg

/-- Bind operation for `SupIndep`. -/
protected theorem SupIndep.sigma {β : ι → Type*} {s : Finset ι} {g : ∀ i, Finset (β i)}
    {f : Sigma β → α} (hs : s.SupIndep fun i => (g i).sup fun b => f ⟨i, b⟩)
    (hg : ∀ i ∈ s, (g i).SupIndep fun b => f ⟨i, b⟩) : (s.sigma g).SupIndep f := by
  rintro t ht ⟨i, b⟩ hi hit
  rw [Finset.disjoint_sup_right]
  rintro ⟨j, c⟩ hj
  have hbc := (ne_of_mem_of_not_mem hj hit).symm
  replace hj := ht hj
  rw [mem_sigma] at hi hj
  obtain rfl | hij := eq_or_ne i j
  · exact (hg _ hj.1).pairwiseDisjoint hi.2 hj.2 (sigma_mk_injective.ne_iff.1 hbc)
  · refine (hs.pairwiseDisjoint hi.1 hj.1 hij).mono ?_ ?_
    · convert le_sup (α := α) hi.2; simp
    · convert le_sup (α := α) hj.2; simp

protected theorem SupIndep.product {s : Finset ι} {t : Finset ι'} {f : ι × ι' → α}
    (hs : s.SupIndep fun i => t.sup fun i' => f (i, i'))
    (ht : t.SupIndep fun i' => s.sup fun i => f (i, i')) : (s ×ˢ t).SupIndep f := by
  rintro u hu ⟨i, i'⟩ hi hiu
  rw [Finset.disjoint_sup_right]
  rintro ⟨j, j'⟩ hj
  have hij := (ne_of_mem_of_not_mem hj hiu).symm
  replace hj := hu hj
  rw [mem_product] at hi hj
  obtain rfl | hij := eq_or_ne i j
  · refine (ht.pairwiseDisjoint hi.2 hj.2 <| (Prod.mk_right_injective _).ne_iff.1 hij).mono ?_ ?_
    · convert le_sup (α := α) hi.1; simp
    · convert le_sup (α := α) hj.1; simp
  · refine (hs.pairwiseDisjoint hi.1 hj.1 hij).mono ?_ ?_
    · convert le_sup (α := α) hi.2; simp
    · convert le_sup (α := α) hj.2; simp

theorem supIndep_product_iff {s : Finset ι} {t : Finset ι'} {f : ι × ι' → α} :
    (s.product t).SupIndep f ↔ (s.SupIndep fun i => t.sup fun i' => f (i, i'))
      ∧ t.SupIndep fun i' => s.sup fun i => f (i, i') := by
  refine ⟨?_, fun h => h.1.product h.2⟩
  simp_rw [supIndep_iff_pairwiseDisjoint]
  refine fun h => ⟨fun i hi j hj hij => ?_, fun i hi j hj hij => ?_⟩ <;>
      simp_rw [Finset.disjoint_sup_left, Finset.disjoint_sup_right] <;>
    intro i' hi' j' hj'
  · exact h (mk_mem_product hi hi') (mk_mem_product hj hj') (ne_of_apply_ne Prod.fst hij)
  · exact h (mk_mem_product hi' hi) (mk_mem_product hj' hj) (ne_of_apply_ne Prod.snd hij)

end DistribLattice

end Finset

/-! ### On complete lattices via `sSup` -/

section CompleteLattice
variable [CompleteLattice α]

open Set Function

/-- An independent set of elements in a complete lattice is one in which every element is disjoint
  from the `Sup` of the rest. -/
def sSupIndep (s : Set α) : Prop :=
  ∀ ⦃a⦄, a ∈ s → Disjoint a (sSup (s \ {a}))

@[deprecated (since := "2024-11-24")] alias CompleteLattice.SetIndependent := sSupIndep

variable {s : Set α} (hs : sSupIndep s)

@[simp]
theorem sSupIndep_empty : sSupIndep (∅ : Set α) := fun x hx =>
  (Set.notMem_empty x hx).elim

@[deprecated (since := "2024-11-24")] alias CompleteLattice.setIndependent_empty := sSupIndep_empty

include hs in
theorem sSupIndep.mono {t : Set α} (hst : t ⊆ s) : sSupIndep t := fun _ ha =>
  (hs (hst ha)).mono_right (sSup_le_sSup (diff_subset_diff_left hst))

@[deprecated (since := "2024-11-24")] alias CompleteLattice.SetIndependent.mono := sSupIndep.mono

include hs in
/-- If the elements of a set are independent, then any pair within that set is disjoint. -/
theorem sSupIndep.pairwiseDisjoint : s.PairwiseDisjoint id := fun _ hx y hy h =>
  disjoint_sSup_right (hs hx) ((mem_diff y).mpr ⟨hy, h.symm⟩)

@[deprecated (since := "2024-11-24")]
alias CompleteLattice.SetIndependent.pairwiseDisjoint := sSupIndep.pairwiseDisjoint

theorem sSupIndep_singleton (a : α) : sSupIndep ({a} : Set α) := fun i hi ↦ by
  simp_all

@[deprecated (since := "2024-11-24")]
alias CompleteLattice.setIndependent_singleton := sSupIndep_singleton

theorem sSupIndep_pair {a b : α} (hab : a ≠ b) :
    sSupIndep ({a, b} : Set α) ↔ Disjoint a b := by
  constructor
  · intro h
    exact h.pairwiseDisjoint (mem_insert _ _) (mem_insert_of_mem _ (mem_singleton _)) hab
  · rintro h c ((rfl : c = a) | (rfl : c = b))
    · convert h using 1
      simp [hab, sSup_singleton]
    · convert h.symm using 1
      simp [hab, sSup_singleton]

@[deprecated (since := "2024-11-24")] alias CompleteLattice.setIndependent_pair := sSupIndep_pair

include hs in
/-- If the elements of a set are independent, then any element is disjoint from the `sSup` of some
subset of the rest. -/
theorem sSupIndep.disjoint_sSup {x : α} {y : Set α} (hx : x ∈ s) (hy : y ⊆ s) (hxy : x ∉ y) :
    Disjoint x (sSup y) := by
  have := (hs.mono <| insert_subset_iff.mpr ⟨hx, hy⟩) (mem_insert x _)
  rw [insert_diff_of_mem _ (mem_singleton _), diff_singleton_eq_self hxy] at this
  exact this

@[deprecated (since := "2024-11-24")]
alias CompleteLattice.SetIndependent.disjoint_sSup := sSupIndep.disjoint_sSup

/-- An independent indexed family of elements in a complete lattice is one in which every element
  is disjoint from the `iSup` of the rest.

  Example: an indexed family of non-zero elements in a
  vector space is linearly independent iff the indexed family of subspaces they generate is
  independent in this sense.

  Example: an indexed family of submodules of a module is independent in this sense if
  and only the natural map from the direct sum of the submodules to the module is injective. -/
def iSupIndep {ι : Sort*} {α : Type*} [CompleteLattice α] (t : ι → α) : Prop :=
  ∀ i : ι, Disjoint (t i) (⨆ (j) (_ : j ≠ i), t j)

@[deprecated (since := "2024-11-24")] alias CompleteLattice.Independent := iSupIndep

theorem sSupIndep_iff {α : Type*} [CompleteLattice α] (s : Set α) :
    sSupIndep s ↔ iSupIndep ((↑) : s → α) := by
  simp_rw [iSupIndep, sSupIndep, SetCoe.forall, sSup_eq_iSup]
  refine forall₂_congr fun a ha => ?_
  simp [iSup_subtype, iSup_and]

@[deprecated (since := "2024-11-24")] alias CompleteLattice.setIndependent_iff := sSupIndep_iff

variable {t : ι → α} (ht : iSupIndep t)

theorem iSupIndep_def : iSupIndep t ↔ ∀ i, Disjoint (t i) (⨆ (j) (_ : j ≠ i), t j) :=
  Iff.rfl

@[deprecated (since := "2024-11-24")] alias CompleteLattice.independent_def := iSupIndep_def

theorem iSupIndep_def' : iSupIndep t ↔ ∀ i, Disjoint (t i) (sSup (t '' { j | j ≠ i })) := by
  simp_rw [sSup_image]
  rfl

@[deprecated (since := "2024-11-24")] alias CompleteLattice.independent_def' := iSupIndep_def'

theorem iSupIndep_def'' :
    iSupIndep t ↔ ∀ i, Disjoint (t i) (sSup { a | ∃ j ≠ i, t j = a }) := by
  rw [iSupIndep_def']
  aesop

@[deprecated (since := "2024-11-24")] alias CompleteLattice.independent_def'' := iSupIndep_def''

@[simp]
theorem iSupIndep_empty (t : Empty → α) : iSupIndep t :=
  nofun

@[deprecated (since := "2024-11-24")] alias CompleteLattice.independent_empty := iSupIndep_empty

@[simp]
theorem iSupIndep_pempty (t : PEmpty → α) : iSupIndep t :=
  nofun

@[deprecated (since := "2024-11-24")] alias CompleteLattice.independent_pempty := iSupIndep_pempty

include ht in
/-- If the elements of a set are independent, then any pair within that set is disjoint. -/
theorem iSupIndep.pairwiseDisjoint : Pairwise (Disjoint on t) := fun x y h =>
  disjoint_sSup_right (ht x) ⟨y, iSup_pos h.symm⟩

@[deprecated (since := "2024-11-24")]
alias CompleteLattice.Independent.pairwiseDisjoint := iSupIndep.pairwiseDisjoint

theorem iSupIndep.mono {s t : ι → α} (hs : iSupIndep s) (hst : t ≤ s) : iSupIndep t :=
  fun i => (hs i).mono (hst i) <| iSup₂_mono fun j _ => hst j

@[deprecated (since := "2024-11-24")] alias CompleteLattice.Independent.mono := iSupIndep.mono

/-- Composing an independent indexed family with an injective function on the index results in
another indepedendent indexed family. -/
theorem iSupIndep.comp {ι ι' : Sort*} {t : ι → α} {f : ι' → ι} (ht : iSupIndep t)
    (hf : Injective f) : iSupIndep (t ∘ f) := fun i =>
  (ht (f i)).mono_right <| by
    refine (iSup_mono fun i => ?_).trans (iSup_comp_le _ f)
    exact iSup_const_mono hf.ne

@[deprecated (since := "2024-11-24")] alias CompleteLattice.Independent.comp := iSupIndep.comp

theorem iSupIndep.comp' {ι ι' : Sort*} {t : ι → α} {f : ι' → ι} (ht : iSupIndep <| t ∘ f)
    (hf : Surjective f) : iSupIndep t := by
  intro i
  obtain ⟨i', rfl⟩ := hf i
  rw [← hf.iSup_comp]
  exact (ht i').mono_right (biSup_mono fun j' hij => mt (congr_arg f) hij)

@[deprecated (since := "2024-11-24")] alias CompleteLattice.Independent.comp' := iSupIndep.comp'

theorem iSupIndep.sSupIndep_range (ht : iSupIndep t) : sSupIndep <| range t := by
  rw [sSupIndep_iff]
  rw [← coe_comp_rangeFactorization t] at ht
  exact ht.comp' surjective_onto_range

@[deprecated (since := "2024-11-24")]
alias CompleteLattice.Independent.setIndependent_range := iSupIndep.sSupIndep_range

@[simp]
theorem iSupIndep_ne_bot :
    iSupIndep (fun i : {i // t i ≠ ⊥} ↦ t i) ↔ iSupIndep t := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp Subtype.val_injective⟩
  simp only [iSupIndep_def] at h ⊢
  intro i
  cases eq_or_ne (t i) ⊥ with
  | inl hi => simp [hi]
  | inr hi => ?_
  convert h ⟨i, hi⟩
  have : ∀ j, ⨆ (_ : t j = ⊥), t j = ⊥ := fun j ↦ by simp only [iSup_eq_bot, imp_self]
  rw [iSup_split _ (fun j ↦ t j = ⊥), iSup_subtype]
  simp only [iSup_comm (ι' := _ ≠ i), this, ne_eq, sup_of_le_right, Subtype.mk.injEq, iSup_bot,
    bot_le]

@[deprecated (since := "2024-11-24")]
alias CompleteLattice.independent_ne_bot_iff_independent := iSupIndep_ne_bot

theorem iSupIndep.injOn (ht : iSupIndep t) : InjOn t {i | t i ≠ ⊥} := by
  rintro i _ j (hj : t j ≠ ⊥) h
  by_contra! contra
  apply hj
  suffices t j ≤ ⨆ (k) (_ : k ≠ i), t k by
    replace ht := (ht i).mono_right this
    rwa [h, disjoint_self] at ht
  replace contra : j ≠ i := Ne.symm contra
  -- Porting note: needs explicit `f`
  exact le_iSup₂ (f := fun x _ ↦ t x) j contra

@[deprecated (since := "2024-11-24")] alias CompleteLattice.Independent.injOn := iSupIndep.injOn

theorem iSupIndep.injective (ht : iSupIndep t) (h_ne_bot : ∀ i, t i ≠ ⊥) : Injective t := by
  suffices univ = {i | t i ≠ ⊥} by rw [injective_iff_injOn_univ, this]; exact ht.injOn
  aesop

@[deprecated (since := "2024-11-24")]
alias CompleteLattice.Independent.injective := iSupIndep.injective

theorem iSupIndep_pair {i j : ι} (hij : i ≠ j) (huniv : ∀ k, k = i ∨ k = j) :
    iSupIndep t ↔ Disjoint (t i) (t j) := by
  constructor
  · exact fun h => h.pairwiseDisjoint hij
  · rintro h k
    obtain rfl | rfl := huniv k
    · refine h.mono_right (iSup_le fun i => iSup_le fun hi => Eq.le ?_)
      rw [(huniv i).resolve_left hi]
    · refine h.symm.mono_right (iSup_le fun j => iSup_le fun hj => Eq.le ?_)
      rw [(huniv j).resolve_right hj]

@[deprecated (since := "2024-11-24")] alias CompleteLattice.independent_pair := iSupIndep_pair

/-- Composing an independent indexed family with an order isomorphism on the elements results in
another independent indexed family. -/
theorem iSupIndep.map_orderIso {ι : Sort*} {α β : Type*} [CompleteLattice α]
    [CompleteLattice β] (f : α ≃o β) {a : ι → α} (ha : iSupIndep a) : iSupIndep (f ∘ a) :=
  fun i => ((ha i).map_orderIso f).mono_right (f.monotone.le_map_iSup₂ _)

@[deprecated (since := "2024-11-24")]
alias CompleteLattice.Independent.map_orderIso := iSupIndep.map_orderIso

@[simp]
theorem iSupIndep_map_orderIso_iff {ι : Sort*} {α β : Type*} [CompleteLattice α]
    [CompleteLattice β] (f : α ≃o β) {a : ι → α} : iSupIndep (f ∘ a) ↔ iSupIndep a :=
  ⟨fun h =>
    have hf : f.symm ∘ f ∘ a = a := congr_arg (· ∘ a) f.left_inv.comp_eq_id
    hf ▸ h.map_orderIso f.symm,
    fun h => h.map_orderIso f⟩

@[deprecated (since := "2024-11-24")]
alias CompleteLattice.independent_map_orderIso_iff := iSupIndep_map_orderIso_iff

/-- If the elements of a set are independent, then any element is disjoint from the `iSup` of some
subset of the rest. -/
theorem iSupIndep.disjoint_biSup {ι : Type*} {α : Type*} [CompleteLattice α] {t : ι → α}
    (ht : iSupIndep t) {x : ι} {y : Set ι} (hx : x ∉ y) : Disjoint (t x) (⨆ i ∈ y, t i) :=
  Disjoint.mono_right (biSup_mono fun _ hi => (ne_of_mem_of_not_mem hi hx :)) (ht x)

@[deprecated (since := "2024-11-24")]
alias CompleteLattice.Independent.disjoint_biSup := iSupIndep.disjoint_biSup

lemma iSupIndep.of_coe_Iic_comp {ι : Sort*} {a : α} {t : ι → Set.Iic a}
    (ht : iSupIndep ((↑) ∘ t : ι → α)) : iSupIndep t := by
  intro i x
  specialize ht i
  simp_rw [Function.comp_apply, ← Set.Iic.coe_iSup] at ht
  exact @ht x

@[deprecated (since := "2024-11-24")]
alias CompleteLattice.independent_of_independent_coe_Iic_comp := iSupIndep.of_coe_Iic_comp

theorem iSupIndep_iff_supIndep {s : Finset ι} {f : ι → α} :
    iSupIndep (f ∘ ((↑) : s → ι)) ↔ s.SupIndep f := by
  classical
    rw [Finset.supIndep_iff_disjoint_erase]
    refine Subtype.forall.trans (forall₂_congr fun a b => ?_)
    rw [Finset.sup_eq_iSup]
    congr! 1
    refine iSup_subtype.trans ?_
    congr! 1
    simp [iSup_and, @iSup_comm _ (_ ∈ s)]

@[deprecated (since := "2024-11-24")]
alias CompleteLattice.independent_iff_supIndep := iSupIndep_iff_supIndep

alias ⟨iSupIndep.supIndep, Finset.SupIndep.independent⟩ := iSupIndep_iff_supIndep

theorem iSupIndep.supIndep' {f : ι → α} (s : Finset ι) (h : iSupIndep f) : s.SupIndep f :=
  iSupIndep.supIndep (h.comp Subtype.coe_injective)

@[deprecated (since := "2024-11-24")]
alias CompleteLattice.Independent.supIndep' := iSupIndep.supIndep'

/-- A variant of `CompleteLattice.iSupIndep_iff_supIndep` for `Fintype`s. -/
theorem iSupIndep_iff_supIndep_univ [Fintype ι] {f : ι → α} :
    iSupIndep f ↔ Finset.univ.SupIndep f := by
  classical
    simp [Finset.supIndep_iff_disjoint_erase, iSupIndep, Finset.sup_eq_iSup]

@[deprecated (since := "2024-11-24")]
alias CompleteLattice.independent_iff_supIndep_univ := iSupIndep_iff_supIndep_univ

alias ⟨iSupIndep.sup_indep_univ, Finset.SupIndep.iSupIndep_of_univ⟩ := iSupIndep_iff_supIndep_univ

end CompleteLattice

section Frame
variable [Order.Frame α]

theorem sSupIndep_iff_pairwiseDisjoint {s : Set α} : sSupIndep s ↔ s.PairwiseDisjoint id :=
  ⟨sSupIndep.pairwiseDisjoint, fun hs _ hi =>
    disjoint_sSup_iff.2 fun _ hj => hs hi hj.1 <| Ne.symm hj.2⟩

@[deprecated (since := "2024-11-24")]
alias setIndependent_iff_pairwiseDisjoint := sSupIndep_iff_pairwiseDisjoint

alias ⟨_, _root_.Set.PairwiseDisjoint.sSupIndep⟩ := sSupIndep_iff_pairwiseDisjoint

open scoped Function in -- required for scoped `on` notation
theorem iSupIndep_iff_pairwiseDisjoint {f : ι → α} : iSupIndep f ↔ Pairwise (Disjoint on f) :=
  ⟨iSupIndep.pairwiseDisjoint, fun hs _ =>
    disjoint_iSup_iff.2 fun _ => disjoint_iSup_iff.2 fun hij => hs hij.symm⟩

@[deprecated (since := "2024-11-24")]
alias independent_iff_pairwiseDisjoint := iSupIndep_iff_pairwiseDisjoint

end Frame
