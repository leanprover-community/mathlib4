/-
Copyright (c) 2021 Aaron Anderson, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Kevin Buzzard, Yaël Dillies, Eric Wieser

! This file was ported from Lean 3 source module order.sup_indep
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Pairwise
import Mathbin.Data.Finset.Powerset
import Mathbin.Data.Fintype.Basic

/-!
# Supremum independence

In this file, we define supremum independence of indexed sets. An indexed family `f : ι → α` is
sup-independent if, for all `a`, `f a` and the supremum of the rest are disjoint.

## Main definitions

* `finset.sup_indep s f`: a family of elements `f` are supremum independent on the finite set `s`.
* `complete_lattice.set_independent s`: a set of elements are supremum independent.
* `complete_lattice.independent f`: a family of elements are supremum independent.

## Main statements

* In a distributive lattice, supremum independence is equivalent to pairwise disjointness:
  * `finset.sup_indep_iff_pairwise_disjoint`
  * `complete_lattice.set_independent_iff_pairwise_disjoint`
  * `complete_lattice.independent_iff_pairwise_disjoint`
* Otherwise, supremum independence is stronger than pairwise disjointness:
  * `finset.sup_indep.pairwise_disjoint`
  * `complete_lattice.set_independent.pairwise_disjoint`
  * `complete_lattice.independent.pairwise_disjoint`

## Implementation notes

For the finite version, we avoid the "obvious" definition
`∀ i ∈ s, disjoint (f i) ((s.erase i).sup f)` because `erase` would require decidable equality on
`ι`.
-/


variable {α β ι ι' : Type _}

/-! ### On lattices with a bottom element, via `finset.sup` -/


namespace Finset

section Lattice

variable [Lattice α] [OrderBot α]

/-- Supremum independence of finite sets. We avoid the "obvious" definition using `s.erase i`
because `erase` would require decidable equality on `ι`. -/
def SupIndep (s : Finset ι) (f : ι → α) : Prop :=
  ∀ ⦃t⦄, t ⊆ s → ∀ ⦃i⦄, i ∈ s → i ∉ t → Disjoint (f i) (t.sup f)
#align finset.sup_indep Finset.SupIndep

variable {s t : Finset ι} {f : ι → α} {i : ι}

instance [DecidableEq ι] [DecidableEq α] : Decidable (SupIndep s f) :=
  by
  apply @Finset.decidableForallOfDecidableSubsets _ _ _ _
  intro t ht
  apply @Finset.decidableDforallFinset _ _ _ _
  exact fun i hi => @Implies.decidable _ _ _ (decidable_of_iff' (_ = ⊥) disjoint_iff)

theorem SupIndep.subset (ht : t.SupIndep f) (h : s ⊆ t) : s.SupIndep f := fun u hu i hi =>
  ht (hu.trans h) (h hi)
#align finset.sup_indep.subset Finset.SupIndep.subset

theorem sup_indep_empty (f : ι → α) : (∅ : Finset ι).SupIndep f := fun _ _ a ha => ha.elim
#align finset.sup_indep_empty Finset.sup_indep_empty

theorem sup_indep_singleton (i : ι) (f : ι → α) : ({i} : Finset ι).SupIndep f :=
  fun s hs j hji hj =>
  by
  rw [eq_empty_of_ssubset_singleton ⟨hs, fun h => hj (h hji)⟩, sup_empty]
  exact disjoint_bot_right
#align finset.sup_indep_singleton Finset.sup_indep_singleton

theorem SupIndep.pairwise_disjoint (hs : s.SupIndep f) : (s : Set ι).PairwiseDisjoint f :=
  fun a ha b hb hab =>
  sup_singleton.subst <| hs (singleton_subset_iff.2 hb) ha <| not_mem_singleton.2 hab
#align finset.sup_indep.pairwise_disjoint Finset.SupIndep.pairwise_disjoint

/-- The RHS looks like the definition of `complete_lattice.independent`. -/
theorem sup_indep_iff_disjoint_erase [DecidableEq ι] :
    s.SupIndep f ↔ ∀ i ∈ s, Disjoint (f i) ((s.erase i).sup f) :=
  ⟨fun hs i hi => hs (erase_subset _ _) hi (not_mem_erase _ _), fun hs t ht i hi hit =>
    (hs i hi).mono_right (sup_mono fun j hj => mem_erase.2 ⟨ne_of_mem_of_not_mem hj hit, ht hj⟩)⟩
#align finset.sup_indep_iff_disjoint_erase Finset.sup_indep_iff_disjoint_erase

@[simp]
theorem sup_indep_pair [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    ({i, j} : Finset ι).SupIndep f ↔ Disjoint (f i) (f j) :=
  ⟨fun h => h.PairwiseDisjoint (by simp) (by simp) hij, fun h =>
    by
    rw [sup_indep_iff_disjoint_erase]
    intro k hk
    rw [Finset.mem_insert, Finset.mem_singleton] at hk
    obtain rfl | rfl := hk
    · convert h using 1
      rw [Finset.erase_insert, Finset.sup_singleton]
      simpa using hij
    · convert h.symm using 1
      have : ({i, k} : Finset ι).erase k = {i} := by
        ext
        rw [mem_erase, mem_insert, mem_singleton, mem_singleton, and_or_left, Ne.def,
          not_and_self_iff, or_false_iff, and_iff_right_of_imp]
        rintro rfl
        exact hij
      rw [this, Finset.sup_singleton]⟩
#align finset.sup_indep_pair Finset.sup_indep_pair

theorem sup_indep_univ_bool (f : Bool → α) :
    (Finset.univ : Finset Bool).SupIndep f ↔ Disjoint (f false) (f true) :=
  haveI : tt ≠ ff := by simp only [Ne.def, not_false_iff]
  (sup_indep_pair this).trans disjoint_comm
#align finset.sup_indep_univ_bool Finset.sup_indep_univ_bool

@[simp]
theorem sup_indep_univ_fin_two (f : Fin 2 → α) :
    (Finset.univ : Finset (Fin 2)).SupIndep f ↔ Disjoint (f 0) (f 1) :=
  haveI : (0 : Fin 2) ≠ 1 := by simp
  sup_indep_pair this
#align finset.sup_indep_univ_fin_two Finset.sup_indep_univ_fin_two

theorem SupIndep.attach (hs : s.SupIndep f) : s.attach.SupIndep (f ∘ Subtype.val) :=
  by
  intro t ht i _ hi
  classical
    rw [← Finset.sup_image]
    refine' hs (image_subset_iff.2 fun (j : { x // x ∈ s }) _ => j.2) i.2 fun hi' => hi _
    rw [mem_image] at hi'
    obtain ⟨j, hj, hji⟩ := hi'
    rwa [Subtype.ext hji] at hj
#align finset.sup_indep.attach Finset.SupIndep.attach

end Lattice

section DistribLattice

variable [DistribLattice α] [OrderBot α] {s : Finset ι} {f : ι → α}

theorem sup_indep_iff_pairwise_disjoint : s.SupIndep f ↔ (s : Set ι).PairwiseDisjoint f :=
  ⟨SupIndep.pairwise_disjoint, fun hs t ht i hi hit =>
    disjoint_sup_right.2 fun j hj => hs hi (ht hj) (ne_of_mem_of_not_mem hj hit).symm⟩
#align finset.sup_indep_iff_pairwise_disjoint Finset.sup_indep_iff_pairwise_disjoint

alias sup_indep_iff_pairwise_disjoint ↔
  sup_indep.pairwise_disjoint _root_.set.pairwise_disjoint.sup_indep
#align finset.sup_indep.pairwise_disjoint Finset.SupIndep.pairwise_disjoint
#align set.pairwise_disjoint.sup_indep Set.PairwiseDisjoint.sup_indep

/-- Bind operation for `sup_indep`. -/
theorem SupIndep.sup [DecidableEq ι] {s : Finset ι'} {g : ι' → Finset ι} {f : ι → α}
    (hs : s.SupIndep fun i => (g i).sup f) (hg : ∀ i' ∈ s, (g i').SupIndep f) :
    (s.sup g).SupIndep f :=
  by
  simp_rw [sup_indep_iff_pairwise_disjoint] at hs hg⊢
  rw [sup_eq_bUnion, coe_bUnion]
  exact hs.bUnion_finset hg
#align finset.sup_indep.sup Finset.SupIndep.sup

/-- Bind operation for `sup_indep`. -/
theorem SupIndep.bUnion [DecidableEq ι] {s : Finset ι'} {g : ι' → Finset ι} {f : ι → α}
    (hs : s.SupIndep fun i => (g i).sup f) (hg : ∀ i' ∈ s, (g i').SupIndep f) :
    (s.bUnion g).SupIndep f := by
  rw [← sup_eq_bUnion]
  exact hs.sup hg
#align finset.sup_indep.bUnion Finset.SupIndep.bUnion

end DistribLattice

end Finset

/-! ### On complete lattices via `has_Sup.Sup` -/


namespace CompleteLattice

variable [CompleteLattice α]

open Set Function

/-- An independent set of elements in a complete lattice is one in which every element is disjoint
  from the `Sup` of the rest. -/
def SetIndependent (s : Set α) : Prop :=
  ∀ ⦃a⦄, a ∈ s → Disjoint a (supₛ (s \ {a}))
#align complete_lattice.set_independent CompleteLattice.SetIndependent

variable {s : Set α} (hs : SetIndependent s)

@[simp]
theorem set_independent_empty : SetIndependent (∅ : Set α) := fun x hx =>
  (Set.not_mem_empty x hx).elim
#align complete_lattice.set_independent_empty CompleteLattice.set_independent_empty

theorem SetIndependent.mono {t : Set α} (hst : t ⊆ s) : SetIndependent t := fun a ha =>
  (hs (hst ha)).mono_right (supₛ_le_supₛ (diff_subset_diff_left hst))
#align complete_lattice.set_independent.mono CompleteLattice.SetIndependent.mono

/-- If the elements of a set are independent, then any pair within that set is disjoint. -/
theorem SetIndependent.pairwise_disjoint : s.PairwiseDisjoint id := fun x hx y hy h =>
  disjoint_supₛ_right (hs hx) ((mem_diff y).mpr ⟨hy, h.symm⟩)
#align
  complete_lattice.set_independent.pairwise_disjoint CompleteLattice.SetIndependent.pairwise_disjoint

theorem set_independent_pair {a b : α} (hab : a ≠ b) :
    SetIndependent ({a, b} : Set α) ↔ Disjoint a b :=
  by
  constructor
  · intro h
    exact h.pairwise_disjoint (mem_insert _ _) (mem_insert_of_mem _ (mem_singleton _)) hab
  · rintro h c ((rfl : c = a) | (rfl : c = b))
    · convert h using 1
      simp [hab, supₛ_singleton]
    · convert h.symm using 1
      simp [hab, supₛ_singleton]
#align complete_lattice.set_independent_pair CompleteLattice.set_independent_pair

include hs

/-- If the elements of a set are independent, then any element is disjoint from the `Sup` of some
subset of the rest. -/
theorem SetIndependent.disjoint_Sup {x : α} {y : Set α} (hx : x ∈ s) (hy : y ⊆ s) (hxy : x ∉ y) :
    Disjoint x (supₛ y) :=
  by
  have := (hs.mono <| insert_subset.mpr ⟨hx, hy⟩) (mem_insert x _)
  rw [insert_diff_of_mem _ (mem_singleton _), diff_singleton_eq_self hxy] at this
  exact this
#align complete_lattice.set_independent.disjoint_Sup CompleteLattice.SetIndependent.disjoint_Sup

omit hs

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (j «expr ≠ » i) -/
/-- An independent indexed family of elements in a complete lattice is one in which every element
  is disjoint from the `supr` of the rest.

  Example: an indexed family of non-zero elements in a
  vector space is linearly independent iff the indexed family of subspaces they generate is
  independent in this sense.

  Example: an indexed family of submodules of a module is independent in this sense if
  and only the natural map from the direct sum of the submodules to the module is injective. -/
def Independent {ι : Sort _} {α : Type _} [CompleteLattice α] (t : ι → α) : Prop :=
  ∀ i : ι, Disjoint (t i) (⨆ (j) (_ : j ≠ i), t j)
#align complete_lattice.independent CompleteLattice.Independent

theorem set_independent_iff {α : Type _} [CompleteLattice α] (s : Set α) :
    SetIndependent s ↔ Independent (coe : s → α) :=
  by
  simp_rw [independent, set_independent, SetCoe.forall, supₛ_eq_supᵢ]
  refine' forall₂_congr fun a ha => _
  congr 2
  convert supr_subtype.symm
  simp [supᵢ_and]
#align complete_lattice.set_independent_iff CompleteLattice.set_independent_iff

variable {t : ι → α} (ht : Independent t)

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (j «expr ≠ » i) -/
theorem independent_def : Independent t ↔ ∀ i : ι, Disjoint (t i) (⨆ (j) (_ : j ≠ i), t j) :=
  Iff.rfl
#align complete_lattice.independent_def CompleteLattice.independent_def

theorem independent_def' : Independent t ↔ ∀ i, Disjoint (t i) (supₛ (t '' { j | j ≠ i })) :=
  by
  simp_rw [supₛ_image]
  rfl
#align complete_lattice.independent_def' CompleteLattice.independent_def'

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (j «expr ≠ » i) -/
theorem independent_def'' :
    Independent t ↔ ∀ i, Disjoint (t i) (supₛ { a | ∃ (j : _)(_ : j ≠ i), t j = a }) :=
  by
  rw [independent_def']
  tidy
#align complete_lattice.independent_def'' CompleteLattice.independent_def''

@[simp]
theorem independent_empty (t : Empty → α) : Independent t :=
  fun.
#align complete_lattice.independent_empty CompleteLattice.independent_empty

@[simp]
theorem independent_pempty (t : PEmpty → α) : Independent t :=
  fun.
#align complete_lattice.independent_pempty CompleteLattice.independent_pempty

/-- If the elements of a set are independent, then any pair within that set is disjoint. -/
theorem Independent.pairwise_disjoint : Pairwise (Disjoint on t) := fun x y h =>
  disjoint_supₛ_right (ht x) ⟨y, supᵢ_pos h.symm⟩
#align complete_lattice.independent.pairwise_disjoint CompleteLattice.Independent.pairwise_disjoint

theorem Independent.mono {s t : ι → α} (hs : Independent s) (hst : t ≤ s) : Independent t :=
  fun i => (hs i).mono (hst i) <| supᵢ₂_mono fun j _ => hst j
#align complete_lattice.independent.mono CompleteLattice.Independent.mono

/-- Composing an independent indexed family with an injective function on the index results in
another indepedendent indexed family. -/
theorem Independent.comp {ι ι' : Sort _} {t : ι → α} {f : ι' → ι} (ht : Independent t)
    (hf : Injective f) : Independent (t ∘ f) := fun i =>
  (ht (f i)).mono_right <|
    by
    refine' (supᵢ_mono fun i => _).trans (supᵢ_comp_le _ f)
    exact supᵢ_const_mono hf.ne
#align complete_lattice.independent.comp CompleteLattice.Independent.comp

theorem Independent.comp' {ι ι' : Sort _} {t : ι → α} {f : ι' → ι} (ht : independent <| t ∘ f)
    (hf : Surjective f) : Independent t := by
  intro i
  obtain ⟨i', rfl⟩ := hf i
  rw [← hf.supr_comp]
  exact (ht i').mono_right (bsupᵢ_mono fun j' hij => mt (congr_arg f) hij)
#align complete_lattice.independent.comp' CompleteLattice.Independent.comp'

theorem Independent.set_independent_range (ht : Independent t) : set_independent <| range t :=
  by
  rw [set_independent_iff]
  rw [← coe_comp_range_factorization t] at ht
  exact ht.comp' surjective_onto_range
#align
  complete_lattice.independent.set_independent_range CompleteLattice.Independent.set_independent_range

theorem Independent.injective (ht : Independent t) (h_ne_bot : ∀ i, t i ≠ ⊥) : Injective t :=
  by
  intro i j h
  by_contra' contra
  apply h_ne_bot j
  suffices t j ≤ ⨆ (k) (hk : k ≠ i), t k
    by
    replace ht := (ht i).mono_right this
    rwa [h, disjoint_self] at ht
  replace contra : j ≠ i
  · exact Ne.symm contra
  exact le_supᵢ₂ j contra
#align complete_lattice.independent.injective CompleteLattice.Independent.injective

theorem independent_pair {i j : ι} (hij : i ≠ j) (huniv : ∀ k, k = i ∨ k = j) :
    Independent t ↔ Disjoint (t i) (t j) := by
  constructor
  · exact fun h => h.PairwiseDisjoint hij
  · rintro h k
    obtain rfl | rfl := huniv k
    · refine' h.mono_right (supᵢ_le fun i => supᵢ_le fun hi => Eq.le _)
      rw [(huniv i).resolve_left hi]
    · refine' h.symm.mono_right (supᵢ_le fun j => supᵢ_le fun hj => Eq.le _)
      rw [(huniv j).resolve_right hj]
#align complete_lattice.independent_pair CompleteLattice.independent_pair

/-- Composing an indepedent indexed family with an order isomorphism on the elements results in
another indepedendent indexed family. -/
theorem Independent.map_order_iso {ι : Sort _} {α β : Type _} [CompleteLattice α]
    [CompleteLattice β] (f : α ≃o β) {a : ι → α} (ha : Independent a) : Independent (f ∘ a) :=
  fun i => ((ha i).map_order_iso f).mono_right (f.Monotone.le_map_supr₂ _)
#align complete_lattice.independent.map_order_iso CompleteLattice.Independent.map_order_iso

@[simp]
theorem independent_map_order_iso_iff {ι : Sort _} {α β : Type _} [CompleteLattice α]
    [CompleteLattice β] (f : α ≃o β) {a : ι → α} : Independent (f ∘ a) ↔ Independent a :=
  ⟨fun h =>
    have hf : f.symm ∘ f ∘ a = a := congr_arg (· ∘ a) f.left_inv.comp_eq_id
    hf ▸ h.map_order_iso f.symm,
    fun h => h.map_order_iso f⟩
#align complete_lattice.independent_map_order_iso_iff CompleteLattice.independent_map_order_iso_iff

/-- If the elements of a set are independent, then any element is disjoint from the `supr` of some
subset of the rest. -/
theorem Independent.disjoint_bsupr {ι : Type _} {α : Type _} [CompleteLattice α] {t : ι → α}
    (ht : Independent t) {x : ι} {y : Set ι} (hx : x ∉ y) : Disjoint (t x) (⨆ i ∈ y, t i) :=
  Disjoint.mono_right (bsupᵢ_mono fun i hi => (ne_of_mem_of_not_mem hi hx : _)) (ht x)
#align complete_lattice.independent.disjoint_bsupr CompleteLattice.Independent.disjoint_bsupr

end CompleteLattice

theorem CompleteLattice.independent_iff_sup_indep [CompleteLattice α] {s : Finset ι} {f : ι → α} :
    CompleteLattice.Independent (f ∘ (coe : s → ι)) ↔ s.SupIndep f := by
  classical
    rw [Finset.sup_indep_iff_disjoint_erase]
    refine' subtype.forall.trans (forall₂_congr fun a b => _)
    rw [Finset.sup_eq_supr]
    congr 2
    refine' supr_subtype.trans _
    congr 1 with x
    simp [supᵢ_and, @supᵢ_comm _ (x ∈ s)]
#align complete_lattice.independent_iff_sup_indep CompleteLattice.independent_iff_sup_indep

alias CompleteLattice.independent_iff_sup_indep ↔
  CompleteLattice.Independent.sup_indep Finset.SupIndep.independent
#align complete_lattice.independent.sup_indep CompleteLattice.Independent.sup_indep
#align finset.sup_indep.independent Finset.SupIndep.independent

/-- A variant of `complete_lattice.independent_iff_sup_indep` for `fintype`s. -/
theorem CompleteLattice.independent_iff_sup_indep_univ [CompleteLattice α] [Fintype ι] {f : ι → α} :
    CompleteLattice.Independent f ↔ Finset.univ.SupIndep f := by
  classical simp [Finset.sup_indep_iff_disjoint_erase, CompleteLattice.Independent,
      Finset.sup_eq_supr]
#align
  complete_lattice.independent_iff_sup_indep_univ CompleteLattice.independent_iff_sup_indep_univ

alias CompleteLattice.independent_iff_sup_indep_univ ↔
  CompleteLattice.Independent.sup_indep_univ Finset.SupIndep.independent_of_univ
#align complete_lattice.independent.sup_indep_univ CompleteLattice.Independent.sup_indep_univ
#align finset.sup_indep.independent_of_univ Finset.SupIndep.independent_of_univ

section Frame

namespace CompleteLattice

variable [Order.Frame α]

theorem set_independent_iff_pairwise_disjoint {s : Set α} :
    SetIndependent s ↔ s.PairwiseDisjoint id :=
  ⟨SetIndependent.pairwise_disjoint, fun hs i hi =>
    disjoint_supₛ_iff.2 fun j hj => hs hi hj.1 <| Ne.symm hj.2⟩
#align
  complete_lattice.set_independent_iff_pairwise_disjoint CompleteLattice.set_independent_iff_pairwise_disjoint

alias set_independent_iff_pairwise_disjoint ↔ _ _root_.set.pairwise_disjoint.set_independent
#align set.pairwise_disjoint.set_independent Set.PairwiseDisjoint.set_independent

theorem independent_iff_pairwise_disjoint {f : ι → α} : Independent f ↔ Pairwise (Disjoint on f) :=
  ⟨Independent.pairwise_disjoint, fun hs i =>
    disjoint_supᵢ_iff.2 fun j => disjoint_supᵢ_iff.2 fun hij => hs hij.symm⟩
#align
  complete_lattice.independent_iff_pairwise_disjoint CompleteLattice.independent_iff_pairwise_disjoint

end CompleteLattice

end Frame

