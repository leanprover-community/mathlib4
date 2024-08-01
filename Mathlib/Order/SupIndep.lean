/-
Copyright (c) 2021 Aaron Anderson, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Kevin Buzzard, Yaël Dillies, Eric Wieser
-/
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Pairwise
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.CompleteLatticeIntervals

/-!
# Supremum independence

In this file, we define supremum independence of indexed sets. An indexed family `f : ι → α` is
sup-independent if, for all `a`, `f a` and the supremum of the rest are disjoint.

## Main definitions

* `Finset.SupIndep s f`: a family of elements `f` are supremum independent on the finite set `s`.
* `CompleteLattice.SetIndependent s`: a set of elements are supremum independent.
* `CompleteLattice.Independent f`: a family of elements are supremum independent.

## Main statements

* In a distributive lattice, supremum independence is equivalent to pairwise disjointness:
  * `Finset.supIndep_iff_pairwiseDisjoint`
  * `CompleteLattice.setIndependent_iff_pairwiseDisjoint`
  * `CompleteLattice.independent_iff_pairwiseDisjoint`
* Otherwise, supremum independence is stronger than pairwise disjointness:
  * `Finset.SupIndep.pairwiseDisjoint`
  * `CompleteLattice.SetIndependent.pairwiseDisjoint`
  * `CompleteLattice.Independent.pairwiseDisjoint`

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

instance [DecidableEq ι] [DecidableEq α] : Decidable (SupIndep s f) := by
  refine @Finset.decidableForallOfDecidableSubsets _ _ _ (?_)
  rintro t -
  refine @Finset.decidableDforallFinset _ _ _ (?_)
  rintro i -
  have : Decidable (Disjoint (f i) (sup t f)) := decidable_of_iff' (_ = ⊥) disjoint_iff
  infer_instance

theorem SupIndep.subset (ht : t.SupIndep f) (h : s ⊆ t) : s.SupIndep f := fun _ hu _ hi =>
  ht (hu.trans h) (h hi)

@[simp]
theorem supIndep_empty (f : ι → α) : (∅ : Finset ι).SupIndep f := fun _ _ a ha =>
  (not_mem_empty a ha).elim

theorem supIndep_singleton (i : ι) (f : ι → α) : ({i} : Finset ι).SupIndep f :=
  fun s hs j hji hj => by
    rw [eq_empty_of_ssubset_singleton ⟨hs, fun h => hj (h hji)⟩, sup_empty]
    exact disjoint_bot_right

theorem SupIndep.pairwiseDisjoint (hs : s.SupIndep f) : (s : Set ι).PairwiseDisjoint f :=
  fun _ ha _ hb hab =>
    sup_singleton.subst <| hs (singleton_subset_iff.2 hb) ha <| not_mem_singleton.2 hab

theorem SupIndep.le_sup_iff (hs : s.SupIndep f) (hts : t ⊆ s) (hi : i ∈ s) (hf : ∀ i, f i ≠ ⊥) :
    f i ≤ t.sup f ↔ i ∈ t := by
  refine ⟨fun h => ?_, le_sup⟩
  by_contra hit
  exact hf i (disjoint_self.1 <| (hs hts hi hit).mono_right h)

/-- The RHS looks like the definition of `CompleteLattice.Independent`. -/
theorem supIndep_iff_disjoint_erase [DecidableEq ι] :
    s.SupIndep f ↔ ∀ i ∈ s, Disjoint (f i) ((s.erase i).sup f) :=
  ⟨fun hs _ hi => hs (erase_subset _ _) hi (not_mem_erase _ _), fun hs _ ht i hi hit =>
    (hs i hi).mono_right (sup_mono fun _ hj => mem_erase.2 ⟨ne_of_mem_of_not_mem hj hit, ht hj⟩)⟩

theorem SupIndep.image [DecidableEq ι] {s : Finset ι'} {g : ι' → ι} (hs : s.SupIndep (f ∘ g)) :
    (s.image g).SupIndep f := by
  intro t ht i hi hit
  rw [mem_image] at hi
  obtain ⟨i, hi, rfl⟩ := hi
  haveI : DecidableEq ι' := Classical.decEq _
  suffices hts : t ⊆ (s.erase i).image g by
    refine (supIndep_iff_disjoint_erase.1 hs i hi).mono_right ((sup_mono hts).trans ?_)
    rw [sup_image]
  rintro j hjt
  obtain ⟨j, hj, rfl⟩ := mem_image.1 (ht hjt)
  exact mem_image_of_mem _ (mem_erase.2 ⟨ne_of_apply_ne g (ne_of_mem_of_not_mem hjt hit), hj⟩)

theorem supIndep_map {s : Finset ι'} {g : ι' ↪ ι} : (s.map g).SupIndep f ↔ s.SupIndep (f ∘ g) := by
  refine ⟨fun hs t ht i hi hit => ?_, fun hs => ?_⟩
  · rw [← sup_map]
    exact hs (map_subset_map.2 ht) ((mem_map' _).2 hi) (by rwa [mem_map'])
  · classical
    rw [map_eq_image]
    exact hs.image

@[simp]
theorem supIndep_pair [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    ({i, j} : Finset ι).SupIndep f ↔ Disjoint (f i) (f j) :=
  ⟨fun h => h.pairwiseDisjoint (by simp) (by simp) hij,
   fun h => by
    rw [supIndep_iff_disjoint_erase]
    intro k hk
    rw [Finset.mem_insert, Finset.mem_singleton] at hk
    obtain rfl | rfl := hk
    · convert h using 1
      rw [Finset.erase_insert, Finset.sup_singleton]
      simpa using hij
    · convert h.symm using 1
      have : ({i, k} : Finset ι).erase k = {i} := by
        ext
        rw [mem_erase, mem_insert, mem_singleton, mem_singleton, and_or_left, Ne,
          not_and_self_iff, or_false_iff, and_iff_right_of_imp]
        rintro rfl
        exact hij
      rw [this, Finset.sup_singleton]⟩

theorem supIndep_univ_bool (f : Bool → α) :
    (Finset.univ : Finset Bool).SupIndep f ↔ Disjoint (f false) (f true) :=
  haveI : true ≠ false := by simp only [Ne, not_false_iff]
  (supIndep_pair this).trans disjoint_comm

@[simp]
theorem supIndep_univ_fin_two (f : Fin 2 → α) :
    (Finset.univ : Finset (Fin 2)).SupIndep f ↔ Disjoint (f 0) (f 1) :=
  haveI : (0 : Fin 2) ≠ 1 := by simp
  supIndep_pair this

theorem SupIndep.attach (hs : s.SupIndep f) : s.attach.SupIndep fun a => f a := by
  intro t _ i _ hi
  classical
    have : (fun (a : { x // x ∈ s }) => f ↑a) = f ∘ (fun a : { x // x ∈ s } => ↑a) := rfl
    rw [this, ← Finset.sup_image]
    refine hs (image_subset_iff.2 fun (j : { x // x ∈ s }) _ => j.2) i.2 fun hi' => hi ?_
    rw [mem_image] at hi'
    obtain ⟨j, hj, hji⟩ := hi'
    rwa [Subtype.ext hji] at hj

/-
Porting note: simpNF linter returns

"Left-hand side does not simplify, when using the simp lemma on itself."

However, simp does indeed solve the following. leanprover/std4#71 is related.

example {α ι} [Lattice α] [OrderBot α] (s : Finset ι) (f : ι → α) :
  (s.attach.SupIndep fun a => f a) ↔ s.SupIndep f := by simp
-/
@[simp, nolint simpNF]
theorem supIndep_attach : (s.attach.SupIndep fun a => f a) ↔ s.SupIndep f := by
  refine ⟨fun h t ht i his hit => ?_, SupIndep.attach⟩
  classical
  convert h (filter_subset (fun (i : { x // x ∈ s }) => (i : ι) ∈ t) _) (mem_attach _ ⟨i, ‹_›⟩)
    fun hi => hit <| by simpa using hi using 1
  refine eq_of_forall_ge_iff ?_
  simp only [Finset.sup_le_iff, mem_filter, mem_attach, true_and_iff, Function.comp_apply,
    Subtype.forall, Subtype.coe_mk]
  exact fun a => forall_congr' fun j => ⟨fun h _ => h, fun h hj => h (ht hj) hj⟩

end Lattice

section DistribLattice

variable [DistribLattice α] [OrderBot α] {s : Finset ι} {f : ι → α}

theorem supIndep_iff_pairwiseDisjoint : s.SupIndep f ↔ (s : Set ι).PairwiseDisjoint f :=
  ⟨SupIndep.pairwiseDisjoint, fun hs _ ht _ hi hit =>
    Finset.disjoint_sup_right.2 fun _ hj => hs hi (ht hj) (ne_of_mem_of_not_mem hj hit).symm⟩

alias ⟨sup_indep.pairwise_disjoint, _root_.Set.PairwiseDisjoint.supIndep⟩ :=
  supIndep_iff_pairwiseDisjoint

/-- Bind operation for `SupIndep`. -/
theorem SupIndep.sup [DecidableEq ι] {s : Finset ι'} {g : ι' → Finset ι} {f : ι → α}
    (hs : s.SupIndep fun i => (g i).sup f) (hg : ∀ i' ∈ s, (g i').SupIndep f) :
    (s.sup g).SupIndep f := by
  simp_rw [supIndep_iff_pairwiseDisjoint] at hs hg ⊢
  rw [sup_eq_biUnion, coe_biUnion]
  exact hs.biUnion_finset hg

/-- Bind operation for `SupIndep`. -/
theorem SupIndep.biUnion [DecidableEq ι] {s : Finset ι'} {g : ι' → Finset ι} {f : ι → α}
    (hs : s.SupIndep fun i => (g i).sup f) (hg : ∀ i' ∈ s, (g i').SupIndep f) :
    (s.biUnion g).SupIndep f := by
  rw [← sup_eq_biUnion]
  exact hs.sup hg

/-- Bind operation for `SupIndep`. -/
theorem SupIndep.sigma {β : ι → Type*} {s : Finset ι} {g : ∀ i, Finset (β i)} {f : Sigma β → α}
    (hs : s.SupIndep fun i => (g i).sup fun b => f ⟨i, b⟩)
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

theorem SupIndep.product {s : Finset ι} {t : Finset ι'} {f : ι × ι' → α}
    (hs : s.SupIndep fun i => t.sup fun i' => f (i, i'))
    (ht : t.SupIndep fun i' => s.sup fun i => f (i, i')) : (s ×ˢ t).SupIndep f := by
  rintro u hu ⟨i, i'⟩ hi hiu
  rw [Finset.disjoint_sup_right]
  rintro ⟨j, j'⟩ hj
  have hij := (ne_of_mem_of_not_mem hj hiu).symm
  replace hj := hu hj
  rw [mem_product] at hi hj
  obtain rfl | hij := eq_or_ne i j
  · refine (ht.pairwiseDisjoint hi.2 hj.2 <| (Prod.mk.inj_left _).ne_iff.1 hij).mono ?_ ?_
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


namespace CompleteLattice

variable [CompleteLattice α]

open Set Function

/-- An independent set of elements in a complete lattice is one in which every element is disjoint
  from the `Sup` of the rest. -/
def SetIndependent (s : Set α) : Prop :=
  ∀ ⦃a⦄, a ∈ s → Disjoint a (sSup (s \ {a}))

variable {s : Set α} (hs : SetIndependent s)

@[simp]
theorem setIndependent_empty : SetIndependent (∅ : Set α) := fun x hx =>
  (Set.not_mem_empty x hx).elim

include hs in
theorem SetIndependent.mono {t : Set α} (hst : t ⊆ s) : SetIndependent t := fun _ ha =>
  (hs (hst ha)).mono_right (sSup_le_sSup (diff_subset_diff_left hst))

include hs in
/-- If the elements of a set are independent, then any pair within that set is disjoint. -/
theorem SetIndependent.pairwiseDisjoint : s.PairwiseDisjoint id := fun _ hx y hy h =>
  disjoint_sSup_right (hs hx) ((mem_diff y).mpr ⟨hy, h.symm⟩)

theorem setIndependent_singleton (a : α) : SetIndependent ({a} : Set α) := fun i hi ↦ by
  simp_all

theorem setIndependent_pair {a b : α} (hab : a ≠ b) :
    SetIndependent ({a, b} : Set α) ↔ Disjoint a b := by
  constructor
  · intro h
    exact h.pairwiseDisjoint (mem_insert _ _) (mem_insert_of_mem _ (mem_singleton _)) hab
  · rintro h c ((rfl : c = a) | (rfl : c = b))
    · convert h using 1
      simp [hab, sSup_singleton]
    · convert h.symm using 1
      simp [hab, sSup_singleton]

include hs in
/-- If the elements of a set are independent, then any element is disjoint from the `sSup` of some
subset of the rest. -/
theorem SetIndependent.disjoint_sSup {x : α} {y : Set α} (hx : x ∈ s) (hy : y ⊆ s) (hxy : x ∉ y) :
    Disjoint x (sSup y) := by
  have := (hs.mono <| insert_subset_iff.mpr ⟨hx, hy⟩) (mem_insert x _)
  rw [insert_diff_of_mem _ (mem_singleton _), diff_singleton_eq_self hxy] at this
  exact this

/-- An independent indexed family of elements in a complete lattice is one in which every element
  is disjoint from the `iSup` of the rest.

  Example: an indexed family of non-zero elements in a
  vector space is linearly independent iff the indexed family of subspaces they generate is
  independent in this sense.

  Example: an indexed family of submodules of a module is independent in this sense if
  and only the natural map from the direct sum of the submodules to the module is injective. -/
def Independent {ι : Sort*} {α : Type*} [CompleteLattice α] (t : ι → α) : Prop :=
  ∀ i : ι, Disjoint (t i) (⨆ (j) (_ : j ≠ i), t j)

theorem setIndependent_iff {α : Type*} [CompleteLattice α] (s : Set α) :
    SetIndependent s ↔ Independent ((↑) : s → α) := by
  simp_rw [Independent, SetIndependent, SetCoe.forall, sSup_eq_iSup]
  refine forall₂_congr fun a ha => ?_
  simp [iSup_subtype, iSup_and]

variable {t : ι → α} (ht : Independent t)

theorem independent_def : Independent t ↔ ∀ i : ι, Disjoint (t i) (⨆ (j) (_ : j ≠ i), t j) :=
  Iff.rfl

theorem independent_def' : Independent t ↔ ∀ i, Disjoint (t i) (sSup (t '' { j | j ≠ i })) := by
  simp_rw [sSup_image]
  rfl

theorem independent_def'' :
    Independent t ↔ ∀ i, Disjoint (t i) (sSup { a | ∃ j ≠ i, t j = a }) := by
  rw [independent_def']
  aesop

@[simp]
theorem independent_empty (t : Empty → α) : Independent t :=
  nofun

@[simp]
theorem independent_pempty (t : PEmpty → α) : Independent t :=
  nofun

include ht in
/-- If the elements of a set are independent, then any pair within that set is disjoint. -/
theorem Independent.pairwiseDisjoint : Pairwise (Disjoint on t) := fun x y h =>
  disjoint_sSup_right (ht x) ⟨y, iSup_pos h.symm⟩

theorem Independent.mono {s t : ι → α} (hs : Independent s) (hst : t ≤ s) : Independent t :=
  fun i => (hs i).mono (hst i) <| iSup₂_mono fun j _ => hst j

/-- Composing an independent indexed family with an injective function on the index results in
another indepedendent indexed family. -/
theorem Independent.comp {ι ι' : Sort*} {t : ι → α} {f : ι' → ι} (ht : Independent t)
    (hf : Injective f) : Independent (t ∘ f) := fun i =>
  (ht (f i)).mono_right <| by
    refine (iSup_mono fun i => ?_).trans (iSup_comp_le _ f)
    exact iSup_const_mono hf.ne

theorem Independent.comp' {ι ι' : Sort*} {t : ι → α} {f : ι' → ι} (ht : Independent <| t ∘ f)
    (hf : Surjective f) : Independent t := by
  intro i
  obtain ⟨i', rfl⟩ := hf i
  rw [← hf.iSup_comp]
  exact (ht i').mono_right (biSup_mono fun j' hij => mt (congr_arg f) hij)

theorem Independent.setIndependent_range (ht : Independent t) : SetIndependent <| range t := by
  rw [setIndependent_iff]
  rw [← coe_comp_rangeFactorization t] at ht
  exact ht.comp' surjective_onto_range

@[simp]
theorem independent_ne_bot_iff_independent :
    Independent (fun i : {i // t i ≠ ⊥} ↦ t i) ↔ Independent t := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp Subtype.val_injective⟩
  simp only [independent_def] at h ⊢
  intro i
  cases eq_or_ne (t i) ⊥ with
  | inl hi => simp [hi]
  | inr hi => ?_
  convert h ⟨i, hi⟩
  have : ∀ j, ⨆ (_ : t j = ⊥), t j = ⊥ := fun j ↦ by simp only [iSup_eq_bot, imp_self]
  rw [iSup_split _ (fun j ↦ t j = ⊥), iSup_subtype]
  simp only [iSup_comm (ι' := _ ≠ i), this, ne_eq, sup_of_le_right, Subtype.mk.injEq, iSup_bot,
    bot_le]

theorem Independent.injOn (ht : Independent t) : InjOn t {i | t i ≠ ⊥} := by
  rintro i _ j (hj : t j ≠ ⊥) h
  by_contra! contra
  apply hj
  suffices t j ≤ ⨆ (k) (_ : k ≠ i), t k by
    replace ht := (ht i).mono_right this
    rwa [h, disjoint_self] at ht
  replace contra : j ≠ i := Ne.symm contra
  -- Porting note: needs explicit `f`
  exact le_iSup₂ (f := fun x _ ↦ t x) j contra

theorem Independent.injective (ht : Independent t) (h_ne_bot : ∀ i, t i ≠ ⊥) : Injective t := by
  suffices univ = {i | t i ≠ ⊥} by rw [injective_iff_injOn_univ, this]; exact ht.injOn
  aesop

theorem independent_pair {i j : ι} (hij : i ≠ j) (huniv : ∀ k, k = i ∨ k = j) :
    Independent t ↔ Disjoint (t i) (t j) := by
  constructor
  · exact fun h => h.pairwiseDisjoint hij
  · rintro h k
    obtain rfl | rfl := huniv k
    · refine h.mono_right (iSup_le fun i => iSup_le fun hi => Eq.le ?_)
      rw [(huniv i).resolve_left hi]
    · refine h.symm.mono_right (iSup_le fun j => iSup_le fun hj => Eq.le ?_)
      rw [(huniv j).resolve_right hj]

/-- Composing an independent indexed family with an order isomorphism on the elements results in
another independent indexed family. -/
theorem Independent.map_orderIso {ι : Sort*} {α β : Type*} [CompleteLattice α]
    [CompleteLattice β] (f : α ≃o β) {a : ι → α} (ha : Independent a) : Independent (f ∘ a) :=
  fun i => ((ha i).map_orderIso f).mono_right (f.monotone.le_map_iSup₂ _)

@[simp]
theorem independent_map_orderIso_iff {ι : Sort*} {α β : Type*} [CompleteLattice α]
    [CompleteLattice β] (f : α ≃o β) {a : ι → α} : Independent (f ∘ a) ↔ Independent a :=
  ⟨fun h =>
    have hf : f.symm ∘ f ∘ a = a := congr_arg (· ∘ a) f.left_inv.comp_eq_id
    hf ▸ h.map_orderIso f.symm,
    fun h => h.map_orderIso f⟩

/-- If the elements of a set are independent, then any element is disjoint from the `iSup` of some
subset of the rest. -/
theorem Independent.disjoint_biSup {ι : Type*} {α : Type*} [CompleteLattice α] {t : ι → α}
    (ht : Independent t) {x : ι} {y : Set ι} (hx : x ∉ y) : Disjoint (t x) (⨆ i ∈ y, t i) :=
  Disjoint.mono_right (biSup_mono fun _ hi => (ne_of_mem_of_not_mem hi hx : _)) (ht x)

lemma independent_of_independent_coe_Iic_comp {ι : Sort*} {a : α} {t : ι → Set.Iic a}
    (ht : Independent ((↑) ∘ t : ι → α)) : Independent t := by
  intro i x
  specialize ht i
  simp_rw [Function.comp_apply, ← Set.Iic.coe_iSup] at ht
  exact @ht x

end CompleteLattice

theorem CompleteLattice.independent_iff_supIndep [CompleteLattice α] {s : Finset ι} {f : ι → α} :
    CompleteLattice.Independent (f ∘ ((↑) : s → ι)) ↔ s.SupIndep f := by
  classical
    rw [Finset.supIndep_iff_disjoint_erase]
    refine Subtype.forall.trans (forall₂_congr fun a b => ?_)
    rw [Finset.sup_eq_iSup]
    congr! 1
    refine iSup_subtype.trans ?_
    congr! 1
    simp [iSup_and, @iSup_comm _ (_ ∈ s)]

alias ⟨CompleteLattice.Independent.supIndep, Finset.SupIndep.independent⟩ :=
  CompleteLattice.independent_iff_supIndep

theorem CompleteLattice.Independent.supIndep' [CompleteLattice α] {f : ι → α} (s : Finset ι)
    (h : CompleteLattice.Independent f) : s.SupIndep f :=
  CompleteLattice.Independent.supIndep (h.comp Subtype.coe_injective)

/-- A variant of `CompleteLattice.independent_iff_supIndep` for `Fintype`s. -/
theorem CompleteLattice.independent_iff_supIndep_univ [CompleteLattice α] [Fintype ι] {f : ι → α} :
    CompleteLattice.Independent f ↔ Finset.univ.SupIndep f := by
  classical
    simp [Finset.supIndep_iff_disjoint_erase, CompleteLattice.Independent, Finset.sup_eq_iSup]

alias ⟨CompleteLattice.Independent.sup_indep_univ, Finset.SupIndep.independent_of_univ⟩ :=
  CompleteLattice.independent_iff_supIndep_univ

section Frame

namespace CompleteLattice

variable [Order.Frame α]

theorem setIndependent_iff_pairwiseDisjoint {s : Set α} :
    SetIndependent s ↔ s.PairwiseDisjoint id :=
  ⟨SetIndependent.pairwiseDisjoint, fun hs _ hi =>
    disjoint_sSup_iff.2 fun _ hj => hs hi hj.1 <| Ne.symm hj.2⟩

alias ⟨_, _root_.Set.PairwiseDisjoint.setIndependent⟩ := setIndependent_iff_pairwiseDisjoint

theorem independent_iff_pairwiseDisjoint {f : ι → α} : Independent f ↔ Pairwise (Disjoint on f) :=
  ⟨Independent.pairwiseDisjoint, fun hs _ =>
    disjoint_iSup_iff.2 fun _ => disjoint_iSup_iff.2 fun hij => hs hij.symm⟩

end CompleteLattice

end Frame
