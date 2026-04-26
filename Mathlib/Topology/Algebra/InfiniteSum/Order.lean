/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Infinite sum or product in an order

This file provides lemmas about the interaction of infinite sums and products and order operations.
-/

public section

open Finset Filter Function

variable {ι κ α : Type*} {L : SummationFilter ι}

section Preorder

variable [Preorder α] [CommMonoid α] [TopologicalSpace α] {a c : α} {f : ι → α}

@[to_additive]
lemma hasProd_le_of_prod_le [ClosedIicTopology α] [L.NeBot]
    (hf : HasProd f a L) (h : ∀ s, ∏ i ∈ s, f i ≤ c) : a ≤ c :=
  le_of_tendsto' hf h

@[to_additive]
theorem le_hasProd_of_le_prod [ClosedIciTopology α] [L.NeBot]
    (hf : HasProd f a L) (h : ∀ s, c ≤ ∏ i ∈ s, f i) : c ≤ a :=
  ge_of_tendsto' hf h

@[to_additive]
protected theorem Multipliable.tprod_le_of_prod_range_le [ClosedIicTopology α] {f : ℕ → α}
    (hf : Multipliable f) (h : ∀ n, ∏ i ∈ range n, f i ≤ c) : ∏' n, f n ≤ c :=
  le_of_tendsto' hf.hasProd.tendsto_prod_nat h

end Preorder

section OrderedCommMonoid

variable [CommMonoid α] [Preorder α] [IsOrderedMonoid α]
  [TopologicalSpace α] [OrderClosedTopology α] {f g : ι → α}
  {a a₁ a₂ : α}

@[to_additive]
theorem hasProd_le (h : ∀ i, f i ≤ g i) (hf : HasProd f a₁ L) (hg : HasProd g a₂ L) [L.NeBot] :
    a₁ ≤ a₂ :=
  le_of_tendsto_of_tendsto' hf hg fun _ ↦ prod_le_prod' fun i _ ↦ h i

@[to_additive]
theorem hasProd_mono (hf : HasProd f a₁ L) (hg : HasProd g a₂ L) (h : f ≤ g) [L.NeBot] : a₁ ≤ a₂ :=
  hasProd_le h hf hg

@[to_additive]
theorem hasProd_le_inj {g : κ → α} (e : ι → κ) (he : Injective e)
    (hs : ∀ c, c ∉ Set.range e → 1 ≤ g c) (h : ∀ i, f i ≤ g (e i)) (hf : HasProd f a₁)
    (hg : HasProd g a₂) : a₁ ≤ a₂ := by
  rw [← hasProd_extend_one he] at hf
  refine hasProd_le (fun c ↦ ?_) hf hg
  obtain ⟨i, rfl⟩ | h := em (c ∈ Set.range e)
  · rw [he.extend_apply]
    exact h _
  · rw [extend_apply' _ _ _ h]
    exact hs _ h

@[to_additive]
protected theorem Multipliable.tprod_le_tprod_of_inj {g : κ → α} (e : ι → κ) (he : Injective e)
    (hs : ∀ c, c ∉ Set.range e → 1 ≤ g c) (h : ∀ i, f i ≤ g (e i)) (hf : Multipliable f)
    (hg : Multipliable g) : tprod f ≤ tprod g :=
  hasProd_le_inj _ he hs h hf.hasProd hg.hasProd

@[to_additive]
protected lemma Multipliable.tprod_subtype_le {κ γ : Type*} [CommGroup γ] [PartialOrder γ]
    [IsOrderedMonoid γ] [UniformSpace γ] [IsUniformGroup γ] [OrderClosedTopology γ]
    [CompleteSpace γ] (f : κ → γ) (β : Set κ) (h : ∀ a : κ, 1 ≤ f a) (hf : Multipliable f) :
    (∏' (b : β), f b) ≤ (∏' (a : κ), f a) := by
  apply Multipliable.tprod_le_tprod_of_inj _
    (Subtype.coe_injective)
    (by simp only [Subtype.range_coe_subtype, Set.setOf_mem_eq, h, implies_true])
    (by simp only [le_refl, implies_true])
    (by apply hf.subtype)
  apply hf

@[to_additive]
theorem prod_le_hasProd [L.NeBot] [L.LeAtTop] (s : Finset ι) (hs : ∀ i, i ∉ s → 1 ≤ f i)
    (hf : HasProd f a L) : ∏ i ∈ s, f i ≤ a := by
  refine ge_of_tendsto hf <| .filter_mono L.le_atTop <| eventually_atTop.2 ?_
  exact ⟨s, fun _t hst ↦ prod_le_prod_of_subset_of_one_le' hst fun i _ hbs ↦ hs i hbs⟩

@[to_additive]
theorem isLUB_hasProd (h : ∀ i, 1 ≤ f i) (hf : HasProd f a) :
    IsLUB (Set.range fun s ↦ ∏ i ∈ s, f i) a := by
  classical
  exact isLUB_of_tendsto_atTop (Finset.prod_mono_set_of_one_le' h) hf

@[to_additive]
theorem le_hasProd [L.NeBot] [L.LeAtTop] (hf : HasProd f a L) (i : ι) (hb : ∀ j, j ≠ i → 1 ≤ f j) :
    f i ≤ a :=
  calc
    f i = ∏ i ∈ {i}, f i := by rw [prod_singleton]
    _ ≤ a := prod_le_hasProd _ (by simpa) hf

@[to_additive]
theorem lt_hasProd [L.NeBot] [L.LeAtTop] [MulRightStrictMono α] (hf : HasProd f a L) (i : ι)
    (hi : ∀ (j : ι), j ≠ i → 1 ≤ f j) (j : ι) (hij : j ≠ i) (hj : 1 < f j) :
    f i < a := by
  classical
  calc
    f i < f j * f i := lt_mul_of_one_lt_left' (f i) hj
    _ = ∏ k ∈ {j, i}, f k := by rw [Finset.prod_pair hij]
    _ ≤ a := prod_le_hasProd _ (fun k hk ↦ hi k (hk ∘ mem_insert_of_mem ∘ mem_singleton.mpr)) hf

@[to_additive]
protected theorem Multipliable.prod_le_tprod [L.NeBot] [L.LeAtTop] {f : ι → α} (s : Finset ι)
    (hs : ∀ i, i ∉ s → 1 ≤ f i) (hf : Multipliable f L) :
    ∏ i ∈ s, f i ≤ ∏'[L] i, f i :=
  prod_le_hasProd s hs hf.hasProd

@[to_additive]
protected theorem Multipliable.le_tprod [L.NeBot] [L.LeAtTop] (hf : Multipliable f L) (i : ι)
    (hb : ∀ j ≠ i, 1 ≤ f j) : f i ≤ ∏'[L] i, f i :=
  le_hasProd hf.hasProd i hb

@[to_additive (attr := gcongr)]
protected theorem Multipliable.tprod_le_tprod [L.NeBot] (h : ∀ i, f i ≤ g i) (hf : Multipliable f L)
    (hg : Multipliable g L) : ∏'[L] i, f i ≤ ∏'[L] i, g i :=
  hasProd_le h hf.hasProd hg.hasProd

@[to_additive (attr := mono)]
protected theorem Multipliable.tprod_mono [L.NeBot] (hf : Multipliable f L) (hg : Multipliable g L)
    (h : f ≤ g) : ∏'[L] n, f n ≤ ∏'[L] n, g n :=
  hf.tprod_le_tprod h hg

omit [IsOrderedMonoid α] in
@[to_additive]
protected theorem Multipliable.tprod_le_of_prod_le [L.NeBot] (hf : Multipliable f L)
    (h : ∀ s, ∏ i ∈ s, f i ≤ a₂) : ∏'[L] i, f i ≤ a₂ :=
  hasProd_le_of_prod_le hf.hasProd h

omit [IsOrderedMonoid α] in
@[to_additive]
theorem tprod_le_of_prod_le' (ha₂ : 1 ≤ a₂) (h : ∀ s, ∏ i ∈ s, f i ≤ a₂) :
    ∏'[L] i, f i ≤ a₂ := by
  by_cases hL : L.NeBot
  · by_cases hf : Multipliable f L
    · exact hf.tprod_le_of_prod_le h
    · rwa [tprod_eq_one_of_not_multipliable hf]
  · by_cases hf : f.mulSupport.Finite
    · simpa [tprod_bot hL, finprod_eq_prod _ hf] using h _
    · rwa [tprod_bot hL, finprod_of_infinite_mulSupport hf]

@[to_additive]
theorem HasProd.one_le [L.NeBot] (h : ∀ i, 1 ≤ g i) (ha : HasProd g a L) : 1 ≤ a :=
  hasProd_le h hasProd_one ha

@[to_additive]
theorem HasProd.le_one [L.NeBot] (h : ∀ i, g i ≤ 1) (ha : HasProd g a L) : a ≤ 1 :=
  hasProd_le h ha hasProd_one

@[to_additive tsum_nonneg]
theorem one_le_tprod (h : ∀ i, 1 ≤ g i) : 1 ≤ ∏'[L] i, g i := by
  by_cases hg : Multipliable g L
  · by_cases hL : L.NeBot
    · exact hg.hasProd.one_le h
    · simpa [tprod_bot hL] using one_le_finprod' h
  · rw [tprod_eq_one_of_not_multipliable hg]

@[to_additive]
theorem tprod_le_one (h : ∀ i, f i ≤ 1) : ∏'[L] i, f i ≤ 1 := by
  by_cases hf : Multipliable f L
  · by_cases hL : L.NeBot
    · exact hf.hasProd.le_one h
    · simp only [tprod_bot hL]
      exact finprod_induction (· ≤ 1) le_rfl (fun _ _ ↦ mul_le_one') h
  · rw [tprod_eq_one_of_not_multipliable hf]

@[to_additive]
theorem hasProd_one_iff_of_one_le {ι α : Type*} {L : SummationFilter ι} [CommMonoid α]
  [PartialOrder α] [IsOrderedMonoid α] [TopologicalSpace α] [OrderClosedTopology α]
  {f : ι → α} [L.LeAtTop] [L.NeBot] (hf : ∀ i, 1 ≤ f i) :
    HasProd f 1 L ↔ f = 1 := by
  refine ⟨fun hf' ↦ ?_, ?_⟩
  · ext i
    exact (hf i).antisymm' (le_hasProd hf' _ fun j _ ↦ hf j)
  · rintro rfl
    exact hasProd_one

end OrderedCommMonoid

section OrderedCommGroup

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]
  [TopologicalSpace α] [IsTopologicalGroup α]
  [OrderClosedTopology α] {f g : ι → α} {a₁ a₂ : α} {i : ι}

@[to_additive]
theorem hasProd_lt [L.NeBot] [L.LeAtTop] (h : f ≤ g) (hi : f i < g i) (hf : HasProd f a₁ L)
    (hg : HasProd g a₂ L) : a₁ < a₂ := by
  classical
  have : update f i 1 ≤ update g i 1 := update_le_update_iff.mpr ⟨rfl.le, fun i _ ↦ h i⟩
  have : 1 / f i * a₁ ≤ 1 / g i * a₂ := hasProd_le this (hf.update i 1) (hg.update i 1)
  simpa only [one_div, mul_inv_cancel_left] using mul_lt_mul_of_lt_of_le hi this

@[to_additive (attr := mono)]
theorem hasProd_strict_mono (hf : HasProd f a₁) (hg : HasProd g a₂) (h : f < g) : a₁ < a₂ :=
  let ⟨hle, _i, hi⟩ := Pi.lt_def.mp h
  hasProd_lt hle hi hf hg

@[to_additive]
protected theorem Multipliable.tprod_lt_tprod [L.NeBot] [L.LeAtTop]
    (h : f ≤ g) (hi : f i < g i) (hf : Multipliable f L) (hg : Multipliable g L) :
    ∏'[L] n, f n < ∏'[L] n, g n :=
  hasProd_lt h hi hf.hasProd hg.hasProd

@[to_additive (attr := mono)]
protected theorem Multipliable.tprod_strict_mono [L.NeBot] [L.LeAtTop]
    (hf : Multipliable f L) (hg : Multipliable g L)
    (h : f < g) : ∏'[L] n, f n < ∏'[L] n, g n :=
  let ⟨hle, _i, hi⟩ := Pi.lt_def.mp h
  hf.tprod_lt_tprod hle hi hg

@[to_additive Summable.tsum_pos]
protected theorem Multipliable.one_lt_tprod [L.LeAtTop] [L.NeBot] (hsum : Multipliable g L)
    (hg : ∀ i, 1 ≤ g i) (i : ι) (hi : 1 < g i) : 1 < ∏'[L] i, g i := by
  rw [← tprod_one (L := L)]
  exact multipliable_one.tprod_lt_tprod hg hi hsum

end OrderedCommGroup

section CanonicallyOrderedMul

variable [CommMonoid α] [PartialOrder α] [IsOrderedMonoid α]
  [CanonicallyOrderedMul α] [TopologicalSpace α]
  [OrderClosedTopology α] {f : ι → α} {a : α}

@[to_additive]
theorem le_hasProd' (hf : HasProd f a) (i : ι) : f i ≤ a :=
  le_hasProd hf i fun _ _ ↦ one_le _

@[to_additive]
protected theorem Multipliable.le_tprod' (hf : Multipliable f) (i : ι) : f i ≤ ∏' i, f i :=
  hf.le_tprod i fun _ _ ↦ one_le _

@[to_additive]
theorem hasProd_one_iff : HasProd f 1 ↔ ∀ x, f x = 1 :=
  (hasProd_one_iff_of_one_le fun _ ↦ one_le _).trans funext_iff

@[to_additive]
protected theorem Multipliable.tprod_eq_one_iff (hf : Multipliable f) :
    ∏' i, f i = 1 ↔ ∀ x, f x = 1 := by
  rw [← hasProd_one_iff, hf.hasProd_iff]

@[to_additive]
protected theorem Multipliable.tprod_ne_one_iff (hf : Multipliable f) :
    ∏' i, f i ≠ 1 ↔ ∃ x, f x ≠ 1 := by
  rw [Ne, hf.tprod_eq_one_iff, not_forall]

omit [IsOrderedMonoid α] in
@[to_additive]
theorem isLUB_hasProd' (hf : HasProd f a) : IsLUB (Set.range fun s ↦ ∏ i ∈ s, f i) a := by
  classical
  exact isLUB_of_tendsto_atTop (Finset.prod_mono_set' f) hf

end CanonicallyOrderedMul

section CompleteLattice

variable [CommMonoid α] [CompleteLattice α] [CanonicallyOrderedMul α] [TopologicalSpace α]
  [SupConvergenceClass α] {ι' : Type*} {f g : ι → α} {s t : Set ι} {x : α} {i j : ι}

@[to_additive]
theorem CompleteLattice.hasProd : HasProd f (⨆ s : Finset ι, ∏ a ∈ s, f a) :=
  tendsto_atTop_iSup fun _ _ ↦ Finset.prod_le_prod_of_subset'

@[to_additive (attr := simp)] theorem CompleteLattice.multipliable : Multipliable f :=
  ⟨_, CompleteLattice.hasProd⟩

open CompleteLattice Set

variable [T2Space α]

@[to_additive] theorem tprod_eq_iSup_prod : ∏' x, f x = ⨆ s : Finset ι, ∏ a ∈ s, f a :=
  CompleteLattice.hasProd.tprod_eq

@[to_additive] theorem tprod_eq_iSup_prod' (s : ι' → Finset ι) (hs : ∀ t, ∃ i, t ⊆ s i) :
    ∏' a, f a = ⨆ i, ∏ a ∈ s i, f a := by
  rw [tprod_eq_iSup_prod]
  symm
  change ⨆ i : ι', (fun t : Finset ι => ∏ a ∈ t, f a) (s i) = ⨆ s : Finset ι, ∏ a ∈ s, f a
  exact (Finset.prod_mono_set' f).iSup_comp_eq hs

variable [ContinuousMul α]

@[to_additive] theorem tprod_mul : ∏' a, (f a * g a) = (∏' a, f a) * ∏' a, g a :=
  multipliable.tprod_mul multipliable

@[to_additive] theorem tprod_union_disjoint (hd : Disjoint s t) :
    ∏' (x : ↑(s ∪ t)), f x = (∏' (x : s), f x) * ∏' (x : t), f x :=
  multipliable.tprod_union_disjoint hd multipliable

@[to_additive] theorem tprod_le_of_subset (h : s ⊆ t) : ∏' (x : s), f x ≤ ∏' (x : t), f x := by
  rw [← diff_union_of_subset h, tprod_union_disjoint disjoint_sdiff_left]
  exact le_mul_self

@[to_additive] theorem tprod_union_le (f : ι → α) (s t : Set ι) :
    ∏' (x : ↑(s ∪ t)), f x ≤ (∏' (x : s), f x) * ∏' (x : t), f x := by
  rw [← diff_union_self, tprod_union_disjoint disjoint_sdiff_left]
  exact mul_le_mul_left (tprod_le_of_subset diff_subset) _

@[to_additive]
theorem tprod_insert (h : i ∉ s) : ∏' (x : ↑(insert i s)), f x = f i * ∏' (x : s), f x := by
  rw [← singleton_union, tprod_union_disjoint, tprod_singleton]
  rwa [Set.disjoint_singleton_left]

@[to_additive]
theorem tprod_singleton_mul_tprod_ne : f i * (∏' (x : {x // x ≠ i}), f x) = ∏' x, f x := by
  rw [eq_comm, ← tprod_univ, show univ = insert i {i}ᶜ by ext; simp [em]]
  exact tprod_insert (by simp)

open Classical in
@[to_additive] theorem tprod_eq_mul_tprod_ite {f : ι' → α} (b : ι') :
    ∏' x, f x = f b * ∏' x, ite (x = b) 1 (f x) :=
  multipliable.tprod_eq_mul_tprod_ite' b

omit [T2Space α]
variable [T3Space α]

@[to_additive] theorem tprod_fiberwise {ι''} (f : ι' → α) (g : ι' → ι'') :
    ∏' x, ∏' b : g ⁻¹' {x}, f b = ∏' i, f i := by
  apply HasProd.tprod_eq
  let equiv := Equiv.sigmaFiberEquiv g
  apply (equiv.hasProd_iff.mpr multipliable.hasProd).sigma
  exact fun _ ↦ multipliable.hasProd_iff.mpr rfl

@[to_additive] theorem tprod_comm {f : ι → ι' → α} : ∏' (a) (b), f a b = ∏' (b) (a), f a b :=
  multipliable.tprod_comm' (fun _ ↦ multipliable) fun _ ↦ multipliable

@[to_additive tsum_prod]
theorem tprod_prod {f : ι → ι' → α} : ∏' p : ι × ι', f p.1 p.2 = ∏' (a) (b), f a b :=
  multipliable.tprod_prod' fun _ ↦ multipliable

@[to_additive tsum_prod']
theorem tprod_prod' {f : ι × ι' → α} : ∏' p : ι × ι', f p = ∏' (a) (b), f (a, b) :=
  multipliable.tprod_prod' fun _ => multipliable

@[to_additive] theorem tprod_sigma {β : ι → Type*} (f : ∀ a, β a → α) :
    ∏' p : Σ i, β i, f p.1 p.2 = ∏' (i) (j), f i j :=
  multipliable.tprod_sigma' (fun _ ↦ multipliable)

@[to_additive] theorem tprod_sigma' {β : ι → Type*} (f : (Σ i, β i) → α) :
    ∏' p : Σ i, β i, f p = ∏' (i) (j), f ⟨i, j⟩ :=
  multipliable.tprod_sigma' (fun _ ↦ multipliable)

@[to_additive] theorem tprod_biUnion' {S : Set ι'} {t : ι' → Set ι} (h : S.PairwiseDisjoint t) :
    ∏' x : ⋃ i ∈ S, t i, f x = ∏' (i : S), ∏' (x : t i), f x := by
  simp [← tprod_sigma, ← (Set.biUnionEqSigmaOfDisjoint h).tprod_eq]

@[to_additive] theorem tprod_biUnion {t : ι' → Set ι} (h : Set.univ.PairwiseDisjoint t) :
    ∏' x : ⋃ i, t i, f x = ∏' (i) (x : t i), f x := by
  nth_rw 2 [← tprod_univ]
  rw [← tprod_biUnion' h, Set.biUnion_univ]

omit [ContinuousMul α] [T3Space α]
variable [IsOrderedMonoid α] [OrderClosedTopology α]

@[to_additive] theorem tprod_le_tprod (h : f ≤ g) : ∏' a, f a ≤ ∏' a, g a :=
  multipliable.tprod_le_tprod h multipliable

@[to_additive] theorem prod_le_tprod (s : Finset ι) : ∏ x ∈ s, f x ≤ ∏' x, f x :=
  multipliable.prod_le_tprod s (fun _ _ ↦ one_le _)

@[to_additive] theorem le_tprod (f : ι → α) (a : ι) : f a ≤ ∏' a, f a := multipliable.le_tprod' a

@[to_additive] theorem le_tprod_of_mem (hi : i ∈ s) : f i ≤ ∏' x : s, f x := by
  exact le_tprod (f ∘ (↑)) (⟨i, hi⟩ : s)

@[to_additive (attr := simp)] theorem tprod_eq_zero : ∏' i, f i = 1 ↔ ∀ i, f i = 1 :=
  multipliable.tprod_eq_one_iff

@[to_additive] theorem tprod_eq_top_of_eq_top : (∃ a, f a = ⊤) → ∏' a, f a = ⊤
  | ⟨a, ha⟩ => top_unique <| ha ▸ le_tprod f a

@[to_additive] theorem tprod_subtype_eq_top_of_eq_top (h : ∃ a ∈ s, f a = ⊤) : ∏' a : s, f a = ⊤ :=
  let ⟨a, ha, has⟩ := h
  tprod_eq_top_of_eq_top ⟨⟨a, ha⟩, has⟩

@[to_additive]
theorem tprod_comp_le_tprod_of_injective {f : ι → ι'} (hf : Injective f) (g : ι' → α) :
    ∏' x, g (f x) ≤ ∏' y, g y :=
  multipliable.tprod_le_tprod_of_inj f hf (fun _ _ ↦ one_le _) (fun _ ↦ le_rfl) multipliable

@[to_additive]
theorem tprod_le_tprod_comp_of_surjective {f : ι → ι'} (hf : Surjective f) (g : ι' → α) :
    ∏' y, g y ≤ ∏' x, g (f x) :=
  calc ∏' y, g y = ∏' y, g (f (surjInv hf y)) := by simp only [surjInv_eq hf]
    _ ≤ ∏' x, g (f x) := tprod_comp_le_tprod_of_injective (injective_surjInv hf) (g ∘ f)

@[to_additive]
theorem tprod_comp_eq_tprod_of_bijective {f : ι → ι'} (hf : f.Bijective) (g : ι' → α) :
    ∏' x, g (f x) = ∏' y, g y :=
  (tprod_comp_le_tprod_of_injective hf.injective g).antisymm
    (tprod_le_tprod_comp_of_surjective hf.surjective g)

@[to_additive]
theorem tprod_comp_eq_tprod_of_equiv (e : ι ≃ ι') (g : ι' → α) : ∏' x, g (e x) = ∏' y, g y := by
  rw [tprod_comp_eq_tprod_of_bijective e.bijective]

@[to_additive] theorem tprod_mono_subtype (f : ι → α) (h : s ⊆ t) : ∏' x : s, f x ≤ ∏' x : t, f x :=
  tprod_comp_le_tprod_of_injective (inclusion_injective h) (f ∘ (↑))

@[to_additive (attr := simp)] theorem tprod_top [Nonempty α] : ∏' _ : α, (⊤ : α) = ⊤ :=
  let ⟨a⟩ := ‹Nonempty α›
  tprod_eq_top_of_eq_top ⟨a, rfl⟩

@[to_additive] theorem ne_top_of_tprod_ne_top (h : ∏' a, f a ≠ ⊤) (i : ι) : f i ≠ ⊤ :=
  fun hi => h <| tprod_eq_top_of_eq_top ⟨i, hi⟩

variable [ContinuousMul α] [T3Space α]

@[to_additive] theorem tprod_iUnion_le_tprod (f : ι → α) (t : ι' → Set ι) :
    ∏' x : ⋃ i, t i, f x ≤ ∏' i, ∏' x : (t i), f x :=
  calc ∏' x : ⋃ i, t i, f x ≤ ∏' x : Σ i, t i, f x.2 :=
    tprod_le_tprod_comp_of_surjective (sigmaToiUnion_surjective t) _
  _ = ∏' i, ∏' x : t i, f x := tprod_sigma' _

@[to_additive] theorem tprod_biUnion_le_tprod (f : ι → α) (s : Set ι') (t : ι' → Set ι) :
    ∏' x : ⋃ i ∈ s , t i, f x ≤ ∏' i : s, ∏' x : t i, f x :=
  calc ∏' x : ⋃ i ∈ s, t i, f x = ∏' x : ⋃ i : s, t i, f x := by rw [tprod_congr_subtype]; simp
  _ ≤ ∏' i : s, ∏' x : t i, f x := tprod_iUnion_le_tprod _ _

@[to_additive] theorem tprod_biUnion_le (f : ι → α) (s : Finset ι') (t : ι' → Set ι) :
    ∏' x : ⋃ i ∈ s, t i, f x ≤ ∏ i ∈ s, ∏' x : t i, f x :=
  (tprod_biUnion_le_tprod f (↑s) t).trans_eq (Finset.tprod_subtype s fun i ↦ ∏' x : t i, f x)

@[to_additive] theorem tprod_iUnion_le [Fintype ι'] (f : ι → α) (t : ι' → Set ι) :
    ∏' x : ⋃ i, t i, f x ≤ ∏ i, ∏' x : t i, f x := by
  convert tprod_iUnion_le_tprod f t
  exact (tprod_fintype fun b ↦ ∏' (x : ↑(t b)), f ↑x).symm

@[to_additive]
theorem tprod_iUnion_eq_tprod (f : ι → α) (t : ι' → Set ι) (ht : Pairwise (Disjoint on t)) :
    ∏' x : ⋃ i, t i, f x = ∏' i, ∏' x : t i, f x := by
  calc ∏' x : ⋃ i, t i, f x = ∏' x : Σ i, t i, f x.2 :=
    (tprod_comp_eq_tprod_of_bijective (sigmaToiUnion_bijective t (fun _ _ hij ↦ ht hij)) _).symm
    _ = _ := tprod_sigma' _

omit [IsOrderedMonoid α] [T3Space α] in
@[to_additive] lemma prod_mul_tprod_compl (s : Finset ι') (f : ι' → α) :
    (∏ i ∈ s, f i) * ∏' i : ↥(s : Set ι')ᶜ, f i = ∏' i, f i := by
  rw [_root_.tprod_subtype, prod_eq_tprod_mulIndicator]
  simp [← tprod_mul]

end CompleteLattice

section LinearOrder

/-!
For infinite sums taking values in a linearly ordered monoid, the existence of a least upper
bound for the finite sums is a criterion for summability.

This criterion is useful when applied in a linearly ordered monoid which is also a complete or
conditionally complete linear order, such as `ℝ`, `ℝ≥0`, `ℝ≥0∞`, because it is then easy to check
the existence of a least upper bound.
-/

@[to_additive]
theorem hasProd_of_isLUB_of_one_le [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α]
    [TopologicalSpace α]
    [OrderTopology α] {f : ι → α} (i : α) (h : ∀ i, 1 ≤ f i)
    (hf : IsLUB (Set.range fun s ↦ ∏ i ∈ s, f i) i) : HasProd f i :=
  tendsto_atTop_isLUB (Finset.prod_mono_set_of_one_le' h) hf

@[to_additive]
theorem hasProd_of_isGLB_of_le_one [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α]
    [TopologicalSpace α]
    [OrderTopology α] {f : ι → α} (i : α) (h₀ : ∀ i, f i ≤ 1)
    (hf : IsGLB (Set.range fun s ↦ ∏ i ∈ s, f i) i) : HasProd f i :=
  tendsto_atTop_isGLB (Finset.prod_anti_set_of_le_one' h₀) hf

@[to_additive]
theorem hasProd_of_isLUB [CommMonoid α] [LinearOrder α]
    [CanonicallyOrderedMul α] [TopologicalSpace α]
    [OrderTopology α] {f : ι → α} (b : α) (hf : IsLUB (Set.range fun s ↦ ∏ i ∈ s, f i) b) :
    HasProd f b :=
  tendsto_atTop_isLUB (Finset.prod_mono_set' f) hf

@[to_additive]
theorem multipliable_mabs_iff [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]
    [UniformSpace α] [IsUniformGroup α]
    [CompleteSpace α] {f : ι → α} : (Multipliable fun x ↦ mabs (f x)) ↔ Multipliable f :=
  let s := { x | 1 ≤ f x }
  have h1 : ∀ x : s, mabs (f x) = f x := fun x ↦ mabs_of_one_le x.2
  have h2 : ∀ x : ↑sᶜ, mabs (f x) = (f x)⁻¹ := fun x ↦ mabs_of_lt_one (not_le.1 x.2)
  calc (Multipliable fun x ↦ mabs (f x)) ↔
      (Multipliable fun x : s ↦ mabs (f x)) ∧ Multipliable fun x : ↑sᶜ ↦ mabs (f x) :=
        multipliable_subtype_and_compl.symm
  _ ↔ (Multipliable fun x : s ↦ f x) ∧ Multipliable fun x : ↑sᶜ ↦ (f x)⁻¹ := by simp only [h1, h2]
  _ ↔ Multipliable f := by simp only [multipliable_inv_iff, multipliable_subtype_and_compl]

alias ⟨Summable.of_abs, Summable.abs⟩ := summable_abs_iff

theorem Finite.of_summable_const [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [TopologicalSpace α] [Archimedean α]
    [OrderClosedTopology α] {b : α} (hb : 0 < b) (hf : Summable fun _ : ι ↦ b) :
    Finite ι := by
  have H : ∀ s : Finset ι, #s • b ≤ ∑' _ : ι, b := fun s ↦ by
    simpa using sum_le_hasSum s (fun a _ ↦ hb.le) hf.hasSum
  obtain ⟨n, hn⟩ := Archimedean.arch (∑' _ : ι, b) hb
  have : ∀ s : Finset ι, #s ≤ n := fun s ↦ by
    simpa [nsmul_le_nsmul_iff_left hb] using (H s).trans hn
  have : Fintype ι := fintypeOfFinsetCardLe n this
  infer_instance

theorem Set.Finite.of_summable_const [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [TopologicalSpace α]
    [Archimedean α] [OrderClosedTopology α] {b : α} (hb : 0 < b) (hf : Summable fun _ : ι ↦ b) :
    (Set.univ : Set ι).Finite :=
  finite_univ_iff.2 <| .of_summable_const hb hf

end LinearOrder

section LinearOrderedCommRing

variable [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
  [TopologicalSpace α] [OrderTopology α] {f : ι → α} {x : α}

nonrec theorem HasProd.abs (hfx : HasProd f x) : HasProd (|f ·|) |x| := by
  simpa only [HasProd, ← abs_prod] using hfx.abs

theorem Multipliable.abs (hf : Multipliable f) : Multipliable (|f ·|) :=
  let ⟨x, hx⟩ := hf; ⟨|x|, hx.abs⟩

protected theorem Multipliable.abs_tprod (hf : Multipliable f) : |∏' i, f i| = ∏' i, |f i| :=
  hf.hasProd.abs.tprod_eq.symm

end LinearOrderedCommRing

theorem Summable.tendsto_atTop_of_pos [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    [TopologicalSpace α] [OrderTopology α]
    {f : ℕ → α} (hf : Summable f⁻¹) (hf' : ∀ n, 0 < f n) : Tendsto f atTop atTop :=
  inv_inv f ▸ Filter.Tendsto.inv_tendsto_nhdsGT_zero <|
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hf.tendsto_atTop_zero <|
      Eventually.of_forall fun _ ↦ inv_pos.2 (hf' _)

namespace Mathlib.Meta.Positivity

open Qq Lean Meta Finset

attribute [local instance] monadLiftOptionMetaM in
/-- Positivity extension for infinite sums.

This extension only proves non-negativity, strict positivity is more delicate for infinite sums and
requires more assumptions. -/
@[positivity tsum _]
meta def evalTsum : PositivityExt where eval {u α} zα pα e := do
  match e with
  | ~q(@tsum _ $ι $instCommMonoid $instTopSpace $f $L) =>
    lambdaBoundedTelescope f 1 fun args (body : Q($α)) => do
      let #[(i : Q($ι))] := args | failure
      let rbody ← core zα pα body
      let pbody ← rbody.toNonneg
      let pr : Q(∀ i, 0 ≤ $f i) ← mkLambdaFVars #[i] pbody
      let mα' ← synthInstanceQ q(AddCommMonoid $α)
      let oα' ← synthInstanceQ q(Preorder $α)
      let pα' ← synthInstanceQ q(IsOrderedAddMonoid $α)
      let instOrderClosed ← synthInstanceQ q(OrderClosedTopology $α)
      assertInstancesCommute
      return .nonnegative
        q(@tsum_nonneg $ι $α $L $mα' $oα' $pα' $instTopSpace $instOrderClosed $f $pr)
  | _ => throwError "not tsum"

end Mathlib.Meta.Positivity
