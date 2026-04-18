/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Jun Kwon
-/
module

public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Infinite sums in `CompleteLinearOrderedAddCommMonoidWithTop E`

This file defines results on infinite sums in `CompleteLinearOrderedAddCommMonoidWithTop E`.
-/

public section

open Set Function

variable {α β γ E : Type*} [CompleteLinearOrderedAddCommMonoidWithTop E] [TopologicalSpace E]
  [OrderTopology E] [CanonicallyOrderedAdd E] {r x y z ε : E} {f g : α → E} {s t : Set α}
  {a b : α}

namespace CompleteLinearOrderedAddCommMonoidWithTop

theorem hasSum : HasSum f (⨆ s : Finset α, ∑ a ∈ s, f a) :=
  tendsto_atTop_iSup fun _ _ ↦ Finset.sum_le_sum_of_subset

@[simp] theorem summable : Summable f := ⟨_, hasSum⟩

theorem tsum_eq_iSup_sum : ∑' x, f x = ⨆ s : Finset α, ∑ a ∈ s, f a := hasSum.tsum_eq

theorem tsum_eq_iSup_sum' {ι : Type*} (s : ι → Finset α) (hs : ∀ t, ∃ i, t ⊆ s i) :
    ∑' a, f a = ⨆ i, ∑ a ∈ s i, f a := by
  rw [tsum_eq_iSup_sum]
  symm
  change ⨆ i : ι, (fun t : Finset α => ∑ a ∈ t, f a) (s i) = ⨆ s : Finset α, ∑ a ∈ s, f a
  exact (Finset.sum_mono_set f).iSup_comp_eq hs

theorem tsum_comm [ContinuousAdd E] {f : α → β → E} : ∑' (a) (b), f a b = ∑' (b) (a), f a b :=
  summable.tsum_comm' (fun _ ↦ summable) fun _ ↦ summable

theorem tsum_prod [ContinuousAdd E] {f : α → β → E} : ∑' p : α × β, f p.1 p.2 = ∑' (a) (b), f a b :=
  summable.tsum_prod' fun _ ↦ summable

theorem tsum_prod' [ContinuousAdd E] {f : α × β → E} : ∑' p : α × β, f p = ∑' (a) (b), f (a, b) :=
  summable.tsum_prod' fun _ => summable

theorem tsum_add [ContinuousAdd E] : ∑' a, (f a + g a) = ∑' a, f a + ∑' a, g a :=
  summable.tsum_add summable

theorem tsum_le_tsum (h : f ≤ g) : ∑' a, f a ≤ ∑' a, g a := summable.tsum_le_tsum h summable

theorem sum_le_tsum (s : Finset α) : ∑ x ∈ s, f x ≤ ∑' x, f x :=
  summable.sum_le_tsum s (fun _ _ ↦ zero_le _)

theorem le_tsum (f : α → E) (a : α) : f a ≤ ∑' a, f a := summable.le_tsum' a

theorem le_tsum_of_mem (ha : a ∈ s) : f a ≤ ∑' x : s, f x := by
  exact le_tsum (f ∘ (↑)) (⟨a, ha⟩ : s)

@[simp] theorem tsum_eq_zero : ∑' i, f i = 0 ↔ ∀ i, f i = 0 := summable.tsum_eq_zero_iff

theorem tsum_eq_top_of_eq_top : (∃ a, f a = ⊤) → ∑' a, f a = ⊤
  | ⟨a, ha⟩ => top_unique <| ha ▸ le_tsum f a

theorem tsum_subtype_eq_top_of_eq_top (h : ∃ a ∈ s, f a = ⊤) : ∑' a : s, f a = ⊤ :=
  let ⟨a, ha, has⟩ := h
  tsum_eq_top_of_eq_top ⟨⟨a, ha⟩, has⟩

theorem tsum_union_disjoint [ContinuousAdd E] (hd : Disjoint s t) :
    ∑' (x : ↑(s ∪ t)), f x = ∑' (x : s), f x + ∑' (x : t), f x :=
  summable.tsum_union_disjoint hd summable

theorem tsum_le_of_subset [ContinuousAdd E] (h : s ⊆ t) : ∑' (x : s), f x ≤ ∑' (x : t), f x := by
  rw [← diff_union_of_subset h, tsum_union_disjoint disjoint_sdiff_left]
  exact le_add_self

theorem tsum_union_le [ContinuousAdd E] (f : α → E) (s t : Set α) :
    ∑' (x : ↑(s ∪ t)), f x ≤ ∑' (x : s), f x + ∑' (x : t), f x := by
  rw [← diff_union_self, tsum_union_disjoint disjoint_sdiff_left]
  exact add_le_add_left (tsum_le_of_subset diff_subset) _

theorem tsum_insert [ContinuousAdd E] (h : a ∉ s) :
    ∑' (x : ↑(insert a s)), f x = f a + ∑' (x : s), f x := by
  rw [← singleton_union, tsum_union_disjoint, tsum_singleton]
  rwa [disjoint_singleton_left]

theorem tsum_singleton_add_tsum_ne [ContinuousAdd E] :
    f a + (∑' (x : {x // x ≠ a}), f x) = ∑' x, f x := by
  rw [eq_comm, ← tsum_univ, show univ = insert a {a}ᶜ by ext; simp [em]]
  exact tsum_insert (by simp)

theorem tsum_comp_le_tsum_of_injective {f : α → β} (hf : Injective f) (g : β → E) :
    ∑' x, g (f x) ≤ ∑' y, g y :=
  summable.tsum_le_tsum_of_inj f hf (fun _ _ ↦ zero_le _) (fun _ ↦ le_rfl) summable

theorem tsum_le_tsum_comp_of_surjective {f : α → β} (hf : Surjective f) (g : β → E) :
    ∑' y, g y ≤ ∑' x, g (f x) :=
  calc ∑' y, g y = ∑' y, g (f (surjInv hf y)) := by simp only [surjInv_eq hf]
    _ ≤ ∑' x, g (f x) := tsum_comp_le_tsum_of_injective (injective_surjInv hf) (g ∘ f)

theorem tsum_comp_eq_tsum_of_bijective {f : α → β} (hf : f.Bijective) (g : β → E) :
    ∑' x, g (f x) = ∑' y, g y :=
  (tsum_comp_le_tsum_of_injective hf.injective g).antisymm
    (tsum_le_tsum_comp_of_surjective hf.surjective g)

theorem tsum_comp_eq_tsum_of_equiv (e : α ≃ β) (g : β → E) :
    ∑' x, g (e x) = ∑' y, g y := by
  rw [tsum_comp_eq_tsum_of_bijective e.bijective]

theorem tsum_mono_subtype (f : α → E) (h : s ⊆ t) : ∑' x : s, f x ≤ ∑' x : t, f x :=
  tsum_comp_le_tsum_of_injective (inclusion_injective h) (f ∘ (↑))

theorem tsum_sigma [ContinuousAdd E] {β : α → Type*} (f : ∀ a, β a → E) :
    ∑' p : Σa, β a, f p.1 p.2 = ∑' (a) (b), f a b :=
  summable.tsum_sigma' (fun _ ↦ summable)

theorem tsum_sigma' [ContinuousAdd E] {β : α → Type*} (f : (Σ a, β a) → E) :
    ∑' p : Σ a, β a, f p = ∑' (a) (b), f ⟨a, b⟩ :=
  summable.tsum_sigma' (fun _ ↦ summable)

lemma le_tsum_of_forall_lt_exists_sum {a : E}
    (h : ∀ b < a, ∃ I : Finset α, b < ∑ i ∈ I, f i) : a ≤ ∑' i, f i := by
  refine le_of_forall_lt fun b hb ↦ ?_
  obtain ⟨I, hI⟩ := h b hb
  exact lt_of_lt_of_le hI (sum_le_tsum I)

theorem lt_top_of_tsum_ne_top {a : α → E} (tsum_ne_top : ∑' i, a i ≠ ⊤) (j : α) : a j < ⊤ := by
  contrapose! tsum_ne_top with h
  exact tsum_eq_top_of_eq_top ⟨j, top_unique h⟩

@[simp] theorem tsum_top [Nonempty α] : ∑' _ : α, (⊤ : E) = ⊤ :=
  let ⟨a⟩ := ‹Nonempty α›
  tsum_eq_top_of_eq_top ⟨a, rfl⟩

theorem ne_top_of_tsum_ne_top (h : ∑' a, f a ≠ ⊤) (a : α) : f a ≠ ⊤ := fun ha =>
  h <| tsum_eq_top_of_eq_top ⟨a, ha⟩

omit [OrderTopology E] in @[simp]
theorem tsum_iSup_eq (a : α) : (∑' b : α, ⨆ _ : a = b, f b) = f a :=
  (tsum_eq_single a fun _ h => by simp [h.symm]).trans <| by simp

open Classical in
theorem tsum_eq_add_tsum_ite [ContinuousAdd E] {f : β → E} (b : β) :
    ∑' x, f x = f b + ∑' x, ite (x = b) 0 (f x) :=
  summable.tsum_eq_add_tsum_ite' b

theorem tsum_fiberwise [ContinuousAdd E] (f : β → E) (g : β → γ) :
    ∑' x, ∑' b : g ⁻¹' {x}, f b = ∑' i, f i := by
  apply HasSum.tsum_eq
  let equiv := Equiv.sigmaFiberEquiv g
  apply (equiv.hasSum_iff.mpr summable.hasSum).sigma
  exact fun _ ↦ summable.hasSum_iff.mpr rfl

variable {ι : Type*} [ContinuousAdd E]

theorem tsum_iUnion_le_tsum (f : α → E) (t : ι → Set α) :
    ∑' x : ⋃ i, t i, f x ≤ ∑' i, ∑' x : (t i), f x :=
  calc ∑' x : ⋃ i, t i, f x ≤ ∑' x : Σ i, t i, f x.2 :=
    tsum_le_tsum_comp_of_surjective (sigmaToiUnion_surjective t) _
  _ = ∑' i, ∑' x : t i, f x := tsum_sigma' _

theorem tsum_biUnion' {S : Set ι} {t : ι → Set α} (h : S.PairwiseDisjoint t) :
    ∑' x : ⋃ i ∈ S, t i, f x = ∑' (i : S), ∑' (x : t i), f x := by
  simp [← tsum_sigma, ← (Set.biUnionEqSigmaOfDisjoint h).tsum_eq]

theorem tsum_biUnion {t : ι → Set α} (h : Set.univ.PairwiseDisjoint t) :
    ∑' x : ⋃ i, t i, f x = ∑' (i) (x : t i), f x := by
  nth_rw 2 [← tsum_univ]
  rw [← tsum_biUnion' h, Set.biUnion_univ]

theorem tsum_biUnion_le_tsum (f : α → E) (s : Set ι) (t : ι → Set α) :
    ∑' x : ⋃ i ∈ s , t i, f x ≤ ∑' i : s, ∑' x : t i, f x :=
  calc ∑' x : ⋃ i ∈ s, t i, f x = ∑' x : ⋃ i : s, t i, f x := by rw [tsum_congr_subtype]; simp
  _ ≤ ∑' i : s, ∑' x : t i, f x := tsum_iUnion_le_tsum _ _

theorem tsum_biUnion_le (f : α → E) (s : Finset ι) (t : ι → Set α) :
    ∑' x : ⋃ i ∈ s, t i, f x ≤ ∑ i ∈ s, ∑' x : t i, f x :=
  (tsum_biUnion_le_tsum f (↑s) t).trans_eq (Finset.tsum_subtype s fun i ↦ ∑' x : t i, f x)

theorem tsum_iUnion_le [Fintype ι] (f : α → E) (t : ι → Set α) :
    ∑' x : ⋃ i, t i, f x ≤ ∑ i, ∑' x : t i, f x := by
  convert tsum_iUnion_le_tsum f t
  exact (tsum_fintype fun b ↦ ∑' (x : ↑(t b)), f ↑x).symm

theorem tsum_iUnion_eq_tsum (f : α → E) (t : ι → Set α) (ht : Pairwise (Disjoint on t)) :
    ∑' x : ⋃ i, t i, f x = ∑' i, ∑' x : t i, f x :=
  calc ∑' x : ⋃ i, t i, f x = ∑' x : Σ i, t i, f x.2 :=
    (tsum_comp_eq_tsum_of_bijective (sigmaToiUnion_bijective t (fun _ _ hij ↦ ht hij)) _).symm
    _ = _ := tsum_sigma' _

lemma sum_add_tsum_compl (s : Finset ι) (f : ι → E) :
    ∑ i ∈ s, f i + ∑' i : ↥(s : Set ι)ᶜ, f i = ∑' i, f i := by
  rw [tsum_subtype, sum_eq_tsum_indicator]
  simp [← tsum_add]

end CompleteLinearOrderedAddCommMonoidWithTop
