/-
Copyright (c) 2022 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Order.T5
import Mathlib.Order.Interval.Set.WithBotTop
import Mathlib.Order.Filter.Pointwise
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Order


/-!
# Topology on extended natural numbers
-/

open Filter Set Topology Function

namespace ENat

/--
Topology on `ℕ∞`.

Note: this is different from the `EMetricSpace` topology. The `EMetricSpace` topology has
`IsOpen {∞}`, but all neighborhoods of `∞` in `ℕ∞` contain infinite intervals.
-/
instance : TopologicalSpace ℕ∞ := Preorder.topology ℕ∞

instance : OrderTopology ℕ∞ := ⟨rfl⟩

@[simp] theorem range_natCast : range ((↑) : ℕ → ℕ∞) = Iio ⊤ :=
  WithTop.range_coe

theorem isEmbedding_natCast : IsEmbedding ((↑) : ℕ → ℕ∞) :=
  Nat.strictMono_cast.isEmbedding_of_ordConnected <| range_natCast ▸ ordConnected_Iio

@[deprecated (since := "2024-10-26")]
alias embedding_natCast := isEmbedding_natCast

theorem isOpenEmbedding_natCast : IsOpenEmbedding ((↑) : ℕ → ℕ∞) :=
  ⟨isEmbedding_natCast, range_natCast ▸ isOpen_Iio⟩

theorem nhds_natCast (n : ℕ) : 𝓝 (n : ℕ∞) = pure (n : ℕ∞) := by
  simp [← isOpenEmbedding_natCast.map_nhds_eq]

@[simp]
protected theorem nhds_eq_pure {n : ℕ∞} (h : n ≠ ⊤) : 𝓝 n = pure n := by
  lift n to ℕ using h
  simp [nhds_natCast]

theorem isOpen_singleton {x : ℕ∞} (hx : x ≠ ⊤) : IsOpen {x} := by
  rw [isOpen_singleton_iff_nhds_eq_pure, ENat.nhds_eq_pure hx]

theorem mem_nhds_iff {x : ℕ∞} {s : Set ℕ∞} (hx : x ≠ ⊤) : s ∈ 𝓝 x ↔ x ∈ s := by
  simp [hx]

theorem mem_nhds_natCast_iff (n : ℕ) {s : Set ℕ∞} : s ∈ 𝓝 (n : ℕ∞) ↔ (n : ℕ∞) ∈ s :=
  mem_nhds_iff (coe_ne_top _)

theorem tendsto_nhds_top_iff_natCast_lt {α : Type*} {l : Filter α} {f : α → ℕ∞} :
    Tendsto f l (𝓝 ⊤) ↔ ∀ n : ℕ, ∀ᶠ a in l, n < f a := by
  simp_rw [nhds_top_order, lt_top_iff_ne_top, tendsto_iInf, tendsto_principal]
  exact Option.forall_ne_none

instance : ContinuousAdd ℕ∞ := by
  refine ⟨continuous_iff_continuousAt.2 fun (a, b) ↦ ?_⟩
  match a, b with
  | ⊤, _ => exact tendsto_nhds_top_mono' continuousAt_fst fun p ↦ le_add_right le_rfl
  | (a : ℕ), ⊤ => exact tendsto_nhds_top_mono' continuousAt_snd fun p ↦ le_add_left le_rfl
  | (a : ℕ), (b : ℕ) => simp [ContinuousAt, nhds_prod_eq, tendsto_pure_nhds]

instance : ContinuousMul ℕ∞ where
  continuous_mul :=
    have key (a : ℕ∞) : ContinuousAt (· * ·).uncurry (a, ⊤) := by
      rcases (zero_le a).eq_or_gt with rfl | ha
      · simp [ContinuousAt, nhds_prod_eq]
      · simp only [ContinuousAt, Function.uncurry, mul_top ha.ne']
        refine tendsto_nhds_top_mono continuousAt_snd ?_
        filter_upwards [continuousAt_fst (lt_mem_nhds ha)] with (x, y) (hx : 0 < x)
        exact le_mul_of_one_le_left (zero_le y) (Order.one_le_iff_pos.2 hx)
    continuous_iff_continuousAt.2 <| Prod.forall.2 fun
      | (a : ℕ∞), ⊤ => key a
      | ⊤, (b : ℕ∞) =>
        ((key b).comp_of_eq (continuous_swap.tendsto (⊤, b)) rfl).congr <|
          .of_forall fun _ ↦ mul_comm ..
      | (a : ℕ), (b : ℕ) => by
        simp [ContinuousAt, nhds_prod_eq, tendsto_pure_nhds]

protected theorem continuousAt_sub {a b : ℕ∞} (h : a ≠ ⊤ ∨ b ≠ ⊤) :
    ContinuousAt (· - ·).uncurry (a, b) := by
  match a, b, h with
  | (a : ℕ), (b : ℕ), _ => simp [ContinuousAt, nhds_prod_eq]
  | (a : ℕ), ⊤, _ =>
    suffices ∀ᶠ b in 𝓝 ⊤, (a - b : ℕ∞) = 0 by
      simpa [ContinuousAt, nhds_prod_eq, tsub_eq_zero_of_le]
    filter_upwards [le_mem_nhds (WithTop.coe_lt_top a)] with b using tsub_eq_zero_of_le
  | ⊤, (b : ℕ), _ =>
    suffices ∀ n : ℕ, ∀ᶠ a : ℕ∞ in 𝓝 ⊤, b + n < a by
      simpa [ContinuousAt, nhds_prod_eq, (· ∘ ·), lt_tsub_iff_left, tendsto_nhds_top_iff_natCast_lt]
    exact fun n ↦ lt_mem_nhds <| WithTop.coe_lt_top (b + n)

end ENat

theorem Filter.Tendsto.enatSub {α : Type*} {l : Filter α} {f g : α → ℕ∞} {a b : ℕ∞}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (h : a ≠ ⊤ ∨ b ≠ ⊤) :
    Tendsto (fun x ↦ f x - g x) l (𝓝 (a - b)) :=
  (ENat.continuousAt_sub h).tendsto.comp (hf.prodMk_nhds hg)

variable {X : Type*} [TopologicalSpace X] {f g : X → ℕ∞} {s : Set X} {x : X}

nonrec theorem ContinuousWithinAt.enatSub
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) (h : f x ≠ ⊤ ∨ g x ≠ ⊤) :
    ContinuousWithinAt (fun x ↦ f x - g x) s x :=
  hf.enatSub hg h

nonrec theorem ContinuousAt.enatSub
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) (h : f x ≠ ⊤ ∨ g x ≠ ⊤) :
    ContinuousAt (fun x ↦ f x - g x) x :=
  hf.enatSub hg h

nonrec theorem ContinuousOn.enatSub
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h : ∀ x ∈ s, f x ≠ ⊤ ∨ g x ≠ ⊤) :
    ContinuousOn (fun x ↦ f x - g x) s := fun x hx ↦
  (hf x hx).enatSub (hg x hx) (h x hx)

nonrec theorem Continuous.enatSub
    (hf : Continuous f) (hg : Continuous g) (h : ∀ x, f x ≠ ⊤ ∨ g x ≠ ⊤) :
    Continuous (fun x ↦ f x - g x) :=
  continuous_iff_continuousAt.2 fun x ↦ hf.continuousAt.enatSub hg.continuousAt (h x)

namespace ENat

section tsum

variable {ι : Sort*} {α β : Type*} {f g : α → ℕ∞} {s t : Set α}

protected theorem hasSum : HasSum f (⨆ s : Finset α, ∑ a ∈ s, f a) :=
  tendsto_atTop_iSup fun _ _ ↦ Finset.sum_le_sum_of_subset

@[simp] protected theorem summable : Summable f :=
  ⟨_, ENat.hasSum⟩

protected theorem tsum_eq_iSup_sum : ∑' x, f x = (⨆ s : Finset α, ∑ a ∈ s, f a) :=
  ENat.hasSum.tsum_eq

protected theorem tsum_comm {f : α → β → ℕ∞} : ∑' (a) (b), f a b = ∑' (b) (a), f a b :=
  tsum_comm' ENat.summable (fun _ ↦ ENat.summable) fun _ ↦ ENat.summable

protected theorem tsum_prod {f : α → β → ℕ∞} : ∑' p : α × β, f p.1 p.2 = ∑' (a) (b), f a b :=
  tsum_prod' ENat.summable fun _ ↦ ENat.summable

protected theorem tsum_add : ∑' a, (f a + g a) = ∑' a, f a + ∑' a, g a :=
  tsum_add ENat.summable ENat.summable

protected theorem tsum_le_tsum (h : f ≤ g) : ∑' a, f a ≤ ∑' a, g a :=
  tsum_le_tsum h ENat.summable ENat.summable

protected theorem sum_le_tsum {f : α → ℕ∞} (s : Finset α) : ∑ x ∈ s, f x ≤ ∑' x, f x :=
  sum_le_tsum s (fun _ _ ↦ zero_le _) ENat.summable

protected theorem le_tsum (a : α) : f a ≤ ∑' a, f a :=
  le_tsum' ENat.summable a

protected theorem le_tsum_of_mem {s : Set α} {a : α} (ha : a ∈ s) : f a ≤ ∑' x : s, f x :=
  ENat.le_tsum (⟨a,ha⟩ : s)

@[simp] protected theorem tsum_eq_zero : ∑' i, f i = 0 ↔ ∀ i, f i = 0 :=
  tsum_eq_zero_iff ENat.summable

protected theorem tsum_eq_top_of_eq_top : (∃ a, f a = ⊤) → ∑' a, f a = ⊤
  | ⟨a, ha⟩ => top_unique <| ha ▸ ENat.le_tsum a

protected theorem tsum_subtype_eq_top_of_eq_top {s : Set α} (h : ∃ a ∈ s, f a = ⊤) :
    ∑' a : s, f a = ⊤ :=
  let ⟨a, ha, has⟩ := h
  ENat.tsum_eq_top_of_eq_top ⟨⟨a, ha⟩, has⟩

protected theorem tsum_subtype_union_disjoint {s t : Set α} (hd : Disjoint s t) :
    ∑' (x : ↑(s ∪ t)), f x = ∑' (x : s), f x + ∑' (x : t), f x :=
  tsum_union_disjoint hd ENat.summable ENat.summable

protected theorem tsum_subtype_le_of_subset {s t : Set α} (h : s ⊆ t) :
    ∑' (x : s), f x ≤ ∑' (x : t), f x := by
  rw [← diff_union_of_subset h, ENat.tsum_subtype_union_disjoint disjoint_sdiff_left]
  exact le_add_self

protected theorem tsum_subtype_union_le (s t : Set α) :
    ∑' (x : ↑(s ∪ t)), f (x : α) ≤ ∑' (x : s), f x + ∑' (x : t), f x := by
  rw [← diff_union_self, ENat.tsum_subtype_union_disjoint disjoint_sdiff_left]
  exact add_le_add_right (ENat.tsum_subtype_le_of_subset diff_subset) _

protected theorem tsum_subtype_insert {s : Set α} {a : α} (h : a ∉ s) :
    ∑' (x : ↑(insert a s)), f x = f a + ∑' (x : s), f x := by
  rw [← singleton_union, ENat.tsum_subtype_union_disjoint, tsum_singleton]
  rwa [disjoint_singleton_left]

protected theorem tsum_sub (hfin : ∑' a, g a ≠ ⊤) (h : g ≤ f) :
    ∑' a, (f a - g a) = ∑' a, f a - ∑' a, g a := by
  rw [← WithTop.add_right_inj hfin, ← ENat.tsum_add,
    tsum_congr (fun i ↦ tsub_add_cancel_of_le (h i)), tsub_add_cancel_of_le (ENat.tsum_le_tsum h)]

protected theorem mul_tsum (c : ℕ∞) : c * ∑' a, f a = ∑' a, c * f a := by
  simp_rw [ENat.tsum_eq_iSup_sum, ENat.mul_iSup, Finset.mul_sum]

protected theorem tsum_mul (c : ℕ∞) : (∑' a, f a) * c = ∑' a, f a * c := by
  simp_rw [ENat.tsum_eq_iSup_sum, ENat.iSup_mul, Finset.sum_mul]

protected theorem tsum_subtype_eq_top_iff_of_finite (hs : s.Finite) :
    ∑' (x : s), f x = ⊤ ↔ ∃ a ∈ s, f a = ⊤ := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | @insert a s₀ has₀ hs₀ ih => simp [ENat.tsum_subtype_insert has₀, ih]

protected theorem tsum_eq_top_of_support_infinite (hf : f.support.Infinite) : ∑' a, f a = ⊤ := by
  rw [ENat.tsum_eq_iSup_sum, iSup_eq_top]
  intro b hb
  lift b to ℕ using hb.ne
  obtain ⟨t, htf, hbt, hfin⟩ := hf.exists_finite_subset_encard_gt b
  refine ⟨hfin.toFinset, hbt.trans_le ?_⟩
  rw [hfin.encard_eq_coe_toFinset_card, Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  simp only [Nat.cast_one, ENat.one_le_iff_ne_zero]
  exact htf <| by simpa using hi

protected theorem tsum_const_eq_top {ι : Type*} [Infinite ι] {c : ℕ∞} (hc : c ≠ 0) :
    ∑' (_ : ι), c = ⊤ :=
  ENat.tsum_eq_top_of_support_infinite <| by rwa [Function.support_const hc, infinite_univ_iff]

protected theorem tsum_eq_top_iff : ∑' a, f a = ⊤ ↔ f.support.Infinite ∨ ∃ a, f a = ⊤ := by
  rw [iff_def, or_imp, and_iff_right ENat.tsum_eq_top_of_support_infinite, or_iff_not_imp_left,
    not_infinite]
  refine ⟨fun htop hfin ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
  · rw [← tsum_subtype_support, ENat.tsum_subtype_eq_top_iff_of_finite hfin] at htop
    exact Exists.elim htop <| fun a h ↦ ⟨a, h.2⟩
  rw [← top_le_iff, ← ha]
  exact ENat.le_tsum a

protected theorem tsum_subtype_eq_top_iff {s : Set α} :
    ∑' (a : s), f a = ⊤ ↔ (s ∩ f.support).Infinite ∨ ∃ a ∈ s, f a = ⊤ := by
  simp only [ENat.tsum_eq_top_iff, Subtype.exists, exists_prop]
  convert Iff.rfl
  convert Set.finite_image_iff Subtype.val_injective.injOn
  aesop

protected theorem tsum_subtype_eq_top_of_inter_support_infinite {s : Set α}
    (hf : (s ∩ f.support).Infinite) : ∑' (a : s), f a = ⊤ :=
  ENat.tsum_subtype_eq_top_iff.2 <| Or.inl hf

protected theorem tsum_subtype_const_eq_top_of_ne_zero {s : Set α} (hs : s.Infinite) {c : ℕ∞}
    (hc : c ≠ 0) : ∑' (_ : s), c = ⊤ :=
  ENat.tsum_subtype_eq_top_of_inter_support_infinite (f := fun _ ↦ c)
    <| by rwa [support_const hc, inter_univ]

protected theorem tsum_comp_le_tsum_of_injective {f : α → β} (hf : Injective f) (g : β → ℕ∞) :
    ∑' x, g (f x) ≤ ∑' y, g y :=
  tsum_le_tsum_of_inj f hf (fun _ _ ↦ zero_le _) (fun _ ↦ le_rfl) ENat.summable ENat.summable

protected theorem tsum_le_tsum_comp_of_surjective {f : α → β} (hf : Surjective f) (g : β → ℕ∞) :
    ∑' y, g y ≤ ∑' x, g (f x) :=
  calc ∑' y, g y = ∑' y, g (f (surjInv hf y)) := by simp only [surjInv_eq hf]
    _ ≤ ∑' x, g (f x) := ENat.tsum_comp_le_tsum_of_injective (injective_surjInv hf) _

protected theorem tsum_comp_eq_tsum_of_bijective {f : α → β} (hf : f.Bijective) (g : β → ℕ∞) :
    ∑' x, g (f x) = ∑' y, g y :=
  (ENat.tsum_comp_le_tsum_of_injective hf.injective g).antisymm
    (ENat.tsum_le_tsum_comp_of_surjective hf.surjective g)

protected theorem tsum_comp_eq_tsum_of_equiv (e : α ≃ β) (g : β → ℕ∞) :
    ∑' x, g (e x) = ∑' y, g y := by
  rw [ENat.tsum_comp_eq_tsum_of_bijective e.bijective]

protected theorem tsum_subtype_mono (f : α → ℕ∞) {s t : Set α} (h : s ⊆ t) :
    ∑' x : s, f x ≤ ∑' x : t, f x :=
  ENat.tsum_comp_le_tsum_of_injective (inclusion_injective h) _

protected theorem tsum_subtype_sigma {β : α → Type*} (f : ∀ a, β a → ℕ∞) :
    ∑' p : Σa, β a, f p.1 p.2 = ∑' (a) (b), f a b :=
  tsum_sigma' (fun _ ↦ ENat.summable) ENat.summable

protected theorem tsum_subtype_sigma' {β : α → Type*} (f : (Σ a, β a) → ℕ∞) :
    ∑' p : Σ a, β a, f p = ∑' (a) (b), f ⟨a, b⟩ :=
  tsum_sigma' (fun _ ↦ ENat.summable) ENat.summable

variable {ι : Type*}

protected theorem tsum_subtype_iUnion_le_tsum (f : α → ℕ∞) (t : ι → Set α) :
    ∑' x : ⋃ i, t i, f x ≤ ∑' i, ∑' x : (t i), f x :=
  calc ∑' x : ⋃ i, t i, f x ≤ ∑' x : Σ i, t i, f x.2 :=
    ENat.tsum_le_tsum_comp_of_surjective (sigmaToiUnion_surjective t) _
  _ = ∑' i, ∑' x : t i, f x := ENat.tsum_subtype_sigma' _

protected theorem tsum_subtype_biUnion_le_tsum (f : α → ℕ∞) (s : Set ι) (t : ι → Set α) :
    ∑' x : ⋃ i ∈ s , t i, f x ≤ ∑' i : s, ∑' x : t i, f x :=
  calc ∑' x : ⋃ i ∈ s, t i, f x = ∑' x : ⋃ i : s, t i, f x := by rw [tsum_congr_subtype]; simp
  _ ≤ ∑' i : s, ∑' x : t i, f x := ENat.tsum_subtype_iUnion_le_tsum _ _

protected theorem tsum_subtype_biUnion_le (f : α → ℕ∞) (s : Finset ι) (t : ι → Set α) :
    ∑' x : ⋃ i ∈ s, t i, f x ≤ ∑ i ∈ s, ∑' x : t i, f x :=
  (ENat.tsum_subtype_biUnion_le_tsum f s.toSet t).trans_eq <|
    Finset.tsum_subtype s fun i ↦ ∑' x : t i, f x

protected theorem tsum_subtype_iUnion_le [Fintype ι] (f : α → ℕ∞) (t : ι → Set α) :
    ∑' x : ⋃ i, t i, f x ≤ ∑ i, ∑' x : t i, f x := by
  rw [← tsum_fintype]
  exact ENat.tsum_subtype_iUnion_le_tsum f t

theorem tsum_subtype_iUnion_eq_tsum (f : α → ℕ∞) (t : ι → Set α) (ht : Pairwise (Disjoint on t)) :
    ∑' x : ⋃ i, t i, f x = ∑' i, ∑' x : t i, f x :=
  calc ∑' x : ⋃ i, t i, f x = ∑' x : Σ i, t i, f x.2 :=
    (ENat.tsum_comp_eq_tsum_of_bijective (sigmaToiUnion_bijective t (fun _ _ hij ↦ ht hij)) _).symm
    _ = _ := ENat.tsum_subtype_sigma' _

end tsum

end ENat
