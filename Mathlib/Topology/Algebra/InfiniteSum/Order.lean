/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.Order.Archimedean
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Order.MonotoneConvergence

#align_import topology.algebra.infinite_sum.order from "leanprover-community/mathlib"@"32253a1a1071173b33dc7d6a218cf722c6feb514"

/-!
# Infinite sum in an order

This file provides lemmas about the interaction of infinite sums and order operations.
-/


open Finset Filter Function BigOperators
open scoped Classical

variable {ι κ α : Type*}

section Preorder

variable [Preorder α] [AddCommMonoid α] [TopologicalSpace α] [OrderClosedTopology α] [T2Space α]
  {f : ℕ → α} {c : α}

theorem tsum_le_of_sum_range_le (hf : Summable f) (h : ∀ n, ∑ i in range n, f i ≤ c) :
    ∑' n, f n ≤ c :=
  let ⟨_l, hl⟩ := hf
  hl.tsum_eq.symm ▸ le_of_tendsto' hl.tendsto_sum_nat h

end Preorder

section OrderedAddCommMonoid

variable [OrderedAddCommMonoid α] [TopologicalSpace α] [OrderClosedTopology α] {f g : ι → α}
  {a a₁ a₂ : α}

theorem hasSum_le (h : ∀ i, f i ≤ g i) (hf : HasSum f a₁) (hg : HasSum g a₂) : a₁ ≤ a₂ :=
  le_of_tendsto_of_tendsto' hf hg fun _ => sum_le_sum fun i _ => h i

@[mono]
theorem hasSum_mono (hf : HasSum f a₁) (hg : HasSum g a₂) (h : f ≤ g) : a₁ ≤ a₂ :=
  hasSum_le h hf hg

theorem hasSum_le_of_sum_le (hf : HasSum f a) (h : ∀ s, ∑ i in s, f i ≤ a₂) : a ≤ a₂ :=
  le_of_tendsto' hf h

theorem le_hasSum_of_le_sum (hf : HasSum f a) (h : ∀ s, a₂ ≤ ∑ i in s, f i) : a₂ ≤ a :=
  ge_of_tendsto' hf h

theorem hasSum_le_inj {g : κ → α} (e : ι → κ) (he : Injective e)
    (hs : ∀ c, c ∉ Set.range e → 0 ≤ g c) (h : ∀ i, f i ≤ g (e i)) (hf : HasSum f a₁)
    (hg : HasSum g a₂) : a₁ ≤ a₂ := by
  rw [← hasSum_extend_zero he] at hf
  refine hasSum_le (fun c => ?_) hf hg
  obtain ⟨i, rfl⟩ | h := em (c ∈ Set.range e)
  · rw [he.extend_apply]
    exact h _
  · rw [extend_apply' _ _ _ h]
    exact hs _ h

theorem tsum_le_tsum_of_inj {g : κ → α} (e : ι → κ) (he : Injective e)
    (hs : ∀ c, c ∉ Set.range e → 0 ≤ g c) (h : ∀ i, f i ≤ g (e i)) (hf : Summable f)
    (hg : Summable g) : tsum f ≤ tsum g :=
  hasSum_le_inj _ he hs h hf.hasSum hg.hasSum

theorem sum_le_hasSum (s : Finset ι) (hs : ∀ i, i ∉ s → 0 ≤ f i) (hf : HasSum f a) :
    ∑ i in s, f i ≤ a :=
  ge_of_tendsto hf (eventually_atTop.2
    ⟨s, fun _t hst => sum_le_sum_of_subset_of_nonneg hst fun i _ hbs => hs i hbs⟩)

theorem isLUB_hasSum (h : ∀ i, 0 ≤ f i) (hf : HasSum f a) :
    IsLUB (Set.range fun s => ∑ i in s, f i) a :=
  isLUB_of_tendsto_atTop (Finset.sum_mono_set_of_nonneg h) hf

theorem le_hasSum (hf : HasSum f a) (i : ι) (hb : ∀ j, j ≠ i → 0 ≤ f j) : f i ≤ a :=
  calc
    f i = ∑ i in {i}, f i := by rw [sum_singleton]
    _ ≤ a := sum_le_hasSum _ (by simpa) hf

theorem sum_le_tsum {f : ι → α} (s : Finset ι) (hs : ∀ i, i ∉ s → 0 ≤ f i) (hf : Summable f) :
    ∑ i in s, f i ≤ ∑' i, f i :=
  sum_le_hasSum s hs hf.hasSum

theorem le_tsum (hf : Summable f) (i : ι) (hb : ∀ j, j ≠ i → 0 ≤ f j) : f i ≤ ∑' i, f i :=
  le_hasSum hf.hasSum i hb

theorem tsum_le_tsum (h : ∀ i, f i ≤ g i) (hf : Summable f) (hg : Summable g) :
    ∑' i, f i ≤ ∑' i, g i :=
  hasSum_le h hf.hasSum hg.hasSum

@[mono]
theorem tsum_mono (hf : Summable f) (hg : Summable g) (h : f ≤ g) : ∑' n, f n ≤ ∑' n, g n :=
  tsum_le_tsum h hf hg

theorem tsum_le_of_sum_le (hf : Summable f) (h : ∀ s, ∑ i in s, f i ≤ a₂) : ∑' i, f i ≤ a₂ :=
  hasSum_le_of_sum_le hf.hasSum h

theorem tsum_le_of_sum_le' (ha₂ : 0 ≤ a₂) (h : ∀ s, ∑ i in s, f i ≤ a₂) : ∑' i, f i ≤ a₂ := by
  by_cases hf : Summable f
  · exact tsum_le_of_sum_le hf h
  · rw [tsum_eq_zero_of_not_summable hf]
    exact ha₂

theorem HasSum.nonneg (h : ∀ i, 0 ≤ g i) (ha : HasSum g a) : 0 ≤ a :=
  hasSum_le h hasSum_zero ha

theorem HasSum.nonpos (h : ∀ i, g i ≤ 0) (ha : HasSum g a) : a ≤ 0 :=
  hasSum_le h ha hasSum_zero

theorem tsum_nonneg (h : ∀ i, 0 ≤ g i) : 0 ≤ ∑' i, g i := by
  by_cases hg : Summable g
  · exact hg.hasSum.nonneg h
  · rw [tsum_eq_zero_of_not_summable hg]

theorem tsum_nonpos (h : ∀ i, f i ≤ 0) : ∑' i, f i ≤ 0 := by
  by_cases hf : Summable f
  · exact hf.hasSum.nonpos h
  · rw [tsum_eq_zero_of_not_summable hf]

-- porting note: generalized from `OrderedAddCommGroup` to `OrderedAddCommMonoid`
theorem hasSum_zero_iff_of_nonneg (hf : ∀ i, 0 ≤ f i) : HasSum f 0 ↔ f = 0 := by
  refine' ⟨fun hf' => _, _⟩
  · ext i
    exact (hf i).antisymm' (le_hasSum hf' _ fun j _ => hf j)
  · rintro rfl
    exact hasSum_zero

end OrderedAddCommMonoid

section OrderedAddCommGroup

variable [OrderedAddCommGroup α] [TopologicalSpace α] [TopologicalAddGroup α]
  [OrderClosedTopology α] {f g : ι → α} {a₁ a₂ : α} {i : ι}

theorem hasSum_lt (h : f ≤ g) (hi : f i < g i) (hf : HasSum f a₁) (hg : HasSum g a₂) : a₁ < a₂ := by
  have : update f i 0 ≤ update g i 0 := update_le_update_iff.mpr ⟨rfl.le, fun i _ => h i⟩
  have : 0 - f i + a₁ ≤ 0 - g i + a₂ := hasSum_le this (hf.update i 0) (hg.update i 0)
  simpa only [zero_sub, add_neg_cancel_left] using add_lt_add_of_lt_of_le hi this

@[mono]
theorem hasSum_strict_mono (hf : HasSum f a₁) (hg : HasSum g a₂) (h : f < g) : a₁ < a₂ :=
  let ⟨hle, _i, hi⟩ := Pi.lt_def.mp h
  hasSum_lt hle hi hf hg

theorem tsum_lt_tsum (h : f ≤ g) (hi : f i < g i) (hf : Summable f) (hg : Summable g) :
    ∑' n, f n < ∑' n, g n :=
  hasSum_lt h hi hf.hasSum hg.hasSum

@[mono]
theorem tsum_strict_mono (hf : Summable f) (hg : Summable g) (h : f < g) :
    ∑' n, f n < ∑' n, g n :=
  let ⟨hle, _i, hi⟩ := Pi.lt_def.mp h
  tsum_lt_tsum hle hi hf hg

theorem tsum_pos (hsum : Summable g) (hg : ∀ i, 0 ≤ g i) (i : ι) (hi : 0 < g i) :
    0 < ∑' i, g i := by
  rw [← tsum_zero]
  exact tsum_lt_tsum hg hi summable_zero hsum

end OrderedAddCommGroup

section CanonicallyOrderedAddCommMonoid

variable [CanonicallyOrderedAddCommMonoid α] [TopologicalSpace α] [OrderClosedTopology α]
  {f : ι → α} {a : α}

theorem le_hasSum' (hf : HasSum f a) (i : ι) : f i ≤ a :=
  le_hasSum hf i fun _ _ => zero_le _

theorem le_tsum' (hf : Summable f) (i : ι) : f i ≤ ∑' i, f i :=
  le_tsum hf i fun _ _ => zero_le _

theorem hasSum_zero_iff : HasSum f 0 ↔ ∀ x, f x = 0 :=
  (hasSum_zero_iff_of_nonneg fun _ => zero_le _).trans funext_iff

theorem tsum_eq_zero_iff (hf : Summable f) : ∑' i, f i = 0 ↔ ∀ x, f x = 0 := by
  rw [← hasSum_zero_iff, hf.hasSum_iff]

theorem tsum_ne_zero_iff (hf : Summable f) : ∑' i, f i ≠ 0 ↔ ∃ x, f x ≠ 0 := by
  rw [Ne.def, tsum_eq_zero_iff hf, not_forall]

theorem isLUB_hasSum' (hf : HasSum f a) : IsLUB (Set.range fun s => ∑ i in s, f i) a :=
  isLUB_of_tendsto_atTop (Finset.sum_mono_set f) hf

end CanonicallyOrderedAddCommMonoid

section LinearOrder

/-!
For infinite sums taking values in a linearly ordered monoid, the existence of a least upper
bound for the finite sums is a criterion for summability.

This criterion is useful when applied in a linearly ordered monoid which is also a complete or
conditionally complete linear order, such as `ℝ`, `ℝ≥0`, `ℝ≥0∞`, because it is then easy to check
the existence of a least upper bound.
-/

theorem hasSum_of_isLUB_of_nonneg [LinearOrderedAddCommMonoid α] [TopologicalSpace α]
    [OrderTopology α] {f : ι → α} (i : α) (h : ∀ i, 0 ≤ f i)
    (hf : IsLUB (Set.range fun s => ∑ i in s, f i) i) : HasSum f i :=
  tendsto_atTop_isLUB (Finset.sum_mono_set_of_nonneg h) hf

theorem hasSum_of_isLUB [CanonicallyLinearOrderedAddCommMonoid α] [TopologicalSpace α]
    [OrderTopology α] {f : ι → α} (b : α) (hf : IsLUB (Set.range fun s => ∑ i in s, f i) b) :
    HasSum f b :=
  tendsto_atTop_isLUB (Finset.sum_mono_set f) hf

theorem summable_abs_iff [LinearOrderedAddCommGroup α] [UniformSpace α] [UniformAddGroup α]
    [CompleteSpace α] {f : ι → α} : (Summable fun x => |f x|) ↔ Summable f :=
  let s := { x | 0 ≤ f x }
  have h1 : ∀ x : s, |f x| = f x := fun x => abs_of_nonneg x.2
  have h2 : ∀ x : ↑sᶜ, |f x| = -f x := fun x => abs_of_neg (not_le.1 x.2)
  calc (Summable fun x => |f x|) ↔
      (Summable fun x : s => |f x|) ∧ Summable fun x : ↑sᶜ => |f x| :=
        summable_subtype_and_compl.symm
  _ ↔ (Summable fun x : s => f x) ∧ Summable fun x : ↑sᶜ => -f x := by simp only [h1, h2]
  _ ↔ Summable f := by simp only [summable_neg_iff, summable_subtype_and_compl]

alias ⟨Summable.of_abs, Summable.abs⟩ := summable_abs_iff

theorem Finite.of_summable_const [LinearOrderedAddCommGroup α] [TopologicalSpace α] [Archimedean α]
    [OrderClosedTopology α] {b : α} (hb : 0 < b) (hf : Summable fun _ : ι => b) :
    Finite ι := by
  have H : ∀ s : Finset ι, s.card • b ≤ ∑' _ : ι, b := fun s => by
    simpa using sum_le_hasSum s (fun a _ => hb.le) hf.hasSum
  obtain ⟨n, hn⟩ := Archimedean.arch (∑' _ : ι, b) hb
  have : ∀ s : Finset ι, s.card ≤ n := fun s => by
    simpa [nsmul_le_nsmul_iff hb] using (H s).trans hn
  have : Fintype ι := fintypeOfFinsetCardLe n this
  infer_instance

theorem Set.Finite.of_summable_const [LinearOrderedAddCommGroup α] [TopologicalSpace α]
    [Archimedean α] [OrderClosedTopology α] {b : α} (hb : 0 < b) (hf : Summable fun _ : ι => b) :
    (Set.univ : Set ι).Finite :=
  finite_univ_iff.2 <| .of_summable_const hb hf

end LinearOrder

theorem Summable.tendsto_atTop_of_pos [LinearOrderedField α] [TopologicalSpace α] [OrderTopology α]
    {f : ℕ → α} (hf : Summable f⁻¹) (hf' : ∀ n, 0 < f n) : Tendsto f atTop atTop :=
  inv_inv f ▸ Filter.Tendsto.inv_tendsto_zero <|
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hf.tendsto_atTop_zero <|
      eventually_of_forall fun _ => inv_pos.2 (hf' _)
