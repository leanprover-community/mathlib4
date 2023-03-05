/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module topology.algebra.infinite_sum.order
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Archimedean
import Mathbin.Topology.Algebra.InfiniteSum.Basic
import Mathbin.Topology.Algebra.Order.Field
import Mathbin.Topology.Algebra.Order.MonotoneConvergence

/-!
# Infinite sum in an order

This file provides lemmas about the interaction of infinite sums and order operations.
-/


open Finset Filter Function

open BigOperators Classical

variable {ι κ α : Type _}

section Preorder

variable [Preorder α] [AddCommMonoid α] [TopologicalSpace α] [OrderClosedTopology α] [T2Space α]
  {f : ℕ → α} {c : α}

theorem tsum_le_of_sum_range_le (hf : Summable f) (h : ∀ n, (∑ i in range n, f i) ≤ c) :
    (∑' n, f n) ≤ c :=
  let ⟨l, hl⟩ := hf
  hl.tsum_eq.symm ▸ le_of_tendsto' hl.tendsto_sum_nat h
#align tsum_le_of_sum_range_le tsum_le_of_sum_range_le

end Preorder

section OrderedAddCommMonoid

variable [OrderedAddCommMonoid α] [TopologicalSpace α] [OrderClosedTopology α] {f g : ι → α}
  {a a₁ a₂ : α}

theorem hasSum_le (h : ∀ i, f i ≤ g i) (hf : HasSum f a₁) (hg : HasSum g a₂) : a₁ ≤ a₂ :=
  le_of_tendsto_of_tendsto' hf hg fun s => sum_le_sum fun i _ => h i
#align has_sum_le hasSum_le

@[mono]
theorem hasSum_mono (hf : HasSum f a₁) (hg : HasSum g a₂) (h : f ≤ g) : a₁ ≤ a₂ :=
  hasSum_le h hf hg
#align has_sum_mono hasSum_mono

theorem hasSum_le_of_sum_le (hf : HasSum f a) (h : ∀ s, (∑ i in s, f i) ≤ a₂) : a ≤ a₂ :=
  le_of_tendsto' hf h
#align has_sum_le_of_sum_le hasSum_le_of_sum_le

theorem le_hasSum_of_le_sum (hf : HasSum f a) (h : ∀ s, a₂ ≤ ∑ i in s, f i) : a₂ ≤ a :=
  ge_of_tendsto' hf h
#align le_has_sum_of_le_sum le_hasSum_of_le_sum

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (c «expr ∉ » set.range[set.range] e) -/
theorem hasSum_le_inj {g : κ → α} (e : ι → κ) (he : Injective e)
    (hs : ∀ (c) (_ : c ∉ Set.range e), 0 ≤ g c) (h : ∀ i, f i ≤ g (e i)) (hf : HasSum f a₁)
    (hg : HasSum g a₂) : a₁ ≤ a₂ :=
  by
  have : HasSum (fun c => (partialInv e c).casesOn' 0 f) a₁ :=
    by
    refine'
      (hasSum_iff_hasSum_of_ne_zero_bij (e ∘ coe) (fun c₁ c₂ hc => he hc) (fun c hc => _) _).2 hf
    · rw [mem_support] at hc
      cases' eq : partial_inv e c with i <;> rw [Eq] at hc
      · contradiction
      · rw [partial_inv_of_injective he] at eq
        exact ⟨⟨i, hc⟩, Eq⟩
    · rintro c
      simp [partial_inv_left he, Option.casesOn']
  refine' hasSum_le (fun c => _) this hg
  obtain ⟨i, rfl⟩ | h := em (c ∈ Set.range e)
  · rw [partial_inv_left he, Option.casesOn']
    exact h _
  · have : partial_inv e c = none := dif_neg h
    rw [this, Option.casesOn']
    exact hs _ h
#align has_sum_le_inj hasSum_le_inj

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (c «expr ∉ » set.range[set.range] e) -/
theorem tsum_le_tsum_of_inj {g : κ → α} (e : ι → κ) (he : Injective e)
    (hs : ∀ (c) (_ : c ∉ Set.range e), 0 ≤ g c) (h : ∀ i, f i ≤ g (e i)) (hf : Summable f)
    (hg : Summable g) : tsum f ≤ tsum g :=
  hasSum_le_inj _ he hs h hf.HasSum hg.HasSum
#align tsum_le_tsum_of_inj tsum_le_tsum_of_inj

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (i «expr ∉ » s) -/
theorem sum_le_hasSum (s : Finset ι) (hs : ∀ (i) (_ : i ∉ s), 0 ≤ f i) (hf : HasSum f a) :
    (∑ i in s, f i) ≤ a :=
  ge_of_tendsto hf
    (eventually_atTop.2
      ⟨s, fun t hst => sum_le_sum_of_subset_of_nonneg hst fun i hbt hbs => hs i hbs⟩)
#align sum_le_has_sum sum_le_hasSum

theorem isLUB_hasSum (h : ∀ i, 0 ≤ f i) (hf : HasSum f a) :
    IsLUB (Set.range fun s => ∑ i in s, f i) a :=
  isLUB_of_tendsto_atTop (Finset.sum_mono_set_of_nonneg h) hf
#align is_lub_has_sum isLUB_hasSum

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (b' «expr ≠ » i) -/
theorem le_hasSum (hf : HasSum f a) (i : ι) (hb : ∀ (b') (_ : b' ≠ i), 0 ≤ f b') : f i ≤ a :=
  calc
    f i = ∑ i in {i}, f i := Finset.sum_singleton.symm
    _ ≤ a :=
      sum_le_hasSum _
        (by
          convert hb
          simp)
        hf
    
#align le_has_sum le_hasSum

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (i «expr ∉ » s) -/
theorem sum_le_tsum {f : ι → α} (s : Finset ι) (hs : ∀ (i) (_ : i ∉ s), 0 ≤ f i) (hf : Summable f) :
    (∑ i in s, f i) ≤ ∑' i, f i :=
  sum_le_hasSum s hs hf.HasSum
#align sum_le_tsum sum_le_tsum

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (b' «expr ≠ » i) -/
theorem le_tsum (hf : Summable f) (i : ι) (hb : ∀ (b') (_ : b' ≠ i), 0 ≤ f b') : f i ≤ ∑' i, f i :=
  le_hasSum (Summable.hasSum hf) i hb
#align le_tsum le_tsum

theorem tsum_le_tsum (h : ∀ i, f i ≤ g i) (hf : Summable f) (hg : Summable g) :
    (∑' i, f i) ≤ ∑' i, g i :=
  hasSum_le h hf.HasSum hg.HasSum
#align tsum_le_tsum tsum_le_tsum

@[mono]
theorem tsum_mono (hf : Summable f) (hg : Summable g) (h : f ≤ g) : (∑' n, f n) ≤ ∑' n, g n :=
  tsum_le_tsum h hf hg
#align tsum_mono tsum_mono

theorem tsum_le_of_sum_le (hf : Summable f) (h : ∀ s, (∑ i in s, f i) ≤ a₂) : (∑' i, f i) ≤ a₂ :=
  hasSum_le_of_sum_le hf.HasSum h
#align tsum_le_of_sum_le tsum_le_of_sum_le

theorem tsum_le_of_sum_le' (ha₂ : 0 ≤ a₂) (h : ∀ s, (∑ i in s, f i) ≤ a₂) : (∑' i, f i) ≤ a₂ :=
  by
  by_cases hf : Summable f
  · exact tsum_le_of_sum_le hf h
  · rw [tsum_eq_zero_of_not_summable hf]
    exact ha₂
#align tsum_le_of_sum_le' tsum_le_of_sum_le'

theorem HasSum.nonneg (h : ∀ i, 0 ≤ g i) (ha : HasSum g a) : 0 ≤ a :=
  hasSum_le h hasSum_zero ha
#align has_sum.nonneg HasSum.nonneg

theorem HasSum.nonpos (h : ∀ i, g i ≤ 0) (ha : HasSum g a) : a ≤ 0 :=
  hasSum_le h ha hasSum_zero
#align has_sum.nonpos HasSum.nonpos

theorem tsum_nonneg (h : ∀ i, 0 ≤ g i) : 0 ≤ ∑' i, g i :=
  by
  by_cases hg : Summable g
  · exact hg.has_sum.nonneg h
  · simp [tsum_eq_zero_of_not_summable hg]
#align tsum_nonneg tsum_nonneg

theorem tsum_nonpos (h : ∀ i, f i ≤ 0) : (∑' i, f i) ≤ 0 :=
  by
  by_cases hf : Summable f
  · exact hf.has_sum.nonpos h
  · simp [tsum_eq_zero_of_not_summable hf]
#align tsum_nonpos tsum_nonpos

end OrderedAddCommMonoid

section OrderedAddCommGroup

variable [OrderedAddCommGroup α] [TopologicalSpace α] [TopologicalAddGroup α]
  [OrderClosedTopology α] {f g : ι → α} {a₁ a₂ : α} {i : ι}

theorem hasSum_lt (h : f ≤ g) (hi : f i < g i) (hf : HasSum f a₁) (hg : HasSum g a₂) : a₁ < a₂ :=
  by
  have : update f i 0 ≤ update g i 0 := update_le_update_iff.mpr ⟨rfl.le, fun i _ => h i⟩
  have : 0 - f i + a₁ ≤ 0 - g i + a₂ := hasSum_le this (hf.update i 0) (hg.update i 0)
  simpa only [zero_sub, add_neg_cancel_left] using add_lt_add_of_lt_of_le hi this
#align has_sum_lt hasSum_lt

@[mono]
theorem hasSum_strict_mono (hf : HasSum f a₁) (hg : HasSum g a₂) (h : f < g) : a₁ < a₂ :=
  let ⟨hle, i, hi⟩ := Pi.lt_def.mp h
  hasSum_lt hle hi hf hg
#align has_sum_strict_mono hasSum_strict_mono

theorem tsum_lt_tsum (h : f ≤ g) (hi : f i < g i) (hf : Summable f) (hg : Summable g) :
    (∑' n, f n) < ∑' n, g n :=
  hasSum_lt h hi hf.HasSum hg.HasSum
#align tsum_lt_tsum tsum_lt_tsum

@[mono]
theorem tsum_strict_mono (hf : Summable f) (hg : Summable g) (h : f < g) :
    (∑' n, f n) < ∑' n, g n :=
  let ⟨hle, i, hi⟩ := Pi.lt_def.mp h
  tsum_lt_tsum hle hi hf hg
#align tsum_strict_mono tsum_strict_mono

theorem tsum_pos (hsum : Summable g) (hg : ∀ i, 0 ≤ g i) (i : ι) (hi : 0 < g i) : 0 < ∑' i, g i :=
  by
  rw [← tsum_zero]
  exact tsum_lt_tsum hg hi summable_zero hsum
#align tsum_pos tsum_pos

theorem hasSum_zero_iff_of_nonneg (hf : ∀ i, 0 ≤ f i) : HasSum f 0 ↔ f = 0 :=
  by
  refine' ⟨fun hf' => _, _⟩
  · ext i
    refine' (hf i).eq_of_not_gt fun hi => _
    simpa using hasSum_lt hf hi hasSum_zero hf'
  · rintro rfl
    exact hasSum_zero
#align has_sum_zero_iff_of_nonneg hasSum_zero_iff_of_nonneg

end OrderedAddCommGroup

section CanonicallyOrderedAddMonoid

variable [CanonicallyOrderedAddMonoid α] [TopologicalSpace α] [OrderClosedTopology α] {f : ι → α}
  {a : α}

theorem le_has_sum' (hf : HasSum f a) (i : ι) : f i ≤ a :=
  le_hasSum hf i fun _ _ => zero_le _
#align le_has_sum' le_has_sum'

theorem le_tsum' (hf : Summable f) (i : ι) : f i ≤ ∑' i, f i :=
  le_tsum hf i fun _ _ => zero_le _
#align le_tsum' le_tsum'

theorem hasSum_zero_iff : HasSum f 0 ↔ ∀ x, f x = 0 :=
  by
  refine' ⟨_, fun h => _⟩
  · contrapose!
    exact fun ⟨x, hx⟩ h => hx (nonpos_iff_eq_zero.1 <| le_has_sum' h x)
  · convert hasSum_zero
    exact funext h
#align has_sum_zero_iff hasSum_zero_iff

theorem tsum_eq_zero_iff (hf : Summable f) : (∑' i, f i) = 0 ↔ ∀ x, f x = 0 := by
  rw [← hasSum_zero_iff, hf.has_sum_iff]
#align tsum_eq_zero_iff tsum_eq_zero_iff

theorem tsum_ne_zero_iff (hf : Summable f) : (∑' i, f i) ≠ 0 ↔ ∃ x, f x ≠ 0 := by
  rw [Ne.def, tsum_eq_zero_iff hf, not_forall]
#align tsum_ne_zero_iff tsum_ne_zero_iff

theorem isLUB_has_sum' (hf : HasSum f a) : IsLUB (Set.range fun s => ∑ i in s, f i) a :=
  isLUB_of_tendsto_atTop (Finset.sum_mono_set f) hf
#align is_lub_has_sum' isLUB_has_sum'

end CanonicallyOrderedAddMonoid

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
#align has_sum_of_is_lub_of_nonneg hasSum_of_isLUB_of_nonneg

theorem hasSum_of_isLUB [CanonicallyLinearOrderedAddMonoid α] [TopologicalSpace α] [OrderTopology α]
    {f : ι → α} (b : α) (hf : IsLUB (Set.range fun s => ∑ i in s, f i) b) : HasSum f b :=
  tendsto_atTop_isLUB (Finset.sum_mono_set f) hf
#align has_sum_of_is_lub hasSum_of_isLUB

theorem summable_abs_iff [LinearOrderedAddCommGroup α] [UniformSpace α] [UniformAddGroup α]
    [CompleteSpace α] {f : ι → α} : (Summable fun x => |f x|) ↔ Summable f :=
  have h1 : ∀ x : { x | 0 ≤ f x }, |f x| = f x := fun x => abs_of_nonneg x.2
  have h2 : ∀ x : { x | 0 ≤ f x }ᶜ, |f x| = -f x := fun x => abs_of_neg (not_le.1 x.2)
  calc
    (Summable fun x => |f x|) ↔
        (Summable fun x : { x | 0 ≤ f x } => |f x|) ∧ Summable fun x : { x | 0 ≤ f x }ᶜ => |f x| :=
      summable_subtype_and_compl.symm
    _ ↔ (Summable fun x : { x | 0 ≤ f x } => f x) ∧ Summable fun x : { x | 0 ≤ f x }ᶜ => -f x := by
      simp only [h1, h2]
    _ ↔ _ := by simp only [summable_neg_iff, summable_subtype_and_compl]
    
#align summable_abs_iff summable_abs_iff

alias summable_abs_iff ↔ Summable.of_abs Summable.abs
#align summable.of_abs Summable.of_abs
#align summable.abs Summable.abs

--TODO: Change the conclusion to `finite ι`
theorem finite_of_summable_const [LinearOrderedAddCommGroup α] [TopologicalSpace α] [Archimedean α]
    [OrderClosedTopology α] {b : α} (hb : 0 < b) (hf : Summable fun i : ι => b) :
    (Set.univ : Set ι).Finite :=
  by
  have H : ∀ s : Finset ι, s.card • b ≤ ∑' i : ι, b :=
    by
    intro s
    simpa using sum_le_hasSum s (fun a ha => hb.le) hf.has_sum
  obtain ⟨n, hn⟩ := Archimedean.arch (∑' i : ι, b) hb
  have : ∀ s : Finset ι, s.card ≤ n := by
    intro s
    simpa [nsmul_le_nsmul_iff hb] using (H s).trans hn
  haveI : Fintype ι := fintypeOfFinsetCardLe n this
  exact Set.finite_univ
#align finite_of_summable_const finite_of_summable_const

end LinearOrder

theorem Summable.tendsto_top_of_pos [LinearOrderedField α] [TopologicalSpace α] [OrderTopology α]
    {f : ℕ → α} (hf : Summable f⁻¹) (hf' : ∀ n, 0 < f n) : Tendsto f atTop atTop :=
  by
  rw [← inv_inv f]
  apply Filter.Tendsto.inv_tendsto_zero
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (Summable.tendsto_atTop_zero hf)
  rw [eventually_iff_exists_mem]
  refine' ⟨Set.Ioi 0, Ioi_mem_at_top _, fun _ _ => _⟩
  rw [Set.mem_Ioi, inv_eq_one_div, one_div, Pi.inv_apply, _root_.inv_pos]
  exact hf' _
#align summable.tendsto_top_of_pos Summable.tendsto_top_of_pos

