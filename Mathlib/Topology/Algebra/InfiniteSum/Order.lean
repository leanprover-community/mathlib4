/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Infinite sum or product in an order

This file provides lemmas about the interaction of infinite sums and products and order operations.
-/

open Finset Filter Function

variable {ι κ α : Type*}

section Preorder

variable [Preorder α] [CommMonoid α] [TopologicalSpace α] {a c : α} {f : ι → α}

@[to_additive]
lemma hasProd_le_of_prod_le [ClosedIicTopology α]
    (hf : HasProd f a) (h : ∀ s, ∏ i ∈ s, f i ≤ c) : a ≤ c :=
  le_of_tendsto' hf h

@[to_additive]
theorem le_hasProd_of_le_prod [ClosedIciTopology α]
    (hf : HasProd f a) (h : ∀ s, c ≤ ∏ i ∈ s, f i) : c ≤ a :=
  ge_of_tendsto' hf h

@[to_additive]
protected theorem Multipliable.tprod_le_of_prod_range_le [ClosedIicTopology α] {f : ℕ → α}
    (hf : Multipliable f) (h : ∀ n, ∏ i ∈ range n, f i ≤ c) : ∏' n, f n ≤ c :=
  le_of_tendsto' hf.hasProd.tendsto_prod_nat h

@[deprecated (since := "2025-04-12")] alias tsum_le_of_sum_range_le :=
  Summable.tsum_le_of_sum_range_le
@[to_additive existing, deprecated (since := "2025-04-12")] alias tprod_le_of_prod_range_le :=
  Multipliable.tprod_le_of_prod_range_le

end Preorder

section OrderedCommMonoid

variable [CommMonoid α] [PartialOrder α] [IsOrderedMonoid α]
  [TopologicalSpace α] [OrderClosedTopology α] {f g : ι → α}
  {a a₁ a₂ : α}

@[to_additive]
theorem hasProd_le (h : ∀ i, f i ≤ g i) (hf : HasProd f a₁) (hg : HasProd g a₂) : a₁ ≤ a₂ :=
  le_of_tendsto_of_tendsto' hf hg fun _ ↦ prod_le_prod' fun i _ ↦ h i

@[to_additive]
theorem hasProd_mono (hf : HasProd f a₁) (hg : HasProd g a₂) (h : f ≤ g) : a₁ ≤ a₂ :=
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

@[deprecated (since := "2025-04-12")] alias tsum_le_tsum_of_inj := Summable.tsum_le_tsum_of_inj
@[to_additive existing, deprecated (since := "2025-04-12")] alias tprod_le_tprod_of_inj :=
  Multipliable.tprod_le_tprod_of_inj

@[to_additive]
protected lemma Multipliable.tprod_subtype_le {κ γ : Type*} [CommGroup γ] [PartialOrder γ]
    [IsOrderedMonoid γ] [UniformSpace γ] [IsUniformGroup γ] [OrderClosedTopology γ]
    [CompleteSpace γ] (f : κ → γ) (β : Set κ) (h : ∀ a : κ, 1 ≤ f a) (hf : Multipliable f) :
    (∏' (b : β), f b) ≤ (∏' (a : κ), f a) := by
  apply Multipliable.tprod_le_tprod_of_inj _
    (Subtype.coe_injective)
    (by simp only [Subtype.range_coe_subtype, Set.setOf_mem_eq, h, implies_true])
    (by simp only [le_refl, Subtype.forall, implies_true])
    (by apply hf.subtype)
  apply hf

@[deprecated (since := "2025-04-12")] alias tsum_subtype_le := Summable.tsum_subtype_le
@[to_additive existing, deprecated (since := "2025-04-12")] alias tprod_subtype_le :=
  Multipliable.tprod_subtype_le

@[to_additive]
theorem prod_le_hasProd (s : Finset ι) (hs : ∀ i, i ∉ s → 1 ≤ f i) (hf : HasProd f a) :
    ∏ i ∈ s, f i ≤ a :=
  ge_of_tendsto hf (eventually_atTop.2
    ⟨s, fun _t hst ↦ prod_le_prod_of_subset_of_one_le' hst fun i _ hbs ↦ hs i hbs⟩)

@[to_additive]
theorem isLUB_hasProd (h : ∀ i, 1 ≤ f i) (hf : HasProd f a) :
    IsLUB (Set.range fun s ↦ ∏ i ∈ s, f i) a := by
  classical
  exact isLUB_of_tendsto_atTop (Finset.prod_mono_set_of_one_le' h) hf

@[to_additive]
theorem le_hasProd (hf : HasProd f a) (i : ι) (hb : ∀ j, j ≠ i → 1 ≤ f j) : f i ≤ a :=
  calc
    f i = ∏ i ∈ {i}, f i := by rw [prod_singleton]
    _ ≤ a := prod_le_hasProd _ (by simpa) hf

@[to_additive]
theorem lt_hasProd [MulRightStrictMono α] (hf : HasProd f a) (i : ι)
    (hi : ∀ (j : ι), j ≠ i → 1 ≤ f j) (j : ι) (hij : j ≠ i) (hj : 1 < f j) :
    f i < a := by
  classical
  calc
    f i < f j * f i := lt_mul_of_one_lt_left' (f i) hj
    _ = ∏ k ∈ {j, i}, f k := by rw [Finset.prod_pair hij]
    _ ≤ a := prod_le_hasProd _ (fun k hk ↦ hi k (hk ∘ mem_insert_of_mem ∘ mem_singleton.mpr)) hf

@[to_additive]
protected theorem Multipliable.prod_le_tprod {f : ι → α} (s : Finset ι) (hs : ∀ i, i ∉ s → 1 ≤ f i)
    (hf : Multipliable f) : ∏ i ∈ s, f i ≤ ∏' i, f i :=
  prod_le_hasProd s hs hf.hasProd

@[deprecated (since := "2025-04-12")] alias sum_le_tsum := Summable.sum_le_tsum
@[to_additive existing, deprecated (since := "2025-04-12")] alias prod_le_tprod :=
  Multipliable.prod_le_tprod

@[to_additive]
protected theorem Multipliable.le_tprod (hf : Multipliable f) (i : ι) (hb : ∀ j, j ≠ i → 1 ≤ f j) :
    f i ≤ ∏' i, f i :=
  le_hasProd hf.hasProd i hb

@[deprecated (since := "2025-04-12")] alias le_tsum := Summable.le_tsum
@[to_additive existing, deprecated (since := "2025-04-12")] alias le_tprod := Multipliable.le_tprod

@[to_additive (attr := gcongr)]
protected theorem Multipliable.tprod_le_tprod (h : ∀ i, f i ≤ g i) (hf : Multipliable f)
    (hg : Multipliable g) : ∏' i, f i ≤ ∏' i, g i :=
  hasProd_le h hf.hasProd hg.hasProd

@[deprecated (since := "2025-04-12")] alias tsum_le_tsum := Summable.tsum_le_tsum
@[to_additive existing, deprecated (since := "2025-04-12")] alias tprod_le_tprod :=
  Multipliable.tprod_le_tprod

@[to_additive (attr := mono)]
protected theorem Multipliable.tprod_mono (hf : Multipliable f) (hg : Multipliable g) (h : f ≤ g) :
    ∏' n, f n ≤ ∏' n, g n :=
  hf.tprod_le_tprod h hg

@[deprecated (since := "2025-04-12")] alias tsum_mono := Summable.tsum_mono
@[to_additive existing (attr := mono), deprecated (since := "2025-04-12")] alias tprod_mono :=
  Multipliable.tprod_mono

omit [IsOrderedMonoid α] in
@[to_additive]
protected theorem Multipliable.tprod_le_of_prod_le (hf : Multipliable f)
    (h : ∀ s, ∏ i ∈ s, f i ≤ a₂) : ∏' i, f i ≤ a₂ :=
  hasProd_le_of_prod_le hf.hasProd h

@[deprecated (since := "2025-04-12")] alias tsum_le_of_sum_le := Summable.tsum_le_of_sum_le
@[to_additive existing, deprecated (since := "2025-04-12")] alias tprod_le_of_prod_le :=
  Multipliable.tprod_le_of_prod_le

omit [IsOrderedMonoid α] in
@[to_additive]
theorem tprod_le_of_prod_le' (ha₂ : 1 ≤ a₂) (h : ∀ s, ∏ i ∈ s, f i ≤ a₂) : ∏' i, f i ≤ a₂ := by
  by_cases hf : Multipliable f
  · exact hf.tprod_le_of_prod_le h
  · rw [tprod_eq_one_of_not_multipliable hf]
    exact ha₂

@[to_additive]
theorem HasProd.one_le (h : ∀ i, 1 ≤ g i) (ha : HasProd g a) : 1 ≤ a :=
  hasProd_le h hasProd_one ha

@[to_additive]
theorem HasProd.le_one (h : ∀ i, g i ≤ 1) (ha : HasProd g a) : a ≤ 1 :=
  hasProd_le h ha hasProd_one

@[to_additive tsum_nonneg]
theorem one_le_tprod (h : ∀ i, 1 ≤ g i) : 1 ≤ ∏' i, g i := by
  by_cases hg : Multipliable g
  · exact hg.hasProd.one_le h
  · rw [tprod_eq_one_of_not_multipliable hg]

@[to_additive]
theorem tprod_le_one (h : ∀ i, f i ≤ 1) : ∏' i, f i ≤ 1 := by
  by_cases hf : Multipliable f
  · exact hf.hasProd.le_one h
  · rw [tprod_eq_one_of_not_multipliable hf]

@[to_additive]
theorem hasProd_one_iff_of_one_le (hf : ∀ i, 1 ≤ f i) : HasProd f 1 ↔ f = 1 := by
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
theorem hasProd_lt (h : f ≤ g) (hi : f i < g i) (hf : HasProd f a₁) (hg : HasProd g a₂) :
    a₁ < a₂ := by
  classical
  have : update f i 1 ≤ update g i 1 := update_le_update_iff.mpr ⟨rfl.le, fun i _ ↦ h i⟩
  have : 1 / f i * a₁ ≤ 1 / g i * a₂ := hasProd_le this (hf.update i 1) (hg.update i 1)
  simpa only [one_div, mul_inv_cancel_left] using mul_lt_mul_of_lt_of_le hi this

@[to_additive (attr := mono)]
theorem hasProd_strict_mono (hf : HasProd f a₁) (hg : HasProd g a₂) (h : f < g) : a₁ < a₂ :=
  let ⟨hle, _i, hi⟩ := Pi.lt_def.mp h
  hasProd_lt hle hi hf hg

@[to_additive]
protected theorem Multipliable.tprod_lt_tprod (h : f ≤ g) (hi : f i < g i) (hf : Multipliable f)
    (hg : Multipliable g) : ∏' n, f n < ∏' n, g n :=
  hasProd_lt h hi hf.hasProd hg.hasProd

@[deprecated (since := "2025-04-12")] alias tsum_lt_tsum := Summable.tsum_lt_tsum
@[to_additive existing, deprecated (since := "2025-04-12")] alias tprod_lt_tprod :=
  Multipliable.tprod_lt_tprod

@[to_additive (attr := mono)]
protected theorem Multipliable.tprod_strict_mono (hf : Multipliable f) (hg : Multipliable g)
    (h : f < g) : ∏' n, f n < ∏' n, g n :=
  let ⟨hle, _i, hi⟩ := Pi.lt_def.mp h
  hf.tprod_lt_tprod hle hi hg

@[deprecated (since := "2025-04-12")] alias tsum_strict_mono := Summable.tsum_strict_mono
@[to_additive existing (attr := mono), deprecated (since := "2025-04-12")] alias
  tprod_strict_mono := Multipliable.tprod_strict_mono

@[to_additive Summable.tsum_pos]
protected theorem Multipliable.one_lt_tprod (hsum : Multipliable g) (hg : ∀ i, 1 ≤ g i) (i : ι)
    (hi : 1 < g i) : 1 < ∏' i, g i := by
  rw [← tprod_one]
  exact multipliable_one.tprod_lt_tprod hg hi hsum

@[deprecated (since := "2025-04-12")] alias tsum_pos := Summable.tsum_pos
@[to_additive existing tsum_pos, deprecated (since := "2025-04-12")] alias one_lt_tprod :=
  Multipliable.one_lt_tprod

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

@[deprecated (since := "2025-04-12")] alias le_tsum' := Summable.le_tsum'
@[to_additive existing, deprecated (since := "2025-04-12")] alias le_tprod' :=
  Multipliable.le_tprod'

@[to_additive]
theorem hasProd_one_iff : HasProd f 1 ↔ ∀ x, f x = 1 :=
  (hasProd_one_iff_of_one_le fun _ ↦ one_le _).trans funext_iff

@[to_additive]
protected theorem Multipliable.tprod_eq_one_iff (hf : Multipliable f) :
    ∏' i, f i = 1 ↔ ∀ x, f x = 1 := by
  rw [← hasProd_one_iff, hf.hasProd_iff]

@[deprecated (since := "2025-04-12")] alias tsum_eq_zero_iff := Summable.tsum_eq_zero_iff
@[to_additive existing, deprecated (since := "2025-04-12")] alias tprod_eq_one_iff :=
  Multipliable.tprod_eq_one_iff

@[to_additive]
protected theorem Multipliable.tprod_ne_one_iff (hf : Multipliable f) :
    ∏' i, f i ≠ 1 ↔ ∃ x, f x ≠ 1 := by
  rw [Ne, hf.tprod_eq_one_iff, not_forall]

@[deprecated (since := "2025-04-12")] alias tsum_ne_zero_iff := Summable.tsum_ne_zero_iff
@[to_additive existing, deprecated (since := "2025-04-12")] alias tprod_ne_one_iff :=
  Multipliable.tprod_ne_one_iff

@[to_additive]
theorem isLUB_hasProd' (hf : HasProd f a) : IsLUB (Set.range fun s ↦ ∏ i ∈ s, f i) a := by
  classical
  exact isLUB_of_tendsto_atTop (Finset.prod_mono_set' f) hf

end CanonicallyOrderedMul

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
theorem hasProd_of_isLUB [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α]
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

@[deprecated (since := "2025-04-12")] alias abs_tprod := Multipliable.abs_tprod

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
def evalTsum : PositivityExt where eval {u α} zα pα e := do
  match e with
  | ~q(@tsum _ $instCommMonoid $instTopSpace $ι $f) =>
    lambdaBoundedTelescope f 1 fun args (body : Q($α)) => do
      let #[(i : Q($ι))] := args | failure
      let rbody ← core zα pα body
      let pbody ← rbody.toNonneg
      let pr : Q(∀ i, 0 ≤ $f i) ← mkLambdaFVars #[i] pbody
      let mα' ← synthInstanceQ q(AddCommMonoid $α)
      let oα' ← synthInstanceQ q(PartialOrder $α)
      let pα' ← synthInstanceQ q(IsOrderedAddMonoid $α)
      let instOrderClosed ← synthInstanceQ q(OrderClosedTopology $α)
      assertInstancesCommute
      return .nonnegative q(@tsum_nonneg $ι $α $mα' $oα' $pα' $instTopSpace $instOrderClosed $f $pr)
  | _ => throwError "not tsum"

end Mathlib.Meta.Positivity
