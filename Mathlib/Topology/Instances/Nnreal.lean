/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module topology.instances.nnreal
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.InfiniteSum.Order
import Mathbin.Topology.Algebra.InfiniteSum.Ring
import Mathbin.Topology.Instances.Real

/-!
# Topology on `ℝ≥0`

The natural topology on `ℝ≥0` (the one induced from `ℝ`), and a basic API.

## Main definitions

Instances for the following typeclasses are defined:

* `topological_space ℝ≥0`
* `topological_semiring ℝ≥0`
* `second_countable_topology ℝ≥0`
* `order_topology ℝ≥0`
* `has_continuous_sub ℝ≥0`
* `has_continuous_inv₀ ℝ≥0` (continuity of `x⁻¹` away from `0`)
* `has_continuous_smul ℝ≥0 α` (whenever `α` has a continuous `mul_action ℝ α`)

Everything is inherited from the corresponding structures on the reals.

## Main statements

Various mathematically trivial lemmas are proved about the compatibility
of limits and sums in `ℝ≥0` and `ℝ`. For example

* `tendsto_coe {f : filter α} {m : α → ℝ≥0} {x : ℝ≥0} :
  tendsto (λa, (m a : ℝ)) f (𝓝 (x : ℝ)) ↔ tendsto m f (𝓝 x)`

says that the limit of a filter along a map to `ℝ≥0` is the same in `ℝ` and `ℝ≥0`, and

* `coe_tsum {f : α → ℝ≥0} : ((∑'a, f a) : ℝ) = (∑'a, (f a : ℝ))`

says that says that a sum of elements in `ℝ≥0` is the same in `ℝ` and `ℝ≥0`.

Similarly, some mathematically trivial lemmas about infinite sums are proved,
a few of which rely on the fact that subtraction is continuous.

-/


noncomputable section

open Set TopologicalSpace Metric Filter

open Topology

namespace NNReal

open NNReal BigOperators Filter

instance : TopologicalSpace ℝ≥0 :=
  inferInstance

-- short-circuit type class inference
instance : TopologicalSemiring ℝ≥0
    where
  continuous_mul := (continuous_subtype_val.fst'.mul continuous_subtype_val.snd').subtype_mk _
  continuous_add := (continuous_subtype_val.fst'.add continuous_subtype_val.snd').subtype_mk _

instance : SecondCountableTopology ℝ≥0 :=
  TopologicalSpace.Subtype.secondCountableTopology _ _

instance : OrderTopology ℝ≥0 :=
  @orderTopology_of_ordConnected _ _ _ _ (Ici 0) _

section coe

variable {α : Type _}

open Filter Finset

theorem continuous_real_toNNReal : Continuous Real.toNNReal :=
  (continuous_id.max continuous_const).subtype_mk _
#align continuous_real_to_nnreal continuous_real_toNNReal

theorem continuous_coe : Continuous (coe : ℝ≥0 → ℝ) :=
  continuous_subtype_val
#align nnreal.continuous_coe NNReal.continuous_coe

/-- Embedding of `ℝ≥0` to `ℝ` as a bundled continuous map. -/
@[simps (config := { fullyApplied := false })]
def ContinuousMap.coeNnrealReal : C(ℝ≥0, ℝ) :=
  ⟨coe, continuous_coe⟩
#align continuous_map.coe_nnreal_real ContinuousMap.coeNnrealReal

instance ContinuousMap.canLift {X : Type _} [TopologicalSpace X] :
    CanLift C(X, ℝ) C(X, ℝ≥0) ContinuousMap.coeNnrealReal.comp fun f => ∀ x, 0 ≤ f x
    where prf f hf := ⟨⟨fun x => ⟨f x, hf x⟩, f.2.subtype_mk _⟩, FunLike.ext' rfl⟩
#align nnreal.continuous_map.can_lift NNReal.ContinuousMap.canLift

@[simp, norm_cast]
theorem tendsto_coe {f : Filter α} {m : α → ℝ≥0} {x : ℝ≥0} :
    Tendsto (fun a => (m a : ℝ)) f (𝓝 (x : ℝ)) ↔ Tendsto m f (𝓝 x) :=
  tendsto_subtype_rng.symm
#align nnreal.tendsto_coe NNReal.tendsto_coe

theorem tendsto_coe' {f : Filter α} [NeBot f] {m : α → ℝ≥0} {x : ℝ} :
    Tendsto (fun a => m a : α → ℝ) f (𝓝 x) ↔ ∃ hx : 0 ≤ x, Tendsto m f (𝓝 ⟨x, hx⟩) :=
  ⟨fun h => ⟨ge_of_tendsto' h fun c => (m c).2, tendsto_coe.1 h⟩, fun ⟨hx, hm⟩ => tendsto_coe.2 hm⟩
#align nnreal.tendsto_coe' NNReal.tendsto_coe'

@[simp]
theorem map_coe_atTop : map (coe : ℝ≥0 → ℝ) atTop = atTop :=
  map_val_Ici_atTop 0
#align nnreal.map_coe_at_top NNReal.map_coe_atTop

theorem comap_coe_atTop : comap (coe : ℝ≥0 → ℝ) atTop = atTop :=
  (atTop_Ici_eq 0).symm
#align nnreal.comap_coe_at_top NNReal.comap_coe_atTop

@[simp, norm_cast]
theorem tendsto_coe_atTop {f : Filter α} {m : α → ℝ≥0} :
    Tendsto (fun a => (m a : ℝ)) f atTop ↔ Tendsto m f atTop :=
  tendsto_Ici_atTop.symm
#align nnreal.tendsto_coe_at_top NNReal.tendsto_coe_atTop

theorem tendsto_real_toNNReal {f : Filter α} {m : α → ℝ} {x : ℝ} (h : Tendsto m f (𝓝 x)) :
    Tendsto (fun a => Real.toNNReal (m a)) f (𝓝 (Real.toNNReal x)) :=
  (continuous_real_toNNReal.Tendsto _).comp h
#align tendsto_real_to_nnreal tendsto_real_toNNReal

theorem tendsto_real_toNNReal_atTop : Tendsto Real.toNNReal atTop atTop :=
  by
  rw [← tendsto_coe_at_top]
  apply tendsto_id.congr' _
  filter_upwards [Ici_mem_at_top (0 : ℝ)]with x hx
  simp only [max_eq_left (Set.mem_Ici.1 hx), id.def, Real.coe_toNNReal']
#align tendsto_real_to_nnreal_at_top tendsto_real_toNNReal_atTop

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (a «expr ≠ » 0) -/
theorem nhds_zero : 𝓝 (0 : ℝ≥0) = ⨅ (a) (_ : a ≠ 0), 𝓟 (Iio a) :=
  nhds_bot_order.trans <| by simp [bot_lt_iff_ne_bot]
#align nnreal.nhds_zero NNReal.nhds_zero

theorem nhds_zero_basis : (𝓝 (0 : ℝ≥0)).HasBasis (fun a : ℝ≥0 => 0 < a) fun a => Iio a :=
  nhds_bot_basis
#align nnreal.nhds_zero_basis NNReal.nhds_zero_basis

instance : ContinuousSub ℝ≥0 :=
  ⟨((continuous_coe.fst'.sub continuous_coe.snd').max continuous_const).subtype_mk _⟩

instance : HasContinuousInv₀ ℝ≥0 :=
  ⟨fun x hx =>
    tendsto_coe.1 <| (Real.tendsto_inv <| NNReal.coe_ne_zero.2 hx).comp continuous_coe.ContinuousAt⟩

instance [TopologicalSpace α] [MulAction ℝ α] [ContinuousSMul ℝ α] : ContinuousSMul ℝ≥0 α
    where continuous_smul := (continuous_induced_dom.comp continuous_fst).smul continuous_snd

@[norm_cast]
theorem hasSum_coe {f : α → ℝ≥0} {r : ℝ≥0} : HasSum (fun a => (f a : ℝ)) (r : ℝ) ↔ HasSum f r := by
  simp only [HasSum, coe_sum.symm, tendsto_coe]
#align nnreal.has_sum_coe NNReal.hasSum_coe

theorem hasSum_real_toNNReal_of_nonneg {f : α → ℝ} (hf_nonneg : ∀ n, 0 ≤ f n) (hf : Summable f) :
    HasSum (fun n => Real.toNNReal (f n)) (Real.toNNReal (∑' n, f n)) :=
  by
  have h_sum : (fun s => ∑ b in s, Real.toNNReal (f b)) = fun s => Real.toNNReal (∑ b in s, f b) :=
    funext fun _ => (Real.toNNReal_sum_of_nonneg fun n _ => hf_nonneg n).symm
  simp_rw [HasSum, h_sum]
  exact tendsto_real_toNNReal hf.has_sum
#align nnreal.has_sum_real_to_nnreal_of_nonneg NNReal.hasSum_real_toNNReal_of_nonneg

@[norm_cast]
theorem summable_coe {f : α → ℝ≥0} : (Summable fun a => (f a : ℝ)) ↔ Summable f :=
  by
  constructor
  exact fun ⟨a, ha⟩ => ⟨⟨a, hasSum_le (fun a => (f a).2) hasSum_zero ha⟩, has_sum_coe.1 ha⟩
  exact fun ⟨a, ha⟩ => ⟨a.1, has_sum_coe.2 ha⟩
#align nnreal.summable_coe NNReal.summable_coe

theorem summable_coe_of_nonneg {f : α → ℝ} (hf₁ : ∀ n, 0 ≤ f n) :
    (@Summable ℝ≥0 _ _ _ fun n => ⟨f n, hf₁ n⟩) ↔ Summable f :=
  by
  lift f to α → ℝ≥0 using hf₁ with f rfl hf₁
  simp only [summable_coe, Subtype.coe_eta]
#align nnreal.summable_coe_of_nonneg NNReal.summable_coe_of_nonneg

open Classical

@[norm_cast]
theorem coe_tsum {f : α → ℝ≥0} : ↑(∑' a, f a) = ∑' a, (f a : ℝ) :=
  if hf : Summable f then Eq.symm <| (hasSum_coe.2 <| hf.HasSum).tsum_eq
  else by simp [tsum, hf, mt summable_coe.1 hf]
#align nnreal.coe_tsum NNReal.coe_tsum

theorem coe_tsum_of_nonneg {f : α → ℝ} (hf₁ : ∀ n, 0 ≤ f n) :
    (⟨∑' n, f n, tsum_nonneg hf₁⟩ : ℝ≥0) = (∑' n, ⟨f n, hf₁ n⟩ : ℝ≥0) :=
  by
  lift f to α → ℝ≥0 using hf₁ with f rfl hf₁
  simp_rw [← NNReal.coe_tsum, Subtype.coe_eta]
#align nnreal.coe_tsum_of_nonneg NNReal.coe_tsum_of_nonneg

theorem tsum_mul_left (a : ℝ≥0) (f : α → ℝ≥0) : (∑' x, a * f x) = a * ∑' x, f x :=
  NNReal.eq <| by simp only [coe_tsum, NNReal.coe_mul, tsum_mul_left]
#align nnreal.tsum_mul_left NNReal.tsum_mul_left

theorem tsum_mul_right (f : α → ℝ≥0) (a : ℝ≥0) : (∑' x, f x * a) = (∑' x, f x) * a :=
  NNReal.eq <| by simp only [coe_tsum, NNReal.coe_mul, tsum_mul_right]
#align nnreal.tsum_mul_right NNReal.tsum_mul_right

theorem summable_comp_injective {β : Type _} {f : α → ℝ≥0} (hf : Summable f) {i : β → α}
    (hi : Function.Injective i) : Summable (f ∘ i) :=
  NNReal.summable_coe.1 <|
    show Summable ((coe ∘ f) ∘ i) from (NNReal.summable_coe.2 hf).comp_injective hi
#align nnreal.summable_comp_injective NNReal.summable_comp_injective

theorem summable_nat_add (f : ℕ → ℝ≥0) (hf : Summable f) (k : ℕ) : Summable fun i => f (i + k) :=
  summable_comp_injective hf <| add_left_injective k
#align nnreal.summable_nat_add NNReal.summable_nat_add

theorem summable_nat_add_iff {f : ℕ → ℝ≥0} (k : ℕ) : (Summable fun i => f (i + k)) ↔ Summable f :=
  by
  rw [← summable_coe, ← summable_coe]
  exact @summable_nat_add_iff ℝ _ _ _ (fun i => (f i : ℝ)) k
#align nnreal.summable_nat_add_iff NNReal.summable_nat_add_iff

theorem hasSum_nat_add_iff {f : ℕ → ℝ≥0} (k : ℕ) {a : ℝ≥0} :
    HasSum (fun n => f (n + k)) a ↔ HasSum f (a + ∑ i in range k, f i) := by
  simp [← has_sum_coe, coe_sum, NNReal.coe_add, ← hasSum_nat_add_iff k]
#align nnreal.has_sum_nat_add_iff NNReal.hasSum_nat_add_iff

theorem sum_add_tsum_nat_add {f : ℕ → ℝ≥0} (k : ℕ) (hf : Summable f) :
    (∑' i, f i) = (∑ i in range k, f i) + ∑' i, f (i + k) := by
  rw [← NNReal.coe_eq, coe_tsum, NNReal.coe_add, coe_sum, coe_tsum,
    sum_add_tsum_nat_add k (NNReal.summable_coe.2 hf)]
#align nnreal.sum_add_tsum_nat_add NNReal.sum_add_tsum_nat_add

theorem infᵢ_real_pos_eq_infᵢ_nNReal_pos [CompleteLattice α] {f : ℝ → α} :
    (⨅ (n : ℝ) (h : 0 < n), f n) = ⨅ (n : ℝ≥0) (h : 0 < n), f n :=
  le_antisymm (infᵢ_mono' fun r => ⟨r, le_rfl⟩) (infᵢ₂_mono' fun r hr => ⟨⟨r, hr.le⟩, hr, le_rfl⟩)
#align nnreal.infi_real_pos_eq_infi_nnreal_pos NNReal.infᵢ_real_pos_eq_infᵢ_nNReal_pos

end coe

theorem tendsto_cofinite_zero_of_summable {α} {f : α → ℝ≥0} (hf : Summable f) :
    Tendsto f cofinite (𝓝 0) :=
  by
  have h_f_coe : f = fun n => Real.toNNReal (f n : ℝ) := funext fun n => real.to_nnreal_coe.symm
  rw [h_f_coe, ← @Real.toNNReal_coe 0]
  exact tendsto_real_toNNReal (summable_coe.mpr hf).tendsto_cofinite_zero
#align nnreal.tendsto_cofinite_zero_of_summable NNReal.tendsto_cofinite_zero_of_summable

theorem tendsto_atTop_zero_of_summable {f : ℕ → ℝ≥0} (hf : Summable f) : Tendsto f atTop (𝓝 0) :=
  by
  rw [← Nat.cofinite_eq_atTop]
  exact tendsto_cofinite_zero_of_summable hf
#align nnreal.tendsto_at_top_zero_of_summable NNReal.tendsto_atTop_zero_of_summable

/-- The sum over the complement of a finset tends to `0` when the finset grows to cover the whole
space. This does not need a summability assumption, as otherwise all sums are zero. -/
theorem tendsto_tsum_compl_atTop_zero {α : Type _} (f : α → ℝ≥0) :
    Tendsto (fun s : Finset α => ∑' b : { x // x ∉ s }, f b) atTop (𝓝 0) :=
  by
  simp_rw [← tendsto_coe, coe_tsum, NNReal.coe_zero]
  exact tendsto_tsum_compl_atTop_zero fun a : α => (f a : ℝ)
#align nnreal.tendsto_tsum_compl_at_top_zero NNReal.tendsto_tsum_compl_atTop_zero

/-- `x ↦ x ^ n` as an order isomorphism of `ℝ≥0`. -/
def powOrderIso (n : ℕ) (hn : n ≠ 0) : ℝ≥0 ≃o ℝ≥0 :=
  (StrictMono.orderIsoOfSurjective (fun x => x ^ n) fun x y h =>
      strictMonoOn_pow hn.bot_lt (zero_le x) (zero_le y) h) <|
    (continuous_id.pow _).Surjective (tendsto_pow_atTop hn) <| by
      simpa [order_bot.at_bot_eq, pos_iff_ne_zero]
#align nnreal.pow_order_iso NNReal.powOrderIso

end NNReal

