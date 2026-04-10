/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Data.NNReal.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Topology on `ℝ≥0`

The basic lemmas for the natural topology on `ℝ≥0` .

## Main statements

Various mathematically trivial lemmas are proved about the compatibility
of limits and sums in `ℝ≥0` and `ℝ`. For example

* `tendsto_coe {f : Filter α} {m : α → ℝ≥0} {x : ℝ≥0} :
  Filter.Tendsto (fun a, (m a : ℝ)) f (𝓝 (x : ℝ)) ↔ Filter.Tendsto m f (𝓝 x)`

says that the limit of a filter along a map to `ℝ≥0` is the same in `ℝ` and `ℝ≥0`, and

* `coe_tsum {f : α → ℝ≥0} : ((∑'a, f a) : ℝ) = (∑'a, (f a : ℝ))`

says that says that a sum of elements in `ℝ≥0` is the same in `ℝ` and `ℝ≥0`.

Similarly, some mathematically trivial lemmas about infinite sums are proved,
a few of which rely on the fact that subtraction is continuous.

-/

@[expose] public section

noncomputable section

open Filter Metric Set TopologicalSpace Topology

variable {ι : Sort*} {n : ℕ}

namespace NNReal

variable {α : Type*} {L : SummationFilter α}

section coe

lemma isOpen_Ico_zero {x : NNReal} : IsOpen (Set.Ico 0 x) :=
  Ico_bot (a := x) ▸ isOpen_Iio

open Filter Finset

@[fun_prop]
theorem _root_.continuous_real_toNNReal : Continuous Real.toNNReal :=
  (continuous_id.max Continuous.const).subtype_mk _

/-- `Real.toNNReal` bundled as a continuous map for convenience. -/
@[simps -fullyApplied]
noncomputable def _root_.ContinuousMap.realToNNReal : C(ℝ, ℝ≥0) :=
  .mk Real.toNNReal continuous_real_toNNReal

@[simp]
theorem map_coe_nhdsGT (x : ℝ≥0) : (𝓝[>] x).map toReal = 𝓝[>] ↑x := by
  rw [isEmbedding_coe.map_nhdsWithin_eq, image_coe_Ioi]

@[simp]
theorem map_coe_nhdsGE (x : ℝ≥0) : (𝓝[≥] x).map toReal = 𝓝[≥] ↑x := by
  rw [isEmbedding_coe.map_nhdsWithin_eq, image_coe_Ici]

lemma _root_.ContinuousOn.ofReal_map_toNNReal {f : ℝ≥0 → ℝ≥0} {s : Set ℝ} {t : Set ℝ≥0}
    (hf : ContinuousOn f t) (h : Set.MapsTo Real.toNNReal s t) :
    ContinuousOn (fun x ↦ f x.toNNReal : ℝ → ℝ) s :=
  continuous_subtype_val.comp_continuousOn <| hf.comp continuous_real_toNNReal.continuousOn h

@[simp, norm_cast]
theorem tendsto_coe {f : Filter α} {m : α → ℝ≥0} {x : ℝ≥0} :
    Tendsto (fun a => (m a : ℝ)) f (𝓝 (x : ℝ)) ↔ Tendsto m f (𝓝 x) :=
  tendsto_subtype_rng.symm

theorem tendsto_coe' {f : Filter α} [NeBot f] {m : α → ℝ≥0} {x : ℝ} :
    Tendsto (fun a => m a : α → ℝ) f (𝓝 x) ↔ ∃ hx : 0 ≤ x, Tendsto m f (𝓝 ⟨x, hx⟩) :=
  ⟨fun h => ⟨ge_of_tendsto' h fun c => (m c).2, tendsto_coe.1 h⟩, fun ⟨_, hm⟩ => tendsto_coe.2 hm⟩

@[simp] theorem map_coe_atTop : map toReal atTop = atTop := map_val_Ici_atTop 0

@[simp]
theorem comap_coe_atTop : comap toReal atTop = atTop := (atTop_Ici_eq 0).symm

@[simp, norm_cast]
theorem tendsto_coe_atTop {f : Filter α} {m : α → ℝ≥0} :
    Tendsto (fun a => (m a : ℝ)) f atTop ↔ Tendsto m f atTop :=
  tendsto_Ici_atTop.symm

theorem _root_.tendsto_real_toNNReal {f : Filter α} {m : α → ℝ} {x : ℝ} (h : Tendsto m f (𝓝 x)) :
    Tendsto (fun a => Real.toNNReal (m a)) f (𝓝 (Real.toNNReal x)) :=
  (continuous_real_toNNReal.tendsto _).comp h

@[simp]
theorem _root_.Real.map_toNNReal_atTop : map Real.toNNReal atTop = atTop := by
  rw [← map_coe_atTop, Function.LeftInverse.filter_map @Real.toNNReal_coe]

theorem _root_.tendsto_real_toNNReal_atTop : Tendsto Real.toNNReal atTop atTop :=
  Real.map_toNNReal_atTop.le

@[simp]
theorem _root_.Real.comap_toNNReal_atTop : comap Real.toNNReal atTop = atTop := by
  refine le_antisymm ?_ tendsto_real_toNNReal_atTop.le_comap
  refine (atTop_basis_Ioi' 0).ge_iff.2 fun a ha ↦ ?_
  filter_upwards [preimage_mem_comap (Ioi_mem_atTop a.toNNReal)] with x hx
  exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg ha.le).1 hx

@[simp]
theorem _root_.Real.tendsto_toNNReal_atTop_iff {l : Filter α} {f : α → ℝ} :
    Tendsto (fun x ↦ (f x).toNNReal) l atTop ↔ Tendsto f l atTop := by
  rw [← Real.comap_toNNReal_atTop, tendsto_comap_iff, Function.comp_def]

theorem _root_.Real.tendsto_toNNReal_atTop : Tendsto Real.toNNReal atTop atTop :=
  Real.tendsto_toNNReal_atTop_iff.2 tendsto_id

theorem nhds_zero : 𝓝 (0 : ℝ≥0) = ⨅ (a : ℝ≥0) (_ : a ≠ 0), 𝓟 (Iio a) :=
  nhds_bot_order.trans <| by simp only [bot_lt_iff_ne_bot]; rfl

theorem nhds_zero_basis : (𝓝 (0 : ℝ≥0)).HasBasis (fun a : ℝ≥0 => 0 < a) fun a => Iio a :=
  nhds_bot_basis


@[norm_cast]
theorem hasSum_coe {f : α → ℝ≥0} {r : ℝ≥0} :
    HasSum (fun a => (f a : ℝ)) (r : ℝ) L ↔ HasSum f r L := by
  simp only [HasSum, ← coe_sum, tendsto_coe]

protected theorem _root_.HasSum.toNNReal {f : α → ℝ} {y : ℝ} (hf₀ : ∀ n, 0 ≤ f n)
    (hy : HasSum f y L) : HasSum (fun x => Real.toNNReal (f x)) y.toNNReal L := by
  rcases L.neBot_or_eq_bot with _ | hL
  · lift y to ℝ≥0 using hy.nonneg hf₀
    lift f to α → ℝ≥0 using hf₀
    simpa [hasSum_coe] using hy
  · simp [HasSum, hL]

theorem hasSum_real_toNNReal_of_nonneg {f : α → ℝ} (hf_nonneg : ∀ n, 0 ≤ f n)
    (hf : Summable f L) :
    HasSum (fun n => Real.toNNReal (f n)) (Real.toNNReal (∑'[L] n, f n)) L :=
  hf.hasSum.toNNReal hf_nonneg

@[norm_cast]
theorem summable_coe {f : α → ℝ≥0} :
    (Summable (fun a => (f a : ℝ)) L) ↔ Summable f L := by
  rcases L.neBot_or_eq_bot with _ | hL
  · constructor
    · exact fun ⟨a, ha⟩ => ⟨⟨a, ha.nonneg fun x => (f x).2⟩, hasSum_coe.1 ha⟩
    · exact fun ⟨a, ha⟩ => ⟨a.1, hasSum_coe.2 ha⟩
  · simp [Summable, HasSum, hL]

theorem summable_mk {f : α → ℝ} (hf : ∀ n, 0 ≤ f n) :
    Summable (fun n ↦ ⟨f n, hf n⟩ : α → ℝ≥0) L ↔ Summable f L :=
  Iff.symm <| summable_coe (f := fun x => ⟨f x, hf x⟩)

@[norm_cast]
theorem coe_tsum {f : α → ℝ≥0} : ↑(∑'[L] a, f a) = ∑'[L] a, (f a : ℝ) :=
  Function.LeftInverse.map_tsum (g := NNReal.toRealHom)
    f NNReal.continuous_coe continuous_real_toNNReal (fun x ↦ by simp)

theorem coe_tsum_of_nonneg {f : α → ℝ} (hf₁ : ∀ n, 0 ≤ f n) :
    NNReal.mk (∑'[L] n, f n) (tsum_nonneg hf₁) = ∑'[L] n, NNReal.mk (f n) (hf₁ n) :=
  NNReal.eq <| Eq.symm <| coe_tsum (f := fun x => ⟨f x, hf₁ x⟩)

nonrec theorem tsum_mul_left (a : ℝ≥0) (f : α → ℝ≥0) :
    ∑'[L] x, a * f x = a * ∑'[L] x, f x :=
  NNReal.eq <| by simp only [coe_tsum, NNReal.coe_mul, tsum_mul_left]

nonrec theorem tsum_mul_right (f : α → ℝ≥0) (a : ℝ≥0) :
    ∑'[L] x, f x * a = (∑'[L] x, f x) * a :=
  NNReal.eq <| by simp only [coe_tsum, NNReal.coe_mul, tsum_mul_right]

theorem summable_comp_injective {β : Type*} {f : α → ℝ≥0} (hf : Summable f) {i : β → α}
    (hi : Function.Injective i) : Summable (f ∘ i) := by
  rw [← summable_coe] at hf ⊢
  exact hf.comp_injective hi

theorem summable_nat_add (f : ℕ → ℝ≥0) (hf : Summable f) (k : ℕ) : Summable fun i => f (i + k) :=
  summable_comp_injective hf <| add_left_injective k

nonrec theorem summable_nat_add_iff {f : ℕ → ℝ≥0} (k : ℕ) :
    (Summable fun i => f (i + k)) ↔ Summable f := by
  rw [← summable_coe, ← summable_coe]
  exact @summable_nat_add_iff ℝ _ _ _ (fun i => (f i : ℝ)) k

nonrec theorem hasSum_nat_add_iff {f : ℕ → ℝ≥0} (k : ℕ) {a : ℝ≥0} :
    HasSum (fun n => f (n + k)) a ↔ HasSum f (a + ∑ i ∈ range k, f i) := by
  rw [← hasSum_coe, hasSum_nat_add_iff (f := fun n => toReal (f n)) k]; norm_cast

theorem sum_add_tsum_nat_add {f : ℕ → ℝ≥0} (k : ℕ) (hf : Summable f) :
    ∑' i, f i = (∑ i ∈ range k, f i) + ∑' i, f (i + k) :=
  (((summable_nat_add_iff k).2 hf).sum_add_tsum_nat_add').symm

theorem iInf_real_pos_eq_iInf_nnreal_pos [CompleteLattice α] {f : ℝ → α} :
    ⨅ (n : ℝ) (_ : 0 < n), f n = ⨅ (n : ℝ≥0) (_ : 0 < n), f n :=
  le_antisymm (iInf_mono' fun r => ⟨r, le_rfl⟩) (iInf₂_mono' fun r hr => ⟨⟨r, hr.le⟩, hr, le_rfl⟩)

end coe

theorem tendsto_cofinite_zero_of_summable {α} {f : α → ℝ≥0} (hf : Summable f) :
    Tendsto f cofinite (𝓝 0) := by
  simp only [← summable_coe, ← tendsto_coe] at hf ⊢
  exact hf.tendsto_cofinite_zero

theorem tendsto_atTop_zero_of_summable {f : ℕ → ℝ≥0} (hf : Summable f) : Tendsto f atTop (𝓝 0) := by
  rw [← Nat.cofinite_eq_atTop]
  exact tendsto_cofinite_zero_of_summable hf

/-- The sum over the complement of a finset tends to `0` when the finset grows to cover the whole
space. This does not need a summability assumption, as otherwise all sums are zero. -/
nonrec theorem tendsto_tsum_compl_atTop_zero {α : Type*} (f : α → ℝ≥0) :
    Tendsto (fun s : Finset α => ∑' b : { x // x ∉ s }, f b) atTop (𝓝 0) := by
  simp_rw [← tendsto_coe, coe_tsum, NNReal.coe_zero]
  exact tendsto_tsum_compl_atTop_zero fun a : α => (f a : ℝ)

/-- `x ↦ x ^ n` as an order isomorphism of `ℝ≥0`. -/
def powOrderIso (n : ℕ) (hn : n ≠ 0) : ℝ≥0 ≃o ℝ≥0 :=
  StrictMono.orderIsoOfSurjective (fun x ↦ x ^ n) (fun x y h =>
      pow_left_strictMonoOn₀ hn (zero_le x) (zero_le y) h) <|
    (continuous_id.pow _).surjective (tendsto_pow_atTop hn) <| by
      simpa [OrderBot.atBot_eq, pos_iff_ne_zero]

section Monotone

/-- A monotone, bounded above sequence `f : ℕ → ℝ` has a finite limit. -/
@[deprecated tendsto_atTop_ciSup (since := "2026-01-14")]
theorem _root_.Real.tendsto_of_bddAbove_monotone {f : ℕ → ℝ} (h_bdd : BddAbove (Set.range f))
    (h_mon : Monotone f) : ∃ r : ℝ, Tendsto f atTop (𝓝 r) :=
  ⟨iSup f, tendsto_atTop_ciSup h_mon h_bdd⟩

/-- An antitone, bounded below sequence `f : ℕ → ℝ` has a finite limit. -/
@[deprecated tendsto_atTop_ciInf (since := "2026-01-14")]
theorem _root_.Real.tendsto_of_bddBelow_antitone {f : ℕ → ℝ} (h_bdd : BddBelow (Set.range f))
    (h_ant : Antitone f) : ∃ r : ℝ, Tendsto f atTop (𝓝 r) :=
  ⟨iInf f, tendsto_atTop_ciInf h_ant h_bdd⟩

variable {ι : Type*} [Preorder ι]

/-- An antitone sequence `f : ℕ → ℝ≥0` has a finite limit. -/
@[deprecated tendsto_atTop_ciInf (since := "2026-01-14")]
theorem tendsto_of_antitone {f : ℕ → ℝ≥0} (h_ant : Antitone f) :
    ∃ r : ℝ≥0, Tendsto f atTop (𝓝 r) := ⟨iInf f, tendsto_atTop_ciInf h_ant (by simp)⟩

end Monotone

lemma iSup_pow_of_ne_zero (hn : n ≠ 0) (f : ι → ℝ≥0) : (⨆ i, f i) ^ n = ⨆ i, f i ^ n :=
  (NNReal.powOrderIso n hn).map_ciSup' _

lemma iSup_pow [Nonempty ι] (f : ι → ℝ≥0) (n : ℕ) : (⨆ i, f i) ^ n = ⨆ i, f i ^ n := by
  by_cases hn : n = 0
  · simp [hn]
  · exact iSup_pow_of_ne_zero hn _

end NNReal

namespace ENNReal

attribute [simp] ENNReal.top_pow

/-- `x ↦ x ^ n` as an order isomorphism of `ℝ≥0∞`.

See also `ENNReal.orderIsoRpow`. -/
def powOrderIso (n : ℕ) (hn : n ≠ 0) : ℝ≥0∞ ≃o ℝ≥0∞ :=
  (NNReal.powOrderIso n hn).withTopCongr.copy (· ^ n) _
    (by cases n; (· cases hn rfl); · ext (_ | _) <;> rfl) rfl

lemma iSup_pow_of_ne_zero (hn : n ≠ 0) (f : ι → ℝ≥0∞) : (⨆ i, f i) ^ n = ⨆ i, f i ^ n :=
  (powOrderIso n hn).map_iSup _

lemma iSup_pow [Nonempty ι] (f : ι → ℝ≥0∞) (n : ℕ) : (⨆ i, f i) ^ n = ⨆ i, f i ^ n := by
  by_cases hn : n = 0
  · simp [hn]
  · exact iSup_pow_of_ne_zero hn _

lemma iSup₂_pow_of_ne_zero {κ : ι → Sort*} (f : (i : ι) → κ i → ℝ≥0∞) {n : ℕ} (hn : n ≠ 0) :
    (⨆ i, ⨆ j, f i j) ^ n = ⨆ i, ⨆ j, f i j ^ n :=
  (powOrderIso n hn).map_iSup₂ f

end ENNReal

open NNReal in
lemma Real.iSup_pow [Nonempty ι] {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) (n : ℕ) :
    (⨆ i, f i) ^ n = ⨆ i, f i ^ n := by
  lift f to ι → ℝ≥0 using hf; dsimp; exact mod_cast NNReal.iSup_pow f n

lemma Real.iSup_pow_of_ne_zero {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) (hn : n ≠ 0) :
    (⨆ i, f i) ^ n = ⨆ i, f i ^ n := by
  cases isEmpty_or_nonempty ι
  · simp [hn]
  · exact iSup_pow hf _
