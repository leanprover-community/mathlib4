/-
Copyright (c) 2024 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Edward van de Meent
-/
module

public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Tactic.Bound

/-!
# Infinite sums in extended nonnegative reals

This file proves results on infinite sums in `ℝ≥0∞`.

In particular, we give lemmas relating sums of constants to the cardinality of the domain of
these sums.

## TODO

+ Once we have a topology on `ENat`, provide an `ENat`-valued version
+ Provide versions which sum over the whole type.
-/

public section

open Set Function

open Filter Function Metric Set Topology
open scoped Finset ENNReal NNReal

variable {α : Type*} {β : Type*} {γ : Type*}

namespace ENNReal

variable {a b : ℝ≥0∞} {r : ℝ≥0} {x : ℝ≥0∞} {ε : ℝ≥0∞}

section tsum

variable {f g : α → ℝ≥0∞}

@[norm_cast]
protected theorem hasSum_coe {f : α → ℝ≥0} {r : ℝ≥0} :
    HasSum (fun a => (f a : ℝ≥0∞)) ↑r ↔ HasSum f r := by
  simp only [HasSum, ← coe_finsetSum, tendsto_coe]

protected theorem tsum_coe_eq {f : α → ℝ≥0} (h : HasSum f r) : (∑' a, (f a : ℝ≥0∞)) = r :=
  (ENNReal.hasSum_coe.2 h).tsum_eq

protected theorem coe_tsum {f : α → ℝ≥0} : Summable f → ↑(tsum f) = ∑' a, (f a : ℝ≥0∞)
  | ⟨r, hr⟩ => by rw [hr.tsum_eq, ENNReal.tsum_coe_eq hr]

protected theorem hasSum : HasSum f (⨆ s : Finset α, ∑ a ∈ s, f a) :=
  tendsto_atTop_iSup fun _ _ => Finset.sum_le_sum_of_subset

@[simp]
protected theorem summable : Summable f :=
  ⟨_, ENNReal.hasSum⟩

macro_rules | `(tactic| gcongr_discharger) => `(tactic| apply ENNReal.summable)

theorem tsum_coe_ne_top_iff_summable {f : β → ℝ≥0} : (∑' b, (f b : ℝ≥0∞)) ≠ ∞ ↔ Summable f := by
  refine ⟨fun h => ?_, fun h => ENNReal.coe_tsum h ▸ ENNReal.coe_ne_top⟩
  lift ∑' b, (f b : ℝ≥0∞) to ℝ≥0 using h with a ha
  refine ⟨a, ENNReal.hasSum_coe.1 ?_⟩
  rw [ha]
  exact ENNReal.summable.hasSum

protected theorem tsum_eq_iSup_sum : ∑' a, f a = ⨆ s : Finset α, ∑ a ∈ s, f a :=
  ENNReal.hasSum.tsum_eq

protected theorem tsum_eq_iSup_sum' {ι : Type*} (s : ι → Finset α) (hs : ∀ t, ∃ i, t ⊆ s i) :
    ∑' a, f a = ⨆ i, ∑ a ∈ s i, f a := by
  rw [ENNReal.tsum_eq_iSup_sum]
  symm
  change ⨆ i : ι, (fun t : Finset α => ∑ a ∈ t, f a) (s i) = ⨆ s : Finset α, ∑ a ∈ s, f a
  exact (Finset.sum_mono_set f).iSup_comp_eq hs

protected theorem tsum_sigma {β : α → Type*} (f : ∀ a, β a → ℝ≥0∞) :
    ∑' p : Σ a, β a, f p.1 p.2 = ∑' (a) (b), f a b :=
  ENNReal.summable.tsum_sigma' fun _ => ENNReal.summable

protected theorem tsum_sigma' {β : α → Type*} (f : (Σ a, β a) → ℝ≥0∞) :
    ∑' p : Σ a, β a, f p = ∑' (a) (b), f ⟨a, b⟩ :=
  ENNReal.summable.tsum_sigma' fun _ => ENNReal.summable

protected theorem tsum_biUnion' {ι : Type*} {S : Set ι} {f : α → ENNReal} {t : ι → Set α}
    (h : S.PairwiseDisjoint t) : ∑' x : ⋃ i ∈ S, t i, f x = ∑' (i : S), ∑' (x : t i), f x := by
  simp [← ENNReal.tsum_sigma, ← (Set.biUnionEqSigmaOfDisjoint h).tsum_eq]

protected theorem tsum_biUnion {ι : Type*} {f : α → ENNReal} {t : ι → Set α}
    (h : Set.univ.PairwiseDisjoint t) : ∑' x : ⋃ i, t i, f x = ∑' (i) (x : t i), f x := by
  nth_rw 2 [← tsum_univ]
  rw [← ENNReal.tsum_biUnion' h, Set.biUnion_univ]

protected theorem tsum_prod {f : α → β → ℝ≥0∞} : ∑' p : α × β, f p.1 p.2 = ∑' (a) (b), f a b :=
  ENNReal.summable.tsum_prod' fun _ => ENNReal.summable

protected theorem tsum_prod' {f : α × β → ℝ≥0∞} : ∑' p : α × β, f p = ∑' (a) (b), f (a, b) :=
  ENNReal.summable.tsum_prod' fun _ => ENNReal.summable

protected theorem tsum_comm {f : α → β → ℝ≥0∞} : ∑' a, ∑' b, f a b = ∑' b, ∑' a, f a b :=
  ENNReal.summable.tsum_comm' (fun _ => ENNReal.summable) fun _ => ENNReal.summable

protected theorem tsum_add : ∑' a, (f a + g a) = ∑' a, f a + ∑' a, g a :=
  ENNReal.summable.tsum_add ENNReal.summable

protected lemma sum_add_tsum_compl {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    ∑ i ∈ s, f i + ∑' i : ↥(s : Set ι)ᶜ, f i = ∑' i, f i := by
  rw [tsum_subtype, sum_eq_tsum_indicator]
  simp [← ENNReal.tsum_add]

protected theorem tsum_le_tsum (h : ∀ a, f a ≤ g a) : ∑' a, f a ≤ ∑' a, g a :=
  ENNReal.summable.tsum_le_tsum h ENNReal.summable

protected theorem sum_le_tsum {f : α → ℝ≥0∞} (s : Finset α) : ∑ x ∈ s, f x ≤ ∑' x, f x :=
  ENNReal.summable.sum_le_tsum s (fun _ _ => zero_le _)

protected lemma le_tsum_of_forall_lt_exists_sum
    (h : ∀ b < a, ∃ I : Finset α, b < ∑ i ∈ I, f i) : a ≤ ∑' i, f i := by
  refine le_of_forall_lt fun b hb ↦ ?_
  obtain ⟨I, hI⟩ := h b hb
  exact lt_of_lt_of_le hI (ENNReal.sum_le_tsum I)

protected theorem tsum_eq_iSup_nat' {f : ℕ → ℝ≥0∞} {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    ∑' i : ℕ, f i = ⨆ i : ℕ, ∑ a ∈ Finset.range (N i), f a :=
  ENNReal.tsum_eq_iSup_sum' _ fun t =>
    let ⟨n, hn⟩ := t.exists_nat_subset_range
    let ⟨k, _, hk⟩ := exists_le_of_tendsto_atTop hN 0 n
    ⟨k, Finset.Subset.trans hn (Finset.range_mono hk)⟩

protected theorem tsum_eq_iSup_nat {f : ℕ → ℝ≥0∞} :
    ∑' i : ℕ, f i = ⨆ i : ℕ, ∑ a ∈ Finset.range i, f a :=
  ENNReal.tsum_eq_iSup_sum' _ Finset.exists_nat_subset_range

protected theorem tsum_eq_liminf_sum_nat {f : ℕ → ℝ≥0∞} :
    ∑' i, f i = liminf (fun n => ∑ i ∈ Finset.range n, f i) atTop :=
  ENNReal.summable.hasSum.tendsto_sum_nat.liminf_eq.symm

protected theorem tsum_eq_limsup_sum_nat {f : ℕ → ℝ≥0∞} :
    ∑' i, f i = limsup (fun n => ∑ i ∈ Finset.range n, f i) atTop :=
  ENNReal.summable.hasSum.tendsto_sum_nat.limsup_eq.symm

protected theorem le_tsum (a : α) : f a ≤ ∑' a, f a :=
  ENNReal.summable.le_tsum' a

@[simp]
protected theorem tsum_eq_zero : ∑' i, f i = 0 ↔ ∀ i, f i = 0 :=
  ENNReal.summable.tsum_eq_zero_iff

protected theorem tsum_eq_top_of_eq_top : (∃ a, f a = ∞) → ∑' a, f a = ∞
  | ⟨a, ha⟩ => top_unique <| ha ▸ ENNReal.le_tsum a

protected theorem lt_top_of_tsum_ne_top {a : α → ℝ≥0∞} (tsum_ne_top : ∑' i, a i ≠ ∞) (j : α) :
    a j < ∞ := by
  contrapose! tsum_ne_top with h
  exact ENNReal.tsum_eq_top_of_eq_top ⟨j, top_unique h⟩

@[simp]
protected theorem tsum_top [Nonempty α] : ∑' _ : α, ∞ = ∞ :=
  let ⟨a⟩ := ‹Nonempty α›
  ENNReal.tsum_eq_top_of_eq_top ⟨a, rfl⟩

theorem tsum_const_eq_top_of_ne_zero {α : Type*} [Infinite α] {c : ℝ≥0∞} (hc : c ≠ 0) :
    ∑' _ : α, c = ∞ := by
  have A : Tendsto (fun n : ℕ => (n : ℝ≥0∞) * c) atTop (𝓝 (∞ * c)) := by
    apply ENNReal.Tendsto.mul_const tendsto_nat_nhds_top
    simp only [true_or, top_ne_zero, Ne, not_false_iff]
  have B : ∀ n : ℕ, (n : ℝ≥0∞) * c ≤ ∑' _ : α, c := fun n => by
    rcases Infinite.exists_subset_card_eq α n with ⟨s, hs⟩
    simpa [hs] using @ENNReal.sum_le_tsum α (fun _ => c) s
  simpa [hc] using le_of_tendsto' A B

protected theorem ne_top_of_tsum_ne_top (h : ∑' a, f a ≠ ∞) (a : α) : f a ≠ ∞ := fun ha =>
  h <| ENNReal.tsum_eq_top_of_eq_top ⟨a, ha⟩

protected theorem tsum_mul_left : ∑' i, a * f i = a * ∑' i, f i := by
  by_cases hf : ∀ i, f i = 0
  · simp [hf]
  · rw [← ENNReal.tsum_eq_zero] at hf
    have : Tendsto (fun s : Finset α => ∑ j ∈ s, a * f j) atTop (𝓝 (a * ∑' i, f i)) := by
      simp only [← Finset.mul_sum]
      exact ENNReal.Tendsto.const_mul ENNReal.summable.hasSum (Or.inl hf)
    exact HasSum.tsum_eq this

protected theorem tsum_mul_right : ∑' i, f i * a = (∑' i, f i) * a := by
  simp [mul_comm, ENNReal.tsum_mul_left]

protected theorem tsum_const_smul {R} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (a : R) :
    ∑' i, a • f i = a • ∑' i, f i := by
  simpa only [smul_one_mul] using @ENNReal.tsum_mul_left _ (a • (1 : ℝ≥0∞)) _

@[simp]
theorem tsum_iSup_eq {α : Type*} (a : α) {f : α → ℝ≥0∞} : (∑' b : α, ⨆ _ : a = b, f b) = f a :=
  (tsum_eq_single a fun _ h => by simp [h.symm]).trans <| by simp

theorem hasSum_iff_tendsto_nat {f : ℕ → ℝ≥0∞} (r : ℝ≥0∞) :
    HasSum f r ↔ Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop (𝓝 r) := by
  refine ⟨HasSum.tendsto_sum_nat, fun h => ?_⟩
  rw [← iSup_eq_of_tendsto _ h, ← ENNReal.tsum_eq_iSup_nat]
  · exact ENNReal.summable.hasSum
  · exact fun s t hst => Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hst)

theorem tendsto_nat_tsum (f : ℕ → ℝ≥0∞) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop (𝓝 (∑' n, f n)) := by
  rw [← hasSum_iff_tendsto_nat]
  exact ENNReal.summable.hasSum

theorem toNNReal_apply_of_tsum_ne_top {α : Type*} {f : α → ℝ≥0∞} (hf : ∑' i, f i ≠ ∞) (x : α) :
    (((ENNReal.toNNReal ∘ f) x : ℝ≥0) : ℝ≥0∞) = f x :=
  coe_toNNReal <| ENNReal.ne_top_of_tsum_ne_top hf _

theorem summable_toNNReal_of_tsum_ne_top {α : Type*} {f : α → ℝ≥0∞} (hf : ∑' i, f i ≠ ∞) :
    Summable (ENNReal.toNNReal ∘ f) := by
  simpa only [← tsum_coe_ne_top_iff_summable, toNNReal_apply_of_tsum_ne_top hf] using hf

theorem tendsto_cofinite_zero_of_tsum_ne_top {α} {f : α → ℝ≥0∞} (hf : ∑' x, f x ≠ ∞) :
    Tendsto f cofinite (𝓝 0) := by
  have f_ne_top : ∀ n, f n ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top hf
  have h_f_coe : f = fun n => ((f n).toNNReal : ENNReal) :=
    funext fun n => (coe_toNNReal (f_ne_top n)).symm
  rw [h_f_coe, ← @coe_zero, tendsto_coe]
  exact NNReal.tendsto_cofinite_zero_of_summable (summable_toNNReal_of_tsum_ne_top hf)

theorem tendsto_atTop_zero_of_tsum_ne_top {f : ℕ → ℝ≥0∞} (hf : ∑' x, f x ≠ ∞) :
    Tendsto f atTop (𝓝 0) := by
  rw [← Nat.cofinite_eq_atTop]
  exact tendsto_cofinite_zero_of_tsum_ne_top hf

/-- The sum over the complement of a finset tends to `0` when the finset grows to cover the whole
space. This does not need a summability assumption, as otherwise all sums are zero. -/
theorem tendsto_tsum_compl_atTop_zero {α : Type*} {f : α → ℝ≥0∞} (hf : ∑' x, f x ≠ ∞) :
    Tendsto (fun s : Finset α => ∑' b : { x // x ∉ s }, f b) atTop (𝓝 0) := by
  lift f to α → ℝ≥0 using ENNReal.ne_top_of_tsum_ne_top hf
  convert ENNReal.tendsto_coe.2 (NNReal.tendsto_tsum_compl_atTop_zero f)
  rw [ENNReal.coe_tsum]
  exact NNReal.summable_comp_injective (tsum_coe_ne_top_iff_summable.1 hf) Subtype.coe_injective

protected theorem tsum_apply {ι α : Type*} {f : ι → α → ℝ≥0∞} {x : α} :
    (∑' i, f i) x = ∑' i, f i x :=
  tsum_apply <| Pi.summable.mpr fun _ => ENNReal.summable

theorem tsum_sub {f : ℕ → ℝ≥0∞} {g : ℕ → ℝ≥0∞} (h₁ : ∑' i, g i ≠ ∞) (h₂ : g ≤ f) :
    ∑' i, (f i - g i) = ∑' i, f i - ∑' i, g i :=
  have : ∀ i, f i - g i + g i = f i := fun i => tsub_add_cancel_of_le (h₂ i)
  ENNReal.eq_sub_of_add_eq h₁ <| by simp only [← ENNReal.tsum_add, this]

theorem tsum_comp_le_tsum_of_injective {f : α → β} (hf : Injective f) (g : β → ℝ≥0∞) :
    ∑' x, g (f x) ≤ ∑' y, g y :=
  ENNReal.summable.tsum_le_tsum_of_inj f hf (fun _ _ => zero_le _) (fun _ => le_rfl)
    ENNReal.summable

theorem tsum_le_tsum_comp_of_surjective {f : α → β} (hf : Surjective f) (g : β → ℝ≥0∞) :
    ∑' y, g y ≤ ∑' x, g (f x) :=
  calc ∑' y, g y = ∑' y, g (f (surjInv hf y)) := by simp only [surjInv_eq hf]
  _ ≤ ∑' x, g (f x) := tsum_comp_le_tsum_of_injective (injective_surjInv hf) _

theorem tsum_mono_subtype (f : α → ℝ≥0∞) {s t : Set α} (h : s ⊆ t) :
    ∑' x : s, f x ≤ ∑' x : t, f x :=
  tsum_comp_le_tsum_of_injective (inclusion_injective h) _

theorem tsum_iUnion_le_tsum {ι : Type*} (f : α → ℝ≥0∞) (t : ι → Set α) :
    ∑' x : ⋃ i, t i, f x ≤ ∑' i, ∑' x : t i, f x :=
  calc ∑' x : ⋃ i, t i, f x ≤ ∑' x : Σ i, t i, f x.2 :=
    tsum_le_tsum_comp_of_surjective (sigmaToiUnion_surjective t) _
  _ = ∑' i, ∑' x : t i, f x := ENNReal.tsum_sigma' _

theorem tsum_biUnion_le_tsum {ι : Type*} (f : α → ℝ≥0∞) (s : Set ι) (t : ι → Set α) :
    ∑' x : ⋃ i ∈ s, t i, f x ≤ ∑' i : s, ∑' x : t i, f x :=
  calc ∑' x : ⋃ i ∈ s, t i, f x = ∑' x : ⋃ i : s, t i, f x := tsum_congr_set_coe _ <| by simp
  _ ≤ ∑' i : s, ∑' x : t i, f x := tsum_iUnion_le_tsum _ _

theorem tsum_biUnion_le {ι : Type*} (f : α → ℝ≥0∞) (s : Finset ι) (t : ι → Set α) :
    ∑' x : ⋃ i ∈ s, t i, f x ≤ ∑ i ∈ s, ∑' x : t i, f x :=
  (tsum_biUnion_le_tsum f s t).trans_eq (Finset.tsum_subtype s fun i => ∑' x : t i, f x)

theorem tsum_iUnion_le {ι : Type*} [Fintype ι] (f : α → ℝ≥0∞) (t : ι → Set α) :
    ∑' x : ⋃ i, t i, f x ≤ ∑ i, ∑' x : t i, f x := by
  rw [← tsum_fintype (L := SummationFilter.unconditional _)]
  exact tsum_iUnion_le_tsum f t

theorem tsum_union_le (f : α → ℝ≥0∞) (s t : Set α) :
    ∑' x : ↑(s ∪ t), f x ≤ ∑' x : s, f x + ∑' x : t, f x :=
  calc ∑' x : ↑(s ∪ t), f x = ∑' x : ⋃ b, cond b s t, f x := tsum_congr_set_coe _ union_eq_iUnion
  _ ≤ _ := by simpa using tsum_iUnion_le f (cond · s t)

open Classical in
theorem tsum_eq_add_tsum_ite {f : β → ℝ≥0∞} (b : β) :
    ∑' x, f x = f b + ∑' x, ite (x = b) 0 (f x) :=
  ENNReal.summable.tsum_eq_add_tsum_ite' b

theorem tsum_add_one_eq_top {f : ℕ → ℝ≥0∞} (hf : ∑' n, f n = ∞) (hf0 : f 0 ≠ ∞) :
    ∑' n, f (n + 1) = ∞ := by
  rw [tsum_eq_zero_add' ENNReal.summable, add_eq_top] at hf
  exact hf.resolve_left hf0

/-- A sum of extended nonnegative reals which is finite can have only finitely many terms
above any positive threshold. -/
theorem finite_const_le_of_tsum_ne_top {ι : Type*} {a : ι → ℝ≥0∞} (tsum_ne_top : ∑' i, a i ≠ ∞)
    {ε : ℝ≥0∞} (ε_ne_zero : ε ≠ 0) : { i : ι | ε ≤ a i }.Finite := by
  by_contra h
  have := Infinite.to_subtype h
  refine tsum_ne_top (top_unique ?_)
  calc ∞ = ∑' _ : { i | ε ≤ a i }, ε := (tsum_const_eq_top_of_ne_zero ε_ne_zero).symm
  _ ≤ ∑' i, a i := ENNReal.summable.tsum_le_tsum_of_inj (↑)
    Subtype.val_injective (fun _ _ => zero_le _) (fun i => i.2) ENNReal.summable

/-- Markov's inequality for `Finset.card` and `tsum` in `ℝ≥0∞`. -/
theorem finset_card_const_le_le_of_tsum_le {ι : Type*} {a : ι → ℝ≥0∞} {c : ℝ≥0∞} (c_ne_top : c ≠ ∞)
    (tsum_le_c : ∑' i, a i ≤ c) {ε : ℝ≥0∞} (ε_ne_zero : ε ≠ 0) :
    ∃ hf : { i : ι | ε ≤ a i }.Finite, #hf.toFinset ≤ c / ε := by
  have hf : { i : ι | ε ≤ a i }.Finite :=
    finite_const_le_of_tsum_ne_top (ne_top_of_le_ne_top c_ne_top tsum_le_c) ε_ne_zero
  refine ⟨hf, (ENNReal.le_div_iff_mul_le (.inl ε_ne_zero) (.inr c_ne_top)).2 ?_⟩
  calc #hf.toFinset * ε = ∑ _i ∈ hf.toFinset, ε := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ hf.toFinset, a i := Finset.sum_le_sum fun i => hf.mem_toFinset.1
    _ ≤ ∑' i, a i := ENNReal.sum_le_tsum _
    _ ≤ c := tsum_le_c

theorem tsum_fiberwise (f : β → ℝ≥0∞) (g : β → γ) :
    ∑' x, ∑' b : g ⁻¹' {x}, f b = ∑' i, f i := by
  apply HasSum.tsum_eq
  let equiv := Equiv.sigmaFiberEquiv g
  apply (equiv.hasSum_iff.mpr ENNReal.summable.hasSum).sigma
  exact fun _ ↦ ENNReal.summable.hasSum_iff.mpr rfl

end tsum

theorem tsum_coe_ne_top_iff_summable_coe {f : α → ℝ≥0} :
    (∑' a, (f a : ℝ≥0∞)) ≠ ∞ ↔ Summable fun a => (f a : ℝ) := by
  rw [NNReal.summable_coe]
  exact tsum_coe_ne_top_iff_summable

theorem tsum_coe_eq_top_iff_not_summable_coe {f : α → ℝ≥0} :
    (∑' a, (f a : ℝ≥0∞)) = ∞ ↔ ¬Summable fun a => (f a : ℝ) :=
  tsum_coe_ne_top_iff_summable_coe.not_right

theorem hasSum_toReal {f : α → ℝ≥0∞} (hsum : ∑' x, f x ≠ ∞) :
    HasSum (fun x => (f x).toReal) (∑' x, (f x).toReal) := by
  lift f to α → ℝ≥0 using ENNReal.ne_top_of_tsum_ne_top hsum
  simp only [coe_toReal, ← NNReal.coe_tsum, NNReal.hasSum_coe]
  exact (tsum_coe_ne_top_iff_summable.1 hsum).hasSum

theorem summable_toReal {f : α → ℝ≥0∞} (hsum : ∑' x, f x ≠ ∞) : Summable fun x => (f x).toReal :=
  (hasSum_toReal hsum).summable

end ENNReal

namespace NNReal


theorem tsum_eq_toNNReal_tsum {f : β → ℝ≥0} : ∑' b, f b = (∑' b, (f b : ℝ≥0∞)).toNNReal := by
  by_cases h : Summable f
  · rw [← ENNReal.coe_tsum h, ENNReal.toNNReal_coe]
  · have A := tsum_eq_zero_of_not_summable h
    simp only [← ENNReal.tsum_coe_ne_top_iff_summable, Classical.not_not] at h
    simp only [h, ENNReal.toNNReal_top, A]

/-- Comparison test of convergence of `ℝ≥0`-valued series. -/
theorem exists_le_hasSum_of_le {f g : β → ℝ≥0} {r : ℝ≥0} (hgf : ∀ b, g b ≤ f b) (hfr : HasSum f r) :
    ∃ p ≤ r, HasSum g p :=
  have : (∑' b, (g b : ℝ≥0∞)) ≤ r := by
    refine hasSum_le (fun b => ?_) ENNReal.summable.hasSum (ENNReal.hasSum_coe.2 hfr)
    exact ENNReal.coe_le_coe.2 (hgf _)
  let ⟨p, Eq, hpr⟩ := ENNReal.le_coe_iff.1 this
  ⟨p, hpr, ENNReal.hasSum_coe.1 <| Eq ▸ ENNReal.summable.hasSum⟩

/-- Comparison test of convergence of `ℝ≥0`-valued series. -/
theorem summable_of_le {f g : β → ℝ≥0} (hgf : ∀ b, g b ≤ f b) : Summable f → Summable g
  | ⟨_r, hfr⟩ =>
    let ⟨_p, _, hp⟩ := exists_le_hasSum_of_le hgf hfr
    hp.summable

/-- Summable non-negative functions have countable support -/
theorem _root_.Summable.countable_support_nnreal (f : α → ℝ≥0) (h : Summable f) :
    f.support.Countable := by
  rw [← NNReal.summable_coe] at h
  simpa [support] using h.countable_support

/-- A series of non-negative real numbers converges to `r` in the sense of `HasSum` if and only if
the sequence of partial sum converges to `r`. -/
theorem hasSum_iff_tendsto_nat {f : ℕ → ℝ≥0} {r : ℝ≥0} :
    HasSum f r ↔ Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop (𝓝 r) := by
  rw [← ENNReal.hasSum_coe, ENNReal.hasSum_iff_tendsto_nat]
  simp only [← ENNReal.coe_finsetSum]
  exact ENNReal.tendsto_coe

theorem not_summable_iff_tendsto_nat_atTop {f : ℕ → ℝ≥0} :
    ¬Summable f ↔ Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop atTop := by
  constructor
  · intro h
    refine ((tendsto_atTop_of_monotone ?_).resolve_right h).comp ?_
    exacts [Finset.sum_mono_set _, tendsto_finset_range]
  · rintro hnat ⟨r, hr⟩
    exact not_tendsto_nhds_of_tendsto_atTop hnat _ (hasSum_iff_tendsto_nat.1 hr)

theorem summable_iff_not_tendsto_nat_atTop {f : ℕ → ℝ≥0} :
    Summable f ↔ ¬Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop atTop := by
  rw [← not_iff_not, Classical.not_not, not_summable_iff_tendsto_nat_atTop]

theorem summable_of_sum_range_le {f : ℕ → ℝ≥0} {c : ℝ≥0}
    (h : ∀ n, ∑ i ∈ Finset.range n, f i ≤ c) : Summable f := by
  refine summable_iff_not_tendsto_nat_atTop.2 fun H => ?_
  rcases exists_lt_of_tendsto_atTop H 0 c with ⟨n, -, hn⟩
  exact lt_irrefl _ (hn.trans_le (h n))

theorem tsum_le_of_sum_range_le {f : ℕ → ℝ≥0} {c : ℝ≥0}
    (h : ∀ n, ∑ i ∈ Finset.range n, f i ≤ c) : ∑' n, f n ≤ c :=
  (summable_of_sum_range_le h).tsum_le_of_sum_range_le h

theorem tsum_comp_le_tsum_of_inj {β : Type*} {f : α → ℝ≥0} (hf : Summable f) {i : β → α}
    (hi : Function.Injective i) : (∑' x, f (i x)) ≤ ∑' x, f x :=
  (summable_comp_injective hf hi).tsum_le_tsum_of_inj i hi (fun _ _ => zero_le _) (fun _ => le_rfl)
    hf

theorem summable_sigma {β : α → Type*} {f : (Σ x, β x) → ℝ≥0} :
    Summable f ↔ (∀ x, Summable fun y => f ⟨x, y⟩) ∧ Summable fun x => ∑' y, f ⟨x, y⟩ := by
  constructor
  · simp only [← NNReal.summable_coe, NNReal.coe_tsum]
    exact fun h => ⟨h.sigma_factor, h.sigma⟩
  · rintro ⟨h₁, h₂⟩
    simpa only [← ENNReal.tsum_coe_ne_top_iff_summable, ENNReal.tsum_sigma',
      ENNReal.coe_tsum (h₁ _)] using h₂

theorem indicator_summable {f : α → ℝ≥0} (hf : Summable f) (s : Set α) :
    Summable (s.indicator f) := by
  classical
  refine NNReal.summable_of_le (fun a => le_trans (le_of_eq (s.indicator_apply f a)) ?_) hf
  split_ifs
  · exact le_refl (f a)
  · exact zero_le_coe

theorem tsum_indicator_ne_zero {f : α → ℝ≥0} (hf : Summable f) {s : Set α} (h : ∃ a ∈ s, f a ≠ 0) :
    (∑' x, (s.indicator f) x) ≠ 0 := fun h' =>
  let ⟨a, ha, hap⟩ := h
  hap ((Set.indicator_apply_eq_self.mpr (absurd ha)).symm.trans
    ((indicator_summable hf s).tsum_eq_zero_iff.1 h' a))

open Finset

/-- For `f : ℕ → ℝ≥0`, then `∑' k, f (k + i)` tends to zero. This does not require a summability
assumption on `f`, as otherwise all sums are zero. -/
theorem tendsto_sum_nat_add (f : ℕ → ℝ≥0) : Tendsto (fun i => ∑' k, f (k + i)) atTop (𝓝 0) := by
  rw [← tendsto_coe]
  convert _root_.tendsto_sum_nat_add fun i => (f i : ℝ)
  norm_cast

nonrec theorem hasSum_lt {f g : α → ℝ≥0} {sf sg : ℝ≥0} {i : α} (h : ∀ a : α, f a ≤ g a)
    (hi : f i < g i) (hf : HasSum f sf) (hg : HasSum g sg) : sf < sg := by
  have A : ∀ a : α, (f a : ℝ) ≤ g a := fun a => NNReal.coe_le_coe.2 (h a)
  have : (sf : ℝ) < sg := hasSum_lt A (NNReal.coe_lt_coe.2 hi) (hasSum_coe.2 hf) (hasSum_coe.2 hg)
  exact NNReal.coe_lt_coe.1 this

@[mono]
theorem hasSum_strict_mono {f g : α → ℝ≥0} {sf sg : ℝ≥0} (hf : HasSum f sf) (hg : HasSum g sg)
    (h : f < g) : sf < sg :=
  let ⟨hle, _i, hi⟩ := Pi.lt_def.mp h
  hasSum_lt hle hi hf hg

theorem tsum_lt_tsum {f g : α → ℝ≥0} {i : α} (h : ∀ a : α, f a ≤ g a) (hi : f i < g i)
    (hg : Summable g) : ∑' n, f n < ∑' n, g n :=
  hasSum_lt h hi (summable_of_le h hg).hasSum hg.hasSum

@[mono]
theorem tsum_strict_mono {f g : α → ℝ≥0} (hg : Summable g) (h : f < g) : ∑' n, f n < ∑' n, g n :=
  let ⟨hle, _i, hi⟩ := Pi.lt_def.mp h
  tsum_lt_tsum hle hi hg

theorem tsum_pos {g : α → ℝ≥0} (hg : Summable g) (i : α) (hi : 0 < g i) : 0 < ∑' b, g b := by
  simpa using tsum_lt_tsum (fun a => zero_le _) hi hg

open Classical in
theorem tsum_eq_add_tsum_ite {f : α → ℝ≥0} (hf : Summable f) (i : α) :
    ∑' x, f x = f i + ∑' x, ite (x = i) 0 (f x) := by
  refine (NNReal.summable_of_le (fun i' => ?_) hf).tsum_eq_add_tsum_ite' i
  rw [Function.update_apply]
  split_ifs <;> simp only [zero_le', le_rfl]

end NNReal

namespace ENNReal

theorem tsum_toNNReal_eq {f : α → ℝ≥0∞} (hf : ∀ a, f a ≠ ∞) :
    (∑' a, f a).toNNReal = ∑' a, (f a).toNNReal :=
  (congr_arg ENNReal.toNNReal (tsum_congr fun x => (coe_toNNReal (hf x)).symm)).trans
    NNReal.tsum_eq_toNNReal_tsum.symm

theorem tsum_toReal_eq {f : α → ℝ≥0∞} (hf : ∀ a, f a ≠ ∞) :
    (∑' a, f a).toReal = ∑' a, (f a).toReal := by
  simp only [ENNReal.toReal, tsum_toNNReal_eq hf, NNReal.coe_tsum]

theorem tendsto_sum_nat_add (f : ℕ → ℝ≥0∞) (hf : ∑' i, f i ≠ ∞) :
    Tendsto (fun i => ∑' k, f (k + i)) atTop (𝓝 0) := by
  lift f to ℕ → ℝ≥0 using ENNReal.ne_top_of_tsum_ne_top hf
  replace hf : Summable f := tsum_coe_ne_top_iff_summable.1 hf
  simp only [← ENNReal.coe_tsum, NNReal.summable_nat_add _ hf, ← ENNReal.coe_zero]
  exact mod_cast NNReal.tendsto_sum_nat_add f

theorem tsum_le_of_sum_range_le {f : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ n, ∑ i ∈ Finset.range n, f i ≤ c) : ∑' n, f n ≤ c :=
  ENNReal.summable.tsum_le_of_sum_range_le h

theorem hasSum_lt {f g : α → ℝ≥0∞} {sf sg : ℝ≥0∞} {i : α} (h : ∀ a : α, f a ≤ g a) (hi : f i < g i)
    (hsf : sf ≠ ∞) (hf : HasSum f sf) (hg : HasSum g sg) : sf < sg := by
  by_cases hsg : sg = ∞
  · exact hsg.symm ▸ lt_of_le_of_ne le_top hsf
  · have hg' : ∀ x, g x ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top (hg.tsum_eq.symm ▸ hsg)
    lift f to α → ℝ≥0 using fun x =>
      ne_of_lt (lt_of_le_of_lt (h x) <| lt_of_le_of_ne le_top (hg' x))
    lift g to α → ℝ≥0 using hg'
    lift sf to ℝ≥0 using hsf
    lift sg to ℝ≥0 using hsg
    simp only [coe_le_coe, coe_lt_coe] at h hi ⊢
    exact NNReal.hasSum_lt h hi (ENNReal.hasSum_coe.1 hf) (ENNReal.hasSum_coe.1 hg)

theorem tsum_lt_tsum {f g : α → ℝ≥0∞} {i : α} (hfi : tsum f ≠ ∞) (h : ∀ a : α, f a ≤ g a)
    (hi : f i < g i) : ∑' x, f x < ∑' x, g x :=
  hasSum_lt h hi hfi ENNReal.summable.hasSum ENNReal.summable.hasSum

end ENNReal

theorem tsum_comp_le_tsum_of_inj {β : Type*} {f : α → ℝ} (hf : Summable f) (hn : ∀ a, 0 ≤ f a)
    {i : β → α} (hi : Function.Injective i) : tsum (f ∘ i) ≤ tsum f := by
  lift f to α → ℝ≥0 using hn
  rw [NNReal.summable_coe] at hf
  simpa only [Function.comp_def, ← NNReal.coe_tsum] using NNReal.tsum_comp_le_tsum_of_inj hf hi

/-- Comparison test of convergence of series of non-negative real numbers. -/
theorem Summable.of_nonneg_of_le {f g : β → ℝ} (hg : ∀ b, 0 ≤ g b) (hgf : ∀ b, g b ≤ f b)
    (hf : Summable f) : Summable g := by
  lift f to β → ℝ≥0 using fun b => (hg b).trans (hgf b)
  lift g to β → ℝ≥0 using hg
  rw [NNReal.summable_coe] at hf ⊢
  exact NNReal.summable_of_le (fun b => NNReal.coe_le_coe.1 (hgf b)) hf

theorem Summable.toNNReal {f : α → ℝ} (hf : Summable f) : Summable fun n => (f n).toNNReal := by
  apply NNReal.summable_coe.1
  refine .of_nonneg_of_le (fun n => NNReal.coe_nonneg _) (fun n => ?_) hf.abs
  simp only [le_abs_self, Real.coe_toNNReal', max_le_iff, abs_nonneg, and_self_iff]

lemma Summable.tsum_ofReal_lt_top {f : α → ℝ} (hf : Summable f) : ∑' i, .ofReal (f i) < ∞ := by
  unfold ENNReal.ofReal
  rw [lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable]
  exact hf.toNNReal

lemma Summable.tsum_ofReal_ne_top {f : α → ℝ} (hf : Summable f) : ∑' i, .ofReal (f i) ≠ ∞ :=
  hf.tsum_ofReal_lt_top.ne

/-- Finitely summable non-negative functions have countable support -/
theorem _root_.Summable.countable_support_ennreal {f : α → ℝ≥0∞} (h : ∑' (i : α), f i ≠ ∞) :
    f.support.Countable := by
  lift f to α → ℝ≥0 using ENNReal.ne_top_of_tsum_ne_top h
  simpa [support] using (ENNReal.tsum_coe_ne_top_iff_summable.1 h).countable_support_nnreal

/-- A series of non-negative real numbers converges to `r` in the sense of `HasSum` if and only if
the sequence of partial sum converges to `r`. -/
theorem hasSum_iff_tendsto_nat_of_nonneg {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i) (r : ℝ) :
    HasSum f r ↔ Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop (𝓝 r) := by
  lift f to ℕ → ℝ≥0 using hf
  simp only [HasSum, ← NNReal.coe_sum, NNReal.tendsto_coe']
  exact exists_congr fun hr => NNReal.hasSum_iff_tendsto_nat

theorem ENNReal.ofReal_tsum_of_nonneg {f : α → ℝ} (hf_nonneg : ∀ n, 0 ≤ f n) (hf : Summable f) :
    ENNReal.ofReal (∑' n, f n) = ∑' n, ENNReal.ofReal (f n) := by
  simp_rw [ENNReal.ofReal, ENNReal.tsum_coe_eq (NNReal.hasSum_real_toNNReal_of_nonneg hf_nonneg hf)]

section tprod

theorem ENNReal.multipliable_of_le_one {f : α → ℝ≥0∞} (h₀ : ∀ i, f i ≤ 1) :
    Multipliable f :=
  ⟨_, _root_.hasProd_of_isGLB_of_le_one _ h₀ (isGLB_sInf _)⟩

theorem ENNReal.hasProd_iInf_prod {f : α → ℝ≥0∞} (h₀ : ∀ i, f i ≤ 1) :
    HasProd f (⨅ s : Finset α, ∏ i ∈ s, f i) :=
  tendsto_atTop_iInf (Finset.prod_anti_set_of_le_one' h₀)

theorem ENNReal.tprod_eq_iInf_prod {f : α → ℝ≥0∞} (h₀ : ∀ i, f i ≤ 1) :
    ∏' i, f i = ⨅ s : Finset α, ∏ i ∈ s, f i :=
  (hasProd_iInf_prod h₀).tprod_eq

end tprod

variable [PseudoEMetricSpace α]

/-- If the extended distance between consecutive points of a sequence is estimated
by a summable series of `NNReal`s, then the original sequence is a Cauchy sequence. -/
theorem cauchySeq_of_edist_le_of_summable {f : ℕ → α} (d : ℕ → ℝ≥0)
    (hf : ∀ n, edist (f n) (f n.succ) ≤ d n) (hd : Summable d) : CauchySeq f := by
  refine EMetric.cauchySeq_iff_NNReal.2 fun ε εpos ↦ ?_
  -- Actually we need partial sums of `d` to be a Cauchy sequence.
  replace hd : CauchySeq fun n : ℕ ↦ ∑ x ∈ Finset.range n, d x :=
    let ⟨_, H⟩ := hd
    H.tendsto_sum_nat.cauchySeq
  -- Now we take the same `N` as in one of the definitions of a Cauchy sequence.
  refine (Metric.cauchySeq_iff'.1 hd ε (NNReal.coe_pos.2 εpos)).imp fun N hN n hn ↦ ?_
  specialize hN n hn
  -- We simplify the known inequality.
  rw [dist_nndist, NNReal.nndist_eq, ← Finset.sum_range_add_sum_Ico _ hn, add_tsub_cancel_left,
    NNReal.coe_lt_coe, max_lt_iff] at hN
  rw [edist_comm]
  -- Then use `hf` to simplify the goal to the same form.
  refine lt_of_le_of_lt (edist_le_Ico_sum_of_edist_le hn fun _ _ ↦ hf _) ?_
  exact mod_cast hN.1

theorem cauchySeq_of_edist_le_of_tsum_ne_top {f : ℕ → α} (d : ℕ → ℝ≥0∞)
    (hf : ∀ n, edist (f n) (f n.succ) ≤ d n) (hd : tsum d ≠ ∞) : CauchySeq f := by
  lift d to ℕ → NNReal using fun i => ENNReal.ne_top_of_tsum_ne_top hd i
  rw [ENNReal.tsum_coe_ne_top_iff_summable] at hd
  exact cauchySeq_of_edist_le_of_summable d hf hd

/-- If `edist (f n) (f (n+1))` is bounded above by a function `d : ℕ → ℝ≥0∞`,
then the distance from `f n` to the limit is bounded by `∑'_{k=n}^∞ d k`. -/
theorem edist_le_tsum_of_edist_le_of_tendsto {f : ℕ → α} (d : ℕ → ℝ≥0∞)
    (hf : ∀ n, edist (f n) (f n.succ) ≤ d n) {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : ℕ) :
    edist (f n) a ≤ ∑' m, d (n + m) := by
  refine le_of_tendsto (tendsto_const_nhds.edist ha) (mem_atTop_sets.2 ⟨n, fun m hnm => ?_⟩)
  change edist _ _ ≤ _
  refine le_trans (edist_le_Ico_sum_of_edist_le hnm fun _ _ => hf _) ?_
  rw [Finset.sum_Ico_eq_sum_range]
  exact ENNReal.summable.sum_le_tsum _ (fun _ _ => zero_le _)

/-- If `edist (f n) (f (n+1))` is bounded above by a function `d : ℕ → ℝ≥0∞`,
then the distance from `f 0` to the limit is bounded by `∑'_{k=0}^∞ d k`. -/
theorem edist_le_tsum_of_edist_le_of_tendsto₀ {f : ℕ → α} (d : ℕ → ℝ≥0∞)
    (hf : ∀ n, edist (f n) (f n.succ) ≤ d n) {a : α} (ha : Tendsto f atTop (𝓝 a)) :
    edist (f 0) a ≤ ∑' m, d m := by simpa using edist_le_tsum_of_edist_le_of_tendsto d hf ha 0


namespace ENNReal

variable {α : Type*} (s : Set α)

lemma tsum_set_one : ∑' _ : s, (1 : ℝ≥0∞) = s.encard := by
  obtain (hfin | hinf) := Set.finite_or_infinite s
  · lift s to Finset α using hfin
    simp [tsum_fintype]
  · have : Infinite s := infinite_coe_iff.mpr hinf
    rw [tsum_const_eq_top_of_ne_zero one_ne_zero, encard_eq_top hinf, ENat.toENNReal_top]

lemma tsum_set_const (c : ℝ≥0∞) : ∑' _ : s, c = s.encard * c := by
  simp [← tsum_set_one, ← ENNReal.tsum_mul_right]

@[simp]
lemma tsum_one : ∑' _ : α, (1 : ℝ≥0∞) = ENat.card α := by
  rw [← tsum_univ]; simpa [encard_univ] using tsum_set_one univ

@[simp]
lemma tsum_const (c : ℝ≥0∞) : ∑' _ : α, c = ENat.card α * c := by
  rw [← tsum_univ]; simpa [encard_univ] using tsum_set_const univ c

end ENNReal
