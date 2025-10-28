/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Johannes Hölzl, Yury Kudryashov, Patrick Massot
-/
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Iterate
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Instances.Rat

/-!
# A collection of specific limit computations

This file, by design, is independent of `NormedSpace` in the import hierarchy.  It contains
important specific limit computations in metric spaces, in ordered rings/fields, and in specific
instances of these such as `ℝ`, `ℝ≥0` and `ℝ≥0∞`.
-/

assert_not_exists Module.Basis NormedSpace

noncomputable section

open Set Function Filter Finset Metric Topology Nat uniformity NNReal ENNReal

variable {α : Type*} {β : Type*} {ι : Type*}

theorem NNRat.tendsto_inv_atTop_nhds_zero_nat : Tendsto (fun n : ℕ ↦ (n : ℚ≥0)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

theorem NNRat.tendsto_algebraMap_inv_atTop_nhds_zero_nat (𝕜 : Type*) [Semiring 𝕜]
    [Algebra ℚ≥0 𝕜] [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] :
    Tendsto (algebraMap ℚ≥0 𝕜 ∘ fun n : ℕ ↦ (n : ℚ≥0)⁻¹) atTop (𝓝 0) := by
  convert (continuous_algebraMap ℚ≥0 𝕜).continuousAt.tendsto.comp
    tendsto_inv_atTop_nhds_zero_nat
  rw [map_zero]

theorem tendsto_inv_atTop_nhds_zero_nat {𝕜 : Type*} [Semifield 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] :
    Tendsto (fun n : ℕ ↦ (n : 𝕜)⁻¹) atTop (𝓝 0) := by
  convert NNRat.tendsto_algebraMap_inv_atTop_nhds_zero_nat 𝕜
  simp

theorem tendsto_const_div_atTop_nhds_zero_nat {𝕜 : Type*} [Semifield 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] [ContinuousMul 𝕜] (C : 𝕜) :
    Tendsto (fun n : ℕ ↦ C / n) atTop (𝓝 0) := by
  simpa only [mul_zero, div_eq_mul_inv] using
    (tendsto_const_nhds (x := C)).mul tendsto_inv_atTop_nhds_zero_nat

theorem tendsto_one_div_atTop_nhds_zero_nat {𝕜 : Type*} [Semifield 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] :
    Tendsto (fun n : ℕ ↦ 1 / (n : 𝕜)) atTop (𝓝 0) := by
  simp [tendsto_inv_atTop_nhds_zero_nat]

theorem EReal.tendsto_const_div_atTop_nhds_zero_nat {C : EReal} (h : C ≠ ⊥) (h' : C ≠ ⊤) :
    Tendsto (fun n : ℕ ↦ C / n) atTop (𝓝 0) := by
  have : (fun n : ℕ ↦ C / n) = fun n : ℕ ↦ ((C.toReal / n : ℝ) : EReal) := by
    ext n
    nth_rw 1 [← coe_toReal h' h, ← coe_coe_eq_natCast n, ← coe_div C.toReal n]
  rw [this, ← coe_zero, tendsto_coe]
  exact _root_.tendsto_const_div_atTop_nhds_zero_nat C.toReal

theorem tendsto_one_div_add_atTop_nhds_zero_nat {𝕜 : Type*} [Semifield 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] :
    Tendsto (fun n : ℕ ↦ 1 / ((n : 𝕜) + 1)) atTop (𝓝 0) :=
  suffices Tendsto (fun n : ℕ ↦ 1 / (↑(n + 1) : 𝕜)) atTop (𝓝 0) by simpa
  (tendsto_add_atTop_iff_nat 1).2 tendsto_one_div_atTop_nhds_zero_nat

theorem tendsto_algebraMap_inv_atTop_nhds_zero_nat {𝕜 : Type*} (A : Type*)
    [Semifield 𝕜] [CharZero 𝕜] [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜]
    [Semiring A] [Algebra 𝕜 A] [TopologicalSpace A] [ContinuousSMul 𝕜 A] :
    Tendsto (algebraMap 𝕜 A ∘ fun n : ℕ ↦ (n : 𝕜)⁻¹) atTop (𝓝 0) := by
  convert (continuous_algebraMap 𝕜 A).continuousAt.tendsto.comp tendsto_inv_atTop_nhds_zero_nat
  rw [map_zero]

/-- The limit of `n / (n + x)` is 1, for any constant `x` (valid in `ℝ` or any topological division
algebra over `ℚ≥0`, e.g., `ℂ`). -/
theorem tendsto_natCast_div_add_atTop {𝕜 : Type*} [DivisionSemiring 𝕜] [TopologicalSpace 𝕜]
    [CharZero 𝕜] [ContinuousSMul ℚ≥0 𝕜] [IsTopologicalSemiring 𝕜] [ContinuousInv₀ 𝕜] (x : 𝕜) :
    Tendsto (fun n : ℕ ↦ (n : 𝕜) / (n + x)) atTop (𝓝 1) := by
  convert Tendsto.congr' ((eventually_ne_atTop 0).mp (Eventually.of_forall fun n hn ↦ _)) _
  · exact fun n : ℕ ↦ 1 / (1 + x / n)
  · simp [Nat.cast_ne_zero.mpr hn, add_div']
  · have : 𝓝 (1 : 𝕜) = 𝓝 (1 / (1 + x * (0 : 𝕜))) := by
      rw [mul_zero, add_zero, div_one]
    rw [this]
    refine tendsto_const_nhds.div (tendsto_const_nhds.add ?_) (by simp)
    simp_rw [div_eq_mul_inv]
    refine tendsto_const_nhds.mul ?_
    have := ((continuous_algebraMap ℚ≥0 𝕜).tendsto _).comp tendsto_inv_atTop_nhds_zero_nat
    rw [map_zero, Filter.tendsto_atTop'] at this
    refine Iff.mpr tendsto_atTop' ?_
    intros
    simp_all only [comp_apply, map_inv₀, map_natCast]

theorem tendsto_add_mul_div_add_mul_atTop_nhds {𝕜 : Type*} [Semifield 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] [IsTopologicalSemiring 𝕜] [ContinuousInv₀ 𝕜]
    (a b c : 𝕜) {d : 𝕜} (hd : d ≠ 0) :
    Tendsto (fun k : ℕ ↦ (a + c * k) / (b + d * k)) atTop (𝓝 (c / d)) := by
  apply Filter.Tendsto.congr'
  case f₁ => exact fun k ↦ (a * (↑k)⁻¹ + c) / (b * (↑k)⁻¹ + d)
  · refine (eventually_ne_atTop 0).mp (Eventually.of_forall ?_)
    intro h hx
    dsimp
    field_simp (discharger := norm_cast)
  · apply Filter.Tendsto.div _ _ hd
    all_goals
      apply zero_add (_ : 𝕜) ▸ Filter.Tendsto.add_const _ _
      apply mul_zero (_ : 𝕜) ▸ Filter.Tendsto.const_mul _ _
      exact tendsto_inv_atTop_nhds_zero_nat

/-- For any positive `m : ℕ`, `((n % m : ℕ) : ℝ) / (n : ℝ)` tends to `0` as `n` tends to `∞`. -/
theorem tendsto_mod_div_atTop_nhds_zero_nat {m : ℕ} (hm : 0 < m) :
    Tendsto (fun n : ℕ => ((n % m : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have h0 : ∀ᶠ n : ℕ in atTop, 0 ≤ (fun n : ℕ => ((n % m : ℕ) : ℝ)) n := by aesop
  exact tendsto_bdd_div_atTop_nhds_zero h0
    (.of_forall (fun n ↦ cast_le.mpr (mod_lt n hm).le)) tendsto_natCast_atTop_atTop

/-- If `a ≠ 0`, `(a * x + c)⁻¹` tends to `0` as `x` tends to `∞`. -/
theorem tendsto_mul_add_inv_atTop_nhds_zero (a c : ℝ) (ha : a ≠ 0) :
    Tendsto (fun x => (a * x + c)⁻¹) atTop (𝓝 0) := by
  obtain ha' | ha' := lt_or_gt_of_ne ha
  · exact tendsto_inv_atBot_zero.comp
      (tendsto_atBot_add_const_right _ c (tendsto_id.const_mul_atTop_of_neg ha'))
  · exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ c (tendsto_id.const_mul_atTop ha'))

theorem Filter.EventuallyEq.div_mul_cancel {α G : Type*} [GroupWithZero G] {f g : α → G}
    {l : Filter α} (hg : Tendsto g l (𝓟 {0}ᶜ)) : (fun x ↦ f x / g x * g x) =ᶠ[l] fun x ↦ f x := by
  filter_upwards [hg.le_comap <| preimage_mem_comap (m := g) (mem_principal_self {0}ᶜ)] with x hx
  simp_all

/-- If `g` tends to `∞`, then eventually for all `x` we have `(f x / g x) * g x = f x`. -/
theorem Filter.EventuallyEq.div_mul_cancel_atTop {α K : Type*}
    [Semifield K] [LinearOrder K] [IsStrictOrderedRing K]
    {f g : α → K} {l : Filter α} (hg : Tendsto g l atTop) :
    (fun x ↦ f x / g x * g x) =ᶠ[l] fun x ↦ f x :=
  div_mul_cancel <| hg.mono_right <| le_principal_iff.mpr <|
    mem_of_superset (Ioi_mem_atTop 0) <| by simp

/-- If when `x` tends to `∞`, `g` tends to `∞` and `f x / g x` tends to a positive
  constant, then `f` tends to `∞`. -/
theorem Filter.Tendsto.num {α K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [TopologicalSpace K] [OrderTopology K]
    {f g : α → K} {l : Filter α} (hg : Tendsto g l atTop) {a : K} (ha : 0 < a)
    (hlim : Tendsto (fun x => f x / g x) l (𝓝 a)) :
    Tendsto f l atTop :=
  (hlim.pos_mul_atTop ha hg).congr' (EventuallyEq.div_mul_cancel_atTop hg)

/-- If when `x` tends to `∞`, `g` tends to `∞` and `f x / g x` tends to a positive
  constant, then `f` tends to `∞`. -/
theorem Filter.Tendsto.den {α K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [TopologicalSpace K] [OrderTopology K]
    [ContinuousInv K] {f g : α → K} {l : Filter α} (hf : Tendsto f l atTop) {a : K} (ha : 0 < a)
    (hlim : Tendsto (fun x => f x / g x) l (𝓝 a)) :
    Tendsto g l atTop :=
  have hlim' : Tendsto (fun x => g x / f x) l (𝓝 a⁻¹) := by
    simp_rw [← inv_div (f _)]
    exact Filter.Tendsto.inv (f := fun x => f x / g x) hlim
  (hlim'.pos_mul_atTop (inv_pos_of_pos ha) hf).congr' (.div_mul_cancel_atTop hf)

/-- If when `x` tends to `∞`, `f x / g x` tends to a positive constant, then `f` tends to `∞` if
  and only if `g` tends to `∞`. -/
theorem Filter.Tendsto.num_atTop_iff_den_atTop {α K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [TopologicalSpace K]
    [OrderTopology K] [ContinuousInv K] {f g : α → K} {l : Filter α} {a : K} (ha : 0 < a)
    (hlim : Tendsto (fun x => f x / g x) l (𝓝 a)) :
    Tendsto f l atTop ↔ Tendsto g l atTop :=
  ⟨fun hf ↦ hf.den ha hlim, fun hg ↦ hg.num ha hlim⟩

/-! ### Powers -/


theorem tendsto_add_one_pow_atTop_atTop_of_pos
    [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [Archimedean α] {r : α}
    (h : 0 < r) : Tendsto (fun n : ℕ ↦ (r + 1) ^ n) atTop atTop :=
  tendsto_atTop_atTop_of_monotone' (pow_right_mono₀ <| le_add_of_nonneg_left h.le) <|
    not_bddAbove_iff.2 fun _ ↦ Set.exists_range_iff.2 <| add_one_pow_unbounded_of_pos _ h

theorem tendsto_pow_atTop_atTop_of_one_lt
    [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α] [Archimedean α] {r : α}
    (h : 1 < r) : Tendsto (fun n : ℕ ↦ r ^ n) atTop atTop := by
  obtain ⟨r, r0, rfl⟩ := exists_pos_add_of_lt' h
  rw [add_comm]
  exact tendsto_add_one_pow_atTop_atTop_of_pos r0

theorem tendsto_pow_atTop_nhds_zero_of_lt_one {𝕜 : Type*}
    [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [ExistsAddOfLE 𝕜] [Archimedean 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜] {r : 𝕜} (h₁ : 0 ≤ r) (h₂ : r < 1) :
    Tendsto (fun n : ℕ ↦ r ^ n) atTop (𝓝 0) :=
  h₁.eq_or_lt.elim
    (fun hr ↦ (tendsto_add_atTop_iff_nat 1).mp <| by
      simp [_root_.pow_succ, ← hr])
    (fun hr ↦
      have := (one_lt_inv₀ hr).2 h₂ |> tendsto_pow_atTop_atTop_of_one_lt
      (tendsto_inv_atTop_zero.comp this).congr fun n ↦ by simp)

@[simp] theorem tendsto_pow_atTop_nhds_zero_iff {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Archimedean 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜] {r : 𝕜} :
    Tendsto (fun n : ℕ ↦ r ^ n) atTop (𝓝 0) ↔ |r| < 1 := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine ⟨fun h ↦ by_contra (fun hr_le ↦ ?_), fun h ↦ ?_⟩
  · by_cases hr : 1 = |r|
    · replace h : Tendsto (fun n : ℕ ↦ |r| ^ n) atTop (𝓝 0) := by simpa only [← abs_pow, h]
      simp only [hr.symm, one_pow] at h
      exact zero_ne_one <| tendsto_nhds_unique h tendsto_const_nhds
    · apply @not_tendsto_nhds_of_tendsto_atTop 𝕜 ℕ _ _ _ _ atTop _ (fun n ↦ |r| ^ n) _ 0 _
      · refine (pow_right_strictMono₀ <| lt_of_le_of_ne (le_of_not_gt hr_le)
          hr).monotone.tendsto_atTop_atTop (fun b ↦ ?_)
        obtain ⟨n, hn⟩ := (pow_unbounded_of_one_lt b (lt_of_le_of_ne (le_of_not_gt hr_le) hr))
        exact ⟨n, le_of_lt hn⟩
      · simpa only [← abs_pow]
  · simpa only [← abs_pow] using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg r)) h

theorem tendsto_pow_atTop_nhdsWithin_zero_of_lt_one {𝕜 : Type*}
    [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [ExistsAddOfLE 𝕜]
    [Archimedean 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] {r : 𝕜} (h₁ : 0 < r) (h₂ : r < 1) :
    Tendsto (fun n : ℕ ↦ r ^ n) atTop (𝓝[>] 0) :=
  tendsto_inf.2
    ⟨tendsto_pow_atTop_nhds_zero_of_lt_one h₁.le h₂,
      tendsto_principal.2 <| Eventually.of_forall fun _ ↦ pow_pos h₁ _⟩

theorem uniformity_basis_dist_pow_of_lt_one {α : Type*} [PseudoMetricSpace α] {r : ℝ} (h₀ : 0 < r)
    (h₁ : r < 1) :
    (uniformity α).HasBasis (fun _ : ℕ ↦ True) fun k ↦ { p : α × α | dist p.1 p.2 < r ^ k } :=
  Metric.mk_uniformity_basis (fun _ _ ↦ pow_pos h₀ _) fun _ ε0 ↦
    (exists_pow_lt_of_lt_one ε0 h₁).imp fun _ hk ↦ ⟨trivial, hk.le⟩

theorem geom_lt {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 0 < n)
    (h : ∀ k < n, c * u k < u (k + 1)) : c ^ n * u 0 < u n := by
  apply (monotone_mul_left_of_nonneg hc).seq_pos_lt_seq_of_le_of_lt hn _ _ h
  · simp
  · simp [_root_.pow_succ', mul_assoc, le_refl]

theorem geom_le {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (h : ∀ k < n, c * u k ≤ u (k + 1)) :
    c ^ n * u 0 ≤ u n := by
  apply (monotone_mul_left_of_nonneg hc).seq_le_seq n _ _ h <;>
    simp [_root_.pow_succ', mul_assoc, le_refl]

theorem lt_geom {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 0 < n)
    (h : ∀ k < n, u (k + 1) < c * u k) : u n < c ^ n * u 0 := by
  apply (monotone_mul_left_of_nonneg hc).seq_pos_lt_seq_of_lt_of_le hn _ h _
  · simp
  · simp [_root_.pow_succ', mul_assoc, le_refl]

theorem le_geom {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (h : ∀ k < n, u (k + 1) ≤ c * u k) :
    u n ≤ c ^ n * u 0 := by
  apply (monotone_mul_left_of_nonneg hc).seq_le_seq n _ h _ <;>
    simp [_root_.pow_succ', mul_assoc, le_refl]

/-- If a sequence `v` of real numbers satisfies `k * v n ≤ v (n+1)` with `1 < k`,
then it goes to +∞. -/
theorem tendsto_atTop_of_geom_le {v : ℕ → ℝ} {c : ℝ} (h₀ : 0 < v 0) (hc : 1 < c)
    (hu : ∀ n, c * v n ≤ v (n + 1)) : Tendsto v atTop atTop :=
  (tendsto_atTop_mono fun n ↦ geom_le (zero_le_one.trans hc.le) n fun k _ ↦ hu k) <|
    (tendsto_pow_atTop_atTop_of_one_lt hc).atTop_mul_const h₀

theorem NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one {r : ℝ≥0} (hr : r < 1) :
    Tendsto (fun n : ℕ ↦ r ^ n) atTop (𝓝 0) :=
  NNReal.tendsto_coe.1 <| by
    simp only [NNReal.coe_pow, NNReal.coe_zero,
      _root_.tendsto_pow_atTop_nhds_zero_of_lt_one r.coe_nonneg hr]

@[simp]
protected theorem NNReal.tendsto_pow_atTop_nhds_zero_iff {r : ℝ≥0} :
    Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) ↔ r < 1 :=
  ⟨fun h => by simpa [coe_pow, coe_zero, abs_eq, coe_lt_one, val_eq_coe] using
    tendsto_pow_atTop_nhds_zero_iff.mp <| tendsto_coe.mpr h, tendsto_pow_atTop_nhds_zero_of_lt_one⟩

theorem ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one {r : ℝ≥0∞} (hr : r < 1) :
    Tendsto (fun n : ℕ ↦ r ^ n) atTop (𝓝 0) := by
  rcases ENNReal.lt_iff_exists_coe.1 hr with ⟨r, rfl, hr'⟩
  rw [← ENNReal.coe_zero]
  norm_cast at *
  apply NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr

@[simp]
protected theorem ENNReal.tendsto_pow_atTop_nhds_zero_iff {r : ℝ≥0∞} :
    Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) ↔ r < 1 := by
  refine ⟨fun h ↦ ?_, tendsto_pow_atTop_nhds_zero_of_lt_one⟩
  lift r to NNReal
  · refine fun hr ↦ top_ne_zero (tendsto_nhds_unique (EventuallyEq.tendsto ?_) (hr ▸ h))
    exact eventually_atTop.mpr ⟨1, fun _ hn ↦ pow_eq_top_iff.mpr ⟨rfl, Nat.pos_iff_ne_zero.mp hn⟩⟩
  rw [← coe_zero] at h
  norm_cast at h ⊢
  exact NNReal.tendsto_pow_atTop_nhds_zero_iff.mp h

@[simp]
protected theorem ENNReal.tendsto_pow_atTop_nhds_top_iff {r : ℝ≥0∞} :
    Tendsto (fun n ↦ r ^ n) atTop (𝓝 ∞) ↔ 1 < r := by
  refine ⟨?_, ?_⟩
  · contrapose!
    intro r_le_one h_tends
    specialize h_tends (Ioi_mem_nhds one_lt_top)
    simp only [Filter.mem_map, mem_atTop_sets, ge_iff_le, Set.mem_preimage, Set.mem_Ioi] at h_tends
    obtain ⟨n, hn⟩ := h_tends
    exact lt_irrefl _ <| lt_of_lt_of_le (hn n le_rfl) <| pow_le_one₀ (zero_le _) r_le_one
  · intro r_gt_one
    have obs := @Tendsto.inv ℝ≥0∞ ℕ _ _ _ (fun n ↦ (r⁻¹) ^ n) atTop 0
    simp only [ENNReal.tendsto_pow_atTop_nhds_zero_iff, inv_zero] at obs
    simpa [← ENNReal.inv_pow] using obs <| ENNReal.inv_lt_one.mpr r_gt_one

lemma ENNReal.eq_zero_of_le_mul_pow {x r : ℝ≥0∞} {ε : ℝ≥0} (hr : r < 1)
    (h : ∀ n : ℕ, x ≤ ε * r ^ n) : x = 0 := by
  rw [← nonpos_iff_eq_zero]
  refine ge_of_tendsto' (f := fun (n : ℕ) ↦ ε * r ^ n) (x := atTop) ?_ h
  rw [← mul_zero (M₀ := ℝ≥0∞) (a := ε)]
  exact Tendsto.const_mul (tendsto_pow_atTop_nhds_zero_of_lt_one hr) (Or.inr coe_ne_top)

/-! ### Geometric series -/

section Geometric

theorem hasSum_geometric_of_lt_one {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
    HasSum (fun n : ℕ ↦ r ^ n) (1 - r)⁻¹ :=
  have : r ≠ 1 := ne_of_lt h₂
  have : Tendsto (fun n ↦ (r ^ n - 1) * (r - 1)⁻¹) atTop (𝓝 ((0 - 1) * (r - 1)⁻¹)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one h₁ h₂).sub tendsto_const_nhds).mul tendsto_const_nhds
  (hasSum_iff_tendsto_nat_of_nonneg (pow_nonneg h₁) _).mpr <| by
    simp_all [neg_inv, geom_sum_eq, div_eq_mul_inv]

theorem summable_geometric_of_lt_one {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
    Summable fun n : ℕ ↦ r ^ n :=
  ⟨_, hasSum_geometric_of_lt_one h₁ h₂⟩


theorem tsum_geometric_of_lt_one {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) : ∑' n : ℕ, r ^ n = (1 - r)⁻¹ :=
  (hasSum_geometric_of_lt_one h₁ h₂).tsum_eq

theorem hasSum_geometric_two : HasSum (fun n : ℕ ↦ ((1 : ℝ) / 2) ^ n) 2 := by
  convert hasSum_geometric_of_lt_one _ _ <;> norm_num

theorem summable_geometric_two : Summable fun n : ℕ ↦ ((1 : ℝ) / 2) ^ n :=
  ⟨_, hasSum_geometric_two⟩

theorem summable_geometric_two_encode {ι : Type*} [Encodable ι] :
    Summable fun i : ι ↦ (1 / 2 : ℝ) ^ Encodable.encode i :=
  summable_geometric_two.comp_injective Encodable.encode_injective

theorem tsum_geometric_two : (∑' n : ℕ, ((1 : ℝ) / 2) ^ n) = 2 :=
  hasSum_geometric_two.tsum_eq

theorem sum_geometric_two_le (n : ℕ) : (∑ i ∈ range n, (1 / (2 : ℝ)) ^ i) ≤ 2 := by
  have : ∀ i, 0 ≤ (1 / (2 : ℝ)) ^ i := by
    intro i
    apply pow_nonneg
    norm_num
  convert summable_geometric_two.sum_le_tsum (range n) (fun i _ ↦ this i)
  exact tsum_geometric_two.symm

theorem tsum_geometric_inv_two : (∑' n : ℕ, (2 : ℝ)⁻¹ ^ n) = 2 :=
  (inv_eq_one_div (2 : ℝ)).symm ▸ tsum_geometric_two

/-- The sum of `2⁻¹ ^ i` for `n ≤ i` equals `2 * 2⁻¹ ^ n`. -/
theorem tsum_geometric_inv_two_ge (n : ℕ) :
    (∑' i, ite (n ≤ i) ((2 : ℝ)⁻¹ ^ i) 0) = 2 * 2⁻¹ ^ n := by
  have A : Summable fun i : ℕ ↦ ite (n ≤ i) ((2⁻¹ : ℝ) ^ i) 0 := by
    simpa only [← piecewise_eq_indicator, one_div]
      using summable_geometric_two.indicator {i | n ≤ i}
  have B : ((Finset.range n).sum fun i : ℕ ↦ ite (n ≤ i) ((2⁻¹ : ℝ) ^ i) 0) = 0 :=
    Finset.sum_eq_zero fun i hi ↦
      ite_eq_right_iff.2 fun h ↦ (lt_irrefl _ ((Finset.mem_range.1 hi).trans_le h)).elim
  simp only [← Summable.sum_add_tsum_nat_add n A, B, if_true, zero_add, zero_le',
    le_add_iff_nonneg_left, pow_add, _root_.tsum_mul_right, tsum_geometric_inv_two]

theorem hasSum_geometric_two' (a : ℝ) : HasSum (fun n : ℕ ↦ a / 2 / 2 ^ n) a := by
  convert HasSum.mul_left (a / 2)
      (hasSum_geometric_of_lt_one (le_of_lt one_half_pos) one_half_lt_one) using 1
  · funext n
    simp only [one_div, inv_pow]
    rfl
  · norm_num

theorem summable_geometric_two' (a : ℝ) : Summable fun n : ℕ ↦ a / 2 / 2 ^ n :=
  ⟨a, hasSum_geometric_two' a⟩

theorem tsum_geometric_two' (a : ℝ) : ∑' n : ℕ, a / 2 / 2 ^ n = a :=
  (hasSum_geometric_two' a).tsum_eq

/-- **Sum of a Geometric Series** -/
theorem NNReal.hasSum_geometric {r : ℝ≥0} (hr : r < 1) : HasSum (fun n : ℕ ↦ r ^ n) (1 - r)⁻¹ := by
  apply NNReal.hasSum_coe.1
  push_cast
  rw [NNReal.coe_sub (le_of_lt hr)]
  exact hasSum_geometric_of_lt_one r.coe_nonneg hr

theorem NNReal.summable_geometric {r : ℝ≥0} (hr : r < 1) : Summable fun n : ℕ ↦ r ^ n :=
  ⟨_, NNReal.hasSum_geometric hr⟩

theorem tsum_geometric_nnreal {r : ℝ≥0} (hr : r < 1) : ∑' n : ℕ, r ^ n = (1 - r)⁻¹ :=
  (NNReal.hasSum_geometric hr).tsum_eq

/-- The series `pow r` converges to `(1-r)⁻¹`. For `r < 1` the RHS is a finite number,
and for `1 ≤ r` the RHS equals `∞`. -/
@[simp]
theorem ENNReal.tsum_geometric (r : ℝ≥0∞) : ∑' n : ℕ, r ^ n = (1 - r)⁻¹ := by
  rcases lt_or_ge r 1 with hr | hr
  · rcases ENNReal.lt_iff_exists_coe.1 hr with ⟨r, rfl, hr'⟩
    norm_cast at *
    convert ENNReal.tsum_coe_eq (NNReal.hasSum_geometric hr)
    rw [ENNReal.coe_inv <| ne_of_gt <| tsub_pos_iff_lt.2 hr, coe_sub, coe_one]
  · rw [tsub_eq_zero_iff_le.mpr hr, ENNReal.inv_zero, ENNReal.tsum_eq_iSup_nat, iSup_eq_top]
    refine fun a ha ↦
      (ENNReal.exists_nat_gt (lt_top_iff_ne_top.1 ha)).imp fun n hn ↦ lt_of_lt_of_le hn ?_
    calc
      (n : ℝ≥0∞) = ∑ i ∈ range n, 1 := by rw [sum_const, nsmul_one, card_range]
      _ ≤ ∑ i ∈ range n, r ^ i := by gcongr; apply one_le_pow₀ hr

theorem ENNReal.tsum_geometric_add_one (r : ℝ≥0∞) : ∑' n : ℕ, r ^ (n + 1) = r * (1 - r)⁻¹ := by
  simp only [_root_.pow_succ', ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

lemma ENNReal.tsum_two_zpow_neg_add_one :
    ∑' m : ℕ, 2 ^ (-1 - m : ℤ) = (1 : ℝ≥0∞) := by
  simp_rw [neg_sub_left, ENNReal.zpow_neg, ← Nat.cast_one (R := ℤ), ← Nat.cast_add, zpow_natCast,
    ENNReal.inv_pow, ENNReal.tsum_geometric_add_one, one_sub_inv_two, inv_inv]
  exact ENNReal.inv_mul_cancel (Ne.symm (NeZero.ne' 2)) (Ne.symm top_ne_ofNat)

open Encodable

protected lemma ENNReal.tsum_geometric_two : ∑' n, (2⁻¹ : ℝ≥0∞) ^ n = 2 := by simp

lemma ENNReal.tsum_geometric_two_encode_le_two {ι : Type*} [Encodable ι] :
    ∑' i : ι, (2⁻¹ : ℝ≥0∞) ^ encode i ≤ 2 :=
  (ENNReal.tsum_comp_le_tsum_of_injective encode_injective _).trans_eq ENNReal.tsum_geometric_two

lemma tsum_geometric_lt_top {r : ℝ≥0∞} : ∑' n, r ^ n < ∞ ↔ r < 1 := by simp

lemma tsum_geometric_encode_lt_top {r : ℝ≥0∞} (hr : r < 1) {ι : Type*} [Encodable ι] :
    ∑' i : ι, (r : ℝ≥0∞) ^ encode i < ∞ :=
  (ENNReal.tsum_comp_le_tsum_of_injective encode_injective _).trans_lt <| by simpa

end Geometric

/-!
### Sequences with geometrically decaying distance in metric spaces

In this paragraph, we discuss sequences in metric spaces or emetric spaces for which the distance
between two consecutive terms decays geometrically. We show that such sequences are Cauchy
sequences, and bound their distances to the limit. We also discuss series with geometrically
decaying terms.
-/


section EdistLeGeometric

variable [PseudoEMetricSpace α] (r C : ℝ≥0∞) (hr : r < 1) (hC : C ≠ ⊤) {f : ℕ → α}
  (hu : ∀ n, edist (f n) (f (n + 1)) ≤ C * r ^ n)

include hr hC hu in
/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, `C ≠ ∞`, `r < 1`,
then `f` is a Cauchy sequence. -/
theorem cauchySeq_of_edist_le_geometric : CauchySeq f := by
  refine cauchySeq_of_edist_le_of_tsum_ne_top _ hu ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  have := (tsub_pos_iff_lt.2 hr).ne'
  finiteness

include hu in
/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, then the distance from
`f n` to the limit of `f` is bounded above by `C * r^n / (1 - r)`. -/
theorem edist_le_of_edist_le_geometric_of_tendsto {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : ℕ) :
    edist (f n) a ≤ C * r ^ n / (1 - r) := by
  convert edist_le_tsum_of_edist_le_of_tendsto _ hu ha _
  simp only [pow_add, ENNReal.tsum_mul_left, ENNReal.tsum_geometric, div_eq_mul_inv, mul_assoc]

include hu in
/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, then the distance from
`f 0` to the limit of `f` is bounded above by `C / (1 - r)`. -/
theorem edist_le_of_edist_le_geometric_of_tendsto₀ {a : α} (ha : Tendsto f atTop (𝓝 a)) :
    edist (f 0) a ≤ C / (1 - r) := by
  simpa only [_root_.pow_zero, mul_one] using edist_le_of_edist_le_geometric_of_tendsto r C hu ha 0

end EdistLeGeometric

section EdistLeGeometricTwo

variable [PseudoEMetricSpace α] (C : ℝ≥0∞) (hC : C ≠ ⊤) {f : ℕ → α}
  (hu : ∀ n, edist (f n) (f (n + 1)) ≤ C / 2 ^ n) {a : α} (ha : Tendsto f atTop (𝓝 a))

include hC hu in
/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then `f` is a Cauchy sequence. -/
theorem cauchySeq_of_edist_le_geometric_two : CauchySeq f := by
  simp only [div_eq_mul_inv, ENNReal.inv_pow] at hu
  refine cauchySeq_of_edist_le_geometric 2⁻¹ C ?_ hC hu
  simp

include hu ha in
/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then the distance from
`f n` to the limit of `f` is bounded above by `2 * C * 2^-n`. -/
theorem edist_le_of_edist_le_geometric_two_of_tendsto (n : ℕ) : edist (f n) a ≤ 2 * C / 2 ^ n := by
  simp only [div_eq_mul_inv, ENNReal.inv_pow] at *
  rw [mul_assoc, mul_comm]
  convert edist_le_of_edist_le_geometric_of_tendsto 2⁻¹ C hu ha n using 1
  rw [ENNReal.one_sub_inv_two, div_eq_mul_inv, inv_inv]

include hu ha in
/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then the distance from
`f 0` to the limit of `f` is bounded above by `2 * C`. -/
theorem edist_le_of_edist_le_geometric_two_of_tendsto₀ : edist (f 0) a ≤ 2 * C := by
  simpa only [_root_.pow_zero, div_eq_mul_inv, inv_one, mul_one] using
    edist_le_of_edist_le_geometric_two_of_tendsto C hu ha 0

end EdistLeGeometricTwo

section LeGeometric

variable [PseudoMetricSpace α] {r C : ℝ} {f : ℕ → α}

section
variable (hr : r < 1) (hu : ∀ n, dist (f n) (f (n + 1)) ≤ C * r ^ n)
include hr hu

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then `f` is a Cauchy sequence. -/
theorem aux_hasSum_of_le_geometric : HasSum (fun n : ℕ ↦ C * r ^ n) (C / (1 - r)) := by
  rcases sign_cases_of_C_mul_pow_nonneg fun n ↦ dist_nonneg.trans (hu n) with (rfl | ⟨_, r₀⟩)
  · simp [hasSum_zero]
  · refine HasSum.mul_left C ?_
    simpa using hasSum_geometric_of_lt_one r₀ hr

variable (r C)

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then `f` is a Cauchy sequence.
Note that this lemma does not assume `0 ≤ C` or `0 ≤ r`. -/
theorem cauchySeq_of_le_geometric : CauchySeq f :=
  cauchySeq_of_dist_le_of_summable _ hu ⟨_, aux_hasSum_of_le_geometric hr hu⟩

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then the distance from
`f n` to the limit of `f` is bounded above by `C * r^n / (1 - r)`. -/
theorem dist_le_of_le_geometric_of_tendsto₀ {a : α} (ha : Tendsto f atTop (𝓝 a)) :
    dist (f 0) a ≤ C / (1 - r) :=
  (aux_hasSum_of_le_geometric hr hu).tsum_eq ▸
    dist_le_tsum_of_dist_le_of_tendsto₀ _ hu ⟨_, aux_hasSum_of_le_geometric hr hu⟩ ha

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then the distance from
`f 0` to the limit of `f` is bounded above by `C / (1 - r)`. -/
theorem dist_le_of_le_geometric_of_tendsto {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : ℕ) :
    dist (f n) a ≤ C * r ^ n / (1 - r) := by
  have := aux_hasSum_of_le_geometric hr hu
  convert dist_le_tsum_of_dist_le_of_tendsto _ hu ⟨_, this⟩ ha n
  simp only [pow_add, mul_left_comm C, mul_div_right_comm]
  rw [mul_comm]
  exact (this.mul_left _).tsum_eq.symm

end

variable (hu₂ : ∀ n, dist (f n) (f (n + 1)) ≤ C / 2 / 2 ^ n)
include hu₂

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then `f` is a Cauchy sequence. -/
theorem cauchySeq_of_le_geometric_two : CauchySeq f :=
  cauchySeq_of_dist_le_of_summable _ hu₂ <| ⟨_, hasSum_geometric_two' C⟩

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then the distance from
`f 0` to the limit of `f` is bounded above by `C`. -/
theorem dist_le_of_le_geometric_two_of_tendsto₀ {a : α} (ha : Tendsto f atTop (𝓝 a)) :
    dist (f 0) a ≤ C :=
  tsum_geometric_two' C ▸ dist_le_tsum_of_dist_le_of_tendsto₀ _ hu₂ (summable_geometric_two' C) ha

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then the distance from
`f n` to the limit of `f` is bounded above by `C / 2^n`. -/
theorem dist_le_of_le_geometric_two_of_tendsto {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : ℕ) :
    dist (f n) a ≤ C / 2 ^ n := by
  convert dist_le_tsum_of_dist_le_of_tendsto _ hu₂ (summable_geometric_two' C) ha n
  simp only [add_comm n, pow_add, ← div_div]
  symm
  exact ((hasSum_geometric_two' C).div_const _).tsum_eq

end LeGeometric

/-! ### Summability tests based on comparison with geometric series -/


/-- A series whose terms are bounded by the terms of a converging geometric series converges. -/
theorem summable_one_div_pow_of_le {m : ℝ} {f : ℕ → ℕ} (hm : 1 < m) (fi : ∀ i, i ≤ f i) :
    Summable fun i ↦ 1 / m ^ f i := by
  refine .of_nonneg_of_le (fun a ↦ by positivity) (fun a ↦ ?_)
      (summable_geometric_of_lt_one (one_div_nonneg.mpr (zero_le_one.trans hm.le))
        ((one_div_lt (zero_lt_one.trans hm) zero_lt_one).mpr (one_div_one.le.trans_lt hm)))
  rw [div_pow, one_pow]
  refine (one_div_le_one_div ?_ ?_).mpr (pow_right_mono₀ hm.le (fi a)) <;>
    exact pow_pos (zero_lt_one.trans hm) _

/-! ### Positive sequences with small sums on countable types -/


/-- For any positive `ε`, define on an encodable type a positive sequence with sum less than `ε` -/
def posSumOfEncodable {ε : ℝ} (hε : 0 < ε) (ι) [Encodable ι] :
    { ε' : ι → ℝ // (∀ i, 0 < ε' i) ∧ ∃ c, HasSum ε' c ∧ c ≤ ε } := by
  let f n := ε / 2 / 2 ^ n
  have hf : HasSum f ε := hasSum_geometric_two' _
  have f0 : ∀ n, 0 < f n := fun n ↦ div_pos (half_pos hε) (pow_pos zero_lt_two _)
  refine ⟨f ∘ Encodable.encode, fun i ↦ f0 _, ?_⟩
  rcases hf.summable.comp_injective (@Encodable.encode_injective ι _) with ⟨c, hg⟩
  refine ⟨c, hg, hasSum_le_inj _ (@Encodable.encode_injective ι _) ?_ ?_ hg hf⟩
  · intro i _
    exact le_of_lt (f0 _)
  · intro n
    exact le_rfl

theorem Set.Countable.exists_pos_hasSum_le {ι : Type*} {s : Set ι} (hs : s.Countable) {ε : ℝ}
    (hε : 0 < ε) : ∃ ε' : ι → ℝ, (∀ i, 0 < ε' i) ∧ ∃ c, HasSum (fun i : s ↦ ε' i) c ∧ c ≤ ε := by
  classical
  haveI := hs.toEncodable
  rcases posSumOfEncodable hε s with ⟨f, hf0, ⟨c, hfc, hcε⟩⟩
  refine ⟨fun i ↦ if h : i ∈ s then f ⟨i, h⟩ else 1, fun i ↦ ?_, ⟨c, ?_, hcε⟩⟩
  · conv_rhs => simp
    split_ifs
    exacts [hf0 _, zero_lt_one]
  · simpa only [Subtype.coe_prop, dif_pos, Subtype.coe_eta]

theorem Set.Countable.exists_pos_forall_sum_le {ι : Type*} {s : Set ι} (hs : s.Countable) {ε : ℝ}
    (hε : 0 < ε) : ∃ ε' : ι → ℝ,
    (∀ i, 0 < ε' i) ∧ ∀ t : Finset ι, ↑t ⊆ s → ∑ i ∈ t, ε' i ≤ ε := by
  classical
  rcases hs.exists_pos_hasSum_le hε with ⟨ε', hpos, c, hε'c, hcε⟩
  refine ⟨ε', hpos, fun t ht ↦ ?_⟩
  rw [← sum_subtype_of_mem _ ht]
  refine (sum_le_hasSum _ ?_ hε'c).trans hcε
  exact fun _ _ ↦ (hpos _).le

namespace NNReal

theorem exists_pos_sum_of_countable {ε : ℝ≥0} (hε : ε ≠ 0) (ι) [Countable ι] :
    ∃ ε' : ι → ℝ≥0, (∀ i, 0 < ε' i) ∧ ∃ c, HasSum ε' c ∧ c < ε := by
  cases nonempty_encodable ι
  obtain ⟨a, a0, aε⟩ := exists_between (pos_iff_ne_zero.2 hε)
  obtain ⟨ε', hε', c, hc, hcε⟩ := posSumOfEncodable a0 ι
  exact
    ⟨fun i ↦ ⟨ε' i, (hε' i).le⟩, fun i ↦ NNReal.coe_lt_coe.1 <| hε' i,
      ⟨c, hasSum_le (fun i ↦ (hε' i).le) hasSum_zero hc⟩, NNReal.hasSum_coe.1 hc,
      aε.trans_le' <| NNReal.coe_le_coe.1 hcε⟩

end NNReal

namespace ENNReal

theorem exists_pos_sum_of_countable {ε : ℝ≥0∞} (hε : ε ≠ 0) (ι) [Countable ι] :
    ∃ ε' : ι → ℝ≥0, (∀ i, 0 < ε' i) ∧ (∑' i, (ε' i : ℝ≥0∞)) < ε := by
  rcases exists_between (pos_iff_ne_zero.2 hε) with ⟨r, h0r, hrε⟩
  rcases lt_iff_exists_coe.1 hrε with ⟨x, rfl, _⟩
  rcases NNReal.exists_pos_sum_of_countable (coe_pos.1 h0r).ne' ι with ⟨ε', hp, c, hc, hcr⟩
  exact ⟨ε', hp, (ENNReal.tsum_coe_eq hc).symm ▸ lt_trans (coe_lt_coe.2 hcr) hrε⟩

theorem exists_pos_sum_of_countable' {ε : ℝ≥0∞} (hε : ε ≠ 0) (ι) [Countable ι] :
    ∃ ε' : ι → ℝ≥0∞, (∀ i, 0 < ε' i) ∧ ∑' i, ε' i < ε :=
  let ⟨δ, δpos, hδ⟩ := exists_pos_sum_of_countable hε ι
  ⟨fun i ↦ δ i, fun i ↦ ENNReal.coe_pos.2 (δpos i), hδ⟩

theorem exists_pos_tsum_mul_lt_of_countable {ε : ℝ≥0∞} (hε : ε ≠ 0) {ι} [Countable ι] (w : ι → ℝ≥0∞)
    (hw : ∀ i, w i ≠ ∞) : ∃ δ : ι → ℝ≥0, (∀ i, 0 < δ i) ∧ (∑' i, (w i * δ i : ℝ≥0∞)) < ε := by
  lift w to ι → ℝ≥0 using hw
  rcases exists_pos_sum_of_countable hε ι with ⟨δ', Hpos, Hsum⟩
  have : ∀ i, 0 < max 1 (w i) := fun i ↦ zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨fun i ↦ δ' i / max 1 (w i), fun i ↦ div_pos (Hpos _) (this i), ?_⟩
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun i ↦ ?_) Hsum
  rw [coe_div (this i).ne']
  refine mul_le_of_le_div' ?_
  grw [← le_max_right]

end ENNReal

/-!
### Factorial
-/


theorem factorial_tendsto_atTop : Tendsto Nat.factorial atTop atTop :=
  tendsto_atTop_atTop_of_monotone (fun _ _ ↦ Nat.factorial_le) fun n ↦ ⟨n, n.self_le_factorial⟩

theorem tendsto_factorial_div_pow_self_atTop :
    Tendsto (fun n ↦ n ! / (n : ℝ) ^ n : ℕ → ℝ) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_const_div_atTop_nhds_zero_nat 1)
    (Eventually.of_forall fun n ↦
      div_nonneg (mod_cast n.factorial_pos.le)
        (pow_nonneg (mod_cast n.zero_le) _))
    (by
      refine (eventually_gt_atTop 0).mono fun n hn ↦ ?_
      rcases Nat.exists_eq_succ_of_ne_zero hn.ne.symm with ⟨k, rfl⟩
      rw [factorial_eq_prod_range_add_one, pow_eq_prod_const, div_eq_mul_inv, ← inv_eq_one_div,
        prod_natCast, Nat.cast_succ, ← Finset.prod_inv_distrib, ← prod_mul_distrib,
        Finset.prod_range_succ']
      simp only [one_mul, Nat.cast_add, zero_add, Nat.cast_one]
      refine
            mul_le_of_le_one_left (inv_nonneg.mpr <| mod_cast hn.le) (prod_le_one ?_ ?_) <;>
          intro x hx <;>
        rw [Finset.mem_range] at hx
      · positivity
      · refine (div_le_one <| mod_cast hn).mpr ?_
        norm_cast
        cutsat)

/-!
### Ceil and floor
-/


section

theorem tendsto_nat_floor_atTop {α : Type*}
    [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorSemiring α] :
    Tendsto (fun x : α ↦ ⌊x⌋₊) atTop atTop :=
  Nat.floor_mono.tendsto_atTop_atTop fun x ↦ ⟨max 0 (x + 1), by simp [Nat.le_floor_iff]⟩

lemma tendsto_nat_ceil_atTop {α : Type*}
    [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorSemiring α] :
    Tendsto (fun x : α ↦ ⌈x⌉₊) atTop atTop := by
  refine Nat.ceil_mono.tendsto_atTop_atTop (fun x ↦ ⟨x, ?_⟩)
  simp only [Nat.ceil_natCast, le_refl]

lemma tendsto_nat_floor_mul_atTop {α : Type _}
    [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] [FloorSemiring α]
    [Archimedean α] (a : α) (ha : 0 < a) : Tendsto (fun (x : ℕ) => ⌊a * x⌋₊) atTop atTop :=
  Tendsto.comp tendsto_nat_floor_atTop
    <| Tendsto.const_mul_atTop ha tendsto_natCast_atTop_atTop

variable {R : Type*} [TopologicalSpace R] [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [OrderTopology R] [FloorRing R]

theorem tendsto_nat_floor_mul_div_atTop {a : R} (ha : 0 ≤ a) :
    Tendsto (fun x ↦ (⌊a * x⌋₊ : R) / x) atTop (𝓝 a) := by
  have A : Tendsto (fun x : R ↦ a - x⁻¹) atTop (𝓝 (a - 0)) :=
    tendsto_const_nhds.sub tendsto_inv_atTop_zero
  rw [sub_zero] at A
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' A tendsto_const_nhds
  · refine eventually_atTop.2 ⟨1, fun x hx ↦ ?_⟩
    simp only [le_div_iff₀ (zero_lt_one.trans_le hx), _root_.sub_mul,
      inv_mul_cancel₀ (zero_lt_one.trans_le hx).ne']
    have := Nat.lt_floor_add_one (a * x)
    linarith
  · refine eventually_atTop.2 ⟨1, fun x hx ↦ ?_⟩
    rw [div_le_iff₀ (zero_lt_one.trans_le hx)]
    simp [Nat.floor_le (mul_nonneg ha (zero_le_one.trans hx))]

theorem tendsto_nat_floor_div_atTop : Tendsto (fun x ↦ (⌊x⌋₊ : R) / x) atTop (𝓝 1) := by
  simpa using tendsto_nat_floor_mul_div_atTop (zero_le_one' R)

theorem tendsto_nat_ceil_mul_div_atTop {a : R} (ha : 0 ≤ a) :
    Tendsto (fun x ↦ (⌈a * x⌉₊ : R) / x) atTop (𝓝 a) := by
  have A : Tendsto (fun x : R ↦ a + x⁻¹) atTop (𝓝 (a + 0)) :=
    tendsto_const_nhds.add tendsto_inv_atTop_zero
  rw [add_zero] at A
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds A
  · refine eventually_atTop.2 ⟨1, fun x hx ↦ ?_⟩
    rw [le_div_iff₀ (zero_lt_one.trans_le hx)]
    exact Nat.le_ceil _
  · refine eventually_atTop.2 ⟨1, fun x hx ↦ ?_⟩
    simp [div_le_iff₀ (zero_lt_one.trans_le hx), inv_mul_cancel₀ (zero_lt_one.trans_le hx).ne',
      (Nat.ceil_lt_add_one (mul_nonneg ha (zero_le_one.trans hx))).le, add_mul]

theorem tendsto_nat_ceil_div_atTop : Tendsto (fun x ↦ (⌈x⌉₊ : R) / x) atTop (𝓝 1) := by
  simpa using tendsto_nat_ceil_mul_div_atTop (zero_le_one' R)

lemma Nat.tendsto_div_const_atTop {n : ℕ} (hn : n ≠ 0) : Tendsto (· / n) atTop atTop := by
  rw [Tendsto, map_div_atTop_eq_nat n hn.bot_lt]

end

@[deprecated (since := "2025-10-27")]
alias tendsto_inverse_atTop_nhds_zero_nat := tendsto_inv_atTop_nhds_zero_nat

@[deprecated (since := "2025-10-27")]
alias NNReal.tendsto_inverse_atTop_nhds_zero_nat := tendsto_inv_atTop_nhds_zero_nat

@[deprecated (since := "2025-10-27")]
alias NNReal.tendsto_const_div_atTop_nhds_zero_nat := tendsto_const_div_atTop_nhds_zero_nat

@[deprecated (since := "2025-10-27")]
alias NNReal.tendsto_algebraMap_inverse_atTop_nhds_zero_nat :=
  tendsto_algebraMap_inv_atTop_nhds_zero_nat

@[deprecated (since := "2025-10-27")]
alias tendsto_algebraMap_inverse_atTop_nhds_zero_nat :=
  tendsto_algebraMap_inv_atTop_nhds_zero_nat

@[deprecated (since := "2025-10-27")]
protected alias Nat.tendsto_pow_atTop_atTop_of_one_lt := tendsto_pow_atTop_atTop_of_one_lt
