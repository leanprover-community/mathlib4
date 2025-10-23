/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Frédéric Dupuis, Heather Macbeth
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Existence of minimizers (Hilbert projection theorem)

This file shows the existence of minimizers (also known as the Hilbert projection theorem).
This is the key tool that is used to define `Submodule.orthogonalProjection` in
`Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`.
-/

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
local notation "absR" => @abs ℝ _ _

open Topology RCLike Real Filter InnerProductSpace

/-- **Existence of minimizers**, aka the **Hilbert projection theorem**.

Let `u` be a point in a real inner product space, and let `K` be a nonempty complete convex subset.
Then there exists a (unique) `v` in `K` that minimizes the distance `‖u - v‖` to `u`. -/
theorem exists_norm_eq_iInf_of_complete_convex {K : Set F} (ne : K.Nonempty) (h₁ : IsComplete K)
    (h₂ : Convex ℝ K) : ∀ u : F, ∃ v ∈ K, ‖u - v‖ = ⨅ w : K, ‖u - w‖ := fun u => by
  let δ := ⨅ w : K, ‖u - w‖
  letI : Nonempty K := ne.to_subtype
  have zero_le_δ : 0 ≤ δ := le_ciInf fun _ => norm_nonneg _
  have δ_le : ∀ w : K, δ ≤ ‖u - w‖ := ciInf_le ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩
  have δ_le' : ∀ w ∈ K, δ ≤ ‖u - w‖ := fun w hw => δ_le ⟨w, hw⟩
  -- Step 1: since `δ` is the infimum, can find a sequence `w : ℕ → K` in `K`
  -- such that `‖u - w n‖ < δ + 1 / (n + 1)` (which implies `‖u - w n‖ --> δ`);
  -- maybe this should be a separate lemma
  have exists_seq : ∃ w : ℕ → K, ∀ n, ‖u - w n‖ < δ + 1 / (n + 1) := by
    have hδ : ∀ n : ℕ, δ < δ + 1 / (n + 1) := fun n =>
      lt_add_of_le_of_pos le_rfl Nat.one_div_pos_of_nat
    have h := fun n => exists_lt_of_ciInf_lt (hδ n)
    let w : ℕ → K := fun n => Classical.choose (h n)
    exact ⟨w, fun n => Classical.choose_spec (h n)⟩
  rcases exists_seq with ⟨w, hw⟩
  have norm_tendsto : Tendsto (fun n => ‖u - w n‖) atTop (𝓝 δ) := by
    have h : Tendsto (fun _ : ℕ => δ) atTop (𝓝 δ) := tendsto_const_nhds
    have h' : Tendsto (fun n : ℕ => δ + 1 / (n + 1)) atTop (𝓝 δ) := by
      convert h.add tendsto_one_div_add_atTop_nhds_zero_nat
      simp only [add_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h h' (fun x => δ_le _) fun x => le_of_lt (hw _)
  -- Step 2: Prove that the sequence `w : ℕ → K` is a Cauchy sequence
  have seq_is_cauchy : CauchySeq fun n => (w n : F) := by
    rw [cauchySeq_iff_le_tendsto_0]
    -- splits into three goals
    let b := fun n : ℕ => 8 * δ * (1 / (n + 1)) + 4 * (1 / (n + 1)) * (1 / (n + 1))
    use fun n => √(b n)
    constructor
    -- first goal :  `∀ (n : ℕ), 0 ≤ √(b n)`
    · intro n
      exact sqrt_nonneg _
    constructor
    -- second goal : `∀ (n m N : ℕ), N ≤ n → N ≤ m → dist ↑(w n) ↑(w m) ≤ √(b N)`
    · intro p q N hp hq
      let wp := (w p : F)
      let wq := (w q : F)
      let a := u - wq
      let b := u - wp
      let half := 1 / (2 : ℝ)
      let div := 1 / ((N : ℝ) + 1)
      have :
        4 * ‖u - half • (wq + wp)‖ * ‖u - half • (wq + wp)‖ + ‖wp - wq‖ * ‖wp - wq‖ =
          2 * (‖a‖ * ‖a‖ + ‖b‖ * ‖b‖) :=
        calc
          4 * ‖u - half • (wq + wp)‖ * ‖u - half • (wq + wp)‖ + ‖wp - wq‖ * ‖wp - wq‖ =
              2 * ‖u - half • (wq + wp)‖ * (2 * ‖u - half • (wq + wp)‖) + ‖wp - wq‖ * ‖wp - wq‖ :=
            by ring
          _ =
              absR 2 * ‖u - half • (wq + wp)‖ * (absR 2 * ‖u - half • (wq + wp)‖) +
                ‖wp - wq‖ * ‖wp - wq‖ := by
            rw [abs_of_nonneg]
            exact zero_le_two
          _ =
              ‖(2 : ℝ) • (u - half • (wq + wp))‖ * ‖(2 : ℝ) • (u - half • (wq + wp))‖ +
                ‖wp - wq‖ * ‖wp - wq‖ := by simp [norm_smul]
          _ = ‖a + b‖ * ‖a + b‖ + ‖a - b‖ * ‖a - b‖ := by
            rw [smul_sub, smul_smul, mul_one_div_cancel (_root_.two_ne_zero : (2 : ℝ) ≠ 0), ←
              one_add_one_eq_two, add_smul]
            simp only [one_smul]
            have eq₁ : wp - wq = a - b := (sub_sub_sub_cancel_left _ _ _).symm
            have eq₂ : u + u - (wq + wp) = a + b := by
              change u + u - (wq + wp) = u - wq + (u - wp)
              abel
            rw [eq₁, eq₂]
          _ = 2 * (‖a‖ * ‖a‖ + ‖b‖ * ‖b‖) := parallelogram_law_with_norm ℝ _ _
      have eq : δ ≤ ‖u - half • (wq + wp)‖ := by
        rw [smul_add]
        apply δ_le'
        apply h₂
        repeat' exact Subtype.mem _
        repeat' exact le_of_lt one_half_pos
        exact add_halves 1
      have eq₂ : ‖a‖ ≤ δ + div := by grw [hw, Nat.one_div_le_one_div hq]
      have eq₂' : ‖b‖ ≤ δ + div := by grw [hw, Nat.one_div_le_one_div hp]
      rw [dist_eq_norm]
      apply nonneg_le_nonneg_of_sq_le_sq
      · exact sqrt_nonneg _
      rw [mul_self_sqrt]
      · calc
        ‖wp - wq‖ * ‖wp - wq‖ =
            2 * (‖a‖ * ‖a‖ + ‖b‖ * ‖b‖) - 4 * ‖u - half • (wq + wp)‖ * ‖u - half • (wq + wp)‖ := by
          simp [← this]
        _ ≤ 2 * (‖a‖ * ‖a‖ + ‖b‖ * ‖b‖) - 4 * δ * δ := by gcongr
        _ ≤ 2 * ((δ + div) * (δ + div) + (δ + div) * (δ + div)) - 4 * δ * δ := by gcongr
        _ = 8 * δ * div + 4 * div * div := by ring
      positivity
    -- third goal : `Tendsto (fun (n : ℕ) => √(b n)) atTop (𝓝 0)`
    suffices Tendsto (fun x ↦ √(8 * δ * x + 4 * x * x) : ℝ → ℝ) (𝓝 0) (𝓝 0)
      from this.comp tendsto_one_div_add_atTop_nhds_zero_nat
    exact Continuous.tendsto' (by fun_prop) _ _ (by simp)
  -- Step 3: By completeness of `K`, let `w : ℕ → K` converge to some `v : K`.
  -- Prove that it satisfies all requirements.
  rcases cauchySeq_tendsto_of_isComplete h₁ (fun n => Subtype.mem _) seq_is_cauchy with
    ⟨v, hv, w_tendsto⟩
  use v
  use hv
  have h_cont : Continuous fun v => ‖u - v‖ :=
    Continuous.comp continuous_norm (Continuous.sub continuous_const continuous_id)
  have : Tendsto (fun n => ‖u - w n‖) atTop (𝓝 ‖u - v‖) := by
    convert Tendsto.comp h_cont.continuousAt w_tendsto
  exact tendsto_nhds_unique this norm_tendsto

/-- Characterization of minimizers for the projection on a convex set in a real inner product
space. -/
theorem norm_eq_iInf_iff_real_inner_le_zero {K : Set F} (h : Convex ℝ K) {u : F} {v : F}
    (hv : v ∈ K) : (‖u - v‖ = ⨅ w : K, ‖u - w‖) ↔ ∀ w ∈ K, ⟪u - v, w - v⟫_ℝ ≤ 0 := by
  letI : Nonempty K := ⟨⟨v, hv⟩⟩
  constructor
  · intro eq w hw
    let δ := ⨅ w : K, ‖u - w‖
    let p := ⟪u - v, w - v⟫_ℝ
    let q := ‖w - v‖ ^ 2
    have δ_le (w : K) : δ ≤ ‖u - w‖ := ciInf_le ⟨0, fun _ ⟨_, h⟩ => h ▸ norm_nonneg _⟩ _
    have δ_le' (w) (hw : w ∈ K) : δ ≤ ‖u - w‖ := δ_le ⟨w, hw⟩
    have (θ : ℝ) (hθ₁ : 0 < θ) (hθ₂ : θ ≤ 1) : 2 * p ≤ θ * q := by
      have : ‖u - v‖ ^ 2 ≤ ‖u - v‖ ^ 2 - 2 * θ * ⟪u - v, w - v⟫_ℝ + θ * θ * ‖w - v‖ ^ 2 :=
        calc ‖u - v‖ ^ 2
          _ ≤ ‖u - (θ • w + (1 - θ) • v)‖ ^ 2 := by
            simp only [sq]; apply mul_self_le_mul_self (norm_nonneg _)
            rw [eq]; apply δ_le'
            apply h hw hv
            exacts [le_of_lt hθ₁, sub_nonneg.2 hθ₂, add_sub_cancel _ _]
          _ = ‖u - v - θ • (w - v)‖ ^ 2 := by
            have : u - (θ • w + (1 - θ) • v) = u - v - θ • (w - v) := by
              rw [smul_sub, sub_smul, one_smul]
              simp only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, neg_add_rev]
            rw [this]
          _ = ‖u - v‖ ^ 2 - 2 * θ * ⟪u - v, w - v⟫_ℝ + θ * θ * ‖w - v‖ ^ 2 := by
            rw [@norm_sub_sq ℝ, inner_smul_right, norm_smul]
            simp only [sq]
            change
              ‖u - v‖ * ‖u - v‖ - 2 * (θ * ⟪u - v, w - v⟫_ℝ) +
                absR θ * ‖w - v‖ * (absR θ * ‖w - v‖) =
              ‖u - v‖ * ‖u - v‖ - 2 * θ * ⟪u - v, w - v⟫_ℝ + θ * θ * (‖w - v‖ * ‖w - v‖)
            rw [abs_of_pos hθ₁]; ring
      have eq₁ :
        ‖u - v‖ ^ 2 - 2 * θ * ⟪u - v, w - v⟫_ℝ + θ * θ * ‖w - v‖ ^ 2 =
          ‖u - v‖ ^ 2 + (θ * θ * ‖w - v‖ ^ 2 - 2 * θ * ⟪u - v, w - v⟫_ℝ) := by
        abel
      rw [eq₁, le_add_iff_nonneg_right] at this
      have eq₂ :
        θ * θ * ‖w - v‖ ^ 2 - 2 * θ * ⟪u - v, w - v⟫_ℝ =
          θ * (θ * ‖w - v‖ ^ 2 - 2 * ⟪u - v, w - v⟫_ℝ) := by ring
      rw [eq₂] at this
      exact le_of_sub_nonneg (nonneg_of_mul_nonneg_right this hθ₁)
    by_cases hq : q = 0
    · rw [hq] at this
      have : p ≤ 0 := by
        have := this (1 : ℝ) (by simp) (by simp)
        linarith
      exact this
    · have q_pos : 0 < q := lt_of_le_of_ne (sq_nonneg _) fun h ↦ hq h.symm
      by_contra hp
      rw [not_le] at hp
      let θ := min (1 : ℝ) (p / q)
      have eq₁ : θ * q ≤ p :=
        calc
          θ * q ≤ p / q * q := mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
          _ = p := div_mul_cancel₀ _ hq
      have : 2 * p ≤ p :=
        calc
          2 * p ≤ θ * q := by
            exact this θ (lt_min (by simp) (div_pos hp q_pos)) (by simp [θ])
          _ ≤ p := eq₁
      linarith
  · intro h
    apply le_antisymm
    · apply le_ciInf
      intro w
      apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
      have := h w w.2
      calc
        ‖u - v‖ * ‖u - v‖ ≤ ‖u - v‖ * ‖u - v‖ - 2 * ⟪u - v, w - v⟫_ℝ := by linarith
        _ ≤ ‖u - v‖ ^ 2 - 2 * ⟪u - v, w - v⟫_ℝ + ‖w - v‖ ^ 2 := by
          rw [sq]
          refine le_add_of_nonneg_right ?_
          exact sq_nonneg _
        _ = ‖u - v - (w - v)‖ ^ 2 := (@norm_sub_sq ℝ _ _ _ _ _ _).symm
        _ = ‖u - w‖ * ‖u - w‖ := by
          have : u - v - (w - v) = u - w := by abel
          rw [this, sq]
    · change ⨅ w : K, ‖u - w‖ ≤ (fun w : K => ‖u - w‖) ⟨v, hv⟩
      apply ciInf_le
      use 0
      rintro y ⟨z, rfl⟩
      exact norm_nonneg _

namespace Submodule

variable (K : Submodule 𝕜 E)

/-- Existence of projections on complete subspaces.
Let `u` be a point in an inner product space, and let `K` be a nonempty complete subspace.
Then there exists a (unique) `v` in `K` that minimizes the distance `‖u - v‖` to `u`.
This point `v` is usually called the orthogonal projection of `u` onto `K`.
-/
theorem exists_norm_eq_iInf_of_complete_subspace (h : IsComplete (↑K : Set E)) :
    ∀ u : E, ∃ v ∈ K, ‖u - v‖ = ⨅ w : (K : Set E), ‖u - w‖ := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal 𝕜 E
  letI : Module ℝ E := RestrictScalars.module ℝ 𝕜 E
  let K' : Submodule ℝ E := Submodule.restrictScalars ℝ K
  exact exists_norm_eq_iInf_of_complete_convex ⟨0, K'.zero_mem⟩ h K'.convex

/-- Characterization of minimizers in the projection on a subspace, in the real case.
Let `u` be a point in a real inner product space, and let `K` be a nonempty subspace.
Then point `v` minimizes the distance `‖u - v‖` over points in `K` if and only if
for all `w ∈ K`, `⟪u - v, w⟫ = 0` (i.e., `u - v` is orthogonal to the subspace `K`).
This is superseded by `norm_eq_iInf_iff_inner_eq_zero` that gives the same conclusion over
any `RCLike` field.
-/
theorem norm_eq_iInf_iff_real_inner_eq_zero (K : Submodule ℝ F) {u : F} {v : F} (hv : v ∈ K) :
    (‖u - v‖ = ⨅ w : (↑K : Set F), ‖u - w‖) ↔ ∀ w ∈ K, ⟪u - v, w⟫_ℝ = 0 :=
  Iff.intro
    (by
      intro h
      have h : ∀ w ∈ K, ⟪u - v, w - v⟫_ℝ ≤ 0 := by
        rwa [norm_eq_iInf_iff_real_inner_le_zero] at h
        exacts [K.convex, hv]
      intro w hw
      have le : ⟪u - v, w⟫_ℝ ≤ 0 := by
        let w' := w + v
        have : w' ∈ K := Submodule.add_mem _ hw hv
        have h₁ := h w' this
        have h₂ : w' - v = w := by
          simp only [w', add_neg_cancel_right, sub_eq_add_neg]
        rw [h₂] at h₁
        exact h₁
      have ge : ⟪u - v, w⟫_ℝ ≥ 0 := by
        let w'' := -w + v
        have : w'' ∈ K := Submodule.add_mem _ (Submodule.neg_mem _ hw) hv
        have h₁ := h w'' this
        have h₂ : w'' - v = -w := by
          simp only [w'', add_neg_cancel_right, sub_eq_add_neg]
        rw [h₂, inner_neg_right] at h₁
        linarith
      exact le_antisymm le ge)
    (by
      intro h
      have : ∀ w ∈ K, ⟪u - v, w - v⟫_ℝ ≤ 0 := by
        intro w hw
        let w' := w - v
        have : w' ∈ K := Submodule.sub_mem _ hw hv
        have h₁ := h w' this
        exact le_of_eq h₁
      rwa [norm_eq_iInf_iff_real_inner_le_zero]
      exacts [Submodule.convex _, hv])

/-- Characterization of minimizers in the projection on a subspace.
Let `u` be a point in an inner product space, and let `K` be a nonempty subspace.
Then point `v` minimizes the distance `‖u - v‖` over points in `K` if and only if
for all `w ∈ K`, `⟪u - v, w⟫ = 0` (i.e., `u - v` is orthogonal to the subspace `K`)
-/
theorem norm_eq_iInf_iff_inner_eq_zero {u : E} {v : E} (hv : v ∈ K) :
    (‖u - v‖ = ⨅ w : K, ‖u - w‖) ↔ ∀ w ∈ K, ⟪u - v, w⟫ = 0 := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal 𝕜 E
  letI : Module ℝ E := RestrictScalars.module ℝ 𝕜 E
  let K' : Submodule ℝ E := K.restrictScalars ℝ
  constructor
  · intro H
    have A : ∀ w ∈ K, re ⟪u - v, w⟫ = 0 := (K'.norm_eq_iInf_iff_real_inner_eq_zero hv).1 H
    intro w hw
    apply RCLike.ext
    · simp [A w hw]
    · symm
      calc
        im (0 : 𝕜) = 0 := im.map_zero
        _ = re ⟪u - v, (-I : 𝕜) • w⟫ := (A _ (K.smul_mem (-I) hw)).symm
        _ = re (-I * ⟪u - v, w⟫) := by rw [inner_smul_right]
        _ = im ⟪u - v, w⟫ := by simp
  · intro H
    have : ∀ w ∈ K', ⟪u - v, w⟫_ℝ = 0 := by
      intro w hw
      rw [real_inner_eq_re_inner, H w hw]
      exact zero_re
    exact (K'.norm_eq_iInf_iff_real_inner_eq_zero hv).2 this

end Submodule
