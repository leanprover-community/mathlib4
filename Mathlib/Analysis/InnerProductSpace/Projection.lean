/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Frédéric Dupuis, Heather Macbeth
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.NormedSpace.IsROrC
import Mathlib.Data.IsROrC.Lemmas
import Mathlib.Algebra.DirectSum.Decomposition

#align_import analysis.inner_product_space.projection from "leanprover-community/mathlib"@"0b7c740e25651db0ba63648fbae9f9d6f941e31b"

/-!
# The orthogonal projection

Given a nonempty complete subspace `K` of an inner product space `E`, this file constructs
`orthogonalProjection K : E →L[𝕜] K`, the orthogonal projection of `E` onto `K`.  This map
satisfies: for any point `u` in `E`, the point `v = orthogonalProjection K u` in `K` minimizes the
distance `‖u - v‖` to `u`.

Also a linear isometry equivalence `reflection K : E ≃ₗᵢ[𝕜] E` is constructed, by choosing, for
each `u : E`, the point `reflection K u` to satisfy
`u + (reflection K u) = 2 • orthogonalProjection K u`.

Basic API for `orthogonalProjection` and `reflection` is developed.

Next, the orthogonal projection is used to prove a series of more subtle lemmas about the
orthogonal complement of complete subspaces of `E` (the orthogonal complement itself was
defined in `Analysis.InnerProductSpace.Orthogonal`); the lemma
`Submodule.sup_orthogonal_of_completeSpace`, stating that for a complete subspace `K` of `E` we have
`K ⊔ Kᗮ = ⊤`, is a typical example.

## References

The orthogonal projection construction is adapted from
* [Clément & Martin, *The Lax-Milgram Theorem. A detailed proof to be formalized in Coq*]
* [Clément & Martin, *A Coq formal proof of the Lax–Milgram theorem*]

The Coq code is available at the following address: <http://www.lri.fr/~sboldo/elfic/index.html>
-/


noncomputable section

open IsROrC Real Filter

open LinearMap (ker range)

open BigOperators Topology

variable {𝕜 E F : Type*} [IsROrC 𝕜]

variable [NormedAddCommGroup E] [NormedAddCommGroup F]

variable [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ F]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

-- mathport name: exprabsR
local notation "absR" => Abs.abs

/-! ### Orthogonal projection in inner product spaces -/


-- FIXME this monolithic proof causes a deterministic timeout with `-T50000`
-- It should be broken in a sequence of more manageable pieces,
-- perhaps with individual statements for the three steps below.
/-- Existence of minimizers
Let `u` be a point in a real inner product space, and let `K` be a nonempty complete convex subset.
Then there exists a (unique) `v` in `K` that minimizes the distance `‖u - v‖` to `u`.
 -/
theorem exists_norm_eq_iInf_of_complete_convex {K : Set F} (ne : K.Nonempty) (h₁ : IsComplete K)
    (h₂ : Convex ℝ K) : ∀ u : F, ∃ v ∈ K, ‖u - v‖ = ⨅ w : K, ‖u - w‖ := fun u => by
  let δ := ⨅ w : K, ‖u - w‖
  -- ⊢ ∃ v, v ∈ K ∧ ‖u - v‖ = ⨅ (w : ↑K), ‖u - ↑w‖
  letI : Nonempty K := ne.to_subtype
  -- ⊢ ∃ v, v ∈ K ∧ ‖u - v‖ = ⨅ (w : ↑K), ‖u - ↑w‖
  have zero_le_δ : 0 ≤ δ := le_ciInf fun _ => norm_nonneg _
  -- ⊢ ∃ v, v ∈ K ∧ ‖u - v‖ = ⨅ (w : ↑K), ‖u - ↑w‖
  have δ_le : ∀ w : K, δ ≤ ‖u - w‖ := ciInf_le ⟨0, Set.forall_range_iff.2 fun _ => norm_nonneg _⟩
  -- ⊢ ∃ v, v ∈ K ∧ ‖u - v‖ = ⨅ (w : ↑K), ‖u - ↑w‖
  have δ_le' : ∀ w ∈ K, δ ≤ ‖u - w‖ := fun w hw => δ_le ⟨w, hw⟩
  -- ⊢ ∃ v, v ∈ K ∧ ‖u - v‖ = ⨅ (w : ↑K), ‖u - ↑w‖
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
  -- ⊢ ∃ v, v ∈ K ∧ ‖u - v‖ = ⨅ (w : ↑K), ‖u - ↑w‖
  have norm_tendsto : Tendsto (fun n => ‖u - w n‖) atTop (nhds δ) := by
    have h : Tendsto (fun _ : ℕ => δ) atTop (nhds δ) := tendsto_const_nhds
    have h' : Tendsto (fun n : ℕ => δ + 1 / (n + 1)) atTop (nhds δ) := by
      convert h.add tendsto_one_div_add_atTop_nhds_0_nat
      simp only [add_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h h' (fun x => δ_le _) fun x => le_of_lt (hw _)
  -- Step 2: Prove that the sequence `w : ℕ → K` is a Cauchy sequence
  have seq_is_cauchy : CauchySeq fun n => (w n : F) := by
    rw [cauchySeq_iff_le_tendsto_0]
    -- splits into three goals
    let b := fun n : ℕ => 8 * δ * (1 / (n + 1)) + 4 * (1 / (n + 1)) * (1 / (n + 1))
    use fun n => sqrt (b n)
    constructor
    -- first goal :  `∀ (n : ℕ), 0 ≤ sqrt (b n)`
    intro n
    exact sqrt_nonneg _
    constructor
    -- second goal : `∀ (n m N : ℕ), N ≤ n → N ≤ m → dist ↑(w n) ↑(w m) ≤ sqrt (b N)`
    intro p q N hp hq
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
            absR (2 : ℝ) * ‖u - half • (wq + wp)‖ * (absR (2 : ℝ) * ‖u - half • (wq + wp)‖) +
              ‖wp - wq‖ * ‖wp - wq‖ := by
          rw [_root_.abs_of_nonneg]
          exact zero_le_two
        _ =
            ‖(2 : ℝ) • (u - half • (wq + wp))‖ * ‖(2 : ℝ) • (u - half • (wq + wp))‖ +
              ‖wp - wq‖ * ‖wp - wq‖ :=
          by simp [norm_smul]
        _ = ‖a + b‖ * ‖a + b‖ + ‖a - b‖ * ‖a - b‖ := by
          rw [smul_sub, smul_smul, mul_one_div_cancel (_root_.two_ne_zero : (2 : ℝ) ≠ 0), ←
            one_add_one_eq_two, add_smul]
          simp only [one_smul]
          have eq₁ : wp - wq = a - b := (sub_sub_sub_cancel_left _ _ _).symm
          have eq₂ : u + u - (wq + wp) = a + b
          show u + u - (wq + wp) = u - wq + (u - wp)
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
    have eq₁ : 4 * δ * δ ≤ 4 * ‖u - half • (wq + wp)‖ * ‖u - half • (wq + wp)‖ := by
      simp_rw [mul_assoc]
      gcongr
    have eq₂ : ‖a‖ ≤ δ + div :=
        le_trans (le_of_lt <| hw q) (add_le_add_left (Nat.one_div_le_one_div hq) _)
    have eq₂' : ‖b‖ ≤ δ + div :=
        le_trans (le_of_lt <| hw p) (add_le_add_left (Nat.one_div_le_one_div hp) _)
    rw [dist_eq_norm]
    apply nonneg_le_nonneg_of_sq_le_sq
    · exact sqrt_nonneg _
    rw [mul_self_sqrt]
    calc
      ‖wp - wq‖ * ‖wp - wq‖ =
          2 * (‖a‖ * ‖a‖ + ‖b‖ * ‖b‖) - 4 * ‖u - half • (wq + wp)‖ * ‖u - half • (wq + wp)‖ := by
        simp [← this]
      _ ≤ 2 * (‖a‖ * ‖a‖ + ‖b‖ * ‖b‖) - 4 * δ * δ := by gcongr
      _ ≤ 2 * ((δ + div) * (δ + div) + (δ + div) * (δ + div)) - 4 * δ * δ := by gcongr
      _ = 8 * δ * div + 4 * div * div := by ring
    positivity
    -- third goal : `Tendsto (fun (n : ℕ) => sqrt (b n)) atTop (𝓝 0)`
    apply Tendsto.comp (f := b) (g := sqrt)
    · have : Tendsto sqrt (nhds 0) (nhds (sqrt 0)) := continuous_sqrt.continuousAt
      convert this
      exact sqrt_zero.symm
    have eq₁ : Tendsto (fun n : ℕ => 8 * δ * (1 / (n + 1))) atTop (nhds (0 : ℝ)) := by
      convert(@tendsto_const_nhds _ _ _ (8 * δ) _).mul tendsto_one_div_add_atTop_nhds_0_nat
      simp only [mul_zero]
    have : Tendsto (fun n : ℕ => (4 : ℝ) * (1 / (n + 1))) atTop (nhds (0 : ℝ)) := by
      convert(@tendsto_const_nhds _ _ _ (4 : ℝ) _).mul tendsto_one_div_add_atTop_nhds_0_nat
      simp only [mul_zero]
    have eq₂ :
        Tendsto (fun n : ℕ => (4 : ℝ) * (1 / (n + 1)) * (1 / (n + 1))) atTop (nhds (0 : ℝ)) := by
      convert this.mul tendsto_one_div_add_atTop_nhds_0_nat
      simp only [mul_zero]
    convert eq₁.add eq₂
    simp only [add_zero]
  -- Step 3: By completeness of `K`, let `w : ℕ → K` converge to some `v : K`.
  -- Prove that it satisfies all requirements.
  rcases cauchySeq_tendsto_of_isComplete h₁ (fun n => Subtype.mem _) seq_is_cauchy with
    ⟨v, hv, w_tendsto⟩
  use v
  -- ⊢ v ∈ K ∧ ‖u - v‖ = ⨅ (w : ↑K), ‖u - ↑w‖
  use hv
  -- ⊢ ‖u - v‖ = ⨅ (w : ↑K), ‖u - ↑w‖
  have h_cont : Continuous fun v => ‖u - v‖ :=
    Continuous.comp continuous_norm (Continuous.sub continuous_const continuous_id)
  have : Tendsto (fun n => ‖u - w n‖) atTop (nhds ‖u - v‖)
  -- ⊢ Tendsto (fun n => ‖u - ↑(w n)‖) atTop (𝓝 ‖u - v‖)
  convert Tendsto.comp h_cont.continuousAt w_tendsto
  -- ⊢ ‖u - v‖ = ⨅ (w : ↑K), ‖u - ↑w‖
  exact tendsto_nhds_unique this norm_tendsto
  -- 🎉 no goals
#align exists_norm_eq_infi_of_complete_convex exists_norm_eq_iInf_of_complete_convex

/-- Characterization of minimizers for the projection on a convex set in a real inner product
space. -/
theorem norm_eq_iInf_iff_real_inner_le_zero {K : Set F} (h : Convex ℝ K) {u : F} {v : F}
    (hv : v ∈ K) : (‖u - v‖ = ⨅ w : K, ‖u - w‖) ↔ ∀ w ∈ K, ⟪u - v, w - v⟫_ℝ ≤ 0 := by
  letI : Nonempty K := ⟨⟨v, hv⟩⟩
  -- ⊢ ‖u - v‖ = ⨅ (w : ↑K), ‖u - ↑w‖ ↔ ∀ (w : F), w ∈ K → inner (u - v) (w - v) ≤ 0
  constructor
  -- ⊢ ‖u - v‖ = ⨅ (w : ↑K), ‖u - ↑w‖ → ∀ (w : F), w ∈ K → inner (u - v) (w - v) ≤ 0
  · intro eq w hw
    -- ⊢ inner (u - v) (w - v) ≤ 0
    let δ := ⨅ w : K, ‖u - w‖
    -- ⊢ inner (u - v) (w - v) ≤ 0
    let p := ⟪u - v, w - v⟫_ℝ
    -- ⊢ inner (u - v) (w - v) ≤ 0
    let q := ‖w - v‖ ^ 2
    -- ⊢ inner (u - v) (w - v) ≤ 0
    have δ_le (w : K) : δ ≤ ‖u - w‖ := ciInf_le ⟨0, fun _ ⟨_, h⟩ => h ▸ norm_nonneg _⟩ _
    -- ⊢ inner (u - v) (w - v) ≤ 0
    have δ_le' (w) (hw : w ∈ K) : δ ≤ ‖u - w‖ := δ_le ⟨w, hw⟩
    -- ⊢ inner (u - v) (w - v) ≤ 0
    have (θ : ℝ) (hθ₁ : 0 < θ) (hθ₂ : θ ≤ 1) : 2 * p ≤ θ * q := by
      have : ‖u - v‖ ^ 2 ≤ ‖u - v‖ ^ 2 - 2 * θ * ⟪u - v, w - v⟫_ℝ + θ * θ * ‖w - v‖ ^ 2 :=
        calc ‖u - v‖ ^ 2
          _ ≤ ‖u - (θ • w + (1 - θ) • v)‖ ^ 2 := by
            simp only [sq]; apply mul_self_le_mul_self (norm_nonneg _)
            rw [eq]; apply δ_le'
            apply h hw hv
            exacts [le_of_lt hθ₁, sub_nonneg.2 hθ₂, add_sub_cancel'_right _ _]
          _ = ‖u - v - θ • (w - v)‖ ^ 2 := by
            have : u - (θ • w + (1 - θ) • v) = u - v - θ • (w - v) := by
              rw [smul_sub, sub_smul, one_smul]
              simp only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, neg_add_rev]
            rw [this]
          _ = ‖u - v‖ ^ 2 - 2 * θ * inner (u - v) (w - v) + θ * θ * ‖w - v‖ ^ 2 := by
            rw [@norm_sub_sq ℝ, inner_smul_right, norm_smul]
            simp only [sq]
            show
              ‖u - v‖ * ‖u - v‖ - 2 * (θ * inner (u - v) (w - v)) +
                absR θ * ‖w - v‖ * (absR θ * ‖w - v‖) =
              ‖u - v‖ * ‖u - v‖ - 2 * θ * inner (u - v) (w - v) + θ * θ * (‖w - v‖ * ‖w - v‖)
            rw [abs_of_pos hθ₁]; ring
      have eq₁ :
        ‖u - v‖ ^ 2 - 2 * θ * inner (u - v) (w - v) + θ * θ * ‖w - v‖ ^ 2 =
          ‖u - v‖ ^ 2 + (θ * θ * ‖w - v‖ ^ 2 - 2 * θ * inner (u - v) (w - v)) := by
        abel
      rw [eq₁, le_add_iff_nonneg_right] at this
      have eq₂ :
        θ * θ * ‖w - v‖ ^ 2 - 2 * θ * inner (u - v) (w - v) =
          θ * (θ * ‖w - v‖ ^ 2 - 2 * inner (u - v) (w - v))
      ring
      rw [eq₂] at this
      have := le_of_sub_nonneg (nonneg_of_mul_nonneg_right this hθ₁)
      exact this
    by_cases hq : q = 0
    -- ⊢ inner (u - v) (w - v) ≤ 0
    · rw [hq] at this
      -- ⊢ inner (u - v) (w - v) ≤ 0
      have : p ≤ 0 := by
        have := this (1 : ℝ) (by norm_num) (by norm_num)
        linarith
      exact this
      -- 🎉 no goals
    · have q_pos : 0 < q := lt_of_le_of_ne (sq_nonneg _) fun h ↦ hq h.symm
      -- ⊢ inner (u - v) (w - v) ≤ 0
      by_contra hp
      -- ⊢ False
      rw [not_le] at hp
      -- ⊢ False
      let θ := min (1 : ℝ) (p / q)
      -- ⊢ False
      have eq₁ : θ * q ≤ p :=
        calc
          θ * q ≤ p / q * q := mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
          _ = p := div_mul_cancel _ hq
      have : 2 * p ≤ p :=
        calc
          2 * p ≤ θ * q := by
            refine' this θ (lt_min (by norm_num) (div_pos hp q_pos)) (by norm_num)
          _ ≤ p := eq₁
      linarith
      -- 🎉 no goals
  · intro h
    -- ⊢ ‖u - v‖ = ⨅ (w : ↑K), ‖u - ↑w‖
    apply le_antisymm
    -- ⊢ ‖u - v‖ ≤ ⨅ (w : ↑K), ‖u - ↑w‖
    · apply le_ciInf
      -- ⊢ ∀ (x : ↑K), ‖u - v‖ ≤ ‖u - ↑x‖
      intro w
      -- ⊢ ‖u - v‖ ≤ ‖u - ↑w‖
      apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
      -- ⊢ ‖u - v‖ * ‖u - v‖ ≤ ‖u - ↑w‖ * ‖u - ↑w‖
      have := h w w.2
      -- ⊢ ‖u - v‖ * ‖u - v‖ ≤ ‖u - ↑w‖ * ‖u - ↑w‖
      calc
        ‖u - v‖ * ‖u - v‖ ≤ ‖u - v‖ * ‖u - v‖ - 2 * inner (u - v) ((w : F) - v) := by linarith
        _ ≤ ‖u - v‖ ^ 2 - 2 * inner (u - v) ((w : F) - v) + ‖(w : F) - v‖ ^ 2 := by
          rw [sq]
          refine' le_add_of_nonneg_right _
          exact sq_nonneg _
        _ = ‖u - v - (w - v)‖ ^ 2 := (@norm_sub_sq ℝ _ _ _ _ _ _).symm
        _ = ‖u - w‖ * ‖u - w‖ := by
          have : u - v - (w - v) = u - w := by abel
          rw [this, sq]
    · show ⨅ w : K, ‖u - w‖ ≤ (fun w : K => ‖u - w‖) ⟨v, hv⟩
      -- ⊢ ⨅ (w : ↑K), ‖u - ↑w‖ ≤ (fun w => ‖u - ↑w‖) { val := v, property := hv }
      apply ciInf_le
      -- ⊢ BddBelow (Set.range fun w => ‖u - ↑w‖)
      use 0
      -- ⊢ 0 ∈ lowerBounds (Set.range fun w => ‖u - ↑w‖)
      rintro y ⟨z, rfl⟩
      -- ⊢ 0 ≤ (fun w => ‖u - ↑w‖) z
      exact norm_nonneg _
      -- 🎉 no goals
#align norm_eq_infi_iff_real_inner_le_zero norm_eq_iInf_iff_real_inner_le_zero

variable (K : Submodule 𝕜 E)

/-- Existence of projections on complete subspaces.
Let `u` be a point in an inner product space, and let `K` be a nonempty complete subspace.
Then there exists a (unique) `v` in `K` that minimizes the distance `‖u - v‖` to `u`.
This point `v` is usually called the orthogonal projection of `u` onto `K`.
-/
theorem exists_norm_eq_iInf_of_complete_subspace (h : IsComplete (↑K : Set E)) :
    ∀ u : E, ∃ v ∈ K, ‖u - v‖ = ⨅ w : (K : Set E), ‖u - w‖ := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.isROrCToReal 𝕜 E
  -- ⊢ ∀ (u : E), ∃ v, v ∈ K ∧ ‖u - v‖ = ⨅ (w : ↑↑K), ‖u - ↑w‖
  letI : Module ℝ E := RestrictScalars.module ℝ 𝕜 E
  -- ⊢ ∀ (u : E), ∃ v, v ∈ K ∧ ‖u - v‖ = ⨅ (w : ↑↑K), ‖u - ↑w‖
  let K' : Submodule ℝ E := Submodule.restrictScalars ℝ K
  -- ⊢ ∀ (u : E), ∃ v, v ∈ K ∧ ‖u - v‖ = ⨅ (w : ↑↑K), ‖u - ↑w‖
  exact exists_norm_eq_iInf_of_complete_convex ⟨0, K'.zero_mem⟩ h K'.convex
  -- 🎉 no goals
#align exists_norm_eq_infi_of_complete_subspace exists_norm_eq_iInf_of_complete_subspace

/-- Characterization of minimizers in the projection on a subspace, in the real case.
Let `u` be a point in a real inner product space, and let `K` be a nonempty subspace.
Then point `v` minimizes the distance `‖u - v‖` over points in `K` if and only if
for all `w ∈ K`, `⟪u - v, w⟫ = 0` (i.e., `u - v` is orthogonal to the subspace `K`).
This is superceded by `norm_eq_iInf_iff_inner_eq_zero` that gives the same conclusion over
any `IsROrC` field.
-/
theorem norm_eq_iInf_iff_real_inner_eq_zero (K : Submodule ℝ F) {u : F} {v : F} (hv : v ∈ K) :
    (‖u - v‖ = ⨅ w : (↑K : Set F), ‖u - w‖) ↔ ∀ w ∈ K, ⟪u - v, w⟫_ℝ = 0 :=
  Iff.intro
    (by
      intro h
      -- ⊢ ∀ (w : F), w ∈ K → inner (u - v) w = 0
      have h : ∀ w ∈ K, ⟪u - v, w - v⟫_ℝ ≤ 0 := by
        rwa [norm_eq_iInf_iff_real_inner_le_zero] at h
        exacts [K.convex, hv]
      intro w hw
      -- ⊢ inner (u - v) w = 0
      have le : ⟪u - v, w⟫_ℝ ≤ 0
      -- ⊢ inner (u - v) w ≤ 0
      let w' := w + v
      -- ⊢ inner (u - v) w ≤ 0
      have : w' ∈ K := Submodule.add_mem _ hw hv
      -- ⊢ inner (u - v) w ≤ 0
      have h₁ := h w' this
      -- ⊢ inner (u - v) w ≤ 0
      have h₂ : w' - v = w
      simp only [add_neg_cancel_right, sub_eq_add_neg]
      -- ⊢ inner (u - v) w ≤ 0
      rw [h₂] at h₁
      -- ⊢ inner (u - v) w ≤ 0
      exact h₁
      -- ⊢ inner (u - v) w = 0
      have ge : ⟪u - v, w⟫_ℝ ≥ 0
      -- ⊢ inner (u - v) w ≥ 0
      let w'' := -w + v
      -- ⊢ inner (u - v) w ≥ 0
      have : w'' ∈ K := Submodule.add_mem _ (Submodule.neg_mem _ hw) hv
      -- ⊢ inner (u - v) w ≥ 0
      have h₁ := h w'' this
      -- ⊢ inner (u - v) w ≥ 0
      have h₂ : w'' - v = -w
      simp only [neg_inj, add_neg_cancel_right, sub_eq_add_neg]
      -- ⊢ inner (u - v) w ≥ 0
      rw [h₂, inner_neg_right] at h₁
      -- ⊢ inner (u - v) w ≥ 0
      linarith
      -- ⊢ inner (u - v) w = 0
      exact le_antisymm le ge)
      -- 🎉 no goals
    (by
      intro h
      -- ⊢ ‖u - v‖ = ⨅ (w : ↑↑K), ‖u - ↑w‖
      have : ∀ w ∈ K, ⟪u - v, w - v⟫_ℝ ≤ 0
      -- ⊢ ∀ (w : F), w ∈ K → inner (u - v) (w - v) ≤ 0
      intro w hw
      -- ⊢ inner (u - v) (w - v) ≤ 0
      let w' := w - v
      -- ⊢ inner (u - v) (w - v) ≤ 0
      have : w' ∈ K := Submodule.sub_mem _ hw hv
      -- ⊢ inner (u - v) (w - v) ≤ 0
      have h₁ := h w' this
      -- ⊢ inner (u - v) (w - v) ≤ 0
      exact le_of_eq h₁
      -- ⊢ ‖u - v‖ = ⨅ (w : ↑↑K), ‖u - ↑w‖
      rwa [norm_eq_iInf_iff_real_inner_le_zero]
      -- ⊢ Convex ℝ ↑K
      exacts [Submodule.convex _, hv])
      -- 🎉 no goals
#align norm_eq_infi_iff_real_inner_eq_zero norm_eq_iInf_iff_real_inner_eq_zero

/-- Characterization of minimizers in the projection on a subspace.
Let `u` be a point in an inner product space, and let `K` be a nonempty subspace.
Then point `v` minimizes the distance `‖u - v‖` over points in `K` if and only if
for all `w ∈ K`, `⟪u - v, w⟫ = 0` (i.e., `u - v` is orthogonal to the subspace `K`)
-/
theorem norm_eq_iInf_iff_inner_eq_zero {u : E} {v : E} (hv : v ∈ K) :
    (‖u - v‖ = ⨅ w : K, ‖u - w‖) ↔ ∀ w ∈ K, ⟪u - v, w⟫ = 0 := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.isROrCToReal 𝕜 E
  -- ⊢ ‖u - v‖ = ⨅ (w : { x // x ∈ K }), ‖u - ↑w‖ ↔ ∀ (w : E), w ∈ K → inner (u - v …
  letI : Module ℝ E := RestrictScalars.module ℝ 𝕜 E
  -- ⊢ ‖u - v‖ = ⨅ (w : { x // x ∈ K }), ‖u - ↑w‖ ↔ ∀ (w : E), w ∈ K → inner (u - v …
  let K' : Submodule ℝ E := K.restrictScalars ℝ
  -- ⊢ ‖u - v‖ = ⨅ (w : { x // x ∈ K }), ‖u - ↑w‖ ↔ ∀ (w : E), w ∈ K → inner (u - v …
  constructor
  -- ⊢ ‖u - v‖ = ⨅ (w : { x // x ∈ K }), ‖u - ↑w‖ → ∀ (w : E), w ∈ K → inner (u - v …
  · intro H
    -- ⊢ ∀ (w : E), w ∈ K → inner (u - v) w = 0
    have A : ∀ w ∈ K, re ⟪u - v, w⟫ = 0 := (norm_eq_iInf_iff_real_inner_eq_zero K' hv).1 H
    -- ⊢ ∀ (w : E), w ∈ K → inner (u - v) w = 0
    intro w hw
    -- ⊢ inner (u - v) w = 0
    apply ext
    -- ⊢ ↑re (inner (u - v) w) = ↑re 0
    · simp [A w hw]
      -- 🎉 no goals
    · symm
      -- ⊢ ↑im 0 = ↑im (inner (u - v) w)
      calc
        im (0 : 𝕜) = 0 := im.map_zero
        _ = re ⟪u - v, (-I : 𝕜) • w⟫ := (A _ (K.smul_mem (-I) hw)).symm
        _ = re (-I * ⟪u - v, w⟫) := by rw [inner_smul_right]
        _ = im ⟪u - v, w⟫ := by simp
  · intro H
    -- ⊢ ‖u - v‖ = ⨅ (w : { x // x ∈ K }), ‖u - ↑w‖
    have : ∀ w ∈ K', ⟪u - v, w⟫_ℝ = 0 := by
      intro w hw
      rw [real_inner_eq_re_inner, H w hw]
      exact zero_re'
    exact (norm_eq_iInf_iff_real_inner_eq_zero K' hv).2 this
    -- 🎉 no goals
#align norm_eq_infi_iff_inner_eq_zero norm_eq_iInf_iff_inner_eq_zero

/-- A subspace `K : Submodule 𝕜 E` has an orthogonal projection if evey vector `v : E` admits an
orthogonal projection to `K`. -/
class HasOrthogonalProjection (K : Submodule 𝕜 E) : Prop where
  exists_orthogonal (v : E) : ∃ w ∈ K, v - w ∈ Kᗮ

instance (priority := 100) HasOrthogonalProjection.ofCompleteSpace [CompleteSpace K] :
    HasOrthogonalProjection K where
  exists_orthogonal v := by
    rcases exists_norm_eq_iInf_of_complete_subspace K (completeSpace_coe_iff_isComplete.mp ‹_›) v
      with ⟨w, hwK, hw⟩
    refine ⟨w, hwK, (K.mem_orthogonal' _).2 ?_⟩
    -- ⊢ ∀ (u : E), u ∈ K → inner (v - w) u = 0
    rwa [← norm_eq_iInf_iff_inner_eq_zero K hwK]
    -- 🎉 no goals

instance [HasOrthogonalProjection K] : HasOrthogonalProjection Kᗮ where
  exists_orthogonal v := by
    rcases HasOrthogonalProjection.exists_orthogonal (K := K) v with ⟨w, hwK, hw⟩
    -- ⊢ ∃ w, w ∈ Kᗮ ∧ v - w ∈ Kᗮᗮ
    refine ⟨_, hw, ?_⟩
    -- ⊢ v - (v - w) ∈ Kᗮᗮ
    rw [sub_sub_cancel]
    -- ⊢ w ∈ Kᗮᗮ
    exact K.le_orthogonal_orthogonal hwK
    -- 🎉 no goals

instance HasOrthogonalProjection.map_linearIsometryEquiv [HasOrthogonalProjection K]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E') :
    HasOrthogonalProjection (K.map (f.toLinearEquiv : E →ₗ[𝕜] E')) where
  exists_orthogonal v := by
    rcases HasOrthogonalProjection.exists_orthogonal (K := K) (f.symm v) with ⟨w, hwK, hw⟩
    -- ⊢ ∃ w, w ∈ Submodule.map (↑f.toLinearEquiv) K ∧ v - w ∈ (Submodule.map (↑f.toL …
    refine ⟨f w, Submodule.mem_map_of_mem hwK, Set.ball_image_iff.2 fun u hu ↦ ?_⟩
    -- ⊢ inner (↑↑f.toLinearEquiv u) (v - ↑f w) = 0
    erw [← f.symm.inner_map_map, f.symm_apply_apply, map_sub, f.symm_apply_apply, hw u hu]
    -- 🎉 no goals

instance HasOrthogonalProjection.map_linearIsometryEquiv' [HasOrthogonalProjection K]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E') :
    HasOrthogonalProjection (K.map f.toLinearIsometry) :=
  HasOrthogonalProjection.map_linearIsometryEquiv K f

instance : HasOrthogonalProjection (⊤ : Submodule 𝕜 E) := ⟨fun v ↦ ⟨v, trivial, by simp⟩⟩
                                                                                   -- 🎉 no goals

section orthogonalProjection

variable [HasOrthogonalProjection K]

/-- The orthogonal projection onto a complete subspace, as an
unbundled function.  This definition is only intended for use in
setting up the bundled version `orthogonalProjection` and should not
be used once that is defined. -/
def orthogonalProjectionFn (v : E) :=
  (HasOrthogonalProjection.exists_orthogonal (K := K) v).choose
#align orthogonal_projection_fn orthogonalProjectionFn

variable {K}

/-- The unbundled orthogonal projection is in the given subspace.
This lemma is only intended for use in setting up the bundled version
and should not be used once that is defined. -/
theorem orthogonalProjectionFn_mem (v : E) : orthogonalProjectionFn K v ∈ K :=
  (HasOrthogonalProjection.exists_orthogonal (K := K) v).choose_spec.left
#align orthogonal_projection_fn_mem orthogonalProjectionFn_mem

/-- The characterization of the unbundled orthogonal projection.  This
lemma is only intended for use in setting up the bundled version
and should not be used once that is defined. -/
theorem orthogonalProjectionFn_inner_eq_zero (v : E) :
    ∀ w ∈ K, ⟪v - orthogonalProjectionFn K v, w⟫ = 0 :=
  (K.mem_orthogonal' _).1 (HasOrthogonalProjection.exists_orthogonal (K := K) v).choose_spec.right
#align orthogonal_projection_fn_inner_eq_zero orthogonalProjectionFn_inner_eq_zero

/-- The unbundled orthogonal projection is the unique point in `K`
with the orthogonality property.  This lemma is only intended for use
in setting up the bundled version and should not be used once that is
defined. -/
theorem eq_orthogonalProjectionFn_of_mem_of_inner_eq_zero {u v : E} (hvm : v ∈ K)
    (hvo : ∀ w ∈ K, ⟪u - v, w⟫ = 0) : orthogonalProjectionFn K u = v := by
  rw [← sub_eq_zero, ← @inner_self_eq_zero 𝕜]
  -- ⊢ inner (orthogonalProjectionFn K u - v) (orthogonalProjectionFn K u - v) = 0
  have hvs : orthogonalProjectionFn K u - v ∈ K :=
    Submodule.sub_mem K (orthogonalProjectionFn_mem u) hvm
  have huo : ⟪u - orthogonalProjectionFn K u, orthogonalProjectionFn K u - v⟫ = 0 :=
    orthogonalProjectionFn_inner_eq_zero u _ hvs
  have huv : ⟪u - v, orthogonalProjectionFn K u - v⟫ = 0 := hvo _ hvs
  -- ⊢ inner (orthogonalProjectionFn K u - v) (orthogonalProjectionFn K u - v) = 0
  have houv : ⟪u - v - (u - orthogonalProjectionFn K u), orthogonalProjectionFn K u - v⟫ = 0 := by
    rw [inner_sub_left, huo, huv, sub_zero]
  rwa [sub_sub_sub_cancel_left] at houv
  -- 🎉 no goals
#align eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero eq_orthogonalProjectionFn_of_mem_of_inner_eq_zero

variable (K)

theorem orthogonalProjectionFn_norm_sq (v : E) :
    ‖v‖ * ‖v‖ =
      ‖v - orthogonalProjectionFn K v‖ * ‖v - orthogonalProjectionFn K v‖ +
        ‖orthogonalProjectionFn K v‖ * ‖orthogonalProjectionFn K v‖ := by
  set p := orthogonalProjectionFn K v
  -- ⊢ ‖v‖ * ‖v‖ = ‖v - p‖ * ‖v - p‖ + ‖p‖ * ‖p‖
  have h' : ⟪v - p, p⟫ = 0 :=
    orthogonalProjectionFn_inner_eq_zero _ _ (orthogonalProjectionFn_mem v)
  convert norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (v - p) p h' using 2 <;> simp
  -- ⊢ ‖v‖ = ‖v - p + p‖
                                                                                       -- 🎉 no goals
                                                                                       -- 🎉 no goals
#align orthogonal_projection_fn_norm_sq orthogonalProjectionFn_norm_sq

/-- The orthogonal projection onto a complete subspace. -/
def orthogonalProjection : E →L[𝕜] K :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨orthogonalProjectionFn K v, orthogonalProjectionFn_mem v⟩
      map_add' := fun x y => by
        have hm : orthogonalProjectionFn K x + orthogonalProjectionFn K y ∈ K :=
          Submodule.add_mem K (orthogonalProjectionFn_mem x) (orthogonalProjectionFn_mem y)
        have ho :
          ∀ w ∈ K, ⟪x + y - (orthogonalProjectionFn K x + orthogonalProjectionFn K y), w⟫ = 0 := by
          intro w hw
          rw [add_sub_add_comm, inner_add_left, orthogonalProjectionFn_inner_eq_zero _ w hw,
            orthogonalProjectionFn_inner_eq_zero _ w hw, add_zero]
        ext
        -- ⊢ ↑((fun v => { val := orthogonalProjectionFn K v, property := (_ : orthogonal …
        simp [eq_orthogonalProjectionFn_of_mem_of_inner_eq_zero hm ho]
        -- 🎉 no goals
      map_smul' := fun c x => by
        have hm : c • orthogonalProjectionFn K x ∈ K :=
          Submodule.smul_mem K _ (orthogonalProjectionFn_mem x)
        have ho : ∀ w ∈ K, ⟪c • x - c • orthogonalProjectionFn K x, w⟫ = 0 := by
          intro w hw
          rw [← smul_sub, inner_smul_left, orthogonalProjectionFn_inner_eq_zero _ w hw,
            mul_zero]
        ext
        -- ⊢ ↑(AddHom.toFun { toFun := fun v => { val := orthogonalProjectionFn K v, prop …
        simp [eq_orthogonalProjectionFn_of_mem_of_inner_eq_zero hm ho] }
        -- 🎉 no goals
    1 fun x => by
    simp only [one_mul, LinearMap.coe_mk]
    -- ⊢ ‖↑{ toFun := fun v => { val := orthogonalProjectionFn K v, property := (_ :  …
    refine' le_of_pow_le_pow 2 (norm_nonneg _) (by norm_num) _
    -- ⊢ ‖↑{ toFun := fun v => { val := orthogonalProjectionFn K v, property := (_ :  …
    change ‖orthogonalProjectionFn K x‖ ^ 2 ≤ ‖x‖ ^ 2
    -- ⊢ ‖orthogonalProjectionFn K x‖ ^ 2 ≤ ‖x‖ ^ 2
    nlinarith [orthogonalProjectionFn_norm_sq K x]
    -- 🎉 no goals
#align orthogonal_projection orthogonalProjection

variable {K}

@[simp]
theorem orthogonalProjectionFn_eq (v : E) :
    orthogonalProjectionFn K v = (orthogonalProjection K v : E) :=
  rfl
#align orthogonal_projection_fn_eq orthogonalProjectionFn_eq

/-- The characterization of the orthogonal projection.  -/
@[simp]
theorem orthogonalProjection_inner_eq_zero (v : E) :
    ∀ w ∈ K, ⟪v - orthogonalProjection K v, w⟫ = 0 :=
  orthogonalProjectionFn_inner_eq_zero v
#align orthogonal_projection_inner_eq_zero orthogonalProjection_inner_eq_zero

/-- The difference of `v` from its orthogonal projection onto `K` is in `Kᗮ`.  -/
@[simp]
theorem sub_orthogonalProjection_mem_orthogonal (v : E) : v - orthogonalProjection K v ∈ Kᗮ := by
  intro w hw
  -- ⊢ inner w (v - ↑(↑(orthogonalProjection K) v)) = 0
  rw [inner_eq_zero_symm]
  -- ⊢ inner (v - ↑(↑(orthogonalProjection K) v)) w = 0
  exact orthogonalProjection_inner_eq_zero _ _ hw
  -- 🎉 no goals
#align sub_orthogonal_projection_mem_orthogonal sub_orthogonalProjection_mem_orthogonal

/-- The orthogonal projection is the unique point in `K` with the
orthogonality property. -/
theorem eq_orthogonalProjection_of_mem_of_inner_eq_zero {u v : E} (hvm : v ∈ K)
    (hvo : ∀ w ∈ K, ⟪u - v, w⟫ = 0) : (orthogonalProjection K u : E) = v :=
  eq_orthogonalProjectionFn_of_mem_of_inner_eq_zero hvm hvo
#align eq_orthogonal_projection_of_mem_of_inner_eq_zero eq_orthogonalProjection_of_mem_of_inner_eq_zero

/-- A point in `K` with the orthogonality property (here characterized in terms of `Kᗮ`) must be the
orthogonal projection. -/
theorem eq_orthogonalProjection_of_mem_orthogonal [HasOrthogonalProjection K] {u v : E} (hv : v ∈ K)
    (hvo : u - v ∈ Kᗮ) : (orthogonalProjection K u : E) = v :=
  eq_orthogonalProjectionFn_of_mem_of_inner_eq_zero hv <| (Submodule.mem_orthogonal' _ _).1 hvo
#align eq_orthogonal_projection_of_mem_orthogonal eq_orthogonalProjection_of_mem_orthogonal

/-- A point in `K` with the orthogonality property (here characterized in terms of `Kᗮ`) must be the
orthogonal projection. -/
theorem eq_orthogonalProjection_of_mem_orthogonal' [HasOrthogonalProjection K] {u v z : E}
    (hv : v ∈ K) (hz : z ∈ Kᗮ) (hu : u = v + z) : (orthogonalProjection K u : E) = v :=
  eq_orthogonalProjection_of_mem_orthogonal hv (by simpa [hu] )
                                                   -- 🎉 no goals
#align eq_orthogonal_projection_of_mem_orthogonal' eq_orthogonalProjection_of_mem_orthogonal'

@[simp]
theorem orthogonalProjection_orthogonal_val [HasOrthogonalProjection K] (u : E) :
    (orthogonalProjection Kᗮ u : E) = u - orthogonalProjection K u :=
  eq_orthogonalProjection_of_mem_orthogonal' (sub_orthogonalProjection_mem_orthogonal _)
    (K.le_orthogonal_orthogonal (orthogonalProjection K u).2) <| by simp
                                                                    -- 🎉 no goals

theorem orthogonalProjection_orthogonal [HasOrthogonalProjection K] (u : E) :
    orthogonalProjection Kᗮ u =
      ⟨u - orthogonalProjection K u, sub_orthogonalProjection_mem_orthogonal _⟩ :=
  Subtype.eq <| orthogonalProjection_orthogonal_val _

/-- The orthogonal projection of `y` on `U` minimizes the distance `‖y - x‖` for `x ∈ U`. -/
theorem orthogonalProjection_minimal {U : Submodule 𝕜 E} [HasOrthogonalProjection U] (y : E) :
    ‖y - orthogonalProjection U y‖ = ⨅ x : U, ‖y - x‖ := by
  rw [norm_eq_iInf_iff_inner_eq_zero _ (Submodule.coe_mem _)]
  -- ⊢ ∀ (w : E), w ∈ U → inner (y - ↑(↑(orthogonalProjection U) y)) w = 0
  exact orthogonalProjection_inner_eq_zero _
  -- 🎉 no goals
#align orthogonal_projection_minimal orthogonalProjection_minimal

/-- The orthogonal projections onto equal subspaces are coerced back to the same point in `E`. -/
theorem eq_orthogonalProjection_of_eq_submodule {K' : Submodule 𝕜 E} [HasOrthogonalProjection K']
    (h : K = K') (u : E) : (orthogonalProjection K u : E) = (orthogonalProjection K' u : E) := by
  subst h; rfl
  -- ⊢ ↑(↑(orthogonalProjection K) u) = ↑(↑(orthogonalProjection K) u)
           -- 🎉 no goals
#align eq_orthogonal_projection_of_eq_submodule eq_orthogonalProjection_of_eq_submodule

/-- The orthogonal projection sends elements of `K` to themselves. -/
@[simp]
theorem orthogonalProjection_mem_subspace_eq_self (v : K) : orthogonalProjection K v = v := by
  ext
  -- ⊢ ↑(↑(orthogonalProjection K) ↑v) = ↑v
  apply eq_orthogonalProjection_of_mem_of_inner_eq_zero <;> simp
  -- ⊢ ↑v ∈ K
                                                            -- 🎉 no goals
                                                            -- 🎉 no goals
#align orthogonal_projection_mem_subspace_eq_self orthogonalProjection_mem_subspace_eq_self

/-- A point equals its orthogonal projection if and only if it lies in the subspace. -/
theorem orthogonalProjection_eq_self_iff {v : E} : (orthogonalProjection K v : E) = v ↔ v ∈ K := by
  refine' ⟨fun h => _, fun h => eq_orthogonalProjection_of_mem_of_inner_eq_zero h _⟩
  -- ⊢ v ∈ K
  · rw [← h]
    -- ⊢ ↑(↑(orthogonalProjection K) v) ∈ K
    simp
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
#align orthogonal_projection_eq_self_iff orthogonalProjection_eq_self_iff

theorem LinearIsometry.map_orthogonalProjection {E E' : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E →ₗᵢ[𝕜] E')
    (p : Submodule 𝕜 E) [HasOrthogonalProjection p] [HasOrthogonalProjection (p.map f.toLinearMap)]
    (x : E) : f (orthogonalProjection p x) = orthogonalProjection (p.map f.toLinearMap) (f x) := by
  refine' (eq_orthogonalProjection_of_mem_of_inner_eq_zero _ fun y hy => _).symm
  -- ⊢ ↑f ↑(↑(orthogonalProjection p) x) ∈ Submodule.map f.toLinearMap p
  refine' Submodule.apply_coe_mem_map _ _
  -- ⊢ inner (↑f x - ↑f ↑(↑(orthogonalProjection p) x)) y = 0
  rcases hy with ⟨x', hx', rfl : f x' = y⟩
  -- ⊢ inner (↑f x - ↑f ↑(↑(orthogonalProjection p) x)) (↑f x') = 0
  rw [← f.map_sub, f.inner_map_map, orthogonalProjection_inner_eq_zero x x' hx']
  -- 🎉 no goals
#align linear_isometry.map_orthogonal_projection LinearIsometry.map_orthogonalProjection

theorem LinearIsometry.map_orthogonalProjection' {E E' : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E →ₗᵢ[𝕜] E')
    (p : Submodule 𝕜 E) [HasOrthogonalProjection p] [HasOrthogonalProjection (p.map f)] (x : E) :
    f (orthogonalProjection p x) = orthogonalProjection (p.map f) (f x) :=
  have : HasOrthogonalProjection (p.map f.toLinearMap) := ‹_›
  f.map_orthogonalProjection p x
#align linear_isometry.map_orthogonal_projection' LinearIsometry.map_orthogonalProjection'

/-- Orthogonal projection onto the `Submodule.map` of a subspace. -/
theorem orthogonalProjection_map_apply {E E' : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E')
    (p : Submodule 𝕜 E) [HasOrthogonalProjection p] (x : E') :
    (orthogonalProjection (p.map (f.toLinearEquiv : E →ₗ[𝕜] E')) x : E') =
      f (orthogonalProjection p (f.symm x)) := by
  simpa only [f.coe_toLinearIsometry, f.apply_symm_apply] using
    (f.toLinearIsometry.map_orthogonalProjection' p (f.symm x)).symm
#align orthogonal_projection_map_apply orthogonalProjection_map_apply

/-- The orthogonal projection onto the trivial submodule is the zero map. -/
@[simp]
theorem orthogonalProjection_bot : orthogonalProjection (⊥ : Submodule 𝕜 E) = 0 := by ext
                                                                                      -- 🎉 no goals
#align orthogonal_projection_bot orthogonalProjection_bot

variable (K)

/-- The orthogonal projection has norm `≤ 1`. -/
theorem orthogonalProjection_norm_le : ‖orthogonalProjection K‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _
                                       -- 🎉 no goals
#align orthogonal_projection_norm_le orthogonalProjection_norm_le

variable (𝕜)

theorem smul_orthogonalProjection_singleton {v : E} (w : E) :
    ((‖v‖ ^ 2 : ℝ) : 𝕜) • (orthogonalProjection (𝕜 ∙ v) w : E) = ⟪v, w⟫ • v := by
  suffices ((orthogonalProjection (𝕜 ∙ v) (((‖v‖ : 𝕜) ^ 2) • w)) : E) = ⟪v, w⟫ • v by
    simpa using this
  apply eq_orthogonalProjection_of_mem_of_inner_eq_zero
  -- ⊢ inner v w • v ∈ Submodule.span 𝕜 {v}
  · rw [Submodule.mem_span_singleton]
    -- ⊢ ∃ a, a • v = inner v w • v
    use ⟪v, w⟫
    -- 🎉 no goals
  · rw [← Submodule.mem_orthogonal', Submodule.mem_orthogonal_singleton_iff_inner_left]
    -- ⊢ inner (↑‖v‖ ^ 2 • w - inner v w • v) v = 0
    simp [inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K, mul_comm]
    -- 🎉 no goals
#align smul_orthogonal_projection_singleton smul_orthogonalProjection_singleton

/-- Formula for orthogonal projection onto a single vector. -/
theorem orthogonalProjection_singleton {v : E} (w : E) :
    (orthogonalProjection (𝕜 ∙ v) w : E) = (⟪v, w⟫ / ((‖v‖ ^ 2 : ℝ) : 𝕜)) • v := by
  by_cases hv : v = 0
  -- ⊢ ↑(↑(orthogonalProjection (Submodule.span 𝕜 {v})) w) = (inner v w / ↑(‖v‖ ^ 2 …
  · rw [hv, eq_orthogonalProjection_of_eq_submodule (Submodule.span_zero_singleton 𝕜)]
    -- ⊢ ↑(↑(orthogonalProjection ⊥) w) = (inner 0 w / ↑(‖0‖ ^ 2)) • 0
    · simp
      -- 🎉 no goals
  have hv' : ‖v‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr hv)
  -- ⊢ ↑(↑(orthogonalProjection (Submodule.span 𝕜 {v})) w) = (inner v w / ↑(‖v‖ ^ 2 …
  have key :
    (((‖v‖ ^ 2 : ℝ) : 𝕜)⁻¹ * ((‖v‖ ^ 2 : ℝ) : 𝕜)) • ((orthogonalProjection (𝕜 ∙ v) w) : E) =
      (((‖v‖ ^ 2 : ℝ) : 𝕜)⁻¹ * ⟪v, w⟫) • v :=
    by simp [mul_smul, smul_orthogonalProjection_singleton 𝕜 w, -ofReal_pow]
  convert key using 1 <;> field_simp [hv']
  -- ⊢ ↑(↑(orthogonalProjection (Submodule.span 𝕜 {v})) w) = ((↑(‖v‖ ^ 2))⁻¹ * ↑(‖v …
                          -- 🎉 no goals
                          -- 🎉 no goals
#align orthogonal_projection_singleton orthogonalProjection_singleton

/-- Formula for orthogonal projection onto a single unit vector. -/
theorem orthogonalProjection_unit_singleton {v : E} (hv : ‖v‖ = 1) (w : E) :
    (orthogonalProjection (𝕜 ∙ v) w : E) = ⟪v, w⟫ • v := by
  rw [← smul_orthogonalProjection_singleton 𝕜 w]
  -- ⊢ ↑(↑(orthogonalProjection (Submodule.span 𝕜 {v})) w) = ↑(‖v‖ ^ 2) • ↑(↑(ortho …
  simp [hv]
  -- 🎉 no goals
#align orthogonal_projection_unit_singleton orthogonalProjection_unit_singleton

end orthogonalProjection

section reflection

variable [HasOrthogonalProjection K]

-- Porting note: `bit0` is deprecated.
/-- Auxiliary definition for `reflection`: the reflection as a linear equivalence. -/
def reflectionLinearEquiv : E ≃ₗ[𝕜] E :=
  LinearEquiv.ofInvolutive
    (2 • (K.subtype.comp (orthogonalProjection K).toLinearMap) - LinearMap.id) fun x => by
    simp [two_smul]
    -- 🎉 no goals
#align reflection_linear_equiv reflectionLinearEquivₓ

/-- Reflection in a complete subspace of an inner product space.  The word "reflection" is
sometimes understood to mean specifically reflection in a codimension-one subspace, and sometimes
more generally to cover operations such as reflection in a point.  The definition here, of
reflection in a subspace, is a more general sense of the word that includes both those common
cases. -/
def reflection : E ≃ₗᵢ[𝕜] E :=
  { reflectionLinearEquiv K with
    norm_map' := by
      intro x
      -- ⊢ ‖↑{ toLinearMap := ↑src✝, invFun := src✝.invFun, left_inv := (_ : Function.L …
      dsimp only
      -- ⊢ ‖↑{ toLinearMap := ↑(reflectionLinearEquiv K), invFun := (reflectionLinearEq …
      let w : K := orthogonalProjection K x
      -- ⊢ ‖↑{ toLinearMap := ↑(reflectionLinearEquiv K), invFun := (reflectionLinearEq …
      let v := x - w
      -- ⊢ ‖↑{ toLinearMap := ↑(reflectionLinearEquiv K), invFun := (reflectionLinearEq …
      have : ⟪v, w⟫ = 0 := orthogonalProjection_inner_eq_zero x w w.2
      -- ⊢ ‖↑{ toLinearMap := ↑(reflectionLinearEquiv K), invFun := (reflectionLinearEq …
      convert norm_sub_eq_norm_add this using 2
      -- ⊢ ↑{ toLinearMap := ↑(reflectionLinearEquiv K), invFun := (reflectionLinearEqu …
      · rw [LinearEquiv.coe_mk, reflectionLinearEquiv, LinearEquiv.toFun_eq_coe,
          LinearEquiv.coe_ofInvolutive, LinearMap.sub_apply, LinearMap.id_apply, two_smul,
          LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply,
          ContinuousLinearMap.coe_coe]
        dsimp
        -- ⊢ ↑(↑(orthogonalProjection K) x) + ↑(↑(orthogonalProjection K) x) - x = ↑(↑(or …
        abel
        -- 🎉 no goals
        -- 🎉 no goals
      · simp only [add_sub_cancel'_right, eq_self_iff_true] }
        -- 🎉 no goals
#align reflection reflection

variable {K}

/-- The result of reflecting. -/
theorem reflection_apply (p : E) : reflection K p = 2 • (orthogonalProjection K p : E) - p :=
  rfl
#align reflection_apply reflection_applyₓ

/-- Reflection is its own inverse. -/
@[simp]
theorem reflection_symm : (reflection K).symm = reflection K :=
  rfl
#align reflection_symm reflection_symm

/-- Reflection is its own inverse. -/
@[simp]
theorem reflection_inv : (reflection K)⁻¹ = reflection K :=
  rfl
#align reflection_inv reflection_inv

variable (K)

/-- Reflecting twice in the same subspace. -/
@[simp]
theorem reflection_reflection (p : E) : reflection K (reflection K p) = p :=
  (reflection K).left_inv p
#align reflection_reflection reflection_reflection

/-- Reflection is involutive. -/
theorem reflection_involutive : Function.Involutive (reflection K) :=
  reflection_reflection K
#align reflection_involutive reflection_involutive

/-- Reflection is involutive. -/
@[simp]
theorem reflection_trans_reflection :
    (reflection K).trans (reflection K) = LinearIsometryEquiv.refl 𝕜 E :=
  LinearIsometryEquiv.ext <| reflection_involutive K
#align reflection_trans_reflection reflection_trans_reflection

/-- Reflection is involutive. -/
@[simp]
theorem reflection_mul_reflection : reflection K * reflection K = 1 :=
  reflection_trans_reflection _
#align reflection_mul_reflection reflection_mul_reflection

theorem reflection_orthogonal_apply (v : E) : reflection Kᗮ v = -reflection K v := by
  simp [reflection_apply]; abel
  -- ⊢ 2 • v - 2 • ↑(↑(orthogonalProjection K) v) - v = v - 2 • ↑(↑(orthogonalProje …
                           -- 🎉 no goals
                           -- 🎉 no goals

theorem reflection_orthogonal : reflection Kᗮ = .trans (reflection K) (.neg _) := by
  ext; apply reflection_orthogonal_apply
  -- ⊢ ↑(reflection Kᗮ) x✝ = ↑(LinearIsometryEquiv.trans (reflection K) (LinearIsom …
       -- 🎉 no goals

variable {K}

theorem reflection_singleton_apply (u v : E) :
    reflection (𝕜 ∙ u) v = 2 • (⟪u, v⟫ / ((‖u‖ : 𝕜) ^ 2)) • u - v := by
  rw [reflection_apply, orthogonalProjection_singleton, ofReal_pow]
  -- 🎉 no goals

/-- A point is its own reflection if and only if it is in the subspace. -/
theorem reflection_eq_self_iff (x : E) : reflection K x = x ↔ x ∈ K := by
  rw [← orthogonalProjection_eq_self_iff, reflection_apply, sub_eq_iff_eq_add', ← two_smul 𝕜,
    two_smul ℕ, ← two_smul 𝕜]
  refine' (smul_right_injective E _).eq_iff
  -- ⊢ 2 ≠ 0
  exact two_ne_zero
  -- 🎉 no goals
#align reflection_eq_self_iff reflection_eq_self_iff

theorem reflection_mem_subspace_eq_self {x : E} (hx : x ∈ K) : reflection K x = x :=
  (reflection_eq_self_iff x).mpr hx
#align reflection_mem_subspace_eq_self reflection_mem_subspace_eq_self

/-- Reflection in the `Submodule.map` of a subspace. -/
theorem reflection_map_apply {E E' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E']
    [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E') (K : Submodule 𝕜 E)
    [HasOrthogonalProjection K] (x : E') :
    reflection (K.map (f.toLinearEquiv : E →ₗ[𝕜] E')) x = f (reflection K (f.symm x)) := by
  simp [two_smul, reflection_apply, orthogonalProjection_map_apply f K x]
  -- 🎉 no goals
#align reflection_map_apply reflection_map_apply

/-- Reflection in the `Submodule.map` of a subspace. -/
theorem reflection_map {E E' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E']
    [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E') (K : Submodule 𝕜 E)
    [HasOrthogonalProjection K] :
    reflection (K.map (f.toLinearEquiv : E →ₗ[𝕜] E')) = f.symm.trans ((reflection K).trans f) :=
  LinearIsometryEquiv.ext <| reflection_map_apply f K
#align reflection_map reflection_map

/-- Reflection through the trivial subspace {0} is just negation. -/
@[simp]
theorem reflection_bot : reflection (⊥ : Submodule 𝕜 E) = LinearIsometryEquiv.neg 𝕜 := by
  ext; simp [reflection_apply]
  -- ⊢ ↑(reflection ⊥) x✝ = ↑(LinearIsometryEquiv.neg 𝕜) x✝
       -- 🎉 no goals
#align reflection_bot reflection_bot

end reflection

section Orthogonal

/-- If `K₁` is complete and contained in `K₂`, `K₁` and `K₁ᗮ ⊓ K₂` span `K₂`. -/
theorem Submodule.sup_orthogonal_inf_of_completeSpace {K₁ K₂ : Submodule 𝕜 E} (h : K₁ ≤ K₂)
    [HasOrthogonalProjection K₁] : K₁ ⊔ K₁ᗮ ⊓ K₂ = K₂ := by
  ext x
  -- ⊢ x ∈ K₁ ⊔ K₁ᗮ ⊓ K₂ ↔ x ∈ K₂
  rw [Submodule.mem_sup]
  -- ⊢ (∃ y, y ∈ K₁ ∧ ∃ z, z ∈ K₁ᗮ ⊓ K₂ ∧ y + z = x) ↔ x ∈ K₂
  let v : K₁ := orthogonalProjection K₁ x
  -- ⊢ (∃ y, y ∈ K₁ ∧ ∃ z, z ∈ K₁ᗮ ⊓ K₂ ∧ y + z = x) ↔ x ∈ K₂
  have hvm : x - v ∈ K₁ᗮ := sub_orthogonalProjection_mem_orthogonal x
  -- ⊢ (∃ y, y ∈ K₁ ∧ ∃ z, z ∈ K₁ᗮ ⊓ K₂ ∧ y + z = x) ↔ x ∈ K₂
  constructor
  -- ⊢ (∃ y, y ∈ K₁ ∧ ∃ z, z ∈ K₁ᗮ ⊓ K₂ ∧ y + z = x) → x ∈ K₂
  · rintro ⟨y, hy, z, hz, rfl⟩
    -- ⊢ y + z ∈ K₂
    exact K₂.add_mem (h hy) hz.2
    -- 🎉 no goals
  · exact fun hx => ⟨v, v.prop, x - v, ⟨hvm, K₂.sub_mem hx (h v.prop)⟩, add_sub_cancel'_right _ _⟩
    -- 🎉 no goals
#align submodule.sup_orthogonal_inf_of_complete_space Submodule.sup_orthogonal_inf_of_completeSpace

variable {K}

/-- If `K` is complete, `K` and `Kᗮ` span the whole space. -/
theorem Submodule.sup_orthogonal_of_completeSpace [HasOrthogonalProjection K] : K ⊔ Kᗮ = ⊤ := by
  convert Submodule.sup_orthogonal_inf_of_completeSpace (le_top : K ≤ ⊤) using 2
  -- ⊢ Kᗮ = Kᗮ ⊓ ⊤
  simp
  -- 🎉 no goals
#align submodule.sup_orthogonal_of_complete_space Submodule.sup_orthogonal_of_completeSpace

variable (K)

/-- If `K` is complete, any `v` in `E` can be expressed as a sum of elements of `K` and `Kᗮ`. -/
theorem Submodule.exists_add_mem_mem_orthogonal [HasOrthogonalProjection K] (v : E) :
    ∃ y ∈ K, ∃ z ∈ Kᗮ, v = y + z :=
  ⟨orthogonalProjection K v, Subtype.coe_prop _, v - orthogonalProjection K v,
    sub_orthogonalProjection_mem_orthogonal _, by simp⟩
                                                  -- 🎉 no goals
#align submodule.exists_sum_mem_mem_orthogonal Submodule.exists_add_mem_mem_orthogonal

/-- If `K` admits an orthogonal projection, then the orthogonal complement of its orthogonal
complement is itself. -/
@[simp]
theorem Submodule.orthogonal_orthogonal [HasOrthogonalProjection K] : Kᗮᗮ = K := by
  ext v
  -- ⊢ v ∈ Kᗮᗮ ↔ v ∈ K
  constructor
  -- ⊢ v ∈ Kᗮᗮ → v ∈ K
  · obtain ⟨y, hy, z, hz, rfl⟩ := K.exists_add_mem_mem_orthogonal v
    -- ⊢ y + z ∈ Kᗮᗮ → y + z ∈ K
    intro hv
    -- ⊢ y + z ∈ K
    have hz' : z = 0 := by
      have hyz : ⟪z, y⟫ = 0 := by simp [hz y hy, inner_eq_zero_symm]
      simpa [inner_add_right, hyz] using hv z hz
    simp [hy, hz']
    -- 🎉 no goals
  · intro hv w hw
    -- ⊢ inner w v = 0
    rw [inner_eq_zero_symm]
    -- ⊢ inner v w = 0
    exact hw v hv
    -- 🎉 no goals
#align submodule.orthogonal_orthogonal Submodule.orthogonal_orthogonal

/-- In a Hilbert space, the orthogonal complement of the orthogonal complement of a subspace `K`
is the topological closure of `K`.

Note that the completeness assumption is necessary. Let `E` be the space `ℕ →₀ ℝ` with inner space
structure inherited from `PiLp 2 (fun _ : ℕ ↦ ℝ)`. Let `K` be the subspace of sequences with the sum
of all elements equal to zero. Then `Kᗮ = ⊥`, `Kᗮᗮ = ⊤`.  -/
theorem Submodule.orthogonal_orthogonal_eq_closure [CompleteSpace E] :
    Kᗮᗮ = K.topologicalClosure := by
  refine' le_antisymm _ _
  -- ⊢ Kᗮᗮ ≤ topologicalClosure K
  · convert Submodule.orthogonal_orthogonal_monotone K.le_topologicalClosure using 1
    -- ⊢ topologicalClosure K = (topologicalClosure K)ᗮᗮ
    rw [K.topologicalClosure.orthogonal_orthogonal]
    -- 🎉 no goals
  · exact K.topologicalClosure_minimal K.le_orthogonal_orthogonal Kᗮ.isClosed_orthogonal
    -- 🎉 no goals
#align submodule.orthogonal_orthogonal_eq_closure Submodule.orthogonal_orthogonal_eq_closure

variable {K}

/-- If `K` admits an orthogonal projection, `K` and `Kᗮ` are complements of each other. -/
theorem Submodule.isCompl_orthogonal_of_completeSpace [HasOrthogonalProjection K] : IsCompl K Kᗮ :=
  ⟨K.orthogonal_disjoint, codisjoint_iff.2 Submodule.sup_orthogonal_of_completeSpace⟩
#align submodule.is_compl_orthogonal_of_complete_space Submodule.isCompl_orthogonal_of_completeSpace

@[simp]
theorem Submodule.orthogonal_eq_bot_iff [HasOrthogonalProjection K] : Kᗮ = ⊥ ↔ K = ⊤ := by
  refine' ⟨_, fun h => by rw [h, Submodule.top_orthogonal_eq_bot]⟩
  -- ⊢ Kᗮ = ⊥ → K = ⊤
  intro h
  -- ⊢ K = ⊤
  have : K ⊔ Kᗮ = ⊤ := Submodule.sup_orthogonal_of_completeSpace
  -- ⊢ K = ⊤
  rwa [h, sup_comm, bot_sup_eq] at this
  -- 🎉 no goals
#align submodule.orthogonal_eq_bot_iff Submodule.orthogonal_eq_bot_iff

/-- The orthogonal projection onto `K` of an element of `Kᗮ` is zero. -/
theorem orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero [HasOrthogonalProjection K]
    {v : E} (hv : v ∈ Kᗮ) : orthogonalProjection K v = 0 := by
  ext
  -- ⊢ ↑(↑(orthogonalProjection K) v) = ↑0
  convert eq_orthogonalProjection_of_mem_orthogonal (K := K) _ _ <;> simp [hv]
  -- ⊢ ↑0 ∈ K
                                                                     -- 🎉 no goals
                                                                     -- 🎉 no goals
#align orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero

/-- The projection into `U` from an orthogonal submodule `V` is the zero map. -/
theorem Submodule.IsOrtho.orthogonalProjection_comp_subtypeL {U V : Submodule 𝕜 E}
    [HasOrthogonalProjection U] (h : U ⟂ V) : orthogonalProjection U ∘L V.subtypeL = 0 :=
  ContinuousLinearMap.ext fun v =>
    orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero <| h.symm v.prop
set_option linter.uppercaseLean3 false in
#align submodule.is_ortho.orthogonal_projection_comp_subtypeL Submodule.IsOrtho.orthogonalProjection_comp_subtypeL

/-- The projection into `U` from `V` is the zero map if and only if `U` and `V` are orthogonal. -/
theorem orthogonalProjection_comp_subtypeL_eq_zero_iff {U V : Submodule 𝕜 E}
    [HasOrthogonalProjection U] : orthogonalProjection U ∘L V.subtypeL = 0 ↔ U ⟂ V :=
  ⟨fun h u hu v hv => by
    convert orthogonalProjection_inner_eq_zero v u hu using 2
    -- ⊢ v = v - ↑(↑(orthogonalProjection U) v)
    have : orthogonalProjection U v = 0 := FunLike.congr_fun h (⟨_, hv⟩ : V)
    -- ⊢ v = v - ↑(↑(orthogonalProjection U) v)
    rw [this, Submodule.coe_zero, sub_zero], Submodule.IsOrtho.orthogonalProjection_comp_subtypeL⟩
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align orthogonal_projection_comp_subtypeL_eq_zero_iff orthogonalProjection_comp_subtypeL_eq_zero_iff

theorem orthogonalProjection_eq_linear_proj [HasOrthogonalProjection K] (x : E) :
    orthogonalProjection K x =
      K.linearProjOfIsCompl _ Submodule.isCompl_orthogonal_of_completeSpace x := by
  have : IsCompl K Kᗮ := Submodule.isCompl_orthogonal_of_completeSpace
  -- ⊢ ↑(orthogonalProjection K) x = ↑(Submodule.linearProjOfIsCompl K Kᗮ (_ : IsCo …
  conv_lhs => rw [← Submodule.linear_proj_add_linearProjOfIsCompl_eq_self this x]
  -- ⊢ ↑(orthogonalProjection K) (↑(↑(Submodule.linearProjOfIsCompl K Kᗮ this) x) + …
  rw [map_add, orthogonalProjection_mem_subspace_eq_self,
    orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero (Submodule.coe_mem _), add_zero]
#align orthogonal_projection_eq_linear_proj orthogonalProjection_eq_linear_proj

theorem orthogonalProjection_coe_linearMap_eq_linearProj [HasOrthogonalProjection K] :
    (orthogonalProjection K : E →ₗ[𝕜] K) =
      K.linearProjOfIsCompl _ Submodule.isCompl_orthogonal_of_completeSpace :=
  LinearMap.ext <| orthogonalProjection_eq_linear_proj
#align orthogonal_projection_coe_linear_map_eq_linear_proj orthogonalProjection_coe_linearMap_eq_linearProj

/-- The reflection in `K` of an element of `Kᗮ` is its negation. -/
theorem reflection_mem_subspace_orthogonalComplement_eq_neg [HasOrthogonalProjection K] {v : E}
    (hv : v ∈ Kᗮ) : reflection K v = -v := by
  simp [reflection_apply, orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero hv]
  -- 🎉 no goals
#align reflection_mem_subspace_orthogonal_complement_eq_neg reflection_mem_subspace_orthogonalComplement_eq_neg

/-- The orthogonal projection onto `Kᗮ` of an element of `K` is zero. -/
theorem orthogonalProjection_mem_subspace_orthogonal_precomplement_eq_zero
    [HasOrthogonalProjection Kᗮ] {v : E} (hv : v ∈ K) : orthogonalProjection Kᗮ v = 0 :=
  orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero (K.le_orthogonal_orthogonal hv)
#align orthogonal_projection_mem_subspace_orthogonal_precomplement_eq_zero orthogonalProjection_mem_subspace_orthogonal_precomplement_eq_zero

/-- If `U ≤ V`, then projecting on `V` and then on `U` is the same as projecting on `U`. -/
theorem orthogonalProjection_orthogonalProjection_of_le {U V : Submodule 𝕜 E}
    [HasOrthogonalProjection U] [HasOrthogonalProjection V] (h : U ≤ V) (x : E) :
    orthogonalProjection U (orthogonalProjection V x) = orthogonalProjection U x :=
  Eq.symm <| by
    simpa only [sub_eq_zero, map_sub] using
      orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero
        (Submodule.orthogonal_le h (sub_orthogonalProjection_mem_orthogonal x))
#align orthogonal_projection_orthogonal_projection_of_le orthogonalProjection_orthogonalProjection_of_le

/-- Given a monotone family `U` of complete submodules of `E` and a fixed `x : E`,
the orthogonal projection of `x` on `U i` tends to the orthogonal projection of `x` on
`(⨆ i, U i).topologicalClosure` along `atTop`. -/
theorem orthogonalProjection_tendsto_closure_iSup [CompleteSpace E] {ι : Type*} [SemilatticeSup ι]
    (U : ι → Submodule 𝕜 E) [∀ i, CompleteSpace (U i)] (hU : Monotone U) (x : E) :
    Filter.Tendsto (fun i => (orthogonalProjection (U i) x : E)) atTop
      (𝓝 (orthogonalProjection (⨆ i, U i).topologicalClosure x : E)) := by
  cases isEmpty_or_nonempty ι
  -- ⊢ Tendsto (fun i => ↑(↑(orthogonalProjection (U i)) x)) atTop (𝓝 ↑(↑(orthogona …
  · exact tendsto_of_isEmpty
    -- 🎉 no goals
  let y := (orthogonalProjection (⨆ i, U i).topologicalClosure x : E)
  -- ⊢ Tendsto (fun i => ↑(↑(orthogonalProjection (U i)) x)) atTop (𝓝 ↑(↑(orthogona …
  have proj_x : ∀ i, orthogonalProjection (U i) x = orthogonalProjection (U i) y := fun i =>
    (orthogonalProjection_orthogonalProjection_of_le
        ((le_iSup U i).trans (iSup U).le_topologicalClosure) _).symm
  suffices ∀ ε > 0, ∃ I, ∀ i ≥ I, ‖(orthogonalProjection (U i) y : E) - y‖ < ε by
    simpa only [proj_x, NormedAddCommGroup.tendsto_atTop] using this
  intro ε hε
  -- ⊢ ∃ I, ∀ (i : ι), i ≥ I → ‖↑(↑(orthogonalProjection (U i)) y) - y‖ < ε
  obtain ⟨a, ha, hay⟩ : ∃ a ∈ ⨆ i, U i, dist y a < ε := by
    have y_mem : y ∈ (⨆ i, U i).topologicalClosure := Submodule.coe_mem _
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at y_mem
    exact y_mem ε hε
  rw [dist_eq_norm] at hay
  -- ⊢ ∃ I, ∀ (i : ι), i ≥ I → ‖↑(↑(orthogonalProjection (U i)) y) - y‖ < ε
  obtain ⟨I, hI⟩ : ∃ I, a ∈ U I := by rwa [Submodule.mem_iSup_of_directed _ hU.directed_le] at ha
  -- ⊢ ∃ I, ∀ (i : ι), i ≥ I → ‖↑(↑(orthogonalProjection (U i)) y) - y‖ < ε
  refine' ⟨I, fun i (hi : I ≤ i) => _⟩
  -- ⊢ ‖↑(↑(orthogonalProjection (U i)) y) - y‖ < ε
  rw [norm_sub_rev, orthogonalProjection_minimal]
  -- ⊢ ⨅ (x : { x // x ∈ U i }), ‖y - ↑x‖ < ε
  refine' lt_of_le_of_lt _ hay
  -- ⊢ ⨅ (x : { x // x ∈ U i }), ‖y - ↑x‖ ≤ ‖y - a‖
  change _ ≤ ‖y - (⟨a, hU hi hI⟩ : U i)‖
  -- ⊢ ⨅ (x : { x // x ∈ U i }), ‖y - ↑x‖ ≤ ‖y - ↑{ val := a, property := (_ : a ∈  …
  exact ciInf_le ⟨0, Set.forall_range_iff.mpr fun _ => norm_nonneg _⟩ _
  -- 🎉 no goals
#align orthogonal_projection_tendsto_closure_supr orthogonalProjection_tendsto_closure_iSup

/-- Given a monotone family `U` of complete submodules of `E` with dense span supremum,
and a fixed `x : E`, the orthogonal projection of `x` on `U i` tends to `x` along `at_top`. -/
theorem orthogonalProjection_tendsto_self [CompleteSpace E] {ι : Type*} [SemilatticeSup ι]
    (U : ι → Submodule 𝕜 E) [∀ t, CompleteSpace (U t)] (hU : Monotone U) (x : E)
    (hU' : ⊤ ≤ (⨆ t, U t).topologicalClosure) :
    Filter.Tendsto (fun t => (orthogonalProjection (U t) x : E)) atTop (𝓝 x) := by
  rw [← eq_top_iff] at hU'
  -- ⊢ Tendsto (fun t => ↑(↑(orthogonalProjection (U t)) x)) atTop (𝓝 x)
  convert orthogonalProjection_tendsto_closure_iSup U hU x
  -- ⊢ x = ↑(↑(orthogonalProjection (Submodule.topologicalClosure (⨆ (i : ι), U i)) …
  rw [orthogonalProjection_eq_self_iff.mpr _]
  -- ⊢ x ∈ Submodule.topologicalClosure (⨆ (i : ι), U i)
  rw [hU']
  -- ⊢ x ∈ ⊤
  trivial
  -- 🎉 no goals
#align orthogonal_projection_tendsto_self orthogonalProjection_tendsto_self

/-- The orthogonal complement satisfies `Kᗮᗮᗮ = Kᗮ`. -/
theorem Submodule.triorthogonal_eq_orthogonal [CompleteSpace E] : Kᗮᗮᗮ = Kᗮ := by
  rw [Kᗮ.orthogonal_orthogonal_eq_closure]
  -- ⊢ topologicalClosure Kᗮ = Kᗮ
  exact K.isClosed_orthogonal.submodule_topologicalClosure_eq
  -- 🎉 no goals
#align submodule.triorthogonal_eq_orthogonal Submodule.triorthogonal_eq_orthogonal

/-- The closure of `K` is the full space iff `Kᗮ` is trivial. -/
theorem Submodule.topologicalClosure_eq_top_iff [CompleteSpace E] :
    K.topologicalClosure = ⊤ ↔ Kᗮ = ⊥ := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  -- ⊢ Kᗮᗮ = ⊤ ↔ Kᗮ = ⊥
  constructor <;> intro h
  -- ⊢ Kᗮᗮ = ⊤ → Kᗮ = ⊥
                  -- ⊢ Kᗮ = ⊥
                  -- ⊢ Kᗮᗮ = ⊤
  · rw [← Submodule.triorthogonal_eq_orthogonal, h, Submodule.top_orthogonal_eq_bot]
    -- 🎉 no goals
  · rw [h, Submodule.bot_orthogonal_eq_top]
    -- 🎉 no goals
#align submodule.topological_closure_eq_top_iff Submodule.topologicalClosure_eq_top_iff

namespace Dense

/- Porting note: unneeded assumption `[CompleteSpace E]` was removed from all theorems in this
section. TODO: Move to another file? -/
open Submodule

variable {x y : E}

theorem eq_zero_of_inner_left (hK : Dense (K : Set E)) (h : ∀ v : K, ⟪x, v⟫ = 0) : x = 0 := by
  have : (⟪x, ·⟫) = 0 := (continuous_const.inner continuous_id).ext_on
    hK continuous_const (Subtype.forall.1 h)
  simpa using congr_fun this x
  -- 🎉 no goals
#align dense.eq_zero_of_inner_left Dense.eq_zero_of_inner_left

theorem eq_zero_of_mem_orthogonal (hK : Dense (K : Set E)) (h : x ∈ Kᗮ) : x = 0 :=
  eq_zero_of_inner_left hK fun v ↦ (mem_orthogonal' _ _).1 h _ v.2
#align dense.eq_zero_of_mem_orthogonal Dense.eq_zero_of_mem_orthogonal

/-- If `S` is dense and `x - y ∈ Kᗮ`, then `x = y`. -/
theorem eq_of_sub_mem_orthogonal (hK : Dense (K : Set E)) (h : x - y ∈ Kᗮ) : x = y :=
  sub_eq_zero.1 <| eq_zero_of_mem_orthogonal hK h
#align dense.eq_of_sub_mem_orthogonal Dense.eq_of_sub_mem_orthogonal

theorem eq_of_inner_left (hK : Dense (K : Set E)) (h : ∀ v : K, ⟪x, v⟫ = ⟪y, v⟫) : x = y :=
  hK.eq_of_sub_mem_orthogonal (Submodule.sub_mem_orthogonal_of_inner_left h)
#align dense.eq_of_inner_left Dense.eq_of_inner_left

theorem eq_of_inner_right (hK : Dense (K : Set E)) (h : ∀ v : K, ⟪(v : E), x⟫ = ⟪(v : E), y⟫) :
    x = y :=
  hK.eq_of_sub_mem_orthogonal (Submodule.sub_mem_orthogonal_of_inner_right h)
#align dense.eq_of_inner_right Dense.eq_of_inner_right

theorem eq_zero_of_inner_right (hK : Dense (K : Set E)) (h : ∀ v : K, ⟪(v : E), x⟫ = 0) : x = 0 :=
  hK.eq_of_inner_right fun v => by rw [inner_zero_right, h v]
                                   -- 🎉 no goals
#align dense.eq_zero_of_inner_right Dense.eq_zero_of_inner_right

end Dense

/-- The reflection in `Kᗮ` of an element of `K` is its negation. -/
theorem reflection_mem_subspace_orthogonal_precomplement_eq_neg [HasOrthogonalProjection K] {v : E}
    (hv : v ∈ K) : reflection Kᗮ v = -v :=
  reflection_mem_subspace_orthogonalComplement_eq_neg (K.le_orthogonal_orthogonal hv)
#align reflection_mem_subspace_orthogonal_precomplement_eq_neg reflection_mem_subspace_orthogonal_precomplement_eq_neg

/-- The orthogonal projection onto `(𝕜 ∙ v)ᗮ` of `v` is zero. -/
theorem orthogonalProjection_orthogonalComplement_singleton_eq_zero (v : E) :
    orthogonalProjection (𝕜 ∙ v)ᗮ v = 0 :=
  orthogonalProjection_mem_subspace_orthogonal_precomplement_eq_zero
    (Submodule.mem_span_singleton_self v)
#align orthogonal_projection_orthogonal_complement_singleton_eq_zero orthogonalProjection_orthogonalComplement_singleton_eq_zero

/-- The reflection in `(𝕜 ∙ v)ᗮ` of `v` is `-v`. -/
theorem reflection_orthogonalComplement_singleton_eq_neg (v : E) : reflection (𝕜 ∙ v)ᗮ v = -v :=
  reflection_mem_subspace_orthogonal_precomplement_eq_neg (Submodule.mem_span_singleton_self v)
#align reflection_orthogonal_complement_singleton_eq_neg reflection_orthogonalComplement_singleton_eq_neg

theorem reflection_sub {v w : F} (h : ‖v‖ = ‖w‖) : reflection (ℝ ∙ (v - w))ᗮ v = w := by
  set R : F ≃ₗᵢ[ℝ] F := reflection (ℝ ∙ v - w)ᗮ
  -- ⊢ ↑R v = w
  suffices R v + R v = w + w by
    apply smul_right_injective F (by norm_num : (2 : ℝ) ≠ 0)
    simpa [two_smul] using this
  have h₁ : R (v - w) = -(v - w) := reflection_orthogonalComplement_singleton_eq_neg (v - w)
  -- ⊢ ↑R v + ↑R v = w + w
  have h₂ : R (v + w) = v + w := by
    apply reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    rw [real_inner_add_sub_eq_zero_iff]
    exact h
  convert congr_arg₂ (· + ·) h₂ h₁ using 1
  -- ⊢ ↑R v + ↑R v = ↑R (v + w) + ↑R (v - w)
  · simp
    -- 🎉 no goals
  · abel
    -- 🎉 no goals
    -- 🎉 no goals
#align reflection_sub reflection_sub

variable (K)

-- Porting note: relax assumptions, swap LHS with RHS
/-- If the orthogonal projection to `K` is well-defined, then a vector splits as the sum of its
orthogonal projections onto a complete submodule `K` and onto the orthogonal complement of `K`.-/
theorem orthogonalProjection_add_orthogonalProjection_orthogonal [HasOrthogonalProjection K]
    (w : E) : (orthogonalProjection K w : E) + (orthogonalProjection Kᗮ w : E) = w := by
  simp
  -- 🎉 no goals
#align eq_sum_orthogonal_projection_self_orthogonal_complement orthogonalProjection_add_orthogonalProjection_orthogonalₓ

/-- The Pythagorean theorem, for an orthogonal projection.-/
theorem norm_sq_eq_add_norm_sq_projection (x : E) (S : Submodule 𝕜 E) [HasOrthogonalProjection S] :
    ‖x‖ ^ 2 = ‖orthogonalProjection S x‖ ^ 2 + ‖orthogonalProjection Sᗮ x‖ ^ 2 :=
  calc
    ‖x‖ ^ 2 = ‖(orthogonalProjection S x : E) + orthogonalProjection Sᗮ x‖ ^ 2 := by
      rw [orthogonalProjection_add_orthogonalProjection_orthogonal]
      -- 🎉 no goals
    _ = ‖orthogonalProjection S x‖ ^ 2 + ‖orthogonalProjection Sᗮ x‖ ^ 2 := by
      simp only [sq]
      -- ⊢ ‖↑(↑(orthogonalProjection S) x) + ↑(↑(orthogonalProjection Sᗮ) x)‖ * ‖↑(↑(or …
      exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ <|
        (S.mem_orthogonal _).1 (orthogonalProjection Sᗮ x).2 _ (orthogonalProjection S x).2
#align norm_sq_eq_add_norm_sq_projection norm_sq_eq_add_norm_sq_projection

/-- In a complete space `E`, the projection maps onto a complete subspace `K` and its orthogonal
complement sum to the identity. -/
theorem id_eq_sum_orthogonalProjection_self_orthogonalComplement [HasOrthogonalProjection K] :
    ContinuousLinearMap.id 𝕜 E =
      K.subtypeL.comp (orthogonalProjection K) + Kᗮ.subtypeL.comp (orthogonalProjection Kᗮ) := by
  ext w
  -- ⊢ ↑(ContinuousLinearMap.id 𝕜 E) w = ↑(ContinuousLinearMap.comp (Submodule.subt …
  exact (orthogonalProjection_add_orthogonalProjection_orthogonal K w).symm
  -- 🎉 no goals
#align id_eq_sum_orthogonal_projection_self_orthogonal_complement id_eq_sum_orthogonalProjection_self_orthogonalComplement

-- Porting note: The priority should be higher than `Submodule.coe_inner`.
@[simp high]
theorem inner_orthogonalProjection_eq_of_mem_right [HasOrthogonalProjection K] (u : K) (v : E) :
    ⟪orthogonalProjection K v, u⟫ = ⟪v, u⟫ :=
  calc
    ⟪orthogonalProjection K v, u⟫ = ⟪(orthogonalProjection K v : E), u⟫ := K.coe_inner _ _
    _ = ⟪(orthogonalProjection K v : E), u⟫ + ⟪v - orthogonalProjection K v, u⟫ := by
      rw [orthogonalProjection_inner_eq_zero _ _ (Submodule.coe_mem _), add_zero]
      -- 🎉 no goals
    _ = ⟪v, u⟫ := by rw [← inner_add_left, add_sub_cancel'_right]
                     -- 🎉 no goals
#align inner_orthogonal_projection_eq_of_mem_right inner_orthogonalProjection_eq_of_mem_right

-- Porting note: The priority should be higher than `Submodule.coe_inner`.
@[simp high]
theorem inner_orthogonalProjection_eq_of_mem_left [HasOrthogonalProjection K] (u : K) (v : E) :
    ⟪u, orthogonalProjection K v⟫ = ⟪(u : E), v⟫ := by
  rw [← inner_conj_symm, ← inner_conj_symm (u : E), inner_orthogonalProjection_eq_of_mem_right]
  -- 🎉 no goals
#align inner_orthogonal_projection_eq_of_mem_left inner_orthogonalProjection_eq_of_mem_left

/-- The orthogonal projection is self-adjoint. -/
theorem inner_orthogonalProjection_left_eq_right [HasOrthogonalProjection K] (u v : E) :
    ⟪↑(orthogonalProjection K u), v⟫ = ⟪u, orthogonalProjection K v⟫ := by
  rw [← inner_orthogonalProjection_eq_of_mem_left, inner_orthogonalProjection_eq_of_mem_right]
  -- 🎉 no goals
#align inner_orthogonal_projection_left_eq_right inner_orthogonalProjection_left_eq_right

/-- The orthogonal projection is symmetric. -/
theorem orthogonalProjection_isSymmetric [HasOrthogonalProjection K] :
    (K.subtypeL ∘L orthogonalProjection K : E →ₗ[𝕜] E).IsSymmetric :=
  inner_orthogonalProjection_left_eq_right K
#align orthogonal_projection_is_symmetric orthogonalProjection_isSymmetric

open FiniteDimensional

/-- Given a finite-dimensional subspace `K₂`, and a subspace `K₁`
contained in it, the dimensions of `K₁` and the intersection of its
orthogonal subspace with `K₂` add to that of `K₂`. -/
theorem Submodule.finrank_add_inf_finrank_orthogonal {K₁ K₂ : Submodule 𝕜 E}
    [FiniteDimensional 𝕜 K₂] (h : K₁ ≤ K₂) :
    finrank 𝕜 K₁ + finrank 𝕜 (K₁ᗮ ⊓ K₂ : Submodule 𝕜 E) = finrank 𝕜 K₂ := by
  haveI : FiniteDimensional 𝕜 K₁ := Submodule.finiteDimensional_of_le h
  -- ⊢ finrank 𝕜 { x // x ∈ K₁ } + finrank 𝕜 { x // x ∈ K₁ᗮ ⊓ K₂ } = finrank 𝕜 { x  …
  haveI := proper_isROrC 𝕜 K₁
  -- ⊢ finrank 𝕜 { x // x ∈ K₁ } + finrank 𝕜 { x // x ∈ K₁ᗮ ⊓ K₂ } = finrank 𝕜 { x  …
  have hd := Submodule.finrank_sup_add_finrank_inf_eq K₁ (K₁ᗮ ⊓ K₂)
  -- ⊢ finrank 𝕜 { x // x ∈ K₁ } + finrank 𝕜 { x // x ∈ K₁ᗮ ⊓ K₂ } = finrank 𝕜 { x  …
  rw [← inf_assoc, (Submodule.orthogonal_disjoint K₁).eq_bot, bot_inf_eq, finrank_bot,
    Submodule.sup_orthogonal_inf_of_completeSpace h] at hd
  rw [add_zero] at hd
  -- ⊢ finrank 𝕜 { x // x ∈ K₁ } + finrank 𝕜 { x // x ∈ K₁ᗮ ⊓ K₂ } = finrank 𝕜 { x  …
  exact hd.symm
  -- 🎉 no goals
#align submodule.finrank_add_inf_finrank_orthogonal Submodule.finrank_add_inf_finrank_orthogonal

/-- Given a finite-dimensional subspace `K₂`, and a subspace `K₁`
contained in it, the dimensions of `K₁` and the intersection of its
orthogonal subspace with `K₂` add to that of `K₂`. -/
theorem Submodule.finrank_add_inf_finrank_orthogonal' {K₁ K₂ : Submodule 𝕜 E}
    [FiniteDimensional 𝕜 K₂] (h : K₁ ≤ K₂) {n : ℕ} (h_dim : finrank 𝕜 K₁ + n = finrank 𝕜 K₂) :
    finrank 𝕜 (K₁ᗮ ⊓ K₂ : Submodule 𝕜 E) = n := by
  rw [← add_right_inj (finrank 𝕜 K₁)]
  -- ⊢ finrank 𝕜 { x // x ∈ K₁ } + finrank 𝕜 { x // x ∈ K₁ᗮ ⊓ K₂ } = finrank 𝕜 { x  …
  simp [Submodule.finrank_add_inf_finrank_orthogonal h, h_dim]
  -- 🎉 no goals
#align submodule.finrank_add_inf_finrank_orthogonal' Submodule.finrank_add_inf_finrank_orthogonal'

/-- Given a finite-dimensional space `E` and subspace `K`, the dimensions of `K` and `Kᗮ` add to
that of `E`. -/
theorem Submodule.finrank_add_finrank_orthogonal [FiniteDimensional 𝕜 E] (K : Submodule 𝕜 E) :
    finrank 𝕜 K + finrank 𝕜 Kᗮ = finrank 𝕜 E := by
  convert Submodule.finrank_add_inf_finrank_orthogonal (le_top : K ≤ ⊤) using 1
  -- ⊢ finrank 𝕜 { x // x ∈ K } + finrank 𝕜 { x // x ∈ Kᗮ } = finrank 𝕜 { x // x ∈  …
  · rw [inf_top_eq]
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
#align submodule.finrank_add_finrank_orthogonal Submodule.finrank_add_finrank_orthogonal

/-- Given a finite-dimensional space `E` and subspace `K`, the dimensions of `K` and `Kᗮ` add to
that of `E`. -/
theorem Submodule.finrank_add_finrank_orthogonal' [FiniteDimensional 𝕜 E] {K : Submodule 𝕜 E}
    {n : ℕ} (h_dim : finrank 𝕜 K + n = finrank 𝕜 E) : finrank 𝕜 Kᗮ = n := by
  rw [← add_right_inj (finrank 𝕜 K)]
  -- ⊢ finrank 𝕜 { x // x ∈ K } + finrank 𝕜 { x // x ∈ Kᗮ } = finrank 𝕜 { x // x ∈  …
  simp [Submodule.finrank_add_finrank_orthogonal, h_dim]
  -- 🎉 no goals
#align submodule.finrank_add_finrank_orthogonal' Submodule.finrank_add_finrank_orthogonal'

/-- In a finite-dimensional inner product space, the dimension of the orthogonal complement of the
span of a nonzero vector is one less than the dimension of the space. -/
theorem finrank_orthogonal_span_singleton {n : ℕ} [_i : Fact (finrank 𝕜 E = n + 1)] {v : E}
    (hv : v ≠ 0) : finrank 𝕜 (𝕜 ∙ v)ᗮ = n := by
  haveI : FiniteDimensional 𝕜 E := fact_finiteDimensional_of_finrank_eq_succ n
  -- ⊢ finrank 𝕜 { x // x ∈ (Submodule.span 𝕜 {v})ᗮ } = n
  exact Submodule.finrank_add_finrank_orthogonal' <| by
    simp [finrank_span_singleton hv, _i.elim, add_comm]
#align finrank_orthogonal_span_singleton finrank_orthogonal_span_singleton

/-- An element `φ` of the orthogonal group of `F` can be factored as a product of reflections, and
specifically at most as many reflections as the dimension of the complement of the fixed subspace
of `φ`. -/
theorem LinearIsometryEquiv.reflections_generate_dim_aux [FiniteDimensional ℝ F] {n : ℕ}
    (φ : F ≃ₗᵢ[ℝ] F) (hn : finrank ℝ (ker (ContinuousLinearMap.id ℝ F - φ))ᗮ ≤ n) :
    ∃ l : List F, l.length ≤ n ∧ φ = (l.map fun v => reflection (ℝ ∙ v)ᗮ).prod := by
  -- We prove this by strong induction on `n`, the dimension of the orthogonal complement of the
  -- fixed subspace of the endomorphism `φ`
  induction' n with n IH generalizing φ
  -- ⊢ ∃ l, List.length l ≤ Nat.zero ∧ φ = List.prod (List.map (fun v => reflection …
  · -- Base case: `n = 0`, the fixed subspace is the whole space, so `φ = id`
    refine' ⟨[], rfl.le, show φ = 1 from _⟩
    -- ⊢ φ = 1
    have : ker (ContinuousLinearMap.id ℝ F - φ) = ⊤ := by
      rwa [Nat.zero_eq, le_zero_iff, finrank_eq_zero, Submodule.orthogonal_eq_bot_iff] at hn
    symm
    -- ⊢ 1 = φ
    ext x
    -- ⊢ ↑1 x = ↑φ x
    have := LinearMap.congr_fun (LinearMap.ker_eq_top.mp this) x
    -- ⊢ ↑1 x = ↑φ x
    simpa only [sub_eq_zero, ContinuousLinearMap.coe_sub, LinearMap.sub_apply,
      LinearMap.zero_apply] using this
  · -- Inductive step.  Let `W` be the fixed subspace of `φ`.  We suppose its complement to have
    -- dimension at most n + 1.
    let W := ker (ContinuousLinearMap.id ℝ F - φ)
    -- ⊢ ∃ l, List.length l ≤ Nat.succ n ∧ φ = List.prod (List.map (fun v => reflecti …
    have hW : ∀ w ∈ W, φ w = w := fun w hw => (sub_eq_zero.mp hw).symm
    -- ⊢ ∃ l, List.length l ≤ Nat.succ n ∧ φ = List.prod (List.map (fun v => reflecti …
    by_cases hn' : finrank ℝ Wᗮ ≤ n
    -- ⊢ ∃ l, List.length l ≤ Nat.succ n ∧ φ = List.prod (List.map (fun v => reflecti …
    · obtain ⟨V, hV₁, hV₂⟩ := IH φ hn'
      -- ⊢ ∃ l, List.length l ≤ Nat.succ n ∧ φ = List.prod (List.map (fun v => reflecti …
      exact ⟨V, hV₁.trans n.le_succ, hV₂⟩
      -- 🎉 no goals
    -- Take a nonzero element `v` of the orthogonal complement of `W`.
    haveI : Nontrivial Wᗮ := nontrivial_of_finrank_pos (by linarith [zero_le n] : 0 < finrank ℝ Wᗮ)
    -- ⊢ ∃ l, List.length l ≤ Nat.succ n ∧ φ = List.prod (List.map (fun v => reflecti …
    obtain ⟨v, hv⟩ := exists_ne (0 : Wᗮ)
    -- ⊢ ∃ l, List.length l ≤ Nat.succ n ∧ φ = List.prod (List.map (fun v => reflecti …
    have hφv : φ v ∈ Wᗮ := by
      intro w hw
      rw [← hW w hw, LinearIsometryEquiv.inner_map_map]
      exact v.prop w hw
    have hv' : (v : F) ∉ W := by
      intro h
      exact hv ((Submodule.mem_left_iff_eq_zero_of_disjoint W.orthogonal_disjoint).mp h)
    -- Let `ρ` be the reflection in `v - φ v`; this is designed to swap `v` and `φ v`
    let x : F := v - φ v
    -- ⊢ ∃ l, List.length l ≤ Nat.succ n ∧ φ = List.prod (List.map (fun v => reflecti …
    let ρ := reflection (ℝ ∙ x)ᗮ
    -- ⊢ ∃ l, List.length l ≤ Nat.succ n ∧ φ = List.prod (List.map (fun v => reflecti …
    -- Notation: Let `V` be the fixed subspace of `φ.trans ρ`
    let V := ker (ContinuousLinearMap.id ℝ F - φ.trans ρ)
    -- ⊢ ∃ l, List.length l ≤ Nat.succ n ∧ φ = List.prod (List.map (fun v => reflecti …
    have hV : ∀ w, ρ (φ w) = w → w ∈ V := by
      intro w hw
      change w - ρ (φ w) = 0
      rw [sub_eq_zero, hw]
    -- Everything fixed by `φ` is fixed by `φ.trans ρ`
    have H₂V : W ≤ V := by
      intro w hw
      apply hV
      rw [hW w hw]
      refine' reflection_mem_subspace_eq_self _
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
      exact Submodule.sub_mem _ v.prop hφv _ hw
    -- `v` is also fixed by `φ.trans ρ`
    have H₁V : (v : F) ∈ V := by
      apply hV
      have : ρ v = φ v := reflection_sub (φ.norm_map v).symm
      rw [← this]
      exact reflection_reflection _ _
    -- By dimension-counting, the complement of the fixed subspace of `φ.trans ρ` has dimension at
    -- most `n`
    have : finrank ℝ Vᗮ ≤ n := by
      change finrank ℝ Wᗮ ≤ n + 1 at hn
      have : finrank ℝ W + 1 ≤ finrank ℝ V :=
        Submodule.finrank_lt_finrank_of_lt (SetLike.lt_iff_le_and_exists.2 ⟨H₂V, v, H₁V, hv'⟩)
      have : finrank ℝ V + finrank ℝ Vᗮ = finrank ℝ F := V.finrank_add_finrank_orthogonal
      have : finrank ℝ W + finrank ℝ Wᗮ = finrank ℝ F := W.finrank_add_finrank_orthogonal
      linarith
    -- So apply the inductive hypothesis to `φ.trans ρ`
    obtain ⟨l, hl, hφl⟩ := IH (ρ * φ) this
    -- ⊢ ∃ l, List.length l ≤ Nat.succ n ∧ φ = List.prod (List.map (fun v => reflecti …
    -- Prepend `ρ` to the factorization into reflections obtained for `φ.trans ρ`; this gives a
    -- factorization into reflections for `φ`.
    refine' ⟨x::l, Nat.succ_le_succ hl, _⟩
    -- ⊢ φ = List.prod (List.map (fun v => reflection (Submodule.span ℝ {v})ᗮ) (x ::  …
    rw [List.map_cons, List.prod_cons]
    -- ⊢ φ = reflection (Submodule.span ℝ {x})ᗮ * List.prod (List.map (fun v => refle …
    have := congr_arg ((· * ·) ρ) hφl
    -- ⊢ φ = reflection (Submodule.span ℝ {x})ᗮ * List.prod (List.map (fun v => refle …
    dsimp only at this
    -- ⊢ φ = reflection (Submodule.span ℝ {x})ᗮ * List.prod (List.map (fun v => refle …
    rwa [← mul_assoc, reflection_mul_reflection, one_mul] at this
    -- 🎉 no goals
#align linear_isometry_equiv.reflections_generate_dim_aux LinearIsometryEquiv.reflections_generate_dim_aux

/-- The orthogonal group of `F` is generated by reflections; specifically each element `φ` of the
orthogonal group is a product of at most as many reflections as the dimension of `F`.

Special case of the **Cartan–Dieudonné theorem**. -/
theorem LinearIsometryEquiv.reflections_generate_dim [FiniteDimensional ℝ F] (φ : F ≃ₗᵢ[ℝ] F) :
    ∃ l : List F, l.length ≤ finrank ℝ F ∧ φ = (l.map fun v => reflection (ℝ ∙ v)ᗮ).prod :=
  let ⟨l, hl₁, hl₂⟩ := φ.reflections_generate_dim_aux le_rfl
  ⟨l, hl₁.trans (Submodule.finrank_le _), hl₂⟩
#align linear_isometry_equiv.reflections_generate_dim LinearIsometryEquiv.reflections_generate_dim

/-- The orthogonal group of `F` is generated by reflections. -/
theorem LinearIsometryEquiv.reflections_generate [FiniteDimensional ℝ F] :
    Subgroup.closure (Set.range fun v : F => reflection (ℝ ∙ v)ᗮ) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  -- ⊢ ∀ (x : F ≃ₗᵢ[ℝ] F), x ∈ Subgroup.closure (Set.range fun v => reflection (Sub …
  intro φ
  -- ⊢ φ ∈ Subgroup.closure (Set.range fun v => reflection (Submodule.span ℝ {v})ᗮ)
  rcases φ.reflections_generate_dim with ⟨l, _, rfl⟩
  -- ⊢ List.prod (List.map (fun v => reflection (Submodule.span ℝ {v})ᗮ) l) ∈ Subgr …
  apply (Subgroup.closure _).list_prod_mem
  -- ⊢ ∀ (x : F ≃ₗᵢ[ℝ] F), x ∈ List.map (fun v => reflection (Submodule.span ℝ {v}) …
  intro x hx
  -- ⊢ x ∈ Subgroup.closure (Set.range fun v => reflection (Submodule.span ℝ {v})ᗮ)
  rcases List.mem_map.mp hx with ⟨a, _, hax⟩
  -- ⊢ x ∈ Subgroup.closure (Set.range fun v => reflection (Submodule.span ℝ {v})ᗮ)
  exact Subgroup.subset_closure ⟨a, hax⟩
  -- 🎉 no goals
#align linear_isometry_equiv.reflections_generate LinearIsometryEquiv.reflections_generate

end Orthogonal

section OrthogonalFamily

variable {ι : Type*}

/-- An orthogonal family of subspaces of `E` satisfies `DirectSum.IsInternal` (that is,
they provide an internal direct sum decomposition of `E`) if and only if their span has trivial
orthogonal complement. -/
theorem OrthogonalFamily.isInternal_iff_of_isComplete [DecidableEq ι] {V : ι → Submodule 𝕜 E}
    (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ)
    (hc : IsComplete (↑(iSup V) : Set E)) : DirectSum.IsInternal V ↔ (iSup V)ᗮ = ⊥ := by
  haveI : CompleteSpace (↥(iSup V)) := hc.completeSpace_coe
  -- ⊢ DirectSum.IsInternal V ↔ (iSup V)ᗮ = ⊥
  simp only [DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top, hV.independent,
    true_and_iff, Submodule.orthogonal_eq_bot_iff]
#align orthogonal_family.is_internal_iff_of_is_complete OrthogonalFamily.isInternal_iff_of_isComplete

/-- An orthogonal family of subspaces of `E` satisfies `DirectSum.IsInternal` (that is,
they provide an internal direct sum decomposition of `E`) if and only if their span has trivial
orthogonal complement. -/
theorem OrthogonalFamily.isInternal_iff [DecidableEq ι] [FiniteDimensional 𝕜 E]
    {V : ι → Submodule 𝕜 E} (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    DirectSum.IsInternal V ↔ (iSup V)ᗮ = ⊥ :=
  haveI h := FiniteDimensional.proper_isROrC 𝕜 (↥(iSup V))
  hV.isInternal_iff_of_isComplete (completeSpace_coe_iff_isComplete.mp inferInstance)
#align orthogonal_family.is_internal_iff OrthogonalFamily.isInternal_iff

open DirectSum

/-- If `x` lies within an orthogonal family `v`, it can be expressed as a sum of projections. -/
theorem OrthogonalFamily.sum_projection_of_mem_iSup [Fintype ι] {V : ι → Submodule 𝕜 E}
    [∀ i, CompleteSpace (V i)] (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ)
    (x : E) (hx : x ∈ iSup V) : (∑ i, (orthogonalProjection (V i) x : E)) = x := by
  -- porting note: switch to the better `induction _ using`. Need the primed induction principle,
  -- the unprimed one doesn't work with `induction` (as it isn't as syntactically general)
  induction hx using Submodule.iSup_induction' with
  | hp i x hx =>
    refine'
      (Finset.sum_eq_single_of_mem i (Finset.mem_univ _) fun j _ hij => _).trans
        (orthogonalProjection_eq_self_iff.mpr hx)
    rw [orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero, Submodule.coe_zero]
    exact hV.isOrtho hij.symm hx
  | h0 =>
    simp_rw [map_zero, Submodule.coe_zero, Finset.sum_const_zero]
  | hadd x y _ _ hx hy =>
    simp_rw [map_add, Submodule.coe_add, Finset.sum_add_distrib]
    exact congr_arg₂ (· + ·) hx hy
#align orthogonal_family.sum_projection_of_mem_supr OrthogonalFamily.sum_projection_of_mem_iSup

/-- If a family of submodules is orthogonal, then the `orthogonalProjection` on a direct sum
is just the coefficient of that direct sum. -/
theorem OrthogonalFamily.projection_directSum_coeAddHom [DecidableEq ι] {V : ι → Submodule 𝕜 E}
    (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) (x : ⨁ i, V i) (i : ι)
    [CompleteSpace (V i)] :
    orthogonalProjection (V i) (DirectSum.coeAddMonoidHom V x) = x i := by
  induction' x using DirectSum.induction_on with j x x y hx hy
  · simp
    -- 🎉 no goals
  · simp_rw [DirectSum.coeAddMonoidHom_of, DirectSum.of]
    -- ⊢ ↑(orthogonalProjection (V i)) ↑x = ↑(↑(DFinsupp.singleAddHom (fun i => { x / …
    -- porting note: was in the previous `simp_rw`, no longer works
    rw [DFinsupp.singleAddHom_apply]
    -- ⊢ ↑(orthogonalProjection (V i)) ↑x = ↑(DFinsupp.single j x) i
    obtain rfl | hij := Decidable.eq_or_ne i j
    -- ⊢ ↑(orthogonalProjection (V i)) ↑x = ↑(DFinsupp.single i x) i
    · rw [orthogonalProjection_mem_subspace_eq_self, DFinsupp.single_eq_same]
      -- 🎉 no goals
    · rw [orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero,
        DFinsupp.single_eq_of_ne hij.symm]
      exact hV.isOrtho hij.symm x.prop
      -- 🎉 no goals
  · simp_rw [map_add]
    -- ⊢ ↑(orthogonalProjection (V i)) (↑(DirectSum.coeAddMonoidHom V) x) + ↑(orthogo …
    exact congr_arg₂ (· + ·) hx hy
    -- 🎉 no goals
#align orthogonal_family.projection_direct_sum_coe_add_hom OrthogonalFamily.projection_directSum_coeAddHom

/-- If a family of submodules is orthogonal and they span the whole space, then the orthogonal
projection provides a means to decompose the space into its submodules.

The projection function is `decompose V x i = orthogonalProjection (V i) x`.

See note [reducible non-instances]. -/
@[reducible]
def OrthogonalFamily.decomposition [DecidableEq ι] [Fintype ι] {V : ι → Submodule 𝕜 E}
    [∀ i, CompleteSpace (V i)] (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ)
    (h : iSup V = ⊤) : DirectSum.Decomposition V
    where
  decompose' x := DFinsupp.equivFunOnFintype.symm fun i => orthogonalProjection (V i) x
  left_inv x := by
    dsimp only
    -- ⊢ ↑(DirectSum.coeAddMonoidHom V) (↑DFinsupp.equivFunOnFintype.symm fun i => ↑( …
    letI := fun i => Classical.decEq (V i)
    -- ⊢ ↑(DirectSum.coeAddMonoidHom V) (↑DFinsupp.equivFunOnFintype.symm fun i => ↑( …
    rw [DirectSum.coeAddMonoidHom, DirectSum.toAddMonoid, DFinsupp.liftAddHom_apply,
      DFinsupp.sumAddHom_apply, DFinsupp.sum_eq_sum_fintype]
    · simp_rw [Equiv.apply_symm_apply, AddSubmonoidClass.coe_subtype]
      -- ⊢ ∑ x_1 : ι, ↑(↑(orthogonalProjection (V x_1)) x) = x
      exact hV.sum_projection_of_mem_iSup _ ((h.ge : _) Submodule.mem_top)
      -- 🎉 no goals
    · intro i
      -- ⊢ ↑(AddSubmonoidClass.subtype (V i)) 0 = 0
      exact map_zero _
      -- 🎉 no goals
  right_inv x := by
    dsimp only
    -- ⊢ (↑DFinsupp.equivFunOnFintype.symm fun i => ↑(orthogonalProjection (V i)) (↑( …
    simp_rw [hV.projection_directSum_coeAddHom, DFinsupp.equivFunOnFintype_symm_coe]
    -- 🎉 no goals
#align orthogonal_family.decomposition OrthogonalFamily.decomposition

end OrthogonalFamily

section OrthonormalBasis

variable {v : Set E}

open FiniteDimensional Submodule Set

/-- An orthonormal set in an `InnerProductSpace` is maximal, if and only if the orthogonal
complement of its span is empty. -/
theorem maximal_orthonormal_iff_orthogonalComplement_eq_bot (hv : Orthonormal 𝕜 ((↑) : v → E)) :
    (∀ (u) (_ : u ⊇ v), Orthonormal 𝕜 ((↑) : u → E) → u = v) ↔ (span 𝕜 v)ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  -- ⊢ (∀ (u : Set E), u ⊇ v → Orthonormal 𝕜 Subtype.val → u = v) ↔ ∀ (x : E), x ∈  …
  constructor
  -- ⊢ (∀ (u : Set E), u ⊇ v → Orthonormal 𝕜 Subtype.val → u = v) → ∀ (x : E), x ∈  …
  · contrapose!
    -- ⊢ (∃ x, x ∈ (span 𝕜 v)ᗮ ∧ x ≠ 0) → ∃ u, u ⊇ v ∧ Orthonormal 𝕜 Subtype.val ∧ u  …
    -- ** direction 1: nonempty orthogonal complement implies nonmaximal
    rintro ⟨x, hx', hx⟩
    -- ⊢ ∃ u, u ⊇ v ∧ Orthonormal 𝕜 Subtype.val ∧ u ≠ v
    -- take a nonzero vector and normalize it
    let e := (‖x‖⁻¹ : 𝕜) • x
    -- ⊢ ∃ u, u ⊇ v ∧ Orthonormal 𝕜 Subtype.val ∧ u ≠ v
    have he : ‖e‖ = 1 := by simp [norm_smul_inv_norm hx]
    -- ⊢ ∃ u, u ⊇ v ∧ Orthonormal 𝕜 Subtype.val ∧ u ≠ v
    have he' : e ∈ (span 𝕜 v)ᗮ := smul_mem' _ _ hx'
    -- ⊢ ∃ u, u ⊇ v ∧ Orthonormal 𝕜 Subtype.val ∧ u ≠ v
    have he'' : e ∉ v := by
      intro hev
      have : e = 0 := by
        have : e ∈ span 𝕜 v ⊓ (span 𝕜 v)ᗮ := ⟨subset_span hev, he'⟩
        simpa [(span 𝕜 v).inf_orthogonal_eq_bot] using this
      have : e ≠ 0 := hv.ne_zero ⟨e, hev⟩
      contradiction
    -- put this together with `v` to provide a candidate orthonormal basis for the whole space
    refine' ⟨insert e v, v.subset_insert e, ⟨_, _⟩, (ne_insert_of_not_mem v he'').symm⟩
    -- ⊢ ∀ (i : { x // x ∈ insert e v }), ‖↑i‖ = 1
    · -- show that the elements of `insert e v` have unit length
      rintro ⟨a, ha'⟩
      -- ⊢ ‖↑{ val := a, property := ha' }‖ = 1
      cases' eq_or_mem_of_mem_insert ha' with ha ha
      -- ⊢ ‖↑{ val := a, property := ha' }‖ = 1
      · simp [ha, he]
        -- 🎉 no goals
      · exact hv.1 ⟨a, ha⟩
        -- 🎉 no goals
    · -- show that the elements of `insert e v` are orthogonal
      have h_end : ∀ a ∈ v, ⟪a, e⟫ = 0 := by
        intro a ha
        exact he' a (Submodule.subset_span ha)
      rintro ⟨a, ha'⟩
      -- ⊢ ∀ {j : { x // x ∈ insert e v }}, { val := a, property := ha' } ≠ j → inner ↑ …
      cases' eq_or_mem_of_mem_insert ha' with ha ha
      -- ⊢ ∀ {j : { x // x ∈ insert e v }}, { val := a, property := ha' } ≠ j → inner ↑ …
      · rintro ⟨b, hb'⟩ hab'
        -- ⊢ inner ↑{ val := a, property := ha' } ↑{ val := b, property := hb' } = 0
        have hb : b ∈ v := by
          refine' mem_of_mem_insert_of_ne hb' _
          intro hbe'
          apply hab'
          simp [ha, hbe']
        rw [inner_eq_zero_symm]
        -- ⊢ inner ↑{ val := b, property := hb' } ↑{ val := a, property := ha' } = 0
        simpa [ha] using h_end b hb
        -- 🎉 no goals
      rintro ⟨b, hb'⟩ hab'
      -- ⊢ inner ↑{ val := a, property := ha' } ↑{ val := b, property := hb' } = 0
      cases' eq_or_mem_of_mem_insert hb' with hb hb
      -- ⊢ inner ↑{ val := a, property := ha' } ↑{ val := b, property := hb' } = 0
      · simpa [hb] using h_end a ha
        -- 🎉 no goals
      have : (⟨a, ha⟩ : v) ≠ ⟨b, hb⟩ := by
        intro hab''
        apply hab'
        simpa using hab''
      exact hv.2 this
      -- 🎉 no goals
  · -- ** direction 2: empty orthogonal complement implies maximal
    simp only [Subset.antisymm_iff]
    -- ⊢ (∀ (x : E), x ∈ (span 𝕜 v)ᗮ → x = 0) → ∀ (u : Set E), u ⊇ v → Orthonormal 𝕜  …
    rintro h u (huv : v ⊆ u) hu
    -- ⊢ u ⊆ v ∧ v ⊆ u
    refine' ⟨_, huv⟩
    -- ⊢ u ⊆ v
    intro x hxu
    -- ⊢ x ∈ v
    refine' ((mt (h x)) (hu.ne_zero ⟨x, hxu⟩)).imp_symm _
    -- ⊢ ¬x ∈ v → x ∈ (span 𝕜 v)ᗮ
    intro hxv y hy
    -- ⊢ inner y x = 0
    have hxv' : (⟨x, hxu⟩ : u) ∉ ((↑) ⁻¹' v : Set u) := by simp [huv, hxv]
    -- ⊢ inner y x = 0
    obtain ⟨l, hl, rfl⟩ :
      ∃ l ∈ Finsupp.supported 𝕜 𝕜 ((↑) ⁻¹' v : Set u), (Finsupp.total (↥u) E 𝕜 (↑)) l = y := by
      rw [← Finsupp.mem_span_image_iff_total]
      simp [huv, inter_eq_self_of_subset_left, hy]
    exact hu.inner_finsupp_eq_zero hxv' hl
    -- 🎉 no goals
#align maximal_orthonormal_iff_orthogonal_complement_eq_bot maximal_orthonormal_iff_orthogonalComplement_eq_bot

variable [FiniteDimensional 𝕜 E]

/-- An orthonormal set in a finite-dimensional `InnerProductSpace` is maximal, if and only if it
is a basis. -/
theorem maximal_orthonormal_iff_basis_of_finiteDimensional (hv : Orthonormal 𝕜 ((↑) : v → E)) :
    (∀ (u) (_ : u ⊇ v), Orthonormal 𝕜 ((↑) : u → E) → u = v) ↔
      ∃ b : Basis v 𝕜 E, ⇑b = ((↑) : v → E) := by
  haveI := proper_isROrC 𝕜 (span 𝕜 v)
  -- ⊢ (∀ (u : Set E), u ⊇ v → Orthonormal 𝕜 Subtype.val → u = v) ↔ ∃ b, ↑b = Subty …
  rw [maximal_orthonormal_iff_orthogonalComplement_eq_bot hv]
  -- ⊢ (span 𝕜 v)ᗮ = ⊥ ↔ ∃ b, ↑b = Subtype.val
  rw [Submodule.orthogonal_eq_bot_iff]
  -- ⊢ span 𝕜 v = ⊤ ↔ ∃ b, ↑b = Subtype.val
  have hv_coe : range ((↑) : v → E) = v := by simp
  -- ⊢ span 𝕜 v = ⊤ ↔ ∃ b, ↑b = Subtype.val
  constructor
  -- ⊢ span 𝕜 v = ⊤ → ∃ b, ↑b = Subtype.val
  · refine' fun h => ⟨Basis.mk hv.linearIndependent _, Basis.coe_mk _ _⟩
    -- ⊢ ⊤ ≤ span 𝕜 (Set.range Subtype.val)
    convert h.ge
    -- 🎉 no goals
  · rintro ⟨h, coe_h⟩
    -- ⊢ span 𝕜 v = ⊤
    rw [← h.span_eq, coe_h, hv_coe]
    -- 🎉 no goals
#align maximal_orthonormal_iff_basis_of_finite_dimensional maximal_orthonormal_iff_basis_of_finiteDimensional

end OrthonormalBasis
