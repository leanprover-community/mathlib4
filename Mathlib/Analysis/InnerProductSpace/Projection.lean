/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Frédéric Dupuis, Heather Macbeth
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.NormedSpace.RCLike
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Algebra.DirectSum.Decomposition

/-!
# The orthogonal projection

Given a nonempty complete subspace `K` of an inner product space `E`, this file constructs
`K.orthogonalProjection : E →L[𝕜] K`, the orthogonal projection of `E` onto `K`.  This map
satisfies: for any point `u` in `E`, the point `v = K.orthogonalProjection u` in `K` minimizes the
distance `‖u - v‖` to `u`.

Also a linear isometry equivalence `K.reflection : E ≃ₗᵢ[𝕜] E` is constructed, by choosing, for
each `u : E`, the point `K.reflection u` to satisfy
`u + (K.reflection u) = 2 • K.orthogonalProjection u`.

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

open InnerProductSpace

open RCLike Real Filter

open LinearMap (ker range)

open Topology Finsupp

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
local notation "absR" => @abs ℝ _ _

/-! ### Orthogonal projection in inner product spaces -/


-- FIXME this monolithic proof causes a deterministic timeout with `-T50000`
-- It should be broken in a sequence of more manageable pieces,
-- perhaps with individual statements for the three steps below.
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
            show
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
        have := this (1 : ℝ) (by norm_num) (by norm_num)
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
            exact this θ (lt_min (by norm_num) (div_pos hp q_pos)) (by norm_num [θ])
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
    · show ⨅ w : K, ‖u - w‖ ≤ (fun w : K => ‖u - w‖) ⟨v, hv⟩
      apply ciInf_le
      use 0
      rintro y ⟨z, rfl⟩
      exact norm_nonneg _

variable (K : Submodule 𝕜 E)

namespace Submodule

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
          simp only [w'', neg_inj, add_neg_cancel_right, sub_eq_add_neg]
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

/-- A subspace `K : Submodule 𝕜 E` has an orthogonal projection if every vector `v : E` admits an
orthogonal projection to `K`. -/
class HasOrthogonalProjection (K : Submodule 𝕜 E) : Prop where
  exists_orthogonal (v : E) : ∃ w ∈ K, v - w ∈ Kᗮ

instance (priority := 100) HasOrthogonalProjection.ofCompleteSpace [CompleteSpace K] :
    K.HasOrthogonalProjection where
  exists_orthogonal v := by
    rcases K.exists_norm_eq_iInf_of_complete_subspace (completeSpace_coe_iff_isComplete.mp ‹_›) v
      with ⟨w, hwK, hw⟩
    refine ⟨w, hwK, (K.mem_orthogonal' _).2 ?_⟩
    rwa [← K.norm_eq_iInf_iff_inner_eq_zero hwK]

instance [K.HasOrthogonalProjection] : Kᗮ.HasOrthogonalProjection where
  exists_orthogonal v := by
    rcases HasOrthogonalProjection.exists_orthogonal (K := K) v with ⟨w, hwK, hw⟩
    refine ⟨_, hw, ?_⟩
    rw [sub_sub_cancel]
    exact K.le_orthogonal_orthogonal hwK

instance HasOrthogonalProjection.map_linearIsometryEquiv [K.HasOrthogonalProjection]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E') :
    (K.map (f.toLinearEquiv : E →ₗ[𝕜] E')).HasOrthogonalProjection where
  exists_orthogonal v := by
    rcases HasOrthogonalProjection.exists_orthogonal (K := K) (f.symm v) with ⟨w, hwK, hw⟩
    refine ⟨f w, Submodule.mem_map_of_mem hwK, Set.forall_mem_image.2 fun u hu ↦ ?_⟩
    erw [← f.symm.inner_map_map, f.symm_apply_apply, map_sub, f.symm_apply_apply, hw u hu]

instance HasOrthogonalProjection.map_linearIsometryEquiv' [K.HasOrthogonalProjection]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E') :
    (K.map f.toLinearIsometry).HasOrthogonalProjection :=
  HasOrthogonalProjection.map_linearIsometryEquiv K f

instance : (⊤ : Submodule 𝕜 E).HasOrthogonalProjection := ⟨fun v ↦ ⟨v, trivial, by simp⟩⟩

section orthogonalProjection

variable [K.HasOrthogonalProjection]

/-- The orthogonal projection onto a complete subspace, as an
unbundled function.  This definition is only intended for use in
setting up the bundled version `orthogonalProjection` and should not
be used once that is defined. -/
def orthogonalProjectionFn (v : E) :=
  (HasOrthogonalProjection.exists_orthogonal (K := K) v).choose

variable {K}

/-- The unbundled orthogonal projection is in the given subspace.
This lemma is only intended for use in setting up the bundled version
and should not be used once that is defined. -/
theorem orthogonalProjectionFn_mem (v : E) : K.orthogonalProjectionFn v ∈ K :=
  (HasOrthogonalProjection.exists_orthogonal (K := K) v).choose_spec.left

/-- The characterization of the unbundled orthogonal projection.  This
lemma is only intended for use in setting up the bundled version
and should not be used once that is defined. -/
theorem orthogonalProjectionFn_inner_eq_zero (v : E) :
    ∀ w ∈ K, ⟪v - K.orthogonalProjectionFn v, w⟫ = 0 :=
  (K.mem_orthogonal' _).1 (HasOrthogonalProjection.exists_orthogonal (K := K) v).choose_spec.right

/-- The unbundled orthogonal projection is the unique point in `K`
with the orthogonality property.  This lemma is only intended for use
in setting up the bundled version and should not be used once that is
defined. -/
theorem eq_orthogonalProjectionFn_of_mem_of_inner_eq_zero {u v : E} (hvm : v ∈ K)
    (hvo : ∀ w ∈ K, ⟪u - v, w⟫ = 0) : K.orthogonalProjectionFn u = v := by
  rw [← sub_eq_zero, ← @inner_self_eq_zero 𝕜]
  have hvs : K.orthogonalProjectionFn u - v ∈ K :=
    Submodule.sub_mem K (orthogonalProjectionFn_mem u) hvm
  have huo : ⟪u - K.orthogonalProjectionFn u, K.orthogonalProjectionFn u - v⟫ = 0 :=
    orthogonalProjectionFn_inner_eq_zero u _ hvs
  have huv : ⟪u - v, K.orthogonalProjectionFn u - v⟫ = 0 := hvo _ hvs
  have houv : ⟪u - v - (u - K.orthogonalProjectionFn u), K.orthogonalProjectionFn u - v⟫ = 0 := by
    rw [inner_sub_left, huo, huv, sub_zero]
  rwa [sub_sub_sub_cancel_left] at houv

variable (K)

theorem orthogonalProjectionFn_norm_sq (v : E) :
    ‖v‖ * ‖v‖ =
      ‖v - K.orthogonalProjectionFn v‖ * ‖v - K.orthogonalProjectionFn v‖ +
        ‖K.orthogonalProjectionFn v‖ * ‖K.orthogonalProjectionFn v‖ := by
  set p := K.orthogonalProjectionFn v
  have h' : ⟪v - p, p⟫ = 0 :=
    orthogonalProjectionFn_inner_eq_zero _ _ (orthogonalProjectionFn_mem v)
  convert norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (v - p) p h' using 2 <;> simp

/-- The orthogonal projection onto a complete subspace. -/
def orthogonalProjection : E →L[𝕜] K :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨K.orthogonalProjectionFn v, orthogonalProjectionFn_mem v⟩
      map_add' := fun x y => by
        have hm : K.orthogonalProjectionFn x + K.orthogonalProjectionFn y ∈ K :=
          Submodule.add_mem K (orthogonalProjectionFn_mem x) (orthogonalProjectionFn_mem y)
        have ho :
          ∀ w ∈ K, ⟪x + y - (K.orthogonalProjectionFn x + K.orthogonalProjectionFn y), w⟫ = 0 := by
          intro w hw
          rw [add_sub_add_comm, inner_add_left, orthogonalProjectionFn_inner_eq_zero _ w hw,
            orthogonalProjectionFn_inner_eq_zero _ w hw, add_zero]
        ext
        simp [eq_orthogonalProjectionFn_of_mem_of_inner_eq_zero hm ho]
      map_smul' := fun c x => by
        have hm : c • K.orthogonalProjectionFn x ∈ K :=
          Submodule.smul_mem K _ (orthogonalProjectionFn_mem x)
        have ho : ∀ w ∈ K, ⟪c • x - c • K.orthogonalProjectionFn x, w⟫ = 0 := by
          intro w hw
          rw [← smul_sub, inner_smul_left, orthogonalProjectionFn_inner_eq_zero _ w hw,
            mul_zero]
        ext
        simp [eq_orthogonalProjectionFn_of_mem_of_inner_eq_zero hm ho] }
    1 fun x => by
    simp only [one_mul, LinearMap.coe_mk]
    refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
    change ‖K.orthogonalProjectionFn x‖ ^ 2 ≤ ‖x‖ ^ 2
    nlinarith [K.orthogonalProjectionFn_norm_sq x]

variable {K}

@[simp]
theorem orthogonalProjectionFn_eq (v : E) :
    K.orthogonalProjectionFn v = (K.orthogonalProjection v : E) :=
  rfl

/-- The characterization of the orthogonal projection. -/
@[simp]
theorem orthogonalProjection_inner_eq_zero (v : E) :
    ∀ w ∈ K, ⟪v - K.orthogonalProjection v, w⟫ = 0 :=
  orthogonalProjectionFn_inner_eq_zero v

/-- The difference of `v` from its orthogonal projection onto `K` is in `Kᗮ`. -/
@[simp]
theorem sub_orthogonalProjection_mem_orthogonal (v : E) : v - K.orthogonalProjection v ∈ Kᗮ := by
  intro w hw
  rw [inner_eq_zero_symm]
  exact orthogonalProjection_inner_eq_zero _ _ hw

/-- The orthogonal projection is the unique point in `K` with the
orthogonality property. -/
theorem eq_orthogonalProjection_of_mem_of_inner_eq_zero {u v : E} (hvm : v ∈ K)
    (hvo : ∀ w ∈ K, ⟪u - v, w⟫ = 0) : (K.orthogonalProjection u : E) = v :=
  eq_orthogonalProjectionFn_of_mem_of_inner_eq_zero hvm hvo

/-- A point in `K` with the orthogonality property (here characterized in terms of `Kᗮ`) must be the
orthogonal projection. -/
theorem eq_orthogonalProjection_of_mem_orthogonal {u v : E} (hv : v ∈ K)
    (hvo : u - v ∈ Kᗮ) : (K.orthogonalProjection u : E) = v :=
  eq_orthogonalProjectionFn_of_mem_of_inner_eq_zero hv <| (Submodule.mem_orthogonal' _ _).1 hvo

/-- A point in `K` with the orthogonality property (here characterized in terms of `Kᗮ`) must be the
orthogonal projection. -/
theorem eq_orthogonalProjection_of_mem_orthogonal' {u v z : E}
    (hv : v ∈ K) (hz : z ∈ Kᗮ) (hu : u = v + z) : (K.orthogonalProjection u : E) = v :=
  eq_orthogonalProjection_of_mem_orthogonal hv (by simpa [hu] )

@[simp]
theorem orthogonalProjection_orthogonal_val (u : E) :
    (Kᗮ.orthogonalProjection u : E) = u - K.orthogonalProjection u :=
  eq_orthogonalProjection_of_mem_orthogonal' (sub_orthogonalProjection_mem_orthogonal _)
    (K.le_orthogonal_orthogonal (K.orthogonalProjection u).2) <| by simp

theorem orthogonalProjection_orthogonal (u : E) :
    Kᗮ.orthogonalProjection u =
      ⟨u - K.orthogonalProjection u, sub_orthogonalProjection_mem_orthogonal _⟩ :=
  Subtype.eq <| orthogonalProjection_orthogonal_val _

/-- The orthogonal projection of `y` on `U` minimizes the distance `‖y - x‖` for `x ∈ U`. -/
theorem orthogonalProjection_minimal {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (y : E) :
    ‖y - U.orthogonalProjection y‖ = ⨅ x : U, ‖y - x‖ := by
  rw [U.norm_eq_iInf_iff_inner_eq_zero (Submodule.coe_mem _)]
  exact orthogonalProjection_inner_eq_zero _

/-- The orthogonal projections onto equal subspaces are coerced back to the same point in `E`. -/
theorem eq_orthogonalProjection_of_eq_submodule {K' : Submodule 𝕜 E} [K'.HasOrthogonalProjection]
    (h : K = K') (u : E) : (K.orthogonalProjection u : E) = (K'.orthogonalProjection u : E) := by
  subst h; rfl

/-- The orthogonal projection sends elements of `K` to themselves. -/
@[simp]
theorem orthogonalProjection_mem_subspace_eq_self (v : K) : K.orthogonalProjection v = v := by
  ext
  apply eq_orthogonalProjection_of_mem_of_inner_eq_zero <;> simp

/-- A point equals its orthogonal projection if and only if it lies in the subspace. -/
theorem orthogonalProjection_eq_self_iff {v : E} : (K.orthogonalProjection v : E) = v ↔ v ∈ K := by
  refine ⟨fun h => ?_, fun h => eq_orthogonalProjection_of_mem_of_inner_eq_zero h ?_⟩
  · rw [← h]
    simp
  · simp

@[simp]
theorem orthogonalProjection_eq_zero_iff {v : E} : K.orthogonalProjection v = 0 ↔ v ∈ Kᗮ := by
  refine ⟨fun h ↦ ?_, fun h ↦ Subtype.eq <| eq_orthogonalProjection_of_mem_orthogonal
    (zero_mem _) ?_⟩
  · simpa [h] using sub_orthogonalProjection_mem_orthogonal (K := K) v
  · simpa

@[simp]
theorem ker_orthogonalProjection : LinearMap.ker K.orthogonalProjection = Kᗮ := by
  ext; exact orthogonalProjection_eq_zero_iff

theorem _root_.LinearIsometry.map_orthogonalProjection {E E' : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E →ₗᵢ[𝕜] E')
    (p : Submodule 𝕜 E) [p.HasOrthogonalProjection] [(p.map f.toLinearMap).HasOrthogonalProjection]
    (x : E) : f (p.orthogonalProjection x) = (p.map f.toLinearMap).orthogonalProjection (f x) := by
  refine (eq_orthogonalProjection_of_mem_of_inner_eq_zero ?_ fun y hy => ?_).symm
  · refine Submodule.apply_coe_mem_map _ _
  rcases hy with ⟨x', hx', rfl : f x' = y⟩
  rw [← f.map_sub, f.inner_map_map, orthogonalProjection_inner_eq_zero x x' hx']

theorem _root_.LinearIsometry.map_orthogonalProjection' {E E' : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E →ₗᵢ[𝕜] E')
    (p : Submodule 𝕜 E) [p.HasOrthogonalProjection] [(p.map f).HasOrthogonalProjection] (x : E) :
    f (p.orthogonalProjection x) = (p.map f).orthogonalProjection (f x) :=
  have : (p.map f.toLinearMap).HasOrthogonalProjection := ‹_›
  f.map_orthogonalProjection p x

/-- Orthogonal projection onto the `Submodule.map` of a subspace. -/
theorem orthogonalProjection_map_apply {E E' : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E')
    (p : Submodule 𝕜 E) [p.HasOrthogonalProjection] (x : E') :
    ((p.map (f.toLinearEquiv : E →ₗ[𝕜] E')).orthogonalProjection x : E') =
      f (p.orthogonalProjection (f.symm x)) := by
  simpa only [f.coe_toLinearIsometry, f.apply_symm_apply] using
    (f.toLinearIsometry.map_orthogonalProjection' p (f.symm x)).symm

/-- The orthogonal projection onto the trivial submodule is the zero map. -/
@[simp]
theorem orthogonalProjection_bot : (⊥ : Submodule 𝕜 E).orthogonalProjection = 0 := by ext

variable (K)

/-- The orthogonal projection has norm `≤ 1`. -/
theorem orthogonalProjection_norm_le : ‖K.orthogonalProjection‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

variable (𝕜)

theorem smul_orthogonalProjection_singleton {v : E} (w : E) :
    ((‖v‖ ^ 2 : ℝ) : 𝕜) • ((𝕜 ∙ v).orthogonalProjection w : E) = ⟪v, w⟫ • v := by
  suffices (((𝕜 ∙ v).orthogonalProjection (((‖v‖ : 𝕜) ^ 2) • w)) : E) = ⟪v, w⟫ • v by
    simpa using this
  apply eq_orthogonalProjection_of_mem_of_inner_eq_zero
  · rw [Submodule.mem_span_singleton]
    use ⟪v, w⟫
  · rw [← Submodule.mem_orthogonal', Submodule.mem_orthogonal_singleton_iff_inner_left]
    simp [inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K, mul_comm]

/-- Formula for orthogonal projection onto a single vector. -/
theorem orthogonalProjection_singleton {v : E} (w : E) :
    ((𝕜 ∙ v).orthogonalProjection w : E) = (⟪v, w⟫ / ((‖v‖ ^ 2 : ℝ) : 𝕜)) • v := by
  by_cases hv : v = 0
  · rw [hv, eq_orthogonalProjection_of_eq_submodule (Submodule.span_zero_singleton 𝕜)]
    simp
  have hv' : ‖v‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr hv)
  have key :
    (((‖v‖ ^ 2 : ℝ) : 𝕜)⁻¹ * ((‖v‖ ^ 2 : ℝ) : 𝕜)) • (((𝕜 ∙ v).orthogonalProjection w) : E) =
      (((‖v‖ ^ 2 : ℝ) : 𝕜)⁻¹ * ⟪v, w⟫) • v := by
    simp [mul_smul, smul_orthogonalProjection_singleton 𝕜 w, -map_pow]
  convert key using 1 <;> field_simp [hv']

/-- Formula for orthogonal projection onto a single unit vector. -/
theorem orthogonalProjection_unit_singleton {v : E} (hv : ‖v‖ = 1) (w : E) :
    ((𝕜 ∙ v).orthogonalProjection w : E) = ⟪v, w⟫ • v := by
  rw [← smul_orthogonalProjection_singleton 𝕜 w]
  simp [hv]

end orthogonalProjection

section reflection

variable [K.HasOrthogonalProjection]

/-- Auxiliary definition for `reflection`: the reflection as a linear equivalence. -/
def reflectionLinearEquiv : E ≃ₗ[𝕜] E :=
  LinearEquiv.ofInvolutive
    (2 • (K.subtype.comp K.orthogonalProjection.toLinearMap) - LinearMap.id) fun x => by
    simp [two_smul]

/-- Reflection in a complete subspace of an inner product space.  The word "reflection" is
sometimes understood to mean specifically reflection in a codimension-one subspace, and sometimes
more generally to cover operations such as reflection in a point.  The definition here, of
reflection in a subspace, is a more general sense of the word that includes both those common
cases. -/
def reflection : E ≃ₗᵢ[𝕜] E :=
  { K.reflectionLinearEquiv with
    norm_map' := by
      intro x
      let w : K := K.orthogonalProjection x
      let v := x - w
      have : ⟪v, w⟫ = 0 := orthogonalProjection_inner_eq_zero x w w.2
      convert norm_sub_eq_norm_add this using 2
      · dsimp [reflectionLinearEquiv, v]
        abel
      · simp only [v, add_sub_cancel, eq_self_iff_true] }

variable {K}

/-- The result of reflecting. -/
theorem reflection_apply (p : E) : K.reflection p = 2 • (K.orthogonalProjection p : E) - p :=
  rfl

/-- Reflection is its own inverse. -/
@[simp]
theorem reflection_symm : K.reflection.symm = K.reflection :=
  rfl

/-- Reflection is its own inverse. -/
@[simp]
theorem reflection_inv : K.reflection⁻¹ = K.reflection :=
  rfl

variable (K)

/-- Reflecting twice in the same subspace. -/
@[simp]
theorem reflection_reflection (p : E) : K.reflection (K.reflection p) = p :=
  K.reflection.left_inv p

/-- Reflection is involutive. -/
theorem reflection_involutive : Function.Involutive K.reflection :=
  K.reflection_reflection

/-- Reflection is involutive. -/
@[simp]
theorem reflection_trans_reflection :
    K.reflection.trans K.reflection = LinearIsometryEquiv.refl 𝕜 E :=
  LinearIsometryEquiv.ext <| reflection_involutive K

/-- Reflection is involutive. -/
@[simp]
theorem reflection_mul_reflection : K.reflection * K.reflection = 1 :=
  reflection_trans_reflection _
theorem reflection_orthogonal_apply (v : E) : Kᗮ.reflection v = -K.reflection v := by
  simp [reflection_apply]; abel

theorem reflection_orthogonal : Kᗮ.reflection = .trans K.reflection (.neg _) := by
  ext; apply reflection_orthogonal_apply

variable {K}

theorem reflection_singleton_apply (u v : E) :
    reflection (𝕜 ∙ u) v = 2 • (⟪u, v⟫ / ((‖u‖ : 𝕜) ^ 2)) • u - v := by
  rw [reflection_apply, orthogonalProjection_singleton, ofReal_pow]

/-- A point is its own reflection if and only if it is in the subspace. -/
theorem reflection_eq_self_iff (x : E) : K.reflection x = x ↔ x ∈ K := by
  rw [← orthogonalProjection_eq_self_iff, reflection_apply, sub_eq_iff_eq_add', ← two_smul 𝕜,
    two_smul ℕ, ← two_smul 𝕜]
  refine (smul_right_injective E ?_).eq_iff
  exact two_ne_zero

theorem reflection_mem_subspace_eq_self {x : E} (hx : x ∈ K) : K.reflection x = x :=
  (reflection_eq_self_iff x).mpr hx

/-- Reflection in the `Submodule.map` of a subspace. -/
theorem reflection_map_apply {E E' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E']
    [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E') (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (x : E') :
    reflection (K.map (f.toLinearEquiv : E →ₗ[𝕜] E')) x = f (K.reflection (f.symm x)) := by
  simp [two_smul, reflection_apply, orthogonalProjection_map_apply f K x]

/-- Reflection in the `Submodule.map` of a subspace. -/
theorem reflection_map {E E' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E']
    [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E') (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] :
    reflection (K.map (f.toLinearEquiv : E →ₗ[𝕜] E')) = f.symm.trans (K.reflection.trans f) :=
  LinearIsometryEquiv.ext <| reflection_map_apply f K

/-- Reflection through the trivial subspace {0} is just negation. -/
@[simp]
theorem reflection_bot : reflection (⊥ : Submodule 𝕜 E) = LinearIsometryEquiv.neg 𝕜 := by
  ext; simp [reflection_apply]

end reflection

end Submodule

section Orthogonal

namespace Submodule

/-- If `K₁` is complete and contained in `K₂`, `K₁` and `K₁ᗮ ⊓ K₂` span `K₂`. -/
theorem sup_orthogonal_inf_of_completeSpace {K₁ K₂ : Submodule 𝕜 E} (h : K₁ ≤ K₂)
    [K₁.HasOrthogonalProjection] : K₁ ⊔ K₁ᗮ ⊓ K₂ = K₂ := by
  ext x
  rw [Submodule.mem_sup]
  let v : K₁ := orthogonalProjection K₁ x
  have hvm : x - v ∈ K₁ᗮ := sub_orthogonalProjection_mem_orthogonal x
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact K₂.add_mem (h hy) hz.2
  · exact fun hx => ⟨v, v.prop, x - v, ⟨hvm, K₂.sub_mem hx (h v.prop)⟩, add_sub_cancel _ _⟩

variable {K} in
/-- If `K` is complete, `K` and `Kᗮ` span the whole space. -/
theorem sup_orthogonal_of_completeSpace [K.HasOrthogonalProjection] : K ⊔ Kᗮ = ⊤ := by
  convert Submodule.sup_orthogonal_inf_of_completeSpace (le_top : K ≤ ⊤) using 2
  simp

/-- If `K` is complete, any `v` in `E` can be expressed as a sum of elements of `K` and `Kᗮ`. -/
theorem exists_add_mem_mem_orthogonal [K.HasOrthogonalProjection] (v : E) :
    ∃ y ∈ K, ∃ z ∈ Kᗮ, v = y + z :=
  ⟨K.orthogonalProjection v, Subtype.coe_prop _, v - K.orthogonalProjection v,
    sub_orthogonalProjection_mem_orthogonal _, by simp⟩

/-- If `K` admits an orthogonal projection, then the orthogonal complement of its orthogonal
complement is itself. -/
@[simp]
theorem orthogonal_orthogonal [K.HasOrthogonalProjection] : Kᗮᗮ = K := by
  ext v
  constructor
  · obtain ⟨y, hy, z, hz, rfl⟩ := K.exists_add_mem_mem_orthogonal v
    intro hv
    have hz' : z = 0 := by
      have hyz : ⟪z, y⟫ = 0 := by simp [hz y hy, inner_eq_zero_symm]
      simpa [inner_add_right, hyz] using hv z hz
    simp [hy, hz']
  · intro hv w hw
    rw [inner_eq_zero_symm]
    exact hw v hv

lemma orthogonal_le_orthogonal_iff {K₀ K₁ : Submodule 𝕜 E} [K₀.HasOrthogonalProjection]
    [K₁.HasOrthogonalProjection] : K₀ᗮ ≤ K₁ᗮ ↔ K₁ ≤ K₀ :=
  ⟨fun h ↦ by simpa using orthogonal_le h, orthogonal_le⟩

lemma orthogonal_le_iff_orthogonal_le {K₀ K₁ : Submodule 𝕜 E} [K₀.HasOrthogonalProjection]
    [K₁.HasOrthogonalProjection] : K₀ᗮ ≤ K₁ ↔ K₁ᗮ ≤ K₀ := by
  rw [← orthogonal_le_orthogonal_iff, orthogonal_orthogonal]

lemma le_orthogonal_iff_le_orthogonal {K₀ K₁ : Submodule 𝕜 E} [K₀.HasOrthogonalProjection]
    [K₁.HasOrthogonalProjection] : K₀ ≤ K₁ᗮ ↔ K₁ ≤ K₀ᗮ := by
  rw [← orthogonal_le_orthogonal_iff, orthogonal_orthogonal]

/-- In a Hilbert space, the orthogonal complement of the orthogonal complement of a subspace `K`
is the topological closure of `K`.

Note that the completeness assumption is necessary. Let `E` be the space `ℕ →₀ ℝ` with inner space
structure inherited from `PiLp 2 (fun _ : ℕ ↦ ℝ)`. Let `K` be the subspace of sequences with the sum
of all elements equal to zero. Then `Kᗮ = ⊥`, `Kᗮᗮ = ⊤`. -/
theorem orthogonal_orthogonal_eq_closure [CompleteSpace E] :
    Kᗮᗮ = K.topologicalClosure := by
  refine le_antisymm ?_ ?_
  · convert Submodule.orthogonal_orthogonal_monotone K.le_topologicalClosure using 1
    rw [K.topologicalClosure.orthogonal_orthogonal]
  · exact K.topologicalClosure_minimal K.le_orthogonal_orthogonal Kᗮ.isClosed_orthogonal

variable {K}

/-- If `K` admits an orthogonal projection, `K` and `Kᗮ` are complements of each other. -/
theorem isCompl_orthogonal_of_completeSpace [K.HasOrthogonalProjection] : IsCompl K Kᗮ :=
  ⟨K.orthogonal_disjoint, codisjoint_iff.2 Submodule.sup_orthogonal_of_completeSpace⟩

@[simp]
theorem orthogonalComplement_eq_orthogonalComplement {L : Submodule 𝕜 E} [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] : Kᗮ = Lᗮ ↔ K = L :=
  ⟨fun h ↦ by simpa using congr(Submodule.orthogonal $(h)),
    fun h ↦ congr(Submodule.orthogonal $(h))⟩

@[simp]
theorem orthogonal_eq_bot_iff [K.HasOrthogonalProjection] : Kᗮ = ⊥ ↔ K = ⊤ := by
  refine ⟨?_, fun h => by rw [h, Submodule.top_orthogonal_eq_bot]⟩
  intro h
  have : K ⊔ Kᗮ = ⊤ := Submodule.sup_orthogonal_of_completeSpace
  rwa [h, sup_comm, bot_sup_eq] at this

/-- The orthogonal projection onto `K` of an element of `Kᗮ` is zero. -/
theorem orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero [K.HasOrthogonalProjection]
    {v : E} (hv : v ∈ Kᗮ) : K.orthogonalProjection v = 0 := by
  ext
  convert eq_orthogonalProjection_of_mem_orthogonal (K := K) _ _ <;> simp [hv]

/-- The projection into `U` from an orthogonal submodule `V` is the zero map. -/
theorem IsOrtho.orthogonalProjection_comp_subtypeL {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (h : U ⟂ V) : U.orthogonalProjection ∘L V.subtypeL = 0 :=
  ContinuousLinearMap.ext fun v =>
    orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero <| h.symm v.prop

/-- The projection into `U` from `V` is the zero map if and only if `U` and `V` are orthogonal. -/
theorem orthogonalProjection_comp_subtypeL_eq_zero_iff {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] : U.orthogonalProjection ∘L V.subtypeL = 0 ↔ U ⟂ V :=
  ⟨fun h u hu v hv => by
    convert orthogonalProjection_inner_eq_zero v u hu using 2
    have : U.orthogonalProjection v = 0 := DFunLike.congr_fun h (⟨_, hv⟩ : V)
    rw [this, Submodule.coe_zero, sub_zero], Submodule.IsOrtho.orthogonalProjection_comp_subtypeL⟩

theorem orthogonalProjection_eq_linear_proj [K.HasOrthogonalProjection] (x : E) :
    K.orthogonalProjection x =
      K.linearProjOfIsCompl _ Submodule.isCompl_orthogonal_of_completeSpace x := by
  have : IsCompl K Kᗮ := Submodule.isCompl_orthogonal_of_completeSpace
  conv_lhs => rw [← Submodule.linear_proj_add_linearProjOfIsCompl_eq_self this x]
  rw [map_add, orthogonalProjection_mem_subspace_eq_self,
    orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero (Submodule.coe_mem _), add_zero]

theorem orthogonalProjection_coe_linearMap_eq_linearProj [K.HasOrthogonalProjection] :
    (K.orthogonalProjection : E →ₗ[𝕜] K) =
      K.linearProjOfIsCompl _ Submodule.isCompl_orthogonal_of_completeSpace :=
  LinearMap.ext <| orthogonalProjection_eq_linear_proj

/-- The reflection in `K` of an element of `Kᗮ` is its negation. -/
theorem reflection_mem_subspace_orthogonalComplement_eq_neg [K.HasOrthogonalProjection] {v : E}
    (hv : v ∈ Kᗮ) : K.reflection v = -v := by
  simp [reflection_apply, orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero hv]

/-- The orthogonal projection onto `Kᗮ` of an element of `K` is zero. -/
theorem orthogonalProjection_mem_subspace_orthogonal_precomplement_eq_zero
    [Kᗮ.HasOrthogonalProjection] {v : E} (hv : v ∈ K) : Kᗮ.orthogonalProjection v = 0 :=
  orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero (K.le_orthogonal_orthogonal hv)

/-- If `U ≤ V`, then projecting on `V` and then on `U` is the same as projecting on `U`. -/
theorem orthogonalProjection_orthogonalProjection_of_le {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U ≤ V) (x : E) :
    U.orthogonalProjection (V.orthogonalProjection x) = U.orthogonalProjection x :=
  Eq.symm <| by
    simpa only [sub_eq_zero, map_sub] using
      orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero
        (Submodule.orthogonal_le h (sub_orthogonalProjection_mem_orthogonal x))

/-- Given a monotone family `U` of complete submodules of `E` and a fixed `x : E`,
the orthogonal projection of `x` on `U i` tends to the orthogonal projection of `x` on
`(⨆ i, U i).topologicalClosure` along `atTop`. -/
theorem orthogonalProjection_tendsto_closure_iSup {ι : Type*} [Preorder ι]
    (U : ι → Submodule 𝕜 E) [∀ i, (U i).HasOrthogonalProjection]
    [(⨆ i, U i).topologicalClosure.HasOrthogonalProjection] (hU : Monotone U) (x : E) :
    Filter.Tendsto (fun i => ((U i).orthogonalProjection x : E)) atTop
      (𝓝 ((⨆ i, U i).topologicalClosure.orthogonalProjection x : E)) := by
  refine .of_neBot_imp fun h ↦ ?_
  cases atTop_neBot_iff.mp h
  let y := ((⨆ i, U i).topologicalClosure.orthogonalProjection x : E)
  have proj_x : ∀ i, (U i).orthogonalProjection x = (U i).orthogonalProjection y := fun i =>
    (orthogonalProjection_orthogonalProjection_of_le
        ((le_iSup U i).trans (iSup U).le_topologicalClosure) _).symm
  suffices ∀ ε > 0, ∃ I, ∀ i ≥ I, ‖((U i).orthogonalProjection y : E) - y‖ < ε by
    simpa only [proj_x, NormedAddCommGroup.tendsto_atTop] using this
  intro ε hε
  obtain ⟨a, ha, hay⟩ : ∃ a ∈ ⨆ i, U i, dist y a < ε := by
    have y_mem : y ∈ (⨆ i, U i).topologicalClosure := Submodule.coe_mem _
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at y_mem
    exact y_mem ε hε
  rw [dist_eq_norm] at hay
  obtain ⟨I, hI⟩ : ∃ I, a ∈ U I := by rwa [Submodule.mem_iSup_of_directed _ hU.directed_le] at ha
  refine ⟨I, fun i (hi : I ≤ i) => ?_⟩
  rw [norm_sub_rev, orthogonalProjection_minimal]
  refine lt_of_le_of_lt ?_ hay
  change _ ≤ ‖y - (⟨a, hU hi hI⟩ : U i)‖
  exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩ _

/-- Given a monotone family `U` of complete submodules of `E` with dense span supremum,
and a fixed `x : E`, the orthogonal projection of `x` on `U i` tends to `x` along `at_top`. -/
theorem orthogonalProjection_tendsto_self {ι : Type*} [Preorder ι]
    (U : ι → Submodule 𝕜 E) [∀ t, (U t).HasOrthogonalProjection] (hU : Monotone U) (x : E)
    (hU' : ⊤ ≤ (⨆ t, U t).topologicalClosure) :
    Filter.Tendsto (fun t => ((U t).orthogonalProjection x : E)) atTop (𝓝 x) := by
  have : (⨆ i, U i).topologicalClosure.HasOrthogonalProjection := by
    rw [top_unique hU']
    infer_instance
  convert orthogonalProjection_tendsto_closure_iSup U hU x
  rw [eq_comm, orthogonalProjection_eq_self_iff, top_unique hU']
  trivial

/-- The orthogonal complement satisfies `Kᗮᗮᗮ = Kᗮ`. -/
theorem triorthogonal_eq_orthogonal [CompleteSpace E] : Kᗮᗮᗮ = Kᗮ := by
  rw [Kᗮ.orthogonal_orthogonal_eq_closure]
  exact K.isClosed_orthogonal.submodule_topologicalClosure_eq

/-- The closure of `K` is the full space iff `Kᗮ` is trivial. -/
theorem topologicalClosure_eq_top_iff [CompleteSpace E] :
    K.topologicalClosure = ⊤ ↔ Kᗮ = ⊥ := by
  rw [← K.orthogonal_orthogonal_eq_closure]
  constructor <;> intro h
  · rw [← Submodule.triorthogonal_eq_orthogonal, h, Submodule.top_orthogonal_eq_bot]
  · rw [h, Submodule.bot_orthogonal_eq_top]

end Submodule

namespace Dense

/- TODO: Move to another file? -/
open Submodule

variable {K} {x y : E}

theorem eq_zero_of_inner_left (hK : Dense (K : Set E)) (h : ∀ v : K, ⟪x, v⟫ = 0) : x = 0 := by
  have : (⟪x, ·⟫) = 0 := (continuous_const.inner continuous_id).ext_on
    hK continuous_const (Subtype.forall.1 h)
  simpa using congr_fun this x

theorem eq_zero_of_mem_orthogonal (hK : Dense (K : Set E)) (h : x ∈ Kᗮ) : x = 0 :=
  eq_zero_of_inner_left hK fun v ↦ (mem_orthogonal' _ _).1 h _ v.2

/-- If `S` is dense and `x - y ∈ Kᗮ`, then `x = y`. -/
theorem eq_of_sub_mem_orthogonal (hK : Dense (K : Set E)) (h : x - y ∈ Kᗮ) : x = y :=
  sub_eq_zero.1 <| eq_zero_of_mem_orthogonal hK h

theorem eq_of_inner_left (hK : Dense (K : Set E)) (h : ∀ v : K, ⟪x, v⟫ = ⟪y, v⟫) : x = y :=
  hK.eq_of_sub_mem_orthogonal (Submodule.sub_mem_orthogonal_of_inner_left h)

theorem eq_of_inner_right (hK : Dense (K : Set E)) (h : ∀ v : K, ⟪(v : E), x⟫ = ⟪(v : E), y⟫) :
    x = y :=
  hK.eq_of_sub_mem_orthogonal (Submodule.sub_mem_orthogonal_of_inner_right h)

theorem eq_zero_of_inner_right (hK : Dense (K : Set E)) (h : ∀ v : K, ⟪(v : E), x⟫ = 0) : x = 0 :=
  hK.eq_of_inner_right fun v => by rw [inner_zero_right, h v]

end Dense

namespace Submodule

variable {K}

/-- The reflection in `Kᗮ` of an element of `K` is its negation. -/
theorem reflection_mem_subspace_orthogonal_precomplement_eq_neg [K.HasOrthogonalProjection] {v : E}
    (hv : v ∈ K) : Kᗮ.reflection v = -v :=
  reflection_mem_subspace_orthogonalComplement_eq_neg (K.le_orthogonal_orthogonal hv)

/-- The orthogonal projection onto `(𝕜 ∙ v)ᗮ` of `v` is zero. -/
theorem orthogonalProjection_orthogonalComplement_singleton_eq_zero (v : E) :
    (𝕜 ∙ v)ᗮ.orthogonalProjection v = 0 :=
  orthogonalProjection_mem_subspace_orthogonal_precomplement_eq_zero
    (Submodule.mem_span_singleton_self v)

/-- The reflection in `(𝕜 ∙ v)ᗮ` of `v` is `-v`. -/
theorem reflection_orthogonalComplement_singleton_eq_neg (v : E) : reflection (𝕜 ∙ v)ᗮ v = -v :=
  reflection_mem_subspace_orthogonal_precomplement_eq_neg (Submodule.mem_span_singleton_self v)

theorem reflection_sub {v w : F} (h : ‖v‖ = ‖w‖) : reflection (ℝ ∙ (v - w))ᗮ v = w := by
  set R : F ≃ₗᵢ[ℝ] F := reflection (ℝ ∙ v - w)ᗮ
  suffices R v + R v = w + w by
    apply smul_right_injective F (by norm_num : (2 : ℝ) ≠ 0)
    simpa [two_smul] using this
  have h₁ : R (v - w) = -(v - w) := reflection_orthogonalComplement_singleton_eq_neg (v - w)
  have h₂ : R (v + w) = v + w := by
    apply reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    rw [real_inner_add_sub_eq_zero_iff]
    exact h
  convert congr_arg₂ (· + ·) h₂ h₁ using 1
  · simp
  · abel

variable (K)

section FiniteDimensional

open Module

variable [FiniteDimensional 𝕜 K]

@[simp]
theorem topologicalClosure_eq_self : K.topologicalClosure = K :=
  K.closed_of_finiteDimensional.submodule_topologicalClosure_eq

@[simp]
theorem det_reflection : LinearMap.det K.reflection.toLinearMap = (-1) ^ finrank 𝕜 Kᗮ := by
  by_cases hK : FiniteDimensional 𝕜 Kᗮ
  swap
  · rw [finrank_of_infinite_dimensional hK, pow_zero, LinearMap.det_eq_one_of_finrank_eq_zero]
    exact finrank_of_infinite_dimensional fun h ↦ hK (h.finiteDimensional_submodule _)
  let e := K.prodEquivOfIsCompl _ K.isCompl_orthogonal_of_completeSpace
  let b := (finBasis 𝕜 K).prod (finBasis 𝕜 Kᗮ)
  have : LinearMap.toMatrix b b (e.symm ∘ₗ K.reflection.toLinearMap ∘ₗ e.symm.symm) =
      Matrix.fromBlocks 1 0 0 (-1) := by
    ext (_ | _) (_ | _) <;>
    simp [LinearMap.toMatrix_apply, b, Matrix.one_apply, Finsupp.single_apply, e, eq_comm,
      reflection_mem_subspace_eq_self, reflection_mem_subspace_orthogonalComplement_eq_neg]
  rw [← LinearMap.det_conj _ e.symm, ← LinearMap.det_toMatrix b, this, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, one_mul, Matrix.det_neg, Fintype.card_fin, Matrix.det_one, mul_one]

@[simp]
theorem linearEquiv_det_reflection : K.reflection.det = (-1) ^ finrank 𝕜 Kᗮ := by
  ext
  rw [LinearEquiv.coe_det, Units.val_pow_eq_pow_val]
  exact K.det_reflection

end FiniteDimensional

/-- If the orthogonal projection to `K` is well-defined, then a vector splits as the sum of its
orthogonal projections onto a complete submodule `K` and onto the orthogonal complement of `K`. -/
theorem orthogonalProjection_add_orthogonalProjection_orthogonal [K.HasOrthogonalProjection]
    (w : E) : (K.orthogonalProjection w : E) + (Kᗮ.orthogonalProjection w : E) = w := by
  simp

/-- The Pythagorean theorem, for an orthogonal projection. -/
theorem norm_sq_eq_add_norm_sq_projection (x : E) (S : Submodule 𝕜 E) [S.HasOrthogonalProjection] :
    ‖x‖ ^ 2 = ‖S.orthogonalProjection x‖ ^ 2 + ‖Sᗮ.orthogonalProjection x‖ ^ 2 :=
  calc
    ‖x‖ ^ 2 = ‖(S.orthogonalProjection x : E) + Sᗮ.orthogonalProjection x‖ ^ 2 := by
      rw [orthogonalProjection_add_orthogonalProjection_orthogonal]
    _ = ‖S.orthogonalProjection x‖ ^ 2 + ‖Sᗮ.orthogonalProjection x‖ ^ 2 := by
      simp only [sq]
      exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ <|
        (S.mem_orthogonal _).1 (Sᗮ.orthogonalProjection x).2 _ (S.orthogonalProjection x).2

/-- In a complete space `E`, the projection maps onto a complete subspace `K` and its orthogonal
complement sum to the identity. -/
theorem id_eq_sum_orthogonalProjection_self_orthogonalComplement [K.HasOrthogonalProjection] :
    ContinuousLinearMap.id 𝕜 E =
      K.subtypeL.comp K.orthogonalProjection + Kᗮ.subtypeL.comp Kᗮ.orthogonalProjection := by
  ext w
  exact (K.orthogonalProjection_add_orthogonalProjection_orthogonal w).symm

-- Porting note: The priority should be higher than `Submodule.coe_inner`.
@[simp high]
theorem inner_orthogonalProjection_eq_of_mem_right [K.HasOrthogonalProjection] (u : K) (v : E) :
    ⟪K.orthogonalProjection v, u⟫ = ⟪v, u⟫ :=
  calc
    ⟪K.orthogonalProjection v, u⟫ = ⟪(K.orthogonalProjection v : E), u⟫ := K.coe_inner _ _
    _ = ⟪(K.orthogonalProjection v : E), u⟫ + ⟪v - K.orthogonalProjection v, u⟫ := by
      rw [orthogonalProjection_inner_eq_zero _ _ (Submodule.coe_mem _), add_zero]
    _ = ⟪v, u⟫ := by rw [← inner_add_left, add_sub_cancel]

-- Porting note: The priority should be higher than `Submodule.coe_inner`.
@[simp high]
theorem inner_orthogonalProjection_eq_of_mem_left [K.HasOrthogonalProjection] (u : K) (v : E) :
    ⟪u, K.orthogonalProjection v⟫ = ⟪(u : E), v⟫ := by
  rw [← inner_conj_symm, ← inner_conj_symm (u : E), inner_orthogonalProjection_eq_of_mem_right]

/-- The orthogonal projection is self-adjoint. -/
theorem inner_orthogonalProjection_left_eq_right [K.HasOrthogonalProjection] (u v : E) :
    ⟪↑(K.orthogonalProjection u), v⟫ = ⟪u, K.orthogonalProjection v⟫ := by
  rw [← inner_orthogonalProjection_eq_of_mem_left, inner_orthogonalProjection_eq_of_mem_right]

/-- The orthogonal projection is symmetric. -/
theorem orthogonalProjection_isSymmetric [K.HasOrthogonalProjection] :
    (K.subtypeL ∘L K.orthogonalProjection : E →ₗ[𝕜] E).IsSymmetric :=
  inner_orthogonalProjection_left_eq_right K

lemma re_inner_orthogonalProjection_eq_normSq [K.HasOrthogonalProjection] (v : E) :
    re ⟪↑(K.orthogonalProjection v), v⟫ = ‖K.orthogonalProjection v‖^2 := by
  rw [re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    div_eq_iff (NeZero.ne' 2).symm, pow_two, add_sub_assoc, ← eq_sub_iff_add_eq', coe_norm,
    ← mul_sub_one, show (2 : ℝ) - 1 = 1 by ring, mul_one, sub_eq_iff_eq_add', norm_sub_rev]
  exact orthogonalProjectionFn_norm_sq K v

lemma re_inner_orthogonalProjection_nonneg [K.HasOrthogonalProjection] (v : E) :
    0 ≤ re ⟪↑(K.orthogonalProjection v), v⟫ := by
  rw [re_inner_orthogonalProjection_eq_normSq K v]
  exact sq_nonneg ‖K.orthogonalProjection v‖

open Module

/-- Given a finite-dimensional subspace `K₂`, and a subspace `K₁`
contained in it, the dimensions of `K₁` and the intersection of its
orthogonal subspace with `K₂` add to that of `K₂`. -/
theorem finrank_add_inf_finrank_orthogonal {K₁ K₂ : Submodule 𝕜 E}
    [FiniteDimensional 𝕜 K₂] (h : K₁ ≤ K₂) :
    finrank 𝕜 K₁ + finrank 𝕜 (K₁ᗮ ⊓ K₂ : Submodule 𝕜 E) = finrank 𝕜 K₂ := by
  haveI : FiniteDimensional 𝕜 K₁ := Submodule.finiteDimensional_of_le h
  haveI := FiniteDimensional.proper_rclike 𝕜 K₁
  have hd := Submodule.finrank_sup_add_finrank_inf_eq K₁ (K₁ᗮ ⊓ K₂)
  rw [← inf_assoc, (Submodule.orthogonal_disjoint K₁).eq_bot, bot_inf_eq, finrank_bot,
    Submodule.sup_orthogonal_inf_of_completeSpace h] at hd
  rw [add_zero] at hd
  exact hd.symm

/-- Given a finite-dimensional subspace `K₂`, and a subspace `K₁`
contained in it, the dimensions of `K₁` and the intersection of its
orthogonal subspace with `K₂` add to that of `K₂`. -/
theorem finrank_add_inf_finrank_orthogonal' {K₁ K₂ : Submodule 𝕜 E}
    [FiniteDimensional 𝕜 K₂] (h : K₁ ≤ K₂) {n : ℕ} (h_dim : finrank 𝕜 K₁ + n = finrank 𝕜 K₂) :
    finrank 𝕜 (K₁ᗮ ⊓ K₂ : Submodule 𝕜 E) = n := by
  rw [← add_right_inj (finrank 𝕜 K₁)]
  simp [Submodule.finrank_add_inf_finrank_orthogonal h, h_dim]

/-- Given a finite-dimensional space `E` and subspace `K`, the dimensions of `K` and `Kᗮ` add to
that of `E`. -/
theorem finrank_add_finrank_orthogonal [FiniteDimensional 𝕜 E] (K : Submodule 𝕜 E) :
    finrank 𝕜 K + finrank 𝕜 Kᗮ = finrank 𝕜 E := by
  convert Submodule.finrank_add_inf_finrank_orthogonal (le_top : K ≤ ⊤) using 1
  · rw [inf_top_eq]
  · simp

/-- Given a finite-dimensional space `E` and subspace `K`, the dimensions of `K` and `Kᗮ` add to
that of `E`. -/
theorem finrank_add_finrank_orthogonal' [FiniteDimensional 𝕜 E] {K : Submodule 𝕜 E}
    {n : ℕ} (h_dim : finrank 𝕜 K + n = finrank 𝕜 E) : finrank 𝕜 Kᗮ = n := by
  rw [← add_right_inj (finrank 𝕜 K)]
  simp [Submodule.finrank_add_finrank_orthogonal, h_dim]

/-- In a finite-dimensional inner product space, the dimension of the orthogonal complement of the
span of a nonzero vector is one less than the dimension of the space. -/
theorem finrank_orthogonal_span_singleton {n : ℕ} [_i : Fact (finrank 𝕜 E = n + 1)] {v : E}
    (hv : v ≠ 0) : finrank 𝕜 (𝕜 ∙ v)ᗮ = n := by
  haveI : FiniteDimensional 𝕜 E := .of_fact_finrank_eq_succ n
  exact finrank_add_finrank_orthogonal' <| by
    simp [finrank_span_singleton hv, _i.elim, add_comm]

end Submodule

open Module Submodule

/-- An element `φ` of the orthogonal group of `F` can be factored as a product of reflections, and
specifically at most as many reflections as the dimension of the complement of the fixed subspace
of `φ`. -/
theorem LinearIsometryEquiv.reflections_generate_dim_aux [FiniteDimensional ℝ F] {n : ℕ}
    (φ : F ≃ₗᵢ[ℝ] F) (hn : finrank ℝ (ker (ContinuousLinearMap.id ℝ F - φ))ᗮ ≤ n) :
    ∃ l : List F, l.length ≤ n ∧ φ = (l.map fun v => (ℝ ∙ v)ᗮ.reflection).prod := by
  -- We prove this by strong induction on `n`, the dimension of the orthogonal complement of the
  -- fixed subspace of the endomorphism `φ`
  induction' n with n IH generalizing φ
  · -- Base case: `n = 0`, the fixed subspace is the whole space, so `φ = id`
    refine ⟨[], rfl.le, show φ = 1 from ?_⟩
    have : ker (ContinuousLinearMap.id ℝ F - φ) = ⊤ := by
      rwa [le_zero_iff, finrank_eq_zero, orthogonal_eq_bot_iff] at hn
    symm
    ext x
    have := LinearMap.congr_fun (LinearMap.ker_eq_top.mp this) x
    simpa only [sub_eq_zero, ContinuousLinearMap.coe_sub, LinearMap.sub_apply,
      LinearMap.zero_apply] using this
  · -- Inductive step.  Let `W` be the fixed subspace of `φ`.  We suppose its complement to have
    -- dimension at most n + 1.
    let W := ker (ContinuousLinearMap.id ℝ F - φ)
    have hW : ∀ w ∈ W, φ w = w := fun w hw => (sub_eq_zero.mp hw).symm
    by_cases hn' : finrank ℝ Wᗮ ≤ n
    · obtain ⟨V, hV₁, hV₂⟩ := IH φ hn'
      exact ⟨V, hV₁.trans n.le_succ, hV₂⟩
    -- Take a nonzero element `v` of the orthogonal complement of `W`.
    haveI : Nontrivial Wᗮ := nontrivial_of_finrank_pos (by omega : 0 < finrank ℝ Wᗮ)
    obtain ⟨v, hv⟩ := exists_ne (0 : Wᗮ)
    have hφv : φ v ∈ Wᗮ := by
      intro w hw
      rw [← hW w hw, LinearIsometryEquiv.inner_map_map]
      exact v.prop w hw
    have hv' : (v : F) ∉ W := by
      intro h
      exact hv ((mem_left_iff_eq_zero_of_disjoint W.orthogonal_disjoint).mp h)
    -- Let `ρ` be the reflection in `v - φ v`; this is designed to swap `v` and `φ v`
    let x : F := v - φ v
    let ρ := (ℝ ∙ x)ᗮ.reflection
    -- Notation: Let `V` be the fixed subspace of `φ.trans ρ`
    let V := ker (ContinuousLinearMap.id ℝ F - φ.trans ρ)
    have hV : ∀ w, ρ (φ w) = w → w ∈ V := by
      intro w hw
      change w - ρ (φ w) = 0
      rw [sub_eq_zero, hw]
    -- Everything fixed by `φ` is fixed by `φ.trans ρ`
    have H₂V : W ≤ V := by
      intro w hw
      apply hV
      rw [hW w hw]
      refine reflection_mem_subspace_eq_self ?_
      rw [mem_orthogonal_singleton_iff_inner_left]
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
        finrank_lt_finrank_of_lt (SetLike.lt_iff_le_and_exists.2 ⟨H₂V, v, H₁V, hv'⟩)
      have : finrank ℝ V + finrank ℝ Vᗮ = finrank ℝ F := V.finrank_add_finrank_orthogonal
      have : finrank ℝ W + finrank ℝ Wᗮ = finrank ℝ F := W.finrank_add_finrank_orthogonal
      omega
    -- So apply the inductive hypothesis to `φ.trans ρ`
    obtain ⟨l, hl, hφl⟩ := IH (ρ * φ) this
    -- Prepend `ρ` to the factorization into reflections obtained for `φ.trans ρ`; this gives a
    -- factorization into reflections for `φ`.
    refine ⟨x::l, Nat.succ_le_succ hl, ?_⟩
    rw [List.map_cons, List.prod_cons]
    have := congr_arg (ρ * ·) hφl
    dsimp only at this
    rwa [← mul_assoc, reflection_mul_reflection, one_mul] at this

/-- The orthogonal group of `F` is generated by reflections; specifically each element `φ` of the
orthogonal group is a product of at most as many reflections as the dimension of `F`.

Special case of the **Cartan–Dieudonné theorem**. -/
theorem LinearIsometryEquiv.reflections_generate_dim [FiniteDimensional ℝ F] (φ : F ≃ₗᵢ[ℝ] F) :
    ∃ l : List F, l.length ≤ finrank ℝ F ∧ φ = (l.map fun v => reflection (ℝ ∙ v)ᗮ).prod :=
  let ⟨l, hl₁, hl₂⟩ := φ.reflections_generate_dim_aux le_rfl
  ⟨l, hl₁.trans (finrank_le _), hl₂⟩

/-- The orthogonal group of `F` is generated by reflections. -/
theorem LinearIsometryEquiv.reflections_generate [FiniteDimensional ℝ F] :
    Subgroup.closure (Set.range fun v : F => reflection (ℝ ∙ v)ᗮ) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro φ
  rcases φ.reflections_generate_dim with ⟨l, _, rfl⟩
  apply (Subgroup.closure _).list_prod_mem
  intro x hx
  rcases List.mem_map.mp hx with ⟨a, _, hax⟩
  exact Subgroup.subset_closure ⟨a, hax⟩

end Orthogonal

section OrthogonalFamily

open Submodule

variable {ι : Type*}

/-- An orthogonal family of subspaces of `E` satisfies `DirectSum.IsInternal` (that is,
they provide an internal direct sum decomposition of `E`) if and only if their span has trivial
orthogonal complement. -/
theorem OrthogonalFamily.isInternal_iff_of_isComplete [DecidableEq ι] {V : ι → Submodule 𝕜 E}
    (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ)
    (hc : IsComplete (↑(iSup V) : Set E)) : DirectSum.IsInternal V ↔ (iSup V)ᗮ = ⊥ := by
  haveI : CompleteSpace (↥(iSup V)) := hc.completeSpace_coe
  simp only [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top, hV.independent,
    true_and, orthogonal_eq_bot_iff]

/-- An orthogonal family of subspaces of `E` satisfies `DirectSum.IsInternal` (that is,
they provide an internal direct sum decomposition of `E`) if and only if their span has trivial
orthogonal complement. -/
theorem OrthogonalFamily.isInternal_iff [DecidableEq ι] [FiniteDimensional 𝕜 E]
    {V : ι → Submodule 𝕜 E} (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    DirectSum.IsInternal V ↔ (iSup V)ᗮ = ⊥ :=
  haveI h := FiniteDimensional.proper_rclike 𝕜 (↥(iSup V))
  hV.isInternal_iff_of_isComplete (completeSpace_coe_iff_isComplete.mp inferInstance)

open DirectSum

/-- If `x` lies within an orthogonal family `v`, it can be expressed as a sum of projections. -/
theorem OrthogonalFamily.sum_projection_of_mem_iSup [Fintype ι] {V : ι → Submodule 𝕜 E}
    [∀ i, CompleteSpace (V i)] (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ)
    (x : E) (hx : x ∈ iSup V) : (∑ i, ((V i).orthogonalProjection x : E)) = x := by
  induction hx using iSup_induction' with
  | mem i x hx =>
    refine
      (Finset.sum_eq_single_of_mem i (Finset.mem_univ _) fun j _ hij => ?_).trans
        (orthogonalProjection_eq_self_iff.mpr hx)
    rw [orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero, Submodule.coe_zero]
    exact hV.isOrtho hij.symm hx
  | zero =>
    simp_rw [map_zero, Submodule.coe_zero, Finset.sum_const_zero]
  | add x y _ _ hx hy =>
    simp_rw [map_add, Submodule.coe_add, Finset.sum_add_distrib]
    exact congr_arg₂ (· + ·) hx hy

/-- If a family of submodules is orthogonal, then the `orthogonalProjection` on a direct sum
is just the coefficient of that direct sum. -/
theorem OrthogonalFamily.projection_directSum_coeAddHom [DecidableEq ι] {V : ι → Submodule 𝕜 E}
    (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) (x : ⨁ i, V i) (i : ι)
    [CompleteSpace (V i)] :
    (V i).orthogonalProjection (DirectSum.coeAddMonoidHom V x) = x i := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j x =>
    simp_rw [DirectSum.coeAddMonoidHom_of, DirectSum.of]
    -- Porting note: was in the previous `simp_rw`, no longer works
    -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    erw [DFinsupp.singleAddHom_apply]
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [orthogonalProjection_mem_subspace_eq_self, DFinsupp.single_eq_same]
    · rw [orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero,
        DFinsupp.single_eq_of_ne hij.symm]
      exact hV.isOrtho hij.symm x.prop
  | add x y hx hy =>
    simp_rw [map_add]
    exact congr_arg₂ (· + ·) hx hy

/-- If a family of submodules is orthogonal and they span the whole space, then the orthogonal
projection provides a means to decompose the space into its submodules.

The projection function is `decompose V x i = (V i).orthogonalProjection x`.

See note [reducible non-instances]. -/
abbrev OrthogonalFamily.decomposition [DecidableEq ι] [Fintype ι] {V : ι → Submodule 𝕜 E}
    [∀ i, CompleteSpace (V i)] (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ)
    (h : iSup V = ⊤) : DirectSum.Decomposition V where
  decompose' x := DFinsupp.equivFunOnFintype.symm fun i => (V i).orthogonalProjection x
  left_inv x := by
    dsimp only
    letI := fun i => Classical.decEq (V i)
    rw [DirectSum.coeAddMonoidHom, DirectSum.toAddMonoid, DFinsupp.liftAddHom_apply]
    -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    erw [DFinsupp.sumAddHom_apply]; rw [DFinsupp.sum_eq_sum_fintype]
    · simp_rw [Equiv.apply_symm_apply, AddSubmonoidClass.coe_subtype]
      exact hV.sum_projection_of_mem_iSup _ ((h.ge :) Submodule.mem_top)
    · intro i
      exact map_zero _
  right_inv x := by
    dsimp only
    simp_rw [hV.projection_directSum_coeAddHom, DFinsupp.equivFunOnFintype_symm_coe]

end OrthogonalFamily

section OrthonormalBasis

variable {v : Set E}

open Module Submodule Set

/-- An orthonormal set in an `InnerProductSpace` is maximal, if and only if the orthogonal
complement of its span is empty. -/
theorem maximal_orthonormal_iff_orthogonalComplement_eq_bot (hv : Orthonormal 𝕜 ((↑) : v → E)) :
    (∀ u ⊇ v, Orthonormal 𝕜 ((↑) : u → E) → u = v) ↔ (span 𝕜 v)ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  constructor
  · contrapose!
    -- ** direction 1: nonempty orthogonal complement implies nonmaximal
    rintro ⟨x, hx', hx⟩
    -- take a nonzero vector and normalize it
    let e := (‖x‖⁻¹ : 𝕜) • x
    have he : ‖e‖ = 1 := by simp [e, norm_smul_inv_norm hx]
    have he' : e ∈ (span 𝕜 v)ᗮ := smul_mem' _ _ hx'
    have he'' : e ∉ v := by
      intro hev
      have : e = 0 := by
        have : e ∈ span 𝕜 v ⊓ (span 𝕜 v)ᗮ := ⟨subset_span hev, he'⟩
        simpa [(span 𝕜 v).inf_orthogonal_eq_bot] using this
      have : e ≠ 0 := hv.ne_zero ⟨e, hev⟩
      contradiction
    -- put this together with `v` to provide a candidate orthonormal basis for the whole space
    refine ⟨insert e v, v.subset_insert e, ⟨?_, ?_⟩, (ne_insert_of_notMem v he'').symm⟩
    · -- show that the elements of `insert e v` have unit length
      rintro ⟨a, ha'⟩
      rcases eq_or_mem_of_mem_insert ha' with ha | ha
      · simp [ha, he]
      · exact hv.1 ⟨a, ha⟩
    · -- show that the elements of `insert e v` are orthogonal
      have h_end : ∀ a ∈ v, ⟪a, e⟫ = 0 := by
        intro a ha
        exact he' a (Submodule.subset_span ha)
      rintro ⟨a, ha'⟩
      rcases eq_or_mem_of_mem_insert ha' with ha | ha
      · rintro ⟨b, hb'⟩ hab'
        have hb : b ∈ v := by
          refine mem_of_mem_insert_of_ne hb' ?_
          intro hbe'
          apply hab'
          simp [ha, hbe']
        rw [inner_eq_zero_symm]
        simpa [ha] using h_end b hb
      rintro ⟨b, hb'⟩ hab'
      rcases eq_or_mem_of_mem_insert hb' with hb | hb
      · simpa [hb] using h_end a ha
      have : (⟨a, ha⟩ : v) ≠ ⟨b, hb⟩ := by
        intro hab''
        apply hab'
        simpa using hab''
      exact hv.2 this
  · -- ** direction 2: empty orthogonal complement implies maximal
    simp only [Subset.antisymm_iff]
    rintro h u (huv : v ⊆ u) hu
    refine ⟨?_, huv⟩
    intro x hxu
    refine ((mt (h x)) (hu.ne_zero ⟨x, hxu⟩)).imp_symm ?_
    intro hxv y hy
    have hxv' : (⟨x, hxu⟩ : u) ∉ ((↑) ⁻¹' v : Set u) := by simp [huv, hxv]
    obtain ⟨l, hl, rfl⟩ :
      ∃ l ∈ supported 𝕜 𝕜 ((↑) ⁻¹' v : Set u), (linearCombination 𝕜 ((↑) : u → E)) l = y := by
      rw [← Finsupp.mem_span_image_iff_linearCombination]
      simp [huv, inter_eq_self_of_subset_right, hy]
    exact hu.inner_finsupp_eq_zero hxv' hl

variable [FiniteDimensional 𝕜 E]

/-- An orthonormal set in a finite-dimensional `InnerProductSpace` is maximal, if and only if it
is a basis. -/
theorem maximal_orthonormal_iff_basis_of_finiteDimensional (hv : Orthonormal 𝕜 ((↑) : v → E)) :
    (∀ u ⊇ v, Orthonormal 𝕜 ((↑) : u → E) → u = v) ↔ ∃ b : Basis v 𝕜 E, ⇑b = ((↑) : v → E) := by
  haveI := FiniteDimensional.proper_rclike 𝕜 (span 𝕜 v)
  rw [maximal_orthonormal_iff_orthogonalComplement_eq_bot hv]
  rw [Submodule.orthogonal_eq_bot_iff]
  have hv_coe : range ((↑) : v → E) = v := by simp
  constructor
  · refine fun h => ⟨Basis.mk hv.linearIndependent _, Basis.coe_mk _ ?_⟩
    convert h.ge
  · rintro ⟨h, coe_h⟩
    rw [← h.span_eq, coe_h, hv_coe]

end OrthonormalBasis
