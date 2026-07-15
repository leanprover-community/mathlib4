/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Riccardo Brasca, Xavier Roblot
-/
module

public import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# Dirichlet density of a set of prime ideals

For a number field `K`, the Dirichlet density of a set `S` of prime ideals of `𝓞 K` is, when it
exists,

  δ(S) = lim_{s → 1⁺} ( Σ_{𝔭 ∈ S} N𝔭^{-s} ) / ( Σ_𝔭 N𝔭^{-s} ),

with both sums running over nonzero prime ideals. The denominator is asymptotic to
`log (s - 1)⁻¹` as `s ↓ 1`.

## Main definitions

* `NumberField.primeIdealZetaSum` — the partial Dirichlet series `Σ_{𝔭 ∈ S} N𝔭^{-s}`.
* `NumberField.HasDirichletDensity` — `S` has Dirichlet density `δ`.
* `NumberField.HasUpperDirichletDensity`, `NumberField.HasLowerDirichletDensity` — the `limsup` /
  `liminf` variants of the density.

## Main results

* `NumberField.hasDirichletDensity_empty` — the empty set has Dirichlet density `0`.
* `NumberField.logDedekindZeta_sub_log_inv_sub_one_bounded` — `log ζ_K(s)` and `log (1 / (s - 1))`
  differ by a bounded amount as `s ↓ 1`.
* `NumberField.primeIdealZetaSum_le_card_of_finite` — for a finite `S`, the partial sum is bounded
  above by the number of qualifying primes.

-/

@[expose] public section

noncomputable section

open Filter Topology Set

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {S : Set (Ideal (𝓞 K))} {δ : ℝ}

/-- The partial Dirichlet series `∑_{𝔭 ∈ S} N𝔭 ^ (-s)`, summed over the nonzero prime ideals
of `𝓞 K` lying in `S`. -/
def primeIdealZetaSum (S : Set (Ideal (𝓞 K))) (s : ℝ) : ℝ :=
  ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)

theorem primeIdealZetaSum_def (S : Set (Ideal (𝓞 K))) (s : ℝ) :
    primeIdealZetaSum S s = ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
    (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := rfl

/-- The Dirichlet density of a set `S` of prime ideals of `𝓞 K` is `δ` when the ratio of partial
sums tends to `δ` as `s ↓ 1`. -/
def HasDirichletDensity (S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop :=
  Tendsto (fun s : ℝ ↦ primeIdealZetaSum S s / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s)
    (𝓝[>] 1) (𝓝 δ)

/-- Upper Dirichlet density, defined as the`limsup` of the ratio. -/
def HasUpperDirichletDensity (S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop :=
  limsup (fun s : ℝ ↦ primeIdealZetaSum S s / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s)
    (𝓝[>] 1) = δ

/-- Lower Dirichlet density, defined as the `liminf` of the ratio. -/
def HasLowerDirichletDensity (S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop :=
  liminf (fun s : ℝ ↦ primeIdealZetaSum S s / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s)
    (𝓝[>] 1) = δ

/-- The Dirichlet density of the empty set is `0`. -/
theorem hasDirichletDensity_empty : HasDirichletDensity (∅ : Set (Ideal (𝓞 K))) 0 := by
  have : IsEmpty {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ (∅ : Set (Ideal (𝓞 K))) ∧
      𝔭.IsPrime ∧ 𝔭 ≠ ⊥} := ⟨fun x ↦ x.2.1⟩
  simp [HasDirichletDensity, primeIdealZetaSum_def]

theorem HasDirichletDensity.hasUpper (h : HasDirichletDensity S δ) :
    HasUpperDirichletDensity S δ :=
  h.limsup_eq

theorem HasDirichletDensity.hasLower (h : HasDirichletDensity S δ) :
    HasLowerDirichletDensity S δ :=
  h.liminf_eq

variable (K)

theorem logDedekindZeta_sub_log_inv_sub_one_bounded : ∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[>] (1 : ℝ),
    |Real.log (dedekindZeta K (s : ℂ)).re - Real.log (1 / (s - 1))| ≤ C := by
  set r := dedekindZeta_residue K
  have hrpos : 0 < r := dedekindZeta_residue_pos K
  have hF : Tendsto (fun s : ℝ ↦ (s - 1) * (dedekindZeta K (s : ℂ)).re) (𝓝[>] (1 : ℝ)) (𝓝 r) := by
    refine ((Complex.continuous_re.tendsto _).comp
      (tendsto_sub_one_mul_dedekindZeta_nhdsGT K)).congr fun s ↦ ?_
    rw [Function.comp_apply, show ((s : ℂ) - 1) = ((s - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul]
  refine ⟨max |Real.log (r / 2)| |Real.log (2 * r)|, ?_⟩
  have hev : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), (s - 1) * (dedekindZeta K (s : ℂ)).re ∈
    Ioo (r / 2) (2 * r) := hF.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  filter_upwards [hev, self_mem_nhdsWithin] with s hF_s hs1
  simp only [mem_Ioi] at hs1
  have hsm1 : (0 : ℝ) < s - 1 := by linarith
  obtain ⟨hlo, hhi⟩ := hF_s
  have hFpos : (0 : ℝ) < (s - 1) * (dedekindZeta K (s : ℂ)).re := by linarith
  have hζpos : (0 : ℝ) < (dedekindZeta K (s : ℂ)).re := (mul_pos_iff_of_pos_left hsm1).mp hFpos
  rw [one_div, Real.log_inv, sub_neg_eq_add,
    ← Real.log_mul (ne_of_gt hζpos) (ne_of_gt hsm1), mul_comm]
  exact abs_le_max_abs_abs (Real.log_lt_log (by linarith) hlo).le (Real.log_lt_log hFpos hhi).le

variable {K}

theorem primeIdealZetaSum_le_card_of_finite (hS : S.Finite) {s : ℝ} (hs : 0 < s) :
    primeIdealZetaSum S s ≤ Nat.card {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} := by
  have : Finite {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
    (hS.subset fun _ hx ↦ hx.1).to_subtype
  let : Fintype {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} := Fintype.ofFinite _
  rw [primeIdealZetaSum_def, tsum_fintype, Nat.card_eq_fintype_card]
  calc ∑ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)
      ≤ ∑ _𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, 1 := by
        refine Finset.sum_le_sum fun 𝔭 _ ↦ Real.rpow_le_one_of_one_le_of_nonpos ?_ (by linarith)
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact 𝔭.2.2.2)
    _ = Fintype.card {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

end NumberField
