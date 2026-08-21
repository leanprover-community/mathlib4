/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Riccardo Brasca, Xavier Roblot
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Dirichlet density of a set of prime ideals

Let `K` be a number field. Given a set `S` of nonzero prime ideals of `𝓞 K`, its Dirichlet
density is
$$
\delta(S) = \lim_{s \to 1^+}
  \frac{\sum_{\mathfrak p \in S} \operatorname{N} \mathfrak p^{-s}}
    {\sum_{\mathfrak p} \operatorname{N} \mathfrak p^{-s}},
$$
when this limit exists. The sum in the denominator runs over all nonzero prime ideals of `𝓞 K`.

This is captured by the predicate `HasDirichletDensity S δ`, stating that the ratio tends to `δ`,
and by the definition `dirichletDensity S`, the density as a real number (with junk value `0` when
it does not exist).

## Main results

* `NumberField.primeIdealZetaSum_le_card_of_finite` — for a finite `S`, the partial sum is bounded
  above by the number of elements of `S`.
* `NumberField.hasDirichletDensity_empty` — the empty set has Dirichlet density `0`.
* `NumberField.dirichletDensity_nonneg` — the Dirichlet density is nonnegative.
* `NumberField.dirichletDensity_le_one` — the Dirichlet density is at most `1`.

-/

public section

noncomputable section

open Filter IsDedekindDomain Set

open scoped Topology

namespace NumberField.Set

open NumberField

variable {K : Type*} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The partial Dirichlet series $\sum_{\mathfrak p \in S} \operatorname{N} \mathfrak p^{-s}$. -/
def primeIdealZetaSum (S : Set (HeightOneSpectrum (𝓞 K))) (s : ℝ) : ℝ :=
  ∑' 𝔭 : S, (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)

theorem primeIdealZetaSum_def (s : ℝ) :
    S.primeIdealZetaSum s = ∑' 𝔭 : S, (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) := by rfl

theorem primeIdealZetaSum_nonneg (s : ℝ) :
    0 ≤ S.primeIdealZetaSum s :=
  tsum_nonneg fun _ ↦ by positivity

variable {S} in
/-- For a finite set `S` of prime ideals, the partial sum
$\sum_{\mathfrak p \in S} \operatorname{N} \mathfrak p^{-s}$ is bounded above by the number of
elements of `S`. -/
theorem primeIdealZetaSum_le_card_of_finite (hS : S.Finite) {s : ℝ} (hs : 0 ≤ s) :
    S.primeIdealZetaSum s ≤ S.ncard := by
  replace hS := hS.to_subtype
  grw [primeIdealZetaSum_def, Real.rpow_le_one_of_one_le_of_nonpos] <;>
  simp [Summable.of_finite, Nat.one_le_iff_ne_zero,
    Ideal.absNorm_eq_zero_iff, hs, HeightOneSpectrum.ne_bot]

/-- `S` has Dirichlet density `δ` when the ratio of the partial sum over `S` to the sum over all
nonzero prime ideals,
$$
\frac{\sum_{\mathfrak p \in S} \operatorname{N} \mathfrak p^{-s}}
  {\sum_{\mathfrak p} \operatorname{N} \mathfrak p^{-s}},
$$
tends to `δ` as $s \to 1^+$. -/
def HasDirichletDensity (δ : ℝ) : Prop :=
  Tendsto (fun s : ℝ ↦ S.primeIdealZetaSum s /
    primeIdealZetaSum (univ : Set (HeightOneSpectrum (𝓞 K))) s) (𝓝[>] 1) (𝓝 δ)

open scoped Classical in
/-- The Dirichlet density of `S` as a real number, taking the junk value `0` when `S` has no
density. As with `tsum`, this value only has content when `S` has a density; the genuine statement
that `S` has density `0` is `HasDirichletDensity S 0`. -/
def dirichletDensity : ℝ :=
  if h : ∃ δ, S.HasDirichletDensity δ then h.choose else 0

variable {S}

/-- If `S` has no Dirichlet density, then `dirichletDensity S = 0`. -/
theorem dirichletDensity_eq_zero_of_not_hasDirichletDensity
    (h : ∀ δ, ¬ S.HasDirichletDensity δ) : S.dirichletDensity = 0 := by
  rw [dirichletDensity, dite_eq_right (not_exists.mpr h)]

/-- If `S` has Dirichlet density `δ`, then `dirichletDensity S = δ`. -/
theorem HasDirichletDensity.dirichletDensity_eq {δ : ℝ} (h : S.HasDirichletDensity δ) :
    S.dirichletDensity = δ := by
  rw [dirichletDensity, dite_eq_left ⟨δ, h⟩, tendsto_nhds_unique (Exists.choose_spec ⟨δ, h⟩) h]

/-- The empty set has Dirichlet density `0`. -/
theorem hasDirichletDensity_empty :
    HasDirichletDensity (∅ : Set (HeightOneSpectrum (𝓞 K))) 0 := by
  simp [HasDirichletDensity, primeIdealZetaSum_def]

/-- The Dirichlet density of the empty set is `0`. -/
@[simp]
theorem dirichletDensity_empty :
    dirichletDensity (∅ : Set (HeightOneSpectrum (𝓞 K))) = 0 :=
  hasDirichletDensity_empty.dirichletDensity_eq

/-- The Dirichlet density is nonnegative. -/
theorem HasDirichletDensity.nonneg {δ : ℝ} (h : S.HasDirichletDensity δ) :
    0 ≤ δ :=
  ge_of_tendsto h <| Eventually.of_forall fun s ↦
    div_nonneg (S.primeIdealZetaSum_nonneg s) (univ.primeIdealZetaSum_nonneg s)

variable (S) in
/-- The Dirichlet density of `S` is nonnegative. -/
theorem dirichletDensity_nonneg : 0 ≤ S.dirichletDensity := by
  rw [dirichletDensity]
  split_ifs with h
  · exact h.choose_spec.nonneg
  · exact le_rfl

/-- The Dirichlet density is at most `1`. -/
theorem HasDirichletDensity.le_one {δ : ℝ} (h : S.HasDirichletDensity δ) :
    δ ≤ 1 := by
  refine le_of_tendsto h (Eventually.of_forall fun s ↦ ?_)
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def,
    tsum_univ fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (𝔭.asIdeal.absNorm : ℝ) ^ (-s)]
  by_cases hs : Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (𝔭.asIdeal.absNorm : ℝ) ^ (-s)
  · exact div_le_one_of_le₀ (hs.tsum_subtype_le _ S (fun _ ↦ by positivity))
      (tsum_nonneg fun _ ↦ by positivity)
  · grw [tsum_eq_zero_of_not_summable hs, div_zero, zero_le_one]

variable (S) in
/-- The Dirichlet density of `S` is at most `1`. -/
theorem dirichletDensity_le_one : S.dirichletDensity ≤ 1 := by
  rw [dirichletDensity]
  split_ifs with h
  · exact h.choose_spec.le_one
  · exact zero_le_one

end NumberField.Set
