/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
public import Mathlib.NumberTheory.LSeries.RiemannZeta

import Mathlib.Algebra.BigOperators.Ring.Nat

/-!
# The Dedekind zeta function of a number field

In this file, we define and prove results about the Dedekind zeta function of a number field.

## Main definitions and results

* `NumberField.dedekindZeta`: the Dedekind zeta function.
* `NumberField.dedekindZeta_residue`: the value of the residue at `s = 1` of the Dedekind
  zeta function.
* `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`: **Dirichlet class number formula**
  computation of the residue of the Dedekind zeta function at `s = 1`, see Chap. 7 of
  [D. Marcus, *Number Fields*][marcus1977number]

## TODO

Generalize the construction of the Dedekind zeta function.
-/

@[expose] public section

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

open Filter Ideal NumberField.InfinitePlace NumberField.Units nonZeroDivisors

open scoped Topology

namespace NumberField

open scoped Real

/--
The Dedekind zeta function of a number field. It is defined as the `L`-series with coefficients
the number of integral ideals of norm `n`.
-/
def dedekindZeta (s : ℂ) :=
  LSeries (fun n ↦ Nat.card {I : Ideal (𝓞 K) // absNorm I = n}) s

/--
The value of the residue at `s = 1` of the Dedekind zeta function, see
`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`.
-/
def dedekindZeta_residue : ℝ :=
  (2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K * classNumber K) /
    (torsionOrder K * Real.sqrt |discr K|)

theorem dedekindZeta_residue_def :
    dedekindZeta_residue K =
      (2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K * classNumber K) /
      (torsionOrder K * Real.sqrt |discr K|) := rfl

theorem dedekindZeta_residue_pos : 0 < dedekindZeta_residue K := by
  refine div_pos ?_ ?_
  · exact mul_pos (mul_pos (by positivity) (regulator_pos K)) (Nat.cast_pos.mpr (classNumber_pos K))
  · exact mul_pos (Nat.cast_pos.mpr (torsionOrder_pos K)) <|
      Real.sqrt_pos_of_pos <| abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))

theorem dedekindZeta_residue_ne_zero : dedekindZeta_residue K ≠ 0 :=
  (dedekindZeta_residue_pos K).ne'

/--
**Dirichlet class number formula**
-/
theorem tendsto_sub_one_mul_dedekindZeta_nhdsGT :
    Tendsto (fun s : ℝ ↦ (s - 1) * dedekindZeta K s) (𝓝[>] 1) (𝓝 (dedekindZeta_residue K)) := by
  refine LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg _ ?_
    (fun _ ↦ Nat.cast_nonneg _)
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by simp,
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq
      (fun k _ ↦ Ring.HasFiniteQuotients.finite_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

/-! ### The rational specialization -/

section Rat

/-- The ring of integers of `ℚ` is free of rank one over `ℤ`, transported along the
canonical ring equivalence `Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ`. -/
theorem finrank_ringOfIntegersQ : Module.finrank ℤ (𝓞 ℚ) = 1 := by
  have hb : Module.Basis (Fin 1) ℤ (𝓞 ℚ) :=
    Module.Basis.map (Module.Basis.singleton (Fin 1) ℤ)
      Rat.ringOfIntegersEquiv.toAddEquiv.toIntLinearEquiv.symm
  rw [Module.finrank_eq_card_basis hb]
  simp

/-- The absolute norm of an ideal is invariant under precomposition with a ring
equivalence of Dedekind domains: the norm is the index of the underlying additive
subgroup, and indices are transported along group equivalences. -/
theorem absNorm_comap_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain R] [Infinite R] [IsDedekindDomain S] [Infinite S] (e : R ≃+* S)
    (J : Ideal S) : absNorm (Ideal.comap (e : R →+* S) J) = absNorm J := by
  have hbridge : (Ideal.comap (e : R →+* S) J).toAddSubgroup
      = J.toAddSubgroup.comap (e.toAddEquiv : R →+ S) := by
    ext x
    exact Iff.rfl
  have hindex : (J.toAddSubgroup.comap (e.toAddEquiv : R →+ S)).index = J.toAddSubgroup.index := by
    have himg : (J.toAddSubgroup.comap (e.toAddEquiv : R →+ S)).map
        (e.toAddEquiv : R →+ S) = J.toAddSubgroup := by
      ext x
      constructor
      · rintro ⟨y, hy, hyx⟩
        have hy' : (e.toAddEquiv : R →+ S) y ∈ J.toAddSubgroup := hy
        rw [hyx] at hy'
        exact hy'
      · intro hx
        have hmem : (e.toAddEquiv) ((e.toAddEquiv).symm x) ∈ J.toAddSubgroup := by
          rw [(e.toAddEquiv).apply_symm_apply]
          exact hx
        exact ⟨(e.toAddEquiv).symm x, hmem, (e.toAddEquiv).apply_symm_apply x⟩
    rw [← AddSubgroup.index_map_equiv _ e.toAddEquiv, himg]
  rw [Ideal.absNorm_eq_index, Ideal.absNorm_eq_index, hbridge, hindex]

/-- The specialization face of the rational Dedekind zeta: every norm level carries
exactly one integral ideal of `𝓞 ℚ`.  Uniqueness transports the two ideals to `ℤ`
along `Rat.ringOfIntegersEquiv`, where an ideal is spanned by its own norm
(argument following google-deepmind/formal-conjectures#3931). -/
theorem dedekindZetaCoeffRat_eq_one (n : ℕ) :
    Nat.card {I : Ideal (𝓞 ℚ) // absNorm I = n} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => ?_⟩, ⟨⟨Ideal.span {(n : 𝓞 ℚ)}, ?_⟩⟩⟩
  · have hcomm : ∀ I : Ideal (𝓞 ℚ),
        Ideal.comap ((Rat.ringOfIntegersEquiv.symm : ℤ ≃+* 𝓞 ℚ) : ℤ →+* 𝓞 ℚ) I
        = Ideal.span {(absNorm I : ℤ)} := by
      intro I
      rw [← Int.ideal_span_absNorm_eq_self
        (Ideal.comap ((Rat.ringOfIntegersEquiv.symm : ℤ ≃+* 𝓞 ℚ) : ℤ →+* 𝓞 ℚ) I),
        absNorm_comap_ringEquiv]
    exact Subtype.ext (by
      rw [← Ideal.map_comap_of_surjective
        ((Rat.ringOfIntegersEquiv.symm : ℤ ≃+* 𝓞 ℚ) : ℤ →+* 𝓞 ℚ)
        Rat.ringOfIntegersEquiv.symm.surjective ↑a,
        ← Ideal.map_comap_of_surjective
        ((Rat.ringOfIntegersEquiv.symm : ℤ ≃+* 𝓞 ℚ) : ℤ →+* 𝓞 ℚ)
        Rat.ringOfIntegersEquiv.symm.surjective ↑b,
        hcomm ↑a, hcomm ↑b, a.2, b.2])
  · rw [Ideal.absNorm_span_natCast, finrank_ringOfIntegersQ, pow_one]

/-- **The series identity bridge.**  On the convergence half-plane `1 < re s`, the
Dedekind zeta function of `ℚ` agrees with the Riemann zeta function.  The hypothesis
`1 < re s` is necessary: the defining `L`-series of `dedekindZeta ℚ` diverges outside it
and takes the junk value `0`, while `riemannZeta` is the analytic continuation
(for instance `riemannZeta 0 = -1 / 2`); see `dedekindZeta_rat_zero_ne_riemannZeta_zero`
below.

The `Z`-side transport in the proof follows an argument due to wwylele
(google-deepmind/formal-conjectures#3931). -/
theorem dedekindZeta_rat_eq_riemannZeta (s : ℂ) (hs : 1 < s.re) :
    dedekindZeta ℚ s = riemannZeta s := by
  have hcoeff : dedekindZeta ℚ s = LSeries (fun _ : ℕ => (1 : ℂ)) s := by
    refine LSeries_congr ?_ s
    intro n _
    simpa using congrArg (fun k : ℕ => (k : ℂ)) (dedekindZetaCoeffRat_eq_one n)
  have hone : LSeries (fun _ : ℕ => (1 : ℂ)) s = ∑' n : ℕ, 1 / (n : ℂ) ^ s := by
    rw [LSeries]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · rw [LSeries.term_zero]
      simp [Complex.zero_cpow (Complex.ne_zero_of_one_lt_re hs)]
    · rw [LSeries.term_of_ne_zero hn]
  rw [hcoeff, hone, zeta_eq_tsum_one_div_nat_cpow hs]

/-- Junk-value face: at `s = 0` the defining series of `dedekindZeta ℚ` diverges (its
terms are eventually the constant `1`), so the `L`-series takes the junk value `0`. -/
theorem dedekindZeta_rat_zero : dedekindZeta ℚ 0 = 0 := by
  show LSeries (fun n ↦ Nat.card {I : Ideal (𝓞 ℚ) // absNorm I = n}) 0 = 0
  apply LSeries.eq_zero_of_not_LSeriesSummable
  intro hsum
  have hterm : ∀ m : ℕ, 1 ≤ m →
      LSeries.term (fun n ↦ Nat.card {I : Ideal (𝓞 ℚ) // absNorm I = n}) 0 m = (1 : ℂ) := by
    intro m hm
    rw [LSeries.term_of_ne_zero (by omega)]
    have h1 : Nat.card {I : Ideal (𝓞 ℚ) // absNorm I = m} = 1 :=
      dedekindZetaCoeffRat_eq_one m
    simp [h1, Complex.cpow_zero]
  have ht : Filter.Tendsto
      (LSeries.term (fun n ↦ Nat.card {I : Ideal (𝓞 ℚ) // absNorm I = n}) 0)
      Filter.atTop (nhds (1 : ℂ)) :=
    tendsto_nhds_of_eventually_eq
      (by rw [Filter.eventually_atTop]; exact ⟨1, fun m hm => hterm m hm⟩)
  have hconst : Filter.Tendsto
      (LSeries.term (fun n ↦ Nat.card {I : Ideal (𝓞 ℚ) // absNorm I = n}) 0)
      Filter.atTop (nhds 0) :=
    hsum.tendsto_atTop_zero
  exact absurd (tendsto_nhds_unique ht hconst) (by norm_num)

/-- The series identity does **not** extend to `s = 0`, where the two sides take the
values `0` and `-1 / 2` respectively. -/
theorem dedekindZeta_rat_zero_ne_riemannZeta_zero :
    dedekindZeta ℚ 0 ≠ riemannZeta 0 := by
  rw [dedekindZeta_rat_zero, riemannZeta_zero]
  norm_num

end Rat

end NumberField
