/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Valuation.RankOne
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

/-!
# p-adic numbers with a valuative relation

The instance `IsNonarchimedeanLocalField ℚ_[p]`, which builds on the instances constructed here,
can be found in `Mathlib/NumberTheory/Padics/LocalField.lean`.

## Tags

p-adic, p adic, padic, norm, valuation, cauchy, completion, p-adic completion
-/

public section

variable {p : ℕ} [hp : Fact p.Prime] {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
    (v : Valuation ℚ_[p] Γ₀)

open ValuativeRel WithZero Valuation MonoidWithZeroHom.ValueGroup₀

namespace Padic

-- TODO: should this be automatic from a nonarchimedean nontrivially normed field?
noncomputable instance : ValuativeRel ℚ_[p] := .ofValuation mulValuation

instance : Valuation.Compatible (mulValuation (p := p)) := .ofValuation _

variable [v.Compatible]

lemma valuation_p_ne_zero : v p ≠ 0 := by
  simp [(isEquiv v (Padic.mulValuation)).eq_zero, hp.out.ne_zero]

@[simp]
lemma valuation_p_lt_one : v p < 1 := by
  simp [(isEquiv v (Padic.mulValuation)).lt_one_iff_lt_one, hp.out.ne_zero]

instance : IsNontrivial ℚ_[p] where
  condition := ⟨ValuativeRel.valuation _ p, valuation_p_ne_zero _, (valuation_p_lt_one _).ne⟩

instance : IsRankLeOne ℚ_[p] := .of_compatible_mulArchimedean mulValuation

instance : IsValuativeTopology ℚ_[p] := by
  refine IsValuativeTopology.of_mem_nhds_zero_iff_vle (mulValuation (p := p)) fun {s} ↦ ?_
  rw [Metric.mem_nhds_iff]
  have h1p : (1 : ℝ) < p := mod_cast hp.out.one_lt
  constructor
  · -- A metric ball `‖·‖ < ε` contains the valuation ball of radius `v (p ^ n)` for large `n`.
    intro ⟨ε, hε, hball⟩
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ h1p)
    have hnorm : ‖(p : ℚ_[p]) ^ n‖ < ε := by simpa [norm_pow, norm_p] using hn
    refine ⟨Units.mk0 (mulValuation.restrict (p ^ n)) ?_,
      fun z hz ↦ hball (mem_ball_zero_iff.mpr ?_)⟩
    · exact (ne_zero_iff _).mpr (pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero))
    simp only [Set.mem_ofPred_eq, Units.val_mk0, restrict_lt_iff] at hz
    exact (norm_lt_norm_iff_mulValuation_lt.mpr hz).trans hnorm
  · -- Conversely, a valuation ball `v · < γ` is the metric ball of radius `p ^ log γ`.
    intro ⟨γ, hγ⟩
    refine ⟨p ^ log (embedding γ.val), zpow_pos (by positivity) _, fun _ hz ↦ hγ ?_⟩
    rw [mem_ball_zero_iff, norm_lt_zpow_iff_mulValuation_lt_exp, exp_log (by simp)] at hz
    simpa [restrict_lt_iff_lt_embedding] using hz

variable {x : ℚ_[p]}

lemma vle_one_iff_norm_le_one : x ≤ᵥ 1 ↔ ‖x‖ ≤ 1 :=
  (Valuation.vle_one_iff mulValuation).trans mulValuation_le_one_iff_norm_le_one

/-- The valuation of `ℚ_[p]` given by its valuative relation is at most one exactly on the
elements of `p`-adic norm at most one. -/
lemma valuation_le_one_iff_norm_le_one :
    ValuativeRel.valuation ℚ_[p] x ≤ 1 ↔ ‖x‖ ≤ 1 :=
  (Valuation.vle_one_iff _).symm.trans vle_one_iff_norm_le_one

lemma integers : Valuation.Integers (ValuativeRel.valuation ℚ_[p]) ℤ_[p] where
  hom_inj _ _ := PadicInt.ext
  map_le_one x := Padic.valuation_le_one_iff_norm_le_one.mpr x.2
  exists_of_le_one {r} hr := ⟨⟨r, Padic.valuation_le_one_iff_norm_le_one.mp hr⟩, rfl⟩

/-- The valuative relation on `ℤ_[p]`, pulled back from `ℚ_[p]` along the inclusion. -/
noncomputable instance : ValuativeRel ℤ_[p] :=
  .ofValuation ((Padic.mulValuation (p := p)).comap (algebraMap ℤ_[p] ℚ_[p]))

instance : ((Padic.mulValuation (p := p)).comap (algebraMap ℤ_[p] ℚ_[p])).Compatible :=
  ⟨fun _ _ ↦ Iff.rfl⟩

/-- The valuative relation on `ℤ_[p]` is the restriction of the one on `ℚ_[p]`. -/
instance : ValuativeExtension ℤ_[p] ℚ_[p] where
  vle_iff_vle _ _ := Iff.rfl

/-- The `p`-adic topology of `ℤ_[p]` is the topology of its valuative relation. -/
instance : IsValuativeTopology ℤ_[p] := by
  refine IsValuativeTopology.of_mem_nhds_zero_iff_vle
    ((Padic.mulValuation (p := p)).comap (algebraMap ℤ_[p] ℚ_[p])) fun {s} ↦ ?_
  rw [Metric.mem_nhds_iff]
  have h1p : (1 : ℝ) < p := mod_cast hp.out.one_lt
  constructor
  · -- A metric ball `‖·‖ < ε` contains the valuation ball of radius `v (p ^ n)` for large `n`.
    rintro ⟨ε, hε, hball⟩
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ h1p)
    have ha0 : (p : ℤ_[p]) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
    have hnorm : ‖(p : ℤ_[p]) ^ n‖ < ε := by simpa [norm_pow, PadicInt.norm_p] using hn
    refine ⟨Units.mk0 (Valuation.restrict _ ((p : ℤ_[p]) ^ n)) (by simpa using ha0),
      fun z hz ↦ hball (mem_ball_zero_iff.mpr ?_)⟩
    simp only [Set.mem_ofPred_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hz
    rw [PadicInt.norm_def]
    exact (Padic.norm_lt_norm_iff_mulValuation_lt.mpr hz).trans hnorm
  · -- Conversely, a valuation ball `v · < γ` is the metric ball of radius `p ^ log γ`.
    rintro ⟨γ, hγ⟩
    refine ⟨p ^ WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.val),
      zpow_pos (by positivity) _, fun z hz ↦ hγ ?_⟩
    rw [mem_ball_zero_iff, PadicInt.norm_def, Padic.norm_lt_zpow_iff_mulValuation_lt_exp,
      WithZero.exp_log (by simp)] at hz
    simpa [Valuation.restrict_lt_iff_lt_embedding] using hz

end Padic
