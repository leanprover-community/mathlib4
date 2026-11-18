/-
Copyright (c) 2026 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
module

public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.Ostrowski

/-!
# Ostrowski's Theorem for number fields

Ostrowski's Theorem for number fields:
every nontrivial absolute value on `K` is equivalent to either a `v`-adic absolute value for some
`v : HeightOneSpectrum (𝓞 K)` or to an archimedean absolute value induced by an embedding of `K`
into `ℂ`. This file proves the archimedean case.

## Main results

- `NumberField.existsUnique_infinitePlace_isEquiv`: every archimedean absolute value on a number
  field `K` is equivalent to the absolute value of a unique infinite place of `K`.
- `NumberField.exists_complexEmbedding_rpow_eq`: every archimedean absolute value `v` on a number
  field `K` is of the form `v x = ‖σ x‖ ^ t` for some embedding `σ : K →+* ℂ` and some `0 < t`.

## TODO

Non-archimedean case.

## Tags

absolute value, number field, Ostrowski's Theorem
-/

@[expose] public section

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

section archimedean

open Polynomial in
/-- For an absolute value `v` whose restriction to `ℚ` is equivalent to the usual absolute value,
`v x` is uniformly bounded when all complex conjugates of `x` lie in the closed unit disk. -/
lemma abv_lt_of_complexEmbedding_norm_le_one (v : AbsoluteValue K ℝ)
    (hQ : (v.under ℚ) ≈ Rat.AbsoluteValue.real) (x : K) (hx : ∀ σ : K →+* ℂ, ‖σ x‖ ≤ 1) :
    v x < v ((Module.finrank ℚ K).choose (Module.finrank ℚ K / 2) : K) + 1 := by
  let C := (Module.finrank ℚ K).choose (Module.finrank ℚ K / 2)
  let p := (minpoly ℚ x).map (algebraMap ℚ (WithAbs v))
  have hm : p.Monic := (minpoly.monic (Algebra.IsIntegral.isIntegral x)).map _
  -- Bounds on the complex conjugates bound the coefficients; equivalence on `ℚ`
  -- transfers these bounds to `v`.
  have hc (i : ℕ) : ‖p.coeff i‖ ≤ v C := by
    simpa [p, -map_natCast, -eq_ratCast, WithAbs.algebraMap_right_apply, WithAbs.norm_toAbs_eq,
      ← AbsoluteValue.under_apply, ← map_natCast (algebraMap ℚ K) C, hQ.le_iff_le,
      ← Rat.norm_cast_real] using Embeddings.coeff_bdd_of_norm_le hx i
  -- The minimal polynomial vanishes at `x`; transport this root to `WithAbs v`.
  have hr : p.IsRoot (WithAbs.toAbs v x) := by
    simp [p, IsRoot, eval_map, ← aeval_def,
      -WithAbs.algEquiv_symm_apply, ← WithAbs.algEquiv_symm_apply (R := ℚ),
      aeval_algHom_apply]
  -- The polynomial is monic, so Cauchy's root bound is at most `v C + 1`.
  have hb : (p.cauchyBound : ℝ) ≤ v C + 1 := by
    rw [cauchyBound, hm.leadingCoeff, nnnorm_one, div_one, NNReal.coe_add,
      NNReal.coe_one, add_le_add_iff_right, ← Real.le_toNNReal_iff_coe_le (v.nonneg _)]
    exact Finset.sup_le fun i _ ↦ (Real.le_toNNReal_iff_coe_le (v.nonneg _)).mpr (hc i)
  exact (NNReal.coe_lt_coe.mpr (hr.norm_lt_cauchyBound hm.ne_zero)).trans_le hb

/-- Every archimedean absolute value on a number field is equivalent to the absolute value
associated to a complex embedding. -/
theorem exists_infinitePlace_isEquiv (v : AbsoluteValue K ℝ) (hv : ¬ IsNonarchimedean v) :
    ∃ w : InfinitePlace K, v ≈ w.val := by
  have hQ := Rat.AbsoluteValue.under_isEquiv_real_of_not_isNonarchimedean hv
  -- The rational restriction gives `v 2 > 1`, hence nontriviality for approximation.
  have hv2 : 1 < v (2 : K) := by
    simpa using (hQ.one_lt_iff (x := 2)).mpr (by norm_num [Rat.AbsoluteValue.real_eq_abs])
  by_contra! h
  -- Index approximation by the finite set consisting of `v` and all infinite places.
  let S : Set (AbsoluteValue K ℝ) := {v} ∪ (Set.range (fun w : InfinitePlace K ↦ w.val))
  let : Fintype S := ((Set.finite_range (fun w : InfinitePlace K ↦ w.val)).insert v).fintype
  have hS : ∀ w : S, w.val.IsNontrivial := by
    rintro ⟨w, rfl | ⟨u, rfl⟩⟩
    · exact ⟨2, by norm_num, ne_of_gt hv2⟩
    · exact u.isNontrivial
  -- Distinct infinite places are inequivalent; the contradiction hypothesis
  -- also separates `v` from every infinite place.
  have hp : Pairwise (fun w w' : S ↦ ¬ w.val.IsEquiv w'.val) := by
    rintro ⟨w, rfl | ⟨u, rfl⟩⟩ ⟨w', rfl | ⟨u', rfl⟩⟩ hne he
    · exact hne rfl
    · exact h u' he
    · exact h u he.symm
    · exact hne (Subtype.ext (congrArg (fun u : InfinitePlace K ↦ u.val)
        (InfinitePlace.eq_iff_isEquiv.mpr he)))
  -- Approximation gives one element large at `v` and small at every infinite place.
  obtain ⟨a, ha, hall⟩ :=
    AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv hS hp ⟨v, .inl rfl⟩
  have hs (σ : K →+* ℂ) : ‖σ a‖ < 1 := by
    apply hall ⟨(InfinitePlace.mk σ).val, .inr ⟨InfinitePlace.mk σ, rfl⟩⟩
    intro he
    apply h (InfinitePlace.mk σ)
    rw [congrArg Subtype.val he]
  -- The conjugates of every power stay bounded, whereas `v a ^ n` is unbounded.
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
    (v ((Module.finrank ℚ K).choose (Module.finrank ℚ K / 2) : K) + 1) ha
  have hb := abv_lt_of_complexEmbedding_norm_le_one v hQ (a ^ n) (fun σ ↦ by
    simpa using pow_le_one₀ (norm_nonneg (σ a)) (hs σ).le (n := n))
  exact hn.not_ge (by simpa using hb.le)

/-- **Ostrowski's Theorem, archimedean case**: every archimedean absolute value on a number
  field `K` is equivalent to the absolute value of a unique infinite place of `K`. -/
theorem existsUnique_infinitePlace_isEquiv (v : AbsoluteValue K ℝ) (hv : ¬ IsNonarchimedean v) :
    ∃! w : InfinitePlace K, v ≈ w.val := by
  obtain ⟨w, hw⟩ := exists_infinitePlace_isEquiv v hv
  -- Two candidates are equivalent through `v`; equivalent infinite places are equal.
  exact ⟨w, hw, fun w' hw' ↦ InfinitePlace.eq_iff_isEquiv.mpr (hw'.symm.trans hw)⟩

/-- **Ostrowski's Theorem, archimedean case**: every archimedean absolute value `v` on a number
  field `K` is of the form `v x = ‖σ x‖ ^ t` for some embedding `σ : K →+* ℂ` and some `0 < t`. -/
theorem exists_complexEmbedding_rpow_eq (v : AbsoluteValue K ℝ)
    (hv : ¬ IsNonarchimedean v) :
    ∃ (σ : K →+* ℂ) (t : ℝ), 0 < t ∧ ∀ x : K, v x = ‖σ x‖ ^ t := by
  obtain ⟨w, hw⟩ := exists_infinitePlace_isEquiv v hv
  -- Use the symmetric equivalence so that `w ^ t = v`, in the desired direction.
  obtain ⟨t, ht, h⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp hw.symm
  refine ⟨w.embedding, t, ht, fun x ↦ ?_⟩
  -- A representative embedding has norm exactly equal to its infinite place.
  simpa [InfinitePlace.norm_embedding_eq, InfinitePlace.coe_apply] using (congrFun h x).symm

end archimedean

end NumberField
