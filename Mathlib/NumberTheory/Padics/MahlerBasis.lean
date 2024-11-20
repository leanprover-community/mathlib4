/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Caflisch, David Loeffler
-/
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.RingTheory.Binomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.ContinuousMap.Compact

/-!
# The Mahler basis of continuous functions

In this file we introduce the Mahler basis function `mahler k`, for `k : ℕ`, which is the unique
continuous map `ℤ_[p] → ℚ_[p]` agreeing with `n ↦ n.choose k` for `n ∈ ℕ`.

In future PR's, we will show that these functions give a Banach basis for the space of continuous
maps `ℤ_[p] → ℚ_[p]`.

## References

* [P. Colmez, *Fonctions d'une variable p-adique*][colmez2010]
-/

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

namespace PadicInt

/-- Bound for norms of ascending Pochhammer symbols. -/
lemma norm_ascPochhammer_le (k : ℕ) (x : ℤ_[p]) :
    ‖(ascPochhammer ℤ_[p] k).eval x‖ ≤ ‖(k.factorial : ℤ_[p])‖ := by
  let f := (ascPochhammer ℤ_[p] k).eval
  change ‖f x‖ ≤ ‖_‖
  have hC : (k.factorial : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hf : ContinuousAt f x := Polynomial.continuousAt _
  -- find `n : ℕ` such that `‖f x - f n‖ ≤ ‖k!‖`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖f x - f n‖ ≤ ‖(k.factorial : ℤ_[p])‖ := by
    obtain ⟨δ, hδp, hδ⟩ := Metric.continuousAt_iff.mp hf _ (norm_pos_iff.mpr hC)
    obtain ⟨n, hn'⟩ := PadicInt.denseRange_natCast.exists_dist_lt x hδp
    simpa only [← dist_eq_norm_sub'] using ⟨n, (hδ (dist_comm x n ▸ hn')).le⟩
  -- use ultrametric property to show that `‖f n‖ ≤ ‖k!‖` implies `‖f x‖ ≤ ‖k!‖`
  refine sub_add_cancel (f x) _ ▸ (IsUltrametricDist.norm_add_le_max _ (f n)).trans (max_le hn ?_)
  -- finish using the fact that `n.multichoose k ∈ ℤ`
  simp_rw [f, ← ascPochhammer_eval_cast, Polynomial.eval_eq_smeval,
    ← Ring.factorial_nsmul_multichoose_eq_ascPochhammer, smul_eq_mul, Nat.cast_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_le_one _)

/-- The p-adic integers are a binomial ring, i.e. a ring where binomial coefficients make sense. -/
noncomputable instance instBinomialRing : BinomialRing ℤ_[p] where
  nsmul_right_injective n hn := smul_right_injective ℤ_[p] hn
  -- We define `multichoose` as a fraction in `ℚ_[p]` together with a proof that its norm is `≤ 1`.
  multichoose x k := ⟨(ascPochhammer ℤ_[p] k).eval x / (k.factorial : ℚ_[p]), by
    rw [norm_div, div_le_one (by simpa using k.factorial_ne_zero)]
    exact x.norm_ascPochhammer_le k⟩
  factorial_nsmul_multichoose x k := by rw [← Subtype.coe_inj, nsmul_eq_mul, PadicInt.coe_mul,
    PadicInt.coe_natCast, mul_div_cancel₀ _ (mod_cast k.factorial_ne_zero), Subtype.coe_inj,
    Polynomial.eval_eq_smeval, Polynomial.ascPochhammer_smeval_cast]

@[fun_prop]
lemma continuous_multichoose (k : ℕ) : Continuous (fun x : ℤ_[p] ↦ Ring.multichoose x k) := by
  simp only [Ring.multichoose, BinomialRing.multichoose, continuous_induced_rng]
  fun_prop

@[fun_prop]
lemma continuous_choose (k : ℕ) : Continuous (fun x : ℤ_[p] ↦ Ring.choose x k) := by
  simp only [Ring.choose]
  fun_prop

end PadicInt

/--
The `k`-th Mahler basis function, i.e. the unique continuous function `ℤ_[p] → ℚ_[p]`
agreeing with `n ↦ n.choose k` for `n ∈ ℕ`. See [colmez2010], §1.2.1.
-/
noncomputable def mahler (k : ℕ) : C(ℤ_[p], ℚ_[p]) where
  toFun x := ↑(Ring.choose x k)
  continuous_toFun := continuous_induced_rng.mp (PadicInt.continuous_choose k)

lemma mahler_apply (k : ℕ) (x : ℤ_[p]) : mahler k x = Ring.choose x k := rfl

/-- The function `mahler k` extends `n ↦ n.choose k` on `ℕ`. -/
lemma mahler_natCast_eq (k n : ℕ) : mahler k (n : ℤ_[p]) = n.choose k := by
  simp only [mahler_apply, Ring.choose_natCast, PadicInt.coe_natCast]

/--
The uniform norm of the `k`-th Mahler basis function is 1, for every `k`.
-/
@[simp] lemma norm_mahler_eq (k : ℕ) : ‖(mahler k : C(ℤ_[p], ℚ_[p]))‖ = 1 := by
  apply le_antisymm
  · -- Show all values have norm ≤ 1
    exact (mahler k).norm_le_of_nonempty.mpr (fun _ ↦ PadicInt.norm_le_one _)
  · -- Show norm 1 is attained at `x = k`
    refine (le_of_eq ?_).trans ((mahler k).norm_coe_le_norm k)
    rw [mahler_natCast_eq, Nat.choose_self, Nat.cast_one, norm_one]
