/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Misc lemma about the tangent cone

This file contains two deprecated lemmas about `tangentConeAt`.
One of them used to be useful before we generalized the definition to topological vector spaces.
Another one brings too many dependencies over too little added value.
-/

public section

open Filter
open scoped Topology

section

variable {𝕜 E : Type*} [NormedDivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [ContinuousSMul 𝕜 E] {s : Set E} {x y : E} {r : 𝕜}

/-- Auxiliary lemma ensuring that, under the assumptions from an old definition of the tangent cone,
the sequence `d` tends to 0 at infinity. -/
@[deprecated "This lemma was useful with the old definition of the tangent cone, not anymore"
  (since := "2026-01-22")]
theorem tangentConeAt.lim_zero {α : Type*} (l : Filter α) {c : α → 𝕜} {d : α → E} {y : E}
    (hc : Tendsto (fun n => ‖c n‖) l atTop) (hd : Tendsto (fun n => c n • d n) l (𝓝 y)) :
    Tendsto d l (𝓝 0) := by
  have : ∀ᶠ n in l, (c n)⁻¹ • c n • d n = d n :=
    (eventually_ne_of_tendsto_norm_atTop hc 0).mono fun n hn ↦ inv_smul_smul₀ hn (d n)
  rw [tendsto_norm_atTop_iff_cobounded] at hc
  simpa using Tendsto.congr' this <| (tendsto_inv₀_cobounded.comp hc).smul hd


@[deprecated mem_tangentConeAt_of_add_smul_mem (since := "2026-01-22")]
theorem mem_tangentConeAt_of_pow_smul (hr₀ : r ≠ 0) (hr : ‖r‖ < 1)
    (hs : ∀ᶠ n : ℕ in atTop, x + r ^ n • y ∈ s) :
    y ∈ tangentConeAt 𝕜 s x := by
  refine mem_tangentConeAt_of_add_smul_mem
    (tendsto_nhdsWithin_iff.mpr ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr, ?_⟩) hs
  simp [hr₀]

end

set_option linter.deprecated false in
/-- Before https://github.com/leanprover-community/mathlib4/pull/34127,
the right-hand side of this equivalence was the definition of the tangent cone.

This lemma is here to show that the new definition is equivalent to the old one,
and will be removed after a deprecation period. -/
@[deprecated mem_tangentConeAt_iff_exists_seq (since := "2026-01-22")]
theorem mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {s : Set E} {x y : E} :
    y ∈ tangentConeAt 𝕜 s x ↔
      ∃ (c : ℕ → 𝕜) (d : ℕ → E), Tendsto (‖c ·‖) atTop atTop ∧ (∀ᶠ n in atTop, x + d n ∈ s) ∧
        Tendsto (fun n ↦ c n • d n) atTop (𝓝 y) := by
  constructor
  · rcases eq_or_ne y 0 with rfl | hy₀
    · rw [zero_mem_tangentConeAt_iff]
      intro hx
      obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 1
      have (n : ℕ) : ∃ d : E, x + d ∈ s ∧ ‖d‖ < (1 / (2 * ‖c‖)) ^ n := by
        rw [Metric.mem_closure_iff] at hx
        rcases hx ((1 / (2 * ‖c‖)) ^ n) (by positivity) with ⟨v, hvs, hv⟩
        use v - x
        simp_all [dist_eq_norm_sub']
      choose d hds hd using this
      refine ⟨(c ^ ·), d, ?tendsto_c, .of_forall hds, ?tendsto_cd⟩
      case tendsto_c =>
        simp only [norm_pow]
        exact tendsto_pow_atTop_atTop_of_one_lt hc
      case tendsto_cd =>
        rw [atTop_basis.tendsto_iff (Metric.nhds_basis_ball_pow one_half_pos one_half_lt_one)]
        refine fun N _ ↦ ⟨N, trivial, fun n hn ↦ ?_⟩
        rw [Set.mem_Ici] at hn
        suffices ‖c‖ ^ n * ‖d n‖ < 1 / (2 ^ N) by simpa [norm_smul]
        rw [← lt_div_iff₀' (by positivity)]
        refine (hd n).trans_le ?_
        grw [hn]
        · simp [mul_pow, div_eq_inv_mul]
        · norm_num1
    · rw [mem_tangentConeAt_iff_exists_seq]
      rintro ⟨c, d, hd₀, hds, hcd⟩
      refine ⟨c, d, ?_, hds, hcd⟩
      replace hd₀ := hd₀.norm
      have hd₀' : ∀ᶠ n in .atTop, d n ≠ 0 :=
        hcd.eventually_ne hy₀ |>.mono fun _ ↦ right_ne_zero_of_smul
      replace hcd := hcd.norm
      simp only [norm_smul, norm_zero, ← div_inv_eq_mul] at hd₀ hcd
      refine .num ?_ (by simpa) hcd
      rw [← inv_nhdsGT_zero (𝕜 := ℝ), ← Filter.comap_inv, Filter.tendsto_comap_iff]
      simpa [Function.comp_def, tendsto_nhdsWithin_iff, hd₀] using hd₀'
  · rintro ⟨c, d, hc, hds, hcd⟩
    exact mem_tangentConeAt_of_seq atTop c d (tangentConeAt.lim_zero atTop hc hcd) hds hcd
