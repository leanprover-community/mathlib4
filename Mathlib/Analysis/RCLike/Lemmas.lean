/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Instances.RealVectorSpace

/-! # Further lemmas about `RCLike` -/

open scoped Finset

variable {K E : Type*} [RCLike K]

namespace Polynomial

theorem ofReal_eval (p : ℝ[X]) (x : ℝ) : (↑(p.eval x) : K) = aeval (↑x) p :=
  (@aeval_algebraMap_apply_eq_algebraMap_eval ℝ K _ _ _ x p).symm

end Polynomial

variable (K) in
lemma RCLike.span_one_I : Submodule.span ℝ (M := K) {1, I} = ⊤ := by
  suffices ∀ x : K, ∃ a b : ℝ, a • 1 + b • I = x by
    simpa [Submodule.eq_top_iff', Submodule.mem_span_pair]
  exact fun x ↦ ⟨re x, im x, by simp [real_smul_eq_coe_mul]⟩

variable (K) in
lemma RCLike.rank_le_two : Module.rank ℝ K ≤ 2 :=
  calc
    _ = Module.rank ℝ ↥(Submodule.span ℝ ({1, I} : Set K)) := by rw [span_one_I]; simp
    _ ≤ #({1, I} : Finset K) := by
      -- TODO: `simp` doesn't rewrite inside the type argument to `Module.rank`, but `rw` does.
      -- We should introduce `Submodule.rank` to fix this.
      have := rank_span_finset_le (R := ℝ) (M := K) {1, I}
      rw [Finset.coe_pair] at this
      simpa [span_one_I] using this
    _ ≤ 2 := mod_cast Finset.card_le_two

variable (K) in
lemma RCLike.finrank_le_two : Module.finrank ℝ K ≤ 2 :=
  Module.finrank_le_of_rank_le <| rank_le_two _

namespace FiniteDimensional

open RCLike

library_note "RCLike instance"/--
This instance generates a type-class problem with a metavariable `?m` that should satisfy
`RCLike ?m`. Since this can only be satisfied by `ℝ` or `ℂ`, this does not cause problems. -/

/-- An `RCLike` field is finite-dimensional over `ℝ`, since it is spanned by `{1, I}`. -/
instance rclike_to_real : FiniteDimensional ℝ K := ⟨{1, I}, by simp [span_one_I]⟩

variable (K E)
variable [NormedAddCommGroup E] [NormedSpace K E]

/-- A finite dimensional vector space over an `RCLike` is a proper metric space.

This is not an instance because it would cause a search for `FiniteDimensional ?x E` before
`RCLike ?x`. -/
theorem proper_rclike [FiniteDimensional K E] : ProperSpace E := by
  -- Using `have` not `let` since it is only existence of `NormedSpace` structure that we need.
  have : NormedSpace ℝ E := RestrictScalars.normedSpace ℝ K E
  have : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ K E
  infer_instance

variable {E}

instance RCLike.properSpace_submodule (S : Submodule K E) [FiniteDimensional K S] :
    ProperSpace S :=
  proper_rclike K S

end FiniteDimensional

namespace RCLike

@[simp, rclike_simps]
theorem reCLM_norm : ‖(reCLM : StrongDual ℝ K)‖ = 1 := by
  apply le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _)
  convert ContinuousLinearMap.ratio_le_opNorm (reCLM : StrongDual ℝ K) (1 : K)
  simp

@[simp, rclike_simps]
theorem conjCLE_norm : ‖(@conjCLE K _ : K →L[ℝ] K)‖ = 1 :=
  (@conjLIE K _).toLinearIsometry.norm_toContinuousLinearMap

@[simp, rclike_simps]
theorem ofRealCLM_norm : ‖(ofRealCLM : ℝ →L[ℝ] K)‖ = 1 :=
  LinearIsometry.norm_toContinuousLinearMap _

lemma mem_balanced_of_norm_le {𝕜 : Type*} [RCLike 𝕜] {K : Set 𝕜} (Balanced_K : Balanced 𝕜 K)
    {x : 𝕜} (hx : x ∈ K) (z : 𝕜) (t : ‖z‖ ≤ ‖x‖) : z ∈ K := by
  by_cases ch: x = 0
  · simp_all
  · have : ‖z / x‖ ≤ 1 := by calc
      _ = ‖z‖ / ‖x‖ := by rw [norm_div]
      _ ≤ _ := (div_le_one₀ (by simpa)).mpr t
    simpa [ch] using balanced_iff_smul_mem.mp Balanced_K this hx

theorem closed_balanced_sep {𝕜 : Type*} [RCLike 𝕜] {r : ℝ} {K : Set 𝕜} (compact_K : IsCompact K)
    (zero_in : 0 ∈ K) (norm_lt_r : ∀ x ∈ K, ‖x‖ < r) :
    ∃ s, 0 < s ∧ s < r ∧ (∀ z ∈ K, ‖z‖ < s) := by
  set g : 𝕜 → ℝ := fun x ↦ ‖x‖ with hg
  obtain ⟨x, xin, eq⟩ : sSup (g '' K) ∈ g '' K :=
    IsCompact.sSup_mem (IsCompact.image compact_K continuous_norm) ⟨0, 0, zero_in, norm_zero⟩
  have g_le : ∀ z ∈ K, g z ≤ g x := fun z hz ↦ by
    rw [eq]
    refine le_csSup ?_ (Set.mem_image_of_mem g hz)
    exact ⟨r, fun y ⟨x, hx, _⟩ ↦ by linarith [norm_lt_r x hx]⟩
  obtain ⟨s, hs₁, hs₂⟩ : ∃ s, g x < s ∧ s < r := exists_between (by simp only [norm_lt_r x xin, g])
  exact ⟨s, by linarith [norm_nonneg x], hs₂, fun z hz ↦ by linarith [norm_lt_r x xin, g_le z hz]⟩

end RCLike

namespace Polynomial

open ComplexConjugate in
lemma aeval_conj (p : ℝ[X]) (z : K) : aeval (conj z) p = conj (aeval z p) :=
  aeval_algHom_apply (RCLike.conjAe (K := K)) z p

lemma aeval_ofReal (p : ℝ[X]) (x : ℝ) : aeval (RCLike.ofReal x : K) p = eval x p :=
  aeval_algHom_apply RCLike.ofRealAm x p

end Polynomial
