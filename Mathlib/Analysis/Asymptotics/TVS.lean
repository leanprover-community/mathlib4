/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Eric Wieser
-/
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.Convex.EGauge
import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
import Mathlib.Analysis.Seminorm
import Mathlib.Tactic.Peel
import Mathlib.Topology.Instances.ENNReal

/-!
# Asymptotics in a Topological Vector Space

This file defines `Asymptotics.IsLittleOTVS` as a generalization of `Asymptotics.IsLittleO` from
normed spaces to topological spaces.

Given two functions `f` and `g` taking values in topological vector spaces
over a normed field `K`,
we say that $f = o(g)$ if for any neighborhood of zero `U` in the codomain of `f`
there exists a neighborhood of zero `V` in the codomain of `g`
such that $\operatorname{gauge}_{K, U} (f(x)) = o(\operatorname{gauge}_{K, V} (g(x)))$,
where $\operatorname{gauge}_{K, U}(y) = \inf \{‖c‖ \mid y ∈ c • U\}$.

In a normed space, we can use balls of positive radius as both `U` and `V`,
thus reducing the definition to the classical one.

This frees the user from having to chose a canonical norm, at the expense of having to pick a
specific base ring.

This definition was added to the library in order to migrate Fréchet derivatives
from normed vector spaces to topological vector spaces.
The definition is motivated by
https://en.wikipedia.org/wiki/Fr%C3%A9chet_derivative#Generalization_to_topological_vector_spaces
but the definition there doesn't work for topological vector spaces over general normed fields.
[This Zulip discussion](https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/generalizing.20deriv.20to.20TVS)
led to the current choice of the definition.

It may be possible to generalize $f = O(g)$ and $f = \Theta(g)$ in a similar way,
but we don't need these definitions to redefine Fréchet derivatives,
so formalization of these generalizations is left for later,
until someone will need it (e.g., to prove properties of the Fréchet derivative over TVS).

## Main results

* `isLittleOTVS_iff_isLittleO`: the equivalence between these two definitions in the case of a
  normed space.

* `isLittleOTVS_iff_tendsto_inv_smul`: the equivalence to convergence of the ratio to zero
  in case of a topological vector space.

## TODO

Use this to redefine `HasFDerivAtFilter`, as the base ring is already chosen there, and this removes
the choice of norm being part of the statement.
-/

open Set Filter Asymptotics Metric
open scoped Topology Pointwise ENNReal NNReal

namespace Asymptotics

/-- `IsLittleOTVS 𝕜 f g l` is a generalization of `f =o[l] g` (`IsLittleO f g l`)
that works in topological `𝕜`-vector spaces.

Given two functions `f` and `g` taking values in topological vector spaces
over a normed field `K`,
we say that $f = o(g)$ if for any neighborhood of zero `U` in the codomain of `f`
there exists a neighborhood of zero `V` in the codomain of `g`
such that $\operatorname{gauge}_{K, U} (f(x)) = o(\operatorname{gauge}_{K, V} (g(x)))$,
where $\operatorname{gauge}_{K, U}(y) = \inf \{‖c‖ \mid y ∈ c • U\}$.

We use an `ENNReal`-valued function `egauge` for the gauge,
so we unfold the definition of little o instead of reusing it. -/
def IsLittleOTVS (𝕜 : Type*) {α E F : Type*}
    [NNNorm 𝕜] [TopologicalSpace E] [TopologicalSpace F] [Zero E] [Zero F] [SMul 𝕜 E] [SMul 𝕜 F]
    (f : α → E) (g : α → F) (l : Filter α) : Prop :=
  ∀ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 (0 : F), ∀ ε ≠ (0 : ℝ≥0),
    ∀ᶠ x in l, egauge 𝕜 U (f x) ≤ ε * egauge 𝕜 V (g x)

variable {α β 𝕜 E F : Type*}

section TopologicalSpace

variable [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]

theorem _root_.Filter.HasBasis.isLittleOTVS_iff {ιE ιF : Sort*} {pE : ιE → Prop} {pF : ιF → Prop}
    {sE : ιE → Set E} {sF : ιF → Set F} (hE : HasBasis (𝓝 (0 : E)) pE sE)
    (hF : HasBasis (𝓝 (0 : F)) pF sF) {f : α → E} {g : α → F} {l : Filter α} :
    IsLittleOTVS 𝕜 f g l ↔ ∀ i, pE i → ∃ j, pF j ∧ ∀ ε ≠ (0 : ℝ≥0),
      ∀ᶠ x in l, egauge 𝕜 (sE i) (f x) ≤ ε * egauge 𝕜 (sF j) (g x) := by
  refine (hE.forall_iff ?_).trans <| forall₂_congr fun _ _ ↦ hF.exists_iff ?_
  · rintro s t hsub ⟨V, hV₀, hV⟩
    exact ⟨V, hV₀, fun ε hε ↦ (hV ε hε).mono fun x ↦ le_trans <| egauge_anti _ hsub _⟩
  · refine fun s t hsub h ε hε ↦ (h ε hε).mono fun x hx ↦ hx.trans ?_
    gcongr

@[simp]
theorem isLittleOTVS_map {f : α → E} {g : α → F} {k : β → α} {l : Filter β} :
    IsLittleOTVS 𝕜 f g (map k l) ↔ IsLittleOTVS 𝕜 (f ∘ k) (g ∘ k) l := by
  simp [IsLittleOTVS]

protected lemma IsLittleOTVS.smul_left {f : α → E} {g : α → F} {l : Filter α}
    (h : IsLittleOTVS 𝕜 f g l) (c : α → 𝕜) :
    IsLittleOTVS 𝕜 (fun x ↦ c x • f x) (fun x ↦ c x • g x) l := by
  unfold IsLittleOTVS at *
  peel h with U hU V hV ε hε x hx
  rw [egauge_smul_right, egauge_smul_right, mul_left_comm]
  · gcongr
  all_goals exact fun _ ↦ Filter.nonempty_of_mem ‹_›

lemma isLittleOTVS_one [ContinuousSMul 𝕜 E] {f : α → E} {l : Filter α} :
    IsLittleOTVS 𝕜 f (1 : α → 𝕜) l ↔ Tendsto f l (𝓝 0) := by
  constructor
  · intro hf
    rw [(basis_sets _).isLittleOTVS_iff nhds_basis_ball] at hf
    rw [(nhds_basis_balanced 𝕜 E).tendsto_right_iff]
    rintro U ⟨hU, hUb⟩
    rcases hf U hU with ⟨r, hr₀, hr⟩
    lift r to ℝ≥0 using hr₀.le
    norm_cast at hr₀
    rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
    obtain ⟨ε, hε₀, hε⟩ : ∃ ε : ℝ≥0, 0 < ε ∧ (ε * ‖c‖₊ / r : ℝ≥0∞) < 1 := by
      apply Eventually.exists_gt
      refine Continuous.tendsto' ?_ _ _ (by simp) |>.eventually_lt_const zero_lt_one
      fun_prop (disch := intros; first | apply ENNReal.coe_ne_top | positivity)
    filter_upwards [hr ε hε₀.ne'] with x hx
    refine mem_of_egauge_lt_one hUb (hx.trans_lt ?_)
    calc
      (ε : ℝ≥0∞) * egauge 𝕜 (ball (0 : 𝕜) r) 1 ≤ (ε * ‖c‖₊ / r : ℝ≥0∞) := by
        rw [mul_div_assoc]
        gcongr
        simpa using egauge_ball_le_of_one_lt_norm (r := r) (x := (1 : 𝕜)) hc (by simp)
      _ < 1 := ‹_›
  · intro hf U hU
    refine ⟨ball 0 1, ball_mem_nhds _ one_pos, fun ε hε ↦ ?_⟩
    rcases NormedField.exists_norm_lt 𝕜 hε.bot_lt with ⟨c, hc₀, hcε⟩
    replace hc₀ : c ≠ 0 := by simpa using hc₀
    filter_upwards [hf ((set_smul_mem_nhds_zero_iff hc₀).2 hU)] with a ha
    calc
      egauge 𝕜 U (f a) ≤ ‖c‖₊ := egauge_le_of_mem_smul ha
      _ ≤ ε := mod_cast hcε.le
      _ ≤ ε * egauge 𝕜 (ball (0 : 𝕜) 1) 1 := by
        apply le_mul_of_one_le_right'
        simpa using le_egauge_ball_one 𝕜 (1 : 𝕜)

lemma IsLittleOTVS.tendsto_inv_smul [ContinuousSMul 𝕜 E] {f : α → 𝕜} {g : α → E} {l : Filter α}
    (h : IsLittleOTVS 𝕜 g f l) : Tendsto (fun x ↦ (f x)⁻¹ • g x) l (𝓝 0) := by
  rw [(basis_sets _).isLittleOTVS_iff nhds_basis_ball] at h
  rw [(nhds_basis_balanced 𝕜 E).tendsto_right_iff]
  rintro U ⟨hU, hUB⟩
  rcases h U hU with ⟨ε, hε₀, hε⟩
  lift ε to ℝ≥0 using hε₀.le; norm_cast at hε₀
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  filter_upwards [hε (ε / 2 / ‖c‖₊) (ne_of_gt <| div_pos (half_pos hε₀) (one_pos.trans hc))]
    with x hx
  refine mem_of_egauge_lt_one hUB ?_
  rw [id, egauge_smul_right (fun _ ↦ Filter.nonempty_of_mem hU), nnnorm_inv]
  calc
    ↑‖f x‖₊⁻¹ * egauge 𝕜 U (g x)
      ≤ (↑‖f x‖₊)⁻¹ * (↑(ε / 2 / ‖c‖₊) * egauge 𝕜 (ball 0 ε) (f x)) :=
      mul_le_mul' ENNReal.coe_inv_le hx
    _ ≤ (↑‖f x‖₊)⁻¹ * ((ε / 2 / ‖c‖₊) * (‖c‖₊ * ‖f x‖₊ / ε)) := by
      gcongr
      · refine ENNReal.coe_div_le.trans ?_; gcongr; apply ENNReal.coe_div_le
      · exact egauge_ball_le_of_one_lt_norm hc (.inl hε₀.ne')
    _ = (‖f x‖₊ / ‖f x‖₊) * (ε / ε) * (‖c‖₊ / ‖c‖₊) * (1 / 2) := by
      simp only [div_eq_mul_inv, one_mul]; ring
    _ ≤ 1 * 1 * 1 * (1 / 2) := by gcongr <;> apply ENNReal.div_self_le_one
    _ < 1 := by norm_num

lemma isLittleOTVS_iff_tendsto_inv_smul [ContinuousSMul 𝕜 E] {f : α → 𝕜} {g : α → E} {l : Filter α}
    (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) :
    IsLittleOTVS 𝕜 g f l ↔ Tendsto (fun x ↦ (f x)⁻¹ • g x) l (𝓝 0) := by
  refine ⟨IsLittleOTVS.tendsto_inv_smul, fun h U hU ↦ ?_⟩
  refine ⟨ball 0 1, ball_mem_nhds _ one_pos, fun ε hε ↦ ?_⟩
  rcases NormedField.exists_norm_lt 𝕜 hε.bot_lt with ⟨c, hc₀, hcε : ‖c‖₊ < ε⟩
  rw [norm_pos_iff] at hc₀
  filter_upwards [h₀, h <| (set_smul_mem_nhds_zero_iff hc₀).2 hU]
    with x hx₀ (hx : (f x)⁻¹ • g x ∈ c • U)
  rcases eq_or_ne (f x) 0 with hf₀ | hf₀
  · simp [hx₀ hf₀, Filter.nonempty_of_mem hU]
  · rw [mem_smul_set_iff_inv_smul_mem₀ hc₀, smul_smul] at hx
    refine (egauge_le_of_smul_mem_of_ne hx (by simp [*])).trans ?_
    simp_rw [nnnorm_mul, nnnorm_inv, mul_inv, inv_inv, ENNReal.coe_mul]
    gcongr
    apply le_egauge_ball_one

end TopologicalSpace

section NormedSpace

variable [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

lemma isLittleOTVS_iff_isLittleO {f : α → E} {g : α → F} {l : Filter α} :
    IsLittleOTVS 𝕜 f g l ↔ f =o[l] g := by
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc : 1 < ‖c‖₊⟩
  have hc₀ : 0 < ‖c‖₊ := one_pos.trans hc
  simp only [isLittleO_iff, nhds_basis_ball.isLittleOTVS_iff nhds_basis_ball]
  refine ⟨fun h ε hε ↦ ?_, fun h ε hε ↦ ⟨1, one_pos, fun δ hδ ↦ ?_⟩⟩
  · rcases h ε hε with ⟨δ, hδ₀, hδ⟩
    lift ε to ℝ≥0 using hε.le; lift δ to ℝ≥0 using hδ₀.le; norm_cast at hε hδ₀
    filter_upwards [hδ (δ / ‖c‖₊) (div_pos hδ₀ hc₀).ne'] with x hx
    suffices (‖f x‖₊ / ε : ℝ≥0∞) ≤ ‖g x‖₊ by
      rw [← ENNReal.coe_div hε.ne'] at this
      rw [← div_le_iff₀' (NNReal.coe_pos.2 hε)]
      exact_mod_cast this
    calc
      (‖f x‖₊ / ε : ℝ≥0∞) ≤ egauge 𝕜 (ball 0 ε) (f x) := div_le_egauge_ball 𝕜 _ _
      _ ≤ ↑(δ / ‖c‖₊) * egauge 𝕜 (ball 0 ↑δ) (g x) := hx
      _ ≤ (δ / ‖c‖₊) * (‖c‖₊ * ‖g x‖₊ / δ) := by
        gcongr
        exacts [ENNReal.coe_div_le, egauge_ball_le_of_one_lt_norm hc (.inl <| ne_of_gt hδ₀)]
      _ = (δ / δ) * (‖c‖₊ / ‖c‖₊) * ‖g x‖₊ := by simp only [div_eq_mul_inv]; ring
      _ ≤ 1 * 1 * ‖g x‖₊ := by gcongr <;> exact ENNReal.div_self_le_one
      _ = ‖g x‖₊ := by simp
  · filter_upwards [@h ↑(ε * δ / ‖c‖₊) (by positivity)] with x (hx : ‖f x‖₊ ≤ ε * δ / ‖c‖₊ * ‖g x‖₊)
    lift ε to ℝ≥0 using hε.le
    calc
      egauge 𝕜 (ball 0 ε) (f x) ≤ ‖c‖₊ * ‖f x‖₊ / ε :=
        egauge_ball_le_of_one_lt_norm hc (.inl <| ne_of_gt hε)
      _ ≤ ‖c‖₊ * (↑(ε * δ / ‖c‖₊) * ‖g x‖₊) / ε := by gcongr; exact_mod_cast hx
      _ = (‖c‖₊ / ‖c‖₊) * (ε / ε) * δ * ‖g x‖₊ := by
        simp only [div_eq_mul_inv, ENNReal.coe_inv hc₀.ne', ENNReal.coe_mul]; ring
      _ ≤ 1 * 1 * δ * ‖g x‖₊ := by gcongr <;> exact ENNReal.div_self_le_one
      _ = δ * ‖g x‖₊ := by simp
      _ ≤ δ * egauge 𝕜 (ball 0 1) (g x) := by gcongr; apply le_egauge_ball_one

alias ⟨isLittleOTVS.isLittleO, IsLittle.isLittleOTVS⟩ := isLittleOTVS_iff_isLittleO

end NormedSpace

end Asymptotics
