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
import Mathlib.Topology.Algebra.Module.LocallyConvex

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
This is exactly the tradeoff we want in `HasFDerivAtFilter`,
as there the base ring is already chosen,
and this removes the choice of norm being part of the statement.

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

-/

open Set Filter Asymptotics Metric
open scoped Topology Pointwise ENNReal NNReal

namespace Asymptotics

/-- `f =o[𝕜;l] g` (`IsLittleOTVS 𝕜 l f g`) is a generalization of `f =o[l] g` (`IsLittleO l f g`)
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
    (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∀ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 (0 : F), ∀ ε ≠ (0 : ℝ≥0),
    ∀ᶠ x in l, egauge 𝕜 U (f x) ≤ ε * egauge 𝕜 V (g x)

@[inherit_doc]
notation:100 f " =o[" 𝕜 ";" l "] " g:100 => IsLittleOTVS 𝕜 l f g

variable {α β 𝕜 E F G : Type*}

section TopologicalSpace

variable [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]
  [AddCommGroup G] [TopologicalSpace G] [Module 𝕜 G]

section congr
variable {f f₁ f₂ : α → E} {g g₁ g₂ : α → F} {l : Filter α}

theorem isLittleOTVS_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    f₁ =o[𝕜;l] g₁ ↔ f₂ =o[𝕜;l] g₂ := by
  simp only [IsLittleOTVS]
  refine forall₂_congr fun U hU => exists_congr fun V => and_congr_right fun hV =>
    forall₂_congr fun ε hε => Filter.eventually_congr ?_
  filter_upwards [hf, hg] with _ e₁ e₂
  rw [e₁, e₂]

/-- A stronger version of `IsLittleOTVS.congr` that requires the functions only agree along the
filter. -/
theorem IsLittleOTVS.congr' (h : f₁ =o[𝕜;l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    f₂ =o[𝕜;l] g₂ :=
  (isLittleOTVS_congr hf hg).mp h

theorem IsLittleOTVS.congr (h : f₁ =o[𝕜;l] g₁) (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) :
    f₂ =o[𝕜;l] g₂ :=
  h.congr' (univ_mem' hf) (univ_mem' hg)

theorem IsLittleOTVS.congr_left (h : f₁ =o[𝕜;l] g) (hf : ∀ x, f₁ x = f₂ x) : f₂ =o[𝕜;l] g :=
  h.congr hf fun _ => rfl

theorem IsLittleOTVS.congr_right (h : f =o[𝕜;l] g₁) (hg : ∀ x, g₁ x = g₂ x) : f =o[𝕜;l] g₂ :=
  h.congr (fun _ => rfl) hg

end congr

@[trans]
theorem IsLittleOTVS.trans {l : Filter α} {f : α → E} {g : α → F} {k : α → G}
    (hfg : f =o[𝕜;l] g) (hgk : g =o[𝕜;l] k) : f =o[𝕜;l] k := by
  intros U hU
  obtain ⟨V, hV0, hV⟩ := hfg U hU
  obtain ⟨W, hW0, hW⟩ := hgk V hV0
  refine ⟨W, hW0, fun ε hε => ?_⟩
  filter_upwards [hV ε hε, hW 1 one_ne_zero] with a hfga hgka
  refine hfga.trans ?_
  gcongr
  simpa using hgka

instance transIsLittleOTVSIsLittleOTVS {l : Filter α} :
    @Trans (α → E) (α → F) (α → G) (· =o[𝕜;l] ·) (· =o[𝕜;l] ·) (· =o[𝕜;l] ·) where
  trans := IsLittleOTVS.trans

theorem _root_.Filter.HasBasis.isLittleOTVS_iff {ιE ιF : Sort*} {pE : ιE → Prop} {pF : ιF → Prop}
    {sE : ιE → Set E} {sF : ιF → Set F} (hE : HasBasis (𝓝 (0 : E)) pE sE)
    (hF : HasBasis (𝓝 (0 : F)) pF sF) {f : α → E} {g : α → F} {l : Filter α} :
    f =o[𝕜;l] g ↔ ∀ i, pE i → ∃ j, pF j ∧ ∀ ε ≠ (0 : ℝ≥0),
      ∀ᶠ x in l, egauge 𝕜 (sE i) (f x) ≤ ε * egauge 𝕜 (sF j) (g x) := by
  refine (hE.forall_iff ?_).trans <| forall₂_congr fun _ _ ↦ hF.exists_iff ?_
  · rintro s t hsub ⟨V, hV₀, hV⟩
    exact ⟨V, hV₀, fun ε hε ↦ (hV ε hε).mono fun x ↦ le_trans <| egauge_anti _ hsub _⟩
  · refine fun s t hsub h ε hε ↦ (h ε hε).mono fun x hx ↦ hx.trans ?_
    gcongr

@[simp]
theorem isLittleOTVS_map {f : α → E} {g : α → F} {k : β → α} {l : Filter β} :
    f =o[𝕜; map k l] g ↔ (f ∘ k) =o[𝕜;l] (g ∘ k) := by
  simp [IsLittleOTVS]

lemma IsLittleOTVS.mono {f : α → E} {g : α → F} {l₁ l₂ : Filter α}
    (hf : f =o[𝕜;l₁] g) (h : l₂ ≤ l₁) : f =o[𝕜;l₂] g :=
  fun U hU => let ⟨V, hV0, hV⟩ := hf U hU; ⟨V, hV0, fun ε hε => (hV ε hε).filter_mono h⟩

lemma IsLittleOTVS.sup {f : α → E} {g : α → F} {l₁ l₂ : Filter α}
    (hf₁ : f =o[𝕜;l₁] g) (hf₂ : f =o[𝕜;l₂] g) :
    f =o[𝕜;(l₁ ⊔ l₂)] g := by
  intro U hU
  let ⟨V₁, hV0₁, hV₁⟩ := hf₁ U hU
  let ⟨V₂, hV0₂, hV₂⟩ := hf₂ U hU
  refine ⟨V₁ ∩ V₂, Filter.inter_mem hV0₁ hV0₂, fun ε hε => ?_⟩
  rw [eventually_sup]
  constructor
  · refine (hV₁ ε hε).mono fun x hx => hx.trans ?_
    gcongr
    exact inter_subset_left
  · refine (hV₂ ε hε).mono fun x hx => hx.trans ?_
    gcongr
    exact inter_subset_right

lemma isLittleOTVS_insert [TopologicalSpace α] {f : α → E} {g : α → F} {x : α} {s : Set α}
    (h : f x = 0) :
    f =o[𝕜;(𝓝[insert x s] x)] g ↔ f =o[𝕜;(𝓝[s] x)] g := by
  refine forall₂_congr fun U hU => exists_congr fun V => and_congr_right fun hV =>
    forall₂_congr fun ε hε => ?_
  simp [h, egauge_zero_right _ (Set.nonempty_of_mem <| mem_of_mem_nhds hU)]

lemma IsLittleOTVS.insert [TopologicalSpace α] {f : α → E} {g : α → F} {x : α} {s : Set α}
    (h : f =o[𝕜;(𝓝[s] x)] g) (hf : f x = 0) :
    f =o[𝕜;(𝓝[insert x s] x)] g :=
  (isLittleOTVS_insert hf).2 h

@[simp]
lemma IsLittleOTVS.bot {f : α → E} {g : α → F} : f =o[𝕜;⊥] g :=
  fun u hU => ⟨univ, by simp⟩

@[simp]
lemma IsLittleOTVS.zero (g : α → F) (l : Filter α) : (0 : α → E) =o[𝕜;l] g := by
  intros U hU
  simpa [egauge_zero_right _ (Set.nonempty_of_mem <| mem_of_mem_nhds hU)] using ⟨univ, by simp⟩

lemma IsLittleOTVS.add
    [TopologicalAddGroup F] [Module ℝ F] [LocallyConvexSpace ℝ F]
    [TopologicalAddGroup E] [Module ℝ E] [LocallyConvexSpace ℝ E]
    [ContinuousSMul 𝕜 E]
    {f₁ f₂ : α → E} {g : α → F} {l : Filter α}
    (hf₁ : IsLittleOTVS 𝕜 f₁ g l) (hf₂ : IsLittleOTVS 𝕜 f₂ g l) :
    IsLittleOTVS 𝕜 (f₁ + f₂) g l := by
  rw [(LocallyConvexSpace.convex_basis_zero ℝ E).isLittleOTVS_iff
    (LocallyConvexSpace.convex_basis_zero ℝ F)] at hf₁ hf₂ ⊢
  intro U hU
  let ⟨V₁, ⟨hV0₁, hVc₁⟩, hV₁⟩ := hf₁ U hU
  let ⟨V₂, ⟨hV0₂, hVc₂⟩, hV₂⟩ := hf₂ U hU
  refine ⟨V₁ ∩ V₂, ⟨Filter.inter_mem hV0₁ hV0₂, hVc₁.inter hVc₂⟩, fun ε hε => ?_⟩
  have hε' := (half_pos <| pos_iff_ne_zero.mpr hε).ne'
  filter_upwards [(hV₁ (ε/2) hε').and (hV₂ (ε/2) hε')] with a ⟨ha, hb⟩
  simp at ha hb ⊢
  refine (egauge_add_right ?_ _ _).trans <| add_le_add ha hb |>.trans <| ?_
  · intros r₁ r₂
    -- almost but not quite convexity
    -- apply hU.2.add_smul r₁ r₂
    sorry
  rw [← mul_add]
  have h := mul_left_mono (a := (ε / 2 : ℝ≥0∞)) <| add_le_add
    (egauge_anti 𝕜 (@inter_subset_left _ V₁ V₂) (g a))
    (egauge_anti 𝕜 (@inter_subset_right _ V₁ V₂) (g a))
  refine h.trans_eq ?_
  dsimp
  rw [← two_mul, ← mul_assoc, ENNReal.div_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

protected lemma IsLittleOTVS.smul_left {f : α → E} {g : α → F} {l : Filter α}
    (h : f =o[𝕜;l] g) (c : α → 𝕜) :
    (fun x ↦ c x • f x) =o[𝕜;l] (fun x ↦ c x • g x) := by
  unfold IsLittleOTVS at *
  peel h with U hU V hV ε hε x hx
  rw [egauge_smul_right, egauge_smul_right, mul_left_comm]
  · gcongr
  all_goals exact fun _ ↦ Filter.nonempty_of_mem ‹_›

lemma isLittleOTVS_one [ContinuousSMul 𝕜 E] {f : α → E} {l : Filter α} :
    f =o[𝕜;l] (1 : α → 𝕜) ↔ Tendsto f l (𝓝 0) := by
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
    (h : g =o[𝕜;l] f) : Tendsto (fun x ↦ (f x)⁻¹ • g x) l (𝓝 0) := by
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
    g =o[𝕜;l] f ↔ Tendsto (fun x ↦ (f x)⁻¹ • g x) l (𝓝 0) := by
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
    f =o[𝕜;l] g ↔ f =o[l] g := by
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
