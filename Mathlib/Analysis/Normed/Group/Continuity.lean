/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Topology.UniformSpace.Real
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Filter.Map
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Group
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToAdditive
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Bornology.Real
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Order.T5
import Mathlib.Topology.Sequences

/-!
# Continuity of the norm on (semi)normed groups

## Tags

normed group
-/

public section

variable {α ι κ E F G : Type*}

open Filter Function Metric Bornology
open ENNReal Filter NNReal Uniformity Pointwise Topology

section SeminormedGroup

variable [SeminormedGroup E] [SeminormedGroup F] [SeminormedGroup G]

open Finset

section ContinuousENorm

variable {E : Type*} [TopologicalSpace E] [ContinuousENorm E]

@[continuity, fun_prop]
lemma continuous_enorm : Continuous fun a : E ↦ ‖a‖ₑ := ContinuousENorm.continuous_enorm

variable {X : Type*} [TopologicalSpace X] {f : X → E} {s : Set X} {a : X}

@[fun_prop]
lemma Continuous.enorm : Continuous f → Continuous (‖f ·‖ₑ) :=
  continuous_enorm.comp

lemma ContinuousAt.enorm {a : X} (h : ContinuousAt f a) : ContinuousAt (‖f ·‖ₑ) a := by fun_prop

@[fun_prop]
lemma ContinuousWithinAt.enorm {s : Set X} {a : X} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (‖f ·‖ₑ) s a :=
  (ContinuousENorm.continuous_enorm.continuousWithinAt).comp (t := Set.univ) h
    (fun _ _ ↦ by trivial)

@[fun_prop]
lemma ContinuousOn.enorm (h : ContinuousOn f s) : ContinuousOn (‖f ·‖ₑ) s :=
  (ContinuousENorm.continuous_enorm.continuousOn).comp (t := Set.univ) h <| Set.mapsTo_univ _ _

end ContinuousENorm

@[to_additive]
theorem tendsto_iff_norm_inv_mul_tendsto_zero {f : α → E} {a : Filter α} {b : E} :
    Tendsto f a (𝓝 b) ↔ Tendsto (fun e => ‖(f e)⁻¹ * b‖) a (𝓝 0) := by
  simp only [← dist_eq_norm_inv_mul, ← tendsto_iff_dist_tendsto_zero]

@[to_additive]
theorem tendsto_one_iff_norm_tendsto_zero {f : α → E} {a : Filter α} :
    Tendsto f a (𝓝 1) ↔ Tendsto (‖f ·‖) a (𝓝 0) :=
  tendsto_iff_norm_inv_mul_tendsto_zero.trans <| by simp

@[to_additive (attr := simp 1100)]
theorem comap_norm_nhds_one : comap norm (𝓝 0) = 𝓝 (1 : E) := by
  simpa only [dist_one_right] using nhds_comap_dist (1 : E)

/-- Special case of the sandwich theorem: if the norm of `f` is eventually bounded by a real
function `a` which tends to `0`, then `f` tends to `1` (neutral element of `SeminormedGroup`).
In this pair of lemmas (`squeeze_one_norm'` and `squeeze_one_norm`), following a convention of
similar lemmas in `Topology.MetricSpace.Basic` and `Topology.Algebra.Order`, the `'` version is
phrased using "eventually" and the non-`'` version is phrased absolutely. -/
@[to_additive /-- Special case of the sandwich theorem: if the norm of `f` is eventually bounded by
a real function `a` which tends to `0`, then `f` tends to `0`. In this pair of lemmas
(`squeeze_zero_norm'` and `squeeze_zero_norm`), following a convention of similar lemmas in
`Topology.MetricSpace.Pseudo.Defs` and `Topology.Algebra.Order`, the `'` version is phrased using
"eventually" and the non-`'` version is phrased absolutely. -/]
theorem squeeze_one_norm' {f : α → E} {a : α → ℝ} {t₀ : Filter α} (h : ∀ᶠ n in t₀, ‖f n‖ ≤ a n)
    (h' : Tendsto a t₀ (𝓝 0)) : Tendsto f t₀ (𝓝 1) :=
  tendsto_one_iff_norm_tendsto_zero.2 <|
    squeeze_zero' (Eventually.of_forall fun _n => norm_nonneg' _) h h'

/-- Special case of the sandwich theorem: if the norm of `f` is bounded by a real function `a` which
tends to `0`, then `f` tends to `1`. -/
@[to_additive /-- Special case of the sandwich theorem: if the norm of `f` is bounded by a real
function `a` which tends to `0`, then `f` tends to `0`. -/]
theorem squeeze_one_norm {f : α → E} {a : α → ℝ} {t₀ : Filter α} (h : ∀ n, ‖f n‖ ≤ a n) :
    Tendsto a t₀ (𝓝 0) → Tendsto f t₀ (𝓝 1) :=
  squeeze_one_norm' <| Eventually.of_forall h

@[to_additive]
theorem tendsto_norm_inv_mul_self (x : E) : Tendsto (fun a => ‖a⁻¹ * x‖) (𝓝 x) (𝓝 0) := by
  simpa [dist_eq_norm_inv_mul] using
    tendsto_id.dist (tendsto_const_nhds : Tendsto (fun _a => (x : E)) (𝓝 x) _)

@[to_additive]
theorem tendsto_norm_inv_mul_self_nhdsGE (x : E) : Tendsto (fun a ↦ ‖a⁻¹ * x‖) (𝓝 x) (𝓝[≥] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_norm_inv_mul_self x, by simp⟩

@[to_additive tendsto_norm]
theorem tendsto_norm' {x : E} : Tendsto (fun a => ‖a‖) (𝓝 x) (𝓝 ‖x‖) := by
  simpa using tendsto_id.dist (tendsto_const_nhds : Tendsto (fun _a => (1 : E)) _ _)

/-- See `tendsto_norm_one` for a version with pointed neighborhoods. -/
@[to_additive /-- See `tendsto_norm_zero` for a version with pointed neighborhoods. -/]
theorem tendsto_norm_one : Tendsto (fun a : E => ‖a‖) (𝓝 1) (𝓝 0) := by
  simpa using tendsto_norm_inv_mul_self (1 : E)

@[to_additive (attr := continuity, fun_prop) continuous_norm]
theorem continuous_norm' : Continuous fun a : E => ‖a‖ := by
  simpa using continuous_id.dist (continuous_const : Continuous fun _a => (1 : E))

@[to_additive (attr := continuity, fun_prop) continuous_nnnorm]
theorem continuous_nnnorm' : Continuous fun a : E => ‖a‖₊ :=
  continuous_norm'.subtype_mk _

end SeminormedGroup

section Instances

@[to_additive]
instance SeminormedGroup.toContinuousENorm [SeminormedGroup E] : ContinuousENorm E where
  continuous_enorm := ENNReal.isOpenEmbedding_coe.continuous.comp continuous_nnnorm'

@[to_additive]
instance NormedGroup.toENormedMonoid {F : Type*} [NormedGroup F] : ENormedMonoid F where
  enorm_zero := by simp [enorm_eq_nnnorm]
  enorm_eq_zero := by simp [enorm_eq_nnnorm]
  enorm_mul_le := by simp [enorm_eq_nnnorm, ← coe_add, nnnorm_mul_le']

@[to_additive]
instance NormedCommGroup.toENormedCommMonoid [NormedCommGroup E] : ENormedCommMonoid E where
  __ := NormedGroup.toENormedMonoid
  __ := ‹NormedCommGroup E›

end Instances

section SeminormedGroup

variable [SeminormedGroup E] [SeminormedGroup F] [SeminormedGroup G] {s : Set E} {a : E}

set_option linter.docPrime false in
@[to_additive Inseparable.norm_eq_norm]
theorem Inseparable.norm_eq_norm' {u v : E} (h : Inseparable u v) : ‖u‖ = ‖v‖ :=
  h.map continuous_norm' |>.eq

set_option linter.docPrime false in
@[to_additive Inseparable.nnnorm_eq_nnnorm]
theorem Inseparable.nnnorm_eq_nnnorm' {u v : E} (h : Inseparable u v) : ‖u‖₊ = ‖v‖₊ :=
  h.map continuous_nnnorm' |>.eq

theorem Inseparable.enorm_eq_enorm {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    {u v : E} (h : Inseparable u v) : ‖u‖ₑ = ‖v‖ₑ :=
  h.map continuous_enorm |>.eq

@[deprecated (since := "2025-12-23")]
alias Inseparable.enorm_eq_enorm' := Inseparable.enorm_eq_enorm

@[to_additive]
theorem mem_closure_one_iff_norm {x : E} : x ∈ closure ({1} : Set E) ↔ ‖x‖ = 0 := by
  rw [← closedBall_zero', mem_closedBall_one_iff, (norm_nonneg' x).ge_iff_eq']

@[to_additive]
theorem closure_one_eq : closure ({1} : Set E) = { x | ‖x‖ = 0 } :=
  Set.ext fun _x => mem_closure_one_iff_norm

section

variable {l : Filter α} {f : α → E}

@[to_additive Filter.Tendsto.norm]
theorem Filter.Tendsto.norm' (h : Tendsto f l (𝓝 a)) : Tendsto (fun x => ‖f x‖) l (𝓝 ‖a‖) :=
  tendsto_norm'.comp h

@[to_additive Filter.Tendsto.nnnorm]
theorem Filter.Tendsto.nnnorm' (h : Tendsto f l (𝓝 a)) : Tendsto (fun x => ‖f x‖₊) l (𝓝 ‖a‖₊) :=
  Tendsto.comp continuous_nnnorm'.continuousAt h


end

section

variable [TopologicalSpace α] {f : α → E} {s : Set α} {a : α}

@[to_additive (attr := fun_prop) Continuous.norm]
theorem Continuous.norm' : Continuous f → Continuous fun x => ‖f x‖ :=
  continuous_norm'.comp

@[to_additive (attr := fun_prop) Continuous.nnnorm]
theorem Continuous.nnnorm' : Continuous f → Continuous fun x => ‖f x‖₊ :=
  continuous_nnnorm'.comp

end
end SeminormedGroup

section ContinuousENorm

variable [TopologicalSpace E] [ContinuousENorm E] {a : E} {l : Filter α} {f : α → E}

lemma Filter.Tendsto.enorm (h : Tendsto f l (𝓝 a)) : Tendsto (‖f ·‖ₑ) l (𝓝 ‖a‖ₑ) :=
  .comp continuous_enorm.continuousAt h

@[deprecated (since := "2025-12-23")] alias Filter.Tendsto.enorm' := Filter.Tendsto.enorm

end ContinuousENorm

section SeminormedGroup

variable [SeminormedGroup E] [SeminormedGroup F] [SeminormedGroup G] {s : Set E} {a : E}

section

variable [TopologicalSpace α] {f : α → E} {s : Set α} {a : α}

@[to_additive (attr := fun_prop) ContinuousAt.norm]
theorem ContinuousAt.norm' {a : α} (h : ContinuousAt f a) : ContinuousAt (fun x => ‖f x‖) a :=
  Tendsto.norm' h

@[to_additive (attr := fun_prop) ContinuousAt.nnnorm]
theorem ContinuousAt.nnnorm' {a : α} (h : ContinuousAt f a) : ContinuousAt (fun x => ‖f x‖₊) a :=
  Tendsto.nnnorm' h

@[to_additive ContinuousWithinAt.norm]
theorem ContinuousWithinAt.norm' {s : Set α} {a : α} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => ‖f x‖) s a :=
  Tendsto.norm' h

@[to_additive ContinuousWithinAt.nnnorm]
theorem ContinuousWithinAt.nnnorm' {s : Set α} {a : α} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => ‖f x‖₊) s a :=
  Tendsto.nnnorm' h

@[to_additive (attr := fun_prop) ContinuousOn.norm]
theorem ContinuousOn.norm' {s : Set α} (h : ContinuousOn f s) : ContinuousOn (fun x => ‖f x‖) s :=
  fun x hx => (h x hx).norm'

@[to_additive (attr := fun_prop) ContinuousOn.nnnorm]
theorem ContinuousOn.nnnorm' {s : Set α} (h : ContinuousOn f s) :
    ContinuousOn (fun x => ‖f x‖₊) s := fun x hx => (h x hx).nnnorm'

end

/-- If `‖y‖ → ∞`, then we can assume `y ≠ x` for any fixed `x`. -/
@[to_additive eventually_ne_of_tendsto_norm_atTop /-- If `‖y‖→∞`, then we can assume `y≠x` for any
fixed `x` -/]
theorem eventually_ne_of_tendsto_norm_atTop' {l : Filter α} {f : α → E}
    (h : Tendsto (fun y => ‖f y‖) l atTop) (x : E) : ∀ᶠ y in l, f y ≠ x :=
  (h.eventually_ne_atTop _).mono fun _x => ne_of_apply_ne norm

@[to_additive]
theorem SeminormedGroup.mem_closure_iff :
    a ∈ closure s ↔ ∀ ε, 0 < ε → ∃ b ∈ s, ‖a⁻¹ * b‖ < ε := by
  simp [Metric.mem_closure_iff, dist_eq_norm_inv_mul]

@[to_additive]
theorem SeminormedGroup.tendstoUniformlyOn_one {f : ι → κ → G} {s : Set κ} {l : Filter ι} :
    TendstoUniformlyOn f 1 l s ↔ ∀ ε > 0, ∀ᶠ i in l, ∀ x ∈ s, ‖f i x‖ < ε := by
  simp only [tendstoUniformlyOn_iff, Pi.one_apply, dist_one_left]

@[to_additive]
theorem SeminormedGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_one {f : ι → κ → G}
    {l : Filter ι} {l' : Filter κ} :
    UniformCauchySeqOnFilter f l l' ↔ TendstoUniformlyOnFilter
      (fun n : ι × ι => fun z => (f n.fst z)⁻¹ * f n.snd z) 1 (l ×ˢ l) l' := by
  refine ⟨fun hf u hu => ?_, fun hf u hu => ?_⟩
  · obtain ⟨ε, hε, H⟩ := uniformity_basis_dist.mem_uniformity_iff.mp hu
    refine
      (hf { p : G × G | dist p.fst p.snd < ε } <| dist_mem_uniformity hε).mono fun x hx =>
        H 1 ((f x.fst.fst x.snd)⁻¹ * f x.fst.snd x.snd) ?_
    simpa [dist_eq_norm_inv_mul, norm_div_rev] using hx
  · obtain ⟨ε, hε, H⟩ := uniformity_basis_dist.mem_uniformity_iff.mp hu
    refine
      (hf { p : G × G | dist p.fst p.snd < ε } <| dist_mem_uniformity hε).mono fun x hx =>
        H (f x.fst.fst x.snd) (f x.fst.snd x.snd) ?_
    simpa [dist_eq_norm_inv_mul, norm_div_rev] using hx

@[to_additive]
theorem SeminormedGroup.uniformCauchySeqOn_iff_tendstoUniformlyOn_one {f : ι → κ → G} {s : Set κ}
    {l : Filter ι} :
    UniformCauchySeqOn f l s ↔
      TendstoUniformlyOn (fun n : ι × ι => fun z => (f n.fst z)⁻¹ * f n.snd z) 1 (l ×ˢ l) s := by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter,
    uniformCauchySeqOn_iff_uniformCauchySeqOnFilter,
    SeminormedGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_one]

end SeminormedGroup

section SeminormedCommGroup

variable [SeminormedCommGroup E] [SeminormedCommGroup F] {a b : E} {r : ℝ}

@[to_additive]
theorem tendsto_iff_norm_div_tendsto_zero {f : α → E} {a : Filter α} {b : E} :
    Tendsto f a (𝓝 b) ↔ Tendsto (fun e => ‖f e / b‖) a (𝓝 0) := by
  simp only [← dist_eq_norm_div, ← tendsto_iff_dist_tendsto_zero]

@[to_additive]
theorem SeminormedCommGroup.mem_closure_iff {s : Set E} :
    a ∈ closure s ↔ ∀ ε, 0 < ε → ∃ b ∈ s, ‖a / b‖ < ε := by
  simp [Metric.mem_closure_iff, dist_eq_norm_div]

@[to_additive]
theorem tendsto_norm_div_self (x : E) : Tendsto (fun a => ‖a / x‖) (𝓝 x) (𝓝 0) := by
  simpa [dist_eq_norm_div] using
    tendsto_id.dist (tendsto_const_nhds : Tendsto (fun _a => (x : E)) (𝓝 x) _)

@[to_additive]
theorem tendsto_norm_div_self_nhdsGE (x : E) : Tendsto (fun a ↦ ‖a / x‖) (𝓝 x) (𝓝[≥] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_norm_div_self x, by simp⟩

open Finset

@[to_additive]
theorem controlled_prod_of_mem_closure {s : Subgroup E} (hg : a ∈ closure (s : Set E)) {b : ℕ → ℝ}
    (b_pos : ∀ n, 0 < b n) :
    ∃ v : ℕ → E,
      Tendsto (fun n => ∏ i ∈ range (n + 1), v i) atTop (𝓝 a) ∧
        (∀ n, v n ∈ s) ∧ ‖(v 0)⁻¹ * a‖ < b 0 ∧ ∀ n, 0 < n → ‖v n‖ < b n := by
  obtain ⟨u : ℕ → E, u_in : ∀ n, u n ∈ s, lim_u : Tendsto u atTop (𝓝 a)⟩ :=
    mem_closure_iff_seq_limit.mp hg
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, ∀ n ≥ n₀, ‖(u n)⁻¹ * a‖ < b 0 :=
    haveI : { x | ‖x⁻¹ * a‖ < b 0 } ∈ 𝓝 a := by
      simp_rw [← dist_eq_norm_inv_mul]
      exact Metric.ball_mem_nhds _ (b_pos _)
    Filter.tendsto_atTop'.mp lim_u _ this
  set z : ℕ → E := fun n => u (n + n₀)
  have lim_z : Tendsto z atTop (𝓝 a) := lim_u.comp (tendsto_add_atTop_nat n₀)
  have mem_𝓤 : ∀ n, { p : E × E | ‖p.1⁻¹ * p.2‖ < b (n + 1) } ∈ 𝓤 E := fun n => by
    simpa [← dist_eq_norm_inv_mul] using Metric.dist_mem_uniformity (b_pos <| n + 1)
  obtain ⟨φ : ℕ → ℕ, φ_extr : StrictMono φ, hφ : ∀ n, ‖(z (φ (n + 1)))⁻¹ * z (φ n)‖ < b (n + 1)⟩ :=
    lim_z.cauchySeq.subseq_mem mem_𝓤
  set w : ℕ → E := z ∘ φ
  have hw : Tendsto w atTop (𝓝 a) := lim_z.comp φ_extr.tendsto_atTop
  set v : ℕ → E := fun i => if i = 0 then w 0 else (w (i - 1))⁻¹ * w i
  refine ⟨v, ?_, ?_, hn₀ _ (n₀.le_add_left _), ?_⟩
  · apply hw.congr (fun n ↦ ?_)
    rw [Finset.prod_range_succ']
    have : ∏ k ∈ range n, v (k + 1) = (v 0)⁻¹ * w n := by
      apply prod_range_induction _ _ (by simp [v]) _ (fun k hk ↦ ?_)
      simp only [↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false, add_tsub_cancel_right, v]
      group
    simp [this]
  · rintro ⟨⟩
    · change w 0 ∈ s
      apply u_in
    · exact s.mul_mem (s.inv_mem (u_in _)) (u_in _)
  · intro l hl
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := Nat.exists_eq_succ_of_ne_zero hl.ne'
    rw [← norm_inv']
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right,
      mul_inv_rev, inv_inv, v]
    apply hφ

@[to_additive]
theorem controlled_prod_of_mem_closure_range {j : E →* F} {b : F}
    (hb : b ∈ closure (j.range : Set F)) {f : ℕ → ℝ} (b_pos : ∀ n, 0 < f n) :
    ∃ a : ℕ → E,
      Tendsto (fun n => ∏ i ∈ range (n + 1), j (a i)) atTop (𝓝 b) ∧
        ‖(j (a 0))⁻¹ * b‖ < f 0 ∧ ∀ n, 0 < n → ‖j (a n)‖ < f n := by
  obtain ⟨v, sum_v, v_in, hv₀, hv_pos⟩ := controlled_prod_of_mem_closure hb b_pos
  choose g hg using v_in
  exact
    ⟨g, by simpa [← hg] using sum_v, by simpa [hg 0] using hv₀,
      fun n hn => by simpa [hg] using hv_pos n hn⟩

end SeminormedCommGroup

section NormedGroup

variable [NormedGroup E] {a b : E}

/-- See `tendsto_norm_one` for a version with full neighborhoods. -/
@[to_additive /-- See `tendsto_norm_zero` for a version with full neighborhoods. -/]
lemma tendsto_norm_nhdsNE_one : Tendsto (norm : E → ℝ) (𝓝[≠] 1) (𝓝[>] 0) :=
  tendsto_norm_one.inf <| tendsto_principal_principal.2 fun _ hx ↦ norm_pos_iff'.2 hx

@[to_additive]
theorem tendsto_norm_inv_mul_self_nhdsNE (a : E) :
    Tendsto (fun x => ‖x⁻¹ * a‖) (𝓝[≠] a) (𝓝[>] 0) := by
  apply (tendsto_norm_inv_mul_self a).inf
  apply tendsto_principal_principal.2 (fun _x hx => norm_pos_iff'.2 ?_)
  simpa [inv_mul_eq_one] using hx

variable (E)

/-- A version of `comap_norm_nhdsGT_zero` for a multiplicative normed group. -/
@[to_additive comap_norm_nhdsGT_zero]
lemma comap_norm_nhdsGT_zero' : comap norm (𝓝[>] 0) = 𝓝[≠] (1 : E) := by
  simp [nhdsWithin, comap_norm_nhds_one, Set.preimage, Set.compl_def]

@[to_additive]
theorem tendsto_norm_div_self_nhdsNE {E : Type*} [NormedCommGroup E] (a : E) :
    Tendsto (fun x => ‖x / a‖) (𝓝[≠] a) (𝓝[>] 0) := by
  simp_rw [← norm_inv_mul]
  exact tendsto_norm_inv_mul_self_nhdsNE a

end NormedGroup
