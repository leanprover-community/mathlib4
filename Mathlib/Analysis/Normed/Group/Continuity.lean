/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Sequences

/-!
# Continuity of the norm on (semi)normed groups

## Tags

normed group
-/

@[expose] public section

variable {𝓕 α ι κ E F G : Type*}

open Filter Function Metric Bornology
open ENNReal Filter NNReal Uniformity Pointwise Topology

section SeminormedGroup

variable [SeminormedGroup E] [SeminormedGroup F] [SeminormedGroup G] {s : Set E}
  {a a₁ a₂ b c d : E} {r r₁ r₂ : ℝ}

@[to_additive of_forall_le_norm]
lemma DiscreteTopology.of_forall_le_norm' (hpos : 0 < r) (hr : ∀ x : E, x ≠ 1 → r ≤ ‖x‖) :
    DiscreteTopology E :=
  .of_forall_le_dist hpos fun x y hne ↦ by
    simp only [dist_eq_norm_div]
    exact hr _ (div_ne_one.2 hne)

open Finset

variable [FunLike 𝓕 E F]

section NNNorm

@[to_additive nontrivialTopology_iff_exists_nnnorm_ne_zero]
theorem nontrivialTopology_iff_exists_nnnorm_ne_zero' :
    NontrivialTopology E ↔ ∃ x : E, ‖x‖₊ ≠ 0 := by
  simp_rw [TopologicalSpace.nontrivial_iff_exists_not_inseparable, Metric.inseparable_iff_nndist,
    nndist_eq_nnnorm_div]
  exact ⟨fun ⟨x, y, hxy⟩ => ⟨_, hxy⟩, fun ⟨x, hx⟩ => ⟨x, 1, by simpa using hx⟩⟩

@[to_additive indiscreteTopology_iff_forall_nnnorm_eq_zero]
theorem indiscreteTopology_iff_forall_nnnorm_eq_zero' :
    IndiscreteTopology E ↔ ∀ x : E, ‖x‖₊ = 0 := by
  simpa using nontrivialTopology_iff_exists_nnnorm_ne_zero' (E := E).not

variable (E) in
@[to_additive exists_nnnorm_ne_zero]
theorem exists_nnnorm_ne_zero' [NontrivialTopology E] : ∃ x : E, ‖x‖₊ ≠ 0 :=
  nontrivialTopology_iff_exists_nnnorm_ne_zero'.1 ‹_›

@[to_additive (attr := nontriviality) nnnorm_eq_zero]
theorem IndiscreteTopology.nnnorm_eq_zero' [IndiscreteTopology E] : ∀ x : E, ‖x‖₊ = 0 :=
  indiscreteTopology_iff_forall_nnnorm_eq_zero'.1 ‹_›

alias ⟨_, NontrivialTopology.of_exists_nnnorm_ne_zero'⟩ :=
  nontrivialTopology_iff_exists_nnnorm_ne_zero'
alias ⟨_, NontrivialTopology.of_exists_nnnorm_ne_zero⟩ :=
  nontrivialTopology_iff_exists_nnnorm_ne_zero
attribute [to_additive existing NontrivialTopology.of_exists_nnnorm_ne_zero]
  NontrivialTopology.of_exists_nnnorm_ne_zero'

alias ⟨_, IndiscreteTopology.of_forall_nnnorm_eq_zero'⟩ :=
  indiscreteTopology_iff_forall_nnnorm_eq_zero'
alias ⟨_, IndiscreteTopology.of_forall_nnnorm_eq_zero⟩ :=
  indiscreteTopology_iff_forall_nnnorm_eq_zero
attribute [to_additive existing IndiscreteTopology.of_forall_nnnorm_eq_zero]
  IndiscreteTopology.of_forall_nnnorm_eq_zero'

@[to_additive nontrivialTopology_iff_exists_norm_ne_zero]
theorem nontrivialTopology_iff_exists_norm_ne_zero' :
    NontrivialTopology E ↔ ∃ x : E, ‖x‖ ≠ 0 := by
  simp [nontrivialTopology_iff_exists_nnnorm_ne_zero', ← NNReal.ne_iff]

@[to_additive indiscreteTopology_iff_forall_norm_eq_zero]
theorem indiscreteTopology_iff_forall_norm_eq_zero' :
    IndiscreteTopology E ↔ ∀ x : E, ‖x‖ = 0 := by
  simpa using nontrivialTopology_iff_exists_norm_ne_zero' (E := E).not

variable (E) in
@[to_additive exists_norm_ne_zero]
theorem exists_norm_ne_zero' [NontrivialTopology E] : ∃ x : E, ‖x‖ ≠ 0 :=
  nontrivialTopology_iff_exists_norm_ne_zero'.1 ‹_›

@[to_additive (attr := nontriviality) IndiscreteTopology.norm_eq_zero]
theorem IndiscreteTopology.norm_eq_zero' [IndiscreteTopology E] : ∀ x : E, ‖x‖ = 0 :=
  indiscreteTopology_iff_forall_norm_eq_zero'.1 ‹_›

alias ⟨_, NontrivialTopology.of_exists_norm_ne_zero'⟩ :=
  nontrivialTopology_iff_exists_norm_ne_zero'
alias ⟨_, NontrivialTopology.of_exists_norm_ne_zero⟩ :=
  nontrivialTopology_iff_exists_norm_ne_zero
attribute [to_additive existing NontrivialTopology.of_exists_norm_ne_zero]
  NontrivialTopology.of_exists_norm_ne_zero'

alias ⟨_, IndiscreteTopology.of_forall_norm_eq_zero'⟩ :=
  indiscreteTopology_iff_forall_norm_eq_zero'
alias ⟨_, IndiscreteTopology.of_forall_norm_eq_zero⟩ :=
  indiscreteTopology_iff_forall_norm_eq_zero
attribute [to_additive existing IndiscreteTopology.of_forall_norm_eq_zero]
  IndiscreteTopology.of_forall_norm_eq_zero'

end NNNorm

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
theorem tendsto_iff_norm_div_tendsto_zero {f : α → E} {a : Filter α} {b : E} :
    Tendsto f a (𝓝 b) ↔ Tendsto (fun e => ‖f e / b‖) a (𝓝 0) := by
  simp only [← dist_eq_norm_div, ← tendsto_iff_dist_tendsto_zero]

@[to_additive]
theorem tendsto_one_iff_norm_tendsto_zero {f : α → E} {a : Filter α} :
    Tendsto f a (𝓝 1) ↔ Tendsto (‖f ·‖) a (𝓝 0) :=
  tendsto_iff_norm_div_tendsto_zero.trans <| by simp only [div_one]

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
theorem tendsto_norm_div_self (x : E) : Tendsto (fun a => ‖a / x‖) (𝓝 x) (𝓝 0) := by
  simpa [dist_eq_norm_div] using
    tendsto_id.dist (tendsto_const_nhds : Tendsto (fun _a => (x : E)) (𝓝 x) _)

@[to_additive]
theorem tendsto_norm_div_self_nhdsGE (x : E) : Tendsto (fun a ↦ ‖a / x‖) (𝓝 x) (𝓝[≥] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_norm_div_self x, by simp⟩

@[to_additive tendsto_norm]
theorem tendsto_norm' {x : E} : Tendsto (fun a => ‖a‖) (𝓝 x) (𝓝 ‖x‖) := by
  simpa using tendsto_id.dist (tendsto_const_nhds : Tendsto (fun _a => (1 : E)) _ _)

/-- See `tendsto_norm_one` for a version with pointed neighborhoods. -/
@[to_additive /-- See `tendsto_norm_zero` for a version with pointed neighborhoods. -/]
theorem tendsto_norm_one : Tendsto (fun a : E => ‖a‖) (𝓝 1) (𝓝 0) := by
  simpa using tendsto_norm_div_self (1 : E)

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
theorem SeminormedCommGroup.mem_closure_iff :
    a ∈ closure s ↔ ∀ ε, 0 < ε → ∃ b ∈ s, ‖a / b‖ < ε := by
  simp [Metric.mem_closure_iff, dist_eq_norm_div]

@[to_additive]
theorem SeminormedGroup.tendstoUniformlyOn_one {f : ι → κ → G} {s : Set κ} {l : Filter ι} :
    TendstoUniformlyOn f 1 l s ↔ ∀ ε > 0, ∀ᶠ i in l, ∀ x ∈ s, ‖f i x‖ < ε := by
  simp only [tendstoUniformlyOn_iff, Pi.one_apply, dist_one_left]

@[to_additive]
theorem SeminormedGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_one {f : ι → κ → G}
    {l : Filter ι} {l' : Filter κ} :
    UniformCauchySeqOnFilter f l l' ↔
      TendstoUniformlyOnFilter (fun n : ι × ι => fun z => f n.fst z / f n.snd z) 1 (l ×ˢ l) l' := by
  refine ⟨fun hf u hu => ?_, fun hf u hu => ?_⟩
  · obtain ⟨ε, hε, H⟩ := uniformity_basis_dist.mem_uniformity_iff.mp hu
    refine
      (hf { p : G × G | dist p.fst p.snd < ε } <| dist_mem_uniformity hε).mono fun x hx =>
        H 1 (f x.fst.fst x.snd / f x.fst.snd x.snd) ?_
    simpa [dist_eq_norm_div, norm_div_rev] using hx
  · obtain ⟨ε, hε, H⟩ := uniformity_basis_dist.mem_uniformity_iff.mp hu
    refine
      (hf { p : G × G | dist p.fst p.snd < ε } <| dist_mem_uniformity hε).mono fun x hx =>
        H (f x.fst.fst x.snd) (f x.fst.snd x.snd) ?_
    simpa [dist_eq_norm_div, norm_div_rev] using hx

@[to_additive]
theorem SeminormedGroup.uniformCauchySeqOn_iff_tendstoUniformlyOn_one {f : ι → κ → G} {s : Set κ}
    {l : Filter ι} :
    UniformCauchySeqOn f l s ↔
      TendstoUniformlyOn (fun n : ι × ι => fun z => f n.fst z / f n.snd z) 1 (l ×ˢ l) s := by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter,
    uniformCauchySeqOn_iff_uniformCauchySeqOnFilter,
    SeminormedGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_one]

end SeminormedGroup

section SeminormedCommGroup

variable [SeminormedCommGroup E] [SeminormedCommGroup F] {a b : E} {r : ℝ}

open Finset

@[to_additive]
theorem controlled_prod_of_mem_closure {s : Subgroup E} (hg : a ∈ closure (s : Set E)) {b : ℕ → ℝ}
    (b_pos : ∀ n, 0 < b n) :
    ∃ v : ℕ → E,
      Tendsto (fun n => ∏ i ∈ range (n + 1), v i) atTop (𝓝 a) ∧
        (∀ n, v n ∈ s) ∧ ‖v 0 / a‖ < b 0 ∧ ∀ n, 0 < n → ‖v n‖ < b n := by
  obtain ⟨u : ℕ → E, u_in : ∀ n, u n ∈ s, lim_u : Tendsto u atTop (𝓝 a)⟩ :=
    mem_closure_iff_seq_limit.mp hg
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, ∀ n ≥ n₀, ‖u n / a‖ < b 0 :=
    haveI : { x | ‖x / a‖ < b 0 } ∈ 𝓝 a := by
      simp_rw [← dist_eq_norm_div]
      exact Metric.ball_mem_nhds _ (b_pos _)
    Filter.tendsto_atTop'.mp lim_u _ this
  set z : ℕ → E := fun n => u (n + n₀)
  have lim_z : Tendsto z atTop (𝓝 a) := lim_u.comp (tendsto_add_atTop_nat n₀)
  have mem_𝓤 : ∀ n, { p : E × E | ‖p.1 / p.2‖ < b (n + 1) } ∈ 𝓤 E := fun n => by
    simpa [← dist_eq_norm_div] using Metric.dist_mem_uniformity (b_pos <| n + 1)
  obtain ⟨φ : ℕ → ℕ, φ_extr : StrictMono φ, hφ : ∀ n, ‖z (φ <| n + 1) / z (φ n)‖ < b (n + 1)⟩ :=
    lim_z.cauchySeq.subseq_mem mem_𝓤
  set w : ℕ → E := z ∘ φ
  have hw : Tendsto w atTop (𝓝 a) := lim_z.comp φ_extr.tendsto_atTop
  set v : ℕ → E := fun i => if i = 0 then w 0 else w i / w (i - 1)
  refine ⟨v, Tendsto.congr (Finset.eq_prod_range_div' w) hw, ?_, hn₀ _ (n₀.le_add_left _), ?_⟩
  · rintro ⟨⟩
    · change w 0 ∈ s
      apply u_in
    · apply s.div_mem <;> apply u_in
  · intro l hl
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := Nat.exists_eq_succ_of_ne_zero hl.ne'
    apply hφ

@[to_additive]
theorem controlled_prod_of_mem_closure_range {j : E →* F} {b : F}
    (hb : b ∈ closure (j.range : Set F)) {f : ℕ → ℝ} (b_pos : ∀ n, 0 < f n) :
    ∃ a : ℕ → E,
      Tendsto (fun n => ∏ i ∈ range (n + 1), j (a i)) atTop (𝓝 b) ∧
        ‖j (a 0) / b‖ < f 0 ∧ ∀ n, 0 < n → ‖j (a n)‖ < f n := by
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
theorem tendsto_norm_div_self_nhdsNE (a : E) : Tendsto (fun x => ‖x / a‖) (𝓝[≠] a) (𝓝[>] 0) :=
  (tendsto_norm_div_self a).inf <|
    tendsto_principal_principal.2 fun _x hx => norm_pos_iff'.2 <| div_ne_one.2 hx

variable (E)

/-- A version of `comap_norm_nhdsGT_zero` for a multiplicative normed group. -/
@[to_additive comap_norm_nhdsGT_zero]
lemma comap_norm_nhdsGT_zero' : comap norm (𝓝[>] 0) = 𝓝[≠] (1 : E) := by
  simp [nhdsWithin, comap_norm_nhds_one, Set.preimage, Set.compl_def]

end NormedGroup
