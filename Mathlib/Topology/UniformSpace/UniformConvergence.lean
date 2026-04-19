/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Uniform convergence

A sequence of functions `Fₙ` (with values in a metric space) converges uniformly on a set `s` to a
function `f` if, for all `ε > 0`, for all large enough `n`, one has for all `y ∈ s` the inequality
`dist (f y, Fₙ y) < ε`. Under uniform convergence, many properties of the `Fₙ` pass to the limit,
most notably continuity. We prove this in the file, defining the notion of uniform convergence
in the more general setting of uniform spaces, and with respect to an arbitrary indexing set
endowed with a filter (instead of just `ℕ` with `atTop`).

## Main results

Let `α` be a topological space, `β` a uniform space, `Fₙ` and `f` be functions from `α` to `β`
(where the index `n` belongs to an indexing type `ι` endowed with a filter `p`).

* `TendstoUniformlyOn F f p s`: the fact that `Fₙ` converges uniformly to `f` on `s`. This means
  that, for any entourage `u` of the diagonal, for large enough `n` (with respect to `p`), one has
  `(f y, Fₙ y) ∈ u` for all `y ∈ s`.
* `TendstoUniformly F f p`: same notion with `s = univ`.
* `TendstoUniformlyOn.continuousOn`: a uniform limit on a set of functions which are continuous
  on this set is itself continuous on this set.
* `TendstoUniformly.continuous`: a uniform limit of continuous functions is continuous.
* `TendstoUniformlyOn.tendsto_comp`: If `Fₙ` tends uniformly to `f` on a set `s`, and `gₙ` tends
  to `x` within `s`, then `Fₙ gₙ` tends to `f x` if `f` is continuous at `x` within `s`.
* `TendstoUniformly.tendsto_comp`: If `Fₙ` tends uniformly to `f`, and `gₙ` tends to `x`, then
  `Fₙ gₙ` tends to `f x`.

Finally, we introduce the notion of a uniform Cauchy sequence, which is to uniform
convergence what a Cauchy sequence is to the usual notion of convergence.

## Implementation notes

We derive most of our initial results from an auxiliary definition `TendstoUniformlyOnFilter`.
This definition in and of itself can sometimes be useful, e.g., when studying the local behavior
of the `Fₙ` near a point, which would typically look like `TendstoUniformlyOnFilter F f p (𝓝 x)`.
Still, while this may be the "correct" definition (see
`tendstoUniformlyOn_iff_tendstoUniformlyOnFilter`), it is somewhat unwieldy to work with in
practice. Thus, we provide the more traditional definition in `TendstoUniformlyOn`.

## Tags

Uniform limit, uniform convergence, tends uniformly to
-/

@[expose] public section

noncomputable section

open Topology Uniformity Filter Set Uniform

variable {α β γ ι : Type*} [UniformSpace β]
variable {F : ι → α → β} {f : α → β} {s s' : Set α} {x : α} {p : Filter ι} {p' : Filter α}

/-!
### Different notions of uniform convergence

We define uniform convergence, on a set or in the whole space.
-/

/-- A sequence of functions `Fₙ` converges uniformly on a filter `p'` to a limiting function `f`
with respect to the filter `p` if, for any entourage of the diagonal `u`, one has
`p ×ˢ p'`-eventually `(f x, Fₙ x) ∈ u`. -/
def TendstoUniformlyOnFilter (F : ι → α → β) (f : α → β) (p : Filter ι) (p' : Filter α) :=
  ∀ u ∈ 𝓤 β, ∀ᶠ n : ι × α in p ×ˢ p', (f n.snd, F n.fst n.snd) ∈ u

/--
A sequence of functions `Fₙ` converges uniformly on a filter `p'` to a limiting function `f` w.r.t.
filter `p` iff the function `(n, x) ↦ (f x, Fₙ x)` converges along `p ×ˢ p'` to the uniformity.
In other words: one knows nothing about the behavior of `x` in this limit besides it being in `p'`.
-/
theorem tendstoUniformlyOnFilter_iff_tendsto :
    TendstoUniformlyOnFilter F f p p' ↔
      Tendsto (fun q : ι × α => (f q.2, F q.1 q.2)) (p ×ˢ p') (𝓤 β) :=
  Iff.rfl

/-- A sequence of functions `Fₙ` converges uniformly on a set `s` to a limiting function `f` with
respect to the filter `p` if, for any entourage of the diagonal `u`, one has `p`-eventually
`(f x, Fₙ x) ∈ u` for all `x ∈ s`. -/
def TendstoUniformlyOn (F : ι → α → β) (f : α → β) (p : Filter ι) (s : Set α) :=
  ∀ u ∈ 𝓤 β, ∀ᶠ n in p, ∀ x : α, x ∈ s → (f x, F n x) ∈ u

theorem tendstoUniformlyOn_iff_tendstoUniformlyOnFilter :
    TendstoUniformlyOn F f p s ↔ TendstoUniformlyOnFilter F f p (𝓟 s) := by
  simp only [TendstoUniformlyOn, TendstoUniformlyOnFilter]
  apply forall₂_congr
  simp_rw [eventually_prod_principal_iff]
  simp

alias ⟨TendstoUniformlyOn.tendstoUniformlyOnFilter, TendstoUniformlyOnFilter.tendstoUniformlyOn⟩ :=
  tendstoUniformlyOn_iff_tendstoUniformlyOnFilter

/-- A sequence of functions `Fₙ` converges uniformly on a set `s` to a limiting function `f` w.r.t.
filter `p` iff the function `(n, x) ↦ (f x, Fₙ x)` converges along `p ×ˢ 𝓟 s` to the uniformity.
In other words: one knows nothing about the behavior of `x` in this limit besides it being in `s`.
-/
theorem tendstoUniformlyOn_iff_tendsto :
    TendstoUniformlyOn F f p s ↔
    Tendsto (fun q : ι × α => (f q.2, F q.1 q.2)) (p ×ˢ 𝓟 s) (𝓤 β) := by
  simp [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter, tendstoUniformlyOnFilter_iff_tendsto]

/-- A sequence of functions `Fₙ` converges uniformly to a limiting function `f` with respect to a
filter `p` if, for any entourage of the diagonal `u`, one has `p`-eventually
`(f x, Fₙ x) ∈ u` for all `x`. -/
@[informal "uniform convergence"]
@[informal "uniform convergence"]
def TendstoUniformly (F : ι → α → β) (f : α → β) (p : Filter ι) :=
  ∀ u ∈ 𝓤 β, ∀ᶠ n in p, ∀ x : α, (f x, F n x) ∈ u

theorem tendstoUniformlyOn_univ : TendstoUniformlyOn F f p univ ↔ TendstoUniformly F f p := by
  simp [TendstoUniformlyOn, TendstoUniformly]

theorem tendstoUniformly_iff_tendstoUniformlyOnFilter :
    TendstoUniformly F f p ↔ TendstoUniformlyOnFilter F f p ⊤ := by
  rw [← tendstoUniformlyOn_univ, tendstoUniformlyOn_iff_tendstoUniformlyOnFilter, principal_univ]

theorem TendstoUniformly.tendstoUniformlyOnFilter (h : TendstoUniformly F f p) :
    TendstoUniformlyOnFilter F f p ⊤ := by rwa [← tendstoUniformly_iff_tendstoUniformlyOnFilter]

theorem tendstoUniformlyOn_iff_tendstoUniformly_comp_coe :
    TendstoUniformlyOn F f p s ↔ TendstoUniformly (fun i (x : s) => F i x) (f ∘ (↑)) p :=
  forall₂_congr fun u _ => by simp

lemma tendstoUniformlyOn_iff_restrict {K : Set α} : TendstoUniformlyOn F f p K ↔
    TendstoUniformly (fun n : ι => K.restrict (F n)) (K.restrict f) p :=
  tendstoUniformlyOn_iff_tendstoUniformly_comp_coe

/-- A sequence of functions `Fₙ` converges uniformly to a limiting function `f` w.r.t.
filter `p` iff the function `(n, x) ↦ (f x, Fₙ x)` converges along `p ×ˢ ⊤` to the uniformity.
In other words: one knows nothing about the behavior of `x` in this limit.
-/
theorem tendstoUniformly_iff_tendsto :
    TendstoUniformly F f p ↔ Tendsto (fun q : ι × α => (f q.2, F q.1 q.2)) (p ×ˢ ⊤) (𝓤 β) := by
  simp [tendstoUniformly_iff_tendstoUniformlyOnFilter, tendstoUniformlyOnFilter_iff_tendsto]

/-- Uniform convergence implies pointwise convergence. -/
theorem TendstoUniformlyOnFilter.tendsto_at (h : TendstoUniformlyOnFilter F f p p')
    (hx : 𝓟 {x} ≤ p') : Tendsto (fun n => F n x) p <| 𝓝 (f x) := by
  refine Uniform.tendsto_nhds_right.mpr fun u hu => mem_map.mpr ?_
  filter_upwards [(h u hu).curry]
  intro i h
  simpa using h.filter_mono hx

/-- Uniform convergence implies pointwise convergence. -/
theorem TendstoUniformlyOn.tendsto_at (h : TendstoUniformlyOn F f p s) (hx : x ∈ s) :
    Tendsto (fun n => F n x) p <| 𝓝 (f x) :=
  h.tendstoUniformlyOnFilter.tendsto_at
    (le_principal_iff.mpr <| mem_principal.mpr <| singleton_subset_iff.mpr <| hx)

/-- Uniform convergence implies pointwise convergence. -/
theorem TendstoUniformly.tendsto_at (h : TendstoUniformly F f p) (x : α) :
    Tendsto (fun n => F n x) p <| 𝓝 (f x) :=
  h.tendstoUniformlyOnFilter.tendsto_at le_top

theorem TendstoUniformlyOnFilter.mono_left {p'' : Filter ι} (h : TendstoUniformlyOnFilter F f p p')
    (hp : p'' ≤ p) : TendstoUniformlyOnFilter F f p'' p' := fun u hu =>
  (h u hu).filter_mono (p'.prod_mono_left hp)

theorem TendstoUniformlyOnFilter.mono_right {p'' : Filter α} (h : TendstoUniformlyOnFilter F f p p')
    (hp : p'' ≤ p') : TendstoUniformlyOnFilter F f p p'' := fun u hu =>
  (h u hu).filter_mono (p.prod_mono_right hp)

theorem TendstoUniformlyOn.mono (h : TendstoUniformlyOn F f p s) (h' : s' ⊆ s) :
    TendstoUniformlyOn F f p s' :=
  tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mpr
    (h.tendstoUniformlyOnFilter.mono_right (le_principal_iff.mpr <| mem_principal.mpr h'))

theorem TendstoUniformlyOnFilter.congr_inseparable {F' : ι → α → β}
    (hf : TendstoUniformlyOnFilter F f p p')
    (hff' : ∀ᶠ n : ι × α in p ×ˢ p', Inseparable (F n.fst n.snd) (F' n.fst n.snd)) :
    TendstoUniformlyOnFilter F' f p p' := by
  rw [tendstoUniformlyOnFilter_iff_tendsto, uniformity_hasBasis_open.tendsto_right_iff] at hf ⊢
  exact fun i hi => (hf i hi).congr (hff'.mono fun x hx =>
    (Inseparable.rfl.prod hx).mem_open_iff hi.2)

theorem TendstoUniformlyOnFilter.congr {F' : ι → α → β} (hf : TendstoUniformlyOnFilter F f p p')
    (hff' : ∀ᶠ n : ι × α in p ×ˢ p', F n.fst n.snd = F' n.fst n.snd) :
    TendstoUniformlyOnFilter F' f p p' :=
  hf.congr_inseparable (hff'.mono fun _ h => .of_eq h)

theorem TendstoUniformlyOn.congr_inseparable {F' : ι → α → β} (hf : TendstoUniformlyOn F f p s)
    (hff' : ∀ᶠ n in p, ∀ x ∈ s, Inseparable (F n x) (F' n x)) : TendstoUniformlyOn F' f p s := by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter] at hf ⊢
  refine hf.congr_inseparable ?_
  rwa [eventually_prod_principal_iff]

theorem TendstoUniformlyOn.congr {F' : ι → α → β} (hf : TendstoUniformlyOn F f p s)
    (hff' : ∀ᶠ n in p, Set.EqOn (F n) (F' n) s) : TendstoUniformlyOn F' f p s :=
  hf.congr_inseparable (hff'.mono fun _ h _ hx => .of_eq (h hx))

lemma tendstoUniformly_congr_inseparable {F' : ι → α → β}
    (hF : ∀ᶠ x in p, ∀ y, Inseparable (F x y) (F' x y)) :
    TendstoUniformly F f p ↔ TendstoUniformly F' f p := by
  rw [← tendstoUniformlyOn_univ, ← tendstoUniformlyOn_univ]
  exact ⟨fun h => h.congr_inseparable (hF.mono fun _ hx y _ => hx y),
    fun h => h.congr_inseparable (hF.mono fun _ hx y _ => (hx y).symm)⟩

lemma tendstoUniformly_congr {F' : ι → α → β} (hF : F =ᶠ[p] F') :
    TendstoUniformly F f p ↔ TendstoUniformly F' f p :=
  tendstoUniformly_congr_inseparable (hF.mono fun _ hx y => .of_eq (congrFun hx y))

theorem TendstoUniformlyOn.congr_inseparable_right {g : α → β} (hf : TendstoUniformlyOn F f p s)
    (hfg : ∀ x ∈ s, Inseparable (f x) (g x)) : TendstoUniformlyOn F g p s := by
  rw [tendstoUniformlyOn_iff_tendsto, uniformity_hasBasis_open.tendsto_right_iff] at hf ⊢
  refine forall₂_imp (fun i hi hf => ?_) hf
  rw [eventually_prod_principal_iff] at hf ⊢
  exact hf.mono fun x hx y hy => (((hfg y hy).prod .rfl).mem_open_iff hi.2).mp (hx y hy)

theorem TendstoUniformlyOn.congr_right {g : α → β} (hf : TendstoUniformlyOn F f p s)
    (hfg : EqOn f g s) : TendstoUniformlyOn F g p s :=
  hf.congr_inseparable_right fun _ hx => .of_eq (hfg hx)

protected theorem TendstoUniformly.tendstoUniformlyOn (h : TendstoUniformly F f p) :
    TendstoUniformlyOn F f p s :=
  (tendstoUniformlyOn_univ.2 h).mono (subset_univ s)

/-- Composing on the right by a function preserves uniform convergence on a filter -/
theorem TendstoUniformlyOnFilter.comp (h : TendstoUniformlyOnFilter F f p p') (g : γ → α) :
    TendstoUniformlyOnFilter (fun n => F n ∘ g) (f ∘ g) p (p'.comap g) := by
  rw [tendstoUniformlyOnFilter_iff_tendsto] at h ⊢
  exact h.comp (tendsto_id.prodMap tendsto_comap)

/-- Composing on the right by a function preserves uniform convergence on a set -/
theorem TendstoUniformlyOn.comp (h : TendstoUniformlyOn F f p s) (g : γ → α) :
    TendstoUniformlyOn (fun n => F n ∘ g) (f ∘ g) p (g ⁻¹' s) := by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter] at h ⊢
  simpa [TendstoUniformlyOn, comap_principal] using TendstoUniformlyOnFilter.comp h g

/-- Composing on the right by a function preserves uniform convergence -/
theorem TendstoUniformly.comp (h : TendstoUniformly F f p) (g : γ → α) :
    TendstoUniformly (fun n => F n ∘ g) (f ∘ g) p := by
  rw [tendstoUniformly_iff_tendstoUniformlyOnFilter] at h ⊢
  simpa [principal_univ, comap_principal] using h.comp g

/-- Composing on the left by a uniformly continuous function preserves
  uniform convergence on a filter -/
theorem UniformContinuous.comp_tendstoUniformlyOnFilter [UniformSpace γ] {g : β → γ}
    (hg : UniformContinuous g) (h : TendstoUniformlyOnFilter F f p p') :
    TendstoUniformlyOnFilter (fun i => g ∘ F i) (g ∘ f) p p' := fun _u hu => h _ (hg hu)

/-- Composing on the left by a uniformly continuous function preserves
  uniform convergence on a set -/
theorem UniformContinuous.comp_tendstoUniformlyOn [UniformSpace γ] {g : β → γ}
    (hg : UniformContinuous g) (h : TendstoUniformlyOn F f p s) :
    TendstoUniformlyOn (fun i => g ∘ F i) (g ∘ f) p s := fun _u hu => h _ (hg hu)

/-- Composing on the left by a uniformly continuous function preserves uniform convergence -/
theorem UniformContinuous.comp_tendstoUniformly [UniformSpace γ] {g : β → γ}
    (hg : UniformContinuous g) (h : TendstoUniformly F f p) :
    TendstoUniformly (fun i => g ∘ F i) (g ∘ f) p := fun _u hu => h _ (hg hu)

theorem TendstoUniformlyOnFilter.prodMap {ι' α' β' : Type*} [UniformSpace β'] {F' : ι' → α' → β'}
    {f' : α' → β'} {q : Filter ι'} {q' : Filter α'} (h : TendstoUniformlyOnFilter F f p p')
    (h' : TendstoUniformlyOnFilter F' f' q q') :
    TendstoUniformlyOnFilter (fun i : ι × ι' => Prod.map (F i.1) (F' i.2)) (Prod.map f f') (p ×ˢ q)
      (p' ×ˢ q') := by
  rw [tendstoUniformlyOnFilter_iff_tendsto] at h h' ⊢
  rw [uniformity_prod_eq_comap_prod, tendsto_comap_iff, ← map_swap4_prod, tendsto_map'_iff]
  simpa using h.prodMap h'

theorem TendstoUniformlyOn.prodMap {ι' α' β' : Type*} [UniformSpace β'] {F' : ι' → α' → β'}
    {f' : α' → β'} {p' : Filter ι'} {s' : Set α'} (h : TendstoUniformlyOn F f p s)
    (h' : TendstoUniformlyOn F' f' p' s') :
    TendstoUniformlyOn (fun i : ι × ι' => Prod.map (F i.1) (F' i.2)) (Prod.map f f') (p ×ˢ p')
      (s ×ˢ s') := by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter] at h h' ⊢
  simpa only [prod_principal_principal] using h.prodMap h'

theorem TendstoUniformly.prodMap {ι' α' β' : Type*} [UniformSpace β'] {F' : ι' → α' → β'}
    {f' : α' → β'} {p' : Filter ι'} (h : TendstoUniformly F f p) (h' : TendstoUniformly F' f' p') :
    TendstoUniformly (fun i : ι × ι' => Prod.map (F i.1) (F' i.2)) (Prod.map f f') (p ×ˢ p') := by
  rw [← tendstoUniformlyOn_univ, ← univ_prod_univ] at *
  exact h.prodMap h'

theorem TendstoUniformlyOnFilter.prodMk {ι' β' : Type*} [UniformSpace β'] {F' : ι' → α → β'}
    {f' : α → β'} {q : Filter ι'} (h : TendstoUniformlyOnFilter F f p p')
    (h' : TendstoUniformlyOnFilter F' f' q p') :
    TendstoUniformlyOnFilter (fun (i : ι × ι') a => (F i.1 a, F' i.2 a)) (fun a => (f a, f' a))
      (p ×ˢ q) p' :=
  fun u hu => ((h.prodMap h') u hu).diag_of_prod_right

protected theorem TendstoUniformlyOn.prodMk {ι' β' : Type*} [UniformSpace β'] {F' : ι' → α → β'}
    {f' : α → β'} {p' : Filter ι'} (h : TendstoUniformlyOn F f p s)
    (h' : TendstoUniformlyOn F' f' p' s) :
    TendstoUniformlyOn (fun (i : ι × ι') a => (F i.1 a, F' i.2 a)) (fun a => (f a, f' a)) (p ×ˢ p')
      s :=
  (congr_arg _ s.inter_self).mp ((h.prodMap h').comp fun a => (a, a))

theorem TendstoUniformly.prodMk {ι' β' : Type*} [UniformSpace β'] {F' : ι' → α → β'} {f' : α → β'}
    {p' : Filter ι'} (h : TendstoUniformly F f p) (h' : TendstoUniformly F' f' p') :
    TendstoUniformly (fun (i : ι × ι') a => (F i.1 a, F' i.2 a)) (fun a => (f a, f' a)) (p ×ˢ p') :=
  (h.prodMap h').comp fun a => (a, a)

/-- Uniform convergence on a filter `p'` to a constant function is equivalent to convergence in
`p ×ˢ p'`. -/
theorem tendsto_prod_filter_iff {c : β} :
    Tendsto ↿F (p ×ˢ p') (𝓝 c) ↔ TendstoUniformlyOnFilter F (fun _ => c) p p' := by
  simp_rw [nhds_eq_comap_uniformity, tendsto_comap_iff]
  rfl

/-- Uniform convergence on a set `s` to a constant function is equivalent to convergence in
`p ×ˢ 𝓟 s`. -/
theorem tendsto_prod_principal_iff {c : β} :
    Tendsto ↿F (p ×ˢ 𝓟 s) (𝓝 c) ↔ TendstoUniformlyOn F (fun _ => c) p s := by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter]
  exact tendsto_prod_filter_iff

/-- Uniform convergence to a constant function is equivalent to convergence in `p ×ˢ ⊤`. -/
theorem tendsto_prod_top_iff {c : β} :
    Tendsto ↿F (p ×ˢ ⊤) (𝓝 c) ↔ TendstoUniformly F (fun _ => c) p := by
  rw [tendstoUniformly_iff_tendstoUniformlyOnFilter]
  exact tendsto_prod_filter_iff

/-- Uniform convergence on the empty set is vacuously true -/
theorem tendstoUniformlyOn_empty : TendstoUniformlyOn F f p ∅ := fun u _ => by simp

/-- Uniform convergence on a singleton is equivalent to regular convergence -/
theorem tendstoUniformlyOn_singleton_iff_tendsto :
    TendstoUniformlyOn F f p {x} ↔ Tendsto (fun n : ι => F n x) p (𝓝 (f x)) := by
  simp_rw [tendstoUniformlyOn_iff_tendsto, Uniform.tendsto_nhds_right, tendsto_def]
  exact forall₂_congr fun u _ => by simp [preimage]

/-- If a sequence `g` converges to some `b`, then the sequence of constant functions
`fun n ↦ fun a ↦ g n` converges to the constant function `fun a ↦ b` on any set `s` -/
theorem Filter.Tendsto.tendstoUniformlyOnFilter_const {g : ι → β} {b : β} (hg : Tendsto g p (𝓝 b))
    (p' : Filter α) :
    TendstoUniformlyOnFilter (fun n : ι => fun _ : α => g n) (fun _ : α => b) p p' := by
  simpa only [nhds_eq_comap_uniformity, tendsto_comap_iff] using hg.comp (tendsto_fst (g := p'))

/-- If a sequence `g` converges to some `b`, then the sequence of constant functions
`fun n ↦ fun a ↦ g n` converges to the constant function `fun a ↦ b` on any set `s` -/
theorem Filter.Tendsto.tendstoUniformlyOn_const {g : ι → β} {b : β} (hg : Tendsto g p (𝓝 b))
    (s : Set α) : TendstoUniformlyOn (fun n : ι => fun _ : α => g n) (fun _ : α => b) p s :=
  tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mpr (hg.tendstoUniformlyOnFilter_const (𝓟 s))

theorem UniformContinuousOn.tendstoUniformlyOn [UniformSpace α] [UniformSpace γ] {U : Set α}
    {V : Set β} {F : α → β → γ} (hF : UniformContinuousOn ↿F (U ×ˢ V)) (hU : x ∈ U) :
    TendstoUniformlyOn F (F x) (𝓝[U] x) V := by
  set φ := fun q : α × β => ((x, q.2), q)
  rw [tendstoUniformlyOn_iff_tendsto]
  change Tendsto (Prod.map ↿F ↿F ∘ φ) (𝓝[U] x ×ˢ 𝓟 V) (𝓤 γ)
  simp only [nhdsWithin, Filter.prod_eq_inf, comap_inf, inf_assoc, comap_principal, inf_principal]
  refine Tendsto.comp hF
    (Tendsto.inf ?_ <| tendsto_principal_principal.2 fun x hx => ⟨⟨hU, hx.2⟩, hx⟩)
  simp only [uniformity_prod_eq_comap_prod, tendsto_comap_iff,
    nhds_eq_comap_uniformity, comap_comap]
  exact tendsto_comap.prodMk (tendsto_diag_uniformity _ _)

theorem UniformContinuousOn.tendstoUniformly [UniformSpace α] [UniformSpace γ] {U : Set α}
    (hU : U ∈ 𝓝 x) {F : α → β → γ} (hF : UniformContinuousOn ↿F (U ×ˢ (univ : Set β))) :
    TendstoUniformly F (F x) (𝓝 x) := by
  simpa only [tendstoUniformlyOn_univ, nhdsWithin_eq_nhds.2 hU]
    using hF.tendstoUniformlyOn (mem_of_mem_nhds hU)

theorem UniformContinuous₂.tendstoUniformly [UniformSpace α] [UniformSpace γ] {f : α → β → γ}
    (h : UniformContinuous₂ f) : TendstoUniformly f (f x) (𝓝 x) :=
  UniformContinuousOn.tendstoUniformly univ_mem <| by rwa [univ_prod_univ, uniformContinuousOn_univ]

namespace Filter.HasBasis

variable {X ιX ια ιβ : Type*}

/-- An analogue of `Filter.HasBasis.tendsto_right_iff` for `TendstoUniformlyOnFilter`. -/
lemma tendstoUniformlyOnFilter_iff_of_uniformity {F : X → α → β} {f : α → β}
    {l : Filter X} {l' : Filter α} {pβ : ιβ → Prop} {sβ : ιβ → Set (β × β)}
    (hβ : (uniformity β).HasBasis pβ sβ) :
    TendstoUniformlyOnFilter F f l l' ↔
      (∀ i, pβ i → ∀ᶠ n in l ×ˢ l', (f n.2, F n.1 n.2) ∈ sβ i) := by
  rw [tendstoUniformlyOnFilter_iff_tendsto, hβ.tendsto_right_iff]

/-- An analogue of `Filter.HasBasis.tendsto_iff` for `TendstoUniformlyOnFilter`. -/
lemma tendstoUniformlyOnFilter_iff {F : X → α → β} {f : α → β}
    {l : Filter X} {l' : Filter α} {pX : ιX → Prop} {sX : ιX → Set X}
    {pα : ια → Prop} {sα : ια → Set α} {pβ : ιβ → Prop} {sβ : ιβ → Set (β × β)}
    (hl : l.HasBasis pX sX) (hl' : l'.HasBasis pα sα)
    (hβ : (uniformity β).HasBasis pβ sβ) :
    TendstoUniformlyOnFilter F f l l' ↔
      (∀ i, pβ i → ∃ j k, (pX j ∧ pα k) ∧ ∀ x a, x ∈ sX j → a ∈ sα k → (f a, F x a) ∈ sβ i) := by
  simp [hβ.tendstoUniformlyOnFilter_iff_of_uniformity, (hl.prod hl').eventually_iff]

/-- An analogue of `Filter.HasBasis.tendsto_right_iff` for `TendstoUniformlyOn`. -/
lemma tendstoUniformlyOn_iff_of_uniformity {F : X → α → β} {f : α → β}
    {l : Filter X} {s : Set α} {pβ : ιβ → Prop} {sβ : ιβ → Set (β × β)}
    (hβ : (uniformity β).HasBasis pβ sβ) :
    TendstoUniformlyOn F f l s ↔
      (∀ i, pβ i → ∀ᶠ n in l, ∀ x ∈ s, (f x, F n x) ∈ sβ i) := by
  simp_rw [tendstoUniformlyOn_iff_tendsto, hβ.tendsto_right_iff, eventually_prod_principal_iff]

/-- An analogue of `Filter.HasBasis.tendsto_iff` for `TendstoUniformlyOn`. -/
lemma tendstoUniformlyOn_iff {F : X → α → β} {f : α → β}
    {l : Filter X} {s : Set α} {pX : ιX → Prop} {sX : ιX → Set X} {pβ : ιβ → Prop}
    {sβ : ιβ → Set (β × β)} (hl : l.HasBasis pX sX) (hβ : (uniformity β).HasBasis pβ sβ) :
    TendstoUniformlyOn F f l s ↔
      (∀ i, pβ i → ∃ j, pX j ∧ ∀ ⦃x⦄, x ∈ sX j → ∀ a ∈ s, (f a, F x a) ∈ sβ i) := by
  simp [hβ.tendstoUniformlyOn_iff_of_uniformity, hl.eventually_iff]

/-- An analogue of `Filter.HasBasis.tendsto_right_iff` for `TendstoUniformly`. -/
lemma tendstoUniformly_iff_of_uniformity {F : X → α → β} {f : α → β}
    {l : Filter X} {pβ : ιβ → Prop} {sβ : ιβ → Set (β × β)}
    (hβ : (uniformity β).HasBasis pβ sβ) :
    TendstoUniformly F f l ↔
      (∀ i, pβ i → ∀ᶠ n in l, ∀ x, (f x, F n x) ∈ sβ i) := by
  simp_rw [← tendstoUniformlyOn_univ, hβ.tendstoUniformlyOn_iff_of_uniformity, mem_univ,
    true_imp_iff]

/-- An analogue of `Filter.HasBasis.tendsto_iff` for `TendstoUniformly`. -/
lemma tendstoUniformly_iff {F : X → α → β} {f : α → β}
    {l : Filter X} {pX : ιX → Prop} {sX : ιX → Set X} (hl : l.HasBasis pX sX)
    {pβ : ιβ → Prop} {sβ : ιβ → Set (β × β)} (hβ : (uniformity β).HasBasis pβ sβ) :
    TendstoUniformly F f l ↔
      (∀ i, pβ i → ∃ j, pX j ∧ ∀ ⦃x⦄, x ∈ sX j → ∀ a, (f a, F x a) ∈ sβ i) := by
  simp only [hβ.tendstoUniformly_iff_of_uniformity, hl.eventually_iff]

end Filter.HasBasis

/-- A sequence is uniformly Cauchy if eventually all of its pairwise differences are
uniformly bounded -/
def UniformCauchySeqOnFilter (F : ι → α → β) (p : Filter ι) (p' : Filter α) : Prop :=
  ∀ u ∈ 𝓤 β, ∀ᶠ m : (ι × ι) × α in (p ×ˢ p) ×ˢ p', (F m.fst.fst m.snd, F m.fst.snd m.snd) ∈ u

/-- A sequence is uniformly Cauchy if eventually all of its pairwise differences are
uniformly bounded -/
def UniformCauchySeqOn (F : ι → α → β) (p : Filter ι) (s : Set α) : Prop :=
  ∀ u ∈ 𝓤 β, ∀ᶠ m : ι × ι in p ×ˢ p, ∀ x : α, x ∈ s → (F m.fst x, F m.snd x) ∈ u

theorem uniformCauchySeqOn_iff_uniformCauchySeqOnFilter :
    UniformCauchySeqOn F p s ↔ UniformCauchySeqOnFilter F p (𝓟 s) := by
  simp only [UniformCauchySeqOn, UniformCauchySeqOnFilter]
  refine forall₂_congr fun u hu => ?_
  rw [eventually_prod_principal_iff]

theorem UniformCauchySeqOn.uniformCauchySeqOnFilter (hF : UniformCauchySeqOn F p s) :
    UniformCauchySeqOnFilter F p (𝓟 s) := by rwa [← uniformCauchySeqOn_iff_uniformCauchySeqOnFilter]

/-- A sequence that converges uniformly is also uniformly Cauchy -/
theorem TendstoUniformlyOnFilter.uniformCauchySeqOnFilter (hF : TendstoUniformlyOnFilter F f p p') :
    UniformCauchySeqOnFilter F p p' := by
  intro u hu
  rcases comp_symm_of_uniformity hu with ⟨t, ht, htsymm, htmem⟩
  have := tendsto_swap4_prod.eventually ((hF t ht).prod_mk (hF t ht))
  apply this.diag_of_prod_right.mono
  simp only [and_imp, Prod.forall]
  intro n1 n2 x hl hr
  exact htmem <| SetRel.prodMk_mem_comp (htsymm hl) hr

/-- A sequence that converges uniformly is also uniformly Cauchy -/
theorem TendstoUniformlyOn.uniformCauchySeqOn (hF : TendstoUniformlyOn F f p s) :
    UniformCauchySeqOn F p s :=
  uniformCauchySeqOn_iff_uniformCauchySeqOnFilter.mpr
    hF.tendstoUniformlyOnFilter.uniformCauchySeqOnFilter

/-- A uniformly Cauchy sequence converges uniformly to its limit -/
theorem UniformCauchySeqOnFilter.tendstoUniformlyOnFilter_of_tendsto
    (hF : UniformCauchySeqOnFilter F p p')
    (hF' : ∀ᶠ x : α in p', Tendsto (fun n => F n x) p (𝓝 (f x))) :
    TendstoUniformlyOnFilter F f p p' := by
  rcases p.eq_or_neBot with rfl | _
  · simp only [TendstoUniformlyOnFilter, bot_prod, eventually_bot, implies_true]
  -- Proof idea: |f_n(x) - f(x)| ≤ |f_n(x) - f_m(x)| + |f_m(x) - f(x)|. We choose `n`
  -- so that |f_n(x) - f_m(x)| is uniformly small across `s` whenever `m ≥ n`. Then for
  -- a fixed `x`, we choose `m` sufficiently large such that |f_m(x) - f(x)| is small.
  intro u hu
  rcases comp_symm_of_uniformity hu with ⟨t, ht, htsymm, htmem⟩
  -- We will choose n, x, and m simultaneously. n and x come from hF. m comes from hF'
  -- But we need to promote hF' to the full product filter to use it
  have hmc : ∀ᶠ x in (p ×ˢ p) ×ˢ p', Tendsto (fun n : ι => F n x.snd) p (𝓝 (f x.snd)) := by
    rw [eventually_prod_iff]
    exact ⟨fun _ => True, by simp, _, hF', by simp⟩
  -- To apply filter operations we'll need to do some order manipulation
  rw [Filter.eventually_swap_iff]
  have := tendsto_prodAssoc.eventually (tendsto_prod_swap.eventually ((hF t ht).and hmc))
  apply this.curry.mono
  simp only [Equiv.prodAssoc_apply, eventually_and, eventually_const, Prod.snd_swap, Prod.fst_swap,
    and_imp, Prod.forall]
  -- Complete the proof
  intro x n hx hm'
  refine Set.mem_of_mem_of_subset ?_ htmem
  rw [Uniform.tendsto_nhds_right] at hm'
  have := hx.and (hm' ht)
  obtain ⟨m, hm⟩ := this.exists
  exact ⟨F m x, ⟨hm.2, htsymm hm.1⟩⟩

/-- A uniformly Cauchy sequence converges uniformly to its limit -/
theorem UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto (hF : UniformCauchySeqOn F p s)
    (hF' : ∀ x : α, x ∈ s → Tendsto (fun n => F n x) p (𝓝 (f x))) : TendstoUniformlyOn F f p s :=
  tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mpr
    (hF.uniformCauchySeqOnFilter.tendstoUniformlyOnFilter_of_tendsto hF')

theorem UniformCauchySeqOnFilter.mono_left {p'' : Filter ι} (hf : UniformCauchySeqOnFilter F p p')
    (hp : p'' ≤ p) : UniformCauchySeqOnFilter F p'' p' := fun u hu =>
  (hf u hu).filter_mono (p'.prod_mono_left (Filter.prod_mono hp hp))

theorem UniformCauchySeqOnFilter.mono_right {p'' : Filter α} (hf : UniformCauchySeqOnFilter F p p')
    (hp : p'' ≤ p') : UniformCauchySeqOnFilter F p p'' := fun u hu =>
  have := (hf u hu).filter_mono ((p ×ˢ p).prod_mono_right hp)
  this.mono (by simp)

theorem UniformCauchySeqOn.mono (hf : UniformCauchySeqOn F p s) (hss' : s' ⊆ s) :
    UniformCauchySeqOn F p s' := by
  rw [uniformCauchySeqOn_iff_uniformCauchySeqOnFilter] at hf ⊢
  exact hf.mono_right (le_principal_iff.mpr <| mem_principal.mpr hss')

/-- Composing on the right by a function preserves uniform Cauchy sequences -/
theorem UniformCauchySeqOnFilter.comp {γ : Type*} (hf : UniformCauchySeqOnFilter F p p')
    (g : γ → α) : UniformCauchySeqOnFilter (fun n => F n ∘ g) p (p'.comap g) := fun u hu => by
  obtain ⟨pa, hpa, pb, hpb, hpapb⟩ := eventually_prod_iff.mp (hf u hu)
  rw [eventually_prod_iff]
  refine ⟨pa, hpa, pb ∘ g, ?_, fun hx _ hy => hpapb hx hy⟩
  exact eventually_comap.mpr (hpb.mono fun x hx y hy => by simp only [hx, hy, Function.comp_apply])

/-- Composing on the right by a function preserves uniform Cauchy sequences -/
theorem UniformCauchySeqOn.comp {γ : Type*} (hf : UniformCauchySeqOn F p s) (g : γ → α) :
    UniformCauchySeqOn (fun n => F n ∘ g) p (g ⁻¹' s) := by
  rw [uniformCauchySeqOn_iff_uniformCauchySeqOnFilter] at hf ⊢
  simpa only [UniformCauchySeqOn, comap_principal] using hf.comp g

/-- Composing on the left by a uniformly continuous function preserves
uniform Cauchy sequences -/
theorem UniformContinuous.comp_uniformCauchySeqOn [UniformSpace γ] {g : β → γ}
    (hg : UniformContinuous g) (hf : UniformCauchySeqOn F p s) :
    UniformCauchySeqOn (fun n => g ∘ F n) p s := fun _u hu => hf _ (hg hu)

theorem UniformCauchySeqOn.prodMap {ι' α' β' : Type*} [UniformSpace β'] {F' : ι' → α' → β'}
    {p' : Filter ι'} {s' : Set α'} (h : UniformCauchySeqOn F p s)
    (h' : UniformCauchySeqOn F' p' s') :
    UniformCauchySeqOn (fun i : ι × ι' => Prod.map (F i.1) (F' i.2)) (p ×ˢ p') (s ×ˢ s') := by
  intro u hu
  rw [uniformity_prod_eq_prod, mem_map, mem_prod_iff] at hu
  obtain ⟨v, hv, w, hw, hvw⟩ := hu
  simp_rw [mem_prod, and_imp, Prod.forall, Prod.map_apply]
  rw [← Set.image_subset_iff] at hvw
  apply (tendsto_swap4_prod.eventually ((h v hv).prod_mk (h' w hw))).mono
  intro x hx a b ha hb
  exact hvw ⟨_, mk_mem_prod (hx.1 a ha) (hx.2 b hb), rfl⟩

theorem UniformCauchySeqOn.prod {ι' β' : Type*} [UniformSpace β'] {F' : ι' → α → β'}
    {p' : Filter ι'} (h : UniformCauchySeqOn F p s) (h' : UniformCauchySeqOn F' p' s) :
    UniformCauchySeqOn (fun (i : ι × ι') a => (F i.fst a, F' i.snd a)) (p ×ˢ p') s :=
  (congr_arg _ s.inter_self).mp ((h.prodMap h').comp fun a => (a, a))

theorem UniformCauchySeqOn.prod' {β' : Type*} [UniformSpace β'] {F' : ι → α → β'}
    (h : UniformCauchySeqOn F p s) (h' : UniformCauchySeqOn F' p s) :
    UniformCauchySeqOn (fun (i : ι) a => (F i a, F' i a)) p s := fun u hu =>
  have hh : Tendsto (fun x : ι => (x, x)) p (p ×ˢ p) := tendsto_diag
  (hh.prodMap hh).eventually ((h.prod h') u hu)

/-- If a sequence of functions is uniformly Cauchy on a set, then the values at each point form
a Cauchy sequence. -/
theorem UniformCauchySeqOn.cauchy_map [hp : NeBot p] (hf : UniformCauchySeqOn F p s) (hx : x ∈ s) :
    Cauchy (map (fun i => F i x) p) := by
  simp only [cauchy_map_iff, hp, true_and]
  intro u hu
  rw [mem_map]
  filter_upwards [hf u hu] with p hp using hp x hx

/-- If a sequence of functions is uniformly Cauchy on a set, then the values at each point form
a Cauchy sequence.  See `UniformCauchySeqOn.cauchy_map` for the non-`atTop` case. -/
theorem UniformCauchySeqOn.cauchySeq [Nonempty ι] [SemilatticeSup ι]
    (hf : UniformCauchySeqOn F atTop s) (hx : x ∈ s) :
    CauchySeq fun i ↦ F i x :=
  hf.cauchy_map (hp := atTop_neBot) hx

section SeqTendsto

theorem tendstoUniformlyOn_of_seq_tendstoUniformlyOn {l : Filter ι} [l.IsCountablyGenerated]
    (h : ∀ u : ℕ → ι, Tendsto u atTop l → TendstoUniformlyOn (fun n => F (u n)) f atTop s) :
    TendstoUniformlyOn F f l s := by
  rw [tendstoUniformlyOn_iff_tendsto, tendsto_iff_seq_tendsto]
  intro u hu
  rw [tendsto_prod_iff'] at hu
  specialize h (fun n => (u n).fst) hu.1
  rw [tendstoUniformlyOn_iff_tendsto] at h
  exact h.comp (tendsto_id.prodMk hu.2)

theorem TendstoUniformlyOn.seq_tendstoUniformlyOn {l : Filter ι} (h : TendstoUniformlyOn F f l s)
    (u : ℕ → ι) (hu : Tendsto u atTop l) : TendstoUniformlyOn (fun n => F (u n)) f atTop s := by
  rw [tendstoUniformlyOn_iff_tendsto] at h ⊢
  exact h.comp ((hu.comp tendsto_fst).prodMk tendsto_snd)

theorem tendstoUniformlyOn_iff_seq_tendstoUniformlyOn {l : Filter ι} [l.IsCountablyGenerated] :
    TendstoUniformlyOn F f l s ↔
      ∀ u : ℕ → ι, Tendsto u atTop l → TendstoUniformlyOn (fun n => F (u n)) f atTop s :=
  ⟨TendstoUniformlyOn.seq_tendstoUniformlyOn, tendstoUniformlyOn_of_seq_tendstoUniformlyOn⟩

theorem tendstoUniformly_iff_seq_tendstoUniformly {l : Filter ι} [l.IsCountablyGenerated] :
    TendstoUniformly F f l ↔
      ∀ u : ℕ → ι, Tendsto u atTop l → TendstoUniformly (fun n => F (u n)) f atTop := by
  simp_rw [← tendstoUniformlyOn_univ]
  exact tendstoUniformlyOn_iff_seq_tendstoUniformlyOn

end SeqTendsto

section

variable [NeBot p] {L : ι → β} {ℓ : β}

theorem TendstoUniformlyOnFilter.tendsto_of_eventually_tendsto
    (h1 : TendstoUniformlyOnFilter F f p p') (h2 : ∀ᶠ i in p, Tendsto (F i) p' (𝓝 (L i)))
    (h3 : Tendsto L p (𝓝 ℓ)) : Tendsto f p' (𝓝 ℓ) := by
  rw [tendsto_nhds_left]
  intro s hs
  rw [mem_map, Set.preimage, ← eventually_iff]
  obtain ⟨t, ht, hts⟩ := comp3_mem_uniformity hs
  have p1 : ∀ᶠ i in p, (L i, ℓ) ∈ t := tendsto_nhds_left.mp h3 ht
  have p2 : ∀ᶠ i in p, ∀ᶠ x in p', (F i x, L i) ∈ t := by
    filter_upwards [h2] with i h2 using tendsto_nhds_left.mp h2 ht
  have p3 : ∀ᶠ i in p, ∀ᶠ x in p', (f x, F i x) ∈ t := (h1 t ht).curry
  obtain ⟨i, p4, p5, p6⟩ := (p1.and (p2.and p3)).exists
  filter_upwards [p5, p6] with x p5 p6 using hts ⟨F i x, p6, L i, p5, p4⟩

theorem TendstoUniformly.tendsto_of_eventually_tendsto
    (h1 : TendstoUniformly F f p) (h2 : ∀ᶠ i in p, Tendsto (F i) p' (𝓝 (L i)))
    (h3 : Tendsto L p (𝓝 ℓ)) : Tendsto f p' (𝓝 ℓ) :=
  (h1.tendstoUniformlyOnFilter.mono_right le_top).tendsto_of_eventually_tendsto h2 h3

end
