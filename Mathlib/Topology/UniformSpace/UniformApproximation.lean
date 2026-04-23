/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Continuous
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.NhdsWithin

/-!
# Uniform approximation

In this file, we give lemmas ensuring that a function is continuous if it can be approximated
uniformly by continuous functions. We give various versions, within a set or the whole space, at
a single point or at all points, with locally uniform approximation or uniform approximation. All
the statements are derived from a statement about locally uniform approximation within a set at
a point, called `continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt`.

## Implementation notes

Most results hold under weaker assumptions of locally uniform approximation. In a first section,
we prove the results under these weaker assumptions. Then, we derive the results on uniform
convergence from them.

## Tags

Uniform limit, uniform convergence, tends uniformly to
-/

public section


noncomputable section

open Topology Uniformity Filter SetRel Set Uniform

variable {α β ι : Type*} [TopologicalSpace α] [UniformSpace β]
variable {F : ι → α → β} {f : α → β} {s s' : Set α} {x : α} {p : Filter ι} {g : ι → α}

/-- A function which can be locally uniformly approximated by functions which are continuous
within a set at a point is continuous within this set at this point. -/
theorem continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt (hx : x ∈ s)
    (L : ∀ u ∈ 𝓤 β, ∃ t ∈ 𝓝[s] x, ∃ F : α → β, ContinuousWithinAt F s x ∧ ∀ y ∈ t, (f y, F y) ∈ u) :
    ContinuousWithinAt f s x := by
  refine Uniform.continuousWithinAt_iff'_left.2 fun u₀ hu₀ => ?_
  obtain ⟨u₁, h₁, u₁₀⟩ : ∃ u ∈ 𝓤 β, u ○ u ⊆ u₀ := comp_mem_uniformity_sets hu₀
  obtain ⟨u₂, h₂, hsymm, u₂₁⟩ : ∃ u ∈ 𝓤 β, (∀ {a b}, (a, b) ∈ u → (b, a) ∈ u) ∧ u ○ u ⊆ u₁ :=
    comp_symm_of_uniformity h₁
  rcases L u₂ h₂ with ⟨t, tx, F, hFc, hF⟩
  have A : ∀ᶠ y in 𝓝[s] x, (f y, F y) ∈ u₂ := Eventually.mono tx hF
  have B : ∀ᶠ y in 𝓝[s] x, (F y, F x) ∈ u₂ := Uniform.continuousWithinAt_iff'_left.1 hFc h₂
  have C : ∀ᶠ y in 𝓝[s] x, (f y, F x) ∈ u₁ :=
    (A.and B).mono fun y hy => u₂₁ (prodMk_mem_comp hy.1 hy.2)
  have : (F x, f x) ∈ u₁ :=
    u₂₁ (prodMk_mem_comp (refl_mem_uniformity h₂) (hsymm (A.self_of_nhdsWithin hx)))
  exact C.mono fun y hy => u₁₀ <| prodMk_mem_comp hy this

/-- A function which can be locally uniformly approximated by functions which are continuous at
a point is continuous at this point. -/
theorem continuousAt_of_locally_uniform_approx_of_continuousAt
    (L : ∀ u ∈ 𝓤 β, ∃ t ∈ 𝓝 x, ∃ F, ContinuousAt F x ∧ ∀ y ∈ t, (f y, F y) ∈ u) :
    ContinuousAt f x := by
  rw [← continuousWithinAt_univ]
  apply continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt (mem_univ _) _
  simpa only [exists_prop, nhdsWithin_univ, continuousWithinAt_univ] using L

/-- A function which can be locally uniformly approximated by functions which are continuous
on a set is continuous on this set. -/
theorem continuousOn_of_locally_uniform_approx_of_continuousWithinAt
    (L : ∀ x ∈ s, ∀ u ∈ 𝓤 β, ∃ t ∈ 𝓝[s] x, ∃ F,
      ContinuousWithinAt F s x ∧ ∀ y ∈ t, (f y, F y) ∈ u) :
    ContinuousOn f s := fun x hx =>
  continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt hx (L x hx)

/-- A function which can be uniformly approximated by functions which are continuous on a set
is continuous on this set. -/
theorem continuousOn_of_uniform_approx_of_continuousOn
    (L : ∀ u ∈ 𝓤 β, ∃ F, ContinuousOn F s ∧ ∀ y ∈ s, (f y, F y) ∈ u) : ContinuousOn f s :=
  continuousOn_of_locally_uniform_approx_of_continuousWithinAt fun _x hx u hu =>
    ⟨s, self_mem_nhdsWithin, (L u hu).imp fun _F hF => ⟨hF.1.continuousWithinAt hx, hF.2⟩⟩

/-- A function which can be locally uniformly approximated by continuous functions is continuous. -/
theorem continuous_of_locally_uniform_approx_of_continuousAt
    (L : ∀ x : α, ∀ u ∈ 𝓤 β, ∃ t ∈ 𝓝 x, ∃ F, ContinuousAt F x ∧ ∀ y ∈ t, (f y, F y) ∈ u) :
    Continuous f :=
  continuous_iff_continuousAt.2 fun x =>
    continuousAt_of_locally_uniform_approx_of_continuousAt (L x)

/-- A function which can be uniformly approximated by continuous functions is continuous. -/
theorem continuous_of_uniform_approx_of_continuous
    (L : ∀ u ∈ 𝓤 β, ∃ F, Continuous F ∧ ∀ y, (f y, F y) ∈ u) : Continuous f :=
  continuousOn_univ.mp <|
    continuousOn_of_uniform_approx_of_continuousOn <| by
      simpa [continuousOn_univ] using L

/-!
### Uniform limits

From the previous statements on uniform approximation, we deduce continuity results for uniform
limits.
-/


/-- A locally uniform limit on a set of functions which are continuous on this set is itself
continuous on this set. -/
protected theorem TendstoLocallyUniformlyOn.continuousOn (h : TendstoLocallyUniformlyOn F f p s)
    (hc : ∃ᶠ n in p, ContinuousOn (F n) s) : ContinuousOn f s := by
  refine continuousOn_of_locally_uniform_approx_of_continuousWithinAt fun x hx u hu => ?_
  rcases h u hu x hx with ⟨t, ht, H⟩
  rcases (hc.and_eventually H).exists with ⟨n, hFc, hF⟩
  exact ⟨t, ht, ⟨F n, hFc.continuousWithinAt hx, hF⟩⟩

/-- A uniform limit on a set of functions which are continuous on this set is itself continuous
on this set. -/
protected theorem TendstoUniformlyOn.continuousOn (h : TendstoUniformlyOn F f p s)
    (hc : ∃ᶠ n in p, ContinuousOn (F n) s) : ContinuousOn f s :=
  h.tendstoLocallyUniformlyOn.continuousOn hc

/-- A locally uniform limit of continuous functions is continuous. -/
protected theorem TendstoLocallyUniformly.continuous (h : TendstoLocallyUniformly F f p)
    (hc : ∃ᶠ n in p, Continuous (F n)) : Continuous f :=
  continuousOn_univ.mp <|
    h.tendstoLocallyUniformlyOn.continuousOn <| hc.mono fun _n hn => hn.continuousOn

/-- A uniform limit of continuous functions is continuous. -/
protected theorem TendstoUniformly.continuous (h : TendstoUniformly F f p)
    (hc : ∃ᶠ n in p, Continuous (F n)) : Continuous f :=
  h.tendstoLocallyUniformly.continuous hc

/-!
### Composing limits under uniform convergence

In general, if `Fₙ` converges pointwise to a function `f`, and `gₙ` tends to `x`, it is not true
that `Fₙ gₙ` tends to `f x`. It is true however if the convergence of `Fₙ` to `f` is uniform. In
this paragraph, we prove variations around this statement.
-/


/-- If `Fₙ` converges locally uniformly on a neighborhood of `x` within a set `s` to a function `f`
which is continuous at `x` within `s`, and `gₙ` tends to `x` within `s`, then `Fₙ (gₙ)` tends
to `f x`. -/
theorem tendsto_comp_of_locally_uniform_limit_within (h : ContinuousWithinAt f s x)
    (hg : Tendsto g p (𝓝[s] x))
    (hunif : ∀ u ∈ 𝓤 β, ∃ t ∈ 𝓝[s] x, ∀ᶠ n in p, ∀ y ∈ t, (f y, F n y) ∈ u) :
    Tendsto (fun n => F n (g n)) p (𝓝 (f x)) := by
  refine Uniform.tendsto_nhds_right.2 fun u₀ hu₀ => ?_
  obtain ⟨u₁, h₁, u₁₀⟩ : ∃ u ∈ 𝓤 β, u ○ u ⊆ u₀ := comp_mem_uniformity_sets hu₀
  rcases hunif u₁ h₁ with ⟨s, sx, hs⟩
  have A : ∀ᶠ n in p, g n ∈ s := hg sx
  have B : ∀ᶠ n in p, (f x, f (g n)) ∈ u₁ := hg (Uniform.continuousWithinAt_iff'_right.1 h h₁)
  exact B.mp <| A.mp <| hs.mono fun y H1 H2 H3 => u₁₀ <| prodMk_mem_comp H3 <| H1 _ H2

/-- If `Fₙ` converges locally uniformly on a neighborhood of `x` to a function `f` which is
continuous at `x`, and `gₙ` tends to `x`, then `Fₙ (gₙ)` tends to `f x`. -/
theorem tendsto_comp_of_locally_uniform_limit (h : ContinuousAt f x) (hg : Tendsto g p (𝓝 x))
    (hunif : ∀ u ∈ 𝓤 β, ∃ t ∈ 𝓝 x, ∀ᶠ n in p, ∀ y ∈ t, (f y, F n y) ∈ u) :
    Tendsto (fun n => F n (g n)) p (𝓝 (f x)) := by
  rw [← continuousWithinAt_univ] at h
  rw [← nhdsWithin_univ] at hunif hg
  exact tendsto_comp_of_locally_uniform_limit_within h hg hunif

/-- If `Fₙ` tends locally uniformly to `f` on a set `s`, and `gₙ` tends to `x` within `s`, then
`Fₙ gₙ` tends to `f x` if `f` is continuous at `x` within `s` and `x ∈ s`. -/
theorem TendstoLocallyUniformlyOn.tendsto_comp (h : TendstoLocallyUniformlyOn F f p s)
    (hf : ContinuousWithinAt f s x) (hx : x ∈ s) (hg : Tendsto g p (𝓝[s] x)) :
    Tendsto (fun n => F n (g n)) p (𝓝 (f x)) :=
  tendsto_comp_of_locally_uniform_limit_within hf hg fun u hu => h u hu x hx

/-- If `Fₙ` tends uniformly to `f` on a set `s`, and `gₙ` tends to `x` within `s`, then `Fₙ gₙ`
tends to `f x` if `f` is continuous at `x` within `s`. -/
theorem TendstoUniformlyOn.tendsto_comp (h : TendstoUniformlyOn F f p s)
    (hf : ContinuousWithinAt f s x) (hg : Tendsto g p (𝓝[s] x)) :
    Tendsto (fun n => F n (g n)) p (𝓝 (f x)) :=
  tendsto_comp_of_locally_uniform_limit_within hf hg fun u hu => ⟨s, self_mem_nhdsWithin, h u hu⟩

/-- If `Fₙ` tends locally uniformly to `f`, and `gₙ` tends to `x`, then `Fₙ gₙ` tends to `f x`. -/
theorem TendstoLocallyUniformly.tendsto_comp (h : TendstoLocallyUniformly F f p)
    (hf : ContinuousAt f x) (hg : Tendsto g p (𝓝 x)) : Tendsto (fun n => F n (g n)) p (𝓝 (f x)) :=
  tendsto_comp_of_locally_uniform_limit hf hg fun u hu => h u hu x

/-- If `Fₙ` tends uniformly to `f`, and `gₙ` tends to `x`, then `Fₙ gₙ` tends to `f x`. -/
theorem TendstoUniformly.tendsto_comp (h : TendstoUniformly F f p) (hf : ContinuousAt f x)
    (hg : Tendsto g p (𝓝 x)) : Tendsto (fun n => F n (g n)) p (𝓝 (f x)) :=
  h.tendstoLocallyUniformly.tendsto_comp hf hg

/-!
### Uniform approximation and limit of uniformly continuous functions.
-/
section UniformContinuous
variable {α β ι : Type*} [UniformSpace α] [UniformSpace β]
variable {F : ι → α → β} {f : α → β} {s : Set α} {p : Filter ι}

/-- A function which can be uniformly approximated by functions which are uniformly continuous on a
set is uniformly continuous on this set. -/
theorem uniformContinuousOn_of_uniform_approx_of_uniformContinuousOn
    (h : ∀ u ∈ 𝓤 β, ∃ F : α → β, UniformContinuousOn F s ∧ ∀ y ∈ s, (f y, F y) ∈ u) :
    UniformContinuousOn f s := by
  simp_rw [uniformContinuousOn_iff_restrict, uniformContinuous_def] at h ⊢
  intro u hu
  obtain ⟨v, hv, hvsymm, hvu⟩ := comp_comp_symm_mem_uniformity_sets hu
  obtain ⟨F, hF, hFv⟩ := h v hv
  filter_upwards [hF v hv] with x hx
  exact hvu <| prodMk_mem_comp (prodMk_mem_comp (hFv _ x.1.prop) hx)
      <| hvsymm.symm (f x.2) (F x.2) <| hFv _ x.2.prop

/-- A function which can be uniformly approximated by uniformly continuous functions is uniformly
continuous. -/
theorem uniformContinuous_of_uniform_approx_of_uniformContinuous
    (h : ∀ u ∈ 𝓤 β, ∃ F : α → β, UniformContinuous F ∧ ∀ y, (f y, F y) ∈ u) :
    UniformContinuous f :=
  uniformContinuousOn_univ.mp <| uniformContinuousOn_of_uniform_approx_of_uniformContinuousOn
    <| by simpa [uniformContinuousOn_univ] using h

/-- A uniform limit on a set of functions which are uniformly continuous on this set is itself
uniformly continuous on this set. -/
protected theorem TendstoUniformlyOn.uniformContinuousOn (h : TendstoUniformlyOn F f p s)
    (hc : ∃ᶠ n in p, UniformContinuousOn (F n) s) : UniformContinuousOn f s :=
  uniformContinuousOn_of_uniform_approx_of_uniformContinuousOn fun u hu ↦
    let ⟨i, hF⟩ := (hc.and_eventually (h u hu)).exists
    ⟨F i, hF⟩

/-- A uniform limit of uniformly continuous functions is uniformly continuous. -/
protected theorem TendstoUniformly.uniformContinuous (h : TendstoUniformly F f p)
    (hc : ∃ᶠ n in p, UniformContinuous (F n)) : UniformContinuous f :=
  uniformContinuous_of_uniform_approx_of_uniformContinuous fun u hu ↦
    let ⟨i, hF⟩ := (hc.and_eventually (h u hu)).exists
    ⟨F i, hF⟩

end UniformContinuous
