/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.TangentCone.Defs
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Basic properties of tangent cones and sets with unique differentiability property

In this file we prove basic lemmas about `tangentConeAt`, `UniqueDiffWithinAt`,
and `UniqueDiffOn`.
-/

open Filter Set Metric NormedField
open scoped Topology Pointwise

namespace Filter

theorem HasBasis.map₂ {ια ιβ : Type*} {α β γ : Type*} {la : Filter α} {lb : Filter β}
    {pa : ια → Prop} {sa : ια → Set α} {pb : ιβ → Prop} {sb : ιβ → Set β}
    (f : α → β → γ) (ha : la.HasBasis pa sa) (hb : lb.HasBasis pb sb) :
    (la.map₂ f lb).HasBasis (fun i : ια × ιβ ↦ pa i.1 ∧ pb i.2)
      fun i ↦ ((sa i.1).image2 f (sb i.2)) := by
  simpa [map_prod_eq_map₂] using (ha.prod hb).map f.uncurry

@[to_additive]
theorem HasBasis.smul {ια ιβ : Type*} {α β : Type*} [SMul α β]
    {la : Filter α} {lb : Filter β} {pa : ια → Prop} {sa : ια → Set α}
    {pb : ιβ → Prop} {sb : ιβ → Set β}
    (ha : la.HasBasis pa sa) (hb : lb.HasBasis pb sb) :
    (la • lb).HasBasis (fun i : ια × ιβ ↦ pa i.1 ∧ pb i.2) fun i ↦ (sa i.1 • sb i.2) :=
  ha.map₂ (· • ·) hb

theorem HasBasis.eq_top_iff {ι : Sort*} {α : Type*} {l : Filter α} {p : ι → Prop}
    {s : ι → Set α} (h : l.HasBasis p s) : l = ⊤ ↔ ∀ i, p i → s i = univ := by
  simp [← top_le_iff, h.ge_iff]

theorem univ_smul_nhds_zero {G₀ X : Type*} [GroupWithZero G₀] [Zero X] [MulActionWithZero G₀ X]
    [TopologicalSpace G₀] [(𝓝[≠] (0 : G₀)).NeBot] [TopologicalSpace X] [ContinuousSMul G₀ X]
    {s : Set X} (hs : s ∈ 𝓝 0) :
    (univ : Set G₀) • s = univ := by
  refine eq_univ_of_forall fun x ↦ ?_
  have : Tendsto (· • x) (𝓝 (0 : G₀)) (𝓝 0) := by
    rw [← zero_smul G₀ x]
    exact tendsto_id.smul tendsto_const_nhds
  rcases nonempty_of_mem (inter_mem_nhdsWithin {0}ᶜ <| mem_map.1 <| this hs) with ⟨c, hc₀, hc⟩
  refine ⟨c⁻¹, trivial, c • x, hc, ?_⟩
  simp_all

@[simp]
theorem top_smul_nhds_zero {G₀ X : Type*} [GroupWithZero G₀] [Zero X] [MulActionWithZero G₀ X]
    [TopologicalSpace G₀] [(𝓝[≠] (0 : G₀)).NeBot] [TopologicalSpace X] [ContinuousSMul G₀ X] :
    (⊤ : Filter G₀) • 𝓝 (0 : X) = ⊤ := by
  rw [(hasBasis_top.smul (basis_sets _)).eq_top_iff]
  rintro ⟨_, s⟩ ⟨-, hs⟩
  exact univ_smul_nhds_zero hs

end Filter

variable {𝕜 E : Type*}

section SMulMonoid

variable [AddCommMonoid E] [SMul 𝕜 E] [TopologicalSpace E] {s t : Set E} {x : E}

@[gcongr]
theorem tangentConeAt_mono (h : s ⊆ t) : tangentConeAt 𝕜 s x ⊆ tangentConeAt 𝕜 t x := fun y hy ↦
  hy.mono <| by gcongr

@[deprecated (since := "2025-04-27")] alias tangentCone_mono := tangentConeAt_mono

/--
Given `x ∈ s` and a field extension `𝕜 ⊆ 𝕜'`, the tangent cone of `s` at `x` with
respect to `𝕜` is contained in the tangent cone of `s` at `x` with respect to `𝕜'`.
-/
theorem tangentConeAt_mono_field
    {𝕜' : Type*} [Monoid 𝕜'] [SMul 𝕜 𝕜'] [MulAction 𝕜' E] [IsScalarTower 𝕜 𝕜' E] :
    tangentConeAt 𝕜 s x ⊆ tangentConeAt 𝕜' s x := by
  refine fun y hy ↦ hy.mono ?_
  rw [← smul_one_smul (Filter 𝕜')]
  grw [le_top (a := ⊤ • 1)]

theorem Filter.HasBasis.tangentConeAt_eq_biInter_closure {ι} {p : ι → Prop} {U : ι → Set E}
    (h : (𝓝 0).HasBasis p U) :
    tangentConeAt 𝕜 s x = ⋂ (i) (_ : p i), closure ((univ : Set 𝕜) • (U i ∩ (x + ·) ⁻¹' s)) := by
  ext y
  simp only [tangentConeAt, mem_setOf_eq, mem_iInter₂, ← map₂_smul, ← map_prod_eq_map₂,
    ((nhdsWithin_hasBasis h _).top_prod.map _).clusterPt_iff_forall_mem_closure, image_prod,
    image2_smul]

theorem tangentConeAt_eq_biInter_closure :
    tangentConeAt 𝕜 s x = ⋂ U ∈ 𝓝 0, closure ((univ : Set 𝕜) • (U ∩ (x + ·) ⁻¹' s)) :=
  (basis_sets _).tangentConeAt_eq_biInter_closure

variable [ContinuousAdd E]

theorem tangentConeAt_mono_nhds (h : 𝓝[s] x ≤ 𝓝[t] x) :
    tangentConeAt 𝕜 s x ⊆ tangentConeAt 𝕜 t x := by
  refine fun y hy ↦ hy.mono ?_
  gcongr _ • ?_
  rw [nhdsWithin_le_iff]
  suffices Tendsto (x + ·) (𝓝[(x + ·) ⁻¹' s] 0) (𝓝[s] x) from
    this.mono_right h |> tendsto_nhdsWithin_iff.mp |>.2
  refine .inf ?_ (mapsTo_preimage _ _).tendsto
  exact (continuous_add_left x).tendsto' 0 x (add_zero _)

@[deprecated (since := "2025-04-27")] alias tangentCone_mono_nhds := tangentConeAt_mono_nhds

/-- Tangent cone of `s` at `x` depends only on `𝓝[s] x`. -/
theorem tangentConeAt_congr (h : 𝓝[s] x = 𝓝[t] x) : tangentConeAt 𝕜 s x = tangentConeAt 𝕜 t x :=
  Subset.antisymm (tangentConeAt_mono_nhds h.le) (tangentConeAt_mono_nhds h.ge)

@[deprecated (since := "2025-04-27")] alias tangentCone_congr := tangentConeAt_congr

/-- Intersecting with a neighborhood of the point does not change the tangent cone. -/
theorem tangentConeAt_inter_nhds (ht : t ∈ 𝓝 x) : tangentConeAt 𝕜 (s ∩ t) x = tangentConeAt 𝕜 s x :=
  tangentConeAt_congr (nhdsWithin_restrict' _ ht).symm

@[deprecated (since := "2025-04-27")] alias tangentCone_inter_nhds := tangentConeAt_inter_nhds

end SMulMonoid

section SMulGroup

variable [AddCommGroup E] [SMul 𝕜 E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousConstSMul 𝕜 E]
  {s t : Set E} {x : E}

@[simp]
theorem tangentConeAt_closure : tangentConeAt 𝕜 (closure s) x = tangentConeAt 𝕜 s x := by
  refine Subset.antisymm ?_ (tangentConeAt_mono subset_closure)
  simp only [(nhds_basis_opens _).tangentConeAt_eq_biInter_closure]
  refine iInter₂_mono fun U hU ↦ closure_minimal ?_ isClosed_closure
  grw [(isOpenMap_add_left x).preimage_closure_subset_closure_preimage, hU.2.inter_closure,
    set_smul_closure_subset]

end SMulGroup

section TVS

@[simp]
theorem tangentConeAt_univ [DivisionSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    [TopologicalSpace 𝕜] [(𝓝[≠] (0 : 𝕜)).NeBot] [TopologicalSpace E] [ContinuousSMul 𝕜 E] {x : E} :
    tangentConeAt 𝕜 univ x = univ := by
  simp [tangentConeAt]

@[deprecated (since := "2025-04-27")] alias tangentCone_univ := tangentConeAt_univ

/-
TODO: restore, deprecate
/-- Auxiliary lemma ensuring that, under the assumptions defining the tangent cone,
the sequence `d` tends to 0 at infinity. -/
theorem tangentConeAt.lim_zero {α : Type*} (l : Filter α) {c : α → 𝕜} {d : α → E}
    (hc : Tendsto (fun n => ‖c n‖) l atTop) (hd : Tendsto (fun n => c n • d n) l (𝓝 y)) :
    Tendsto d l (𝓝 0) := by
  have : ∀ᶠ n in l, (c n)⁻¹ • c n • d n = d n :=
    (eventually_ne_of_tendsto_norm_atTop hc 0).mono fun n hn ↦ inv_smul_smul₀ hn (d n)
  rw [tendsto_norm_atTop_iff_cobounded] at hc
  simpa using Tendsto.congr' this <| (tendsto_inv₀_cobounded.comp hc).smul hd
-/

end TVS

section Normed
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {x y : E} {s t : Set E}

/-- The tangent cone at a non-isolated point contains `0`. -/
theorem zero_mem_tangentCone {s : Set E} {x : E} (hx : x ∈ closure s) :
    0 ∈ tangentConeAt 𝕜 s x := by
  /- Take a sequence `d n` tending to `0` such that `x + d n ∈ s`. Taking `c n` of the order
  of `1 / (d n) ^ (1/2)`, then `c n` tends to infinity, but `c n • d n` tends to `0`. By definition,
  this shows that `0` belongs to the tangent cone. -/
  obtain ⟨u, -, hu, u_lim⟩ :
      ∃ u, StrictAnti u ∧ (∀ (n : ℕ), 0 < u n ∧ u n < 1) ∧ Tendsto u atTop (𝓝 (0 : ℝ)) :=
    exists_seq_strictAnti_tendsto' one_pos
  choose u_pos u_lt_one using hu
  choose v hvs hvu using fun n ↦ Metric.mem_closure_iff.mp hx _ (mul_pos (u_pos n) (u_pos n))
  let d n := v n - x
  let ⟨r, hr⟩ := exists_one_lt_norm 𝕜
  have A n := exists_nat_pow_near (one_le_inv_iff₀.mpr ⟨u_pos n, (u_lt_one n).le⟩) hr
  choose m hm_le hlt_m using A
  set c := fun n ↦ r ^ (m n + 1)
  have c_lim : Tendsto (fun n ↦ ‖c n‖) atTop atTop := by
    simp only [c, norm_pow]
    refine tendsto_atTop_mono (fun n ↦ (hlt_m n).le) <| .inv_tendsto_nhdsGT_zero ?_
    exact tendsto_nhdsWithin_iff.mpr ⟨u_lim, .of_forall u_pos⟩
  refine ⟨c, d, .of_forall <| by simpa [d], c_lim, ?_⟩
  have Hle n : ‖c n • d n‖ ≤ ‖r‖ * u n := by
    specialize u_pos n
    calc
      ‖c n • d n‖ ≤ (u n)⁻¹ * ‖r‖ * (u n * u n) := by
        simp only [c, norm_smul, norm_pow, pow_succ, norm_mul, d, ← dist_eq_norm']
        gcongr
        exacts [hm_le n, (hvu n).le]
      _ = ‖r‖ * u n := by field_simp
  refine squeeze_zero_norm Hle ?_
  simpa using tendsto_const_nhds.mul u_lim

/-- If `x` is not an accumulation point of `s, then the tangent cone of `s` at `x`
is a subset of `{0}`. -/
theorem tangentConeAt_subset_zero (hx : ¬AccPt x (𝓟 s)) : tangentConeAt 𝕜 s x ⊆ 0 := by
  rintro y ⟨c, d, hds, hc, hcd⟩
  suffices ∀ᶠ n in .atTop, d n = 0 from
    tendsto_nhds_unique hcd <| tendsto_const_nhds.congr' <| this.mono fun n hn ↦ by simp [hn]
  simp only [accPt_iff_frequently, not_frequently, not_and', ne_eq, not_not] at hx
  have : Tendsto (x + d ·) atTop (𝓝 x) := by
    simpa using tendsto_const_nhds.add (tangentConeAt.lim_zero _ hc hcd)
  filter_upwards [this.eventually hx, hds] with n h₁ h₂
  simpa using h₁ h₂

theorem UniqueDiffWithinAt.accPt [Nontrivial E] (h : UniqueDiffWithinAt 𝕜 s x) : AccPt x (𝓟 s) := by
  by_contra! h'
  have : Dense (Submodule.span 𝕜 (0 : Set E) : Set E) :=
    h.1.mono <| by gcongr; exact tangentConeAt_subset_zero h'
  simp [dense_iff_closure_eq] at this

end Normed

section UniqueDiff

/-!
### Properties of `UniqueDiffWithinAt` and `UniqueDiffOn`

This section is devoted to properties of the predicates `UniqueDiffWithinAt` and `UniqueDiffOn`. -/

section Module
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {x y : E} {s t : Set E}

theorem UniqueDiffOn.uniqueDiffWithinAt {s : Set E} {x} (hs : UniqueDiffOn 𝕜 s) (h : x ∈ s) :
    UniqueDiffWithinAt 𝕜 s x :=
  hs x h

@[simp]
theorem uniqueDiffWithinAt_univ : UniqueDiffWithinAt 𝕜 univ x := by
  rw [uniqueDiffWithinAt_iff, tangentConeAt_univ]
  simp

@[simp]
theorem uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E) :=
  fun _ _ => uniqueDiffWithinAt_univ

theorem uniqueDiffOn_empty : UniqueDiffOn 𝕜 (∅ : Set E) :=
  fun _ hx => hx.elim

theorem UniqueDiffWithinAt.congr_pt (h : UniqueDiffWithinAt 𝕜 s x) (hy : x = y) :
    UniqueDiffWithinAt 𝕜 s y := hy ▸ h

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [Module 𝕜' E] [IsScalarTower 𝕜 𝕜' E]

/--
Assume that `E` is a normed vector space over normed fields `𝕜 ⊆ 𝕜'` and that `x ∈ s` is a point
of unique differentiability with respect to the set `s` and the smaller field `𝕜`, then `x` is also
a point of unique differentiability with respect to the set `s` and the larger field `𝕜'`.
-/
theorem UniqueDiffWithinAt.mono_field (h₂s : UniqueDiffWithinAt 𝕜 s x) :
    UniqueDiffWithinAt 𝕜' s x := by
  simp_all only [uniqueDiffWithinAt_iff, and_true]
  apply Dense.mono _ h₂s.1
  trans ↑(Submodule.span 𝕜 (tangentConeAt 𝕜' s x))
  <;> simp [Submodule.span_mono tangentConeAt_mono_field]

/--
Assume that `E` is a normed vector space over normed fields `𝕜 ⊆ 𝕜'` and all points of `s` are
points of unique differentiability with respect to the smaller field `𝕜`, then they are also points
of unique differentiability with respect to the larger field `𝕜`.
-/
theorem UniqueDiffOn.mono_field (h₂s : UniqueDiffOn 𝕜 s) :
    UniqueDiffOn 𝕜' s := fun x hx ↦ (h₂s x hx).mono_field

end Module

section TVS
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {x y : E} {s t : Set E}
variable [ContinuousAdd E] [ContinuousSMul 𝕜 E]

theorem UniqueDiffWithinAt.mono_nhds (h : UniqueDiffWithinAt 𝕜 s x) (st : 𝓝[s] x ≤ 𝓝[t] x) :
    UniqueDiffWithinAt 𝕜 t x := by
  simp only [uniqueDiffWithinAt_iff] at *
  rw [mem_closure_iff_nhdsWithin_neBot] at h ⊢
  exact ⟨h.1.mono <| Submodule.span_mono <| tangentConeAt_mono_nhds st, h.2.mono st⟩

theorem UniqueDiffWithinAt.mono (h : UniqueDiffWithinAt 𝕜 s x) (st : s ⊆ t) :
    UniqueDiffWithinAt 𝕜 t x :=
  h.mono_nhds <| nhdsWithin_mono _ st

theorem uniqueDiffWithinAt_congr (st : 𝓝[s] x = 𝓝[t] x) :
    UniqueDiffWithinAt 𝕜 s x ↔ UniqueDiffWithinAt 𝕜 t x :=
  ⟨fun h => h.mono_nhds <| le_of_eq st, fun h => h.mono_nhds <| le_of_eq st.symm⟩

theorem uniqueDiffWithinAt_inter (ht : t ∈ 𝓝 x) :
    UniqueDiffWithinAt 𝕜 (s ∩ t) x ↔ UniqueDiffWithinAt 𝕜 s x :=
  uniqueDiffWithinAt_congr <| (nhdsWithin_restrict' _ ht).symm

theorem UniqueDiffWithinAt.inter (hs : UniqueDiffWithinAt 𝕜 s x) (ht : t ∈ 𝓝 x) :
    UniqueDiffWithinAt 𝕜 (s ∩ t) x :=
  (uniqueDiffWithinAt_inter ht).2 hs

theorem uniqueDiffWithinAt_inter' (ht : t ∈ 𝓝[s] x) :
    UniqueDiffWithinAt 𝕜 (s ∩ t) x ↔ UniqueDiffWithinAt 𝕜 s x :=
  uniqueDiffWithinAt_congr <| (nhdsWithin_restrict'' _ ht).symm

theorem UniqueDiffWithinAt.inter' (hs : UniqueDiffWithinAt 𝕜 s x) (ht : t ∈ 𝓝[s] x) :
    UniqueDiffWithinAt 𝕜 (s ∩ t) x :=
  (uniqueDiffWithinAt_inter' ht).2 hs

theorem uniqueDiffWithinAt_of_mem_nhds (h : s ∈ 𝓝 x) : UniqueDiffWithinAt 𝕜 s x := by
  simpa only [univ_inter] using uniqueDiffWithinAt_univ.inter h

theorem IsOpen.uniqueDiffWithinAt (hs : IsOpen s) (xs : x ∈ s) : UniqueDiffWithinAt 𝕜 s x :=
  uniqueDiffWithinAt_of_mem_nhds (IsOpen.mem_nhds hs xs)

theorem UniqueDiffOn.inter (hs : UniqueDiffOn 𝕜 s) (ht : IsOpen t) : UniqueDiffOn 𝕜 (s ∩ t) :=
  fun x hx => (hs x hx.1).inter (IsOpen.mem_nhds ht hx.2)

theorem IsOpen.uniqueDiffOn (hs : IsOpen s) : UniqueDiffOn 𝕜 s :=
  fun _ hx => IsOpen.uniqueDiffWithinAt hs hx

end TVS

section Normed
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {x y : E} {s t : Set E}

@[simp]
theorem uniqueDiffWithinAt_closure :
    UniqueDiffWithinAt 𝕜 (closure s) x ↔ UniqueDiffWithinAt 𝕜 s x := by
  simp [uniqueDiffWithinAt_iff]

protected alias ⟨UniqueDiffWithinAt.of_closure, UniqueDiffWithinAt.closure⟩ :=
  uniqueDiffWithinAt_closure

theorem UniqueDiffWithinAt.mono_closure (h : UniqueDiffWithinAt 𝕜 s x) (st : s ⊆ closure t) :
    UniqueDiffWithinAt 𝕜 t x :=
  (h.mono st).of_closure

end Normed

end UniqueDiff
