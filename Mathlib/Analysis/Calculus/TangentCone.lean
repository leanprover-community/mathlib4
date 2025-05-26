/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Module.LinearMapPiProd

/-!
# Tangent cone

In this file, we define two predicates `UniqueDiffWithinAt R s x` and `UniqueDiffOn R s`
ensuring that, if a function has two derivatives, then they have to coincide. As a direct
definition of this fact (quantifying on all target types and all functions) would depend on
universes, we use a more intrinsic definition: if all the possible tangent directions to the set
`s` at the point `x` span a dense subset of the whole subset, it is easy to check that the
derivative has to be unique.

Therefore, we introduce the set of all tangent directions, named `tangentConeAt`,
and express `UniqueDiffWithinAt` and `UniqueDiffOn` in terms of it.
One should however think of this definition as an implementation detail: the only reason to
introduce the predicates `UniqueDiffWithinAt` and `UniqueDiffOn` is to ensure the uniqueness
of the derivative. This is why their names reflect their uses, and not how they are defined.

## Implementation details

Note that this file is imported by `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`. Hence, derivatives
are not defined yet. The property of uniqueness of the derivative is therefore proved in
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`, but based on the properties of the tangent cone we
prove here.
-/

universe u v
open Function Filter Set Bornology
open scoped Topology Pointwise

section Defs

/-- The set of all tangent directions to the set `s` at the point `x`. -/
def tangentConeAt (R : Type*) {E : Type*} [AddCommMonoid E] [SMul R E] [TopologicalSpace E]
    (s : Set E) (x : E) : Set E :=
  {y : E | MapClusterPt y ((⊤ : Filter R) ×ˢ 𝓝[(x + ·) ⁻¹' s] 0) (· • ·).uncurry}

variable (R : Type*) [Semiring R] {E : Type*} [AddCommGroup E] [Module R E] [TopologicalSpace E]

/-- A property ensuring that the tangent cone to `s` at `x` spans a dense subset of the whole space.
The main role of this property is to ensure that the differential within `s` at `x` is unique,
hence this name. The uniqueness it asserts is proved in `UniqueDiffWithinAt.eq` in
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.
To avoid pathologies in dimension 0, we also require that `x` belongs to the closure of `s` (which
is automatic when `E` is not `0`-dimensional). -/
@[mk_iff]
structure UniqueDiffWithinAt (s : Set E) (x : E) : Prop where
  dense_tangentConeAt : Dense (Submodule.span R (tangentConeAt R s x) : Set E)
  mem_closure : x ∈ closure s

@[deprecated (since := "2025-04-27")]
alias UniqueDiffWithinAt.dense_tangentCone := UniqueDiffWithinAt.dense_tangentConeAt

/-- A property ensuring that the tangent cone to `s` at any of its points spans a dense subset of
the whole space. The main role of this property is to ensure that the differential along `s` is
unique, hence this name. The uniqueness it asserts is proved in `UniqueDiffOn.eq` in
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`. -/
def UniqueDiffOn (s : Set E) : Prop :=
  ∀ x ∈ s, UniqueDiffWithinAt R s x

end Defs

section TangentCone

section SMul

variable {R : Type u} {E : Type v} [AddCommMonoid E] [SMul R E] [TopologicalSpace E]
  {s t : Set E} {x y : E}

theorem isClosed_tangentConeAt : IsClosed (tangentConeAt R s x) :=
  isClosed_setOf_clusterPt

theorem mem_tangentConeAt_of_seq {α : Type*} {l : Filter α} [l.NeBot] {c : α → R} {d : α → E}
    (hd₀ : Tendsto d l (𝓝 0)) (hd : ∀ᶠ n in l, x + d n ∈ s)
    (hcd : Tendsto (fun n ↦ c n • d n) l (𝓝 y)) : y ∈ tangentConeAt R s x :=
  .of_comp (tendsto_top.prodMk <| tendsto_nhdsWithin_iff.mpr ⟨hd₀, hd⟩)
    (by simpa [comp_def] using hcd.mapClusterPt)

theorem exists_tendsto_of_mem_tangentConeAt (h : y ∈ tangentConeAt R s x) :
    ∃ (α : Type (max u v)) (l : Filter α), l.NeBot ∧ ∃ (c : α → R) (d : α → E),
      Tendsto d l (𝓝 0) ∧ (∀ n, x + d n ∈ s) ∧ Tendsto (fun n ↦ c n • d n) l (𝓝 y) := by
  rw [tangentConeAt, mem_setOf_eq, MapClusterPt, ClusterPt, ← neBot_inf_comap_iff_map',
    top_prod, nhdsWithin, comap_inf, comap_principal, ← inf_assoc, preimage_preimage,
    ← map_comap_setCoe_val, map_neBot_iff, comap_inf, comap_comap, comap_comap] at h
  exact ⟨_, _, h, fun cd ↦ cd.1.1, fun cd ↦ cd.1.2, tendsto_comap.mono_left inf_le_right,
    Subtype.property, tendsto_comap.mono_left inf_le_left⟩

@[deprecated (since := "2025-04-27")] alias tangentCone_univ := tangentConeAt_univ

@[gcongr]
theorem tangentConeAt_mono (h : s ⊆ t) : tangentConeAt R s x ⊆ tangentConeAt R t x :=
  fun y hy ↦ hy.mono <| by gcongr

@[deprecated (since := "2025-03-06")]
alias tangentCone_mono := tangentConeAt_mono

theorem Filter.HasBasis.tangentConeAt_eq_biInter_closure {ι} {p : ι → Prop} {U : ι → Set E}
    (h : (𝓝 0).HasBasis p U) :
    tangentConeAt R s x = ⋂ (i) (_ : p i), closure ((univ : Set R) • (U i ∩ (x + ·) ⁻¹' s)) := by
  ext y
  simp only [tangentConeAt, MapClusterPt, mem_setOf_eq, mem_iInter₂, image_uncurry_prod,
    ((nhdsWithin_hasBasis h _).top_prod.map _).clusterPt_iff_forall_mem_closure, image2_smul]

theorem tangentConeAt_eq_biInter_closure :
    tangentConeAt R s x = ⋂ U ∈ 𝓝 0, closure ((univ : Set R) • (U ∩ (x + ·) ⁻¹' s)) :=
  (basis_sets _).tangentConeAt_eq_biInter_closure

variable [ContinuousAdd E]

theorem tangentConeAt_mono_nhds (h : 𝓝[s] x ≤ 𝓝[t] x) :
    tangentConeAt R s x ⊆ tangentConeAt R t x := by
  refine fun y hy ↦ hy.mono ?_
  gcongr _ ×ˢ ?_
  refine le_inf inf_le_left <| ?_
  rw [le_principal_iff]
  have : Tendsto (x + ·) (𝓝 0) (𝓝 x) :=
    Continuous.tendsto' (by fun_prop) _ _ (by simp)
  exact this.inf (mapsTo_preimage _ _).tendsto <| h self_mem_nhdsWithin

@[deprecated (since := "2025-03-06")]
alias tangentCone_mono_nhds := tangentConeAt_mono_nhds

@[deprecated (since := "2025-04-27")] alias tangentCone_mono_nhds := tangentConeAt_mono_nhds

/-- Tangent cone of `s` at `x` depends only on `𝓝[s] x`. -/
theorem tangentConeAt_congr (h : 𝓝[s] x = 𝓝[t] x) : tangentConeAt R s x = tangentConeAt R t x :=
  (tangentConeAt_mono_nhds h.le).antisymm (tangentConeAt_mono_nhds h.ge)

@[deprecated (since := "2025-03-06")]
alias tangentCone_congr := tangentConeAt_congr

/-- Intersecting with a neighborhood of the point does not change the tangent cone. -/
theorem tangentConeAt_inter_nhds (ht : t ∈ 𝓝 x) : tangentConeAt R (s ∩ t) x = tangentConeAt R s x :=
  tangentConeAt_congr (nhdsWithin_restrict' _ ht).symm

@[deprecated (since := "2025-03-06")]
alias tangentCone_inter_nhds := tangentConeAt_inter_nhds

theorem mem_closure_of_tangentConeAt_nonempty (h : (tangentConeAt R s x).Nonempty) :
    x ∈ closure s := by
  rcases h with ⟨y, hy⟩
  have : 0 ∈ closure ((x + ·) ⁻¹' s) := by
    have := hy.neBot.mono inf_le_right
    simp_all [mem_closure_iff_nhdsWithin_neBot]
  simpa using map_mem_closure (by fun_prop) this (mapsTo_preimage _ _)

theorem tangentConeAt_of_not_mem_closure (h : x ∉ closure s) : tangentConeAt R s x = ∅ := by
  contrapose! h
  exact mem_closure_of_tangentConeAt_nonempty h

end SMul

variable {R E F : Type*}

section AddCommMonoid

variable [Semiring R] [AddCommMonoid E] [Module R E] [TopologicalSpace E] {s : Set E} {x : E}

@[simp]
theorem tangentConeAt_univ [TopologicalSpace R] [NeBot (𝓝[{c | IsUnit c}] (0 : R))]
    [ContinuousSMul R E] : tangentConeAt R univ x = univ := by
  refine eq_univ_of_forall fun y ↦ ?_
  set l := 𝓝[{c | IsUnit c}] (0 : R)
  have hd : Tendsto (fun c : R ↦ c • y) l (𝓝 0) :=
    .mono_left (Continuous.tendsto' (by fun_prop) _ _ (zero_smul _ y)) nhdsWithin_le_nhds
  have hcd : Tendsto (fun c : R ↦ Ring.inverse c • c • y) l (𝓝 y) :=
    tendsto_const_nhds.congr' <| eventually_mem_nhdsWithin.mono fun c hc ↦ by
      simp [smul_smul, Ring.inverse_mul_cancel c hc]
  exact mem_tangentConeAt_of_seq hd (by simp) hcd

@[deprecated (since := "2025-03-06")]
alias tangentCone_univ := tangentConeAt_univ

variable [AddCommMonoid F] [Module R F] [TopologicalSpace F] {t : Set F} {y : F}

/-- If a continuous linear map maps `s` to `t`,
then it maps the tangent cone of `s` at `x` to the tangent cone of `t` at `f x`. -/
theorem Set.MapsTo.tangentConeAt_of_clm_add_const {f : E →L[R] F} {a : F}
    (h : MapsTo (f · + a) s t) : MapsTo f (tangentConeAt R s x) (tangentConeAt R t (f x + a)) := by
  intro z hz
  refine .of_comp (φ := Prod.map id f) ?_ <|
    ((hz.out.tendsto_comp f.continuous.continuousAt)).congrFun <| .of_forall <| by simp
  refine tendsto_id.prodMap <| .inf (f.continuous.tendsto' _ _ (map_zero f)) ?_
  rw [tendsto_principal_principal]
  intro a ha
  simpa [add_right_comm] using h ha

/-- If a continuous affine map maps `s` to `t`,
then its linar part maps the tangent cone of `s` at `x` to the tangent cone of `t` at `f x`. -/
theorem Set.MapsTo.tangentConeAt_clm {f : E →L[R] F} :
    MapsTo f s t → MapsTo f (tangentConeAt R s x) (tangentConeAt R t (f x)) := by
  simpa using Set.MapsTo.tangentConeAt_of_clm_add_const (f := f) (a := 0)

end AddCommMonoid

section AddCommGroup

variable [Semiring R] [AddCommGroup E] [Module R E] [TopologicalSpace E]
  {s : Set E} {x y : E}

/-- In a topological group, zero belongs to the tangent cone
iff the point belongs to the closure of the set. -/
@[simp]
theorem zero_mem_tangentConeAt_iff [ContinuousAdd E] : 0 ∈ tangentConeAt R s x ↔ x ∈ closure s := by
  refine ⟨fun h ↦ mem_closure_of_tangentConeAt_nonempty ⟨_, h⟩, fun h ↦ ?_⟩
  simp only [tangentConeAt_eq_biInter_closure, mem_iInter₂]
  refine fun U hU ↦ subset_closure ?_
  rcases mem_closure_iff_nhds.mp h (x +ᵥ U) (by simpa) with ⟨_, ⟨y, hyU, rfl⟩, hys⟩
  exact ⟨0, mem_univ 0, y, ⟨hyU, hys⟩, by simp⟩

@[simp]
protected theorem UniqueDiffWithinAt.univ [TopologicalSpace R] [NeBot (𝓝[{c | IsUnit c}] (0 : R))]
    [ContinuousSMul R E] : UniqueDiffWithinAt R (univ : Set E) x where
  dense_tangentCone := by simp
  mem_closure := by simp

@[simp]
protected theorem UniqueDiffOn.univ [TopologicalSpace R] [NeBot (𝓝[{c | IsUnit c}] (0 : R))]
    [ContinuousSMul R E] : UniqueDiffOn R (univ : Set E) := fun _ _ ↦ .univ

variable [ContinuousAdd E] [T1Space E]

theorem tangentConeAt_subset_of_not_accPt (h : ¬AccPt x (𝓟 s)) :
    tangentConeAt R s x ⊆ 0 := by
  intro y hy
  simp only [tangentConeAt_eq_biInter_closure, mem_iInter₂, accPt_iff_nhds] at h hy
  push_neg at h
  rcases h with ⟨U, hUx, hU⟩
  suffices closure ((univ : Set R) • ((x + ·) ⁻¹' (U ∩ s))) ⊆ 0 from
    this <| hy ((x + ·) ⁻¹' U) (mem_map.mp <| Continuous.tendsto' (by fun_prop) _ _ (by simp) hUx)
  refine closure_minimal ?_ isClosed_singleton
  calc
    (univ : Set R) • ((x + ·) ⁻¹' (U ∩ s)) ⊆ (univ : Set R) • ((x + ·) ⁻¹' {x}) := by
      gcongr; assumption
    _ = {0} := by simp

theorem AccPt.of_mem_tangentConeAt_ne_zero (h : y ∈ tangentConeAt R s x) (hy₀ : y ≠ 0) :
    AccPt x (𝓟 s) := by
  contrapose! hy₀
  exact tangentConeAt_subset_of_not_accPt hy₀ h

theorem AccPt.of_tangentConeAt_nontrivial (h : (tangentConeAt R s x).Nontrivial) :
    AccPt x (𝓟 s) :=
  let ⟨_y, hy, hy₀⟩ := h.exists_ne 0; .of_mem_tangentConeAt_ne_zero hy hy₀

end AddCommGroup

section DivisionRing

variable [DivisionRing R] [TopologicalSpace R] [ContinuousAdd R] {s : Set R} {x : R}

theorem tangentConeAt_eq_univ (hx : AccPt x (𝓟 s)) : tangentConeAt R s x = univ := by
  simp only [tangentConeAt_eq_biInter_closure, eq_univ_iff_forall, mem_iInter₂, accPt_iff_nhds]
    at hx ⊢
  refine fun c U hU ↦ subset_closure ?_
  rcases hx (x +ᵥ U) (by simpa) with ⟨_, ⟨⟨y, hy, rfl⟩, hys⟩, hne⟩
  refine ⟨c / y, mem_univ _, _, ⟨hy, hys⟩, div_mul_cancel₀ _ ?_⟩
  simpa using hne

@[simp]
theorem tangentConeAt_eq_univ_iff [T1Space R] : tangentConeAt R s x = univ ↔ AccPt x (𝓟 s) := by
  refine ⟨fun h ↦ .of_tangentConeAt_nontrivial (R := R) ?_, tangentConeAt_eq_univ⟩
  rw [h]
  exact nontrivial_univ

end DivisionRing

section TVSSemiring

variable [Semiring R]
  [AddCommGroup E] [Module R E] [TopologicalSpace E] [ContinuousConstSMul R E] [ContinuousAdd E]
  [AddCommGroup F] [Module R F] [TopologicalSpace F] [ContinuousConstSMul R F] [ContinuousAdd F]
  {s : Set E} {x : E} {t : Set F} {y : F}

@[simp]
theorem tangentConeAt_closure (s : Set E) (x : E) :
    tangentConeAt R (closure s) x = tangentConeAt R s x := by
  refine Subset.antisymm ?_ (tangentConeAt_mono subset_closure)
  simp only [(nhds_basis_opens _).tangentConeAt_eq_biInter_closure,
    ← vadd_eq_add, preimage_vadd, ← closure_vadd, biUnion_univ]
  refine iInter₂_mono fun U hU ↦ closure_minimal ?_ isClosed_closure
  exact (smul_subset_smul_left hU.2.inter_closure).trans <| set_smul_closure_subset _ _

/-- If `y` is a point in the closure of `t`,
then the map `z ↦ (z, 0)` sends the tangent cone of `s` at `x`
to a point in the tangent cone of `s ×ˢ t` at `(x, y)`.

It is possible to prove this theorem without assuming continuity of the operations on `E`,
but we only need it as an auxiliary lemma for `UniqueDiffWithinAt.prod` below. -/
theorem mapsTo_inl_tangentConeAt (hy : y ∈ closure t) :
    MapsTo (·, 0) (tangentConeAt R s x) (tangentConeAt R (s ×ˢ t) (x, y)) := by
  rw [← tangentConeAt_closure (s ×ˢ t), closure_prod_eq]
  have : MapsTo (ContinuousLinearMap.inl R E F · + (0, y)) s (closure s ×ˢ closure t) := by
    simpa [MapsTo, hy] using subset_closure
  convert this.tangentConeAt_of_clm_add_const <;> simp

/-- If `x` is a point in the closure of `s`,
then the map `z ↦ (0, z)` sends the tangent cone of `t` at `y`
to a point in the tangent cone of `s ×ˢ t` at `(x, y)`.

It is possible to prove this theorem without assuming continuity of the operations on `F`,
but we only need it as an auxiliary lemma for `UniqueDiffWithinAt.prod` below. -/
theorem mapsTo_inr_tangentConeAt (hx : x ∈ closure s) :
    MapsTo (0, ·) (tangentConeAt R t y) (tangentConeAt R (s ×ˢ t) (x, y)) := by
  convert ((mapsTo_swap_prod t s).tangentConeAt_clm (f := .prod (.snd ..) (.fst ..))).comp
    (mapsTo_inl_tangentConeAt (R := R) (s := t) hx)

theorem UniqueDiffWithinAt.prod (hs : UniqueDiffWithinAt R s x) (ht : UniqueDiffWithinAt R t y) :
    UniqueDiffWithinAt R (s ×ˢ t) (x, y) where
  dense_tangentCone := by
    refine (hs.dense_tangentCone.prod ht.dense_tangentCone).mono ?_
    rw [← Submodule.prod_coe, ← LinearMap.span_inl_union_inr, SetLike.coe_subset_coe]
    gcongr
    exact union_subset (mapsTo_inl_tangentConeAt ht.2).image_subset
      (mapsTo_inr_tangentConeAt hs.2).image_subset
  mem_closure := by rw [closure_prod_eq]; exact ⟨hs.2, ht.2⟩

theorem UniqueDiffOn.prod (hs : UniqueDiffOn R s) (ht : UniqueDiffOn R t) :
    UniqueDiffOn R (s ×ˢ t) := fun (x, y) ⟨hx, hy⟩ ↦
  (hs x hx).prod (ht y hy)

end TVSSemiring

/-
section TVSNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [ContinuousAdd E] [Module 𝕜 E] [ContinuousSMul 𝕜 E]
  [AddCommGroup F] [TopologicalSpace F] [ContinuousAdd F] [Module 𝕜 F] [ContinuousSMul 𝕜 F]
  {s : Set E} {x : E} {t : Set F} {y : F}

theorem IsCompact.rescale_to_shell (hs : IsCompact s) (hs₀ : s ∈ 𝓝 0) {c : 𝕜} (hc : 1 < ‖c‖)
    (hx : x ≠ 0) : ∃ m : ℤ, c ^ m • x ∈ s \ c⁻¹ • s := by
  have H₁ : Tendsto (c ^ · • x : ℤ → E) atBot (𝓝 0) := by
    sorry -- TODO: 
  have hc₀ : c ≠ 0 := by rintro rfl; simp [one_pos.not_lt] at hc
  have H₂ : Set.Nonempty {m : ℤ | c ^ m • x ∈ s} :=
    Filter.nonempty_of_mem (H₁.eventually hs₀)
  suffices BddAbove {m : ℤ | c ^ m • x ∈ s} by
    use sSup {m : ℤ | c ^ m • x ∈ s}, Int.csSup_mem H₂ this
    rw [mem_inv_smul_set_iff₀ hc₀, smul_smul, Commute.self_zpow₀, ← zpow_add_one₀ hc₀]
    intro h
    simpa using le_csSup this h
  
  sorry


end TVSDivisionRing
-/

section Pi

variable {ι : Type*} {E : ι → Type*} [Semiring R]
    [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, ContinuousAdd (E i)]

@[deprecated (since := "2025-04-27")]
alias subset_tangentCone_prod_right := subset_tangentConeAt_prod_right

/-- The tangent cone of a product contains the tangent cone of each factor. -/
theorem mapsTo_tangentConeAt_pi [DecidableEq ι] [∀ i, ContinuousConstSMul R (E i)]
    {s : ∀ i, Set (E i)} {x : ∀ i, E i} {i : ι} (hi : ∀ j ≠ i, x j ∈ closure (s j)) :
    MapsTo (Pi.single i) (tangentConeAt R (s i) (x i))
      (tangentConeAt R (Set.pi univ s) x) := by
  rw [← tangentConeAt_closure (.pi _ _), closure_pi_set]
  set f : E i →L[R] (∀ i, E i) := .single ..
  convert MapsTo.tangentConeAt_of_clm_add_const (f := f) (a := x - Pi.single i (x i)) _
  · simp [f]
  · intro y hy j _
    rcases eq_or_ne j i with rfl | hj
    · simpa [f] using subset_closure hy
    · simpa [f, hj] using hi j hj

theorem UniqueDiffWithinAt.univ_pi [∀ i, ContinuousConstSMul R (E i)]
    {s : ∀ i, Set (E i)} {x : ∀ i, E i} (h : ∀ i, UniqueDiffWithinAt R (s i) (x i)) :
    UniqueDiffWithinAt R (.pi univ s) x where
  dense_tangentCone := by
    classical
    have := dense_pi univ fun i _ ↦ (h i).dense_tangentCone
    simp only [dense_iff_closure_eq, closure_pi_set, ← Submodule.closure_coe_iSup_map_single,
      ← univ_subset_iff, Submodule.map_span] at this ⊢
    refine this.trans ?_
    gcongr
    refine iSup_le fun i ↦ ?_
    gcongr
    exact (mapsTo_tangentConeAt_pi fun j _ ↦ (h j).2).image_subset
  mem_closure := by
    rw [closure_pi_set]
    exact fun i _ ↦ (h i).2

theorem UniqueDiffWithinAt.pi [TopologicalSpace R] [NeBot (𝓝[{c | IsUnit c}] (0 : R))]
    [∀ i, ContinuousSMul R (E i)] (s : ∀ i, Set (E i)) (x : ∀ i, E i) (I : Set ι)
    (h : ∀ i ∈ I, UniqueDiffWithinAt R (s i) (x i)) : UniqueDiffWithinAt R (Set.pi I s) x := by
  classical
  rw [← Set.univ_pi_piecewise_univ]
  refine UniqueDiffWithinAt.univ_pi fun i => ?_
  by_cases hi : i ∈ I <;> simp [*, UniqueDiffWithinAt.univ]

end Pi

#exit
  

section Normed
variable [NormedAddCommGroup E] [NormedSpace R E]
variable [NormedAddCommGroup F] [NormedSpace R F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {x y : E} {s t : Set E}

@[deprecated (since := "2025-04-27")] alias mapsTo_tangentCone_pi := mapsTo_tangentConeAt_pi

/-- If a subset of a real vector space contains an open segment, then the direction of this
segment belongs to the tangent cone at its endpoints. -/
theorem mem_tangentConeAt_of_openSegment_subset {s : Set G} {x y : G} (h : openSegment ℝ x y ⊆ s) :
    y - x ∈ tangentConeAt ℝ s x := by
  refine mem_tangentConeAt_of_pow_smul one_half_pos.ne' (by norm_num) ?_
  refine (eventually_ne_atTop 0).mono fun n hn ↦ (h ?_)
  rw [openSegment_eq_image]
  refine ⟨(1 / 2) ^ n, ⟨?_, ?_⟩, ?_⟩
  · exact pow_pos one_half_pos _
  · exact pow_lt_one₀ one_half_pos.le one_half_lt_one hn
  · simp only [sub_smul, one_smul, smul_sub]; abel

@[deprecated (since := "2025-04-27")]
alias mem_tangentCone_of_openSegment_subset := mem_tangentConeAt_of_openSegment_subset

/-- If a subset of a real vector space contains a segment, then the direction of this
segment belongs to the tangent cone at its endpoints. -/
theorem mem_tangentConeAt_of_segment_subset {s : Set G} {x y : G} (h : segment ℝ x y ⊆ s) :
    y - x ∈ tangentConeAt ℝ s x :=
  mem_tangentConeAt_of_openSegment_subset ((openSegment_subset_segment ℝ x y).trans h)

@[deprecated (since := "2025-04-27")]
alias mem_tangentCone_of_segment_subset := mem_tangentConeAt_of_segment_subset

/-- In a proper space, the tangent cone at a non-isolated point is nontrivial. -/
theorem tangentConeAt_nonempty_of_properSpace [ProperSpace E]
    {s : Set E} {x : E} (hx : AccPt x (𝓟 s)) :
    (tangentConeAt 𝕜 s x ∩ {0}ᶜ).Nonempty := by
  /- Take a sequence `d n` tending to `0` such that `x + d n ∈ s`. Taking `c n` of the order
  of `1 / d n`. Then `c n • d n` belongs to a fixed annulus. By compactness, one can extract
  a subsequence converging to a limit `l`. Then `l` is nonzero, and by definition it belongs to
  the tangent cone. -/
  obtain ⟨u, -, u_pos, u_lim⟩ :
      ∃ u, StrictAnti u ∧ (∀ (n : ℕ), 0 < u n) ∧ Tendsto u atTop (𝓝 (0 : ℝ)) :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  have A n : ∃ y ∈ closedBall x (u n) ∩ s, y ≠ x :=
    (accPt_iff_nhds).mp hx _ (closedBall_mem_nhds _ (u_pos n))
  choose v hv hvx using A
  choose hvu hvs using hv
  let d := fun n ↦ v n - x
  have M n : x + d n ∈ s \ {x} := by simpa [d] using (hv n).1
  let ⟨r, hr⟩ := exists_one_lt_norm R
  have W n := rescale_to_shell hr zero_lt_one (x := d n) (by simpa using (M n).2)
  choose c c_ne c_le le_c hc using W
  have c_lim : Tendsto (fun n ↦ ‖c n‖) atTop atTop := by
    suffices Tendsto (fun n ↦ ‖c n‖⁻¹ ⁻¹ ) atTop atTop by simpa
    apply tendsto_inv_nhdsGT_zero.comp
    simp only [nhdsWithin, tendsto_inf, tendsto_principal, mem_Ioi, norm_pos_iff, ne_eq,
      eventually_atTop, ge_iff_le]
    have B (n : ℕ) : ‖c n‖⁻¹ ≤ 1⁻¹ * ‖r‖ * u n := by
      apply (hc n).trans
      gcongr
      simpa [d, dist_eq_norm] using hvu n
    refine ⟨?_, 0, fun n hn ↦ by simpa using c_ne n⟩
    apply squeeze_zero (fun n ↦ by positivity) B
    simpa using u_lim.const_mul _
  obtain ⟨l, l_mem, φ, φ_strict, hφ⟩ :
      ∃ l ∈ Metric.closedBall (0 : E) 1 \ Metric.ball (0 : E) (1 / ‖r‖),
      ∃ (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto ((fun n ↦ c n • d n) ∘ φ) atTop (𝓝 l) := by
    apply IsCompact.tendsto_subseq _ (fun n ↦ ?_)
    · exact (isCompact_closedBall 0 1).diff Metric.isOpen_ball
    simp only [mem_diff, Metric.mem_closedBall, dist_zero_right, (c_le n).le,
      Metric.mem_ball, not_lt, true_and, le_c n]
  refine ⟨l, ?_, ?_⟩; swap
  · simp only [mem_compl_iff, mem_singleton_iff]
    contrapose! l_mem
    simp only [one_div, l_mem, mem_diff, Metric.mem_closedBall, dist_self, zero_le_one,
      Metric.mem_ball, inv_pos, norm_pos_iff, ne_eq, not_not, true_and]
    contrapose! hr
    simp [hr]
  refine ⟨c ∘ φ, d ∘ φ, .of_forall fun n ↦ ?_, ?_, hφ⟩
  · simpa [d] using hvs (φ n)
  · exact c_lim.comp φ_strict.tendsto_atTop

end Normed

end TangentCone

section UniqueDiff

/-!
### Properties of `UniqueDiffWithinAt` and `UniqueDiffOn`

This section is devoted to properties of the predicates `UniqueDiffWithinAt` and `UniqueDiffOn`. -/

section TVS
variable [AddCommGroup E] [Module R E] [TopologicalSpace E]
variable {x y : E} {s t : Set E}

theorem UniqueDiffOn.uniqueDiffWithinAt {s : Set E} {x} (hs : UniqueDiffOn R s) (h : x ∈ s) :
    UniqueDiffWithinAt R s x :=
  hs x h

theorem uniqueDiffWithinAt_univ : UniqueDiffWithinAt R univ x := by
  rw [uniqueDiffWithinAt_iff, tangentCone_univ]
  simp

theorem uniqueDiffOn_univ : UniqueDiffOn R (univ : Set E) :=
  fun _ _ => uniqueDiffWithinAt_univ

theorem uniqueDiffOn_empty : UniqueDiffOn R (∅ : Set E) :=
  fun _ hx => hx.elim

theorem UniqueDiffWithinAt.congr_pt (h : UniqueDiffWithinAt R s x) (hy : x = y) :
    UniqueDiffWithinAt R s y := hy ▸ h

end TVS

section Normed
variable [NormedAddCommGroup E] [NormedSpace R E]
variable [NormedAddCommGroup F] [NormedSpace R F]
variable {x y : E} {s t : Set E}

@[simp]
theorem uniqueDiffWithinAt_closure :
    UniqueDiffWithinAt R (closure s) x ↔ UniqueDiffWithinAt R s x := by
  simp [uniqueDiffWithinAt_iff]

protected alias ⟨UniqueDiffWithinAt.of_closure, UniqueDiffWithinAt.closure⟩ :=
  uniqueDiffWithinAt_closure

theorem UniqueDiffWithinAt.mono_nhds (h : UniqueDiffWithinAt R s x) (st : 𝓝[s] x ≤ 𝓝[t] x) :
    UniqueDiffWithinAt R t x := by
  simp only [uniqueDiffWithinAt_iff] at *
  rw [mem_closure_iff_nhdsWithin_neBot] at h ⊢
  exact ⟨h.1.mono <| Submodule.span_mono <| tangentConeAt_mono_nhds st, h.2.mono st⟩

theorem UniqueDiffWithinAt.mono (h : UniqueDiffWithinAt R s x) (st : s ⊆ t) :
    UniqueDiffWithinAt R t x :=
  h.mono_nhds <| nhdsWithin_mono _ st

theorem UniqueDiffWithinAt.mono_closure (h : UniqueDiffWithinAt 𝕜 s x) (st : s ⊆ closure t) :
    UniqueDiffWithinAt 𝕜 t x :=
  (h.mono st).of_closure

theorem uniqueDiffWithinAt_congr (st : 𝓝[s] x = 𝓝[t] x) :
    UniqueDiffWithinAt R s x ↔ UniqueDiffWithinAt R t x :=
  ⟨fun h => h.mono_nhds <| le_of_eq st, fun h => h.mono_nhds <| le_of_eq st.symm⟩

theorem uniqueDiffWithinAt_inter (ht : t ∈ 𝓝 x) :
    UniqueDiffWithinAt R (s ∩ t) x ↔ UniqueDiffWithinAt R s x :=
  uniqueDiffWithinAt_congr <| (nhdsWithin_restrict' _ ht).symm

theorem UniqueDiffWithinAt.inter (hs : UniqueDiffWithinAt R s x) (ht : t ∈ 𝓝 x) :
    UniqueDiffWithinAt R (s ∩ t) x :=
  (uniqueDiffWithinAt_inter ht).2 hs

theorem uniqueDiffWithinAt_inter' (ht : t ∈ 𝓝[s] x) :
    UniqueDiffWithinAt R (s ∩ t) x ↔ UniqueDiffWithinAt R s x :=
  uniqueDiffWithinAt_congr <| (nhdsWithin_restrict'' _ ht).symm

theorem UniqueDiffWithinAt.inter' (hs : UniqueDiffWithinAt R s x) (ht : t ∈ 𝓝[s] x) :
    UniqueDiffWithinAt R (s ∩ t) x :=
  (uniqueDiffWithinAt_inter' ht).2 hs

theorem uniqueDiffWithinAt_of_mem_nhds (h : s ∈ 𝓝 x) : UniqueDiffWithinAt R s x := by
  simpa only [univ_inter] using uniqueDiffWithinAt_univ.inter h

theorem IsOpen.uniqueDiffWithinAt (hs : IsOpen s) (xs : x ∈ s) : UniqueDiffWithinAt R s x :=
  uniqueDiffWithinAt_of_mem_nhds (IsOpen.mem_nhds hs xs)

theorem UniqueDiffOn.inter (hs : UniqueDiffOn R s) (ht : IsOpen t) : UniqueDiffOn R (s ∩ t) :=
  fun x hx => (hs x hx.1).inter (IsOpen.mem_nhds ht hx.2)

theorem IsOpen.uniqueDiffOn (hs : IsOpen s) : UniqueDiffOn R s :=
  fun _ hx => IsOpen.uniqueDiffWithinAt hs hx

/-- The product of two sets of unique differentiability at points `x` and `y` has unique
differentiability at `(x, y)`. -/
theorem UniqueDiffWithinAt.prod {t : Set F} {y : F} (hs : UniqueDiffWithinAt R s x)
    (ht : UniqueDiffWithinAt R t y) : UniqueDiffWithinAt R (s ×ˢ t) (x, y) := by
  rw [uniqueDiffWithinAt_iff] at hs ht ⊢
  rw [closure_prod_eq]
  refine ⟨?_, hs.2, ht.2⟩
  have : _ ≤ Submodule.span R (tangentConeAt R (s ×ˢ t) (x, y)) := Submodule.span_mono
    (union_subset (subset_tangentCone_prod_left ht.2) (subset_tangentCone_prod_right hs.2))
  rw [LinearMap.span_inl_union_inr, SetLike.le_def] at this
  exact (hs.1.prod ht.1).mono this

theorem UniqueDiffWithinAt.univ_pi (ι : Type*) [Finite ι] (E : ι → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace R (E i)] (s : ∀ i, Set (E i)) (x : ∀ i, E i)
    (h : ∀ i, UniqueDiffWithinAt R (s i) (x i)) : UniqueDiffWithinAt R (Set.pi univ s) x := by
  classical
  simp only [uniqueDiffWithinAt_iff, closure_pi_set] at h ⊢
  refine ⟨(dense_pi univ fun i _ => (h i).1).mono ?_, fun i _ => (h i).2⟩
  norm_cast
  simp only [← Submodule.iSup_map_single, iSup_le_iff, LinearMap.map_span, Submodule.span_le,
    ← mapsTo']
  exact fun i => (mapsTo_tangentConeAt_pi fun j _ => (h j).2).mono Subset.rfl Submodule.subset_span

theorem UniqueDiffWithinAt.pi (ι : Type*) [Finite ι] (E : ι → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace R (E i)] (s : ∀ i, Set (E i)) (x : ∀ i, E i)
    (I : Set ι) (h : ∀ i ∈ I, UniqueDiffWithinAt R (s i) (x i)) :
    UniqueDiffWithinAt R (Set.pi I s) x := by
  classical
  rw [← Set.univ_pi_piecewise_univ]
  refine UniqueDiffWithinAt.univ_pi ι E _ _ fun i => ?_
  by_cases hi : i ∈ I <;> simp [*, uniqueDiffWithinAt_univ]

/-- The product of two sets of unique differentiability is a set of unique differentiability. -/
theorem UniqueDiffOn.prod {t : Set F} (hs : UniqueDiffOn R s) (ht : UniqueDiffOn R t) :
    UniqueDiffOn R (s ×ˢ t) :=
  fun ⟨x, y⟩ h => UniqueDiffWithinAt.prod (hs x h.1) (ht y h.2)

/-- The finite product of a family of sets of unique differentiability is a set of unique
differentiability. -/
theorem UniqueDiffOn.pi (ι : Type*) [Finite ι] (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace R (E i)] (s : ∀ i, Set (E i)) (I : Set ι)
    (h : ∀ i ∈ I, UniqueDiffOn R (s i)) : UniqueDiffOn R (Set.pi I s) :=
  fun x hx => UniqueDiffWithinAt.pi _ _ _ _ _ fun i hi => h i hi (x i) (hx i hi)

/-- The finite product of a family of sets of unique differentiability is a set of unique
differentiability. -/
theorem UniqueDiffOn.univ_pi (ι : Type*) [Finite ι] (E : ι → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace R (E i)] (s : ∀ i, Set (E i))
    (h : ∀ i, UniqueDiffOn R (s i)) : UniqueDiffOn R (Set.pi univ s) :=
  UniqueDiffOn.pi _ _ _ _ fun i _ => h i

end Normed

section RealNormed
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- In a real vector space, a convex set with nonempty interior is a set of unique
differentiability at every point of its closure. -/
theorem uniqueDiffWithinAt_convex {s : Set G} (conv : Convex ℝ s) (hs : (interior s).Nonempty)
    {x : G} (hx : x ∈ closure s) : UniqueDiffWithinAt ℝ s x := by
  rcases hs with ⟨y, hy⟩
  suffices y - x ∈ interior (tangentConeAt ℝ s x) by
    refine ⟨Dense.of_closure ?_, hx⟩
    simp [(Submodule.span ℝ (tangentConeAt ℝ s x)).eq_top_of_nonempty_interior'
        ⟨y - x, interior_mono Submodule.subset_span this⟩]
  rw [mem_interior_iff_mem_nhds]
  replace hy : interior s ∈ 𝓝 y := IsOpen.mem_nhds isOpen_interior hy
  apply mem_of_superset ((isOpenMap_sub_right x).image_mem_nhds hy)
  rintro _ ⟨z, zs, rfl⟩
  refine mem_tangentConeAt_of_openSegment_subset (Subset.trans ?_ interior_subset)
  exact conv.openSegment_closure_interior_subset_interior hx zs

/-- In a real vector space, a convex set with nonempty interior is a set of unique
differentiability. -/
theorem uniqueDiffOn_convex {s : Set G} (conv : Convex ℝ s) (hs : (interior s).Nonempty) :
    UniqueDiffOn ℝ s :=
  fun _ xs => uniqueDiffWithinAt_convex conv hs (subset_closure xs)

end RealNormed

section Real

theorem uniqueDiffOn_Ici (a : ℝ) : UniqueDiffOn ℝ (Ici a) :=
  uniqueDiffOn_convex (convex_Ici a) <| by simp only [interior_Ici, nonempty_Ioi]

theorem uniqueDiffOn_Iic (a : ℝ) : UniqueDiffOn ℝ (Iic a) :=
  uniqueDiffOn_convex (convex_Iic a) <| by simp only [interior_Iic, nonempty_Iio]

theorem uniqueDiffOn_Ioi (a : ℝ) : UniqueDiffOn ℝ (Ioi a) :=
  isOpen_Ioi.uniqueDiffOn

theorem uniqueDiffOn_Iio (a : ℝ) : UniqueDiffOn ℝ (Iio a) :=
  isOpen_Iio.uniqueDiffOn

theorem uniqueDiffOn_Icc {a b : ℝ} (hab : a < b) : UniqueDiffOn ℝ (Icc a b) :=
  uniqueDiffOn_convex (convex_Icc a b) <| by simp only [interior_Icc, nonempty_Ioo, hab]

theorem uniqueDiffOn_Ico (a b : ℝ) : UniqueDiffOn ℝ (Ico a b) :=
  if hab : a < b then
    uniqueDiffOn_convex (convex_Ico a b) <| by simp only [interior_Ico, nonempty_Ioo, hab]
  else by simp only [Ico_eq_empty hab, uniqueDiffOn_empty]

theorem uniqueDiffOn_Ioc (a b : ℝ) : UniqueDiffOn ℝ (Ioc a b) :=
  if hab : a < b then
    uniqueDiffOn_convex (convex_Ioc a b) <| by simp only [interior_Ioc, nonempty_Ioo, hab]
  else by simp only [Ioc_eq_empty hab, uniqueDiffOn_empty]

theorem uniqueDiffOn_Ioo (a b : ℝ) : UniqueDiffOn ℝ (Ioo a b) :=
  isOpen_Ioo.uniqueDiffOn

/-- The real interval `[0, 1]` is a set of unique differentiability. -/
theorem uniqueDiffOn_Icc_zero_one : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) :=
  uniqueDiffOn_Icc zero_lt_one

theorem uniqueDiffWithinAt_Ioo {a b t : ℝ} (ht : t ∈ Set.Ioo a b) :
    UniqueDiffWithinAt ℝ (Set.Ioo a b) t :=
  IsOpen.uniqueDiffWithinAt isOpen_Ioo ht

theorem uniqueDiffWithinAt_Ioi (a : ℝ) : UniqueDiffWithinAt ℝ (Ioi a) a :=
  uniqueDiffWithinAt_convex (convex_Ioi a) (by simp) (by simp)

theorem uniqueDiffWithinAt_Iio (a : ℝ) : UniqueDiffWithinAt ℝ (Iio a) a :=
  uniqueDiffWithinAt_convex (convex_Iio a) (by simp) (by simp)

/-- In one dimension, a point is a point of unique differentiability of a set
iff it is an accumulation point of the set. -/
theorem uniqueDiffWithinAt_iff_accPt {s : Set 𝕜} {x : 𝕜} :
    UniqueDiffWithinAt 𝕜 s x ↔ AccPt x (𝓟 s) :=
  ⟨UniqueDiffWithinAt.accPt, fun h ↦
    ⟨by simp [tangentConeAt_eq_univ h], mem_closure_iff_clusterPt.mpr h.clusterPt⟩⟩

alias ⟨_, AccPt.uniqueDiffWithinAt⟩ := uniqueDiffWithinAt_iff_accPt

/-- In one dimension, every point is either a point of unique differentiability, or isolated. -/
@[deprecated uniqueDiffWithinAt_iff_accPt (since := "2025-04-20")]
theorem uniqueDiffWithinAt_or_nhdsWithin_eq_bot (s : Set 𝕜) (x : 𝕜) :
    UniqueDiffWithinAt 𝕜 s x ∨ 𝓝[s \ {x}] x = ⊥ :=
  (em (AccPt x (𝓟 s))).imp AccPt.uniqueDiffWithinAt fun h ↦ by
    rwa [accPt_principal_iff_nhdsWithin, not_neBot] at h

end Real

end UniqueDiff
