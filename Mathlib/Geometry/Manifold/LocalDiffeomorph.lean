/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Topology.IsLocalHomeomorph

/-!
# Local diffeomorphisms between manifolds

In this file, we define `C^n` local diffeomorphisms between manifolds.

A `C^n` map `f : M → N` is a **local diffeomorphism at `x`** iff there are neighbourhoods `s`
and `t` of `x` and `f x`, respectively, such that `f` restricts to a diffeomorphism
between `s` and `t`. `f` is called a **local diffeomorphism on `s`** iff it is a local
diffeomorphism at every `x ∈ s`, and a **local diffeomorphism** iff it is a local diffeomorphism on
`univ`.

## Main definitions
* `IsLocalDiffeomorphAt I J n f x`: `f` is a `C^n` local diffeomorphism at `x`
* `IsLocalDiffeomorphOn I J n f s`: `f` is a `C^n` local diffeomorphism on `s`
* `IsLocalDiffeomorph I J n f`: `f` is a `C^n` local diffeomorphism

## Main results
* Each of `Diffeomorph`, `IsLocalDiffeomorph`, `IsLocalDiffeomorphOn` and `IsLocalDiffeomorphAt`
  implies the next condition.
* `IsLocalDiffeomorph.isLocalHomeomorph`: a local diffeomorphism is a local homeomorphism,
  and similarly for a local diffeomorphism on `s`.
* `IsLocalDiffeomorph.isOpen_range`: the image of a local diffeomorphism is open
* `IsLocalDiffeomorph.diffeomorphOfBijective`:
  a bijective local diffeomorphism is a diffeomorphism

* `Diffeomorph.mfderivToContinuousLinearEquiv`: each differential of a `C^n` diffeomorphism
  (`n ≠ 0`) is a linear equivalence.
* `LocalDiffeomorphAt.mfderivToContinuousLinearEquiv`: if `f` is a local diffeomorphism
  at `x`, the differential `mfderiv I J n f x` is a continuous linear equivalence.
* `LocalDiffeomorph.mfderivToContinuousLinearEquiv`: if `f` is a local diffeomorphism,
  each differential `mfderiv I J n f x` is a continuous linear equivalence.

## TODO
* an injective local diffeomorphism is a diffeomorphism to its image
* if `f` is `C^n` at `x` and `mfderiv I J n f x` is a linear isomorphism,
  `f` is a local diffeomorphism at `x` (using the inverse function theorem).

## Implementation notes

This notion of diffeomorphism is needed although there is already a notion of local structomorphism
because structomorphisms do not allow the model spaces `H` and `H'` of the two manifolds to be
different, i.e. for a structomorphism one has to impose `H = H'` which is often not the case in
practice.

## Tags
local diffeomorphism, manifold

-/

@[expose] public section

open Manifold Set TopologicalSpace ModelWithCorners

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {D : Type*} [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  {H : Type*} [TopologicalSpace H]
  {G : Type*} [TopologicalSpace G]
  {R : Type*} [TopologicalSpace R]
  (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F G) (K : ModelWithCorners 𝕜 D R)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  (N : Type*) [TopologicalSpace N] [ChartedSpace G N]
  (P : Type*) [TopologicalSpace P] [ChartedSpace R P]
  (n : WithTop ℕ∞)

section PartialDiffeomorph
/-- A partial diffeomorphism on `s` is a function `f : M → N` such that `f` restricts to a
diffeomorphism `s → t` between open subsets of `M` and `N`, respectively.
This is an auxiliary definition and should not be used outside of this file. -/
structure PartialDiffeomorph extends PartialEquiv M N where
  open_source : IsOpen source
  open_target : IsOpen target
  contMDiffOn_toFun : ContMDiffOn I J n toFun source
  contMDiffOn_invFun : ContMDiffOn J I n invFun target

/-- Coercion of a `PartialDiffeomorph` to function.
Note that a `PartialDiffeomorph` is not `DFunLike` (like `OpenPartialHomeomorph`),
as `toFun` doesn't determine `invFun` outside of `target`. -/
instance : CoeFun (PartialDiffeomorph I J M N n) fun _ => M → N :=
  ⟨fun Φ => Φ.toFun⟩

variable {I J M N n}

/-- A diffeomorphism is a partial diffeomorphism. -/
def Diffeomorph.toPartialDiffeomorph (h : Diffeomorph I J M N n) :
    PartialDiffeomorph I J M N n where
  toPartialEquiv := h.toHomeomorph.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun x _ := h.contMDiff_toFun x
  contMDiffOn_invFun _ _ := h.symm.contMDiffWithinAt

-- Add the very basic API we need.
namespace PartialDiffeomorph
variable (Φ : PartialDiffeomorph I J M N n)
variable (Ψ : PartialDiffeomorph J K N P n)

/-- A partial diffeomorphism is also a local homeomorphism. -/
def toOpenPartialHomeomorph : OpenPartialHomeomorph M N where
  toPartialEquiv := Φ.toPartialEquiv
  open_source := Φ.open_source
  open_target := Φ.open_target
  continuousOn_toFun := Φ.contMDiffOn_toFun.continuousOn
  continuousOn_invFun := Φ.contMDiffOn_invFun.continuousOn

@[deprecated (since := "2025-08-29")] alias
  toPartialHomeomorph := toOpenPartialHomeomorph

/-- The inverse of a local diffeomorphism. -/
protected def symm : PartialDiffeomorph J I N M n where
  toPartialEquiv := Φ.toPartialEquiv.symm
  open_source := Φ.open_target
  open_target := Φ.open_source
  contMDiffOn_toFun := Φ.contMDiffOn_invFun
  contMDiffOn_invFun := Φ.contMDiffOn_toFun

-- todo : trans shouldn't need the models with corners as explicit arguments. This also prevents
-- us from using dot notation (see next theorem statement) (how to make these implicit?)
protected def trans : PartialDiffeomorph I K M P n where
  toPartialEquiv := ((Φ.toOpenPartialHomeomorph).trans (Ψ.toOpenPartialHomeomorph)).toPartialEquiv
  open_source := ((Φ.toOpenPartialHomeomorph).trans (Ψ.toOpenPartialHomeomorph)).open_source
  open_target := ((Φ.toOpenPartialHomeomorph).trans (Ψ.toOpenPartialHomeomorph)).open_target
  contMDiffOn_toFun := ContMDiffOn.comp' Ψ.contMDiffOn_toFun Φ.contMDiffOn_toFun
  contMDiffOn_invFun := ContMDiffOn.comp' Φ.contMDiffOn_invFun Ψ.contMDiffOn_invFun

theorem trans_source : (PartialDiffeomorph.trans _ _ Φ Ψ).source = Φ.source ∩ Φ ⁻¹' Ψ.source :=
  by simp [PartialDiffeomorph.trans, toOpenPartialHomeomorph]

protected theorem contMDiffOn : ContMDiffOn I J n Φ Φ.source :=
  Φ.contMDiffOn_toFun

protected theorem mdifferentiableOn (hn : n ≠ 0) : MDifferentiableOn I J Φ Φ.source :=
  (Φ.contMDiffOn).mdifferentiableOn hn

protected theorem mdifferentiableAt (hn : n ≠ 0) {x : M} (hx : x ∈ Φ.source) :
    MDifferentiableAt I J Φ x :=
  (Φ.mdifferentiableOn hn x hx).mdifferentiableAt (Φ.open_source.mem_nhds hx)

-- not really sure what to call this/where to put it
def openPartialHomeomorph_of_isInteriorPoint {p : M} (hp : IsInteriorPoint I p) :
    OpenPartialHomeomorph H E where
  toFun := I.toFun
  invFun := I.invFun
  source := I.toFun ⁻¹' (Classical.choose hp)
  target := I.target ∩ (Classical.choose hp)
  map_source' := by simp
  map_target' := by simp
  left_inv' := by simp
  right_inv' := by simp
  open_source := I.continuous_toFun.isOpen_preimage _ (Classical.choose_spec hp).1.1
  open_target := by
    rw [target_eq, ← right_eq_inter.mpr (Classical.choose_spec hp).1.2]
    exact (Classical.choose_spec hp).1.1
  continuousOn_toFun := I.continuous_toFun.continuousOn
  continuousOn_invFun := I.continuous_invFun.continuousOn

/-- If p is an interior point of M, then (extChartAt I p) can be restricted to an open set
on which it becomes a PartialDiffeomorph (viewing E as a manifold modeled on itself trivially) -/
def diffeoExtChartAt (n : WithTop ℕ∞) [IsManifold I n M] {p : M} (hp : IsInteriorPoint I p) :
    PartialDiffeomorph I 𝓘(𝕜, E) M E n where
  toPartialEquiv :=
    ((chartAt H p).trans (openPartialHomeomorph_of_isInteriorPoint hp)).toPartialEquiv
  open_source := ((chartAt H p).trans (openPartialHomeomorph_of_isInteriorPoint hp)).open_source
  open_target := ((chartAt H p).trans (openPartialHomeomorph_of_isInteriorPoint hp)).open_target
  contMDiffOn_toFun := by
    set homeo := (chartAt H p).trans (openPartialHomeomorph_of_isInteriorPoint hp)
    -- this is just the identity in coordinates
    have h₁: homeo.source ⊆ (chartAt H p).source := by simp [homeo]
    have h₂ : MapsTo homeo homeo.source (chartAt E (homeo p)).source := by simp [MapsTo]
    refine (contMDiffOn_iff_of_subset_source h₁ h₂).mpr ⟨homeo.continuousOn_toFun, ?_⟩
    set f := homeo ∘ (chartAt H p).symm ∘ I.symm
    set s := (fun a ↦ I ((chartAt H p) a)) '' homeo.source
    suffices ContDiffOn 𝕜 n f s by simpa
    have : ∀ e ∈ s, f e = e := by
      rintro e ⟨w, ⟨hw, _⟩, rfl⟩
      simp [f, homeo, openPartialHomeomorph_of_isInteriorPoint,
        (chartAt H p).right_inv ((chartAt H p).map_source hw)]
    exact contDiffOn_id.congr this
  contMDiffOn_invFun := by
    set homeo := (chartAt H p).trans (openPartialHomeomorph_of_isInteriorPoint hp)
    -- this is also just the identity in coordinates
    have h₁ : homeo.target ⊆ (chartAt E (homeo p)).source := by simp [homeo]
    have h₂ : MapsTo homeo.invFun homeo.target  (chartAt H p).source :=
      fun _ he ↦ (homeo.map_target he).1
    refine (contMDiffOn_iff_of_subset_source h₁ h₂).mpr ⟨homeo.continuousOn_invFun, ?_⟩
    set f := (↑I ∘ ↑(chartAt H p)) ∘ ↑homeo.symm
    suffices ContDiffOn 𝕜 n f homeo.target by simpa
    have : ∀ e ∈ homeo.target, f e = e := by
      intro e he
      simp [f, homeo, openPartialHomeomorph_of_isInteriorPoint] at he ⊢
      simp [(chartAt H p).right_inv he.2, I.right_inv he.1.1]
    exact contDiffOn_id.congr this

lemma eqOn_diffeoExtChartAt_extChartAt [IsManifold I n M] {p : M} (hp : IsInteriorPoint I p) :
    EqOn (diffeoExtChartAt n hp) (extChartAt I p) (diffeoExtChartAt n hp).source :=
  graphOn_inj.mp rfl

lemma eqOn_diffeoExtChartAt_symm_extChartAt_symm [IsManifold I n M] {p : M}
    (hp : IsInteriorPoint I p) :
    EqOn (diffeoExtChartAt n hp).symm (extChartAt I p).symm (diffeoExtChartAt n hp).target :=
  graphOn_inj.mp rfl

lemma mem_diffeoExtChartAt_source [IsManifold I n M] {p : M} (hp : IsInteriorPoint I p) :
    p ∈ (diffeoExtChartAt n hp).source := by
  suffices I ((chartAt H p) p) ∈ Classical.choose hp by
    simpa [diffeoExtChartAt, openPartialHomeomorph_of_isInteriorPoint]
  exact (Classical.choose_spec hp).2

lemma diffeoExtChartAt_source_subset [IsManifold I n M] {p : M} (hp : IsInteriorPoint I p) :
    (diffeoExtChartAt n hp).source ⊆ (extChartAt I p).source  := by simp [diffeoExtChartAt]

lemma diffeoExtChartAt_target_subset [IsManifold I n M] {p : M} (hp : IsInteriorPoint I p) :
    (diffeoExtChartAt n hp).target ⊆ (extChartAt I p).target  := by
  intro e he
  rw [← (diffeoExtChartAt n hp).image_source_eq_target] at he
  rcases he with ⟨m, hm, rfl⟩
  rw [← (extChartAt I p).image_source_eq_target]
  exact ⟨m, (diffeoExtChartAt_source_subset hp) hm, eqOn_diffeoExtChartAt_extChartAt hp hm⟩

/- We could add lots of additional API (following `Diffeomorph` and `OpenPartialHomeomorph`),
such as
* further continuity and differentiability lemmas
* refl and trans instances; lemmas between them.
As this declaration is meant for internal use only, we keep it simple. -/
end PartialDiffeomorph
end PartialDiffeomorph

variable {M N}

/-- `f : M → N` is called a **`C^n` local diffeomorphism at *x*** iff there exist
open sets `U ∋ x` and `V ∋ f x` and a diffeomorphism `Φ : U → V` such that `f = Φ` on `U`. -/
def IsLocalDiffeomorphAt (f : M → N) (x : M) : Prop :=
  ∃ Φ : PartialDiffeomorph I J M N n, x ∈ Φ.source ∧ EqOn f Φ Φ.source

lemma PartialDiffeomorph.isLocalDiffeomorphAt (φ : PartialDiffeomorph I J M N n)
    {x : M} (hx : x ∈ φ.source) : IsLocalDiffeomorphAt I J n φ x :=
  ⟨φ, hx, Set.eqOn_refl _ _⟩

namespace IsLocalDiffeomorphAt

variable {f : M → N} {x : M}

variable {I I' J n}

/-- An arbitrary choice of local inverse of `f` near `x`. -/
noncomputable def localInverse (hf : IsLocalDiffeomorphAt I J n f x) :
    PartialDiffeomorph J I N M n := (Classical.choose hf).symm

lemma localInverse_open_source (hf : IsLocalDiffeomorphAt I J n f x) :
    IsOpen hf.localInverse.source :=
  PartialDiffeomorph.open_source _

lemma localInverse_mem_source (hf : IsLocalDiffeomorphAt I J n f x) :
    f x ∈ hf.localInverse.source := by
  rw [(hf.choose_spec.2 hf.choose_spec.1)]
  exact (Classical.choose hf).map_source hf.choose_spec.1

lemma localInverse_mem_target (hf : IsLocalDiffeomorphAt I J n f x) :
    x ∈ hf.localInverse.target :=
  hf.choose_spec.1

lemma contmdiffOn_localInverse (hf : IsLocalDiffeomorphAt I J n f x) :
    ContMDiffOn J I n hf.localInverse hf.localInverse.source :=
  hf.localInverse.contMDiffOn_toFun

lemma localInverse_right_inv (hf : IsLocalDiffeomorphAt I J n f x) {y : N}
    (hy : y ∈ hf.localInverse.source) : f (hf.localInverse y) = y := by
  have : hf.localInverse y ∈ hf.choose.source := by
    rw [← hf.choose.symm_target]
    exact hf.choose.symm.map_source hy
  rw [hf.choose_spec.2 this]
  exact hf.choose.right_inv hy

lemma localInverse_eqOn_right (hf : IsLocalDiffeomorphAt I J n f x) :
    EqOn (f ∘ hf.localInverse) id hf.localInverse.source :=
  fun _y hy ↦ hf.localInverse_right_inv hy

lemma localInverse_eventuallyEq_right (hf : IsLocalDiffeomorphAt I J n f x) :
    f ∘ hf.localInverse =ᶠ[nhds (f x)] id :=
  Filter.eventuallyEq_of_mem
    (hf.localInverse.open_source.mem_nhds hf.localInverse_mem_source)
    hf.localInverse_eqOn_right

lemma localInverse_left_inv (hf : IsLocalDiffeomorphAt I J n f x) {x' : M}
    (hx' : x' ∈ hf.localInverse.target) : hf.localInverse (f x') = x' := by
  rw [hf.choose_spec.2 (hf.choose.symm_target ▸ hx')]
  exact hf.choose.left_inv hx'

lemma localInverse_eqOn_left (hf : IsLocalDiffeomorphAt I J n f x) :
    EqOn (hf.localInverse ∘ f) id hf.localInverse.target :=
  fun _ hx ↦ hf.localInverse_left_inv hx

lemma localInverse_eventuallyEq_left (hf : IsLocalDiffeomorphAt I J n f x) :
    hf.localInverse ∘ f =ᶠ[nhds x] id :=
  Filter.eventuallyEq_of_mem
    (hf.localInverse.open_target.mem_nhds hf.localInverse_mem_target) hf.localInverse_eqOn_left

lemma localInverse_isLocalDiffeomorphAt (hf : IsLocalDiffeomorphAt I J n f x) :
    IsLocalDiffeomorphAt J I n (hf.localInverse) (f x) :=
  hf.localInverse.isLocalDiffeomorphAt _ _ _ hf.localInverse_mem_source

lemma localInverse_contMDiffOn (hf : IsLocalDiffeomorphAt I J n f x) :
    ContMDiffOn J I n hf.localInverse hf.localInverse.source :=
  hf.localInverse.contMDiffOn_toFun

lemma localInverse_contMDiffAt (hf : IsLocalDiffeomorphAt I J n f x) :
    ContMDiffAt J I n hf.localInverse (f x) :=
  hf.localInverse_contMDiffOn.contMDiffAt
    (hf.localInverse.open_source.mem_nhds hf.localInverse_mem_source)

lemma localInverse_mdifferentiableAt (hf : IsLocalDiffeomorphAt I J n f x) (hn : n ≠ 0) :
    MDifferentiableAt J I hf.localInverse (f x) :=
  hf.localInverse_contMDiffAt.mdifferentiableAt hn

end IsLocalDiffeomorphAt

/-- `f : M → N` is called a **`C^n` local diffeomorphism on *s*** iff it is a local diffeomorphism
at each `x : s`. -/
def IsLocalDiffeomorphOn (f : M → N) (s : Set M) : Prop :=
  ∀ x : s, IsLocalDiffeomorphAt I J n f x

/-- `f : M → N` is a **`C^n` local diffeomorphism** iff it is a local diffeomorphism
at each `x ∈ M`. -/
def IsLocalDiffeomorph (f : M → N) : Prop :=
  ∀ x : M, IsLocalDiffeomorphAt I J n f x

variable {I J n} in
lemma isLocalDiffeomorphOn_iff {f : M → N} (s : Set M) :
    IsLocalDiffeomorphOn I J n f s ↔ ∀ x : s, IsLocalDiffeomorphAt I J n f x := by rfl

variable {I J n} in
lemma isLocalDiffeomorph_iff {f : M → N} :
    IsLocalDiffeomorph I J n f ↔ ∀ x : M, IsLocalDiffeomorphAt I J n f x := by rfl

variable {I J n} in
theorem isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ {f : M → N} :
    IsLocalDiffeomorph I J n f ↔ IsLocalDiffeomorphOn I J n f Set.univ :=
  ⟨fun hf x ↦ hf x, fun hf x ↦ hf ⟨x, trivial⟩⟩

variable {I J n} in
lemma IsLocalDiffeomorph.isLocalDiffeomorphOn
    {f : M → N} (hf : IsLocalDiffeomorph I J n f) (s : Set M) : IsLocalDiffeomorphOn I J n f s :=
  fun x ↦ hf x

/-! ### Basic properties of local diffeomorphisms -/
section Basic
variable {f : M → N} {s : Set M} {x : M}
variable {I J n}

/-- A `C^n` local diffeomorphism at `x` is `C^n` differentiable at `x`. -/
lemma IsLocalDiffeomorphAt.contMDiffAt (hf : IsLocalDiffeomorphAt I J n f x) :
    ContMDiffAt I J n f x := by
  choose Φ hx heq using hf
  -- In fact, even `ContMDiffOn I J n f Φ.source`.
  exact ((Φ.contMDiffOn_toFun).congr heq).contMDiffAt (Φ.open_source.mem_nhds hx)

/-- A local diffeomorphism at `x` is differentiable at `x`. -/
lemma IsLocalDiffeomorphAt.mdifferentiableAt (hf : IsLocalDiffeomorphAt I J n f x) (hn : n ≠ 0) :
    MDifferentiableAt I J f x :=
  hf.contMDiffAt.mdifferentiableAt hn

/-- A `C^n` local diffeomorphism on `s` is `C^n` on `s`. -/
lemma IsLocalDiffeomorphOn.contMDiffOn (hf : IsLocalDiffeomorphOn I J n f s) :
    ContMDiffOn I J n f s :=
  fun x hx ↦ (hf ⟨x, hx⟩).contMDiffAt.contMDiffWithinAt

/-- A local diffeomorphism on `s` is differentiable on `s`. -/
lemma IsLocalDiffeomorphOn.mdifferentiableOn (hf : IsLocalDiffeomorphOn I J n f s) (hn : n ≠ 0) :
    MDifferentiableOn I J f s :=
  hf.contMDiffOn.mdifferentiableOn hn

/-- A `C^n` local diffeomorphism is `C^n`. -/
lemma IsLocalDiffeomorph.contMDiff (hf : IsLocalDiffeomorph I J n f) : ContMDiff I J n f :=
  fun x ↦ (hf x).contMDiffAt

/-- A `C^n` local diffeomorphism is differentiable. -/
lemma IsLocalDiffeomorph.mdifferentiable (hf : IsLocalDiffeomorph I J n f) (hn : n ≠ 0) :
    MDifferentiable I J f :=
  fun x ↦ (hf x).mdifferentiableAt hn

/-- A `C^n` diffeomorphism is a local diffeomorphism. -/
lemma Diffeomorph.isLocalDiffeomorph (Φ : M ≃ₘ^n⟮I, J⟯ N) : IsLocalDiffeomorph I J n Φ :=
  fun _x ↦ ⟨Φ.toPartialDiffeomorph, by trivial, eqOn_refl Φ _⟩

-- FUTURE: if useful, also add "a `PartialDiffeomorph` is a local diffeomorphism on its source"

/-- A local diffeomorphism on `s` is a local homeomorphism on `s`. -/
theorem IsLocalDiffeomorphOn.isLocalHomeomorphOn {s : Set M} (hf : IsLocalDiffeomorphOn I J n f s) :
    IsLocalHomeomorphOn f s := by
  apply IsLocalHomeomorphOn.mk
  intro x hx
  choose U hyp using hf ⟨x, hx⟩
  exact ⟨U.toOpenPartialHomeomorph, hyp⟩

/-- A local diffeomorphism is a local homeomorphism. -/
theorem IsLocalDiffeomorph.isLocalHomeomorph (hf : IsLocalDiffeomorph I J n f) :
    IsLocalHomeomorph f := by
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
  rw [isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ] at hf
  exact hf.isLocalHomeomorphOn

/-- A local diffeomorphism is an open map. -/
lemma IsLocalDiffeomorph.isOpenMap (hf : IsLocalDiffeomorph I J n f) : IsOpenMap f :=
  (hf.isLocalHomeomorph).isOpenMap

/-- A local diffeomorphism has open range. -/
lemma IsLocalDiffeomorph.isOpen_range (hf : IsLocalDiffeomorph I J n f) : IsOpen (range f) :=
  (hf.isOpenMap).isOpen_range

/-- The image of a local diffeomorphism is open. -/
def IsLocalDiffeomorph.image (hf : IsLocalDiffeomorph I J n f) : Opens N :=
  ⟨range f, hf.isOpen_range⟩

lemma IsLocalDiffeomorph.image_coe (hf : IsLocalDiffeomorph I J n f) : hf.image.1 = range f :=
  rfl

-- TODO: this result holds more generally for (local) structomorphisms
-- This argument implies a `LocalDiffeomorphOn f s` for `s` open is a `PartialDiffeomorph`

/-- A bijective local diffeomorphism is a diffeomorphism. -/
noncomputable def IsLocalDiffeomorph.diffeomorphOfBijective
    (hf : IsLocalDiffeomorph I J n f) (hf' : Function.Bijective f) : Diffeomorph I J M N n := by
  -- Choose a right inverse `g` of `f`.
  choose g hgInverse using (Function.bijective_iff_has_inverse).mp hf'
  -- Choose diffeomorphisms φ_x which coincide with `f` near `x`.
  choose Φ hyp using (fun x ↦ hf x)
  -- Two such diffeomorphisms (and their inverses!) coincide on their sources:
  -- they're both inverses to g. In fact, the latter suffices for our proof.
  -- have (x y) : EqOn (Φ x).symm (Φ y).symm ((Φ x).target ∩ (Φ y).target) := sorry
  have aux (x) : EqOn g (Φ x).symm (Φ x).target :=
    eqOn_of_leftInvOn_of_rightInvOn (fun x' _ ↦ hgInverse.1 x')
      (LeftInvOn.congr_left ((Φ x).toOpenPartialHomeomorph).rightInvOn
        ((Φ x).toOpenPartialHomeomorph).symm_mapsTo (hyp x).2.symm)
      (fun _y hy ↦ (Φ x).map_target hy)
  exact {
    toFun := f
    invFun := g
    left_inv := hgInverse.1
    right_inv := hgInverse.2
    contMDiff_toFun := hf.contMDiff
    contMDiff_invFun := by
      intro y
      let x := g y
      obtain ⟨hx, hfx⟩ := hyp x
      apply ((Φ x).symm.contMDiffOn.congr (aux x)).contMDiffAt (((Φ x).open_target).mem_nhds ?_)
      have : y = (Φ x) x := ((hgInverse.2 y).congr (hfx hx)).mp rfl
      exact this ▸ (Φ x).map_source hx }

@[deprecated (since := "2025-12-19")]
alias IsLocalDiffeomorph.diffeomorph_of_bijective := IsLocalDiffeomorph.diffeomorphOfBijective

end Basic

section Differential

variable {f : M → N} {s : Set M} {x : M}

variable {I I' J n}

set_option backward.isDefEq.respectTransparency false in
/-- If `f` is a `C^n` local diffeomorphism at `x`, for `n ≠ 0`, the differential `df_x`
is a linear equivalence. -/
noncomputable def IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
    (hf : IsLocalDiffeomorphAt I J n f x) (hn : n ≠ 0) :
    TangentSpace I x ≃L[𝕜] TangentSpace J (f x) where
  toFun := mfderiv I J f x
  invFun := mfderiv J I hf.localInverse (f x)
  left_inv := by
    apply ContinuousLinearMap.leftInverse_of_comp
    rw [← mfderiv_id, ← hf.localInverse_eventuallyEq_left.mfderiv_eq]
    exact (mfderiv_comp _ (hf.localInverse_mdifferentiableAt hn) (hf.mdifferentiableAt hn)).symm
  right_inv := by
    apply ContinuousLinearMap.rightInverse_of_comp
    rw [← mfderiv_id, ← hf.localInverse_eventuallyEq_right.mfderiv_eq]
    -- We need to rewrite the base point hf.localInverse (f x) = x twice,
    -- in the differentiability hypothesis and for applying the chain rule.
    have hf' : MDifferentiableAt I J f (hf.localInverse (f x)) := by
      rw [hf.localInverse_left_inv hf.localInverse_mem_target]
      exact hf.mdifferentiableAt hn
    rw [mfderiv_comp _ hf' (hf.localInverse_mdifferentiableAt hn),
      hf.localInverse_left_inv hf.localInverse_mem_target]
  continuous_toFun := (mfderiv I J f x).cont
  continuous_invFun := (mfderiv J I hf.localInverse (f x)).cont
  map_add' := fun x_1 y ↦ map_add _ x_1 y
  map_smul' := by intros; simp

@[simp, mfld_simps]
lemma IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe
    (hf : IsLocalDiffeomorphAt I J n f x) (hn : n ≠ 0) :
    hf.mfderivToContinuousLinearEquiv hn = mfderiv I J f x := rfl

/-- Each differential of a `C^n` diffeomorphism of Banach manifolds (`n ≠ 0`)
is a linear equivalence. -/
noncomputable def Diffeomorph.mfderivToContinuousLinearEquiv
    (Φ : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (x : M) :
    TangentSpace I x ≃L[𝕜] TangentSpace J (Φ x) :=
  (Φ.isLocalDiffeomorph x).mfderivToContinuousLinearEquiv hn

lemma Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) :
    Φ.mfderivToContinuousLinearEquiv hn x = mfderiv I J Φ x := by rfl

/-- If `f` is a `C^n` local diffeomorphism of Banach manifolds (`n ≠ 0`),
each differential is a linear equivalence. -/
noncomputable def IsLocalDiffeomorph.mfderivToContinuousLinearEquiv
    (hf : IsLocalDiffeomorph I J n f) (hn : n ≠ 0) (x : M) :
    TangentSpace I x ≃L[𝕜] TangentSpace J (f x) :=
  (hf x).mfderivToContinuousLinearEquiv hn

lemma IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
    (hf : IsLocalDiffeomorph I J n f) (hn : n ≠ 0) (x : M) :
    hf.mfderivToContinuousLinearEquiv hn x = mfderiv I J f x :=
  (hf x).mfderivToContinuousLinearEquiv_coe hn

end Differential

section InverseFunctionTheorem

open PartialDiffeomorph

-- need to redefine variables (this time with RCLike 𝕜) to prevent typeclass resolution conflicts
variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {H : Type*} [TopologicalSpace H]
  {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : WithTop ℕ∞} [IsManifold I n M] [IsManifold J n N]

theorem localDiffeomorph_of_mfderiv_iso (hn : n ≠ 0) {f : M → N} {p : M} (hp : IsInteriorPoint I p)
    (hfp : IsInteriorPoint J (f p)) {A : Set M} (hA : IsOpen A) (hpA : p ∈ A)
    (hf : ContMDiffOn I J n f A) (hf' : (mfderiv I J f p).ker = ⊥ ∧ (mfderiv I J f p).range = ⊤) :
    IsLocalDiffeomorphAt I J n f p := by
  /- question : would it be better to have f' (linear equiv) and HasMFDerivAt f p f' as hypotheses?
  The hf' hypothesis and the process of using it to obtain g' seems a bit awkward -/

  -- write the function in coordinates and obtain coordinate charts
  set g : E → F := writtenInExtChartAt I J p f
  set φ₀ := extChartAt I p
  set φ₁ := diffeoExtChartAt n hp
  set ψ₀ := extChartAt J (f p)
  set ψ₁ := diffeoExtChartAt n hfp
  -- define U ⊆ E, an open set where we can easily show that g is ContDiff
  set U : Set E := φ₁ '' (φ₁.source ∩ (A ∩ f ⁻¹' ψ₁.source))
  have U_open : IsOpen U := by
    refine φ₁.toOpenPartialHomeomorph.isOpen_image_of_subset_source ?_ inter_subset_left
    exact φ₁.open_source.inter (hf.continuousOn.isOpen_inter_preimage hA ψ₁.open_source)
  have U_nhd : U ∈ nhds (φ₀ p) := mem_nhds_iff.mpr ⟨U, subset_refl _, U_open, mem_image_of_mem _
    ⟨mem_diffeoExtChartAt_source hp, hpA, mem_diffeoExtChartAt_source (n := n) hfp⟩⟩
  have hg : ContDiffOn 𝕜 n g U := by
    refine ((contMDiffOn_iff.mp hf).2 p (f p)).mono ?_
    rintro e ⟨m, ⟨hm₁, hm₂, hm₃⟩, rfl⟩
    refine ⟨diffeoExtChartAt_target_subset hp (φ₁.map_source hm₁), ?_⟩
    simp only [mem_preimage] at hm₃ ⊢
    rw [eqOn_diffeoExtChartAt_extChartAt hp hm₁,
      φ₀.left_inv (diffeoExtChartAt_source_subset hp hm₁)]
    exact ⟨hm₂, diffeoExtChartAt_source_subset hfp hm₃⟩
  -- use hf' to show that the derivative of g at φ₀ p is a linear equivalence
  have ⟨g', hg'⟩ : ∃ g' : E ≃L[𝕜] F, HasFDerivAt g (g' : E →L[𝕜] F) (φ₀ p) := by
    have A_nhd : A ∈ nhds p := mem_nhds_iff.mpr ⟨A, subset_refl _, hA, hpA⟩
    have g_diff: DifferentiableWithinAt 𝕜 g (range I) (φ₀ p) :=
      ((hg.differentiableOn hn).differentiableAt U_nhd).differentiableWithinAt
    rw [mfderiv, if_pos ((hf.contMDiffAt A_nhd).mdifferentiableAt hn), fderivWithin] at hf'
    by_cases g'_zero: HasFDerivWithinAt g (0 : E →L[𝕜] F) (range I) (φ₀ p)
    · rw [if_pos g'_zero] at hf'
      exact ⟨ContinuousLinearEquiv.ofBijective 0 hf'.1 hf'.2,
        g'_zero.hasFDerivAt (range_mem_nhds_isInteriorPoint hp)⟩
    · rw [if_neg g'_zero, dif_pos g_diff] at hf'
      exact ⟨ContinuousLinearEquiv.ofBijective (Classical.choose g_diff) hf'.1 hf'.2,
        (Classical.choose_spec g_diff).hasFDerivAt (range_mem_nhds_isInteriorPoint hp)⟩
  -- define V, the open set where g' is a linear equivalence
  set V := fderiv 𝕜 g ⁻¹' range ContinuousLinearEquiv.toContinuousLinearMap
  have hUV: IsOpen (U ∩ V) :=
    (hg.continuousOn_fderiv_of_isOpen U_open (ENat.one_le_iff_ne_zero_withTop.mpr hn)
    ).isOpen_inter_preimage U_open (ContinuousLinearEquiv.isOpen)
  /- obtain an OpenPartialHomeomorph E → F using the standard inverse function theorem. We must
  restrict to U ∩ V so that we can later show ContDiff of the forward and inverse function
  todo : refactor this part to a separate function since it could be independently useful -/
  set homeo := ((hg.contDiffAt U_nhd).toOpenPartialHomeomorph g hg' hn).restrOpen _ hUV
  have homeo_source_sub_UV : homeo.source ⊆ U ∩ V :=
    ((hg.contDiffAt U_nhd).toOpenPartialHomeomorph g hg' hn).restrOpen_source _ hUV ▸
    inter_subset_right
  have homeo_contdiff : ContDiffOn 𝕜 n homeo.toFun homeo.source := by
    intro x hx
    have : homeo.source ⊆ U := subset_trans homeo_source_sub_UV inter_subset_left
    exact (hg.contDiffWithinAt (this hx)).mono (subset_trans homeo_source_sub_UV inter_subset_left)
  -- upgrade to a PartialDiffeomorph using the properties of U and V
  set coord_diffeo : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, F) E F n := {
    toPartialEquiv := homeo.toPartialEquiv
    open_source := homeo.open_source
    open_target := homeo.open_target
    contMDiffOn_toFun := by
      intro x hx
      refine ⟨homeo.continuousOn_toFun.continuousWithinAt hx, ?_⟩
      suffices ContDiffWithinAt 𝕜 n homeo homeo.source x by simpa [ContDiffWithinAtProp]
      exact homeo_contdiff x hx
    contMDiffOn_invFun := by
      intro y hy
      refine ⟨homeo.continuousOn_invFun.continuousWithinAt hy, ?_⟩
      rcases (subset_trans homeo_source_sub_UV inter_subset_right) (homeo.map_target hy) with
        ⟨g', hg'⟩
      have source_nhd : homeo.source ∈ nhds (homeo.symm y) :=
        mem_nhds_iff.mpr ⟨homeo.source, subset_refl _, homeo.open_source, homeo.map_target hy⟩
      have : DifferentiableAt 𝕜 homeo (homeo.symm y) := (homeo_contdiff.differentiableOn hn
        (homeo.symm y) (homeo.map_target hy)).differentiableAt source_nhd
      exact (homeo.contDiffAt_symm hy (hg' ▸ this.hasFDerivAt)
        (homeo_contdiff.contDiffAt source_nhd)).contDiffWithinAt
  }
  -- compose with the charts to obtain our partial diffeomorphism M → N
  set diffeo := PartialDiffeomorph.trans _ _ (PartialDiffeomorph.trans _ _ φ₁ coord_diffeo) ψ₁.symm
  use diffeo
  -- rote verification of remaining conditions, mostly just unwrapping definitions (todo: clean up)
  constructor
  · show p ∈ diffeo.source
    simp [diffeo, PartialDiffeomorph.trans, toOpenPartialHomeomorph, coord_diffeo, homeo, U, V,
      and_assoc]
    refine ⟨mem_diffeoExtChartAt_source hp,
      ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _,
      ⟨p, mem_diffeoExtChartAt_source hp, hpA, mem_diffeoExtChartAt_source hfp, rfl⟩,
      ⟨g', hg'.fderiv.symm⟩,
      ?_⟩
    suffices ψ₁ (f p) ∈ ψ₁.symm.source by
      simpa [g, φ₁, diffeoExtChartAt, openPartialHomeomorph_of_isInteriorPoint]
    exact ψ₁.map_source (mem_diffeoExtChartAt_source hfp)
  · show EqOn f diffeo diffeo.source
    intro m hm
    suffices f m = (chartAt G (f p)).symm
      ((chartAt G (f p)) (f ((chartAt H p).symm ((chartAt H p) m)))) by
      simpa [diffeo, PartialDiffeomorph.trans, φ₁, ψ₁, toOpenPartialHomeomorph, diffeoExtChartAt,
        coord_diffeo, homeo, PartialDiffeomorph.symm, openPartialHomeomorph_of_isInteriorPoint, g]
    rw [(chartAt H p).left_inv
      (extChartAt_source I p ▸ (diffeoExtChartAt_source_subset (n := n) hp) hm.1.1),
      (chartAt G (f p)).left_inv ?_]
    rcases hm.1.2.2.1 with ⟨m', hm'₁, hm'₂⟩
    have : m' = m := by
      calc m' = φ₁.symm (φ₁ m') := (φ₁.left_inv hm'₁.1).symm
      _ = φ₁.symm (φ₁ m) := by congr 1
      _ = m := (φ₁.left_inv hm.1.1)
    subst this
    exact extChartAt_source J (f p) ▸ diffeoExtChartAt_source_subset (n := n) hfp hm'₁.2.2

end InverseFunctionTheorem
