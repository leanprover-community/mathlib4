/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv

/-!
# Local diffeomorphisms between smooth manifolds

In this file, we define `C^n` local diffeomorphisms between manifolds.

A `C^n` map `f : M → N` is a **local diffeomorphism at `x`** iff there are neighbourhoods `s`
and `t` of `x` and `f x`, respectively such that `f` restricts to a diffeomorphism from `s` and `t`.
`f` is called a **local diffeomorphism** iff it is a local diffeomorphism at every `x ∈ M`.

## Main definitions
* `LocalDiffeomorphAt x`: `f` is a local diffeomorphism at `x`
* `LocalDiffeomorph`: `f` is a local diffeomorphism
* `DiffeomorphOn`: `f` is a "diffeomorphism between open subsets of `M` and `N`, respectively.
This definition is an implementation detail, and not meant for use outside of this file.

## Main results
* Each of `Diffeomorph`, `LocalDiffeomorph`, `DiffeomorphOn` and `LocalDiffeomorphAt`
implies the next condition.
* `Diffeomorph.of_localDiffeomorph`: a bijective local diffeomorphisms is a diffeomorphism.
* `LocalDiffeomorphAt.differential_toContinuousLinearEquiv`: if `f` is a local diffeomorphism
at `x`, the differential `mfderiv I J n f x` is a continuous linear isomorphism.
* `LocalDiffeomorphAt.of_DifferentialIsoAt`: conversely, if `f` is `C^n` at `x` and
`mfderiv I J n f x` is a linear isomorphism, `f` is a local diffeomorphism at `x`.
* `LocalDiffeomorph.differential_toContinuousLinearEquiv`: if `f` is a local diffeomorphism,
each differential `mfderiv I J n f x` is a continuous linear isomorphism.
* `LocalDiffeomorph.of_differentialInvertible`: Conversely, if `f` is `C^n` and each differential
is a linear isomorphism, `f` is a local diffeomorphism.

## Design decisions
For all definitions, we use the junk value pattern: a local diffeomorphism at `x` is still given
by a function on all of `M`; its values outside its `source` are irrelevant. (This matches the
treatment of smooth manifolds and `LocalHomeomorph`.)

This combines with the second major design decision: all our definitions are bundled. That is,
we consider `f` together with a choice `g` of inverse. For local diffeomorphisms, `g` can take any
values outside of `f.target`.
A local diffeomorphism contains the data `f` and `g`, together with proofs that these define a
local diffeomorphism at each point.

## Tags
local diffeomorphism

-/

open Function Manifold Set SmoothManifoldWithCorners TopologicalSpace Topology
set_option autoImplicit false

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {G : Type*} [TopologicalSpace G] {G' : Type*} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {J : ModelWithCorners 𝕜 F G}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] {n : ℕ∞}

variable (I I' J M M' N n)

-- FIXME, everywhere: move n to a different position, to match Diffeomorph?

/-- A "diffeomorphism on" `s` is a function `f : M → N` such that `f` restricts to a diffeomorphism
`s → t` between open subsets of `M` and `N`, respectively. -/
-- In Lean, `s` and `t` are `source` and `target`, respectively.
structure DiffeomorphOn extends LocalHomeomorph M N where
  contMDiffOn_toFun : ContMDiffOn I J n toFun source
  contMDiffOn_invFun : ContMDiffOn J I n invFun target

namespace DiffeomorphOn
-- Basic API for `DiffeomorphOn`: coe and ext lemmas; continuity and smoothness results,
-- refl, symm and trans with simple relations between them.
-- TODO: the first and last ones are cargo-culted. double-check they make sense!

/-- Coercion of a `DiffeomorphOn` to function. Note that a `DiffeomorphOn` is not `FunLike`
(like `LocalHomeomorph`), as `toFun` doesn't determine `invFun` outside of `target`. -/
instance : CoeFun (DiffeomorphOn I J M N n) fun _ => M → N :=
  ⟨fun e => e.toFun'⟩

-- mk_coe and mk_coe_symm could go here

variable {I J M N n} in
-- TODO: prove this; somehow adapting the LocalHomeomorph proof always failed...
lemma toLocalHomeomorph_injective : Injective
    (toLocalHomeomorph : DiffeomorphOn I J M N n → LocalHomeomorph M N) := sorry

/-- Inverse of a diffeomorphism on a set. -/
@[pp_dot]
protected def symm (h : DiffeomorphOn I I' M M' n) : DiffeomorphOn I' I M' M n where
  toLocalHomeomorph := h.toLocalHomeomorph.symm
  contMDiffOn_toFun := h.contMDiffOn_invFun
  contMDiffOn_invFun := h.contMDiffOn_toFun

/- Register a few simp lemmas to make sure that `simp` puts the application of a local
homeomorphism in its normal form, i.e., in terms of its coercion to a function. -/
@[simp, mfld_simps]
theorem toFun_eq_coe (h : DiffeomorphOn I J M N n) : h.toFun = h :=
  rfl

@[simp, mfld_simps]
theorem invFun_eq_coe (h : DiffeomorphOn I J M N n) : h.invFun = h.symm :=
  rfl

@[simp, mfld_simps]
theorem coe_coe (h : DiffeomorphOn I J M N n) : (h.toLocalEquiv : M → N) = h :=
  rfl

@[simp, mfld_simps]
theorem coe_coe_symm (h : DiffeomorphOn I J M N n) : (h.toLocalEquiv.symm : N → M) = h.symm :=
  rfl

-- many results from `LocalHomeomorph` not duplicated here, including
--   eq_symm_apply, mapsTo, symm_mapsTo, leftInvOn, rightInvOn, invOn, bijOn, injOn, surjOn
--   replaceEquiv, replaceEquiv_eq_self
--   eventually_{xxx}_inverse, eventualy_{}
--   lemmas about images and preimages in source and target
-- all of these follow immediately by coercing e to a `LocalHomeomorph`

variable {I J M N n} in
/-- Two local diffeomorphisms are equal when they have equal `toFun`, `invFun` and `source`.
It is not sufficient to have equal `toFun` and `source`, as this only determines `invFun` on
the target. This would only be true for a weaker notion of equality, arguably the right one,
called `eq_on_source`. -/
@[ext]
protected theorem ext (e e' : DiffeomorphOn I J M N n) (h : ∀ x, e x = e' x)
    (hinv : ∀ x, e.symm x = e'.symm x) (hs : e.source = e'.source) : e = e' :=
  toLocalHomeomorph_injective (LocalHomeomorph.ext _ _ h hinv hs)

variable {I J M N n} in
protected theorem ext_iff {e e' : DiffeomorphOn I J M N n} :
    e = e' ↔ (∀ x, e x = e' x) ∧ (∀ x, e.symm x = e'.symm x) ∧ e.source = e'.source :=
  ⟨by
    rintro rfl
    exact ⟨fun x => rfl, fun x => rfl, rfl⟩, fun h => e.ext e' h.1 h.2.1 h.2.2⟩

@[simp, mfld_simps] theorem symm_symm (h : DiffeomorphOn I J M N n) : (h.symm).symm = h := rfl

/-! Continuity and smoothness results, mostly for convenient access. -/
section ContSmooth
variable (h : DiffeomorphOn I J M N n)

@[continuity]
protected theorem continuousOn : ContinuousOn h.toFun h.source :=
  h.toLocalHomeomorph.continuousOn

@[continuity]
theorem continuousOn_symm : ContinuousOn h.invFun h.target :=
  (h.symm).continuousOn

/-- A diffeomorphism on a set is continuous at any point of its source. -/
protected theorem continuousAt {x : M} (hx : x ∈ h.source) : ContinuousAt h.toFun x :=
  h.toLocalHomeomorph.continuousAt hx

/-- The inverse of a diffeomorphism on a set is continuous at any point of its target. -/
theorem continuousAt_symm {x : N} (hx : x ∈ h.target) : ContinuousAt h.invFun x :=
  (h.symm).continuousAt hx

protected theorem contMDiffOn : ContMDiffOn I J n h.toFun h.source :=
  h.contMDiffOn_toFun

theorem contMDiffOn_symm : ContMDiffOn J I n h.invFun h.target :=
  h.contMDiffOn_invFun

protected theorem contMDiffAt {x : M} (hx : x ∈ h.source) : ContMDiffAt I J n h.toFun x :=
  h.contMDiffOn_toFun.contMDiffAt (h.open_source.mem_nhds hx)

theorem contMDiffAt_symm {x : N} (hx : x ∈ h.target) : ContMDiffAt J I n h.invFun x :=
  (h.symm).contMDiffAt hx

protected theorem contMDiffWithinAt (s : Set M) {x : M} (hx : x ∈ h.source) :
    ContMDiffWithinAt I J n h.toFun s x :=
  (h.contMDiffAt hx).contMDiffWithinAt

theorem contMDiffWithinAt_symm (t : Set N) {x : N} (hx : x ∈ h.target) :
    ContMDiffWithinAt J I n h.invFun t x :=
  (h.symm).contMDiffWithinAt t hx

protected theorem mdifferentiableOn (hn : 1 ≤ n) : MDifferentiableOn I J h.toFun h.source :=
  (h.contMDiffOn).mdifferentiableOn hn

theorem mdifferentiableOn_symm (hn : 1 ≤ n) : MDifferentiableOn J I h.invFun h.target :=
  (h.symm).mdifferentiableOn hn
end ContSmooth

protected def refl : DiffeomorphOn I I M M n where
  toLocalHomeomorph := LocalHomeomorph.refl M
  contMDiffOn_toFun := contMDiff_id.contMDiffOn
  contMDiffOn_invFun := contMDiff_id.contMDiffOn

@[simp]
theorem refl_toEquiv : (DiffeomorphOn.refl I M n).toEquiv = Equiv.refl _ :=
  rfl

@[simp]
theorem coe_refl : ⇑(DiffeomorphOn.refl I M n) = id :=
  rfl

variable {I I' J M M' N n} in
/-- Composition of two local diffeomorphisms, restricted to the maximal domain where
this is defined. -/
protected def trans (h₁ : DiffeomorphOn I I' M M' n) (h₂ : DiffeomorphOn I' J M' N n) :
    DiffeomorphOn I J M N n where
  toLocalHomeomorph := h₁.toLocalHomeomorph.trans h₂.toLocalHomeomorph
  contMDiffOn_toFun := sorry -- (h₂.contMDiffOn).comp h₁.contMDiffOn h plus restricting
  contMDiffOn_invFun := sorry --h₁.contMDiffOn_invFun.comp h₂.contMDiffOn_invFun h + restricting

-- FIXME: show continuity and smoothness for trans also? or is that implied by comp results?

variable (h : DiffeomorphOn I I' M M' n)

@[simp]
theorem trans_refl : h.trans (DiffeomorphOn.refl I' M' n) = h := by
  refine DiffeomorphOn.ext _ _ (fun _ ↦ rfl) (fun _ ↦ rfl) ?_
  sorry -- TODO: need more simp lemmas around the source, later...

@[simp]
theorem refl_trans : (DiffeomorphOn.refl I M n).trans h = h := by
  refine DiffeomorphOn.ext _ _ (fun _ ↦ rfl) (fun _ ↦ rfl) ?_
  sorry -- similarly here

@[simp]
theorem coe_trans (h₁ : DiffeomorphOn I I' M M' n) (h₂ : DiffeomorphOn I' J M' N n) :
    ⇑(h₁.trans h₂) = h₂ ∘ h₁ :=
  rfl

@[simp]
theorem symm_refl : (DiffeomorphOn.refl I M n).symm = DiffeomorphOn.refl I M n :=
  -- TODO: add simp lemmas on the source
  DiffeomorphOn.ext _ _ (fun _ => rfl) sorry sorry

@[simp]
theorem symm_trans' (h₁ : DiffeomorphOn I I' M M' n) (h₂ : DiffeomorphOn I' J M' N n) :
    (h₁.trans h₂).symm = (h₂.symm).trans h₁.symm :=
  rfl

@[simp]
theorem symm_toEquiv : (h.symm).toEquiv = h.toEquiv.symm :=
  rfl

-- TODO: this doesn't compile
-- @[simp, mfld_simps]
-- theorem toEquiv_coe_symm : ⇑h.toEquiv.symm = h.symm :=
--   rfl

@[simp]
theorem symm_toLocalHomeomorph : (h.symm).toLocalHomeomorph = h.toLocalHomeomorph.symm :=
  rfl

@[simp]
theorem coe_toLocalHomeomorph : ⇑h.toLocalHomeomorph = h :=
  rfl

@[simp]
theorem coe_toLocalHomeomorph_symm : ⇑h.toLocalHomeomorph.symm = h.symm :=
  rfl

end DiffeomorphOn

/-- A **local diffeomorphism `f : M → N` at `x ∈ M`** is a `C^n` map `f` such that there are
neighbourhoods `s` and `t` of `x` and `f x`, respectively, for which `f` defines a diffeomorphism
from `s` to `t`. -/
-- This means `f` is a DiffeomorphOn `s`, where `x : s`
structure LocalDiffeomorphAt (x : M) extends DiffeomorphOn I J M N n where
  hx : x ∈ source

namespace LocalDiffeomorphAt
/-! Continuity and smoothness lemmas. -/
section ContSmooth
variable {x : M} (h : LocalDiffeomorphAt I J M N n x)
@[continuity]
protected theorem continuousOn : ContinuousOn h.toFun h.source :=
  h.contMDiffOn_toFun.continuousOn

@[continuity]
theorem continuousOn_symm : ContinuousOn h.invFun h.target :=
  (h.symm).continuousOn

/-- A local diffeomorphism at `x` is continuous at any point of its source. -/
protected theorem continuousAt {x : M} (hx : x ∈ h.source) : ContinuousAt h.toFun x :=
  h.toLocalHomeomorph.continuousAt hx

/-- The inverse of a local diffeomorphism at `x` is continuous at any point of its target. -/
theorem continuousAt_symm {x : N} (hx : x ∈ h.target) : ContinuousAt h.invFun x :=
  (h.symm).continuousAt hx

protected theorem contMDiffOn : ContMDiffOn I J n h.toFun h.source :=
  h.contMDiffOn_toFun

theorem contMDiffOn_symm : ContMDiffOn J I n h.invFun h.target :=
  h.contMDiffOn_invFun

theorem contMDiffAt (hx : x ∈ h.source) : ContMDiffAt I J n h.toFun x :=
  h.toDiffeomorphOn.contMDiffAt hx

protected theorem contMDiffAt_symm {x : N} (hx : x ∈ h.target) : ContMDiffAt J I n h.invFun x :=
  h.toDiffeomorphOn.contMDiffAt_symm hx

protected theorem contMDiffWithinAt {s : Set M} (hx : x ∈ h.source) :
    ContMDiffWithinAt I J n h.toFun s x :=
  h.toDiffeomorphOn.contMDiffWithinAt s hx

theorem contMDiffWithinAt_symm {s : Set N} {x : N} (hx : x ∈ h.target) :
    ContMDiffWithinAt J I n h.invFun s x :=
  (h.symm).contMDiffWithinAt s hx

protected theorem mdifferentiableOn (hn : 1 ≤ n) : MDifferentiableOn I J h.toFun h.source :=
  (h.contMDiffOn).mdifferentiableOn hn

theorem mdifferentiableOn_symm (hn : 1 ≤ n) : MDifferentiableOn J I h.invFun h.target :=
  (h.symm).mdifferentiableOn hn
end ContSmooth

-- TODO: add coe instance, ext lemmas, etc.

/-- Identity map as a local diffeomorphism at any point. -/
protected def refl (x : M) : LocalDiffeomorphAt I I M M n x where
  toDiffeomorphOn := DiffeomorphOn.refl I M n
  hx := trivial

@[simp]
theorem refl_toEquiv (x : M) : (LocalDiffeomorphAt.refl I M n x).toEquiv = Equiv.refl _ :=
  rfl

/- Inverse of a local diffeomorphism at `x`. -/
@[pp_dot]
protected def symm (x : M) (h : LocalDiffeomorphAt I I' M M' n x) :
    LocalDiffeomorphAt I' I M' M n (h.toFun x) where
  toDiffeomorphOn := h.toDiffeomorphOn.symm
  hx := h.map_source' h.hx

/-- Composing two local diffeomorphisms `h` and `h'` at `x` resp. `h x`,
by restricting to the maximal domain where their composition is well defined. -/
protected def trans (x : M) (h : LocalDiffeomorphAt I I' M M' n x)
    (h' : LocalDiffeomorphAt I' J M' N n (h.toFun x)) : LocalDiffeomorphAt I J M N n x where
  toDiffeomorphOn := h.toDiffeomorphOn.trans h'.toDiffeomorphOn
  hx := ⟨h.hx, h'.hx⟩

-- TODO: show basic properties of these constructions!
end LocalDiffeomorphAt

/-- A **local diffeomorphism `f : M → N`** is a `C^n` map `f` such that each `x : M` has
neighbourhoods `s` and `t` of `x` and `f x`, respectively, so `f` defines a diffeomorphism
from `s` to `t`.

We make these choices for each `x : M` part of the data defining a local diffeomorphism. -/
structure LocalDiffeomorph where
  toFun : M → N
  invFun : N → M
  -- Choices of neighbourhoods for each point.
  sources : Set (Opens M)
  targets : Set (Opens N)
  sourceAt : M → sources
  targetAt : M → targets
  mem_sources : ∀ x : M, x ∈ (sourceAt x).1
  mem_targets : ∀ x : M, (toFun x) ∈ (targetAt x).1
  map_sources : ∀ x x' : M, x' ∈ (sourceAt x).1 → toFun x' ∈ (targetAt x).1
  map_targets : ∀ x : M, ∀ y : N, y ∈ (targetAt x).1 → invFun y ∈ (sourceAt x).1
  /- `invFun` is a local left inverse of `toFun`, on each `sourceAt x`. -/
  left_inv : ∀ x x' : M, x' ∈ (sourceAt x).1 → invFun (toFun x') = x'
  /- `invFun` is a local right inverse of `toFun`, on each `targetAt x`. -/
  right_inv : ∀ x : M, ∀ y : N, y ∈ (targetAt x).1 → toFun (invFun y) = y
  contMDiffOn_toFun : ∀ x : M, ContMDiffOn I J n toFun (sourceAt x)
  contMDiffOn_invFun : ∀ x : M, ContMDiffOn J I n invFun (targetAt x)

namespace LocalDiffeomorph
/- Inverse of a local diffeomorphism. -/
@[pp_dot]
protected def symm (h : LocalDiffeomorph I J M N n) :
    LocalDiffeomorph J I N M n where
  toFun := h.invFun
  left_inv := by
    intro x hx -- hx: x ∈ targetAt (xrela), where xrela = h⁻¹y
    sorry -- fun _ => h.right_inv __ todofixup
  right_inv := sorry -- fun ... h.left_inv todofixup
  sources := h.targets
  targets := h.sources
  map_sources := sorry -- TODO!
  map_targets := sorry -- TODO!
  sourceAt := fun y ↦ (h.targetAt (h.invFun y))
  targetAt := fun y ↦ (h.sourceAt (h.invFun y))
  mem_sources := by
    intro y
    have : h.toFun (h.invFun y) = y := by sorry -- TODO: fixup!
      -- apply h.right_inv (h.invFun y)
      -- let sdf := h.mem_targets (h.invFun y)
      -- was: by apply h.right_inv
    let r := h.mem_targets (h.invFun y)
    rw [← this] at r
    sorry -- apply r
  mem_targets := sorry -- similar
  contMDiffOn_toFun := fun y ↦ h.contMDiffOn_invFun (h.invFun y)
  contMDiffOn_invFun := fun y ↦ h.contMDiffOn_toFun (h.invFun y)

/-! Continuity and smoothness results. -/
section ContSmooth
variable (h : LocalDiffeomorph I J M N n)
-- We deduce continuity from smoothness: no need for redundant work.
protected theorem contMDiff : ContMDiff I J n h.toFun := by
  show ∀ x : M, ContMDiffAt I J n h.toFun x
  intro x
  set s := (LocalDiffeomorph.sourceAt h x).1
  exact (h.contMDiffOn_toFun x).contMDiffAt (((s.2).mem_nhds_iff).mpr (h.mem_sources x))

@[continuity]
protected theorem continuous : Continuous h.toFun :=
  (h.contMDiff).continuous

@[continuity]
theorem continuous_symm : Continuous h.invFun :=
  (h.symm).continuous

/-- A local diffeomorphism is continuous every point. -/
protected theorem continuousAt (x : M) : ContinuousAt h.toFun x :=
  (h.continuous).continuousAt

/-- The inverse of a local diffeomorphism is continuous every point. -/
theorem continuousAt_symm (y : N) : ContinuousAt h.invFun y :=
  (h.symm).continuousAt y

protected theorem contMDiff_symm : ContMDiff J I n h.invFun :=
  (h.symm).contMDiff

protected theorem contMDiffOn (s : Set M) : ContMDiffOn I J n h.toFun s :=
  (h.contMDiff).contMDiffOn

theorem contMDiffOn_symm (t : Set N) : ContMDiffOn J I n h.invFun t :=
  (h.symm).contMDiffOn t

theorem contMDiffAt (x : M) : ContMDiffAt I J n h.toFun x :=
  (h.contMDiff).contMDiffAt

protected theorem contMDiffAt_symm (x : N) : ContMDiffAt J I n h.invFun x :=
  (h.symm).contMDiffAt x

protected theorem contMDiffWithinAt {s : Set M} {x : M} (hx : x ∈ s) :
    ContMDiffWithinAt I J n h.toFun s x :=
  (h.contMDiffOn s) x hx

theorem contMDiffWithinAt_symm {t : Set N} {y : N} (hy : y ∈ t) :
    ContMDiffWithinAt J I n h.invFun t y :=
  (h.symm).contMDiffWithinAt hy

protected theorem mdifferentiableOn (s : Set M) (hn : 1 ≤ n) : MDifferentiableOn I J h.toFun s :=
  (h.contMDiffOn s).mdifferentiableOn hn

theorem mdifferentiableOn_symm {t : Set N} (hn : 1 ≤ n) : MDifferentiableOn J I h.invFun t :=
  (h.symm).mdifferentiableOn t hn
end ContSmooth

variable {I J M N n} in
/-- A local diffeomorphism is a local homeomorphism, around each `x : M`. -/
noncomputable def LocalDiffeomorph.toLocalHomeomorphAt (h : LocalDiffeomorph I J M N n) (x : M) :
    LocalHomeomorph M N :=
  {
    toFun := h.toFun
    invFun := h.invFun
    source := h.sourceAt x
    target := h.targetAt x
    open_source := (h.sourceAt x).1.2
    open_target := (h.targetAt x).1.2
    map_source' := h.map_sources x
    map_target' := h.map_targets x
    left_inv' := h.left_inv x
    right_inv' := h.right_inv x
    continuous_toFun := (h.continuous).continuousOn
    continuous_invFun := (h.continuous_symm).continuousOn
  }

-- TODO: add coe instance, ext lemmas, etc.

/-- Identity map as a local diffeomorphism. -/
protected def refl : LocalDiffeomorph I I M M n where
  toFun := id
  left_inv := fun _ _ _ => rfl
  right_inv := fun _ _ _ => rfl
  -- At every point, we choose the set `univ`.
  sources := singleton ⟨univ, isOpen_univ⟩
  targets := singleton ⟨univ, isOpen_univ⟩
  mem_sources := by exact fun _ ↦ trivial
  mem_targets := by exact fun _ ↦ trivial
  map_sources := by intros; trivial
  map_targets := by intros; trivial
  -- XXX: can I golf these lines?
  sourceAt := by intro; apply Subtype.mk; apply Eq.refl
  targetAt := by intro; apply Subtype.mk; apply Eq.refl
  contMDiffOn_toFun := fun _ ↦ contMDiff_id.contMDiffOn
  contMDiffOn_invFun := fun _ ↦ contMDiff_id.contMDiffOn

-- TODO: complete this definition, mimicking what LocalHomeomorph.trans does.
-- /-- Composing two local diffeomorphisms, by restricting the source and target sets
-- to the maximal domain where their composition is well defined. -/
-- protected def trans (h : LocalDiffeomorph I I' M M' n)
--     (h' : LocalDiffeomorph I' J M' N n) : LocalDiffeomorph I J M N n where
--   toEquiv := h.toEquiv.trans h'.toEquiv
--   -- Source is h.sourceAt x ∩ h ⁻¹' (h'.sourceAt (h x)),
--   sourceAt := by
--     intro x
--     let s := (h.sourceAt x).1.1 ∩ h.toFun ⁻¹' (h'.sourceAt (h.toFun x))
--     have : IsOpen s := sorry
--     sorry -- ⟨s, this⟩, except for Lean shenanigans
--   -- target at x is h'.targetAx (h x) ∩ h' '' (h.targetAt x).
--   targetAt := by
--     intro x
--     let t := (h'.targetAt (h.toFun x)).1.1 ∩ h'.toFun '' (h.targetAt x).1.1
--     have : IsOpen t := sorry
--     sorry -- ⟨t, this⟩, plus some fuzz
--   sources := sorry
--   mem_sources := sorry
--   targets := sorry
--   mem_targets := sorry
--   contMDiffOn_toFun := sorry
--   contMDiffOn_invFun := sorry

-- TODO: add simple lemmas relating refl, symm and trans!
end LocalDiffeomorph

/-! Easy implications between `Diffeomorph`, `LocalDiffeomorph`,
  `DiffeomorphOn` and `LocalDiffeomorphAt`: each concept implies the next. -/
section EasyImplications
/-- A diffeomorphism on an open set is a local diffeomorph at each point of its source. -/
def DiffeomorphOn.toLocalDiffeomorphAt (h : DiffeomorphOn I J M N n) {x : M} (hx : x ∈ h.source) :
    LocalDiffeomorphAt I J M N n x :=
  { toDiffeomorphOn := h, hx := hx }

/-- A local diffeomorphism is a local diffeomorphism at each point. -/
noncomputable def LocalDiffeomorph.toLocalDiffeomorphAt (h : LocalDiffeomorph I J M N n) (x : M) :
    LocalDiffeomorphAt I J M N n x :=
  {
    -- FIXME: why can't I use dot notation?
    toLocalHomeomorph := LocalDiffeomorph.toLocalHomeomorphAt h x
    hx := h.mem_sources x
    contMDiffOn_toFun := h.contMDiffOn (h.sourceAt x)
    contMDiffOn_invFun := h.contMDiffOn_symm (h.targetAt x)
  }

-- /-- For each `x : M`, a local diffeomorph is a diffeomorphism on some open set containing `x`. -/
-- FIXME: do I want to expose this outside of this file?
private noncomputable def LocalDiffeomorph.toDiffeomorphOn (h : LocalDiffeomorph I J M N n)
    (x : M) : DiffeomorphOn I J M N n :=
  (h.toLocalDiffeomorphAt x).toDiffeomorphOn

/-- A diffeomorphism is a local diffeomorphism. -/
-- FIXME: can I deduplicate this proof with with `LocalDiffeomorph.refl`?
def Diffeomorph.toLocalDiffeomorph (h : Diffeomorph I J M N n) : LocalDiffeomorph I J M N n :=
  {
    toFun := h.toFun
    invFun := h.invFun
    left_inv := by intros; simp
    right_inv := by intros; simp
    sources := singleton ⟨univ, isOpen_univ⟩
    targets := singleton ⟨univ, isOpen_univ⟩
    map_sources := by intros; trivial
    map_targets := by intros; trivial
    sourceAt := by intro; apply Subtype.mk; apply Eq.refl
    targetAt := by intro; apply Subtype.mk; apply Eq.refl
    mem_sources := fun _ ↦ (by exact trivial)
    mem_targets := fun _ ↦ (by exact trivial)
    contMDiffOn_toFun := by
      intro
      simp only [Equiv.toFun_as_coe, coe_toEquiv, Opens.mk_univ, Opens.coe_top, contMDiffOn_univ]
      exact h.contMDiff_toFun
    contMDiffOn_invFun := by
      intro
      simp only [Equiv.toFun_as_coe, coe_toEquiv, Opens.mk_univ, Opens.coe_top, contMDiffOn_univ]
      exact h.contMDiff_invFun
  }

/-- A diffeomorphism is a local diffeomorphism at each point. -/
noncomputable def Diffeomorph.toLocalDiffeomorphAt (h : Diffeomorph I J M N n) (x : M) :
    LocalDiffeomorphAt I J M N n x :=
  (h.toLocalDiffeomorph).toLocalDiffeomorphAt x

/-- A bijective local diffeomorphism is a diffeomorphism.
We formalise bijectivity by asking that `toFun` and `invFun` be left and right inverses globally. -/
def Diffeomorph.of_localDiffeomorph (h : LocalDiffeomorph I J M N n)
    (hleft_inv : LeftInverse h.invFun h.toFun) (hright_inv : RightInverse h.invFun h.toFun) :
    Diffeomorph I J M N n :=
  {
    toFun := h.toFun
    invFun := h.invFun
    left_inv := hleft_inv
    right_inv := hright_inv
    contMDiff_toFun := h.contMDiff
    contMDiff_invFun := h.contMDiff_symm
  }
end EasyImplications

-- FIXME: should be able to write h.symm, h instead of h.invFun and h.toFun!
-- add enough basic API to make this possible

/-! Local diffeomorphisms have invertible differentiable at each point in their source.
Conversely, an invertible differential (everywhere resp. at `x`) implies `f` is a local
diffeomorphism (resp. a local diffeomorphism at `x`).
This follows from the inverse function theorem. -/
section Differentials
variable [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners J N]
variable {I J M M' N n}

section simpler -- FIXME: move to Algebra.Module.Basic
variable {R : Type*} [Ring R]
variable {E'' : Type*} [TopologicalSpace E''] [AddCommMonoid E''] [Module R E'']
variable {F'' : Type*} [TopologicalSpace F''] [AddCommMonoid F''] [Module R F'']

lemma LeftInverse.of_composition {f' : E'' →L[R] F''} {g' : F'' →L[R] E''}
    (hinv : g'.comp f' = ContinuousLinearMap.id R E'') : LeftInverse g' f' := by
  have : g' ∘ f' = id := calc g' ∘ f'
      _ = ↑(g'.comp f') := by rw [ContinuousLinearMap.coe_comp']
      _ = ↑( ContinuousLinearMap.id R E'') := by rw [hinv]
      _ = id := by rw [ContinuousLinearMap.coe_id']
  exact congrFun this

lemma RightInverse.of_composition {f' : E'' →L[R] F''} {g' : F'' →L[R] E''}
    (hinv : f'.comp g' = ContinuousLinearMap.id R F'') : RightInverse g' f' :=
  LeftInverse.of_composition hinv
end simpler

/-- If `f` is a local diffeomorphism at `x`,
  the differential of `f` at `x` is a linear isomorphism. -/
noncomputable def LocalDiffeomorphAt.differential_toContinuousLinearEquiv (hn : 1 ≤ n)
    {x : M} (h : LocalDiffeomorphAt I J M N n x) :
    ContinuousLinearEquiv (RingHom.id 𝕜) (TangentSpace I x) (TangentSpace J (h.toFun x)) := by
  let y := h.toFun x
  have hy : y ∈ h.target := h.toLocalEquiv.mapsTo h.hx
  let A := mfderiv I J h.toFun x
  let B := mfderiv J I h.invFun (h.toFun x)

  -- FUTURE: can the `differentiability` tactic show this?
  have hgat : MDifferentiableAt J I h.invFun y :=
    (h.contMDiffAt_symm (h.toLocalEquiv.mapsTo h.hx)).mdifferentiableAt hn
  have hfat : MDifferentiableAt I J h.toFun x :=
    (h.contMDiffAt h.hx).mdifferentiableAt hn
  have inv1 : B.comp A = ContinuousLinearMap.id 𝕜 (TangentSpace I x) := calc B.comp A
    _ = mfderiv I I (h.invFun ∘ h.toFun) x := (mfderiv_comp x hgat hfat).symm
    _ = mfderivWithin I I (h.invFun ∘ h.toFun) h.source x :=
      (mfderivWithin_of_open h.open_source h.hx).symm
    _ = mfderivWithin I I id h.source x :=
      mfderivWithin_congr (h.open_source.uniqueMDiffWithinAt h.hx) h.left_inv' (h.left_inv' h.hx)
    _ = mfderiv I I id x := mfderivWithin_of_open h.open_source h.hx
    _ = ContinuousLinearMap.id 𝕜 (TangentSpace I x) := mfderiv_id I
  have inv2 : A.comp B = ContinuousLinearMap.id 𝕜 (TangentSpace J (h.toFun x)) := calc A.comp B
    _ = mfderiv J J (h.toFun ∘ h.invFun) y := by
          -- Use the chain rule: rewrite the base point (I ∘ e ∘ e.invFun ∘ I.invFun) x = x, ...
          let sdf := h.left_inv' h.hx
          sorry -- TODO: this fails with `motive is not type correct` -- rw [← sdf] at hfat
          -- ... but also the points x and y under the map.
          -- for some reason, cannot plug this in directly
          -- have : (LocalEquiv.invFun h.toLocalEquiv y) = x := (h.left_inv' hx)
          -- exact (this ▸ (mfderiv_comp y hfat hgat)).symm
    _ = mfderivWithin J J (h.toFun ∘ h.invFun) h.target y :=
      (mfderivWithin_of_open h.open_target hy).symm
    _ = mfderivWithin J J id h.target y :=
      mfderivWithin_congr (h.open_target.uniqueMDiffWithinAt hy) h.right_inv' (h.right_inv' hy)
    _ = mfderiv J J id y := mfderivWithin_of_open h.open_target hy
    _ = ContinuousLinearMap.id 𝕜 (TangentSpace J y) := mfderiv_id J

  exact {
    toFun := A
    invFun := B
    left_inv := LeftInverse.of_composition inv1
    right_inv := RightInverse.of_composition inv2
    continuous_toFun := A.cont
    continuous_invFun := B.cont
    map_add' := fun x_1 y ↦ ContinuousLinearMap.map_add A x_1 y
    map_smul' := by intros; simp
  }

/-- If `f` is a diffeomorphism on `s`, its differential is a linear isomorphism at each `x ∈ s`. -/
-- not sure if this result should be generally available; in any case, it's a simple corollary
noncomputable def DiffeomorphOn.differential_toContinuousLinearEquiv (hn : 1 ≤ n) {x : M}
    (h : DiffeomorphOn I J M N n) (hx : x ∈ h.source) :
    ContinuousLinearEquiv (RingHom.id 𝕜) (TangentSpace I x) (TangentSpace J (h.toFun x)) :=
  (h.toLocalDiffeomorphAt hx).differential_toContinuousLinearEquiv hn

/-- If `f` is a local diffeomorphism, the differential is a linear isomorphism at each point. -/
noncomputable def LocalDiffeomorph.differential_toContinuousLinearEquiv (hn : 1 ≤ n) {x : M}
    (h : LocalDiffeomorph I J M N n):
    ContinuousLinearEquiv (RingHom.id 𝕜) (TangentSpace I x) (TangentSpace J (h.toFun x)) :=
  (h.toLocalDiffeomorphAt x).differential_toContinuousLinearEquiv hn

/-- A local diffeomorphism at `x` has bijective differential at `x`. -/
lemma LocalDiffeomorphAt.differential_bijective (hn : 1 ≤ n) {x : M}
    (h : LocalDiffeomorphAt I J M N n x) : Bijective (mfderiv I J h.toFun x) := by
  let aux := h.differential_toContinuousLinearEquiv hn
  exact bijective_of_inverses aux.left_inv aux.right_inv

/-- A local diffeomorphism has bijective differential at each point in its source. -/
lemma DiffeomorphOn.differential_bijective (hn : 1 ≤ n) {x : M}
    (h : DiffeomorphOn I J M N n) (hx : x ∈ h.source) : Bijective (mfderiv I J h.toFun x) :=
  (h.toLocalDiffeomorphAt hx).differential_bijective hn

/-- A diffeomorphism has bijective differential at each point. -/
lemma Diffeomorph.differential_bijective (hn : 1 ≤ n) (f : Diffeomorph I J M N n) {x : M} :
    Bijective (mfderiv I J f.toFun x) :=
  (f.toLocalDiffeomorphAt x).differential_bijective hn

/-- If `f : M → N` is smooth at `x` and `mfderiv I J f x` is a linear isomorphism,
  then `f` is a local diffeomorphism at `x`. -/
-- XXX: which is more convenient for applications: hinv₁₂ stated with ∘ or with comp?
def LocalDiffeomorphAt.of_DifferentialIsomorphismAt (hn : 1 ≤ n) {x : M} {f : M → N}
    {f' : TangentSpace I x →L[𝕜] TangentSpace J (f x)} (hf' : HasMFDerivAt I J f x f')
    {g' : TangentSpace J (f x) →L[𝕜] TangentSpace I x} (hinv₁ : g' ∘ f' = id) (hinv₂ : f' ∘ g' = id)
    (hf : ContMDiffAt I J n f x) : LocalDiffeomorphAt I J M N n x := by
  --have : f' = mfderiv I J f x := hasMFDerivAt_unique hf' (hf.mdifferentiableAt hn).hasMFDerivAt
  --rw [this] at *
  have : ContinuousLinearEquiv (RingHom.id 𝕜) (TangentSpace I x) (TangentSpace J (f x)) :=
    {
      toFun := f'
      invFun := g'
      continuous_toFun := f'.cont
      continuous_invFun := g'.cont
      map_add' := fun x_1 y ↦ ContinuousLinearMap.map_add f' x_1 y
      map_smul' := by intros; simp
      left_inv := congrFun hinv₁
      right_inv := congrFun hinv₂
    }
  -- Now, I'd apply the inverse function theorem, which mathlib only has for normed space.
  -- Let's wait for the general version before completing this.
  sorry

-- TODO: what would these two statements mean in Lean? How could I formalise them?
-- In my setting, they are mostly true by definition.

-- If `f : M → N` is a local diffeomorphism at each `x ∈ s`, it's a local diffeomorphism on `s`.
-- If `f : M → N` is a local diffeomorphism at each point, it's a local diffeomorphism.
-- also: can I state both this as an iff statement?

/-- If `f : M → N` is `C^n` and each differential `mfderiv I J f x` is a linear isomorphism,
  `f` is a local diffeomorphism. -/
-- formalise: pick an inverse of each differential, yielding a map on the tangent bundles
-- TODO: impose that each map g_x is continuous and linear, we *do* need that
def LocalDiffeomorph.of_differentialInvertible (hn : 1 ≤ n) {x : M}
    {f : M → N} (hf : ContMDiff I J n f) {g' : TangentBundle J N → TangentBundle I M}
    (hg : ∀ x : M, Continuous (fun v ↦ (g' ⟨f x, v⟩).2))
    (hinv₁ : (tangentMap I J f) ∘ g' = id) (hinv₂ : g' ∘ (tangentMap I J f) = id) :
    LocalDiffeomorph I J M N n := by

  let df := tangentMap I J f
  let dfx := fun v ↦ (df ⟨x, v⟩).2 -- differential of f at x
  have defeq1 : dfx = mfderiv I J f x := by rfl
  let g'y := fun v ↦ (g' ⟨f x, v⟩).2 -- g' at y
  have : ∀ v : TangentSpace J (f x),
      TangentSpace I (g' { proj := f x, snd := v }).proj = TangentSpace I x := by
    intro; rfl
  have inv1 : dfx ∘ g'y = id := sorry -- follows from hinv₁, somehow
  have inv1 : (mfderiv I J f x) ∘ g'y = id := by rw [← defeq1]; exact inv1
  have inv2 : g'y ∘ dfx = id := sorry -- follows from hinv₂, somehow
  have inv2 : g'y ∘ (mfderiv I J f x) = id := by rw [← defeq1]; exact inv2

  let hfx := ((hf x).mdifferentiableAt hn).hasMFDerivAt
  -- have : LocalDiffeomorphAt I J M N n x :=
  --   LocalDiffeomorphAt.of_DifferentialIsomorphismAt (g' := g'y) hn hfx inv1 inv2 (hf x)
  -- now, run the above argument for all x together
  sorry

end Differentials

-- can I say that **the tangent map of a local diffeo is a bundle isomorphism?**
