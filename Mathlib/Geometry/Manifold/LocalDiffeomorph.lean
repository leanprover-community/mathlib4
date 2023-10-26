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

A `C^n` map `f : M → N` is a **local diffeomorphism at `x`** iff there are neighbourhoods `s` and `t`
of `x` and `f x`, respectively such that `f` restricts to a diffeomorphism from `s` and `t`.
`f` is called a **local diffeomorphism** iff it is a local diffeomorphism at every `x ∈ M`.

## Main definitions
* `LocalDiffeomorphAt x`: `f` is a local diffeomorphism at `x`
* `LocalDiffeomorph`: `f` is a local diffeomorphism
* `DiffeomorphOn`: `f` is a "diffeomorphism between open subsets of `M` and `N`, respectively.
This definition is an implementation detail, and not meant for use outside of this file.

## Main results
to be inserted!

## Design decisions
For all definitions, we use the junk value pattern: a local diffeomorphism at `x` is still given
by a function on all of `M`; its values outside its `source` are irrelevant. (This matches the
treatment of smooth manifolds and `LocalHomeomorph`.)

This combines with the second major design decision: all our definitions are bundled. That is,
we consider `f` together with a choice `g` of inverse. For local diffeomorphisms, `g` can take any
values outside of `f.target`.
A local diffeomorphism contains the data `f` and `g`, together with proofs that these define a
local diffeomorphism at each point.

**TODO**: stuff here
Tags: optional, later!

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

/-- A "diffeomorphism on" `s` is a function `f : M → N` such that `f` restricts to a diffeomorphism
`s → t` between open subsets of `M` and `N`, respectively. -/
-- In Lean, `s` and `t` are `source` and `target`, respectively.
structure DiffeomorphOn extends LocalHomeomorph M N where
  contMDiffOn_toFun : ContMDiffOn I J n toFun source
  contMDiffOn_invFun : ContMDiffOn J I n invFun target

namespace DiffeomorphOn
-- Simple properties, mostly convenience access to the different proofs.
-- TODO: go over Diffeomorph and complete this list. Including a Coe instance, ext lemma etc.
@[continuity]
protected theorem continuousOn (h : DiffeomorphOn I J M N n) : ContinuousOn h.toFun h.source :=
  h.contMDiffOn_toFun.continuousOn

@[continuity]
protected theorem continuousOn_symm (h : DiffeomorphOn I J M N n) :
    ContinuousOn h.invFun h.target :=
  h.contMDiffOn_invFun.continuousOn

protected theorem contMDiffOn (h : DiffeomorphOn I J M N n) : ContMDiffOn I J n h.toFun h.source :=
  h.contMDiffOn_toFun

protected theorem contMDiffOn_symm (h : DiffeomorphOn I J M N n) :
    ContMDiffOn J I n h.invFun h.target :=
  h.contMDiffOn_invFun

protected theorem contMDiffAt (h : DiffeomorphOn I J M N n) {x : M} (hx : x ∈ h.source) :
    ContMDiffAt I J n h.toFun x :=
  h.contMDiffOn_toFun.contMDiffAt (h.open_source.mem_nhds hx)

protected theorem contMDiffAt_symm (h : DiffeomorphOn I J M N n) {x : N} (hx : x ∈ h.target) :
    ContMDiffAt J I n h.invFun x :=
  h.contMDiffOn_invFun.contMDiffAt (h.open_target.mem_nhds hx)

protected theorem contMDiffWithinAt (h : DiffeomorphOn I J M N n)
    {s : Set M} {x : M} (hx : x ∈ h.source) : ContMDiffWithinAt I J n h.toFun s x :=
  (h.contMDiffAt hx).contMDiffWithinAt

protected theorem contMDiffWithinAt_symm (h : DiffeomorphOn I J M N n)
    {s : Set N} {x : N} (hx : x ∈ h.target) : ContMDiffWithinAt J I n h.invFun s x :=
  (h.contMDiffAt_symm hx).contMDiffWithinAt

protected theorem mdifferentiableOn (h :  DiffeomorphOn I J M N n) (hn : 1 ≤ n) :
    MDifferentiableOn I J h.toFun h.source :=
  (h.contMDiffOn).mdifferentiableOn hn

protected theorem mdifferentiableOn_symm (h :  DiffeomorphOn I J M N n) (hn : 1 ≤ n) :
    MDifferentiableOn J I h.invFun h.target :=
  (h.contMDiffOn_symm).mdifferentiableOn hn

protected def refl : DiffeomorphOn I I M M n where
  contMDiffOn_toFun := contMDiff_id.contMDiffOn
  contMDiffOn_invFun := contMDiff_id.contMDiffOn
  toLocalHomeomorph := LocalHomeomorph.refl M

@[simp]
theorem refl_toEquiv : (DiffeomorphOn.refl I M n).toEquiv = Equiv.refl _ :=
  rfl

/-- Composition of two local diffeomorphisms, restricted to the maximal domain where
this is defined. -/
protected def trans (h₁ : DiffeomorphOn I I' M M' n) (h₂ : DiffeomorphOn I' J M' N n) :
    DiffeomorphOn I J M N n where
  toLocalHomeomorph := h₁.toLocalHomeomorph.trans h₂.toLocalHomeomorph
  contMDiffOn_toFun := sorry -- (h₂.contMDiffOn).comp h₁.contMDiffOn h plus restricting
  contMDiffOn_invFun := sorry --h₁.contMDiffOn_invFun.comp h₂.contMDiffOn_invFun h + restricting

/-- Inverse of a diffeomorphism on a set. -/
@[pp_dot]
protected def symm (h : DiffeomorphOn I I' M M' n) : DiffeomorphOn I' I M' M n where
  contMDiffOn_toFun := h.contMDiffOn_invFun
  contMDiffOn_invFun := h.contMDiffOn_toFun
  toLocalHomeomorph := h.toLocalHomeomorph.symm

@[simp]
theorem symm_toLocalHomeomorph (h : DiffeomorphOn I J M N n) :
    (h.symm).toLocalHomeomorph = h.toLocalHomeomorph.symm :=
  rfl

-- TODO: add more API for refl, trans and symm
end DiffeomorphOn

/-- A **local diffeomorphism `f : M → N` at `x ∈ M`** is a `C^n` map `f` such that there are
neighbourhoods `s` and `t` of `x` and `f x`, respectively, for which `f` defines a diffeomorphism
from `s` to `t`. -/
-- This means `f` is a DiffeomorphOn `s`, where `x : s`
structure LocalDiffeomorphAt (x : M) extends DiffeomorphOn I J M N n where
  hx : x ∈ source

namespace LocalDiffeomorphAt
-- TODO: add coe instance, ext lemmas, etc.

/-- Identity map as a local diffeomorphism at any point. -/
protected def refl (x : M) : LocalDiffeomorphAt I I M M n x where
  toDiffeomorphOn := DiffeomorphOn.refl I M n
  hx := by exact trivial

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
  toLocalHomeomorph := h.toLocalHomeomorph.trans h'.toLocalHomeomorph
  hx := ⟨h.hx, h'.hx⟩
  -- FIXME: can I reuse toDiffeomorphOn.trans?
  contMDiffOn_toFun := sorry -- (h₂.contMDiffOn).comp h₁.contMDiffOn h plus restricting
  contMDiffOn_invFun := sorry --h₁.contMDiffOn_invFun.comp h₂.contMDiffOn_invFun h + restricting

-- TODO: show basic properties of these constructions!
end LocalDiffeomorphAt

/-- A **local diffeomorphism `f : M → N`** is a `C^n` map `f` such that each `x : M` has
neighbourhoods `s` and `t` of `x` and `f x`, respectively, so `f` defines a diffeomorphism
from `s` to `t`.

We make these choices, for each `x` part of the data defining a local diffeomorphism. -/
structure LocalDiffeomorph extends LocalHomeomorph M N where
  --source := univ -- for clarity, can I elide these??
  --target := univ
  -- Choices of neighbourhoods for each point.
  sources : Set (Opens M)
  targets : Set (Opens N)
  sourceAt : M → sources
  mem_sources : ∀ x : M, x ∈ (sourceAt x).1
  targetAt : M → targets
  mem_targets : ∀ x : M, (toFun x) ∈ (targetAt x).1
  contMDiffOn_toFun : ∀ x : M, ContMDiffOn I J n toFun (sourceAt x)
  contMDiffOn_invFun : ∀ x : M, ContMDiffOn J I n invFun (targetAt x)

namespace LocalDiffeomorph
-- TODO: add coe instance, ext lemmas, etc.

/-- Identity map as a local diffeomorphism. -/
protected def refl : LocalDiffeomorph I I M M n where
  toLocalHomeomorph := LocalHomeomorph.refl M
  -- At every point, we choose the set `univ`.
  sources := singleton ⟨univ, isOpen_univ⟩
  targets := singleton ⟨univ, isOpen_univ⟩
  mem_sources := fun x ↦ sorry -- should be : (by exact trivial)
  mem_targets := fun x ↦ sorry -- should be: (by exact trivial)
  sourceAt := sorry -- obvious
    -- intro x --fun _ ↦ ⟨univ, isOpen_univ⟩
    -- set s : Opens M := ⟨univ, isOpen_univ⟩
    -- exact mem_singleton_iff.mpr (Eq.subset rfl)--aesop?--rw [← mem_singleton_iff]--apply codRestrict (fun a ↦ s) {s} _ x
    -- --rw [← s]--let sdf := mem_singleton_iff.mp trivial
    -- --rw [mem_singleton_iff]--aesop?--let sdf := ⟨univ, isOpen_univ⟩
  targetAt := sorry
  contMDiffOn_toFun := fun _ ↦ contMDiff_id.contMDiffOn
  contMDiffOn_invFun := fun _ ↦ contMDiff_id.contMDiffOn

-- @[simp]
-- theorem refl_toEquiv : (LocalDiffeomorph.refl I M n).toLocalEquiv = LocalEquiv.refl _ :=
--   rfl

/- Inverse of a local diffeomorphism. -/
@[pp_dot]
protected def symm (h : LocalDiffeomorph I J M N n) :
    LocalDiffeomorph J I N M n where
  toLocalHomeomorph := h.toLocalHomeomorph.symm
  sources := h.targets
  targets := h.sources
  sourceAt := fun y ↦ (h.targetAt (h.invFun y))
  targetAt := fun y ↦ (h.sourceAt (h.invFun y))
  mem_sources := by
    intro y
    let r := h.mem_targets (h.invFun y)
    have : h.toLocalEquiv (LocalEquiv.invFun h.toLocalEquiv y) = y := sorry -- left_inv!
    rw [this] at r
    exact r
  mem_targets := sorry -- should be similar
  contMDiffOn_toFun := fun y ↦ h.contMDiffOn_invFun (h.invFun y)
  contMDiffOn_invFun := fun y ↦ h.contMDiffOn_toFun (h.invFun y)

/-- Composing two local diffeomorphisms at `x` resp. `h x` if for each `x ∈ M`, the target of
the first at `x` coincides with the source of the second at `h x`. -/
-- I'm not sure if this is actually useful, or not.
-- --@[simps]
protected def trans' (h : LocalDiffeomorph I I' M M' n)
    (h' : LocalDiffeomorph I' J M' N n) (hyp : ∀ x : M, (h.targetAt x).1 = (h'.sourceAt (h.toFun x)).1) : LocalDiffeomorph I J M N n where
  -- both source and target are univ, so the last is obvious. just cannot convince Lean yet
  toLocalHomeomorph := h.toLocalHomeomorph.trans' h'.toLocalHomeomorph sorry
  -- sources := h.sources
  -- targets := h'.targets
  -- This is h.sourceAt x ∩ h ⁻¹' (h'.sourceAt (h x)), in this case it's just h.sourceAt.
  sourceAt := h.sourceAt
  -- Since source and target agree, this is just targetAt.
  targetAt := fun x ↦ h'.targetAt (h.toFun x)
  mem_sources := h.mem_sources
  mem_targets := fun x ↦ h'.mem_targets (h.toFun x)
  contMDiffOn_toFun := sorry -- h.contMDiffOn_toFun.comp h'.contMDiffOn_toFun plus details
  contMDiffOn_invFun := sorry --h'.contMDiffOn_invFun.comp h.contMDiffOn_invFun plus details

/-- Composing two local diffeomorphisms at `x`, by restricting to the maximal domain where their
composition is well defined. -/
protected def trans (h : LocalDiffeomorph I I' M M' n)
    (h' : LocalDiffeomorph I' J M' N n) : LocalDiffeomorph I J M N n where
  toLocalHomeomorph := h.toLocalHomeomorph.trans h'.toLocalHomeomorph
  -- Source is h.sourceAt x ∩ h ⁻¹' (h'.sourceAt (h x)),
  sourceAt := by
    intro x
    let s := (h.sourceAt x).1.1 ∩ h.toFun ⁻¹' (h'.sourceAt (h.toFun x))
    have : IsOpen s := sorry
    sorry -- ⟨s, this⟩, except for Lean shenanigans
  -- target at x is h'.targetAx (h x) ∩ h' '' (h.targetAt x).
  targetAt := by
    intro x
    let t := (h'.targetAt (h.toFun x)).1.1 ∩ h'.toFun '' (h.targetAt x).1.1
    have : IsOpen t := sorry
    sorry -- ⟨t, this⟩, plus some fuzz
  sources := sorry
  mem_sources := sorry
  targets := sorry
  mem_targets := sorry
  contMDiffOn_toFun := sorry
  contMDiffOn_invFun := sorry

-- TODO: add simple lemmas relating refl, symm and trans!
end LocalDiffeomorph

-- A DiffeomorphOn is a local diffeo at each point of its source.

-- A local diffeomorph is a local diffeomorphism at each point.

-- what would this mean: if f : M → N f is a local diffeomorphism at each point,
-- it's a local diffeomorphism.

-- if f is a local diffeo at x, the differential df_x is a linear iso.

-- conversely, if f is smooth and df_x is a linear iso, then f is a local diffeo at x
-- uses the inverse function theorem, might be a tad harder to show. punt on first first.

-- if f is a DiffeoOn, the differential df_x is a linear iso for each x ∈ source.
-- not sure if this should be outward-facing; in any case, should be a simple corollary.

-- if f is a local diffeo, the differential is a linear iso at each point.

-- if f is smooth and each differential df_x is a linear iso, f is a local diffeo

-- a bijective local diffeo is a diffeo: hard to formalise?!
-- a diffeo is a local diffeo
-- a diffeo is bijective (easy)
-- corollary: a diffeo is a bijective local diffeo (exact with two things)

-- can I say that **the tangent map is a bundle isomorphism?**
