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

/-- A **local diffeomorphism `f : M → N` at `x ∈ M`** is a `C^n` map `f` such that there are
neighbourhoods `s` and `t` of `x` and `f x`, respectively, for which `f` defines a diffeomorphism
from `s` to `t`. -/
-- In Lean `s` and `t` are `source` and `target`, respectively.
structure LocalDiffeomorphAt (x : M) extends LocalHomeomorph M N where
  hx : x ∈ source
  contMDiffOn_toFun : ContMDiffOn I J n toFun source
  contMDiffOn_invFun : ContMDiffOn J I n invFun target

namespace LocalDiffeomorphAt
/-- Identity map as a local diffeomorphism at any point. -/
protected def refl (x : M) : LocalDiffeomorphAt I I M M n x where
  toLocalHomeomorph := LocalHomeomorph.refl M
  hx := by exact trivial
  contMDiffOn_toFun := contMDiff_id.contMDiffOn
  contMDiffOn_invFun := contMDiff_id.contMDiffOn

@[simp]
theorem refl_toEquiv (x : M) : (LocalDiffeomorphAt.refl I M n x).toEquiv = Equiv.refl _ :=
  rfl

/- Inverse of a local diffeomorphism at `x`. -/
@[pp_dot]
protected def symm (x : M) (h : LocalDiffeomorphAt I I' M M' n x) :
    LocalDiffeomorphAt I' I M' M n (h.toFun x) where
  toLocalHomeomorph := h.toLocalHomeomorph.symm
  hx := h.map_source' h.hx
  contMDiffOn_toFun := h.contMDiffOn_invFun
  contMDiffOn_invFun := h.contMDiffOn_toFun

/-- Composing two local diffeomorphisms at `x` if the target of the first coincides with the source
of the second, and the base points also do. -/
--@[simps]
protected def trans' (x : M) (h : LocalDiffeomorphAt I I' M M' n x)
    (h' : LocalDiffeomorphAt I' J M' N n (h.toFun x)) (hyp : h.target = h'.source) : LocalDiffeomorphAt I J M N n x where
  toLocalHomeomorph := h.toLocalHomeomorph.trans' h'.toLocalHomeomorph hyp
  hx := h.hx
  contMDiffOn_toFun := sorry -- h.contMDiffOn_toFun.comp h'.contMDiffOn_toFun plus details
  contMDiffOn_invFun := sorry --h'.contMDiffOn_invFun.comp h.contMDiffOn_invFun plus details

/-- Composing two local diffeomorphisms at `x`, by restricting to the maximal domain where their
composition is well defined. -/
-- XXX: do I need trans' also, or is just trans fine??
protected def trans (x : M) (h : LocalDiffeomorphAt I I' M M' n x)
    (h' : LocalDiffeomorphAt I' J M' N n (h.toFun x)) : LocalDiffeomorphAt I J M N n x where
  toLocalHomeomorph := h.toLocalHomeomorph.trans h'.toLocalHomeomorph
  hx := ⟨h.hx, h'.hx⟩
  contMDiffOn_toFun := sorry
  contMDiffOn_invFun := sorry
end LocalDiffeomorphAt


/-- A **local diffeomorphism `f : M → N`** is a `C^n` map `f` such that each `x : M` has
neighbourhoods `s` and `t` of `x` and `f x`, respectively, so `f` defines a diffeomorphism
from `s` to `t`.

We make these choices, for each `x` part of the data defining a local diffeomorphism. -/
structure LocalDiffeomorph extends LocalHomeomorph M N where
  source := univ -- for clarity, can I elide these??
  target := univ
  -- Choices of neighbourhoods for each point.
  sources : Set (Opens M)
  targets : Set (Opens N)
  sourceAt : M → sources
  targetAt : M → targets
  contMDiffOn_toFun : ∀ x : M, ContMDiffOn I J n toFun (sourceAt x)
  contMDiffOn_invFun : ∀ x : M, ContMDiffOn J I n invFun (targetAt x)

namespace LocalDiffeomorphism
/-- Identity map as a local diffeomorphism. -/
protected def refl : LocalDiffeomorph I I M M n where
  toLocalHomeomorph := LocalHomeomorph.refl M
  -- At every point, we choose the set `univ`.
  sources := singleton ⟨univ, isOpen_univ⟩
  targets := singleton ⟨univ, isOpen_univ⟩
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
-- theorem refl_toEquiv : (LocalDiffeomorph.refl I M n).toEquiv = Equiv.refl _ :=
--   rfl

/- Inverse of a local diffeomorphism. -/
@[pp_dot]
protected def symm (h : LocalDiffeomorph I I' M M' n) :
    LocalDiffeomorph I' I M' M n where
  toLocalHomeomorph := h.toLocalHomeomorph.symm
  -- XXX: why are all of these not required?
  -- sources := h.targets
  -- targets := h.sources
  -- sourceAt := fun y ↦ (h.targetAt (h.invFun y))
  -- targetAt := fun y ↦ (h.sourceAt (h.invFun y))
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
  targets := sorry
  contMDiffOn_toFun := sorry
  contMDiffOn_invFun := sorry
end LocalDiffeomorphism

-- A local diffeomorphism is a local diffeomorphism at each point.
-- If f is a local diffeomorphism at each point, it's a local diffeomorphism.
-- The identity function is a local diffeo.



/-- A `C^n` diffeomorphism between open subsets of `M` and `N`.
This is the `C^n` analogue of `LocalHomeomorph`; we don't call it so as `LocalDiffeomorph` means
something else. -/
structure DiffeomorphOn extends LocalHomeomorph M N where
  contMDiffOn_toFun : ContMDiffOn I J n toFun source
  contMDiffOn_invFun : ContMDiffOn J I n invFun target
