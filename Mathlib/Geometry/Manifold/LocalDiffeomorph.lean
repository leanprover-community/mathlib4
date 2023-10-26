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
* more, to be inserted!
* `LocalDiffeomorphAt.differential_toContinuousLinearEquiv`: if `f` is a local diffeomorphism at `x`,
the differential `mfderiv I J n f x` is a continuous linear isomorphism.
* `LocalDiffeomorphAt.of_DifferentialIsoAt`: conversely, if `f` is `C^n` at `x` and
`mfderiv I J n f x` is a linear isomorphism, `f` is a local diffeomorphism at x.

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

-- FIXME, everywhere: move n to a different position, to match Diffeomorph?

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
structure LocalDiffeomorph extends Equiv M N where
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
theorem toEquiv_injective : Injective (LocalDiffeomorph.toEquiv : LocalDiffeomorph I J M N n → M ≃ N) := sorry
-- | ⟨_, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _⟩, rfl => rfl

-- instance : EquivLike (LocalDiffeomorph I I' M M' M n) M M' where
--   coe Φ := Φ.toEquiv
--   inv Φ := Φ.toEquiv.symm
--   left_inv Φ := Φ.left_inv
--   right_inv Φ := Φ.right_inv
--   coe_injective' _ _ h _ := toEquiv_injective <| FunLike.ext' h

-- TODO: add coe instance, ext lemmas, etc.
-- def LocalDiffeomorph.toEquiv (h : LocalDiffeomorph I J M N n) := by
--   exact {
--     toEquiv := h.toEquiv
--   }

-- TODO: prove this; shouldn't be too hard
variable {I J M N n} in
protected theorem toHomeomorph (h : LocalDiffeomorph I J M N n) : Homeomorph M N := sorry

/-- Identity map as a local diffeomorphism. -/
protected def refl : LocalDiffeomorph I I M M n where
  toEquiv := Equiv.refl M
  -- At every point, we choose the set `univ`.
  sources := singleton ⟨univ, isOpen_univ⟩
  targets := singleton ⟨univ, isOpen_univ⟩
  mem_sources := fun x ↦ sorry -- should be: (by exact trivial)
  mem_targets := fun x ↦ sorry -- should be: (by exact trivial)
  sourceAt := by -- xxx: presumably, can golf this
    intro; apply Subtype.mk; apply Eq.refl
  targetAt := by
    intro; apply Subtype.mk; apply Eq.refl
  contMDiffOn_toFun := fun _ ↦ contMDiff_id.contMDiffOn
  contMDiffOn_invFun := fun _ ↦ contMDiff_id.contMDiffOn

@[simp]
theorem refl_toEquiv : (LocalDiffeomorph.refl I M n).toLocalEquiv = LocalEquiv.refl _ :=
  rfl

/- Inverse of a local diffeomorphism. -/
@[pp_dot]
protected def symm (h : LocalDiffeomorph I J M N n) :
    LocalDiffeomorph J I N M n where
  toEquiv := h.toEquiv.symm
  sources := h.targets
  targets := h.sources
  sourceAt := fun y ↦ (h.targetAt (h.invFun y))
  targetAt := fun y ↦ (h.sourceAt (h.invFun y))
  mem_sources := by
    intro y
    have : h.toFun (h.invFun y) = y := by apply h.right_inv
    let r := h.mem_targets (h.invFun y)
    rw [← this] at r
    sorry -- apply r
  mem_targets := sorry -- similar
  contMDiffOn_toFun := fun y ↦ h.contMDiffOn_invFun (h.invFun y)
  contMDiffOn_invFun := fun y ↦ h.contMDiffOn_toFun (h.invFun y)

/-- Composing two local diffeomorphisms, by restricting the source and target sets
to the maximal domain where their composition is well defined. -/
protected def trans (h : LocalDiffeomorph I I' M M' n)
    (h' : LocalDiffeomorph I' J M' N n) : LocalDiffeomorph I J M N n where
  toEquiv := h.toEquiv.trans h'.toEquiv
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

-- /-- A local diffeomorph is a diffeomorphism on some open set. -/
-- FIXME: do I want to add this definition? probably yes?!

/-- A diffeomorphism on an open set is a local diffeomorph at each point of its source. -/
lemma DiffeomorphOn.toLocalDiffeomorphAt (h : DiffeomorphOn I J M N n) {x : M} (hx : x ∈ h.source) :
    LocalDiffeomorphAt I J M N n x :=
  { toDiffeomorphOn := h, hx := hx }

/-- A local diffeomorphism is a local diffeomorphism at each point. -/
lemma LocalDiffeomorph.toLocalDiffeomorphAt (h : LocalDiffeomorph I J M N n) {x : M}: LocalDiffeomorphAt I J M N n x := by
  exact {
    toLocalHomeomorph := (h.toHomeomorph).toLocalHomeomorph
    hx := trivial
    contMDiffOn_toFun := by
      have : ∀ x : M, ContMDiffAt I J n h.toFun x := by
        intro x
        apply (h.contMDiffOn_toFun x).contMDiffAt
        apply (((h.sourceAt x).1.2).mem_nhds_iff).mpr (h.mem_sources x)
      set badboy := h.toHomeomorph.toLocalHomeomorph.toLocalEquiv
      have aux : badboy = h.toFun := sorry -- TODO: add as a lemma later!
      rw [aux, Homeomorph.toLocalHomeomorph_source, contMDiffOn_univ] -- TODO: why last two lemmas?
      exact this
    contMDiffOn_invFun := by
      have : ∀ x : M, ContMDiffAt J I n h.invFun (h.toFun x) := by
        intro x
        apply (h.contMDiffOn_invFun x).contMDiffAt
        apply (((h.targetAt x).1.2).mem_nhds_iff).mpr (h.mem_targets x)
      have : ∀ y : N, ContMDiffAt J I n h.invFun y := by -- this should be almost obvious!
        intro y
        let x := h.invFun y
        -- TODO: extract as a lemma for later!
        have aux2 : h.toFun (h.invFun y) = y := h.toLocalEquiv.right_inv' (mem_univ y)
        exact aux2 ▸ (this x)
      set badboy := (h.toHomeomorph.toLocalHomeomorph).toLocalEquiv.invFun
      have aux : badboy = h.invFun := sorry -- TODO: add as a lemma later!
      rw [aux]
      apply ContMDiff.contMDiffOn this
  }

variable {I J M N r} in
lemma should_be_obvious (h : DiffeomorphOn I J M N r) {x : M} (hx : x ∈ h.source) :
    h.source = (h.toLocalDiffeomorphAt hx).toLocalHomeomorph.source := by
  set r := h.toLocalDiffeomorphAt hx
  have : r.toLocalHomeomorph = h.toLocalHomeomorph := sorry -- TODO: make this true!!
  rw [this]

-- xxx: what would this mean in Lean?
-- if f : M → N f is a local diffeomorphism at each point, it's a local diffeomorphism.

-- FIXME: should be able to write h.symm, h instead of h.invFun and h.toFun!
section Differentials
variable [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners J N]

-- similar to `fderivWithin_of_open`; seems missing
lemma hasFDerivWithinAt_of_open {s : Set E} {x : E} (h : IsOpen s) (hx : x ∈ s) {f : E → F}
    {f' : E →L[𝕜] F} : HasFDerivWithinAt f f' s x ↔ HasFDerivAt f f' x := by
  simp only [HasFDerivAt, HasFDerivWithinAt]
  rw [IsOpen.nhdsWithin_eq h hx]

-- I have not compared FDeriv.Basic to MFDeriv and added all analogous lemmas.
-- analogous to `fderivWithin_of_mem_nhds`
variable {M N} in
theorem mfderivWithin_of_mem_nhds {f : M → N} {s : Set M} {x : M} (h : s ∈ 𝓝 x) :
    mfderivWithin I J f s x = mfderiv I J f x := by
  rw [← mfderivWithin_univ, ← univ_inter s, mfderivWithin_inter h]

-- similar to `fderivWith_of_open`
variable {M N} in
lemma mfderivWithin_of_open {s : Set M} {x : M} (hs : IsOpen s) (hx : x ∈ s) {f : M → N} :
    mfderivWithin I J f s x = mfderiv I J f x := by
  apply mfderivWithin_of_mem_nhds I J (hs.mem_nhds hx)

-- analogous to `mfderivWithin_eq_mfderiv`
theorem mfderivWithin_eq_mfderiv {s : Set M} {x : M} {f : M → N}
    (hs : UniqueMDiffWithinAt I s x) (h : MDifferentiableAt I J f x) :
    mfderivWithin I J f s x = mfderiv I J f x := by
  rw [← mfderivWithin_univ]
  exact mfderivWithin_subset (subset_univ _) hs h.mdifferentiableWithinAt

variable {I J M M' N n}

/-- If `f` is a local diffeomorphism at `x`,
  the differential of `f` at `x` is a linear isomorphism. -/
noncomputable def LocalDiffeomorphAt.differential_toContinuousLinearEquiv {r : ℕ} (hr : 1 ≤ r)
    {x : M} (h : LocalDiffeomorphAt I J M N r x) :
    ContinuousLinearEquiv (RingHom.id 𝕜) (TangentSpace I x) (TangentSpace J (h.toFun x)) := by
  let y := h.toFun x
  have hy : y ∈ h.target := h.toLocalEquiv.mapsTo h.hx
  let A := mfderiv I J h.toFun x
  let B := mfderiv J I h.invFun (h.toFun x)

  have hr : 1 ≤ (r : ℕ∞) := Nat.one_le_cast.mpr (Nat.one_le_of_lt hr)
  -- FUTURE: can the `differentiability` tactic show this?
  have hgat : MDifferentiableAt J I h.invFun y :=
    (h.contMDiffAt_symm (h.toLocalEquiv.mapsTo h.hx)).mdifferentiableAt hr
  have hfat : MDifferentiableAt I J h.toFun x :=
    (h.contMDiffAt h.hx).mdifferentiableAt hr
  have inv1 : B.comp A = ContinuousLinearMap.id 𝕜 (TangentSpace I x) := calc B.comp A
    _ = mfderiv I I (h.invFun ∘ h.toFun) x := (mfderiv_comp x hgat hfat).symm
    _ = mfderivWithin I I (h.invFun ∘ h.toFun) h.source x :=
      (mfderivWithin_of_open I I h.open_source h.hx).symm
    _ = mfderivWithin I I id h.source x :=
      mfderivWithin_congr (h.open_source.uniqueMDiffWithinAt h.hx) h.left_inv' (h.left_inv' h.hx)
    _ = mfderiv I I id x := mfderivWithin_of_open I I h.open_source h.hx
    _ = ContinuousLinearMap.id 𝕜 (TangentSpace I x) := mfderiv_id I
  have inv2 : A.comp B = ContinuousLinearMap.id 𝕜 (TangentSpace J (h.toFun x)) := calc A.comp B
    _ = mfderiv J J (h.toFun ∘ h.invFun) y := by
          -- Use the chain rule: rewrite the base point (I ∘ e ∘ e.invFun ∘ I.invFun) x = x, ...
          let sdf := h.left_inv' h.hx
          sorry -- fails, don't care for now -- rw [← sdf] at hfat
          -- ... but also the points x and y under the map.
          -- for some reason, cannot plug this in directly
          -- have : (LocalEquiv.invFun h.toLocalEquiv y) = x := (h.left_inv' hx)
          -- exact (this ▸ (mfderiv_comp y hfat hgat)).symm
    _ = mfderivWithin J J (h.toFun ∘ h.invFun) h.target y :=
      (mfderivWithin_of_open J J h.open_target hy).symm
    _ = mfderivWithin J J id h.target y :=
      mfderivWithin_congr (h.open_target.uniqueMDiffWithinAt hy) h.right_inv' (h.right_inv' hy)
    _ = mfderiv J J id y := mfderivWithin_of_open J J h.open_target hy
    _ = ContinuousLinearMap.id 𝕜 (TangentSpace J y) := mfderiv_id J

  have h1 : Function.LeftInverse B A := sorry -- TODO: should be obvious from inv1
  have h2 : Function.RightInverse B A := sorry -- same here
  exact {
    toFun := A
    invFun := B
    left_inv := h1
    right_inv := h2
    continuous_toFun := A.cont
    continuous_invFun := B.cont
    map_add' := fun x_1 y ↦ ContinuousLinearMap.map_add A x_1 y
    map_smul' := by intros; simp
  }

/-- If `f` is a diffeomorphism on `s`, its differential is a linear isomorphism at each `x ∈ s`. -/
-- not sure if this result should be generally available; in any case, it's a simple corollary
noncomputable def DiffeomorphOn.differential_toContinuousLinearEquiv {r : ℕ} (hr : 1 ≤ r) {x : M}
    (h : DiffeomorphOn I J M N r) (hx : x ∈ h.source) :
    ContinuousLinearEquiv (RingHom.id 𝕜) (TangentSpace I x) (TangentSpace J (h.toFun x)) :=
  (h.toLocalDiffeomorphAt hx).differential_toContinuousLinearEquiv hr

/-- If `f` is a local diffeomorphism, the differential is a linear isomorphism at each point. -/
noncomputable def LocalDiffeomorph.differential_toContinuousLinearEquiv {r : ℕ} (hr : 1 ≤ r) {x : M}
    (h : LocalDiffeomorph I J M N r):
    ContinuousLinearEquiv (RingHom.id 𝕜) (TangentSpace I x) (TangentSpace J (h.toFun x)) :=
  (h.toLocalDiffeomorphAt).differential_toContinuousLinearEquiv hr

-- TODO: move this to Init.Function
lemma bijective_iff_inverses {X Y : Type*} {f : X → Y} {g : Y → X}
    (h1 : LeftInverse g f) (h2 : LeftInverse f g) : Bijective f :=
  ⟨h1.injective, h2.surjective⟩

/-- A local diffeomorphism at `x` has bijective differential at `x`. -/
lemma LocalDiffeomorphAt.differential_bijective {r : ℕ} (hr : 1 ≤ r) {x : M}
    (h : LocalDiffeomorphAt I J M N r x) : Bijective (mfderiv I J h.toFun x) := by
  let aux := h.differential_toContinuousLinearEquiv hr
  have h : aux.toFun = mfderiv I J h.toFun x := sorry -- TODO: should be obvious!
  rw [← h]
  exact bijective_iff_inverses aux.left_inv aux.right_inv

/-- A local diffeomorphism has bijective differential at each point in its source. -/
lemma DiffeomorphOn.differential_bijective {r : ℕ} (hr : 1 ≤ r) {x : M}
    (h : DiffeomorphOn I J M N r) (hx : x ∈ h.source) : Bijective (mfderiv I J h.toFun x) := by
  let _s := (h.toLocalDiffeomorphAt hx).differential_bijective
  -- TODO: why does this not match? tweak my setup to make sure it does!
  sorry --exact _s hr

/-- A diffeomorphism is a local diffeomorphism. -/
-- TODO: deduplicate this with with LocalDiffeomorph.refl
def Diffeomorph.toLocalDiffeomorph (h : Diffeomorph I J M N n) : LocalDiffeomorph I J M N n := by
  exact {
    toEquiv := h.toEquiv
    sources := singleton ⟨univ, isOpen_univ⟩
    targets := singleton ⟨univ, isOpen_univ⟩
    sourceAt := by intro; apply Subtype.mk; apply Eq.refl
    targetAt := by intro; apply Subtype.mk; apply Eq.refl
    mem_sources := fun _ ↦ (by exact trivial)
    mem_targets := fun _ ↦ (by exact trivial)
    contMDiffOn_toFun := by
      intro
      simp only [Equiv.toFun_as_coe, coe_toEquiv, Opens.mk_univ, Opens.coe_top]
      rw [contMDiffOn_univ]
      exact h.contMDiff_toFun
    contMDiffOn_invFun := by
      intro
      simp only [Equiv.toFun_as_coe, coe_toEquiv, Opens.mk_univ, Opens.coe_top]
      rw [contMDiffOn_univ]
      exact h.contMDiff_invFun
  }

/-- A diffeomorphism is a local diffeomorphism at each point. -/
noncomputable def Diffeomorph.toLocalDiffeomorphAt (h : Diffeomorph I J M N n) (x : M) :
    LocalDiffeomorphAt I J M N n x :=
  (h.toLocalDiffeomorph).toLocalDiffeomorphAt

/-- A diffeomorphism has bijective differential at each point. -/
lemma Diffeomorph.differential_bijective {r : ℕ} (hr : 1 ≤ r) (f : Diffeomorph I J M N r) {x : M} :
    Bijective (mfderiv I J f.toFun x) := by
  let aux := (f.toLocalDiffeomorphAt x).differential_bijective hr
  -- TODO: why is this rewrite necessary?
  have : (f.toLocalDiffeomorphAt x).toDiffeomorphOn.toLocalHomeomorph.toLocalEquiv = f.toFun := sorry
  rw [← this]
  exact aux

/-- If `f : M → N` is smooth at `x` and `mfderiv I J f x` is a linear isomorphism,
  then `f` is a local diffeomorphism at `x`. -/
lemma LocalDiffeomorphAt.of_DifferentialIsomorphismAt {r : ℕ} (hr : 1 ≤ r) {x : M} {f : M → N}
    {f' : TangentSpace I x →L[𝕜] TangentSpace J (f x)} (hf' : HasMFDerivAt I J f x f')
    {g' : TangentSpace J (f x) →L[𝕜] TangentSpace I x}
    (hinv₁ : f' ∘ g' = id) (hinv₂ : g' ∘ f' = id)
    (hf : ContMDiffAt I J r f x) : LocalDiffeomorphAt I J M N r x := by
  -- FIXME: can I prove this using rw instead of calc?
  have aux1 : LeftInverse g' f' := by
    intro x
    calc g' (f' x)
      _ = (g' ∘ f') x := by rw [comp_apply] -- or rfl
      _ = id x := by rw [← hinv₂]
      _ = x := by rw [id_eq] -- or rfl
  have aux2 : RightInverse g' f' := by
    intro y
    calc f' (g' y)
      _ = (f' ∘ g') y := by rw [comp_apply]
      _ = id y := by rw [← hinv₁]
      _ = y := by rw [id_eq]
  have hr : 1 ≤ (r : ℕ∞) := Nat.one_le_cast.mpr (Nat.one_le_of_lt hr)
  have : f' = mfderiv I J f x := hasMFDerivAt_unique hf' (hf.mdifferentiableAt hr).hasMFDerivAt
  rw [this] at *
  have : ContinuousLinearEquiv (RingHom.id 𝕜) (TangentSpace I x) (TangentSpace J (f x)) :=
    {
      toFun := f'
      invFun := g'
      continuous_toFun := f'.cont
      continuous_invFun := g'.cont
      map_add' := fun x_1 y ↦ ContinuousLinearMap.map_add f' x_1 y
      map_smul' := by intros; simp
      left_inv := aux1
      right_inv := aux2
    }
  -- Now, the argument would apply the inverse function theorem, which mathlib only has for
  -- normed space. Let's wait for that to happen first.
  sorry
end Differentials



-- if f is smooth and each differential df_x is a linear iso, f is a local diffeo

-- a bijective local diffeo is a diffeo: hard to formalise?!
-- a diffeo is a local diffeo
-- a diffeo is bijective (easy)
-- corollary: a diffeo is a bijective local diffeo (exact with two things)

-- can I say that **the tangent map is a bundle isomorphism?**
