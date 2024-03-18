/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.IsLocalHomeomorph

/-!
# Local diffeomorphisms between manifolds

In this file, we define `C^n` local diffeomorphisms between manifolds.

A `C^n` map `f : M → N` is a **local diffeomorphism at `x`** iff there are neighbourhoods `s`
and `t` of `x` and `f x`, respectively such that `f` restricts to a diffeomorphism
between `s` and `t`. `f` is called a **local diffeomorphism on s** iff it is a local diffeomorphism
at every `x ∈ s`, and a **local diffeomorphism** iff it is a local diffeomorphism on `univ`.

## Main definitions
* `IsLocalDiffeomorphAt I J n f x`: `f` is a `C^n` local diffeomorphism at `x`
* `IsLocalDiffeomorphOn I J n f s`: `f` is a `C^n` local diffeomorphism on `s`
* `IsLocalDiffeomorph I J n f`: `f` is a `C^n` local diffeomorphism

## Main results
* Each of `Diffeomorph`, `IsLocalDiffeomorph`, `IsLocalDiffeomorphOn` and `IsLocalDiffeomorphAt`
  implies the next.
* `IsLocalDiffeomorph.isLocalHomeomorph`: a local diffeomorphisms is a local homeomorphism,
  similarly for local diffeomorphism on `s`
* `IsLocalDiffeomorph.isOpen_range`: the image of a local diffeomorphism is open
* `IslocalDiffeomorph.diffeomorph_of_bijective`:
  a bijective local diffeomorphism is a diffeomorphism

## TODO
* an injective local diffeomorphism is a diffeomorphism to its image
* each differential of a `C^n` diffeomorphism (`n ≥ 1`) is a linear equivalence.
* if `f` is a local diffeomorphism at `x`, the differential `mfderiv I J n f x`
is a continuous linear isomorphism.
* conversely, if `f` is `C^n` at `x` and `mfderiv I J n f x` is a linear isomorphism,
`f` is a local diffeomorphism at `x`.
* if `f` is a local diffeomorphism, each differential `mfderiv I J n f x`
is a continuous linear isomorphism.
* Conversely, if `f` is `C^n` and each differential is a linear isomorphism,
`f` is a local diffeomorphism.

## Implementation notes

This notion of diffeomorphism is needed although there is already a notion of local structomorphism
because structomorphisms do not allow the model spaces `H` and `H'` of the two manifolds to be
different, i.e. for a structomorphism one has to impose `H = H'` which is often not the case in
practice.

## Tags
local diffeomorphism, manifold

-/

open Manifold Set TopologicalSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H]
  {G : Type*} [TopologicalSpace G]
  (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F G)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  (N : Type*) [TopologicalSpace N] [ChartedSpace G N] (n : ℕ∞)

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
Note that a `PartialDiffeomorph` is not `DFunLike` (like `PartialHomeomorph`),
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
variable (Φ : PartialDiffeomorph I J M N n) (hn : 1 ≤ n)

/-- A partial diffeomorphism is also a local homeomorphism. -/
def toPartialHomeomorph : PartialHomeomorph M N where
  toPartialEquiv := Φ.toPartialEquiv
  open_source := Φ.open_source
  open_target := Φ.open_target
  continuousOn_toFun := Φ.contMDiffOn_toFun.continuousOn
  continuousOn_invFun := Φ.contMDiffOn_invFun.continuousOn

/-- The inverse of a local diffeomorphism. -/
protected def symm : PartialDiffeomorph J I N M n where
  toPartialEquiv := Φ.toPartialEquiv.symm
  open_source := Φ.open_target
  open_target := Φ.open_source
  contMDiffOn_toFun := Φ.contMDiffOn_invFun
  contMDiffOn_invFun := Φ.contMDiffOn_toFun

protected theorem contMDiffOn : ContMDiffOn I J n Φ Φ.source :=
  Φ.contMDiffOn_toFun

protected theorem mdifferentiableOn : MDifferentiableOn I J Φ Φ.source :=
  (Φ.contMDiffOn).mdifferentiableOn hn

protected theorem mdifferentiableAt {x : M} (hx : x ∈ Φ.source) : MDifferentiableAt I J Φ x :=
  (Φ.mdifferentiableOn hn x hx).mdifferentiableAt (Φ.open_source.mem_nhds hx)

/- We could add lots of additional API (following `Diffeomorph` and `PartialHomeomorph`), such as
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

/-! # Basic properties of local diffeomorphisms -/
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
lemma IsLocalDiffeomorphAt.mdifferentiableAt (hf : IsLocalDiffeomorphAt I J n f x) (hn : 1 ≤ n) :
    MDifferentiableAt I J f x :=
  hf.contMDiffAt.mdifferentiableAt hn

/-- A `C^n` local diffeomorphism on `s` is `C^n` on `s`. -/
lemma IsLocalDiffeomorphOn.contMDiffOn (hf : IsLocalDiffeomorphOn I J n f s) :
    ContMDiffOn I J n f s :=
  fun x hx ↦ (hf ⟨x, hx⟩).contMDiffAt.contMDiffWithinAt

/-- A local diffeomorphism on `s` is differentiable on `s`. -/
lemma IsLocalDiffeomorphOn.mdifferentiableOn (hf : IsLocalDiffeomorphOn I J n f s) (hn : 1 ≤ n) :
    MDifferentiableOn I J f s :=
  hf.contMDiffOn.mdifferentiableOn hn

/-- A `C^n` local diffeomorphism is `C^n`. -/
lemma IsLocalDiffeomorph.contMDiff (hf : IsLocalDiffeomorph I J n f) : ContMDiff I J n f :=
  fun x ↦ (hf x).contMDiffAt

/-- A `C^n` local diffeomorphism is differentiable. -/
lemma IsLocalDiffeomorph.mdifferentiable (hf : IsLocalDiffeomorph I J n f) (hn : 1 ≤ n) :
    MDifferentiable I J f :=
  fun x ↦ (hf x).mdifferentiableAt hn

/-- A `C^n` diffeomorphism is a local diffeomorphism. -/
lemma Diffeomorph.isLocalDiffeomorph (Φ : M ≃ₘ^n⟮I, J⟯ N) : IsLocalDiffeomorph I J n Φ :=
  fun _x ↦ ⟨Φ.toPartialDiffeomorph, by trivial, eqOn_refl Φ _⟩

-- FUTURE: if useful, also add "a `PartialDiffeomorph` is a local diffeomorphism on its source"

/-- A local diffeomorphism on `s` is a local homeomorphism on `s`. -/
theorem IsLocalDiffeomorphOn.isLocalHomeomorphOn {s : Set M} (hf : IsLocalDiffeomorphOn I J n f s):
    IsLocalHomeomorphOn f s := by
  apply IsLocalHomeomorphOn.mk
  intro x hx
  choose U hyp using hf ⟨x, hx⟩
  exact ⟨U.toPartialHomeomorph, hyp⟩

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
noncomputable def IslocalDiffeomorph.diffeomorph_of_bijective
    (hf : IsLocalDiffeomorph I J n f) (hf' : Function.Bijective f) : Diffeomorph I J M N n := by
  -- Choose a right inverse `g` of `f`.
  choose g hgInverse using (Function.bijective_iff_has_inverse).mp hf'
   -- Choose diffeomorphisms φ_x which coincide which `f` near `x`.
  choose Φ hyp using (fun x ↦ hf x)
  -- Two such diffeomorphisms (and their inverses!) coincide on their sources:
  -- they're both inverses to g. In fact, the latter suffices for our proof.
  -- have (x y) : EqOn (Φ x).symm (Φ y).symm ((Φ x).target ∩ (Φ y).target) := sorry
  have aux (x) : EqOn g (Φ x).symm (Φ x).target :=
    eqOn_of_leftInvOn_of_rightInvOn (fun x' _ ↦ hgInverse.1 x')
      (LeftInvOn.congr_left ((Φ x).toPartialHomeomorph).rightInvOn
        ((Φ x).toPartialHomeomorph).symm_mapsTo (hyp x).2.symm)
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

end Basic
