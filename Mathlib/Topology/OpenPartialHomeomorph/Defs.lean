/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Logic.Equiv.PartialEquiv
public import Mathlib.Topology.ContinuousOn

/-!
# Partial homeomorphisms: definitions

This file defines homeomorphisms between open subsets of topological spaces. An element `e` of
`OpenPartialHomeomorph X Y` is an extension of `PartialEquiv X Y`, i.e., it is a pair of functions
`e.toFun` and `e.invFun`, inverse of each other on the sets `e.source` and `e.target`.
Additionally, we require that these sets are open, and that the functions are continuous on them.
Equivalently, they are homeomorphisms there.

As in equivs, we register a coercion to functions, and we use `e x` and `e.symm x` throughout
instead of `e.toFun x` and `e.invFun x`.

## Main definitions

This file is intentionally kept small; many other constructions of, and lemmas about,
partial homeomorphisms can be found in other files under `Mathlib/Topology/PartialHomeomorph/`.

* `Homeomorph.toOpenPartialHomeomorph`: associating an open partial homeomorphism to a
  homeomorphism, with `source = target = Set.univ`;
* `OpenPartialHomeomorph.symm`: the inverse of an open partial homeomorphism

## Implementation notes

Most statements are copied from their `PartialEquiv` versions, although some care is required
especially when restricting to subsets, as these should be open subsets.

For design notes, see `PartialEquiv.lean`.

### Local coding conventions

If a lemma deals with the intersection of a set with either source or target of a `PartialEquiv`,
then it should use `e.source ∩ s` or `e.target ∩ t`, not `s ∩ e.source` or `t ∩ e.target`.
-/

@[expose] public section

open Function Set Filter Topology

variable {X X' : Type*} {Y Y' : Type*} {Z Z' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Z] [TopologicalSpace Z']

/-- Partial homeomorphisms, defined on open subsets of the space -/
structure OpenPartialHomeomorph (X : Type*) (Y : Type*) [TopologicalSpace X]
  [TopologicalSpace Y] extends PartialEquiv X Y where
  open_source : IsOpen source
  open_target : IsOpen target
  continuousOn_toFun : ContinuousOn toFun source
  continuousOn_invFun : ContinuousOn invFun target

@[deprecated (since := "2025-08-29")] alias PartialHomeomorph := OpenPartialHomeomorph

namespace OpenPartialHomeomorph

variable (e : OpenPartialHomeomorph X Y)

/-! Basic properties; inverse (symm instance) -/
section Basic
/-- Coercion of an open partial homeomorphisms to a function. We don't use `e.toFun` because it is
actually `e.toPartialEquiv.toFun`, so `simp` will apply lemmas about `toPartialEquiv`.
While we may want to switch to this behavior later, doing it mid-port will break a lot of proofs. -/
@[coe] def toFun' : X → Y := e.toFun

/-- Coercion of an `OpenPartialHomeomorph` to function.
Note that an `OpenPartialHomeomorph` is not `DFunLike`. -/
instance : CoeFun (OpenPartialHomeomorph X Y) fun _ => X → Y :=
  ⟨fun e => e.toFun'⟩

/-- The inverse of an open partial homeomorphism -/
@[symm]
protected def symm : OpenPartialHomeomorph Y X where
  toPartialEquiv := e.toPartialEquiv.symm
  open_source := e.open_target
  open_target := e.open_source
  continuousOn_toFun := e.continuousOn_invFun
  continuousOn_invFun := e.continuousOn_toFun

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (e : OpenPartialHomeomorph X Y) : X → Y := e

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : OpenPartialHomeomorph X Y) : Y → X := e.symm

initialize_simps_projections OpenPartialHomeomorph (toFun → apply, invFun → symm_apply)

protected theorem continuousOn : ContinuousOn e e.source :=
  e.continuousOn_toFun

theorem continuousOn_symm : ContinuousOn e.symm e.target :=
  e.continuousOn_invFun

@[simp, mfld_simps]
theorem mk_coe (e : PartialEquiv X Y) (a b c d) :
    (OpenPartialHomeomorph.mk e a b c d : X → Y) = e :=
  rfl

@[simp, mfld_simps]
theorem mk_coe_symm (e : PartialEquiv X Y) (a b c d) :
    ((OpenPartialHomeomorph.mk e a b c d).symm : Y → X) = e.symm :=
  rfl

theorem toPartialEquiv_injective :
    Injective (toPartialEquiv : OpenPartialHomeomorph X Y → PartialEquiv X Y)
  | ⟨_, _, _, _, _⟩, ⟨_, _, _, _, _⟩, rfl => rfl

/- Register a few simp lemmas to make sure that `simp` puts the application of a local
homeomorphism in its normal form, i.e., in terms of its coercion to a function. -/
@[simp, mfld_simps]
theorem toFun_eq_coe (e : OpenPartialHomeomorph X Y) : e.toFun = e :=
  rfl

@[simp, mfld_simps]
theorem invFun_eq_coe (e : OpenPartialHomeomorph X Y) : e.invFun = e.symm :=
  rfl

@[simp, mfld_simps]
theorem coe_coe : (e.toPartialEquiv : X → Y) = e :=
  rfl

@[simp, mfld_simps]
theorem coe_coe_symm : (e.toPartialEquiv.symm : Y → X) = e.symm :=
  rfl

@[simp, mfld_simps]
theorem map_source {x : X} (h : x ∈ e.source) : e x ∈ e.target :=
  e.map_source' h

/-- Variant of `map_source`, stated for images of subsets of `source`. -/
lemma map_source'' : e '' e.source ⊆ e.target :=
  fun _ ⟨_, hx, hex⟩ ↦ mem_of_eq_of_mem (id hex.symm) (e.map_source' hx)

@[simp, mfld_simps]
theorem map_target {x : Y} (h : x ∈ e.target) : e.symm x ∈ e.source :=
  e.map_target' h

@[simp, mfld_simps]
theorem left_inv {x : X} (h : x ∈ e.source) : e.symm (e x) = x :=
  e.left_inv' h

@[simp, mfld_simps]
theorem right_inv {x : Y} (h : x ∈ e.target) : e (e.symm x) = x :=
  e.right_inv' h

theorem eq_symm_apply {x : X} {y : Y} (hx : x ∈ e.source) (hy : y ∈ e.target) :
    x = e.symm y ↔ e x = y :=
  e.toPartialEquiv.eq_symm_apply hx hy

protected theorem mapsTo : MapsTo e e.source e.target := fun _ => e.map_source

protected theorem symm_mapsTo : MapsTo e.symm e.target e.source :=
  e.symm.mapsTo

protected theorem leftInvOn : LeftInvOn e.symm e e.source := fun _ => e.left_inv

protected theorem rightInvOn : RightInvOn e.symm e e.target := fun _ => e.right_inv

protected theorem invOn : InvOn e.symm e e.source e.target :=
  ⟨e.leftInvOn, e.rightInvOn⟩

protected theorem injOn : InjOn e e.source :=
  e.leftInvOn.injOn

protected theorem bijOn : BijOn e e.source e.target :=
  e.invOn.bijOn e.mapsTo e.symm_mapsTo

protected theorem surjOn : SurjOn e e.source e.target :=
  e.bijOn.surjOn

end Basic

/-- Interpret a `Homeomorph` as an `OpenPartialHomeomorph` by restricting it
to an open set `s` in the domain and to `t` in the codomain. -/
@[simps! -fullyApplied apply symm_apply toPartialEquiv,
  simps! -isSimp source target]
def _root_.Homeomorph.toOpenPartialHomeomorphOfImageEq (e : X ≃ₜ Y) (s : Set X) (hs : IsOpen s)
    (t : Set Y) (h : e '' s = t) : OpenPartialHomeomorph X Y where
  toPartialEquiv := e.toPartialEquivOfImageEq s t h
  open_source := hs
  open_target := by simpa [← h]
  continuousOn_toFun := e.continuous.continuousOn
  continuousOn_invFun := e.symm.continuous.continuousOn

@[deprecated (since := "2025-08-29")] alias
_root_.Homeomorph.toPartialHomeomorphOfImageEq := _root_.Homeomorph.toOpenPartialHomeomorphOfImageEq

/-- A homeomorphism induces an open partial homeomorphism on the whole space -/
@[simps! (attr := mfld_simps) -fullyApplied]
def _root_.Homeomorph.toOpenPartialHomeomorph (e : X ≃ₜ Y) : OpenPartialHomeomorph X Y :=
  e.toOpenPartialHomeomorphOfImageEq univ isOpen_univ univ <|
    by rw [image_univ, e.surjective.range_eq]

@[deprecated (since := "2025-08-29")] alias
_root_.Homeomorph.toPartialHomeomorph := _root_.Homeomorph.toOpenPartialHomeomorph

/-- Replace `toPartialEquiv` field to provide better definitional equalities. -/
def replaceEquiv (e : OpenPartialHomeomorph X Y) (e' : PartialEquiv X Y)
    (h : e.toPartialEquiv = e') : OpenPartialHomeomorph X Y where
  toPartialEquiv := e'
  open_source := h ▸ e.open_source
  open_target := h ▸ e.open_target
  continuousOn_toFun := h ▸ e.continuousOn_toFun
  continuousOn_invFun := h ▸ e.continuousOn_invFun

theorem replaceEquiv_eq_self (e' : PartialEquiv X Y)
    (h : e.toPartialEquiv = e') : e.replaceEquiv e' h = e := by
  cases e
  subst e'
  rfl

/-- Two open partial homeomorphisms are equal when they have equal `toFun`, `invFun` and `source`.
It is not sufficient to have equal `toFun` and `source`, as this only determines `invFun` on
the target. This would only be true for a weaker notion of equality, arguably the right one,
called `EqOnSource`. -/
@[ext]
protected theorem ext (e' : OpenPartialHomeomorph X Y) (h : ∀ x, e x = e' x)
    (hinv : ∀ x, e.symm x = e'.symm x) (hs : e.source = e'.source) : e = e' :=
  toPartialEquiv_injective (PartialEquiv.ext h hinv hs)

@[simp, mfld_simps]
theorem symm_toPartialEquiv : e.symm.toPartialEquiv = e.toPartialEquiv.symm :=
  rfl

-- The following lemmas are already simp via `PartialEquiv`
theorem symm_source : e.symm.source = e.target :=
  rfl

theorem symm_target : e.symm.target = e.source :=
  rfl

@[simp, mfld_simps] theorem symm_symm : e.symm.symm = e := rfl

theorem symm_bijective : Function.Bijective
    (OpenPartialHomeomorph.symm : OpenPartialHomeomorph X Y → OpenPartialHomeomorph Y X) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

end OpenPartialHomeomorph
