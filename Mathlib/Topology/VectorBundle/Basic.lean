/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sébastien Gouëzel, Heather Macbeth, Patrick Massot, Floris van Doorn
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Topology.FiberBundle.Basic

/-!
# Vector bundles

In this file we define (topological) vector bundles.

Let `B` be the base space, let `F` be a normed space over a normed field `R`, and let
`E : B → Type*` be a `FiberBundle` with fiber `F`, in which, for each `x`, the fiber `E x` is a
topological vector space over `R`.

To have a vector bundle structure on `Bundle.TotalSpace F E`, one should additionally have the
following properties:

* The bundle trivializations in the trivialization atlas should be continuous linear equivs in the
  fibers;
* For any two trivializations `e`, `e'` in the atlas the transition function considered as a map
  from `B` into `F →L[R] F` is continuous on `e.baseSet ∩ e'.baseSet` with respect to the operator
  norm topology on `F →L[R] F`.

If these conditions are satisfied, we register the typeclass `VectorBundle R F E`.

We define constructions on vector bundles like pullbacks and direct sums in other files.

## Main Definitions

* `Bundle.Trivialization.IsLinear`: a class stating that a trivialization is fiberwise linear
  on its base set.
* `Bundle.Trivialization.linearEquivAt` and `Bundle.Trivialization.continuousLinearMapAt` are the
  (continuous) linear fiberwise equivalences a trivialization induces.
* They have forward maps `Bundle.Trivialization.linearMapAt` /
  `Bundle.Trivialization.continuousLinearMapAt` and inverses `Bundle.Trivialization.symmₗ` /
  `Bundle.Trivialization.symmL`. Note that these are all defined
  everywhere, since they are extended using the zero function.
* `Bundle.Trivialization.coordChangeL` is the coordinate change induced by two trivializations.
  It only makes sense on the intersection of their base sets,
  but is extended outside it using the identity.
* Given a continuous (semi)linear map between `E x` and `E' y` where `E` and `E'` are bundles over
  possibly different base sets, `ContinuousLinearMap.inCoordinates` turns this into a continuous
  (semi)linear map between the chosen fibers of those bundles.

## Implementation notes

The implementation choices in the vector bundle definition are discussed in the "Implementation
notes" section of `Mathlib/Topology/FiberBundle/Basic.lean`.

## Tags
Vector bundle
-/

@[expose] public section

noncomputable section

open Bundle Set Topology

variable (R : Type*) {B : Type*} (F : Type*) (E : B → Type*)

section TopologicalVectorSpace

variable {F E}
variable [Semiring R] [TopologicalSpace F] [TopologicalSpace B]

/-- A mixin class for `Pretrivialization`, stating that a pretrivialization is fiberwise linear with
respect to given module structures on its fibers and the model fiber. -/
protected class Bundle.Pretrivialization.IsLinear [AddCommMonoid F] [Module R F]
  [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)] (e : Pretrivialization F (π F E)) : Prop where
  linear : ∀ b ∈ e.baseSet, IsLinearMap R fun x : E b => (e ⟨b, x⟩).2

namespace Bundle.Pretrivialization

variable (e : Pretrivialization F (π F E)) {x : TotalSpace F E} {b : B} {y : E b}

theorem linear [AddCommMonoid F] [Module R F] [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)]
    [e.IsLinear R] {b : B} (hb : b ∈ e.baseSet) :
    IsLinearMap R fun x : E b => (e ⟨b, x⟩).2 :=
  IsLinear.linear b hb

variable [AddCommMonoid F] [Module R F] [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)]

/-- A fiberwise linear inverse to `e`. -/
@[simps!]
protected def symmₗ (e : Pretrivialization F (π F E)) [e.IsLinear R] (b : B) : F →ₗ[R] E b := by
  refine IsLinearMap.mk' (e.symm b) ?_
  by_cases hb : b ∈ e.baseSet
  · exact (((e.linear R hb).mk' _).inverse (e.symm b) (e.symm_apply_apply_mk hb) fun v ↦
      congr_arg Prod.snd <| e.apply_mk_symm hb v).isLinear
  · rw [e.coe_symm_of_notMem hb]
    exact (0 : F →ₗ[R] E b).isLinear

/-- A pretrivialization for a vector bundle defines linear equivalences between the
fibers and the model space. -/
@[simps -fullyApplied]
def linearEquivAt (e : Pretrivialization F (π F E)) [e.IsLinear R] (b : B) (hb : b ∈ e.baseSet) :
    E b ≃ₗ[R] F where
  toFun y := (e ⟨b, y⟩).2
  invFun := e.symm b
  left_inv := e.symm_apply_apply_mk hb
  right_inv v := by simp_rw [e.apply_mk_symm hb v]
  map_add' v w := (e.linear R hb).map_add v w
  map_smul' c v := (e.linear R hb).map_smul c v

open Classical in
/-- A fiberwise linear map equal to `e` on `e.baseSet`. -/
protected def linearMapAt (e : Pretrivialization F (π F E)) [e.IsLinear R] (b : B) : E b →ₗ[R] F :=
  if hb : b ∈ e.baseSet then e.linearEquivAt R b hb else 0

variable {R}

open Classical in
theorem coe_linearMapAt (e : Pretrivialization F (π F E)) [e.IsLinear R] (b : B) :
    ⇑(e.linearMapAt R b) = fun y => if b ∈ e.baseSet then (e ⟨b, y⟩).2 else 0 := by
  rw [Pretrivialization.linearMapAt]
  split_ifs <;> rfl

theorem coe_linearMapAt_of_mem (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet) : ⇑(e.linearMapAt R b) = fun y => (e ⟨b, y⟩).2 := by
  simp_rw [coe_linearMapAt, if_pos hb]

open Classical in
theorem linearMapAt_apply (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B} (y : E b) :
    e.linearMapAt R b y = if b ∈ e.baseSet then (e ⟨b, y⟩).2 else 0 := by
  rw [coe_linearMapAt]

theorem linearMapAt_def_of_mem (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet) : e.linearMapAt R b = e.linearEquivAt R b hb :=
  dif_pos hb

theorem linearMapAt_def_of_notMem (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∉ e.baseSet) : e.linearMapAt R b = 0 :=
  dif_neg hb

theorem linearMapAt_eq_zero (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∉ e.baseSet) : e.linearMapAt R b = 0 :=
  dif_neg hb

theorem symmₗ_linearMapAt (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet) (y : E b) : e.symmₗ R b (e.linearMapAt R b y) = y := by
  rw [e.linearMapAt_def_of_mem hb]
  exact (e.linearEquivAt R b hb).left_inv y

theorem linearMapAt_symmₗ (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet) (y : F) : e.linearMapAt R b (e.symmₗ R b y) = y := by
  rw [e.linearMapAt_def_of_mem hb]
  exact (e.linearEquivAt R b hb).right_inv y

end Pretrivialization

variable [TopologicalSpace (TotalSpace F E)]

/-- A mixin class for `Bundle.Trivialization`, stating that a trivialization is fiberwise linear
with respect to given module structures on its fibers and the model fiber. -/
protected class Trivialization.IsLinear [AddCommMonoid F] [Module R F] [∀ x, AddCommMonoid (E x)]
  [∀ x, Module R (E x)] (e : Trivialization F (π F E)) : Prop where
  linear : ∀ b ∈ e.baseSet, IsLinearMap R fun x : E b => (e ⟨b, x⟩).2

namespace Trivialization

variable (e : Trivialization F (π F E)) {x : TotalSpace F E} {b : B} {y : E b}

protected theorem linear [AddCommMonoid F] [Module R F] [∀ x, AddCommMonoid (E x)]
    [∀ x, Module R (E x)] [e.IsLinear R] {b : B} (hb : b ∈ e.baseSet) :
    IsLinearMap R fun y : E b => (e ⟨b, y⟩).2 :=
  Trivialization.IsLinear.linear b hb

instance toPretrivialization.isLinear [AddCommMonoid F] [Module R F] [∀ x, AddCommMonoid (E x)]
    [∀ x, Module R (E x)] [e.IsLinear R] : e.toPretrivialization.IsLinear R :=
  { (‹_› : e.IsLinear R) with }

variable [AddCommMonoid F] [Module R F] [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)]

/-- A trivialization for a vector bundle defines linear equivalences between the
fibers and the model space. -/
def linearEquivAt (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) (hb : b ∈ e.baseSet) :
    E b ≃ₗ[R] F :=
  e.toPretrivialization.linearEquivAt R b hb

variable {R}

@[simp]
theorem linearEquivAt_apply (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
    (hb : b ∈ e.baseSet) (v : E b) : e.linearEquivAt R b hb v = (e ⟨b, v⟩).2 :=
  rfl

@[simp]
theorem linearEquivAt_symm_apply (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
    (hb : b ∈ e.baseSet) (v : F) : (e.linearEquivAt R b hb).symm v = e.symm b v :=
  rfl

variable (R) in
/-- A fiberwise linear inverse to `e`. -/
protected def symmₗ (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) : F →ₗ[R] E b :=
  e.toPretrivialization.symmₗ R b

theorem coe_symmₗ (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) :
    ⇑(e.symmₗ R b) = e.symm b :=
  rfl

variable (R) in
/-- A fiberwise linear map equal to `e` on `e.baseSet`. -/
protected def linearMapAt (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) : E b →ₗ[R] F :=
  e.toPretrivialization.linearMapAt R b

open Classical in
theorem coe_linearMapAt (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) :
    ⇑(e.linearMapAt R b) = fun y => if b ∈ e.baseSet then (e ⟨b, y⟩).2 else 0 :=
  e.toPretrivialization.coe_linearMapAt b

theorem coe_linearMapAt_of_mem (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet) : ⇑(e.linearMapAt R b) = fun y => (e ⟨b, y⟩).2 := by
  simp_rw [coe_linearMapAt, if_pos hb]

open Classical in
theorem linearMapAt_apply (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (y : E b) :
    e.linearMapAt R b y = if b ∈ e.baseSet then (e ⟨b, y⟩).2 else 0 := by
  rw [coe_linearMapAt]

theorem linearMapAt_def_of_mem (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet) : e.linearMapAt R b = e.linearEquivAt R b hb :=
  dif_pos hb

theorem linearMapAt_def_of_notMem (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∉ e.baseSet) : e.linearMapAt R b = 0 :=
  dif_neg hb

@[simp]
theorem symm_linearMapAt (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b ∈ e.baseSet)
    (y : E b) : e.symm b (e.linearMapAt R b y) = y :=
  e.toPretrivialization.symmₗ_linearMapAt hb y

theorem symmₗ_linearMapAt (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b ∈ e.baseSet)
    (y : E b) : e.symmₗ R b (e.linearMapAt R b y) = y :=
  e.toPretrivialization.symmₗ_linearMapAt hb y

@[simp]
theorem linearMapAt_symm (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b ∈ e.baseSet)
    (y : F) : e.linearMapAt R b (e.symm b y) = y :=
  e.toPretrivialization.linearMapAt_symmₗ hb y

theorem linearMapAt_symmₗ (e : Trivialization F (π F E)) [e.IsLinear R] {b : B} (hb : b ∈ e.baseSet)
    (y : F) : e.linearMapAt R b (e.symmₗ R b y) = y :=
  e.toPretrivialization.linearMapAt_symmₗ hb y

variable (R) in
open Classical in
/-- A coordinate change function between two trivializations, as a continuous linear equivalence.
  Defined to be the identity when `b` does not lie in the base set of both trivializations. -/
def coordChangeL (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] (b : B) :
    F ≃L[R] F :=
  { toLinearEquiv := if hb : b ∈ e.baseSet ∩ e'.baseSet
      then (e.linearEquivAt R b (hb.1 :)).symm.trans (e'.linearEquivAt R b hb.2)
      else LinearEquiv.refl R F
    continuous_toFun := by
      by_cases hb : b ∈ e.baseSet ∩ e'.baseSet
      · rw [dif_pos hb]
        refine (e'.continuousOn.comp_continuous ?_ ?_).snd
        · exact e.continuousOn_symm.comp_continuous (Continuous.prodMk_right b) fun y =>
            mk_mem_prod hb.1 (mem_univ y)
        · exact fun y => e'.mem_source.mpr hb.2
      · rw [dif_neg hb]
        exact continuous_id
    continuous_invFun := by
      by_cases hb : b ∈ e.baseSet ∩ e'.baseSet
      · rw [dif_pos hb]
        refine (e.continuousOn.comp_continuous ?_ ?_).snd
        · exact e'.continuousOn_symm.comp_continuous (Continuous.prodMk_right b) fun y =>
            mk_mem_prod hb.2 (mem_univ y)
        exact fun y => e.mem_source.mpr hb.1
      · rw [dif_neg hb]
        exact continuous_id }

theorem coe_coordChangeL (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    ⇑(coordChangeL R e e' b) = (e.linearEquivAt R b hb.1).symm.trans (e'.linearEquivAt R b hb.2) :=
  congr_arg (fun f : F ≃ₗ[R] F ↦ ⇑f) (dif_pos hb)

theorem coe_coordChangeL' (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    (coordChangeL R e e' b).toLinearEquiv =
      (e.linearEquivAt R b hb.1).symm.trans (e'.linearEquivAt R b hb.2) :=
  LinearEquiv.coe_injective (coe_coordChangeL _ _ hb)

theorem symm_coordChangeL (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
    (hb : b ∈ e'.baseSet ∩ e.baseSet) : (e.coordChangeL R e' b).symm = e'.coordChangeL R e b := by
  apply ContinuousLinearEquiv.toLinearEquiv_injective
  rw [coe_coordChangeL' e' e hb, (coordChangeL R e e' b).toLinearEquiv_symm,
    coe_coordChangeL' e e' hb.symm, LinearEquiv.trans_symm, LinearEquiv.symm_symm]

theorem coordChangeL_apply (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet ∩ e'.baseSet) (y : F) :
    coordChangeL R e e' b y = (e' ⟨b, e.symm b y⟩).2 :=
  congr_fun (coe_coordChangeL e e' hb) y

theorem mk_coordChangeL (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet ∩ e'.baseSet) (y : F) :
    (b, coordChangeL R e e' b y) = e' ⟨b, e.symm b y⟩ := by
  ext
  · rw [e.mk_symm hb.1 y, e'.coe_fst', e.proj_symm_apply' hb.1]
    rw [e.proj_symm_apply' hb.1]
    exact hb.2
  · exact e.coordChangeL_apply e' hb y

theorem apply_symm_apply_eq_coordChangeL (e e' : Trivialization F (π F E)) [e.IsLinear R]
    [e'.IsLinear R] {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) (v : F) :
    e' (e.toOpenPartialHomeomorph.symm (b, v)) = (b, e.coordChangeL R e' b v) := by
  rw [e.mk_coordChangeL e' hb, e.mk_symm hb.1]

/-- A version of `Bundle.Trivialization.coordChangeL_apply` that fully unfolds `coordChange`. The
right-hand side is ugly, but has good definitional properties for specifically defined
trivializations. -/
theorem coordChangeL_apply' (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet ∩ e'.baseSet) (y : F) :
    coordChangeL R e e' b y = (e' (e.toOpenPartialHomeomorph.symm (b, y))).2 := by
  rw [e.coordChangeL_apply e' hb, e.mk_symm hb.1]

theorem coordChangeL_symm_apply (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R]
    {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    ⇑(coordChangeL R e e' b).symm =
      (e'.linearEquivAt R b hb.2).symm.trans (e.linearEquivAt R b hb.1) :=
  congr_arg LinearEquiv.invFun (dif_pos hb)

end Bundle.Trivialization

end TopologicalVectorSpace

section

namespace Bundle

/-- The zero section of a vector bundle -/
def zeroSection [∀ x, Zero (E x)] : B → TotalSpace F E := (⟨·, 0⟩)

@[simp, mfld_simps]
theorem zeroSection_proj [∀ x, Zero (E x)] (x : B) : (zeroSection F E x).proj = x :=
  rfl

@[simp, mfld_simps]
theorem zeroSection_snd [∀ x, Zero (E x)] (x : B) : (zeroSection F E x).2 = 0 :=
  rfl

end Bundle

open Bundle

variable [NontriviallyNormedField R] [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)]
  [NormedAddCommGroup F] [NormedSpace R F] [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle F E]

/-- The space `Bundle.TotalSpace F E` (for `E : B → Type*` such that each `E x` is a topological
vector space) has a topological vector space structure with fiber `F` (denoted with
`VectorBundle R F E`) if around every point there is a fiber bundle trivialization which is linear
in the fibers. -/
class VectorBundle : Prop where
  trivialization_linear' : ∀ (e : Trivialization F (π F E)) [MemTrivializationAtlas e], e.IsLinear R
  continuousOn_coordChange' :
    ∀ (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e'],
      ContinuousOn (fun b => Trivialization.coordChangeL R e e' b : B → F →L[R] F)
        (e.baseSet ∩ e'.baseSet)

variable {F E}

instance (priority := 100) trivialization_linear [VectorBundle R F E] (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] : e.IsLinear R :=
  VectorBundle.trivialization_linear' e

theorem continuousOn_coordChange [VectorBundle R F E] (e e' : Trivialization F (π F E))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] :
    ContinuousOn (fun b => Trivialization.coordChangeL R e e' b : B → F →L[R] F)
      (e.baseSet ∩ e'.baseSet) :=
  VectorBundle.continuousOn_coordChange' e e'

namespace Bundle.Trivialization

/-- Forward map of `Bundle.Trivialization.continuousLinearEquivAt` (only propositionally equal),
  defined everywhere (`0` outside domain). -/
@[simps -fullyApplied apply]
def continuousLinearMapAt (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) : E b →L[R] F :=
  { e.linearMapAt R b with
    toFun := e.linearMapAt R b -- given explicitly to help `simps`
    cont := by
      rw [e.coe_linearMapAt b]
      classical
      refine continuous_if_const _ (fun hb => ?_) fun _ => continuous_zero
      exact (e.continuousOn.comp_continuous (FiberBundle.totalSpaceMk_isInducing F E b).continuous
        fun x => e.mem_source.mpr hb).snd }

/-- Backwards map of `Bundle.Trivialization.continuousLinearEquivAt`, defined everywhere. -/
@[simps -fullyApplied apply]
def symmL (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) : F →L[R] E b :=
  { e.symmₗ R b with
    toFun := e.symm b -- given explicitly to help `simps`
    cont := by
      by_cases hb : b ∈ e.baseSet
      · rw [(FiberBundle.totalSpaceMk_isInducing F E b).continuous_iff]
        exact e.continuousOn_symm.comp_continuous (.prodMk_right _) fun x ↦
          mk_mem_prod hb (mem_univ x)
      · refine continuous_zero.congr fun x => (e.symm_apply_of_notMem hb x).symm }

variable {R}

theorem symmL_continuousLinearMapAt (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet) (y : E b) : e.symmL R b (e.continuousLinearMapAt R b y) = y :=
  e.symmₗ_linearMapAt hb y

theorem continuousLinearMapAt_symmL (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet) (y : F) : e.continuousLinearMapAt R b (e.symmL R b y) = y :=
  e.linearMapAt_symmₗ hb y

variable (R) in
/-- In a vector bundle, a trivialization in the fiber (which is a priori only linear)
is in fact a continuous linear equiv between the fibers and the model fiber. -/
@[simps -fullyApplied apply symm_apply]
def continuousLinearEquivAt (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
    (hb : b ∈ e.baseSet) : E b ≃L[R] F :=
  { e.toPretrivialization.linearEquivAt R b hb with
    toFun := fun y => (e ⟨b, y⟩).2 -- given explicitly to help `simps`
    invFun := e.symm b -- given explicitly to help `simps`
    continuous_toFun := (e.continuousOn.comp_continuous
      (FiberBundle.totalSpaceMk_isInducing F E b).continuous fun _ => e.mem_source.mpr hb).snd
    continuous_invFun := (e.symmL R b).continuous }

theorem coe_continuousLinearEquivAt_eq (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet) :
    (e.continuousLinearEquivAt R b hb : E b → F) = e.continuousLinearMapAt R b :=
  (e.coe_linearMapAt_of_mem hb).symm

theorem coe_continuousLinearEquivAt_eq' (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet) :
    (e.continuousLinearEquivAt R b hb : E b →L[R] F) = e.continuousLinearMapAt R b :=
  DFunLike.coe_injective (e.coe_linearMapAt_of_mem hb).symm

theorem symm_continuousLinearEquivAt_eq (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet) : ((e.continuousLinearEquivAt R b hb).symm : F → E b) = e.symmL R b :=
  rfl

theorem symm_continuousLinearEquivAt_eq' (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet) : ((e.continuousLinearEquivAt R b hb).symm : F →L[R] E b) = e.symmL R b :=
  rfl

@[simp]
theorem continuousLinearEquivAt_apply' (e : Trivialization F (π F E)) [e.IsLinear R]
    (x : TotalSpace F E) (hx : x ∈ e.source) :
    e.continuousLinearEquivAt R x.proj (e.mem_source.1 hx) x.2 = (e x).2 := rfl

variable (R)

theorem apply_eq_prod_continuousLinearEquivAt (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
    (hb : b ∈ e.baseSet) (z : E b) : e ⟨b, z⟩ = (b, e.continuousLinearEquivAt R b hb z) := by
  ext
  · refine e.coe_fst ?_
    rw [e.source_eq]
    exact hb
  · simp only [continuousLinearEquivAt_apply]

protected theorem zeroSection (e : Trivialization F (π F E)) [e.IsLinear R] {x : B}
    (hx : x ∈ e.baseSet) : e (zeroSection F E x) = (x, 0) := by
  simp_rw [zeroSection, e.apply_eq_prod_continuousLinearEquivAt R x hx 0, map_zero]

variable {R}

theorem symm_apply_eq_mk_continuousLinearEquivAt_symm (e : Trivialization F (π F E)) [e.IsLinear R]
    (b : B) (hb : b ∈ e.baseSet) (z : F) :
    e.toOpenPartialHomeomorph.symm ⟨b, z⟩ = ⟨b, (e.continuousLinearEquivAt R b hb).symm z⟩ := by
  simpa using (mk_symm _ hb _).symm

theorem comp_continuousLinearEquivAt_eq_coord_change (e e' : Trivialization F (π F E))
    [e.IsLinear R] [e'.IsLinear R] {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    (e.continuousLinearEquivAt R b hb.1).symm.trans (e'.continuousLinearEquivAt R b hb.2) =
      coordChangeL R e e' b := by
  ext v
  rw [coordChangeL_apply e e' hb]
  rfl

end Bundle.Trivialization

/-! ### Constructing vector bundles -/

variable (B F)

/-- Analogous construction of `FiberBundleCore` for vector bundles. This
construction gives a way to construct vector bundles from a structure registering how
trivialization changes act on fibers. -/
structure VectorBundleCore (ι : Type*) where
  baseSet : ι → Set B
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  indexAt : B → ι
  mem_baseSet_at : ∀ x, x ∈ baseSet (indexAt x)
  coordChange : ι → ι → B → F →L[R] F
  coordChange_self : ∀ i, ∀ x ∈ baseSet i, ∀ v, coordChange i i x v = v
  continuousOn_coordChange : ∀ i j, ContinuousOn (coordChange i j) (baseSet i ∩ baseSet j)
  coordChange_comp : ∀ i j k, ∀ x ∈ baseSet i ∩ baseSet j ∩ baseSet k, ∀ v,
    (coordChange j k x) (coordChange i j x v) = coordChange i k x v

/-- The trivial vector bundle core, in which all the changes of coordinates are the
identity. -/
def trivialVectorBundleCore (ι : Type*) [Inhabited ι] : VectorBundleCore R B F ι where
  baseSet _ := univ
  isOpen_baseSet _ := isOpen_univ
  indexAt := default
  mem_baseSet_at x := mem_univ x
  coordChange _ _ _ := ContinuousLinearMap.id R F
  coordChange_self _ _ _ _ := rfl
  coordChange_comp _ _ _ _ _ _ := rfl
  continuousOn_coordChange _ _ := continuousOn_const

instance (ι : Type*) [Inhabited ι] : Inhabited (VectorBundleCore R B F ι) :=
  ⟨trivialVectorBundleCore R B F ι⟩

namespace VectorBundleCore

variable {R B F} {ι : Type*}
variable (Z : VectorBundleCore R B F ι)

/-- Natural identification to a `FiberBundleCore`. -/
@[simps (attr := mfld_simps) -fullyApplied]
def toFiberBundleCore : FiberBundleCore ι B F :=
  { Z with
    coordChange := fun i j b => Z.coordChange i j b
    continuousOn_coordChange := fun i j =>
      isBoundedBilinearMap_apply.continuous.comp_continuousOn
        ((Z.continuousOn_coordChange i j).prodMap continuousOn_id) }

-- TODO: restore coercion?
-- instance toFiberBundleCoreCoe : Coe (VectorBundleCore R B F ι) (FiberBundleCore ι B F) :=
--   ⟨toFiberBundleCore⟩

theorem coordChange_linear_comp (i j k : ι) :
    ∀ x ∈ Z.baseSet i ∩ Z.baseSet j ∩ Z.baseSet k,
      (Z.coordChange j k x).comp (Z.coordChange i j x) = Z.coordChange i k x :=
  fun x hx => by
  ext v
  exact Z.coordChange_comp i j k x hx v

/-- The index set of a vector bundle core, as a convenience function for dot notation -/
@[nolint unusedArguments]
def Index := ι

/-- The base space of a vector bundle core, as a convenience function for dot notation -/
@[nolint unusedArguments, reducible]
def Base := B

/-- The fiber of a vector bundle core, as a convenience function for dot notation and
typeclass inference -/
@[nolint unusedArguments]
def Fiber : B → Type _ :=
  Z.toFiberBundleCore.Fiber

instance topologicalSpaceFiber (x : B) : TopologicalSpace (Z.Fiber x) :=
  Z.toFiberBundleCore.topologicalSpaceFiber x

instance addCommGroupFiber (x : B) : AddCommGroup (Z.Fiber x) :=
  inferInstanceAs (AddCommGroup F)

instance moduleFiber (x : B) : Module R (Z.Fiber x) :=
  inferInstanceAs (Module R F)

/-- The projection from the total space of a fiber bundle core, on its base. -/
@[reducible, simp, mfld_simps]
protected def proj : TotalSpace F Z.Fiber → B :=
  TotalSpace.proj

/-- The total space of the vector bundle, as a convenience function for dot notation.
It is by definition equal to `Bundle.TotalSpace F Z.Fiber`. -/
@[nolint unusedArguments, reducible]
protected def TotalSpace :=
  Bundle.TotalSpace F Z.Fiber

/-- Local homeomorphism version of the trivialization change. -/
def trivChange (i j : ι) : OpenPartialHomeomorph (B × F) (B × F) :=
  Z.toFiberBundleCore.trivChange i j

@[simp, mfld_simps]
theorem mem_trivChange_source (i j : ι) (p : B × F) :
    p ∈ (Z.trivChange i j).source ↔ p.1 ∈ Z.baseSet i ∩ Z.baseSet j :=
  Z.toFiberBundleCore.mem_trivChange_source i j p

/-- Topological structure on the total space of a vector bundle created from core, designed so
that all the local trivialization are continuous. -/
instance toTopologicalSpace : TopologicalSpace Z.TotalSpace :=
  Z.toFiberBundleCore.toTopologicalSpace

variable (b : B) (a : F)

@[simp, mfld_simps]
theorem coe_coordChange (i j : ι) : Z.toFiberBundleCore.coordChange i j b = Z.coordChange i j b :=
  rfl

/-- One of the standard local trivializations of a vector bundle constructed from core, taken by
considering this in particular as a fiber bundle constructed from core. -/
def localTriv (i : ι) : Trivialization F (π F Z.Fiber) :=
  Z.toFiberBundleCore.localTriv i

@[simp, mfld_simps]
theorem localTriv_apply {i : ι} (p : Z.TotalSpace) :
    (Z.localTriv i) p = ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The standard local trivializations of a vector bundle constructed from core are linear. -/
instance localTriv.isLinear (i : ι) : (Z.localTriv i).IsLinear R where
  linear x _ :=
    { map_add := fun _ _ => by simp only [map_add, localTriv_apply, mfld_simps]
      map_smul := fun _ _ => by simp only [map_smul, localTriv_apply, mfld_simps] }

variable (i j : ι)

@[simp, mfld_simps]
theorem mem_localTriv_source (p : Z.TotalSpace) : p ∈ (Z.localTriv i).source ↔ p.1 ∈ Z.baseSet i :=
  Iff.rfl

@[simp, mfld_simps]
theorem baseSet_at : Z.baseSet i = (Z.localTriv i).baseSet :=
  rfl

@[simp, mfld_simps]
theorem mem_localTriv_target (p : B × F) :
    p ∈ (Z.localTriv i).target ↔ p.1 ∈ (Z.localTriv i).baseSet :=
  Z.toFiberBundleCore.mem_localTriv_target i p

@[simp, mfld_simps]
theorem localTriv_symm_fst (p : B × F) :
    (Z.localTriv i).toOpenPartialHomeomorph.symm p =
      ⟨p.1, Z.coordChange i (Z.indexAt p.1) p.1 p.2⟩ :=
  rfl

@[simp, mfld_simps]
theorem localTriv_symm_apply {b : B} (hb : b ∈ (Z.localTriv i).baseSet) (v : F) :
    (Z.localTriv i).symm b v = Z.coordChange i (Z.indexAt b) b v := by
  apply (Z.localTriv i).symm_apply hb v

@[simp, mfld_simps]
theorem localTriv_coordChange_eq {b : B}
    (hb : b ∈ (Z.localTriv i).baseSet ∧ b ∈ (Z.localTriv j).baseSet) (v : F) :
    (Z.localTriv i).coordChangeL R (Z.localTriv j) b v = Z.coordChange i j b v := by
  rw [Trivialization.coordChangeL_apply', localTriv_symm_fst, localTriv_apply, coordChange_comp]
  exacts [⟨⟨hb.1, Z.mem_baseSet_at b⟩, hb.2⟩, hb]

/-- Preferred local trivialization of a vector bundle constructed from core, at a given point, as
a bundle trivialization -/
def localTrivAt (b : B) : Trivialization F (π F Z.Fiber) :=
  Z.localTriv (Z.indexAt b)

@[simp, mfld_simps]
theorem localTrivAt_def : Z.localTriv (Z.indexAt b) = Z.localTrivAt b :=
  rfl

@[simp, mfld_simps]
theorem mem_source_at : (⟨b, a⟩ : Z.TotalSpace) ∈ (Z.localTrivAt b).source := by
  rw [localTrivAt, mem_localTriv_source]
  exact Z.mem_baseSet_at b

@[simp, mfld_simps]
theorem localTrivAt_apply (p : Z.TotalSpace) : Z.localTrivAt p.1 p = ⟨p.1, p.2⟩ :=
  Z.toFiberBundleCore.localTrivAt_apply p

@[simp, mfld_simps]
theorem localTrivAt_apply_mk (b : B) (a : F) : Z.localTrivAt b ⟨b, a⟩ = ⟨b, a⟩ :=
  Z.localTrivAt_apply _

@[simp, mfld_simps]
theorem mem_localTrivAt_baseSet : b ∈ (Z.localTrivAt b).baseSet :=
  Z.toFiberBundleCore.mem_localTrivAt_baseSet b

instance fiberBundle : FiberBundle F Z.Fiber :=
  Z.toFiberBundleCore.fiberBundle

protected lemma trivializationAt : trivializationAt F Z.Fiber b = Z.localTrivAt b := rfl

instance vectorBundle : VectorBundle R F Z.Fiber where
  trivialization_linear' := by
    rintro _ ⟨i, rfl⟩
    apply localTriv.isLinear
  continuousOn_coordChange' := by
    rintro _ _ ⟨i, rfl⟩ ⟨i', rfl⟩
    refine (Z.continuousOn_coordChange i i').congr fun b hb => ?_
    ext v
    exact Z.localTriv_coordChange_eq i i' hb v

/-- The projection on the base of a vector bundle created from core is continuous -/
@[continuity]
theorem continuous_proj : Continuous Z.proj :=
  Z.toFiberBundleCore.continuous_proj

/-- The projection on the base of a vector bundle created from core is an open map -/
theorem isOpenMap_proj : IsOpenMap Z.proj :=
  Z.toFiberBundleCore.isOpenMap_proj

variable {i j}

@[simp, mfld_simps]
theorem localTriv_continuousLinearMapAt {b : B} (hb : b ∈ (Z.localTriv i).baseSet) :
    (Z.localTriv i).continuousLinearMapAt R b = Z.coordChange (Z.indexAt b) i b := by
  ext1 v
  rw [(Z.localTriv i).continuousLinearMapAt_apply R, (Z.localTriv i).coe_linearMapAt_of_mem]
  exacts [rfl, hb]

@[simp, mfld_simps]
theorem trivializationAt_continuousLinearMapAt {b₀ b : B}
    (hb : b ∈ (trivializationAt F Z.Fiber b₀).baseSet) :
    (trivializationAt F Z.Fiber b₀).continuousLinearMapAt R b =
      Z.coordChange (Z.indexAt b) (Z.indexAt b₀) b :=
  Z.localTriv_continuousLinearMapAt hb

@[simp, mfld_simps]
theorem localTriv_symmL {b : B} (hb : b ∈ (Z.localTriv i).baseSet) :
    (Z.localTriv i).symmL R b = Z.coordChange i (Z.indexAt b) b := by
  ext1 v
  rw [(Z.localTriv i).symmL_apply R, (Z.localTriv i).symm_apply]
  exacts [rfl, hb]

@[simp, mfld_simps]
theorem trivializationAt_symmL {b₀ b : B} (hb : b ∈ (trivializationAt F Z.Fiber b₀).baseSet) :
    (trivializationAt F Z.Fiber b₀).symmL R b = Z.coordChange (Z.indexAt b₀) (Z.indexAt b) b :=
  Z.localTriv_symmL hb

@[simp, mfld_simps]
theorem trivializationAt_coordChange_eq {b₀ b₁ b : B}
    (hb : b ∈ (trivializationAt F Z.Fiber b₀).baseSet ∩ (trivializationAt F Z.Fiber b₁).baseSet)
    (v : F) :
    (trivializationAt F Z.Fiber b₀).coordChangeL R (trivializationAt F Z.Fiber b₁) b v =
      Z.coordChange (Z.indexAt b₀) (Z.indexAt b₁) b v :=
  Z.localTriv_coordChange_eq _ _ hb v

end VectorBundleCore

end

/-! ### Vector prebundle -/

section

variable [NontriviallyNormedField R] [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)]
  [NormedAddCommGroup F] [NormedSpace R F] [TopologicalSpace B] [∀ x, TopologicalSpace (E x)]

open TopologicalSpace

open VectorBundle

/-- This structure permits to define a vector bundle when trivializations are given as local
equivalences but there is not yet a topology on the total space or the fibers.
The total space is hence given a topology in such a way that there is a fiber bundle structure for
which the partial equivalences are also open partial homeomorphisms and hence vector bundle
trivializations. The topology on the fibers is induced from the one on the total space.

The field `exists_coordChange` is stated as an existential statement (instead of 3 separate
fields), since it depends on propositional information (namely `e e' ∈ pretrivializationAtlas`).
This makes it inconvenient to explicitly define a `coordChange` function when constructing a
`VectorPrebundle`. -/
structure VectorPrebundle where
  pretrivializationAtlas : Set (Pretrivialization F (π F E))
  pretrivialization_linear' : ∀ e, e ∈ pretrivializationAtlas → e.IsLinear R
  pretrivializationAt : B → Pretrivialization F (π F E)
  mem_base_pretrivializationAt : ∀ x : B, x ∈ (pretrivializationAt x).baseSet
  pretrivialization_mem_atlas : ∀ x : B, pretrivializationAt x ∈ pretrivializationAtlas
  exists_coordChange : ∀ᵉ (e ∈ pretrivializationAtlas) (e' ∈ pretrivializationAtlas),
    ∃ f : B → F →L[R] F, ContinuousOn f (e.baseSet ∩ e'.baseSet) ∧
      ∀ᵉ (b ∈ e.baseSet ∩ e'.baseSet) (v : F), f b v = (e' ⟨b, e.symm b v⟩).2
  totalSpaceMk_isInducing : ∀ b : B, IsInducing (pretrivializationAt b ∘ .mk b)

namespace VectorPrebundle

variable {R E F}

/-- A randomly chosen coordinate change on a `VectorPrebundle`, given by
  the field `exists_coordChange`. -/
def coordChange (a : VectorPrebundle R F E) {e e' : Pretrivialization F (π F E)}
    (he : e ∈ a.pretrivializationAtlas) (he' : e' ∈ a.pretrivializationAtlas) (b : B) : F →L[R] F :=
  Classical.choose (a.exists_coordChange e he e' he') b

theorem continuousOn_coordChange (a : VectorPrebundle R F E) {e e' : Pretrivialization F (π F E)}
    (he : e ∈ a.pretrivializationAtlas) (he' : e' ∈ a.pretrivializationAtlas) :
    ContinuousOn (a.coordChange he he') (e.baseSet ∩ e'.baseSet) :=
  (Classical.choose_spec (a.exists_coordChange e he e' he')).1

theorem coordChange_apply (a : VectorPrebundle R F E) {e e' : Pretrivialization F (π F E)}
    (he : e ∈ a.pretrivializationAtlas) (he' : e' ∈ a.pretrivializationAtlas) {b : B}
    (hb : b ∈ e.baseSet ∩ e'.baseSet) (v : F) :
    a.coordChange he he' b v = (e' ⟨b, e.symm b v⟩).2 :=
  (Classical.choose_spec (a.exists_coordChange e he e' he')).2 b hb v

theorem mk_coordChange (a : VectorPrebundle R F E) {e e' : Pretrivialization F (π F E)}
    (he : e ∈ a.pretrivializationAtlas) (he' : e' ∈ a.pretrivializationAtlas) {b : B}
    (hb : b ∈ e.baseSet ∩ e'.baseSet) (v : F) :
    (b, a.coordChange he he' b v) = e' ⟨b, e.symm b v⟩ := by
  ext
  · rw [e.mk_symm hb.1 v, e'.coe_fst', e.proj_symm_apply' hb.1]
    rw [e.proj_symm_apply' hb.1]
    exact hb.2
  · exact a.coordChange_apply he he' hb v

/-- Natural identification of `VectorPrebundle` as a `FiberPrebundle`. -/
def toFiberPrebundle (a : VectorPrebundle R F E) : FiberPrebundle F E :=
  { a with
    continuous_trivChange := fun e he e' he' ↦ by
      have : ContinuousOn (fun x : B × F ↦ a.coordChange he' he x.1 x.2)
          ((e'.baseSet ∩ e.baseSet) ×ˢ univ) :=
        isBoundedBilinearMap_apply.continuous.comp_continuousOn
          ((a.continuousOn_coordChange he' he).prodMap continuousOn_id)
      rw [e.target_inter_preimage_symm_source_eq e', inter_comm]
      refine (continuousOn_fst.prodMk this).congr ?_
      rintro ⟨b, f⟩ ⟨hb, -⟩
      dsimp only [Function.comp_def, Prod.map]
      rw [a.mk_coordChange _ _ hb, e'.mk_symm hb.1] }

/-- Topology on the total space that will make the prebundle into a bundle. -/
@[implicit_reducible]
def totalSpaceTopology (a : VectorPrebundle R F E) : TopologicalSpace (TotalSpace F E) :=
  a.toFiberPrebundle.totalSpaceTopology

/-- Promotion from a `Pretrivialization` in the `pretrivializationAtlas` of a
`VectorPrebundle` to a `Trivialization`. -/
def trivializationOfMemPretrivializationAtlas (a : VectorPrebundle R F E)
    {e : Pretrivialization F (π F E)} (he : e ∈ a.pretrivializationAtlas) :
    @Trivialization B F _ _ _ a.totalSpaceTopology (π F E) :=
  a.toFiberPrebundle.trivializationOfMemPretrivializationAtlas he

theorem linear_trivializationOfMemPretrivializationAtlas (a : VectorPrebundle R F E)
    {e : Pretrivialization F (π F E)} (he : e ∈ a.pretrivializationAtlas) :
    letI := a.totalSpaceTopology
    Trivialization.IsLinear R (trivializationOfMemPretrivializationAtlas a he) :=
  letI := a.totalSpaceTopology
  { linear := (a.pretrivialization_linear' e he).linear }

variable (a : VectorPrebundle R F E)

theorem mem_trivialization_at_source (b : B) (x : E b) :
    ⟨b, x⟩ ∈ (a.pretrivializationAt b).source :=
  a.toFiberPrebundle.mem_pretrivializationAt_source b x

@[simp]
theorem totalSpaceMk_preimage_source (b : B) :
    .mk b ⁻¹' (a.pretrivializationAt b).source = univ :=
  a.toFiberPrebundle.totalSpaceMk_preimage_source b

@[continuity]
theorem continuous_totalSpaceMk (b : B) :
    Continuous[_, a.totalSpaceTopology] (.mk b) :=
  a.toFiberPrebundle.continuous_totalSpaceMk b

/-- Make a `FiberBundle` from a `VectorPrebundle`; auxiliary construction for
`VectorPrebundle.toVectorBundle`. -/
@[implicit_reducible]
def toFiberBundle : @FiberBundle B F _ _ _ a.totalSpaceTopology _ :=
  a.toFiberPrebundle.toFiberBundle

/-- Make a `VectorBundle` from a `VectorPrebundle`.  Concretely this means
that, given a `VectorPrebundle` structure for a sigma-type `E` -- which consists of a
number of "pretrivializations" identifying parts of `E` with product spaces `U × F` -- one
establishes that for the topology constructed on the sigma-type using
`VectorPrebundle.totalSpaceTopology`, these "pretrivializations" are actually
"trivializations" (i.e., homeomorphisms with respect to the constructed topology). -/
theorem toVectorBundle : @VectorBundle R _ F E _ _ _ _ _ _ a.totalSpaceTopology _ a.toFiberBundle :=
  letI := a.totalSpaceTopology; letI := a.toFiberBundle
  { trivialization_linear' := by
      rintro _ ⟨e, he, rfl⟩
      apply linear_trivializationOfMemPretrivializationAtlas
    continuousOn_coordChange' := by
      rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
      refine (a.continuousOn_coordChange he he').congr fun b hb ↦ ?_
      ext v
      haveI h₁ := a.linear_trivializationOfMemPretrivializationAtlas he
      haveI h₂ := a.linear_trivializationOfMemPretrivializationAtlas he'
      rw [trivializationOfMemPretrivializationAtlas] at h₁ h₂
      rw [a.coordChange_apply he he' hb v, ContinuousLinearEquiv.coe_coe,
        Trivialization.coordChangeL_apply]
      exacts [rfl, hb] }

end VectorPrebundle

namespace ContinuousLinearMap

variable {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
variable {σ : 𝕜₁ →+* 𝕜₂}
variable {B' : Type*} [TopologicalSpace B']
variable [NormedSpace 𝕜₁ F] [∀ x, Module 𝕜₁ (E x)] [TopologicalSpace (TotalSpace F E)]
variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜₂ F'] {E' : B' → Type*}
  [∀ x, AddCommMonoid (E' x)] [∀ x, Module 𝕜₂ (E' x)] [TopologicalSpace (TotalSpace F' E')]

variable [FiberBundle F E] [VectorBundle 𝕜₁ F E]
variable [∀ x, TopologicalSpace (E' x)] [FiberBundle F' E'] [VectorBundle 𝕜₂ F' E']
variable (F' E')

/-- When `ϕ` is a continuous (semi)linear map between the fibers `E x` and `E' y` of two vector
bundles `E` and `E'`, `ContinuousLinearMap.inCoordinates F E F' E' x₀ x y₀ y ϕ` is a coordinate
change of this continuous linear map w.r.t. the chart around `x₀` and the chart around `y₀`.

It is defined by composing `ϕ` with appropriate coordinate changes given by the vector bundles
`E` and `E'`.
We use the operations `Bundle.Trivialization.continuousLinearMapAt` and
`Bundle.Trivialization.symmL` in the definition, instead of
`Bundle.Trivialization.continuousLinearEquivAt`, so that
`ContinuousLinearMap.inCoordinates` is defined everywhere (but see
`ContinuousLinearMap.inCoordinates_eq`).

This is the (second component of the) underlying function of a trivialization of the hom-bundle
(see `hom_trivializationAt_apply`). However, note that `ContinuousLinearMap.inCoordinates` is
defined even when `x` and `y` live in different base sets.
Therefore, it is also convenient when working with the hom-bundle between pulled back bundles.
-/
def inCoordinates (x₀ x : B) (y₀ y : B') (ϕ : E x →SL[σ] E' y) : F →SL[σ] F' :=
  ((trivializationAt F' E' y₀).continuousLinearMapAt 𝕜₂ y).comp <|
    ϕ.comp <| (trivializationAt F E x₀).symmL 𝕜₁ x

variable {E E' F F'}

/-- Rewrite `ContinuousLinearMap.inCoordinates` using continuous linear equivalences. -/
theorem inCoordinates_eq {x₀ x : B} {y₀ y : B'} {ϕ : E x →SL[σ] E' y}
    (hx : x ∈ (trivializationAt F E x₀).baseSet) (hy : y ∈ (trivializationAt F' E' y₀).baseSet) :
    inCoordinates F E F' E' x₀ x y₀ y ϕ =
      ((trivializationAt F' E' y₀).continuousLinearEquivAt 𝕜₂ y hy : E' y →L[𝕜₂] F').comp
        (ϕ.comp <|
          (((trivializationAt F E x₀).continuousLinearEquivAt 𝕜₁ x hx).symm : F →L[𝕜₁] E x)) := by
  ext
  simp_rw [inCoordinates, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
    Trivialization.coe_continuousLinearEquivAt_eq, Trivialization.symm_continuousLinearEquivAt_eq]

set_option backward.isDefEq.respectTransparency false in
/-- Rewrite `ContinuousLinearMap.inCoordinates` in a `VectorBundleCore`. -/
protected theorem _root_.VectorBundleCore.inCoordinates_eq {ι ι'} (Z : VectorBundleCore 𝕜₁ B F ι)
    (Z' : VectorBundleCore 𝕜₂ B' F' ι') {x₀ x : B} {y₀ y : B'} (ϕ : F →SL[σ] F')
    (hx : x ∈ Z.baseSet (Z.indexAt x₀)) (hy : y ∈ Z'.baseSet (Z'.indexAt y₀)) :
    inCoordinates F Z.Fiber F' Z'.Fiber x₀ x y₀ y ϕ =
      (Z'.coordChange (Z'.indexAt y) (Z'.indexAt y₀) y).comp
        (ϕ.comp <| Z.coordChange (Z.indexAt x₀) (Z.indexAt x) x) := by
  simp_rw [inCoordinates, Z'.trivializationAt_continuousLinearMapAt hy,
    Z.trivializationAt_symmL hx]

end ContinuousLinearMap

end
