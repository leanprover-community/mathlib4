/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Topology.Algebra.Module.Basic

#align_import topology.algebra.continuous_affine_map from "leanprover-community/mathlib"@"bd1fc183335ea95a9519a1630bcf901fe9326d83"

/-!
# Continuous affine maps.

This file defines a type of bundled continuous affine maps.

Note that the definition and basic properties established here require minimal assumptions, and do
not even assume compatibility between the topological and algebraic structures. Of course it is
necessary to assume some compatibility in order to obtain a useful theory. Such a theory is
developed elsewhere for affine spaces modelled on _normed_ vector spaces, but not yet for general
topological affine spaces (since we have not defined these yet).

## Main definitions:

 * `ContinuousAffineMap`

## Notation:

We introduce the notation `P →ᴬ[R] Q` for `ContinuousAffineMap R P Q`. Note that this is parallel
to the notation `E →L[R] F` for `ContinuousLinearMap R E F`.
-/


/-- A continuous map of affine spaces. -/
structure ContinuousAffineMap (R : Type*) {V W : Type*} (P Q : Type*) [Ring R] [AddCommGroup V]
  [Module R V] [TopologicalSpace P] [AddTorsor V P] [AddCommGroup W] [Module R W]
  [TopologicalSpace Q] [AddTorsor W Q] extends P →ᵃ[R] Q where
  cont : Continuous toFun
#align continuous_affine_map ContinuousAffineMap

/-- A continuous map of affine spaces. -/
notation:25 P " →ᴬ[" R "] " Q => ContinuousAffineMap R P Q

namespace ContinuousAffineMap

variable {R V W P Q : Type*} [Ring R]
variable [AddCommGroup V] [Module R V] [TopologicalSpace P] [AddTorsor V P]
variable [AddCommGroup W] [Module R W] [TopologicalSpace Q] [AddTorsor W Q]

instance : Coe (P →ᴬ[R] Q) (P →ᵃ[R] Q) :=
  ⟨toAffineMap⟩

theorem to_affineMap_injective {f g : P →ᴬ[R] Q} (h : (f : P →ᵃ[R] Q) = (g : P →ᵃ[R] Q)) :
    f = g := by
  cases f
  cases g
  congr
#align continuous_affine_map.to_affine_map_injective ContinuousAffineMap.to_affineMap_injective

instance : FunLike (P →ᴬ[R] Q) P Q where
  coe f := f.toAffineMap
  coe_injective' _ _ h := to_affineMap_injective <| DFunLike.coe_injective h

instance : ContinuousMapClass (P →ᴬ[R] Q) P Q where
  map_continuous := cont

theorem toFun_eq_coe (f : P →ᴬ[R] Q) : f.toFun = ⇑f := rfl
#align continuous_affine_map.to_fun_eq_coe ContinuousAffineMap.toFun_eq_coe

theorem coe_injective : @Function.Injective (P →ᴬ[R] Q) (P → Q) (⇑) :=
  DFunLike.coe_injective
#align continuous_affine_map.coe_injective ContinuousAffineMap.coe_injective

@[ext]
theorem ext {f g : P →ᴬ[R] Q} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h
#align continuous_affine_map.ext ContinuousAffineMap.ext

theorem ext_iff {f g : P →ᴬ[R] Q} : f = g ↔ ∀ x, f x = g x :=
  DFunLike.ext_iff
#align continuous_affine_map.ext_iff ContinuousAffineMap.ext_iff

theorem congr_fun {f g : P →ᴬ[R] Q} (h : f = g) (x : P) : f x = g x :=
  DFunLike.congr_fun h _
#align continuous_affine_map.congr_fun ContinuousAffineMap.congr_fun

/-- Forgetting its algebraic properties, a continuous affine map is a continuous map. -/
def toContinuousMap (f : P →ᴬ[R] Q) : C(P, Q) :=
  ⟨f, f.cont⟩
#align continuous_affine_map.to_continuous_map ContinuousAffineMap.toContinuousMap

-- Porting note: changed to CoeHead due to difficulty with synthesization order
instance : CoeHead (P →ᴬ[R] Q) C(P, Q) :=
  ⟨toContinuousMap⟩

@[simp]
theorem toContinuousMap_coe (f : P →ᴬ[R] Q) : f.toContinuousMap = ↑f := rfl
#align continuous_affine_map.to_continuous_map_coe ContinuousAffineMap.toContinuousMap_coe

@[simp] -- Porting note: removed `norm_cast`
theorem coe_to_affineMap (f : P →ᴬ[R] Q) : ((f : P →ᵃ[R] Q) : P → Q) = f := rfl
#align continuous_affine_map.coe_to_affine_map ContinuousAffineMap.coe_to_affineMap

-- Porting note: removed `norm_cast` and `simp` since proof is `simp only [ContinuousMap.coe_mk]`
theorem coe_to_continuousMap (f : P →ᴬ[R] Q) : ((f : C(P, Q)) : P → Q) = f := rfl
#align continuous_affine_map.coe_to_continuous_map ContinuousAffineMap.coe_to_continuousMap

theorem to_continuousMap_injective {f g : P →ᴬ[R] Q} (h : (f : C(P, Q)) = (g : C(P, Q))) :
    f = g := by
  ext a
  exact ContinuousMap.congr_fun h a
#align continuous_affine_map.to_continuous_map_injective ContinuousAffineMap.to_continuousMap_injective

-- Porting note: removed `norm_cast`
theorem coe_affineMap_mk (f : P →ᵃ[R] Q) (h) : ((⟨f, h⟩ : P →ᴬ[R] Q) : P →ᵃ[R] Q) = f := rfl
#align continuous_affine_map.coe_affine_map_mk ContinuousAffineMap.coe_affineMap_mk

@[norm_cast]
theorem coe_continuousMap_mk (f : P →ᵃ[R] Q) (h) : ((⟨f, h⟩ : P →ᴬ[R] Q) : C(P, Q)) = ⟨f, h⟩ := rfl
#align continuous_affine_map.coe_continuous_map_mk ContinuousAffineMap.coe_continuousMap_mk

@[simp]
theorem coe_mk (f : P →ᵃ[R] Q) (h) : ((⟨f, h⟩ : P →ᴬ[R] Q) : P → Q) = f := rfl
#align continuous_affine_map.coe_mk ContinuousAffineMap.coe_mk

@[simp]
theorem mk_coe (f : P →ᴬ[R] Q) (h) : (⟨(f : P →ᵃ[R] Q), h⟩ : P →ᴬ[R] Q) = f := by
  ext
  rfl
#align continuous_affine_map.mk_coe ContinuousAffineMap.mk_coe

@[continuity]
protected theorem continuous (f : P →ᴬ[R] Q) : Continuous f := f.2
#align continuous_affine_map.continuous ContinuousAffineMap.continuous

variable (R P)

/-- The constant map is a continuous affine map. -/
def const (q : Q) : P →ᴬ[R] Q :=
  { AffineMap.const R P q with
    toFun := AffineMap.const R P q
    cont := continuous_const }
#align continuous_affine_map.const ContinuousAffineMap.const

@[simp]
theorem coe_const (q : Q) : (const R P q : P → Q) = Function.const P q := rfl
#align continuous_affine_map.coe_const ContinuousAffineMap.coe_const

noncomputable instance : Inhabited (P →ᴬ[R] Q) :=
  ⟨const R P <| Nonempty.some (by infer_instance : Nonempty Q)⟩

variable {R P} {W₂ Q₂ : Type*}
variable [AddCommGroup W₂] [Module R W₂] [TopologicalSpace Q₂] [AddTorsor W₂ Q₂]

/-- The composition of morphisms is a morphism. -/
def comp (f : Q →ᴬ[R] Q₂) (g : P →ᴬ[R] Q) : P →ᴬ[R] Q₂ :=
  { (f : Q →ᵃ[R] Q₂).comp (g : P →ᵃ[R] Q) with cont := f.cont.comp g.cont }
#align continuous_affine_map.comp ContinuousAffineMap.comp

@[simp, norm_cast]
theorem coe_comp (f : Q →ᴬ[R] Q₂) (g : P →ᴬ[R] Q) :
    (f.comp g : P → Q₂) = (f : Q → Q₂) ∘ (g : P → Q) := rfl
#align continuous_affine_map.coe_comp ContinuousAffineMap.coe_comp

theorem comp_apply (f : Q →ᴬ[R] Q₂) (g : P →ᴬ[R] Q) (x : P) : f.comp g x = f (g x) := rfl
#align continuous_affine_map.comp_apply ContinuousAffineMap.comp_apply

section ModuleValuedMaps

variable {S : Type*}
variable [TopologicalSpace W]

instance : Zero (P →ᴬ[R] W) :=
  ⟨ContinuousAffineMap.const R P 0⟩

@[norm_cast, simp]
theorem coe_zero : ((0 : P →ᴬ[R] W) : P → W) = 0 := rfl
#align continuous_affine_map.coe_zero ContinuousAffineMap.coe_zero

theorem zero_apply (x : P) : (0 : P →ᴬ[R] W) x = 0 := rfl
#align continuous_affine_map.zero_apply ContinuousAffineMap.zero_apply

section MulAction

variable [Monoid S] [DistribMulAction S W] [SMulCommClass R S W]
variable [ContinuousConstSMul S W]

instance : SMul S (P →ᴬ[R] W) where
  smul t f := { t • (f : P →ᵃ[R] W) with cont := f.continuous.const_smul t }

@[norm_cast, simp]
theorem coe_smul (t : S) (f : P →ᴬ[R] W) : ⇑(t • f) = t • ⇑f := rfl
#align continuous_affine_map.coe_smul ContinuousAffineMap.coe_smul

theorem smul_apply (t : S) (f : P →ᴬ[R] W) (x : P) : (t • f) x = t • f x := rfl
#align continuous_affine_map.smul_apply ContinuousAffineMap.smul_apply

instance [DistribMulAction Sᵐᵒᵖ W] [IsCentralScalar S W] : IsCentralScalar S (P →ᴬ[R] W) where
  op_smul_eq_smul _ _ := ext fun _ ↦ op_smul_eq_smul _ _

instance : MulAction S (P →ᴬ[R] W) :=
  Function.Injective.mulAction _ coe_injective coe_smul

end MulAction

variable [TopologicalAddGroup W]

instance : Add (P →ᴬ[R] W) where
  add f g := { (f : P →ᵃ[R] W) + (g : P →ᵃ[R] W) with cont := f.continuous.add g.continuous }

@[norm_cast, simp]
theorem coe_add (f g : P →ᴬ[R] W) : ⇑(f + g) = f + g := rfl
#align continuous_affine_map.coe_add ContinuousAffineMap.coe_add

theorem add_apply (f g : P →ᴬ[R] W) (x : P) : (f + g) x = f x + g x := rfl
#align continuous_affine_map.add_apply ContinuousAffineMap.add_apply

instance : Sub (P →ᴬ[R] W) where
  sub f g := { (f : P →ᵃ[R] W) - (g : P →ᵃ[R] W) with cont := f.continuous.sub g.continuous }

@[norm_cast, simp]
theorem coe_sub (f g : P →ᴬ[R] W) : ⇑(f - g) = f - g := rfl
#align continuous_affine_map.coe_sub ContinuousAffineMap.coe_sub

theorem sub_apply (f g : P →ᴬ[R] W) (x : P) : (f - g) x = f x - g x := rfl
#align continuous_affine_map.sub_apply ContinuousAffineMap.sub_apply

instance : Neg (P →ᴬ[R] W) :=
  { neg := fun f => { -(f : P →ᵃ[R] W) with cont := f.continuous.neg } }

@[norm_cast, simp]
theorem coe_neg (f : P →ᴬ[R] W) : ⇑(-f) = -f := rfl
#align continuous_affine_map.coe_neg ContinuousAffineMap.coe_neg

theorem neg_apply (f : P →ᴬ[R] W) (x : P) : (-f) x = -f x := rfl
#align continuous_affine_map.neg_apply ContinuousAffineMap.neg_apply

instance : AddCommGroup (P →ᴬ[R] W) :=
  coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ ↦ coe_smul _ _) fun _ _ ↦
    coe_smul _ _

instance [Monoid S] [DistribMulAction S W] [SMulCommClass R S W] [ContinuousConstSMul S W] :
    DistribMulAction S (P →ᴬ[R] W) :=
  Function.Injective.distribMulAction ⟨⟨fun f ↦ f.toAffineMap.toFun, rfl⟩, coe_add⟩ coe_injective
    coe_smul

instance [Semiring S] [Module S W] [SMulCommClass R S W] [ContinuousConstSMul S W] :
    Module S (P →ᴬ[R] W) :=
  Function.Injective.module S ⟨⟨fun f ↦ f.toAffineMap.toFun, rfl⟩, coe_add⟩ coe_injective coe_smul

end ModuleValuedMaps

end ContinuousAffineMap

namespace ContinuousLinearMap

variable {R V W : Type*} [Ring R]
variable [AddCommGroup V] [Module R V] [TopologicalSpace V]
variable [AddCommGroup W] [Module R W] [TopologicalSpace W]

/-- A continuous linear map can be regarded as a continuous affine map. -/
def toContinuousAffineMap (f : V →L[R] W) : V →ᴬ[R] W where
  toFun := f
  linear := f
  map_vadd' := by simp
  cont := f.cont
#align continuous_linear_map.to_continuous_affine_map ContinuousLinearMap.toContinuousAffineMap

@[simp]
theorem coe_toContinuousAffineMap (f : V →L[R] W) : ⇑f.toContinuousAffineMap = f := rfl
#align continuous_linear_map.coe_to_continuous_affine_map ContinuousLinearMap.coe_toContinuousAffineMap

@[simp]
theorem toContinuousAffineMap_map_zero (f : V →L[R] W) : f.toContinuousAffineMap 0 = 0 := by simp
#align continuous_linear_map.to_continuous_affine_map_map_zero ContinuousLinearMap.toContinuousAffineMap_map_zero

end ContinuousLinearMap
