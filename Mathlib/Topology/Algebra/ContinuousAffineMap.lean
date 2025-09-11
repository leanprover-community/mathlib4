/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Topology.Algebra.Module.LinearMap

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


/-- A continuous map of affine spaces -/
structure ContinuousAffineMap (R : Type*) {V W : Type*} (P Q : Type*) [Ring R] [AddCommGroup V]
  [Module R V] [TopologicalSpace P] [AddTorsor V P] [AddCommGroup W] [Module R W]
  [TopologicalSpace Q] [AddTorsor W Q] extends P →ᵃ[R] Q where
  cont : Continuous toFun

/-- A continuous map of affine spaces -/
notation:25 P " →ᴬ[" R "] " Q => ContinuousAffineMap R P Q

namespace ContinuousAffineMap

variable {R V W P Q : Type*} [Ring R]
variable [AddCommGroup V] [Module R V] [TopologicalSpace P] [AddTorsor V P]
variable [AddCommGroup W] [Module R W] [TopologicalSpace Q] [AddTorsor W Q]

instance : Coe (P →ᴬ[R] Q) (P →ᵃ[R] Q) :=
  ⟨toAffineMap⟩

attribute [coe] ContinuousAffineMap.toAffineMap

theorem toAffineMap_injective {f g : P →ᴬ[R] Q} (h : (f : P →ᵃ[R] Q) = (g : P →ᵃ[R] Q)) :
    f = g := by
  cases f
  cases g
  congr

instance : FunLike (P →ᴬ[R] Q) P Q where
  coe f := f.toAffineMap
  coe_injective' _ _ h := toAffineMap_injective <| DFunLike.coe_injective h

instance : ContinuousMapClass (P →ᴬ[R] Q) P Q where
  map_continuous := cont

theorem toFun_eq_coe (f : P →ᴬ[R] Q) : f.toFun = ⇑f := rfl

theorem coe_injective : @Function.Injective (P →ᴬ[R] Q) (P → Q) (⇑) :=
  DFunLike.coe_injective

@[ext]
theorem ext {f g : P →ᴬ[R] Q} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

theorem congr_fun {f g : P →ᴬ[R] Q} (h : f = g) (x : P) : f x = g x :=
  DFunLike.congr_fun h _

/-- Forgetting its algebraic properties, a continuous affine map is a continuous map. -/
def toContinuousMap (f : P →ᴬ[R] Q) : C(P, Q) :=
  ⟨f, f.cont⟩

instance : CoeHead (P →ᴬ[R] Q) C(P, Q) :=
  ⟨toContinuousMap⟩

@[simp]
theorem toContinuousMap_coe (f : P →ᴬ[R] Q) : f.toContinuousMap = ↑f := rfl

@[simp, norm_cast]
theorem coe_toAffineMap (f : P →ᴬ[R] Q) : ((f : P →ᵃ[R] Q) : P → Q) = f := rfl

@[simp, norm_cast]
theorem coe_to_continuousMap (f : P →ᴬ[R] Q) : ((f : C(P, Q)) : P → Q) = f := rfl

theorem to_continuousMap_injective {f g : P →ᴬ[R] Q} (h : (f : C(P, Q)) = (g : C(P, Q))) :
    f = g := by
  ext a
  exact ContinuousMap.congr_fun h a

@[norm_cast]
theorem coe_toAffineMap_mk (f : P →ᵃ[R] Q) (h) : ((⟨f, h⟩ : P →ᴬ[R] Q) : P →ᵃ[R] Q) = f := rfl

@[norm_cast]
theorem coe_continuousMap_mk (f : P →ᵃ[R] Q) (h) : ((⟨f, h⟩ : P →ᴬ[R] Q) : C(P, Q)) = ⟨f, h⟩ := rfl

@[simp]
theorem coe_mk (f : P →ᵃ[R] Q) (h) : ((⟨f, h⟩ : P →ᴬ[R] Q) : P → Q) = f := rfl

@[simp]
theorem mk_coe (f : P →ᴬ[R] Q) (h) : (⟨(f : P →ᵃ[R] Q), h⟩ : P →ᴬ[R] Q) = f := by
  ext
  rfl

@[continuity]
protected theorem continuous (f : P →ᴬ[R] Q) : Continuous f := f.2

variable (R P)

/-- The constant map as a continuous affine map -/
def const (q : Q) : P →ᴬ[R] Q :=
  { AffineMap.const R P q with cont := continuous_const }

@[simp]
theorem coe_const (q : Q) : ⇑(const R P q) = Function.const P q := rfl

noncomputable instance : Inhabited (P →ᴬ[R] Q) :=
  ⟨const R P <| Nonempty.some (by infer_instance : Nonempty Q)⟩

/-- The identity map as a continuous affine map -/
def id : P →ᴬ[R] P := { AffineMap.id R P with cont := continuous_id }

@[simp, norm_cast]
theorem coe_id : ⇑(id R P) = _root_.id := rfl

variable {R P} {W₂ Q₂ W₃ Q₃ : Type*}
variable [AddCommGroup W₂] [Module R W₂] [TopologicalSpace Q₂] [AddTorsor W₂ Q₂]

/-- The composition of continuous affine maps as a continuous affine map -/
def comp (f : Q →ᴬ[R] Q₂) (g : P →ᴬ[R] Q) : P →ᴬ[R] Q₂ :=
  { (f : Q →ᵃ[R] Q₂).comp (g : P →ᵃ[R] Q) with cont := f.cont.comp g.cont }

@[simp, norm_cast]
theorem coe_comp (f : Q →ᴬ[R] Q₂) (g : P →ᴬ[R] Q) : ⇑(f.comp g) = f ∘ g := rfl

theorem comp_apply (f : Q →ᴬ[R] Q₂) (g : P →ᴬ[R] Q) (p : P) : f.comp g p = f (g p) := rfl

@[simp]
theorem comp_id (f : P →ᴬ[R] Q) : f.comp (id R P) = f :=
  ext fun _ => rfl

@[simp]
theorem id_comp (f : P →ᴬ[R] Q) : (id R Q).comp f = f :=
  ext fun _ => rfl

/-- The continuous affine map sending `0` to `p₀` and `1` to `p₁` -/
def lineMap (p₀ p₁ : P) [TopologicalSpace R] [TopologicalSpace V]
    [ContinuousSMul R V] [ContinuousVAdd V P] : R →ᴬ[R] P where
  toAffineMap := AffineMap.lineMap p₀ p₁
  cont := (continuous_id.smul continuous_const).vadd continuous_const

@[simp] lemma lineMap_toAffineMap (p₀ p₁ : P) [TopologicalSpace R] [TopologicalSpace V]
    [ContinuousSMul R V] [ContinuousVAdd V P] :
    (lineMap p₀ p₁).toAffineMap = AffineMap.lineMap (k := R) p₀ p₁ := rfl

lemma coe_lineMap_eq (p₀ p₁ : P) [TopologicalSpace R] [TopologicalSpace V]
    [ContinuousSMul R V] [ContinuousVAdd V P] :
    ⇑(ContinuousAffineMap.lineMap p₀ p₁) = ⇑(AffineMap.lineMap (k := R) p₀ p₁) := rfl

section ModuleValuedMaps

variable {S : Type*}
variable [TopologicalSpace W]

instance : Zero (P →ᴬ[R] W) :=
  ⟨ContinuousAffineMap.const R P 0⟩

@[norm_cast, simp]
theorem coe_zero : ((0 : P →ᴬ[R] W) : P → W) = 0 := rfl

theorem zero_apply (x : P) : (0 : P →ᴬ[R] W) x = 0 := rfl

section MulAction

variable [Monoid S] [DistribMulAction S W] [SMulCommClass R S W]
variable [ContinuousConstSMul S W]

instance : SMul S (P →ᴬ[R] W) where
  smul t f := { t • (f : P →ᵃ[R] W) with cont := f.continuous.const_smul t }

@[norm_cast, simp]
theorem coe_smul (t : S) (f : P →ᴬ[R] W) : ⇑(t • f) = t • ⇑f := rfl

theorem smul_apply (t : S) (f : P →ᴬ[R] W) (x : P) : (t • f) x = t • f x := rfl

instance [DistribMulAction Sᵐᵒᵖ W] [IsCentralScalar S W] : IsCentralScalar S (P →ᴬ[R] W) where
  op_smul_eq_smul _ _ := ext fun _ ↦ op_smul_eq_smul _ _

instance : MulAction S (P →ᴬ[R] W) :=
  Function.Injective.mulAction _ coe_injective coe_smul

end MulAction

variable [IsTopologicalAddGroup W]

instance : Add (P →ᴬ[R] W) where
  add f g := { (f : P →ᵃ[R] W) + (g : P →ᵃ[R] W) with cont := f.continuous.add g.continuous }

@[norm_cast, simp]
theorem coe_add (f g : P →ᴬ[R] W) : ⇑(f + g) = f + g := rfl

theorem add_apply (f g : P →ᴬ[R] W) (x : P) : (f + g) x = f x + g x := rfl

instance : Sub (P →ᴬ[R] W) where
  sub f g := { (f : P →ᵃ[R] W) - (g : P →ᵃ[R] W) with cont := f.continuous.sub g.continuous }

@[norm_cast, simp]
theorem coe_sub (f g : P →ᴬ[R] W) : ⇑(f - g) = f - g := rfl

theorem sub_apply (f g : P →ᴬ[R] W) (x : P) : (f - g) x = f x - g x := rfl

instance : Neg (P →ᴬ[R] W) :=
  { neg := fun f => { -(f : P →ᵃ[R] W) with cont := f.continuous.neg } }

@[norm_cast, simp]
theorem coe_neg (f : P →ᴬ[R] W) : ⇑(-f) = -f := rfl

theorem neg_apply (f : P →ᴬ[R] W) (x : P) : (-f) x = -f x := rfl

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

@[simp]
theorem coe_toContinuousAffineMap (f : V →L[R] W) : ⇑f.toContinuousAffineMap = f := rfl

@[simp]
theorem toContinuousAffineMap_map_zero (f : V →L[R] W) : f.toContinuousAffineMap 0 = 0 := by simp

end ContinuousLinearMap
