/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Affine

/-!
# Continuous affine maps.

This file defines a type of bundled continuous affine maps.

## Main definitions:

* `ContinuousAffineMap`

## Notation:

We introduce the notation `P →ᴬ[R] Q` for `ContinuousAffineMap R P Q` (not to be confused with the
notation `A →A[R] B` for `ContinuousAlgHom`). Note that this is parallel to the notation `E →L[R] F`
for `ContinuousLinearMap R E F`.
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

section IsTopologicalAddTorsor

variable [TopologicalSpace V] [IsTopologicalAddTorsor P]
variable [TopologicalSpace W] [IsTopologicalAddTorsor Q]
variable [TopologicalSpace W₂] [IsTopologicalAddTorsor Q₂]

/-- The linear map underlying a continuous affine map is continuous. -/
def contLinear (f : P →ᴬ[R] Q) : V →L[R] W :=
  { f.linear with
    toFun := f.linear
    cont := by rw [AffineMap.continuous_linear_iff]; exact f.cont }

@[simp]
theorem coe_contLinear (f : P →ᴬ[R] Q) : (f.contLinear : V → W) = f.linear :=
  rfl

@[simp]
theorem coe_contLinear_eq_linear (f : P →ᴬ[R] Q) :
    (f.contLinear : V →ₗ[R] W) = (f : P →ᵃ[R] Q).linear :=
  rfl

@[simp]
theorem coe_mk_contLinear_eq_linear (f : P →ᵃ[R] Q) (h) :
    ((⟨f, h⟩ : P →ᴬ[R] Q).contLinear : V → W) = f.linear :=
  rfl

@[deprecated (since := "2025-09-17")]
alias coe_mk_const_linear_eq_linear := coe_mk_contLinear_eq_linear

theorem coe_linear_eq_coe_contLinear (f : P →ᴬ[R] Q) :
    ((f : P →ᵃ[R] Q).linear : V → W) = (⇑f.contLinear : V → W) :=
  rfl

@[simp]
theorem comp_contLinear (f : P →ᴬ[R] Q) (g : Q →ᴬ[R] Q₂) :
    (g.comp f).contLinear = g.contLinear.comp f.contLinear :=
  rfl

@[simp]
theorem map_vadd (f : P →ᴬ[R] Q) (p : P) (v : V) : f (v +ᵥ p) = f.contLinear v +ᵥ f p :=
  f.map_vadd' p v

@[simp]
theorem contLinear_map_vsub (f : P →ᴬ[R] Q) (p₁ p₂ : P) : f.contLinear (p₁ -ᵥ p₂) = f p₁ -ᵥ f p₂ :=
  f.toAffineMap.linearMap_vsub p₁ p₂

@[simp]
theorem const_contLinear (q : Q) : (const R P q).contLinear = 0 :=
  rfl

theorem contLinear_eq_zero_iff_exists_const (f : P →ᴬ[R] Q) :
    f.contLinear = 0 ↔ ∃ q, f = const R P q := by
  have h₁ : f.contLinear = 0 ↔ (f : P →ᵃ[R] Q).linear = 0 := by
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> ext
    · rw [← coe_contLinear_eq_linear, h]; rfl
    · rw [← coe_linear_eq_coe_contLinear, h]; rfl
  have h₂ : ∀ q : Q, f = const R P q ↔ (f : P →ᵃ[R] Q) = AffineMap.const R P q := by
    intro q
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> ext
    · rw [h]; rfl
    · rw [← coe_toAffineMap, h, AffineMap.const_apply, coe_const, Function.const_apply]
  simp_rw [h₁, h₂]
  exact (f : P →ᵃ[R] Q).linear_eq_zero_iff_exists_const

end IsTopologicalAddTorsor

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

variable [TopologicalSpace V] [IsTopologicalAddTorsor P] [IsTopologicalAddGroup W]

@[simp]
theorem smul_contLinear (t : S) (f : P →ᴬ[R] W) : (t • f).contLinear = t • f.contLinear :=
  rfl

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

variable [TopologicalSpace V] [IsTopologicalAddTorsor P]

@[simp]
theorem zero_contLinear : (0 : P →ᴬ[R] W).contLinear = 0 :=
  rfl

@[simp]
theorem add_contLinear (f g : P →ᴬ[R] W) : (f + g).contLinear = f.contLinear + g.contLinear :=
  rfl

@[simp]
theorem sub_contLinear (f g : P →ᴬ[R] W) : (f - g).contLinear = f.contLinear - g.contLinear :=
  rfl

@[simp]
theorem neg_contLinear (f : P →ᴬ[R] W) : (-f).contLinear = -f.contLinear :=
  rfl

end ModuleValuedMaps

section

variable [TopologicalSpace W] [IsTopologicalAddGroup W] [IsTopologicalAddTorsor Q]

/-- The space of continuous affine maps from `P` to `Q` is an affine space over the space of
continuous affine maps from `P` to `W`. -/
instance : AddTorsor (P →ᴬ[R] W) (P →ᴬ[R] Q) where
  vadd f g := { __ := f.toAffineMap +ᵥ g.toAffineMap, cont := f.cont.vadd g.cont }
  zero_vadd _ := ext fun _ ↦ zero_vadd _ _
  add_vadd _ _ _ := ext fun _ ↦ add_vadd _ _ _
  vsub f g := { __ := f.toAffineMap -ᵥ g.toAffineMap, cont := f.cont.vsub g.cont }
  vsub_vadd' _ _ := ext fun _ ↦ vsub_vadd _ _
  vadd_vsub' _ _ := ext fun _ ↦ vadd_vsub _ _

@[simp] lemma vadd_apply (f : P →ᴬ[R] W) (g : P →ᴬ[R] Q) (p : P) : (f +ᵥ g) p = f p +ᵥ g p :=
  rfl

@[simp] lemma vsub_apply (f g : P →ᴬ[R] Q) (p : P) : (f -ᵥ g) p = f p -ᵥ g p :=
  rfl

@[simp] lemma vadd_toAffineMap (f : P →ᴬ[R] W) (g : P →ᴬ[R] Q) :
    (f +ᵥ g).toAffineMap = f.toAffineMap +ᵥ g.toAffineMap :=
  rfl

@[simp] lemma vsub_toAffineMap (f g : P →ᴬ[R] Q) :
    (f -ᵥ g).toAffineMap = f.toAffineMap -ᵥ g.toAffineMap :=
  rfl

variable [TopologicalSpace V] [IsTopologicalAddTorsor P]

@[simp] lemma vadd_contLinear (f : P →ᴬ[R] W) (g : P →ᴬ[R] Q) :
    (f +ᵥ g).contLinear = f.contLinear + g.contLinear :=
  rfl

@[simp] lemma vsub_contLinear (f g : P →ᴬ[R] Q) :
    (f -ᵥ g).contLinear = f.contLinear - g.contLinear :=
  rfl

end

section Prod

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁] [TopologicalSpace P₁]
  [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂] [TopologicalSpace P₂]
  [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃] [TopologicalSpace P₃]
  [AddCommGroup V₄] [Module k V₄] [AddTorsor V₄ P₄] [TopologicalSpace P₄]

/-- The product of two continuous affine maps is a continuous affine map. -/
@[simps toAffineMap]
def prod (f : P₁ →ᴬ[k] P₂) (g : P₁ →ᴬ[k] P₃) : P₁ →ᴬ[k] P₂ × P₃ where
  __ := AffineMap.prod f g
  cont := by eta_expand; dsimp; fun_prop

theorem coe_prod (f : P₁ →ᴬ[k] P₂) (g : P₁ →ᴬ[k] P₃) : prod f g = Pi.prod f g :=
  rfl

@[simp]
theorem prod_apply (f : P₁ →ᴬ[k] P₂) (g : P₁ →ᴬ[k] P₃) (p : P₁) : prod f g p = (f p, g p) :=
  rfl

/-- `Prod.map` of two continuous affine maps. -/
@[simps toAffineMap]
def prodMap (f : P₁ →ᴬ[k] P₂) (g : P₃ →ᴬ[k] P₄) : P₁ × P₃ →ᴬ[k] P₂ × P₄ where
  __ := AffineMap.prodMap f g
  cont := by eta_expand; dsimp; fun_prop

theorem coe_prodMap (f : P₁ →ᴬ[k] P₂) (g : P₃ →ᴬ[k] P₄) : ⇑(f.prodMap g) = Prod.map f g :=
  rfl

@[simp]
theorem prodMap_apply (f : P₁ →ᴬ[k] P₂) (g : P₃ →ᴬ[k] P₄) (x) : f.prodMap g x = (f x.1, g x.2) :=
  rfl

variable
  [TopologicalSpace V₁] [IsTopologicalAddTorsor P₁]
  [TopologicalSpace V₂] [IsTopologicalAddTorsor P₂]
  [TopologicalSpace V₃] [IsTopologicalAddTorsor P₃]
  [TopologicalSpace V₄] [IsTopologicalAddTorsor P₄]

@[simp]
theorem prod_contLinear (f : P₁ →ᴬ[k] P₂) (g : P₁ →ᴬ[k] P₃) :
    (f.prod g).contLinear = f.contLinear.prod g.contLinear :=
  rfl

@[simp]
theorem prodMap_contLinear (f : P₁ →ᴬ[k] P₂) (g : P₃ →ᴬ[k] P₄) :
    (f.prodMap g).contLinear = f.contLinear.prodMap g.contLinear :=
  rfl

end Prod

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

variable [IsTopologicalAddGroup V] [IsTopologicalAddGroup W]

@[simp]
theorem toContinuousAffineMap_contLinear (f : V →L[R] W) : f.toContinuousAffineMap.contLinear = f :=
  rfl

@[deprecated (since := "2025-09-23")]
alias _root_.ContinuousAffineMap.to_affine_map_contLinear := toContinuousAffineMap_contLinear

theorem _root_.ContinuousAffineMap.decomp (f : V →ᴬ[R] W) :
    (f : V → W) = f.contLinear + Function.const V (f 0) := by
  rcases f with ⟨f, h⟩
  rw [ContinuousAffineMap.coe_mk_contLinear_eq_linear, ContinuousAffineMap.coe_mk, f.decomp,
    Pi.add_apply, LinearMap.map_zero, zero_add, ← Function.const_def]

end ContinuousLinearMap
