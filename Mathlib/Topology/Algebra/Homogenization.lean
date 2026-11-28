/-
Copyright (c) 2026 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Homogenization
public import Mathlib.Topology.Algebra.ContinuousAffineMap.Topology

/-!
# Topology of the homogenization

This file defines a topological vector space structure on the homogenization of a topological affine
space `P` over a topological ring `R`. This topology has the universal property that every
continuous affine map on `P` taking values in a topological vector space extends uniquely to a
continuous linear map from `Homogenization R P`.
-/

@[expose] public noncomputable section

open Topology

namespace Homogenization

section General

variable
  {R : Type*} [Ring R] [TopologicalSpace R]
  {V P : Type*} [AddCommGroup V] [Module R V] [AddTorsor V P] [TopologicalSpace P]
  {V₁ P₁ : Type*} [AddCommGroup V₁] [Module R V₁] [AddTorsor V₁ P₁] [TopologicalSpace P₁]
  {V₂ P₂ : Type*} [AddCommGroup V₂] [Module R V₂] [AddTorsor V₂ P₂] [TopologicalSpace P₂]
  {V₃ P₃ : Type*} [AddCommGroup V₃] [Module R V₃] [AddTorsor V₃ P₃] [TopologicalSpace P₃]
  {W : Type*} [AddCommGroup W] [Module R W]
  [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul R W]

@[no_expose]
instance : TopologicalSpace (Homogenization R P) :=
  sInf {_t : TopologicalSpace (Homogenization R P) |
    IsTopologicalAddGroup (Homogenization R P) ∧ ContinuousSMul R (Homogenization R P) ∧
    Continuous (ofPoint (R := R) (P := P))}

instance : IsTopologicalAddGroup (Homogenization R P) :=
  isTopologicalAddGroup_sInf fun _ ⟨h, _, _⟩ => h

instance : ContinuousSMul R (Homogenization R P) :=
  continuousSMul_sInf fun _ ⟨_, h, _⟩ => h

@[fun_prop]
theorem continuous_ofPoint : Continuous (ofPoint (R := R) (P := P)) :=
  continuous_sInf_rng.mpr fun _ ⟨_, _, h⟩ => h

theorem continuous_dom_iff {f : Homogenization R P →ₗ[R] W} :
    Continuous f ↔ Continuous (f ∘ ofPoint) where
  mp hf := hf.comp continuous_ofPoint
  mpr h :=
    continuous_sInf_dom (t := .induced f inferInstance)
      ⟨isTopologicalAddGroup_induced _, continuousSMul_induced _, continuous_induced_rng.mpr h⟩
      continuous_induced_dom

section SMul

variable
  {S : Type*} [Semiring S] [Module S R] [Module S V] [IsScalarTower S R V] [IsScalarTower S R R]

instance : ContinuousConstSMul S (Homogenization R P) :=
  IsScalarTower.continuousConstSMul S R _

instance [TopologicalSpace S] [ContinuousSMul S R] : ContinuousSMul S (Homogenization R P) :=
  IsScalarTower.continuousSMul R

end SMul

/-- Continuous version of `Homogenization.ofPoint`. -/
def ofPointA : P →ᴬ[R] Homogenization R P where
  __ := ofPoint
  cont := continuous_ofPoint

@[simp]
theorem coe_ofPointA : ⇑(ofPointA (R := R) (P := P)) = ofPoint :=
  rfl

@[simp]
theorem toAffineMap_ofPointA : (ofPointA (R := R) (P := P)).toAffineMap = ofPoint :=
  rfl

@[fun_prop]
theorem continuous_lift {f : P →ᵃ[R] W} (hf : Continuous f) : Continuous (lift f) := by
  simpa only [continuous_dom_iff, Function.comp_def, lift_apply_ofPoint]

/-- A continuous affine map on `P` taking values in a topological vector space extends uniquely to a
continuous linear map on `Homogenization R P`. -/
def contLift : (P →ᴬ[R] W) ≃+ (Homogenization R P →L[R] W) where
  toFun f := ⟨lift f, continuous_lift (map_continuous f)⟩
  invFun f := f.toContinuousAffineMap.comp ofPointA
  left_inv _ := by ext; simp
  right_inv _ := hom_ext <| by simp
  map_add' _ _ := hom_ext <| by simp

@[simp]
theorem coe_contLift (f : P →ᴬ[R] W) : ⇑(contLift f) = lift f :=
  rfl

@[simp]
theorem toLinearMap_contLift (f : P →ᴬ[R] W) : (contLift f).toLinearMap = lift f :=
  rfl

@[simp]
theorem coe_contLift_symm (f : Homogenization R P →L[R] W) :
    ⇑(contLift.symm f) = lift.symm f.toLinearMap :=
  rfl

theorem contLift_symm_apply (f : Homogenization R P →L[R] W) (p : P) :
    contLift.symm f p = f (ofPoint p) :=
  rfl

theorem contLift_symm_id : (contLift (R := R) (P := P)).symm (.id ..) = ofPointA :=
  rfl

theorem contLift_ofPointA : contLift (R := R) (P := P) ofPointA = .id .. :=
  hom_ext <| by simp

section weight

variable [IsTopologicalRing R]

@[fun_prop]
theorem continuous_weight : Continuous (weight (R := R) (P := P)) :=
  continuous_lift continuous_const

/-- Continuous version of `Homogenization.weight`. -/
def weightL : Homogenization R P →L[R] R where
  __ := weight

@[simp]
theorem coe_weightL : ⇑(weightL (R := R) (P := P)) = weight :=
  rfl

@[simp]
theorem toLinearMap_weightL : (weightL (R := R) (P := P)).toLinearMap = weight :=
  rfl

end weight

section ofVector

variable [TopologicalSpace V] [IsTopologicalAddTorsor P]

@[fun_prop]
theorem continuous_ofVector :
    Continuous (ofVector (R := R) (P := P)) :=
  AffineMap.continuous_linear_iff.mpr continuous_ofPoint

/-- Continuous version of `Homogenization.ofVector`. -/
def ofVectorL : V →L[R] Homogenization R P :=
  ofPointA.contLinear

@[simp]
theorem coe_ofVectorL : ⇑(ofVectorL (R := R) (P := P)) = ofVector :=
  rfl

@[simp]
theorem toLinearMap_ofVectorL : (ofVectorL (R := R) (P := P)).toLinearMap = ofVector :=
  rfl

@[simp]
theorem ofPointA_contLinear : (ofPointA (R := R) (P := P)).contLinear = ofVectorL :=
  rfl

@[simp]
theorem contLift_symm_contLinear (f : Homogenization R P →L[R] W) :
    (contLift.symm f).contLinear = f ∘L ofVectorL :=
  rfl

variable [ContinuousSMul R V]

theorem isEmbedding_ofVector : IsEmbedding (ofVector (R := R) (P := P)) :=
  have ⟨p⟩ : Nonempty P := inferInstance
  have := IsTopologicalAddTorsor.to_isTopologicalAddGroup V P
  .of_leftInverse (f := lift (AffineEquiv.vaddConst R p).symm) (fun q => by simp)
    (continuous_lift <| continuous_id.vsub continuous_const)
    continuous_ofVector

theorem isEmbedding_ofPoint : IsEmbedding (ofPoint (R := R) (P := P)) :=
  AffineMap.isEmbedding_linear_iff.mp isEmbedding_ofVector

variable [IsTopologicalRing R] [T1Space R]

theorem isClosedEmbedding_ofVector : IsClosedEmbedding (ofVector (R := R) (P := P)) where
  __ := isEmbedding_ofVector
  isClosed_range := by
    simp_rw [Set.range, eq_comm, ← weight_eq_zero_iff]
    exact isClosed_singleton.preimage continuous_weight

theorem isClosedEmbedding_ofPoint : IsClosedEmbedding (ofPoint (R := R) (P := P)) :=
  AffineMap.isClosedEmbedding_linear_iff.mp isClosedEmbedding_ofVector

end ofVector

@[fun_prop]
theorem continuous_map {f : P₁ →ᵃ[R] P₂} (hf : Continuous f) : Continuous (map f) :=
  continuous_lift <| continuous_ofPoint.comp hf

/-- A continuous affine map between topological affine spaces extends to a continuous linear map
between their homogenizations. -/
def contMap (f : P₁ →ᴬ[R] P₂) : Homogenization R P₁ →L[R] Homogenization R P₂ where
  __ := map f
  cont := continuous_map (map_continuous f)

@[simp]
theorem coe_contMap (f : P₁ →ᴬ[R] P₂) : ⇑(contMap f) = map f :=
  rfl

@[simp]
theorem toLinearMap_contMap (f : P₁ →ᴬ[R] P₂) : (contMap f).toLinearMap = map f :=
  rfl

@[simp]
theorem contMap_id : contMap (.id R P) = .id .. :=
  hom_ext <| by simp

theorem contMap_comp (f : P₂ →ᴬ[R] P₃) (g : P₁ →ᴬ[R] P₂) :
    contMap (f.comp g) = contMap f ∘L contMap g :=
  hom_ext <| by simp

theorem contLift_comp (f : P₂ →ᴬ[R] W) (g : P₁ →ᴬ[R] P₂) :
    contLift (f.comp g) = contLift f ∘L contMap g :=
  hom_ext <| by simp

/-- An isomorphism of topological affine spaces extends to an isomorphism of topological vector
spaces between their homogenizations. -/
def contCongr (f : P₁ ≃ᴬ[R] P₂) : Homogenization R P₁ ≃L[R] Homogenization R P₂ where
  __ := congr f.toAffineEquiv
  continuous_toFun := continuous_map (map_continuous f)
  continuous_invFun := continuous_map (map_continuous f.symm)

@[simp]
theorem coe_contCongr (f : P₁ ≃ᴬ[R] P₂) : ⇑(contCongr f) = map f :=
  rfl

@[simp]
theorem toLinearMap_contCongr (f : P₁ ≃ᴬ[R] P₂) : contCongr f = contMap f.toContinuousAffineMap :=
  rfl

@[simp]
theorem toLinearEquiv_contCongr (f : P₁ ≃ᴬ[R] P₂) : contCongr f = congr f.toAffineEquiv :=
  rfl

@[simp]
theorem contCongr_symm (f : P₁ ≃ᴬ[R] P₂) : (contCongr f).symm = contCongr f.symm :=
  rfl

@[simp]
theorem contCongr_refl : contCongr (.refl R P) = .refl .. :=
  hom_ext <| by simp

@[simp]
theorem contCongr_trans (f : P₁ ≃ᴬ[R] P₂) (g : P₂ ≃ᴬ[R] P₃) :
    contCongr (f.trans g) = (contCongr f).trans (contCongr g) :=
  hom_ext <| by simp

section toProdL

variable [TopologicalSpace V] [IsTopologicalAddGroup V]

@[fun_prop]
theorem continuous_toProd_symm : Continuous (toProd (R := R) (V := V)).symm := by
  eta_expand
  simp only [toProd_symm_apply]
  fun_prop

variable [ContinuousSMul R V] [IsTopologicalRing R]

@[fun_prop]
theorem continuous_toProd : Continuous (toProd (R := R) (V := V)) :=
  .prodMk (continuous_lift continuous_id) continuous_weight

/-- Continuous version of `Homogenization.toProd`. -/
def toProdL : Homogenization R V ≃L[R] V × R where
  __ := toProd

@[simp]
theorem coe_toProdL : ⇑(toProdL (R := R) (V := V)) = toProd :=
  rfl

@[simp]
theorem coe_toProdL_symm : ⇑(toProdL (R := R) (V := V)).symm = toProd.symm :=
  rfl

@[simp]
theorem toLinearEquiv_toProdL :
    toProdL (R := R) (V := V) = toProd (R := R) (V := V) :=
  rfl

end toProdL

end General

section NontriviallyNormedField

variable
  {R : Type*} [NontriviallyNormedField R]
  {V P : Type*} [AddCommGroup V] [Module R V] [AddTorsor V P] [TopologicalSpace P]
  [TopologicalSpace V] [ContinuousSMul R V] [IsTopologicalAddTorsor P]
  {V₁ P₁ : Type*} [AddCommGroup V₁] [Module R V₁] [AddTorsor V₁ P₁] [TopologicalSpace P₁]
  [TopologicalSpace V₁] [ContinuousSMul R V₁] [IsTopologicalAddTorsor P₁]
  {V₂ P₂ : Type*} [AddCommGroup V₂] [Module R V₂] [AddTorsor V₂ P₂] [TopologicalSpace P₂]
  [TopologicalSpace V₂] [ContinuousSMul R V₂] [IsTopologicalAddTorsor P₂]
  {W : Type*} [AddCommGroup W] [Module R W]
  [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul R W]

@[fun_prop]
theorem continuous_contLift : Continuous (contLift (R := R) (P := P) (W := W)) := by
  obtain ⟨p⟩ : Nonempty P := inferInstance
  have := IsTopologicalAddTorsor.to_isTopologicalAddGroup V P
  conv =>
    enter [1, f]
    equals toProdL.toContinuousLinearMap ∘L contMap (ContinuousAffineEquiv.vaddConst R p).symm
        |>.precomp _ <| .coprodEquivL R (f.contLinear, .toSpanSingletonCLE (f p)) =>
      apply hom_ext; simp
  fun_prop

omit [ContinuousSMul R V] in
@[fun_prop]
theorem continuous_contLift_symm : Continuous (contLift (R := R) (P := P) (W := W)).symm :=
  ofPointA.continuous_precomp.comp ContinuousLinearMap.continuous_toContinuousAffineMap

section contLiftL

variable (S : Type*) [Semiring S] [Module S W] [ContinuousConstSMul S W] [SMulCommClass R S W]

/-- `Homogenization.contLift` as a continuous linear map. -/
def contLiftL : (P →ᴬ[R] W) ≃L[S] (Homogenization R P →L[R] W) where
  __ := contLift
  map_add' := by simp
  map_smul' _ _ := hom_ext <| by simp

@[simp]
theorem coe_contLiftL : ⇑(contLiftL (R := R) (P := P) (W := W) S) = contLift :=
  rfl

@[simp]
theorem coe_contLiftL_symm : ⇑(contLiftL (R := R) (P := P) (W := W) S).symm = contLift.symm :=
  rfl

end contLiftL

@[fun_prop]
theorem continuous_contMap : Continuous (contMap (R := R) (P₁ := P₁) (P₂ := P₂)) :=
  continuous_contLift.comp ofPointA.continuous_postcomp

section contMapA

variable
  (S : Type*) [Ring S] [Module S R] [Module S V₂] [IsScalarTower S R V₂] [IsScalarTower S R R]
  [IsTopologicalAddGroup V₂] [ContinuousConstSMul S V₂] [SMulCommClass R S R] [SMulCommClass R S V₂]

/-- `Homogenization.contMap` as a continuous affine map. -/
def contMapA : (P₁ →ᴬ[R] P₂) →ᴬ[S] (Homogenization R P₁ →L[R] Homogenization R P₂) where
  toFun := contMap
  cont := continuous_contMap
  linear :=
    { toFun f := contLift (ofVectorL.toContinuousAffineMap.comp f)
      map_add' _ _ := hom_ext <| by simp
      map_smul' _ _ := hom_ext <| by simp }
  map_vadd' _ _ := hom_ext <| by simp

@[simp]
theorem coe_contMapA : ⇑(contMapA (R := R) (P₁ := P₁) (P₂ := P₂) S) = contMap :=
  rfl

end contMapA

end NontriviallyNormedField

end Homogenization
