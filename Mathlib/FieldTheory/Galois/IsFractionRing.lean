/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu, Zixun Guo
-/
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Tactic.LiftLets

/-!
# Galois extension is transfered between two pairs of fraction rings

## Main results
  * `IsGalois.of_isGalois_isFractionRing`: Galois extension is transfered between
      two pairs of rings with `IsFractionRing` instances.
  * `IsGalois.iff_isGalois_isFractionRing`: Galois extension is equivalent between
      two pairs of rings with `IsFractionRing` instances.
  * `IsGalois.isFractionRing_of_isGalois_fractionRing`: Galois extension is transfered between
      two pairs of ring with `IsGalois` instances and `FractionRing`.
  * `IsGalois.fractionRing_of_isGalois_isFractionRing`: Galois extension is transfered between
      two pairs of  with `FractionRing` and ring with `IsGalois` instances.

-/

/-
  The aim is to prove a commutative diagram:
  ----------------
  |               |
  \/             \/
  L  <--- B ---> L'
  /\      /\     /\
  |       |      |
  |       |      |
  K  <--- A ---> K'
  /\             /\
  |               |
  -----------------
  in which K <-> K' and L <-> L' come from canonical isomorphisms
  between two fraction rings of A and B, respectively.
  The only path to prove is :
  K -> L -> L' = K -> K' -> L'
  which induced by the fact that they are both lifting functions of A -> L'
-/
#check Equiv.algEquiv
section
variable (A B K L K' L' : Type*)
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B] [NoZeroSMulDivisors A B]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Field K'] [Field L']
    [Algebra A K'] [IsFractionRing A K']
    [Algebra B L'] [IsFractionRing B L']
    [Algebra K' L'] [Algebra A L']
    [IsScalarTower A B L'] [IsScalarTower A K' L']

private noncomputable def KK' := (FractionRing.algEquiv A K).symm.trans (FractionRing.algEquiv A K')
private noncomputable def LL' := (FractionRing.algEquiv B L).symm.trans (FractionRing.algEquiv B L')

private noncomputable def alg_KL' : Algebra K L' := Algebra.compHom L' (KK' A K K').toRingHom

/- following directly from definition, there is a scalar tower K -> K' -> L'
-/
private def scalar_tower_K_K'_L':
    let _ := alg_KL' A K K' L'
    let KK' := KK' A K K'
    let _ := RingHom.toAlgebra KK'.toRingHom
    IsScalarTower K K' L' :=
  let _ := alg_KL' A K K' L'
  let KK' := KK' A K K'
  let _ := RingHom.toAlgebra KK'.toRingHom
  IsScalarTower.of_compHom _ _ _


private def scalar_tower_K_L_L':
    let _ := alg_KL' A K K' L'
    let LL' := LL' B L L'
    let _ := RingHom.toAlgebra LL'.toRingHom
    IsScalarTower K L L' := by
  let _ := alg_KL' A K K' L'
  let LL' := LL' B L L'
  let KK' := KK' A K K'
  let _ := RingHom.toAlgebra LL'.toRingHom
  let _ := RingHom.toAlgebra KK'.toRingHom
  let _KK'L' := scalar_tower_K_K'_L' A K K' L'
  simp at _KK'L'
  simp only at *
  apply IsScalarTower.of_algebraMap_eq
  intro x
  rw [<-Function.comp_apply (x := x) (g := algebraMap K L) (f := algebraMap L L')]
  apply congrFun
  rw [<-RingHom.coe_comp, DFunLike.coe_fn_eq]
  apply IsFractionRing.lift_unique' (A := A) (g := algebraMap A L')
  · rw [IsScalarTower.algebraMap_eq A B L', RingHom.coe_comp]
    apply Function.Injective.comp <;> apply NoZeroSMulDivisors.algebraMap_injective
  · intro x
    rw [@IsScalarTower.algebraMap_eq K K' L' _ _ _ _ _ _ _KK'L']
    simp only [RingHom.algebraMap_toAlgebra, AlgEquiv.toRingEquiv_eq_coe,
      RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp, RingHom.coe_coe,
      Function.comp_apply, AlgEquiv.commutes]
    exact Eq.symm (IsScalarTower.algebraMap_apply _ _ _ _)
  · intro x
    rw [IsScalarTower.algebraMap_eq A B L']
    have : algebraMap B L' = (algebraMap L L').comp (algebraMap B L) := by
      ext x
      simp only [RingHom.algebraMap_toAlgebra, AlgEquiv.toRingEquiv_eq_coe,
        RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp,
        RingHom.coe_coe, Function.comp_apply, AlgEquiv.commutes]
    rw [this]
    simp only [RingHom.algebraMap_toAlgebra, RingHom.coe_comp,
        RingHom.coe_coe, Function.comp_apply]
    rw [<-IsScalarTower.algebraMap_apply A K L]
    rw [<-IsScalarTower.algebraMap_apply A B L]

end


/- Galois extension is transfered between two pairs of fraction rings
-/
theorem IsGalois.of_isGalois_isFractionRing
    (A B K L K' L' : Type*)
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B] [NoZeroSMulDivisors A B]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Field K'] [Field L']
    [Algebra A K'] [IsFractionRing A K']
    [Algebra B L'] [IsFractionRing B L']
    [Algebra K' L'] [Algebra A L']
    [IsScalarTower A B L'] [IsScalarTower A K' L']
    [IsGalois K L]: IsGalois K' L' := by
  let _ := alg_KL' A K K' L'
  let LL' := LL' B L L'
  let KK' := KK' A K K'
  let _ := RingHom.toAlgebra LL'.toRingHom
  let _ := RingHom.toAlgebra KK'.toRingHom
  let KK'L' := scalar_tower_K_K'_L' A K K' L'
  let KLL' := scalar_tower_K_L_L' A B K L K' L'
  simp at KK'L'
  simp at KLL'
  haveI : IsGalois K L' := by
    apply IsGalois.of_algEquiv (E := L)
    apply AlgEquiv.ofRingEquiv (f := LL'.toRingEquiv)
    rw [@IsScalarTower.algebraMap_eq K L L' _ _ _ _ _ _ KLL']
    exact fun _ => rfl
  exact @IsGalois.tower_top_of_isGalois K K' L' _ _ _ _ _ _ KK'L' _

theorem IsGalois.iff_isGalois_isFractionRing
    (A B K L K' L' : Type*)
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B] [NoZeroSMulDivisors A B]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Field K'] [Field L']
    [Algebra A K'] [IsFractionRing A K']
    [Algebra B L'] [IsFractionRing B L']
    [Algebra K' L'] [Algebra A L']
    [IsScalarTower A B L'] [IsScalarTower A K' L']:
    IsGalois K L ↔ IsGalois K' L' :=
  Iff.intro
    (fun _ => IsGalois.of_isGalois_isFractionRing A B K L K' L')
    (fun _ => IsGalois.of_isGalois_isFractionRing A B K' L' K L)

attribute [local instance] FractionRing.liftAlgebra

theorem IsGalois.isFractionRing_of_isGalois_fractionRing
    (A B K L : Type*)
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B] [NoZeroSMulDivisors A B]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsGalois (FractionRing A) (FractionRing B)]: IsGalois K L :=
  IsGalois.of_isGalois_isFractionRing A B (FractionRing A) (FractionRing B) K L


theorem IsGalois.fractionRing_of_isGalois_isFractionRing
    (A B K L : Type*)
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B] [NoZeroSMulDivisors A B]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsGalois K L]: IsGalois (FractionRing A) (FractionRing B) :=
  IsGalois.of_isGalois_isFractionRing A B K L (FractionRing A) (FractionRing B)
