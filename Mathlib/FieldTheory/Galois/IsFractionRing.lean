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

/- Galois extension is transfered between two pairs of fraction rings
-/
theorem IsGalois.of_isGalois_isFractionRing (A B K L K' L' : Type*)
    [CommRing A] [CommRing B] [IsDomain B] [Algebra A B] [NoZeroSMulDivisors A B]
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
    [IsGalois K L] : IsGalois K' L' := by
  let KK' : K ≃ₐ[A] K' := (FractionRing.algEquiv A K).symm.trans (FractionRing.algEquiv A K')
  let _ : Algebra K L' := Algebra.compHom L' KK'.toRingHom
  have : IsScalarTower A K L' := by
    apply IsScalarTower.of_algebraMap_eq
    simp [Algebra.compHom_algebraMap_apply, IsScalarTower.algebraMap_apply A K' L']
  let LL' : L ≃ₐ[K] L' := IsFractionRing.fieldEquivOfAlgEquiv K L L' (AlgEquiv.refl : B ≃ₐ[A] B)
  have : IsGalois K L' := IsGalois.of_algEquiv LL'
  let _ : Algebra K K' := RingHom.toAlgebra KK'
  have : IsScalarTower K K' L' := IsScalarTower.of_algebraMap_eq' rfl
  exact IsGalois.tower_top_of_isGalois K K' L'

theorem IsGalois.iff_isGalois_isFractionRing (A B K L K' L' : Type*)
    [CommRing A] [CommRing B] [IsDomain B] [Algebra A B] [NoZeroSMulDivisors A B]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Field K'] [Field L']
    [Algebra A K'] [IsFractionRing A K']
    [Algebra B L'] [IsFractionRing B L']
    [Algebra K' L'] [Algebra A L']
    [IsScalarTower A B L'] [IsScalarTower A K' L'] :
    IsGalois K L ↔ IsGalois K' L' :=
  Iff.intro
    (fun _ => IsGalois.of_isGalois_isFractionRing A B K L K' L')
    (fun _ => IsGalois.of_isGalois_isFractionRing A B K' L' K L)

attribute [local instance] FractionRing.liftAlgebra

theorem IsGalois.isFractionRing_of_isGalois_fractionRing (A B K L : Type*)
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B] [NoZeroSMulDivisors A B]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsGalois (FractionRing A) (FractionRing B)] : IsGalois K L :=
  IsGalois.of_isGalois_isFractionRing A B (FractionRing A) (FractionRing B) K L


theorem IsGalois.fractionRing_of_isGalois_isFractionRing (A B K L : Type*)
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B] [NoZeroSMulDivisors A B]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsGalois K L]: IsGalois (FractionRing A) (FractionRing B) :=
  IsGalois.of_isGalois_isFractionRing A B K L (FractionRing A) (FractionRing B)
