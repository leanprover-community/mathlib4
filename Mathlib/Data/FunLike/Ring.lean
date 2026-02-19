/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Data.FunLike.Group
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Ring.Pi
import Mathlib.Tactic.FastInstance

/-! # Ring structure for `FunLike` -/

@[expose] public section

namespace FunLike

variable {F α β : Type*} [FunLike F α β]

variable [Mul F]

instance instDistrib [Add F] [Distrib β] [FunLikeMul F α β] [FunLikeAdd F α β] : Distrib F :=
  fast_instance% DFunLike.coe_injective.distrib (fun (f : F) ↦ (f : α → β)) coe_add coe_mul

instance instHasDistribNeg [Neg F] [Mul β] [Add β] [HasDistribNeg β] [FunLikeNeg F α β]
    [FunLikeMul F α β] : HasDistribNeg F :=
  fast_instance% DFunLike.coe_injective.hasDistribNeg (fun (f : F) ↦ (f : α → β)) coe_neg coe_mul

variable [Add F] [Zero F] [One F] [SMul ℕ F]

instance [NonUnitalNonAssocSemiring β] [FunLikeZero F α β] [FunLikeAdd F α β] [FunLikeMul F α β]
    [FunLikeSMul ℕ F α β] : NonUnitalNonAssocSemiring F :=
  fast_instance% DFunLike.coe_injective.nonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul
    coe_smul

instance [NonUnitalSemiring β] [FunLikeZero F α β] [FunLikeAdd F α β] [FunLikeMul F α β]
    [FunLikeSMul ℕ F α β] : NonUnitalSemiring F :=
  fast_instance% DFunLike.coe_injective.nonUnitalSemiring _ coe_zero coe_add coe_mul coe_smul

instance [NonUnitalCommSemiring β] [FunLikeZero F α β] [FunLikeAdd F α β] [FunLikeMul F α β]
    [FunLikeSMul ℕ F α β] : NonUnitalCommSemiring F :=
  fast_instance% DFunLike.coe_injective.nonUnitalCommSemiring _ coe_zero coe_add coe_mul coe_smul

variable [Neg F] [Sub F] [SMul ℤ F]

instance [NonUnitalNonAssocRing β] [FunLikeZero F α β] [FunLikeAdd F α β] [FunLikeMul F α β]
    [FunLikeSMul ℕ F α β] [FunLikeSMul ℤ F α β] [FunLikeNeg F α β] [FunLikeSub F α β] :
    NonUnitalNonAssocRing F :=
  fast_instance% DFunLike.coe_injective.nonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg
    coe_sub coe_smul coe_smul

instance [NonUnitalRing β] [FunLikeZero F α β] [FunLikeAdd F α β] [FunLikeMul F α β]
    [FunLikeSMul ℕ F α β] [FunLikeSMul ℤ F α β] [FunLikeNeg F α β] [FunLikeSub F α β] :
    NonUnitalRing F :=
  fast_instance% DFunLike.coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    coe_smul coe_smul

instance [NonUnitalCommRing β] [FunLikeZero F α β] [FunLikeAdd F α β] [FunLikeMul F α β]
    [FunLikeSMul ℕ F α β] [FunLikeSMul ℤ F α β] [FunLikeNeg F α β] [FunLikeSub F α β] :
    NonUnitalCommRing F :=
  fast_instance% DFunLike.coe_injective.nonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    coe_smul coe_smul

end FunLike
