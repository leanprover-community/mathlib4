/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.Dual

/-!
# Perfect pairings of modules

A perfect pairing of two (left) modules may be defined either as:
 1. A bilinear map `M × N → R` such that the induced maps `M → Dual R N` and `N → Dual R M` are both
    bijective. (It follows from this that both `M` and `N` are both reflexive modules.)
 2. A linear equivalence `N ≃ Dual R M` for which `M` is reflexive. (It then follows that `N` is
    reflexive.)

The second definition is more convenient and we prove some basic facts about it here.

## Main definitions

 * `LinearEquiv.flip`
 * `LinearEquiv.IsReflexive_of_equiv_Dual_of_IsReflexive`

-/

namespace LinearEquiv

open Module

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [IsReflexive R M] (e : N ≃ₗ[R] Dual R M)

/-- For a reflexive module `M`, an equivalence `N ≃ₗ[R] Dual R M` naturally yields an equivalence
`M ≃ₗ[R] Dual R N`. Such equivalences are known as perfect pairings. -/
noncomputable def flip : M ≃ₗ[R] Dual R N :=
(evalEquiv R M).trans e.dualMap

@[simp] lemma coe_toLinearMap_flip : e.flip = (↑e : N →ₗ[R] Dual R M).flip := rfl

@[simp] lemma flip_apply (m : M) (n : N) : e.flip m n = e n m := rfl

@[simp] lemma symm_flip : e.flip.symm = e.symm.dualMap.trans (evalEquiv R M).symm := rfl

lemma trans_dualMap_symm_flip : e.trans e.flip.symm.dualMap = Dual.eval R N := by ext; simp
                                                                                  -- ⊢ ↑(↑↑(trans e (dualMap (symm (flip e)))) x✝¹) x✝ = ↑(↑(Dual.eval R N) x✝¹) x✝
                                                                                       -- 🎉 no goals

/-- If `N` is in perfect pairing with `M`, then it is reflexive. -/
lemma isReflexive_of_equiv_dual_of_isReflexive : IsReflexive R N := by
  constructor
  -- ⊢ Function.Bijective ↑(Dual.eval R N)
  rw [← trans_dualMap_symm_flip e]
  -- ⊢ Function.Bijective ↑↑(trans e (dualMap (symm (flip e))))
  exact LinearEquiv.bijective _
  -- 🎉 no goals

@[simp] lemma flip_flip (h : IsReflexive R N := isReflexive_of_equiv_dual_of_isReflexive e) :
  e.flip.flip = e :=
by ext; rfl
   -- ⊢ ↑(↑(flip (flip e)) x✝¹) x✝ = ↑(↑e x✝¹) x✝
        -- 🎉 no goals

end LinearEquiv
