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

In this file we provide a `PerfectPairing` definition corresponding to 1 above, together with logic
to connect 1 and 2.

## Main definitions

 * `PerfectPairing`
 * `PerfectPairing.flip`
 * `LinearEquiv.flip`
 * `LinearEquiv.isReflexive_of_equiv_dual_of_isReflexive`
 * `LinearEquiv.toPerfectPairing`

-/

open Function Module

variable (R M N : Type*) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A perfect pairing of two (left) modules over a commutative ring. -/
structure PerfectPairing :=
  toLin : M →ₗ[R] N →ₗ[R] R
  bijectiveLeft : Bijective toLin
  bijectiveRight : Bijective toLin.flip

attribute [nolint docBlame] PerfectPairing.toLin

variable {R M N}

namespace PerfectPairing

instance instFunLike : FunLike (PerfectPairing R M N) M (fun _  ↦ N →ₗ[R] R) where
  coe f := f.toLin
  coe_injective' x y h := by cases x; cases y; simpa using h

variable (p : PerfectPairing R M N)

/-- Given a perfect pairing between `M` and `N`, we may interchange the roles of `M` and `N`. -/
protected def flip : PerfectPairing R N M where
  toLin := p.toLin.flip
  bijectiveLeft := p.bijectiveRight
  bijectiveRight := p.bijectiveLeft

@[simp] lemma flip_flip : p.flip.flip = p := rfl

-- TODO `M` and `N` are both reflexive

end PerfectPairing

variable [IsReflexive R M]

/-- A reflexive module has a perfect pairing with its dual. -/
@[simps]
def IsReflexive.toPerfectPairingDual : PerfectPairing R (Dual R M) M where
  toLin := LinearMap.id
  bijectiveLeft := bijective_id
  bijectiveRight := bijective_dual_eval R M

variable (e : N ≃ₗ[R] Dual R M)

namespace LinearEquiv

/-- For a reflexive module `M`, an equivalence `N ≃ₗ[R] Dual R M` naturally yields an equivalence
`M ≃ₗ[R] Dual R N`. Such equivalences are known as perfect pairings. -/
noncomputable def flip : M ≃ₗ[R] Dual R N :=
  (evalEquiv R M).trans e.dualMap

@[simp] lemma coe_toLinearMap_flip : e.flip = (↑e : N →ₗ[R] Dual R M).flip := rfl

@[simp] lemma flip_apply (m : M) (n : N) : e.flip m n = e n m := rfl

lemma symm_flip : e.flip.symm = e.symm.dualMap.trans (evalEquiv R M).symm := rfl

lemma trans_dualMap_symm_flip : e.trans e.flip.symm.dualMap = Dual.eval R N := by
  ext; simp [symm_flip]

/-- If `N` is in perfect pairing with `M`, then it is reflexive. -/
lemma isReflexive_of_equiv_dual_of_isReflexive : IsReflexive R N := by
  constructor
  rw [← trans_dualMap_symm_flip e]
  exact LinearEquiv.bijective _

@[simp] lemma flip_flip (h : IsReflexive R N := isReflexive_of_equiv_dual_of_isReflexive e) :
    e.flip.flip = e := by
  ext; rfl

/-- If `M` is reflexive then a linear equivalence `N ≃ Dual R M` is a perfect pairing. -/
@[simps]
noncomputable def toPerfectPairing : PerfectPairing R N M where
  toLin := e
  bijectiveLeft := e.bijective
  bijectiveRight := e.flip.bijective

end LinearEquiv

namespace Submodule

open LinearEquiv

@[simp]
lemma dualCoannihilator_map_linearEquiv_flip (p : Submodule R M) :
    (p.map e.flip).dualCoannihilator = p.dualAnnihilator.map e.symm := by
  ext; simp [LinearEquiv.symm_apply_eq, Submodule.mem_dualCoannihilator]

@[simp]
lemma map_dualAnnihilator_linearEquiv_flip_symm (p : Submodule R N) :
    p.dualAnnihilator.map e.flip.symm = (p.map e).dualCoannihilator := by
  have : IsReflexive R N := e.isReflexive_of_equiv_dual_of_isReflexive
  rw [← dualCoannihilator_map_linearEquiv_flip, flip_flip]

@[simp]
lemma map_dualCoannihilator_linearEquiv_flip (p : Submodule R (Dual R M)) :
    p.dualCoannihilator.map e.flip = (p.map e.symm).dualAnnihilator := by
  have : IsReflexive R N := e.isReflexive_of_equiv_dual_of_isReflexive
  suffices (p.map e.symm).dualAnnihilator.map e.flip.symm =
      (p.dualCoannihilator.map e.flip).map e.flip.symm by
    exact (Submodule.map_injective_of_injective e.flip.symm.injective this).symm
  erw [← dualCoannihilator_map_linearEquiv_flip, flip_flip, ← map_comp, ← map_comp]
  simp [-coe_toLinearMap_flip]

@[simp]
lemma dualAnnihilator_map_linearEquiv_flip_symm (p : Submodule R (Dual R N)) :
    (p.map e.flip.symm).dualAnnihilator = p.dualCoannihilator.map e := by
  have : IsReflexive R N := e.isReflexive_of_equiv_dual_of_isReflexive
  rw [← map_dualCoannihilator_linearEquiv_flip, flip_flip]

end Submodule
