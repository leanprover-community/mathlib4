/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Perfect pairings of modules

A perfect pairing of two (left) modules may be defined either as:
 1. A bilinear map `M × N → R` such that the induced maps `M → Dual R N` and `N → Dual R M` are both
    bijective. It follows from this that both `M` and `N` are reflexive modules.
 2. A linear equivalence `N ≃ Dual R M` for which `M` is reflexive. (It then follows that `N` is
    reflexive.)

In this file we provide a `PerfectPairing` definition corresponding to 1 above, together with logic
to connect 1 and 2.

## Main definitions

 * `PerfectPairing`
 * `PerfectPairing.flip`
 * `PerfectPairing.toDualLeft`
 * `PerfectPairing.toDualRight`
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

instance instFunLike : FunLike (PerfectPairing R M N) M (N →ₗ[R] R) where
  coe f := f.toLin
  coe_injective' x y h := by cases x; cases y; simpa using h

variable (p : PerfectPairing R M N)

/-- Given a perfect pairing between `M` and `N`, we may interchange the roles of `M` and `N`. -/
protected def flip : PerfectPairing R N M where
  toLin := p.toLin.flip
  bijectiveLeft := p.bijectiveRight
  bijectiveRight := p.bijectiveLeft

@[simp] lemma flip_flip : p.flip.flip = p := rfl

section reflexive

/-- The linear equivalence from `M` to `Dual R N` induced by a perfect pairing. -/
noncomputable def toDualLeft : M ≃ₗ[R] Dual R N :=
  LinearEquiv.ofBijective p.toLin p.bijectiveLeft

@[simp]
theorem toDualLeft_apply (a : M) : p.toDualLeft a = p.toLin a :=
  rfl

@[simp]
theorem apply_toDualLeft_symm_apply (f : Dual R N) (x : N) : p (p.toDualLeft.symm f) x = f x := by
  have h := LinearEquiv.apply_symm_apply p.toDualLeft f
  rw [toDualLeft_apply] at h
  exact congrFun (congrArg DFunLike.coe h) x

/-- The linear equivalence from `N` to `Dual R M` induced by a perfect pairing. -/
noncomputable def toDualRight : N ≃ₗ[R] Dual R M := toDualLeft p.flip


@[simp]
theorem toDualRight_apply (a : N) : p.toDualRight a = p.flip.toLin a :=
  rfl

@[simp]
theorem apply_apply_toDualRight_symm (x : M) (f : Dual R M) :
    (p x) (p.toDualRight.symm f) = f x := by
  have h := LinearEquiv.apply_symm_apply p.toDualRight f
  rw [toDualRight_apply] at h
  exact congrFun (congrArg DFunLike.coe h) x

theorem toDualLeft_of_toDualRightInvFun (x : M) (f : Dual R M) :
    (p.toDualLeft x) (p.toDualRight.invFun f) = f x := by
  rw [@toDualLeft_apply]
  exact apply_apply_toDualRight_symm p x f

theorem toDualRight_symm_toDualLeft (x : M) :
    p.toDualRight.symm.dualMap (p.toDualLeft x) = Dual.eval R M x := by
  ext f
  simp only [LinearEquiv.dualMap_apply, Dual.eval_apply]
  exact toDualLeft_of_toDualRightInvFun p x f

theorem bijective_toDualRight_symm_toDualLeft :
    Bijective (fun x => p.toDualRight.symm.dualMap (p.toDualLeft x)) :=
  Bijective.comp (LinearEquiv.bijective p.toDualRight.symm.dualMap)
    (LinearEquiv.bijective p.toDualLeft)

theorem reflexive_left : IsReflexive R M where
  bijective_dual_eval' := by
    constructor
    · intro a b h
      rw [← toDualRight_symm_toDualLeft p a, ← toDualRight_symm_toDualLeft p b] at h
      apply (bijective_toDualRight_symm_toDualLeft p).1 h
    · intro a
      simp_rw [← toDualRight_symm_toDualLeft p]
      apply (bijective_toDualRight_symm_toDualLeft p).2

theorem reflexive_right : IsReflexive R N := reflexive_left p.flip

end reflexive

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


section baseChange
/-!
We have a correspondence between reflexive modules and perfect pairings.  Unfortunately, reflexivity
is not preserved under arbitrary base change, so we need to assume the base change of `M` is
reflexive.
-/
open TensorProduct

variable {S : Type*} [CommRing S] [Algebra R S] (p : PerfectPairing R M N)
(hSM : IsReflexive S (S ⊗[R] M))

namespace PerfectPairing

/-- The first step in a base change. -/
noncomputable def baseChange1 : S ⊗[R] M ≃ₗ[S] (S ⊗[R] (N →ₗ[R] R)) :=
  TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl S S) p.toDualLeft

/-- The second step in a base change. -/
noncomputable def self_module_hom : (S →ₗ[S] S) ≃ₗ[S] S :=
  LinearMap.ringLmapEquivSelf S S S
  --((Module.moduleEndSelf S).toLinearEquiv xxx).symm ≪≫ₗ (MulOpposite.opLinearEquiv S).symm


/-- The third step in a base change. -/
noncomputable def baseChange3 : (S →ₗ[S] S) ⊗[R] (N →ₗ[R] R) →ₗ[S] (S ⊗[R] N →ₗ[S] S ⊗[R] R) :=
  TensorProduct.AlgebraTensorModule.homTensorHomMap R S S S N S R


/-!
  TensorProduct.AlgebraTensorModule.map (LinearEquiv.refl S S)

(S ⊗[R] (N →ₗ[R] R)) ≃ₗ[S] ((S ⊗[R] N) →ₗ[S] (S ⊗[R] R))

noncomputable def LinearEquiv.rTensor (e : M ≃ₗ[R] N)   :
    M ⊗[R] P ≃ₗ[R] N ⊗[R] P := TensorProduct.congr e (refl R P)
LinearEquiv.refl
noncomputable def baseChange : PerfectPairing S (S ⊗[R] M) (S ⊗[R] N)
    where
  toLin := TensorProduct.AlgebraTensorModule.homTensorHomMap R S S S N S R
    ∘ₗ (TensorProduct.AlgebraTensorModule.map
      (Module.moduleEndSelf S ∘ₗ MulOpposite.opLinearEquiv S) (LinearEquiv.refl R (N →ₗ[R] R)))
    ∘ₗ (TensorProduct.AlgebraTensorModule.map (LinearEquiv.refl S S) p.toLin)
  bijectiveLeft := sorry
  bijectiveRight := sorry

LinearEquiv.smulOfUnit : inverse to (S →ₗ[S] S) ≃ₗ[S] S

revision: I think this may fail for non-flat base change!
also, it might be better to skip curry/uncurry - just base change via
TensorProduct.AlgebraTensorModule.map (LinearEquiv.refl S S) p.toLin to
  S ⊗[R] M →ₗ[S] (S ⊗[R] (N →ₗ[R] R))
and compose with the equiv ???
  (S ⊗[R] (N →ₗ[R] R)) ≃ₗ[S] (S ⊗[R] N →ₗ[S] S ⊗[R] R) ≃ₗ[S] (S ⊗[R] N →ₗ[S] S)
We may even have base change of duals already!
Hm. I don't have the left map, but I do have TensorProduct.AlgebraTensorModule.homTensorHomMap
  (S →ₗ[S] S) ⊗[R] (N →ₗ[R] R)) →ₗ[S] (S ⊗[R] N →ₗ[S] S ⊗[R] R)
so I left-compose with
TensorProduct.AlgebraTensorModule.map ??? (LinearEquiv.refl R (N →ₗ[R] R))
  (S ⊗[R] (N →ₗ[R] R)) ≃ₗ[S] (S →ₗ[S] S) ⊗[R] (N →ₗ[R] R))


TensorProduct.AlgebraTensorModule.map (LinearEquiv.refl S S)

/-- The base chage of a perfect pairing`. -/
noncomputable def baseChange : PerfectPairing S (S ⊗[R] M) (S ⊗[R] N)
    where
  toLin := TensorProduct.curry (TensorProduct.AlgebraTensorModule.rid R S S
    ∘ₗ TensorProduct.AlgebraTensorModule.map (LinearEquiv.refl S S)
      ((TensorProduct.uncurry R M N R) P.toLin)
    ∘ₗ ((TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R S S M S N)
    ≪≫ₗ (TensorProduct.AlgebraTensorModule.congr
      (TensorProduct.rid S S) (LinearEquiv.refl R (M ⊗[R] N)))))
  bijectiveLeft := sorry
  bijectiveRight := sorry


TensorProduct.AlgebraTensorModule.map (RingHom.id S) ((TensorProduct.uncurry R M N R) P.toLin) :
  S ⊗[R] M ⊗[R] N →ₗ[S] S ⊗[R] R
so compose on left with TensorProduct.AlgebraTensorModule.rid R S S :
  S ⊗[R] R ≃ₗ[A] S,
on the right with
  (S ⊗[R] M) ⊗[S] (S ⊗[R] N) →ₗ[S] S) ≃ S ⊗[R] M ⊗[R] N
which is TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R S S M S N :
  (S ⊗[R] M) ⊗[S] (S ⊗[R] N) ≃ₗ[S] (S ⊗[S] S) ⊗[R] (M ⊗[R] N)
followed by
  TensorProduct.AlgebraTensorModule.congr TensorProduct.lid (LinearEquiv.refl R (M ⊗[R] N)) :
  (S ⊗[S] S) ⊗[R] (M ⊗[R] N) → S ⊗[R] M ⊗[R] N
then curry

/-- just copied -/
def tensorDistrib : BilinForm A M₁ ⊗[R] BilinForm R M₂ →ₗ[A] BilinForm A (M₁ ⊗[R] M₂) :=
  ((TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R A M₁ M₂ M₁ M₂).dualMap
    ≪≫ₗ (TensorProduct.lift.equiv A (M₁ ⊗[R] M₂) (M₁ ⊗[R] M₂) A).symm).toLinearMap
  ∘ₗ TensorProduct.AlgebraTensorModule.dualDistrib R _ _ _
  ∘ₗ (TensorProduct.AlgebraTensorModule.congr
    (TensorProduct.lift.equiv A M₁ M₁ A)
    (TensorProduct.lift.equiv R _ _ _)).toLinearMap

/-- just copied -/
protected def tmul (B₁ : BilinForm A M₁) (B₂ : BilinForm R M₂) : BilinForm A (M₁ ⊗[R] M₂) :=
  tensorDistrib R A (B₁ ⊗ₜ[R] B₂)

/-- just copied -/
protected def baseChange (B : BilinForm R M₂) : BilinForm A (A ⊗[R] M₂) :=
  BilinForm.tmul (R := R) (A := A) (M₁ := A) (M₂ := M₂) (LinearMap.mul A A) B

-/
end PerfectPairing

end baseChange
