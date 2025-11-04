/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-! # Base change properties for modules of linear maps

* `IsBaseChange.linearMapRight`:
  If `M` has a finite basis and `P` is a base change of `N` to `S`,
  then `M →ₗ[R] P` is a base change of `M →ₗ[R] N` to `S`.

  -/

namespace IsBaseChange

open LinearMap TensorProduct

variable {R : Type*} [CommSemiring R]
    (S : Type*) [CommSemiring S] [Algebra R S]
    (M : Type*) [AddCommMonoid M] [Module R M] -- [Module S M] [IsScalarTower R S M]
    {N : Type*} [AddCommMonoid N] [Module R N]
    {ι : Type*} [DecidableEq ι]
    {P : Type*} [AddCommMonoid P] [Module R P] -- [Module S P] [IsScalarTower R S P]

section LinearMapRight

variable [Module S P] [IsScalarTower R S P]

/-- The base change homomorphism underlying `IsBaseChange.linearMapRight` -/
def linearMapRightBaseChangeHom (ε : N →ₗ[R] P) :
    (S ⊗[R] (M →ₗ[R] N)) →ₗ[S] (M →ₗ[R] P) where
  toAddHom := (TensorProduct.lift {
    toFun s := s • (LinearMap.compRight R ε (M := M))
    map_add' x y := by ext; simp [add_smul]
    map_smul' r s := by aesop }).toAddHom
  map_smul' s x := by
    simp
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [smul_add, hx, hy]
    | tmul t f => simp [TensorProduct.smul_tmul', mul_smul]

variable [Module.Free R M] [Module.Finite R M]

variable {S}

/-- The base change isomorphism funderlying `IsBaseChange.linearMapRight` -/
noncomputable def linearMapRightBaseChangeEquiv
    {ε : N →ₗ[R] P} (ibc : IsBaseChange S ε) :
    S ⊗[R] (M →ₗ[R] N) ≃ₗ[S] (M →ₗ[R] P) := by
  apply LinearEquiv.ofBijective (linearMapRightBaseChangeHom S M ε)
  let b := Module.Free.chooseBasis R M
  set ι := Module.Free.ChooseBasisIndex R M
  have := Module.Free.ChooseBasisIndex.fintype R M
  let e := (b.repr.congrLeft N R).trans (Finsupp.llift N R R ι).symm
  let f := (b.repr.congrLeft P S).trans (Finsupp.llift P R S ι).symm
  let h := linearMapRightBaseChangeHom S M ε
  let e' : S ⊗[R] (M →ₗ[R] N) ≃ₗ[S] S ⊗[R] (ι → N) :=
    LinearEquiv.baseChange R S (M →ₗ[R] N) (ι → N) e
  let h' := (f.toLinearMap.comp (linearMapRightBaseChangeHom S M ε)).comp e'.symm.toLinearMap
  suffices Function.Bijective h' by simpa [h'] using this
  have := IsBaseChange.pi (ι := ι) (f := fun _ ↦ ε) (fun _ ↦ ibc)
  suffices h' = (finitePow ι ibc).equiv by
    simp only [this]
    apply LinearEquiv.bijective
  suffices f.toLinearMap.comp (linearMapRightBaseChangeHom S M ε) =
      (finitePow ι ibc).equiv.toLinearMap.comp e'.toLinearMap by
    simp [h', this]
    rw [← LinearEquiv.trans_assoc]
    simp
  ext φ i
  simp
  simp [f, e', linearMapRightBaseChangeHom, LinearEquiv.baseChange, equiv_tmul,
    LinearEquiv.congrLeft, e]

/-- If `M` has a finite basis and `P` is a base change of `N` to `S`,
then `M →ₗ[R] P` is a base change of `M →ₗ[R] N` to `S`. -/
theorem linearMapRight {ε : N →ₗ[R] P} (ibc : IsBaseChange S ε) :
    IsBaseChange S (LinearMap.compRight (M := M) R ε) := by
  apply of_equiv (linearMapRightBaseChangeEquiv M ibc)
  intro f
  simp [linearMapRightBaseChangeEquiv, linearMapRightBaseChangeHom]

end LinearMapRight

section LinearMapLeft

end LinearMapLeft

end IsBaseChange
