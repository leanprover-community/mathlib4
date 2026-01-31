/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.LinearAlgebra.Determinant

/-! # Base change properties for modules of linear maps

* `IsBaseChange.linearMapRight`:
  If `M` is finite free and `P` is a base change of `N` to `S`,
  then `M →ₗ[R] P` is a base change of `M →ₗ[R] N` to `S`.

* `IsBaseChange.linearMapLeftRight`:
  If `M` is finite free and `P` is a base change of `M` to `S`,
  if `Q` is a base change of `N` to `S`,
  then `P →ₗ[S] Q` is a base change of `M →ₗ[R] N` to `S`.

* `IsBaseChange.end`:
  If `M` is finite free and `P` is a base change of `M` to `S`,
  then `P →ₗ[S] P` is a base change of `M →ₗ[R] M` to `S`.

-/

@[expose] public section

namespace IsBaseChange

open LinearMap TensorProduct Module

variable {R : Type*} [CommSemiring R]
    (S : Type*) [CommSemiring S] [Algebra R S]
    (M : Type*) [AddCommMonoid M] [Module R M]
    {N : Type*} [AddCommMonoid N] [Module R N]
    {P : Type*} [AddCommMonoid P] [Module R P]

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
    simp only [AddHom.toFun_eq_coe, coe_toAddHom, RingHom.id_apply]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [smul_add, hx, hy]
    | tmul t f => simp [TensorProduct.smul_tmul', mul_smul]

variable [Free R M] [Module.Finite R M]

variable {S}

/-- The base change isomorphism funderlying `IsBaseChange.linearMapRight` -/
noncomputable def linearMapRightBaseChangeEquiv
    {ε : N →ₗ[R] P} (ibc : IsBaseChange S ε) :
    S ⊗[R] (M →ₗ[R] N) ≃ₗ[S] (M →ₗ[R] P) := by
  apply LinearEquiv.ofBijective (linearMapRightBaseChangeHom S M ε)
  let b := Free.chooseBasis R M
  set ι := Free.ChooseBasisIndex R M
  have := Free.ChooseBasisIndex.fintype R M
  let e := (b.repr.congrLeft N R).trans (Finsupp.llift N R R ι).symm
  let f := (b.repr.congrLeft P S).trans (Finsupp.llift P R S ι).symm
  let h := linearMapRightBaseChangeHom S M ε
  let e' : S ⊗[R] (M →ₗ[R] N) ≃ₗ[S] S ⊗[R] (ι → N) :=
    LinearEquiv.baseChange R S (M →ₗ[R] N) (ι → N) e
  let h' := (f.toLinearMap.comp (linearMapRightBaseChangeHom S M ε)).comp e'.symm.toLinearMap
  suffices Function.Bijective h' by simpa [h'] using this
  suffices h' = (finitePow ι ibc).equiv by
    simp only [this]
    apply LinearEquiv.bijective
  suffices f.toLinearMap.comp (linearMapRightBaseChangeHom S M ε) =
      (finitePow ι ibc).equiv.toLinearMap.comp e'.toLinearMap by
    simp [h', this, ← LinearEquiv.trans_assoc e'.symm e']
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

section LinearMapLeftRight

variable {S M}
  {Q : Type*} [AddCommMonoid Q] [Module R Q]
  [Module S P] [IsScalarTower R S P]
  [Module S Q] [IsScalarTower R S Q]

/-- The base change map for linear maps with source a free finite module. -/
noncomputable def linearMapLeftRightHom {α : M →ₗ[R] P} (j : IsBaseChange S α)
    (β : N →ₗ[R] Q) :
    (M →ₗ[R] N) →ₗ[R] (P →ₗ[S] Q) :=
  ((LinearMap.llcomp (σ₂₃ := RingHom.id S) S P (S ⊗[R] M) Q).flip
    j.equiv.symm.toLinearMap) ∘ₗ
    (liftBaseChangeEquiv S).toLinearMap.restrictScalars R ∘ₗ
      (compRight R β (M := M))

theorem linearMapLeftRightHom_apply
    {α : M →ₗ[R] P} (j : IsBaseChange S α) (β : N →ₗ[R] Q) (f : M →ₗ[R] N) (p : P) :
    linearMapLeftRightHom j β f p = ((liftBaseChangeEquiv S) (β ∘ₗ f)) (j.equiv.symm p) := by
  rfl

@[simp] theorem linearMapLeftRightHom_comp_apply
    {α : M →ₗ[R] P} (j : IsBaseChange S α) (β : N →ₗ[R] Q) (f : M →ₗ[R] N) (m : M) :
    linearMapLeftRightHom j β f (α m) = β (f m) := by
  simp [linearMapLeftRightHom_apply, IsBaseChange.equiv_symm_apply]

@[simp] theorem linearMapLeftRightHom_comp
    {α : M →ₗ[R] P} (j : IsBaseChange S α) (β : N →ₗ[R] Q) (f : M →ₗ[R] N) :
    (linearMapLeftRightHom j β f).restrictScalars R ∘ₗ α = β ∘ₗ f := by
  ext; simp [linearMapLeftRightHom_comp_apply]

variable [Free R M] [Module.Finite R M]

theorem linearMapLeftRight {α : M →ₗ[R] P} (j : IsBaseChange S α)
    {β : N →ₗ[R] Q} (k : IsBaseChange S β) :
    IsBaseChange S (linearMapLeftRightHom j β) := by
  apply of_equiv <|
      (k.linearMapRight M).equiv ≪≫ₗ liftBaseChangeEquiv S ≪≫ₗ LinearEquiv.congrLeft Q S j.equiv
  intro f
  ext p
  simp [IsBaseChange.equiv_tmul, LinearEquiv.congrLeft, linearMapLeftRightHom_apply]

end LinearMapLeftRight

section End

variable {S M}
  [Module S P] [IsScalarTower R S P]

/-- The base change map for endomorphisms of a free finite module. -/
noncomputable def endHom {α : M →ₗ[R] P} (j : IsBaseChange S α) :
    (M →ₗ[R] M) →ₗ[R] (P →ₗ[S] P) :=
  ((LinearMap.llcomp (σ₂₃ := RingHom.id S) S P (S ⊗[R] M) P).flip
    j.equiv.symm.toLinearMap) ∘ₗ
    (liftBaseChangeEquiv S).toLinearMap.restrictScalars R ∘ₗ
      (compRight R α (M := M))

theorem endHom_apply
    {α : M →ₗ[R] P} (j : IsBaseChange S α) (f : M →ₗ[R] M) (p : P) :
    endHom j f p = ((liftBaseChangeEquiv S) (α ∘ₗ f)) (j.equiv.symm p) := by
  rfl

theorem endHom_comp_apply
    {α : M →ₗ[R] P} (j : IsBaseChange S α) (f : M →ₗ[R] M) (m : M) :
    endHom j f (α m) = α (f m) := by
  simp [endHom_apply, IsBaseChange.equiv_symm_apply]

theorem endHom_comp
    {α : M →ₗ[R] P} (j : IsBaseChange S α) (f : M →ₗ[R] M) :
    (endHom j f).restrictScalars R ∘ₗ α = α ∘ₗ f := by
  ext; simp [endHom_comp_apply]

theorem endHom_one {α : M →ₗ[R] P} (j : IsBaseChange S α) :
    j.endHom 1 = 1 := by
  ext p
  induction p using j.inductionOn with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | smul _ _ h => simp [h]
  | tmul m => simp [endHom_comp_apply]

variable [Free R M] [Module.Finite R M]

theorem _root_.IsBaseChange.end {α : M →ₗ[R] P} (j : IsBaseChange S α) :
    IsBaseChange S (endHom j) := by
  apply of_equiv <|
      (j.linearMapRight M).equiv ≪≫ₗ liftBaseChangeEquiv S ≪≫ₗ LinearEquiv.congrLeft P S j.equiv
  intro f
  ext p
  simp [equiv_tmul, LinearEquiv.congrLeft, endHom_apply]

end End

section Matrix

variable {Q : Type*} [AddCommMonoid Q] [Module R Q] [Module S P] [IsScalarTower R S P]
  [Module S Q] [IsScalarTower R S Q]
  {α : M →ₗ[R] P} {β : N →ₗ[R] Q}
  (ibcM : IsBaseChange S α) (ibcN : IsBaseChange S β)
  {ι θ : Type*} [DecidableEq ι] [Fintype ι] [Fintype θ]
  (b : Module.Basis ι R M) (c : Module.Basis θ R N)

theorem linearMapLeftRightHom_toMatrix (f : M →ₗ[R] N) :
    (linearMapLeftRightHom ibcM β f).toMatrix (ibcM.basis b) (ibcN.basis c) =
      (f.toMatrix b c).map (algebraMap R S) := by
  ext i j
  simp only [toMatrix_apply, Matrix.map_apply, basis_apply,
    linearMapLeftRightHom_comp_apply, basis_repr_comp_apply]

theorem endHom_toMatrix (f : M →ₗ[R] M) :
    (endHom ibcM f).toMatrix (ibcM.basis b) (ibcM.basis b) =
      (f.toMatrix b b).map (algebraMap R S) := by
  ext i j
  simp only [toMatrix_apply, Matrix.map_apply]
  simp only [basis_apply, endHom_comp_apply, basis_repr_comp_apply]


end Matrix

section determinant

variable {R : Type*} [CommRing R]
    (S : Type*) [CommRing S] [Algebra R S]
    (M : Type*) [AddCommGroup M] [Module R M]
    {P : Type*} [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]

variable [Free R M] [Module.Finite R M]

theorem det_endHom {α : M →ₗ[R] P} (j : IsBaseChange S α) (f : M →ₗ[R] M) :
    LinearMap.det (endHom j f) = algebraMap R S (LinearMap.det f) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have : f = 1 := by
      have : Subsingleton M := Module.subsingleton R M
      exact Subsingleton.eq_one f
    simp [this, endHom_one]
  let b := Module.finBasis R M
  rw [← f.det_toMatrix b, ← (j.endHom f).det_toMatrix (j.basis b),
    endHom_toMatrix, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

end determinant

end IsBaseChange
