/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
/-!
# Base change for the dual of a module

* `Module.Dual.congr` : equivalent modules have equivalent duals.

If `f : Module.Dual R V` and `Algebra R A`, then

* `Module.Dual.baseChange A f` is the element
of `Module.Dual A (A ⊗[R] V)` deduced by base change.

* `Module.Dual.baseChangeHom` is the `R`-linear map
given by `Module.Dual.baseChange`.

-/

universe u v

namespace Module.Dual

open TensorProduct LinearEquiv

variable {R : Type*} [CommSemiring R]
  {V : Type*} [AddCommMonoid V] [Module R V]
  {W : Type*} [AddCommMonoid W] [Module R W]
  (A : Type*) [CommSemiring A] [Algebra R A]

/-- Equivalent modules have equivalent duals. -/
def congr (e : V ≃ₗ[R] W) :
    Module.Dual R V ≃ₗ[R] Module.Dual R W :=
  LinearEquiv.congrLeft R R e

/-- `LinearMap.baseChange` for `Module.Dual`. -/
def baseChange (f : Module.Dual R V) :
    Module.Dual A (A ⊗[R] V) :=
  (AlgebraTensorModule.rid R A A).toLinearMap.comp (LinearMap.baseChange A f)

@[simp]
theorem baseChange_add (f g : Module.Dual R V) :
    (f + g).baseChange A = f.baseChange A + g.baseChange A := by
  unfold baseChange; aesop

@[simp]
theorem baseChange_smul (r : R) (f : Module.Dual R V) :
    (r • f).baseChange A = r • f.baseChange A := by
  unfold baseChange
  ext x
  simp [LinearMap.baseChange_smul, ← TensorProduct.tmul_smul, mul_smul]

@[simp]
theorem baseChange_apply_tmul (f : Module.Dual R V) (a : A) (v : V) :
    f.baseChange A (a ⊗ₜ v) = (f v) • a := by
  simp [baseChange]

/-- `Module.Dual.baseChange` as a linear map. -/
def baseChangeHom :
    Module.Dual R V →ₗ[R] Module.Dual A (A ⊗[R] V) where
  toFun := Module.Dual.baseChange A
  map_add' := Module.Dual.baseChange_add A
  map_smul' := Module.Dual.baseChange_smul A

@[simp]
theorem baseChangeHom_apply (f : Module.Dual R V) :
    Module.Dual.baseChangeHom A f = f.baseChange A :=
  rfl

theorem coe_baseChangeHom :
    ⇑(Module.Dual.baseChangeHom (V := V) (R := R) A) = Module.Dual.baseChange A :=
  rfl

section group

variable {R : Type*} [CommRing R]
  {V : Type*} [AddCommGroup V] [Module R V]
  (A : Type*) [CommRing A] [Algebra R A]

theorem baseChange_sub (f g : Module.Dual R V) :
    Module.Dual.baseChange A (f - g) = Module.Dual.baseChange A f - Module.Dual.baseChange A g := by
  unfold Module.Dual.baseChange; aesop

theorem baseChange_neg (f : Module.Dual R V) :
    Module.Dual.baseChange A (-f) = -(Module.Dual.baseChange A f) := by
  unfold Module.Dual.baseChange; aesop

end group

section comp

variable (B : Type*) [CommSemiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

theorem baseChange_comp (f : Module.Dual R V) :
    ((f.baseChange A).baseChange B) =
      (Module.Dual.congr (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B V)).symm
       (f.baseChange B) := by
  ext; simp [Module.Dual.congr, congrLeft]

end comp

end Module.Dual

namespace IsBaseChange

open TensorProduct

variable {R : Type*} [CommSemiring R]
  {V : Type*} [AddCommMonoid V] [Module R V]
  {W : Type*} [AddCommMonoid W] [Module R W]
  {A : Type*} [CommSemiring A] [Algebra R A] [Module A W] [IsScalarTower R A W]
  {j : V →ₗ[R] W} (ibc : IsBaseChange A j)

/-- The base change of an element of the dual. -/
noncomputable def toDual (f : Module.Dual R V) :
    Module.Dual A W :=
  (f.baseChange A).congr ibc.equiv

/-- The base change of an element of the dual. -/
noncomputable def toDualHom :
    Module.Dual R V →ₗ[R] Module.Dual A W where
  toFun f := ibc.toDual f
  map_add' f g := by unfold toDual; aesop
  map_smul' r f := by unfold toDual; aesop

noncomputable def foo :
    A ⊗[R] Module.Dual R V →ₗ[A] Module.Dual A W where
  toAddHom := (TensorProduct.lift {
    toFun a := a • ibc.toDualHom
    map_add' a b := by simp [add_smul]
    map_smul' r a := by simp }).toAddHom
  map_smul' a g := by
    induction g using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.id_apply] at hx hy
      simp [map_add, hx, hy]
    | tmul b f =>
      simp [TensorProduct.smul_tmul', mul_smul]

variable [Module.Free R V] [Module.Finite R V]

section

variable (R : Type*) [CommSemiring R]
    (S : Type*) [CommSemiring S] [Algebra R S]
    (M : Type*) [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
    {ι : Type*} [DecidableEq ι]
    (N : ι → Type*) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module R (N i)]

@[simp]
theorem directSumRight_apply (m : M) (n : DFinsupp N) (i : ι) :
    directSumRight R M N (m ⊗ₜ[R] n) i = m ⊗ₜ[R] (n i) := by
  let f : DFinsupp N →ₗ[R] M ⊗[R] N i := {
    toFun n := (directSumRight R M N) (m ⊗ₜ[R] n) i
    map_add' x y := by simp [tmul_add]
    map_smul' r x := by simp [DirectSum.smul_apply] }
  let g : DFinsupp N →ₗ[R] M ⊗[R] N i := {
    toFun n := m ⊗ₜ[R] n i
    map_add' x y := by simp [tmul_add]
    map_smul' r x := by simp }
  suffices f = g by
    exact LinearMap.congr_fun this n
  ext j n
  simp only [f, g, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
    DFinsupp.lsingle_apply, DFinsupp.single_apply]
  by_cases hj : j = i
  · subst hj
    simp [DirectSum.single_eq_lof R]
  · rw [dif_neg hj, DirectSum.single_eq_lof R, directSumRight_tmul_lof, tmul_zero]
    exact DFinsupp.single_eq_of_ne fun a ↦ hj (id (Eq.symm a))

def _root_.TensorProduct.directSumRight' :
    M ⊗[R] (DirectSum ι N) ≃ₗ[S] DirectSum ι (fun i ↦ M ⊗[R] (N i)) where
  toAddEquiv := (directSumRight R M N).toAddEquiv
  map_smul' s n :=  by
    induction n using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
        RingHom.id_apply] at hx hy ⊢
      simp only [smul_add, hx, hy, map_add]
    | tmul m n =>
      ext i
      simp [TensorProduct.smul_tmul', directSumRight_apply, DirectSum.smul_apply]

variable (P : ι → Type*) [∀ i, AddCommMonoid (P i)]
  [∀ i, Module R (P i)] [∀ i, Module S (P i)] [∀ i, IsScalarTower R S (P i)]
  (ε : (i : ι) → N i →ₗ[R] P i) (ibc : ∀ i, IsBaseChange S (ε i))

variable {R N P} in
def LinearEquiv.directSumRight (u : (i : ι) → N i ≃ₗ[R] P i) :
    DirectSum ι N ≃ₗ[R] DirectSum ι P where
  toLinearMap := DirectSum.lmap fun i ↦ (u i).toLinearMap
  invFun := DirectSum.lmap fun i ↦ (u i).symm.toLinearMap
  left_inv u := by
    simp [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ← LinearMap.comp_apply,
      ← DirectSum.lmap_comp]
  right_inv u := by
    simp [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ← LinearMap.comp_apply,
      ← DirectSum.lmap_comp]

omit [DecidableEq ι] in
variable {R N P} in
theorem LinearEquiv.coe_directSumRight (u : (i : ι) → N i ≃ₗ[R] P i) :
    (LinearEquiv.directSumRight u).toLinearMap = DirectSum.lmap fun i ↦ (u i).toLinearMap :=
  rfl

variable {R S N P ε} in
theorem directSum (ibc : ∀ i, IsBaseChange S (ε i)) :
    IsBaseChange S (DirectSum.lmap ε) := by
  apply of_equiv <| directSumRight' R S S N ≪≫ₗ LinearEquiv.directSumRight fun i ↦ (ibc i).equiv
  intro x
  ext i
  simp [TensorProduct.directSumRight', LinearEquiv.directSumRight, equiv_tmul]

end

section

variable (R : Type*) [CommSemiring R]
    (S : Type*) [CommSemiring S] [Algebra R S]
    (M : Type*) [AddCommMonoid M] [Module R M] -- [Module S M] [IsScalarTower R S M]
    {ι : Type*} [DecidableEq ι]
    (N : ι → Type*) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module R (N i)]

variable {R}
variable {N : Type*} [AddCommMonoid N] [Module R N]
    {P : Type*} [AddCommMonoid P] [Module R P] [Module S P] [IsScalarTower R S P]
    {ε : N →ₗ[R] P} (ibc : IsBaseChange S ε)

variable {S M} in
theorem finitePow (ι : Type*) [Finite ι] (ibc : IsBaseChange S ε) :
    IsBaseChange S (ε.compLeft ι) :=
  IsBaseChange.pi (f := fun _ ↦ ε) (fun _ ↦ ibc)

variable {S M} in
theorem finsuppPow (ι : Type*) [DecidableEq ι] (ibc : IsBaseChange S ε) :
    IsBaseChange S (DirectSum.lmap fun _ : ι ↦ ε) :=
  IsBaseChange.directSum (fun _ : ι ↦ ibc)

variable {S M} in
noncomputable def bar : S ⊗[R] (ι →₀ N) ≃ₗ[S] (ι →₀ P) := by
  let e := (ibc.finsuppPow ι).equiv
  let f : DirectSum ι (fun _ ↦ N) ≃ₗ[R] (ι →₀ N) :=
    (finsuppLEquivDirectSum R N ι).symm
  let fS : S ⊗[R] (DirectSum ι (fun _ ↦ N)) ≃ₗ[S] S ⊗[R] (ι →₀ N) :=
    LinearEquiv.baseChange R S (DirectSum ι fun x ↦ N) (ι →₀ N) f
  let g : DirectSum ι (fun _ ↦ P) ≃ₗ[S] (ι →₀ P) :=
    (finsuppLEquivDirectSum S P ι).symm
  exact (fS.symm.trans e).trans g

variable {S M} in
theorem finsuppPow' (ι : Type*) [DecidableEq ι] (ibc : IsBaseChange S ε) :
    IsBaseChange S (Finsupp.mapRange.linearMap (α := ι) ε) := by
  apply of_equiv ibc.bar
  sorry

variable (ε) in
def homFoo : S ⊗[R] (M →ₗ[R] N) →ₗ[R] (M →ₗ[R] P) := by
  apply TensorProduct.lift {
    toFun s := s • LinearMap.compRight R ε
    map_add' x y := by ext; simp [add_smul]
    map_smul' r s := by aesop }

variable (ε) in
def homFoo' : (S ⊗[R] (M →ₗ[R] N)) →ₗ[S] (M →ₗ[R] P) where
  toAddHom := homFoo S M ε
  map_smul' s x := by
    simp
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [smul_add, hx, hy]
    | tmul t f => simp [TensorProduct.smul_tmul', homFoo, mul_smul]

variable [Module.Free R M] [Module.Finite R M]
noncomputable def linearMapRightBaseChangeEquiv (ibc : IsBaseChange S ε) :
    S ⊗[R] (M →ₗ[R] N) ≃ₗ[S] (M →ₗ[R] P) := by
  apply LinearEquiv.ofBijective (homFoo' S M ε)
  let b := Module.Free.chooseBasis R M
  set ι := Module.Free.ChooseBasisIndex R M
  have := Module.Free.ChooseBasisIndex.fintype R M
  let e := (b.repr.congrLeft N R).trans (Finsupp.llift N R R ι).symm
  let f := (b.repr.congrLeft P S).trans (Finsupp.llift P R S ι).symm
  let h := homFoo' S M ε
  let e' : S ⊗[R] (M →ₗ[R] N) ≃ₗ[S] S ⊗[R] (ι → N) :=
    LinearEquiv.baseChange R S (M →ₗ[R] N) (ι → N) e
  let h' := (f.toLinearMap.comp (homFoo' S M ε)).comp e'.symm.toLinearMap
  suffices Function.Bijective h' by simpa [h'] using this
  have := IsBaseChange.pi (ι := ι) (f := fun _ ↦ ε) (fun _ ↦ ibc)
  suffices h' = (finitePow ι ibc).equiv by
    simp only [this]
    apply LinearEquiv.bijective
  suffices f.toLinearMap.comp (homFoo' S M ε) =
      (finitePow ι ibc).equiv.toLinearMap.comp e'.toLinearMap by
    simp [h', this]
    rw [← LinearEquiv.trans_assoc]
    simp
  ext φ i
  simp
  simp [f, e', homFoo', homFoo, LinearEquiv.baseChange, equiv_tmul,
    LinearEquiv.congrLeft, e]

theorem linearMapRight (ibc : IsBaseChange S ε) :
    IsBaseChange S (LinearMap.compRight (M := M) R ε) := by
  apply of_equiv (linearMapRightBaseChangeEquiv S M ibc)
  intro f
  simp [linearMapRightBaseChangeEquiv, homFoo', homFoo]

end

section

variable (R : Type*) [CommSemiring R]
  (S : Type*) [CommSemiring S] [Algebra R S]
  (M : Type*) [AddCommMonoid M] [Module R M]
  (N : Type*) [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
  (ε : M →ₗ[R] N) (ibc : IsBaseChange S ε)

noncomputable example : Module.Dual R M →ₗ[R] Module.Dual S N :=
  ibc.toDualHom

variable [Module.Free R M] [Module.Finite R M]

noncomputable def foo' : S ⊗[R] Module.Dual R M ≃ₗ[S] Module.Dual S N := by
  apply LinearEquiv.ofBijective ibc.foo
  classical
  let b := Module.Free.chooseBasis R M
  set ι := Module.Free.ChooseBasisIndex R M
  have ibc' : IsBaseChange S (Algebra.linearMap R S) := linearMap R S
  have ibc'_pow := ibc'.finsuppPow ι
  have := Module.Free.ChooseBasisIndex.fintype R M
  let e : Module.Dual R M ≃ₗ[R] ι → R := (Module.Free.constr R M R).symm
  let j := ibc.equiv
  let f : S ⊗[R] M ≃ₗ[R] S ⊗[R] (ι →₀ R) := {
    toAddEquiv := LinearEquiv.lTensor S b.repr
    map_smul' := sorry }
  let g : S ⊗[R] (ι →₀ R) ≃ₗ[S] ι →₀ S := by
    have := ibc'_pow.equiv



example : IsBaseChange S ibc.toDualHom := by
  apply of_equiv
  swap

end

end IsBaseChange
