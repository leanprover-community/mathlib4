/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Linear structures on function with finite support `ι →₀ M`

This file contains results on the `R`-module structure on functions of finite support from a type
`ι` to an `R`-module `M`, in particular in the case that `R` is a field.

-/


noncomputable section

open Set LinearMap Submodule

universe u v w

namespace DFinsupp

variable {ι : Type*} {R : Type*} {M : ι → Type*}
variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The direct sum of free modules is free.

Note that while this is stated for `DFinsupp` not `DirectSum`, the types are defeq. -/
noncomputable def basis {η : ι → Type*} (b : ∀ i, Basis (η i) R (M i)) :
    Basis (Σ i, η i) R (Π₀ i, M i) :=
  .ofRepr
    ((mapRange.linearEquiv fun i => (b i).repr).trans (sigmaFinsuppLequivDFinsupp R).symm)

variable (R M) in
instance _root_.Module.Free.dfinsupp [∀ i : ι, Module.Free R (M i)] : Module.Free R (Π₀ i, M i) :=
  .of_basis <| DFinsupp.basis fun i => Module.Free.chooseBasis R (M i)

variable [DecidableEq ι] {φ : ι → Type*} (f : ∀ i, φ i → M i)

open Finsupp (linearCombination)

theorem linearIndependent_single (hf : ∀ i, LinearIndependent R (f i)) :
    LinearIndependent R fun ix : Σ i, φ i ↦ single ix.1 (f ix.1 ix.2) := by
  classical
  have : linearCombination R (fun ix : Σ i, φ i ↦ single ix.1 (f ix.1 ix.2)) =
    DFinsupp.mapRange.linearMap (fun i ↦ linearCombination R (f i)) ∘ₗ
    (sigmaFinsuppLequivDFinsupp R).toLinearMap := by ext; simp
  rw [LinearIndependent, this]
  exact ((DFinsupp.mapRange_injective _ fun _ ↦ map_zero _).mpr hf).comp (Equiv.injective _)

lemma linearIndependent_single_iff :
    LinearIndependent R (fun ix : Σ i, φ i ↦ single ix.1 (f ix.1 ix.2)) ↔
      ∀ i, LinearIndependent R (f i) :=
  ⟨fun h i ↦ (h.comp _ sigma_mk_injective).of_comp (lsingle i), linearIndependent_single _⟩

end DFinsupp

namespace Finsupp

section Semiring

variable {R : Type*} {M : Type*} {ι : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M]

theorem linearIndependent_single {φ : ι → Type*} (f : ∀ i, φ i → M)
    (hf : ∀ i, LinearIndependent R (f i)) :
    LinearIndependent R fun ix : Σ i, φ i ↦ single ix.1 (f ix.1 ix.2) := by
  classical
  convert (DFinsupp.linearIndependent_single _ hf).map_injOn
    _ (finsuppLequivDFinsupp R).symm.injective.injOn
  simp

lemma linearIndependent_single_iff {φ : ι → Type*} {f : ∀ i, φ i → M} :
    LinearIndependent R (fun ix : Σ i, φ i ↦ single ix.1 (f ix.1 ix.2)) ↔
      ∀ i, LinearIndependent R (f i) :=
  ⟨fun h i ↦ (h.comp _ sigma_mk_injective).of_comp (lsingle i), linearIndependent_single _⟩

open LinearMap Submodule

open scoped Classical in
/-- The basis on `ι →₀ M` with basis vectors `fun ⟨i, x⟩ ↦ single i (b i x)`. -/
protected def basis {φ : ι → Type*} (b : ∀ i, Basis (φ i) R M) : Basis (Σ i, φ i) R (ι →₀ M) :=
  .ofRepr <| (finsuppLequivDFinsupp R).trans <|
    (DFinsupp.mapRange.linearEquiv fun i ↦ (b i).repr).trans (sigmaFinsuppLequivDFinsupp R).symm

@[simp]
theorem basis_repr {φ : ι → Type*} (b : ∀ i, Basis (φ i) R M) (g : ι →₀ M) (ix) :
    (Finsupp.basis b).repr g ix = (b ix.1).repr (g ix.1) ix.2 :=
  rfl

@[simp]
theorem coe_basis {φ : ι → Type*} (b : ∀ i, Basis (φ i) R M) :
    ⇑(Finsupp.basis b) = fun ix : Σi, φ i => single ix.1 (b ix.1 ix.2) :=
  funext fun ⟨i, x⟩ =>
    Basis.apply_eq_iff.mpr <| by
      ext ⟨j, y⟩
      by_cases h : i = j
      · cases h
        simp [Finsupp.single_apply_left sigma_mk_injective]
      · simp_all

variable (ι R M) in
instance _root_.Module.Free.finsupp [Module.Free R M] : Module.Free R (ι →₀ M) :=
  .of_basis (Finsupp.basis fun _ => Module.Free.chooseBasis R M)

/-- The basis on `ι →₀ R` with basis vectors `fun i ↦ single i 1`. -/
@[simps]
protected def basisSingleOne : Basis ι R (ι →₀ R) :=
  Basis.ofRepr (LinearEquiv.refl _ _)

@[simp]
theorem coe_basisSingleOne : (Finsupp.basisSingleOne : ι → ι →₀ R) = fun i => Finsupp.single i 1 :=
  funext fun _ => Basis.apply_eq_iff.mpr rfl

variable (ι R) in
lemma linearIndependent_single_one : LinearIndependent R fun i : ι ↦ single i (1 : R) :=
  Finsupp.basisSingleOne.linearIndependent

end Semiring

section Ring

variable {R : Type*} {M : Type*} {ι : Type*}
variable [Ring R] [AddCommGroup M] [Module R M]

lemma linearIndependent_single_of_ne_zero [NoZeroSMulDivisors R M] {v : ι → M} (hv : ∀ i, v i ≠ 0) :
    LinearIndependent R fun i : ι ↦ single i (v i) := by
  rw [← linearIndependent_equiv (Equiv.sigmaPUnit ι)]
  exact linearIndependent_single (f := fun i (_ : Unit) ↦ v i) <| by
    simp +contextual [Fintype.linearIndependent_iff, hv]

end Ring

end Finsupp

lemma Module.Free.trans {R S M : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Free S M]
    [Module.Free R S] : Module.Free R M :=
  let e : (ChooseBasisIndex S M →₀ S) ≃ₗ[R] ChooseBasisIndex S M →₀ (ChooseBasisIndex R S →₀ R) :=
    Finsupp.mapRange.linearEquiv (chooseBasis R S).repr
  let e : M ≃ₗ[R] ChooseBasisIndex S M →₀ (ChooseBasisIndex R S →₀ R) :=
    (chooseBasis S M).repr.restrictScalars R ≪≫ₗ e
  .of_equiv e.symm

/-! TODO: move this section to an earlier file. -/


namespace Basis

variable {R M n : Type*}
variable [DecidableEq n]
variable [Semiring R] [AddCommMonoid M] [Module R M]

theorem _root_.Finset.sum_single_ite [Fintype n] (a : R) (i : n) :
    (∑ x : n, Finsupp.single x (if i = x then a else 0)) = Finsupp.single i a := by
  simp only [apply_ite (Finsupp.single _), Finsupp.single_zero, Finset.sum_ite_eq,
    if_pos (Finset.mem_univ _)]

@[simp]
theorem equivFun_symm_single [Finite n] (b : Basis n R M) (i : n) :
    b.equivFun.symm (Pi.single i 1) = b i := by
  cases nonempty_fintype n
  simp [Pi.single_apply]

end Basis

section Algebra

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S] {ι : Type*} (B : Basis ι R S)

/-- For any `r : R`, `s : S`, we have
  `B.repr ((algebra_map R S r) * s) i = r * (B.repr s i) `. -/
theorem Basis.repr_smul' (i : ι) (r : R) (s : S) :
    B.repr (algebraMap R S r * s) i = r * B.repr s i := by
  rw [← smul_eq_mul, ← smul_eq_mul, algebraMap_smul, map_smul, Finsupp.smul_apply]

end Algebra
