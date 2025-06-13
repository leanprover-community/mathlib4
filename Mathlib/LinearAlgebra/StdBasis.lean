/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# The standard basis

This file defines the standard basis `Pi.basis (s : ∀ j, Basis (ι j) R (M j))`,
which is the `Σ j, ι j`-indexed basis of `Π j, M j`. The basis vectors are given by
`Pi.basis s ⟨j, i⟩ j' = Pi.single j' (s j) i = if j = j' then s i else 0`.

The standard basis on `R^η`, i.e. `η → R` is called `Pi.basisFun`.

To give a concrete example, `Pi.single (i : Fin 3) (1 : R)`
gives the `i`th unit basis vector in `R³`, and `Pi.basisFun R (Fin 3)` proves
this is a basis over `Fin 3 → R`.

## Main definitions

- `Pi.basis s`: given a basis `s i` for each `M i`, the standard basis on `Π i, M i`
- `Pi.basisFun R η`: the standard basis on `R^η`, i.e. `η → R`, given by
  `Pi.basisFun R η i j = Pi.single i 1 j = if i = j then 1 else 0`.
- `Matrix.stdBasis R n m`: the standard basis on `Matrix n m R`, given by
  `Matrix.stdBasis R n m (i, j) i' j' = if (i, j) = (i', j') then 1 else 0`.

-/

open Function Set Submodule

namespace Pi

open LinearMap

open Set

variable {R : Type*}

section Module

variable {η : Type*} {ιs : η → Type*} {Ms : η → Type*}

theorem linearIndependent_single [Semiring R] [∀ i, AddCommMonoid (Ms i)] [∀ i, Module R (Ms i)]
    [DecidableEq η] (v : ∀ j, ιs j → Ms j) (hs : ∀ i, LinearIndependent R (v i)) :
    LinearIndependent R fun ji : Σ j, ιs j ↦ Pi.single ji.1 (v ji.1 ji.2) := by
  convert (DFinsupp.linearIndependent_single _ hs).map_injOn _ DFinsupp.injective_pi_lapply.injOn

theorem linearIndependent_single_one (ι R : Type*) [Semiring R] [DecidableEq ι] :
    LinearIndependent R (fun i : ι ↦ Pi.single i (1 : R)) := by
  rw [← linearIndependent_equiv (Equiv.sigmaPUnit ι)]
  exact Pi.linearIndependent_single (fun (_ : ι) (_ : Unit) ↦ (1 : R))
    <| by simp +contextual [Fintype.linearIndependent_iffₛ]

lemma linearIndependent_single_of_ne_zero {ι R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [NoZeroSMulDivisors R M] [DecidableEq ι] {v : ι → M} (hv : ∀ i, v i ≠ 0) :
    LinearIndependent R fun i : ι ↦ Pi.single i (v i) := by
  rw [← linearIndependent_equiv (Equiv.sigmaPUnit ι)]
  exact linearIndependent_single (fun i (_ : Unit) ↦ v i) <| by
    simp +contextual [Fintype.linearIndependent_iff, hv]

@[deprecated linearIndependent_single_of_ne_zero (since := "2025-04-14")]
theorem linearIndependent_single_ne_zero {ι R : Type*} [Ring R] [NoZeroDivisors R] [DecidableEq ι]
    {v : ι → R} (hv : ∀ i, v i ≠ 0) : LinearIndependent R (fun i : ι ↦ Pi.single i (v i)) :=
  linearIndependent_single_of_ne_zero hv

variable [Semiring R] [∀ i, AddCommMonoid (Ms i)] [∀ i, Module R (Ms i)]

section Fintype

variable [Fintype η]

open LinearEquiv

/-- `Pi.basis (s : ∀ j, Basis (ιs j) R (Ms j))` is the `Σ j, ιs j`-indexed basis on `Π j, Ms j`
given by `s j` on each component.

For the standard basis over `R` on the finite-dimensional space `η → R` see `Pi.basisFun`.
-/
protected noncomputable def basis (s : ∀ j, Basis (ιs j) R (Ms j)) :
    Basis (Σ j, ιs j) R (∀ j, Ms j) :=
  Basis.ofRepr
    ((LinearEquiv.piCongrRight fun j => (s j).repr) ≪≫ₗ
      (Finsupp.sigmaFinsuppLEquivPiFinsupp R).symm)

@[simp]
theorem basis_repr_single [DecidableEq η] (s : ∀ j, Basis (ιs j) R (Ms j)) (j i) :
    (Pi.basis s).repr (Pi.single j (s j i)) = Finsupp.single ⟨j, i⟩ 1 := by
  classical
  ext ⟨j', i'⟩
  by_cases hj : j = j'
  · subst hj
    simp only [Pi.basis, LinearEquiv.trans_apply, Basis.repr_self, Pi.single_eq_same,
      LinearEquiv.piCongrRight, Finsupp.sigmaFinsuppLEquivPiFinsupp_symm_apply,
      Basis.repr_symm_apply, LinearEquiv.coe_mk, ne_eq, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    symm
    simp [Finsupp.single_apply]
  simp only [Pi.basis, LinearEquiv.trans_apply, Finsupp.sigmaFinsuppLEquivPiFinsupp_symm_apply,
    LinearEquiv.piCongrRight, coe_single]
  dsimp
  rw [Pi.single_eq_of_ne (Ne.symm hj), LinearEquiv.map_zero, Finsupp.zero_apply,
    Finsupp.single_eq_of_ne]
  rintro ⟨⟩
  contradiction

@[simp]
theorem basis_apply [DecidableEq η] (s : ∀ j, Basis (ιs j) R (Ms j)) (ji) :
    Pi.basis s ji = Pi.single ji.1 (s ji.1 ji.2) :=
  Basis.apply_eq_iff.mpr (by simp)

@[simp]
theorem basis_repr (s : ∀ j, Basis (ιs j) R (Ms j)) (x) (ji) :
    (Pi.basis s).repr x ji = (s ji.1).repr (x ji.1) ji.2 :=
  rfl

end Fintype

section

variable [Finite η]
variable (R η)

/-- The basis on `η → R` where the `i`th basis vector is `Function.update 0 i 1`. -/
noncomputable def basisFun : Basis η R (η → R) :=
  Basis.ofEquivFun (LinearEquiv.refl _ _)

@[simp]
theorem basisFun_apply [DecidableEq η] (i) :
    basisFun R η i = Pi.single i 1 := by
  simp only [basisFun, Basis.coe_ofEquivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply]

@[simp]
theorem basisFun_repr (x : η → R) (i : η) : (Pi.basisFun R η).repr x i = x i := by simp [basisFun]

@[simp]
theorem basisFun_equivFun : (Pi.basisFun R η).equivFun = LinearEquiv.refl _ _ :=
  Basis.equivFun_ofEquivFun _

end

end Module

end Pi

/-- Let `k` be an integral domain and `G` an arbitrary finite set.
Then any algebra morphism `φ : (G → k) →ₐ[k] k` is an evaluation map. -/
lemma AlgHom.eq_piEvalAlgHom {k G : Type*} [CommSemiring k] [NoZeroDivisors k] [Nontrivial k]
    [Finite G] (φ : (G → k) →ₐ[k] k) : ∃ (s : G), φ = Pi.evalAlgHom _ _ s := by
  have h1 := map_one φ
  classical
  have := Fintype.ofFinite G
  simp only [← Finset.univ_sum_single (1 : G → k), Pi.one_apply, map_sum] at h1
  obtain ⟨s, hs⟩ : ∃ (s : G), φ (Pi.single s 1) ≠ 0 := by
    by_contra
    simp_all
  have h2 : ∀ t ≠ s, φ (Pi.single t 1) = 0 := by
    refine fun _ _ ↦ (eq_zero_or_eq_zero_of_mul_eq_zero ?_).resolve_left hs
    rw [← map_mul]
    convert map_zero φ
    ext u
    by_cases u = s <;> simp_all
  have h3 : φ (Pi.single s 1) = 1 := by
    rwa [Fintype.sum_eq_single s h2] at h1
  use s
  refine AlgHom.toLinearMap_injective ((Pi.basisFun k G).ext fun t ↦ ?_)
  by_cases t = s <;> simp_all

@[deprecated (since := "2025-04-15")] alias eval_of_algHom := AlgHom.eq_piEvalAlgHom

namespace Module

variable (ι R M N : Type*) [Finite ι] [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/-- The natural linear equivalence: `Mⁱ ≃ Hom(Rⁱ, M)` for an `R`-module `M`. -/
noncomputable def piEquiv : (ι → M) ≃ₗ[R] ((ι → R) →ₗ[R] M) := Basis.constr (Pi.basisFun R ι) R

lemma piEquiv_apply_apply (ι R M : Type*) [Fintype ι] [CommSemiring R]
    [AddCommMonoid M] [Module R M] (v : ι → M) (w : ι → R) :
    piEquiv ι R M v w = ∑ i, w i • v i := by
  simp only [piEquiv, Basis.constr_apply_fintype, Basis.equivFun_apply]
  congr

@[simp] lemma range_piEquiv (v : ι → M) :
    LinearMap.range (piEquiv ι R M v) = span R (range v) :=
  Basis.constr_range _ _

@[simp] lemma surjective_piEquiv_apply_iff (v : ι → M) :
    Surjective (piEquiv ι R M v) ↔ span R (range v) = ⊤ := by
  rw [← LinearMap.range_eq_top, range_piEquiv]

end Module

namespace Module.Free

variable {ι : Type*} (R : Type*) (M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

/-- The product of finitely many free modules is free. -/
instance _root_.Module.Free.pi (M : ι → Type*) [Finite ι] [∀ i : ι, AddCommMonoid (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] : Module.Free R (∀ i, M i) :=
  let ⟨_⟩ := nonempty_fintype ι
  .of_basis <| Pi.basis fun i => Module.Free.chooseBasis R (M i)

variable (ι) in
/-- The product of finitely many free modules is free (non-dependent version to help with typeclass
search). -/
instance _root_.Module.Free.function [Finite ι] [Module.Free R M] : Module.Free R (ι → M) :=
  Free.pi _ _

end Module.Free
