/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.Algebra.Algebra.Subalgebra.MulOpposite
import Mathlib.Algebra.Algebra.Subalgebra.Rank
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.LinearAlgebra.LinearDisjoint
import Mathlib.LinearAlgebra.TensorProduct.Subalgebra
import Mathlib.RingTheory.Adjoin.Dimension
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.RingTheory.Trace.Defs

/-!

# Linearly disjoint subalgebras

This file contains basics about linearly disjoint subalgebras.
We adapt the definitions in <https://en.wikipedia.org/wiki/Linearly_disjoint>.
See the file `Mathlib/LinearAlgebra/LinearDisjoint.lean` for details.

## Main definitions

- `Subalgebra.LinearDisjoint`: two subalgebras are linearly disjoint, if they are
  linearly disjoint as submodules (`Submodule.LinearDisjoint`).

- `Subalgebra.LinearDisjoint.mulMap`: if two subalgebras `A` and `B` of `S / R` are
  linearly disjoint, then there is `A ⊗[R] B ≃ₐ[R] A ⊔ B` induced by multiplication in `S`.

## Main results

### Equivalent characterization of linear disjointness

- `Subalgebra.LinearDisjoint.linearIndependent_left_of_flat`:
  if `A` and `B` are linearly disjoint, and if `B` is a flat `R`-module, then for any family of
  `R`-linearly independent elements of `A`, they are also `B`-linearly independent.

- `Subalgebra.LinearDisjoint.of_basis_left_op`:
  conversely, if a basis of `A` is also `B`-linearly independent, then `A` and `B` are
  linearly disjoint.

- `Subalgebra.LinearDisjoint.linearIndependent_right_of_flat`:
  if `A` and `B` are linearly disjoint, and if `A` is a flat `R`-module, then for any family of
  `R`-linearly independent elements of `B`, they are also `A`-linearly independent.

- `Subalgebra.LinearDisjoint.of_basis_right`:
  conversely, if a basis of `B` is also `A`-linearly independent,
  then `A` and `B` are linearly disjoint.

- `Subalgebra.LinearDisjoint.linearIndependent_mul_of_flat`:
  if `A` and `B` are linearly disjoint, and if one of `A` and `B` is flat, then for any family of
  `R`-linearly independent elements `{ a_i }` of `A`, and any family of
  `R`-linearly independent elements `{ b_j }` of `B`, the family `{ a_i * b_j }` in `S` is
  also `R`-linearly independent.

- `Subalgebra.LinearDisjoint.of_basis_mul`:
  conversely, if `{ a_i }` is an `R`-basis of `A`, if `{ b_j }` is an `R`-basis of `B`,
  such that the family `{ a_i * b_j }` in `S` is `R`-linearly independent,
  then `A` and `B` are linearly disjoint.

### Equivalent characterization by `IsDomain` or `IsField` of tensor product

The following results are related to the equivalent characterizations in
<https://mathoverflow.net/questions/8324>.

- `Subalgebra.LinearDisjoint.isDomain_of_injective`,
  `Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective`:
  under some flatness and injectivity conditions, if `A` and `B` are `R`-algebras, then `A ⊗[R] B`
  is a domain if and only if there exists an `R`-algebra which is a field that `A` and `B`
  embed into with linearly disjoint images.

- `Subalgebra.LinearDisjoint.of_isField`, `Subalgebra.LinearDisjoint.of_isField'`:
  if `A ⊗[R] B` is a field, then `A` and `B` are linearly disjoint, moreover, for any
  `R`-algebra `S` and injections of `A` and `B` into `S`, their images are linearly disjoint.

- `Algebra.TensorProduct.not_isField_of_transcendental`,
  `Algebra.TensorProduct.isAlgebraic_of_isField`:
  if `A` and `B` are flat `R`-algebras, both of them are transcendental, then `A ⊗[R] B` cannot
  be a field, equivalently, if `A ⊗[R] B` is a field, then one of them is algebraic.

### Other main results

- `Subalgebra.LinearDisjoint.symm_of_commute`, `Subalgebra.linearDisjoint_comm_of_commute`:
  linear disjointness is symmetric under some commutative conditions.

- `Subalgebra.LinearDisjoint.map`:
  linear disjointness is preserved by injective algebra homomorphisms.

- `Subalgebra.LinearDisjoint.bot_left`, `Subalgebra.LinearDisjoint.bot_right`:
  the image of `R` in `S` is linearly disjoint with any other subalgebras.

- `Subalgebra.LinearDisjoint.sup_free_of_free`: the compositum of two linearly disjoint
  subalgebras is a free module, if two subalgebras are also free modules.

- `Subalgebra.LinearDisjoint.rank_sup_of_free`,
  `Subalgebra.LinearDisjoint.finrank_sup_of_free`:
  if subalgebras `A` and `B` are linearly disjoint and they are
  free modules, then the rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`.

- `Subalgebra.LinearDisjoint.of_finrank_sup_of_free`:
  conversely, if `A` and `B` are subalgebras which are free modules of finite rank,
  such that rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`,
  then `A` and `B` are linearly disjoint.

- `Subalgebra.LinearDisjoint.adjoin_rank_eq_rank_left`:
  `Subalgebra.LinearDisjoint.adjoin_rank_eq_rank_right`:
  if `A` and `B` are linearly disjoint, if `A` is free and `B` is flat (resp. `B` is free and
  `A` is flat), then `[B[A] : B] = [A : R]` (resp. `[A[B] : A] = [B : R]`).
  See also `Subalgebra.adjoin_rank_le`.

- `Subalgebra.LinearDisjoint.of_finrank_coprime_of_free`:
  if the rank of `A` and `B` are coprime, and they satisfy some freeness condition,
  then `A` and `B` are linearly disjoint.

- `Subalgebra.LinearDisjoint.inf_eq_bot_of_commute`, `Subalgebra.LinearDisjoint.inf_eq_bot`:
  if `A` and `B` are linearly disjoint, under suitable technical conditions, they are disjoint.

The results with name containing "of_commute" also have corresponding specialized versions
assuming `S` is commutative.

## Tags

linearly disjoint, linearly independent, tensor product

-/

open Module
open scoped TensorProduct

noncomputable section

universe u v w

namespace Subalgebra

variable {R : Type u} {S : Type v}

section Semiring

variable [CommSemiring R] [Semiring S] [Algebra R S]

variable (A B : Subalgebra R S)

/-- If `A` and `B` are subalgebras of `S / R`,
then `A` and `B` are linearly disjoint, if they are linearly disjoint as submodules of `S`. -/
protected abbrev LinearDisjoint : Prop := (toSubmodule A).LinearDisjoint (toSubmodule B)

theorem linearDisjoint_iff : A.LinearDisjoint B ↔ (toSubmodule A).LinearDisjoint (toSubmodule B) :=
  Iff.rfl

variable {A B}

@[nontriviality]
theorem LinearDisjoint.of_subsingleton [Subsingleton R] : A.LinearDisjoint B :=
  Submodule.LinearDisjoint.of_subsingleton

@[nontriviality]
theorem LinearDisjoint.of_subsingleton_top [Subsingleton S] : A.LinearDisjoint B :=
  Submodule.LinearDisjoint.of_subsingleton_top

/-- Linear disjointness is symmetric if elements in the module commute. -/
theorem LinearDisjoint.symm_of_commute (H : A.LinearDisjoint B)
    (hc : ∀ (a : A) (b : B), Commute a.1 b.1) : B.LinearDisjoint A :=
  Submodule.LinearDisjoint.symm_of_commute H hc

/-- Linear disjointness is symmetric if elements in the module commute. -/
theorem linearDisjoint_comm_of_commute
    (hc : ∀ (a : A) (b : B), Commute a.1 b.1) : A.LinearDisjoint B ↔ B.LinearDisjoint A :=
  ⟨fun H ↦ H.symm_of_commute hc, fun H ↦ H.symm_of_commute fun _ _ ↦ (hc _ _).symm⟩

namespace LinearDisjoint

/-- Linear disjointness is preserved by injective algebra homomorphisms. -/
theorem map (H : A.LinearDisjoint B) {T : Type w} [Semiring T] [Algebra R T]
    (f : S →ₐ[R] T) (hf : Function.Injective f) : (A.map f).LinearDisjoint (B.map f) :=
  Submodule.LinearDisjoint.map H f hf

variable (A B)

/-- The image of `R` in `S` is linearly disjoint with any other subalgebras. -/
theorem bot_left : (⊥ : Subalgebra R S).LinearDisjoint B := by
  rw [Subalgebra.LinearDisjoint, Algebra.toSubmodule_bot]
  exact Submodule.LinearDisjoint.one_left _

/-- The image of `R` in `S` is linearly disjoint with any other subalgebras. -/
theorem bot_right : A.LinearDisjoint ⊥ := by
  rw [Subalgebra.LinearDisjoint, Algebra.toSubmodule_bot]
  exact Submodule.LinearDisjoint.one_right _

variable (R) in
/-- Images of two `R`-algebras `A` and `B` in `A ⊗[R] B` are linearly disjoint. -/
theorem include_range (A : Type v) [Semiring A] (B : Type w) [Semiring B]
    [Algebra R A] [Algebra R B] :
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).range.LinearDisjoint
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).range := by
  rw [Subalgebra.LinearDisjoint, Submodule.linearDisjoint_iff]
  change Function.Injective <|
    Submodule.mulMap (LinearMap.range Algebra.TensorProduct.includeLeft)
      (LinearMap.range Algebra.TensorProduct.includeRight)
  rw [← Algebra.TensorProduct.linearEquivIncludeRange_symm_toLinearMap]
  exact LinearEquiv.injective _

end LinearDisjoint

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring S] [Algebra R S]

variable {A B : Subalgebra R S}

/-- Linear disjointness is symmetric in a commutative ring. -/
theorem LinearDisjoint.symm (H : A.LinearDisjoint B) : B.LinearDisjoint A :=
  H.symm_of_commute fun _ _ ↦ mul_comm _ _

/-- Linear disjointness is symmetric in a commutative ring. -/
theorem linearDisjoint_comm : A.LinearDisjoint B ↔ B.LinearDisjoint A :=
  ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩

/-- Two subalgebras `A`, `B` in a commutative ring are linearly disjoint if and only if
`Subalgebra.mulMap A B` is injective. -/
theorem linearDisjoint_iff_injective : A.LinearDisjoint B ↔ Function.Injective (A.mulMap B) := by
  rw [linearDisjoint_iff, Submodule.linearDisjoint_iff]
  rfl

namespace LinearDisjoint

variable (H : A.LinearDisjoint B)

/-- If `A` and `B` are subalgebras in a commutative algebra `S` over `R`, and if they are
linearly disjoint, then there is the natural isomorphism
`A ⊗[R] B ≃ₐ[R] A ⊔ B` induced by multiplication in `S`. -/
protected def mulMap :=
  (AlgEquiv.ofInjective (A.mulMap B) H.injective).trans (equivOfEq _ _ (mulMap_range A B))

@[simp]
theorem val_mulMap_tmul (a : A) (b : B) : (H.mulMap (a ⊗ₜ[R] b) : S) = a.1 * b.1 := rfl

/--
If `A` and `B` are linearly disjoint subalgebras in a commutative algebra `S` over `R`
such that `A ⊔ B = S`, then this is the natural isomorphism
`A ⊗[R] B ≃ₐ[A] S` induced by multiplication in `S`.
-/
noncomputable def mulMapLeftOfSupEqTop (H' : A ⊔ B = ⊤) :
    A ⊗[R] B ≃ₐ[A] S :=
  (AlgEquiv.ofInjective (Algebra.TensorProduct.productLeftAlgHom
    (Algebra.ofId A S) B.val) H.injective).trans ((Subalgebra.equivOfEq _ _ (by
      apply Subalgebra.restrictScalars_injective R
      rw [restrictScalars_top, ← H']
      exact mulMap_range A B)).trans Subalgebra.topEquiv)

@[simp]
theorem mulMapLeftOfSupEqTop_tmul (H' : A ⊔ B = ⊤) (a : A) (b : B) :
    H.mulMapLeftOfSupEqTop H' (a ⊗ₜ[R] b) = (a : S) * (b : S) := rfl

/--
If `A` and `B` are linearly disjoint subalgebras in a commutative algebra `S` over `R`
such that `A ⊔ B = S`, then any `R`-basis of `B` is also an `A`-basis of `S`.
-/
noncomputable def basisOfBasisRight (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R B) :
    Basis ι A S :=
  (b.baseChange A).map (H.mulMapLeftOfSupEqTop H').toLinearEquiv

@[simp]
theorem algebraMap_basisOfBasisRight_apply (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R B) (i : ι) :
    H.basisOfBasisRight H' b i = algebraMap B S (b i) := by
  simp [basisOfBasisRight, Subalgebra.algebraMap_def]

@[simp]
theorem mulMapLeftOfSupEqTop_symm_apply (H' : A ⊔ B = ⊤) (x : B) :
    (H.mulMapLeftOfSupEqTop H').symm x = 1 ⊗ₜ[R] x :=
  (H.mulMapLeftOfSupEqTop H').symm_apply_eq.mpr (by simp)

theorem algebraMap_basisOfBasisRight_repr_apply (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R B)
    (x : B) (i : ι) :
    algebraMap A S ((H.basisOfBasisRight H' b).repr x i) = algebraMap R S (b.repr x i) := by
  simp [basisOfBasisRight, Algebra.algebraMap_eq_smul_one]

theorem leftMulMatrix_basisOfBasisRight_algebraMap (H' : A ⊔ B = ⊤) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι R B) (x : B) :
    Algebra.leftMulMatrix (H.basisOfBasisRight H' b) (algebraMap B S x) =
      RingHom.mapMatrix (algebraMap R A) (Algebra.leftMulMatrix b x) := by
  ext
  simp [Algebra.leftMulMatrix_eq_repr_mul, ← H.algebraMap_basisOfBasisRight_repr_apply H',
    Subalgebra.algebraMap_def]

/--
If `A` and `B` are subalgebras in a commutative algebra `S` over `R`, and if they are
linearly disjoint and such that `A ⊔ B = S`, then any `R`-basis of `A` is also a `B`-basis of `S`.
-/
noncomputable def basisOfBasisLeft (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R A) :
    Basis ι B S :=
  (b.baseChange B).map (H.symm.mulMapLeftOfSupEqTop (by rwa [sup_comm])).toLinearEquiv

@[simp]
theorem basisOfBasisLeft_apply (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R A) (i : ι) :
    H.basisOfBasisLeft H' b i = algebraMap A S (b i) :=
  H.symm.algebraMap_basisOfBasisRight_apply (by rwa [sup_comm]) b i

theorem basisOfBasisLeft_repr_apply (H' : A ⊔ B = ⊤) {ι : Type*} (b : Basis ι R A)
    (x : A) (i : ι) :
    algebraMap B S ((H.basisOfBasisLeft H' b).repr x i) = algebraMap R S (b.repr x i) :=
  H.symm.algebraMap_basisOfBasisRight_repr_apply (by rwa [sup_comm]) b x i

include H in
/-- If `A` and `B` are subalgebras in a commutative algebra `S` over `R`, and if they are
linearly disjoint, and if they are free `R`-modules, then `A ⊔ B` is also a free `R`-module. -/
theorem sup_free_of_free [Module.Free R A] [Module.Free R B] : Module.Free R ↥(A ⊔ B) :=
  Module.Free.of_equiv H.mulMap.toLinearEquiv

include H in
/-- If `A` and `B` are subalgebras in a domain `S` over `R`, and if they are
linearly disjoint, then `A ⊗[R] B` is also a domain. -/
theorem isDomain [IsDomain S] : IsDomain (A ⊗[R] B) :=
  H.injective.isDomain (A.mulMap B).toRingHom

/-- If `A` and `B` are `R`-algebras, such that there exists a domain `S` over `R`
such that `A` and `B` inject into it and their images are linearly disjoint,
then `A ⊗[R] B` is also a domain. -/
theorem isDomain_of_injective [IsDomain S] {A B : Type*} [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] {fa : A →ₐ[R] S} {fb : B →ₐ[R] S}
    (hfa : Function.Injective fa) (hfb : Function.Injective fb)
    (H : fa.range.LinearDisjoint fb.range) : IsDomain (A ⊗[R] B) :=
  have := H.isDomain
  (Algebra.TensorProduct.congr
    (AlgEquiv.ofInjective fa hfa) (AlgEquiv.ofInjective fb hfb)).toMulEquiv.isDomain

end LinearDisjoint

end CommSemiring

section Ring

namespace LinearDisjoint

variable [CommRing R] [Ring S] [Algebra R S]

variable (A B : Subalgebra R S)

lemma mulLeftMap_ker_eq_bot_iff_linearIndependent_op {ι : Type*} (a : ι → A) :
    LinearMap.ker (Submodule.mulLeftMap (M := toSubmodule A) (toSubmodule B) a) = ⊥ ↔
    LinearIndependent B.op (MulOpposite.op ∘ A.val ∘ a) := by
  simp_rw [LinearIndependent, LinearMap.ker_eq_bot]
  let i : (ι →₀ B) →ₗ[R] S := Submodule.mulLeftMap (M := toSubmodule A) (toSubmodule B) a
  let j : (ι →₀ B) →ₗ[R] S := (MulOpposite.opLinearEquiv _).symm.toLinearMap ∘ₗ
    (Finsupp.linearCombination B.op (MulOpposite.op ∘ A.val ∘ a)).restrictScalars R ∘ₗ
    (Finsupp.mapRange.linearEquiv (linearEquivOp B)).toLinearMap
  suffices i = j by
    change Function.Injective i ↔ _
    simp_rw [this, j, LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_injective,
      EquivLike.injective_comp, LinearMap.coe_restrictScalars]
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, coe_val,
    Finsupp.mapRange.linearEquiv_toLinearMap, LinearEquiv.coe_coe,
    MulOpposite.coe_opLinearEquiv_symm, LinearMap.coe_restrictScalars,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Finsupp.linearCombination_single,
    MulOpposite.unop_smul, MulOpposite.unop_op, i, j]
  exact Submodule.mulLeftMap_apply_single _ _ _

variable {A B} in
/-- If `A` and `B` are linearly disjoint, if `B` is a flat `R`-module, then for any family of
`R`-linearly independent elements of `A`, they are also `B`-linearly independent
in the opposite ring. -/
theorem linearIndependent_left_op_of_flat (H : A.LinearDisjoint B) [Module.Flat R B]
    {ι : Type*} {a : ι → A} (ha : LinearIndependent R a) :
    LinearIndependent B.op (MulOpposite.op ∘ A.val ∘ a) := by
  have h := Submodule.LinearDisjoint.linearIndependent_left_of_flat H ha
  rwa [mulLeftMap_ker_eq_bot_iff_linearIndependent_op] at h

/-- If a basis of `A` is also `B`-linearly independent in the opposite ring,
then `A` and `B` are linearly disjoint. -/
theorem of_basis_left_op {ι : Type*} (a : Basis ι R A)
    (H : LinearIndependent B.op (MulOpposite.op ∘ A.val ∘ a)) :
    A.LinearDisjoint B := by
  rw [← mulLeftMap_ker_eq_bot_iff_linearIndependent_op] at H
  exact Submodule.LinearDisjoint.of_basis_left _ _ a H

lemma mulRightMap_ker_eq_bot_iff_linearIndependent {ι : Type*} (b : ι → B) :
    LinearMap.ker (Submodule.mulRightMap (toSubmodule A) (N := toSubmodule B) b) = ⊥ ↔
    LinearIndependent A (B.val ∘ b) := by
  simp_rw [LinearIndependent, LinearMap.ker_eq_bot]
  let i : (ι →₀ A) →ₗ[R] S := Submodule.mulRightMap (toSubmodule A) (N := toSubmodule B) b
  let j : (ι →₀ A) →ₗ[R] S := (Finsupp.linearCombination A (B.val ∘ b)).restrictScalars R
  suffices i = j by change Function.Injective i ↔ Function.Injective j; rw [this]
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, coe_val,
    LinearMap.coe_restrictScalars, Finsupp.linearCombination_single, i, j]
  exact Submodule.mulRightMap_apply_single _ _ _

variable {A B} in
/-- If `A` and `B` are linearly disjoint, if `A` is a flat `R`-module, then for any family of
`R`-linearly independent elements of `B`, they are also `A`-linearly independent. -/
theorem linearIndependent_right_of_flat (H : A.LinearDisjoint B) [Module.Flat R A]
    {ι : Type*} {b : ι → B} (hb : LinearIndependent R b) :
    LinearIndependent A (B.val ∘ b) := by
  have h := Submodule.LinearDisjoint.linearIndependent_right_of_flat H hb
  rwa [mulRightMap_ker_eq_bot_iff_linearIndependent] at h

/-- If a basis of `B` is also `A`-linearly independent, then `A` and `B` are linearly disjoint. -/
theorem of_basis_right {ι : Type*} (b : Basis ι R B)
    (H : LinearIndependent A (B.val ∘ b)) : A.LinearDisjoint B := by
  rw [← mulRightMap_ker_eq_bot_iff_linearIndependent] at H
  exact Submodule.LinearDisjoint.of_basis_right _ _ b H

variable {A B} in
/-- If `A` and `B` are linearly disjoint and their elements commute, if `B` is a flat `R`-module,
then for any family of `R`-linearly independent elements of `A`,
they are also `B`-linearly independent. -/
theorem linearIndependent_left_of_flat_of_commute (H : A.LinearDisjoint B) [Module.Flat R B]
    {ι : Type*} {a : ι → A} (ha : LinearIndependent R a)
    (hc : ∀ (a : A) (b : B), Commute a.1 b.1) : LinearIndependent B (A.val ∘ a) :=
  (H.symm_of_commute hc).linearIndependent_right_of_flat ha

/-- If a basis of `A` is also `B`-linearly independent, if elements in `A` and `B` commute,
then `A` and `B` are linearly disjoint. -/
theorem of_basis_left_of_commute {ι : Type*} (a : Basis ι R A)
    (H : LinearIndependent B (A.val ∘ a)) (hc : ∀ (a : A) (b : B), Commute a.1 b.1) :
    A.LinearDisjoint B :=
  (of_basis_right B A a H).symm_of_commute fun _ _ ↦ (hc _ _).symm

variable {A B} in
/-- If `A` and `B` are linearly disjoint, if `A` is flat, then for any family of
`R`-linearly independent elements `{ a_i }` of `A`, and any family of
`R`-linearly independent elements `{ b_j }` of `B`, the family `{ a_i * b_j }` in `S` is
also `R`-linearly independent. -/
theorem linearIndependent_mul_of_flat_left (H : A.LinearDisjoint B) [Module.Flat R A]
    {κ ι : Type*} {a : κ → A} {b : ι → B} (ha : LinearIndependent R a)
    (hb : LinearIndependent R b) : LinearIndependent R fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1 :=
  Submodule.LinearDisjoint.linearIndependent_mul_of_flat_left H ha hb

variable {A B} in
/-- If `A` and `B` are linearly disjoint, if `B` is flat, then for any family of
`R`-linearly independent elements `{ a_i }` of `A`, and any family of
`R`-linearly independent elements `{ b_j }` of `B`, the family `{ a_i * b_j }` in `S` is
also `R`-linearly independent. -/
theorem linearIndependent_mul_of_flat_right (H : A.LinearDisjoint B) [Module.Flat R B]
    {κ ι : Type*} {a : κ → A} {b : ι → B} (ha : LinearIndependent R a)
    (hb : LinearIndependent R b) : LinearIndependent R fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1 :=
  Submodule.LinearDisjoint.linearIndependent_mul_of_flat_right H ha hb

variable {A B} in
/-- If `A` and `B` are linearly disjoint, if one of `A` and `B` is flat, then for any family of
`R`-linearly independent elements `{ a_i }` of `A`, and any family of
`R`-linearly independent elements `{ b_j }` of `B`, the family `{ a_i * b_j }` in `S` is
also `R`-linearly independent. -/
theorem linearIndependent_mul_of_flat (H : A.LinearDisjoint B)
    (hf : Module.Flat R A ∨ Module.Flat R B)
    {κ ι : Type*} {a : κ → A} {b : ι → B} (ha : LinearIndependent R a)
    (hb : LinearIndependent R b) : LinearIndependent R fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1 :=
  Submodule.LinearDisjoint.linearIndependent_mul_of_flat H hf ha hb

/-- If `{ a_i }` is an `R`-basis of `A`, if `{ b_j }` is an `R`-basis of `B`,
such that the family `{ a_i * b_j }` in `S` is `R`-linearly independent,
then `A` and `B` are linearly disjoint. -/
theorem of_basis_mul {κ ι : Type*} (a : Basis κ R A) (b : Basis ι R B)
    (H : LinearIndependent R fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1) : A.LinearDisjoint B :=
  Submodule.LinearDisjoint.of_basis_mul _ _ a b H

variable {A B}

section

variable (H : A.LinearDisjoint B)
include H

theorem of_le_left_of_flat {A' : Subalgebra R S}
    (h : A' ≤ A) [Module.Flat R B] : A'.LinearDisjoint B :=
  Submodule.LinearDisjoint.of_le_left_of_flat H h

theorem of_le_right_of_flat {B' : Subalgebra R S}
    (h : B' ≤ B) [Module.Flat R A] : A.LinearDisjoint B' :=
  Submodule.LinearDisjoint.of_le_right_of_flat H h

theorem of_le_of_flat_right {A' B' : Subalgebra R S}
    (ha : A' ≤ A) (hb : B' ≤ B) [Module.Flat R B] [Module.Flat R A'] :
    A'.LinearDisjoint B' := (H.of_le_left_of_flat ha).of_le_right_of_flat hb

theorem of_le_of_flat_left {A' B' : Subalgebra R S}
    (ha : A' ≤ A) (hb : B' ≤ B) [Module.Flat R A] [Module.Flat R B'] :
    A'.LinearDisjoint B' := (H.of_le_right_of_flat hb).of_le_left_of_flat ha

theorem rank_inf_eq_one_of_commute_of_flat_of_inj (hf : Module.Flat R A ∨ Module.Flat R B)
    (hc : ∀ (a b : ↥(A ⊓ B)), Commute a.1 b.1)
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 := by
  nontriviality R
  refine le_antisymm (Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat H hf hc) ?_
  have : Cardinal.lift.{u} (Module.rank R (⊥ : Subalgebra R S)) =
      Cardinal.lift.{v} (Module.rank R R) :=
    lift_rank_range_of_injective (Algebra.linearMap R S) hinj
  rw [Module.rank_self, Cardinal.lift_one, Cardinal.lift_eq_one] at this
  rw [← this]
  change Module.rank R (toSubmodule (⊥ : Subalgebra R S)) ≤
    Module.rank R (toSubmodule (A ⊓ B))
  exact Submodule.rank_mono (bot_le : (⊥ : Subalgebra R S) ≤ A ⊓ B)

theorem rank_inf_eq_one_of_commute_of_flat_left_of_inj [Module.Flat R A]
    (hc : ∀ (a b : ↥(A ⊓ B)), Commute a.1 b.1)
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 :=
  H.rank_inf_eq_one_of_commute_of_flat_of_inj (Or.inl ‹_›) hc hinj

theorem rank_inf_eq_one_of_commute_of_flat_right_of_inj [Module.Flat R B]
    (hc : ∀ (a b : ↥(A ⊓ B)), Commute a.1 b.1)
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 :=
  H.rank_inf_eq_one_of_commute_of_flat_of_inj (Or.inr ‹_›) hc hinj

end

theorem rank_eq_one_of_commute_of_flat_of_self_of_inj (H : A.LinearDisjoint A) [Module.Flat R A]
    (hc : ∀ (a b : A), Commute a.1 b.1)
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R A = 1 := by
  rw [← inf_of_le_left (le_refl A)] at hc ⊢
  exact H.rank_inf_eq_one_of_commute_of_flat_left_of_inj hc hinj

end LinearDisjoint

end Ring

section CommRing

namespace LinearDisjoint

variable [CommRing R] [CommRing S] [Algebra R S]

variable {A B : Subalgebra R S}

/--
If `A` and `B` are subalgebras in a commutative algebra `S` over `R`, and if they are
linearly disjoint and such that `A ⊔ B = S`, then `trace` and `algebraMap` commutes.
-/
theorem trace_algebraMap (H : A.LinearDisjoint B) (H' : A ⊔ B = ⊤) [Module.Free R B]
    [Module.Finite R B] (x : B) :
    Algebra.trace A S (algebraMap B S x) = algebraMap R A (Algebra.trace R B x) := by
  simp_rw [Algebra.trace_eq_matrix_trace (Module.Free.chooseBasis R B),
    Algebra.trace_eq_matrix_trace (H.basisOfBasisRight H' (Module.Free.chooseBasis R B)),
    Matrix.trace, map_sum, leftMulMatrix_basisOfBasisRight_algebraMap, RingHom.mapMatrix_apply,
    Matrix.diag_apply, Matrix.map_apply]

/--
If `A` and `B` are subalgebras in a commutative algebra `S` over `R`, and if they are
linearly disjoint and such that `A ⊔ B = S`, then `norm` and `algebraMap` commutes.
-/
theorem norm_algebraMap (H : A.LinearDisjoint B) (H' : A ⊔ B = ⊤) [Module.Free R B]
    [Module.Finite R B] (x : B) :
    Algebra.norm A (algebraMap B S x) = algebraMap R A (Algebra.norm R x) := by
  simp_rw [Algebra.norm_eq_matrix_det (Module.Free.chooseBasis R B),
    Algebra.norm_eq_matrix_det (H.basisOfBasisRight H' (Module.Free.chooseBasis R B)),
    leftMulMatrix_basisOfBasisRight_algebraMap, RingHom.map_det]

/-- In a commutative ring, if `A` and `B` are linearly disjoint, if `B` is a flat `R`-module,
then for any family of `R`-linearly independent elements of `A`,
they are also `B`-linearly independent. -/
theorem linearIndependent_left_of_flat (H : A.LinearDisjoint B) [Module.Flat R B]
    {ι : Type*} {a : ι → A} (ha : LinearIndependent R a) : LinearIndependent B (A.val ∘ a) :=
  H.linearIndependent_left_of_flat_of_commute ha fun _ _ ↦ mul_comm _ _

variable (A B) in
/-- In a commutative ring, if a basis of `A` is also `B`-linearly independent,
then `A` and `B` are linearly disjoint. -/
theorem of_basis_left {ι : Type*} (a : Basis ι R A)
    (H : LinearIndependent B (A.val ∘ a)) : A.LinearDisjoint B :=
  of_basis_left_of_commute A B a H fun _ _ ↦ mul_comm _ _

variable (R) in
/-- If `A` and `B` are flat algebras over `R`, such that `A ⊗[R] B` is a domain, and such that
the algebra maps are injective, then there exists an `R`-algebra `K` that is a field that `A`
and `B` inject into with linearly disjoint images. Note: `K` can chosen to be the
fraction field of `A ⊗[R] B`, but here we hide this fact. -/
theorem exists_field_of_isDomain_of_injective (A : Type v) [CommRing A] (B : Type w) [CommRing B]
    [Algebra R A] [Algebra R B] [Module.Flat R A] [Module.Flat R B] [IsDomain (A ⊗[R] B)]
    (ha : Function.Injective (algebraMap R A)) (hb : Function.Injective (algebraMap R B)) :
    ∃ (K : Type (max v w)) (_ : Field K) (_ : Algebra R K) (fa : A →ₐ[R] K) (fb : B →ₐ[R] K),
    Function.Injective fa ∧ Function.Injective fb ∧ fa.range.LinearDisjoint fb.range :=
  let K := FractionRing (A ⊗[R] B)
  let i := IsScalarTower.toAlgHom R (A ⊗[R] B) K
  have hi : Function.Injective i := IsFractionRing.injective (A ⊗[R] B) K
  ⟨K, inferInstance, inferInstance,
    i.comp Algebra.TensorProduct.includeLeft,
    i.comp Algebra.TensorProduct.includeRight,
    hi.comp (Algebra.TensorProduct.includeLeft_injective hb),
    hi.comp (Algebra.TensorProduct.includeRight_injective ha), by
      simpa only [AlgHom.range_comp] using (include_range R A B).map i hi⟩

/-- If `A ⊗[R] B` is a field, then `A` and `B` are linearly disjoint. -/
theorem of_isField (H : IsField (A ⊗[R] B)) : A.LinearDisjoint B := by
  nontriviality S
  rw [linearDisjoint_iff_injective]
  letI : Field (A ⊗[R] B) := H.toField
  -- need this otherwise `RingHom.injective` does not work
  letI : NonAssocRing (A ⊗[R] B) := Ring.toNonAssocRing
  exact RingHom.injective _

/-- If `A ⊗[R] B` is a field, then for any `R`-algebra `S`
and injections of `A` and `B` into `S`, their images are linearly disjoint. -/
theorem of_isField' {A : Type v} [Ring A] {B : Type w} [Ring B]
    [Algebra R A] [Algebra R B] (H : IsField (A ⊗[R] B))
    (fa : A →ₐ[R] S) (fb : B →ₐ[R] S) (hfa : Function.Injective fa) (hfb : Function.Injective fb) :
    fa.range.LinearDisjoint fb.range := by
  apply of_isField
  exact Algebra.TensorProduct.congr (AlgEquiv.ofInjective fa hfa)
    (AlgEquiv.ofInjective fb hfb) |>.symm.toMulEquiv.isField H

-- need to be in this file since it uses linearly disjoint
open Cardinal Polynomial in
variable (R) in
/-- If `A` and `B` are flat `R`-algebras, both of them are transcendental, then `A ⊗[R] B` cannot
be a field. -/
theorem _root_.Algebra.TensorProduct.not_isField_of_transcendental
    (A : Type v) [CommRing A] (B : Type w) [CommRing B] [Algebra R A] [Algebra R B]
    [Module.Flat R A] [Module.Flat R B] [Algebra.Transcendental R A] [Algebra.Transcendental R B] :
    ¬IsField (A ⊗[R] B) := fun H ↦ by
  letI := H.toField
  obtain ⟨a, hta⟩ := ‹Algebra.Transcendental R A›
  obtain ⟨b, htb⟩ := ‹Algebra.Transcendental R B›
  have ha : Function.Injective (algebraMap R A) := Algebra.injective_of_transcendental
  have hb : Function.Injective (algebraMap R B) := Algebra.injective_of_transcendental
  let fa : A →ₐ[R] A ⊗[R] B := Algebra.TensorProduct.includeLeft
  let fb : B →ₐ[R] A ⊗[R] B := Algebra.TensorProduct.includeRight
  have hfa : Function.Injective fa := Algebra.TensorProduct.includeLeft_injective hb
  have hfb : Function.Injective fb := Algebra.TensorProduct.includeRight_injective ha
  haveI := hfa.isDomain fa.toRingHom
  haveI := hfb.isDomain fb.toRingHom
  haveI := ha.isDomain _
  haveI : Module.Flat R (toSubmodule fa.range) :=
    .of_linearEquiv (AlgEquiv.ofInjective fa hfa).symm.toLinearEquiv
  have key1 : Module.rank R ↥(fa.range ⊓ fb.range) ≤ 1 :=
    (include_range R A B).rank_inf_le_one_of_flat_left
  let ga : R[X] →ₐ[R] A := aeval a
  let gb : R[X] →ₐ[R] B := aeval b
  let gab := fa.comp ga
  replace hta : Function.Injective ga := transcendental_iff_injective.1 hta
  replace htb : Function.Injective gb := transcendental_iff_injective.1 htb
  have htab : Function.Injective gab := hfa.comp hta
  algebraize_only [ga.toRingHom, gb.toRingHom]
  let f := Algebra.TensorProduct.mapOfCompatibleSMul R[X] R A B
  haveI := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain R[X] A B hta htb
  have hf : Function.Injective f := RingHom.injective _
  have key2 : gab.range ≤ fa.range ⊓ fb.range := by
    simp_rw [gab, ga, ← aeval_algHom]
    rw [Algebra.TensorProduct.includeLeft_apply, ← Algebra.adjoin_singleton_eq_range_aeval]
    simp_rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff, Algebra.coe_inf, Set.mem_inter_iff,
      AlgHom.coe_range, Set.mem_range]
    refine ⟨⟨a, by simp [fa]⟩, ⟨b, hf ?_⟩⟩
    simp_rw [fb, Algebra.TensorProduct.includeRight_apply, f,
      Algebra.TensorProduct.mapOfCompatibleSMul_tmul]
    convert ← (TensorProduct.smul_tmul (R := R[X]) (R' := R[X]) (M := A) (N := B) X 1 1).symm <;>
      (simp_rw [Algebra.smul_def, mul_one]; exact aeval_X _)
  have key3 := (Subalgebra.inclusion key2).comp (AlgEquiv.ofInjective gab htab).toAlgHom
    |>.toLinearMap.lift_rank_le_of_injective
      ((Subalgebra.inclusion_injective key2).comp (AlgEquiv.injective _))
  have := lift_uzero.{u} _ ▸ (basisMonomials R).mk_eq_rank.symm
  simp only [this, mk_eq_aleph0, lift_aleph0, aleph0_le_lift] at key3
  exact (key3.trans key1).not_gt one_lt_aleph0

variable (R) in
/-- If `A` and `B` are flat `R`-algebras, such that `A ⊗[R] B` is a field, then one of `A` and `B`
is algebraic over `R`. -/
theorem _root_.Algebra.TensorProduct.isAlgebraic_of_isField
    (A : Type v) [CommRing A] (B : Type w) [CommRing B] [Algebra R A] [Algebra R B]
    [Module.Flat R A] [Module.Flat R B] (H : IsField (A ⊗[R] B)) :
    Algebra.IsAlgebraic R A ∨ Algebra.IsAlgebraic R B := by
  by_contra! h
  simp_rw [← Algebra.transcendental_iff_not_isAlgebraic] at h
  obtain ⟨_, _⟩ := h
  exact Algebra.TensorProduct.not_isField_of_transcendental R A B H

variable (H : A.LinearDisjoint B)

include H in
theorem rank_inf_eq_one_of_flat_of_inj (hf : Module.Flat R A ∨ Module.Flat R B)
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 :=
  H.rank_inf_eq_one_of_commute_of_flat_of_inj hf (fun _ _ ↦ mul_comm _ _) hinj

include H in
theorem rank_inf_eq_one_of_flat_left_of_inj [Module.Flat R A]
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 :=
  H.rank_inf_eq_one_of_commute_of_flat_left_of_inj (fun _ _ ↦ mul_comm _ _) hinj

include H in
theorem rank_inf_eq_one_of_flat_right_of_inj [Module.Flat R B]
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 :=
  H.rank_inf_eq_one_of_commute_of_flat_right_of_inj (fun _ _ ↦ mul_comm _ _) hinj

theorem rank_eq_one_of_flat_of_self_of_inj (H : A.LinearDisjoint A) [Module.Flat R A]
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R A = 1 :=
  H.rank_eq_one_of_commute_of_flat_of_self_of_inj (fun _ _ ↦ mul_comm _ _) hinj

include H in
/-- In a commutative ring, if subalgebras `A` and `B` are linearly disjoint and they are
free modules, then the rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`. -/
theorem rank_sup_of_free [Module.Free R A] [Module.Free R B] :
    Module.rank R ↥(A ⊔ B) = Module.rank R A * Module.rank R B := by
  nontriviality R
  rw [← rank_tensorProduct', H.mulMap.toLinearEquiv.rank_eq]

include H in
/-- In a commutative ring, if subalgebras `A` and `B` are linearly disjoint and they are
free modules, then the rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`. -/
theorem finrank_sup_of_free [Module.Free R A] [Module.Free R B] :
    Module.finrank R ↥(A ⊔ B) = Module.finrank R A * Module.finrank R B := by
  simpa only [map_mul] using congr(Cardinal.toNat $(H.rank_sup_of_free))

/-- In a commutative ring, if `A` and `B` are subalgebras which are free modules of finite rank,
such that rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`,
then `A` and `B` are linearly disjoint. -/
theorem of_finrank_sup_of_free [Module.Free R A] [Module.Free R B]
    [Module.Finite R A] [Module.Finite R B]
    (H : Module.finrank R ↥(A ⊔ B) = Module.finrank R A * Module.finrank R B) :
    A.LinearDisjoint B := by
  nontriviality R
  rw [← Module.finrank_tensorProduct] at H
  obtain ⟨j, hj⟩ := exists_linearIndependent_of_le_finrank H.ge
  rw [LinearIndependent] at hj
  let j' := Finsupp.linearCombination R j ∘ₗ
    (LinearEquiv.ofFinrankEq (A ⊗[R] B) _ (by simp)).toLinearMap
  replace hj : Function.Injective j' := by simpa [j']
  have hf : Function.Surjective (mulMap' A B).toLinearMap := mulMap'_surjective A B
  haveI := Subalgebra.finite_sup A B
  rw [linearDisjoint_iff, Submodule.linearDisjoint_iff]
  exact Subtype.val_injective.comp (OrzechProperty.injective_of_surjective_of_injective j' _ hj hf)

include H in
/-- If `A` and `B` are linearly disjoint, if `A` is free and `B` is flat,
then `[B[A] : B] = [A : R]`. See also `Subalgebra.adjoin_rank_le`. -/
theorem adjoin_rank_eq_rank_left [Module.Free R A] [Module.Flat R B]
    [Nontrivial R] [Nontrivial S] :
    Module.rank B (Algebra.adjoin B (A : Set S)) = Module.rank R A := by
  rw [← rank_toSubmodule, Module.Free.rank_eq_card_chooseBasisIndex R A,
    A.adjoin_eq_span_basis B (Module.Free.chooseBasis R A)]
  change Module.rank B (Submodule.span B (Set.range (A.val ∘ Module.Free.chooseBasis R A))) = _
  have := H.linearIndependent_left_of_flat (Module.Free.chooseBasis R A).linearIndependent
  rw [rank_span this, Cardinal.mk_range_eq _ this.injective]

include H in
/-- If `A` and `B` are linearly disjoint, if `B` is free and `A` is flat,
then `[A[B] : A] = [B : R]`. See also `Subalgebra.adjoin_rank_le`. -/
theorem adjoin_rank_eq_rank_right [Module.Free R B] [Module.Flat R A]
    [Nontrivial R] [Nontrivial S] :
    Module.rank A (Algebra.adjoin A (B : Set S)) = Module.rank R B :=
  H.symm.adjoin_rank_eq_rank_left

/-- If the rank of `A` and `B` are coprime, and they satisfy some freeness condition,
then `A` and `B` are linearly disjoint. -/
theorem of_finrank_coprime_of_free [Module.Free R A] [Module.Free R B]
    [Module.Free A (Algebra.adjoin A (B : Set S))] [Module.Free B (Algebra.adjoin B (A : Set S))]
    (H : (Module.finrank R A).Coprime (Module.finrank R B)) : A.LinearDisjoint B := by
  nontriviality R
  by_cases h1 : Module.finrank R A = 0
  · rw [h1, Nat.coprime_zero_left] at H
    rw [eq_bot_of_finrank_one H]
    exact bot_right _
  by_cases h2 : Module.finrank R B = 0
  · rw [h2, Nat.coprime_zero_right] at H
    rw [eq_bot_of_finrank_one H]
    exact bot_left _
  haveI := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h1)
  haveI := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h2)
  haveI := finite_sup A B
  have : Module.finrank R A ≤ Module.finrank R ↥(A ⊔ B) :=
    LinearMap.finrank_le_finrank_of_injective <|
      Submodule.inclusion_injective (show toSubmodule A ≤ toSubmodule (A ⊔ B) by simp)
  exact of_finrank_sup_of_free <| (finrank_sup_le_of_free A B).antisymm <|
    Nat.le_of_dvd (lt_of_lt_of_le (Nat.pos_of_ne_zero h1) this) <| H.mul_dvd_of_dvd_of_dvd
      (finrank_left_dvd_finrank_sup_of_free A B) (finrank_right_dvd_finrank_sup_of_free A B)

variable (A B)

/-- If `A/R` is integral, such that `A'` and `B` are linearly disjoint for all subalgebras `A'`
of `A` which are finitely generated `R`-modules, then `A` and `B` are linearly disjoint. -/
theorem of_linearDisjoint_finite_left [Algebra.IsIntegral R A]
    (H : ∀ A' : Subalgebra R S, A' ≤ A → [Module.Finite R A'] → A'.LinearDisjoint B) :
    A.LinearDisjoint B := by
  rw [linearDisjoint_iff, Submodule.linearDisjoint_iff]
  intro x y hxy
  obtain ⟨M', hM, hf, h⟩ :=
    TensorProduct.exists_finite_submodule_left_of_finite' {x, y} (Set.toFinite _)
  obtain ⟨s, hs⟩ := Module.Finite.iff_fg.1 hf
  have hs' : (s : Set S) ⊆ A := by rwa [← hs, Submodule.span_le] at hM
  let A' := Algebra.adjoin R (s : Set S)
  have hf' : Submodule.FG (toSubmodule A') := fg_adjoin_of_finite s.finite_toSet fun x hx ↦
    (isIntegral_algHom_iff A.val Subtype.val_injective).2
      (Algebra.IsIntegral.isIntegral (R := R) (A := A) ⟨x, hs' hx⟩)
  replace hf' : Module.Finite R A' := Module.Finite.iff_fg.2 hf'
  have hA : toSubmodule A' ≤ toSubmodule A := Algebra.adjoin_le_iff.2 hs'
  replace h : {x, y} ⊆ (LinearMap.range (LinearMap.rTensor (toSubmodule B)
      (Submodule.inclusion hA)) : Set _) := fun _ hx ↦ by
    have : Submodule.inclusion hM = Submodule.inclusion hA ∘ₗ Submodule.inclusion
      (show M' ≤ toSubmodule A' by
        rw [← hs, Submodule.span_le]; exact Algebra.adjoin_le_iff.1 (le_refl _)) := rfl
    rw [this, LinearMap.rTensor_comp] at h
    exact LinearMap.range_comp_le_range _ _ (h hx)
  obtain ⟨x', hx'⟩ := h (show x ∈ {x, y} by simp)
  obtain ⟨y', hy'⟩ := h (show y ∈ {x, y} by simp)
  rw [← hx', ← hy']; congr
  exact (H A' hA).injective (by simp [← Submodule.mulMap_comp_rTensor _ hA, hx', hy', hxy])

/-- If `B/R` is integral, such that `A` and `B'` are linearly disjoint for all subalgebras `B'`
of `B` which are finitely generated `R`-modules, then `A` and `B` are linearly disjoint. -/
theorem of_linearDisjoint_finite_right [Algebra.IsIntegral R B]
    (H : ∀ B' : Subalgebra R S, B' ≤ B → [Module.Finite R B'] → A.LinearDisjoint B') :
    A.LinearDisjoint B :=
  (of_linearDisjoint_finite_left B A fun B' hB' _ ↦ (H B' hB').symm).symm

variable {A B}

/-- If `A/R` and `B/R` are integral, such that any finite subalgebras in `A` and `B` are
linearly disjoint, then `A` and `B` are linearly disjoint. -/
theorem of_linearDisjoint_finite
    [Algebra.IsIntegral R A] [Algebra.IsIntegral R B]
    (H : ∀ (A' B' : Subalgebra R S), A' ≤ A → B' ≤ B →
      [Module.Finite R A'] → [Module.Finite R B'] → A'.LinearDisjoint B') :
    A.LinearDisjoint B :=
  of_linearDisjoint_finite_left A B fun _ hA' _ ↦
    of_linearDisjoint_finite_right _ B fun _ hB' _ ↦ H _ _ hA' hB'

end LinearDisjoint

end CommRing

section FieldAndRing

namespace LinearDisjoint

variable [Field R] [Ring S] [Algebra R S]

variable {A B : Subalgebra R S}

theorem inf_eq_bot_of_commute (H : A.LinearDisjoint B)
    (hc : ∀ (a b : ↥(A ⊓ B)), Commute a.1 b.1) : A ⊓ B = ⊥ :=
  eq_bot_of_rank_le_one (Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat_left H hc)

theorem eq_bot_of_commute_of_self (H : A.LinearDisjoint A)
    (hc : ∀ (a b : A), Commute a.1 b.1) : A = ⊥ := by
  rw [← inf_of_le_left (le_refl A)] at hc ⊢
  exact H.inf_eq_bot_of_commute hc

end LinearDisjoint

end FieldAndRing

section FieldAndCommRing

namespace LinearDisjoint

variable [Field R] [CommRing S] [Algebra R S]

variable {A B : Subalgebra R S}

theorem inf_eq_bot (H : A.LinearDisjoint B) : A ⊓ B = ⊥ :=
  H.inf_eq_bot_of_commute fun _ _ ↦ mul_comm _ _

theorem eq_bot_of_self (H : A.LinearDisjoint A) : A = ⊥ :=
  H.eq_bot_of_commute_of_self fun _ _ ↦ mul_comm _ _

end LinearDisjoint

end FieldAndCommRing

end Subalgebra
