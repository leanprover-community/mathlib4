/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Module structure on monoid algebras

## Main results

* `MonoidAlgebra.module`, `AddMonoidAlgebra.module`: lift a module structure to monoid algebras

## Implementation notes

We do not state the equivalent of `DistribMulAction M (MonoidAlgebra S M)` for `AddMonoidAlgebra`
because mathlib does not have the notion of distributive actions of additive groups.
-/

@[expose] public section

assert_not_exists NonUnitalAlgHom AlgEquiv

noncomputable section

open Finsupp hiding single

variable {R S M N G : Type*}

/-! ### Multiplicative monoids -/

namespace MonoidAlgebra

section SMul

@[to_additive (dont_translate := R) noZeroSMulDivisors]
instance noZeroSMulDivisors [Zero R] [Semiring S] [SMulZeroClass R S] [NoZeroSMulDivisors R S] :
    NoZeroSMulDivisors R S[M] :=
  coeffEquiv.noZeroSMulDivisors _

section DistribMulAction
variable [Monoid S] [Semiring R] [DistribMulAction S R]

@[to_additive (dont_translate := S) (relevant_arg := M) distribMulAction]
instance distribMulAction : DistribMulAction S R[M] := coeffEquiv.distribMulAction _

@[to_additive (dont_translate := S) (relevant_arg := M) (attr := simp)]
lemma mapDomain_smul (f : M → N) (s : S) (x : R[M]) : mapDomain f (s • x) = s • mapDomain f x := by
  ext; simp [Finsupp.mapDomain_smul]

end DistribMulAction

@[to_additive (dont_translate := R) (relevant_arg := M)]
instance module [Semiring R] [Semiring S] [Module R S] : Module R S[M] := coeffEquiv.module _

variable (R) in
/-- `MonoidAlgebra.coeff` as a linear equiv. -/
@[to_additive (attr := simps!) (relevant_arg := M) /-- `MonoidAlgebra.coeff` as a linear equiv. -/]
def coeffLinearEquiv [Semiring R] [Semiring S] [Module R S] : S[M] ≃ₗ[R] M →₀ S :=
  coeffEquiv.linearEquiv _

@[to_additive (dont_translate := R) faithfulSMul]
instance faithfulSMul [Semiring S] [SMulZeroClass R S] [FaithfulSMul R S] [Nonempty M] :
    FaithfulSMul R S[M] :=
  coeffEquiv.faithfulSMul _

/-- This is not an instance as it conflicts with `MonoidAlgebra.distribMulAction` when `M = kˣ`.

TODO: Change the type to `DistribMulAction Gᵈᵐᵃ S[M]` and then it can be an instance.
TODO: Generalise to a group acting on another, instead of just the left multiplication action.
-/
def comapDistribMulActionSelf [Group G] [Semiring S] : DistribMulAction G S[G] :=
  have := Finsupp.comapDistribMulAction (G := G) (α := G) (M := S)
  coeffEquiv.distribMulAction _

end SMul

/-! #### Copies of `ext` lemmas and bundled `single`s from `Finsupp` -/

section ExtLemmas
variable [Semiring S]

/-- `MonoidAlgebra.single` as a `DistribMulActionHom`. -/
@[to_additive (dont_translate := R) (relevant_arg := M) singleDistribMulActionHom
/-- `AddMonoidAlgebra.single` as a `DistribMulActionHom`. -/]
def singleDistribMulActionHom [Monoid R] [DistribMulAction R S] (a : M) : S →+[R] S[M] where
  __ := singleAddHom a
  map_smul' S m := by simp

/-- A copy of `Finsupp.distribMulActionHom_ext'` for `MonoidAlgebra`. -/
@[to_additive (dont_translate := R) (relevant_arg := N) (attr := ext) distribMulActionHom_ext'
/-- A copy of `Finsupp.distribMulActionHom_ext'` for `AddMonoidAlgebra`. -/]
theorem distribMulActionHom_ext' {N : Type*} [Monoid R] [AddMonoid N] [DistribMulAction R N]
    [DistribMulAction R S] {f g : S[M] →+[R] N}
    (h : ∀ a, f.comp (singleDistribMulActionHom a) = g.comp (singleDistribMulActionHom a)) :
    f = g :=
  DistribMulActionHom.toAddMonoidHom_injective <| addMonoidHom_ext fun a x ↦ congr($(h a) x)

/-- A copy of `Finsupp.lsingle` for `MonoidAlgebra`. -/
@[to_additive (dont_translate := R) (relevant_arg := M)
/-- A copy of `Finsupp.lsingle` for `AddMonoidAlgebra`. -/]
def lsingle [Semiring R] [Module R S] (a : M) : S →ₗ[R] S[M] :=
  (coeffLinearEquiv _).symm.toLinearMap.comp <| Finsupp.lsingle a

@[to_additive (attr := simp)]
lemma lsingle_apply [Semiring R] [Module R S] (a : M) (b : S) :
    lsingle (R := R) a b = single a b :=
  rfl

/-- A copy of `Finsupp.lhom_ext'` for `MonoidAlgebra`. -/
@[to_additive (attr := ext high) (relevant_arg := M)]
lemma lhom_ext' {N : Type*} [Semiring R] [AddCommMonoid N] [Module R N] [Module R S]
    ⦃f g : S[M] →ₗ[R] N⦄
    (H : ∀ (x : M), LinearMap.comp f (lsingle x) = LinearMap.comp g (lsingle x)) : f = g :=
  LinearMap.toAddMonoidHom_injective <| addMonoidHom_ext fun a x ↦ congr($(H a) x)

end ExtLemmas

section MiscTheorems

variable [Semiring S]

theorem smul_of [MulOneClass M] (g : M) (r : S) : r • of S M g = single g r := by
  simp

theorem liftNC_smul [MulOneClass M] {R : Type*} [Semiring R] (f : S →+* R) (g : M →* R) (c : S)
    (φ : S[M]) : liftNC (f : S →+ R) g (c • φ) = f c * liftNC (f : S →+ R) g φ := by
  suffices (liftNC (↑f) g).comp (smulAddHom S S[M] c) =
      (AddMonoidHom.mulLeft (f c)).comp (liftNC (↑f) g) from
    DFunLike.congr_fun this φ
  ext
  simp_rw [AddMonoidHom.comp_apply, singleAddHom_apply, smulAddHom_apply,
    AddMonoidHom.coe_mulLeft, smul_single', liftNC_single, AddMonoidHom.coe_coe, map_mul, mul_assoc]

end MiscTheorems

/-! #### Non-unital, non-associative algebra structure -/
section NonUnitalNonAssocAlgebra

variable (S) [Semiring S] [DistribSMul R S] [Mul M]

instance isScalarTower_self [IsScalarTower R S S] : IsScalarTower R S[M] S[M] where
  smul_assoc t a b := by
    classical ext; simp [coeff_mul, coeff_smul, sum_smul_index', Finsupp.smul_sum, smul_mul_assoc]

/-- Note that if `S` is a `CommSemiring` then we have `SMulCommClass S S S` and so we can take
`R = S` in the below. In other words, if the coefficients are commutative amongst themselves, they
also commute with the algebra multiplication. -/
instance smulCommClass_self [SMulCommClass R S S] : SMulCommClass R S[M] S[M] where
  smul_comm t a b := by
    classical ext; simp [coeff_mul, coeff_smul, sum_smul_index', Finsupp.smul_sum, mul_smul_comm]

instance smulCommClass_symm_self [SMulCommClass S R S] : SMulCommClass S[M] R S[M] :=
  have := SMulCommClass.symm S R S; .symm ..

end NonUnitalNonAssocAlgebra

section Submodule

variable [CommSemiring S] [Monoid M]
variable {V : Type*} [AddCommMonoid V]
variable [Module S V] [Module S[M] V] [IsScalarTower S S[M] V]

/-- A submodule over `S` which is stable under scalar multiplication by elements of `M` is a
submodule over `S[M]` -/
def submoduleOfSMulMem (W : Submodule S V) (h : ∀ (g : M) (v : V), v ∈ W → of S M g • v ∈ W) :
    Submodule S[M] V where
  carrier := W
  zero_mem' := W.zero_mem'
  add_mem' := W.add_mem'
  smul_mem' f v hv := by
    rw [← f.sum_coeff_single, Finsupp.sum, Finset.sum_smul]
    simp_rw [← smul_of, smul_assoc]
    exact Submodule.sum_smul_mem W _ fun g _ => h g v hv

end Submodule

end MonoidAlgebra

/-! ### Additive monoids -/

namespace AddMonoidAlgebra
variable [Semiring S]

theorem liftNC_smul {R : Type*} [AddZeroClass M] [Semiring R] (f : S →+* R)
    (g : Multiplicative M →* R) (c : S) (φ : S[M]) :
    liftNC (f : S →+ R) g (c • φ) = f c * liftNC (f : S →+ R) g φ := by
  suffices (liftNC (↑f) g).comp (smulAddHom S S[M] c) =
      (AddMonoidHom.mulLeft (f c)).comp (liftNC f g) from DFunLike.congr_fun this φ
  ext
  simp_rw [AddMonoidHom.comp_apply, singleAddHom_apply, smulAddHom_apply,
    AddMonoidHom.coe_mulLeft, smul_single', liftNC_single, AddMonoidHom.coe_coe, map_mul, mul_assoc]

end AddMonoidAlgebra

namespace AddMonoidAlgebra

/-! #### Non-unital, non-associative algebra structure -/
section NonUnitalNonAssocAlgebra

variable [Semiring S] [DistribSMul R S] [Add M]

instance isScalarTower_self [IsScalarTower R S S] : IsScalarTower R S[M] S[M] where
  smul_assoc t a b := by
    classical ext; simp [coeff_mul, coeff_smul, sum_smul_index', Finsupp.smul_sum, smul_mul_assoc]

/-- Note that if `S` is a `CommSemiring` then we have `SMulCommClass S S S` and so we can take
`R = S` in the below. In other words, if the coefficients are commutative amongst themselves, they
also commute with the algebra multiplication. -/
instance smulCommClass_self [SMulCommClass R S S] : SMulCommClass R S[M] S[M] where
  smul_comm t a b := by
    classical ext; simp [coeff_mul, coeff_smul, sum_smul_index', Finsupp.smul_sum, mul_smul_comm]

instance smulCommClass_symm_self [SMulCommClass S R S] : SMulCommClass S[M] R S[M] :=
  have := SMulCommClass.symm S R S; .symm ..

end NonUnitalNonAssocAlgebra

end AddMonoidAlgebra
