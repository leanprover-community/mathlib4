/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Module structure on monoid algebras

## Main results

* `MonoidAlgebra.module`, `AddMonoidAlgebra.module`: lift a module structure to monoid algebras

## Implementation notes

We do not state the equivalent of `DistribMulAction G (MonoidAlgebra k G)` for `AddMonoidAlgebra`
because mathlib does not have the notion of distributive actions of additive groups.
-/

@[expose] public section

assert_not_exists NonUnitalAlgHom AlgEquiv

noncomputable section

open Finsupp hiding single

universe u₁ u₂ u₃ u₄

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S M : Type*}

/-! ### Multiplicative monoids -/

namespace MonoidAlgebra

variable {k G}

section SMul

variable {S : Type*}

@[to_additive (dont_translate := R) noZeroSMulDivisors]
instance noZeroSMulDivisors [Zero R] [Semiring k] [SMulZeroClass R k] [NoZeroSMulDivisors R k] :
    NoZeroSMulDivisors R k[G] :=
  Finsupp.noZeroSMulDivisors

@[to_additive (dont_translate := R) distribMulAction]
instance distribMulAction [Monoid R] [Semiring k] [DistribMulAction R k] :
    DistribMulAction R k[G] :=
  Finsupp.distribMulAction G k

@[to_additive (dont_translate := R)]
instance module [Semiring R] [Semiring k] [Module R k] : Module R k[G] :=
  Finsupp.module G k

@[to_additive (dont_translate := R) faithfulSMul]
instance faithfulSMul [Semiring k] [SMulZeroClass R k] [FaithfulSMul R k] [Nonempty G] :
    FaithfulSMul R k[G] :=
  Finsupp.faithfulSMul

/-- This is not an instance as it conflicts with `MonoidAlgebra.distribMulAction` when `G = kˣ`.

TODO: Change the type to `DistribMulAction Gᵈᵐᵃ k[G]` and then it can be an instance.
TODO: Generalise to a group acting on another, instead of just the left multiplication action.
-/
def comapDistribMulActionSelf [Group G] [Semiring k] : DistribMulAction G k[G] :=
  Finsupp.comapDistribMulAction

end SMul

/-!
#### Copies of `ext` lemmas and bundled `single`s from `Finsupp`

As `MonoidAlgebra` is a type synonym, `ext` will not unfold it to find `ext` lemmas.
We need bundled version of `Finsupp.single` with the right types to state these lemmas.
It is good practice to have those, regardless of the `ext` issue.
-/

section ExtLemmas
variable [Semiring k]

/-- `MonoidAlgebra.single` as a `DistribMulActionHom`. -/
@[to_additive (dont_translate := R) (relevant_arg := G) singleDistribMulActionHom
/-- `AddMonoidAlgebra.single` as a `DistribMulActionHom`. -/]
def singleDistribMulActionHom [Monoid R] [DistribMulAction R k] (a : G) : k →+[R] k[G] where
  __ := singleAddHom a
  map_smul' k m := by simp

/-- A copy of `Finsupp.distribMulActionHom_ext'` for `MonoidAlgebra`. -/
@[to_additive (dont_translate := R) (relevant_arg := N) (attr := ext) distribMulActionHom_ext'
/-- A copy of `Finsupp.distribMulActionHom_ext'` for `AddMonoidAlgebra`. -/]
theorem distribMulActionHom_ext' {N : Type*} [Monoid R] [AddMonoid N] [DistribMulAction R N]
    [DistribMulAction R k] {f g : k[G] →+[R] N}
    (h : ∀ a, f.comp (singleDistribMulActionHom a) = g.comp (singleDistribMulActionHom a)) :
    f = g :=
  Finsupp.distribMulActionHom_ext' h

/-- A copy of `Finsupp.lsingle` for `MonoidAlgebra`. -/
@[to_additive (dont_translate := R) (relevant_arg := G)
/-- A copy of `Finsupp.lsingle` for `AddMonoidAlgebra`. -/]
abbrev lsingle [Semiring R] [Module R k] (a : G) : k →ₗ[R] k[G] := Finsupp.lsingle a

@[to_additive (attr := simp)]
lemma lsingle_apply [Semiring R] [Module R k] (a : G) (b : k) :
    lsingle (R := R) a b = single a b :=
  rfl

/-- A copy of `Finsupp.lhom_ext'` for `MonoidAlgebra`. -/
@[to_additive (attr := ext high)]
lemma lhom_ext' {N : Type*} [Semiring R] [AddCommMonoid N] [Module R N] [Module R k]
    ⦃f g : k[G] →ₗ[R] N⦄
    (H : ∀ (x : G), LinearMap.comp f (lsingle x) = LinearMap.comp g (lsingle x)) :
    f = g :=
  Finsupp.lhom_ext' H

end ExtLemmas

section MiscTheorems

variable [Semiring k]

theorem smul_of [MulOneClass G] (g : G) (r : k) : r • of k G g = single g r := by
  simp

theorem liftNC_smul [MulOneClass G] {R : Type*} [Semiring R] (f : k →+* R) (g : G →* R) (c : k)
    (φ : k[G]) : liftNC (f : k →+ R) g (c • φ) = f c * liftNC (f : k →+ R) g φ := by
  suffices (liftNC (↑f) g).comp (smulAddHom k k[G] c) =
      (AddMonoidHom.mulLeft (f c)).comp (liftNC (↑f) g) from
    DFunLike.congr_fun this φ
  ext
  simp_rw [AddMonoidHom.comp_apply, singleAddHom_apply, smulAddHom_apply,
    AddMonoidHom.coe_mulLeft, smul_single', liftNC_single, AddMonoidHom.coe_coe, map_mul, mul_assoc]

end MiscTheorems

/-! #### Non-unital, non-associative algebra structure -/
section NonUnitalNonAssocAlgebra

variable (k) [Semiring k] [DistribSMul R k] [Mul G]

instance isScalarTower_self [IsScalarTower R k k] : IsScalarTower R k[G] k[G] where
  smul_assoc t a b := by
    ext
    -- Porting note: `refine` & `rw` are required because `simp` behaves differently.
    classical
    simp only [smul_eq_mul, mul_apply]
    rw [coe_smul]
    refine Eq.trans (sum_smul_index' (g := a) (b := t) ?_) ?_ <;>
      simp only [mul_apply, Finsupp.smul_sum, smul_ite, smul_mul_assoc,
        zero_mul, ite_self, imp_true_iff, sum_zero, Pi.smul_apply, smul_zero]

/-- Note that if `k` is a `CommSemiring` then we have `SMulCommClass k k k` and so we can take
`R = k` in the below. In other words, if the coefficients are commutative amongst themselves, they
also commute with the algebra multiplication. -/
instance smulCommClass_self [SMulCommClass R k k] : SMulCommClass R k[G] k[G] where
  smul_comm t a b := by
    ext
    -- Porting note: `refine` & `rw` are required because `simp` behaves differently.
    classical
    simp only [smul_eq_mul, mul_apply]
    rw [coe_smul]
    refine Eq.symm (Eq.trans (congr_arg (sum a)
      (funext₂ fun a₁ b₁ => sum_smul_index' (g := b) (b := t) ?_)) ?_) <;>
    simp only [mul_apply, Finsupp.sum, Finset.smul_sum, smul_ite, mul_smul_comm,
      imp_true_iff, ite_eq_right_iff, Pi.smul_apply, mul_zero, smul_zero]

instance smulCommClass_symm_self [SMulCommClass k R k] : SMulCommClass k[G] R k[G] :=
  have := SMulCommClass.symm k R k; .symm ..

end NonUnitalNonAssocAlgebra

section Submodule

variable [CommSemiring k] [Monoid G]
variable {V : Type*} [AddCommMonoid V]
variable [Module k V] [Module k[G] V] [IsScalarTower k k[G] V]

/-- A submodule over `k` which is stable under scalar multiplication by elements of `G` is a
submodule over `k[G]` -/
def submoduleOfSMulMem (W : Submodule k V) (h : ∀ (g : G) (v : V), v ∈ W → of k G g • v ∈ W) :
    Submodule k[G] V where
  carrier := W
  zero_mem' := W.zero_mem'
  add_mem' := W.add_mem'
  smul_mem' := by
    intro f v hv
    rw [← Finsupp.sum_single f, Finsupp.sum, Finset.sum_smul]
    simp_rw [← smul_of, smul_assoc]
    exact Submodule.sum_smul_mem W _ fun g _ => h g v hv

end Submodule

end MonoidAlgebra

/-! ### Additive monoids -/

namespace AddMonoidAlgebra

variable {k G}

section MiscTheorems

variable [Semiring k]

theorem liftNC_smul {R : Type*} [AddZeroClass G] [Semiring R] (f : k →+* R)
    (g : Multiplicative G →* R) (c : k) (φ : k[G]) :
    liftNC (f : k →+ R) g (c • φ) = f c * liftNC (f : k →+ R) g φ :=
  @MonoidAlgebra.liftNC_smul k (Multiplicative G) _ _ _ _ f g c φ

end MiscTheorems

end AddMonoidAlgebra

namespace AddMonoidAlgebra

variable {k G H}

/-! #### Non-unital, non-associative algebra structure -/
section NonUnitalNonAssocAlgebra

variable (k) [Semiring k] [DistribSMul R k] [Add G]

instance isScalarTower_self [IsScalarTower R k k] :
    IsScalarTower R k[G] k[G] :=
  @MonoidAlgebra.isScalarTower_self k (Multiplicative G) R _ _ _ _

/-- Note that if `k` is a `CommSemiring` then we have `SMulCommClass k k k` and so we can take
`R = k` in the below. In other words, if the coefficients are commutative amongst themselves, they
also commute with the algebra multiplication. -/
instance smulCommClass_self [SMulCommClass R k k] :
    SMulCommClass R k[G] k[G] :=
  @MonoidAlgebra.smulCommClass_self k (Multiplicative G) R _ _ _ _

instance smulCommClass_symm_self [SMulCommClass k R k] : SMulCommClass k[G] R k[G] :=
  have := SMulCommClass.symm k R k; .symm ..

end NonUnitalNonAssocAlgebra

end AddMonoidAlgebra
