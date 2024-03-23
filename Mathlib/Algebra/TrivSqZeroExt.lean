/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Eric Wieser
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.GroupTheory.GroupAction.BigOperators
import Mathlib.LinearAlgebra.Prod

#align_import algebra.triv_sq_zero_ext from "leanprover-community/mathlib"@"ce7e9d53d4bbc38065db3b595cd5bd73c323bc1d"

/-!
# Trivial Square-Zero Extension

Given a ring `R` together with an `(R, R)`-bimodule `M`, the trivial square-zero extension of `M`
over `R` is defined to be the `R`-algebra `R ⊕ M` with multiplication given by
`(r₁ + m₁) * (r₂ + m₂) = r₁ r₂ + r₁ m₂ + m₁ r₂`.

It is a square-zero extension because `M^2 = 0`.

Note that expressing this requires bimodules; we write these in general for a
not-necessarily-commutative `R` as:
```lean
variable {R M : Type*} [Semiring R] [AddCommMonoid M]
variable [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
```
If we instead work with a commutative `R'` acting symmetrically on `M`, we write
```lean
variable {R' M : Type*} [CommSemiring R'] [AddCommMonoid M]
variable [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]
```
noting that in this context `IsCentralScalar R' M` implies `SMulCommClass R' R'ᵐᵒᵖ M`.

Many of the later results in this file are only stated for the commutative `R'` for simplicity.

## Main definitions

* `TrivSqZeroExt.inl`, `TrivSqZeroExt.inr`: the canonical inclusions into
  `TrivSqZeroExt R M`.
* `TrivSqZeroExt.fst`, `TrivSqZeroExt.snd`: the canonical projections from
  `TrivSqZeroExt R M`.
* `triv_sq_zero_ext.algebra`: the associated `R`-algebra structure.
* `TrivSqZeroExt.lift`: the universal property of the trivial square-zero extension; algebra
  morphisms `TrivSqZeroExt R M →ₐ[S] A` are uniquely defined by an algebra morphism `f : R →ₐ[S] A`
  on `R` and a linear map `g : M →ₗ[S] A` on `M` such that:
  * `g x * g y = 0`: the elements of `M` continue to square to zero.
  * `g (r •> x) = f r * g x` and `g (x <• r) = g x * f r`: left and right actions are preserved by
    `g`.
* `TrivSqZeroExt.lift`: the universal property of the trivial square-zero extension; algebra
  morphisms `TrivSqZeroExt R M →ₐ[R] A` are uniquely defined by linear maps `M →ₗ[R] A` for
  which the product of any two elements in the range is zero.

-/

universe u v w

/-- "Trivial Square-Zero Extension".

Given a module `M` over a ring `R`, the trivial square-zero extension of `M` over `R` is defined
to be the `R`-algebra `R × M` with multiplication given by
`(r₁ + m₁) * (r₂ + m₂) = r₁ r₂ + r₁ m₂ + r₂ m₁`.

It is a square-zero extension because `M^2 = 0`.
-/
def TrivSqZeroExt (R : Type u) (M : Type v) :=
  R × M
#align triv_sq_zero_ext TrivSqZeroExt

-- mathport name: exprtsze
local notation "tsze" => TrivSqZeroExt

open scoped BigOperators RightActions

namespace TrivSqZeroExt

open MulOpposite

section Basic

variable {R : Type u} {M : Type v}

/-- The canonical inclusion `R → TrivSqZeroExt R M`. -/
def inl [Zero M] (r : R) : tsze R M :=
  (r, 0)
#align triv_sq_zero_ext.inl TrivSqZeroExt.inl

/-- The canonical inclusion `M → TrivSqZeroExt R M`. -/
def inr [Zero R] (m : M) : tsze R M :=
  (0, m)
#align triv_sq_zero_ext.inr TrivSqZeroExt.inr

/-- The canonical projection `TrivSqZeroExt R M → R`. -/
def fst (x : tsze R M) : R :=
  x.1
#align triv_sq_zero_ext.fst TrivSqZeroExt.fst

/-- The canonical projection `TrivSqZeroExt R M → M`. -/
def snd (x : tsze R M) : M :=
  x.2
#align triv_sq_zero_ext.snd TrivSqZeroExt.snd

@[simp]
theorem fst_mk (r : R) (m : M) : fst (r, m) = r :=
  rfl
#align triv_sq_zero_ext.fst_mk TrivSqZeroExt.fst_mk

@[simp]
theorem snd_mk (r : R) (m : M) : snd (r, m) = m :=
  rfl
#align triv_sq_zero_ext.snd_mk TrivSqZeroExt.snd_mk

@[ext]
theorem ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y :=
  Prod.ext h1 h2
#align triv_sq_zero_ext.ext TrivSqZeroExt.ext

section

variable (M)

@[simp]
theorem fst_inl [Zero M] (r : R) : (inl r : tsze R M).fst = r :=
  rfl
#align triv_sq_zero_ext.fst_inl TrivSqZeroExt.fst_inl

@[simp]
theorem snd_inl [Zero M] (r : R) : (inl r : tsze R M).snd = 0 :=
  rfl
#align triv_sq_zero_ext.snd_inl TrivSqZeroExt.snd_inl

@[simp]
theorem fst_comp_inl [Zero M] : fst ∘ (inl : R → tsze R M) = id :=
  rfl
#align triv_sq_zero_ext.fst_comp_inl TrivSqZeroExt.fst_comp_inl

@[simp]
theorem snd_comp_inl [Zero M] : snd ∘ (inl : R → tsze R M) = 0 :=
  rfl
#align triv_sq_zero_ext.snd_comp_inl TrivSqZeroExt.snd_comp_inl

end

section

variable (R)

@[simp]
theorem fst_inr [Zero R] (m : M) : (inr m : tsze R M).fst = 0 :=
  rfl
#align triv_sq_zero_ext.fst_inr TrivSqZeroExt.fst_inr

@[simp]
theorem snd_inr [Zero R] (m : M) : (inr m : tsze R M).snd = m :=
  rfl
#align triv_sq_zero_ext.snd_inr TrivSqZeroExt.snd_inr

@[simp]
theorem fst_comp_inr [Zero R] : fst ∘ (inr : M → tsze R M) = 0 :=
  rfl
#align triv_sq_zero_ext.fst_comp_inr TrivSqZeroExt.fst_comp_inr

@[simp]
theorem snd_comp_inr [Zero R] : snd ∘ (inr : M → tsze R M) = id :=
  rfl
#align triv_sq_zero_ext.snd_comp_inr TrivSqZeroExt.snd_comp_inr

end

theorem inl_injective [Zero M] : Function.Injective (inl : R → tsze R M) :=
  Function.LeftInverse.injective <| fst_inl _
#align triv_sq_zero_ext.inl_injective TrivSqZeroExt.inl_injective

theorem inr_injective [Zero R] : Function.Injective (inr : M → tsze R M) :=
  Function.LeftInverse.injective <| snd_inr _
#align triv_sq_zero_ext.inr_injective TrivSqZeroExt.inr_injective

end Basic

/-! ### Structures inherited from `Prod`

Additive operators and scalar multiplication operate elementwise. -/


section Additive

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

instance inhabited [Inhabited R] [Inhabited M] : Inhabited (tsze R M) :=
  instInhabitedProd

instance zero [Zero R] [Zero M] : Zero (tsze R M) :=
  Prod.instZero

instance add [Add R] [Add M] : Add (tsze R M) :=
  Prod.instAdd

instance sub [Sub R] [Sub M] : Sub (tsze R M) :=
  Prod.instSub

instance neg [Neg R] [Neg M] : Neg (tsze R M) :=
  Prod.instNeg

instance addSemigroup [AddSemigroup R] [AddSemigroup M] : AddSemigroup (tsze R M) :=
  Prod.instAddSemigroup

instance addZeroClass [AddZeroClass R] [AddZeroClass M] : AddZeroClass (tsze R M) :=
  Prod.instAddZeroClass

instance addMonoid [AddMonoid R] [AddMonoid M] : AddMonoid (tsze R M) :=
  Prod.instAddMonoid

instance addGroup [AddGroup R] [AddGroup M] : AddGroup (tsze R M) :=
  Prod.instAddGroup

instance addCommSemigroup [AddCommSemigroup R] [AddCommSemigroup M] : AddCommSemigroup (tsze R M) :=
  Prod.instAddCommSemigroup

instance addCommMonoid [AddCommMonoid R] [AddCommMonoid M] : AddCommMonoid (tsze R M) :=
  Prod.instAddCommMonoid

instance addCommGroup [AddCommGroup R] [AddCommGroup M] : AddCommGroup (tsze R M) :=
  Prod.instAddCommGroup

instance smul [SMul S R] [SMul S M] : SMul S (tsze R M) :=
  Prod.smul

instance isScalarTower [SMul T R] [SMul T M] [SMul S R] [SMul S M] [SMul T S]
    [IsScalarTower T S R] [IsScalarTower T S M] : IsScalarTower T S (tsze R M) :=
  Prod.isScalarTower

instance smulCommClass [SMul T R] [SMul T M] [SMul S R] [SMul S M]
    [SMulCommClass T S R] [SMulCommClass T S M] : SMulCommClass T S (tsze R M) :=
  Prod.smulCommClass

instance isCentralScalar [SMul S R] [SMul S M] [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M] [IsCentralScalar S R]
    [IsCentralScalar S M] : IsCentralScalar S (tsze R M) :=
  Prod.isCentralScalar

instance mulAction [Monoid S] [MulAction S R] [MulAction S M] : MulAction S (tsze R M) :=
  Prod.mulAction

instance distribMulAction [Monoid S] [AddMonoid R] [AddMonoid M]
    [DistribMulAction S R] [DistribMulAction S M] : DistribMulAction S (tsze R M) :=
  Prod.distribMulAction

instance module [Semiring S] [AddCommMonoid R] [AddCommMonoid M] [Module S R] [Module S M] :
    Module S (tsze R M) :=
  Prod.instModule

@[simp]
theorem fst_zero [Zero R] [Zero M] : (0 : tsze R M).fst = 0 :=
  rfl
#align triv_sq_zero_ext.fst_zero TrivSqZeroExt.fst_zero

@[simp]
theorem snd_zero [Zero R] [Zero M] : (0 : tsze R M).snd = 0 :=
  rfl
#align triv_sq_zero_ext.snd_zero TrivSqZeroExt.snd_zero

@[simp]
theorem fst_add [Add R] [Add M] (x₁ x₂ : tsze R M) : (x₁ + x₂).fst = x₁.fst + x₂.fst :=
  rfl
#align triv_sq_zero_ext.fst_add TrivSqZeroExt.fst_add

@[simp]
theorem snd_add [Add R] [Add M] (x₁ x₂ : tsze R M) : (x₁ + x₂).snd = x₁.snd + x₂.snd :=
  rfl
#align triv_sq_zero_ext.snd_add TrivSqZeroExt.snd_add

@[simp]
theorem fst_neg [Neg R] [Neg M] (x : tsze R M) : (-x).fst = -x.fst :=
  rfl
#align triv_sq_zero_ext.fst_neg TrivSqZeroExt.fst_neg

@[simp]
theorem snd_neg [Neg R] [Neg M] (x : tsze R M) : (-x).snd = -x.snd :=
  rfl
#align triv_sq_zero_ext.snd_neg TrivSqZeroExt.snd_neg

@[simp]
theorem fst_sub [Sub R] [Sub M] (x₁ x₂ : tsze R M) : (x₁ - x₂).fst = x₁.fst - x₂.fst :=
  rfl
#align triv_sq_zero_ext.fst_sub TrivSqZeroExt.fst_sub

@[simp]
theorem snd_sub [Sub R] [Sub M] (x₁ x₂ : tsze R M) : (x₁ - x₂).snd = x₁.snd - x₂.snd :=
  rfl
#align triv_sq_zero_ext.snd_sub TrivSqZeroExt.snd_sub

@[simp]
theorem fst_smul [SMul S R] [SMul S M] (s : S) (x : tsze R M) : (s • x).fst = s • x.fst :=
  rfl
#align triv_sq_zero_ext.fst_smul TrivSqZeroExt.fst_smul

@[simp]
theorem snd_smul [SMul S R] [SMul S M] (s : S) (x : tsze R M) : (s • x).snd = s • x.snd :=
  rfl
#align triv_sq_zero_ext.snd_smul TrivSqZeroExt.snd_smul

theorem fst_sum {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι → tsze R M) :
    (∑ i in s, f i).fst = ∑ i in s, (f i).fst :=
  Prod.fst_sum
#align triv_sq_zero_ext.fst_sum TrivSqZeroExt.fst_sum

theorem snd_sum {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι → tsze R M) :
    (∑ i in s, f i).snd = ∑ i in s, (f i).snd :=
  Prod.snd_sum
#align triv_sq_zero_ext.snd_sum TrivSqZeroExt.snd_sum

section

variable (M)

@[simp]
theorem inl_zero [Zero R] [Zero M] : (inl 0 : tsze R M) = 0 :=
  rfl
#align triv_sq_zero_ext.inl_zero TrivSqZeroExt.inl_zero

@[simp]
theorem inl_add [Add R] [AddZeroClass M] (r₁ r₂ : R) :
    (inl (r₁ + r₂) : tsze R M) = inl r₁ + inl r₂ :=
  ext rfl (add_zero 0).symm
#align triv_sq_zero_ext.inl_add TrivSqZeroExt.inl_add

@[simp]
theorem inl_neg [Neg R] [SubNegZeroMonoid M] (r : R) : (inl (-r) : tsze R M) = -inl r :=
  ext rfl neg_zero.symm
#align triv_sq_zero_ext.inl_neg TrivSqZeroExt.inl_neg

@[simp]
theorem inl_sub [Sub R] [SubNegZeroMonoid M] (r₁ r₂ : R) :
    (inl (r₁ - r₂) : tsze R M) = inl r₁ - inl r₂ :=
  ext rfl (sub_zero _).symm
#align triv_sq_zero_ext.inl_sub TrivSqZeroExt.inl_sub

@[simp]
theorem inl_smul [Monoid S] [AddMonoid M] [SMul S R] [DistribMulAction S M] (s : S) (r : R) :
    (inl (s • r) : tsze R M) = s • inl r :=
  ext rfl (smul_zero s).symm
#align triv_sq_zero_ext.inl_smul TrivSqZeroExt.inl_smul

theorem inl_sum {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι → R) :
    (inl (∑ i in s, f i) : tsze R M) = ∑ i in s, inl (f i) :=
  map_sum (LinearMap.inl ℕ _ _) _ _
#align triv_sq_zero_ext.inl_sum TrivSqZeroExt.inl_sum

end

section

variable (R)

@[simp]
theorem inr_zero [Zero R] [Zero M] : (inr 0 : tsze R M) = 0 :=
  rfl
#align triv_sq_zero_ext.inr_zero TrivSqZeroExt.inr_zero

@[simp]
theorem inr_add [AddZeroClass R] [AddZeroClass M] (m₁ m₂ : M) :
    (inr (m₁ + m₂) : tsze R M) = inr m₁ + inr m₂ :=
  ext (add_zero 0).symm rfl
#align triv_sq_zero_ext.inr_add TrivSqZeroExt.inr_add

@[simp]
theorem inr_neg [SubNegZeroMonoid R] [Neg M] (m : M) : (inr (-m) : tsze R M) = -inr m :=
  ext neg_zero.symm rfl
#align triv_sq_zero_ext.inr_neg TrivSqZeroExt.inr_neg

@[simp]
theorem inr_sub [SubNegZeroMonoid R] [Sub M] (m₁ m₂ : M) :
    (inr (m₁ - m₂) : tsze R M) = inr m₁ - inr m₂ :=
  ext (sub_zero _).symm rfl
#align triv_sq_zero_ext.inr_sub TrivSqZeroExt.inr_sub

@[simp]
theorem inr_smul [Zero R] [Zero S] [SMulWithZero S R] [SMul S M] (r : S) (m : M) :
    (inr (r • m) : tsze R M) = r • inr m :=
  ext (smul_zero _).symm rfl
#align triv_sq_zero_ext.inr_smul TrivSqZeroExt.inr_smul

theorem inr_sum {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι → M) :
    (inr (∑ i in s, f i) : tsze R M) = ∑ i in s, inr (f i) :=
  map_sum (LinearMap.inr ℕ _ _) _ _
#align triv_sq_zero_ext.inr_sum TrivSqZeroExt.inr_sum

end

theorem inl_fst_add_inr_snd_eq [AddZeroClass R] [AddZeroClass M] (x : tsze R M) :
    inl x.fst + inr x.snd = x :=
  ext (add_zero x.1) (zero_add x.2)
#align triv_sq_zero_ext.inl_fst_add_inr_snd_eq TrivSqZeroExt.inl_fst_add_inr_snd_eq

/-- To show a property hold on all `TrivSqZeroExt R M` it suffices to show it holds
on terms of the form `inl r + inr m`.

This can be used as `induction x using TrivSqZeroExt.ind`. -/
theorem ind {R M} [AddZeroClass R] [AddZeroClass M] {P : TrivSqZeroExt R M → Prop}
    (h : ∀ r m, P (inl r + inr m)) (x) : P x :=
  inl_fst_add_inr_snd_eq x ▸ h x.1 x.2
#align triv_sq_zero_ext.ind TrivSqZeroExt.ind

/-- This cannot be marked `@[ext]` as it ends up being used instead of `LinearMap.prod_ext` when
working with `R × M`. -/
theorem linearMap_ext {N} [Semiring S] [AddCommMonoid R] [AddCommMonoid M] [AddCommMonoid N]
    [Module S R] [Module S M] [Module S N] ⦃f g : tsze R M →ₗ[S] N⦄
    (hl : ∀ r, f (inl r) = g (inl r)) (hr : ∀ m, f (inr m) = g (inr m)) : f = g :=
  LinearMap.prod_ext (LinearMap.ext hl) (LinearMap.ext hr)
#align triv_sq_zero_ext.linear_map_ext TrivSqZeroExt.linearMap_ext

variable (R M)

/-- The canonical `R`-linear inclusion `M → TrivSqZeroExt R M`. -/
@[simps apply]
def inrHom [Semiring R] [AddCommMonoid M] [Module R M] : M →ₗ[R] tsze R M :=
  { LinearMap.inr R R M with toFun := inr }
#align triv_sq_zero_ext.inr_hom TrivSqZeroExt.inrHom

/-- The canonical `R`-linear projection `TrivSqZeroExt R M → M`. -/
@[simps apply]
def sndHom [Semiring R] [AddCommMonoid M] [Module R M] : tsze R M →ₗ[R] M :=
  { LinearMap.snd _ _ _ with toFun := snd }
#align triv_sq_zero_ext.snd_hom TrivSqZeroExt.sndHom

end Additive

/-! ### Multiplicative structure -/


section Mul

variable {R : Type u} {M : Type v}

instance one [One R] [Zero M] : One (tsze R M) :=
  ⟨(1, 0)⟩

instance mul [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] : Mul (tsze R M) :=
  ⟨fun x y => (x.1 * y.1, x.1 •> y.2 + x.2 <• y.1)⟩

@[simp]
theorem fst_one [One R] [Zero M] : (1 : tsze R M).fst = 1 :=
  rfl
#align triv_sq_zero_ext.fst_one TrivSqZeroExt.fst_one

@[simp]
theorem snd_one [One R] [Zero M] : (1 : tsze R M).snd = 0 :=
  rfl
#align triv_sq_zero_ext.snd_one TrivSqZeroExt.snd_one

@[simp]
theorem fst_mul [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] (x₁ x₂ : tsze R M) :
    (x₁ * x₂).fst = x₁.fst * x₂.fst :=
  rfl
#align triv_sq_zero_ext.fst_mul TrivSqZeroExt.fst_mul

@[simp]
theorem snd_mul [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] (x₁ x₂ : tsze R M) :
    (x₁ * x₂).snd = x₁.fst •> x₂.snd + x₁.snd <• x₂.fst :=
  rfl
#align triv_sq_zero_ext.snd_mul TrivSqZeroExt.snd_mul

section

variable (M)

@[simp]
theorem inl_one [One R] [Zero M] : (inl 1 : tsze R M) = 1 :=
  rfl
#align triv_sq_zero_ext.inl_one TrivSqZeroExt.inl_one

@[simp]
theorem inl_mul [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    (r₁ r₂ : R) : (inl (r₁ * r₂) : tsze R M) = inl r₁ * inl r₂ :=
  ext rfl <| show (0 : M) = r₁ •> (0 : M) + (0 : M) <• r₂ by rw [smul_zero, zero_add, smul_zero]
#align triv_sq_zero_ext.inl_mul TrivSqZeroExt.inl_mul

theorem inl_mul_inl [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    (r₁ r₂ : R) : (inl r₁ * inl r₂ : tsze R M) = inl (r₁ * r₂) :=
  (inl_mul M r₁ r₂).symm
#align triv_sq_zero_ext.inl_mul_inl TrivSqZeroExt.inl_mul_inl

end

section

variable (R)

@[simp]
theorem inr_mul_inr [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] (m₁ m₂ : M) :
    (inr m₁ * inr m₂ : tsze R M) = 0 :=
  ext (mul_zero _) <|
    show (0 : R) •> m₂ + m₁ <• (0 : R) = 0 by rw [zero_smul, zero_add, op_zero, zero_smul]
#align triv_sq_zero_ext.inr_mul_inr TrivSqZeroExt.inr_mul_inr

end

theorem inl_mul_inr [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] (r : R) (m : M) :
    (inl r * inr m : tsze R M) = inr (r • m) :=
  ext (mul_zero r) <|
    show r • m + (0 : Rᵐᵒᵖ) • (0 : M) = r • m by rw [smul_zero, add_zero]
#align triv_sq_zero_ext.inl_mul_inr TrivSqZeroExt.inl_mul_inr

theorem inr_mul_inl [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] (r : R) (m : M) :
    (inr m * inl r : tsze R M) = inr (m <• r) :=
  ext (zero_mul r) <|
    show (0 : R) •> (0 : M) + m <• r = m <• r by rw [smul_zero, zero_add]
#align triv_sq_zero_ext.inr_mul_inl TrivSqZeroExt.inr_mul_inl

theorem inl_mul_eq_smul [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
    (r : R) (x : tsze R M) :
    inl r * x = r •> x :=
  ext rfl (by dsimp; rw [smul_zero, add_zero])

theorem mul_inl_eq_op_smul [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
    (x : tsze R M) (r : R) :
    x * inl r = x <• r :=
  ext rfl (by dsimp; rw [smul_zero, zero_add])

instance mulOneClass [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] :
    MulOneClass (tsze R M) :=
  { TrivSqZeroExt.one, TrivSqZeroExt.mul with
    one_mul := fun x =>
      ext (one_mul x.1) <|
        show (1 : R) •> x.2 + (0 : M) <• x.1 = x.2 by rw [one_smul, smul_zero, add_zero]
    mul_one := fun x =>
      ext (mul_one x.1) <|
        show x.1 • (0 : M) + x.2 <• (1 : R) = x.2 by rw [smul_zero, zero_add, op_one, one_smul] }

instance addMonoidWithOne [AddMonoidWithOne R] [AddMonoid M] : AddMonoidWithOne (tsze R M) :=
  { TrivSqZeroExt.addMonoid, TrivSqZeroExt.one with
    natCast := fun n => inl n
    natCast_zero := by simp [Nat.cast]
    natCast_succ := fun _ => by ext <;> simp [Nat.cast] }

@[simp]
theorem fst_nat_cast [AddMonoidWithOne R] [AddMonoid M] (n : ℕ) : (n : tsze R M).fst = n :=
  rfl
#align triv_sq_zero_ext.fst_nat_cast TrivSqZeroExt.fst_nat_cast

@[simp]
theorem snd_nat_cast [AddMonoidWithOne R] [AddMonoid M] (n : ℕ) : (n : tsze R M).snd = 0 :=
  rfl
#align triv_sq_zero_ext.snd_nat_cast TrivSqZeroExt.snd_nat_cast

@[simp]
theorem inl_nat_cast [AddMonoidWithOne R] [AddMonoid M] (n : ℕ) : (inl n : tsze R M) = n :=
  rfl
#align triv_sq_zero_ext.inl_nat_cast TrivSqZeroExt.inl_nat_cast

instance addGroupWithOne [AddGroupWithOne R] [AddGroup M] : AddGroupWithOne (tsze R M) :=
  { TrivSqZeroExt.addGroup, TrivSqZeroExt.addMonoidWithOne with
    intCast := fun z => inl z
    intCast_ofNat := fun _n => ext (Int.cast_ofNat _) rfl
    intCast_negSucc := fun _n => ext (Int.cast_negSucc _) neg_zero.symm }

@[simp]
theorem fst_int_cast [AddGroupWithOne R] [AddGroup M] (z : ℤ) : (z : tsze R M).fst = z :=
  rfl
#align triv_sq_zero_ext.fst_int_cast TrivSqZeroExt.fst_int_cast

@[simp]
theorem snd_int_cast [AddGroupWithOne R] [AddGroup M] (z : ℤ) : (z : tsze R M).snd = 0 :=
  rfl
#align triv_sq_zero_ext.snd_int_cast TrivSqZeroExt.snd_int_cast

@[simp]
theorem inl_int_cast [AddGroupWithOne R] [AddGroup M] (z : ℤ) : (inl z : tsze R M) = z :=
  rfl
#align triv_sq_zero_ext.inl_int_cast TrivSqZeroExt.inl_int_cast

instance nonAssocSemiring [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] :
    NonAssocSemiring (tsze R M) :=
  { TrivSqZeroExt.addMonoidWithOne, TrivSqZeroExt.mulOneClass, TrivSqZeroExt.addCommMonoid with
    zero_mul := fun x =>
      ext (zero_mul x.1) <|
        show (0 : R) •> x.2 + (0 : M) <• x.1 = 0 by rw [zero_smul, zero_add, smul_zero]
    mul_zero := fun x =>
      ext (mul_zero x.1) <|
        show x.1 • (0 : M) + (0 : Rᵐᵒᵖ) • x.2 = 0 by rw [smul_zero, zero_add, zero_smul]
    left_distrib := fun x₁ x₂ x₃ =>
      ext (mul_add x₁.1 x₂.1 x₃.1) <|
        show
          x₁.1 •> (x₂.2 + x₃.2) + x₁.2 <• (x₂.1 + x₃.1) =
            x₁.1 •> x₂.2 + x₁.2 <• x₂.1 + (x₁.1 •> x₃.2 + x₁.2 <• x₃.1)
          by simp_rw [smul_add, MulOpposite.op_add, add_smul, add_add_add_comm]
    right_distrib := fun x₁ x₂ x₃ =>
      ext (add_mul x₁.1 x₂.1 x₃.1) <|
        show
          (x₁.1 + x₂.1) •> x₃.2 + (x₁.2 + x₂.2) <• x₃.1 =
            x₁.1 •> x₃.2 + x₁.2 <• x₃.1 + (x₂.1 •> x₃.2 + x₂.2 <• x₃.1)
          by simp_rw [add_smul, smul_add, add_add_add_comm] }

instance nonAssocRing [Ring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] :
    NonAssocRing (tsze R M) :=
  { TrivSqZeroExt.addGroupWithOne, TrivSqZeroExt.nonAssocSemiring with }

/-- In the general non-commutative case, the power operator is

$$\begin{align}
(r + m)^n &= r^n + r^{n-1}m + r^{n-2}mr + \cdots + rmr^{n-2} + mr^{n-1} \\
          & =r^n + \sum_{i = 0}^{n - 1} r^{(n - 1) - i} m r^{i}
\end{align}$$

In the commutative case this becomes the simpler $(r + m)^n = r^n + nr^{n-1}m$.
-/
instance [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] :
    Pow (tsze R M) ℕ :=
  ⟨fun x n =>
    ⟨x.fst ^ n, ((List.range n).map fun i => x.fst ^ (n.pred - i) •> x.snd <• x.fst ^ i).sum⟩⟩

@[simp]
theorem fst_pow [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    (x : tsze R M) (n : ℕ) : fst (x ^ n) = x.fst ^ n :=
  rfl
#align triv_sq_zero_ext.fst_pow TrivSqZeroExt.fst_pow

theorem snd_pow_eq_sum [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    (x : tsze R M) (n : ℕ) :
    snd (x ^ n) = ((List.range n).map fun i => x.fst ^ (n.pred - i) •> x.snd <• x.fst ^ i).sum :=
  rfl
#align triv_sq_zero_ext.snd_pow_eq_sum TrivSqZeroExt.snd_pow_eq_sum

theorem snd_pow_of_smul_comm [Monoid R] [AddMonoid M] [DistribMulAction R M]
    [DistribMulAction Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] (x : tsze R M) (n : ℕ)
    (h : x.snd <• x.fst = x.fst •> x.snd) : snd (x ^ n) = n • x.fst ^ n.pred •> x.snd := by
  simp_rw [snd_pow_eq_sum, ← smul_comm (_ : R) (_ : Rᵐᵒᵖ), aux, smul_smul, ← pow_add]
  match n with
  | 0 => rw [Nat.pred_zero, pow_zero, List.range_zero, zero_smul, List.map_nil, List.sum_nil]
  | (Nat.succ n) =>
    simp_rw [Nat.pred_succ]
    refine' (List.sum_eq_card_nsmul _ (x.fst ^ n • x.snd) _).trans _
    · rintro m hm
      simp_rw [List.mem_map, List.mem_range] at hm
      obtain ⟨i, hi, rfl⟩ := hm
      rw [tsub_add_cancel_of_le (Nat.lt_succ_iff.mp hi)]
    · rw [List.length_map, List.length_range]
where
  aux : ∀ n : ℕ, x.snd <• x.fst ^ n = x.fst ^ n •> x.snd := by
    intro n
    induction' n with n ih
    · simp
    · rw [pow_succ, op_mul, mul_smul, mul_smul, ← h, smul_comm (_ : R) (op x.fst) x.snd, ih]
#align triv_sq_zero_ext.snd_pow_of_smul_comm TrivSqZeroExt.snd_pow_of_smul_comm

theorem snd_pow_of_smul_comm' [Monoid R] [AddMonoid M] [DistribMulAction R M]
    [DistribMulAction Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] (x : tsze R M) (n : ℕ)
    (h : x.snd <• x.fst = x.fst •> x.snd) : snd (x ^ n) = n • (x.snd <• x.fst ^ n.pred) := by
  rw [snd_pow_of_smul_comm _ _ h, snd_pow_of_smul_comm.aux _ h]

@[simp]
theorem snd_pow [CommMonoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    [IsCentralScalar R M] (x : tsze R M) (n : ℕ) : snd (x ^ n) = n • x.fst ^ n.pred • x.snd :=
  snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _)
#align triv_sq_zero_ext.snd_pow TrivSqZeroExt.snd_pow

@[simp]
theorem inl_pow [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] (r : R)
    (n : ℕ) : (inl r ^ n : tsze R M) = inl (r ^ n) :=
  ext rfl <| by simp [snd_pow_eq_sum]
#align triv_sq_zero_ext.inl_pow TrivSqZeroExt.inl_pow

instance monoid [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    [SMulCommClass R Rᵐᵒᵖ M] : Monoid (tsze R M) :=
  { TrivSqZeroExt.mulOneClass with
    mul_assoc := fun x y z =>
      ext (mul_assoc x.1 y.1 z.1) <|
        show
          (x.1 * y.1) •> z.2 + (x.1 •> y.2 + x.2 <• y.1) <• z.1 =
            x.1 •> (y.1 •> z.2 + y.2 <• z.1) + x.2 <• (y.1 * z.1)
          by simp_rw [smul_add, ← mul_smul, add_assoc, smul_comm, op_mul]
    npow := fun n x => x ^ n
    npow_zero := fun x => ext (pow_zero x.fst) (by simp [snd_pow_eq_sum])
    npow_succ := fun n x => ext (pow_succ _ _) (by
      simp_rw [snd_mul, snd_pow_eq_sum, Nat.pred_succ]
      cases n
      · simp [List.range_succ]
      rw [List.sum_range_succ']
      simp only [pow_zero, op_one, tsub_zero, one_smul, Nat.succ_sub_succ_eq_sub, fst_pow,
        Nat.pred_succ, List.smul_sum, List.map_map, Function.comp]
      simp_rw [← smul_comm (_ : R) (_ : Rᵐᵒᵖ), smul_smul, pow_succ]
      rfl) }

theorem fst_list_prod [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    [SMulCommClass R Rᵐᵒᵖ M] (l : List (tsze R M)) : l.prod.fst = (l.map fst).prod :=
  map_list_prod ({ toFun := fst, map_one' := fst_one, map_mul' := fst_mul } : tsze R M →* R) _
#align triv_sq_zero_ext.fst_list_prod TrivSqZeroExt.fst_list_prod

instance semiring [Semiring R] [AddCommMonoid M]
    [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] : Semiring (tsze R M) :=
  { TrivSqZeroExt.monoid, TrivSqZeroExt.nonAssocSemiring with }

/-- The second element of a product $\prod_{i=0}^n (r_i + m_i)$ is a sum of terms of the form
$r_0\cdots r_{i-1}m_ir_{i+1}\cdots r_n$. -/
theorem snd_list_prod [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
    [SMulCommClass R Rᵐᵒᵖ M] (l : List (tsze R M)) :
    l.prod.snd =
      (l.enum.map fun x : ℕ × tsze R M =>
          ((l.map fst).take x.1).prod •> x.snd.snd <• ((l.map fst).drop x.1.succ).prod).sum := by
  induction' l with x xs ih
  · simp
  · rw [List.enum_cons, ← List.map_fst_add_enum_eq_enumFrom]
    simp_rw [List.map_cons, List.map_map, Function.comp, Prod.map_snd, Prod.map_fst, id,
      List.take_zero, List.take_cons, List.prod_nil, List.prod_cons, snd_mul, one_smul, List.drop,
      mul_smul, List.sum_cons, fst_list_prod, ih, List.smul_sum, List.map_map,
      ← smul_comm (_ : R) (_ : Rᵐᵒᵖ)]
    exact add_comm _ _
#align triv_sq_zero_ext.snd_list_prod TrivSqZeroExt.snd_list_prod

instance ring [Ring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] :
    Ring (tsze R M) :=
  { TrivSqZeroExt.semiring, TrivSqZeroExt.nonAssocRing with }

instance commMonoid [CommMonoid R] [AddCommMonoid M] [DistribMulAction R M]
    [DistribMulAction Rᵐᵒᵖ M] [IsCentralScalar R M] : CommMonoid (tsze R M) :=
  { TrivSqZeroExt.monoid with
    mul_comm := fun x₁ x₂ =>
      ext (mul_comm x₁.1 x₂.1) <|
        show x₁.1 •> x₂.2 + x₁.2 <• x₂.1 = x₂.1 •> x₁.2 + x₂.2 <• x₁.1 by
          rw [op_smul_eq_smul, op_smul_eq_smul, add_comm] }

instance commSemiring [CommSemiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
    [IsCentralScalar R M] : CommSemiring (tsze R M) :=
  { TrivSqZeroExt.commMonoid, TrivSqZeroExt.nonAssocSemiring with }

instance commRing [CommRing R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] :
    CommRing (tsze R M) :=
  { TrivSqZeroExt.nonAssocRing, TrivSqZeroExt.commSemiring with }

variable (R M)

/-- The canonical inclusion of rings `R → TrivSqZeroExt R M`. -/
@[simps apply]
def inlHom [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] : R →+* tsze R M where
  toFun := inl
  map_one' := inl_one M
  map_mul' := inl_mul M
  map_zero' := inl_zero M
  map_add' := inl_add M
#align triv_sq_zero_ext.inl_hom TrivSqZeroExt.inlHom

end Mul

section Algebra

variable (S : Type*) (R R' : Type u) (M : Type v)
variable [CommSemiring S] [Semiring R] [CommSemiring R'] [AddCommMonoid M]
variable [Algebra S R] [Algebra S R'] [Module S M]
variable [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
variable [IsScalarTower S R M] [IsScalarTower S Rᵐᵒᵖ M]
variable [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M] [IsScalarTower S R' M]

instance algebra' : Algebra S (tsze R M) :=
  { (TrivSqZeroExt.inlHom R M).comp (algebraMap S R) with
    smul := (· • ·)
    commutes' := fun s x =>
      ext (Algebra.commutes _ _) <|
        show algebraMap S R s •> x.snd + (0 : M) <• x.fst
            = x.fst •> (0 : M) + x.snd <• algebraMap S R s by
          rw [smul_zero, smul_zero, add_zero, zero_add]
          rw [Algebra.algebraMap_eq_smul_one, MulOpposite.op_smul, op_one, smul_assoc,
            one_smul, smul_assoc, one_smul]
    smul_def' := fun s x =>
      ext (Algebra.smul_def _ _) <|
        show s • x.snd = algebraMap S R s •> x.snd + (0 : M) <• x.fst by
          rw [smul_zero, add_zero, algebraMap_smul] }
#align triv_sq_zero_ext.algebra' TrivSqZeroExt.algebra'

-- shortcut instance for the common case
instance : Algebra R' (tsze R' M) :=
  TrivSqZeroExt.algebra' _ _ _

theorem algebraMap_eq_inl : ⇑(algebraMap R' (tsze R' M)) = inl :=
  rfl
#align triv_sq_zero_ext.algebra_map_eq_inl TrivSqZeroExt.algebraMap_eq_inl

theorem algebraMap_eq_inlHom : algebraMap R' (tsze R' M) = inlHom R' M :=
  rfl
#align triv_sq_zero_ext.algebra_map_eq_inl_hom TrivSqZeroExt.algebraMap_eq_inlHom

theorem algebraMap_eq_inl' (s : S) : algebraMap S (tsze R M) s = inl (algebraMap S R s) :=
  rfl
#align triv_sq_zero_ext.algebra_map_eq_inl' TrivSqZeroExt.algebraMap_eq_inl'

/-- The canonical `S`-algebra projection `TrivSqZeroExt R M → R`. -/
@[simps]
def fstHom : tsze R M →ₐ[S] R where
  toFun := fst
  map_one' := fst_one
  map_mul' := fst_mul
  map_zero' := fst_zero (M := M)
  map_add' := fst_add
  commutes' _r := fst_inl M _
#align triv_sq_zero_ext.fst_hom TrivSqZeroExt.fstHom

/-- The canonical `S`-algebra inclusion `R → TrivSqZeroExt R M`. -/
@[simps]
def inlAlgHom : R →ₐ[S] tsze R M where
  toFun := inl
  map_one' := inl_one _
  map_mul' := inl_mul _
  map_zero' := inl_zero (M := M)
  map_add' := inl_add _
  commutes' _r := (algebraMap_eq_inl' _ _ _ _).symm

variable {R R' S M}

theorem algHom_ext {A} [Semiring A] [Algebra R' A] ⦃f g : tsze R' M →ₐ[R'] A⦄
    (h : ∀ m, f (inr m) = g (inr m)) : f = g :=
  AlgHom.toLinearMap_injective <|
    linearMap_ext (fun _r => (f.commutes _).trans (g.commutes _).symm) h
#align triv_sq_zero_ext.alg_hom_ext TrivSqZeroExt.algHom_ext

@[ext]
theorem algHom_ext' {A} [Semiring A] [Algebra S A] ⦃f g : tsze R M →ₐ[S] A⦄
    (hinl : f.comp (inlAlgHom S R M) = g.comp (inlAlgHom S R M))
    (hinr : f.toLinearMap.comp (inrHom R M |>.restrictScalars S) =
      g.toLinearMap.comp (inrHom R M |>.restrictScalars S)) : f = g :=
  AlgHom.toLinearMap_injective <|
    linearMap_ext (AlgHom.congr_fun hinl) (LinearMap.congr_fun hinr)
#align triv_sq_zero_ext.alg_hom_ext' TrivSqZeroExt.algHom_ext'

variable {A : Type*} [Semiring A] [Algebra S A] [Algebra R' A]

/--
Assemble an algebra morphism `TrivSqZeroExt R M →ₐ[S] A` from separate morphisms on `R` and `M`.

Namely, we require that for an algebra morphism `f : R →ₐ[S] A` and a linear map `g : M →ₗ[S] A`,
we have:

* `g x * g y = 0`: the elements of `M` continue to square to zero.
* `g (r •> x) = f r * g x` and `g (x <• r) = g x * f r`: scalar multiplication on the left and
  right is sent to left- and right- multiplication by the image under `f`.

See `TrivSqZeroExt.liftEquiv` for this as an equiv; namely that any such algebra morphism can be
factored in this way.

When `R` is commutative, this can be invoked with `f = Algebra.ofId R A`, which satisfies `hfg` and
`hgf`. This version is captured as an equiv by `TrivSqZeroExt.liftEquivOfComm`. -/
def lift (f : R →ₐ[S] A) (g : M →ₗ[S] A)
    (hg : ∀ x y, g x * g y = 0)
    (hfg : ∀ r x, g (r •> x) = f r * g x)
    (hgf : ∀ r x, g (x <• r) = g x * f r) : tsze R M →ₐ[S] A :=
  AlgHom.ofLinearMap
    ((f.comp <| fstHom S R M).toLinearMap + g ∘ₗ (sndHom R M |>.restrictScalars S))
    (show f 1 + g (0 : M) = 1 by rw [map_zero, map_one, add_zero])
    (TrivSqZeroExt.ind fun r₁ m₁ =>
      TrivSqZeroExt.ind fun r₂ m₂ => by
        dsimp
        simp only [add_zero, zero_add, add_mul, mul_add, smul_mul_smul, hg, smul_zero,
          op_smul_eq_smul]
        rw [← AlgHom.map_mul, LinearMap.map_add, add_comm (g _), add_assoc, hfg, hgf])
#align triv_sq_zero_ext.lift_aux TrivSqZeroExt.lift

theorem lift_def (f : R →ₐ[S] A) (g : M →ₗ[S] A)
    (hg : ∀ x y, g x * g y = 0)
    (hfg : ∀ r x, g (r • x) = f r * g x)
    (hgf : ∀ r x, g (op r • x) = g x * f r) (x : tsze R M) :
    lift f g hg hfg hgf x = f x.fst + g x.snd :=
  rfl

@[simp]
theorem lift_apply_inl (f : R →ₐ[S] A) (g : M →ₗ[S] A)
    (hg : ∀ x y, g x * g y = 0)
    (hfg : ∀ r x, g (r •> x) = f r * g x)
    (hgf : ∀ r x, g (x <• r) = g x * f r)
    (r : R) :
    lift f g hg hfg hgf (inl r) = f r :=
  show f r + g 0 = f r by rw [map_zero, add_zero]

@[simp]
theorem lift_apply_inr (f : R →ₐ[S] A) (g : M →ₗ[S] A)
    (hg : ∀ x y, g x * g y = 0)
    (hfg : ∀ r x, g (r •> x) = f r * g x)
    (hgf : ∀ r x, g (x <• r) = g x * f r)
    (m : M) :
    lift f g hg hfg hgf (inr m) = g m :=
  show f 0 + g m = g m by rw [map_zero, zero_add]
#align triv_sq_zero_ext.lift_aux_apply_inr TrivSqZeroExt.lift_apply_inr

@[simp]
theorem lift_comp_inlHom (f : R →ₐ[S] A) (g : M →ₗ[S] A)
    (hg : ∀ x y, g x * g y = 0)
    (hfg : ∀ r x, g (r •> x) = f r * g x)
    (hgf : ∀ r x, g (x <• r) = g x * f r) :
    (lift f g hg hfg hgf).comp (inlAlgHom S R M) = f :=
  AlgHom.ext <| lift_apply_inl f g hg hfg hgf

@[simp]
theorem lift_comp_inrHom (f : R →ₐ[S] A) (g : M →ₗ[S] A)
    (hg : ∀ x y, g x * g y = 0)
    (hfg : ∀ r x, g (r •> x) = f r * g x)
    (hgf : ∀ r x, g (x <• r) = g x * f r) :
    (lift f g hg hfg hgf).toLinearMap.comp (inrHom R M |>.restrictScalars S) = g :=
  LinearMap.ext <| lift_apply_inr f g hg hfg hgf
#align triv_sq_zero_ext.lift_aux_comp_inr_hom TrivSqZeroExt.lift_comp_inrHom

/-- When applied to `inr` and `inl` themselves, `lift` is the identity. -/
@[simp]
theorem lift_inlAlgHom_inrHom :
    lift (inlAlgHom _ _ _) (inrHom R M |>.restrictScalars S)
      (inr_mul_inr R) (fun _ _ => (inl_mul_inr _ _).symm) (fun _ _ => (inr_mul_inl _ _).symm) =
    AlgHom.id S (tsze R M) :=
  algHom_ext' (lift_comp_inlHom _ _ _ _ _) (lift_comp_inrHom _ _ _ _ _)
#align triv_sq_zero_ext.lift_aux_inr_hom TrivSqZeroExt.lift_inlAlgHom_inrHomₓ

/-- A universal property of the trivial square-zero extension, providing a unique
`TrivSqZeroExt R M →ₐ[R] A` for every pair of maps `f : R →ₐ[S] A` and `g : M →ₗ[S] A`,
where the range of `g` has no non-zero products, and scaling the input to `g` on the left or right
amounts to a corresponding multiplication by `f` in the output.

This isomorphism is named to match the very similar `Complex.lift`. -/
@[simps! apply symm_apply_coe]
def liftEquiv :
    {fg : (R →ₐ[S] A) × (M →ₗ[S] A) //
      (∀ x y, fg.2 x * fg.2 y = 0) ∧
      (∀ r x, fg.2 (r •> x) = fg.1 r * fg.2 x) ∧
      (∀ r x, fg.2 (x <• r) = fg.2 x * fg.1 r)} ≃ (tsze R M →ₐ[S] A) where
  toFun fg := lift fg.val.1 fg.val.2 fg.prop.1 fg.prop.2.1 fg.prop.2.2
  invFun F :=
    ⟨(F.comp (inlAlgHom _ _ _), F.toLinearMap ∘ₗ (inrHom _ _ |>.restrictScalars _)),
      (fun _x _y =>
        (F.map_mul _ _).symm.trans <| (F.congr_arg <| inr_mul_inr _ _ _).trans F.map_zero),
      (fun _r _x => (F.congr_arg (inl_mul_inr _ _).symm).trans (F.map_mul _ _)),
      (fun _r _x => (F.congr_arg (inr_mul_inl _ _).symm).trans (F.map_mul _ _))⟩
  left_inv _f := Subtype.ext <| Prod.ext (lift_comp_inlHom _ _ _ _ _) (lift_comp_inrHom _ _ _ _ _)
  right_inv _F := algHom_ext' (lift_comp_inlHom _ _ _ _ _) (lift_comp_inrHom _ _ _ _ _)

/-- A simplified version of `TrivSqZeroExt.liftEquiv` for the commutative case. -/
@[simps! apply symm_apply_coe]
def liftEquivOfComm :
    { f : M →ₗ[R'] A // ∀ x y, f x * f y = 0 } ≃ (tsze R' M →ₐ[R'] A) := by
  refine Equiv.trans ?_ liftEquiv
  exact {
    toFun := fun f => ⟨(Algebra.ofId _ _, f.val), f.prop,
      fun r x => by simp [Algebra.smul_def, Algebra.ofId_apply],
      fun r x => by simp [Algebra.smul_def, Algebra.ofId_apply, Algebra.commutes]⟩
    invFun := fun fg => ⟨fg.val.2, fg.prop.1⟩
    left_inv := fun f => rfl
    right_inv := fun fg => Subtype.ext <|
      Prod.ext (AlgHom.toLinearMap_injective <| LinearMap.ext_ring <| by simp)
      rfl }
#align triv_sq_zero_ext.lift TrivSqZeroExt.liftEquiv

section map

variable {N P : Type*} [AddCommMonoid N] [Module R' N] [Module R'ᵐᵒᵖ N] [IsCentralScalar R' N]
  [AddCommMonoid P] [Module R' P] [Module R'ᵐᵒᵖ P] [IsCentralScalar R' P]

/-- Functoriality of `TrivSqZeroExt` when the ring is commutative: a linear map
`f : M →ₗ[R'] N` induces a morphism of `R'`-algebras from `TrivSqZeroExt R' M` to
`TrivSqZeroExt R' N`.

Note that we cannot neatly state the non-commutative case, as we do not have morphisms of bimodules.
-/
def map (f : M →ₗ[R'] N) : TrivSqZeroExt R' M →ₐ[R'] TrivSqZeroExt R' N :=
  liftEquivOfComm ⟨inrHom R' N ∘ₗ f, fun _ _ => inr_mul_inr _ _ _⟩

@[simp]
theorem map_inl (f : M →ₗ[R'] N) (r : R') : map f (inl r) = inl r := by
  rw [map, liftEquivOfComm_apply, lift_apply_inl, Algebra.ofId_apply, algebraMap_eq_inl]

@[simp]
theorem map_inr (f : M →ₗ[R'] N) (x : M) : map f (inr x) = inr (f x) := by
  rw [map, liftEquivOfComm_apply, lift_apply_inr, LinearMap.comp_apply, inrHom_apply]

@[simp]
theorem fst_map (f : M →ₗ[R'] N) (x : TrivSqZeroExt R' M) : fst (map f x) = fst x := by
  simp [map, lift_def, Algebra.ofId_apply, algebraMap_eq_inl]

@[simp]
theorem snd_map (f : M →ₗ[R'] N) (x : TrivSqZeroExt R' M) : snd (map f x) = f (snd x) := by
  simp [map, lift_def, Algebra.ofId_apply, algebraMap_eq_inl]

@[simp]
theorem map_comp_inlAlgHom (f : M →ₗ[R'] N) :
    (map f).comp (inlAlgHom R' R' M) = inlAlgHom R' R' N :=
  AlgHom.ext <| map_inl _

@[simp]
theorem map_comp_inrHom (f : M →ₗ[R'] N) :
    (map f).toLinearMap ∘ₗ inrHom R' M = inrHom R' N ∘ₗ f :=
  LinearMap.ext <| map_inr _

@[simp]
theorem fstHom_comp_map (f : M →ₗ[R'] N) :
    (fstHom R' R' N).comp (map f) = fstHom R' R' M :=
  AlgHom.ext <| fst_map _

@[simp]
theorem sndHom_comp_map (f : M →ₗ[R'] N) :
    sndHom R' N ∘ₗ (map f).toLinearMap = f ∘ₗ sndHom R' M :=
  LinearMap.ext <| snd_map _

@[simp]
theorem map_id : map (LinearMap.id : M →ₗ[R'] M) = AlgHom.id R' _ := by
  apply algHom_ext
  simp only [map_inr, LinearMap.id_coe, id_eq, AlgHom.coe_id, forall_const]

theorem map_comp_map (f : M →ₗ[R'] N) (g : N →ₗ[R'] P) :
    map (g.comp f) = (map g).comp (map f) := by
  apply algHom_ext
  simp only [map_inr, LinearMap.coe_comp, Function.comp_apply, AlgHom.coe_comp, forall_const]

end map

end Algebra

end TrivSqZeroExt
