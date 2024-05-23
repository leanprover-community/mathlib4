/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Finsupp.ToDFinsupp

#align_import algebra.monoid_algebra.to_direct_sum from "leanprover-community/mathlib"@"c0a51cf2de54089d69301befc4c73bbc2f5c7342"

/-!
# Conversion between `AddMonoidAlgebra` and homogenous `DirectSum`

This module provides conversions between `AddMonoidAlgebra` and `DirectSum`.
The latter is essentially a dependent version of the former.

Note that since `direct_sum.has_mul` combines indices additively, there is no equivalent to
`MonoidAlgebra`.

## Main definitions

* `AddMonoidAlgebra.toDirectSum : AddMonoidAlgebra M ι → (⨁ i : ι, M)`
* `DirectSum.toAddMonoidAlgebra : (⨁ i : ι, M) → AddMonoidAlgebra M ι`
* Bundled equiv versions of the above:
  * `addMonoidAlgebraEquivDirectSum : AddMonoidAlgebra M ι ≃ (⨁ i : ι, M)`
  * `addMonoidAlgebraAddEquivDirectSum : AddMonoidAlgebra M ι ≃+ (⨁ i : ι, M)`
  * `addMonoidAlgebraRingEquivDirectSum R : AddMonoidAlgebra M ι ≃+* (⨁ i : ι, M)`
  * `addMonoidAlgebraAlgEquivDirectSum R : AddMonoidAlgebra A ι ≃ₐ[R] (⨁ i : ι, A)`

## Theorems

The defining feature of these operations is that they map `Finsupp.single` to
`DirectSum.of` and vice versa:

* `AddMonoidAlgebra.toDirectSum_single`
* `DirectSum.toAddMonoidAlgebra_of`

as well as preserving arithmetic operations.

For the bundled equivalences, we provide lemmas that they reduce to
`AddMonoidAlgebra.toDirectSum`:

* `addMonoidAlgebraAddEquivDirectSum_apply`
* `add_monoid_algebra_lequiv_direct_sum_apply`
* `addMonoidAlgebraAddEquivDirectSum_symm_apply`
* `add_monoid_algebra_lequiv_direct_sum_symm_apply`

## Implementation notes

This file largely just copies the API of `Mathlib/Data/Finsupp/ToDFinsupp.lean`, and reuses the
proofs. Recall that `AddMonoidAlgebra M ι` is defeq to `ι →₀ M` and `⨁ i : ι, M` is defeq to
`Π₀ i : ι, M`.

Note that there is no `AddMonoidAlgebra` equivalent to `Finsupp.single`, so many statements
still involve this definition.
-/


variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

open DirectSum

/-! ### Basic definitions and lemmas -/


section Defs

/-- Interpret an `AddMonoidAlgebra` as a homogenous `DirectSum`. -/
def AddMonoidAlgebra.toDirectSum [Semiring M] (f : AddMonoidAlgebra M ι) : ⨁ _ : ι, M :=
  Finsupp.toDFinsupp f
#align add_monoid_algebra.to_direct_sum AddMonoidAlgebra.toDirectSum

section

variable [DecidableEq ι] [Semiring M]

@[simp]
theorem AddMonoidAlgebra.toDirectSum_single (i : ι) (m : M) :
    AddMonoidAlgebra.toDirectSum (Finsupp.single i m) = DirectSum.of _ i m :=
  Finsupp.toDFinsupp_single i m
#align add_monoid_algebra.to_direct_sum_single AddMonoidAlgebra.toDirectSum_single

variable [∀ m : M, Decidable (m ≠ 0)]

/-- Interpret a homogenous `DirectSum` as an `AddMonoidAlgebra`. -/
def DirectSum.toAddMonoidAlgebra (f : ⨁ _ : ι, M) : AddMonoidAlgebra M ι :=
  DFinsupp.toFinsupp f
#align direct_sum.to_add_monoid_algebra DirectSum.toAddMonoidAlgebra

@[simp]
theorem DirectSum.toAddMonoidAlgebra_of (i : ι) (m : M) :
    (DirectSum.of _ i m : ⨁ _ : ι, M).toAddMonoidAlgebra = Finsupp.single i m :=
  DFinsupp.toFinsupp_single i m
#align direct_sum.to_add_monoid_algebra_of DirectSum.toAddMonoidAlgebra_of

@[simp]
theorem AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra (f : AddMonoidAlgebra M ι) :
    f.toDirectSum.toAddMonoidAlgebra = f :=
  Finsupp.toDFinsupp_toFinsupp f
#align add_monoid_algebra.to_direct_sum_to_add_monoid_algebra AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra

@[simp]
theorem DirectSum.toAddMonoidAlgebra_toDirectSum (f : ⨁ _ : ι, M) :
    f.toAddMonoidAlgebra.toDirectSum = f :=
  (DFinsupp.toFinsupp_toDFinsupp (show Π₀ _ : ι, M from f) : _)
#align direct_sum.to_add_monoid_algebra_to_direct_sum DirectSum.toAddMonoidAlgebra_toDirectSum

end

end Defs

/-! ### Lemmas about arithmetic operations -/


section Lemmas

namespace AddMonoidAlgebra

@[simp]
theorem toDirectSum_zero [Semiring M] : (0 : AddMonoidAlgebra M ι).toDirectSum = 0 :=
  Finsupp.toDFinsupp_zero
#align add_monoid_algebra.to_direct_sum_zero AddMonoidAlgebra.toDirectSum_zero

@[simp]
theorem toDirectSum_add [Semiring M] (f g : AddMonoidAlgebra M ι) :
    (f + g).toDirectSum = f.toDirectSum + g.toDirectSum :=
  Finsupp.toDFinsupp_add _ _
#align add_monoid_algebra.to_direct_sum_add AddMonoidAlgebra.toDirectSum_add

@[simp]
theorem toDirectSum_mul [DecidableEq ι] [AddMonoid ι] [Semiring M] (f g : AddMonoidAlgebra M ι) :
    (f * g).toDirectSum = f.toDirectSum * g.toDirectSum := by
  let to_hom : AddMonoidAlgebra M ι →+ ⨁ _ : ι, M :=
  { toFun := toDirectSum
    map_zero' := toDirectSum_zero
    map_add' := toDirectSum_add }
  show to_hom (f * g) = to_hom f * to_hom g
  let _ : NonUnitalNonAssocSemiring (ι →₀ M) := AddMonoidAlgebra.nonUnitalNonAssocSemiring
  revert f g
  rw [AddMonoidHom.map_mul_iff]
  -- Porting note: does not find `addHom_ext'`, was `ext (xi xv yi yv) : 4`
  refine Finsupp.addHom_ext' fun xi => AddMonoidHom.ext fun xv => ?_
  refine Finsupp.addHom_ext' fun yi => AddMonoidHom.ext fun yv => ?_
  dsimp only [AddMonoidHom.comp_apply, AddMonoidHom.compl₂_apply, AddMonoidHom.compr₂_apply,
    AddMonoidHom.mul_apply, Finsupp.singleAddHom_apply]
  -- This was not needed before leanprover/lean4#2644
  erw [AddMonoidHom.compl₂_apply]
  -- This was not needed before leanprover/lean4#2644
  erw [AddMonoidHom.coe_mk]
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, toDirectSum_single]
  -- This was not needed before leanprover/lean4#2644
  dsimp
  erw [AddMonoidAlgebra.single_mul_single, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    AddMonoidAlgebra.toDirectSum_single]
  simp only [AddMonoidHom.coe_comp, AddMonoidHom.coe_mul, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Function.comp_apply, toDirectSum_single, AddMonoidHom.id_apply, Finsupp.singleAddHom_apply,
    AddMonoidHom.coe_mulLeft]
  erw [DirectSum.of_mul_of, Mul.gMul_mul]
#align add_monoid_algebra.to_direct_sum_mul AddMonoidAlgebra.toDirectSum_mul

end AddMonoidAlgebra

namespace DirectSum

variable [DecidableEq ι]

@[simp]
theorem toAddMonoidAlgebra_zero [Semiring M] [∀ m : M, Decidable (m ≠ 0)] :
    toAddMonoidAlgebra 0 = (0 : AddMonoidAlgebra M ι) :=
  DFinsupp.toFinsupp_zero
#align direct_sum.to_add_monoid_algebra_zero DirectSum.toAddMonoidAlgebra_zero

@[simp]
theorem toAddMonoidAlgebra_add [Semiring M] [∀ m : M, Decidable (m ≠ 0)] (f g : ⨁ _ : ι, M) :
    (f + g).toAddMonoidAlgebra = toAddMonoidAlgebra f + toAddMonoidAlgebra g :=
  DFinsupp.toFinsupp_add _ _
#align direct_sum.to_add_monoid_algebra_add DirectSum.toAddMonoidAlgebra_add

@[simp]
theorem toAddMonoidAlgebra_mul [AddMonoid ι] [Semiring M]
    [∀ m : M, Decidable (m ≠ 0)] (f g : ⨁ _ : ι, M) :
    (f * g).toAddMonoidAlgebra = toAddMonoidAlgebra f * toAddMonoidAlgebra g := by
  apply_fun AddMonoidAlgebra.toDirectSum
  · simp
  · apply Function.LeftInverse.injective
    apply AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra
#align direct_sum.to_add_monoid_algebra_mul DirectSum.toAddMonoidAlgebra_mul

end DirectSum

end Lemmas

/-! ### Bundled `Equiv`s -/


section Equivs

/-- `AddMonoidAlgebra.toDirectSum` and `DirectSum.toAddMonoidAlgebra` together form an
equiv. -/
@[simps (config := .asFn)]
def addMonoidAlgebraEquivDirectSum [DecidableEq ι] [Semiring M] [∀ m : M, Decidable (m ≠ 0)] :
    AddMonoidAlgebra M ι ≃ ⨁ _ : ι, M :=
  { finsuppEquivDFinsupp with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra }
#align add_monoid_algebra_equiv_direct_sum addMonoidAlgebraEquivDirectSum

/-- The additive version of `AddMonoidAlgebra.addMonoidAlgebraEquivDirectSum`.  -/
@[simps (config := .asFn)]
def addMonoidAlgebraAddEquivDirectSum [DecidableEq ι] [Semiring M] [∀ m : M, Decidable (m ≠ 0)] :
    AddMonoidAlgebra M ι ≃+ ⨁ _ : ι, M :=
  { addMonoidAlgebraEquivDirectSum with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra
    map_add' := AddMonoidAlgebra.toDirectSum_add }
#align add_monoid_algebra_add_equiv_direct_sum addMonoidAlgebraAddEquivDirectSum

/-- The ring version of `AddMonoidAlgebra.addMonoidAlgebraEquivDirectSum`.  -/
@[simps (config := .asFn)]
def addMonoidAlgebraRingEquivDirectSum [DecidableEq ι] [AddMonoid ι] [Semiring M]
    [∀ m : M, Decidable (m ≠ 0)] : AddMonoidAlgebra M ι ≃+* ⨁ _ : ι, M :=
  { (addMonoidAlgebraAddEquivDirectSum : AddMonoidAlgebra M ι ≃+ ⨁ _ : ι, M) with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra
    map_mul' := AddMonoidAlgebra.toDirectSum_mul }
#align add_monoid_algebra_ring_equiv_direct_sum addMonoidAlgebraRingEquivDirectSum

/-- The algebra version of `AddMonoidAlgebra.addMonoidAlgebraEquivDirectSum`. -/
@[simps (config := .asFn)]
def addMonoidAlgebraAlgEquivDirectSum [DecidableEq ι] [AddMonoid ι] [CommSemiring R] [Semiring A]
    [Algebra R A] [∀ m : A, Decidable (m ≠ 0)] : AddMonoidAlgebra A ι ≃ₐ[R] ⨁ _ : ι, A :=
  { (addMonoidAlgebraRingEquivDirectSum : AddMonoidAlgebra A ι ≃+* ⨁ _ : ι, A) with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra
    commutes' := fun _r => AddMonoidAlgebra.toDirectSum_single _ _ }
#align add_monoid_algebra_alg_equiv_direct_sum addMonoidAlgebraAlgEquivDirectSum

end Equivs
