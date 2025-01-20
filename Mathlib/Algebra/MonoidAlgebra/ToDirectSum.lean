/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Finsupp.ToDFinsupp

/-!
# Conversion between `AddMonoidAlgebra` and homogeneous `DirectSum`

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

/-- Interpret an `AddMonoidAlgebra` as a homogeneous `DirectSum`. -/
def AddMonoidAlgebra.toDirectSum [Semiring M] (f : AddMonoidAlgebra M ι) : ⨁ _ : ι, M :=
  Finsupp.toDFinsupp f

section

variable [DecidableEq ι] [Semiring M]

@[simp]
theorem AddMonoidAlgebra.toDirectSum_single (i : ι) (m : M) :
    AddMonoidAlgebra.toDirectSum (Finsupp.single i m) = DirectSum.of _ i m :=
  Finsupp.toDFinsupp_single i m

variable [∀ m : M, Decidable (m ≠ 0)]

/-- Interpret a homogeneous `DirectSum` as an `AddMonoidAlgebra`. -/
def DirectSum.toAddMonoidAlgebra (f : ⨁ _ : ι, M) : AddMonoidAlgebra M ι :=
  DFinsupp.toFinsupp f

@[simp]
theorem DirectSum.toAddMonoidAlgebra_of (i : ι) (m : M) :
    (DirectSum.of _ i m : ⨁ _ : ι, M).toAddMonoidAlgebra = Finsupp.single i m :=
  DFinsupp.toFinsupp_single i m

@[simp]
theorem AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra (f : AddMonoidAlgebra M ι) :
    f.toDirectSum.toAddMonoidAlgebra = f :=
  Finsupp.toDFinsupp_toFinsupp f

@[simp]
theorem DirectSum.toAddMonoidAlgebra_toDirectSum (f : ⨁ _ : ι, M) :
    f.toAddMonoidAlgebra.toDirectSum = f :=
  (DFinsupp.toFinsupp_toDFinsupp (show Π₀ _ : ι, M from f) : _)

end

end Defs

/-! ### Lemmas about arithmetic operations -/


section Lemmas

namespace AddMonoidAlgebra

@[simp]
theorem toDirectSum_zero [Semiring M] : (0 : AddMonoidAlgebra M ι).toDirectSum = 0 :=
  Finsupp.toDFinsupp_zero

@[simp]
theorem toDirectSum_add [Semiring M] (f g : AddMonoidAlgebra M ι) :
    (f + g).toDirectSum = f.toDirectSum + g.toDirectSum :=
  Finsupp.toDFinsupp_add _ _

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
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): does not find `addHom_ext'`, was `ext (xi xv yi yv) : 4`
  refine Finsupp.addHom_ext' fun xi => AddMonoidHom.ext fun xv => ?_
  refine Finsupp.addHom_ext' fun yi => AddMonoidHom.ext fun yv => ?_
  dsimp only [AddMonoidHom.comp_apply, AddMonoidHom.compl₂_apply, AddMonoidHom.compr₂_apply,
    AddMonoidHom.mul_apply, Finsupp.singleAddHom_apply]
  -- This was not needed before https://github.com/leanprover/lean4/pull/2644
  erw [AddMonoidHom.compl₂_apply]
  -- If we remove the next `rw`, the `erw` after it will complain (when we get an `erw` linter)
  -- that it could be a `rw`. But the `erw` and `rw` will rewrite different occurrences.
  -- So first get rid of the `rw`-able occurrences to force `erw` to do the expensive rewrite only.
  rw [AddMonoidHom.coe_mk, AddMonoidHom.coe_mk]
  -- This was not needed before https://github.com/leanprover/lean4/pull/2644
  erw [AddMonoidHom.coe_mk]
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, toDirectSum_single]
  -- This was not needed before https://github.com/leanprover/lean4/pull/2644
  dsimp
  rw [AddMonoidAlgebra.single_mul_single, AddMonoidHom.coe_mk, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    AddMonoidAlgebra.toDirectSum_single]
  simp only [AddMonoidHom.coe_comp, AddMonoidHom.coe_mul, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Function.comp_apply, toDirectSum_single, AddMonoidHom.id_apply, Finsupp.singleAddHom_apply,
    AddMonoidHom.coe_mulLeft]
  rw [DirectSum.of_mul_of, Mul.gMul_mul]

end AddMonoidAlgebra

namespace DirectSum

variable [DecidableEq ι]

@[simp]
theorem toAddMonoidAlgebra_zero [Semiring M] [∀ m : M, Decidable (m ≠ 0)] :
    toAddMonoidAlgebra 0 = (0 : AddMonoidAlgebra M ι) :=
  DFinsupp.toFinsupp_zero

@[simp]
theorem toAddMonoidAlgebra_add [Semiring M] [∀ m : M, Decidable (m ≠ 0)] (f g : ⨁ _ : ι, M) :
    (f + g).toAddMonoidAlgebra = toAddMonoidAlgebra f + toAddMonoidAlgebra g :=
  DFinsupp.toFinsupp_add _ _

@[simp]
theorem toAddMonoidAlgebra_mul [AddMonoid ι] [Semiring M]
    [∀ m : M, Decidable (m ≠ 0)] (f g : ⨁ _ : ι, M) :
    (f * g).toAddMonoidAlgebra = toAddMonoidAlgebra f * toAddMonoidAlgebra g := by
  apply_fun AddMonoidAlgebra.toDirectSum
  · simp
  · apply Function.LeftInverse.injective
    apply AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra

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

/-- The additive version of `AddMonoidAlgebra.addMonoidAlgebraEquivDirectSum`. -/
@[simps (config := .asFn)]
def addMonoidAlgebraAddEquivDirectSum [DecidableEq ι] [Semiring M] [∀ m : M, Decidable (m ≠ 0)] :
    AddMonoidAlgebra M ι ≃+ ⨁ _ : ι, M :=
  { addMonoidAlgebraEquivDirectSum with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra
    map_add' := AddMonoidAlgebra.toDirectSum_add }

/-- The ring version of `AddMonoidAlgebra.addMonoidAlgebraEquivDirectSum`. -/
@[simps (config := .asFn)]
def addMonoidAlgebraRingEquivDirectSum [DecidableEq ι] [AddMonoid ι] [Semiring M]
    [∀ m : M, Decidable (m ≠ 0)] : AddMonoidAlgebra M ι ≃+* ⨁ _ : ι, M :=
  { (addMonoidAlgebraAddEquivDirectSum : AddMonoidAlgebra M ι ≃+ ⨁ _ : ι, M) with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra
    map_mul' := AddMonoidAlgebra.toDirectSum_mul }

/-- The algebra version of `AddMonoidAlgebra.addMonoidAlgebraEquivDirectSum`. -/
@[simps (config := .asFn)]
def addMonoidAlgebraAlgEquivDirectSum [DecidableEq ι] [AddMonoid ι] [CommSemiring R] [Semiring A]
    [Algebra R A] [∀ m : A, Decidable (m ≠ 0)] : AddMonoidAlgebra A ι ≃ₐ[R] ⨁ _ : ι, A :=
  { (addMonoidAlgebraRingEquivDirectSum : AddMonoidAlgebra A ι ≃+* ⨁ _ : ι, A) with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra
    commutes' := fun _r => AddMonoidAlgebra.toDirectSum_single _ _ }

end Equivs
