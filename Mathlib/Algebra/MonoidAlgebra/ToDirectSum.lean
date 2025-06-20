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

Note that since `DirectSum.instMul` combines indices additively, there is no equivalent to
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
  (DFinsupp.toFinsupp_toDFinsupp (show Π₀ _ : ι, M from f) :)

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
theorem toDirectSum_natCast [DecidableEq ι] [AddMonoid ι] [Semiring M] (n : ℕ) :
    (n : AddMonoidAlgebra M ι).toDirectSum = n :=
  Finsupp.toDFinsupp_single _ _

@[simp]
theorem toDirectSum_ofNat [DecidableEq ι] [AddMonoid ι] [Semiring M] (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : AddMonoidAlgebra M ι).toDirectSum = ofNat(n) :=
  Finsupp.toDFinsupp_single _ _

@[simp]
theorem toDirectSum_sub [Ring M] (f g : AddMonoidAlgebra M ι) :
    (f - g).toDirectSum = f.toDirectSum - g.toDirectSum :=
  Finsupp.toDFinsupp_sub _ _

@[simp]
theorem toDirectSum_neg [Ring M] (f : AddMonoidAlgebra M ι) :
    (- f).toDirectSum = - f.toDirectSum :=
  Finsupp.toDFinsupp_neg _

@[simp]
theorem toDirectSum_intCast [DecidableEq ι] [AddMonoid ι] [Ring M] (z : ℤ) :
    (Int.cast z : AddMonoidAlgebra M ι).toDirectSum = z :=
  Finsupp.toDFinsupp_single _ _

@[simp]
theorem toDirectSum_one [DecidableEq ι] [Zero ι] [Semiring M] :
    (1 : AddMonoidAlgebra M ι).toDirectSum = 1 :=
  Finsupp.toDFinsupp_single _ _

@[simp]
theorem toDirectSum_mul [DecidableEq ι] [AddMonoid ι] [Semiring M] (f g : AddMonoidAlgebra M ι) :
    (f * g).toDirectSum = f.toDirectSum * g.toDirectSum := by
  let to_hom : AddMonoidAlgebra M ι →+ ⨁ _ : ι, M :=
  { toFun := toDirectSum
    map_zero' := toDirectSum_zero
    map_add' := toDirectSum_add }
  change to_hom (f * g) = to_hom f * to_hom g
  revert f g
  rw [AddMonoidHom.map_mul_iff]
  ext xi xv yi yv : 4
  simp [to_hom, AddMonoidAlgebra.single_mul_single, DirectSum.of_mul_of]

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
theorem toAddMonoidAlgebra_natCast [AddMonoid ι] [Semiring M] [∀ m : M, Decidable (m ≠ 0)] (n : ℕ) :
    (n : ⨁ _ : ι, M).toAddMonoidAlgebra = n :=
  DFinsupp.toFinsupp_single _ _

@[simp]
theorem toAddMonoidAlgebra_ofNat [AddMonoid ι] [Semiring M] [∀ m : M, Decidable (m ≠ 0)] (n : ℕ)
    [n.AtLeastTwo] :
    (ofNat(n) : ⨁ _ : ι, M).toAddMonoidAlgebra = ofNat(n) :=
  DFinsupp.toFinsupp_single _ _

@[simp]
theorem toAddMonoidAlgebra_sub [Ring M] [∀ m : M, Decidable (m ≠ 0)] (f g : ⨁ _ : ι, M) :
    (f - g).toAddMonoidAlgebra = toAddMonoidAlgebra f - toAddMonoidAlgebra g :=
  DFinsupp.toFinsupp_sub _ _

@[simp]
theorem toAddMonoidAlgebra_neg [Ring M] [∀ m : M, Decidable (m ≠ 0)] (f : ⨁ _ : ι, M) :
    (- f).toAddMonoidAlgebra = - toAddMonoidAlgebra f :=
  DFinsupp.toFinsupp_neg _

@[simp]
theorem toAddMonoidAlgebra_intCast [AddMonoid ι] [Ring M] [∀ m : M, Decidable (m ≠ 0)] (z : ℤ) :
    (z : ⨁ _ : ι, M).toAddMonoidAlgebra = z :=
  DFinsupp.toFinsupp_single _ _

@[simp]
theorem toAddMonoidAlgebra_one [Zero ι] [Semiring M] [∀ m : M, Decidable (m ≠ 0)] :
    (1 : ⨁ _ : ι, M).toAddMonoidAlgebra = 1 :=
  DFinsupp.toFinsupp_single _ _

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
@[simps -fullyApplied]
def addMonoidAlgebraEquivDirectSum [DecidableEq ι] [Semiring M] [∀ m : M, Decidable (m ≠ 0)] :
    AddMonoidAlgebra M ι ≃ ⨁ _ : ι, M :=
  { finsuppEquivDFinsupp with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra }

/-- The additive version of `AddMonoidAlgebra.addMonoidAlgebraEquivDirectSum`. -/
@[simps -fullyApplied]
def addMonoidAlgebraAddEquivDirectSum [DecidableEq ι] [Semiring M] [∀ m : M, Decidable (m ≠ 0)] :
    AddMonoidAlgebra M ι ≃+ ⨁ _ : ι, M :=
  { addMonoidAlgebraEquivDirectSum with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra
    map_add' := AddMonoidAlgebra.toDirectSum_add }

/-- The ring version of `AddMonoidAlgebra.addMonoidAlgebraEquivDirectSum`. -/
@[simps -fullyApplied]
def addMonoidAlgebraRingEquivDirectSum [DecidableEq ι] [AddMonoid ι] [Semiring M]
    [∀ m : M, Decidable (m ≠ 0)] : AddMonoidAlgebra M ι ≃+* ⨁ _ : ι, M :=
  { (addMonoidAlgebraAddEquivDirectSum : AddMonoidAlgebra M ι ≃+ ⨁ _ : ι, M) with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra
    map_mul' := AddMonoidAlgebra.toDirectSum_mul }

/-- The algebra version of `AddMonoidAlgebra.addMonoidAlgebraEquivDirectSum`. -/
@[simps -fullyApplied]
def addMonoidAlgebraAlgEquivDirectSum [DecidableEq ι] [AddMonoid ι] [CommSemiring R] [Semiring A]
    [Algebra R A] [∀ m : A, Decidable (m ≠ 0)] : AddMonoidAlgebra A ι ≃ₐ[R] ⨁ _ : ι, A :=
  { (addMonoidAlgebraRingEquivDirectSum : AddMonoidAlgebra A ι ≃+* ⨁ _ : ι, A) with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra
    commutes' := fun _r => AddMonoidAlgebra.toDirectSum_single _ _ }

@[simp]
theorem AddMonoidAlgebra.toDirectSum_pow [DecidableEq ι] [AddMonoid ι] [Semiring M]
    (f : AddMonoidAlgebra M ι) (n : ℕ) :
    (f ^ n).toDirectSum = f.toDirectSum ^ n := by
  classical exact map_pow addMonoidAlgebraRingEquivDirectSum f n

@[simp]
theorem DirectSum.toAddMonoidAlgebra_pow [DecidableEq ι] [AddMonoid ι] [Semiring M]
    [∀ m : M, Decidable (m ≠ 0)] (f : ⨁ _ : ι, M) (n : ℕ):
    (f ^ n).toAddMonoidAlgebra = toAddMonoidAlgebra f ^ n :=  by
  classical exact map_pow addMonoidAlgebraRingEquivDirectSum.symm f n

end Equivs
