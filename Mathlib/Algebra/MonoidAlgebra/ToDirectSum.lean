/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module algebra.monoid_algebra.to_direct_sum
! leanprover-community/mathlib commit c0a51cf2de54089d69301befc4c73bbc2f5c7342
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Finsupp.ToDfinsupp
-- porting note: Added import to bring pointwise multiplication into scope
import Mathlib.Data.Finsupp.Pointwise

/-!
# Conversion between `add_monoid_algebra` and homogenous `direct_sum`

This module provides conversions between `add_monoid_algebra` and `direct_sum`.
The latter is essentially a dependent version of the former.

Note that since `direct_sum.has_mul` combines indices additively, there is no equivalent to
`monoid_algebra`.

## Main definitions

* `add_monoid_algebra.to_direct_sum : add_monoid_algebra M ι → (⨁ i : ι, M)`
* `direct_sum.to_add_monoid_algebra : (⨁ i : ι, M) → add_monoid_algebra M ι`
* Bundled equiv versions of the above:
  * `add_monoid_algebra_equiv_direct_sum : add_monoid_algebra M ι ≃ (⨁ i : ι, M)`
  * `add_monoid_algebra_add_equiv_direct_sum : add_monoid_algebra M ι ≃+ (⨁ i : ι, M)`
  * `add_monoid_algebra_ring_equiv_direct_sum R : add_monoid_algebra M ι ≃+* (⨁ i : ι, M)`
  * `add_monoid_algebra_alg_equiv_direct_sum R : add_monoid_algebra A ι ≃ₐ[R] (⨁ i : ι, A)`

## Theorems

The defining feature of these operations is that they map `finsupp.single` to
`direct_sum.of` and vice versa:

* `add_monoid_algebra.to_direct_sum_single`
* `direct_sum.to_add_monoid_algebra_of`

as well as preserving arithmetic operations.

For the bundled equivalences, we provide lemmas that they reduce to
`add_monoid_algebra.to_direct_sum`:

* `add_monoid_algebra_add_equiv_direct_sum_apply`
* `add_monoid_algebra_lequiv_direct_sum_apply`
* `add_monoid_algebra_add_equiv_direct_sum_symm_apply`
* `add_monoid_algebra_lequiv_direct_sum_symm_apply`

## Implementation notes

This file largely just copies the API of `data/finsupp/to_dfinsupp`, and reuses the proofs.
Recall that `add_monoid_algebra M ι` is defeq to `ι →₀ M` and `⨁ i : ι, M` is defeq to
`Π₀ i : ι, M`.

Note that there is no `add_monoid_algebra` equivalent to `finsupp.single`, so many statements
still involve this definition.
-/


variable {ι : Type _} {R : Type _} {M : Type _} {A : Type _}

open DirectSum

/-! ### Basic definitions and lemmas -/


section Defs

/-- Interpret a `add_monoid_algebra` as a homogenous `direct_sum`. -/
def AddMonoidAlgebra.toDirectSum [Semiring M] (f : AddMonoidAlgebra M ι) : ⨁ i : ι, M :=
  Finsupp.toDfinsupp f
#align add_monoid_algebra.to_direct_sum AddMonoidAlgebra.toDirectSum

section

variable [DecidableEq ι] [Semiring M]

@[simp]
theorem AddMonoidAlgebra.toDirectSum_single (i : ι) (m : M) :
    AddMonoidAlgebra.toDirectSum (Finsupp.single i m) = DirectSum.of _ i m :=
  Finsupp.toDfinsupp_single i m
#align add_monoid_algebra.to_direct_sum_single AddMonoidAlgebra.toDirectSum_single

variable [∀ m : M, Decidable (m ≠ 0)]

/-- Interpret a homogenous `direct_sum` as a `add_monoid_algebra`. -/
def DirectSum.toAddMonoidAlgebra (f : ⨁ i : ι, M) : AddMonoidAlgebra M ι :=
  Dfinsupp.toFinsupp f
#align direct_sum.to_add_monoid_algebra DirectSum.toAddMonoidAlgebra

@[simp]
theorem DirectSum.toAddMonoidAlgebra_of (i : ι) (m : M) :
    (DirectSum.of _ i m : ⨁ i : ι, M).toAddMonoidAlgebra = Finsupp.single i m :=
  Dfinsupp.toFinsupp_single i m
#align direct_sum.to_add_monoid_algebra_of DirectSum.toAddMonoidAlgebra_of

@[simp]
theorem AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra (f : AddMonoidAlgebra M ι) :
    f.toDirectSum.toAddMonoidAlgebra = f :=
  Finsupp.toDfinsupp_toFinsupp f
#align add_monoid_algebra.to_direct_sum_to_add_monoid_algebra AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra

-- porting note: Not needed in mathlib
instance : Coe (DirectSum ι fun i ↦ M) ( Π₀ _i : ι, M) where
   coe s := s

@[simp]
theorem DirectSum.toAddMonoidAlgebra_toDirectSum (f : ⨁ i : ι, M) :
    f.toAddMonoidAlgebra.toDirectSum = f := by {
      rw [DirectSum.toAddMonoidAlgebra, AddMonoidAlgebra.toDirectSum]
      exact @Dfinsupp.toFinsupp_toDfinsupp ι M _ _ _ f
    }
#align direct_sum.to_add_monoid_algebra_to_direct_sum DirectSum.toAddMonoidAlgebra_toDirectSum

end

end Defs

/-! ### Lemmas about arithmetic operations -/


section Lemmas

namespace AddMonoidAlgebra

@[simp]
theorem toDirectSum_zero [Semiring M] : (0 : AddMonoidAlgebra M ι).toDirectSum = 0 :=
  Finsupp.toDfinsupp_zero
#align add_monoid_algebra.to_direct_sum_zero AddMonoidAlgebra.toDirectSum_zero

@[simp]
theorem toDirectSum_add [Semiring M] (f g : AddMonoidAlgebra M ι) :
    (f + g).toDirectSum = f.toDirectSum + g.toDirectSum :=
  Finsupp.toDfinsupp_add _ _
#align add_monoid_algebra.to_direct_sum_add AddMonoidAlgebra.toDirectSum_add


instance [MulZeroClass M] : Mul (Π₀ _i : ι, M) :=
  ⟨Dfinsupp.zipWith (fun _i => (· * ·)) (fun _i => mul_zero 0)⟩
--instance MulDFinsupp {β : ι → M } [Semiring M] :  HMul (Dfinsupp ι (Π₀ _i, M)) (Dfinsupp (Π₀ _i, M)) := _
instance [DecidableEq ι] [AddMonoid ι] [Semiring M] : Mul (AddMonoidAlgebra M ι) :=
  ⟨Dfinsupp.zipWith (fun _i => (· * ·)) (fun _i => mul_zero 0)⟩
-- instance [Semiring M] : HMul (ι →₀ M) (ι →₀ M) (ι →₀ M) where
--   hMul := fun f g => (f i) * (g i)
-- [Semiring M] Π₀ i, β i
-- -- port note: not needed in mathlib
@[simp]
theorem toDfinsupp_mul [MulZeroClass M] (f g : ι →₀ M) :
    (f * g).toDfinsupp = f.toDfinsupp * g.toDfinsupp :=
       FunLike.coe_injective rfl



@[simp]
theorem toDirectSum_mul [DecidableEq ι] [AddMonoid ι] [Semiring M] (f g : AddMonoidAlgebra M ι) :
    (f * g).toDirectSum = f.toDirectSum * g.toDirectSum := by
      -- rw [AddMonoidAlgebra.toDirectSum]
      -- rw [AddMonoidAlgebra.toDirectSum]
      -- rw [AddMonoidAlgebra.toDirectSum]
      -- exact toDfinsupp_mul f g
      let to_hom : AddMonoidAlgebra M ι →+ ⨁ i : ι, M :=
        {
          toFun := toDirectSum
          map_zero' := rfl
          map_add' := by simp only [toDirectSum_add, forall_const]
        }
      show to_hom (f * g) = to_hom f * to_hom g
      revert f g
      rw [@AddMonoidHom.map_mul_iff (AddMonoidAlgebra M ι) (⨁ i : ι, M) _ _ to_hom ]
      ext (xi xv yi yv) : 4
      dsimp only [AddMonoidHom.comp_apply, AddMonoidHom.compl₂_apply, AddMonoidHom.compr₂_apply,
        AddMonoidHom.mul_apply, AddEquiv.coe_toAddMonoidHom, Finsupp.singleAddHom_apply]
      simp [AddMonoidAlgebra.single_mul_single, AddMonoidHom.coe_mk,
        AddMonoidAlgebra.toDirectSum_single, DirectSum.of_mul_of, Mul.gMul_mul]
      exact toDfinsupp_mul xi xv
#align add_monoid_algebra.to_direct_sum_mul AddMonoidAlgebra.toDirectSum_mul

end AddMonoidAlgebra

namespace DirectSum

variable [DecidableEq ι]

@[simp]
theorem toAddMonoidAlgebra_zero [Semiring M] [∀ m : M, Decidable (m ≠ 0)] :
    toAddMonoidAlgebra 0 = (0 : AddMonoidAlgebra M ι) :=
  Dfinsupp.toFinsupp_zero
#align direct_sum.to_add_monoid_algebra_zero DirectSum.toAddMonoidAlgebra_zero

@[simp]
theorem toAddMonoidAlgebra_add [Semiring M] [∀ m : M, Decidable (m ≠ 0)] (f g : ⨁ i : ι, M) :
    (f + g).toAddMonoidAlgebra = toAddMonoidAlgebra f + toAddMonoidAlgebra g :=
  Dfinsupp.toFinsupp_add _ _
#align direct_sum.to_add_monoid_algebra_add DirectSum.toAddMonoidAlgebra_add

@[simp]
theorem toAddMonoidAlgebra_mul [AddMonoid ι] [Semiring M] [∀ m : M, Decidable (m ≠ 0)]
    (f g : ⨁ i : ι, M) : (f * g).toAddMonoidAlgebra = toAddMonoidAlgebra f * toAddMonoidAlgebra g :=
  by
  apply_fun AddMonoidAlgebra.toDirectSum
  · simp
  · apply Function.LeftInverse.injective
    apply AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra
#align direct_sum.to_add_monoid_algebra_mul DirectSum.toAddMonoidAlgebra_mul

end DirectSum

end Lemmas

/-! ### Bundled `equiv`s -/


section Equivs

/-- `add_monoid_algebra.to_direct_sum` and `direct_sum.to_add_monoid_algebra` together form an
equiv. -/
@[simps (config := { fullyApplied := false })]
def addMonoidAlgebraEquivDirectSum [DecidableEq ι] [Semiring M] [∀ m : M, Decidable (m ≠ 0)] :
    AddMonoidAlgebra M ι ≃ ⨁ i : ι, M :=
  { finsuppEquivDfinsupp with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra }
#align add_monoid_algebra_equiv_direct_sum addMonoidAlgebraEquivDirectSum

/-- The additive version of `add_monoid_algebra.to_add_monoid_algebra`. Note that this is
`noncomputable` because `add_monoid_algebra.has_add` is noncomputable. -/
@[simps (config := { fullyApplied := false })]
def addMonoidAlgebraAddEquivDirectSum [DecidableEq ι] [Semiring M] [∀ m : M, Decidable (m ≠ 0)] :
    AddMonoidAlgebra M ι ≃+ ⨁ i : ι, M :=
  {
    addMonoidAlgebraEquivDirectSum with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra
    map_add' := AddMonoidAlgebra.toDirectSum_add }
#align add_monoid_algebra_add_equiv_direct_sum addMonoidAlgebraAddEquivDirectSum

/-- The ring version of `add_monoid_algebra.to_add_monoid_algebra`. Note that this is
`noncomputable` because `add_monoid_algebra.has_add` is noncomputable. -/
@[simps (config := { fullyApplied := false })]
def addMonoidAlgebraRingEquivDirectSum [DecidableEq ι] [AddMonoid ι] [Semiring M]
    [∀ m : M, Decidable (m ≠ 0)] : AddMonoidAlgebra M ι ≃+* ⨁ i : ι, M :=
  {
    (addMonoidAlgebraAddEquivDirectSum :
      AddMonoidAlgebra M ι ≃+
        ⨁ i : ι, M) with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra
    map_mul' := AddMonoidAlgebra.toDirectSum_mul }
#align add_monoid_algebra_ring_equiv_direct_sum addMonoidAlgebraRingEquivDirectSum

/-- The algebra version of `add_monoid_algebra.to_add_monoid_algebra`. Note that this is
`noncomputable` because `add_monoid_algebra.has_add` is noncomputable. -/
@[simps (config := { fullyApplied := false })]
def addMonoidAlgebraAlgEquivDirectSum [DecidableEq ι] [AddMonoid ι] [CommSemiring R] [Semiring A]
    [Algebra R A] [∀ m : A, Decidable (m ≠ 0)] : AddMonoidAlgebra A ι ≃ₐ[R] ⨁ i : ι, A :=
  {
    (addMonoidAlgebraRingEquivDirectSum :
      AddMonoidAlgebra A ι ≃+*
        ⨁ i : ι, A) with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra
    commutes' := fun r => AddMonoidAlgebra.toDirectSum_single _ _ }
#align add_monoid_algebra_alg_equiv_direct_sum addMonoidAlgebraAlgEquivDirectSum

end Equivs
