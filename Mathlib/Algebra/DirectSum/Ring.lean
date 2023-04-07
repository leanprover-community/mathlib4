/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module algebra.direct_sum.ring
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GradedMonoid
import Mathbin.Algebra.DirectSum.Basic

/-!
# Additively-graded multiplicative structures on `⨁ i, A i`

This module provides a set of heterogeneous typeclasses for defining a multiplicative structure
over `⨁ i, A i` such that `(*) : A i → A j → A (i + j)`; that is to say, `A` forms an
additively-graded ring. The typeclasses are:

* `direct_sum.gnon_unital_non_assoc_semiring A`
* `direct_sum.gsemiring A`
* `direct_sum.gring A`
* `direct_sum.gcomm_semiring A`
* `direct_sum.gcomm_ring A`

Respectively, these imbue the external direct sum `⨁ i, A i` with:

* `direct_sum.non_unital_non_assoc_semiring`, `direct_sum.non_unital_non_assoc_ring`
* `direct_sum.semiring`
* `direct_sum.ring`
* `direct_sum.comm_semiring`
* `direct_sum.comm_ring`

the base ring `A 0` with:

* `direct_sum.grade_zero.non_unital_non_assoc_semiring`,
  `direct_sum.grade_zero.non_unital_non_assoc_ring`
* `direct_sum.grade_zero.semiring`
* `direct_sum.grade_zero.ring`
* `direct_sum.grade_zero.comm_semiring`
* `direct_sum.grade_zero.comm_ring`

and the `i`th grade `A i` with `A 0`-actions (`•`) defined as left-multiplication:

* `direct_sum.grade_zero.has_smul (A 0)`, `direct_sum.grade_zero.smul_with_zero (A 0)`
* `direct_sum.grade_zero.module (A 0)`
* (nothing)
* (nothing)
* (nothing)

Note that in the presence of these instances, `⨁ i, A i` itself inherits an `A 0`-action.

`direct_sum.of_zero_ring_hom : A 0 →+* ⨁ i, A i` provides `direct_sum.of A 0` as a ring
homomorphism.

`direct_sum.to_semiring` extends `direct_sum.to_add_monoid` to produce a `ring_hom`.

## Direct sums of subobjects

Additionally, this module provides helper functions to construct `gsemiring` and `gcomm_semiring`
instances for:

* `A : ι → submonoid S`:
  `direct_sum.gsemiring.of_add_submonoids`, `direct_sum.gcomm_semiring.of_add_submonoids`.
* `A : ι → subgroup S`:
  `direct_sum.gsemiring.of_add_subgroups`, `direct_sum.gcomm_semiring.of_add_subgroups`.
* `A : ι → submodule S`:
  `direct_sum.gsemiring.of_submodules`, `direct_sum.gcomm_semiring.of_submodules`.

If `complete_lattice.independent (set.range A)`, these provide a gradation of `⨆ i, A i`, and the
mapping `⨁ i, A i →+ ⨆ i, A i` can be obtained as
`direct_sum.to_monoid (λ i, add_submonoid.inclusion $ le_supr A i)`.

## tags

graded ring, filtered ring, direct sum, add_submonoid
-/


variable {ι : Type _} [DecidableEq ι]

namespace DirectSum

open DirectSum

/-! ### Typeclasses -/


section Defs

variable (A : ι → Type _)

/-- A graded version of `non_unital_non_assoc_semiring`. -/
class GnonUnitalNonAssocSemiring [Add ι] [∀ i, AddCommMonoid (A i)] extends
  GradedMonoid.GMul A where
  mul_zero : ∀ {i j} (a : A i), mul a (0 : A j) = 0
  zero_mul : ∀ {i j} (b : A j), mul (0 : A i) b = 0
  mul_add : ∀ {i j} (a : A i) (b c : A j), mul a (b + c) = mul a b + mul a c
  add_mul : ∀ {i j} (a b : A i) (c : A j), mul (a + b) c = mul a c + mul b c
#align direct_sum.gnon_unital_non_assoc_semiring DirectSum.GnonUnitalNonAssocSemiring

end Defs

section Defs

variable (A : ι → Type _)

/-- A graded version of `semiring`. -/
class Gsemiring [AddMonoid ι] [∀ i, AddCommMonoid (A i)] extends GnonUnitalNonAssocSemiring A,
  GradedMonoid.GMonoid A where
  natCast : ℕ → A 0
  natCast_zero : nat_cast 0 = 0
  natCast_succ : ∀ n : ℕ, nat_cast (n + 1) = nat_cast n + GradedMonoid.GOne.one
#align direct_sum.gsemiring DirectSum.Gsemiring

/-- A graded version of `comm_semiring`. -/
class GcommSemiring [AddCommMonoid ι] [∀ i, AddCommMonoid (A i)] extends Gsemiring A,
  GradedMonoid.GCommMonoid A
#align direct_sum.gcomm_semiring DirectSum.GcommSemiring

/-- A graded version of `ring`. -/
class Gring [AddMonoid ι] [∀ i, AddCommGroup (A i)] extends Gsemiring A where
  intCast : ℤ → A 0
  intCast_ofNat : ∀ n : ℕ, int_cast n = nat_cast n
  intCast_negSucc : ∀ n : ℕ, int_cast (-(n + 1 : ℕ)) = -nat_cast (n + 1 : ℕ)
#align direct_sum.gring DirectSum.Gring

/-- A graded version of `comm_ring`. -/
class GcommRing [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] extends Gring A, GcommSemiring A
#align direct_sum.gcomm_ring DirectSum.GcommRing

end Defs

theorem of_eq_of_gradedMonoid_eq {A : ι → Type _} [∀ i : ι, AddCommMonoid (A i)] {i j : ι} {a : A i}
    {b : A j} (h : GradedMonoid.mk i a = GradedMonoid.mk j b) :
    DirectSum.of A i a = DirectSum.of A j b :=
  Dfinsupp.single_eq_of_sigma_eq h
#align direct_sum.of_eq_of_graded_monoid_eq DirectSum.of_eq_of_gradedMonoid_eq

variable (A : ι → Type _)

/-! ### Instances for `⨁ i, A i` -/


section One

variable [Zero ι] [GradedMonoid.GOne A] [∀ i, AddCommMonoid (A i)]

instance : One (⨁ i, A i) where one := DirectSum.of (fun i => A i) 0 GradedMonoid.GOne.one

end One

section Mul

variable [Add ι] [∀ i, AddCommMonoid (A i)] [GnonUnitalNonAssocSemiring A]

open AddMonoidHom (flip_apply coe_comp compHom_apply_apply)

/-- The piecewise multiplication from the `has_mul` instance, as a bundled homomorphism. -/
@[simps]
def gmulHom {i j} : A i →+ A j →+ A (i + j)
    where
  toFun a :=
    { toFun := fun b => GradedMonoid.GMul.mul a b
      map_zero' := GnonUnitalNonAssocSemiring.mul_zero _
      map_add' := GnonUnitalNonAssocSemiring.mul_add _ }
  map_zero' := AddMonoidHom.ext fun a => GnonUnitalNonAssocSemiring.zero_mul a
  map_add' a₁ a₂ := AddMonoidHom.ext fun b => GnonUnitalNonAssocSemiring.add_mul _ _ _
#align direct_sum.gmul_hom DirectSum.gmulHom

/-- The multiplication from the `has_mul` instance, as a bundled homomorphism. -/
def mulHom : (⨁ i, A i) →+ (⨁ i, A i) →+ ⨁ i, A i :=
  DirectSum.toAddMonoid fun i =>
    AddMonoidHom.flip <|
      DirectSum.toAddMonoid fun j =>
        AddMonoidHom.flip <| (DirectSum.of A _).compHom.comp <| gmulHom A
#align direct_sum.mul_hom DirectSum.mulHom

instance : NonUnitalNonAssocSemiring (⨁ i, A i) :=
  { DirectSum.addCommMonoid _ _ with
    mul := fun a b => mulHom A a b
    zero := 0
    add := (· + ·)
    zero_mul := fun a => by simp only [AddMonoidHom.map_zero, AddMonoidHom.zero_apply]
    mul_zero := fun a => by simp only [AddMonoidHom.map_zero]
    left_distrib := fun a b c => by simp only [AddMonoidHom.map_add]
    right_distrib := fun a b c => by simp only [AddMonoidHom.map_add, AddMonoidHom.add_apply] }

variable {A}

theorem mulHom_of_of {i j} (a : A i) (b : A j) :
    mulHom A (of _ i a) (of _ j b) = of _ (i + j) (GradedMonoid.GMul.mul a b) :=
  by
  unfold MulHom
  rw [to_add_monoid_of, flip_apply, to_add_monoid_of, flip_apply, coe_comp, Function.comp_apply,
    comp_hom_apply_apply, coe_comp, Function.comp_apply, gmul_hom_apply_apply]
#align direct_sum.mul_hom_of_of DirectSum.mulHom_of_of

theorem of_mul_of {i j} (a : A i) (b : A j) :
    of _ i a * of _ j b = of _ (i + j) (GradedMonoid.GMul.mul a b) :=
  mulHom_of_of a b
#align direct_sum.of_mul_of DirectSum.of_mul_of

end Mul

section Semiring

variable [∀ i, AddCommMonoid (A i)] [AddMonoid ι] [Gsemiring A]

open AddMonoidHom (flipHom coe_comp compHom_apply_apply flip_apply flipHom_apply)

private theorem one_mul (x : ⨁ i, A i) : 1 * x = x :=
  by
  suffices mulHom A 1 = AddMonoidHom.id (⨁ i, A i) from AddMonoidHom.congr_fun this x
  apply add_hom_ext; intro i xi
  unfold One.one
  rw [mul_hom_of_of]
  exact of_eq_of_graded_monoid_eq (one_mul <| GradedMonoid.mk i xi)
#align direct_sum.one_mul direct_sum.one_mul

private theorem mul_one (x : ⨁ i, A i) : x * 1 = x :=
  by
  suffices (mulHom A).flip 1 = AddMonoidHom.id (⨁ i, A i) from AddMonoidHom.congr_fun this x
  apply add_hom_ext; intro i xi
  unfold One.one
  rw [flip_apply, mul_hom_of_of]
  exact of_eq_of_graded_monoid_eq (mul_one <| GradedMonoid.mk i xi)
#align direct_sum.mul_one direct_sum.mul_one

private theorem mul_assoc (a b c : ⨁ i, A i) : a * b * c = a * (b * c) :=
  by
  suffices
    (-- `λ a b c, a * b * c` as a bundled hom
              mulHom
              A).compHom.comp
        (mulHom A) =
      (AddMonoidHom.compHom flipHom <|
          (-- `λ a b c, a * (b * c)` as a bundled hom
                    mulHom
                    A).flip.compHom.comp
            (mulHom A)).flip
    from AddMonoidHom.congr_fun (AddMonoidHom.congr_fun (AddMonoidHom.congr_fun this a) b) c
  ext (ai ax bi bx ci cx) : 6
  dsimp only [coe_comp, Function.comp_apply, comp_hom_apply_apply, flip_apply, flip_hom_apply]
  rw [mul_hom_of_of, mul_hom_of_of, mul_hom_of_of, mul_hom_of_of]
  exact of_eq_of_graded_monoid_eq (mul_assoc (GradedMonoid.mk ai ax) ⟨bi, bx⟩ ⟨ci, cx⟩)
#align direct_sum.mul_assoc direct_sum.mul_assoc

/-- The `semiring` structure derived from `gsemiring A`. -/
instance semiring : Semiring (⨁ i, A i) :=
  { DirectSum.nonUnitalNonAssocSemiring _ with
    one := 1
    mul := (· * ·)
    zero := 0
    add := (· + ·)
    one_mul := one_mul A
    mul_one := mul_one A
    mul_assoc := mul_assoc A
    natCast := fun n => of _ _ (Gsemiring.natCast n)
    natCast_zero := by rw [gsemiring.nat_cast_zero, map_zero]
    natCast_succ := fun n => by
      rw [gsemiring.nat_cast_succ, map_add]
      rfl }
#align direct_sum.semiring DirectSum.semiring

theorem of_pow {i} (a : A i) (n : ℕ) :
    of _ i a ^ n = of _ (n • i) (GradedMonoid.GMonoid.gnpow _ a) :=
  by
  induction' n with n
  · exact of_eq_of_graded_monoid_eq (pow_zero <| GradedMonoid.mk _ a).symm
  · rw [pow_succ, n_ih, of_mul_of]
    exact of_eq_of_graded_monoid_eq (pow_succ (GradedMonoid.mk _ a) n).symm
#align direct_sum.of_pow DirectSum.of_pow

theorem of_list_dProd {α} (l : List α) (fι : α → ι) (fA : ∀ a, A (fι a)) :
    of A _ (l.dProd fι fA) = (l.map fun a => of A (fι a) (fA a)).Prod :=
  by
  induction l
  · simp only [List.map_nil, List.prod_nil, List.dProd_nil]
    rfl
  · simp only [List.map_cons, List.prod_cons, List.dProd_cons, ← l_ih, DirectSum.of_mul_of]
    rfl
#align direct_sum.of_list_dprod DirectSum.of_list_dProd

theorem list_prod_ofFn_of_eq_dProd (n : ℕ) (fι : Fin n → ι) (fA : ∀ a, A (fι a)) :
    (List.ofFn fun a => of A (fι a) (fA a)).Prod = of A _ ((List.finRange n).dProd fι fA) := by
  rw [List.ofFn_eq_map, of_list_dprod]
#align direct_sum.list_prod_of_fn_of_eq_dprod DirectSum.list_prod_ofFn_of_eq_dProd

open BigOperators

theorem mul_eq_dfinsupp_sum [∀ (i : ι) (x : A i), Decidable (x ≠ 0)] (a a' : ⨁ i, A i) :
    a * a' = a.Sum fun i ai => a'.Sum fun j aj => DirectSum.of _ _ <| GradedMonoid.GMul.mul ai aj :=
  by
  change MulHom _ a a' = _
  simpa only [MulHom, to_add_monoid, Dfinsupp.liftAddHom_apply, Dfinsupp.sumAddHom_apply,
    AddMonoidHom.dfinsupp_sum_apply, flip_apply, AddMonoidHom.dfinsupp_sumAddHom_apply]
#align direct_sum.mul_eq_dfinsupp_sum DirectSum.mul_eq_dfinsupp_sum

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A heavily unfolded version of the definition of multiplication -/
theorem mul_eq_sum_support_ghas_mul [∀ (i : ι) (x : A i), Decidable (x ≠ 0)] (a a' : ⨁ i, A i) :
    a * a' =
      ∑ ij in Dfinsupp.support a ×ˢ Dfinsupp.support a',
        DirectSum.of _ _ (GradedMonoid.GMul.mul (a ij.fst) (a' ij.snd)) :=
  by simp only [mul_eq_dfinsupp_sum, Dfinsupp.sum, Finset.sum_product]
#align direct_sum.mul_eq_sum_support_ghas_mul DirectSum.mul_eq_sum_support_ghas_mul

end Semiring

section CommSemiring

variable [∀ i, AddCommMonoid (A i)] [AddCommMonoid ι] [GcommSemiring A]

private theorem mul_comm (a b : ⨁ i, A i) : a * b = b * a :=
  by
  suffices mulHom A = (mulHom A).flip from AddMonoidHom.congr_fun (AddMonoidHom.congr_fun this a) b
  apply add_hom_ext; intro ai ax; apply add_hom_ext; intro bi bx
  rw [AddMonoidHom.flip_apply, mul_hom_of_of, mul_hom_of_of]
  exact of_eq_of_graded_monoid_eq (gcomm_semiring.mul_comm ⟨ai, ax⟩ ⟨bi, bx⟩)
#align direct_sum.mul_comm direct_sum.mul_comm

/-- The `comm_semiring` structure derived from `gcomm_semiring A`. -/
instance commSemiring : CommSemiring (⨁ i, A i) :=
  { DirectSum.semiring _ with
    one := 1
    mul := (· * ·)
    zero := 0
    add := (· + ·)
    mul_comm := mul_comm A }
#align direct_sum.comm_semiring DirectSum.commSemiring

end CommSemiring

section NonUnitalNonAssocRing

variable [∀ i, AddCommGroup (A i)] [Add ι] [GnonUnitalNonAssocSemiring A]

/-- The `ring` derived from `gsemiring A`. -/
instance nonAssocRing : NonUnitalNonAssocRing (⨁ i, A i) :=
  { DirectSum.nonUnitalNonAssocSemiring _,
    DirectSum.addCommGroup _ with
    mul := (· * ·)
    zero := 0
    add := (· + ·)
    neg := Neg.neg }
#align direct_sum.non_assoc_ring DirectSum.nonAssocRing

end NonUnitalNonAssocRing

section Ring

variable [∀ i, AddCommGroup (A i)] [AddMonoid ι] [Gring A]

/-- The `ring` derived from `gsemiring A`. -/
instance ring : Ring (⨁ i, A i) :=
  { DirectSum.semiring _,
    DirectSum.addCommGroup _ with
    one := 1
    mul := (· * ·)
    zero := 0
    add := (· + ·)
    neg := Neg.neg
    intCast := fun z => of _ _ (Gring.intCast z)
    intCast_ofNat := fun z => congr_arg _ <| Gring.intCast_of_nat _
    intCast_negSucc := fun z =>
      (congr_arg _ <| Gring.intCast_neg_succ_of_nat _).trans (map_neg _ _) }
#align direct_sum.ring DirectSum.ring

end Ring

section CommRing

variable [∀ i, AddCommGroup (A i)] [AddCommMonoid ι] [GcommRing A]

/-- The `comm_ring` derived from `gcomm_semiring A`. -/
instance commRing : CommRing (⨁ i, A i) :=
  { DirectSum.ring _,
    DirectSum.commSemiring _ with
    one := 1
    mul := (· * ·)
    zero := 0
    add := (· + ·)
    neg := Neg.neg }
#align direct_sum.comm_ring DirectSum.commRing

end CommRing

/-! ### Instances for `A 0`

The various `g*` instances are enough to promote the `add_comm_monoid (A 0)` structure to various
types of multiplicative structure.
-/


section GradeZero

section One

variable [Zero ι] [GradedMonoid.GOne A] [∀ i, AddCommMonoid (A i)]

@[simp]
theorem of_zero_one : of _ 0 (1 : A 0) = 1 :=
  rfl
#align direct_sum.of_zero_one DirectSum.of_zero_one

end One

section Mul

variable [AddZeroClass ι] [∀ i, AddCommMonoid (A i)] [GnonUnitalNonAssocSemiring A]

@[simp]
theorem of_zero_smul {i} (a : A 0) (b : A i) : of _ _ (a • b) = of _ _ a * of _ _ b :=
  (of_eq_of_gradedMonoid_eq (GradedMonoid.mk_zero_smul a b)).trans (of_mul_of _ _).symm
#align direct_sum.of_zero_smul DirectSum.of_zero_smul

@[simp]
theorem of_zero_mul (a b : A 0) : of _ 0 (a * b) = of _ 0 a * of _ 0 b :=
  of_zero_smul A a b
#align direct_sum.of_zero_mul DirectSum.of_zero_mul

instance GradeZero.nonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (A 0) :=
  Function.Injective.nonUnitalNonAssocSemiring (of A 0) Dfinsupp.single_injective (of A 0).map_zero
    (of A 0).map_add (of_zero_mul A) fun x n => Dfinsupp.single_smul n x
#align direct_sum.grade_zero.non_unital_non_assoc_semiring DirectSum.GradeZero.nonUnitalNonAssocSemiring

instance GradeZero.smulWithZero (i : ι) : SMulWithZero (A 0) (A i) :=
  by
  letI := SMulWithZero.compHom (⨁ i, A i) (of A 0).toZeroHom
  refine' dfinsupp.single_injective.smul_with_zero (of A i).toZeroHom (of_zero_smul A)
#align direct_sum.grade_zero.smul_with_zero DirectSum.GradeZero.smulWithZero

end Mul

section Semiring

variable [∀ i, AddCommMonoid (A i)] [AddMonoid ι] [Gsemiring A]

@[simp]
theorem of_zero_pow (a : A 0) : ∀ n : ℕ, of _ 0 (a ^ n) = of _ 0 a ^ n
  | 0 => by rw [pow_zero, pow_zero, DirectSum.of_zero_one]
  | n + 1 => by rw [pow_succ, pow_succ, of_zero_mul, of_zero_pow]
#align direct_sum.of_zero_pow DirectSum.of_zero_pow

instance : NatCast (A 0) :=
  ⟨Gsemiring.natCast⟩

@[simp]
theorem of_nat_cast (n : ℕ) : of A 0 n = n :=
  rfl
#align direct_sum.of_nat_cast DirectSum.of_nat_cast

/-- The `semiring` structure derived from `gsemiring A`. -/
instance GradeZero.semiring : Semiring (A 0) :=
  Function.Injective.semiring (of A 0) Dfinsupp.single_injective (of A 0).map_zero (of_zero_one A)
    (of A 0).map_add (of_zero_mul A) (of A 0).map_nsmul (fun x n => of_zero_pow _ _ _)
    (of_nat_cast A)
#align direct_sum.grade_zero.semiring DirectSum.GradeZero.semiring

/-- `of A 0` is a `ring_hom`, using the `direct_sum.grade_zero.semiring` structure. -/
def ofZeroRingHom : A 0 →+* ⨁ i, A i :=
  { of _ 0 with
    map_one' := of_zero_one A
    map_mul' := of_zero_mul A }
#align direct_sum.of_zero_ring_hom DirectSum.ofZeroRingHom

/-- Each grade `A i` derives a `A 0`-module structure from `gsemiring A`. Note that this results
in an overall `module (A 0) (⨁ i, A i)` structure via `direct_sum.module`.
-/
instance GradeZero.module {i} : Module (A 0) (A i) :=
  letI := Module.compHom (⨁ i, A i) (of_zero_ring_hom A)
  dfinsupp.single_injective.module (A 0) (of A i) fun a => of_zero_smul A a
#align direct_sum.grade_zero.module DirectSum.GradeZero.module

end Semiring

section CommSemiring

variable [∀ i, AddCommMonoid (A i)] [AddCommMonoid ι] [GcommSemiring A]

/-- The `comm_semiring` structure derived from `gcomm_semiring A`. -/
instance GradeZero.commSemiring : CommSemiring (A 0) :=
  Function.Injective.commSemiring (of A 0) Dfinsupp.single_injective (of A 0).map_zero
    (of_zero_one A) (of A 0).map_add (of_zero_mul A) (fun x n => Dfinsupp.single_smul n x)
    (fun x n => of_zero_pow _ _ _) (of_nat_cast A)
#align direct_sum.grade_zero.comm_semiring DirectSum.GradeZero.commSemiring

end CommSemiring

section Ring

variable [∀ i, AddCommGroup (A i)] [AddZeroClass ι] [GnonUnitalNonAssocSemiring A]

/-- The `non_unital_non_assoc_ring` derived from `gnon_unital_non_assoc_semiring A`. -/
instance GradeZero.nonUnitalNonAssocRing : NonUnitalNonAssocRing (A 0) :=
  Function.Injective.nonUnitalNonAssocRing (of A 0) Dfinsupp.single_injective (of A 0).map_zero
    (of A 0).map_add (of_zero_mul A) (of A 0).map_neg (of A 0).map_sub
    (fun x n =>
      letI : ∀ i, DistribMulAction ℕ (A i) := fun i => inferInstance
      Dfinsupp.single_smul n x)
    fun x n =>
    letI : ∀ i, DistribMulAction ℤ (A i) := fun i => inferInstance
    Dfinsupp.single_smul n x
#align direct_sum.grade_zero.non_unital_non_assoc_ring DirectSum.GradeZero.nonUnitalNonAssocRing

end Ring

section Ring

variable [∀ i, AddCommGroup (A i)] [AddMonoid ι] [Gring A]

instance : IntCast (A 0) :=
  ⟨Gring.intCast⟩

@[simp]
theorem of_int_cast (n : ℤ) : of A 0 n = n :=
  rfl
#align direct_sum.of_int_cast DirectSum.of_int_cast

/-- The `ring` derived from `gsemiring A`. -/
instance GradeZero.ring : Ring (A 0) :=
  Function.Injective.ring (of A 0) Dfinsupp.single_injective (of A 0).map_zero (of_zero_one A)
    (of A 0).map_add (of_zero_mul A) (of A 0).map_neg (of A 0).map_sub
    (fun x n =>
      letI : ∀ i, DistribMulAction ℕ (A i) := fun i => inferInstance
      Dfinsupp.single_smul n x)
    (fun x n =>
      letI : ∀ i, DistribMulAction ℤ (A i) := fun i => inferInstance
      Dfinsupp.single_smul n x)
    (fun x n => of_zero_pow _ _ _) (of_nat_cast A) (of_int_cast A)
#align direct_sum.grade_zero.ring DirectSum.GradeZero.ring

end Ring

section CommRing

variable [∀ i, AddCommGroup (A i)] [AddCommMonoid ι] [GcommRing A]

/-- The `comm_ring` derived from `gcomm_semiring A`. -/
instance GradeZero.commRing : CommRing (A 0) :=
  Function.Injective.commRing (of A 0) Dfinsupp.single_injective (of A 0).map_zero (of_zero_one A)
    (of A 0).map_add (of_zero_mul A) (of A 0).map_neg (of A 0).map_sub
    (fun x n =>
      letI : ∀ i, DistribMulAction ℕ (A i) := fun i => inferInstance
      Dfinsupp.single_smul n x)
    (fun x n =>
      letI : ∀ i, DistribMulAction ℤ (A i) := fun i => inferInstance
      Dfinsupp.single_smul n x)
    (fun x n => of_zero_pow _ _ _) (of_nat_cast A) (of_int_cast A)
#align direct_sum.grade_zero.comm_ring DirectSum.GradeZero.commRing

end CommRing

end GradeZero

section ToSemiring

variable {R : Type _} [∀ i, AddCommMonoid (A i)] [AddMonoid ι] [Gsemiring A] [Semiring R]

variable {A}

/-- If two ring homomorphisms from `⨁ i, A i` are equal on each `of A i y`,
then they are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
theorem ringHom_ext' ⦃F G : (⨁ i, A i) →+* R⦄
    (h : ∀ i, (↑F : _ →+ R).comp (of A i) = (↑G : _ →+ R).comp (of A i)) : F = G :=
  RingHom.coe_addMonoidHom_injective <| DirectSum.addHom_ext' h
#align direct_sum.ring_hom_ext' DirectSum.ringHom_ext'

/-- Two `ring_hom`s out of a direct sum are equal if they agree on the generators. -/
theorem ringHom_ext ⦃f g : (⨁ i, A i) →+* R⦄ (h : ∀ i x, f (of A i x) = g (of A i x)) : f = g :=
  ringHom_ext' fun i => AddMonoidHom.ext <| h i
#align direct_sum.ring_hom_ext DirectSum.ringHom_ext

/-- A family of `add_monoid_hom`s preserving `direct_sum.ghas_one.one` and `direct_sum.ghas_mul.mul`
describes a `ring_hom`s on `⨁ i, A i`. This is a stronger version of `direct_sum.to_monoid`.

Of particular interest is the case when `A i` are bundled subojects, `f` is the family of
coercions such as `add_submonoid.subtype (A i)`, and the `[gsemiring A]` structure originates from
`direct_sum.gsemiring.of_add_submonoids`, in which case the proofs about `ghas_one` and `ghas_mul`
can be discharged by `rfl`. -/
@[simps]
def toSemiring (f : ∀ i, A i →+ R) (hone : f _ GradedMonoid.GOne.one = 1)
    (hmul : ∀ {i j} (ai : A i) (aj : A j), f _ (GradedMonoid.GMul.mul ai aj) = f _ ai * f _ aj) :
    (⨁ i, A i) →+* R :=
  { toAddMonoid f with
    toFun := toAddMonoid f
    map_one' := by
      change (to_add_monoid f) (of _ 0 _) = 1
      rw [to_add_monoid_of]
      exact hone
    map_mul' := by
      rw [(to_add_monoid f).map_mul_iff]
      ext (xi xv yi yv) : 4
      show
        to_add_monoid f (of A xi xv * of A yi yv) =
          to_add_monoid f (of A xi xv) * to_add_monoid f (of A yi yv)
      rw [of_mul_of, to_add_monoid_of, to_add_monoid_of, to_add_monoid_of]
      exact hmul _ _ }
#align direct_sum.to_semiring DirectSum.toSemiring

@[simp]
theorem toSemiring_of (f : ∀ i, A i →+ R) (hone hmul) (i : ι) (x : A i) :
    toSemiring f hone hmul (of _ i x) = f _ x :=
  toAddMonoid_of f i x
#align direct_sum.to_semiring_of DirectSum.toSemiring_of

@[simp]
theorem toSemiring_coe_addMonoidHom (f : ∀ i, A i →+ R) (hone hmul) :
    (toSemiring f hone hmul : (⨁ i, A i) →+ R) = toAddMonoid f :=
  rfl
#align direct_sum.to_semiring_coe_add_monoid_hom DirectSum.toSemiring_coe_addMonoidHom

/-- Families of `add_monoid_hom`s preserving `direct_sum.ghas_one.one` and `direct_sum.ghas_mul.mul`
are isomorphic to `ring_hom`s on `⨁ i, A i`. This is a stronger version of `dfinsupp.lift_add_hom`.
-/
@[simps]
def liftRingHom :
    { f : ∀ {i}, A i →+ R //
        f GradedMonoid.GOne.one = 1 ∧
          ∀ {i j} (ai : A i) (aj : A j), f (GradedMonoid.GMul.mul ai aj) = f ai * f aj } ≃
      ((⨁ i, A i) →+* R)
    where
  toFun f := toSemiring (fun _ => f.1) f.2.1 fun _ _ => f.2.2
  invFun F :=
    ⟨fun i => (F : (⨁ i, A i) →+ R).comp (of _ i),
      by
      simp only [AddMonoidHom.comp_apply, [anonymous]]
      rw [← F.map_one]
      rfl, fun i j ai aj =>
      by
      simp only [AddMonoidHom.comp_apply, [anonymous]]
      rw [← F.map_mul, of_mul_of]⟩
  left_inv f := by
    ext (xi xv)
    exact to_add_monoid_of (fun _ => f.1) xi xv
  right_inv F := by
    apply RingHom.coe_addMonoidHom_injective
    ext (xi xv)
    simp only [RingHom.coe_addMonoidHom_mk, DirectSum.toAddMonoid_of, AddMonoidHom.mk_coe,
      AddMonoidHom.comp_apply, to_semiring_coe_add_monoid_hom]
#align direct_sum.lift_ring_hom DirectSum.liftRingHom

end ToSemiring

end DirectSum

/-! ### Concrete instances -/


section Uniform

variable (ι)

/-- A direct sum of copies of a `semiring` inherits the multiplication structure. -/
instance NonUnitalNonAssocSemiring.directSumGnonUnitalNonAssocSemiring {R : Type _} [AddMonoid ι]
    [NonUnitalNonAssocSemiring R] : DirectSum.GnonUnitalNonAssocSemiring fun i : ι => R :=
  { Mul.gMul ι with
    mul_zero := fun i j => MulZeroClass.mul_zero
    zero_mul := fun i j => MulZeroClass.zero_mul
    mul_add := fun i j => mul_add
    add_mul := fun i j => add_mul }
#align non_unital_non_assoc_semiring.direct_sum_gnon_unital_non_assoc_semiring NonUnitalNonAssocSemiring.directSumGnonUnitalNonAssocSemiring

/-- A direct sum of copies of a `semiring` inherits the multiplication structure. -/
instance Semiring.directSumGsemiring {R : Type _} [AddMonoid ι] [Semiring R] :
    DirectSum.Gsemiring fun i : ι => R :=
  { NonUnitalNonAssocSemiring.directSumGnonUnitalNonAssocSemiring ι,
    Monoid.gMonoid ι with
    natCast := fun n => n
    natCast_zero := Nat.cast_zero
    natCast_succ := Nat.cast_succ }
#align semiring.direct_sum_gsemiring Semiring.directSumGsemiring

open DirectSum

-- To check `has_mul.ghas_mul_mul` matches
example {R : Type _} [AddMonoid ι] [Semiring R] (i j : ι) (a b : R) :
    (DirectSum.of _ i a * DirectSum.of _ j b : ⨁ i, R) = DirectSum.of _ (i + j) (a * b) := by
  rw [DirectSum.of_mul_of, Mul.gMul_mul]

/-- A direct sum of copies of a `comm_semiring` inherits the commutative multiplication structure.
-/
instance CommSemiring.directSumGcommSemiring {R : Type _} [AddCommMonoid ι] [CommSemiring R] :
    DirectSum.GcommSemiring fun i : ι => R :=
  { CommMonoid.gCommMonoid ι, Semiring.directSumGsemiring ι with }
#align comm_semiring.direct_sum_gcomm_semiring CommSemiring.directSumGcommSemiring

end Uniform

