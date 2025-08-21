/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.GradedMonoid
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Ring.Associator

/-!
# Additively-graded multiplicative structures on `⨁ i, A i`

This module provides a set of heterogeneous typeclasses for defining a multiplicative structure
over `⨁ i, A i` such that `(*) : A i → A j → A (i + j)`; that is to say, `A` forms an
additively-graded ring. The typeclasses are:

* `DirectSum.GNonUnitalNonAssocSemiring A`
* `DirectSum.GSemiring A`
* `DirectSum.GRing A`
* `DirectSum.GCommSemiring A`
* `DirectSum.GCommRing A`

Respectively, these imbue the external direct sum `⨁ i, A i` with:

* `DirectSum.nonUnitalNonAssocSemiring`, `DirectSum.nonUnitalNonAssocRing`
* `DirectSum.semiring`
* `DirectSum.ring`
* `DirectSum.commSemiring`
* `DirectSum.commRing`

the base ring `A 0` with:

* `DirectSum.GradeZero.nonUnitalNonAssocSemiring`,
  `DirectSum.GradeZero.nonUnitalNonAssocRing`
* `DirectSum.GradeZero.semiring`
* `DirectSum.GradeZero.ring`
* `DirectSum.GradeZero.commSemiring`
* `DirectSum.GradeZero.commRing`

and the `i`th grade `A i` with `A 0`-actions (`•`) defined as left-multiplication:

* `DirectSum.GradeZero.smul (A 0)`, `DirectSum.GradeZero.smulWithZero (A 0)`
* `DirectSum.GradeZero.module (A 0)`
* (nothing)
* (nothing)
* (nothing)

Note that in the presence of these instances, `⨁ i, A i` itself inherits an `A 0`-action.

`DirectSum.ofZeroRingHom : A 0 →+* ⨁ i, A i` provides `DirectSum.of A 0` as a ring
homomorphism.

`DirectSum.toSemiring` extends `DirectSum.toAddMonoid` to produce a `RingHom`.

## Direct sums of subobjects

Additionally, this module provides helper functions to construct `GSemiring` and `GCommSemiring`
instances for:

* `A : ι → Submonoid S`:
  `DirectSum.GSemiring.ofAddSubmonoids`, `DirectSum.GCommSemiring.ofAddSubmonoids`.
* `A : ι → Subgroup S`:
  `DirectSum.GSemiring.ofAddSubgroups`, `DirectSum.GCommSemiring.ofAddSubgroups`.
* `A : ι → Submodule S`:
  `DirectSum.GSemiring.ofSubmodules`, `DirectSum.GCommSemiring.ofSubmodules`.

If `sSupIndep A`, these provide a gradation of `⨆ i, A i`, and the mapping `⨁ i, A i →+ ⨆ i, A i`
can be obtained as `DirectSum.toMonoid (fun i ↦ AddSubmonoid.inclusion <| le_iSup A i)`.

## Tags

graded ring, filtered ring, direct sum, add_submonoid
-/


variable {ι : Type*} [DecidableEq ι]

namespace DirectSum

open DirectSum

/-! ### Typeclasses -/


section Defs

variable (A : ι → Type*)

/-- A graded version of `NonUnitalNonAssocSemiring`. -/
class GNonUnitalNonAssocSemiring [Add ι] [∀ i, AddCommMonoid (A i)] extends
  GradedMonoid.GMul A where
  /-- Multiplication from the right with any graded component's zero vanishes. -/
  mul_zero : ∀ {i j} (a : A i), mul a (0 : A j) = 0
  /-- Multiplication from the left with any graded component's zero vanishes. -/
  zero_mul : ∀ {i j} (b : A j), mul (0 : A i) b = 0
  /-- Multiplication from the right between graded components distributes with respect to
  addition. -/
  mul_add : ∀ {i j} (a : A i) (b c : A j), mul a (b + c) = mul a b + mul a c
  /-- Multiplication from the left between graded components distributes with respect to
  addition. -/
  add_mul : ∀ {i j} (a b : A i) (c : A j), mul (a + b) c = mul a c + mul b c

end Defs

section Defs

variable (A : ι → Type*)

/-- A graded version of `Semiring`. -/
class GSemiring [AddMonoid ι] [∀ i, AddCommMonoid (A i)] extends GNonUnitalNonAssocSemiring A,
  GradedMonoid.GMonoid A where
  /-- The canonical map from ℕ to the zeroth component of a graded semiring. -/
  natCast : ℕ → A 0
  /-- The canonical map from ℕ to a graded semiring respects zero. -/
  natCast_zero : natCast 0 = 0
  /-- The canonical map from ℕ to a graded semiring respects successors. -/
  natCast_succ : ∀ n : ℕ, natCast (n + 1) = natCast n + GradedMonoid.GOne.one

/-- A graded version of `CommSemiring`. -/
class GCommSemiring [AddCommMonoid ι] [∀ i, AddCommMonoid (A i)] extends GSemiring A,
  GradedMonoid.GCommMonoid A

/-- A graded version of `Ring`. -/
class GRing [AddMonoid ι] [∀ i, AddCommGroup (A i)] extends GSemiring A where
  /-- The canonical map from ℤ to the zeroth component of a graded ring. -/
  intCast : ℤ → A 0
  /-- The canonical map from ℤ to a graded ring extends the canonical map from ℕ to the underlying
  graded semiring. -/
  intCast_ofNat : ∀ n : ℕ, intCast n = natCast n
  /-- On negative integers, the canonical map from ℤ to a graded ring is the negative extension of
  the canonical map from ℕ to the underlying graded semiring. -/
  -- Porting note: -(n + 1) -> Int.negSucc
  intCast_negSucc_ofNat : ∀ n : ℕ, intCast (Int.negSucc n) = -natCast (n + 1 : ℕ)

/-- A graded version of `CommRing`. -/
class GCommRing [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] extends GRing A, GCommSemiring A

end Defs

theorem of_eq_of_gradedMonoid_eq {A : ι → Type*} [∀ i : ι, AddCommMonoid (A i)] {i j : ι} {a : A i}
    {b : A j} (h : GradedMonoid.mk i a = GradedMonoid.mk j b) :
    DirectSum.of A i a = DirectSum.of A j b :=
  DFinsupp.single_eq_of_sigma_eq h

variable (A : ι → Type*)

/-! ### Instances for `⨁ i, A i` -/


section One

variable [Zero ι] [GradedMonoid.GOne A] [∀ i, AddCommMonoid (A i)]

instance : One (⨁ i, A i) where one := DirectSum.of A 0 GradedMonoid.GOne.one

theorem one_def : 1 = DirectSum.of A 0 GradedMonoid.GOne.one := rfl

end One

section Mul

variable [Add ι] [∀ i, AddCommMonoid (A i)] [GNonUnitalNonAssocSemiring A]

open AddMonoidHom (flip_apply coe_comp compHom)

/-- The piecewise multiplication from the `Mul` instance, as a bundled homomorphism. -/
@[simps]
def gMulHom {i j} : A i →+ A j →+ A (i + j) where
  toFun a :=
    { toFun := fun b => GradedMonoid.GMul.mul a b
      map_zero' := GNonUnitalNonAssocSemiring.mul_zero _
      map_add' := GNonUnitalNonAssocSemiring.mul_add _ }
  map_zero' := AddMonoidHom.ext fun a => GNonUnitalNonAssocSemiring.zero_mul a
  map_add' _ _ := AddMonoidHom.ext fun _ => GNonUnitalNonAssocSemiring.add_mul _ _ _

/-- The multiplication from the `Mul` instance, as a bundled homomorphism. -/
-- See note [non-reducible instance]
@[reducible]
def mulHom : (⨁ i, A i) →+ (⨁ i, A i) →+ ⨁ i, A i :=
  DirectSum.toAddMonoid fun _ =>
    AddMonoidHom.flip <|
      DirectSum.toAddMonoid fun _ =>
        AddMonoidHom.flip <| (DirectSum.of A _).compHom.comp <| gMulHom A

instance instMul : Mul (⨁ i, A i) where
  mul := fun a b => mulHom A a b

instance : NonUnitalNonAssocSemiring (⨁ i, A i) :=
  { (inferInstance : AddCommMonoid _) with
    zero_mul := fun _ => by simp only [Mul.mul, HMul.hMul, map_zero, AddMonoidHom.zero_apply]
    mul_zero := fun _ => by simp only [Mul.mul, HMul.hMul, AddMonoidHom.map_zero]
    left_distrib := fun _ _ _ => by simp only [Mul.mul, HMul.hMul, AddMonoidHom.map_add]
    right_distrib := fun _ _ _ => by
      simp only [Mul.mul, HMul.hMul, AddMonoidHom.map_add, AddMonoidHom.add_apply] }

variable {A}

theorem mulHom_apply (a b : ⨁ i, A i) : mulHom A a b = a * b := rfl

theorem mulHom_of_of {i j} (a : A i) (b : A j) :
    mulHom A (of A i a) (of A j b) = of A (i + j) (GradedMonoid.GMul.mul a b) := by
  simp

theorem of_mul_of {i j} (a : A i) (b : A j) :
    of A i a * of A j b = of _ (i + j) (GradedMonoid.GMul.mul a b) :=
  mulHom_of_of a b

end Mul

section Semiring

variable [∀ i, AddCommMonoid (A i)] [AddMonoid ι] [GSemiring A]

open AddMonoidHom (flipHom coe_comp compHom flip_apply)

private nonrec theorem one_mul (x : ⨁ i, A i) : 1 * x = x := by
  suffices mulHom A One.one = AddMonoidHom.id (⨁ i, A i) from DFunLike.congr_fun this x
  apply addHom_ext; intro i xi
  simp only [One.one]
  rw [mulHom_of_of]
  exact of_eq_of_gradedMonoid_eq (one_mul <| GradedMonoid.mk i xi)

private nonrec theorem mul_one (x : ⨁ i, A i) : x * 1 = x := by
  suffices (mulHom A).flip One.one = AddMonoidHom.id (⨁ i, A i) from DFunLike.congr_fun this x
  apply addHom_ext; intro i xi
  simp only [One.one]
  rw [flip_apply, mulHom_of_of]
  exact of_eq_of_gradedMonoid_eq (mul_one <| GradedMonoid.mk i xi)

private theorem mul_assoc (a b c : ⨁ i, A i) : a * b * c = a * (b * c) := by
  -- (`fun a b c => a * b * c` as a bundled hom) = (`fun a b c => a * (b * c)` as a bundled hom)
  suffices AddMonoidHom.mulLeft₃ = AddMonoidHom.mulRight₃ by
      simpa only [AddMonoidHom.mulLeft₃_apply, AddMonoidHom.mulRight₃_apply] using
        DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun this a) b) c
  ext ai ax bi bx ci cx : 6
  dsimp only [coe_comp, Function.comp_apply, AddMonoidHom.mulLeft₃_apply,
    AddMonoidHom.mulRight₃_apply]
  simp_rw [of_mul_of]
  exact of_eq_of_gradedMonoid_eq (_root_.mul_assoc (GradedMonoid.mk ai ax) ⟨bi, bx⟩ ⟨ci, cx⟩)

instance instNatCast : NatCast (⨁ i, A i) where
  natCast := fun n => of _ _ (GSemiring.natCast n)

/-- The `Semiring` structure derived from `GSemiring A`. -/
instance semiring : Semiring (⨁ i, A i) :=
  { (inferInstance : NonUnitalNonAssocSemiring _) with
    one_mul := one_mul A
    mul_one := mul_one A
    mul_assoc := mul_assoc A
    toNatCast := instNatCast _
    natCast_zero := by simp only [NatCast.natCast, GSemiring.natCast_zero, map_zero]
    natCast_succ := fun n => by
      simp_rw [NatCast.natCast, GSemiring.natCast_succ]
      rw [map_add]
      rfl }

theorem ofPow {i} (a : A i) (n : ℕ) :
    of _ i a ^ n = of _ (n • i) (GradedMonoid.GMonoid.gnpow _ a) := by
  induction n with
  | zero => exact of_eq_of_gradedMonoid_eq (pow_zero <| GradedMonoid.mk _ a).symm
  | succ n n_ih =>
    rw [pow_succ, n_ih, of_mul_of]
    exact of_eq_of_gradedMonoid_eq (pow_succ (GradedMonoid.mk _ a) n).symm

theorem ofList_dProd {α} (l : List α) (fι : α → ι) (fA : ∀ a, A (fι a)) :
    of A _ (l.dProd fι fA) = (l.map fun a => of A (fι a) (fA a)).prod := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, List.dProd_nil]; rfl
  | cons head tail =>
    rename_i ih
    simp only [List.map_cons, List.prod_cons, List.dProd_cons, ← ih]
    rw [DirectSum.of_mul_of (fA head)]
    rfl

theorem list_prod_ofFn_of_eq_dProd (n : ℕ) (fι : Fin n → ι) (fA : ∀ a, A (fι a)) :
    (List.ofFn fun a => of A (fι a) (fA a)).prod = of A _ ((List.finRange n).dProd fι fA) := by
  rw [List.ofFn_eq_map, ofList_dProd]

theorem mul_eq_dfinsuppSum [∀ (i : ι) (x : A i), Decidable (x ≠ 0)] (a a' : ⨁ i, A i) :
    a * a'
      = a.sum fun _ ai => a'.sum fun _ aj => DirectSum.of _ _ <| GradedMonoid.GMul.mul ai aj := by
  change mulHom _ a a' = _
  -- Porting note: I have no idea how the proof from ml3 worked it used to be
  -- simpa only [mul_hom, to_add_monoid, dfinsupp.lift_add_hom_apply, dfinsupp.sum_add_hom_apply,
  -- add_monoid_hom.dfinsupp_sum_apply, flip_apply, add_monoid_hom.dfinsupp_sum_add_hom_apply],
  rw [mulHom, toAddMonoid, DFinsupp.liftAddHom_apply]
  dsimp only [DirectSum]
  rw [DFinsupp.sumAddHom_apply, AddMonoidHom.dfinsuppSum_apply]
  apply congrArg _
  simp_rw [flip_apply]
  funext x
  -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
  erw [DFinsupp.sumAddHom_apply]
  simp only [gMulHom, AddMonoidHom.dfinsuppSum_apply, flip_apply, coe_comp, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, Function.comp_apply, AddMonoidHom.compHom_apply_apply]

@[deprecated (since := "2025-04-06")] alias mul_eq_dfinsupp_sum := mul_eq_dfinsuppSum

/-- A heavily unfolded version of the definition of multiplication -/
theorem mul_eq_sum_support_ghas_mul [∀ (i : ι) (x : A i), Decidable (x ≠ 0)] (a a' : ⨁ i, A i) :
    a * a' =
      ∑ ij ∈ DFinsupp.support a ×ˢ DFinsupp.support a',
        DirectSum.of _ _ (GradedMonoid.GMul.mul (a ij.fst) (a' ij.snd)) := by
  simp only [mul_eq_dfinsuppSum, DFinsupp.sum, Finset.sum_product]

end Semiring

section CommSemiring

variable [∀ i, AddCommMonoid (A i)] [AddCommMonoid ι] [GCommSemiring A]

private theorem mul_comm (a b : ⨁ i, A i) : a * b = b * a := by
  suffices mulHom A = (mulHom A).flip by
    rw [← mulHom_apply, this, AddMonoidHom.flip_apply, mulHom_apply]
  apply addHom_ext; intro ai ax; apply addHom_ext; intro bi bx
  rw [AddMonoidHom.flip_apply, mulHom_of_of, mulHom_of_of]
  exact of_eq_of_gradedMonoid_eq (GCommSemiring.mul_comm ⟨ai, ax⟩ ⟨bi, bx⟩)

/-- The `CommSemiring` structure derived from `GCommSemiring A`. -/
instance commSemiring : CommSemiring (⨁ i, A i) :=
  { DirectSum.semiring A with
    mul_comm := mul_comm A }

end CommSemiring

section NonUnitalNonAssocRing

variable [∀ i, AddCommGroup (A i)] [Add ι] [GNonUnitalNonAssocSemiring A]

/-- The `Ring` derived from `GSemiring A`. -/
instance nonAssocRing : NonUnitalNonAssocRing (⨁ i, A i) :=
  { (inferInstance : NonUnitalNonAssocSemiring (⨁ i, A i)),
    (inferInstance : AddCommGroup (⨁ i, A i)) with }

end NonUnitalNonAssocRing

section Ring

variable [∀ i, AddCommGroup (A i)] [AddMonoid ι] [GRing A]

-- Porting note: overspecified fields in ml4
/-- The `Ring` derived from `GSemiring A`. -/
instance ring : Ring (⨁ i, A i) :=
  { DirectSum.semiring A,
    (inferInstance : AddCommGroup (⨁ i, A i)) with
    toIntCast.intCast := fun z => of A 0 <| (GRing.intCast z)
    intCast_ofNat := fun _ => congrArg (of A 0) <| GRing.intCast_ofNat _
    intCast_negSucc := fun _ =>
      (congrArg (of A 0) <| GRing.intCast_negSucc_ofNat _).trans <| map_neg _ _}

end Ring

section CommRing

variable [∀ i, AddCommGroup (A i)] [AddCommMonoid ι] [GCommRing A]

/-- The `CommRing` derived from `GCommSemiring A`. -/
instance commRing : CommRing (⨁ i, A i) :=
  { DirectSum.ring A,
    DirectSum.commSemiring A with }

end CommRing

/-! ### Instances for `A 0`

The various `G*` instances are enough to promote the `AddCommMonoid (A 0)` structure to various
types of multiplicative structure.
-/


section GradeZero

section One

variable [Zero ι] [GradedMonoid.GOne A] [∀ i, AddCommMonoid (A i)]

@[simp]
theorem of_zero_one : of _ 0 (1 : A 0) = 1 :=
  rfl

end One

section Mul

variable [AddZeroClass ι] [∀ i, AddCommMonoid (A i)] [GNonUnitalNonAssocSemiring A]

@[simp]
theorem of_zero_smul {i} (a : A 0) (b : A i) : of _ _ (a • b) = of _ _ a * of _ _ b :=
  (of_eq_of_gradedMonoid_eq (GradedMonoid.mk_zero_smul a b)).trans (of_mul_of _ _).symm

@[simp]
theorem of_zero_mul (a b : A 0) : of _ 0 (a * b) = of _ 0 a * of _ 0 b :=
  of_zero_smul A a b

instance GradeZero.nonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (A 0) :=
  Function.Injective.nonUnitalNonAssocSemiring (of A 0) DFinsupp.single_injective (of A 0).map_zero
    (of A 0).map_add (of_zero_mul A) (map_nsmul _)

instance GradeZero.smulWithZero (i : ι) : SMulWithZero (A 0) (A i) := by
  letI := SMulWithZero.compHom (⨁ i, A i) (of A 0).toZeroHom
  exact Function.Injective.smulWithZero (of A i).toZeroHom DFinsupp.single_injective
    (of_zero_smul A)

end Mul

section Semiring

variable [∀ i, AddCommMonoid (A i)] [AddMonoid ι] [GSemiring A]

@[simp]
theorem of_zero_pow (a : A 0) : ∀ n : ℕ, of A 0 (a ^ n) = of A 0 a ^ n
  | 0 => by rw [pow_zero, pow_zero, DirectSum.of_zero_one]
  -- Porting note: Lean doesn't think this terminates if we only use `of_zero_pow` alone
  | n + 1 => by rw [pow_succ, pow_succ, of_zero_mul, of_zero_pow _ n]

instance : NatCast (A 0) :=
  ⟨GSemiring.natCast⟩


-- TODO: These could be replaced by the general lemmas for `AddMonoidHomClass` (`map_natCast'` and
-- `map_ofNat'`) if those were marked `@[simp low]`.
@[simp]
theorem of_natCast (n : ℕ) : of A 0 n = n :=
  rfl

@[simp]
theorem of_zero_ofNat (n : ℕ) [n.AtLeastTwo] : of A 0 ofNat(n) = ofNat(n) :=
  of_natCast A n

/-- The `Semiring` structure derived from `GSemiring A`. -/
instance GradeZero.semiring : Semiring (A 0) :=
  Function.Injective.semiring (of A 0) DFinsupp.single_injective (of A 0).map_zero (of_zero_one A)
    (of A 0).map_add (of_zero_mul A) (fun _ _ ↦ (of A 0).map_nsmul _ _)
    (fun _ _ => of_zero_pow _ _ _) (of_natCast A)

/-- `of A 0` is a `RingHom`, using the `DirectSum.GradeZero.semiring` structure. -/
def ofZeroRingHom : A 0 →+* ⨁ i, A i :=
  { of _ 0 with
    map_one' := of_zero_one A
    map_mul' := of_zero_mul A }

/-- Each grade `A i` derives an `A 0`-module structure from `GSemiring A`. Note that this results
in an overall `Module (A 0) (⨁ i, A i)` structure via `DirectSum.module`.
-/
instance GradeZero.module {i} : Module (A 0) (A i) :=
  letI := Module.compHom (⨁ i, A i) (ofZeroRingHom A)
  DFinsupp.single_injective.module (A 0) (of A i) fun a => of_zero_smul A a

end Semiring

section CommSemiring

variable [∀ i, AddCommMonoid (A i)] [AddCommMonoid ι] [GCommSemiring A]

/-- The `CommSemiring` structure derived from `GCommSemiring A`. -/
instance GradeZero.commSemiring : CommSemiring (A 0) :=
  Function.Injective.commSemiring (of A 0) DFinsupp.single_injective (of A 0).map_zero
    (of_zero_one A) (of A 0).map_add (of_zero_mul A) (fun _ _ ↦ map_nsmul _ _ _)
    (fun _ _ => of_zero_pow _ _ _) (of_natCast A)

end CommSemiring

section Ring

variable [∀ i, AddCommGroup (A i)] [AddZeroClass ι] [GNonUnitalNonAssocSemiring A]

/-- The `NonUnitalNonAssocRing` derived from `GNonUnitalNonAssocSemiring A`. -/
instance GradeZero.nonUnitalNonAssocRing : NonUnitalNonAssocRing (A 0) :=
  Function.Injective.nonUnitalNonAssocRing (of A 0) DFinsupp.single_injective (of A 0).map_zero
    (of A 0).map_add (of_zero_mul A) (of A 0).map_neg (of A 0).map_sub (fun _ _ ↦ map_nsmul _ _ _)
    (fun _ _ ↦ map_zsmul _ _ _)

end Ring

section Ring

variable [∀ i, AddCommGroup (A i)] [AddMonoid ι] [GRing A]

instance : IntCast (A 0) :=
  ⟨GRing.intCast⟩

@[simp]
theorem of_intCast (n : ℤ) : of A 0 n = n := by
  rfl

/-- The `Ring` derived from `GSemiring A`. -/
instance GradeZero.ring : Ring (A 0) :=
  Function.Injective.ring (of A 0) DFinsupp.single_injective (of A 0).map_zero (of_zero_one A)
    (of A 0).map_add (of_zero_mul A) (of A 0).map_neg (of A 0).map_sub (fun _ _ ↦ map_nsmul _ _ _)
    (fun _ _ ↦ map_zsmul _ _ _) (fun _ _ => of_zero_pow _ _ _) (of_natCast A) (of_intCast A)

end Ring

section CommRing

variable [∀ i, AddCommGroup (A i)] [AddCommMonoid ι] [GCommRing A]

/-- The `CommRing` derived from `GCommSemiring A`. -/
instance GradeZero.commRing : CommRing (A 0) :=
  Function.Injective.commRing (of A 0) DFinsupp.single_injective (of A 0).map_zero (of_zero_one A)
    (of A 0).map_add (of_zero_mul A) (of A 0).map_neg (of A 0).map_sub (fun _ _ ↦ map_nsmul _ _ _)
    (fun _ _ ↦ map_zsmul _ _ _) (fun _ _ => of_zero_pow _ _ _) (of_natCast A) (of_intCast A)

end CommRing

end GradeZero

section ToSemiring

variable {R : Type*} [∀ i, AddCommMonoid (A i)] [AddMonoid ι] [GSemiring A] [Semiring R]
variable {A}

/-- If two ring homomorphisms from `⨁ i, A i` are equal on each `of A i y`,
then they are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
theorem ringHom_ext' ⦃F G : (⨁ i, A i) →+* R⦄
    (h : ∀ i, (↑F : _ →+ R).comp (of A i) = (↑G : _ →+ R).comp (of A i)) : F = G :=
  RingHom.coe_addMonoidHom_injective <| DirectSum.addHom_ext' h

/-- Two `RingHom`s out of a direct sum are equal if they agree on the generators. -/
theorem ringHom_ext ⦃f g : (⨁ i, A i) →+* R⦄ (h : ∀ i x, f (of A i x) = g (of A i x)) : f = g :=
  ringHom_ext' fun i => AddMonoidHom.ext <| h i

/-- A family of `AddMonoidHom`s preserving `DirectSum.One.one` and `DirectSum.Mul.mul`
describes a `RingHom`s on `⨁ i, A i`. This is a stronger version of `DirectSum.toMonoid`.

Of particular interest is the case when `A i` are bundled subobjects, `f` is the family of
coercions such as `AddSubmonoid.subtype (A i)`, and the `[GSemiring A]` structure originates from
`DirectSum.gsemiring.ofAddSubmonoids`, in which case the proofs about `GOne` and `GMul`
can be discharged by `rfl`. -/
@[simps]
def toSemiring (f : ∀ i, A i →+ R) (hone : f _ GradedMonoid.GOne.one = 1)
    (hmul : ∀ {i j} (ai : A i) (aj : A j), f _ (GradedMonoid.GMul.mul ai aj) = f _ ai * f _ aj) :
    (⨁ i, A i) →+* R :=
  { toAddMonoid f with
    toFun := toAddMonoid f
    map_one' := by
      change (toAddMonoid f) (of _ 0 _) = 1
      rw [toAddMonoid_of]
      exact hone
    map_mul' := by
      rw [(toAddMonoid f).map_mul_iff]
      refine DirectSum.addHom_ext' (fun xi ↦ AddMonoidHom.ext (fun xv ↦ ?_))
      refine DirectSum.addHom_ext' (fun yi ↦ AddMonoidHom.ext (fun yv ↦ ?_))
      change
        toAddMonoid f (of A xi xv * of A yi yv) =
          toAddMonoid f (of A xi xv) * toAddMonoid f (of A yi yv)
      simp_rw [of_mul_of, toAddMonoid_of]
      exact hmul _ _ }

theorem toSemiring_of (f : ∀ i, A i →+ R) (hone hmul) (i : ι) (x : A i) :
    toSemiring f hone hmul (of _ i x) = f _ x :=
  toAddMonoid_of f i x

@[simp]
theorem toSemiring_coe_addMonoidHom (f : ∀ i, A i →+ R) (hone hmul) :
    (toSemiring f hone hmul : (⨁ i, A i) →+ R) = toAddMonoid f :=
  rfl

/-- Families of `AddMonoidHom`s preserving `DirectSum.One.one` and `DirectSum.Mul.mul`
are isomorphic to `RingHom`s on `⨁ i, A i`. This is a stronger version of `DFinsupp.liftAddHom`.
-/
@[simps]
def liftRingHom :
    { f : ∀ {i}, A i →+ R //
        f GradedMonoid.GOne.one = 1 ∧
          ∀ {i j} (ai : A i) (aj : A j), f (GradedMonoid.GMul.mul ai aj) = f ai * f aj } ≃
      ((⨁ i, A i) →+* R) where
  toFun f := toSemiring (fun _ => f.1) f.2.1 f.2.2
  invFun F :=
    ⟨by intro i; exact (F : (⨁ i, A i) →+ R).comp (of _ i),
      by
      simp only [AddMonoidHom.comp_apply]
      rw [← F.map_one]
      rfl,
      by
      intros i j ai aj
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_coe]
      rw [← F.map_mul (of A i ai), of_mul_of ai]⟩
  left_inv f := by
    ext xi xv
    exact toAddMonoid_of (fun _ => f.1) xi xv
  right_inv F := by
    apply RingHom.coe_addMonoidHom_injective
    refine DirectSum.addHom_ext' (fun xi ↦ AddMonoidHom.ext (fun xv ↦ ?_))
    simp only [DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply, toSemiring_coe_addMonoidHom]

end ToSemiring

end DirectSum

/-! ### Concrete instances -/


section Uniform

variable (ι)

/-- A direct sum of copies of a `NonUnitalNonAssocSemiring` inherits the multiplication structure.
-/
instance NonUnitalNonAssocSemiring.directSumGNonUnitalNonAssocSemiring {R : Type*} [AddMonoid ι]
    [NonUnitalNonAssocSemiring R] : DirectSum.GNonUnitalNonAssocSemiring fun _ : ι => R :=
  { -- Porting note: removed Mul.gMul ι with and we seem ok
    mul_zero := mul_zero
    zero_mul := zero_mul
    mul_add := mul_add
    add_mul := add_mul }

/-- A direct sum of copies of a `Semiring` inherits the multiplication structure. -/
instance Semiring.directSumGSemiring {R : Type*} [AddMonoid ι] [Semiring R] :
    DirectSum.GSemiring fun _ : ι => R where
  __ := NonUnitalNonAssocSemiring.directSumGNonUnitalNonAssocSemiring ι
  __ := Monoid.gMonoid ι
  natCast n := n
  natCast_zero := Nat.cast_zero
  natCast_succ := Nat.cast_succ

/-- A direct sum of copies of a `Ring` inherits the multiplication structure. -/
instance Ring.directSumGRing {R : Type*} [AddMonoid ι] [Ring R] :
    DirectSum.GRing fun _ : ι => R where
  __ := Semiring.directSumGSemiring ι
  intCast z := z
  intCast_ofNat := Int.cast_natCast
  intCast_negSucc_ofNat := Int.cast_negSucc

open DirectSum

-- To check `Mul.gmul_mul` matches
example {R : Type*} [AddMonoid ι] [Semiring R] (i j : ι) (a b : R) :
    (DirectSum.of _ i a * DirectSum.of _ j b : ⨁ _, R) = DirectSum.of _ (i + j) (a * b) := by
  rw [DirectSum.of_mul_of, Mul.gMul_mul]

/-- A direct sum of copies of a `CommSemiring` inherits the commutative multiplication structure. -/
instance CommSemiring.directSumGCommSemiring {R : Type*} [AddCommMonoid ι] [CommSemiring R] :
    DirectSum.GCommSemiring fun _ : ι => R where
  __ := Semiring.directSumGSemiring ι
  __ := CommMonoid.gCommMonoid ι

/-- A direct sum of copies of a `CommRing` inherits the commutative multiplication structure. -/
instance CommRing.directSumGCommRing {R : Type*} [AddCommMonoid ι] [CommRing R] :
    DirectSum.GCommRing fun _ : ι => R where
  __ := Ring.directSumGRing ι
  __ := CommMonoid.gCommMonoid ι

end Uniform
