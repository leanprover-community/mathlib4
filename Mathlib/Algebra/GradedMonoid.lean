/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module algebra.graded_monoid
! leanprover-community/mathlib commit 008205aa645b3f194c1da47025c5f110c8406eab
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Data.List.BigOperators.Basic
import Mathlib.Data.List.FinRange
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.Submonoid.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Sigma.Basic
import Lean.Elab.Tactic

/-!
# Additively-graded multiplicative structures

This module provides a set of heterogeneous typeclasses for defining a multiplicative structure
over the sigma type `GradedMonoid A` such that `(*) : A i → A j → A (i + j)`; that is to say, `A`
forms an additively-graded monoid. The typeclasses are:

* `GradedMonoid.ghas_one A`
* `GradedMonoid.ghas_mul A`
* `GradedMonoid.gmonoid A`
* `GradedMonoid.gcomm_monoid A`

With the `sigma_graded` locale open, these respectively imbue:

* `has_one (GradedMonoid A)`
* `has_mul (GradedMonoid A)`
* `monoid (GradedMonoid A)`
* `comm_monoid (GradedMonoid A)`

the base type `A 0` with:

* `GradedMonoid.grade_zero.has_one`
* `GradedMonoid.grade_zero.has_mul`
* `GradedMonoid.grade_zero.monoid`
* `GradedMonoid.grade_zero.comm_monoid`

and the `i`th grade `A i` with `A 0`-actions (`•`) defined as left-multiplication:

* (nothing)
* `GradedMonoid.grade_zero.has_smul (A 0)`
* `GradedMonoid.grade_zero.mul_action (A 0)`
* (nothing)

For now, these typeclasses are primarily used in the construction of `direct_sum.ring` and the rest
of that file.

## Dependent graded products

This also introduces `list.dprod`, which takes the (possibly non-commutative) product of a list
of graded elements of type `A i`. This definition primarily exist to allow `GradedMonoid.mk`
and `direct_sum.of` to be pulled outside a product, such as in `GradedMonoid.mk_list_dprod` and
`direct_sum.of_list_dprod`.

## Internally graded monoids

In addition to the above typeclasses, in the most frequent case when `A` is an indexed collection of
`set_like` subobjects (such as `add_submonoid`s, `add_subgroup`s, or `submodule`s), this file
provides the `Prop` typeclasses:

* `set_like.has_graded_one A` (which provides the obvious `GradedMonoid.ghas_one A` instance)
* `set_like.has_graded_mul A` (which provides the obvious `GradedMonoid.ghas_mul A` instance)
* `set_like.GradedMonoid A` (which provides the obvious `GradedMonoid.gmonoid A` and
  `GradedMonoid.gcomm_monoid A` instances)

which respectively provide the API lemmas

* `set_like.one_mem_graded`
* `set_like.mul_mem_graded`
* `set_like.pow_mem_graded`, `set_like.list_prod_map_mem_graded`

Strictly this last class is unecessary as it has no fields not present in its parents, but it is
included for convenience. Note that there is no need for `set_like.graded_ring` or similar, as all
the information it would contain is already supplied by `GradedMonoid` when `A` is a collection
of objects satisfying `add_submonoid_class` such as `submodule`s. These constructions are explored
in `algebra.direct_sum.internal`.

This file also defines:

* `set_like.is_homogeneous A` (which says that `a` is homogeneous iff `a ∈ A i` for some `i : ι`)
* `set_like.homogeneous_submonoid A`, which is, as the name suggests, the submonoid consisting of
  all the homogeneous elements.

## tags

graded monoid
-/


variable {ι : Type _}

/-- A type alias of sigma types for graded monoids. -/
def GradedMonoid (A : ι → Type _) :=
  Sigma A
#align GradedMonoid GradedMonoid

namespace GradedMonoid

instance {A : ι → Type _} [Inhabited ι] [Inhabited (A default)] : Inhabited (GradedMonoid A) where 
  default := Sigma.instInhabitedSigma.default

/-- Construct an element of a graded monoid. -/
def mk {A : ι → Type _} : ∀ i, A i → GradedMonoid A :=
  Sigma.mk
#align graded_monoid.mk GradedMonoid.mk

/-! ### Typeclasses -/


section Defs

variable (A : ι → Type _)

/-- A graded version of `has_one`, which must be of grade 0. -/
class GhasOne [Zero ι] where
  one : A 0
#align graded_monoid.ghas_one GradedMonoid.GhasOne

/-- `ghas_one` implies `has_one (graded_monoid A)` -/
instance GhasOne.toHasOne [Zero ι] [GhasOne A] : One (GradedMonoid A) :=
  ⟨⟨_, GhasOne.one⟩⟩
#align graded_monoid.ghas_one.to_has_one GradedMonoid.GhasOne.toHasOne

/-- A graded version of `has_mul`. Multiplication combines grades additively, like
`add_monoid_algebra`. -/
class GhasMul [Add ι] where
  mul {i j} : A i → A j → A (i + j)
#align graded_monoid.ghas_mul GradedMonoid.GhasMul

/-- `ghas_mul` implies `has_mul (GradedMonoid A)`. -/
instance GhasMul.toHasMul [Add ι] [GhasMul A] : Mul (GradedMonoid A) :=
  ⟨fun x y : GradedMonoid A => ⟨_, GhasMul.mul x.snd y.snd⟩⟩
#align graded_monoid.ghas_mul.to_has_mul GradedMonoid.GhasMul.toHasMul

theorem mk_mul_mk [Add ι] [GhasMul A] {i j} (a : A i) (b : A j) :
    mk i a * mk j b = mk (i + j) (GhasMul.mul a b) :=
  rfl
#align graded_monoid.mk_mul_mk GradedMonoid.mk_mul_mk

namespace Gmonoid

variable {A} [AddMonoid ι] [GhasMul A] [GhasOne A]

/-- A default implementation of power on a graded monoid, like `npow_rec`.
`gmonoid.gnpow` should be used instead. -/
def gnpowRec : ∀ (n : ℕ) {i}, A i → A (n • i)
  | 0, i, _ => cast (congr_arg A (zero_nsmul i).symm) GhasOne.one
  | n + 1, i, a => cast (congr_arg A (succ_nsmul i n).symm) (GhasMul.mul a <| gnpowRec _ a)
#align graded_monoid.gmonoid.gnpow_rec GradedMonoid.Gmonoid.gnpowRec

@[simp]
theorem gnpow_rec_zero (a : GradedMonoid A) : GradedMonoid.mk _ (gnpowRec 0 a.snd) = 1 :=
  Sigma.ext (zero_nsmul _) (heq_of_cast_eq _ rfl).symm
#align graded_monoid.gmonoid.gnpow_rec_zero GradedMonoid.Gmonoid.gnpow_rec_zero

@[simp]
theorem gnpow_rec_succ (n : ℕ) (a : GradedMonoid A) :
    (GradedMonoid.mk _ <| gnpowRec n.succ a.snd) = a * ⟨_, gnpowRec n a.snd⟩ :=
  Sigma.ext (succ_nsmul _ _) (heq_of_cast_eq _ rfl).symm
#align graded_monoid.gmonoid.gnpow_rec_succ GradedMonoid.Gmonoid.gnpow_rec_succ

end Gmonoid

/-- A graded version of `monoid`

Like `monoid.npow`, this has an optional `gmonoid.gnpow` field to allow definitional control of
natural powers of a graded monoid. -/
macro "apply_gmonoid_gnpow_rec_zero_tac" : tactic => `(tactic | apply Gmonoid.gnpow_rec_zero)
macro "apply_gmonoid_gnpow_rec_succ_tac" : tactic => `(tactic | apply Gmonoid.gnpow_rec_succ)

class Gmonoid [AddMonoid ι] extends GhasMul A, GhasOne A where
  one_mul (a : GradedMonoid A) : 1 * a = a
  mul_one (a : GradedMonoid A) : a * 1 = a
  mul_assoc (a b c : GradedMonoid A) : a * b * c = a * (b * c)
  gnpow : ∀ (n : ℕ) {i}, A i → A (n • i) := Gmonoid.gnpowRec
  gnpow_zero' : ∀ a : GradedMonoid A, GradedMonoid.mk _ (gnpow 0 a.snd) = 1 := by
    apply_gmonoid_gnpow_rec_zero_tac
  gnpow_succ' :
    ∀ (n : ℕ) (a : GradedMonoid A),
      (GradedMonoid.mk _ <| gnpow n.succ a.snd) = a * ⟨_, gnpow n a.snd⟩ := by 
    apply_gmonoid_gnpow_rec_succ_tac
#align graded_monoid.gmonoid GradedMonoid.Gmonoid

/-- `gmonoid` implies a `monoid (GradedMonoid A)`. -/
instance Gmonoid.toMonoid [AddMonoid ι] [Gmonoid A] : Monoid (GradedMonoid A)
    where
  one := 1
  mul := (· * ·)
  npow n a := GradedMonoid.mk _ (Gmonoid.gnpow n a.snd)
  npow_zero a := Gmonoid.gnpow_zero' a
  npow_succ n a := Gmonoid.gnpow_succ' n a
  one_mul := Gmonoid.one_mul
  mul_one := Gmonoid.mul_one
  mul_assoc := Gmonoid.mul_assoc
#align graded_monoid.gmonoid.to_monoid GradedMonoid.Gmonoid.toMonoid

theorem mk_pow [AddMonoid ι] [Gmonoid A] {i} (a : A i) (n : ℕ) :
    mk i a ^ n = mk (n • i) (Gmonoid.gnpow _ a) :=
  by
  match n with 
  | 0 => 
    rw [pow_zero]
    exact (Gmonoid.gnpow_zero' ⟨_, a⟩).symm
  | n+1 => 
    rw [pow_succ, mk_pow a n, mk_mul_mk]
    exact (Gmonoid.gnpow_succ' n ⟨_, a⟩).symm
#align graded_monoid.mk_pow GradedMonoid.mk_pow

/-- A graded version of `comm_monoid`. -/
class GcommMonoid [AddCommMonoid ι] extends Gmonoid A where
  mul_comm (a : GradedMonoid A) (b : GradedMonoid A) : a * b = b * a
#align graded_monoid.gcomm_monoid GradedMonoid.GcommMonoid

/-- `gcomm_monoid` implies a `comm_monoid (GradedMonoid A)`, although this is only used as an
instance locally to define notation in `gmonoid` and similar typeclasses. -/
instance GcommMonoid.toCommMonoid [AddCommMonoid ι] [GcommMonoid A] : CommMonoid (GradedMonoid A) :=
  { Gmonoid.toMonoid A with mul_comm := GcommMonoid.mul_comm }
#align graded_monoid.gcomm_monoid.to_comm_monoid GradedMonoid.GcommMonoid.toCommMonoid

end Defs

/-! ### Instances for `A 0`

The various `g*` instances are enough to promote the `add_comm_monoid (A 0)` structure to various
types of multiplicative structure.
-/


section GradeZero

variable (A : ι → Type _)

section One

variable [Zero ι] [GhasOne A]

/-- `1 : A 0` is the value provided in `ghas_one.one`. -/
@[nolint unusedArguments]
instance GradeZero.hasOne : One (A 0) :=
  ⟨GhasOne.one⟩
#align graded_monoid.grade_zero.has_one GradedMonoid.GradeZero.hasOne

end One

section Mul

variable [AddZeroClass ι] [GhasMul A]

/-- `(•) : A 0 → A i → A i` is the value provided in `GradedMonoid.ghas_mul.mul`, composed with
an `eq.rec` to turn `A (0 + i)` into `A i`.
-/
instance GradeZero.hasSmul (i : ι) : SMul (A 0) (A i)
    where smul x y := @Eq.rec ι (0+i) (fun a _ => A a) (GhasMul.mul x y) i (zero_add i)   
#align graded_monoid.grade_zero.has_smul GradedMonoid.GradeZero.hasSmul

/-- `(*) : A 0 → A 0 → A 0` is the value provided in `GradedMonoid.ghas_mul.mul`, composed with
an `eq.rec` to turn `A (0 + 0)` into `A 0`.
-/
instance GradeZero.hasMul : Mul (A 0) where mul := (· • ·)
#align graded_monoid.grade_zero.has_mul GradedMonoid.GradeZero.hasMul

variable {A}

@[simp]
theorem mk_zero_smul {i} (a : A 0) (b : A i) : mk _ (a • b) = mk _ a * mk _ b :=
  Sigma.ext (zero_add _).symm <| eq_rec_heq _ _ 
#align graded_monoid.mk_zero_smul GradedMonoid.mk_zero_smul

@[simp]
theorem GradeZero.smul_eq_mul (a b : A 0) : a • b = a * b :=
  rfl
#align graded_monoid.grade_zero.smul_eq_mul GradedMonoid.GradeZero.smul_eq_mul

end Mul

section Monoid

variable [AddMonoid ι] [Gmonoid A]

instance : Pow (A 0) ℕ where 
  pow x n := @Eq.rec ι (n • (0:ι)) (fun a _ => A a) (Gmonoid.gnpow n x) 0 (nsmul_zero n)

variable {A}

@[simp]
theorem mk_zero_pow (a : A 0) (n : ℕ) : mk _ (a ^ n) = mk _ a ^ n :=
  Sigma.ext (nsmul_zero n).symm <| eq_rec_heq _ _
#align graded_monoid.mk_zero_pow GradedMonoid.mk_zero_pow

variable (A)

/-- The `monoid` structure derived from `gmonoid A`. -/
instance GradeZero.monoid : Monoid (A 0) :=
  Function.Injective.monoid (mk 0) sigma_mk_injective rfl mk_zero_smul mk_zero_pow
#align graded_monoid.grade_zero.monoid GradedMonoid.GradeZero.monoid

end Monoid

section Monoid

variable [AddCommMonoid ι] [GcommMonoid A]

/-- The `comm_monoid` structure derived from `gcomm_monoid A`. -/
instance GradeZero.commMonoid : CommMonoid (A 0) :=
  Function.Injective.commMonoid (mk 0) sigma_mk_injective rfl mk_zero_smul mk_zero_pow
#align graded_monoid.grade_zero.comm_monoid GradedMonoid.GradeZero.commMonoid

end Monoid

section MulAction

variable [AddMonoid ι] [Gmonoid A]

/-- `GradedMonoid.mk 0` is a `monoid_hom`, using the `GradedMonoid.grade_zero.monoid` structure.
-/
def mkZeroMonoidHom : A 0 →* GradedMonoid A
    where
  toFun := mk 0
  map_one' := rfl
  map_mul' := mk_zero_smul
#align graded_monoid.mk_zero_monoid_hom GradedMonoid.mkZeroMonoidHom

/-- Each grade `A i` derives a `A 0`-action structure from `gmonoid A`. -/
instance GradeZero.mulAction {i} : MulAction (A 0) (A i) :=
  letI := MulAction.compHom (GradedMonoid A) (mkZeroMonoidHom A)
  Function.Injective.mulAction (mk i) sigma_mk_injective mk_zero_smul
#align graded_monoid.grade_zero.mul_action GradedMonoid.GradeZero.mulAction

end MulAction

end GradeZero

end GradedMonoid

/-! ### Dependent products of graded elements -/


section Dprod

variable {α : Type _} {A : ι → Type _} [AddMonoid ι] [GradedMonoid.Gmonoid A]

/-- The index used by `list.dprod`. Propositionally this is equal to `(l.map fι).sum`, but
definitionally it needs to have a different form to avoid introducing `eq.rec`s in `list.dprod`. -/
def List.dprodIndex (l : List α) (fι : α → ι) : ι :=
  l.foldr (fun i b => fι i + b) 0
#align list.dprod_index List.dprodIndex

@[simp]
theorem List.dprod_index_nil (fι : α → ι) : ([] : List α).dprodIndex fι = 0 :=
  rfl
#align list.dprod_index_nil List.dprod_index_nil

@[simp]
theorem List.dprod_index_cons (a : α) (l : List α) (fι : α → ι) :
    (a :: l).dprodIndex fι = fι a + l.dprodIndex fι :=
  rfl
#align list.dprod_index_cons List.dprod_index_cons

theorem List.dprod_index_eq_map_sum (l : List α) (fι : α → ι) : l.dprodIndex fι = (l.map fι).sum :=
  by
  match l with 
  | [] => simp 
  | head::tail => simp [List.dprod_index_eq_map_sum tail fι] 
#align list.dprod_index_eq_map_sum List.dprod_index_eq_map_sum

/-- A dependent product for graded monoids represented by the indexed family of types `A i`.
This is a dependent version of `(l.map fA).prod`.

For a list `l : list α`, this computes the product of `fA a` over `a`, where each `fA` is of type
`A (fι a)`. -/
def List.dprod (l : List α) (fι : α → ι) (fA : ∀ a, A (fι a)) : A (l.dprodIndex fι) :=
  l.foldrRecOn _ _ GradedMonoid.GhasOne.one fun _ x a _ => GradedMonoid.GhasMul.mul (fA a) x
#align list.dprod List.dprod

@[simp]
theorem List.dprod_nil (fι : α → ι) (fA : ∀ a, A (fι a)) :
    (List.nil : List α).dprod fι fA = GradedMonoid.GhasOne.one :=
  rfl
#align list.dprod_nil List.dprod_nil

-- the `( : _)` in this lemma statement results in the type on the RHS not being unfolded, which
-- is nicer in the goal view.
@[simp]
theorem List.dprod_cons (fι : α → ι) (fA : ∀ a, A (fι a)) (a : α) (l : List α) :
    (a :: l).dprod fι fA = (GradedMonoid.GhasMul.mul (fA a) (l.dprod fι fA) : _) :=
  rfl
#align list.dprod_cons List.dprod_cons

theorem GradedMonoid.mk_list_dprod (l : List α) (fι : α → ι) (fA : ∀ a, A (fι a)) :
    GradedMonoid.mk _ (l.dprod fι fA) = (l.map fun a => GradedMonoid.mk (fι a) (fA a)).prod :=
  by
  match l with 
  | [] => simp; rfl 
  | head::tail => 
    simp[← GradedMonoid.mk_list_dprod tail _ _, GradedMonoid.mk_mul_mk, List.prod_cons]
#align graded_monoid.mk_list_dprod GradedMonoid.mk_list_dprod

/-- A variant of `GradedMonoid.mk_list_dprod` for rewriting in the other direction. -/
theorem GradedMonoid.list_prod_map_eq_dprod (l : List α) (f : α → GradedMonoid A) :
    (l.map f).prod = GradedMonoid.mk _ (l.dprod (fun i => (f i).1) fun i => (f i).2) :=
  by
  rw [GradedMonoid.mk_list_dprod, GradedMonoid.mk]
  simp_rw [Sigma.eta]
#align graded_monoid.list_prod_map_eq_dprod GradedMonoid.list_prod_map_eq_dprod

theorem GradedMonoid.list_prod_of_fn_eq_dprod {n : ℕ} (f : Fin n → GradedMonoid A) :
    (List.ofFn f).prod =
      GradedMonoid.mk _ ((List.finRange n).dprod (fun i => (f i).1) fun i => (f i).2) :=
  by rw [List.ofFn_eq_map, GradedMonoid.list_prod_map_eq_dprod]
#align graded_monoid.list_prod_of_fn_eq_dprod GradedMonoid.list_prod_of_fn_eq_dprod

end Dprod

/-! ### Concrete instances -/


section

variable (ι) {R : Type _}

@[simps one]
instance One.ghasOne [Zero ι] [One R] : GradedMonoid.GhasOne fun _ : ι => R where one := 1
#align has_one.ghas_one One.ghasOne

@[simps mul]
instance Mul.ghasMul [Add ι] [Mul R] : GradedMonoid.GhasMul fun _ : ι => R where mul x y := x * y
#align has_mul.ghas_mul Mul.ghasMul

/-- If all grades are the same type and themselves form a monoid, then there is a trivial grading
structure. -/
@[simps gnpow]
instance Monoid.gmonoid [AddMonoid ι] [Monoid R] : GradedMonoid.Gmonoid fun _ : ι => R :=
  -- { Mul.ghasMul ι, One.ghasOne ι with
  { One.ghasOne ι with
    mul := fun x y => x * y 
    one_mul := fun _ => Sigma.ext (zero_add _) (heq_of_eq (one_mul _))
    mul_one := fun _ => Sigma.ext (add_zero _) (heq_of_eq (mul_one _))
    mul_assoc := fun _ _ _ => Sigma.ext (add_assoc _ _ _) (heq_of_eq (mul_assoc _ _ _))
    gnpow := fun n _ a => a ^ n
    gnpow_zero' := fun _ => Sigma.ext (zero_nsmul _) (heq_of_eq (Monoid.npow_zero _))
    gnpow_succ' := fun _ ⟨_, _⟩ => Sigma.ext (succ_nsmul _ _) (heq_of_eq (Monoid.npow_succ _ _)) }
#align monoid.gmonoid Monoid.gmonoid

/-- If all grades are the same type and themselves form a commutative monoid, then there is a
trivial grading structure. -/
instance CommMonoid.gcommMonoid [AddCommMonoid ι] [CommMonoid R] :
    GradedMonoid.GcommMonoid fun _ : ι => R :=
  { Monoid.gmonoid ι with
    mul_comm := fun _ _ => Sigma.ext (add_comm _ _) (heq_of_eq (mul_comm _ _)) }
#align comm_monoid.gcomm_monoid CommMonoid.gcommMonoid

/-- When all the indexed types are the same, the dependent product is just the regular product. -/
@[simp]
theorem List.dprod_monoid {α} [AddMonoid ι] [Monoid R] (l : List α) (fι : α → ι) (fA : α → R) :
    -- (l.dprod fι fA : (fun i : ι => R) _ ) = ((l.map fA).prod : R) :=
    @List.dprod _ _ (fun _:ι => R) _ _ l fι fA = (l.map fA).prod  :=
  by
  -- A (l.dprodIndex fι) 
  match l with 
  | [] => 
    rw [List.dprod_nil, List.map_nil, List.prod_nil]
    rfl
  | head::tail => 
    rw [List.dprod_cons, List.map_cons, List.prod_cons, List.dprod_monoid tail _ _]
    rfl
#align list.dprod_monoid List.dprod_monoid

end

/-! ### Shorthands for creating instance of the above typeclasses for collections of subobjects -/


section Subobjects

variable {R : Type _}

/-- A version of `GradedMonoid.ghas_one` for internally graded objects. -/
class SetLike.HasGradedOne {S : Type _} [SetLike S R] [One R] [Zero ι] (A : ι → S) : Prop where
  one_mem : (1 : R) ∈ A 0
#align set_like.has_graded_one SetLike.HasGradedOne

theorem SetLike.one_mem_graded {S : Type _} [SetLike S R] [One R] [Zero ι] (A : ι → S)
    [SetLike.HasGradedOne A] : (1 : R) ∈ A 0 :=
  SetLike.HasGradedOne.one_mem
#align set_like.one_mem_graded SetLike.one_mem_graded

instance SetLike.ghasOne {S : Type _} [SetLike S R] [One R] [Zero ι] (A : ι → S)
    [SetLike.HasGradedOne A] : GradedMonoid.GhasOne fun i => A i
    where one := ⟨1, SetLike.one_mem_graded _⟩
#align set_like.ghas_one SetLike.ghasOne

@[simp]
theorem SetLike.coe_ghas_one {S : Type _} [SetLike S R] [One R] [Zero ι] (A : ι → S)
    [SetLike.HasGradedOne A] : ↑(@GradedMonoid.GhasOne.one _ (fun i => A i) _ _) = (1 : R) :=
  rfl
#align set_like.coe_ghas_one SetLike.coe_ghas_one

/-- A version of `GradedMonoid.ghas_one` for internally graded objects. -/
class SetLike.HasGradedMul {S : Type _} [SetLike S R] [Mul R] [Add ι] (A : ι → S) : Prop where
  mul_mem : ∀ ⦃i j⦄ {gi gj}, gi ∈ A i → gj ∈ A j → gi * gj ∈ A (i + j)
#align set_like.has_graded_mul SetLike.HasGradedMul

theorem SetLike.mul_mem_graded {S : Type _} [SetLike S R] [Mul R] [Add ι] {A : ι → S}
    [SetLike.HasGradedMul A] ⦃i j⦄ {gi gj} (hi : gi ∈ A i) (hj : gj ∈ A j) : gi * gj ∈ A (i + j) :=
  SetLike.HasGradedMul.mul_mem hi hj
#align set_like.mul_mem_graded SetLike.mul_mem_graded

instance SetLike.ghasMul {S : Type _} [SetLike S R] [Mul R] [Add ι] (A : ι → S)
    [SetLike.HasGradedMul A] : GradedMonoid.GhasMul fun i => A i
    where mul := fun a b => ⟨(a * b : R), SetLike.mul_mem_graded a.prop b.prop⟩
#align set_like.ghas_mul SetLike.ghasMul

@[simp]
theorem SetLike.coe_ghas_mul {S : Type _} [SetLike S R] [Mul R] [Add ι] (A : ι → S)
    [SetLike.HasGradedMul A] {i j : ι} (x : A i) (y : A j) :
    ↑(@GradedMonoid.GhasMul.mul _ (fun i => A i) _ _ _ _ x y) = (x * y : R) :=
  rfl
#align set_like.coe_ghas_mul SetLike.coe_ghas_mul

/-- A version of `GradedMonoid.gmonoid` for internally graded objects. -/
class SetLike.GradedMonoid {S : Type _} [SetLike S R] [Monoid R] [AddMonoid ι] (A : ι → S) extends
  SetLike.HasGradedOne A, SetLike.HasGradedMul A : Prop
#align set_like.graded_monoid SetLike.GradedMonoid

namespace SetLike

variable {S : Type _} [SetLike S R] [Monoid R] [AddMonoid ι]

variable {A : ι → S} [SetLike.GradedMonoid A]

theorem pow_mem_graded (n : ℕ) {r : R} {i : ι} (h : r ∈ A i) : r ^ n ∈ A (n • i) :=
  by
  match n with 
  | 0 => 
    rw [pow_zero, zero_nsmul]
    exact one_mem_graded _
  | n+1 => 
    rw [pow_succ', succ_nsmul']
    exact mul_mem_graded (pow_mem_graded n h) h
#align set_like.pow_mem_graded SetLike.pow_mem_graded

theorem list_prod_map_mem_graded {ι'} (l : List ι') (i : ι' → ι) (r : ι' → R)
    (h : ∀ j ∈ l, r j ∈ A (i j)) : (l.map r).prod ∈ A (l.map i).sum :=
  by
  match l with 
  | [] => 
    rw [List.map_nil, List.map_nil, List.prod_nil, List.sum_nil]
    exact one_mem_graded _
  | head::tail => 
    rw [List.map_cons, List.map_cons, List.prod_cons, List.sum_cons]
    exact
      mul_mem_graded (h _ <| List.mem_cons_self _ _)
        (list_prod_map_mem_graded tail _ _ <| fun j hj => h _ <| List.mem_cons_of_mem _ hj)
#align set_like.list_prod_map_mem_graded SetLike.list_prod_map_mem_graded

theorem list_prod_of_fn_mem_graded {n} (i : Fin n → ι) (r : Fin n → R) (h : ∀ j, r j ∈ A (i j)) :
    (List.ofFn r).prod ∈ A (List.ofFn i).sum :=
  by
  rw [List.ofFn_eq_map, List.ofFn_eq_map]
  exact list_prod_map_mem_graded _ _ _ fun _ _ => h _
#align set_like.list_prod_of_fn_mem_graded SetLike.list_prod_of_fn_mem_graded

end SetLike

/-- Build a `gmonoid` instance for a collection of subobjects. -/
instance SetLike.gmonoid {S : Type _} [SetLike S R] [Monoid R] [AddMonoid ι] (A : ι → S)
    [SetLike.GradedMonoid A] : GradedMonoid.Gmonoid fun i => A i :=
  { SetLike.ghasOne A,
    SetLike.ghasMul
      A with
    one_mul := fun ⟨_, _, _⟩ => Sigma.subtype_ext (zero_add _) (one_mul _)
    mul_one := fun ⟨_, _, _⟩ => Sigma.subtype_ext (add_zero _) (mul_one _)
    mul_assoc := fun ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨_, _, _⟩ =>
      Sigma.subtype_ext (add_assoc _ _ _) (mul_assoc _ _ _)
    gnpow := fun n _ a => ⟨(a:R)^n, SetLike.pow_mem_graded n a.prop⟩
    gnpow_zero' := fun _ => Sigma.subtype_ext (zero_nsmul _) (pow_zero _)
    gnpow_succ' := fun _ _ => Sigma.subtype_ext (succ_nsmul _ _) (pow_succ _ _) }
#align set_like.gmonoid SetLike.gmonoid

@[simp]
theorem SetLike.coe_gnpow {S : Type _} [SetLike S R] [Monoid R] [AddMonoid ι] (A : ι → S)
    [SetLike.GradedMonoid A] {i : ι} (x : A i) (n : ℕ) :
    ↑(@GradedMonoid.Gmonoid.gnpow _ (fun i => A i) _ _ n _ x) = (x:R)^n :=
  rfl
#align set_like.coe_gnpow SetLike.coe_gnpow

/-- Build a `gcomm_monoid` instance for a collection of subobjects. -/
instance SetLike.gcommMonoid {S : Type _} [SetLike S R] [CommMonoid R] [AddCommMonoid ι] (A : ι → S)
    [SetLike.GradedMonoid A] : GradedMonoid.GcommMonoid fun i => A i :=
  { SetLike.gmonoid A with
    mul_comm := fun ⟨_, _, _⟩ ⟨_, _, _⟩ => Sigma.subtype_ext (add_comm _ _) (mul_comm _ _) }
#align set_like.gcomm_monoid SetLike.gcommMonoid

section Dprod

open SetLike SetLike.GradedMonoid

variable {α S : Type _} [SetLike S R] [Monoid R] [AddMonoid ι]

/-- Coercing a dependent product of subtypes is the same as taking the regular product of the
coercions. -/
@[simp]
theorem SetLike.coe_list_dprod (A : ι → S) [SetLike.GradedMonoid A] (fι : α → ι)
    (fA : ∀ a, A (fι a)) (l : List α) : ↑(@List.dprod _ _ (fun i => ↥(A i)) _ _ l fι fA) 
    = (List.prod (l.map fun a => fA a) : R) := by
  match l with 
  | [] => 
    rw [List.dprod_nil, coe_ghas_one, List.map_nil, List.prod_nil]
  | head::tail => 
    rw [List.dprod_cons, coe_ghas_mul, List.map_cons, List.prod_cons, 
      SetLike.coe_list_dprod _ _ _ tail]
#align set_like.coe_list_dprod SetLike.coe_list_dprod

/-- A version of `list.coe_dprod_set_like` with `subtype.mk`. -/
theorem SetLike.list_dprod_eq (A : ι → S) [SetLike.GradedMonoid A] (fι : α → ι) (fA : ∀ a, A (fι a))
    (l : List α) :
    (@List.dprod _ _ (fun i => ↥(A i)) _ _ l fι fA ) =
      ⟨List.prod (l.map fun a => fA a),
        (l.dprod_index_eq_map_sum fι).symm ▸
          list_prod_map_mem_graded l _ _ fun i _ => (fA i).prop⟩ :=
  Subtype.ext <| SetLike.coe_list_dprod _ _ _ _
#align set_like.list_dprod_eq SetLike.list_dprod_eq

end Dprod

end Subobjects

section HomogeneousElements

variable {R S : Type _} [SetLike S R]

/-- An element `a : R` is said to be homogeneous if there is some `i : ι` such that `a ∈ A i`. -/
def SetLike.IsHomogeneous (A : ι → S) (a : R) : Prop :=
  ∃ i, a ∈ A i
#align set_like.is_homogeneous SetLike.IsHomogeneous

@[simp]
theorem SetLike.is_homogeneous_coe {A : ι → S} {i} (x : A i) : SetLike.IsHomogeneous A (x : R) :=
  ⟨i, x.prop⟩
#align set_like.is_homogeneous_coe SetLike.is_homogeneous_coe

theorem SetLike.is_homogeneous_one [Zero ι] [One R] (A : ι → S) [SetLike.HasGradedOne A] :
    SetLike.IsHomogeneous A (1 : R) :=
  ⟨0, SetLike.one_mem_graded _⟩
#align set_like.is_homogeneous_one SetLike.is_homogeneous_one

theorem SetLike.IsHomogeneous.mul [Add ι] [Mul R] {A : ι → S} [SetLike.HasGradedMul A] {a b : R} :
    SetLike.IsHomogeneous A a → SetLike.IsHomogeneous A b → SetLike.IsHomogeneous A (a * b)
  | ⟨i, hi⟩, ⟨j, hj⟩ => ⟨i + j, SetLike.mul_mem_graded hi hj⟩
#align set_like.is_homogeneous.mul SetLike.IsHomogeneous.mul

/-- When `A` is a `SetLike.GradedMonoid A`, then the homogeneous elements forms a submonoid. -/
def SetLike.homogeneousSubmonoid [AddMonoid ι] [Monoid R] (A : ι → S) [SetLike.GradedMonoid A] :
    Submonoid R where
  carrier := { a | SetLike.IsHomogeneous A a }
  one_mem' := SetLike.is_homogeneous_one A
  mul_mem' a b := SetLike.IsHomogeneous.mul a b 
#align set_like.homogeneous_submonoid SetLike.homogeneousSubmonoid

end HomogeneousElements

