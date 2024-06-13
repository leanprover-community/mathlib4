/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.BigOperators.Group.List
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.SetLike.Basic
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Data.Sigma.Basic
import Lean.Elab.Tactic

#align_import algebra.graded_monoid from "leanprover-community/mathlib"@"008205aa645b3f194c1da47025c5f110c8406eab"

/-!
# Additively-graded multiplicative structures

This module provides a set of heterogeneous typeclasses for defining a multiplicative structure
over the sigma type `GradedMonoid A` such that `(*) : A i → A j → A (i + j)`; that is to say, `A`
forms an additively-graded monoid. The typeclasses are:

* `GradedMonoid.GOne A`
* `GradedMonoid.GMul A`
* `GradedMonoid.GMonoid A`
* `GradedMonoid.GCommMonoid A`

These respectively imbue:

* `One (GradedMonoid A)`
* `Mul (GradedMonoid A)`
* `Monoid (GradedMonoid A)`
* `CommMonoid (GradedMonoid A)`

the base type `A 0` with:

* `GradedMonoid.GradeZero.One`
* `GradedMonoid.GradeZero.Mul`
* `GradedMonoid.GradeZero.Monoid`
* `GradedMonoid.GradeZero.CommMonoid`

and the `i`th grade `A i` with `A 0`-actions (`•`) defined as left-multiplication:

* (nothing)
* `GradedMonoid.GradeZero.SMul (A 0)`
* `GradedMonoid.GradeZero.MulAction (A 0)`
* (nothing)

For now, these typeclasses are primarily used in the construction of `DirectSum.Ring` and the rest
of that file.

## Dependent graded products

This also introduces `List.dProd`, which takes the (possibly non-commutative) product of a list
of graded elements of type `A i`. This definition primarily exist to allow `GradedMonoid.mk`
and `DirectSum.of` to be pulled outside a product, such as in `GradedMonoid.mk_list_dProd` and
`DirectSum.of_list_dProd`.

## Internally graded monoids

In addition to the above typeclasses, in the most frequent case when `A` is an indexed collection of
`SetLike` subobjects (such as `AddSubmonoid`s, `AddSubgroup`s, or `Submodule`s), this file
provides the `Prop` typeclasses:

* `SetLike.GradedOne A` (which provides the obvious `GradedMonoid.GOne A` instance)
* `SetLike.GradedMul A` (which provides the obvious `GradedMonoid.GMul A` instance)
* `SetLike.GradedMonoid A` (which provides the obvious `GradedMonoid.GMonoid A` and
  `GradedMonoid.GCommMonoid A` instances)

which respectively provide the API lemmas

* `SetLike.one_mem_graded`
* `SetLike.mul_mem_graded`
* `SetLike.pow_mem_graded`, `SetLike.list_prod_map_mem_graded`

Strictly this last class is unnecessary as it has no fields not present in its parents, but it is
included for convenience. Note that there is no need for `SetLike.GradedRing` or similar, as all
the information it would contain is already supplied by `GradedMonoid` when `A` is a collection
of objects satisfying `AddSubmonoidClass` such as `Submodule`s. These constructions are explored
in `Algebra.DirectSum.Internal`.

This file also defines:

* `SetLike.isHomogeneous A` (which says that `a` is homogeneous iff `a ∈ A i` for some `i : ι`)
* `SetLike.homogeneousSubmonoid A`, which is, as the name suggests, the submonoid consisting of
  all the homogeneous elements.

## Tags

graded monoid
-/


variable {ι : Type*}

/-- A type alias of sigma types for graded monoids. -/
def GradedMonoid (A : ι → Type*) :=
  Sigma A
#align graded_monoid GradedMonoid

namespace GradedMonoid

instance {A : ι → Type*} [Inhabited ι] [Inhabited (A default)] : Inhabited (GradedMonoid A) :=
  inferInstanceAs <| Inhabited (Sigma _)

/-- Construct an element of a graded monoid. -/
def mk {A : ι → Type*} : ∀ i, A i → GradedMonoid A :=
  Sigma.mk
#align graded_monoid.mk GradedMonoid.mk

/-! ### Actions -/

section actions
variable {α β} {A : ι → Type*}

/-- If `R` acts on each `A i`, then it acts on `GradedMonoid A` via the `.2` projection. -/
instance [∀ i, SMul α (A i)] : SMul α (GradedMonoid A) where
  smul r g := GradedMonoid.mk g.1 (r • g.2)

@[simp] theorem fst_smul [∀ i, SMul α (A i)] (a : α) (x : GradedMonoid A) :
    (a • x).fst = x.fst := rfl

@[simp] theorem snd_smul [∀ i, SMul α (A i)] (a : α) (x : GradedMonoid A) :
    (a • x).snd = a • x.snd := rfl

theorem smul_mk [∀ i, SMul α (A i)] {i} (c : α) (a : A i) :
    c • mk i a = mk i (c • a) :=
  rfl

instance [∀ i, SMul α (A i)] [∀ i, SMul β (A i)]
    [∀ i, SMulCommClass α β (A i)] :
    SMulCommClass α β (GradedMonoid A) where
  smul_comm a b g := Sigma.ext rfl <| heq_of_eq <| smul_comm a b g.2

instance [SMul α β] [∀ i, SMul α (A i)] [∀ i, SMul β (A i)]
    [∀ i, IsScalarTower α β (A i)] :
    IsScalarTower α β (GradedMonoid A) where
  smul_assoc a b g := Sigma.ext rfl <| heq_of_eq <| smul_assoc a b g.2

instance [Monoid α] [∀ i, MulAction α (A i)] :
    MulAction α (GradedMonoid A) where
  one_smul g := Sigma.ext rfl <| heq_of_eq <| one_smul _ g.2
  mul_smul r₁ r₂ g := Sigma.ext rfl <| heq_of_eq <| mul_smul r₁ r₂ g.2

end actions

/-! ### Typeclasses -/

section Defs

variable (A : ι → Type*)

/-- A graded version of `One`, which must be of grade 0. -/
class GOne [Zero ι] where
  /-- The term `one` of grade 0 -/
  one : A 0
#align graded_monoid.ghas_one GradedMonoid.GOne

/-- `GOne` implies `One (GradedMonoid A)` -/
instance GOne.toOne [Zero ι] [GOne A] : One (GradedMonoid A) :=
  ⟨⟨_, GOne.one⟩⟩
#align graded_monoid.ghas_one.to_has_one GradedMonoid.GOne.toOne

@[simp] theorem fst_one [Zero ι] [GOne A] : (1 : GradedMonoid A).fst = 0 := rfl

@[simp] theorem snd_one [Zero ι] [GOne A] : (1 : GradedMonoid A).snd = GOne.one := rfl

/-- A graded version of `Mul`. Multiplication combines grades additively, like
`AddMonoidAlgebra`. -/
class GMul [Add ι] where
  /-- The homogeneous multiplication map `mul` -/
  mul {i j} : A i → A j → A (i + j)
#align graded_monoid.ghas_mul GradedMonoid.GMul

/-- `GMul` implies `Mul (GradedMonoid A)`. -/
instance GMul.toMul [Add ι] [GMul A] : Mul (GradedMonoid A) :=
  ⟨fun x y : GradedMonoid A => ⟨_, GMul.mul x.snd y.snd⟩⟩
#align graded_monoid.ghas_mul.to_has_mul GradedMonoid.GMul.toMul

@[simp] theorem fst_mul [Add ι] [GMul A] (x y : GradedMonoid A) :
    (x * y).fst = x.fst + y.fst := rfl

@[simp] theorem snd_mul [Add ι] [GMul A] (x y : GradedMonoid A) :
    (x * y).snd = GMul.mul x.snd y.snd := rfl

theorem mk_mul_mk [Add ι] [GMul A] {i j} (a : A i) (b : A j) :
    mk i a * mk j b = mk (i + j) (GMul.mul a b) :=
  rfl
#align graded_monoid.mk_mul_mk GradedMonoid.mk_mul_mk

namespace GMonoid

variable {A}
variable [AddMonoid ι] [GMul A] [GOne A]

/-- A default implementation of power on a graded monoid, like `npowRec`.
`GMonoid.gnpow` should be used instead. -/
def gnpowRec : ∀ (n : ℕ) {i}, A i → A (n • i)
  | 0, i, _ => cast (congr_arg A (zero_nsmul i).symm) GOne.one
  | n + 1, i, a => cast (congr_arg A (succ_nsmul i n).symm) (GMul.mul (gnpowRec _ a) a)
#align graded_monoid.gmonoid.gnpow_rec GradedMonoid.GMonoid.gnpowRec

@[simp]
theorem gnpowRec_zero (a : GradedMonoid A) : GradedMonoid.mk _ (gnpowRec 0 a.snd) = 1 :=
  Sigma.ext (zero_nsmul _) (heq_of_cast_eq _ rfl).symm
#align graded_monoid.gmonoid.gnpow_rec_zero GradedMonoid.GMonoid.gnpowRec_zero

@[simp]
theorem gnpowRec_succ (n : ℕ) (a : GradedMonoid A) :
    (GradedMonoid.mk _ <| gnpowRec n.succ a.snd) = ⟨_, gnpowRec n a.snd⟩ * a :=
  Sigma.ext (succ_nsmul _ _) (heq_of_cast_eq _ rfl).symm
#align graded_monoid.gmonoid.gnpow_rec_succ GradedMonoid.GMonoid.gnpowRec_succ

end GMonoid

/-- A tactic to for use as an optional value for `GMonoid.gnpow_zero'`. -/
macro "apply_gmonoid_gnpowRec_zero_tac" : tactic => `(tactic| apply GMonoid.gnpowRec_zero)
/-- A tactic to for use as an optional value for `GMonoid.gnpow_succ'`. -/
macro "apply_gmonoid_gnpowRec_succ_tac" : tactic => `(tactic| apply GMonoid.gnpowRec_succ)

/-- A graded version of `Monoid`

Like `Monoid.npow`, this has an optional `GMonoid.gnpow` field to allow definitional control of
natural powers of a graded monoid. -/
class GMonoid [AddMonoid ι] extends GMul A, GOne A where
  /-- Multiplication by `one` on the left is the identity -/
  one_mul (a : GradedMonoid A) : 1 * a = a
  /-- Multiplication by `one` on the right is the identity -/
  mul_one (a : GradedMonoid A) : a * 1 = a
  /-- Multiplication is associative -/
  mul_assoc (a b c : GradedMonoid A) : a * b * c = a * (b * c)
  /-- Optional field to allow definitional control of natural powers -/
  gnpow : ∀ (n : ℕ) {i}, A i → A (n • i) := GMonoid.gnpowRec
  /-- The zeroth power will yield 1 -/
  gnpow_zero' : ∀ a : GradedMonoid A, GradedMonoid.mk _ (gnpow 0 a.snd) = 1 := by
    apply_gmonoid_gnpowRec_zero_tac
  /-- Successor powers behave as expected -/
  gnpow_succ' :
    ∀ (n : ℕ) (a : GradedMonoid A),
      (GradedMonoid.mk _ <| gnpow n.succ a.snd) = ⟨_, gnpow n a.snd⟩ * a:= by
    apply_gmonoid_gnpowRec_succ_tac
#align graded_monoid.gmonoid GradedMonoid.GMonoid

/-- `GMonoid` implies a `Monoid (GradedMonoid A)`. -/
instance GMonoid.toMonoid [AddMonoid ι] [GMonoid A] : Monoid (GradedMonoid A) where
  one := 1
  mul := (· * ·)
  npow n a := GradedMonoid.mk _ (GMonoid.gnpow n a.snd)
  npow_zero a := GMonoid.gnpow_zero' a
  npow_succ n a := GMonoid.gnpow_succ' n a
  one_mul := GMonoid.one_mul
  mul_one := GMonoid.mul_one
  mul_assoc := GMonoid.mul_assoc
#align graded_monoid.gmonoid.to_monoid GradedMonoid.GMonoid.toMonoid

@[simp] theorem fst_pow [AddMonoid ι] [GMonoid A] (x : GradedMonoid A) (n : ℕ) :
    (x ^ n).fst = n • x.fst := rfl

@[simp] theorem snd_pow [AddMonoid ι] [GMonoid A] (x : GradedMonoid A) (n : ℕ) :
    (x ^ n).snd = GMonoid.gnpow n x.snd := rfl

theorem mk_pow [AddMonoid ι] [GMonoid A] {i} (a : A i) (n : ℕ) :
    mk i a ^ n = mk (n • i) (GMonoid.gnpow _ a) := rfl
#align graded_monoid.mk_pow GradedMonoid.mk_pow

/-- A graded version of `CommMonoid`. -/
class GCommMonoid [AddCommMonoid ι] extends GMonoid A where
  /-- Multiplication is commutative -/
  mul_comm (a : GradedMonoid A) (b : GradedMonoid A) : a * b = b * a
#align graded_monoid.gcomm_monoid GradedMonoid.GCommMonoid

/-- `GCommMonoid` implies a `CommMonoid (GradedMonoid A)`, although this is only used as an
instance locally to define notation in `gmonoid` and similar typeclasses. -/
instance GCommMonoid.toCommMonoid [AddCommMonoid ι] [GCommMonoid A] : CommMonoid (GradedMonoid A) :=
  { GMonoid.toMonoid A with mul_comm := GCommMonoid.mul_comm }
#align graded_monoid.gcomm_monoid.to_comm_monoid GradedMonoid.GCommMonoid.toCommMonoid

end Defs

/-! ### Instances for `A 0`

The various `g*` instances are enough to promote the `AddCommMonoid (A 0)` structure to various
types of multiplicative structure.
-/


section GradeZero

variable (A : ι → Type*)

section One

variable [Zero ι] [GOne A]

/-- `1 : A 0` is the value provided in `GOne.one`. -/
@[nolint unusedArguments]
instance GradeZero.one : One (A 0) :=
  ⟨GOne.one⟩
#align graded_monoid.grade_zero.has_one GradedMonoid.GradeZero.one

end One

section Mul

variable [AddZeroClass ι] [GMul A]

/-- `(•) : A 0 → A i → A i` is the value provided in `GradedMonoid.GMul.mul`, composed with
an `Eq.rec` to turn `A (0 + i)` into `A i`.
-/
instance GradeZero.smul (i : ι) : SMul (A 0) (A i) where
  smul x y := @Eq.rec ι (0+i) (fun a _ => A a) (GMul.mul x y) i (zero_add i)
#align graded_monoid.grade_zero.has_smul GradedMonoid.GradeZero.smul

/-- `(*) : A 0 → A 0 → A 0` is the value provided in `GradedMonoid.GMul.mul`, composed with
an `Eq.rec` to turn `A (0 + 0)` into `A 0`.
-/
instance GradeZero.mul : Mul (A 0) where mul := (· • ·)
#align graded_monoid.grade_zero.has_mul GradedMonoid.GradeZero.mul

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

variable [AddMonoid ι] [GMonoid A]

instance : NatPow (A 0) where
  pow x n := @Eq.rec ι (n • (0:ι)) (fun a _ => A a) (GMonoid.gnpow n x) 0 (nsmul_zero n)

variable {A}

@[simp]
theorem mk_zero_pow (a : A 0) (n : ℕ) : mk _ (a ^ n) = mk _ a ^ n :=
  Sigma.ext (nsmul_zero n).symm <| eq_rec_heq _ _
#align graded_monoid.mk_zero_pow GradedMonoid.mk_zero_pow

variable (A)

/-- The `Monoid` structure derived from `GMonoid A`. -/
instance GradeZero.monoid : Monoid (A 0) :=
  Function.Injective.monoid (mk 0) sigma_mk_injective rfl mk_zero_smul mk_zero_pow
#align graded_monoid.grade_zero.monoid GradedMonoid.GradeZero.monoid

end Monoid

section Monoid

variable [AddCommMonoid ι] [GCommMonoid A]

/-- The `CommMonoid` structure derived from `GCommMonoid A`. -/
instance GradeZero.commMonoid : CommMonoid (A 0) :=
  Function.Injective.commMonoid (mk 0) sigma_mk_injective rfl mk_zero_smul mk_zero_pow
#align graded_monoid.grade_zero.comm_monoid GradedMonoid.GradeZero.commMonoid

end Monoid

section MulAction

variable [AddMonoid ι] [GMonoid A]

/-- `GradedMonoid.mk 0` is a `MonoidHom`, using the `GradedMonoid.GradeZero.monoid` structure.
-/
def mkZeroMonoidHom : A 0 →* GradedMonoid A where
  toFun := mk 0
  map_one' := rfl
  map_mul' := mk_zero_smul
#align graded_monoid.mk_zero_monoid_hom GradedMonoid.mkZeroMonoidHom

/-- Each grade `A i` derives an `A 0`-action structure from `GMonoid A`. -/
instance GradeZero.mulAction {i} : MulAction (A 0) (A i) :=
  letI := MulAction.compHom (GradedMonoid A) (mkZeroMonoidHom A)
  Function.Injective.mulAction (mk i) sigma_mk_injective mk_zero_smul
#align graded_monoid.grade_zero.mul_action GradedMonoid.GradeZero.mulAction

end MulAction

end GradeZero

end GradedMonoid

/-! ### Dependent products of graded elements -/


section DProd

variable {α : Type*} {A : ι → Type*} [AddMonoid ι] [GradedMonoid.GMonoid A]

/-- The index used by `List.dProd`. Propositionally this is equal to `(l.map fι).Sum`, but
definitionally it needs to have a different form to avoid introducing `Eq.rec`s in `List.dProd`. -/
def List.dProdIndex (l : List α) (fι : α → ι) : ι :=
  l.foldr (fun i b => fι i + b) 0
#align list.dprod_index List.dProdIndex

@[simp]
theorem List.dProdIndex_nil (fι : α → ι) : ([] : List α).dProdIndex fι = 0 :=
  rfl
#align list.dprod_index_nil List.dProdIndex_nil

@[simp]
theorem List.dProdIndex_cons (a : α) (l : List α) (fι : α → ι) :
    (a :: l).dProdIndex fι = fι a + l.dProdIndex fι :=
  rfl
#align list.dprod_index_cons List.dProdIndex_cons

theorem List.dProdIndex_eq_map_sum (l : List α) (fι : α → ι) :
    l.dProdIndex fι = (l.map fι).sum := by
  match l with
  | [] => simp
  | head::tail => simp [List.dProdIndex_eq_map_sum tail fι]
#align list.dprod_index_eq_map_sum List.dProdIndex_eq_map_sum

/-- A dependent product for graded monoids represented by the indexed family of types `A i`.
This is a dependent version of `(l.map fA).prod`.

For a list `l : List α`, this computes the product of `fA a` over `a`, where each `fA` is of type
`A (fι a)`. -/
def List.dProd (l : List α) (fι : α → ι) (fA : ∀ a, A (fι a)) : A (l.dProdIndex fι) :=
  l.foldrRecOn _ _ GradedMonoid.GOne.one fun _ x a _ => GradedMonoid.GMul.mul (fA a) x
#align list.dprod List.dProd

@[simp]
theorem List.dProd_nil (fι : α → ι) (fA : ∀ a, A (fι a)) :
    (List.nil : List α).dProd fι fA = GradedMonoid.GOne.one :=
  rfl
#align list.dprod_nil List.dProd_nil

-- the `( : _)` in this lemma statement results in the type on the RHS not being unfolded, which
-- is nicer in the goal view.
@[simp]
theorem List.dProd_cons (fι : α → ι) (fA : ∀ a, A (fι a)) (a : α) (l : List α) :
    (a :: l).dProd fι fA = (GradedMonoid.GMul.mul (fA a) (l.dProd fι fA) : _) :=
  rfl
#align list.dprod_cons List.dProd_cons

theorem GradedMonoid.mk_list_dProd (l : List α) (fι : α → ι) (fA : ∀ a, A (fι a)) :
    GradedMonoid.mk _ (l.dProd fι fA) = (l.map fun a => GradedMonoid.mk (fι a) (fA a)).prod := by
  match l with
  | [] => simp only [List.dProdIndex_nil, List.dProd_nil, List.map_nil, List.prod_nil]; rfl
  | head::tail =>
    simp [← GradedMonoid.mk_list_dProd tail _ _, GradedMonoid.mk_mul_mk, List.prod_cons]
#align graded_monoid.mk_list_dprod GradedMonoid.mk_list_dProd

/-- A variant of `GradedMonoid.mk_list_dProd` for rewriting in the other direction. -/
theorem GradedMonoid.list_prod_map_eq_dProd (l : List α) (f : α → GradedMonoid A) :
    (l.map f).prod = GradedMonoid.mk _ (l.dProd (fun i => (f i).1) fun i => (f i).2) := by
  rw [GradedMonoid.mk_list_dProd, GradedMonoid.mk]
  simp_rw [Sigma.eta]
#align graded_monoid.list_prod_map_eq_dprod GradedMonoid.list_prod_map_eq_dProd

theorem GradedMonoid.list_prod_ofFn_eq_dProd {n : ℕ} (f : Fin n → GradedMonoid A) :
    (List.ofFn f).prod =
      GradedMonoid.mk _ ((List.finRange n).dProd (fun i => (f i).1) fun i => (f i).2) := by
  rw [List.ofFn_eq_map, GradedMonoid.list_prod_map_eq_dProd]
#align graded_monoid.list_prod_of_fn_eq_dprod GradedMonoid.list_prod_ofFn_eq_dProd

end DProd

/-! ### Concrete instances -/


section

variable (ι) {R : Type*}

@[simps one]
instance One.gOne [Zero ι] [One R] : GradedMonoid.GOne fun _ : ι => R where one := 1
#align has_one.ghas_one One.gOne

@[simps mul]
instance Mul.gMul [Add ι] [Mul R] : GradedMonoid.GMul fun _ : ι => R where mul x y := x * y
#align has_mul.ghas_mul Mul.gMul

/-- If all grades are the same type and themselves form a monoid, then there is a trivial grading
structure. -/
@[simps gnpow]
instance Monoid.gMonoid [AddMonoid ι] [Monoid R] : GradedMonoid.GMonoid fun _ : ι => R :=
  -- { Mul.gMul ι, One.gOne ι with
  { One.gOne ι with
    mul := fun x y => x * y
    one_mul := fun _ => Sigma.ext (zero_add _) (heq_of_eq (one_mul _))
    mul_one := fun _ => Sigma.ext (add_zero _) (heq_of_eq (mul_one _))
    mul_assoc := fun _ _ _ => Sigma.ext (add_assoc _ _ _) (heq_of_eq (mul_assoc _ _ _))
    gnpow := fun n _ a => a ^ n
    gnpow_zero' := fun _ => Sigma.ext (zero_nsmul _) (heq_of_eq (Monoid.npow_zero _))
    gnpow_succ' := fun _ ⟨_, _⟩ => Sigma.ext (succ_nsmul _ _) (heq_of_eq (Monoid.npow_succ _ _)) }
#align monoid.gmonoid Monoid.gMonoid
#align monoid.gmonoid_gnpow Monoid.gMonoid_gnpow

/-- If all grades are the same type and themselves form a commutative monoid, then there is a
trivial grading structure. -/
instance CommMonoid.gCommMonoid [AddCommMonoid ι] [CommMonoid R] :
    GradedMonoid.GCommMonoid fun _ : ι => R :=
  { Monoid.gMonoid ι with
    mul_comm := fun _ _ => Sigma.ext (add_comm _ _) (heq_of_eq (mul_comm _ _)) }
#align comm_monoid.gcomm_monoid CommMonoid.gCommMonoid

/-- When all the indexed types are the same, the dependent product is just the regular product. -/
@[simp]
theorem List.dProd_monoid {α} [AddMonoid ι] [Monoid R] (l : List α) (fι : α → ι) (fA : α → R) :
    @List.dProd _ _ (fun _ : ι => R) _ _ l fι fA = (l.map fA).prod := by
  match l with
  | [] =>
    rw [List.dProd_nil, List.map_nil, List.prod_nil]
    rfl
  | head::tail =>
    rw [List.dProd_cons, List.map_cons, List.prod_cons, List.dProd_monoid tail _ _]
    rfl
#align list.dprod_monoid List.dProd_monoid

end

/-! ### Shorthands for creating instance of the above typeclasses for collections of subobjects -/


section Subobjects

variable {R : Type*}

/-- A version of `GradedMonoid.GOne` for internally graded objects. -/
class SetLike.GradedOne {S : Type*} [SetLike S R] [One R] [Zero ι] (A : ι → S) : Prop where
  /-- One has grade zero -/
  one_mem : (1 : R) ∈ A 0
#align set_like.has_graded_one SetLike.GradedOne

theorem SetLike.one_mem_graded {S : Type*} [SetLike S R] [One R] [Zero ι] (A : ι → S)
    [SetLike.GradedOne A] : (1 : R) ∈ A 0 :=
  SetLike.GradedOne.one_mem
#align set_like.one_mem_graded SetLike.one_mem_graded

instance SetLike.gOne {S : Type*} [SetLike S R] [One R] [Zero ι] (A : ι → S)
    [SetLike.GradedOne A] : GradedMonoid.GOne fun i => A i where
  one := ⟨1, SetLike.one_mem_graded _⟩
#align set_like.ghas_one SetLike.gOne

@[simp]
theorem SetLike.coe_gOne {S : Type*} [SetLike S R] [One R] [Zero ι] (A : ι → S)
    [SetLike.GradedOne A] : ↑(@GradedMonoid.GOne.one _ (fun i => A i) _ _) = (1 : R) :=
  rfl
#align set_like.coe_ghas_one SetLike.coe_gOne

/-- A version of `GradedMonoid.ghas_one` for internally graded objects. -/
class SetLike.GradedMul {S : Type*} [SetLike S R] [Mul R] [Add ι] (A : ι → S) : Prop where
  /-- Multiplication is homogeneous -/
  mul_mem : ∀ ⦃i j⦄ {gi gj}, gi ∈ A i → gj ∈ A j → gi * gj ∈ A (i + j)
#align set_like.has_graded_mul SetLike.GradedMul

theorem SetLike.mul_mem_graded {S : Type*} [SetLike S R] [Mul R] [Add ι] {A : ι → S}
    [SetLike.GradedMul A] ⦃i j⦄ {gi gj} (hi : gi ∈ A i) (hj : gj ∈ A j) : gi * gj ∈ A (i + j) :=
  SetLike.GradedMul.mul_mem hi hj
#align set_like.mul_mem_graded SetLike.mul_mem_graded

instance SetLike.gMul {S : Type*} [SetLike S R] [Mul R] [Add ι] (A : ι → S)
    [SetLike.GradedMul A] : GradedMonoid.GMul fun i => A i where
  mul := fun a b => ⟨(a * b : R), SetLike.mul_mem_graded a.prop b.prop⟩
#align set_like.ghas_mul SetLike.gMul

/-
Porting note: simpNF linter returns

"Left-hand side does not simplify, when using the simp lemma on itself."

However, simp does indeed solve the following. Possibly related std#71,std#78

example {S : Type*} [SetLike S R] [Mul R] [Add ι] (A : ι → S)
    [SetLike.GradedMul A] {i j : ι} (x : A i) (y : A j) :
    ↑(@GradedMonoid.GMul.mul _ (fun i => A i) _ _ _ _ x y) = (x * y : R) := by simp

-/
@[simp,nolint simpNF]
theorem SetLike.coe_gMul {S : Type*} [SetLike S R] [Mul R] [Add ι] (A : ι → S)
    [SetLike.GradedMul A] {i j : ι} (x : A i) (y : A j) :
    ↑(@GradedMonoid.GMul.mul _ (fun i => A i) _ _ _ _ x y) = (x * y : R) :=
  rfl
#align set_like.coe_ghas_mul SetLike.coe_gMul


/-- A version of `GradedMonoid.GMonoid` for internally graded objects. -/
class SetLike.GradedMonoid {S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι] (A : ι → S) extends
  SetLike.GradedOne A, SetLike.GradedMul A : Prop
#align set_like.graded_monoid SetLike.GradedMonoid

namespace SetLike

variable {S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι]
variable {A : ι → S} [SetLike.GradedMonoid A]

theorem pow_mem_graded (n : ℕ) {r : R} {i : ι} (h : r ∈ A i) : r ^ n ∈ A (n • i) := by
  match n with
  | 0 =>
    rw [pow_zero, zero_nsmul]
    exact one_mem_graded _
  | n+1 =>
    rw [pow_succ', succ_nsmul']
    exact mul_mem_graded h (pow_mem_graded n h)
#align set_like.pow_mem_graded SetLike.pow_mem_graded

theorem list_prod_map_mem_graded {ι'} (l : List ι') (i : ι' → ι) (r : ι' → R)
    (h : ∀ j ∈ l, r j ∈ A (i j)) : (l.map r).prod ∈ A (l.map i).sum := by
  match l with
  | [] =>
    rw [List.map_nil, List.map_nil, List.prod_nil, List.sum_nil]
    exact one_mem_graded _
  | head::tail =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.sum_cons]
    exact
      mul_mem_graded (h _ <| List.mem_cons_self _ _)
        (list_prod_map_mem_graded tail _ _ fun j hj => h _ <| List.mem_cons_of_mem _ hj)
#align set_like.list_prod_map_mem_graded SetLike.list_prod_map_mem_graded

theorem list_prod_ofFn_mem_graded {n} (i : Fin n → ι) (r : Fin n → R) (h : ∀ j, r j ∈ A (i j)) :
    (List.ofFn r).prod ∈ A (List.ofFn i).sum := by
  rw [List.ofFn_eq_map, List.ofFn_eq_map]
  exact list_prod_map_mem_graded _ _ _ fun _ _ => h _
#align set_like.list_prod_of_fn_mem_graded SetLike.list_prod_ofFn_mem_graded

end SetLike

/-- Build a `GMonoid` instance for a collection of subobjects. -/
instance SetLike.gMonoid {S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι] (A : ι → S)
    [SetLike.GradedMonoid A] : GradedMonoid.GMonoid fun i => A i :=
  { SetLike.gOne A,
    SetLike.gMul A with
    one_mul := fun ⟨_, _, _⟩ => Sigma.subtype_ext (zero_add _) (one_mul _)
    mul_one := fun ⟨_, _, _⟩ => Sigma.subtype_ext (add_zero _) (mul_one _)
    mul_assoc := fun ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨_, _, _⟩ =>
      Sigma.subtype_ext (add_assoc _ _ _) (mul_assoc _ _ _)
    gnpow := fun n _ a => ⟨(a:R)^n, SetLike.pow_mem_graded n a.prop⟩
    gnpow_zero' := fun _ => Sigma.subtype_ext (zero_nsmul _) (pow_zero _)
    gnpow_succ' := fun _ _ => Sigma.subtype_ext (succ_nsmul _ _) (pow_succ _ _) }
#align set_like.gmonoid SetLike.gMonoid

/-
Porting note: simpNF linter returns

"Left-hand side does not simplify, when using the simp lemma on itself."

However, simp does indeed solve the following. Possibly related std#71,std#78

example {S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι] (A : ι → S)
    [SetLike.GradedMonoid A] {i : ι} (x : A i) (n : ℕ) :
    ↑(@GradedMonoid.GMonoid.gnpow _ (fun i => A i) _ _ n _ x) = (x:R)^n := by simp

-/
@[simp,nolint simpNF]
theorem SetLike.coe_gnpow {S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι] (A : ι → S)
    [SetLike.GradedMonoid A] {i : ι} (x : A i) (n : ℕ) :
    ↑(@GradedMonoid.GMonoid.gnpow _ (fun i => A i) _ _ n _ x) = (x:R)^n :=
  rfl
#align set_like.coe_gnpow SetLike.coe_gnpow

/-- Build a `GCommMonoid` instance for a collection of subobjects. -/
instance SetLike.gCommMonoid {S : Type*} [SetLike S R] [CommMonoid R] [AddCommMonoid ι] (A : ι → S)
    [SetLike.GradedMonoid A] : GradedMonoid.GCommMonoid fun i => A i :=
  { SetLike.gMonoid A with
    mul_comm := fun ⟨_, _, _⟩ ⟨_, _, _⟩ => Sigma.subtype_ext (add_comm _ _) (mul_comm _ _) }
#align set_like.gcomm_monoid SetLike.gCommMonoid

section DProd

open SetLike SetLike.GradedMonoid

variable {α S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι]

/-
Porting note: simpNF linter returns

"Left-hand side does not simplify, when using the simp lemma on itself."

However, simp does indeed solve the following. Possibly related std#71,std#78

example (A : ι → S) [SetLike.GradedMonoid A] (fι : α → ι)
    (fA : ∀ a, A (fι a)) (l : List α) : ↑(@List.dProd _ _ (fun i => ↥(A i)) _ _ l fι fA)
    = (List.prod (l.map fun a => fA a) : R) := by simp
-/
/-- Coercing a dependent product of subtypes is the same as taking the regular product of the
coercions. -/
@[simp,nolint simpNF]
theorem SetLike.coe_list_dProd (A : ι → S) [SetLike.GradedMonoid A] (fι : α → ι)
    (fA : ∀ a, A (fι a)) (l : List α) : ↑(@List.dProd _ _ (fun i => ↥(A i)) _ _ l fι fA)
    = (List.prod (l.map fun a => fA a) : R) := by
  match l with
  | [] =>
    rw [List.dProd_nil, coe_gOne, List.map_nil, List.prod_nil]
  | head::tail =>
    rw [List.dProd_cons, coe_gMul, List.map_cons, List.prod_cons,
      SetLike.coe_list_dProd _ _ _ tail]
#align set_like.coe_list_dprod SetLike.coe_list_dProd

/-- A version of `List.coe_dProd_set_like` with `Subtype.mk`. -/
theorem SetLike.list_dProd_eq (A : ι → S) [SetLike.GradedMonoid A] (fι : α → ι) (fA : ∀ a, A (fι a))
    (l : List α) :
    (@List.dProd _ _ (fun i => ↥(A i)) _ _ l fι fA) =
      ⟨List.prod (l.map fun a => fA a),
        (l.dProdIndex_eq_map_sum fι).symm ▸
          list_prod_map_mem_graded l _ _ fun i _ => (fA i).prop⟩ :=
  Subtype.ext <| SetLike.coe_list_dProd _ _ _ _
#align set_like.list_dprod_eq SetLike.list_dProd_eq

end DProd

end Subobjects

section HomogeneousElements

variable {R S : Type*} [SetLike S R]

/-- An element `a : R` is said to be homogeneous if there is some `i : ι` such that `a ∈ A i`. -/
def SetLike.Homogeneous (A : ι → S) (a : R) : Prop :=
  ∃ i, a ∈ A i
#align set_like.is_homogeneous SetLike.Homogeneous

@[simp]
theorem SetLike.homogeneous_coe {A : ι → S} {i} (x : A i) : SetLike.Homogeneous A (x : R) :=
  ⟨i, x.prop⟩
#align set_like.is_homogeneous_coe SetLike.homogeneous_coe

theorem SetLike.homogeneous_one [Zero ι] [One R] (A : ι → S) [SetLike.GradedOne A] :
    SetLike.Homogeneous A (1 : R) :=
  ⟨0, SetLike.one_mem_graded _⟩
#align set_like.is_homogeneous_one SetLike.homogeneous_one

theorem SetLike.homogeneous_mul [Add ι] [Mul R] {A : ι → S} [SetLike.GradedMul A] {a b : R} :
    SetLike.Homogeneous A a → SetLike.Homogeneous A b → SetLike.Homogeneous A (a * b)
  | ⟨i, hi⟩, ⟨j, hj⟩ => ⟨i + j, SetLike.mul_mem_graded hi hj⟩
#align set_like.is_homogeneous.mul SetLike.homogeneous_mul

/-- When `A` is a `SetLike.GradedMonoid A`, then the homogeneous elements forms a submonoid. -/
def SetLike.homogeneousSubmonoid [AddMonoid ι] [Monoid R] (A : ι → S) [SetLike.GradedMonoid A] :
    Submonoid R where
  carrier := { a | SetLike.Homogeneous A a }
  one_mem' := SetLike.homogeneous_one A
  mul_mem' a b := SetLike.homogeneous_mul a b
#align set_like.homogeneous_submonoid SetLike.homogeneousSubmonoid

end HomogeneousElements
