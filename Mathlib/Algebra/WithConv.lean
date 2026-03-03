/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.TransferInstance

/-! # Type synonym for linear map convolutive ring and intrinsic star

This files provides the type synonym `WithConv` which we will use in later files
to put the convolutive product on linear maps instance and the intrinsic star instance.
This is to ensure that we only have one multiplication, one unit, and one star.

This is given for any type `A` so that we can have `WithConv (A →ₗ[R] B)`,
`WithConv (A →L[R] B)`, `WithConv (Matrix m n R)`, etc.
-/

@[expose] public section

/-- A type synonym for the convolutive product of linear maps and intrinsic star.

The instances for the convolutive product and intrinsic star are only available with this type.

Use `WithConv.linearEquiv` to coerce into this type. -/
structure WithConv A where
  /-- Converts an element of `A` to `WithConv A`. -/ toConv ::
  /-- Converts an element of `WithConv A` back to `A`. -/ ofConv : A

namespace WithConv

open Lean.PrettyPrinter.Delaborator in
/-- This prevents `toConv x` being printed as `{ ofConv := x }` by `delabStructureInstance`. -/
@[app_delab toConv]
meta def delabToConv : Delab := delabApp

variable {R A B C : Type*}

lemma ofConv_toConv (x : A) : ofConv (toConv x) = x := rfl
@[simp] lemma toConv_ofConv (x : WithConv A) : toConv (ofConv x) = x := rfl

lemma ofConv_surjective : Function.Surjective (@ofConv A) :=
  Function.RightInverse.surjective ofConv_toConv

lemma toConv_surjective : Function.Surjective (@toConv A) :=
  Function.RightInverse.surjective toConv_ofConv

lemma ofConv_injective : Function.Injective (@ofConv A) :=
  Function.LeftInverse.injective toConv_ofConv

lemma toConv_injective : Function.Injective (@toConv A) :=
  Function.LeftInverse.injective ofConv_toConv

lemma ofConv_bijective : Function.Bijective (@ofConv A) := ⟨ofConv_injective, ofConv_surjective⟩
lemma toConv_bijective : Function.Bijective (@toConv A) := ⟨toConv_injective, toConv_surjective⟩

instance [CoeFun A (fun _ ↦ B → C)] : CoeFun (WithConv A) (fun _ ↦ B → C) where coe f := ⇑f.ofConv

@[ext] protected theorem ext {x y : WithConv A}
    (h : x.ofConv = y.ofConv) : x = y := ofConv_injective h

variable (A) in
/-- `WithConv.ofConv` and `WithConv.toConv` as an equivalence. -/
protected def equiv : WithConv A ≃ A where
  toFun := ofConv
  invFun := toConv
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma equiv_apply (x : WithConv A) : WithConv.equiv A x = x.ofConv := rfl
@[simp] lemma symm_equiv_apply (x : A) : (WithConv.equiv A).symm x = toConv x := rfl

instance [Nontrivial A] : Nontrivial (WithConv A) := (WithConv.equiv A).nontrivial
instance [Unique A] : Unique (WithConv A) := (WithConv.equiv A).unique
instance [DecidableEq A] : DecidableEq (WithConv A) := (WithConv.equiv A).decidableEq
instance [AddMonoid A] : AddMonoid (WithConv A) := (WithConv.equiv A).addMonoid
instance [AddCommMonoid A] : AddCommMonoid (WithConv A) := (WithConv.equiv A).addCommMonoid
instance [AddGroup A] : AddGroup (WithConv A) := (WithConv.equiv A).addGroup
instance [AddCommGroup A] : AddCommGroup (WithConv A) := (WithConv.equiv A).addCommGroup
@[to_additive] instance [Monoid R] [MulAction R A] : MulAction R (WithConv A) :=
  fast_instance% (WithConv.equiv A).mulAction R
instance [Monoid R] [AddCommMonoid A] [DistribMulAction R A] : DistribMulAction R (WithConv A) :=
  fast_instance% (WithConv.equiv A).distribMulAction R
instance [Semiring R] [AddCommMonoid A] [Module R A] : Module R (WithConv A) :=
  fast_instance% (WithConv.equiv A).module R

section AddGroup
variable [AddGroup A]

@[simp] lemma toConv_sub (x y : A) : toConv (x - y) = toConv x - toConv y := rfl
@[simp] lemma ofConv_sub (x y : WithConv A) : ofConv (x - y) = ofConv x - ofConv y := rfl
@[simp] lemma ofConv_neg (x : WithConv A) : ofConv (-x) = -ofConv x := rfl
@[simp] lemma toConv_neg (x : A) : toConv (-x) = -toConv x := rfl

end AddGroup

@[simp] lemma ofConv_smul [Monoid R] [MulAction R A] (c : R) (x : WithConv A) :
    ofConv (c • x) = c • ofConv x := rfl
@[simp] lemma toConv_smul [Monoid R] [MulAction R A] (c : R) (x : A) :
    toConv (c • x) = c • toConv x := rfl

section
variable [AddMonoid A]

@[simp] lemma ofConv_zero : ofConv (0 : WithConv A) = 0 := rfl
@[simp] lemma toConv_zero : toConv (0 : A) = 0 := rfl
@[simp] lemma ofConv_add (x y : WithConv A) : ofConv (x + y) = ofConv x + ofConv y := rfl
@[simp] lemma toConv_add (x y : A) : toConv (x + y) = toConv x + toConv y := rfl
@[simp] lemma ofConv_eq_zero {x : WithConv A} : ofConv x = 0 ↔ x = 0 := ofConv_injective.eq_iff
@[simp] lemma toConv_eq_zero {x : A} : toConv x = 0 ↔ x = 0 := toConv_injective.eq_iff

variable (A) in
/-- The additive equivalence between `WithConv A` and `A`. -/
@[simps!] protected def addEquiv : WithConv A ≃+ A where
  __ := WithConv.equiv A
  map_add' := by simp

@[simp] theorem toEquiv_addEquiv : (WithConv.addEquiv A : WithConv A ≃ A) = WithConv.equiv A := rfl

end

variable [AddCommMonoid A]

variable (R A) in
/-- The linear equivalence between `WithConv A` and `A`. -/
protected def linearEquiv [Semiring R] [Module R A] : WithConv A ≃ₗ[R] A where
  __ := WithConv.addEquiv A
  map_smul' := by simp

@[simp] lemma linearEquiv_apply [Semiring R] [Module R A]
    (a : WithConv A) : WithConv.linearEquiv R A a = ofConv a := rfl
@[simp] lemma symm_linearEquiv_apply [Semiring R] [Module R A]
    (a : A) : (WithConv.linearEquiv R A).symm a = toConv a := rfl
@[simp] lemma toAddEquiv_linearEquiv [Semiring R] [Module R A] :
    (WithConv.linearEquiv R A).toAddEquiv = WithConv.addEquiv A := rfl

@[simp] lemma ofConv_sum {ι : Type*} (s : Finset ι) (f : ι → WithConv A) :
    (∑ i ∈ s, f i).ofConv = ∑ i ∈ s, (f i).ofConv := map_sum (WithConv.addEquiv _) _ _
@[simp] lemma toConv_sum {ι : Type*} (s : Finset ι) (f : ι → A) :
    toConv (∑ i ∈ s, f i) = ∑ i ∈ s, toConv (f i) := map_sum (WithConv.addEquiv _).symm _ _
@[simp] lemma ofConv_listSum (l : List (WithConv A)) :
    l.sum.ofConv = (l.map ofConv).sum := map_list_sum (WithConv.addEquiv _) _
@[simp] lemma toConv_listSum (l : List A) :
    toConv l.sum = (l.map toConv).sum := map_list_sum (WithConv.addEquiv _).symm _
@[simp] lemma ofConv_multisetSum (s : Multiset (WithConv A)) :
    s.sum.ofConv = (s.map ofConv).sum := map_multiset_sum (WithConv.addEquiv _) _
@[simp] lemma toConv_multisetSum (s : Multiset A) :
    toConv s.sum = (s.map toConv).sum := map_multiset_sum (WithConv.addEquiv _).symm _

end WithConv
