/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.free_monoid.basic
! leanprover-community/mathlib commit dd71334db81d0bd444af1ee339a29298bef40734
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.List.BigOperators.Basic

/-!
# Free monoid over a given alphabet

## Main definitions

* `FreeMonoid α`: free monoid over alphabet `α`; defined as a synonym for `List α`
  with multiplication given by `(++)`.
* `FreeMonoid.of`: embedding `α → FreeMonoid α` sending each element `x` to `[x]`;
* `FreeMonoid.lift`: natural equivalence between `α → M` and `FreeMonoid α →* M`
* `FreeMonoid.map`: embedding of `α → β` into `FreeMonoid α →* FreeMonoid β` given by `List.map`.
-/


variable {α : Type _} {β : Type _} {γ : Type _} {M : Type _} [Monoid M] {N : Type _} [Monoid N]

/-- Free monoid over a given alphabet. -/
@[to_additive "Free nonabelian additive monoid over a given alphabet"]
def FreeMonoid (α) := List α
#align free_monoid FreeMonoid

namespace FreeMonoid

-- Porting note: TODO. Check this is still needed
@[to_additive]
instance [DecidableEq α] : DecidableEq (FreeMonoid α) := instDecidableEqList

/-- The identity equivalence between `FreeMonoid α` and `List α`. -/
@[to_additive "The identity equivalence between `FreeAddMonoid α` and `List α`."]
def toList : FreeMonoid α ≃ List α := Equiv.refl _
#align free_monoid.to_list FreeMonoid.toList

/-- The identity equivalence between `List α` and `FreeMonoid α`. -/
@[to_additive "The identity equivalence between `List α` and `FreeAddMonoid α`."]
def ofList : List α ≃ FreeMonoid α := Equiv.refl _
#align free_monoid.of_list FreeMonoid.ofList

@[to_additive (attr := simp)]
theorem toList_symm : (@toList α).symm = ofList := rfl
#align free_monoid.to_list_symm FreeMonoid.toList_symm

@[to_additive (attr := simp)]
theorem ofList_symm : (@ofList α).symm = toList := rfl
#align free_monoid.of_list_symm FreeMonoid.ofList_symm

@[to_additive (attr := simp)]
theorem toList_ofList (l : List α) : toList (ofList l) = l := rfl
#align free_monoid.to_list_of_list FreeMonoid.toList_ofList

@[to_additive (attr := simp)]
theorem ofList_toList (xs : FreeMonoid α) : ofList (toList xs) = xs := rfl
#align free_monoid.of_list_to_list FreeMonoid.ofList_toList

@[to_additive (attr := simp)]
theorem toList_comp_ofList : @toList α ∘ ofList = id := rfl
#align free_monoid.to_list_comp_of_list FreeMonoid.toList_comp_ofList

@[to_additive (attr := simp)]
theorem ofList_comp_toList : @ofList α ∘ toList = id := rfl
#align free_monoid.of_list_comp_to_list FreeMonoid.ofList_comp_toList

@[to_additive]
instance : CancelMonoid (FreeMonoid α)
    where
  one := ofList []
  mul x y := ofList (toList x ++ toList y)
  mul_one := List.append_nil
  one_mul := List.nil_append
  mul_assoc := List.append_assoc
  mul_left_cancel _ _ _ := List.append_left_cancel
  mul_right_cancel _ _ _ := List.append_right_cancel

@[to_additive]
instance : Inhabited (FreeMonoid α) := ⟨1⟩

@[to_additive (attr := simp)]
theorem toList_one : toList (1 : FreeMonoid α) = [] := rfl
#align free_monoid.to_list_one FreeMonoid.toList_one

@[to_additive (attr := simp)]
theorem ofList_nil : ofList ([] : List α) = 1 := rfl
#align free_monoid.of_list_nil FreeMonoid.ofList_nil

@[to_additive (attr := simp)]
theorem toList_mul (xs ys : FreeMonoid α) : toList (xs * ys) = toList xs ++ toList ys := rfl
#align free_monoid.to_list_mul FreeMonoid.toList_mul

@[to_additive (attr := simp)]
theorem ofList_append (xs ys : List α) : ofList (xs ++ ys) = ofList xs * ofList ys := rfl
#align free_monoid.of_list_append FreeMonoid.ofList_append

@[to_additive (attr := simp)]
theorem toList_prod (xs : List (FreeMonoid α)) : toList xs.prod = (xs.map toList).join := by
  induction xs <;> simp [*, List.join]
#align free_monoid.to_list_prod FreeMonoid.toList_prod

@[to_additive (attr := simp)]
theorem ofList_join (xs : List (List α)) : ofList xs.join = (xs.map ofList).prod :=
  toList.injective <| by simp
#align free_monoid.of_list_join FreeMonoid.ofList_join

/-- Embeds an element of `α` into `FreeMonoid α` as a singleton list. -/
@[to_additive "Embeds an element of `α` into `FreeAddMonoid α` as a singleton list."]
def of (x : α) : FreeMonoid α := ofList [x]
#align free_monoid.of FreeMonoid.of

@[to_additive (attr := simp)]
theorem toList_of (x : α) : toList (of x) = [x] := rfl
#align free_monoid.to_list_of FreeMonoid.toList_of

@[to_additive]
theorem ofList_singleton (x : α) : ofList [x] = of x := rfl
#align free_monoid.of_list_singleton FreeMonoid.ofList_singleton

@[to_additive (attr := simp)]
theorem ofList_cons (x : α) (xs : List α) : ofList (x :: xs) = of x * ofList xs := rfl
#align free_monoid.of_list_cons FreeMonoid.ofList_cons

@[to_additive]
theorem toList_of_mul (x : α) (xs : FreeMonoid α) : toList (of x * xs) = x :: toList xs := rfl
#align free_monoid.to_list_of_mul FreeMonoid.toList_of_mul

@[to_additive]
theorem of_injective : Function.Injective (@of α) := List.singleton_injective
#align free_monoid.of_injective FreeMonoid.of_injective

/-- Recursor for `FreeMonoid` using `1` and `FreeMonoid.of x * xs` instead of `[]` and `x :: xs`. -/
@[elab_as_elim, to_additive "Recursor for `FreeAddMonoid` using `0` and `FreeAddMonoid.of x + xs`
instead of `[]` and `x :: xs`."]
-- Porting note: added noncomputable
noncomputable def recOn {C : FreeMonoid α → Sort _} (xs : FreeMonoid α) (h0 : C 1)
    (ih : ∀ x xs, C xs → C (of x * xs)) : C xs := List.recOn xs h0 ih
#align free_monoid.rec_on FreeMonoid.recOn

@[to_additive (attr := simp)]
theorem recOn_one {C : FreeMonoid α → Sort _} (h0 : C 1) (ih : ∀ x xs, C xs → C (of x * xs)) :
    @recOn α C 1 h0 ih = h0 := rfl
#align free_monoid.rec_on_one FreeMonoid.recOn_one

@[to_additive (attr := simp)]
theorem recOn_of_mul {C : FreeMonoid α → Sort _} (x : α) (xs : FreeMonoid α) (h0 : C 1)
    (ih : ∀ x xs, C xs → C (of x * xs)) : @recOn α C (of x * xs) h0 ih = ih x xs (recOn xs h0 ih) :=
  rfl
#align free_monoid.rec_on_of_mul FreeMonoid.recOn_of_mul

/-- A version of `List.cases_on` for `FreeMonoid` using `1` and `FreeMonoid.of x * xs` instead of
`[]` and `x :: xs`. -/
@[elab_as_elim, to_additive "A version of `List.casesOn` for `FreeAddMonoid` using `0` and
`FreeAddMonoid.of x + xs` instead of `[]` and `x :: xs`."]
def casesOn {C : FreeMonoid α → Sort _} (xs : FreeMonoid α) (h0 : C 1)
    (ih : ∀ x xs, C (of x * xs)) : C xs := List.casesOn xs h0 ih
#align free_monoid.cases_on FreeMonoid.casesOn

@[to_additive (attr := simp)]
theorem casesOn_one {C : FreeMonoid α → Sort _} (h0 : C 1) (ih : ∀ x xs, C (of x * xs)) :
    @casesOn α C 1 h0 ih = h0 := rfl
#align free_monoid.cases_on_one FreeMonoid.casesOn_one

@[to_additive (attr := simp)]
theorem casesOn_of_mul {C : FreeMonoid α → Sort _} (x : α) (xs : FreeMonoid α) (h0 : C 1)
    (ih : ∀ x xs, C (of x * xs)) : @casesOn α C (of x * xs) h0 ih = ih x xs := rfl
#align free_monoid.cases_on_of_mul FreeMonoid.casesOn_of_mul

@[to_additive (attr := ext)]
theorem hom_eq ⦃f g : FreeMonoid α →* M⦄ (h : ∀ x, f (of x) = g (of x)) : f = g :=
  MonoidHom.ext fun l ↦ recOn l (f.map_one.trans g.map_one.symm)
    (fun x xs hxs ↦ by  simp only [h, hxs, MonoidHom.map_mul])
#align free_monoid.hom_eq FreeMonoid.hom_eq

/-- Equivalence between maps `α → M` and monoid homomorphisms `FreeMonoid α →* M`. -/
@[to_additive "Equivalence between maps `α → A` and additive monoid homomorphisms
`FreeAddMonoid α →+ A`."]
def lift : (α → M) ≃ (FreeMonoid α →* M)
    where
  toFun f :=
  { toFun := fun l ↦ ((toList l).map f).prod
    map_one' := rfl -- sorry
    map_mul' := fun _ _ ↦ by simp only [toList_mul, List.map_append, List.prod_append] }
  invFun f x := f (of x)
  left_inv f := funext fun x ↦ one_mul (f x)
  right_inv f := hom_eq fun x ↦ one_mul (f (of x))
#align free_monoid.lift FreeMonoid.lift

@[to_additive (attr := simp)]
theorem lift_symm_apply (f : FreeMonoid α →* M) : lift.symm f = f ∘ of := rfl
#align free_monoid.lift_symm_apply FreeMonoid.lift_symm_apply

@[to_additive]
theorem lift_apply (f : α → M) (l : FreeMonoid α) : lift f l = ((toList l).map f).prod := rfl
#align free_monoid.lift_apply FreeMonoid.lift_apply

@[to_additive]
theorem lift_comp_of (f : α → M) : lift f ∘ of = f := lift.symm_apply_apply f
#align free_monoid.lift_comp_of FreeMonoid.lift_comp_of

@[to_additive (attr := simp)]
theorem lift_eval_of (f : α → M) (x : α) : lift f (of x) = f x := congr_fun (lift_comp_of f) x
#align free_monoid.lift_eval_of FreeMonoid.lift_eval_of

@[to_additive (attr := simp)]
theorem lift_restrict (f : FreeMonoid α →* M) : lift (f ∘ of) = f := lift.apply_symm_apply f
#align free_monoid.lift_restrict FreeMonoid.lift_restrict

@[to_additive]
theorem comp_lift (g : M →* N) (f : α → M) : g.comp (lift f) = lift (g ∘ f) :=
-- Porting note: replace ext by FreeMonoid.hom_eq
  FreeMonoid.hom_eq (by simp)
#align free_monoid.comp_lift FreeMonoid.comp_lift

@[to_additive]
theorem hom_map_lift (g : M →* N) (f : α → M) (x : FreeMonoid α) : g (lift f x) = lift (g ∘ f) x :=
  FunLike.ext_iff.1 (comp_lift g f) x
#align free_monoid.hom_map_lift FreeMonoid.hom_map_lift

/-- Define a multiplicative action of `FreeMonoid α` on `β`. -/
@[to_additive "Define an additive action of `FreeAddMonoid α` on `β`."]
def mkMulAction (f : α → β → β) : MulAction (FreeMonoid α) β where
  smul l b := l.toList.foldr f b
  one_smul _ := rfl
  mul_smul _ _ _ := List.foldr_append _ _ _ _
#align free_monoid.mk_mul_action FreeMonoid.mkMulAction

@[to_additive]
theorem smul_def (f : α → β → β) (l : FreeMonoid α) (b : β) :
    haveI := mkMulAction f
    l • b = l.toList.foldr f b := rfl
#align free_monoid.smul_def FreeMonoid.smul_def

@[to_additive]
theorem ofList_smul (f : α → β → β) (l : List α) (b : β) :
    haveI := mkMulAction f
    ofList l • b = l.foldr f b := rfl
#align free_monoid.of_list_smul FreeMonoid.ofList_smul

@[to_additive (attr := simp)]
theorem of_smul (f : α → β → β) (x : α) (y : β) :
    (haveI := mkMulAction f
    of x • y) = f x y := rfl
#align free_monoid.of_smul FreeMonoid.of_smul

/-- The unique monoid homomorphism `FreeMonoid α →* FreeMonoid β` that sends
each `of x` to `of (f x)`. -/
@[to_additive "The unique additive monoid homomorphism `FreeAddMonoid α →+ FreeAddMonoid β`
that sends each `of x` to `of (f x)`."]
def map (f : α → β) : FreeMonoid α →* FreeMonoid β
    where
  toFun l := ofList <| l.toList.map f
  map_one' := rfl
  map_mul' _ _ := List.map_append _ _ _
#align free_monoid.map FreeMonoid.map

@[to_additive (attr := simp)]
theorem map_of (f : α → β) (x : α) : map f (of x) = of (f x) := rfl
#align free_monoid.map_of FreeMonoid.map_of

@[to_additive]
theorem toList_map (f : α → β) (xs : FreeMonoid α) : toList (map f xs) = xs.toList.map f := rfl
#align free_monoid.to_list_map FreeMonoid.toList_map

@[to_additive]
theorem ofList_map (f : α → β) (xs : List α) : ofList (xs.map f) = map f (ofList xs) := rfl
#align free_monoid.of_list_map FreeMonoid.ofList_map

@[to_additive]
theorem lift_of_comp_eq_map (f : α → β) : (lift fun x ↦ of (f x)) = map f := hom_eq fun _ ↦ rfl
#align free_monoid.lift_of_comp_eq_map FreeMonoid.lift_of_comp_eq_map

@[to_additive]
theorem map_comp (g : β → γ) (f : α → β) : map (g ∘ f) = (map g).comp (map f) := hom_eq fun _ ↦ rfl
#align free_monoid.map_comp FreeMonoid.map_comp

@[to_additive (attr := simp)]
theorem map_id : map (@id α) = MonoidHom.id (FreeMonoid α) := hom_eq fun _ ↦ rfl
#align free_monoid.map_id FreeMonoid.map_id

end FreeMonoid
