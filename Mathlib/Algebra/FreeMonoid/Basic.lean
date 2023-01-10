/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.free_monoid.basic
! leanprover-community/mathlib commit dd71334db81d0bd444af1ee339a29298bef40734
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.BigOperators.Basic

/-!
# Free monoid over a given alphabet

## Main definitions

* `free_monoid α`: free monoid over alphabet `α`; defined as a synonym for `list α`
  with multiplication given by `(++)`.
* `free_monoid.of`: embedding `α → free_monoid α` sending each element `x` to `[x]`;
* `free_monoid.lift`: natural equivalence between `α → M` and `free_monoid α →* M`
* `free_monoid.map`: embedding of `α → β` into `free_monoid α →* free_monoid β` given by `list.map`.
-/


variable {α : Type _} {β : Type _} {γ : Type _} {M : Type _} [Monoid M] {N : Type _} [Monoid N]

/-- Free monoid over a given alphabet. -/
@[to_additive "Free nonabelian additive monoid over a given alphabet"]
def FreeMonoid (α) :=
  List α
#align free_monoid FreeMonoid

namespace FreeMonoid

@[to_additive]
instance [DecidableEq α] : DecidableEq (FreeMonoid α) :=
  List.decidableEq

/-- The identity equivalence between `free_monoid α` and `list α`. -/
@[to_additive "The identity equivalence between `free_add_monoid α` and `list α`."]
def toList : FreeMonoid α ≃ List α :=
  Equiv.refl _
#align free_monoid.to_list FreeMonoid.toList

/-- The identity equivalence between `list α` and `free_monoid α`. -/
@[to_additive "The identity equivalence between `list α` and `free_add_monoid α`."]
def ofList : List α ≃ FreeMonoid α :=
  Equiv.refl _
#align free_monoid.of_list FreeMonoid.ofList

@[simp, to_additive]
theorem to_list_symm : (@toList α).symm = of_list :=
  rfl
#align free_monoid.to_list_symm FreeMonoid.to_list_symm

@[simp, to_additive]
theorem of_list_symm : (@ofList α).symm = to_list :=
  rfl
#align free_monoid.of_list_symm FreeMonoid.of_list_symm

@[simp, to_additive]
theorem to_list_of_list (l : List α) : toList (ofList l) = l :=
  rfl
#align free_monoid.to_list_of_list FreeMonoid.to_list_of_list

@[simp, to_additive]
theorem of_list_to_list (xs : FreeMonoid α) : ofList (toList xs) = xs :=
  rfl
#align free_monoid.of_list_to_list FreeMonoid.of_list_to_list

@[simp, to_additive]
theorem to_list_comp_of_list : @toList α ∘ of_list = id :=
  rfl
#align free_monoid.to_list_comp_of_list FreeMonoid.to_list_comp_of_list

@[simp, to_additive]
theorem of_list_comp_to_list : @ofList α ∘ to_list = id :=
  rfl
#align free_monoid.of_list_comp_to_list FreeMonoid.of_list_comp_to_list

@[to_additive]
instance : CancelMonoid (FreeMonoid α)
    where
  one := ofList []
  mul x y := ofList (x.toList ++ y.toList)
  mul_one := List.append_nil
  one_mul := List.nil_append
  mul_assoc := List.append_assoc
  mul_left_cancel _ _ _ := List.append_left_cancel
  mul_right_cancel _ _ _ := List.append_right_cancel

@[to_additive]
instance : Inhabited (FreeMonoid α) :=
  ⟨1⟩

@[simp, to_additive]
theorem to_list_one : (1 : FreeMonoid α).toList = [] :=
  rfl
#align free_monoid.to_list_one FreeMonoid.to_list_one

@[simp, to_additive]
theorem of_list_nil : ofList ([] : List α) = 1 :=
  rfl
#align free_monoid.of_list_nil FreeMonoid.of_list_nil

@[simp, to_additive]
theorem to_list_mul (xs ys : FreeMonoid α) : (xs * ys).toList = xs.toList ++ ys.toList :=
  rfl
#align free_monoid.to_list_mul FreeMonoid.to_list_mul

@[simp, to_additive]
theorem of_list_append (xs ys : List α) : ofList (xs ++ ys) = ofList xs * ofList ys :=
  rfl
#align free_monoid.of_list_append FreeMonoid.of_list_append

@[simp, to_additive]
theorem to_list_prod (xs : List (FreeMonoid α)) : toList xs.Prod = (xs.map toList).join := by
  induction xs <;> simp [*, List.join]
#align free_monoid.to_list_prod FreeMonoid.to_list_prod

@[simp, to_additive]
theorem of_list_join (xs : List (List α)) : ofList xs.join = (xs.map ofList).Prod :=
  toList.Injective <| by simp
#align free_monoid.of_list_join FreeMonoid.of_list_join

/-- Embeds an element of `α` into `free_monoid α` as a singleton list. -/
@[to_additive "Embeds an element of `α` into `free_add_monoid α` as a singleton list."]
def of (x : α) : FreeMonoid α :=
  ofList [x]
#align free_monoid.of FreeMonoid.of

@[simp, to_additive]
theorem to_list_of (x : α) : toList (of x) = [x] :=
  rfl
#align free_monoid.to_list_of FreeMonoid.to_list_of

@[to_additive]
theorem of_list_singleton (x : α) : ofList [x] = of x :=
  rfl
#align free_monoid.of_list_singleton FreeMonoid.of_list_singleton

@[simp, to_additive]
theorem of_list_cons (x : α) (xs : List α) : ofList (x :: xs) = of x * ofList xs :=
  rfl
#align free_monoid.of_list_cons FreeMonoid.of_list_cons

@[to_additive]
theorem to_list_of_mul (x : α) (xs : FreeMonoid α) : toList (of x * xs) = x :: xs.toList :=
  rfl
#align free_monoid.to_list_of_mul FreeMonoid.to_list_of_mul

@[to_additive]
theorem of_injective : Function.Injective (@of α) :=
  List.singleton_injective
#align free_monoid.of_injective FreeMonoid.of_injective

/-- Recursor for `free_monoid` using `1` and `free_monoid.of x * xs` instead of `[]` and
`x :: xs`. -/
@[elab_as_elim,
  to_additive
      "Recursor for `free_add_monoid` using `0` and `free_add_monoid.of x + xs` instead of `[]` and\n  `x :: xs`."]
def recOn {C : FreeMonoid α → Sort _} (xs : FreeMonoid α) (h0 : C 1)
    (ih : ∀ x xs, C xs → C (of x * xs)) : C xs :=
  List.recOn xs h0 ih
#align free_monoid.rec_on FreeMonoid.recOn

@[simp, to_additive]
theorem rec_on_one {C : FreeMonoid α → Sort _} (h0 : C 1) (ih : ∀ x xs, C xs → C (of x * xs)) :
    @recOn α C 1 h0 ih = h0 :=
  rfl
#align free_monoid.rec_on_one FreeMonoid.rec_on_one

@[simp, to_additive]
theorem rec_on_of_mul {C : FreeMonoid α → Sort _} (x : α) (xs : FreeMonoid α) (h0 : C 1)
    (ih : ∀ x xs, C xs → C (of x * xs)) : @recOn α C (of x * xs) h0 ih = ih x xs (recOn xs h0 ih) :=
  rfl
#align free_monoid.rec_on_of_mul FreeMonoid.rec_on_of_mul

/-- A version of `list.cases_on` for `free_monoid` using `1` and `free_monoid.of x * xs` instead of
`[]` and `x :: xs`. -/
@[elab_as_elim,
  to_additive
      "A version of `list.cases_on` for `free_add_monoid` using `0` and `free_add_monoid.of x + xs`\n  instead of `[]` and `x :: xs`."]
def casesOn {C : FreeMonoid α → Sort _} (xs : FreeMonoid α) (h0 : C 1)
    (ih : ∀ x xs, C (of x * xs)) : C xs :=
  List.casesOn xs h0 ih
#align free_monoid.cases_on FreeMonoid.casesOn

@[simp, to_additive]
theorem cases_on_one {C : FreeMonoid α → Sort _} (h0 : C 1) (ih : ∀ x xs, C (of x * xs)) :
    @casesOn α C 1 h0 ih = h0 :=
  rfl
#align free_monoid.cases_on_one FreeMonoid.cases_on_one

@[simp, to_additive]
theorem cases_on_of_mul {C : FreeMonoid α → Sort _} (x : α) (xs : FreeMonoid α) (h0 : C 1)
    (ih : ∀ x xs, C (of x * xs)) : @casesOn α C (of x * xs) h0 ih = ih x xs :=
  rfl
#align free_monoid.cases_on_of_mul FreeMonoid.cases_on_of_mul

@[ext, to_additive]
theorem hom_eq ⦃f g : FreeMonoid α →* M⦄ (h : ∀ x, f (of x) = g (of x)) : f = g :=
  MonoidHom.ext fun l =>
    (recOn l (f.map_one.trans g.map_one.symm)) fun x xs hxs => by
      simp only [h, hxs, MonoidHom.map_mul]
#align free_monoid.hom_eq FreeMonoid.hom_eq

/-- Equivalence between maps `α → M` and monoid homomorphisms `free_monoid α →* M`. -/
@[to_additive
      "Equivalence between maps `α → A` and additive monoid homomorphisms\n`free_add_monoid α →+ A`."]
def lift : (α → M) ≃ (FreeMonoid α →* M)
    where
  toFun f :=
    ⟨fun l => (l.toList.map f).Prod, rfl, fun l₁ l₂ => by
      simp only [to_list_mul, List.map_append, List.prod_append]⟩
  invFun f x := f (of x)
  left_inv f := funext fun x => one_mul (f x)
  right_inv f := hom_eq fun x => one_mul (f (of x))
#align free_monoid.lift FreeMonoid.lift

@[simp, to_additive]
theorem lift_symm_apply (f : FreeMonoid α →* M) : lift.symm f = f ∘ of :=
  rfl
#align free_monoid.lift_symm_apply FreeMonoid.lift_symm_apply

@[to_additive]
theorem lift_apply (f : α → M) (l : FreeMonoid α) : lift f l = (l.toList.map f).Prod :=
  rfl
#align free_monoid.lift_apply FreeMonoid.lift_apply

@[to_additive]
theorem lift_comp_of (f : α → M) : lift f ∘ of = f :=
  lift.symm_apply_apply f
#align free_monoid.lift_comp_of FreeMonoid.lift_comp_of

@[simp, to_additive]
theorem lift_eval_of (f : α → M) (x : α) : lift f (of x) = f x :=
  congr_fun (lift_comp_of f) x
#align free_monoid.lift_eval_of FreeMonoid.lift_eval_of

@[simp, to_additive]
theorem lift_restrict (f : FreeMonoid α →* M) : lift (f ∘ of) = f :=
  lift.apply_symm_apply f
#align free_monoid.lift_restrict FreeMonoid.lift_restrict

@[to_additive]
theorem comp_lift (g : M →* N) (f : α → M) : g.comp (lift f) = lift (g ∘ f) :=
  by
  ext
  simp
#align free_monoid.comp_lift FreeMonoid.comp_lift

@[to_additive]
theorem hom_map_lift (g : M →* N) (f : α → M) (x : FreeMonoid α) : g (lift f x) = lift (g ∘ f) x :=
  MonoidHom.ext_iff.1 (comp_lift g f) x
#align free_monoid.hom_map_lift FreeMonoid.hom_map_lift

/-- Define a multiplicative action of `free_monoid α` on `β`. -/
@[to_additive "Define an additive action of `free_add_monoid α` on `β`."]
def mkMulAction (f : α → β → β) : MulAction (FreeMonoid α) β
    where
  smul l b := l.toList.foldr f b
  one_smul x := rfl
  mul_smul xs ys b := List.foldr_append _ _ _ _
#align free_monoid.mk_mul_action FreeMonoid.mkMulAction

@[to_additive]
theorem smul_def (f : α → β → β) (l : FreeMonoid α) (b : β) :
    haveI := mk_mul_action f
    l • b = l.to_list.foldr f b :=
  rfl
#align free_monoid.smul_def FreeMonoid.smul_def

@[to_additive]
theorem of_list_smul (f : α → β → β) (l : List α) (b : β) :
    haveI := mk_mul_action f
    of_list l • b = l.foldr f b :=
  rfl
#align free_monoid.of_list_smul FreeMonoid.of_list_smul

@[simp, to_additive]
theorem of_smul (f : α → β → β) (x : α) (y : β) :
    (haveI := mk_mul_action f
      of x • y) =
      f x y :=
  rfl
#align free_monoid.of_smul FreeMonoid.of_smul

/-- The unique monoid homomorphism `free_monoid α →* free_monoid β` that sends
each `of x` to `of (f x)`. -/
@[to_additive
      "The unique additive monoid homomorphism `free_add_monoid α →+ free_add_monoid β`\nthat sends each `of x` to `of (f x)`."]
def map (f : α → β) : FreeMonoid α →* FreeMonoid β
    where
  toFun l := of_list <| l.toList.map f
  map_one' := rfl
  map_mul' l₁ l₂ := List.map_append _ _ _
#align free_monoid.map FreeMonoid.map

@[simp, to_additive]
theorem map_of (f : α → β) (x : α) : map f (of x) = of (f x) :=
  rfl
#align free_monoid.map_of FreeMonoid.map_of

@[to_additive]
theorem to_list_map (f : α → β) (xs : FreeMonoid α) : (map f xs).toList = xs.toList.map f :=
  rfl
#align free_monoid.to_list_map FreeMonoid.to_list_map

@[to_additive]
theorem of_list_map (f : α → β) (xs : List α) : ofList (xs.map f) = map f (ofList xs) :=
  rfl
#align free_monoid.of_list_map FreeMonoid.of_list_map

@[to_additive]
theorem lift_of_comp_eq_map (f : α → β) : (lift fun x => of (f x)) = map f :=
  hom_eq fun x => rfl
#align free_monoid.lift_of_comp_eq_map FreeMonoid.lift_of_comp_eq_map

@[to_additive]
theorem map_comp (g : β → γ) (f : α → β) : map (g ∘ f) = (map g).comp (map f) :=
  hom_eq fun x => rfl
#align free_monoid.map_comp FreeMonoid.map_comp

@[simp, to_additive]
theorem map_id : map (@id α) = MonoidHom.id (FreeMonoid α) :=
  hom_eq fun x => rfl
#align free_monoid.map_id FreeMonoid.map_id

end FreeMonoid

