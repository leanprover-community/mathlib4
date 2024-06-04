/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Yury Kudryashov
-/
import Mathlib.Algebra.BigOperators.Group.List
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Data.Finset.Basic


#align_import algebra.free_monoid.basic from "leanprover-community/mathlib"@"657df4339ae6ceada048c8a2980fb10e393143ec"

/-!
# Free monoid over a given alphabet

## Main definitions

* `FreeMonoid α`: free monoid over alphabet `α`; defined as a synonym for `List α`
  with multiplication given by `(++)`.
* `FreeMonoid.of`: embedding `α → FreeMonoid α` sending each element `x` to `[x]`;
* `FreeMonoid.lift`: natural equivalence between `α → M` and `FreeMonoid α →* M`
* `FreeMonoid.map`: embedding of `α → β` into `FreeMonoid α →* FreeMonoid β` given by `List.map`.
-/


variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

/-- Free monoid over a given alphabet. -/
@[to_additive "Free nonabelian additive monoid over a given alphabet"]
def FreeMonoid (α) := List α
#align free_monoid FreeMonoid
#align free_add_monoid FreeAddMonoid

namespace FreeMonoid

/-- The identity equivalence between `FreeMonoid α` and `List α`. -/
@[to_additive "The identity equivalence between `FreeAddMonoid α` and `List α`."]
def toList : FreeMonoid α ≃ List α := Equiv.refl _
#align free_monoid.to_list FreeMonoid.toList
#align free_add_monoid.to_list FreeAddMonoid.toList

/-- The identity equivalence between `List α` and `FreeMonoid α`. -/
@[to_additive "The identity equivalence between `List α` and `FreeAddMonoid α`."]
def ofList : List α ≃ FreeMonoid α := Equiv.refl _
#align free_monoid.of_list FreeMonoid.ofList
#align free_add_monoid.of_list FreeAddMonoid.ofList

@[to_additive (attr := simp)]
theorem toList_symm : (@toList α).symm = ofList := rfl
#align free_monoid.to_list_symm FreeMonoid.toList_symm
#align free_add_monoid.to_list_symm FreeAddMonoid.toList_symm

@[to_additive (attr := simp)]
theorem ofList_symm : (@ofList α).symm = toList := rfl
#align free_monoid.of_list_symm FreeMonoid.ofList_symm
#align free_add_monoid.of_list_symm FreeAddMonoid.ofList_symm

@[to_additive (attr := simp)]
theorem toList_ofList (l : List α) : toList (ofList l) = l := rfl
#align free_monoid.to_list_of_list FreeMonoid.toList_ofList
#align free_add_monoid.to_list_of_list FreeAddMonoid.toList_ofList

@[to_additive (attr := simp)]
theorem ofList_toList (xs : FreeMonoid α) : ofList (toList xs) = xs := rfl
#align free_monoid.of_list_to_list FreeMonoid.ofList_toList
#align free_add_monoid.of_list_to_list FreeAddMonoid.ofList_toList

@[to_additive (attr := simp)]
theorem toList_comp_ofList : @toList α ∘ ofList = id := rfl
#align free_monoid.to_list_comp_of_list FreeMonoid.toList_comp_ofList
#align free_add_monoid.to_list_comp_of_list FreeAddMonoid.toList_comp_ofList

@[to_additive (attr := simp)]
theorem ofList_comp_toList : @ofList α ∘ toList = id := rfl
#align free_monoid.of_list_comp_to_list FreeMonoid.ofList_comp_toList
#align free_add_monoid.of_list_comp_to_list FreeAddMonoid.ofList_comp_toList

@[to_additive]
instance : CancelMonoid (FreeMonoid α) where
  one := ofList []
  mul x y := ofList (toList x ++ toList y)
  mul_one := List.append_nil
  one_mul := List.nil_append
  mul_assoc := List.append_assoc
  mul_left_cancel _ _ _ := List.append_cancel_left
  mul_right_cancel _ _ _ := List.append_cancel_right

@[to_additive]
instance : Inhabited (FreeMonoid α) := ⟨1⟩

@[to_additive (attr := simp)]
theorem toList_one : toList (1 : FreeMonoid α) = [] := rfl
#align free_monoid.to_list_one FreeMonoid.toList_one
#align free_add_monoid.to_list_zero FreeAddMonoid.toList_zero

@[to_additive (attr := simp)]
theorem ofList_nil : ofList ([] : List α) = 1 := rfl
#align free_monoid.of_list_nil FreeMonoid.ofList_nil
#align free_add_monoid.of_list_nil FreeAddMonoid.ofList_nil

@[to_additive (attr := simp)]
theorem toList_mul (xs ys : FreeMonoid α) : toList (xs * ys) = toList xs ++ toList ys := rfl
#align free_monoid.to_list_mul FreeMonoid.toList_mul
#align free_add_monoid.to_list_add FreeAddMonoid.toList_add

@[to_additive (attr := simp)]
theorem ofList_append (xs ys : List α) : ofList (xs ++ ys) = ofList xs * ofList ys := rfl
#align free_monoid.of_list_append FreeMonoid.ofList_append
#align free_add_monoid.of_list_append FreeAddMonoid.ofList_append

@[to_additive (attr := simp)]
theorem toList_prod (xs : List (FreeMonoid α)) : toList xs.prod = (xs.map toList).join := by
  induction xs <;> simp [*, List.join]
#align free_monoid.to_list_prod FreeMonoid.toList_prod
#align free_add_monoid.to_list_sum FreeAddMonoid.toList_sum

@[to_additive (attr := simp)]
theorem ofList_join (xs : List (List α)) : ofList xs.join = (xs.map ofList).prod :=
  toList.injective <| by simp
#align free_monoid.of_list_join FreeMonoid.ofList_join
#align free_add_monoid.of_list_join FreeAddMonoid.ofList_join

/-- Embeds an element of `α` into `FreeMonoid α` as a singleton list. -/
@[to_additive "Embeds an element of `α` into `FreeAddMonoid α` as a singleton list."]
def of (x : α) : FreeMonoid α := ofList [x]
#align free_monoid.of FreeMonoid.of
#align free_add_monoid.of FreeAddMonoid.of

@[to_additive (attr := simp)]
theorem toList_of (x : α) : toList (of x) = [x] := rfl
#align free_monoid.to_list_of FreeMonoid.toList_of
#align free_add_monoid.to_list_of FreeAddMonoid.toList_of

@[to_additive]
theorem ofList_singleton (x : α) : ofList [x] = of x := rfl
#align free_monoid.of_list_singleton FreeMonoid.ofList_singleton
#align free_add_monoid.of_list_singleton FreeAddMonoid.ofList_singleton

@[to_additive (attr := simp)]
theorem ofList_cons (x : α) (xs : List α) : ofList (x :: xs) = of x * ofList xs := rfl
#align free_monoid.of_list_cons FreeMonoid.ofList_cons
#align free_add_monoid.of_list_cons FreeAddMonoid.ofList_cons

@[to_additive]
theorem toList_of_mul (x : α) (xs : FreeMonoid α) : toList (of x * xs) = x :: toList xs := rfl
#align free_monoid.to_list_of_mul FreeMonoid.toList_of_mul
#align free_add_monoid.to_list_of_add FreeAddMonoid.toList_of_add

@[to_additive]
theorem of_injective : Function.Injective (@of α) := List.singleton_injective
#align free_monoid.of_injective FreeMonoid.of_injective
#align free_add_monoid.of_injective FreeAddMonoid.of_injective

/-! ### length -/

section Length
variable {a : FreeMonoid α}

/-- the length of a free monoid element: 1.length = 0 and (a * b).length = a.length + b.length -/
@[to_additive "the length of a additive free monoid element: 1.length = 0 and (a * b).length =
  a.length + b.length"]
def length (a : FreeMonoid α) : ℕ := List.length a

@[to_additive (attr := simp)]
theorem length_one : length (1 : FreeMonoid α) = 0 := rfl

@[to_additive]
theorem eq_one_of_length_eq_zero (h : length a = 0) : a = 1 :=
  List.eq_nil_of_length_eq_zero h

@[to_additive (attr := simp)]
theorem length_of {m : α}: length (of m) = 1 := rfl

@[to_additive]
theorem length_eq_one : length a = 1 ↔ ∃ m, a = FreeMonoid.of m := List.length_eq_one

@[to_additive (attr := simp)]
theorem length_mul (a b : FreeMonoid α) : (a * b).length = a.length + b.length :=
  List.length_append _ _

end Length

/-! ### symbols -/

section Symbols
variable [DecidableEq α]

/-- the set of unique symbols in a free monoid element -/
@[to_additive "the set of unique symbols in an additive free monoid element"]
def symbols (a : FreeMonoid α) : Finset α := List.toFinset a

@[to_additive (attr := simp)]
theorem symbols_one : symbols (1 : FreeMonoid α) = ∅ := rfl

@[to_additive (attr := simp)]
theorem symbols_of {m : α} : symbols (of m : FreeMonoid α) = {m} := rfl

@[to_additive (attr := simp)]
theorem symbols_mul {a b : FreeMonoid α} : symbols (a * b : FreeMonoid α) =
    (symbols a) ∪ (symbols b) := by
  simp only [symbols, List.mem_toFinset, Finset.mem_union]
  apply List.toFinset_append

end Symbols

/-! ### mem -/

section mem
variable {m : α}

/-- membership in a free monoid element -/
@[to_additive "membership in a free monoid element"]
def mem (m : α) (a : FreeMonoid α) := m ∈ toList a

@[to_additive]
instance : Membership α (FreeMonoid α) := ⟨mem⟩

@[to_additive]
theorem mem_one_iff : m ∈ (1 : FreeMonoid α) ↔ False := List.mem_nil_iff _

@[to_additive (attr := simp)]
theorem mem_of {n : α} : m ∈ (of n) ↔ m = n := List.mem_singleton

@[to_additive]
theorem mem_of_self : m ∈ of m := List.mem_singleton_self _

@[to_additive (attr := simp)]
theorem mem_mul {a b : FreeMonoid α} : m ∈ (a * b) ↔ m ∈ a ∨ m ∈ b := List.mem_append

@[to_additive (attr := simp)]
theorem mem_symbols [DecidableEq α] {a : FreeMonoid α}: m ∈ FreeMonoid.symbols a ↔ m ∈ a :=
  List.mem_toFinset

end mem

/-- Recursor for `FreeMonoid` using `1` and `FreeMonoid.of x * xs` instead of `[]` and `x :: xs`. -/
@[to_additive (attr := elab_as_elim) "Recursor for `FreeAddMonoid` using `0` and
`FreeAddMonoid.of x + xs` instead of `[]` and `x :: xs`."]
-- Porting note: change from `List.recOn` to `List.rec` since only the latter is computable
def recOn {C : FreeMonoid α → Sort*} (xs : FreeMonoid α) (h0 : C 1)
    (ih : ∀ x xs, C xs → C (of x * xs)) : C xs := List.rec h0 ih xs
#align free_monoid.rec_on FreeMonoid.recOn
#align free_add_monoid.rec_on FreeAddMonoid.recOn

@[to_additive (attr := simp)]
theorem recOn_one {C : FreeMonoid α → Sort*} (h0 : C 1) (ih : ∀ x xs, C xs → C (of x * xs)) :
    @recOn α C 1 h0 ih = h0 := rfl
#align free_monoid.rec_on_one FreeMonoid.recOn_one
#align free_add_monoid.rec_on_zero FreeAddMonoid.recOn_zero

@[to_additive (attr := simp)]
theorem recOn_of_mul {C : FreeMonoid α → Sort*} (x : α) (xs : FreeMonoid α) (h0 : C 1)
    (ih : ∀ x xs, C xs → C (of x * xs)) : @recOn α C (of x * xs) h0 ih = ih x xs (recOn xs h0 ih) :=
  rfl
#align free_monoid.rec_on_of_mul FreeMonoid.recOn_of_mul
#align free_add_monoid.rec_on_of_add FreeAddMonoid.recOn_of_add

/-! ### induction -/
section induction_principles

/-- an induction principle on free monoids, with cases for one, ofs, and multiplication -/
@[to_additive (attr := elab_as_elim, induction_eliminator)]
protected theorem inductionOn {C : FreeMonoid α → Prop} (z : FreeMonoid α) (one : C 1)
    (of : ∀ (x : α), C (FreeMonoid.of x)) (mul : ∀ (x y : FreeMonoid α), C x → C y → C (x * y)) :
  C z := List.rec one (fun _ _ ih => mul [_] _ (of _) ih) z

/-- an induction principle for free monoids more closely mirroring induction on lists -/
@[to_additive (attr := elab_as_elim)]
protected theorem inductionOn' {p : FreeMonoid α → Prop} (a : FreeMonoid α)
    (one : p (1 : FreeMonoid α)) (mul_of : ∀ b a, p a → p (of b * a)) : p a :=
  List.rec one (fun _ _ tail_ih => mul_of _ _ tail_ih) a

end induction_principles

@[to_additive]
theorem eq_one_or_has_last_elem (u : FreeMonoid α): u = 1 ∨ ∃ front last, u = front * of last :=
  List.eq_nil_or_concat _

/-- A version of `List.cases_on` for `FreeMonoid` using `1` and `FreeMonoid.of x * xs` instead of
`[]` and `x :: xs`. -/
@[to_additive (attr := elab_as_elim) "A version of `List.casesOn` for `FreeAddMonoid` using `0` and
`FreeAddMonoid.of x + xs` instead of `[]` and `x :: xs`."]
def casesOn {C : FreeMonoid α → Sort*} (xs : FreeMonoid α) (h0 : C 1)
    (ih : ∀ x xs, C (of x * xs)) : C xs := List.casesOn xs h0 ih
#align free_monoid.cases_on FreeMonoid.casesOn
#align free_add_monoid.cases_on FreeAddMonoid.casesOn

@[to_additive (attr := simp)]
theorem casesOn_one {C : FreeMonoid α → Sort*} (h0 : C 1) (ih : ∀ x xs, C (of x * xs)) :
    @casesOn α C 1 h0 ih = h0 := rfl
#align free_monoid.cases_on_one FreeMonoid.casesOn_one
#align free_add_monoid.cases_on_zero FreeAddMonoid.casesOn_zero

@[to_additive (attr := simp)]
theorem casesOn_of_mul {C : FreeMonoid α → Sort*} (x : α) (xs : FreeMonoid α) (h0 : C 1)
    (ih : ∀ x xs, C (of x * xs)) : @casesOn α C (of x * xs) h0 ih = ih x xs := rfl
#align free_monoid.cases_on_of_mul FreeMonoid.casesOn_of_mul
#align free_add_monoid.cases_on_of_add FreeAddMonoid.casesOn_of_add

@[to_additive (attr := ext)]
theorem hom_eq ⦃f g : FreeMonoid α →* M⦄ (h : ∀ x, f (of x) = g (of x)) : f = g :=
  MonoidHom.ext fun l ↦ recOn l (f.map_one.trans g.map_one.symm)
    (fun x xs hxs ↦ by simp only [h, hxs, MonoidHom.map_mul])
#align free_monoid.hom_eq FreeMonoid.hom_eq
#align free_add_monoid.hom_eq FreeAddMonoid.hom_eq

/-- A variant of `List.prod` that has `[x].prod = x` true definitionally.
The purpose is to make `FreeMonoid.lift_eval_of` true by `rfl`. -/
@[to_additive "A variant of `List.sum` that has `[x].sum = x` true definitionally.
The purpose is to make `FreeAddMonoid.lift_eval_of` true by `rfl`."]
def prodAux {M} [Monoid M] : List M → M
  | [] => 1
  | (x :: xs) => List.foldl (· * ·) x xs
#align free_monoid.prod_aux FreeMonoid.prodAux
#align free_add_monoid.sum_aux FreeAddMonoid.sumAux

@[to_additive]
lemma prodAux_eq : ∀ l : List M, FreeMonoid.prodAux l = l.prod
  | [] => rfl
  | (_ :: xs) => congr_arg (fun x => List.foldl (· * ·) x xs) (one_mul _).symm
#align free_monoid.prod_aux_eq FreeMonoid.prodAux_eq
#align free_add_monoid.sum_aux_eq FreeAddMonoid.sumAux_eq

/-- Equivalence between maps `α → M` and monoid homomorphisms `FreeMonoid α →* M`. -/
@[to_additive "Equivalence between maps `α → A` and additive monoid homomorphisms
`FreeAddMonoid α →+ A`."]
def lift : (α → M) ≃ (FreeMonoid α →* M) where
  toFun f :=
  { toFun := fun l ↦ prodAux ((toList l).map f)
    map_one' := rfl
    map_mul' := fun _ _ ↦ by simp only [prodAux_eq, toList_mul, List.map_append, List.prod_append]}
  invFun f x := f (of x)
  left_inv f := rfl
  right_inv f := hom_eq fun x ↦ rfl
#align free_monoid.lift FreeMonoid.lift
#align free_add_monoid.lift FreeAddMonoid.lift

-- Porting note (#10756): new theorem
@[to_additive (attr := simp)]
theorem lift_ofList (f : α → M) (l : List α) : lift f (ofList l) = (l.map f).prod :=
  prodAux_eq _

@[to_additive (attr := simp)]
theorem lift_symm_apply (f : FreeMonoid α →* M) : lift.symm f = f ∘ of := rfl
#align free_monoid.lift_symm_apply FreeMonoid.lift_symm_apply
#align free_add_monoid.lift_symm_apply FreeAddMonoid.lift_symm_apply

@[to_additive]
theorem lift_apply (f : α → M) (l : FreeMonoid α) : lift f l = ((toList l).map f).prod :=
  prodAux_eq _
#align free_monoid.lift_apply FreeMonoid.lift_apply
#align free_add_monoid.lift_apply FreeAddMonoid.lift_apply

@[to_additive]
theorem lift_comp_of (f : α → M) : lift f ∘ of = f := rfl
#align free_monoid.lift_comp_of FreeMonoid.lift_comp_of
#align free_add_monoid.lift_comp_of FreeAddMonoid.lift_comp_of

@[to_additive (attr := simp)]
theorem lift_eval_of (f : α → M) (x : α) : lift f (of x) = f x := rfl
#align free_monoid.lift_eval_of FreeMonoid.lift_eval_of
#align free_add_monoid.lift_eval_of FreeAddMonoid.lift_eval_of

@[to_additive (attr := simp)]
theorem lift_restrict (f : FreeMonoid α →* M) : lift (f ∘ of) = f := lift.apply_symm_apply f
#align free_monoid.lift_restrict FreeMonoid.lift_restrict
#align free_add_monoid.lift_restrict FreeAddMonoid.lift_restrict

@[to_additive]
theorem comp_lift (g : M →* N) (f : α → M) : g.comp (lift f) = lift (g ∘ f) := by
  ext
  simp
#align free_monoid.comp_lift FreeMonoid.comp_lift
#align free_add_monoid.comp_lift FreeAddMonoid.comp_lift

@[to_additive]
theorem hom_map_lift (g : M →* N) (f : α → M) (x : FreeMonoid α) : g (lift f x) = lift (g ∘ f) x :=
  DFunLike.ext_iff.1 (comp_lift g f) x
#align free_monoid.hom_map_lift FreeMonoid.hom_map_lift
#align free_add_monoid.hom_map_lift FreeAddMonoid.hom_map_lift

/-- Define a multiplicative action of `FreeMonoid α` on `β`. -/
@[to_additive "Define an additive action of `FreeAddMonoid α` on `β`."]
def mkMulAction (f : α → β → β) : MulAction (FreeMonoid α) β where
  smul l b := l.toList.foldr f b
  one_smul _ := rfl
  mul_smul _ _ _ := List.foldr_append _ _ _ _
#align free_monoid.mk_mul_action FreeMonoid.mkMulAction
#align free_add_monoid.mk_add_action FreeAddMonoid.mkAddAction

@[to_additive]
theorem smul_def (f : α → β → β) (l : FreeMonoid α) (b : β) :
    haveI := mkMulAction f
    l • b = l.toList.foldr f b := rfl
#align free_monoid.smul_def FreeMonoid.smul_def
#align free_add_monoid.vadd_def FreeAddMonoid.vadd_def

@[to_additive]
theorem ofList_smul (f : α → β → β) (l : List α) (b : β) :
    haveI := mkMulAction f
    ofList l • b = l.foldr f b := rfl
#align free_monoid.of_list_smul FreeMonoid.ofList_smul
#align free_add_monoid.of_list_vadd FreeAddMonoid.ofList_vadd

@[to_additive (attr := simp)]
theorem of_smul (f : α → β → β) (x : α) (y : β) :
    (haveI := mkMulAction f
    of x • y) = f x y := rfl
#align free_monoid.of_smul FreeMonoid.of_smul
#align free_add_monoid.of_vadd FreeAddMonoid.of_vadd

/-! ### map -/

section Map
variable {f : α → β} { a b : FreeMonoid α}
/-- The unique monoid homomorphism `FreeMonoid α →* FreeMonoid β` that sends
each `of x` to `of (f x)`. -/
@[to_additive "The unique additive monoid homomorphism `FreeAddMonoid α →+ FreeAddMonoid β`
that sends each `of x` to `of (f x)`."]
def map (f : α → β) : FreeMonoid α →* FreeMonoid β where
  toFun l := ofList <| l.toList.map f
  map_one' := rfl
  map_mul' _ _ := List.map_append _ _ _
#align free_monoid.map FreeMonoid.map
#align free_add_monoid.map FreeAddMonoid.map

-- @[to_additive (attr := simp)]
-- theorem map_one : map f 1 = 1 := rfl

@[to_additive (attr := simp)]
theorem map_of (f : α → β) (x : α) : map f (of x) = of (f x) := rfl
#align free_monoid.map_of FreeMonoid.map_of
#align free_add_monoid.map_of FreeAddMonoid.map_of

-- @[to_additive (attr := simp)]
-- theorem map_mul : map f (a * b) = map f a * map f b := MonoidHom.map_mul (map f) a b

@[to_additive (attr := simp)]
theorem mem_map {m : β} : m ∈ map f a ↔ ∃ n ∈ a, f n = m := List.mem_map

@[to_additive]
theorem map_map {α₁ : Type*} {g : α₁ → α} {x : FreeMonoid α₁} :
    map f (map g x) = map (f ∘ g) x := by
  unfold map
  simp [MonoidHom.comp_apply]

@[to_additive]
theorem toList_map (f : α → β) (xs : FreeMonoid α) : toList (map f xs) = xs.toList.map f := rfl
#align free_monoid.to_list_map FreeMonoid.toList_map
#align free_add_monoid.to_list_map FreeAddMonoid.toList_map

@[to_additive]
theorem ofList_map (f : α → β) (xs : List α) : ofList (xs.map f) = map f (ofList xs) := rfl
#align free_monoid.of_list_map FreeMonoid.ofList_map
#align free_add_monoid.of_list_map FreeAddMonoid.ofList_map

@[to_additive]
theorem lift_of_comp_eq_map (f : α → β) : (lift fun x ↦ of (f x)) = map f := hom_eq fun _ ↦ rfl
#align free_monoid.lift_of_comp_eq_map FreeMonoid.lift_of_comp_eq_map
#align free_add_monoid.lift_of_comp_eq_map FreeAddMonoid.lift_of_comp_eq_map

@[to_additive]
theorem map_comp (g : β → γ) (f : α → β) : map (g ∘ f) = (map g).comp (map f) := hom_eq fun _ ↦ rfl
#align free_monoid.map_comp FreeMonoid.map_comp
#align free_add_monoid.map_comp FreeAddMonoid.map_comp

@[to_additive (attr := simp)]
theorem map_id : map (@id α) = MonoidHom.id (FreeMonoid α) := hom_eq fun _ ↦ rfl
#align free_monoid.map_id FreeMonoid.map_id
#align free_add_monoid.map_id FreeAddMonoid.map_id

theorem map_surjective (f : α → β) : Function.Surjective f → Function.Surjective (map f) := by
  intro fs d
  induction' d using FreeMonoid.inductionOn' with head tail ih
  · use 1
    rfl
  specialize fs head
  rcases fs with ⟨thingie, rfl⟩
  rcases ih with ⟨another, rfl⟩
  use FreeMonoid.of thingie * another
  rfl

end Map

/-! ### reverse -/

/-- reverses the symbols in a free monoid element -/
@[to_additive "reverses the symbols in an additive free monoid element"]
def reverse : FreeMonoid α → FreeMonoid α := List.reverse

@[to_additive (attr := simp)]
theorem reverse_mul {a b : FreeMonoid α} : reverse (a * b) = reverse b * reverse a :=
  List.reverse_append _ _


/-! ### foldr -/

/--
Applies function `f` to all of the elements of the free monoid, from right to left.
* `foldr f init (of a * of b * of c) = f a <| f b <| f c <| init
-/
@[to_additive (attr := specialize) "Applies function `f` to all of the elements of the free monoid,
from right to left. `foldr f init (of a + of b + of c) = f a <| f b <| f c <| init"]
def foldr (f : α → α → α) (init : α) (a : FreeMonoid α) := List.foldr f init a

@[to_additive (attr := simp)]
theorem foldr_one f (init : α) : foldr f init 1 = init := rfl

@[to_additive (attr := simp)]
theorem foldr_of f (init first : α) : foldr f init (of first) = f first init := rfl

@[to_additive (attr := simp)]
theorem foldr_mul_of f (init first : α) (a : FreeMonoid α) :
    foldr f init (of first * a) = f first (foldr f init a) := rfl

/-- The only invertible element of the free monoid is 1; this instance enables `units_eq_one`. -/
@[to_additive]
instance uniqueUnits : Unique (FreeMonoid α)ˣ where
  uniq u := Units.ext <| toList.injective <|
    have : toList u.val ++ toList u.inv = [] := DFunLike.congr_arg toList u.val_inv
    (List.append_eq_nil.mp this).1

/-- if two types are isomorphic, the free monoids over those types are isomorphic -/
@[to_additive "if two types are isomorphic, the additive free monoids over those types are
isomorphic"]
def congr_iso {α : Type u_1} {β : Type u_2} (e : α ≃ β) : FreeMonoid α ≃* FreeMonoid β := by
  apply MulEquiv.mk' ⟨FreeMonoid.map e.toFun, FreeMonoid.map e.invFun, _, _⟩
  · simp
  all_goals
  intro x
  simp [map_map]

/-- given an isomorphism between α and β, convert a relation predicate to
have an underlying type of β -/
@[to_additive "given an isomorphism between α and β, convert a relation predicate to
have an underlying type of β"]
def map_rel (e : α ≃ β) (rel : FreeMonoid α → FreeMonoid α → Prop) :
    FreeMonoid β → FreeMonoid β  → Prop :=
  fun a b ↦ rel (FreeMonoid.congr_iso e.symm a) (FreeMonoid.congr_iso e.symm b)

/-- given an isomorphism between α and β, pull back a relation predicate with underlying type β to
one with underlying type α -/
@[to_additive "given an isomorphism between α and β, pull back a relation predicate with underlying
type β to one with underlying type α "]
def comap_rel (e : α ≃ β) (rel : FreeMonoid β → FreeMonoid β → Prop) :
    FreeMonoid α → FreeMonoid α → Prop :=
  fun a b ↦ rel (FreeMonoid.congr_iso e a) (FreeMonoid.congr_iso e b)


end FreeMonoid
