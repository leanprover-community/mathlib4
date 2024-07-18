/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Simon Hudon
-/
import Mathlib.Data.Fin.Fin2
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Common

#align_import data.typevec from "leanprover-community/mathlib"@"48fb5b5280e7c81672afc9524185ae994553ebf4"

/-!

# Tuples of types, and their categorical structure.

## Features

* `TypeVec n` - n-tuples of types
* `α ⟹ β`    - n-tuples of maps
* `f ⊚ g`     - composition

Also, support functions for operating with n-tuples of types, such as:

* `append1 α β`    - append type `β` to n-tuple `α` to obtain an (n+1)-tuple
* `drop α`         - drops the last element of an (n+1)-tuple
* `last α`         - returns the last element of an (n+1)-tuple
* `appendFun f g` - appends a function g to an n-tuple of functions
* `dropFun f`     - drops the last function from an n+1-tuple
* `lastFun f`     - returns the last function of a tuple.

Since e.g. `append1 α.drop α.last` is propositionally equal to `α` but not definitionally equal
to it, we need support functions and lemmas to mediate between constructions.
-/

universe u v w

/-- n-tuples of types, as a category -/
@[pp_with_univ]
def TypeVec (n : ℕ) :=
  Fin2 n → Type*
#align typevec TypeVec

instance {n} : Inhabited (TypeVec.{u} n) :=
  ⟨fun _ => PUnit⟩

namespace TypeVec

variable {n : ℕ}

/-- arrow in the category of `TypeVec` -/
def Arrow (α β : TypeVec n) :=
  ∀ i : Fin2 n, α i → β i
#align typevec.arrow TypeVec.Arrow

@[inherit_doc] scoped[MvFunctor] infixl:40 " ⟹ " => TypeVec.Arrow
open MvFunctor

/-- Extensionality for arrows -/
@[ext]
theorem Arrow.ext {α β : TypeVec n} (f g : α ⟹ β) :
    (∀ i, f i = g i) → f = g := by
  intro h; funext i; apply h

instance Arrow.inhabited (α β : TypeVec n) [∀ i, Inhabited (β i)] : Inhabited (α ⟹ β) :=
  ⟨fun _ _ => default⟩
#align typevec.arrow.inhabited TypeVec.Arrow.inhabited

/-- identity of arrow composition -/
def id {α : TypeVec n} : α ⟹ α := fun _ x => x
#align typevec.id TypeVec.id

/-- arrow composition in the category of `TypeVec` -/
def comp {α β γ : TypeVec n} (g : β ⟹ γ) (f : α ⟹ β) : α ⟹ γ := fun i x => g i (f i x)
#align typevec.comp TypeVec.comp

@[inherit_doc] scoped[MvFunctor] infixr:80 " ⊚ " => TypeVec.comp -- type as \oo

@[simp]
theorem id_comp {α β : TypeVec n} (f : α ⟹ β) : id ⊚ f = f :=
  rfl
#align typevec.id_comp TypeVec.id_comp

@[simp]
theorem comp_id {α β : TypeVec n} (f : α ⟹ β) : f ⊚ id = f :=
  rfl
#align typevec.comp_id TypeVec.comp_id

theorem comp_assoc {α β γ δ : TypeVec n} (h : γ ⟹ δ) (g : β ⟹ γ) (f : α ⟹ β) :
    (h ⊚ g) ⊚ f = h ⊚ g ⊚ f :=
  rfl
#align typevec.comp_assoc TypeVec.comp_assoc

/-- Support for extending a `TypeVec` by one element. -/
def append1 (α : TypeVec n) (β : Type*) : TypeVec (n + 1)
  | Fin2.fs i => α i
  | Fin2.fz => β
#align typevec.append1 TypeVec.append1

@[inherit_doc] infixl:67 " ::: " => append1

/-- retain only a `n-length` prefix of the argument -/
def drop (α : TypeVec.{u} (n + 1)) : TypeVec n := fun i => α i.fs
#align typevec.drop TypeVec.drop

/-- take the last value of a `(n+1)-length` vector -/
def last (α : TypeVec.{u} (n + 1)) : Type _ :=
  α Fin2.fz
#align typevec.last TypeVec.last

instance last.inhabited (α : TypeVec (n + 1)) [Inhabited (α Fin2.fz)] : Inhabited (last α) :=
  ⟨show α Fin2.fz from default⟩
#align typevec.last.inhabited TypeVec.last.inhabited

theorem drop_append1 {α : TypeVec n} {β : Type*} {i : Fin2 n} : drop (append1 α β) i = α i :=
  rfl
#align typevec.drop_append1 TypeVec.drop_append1

theorem drop_append1' {α : TypeVec n} {β : Type*} : drop (append1 α β) = α :=
  funext fun _ => drop_append1
#align typevec.drop_append1' TypeVec.drop_append1'

theorem last_append1 {α : TypeVec n} {β : Type*} : last (append1 α β) = β :=
  rfl
#align typevec.last_append1 TypeVec.last_append1

@[simp]
theorem append1_drop_last (α : TypeVec (n + 1)) : append1 (drop α) (last α) = α :=
  funext fun i => by cases i <;> rfl
#align typevec.append1_drop_last TypeVec.append1_drop_last

/-- cases on `(n+1)-length` vectors -/
@[elab_as_elim]
def append1Cases {C : TypeVec (n + 1) → Sort u} (H : ∀ α β, C (append1 α β)) (γ) : C γ := by
  rw [← @append1_drop_last _ γ]; apply H
#align typevec.append1_cases TypeVec.append1Cases

@[simp]
theorem append1_cases_append1 {C : TypeVec (n + 1) → Sort u} (H : ∀ α β, C (append1 α β)) (α β) :
    @append1Cases _ C H (append1 α β) = H α β :=
  rfl
#align typevec.append1_cases_append1 TypeVec.append1_cases_append1

/-- append an arrow and a function for arbitrary source and target type vectors -/
def splitFun {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last α → last α') : α ⟹ α'
  | Fin2.fs i => f i
  | Fin2.fz => g
#align typevec.split_fun TypeVec.splitFun

/-- append an arrow and a function as well as their respective source and target types / typevecs -/
def appendFun {α α' : TypeVec n} {β β' : Type*} (f : α ⟹ α') (g : β → β') :
    append1 α β ⟹ append1 α' β' :=
  splitFun f g
#align typevec.append_fun TypeVec.appendFun

@[inherit_doc] infixl:0 " ::: " => appendFun

/-- split off the prefix of an arrow -/
def dropFun {α β : TypeVec (n + 1)} (f : α ⟹ β) : drop α ⟹ drop β := fun i => f i.fs
#align typevec.drop_fun TypeVec.dropFun

/-- split off the last function of an arrow -/
def lastFun {α β : TypeVec (n + 1)} (f : α ⟹ β) : last α → last β :=
  f Fin2.fz
#align typevec.last_fun TypeVec.lastFun

-- Porting note: Lean wasn't able to infer the motive in term mode
/-- arrow in the category of `0-length` vectors -/
def nilFun {α : TypeVec 0} {β : TypeVec 0} : α ⟹ β := fun i => by apply Fin2.elim0 i
#align typevec.nil_fun TypeVec.nilFun

theorem eq_of_drop_last_eq {α β : TypeVec (n + 1)} {f g : α ⟹ β} (h₀ : dropFun f = dropFun g)
    (h₁ : lastFun f = lastFun g) : f = g := by
  -- Porting note: FIXME: congr_fun h₀ <;> ext1 ⟨⟩ <;> apply_assumption
  refine funext (fun x => ?_)
  cases x
  · apply h₁
  · apply congr_fun h₀
#align typevec.eq_of_drop_last_eq TypeVec.eq_of_drop_last_eq

@[simp]
theorem dropFun_splitFun {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last α → last α') :
    dropFun (splitFun f g) = f :=
  rfl
#align typevec.drop_fun_split_fun TypeVec.dropFun_splitFun

/-- turn an equality into an arrow -/
def Arrow.mp {α β : TypeVec n} (h : α = β) : α ⟹ β
  | _ => Eq.mp (congr_fun h _)
#align typevec.arrow.mp TypeVec.Arrow.mp

/-- turn an equality into an arrow, with reverse direction -/
def Arrow.mpr {α β : TypeVec n} (h : α = β) : β ⟹ α
  | _ => Eq.mpr (congr_fun h _)
#align typevec.arrow.mpr TypeVec.Arrow.mpr

/-- decompose a vector into its prefix appended with its last element -/
def toAppend1DropLast {α : TypeVec (n + 1)} : α ⟹ (drop α ::: last α) :=
  Arrow.mpr (append1_drop_last _)
#align typevec.to_append1_drop_last TypeVec.toAppend1DropLast

/-- stitch two bits of a vector back together -/
def fromAppend1DropLast {α : TypeVec (n + 1)} : (drop α ::: last α) ⟹ α :=
  Arrow.mp (append1_drop_last _)
#align typevec.from_append1_drop_last TypeVec.fromAppend1DropLast

@[simp]
theorem lastFun_splitFun {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last α → last α') :
    lastFun (splitFun f g) = g :=
  rfl
#align typevec.last_fun_split_fun TypeVec.lastFun_splitFun

@[simp]
theorem dropFun_appendFun {α α' : TypeVec n} {β β' : Type*} (f : α ⟹ α') (g : β → β') :
    dropFun (f ::: g) = f :=
  rfl
#align typevec.drop_fun_append_fun TypeVec.dropFun_appendFun

@[simp]
theorem lastFun_appendFun {α α' : TypeVec n} {β β' : Type*} (f : α ⟹ α') (g : β → β') :
    lastFun (f ::: g) = g :=
  rfl
#align typevec.last_fun_append_fun TypeVec.lastFun_appendFun

theorem split_dropFun_lastFun {α α' : TypeVec (n + 1)} (f : α ⟹ α') :
    splitFun (dropFun f) (lastFun f) = f :=
  eq_of_drop_last_eq rfl rfl
#align typevec.split_drop_fun_last_fun TypeVec.split_dropFun_lastFun

theorem splitFun_inj {α α' : TypeVec (n + 1)} {f f' : drop α ⟹ drop α'} {g g' : last α → last α'}
    (H : splitFun f g = splitFun f' g') : f = f' ∧ g = g' := by
  rw [← dropFun_splitFun f g, H, ← lastFun_splitFun f g, H]; simp
#align typevec.split_fun_inj TypeVec.splitFun_inj

theorem appendFun_inj {α α' : TypeVec n} {β β' : Type*} {f f' : α ⟹ α'} {g g' : β → β'} :
    (f ::: g : (α ::: β) ⟹ _) = (f' ::: g' : (α ::: β) ⟹ _)
    → f = f' ∧ g = g' :=
  splitFun_inj
#align typevec.append_fun_inj TypeVec.appendFun_inj

theorem splitFun_comp {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : drop α₀ ⟹ drop α₁)
    (f₁ : drop α₁ ⟹ drop α₂) (g₀ : last α₀ → last α₁) (g₁ : last α₁ → last α₂) :
    splitFun (f₁ ⊚ f₀) (g₁ ∘ g₀) = splitFun f₁ g₁ ⊚ splitFun f₀ g₀ :=
  eq_of_drop_last_eq rfl rfl
#align typevec.split_fun_comp TypeVec.splitFun_comp

theorem appendFun_comp_splitFun {α γ : TypeVec n} {β δ : Type*} {ε : TypeVec (n + 1)}
    (f₀ : drop ε ⟹ α) (f₁ : α ⟹ γ) (g₀ : last ε → β) (g₁ : β → δ) :
    appendFun f₁ g₁ ⊚ splitFun f₀ g₀ = splitFun (α' := γ.append1 δ) (f₁ ⊚ f₀) (g₁ ∘ g₀) :=
  (splitFun_comp _ _ _ _).symm
#align typevec.append_fun_comp_split_fun TypeVec.appendFun_comp_splitFun

theorem appendFun_comp  {α₀ α₁ α₂ : TypeVec n}
    {β₀ β₁ β₂ : Type*}
    (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂)
    (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
    (f₁ ⊚ f₀ ::: g₁ ∘ g₀) = (f₁ ::: g₁) ⊚ (f₀ ::: g₀) :=
  eq_of_drop_last_eq rfl rfl
#align typevec.append_fun_comp TypeVec.appendFun_comp

theorem appendFun_comp' {α₀ α₁ α₂ : TypeVec n} {β₀ β₁ β₂ : Type*}
    (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
    (f₁ ::: g₁) ⊚ (f₀ ::: g₀) = (f₁ ⊚ f₀ ::: g₁ ∘ g₀) :=
  eq_of_drop_last_eq rfl rfl
#align typevec.append_fun_comp' TypeVec.appendFun_comp'

theorem nilFun_comp {α₀ : TypeVec 0} (f₀ : α₀ ⟹ Fin2.elim0) : nilFun ⊚ f₀ = f₀ :=
  funext fun x => by apply Fin2.elim0 x -- Porting note: `by apply` is necessary?
#align typevec.nil_fun_comp TypeVec.nilFun_comp

theorem appendFun_comp_id {α : TypeVec n} {β₀ β₁ β₂ : Type u} (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
    (@id _ α ::: g₁ ∘ g₀) = (id ::: g₁) ⊚ (id ::: g₀) :=
  eq_of_drop_last_eq rfl rfl
#align typevec.append_fun_comp_id TypeVec.appendFun_comp_id

@[simp]
theorem dropFun_comp {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
    dropFun (f₁ ⊚ f₀) = dropFun f₁ ⊚ dropFun f₀ :=
  rfl
#align typevec.drop_fun_comp TypeVec.dropFun_comp

@[simp]
theorem lastFun_comp {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
    lastFun (f₁ ⊚ f₀) = lastFun f₁ ∘ lastFun f₀ :=
  rfl
#align typevec.last_fun_comp TypeVec.lastFun_comp

theorem appendFun_aux {α α' : TypeVec n} {β β' : Type*} (f : (α ::: β) ⟹ (α' ::: β')) :
    (dropFun f ::: lastFun f) = f :=
  eq_of_drop_last_eq rfl rfl
#align typevec.append_fun_aux TypeVec.appendFun_aux

theorem appendFun_id_id {α : TypeVec n} {β : Type*} :
    (@TypeVec.id n α ::: @_root_.id β) = TypeVec.id :=
  eq_of_drop_last_eq rfl rfl
#align typevec.append_fun_id_id TypeVec.appendFun_id_id

instance subsingleton0 : Subsingleton (TypeVec 0) :=
  ⟨fun a b => funext fun a => by apply Fin2.elim0 a⟩ -- Porting note: `by apply` necessary?
#align typevec.subsingleton0 TypeVec.subsingleton0

-- Porting note: `simp` attribute `TypeVec` moved to file `Tactic/Attr/Register.lean`

/-- cases distinction for 0-length type vector -/
protected def casesNil {β : TypeVec 0 → Sort*} (f : β Fin2.elim0) : ∀ v, β v :=
  fun v => cast (by congr; funext i; cases i) f
#align typevec.cases_nil TypeVec.casesNil

/-- cases distinction for (n+1)-length type vector -/
protected def casesCons (n : ℕ) {β : TypeVec (n + 1) → Sort*}
    (f : ∀ (t) (v : TypeVec n), β (v ::: t)) :
    ∀ v, β v :=
  fun v : TypeVec (n + 1) => cast (by simp) (f v.last v.drop)
#align typevec.cases_cons TypeVec.casesCons

protected theorem casesNil_append1 {β : TypeVec 0 → Sort*} (f : β Fin2.elim0) :
    TypeVec.casesNil f Fin2.elim0 = f :=
  rfl
#align typevec.cases_nil_append1 TypeVec.casesNil_append1

protected theorem casesCons_append1 (n : ℕ) {β : TypeVec (n + 1) → Sort*}
    (f : ∀ (t) (v : TypeVec n), β (v ::: t)) (v : TypeVec n) (α) :
    TypeVec.casesCons n f (v ::: α) = f α v :=
  rfl
#align typevec.cases_cons_append1 TypeVec.casesCons_append1

/-- cases distinction for an arrow in the category of 0-length type vectors -/
def typevecCasesNil₃ {β : ∀ v v' : TypeVec 0, v ⟹ v' → Sort*}
    (f : β Fin2.elim0 Fin2.elim0 nilFun) :
    ∀ v v' fs, β v v' fs := fun v v' fs => by
  refine cast ?_ f
  have eq₁ : v = Fin2.elim0 := by funext i; contradiction
  have eq₂ : v' = Fin2.elim0 := by funext i; contradiction
  have eq₃ : fs = nilFun := by funext i; contradiction
  cases eq₁; cases eq₂; cases eq₃; rfl
#align typevec.typevec_cases_nil₃ TypeVec.typevecCasesNil₃

/-- cases distinction for an arrow in the category of (n+1)-length type vectors -/
def typevecCasesCons₃ (n : ℕ) {β : ∀ v v' : TypeVec (n + 1), v ⟹ v' → Sort*}
    (F : ∀ (t t') (f : t → t') (v v' : TypeVec n) (fs : v ⟹ v'),
    β (v ::: t) (v' ::: t') (fs ::: f)) :
    ∀ v v' fs, β v v' fs := by
  intro v v'
  rw [← append1_drop_last v, ← append1_drop_last v']
  intro fs
  rw [← split_dropFun_lastFun fs]
  apply F
#align typevec.typevec_cases_cons₃ TypeVec.typevecCasesCons₃

/-- specialized cases distinction for an arrow in the category of 0-length type vectors -/
def typevecCasesNil₂ {β : Fin2.elim0 ⟹ Fin2.elim0 → Sort*} (f : β nilFun) : ∀ f, β f := by
  intro g
  suffices g = nilFun by rwa [this]
  ext ⟨⟩
#align typevec.typevec_cases_nil₂ TypeVec.typevecCasesNil₂

/-- specialized cases distinction for an arrow in the category of (n+1)-length type vectors -/
def typevecCasesCons₂ (n : ℕ) (t t' : Type*) (v v' : TypeVec n)
    {β : (v ::: t) ⟹ (v' ::: t') → Sort*}
    (F : ∀ (f : t → t') (fs : v ⟹ v'), β (fs ::: f)) : ∀ fs, β fs := by
  intro fs
  rw [← split_dropFun_lastFun fs]
  apply F
#align typevec.typevec_cases_cons₂ TypeVec.typevecCasesCons₂


theorem typevecCasesNil₂_appendFun {β : Fin2.elim0 ⟹ Fin2.elim0 → Sort*} (f : β nilFun) :
    typevecCasesNil₂ f nilFun = f :=
  rfl
#align typevec.typevec_cases_nil₂_append_fun TypeVec.typevecCasesNil₂_appendFun

theorem typevecCasesCons₂_appendFun (n : ℕ) (t t' : Type*) (v v' : TypeVec n)
    {β : (v ::: t) ⟹ (v' ::: t') → Sort*}
    (F : ∀ (f : t → t') (fs : v ⟹ v'), β (fs ::: f))
    (f fs) :
    typevecCasesCons₂ n t t' v v' F (fs ::: f) = F f fs :=
  rfl
#align typevec.typevec_cases_cons₂_append_fun TypeVec.typevecCasesCons₂_appendFun

-- for lifting predicates and relations
/-- `PredLast α p x` predicates `p` of the last element of `x : α.append1 β`. -/
def PredLast (α : TypeVec n) {β : Type*} (p : β → Prop) : ∀ ⦃i⦄, (α.append1 β) i → Prop
  | Fin2.fs _ => fun _ => True
  | Fin2.fz => p
#align typevec.pred_last TypeVec.PredLast

/-- `RelLast α r x y` says that `p` the last elements of `x y : α.append1 β` are related by `r` and
all the other elements are equal. -/
def RelLast (α : TypeVec n) {β γ : Type u} (r : β → γ → Prop) :
    ∀ ⦃i⦄, (α.append1 β) i → (α.append1 γ) i → Prop
  | Fin2.fs _ => Eq
  | Fin2.fz => r
#align typevec.rel_last TypeVec.RelLast

section Liftp'

open Nat

/-- `repeat n t` is a `n-length` type vector that contains `n` occurrences of `t` -/
def «repeat» : ∀ (n : ℕ), Sort _ → TypeVec n
  | 0, _ => Fin2.elim0
  | Nat.succ i, t => append1 («repeat» i t) t
#align typevec.repeat TypeVec.repeat

/-- `prod α β` is the pointwise product of the components of `α` and `β` -/
def prod : ∀ {n}, TypeVec.{u} n → TypeVec.{u} n → TypeVec n
  | 0,     _, _ => Fin2.elim0
  | n + 1, α, β => (@prod n (drop α) (drop β)) ::: (last α × last β)
#align typevec.prod TypeVec.prod

@[inherit_doc] scoped[MvFunctor] infixl:45 " ⊗ " => TypeVec.prod

/- porting note: the order of universes in `const` is reversed w.r.t. mathlib3 -/
/-- `const x α` is an arrow that ignores its source and constructs a `TypeVec` that
contains nothing but `x` -/
protected def const {β} (x : β) : ∀ {n} (α : TypeVec n), α ⟹ «repeat» _ β
  | succ _, α, Fin2.fs _ => TypeVec.const x (drop α) _
  | succ _, _, Fin2.fz   => fun _ => x
#align typevec.const TypeVec.const

open Function (uncurry)

/-- vector of equality on a product of vectors -/
def repeatEq : ∀ {n} (α : TypeVec n), (α ⊗ α) ⟹ «repeat» _ Prop
  | 0, _ => nilFun
  | succ _, α => repeatEq (drop α) ::: uncurry Eq
#align typevec.repeat_eq TypeVec.repeatEq

theorem const_append1 {β γ} (x : γ) {n} (α : TypeVec n) :
    TypeVec.const x (α ::: β) = appendFun (TypeVec.const x α) fun _ => x := by
  ext i : 1; cases i <;> rfl
#align typevec.const_append1 TypeVec.const_append1

theorem eq_nilFun {α β : TypeVec 0} (f : α ⟹ β) : f = nilFun := by
  ext x; cases x
#align typevec.eq_nil_fun TypeVec.eq_nilFun

theorem id_eq_nilFun {α : TypeVec 0} : @id _ α = nilFun := by
  ext x; cases x
#align typevec.id_eq_nil_fun TypeVec.id_eq_nilFun

theorem const_nil {β} (x : β) (α : TypeVec 0) : TypeVec.const x α = nilFun := by
  ext i : 1; cases i
#align typevec.const_nil TypeVec.const_nil

@[typevec]
theorem repeat_eq_append1 {β} {n} (α : TypeVec n) :
    repeatEq (α ::: β) = splitFun (α := (α ⊗ α) ::: _ )
    (α' := («repeat» n Prop) ::: _) (repeatEq α) (uncurry Eq) := by
  induction n <;> rfl
#align typevec.repeat_eq_append1 TypeVec.repeat_eq_append1

@[typevec]
theorem repeat_eq_nil (α : TypeVec 0) : repeatEq α = nilFun := by ext i; cases i
#align typevec.repeat_eq_nil TypeVec.repeat_eq_nil

/-- predicate on a type vector to constrain only the last object -/
def PredLast' (α : TypeVec n) {β : Type*} (p : β → Prop) :
    (α ::: β) ⟹ «repeat» (n + 1) Prop :=
  splitFun (TypeVec.const True α) p
#align typevec.pred_last' TypeVec.PredLast'

/-- predicate on the product of two type vectors to constrain only their last object -/
def RelLast' (α : TypeVec n) {β : Type*} (p : β → β → Prop) :
    (α ::: β) ⊗ (α ::: β) ⟹ «repeat» (n + 1) Prop :=
  splitFun (repeatEq α) (uncurry p)
#align typevec.rel_last' TypeVec.RelLast'

/-- given `F : TypeVec.{u} (n+1) → Type u`, `curry F : Type u → TypeVec.{u} → Type u`,
i.e. its first argument can be fed in separately from the rest of the vector of arguments -/
def Curry (F : TypeVec.{u} (n + 1) → Type*) (α : Type u) (β : TypeVec.{u} n) : Type _ :=
  F (β ::: α)
#align typevec.curry TypeVec.Curry

instance Curry.inhabited (F : TypeVec.{u} (n + 1) → Type*) (α : Type u) (β : TypeVec.{u} n)
    [I : Inhabited (F <| (β ::: α))] : Inhabited (Curry F α β) :=
  I
#align typevec.curry.inhabited TypeVec.Curry.inhabited

/-- arrow to remove one element of a `repeat` vector -/
def dropRepeat (α : Type*) : ∀ {n}, drop («repeat» (succ n) α) ⟹ «repeat» n α
  | succ _, Fin2.fs i => dropRepeat α i
  | succ _, Fin2.fz   => fun (a : α) => a
#align typevec.drop_repeat TypeVec.dropRepeat

/-- projection for a repeat vector -/
def ofRepeat {α : Sort _} : ∀ {n i}, «repeat» n α i → α
  | _, Fin2.fz   => fun (a : α) => a
  | _, Fin2.fs i => @ofRepeat _ _ i
#align typevec.of_repeat TypeVec.ofRepeat

theorem const_iff_true {α : TypeVec n} {i x p} : ofRepeat (TypeVec.const p α i x) ↔ p := by
  induction i with
  | fz      => rfl
  | fs _ ih => erw [TypeVec.const, @ih (drop α) x]
#align typevec.const_iff_true TypeVec.const_iff_true


section
variable {α β γ : TypeVec.{u} n}
variable (p : α ⟹ «repeat» n Prop) (r : α ⊗ α ⟹ «repeat» n Prop)

/-- left projection of a `prod` vector -/
def prod.fst : ∀ {n} {α β : TypeVec.{u} n}, α ⊗ β ⟹ α
  | succ _, α, β, Fin2.fs i => @prod.fst _ (drop α) (drop β) i
  | succ _, _, _, Fin2.fz => Prod.fst
#align typevec.prod.fst TypeVec.prod.fst

/-- right projection of a `prod` vector -/
def prod.snd : ∀ {n} {α β : TypeVec.{u} n}, α ⊗ β ⟹ β
  | succ _, α, β, Fin2.fs i => @prod.snd _ (drop α) (drop β) i
  | succ _, _, _, Fin2.fz => Prod.snd
#align typevec.prod.snd TypeVec.prod.snd

/-- introduce a product where both components are the same -/
def prod.diag : ∀ {n} {α : TypeVec.{u} n}, α ⟹ α ⊗ α
  | succ _, α, Fin2.fs _, x => @prod.diag _ (drop α) _ x
  | succ _, _, Fin2.fz, x => (x, x)
#align typevec.prod.diag TypeVec.prod.diag

/-- constructor for `prod` -/
def prod.mk : ∀ {n} {α β : TypeVec.{u} n} (i : Fin2 n), α i → β i → (α ⊗ β) i
  | succ _, α, β, Fin2.fs i => mk (α := fun i => α i.fs) (β := fun i => β i.fs) i
  | succ _, _, _, Fin2.fz   => Prod.mk
#align typevec.prod.mk TypeVec.prod.mk

end


@[simp]
theorem prod_fst_mk {α β : TypeVec n} (i : Fin2 n) (a : α i) (b : β i) :
    TypeVec.prod.fst i (prod.mk i a b) = a := by
  induction' i with _ _ _ i_ih
  · simp_all only [prod.fst, prod.mk]
  apply i_ih
#align typevec.prod_fst_mk TypeVec.prod_fst_mk

@[simp]
theorem prod_snd_mk {α β : TypeVec n} (i : Fin2 n) (a : α i) (b : β i) :
    TypeVec.prod.snd i (prod.mk i a b) = b := by
  induction' i with _ _ _ i_ih
  · simp_all [prod.snd, prod.mk]
  apply i_ih
#align typevec.prod_snd_mk TypeVec.prod_snd_mk

/-- `prod` is functorial -/
protected def prod.map : ∀ {n} {α α' β β' : TypeVec.{u} n}, α ⟹ β → α' ⟹ β' → α ⊗ α' ⟹ β ⊗ β'
  | succ _, α, α', β, β', x, y, Fin2.fs _, a =>
    @prod.map _ (drop α) (drop α') (drop β) (drop β') (dropFun x) (dropFun y) _ a
  | succ _, _, _, _, _, x, y, Fin2.fz, a => (x _ a.1, y _ a.2)
#align typevec.prod.map TypeVec.prod.map



@[inherit_doc] scoped[MvFunctor] infixl:45 " ⊗' " => TypeVec.prod.map

theorem fst_prod_mk {α α' β β' : TypeVec n} (f : α ⟹ β) (g : α' ⟹ β') :
    TypeVec.prod.fst ⊚ (f ⊗' g) = f ⊚ TypeVec.prod.fst := by
  funext i; induction i with
  | fz => rfl
  | fs _ i_ih => apply i_ih
#align typevec.fst_prod_mk TypeVec.fst_prod_mk

theorem snd_prod_mk {α α' β β' : TypeVec n} (f : α ⟹ β) (g : α' ⟹ β') :
    TypeVec.prod.snd ⊚ (f ⊗' g) = g ⊚ TypeVec.prod.snd := by
  funext i; induction i with
  | fz => rfl
  | fs _ i_ih => apply i_ih
#align typevec.snd_prod_mk TypeVec.snd_prod_mk

theorem fst_diag {α : TypeVec n} : TypeVec.prod.fst ⊚ (prod.diag : α ⟹ _) = id := by
  funext i; induction i with
  | fz => rfl
  | fs _ i_ih => apply i_ih
#align typevec.fst_diag TypeVec.fst_diag

theorem snd_diag {α : TypeVec n} : TypeVec.prod.snd ⊚ (prod.diag : α ⟹ _) = id := by
  funext i; induction i with
  | fz => rfl
  | fs _ i_ih => apply i_ih
#align typevec.snd_diag TypeVec.snd_diag

theorem repeatEq_iff_eq {α : TypeVec n} {i x y} :
    ofRepeat (repeatEq α i (prod.mk _ x y)) ↔ x = y := by
  induction' i with _ _ _ i_ih
  · rfl
  erw [repeatEq, i_ih]
#align typevec.repeat_eq_iff_eq TypeVec.repeatEq_iff_eq

/-- given a predicate vector `p` over vector `α`, `Subtype_ p` is the type of vectors
that contain an `α` that satisfies `p` -/
def Subtype_ : ∀ {n} {α : TypeVec.{u} n}, (α ⟹ «repeat» n Prop) → TypeVec n
  | _, _, p, Fin2.fz => Subtype fun x => p Fin2.fz x
  | _, _, p, Fin2.fs i => Subtype_ (dropFun p) i
#align typevec.subtype_ TypeVec.Subtype_

/-- projection on `Subtype_` -/
def subtypeVal : ∀ {n} {α : TypeVec.{u} n} (p : α ⟹ «repeat» n Prop), Subtype_ p ⟹ α
  | succ n, _, _, Fin2.fs i => @subtypeVal n _ _ i
  | succ _, _, _, Fin2.fz => Subtype.val
#align typevec.subtype_val TypeVec.subtypeVal

/-- arrow that rearranges the type of `Subtype_` to turn a subtype of vector into
a vector of subtypes -/
def toSubtype :
    ∀ {n} {α : TypeVec.{u} n} (p : α ⟹ «repeat» n Prop),
      (fun i : Fin2 n => { x // ofRepeat <| p i x }) ⟹ Subtype_ p
  | succ _, _, p, Fin2.fs i, x => toSubtype (dropFun p) i x
  | succ _, _, _, Fin2.fz, x => x
#align typevec.to_subtype TypeVec.toSubtype

/-- arrow that rearranges the type of `Subtype_` to turn a vector of subtypes
into a subtype of vector -/
def ofSubtype {n} {α : TypeVec.{u} n} (p : α ⟹ «repeat» n Prop) :
    Subtype_ p ⟹ fun i : Fin2 n => { x // ofRepeat <| p i x }
  | Fin2.fs i, x => ofSubtype _ i x
  | Fin2.fz,   x => x
#align typevec.of_subtype TypeVec.ofSubtype

/-- similar to `toSubtype` adapted to relations (i.e. predicate on product) -/
def toSubtype' {n} {α : TypeVec.{u} n} (p : α ⊗ α ⟹ «repeat» n Prop) :
    (fun i : Fin2 n => { x : α i × α i // ofRepeat <| p i (prod.mk _ x.1 x.2) }) ⟹ Subtype_ p
  | Fin2.fs i, x => toSubtype' (dropFun p) i x
  | Fin2.fz, x => ⟨x.val, cast (by congr) x.property⟩
#align typevec.to_subtype' TypeVec.toSubtype'

/-- similar to `of_subtype` adapted to relations (i.e. predicate on product) -/
def ofSubtype' {n} {α : TypeVec.{u} n} (p : α ⊗ α ⟹ «repeat» n Prop) :
    Subtype_ p ⟹ fun i : Fin2 n => { x : α i × α i // ofRepeat <| p i (prod.mk _ x.1 x.2) }
  | Fin2.fs i, x => ofSubtype' _ i x
  | Fin2.fz, x => ⟨x.val, cast (by congr) x.property⟩
#align typevec.of_subtype' TypeVec.ofSubtype'

/-- similar to `diag` but the target vector is a `Subtype_`
guaranteeing the equality of the components -/
def diagSub {n} {α : TypeVec.{u} n} : α ⟹ Subtype_ (repeatEq α)
  | Fin2.fs _, x => @diagSub _ (drop α) _ x
  | Fin2.fz, x => ⟨(x, x), rfl⟩
#align typevec.diag_sub TypeVec.diagSub

theorem subtypeVal_nil {α : TypeVec.{u} 0} (ps : α ⟹ «repeat» 0 Prop) :
    TypeVec.subtypeVal ps = nilFun :=
  funext <| by rintro ⟨⟩
#align typevec.subtype_val_nil TypeVec.subtypeVal_nil

theorem diag_sub_val {n} {α : TypeVec.{u} n} : subtypeVal (repeatEq α) ⊚ diagSub = prod.diag := by
  ext i x
  induction' i with _ _ _ i_ih
  · simp only [comp, subtypeVal, repeatEq.eq_2, diagSub, prod.diag]
  apply @i_ih (drop α)
#align typevec.diag_sub_val TypeVec.diag_sub_val

theorem prod_id : ∀ {n} {α β : TypeVec.{u} n}, (id ⊗' id) = (id : α ⊗ β ⟹ _) := by
  intros
  ext i a
  induction' i with _ _ _ i_ih
  · cases a
    rfl
  · apply i_ih
#align typevec.prod_id TypeVec.prod_id

theorem append_prod_appendFun {n} {α α' β β' : TypeVec.{u} n} {φ φ' ψ ψ' : Type u}
    {f₀ : α ⟹ α'} {g₀ : β ⟹ β'} {f₁ : φ → φ'} {g₁ : ψ → ψ'} :
    ((f₀ ⊗' g₀) ::: (_root_.Prod.map f₁ g₁)) = ((f₀ ::: f₁) ⊗' (g₀ ::: g₁)) := by
  ext i a
  cases i
  · cases a
    rfl
  · rfl
#align typevec.append_prod_append_fun TypeVec.append_prod_appendFun

end Liftp'

@[simp]
theorem dropFun_diag {α} : dropFun (@prod.diag (n + 1) α) = prod.diag := by
  ext i : 2
  induction i <;> simp [dropFun, *] <;> rfl
#align typevec.drop_fun_diag TypeVec.dropFun_diag

@[simp]
theorem dropFun_subtypeVal {α} (p : α ⟹ «repeat» (n + 1) Prop) :
    dropFun (subtypeVal p) = subtypeVal _ :=
  rfl
#align typevec.drop_fun_subtype_val TypeVec.dropFun_subtypeVal

@[simp]
theorem lastFun_subtypeVal {α} (p : α ⟹ «repeat» (n + 1) Prop) :
    lastFun (subtypeVal p) = Subtype.val :=
  rfl
#align typevec.last_fun_subtype_val TypeVec.lastFun_subtypeVal

@[simp]
theorem dropFun_toSubtype {α} (p : α ⟹ «repeat» (n + 1) Prop) :
    dropFun (toSubtype p) = toSubtype _ := by
  ext i
  induction i <;> simp [dropFun, *] <;> rfl
#align typevec.drop_fun_to_subtype TypeVec.dropFun_toSubtype

@[simp]
theorem lastFun_toSubtype {α} (p : α ⟹ «repeat» (n + 1) Prop) :
    lastFun (toSubtype p) = _root_.id := by
  ext i : 2
  induction i; simp [dropFun, *]; rfl
#align typevec.last_fun_to_subtype TypeVec.lastFun_toSubtype

@[simp]
theorem dropFun_of_subtype {α} (p : α ⟹ «repeat» (n + 1) Prop) :
    dropFun (ofSubtype p) = ofSubtype _ := by
  ext i : 2
  induction i <;> simp [dropFun, *] <;> rfl
#align typevec.drop_fun_of_subtype TypeVec.dropFun_of_subtype

@[simp]
theorem lastFun_of_subtype {α} (p : α ⟹ «repeat» (n + 1) Prop) :
    lastFun (ofSubtype p) = _root_.id := by
  ext i : 2
  induction i; simp [dropFun, *]; rfl
#align typevec.last_fun_of_subtype TypeVec.lastFun_of_subtype

@[simp]
theorem dropFun_RelLast' {α : TypeVec n} {β} (R : β → β → Prop) :
    dropFun (RelLast' α R) = repeatEq α :=
  rfl
#align typevec.drop_fun_rel_last TypeVec.dropFun_RelLast'

attribute [simp] drop_append1'

open MvFunctor

@[simp]
theorem dropFun_prod {α α' β β' : TypeVec (n + 1)} (f : α ⟹ β) (f' : α' ⟹ β') :
    dropFun (f ⊗' f') = (dropFun f ⊗' dropFun f') := by
  ext i : 2
  induction i <;> simp [dropFun, *] <;> rfl
#align typevec.drop_fun_prod TypeVec.dropFun_prod

@[simp]
theorem lastFun_prod {α α' β β' : TypeVec (n + 1)} (f : α ⟹ β) (f' : α' ⟹ β') :
    lastFun (f ⊗' f') = Prod.map (lastFun f) (lastFun f') := by
  ext i : 1
  induction i; simp [lastFun, *]; rfl
#align typevec.last_fun_prod TypeVec.lastFun_prod

@[simp]
theorem dropFun_from_append1_drop_last {α : TypeVec (n + 1)} :
    dropFun (@fromAppend1DropLast _ α) = id :=
  rfl
#align typevec.drop_fun_from_append1_drop_last TypeVec.dropFun_from_append1_drop_last

@[simp]
theorem lastFun_from_append1_drop_last {α : TypeVec (n + 1)} :
    lastFun (@fromAppend1DropLast _ α) = _root_.id :=
  rfl
#align typevec.last_fun_from_append1_drop_last TypeVec.lastFun_from_append1_drop_last

@[simp]
theorem dropFun_id {α : TypeVec (n + 1)} : dropFun (@TypeVec.id _ α) = id :=
  rfl
#align typevec.drop_fun_id TypeVec.dropFun_id

@[simp]
theorem prod_map_id {α β : TypeVec n} : (@TypeVec.id _ α ⊗' @TypeVec.id _ β) = id := by
  ext i x : 2
  induction i <;> simp only [TypeVec.prod.map, *, dropFun_id]
  cases x
  · rfl
  · rfl
#align typevec.prod_map_id TypeVec.prod_map_id

@[simp]
theorem subtypeVal_diagSub {α : TypeVec n} : subtypeVal (repeatEq α) ⊚ diagSub = prod.diag := by
  ext i x
  induction' i with _ _ _ i_ih
  · simp [comp, diagSub, subtypeVal, prod.diag]
  · simp [prod.diag]
    simp? [comp, diagSub, subtypeVal, prod.diag] at * says
      simp only [comp, subtypeVal, diagSub] at *
    apply @i_ih (drop _)
#align typevec.subtype_val_diag_sub TypeVec.subtypeVal_diagSub

@[simp]
theorem toSubtype_of_subtype {α : TypeVec n} (p : α ⟹ «repeat» n Prop) :
    toSubtype p ⊚ ofSubtype p = id := by
  ext i x
  induction i <;> dsimp only [id, toSubtype, comp, ofSubtype] at *
  simp [*]
#align typevec.to_subtype_of_subtype TypeVec.toSubtype_of_subtype

@[simp]
theorem subtypeVal_toSubtype {α : TypeVec n} (p : α ⟹ «repeat» n Prop) :
    subtypeVal p ⊚ toSubtype p = fun _ => Subtype.val := by
  ext i x
  induction i <;> dsimp only [toSubtype, comp, subtypeVal] at *
  simp [*]
#align typevec.subtype_val_to_subtype TypeVec.subtypeVal_toSubtype

@[simp]
theorem toSubtype_of_subtype_assoc
    {α β : TypeVec n} (p : α ⟹ «repeat» n Prop) (f : β ⟹ Subtype_ p) :
    @toSubtype n _ p ⊚ ofSubtype _ ⊚ f = f := by
  rw [← comp_assoc, toSubtype_of_subtype]; simp
#align typevec.to_subtype_of_subtype_assoc TypeVec.toSubtype_of_subtype_assoc

@[simp]
theorem toSubtype'_of_subtype' {α : TypeVec n} (r : α ⊗ α ⟹ «repeat» n Prop) :
    toSubtype' r ⊚ ofSubtype' r = id := by
  ext i x
  induction i
  <;> dsimp only [id, toSubtype', comp, ofSubtype'] at *
  <;> simp [Subtype.eta, *]
#align typevec.to_subtype'_of_subtype' TypeVec.toSubtype'_of_subtype'

theorem subtypeVal_toSubtype' {α : TypeVec n} (r : α ⊗ α ⟹ «repeat» n Prop) :
    subtypeVal r ⊚ toSubtype' r = fun i x => prod.mk i x.1.fst x.1.snd := by
  ext i x
  induction i <;> dsimp only [id, toSubtype', comp, subtypeVal, prod.mk] at *
  simp [*]
#align typevec.subtype_val_to_subtype' TypeVec.subtypeVal_toSubtype'

end TypeVec
