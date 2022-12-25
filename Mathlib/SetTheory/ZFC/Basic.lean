/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module set_theory.zfc.basic
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Small.Basic
import Mathlib.Order.WellFounded

/-!
# A model of ZFC

In this file, we model Zermelo-Fraenkel set theory (+ Choice) using Lean's underlying type theory.
We do this in four main steps:
* Define pre-sets inductively.
* Define extensional equivalence on pre-sets and give it a `setoid` instance.
* Define ZFC sets by quotienting pre-sets by extensional equivalence.
* Define classes as sets of ZFC sets.
Then the rest is usual set theory.

## The model

* `pSet`: Pre-set. A pre-set is inductively defined by its indexing type and its members, which are
  themselves pre-sets.
* `Set`: ZFC set. Defined as `pSet` quotiented by `pSet.equiv`, the extensional equivalence.
* `Class`: Class. Defined as `set Set`.
* `Set.choice`: Axiom of choice. Proved from Lean's axiom of choice.

## Other definitions

* `arity α n`: `n`-ary function `α → α → ... → α`. Defined inductively.
* `arity.const a n`: `n`-ary constant function equal to `a`.
* `pSet.type`: Underlying type of a pre-set.
* `pSet.func`: Underlying family of pre-sets of a pre-set.
* `pSet.equiv`: Extensional equivalence of pre-sets. Defined inductively.
* `pSet.omega`, `Set.omega`: The von Neumann ordinal `ω` as a `pSet`, as a `Set`.
* `pSet.arity.equiv`: Extensional equivalence of `n`-ary `pSet`-valued functions. Extension of
  `pSet.equiv`.
* `pSet.resp`: Collection of `n`-ary `pSet`-valued functions that respect extensional equivalence.
* `pSet.eval`: Turns a `pSet`-valued function that respect extensional equivalence into a
  `Set`-valued function.
* `classical.all_definable`: All functions are classically definable.
* `Set.is_func` : Predicate that a ZFC set is a subset of `x × y` that can be considered as a ZFC
  function `x → y`. That is, each member of `x` is related by the ZFC set to exactly one member of
  `y`.
* `Set.funs`: ZFC set of ZFC functions `x → y`.
* `Class.iota`: Definite description operator.

## Notes

To avoid confusion between the Lean `set` and the ZFC `Set`, docstrings in this file refer to them
respectively as "`set`" and "ZFC set".

## TODO

Prove `Set.map_definable_aux` computably.
-/


universe u v

/-- The type of `n`-ary functions `α → α → ... → α`. -/
def Arity (α : Type u) : ℕ → Type u
  | 0 => α
  | n + 1 => α → Arity α n
#align arity Arity

@[simp]
theorem arity_zero (α : Type u) : Arity α 0 = α :=
  rfl
#align arity_zero arity_zero

@[simp]
theorem arity_succ (α : Type u) (n : ℕ) : Arity α n.succ = (α → Arity α n) :=
  rfl
#align arity_succ arity_succ

namespace Arity

/-- Constant `n`-ary function with value `a`. -/
def Const {α : Type u} (a : α) : ∀ n, Arity α n
  | 0 => a
  | n + 1 => fun _ => Const a n
#align arity.const Arity.Const

@[simp]
theorem const_zero {α : Type u} (a : α) : Const a 0 = a :=
  rfl
#align arity.const_zero Arity.const_zero

@[simp]
theorem const_succ {α : Type u} (a : α) (n : ℕ) : Const a n.succ = fun _ => Const a n :=
  rfl
#align arity.const_succ Arity.const_succ

theorem const_succ_apply {α : Type u} (a : α) (n : ℕ) (x : α) : Const a n.succ x = Const a n :=
  rfl
#align arity.const_succ_apply Arity.const_succ_apply

instance Arity.inhabited {α n} [Inhabited α] : Inhabited (Arity α n) :=
  ⟨Const default _⟩
#align arity.arity.inhabited Arity.Arity.inhabited

end Arity

/-- The type of pre-sets in universe `u`. A pre-set
  is a family of pre-sets indexed by a type in `Type u`.
  The ZFC universe is defined as a quotient of this
  to ensure extensionality. -/
inductive PSet : Type (u + 1)
  | mk (α : Type u) (A : α → PSet) : PSet
#align pSet PSet

namespace PSet

/-- The underlying type of a pre-set -/
def «Type» : PSet → Type u
  | ⟨α, _⟩ => α
#align pSet.type PSet.Type

/-- The underlying pre-set family of a pre-set -/
def Func : ∀ x : PSet, x.Type → PSet
  | ⟨_, A⟩ => A
#align pSet.func PSet.Func

@[simp]
theorem mk_type (α A) : «Type» ⟨α, A⟩ = α :=
  rfl
#align pSet.mk_type PSet.mk_type

@[simp]
theorem mk_func (α A) : Func ⟨α, A⟩ = A :=
  rfl
#align pSet.mk_func PSet.mk_func

@[simp]
theorem eta : ∀ x : PSet, mk x.Type x.Func = x
  | ⟨_, _⟩ => rfl
#align pSet.eta PSet.eta

/-- Two pre-sets are extensionally equivalent if every element of the first family is extensionally
equivalent to some element of the second family and vice-versa. -/
def Equiv : PSet → PSet → Prop
  | ⟨_, A⟩, ⟨_, B⟩ => (∀ a, ∃ b, Equiv (A a) (B b)) ∧ (∀ b, ∃ a, Equiv (A a) (B b))
#align pSet.equiv PSet.Equiv

theorem equiv_iff :
    ∀ {x y : PSet},
      Equiv x y ↔ (∀ i, ∃ j, Equiv (x.Func i) (y.Func j)) ∧ ∀ j, ∃ i, Equiv (x.Func i) (y.Func j)
  | ⟨_, _⟩, ⟨_, _⟩ => Iff.rfl
#align pSet.equiv_iff PSet.equiv_iff

theorem Equiv.exists_left {x y : PSet} (h : Equiv x y) : ∀ i, ∃ j, Equiv (x.Func i) (y.Func j) :=
  (equiv_iff.1 h).1
#align pSet.equiv.exists_left PSet.Equiv.exists_left

theorem Equiv.exists_right {x y : PSet} (h : Equiv x y) : ∀ j, ∃ i, Equiv (x.Func i) (y.Func j) :=
  (equiv_iff.1 h).2
#align pSet.equiv.exists_right PSet.Equiv.exists_right

@[refl]
protected theorem Equiv.refl : ∀ x, Equiv x x
  | ⟨_, _⟩ => ⟨fun a => ⟨a, Equiv.refl _⟩, fun a => ⟨a, Equiv.refl _⟩⟩
#align pSet.equiv.refl PSet.Equiv.refl

protected theorem Equiv.rfl {x} : Equiv x x :=
  Equiv.refl x
#align pSet.equiv.rfl PSet.Equiv.rfl

protected theorem Equiv.euc : ∀ {x y z}, Equiv x y → Equiv z y → Equiv x z
  | ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨αβ, βα⟩, ⟨γβ, βγ⟩ =>
    ⟨ fun a =>
        let ⟨b, ab⟩ := αβ a
        let ⟨c, bc⟩ := βγ b
        ⟨c, Equiv.euc ab bc⟩,
      fun c =>
        let ⟨b, cb⟩ := γβ c
        let ⟨a, ba⟩ := βα b
        ⟨a, Equiv.euc ba cb⟩ ⟩
#align pSet.equiv.euc PSet.Equiv.euc

@[symm]
protected theorem Equiv.symm {x y} : Equiv x y → Equiv y x :=
  (Equiv.refl y).euc
#align pSet.equiv.symm PSet.Equiv.symm

@[trans]
protected theorem Equiv.trans {x y z} (h1 : Equiv x y) (h2 : Equiv y z) : Equiv x z :=
  h1.euc h2.symm
#align pSet.equiv.trans PSet.Equiv.trans

protected theorem equiv_of_is_empty (x y : PSet) [IsEmpty x.Type] [IsEmpty y.Type] : Equiv x y :=
  equiv_iff.2 <| by simp
#align pSet.equiv_of_is_empty PSet.equiv_of_is_empty

instance setoid : Setoid PSet :=
  ⟨PSet.Equiv, Equiv.refl, Equiv.symm, Equiv.trans⟩
#align pSet.setoid PSet.setoid

/-- A pre-set is a subset of another pre-set if every element of the first family is extensionally
equivalent to some element of the second family.-/
protected def Subset (x y : PSet) : Prop :=
  ∀ a, ∃ b, Equiv (x.Func a) (y.Func b)
#align pSet.subset PSet.Subset

instance : HasSubset PSet :=
  ⟨PSet.Subset⟩

instance : IsRefl PSet (· ⊆ ·) :=
  ⟨fun _ a => ⟨a, Equiv.refl _⟩⟩

instance : IsTrans PSet (· ⊆ ·) :=
  ⟨fun x y z hxy hyz a => by
    cases' hxy a with b hb
    cases' hyz b with c hc
    exact ⟨c, hb.trans hc⟩⟩

theorem Equiv.ext : ∀ x y : PSet, Equiv x y ↔ x ⊆ y ∧ y ⊆ x
  | ⟨_, _⟩, ⟨_, _⟩ =>
    ⟨fun ⟨αβ, βα⟩ =>
      ⟨αβ, fun b =>
        let ⟨a, h⟩ := βα b
        ⟨a, Equiv.symm h⟩⟩,
      fun ⟨αβ, βα⟩ =>
      ⟨αβ, fun b =>
        let ⟨a, h⟩ := βα b
        ⟨a, Equiv.symm h⟩⟩⟩
#align pSet.equiv.ext PSet.Equiv.ext

theorem Subset.congr_left : ∀ {x y z : PSet}, Equiv x y → (x ⊆ z ↔ y ⊆ z)
  | ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨αβ, βα⟩ =>
    ⟨fun αγ b =>
      let ⟨a, ba⟩ := βα b
      let ⟨c, ac⟩ := αγ a
      ⟨c, (Equiv.symm ba).trans ac⟩,
      fun βγ a =>
      let ⟨b, ab⟩ := αβ a
      let ⟨c, bc⟩ := βγ b
      ⟨c, Equiv.trans ab bc⟩⟩
#align pSet.subset.congr_left PSet.Subset.congr_left

theorem Subset.congr_right : ∀ {x y z : PSet}, Equiv x y → (z ⊆ x ↔ z ⊆ y)
  | ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨αβ, βα⟩ =>
    ⟨fun γα c =>
      let ⟨a, ca⟩ := γα c
      let ⟨b, ab⟩ := αβ a
      ⟨b, ca.trans ab⟩,
      fun γβ c =>
      let ⟨b, cb⟩ := γβ c
      let ⟨a, ab⟩ := βα b
      ⟨a, cb.trans (Equiv.symm ab)⟩⟩
#align pSet.subset.congr_right PSet.Subset.congr_right

/-- `x ∈ y` as pre-sets if `x` is extensionally equivalent to a member of the family `y`. -/
protected def Mem (x y : PSet.{u}) : Prop :=
  ∃ b, Equiv x (y.Func b)
#align pSet.mem PSet.Mem

instance : Membership PSet PSet :=
  ⟨PSet.Mem⟩

theorem Mem.mk {α : Type u} (A : α → PSet) (a : α) : A a ∈ mk α A :=
  ⟨a, Equiv.refl (A a)⟩
#align pSet.mem.mk PSet.Mem.mk

theorem func_mem (x : PSet) (i : x.Type) : x.Func i ∈ x := by
  cases x
  apply Mem.mk
#align pSet.func_mem PSet.func_mem

theorem Mem.ext : ∀ {x y : PSet.{u}}, (∀ w : PSet.{u}, w ∈ x ↔ w ∈ y) → Equiv x y
  | ⟨_, A⟩, ⟨_, B⟩, h =>
    ⟨fun a => (h (A a)).1 (Mem.mk A a), fun b =>
      let ⟨a, ha⟩ := (h (B b)).2 (Mem.mk B b)
      ⟨a, ha.symm⟩⟩
#align pSet.mem.ext PSet.Mem.ext

theorem Mem.congr_right : ∀ {x y : PSet.{u}}, Equiv x y → ∀ {w : PSet.{u}}, w ∈ x ↔ w ∈ y
  | ⟨_, _⟩, ⟨_, _⟩, ⟨αβ, βα⟩, _ =>
    ⟨fun ⟨a, ha⟩ =>
      let ⟨b, hb⟩ := αβ a
      ⟨b, ha.trans hb⟩,
      fun ⟨b, hb⟩ =>
      let ⟨a, ha⟩ := βα b
      ⟨a, hb.euc ha⟩⟩
#align pSet.mem.congr_right PSet.Mem.congr_right

theorem equiv_iff_mem {x y : PSet.{u}} : Equiv x y ↔ ∀ {w : PSet.{u}}, w ∈ x ↔ w ∈ y :=
  ⟨Mem.congr_right,
    match x, y with
    | ⟨_, A⟩, ⟨_, B⟩ => fun h =>
      ⟨fun a => h.1 (Mem.mk A a), fun b =>
        let ⟨a, h⟩ := h.2 (Mem.mk B b)
        ⟨a, h.symm⟩⟩⟩
#align pSet.equiv_iff_mem PSet.equiv_iff_mem

theorem Mem.congr_left : ∀ {x y : PSet.{u}}, Equiv x y → ∀ {w : PSet.{u}}, x ∈ w ↔ y ∈ w
  | _, _, h, ⟨_, _⟩ => ⟨fun ⟨a, ha⟩ => ⟨a, h.symm.trans ha⟩, fun ⟨a, ha⟩ => ⟨a, h.trans ha⟩⟩
#align pSet.mem.congr_left PSet.Mem.congr_left

private theorem mem_wf_aux : ∀ {x y : PSet.{u}}, Equiv x y → Acc (· ∈ ·) y
  | ⟨α, A⟩, ⟨β, B⟩, H =>
    ⟨_, by
      rintro ⟨γ, C⟩ ⟨b, hc⟩
      cases' H.exists_right b with a ha
      have H := ha.trans hc.symm
      rw [mk_func] at H
      exact mem_wf_aux H⟩

theorem mem_wf : @WellFounded PSet (· ∈ ·) :=
  ⟨fun x => mem_wf_aux <| Equiv.refl x⟩
#align pSet.mem_wf PSet.mem_wf

instance : WellFoundedRelation PSet :=
  ⟨_, mem_wf⟩

instance : IsAsymm PSet (· ∈ ·) :=
  mem_wf.isAsymm

instance : IsIrrefl PSet (· ∈ ·) :=
  mem_wf.isIrrefl

theorem mem_asymm {x y : PSet} : x ∈ y → y ∉ x :=
  asymm
#align pSet.mem_asymm PSet.mem_asymm

theorem mem_irrefl (x : PSet) : x ∉ x :=
  irrefl x
#align pSet.mem_irrefl PSet.mem_irrefl

/-- Convert a pre-set to a `set` of pre-sets. -/
def toSet (u : PSet.{u}) : Set PSet.{u} :=
  { x | x ∈ u }
#align pSet.to_set PSet.toSet

@[simp]
theorem mem_toSet (a u : PSet.{u}) : a ∈ u.toSet ↔ a ∈ u :=
  Iff.rfl
#align pSet.mem_to_set PSet.mem_toSet

/-- A nonempty set is one that contains some element. -/
protected def Nonempty (u : PSet) : Prop :=
  u.toSet.Nonempty
#align pSet.nonempty PSet.Nonempty

theorem nonempty_def (u : PSet) : u.Nonempty ↔ ∃ x, x ∈ u :=
  Iff.rfl
#align pSet.nonempty_def PSet.nonempty_def

theorem nonempty_of_mem {x u : PSet} (h : x ∈ u) : u.Nonempty :=
  ⟨x, h⟩
#align pSet.nonempty_of_mem PSet.nonempty_of_mem

@[simp]
theorem nonempty_toSet_iff {u : PSet} : u.toSet.Nonempty ↔ u.Nonempty :=
  Iff.rfl
#align pSet.nonempty_to_set_iff PSet.nonempty_toSet_iff

theorem nonempty_type_iff_nonempty {x : PSet} : Nonempty x.Type ↔ PSet.Nonempty x :=
  ⟨fun ⟨i⟩ => ⟨_, func_mem _ i⟩, fun ⟨_, j, _⟩ => ⟨j⟩⟩
#align pSet.nonempty_type_iff_nonempty PSet.nonempty_type_iff_nonempty

theorem nonempty_of_nonempty_type (x : PSet) [h : Nonempty x.Type] : PSet.Nonempty x :=
  nonempty_type_iff_nonempty.1 h
#align pSet.nonempty_of_nonempty_type PSet.nonempty_of_nonempty_type

/-- Two pre-sets are equivalent iff they have the same members. -/
theorem Equiv.eq {x y : PSet} : Equiv x y ↔ toSet x = toSet y :=
  equiv_iff_mem.trans Set.ext_iff.symm
#align pSet.equiv.eq PSet.Equiv.eq

instance : Coe PSet (Set PSet) :=
  ⟨toSet⟩

/-- The empty pre-set -/
protected def Empty : PSet :=
  ⟨_, PEmpty.elim⟩
#align pSet.empty PSet.Empty

instance : EmptyCollection PSet :=
  ⟨PSet.Empty⟩

instance : Inhabited PSet :=
  ⟨∅⟩

instance : IsEmpty («Type» ∅) :=
  ⟨PEmpty.elim⟩

@[simp]
theorem mem_empty (x : PSet.{u}) : x ∉ (∅ : PSet.{u}) :=
  IsEmpty.exists_iff.1
#align pSet.mem_empty PSet.mem_empty

@[simp]
theorem to_set_empty : toSet ∅ = ∅ := by simp [toSet]
#align pSet.to_set_empty PSet.to_set_empty

@[simp]
theorem empty_subset (x : PSet.{u}) : (∅ : PSet) ⊆ x := fun x => x.elim
#align pSet.empty_subset PSet.empty_subset

@[simp]
theorem not_nonempty_empty : ¬PSet.Nonempty ∅ := by simp [PSet.Nonempty]
#align pSet.not_nonempty_empty PSet.not_nonempty_empty

protected theorem equiv_empty (x : PSet) [IsEmpty x.Type] : Equiv x ∅ :=
  PSet.equiv_of_is_empty x _
#align pSet.equiv_empty PSet.equiv_empty

/-- Insert an element into a pre-set -/
protected def insert (x y : PSet) : PSet :=
  ⟨Option y.Type, fun o => Option.casesOn o x y.Func⟩
#align pSet.insert PSet.insert

instance : Insert PSet PSet :=
  ⟨PSet.insert⟩

instance : Singleton PSet PSet :=
  ⟨fun s => insert s ∅⟩

instance : IsLawfulSingleton PSet PSet :=
  ⟨fun _ => rfl⟩

instance (x y : PSet) : Inhabited (insert x y).Type :=
  inferInstanceAs (Inhabited <| Option y.Type)

/-- The n-th von Neumann ordinal -/
def ofNat : ℕ → PSet
  | 0 => ∅
  | n + 1 => insert (ofNat n) (ofNat n)
#align pSet.of_nat PSet.ofNat

/-- The von Neumann ordinal ω -/
def omega : PSet :=
  ⟨ULift ℕ, fun n => ofNat n.down⟩
#align pSet.omega PSet.omega

/-- The pre-set separation operation `{x ∈ a | p x}` -/
protected def sep (p : PSet → Prop) (x : PSet) : PSet :=
  ⟨{ a // p (x.Func a) }, fun y => x.Func y.1⟩
#align pSet.sep PSet.sep

instance : Sep PSet PSet :=
  ⟨PSet.sep⟩

/-- The pre-set powerset operator -/
def powerset (x : PSet) : PSet :=
  ⟨Set x.Type, fun p => ⟨{ a // p a }, fun y => x.Func y.1⟩⟩
#align pSet.powerset PSet.powerset

@[simp]
theorem mem_powerset : ∀ {x y : PSet}, y ∈ powerset x ↔ y ⊆ x
  | ⟨_, A⟩, ⟨_, B⟩ =>
    ⟨fun ⟨_, e⟩ => (Subset.congr_left e).2 fun ⟨a, _⟩ => ⟨a, Equiv.refl (A a)⟩, fun βα =>
      ⟨{ a | ∃ b, Equiv (B b) (A a) }, fun b =>
        let ⟨a, ba⟩ := βα b
        ⟨⟨a, b, ba⟩, ba⟩,
        fun ⟨_, b, ba⟩ => ⟨b, ba⟩⟩⟩
#align pSet.mem_powerset PSet.mem_powerset

/-- The pre-set union operator -/
def unionₛ (a : PSet) : PSet :=
  ⟨Σx, (a.Func x).Type, fun ⟨x, y⟩ => (a.Func x).Func y⟩
#align pSet.sUnion PSet.unionₛ

prefix:110 "⋃₀ " => unionₛ

@[simp]
theorem mem_unionₛ : ∀ {x y : PSet.{u}}, y ∈ ⋃₀ x ↔ ∃ z ∈ x, y ∈ z
  | ⟨α, A⟩, y =>
    ⟨fun ⟨⟨a, c⟩, (e : Equiv y ((A a).Func c))⟩ =>
      have : Func (A a) c ∈ mk (A a).Type (A a).Func := Mem.mk (A a).Func c
      ⟨_, Mem.mk _ _, (Mem.congr_left e).2 (by rwa [eta] at this)⟩,
      fun ⟨⟨β, B⟩, ⟨a, (e : Equiv (mk β B) (A a))⟩, ⟨b, yb⟩⟩ => by
      rw [← eta (A a)] at e
      exact
        let ⟨βt, _⟩ := e
        let ⟨c, bc⟩ := βt b
        ⟨⟨a, c⟩, yb.trans bc⟩⟩
#align pSet.mem_sUnion PSet.mem_unionₛ

@[simp]
theorem toSet_unionₛ (x : PSet.{u}) : (⋃₀ x).toSet = ⋃₀ (toSet '' x.toSet) := by
  ext
  simp
#align pSet.to_set_sUnion PSet.toSet_unionₛ

/-- The image of a function from pre-sets to pre-sets. -/
def image (f : PSet.{u} → PSet.{u}) (x : PSet.{u}) : PSet :=
  ⟨x.Type, f ∘ x.Func⟩
#align pSet.image PSet.image

theorem mem_image {f : PSet.{u} → PSet.{u}} (H : ∀ {x y}, Equiv x y → Equiv (f x) (f y)) :
    ∀ {x y : PSet.{u}}, y ∈ image f x ↔ ∃ z ∈ x, Equiv y (f z)
  | ⟨_, A⟩, _ =>
    ⟨fun ⟨a, ya⟩ => ⟨A a, Mem.mk A a, ya⟩, fun ⟨_, ⟨a, za⟩, yz⟩ => ⟨a, yz.trans (H za)⟩⟩
#align pSet.mem_image PSet.mem_image

/-- Universe lift operation -/
protected def Lift : PSet.{u} → PSet.{max u v}
  | ⟨α, A⟩ => ⟨ULift.{v, u} α, fun ⟨x⟩ => PSet.Lift (A x)⟩
#align pSet.lift PSet.Lift

-- intended to be used with explicit universe parameters
/-- Embedding of one universe in another -/
@[nolint checkUnivs]
def embed : PSet.{max (u + 1) v} :=
  ⟨ULift.{v, u + 1} PSet, fun ⟨x⟩ => PSet.Lift.{u, max (u + 1) v} x⟩
#align pSet.embed PSet.embed

theorem lift_mem_embed : ∀ x : PSet.{u}, PSet.Lift.{u, max (u + 1) v} x ∈ embed.{u, v} := fun x =>
  ⟨⟨x⟩, Equiv.rfl⟩
#align pSet.lift_mem_embed PSet.lift_mem_embed

/-- Function equivalence is defined so that `f ~ g` iff `∀ x y, x ~ y → f x ~ g y`. This extends to
equivalence of `n`-ary functions. -/
def Arity.Equiv : ∀ {n}, Arity PSet.{u} n → Arity PSet.{u} n → Prop
  | 0, a, b => PSet.Equiv a b
  | _ + 1, a, b => ∀ x y : PSet, PSet.Equiv x y → Arity.Equiv (a x) (b y)
#align pSet.arity.equiv PSet.Arity.Equiv

theorem Arity.equiv_const {a : PSet.{u}} : ∀ n, Arity.Equiv (Arity.Const a n) (Arity.Const a n)
  | 0 => Equiv.rfl
  | _ + 1 => fun _ _ _ => Arity.equiv_const _
#align pSet.arity.equiv_const PSet.Arity.equiv_const

/-- `resp n` is the collection of n-ary functions on `pSet` that respect
  equivalence, i.e. when the inputs are equivalent the output is as well. -/
def Resp (n) :=
  { x : Arity PSet.{u} n // Arity.Equiv x x }
#align pSet.resp PSet.Resp

instance Resp.inhabited {n} : Inhabited (Resp n) :=
  ⟨⟨Arity.Const default _, Arity.equiv_const _⟩⟩
#align pSet.resp.inhabited PSet.Resp.inhabited

/-- The `n`-ary image of a `(n + 1)`-ary function respecting equivalence as a function respecting
equivalence. -/
def Resp.f {n} (f : Resp (n + 1)) (x : PSet) : Resp n :=
  ⟨f.1 x, f.2 _ _ <| Equiv.refl x⟩
#align pSet.resp.f PSet.Resp.f

/-- Function equivalence for functions respecting equivalence. See `pSet.arity.equiv`. -/
def Resp.Equiv {n} (a b : Resp n) : Prop :=
  Arity.Equiv a.1 b.1
#align pSet.resp.equiv PSet.Resp.Equiv

protected theorem Resp.Equiv.refl {n} (a : Resp n) : Resp.Equiv a a :=
  a.2
#align pSet.resp.equiv.refl PSet.Resp.Equiv.refl

protected theorem Resp.Equiv.euc :
    ∀ {n} {a b c : Resp n}, Resp.Equiv a b → Resp.Equiv c b → Resp.Equiv a c
  | 0, _, _, _, hab, hcb => PSet.Equiv.euc hab hcb
  | n + 1, a, b, c, hab, hcb => fun x y h =>
    @Resp.Equiv.euc n (a.f x) (b.f y) (c.f y) (hab _ _ h) (hcb _ _ <| PSet.Equiv.refl y)
#align pSet.resp.equiv.euc PSet.Resp.Equiv.euc

protected theorem Resp.Equiv.symm {n} {a b : Resp n} : Resp.Equiv a b → Resp.Equiv b a :=
  (Resp.Equiv.refl b).euc
#align pSet.resp.equiv.symm PSet.Resp.Equiv.symm

protected theorem Resp.Equiv.trans {n} {x y z : Resp n} (h1 : Resp.Equiv x y)
    (h2 : Resp.Equiv y z) : Resp.Equiv x z :=
  h1.euc h2.symm
#align pSet.resp.equiv.trans PSet.Resp.Equiv.trans

instance Resp.setoid {n} : Setoid (Resp n) :=
  ⟨Resp.Equiv, Resp.Equiv.refl, Resp.Equiv.symm, Resp.Equiv.trans⟩
#align pSet.resp.setoid PSet.Resp.setoid

end PSet

/-- The ZFC universe of sets consists of the type of pre-sets,
  quotiented by extensional equivalence. -/
def ZFSet : Type (u + 1) :=
  Quotient PSet.setoid.{u}
#align Set ZFSet

namespace PSet

namespace Resp

/-- Helper function for `pSet.eval`. -/
def EvalAux :
    ∀ {n}, { f : Resp n → Arity ZFSet.{u} n // ∀ a b : Resp n, Resp.Equiv a b → f a = f b }
  | 0 => ⟨fun a => ⟦a.1⟧, fun _ _ h => Quotient.sound h⟩
  | n + 1 =>
    let F : Resp (n + 1) → Arity ZFSet (n + 1) := fun a =>
      @Quotient.lift _ _ PSet.setoid (fun x => EvalAux.1 (a.f x)) fun _ _ h =>
        EvalAux.2 _ _ (a.2 _ _ h)
    ⟨F, fun b c h =>
      funext <|
        (@Quotient.ind _ _ fun q => F b q = F c q) fun z =>
          EvalAux.2 (Resp.f b z) (Resp.f c z) (h _ _ (PSet.Equiv.refl z))⟩
#align pSet.resp.eval_aux PSet.Resp.EvalAux

/-- An equivalence-respecting function yields an n-ary ZFC set function. -/
def eval (n) : Resp n → Arity ZFSet.{u} n :=
  EvalAux.1
#align pSet.resp.eval PSet.Resp.eval

theorem eval_val {n f x} : (@eval (n + 1) f : ZFSet → Arity ZFSet n) ⟦x⟧ = eval n (Resp.f f x) :=
  rfl
#align pSet.resp.eval_val PSet.Resp.eval_val

end Resp

/-- A set function is "definable" if it is the image of some n-ary pre-set
  function. This isn't exactly definability, but is useful as a sufficient
  condition for functions that have a computable image. -/
class inductive Definable (n) : Arity ZFSet.{u} n → Type (u + 1)
  | mk (f) : Definable n (Resp.eval n f)
#align pSet.definable PSet.Definable

attribute [instance] Definable.mk

/-- The evaluation of a function respecting equivalence is definable, by that same function. -/
def Definable.EqMk {n} (f) : ∀ {s : Arity ZFSet.{u} n} (_ : Resp.eval _ f = s), Definable n s
  | _, rfl => ⟨f⟩
#align pSet.definable.eq_mk PSet.Definable.EqMk

/-- Turns a definable function into a function that respects equivalence. -/
def Definable.Resp {n} : ∀ (s : Arity ZFSet.{u} n) [Definable n s], Resp n
  | _, ⟨f⟩ => f
#align pSet.definable.resp PSet.Definable.Resp

theorem Definable.eq {n} :
    ∀ (s : Arity ZFSet.{u} n) [H : Definable n s], (@Definable.Resp n s H).eval _ = s
  | _, ⟨_⟩ => rfl
#align pSet.definable.eq PSet.Definable.eq

end PSet

namespace Classical

open PSet

/-- All functions are classically definable. -/
noncomputable def AllDefinable : ∀ {n} (F : Arity ZFSet.{u} n), Definable n F
  | 0, F =>
    let p := @Quotient.exists_rep PSet _ F
    Definable.EqMk ⟨choose _, _⟩ (choose_spec p)
  | n + 1, (F : Arity ZFSet.{u} (n + 1)) => by
    have I := fun x => AllDefinable (F x)
    refine' Definable.EqMk ⟨fun x : PSet => (@Definable.Resp _ _ (I ⟦x⟧)).1, _⟩ _
    · dsimp [Arity.Equiv]
      intro x y h
      rw [@Quotient.sound PSet _ _ _ h]
      exact (definable.resp (F ⟦y⟧)).2
    refine' funext fun q => (Quotient.inductionOn q) fun x => _
    simp_rw [Resp.eval_val, resp.f, Subtype.val_eq_coe, Subtype.coe_eta]
    exact @definable.eq _ (F ⟦x⟧) (I ⟦x⟧)
#align classical.all_definable Classical.allDefinable

end Classical

namespace ZFSet

open PSet

/-- Turns a pre-set into a ZFC set. -/
def mk : PSet → ZFSet :=
  Quotient.mk''
#align Set.mk ZFSet.mk

@[simp]
theorem mk_eq (x : PSet) : @Eq ZFSet ⟦x⟧ (mk x) :=
  rfl
#align Set.mk_eq ZFSet.mk_eq

@[simp]
theorem mk_out : ∀ x : ZFSet, mk x.out = x :=
  Quotient.out_eq
#align Set.mk_out ZFSet.mk_out

theorem eq {x y : PSet} : mk x = mk y ↔ Equiv x y :=
  Quotient.eq
#align Set.eq ZFSet.eq

theorem sound {x y : PSet} (h : PSet.Equiv x y) : mk x = mk y :=
  Quotient.sound h
#align Set.sound ZFSet.sound

theorem exact {x y : PSet} : mk x = mk y → PSet.Equiv x y :=
  Quotient.exact
#align Set.exact ZFSet.exact

@[simp]
theorem eval_mk {n f x} :
    (@Resp.eval (n + 1) f : ZFSet → Arity ZFSet n) (mk x) = Resp.eval n (Resp.f f x) :=
  rfl
#align Set.eval_mk ZFSet.eval_mk

/-- The membership relation for ZFC sets is inherited from the membership relation for pre-sets. -/
protected def Mem : ZFSet → ZFSet → Prop :=
  Quotient.lift₂ PSet.Mem fun _ _ _ _ hx hy =>
    propext ((Mem.congr_left hx).trans (Mem.congr_right hy))
#align Set.mem ZFSet.Mem

instance : Membership ZFSet ZFSet :=
  ⟨ZFSet.Mem⟩

@[simp]
theorem mk_mem_iff {x y : PSet} : mk x ∈ mk y ↔ x ∈ y :=
  Iff.rfl
#align Set.mk_mem_iff ZFSet.mk_mem_iff

/-- Convert a ZFC set into a `set` of ZFC sets -/
def toSet (u : ZFSet.{u}) : Set ZFSet.{u} :=
  { x | x ∈ u }
#align Set.to_set ZFSet.toSet

@[simp]
theorem mem_toSet (a u : ZFSet.{u}) : a ∈ u.toSet ↔ a ∈ u :=
  Iff.rfl
#align Set.mem_to_set ZFSet.mem_toSet

instance small_toSet (x : ZFSet.{u}) : Small.{u} x.toSet :=
  (Quotient.inductionOn x (motive := fun x => Small.{u} (ZFSet.toSet x))) fun a => by
    let f : a.Type → (mk a).toSet := fun i => ⟨mk <| a.Func i, func_mem a i⟩
    suffices Function.Surjective f by exact small_of_surjective this
    rintro ⟨y, hb⟩
    induction y using Quotient.inductionOn
    cases' hb with i h
    exact ⟨i, Subtype.coe_injective (Quotient.sound h.symm)⟩
#align Set.small_to_set ZFSet.small_toSet

/-- A nonempty set is one that contains some element. -/
protected def Nonempty (u : ZFSet) : Prop :=
  u.toSet.Nonempty
#align Set.nonempty ZFSet.Nonempty

theorem nonempty_def (u : ZFSet) : u.Nonempty ↔ ∃ x, x ∈ u :=
  Iff.rfl
#align Set.nonempty_def ZFSet.nonempty_def

theorem nonempty_of_mem {x u : ZFSet} (h : x ∈ u) : u.Nonempty :=
  ⟨x, h⟩
#align Set.nonempty_of_mem ZFSet.nonempty_of_mem

@[simp]
theorem nonempty_toSet_iff {u : ZFSet} : u.toSet.Nonempty ↔ u.Nonempty :=
  Iff.rfl
#align Set.nonempty_to_set_iff ZFSet.nonempty_toSet_iff

/-- `x ⊆ y` as ZFC sets means that all members of `x` are members of `y`. -/
protected def Subset (x y : ZFSet.{u}) :=
  ∀ ⦃z⦄, z ∈ x → z ∈ y
#align Set.subset ZFSet.Subset

instance hasSubset : HasSubset ZFSet :=
  ⟨ZFSet.Subset⟩
#align Set.has_subset ZFSet.hasSubset

theorem subset_def {x y : ZFSet.{u}} : x ⊆ y ↔ ∀ ⦃z⦄, z ∈ x → z ∈ y :=
  Iff.rfl
#align Set.subset_def ZFSet.subset_def

instance : IsRefl ZFSet (· ⊆ ·) :=
  ⟨fun _ _ => id⟩

instance : IsTrans ZFSet (· ⊆ ·) :=
  ⟨fun _ _ _ hxy hyz _ ha => hyz (hxy ha)⟩

@[simp]
theorem subset_iff : ∀ {x y : PSet}, mk x ⊆ mk y ↔ x ⊆ y
  | ⟨_, A⟩, ⟨_, _⟩ =>
    ⟨fun h a => @h ⟦A a⟧ (Mem.mk A a), fun h z =>
      Quotient.inductionOn z fun _ ⟨a, za⟩ =>
        let ⟨b, ab⟩ := h a
        ⟨b, za.trans ab⟩⟩
#align Set.subset_iff ZFSet.subset_iff

@[simp]
theorem toSet_subset_iff {x y : ZFSet} : x.toSet ⊆ y.toSet ↔ x ⊆ y := by
  simp [subset_def, Set.subset_def]
#align Set.to_set_subset_iff ZFSet.toSet_subset_iff

@[ext]
theorem ext {x y : ZFSet.{u}} : (∀ z : ZFSet.{u}, z ∈ x ↔ z ∈ y) → x = y :=
  Quotient.inductionOn₂ x y fun _ _ h => Quotient.sound (Mem.ext fun w => h ⟦w⟧)
#align Set.ext ZFSet.ext

theorem ext_iff {x y : ZFSet.{u}} : x = y ↔ ∀ z : ZFSet.{u}, z ∈ x ↔ z ∈ y :=
  ⟨fun h => by simp [h], ext⟩
#align Set.ext_iff ZFSet.ext_iff

theorem toSet_injective : Function.Injective toSet := fun _ _ h => ext <| Set.ext_iff.1 h
#align Set.to_set_injective ZFSet.toSet_injective

@[simp]
theorem toSet_inj {x y : ZFSet} : x.toSet = y.toSet ↔ x = y :=
  toSet_injective.eq_iff
#align Set.to_set_inj ZFSet.toSet_inj

instance : IsAntisymm ZFSet (· ⊆ ·) :=
  ⟨fun _ _ hab hba => ext fun c => ⟨@hab c, @hba c⟩⟩

/-- The empty ZFC set -/
protected def empty : ZFSet :=
  mk ∅
#align Set.empty ZFSet.empty

instance : EmptyCollection ZFSet :=
  ⟨ZFSet.empty⟩

instance : Inhabited ZFSet :=
  ⟨∅⟩

@[simp]
theorem mem_empty (x) : x ∉ (∅ : ZFSet.{u}) :=
  Quotient.inductionOn x PSet.mem_empty
#align Set.mem_empty ZFSet.mem_empty

@[simp]
theorem toSet_empty : toSet ∅ = ∅ := by simp [toSet]
#align Set.to_set_empty ZFSet.toSet_empty

@[simp]
theorem empty_subset (x : ZFSet.{u}) : (∅ : ZFSet) ⊆ x :=
  (Quotient.inductionOn x (motive := _)) fun y => subset_iff.2 <| PSet.empty_subset y
#align Set.empty_subset ZFSet.empty_subset

@[simp]
theorem not_nonempty_empty : ¬ZFSet.Nonempty ∅ := by simp [ZFSet.Nonempty]
#align Set.not_nonempty_empty ZFSet.not_nonempty_empty

@[simp]
theorem nonempty_mk_iff {x : PSet} : (mk x).Nonempty ↔ x.Nonempty := by
  refine' ⟨_, fun ⟨a, h⟩ => ⟨mk a, h⟩⟩
  rintro ⟨a, h⟩
  induction a using Quotient.inductionOn
  exact ⟨_, h⟩
#align Set.nonempty_mk_iff ZFSet.nonempty_mk_iff

theorem eq_empty (x : ZFSet.{u}) : x = ∅ ↔ ∀ y : ZFSet.{u}, y ∉ x :=
  ⟨fun h y => h.symm ▸ mem_empty y, fun h =>
    ext fun y => ⟨fun yx => absurd yx (h y), fun y0 => absurd y0 (mem_empty _)⟩⟩
#align Set.eq_empty ZFSet.eq_empty

/-- `Insert x y` is the set `{x} ∪ y` -/
protected def Insert : ZFSet → ZFSet → ZFSet :=
  Resp.eval 2
    ⟨PSet.insert, fun _ _ uv ⟨_, _⟩ ⟨_, _⟩ ⟨αβ, βα⟩ =>
      ⟨fun o =>
        match o with
        | some a =>
          let ⟨b, hb⟩ := αβ a
          ⟨some b, hb⟩
        | none => ⟨none, uv⟩,
        fun o =>
        match o with
        | some b =>
          let ⟨a, ha⟩ := βα b
          ⟨some a, ha⟩
        | none => ⟨none, uv⟩⟩⟩
#align Set.insert ZFSet.Insert

instance : Insert ZFSet ZFSet :=
  ⟨ZFSet.Insert⟩

instance : Singleton ZFSet ZFSet :=
  ⟨fun x => insert x ∅⟩

instance : IsLawfulSingleton ZFSet ZFSet :=
  ⟨fun _ => rfl⟩

@[simp]
theorem mem_insert_iff {x y z : ZFSet.{u}} : x ∈ insert y z ↔ x = y ∨ x ∈ z :=
  Quotient.inductionOn₃ x y z fun x y ⟨α, A⟩ =>
    show (x ∈ PSet.mk (Option α) fun o => Option.rec y A o) ↔ mk x = mk y ∨ x ∈ PSet.mk α A from
      ⟨fun m =>
        match m with
        | ⟨some a, ha⟩ => by exact Or.inr ⟨a, ha⟩
        | ⟨none, h⟩ => by exact Or.inl (Quotient.sound h),
        fun m =>
        match m with
        | Or.inr ⟨a, ha⟩ => ⟨some a, ha⟩
        | Or.inl h => ⟨none, Quotient.exact h⟩⟩
#align Set.mem_insert_iff ZFSet.mem_insert_iff

theorem mem_insert (x y : ZFSet) : x ∈ insert x y :=
  mem_insert_iff.2 <| Or.inl rfl
#align Set.mem_insert ZFSet.mem_insert

theorem mem_insert_of_mem {y z : ZFSet} (x) (h : z ∈ y) : z ∈ insert x y :=
  mem_insert_iff.2 <| Or.inr h
#align Set.mem_insert_of_mem ZFSet.mem_insert_of_mem

@[simp]
theorem toSet_insert (x y : ZFSet) : (insert x y).toSet = insert x y.toSet := by
  ext
  simp
#align Set.to_set_insert ZFSet.toSet_insert

@[simp]
theorem mem_singleton {x y : ZFSet.{u}} : x ∈ @singleton ZFSet.{u} ZFSet.{u} _ y ↔ x = y :=
  Iff.trans mem_insert_iff
    ⟨fun o => Or.rec (fun h => h) (fun n => absurd n (mem_empty _)) o, Or.inl⟩
#align Set.mem_singleton ZFSet.mem_singleton

@[simp]
theorem toSet_singleton (x : ZFSet) : ({x} : ZFSet).toSet = {x} := by
  ext
  simp
#align Set.to_set_singleton ZFSet.toSet_singleton

@[simp]
theorem mem_pair {x y z : ZFSet.{u}} : x ∈ ({y, z} : ZFSet) ↔ x = y ∨ x = z :=
  Iff.trans mem_insert_iff <| or_congr Iff.rfl mem_singleton
#align Set.mem_pair ZFSet.mem_pair

/-- `omega` is the first infinite von Neumann ordinal -/
def omega : ZFSet :=
  mk PSet.omega
#align Set.omega ZFSet.omega

@[simp]
theorem omega_zero : ∅ ∈ omega :=
  ⟨⟨0⟩, Equiv.rfl⟩
#align Set.omega_zero ZFSet.omega_zero

@[simp]
theorem omega_succ {n} : n ∈ omega.{u} → insert n n ∈ omega.{u} :=
  Quotient.inductionOn n fun x ⟨⟨n⟩, h⟩ =>
    ⟨⟨n + 1⟩,
      ZFSet.exact <|
        show insert (mk x) (mk x) = insert (mk <| ofNat n) (mk <| ofNat n) by
          rw [ZFSet.sound h]
          rfl⟩
#align Set.omega_succ ZFSet.omega_succ

/-- `{x ∈ a | p x}` is the set of elements in `a` satisfying `p` -/
protected def sep (p : ZFSet → Prop) : ZFSet → ZFSet :=
  Resp.eval 1
    ⟨PSet.sep fun y => p (mk y), fun ⟨α, A⟩ ⟨β, B⟩ ⟨αβ, βα⟩ =>
      ⟨fun ⟨a, pa⟩ =>
        let ⟨b, hb⟩ := αβ a
        ⟨⟨b, by simpa only [mk_func, ← ZFSet.sound hb]⟩, hb⟩,
        fun ⟨b, pb⟩ =>
        let ⟨a, ha⟩ := βα b
        ⟨⟨a, by simpa only [mk_func, ZFSet.sound ha]⟩, ha⟩⟩⟩
#align Set.sep ZFSet.sep

instance : Sep ZFSet ZFSet :=
  ⟨ZFSet.sep⟩

-- TODO: this looks fishy
@[simp]
theorem mem_sep {p : ZFSet.{u} → Prop} {x y : ZFSet.{u}} : y ∈ { y ∈ x | p y } ↔ y ∈ x ∧ p y :=
  Iff.rfl
--  Quotient.inductionOn₂ x y fun _ _ =>
--    ⟨fun ⟨⟨a, pa⟩, h⟩ => ⟨⟨a, pa⟩, h⟩, fun ⟨⟨a, h⟩, pa⟩ => ⟨⟨a, h⟩, pa⟩⟩
#align Set.mem_sep ZFSet.mem_sep

@[simp]
theorem toSet_sep (a : ZFSet) (p : ZFSet → Prop) :
    { x ∈ a | p x }.toSet = { x ∈ a.toSet | p x } := by
  ext
  simp
#align Set.to_set_sep SetCat.to_set_sep

/-- The powerset operation, the collection of subsets of a ZFC set -/
def powerset : SetCat → SetCat :=
  Resp.eval 1
    ⟨powerset, fun ⟨α, A⟩ ⟨β, B⟩ ⟨αβ, βα⟩ =>
      ⟨fun p =>
        ⟨{ b | ∃ a, p a ∧ Equiv (A a) (B b) }, fun ⟨a, pa⟩ =>
          let ⟨b, ab⟩ := αβ a
          ⟨⟨b, a, pa, ab⟩, ab⟩,
          fun ⟨b, a, pa, ab⟩ => ⟨⟨a, pa⟩, ab⟩⟩,
        fun q =>
        ⟨{ a | ∃ b, q b ∧ Equiv (A a) (B b) }, fun ⟨a, b, qb, ab⟩ => ⟨⟨b, qb⟩, ab⟩, fun ⟨b, qb⟩ =>
          let ⟨a, ab⟩ := βα b
          ⟨⟨a, b, qb, ab⟩, ab⟩⟩⟩⟩
#align Set.powerset SetCat.powerset

@[simp]
theorem mem_powerset {x y : SetCat.{u}} : y ∈ powerset x ↔ y ⊆ x :=
  Quotient.induction_on₂ x y fun ⟨α, A⟩ ⟨β, B⟩ =>
    show (⟨β, B⟩ : PSet.{u}) ∈ PSet.powerset.{u} ⟨α, A⟩ ↔ _ by simp [mem_powerset, subset_iff]
#align Set.mem_powerset SetCat.mem_powerset

theorem sUnion_lem {α β : Type u} (A : α → PSet) (B : β → PSet) (αβ : ∀ a, ∃ b, Equiv (A a) (B b)) :
    ∀ a, ∃ b, Equiv ((sUnion ⟨α, A⟩).func a) ((sUnion ⟨β, B⟩).func b)
  | ⟨a, c⟩ => by
    let ⟨b, hb⟩ := αβ a
    induction' ea : A a with γ Γ
    induction' eb : B b with δ Δ
    rw [ea, eb] at hb
    cases' hb with γδ δγ
    exact
      let c : type (A a) := c
      let ⟨d, hd⟩ := γδ (by rwa [ea] at c)
      have : PSet.Equiv ((A a).func c) ((B b).func (Eq.ndrec d (Eq.symm eb))) :=
        match A a, B b, ea, eb, c, d, hd with
        | _, _, rfl, rfl, x, y, hd => hd
      ⟨⟨b, by
          rw [mk_func]
          exact Eq.ndrec d (Eq.symm eb)⟩,
        this⟩
#align Set.sUnion_lem SetCat.sUnion_lem

/-- The union operator, the collection of elements of elements of a ZFC set -/
def sUnion : SetCat → SetCat :=
  Resp.eval 1
    ⟨PSet.sUnion, fun ⟨α, A⟩ ⟨β, B⟩ ⟨αβ, βα⟩ =>
      ⟨sUnion_lem A B αβ, fun a =>
        Exists.elim
          (sUnion_lem B A (fun b => Exists.elim (βα b) fun c hc => ⟨c, PSet.Equiv.symm hc⟩) a)
          fun b hb => ⟨b, PSet.Equiv.symm hb⟩⟩⟩
#align Set.sUnion SetCat.sUnion

-- mathport name: Set.sUnion
prefix:110 "⋃₀ " => SetCat.sUnion

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem mem_sUnion {x y : SetCat.{u}} : y ∈ ⋃₀ x ↔ ∃ z ∈ x, y ∈ z :=
  Quotient.induction_on₂ x y fun x y =>
    Iff.trans mem_sUnion
      ⟨fun ⟨z, h⟩ => ⟨⟦z⟧, h⟩, fun ⟨z, h⟩ => Quotient.induction_on z (fun z h => ⟨z, h⟩) h⟩
#align Set.mem_sUnion SetCat.mem_sUnion

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mem_sUnion_of_mem {x y z : SetCat} (hy : y ∈ z) (hz : z ∈ x) : y ∈ ⋃₀ x :=
  mem_sUnion.2 ⟨z, hz, hy⟩
#align Set.mem_sUnion_of_mem SetCat.mem_sUnion_of_mem

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem sUnion_singleton {x : SetCat.{u}} : ⋃₀ ({x} : SetCat) = x :=
  ext fun y => by simp_rw [mem_sUnion, exists_prop, mem_singleton, exists_eq_left]
#align Set.sUnion_singleton SetCat.sUnion_singleton

theorem singleton_injective : Function.Injective (@singleton SetCat SetCat _) := fun x y H => by
  let this := congr_arg sUnion H
  rwa [sUnion_singleton, sUnion_singleton] at this
#align Set.singleton_injective SetCat.singleton_injective

@[simp]
theorem singleton_inj {x y : SetCat} : ({x} : SetCat) = {y} ↔ x = y :=
  singleton_injective.eq_iff
#align Set.singleton_inj SetCat.singleton_inj

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem to_set_sUnion (x : SetCat.{u}) : (⋃₀ x).toSet = ⋃₀ (to_set '' x.toSet) := by
  ext
  simp
#align Set.to_set_sUnion SetCat.to_set_sUnion

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The binary union operation -/
protected def union (x y : SetCat.{u}) : SetCat.{u} :=
  ⋃₀ {x, y}
#align Set.union SetCat.union

/-- The binary intersection operation -/
protected def inter (x y : SetCat.{u}) : SetCat.{u} :=
  { z ∈ x | z ∈ y }
#align Set.inter SetCat.inter

/-- The set difference operation -/
protected def diff (x y : SetCat.{u}) : SetCat.{u} :=
  { z ∈ x | z ∉ y }
#align Set.diff SetCat.diff

instance : Union SetCat :=
  ⟨SetCat.union⟩

instance : Inter SetCat :=
  ⟨SetCat.inter⟩

instance : SDiff SetCat :=
  ⟨SetCat.diff⟩

@[simp]
theorem to_set_union (x y : SetCat.{u}) : (x ∪ y).toSet = x.toSet ∪ y.toSet := by
  unfold Union.union
  rw [SetCat.union]
  simp
#align Set.to_set_union SetCat.to_set_union

@[simp]
theorem to_set_inter (x y : SetCat.{u}) : (x ∩ y).toSet = x.toSet ∩ y.toSet := by
  unfold Inter.inter
  rw [SetCat.inter]
  ext
  simp
#align Set.to_set_inter SetCat.to_set_inter

@[simp]
theorem to_set_sdiff (x y : SetCat.{u}) : (x \ y).toSet = x.toSet \ y.toSet := by
  change { z ∈ x | z ∉ y }.toSet = _
  ext
  simp
#align Set.to_set_sdiff SetCat.to_set_sdiff

@[simp]
theorem mem_union {x y z : SetCat.{u}} : z ∈ x ∪ y ↔ z ∈ x ∨ z ∈ y := by
  rw [← mem_to_set]
  simp
#align Set.mem_union SetCat.mem_union

@[simp]
theorem mem_inter {x y z : SetCat.{u}} : z ∈ x ∩ y ↔ z ∈ x ∧ z ∈ y :=
  @mem_sep fun z : SetCat.{u} => z ∈ y
#align Set.mem_inter SetCat.mem_inter

@[simp]
theorem mem_diff {x y z : SetCat.{u}} : z ∈ x \ y ↔ z ∈ x ∧ z ∉ y :=
  @mem_sep fun z : SetCat.{u} => z ∉ y
#align Set.mem_diff SetCat.mem_diff

/-- Induction on the `∈` relation. -/
@[elab_as_elim]
theorem induction_on {p : SetCat → Prop} (x) (h : ∀ x, (∀ y ∈ x, p y) → p x) : p x :=
  (Quotient.induction_on x) fun u =>
    (PSet.recOn u) fun α A IH =>
      (h _) fun y =>
        show @Membership.Mem _ _ SetCat.hasMem y ⟦⟨α, A⟩⟧ → p y from
          Quotient.induction_on y fun v ⟨a, ha⟩ => by
            rw [@Quotient.sound PSet _ _ _ ha]
            exact IH a
#align Set.induction_on SetCat.induction_on

theorem mem_wf : @WellFounded SetCat (· ∈ ·) :=
  ⟨fun x => induction_on x Acc.intro⟩
#align Set.mem_wf SetCat.mem_wf

instance : WellFoundedRelation SetCat :=
  ⟨_, mem_wf⟩

instance : IsAsymm SetCat (· ∈ ·) :=
  mem_wf.IsAsymm

theorem mem_asymm {x y : SetCat} : x ∈ y → y ∉ x :=
  asymm
#align Set.mem_asymm SetCat.mem_asymm

theorem mem_irrefl (x : SetCat) : x ∉ x :=
  irrefl x
#align Set.mem_irrefl SetCat.mem_irrefl

theorem regularity (x : SetCat.{u}) (h : x ≠ ∅) : ∃ y ∈ x, x ∩ y = ∅ :=
  by_contradiction fun ne =>
    h <|
      (eq_empty x).2 fun y =>
        (induction_on y) fun z (IH : ∀ w : SetCat.{u}, w ∈ z → w ∉ x) =>
          show z ∉ x from fun zx =>
            Ne
              ⟨z, zx,
                (eq_empty _).2 fun w wxz =>
                  let ⟨wx, wz⟩ := mem_inter.1 wxz
                  IH w wz wx⟩
#align Set.regularity SetCat.regularity

/-- The image of a (definable) ZFC set function -/
def image (f : SetCat → SetCat) [H : Definable 1 f] : SetCat → SetCat :=
  let r := @Definable.resp 1 f _
  Resp.eval 1
    ⟨image r.1, fun x y e =>
      mem.ext fun z =>
        Iff.trans (mem_image r.2) <|
          Iff.trans
              ⟨fun ⟨w, h1, h2⟩ => ⟨w, (mem.congr_right e).1 h1, h2⟩, fun ⟨w, h1, h2⟩ =>
                ⟨w, (mem.congr_right e).2 h1, h2⟩⟩ <|
            Iff.symm (mem_image r.2)⟩
#align Set.image SetCat.image

theorem image.mk :
    ∀ (f : SetCat.{u} → SetCat.{u}) [H : Definable 1 f] (x) {y} (h : y ∈ x), f y ∈ @image f H x
  | _, ⟨F⟩, x, y => (Quotient.induction_on₂ x y) fun ⟨α, A⟩ y ⟨a, ya⟩ => ⟨a, F.2 _ _ ya⟩
#align Set.image.mk SetCat.image.mk

@[simp]
theorem mem_image :
    ∀ {f : SetCat.{u} → SetCat.{u}} [H : Definable 1 f] {x y : SetCat.{u}},
      y ∈ @image f H x ↔ ∃ z ∈ x, f z = y
  | _, ⟨F⟩, x, y =>
    (Quotient.induction_on₂ x y) fun ⟨α, A⟩ y =>
      ⟨fun ⟨a, ya⟩ => ⟨⟦A a⟧, Mem.mk A a, Eq.symm <| Quotient.sound ya⟩, fun ⟨z, hz, e⟩ =>
        e ▸ image.mk _ _ hz⟩
#align Set.mem_image SetCat.mem_image

@[simp]
theorem to_set_image (f : SetCat → SetCat) [H : Definable 1 f] (x : SetCat) :
    (image f x).toSet = f '' x.toSet := by
  ext
  simp
#align Set.to_set_image SetCat.to_set_image

/-- Kuratowski ordered pair -/
def pair (x y : SetCat.{u}) : SetCat.{u} :=
  {{x}, {x, y}}
#align Set.pair SetCat.pair

@[simp]
theorem to_set_pair (x y : SetCat.{u}) : (pair x y).toSet = {{x}, {x, y}} := by simp [pair]
#align Set.to_set_pair SetCat.to_set_pair

/-- A subset of pairs `{(a, b) ∈ x × y | p a b}` -/
def pairSep (p : SetCat.{u} → SetCat.{u} → Prop) (x y : SetCat.{u}) : SetCat.{u} :=
  { z ∈ powerset (powerset (x ∪ y)) | ∃ a ∈ x, ∃ b ∈ y, z = pair a b ∧ p a b }
#align Set.pair_sep SetCat.pairSep

@[simp]
theorem mem_pair_sep {p} {x y z : SetCat.{u}} :
    z ∈ pairSep p x y ↔ ∃ a ∈ x, ∃ b ∈ y, z = pair a b ∧ p a b := by
  refine' mem_sep.trans ⟨And.right, fun e => ⟨_, e⟩⟩
  rcases e with ⟨a, ax, b, bY, rfl, pab⟩
  simp only [mem_powerset, subset_def, mem_union, pair, mem_pair]
  rintro u (rfl | rfl) v <;> simp only [mem_singleton, mem_pair]
  · rintro rfl
    exact Or.inl ax
  · rintro (rfl | rfl) <;> [left, right] <;> assumption
#align Set.mem_pair_sep SetCat.mem_pair_sep

theorem pair_injective : Function.Injective2 pair := fun x x' y y' H => by
  have ae := ext_iff.1 H
  simp only [pair, mem_pair] at ae
  obtain rfl : x = x' := by
    cases' (ae {x}).1 (by simp) with h h
    · exact singleton_injective h
    · have m : x' ∈ ({x} : SetCat) := by simp [h]
      rw [mem_singleton.mp m]
  have he : x = y → y = y' := by
    rintro rfl
    cases' (ae {x, y'}).2 (by simp only [eq_self_iff_true, or_true_iff]) with xy'x xy'xx
    · rw [eq_comm, ← mem_singleton, ← xy'x, mem_pair]
      exact Or.inr rfl
    · simpa [eq_comm] using (ext_iff.1 xy'xx y').1 (by simp)
  obtain xyx | xyy' := (ae {x, y}).1 (by simp)
  · obtain rfl := mem_singleton.mp ((ext_iff.1 xyx y).1 <| by simp)
    simp [he rfl]
  · obtain rfl | yy' := mem_pair.mp ((ext_iff.1 xyy' y).1 <| by simp)
    · simp [he rfl]
    · simp [yy']
#align Set.pair_injective SetCat.pair_injective

@[simp]
theorem pair_inj {x y x' y' : SetCat} : pair x y = pair x' y' ↔ x = x' ∧ y = y' :=
  pair_injective.eq_iff
#align Set.pair_inj SetCat.pair_inj

/-- The cartesian product, `{(a, b) | a ∈ x, b ∈ y}` -/
def prod : SetCat.{u} → SetCat.{u} → SetCat.{u} :=
  pairSep fun a b => True
#align Set.prod SetCat.prod

@[simp]
theorem mem_prod {x y z : SetCat.{u}} : z ∈ prod x y ↔ ∃ a ∈ x, ∃ b ∈ y, z = pair a b := by
  simp [Prod]
#align Set.mem_prod SetCat.mem_prod

@[simp]
theorem pair_mem_prod {x y a b : SetCat.{u}} : pair a b ∈ prod x y ↔ a ∈ x ∧ b ∈ y :=
  ⟨fun h =>
    let ⟨a', a'x, b', b'y, e⟩ := mem_prod.1 h
    match a', b', pair_injective e, a'x, b'y with
    | _, _, ⟨rfl, rfl⟩, ax, bY => ⟨ax, bY⟩,
    fun ⟨ax, bY⟩ => mem_prod.2 ⟨a, ax, b, bY, rfl⟩⟩
#align Set.pair_mem_prod SetCat.pair_mem_prod

/-- `is_func x y f` is the assertion that `f` is a subset of `x × y` which relates to each element
of `x` a unique element of `y`, so that we can consider `f`as a ZFC function `x → y`. -/
def IsFunc (x y f : SetCat.{u}) : Prop :=
  f ⊆ prod x y ∧ ∀ z : SetCat.{u}, z ∈ x → ∃! w, pair z w ∈ f
#align Set.is_func SetCat.IsFunc

/-- `funs x y` is `y ^ x`, the set of all set functions `x → y` -/
def funs (x y : SetCat.{u}) : SetCat.{u} :=
  { f ∈ powerset (prod x y) | IsFunc x y f }
#align Set.funs SetCat.funs

@[simp]
theorem mem_funs {x y f : SetCat.{u}} : f ∈ funs x y ↔ IsFunc x y f := by simp [funs, is_func]
#align Set.mem_funs SetCat.mem_funs

-- TODO(Mario): Prove this computably
noncomputable instance mapDefinableAux (f : SetCat → SetCat) [H : Definable 1 f] :
    Definable 1 fun y => pair y (f y) :=
  @Classical.allDefinable 1 _
#align Set.map_definable_aux SetCat.mapDefinableAux

/-- Graph of a function: `map f x` is the ZFC function which maps `a ∈ x` to `f a` -/
noncomputable def map (f : SetCat → SetCat) [H : Definable 1 f] : SetCat → SetCat :=
  image fun y => pair y (f y)
#align Set.map SetCat.map

@[simp]
theorem mem_map {f : SetCat → SetCat} [H : Definable 1 f] {x y : SetCat} :
    y ∈ map f x ↔ ∃ z ∈ x, pair z (f z) = y :=
  mem_image
#align Set.mem_map SetCat.mem_map

theorem map_unique {f : SetCat.{u} → SetCat.{u}} [H : Definable 1 f] {x z : SetCat.{u}}
    (zx : z ∈ x) : ∃! w, pair z w ∈ map f x :=
  ⟨f z, image.mk _ _ zx, fun y yx => by
    let ⟨w, wx, we⟩ := mem_image.1 yx
    let ⟨wz, fy⟩ := pair_injective we
    rw [← fy, wz]⟩
#align Set.map_unique SetCat.map_unique

@[simp]
theorem map_is_func {f : SetCat → SetCat} [H : Definable 1 f] {x y : SetCat} :
    IsFunc x y (map f x) ↔ ∀ z ∈ x, f z ∈ y :=
  ⟨fun ⟨ss, h⟩ z zx =>
    let ⟨t, t1, t2⟩ := h z zx
    (t2 (f z) (image.mk _ _ zx)).symm ▸ (pair_mem_prod.1 (ss t1)).right,
    fun h =>
    ⟨fun y yx =>
      let ⟨z, zx, ze⟩ := mem_image.1 yx
      ze ▸ pair_mem_prod.2 ⟨zx, h z zx⟩,
      fun z => map_unique⟩⟩
#align Set.map_is_func SetCat.map_is_func

end SetCat

/- ./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler has_sep[has_sep] Set[Set] -/
/- ./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler has_insert[has_insert] Set[Set] -/
/-- The collection of all classes.

We define `Class` as `set Set`, as this allows us to get many instances automatically. However, in
practice, we treat it as (the definitionally equal) `Set → Prop`. This means, the preferred way to
state that `x : Set` belongs to `A : Class` is to write `A x`. -/
def ClassCat :=
  Set SetCat deriving HasSubset,
  «./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler has_sep[has_sep] Set[Set]»,
  EmptyCollection, Inhabited,
  «./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler has_insert[has_insert] Set[Set]»,
  Union, Inter, HasCompl, SDiff
#align Class ClassCat

namespace ClassCat

/-- Coerce a ZFC set into a class -/
def ofSet (x : SetCat.{u}) : ClassCat.{u} :=
  { y | y ∈ x }
#align Class.of_Set ClassCat.ofSet

instance : Coe SetCat ClassCat :=
  ⟨ofSet⟩

/-- The universal class -/
def univ : ClassCat :=
  Set.univ
#align Class.univ ClassCat.univ

/-- Assert that `A` is a ZFC set satisfying `B` -/
def ToSet (B : ClassCat.{u}) (A : ClassCat.{u}) : Prop :=
  ∃ x, ↑x = A ∧ B x
#align Class.to_Set ClassCat.ToSet

/-- `A ∈ B` if `A` is a ZFC set which satisfies `B` -/
protected def Mem (A B : ClassCat.{u}) : Prop :=
  ToSet.{u} B A
#align Class.mem ClassCat.Mem

instance : Membership ClassCat ClassCat :=
  ⟨ClassCat.Mem⟩

theorem mem_univ {A : ClassCat.{u}} : A ∈ univ.{u} ↔ ∃ x : SetCat.{u}, ↑x = A :=
  exists_congr fun x => and_true_iff _
#align Class.mem_univ ClassCat.mem_univ

theorem mem_wf : @WellFounded ClassCat.{u} (· ∈ ·) :=
  ⟨by
    have H : ∀ x : SetCat.{u}, @Acc ClassCat.{u} (· ∈ ·) ↑x := by
      refine' fun a => SetCat.induction_on a fun x IH => ⟨x, _⟩
      rintro A ⟨z, rfl, hz⟩
      exact IH z hz
    · refine' fun A => ⟨A, _⟩
      rintro B ⟨x, rfl, hx⟩
      exact H x⟩
#align Class.mem_wf ClassCat.mem_wf

instance : WellFoundedRelation ClassCat :=
  ⟨_, mem_wf⟩

instance : IsAsymm ClassCat (· ∈ ·) :=
  mem_wf.IsAsymm

theorem mem_asymm {x y : ClassCat} : x ∈ y → y ∉ x :=
  asymm
#align Class.mem_asymm ClassCat.mem_asymm

theorem mem_irrefl (x : ClassCat) : x ∉ x :=
  irrefl x
#align Class.mem_irrefl ClassCat.mem_irrefl

/-- There is no universal set. -/
theorem univ_not_mem_univ : univ ∉ univ :=
  mem_irrefl _
#align Class.univ_not_mem_univ ClassCat.univ_not_mem_univ

/-- Convert a conglomerate (a collection of classes) into a class -/
def congToClass (x : Set ClassCat.{u}) : ClassCat.{u} :=
  { y | ↑y ∈ x }
#align Class.Cong_to_Class ClassCat.congToClass

/-- Convert a class into a conglomerate (a collection of classes) -/
def classToCong (x : ClassCat.{u}) : Set ClassCat.{u} :=
  { y | y ∈ x }
#align Class.Class_to_Cong ClassCat.classToCong

/-- The power class of a class is the class of all subclasses that are ZFC sets -/
def powerset (x : ClassCat) : ClassCat :=
  congToClass (Set.powerset x)
#align Class.powerset ClassCat.powerset

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The union of a class is the class of all members of ZFC sets in the class -/
def sUnion (x : ClassCat) : ClassCat :=
  ⋃₀ classToCong x
#align Class.sUnion ClassCat.sUnion

-- mathport name: Class.sUnion
prefix:110 "⋃₀ " => ClassCat.sUnion

theorem ofSet.inj {x y : SetCat.{u}} (h : (x : ClassCat.{u}) = y) : x = y :=
  SetCat.ext fun z => by
    change (x : ClassCat.{u}) z ↔ (y : ClassCat.{u}) z
    rw [h]
#align Class.of_Set.inj ClassCat.ofSet.inj

@[simp]
theorem to_Set_of_Set (A : ClassCat.{u}) (x : SetCat.{u}) : ToSet A x ↔ A x :=
  ⟨fun ⟨y, yx, py⟩ => by rwa [of_Set.inj yx] at py, fun px => ⟨x, rfl, px⟩⟩
#align Class.to_Set_of_Set ClassCat.to_Set_of_Set

@[simp]
theorem mem_hom_left (x : SetCat.{u}) (A : ClassCat.{u}) : (x : ClassCat.{u}) ∈ A ↔ A x :=
  to_Set_of_Set _ _
#align Class.mem_hom_left ClassCat.mem_hom_left

@[simp]
theorem mem_hom_right (x y : SetCat.{u}) : (y : ClassCat.{u}) x ↔ x ∈ y :=
  Iff.rfl
#align Class.mem_hom_right ClassCat.mem_hom_right

@[simp]
theorem subset_hom (x y : SetCat.{u}) : (x : ClassCat.{u}) ⊆ y ↔ x ⊆ y :=
  Iff.rfl
#align Class.subset_hom ClassCat.subset_hom

@[simp]
theorem sep_hom (p : ClassCat.{u}) (x : SetCat.{u}) :
    (↑({ y ∈ x | p y }) : ClassCat.{u}) = { y ∈ x | p y } :=
  Set.ext fun y => SetCat.mem_sep
#align Class.sep_hom ClassCat.sep_hom

@[simp]
theorem empty_hom : ↑(∅ : SetCat.{u}) = (∅ : ClassCat.{u}) :=
  Set.ext fun y => (iff_false_iff _).2 (SetCat.mem_empty y)
#align Class.empty_hom ClassCat.empty_hom

@[simp]
theorem insert_hom (x y : SetCat.{u}) : @insert SetCat.{u} ClassCat.{u} _ x y = ↑(insert x y) :=
  Set.ext fun z => Iff.symm SetCat.mem_insert_iff
#align Class.insert_hom ClassCat.insert_hom

@[simp]
theorem union_hom (x y : SetCat.{u}) : (x : ClassCat.{u}) ∪ y = (x ∪ y : SetCat.{u}) :=
  Set.ext fun z => Iff.symm SetCat.mem_union
#align Class.union_hom ClassCat.union_hom

@[simp]
theorem inter_hom (x y : SetCat.{u}) : (x : ClassCat.{u}) ∩ y = (x ∩ y : SetCat.{u}) :=
  Set.ext fun z => Iff.symm SetCat.mem_inter
#align Class.inter_hom ClassCat.inter_hom

@[simp]
theorem diff_hom (x y : SetCat.{u}) : (x : ClassCat.{u}) \ y = (x \ y : SetCat.{u}) :=
  Set.ext fun z => Iff.symm SetCat.mem_diff
#align Class.diff_hom ClassCat.diff_hom

@[simp]
theorem powerset_hom (x : SetCat.{u}) : powerset.{u} x = SetCat.powerset x :=
  Set.ext fun z => Iff.symm SetCat.mem_powerset
#align Class.powerset_hom ClassCat.powerset_hom

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem sUnion_hom (x : SetCat.{u}) : ⋃₀ (x : ClassCat.{u}) = ⋃₀ x :=
  Set.ext fun z => by
    refine' Iff.trans _ Set.mem_sUnion.symm
    exact ⟨fun ⟨_, ⟨a, rfl, ax⟩, za⟩ => ⟨a, ax, za⟩, fun ⟨a, ax, za⟩ => ⟨_, ⟨a, rfl, ax⟩, za⟩⟩
#align Class.sUnion_hom ClassCat.sUnion_hom

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The definite description operator, which is `{x}` if `{y | A y} = {x}` and `∅` otherwise. -/
def iota (A : ClassCat) : ClassCat :=
  ⋃₀ { x | ∀ y, A y ↔ y = x }
#align Class.iota ClassCat.iota

theorem iota_val (A : ClassCat) (x : SetCat) (H : ∀ y, A y ↔ y = x) : iota A = ↑x :=
  Set.ext fun y =>
    ⟨fun ⟨_, ⟨x', rfl, h⟩, yx'⟩ => by rwa [← (H x').1 <| (h x').2 rfl], fun yx =>
      ⟨_, ⟨x, rfl, H⟩, yx⟩⟩
#align Class.iota_val ClassCat.iota_val

/-- Unlike the other set constructors, the `iota` definite descriptor
  is a set for any set input, but not constructively so, so there is no
  associated `Class → Set` function. -/
theorem iota_ex (A) : iota.{u} A ∈ univ.{u} :=
  mem_univ.2 <|
    Or.elim (Classical.em <| ∃ x, ∀ y, A y ↔ y = x) (fun ⟨x, h⟩ => ⟨x, Eq.symm <| iota_val A x h⟩)
      fun hn =>
      ⟨∅, Set.ext fun z => empty_hom.symm ▸ ⟨False.ndrec _, fun ⟨_, ⟨x, rfl, H⟩, zA⟩ => hn ⟨x, H⟩⟩⟩
#align Class.iota_ex ClassCat.iota_ex

/-- Function value -/
def fval (F A : ClassCat.{u}) : ClassCat.{u} :=
  iota fun y => ToSet (fun x => F (SetCat.pair x y)) A
#align Class.fval ClassCat.fval

-- mathport name: «expr ′ »
infixl:100 " ′ " => fval

theorem fval_ex (F A : ClassCat.{u}) : F ′ A ∈ univ.{u} :=
  iota_ex _
#align Class.fval_ex ClassCat.fval_ex

end ClassCat

namespace SetCat

@[simp]
theorem map_fval {f : SetCat.{u} → SetCat.{u}} [H : PSet.Definable 1 f] {x y : SetCat.{u}}
    (h : y ∈ x) : (SetCat.map f x ′ y : ClassCat.{u}) = f y :=
  ClassCat.iota_val _ _ fun z => by
    rw [ClassCat.to_Set_of_Set, ClassCat.mem_hom_right, mem_map]
    exact
      ⟨fun ⟨w, wz, pr⟩ => by
        let ⟨wy, fw⟩ := SetCat.pair_injective pr
        rw [← fw, wy], fun e => by
        subst e
        exact ⟨_, h, rfl⟩⟩
#align Set.map_fval SetCat.map_fval

variable (x : SetCat.{u}) (h : ∅ ∉ x)

/-- A choice function on the class of nonempty ZFC sets. -/
noncomputable def choice : SetCat :=
  @map (fun y => Classical.epsilon fun z => z ∈ y) (Classical.allDefinable _) x
#align Set.choice SetCat.choice

include h

theorem choice_mem_aux (y : SetCat.{u}) (yx : y ∈ x) :
    (Classical.epsilon fun z : SetCat.{u} => z ∈ y) ∈ y :=
  (@Classical.epsilon_spec _ fun z : SetCat.{u} => z ∈ y) <|
    by_contradiction fun n => h <| by rwa [← (eq_empty y).2 fun z zx => n ⟨z, zx⟩]
#align Set.choice_mem_aux SetCat.choice_mem_aux

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem choice_is_func : IsFunc x (⋃₀ x) (choice x) :=
  (@map_is_func _ (Classical.allDefinable _) _ _).2 fun y yx =>
    mem_sUnion.2 ⟨y, yx, choice_mem_aux x h y yx⟩
#align Set.choice_is_func SetCat.choice_is_func

theorem choice_mem (y : SetCat.{u}) (yx : y ∈ x) :
    (choice x ′ y : ClassCat.{u}) ∈ (y : ClassCat.{u}) := by
  delta choice
  rw [map_fval yx, ClassCat.mem_hom_left, ClassCat.mem_hom_right]
  exact choice_mem_aux x h y yx
#align Set.choice_mem SetCat.choice_mem

end SetCat
