/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Small.Basic
import Mathlib.Order.WellFounded

#align_import set_theory.zfc.basic from "leanprover-community/mathlib"@"f0b3759a8ef0bd8239ecdaa5e1089add5feebe1a"

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

* `PSet`: Pre-set. A pre-set is inductively defined by its indexing type and its members, which are
  themselves pre-sets.
* `ZFSet`: ZFC set. Defined as `PSet` quotiented by `PSet.Equiv`, the extensional equivalence.
* `Class`: Class. Defined as `Set ZFSet`.
* `ZFSet.choice`: Axiom of choice. Proved from Lean's axiom of choice.

## Other definitions

* `Arity α n`: `n`-ary function `α → α → ... → α`. Defined inductively.
* `Arity.const a n`: `n`-ary constant function equal to `a`.
* `PSet.Type`: Underlying type of a pre-set.
* `PSet.Func`: Underlying family of pre-sets of a pre-set.
* `PSet.Equiv`: Extensional equivalence of pre-sets. Defined inductively.
* `PSet.omega`, `ZFSet.omega`: The von Neumann ordinal `ω` as a `PSet`, as a `Set`.
* `PSet.Arity.Equiv`: Extensional equivalence of `n`-ary `PSet`-valued functions. Extension of
  `PSet.Equiv`.
* `PSet.Resp`: Collection of `n`-ary `PSet`-valued functions that respect extensional equivalence.
* `PSet.eval`: Turns a `PSet`-valued function that respect extensional equivalence into a
  `ZFSet`-valued function.
* `Classical.allDefinable`: All functions are classically definable.
* `ZFSet.IsFunc` : Predicate that a ZFC set is a subset of `x × y` that can be considered as a ZFC
  function `x → y`. That is, each member of `x` is related by the ZFC set to exactly one member of
  `y`.
* `ZFSet.funs`: ZFC set of ZFC functions `x → y`.
* `ZFSet.Hereditarily p x`: Predicate that every set in the transitive closure of `x` has property
  `p`.
* `Class.iota`: Definite description operator.

## Notes

To avoid confusion between the Lean `set` and the ZFC `Set`, docstrings in this file refer to them
respectively as "`set`" and "ZFC set".

## TODO

Prove `Set.map_definable_aux` computably.
-/

-- Porting note: Lean 3 uses `Set` for `ZFSet`.
set_option linter.uppercaseLean3 false

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
def const {α : Type u} (a : α) : ∀ n, Arity α n
  | 0 => a
  | n + 1 => fun _ => const a n
#align arity.const Arity.const

@[simp]
theorem const_zero {α : Type u} (a : α) : const a 0 = a :=
  rfl
#align arity.const_zero Arity.const_zero

@[simp]
theorem const_succ {α : Type u} (a : α) (n : ℕ) : const a n.succ = fun _ => const a n :=
  rfl
#align arity.const_succ Arity.const_succ

theorem const_succ_apply {α : Type u} (a : α) (n : ℕ) (x : α) : const a n.succ x = const a n :=
  rfl
#align arity.const_succ_apply Arity.const_succ_apply

instance Arity.inhabited {α n} [Inhabited α] : Inhabited (Arity α n) :=
  ⟨const default _⟩
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

protected theorem Equiv.comm {x y} : Equiv x y ↔ Equiv y x :=
  ⟨Equiv.symm, Equiv.symm⟩
#align pSet.equiv.comm PSet.Equiv.comm

@[trans]
protected theorem Equiv.trans {x y z} (h1 : Equiv x y) (h2 : Equiv y z) : Equiv x z :=
  h1.euc h2.symm
#align pSet.equiv.trans PSet.Equiv.trans

protected theorem equiv_of_isEmpty (x y : PSet) [IsEmpty x.Type] [IsEmpty y.Type] : Equiv x y :=
  equiv_iff.2 <| by simp
                    -- 🎉 no goals
#align pSet.equiv_of_is_empty PSet.equiv_of_isEmpty

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
    -- ⊢ ∃ b, Equiv (Func x a) (Func z b)
    cases' hyz b with c hc
    -- ⊢ ∃ b, Equiv (Func x a) (Func z b)
    exact ⟨c, hb.trans hc⟩⟩
    -- 🎉 no goals

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
  -- ⊢ Func (mk α✝ A✝) i ∈ mk α✝ A✝
  apply Mem.mk
  -- 🎉 no goals
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
      -- ⊢ Acc (fun x x_1 => x ∈ x_1) (mk γ C)
      cases' H.exists_right b with a ha
      -- ⊢ Acc (fun x x_1 => x ∈ x_1) (mk γ C)
      have H := ha.trans hc.symm
      -- ⊢ Acc (fun x x_1 => x ∈ x_1) (mk γ C)
      rw [mk_func] at H
      -- ⊢ Acc (fun x x_1 => x ∈ x_1) (mk γ C)
      exact mem_wf_aux H⟩
      -- 🎉 no goals

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
protected def empty : PSet :=
  ⟨_, PEmpty.elim⟩
#align pSet.empty PSet.empty

instance : EmptyCollection PSet :=
  ⟨PSet.empty⟩

instance : Inhabited PSet :=
  ⟨∅⟩

instance : IsEmpty («Type» ∅) :=
  ⟨PEmpty.elim⟩

@[simp]
theorem not_mem_empty (x : PSet.{u}) : x ∉ (∅ : PSet.{u}) :=
  IsEmpty.exists_iff.1
#align pSet.not_mem_empty PSet.not_mem_empty

@[simp]
theorem toSet_empty : toSet ∅ = ∅ := by simp [toSet]
                                        -- 🎉 no goals
#align pSet.to_set_empty PSet.toSet_empty

@[simp]
theorem empty_subset (x : PSet.{u}) : (∅ : PSet) ⊆ x := fun x => x.elim
#align pSet.empty_subset PSet.empty_subset

@[simp]
theorem not_nonempty_empty : ¬PSet.Nonempty ∅ := by simp [PSet.Nonempty]
                                                    -- 🎉 no goals
#align pSet.not_nonempty_empty PSet.not_nonempty_empty

protected theorem equiv_empty (x : PSet) [IsEmpty x.Type] : Equiv x ∅ :=
  PSet.equiv_of_isEmpty x _
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
def sUnion (a : PSet) : PSet :=
  ⟨Σx, (a.Func x).Type, fun ⟨x, y⟩ => (a.Func x).Func y⟩
#align pSet.sUnion PSet.sUnion

@[inherit_doc]
prefix:110 "⋃₀ " => sUnion

@[simp]
theorem mem_sUnion : ∀ {x y : PSet.{u}}, y ∈ ⋃₀ x ↔ ∃ z ∈ x, y ∈ z
  | ⟨α, A⟩, y =>
    ⟨fun ⟨⟨a, c⟩, (e : Equiv y ((A a).Func c))⟩ =>
      have : Func (A a) c ∈ mk (A a).Type (A a).Func := Mem.mk (A a).Func c
      ⟨_, Mem.mk _ _, (Mem.congr_left e).2 (by rwa [eta] at this)⟩,
                                               -- 🎉 no goals
      fun ⟨⟨β, B⟩, ⟨a, (e : Equiv (mk β B) (A a))⟩, ⟨b, yb⟩⟩ => by
      rw [← eta (A a)] at e
      -- ⊢ y ∈ ⋃₀ mk α A
      exact
        let ⟨βt, _⟩ := e
        let ⟨c, bc⟩ := βt b
        ⟨⟨a, c⟩, yb.trans bc⟩⟩
#align pSet.mem_sUnion PSet.mem_sUnion

@[simp]
theorem toSet_sUnion (x : PSet.{u}) : (⋃₀ x).toSet = ⋃₀ (toSet '' x.toSet) := by
  ext
  -- ⊢ x✝ ∈ toSet (⋃₀ x) ↔ x✝ ∈ ⋃₀ (toSet '' toSet x)
  simp
  -- 🎉 no goals
#align pSet.to_set_sUnion PSet.toSet_sUnion

/-- The image of a function from pre-sets to pre-sets. -/
def image (f : PSet.{u} → PSet.{u}) (x : PSet.{u}) : PSet :=
  ⟨x.Type, f ∘ x.Func⟩
#align pSet.image PSet.image

-- Porting note: H arguments made explicit.
theorem mem_image {f : PSet.{u} → PSet.{u}} (H : ∀ x y, Equiv x y → Equiv (f x) (f y)) :
    ∀ {x y : PSet.{u}}, y ∈ image f x ↔ ∃ z ∈ x, Equiv y (f z)
  | ⟨_, A⟩, _ =>
    ⟨fun ⟨a, ya⟩ => ⟨A a, Mem.mk A a, ya⟩, fun ⟨_, ⟨a, za⟩, yz⟩ => ⟨a, yz.trans <| H _ _ za⟩⟩
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

theorem Arity.equiv_const {a : PSet.{u}} : ∀ n, Arity.Equiv (Arity.const a n) (Arity.const a n)
  | 0 => Equiv.rfl
  | _ + 1 => fun _ _ _ => Arity.equiv_const _
#align pSet.arity.equiv_const PSet.Arity.equiv_const

/-- `resp n` is the collection of n-ary functions on `PSet` that respect
  equivalence, i.e. when the inputs are equivalent the output is as well. -/
def Resp (n) :=
  { x : Arity PSet.{u} n // Arity.Equiv x x }
#align pSet.resp PSet.Resp

instance Resp.inhabited {n} : Inhabited (Resp n) :=
  ⟨⟨Arity.const default _, Arity.equiv_const _⟩⟩
#align pSet.resp.inhabited PSet.Resp.inhabited

/-- The `n`-ary image of a `(n + 1)`-ary function respecting equivalence as a function respecting
equivalence. -/
def Resp.f {n} (f : Resp (n + 1)) (x : PSet) : Resp n :=
  ⟨f.1 x, f.2 _ _ <| Equiv.refl x⟩
#align pSet.resp.f PSet.Resp.f

/-- Function equivalence for functions respecting equivalence. See `PSet.Arity.Equiv`. -/
def Resp.Equiv {n} (a b : Resp n) : Prop :=
  Arity.Equiv a.1 b.1
#align pSet.resp.equiv PSet.Resp.Equiv

@[refl]
protected theorem Resp.Equiv.refl {n} (a : Resp n) : Resp.Equiv a a :=
  a.2
#align pSet.resp.equiv.refl PSet.Resp.Equiv.refl

protected theorem Resp.Equiv.euc :
    ∀ {n} {a b c : Resp n}, Resp.Equiv a b → Resp.Equiv c b → Resp.Equiv a c
  | 0, _, _, _, hab, hcb => PSet.Equiv.euc hab hcb
  | n + 1, a, b, c, hab, hcb => fun x y h =>
    @Resp.Equiv.euc n (a.f x) (b.f y) (c.f y) (hab _ _ h) (hcb _ _ <| PSet.Equiv.refl y)
#align pSet.resp.equiv.euc PSet.Resp.Equiv.euc

@[symm]
protected theorem Resp.Equiv.symm {n} {a b : Resp n} : Resp.Equiv a b → Resp.Equiv b a :=
  (Resp.Equiv.refl b).euc
#align pSet.resp.equiv.symm PSet.Resp.Equiv.symm

@[trans]
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

/-- Helper function for `PSet.eval`. -/
def evalAux :
    ∀ {n}, { f : Resp n → Arity ZFSet.{u} n // ∀ a b : Resp n, Resp.Equiv a b → f a = f b }
  | 0 => ⟨fun a => ⟦a.1⟧, fun _ _ h => Quotient.sound h⟩
  | n + 1 =>
    let F : Resp (n + 1) → Arity ZFSet (n + 1) := fun a =>
      @Quotient.lift _ _ PSet.setoid (fun x => evalAux.1 (a.f x)) fun _ _ h =>
        evalAux.2 _ _ (a.2 _ _ h)
    ⟨F, fun b c h =>
      funext <|
        (@Quotient.ind _ _ fun q => F b q = F c q) fun z =>
          evalAux.2 (Resp.f b z) (Resp.f c z) (h _ _ (PSet.Equiv.refl z))⟩
#align pSet.resp.eval_aux PSet.Resp.evalAux

/-- An equivalence-respecting function yields an n-ary ZFC set function. -/
def eval (n) : Resp n → Arity ZFSet.{u} n :=
  evalAux.1
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
noncomputable def allDefinable : ∀ {n} (F : Arity ZFSet n), Definable n F
  | 0, F =>
    let p := @Quotient.exists_rep PSet _ F
    @Definable.EqMk 0 ⟨choose p, Equiv.rfl⟩ _ (choose_spec p)
  | n + 1, (F : Arity ZFSet (n + 1)) => by
    have I := fun x => allDefinable (F x)
    -- ⊢ Definable (n + 1) F
    refine' @Definable.EqMk (n + 1) ⟨fun x : PSet => (@Definable.Resp _ _ (I ⟦x⟧)).1, _⟩ _ _
    -- ⊢ Arity.Equiv (fun x => ↑(Definable.Resp (F (Quotient.mk setoid x)))) fun x => …
    · dsimp [Arity.Equiv]
      -- ⊢ ∀ (x y : PSet), PSet.Equiv x y → Arity.Equiv ↑(Definable.Resp (F (Quotient.m …
      intro x y h
      -- ⊢ Arity.Equiv ↑(Definable.Resp (F (Quotient.mk setoid x))) ↑(Definable.Resp (F …
      rw [@Quotient.sound PSet _ _ _ h]
      -- ⊢ Arity.Equiv ↑(Definable.Resp (F (Quotient.mk setoid y))) ↑(Definable.Resp (F …
      exact (Definable.Resp (F ⟦y⟧)).2
      -- 🎉 no goals
    refine' funext fun q => Quotient.inductionOn q fun x => _
    -- ⊢ Resp.eval (n + 1) { val := fun x => ↑(Definable.Resp (F (Quotient.mk setoid  …
    simp_rw [Resp.eval_val, Resp.f]
    -- ⊢ Resp.eval n { val := ↑(Definable.Resp (F (Quotient.mk setoid x))), property  …
    exact @Definable.eq _ (F ⟦x⟧) (I ⟦x⟧)
    -- 🎉 no goals
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
  Quotient.inductionOn x fun a => by
    let f : a.Type → (mk a).toSet := fun i => ⟨mk <| a.Func i, func_mem a i⟩
    -- ⊢ Small.{u, u + 1} ↑(toSet (Quotient.mk setoid a))
    suffices Function.Surjective f by exact small_of_surjective this
    -- ⊢ Function.Surjective f
    rintro ⟨y, hb⟩
    -- ⊢ ∃ a_1, f a_1 = { val := y, property := hb }
    induction y using Quotient.inductionOn
    -- ⊢ ∃ a_1, f a_1 = { val := Quotient.mk setoid a✝, property := hb }
    cases' hb with i h
    -- ⊢ ∃ a_1, f a_1 = { val := Quotient.mk setoid a✝, property := (_ : ∃ b, PSet.Eq …
    exact ⟨i, Subtype.coe_injective (Quotient.sound h.symm)⟩
    -- 🎉 no goals
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
  -- 🎉 no goals
#align Set.to_set_subset_iff ZFSet.toSet_subset_iff

@[ext]
theorem ext {x y : ZFSet.{u}} : (∀ z : ZFSet.{u}, z ∈ x ↔ z ∈ y) → x = y :=
  Quotient.inductionOn₂ x y fun _ _ h => Quotient.sound (Mem.ext fun w => h ⟦w⟧)
#align Set.ext ZFSet.ext

theorem ext_iff {x y : ZFSet.{u}} : x = y ↔ ∀ z : ZFSet.{u}, z ∈ x ↔ z ∈ y :=
  ⟨fun h => by simp [h], ext⟩
               -- 🎉 no goals
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
theorem not_mem_empty (x) : x ∉ (∅ : ZFSet.{u}) :=
  Quotient.inductionOn x PSet.not_mem_empty
#align Set.not_mem_empty ZFSet.not_mem_empty

@[simp]
theorem toSet_empty : toSet ∅ = ∅ := by simp [toSet]
                                        -- 🎉 no goals
#align Set.to_set_empty ZFSet.toSet_empty

@[simp]
theorem empty_subset (x : ZFSet.{u}) : (∅ : ZFSet) ⊆ x :=
  Quotient.inductionOn x fun y => subset_iff.2 <| PSet.empty_subset y
#align Set.empty_subset ZFSet.empty_subset

@[simp]
theorem not_nonempty_empty : ¬ZFSet.Nonempty ∅ := by simp [ZFSet.Nonempty]
                                                     -- 🎉 no goals
#align Set.not_nonempty_empty ZFSet.not_nonempty_empty

@[simp]
theorem nonempty_mk_iff {x : PSet} : (mk x).Nonempty ↔ x.Nonempty := by
  refine' ⟨_, fun ⟨a, h⟩ => ⟨mk a, h⟩⟩
  -- ⊢ ZFSet.Nonempty (mk x) → PSet.Nonempty x
  rintro ⟨a, h⟩
  -- ⊢ PSet.Nonempty x
  induction a using Quotient.inductionOn
  -- ⊢ PSet.Nonempty x
  exact ⟨_, h⟩
  -- 🎉 no goals
#align Set.nonempty_mk_iff ZFSet.nonempty_mk_iff

theorem eq_empty (x : ZFSet.{u}) : x = ∅ ↔ ∀ y : ZFSet.{u}, y ∉ x := by
  rw [ext_iff]
  -- ⊢ (∀ (z : ZFSet), z ∈ x ↔ z ∈ ∅) ↔ ∀ (y : ZFSet), ¬y ∈ x
  simp
  -- 🎉 no goals
#align Set.eq_empty ZFSet.eq_empty

theorem eq_empty_or_nonempty (u : ZFSet) : u = ∅ ∨ u.Nonempty := by
  rw [eq_empty, ← not_exists]
  -- ⊢ (¬∃ x, x ∈ u) ∨ ZFSet.Nonempty u
  apply em'
  -- 🎉 no goals
#align Set.eq_empty_or_nonempty ZFSet.eq_empty_or_nonempty

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
        | ⟨some a, ha⟩ => Or.inr ⟨a, ha⟩
        | ⟨none, h⟩ => Or.inl (Quotient.sound h),
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
  -- ⊢ x✝ ∈ toSet (insert x y) ↔ x✝ ∈ insert x (toSet y)
  simp
  -- 🎉 no goals
#align Set.to_set_insert ZFSet.toSet_insert

@[simp]
theorem mem_singleton {x y : ZFSet.{u}} : x ∈ @singleton ZFSet.{u} ZFSet.{u} _ y ↔ x = y :=
  Iff.trans mem_insert_iff
    ⟨fun o => Or.rec (fun h => h) (fun n => absurd n (not_mem_empty _)) o, Or.inl⟩
#align Set.mem_singleton ZFSet.mem_singleton

@[simp]
theorem toSet_singleton (x : ZFSet) : ({x} : ZFSet).toSet = {x} := by
  ext
  -- ⊢ x✝ ∈ toSet {x} ↔ x✝ ∈ {x}
  simp
  -- 🎉 no goals
#align Set.to_set_singleton ZFSet.toSet_singleton

theorem insert_nonempty (u v : ZFSet) : (insert u v).Nonempty :=
  ⟨u, mem_insert u v⟩
#align Set.insert_nonempty ZFSet.insert_nonempty

theorem singleton_nonempty (u : ZFSet) : ZFSet.Nonempty {u} :=
  insert_nonempty u ∅
#align Set.singleton_nonempty ZFSet.singleton_nonempty

theorem mem_pair {x y z : ZFSet.{u}} : x ∈ ({y, z} : ZFSet) ↔ x = y ∨ x = z := by
  simp
  -- 🎉 no goals
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
          -- ⊢ insert (mk (Func PSet.omega { down := n })) (mk (Func PSet.omega { down := n …
          rfl⟩
          -- 🎉 no goals
#align Set.omega_succ ZFSet.omega_succ

/-- `{x ∈ a | p x}` is the set of elements in `a` satisfying `p` -/
protected def sep (p : ZFSet → Prop) : ZFSet → ZFSet :=
  Resp.eval 1
    ⟨PSet.sep fun y => p (mk y), fun ⟨α, A⟩ ⟨β, B⟩ ⟨αβ, βα⟩ =>
      ⟨fun ⟨a, pa⟩ =>
        let ⟨b, hb⟩ := αβ a
        ⟨⟨b, by simpa only [mk_func, ← ZFSet.sound hb]⟩, hb⟩,
                -- 🎉 no goals
        fun ⟨b, pb⟩ =>
        let ⟨a, ha⟩ := βα b
        ⟨⟨a, by simpa only [mk_func, ZFSet.sound ha]⟩, ha⟩⟩⟩
                -- 🎉 no goals
#align Set.sep ZFSet.sep

-- Porting note: the { x | p x } notation appears to be disabled in Lean 4.
instance : Sep ZFSet ZFSet :=
  ⟨ZFSet.sep⟩

@[simp]
theorem mem_sep {p : ZFSet.{u} → Prop} {x y : ZFSet.{u}} :
    y ∈ ZFSet.sep p x ↔ y ∈ x ∧ p y :=
  Quotient.inductionOn₂ x y fun ⟨α, A⟩ y =>
    ⟨fun ⟨⟨a, pa⟩, h⟩ => ⟨⟨a, h⟩, by rwa [@Quotient.sound PSet _ _ _ h]⟩, fun ⟨⟨a, h⟩, pa⟩ =>
                                     -- 🎉 no goals
      ⟨⟨a, by
          rw [mk_func] at h
          -- ⊢ p (mk (Func (PSet.mk α A) a))
          rwa [mk_func, ← ZFSet.sound h]⟩,
          -- 🎉 no goals
        h⟩⟩
#align Set.mem_sep ZFSet.mem_sep

@[simp]
theorem toSet_sep (a : ZFSet) (p : ZFSet → Prop) :
    (ZFSet.sep p a).toSet = { x ∈ a.toSet | p x } := by
  ext
  -- ⊢ x✝ ∈ toSet (ZFSet.sep p a) ↔ x✝ ∈ {x | x ∈ toSet a ∧ p x}
  simp
  -- 🎉 no goals
#align Set.to_set_sep ZFSet.toSet_sep

/-- The powerset operation, the collection of subsets of a ZFC set -/
def powerset : ZFSet → ZFSet :=
  Resp.eval 1
    ⟨PSet.powerset, fun ⟨_, A⟩ ⟨_, B⟩ ⟨αβ, βα⟩ =>
      ⟨fun p =>
        ⟨{ b | ∃ a, p a ∧ Equiv (A a) (B b) }, fun ⟨a, pa⟩ =>
          let ⟨b, ab⟩ := αβ a
          ⟨⟨b, a, pa, ab⟩, ab⟩,
          fun ⟨_, a, pa, ab⟩ => ⟨⟨a, pa⟩, ab⟩⟩,
        fun q =>
        ⟨{ a | ∃ b, q b ∧ Equiv (A a) (B b) }, fun ⟨_, b, qb, ab⟩ => ⟨⟨b, qb⟩, ab⟩, fun ⟨b, qb⟩ =>
          let ⟨a, ab⟩ := βα b
          ⟨⟨a, b, qb, ab⟩, ab⟩⟩⟩⟩
#align Set.powerset ZFSet.powerset

@[simp]
theorem mem_powerset {x y : ZFSet.{u}} : y ∈ powerset x ↔ y ⊆ x :=
  Quotient.inductionOn₂ x y fun ⟨α, A⟩ ⟨β, B⟩ =>
    show (⟨β, B⟩ : PSet.{u}) ∈ PSet.powerset.{u} ⟨α, A⟩ ↔ _ by simp [mem_powerset, subset_iff]
                                                               -- 🎉 no goals
#align Set.mem_powerset ZFSet.mem_powerset

theorem sUnion_lem {α β : Type u} (A : α → PSet) (B : β → PSet) (αβ : ∀ a, ∃ b, Equiv (A a) (B b)) :
    ∀ a, ∃ b, Equiv ((sUnion ⟨α, A⟩).Func a) ((sUnion ⟨β, B⟩).Func b)
  | ⟨a, c⟩ => by
    let ⟨b, hb⟩ := αβ a
    -- ⊢ ∃ b, PSet.Equiv (Func (⋃₀ PSet.mk α A) { fst := a, snd := c }) (Func (⋃₀ PSe …
    induction' ea : A a with γ Γ
    -- ⊢ ∃ b, PSet.Equiv (Func (⋃₀ PSet.mk α A) { fst := a, snd := c }) (Func (⋃₀ PSe …
    induction' eb : B b with δ Δ
    -- ⊢ ∃ b, PSet.Equiv (Func (⋃₀ PSet.mk α A) { fst := a, snd := c }) (Func (⋃₀ PSe …
    rw [ea, eb] at hb
    -- ⊢ ∃ b, PSet.Equiv (Func (⋃₀ PSet.mk α A) { fst := a, snd := c }) (Func (⋃₀ PSe …
    cases' hb with γδ δγ
    -- ⊢ ∃ b, PSet.Equiv (Func (⋃₀ PSet.mk α A) { fst := a, snd := c }) (Func (⋃₀ PSe …
    let c : (A a).Type := c
    -- ⊢ ∃ b, PSet.Equiv (Func (⋃₀ PSet.mk α A) { fst := a, snd := c✝ }) (Func (⋃₀ PS …
    let ⟨d, hd⟩ := γδ (by rwa [ea] at c)
    -- ⊢ ∃ b, PSet.Equiv (Func (⋃₀ PSet.mk α A) { fst := a, snd := c✝ }) (Func (⋃₀ PS …
    use ⟨b, Eq.ndrec d (Eq.symm eb)⟩
    -- ⊢ PSet.Equiv (Func (⋃₀ PSet.mk α A) { fst := a, snd := c✝ }) (Func (⋃₀ PSet.mk …
    change PSet.Equiv ((A a).Func c) ((B b).Func (Eq.ndrec d eb.symm))
    -- ⊢ PSet.Equiv (Func (A a) c) (Func (B b) ((_ : PSet.mk δ Δ = B b) ▸ d))
    match A a, B b, ea, eb, c, d, hd with
    | _, _, rfl, rfl, _, _, hd => exact hd
#align Set.sUnion_lem ZFSet.sUnion_lem

/-- The union operator, the collection of elements of elements of a ZFC set -/
def sUnion : ZFSet → ZFSet :=
  Resp.eval 1
    ⟨PSet.sUnion, fun ⟨_, A⟩ ⟨_, B⟩ ⟨αβ, βα⟩ =>
      ⟨sUnion_lem A B αβ, fun a =>
        Exists.elim
          (sUnion_lem B A (fun b => Exists.elim (βα b) fun c hc => ⟨c, PSet.Equiv.symm hc⟩) a)
          fun b hb => ⟨b, PSet.Equiv.symm hb⟩⟩⟩
#align Set.sUnion ZFSet.sUnion

@[inherit_doc]
prefix:110 "⋃₀ " => ZFSet.sUnion

/-- The intersection operator, the collection of elements in all of the elements of a ZFC set. We
special-case `⋂₀ ∅ = ∅`. -/
noncomputable def sInter (x : ZFSet) : ZFSet := by
   classical exact if h : x.Nonempty then ZFSet.sep (fun y => ∀ z ∈ x, y ∈ z) h.some else ∅
   -- 🎉 no goals
#align Set.sInter ZFSet.sInter

@[inherit_doc]
prefix:110 "⋂₀ " => ZFSet.sInter

@[simp]
theorem mem_sUnion {x y : ZFSet.{u}} : y ∈ ⋃₀ x ↔ ∃ z ∈ x, y ∈ z :=
  Quotient.inductionOn₂ x y fun _ _ =>
    Iff.trans PSet.mem_sUnion
      ⟨fun ⟨z, h⟩ => ⟨⟦z⟧, h⟩, fun ⟨z, h⟩ => Quotient.inductionOn z (fun z h => ⟨z, h⟩) h⟩
#align Set.mem_sUnion ZFSet.mem_sUnion

theorem mem_sInter {x y : ZFSet} (h : x.Nonempty) : y ∈ ⋂₀ x ↔ ∀ z ∈ x, y ∈ z := by
  rw [sInter, dif_pos h]
  -- ⊢ y ∈ ZFSet.sep (fun y => ∀ (z : ZFSet), z ∈ x → y ∈ z) (Set.Nonempty.some h)  …
  simp only [mem_toSet, mem_sep, and_iff_right_iff_imp]
  -- ⊢ (∀ (z : ZFSet), z ∈ x → y ∈ z) → y ∈ Set.Nonempty.some h
  exact fun H => H _ h.some_mem
  -- 🎉 no goals
#align Set.mem_sInter ZFSet.mem_sInter

@[simp]
theorem sUnion_empty : ⋃₀ (∅ : ZFSet.{u}) = ∅ := by
  ext
  -- ⊢ z✝ ∈ ⋃₀ ∅ ↔ z✝ ∈ ∅
  simp
  -- 🎉 no goals
#align Set.sUnion_empty ZFSet.sUnion_empty

@[simp]
theorem sInter_empty : ⋂₀ (∅ : ZFSet) = ∅ := dif_neg <| by simp
                                                           -- 🎉 no goals
#align Set.sInter_empty ZFSet.sInter_empty

theorem mem_of_mem_sInter {x y z : ZFSet} (hy : y ∈ ⋂₀ x) (hz : z ∈ x) : y ∈ z := by
  rcases eq_empty_or_nonempty x with (rfl | hx)
  -- ⊢ y ∈ z
  · exact (not_mem_empty z hz).elim
    -- 🎉 no goals
  · exact (mem_sInter hx).1 hy z hz
    -- 🎉 no goals
#align Set.mem_of_mem_sInter ZFSet.mem_of_mem_sInter

theorem mem_sUnion_of_mem {x y z : ZFSet} (hy : y ∈ z) (hz : z ∈ x) : y ∈ ⋃₀ x :=
  mem_sUnion.2 ⟨z, hz, hy⟩
#align Set.mem_sUnion_of_mem ZFSet.mem_sUnion_of_mem

theorem not_mem_sInter_of_not_mem {x y z : ZFSet} (hy : ¬y ∈ z) (hz : z ∈ x) : ¬y ∈ ⋂₀ x :=
  fun hx => hy <| mem_of_mem_sInter hx hz
#align Set.not_mem_sInter_of_not_mem ZFSet.not_mem_sInter_of_not_mem

@[simp]
theorem sUnion_singleton {x : ZFSet.{u}} : ⋃₀ ({x} : ZFSet) = x :=
  ext fun y => by simp_rw [mem_sUnion, mem_singleton, exists_eq_left]
                  -- 🎉 no goals
#align Set.sUnion_singleton ZFSet.sUnion_singleton

@[simp]
theorem sInter_singleton {x : ZFSet.{u}} : ⋂₀ ({x} : ZFSet) = x :=
  ext fun y => by simp_rw [mem_sInter (singleton_nonempty x), mem_singleton, forall_eq]
                  -- 🎉 no goals
#align Set.sInter_singleton ZFSet.sInter_singleton

@[simp]
theorem toSet_sUnion (x : ZFSet.{u}) : (⋃₀ x).toSet = ⋃₀ (toSet '' x.toSet) := by
  ext
  -- ⊢ x✝ ∈ toSet (⋃₀ x) ↔ x✝ ∈ ⋃₀ (toSet '' toSet x)
  simp
  -- 🎉 no goals
#align Set.to_set_sUnion ZFSet.toSet_sUnion

theorem toSet_sInter {x : ZFSet.{u}} (h : x.Nonempty) : (⋂₀ x).toSet = ⋂₀ (toSet '' x.toSet) := by
  ext
  -- ⊢ x✝ ∈ toSet (⋂₀ x) ↔ x✝ ∈ ⋂₀ (toSet '' toSet x)
  simp [mem_sInter h]
  -- 🎉 no goals
#align Set.to_set_sInter ZFSet.toSet_sInter

theorem singleton_injective : Function.Injective (@singleton ZFSet ZFSet _) := fun x y H => by
  let this := congr_arg sUnion H
  -- ⊢ x = y
  rwa [sUnion_singleton, sUnion_singleton] at this
  -- 🎉 no goals
#align Set.singleton_injective ZFSet.singleton_injective

@[simp]
theorem singleton_inj {x y : ZFSet} : ({x} : ZFSet) = {y} ↔ x = y :=
  singleton_injective.eq_iff
#align Set.singleton_inj ZFSet.singleton_inj

/-- The binary union operation -/
protected def union (x y : ZFSet.{u}) : ZFSet.{u} :=
  ⋃₀ {x, y}
#align Set.union ZFSet.union

/-- The binary intersection operation -/
protected def inter (x y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∈ y) x -- { z ∈ x | z ∈ y }
#align Set.inter ZFSet.inter

/-- The set difference operation -/
protected def diff (x y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∉ y) x -- { z ∈ x | z ∉ y }
#align Set.diff ZFSet.diff

instance : Union ZFSet :=
  ⟨ZFSet.union⟩

instance : Inter ZFSet :=
  ⟨ZFSet.inter⟩

instance : SDiff ZFSet :=
  ⟨ZFSet.diff⟩

@[simp]
theorem toSet_union (x y : ZFSet.{u}) : (x ∪ y).toSet = x.toSet ∪ y.toSet := by
  change (⋃₀ {x, y}).toSet = _
  -- ⊢ toSet (⋃₀ {x, y}) = toSet x ∪ toSet y
  simp
  -- 🎉 no goals
#align Set.to_set_union ZFSet.toSet_union

@[simp]
theorem toSet_inter (x y : ZFSet.{u}) : (x ∩ y).toSet = x.toSet ∩ y.toSet := by
  change (ZFSet.sep (fun z => z ∈ y) x).toSet = _
  -- ⊢ toSet (ZFSet.sep (fun z => z ∈ y) x) = toSet x ∩ toSet y
  ext
  -- ⊢ x✝ ∈ toSet (ZFSet.sep (fun z => z ∈ y) x) ↔ x✝ ∈ toSet x ∩ toSet y
  simp
  -- 🎉 no goals
#align Set.to_set_inter ZFSet.toSet_inter

@[simp]
theorem toSet_sdiff (x y : ZFSet.{u}) : (x \ y).toSet = x.toSet \ y.toSet := by
  change (ZFSet.sep (fun z => z ∉ y) x).toSet = _
  -- ⊢ toSet (ZFSet.sep (fun z => ¬z ∈ y) x) = toSet x \ toSet y
  ext
  -- ⊢ x✝ ∈ toSet (ZFSet.sep (fun z => ¬z ∈ y) x) ↔ x✝ ∈ toSet x \ toSet y
  simp
  -- 🎉 no goals
#align Set.to_set_sdiff ZFSet.toSet_sdiff

@[simp]
theorem mem_union {x y z : ZFSet.{u}} : z ∈ x ∪ y ↔ z ∈ x ∨ z ∈ y := by
  rw [← mem_toSet]
  -- ⊢ z ∈ toSet (x ∪ y) ↔ z ∈ x ∨ z ∈ y
  simp
  -- 🎉 no goals
#align Set.mem_union ZFSet.mem_union

@[simp]
theorem mem_inter {x y z : ZFSet.{u}} : z ∈ x ∩ y ↔ z ∈ x ∧ z ∈ y :=
  @mem_sep (fun z : ZFSet.{u} => z ∈ y) x z
#align Set.mem_inter ZFSet.mem_inter

@[simp]
theorem mem_diff {x y z : ZFSet.{u}} : z ∈ x \ y ↔ z ∈ x ∧ z ∉ y :=
  @mem_sep (fun z : ZFSet.{u} => z ∉ y) x z
#align Set.mem_diff ZFSet.mem_diff

@[simp]
theorem sUnion_pair {x y : ZFSet.{u}} : ⋃₀ ({x, y} : ZFSet.{u}) = x ∪ y :=
  rfl
#align Set.sUnion_pair ZFSet.sUnion_pair

theorem mem_wf : @WellFounded ZFSet (· ∈ ·) :=
  (wellFounded_lift₂_iff (H := fun a b c d hx hy =>
    propext ((@Mem.congr_left a c hx).trans (@Mem.congr_right b d hy _)))).mpr PSet.mem_wf
#align Set.mem_wf ZFSet.mem_wf

/-- Induction on the `∈` relation. -/
@[elab_as_elim]
theorem inductionOn {p : ZFSet → Prop} (x) (h : ∀ x, (∀ y ∈ x, p y) → p x) : p x :=
  mem_wf.induction x h
#align Set.induction_on ZFSet.inductionOn

instance : WellFoundedRelation ZFSet :=
  ⟨_, mem_wf⟩

instance : IsAsymm ZFSet (· ∈ ·) :=
  mem_wf.isAsymm

-- Porting note: this can't be inferred automatically for some reason.
instance : IsIrrefl ZFSet (· ∈ ·) :=
  mem_wf.isIrrefl

theorem mem_asymm {x y : ZFSet} : x ∈ y → y ∉ x :=
  asymm
#align Set.mem_asymm ZFSet.mem_asymm

theorem mem_irrefl (x : ZFSet) : x ∉ x :=
  irrefl x
#align Set.mem_irrefl ZFSet.mem_irrefl

theorem regularity (x : ZFSet.{u}) (h : x ≠ ∅) : ∃ y ∈ x, x ∩ y = ∅ :=
  by_contradiction fun ne =>
    h <| (eq_empty x).2 fun y =>
      @inductionOn (fun z => z ∉ x) y fun z IH zx =>
        ne ⟨z, zx, (eq_empty _).2 fun w wxz =>
          let ⟨wx, wz⟩ := mem_inter.1 wxz
          IH w wz wx⟩
#align Set.regularity ZFSet.regularity

/-- The image of a (definable) ZFC set function -/
def image (f : ZFSet → ZFSet) [Definable 1 f] : ZFSet → ZFSet :=
  let ⟨r, hr⟩ := @Definable.Resp 1 f _
  Resp.eval 1
    ⟨PSet.image r, fun _ _ e =>
      Mem.ext fun _ =>
        (mem_image hr).trans <|
          Iff.trans
              ⟨fun ⟨w, h1, h2⟩ => ⟨w, (Mem.congr_right e).1 h1, h2⟩, fun ⟨w, h1, h2⟩ =>
                ⟨w, (Mem.congr_right e).2 h1, h2⟩⟩ <|
            (mem_image hr).symm⟩
#align Set.image ZFSet.image

theorem image.mk :
    ∀ (f : ZFSet.{u} → ZFSet.{u}) [H : Definable 1 f] (x) {y} (_ : y ∈ x), f y ∈ @image f H x
  | _, ⟨F⟩, x, y => Quotient.inductionOn₂ x y fun ⟨_, _⟩ _ ⟨a, ya⟩ => ⟨a, F.2 _ _ ya⟩
#align Set.image.mk ZFSet.image.mk

@[simp]
theorem mem_image :
    ∀ {f : ZFSet.{u} → ZFSet.{u}} [H : Definable 1 f] {x y : ZFSet.{u}},
      y ∈ @image f H x ↔ ∃ z ∈ x, f z = y
  | _, ⟨_⟩, x, y =>
    Quotient.inductionOn₂ x y fun ⟨_, A⟩ _ =>
      ⟨fun ⟨a, ya⟩ => ⟨⟦A a⟧, Mem.mk A a, Eq.symm <| Quotient.sound ya⟩, fun ⟨_, hz, e⟩ =>
        e ▸ image.mk _ _ hz⟩
#align Set.mem_image ZFSet.mem_image

@[simp]
theorem toSet_image (f : ZFSet → ZFSet) [H : Definable 1 f] (x : ZFSet) :
    (image f x).toSet = f '' x.toSet := by
  ext
  -- ⊢ x✝ ∈ toSet (image f x) ↔ x✝ ∈ f '' toSet x
  simp
  -- 🎉 no goals
#align Set.to_set_image ZFSet.toSet_image

/-- The range of an indexed family of sets. The universes allow for a more general index type
  without manual use of `ULift`. -/
noncomputable def range {α : Type u} (f : α → ZFSet.{max u v}) : ZFSet.{max u v} :=
  ⟦⟨ULift.{v} α, Quotient.out ∘ f ∘ ULift.down⟩⟧
#align Set.range ZFSet.range

@[simp]
theorem mem_range {α : Type u} {f : α → ZFSet.{max u v}} {x : ZFSet.{max u v}} :
    x ∈ range.{u, v} f ↔ x ∈ Set.range f :=
  Quotient.inductionOn x fun y => by
    constructor
    -- ⊢ Quotient.mk setoid y ∈ range f → Quotient.mk setoid y ∈ Set.range f
    · rintro ⟨z, hz⟩
      -- ⊢ Quotient.mk setoid y ∈ Set.range f
      exact ⟨z.down, Quotient.eq_mk_iff_out.2 hz.symm⟩
      -- 🎉 no goals
    · rintro ⟨z, hz⟩
      -- ⊢ Quotient.mk setoid y ∈ range f
      use ULift.up z
      -- ⊢ PSet.Equiv y (Func (PSet.mk (ULift α) (Quotient.out ∘ f ∘ ULift.down)) { dow …
      simpa [hz] using PSet.Equiv.symm (Quotient.mk_out y)
      -- 🎉 no goals
#align Set.mem_range ZFSet.mem_range

@[simp]
theorem toSet_range {α : Type u} (f : α → ZFSet.{max u v}) :
    (range.{u, v} f).toSet = Set.range f := by
  ext
  -- ⊢ x✝ ∈ toSet (range f) ↔ x✝ ∈ Set.range f
  simp
  -- 🎉 no goals
#align Set.to_set_range ZFSet.toSet_range

/-- Kuratowski ordered pair -/
def pair (x y : ZFSet.{u}) : ZFSet.{u} :=
  {{x}, {x, y}}
#align Set.pair ZFSet.pair

@[simp]
theorem toSet_pair (x y : ZFSet.{u}) : (pair x y).toSet = {{x}, {x, y}} := by simp [pair]
                                                                              -- 🎉 no goals
#align Set.to_set_pair ZFSet.toSet_pair

/-- A subset of pairs `{(a, b) ∈ x × y | p a b}` -/
def pairSep (p : ZFSet.{u} → ZFSet.{u} → Prop) (x y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ a ∈ x, ∃ b ∈ y, z = pair a b ∧ p a b) (powerset (powerset (x ∪ y)))
#align Set.pair_sep ZFSet.pairSep

@[simp]
theorem mem_pairSep {p} {x y z : ZFSet.{u}} :
    z ∈ pairSep p x y ↔ ∃ a ∈ x, ∃ b ∈ y, z = pair a b ∧ p a b := by
  refine' mem_sep.trans ⟨And.right, fun e => ⟨_, e⟩⟩
  -- ⊢ z ∈ powerset (powerset (x ∪ y))
  rcases e with ⟨a, ax, b, bY, rfl, pab⟩
  -- ⊢ pair a b ∈ powerset (powerset (x ∪ y))
  simp only [mem_powerset, subset_def, mem_union, pair, mem_pair]
  -- ⊢ ∀ ⦃z : ZFSet⦄, z = {a} ∨ z = {a, b} → ∀ ⦃z_1 : ZFSet⦄, z_1 ∈ z → z_1 ∈ x ∨ z …
  rintro u (rfl | rfl) v <;> simp only [mem_singleton, mem_pair]
  -- ⊢ v ∈ {a} → v ∈ x ∨ v ∈ y
                             -- ⊢ v = a → v ∈ x ∨ v ∈ y
                             -- ⊢ v = a ∨ v = b → v ∈ x ∨ v ∈ y
  · rintro rfl
    -- ⊢ v ∈ x ∨ v ∈ y
    exact Or.inl ax
    -- 🎉 no goals
  · rintro (rfl | rfl) <;> [left; right] <;> assumption
    -- ⊢ v ∈ x
                                             -- 🎉 no goals
                                             -- 🎉 no goals
#align Set.mem_pair_sep ZFSet.mem_pairSep

theorem pair_injective : Function.Injective2 pair := fun x x' y y' H => by
  have ae := ext_iff.1 H
  -- ⊢ x = x' ∧ y = y'
  simp only [pair, mem_pair] at ae
  -- ⊢ x = x' ∧ y = y'
  obtain rfl : x = x' := by
    cases' (ae {x}).1 (by simp) with h h
    · exact singleton_injective h
    · have m : x' ∈ ({x} : ZFSet) := by simp [h]
      rw [mem_singleton.mp m]
  have he : x = y → y = y' := by
    rintro rfl
    cases' (ae {x, y'}).2 (by simp only [eq_self_iff_true, or_true_iff]) with xy'x xy'xx
    · rw [eq_comm, ← mem_singleton, ← xy'x, mem_pair]
      exact Or.inr rfl
    · simpa [eq_comm] using (ext_iff.1 xy'xx y').1 (by simp)
  obtain xyx | xyy' := (ae {x, y}).1 (by simp)
  -- ⊢ x = x ∧ y = y'
  · obtain rfl := mem_singleton.mp ((ext_iff.1 xyx y).1 <| by simp)
    -- ⊢ y = y ∧ y = y'
    simp [he rfl]
    -- 🎉 no goals
  · obtain rfl | yy' := mem_pair.mp ((ext_iff.1 xyy' y).1 <| by simp)
    -- ⊢ y = y ∧ y = y'
    · simp [he rfl]
      -- 🎉 no goals
    · simp [yy']
      -- 🎉 no goals
#align Set.pair_injective ZFSet.pair_injective

@[simp]
theorem pair_inj {x y x' y' : ZFSet} : pair x y = pair x' y' ↔ x = x' ∧ y = y' :=
  pair_injective.eq_iff
#align Set.pair_inj ZFSet.pair_inj

/-- The cartesian product, `{(a, b) | a ∈ x, b ∈ y}` -/
def prod : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} :=
  pairSep fun _ _ => True
#align Set.prod ZFSet.prod

@[simp]
theorem mem_prod {x y z : ZFSet.{u}} : z ∈ prod x y ↔ ∃ a ∈ x, ∃ b ∈ y, z = pair a b := by
  simp [prod]
  -- 🎉 no goals
#align Set.mem_prod ZFSet.mem_prod

theorem pair_mem_prod {x y a b : ZFSet.{u}} : pair a b ∈ prod x y ↔ a ∈ x ∧ b ∈ y := by
  simp
  -- 🎉 no goals
#align Set.pair_mem_prod ZFSet.pair_mem_prod

/-- `isFunc x y f` is the assertion that `f` is a subset of `x × y` which relates to each element
of `x` a unique element of `y`, so that we can consider `f` as a ZFC function `x → y`. -/
def IsFunc (x y f : ZFSet.{u}) : Prop :=
  f ⊆ prod x y ∧ ∀ z : ZFSet.{u}, z ∈ x → ∃! w, pair z w ∈ f
#align Set.is_func ZFSet.IsFunc

/-- `funs x y` is `y ^ x`, the set of all set functions `x → y` -/
def funs (x y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (IsFunc x y) (powerset (prod x y))
#align Set.funs ZFSet.funs

@[simp]
theorem mem_funs {x y f : ZFSet.{u}} : f ∈ funs x y ↔ IsFunc x y f := by simp [funs, IsFunc]
                                                                         -- 🎉 no goals
#align Set.mem_funs ZFSet.mem_funs

-- TODO(Mario): Prove this computably
/- Porting note: the `Definable` argument in `mapDefinableAux` is unused, though the TODO remark
   suggests it shouldn't be. -/
@[nolint unusedArguments]
noncomputable instance mapDefinableAux (f : ZFSet → ZFSet) [Definable 1 f] :
    Definable 1 fun y => pair y (f y) :=
  @Classical.allDefinable 1 _
#align Set.map_definable_aux ZFSet.mapDefinableAux

/-- Graph of a function: `map f x` is the ZFC function which maps `a ∈ x` to `f a` -/
noncomputable def map (f : ZFSet → ZFSet) [Definable 1 f] : ZFSet → ZFSet :=
  image fun y => pair y (f y)
#align Set.map ZFSet.map

@[simp]
theorem mem_map {f : ZFSet → ZFSet} [Definable 1 f] {x y : ZFSet} :
    y ∈ map f x ↔ ∃ z ∈ x, pair z (f z) = y :=
  mem_image
#align Set.mem_map ZFSet.mem_map

theorem map_unique {f : ZFSet.{u} → ZFSet.{u}} [H : Definable 1 f] {x z : ZFSet.{u}}
    (zx : z ∈ x) : ∃! w, pair z w ∈ map f x :=
  ⟨f z, image.mk _ _ zx, fun y yx => by
    let ⟨w, _, we⟩ := mem_image.1 yx
    -- ⊢ y = f z
    let ⟨wz, fy⟩ := pair_injective we
    -- ⊢ y = f z
    rw [← fy, wz]⟩
    -- 🎉 no goals
#align Set.map_unique ZFSet.map_unique

@[simp]
theorem map_isFunc {f : ZFSet → ZFSet} [Definable 1 f] {x y : ZFSet} :
    IsFunc x y (map f x) ↔ ∀ z ∈ x, f z ∈ y :=
  ⟨fun ⟨ss, h⟩ z zx =>
    let ⟨_, t1, t2⟩ := h z zx
    (t2 (f z) (image.mk _ _ zx)).symm ▸ (pair_mem_prod.1 (ss t1)).right,
    fun h =>
    ⟨fun _ yx =>
      let ⟨z, zx, ze⟩ := mem_image.1 yx
      ze ▸ pair_mem_prod.2 ⟨zx, h z zx⟩,
      fun _ => map_unique⟩⟩
#align Set.map_is_func ZFSet.map_isFunc

/-- Given a predicate `p` on ZFC sets. `Hereditarily p x` means that `x` has property `p` and the
members of `x` are all `Hereditarily p`. -/
def Hereditarily (p : ZFSet → Prop) (x : ZFSet) : Prop :=
  p x ∧ ∀ y ∈ x, Hereditarily p y
termination_by _ => x
#align Set.hereditarily ZFSet.Hereditarily

section Hereditarily

variable {p : ZFSet.{u} → Prop} {x y : ZFSet.{u}}

theorem hereditarily_iff : Hereditarily p x ↔ p x ∧ ∀ y ∈ x, Hereditarily p y := by
  rw [← Hereditarily]
  -- 🎉 no goals
#align Set.hereditarily_iff ZFSet.hereditarily_iff

alias ⟨Hereditarily.def, _⟩ := hereditarily_iff
#align Set.hereditarily.def ZFSet.Hereditarily.def

theorem Hereditarily.self (h : x.Hereditarily p) : p x :=
  h.def.1
#align Set.hereditarily.self ZFSet.Hereditarily.self

theorem Hereditarily.mem (h : x.Hereditarily p) (hy : y ∈ x) : y.Hereditarily p :=
  h.def.2 _ hy
#align Set.hereditarily.mem ZFSet.Hereditarily.mem

theorem Hereditarily.empty : Hereditarily p x → p ∅ := by
  apply @ZFSet.inductionOn _ x
  -- ⊢ ∀ (x : ZFSet), (∀ (y : ZFSet), y ∈ x → Hereditarily p y → p ∅) → Hereditaril …
  intro y IH h
  -- ⊢ p ∅
  rcases ZFSet.eq_empty_or_nonempty y with (rfl | ⟨a, ha⟩)
  -- ⊢ p ∅
  · exact h.self
    -- 🎉 no goals
  · exact IH a ha (h.mem ha)
    -- 🎉 no goals
#align Set.hereditarily.empty ZFSet.Hereditarily.empty

end Hereditarily

end ZFSet

/-- The collection of all classes.
We define `Class` as `Set ZFSet`, as this allows us to get many instances automatically. However, in
practice, we treat it as (the definitionally equal) `ZFSet → Prop`. This means, the preferred way to
state that `x : ZFSet` belongs to `A : Class` is to write `A x`. -/
def Class :=
  Set ZFSet deriving HasSubset, EmptyCollection, Nonempty, Union, Inter, HasCompl, SDiff
#align Class Class

instance : Insert ZFSet Class :=
  ⟨Set.insert⟩

namespace Class

-- Porting note: this is no longer an automatically derived instance.
/-- `{x ∈ A | p x}` is the class of elements in `A` satisfying `p` -/
protected def sep (p : ZFSet → Prop) (A : Class) : Class :=
  {y | A y ∧ p y}

@[ext]
theorem ext {x y : Class.{u}} : (∀ z : ZFSet.{u}, x z ↔ y z) → x = y :=
  Set.ext
#align Class.ext Class.ext

theorem ext_iff {x y : Class.{u}} : x = y ↔ ∀ z, x z ↔ y z :=
  Set.ext_iff
#align Class.ext_iff Class.ext_iff

/-- Coerce a ZFC set into a class -/
@[coe]
def ofSet (x : ZFSet.{u}) : Class.{u} :=
  { y | y ∈ x }
#align Class.of_Set Class.ofSet

instance : Coe ZFSet Class :=
  ⟨ofSet⟩

/-- The universal class -/
def univ : Class :=
  Set.univ
#align Class.univ Class.univ

/-- Assert that `A` is a ZFC set satisfying `B` -/
def ToSet (B : Class.{u}) (A : Class.{u}) : Prop :=
  ∃ x : ZFSet, ↑x = A ∧ B x
#align Class.to_Set Class.ToSet

/-- `A ∈ B` if `A` is a ZFC set which satisfies `B` -/
protected def Mem (A B : Class.{u}) : Prop :=
  ToSet.{u} B A
#align Class.mem Class.Mem

instance : Membership Class Class :=
  ⟨Class.Mem⟩

theorem mem_def (A B : Class.{u}) : A ∈ B ↔ ∃ x : ZFSet, ↑x = A ∧ B x :=
  Iff.rfl
#align Class.mem_def Class.mem_def

@[simp]
theorem not_mem_empty (x : Class.{u}) : x ∉ (∅ : Class.{u}) := fun ⟨_, _, h⟩ => h
#align Class.not_mem_empty Class.not_mem_empty

@[simp]
theorem not_empty_hom (x : ZFSet.{u}) : ¬(∅ : Class.{u}) x :=
  id
#align Class.not_empty_hom Class.not_empty_hom

@[simp]
theorem mem_univ {A : Class.{u}} : A ∈ univ.{u} ↔ ∃ x : ZFSet.{u}, ↑x = A :=
  exists_congr fun _ => and_true_iff _
#align Class.mem_univ Class.mem_univ

@[simp]
theorem mem_univ_hom (x : ZFSet.{u}) : univ.{u} x :=
  trivial
#align Class.mem_univ_hom Class.mem_univ_hom

theorem eq_univ_iff_forall {A : Class.{u}} : A = univ ↔ ∀ x : ZFSet, A x :=
  Set.eq_univ_iff_forall
#align Class.eq_univ_iff_forall Class.eq_univ_iff_forall

theorem eq_univ_of_forall {A : Class.{u}} : (∀ x : ZFSet, A x) → A = univ :=
  Set.eq_univ_of_forall
#align Class.eq_univ_of_forall Class.eq_univ_of_forall

theorem mem_wf : @WellFounded Class.{u} (· ∈ ·) :=
  ⟨by
    have H : ∀ x : ZFSet.{u}, @Acc Class.{u} (· ∈ ·) ↑x := by
      refine' fun a => ZFSet.inductionOn a fun x IH => ⟨_, _⟩
      rintro A ⟨z, rfl, hz⟩
      exact IH z hz
    · refine' fun A => ⟨A, _⟩
      -- ⊢ ∀ (y : Class), y ∈ A → Acc (fun x x_1 => x ∈ x_1) y
      rintro B ⟨x, rfl, _⟩
      -- ⊢ Acc (fun x x_1 => x ∈ x_1) ↑x
      exact H x⟩
      -- 🎉 no goals
#align Class.mem_wf Class.mem_wf

instance : WellFoundedRelation Class :=
  ⟨_, mem_wf⟩

instance : IsAsymm Class (· ∈ ·) :=
  mem_wf.isAsymm

-- Porting note: this can't be inferred automatically for some reason.
instance : IsIrrefl Class (· ∈ ·) :=
  mem_wf.isIrrefl

theorem mem_asymm {x y : Class} : x ∈ y → y ∉ x :=
  asymm
#align Class.mem_asymm Class.mem_asymm

theorem mem_irrefl (x : Class) : x ∉ x :=
  irrefl x
#align Class.mem_irrefl Class.mem_irrefl

/-- **There is no universal set.**
This is stated as `univ ∉ univ`, meaning that `univ` (the class of all sets) is proper (does not
belong to the class of all sets). -/
theorem univ_not_mem_univ : univ ∉ univ :=
  mem_irrefl _
#align Class.univ_not_mem_univ Class.univ_not_mem_univ

/-- Convert a conglomerate (a collection of classes) into a class -/
def congToClass (x : Set Class.{u}) : Class.{u} :=
  { y | ↑y ∈ x }
#align Class.Cong_to_Class Class.congToClass

@[simp]
theorem congToClass_empty : congToClass ∅ = ∅ := by
  ext z
  -- ⊢ congToClass ∅ z ↔ ∅ z
  simp only [congToClass, not_empty_hom, iff_false_iff]
  -- ⊢ ¬setOf (fun y => ↑y ∈ ∅) z
  exact Set.not_mem_empty z
  -- 🎉 no goals
#align Class.Cong_to_Class_empty Class.congToClass_empty

/-- Convert a class into a conglomerate (a collection of classes) -/
def classToCong (x : Class.{u}) : Set Class.{u} :=
  { y | y ∈ x }
#align Class.Class_to_Cong Class.classToCong

@[simp]
theorem classToCong_empty : classToCong ∅ = ∅ := by
  ext
  -- ⊢ x✝ ∈ classToCong ∅ ↔ x✝ ∈ ∅
  simp [classToCong]
  -- 🎉 no goals
#align Class.Class_to_Cong_empty Class.classToCong_empty

/-- The power class of a class is the class of all subclasses that are ZFC sets -/
def powerset (x : Class) : Class :=
  congToClass (Set.powerset x)
#align Class.powerset Class.powerset

/-- The union of a class is the class of all members of ZFC sets in the class -/
def sUnion (x : Class) : Class :=
  ⋃₀ classToCong x
#align Class.sUnion Class.sUnion

@[inherit_doc]
prefix:110 "⋃₀ " => Class.sUnion

/-- The intersection of a class is the class of all members of ZFC sets in the class -/
def sInter (x : Class) : Class :=
  ⋂₀ classToCong x

@[inherit_doc]
prefix:110 "⋂₀ " => Class.sInter

theorem ofSet.inj {x y : ZFSet.{u}} (h : (x : Class.{u}) = y) : x = y :=
  ZFSet.ext fun z => by
    change (x : Class.{u}) z ↔ (y : Class.{u}) z
    -- ⊢ ↑x z ↔ ↑y z
    rw [h]
    -- 🎉 no goals
#align Class.of_Set.inj Class.ofSet.inj

@[simp]
theorem toSet_of_ZFSet (A : Class.{u}) (x : ZFSet.{u}) : ToSet A x ↔ A x :=
  ⟨fun ⟨y, yx, py⟩ => by rwa [ofSet.inj yx] at py, fun px => ⟨x, rfl, px⟩⟩
                         -- 🎉 no goals
#align Class.to_Set_of_Set Class.toSet_of_ZFSet

@[simp, norm_cast]
theorem coe_mem {x : ZFSet.{u}} {A : Class.{u}} : ↑x ∈ A ↔ A x :=
  toSet_of_ZFSet _ _
#align Class.coe_mem Class.coe_mem

@[simp]
theorem coe_apply {x y : ZFSet.{u}} : (y : Class.{u}) x ↔ x ∈ y :=
  Iff.rfl
#align Class.coe_apply Class.coe_apply

@[simp, norm_cast]
theorem coe_subset (x y : ZFSet.{u}) : (x : Class.{u}) ⊆ y ↔ x ⊆ y :=
  Iff.rfl
#align Class.coe_subset Class.coe_subset

@[simp, norm_cast]
theorem coe_sep (p : Class.{u}) (x : ZFSet.{u}) :
    (ZFSet.sep p x : Class) = { y ∈ x | p y } :=
  ext fun _ => ZFSet.mem_sep
#align Class.coe_sep Class.coe_sep

@[simp, norm_cast]
theorem coe_empty : ↑(∅ : ZFSet.{u}) = (∅ : Class.{u}) :=
  ext fun y => iff_false_iff.2 <| ZFSet.not_mem_empty y
#align Class.coe_empty Class.coe_empty

@[simp, norm_cast]
theorem coe_insert (x y : ZFSet.{u}) : ↑(insert x y) = @insert ZFSet.{u} Class.{u} _ x y :=
  ext fun _ => ZFSet.mem_insert_iff
#align Class.coe_insert Class.coe_insert

@[simp, norm_cast]
theorem coe_union (x y : ZFSet.{u}) : ↑(x ∪ y) = (x : Class.{u}) ∪ y :=
  ext fun _ => ZFSet.mem_union
#align Class.coe_union Class.coe_union

@[simp, norm_cast]
theorem coe_inter (x y : ZFSet.{u}) : ↑(x ∩ y) = (x : Class.{u}) ∩ y :=
  ext fun _ => ZFSet.mem_inter
#align Class.coe_inter Class.coe_inter

@[simp, norm_cast]
theorem coe_diff (x y : ZFSet.{u}) : ↑(x \ y) = (x : Class.{u}) \ y :=
  ext fun _ => ZFSet.mem_diff
#align Class.coe_diff Class.coe_diff

@[simp, norm_cast]
theorem coe_powerset (x : ZFSet.{u}) : ↑x.powerset = powerset.{u} x :=
  ext fun _ => ZFSet.mem_powerset
#align Class.coe_powerset Class.coe_powerset

@[simp]
theorem powerset_apply {A : Class.{u}} {x : ZFSet.{u}} : powerset A x ↔ ↑x ⊆ A :=
  Iff.rfl
#align Class.powerset_apply Class.powerset_apply

@[simp]
theorem sUnion_apply {x : Class} {y : ZFSet} : (⋃₀ x) y ↔ ∃ z : ZFSet, x z ∧ y ∈ z := by
  constructor
  -- ⊢ (⋃₀ x) y → ∃ z, x z ∧ y ∈ z
  · rintro ⟨-, ⟨z, rfl, hxz⟩, hyz⟩
    -- ⊢ ∃ z, x z ∧ y ∈ z
    exact ⟨z, hxz, hyz⟩
    -- 🎉 no goals
  · exact fun ⟨z, hxz, hyz⟩ => ⟨_, coe_mem.2 hxz, hyz⟩
    -- 🎉 no goals
#align Class.sUnion_apply Class.sUnion_apply

@[simp, norm_cast]
theorem coe_sUnion (x : ZFSet.{u}) : ↑(⋃₀ x : ZFSet) = ⋃₀ (x : Class.{u}) :=
  ext fun y =>
    ZFSet.mem_sUnion.trans (sUnion_apply.trans <| by rfl).symm
                                                     -- 🎉 no goals
#align Class.coe_sUnion Class.coe_sUnion

@[simp]
theorem mem_sUnion {x y : Class.{u}} : y ∈ ⋃₀ x ↔ ∃ z, z ∈ x ∧ y ∈ z := by
  constructor
  -- ⊢ y ∈ ⋃₀ x → ∃ z, z ∈ x ∧ y ∈ z
  · rintro ⟨w, rfl, z, hzx, hwz⟩
    -- ⊢ ∃ z, z ∈ x ∧ ↑w ∈ z
    exact ⟨z, hzx, coe_mem.2 hwz⟩
    -- 🎉 no goals
  · rintro ⟨w, hwx, z, rfl, hwz⟩
    -- ⊢ ↑z ∈ ⋃₀ x
    exact ⟨z, rfl, w, hwx, hwz⟩
    -- 🎉 no goals
#align Class.mem_sUnion Class.mem_sUnion

theorem sInter_apply {x : Class.{u}} {y : ZFSet.{u}} : (⋂₀ x) y ↔ ∀ z : ZFSet.{u}, x z → y ∈ z := by
  refine' ⟨fun hxy z hxz => hxy _ ⟨z, rfl, hxz⟩, _⟩
  -- ⊢ (∀ (z : ZFSet), x z → y ∈ z) → (⋂₀ x) y
  rintro H - ⟨z, rfl, hxz⟩
  -- ⊢ y ∈ ↑z
  exact H _ hxz
  -- 🎉 no goals
#align Class.sInter_apply Class.sInter_apply

@[simp, norm_cast]
theorem coe_sInter {x : ZFSet.{u}} (h : x.Nonempty) : ↑(⋂₀ x : ZFSet) = ⋂₀ (x : Class.{u}) :=
  Set.ext fun _ => (ZFSet.mem_sInter h).trans sInter_apply.symm
#align Class.sInter_coe Class.coe_sInter

theorem mem_of_mem_sInter {x y z : Class} (hy : y ∈ ⋂₀ x) (hz : z ∈ x) : y ∈ z := by
  obtain ⟨w, rfl, hw⟩ := hy
  -- ⊢ ↑w ∈ z
  exact coe_mem.2 (hw z hz)
  -- 🎉 no goals
#align Class.mem_of_mem_sInter Class.mem_of_mem_sInter

theorem mem_sInter {x y : Class.{u}} (h : x.Nonempty) : y ∈ ⋂₀ x ↔ ∀ z, z ∈ x → y ∈ z := by
  refine' ⟨fun hy z => mem_of_mem_sInter hy, fun H => _⟩
  -- ⊢ y ∈ ⋂₀ x
  simp_rw [mem_def, sInter_apply]
  -- ⊢ ∃ x_1, ↑x_1 = y ∧ ∀ (z : ZFSet), x z → x_1 ∈ z
  obtain ⟨z, hz⟩ := h
  -- ⊢ ∃ x_1, ↑x_1 = y ∧ ∀ (z : ZFSet), x z → x_1 ∈ z
  obtain ⟨y, rfl, _⟩ := H z (coe_mem.2 hz)
  -- ⊢ ∃ x_1, ↑x_1 = ↑y ∧ ∀ (z : ZFSet), x z → x_1 ∈ z
  refine' ⟨y, rfl, fun w hxw => _⟩
  -- ⊢ y ∈ w
  simpa only [coe_mem, coe_apply] using H w (coe_mem.2 hxw)
  -- 🎉 no goals
#align Class.mem_sInter Class.mem_sInter

@[simp]
theorem sUnion_empty : ⋃₀ (∅ : Class.{u}) = (∅ : Class.{u}) := by
  ext
  -- ⊢ (⋃₀ ∅) z✝ ↔ ∅ z✝
  simp
  -- 🎉 no goals
#align Class.sUnion_empty Class.sUnion_empty

@[simp]
theorem sInter_empty : ⋂₀ (∅ : Class.{u}) = univ := by
  rw [sInter, classToCong_empty, Set.sInter_empty, univ]
  -- 🎉 no goals
#align Class.sInter_empty Class.sInter_empty

/-- An induction principle for sets. If every subset of a class is a member, then the class is
  universal. -/
theorem eq_univ_of_powerset_subset {A : Class} (hA : powerset A ⊆ A) : A = univ :=
  eq_univ_of_forall
    (by
      by_contra' hnA
      -- ⊢ False
      exact
        WellFounded.min_mem ZFSet.mem_wf _ hnA
          (hA fun x hx =>
            Classical.not_not.1 fun hB =>
              WellFounded.not_lt_min ZFSet.mem_wf _ hnA hB <| coe_apply.1 hx))
#align Class.eq_univ_of_powerset_subset Class.eq_univ_of_powerset_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The definite description operator, which is `{x}` if `{y | A y} = {x}` and `∅` otherwise. -/
def iota (A : Class) : Class :=
  ⋃₀ { x | ∀ y, A y ↔ y = x }
#align Class.iota Class.iota

theorem iota_val (A : Class) (x : ZFSet) (H : ∀ y, A y ↔ y = x) : iota A = ↑x :=
  ext fun y =>
    ⟨fun ⟨_, ⟨x', rfl, h⟩, yx'⟩ => by rwa [← (H x').1 <| (h x').2 rfl], fun yx =>
                                      -- 🎉 no goals
      ⟨_, ⟨x, rfl, H⟩, yx⟩⟩
#align Class.iota_val Class.iota_val

/-- Unlike the other set constructors, the `iota` definite descriptor
  is a set for any set input, but not constructively so, so there is no
  associated `Class → Set` function. -/
theorem iota_ex (A) : iota.{u} A ∈ univ.{u} :=
  mem_univ.2 <|
    Or.elim (Classical.em <| ∃ x, ∀ y, A y ↔ y = x) (fun ⟨x, h⟩ => ⟨x, Eq.symm <| iota_val A x h⟩)
      fun hn =>
      ⟨∅, ext fun _ => coe_empty.symm ▸ ⟨False.rec, fun ⟨_, ⟨x, rfl, H⟩, _⟩ => hn ⟨x, H⟩⟩⟩
#align Class.iota_ex Class.iota_ex

/-- Function value -/
def fval (F A : Class.{u}) : Class.{u} :=
  iota fun y => ToSet (fun x => F (ZFSet.pair x y)) A
#align Class.fval Class.fval

@[inherit_doc]
infixl:100 " ′ " => fval

theorem fval_ex (F A : Class.{u}) : F ′ A ∈ univ.{u} :=
  iota_ex _
#align Class.fval_ex Class.fval_ex

end Class

namespace ZFSet

@[simp]
theorem map_fval {f : ZFSet.{u} → ZFSet.{u}} [H : PSet.Definable 1 f] {x y : ZFSet.{u}}
    (h : y ∈ x) : (ZFSet.map f x ′ y : Class.{u}) = f y :=
  Class.iota_val _ _ fun z => by
    rw [Class.toSet_of_ZFSet, Class.coe_apply, mem_map]
    -- ⊢ (∃ z_1, z_1 ∈ x ∧ pair z_1 (f z_1) = pair y z) ↔ z = f y
    exact
      ⟨fun ⟨w, _, pr⟩ => by
        let ⟨wy, fw⟩ := ZFSet.pair_injective pr
        rw [← fw, wy], fun e => by
        subst e
        exact ⟨_, h, rfl⟩⟩
#align Set.map_fval ZFSet.map_fval

variable (x : ZFSet.{u}) (h : ∅ ∉ x)

/-- A choice function on the class of nonempty ZFC sets. -/
noncomputable def choice : ZFSet :=
  @map (fun y => Classical.epsilon fun z => z ∈ y) (Classical.allDefinable _) x
#align Set.choice ZFSet.choice

theorem choice_mem_aux (y : ZFSet.{u}) (yx : y ∈ x) :
    (Classical.epsilon fun z : ZFSet.{u} => z ∈ y) ∈ y :=
  (@Classical.epsilon_spec _ fun z : ZFSet.{u} => z ∈ y) <|
    by_contradiction fun n => h <| by rwa [← (eq_empty y).2 fun z zx => n ⟨z, zx⟩]
                                      -- 🎉 no goals
#align Set.choice_mem_aux ZFSet.choice_mem_aux

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem choice_isFunc : IsFunc x (⋃₀ x) (choice x) :=
  (@map_isFunc _ (Classical.allDefinable _) _ _).2 fun y yx =>
    mem_sUnion.2 ⟨y, yx, choice_mem_aux x h y yx⟩
#align Set.choice_is_func ZFSet.choice_isFunc

theorem choice_mem (y : ZFSet.{u}) (yx : y ∈ x) : (choice x ′ y : Class.{u}) ∈ (y : Class.{u}) := by
  delta choice
  -- ⊢ ↑(map (fun y => Classical.epsilon fun z => z ∈ y) x) ′ ↑y ∈ ↑y
  rw [@map_fval _ (Classical.allDefinable _) x y yx, Class.coe_mem, Class.coe_apply]
  -- ⊢ (Classical.epsilon fun z => z ∈ y) ∈ y
  exact choice_mem_aux x h y yx
  -- 🎉 no goals
#align Set.choice_mem ZFSet.choice_mem

end ZFSet
