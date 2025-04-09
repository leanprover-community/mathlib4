/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Small.Basic
import Mathlib.Logic.Function.OfArity
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

* `PSet`: Pre-set. A pre-set is inductively defined by its indexing type and its members, which are
  themselves pre-sets.
* `ZFSet`: ZFC set. Defined as `PSet` quotiented by `PSet.Equiv`, the extensional equivalence.
* `Class`: Class. Defined as `Set ZFSet`.
* `ZFSet.choice`: Axiom of choice. Proved from Lean's axiom of choice.

## Other definitions

* `PSet.Type`: Underlying type of a pre-set.
* `PSet.Func`: Underlying family of pre-sets of a pre-set.
* `PSet.Equiv`: Extensional equivalence of pre-sets. Defined inductively.
* `PSet.omega`, `ZFSet.omega`: The von Neumann ordinal `ω` as a `PSet`, as a `Set`.
* `Classical.allZFSetDefinable`: All functions are classically definable.
* `ZFSet.IsFunc` : Predicate that a ZFC set is a subset of `x × y` that can be considered as a ZFC
  function `x → y`. That is, each member of `x` is related by the ZFC set to exactly one member of
  `y`.
* `ZFSet.funs`: ZFC set of ZFC functions `x → y`.
* `ZFSet.Hereditarily p x`: Predicate that every set in the transitive closure of `x` has property
  `p`.
* `Class.iota`: Definite description operator.

## Notes

To avoid confusion between the Lean `Set` and the ZFC `Set`, docstrings in this file refer to them
respectively as "`Set`" and "ZFC set".
-/


universe u v

open Function (OfArity)

/-- The type of pre-sets in universe `u`. A pre-set
  is a family of pre-sets indexed by a type in `Type u`.
  The ZFC universe is defined as a quotient of this
  to ensure extensionality. -/
@[pp_with_univ]
inductive PSet : Type (u + 1)
  | mk (α : Type u) (A : α → PSet) : PSet

namespace PSet

/-- The underlying type of a pre-set -/
def «Type» : PSet → Type u
  | ⟨α, _⟩ => α

/-- The underlying pre-set family of a pre-set -/
def Func : ∀ x : PSet, x.Type → PSet
  | ⟨_, A⟩ => A

@[simp]
theorem mk_type (α A) : «Type» ⟨α, A⟩ = α :=
  rfl

@[simp]
theorem mk_func (α A) : Func ⟨α, A⟩ = A :=
  rfl

@[simp]
theorem eta : ∀ x : PSet, mk x.Type x.Func = x
  | ⟨_, _⟩ => rfl

/-- Two pre-sets are extensionally equivalent if every element of the first family is extensionally
equivalent to some element of the second family and vice-versa. -/
def Equiv : PSet → PSet → Prop
  | ⟨_, A⟩, ⟨_, B⟩ => (∀ a, ∃ b, Equiv (A a) (B b)) ∧ (∀ b, ∃ a, Equiv (A a) (B b))

theorem equiv_iff :
    ∀ {x y : PSet},
      Equiv x y ↔ (∀ i, ∃ j, Equiv (x.Func i) (y.Func j)) ∧ ∀ j, ∃ i, Equiv (x.Func i) (y.Func j)
  | ⟨_, _⟩, ⟨_, _⟩ => Iff.rfl

theorem Equiv.exists_left {x y : PSet} (h : Equiv x y) : ∀ i, ∃ j, Equiv (x.Func i) (y.Func j) :=
  (equiv_iff.1 h).1

theorem Equiv.exists_right {x y : PSet} (h : Equiv x y) : ∀ j, ∃ i, Equiv (x.Func i) (y.Func j) :=
  (equiv_iff.1 h).2

@[refl]
protected theorem Equiv.refl : ∀ x, Equiv x x
  | ⟨_, _⟩ => ⟨fun a => ⟨a, Equiv.refl _⟩, fun a => ⟨a, Equiv.refl _⟩⟩

protected theorem Equiv.rfl {x} : Equiv x x :=
  Equiv.refl x

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

@[symm]
protected theorem Equiv.symm {x y} : Equiv x y → Equiv y x :=
  (Equiv.refl y).euc

protected theorem Equiv.comm {x y} : Equiv x y ↔ Equiv y x :=
  ⟨Equiv.symm, Equiv.symm⟩

@[trans]
protected theorem Equiv.trans {x y z} (h1 : Equiv x y) (h2 : Equiv y z) : Equiv x z :=
  h1.euc h2.symm

protected theorem equiv_of_isEmpty (x y : PSet) [IsEmpty x.Type] [IsEmpty y.Type] : Equiv x y :=
  equiv_iff.2 <| by simp

instance setoid : Setoid PSet :=
  ⟨PSet.Equiv, Equiv.refl, Equiv.symm, Equiv.trans⟩

/-- A pre-set is a subset of another pre-set if every element of the first family is extensionally
equivalent to some element of the second family. -/
protected def Subset (x y : PSet) : Prop :=
  ∀ a, ∃ b, Equiv (x.Func a) (y.Func b)

instance : HasSubset PSet :=
  ⟨PSet.Subset⟩

instance : IsRefl PSet (· ⊆ ·) :=
  ⟨fun _ a => ⟨a, Equiv.refl _⟩⟩

instance : IsTrans PSet (· ⊆ ·) :=
  ⟨fun x y z hxy hyz a => by
    obtain ⟨b, hb⟩ := hxy a
    obtain ⟨c, hc⟩ := hyz b
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

/-- `x ∈ y` as pre-sets if `x` is extensionally equivalent to a member of the family `y`. -/
protected def Mem (y x : PSet.{u}) : Prop :=
  ∃ b, Equiv x (y.Func b)

instance : Membership PSet PSet :=
  ⟨PSet.Mem⟩

theorem Mem.mk {α : Type u} (A : α → PSet) (a : α) : A a ∈ mk α A :=
  ⟨a, Equiv.refl (A a)⟩

theorem func_mem (x : PSet) (i : x.Type) : x.Func i ∈ x := by
  cases x
  apply Mem.mk

theorem Mem.ext : ∀ {x y : PSet.{u}}, (∀ w : PSet.{u}, w ∈ x ↔ w ∈ y) → Equiv x y
  | ⟨_, A⟩, ⟨_, B⟩, h =>
    ⟨fun a => (h (A a)).1 (Mem.mk A a), fun b =>
      let ⟨a, ha⟩ := (h (B b)).2 (Mem.mk B b)
      ⟨a, ha.symm⟩⟩

theorem Mem.congr_right : ∀ {x y : PSet.{u}}, Equiv x y → ∀ {w : PSet.{u}}, w ∈ x ↔ w ∈ y
  | ⟨_, _⟩, ⟨_, _⟩, ⟨αβ, βα⟩, _ =>
    ⟨fun ⟨a, ha⟩ =>
      let ⟨b, hb⟩ := αβ a
      ⟨b, ha.trans hb⟩,
      fun ⟨b, hb⟩ =>
      let ⟨a, ha⟩ := βα b
      ⟨a, hb.euc ha⟩⟩

theorem equiv_iff_mem {x y : PSet.{u}} : Equiv x y ↔ ∀ {w : PSet.{u}}, w ∈ x ↔ w ∈ y :=
  ⟨Mem.congr_right,
    match x, y with
    | ⟨_, A⟩, ⟨_, B⟩ => fun h =>
      ⟨fun a => h.1 (Mem.mk A a), fun b =>
        let ⟨a, h⟩ := h.2 (Mem.mk B b)
        ⟨a, h.symm⟩⟩⟩

theorem Mem.congr_left : ∀ {x y : PSet.{u}}, Equiv x y → ∀ {w : PSet.{u}}, x ∈ w ↔ y ∈ w
  | _, _, h, ⟨_, _⟩ => ⟨fun ⟨a, ha⟩ => ⟨a, h.symm.trans ha⟩, fun ⟨a, ha⟩ => ⟨a, h.trans ha⟩⟩

theorem mem_of_subset {x y z : PSet} : x ⊆ y → z ∈ x → z ∈ y
  | h₁, ⟨a, h₂⟩ => (h₁ a).elim fun b h₃ => ⟨b, h₂.trans h₃⟩

theorem subset_iff {x y : PSet} : x ⊆ y ↔ ∀ ⦃z⦄, z ∈ x → z ∈ y :=
  ⟨fun h _ => mem_of_subset h, fun h a => h (Mem.mk _ a)⟩

private theorem mem_wf_aux : ∀ {x y : PSet.{u}}, Equiv x y → Acc (· ∈ ·) y
  | ⟨α, A⟩, ⟨β, B⟩, H =>
    ⟨_, by
      rintro ⟨γ, C⟩ ⟨b, hc⟩
      obtain ⟨a, ha⟩ := H.exists_right b
      have H := ha.trans hc.symm
      rw [mk_func] at H
      exact mem_wf_aux H⟩

theorem mem_wf : @WellFounded PSet (· ∈ ·) :=
  ⟨fun x => mem_wf_aux <| Equiv.refl x⟩

instance : IsWellFounded PSet (· ∈ ·) :=
  ⟨mem_wf⟩

instance : WellFoundedRelation PSet :=
  ⟨_, mem_wf⟩

theorem mem_asymm {x y : PSet} : x ∈ y → y ∉ x :=
  asymm_of (· ∈ ·)

theorem mem_irrefl (x : PSet) : x ∉ x :=
  irrefl_of (· ∈ ·) x

theorem not_subset_of_mem {x y : PSet} (h : x ∈ y) : ¬ y ⊆ x :=
  fun h' ↦ mem_irrefl _ <| mem_of_subset h' h

theorem not_mem_of_subset {x y : PSet} (h : x ⊆ y) : y ∉ x :=
  imp_not_comm.2 not_subset_of_mem h

/-- Convert a pre-set to a `Set` of pre-sets. -/
def toSet (u : PSet.{u}) : Set PSet.{u} :=
  { x | x ∈ u }

@[simp]
theorem mem_toSet (a u : PSet.{u}) : a ∈ u.toSet ↔ a ∈ u :=
  Iff.rfl

/-- A nonempty set is one that contains some element. -/
protected def Nonempty (u : PSet) : Prop :=
  u.toSet.Nonempty

theorem nonempty_def (u : PSet) : u.Nonempty ↔ ∃ x, x ∈ u :=
  Iff.rfl

theorem nonempty_of_mem {x u : PSet} (h : x ∈ u) : u.Nonempty :=
  ⟨x, h⟩

@[simp]
theorem nonempty_toSet_iff {u : PSet} : u.toSet.Nonempty ↔ u.Nonempty :=
  Iff.rfl

theorem nonempty_type_iff_nonempty {x : PSet} : Nonempty x.Type ↔ PSet.Nonempty x :=
  ⟨fun ⟨i⟩ => ⟨_, func_mem _ i⟩, fun ⟨_, j, _⟩ => ⟨j⟩⟩

theorem nonempty_of_nonempty_type (x : PSet) [h : Nonempty x.Type] : PSet.Nonempty x :=
  nonempty_type_iff_nonempty.1 h

/-- Two pre-sets are equivalent iff they have the same members. -/
theorem Equiv.eq {x y : PSet} : Equiv x y ↔ toSet x = toSet y :=
  equiv_iff_mem.trans Set.ext_iff.symm

instance : Coe PSet (Set PSet) :=
  ⟨toSet⟩

/-- The empty pre-set -/
protected def empty : PSet :=
  ⟨_, PEmpty.elim⟩

instance : EmptyCollection PSet :=
  ⟨PSet.empty⟩

instance : Inhabited PSet :=
  ⟨∅⟩

instance : IsEmpty («Type» ∅) :=
  ⟨PEmpty.elim⟩

theorem empty_def : (∅ : PSet) = ⟨_, PEmpty.elim⟩ := by
  simp [EmptyCollection.emptyCollection, PSet.empty]

@[simp]
theorem not_mem_empty (x : PSet.{u}) : x ∉ (∅ : PSet.{u}) :=
  IsEmpty.exists_iff.1

@[simp]
theorem toSet_empty : toSet ∅ = ∅ := by simp [toSet]

@[simp]
theorem empty_subset (x : PSet.{u}) : (∅ : PSet) ⊆ x := fun x => x.elim

@[simp]
theorem not_nonempty_empty : ¬PSet.Nonempty ∅ := by simp [PSet.Nonempty]

protected theorem equiv_empty (x : PSet) [IsEmpty x.Type] : Equiv x ∅ :=
  PSet.equiv_of_isEmpty x _

/-- Insert an element into a pre-set -/
protected def insert (x y : PSet) : PSet :=
  ⟨Option y.Type, fun o => Option.casesOn o x y.Func⟩

instance : Insert PSet PSet :=
  ⟨PSet.insert⟩

instance : Singleton PSet PSet :=
  ⟨fun s => insert s ∅⟩

instance : LawfulSingleton PSet PSet :=
  ⟨fun _ => rfl⟩

instance (x y : PSet) : Inhabited (insert x y).Type :=
  inferInstanceAs (Inhabited <| Option y.Type)

@[simp]
theorem mem_insert_iff : ∀ {x y z : PSet.{u}}, x ∈ insert y z ↔ Equiv x y ∨ x ∈ z
  | x, y, ⟨α, A⟩ =>
    show (x ∈ PSet.mk (Option α) fun o => Option.rec y A o) ↔ Equiv x y ∨ x ∈ PSet.mk α A from
      ⟨fun m =>
        match m with
        | ⟨some a, ha⟩ => Or.inr ⟨a, ha⟩
        | ⟨none, h⟩ => Or.inl h,
        fun m =>
        match m with
        | Or.inr ⟨a, ha⟩ => ⟨some a, ha⟩
        | Or.inl h => ⟨none, h⟩⟩

theorem mem_insert (x y : PSet) : x ∈ insert x y :=
  mem_insert_iff.2 <| Or.inl Equiv.rfl

theorem mem_insert_of_mem {y z : PSet} (x) (h : z ∈ y) : z ∈ insert x y :=
  mem_insert_iff.2 <| Or.inr h

@[simp]
theorem mem_singleton {x y : PSet} : x ∈ ({y} : PSet) ↔ Equiv x y :=
  mem_insert_iff.trans
    ⟨fun o => Or.rec id (fun n => absurd n (not_mem_empty _)) o, Or.inl⟩

theorem mem_pair {x y z : PSet} : x ∈ ({y, z} : PSet) ↔ Equiv x y ∨ Equiv x z := by
  simp

/-- The n-th von Neumann ordinal -/
def ofNat : ℕ → PSet
  | 0 => ∅
  | n + 1 => insert (ofNat n) (ofNat n)

/-- The von Neumann ordinal ω -/
def omega : PSet :=
  ⟨ULift ℕ, fun n => ofNat n.down⟩

/-- The pre-set separation operation `{x ∈ a | p x}` -/
protected def sep (p : PSet → Prop) (x : PSet) : PSet :=
  ⟨{ a // p (x.Func a) }, fun y => x.Func y.1⟩

instance : Sep PSet PSet :=
  ⟨PSet.sep⟩

theorem mem_sep {p : PSet → Prop} (H : ∀ x y, Equiv x y → p x → p y) :
    ∀ {x y : PSet}, y ∈ PSet.sep p x ↔ y ∈ x ∧ p y
  | ⟨_, _⟩, _ =>
    ⟨fun ⟨⟨a, pa⟩, h⟩ => ⟨⟨a, h⟩, H _ _ h.symm pa⟩, fun ⟨⟨a, h⟩, pa⟩ =>
      ⟨⟨a, H _ _ h pa⟩, h⟩⟩

/-- The pre-set powerset operator -/
def powerset (x : PSet) : PSet :=
  ⟨Set x.Type, fun p => ⟨{ a // p a }, fun y => x.Func y.1⟩⟩

@[simp]
theorem mem_powerset : ∀ {x y : PSet}, y ∈ powerset x ↔ y ⊆ x
  | ⟨_, A⟩, ⟨_, B⟩ =>
    ⟨fun ⟨_, e⟩ => (Subset.congr_left e).2 fun ⟨a, _⟩ => ⟨a, Equiv.refl (A a)⟩, fun βα =>
      ⟨{ a | ∃ b, Equiv (B b) (A a) }, fun b =>
        let ⟨a, ba⟩ := βα b
        ⟨⟨a, b, ba⟩, ba⟩,
        fun ⟨_, b, ba⟩ => ⟨b, ba⟩⟩⟩

/-- The pre-set union operator -/
def sUnion (a : PSet) : PSet :=
  ⟨Σx, (a.Func x).Type, fun ⟨x, y⟩ => (a.Func x).Func y⟩

@[inherit_doc]
prefix:110 "⋃₀ " => sUnion

@[simp]
theorem mem_sUnion : ∀ {x y : PSet.{u}}, y ∈ ⋃₀ x ↔ ∃ z ∈ x, y ∈ z
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

@[simp]
theorem toSet_sUnion (x : PSet.{u}) : (⋃₀ x).toSet = ⋃₀ (toSet '' x.toSet) := by
  ext
  simp

/-- The image of a function from pre-sets to pre-sets. -/
def image (f : PSet.{u} → PSet.{u}) (x : PSet.{u}) : PSet :=
  ⟨x.Type, f ∘ x.Func⟩

-- Porting note: H arguments made explicit.
theorem mem_image {f : PSet.{u} → PSet.{u}} (H : ∀ x y, Equiv x y → Equiv (f x) (f y)) :
    ∀ {x y : PSet.{u}}, y ∈ image f x ↔ ∃ z ∈ x, Equiv y (f z)
  | ⟨_, A⟩, _ =>
    ⟨fun ⟨a, ya⟩ => ⟨A a, Mem.mk A a, ya⟩, fun ⟨_, ⟨a, za⟩, yz⟩ => ⟨a, yz.trans <| H _ _ za⟩⟩

/-- Universe lift operation -/
protected def Lift : PSet.{u} → PSet.{max u v}
  | ⟨α, A⟩ => ⟨ULift.{v, u} α, fun ⟨x⟩ => PSet.Lift (A x)⟩

-- intended to be used with explicit universe parameters
/-- Embedding of one universe in another -/
@[nolint checkUnivs]
def embed : PSet.{max (u + 1) v} :=
  ⟨ULift.{v, u + 1} PSet, fun ⟨x⟩ => PSet.Lift.{u, max (u + 1) v} x⟩

theorem lift_mem_embed : ∀ x : PSet.{u}, PSet.Lift.{u, max (u + 1) v} x ∈ embed.{u, v} := fun x =>
  ⟨⟨x⟩, Equiv.rfl⟩

/-- Function equivalence is defined so that `f ~ g` iff `∀ x y, x ~ y → f x ~ g y`. This extends to
equivalence of `n`-ary functions. -/
@[deprecated "No deprecation message was provided." (since := "2024-09-02")]
def Arity.Equiv : ∀ {n}, OfArity PSet.{u} PSet.{u} n → OfArity PSet.{u} PSet.{u} n → Prop
  | 0, a, b => PSet.Equiv a b
  | _ + 1, a, b => ∀ x y : PSet, PSet.Equiv x y → Arity.Equiv (a x) (b y)

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided." (since := "2024-09-02")]
theorem Arity.equiv_const {a : PSet.{u}} :
    ∀ n, Arity.Equiv (OfArity.const PSet.{u} a n) (OfArity.const PSet.{u} a n)
  | 0 => Equiv.rfl
  | _ + 1 => fun _ _ _ => Arity.equiv_const _

set_option linter.deprecated false in
/-- `resp n` is the collection of n-ary functions on `PSet` that respect
  equivalence, i.e. when the inputs are equivalent the output is as well. -/
@[deprecated "No deprecation message was provided." (since := "2024-09-02")]
def Resp (n) :=
  { x : OfArity PSet.{u} PSet.{u} n // Arity.Equiv x x }

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided." (since := "2024-09-02")]
instance Resp.inhabited {n} : Inhabited (Resp n) :=
  ⟨⟨OfArity.const _ default _, Arity.equiv_const _⟩⟩

set_option linter.deprecated false in
/-- The `n`-ary image of a `(n + 1)`-ary function respecting equivalence as a function respecting
equivalence. -/
@[deprecated "No deprecation message was provided." (since := "2024-09-02")]
def Resp.f {n} (f : Resp (n + 1)) (x : PSet) : Resp n :=
  ⟨f.1 x, f.2 _ _ <| Equiv.refl x⟩

set_option linter.deprecated false in
/-- Function equivalence for functions respecting equivalence. See `PSet.Arity.Equiv`. -/
@[deprecated "No deprecation message was provided." (since := "2024-09-02")]
def Resp.Equiv {n} (a b : Resp n) : Prop :=
  Arity.Equiv a.1 b.1

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided." (since := "2024-09-02"), refl]
protected theorem Resp.Equiv.refl {n} (a : Resp n) : Resp.Equiv a a :=
  a.2

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided." (since := "2024-09-02")]
protected theorem Resp.Equiv.euc :
    ∀ {n} {a b c : Resp n}, Resp.Equiv a b → Resp.Equiv c b → Resp.Equiv a c
  | 0, _, _, _, hab, hcb => PSet.Equiv.euc hab hcb
  | n + 1, a, b, c, hab, hcb => fun x y h =>
    @Resp.Equiv.euc n (a.f x) (b.f y) (c.f y) (hab _ _ h) (hcb _ _ <| PSet.Equiv.refl y)

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided." (since := "2024-09-02"), symm]
protected theorem Resp.Equiv.symm {n} {a b : Resp n} : Resp.Equiv a b → Resp.Equiv b a :=
  (Resp.Equiv.refl b).euc

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided." (since := "2024-09-02"), trans]
protected theorem Resp.Equiv.trans {n} {x y z : Resp n} (h1 : Resp.Equiv x y)
    (h2 : Resp.Equiv y z) : Resp.Equiv x z :=
  h1.euc h2.symm

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided." (since := "2024-09-02")]
instance Resp.setoid {n} : Setoid (Resp n) :=
  ⟨Resp.Equiv, Resp.Equiv.refl, Resp.Equiv.symm, Resp.Equiv.trans⟩

end PSet

/-- The ZFC universe of sets consists of the type of pre-sets,
  quotiented by extensional equivalence. -/
@[pp_with_univ]
def ZFSet : Type (u + 1) :=
  Quotient PSet.setoid.{u}

namespace ZFSet

/-- Turns a pre-set into a ZFC set. -/
def mk : PSet → ZFSet :=
  Quotient.mk''

@[simp]
theorem mk_eq (x : PSet) : @Eq ZFSet ⟦x⟧ (mk x) :=
  rfl

@[simp]
theorem mk_out : ∀ x : ZFSet, mk x.out = x :=
  Quotient.out_eq

/-- A set function is "definable" if it is the image of some n-ary `PSet`
  function. This isn't exactly definability, but is useful as a sufficient
  condition for functions that have a computable image. -/
class Definable (n) (f : (Fin n → ZFSet.{u}) → ZFSet.{u}) where
  /-- Turns a definable function into an n-ary `PSet` function. -/
  out : (Fin n → PSet.{u}) → PSet.{u}
  /-- A set function `f` is the image of `Definable.out f`. -/
  mk_out xs : mk (out xs) = f (mk <| xs ·) := by simp

attribute [simp] Definable.mk_out

/-- An abbrev of `ZFSet.Definable` for unary functions. -/
abbrev Definable₁ (f : ZFSet.{u} → ZFSet.{u}) := Definable 1 (fun s ↦ f (s 0))

/-- A simpler constructor for `ZFSet.Definable₁`. -/
abbrev Definable₁.mk {f : ZFSet.{u} → ZFSet.{u}}
    (out : PSet.{u} → PSet.{u}) (mk_out : ∀ x, ⟦out x⟧ = f ⟦x⟧) :
    Definable₁ f where
  out xs := out (xs 0)
  mk_out xs := mk_out (xs 0)

/-- Turns a unary definable function into a unary `PSet` function. -/
abbrev Definable₁.out (f : ZFSet.{u} → ZFSet.{u}) [Definable₁ f] :
    PSet.{u} → PSet.{u} :=
  fun x ↦ Definable.out (fun s ↦ f (s 0)) ![x]

lemma Definable₁.mk_out {f : ZFSet.{u} → ZFSet.{u}} [Definable₁ f]
    {x : PSet} :
    .mk (out f x) = f (.mk x) :=
  Definable.mk_out ![x]

/-- An abbrev of `ZFSet.Definable` for binary functions. -/
abbrev Definable₂ (f : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) := Definable 2 (fun s ↦ f (s 0) (s 1))

/-- A simpler constructor for `ZFSet.Definable₂`. -/
abbrev Definable₂.mk {f : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}}
    (out : PSet.{u} → PSet.{u} → PSet.{u}) (mk_out : ∀ x y, ⟦out x y⟧ = f ⟦x⟧ ⟦y⟧) :
    Definable₂ f where
  out xs := out (xs 0) (xs 1)
  mk_out xs := mk_out (xs 0) (xs 1)

/-- Turns a binary definable function into a binary `PSet` function. -/
abbrev Definable₂.out (f : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) [Definable₂ f] :
    PSet.{u} → PSet.{u} → PSet.{u} :=
  fun x y ↦ Definable.out (fun s ↦ f (s 0) (s 1)) ![x, y]

lemma Definable₂.mk_out {f : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}} [Definable₂ f]
    {x y : PSet} :
    .mk (out f x y) = f (.mk x) (.mk y) :=
  Definable.mk_out ![x, y]

instance (f) [Definable₁ f] (n g) [Definable n g] :
    Definable n (fun s ↦ f (g s)) where
  out xs := Definable₁.out f (Definable.out g xs)

instance (f) [Definable₂ f] (n g₁ g₂) [Definable n g₁] [Definable n g₂] :
    Definable n (fun s ↦ f (g₁ s) (g₂ s)) where
  out xs := Definable₂.out f (Definable.out g₁ xs) (Definable.out g₂ xs)

instance (n) (i) : Definable n (fun s ↦ s i) where
  out s := s i

lemma Definable.out_equiv {n} (f : (Fin n → ZFSet.{u}) → ZFSet.{u}) [Definable n f]
    {xs ys : Fin n → PSet} (h : ∀ i, xs i ≈ ys i) :
    out f xs ≈ out f ys := by
  rw [← Quotient.eq_iff_equiv, mk_eq, mk_eq, mk_out, mk_out]
  exact congrArg _ (funext fun i ↦ Quotient.sound (h i))

lemma Definable₁.out_equiv (f : ZFSet.{u} → ZFSet.{u}) [Definable₁ f]
    {x y : PSet} (h : x ≈ y) :
    out f x ≈ out f y :=
  Definable.out_equiv _ (by simp [h])

lemma Definable₂.out_equiv (f : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) [Definable₂ f]
    {x₁ y₁ x₂ y₂ : PSet} (h₁ : x₁ ≈ y₁) (h₂ : x₂ ≈ y₂) :
    out f x₁ x₂ ≈ out f y₁ y₂ :=
  Definable.out_equiv _ (by simp [Fin.forall_fin_succ, h₁, h₂])

end ZFSet

namespace PSet

namespace Resp

set_option linter.deprecated false in
/-- Helper function for `PSet.eval`. -/
@[deprecated "No deprecation message was provided." (since := "2024-09-02")]
def evalAux :
    ∀ {n},
      { f : Resp n → OfArity ZFSet.{u} ZFSet.{u} n // ∀ a b : Resp n, Resp.Equiv a b → f a = f b }
  | 0 => ⟨fun a => ⟦a.1⟧, fun _ _ h => Quotient.sound h⟩
  | n + 1 =>
    let F : Resp (n + 1) → OfArity ZFSet ZFSet (n + 1) := fun a =>
      @Quotient.lift _ _ PSet.setoid (fun x => evalAux.1 (a.f x)) fun _ _ h =>
        evalAux.2 _ _ (a.2 _ _ h)
    ⟨F, fun b c h =>
      funext <|
        (@Quotient.ind _ _ fun q => F b q = F c q) fun z =>
          evalAux.2 (Resp.f b z) (Resp.f c z) (h _ _ (PSet.Equiv.refl z))⟩

set_option linter.deprecated false in
/-- An equivalence-respecting function yields an n-ary ZFC set function. -/
@[deprecated "No deprecation message was provided." (since := "2024-09-02")]
def eval (n) : Resp n → OfArity ZFSet.{u} ZFSet.{u} n :=
  evalAux.1

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided." (since := "2024-09-02")]
theorem eval_val {n f x} :
    (@eval (n + 1) f : ZFSet → OfArity ZFSet ZFSet n) ⟦x⟧ = eval n (Resp.f f x) :=
  rfl

end Resp

set_option linter.deprecated false in
/-- A set function is "definable" if it is the image of some n-ary pre-set
  function. This isn't exactly definability, but is useful as a sufficient
  condition for functions that have a computable image. -/
@[deprecated "No deprecation message was provided." (since := "2024-09-02")]
class inductive Definable (n) : OfArity ZFSet.{u} ZFSet.{u} n → Type (u + 1)
  | mk (f) : Definable n (Resp.eval n f)

attribute [deprecated "No deprecation message was provided." (since := "2024-09-02"), instance]
  Definable.mk

set_option linter.deprecated false in
/-- The evaluation of a function respecting equivalence is definable, by that same function. -/
@[deprecated "No deprecation message was provided." (since := "2024-09-02")]
def Definable.EqMk {n} (f) :
    ∀ {s : OfArity ZFSet.{u} ZFSet.{u} n} (_ : Resp.eval _ f = s), Definable n s
  | _, rfl => ⟨f⟩

set_option linter.deprecated false in
/-- Turns a definable function into a function that respects equivalence. -/
@[deprecated "No deprecation message was provided." (since := "2024-09-02")]
def Definable.Resp {n} : ∀ (s : OfArity ZFSet.{u} ZFSet.{u} n) [Definable n s], Resp n
  | _, ⟨f⟩ => f

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided." (since := "2024-09-02")]
theorem Definable.eq {n} :
    ∀ (s : OfArity ZFSet.{u} ZFSet.{u} n) [H : Definable n s], (@Definable.Resp n s H).eval _ = s
  | _, ⟨_⟩ => rfl

end PSet

namespace Classical

open PSet ZFSet

set_option linter.deprecated false in
/-- All functions are classically definable. -/
@[deprecated "No deprecation message was provided." (since := "2024-09-02")]
noncomputable def allDefinable : ∀ {n} (F : OfArity ZFSet ZFSet n), Definable n F
  | 0, F =>
    let p := @Quotient.exists_rep PSet _ F
    @Definable.EqMk 0 ⟨choose p, Equiv.rfl⟩ _ (choose_spec p)
  | n + 1, (F : OfArity ZFSet ZFSet (n + 1)) => by
    have I : (x : ZFSet) → Definable n (F x) := fun x => allDefinable (F x)
    refine @Definable.EqMk (n + 1) ⟨fun x : PSet => (@Definable.Resp _ _ (I ⟦x⟧)).1, ?_⟩ _ ?_
    · dsimp only [Arity.Equiv]
      intro x y h
      rw [@Quotient.sound PSet _ _ _ h]
      exact (Definable.Resp (F ⟦y⟧)).2
    refine funext fun q => Quotient.inductionOn q fun x => ?_
    simp_rw [Resp.eval_val, Resp.f]
    exact @Definable.eq _ (F ⟦x⟧) (I ⟦x⟧)

/-- All functions are classically definable. -/
noncomputable def allZFSetDefinable {n} (F : (Fin n → ZFSet.{u}) → ZFSet.{u}) : Definable n F where
  out xs := (F (mk <| xs ·)).out

end Classical

namespace ZFSet

open PSet hiding Definable

theorem eq {x y : PSet} : mk x = mk y ↔ Equiv x y :=
  Quotient.eq

theorem sound {x y : PSet} (h : PSet.Equiv x y) : mk x = mk y :=
  Quotient.sound h

theorem exact {x y : PSet} : mk x = mk y → PSet.Equiv x y :=
  Quotient.exact

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided." (since := "2024-09-02"), simp]
theorem eval_mk {n f x} :
    (@Resp.eval (n + 1) f : ZFSet → OfArity ZFSet ZFSet n) (mk x) = Resp.eval n (Resp.f f x) :=
  rfl

/-- The membership relation for ZFC sets is inherited from the membership relation for pre-sets. -/
protected def Mem : ZFSet → ZFSet → Prop :=
  Quotient.lift₂ (· ∈ ·) fun _ _ _ _ hx hy =>
    propext ((Mem.congr_left hx).trans (Mem.congr_right hy))

instance : Membership ZFSet ZFSet where
  mem t s := ZFSet.Mem s t

@[simp]
theorem mk_mem_iff {x y : PSet} : mk x ∈ mk y ↔ x ∈ y :=
  Iff.rfl

/-- Convert a ZFC set into a `Set` of ZFC sets -/
def toSet (u : ZFSet.{u}) : Set ZFSet.{u} :=
  { x | x ∈ u }

@[simp]
theorem mem_toSet (a u : ZFSet.{u}) : a ∈ u.toSet ↔ a ∈ u :=
  Iff.rfl

instance small_toSet (x : ZFSet.{u}) : Small.{u} x.toSet :=
  Quotient.inductionOn x fun a => by
    let f : a.Type → (mk a).toSet := fun i => ⟨mk <| a.Func i, func_mem a i⟩
    suffices Function.Surjective f by exact small_of_surjective this
    rintro ⟨y, hb⟩
    induction y using Quotient.inductionOn
    obtain ⟨i, h⟩ := hb
    exact ⟨i, Subtype.coe_injective (Quotient.sound h.symm)⟩

/-- A nonempty set is one that contains some element. -/
protected def Nonempty (u : ZFSet) : Prop :=
  u.toSet.Nonempty

theorem nonempty_def (u : ZFSet) : u.Nonempty ↔ ∃ x, x ∈ u :=
  Iff.rfl

theorem nonempty_of_mem {x u : ZFSet} (h : x ∈ u) : u.Nonempty :=
  ⟨x, h⟩

@[simp]
theorem nonempty_toSet_iff {u : ZFSet} : u.toSet.Nonempty ↔ u.Nonempty :=
  Iff.rfl

/-- `x ⊆ y` as ZFC sets means that all members of `x` are members of `y`. -/
protected def Subset (x y : ZFSet.{u}) :=
  ∀ ⦃z⦄, z ∈ x → z ∈ y

instance hasSubset : HasSubset ZFSet :=
  ⟨ZFSet.Subset⟩

theorem subset_def {x y : ZFSet.{u}} : x ⊆ y ↔ ∀ ⦃z⦄, z ∈ x → z ∈ y :=
  Iff.rfl

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

@[simp]
theorem toSet_subset_iff {x y : ZFSet} : x.toSet ⊆ y.toSet ↔ x ⊆ y := by
  simp [subset_def, Set.subset_def]

@[ext]
theorem ext {x y : ZFSet.{u}} : (∀ z : ZFSet.{u}, z ∈ x ↔ z ∈ y) → x = y :=
  Quotient.inductionOn₂ x y fun _ _ h => Quotient.sound (Mem.ext fun w => h ⟦w⟧)

theorem toSet_injective : Function.Injective toSet := fun _ _ h => ext <| Set.ext_iff.1 h

@[simp]
theorem toSet_inj {x y : ZFSet} : x.toSet = y.toSet ↔ x = y :=
  toSet_injective.eq_iff

instance : IsAntisymm ZFSet (· ⊆ ·) :=
  ⟨fun _ _ hab hba => ext fun c => ⟨@hab c, @hba c⟩⟩

/-- The empty ZFC set -/
protected def empty : ZFSet :=
  mk ∅

instance : EmptyCollection ZFSet :=
  ⟨ZFSet.empty⟩

instance : Inhabited ZFSet :=
  ⟨∅⟩

@[simp]
theorem not_mem_empty (x) : x ∉ (∅ : ZFSet.{u}) :=
  Quotient.inductionOn x PSet.not_mem_empty

@[simp]
theorem toSet_empty : toSet ∅ = ∅ := by simp [toSet]

@[simp]
theorem empty_subset (x : ZFSet.{u}) : (∅ : ZFSet) ⊆ x :=
  Quotient.inductionOn x fun y => subset_iff.2 <| PSet.empty_subset y

@[simp]
theorem not_nonempty_empty : ¬ZFSet.Nonempty ∅ := by simp [ZFSet.Nonempty]

@[simp]
theorem nonempty_mk_iff {x : PSet} : (mk x).Nonempty ↔ x.Nonempty := by
  refine ⟨?_, fun ⟨a, h⟩ => ⟨mk a, h⟩⟩
  rintro ⟨a, h⟩
  induction a using Quotient.inductionOn
  exact ⟨_, h⟩

theorem eq_empty (x : ZFSet.{u}) : x = ∅ ↔ ∀ y : ZFSet.{u}, y ∉ x := by
  simp [ZFSet.ext_iff]

theorem eq_empty_or_nonempty (u : ZFSet) : u = ∅ ∨ u.Nonempty := by
  rw [eq_empty, ← not_exists]
  apply em'

/-- `Insert x y` is the set `{x} ∪ y` -/
protected def Insert : ZFSet → ZFSet → ZFSet :=
  Quotient.map₂ PSet.insert
    fun _ _ uv ⟨_, _⟩ ⟨_, _⟩ ⟨αβ, βα⟩ =>
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
        | none => ⟨none, uv⟩⟩

instance : Insert ZFSet ZFSet :=
  ⟨ZFSet.Insert⟩

instance : Singleton ZFSet ZFSet :=
  ⟨fun x => insert x ∅⟩

instance : LawfulSingleton ZFSet ZFSet :=
  ⟨fun _ => rfl⟩

@[simp]
theorem mem_insert_iff {x y z : ZFSet.{u}} : x ∈ insert y z ↔ x = y ∨ x ∈ z :=
  Quotient.inductionOn₃ x y z fun _ _ _ => PSet.mem_insert_iff.trans (or_congr_left eq.symm)

theorem mem_insert (x y : ZFSet) : x ∈ insert x y :=
  mem_insert_iff.2 <| Or.inl rfl

theorem mem_insert_of_mem {y z : ZFSet} (x) (h : z ∈ y) : z ∈ insert x y :=
  mem_insert_iff.2 <| Or.inr h

@[simp]
theorem toSet_insert (x y : ZFSet) : (insert x y).toSet = insert x y.toSet := by
  ext
  simp

@[simp]
theorem mem_singleton {x y : ZFSet.{u}} : x ∈ @singleton ZFSet.{u} ZFSet.{u} _ y ↔ x = y :=
  Quotient.inductionOn₂ x y fun _ _ => PSet.mem_singleton.trans eq.symm

@[simp]
theorem toSet_singleton (x : ZFSet) : ({x} : ZFSet).toSet = {x} := by
  ext
  simp

theorem insert_nonempty (u v : ZFSet) : (insert u v).Nonempty :=
  ⟨u, mem_insert u v⟩

theorem singleton_nonempty (u : ZFSet) : ZFSet.Nonempty {u} :=
  insert_nonempty u ∅

theorem mem_pair {x y z : ZFSet.{u}} : x ∈ ({y, z} : ZFSet) ↔ x = y ∨ x = z := by
  simp

@[simp]
theorem pair_eq_singleton (x : ZFSet) : {x, x} = ({x} : ZFSet) := by
  ext
  simp

@[simp]
theorem pair_eq_singleton_iff {x y z : ZFSet} : ({x, y} : ZFSet) = {z} ↔ x = z ∧ y = z := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rw [← mem_singleton, ← mem_singleton]
    simp [← h]
  · rintro ⟨rfl, rfl⟩
    exact pair_eq_singleton y

@[simp]
theorem singleton_eq_pair_iff {x y z : ZFSet} : ({x} : ZFSet) = {y, z} ↔ x = y ∧ x = z := by
  rw [eq_comm, pair_eq_singleton_iff]
  simp_rw [eq_comm]

/-- `omega` is the first infinite von Neumann ordinal -/
def omega : ZFSet :=
  mk PSet.omega

@[simp]
theorem omega_zero : ∅ ∈ omega :=
  ⟨⟨0⟩, Equiv.rfl⟩

@[simp]
theorem omega_succ {n} : n ∈ omega.{u} → insert n n ∈ omega.{u} :=
  Quotient.inductionOn n fun x ⟨⟨n⟩, h⟩ =>
    ⟨⟨n + 1⟩,
      ZFSet.exact <|
        show insert (mk x) (mk x) = insert (mk <| ofNat n) (mk <| ofNat n) by
          rw [ZFSet.sound h]
          rfl⟩

/-- `{x ∈ a | p x}` is the set of elements in `a` satisfying `p` -/
protected def sep (p : ZFSet → Prop) : ZFSet → ZFSet :=
  Quotient.map (PSet.sep fun y => p (mk y))
    fun ⟨α, A⟩ ⟨β, B⟩ ⟨αβ, βα⟩ =>
      ⟨fun ⟨a, pa⟩ =>
        let ⟨b, hb⟩ := αβ a
        ⟨⟨b, by simpa only [mk_func, ← ZFSet.sound hb]⟩, hb⟩,
        fun ⟨b, pb⟩ =>
        let ⟨a, ha⟩ := βα b
        ⟨⟨a, by simpa only [mk_func, ZFSet.sound ha]⟩, ha⟩⟩

-- Porting note: the { x | p x } notation appears to be disabled in Lean 4.
instance : Sep ZFSet ZFSet :=
  ⟨ZFSet.sep⟩

@[simp]
theorem mem_sep {p : ZFSet.{u} → Prop} {x y : ZFSet.{u}} :
    y ∈ ZFSet.sep p x ↔ y ∈ x ∧ p y :=
  Quotient.inductionOn₂ x y fun _ _ =>
    PSet.mem_sep (p := p ∘ mk) fun _ _ h => (Quotient.sound h).subst

@[simp]
theorem sep_empty (p : ZFSet → Prop) : (∅ : ZFSet).sep p = ∅ :=
  (eq_empty _).mpr fun _ h ↦ not_mem_empty _ (mem_sep.mp h).1

@[simp]
theorem toSet_sep (a : ZFSet) (p : ZFSet → Prop) :
    (ZFSet.sep p a).toSet = { x ∈ a.toSet | p x } := by
  ext
  simp

/-- The powerset operation, the collection of subsets of a ZFC set -/
def powerset : ZFSet → ZFSet :=
  Quotient.map PSet.powerset
    fun ⟨_, A⟩ ⟨_, B⟩ ⟨αβ, βα⟩ =>
      ⟨fun p =>
        ⟨{ b | ∃ a, p a ∧ Equiv (A a) (B b) }, fun ⟨a, pa⟩ =>
          let ⟨b, ab⟩ := αβ a
          ⟨⟨b, a, pa, ab⟩, ab⟩,
          fun ⟨_, a, pa, ab⟩ => ⟨⟨a, pa⟩, ab⟩⟩,
        fun q =>
        ⟨{ a | ∃ b, q b ∧ Equiv (A a) (B b) }, fun ⟨_, b, qb, ab⟩ => ⟨⟨b, qb⟩, ab⟩, fun ⟨b, qb⟩ =>
          let ⟨a, ab⟩ := βα b
          ⟨⟨a, b, qb, ab⟩, ab⟩⟩⟩

@[simp]
theorem mem_powerset {x y : ZFSet.{u}} : y ∈ powerset x ↔ y ⊆ x :=
  Quotient.inductionOn₂ x y fun _ _ => PSet.mem_powerset.trans subset_iff.symm

theorem sUnion_lem {α β : Type u} (A : α → PSet) (B : β → PSet) (αβ : ∀ a, ∃ b, Equiv (A a) (B b)) :
    ∀ a, ∃ b, Equiv ((sUnion ⟨α, A⟩).Func a) ((sUnion ⟨β, B⟩).Func b)
  | ⟨a, c⟩ => by
    let ⟨b, hb⟩ := αβ a
    induction' ea : A a with γ Γ
    induction' eb : B b with δ Δ
    rw [ea, eb] at hb
    obtain ⟨γδ, δγ⟩ := hb
    let c : (A a).Type := c
    let ⟨d, hd⟩ := γδ (by rwa [ea] at c)
    use ⟨b, Eq.ndrec d (Eq.symm eb)⟩
    change PSet.Equiv ((A a).Func c) ((B b).Func (Eq.ndrec d eb.symm))
    match A a, B b, ea, eb, c, d, hd with
    | _, _, rfl, rfl, _, _, hd => exact hd

/-- The union operator, the collection of elements of elements of a ZFC set -/
def sUnion : ZFSet → ZFSet :=
  Quotient.map PSet.sUnion
    fun ⟨_, A⟩ ⟨_, B⟩ ⟨αβ, βα⟩ =>
      ⟨sUnion_lem A B αβ, fun a =>
        Exists.elim
          (sUnion_lem B A (fun b => Exists.elim (βα b) fun c hc => ⟨c, PSet.Equiv.symm hc⟩) a)
          fun b hb => ⟨b, PSet.Equiv.symm hb⟩⟩

@[inherit_doc]
prefix:110 "⋃₀ " => ZFSet.sUnion

/-- The intersection operator, the collection of elements in all of the elements of a ZFC set. We
define `⋂₀ ∅ = ∅`. -/
def sInter (x : ZFSet) : ZFSet := (⋃₀ x).sep (fun y => ∀ z ∈ x, y ∈ z)

@[inherit_doc]
prefix:110 "⋂₀ " => ZFSet.sInter

@[simp]
theorem mem_sUnion {x y : ZFSet.{u}} : y ∈ ⋃₀ x ↔ ∃ z ∈ x, y ∈ z :=
  Quotient.inductionOn₂ x y fun _ _ => PSet.mem_sUnion.trans
    ⟨fun ⟨z, h⟩ => ⟨⟦z⟧, h⟩, fun ⟨z, h⟩ => Quotient.inductionOn z (fun z h => ⟨z, h⟩) h⟩

theorem mem_sInter {x y : ZFSet} (h : x.Nonempty) : y ∈ ⋂₀ x ↔ ∀ z ∈ x, y ∈ z := by
  unfold sInter
  simp only [and_iff_right_iff_imp, mem_sep]
  intro mem
  apply mem_sUnion.mpr
  replace ⟨s, h⟩ := h
  exact ⟨_, h, mem _ h⟩

@[simp]
theorem sUnion_empty : ⋃₀ (∅ : ZFSet.{u}) = ∅ := by
  ext
  simp

@[simp]
theorem sInter_empty : ⋂₀ (∅ : ZFSet) = ∅ := by simp [sInter]

theorem mem_of_mem_sInter {x y z : ZFSet} (hy : y ∈ ⋂₀ x) (hz : z ∈ x) : y ∈ z := by
  rcases eq_empty_or_nonempty x with (rfl | hx)
  · exact (not_mem_empty z hz).elim
  · exact (mem_sInter hx).1 hy z hz

theorem mem_sUnion_of_mem {x y z : ZFSet} (hy : y ∈ z) (hz : z ∈ x) : y ∈ ⋃₀ x :=
  mem_sUnion.2 ⟨z, hz, hy⟩

theorem not_mem_sInter_of_not_mem {x y z : ZFSet} (hy : ¬y ∈ z) (hz : z ∈ x) : ¬y ∈ ⋂₀ x :=
  fun hx => hy <| mem_of_mem_sInter hx hz

@[simp]
theorem sUnion_singleton {x : ZFSet.{u}} : ⋃₀ ({x} : ZFSet) = x :=
  ext fun y => by simp_rw [mem_sUnion, mem_singleton, exists_eq_left]

@[simp]
theorem sInter_singleton {x : ZFSet.{u}} : ⋂₀ ({x} : ZFSet) = x :=
  ext fun y => by simp_rw [mem_sInter (singleton_nonempty x), mem_singleton, forall_eq]

@[simp]
theorem toSet_sUnion (x : ZFSet.{u}) : (⋃₀ x).toSet = ⋃₀ (toSet '' x.toSet) := by
  ext
  simp

theorem toSet_sInter {x : ZFSet.{u}} (h : x.Nonempty) : (⋂₀ x).toSet = ⋂₀ (toSet '' x.toSet) := by
  ext
  simp [mem_sInter h]

theorem singleton_injective : Function.Injective (@singleton ZFSet ZFSet _) := fun x y H => by
  let this := congr_arg sUnion H
  rwa [sUnion_singleton, sUnion_singleton] at this

@[simp]
theorem singleton_inj {x y : ZFSet} : ({x} : ZFSet) = {y} ↔ x = y :=
  singleton_injective.eq_iff

/-- The binary union operation -/
protected def union (x y : ZFSet.{u}) : ZFSet.{u} :=
  ⋃₀ {x, y}

/-- The binary intersection operation -/
protected def inter (x y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∈ y) x -- { z ∈ x | z ∈ y }

/-- The set difference operation -/
protected def diff (x y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∉ y) x -- { z ∈ x | z ∉ y }

instance : Union ZFSet :=
  ⟨ZFSet.union⟩

instance : Inter ZFSet :=
  ⟨ZFSet.inter⟩

instance : SDiff ZFSet :=
  ⟨ZFSet.diff⟩

@[simp]
theorem toSet_union (x y : ZFSet.{u}) : (x ∪ y).toSet = x.toSet ∪ y.toSet := by
  change (⋃₀ {x, y}).toSet = _
  simp

@[simp]
theorem toSet_inter (x y : ZFSet.{u}) : (x ∩ y).toSet = x.toSet ∩ y.toSet := by
  change (ZFSet.sep (fun z => z ∈ y) x).toSet = _
  ext
  simp

@[simp]
theorem toSet_sdiff (x y : ZFSet.{u}) : (x \ y).toSet = x.toSet \ y.toSet := by
  change (ZFSet.sep (fun z => z ∉ y) x).toSet = _
  ext
  simp

@[simp]
theorem mem_union {x y z : ZFSet.{u}} : z ∈ x ∪ y ↔ z ∈ x ∨ z ∈ y := by
  rw [← mem_toSet]
  simp

@[simp]
theorem mem_inter {x y z : ZFSet.{u}} : z ∈ x ∩ y ↔ z ∈ x ∧ z ∈ y :=
  @mem_sep (fun z : ZFSet.{u} => z ∈ y) x z

@[simp]
theorem mem_diff {x y z : ZFSet.{u}} : z ∈ x \ y ↔ z ∈ x ∧ z ∉ y :=
  @mem_sep (fun z : ZFSet.{u} => z ∉ y) x z

@[simp]
theorem sUnion_pair {x y : ZFSet.{u}} : ⋃₀ ({x, y} : ZFSet.{u}) = x ∪ y :=
  rfl

theorem mem_wf : @WellFounded ZFSet (· ∈ ·) :=
  (wellFounded_lift₂_iff (H := fun a b c d hx hy =>
    propext ((@Mem.congr_left a c hx).trans (@Mem.congr_right b d hy _)))).mpr PSet.mem_wf

/-- Induction on the `∈` relation. -/
@[elab_as_elim]
theorem inductionOn {p : ZFSet → Prop} (x) (h : ∀ x, (∀ y ∈ x, p y) → p x) : p x :=
  mem_wf.induction x h

instance : IsWellFounded ZFSet (· ∈ ·) :=
  ⟨mem_wf⟩

instance : WellFoundedRelation ZFSet :=
  ⟨_, mem_wf⟩

theorem mem_asymm {x y : ZFSet} : x ∈ y → y ∉ x :=
  asymm_of (· ∈ ·)

theorem mem_irrefl (x : ZFSet) : x ∉ x :=
  irrefl_of (· ∈ ·) x

theorem not_subset_of_mem {x y : ZFSet} (h : x ∈ y) : ¬ y ⊆ x :=
  fun h' ↦ mem_irrefl _ (h' h)

theorem not_mem_of_subset {x y : ZFSet} (h : x ⊆ y) : y ∉ x :=
  imp_not_comm.2 not_subset_of_mem h

theorem regularity (x : ZFSet.{u}) (h : x ≠ ∅) : ∃ y ∈ x, x ∩ y = ∅ :=
  by_contradiction fun ne =>
    h <| (eq_empty x).2 fun y =>
      @inductionOn (fun z => z ∉ x) y fun z IH zx =>
        ne ⟨z, zx, (eq_empty _).2 fun w wxz =>
          let ⟨wx, wz⟩ := mem_inter.1 wxz
          IH w wz wx⟩

/-- The image of a (definable) ZFC set function -/
def image (f : ZFSet → ZFSet) [Definable₁ f] : ZFSet → ZFSet :=
  let r := Definable₁.out f
  Quotient.map (PSet.image r)
    fun _ _ e =>
      Mem.ext fun _ =>
        (mem_image (fun _ _ ↦ Definable₁.out_equiv _)).trans <|
          Iff.trans
              ⟨fun ⟨w, h1, h2⟩ => ⟨w, (Mem.congr_right e).1 h1, h2⟩, fun ⟨w, h1, h2⟩ =>
                ⟨w, (Mem.congr_right e).2 h1, h2⟩⟩ <|
            (mem_image (fun _ _ ↦ Definable₁.out_equiv _)).symm

theorem image.mk (f : ZFSet.{u} → ZFSet.{u}) [Definable₁ f] (x) {y} : y ∈ x → f y ∈ image f x :=
  Quotient.inductionOn₂ x y fun ⟨_, _⟩ _ ⟨a, ya⟩ => by
    simp only [mk_eq, ← Definable₁.mk_out (f := f)]
    exact ⟨a, Definable₁.out_equiv f ya⟩

@[simp]
theorem mem_image {f : ZFSet.{u} → ZFSet.{u}} [Definable₁ f] {x y : ZFSet.{u}} :
    y ∈ image f x ↔ ∃ z ∈ x, f z = y :=
  Quotient.inductionOn₂ x y fun ⟨_, A⟩ _ =>
    ⟨fun ⟨a, ya⟩ => ⟨⟦A a⟧, Mem.mk A a, ((Quotient.sound ya).trans Definable₁.mk_out).symm⟩,
      fun ⟨_, hz, e⟩ => e ▸ image.mk _ _ hz⟩

@[simp]
theorem toSet_image (f : ZFSet → ZFSet) [Definable₁ f] (x : ZFSet) :
    (image f x).toSet = f '' x.toSet := by
  ext
  simp

/-- The range of a type-indexed family of sets. -/
noncomputable def range {α} [Small.{u} α] (f : α → ZFSet.{u}) : ZFSet.{u} :=
  ⟦⟨_, Quotient.out ∘ f ∘ (equivShrink α).symm⟩⟧

@[simp]
theorem mem_range {α} [Small.{u} α] {f : α → ZFSet.{u}} {x : ZFSet.{u}} :
    x ∈ range f ↔ x ∈ Set.range f :=
  Quotient.inductionOn x fun y => by
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨(equivShrink α).symm z, Quotient.eq_mk_iff_out.2 hz.symm⟩
    · rintro ⟨z, hz⟩
      use equivShrink α z
      simpa [hz] using PSet.Equiv.symm (Quotient.mk_out y)

@[simp]
theorem toSet_range {α} [Small.{u} α] (f : α → ZFSet.{u}) :
    (range f).toSet = Set.range f := by
  ext
  simp

/-- Kuratowski ordered pair -/
def pair (x y : ZFSet.{u}) : ZFSet.{u} :=
  {{x}, {x, y}}

@[simp]
theorem toSet_pair (x y : ZFSet.{u}) : (pair x y).toSet = {{x}, {x, y}} := by simp [pair]

/-- A subset of pairs `{(a, b) ∈ x × y | p a b}` -/
def pairSep (p : ZFSet.{u} → ZFSet.{u} → Prop) (x y : ZFSet.{u}) : ZFSet.{u} :=
  (powerset (powerset (x ∪ y))).sep fun z => ∃ a ∈ x, ∃ b ∈ y, z = pair a b ∧ p a b

@[simp]
theorem mem_pairSep {p} {x y z : ZFSet.{u}} :
    z ∈ pairSep p x y ↔ ∃ a ∈ x, ∃ b ∈ y, z = pair a b ∧ p a b := by
  refine mem_sep.trans ⟨And.right, fun e => ⟨?_, e⟩⟩
  rcases e with ⟨a, ax, b, bY, rfl, pab⟩
  simp only [mem_powerset, subset_def, mem_union, pair, mem_pair]
  rintro u (rfl | rfl) v <;> simp only [mem_singleton, mem_pair]
  · rintro rfl
    exact Or.inl ax
  · rintro (rfl | rfl) <;> [left; right] <;> assumption

theorem pair_injective : Function.Injective2 pair := by
  intro x x' y y' H
  simp_rw [ZFSet.ext_iff, pair, mem_pair] at H
  obtain rfl : x = x' := And.left <| by simpa [or_and_left] using (H {x}).1 (Or.inl rfl)
  have he : y = x → y = y' := by
    rintro rfl
    simpa [eq_comm] using H {y, y'}
  have hx := H {x, y}
  simp_rw [pair_eq_singleton_iff, true_and, or_true, true_iff] at hx
  refine ⟨rfl, hx.elim he fun hy ↦ Or.elim ?_ he id⟩
  simpa using ZFSet.ext_iff.1 hy y

@[simp]
theorem pair_inj {x y x' y' : ZFSet} : pair x y = pair x' y' ↔ x = x' ∧ y = y' :=
  pair_injective.eq_iff

/-- The cartesian product, `{(a, b) | a ∈ x, b ∈ y}` -/
def prod : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} :=
  pairSep fun _ _ => True

@[simp]
theorem mem_prod {x y z : ZFSet.{u}} : z ∈ prod x y ↔ ∃ a ∈ x, ∃ b ∈ y, z = pair a b := by
  simp [prod]

theorem pair_mem_prod {x y a b : ZFSet.{u}} : pair a b ∈ prod x y ↔ a ∈ x ∧ b ∈ y := by
  simp

/-- `isFunc x y f` is the assertion that `f` is a subset of `x × y` which relates to each element
of `x` a unique element of `y`, so that we can consider `f` as a ZFC function `x → y`. -/
def IsFunc (x y f : ZFSet.{u}) : Prop :=
  f ⊆ prod x y ∧ ∀ z : ZFSet.{u}, z ∈ x → ∃! w, pair z w ∈ f

/-- `funs x y` is `y ^ x`, the set of all set functions `x → y` -/
def funs (x y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (IsFunc x y) (powerset (prod x y))

@[simp]
theorem mem_funs {x y f : ZFSet.{u}} : f ∈ funs x y ↔ IsFunc x y f := by simp [funs, IsFunc]

instance : Definable₁ ({·}) := .mk ({·}) (fun _ ↦ rfl)
instance : Definable₂ insert := .mk insert (fun _ _ ↦ rfl)
instance : Definable₂ pair := by unfold pair; infer_instance

/-- Graph of a function: `map f x` is the ZFC function which maps `a ∈ x` to `f a` -/
def map (f : ZFSet → ZFSet) [Definable₁ f] : ZFSet → ZFSet :=
  image fun y => pair y (f y)

@[simp]
theorem mem_map {f : ZFSet → ZFSet} [Definable₁ f] {x y : ZFSet} :
    y ∈ map f x ↔ ∃ z ∈ x, pair z (f z) = y :=
  mem_image

theorem map_unique {f : ZFSet.{u} → ZFSet.{u}} [Definable₁ f] {x z : ZFSet.{u}}
    (zx : z ∈ x) : ∃! w, pair z w ∈ map f x :=
  ⟨f z, image.mk _ _ zx, fun y yx => by
    let ⟨w, _, we⟩ := mem_image.1 yx
    let ⟨wz, fy⟩ := pair_injective we
    rw [← fy, wz]⟩

@[simp]
theorem map_isFunc {f : ZFSet → ZFSet} [Definable₁ f] {x y : ZFSet} :
    IsFunc x y (map f x) ↔ ∀ z ∈ x, f z ∈ y :=
  ⟨fun ⟨ss, h⟩ z zx =>
    let ⟨_, t1, t2⟩ := h z zx
    (t2 (f z) (image.mk _ _ zx)).symm ▸ (pair_mem_prod.1 (ss t1)).right,
    fun h =>
    ⟨fun _ yx =>
      let ⟨z, zx, ze⟩ := mem_image.1 yx
      ze ▸ pair_mem_prod.2 ⟨zx, h z zx⟩,
      fun _ => map_unique⟩⟩

/-- Given a predicate `p` on ZFC sets. `Hereditarily p x` means that `x` has property `p` and the
members of `x` are all `Hereditarily p`. -/
def Hereditarily (p : ZFSet → Prop) (x : ZFSet) : Prop :=
  p x ∧ ∀ y ∈ x, Hereditarily p y
termination_by x

section Hereditarily

variable {p : ZFSet.{u} → Prop} {x y : ZFSet.{u}}

theorem hereditarily_iff : Hereditarily p x ↔ p x ∧ ∀ y ∈ x, Hereditarily p y := by
  rw [← Hereditarily]

alias ⟨Hereditarily.def, _⟩ := hereditarily_iff

theorem Hereditarily.self (h : x.Hereditarily p) : p x :=
  h.def.1

theorem Hereditarily.mem (h : x.Hereditarily p) (hy : y ∈ x) : y.Hereditarily p :=
  h.def.2 _ hy

theorem Hereditarily.empty : Hereditarily p x → p ∅ := by
  apply @ZFSet.inductionOn _ x
  intro y IH h
  rcases ZFSet.eq_empty_or_nonempty y with (rfl | ⟨a, ha⟩)
  · exact h.self
  · exact IH a ha (h.mem ha)

end Hereditarily

end ZFSet

/-- The collection of all classes.
We define `Class` as `Set ZFSet`, as this allows us to get many instances automatically. However, in
practice, we treat it as (the definitionally equal) `ZFSet → Prop`. This means, the preferred way to
state that `x : ZFSet` belongs to `A : Class` is to write `A x`. -/
@[pp_with_univ]
def Class :=
  Set ZFSet deriving HasSubset, EmptyCollection, Nonempty, Union, Inter, HasCompl, SDiff

instance : Insert ZFSet Class :=
  ⟨Set.insert⟩

namespace Class

-- Porting note: this used to be a `deriving HasSep Set` instance,
-- it should probably be turned into notation.
/-- `{x ∈ A | p x}` is the class of elements in `A` satisfying `p` -/
protected def sep (p : ZFSet → Prop) (A : Class) : Class :=
  {y | A y ∧ p y}

@[ext]
theorem ext {x y : Class.{u}} : (∀ z : ZFSet.{u}, x z ↔ y z) → x = y :=
  Set.ext

/-- Coerce a ZFC set into a class -/
@[coe]
def ofSet (x : ZFSet.{u}) : Class.{u} :=
  { y | y ∈ x }

instance : Coe ZFSet Class :=
  ⟨ofSet⟩

/-- The universal class -/
def univ : Class :=
  Set.univ

/-- Assert that `A` is a ZFC set satisfying `B` -/
def ToSet (B : Class.{u}) (A : Class.{u}) : Prop :=
  ∃ x : ZFSet, ↑x = A ∧ B x

/-- `A ∈ B` if `A` is a ZFC set which satisfies `B` -/
protected def Mem (B A : Class.{u}) : Prop :=
  ToSet.{u} B A

instance : Membership Class Class :=
  ⟨Class.Mem⟩

theorem mem_def (A B : Class.{u}) : A ∈ B ↔ ∃ x : ZFSet, ↑x = A ∧ B x :=
  Iff.rfl

@[simp]
theorem not_mem_empty (x : Class.{u}) : x ∉ (∅ : Class.{u}) := fun ⟨_, _, h⟩ => h

@[simp]
theorem not_empty_hom (x : ZFSet.{u}) : ¬(∅ : Class.{u}) x :=
  id

@[simp]
theorem mem_univ {A : Class.{u}} : A ∈ univ.{u} ↔ ∃ x : ZFSet.{u}, ↑x = A :=
  exists_congr fun _ => iff_of_eq (and_true _)

@[simp]
theorem mem_univ_hom (x : ZFSet.{u}) : univ.{u} x :=
  trivial

theorem eq_univ_iff_forall {A : Class.{u}} : A = univ ↔ ∀ x : ZFSet, A x :=
  Set.eq_univ_iff_forall

theorem eq_univ_of_forall {A : Class.{u}} : (∀ x : ZFSet, A x) → A = univ :=
  Set.eq_univ_of_forall

theorem mem_wf : @WellFounded Class.{u} (· ∈ ·) :=
  ⟨by
    have H : ∀ x : ZFSet.{u}, @Acc Class.{u} (· ∈ ·) ↑x := by
      refine fun a => ZFSet.inductionOn a fun x IH => ⟨_, ?_⟩
      rintro A ⟨z, rfl, hz⟩
      exact IH z hz
    refine fun A => ⟨A, ?_⟩
    rintro B ⟨x, rfl, _⟩
    exact H x⟩

instance : IsWellFounded Class (· ∈ ·) :=
  ⟨mem_wf⟩

instance : WellFoundedRelation Class :=
  ⟨_, mem_wf⟩

theorem mem_asymm {x y : Class} : x ∈ y → y ∉ x :=
  asymm_of (· ∈ ·)

theorem mem_irrefl (x : Class) : x ∉ x :=
  irrefl_of (· ∈ ·) x

/-- **There is no universal set.**
This is stated as `univ ∉ univ`, meaning that `univ` (the class of all sets) is proper (does not
belong to the class of all sets). -/
theorem univ_not_mem_univ : univ ∉ univ :=
  mem_irrefl _

/-- Convert a conglomerate (a collection of classes) into a class -/
def congToClass (x : Set Class.{u}) : Class.{u} :=
  { y | ↑y ∈ x }

@[simp]
theorem congToClass_empty : congToClass ∅ = ∅ := by
  ext z
  simp only [congToClass, not_empty_hom, iff_false]
  exact Set.not_mem_empty z

/-- Convert a class into a conglomerate (a collection of classes) -/
def classToCong (x : Class.{u}) : Set Class.{u} :=
  { y | y ∈ x }

@[simp]
theorem classToCong_empty : classToCong ∅ = ∅ := by
  ext
  simp [classToCong]

/-- The power class of a class is the class of all subclasses that are ZFC sets -/
def powerset (x : Class) : Class :=
  congToClass (Set.powerset x)

/-- The union of a class is the class of all members of ZFC sets in the class -/
def sUnion (x : Class) : Class :=
  ⋃₀ classToCong x

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
    rw [h]

@[simp]
theorem toSet_of_ZFSet (A : Class.{u}) (x : ZFSet.{u}) : ToSet A x ↔ A x :=
  ⟨fun ⟨y, yx, py⟩ => by rwa [ofSet.inj yx] at py, fun px => ⟨x, rfl, px⟩⟩

@[simp, norm_cast]
theorem coe_mem {x : ZFSet.{u}} {A : Class.{u}} : ↑x ∈ A ↔ A x :=
  toSet_of_ZFSet _ _

@[simp]
theorem coe_apply {x y : ZFSet.{u}} : (y : Class.{u}) x ↔ x ∈ y :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_subset (x y : ZFSet.{u}) : (x : Class.{u}) ⊆ y ↔ x ⊆ y :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_sep (p : Class.{u}) (x : ZFSet.{u}) :
    (ZFSet.sep p x : Class) = { y ∈ x | p y } :=
  ext fun _ => ZFSet.mem_sep

@[simp, norm_cast]
theorem coe_empty : ↑(∅ : ZFSet.{u}) = (∅ : Class.{u}) :=
  ext fun y => iff_false _ ▸ ZFSet.not_mem_empty y

@[simp, norm_cast]
theorem coe_insert (x y : ZFSet.{u}) : ↑(insert x y) = @insert ZFSet.{u} Class.{u} _ x y :=
  ext fun _ => ZFSet.mem_insert_iff

@[simp, norm_cast]
theorem coe_union (x y : ZFSet.{u}) : ↑(x ∪ y) = (x : Class.{u}) ∪ y :=
  ext fun _ => ZFSet.mem_union

@[simp, norm_cast]
theorem coe_inter (x y : ZFSet.{u}) : ↑(x ∩ y) = (x : Class.{u}) ∩ y :=
  ext fun _ => ZFSet.mem_inter

@[simp, norm_cast]
theorem coe_diff (x y : ZFSet.{u}) : ↑(x \ y) = (x : Class.{u}) \ y :=
  ext fun _ => ZFSet.mem_diff

@[simp, norm_cast]
theorem coe_powerset (x : ZFSet.{u}) : ↑x.powerset = powerset.{u} x :=
  ext fun _ => ZFSet.mem_powerset

@[simp]
theorem powerset_apply {A : Class.{u}} {x : ZFSet.{u}} : powerset A x ↔ ↑x ⊆ A :=
  Iff.rfl

@[simp]
theorem sUnion_apply {x : Class} {y : ZFSet} : (⋃₀ x) y ↔ ∃ z : ZFSet, x z ∧ y ∈ z := by
  constructor
  · rintro ⟨-, ⟨z, rfl, hxz⟩, hyz⟩
    exact ⟨z, hxz, hyz⟩
  · exact fun ⟨z, hxz, hyz⟩ => ⟨_, coe_mem.2 hxz, hyz⟩

@[simp, norm_cast]
theorem coe_sUnion (x : ZFSet.{u}) : ↑(⋃₀ x : ZFSet) = ⋃₀ (x : Class.{u}) :=
  ext fun y =>
    ZFSet.mem_sUnion.trans (sUnion_apply.trans <| by rfl).symm

@[simp]
theorem mem_sUnion {x y : Class.{u}} : y ∈ ⋃₀ x ↔ ∃ z, z ∈ x ∧ y ∈ z := by
  constructor
  · rintro ⟨w, rfl, z, hzx, hwz⟩
    exact ⟨z, hzx, coe_mem.2 hwz⟩
  · rintro ⟨w, hwx, z, rfl, hwz⟩
    exact ⟨z, rfl, w, hwx, hwz⟩

theorem sInter_apply {x : Class.{u}} {y : ZFSet.{u}} : (⋂₀ x) y ↔ ∀ z : ZFSet.{u}, x z → y ∈ z := by
  refine ⟨fun hxy z hxz => hxy _ ⟨z, rfl, hxz⟩, ?_⟩
  rintro H - ⟨z, rfl, hxz⟩
  exact H _ hxz

@[simp, norm_cast]
theorem coe_sInter {x : ZFSet.{u}} (h : x.Nonempty) : ↑(⋂₀ x : ZFSet) = ⋂₀ (x : Class.{u}) :=
  Set.ext fun _ => (ZFSet.mem_sInter h).trans sInter_apply.symm

theorem mem_of_mem_sInter {x y z : Class} (hy : y ∈ ⋂₀ x) (hz : z ∈ x) : y ∈ z := by
  obtain ⟨w, rfl, hw⟩ := hy
  exact coe_mem.2 (hw z hz)

theorem mem_sInter {x y : Class.{u}} (h : x.Nonempty) : y ∈ ⋂₀ x ↔ ∀ z, z ∈ x → y ∈ z := by
  refine ⟨fun hy z => mem_of_mem_sInter hy, fun H => ?_⟩
  simp_rw [mem_def, sInter_apply]
  obtain ⟨z, hz⟩ := h
  obtain ⟨y, rfl, _⟩ := H z (coe_mem.2 hz)
  refine ⟨y, rfl, fun w hxw => ?_⟩
  simpa only [coe_mem, coe_apply] using H w (coe_mem.2 hxw)

@[simp]
theorem sUnion_empty : ⋃₀ (∅ : Class.{u}) = (∅ : Class.{u}) := by
  ext
  simp

@[simp]
theorem sInter_empty : ⋂₀ (∅ : Class.{u}) = univ := by
  rw [sInter, classToCong_empty, Set.sInter_empty, univ]

/-- An induction principle for sets. If every subset of a class is a member, then the class is
  universal. -/
theorem eq_univ_of_powerset_subset {A : Class} (hA : powerset A ⊆ A) : A = univ :=
  eq_univ_of_forall
    (by
      by_contra! hnA
      exact
        WellFounded.min_mem ZFSet.mem_wf _ hnA
          (hA fun x hx =>
            Classical.not_not.1 fun hB =>
              WellFounded.not_lt_min ZFSet.mem_wf _ hnA hB <| coe_apply.1 hx))

/-- The definite description operator, which is `{x}` if `{y | A y} = {x}` and `∅` otherwise. -/
def iota (A : Class) : Class :=
  ⋃₀ { x | ∀ y, A y ↔ y = x }

theorem iota_val (A : Class) (x : ZFSet) (H : ∀ y, A y ↔ y = x) : iota A = ↑x :=
  ext fun y =>
    ⟨fun ⟨_, ⟨x', rfl, h⟩, yx'⟩ => by rwa [← (H x').1 <| (h x').2 rfl], fun yx =>
      ⟨_, ⟨x, rfl, H⟩, yx⟩⟩

/-- Unlike the other set constructors, the `iota` definite descriptor
  is a set for any set input, but not constructively so, so there is no
  associated `Class → Set` function. -/
theorem iota_ex (A) : iota.{u} A ∈ univ.{u} :=
  mem_univ.2 <|
    Or.elim (Classical.em <| ∃ x, ∀ y, A y ↔ y = x) (fun ⟨x, h⟩ => ⟨x, Eq.symm <| iota_val A x h⟩)
      fun hn =>
      ⟨∅, ext fun _ => coe_empty.symm ▸ ⟨False.rec, fun ⟨_, ⟨x, rfl, H⟩, _⟩ => hn ⟨x, H⟩⟩⟩

/-- Function value -/
def fval (F A : Class.{u}) : Class.{u} :=
  iota fun y => ToSet (fun x => F (ZFSet.pair x y)) A

@[inherit_doc]
infixl:100 " ′ " => fval

theorem fval_ex (F A : Class.{u}) : F ′ A ∈ univ.{u} :=
  iota_ex _

end Class

namespace ZFSet

@[simp]
theorem map_fval {f : ZFSet.{u} → ZFSet.{u}} [Definable₁ f] {x y : ZFSet.{u}}
    (h : y ∈ x) : (ZFSet.map f x ′ y : Class.{u}) = f y :=
  Class.iota_val _ _ fun z => by
    rw [Class.toSet_of_ZFSet, Class.coe_apply, mem_map]
    exact
      ⟨fun ⟨w, _, pr⟩ => by
        let ⟨wy, fw⟩ := ZFSet.pair_injective pr
        rw [← fw, wy], fun e => by
        subst e
        exact ⟨_, h, rfl⟩⟩

variable (x : ZFSet.{u})

/-- A choice function on the class of nonempty ZFC sets. -/
noncomputable def choice : ZFSet :=
  @map (fun y => Classical.epsilon fun z => z ∈ y) (Classical.allZFSetDefinable _) x

theorem choice_mem_aux (h : ∅ ∉ x) (y : ZFSet.{u}) (yx : y ∈ x) :
    (Classical.epsilon fun z : ZFSet.{u} => z ∈ y) ∈ y :=
  (@Classical.epsilon_spec _ fun z : ZFSet.{u} => z ∈ y) <|
    by_contradiction fun n => h <| by rwa [← (eq_empty y).2 fun z zx => n ⟨z, zx⟩]

theorem choice_isFunc (h : ∅ ∉ x) : IsFunc x (⋃₀ x) (choice x) :=
  (@map_isFunc _ (Classical.allZFSetDefinable _) _ _).2 fun y yx =>
    mem_sUnion.2 ⟨y, yx, choice_mem_aux x h y yx⟩

theorem choice_mem (h : ∅ ∉ x) (y : ZFSet.{u}) (yx : y ∈ x) :
    (choice x ′ y : Class.{u}) ∈ (y : Class.{u}) := by
  delta choice
  rw [@map_fval _ (Classical.allZFSetDefinable _) x y yx, Class.coe_mem, Class.coe_apply]
  exact choice_mem_aux x h y yx

private lemma toSet_equiv_aux {s : Set ZFSet.{u}} (hs : Small.{u} s) :
  (mk <| PSet.mk (Shrink s) fun x ↦ ((equivShrink s).symm x).1.out).toSet = s := by
    ext x
    rw [mem_toSet, ← mk_out x, mk_mem_iff, mk_out]
    refine ⟨?_, fun xs ↦ ⟨equivShrink s (Subtype.mk x xs), ?_⟩⟩
    · rintro ⟨b, h2⟩
      rw [← ZFSet.eq, ZFSet.mk_out] at h2
      simp [h2]
    · simp [PSet.Equiv.refl]

/-- `ZFSet.toSet` as an equivalence. -/
@[simps apply_coe]
noncomputable def toSet_equiv : ZFSet.{u} ≃ {s : Set ZFSet.{u} // Small.{u, u+1} s} where
  toFun x := ⟨x.toSet, x.small_toSet⟩
  invFun := fun ⟨s, _⟩ ↦ mk <| PSet.mk (Shrink s) fun x ↦ ((equivShrink.{u, u+1} s).symm x).1.out
  left_inv := Function.rightInverse_of_injective_of_leftInverse (by intros x y; simp)
    fun s ↦ Subtype.coe_injective <| toSet_equiv_aux s.2
  right_inv s := Subtype.coe_injective <| toSet_equiv_aux s.2

end ZFSet

set_option linter.style.longFile 1700
