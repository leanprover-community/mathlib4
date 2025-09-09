/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Set.Lattice

/-!
# Pre-sets

A pre-set is inductively defined by its indexing type and its members, which are themselves
pre-sets.

After defining pre-sets we define extensional equality over them, also inductively. We construct a
`Setoid` instance from it, and in `Mathlib/SetTheory/ZFC/Basic.lean` we define ZFC sets as the
quotient of pre-sets by extensional equality.

## Main definitions

* `PSet`: Pre-set.
* `PSet.Type`: Underlying type of a pre-set.
* `PSet.Func`: Underlying family of pre-sets of a pre-set.
* `PSet.Equiv`: Extensional equivalence of pre-sets. Defined inductively.
* `PSet.omega`: The von Neumann ordinal `ω` as a `PSet`.
-/


universe u v

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

instance : Preorder PSet where
  le := (· ⊆ ·)
  le_refl := refl_of (· ⊆ ·)
  le_trans _ _ _ := trans_of (· ⊆ ·)

instance : HasSSubset PSet := ⟨(· < ·)⟩

@[simp]
theorem le_def (x y : PSet) : x ≤ y ↔ x ⊆ y :=
  Iff.rfl

@[simp]
theorem lt_def (x y : PSet) : x < y ↔ x ⊂ y :=
  Iff.rfl

instance : IsNonstrictStrictOrder PSet (· ⊆ ·) (· ⊂ ·) :=
  ⟨fun _ _ ↦ Iff.rfl⟩

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

theorem notMem_of_subset {x y : PSet} (h : x ⊆ y) : y ∉ x :=
  imp_not_comm.2 not_subset_of_mem h

@[deprecated (since := "2025-05-23")] alias not_mem_of_subset := notMem_of_subset

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
theorem notMem_empty (x : PSet.{u}) : x ∉ (∅ : PSet.{u}) :=
  IsEmpty.exists_iff.1

@[deprecated (since := "2025-05-23")] alias not_mem_empty := notMem_empty

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
    ⟨fun o => Or.rec id (fun n => absurd n (notMem_empty _)) o, Or.inl⟩

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
  ⟨Σ x, (a.Func x).Type, fun ⟨x, y⟩ => (a.Func x).Func y⟩

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

end PSet
