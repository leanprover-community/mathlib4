/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.SetLike.Basic
import Mathlib.Logic.Small.Basic
import Mathlib.SetTheory.ZFC.PSet

/-!
# A model of ZFC

In this file, we model Zermelo-Fraenkel set theory (+ choice) using Lean's underlying type theory,
building on the pre-sets defined in `Mathlib/SetTheory/ZFC/PSet.lean`.

The theory of classes is developed in `Mathlib/SetTheory/ZFC/Class.lean`.

## Main definitions

* `ZFSet`: ZFC set. Defined as `PSet` quotiented by `PSet.Equiv`, the extensional equivalence.
* `ZFSet.choice`: Axiom of choice. Proved from Lean's axiom of choice.
* `ZFSet.omega`: The von Neumann ordinal `ω` as a `Set`.
* `Classical.allZFSetDefinable`: All functions are classically definable.
* `ZFSet.IsFunc` : Predicate that a ZFC set is a subset of `x × y` that can be considered as a ZFC
  function `x → y`. That is, each member of `x` is related by the ZFC set to exactly one member of
  `y`.
* `ZFSet.funs`: ZFC set of ZFC functions `x → y`.
* `ZFSet.Hereditarily p x`: Predicate that every set in the transitive closure of `x` has property
  `p`.

## Notes

To avoid confusion between the Lean `Set` and the ZFC `Set`, docstrings in this file refer to them
respectively as "`Set`" and "ZFC set".
-/


universe u

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

namespace Classical

open PSet ZFSet

/-- All functions are classically definable. -/
noncomputable def allZFSetDefinable {n} (F : (Fin n → ZFSet.{u}) → ZFSet.{u}) : Definable n F where
  out xs := (F (mk <| xs ·)).out

end Classical

namespace ZFSet

open PSet

theorem eq {x y : PSet} : mk x = mk y ↔ Equiv x y :=
  Quotient.eq

theorem sound {x y : PSet} (h : PSet.Equiv x y) : mk x = mk y :=
  Quotient.sound h

theorem exact {x y : PSet} : mk x = mk y → PSet.Equiv x y :=
  Quotient.exact

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

instance : SetLike ZFSet ZFSet where
  coe := toSet
  coe_injective' := toSet_injective

instance : HasSSubset ZFSet := ⟨(· < ·)⟩

@[simp]
theorem le_def (x y : ZFSet) : x ≤ y ↔ x ⊆ y :=
  Iff.rfl

@[simp]
theorem lt_def (x y : ZFSet) : x < y ↔ x ⊂ y :=
  Iff.rfl

instance : IsAntisymm ZFSet (· ⊆ ·) :=
  ⟨@le_antisymm ZFSet _⟩

instance : IsNonstrictStrictOrder ZFSet (· ⊆ ·) (· ⊂ ·) :=
  ⟨fun _ _ ↦ Iff.rfl⟩

/-- The empty ZFC set -/
protected def empty : ZFSet :=
  mk ∅

instance : EmptyCollection ZFSet :=
  ⟨ZFSet.empty⟩

instance : Inhabited ZFSet :=
  ⟨∅⟩

@[simp]
theorem notMem_empty (x) : x ∉ (∅ : ZFSet.{u}) :=
  Quotient.inductionOn x PSet.notMem_empty

@[deprecated (since := "2025-05-23")] alias not_mem_empty := notMem_empty

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
  (eq_empty _).mpr fun _ h ↦ notMem_empty _ (mem_sep.mp h).1

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
    induction ea : A a with | _ γ Γ
    induction eb : B b with | _ δ Δ
    rw [ea, eb] at hb
    obtain ⟨γδ, δγ⟩ := hb
    let c : (A a).Type := c
    let ⟨d, hd⟩ := γδ (by rwa [ea] at c)
    use ⟨b, Eq.ndrec d (Eq.symm eb)⟩
    change PSet.Equiv ((A a).Func c) ((B b).Func (Eq.ndrec d eb.symm))
    match A a, B b, ea, eb, c, d, hd with
    | _, _, rfl, rfl, _, _, hd => exact hd

/-- The union operator, the collection of elements of elements of a ZFC set. Uses `⋃₀` notation,
scoped under the `ZFSet` namespace.
-/
def sUnion : ZFSet → ZFSet :=
  Quotient.map PSet.sUnion
    fun ⟨_, A⟩ ⟨_, B⟩ ⟨αβ, βα⟩ =>
      ⟨sUnion_lem A B αβ, fun a =>
        Exists.elim
          (sUnion_lem B A (fun b => Exists.elim (βα b) fun c hc => ⟨c, PSet.Equiv.symm hc⟩) a)
          fun b hb => ⟨b, PSet.Equiv.symm hb⟩⟩

@[inherit_doc]
scoped prefix:110 "⋃₀ " => ZFSet.sUnion

/-- The intersection operator, the collection of elements in all of the elements of a ZFC set. We
define `⋂₀ ∅ = ∅`. Uses `⋂₀` notation, scoped under the `ZFSet` namespace. -/
def sInter (x : ZFSet) : ZFSet := (⋃₀ x).sep (fun y => ∀ z ∈ x, y ∈ z)

@[inherit_doc]
scoped prefix:110 "⋂₀ " => ZFSet.sInter

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
  · exact (notMem_empty z hz).elim
  · exact (mem_sInter hx).1 hy z hz

theorem mem_sUnion_of_mem {x y z : ZFSet} (hy : y ∈ z) (hz : z ∈ x) : y ∈ ⋃₀ x :=
  mem_sUnion.2 ⟨z, hz, hy⟩

theorem notMem_sInter_of_notMem {x y z : ZFSet} (hy : y ∉ z) (hz : z ∈ x) : y ∉ ⋂₀ x :=
  fun hx => hy <| mem_of_mem_sInter hx hz

@[deprecated (since := "2025-05-23")] alias not_mem_sInter_of_not_mem := notMem_sInter_of_notMem

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

theorem notMem_of_subset {x y : ZFSet} (h : x ⊆ y) : y ∉ x :=
  imp_not_comm.2 not_subset_of_mem h

@[deprecated (since := "2025-05-23")] alias not_mem_of_subset := notMem_of_subset

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

section

variable {α : Type*} [Small.{u} α]

/-- The range of a type-indexed family of sets. -/
noncomputable def range (f : α → ZFSet.{u}) : ZFSet.{u} :=
  ⟦⟨_, Quotient.out ∘ f ∘ (equivShrink α).symm⟩⟧

@[simp]
theorem mem_range {f : α → ZFSet.{u}} {x : ZFSet.{u}} : x ∈ range f ↔ x ∈ Set.range f :=
  Quotient.inductionOn x fun y => by
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨(equivShrink α).symm z, Quotient.eq_mk_iff_out.2 hz.symm⟩
    · rintro ⟨z, hz⟩
      use equivShrink α z
      simpa [hz] using PSet.Equiv.symm (Quotient.mk_out y)

@[simp]
theorem toSet_range (f : α → ZFSet.{u}) : (range f).toSet = Set.range f := by
  ext
  simp

theorem mem_range_self {f : α → ZFSet.{u}} (a : α) : f a ∈ range f := by simp

/-- Indexed union of a family of ZFC sets. Uses `⋃` notation, scoped under the `ZFSet` namespace. -/
noncomputable def iUnion (f : α → ZFSet.{u}) : ZFSet.{u} :=
  sUnion (range f)

@[inherit_doc iUnion] scoped notation3 "⋃ " (...)", " r:60:(scoped f => iUnion f) => r

@[simp]
theorem mem_iUnion {f : α → ZFSet.{u}} {x : ZFSet.{u}} : x ∈ ⋃ i, f i ↔ ∃ i, x ∈ f i := by
  simp [iUnion]

@[simp]
theorem toSet_iUnion (f : α → ZFSet.{u}) : (⋃ i, f i).toSet = ⋃ i, (f i).toSet := by
  ext
  simp

theorem subset_iUnion (f : α → ZFSet.{u}) (i : α) : f i ⊆ ⋃ i, f i := by
  intro x hx
  simpa using ⟨i, hx⟩

end

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
  grind [mem_pair, mem_powerset, mem_singleton, mem_union, pair, subset_def]

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

/-- The Cartesian product, `{(a, b) | a ∈ x, b ∈ y}` -/
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
