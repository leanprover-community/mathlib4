/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
import Mathlib.Control.Functor.Multivariate
import Mathlib.Data.PFunctor.Univariate.Basic

/-!
# Multivariate polynomial functors.

Multivariate polynomial functors are used for defining M-types and W-types.
They map a type vector `α` to the type `Σ a : A, B a ⟹ α`, with `A : Type` and
`B : A → TypeVec n`. They interact well with Lean's inductive definitions because
they guarantee that occurrences of `α` are positive.
-/


universe u v

open MvFunctor

/-- multivariate polynomial functors
-/
@[pp_with_univ]
structure MvPFunctor (n : ℕ) where
  /-- The head type -/
  A : Type u
  /-- The child family of types -/
  B : A → TypeVec.{u} n

namespace MvPFunctor

open MvFunctor (LiftP LiftR)

variable {n m : ℕ} (P : MvPFunctor.{u} n)

/-- Applying `P` to an object of `Type` -/
@[coe]
def Obj (α : TypeVec.{u} n) : Type u :=
  Σ a : P.A, P.B a ⟹ α

instance : CoeFun (MvPFunctor.{u} n) (fun _ => TypeVec.{u} n → Type u) where
  coe := Obj

/-- Applying `P` to a morphism of `Type` -/
def map {α β : TypeVec n} (f : α ⟹ β) : P α → P β := fun ⟨a, g⟩ => ⟨a, TypeVec.comp f g⟩

instance : Inhabited (MvPFunctor n) :=
  ⟨⟨default, default⟩⟩

instance Obj.inhabited {α : TypeVec n} [Inhabited P.A] [∀ i, Inhabited (α i)] :
    Inhabited (P α) :=
  ⟨⟨default, fun _ _ => default⟩⟩

instance : MvFunctor.{u} P.Obj :=
  ⟨@MvPFunctor.map n P⟩

theorem map_eq {α β : TypeVec n} (g : α ⟹ β) (a : P.A) (f : P.B a ⟹ α) :
    @MvFunctor.map _ P.Obj _ _ _ g ⟨a, f⟩ = ⟨a, g ⊚ f⟩ :=
  rfl

theorem id_map {α : TypeVec n} : ∀ x : P α, TypeVec.id <$$> x = x
  | ⟨_, _⟩ => rfl

theorem comp_map {α β γ : TypeVec n} (f : α ⟹ β) (g : β ⟹ γ) :
    ∀ x : P α, (g ⊚ f) <$$> x = g <$$> f <$$> x
  | ⟨_, _⟩ => rfl

instance : LawfulMvFunctor.{u} P.Obj where
  id_map := @id_map _ P
  comp_map := @comp_map _ P

/-- Constant functor where the input object does not affect the output -/
def const (n : ℕ) (A : Type u) : MvPFunctor n :=
  { A
    B := fun _ _ => PEmpty }

section Const

variable (n) {A : Type u} {α β : TypeVec.{u} n}

/-- Constructor for the constant functor -/
def const.mk (x : A) {α} : const n A α :=
  ⟨x, fun _ a => PEmpty.elim a⟩

variable {n}

/-- Destructor for the constant functor -/
def const.get (x : const n A α) : A :=
  x.1

@[simp]
theorem const.get_map (f : α ⟹ β) (x : const n A α) : const.get (f <$$> x) = const.get x := by
  cases x
  rfl

@[simp]
theorem const.get_mk (x : A) : const.get (const.mk n x : const n A α) = x := rfl

@[simp]
theorem const.mk_get (x : const n A α) : const.mk n (const.get x) = x := by
  cases x
  dsimp [const.get, const.mk]
  congr with (_⟨⟩)

end Const

/-- Functor composition on polynomial functors -/
def comp (P : MvPFunctor.{u} n) (Q : Fin2 n → MvPFunctor.{u} m) : MvPFunctor m where
  A := Σ a₂ : P.1, ∀ i, P.2 a₂ i → (Q i).1
  B a i := Σ (j : _) (b : P.2 a.1 j), (Q j).2 (a.snd j b) i

variable {P} {Q : Fin2 n → MvPFunctor.{u} m} {α β : TypeVec.{u} m}

/-- Constructor for functor composition -/
def comp.mk (x : P (fun i => Q i α)) : comp P Q α :=
  ⟨⟨x.1, fun _ a => (x.2 _ a).1⟩, fun i a => (x.snd a.fst a.snd.fst).snd i a.snd.snd⟩

/-- Destructor for functor composition -/
def comp.get (x : comp P Q α) : P (fun i => Q i α) :=
  ⟨x.1.1, fun i a => ⟨x.fst.snd i a, fun (j : Fin2 m) (b : (Q i).B _ j) => x.snd j ⟨i, ⟨a, b⟩⟩⟩⟩

theorem comp.get_map (f : α ⟹ β) (x : comp P Q α) :
    comp.get (f <$$> x) = (fun i (x : Q i α) => f <$$> x) <$$> comp.get x := by
  rfl

@[simp]
theorem comp.get_mk (x : P (fun i => Q i α)) : comp.get (comp.mk x) = x := by
  rfl

@[simp]
theorem comp.mk_get (x : comp P Q α) : comp.mk (comp.get x) = x := by
  rfl

/-
lifting predicates and relations
-/
theorem liftP_iff {α : TypeVec n} (p : ∀ ⦃i⦄, α i → Prop) (x : P α) :
    LiftP p x ↔ ∃ a f, x = ⟨a, f⟩ ∧ ∀ i j, p (f i j) := by
  constructor
  · rintro ⟨y, hy⟩
    rcases h : y with ⟨a, f⟩
    refine ⟨a, fun i j => (f i j).val, ?_, fun i j => (f i j).property⟩
    rw [← hy, h, map_eq]
    rfl
  rintro ⟨a, f, xeq, pf⟩
  use ⟨a, fun i j => ⟨f i j, pf i j⟩⟩
  rw [xeq]; rfl

theorem liftP_iff' {α : TypeVec n} (p : ∀ ⦃i⦄, α i → Prop) (a : P.A) (f : P.B a ⟹ α) :
    @LiftP.{u} _ P.Obj _ α p ⟨a, f⟩ ↔ ∀ i x, p (f i x) := by
  simp only [liftP_iff]; constructor
  · rintro ⟨_, _, ⟨⟩, _⟩
    assumption
  · intro
    repeat' first |constructor|assumption

theorem liftR_iff {α : TypeVec n} (r : ∀ ⦃i⦄, α i → α i → Prop) (x y : P α) :
    LiftR @r x y ↔ ∃ a f₀ f₁, x = ⟨a, f₀⟩ ∧ y = ⟨a, f₁⟩ ∧ ∀ i j, r (f₀ i j) (f₁ i j) := by
  constructor
  · rintro ⟨u, xeq, yeq⟩
    rcases h : u with ⟨a, f⟩
    use a, fun i j => (f i j).val.fst, fun i j => (f i j).val.snd
    constructor
    · rw [← xeq, h]
      rfl
    constructor
    · rw [← yeq, h]
      rfl
    intro i j
    exact (f i j).property
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  use ⟨a, fun i j => ⟨(f₀ i j, f₁ i j), h i j⟩⟩
  dsimp; constructor
  · rw [xeq]
    rfl
  rw [yeq]; rfl

open Set

theorem supp_eq {α : TypeVec n} (a : P.A) (f : P.B a ⟹ α) (i) :
    @supp.{u} _ P.Obj _ α (⟨a, f⟩ : P α) i = f i '' univ := by
  ext x; simp only [supp, image_univ, mem_range, mem_setOf_eq]
  constructor <;> intro h
  · apply @h fun i x => ∃ y : P.B a i, f i y = x
    rw [liftP_iff']
    intros
    exact ⟨_, rfl⟩
  · simp only [liftP_iff']
    cases h
    subst x
    tauto

end MvPFunctor

/-
Decomposing an n+1-ary pfunctor.
-/
namespace MvPFunctor

open TypeVec

variable {n : ℕ} (P : MvPFunctor.{u} (n + 1))

/-- Split polynomial functor, get an n-ary functor
from an `n+1`-ary functor -/
def drop : MvPFunctor n where
  A := P.A
  B a := (P.B a).drop

/-- Split polynomial functor, get a univariate functor
from an `n+1`-ary functor -/
def last : PFunctor where
  A := P.A
  B a := (P.B a).last

/-- append arrows of a polynomial functor application -/
abbrev appendContents {α : TypeVec n} {β : Type*} {a : P.A} (f' : P.drop.B a ⟹ α)
    (f : P.last.B a → β) : P.B a ⟹ (α ::: β) :=
  splitFun f' f

end MvPFunctor
