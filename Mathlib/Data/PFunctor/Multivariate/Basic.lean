/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
import Mathlib.Control.Functor.Multivariate
import Mathlib.Data.PFunctor.Univariate.Basic

#align_import data.pfunctor.multivariate.basic from "leanprover-community/mathlib"@"e3d9ab8faa9dea8f78155c6c27d62a621f4c152d"

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
structure MvPFunctor (n : ℕ) where
  /-- The head type -/
  A : Type u
  /-- The child family of types -/
  B : A → TypeVec.{u} n
#align mvpfunctor MvPFunctor

namespace MvPFunctor

open MvFunctor (LiftP LiftR)

variable {n m : ℕ} (P : MvPFunctor.{u} n)

/-- Applying `P` to an object of `Type` -/
def Obj (α : TypeVec.{u} n) : Type u :=
  Σa : P.A, P.B a ⟹ α
#align mvpfunctor.obj MvPFunctor.Obj

/-- Applying `P` to a morphism of `Type` -/
def map {α β : TypeVec n} (f : α ⟹ β) : P.Obj α → P.Obj β := fun ⟨a, g⟩ => ⟨a, TypeVec.comp f g⟩
#align mvpfunctor.map MvPFunctor.map

instance : Inhabited (MvPFunctor n) :=
  ⟨⟨default, default⟩⟩

instance Obj.inhabited {α : TypeVec n} [Inhabited P.A] [∀ i, Inhabited (α i)] :
    Inhabited (P.Obj α) :=
  ⟨⟨default, fun _ _ => default⟩⟩
#align mvpfunctor.obj.inhabited MvPFunctor.Obj.inhabited

instance : MvFunctor P.Obj :=
  ⟨@MvPFunctor.map n P⟩

theorem map_eq {α β : TypeVec n} (g : α ⟹ β) (a : P.A) (f : P.B a ⟹ α) :
    @MvFunctor.map _ P.Obj _ _ _ g ⟨a, f⟩ = ⟨a, g ⊚ f⟩ :=
  rfl
#align mvpfunctor.map_eq MvPFunctor.map_eq

theorem id_map {α : TypeVec n} : ∀ x : P.Obj α, TypeVec.id <$$> x = x
  | ⟨_, _⟩ => rfl
#align mvpfunctor.id_map MvPFunctor.id_map

theorem comp_map {α β γ : TypeVec n} (f : α ⟹ β) (g : β ⟹ γ) :
    ∀ x : P.Obj α, (g ⊚ f) <$$> x = g <$$> f <$$> x
  | ⟨_, _⟩ => rfl
#align mvpfunctor.comp_map MvPFunctor.comp_map

instance : LawfulMvFunctor P.Obj where
  id_map := @id_map _ P
  comp_map := @comp_map _ P

/-- Constant functor where the input object does not affect the output -/
def const (n : ℕ) (A : Type u) : MvPFunctor n :=
  { A
    B := fun _ _ => PEmpty }
#align mvpfunctor.const MvPFunctor.const

section Const

variable (n) {A : Type u} {α β : TypeVec.{u} n}

/-- Constructor for the constant functor -/
def const.mk (x : A) {α} : (const n A).Obj α :=
  ⟨x, fun _ a => PEmpty.elim a⟩
#align mvpfunctor.const.mk MvPFunctor.const.mk

variable {n}

/-- Destructor for the constant functor -/
def const.get (x : (const n A).Obj α) : A :=
  x.1
#align mvpfunctor.const.get MvPFunctor.const.get

@[simp]
theorem const.get_map (f : α ⟹ β) (x : (const n A).Obj α) : const.get (f <$$> x) = const.get x := by
  cases x
  -- ⊢ get (f <$$> { fst := fst✝, snd := snd✝ }) = get { fst := fst✝, snd := snd✝ }
  rfl
  -- 🎉 no goals
#align mvpfunctor.const.get_map MvPFunctor.const.get_map

@[simp]
theorem const.get_mk (x : A) : const.get (const.mk n x : (const n A).Obj α) = x := by rfl
                                                                                      -- 🎉 no goals
#align mvpfunctor.const.get_mk MvPFunctor.const.get_mk

@[simp]
theorem const.mk_get (x : (const n A).Obj α) : const.mk n (const.get x) = x := by
  cases x
  -- ⊢ mk n (get { fst := fst✝, snd := snd✝ }) = { fst := fst✝, snd := snd✝ }
  dsimp [const.get, const.mk]
  -- ⊢ { fst := fst✝, snd := fun x a => PEmpty.elim a } = { fst := fst✝, snd := snd …
  congr with (_⟨⟩)
  -- 🎉 no goals
#align mvpfunctor.const.mk_get MvPFunctor.const.mk_get

end Const

/-- Functor composition on polynomial functors -/
def comp (P : MvPFunctor.{u} n) (Q : Fin2 n → MvPFunctor.{u} m) : MvPFunctor m
    where
  A := Σa₂ : P.1, ∀ i, P.2 a₂ i → (Q i).1
  B a i := Σ(j : _) (b : P.2 a.1 j), (Q j).2 (a.snd j b) i
#align mvpfunctor.comp MvPFunctor.comp

variable {P} {Q : Fin2 n → MvPFunctor.{u} m} {α β : TypeVec.{u} m}

/-- Constructor for functor composition -/
def comp.mk (x : P.Obj fun i => (Q i).Obj α) : (comp P Q).Obj α :=
  ⟨⟨x.1, fun _ a => (x.2 _ a).1⟩, fun i a => (x.snd a.fst a.snd.fst).snd i a.snd.snd⟩
#align mvpfunctor.comp.mk MvPFunctor.comp.mk

/-- Destructor for functor composition -/
def comp.get (x : (comp P Q).Obj α) : P.Obj fun i => (Q i).Obj α :=
  ⟨x.1.1, fun i a => ⟨x.fst.snd i a, fun (j : Fin2 m) (b : (Q i).B _ j) => x.snd j ⟨i, ⟨a, b⟩⟩⟩⟩
#align mvpfunctor.comp.get MvPFunctor.comp.get

theorem comp.get_map (f : α ⟹ β) (x : (comp P Q).Obj α) :
    comp.get (f <$$> x) = (fun i (x : (Q i).Obj α) => f <$$> x) <$$> comp.get x := by
  rfl
  -- 🎉 no goals
#align mvpfunctor.comp.get_map MvPFunctor.comp.get_map

@[simp]
theorem comp.get_mk (x : P.Obj fun i => (Q i).Obj α) : comp.get (comp.mk x) = x := by
  rfl
  -- 🎉 no goals
#align mvpfunctor.comp.get_mk MvPFunctor.comp.get_mk

@[simp]
theorem comp.mk_get (x : (comp P Q).Obj α) : comp.mk (comp.get x) = x := by
  rfl
  -- 🎉 no goals
#align mvpfunctor.comp.mk_get MvPFunctor.comp.mk_get

/-
lifting predicates and relations
-/
theorem liftP_iff {α : TypeVec n} (p : ∀ ⦃i⦄, α i → Prop) (x : P.Obj α) :
    LiftP p x ↔ ∃ a f, x = ⟨a, f⟩ ∧ ∀ i j, p (f i j) := by
  constructor
  -- ⊢ LiftP p x → ∃ a f, x = { fst := a, snd := f } ∧ ∀ (i : Fin2 n) (j : B P a i) …
  · rintro ⟨y, hy⟩
    -- ⊢ ∃ a f, x = { fst := a, snd := f } ∧ ∀ (i : Fin2 n) (j : B P a i), p (f i j)
    cases' h : y with a f
    -- ⊢ ∃ a f, x = { fst := a, snd := f } ∧ ∀ (i : Fin2 n) (j : B P a i), p (f i j)
    refine' ⟨a, fun i j => (f i j).val, _, fun i j => (f i j).property⟩
    -- ⊢ x = { fst := a, snd := fun i j => ↑(f i j) }
    rw [← hy, h, map_eq]
    -- ⊢ { fst := a, snd := (fun i => Subtype.val) ⊚ f } = { fst := a, snd := fun i j …
    rfl
    -- 🎉 no goals
  rintro ⟨a, f, xeq, pf⟩
  -- ⊢ LiftP p x
  use ⟨a, fun i j => ⟨f i j, pf i j⟩⟩
  -- ⊢ (fun i => Subtype.val) <$$> { fst := a, snd := fun i j => { val := f i j, pr …
  rw [xeq]; rfl
  -- ⊢ (fun i => Subtype.val) <$$> { fst := a, snd := fun i j => { val := f i j, pr …
            -- 🎉 no goals
#align mvpfunctor.liftp_iff MvPFunctor.liftP_iff

theorem liftP_iff' {α : TypeVec n} (p : ∀ ⦃i⦄, α i → Prop) (a : P.A) (f : P.B a ⟹ α) :
    @LiftP.{u} _ P.Obj _ α p ⟨a, f⟩ ↔ ∀ i x, p (f i x) := by
  simp only [liftP_iff, Sigma.mk.inj_iff]; constructor
  -- ⊢ (∃ a_1 f_1, { fst := a, snd := f } = { fst := a_1, snd := f_1 } ∧ ∀ (i : Fin …
                                           -- ⊢ (∃ a_1 f_1, { fst := a, snd := f } = { fst := a_1, snd := f_1 } ∧ ∀ (i : Fin …
  · rintro ⟨_, _, ⟨⟩, _⟩
    -- ⊢ ∀ (i : Fin2 n) (x : B P a i), p (f i x)
    assumption
    -- 🎉 no goals
  · intro
    -- ⊢ ∃ a_1 f_1, { fst := a, snd := f } = { fst := a_1, snd := f_1 } ∧ ∀ (i : Fin2 …
    repeat' first |constructor|assumption
    -- 🎉 no goals
#align mvpfunctor.liftp_iff' MvPFunctor.liftP_iff'

theorem liftR_iff {α : TypeVec n} (r : ∀ ⦃i⦄, α i → α i → Prop) (x y : P.Obj α) :
    LiftR @r x y ↔ ∃ a f₀ f₁, x = ⟨a, f₀⟩ ∧ y = ⟨a, f₁⟩ ∧ ∀ i j, r (f₀ i j) (f₁ i j) := by
  constructor
  -- ⊢ LiftR r x y → ∃ a f₀ f₁, x = { fst := a, snd := f₀ } ∧ y = { fst := a, snd : …
  · rintro ⟨u, xeq, yeq⟩
    -- ⊢ ∃ a f₀ f₁, x = { fst := a, snd := f₀ } ∧ y = { fst := a, snd := f₁ } ∧ ∀ (i  …
    cases' h : u with a f
    -- ⊢ ∃ a f₀ f₁, x = { fst := a, snd := f₀ } ∧ y = { fst := a, snd := f₁ } ∧ ∀ (i  …
    use a, fun i j => (f i j).val.fst, fun i j => (f i j).val.snd
    -- ⊢ x = { fst := a, snd := fun i j => (↑(f i j)).fst } ∧ y = { fst := a, snd :=  …
    constructor
    -- ⊢ x = { fst := a, snd := fun i j => (↑(f i j)).fst }
    · rw [← xeq, h]
      -- ⊢ (fun i t => (↑t).fst) <$$> { fst := a, snd := f } = { fst := a, snd := fun i …
      rfl
      -- 🎉 no goals
    constructor
    -- ⊢ y = { fst := a, snd := fun i j => (↑(f i j)).snd }
    · rw [← yeq, h]
      -- ⊢ (fun i t => (↑t).snd) <$$> { fst := a, snd := f } = { fst := a, snd := fun i …
      rfl
      -- 🎉 no goals
    intro i j
    -- ⊢ r (↑(f i j)).fst (↑(f i j)).snd
    exact (f i j).property
    -- 🎉 no goals
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  -- ⊢ LiftR r x y
  use ⟨a, fun i j => ⟨(f₀ i j, f₁ i j), h i j⟩⟩
  -- ⊢ (fun i t => (↑t).fst) <$$> { fst := a, snd := fun i j => { val := (f₀ i j, f …
  dsimp; constructor
  -- ⊢ (fun i t => (↑t).fst) <$$> { fst := a, snd := fun i j => { val := (f₀ i j, f …
         -- ⊢ (fun i t => (↑t).fst) <$$> { fst := a, snd := fun i j => { val := (f₀ i j, f …
  · rw [xeq]
    -- ⊢ (fun i t => (↑t).fst) <$$> { fst := a, snd := fun i j => { val := (f₀ i j, f …
    rfl
    -- 🎉 no goals
  rw [yeq]; rfl
  -- ⊢ (fun i t => (↑t).snd) <$$> { fst := a, snd := fun i j => { val := (f₀ i j, f …
            -- 🎉 no goals
#align mvpfunctor.liftr_iff MvPFunctor.liftR_iff

open Set MvFunctor

theorem supp_eq {α : TypeVec n} (a : P.A) (f : P.B a ⟹ α) (i) :
    @supp.{u} _ P.Obj _ α (⟨a, f⟩ : P.Obj α) i = f i '' univ := by
  ext x; simp only [supp, image_univ, mem_range, mem_setOf_eq]
  -- ⊢ x ∈ supp { fst := a, snd := f } i ↔ x ∈ f i '' univ
         -- ⊢ (∀ ⦃P_1 : (i : Fin2 n) → α i → Prop⦄, LiftP P_1 { fst := a, snd := f } → P_1 …
  constructor <;> intro h
  -- ⊢ (∀ ⦃P_1 : (i : Fin2 n) → α i → Prop⦄, LiftP P_1 { fst := a, snd := f } → P_1 …
                  -- ⊢ ∃ y, f i y = x
                  -- ⊢ ∀ ⦃P_1 : (i : Fin2 n) → α i → Prop⦄, LiftP P_1 { fst := a, snd := f } → P_1  …
  · apply @h fun i x => ∃ y : P.B a i, f i y = x
    -- ⊢ LiftP (fun i x => ∃ y, f i y = x) { fst := a, snd := f }
    rw [liftP_iff']
    -- ⊢ ∀ (i : Fin2 n) (x : B P a i), ∃ y, f i y = f i x
    intros
    -- ⊢ ∃ y, f i✝ y = f i✝ x✝
    refine' ⟨_, rfl⟩
    -- 🎉 no goals
  · simp only [liftP_iff']
    -- ⊢ ∀ ⦃P_1 : (i : Fin2 n) → α i → Prop⦄, (∀ (i : Fin2 n) (x : B P a i), P_1 i (f …
    cases h
    -- ⊢ ∀ ⦃P_1 : (i : Fin2 n) → α i → Prop⦄, (∀ (i : Fin2 n) (x : B P a i), P_1 i (f …
    subst x
    -- ⊢ ∀ ⦃P_1 : (i : Fin2 n) → α i → Prop⦄, (∀ (i : Fin2 n) (x : B P a i), P_1 i (f …
    tauto
    -- 🎉 no goals
#align mvpfunctor.supp_eq MvPFunctor.supp_eq

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
#align mvpfunctor.drop MvPFunctor.drop

/-- Split polynomial functor, get a univariate functor
from an `n+1`-ary functor -/
def last : PFunctor where
  A := P.A
  B a := (P.B a).last
#align mvpfunctor.last MvPFunctor.last

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- append arrows of a polynomial functor application -/
@[reducible]
def appendContents {α : TypeVec n} {β : Type*} {a : P.A} (f' : P.drop.B a ⟹ α)
    (f : P.last.B a → β) : P.B a ⟹ (α ::: β) :=
  splitFun f' f
#align mvpfunctor.append_contents MvPFunctor.appendContents

end MvPFunctor
