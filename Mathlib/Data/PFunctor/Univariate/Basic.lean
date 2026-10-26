/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Data.W.Basic

/-!
# Polynomial Functors

This file defines polynomial functors and the W-type construction as a polynomial functor.
(For the M-type construction, see `Mathlib/Data/PFunctor/Univariate/M.lean`.)
-/

@[expose] public section

universe u v uA uB uA₁ uB₁ uA₂ uB₂ v₁ v₂ v₃

-- Note: `set_option linter.checkUnivs` should not apply here,
-- we really do want two separate universe levels
set_option linter.checkUnivs false in
/-- A polynomial functor `P` is given by a type `A` and a family `B` of types over `A`. `P` maps
any type `α` to a new type `P α`, which is defined as the sigma type `Σ x, P.B x → α`.

An element of `P α` is a pair `⟨a, f⟩`, where `a` is an element of a type `A` and
`f : B a → α`. Think of `a` as the shape of the object and `f` as an index to the relevant
elements of `α`.
-/
@[pp_with_univ]
structure PFunctor where
  /-- The head type -/
  A : Type uA
  /-- The child family of types -/
  B : A → Type uB

namespace PFunctor

instance : Inhabited PFunctor :=
  ⟨⟨default, default⟩⟩

variable (P : PFunctor.{uA, uB}) {α : Type v₁} {β : Type v₂} {γ : Type v₃}

/-- Applying `P` to an object of `Type` -/
@[coe, implicit_reducible]
def Obj (α : Type v) : Type (max v uA uB) :=
  Σ x : P.A, P.B x → α

instance : CoeFun PFunctor.{uA, uB} (fun _ => Type v → Type (max v uA uB)) where
  coe := Obj

section Obj

variable {P}

/-- Make an element of `P α` from a "shape" `a : P.A` and a family of elements `f : P.B a → α`.

Important: You should use `PFunctor.Obj.mk` instead of the anonymous constructor `⟨_, _⟩`
to avoid abuse of the definitional equality between `P α` and `Σ x : P.A, P.B x → α`. -/
@[implicit_reducible, match_pattern]
def Obj.mk (a : P.A) (f : P.B a → α) : P α := ⟨a, f⟩

/-- To prove a theorem about `t : P α` it suffices to
prove it for `P.Obj.mk a f` for all possible values of `a` and `f`. -/
@[implicit_reducible, elab_as_elim, induction_eliminator, cases_eliminator]
def Obj.rec {motive : P α → Sort*} (mk : ∀ a f, motive (.mk a f)) : ∀ t, motive t :=
  fun t => mk t.1 t.2

@[simp]
theorem Obj.rec_mk {motive : P α → Sort*}
    {mk : ∀ a b, motive (.mk a b)} (a : P.A) (b : P.B a → α) :
    Obj.rec mk (.mk a b) = mk a b := rfl

/-- Extract the "shape" of a `x : P α` as `x.fst : P.A`. -/
@[implicit_reducible] def Obj.fst (x : P α) : P.A := x.1
/-- Extract the underlying value of type `α` associated to an object `x : P α`
at an index `i : P.B x.fst`. -/
@[implicit_reducible] def Obj.snd (x : P α) : P.B x.fst → α := x.2

@[simp] theorem Obj.fst_mk (a : P.A) (f : P.B a → α) : Obj.fst (.mk a f) = a := rfl
@[simp] theorem Obj.snd_mk (a : P.A) (f : P.B a → α) : Obj.snd (.mk a f) = f := rfl

@[simp] theorem Obj.eta (x : P α) : .mk x.fst x.snd = x := rfl

end Obj

/-- Applying `P` to a morphism of `Type` -/
def map (f : α → β) : P α → P β := fun x => .mk x.fst (f ∘ x.snd)

instance Obj.inhabited [Inhabited P.A] [Inhabited α] : Inhabited (P α) :=
  ⟨⟨default, default⟩⟩

instance : Functor P.Obj where map := @map P

/-- We prefer `PFunctor.map` to `Functor.map` because it is universe-polymorphic. -/
@[simp]
theorem map_eq_map {α β : Type v} (f : α → β) (x : P α) : f <$> x = P.map f x :=
  rfl

@[simp]
protected theorem map_eq (f : α → β) (a : P.A) (g : P.B a → α) :
    P.map f (.mk a g) = .mk a (f ∘ g) :=
  rfl

@[simp]
protected theorem id_map (x : P α) : P.map id x = x := rfl

@[simp]
protected theorem map_map (f : α → β) (g : β → γ) (x : P α) :
    P.map g (P.map f x) = P.map (g ∘ f) x := rfl

instance : LawfulFunctor (Obj.{v} P) where
  map_const := rfl
  id_map x := P.id_map x
  comp_map f g x := P.map_map f g x |>.symm

/-- Re-export existing definition of W-types and adapt it to a packaged definition of polynomial
functor. -/
def W : Type (max uA uB) :=
  WType P.B

/- Inhabitants of W types is awkward to encode as an instance assumption because there needs to be a
value `a : P.A` such that `P.B a` is empty to yield a finite tree. -/

variable {P}

/-- The root element of a W tree -/
def W.head : W P → P.A
  | ⟨a, _f⟩ => a

/-- The children of the root of a W tree -/
def W.children : ∀ x : W P, P.B (W.head x) → W P
  | ⟨_a, f⟩ => f

/-- The destructor for W-types -/
def W.dest : W P → P (W P)
  | ⟨a, f⟩ => ⟨a, f⟩

/-- The constructor for W-types -/
def W.mk : P (W P) → W P
  | ⟨a, f⟩ => ⟨a, f⟩

@[simp]
theorem W.dest_mk (p : P (W P)) : W.dest (W.mk p) = p := by cases p; rfl

@[simp]
theorem W.mk_dest (p : W P) : W.mk (W.dest p) = p := by cases p; rfl

variable (P)

/-- `Idx` identifies a location inside the application of a polynomial functor. For `F : PFunctor`,
`x : F α` and `i : F.Idx`, `i` can designate one part of `x` or is invalid, if `i.1 ≠ x.1`. -/
def Idx : Type (max uA uB) :=
  Σ x : P.A, P.B x

instance Idx.inhabited [Inhabited P.A] [Inhabited (P.B default)] : Inhabited P.Idx :=
  ⟨⟨default, default⟩⟩

variable {P}

/-- `x.iget i` takes the component of `x` designated by `i` if any is or returns a default value -/
def Obj.iget [DecidableEq P.A] {α} [Inhabited α] (x : P α) (i : P.Idx) : α :=
  if h : i.1 = x.1 then x.2 (cast (congr_arg _ h) i.2) else default

@[simp]
theorem fst_map (x : P α) (f : α → β) : (P.map f x).1 = x.1 := by cases x; rfl

@[simp]
theorem iget_map [DecidableEq P.A] [Inhabited α] [Inhabited β] (x : P α)
    (f : α → β) (i : P.Idx) (h : i.1 = x.1) : (P.map f x).iget i = f (x.iget i) := by
  simp only [Obj.iget, fst_map, *, dite_eq_left]
  cases x
  rfl

end PFunctor

/-
Composition of polynomial functors.
-/
namespace PFunctor

/-- Composition for polynomial functors -/
@[implicit_reducible]
def comp (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁}) :
    PFunctor.{max uA₁ uA₂ uB₂, max uB₁ uB₂} where
  A := Σ a₂ : P₂.A, P₂.B a₂ → P₁.A
  B a₂a₁ := Σ u : P₂.B a₂a₁.1, P₁.B (a₂a₁.2 u)

/-- Constructor for composition -/
def comp.mk (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁}) {α : Type v} (x : P₂ (P₁ α)) :
    comp P₂ P₁ α :=
  .mk ⟨x.fst, Obj.fst ∘ x.snd⟩ fun a₂a₁ => (x.snd a₂a₁.1).snd a₂a₁.2

/-- Destructor for composition -/
def comp.get (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁}) {α : Type v} (x : comp P₂ P₁ α) :
    P₂ (P₁ α) :=
  .mk x.fst.1 fun a₂ => .mk (x.fst.2 a₂) fun a₁ => x.snd ⟨a₂, a₁⟩

end PFunctor

/-
Lifting predicates and relations.
-/
namespace PFunctor

variable {P : PFunctor.{uA, uB}}

open Functor

theorem liftp_iff {α : Type u} (p : α → Prop) (x : P α) :
    Liftp p x ↔ ∃ a f, x = .mk a f ∧ ∀ i, p (f i) := by
  constructor
  · rintro ⟨y, rfl⟩
    cases y with | mk a f
    refine ⟨a, fun i => (f i).val, rfl, fun i => (f i).property⟩
  · rintro ⟨a, f, rfl, pf⟩
    exact ⟨.mk a fun i => ⟨f i, pf i⟩, rfl⟩

theorem liftp_iff' {α : Type u} (p : α → Prop) (a : P.A) (f : P.B a → α) :
    Liftp p (.mk a f : P α) ↔ ∀ i, p (f i) := by
  simp only [liftp_iff]; constructor <;> intro h
  · rcases h with ⟨a', f', heq, h'⟩
    cases heq
    assumption
  · repeat' first | constructor | assumption

theorem liftr_iff {α : Type u} (r : α → α → Prop) (x y : P α) :
    Liftr r x y ↔ ∃ a f₀ f₁, x = .mk a f₀ ∧ y = .mk a f₁ ∧ ∀ i, r (f₀ i) (f₁ i) := by
  constructor
  · rintro ⟨u, rfl, rfl⟩
    cases u with | mk a f
    exact ⟨a, fun i => (f i).1.1, fun i => (f i).1.2, rfl, rfl, fun i => (f i).2⟩
  · rintro ⟨a, f₀, f₁, rfl, rfl, h⟩
    exact ⟨.mk a fun i => ⟨(f₀ i, f₁ i), h i⟩, rfl, rfl⟩

open Set

theorem supp_eq {α : Type u} (a : P.A) (f : P.B a → α) :
    supp (.mk a f : P α) = f '' univ := by
  ext x; simp only [supp, image_univ, mem_range, mem_ofPred_eq]
  constructor <;> intro h
  · apply @h fun x => ∃ y : P.B a, f y = x
    rw [liftp_iff']
    intro
    exact ⟨_, rfl⟩
  · simp only [liftp_iff']
    cases h
    subst x
    tauto

end PFunctor
