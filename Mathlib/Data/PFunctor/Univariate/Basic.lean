/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Data.W.Basic

/-!
# Polynomial Functors

This file defines polynomial functors and the W-type construction as a polynomial functor.
(For the M-type construction, see `Mathlib/Data/PFunctor/Univariate/M.lean`.)
-/

universe u v uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ v₁ v₂ v₃ vA vB

/-- A polynomial functor `P` is given by a type `A` and a family `B` of types over `A`. `P` maps
any type `α` to a new type `P α`, which is defined as the sigma type `Σ x, P.B x → α`.

An element of `P α` is a pair `⟨a, f⟩`, where `a` is an element of a type `A` and
`f : B a → α`. Think of `a` as the shape of the object and `f` as an index to the relevant
elements of `α`.
-/
-- Note: `nolint checkUnivs` should not apply here, we really do want two separate universe levels
@[ext, pp_with_univ, nolint checkUnivs]
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
@[coe]
def Obj (α : Type v) : Type (max v uA uB) :=
  Σ x : P.A, P.B x → α

instance : CoeFun PFunctor.{uA, uB} (fun _ => Type v → Type (max v uA uB)) where
  coe := Obj

/-- Applying `P` to a morphism of `Type` -/
def map (f : α → β) : P α → P β :=
  fun ⟨a, g⟩ => ⟨a, f ∘ g⟩

instance Obj.inhabited [Inhabited P.A] [Inhabited α] : Inhabited (P α) :=
  ⟨⟨default, default⟩⟩

instance : Functor P.Obj where map := @map P

/-- We prefer `PFunctor.map` to `Functor.map` because it is universe-polymorphic. -/
@[simp]
theorem map_eq_map {α β : Type v} (f : α → β) (x : P α) : f <$> x = P.map f x :=
  rfl

@[simp]
protected theorem map_eq (f : α → β) (a : P.A) (g : P.B a → α) :
    P.map f ⟨a, g⟩ = ⟨a, f ∘ g⟩ :=
  rfl

@[simp]
protected theorem id_map : ∀ x : P α, P.map id x = x := fun ⟨_, _⟩ => rfl

@[simp]
protected theorem map_map (f : α → β) (g : β → γ) :
    ∀ x : P α, P.map g (P.map f x) = P.map (g ∘ f) x := fun ⟨_, _⟩ => rfl

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
  simp only [Obj.iget, fst_map, *, dif_pos]
  cases x
  rfl

end PFunctor

/-
Constructions on polynomial functors.
-/
namespace PFunctor

section Basic

/-- The zero polynomial functor, defined as `A = PEmpty` and `B _ = PEmpty` -/
instance : Zero PFunctor.{uA, uB} where
  zero := ⟨PEmpty, fun _ => PEmpty⟩

/-- The unit polynomial functor, defined as `A = PUnit` and `B _ = PEmpty` -/
instance : One PFunctor.{uA, uB} where
  one := ⟨PUnit, fun _ => PEmpty⟩

/-- The variable `y` polynomial functor, defined as `A = PUnit` and `B _ = PUnit`. -/
def y : PFunctor.{uA, uB} :=
  ⟨PUnit, fun _ => PUnit⟩

instance : IsEmpty (A 0) := inferInstanceAs (IsEmpty PEmpty)

instance : Unique (A 1) := inferInstanceAs (Unique PUnit)

instance : IsEmpty (B 1 PUnit.unit) := inferInstanceAs (IsEmpty PEmpty)

instance : Unique (A y) := inferInstanceAs (Unique PUnit)

instance : Unique (B y PUnit.unit) := inferInstanceAs (Unique PUnit)

@[simp] lemma y_A : y.A = PUnit := rfl

@[simp] lemma y_B (a : y.A) : y.B a = PUnit := rfl

end Basic

section Monomial

/-- The monomial functor `P(y) = A y^ B` for types `A` and `B`. -/
def monomial (A : Type uA) (B : Type uB) : PFunctor.{uA, uB} :=
  ⟨A, fun _ => B⟩

@[inherit_doc] scoped[PFunctor] infixr:80 " y^ " => monomial

/-- The constant polynomial functor `P(y) = A` -/
def C (A : Type uA) : PFunctor.{uA, uB} :=
  A y^ PEmpty

/-- The linear polynomial functor `P(y) = A y` -/
def linear (A : Type uA) : PFunctor.{uA, uB} :=
  A y^ PUnit

/-- The self monomial polynomial functor `P(y) = S y^ S` -/
def selfMonomial (S : Type uA) : PFunctor.{uA, uA} :=
  S y^ S

/-- The pure power polynomial functor `P(y) = y^ B` -/
def purePower (B : Type uB) : PFunctor.{uA, uB} :=
  PUnit y^ B

@[simp] lemma C_zero : C PEmpty = 0 := rfl

@[simp] lemma C_one : C PUnit = 1 := rfl

@[simp] lemma C_A (A : Type u) : (C A).A = A := rfl

@[simp] lemma C_B (A : Type u) (a : (C A).A) : (C A).B a = PEmpty := rfl

@[simp] lemma linear_A (A : Type u) : (linear A).A = A := rfl

@[simp] lemma linear_B (A : Type u) (a : (linear A).A) : (linear A).B a = PUnit := rfl

@[simp] lemma purePower_A (B : Type u) : (purePower B).A = PUnit := rfl

@[simp] lemma purePower_B (B : Type u) (a : (purePower B).A) : (purePower B).B a = B := rfl

end Monomial

section Coprod

/-- The coproduct (sum) of two polynomial functors `P` and `Q`, can be written as `P + Q`.
Requires the output universe level to be the same. -/
def coprod (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    PFunctor.{max uA₁ uA₂, uB} :=
  ⟨P.A ⊕ Q.A, Sum.elim P.B Q.B⟩

instance : HAdd PFunctor.{uA₁, uB} PFunctor.{uA₂, uB} PFunctor.{max uA₁ uA₂, uB} where
  hAdd := coprod

/-- The generalized coproduct (sigma type) of an indexed family of polynomial functors. -/
def sigma {I : Type v} (F : I → PFunctor.{uA, uB}) : PFunctor.{max uA v, uB} :=
  ⟨Σ i, (F i).A, fun ⟨i, a⟩ => (F i).B a⟩

end Coprod

section Prod

/-- The product of two polynomial functors `P` and `Q`. Can be written as `P * Q`. -/
def prod (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) :
    PFunctor.{max uA₁ uA₂, max uB₁ uB₂} :=
  ⟨P.A × Q.A, fun ab => P.B ab.1 ⊕ Q.B ab.2⟩

instance : HMul PFunctor.{uA₁, uB₁} PFunctor.{uA₂, uB₂} PFunctor.{max uA₁ uA₂, max uB₁ uB₂} where
  hMul := prod

/-- The generalized product (pi type) of an indexed family of polynomial functors. -/
def pi {I : Type v} (F : I → PFunctor.{uA, uB}) : PFunctor.{max uA v, max uB v} :=
  ⟨(i : I) → (F i).A, fun f => Σ i, (F i).B (f i)⟩

end Prod

section Tensor

/-- The tensor or parallel product of two polynomial functors `P` and `Q`. -/
def tensor (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) :
    PFunctor.{max uA₁ uA₂, max uB₁ uB₂} :=
  ⟨P.A × Q.A, fun ab => P.B ab.1 × Q.B ab.2⟩

@[inherit_doc] scoped[PFunctor] infixr:80 " ⊗ " => tensor

end Tensor

section Comp

/-- The composition of two polynomial functors `P₁` and `P₂`. -/
def comp (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁}) :
    PFunctor.{max uA₁ uA₂ uB₂, max uB₁ uB₂} :=
  ⟨Σ a₂ : P₂.1, P₂.2 a₂ → P₁.1, fun a₂a₁ => Σ u : P₂.2 a₂a₁.1, P₁.2 (a₂a₁.2 u)⟩

/-- Constructor for composition -/
def comp.mk (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁}) {α : Type v} (x : P₂ (P₁ α)) :
    comp P₂ P₁ α :=
  ⟨⟨x.1, Sigma.fst ∘ x.2⟩, fun a₂a₁ => (x.2 a₂a₁.1).2 a₂a₁.2⟩

/-- Destructor for composition -/
def comp.get (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁}) {α : Type v} (x : comp P₂ P₁ α) :
    P₂ (P₁ α) :=
  ⟨x.1.1, fun a₂ => ⟨x.1.2 a₂, fun a₁ => x.2 ⟨a₂, a₁⟩⟩⟩

@[inherit_doc] scoped[PFunctor] infixr:80 " ◃ " => comp

end Comp

section ULift

/-- Lift a polynomial functor `P` to a pair of larger universes. -/
protected def ulift (P : PFunctor.{uA, uB}) : PFunctor.{max uA vA, max uB vB} :=
  ⟨ULift P.A, fun a => ULift (P.B (ULift.down a))⟩

end ULift

/-- An equivalence between two polynomial functors `P` and `Q` is given by an equivalence of the
`A` types and an equivalence between the `B` types for each `a : A`. -/
@[ext]
structure Equiv (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) where
  equivA : P.A ≃ Q.A
  equivB : ∀ a, P.B a ≃ Q.B (equivA a)

namespace Equiv

/-- The identity equivalence between a polynomial functor `P` and itself. -/
def refl (P : PFunctor.{uA, uB}) : Equiv P P where
  equivA := _root_.Equiv.refl P.A
  equivB := fun a => _root_.Equiv.refl (P.B a)

/-- The inverse of an equivalence between polynomial functors. -/
def symm (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) (E : Equiv P Q) : Equiv Q P where
  equivA := E.equivA.symm
  equivB := fun a =>
    (Equiv.cast (congrArg Q.B ((Equiv.symm_apply_eq E.equivA).mp rfl))).trans
      (E.equivB (E.equivA.symm a)).symm

/-- The composition of two equivalences between polynomial functors. -/
def trans (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) (R : PFunctor.{uA₃, uB₃})
    (E : Equiv P Q) (F : Equiv Q R) : Equiv P R where
  equivA := E.equivA.trans F.equivA
  equivB := fun a => (E.equivB a).trans (F.equivB (E.equivA a))

/-- Equivalence between two polynomial functors `P` and `Q` that are equal. -/
def cast {P Q : PFunctor.{uA, uB}} (hA : P.A = Q.A) (hB : ∀ a, P.B a = Q.B (cast hA a)) :
    Equiv P Q where
  equivA := _root_.Equiv.cast hA
  equivB := fun a => _root_.Equiv.cast (hB a)

end Equiv

end PFunctor

/-
Lifting predicates and relations.
-/
namespace PFunctor

variable {P : PFunctor.{uA, uB}}

open Functor

theorem liftp_iff {α : Type u} (p : α → Prop) (x : P α) :
    Liftp p x ↔ ∃ a f, x = ⟨a, f⟩ ∧ ∀ i, p (f i) := by
  constructor
  · rintro ⟨y, hy⟩
    rcases h : y with ⟨a, f⟩
    refine ⟨a, fun i => (f i).val, ?_, fun i => (f i).property⟩
    rw [← hy, h, map_eq_map, PFunctor.map_eq]
    congr
  rintro ⟨a, f, xeq, pf⟩
  use ⟨a, fun i => ⟨f i, pf i⟩⟩
  rw [xeq]; rfl

theorem liftp_iff' {α : Type u} (p : α → Prop) (a : P.A) (f : P.B a → α) :
    @Liftp.{u} P.Obj _ α p ⟨a, f⟩ ↔ ∀ i, p (f i) := by
  simp only [liftp_iff]; constructor <;> intro h
  · rcases h with ⟨a', f', heq, h'⟩
    cases heq
    assumption
  repeat' first |constructor|assumption

theorem liftr_iff {α : Type u} (r : α → α → Prop) (x y : P α) :
    Liftr r x y ↔ ∃ a f₀ f₁, x = ⟨a, f₀⟩ ∧ y = ⟨a, f₁⟩ ∧ ∀ i, r (f₀ i) (f₁ i) := by
  constructor
  · rintro ⟨u, xeq, yeq⟩
    rcases h : u with ⟨a, f⟩
    use a, fun i => (f i).val.fst, fun i => (f i).val.snd
    constructor
    · rw [← xeq, h]
      rfl
    constructor
    · rw [← yeq, h]
      rfl
    intro i
    exact (f i).property
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  use ⟨a, fun i => ⟨(f₀ i, f₁ i), h i⟩⟩
  constructor
  · rw [xeq]
    rfl
  rw [yeq]; rfl

open Set

theorem supp_eq {α : Type u} (a : P.A) (f : P.B a → α) :
    @supp.{u} P.Obj _ α (⟨a, f⟩ : P α) = f '' univ := by
  ext x; simp only [supp, image_univ, mem_range, mem_setOf_eq]
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
