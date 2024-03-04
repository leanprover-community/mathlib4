/-
Copyright (c) 2024 Shogo Saito. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shogo Saito. Adapted for mathlib by Hunter Monroe
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.FunLike.Basic
/-!
# Logic Symbols

Proof Theory studies proofs as mathematical objects, including axiomatic (Hilbert), deductive,
and sequent-based systems. This file defines logical symbols as objects abstractly to encompass
these approaches. It also defines homomorphisms that preserve these connectives.

## Main Definitions
* `LogicSymbol` is defined so that `LogicSymbol F` is a type that has logical connectives $\top,
  \bot, \land, \lor, \to, \lnot$.
* `LogicSymbol.Hom` is defined so that `f : F →ˡᶜ G` is a homomorphism from `F` to `G` that
preserves logical connectives.
-/

namespace ProofTheory

universe u

inductive Polarity := | sigma | pi

namespace Polarity

notation "Σ" => sigma
notation "Π" => pi

def alt : Polarity → Polarity
  | Σ => Π
  | Π => Σ

@[simp] lemma alt_sigma : Σ.alt = Π := rfl

@[simp] lemma alt_pi : Π.alt = Σ := rfl

@[simp] lemma alt_alt (b : Polarity) : b.alt.alt = b := by rcases b <;> simp

end Polarity

section logicNotation

@[notation_class] class Tilde (α : Type*) where
  tilde : α → α

@[notation_class] class Arrow (α : Type*) where
  arrow : α → α → α

@[notation_class] class Wedge (α : Type*) where
  wedge : α → α → α

@[notation_class] class Vee (α : Type*) where
  vee : α → α → α

class LogicSymbol (α : Type*)
  extends Top α, Bot α, Tilde α, Arrow α, Wedge α, Vee α

@[notation_class] class UnivQuantifier (α : ℕ → Type*) where
  univ : ∀ {n}, α (n + 1) → α n

@[notation_class] class ExQuantifier (α : ℕ → Type*) where
  ex : ∀ {n}, α (n + 1) → α n

prefix:75 "~" => Tilde.tilde

infixr:60 " ⭢ " => Arrow.arrow

infixr:69 " ⋏ " => Wedge.wedge

infixr:68 " ⋎ " => Vee.vee

prefix:64 "∀' " => UnivQuantifier.univ

prefix:64 "∃' " => ExQuantifier.ex

attribute [match_pattern]
  Tilde.tilde
  Arrow.arrow
  Wedge.wedge
  Vee.vee
  UnivQuantifier.univ
  ExQuantifier.ex

section UnivQuantifier

variable {α : ℕ → Type*} [UnivQuantifier α]

def univClosure : {n : ℕ} → α n → α 0
  | 0,     a => a
  | _ + 1, a => univClosure (∀' a)

prefix:64 "∀* " => univClosure

@[simp] lemma univClosure_zero (a : α 0) : ∀* a = a := rfl

lemma univClosure_succ {n} (a : α (n + 1)) : ∀* a = ∀* ∀' a := rfl

end UnivQuantifier

section ExQuantifier

variable {α : ℕ → Type*} [ExQuantifier α]

def exClosure : {n : ℕ} → α n → α 0
  | 0,     a => a
  | _ + 1, a => exClosure (∃' a)

prefix:64 "∃* " => exClosure

@[simp] lemma exClosure_zero (a : α 0) : ∃* a = a := rfl

lemma exClosure_succ {n} (a : α (n + 1)) : ∃* a = ∃* ∃' a := rfl

end ExQuantifier

@[notation_class] class HasTurnstile (α : Sort _) (β : Sort _) where
  turnstile : Set α → α → β

infix:45 " ⊢ " => HasTurnstile.turnstile

@[notation_class] class HasVdash (α : Sort _) (β : outParam (Sort _)) where
  vdash : α → β

prefix:45 "⊩ " => HasVdash.vdash

end logicNotation

class DeMorgan (F : Type*) [LogicSymbol F] where
  verum           : ~(⊤ : F) = ⊥
  falsum          : ~(⊥ : F) = ⊤
  imply (p q : F) : (p ⭢ q) = ~p ⋎ q
  and (p q : F)   : ~(p ⋏ q) = ~p ⋎ ~q
  or (p q : F)    : ~(p ⋎ q) = ~p ⋏ ~q
  neg (p : F)     : ~~p = p

attribute [simp] DeMorgan.verum DeMorgan.falsum DeMorgan.and DeMorgan.or DeMorgan.neg

class NegDefinition (F : Type*) [LogicSymbol F] where
  neg {p : F} : ~p = p ⭢ ⊥

attribute [simp] NegDefinition.neg

namespace LogicSymbol

section
variable {α : Sort _} [LogicSymbol α]

@[match_pattern] def iff (a b : α) := (a ⭢ b) ⋏ (b ⭢ a)

infix:61 " ⭤ " => LogicSymbol.iff

end

@[reducible]
instance propLogicSymbol : LogicSymbol Prop where
  top := True
  bot := False
  tilde := Not
  arrow := (· → ·)
  wedge := And
  vee := Or

@[simp] lemma Prop_top_eq : ⊤ = True := rfl

@[simp] lemma Prop_bot_eq : ⊥ = False := rfl

@[simp] lemma Prop_neg_eq (p : Prop) : ~ p = ¬p := rfl

@[simp] lemma Prop_arrow_eq (p q : Prop) : (p ⭢ q) = (p → q) := rfl

@[simp] lemma Prop_and_eq (p q : Prop) : (p ⋏ q) = (p ∧ q) := rfl

@[simp] lemma Prop_or_eq (p q : Prop) : (p ⋎ q) = (p ∨ q) := rfl

@[simp] lemma Prop_iff_eq (p q : Prop) : (p ⭤ q) = (p ↔ q) := by
  simp[LogicSymbol.iff, iff_iff_implies_and_implies]

instance : DeMorgan Prop where
  verum := by simp
  falsum := by simp
  imply := fun _ _ ↦ by simp[imp_iff_not_or]
  and := fun _ _ ↦ by simp[-not_and, not_and_or]
  or := fun _ _ ↦ by simp[not_or]
  neg := fun _ ↦ by simp

class HomClass (F : Type*) (α β : outParam Type*) [LogicSymbol α] [LogicSymbol β] [FunLike F α β] where
  map_top : ∀ (f : F), f ⊤ = ⊤
  map_bot : ∀ (f : F), f ⊥ = ⊥
  map_neg : ∀ (f : F) (p : α), f (~ p) = ~f p
  map_imply : ∀ (f : F) (p q : α), f (p ⭢ q) = f p ⭢ f q
  map_and : ∀ (f : F) (p q : α), f (p ⋏ q) = f p ⋏ f q
  map_or  : ∀ (f : F) (p q : α), f (p ⋎ q) = f p ⋎ f q

attribute [simp] HomClass.map_top HomClass.map_bot HomClass.map_neg HomClass.map_imply
  HomClass.map_and HomClass.map_or

namespace HomClass

variable (F : Type*) (α β : Type*) [LogicSymbol α] [LogicSymbol β] [FunLike F α β] [HomClass F α β]
variable (f : F) (a b : α)

instance : CoeFun F (fun _ ↦ α → β) := ⟨DFunLike.coe⟩

@[simp] lemma map_iff : f (a ⭤ b) = f a ⭤ f b := by simp[LogicSymbol.iff]

end HomClass

variable (α β γ : Type*) [LogicSymbol α] [LogicSymbol β] [LogicSymbol γ]

/-- α →ˡᶜ β is the type of functions α → β that preserve the logical connectives -/
structure Hom where
  toFun : α → β
  map_top' : toFun ⊤ = ⊤
  map_bot' : toFun ⊥ = ⊥
  map_neg' : ∀ p, toFun (~ p) = ~toFun p
  map_imply' : ∀ p q, toFun (p ⭢ q) = toFun p ⭢ toFun q
  map_and' : ∀ p q, toFun (p ⋏ q) = toFun p ⋏ toFun q
  map_or'  : ∀ p q, toFun (p ⋎ q) = toFun p ⋎ toFun q

infix:25 " →ˡᶜ " => Hom

namespace Hom

variable {α β γ}

instance : FunLike (α →ˡᶜ β) α β where
  coe := toFun
  coe_injective' := by intro f g h; rcases f; rcases g; simp; exact h

instance : CoeFun (α →ˡᶜ β) (fun _ ↦ α → β) := DFunLike.hasCoeToFun

@[ext] lemma ext (f g : α →ˡᶜ β) (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

instance : HomClass (α →ˡᶜ β) α β where
  map_top := map_top'
  map_bot := map_bot'
  map_neg := map_neg'
  map_imply := map_imply'
  map_and := map_and'
  map_or := map_or'

protected def id : α →ˡᶜ α where
  toFun := id
  map_top' := by simp
  map_bot' := by simp
  map_neg' := by simp
  map_imply' := by simp
  map_and' := by simp
  map_or' := by simp

@[simp] lemma app_id (a : α) : LogicSymbol.Hom.id a = a := rfl

def comp (g : β →ˡᶜ γ) (f : α →ˡᶜ β) : α →ˡᶜ γ where
  toFun := g ∘ f
  map_top' := by simp
  map_bot' := by simp
  map_neg' := by simp
  map_imply' := by simp
  map_and' := by simp
  map_or' := by simp

@[simp] lemma app_comp (g : β →ˡᶜ γ) (f : α →ˡᶜ β) (a : α) :
     g.comp f a = g (f a) := rfl

end Hom

section quantifier
variable {α : ℕ → Type u} [∀ i, LogicSymbol (α i)] [UnivQuantifier α] [ExQuantifier α]

def ball {n : ℕ} (p : α (n + 1)) (q : α (n + 1)) : α n := ∀' (p ⭢ q)

def bex {n : ℕ} (p : α (n + 1)) (q : α (n + 1)) : α n := ∃' (p ⋏ q)

notation:64 "∀[" p "] " q => ball p q

notation:64 "∃[" p "] " q => bex p q

end quantifier

class AndOrClosed {F} [LogicSymbol F] (C : F → Prop) where
  verum  : C ⊤
  falsum : C ⊥
  and {f g : F} : C f → C g → C (f ⋏ g)
  or  {f g : F} : C f → C g → C (f ⋎ g)

class Closed {F} [LogicSymbol F] (C : F → Prop) extends AndOrClosed C where
  not {f : F} : C f → C (~f)
  imply {f g : F} : C f → C g → C (f ⭢ g)

attribute [simp] AndOrClosed.verum AndOrClosed.falsum

end LogicSymbol

end ProofTheory

open ProofTheory

namespace Matrix

section And

variable {α β : Type*}
variable [LogicSymbol α] [LogicSymbol β]

def conj : {n : ℕ} → (Fin n → α) → α
  | 0,     _ => ⊤
  | _ + 1, v => v 0 ⋏ conj (vecTail v)

@[simp] lemma conj_nil (v : Fin 0 → α) : conj v = ⊤ := rfl

--infixr:70 " :> " ↦ vecCons

@[simp] lemma conj_cons {n} {a : α} {v : Fin n → α} : conj (a :> v) = a ⋏ conj v := rfl

@[simp] lemma conj_hom_prop {F : Type*} [FunLike F α Prop] [LogicSymbol.HomClass F α Prop]
  (f : F) {n} (v : Fin n → α) : f (conj v) = ∀ i, f (v i) := by
  induction' n with n ih <;> simp[conj]
  · simp[ih]; constructor
    · intro ⟨hz, hs⟩ i; cases i using Fin.cases; { exact hz }; { exact hs _ }
    · intro h; exact ⟨h 0, fun i ↦ h _⟩

lemma hom_conj {F : Type*} [FunLike F α β] [LogicSymbol.HomClass F α β]
    (f : F) {n} (v : Fin n → α) : f (conj v) = conj (f ∘ v) := by
  induction' n with n ih <;> simp[*, conj]

lemma hom_conj' {F : Type*} [FunLike F α β]  [LogicSymbol.HomClass F α β]
    (f : F) {n} (v : Fin n → α) : f (conj v) = conj fun i ↦ f (v i) :=
  hom_conj f v

end And

end Matrix

namespace List

section

variable {α : Type*} [LogicSymbol α]

def conj : List α → α
  | []      => ⊤
  | a :: as => a ⋏ as.conj

@[simp] lemma conj_nil : conj (α := α) [] = ⊤ := rfl

@[simp] lemma conj_cons {a : α} {as : List α} : conj (a :: as) = a ⋏ as.conj := rfl

lemma map_conj {F : Type*} [FunLike F α Prop] [LogicSymbol.HomClass F α Prop]
    (f : F) (l : List α) : f l.conj ↔ ∀ a ∈ l, f a := by
  induction l <;> simp[*]

def disj : List α → α
  | []      => ⊥
  | a :: as => a ⋎ as.disj

@[simp] lemma disj_nil : disj (α := α) [] = ⊥ := rfl

@[simp] lemma disj_cons {a : α} {as : List α} : disj (a :: as) = a ⋎ as.disj := rfl

lemma map_disj {F : Type*} [FunLike F α Prop] [LogicSymbol.HomClass F α Prop]
    (f : F) (l : List α) : f l.disj ↔ ∃ a ∈ l, f a := by
  induction l <;> simp[*]

end

end List

namespace Finset

section

variable {α : Type*} [LogicSymbol α]

noncomputable def conj (s : Finset α) : α := s.toList.conj

lemma map_conj {F : Type*} [FunLike F α Prop] [LogicSymbol.HomClass F α Prop] (f : F) (s : Finset α) :
    f s.conj ↔ ∀ a ∈ s, f a := by
  simpa using List.map_conj f s.toList

noncomputable def disj (s : Finset α) : α := s.toList.disj

lemma map_disj {F : Type*} [FunLike F α Prop] [LogicSymbol.HomClass F α Prop] (f : F) (s : Finset α) :
    f s.disj ↔ ∃ a ∈ s, f a := by
  simpa using List.map_disj f s.toList

end

end Finset
