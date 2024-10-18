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
* `LogicalConnective` is defined so that `LogicalConnective F` is a type that has logical
  connectives $\top, \bot, \land, \lor, \to, \lnot$.
* `LogicalConnectiveHom` is defined so that `f : F →ˡᶜ G` is a homomorphism from `F` to `G` that
preserves logical connectives.
-/

/-- Syntax typeclass for negation of formula -/
@[notation_class] class FNot (α : Type*) where
  /-- Negation of formula -/
  fnot : α → α

/-- Syntax typeclass for implication of formula -/
@[notation_class] class FImp (α : Type*) where
  /-- Implication of formula -/
  fimp : α → α → α

/-- Syntax typeclass for conjunction of formula -/
@[notation_class] class FConj (α : Type*) where
  /-- Conjunction of formula -/
  fconj : α → α → α

/-- Syntax typeclass for disjunction of formula -/
@[notation_class] class FDisj (α : Type*) where
  /-- Disjunction of formula -/
  fdisj : α → α → α

/-- Prefix notation for `fnot` -/
prefix:75 "~" => FNot.fnot

/-- Infix notation for `fimp` -/
infixr:60 " ⭢ " => FImp.fimp

/-- Infix notation for `fconj` -/
infixr:69 " ⋏ " => FConj.fconj

/-- Infix notation for `fdisj` -/
infixr:68 " ⋎ " => FDisj.fdisj

attribute [match_pattern]
  FNot.fnot
  FImp.fimp
  FConj.fconj
  FDisj.fdisj

namespace ProofTheory

/-- `LogicalConnective` class describes a type's logical connectives -/
class LogicalConnective (α : Type*)
  extends Top α, Bot α, FNot α, FImp α, FConj α, FDisj α

/-- `DeMorgan` class describes proof systems implementing De Morgan's laws -/
class DeMorgan (F : Type*) [LogicalConnective F] : Prop where
  verum           : ~(⊤ : F) = ⊥
  falsum          : ~(⊥ : F) = ⊤
  imply (p q : F) : (p ⭢ q) = ~p ⋎ q
  and (p q : F)   : ~(p ⋏ q) = ~p ⋎ ~q
  or (p q : F)    : ~(p ⋎ q) = ~p ⋏ ~q
  neg (p : F)     : ~~p = p

attribute [simp] DeMorgan.verum DeMorgan.falsum DeMorgan.and DeMorgan.or DeMorgan.neg

/-- `NegDefinition` class describes proof systems implementing negation -/
class NegDefinition (F : Type*) [LogicalConnective F] : Prop where
  neg {p : F} : ~p = p ⭢ ⊥

attribute [simp] NegDefinition.neg

namespace LogicalConnective

section
variable {α : Type*} [LogicalConnective α]

/-- `iff` specifies if and only if notation -/
@[match_pattern] def iff (a b : α) := (a ⭢ b) ⋏ (b ⭢ a)

/-- Infix notation for `iff` -/
infix:61 " ⭤ " => LogicalConnective.iff

end

section Heyting

variable (α : Type*) [HeytingAlgebra α]

instance heyting : LogicalConnective α where
  fnot := (·ᶜ)
  fimp := (· ⇨ ·)
  fconj := (· ⊓ ·)
  fdisj := (· ⊔ ·)

variable {α}

@[simp] lemma prop_neg_eq_not (p : Prop) : ~p = ¬p := rfl

@[simp] lemma prop_arrow_eq_imp (p q : Prop) : (p ⭢ q) = (p → q) := rfl

@[simp] lemma prop_wedge_eq_and (p q : Prop) : (p ⋏ q) = (p ∧ q) := rfl

@[simp] lemma prop_vee_eq_or (p q : Prop) : (p ⋎ q) = (p ∨ q) := rfl

@[simp] lemma prop_iff_eq_iff (p q : Prop) : (p ⭤ q) = (p ↔ q) := by
  simp[LogicalConnective.iff, iff_iff_implies_and_implies]

instance : DeMorgan Prop where
  verum := by simp [Prop.top_eq_true, Prop.bot_eq_false]
  falsum := by simp [Prop.top_eq_true, Prop.bot_eq_false]
  imply := fun _ _ ↦ by simp[imp_iff_not_or]
  and := fun _ _ ↦ by simp[-not_and, not_and_or]
  or := fun _ _ ↦ by simp[not_or]
  neg := fun _ ↦ by simp

end Heyting

end LogicalConnective

variable (α β γ : Type*) [LogicalConnective α] [LogicalConnective β] [LogicalConnective γ]

/-- α →ˡᶜ β is the type of functions α → β that preserve the logical connectives.-/
structure LogicalConnectiveHom where
  /-- Function for homomorphism -/
  toFun : α → β
  /-- The proposition that a homomorphism preserves the top element.-/
  map_top' : toFun ⊤ = ⊤
  /-- The proposition that a homomorphism preserves the botom element.-/
  map_bot' : toFun ⊥ = ⊥
  /-- The proposition that a homomorphism preserves negation.-/
  map_neg' : ∀ p, toFun (~p) = ~toFun p
  /-- The proposition that a homomorphism preserves implication.-/
  map_imply' : ∀ p q, toFun (p ⭢ q) = toFun p ⭢ toFun q
  /-- The proposition that a homomorphism preserves conjunction.-/
  map_and' : ∀ p q, toFun (p ⋏ q) = toFun p ⋏ toFun q
  /-- The proposition that a homomorphism preserves disjunction.-/
  map_or'  : ∀ p q, toFun (p ⋎ q) = toFun p ⋎ toFun q

/-- Infix notation for `LogicalConnectiveHom` -/
infix:25 " →ˡᶜ " => LogicalConnectiveHom

/-- `LogicalConnectiveHomClass F α β` states that `F` is a type of homomorphisms over
logical connectives.

You should extend this class when you extend `LogicalConnectiveHom`. -/
class LogicalConnectiveHomClass (F : Type*) (α β : outParam Type*)
    [LogicalConnective α] [LogicalConnective β] [FunLike F α β] : Prop where
  /-- The proposition that a homomorphism preserves the top element.-/
  map_top (f : F) : f ⊤ = ⊤
  /-- The proposition that a homomorphism preserves the botom element.-/
  map_bot (f : F) : f ⊥ = ⊥
  /-- The proposition that a homomorphism preserves negation.-/
  map_neg (f : F) : ∀ (p : α), f (~p) = ~f p
  /-- The proposition that a homomorphism preserves implication.-/
  map_imply (f : F) : ∀ (p q : α), f (p ⭢ q) = f p ⭢ f q
  /-- The proposition that a homomorphism preserves conjunction.-/
  map_and (f : F) : ∀ (p q : α), f (p ⋏ q) = f p ⋏ f q
  /-- The proposition that a homomorphism preserves disjunction.-/
  map_or  (f : F) : ∀ (p q : α), f (p ⋎ q) = f p ⋎ f q

attribute [simp]
  LogicalConnectiveHomClass.map_top
  LogicalConnectiveHomClass.map_bot
  LogicalConnectiveHomClass.map_neg
  LogicalConnectiveHomClass.map_imply
  LogicalConnectiveHomClass.map_and
  LogicalConnectiveHomClass.map_or

namespace LogicalConnectiveHom

variable {α β γ}

instance : FunLike (α →ˡᶜ β) α β where
  coe := toFun
  coe_injective' := by intro f g h; rcases f; rcases g; simp; exact h

instance : CoeFun (α →ˡᶜ β) (fun _ ↦ α → β) := DFunLike.hasCoeToFun

@[ext] lemma ext (f g : α →ˡᶜ β) (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

instance : LogicalConnectiveHomClass (α →ˡᶜ β) α β where
  map_top := map_top'
  map_bot := map_bot'
  map_neg := map_neg'
  map_imply := map_imply'
  map_and := map_and'
  map_or := map_or'

/-- `id` defines the identity homomorphism preserving connectives -/
protected def id : α →ˡᶜ α where
  toFun := id
  map_top' := by simp
  map_bot' := by simp
  map_neg' := by simp
  map_imply' := by simp
  map_and' := by simp
  map_or' := by simp

@[simp] lemma app_id (a : α) : LogicalConnectiveHom.id a = a := rfl

/-- `comp` defines the composition of homomorphisms preserving connectives -/
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

end LogicalConnectiveHom

namespace LogicalConnectiveHomClass

variable {F : Type*} {α β : Type*}
  [LogicalConnective α] [LogicalConnective β] [FunLike F α β] [LogicalConnectiveHomClass F α β]
variable (f : F) (a b : α)

instance : CoeFun F (fun _ ↦ α → β) := ⟨DFunLike.coe⟩

@[simp] lemma map_iff : f (a ⭤ b) = f a ⭤ f b := by simp[LogicalConnective.iff]

end LogicalConnectiveHomClass

section quantifier

/-- `UnivQuantifier` class describes types indexed by `ℕ` using universal quantifers -/
@[notation_class] class UnivQuantifier (α : ℕ → Type*) where
  /-- universal quantifier symbol -/
  all : ∀ {n}, α (n + 1) → α n

/-- `ExQuantifier` class describes types indexed by `ℕ` using existential quantifers -/
@[notation_class] class ExQuantifier (α : ℕ → Type*) where
  /-- existential quantifier symbol -/
  ex : ∀ {n}, α (n + 1) → α n

/-- Infix notation for `univ` -/
prefix:64 "∀' " => UnivQuantifier.all

/-- Infix notation for `ex` -/
prefix:64 "∃' " => ExQuantifier.ex

attribute [match_pattern]
  UnivQuantifier.all
  ExQuantifier.ex

section UnivQuantifier

variable {α : ℕ → Type*} [UnivQuantifier α]

/-- Universal closure over `∀'` -/
def univClosure : {n : ℕ} → α n → α 0
  | 0,     a => a
  | _ + 1, a => univClosure (∀' a)

/-- Prefix notation for `univClosure` -/
prefix:64 "∀* " => univClosure

@[simp] lemma univClosure_zero (a : α 0) : ∀* a = a := rfl

lemma univClosure_succ {n} (a : α (n + 1)) : ∀* a = ∀* ∀' a := rfl

end UnivQuantifier

section ExQuantifier

variable {α : ℕ → Type*} [ExQuantifier α]

/-- Existential closure over `∃'` -/
def exClosure : {n : ℕ} → α n → α 0
  | 0,     a => a
  | _ + 1, a => exClosure (∃' a)

/-- Prefix notation for `exClosure` -/
prefix:64 "∃* " => exClosure

@[simp] lemma exClosure_zero (a : α 0) : ∃* a = a := rfl

lemma exClosure_succ {n} (a : α (n + 1)) : ∃* a = ∃* ∃' a := rfl

end ExQuantifier

variable {α : ℕ → Type*} [(n : ℕ) → LogicalConnective (α n)] [UnivQuantifier α] [ExQuantifier α]

/-- `ball` defines a bounded universal quantifier -/
def UnivQuantifier.ball {n : ℕ} (p : α (n + 1)) (q : α (n + 1)) : α n := ∀' (p ⭢ q)

/-- `bex` defines a bounded existential quantifier -/
def ExQuantifier.bex {n : ℕ} (p : α (n + 1)) (q : α (n + 1)) : α n := ∃' (p ⋏ q)

/-- Notation for `ball` -/
notation:64 "∀[" p "] " q => UnivQuantifier.ball p q

/-- Notation for `bex` -/
notation:64 "∃[" p "] " q => ExQuantifier.bex p q

end quantifier

/-- `Polarity` is a data type for managing quantifier alternation -/
inductive Polarity := | sigma | pi

namespace Polarity

/-- Notation for `sigma` -/
scoped[ProofTheory] notation "Σ" => Polarity.sigma
/-- Notation for `pi` -/
scoped[ProofTheory] notation "Π" => Polarity.pi

/-- `alt` specifies how quantifiers alternate -/
def alt : Polarity → Polarity
  | Σ => Π
  | Π => Σ

@[simp] lemma alt_sigma : Σ.alt = Π := rfl

@[simp] lemma alt_pi : Π.alt = Σ := rfl

@[simp] lemma alt_alt (b : Polarity) : b.alt.alt = b := by rcases b <;> simp

end Polarity

/-- `Turnstile` describes proof systems with turnstile (proves) -/
@[notation_class] class Turnstile (α : Type*) (β : Type*) where
  /-- turnstile symbol -/
  turnstile : Set α → α → β

/-- Infix notation for `turnstile` -/
infix:45 " ⊢ " => Turnstile.turnstile

end ProofTheory

open ProofTheory

namespace Matrix

variable {α β : Type*}

variable [LogicalConnective α] [LogicalConnective β]

/-- `Matrix.conj` defines conjunction over a vector -/
def conj : {n : ℕ} → (Fin n → α) → α
  | 0,     _ => ⊤
  | _ + 1, v => v 0 ⋏ conj (vecTail v)

@[simp] lemma conj_nil (v : Fin 0 → α) : conj v = ⊤ := rfl

@[simp] lemma conj_cons {n} (a : α) (v : Fin n → α) : conj (a :> v) = a ⋏ conj v := rfl

@[simp] lemma conj_hom_prop {F : Type*} [FunLike F α Prop] [LogicalConnectiveHomClass F α Prop]
  (f : F) {n} (v : Fin n → α) : f (conj v) = ∀ i, f (v i) := by
  induction' n with n ih <;> simp[Prop.top_eq_true, conj]
  · simp[ih]; constructor
    · intro ⟨hz, hs⟩ i; cases i using Fin.cases; { exact hz }; { exact hs _ }
    · intro h; exact ⟨h 0, fun i ↦ h _⟩

lemma hom_conj {F : Type*} [FunLike F α β] [LogicalConnectiveHomClass F α β]
    (f : F) {n} (v : Fin n → α) : f (conj v) = conj (f ∘ v) := by
  induction' n with n ih <;> simp[*, conj]

lemma hom_conj' {F : Type*} [FunLike F α β]  [LogicalConnectiveHomClass F α β]
    (f : F) {n} (v : Fin n → α) : f (conj v) = conj fun i ↦ f (v i) :=
  hom_conj f v

end Matrix

namespace List

variable {α : Type*} [LogicalConnective α]

/-- `List.conj` defines conjunction over a list -/
def conj : List α → α
  | []      => ⊤
  | a :: as => a ⋏ as.conj

@[simp] lemma conj_nil : conj (α := α) [] = ⊤ := rfl

@[simp] lemma conj_cons {a : α} {as : List α} : conj (a :: as) = a ⋏ as.conj := rfl

lemma map_conj {F : Type*} [FunLike F α Prop] [LogicalConnectiveHomClass F α Prop]
    (f : F) (l : List α) : f l.conj ↔ ∀ a ∈ l, f a := by
  induction l <;> simp[*, Prop.top_eq_true]

/-- `List.disj` defines disjunction over a list -/
def disj : List α → α
  | []      => ⊥
  | a :: as => a ⋎ as.disj

@[simp] lemma disj_nil : disj (α := α) [] = ⊥ := rfl

@[simp] lemma disj_cons {a : α} {as : List α} : disj (a :: as) = a ⋎ as.disj := rfl

lemma map_disj {F : Type*} [FunLike F α Prop] [LogicalConnectiveHomClass F α Prop]
    (f : F) (l : List α) : f l.disj ↔ ∃ a ∈ l, f a := by
  induction l <;> simp[*, Prop.top_eq_true, Prop.bot_eq_false]

end List

namespace Finset

variable {α : Type*} [LogicalConnective α]

/-- `Finset.conj` defines conjunction over a finite set -/
noncomputable def conj (s : Finset α) : α := s.toList.conj

lemma map_conj {F : Type*} [FunLike F α Prop] [LogicalConnectiveHomClass F α Prop] (f : F)
    (s : Finset α) : f s.conj ↔ ∀ a ∈ s, f a := by
  simpa using List.map_conj f s.toList

/-- `Finset.disj` defines disjunction over a set -/
noncomputable def disj (s : Finset α) : α := s.toList.disj

lemma map_disj {F : Type*} [FunLike F α Prop] [LogicalConnectiveHomClass F α Prop] (f : F)
    (s : Finset α) : f s.disj ↔ ∃ a ∈ s, f a := by
  simpa using List.map_disj f s.toList

end Finset
