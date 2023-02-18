/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module computability.primrec
! leanprover-community/mathlib commit 2738d2ca56cbc63be80c3bd48e9ed90ad94e947d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Equiv.Array
import Mathbin.Logic.Equiv.List
import Mathbin.Logic.Function.Iterate

/-!
# The primitive recursive functions

The primitive recursive functions are the least collection of functions
`nat → nat` which are closed under projections (using the mkpair
pairing function), composition, zero, successor, and primitive recursion
(i.e. nat.rec where the motive is C n := nat).

We can extend this definition to a large class of basic types by
using canonical encodings of types as natural numbers (Gödel numbering),
which we implement through the type class `encodable`. (More precisely,
we need that the composition of encode with decode yields a
primitive recursive function, so we have the `primcodable` type class
for this.)

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]
-/


open Denumerable Encodable Function

namespace Nat

/-- The non-dependent recursor on naturals. -/
def elim {C : Sort _} : C → (ℕ → C → C) → ℕ → C :=
  @Nat.rec fun _ => C
#align nat.elim Nat.elim

@[simp]
theorem elim_zero {C} (a f) : @Nat.elim C a f 0 = a :=
  rfl
#align nat.elim_zero Nat.elim_zero

@[simp]
theorem elim_succ {C} (a f n) : @Nat.elim C a f (succ n) = f n (Nat.elim a f n) :=
  rfl
#align nat.elim_succ Nat.elim_succ

/-- Cases on whether the input is 0 or a successor. -/
def cases {C : Sort _} (a : C) (f : ℕ → C) : ℕ → C :=
  Nat.elim a fun n _ => f n
#align nat.cases Nat.cases

@[simp]
theorem cases_zero {C} (a f) : @Nat.cases C a f 0 = a :=
  rfl
#align nat.cases_zero Nat.cases_zero

@[simp]
theorem cases_succ {C} (a f n) : @Nat.cases C a f (succ n) = f n :=
  rfl
#align nat.cases_succ Nat.cases_succ

/-- Calls the given function on a pair of entries `n`, encoded via the pairing function. -/
@[simp, reducible]
def unpaired {α} (f : ℕ → ℕ → α) (n : ℕ) : α :=
  f n.unpair.1 n.unpair.2
#align nat.unpaired Nat.unpaired

/-- The primitive recursive functions `ℕ → ℕ`. -/
inductive Primrec : (ℕ → ℕ) → Prop
  | zero : Primrec fun n => 0
  | succ : Primrec succ
  | left : Primrec fun n => n.unpair.1
  | right : Primrec fun n => n.unpair.2
  | pair {f g} : Primrec f → Primrec g → Primrec fun n => mkpair (f n) (g n)
  | comp {f g} : Primrec f → Primrec g → Primrec fun n => f (g n)
  |
  prec {f g} :
    Primrec f →
      Primrec g →
        Primrec (unpaired fun z n => n.elim (f z) fun y IH => g <| mkpair z <| mkpair y IH)
#align nat.primrec Nat.Primrec

namespace Primrec

theorem of_eq {f g : ℕ → ℕ} (hf : Primrec f) (H : ∀ n, f n = g n) : Primrec g :=
  (funext H : f = g) ▸ hf
#align nat.primrec.of_eq Nat.Primrec.of_eq

theorem const : ∀ n : ℕ, Primrec fun _ => n
  | 0 => zero
  | n + 1 => succ.comp (const n)
#align nat.primrec.const Nat.Primrec.const

protected theorem id : Primrec id :=
  (left.pair right).of_eq fun n => by simp
#align nat.primrec.id Nat.Primrec.id

theorem prec1 {f} (m : ℕ) (hf : Primrec f) :
    Primrec fun n => n.elim m fun y IH => f <| mkpair y IH :=
  ((prec (const m) (hf.comp right)).comp (zero.pair Primrec.id)).of_eq fun n => by simp
#align nat.primrec.prec1 Nat.Primrec.prec1

theorem cases1 {f} (m : ℕ) (hf : Primrec f) : Primrec (Nat.cases m f) :=
  (prec1 m (hf.comp left)).of_eq <| by simp [cases]
#align nat.primrec.cases1 Nat.Primrec.cases1

theorem cases {f g} (hf : Primrec f) (hg : Primrec g) :
    Primrec (unpaired fun z n => n.cases (f z) fun y => g <| mkpair z y) :=
  (prec hf (hg.comp (pair left (left.comp right)))).of_eq <| by simp [cases]
#align nat.primrec.cases Nat.Primrec.cases

protected theorem swap : Primrec (unpaired (swap mkpair)) :=
  (pair right left).of_eq fun n => by simp
#align nat.primrec.swap Nat.Primrec.swap

theorem swap' {f} (hf : Primrec (unpaired f)) : Primrec (unpaired (swap f)) :=
  (hf.comp Primrec.swap).of_eq fun n => by simp
#align nat.primrec.swap' Nat.Primrec.swap'

theorem pred : Primrec pred :=
  (cases1 0 Primrec.id).of_eq fun n => by cases n <;> simp [*]
#align nat.primrec.pred Nat.Primrec.pred

theorem add : Primrec (unpaired (· + ·)) :=
  (prec Primrec.id ((succ.comp right).comp right)).of_eq fun p => by
    simp <;> induction p.unpair.2 <;> simp [*, -add_comm, add_succ]
#align nat.primrec.add Nat.Primrec.add

theorem sub : Primrec (unpaired Sub.sub) :=
  (prec Primrec.id ((pred.comp right).comp right)).of_eq fun p => by
    simp <;> induction p.unpair.2 <;> simp [*, -add_comm, sub_succ]
#align nat.primrec.sub Nat.Primrec.sub

theorem mul : Primrec (unpaired (· * ·)) :=
  (prec zero (add.comp (pair left (right.comp right)))).of_eq fun p => by
    simp <;> induction p.unpair.2 <;> simp [*, mul_succ, add_comm]
#align nat.primrec.mul Nat.Primrec.mul

theorem pow : Primrec (unpaired (· ^ ·)) :=
  (prec (const 1) (mul.comp (pair (right.comp right) left))).of_eq fun p => by
    simp <;> induction p.unpair.2 <;> simp [*, pow_succ']
#align nat.primrec.pow Nat.Primrec.pow

end Primrec

end Nat

/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`prim] [] -/
/-- A `primcodable` type is an `encodable` type for which
  the encode/decode functions are primitive recursive. -/
class Primcodable (α : Type _) extends Encodable α where
  prim : Nat.Primrec fun n => Encodable.encode (decode n)
#align primcodable Primcodable

namespace Primcodable

open Nat.Primrec

instance (priority := 10) ofDenumerable (α) [Denumerable α] : Primcodable α :=
  ⟨succ.of_eq <| by simp⟩
#align primcodable.of_denumerable Primcodable.ofDenumerable

/-- Builds a `primcodable` instance from an equivalence to a `primcodable` type. -/
def ofEquiv (α) {β} [Primcodable α] (e : β ≃ α) : Primcodable β :=
  { Encodable.ofEquiv α e with
    prim :=
      (Primcodable.prim α).of_eq fun n =>
        show
          encode (decode α n) =
            (Option.casesOn (Option.map e.symm (decode α n)) 0 fun a => Nat.succ (encode (e a)) : ℕ)
          by cases decode α n <;> dsimp <;> simp }
#align primcodable.of_equiv Primcodable.ofEquiv

instance empty : Primcodable Empty :=
  ⟨zero⟩
#align primcodable.empty Primcodable.empty

instance unit : Primcodable PUnit :=
  ⟨(cases1 1 zero).of_eq fun n => by cases n <;> simp⟩
#align primcodable.unit Primcodable.unit

instance option {α : Type _} [h : Primcodable α] : Primcodable (Option α) :=
  ⟨(cases1 1 ((cases1 0 (succ.comp succ)).comp (Primcodable.prim α))).of_eq fun n => by
      cases n <;> simp <;> cases decode α n <;> rfl⟩
#align primcodable.option Primcodable.option

instance bool : Primcodable Bool :=
  ⟨(cases1 1 (cases1 2 zero)).of_eq fun n => by
      cases n; · rfl; cases n; · rfl
      rw [decode_ge_two]; · rfl
      exact by decide⟩
#align primcodable.bool Primcodable.bool

end Primcodable

/-- `primrec f` means `f` is primitive recursive (after
  encoding its input and output as natural numbers). -/
def Primrec {α β} [Primcodable α] [Primcodable β] (f : α → β) : Prop :=
  Nat.Primrec fun n => encode ((decode α n).map f)
#align primrec Primrec

namespace Primrec

variable {α : Type _} {β : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable σ]

open Nat.Primrec

protected theorem encode : Primrec (@encode α _) :=
  (Primcodable.prim α).of_eq fun n => by cases decode α n <;> rfl
#align primrec.encode Primrec.encode

protected theorem decode : Primrec (decode α) :=
  succ.comp (Primcodable.prim α)
#align primrec.decode Primrec.decode

theorem dom_denumerable {α β} [Denumerable α] [Primcodable β] {f : α → β} :
    Primrec f ↔ Nat.Primrec fun n => encode (f (ofNat α n)) :=
  ⟨fun h => (pred.comp h).of_eq fun n => by simp <;> rfl, fun h =>
    (succ.comp h).of_eq fun n => by simp <;> rfl⟩
#align primrec.dom_denumerable Primrec.dom_denumerable

theorem nat_iff {f : ℕ → ℕ} : Primrec f ↔ Nat.Primrec f :=
  dom_denumerable
#align primrec.nat_iff Primrec.nat_iff

theorem encdec : Primrec fun n => encode (decode α n) :=
  nat_iff.2 (Primcodable.prim α)
#align primrec.encdec Primrec.encdec

theorem option_some : Primrec (@some α) :=
  ((cases1 0 (succ.comp succ)).comp (Primcodable.prim α)).of_eq fun n => by
    cases decode α n <;> simp
#align primrec.option_some Primrec.option_some

theorem of_eq {f g : α → σ} (hf : Primrec f) (H : ∀ n, f n = g n) : Primrec g :=
  (funext H : f = g) ▸ hf
#align primrec.of_eq Primrec.of_eq

theorem const (x : σ) : Primrec fun a : α => x :=
  ((cases1 0 (const (encode x).succ)).comp (Primcodable.prim α)).of_eq fun n => by
    cases decode α n <;> rfl
#align primrec.const Primrec.const

protected theorem id : Primrec (@id α) :=
  (Primcodable.prim α).of_eq <| by simp
#align primrec.id Primrec.id

theorem comp {f : β → σ} {g : α → β} (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f (g a) :=
  ((cases1 0 (hf.comp <| pred.comp hg)).comp (Primcodable.prim α)).of_eq fun n =>
    by
    cases decode α n; · rfl
    simp [encodek]
#align primrec.comp Primrec.comp

theorem succ : Primrec Nat.succ :=
  nat_iff.2 Nat.Primrec.succ
#align primrec.succ Primrec.succ

theorem pred : Primrec Nat.pred :=
  nat_iff.2 Nat.Primrec.pred
#align primrec.pred Primrec.pred

theorem encode_iff {f : α → σ} : (Primrec fun a => encode (f a)) ↔ Primrec f :=
  ⟨fun h => Nat.Primrec.of_eq h fun n => by cases decode α n <;> rfl, Primrec.encode.comp⟩
#align primrec.encode_iff Primrec.encode_iff

theorem ofNat_iff {α β} [Denumerable α] [Primcodable β] {f : α → β} :
    Primrec f ↔ Primrec fun n => f (ofNat α n) :=
  dom_denumerable.trans <| nat_iff.symm.trans encode_iff
#align primrec.of_nat_iff Primrec.ofNat_iff

protected theorem ofNat (α) [Denumerable α] : Primrec (ofNat α) :=
  ofNat_iff.1 Primrec.id
#align primrec.of_nat Primrec.ofNat

theorem option_some_iff {f : α → σ} : (Primrec fun a => some (f a)) ↔ Primrec f :=
  ⟨fun h => encode_iff.1 <| pred.comp <| encode_iff.2 h, option_some.comp⟩
#align primrec.option_some_iff Primrec.option_some_iff

theorem ofEquiv {β} {e : β ≃ α} :
    haveI := Primcodable.ofEquiv α e
    Primrec e :=
  letI : Primcodable β := Primcodable.ofEquiv α e
  encode_iff.1 Primrec.encode
#align primrec.of_equiv Primrec.ofEquiv

theorem ofEquiv_symm {β} {e : β ≃ α} :
    haveI := Primcodable.ofEquiv α e
    Primrec e.symm :=
  letI := Primcodable.ofEquiv α e
  encode_iff.1 (show Primrec fun a => encode (e (e.symm a)) by simp [Primrec.encode])
#align primrec.of_equiv_symm Primrec.ofEquiv_symm

theorem ofEquiv_iff {β} (e : β ≃ α) {f : σ → β} :
    haveI := Primcodable.ofEquiv α e
    (Primrec fun a => e (f a)) ↔ Primrec f :=
  letI := Primcodable.ofEquiv α e
  ⟨fun h => (of_equiv_symm.comp h).of_eq fun a => by simp, of_equiv.comp⟩
#align primrec.of_equiv_iff Primrec.ofEquiv_iff

theorem ofEquiv_symm_iff {β} (e : β ≃ α) {f : σ → α} :
    haveI := Primcodable.ofEquiv α e
    (Primrec fun a => e.symm (f a)) ↔ Primrec f :=
  letI := Primcodable.ofEquiv α e
  ⟨fun h => (of_equiv.comp h).of_eq fun a => by simp, of_equiv_symm.comp⟩
#align primrec.of_equiv_symm_iff Primrec.ofEquiv_symm_iff

end Primrec

namespace Primcodable

open Nat.Primrec

instance prod {α β} [Primcodable α] [Primcodable β] : Primcodable (α × β) :=
  ⟨((cases zero ((cases zero succ).comp (pair right ((Primcodable.prim β).comp left)))).comp
          (pair right ((Primcodable.prim α).comp left))).of_eq
      fun n => by
      simp [Nat.unpaired]
      cases decode α n.unpair.1; · simp
      cases decode β n.unpair.2 <;> simp⟩
#align primcodable.prod Primcodable.prod

end Primcodable

namespace Primrec

variable {α : Type _} {σ : Type _} [Primcodable α] [Primcodable σ]

open Nat.Primrec

theorem fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.fst α β) :=
  ((cases zero
            ((cases zero (Nat.Primrec.succ.comp left)).comp
              (pair right ((Primcodable.prim β).comp left)))).comp
        (pair right ((Primcodable.prim α).comp left))).of_eq
    fun n => by
    simp
    cases decode α n.unpair.1 <;> simp
    cases decode β n.unpair.2 <;> simp
#align primrec.fst Primrec.fst

theorem snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.snd α β) :=
  ((cases zero
            ((cases zero (Nat.Primrec.succ.comp right)).comp
              (pair right ((Primcodable.prim β).comp left)))).comp
        (pair right ((Primcodable.prim α).comp left))).of_eq
    fun n => by
    simp
    cases decode α n.unpair.1 <;> simp
    cases decode β n.unpair.2 <;> simp
#align primrec.snd Primrec.snd

theorem pair {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {f : α → β} {g : α → γ}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => (f a, g a) :=
  ((cases1 0
            (Nat.Primrec.succ.comp <|
              pair (Nat.Primrec.pred.comp hf) (Nat.Primrec.pred.comp hg))).comp
        (Primcodable.prim α)).of_eq
    fun n => by cases decode α n <;> simp [encodek] <;> rfl
#align primrec.pair Primrec.pair

theorem unpair : Primrec Nat.unpair :=
  (pair (nat_iff.2 Nat.Primrec.left) (nat_iff.2 Nat.Primrec.right)).of_eq fun n => by simp
#align primrec.unpair Primrec.unpair

theorem list_nth₁ : ∀ l : List α, Primrec l.get?
  | [] => dom_denumerable.2 zero
  | a :: l =>
    dom_denumerable.2 <|
      (cases1 (encode a).succ <| dom_denumerable.1 <| list_nth₁ l).of_eq fun n => by
        cases n <;> simp
#align primrec.list_nth₁ Primrec.list_nth₁

end Primrec

/-- `primrec₂ f` means `f` is a binary primitive recursive function.
  This is technically unnecessary since we can always curry all
  the arguments together, but there are enough natural two-arg
  functions that it is convenient to express this directly. -/
def Primrec₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α → β → σ) :=
  Primrec fun p : α × β => f p.1 p.2
#align primrec₂ Primrec₂

/-- `primrec_pred p` means `p : α → Prop` is a (decidable)
  primitive recursive predicate, which is to say that
  `to_bool ∘ p : α → bool` is primitive recursive. -/
def PrimrecPred {α} [Primcodable α] (p : α → Prop) [DecidablePred p] :=
  Primrec fun a => decide (p a)
#align primrec_pred PrimrecPred

/-- `primrec_rel p` means `p : α → β → Prop` is a (decidable)
  primitive recursive relation, which is to say that
  `to_bool ∘ p : α → β → bool` is primitive recursive. -/
def PrimrecRel {α β} [Primcodable α] [Primcodable β] (s : α → β → Prop)
    [∀ a b, Decidable (s a b)] :=
  Primrec₂ fun a b => decide (s a b)
#align primrec_rel PrimrecRel

namespace Primrec₂

variable {α : Type _} {β : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable σ]

theorem of_eq {f g : α → β → σ} (hg : Primrec₂ f) (H : ∀ a b, f a b = g a b) : Primrec₂ g :=
  (by funext a b <;> apply H : f = g) ▸ hg
#align primrec₂.of_eq Primrec₂.of_eq

theorem const (x : σ) : Primrec₂ fun (a : α) (b : β) => x :=
  Primrec.const _
#align primrec₂.const Primrec₂.const

protected theorem pair : Primrec₂ (@Prod.mk α β) :=
  Primrec.pair Primrec.fst Primrec.snd
#align primrec₂.pair Primrec₂.pair

theorem left : Primrec₂ fun (a : α) (b : β) => a :=
  Primrec.fst
#align primrec₂.left Primrec₂.left

theorem right : Primrec₂ fun (a : α) (b : β) => b :=
  Primrec.snd
#align primrec₂.right Primrec₂.right

theorem mkpair : Primrec₂ Nat.mkpair := by simp [Primrec₂, Primrec] <;> constructor
#align primrec₂.mkpair Primrec₂.mkpair

theorem unpaired {f : ℕ → ℕ → α} : Primrec (Nat.unpaired f) ↔ Primrec₂ f :=
  ⟨fun h => by simpa using h.comp mkpair, fun h => h.comp Primrec.unpair⟩
#align primrec₂.unpaired Primrec₂.unpaired

theorem unpaired' {f : ℕ → ℕ → ℕ} : Nat.Primrec (Nat.unpaired f) ↔ Primrec₂ f :=
  Primrec.nat_iff.symm.trans unpaired
#align primrec₂.unpaired' Primrec₂.unpaired'

theorem encode_iff {f : α → β → σ} : (Primrec₂ fun a b => encode (f a b)) ↔ Primrec₂ f :=
  Primrec.encode_iff
#align primrec₂.encode_iff Primrec₂.encode_iff

theorem option_some_iff {f : α → β → σ} : (Primrec₂ fun a b => some (f a b)) ↔ Primrec₂ f :=
  Primrec.option_some_iff
#align primrec₂.option_some_iff Primrec₂.option_some_iff

theorem ofNat_iff {α β σ} [Denumerable α] [Denumerable β] [Primcodable σ] {f : α → β → σ} :
    Primrec₂ f ↔ Primrec₂ fun m n : ℕ => f (ofNat α m) (ofNat β n) :=
  (Primrec.ofNat_iff.trans <| by simp).trans unpaired
#align primrec₂.of_nat_iff Primrec₂.ofNat_iff

theorem uncurry {f : α → β → σ} : Primrec (Function.uncurry f) ↔ Primrec₂ f := by
  rw [show Function.uncurry f = fun p : α × β => f p.1 p.2 from funext fun ⟨a, b⟩ => rfl] <;> rfl
#align primrec₂.uncurry Primrec₂.uncurry

theorem curry {f : α × β → σ} : Primrec₂ (Function.curry f) ↔ Primrec f := by
  rw [← uncurry, Function.uncurry_curry]
#align primrec₂.curry Primrec₂.curry

end Primrec₂

section Comp

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable σ]

theorem Primrec.comp₂ {f : γ → σ} {g : α → β → γ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec₂ fun a b => f (g a b) :=
  hf.comp hg
#align primrec.comp₂ Primrec.comp₂

theorem Primrec₂.comp {f : β → γ → σ} {g : α → β} {h : α → γ} (hf : Primrec₂ f) (hg : Primrec g)
    (hh : Primrec h) : Primrec fun a => f (g a) (h a) :=
  hf.comp (hg.pair hh)
#align primrec₂.comp Primrec₂.comp

theorem Primrec₂.comp₂ {f : γ → δ → σ} {g : α → β → γ} {h : α → β → δ} (hf : Primrec₂ f)
    (hg : Primrec₂ g) (hh : Primrec₂ h) : Primrec₂ fun a b => f (g a b) (h a b) :=
  hf.comp hg hh
#align primrec₂.comp₂ Primrec₂.comp₂

theorem PrimrecPred.comp {p : β → Prop} [DecidablePred p] {f : α → β} :
    PrimrecPred p → Primrec f → PrimrecPred fun a => p (f a) :=
  Primrec.comp
#align primrec_pred.comp PrimrecPred.comp

theorem PrimrecRel.comp {R : β → γ → Prop} [∀ a b, Decidable (R a b)] {f : α → β} {g : α → γ} :
    PrimrecRel R → Primrec f → Primrec g → PrimrecPred fun a => R (f a) (g a) :=
  Primrec₂.comp
#align primrec_rel.comp PrimrecRel.comp

theorem PrimrecRel.comp₂ {R : γ → δ → Prop} [∀ a b, Decidable (R a b)] {f : α → β → γ}
    {g : α → β → δ} :
    PrimrecRel R → Primrec₂ f → Primrec₂ g → PrimrecRel fun a b => R (f a b) (g a b) :=
  PrimrecRel.comp
#align primrec_rel.comp₂ PrimrecRel.comp₂

end Comp

theorem PrimrecPred.of_eq {α} [Primcodable α] {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hp : PrimrecPred p) (H : ∀ a, p a ↔ q a) : PrimrecPred q :=
  Primrec.of_eq hp fun a => Bool.decide_congr (H a)
#align primrec_pred.of_eq PrimrecPred.of_eq

theorem PrimrecRel.of_eq {α β} [Primcodable α] [Primcodable β] {r s : α → β → Prop}
    [∀ a b, Decidable (r a b)] [∀ a b, Decidable (s a b)] (hr : PrimrecRel r)
    (H : ∀ a b, r a b ↔ s a b) : PrimrecRel s :=
  Primrec₂.of_eq hr fun a b => Bool.decide_congr (H a b)
#align primrec_rel.of_eq PrimrecRel.of_eq

namespace Primrec₂

variable {α : Type _} {β : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable σ]

open Nat.Primrec

theorem swap {f : α → β → σ} (h : Primrec₂ f) : Primrec₂ (swap f) :=
  h.comp₂ Primrec₂.right Primrec₂.left
#align primrec₂.swap Primrec₂.swap

theorem nat_iff {f : α → β → σ} :
    Primrec₂ f ↔
      Nat.Primrec
        (Nat.unpaired fun m n : ℕ => encode <| (decode α m).bind fun a => (decode β n).map (f a)) :=
  by
  have :
    ∀ (a : Option α) (b : Option β),
      Option.map (fun p : α × β => f p.1 p.2)
          (Option.bind a fun a : α => Option.map (Prod.mk a) b) =
        Option.bind a fun a => Option.map (f a) b :=
    by intros <;> cases a <;> [rfl, · cases b <;> rfl]
  simp [Primrec₂, Primrec, this]
#align primrec₂.nat_iff Primrec₂.nat_iff

theorem nat_iff' {f : α → β → σ} :
    Primrec₂ f ↔
      Primrec₂ fun m n : ℕ => Option.bind (decode α m) fun a => Option.map (f a) (decode β n) :=
  nat_iff.trans <| unpaired'.trans encode_iff
#align primrec₂.nat_iff' Primrec₂.nat_iff'

end Primrec₂

namespace Primrec

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable σ]

theorem to₂ {f : α × β → σ} (hf : Primrec f) : Primrec₂ fun a b => f (a, b) :=
  hf.of_eq fun ⟨a, b⟩ => rfl
#align primrec.to₂ Primrec.to₂

theorem nat_elim {f : α → β} {g : α → ℕ × β → β} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec₂ fun a (n : ℕ) => n.elim (f a) fun n IH => g a (n, IH) :=
  Primrec₂.nat_iff.2 <|
    ((Nat.Primrec.cases Nat.Primrec.zero <|
              (Nat.Primrec.prec hf <|
                    Nat.Primrec.comp hg <|
                      Nat.Primrec.left.pair <|
                        (Nat.Primrec.left.comp Nat.Primrec.right).pair <|
                          Nat.Primrec.pred.comp <| Nat.Primrec.right.comp Nat.Primrec.right).comp <|
                Nat.Primrec.right.pair <| Nat.Primrec.right.comp Nat.Primrec.left).comp <|
          Nat.Primrec.id.pair <| (Primcodable.prim α).comp Nat.Primrec.left).of_eq
      fun n => by
      simp
      cases' decode α n.unpair.1 with a; · rfl
      simp [encodek]
      induction' n.unpair.2 with m <;> simp [encodek]
      simp [ih, encodek]
#align primrec.nat_elim Primrec.nat_elim

theorem nat_elim' {f : α → ℕ} {g : α → β} {h : α → ℕ × β → β} (hf : Primrec f) (hg : Primrec g)
    (hh : Primrec₂ h) : Primrec fun a => (f a).elim (g a) fun n IH => h a (n, IH) :=
  (nat_elim hg hh).comp Primrec.id hf
#align primrec.nat_elim' Primrec.nat_elim'

theorem nat_elim₁ {f : ℕ → α → α} (a : α) (hf : Primrec₂ f) : Primrec (Nat.elim a f) :=
  nat_elim' Primrec.id (const a) <| comp₂ hf Primrec₂.right
#align primrec.nat_elim₁ Primrec.nat_elim₁

theorem nat_cases' {f : α → β} {g : α → ℕ → β} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec₂ fun a => Nat.cases (f a) (g a) :=
  nat_elim hf <| hg.comp₂ Primrec₂.left <| comp₂ fst Primrec₂.right
#align primrec.nat_cases' Primrec.nat_cases'

theorem nat_cases {f : α → ℕ} {g : α → β} {h : α → ℕ → β} (hf : Primrec f) (hg : Primrec g)
    (hh : Primrec₂ h) : Primrec fun a => (f a).cases (g a) (h a) :=
  (nat_cases' hg hh).comp Primrec.id hf
#align primrec.nat_cases Primrec.nat_cases

theorem nat_cases₁ {f : ℕ → α} (a : α) (hf : Primrec f) : Primrec (Nat.cases a f) :=
  nat_cases Primrec.id (const a) (comp₂ hf Primrec₂.right)
#align primrec.nat_cases₁ Primrec.nat_cases₁

theorem nat_iterate {f : α → ℕ} {g : α → β} {h : α → β → β} (hf : Primrec f) (hg : Primrec g)
    (hh : Primrec₂ h) : Primrec fun a => (h a^[f a]) (g a) :=
  (nat_elim' hf hg (hh.comp₂ Primrec₂.left <| snd.comp₂ Primrec₂.right)).of_eq fun a => by
    induction f a <;> simp [*, Function.iterate_succ']
#align primrec.nat_iterate Primrec.nat_iterate

theorem option_cases {o : α → Option β} {f : α → σ} {g : α → β → σ} (ho : Primrec o)
    (hf : Primrec f) (hg : Primrec₂ g) :
    @Primrec _ σ _ _ fun a => Option.casesOn (o a) (f a) (g a) :=
  encode_iff.1 <|
    (nat_cases (encode_iff.2 ho) (encode_iff.2 hf) <|
          pred.comp₂ <|
            Primrec₂.encode_iff.2 <|
              (Primrec₂.nat_iff'.1 hg).comp₂ ((@Primrec.encode α _).comp fst).to₂
                Primrec₂.right).of_eq
      fun a => by cases' o a with b <;> simp [encodek] <;> rfl
#align primrec.option_cases Primrec.option_cases

theorem option_bind {f : α → Option β} {g : α → β → Option σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => (f a).bind (g a) :=
  (option_cases hf (const none) hg).of_eq fun a => by cases f a <;> rfl
#align primrec.option_bind Primrec.option_bind

theorem option_bind₁ {f : α → Option σ} (hf : Primrec f) : Primrec fun o => Option.bind o f :=
  option_bind Primrec.id (hf.comp snd).to₂
#align primrec.option_bind₁ Primrec.option_bind₁

theorem option_map {f : α → Option β} {g : α → β → σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => (f a).map (g a) :=
  option_bind hf (option_some.comp₂ hg)
#align primrec.option_map Primrec.option_map

theorem option_map₁ {f : α → σ} (hf : Primrec f) : Primrec (Option.map f) :=
  option_map Primrec.id (hf.comp snd).to₂
#align primrec.option_map₁ Primrec.option_map₁

theorem option_iget [Inhabited α] : Primrec (@Option.iget α _) :=
  (option_cases Primrec.id (const <| @default α _) Primrec₂.right).of_eq fun o => by cases o <;> rfl
#align primrec.option_iget Primrec.option_iget

theorem option_isSome : Primrec (@Option.isSome α) :=
  (option_cases Primrec.id (const false) (const true).to₂).of_eq fun o => by cases o <;> rfl
#align primrec.option_is_some Primrec.option_isSome

theorem option_getD : Primrec₂ (@Option.getD α) :=
  Primrec.of_eq (option_cases Primrec₂.left Primrec₂.right Primrec₂.right) fun ⟨o, a⟩ => by
    cases o <;> rfl
#align primrec.option_get_or_else Primrec.option_getD

theorem bind_decode_iff {f : α → β → Option σ} :
    (Primrec₂ fun a n => (decode β n).bind (f a)) ↔ Primrec₂ f :=
  ⟨fun h => by simpa [encodek] using h.comp fst ((@Primrec.encode β _).comp snd), fun h =>
    option_bind (Primrec.decode.comp snd) <| h.comp (fst.comp fst) snd⟩
#align primrec.bind_decode_iff Primrec.bind_decode_iff

theorem map_decode_iff {f : α → β → σ} :
    (Primrec₂ fun a n => (decode β n).map (f a)) ↔ Primrec₂ f :=
  bind_decode_iff.trans Primrec₂.option_some_iff
#align primrec.map_decode_iff Primrec.map_decode_iff

theorem nat_add : Primrec₂ ((· + ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.add
#align primrec.nat_add Primrec.nat_add

theorem nat_sub : Primrec₂ (Sub.sub : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.sub
#align primrec.nat_sub Primrec.nat_sub

theorem nat_mul : Primrec₂ ((· * ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.mul
#align primrec.nat_mul Primrec.nat_mul

theorem cond {c : α → Bool} {f : α → σ} {g : α → σ} (hc : Primrec c) (hf : Primrec f)
    (hg : Primrec g) : Primrec fun a => cond (c a) (f a) (g a) :=
  (nat_cases (encode_iff.2 hc) hg (hf.comp fst).to₂).of_eq fun a => by cases c a <;> rfl
#align primrec.cond Primrec.cond

theorem ite {c : α → Prop} [DecidablePred c] {f : α → σ} {g : α → σ} (hc : PrimrecPred c)
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => if c a then f a else g a := by
  simpa using cond hc hf hg
#align primrec.ite Primrec.ite

theorem nat_le : PrimrecRel ((· ≤ ·) : ℕ → ℕ → Prop) :=
  (nat_cases nat_sub (const true) (const false).to₂).of_eq fun p =>
    by
    dsimp [swap]
    cases' e : p.1 - p.2 with n
    · simp [tsub_eq_zero_iff_le.1 e]
    · simp [not_le.2 (Nat.lt_of_sub_eq_succ e)]
#align primrec.nat_le Primrec.nat_le

theorem nat_min : Primrec₂ (@min ℕ _) :=
  ite nat_le fst snd
#align primrec.nat_min Primrec.nat_min

theorem nat_max : Primrec₂ (@max ℕ _) :=
  ite (nat_le.comp Primrec.fst Primrec.snd) snd fst
#align primrec.nat_max Primrec.nat_max

theorem dom_bool (f : Bool → α) : Primrec f :=
  (cond Primrec.id (const (f true)) (const (f false))).of_eq fun b => by cases b <;> rfl
#align primrec.dom_bool Primrec.dom_bool

theorem dom_bool₂ (f : Bool → Bool → α) : Primrec₂ f :=
  (cond fst ((dom_bool (f true)).comp snd) ((dom_bool (f false)).comp snd)).of_eq fun ⟨a, b⟩ => by
    cases a <;> rfl
#align primrec.dom_bool₂ Primrec.dom_bool₂

protected theorem not : Primrec not :=
  dom_bool _
#align primrec.bnot Primrec.not

protected theorem and : Primrec₂ and :=
  dom_bool₂ _
#align primrec.band Primrec.and

protected theorem or : Primrec₂ or :=
  dom_bool₂ _
#align primrec.bor Primrec.or

/- warning: primrec.not clashes with primrec.bnot -> Primrec.not
warning: primrec.not -> Primrec.not is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : Primcodable.{u_1} α] {p : α -> Prop} [_inst_6 : DecidablePred.{succ u_1} α p], (PrimrecPred.{u_1} α _inst_1 p (fun (a : α) => _inst_6 a)) -> (PrimrecPred.{u_1} α _inst_1 (fun (a : α) => Not (p a)) (fun (a : α) => Not.decidable (p a) (_inst_6 a)))
but is expected to have type
  Primrec.{0, 0} Bool Bool Primcodable.bool Primcodable.bool not
Case conversion may be inaccurate. Consider using '#align primrec.not Primrec.notₓ'. -/
protected theorem not {p : α → Prop} [DecidablePred p] (hp : PrimrecPred p) :
    PrimrecPred fun a => ¬p a :=
  (Primrec.not.comp hp).of_eq fun n => by simp
#align primrec.not Primrec.not

/- warning: primrec.and clashes with primrec.band -> Primrec.and
warning: primrec.and -> Primrec.and is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : Primcodable.{u_1} α] {p : α -> Prop} {q : α -> Prop} [_inst_6 : DecidablePred.{succ u_1} α p] [_inst_7 : DecidablePred.{succ u_1} α q], (PrimrecPred.{u_1} α _inst_1 p (fun (a : α) => _inst_6 a)) -> (PrimrecPred.{u_1} α _inst_1 q (fun (a : α) => _inst_7 a)) -> (PrimrecPred.{u_1} α _inst_1 (fun (a : α) => And (p a) (q a)) (fun (a : α) => And.decidable (p a) (q a) (_inst_6 a) (_inst_7 a)))
but is expected to have type
  Primrec₂.{0, 0, 0} Bool Bool Bool Primcodable.bool Primcodable.bool Primcodable.bool and
Case conversion may be inaccurate. Consider using '#align primrec.and Primrec.andₓ'. -/
protected theorem and {p q : α → Prop} [DecidablePred p] [DecidablePred q] (hp : PrimrecPred p)
    (hq : PrimrecPred q) : PrimrecPred fun a => p a ∧ q a :=
  (Primrec.and.comp hp hq).of_eq fun n => by simp
#align primrec.and Primrec.and

/- warning: primrec.or clashes with primrec.bor -> Primrec.or
warning: primrec.or -> Primrec.or is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : Primcodable.{u_1} α] {p : α -> Prop} {q : α -> Prop} [_inst_6 : DecidablePred.{succ u_1} α p] [_inst_7 : DecidablePred.{succ u_1} α q], (PrimrecPred.{u_1} α _inst_1 p (fun (a : α) => _inst_6 a)) -> (PrimrecPred.{u_1} α _inst_1 q (fun (a : α) => _inst_7 a)) -> (PrimrecPred.{u_1} α _inst_1 (fun (a : α) => Or (p a) (q a)) (fun (a : α) => Or.decidable (p a) (q a) (_inst_6 a) (_inst_7 a)))
but is expected to have type
  Primrec₂.{0, 0, 0} Bool Bool Bool Primcodable.bool Primcodable.bool Primcodable.bool or
Case conversion may be inaccurate. Consider using '#align primrec.or Primrec.orₓ'. -/
protected theorem or {p q : α → Prop} [DecidablePred p] [DecidablePred q] (hp : PrimrecPred p)
    (hq : PrimrecPred q) : PrimrecPred fun a => p a ∨ q a :=
  (Primrec.or.comp hp hq).of_eq fun n => by simp
#align primrec.or Primrec.or

protected theorem eq [DecidableEq α] : PrimrecRel (@Eq α) :=
  have : PrimrecRel fun a b : ℕ => a = b :=
    (Primrec.and nat_le nat_le.symm).of_eq fun a => by simp [le_antisymm_iff]
  (this.comp₂ (Primrec.encode.comp₂ Primrec₂.left) (Primrec.encode.comp₂ Primrec₂.right)).of_eq
    fun a b => encode_injective.eq_iff
#align primrec.eq Primrec.eq

theorem nat_lt : PrimrecRel ((· < ·) : ℕ → ℕ → Prop) :=
  (nat_le.comp snd fst).Not.of_eq fun p => by simp
#align primrec.nat_lt Primrec.nat_lt

theorem option_guard {p : α → β → Prop} [∀ a b, Decidable (p a b)] (hp : PrimrecRel p) {f : α → β}
    (hf : Primrec f) : Primrec fun a => Option.guard (p a) (f a) :=
  ite (hp.comp Primrec.id hf) (option_some_iff.2 hf) (const none)
#align primrec.option_guard Primrec.option_guard

theorem option_orelse : Primrec₂ ((· <|> ·) : Option α → Option α → Option α) :=
  (option_cases fst snd (fst.comp fst).to₂).of_eq fun ⟨o₁, o₂⟩ => by cases o₁ <;> cases o₂ <;> rfl
#align primrec.option_orelse Primrec.option_orelse

protected theorem decode₂ : Primrec (decode₂ α) :=
  option_bind Primrec.decode <|
    option_guard ((@Primrec.eq _ _ Nat.decidableEq).comp (encode_iff.2 snd) (fst.comp fst)) snd
#align primrec.decode₂ Primrec.decode₂

theorem list_find_index₁ {p : α → β → Prop} [∀ a b, Decidable (p a b)] (hp : PrimrecRel p) :
    ∀ l : List β, Primrec fun a => l.findIndex (p a)
  | [] => const 0
  | a :: l => ite (hp.comp Primrec.id (const a)) (const 0) (succ.comp (list_find_index₁ l))
#align primrec.list_find_index₁ Primrec.list_find_index₁

theorem list_index_of₁ [DecidableEq α] (l : List α) : Primrec fun a => l.indexOfₓ a :=
  list_find_index₁ Primrec.eq l
#align primrec.list_index_of₁ Primrec.list_index_of₁

theorem dom_fintype [Fintype α] (f : α → σ) : Primrec f :=
  let ⟨l, nd, m⟩ := Finite.exists_univ_list α
  option_some_iff.1 <| by
    haveI := decidable_eq_of_encodable α
    refine' ((list_nth₁ (l.map f)).comp (list_index_of₁ l)).of_eq fun a => _
    rw [List.get?_map, List.nthLe_get? (List.indexOf_lt_length.2 (m _)), List.indexOf_nthLe] <;> rfl
#align primrec.dom_fintype Primrec.dom_fintype

theorem nat_boddDiv2 : Primrec Nat.boddDiv2 :=
  (nat_elim' Primrec.id (const (false, 0))
        (((cond fst (pair (const false) (succ.comp snd)) (pair (const true) snd)).comp snd).comp
            snd).to₂).of_eq
    fun n => by
    simp [-Nat.boddDiv2_eq]
    induction' n with n IH; · rfl
    simp [-Nat.boddDiv2_eq, Nat.boddDiv2, *]
    rcases Nat.boddDiv2 n with ⟨_ | _, m⟩ <;> simp [Nat.boddDiv2]
#align primrec.nat_bodd_div2 Primrec.nat_boddDiv2

theorem nat_bodd : Primrec Nat.bodd :=
  fst.comp nat_boddDiv2
#align primrec.nat_bodd Primrec.nat_bodd

theorem nat_div2 : Primrec Nat.div2 :=
  snd.comp nat_boddDiv2
#align primrec.nat_div2 Primrec.nat_div2

theorem nat_bit0 : Primrec (@bit0 ℕ _) :=
  nat_add.comp Primrec.id Primrec.id
#align primrec.nat_bit0 Primrec.nat_bit0

theorem nat_bit1 : Primrec (@bit1 ℕ _ _) :=
  nat_add.comp nat_bit0 (const 1)
#align primrec.nat_bit1 Primrec.nat_bit1

theorem nat_bit : Primrec₂ Nat.bit :=
  (cond Primrec.fst (nat_bit1.comp Primrec.snd) (nat_bit0.comp Primrec.snd)).of_eq fun n => by
    cases n.1 <;> rfl
#align primrec.nat_bit Primrec.nat_bit

theorem nat_div_mod : Primrec₂ fun n k : ℕ => (n / k, n % k) :=
  let f (a : ℕ × ℕ) : ℕ × ℕ :=
    a.1.elim (0, 0) fun _ IH =>
      if Nat.succ IH.2 = a.2 then (Nat.succ IH.1, 0) else (IH.1, Nat.succ IH.2)
  have hf : Primrec f :=
    nat_elim' fst (const (0, 0)) <|
      ((ite ((@Primrec.eq ℕ _ _).comp (succ.comp <| snd.comp snd) fst)
              (pair (succ.comp <| fst.comp snd) (const 0))
              (pair (fst.comp snd) (succ.comp <| snd.comp snd))).comp
          (pair (snd.comp fst) (snd.comp snd))).to₂
  suffices ∀ k n, (n / k, n % k) = f (n, k) from hf.of_eq fun ⟨m, n⟩ => by simp [this]
  fun k n =>
  by
  have :
    (f (n, k)).2 + k * (f (n, k)).1 = n ∧ (0 < k → (f (n, k)).2 < k) ∧ (k = 0 → (f (n, k)).1 = 0) :=
    by
    induction' n with n IH
    · exact ⟨rfl, id, fun _ => rfl⟩
    rw [fun n : ℕ =>
      show
        f (n.succ, k) =
          _root_.ite ((f (n, k)).2.succ = k) (Nat.succ (f (n, k)).1, 0)
            ((f (n, k)).1, (f (n, k)).2.succ)
        from rfl]
    by_cases h : (f (n, k)).2.succ = k <;> simp [h]
    · have := congr_arg Nat.succ IH.1
      refine' ⟨_, fun k0 => Nat.noConfusion (h.trans k0)⟩
      rwa [← Nat.succ_add, h, add_comm, ← Nat.mul_succ] at this
    · exact ⟨by rw [Nat.succ_add, IH.1], fun k0 => lt_of_le_of_ne (IH.2.1 k0) h, IH.2.2⟩
  revert this
  cases' f (n, k) with D M
  simp
  intro h₁ h₂ h₃
  cases Nat.eq_zero_or_pos k
  · simp [h, h₃ h] at h₁⊢
    simp [h₁]
  · exact (Nat.div_mod_unique h).2 ⟨h₁, h₂ h⟩
#align primrec.nat_div_mod Primrec.nat_div_mod

theorem nat_div : Primrec₂ ((· / ·) : ℕ → ℕ → ℕ) :=
  fst.comp₂ nat_div_mod
#align primrec.nat_div Primrec.nat_div

theorem nat_mod : Primrec₂ ((· % ·) : ℕ → ℕ → ℕ) :=
  snd.comp₂ nat_div_mod
#align primrec.nat_mod Primrec.nat_mod

end Primrec

section

variable {α : Type _} {β : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable σ]

variable (H : Nat.Primrec fun n => Encodable.encode (decode (List β) n))

include H

open Primrec

private def prim : Primcodable (List β) :=
  ⟨H⟩
#align prim prim

private theorem list_cases' {f : α → List β} {g : α → σ} {h : α → β × List β → σ}
    (hf :
      haveI := prim H
      Primrec f)
    (hg : Primrec g)
    (hh :
      haveI := prim H
      Primrec₂ h) :
    @Primrec _ σ _ _ fun a => List.casesOn (f a) (g a) fun b l => h a (b, l) :=
  letI := prim H
  have :
    @Primrec _ (Option σ) _ _ fun a =>
      (decode (Option (β × List β)) (encode (f a))).map fun o => Option.casesOn o (g a) (h a) :=
    ((@map_decode_iff _ (Option (β × List β)) _ _ _ _ _).2 <|
          to₂ <|
            option_cases snd (hg.comp fst) (hh.comp₂ (fst.comp₂ Primrec₂.left) Primrec₂.right)).comp
      Primrec.id (encode_iff.2 hf)
  option_some_iff.1 <| this.of_eq fun a => by cases' f a with b l <;> simp [encodek] <;> rfl
#align list_cases' list_cases'

private theorem list_foldl' {f : α → List β} {g : α → σ} {h : α → σ × β → σ}
    (hf :
      haveI := prim H
      Primrec f)
    (hg : Primrec g)
    (hh :
      haveI := prim H
      Primrec₂ h) :
    Primrec fun a => (f a).foldl (fun s b => h a (s, b)) (g a) :=
  letI := prim H
  let G (a : α) (IH : σ × List β) : σ × List β := List.casesOn IH.2 IH fun b l => (h a (IH.1, b), l)
  let F (a : α) (n : ℕ) := (G a^[n]) (g a, f a)
  have : Primrec fun a => (F a (encode (f a))).1 :=
    fst.comp <|
      nat_iterate (encode_iff.2 hf) (pair hg hf) <|
        list_cases' H (snd.comp snd) snd <|
          to₂ <|
            pair (hh.comp (fst.comp fst) <| pair ((fst.comp snd).comp fst) (fst.comp snd))
              (snd.comp snd)
  this.of_eq fun a =>
    by
    have :
      ∀ n, F a n = ((List.take n (f a)).foldl (fun s b => h a (s, b)) (g a), List.drop n (f a)) :=
      by
      intro
      simp [F]
      generalize f a = l
      generalize g a = x
      induction' n with n IH generalizing l x
      · rfl
      simp
      cases' l with b l <;> simp [IH]
    rw [this, List.take_all_of_le (length_le_encode _)]
#align list_foldl' list_foldl'

private theorem list_cons' :
    haveI := prim H
    Primrec₂ (@List.cons β) :=
  letI := prim H
  encode_iff.1 (succ.comp <| primrec₂.mkpair.comp (encode_iff.2 fst) (encode_iff.2 snd))
#align list_cons' list_cons'

private theorem list_reverse' :
    haveI := prim H
    Primrec (@List.reverse β) :=
  letI := prim H
  (list_foldl' H Primrec.id (const []) <| to₂ <| ((list_cons' H).comp snd fst).comp snd).of_eq
    (suffices ∀ l r, List.foldl (fun (s : List β) (b : β) => b :: s) r l = List.reverseAux l r from
      fun l => this l []
    fun l => by induction l <;> simp [*, List.reverseAux])
#align list_reverse' list_reverse'

end

namespace Primcodable

variable {α : Type _} {β : Type _}

variable [Primcodable α] [Primcodable β]

open Primrec

instance sum : Primcodable (Sum α β) :=
  ⟨Primrec.nat_iff.1 <|
      (encode_iff.2
            (cond nat_bodd
              (((@Primrec.decode β _).comp nat_div2).option_map <|
                to₂ <| nat_bit.comp (const true) (Primrec.encode.comp snd))
              (((@Primrec.decode α _).comp nat_div2).option_map <|
                to₂ <| nat_bit.comp (const false) (Primrec.encode.comp snd)))).of_eq
        fun n =>
        show _ = encode (decodeSum n) by
          simp [decode_sum]
          cases Nat.bodd n <;> simp [decode_sum]
          · cases decode α n.div2 <;> rfl
          · cases decode β n.div2 <;> rfl⟩
#align primcodable.sum Primcodable.sum

instance list : Primcodable (List α) :=
  ⟨letI H := Primcodable.prim (List ℕ)
    have : Primrec₂ fun (a : α) (o : Option (List ℕ)) => o.map (List.cons (encode a)) :=
      option_map snd <| (list_cons' H).comp ((@Primrec.encode α _).comp (fst.comp fst)) snd
    have :
      Primrec fun n =>
        (of_nat (List ℕ) n).reverse.foldl
          (fun o m => (decode α m).bind fun a => o.map (List.cons (encode a))) (some []) :=
      list_foldl' H ((list_reverse' H).comp (Primrec.ofNat (List ℕ))) (const (some []))
        (Primrec.comp₂ (bind_decode_iff.2 <| Primrec₂.swap this) Primrec₂.right)
    nat_iff.1 <|
      (encode_iff.2 this).of_eq fun n => by
        rw [List.foldl_reverse]
        apply Nat.case_strong_induction_on n; · simp
        intro n IH; simp
        cases' decode α n.unpair.1 with a; · rfl
        simp
        suffices :
          ∀ (o : Option (List ℕ)) (p) (_ : encode o = encode p),
            encode (Option.map (List.cons (encode a)) o) = encode (Option.map (List.cons a) p)
        exact this _ _ (IH _ (Nat.unpair_right_le n))
        intro o p IH
        cases o <;> cases p <;> injection IH with h
        exact congr_arg (fun k => (Nat.mkpair (encode a) k).succ.succ) h⟩
#align primcodable.list Primcodable.list

end Primcodable

namespace Primrec

variable {α : Type _} {β : Type _} {γ : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

theorem sum_inl : Primrec (@Sum.inl α β) :=
  encode_iff.1 <| nat_bit0.comp Primrec.encode
#align primrec.sum_inl Primrec.sum_inl

theorem sum_inr : Primrec (@Sum.inr α β) :=
  encode_iff.1 <| nat_bit1.comp Primrec.encode
#align primrec.sum_inr Primrec.sum_inr

theorem sum_cases {f : α → Sum β γ} {g : α → β → σ} {h : α → γ → σ} (hf : Primrec f)
    (hg : Primrec₂ g) (hh : Primrec₂ h) : @Primrec _ σ _ _ fun a => Sum.casesOn (f a) (g a) (h a) :=
  option_some_iff.1 <|
    (cond (nat_bodd.comp <| encode_iff.2 hf)
          (option_map (Primrec.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hh)
          (option_map (Primrec.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hg)).of_eq
      fun a => by cases' f a with b c <;> simp [Nat.div2_bit, Nat.bodd_bit, encodek] <;> rfl
#align primrec.sum_cases Primrec.sum_cases

theorem list_cons : Primrec₂ (@List.cons α) :=
  list_cons' (Primcodable.prim _)
#align primrec.list_cons Primrec.list_cons

theorem list_cases {f : α → List β} {g : α → σ} {h : α → β × List β → σ} :
    Primrec f →
      Primrec g →
        Primrec₂ h → @Primrec _ σ _ _ fun a => List.casesOn (f a) (g a) fun b l => h a (b, l) :=
  list_cases' (Primcodable.prim _)
#align primrec.list_cases Primrec.list_cases

theorem list_foldl {f : α → List β} {g : α → σ} {h : α → σ × β → σ} :
    Primrec f →
      Primrec g → Primrec₂ h → Primrec fun a => (f a).foldl (fun s b => h a (s, b)) (g a) :=
  list_foldl' (Primcodable.prim _)
#align primrec.list_foldl Primrec.list_foldl

theorem list_reverse : Primrec (@List.reverse α) :=
  list_reverse' (Primcodable.prim _)
#align primrec.list_reverse Primrec.list_reverse

theorem list_foldr {f : α → List β} {g : α → σ} {h : α → β × σ → σ} (hf : Primrec f)
    (hg : Primrec g) (hh : Primrec₂ h) :
    Primrec fun a => (f a).foldr (fun b s => h a (b, s)) (g a) :=
  (list_foldl (list_reverse.comp hf) hg <| to₂ <| hh.comp fst <| (pair snd fst).comp snd).of_eq
    fun a => by simp [List.foldl_reverse]
#align primrec.list_foldr Primrec.list_foldr

theorem list_head? : Primrec (@List.head? α) :=
  (list_cases Primrec.id (const none) (option_some_iff.2 <| fst.comp snd).to₂).of_eq fun l => by
    cases l <;> rfl
#align primrec.list_head' Primrec.list_head?

theorem list_headI [Inhabited α] : Primrec (@List.headI α _) :=
  (option_iget.comp list_head?).of_eq fun l => l.head!_eq_head?.symm
#align primrec.list_head Primrec.list_headI

theorem list_tail : Primrec (@List.tail α) :=
  (list_cases Primrec.id (const []) (snd.comp snd).to₂).of_eq fun l => by cases l <;> rfl
#align primrec.list_tail Primrec.list_tail

theorem list_rec {f : α → List β} {g : α → σ} {h : α → β × List β × σ → σ} (hf : Primrec f)
    (hg : Primrec g) (hh : Primrec₂ h) :
    @Primrec _ σ _ _ fun a => List.recOn (f a) (g a) fun b l IH => h a (b, l, IH) :=
  let F (a : α) := (f a).foldr (fun (b : β) (s : List β × σ) => (b :: s.1, h a (b, s))) ([], g a)
  have : Primrec F :=
    list_foldr hf (pair (const []) hg) <|
      to₂ <| pair ((list_cons.comp fst (fst.comp snd)).comp snd) hh
  (snd.comp this).of_eq fun a =>
    by
    suffices F a = (f a, List.recOn (f a) (g a) fun b l IH => h a (b, l, IH)) by rw [this]
    simp [F]
    induction' f a with b l IH <;> simp [*]
#align primrec.list_rec Primrec.list_rec

theorem list_get? : Primrec₂ (@List.get? α) :=
  let F (l : List α) (n : ℕ) :=
    l.foldl
      (fun (s : Sum ℕ α) (a : α) =>
        Sum.casesOn s (@Nat.cases (Sum ℕ α) (Sum.inr a) Sum.inl) Sum.inr)
      (Sum.inl n)
  have hF : Primrec₂ F :=
    list_foldl fst (sum_inl.comp snd)
      ((sum_cases fst (nat_cases snd (sum_inr.comp <| snd.comp fst) (sum_inl.comp snd).to₂).to₂
              (sum_inr.comp snd).to₂).comp
          snd).to₂
  have :
    @Primrec _ (Option α) _ _ fun p : List α × ℕ => Sum.casesOn (F p.1 p.2) (fun _ => none) some :=
    sum_cases hF (const none).to₂ (option_some.comp snd).to₂
  this.to₂.of_eq fun l n => by
    dsimp; symm
    induction' l with a l IH generalizing n; · rfl
    cases' n with n
    · rw [(_ : F (a :: l) 0 = Sum.inr a)]
      · rfl
      clear IH
      dsimp [F]
      induction' l with b l IH <;> simp [*]
    · apply IH
#align primrec.list_nth Primrec.list_get?

theorem list_getD (d : α) : Primrec₂ fun l n => List.getD l n d :=
  by
  simp only [List.getD_eq_getD_get?]
  exact option_get_or_else.comp₂ list_nth (const _)
#align primrec.list_nthd Primrec.list_getD

theorem list_getI [Inhabited α] : Primrec₂ (@List.getI α _) :=
  list_getD _
#align primrec.list_inth Primrec.list_getI

theorem list_append : Primrec₂ ((· ++ ·) : List α → List α → List α) :=
  (list_foldr fst snd <| to₂ <| comp (@list_cons α _) snd).to₂.of_eq fun l₁ l₂ => by
    induction l₁ <;> simp [*]
#align primrec.list_append Primrec.list_append

theorem list_concat : Primrec₂ fun l (a : α) => l ++ [a] :=
  list_append.comp fst (list_cons.comp snd (const []))
#align primrec.list_concat Primrec.list_concat

theorem list_map {f : α → List β} {g : α → β → σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => (f a).map (g a) :=
  (list_foldr hf (const []) <|
        to₂ <| list_cons.comp (hg.comp fst (fst.comp snd)) (snd.comp snd)).of_eq
    fun a => by induction f a <;> simp [*]
#align primrec.list_map Primrec.list_map

theorem list_range : Primrec List.range :=
  (nat_elim' Primrec.id (const []) ((list_concat.comp snd fst).comp snd).to₂).of_eq fun n => by
    simp <;> induction n <;> simp [*, List.range_succ] <;> rfl
#align primrec.list_range Primrec.list_range

theorem list_join : Primrec (@List.join α) :=
  (list_foldr Primrec.id (const []) <| to₂ <| comp (@list_append α _) snd).of_eq fun l => by
    dsimp <;> induction l <;> simp [*]
#align primrec.list_join Primrec.list_join

theorem list_length : Primrec (@List.length α) :=
  (list_foldr (@Primrec.id (List α) _) (const 0) <| to₂ <| (succ.comp <| snd.comp snd).to₂).of_eq
    fun l => by dsimp <;> induction l <;> simp [*, -add_comm]
#align primrec.list_length Primrec.list_length

theorem list_findIndex {f : α → List β} {p : α → β → Prop} [∀ a b, Decidable (p a b)]
    (hf : Primrec f) (hp : PrimrecRel p) : Primrec fun a => (f a).findIndex (p a) :=
  (list_foldr hf (const 0) <|
        to₂ <| ite (hp.comp fst <| fst.comp snd) (const 0) (succ.comp <| snd.comp snd)).of_eq
    fun a => Eq.symm <| by dsimp <;> induction' f a with b l <;> [rfl, simp [*, List.findIndex]]
#align primrec.list_find_index Primrec.list_findIndex

theorem list_indexOf [DecidableEq α] : Primrec₂ (@List.indexOf α _) :=
  to₂ <| list_findIndex snd <| Primrec.eq.comp₂ (fst.comp fst).to₂ snd.to₂
#align primrec.list_index_of Primrec.list_indexOfₓ

theorem nat_strong_rec (f : α → ℕ → σ) {g : α → List σ → Option σ} (hg : Primrec₂ g)
    (H : ∀ a n, g a ((List.range n).map (f a)) = some (f a n)) : Primrec₂ f :=
  suffices Primrec₂ fun a n => (List.range n).map (f a) from
    Primrec₂.option_some_iff.1 <|
      (list_get?.comp (this.comp fst (succ.comp snd)) snd).to₂.of_eq fun a n => by
        simp [List.get?_range (Nat.lt_succ_self n)] <;> rfl
  Primrec₂.option_some_iff.1 <|
    (nat_elim (const (some []))
          (to₂ <|
            option_bind (snd.comp snd) <|
              to₂ <|
                option_map (hg.comp (fst.comp fst) snd)
                  (to₂ <| list_concat.comp (snd.comp fst) snd))).of_eq
      fun a n => by
      simp; induction' n with n IH; · rfl
      simp [IH, H, List.range_succ]
#align primrec.nat_strong_rec Primrec.nat_strong_rec

end Primrec

namespace Primcodable

variable {α : Type _} {β : Type _}

variable [Primcodable α] [Primcodable β]

open Primrec

/-- A subtype of a primitive recursive predicate is `primcodable`. -/
def subtype {p : α → Prop} [DecidablePred p] (hp : PrimrecPred p) : Primcodable (Subtype p) :=
  ⟨have : Primrec fun n => (decode α n).bind fun a => Option.guard p a :=
      option_bind Primrec.decode (option_guard (hp.comp snd) snd)
    nat_iff.1 <|
      (encode_iff.2 this).of_eq fun n =>
        show _ = encode ((decode α n).bind fun a => _)
          by
          cases' decode α n with a; · rfl
          dsimp [Option.guard]
          by_cases h : p a <;> simp [h] <;> rfl⟩
#align primcodable.subtype Primcodable.subtype

instance fin {n} : Primcodable (Fin n) :=
  @ofEquiv _ _ (subtype <| nat_lt.comp Primrec.id (const n)) Fin.equivSubtype
#align primcodable.fin Primcodable.fin

instance vector {n} : Primcodable (Vector α n) :=
  subtype ((@Primrec.eq _ _ Nat.decidableEq).comp list_length (const _))
#align primcodable.vector Primcodable.vector

instance finArrow {n} : Primcodable (Fin n → α) :=
  ofEquiv _ (Equiv.vectorEquivFin _ _).symm
#align primcodable.fin_arrow Primcodable.finArrow

instance array {n} : Primcodable (Array' n α) :=
  ofEquiv _ (Equiv.arrayEquivFin _ _)
#align primcodable.array Primcodable.array

section Ulower

attribute [local instance] Encodable.decidableRangeEncode Encodable.decidableEqOfEncodable

instance ulower : Primcodable (Ulower α) :=
  have : PrimrecPred fun n => Encodable.decode₂ α n ≠ none :=
    Primrec.not
      (Primrec.eq.comp
        (Primrec.option_bind Primrec.decode
          (Primrec.ite (Primrec.eq.comp (Primrec.encode.comp Primrec.snd) Primrec.fst)
            (Primrec.option_some.comp Primrec.snd) (Primrec.const _)))
        (Primrec.const _))
  Primcodable.subtype <| PrimrecPred.of_eq this fun n => decode₂_ne_none_iff
#align primcodable.ulower Primcodable.ulower

end Ulower

end Primcodable

namespace Primrec

variable {α : Type _} {β : Type _} {γ : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

theorem subtype_val {p : α → Prop} [DecidablePred p] {hp : PrimrecPred p} :
    haveI := Primcodable.subtype hp
    Primrec (@Subtype.val α p) :=
  by
  letI := Primcodable.subtype hp
  refine' (Primcodable.prim (Subtype p)).of_eq fun n => _
  rcases decode (Subtype p) n with (_ | ⟨a, h⟩) <;> rfl
#align primrec.subtype_val Primrec.subtype_val

theorem subtype_val_iff {p : β → Prop} [DecidablePred p] {hp : PrimrecPred p} {f : α → Subtype p} :
    haveI := Primcodable.subtype hp
    (Primrec fun a => (f a).1) ↔ Primrec f :=
  by
  letI := Primcodable.subtype hp
  refine' ⟨fun h => _, fun hf => subtype_val.comp hf⟩
  refine' Nat.Primrec.of_eq h fun n => _
  cases' decode α n with a; · rfl
  simp; cases f a <;> rfl
#align primrec.subtype_val_iff Primrec.subtype_val_iff

theorem subtype_mk {p : β → Prop} [DecidablePred p] {hp : PrimrecPred p} {f : α → β}
    {h : ∀ a, p (f a)} (hf : Primrec f) :
    haveI := Primcodable.subtype hp
    Primrec fun a => @Subtype.mk β p (f a) (h a) :=
  subtype_val_iff.1 hf
#align primrec.subtype_mk Primrec.subtype_mk

theorem option_get {f : α → Option β} {h : ∀ a, (f a).isSome} :
    Primrec f → Primrec fun a => Option.get (h a) :=
  by
  intro hf
  refine' (nat.primrec.pred.comp hf).of_eq fun n => _
  generalize hx : decode α n = x
  cases x <;> simp
#align primrec.option_get Primrec.option_get

theorem ulower_down : Primrec (Ulower.down : α → Ulower α) :=
  letI : ∀ a, Decidable (a ∈ Set.range (encode : α → ℕ)) := decidable_range_encode _
  subtype_mk Primrec.encode
#align primrec.ulower_down Primrec.ulower_down

theorem ulower_up : Primrec (Ulower.up : Ulower α → α) :=
  letI : ∀ a, Decidable (a ∈ Set.range (encode : α → ℕ)) := decidable_range_encode _
  option_get (primrec.decode₂.comp subtype_val)
#align primrec.ulower_up Primrec.ulower_up

theorem fin_val_iff {n} {f : α → Fin n} : (Primrec fun a => (f a).1) ↔ Primrec f :=
  by
  let : Primcodable { a // id a < n }; swap
  exact (Iff.trans (by rfl) subtype_val_iff).trans (of_equiv_iff _)
#align primrec.fin_val_iff Primrec.fin_val_iff

theorem fin_val {n} : Primrec (coe : Fin n → ℕ) :=
  fin_val_iff.2 Primrec.id
#align primrec.fin_val Primrec.fin_val

theorem fin_succ {n} : Primrec (@Fin.succ n) :=
  fin_val_iff.1 <| by simp [succ.comp fin_val]
#align primrec.fin_succ Primrec.fin_succ

theorem vector_toList {n} : Primrec (@Vector.toList α n) :=
  subtype_val
#align primrec.vector_to_list Primrec.vector_toList

theorem vector_toList_iff {n} {f : α → Vector β n} : (Primrec fun a => (f a).toList) ↔ Primrec f :=
  subtype_val_iff
#align primrec.vector_to_list_iff Primrec.vector_toList_iff

theorem vector_cons {n} : Primrec₂ (@Vector.cons α n) :=
  vector_toList_iff.1 <| by simp <;> exact list_cons.comp fst (vector_to_list_iff.2 snd)
#align primrec.vector_cons Primrec.vector_cons

theorem vector_length {n} : Primrec (@Vector.length α n) :=
  const _
#align primrec.vector_length Primrec.vector_length

theorem vector_head {n} : Primrec (@Vector.head α n) :=
  option_some_iff.1 <| (list_head?.comp vector_toList).of_eq fun ⟨a :: l, h⟩ => rfl
#align primrec.vector_head Primrec.vector_head

theorem vector_tail {n} : Primrec (@Vector.tail α n) :=
  vector_toList_iff.1 <| (list_tail.comp vector_toList).of_eq fun ⟨l, h⟩ => by cases l <;> rfl
#align primrec.vector_tail Primrec.vector_tail

theorem vector_get {n} : Primrec₂ (@Vector.get α n) :=
  option_some_iff.1 <|
    (list_get?.comp (vector_toList.comp fst) (fin_val.comp snd)).of_eq fun a => by
      simp [Vector.get_eq_get] <;> rw [← List.nthLe_get?]
#align primrec.vector_nth Primrec.vector_get

theorem list_ofFn :
    ∀ {n} {f : Fin n → α → σ}, (∀ i, Primrec (f i)) → Primrec fun a => List.ofFn fun i => f i a
  | 0, f, hf => const []
  | n + 1, f, hf => by
    simp [List.ofFn_succ] <;> exact list_cons.comp (hf 0) (list_of_fn fun i => hf i.succ)
#align primrec.list_of_fn Primrec.list_ofFn

theorem vector_ofFn {n} {f : Fin n → α → σ} (hf : ∀ i, Primrec (f i)) :
    Primrec fun a => Vector.ofFn fun i => f i a :=
  vector_toList_iff.1 <| by simp [list_of_fn hf]
#align primrec.vector_of_fn Primrec.vector_ofFn

theorem vector_nth' {n} : Primrec (@Vector.get α n) :=
  ofEquiv_symm
#align primrec.vector_nth' Primrec.vector_nth'

theorem vector_of_fn' {n} : Primrec (@Vector.ofFn α n) :=
  ofEquiv
#align primrec.vector_of_fn' Primrec.vector_of_fn'

theorem fin_app {n} : Primrec₂ (@id (Fin n → σ)) :=
  (vector_get.comp (vector_of_fn'.comp fst) snd).of_eq fun ⟨v, i⟩ => by simp
#align primrec.fin_app Primrec.fin_app

theorem fin_curry₁ {n} {f : Fin n → α → σ} : Primrec₂ f ↔ ∀ i, Primrec (f i) :=
  ⟨fun h i => h.comp (const i) Primrec.id, fun h =>
    (vector_get.comp ((vector_ofFn h).comp snd) fst).of_eq fun a => by simp⟩
#align primrec.fin_curry₁ Primrec.fin_curry₁

theorem fin_curry {n} {f : α → Fin n → σ} : Primrec f ↔ Primrec₂ f :=
  ⟨fun h => fin_app.comp (h.comp fst) snd, fun h =>
    (vector_nth'.comp
          (vector_ofFn fun i => show Primrec fun a => f a i from h.comp Primrec.id (const i))).of_eq
      fun a => by funext i <;> simp⟩
#align primrec.fin_curry Primrec.fin_curry

end Primrec

namespace Nat

open Vector

/-- An alternative inductive definition of `primrec` which
  does not use the pairing function on ℕ, and so has to
  work with n-ary functions on ℕ instead of unary functions.
  We prove that this is equivalent to the regular notion
  in `to_prim` and `of_prim`. -/
inductive Primrec' : ∀ {n}, (Vector ℕ n → ℕ) → Prop
  | zero : @primrec' 0 fun _ => 0
  | succ : @primrec' 1 fun v => succ v.headI
  | nth {n} (i : Fin n) : primrec' fun v => v.get? i
  |
  comp {m n f} (g : Fin n → Vector ℕ m → ℕ) :
    primrec' f → (∀ i, primrec' (g i)) → primrec' fun a => f (ofFn fun i => g i a)
  |
  prec {n f g} :
    @primrec' n f →
      @primrec' (n + 2) g →
        primrec' fun v : Vector ℕ (n + 1) =>
          v.headI.elim (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)
#align nat.primrec' Nat.Primrec'

end Nat

namespace Nat.Primrec'

open Vector Primrec

open Nat (Primrec')

open Nat.Primrec'

/- ./././Mathport/Syntax/Translate/Command.lean:691:6: unsupported: hide command -/
theorem to_prim {n f} (pf : @Primrec' n f) : Primrec f :=
  by
  induction pf
  case zero => exact const 0
  case succ => exact primrec.succ.comp vector_head
  case nth n i => exact vector_nth.comp Primrec.id (const i)
  case comp m n f g _ _ hf hg => exact hf.comp (vector_of_fn fun i => hg i)
  case prec n f g _ _ hf hg =>
    exact
      nat_elim' vector_head (hf.comp vector_tail)
        (hg.comp <|
            vector_cons.comp (fst.comp snd) <|
              vector_cons.comp (snd.comp snd) <| (@vector_tail _ _ (n + 1)).comp fst).to₂
#align nat.primrec'.to_prim Nat.Primrec'.to_prim

theorem of_eq {n} {f g : Vector ℕ n → ℕ} (hf : Primrec' f) (H : ∀ i, f i = g i) : Primrec' g :=
  (funext H : f = g) ▸ hf
#align nat.primrec'.of_eq Nat.Primrec'.of_eq

theorem const {n} : ∀ m, @Primrec' n fun v => m
  | 0 => zero.comp Fin.elim0 fun i => i.elim0ₓ
  | m + 1 => succ.comp _ fun i => const m
#align nat.primrec'.const Nat.Primrec'.const

theorem head {n : ℕ} : @Primrec' n.succ head :=
  (nth 0).of_eq fun v => by simp [nth_zero]
#align nat.primrec'.head Nat.Primrec'.head

theorem tail {n f} (hf : @Primrec' n f) : @Primrec' n.succ fun v => f v.tail :=
  (hf.comp _ fun i => @nth _ i.succ).of_eq fun v => by
    rw [← of_fn_nth v.tail] <;> congr <;> funext i <;> simp
#align nat.primrec'.tail Nat.Primrec'.tail

/-- A function from vectors to vectors is primitive recursive when all of its projections are. -/
def Vec {n m} (f : Vector ℕ n → Vector ℕ m) : Prop :=
  ∀ i, Primrec' fun v => (f v).get? i
#align nat.primrec'.vec Nat.Primrec'.Vec

protected theorem nil {n} : @Vec n 0 fun _ => nil := fun i => i.elim0ₓ
#align nat.primrec'.nil Nat.Primrec'.nil

protected theorem cons {n m f g} (hf : @Primrec' n f) (hg : @Vec n m g) :
    Vec fun v => f v ::ᵥ g v := fun i => Fin.cases (by simp [*]) (fun i => by simp [hg i]) i
#align nat.primrec'.cons Nat.Primrec'.cons

theorem idv {n} : @Vec n n id :=
  nth
#align nat.primrec'.idv Nat.Primrec'.idv

theorem comp' {n m f g} (hf : @Primrec' m f) (hg : @Vec n m g) : Primrec' fun v => f (g v) :=
  (hf.comp _ hg).of_eq fun v => by simp
#align nat.primrec'.comp' Nat.Primrec'.comp'

theorem comp₁ (f : ℕ → ℕ) (hf : @Primrec' 1 fun v => f v.headI) {n g} (hg : @Primrec' n g) :
    Primrec' fun v => f (g v) :=
  hf.comp _ fun i => hg
#align nat.primrec'.comp₁ Nat.Primrec'.comp₁

theorem comp₂ (f : ℕ → ℕ → ℕ) (hf : @Primrec' 2 fun v => f v.headI v.tail.headI) {n g h}
    (hg : @Primrec' n g) (hh : @Primrec' n h) : Primrec' fun v => f (g v) (h v) := by
  simpa using hf.comp' (hg.cons <| hh.cons primrec'.nil)
#align nat.primrec'.comp₂ Nat.Primrec'.comp₂

theorem prec' {n f g h} (hf : @Primrec' n f) (hg : @Primrec' n g) (hh : @Primrec' (n + 2) h) :
    @Primrec' n fun v => (f v).elim (g v) fun y IH : ℕ => h (y ::ᵥ IH ::ᵥ v) := by
  simpa using comp' (prec hg hh) (hf.cons idv)
#align nat.primrec'.prec' Nat.Primrec'.prec'

theorem pred : @Primrec' 1 fun v => v.headI.pred :=
  (prec' head (const 0) head).of_eq fun v => by simp <;> cases v.head <;> rfl
#align nat.primrec'.pred Nat.Primrec'.pred

theorem add : @Primrec' 2 fun v => v.headI + v.tail.headI :=
  (prec head (succ.comp₁ _ (tail head))).of_eq fun v => by
    simp <;> induction v.head <;> simp [*, Nat.succ_add]
#align nat.primrec'.add Nat.Primrec'.add

theorem sub : @Primrec' 2 fun v => v.headI - v.tail.headI :=
  by
  suffices; simpa using comp₂ (fun a b => b - a) this (tail head) head
  refine' (prec head (pred.comp₁ _ (tail head))).of_eq fun v => _
  simp; induction v.head <;> simp [*, Nat.sub_succ]
#align nat.primrec'.sub Nat.Primrec'.sub

theorem mul : @Primrec' 2 fun v => v.headI * v.tail.headI :=
  (prec (const 0) (tail (add.comp₂ _ (tail head) head))).of_eq fun v => by
    simp <;> induction v.head <;> simp [*, Nat.succ_mul] <;> rw [add_comm]
#align nat.primrec'.mul Nat.Primrec'.mul

theorem if_lt {n a b f g} (ha : @Primrec' n a) (hb : @Primrec' n b) (hf : @Primrec' n f)
    (hg : @Primrec' n g) : @Primrec' n fun v => if a v < b v then f v else g v :=
  (prec' (sub.comp₂ _ hb ha) hg (tail <| tail hf)).of_eq fun v =>
    by
    cases e : b v - a v
    · simp [not_lt.2 (tsub_eq_zero_iff_le.mp e)]
    · simp [Nat.lt_of_sub_eq_succ e]
#align nat.primrec'.if_lt Nat.Primrec'.if_lt

theorem mkpair : @Primrec' 2 fun v => v.headI.mkpair v.tail.headI :=
  if_lt head (tail head) (add.comp₂ _ (tail <| mul.comp₂ _ head head) head)
    (add.comp₂ _ (add.comp₂ _ (mul.comp₂ _ head head) head) (tail head))
#align nat.primrec'.mkpair Nat.Primrec'.mkpair

protected theorem encode : ∀ {n}, @Primrec' n encode
  | 0 => (const 0).of_eq fun v => by rw [v.eq_nil] <;> rfl
  | n + 1 => (succ.comp₁ _ (mkpair.comp₂ _ head (tail encode))).of_eq fun ⟨a :: l, e⟩ => rfl
#align nat.primrec'.encode Nat.Primrec'.encode

theorem sqrt : @Primrec' 1 fun v => v.headI.sqrt :=
  by
  suffices H : ∀ n : ℕ, n.sqrt = n.elim 0 fun x y => if x.succ < y.succ * y.succ then y else y.succ
  · simp [H]
    have :=
      @prec' 1 _ _
        (fun v => by
          have x := v.head <;> have y := v.tail.head <;>
            exact if x.succ < y.succ * y.succ then y else y.succ)
        head (const 0) _
    · convert this
      funext
      congr
      funext x y
      congr <;> simp
    have x1 := succ.comp₁ _ head
    have y1 := succ.comp₁ _ (tail head)
    exact if_lt x1 (mul.comp₂ _ y1 y1) (tail head) y1
  intro ; symm
  induction' n with n IH; · simp
  dsimp; rw [IH]; split_ifs
  · exact le_antisymm (Nat.sqrt_le_sqrt (Nat.le_succ _)) (Nat.lt_succ_iff.1 <| Nat.sqrt_lt.2 h)
  ·
    exact
      Nat.eq_sqrt.2 ⟨not_lt.1 h, Nat.sqrt_lt.1 <| Nat.lt_succ_iff.2 <| Nat.sqrt_succ_le_succ_sqrt _⟩
#align nat.primrec'.sqrt Nat.Primrec'.sqrt

theorem unpair₁ {n f} (hf : @Primrec' n f) : @Primrec' n fun v => (f v).unpair.1 :=
  by
  have s := sqrt.comp₁ _ hf
  have fss := sub.comp₂ _ hf (mul.comp₂ _ s s)
  refine' (if_lt fss s fss s).of_eq fun v => _
  simp [Nat.unpair]; split_ifs <;> rfl
#align nat.primrec'.unpair₁ Nat.Primrec'.unpair₁

theorem unpair₂ {n f} (hf : @Primrec' n f) : @Primrec' n fun v => (f v).unpair.2 :=
  by
  have s := sqrt.comp₁ _ hf
  have fss := sub.comp₂ _ hf (mul.comp₂ _ s s)
  refine' (if_lt fss s s (sub.comp₂ _ fss s)).of_eq fun v => _
  simp [Nat.unpair]; split_ifs <;> rfl
#align nat.primrec'.unpair₂ Nat.Primrec'.unpair₂

theorem of_prim : ∀ {n f}, Primrec f → @Primrec' n f :=
  suffices ∀ f, Nat.Primrec f → @Primrec' 1 fun v => f v.headI from fun n f hf =>
    (pred.comp₁ _ <|
          (this _ hf).comp₁ (fun m => Encodable.encode <| (decode (Vector ℕ n) m).map f)
            Primrec'.encode).of_eq
      fun i => by simp [encodek]
  fun f hf => by
  induction hf
  case zero => exact const 0
  case succ => exact succ
  case left => exact unpair₁ head
  case right => exact unpair₂ head
  case pair f g _ _ hf hg => exact mkpair.comp₂ _ hf hg
  case comp f g _ _ hf hg => exact hf.comp₁ _ hg
  case prec f g _ _ hf hg =>
    simpa using
      prec' (unpair₂ head) (hf.comp₁ _ (unpair₁ head))
        (hg.comp₁ _ <|
          mkpair.comp₂ _ (unpair₁ <| tail <| tail head) (mkpair.comp₂ _ head (tail head)))
#align nat.primrec'.of_prim Nat.Primrec'.of_prim

theorem prim_iff {n f} : @Primrec' n f ↔ Primrec f :=
  ⟨to_prim, of_prim⟩
#align nat.primrec'.prim_iff Nat.Primrec'.prim_iff

theorem prim_iff₁ {f : ℕ → ℕ} : (@Primrec' 1 fun v => f v.headI) ↔ Primrec f :=
  prim_iff.trans
    ⟨fun h => (h.comp <| vector_ofFn fun i => Primrec.id).of_eq fun v => by simp, fun h =>
      h.comp vector_head⟩
#align nat.primrec'.prim_iff₁ Nat.Primrec'.prim_iff₁

theorem prim_iff₂ {f : ℕ → ℕ → ℕ} : (@Primrec' 2 fun v => f v.headI v.tail.headI) ↔ Primrec₂ f :=
  prim_iff.trans
    ⟨fun h =>
      (h.comp <| vector_cons.comp fst <| vector_cons.comp snd (Primrec.const nil)).of_eq fun v => by
        simp,
      fun h => h.comp vector_head (vector_head.comp vector_tail)⟩
#align nat.primrec'.prim_iff₂ Nat.Primrec'.prim_iff₂

theorem vec_iff {m n f} : @Vec m n f ↔ Primrec f :=
  ⟨fun h => by simpa using vector_of_fn fun i => to_prim (h i), fun h i =>
    of_prim <| vector_get.comp h (Primrec.const i)⟩
#align nat.primrec'.vec_iff Nat.Primrec'.vec_iff

end Nat.Primrec'

theorem Primrec.nat_sqrt : Primrec Nat.sqrt :=
  Nat.Primrec'.prim_iff₁.1 Nat.Primrec'.sqrt
#align primrec.nat_sqrt Primrec.nat_sqrt

