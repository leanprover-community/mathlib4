/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Logic.Encodable.Pi
import Mathlib.Logic.Function.Iterate

/-!
# The primitive recursive functions

The primitive recursive functions are the least collection of functions
`ℕ → ℕ` which are closed under projections (using the `pair`
pairing function), composition, zero, successor, and primitive recursion
(i.e. `Nat.rec` where the motive is `C n := ℕ`).

We can extend this definition to a large class of basic types by
using canonical encodings of types as natural numbers (Gödel numbering),
which we implement through the type class `Encodable`. (More precisely,
we need that the composition of encode with decode yields a
primitive recursive function, so we have the `Primcodable` type class
for this.)

In the above, the pairing function is primitive recursive by definition.
This deviates from the textbook definition of primitive recursive functions,
which instead work with *`n`-ary* functions. We formalize the textbook
definition in `Nat.Primrec'`. `Nat.Primrec'.prim_iff` then proves it is
equivalent to our chosen formulation. For more discussion of this and
other design choices in this formalization, see [carneiro2019].

## Main definitions

- `Nat.Primrec f`: `f` is primitive recursive, for functions `f : ℕ → ℕ`
- `Primrec f`: `f` is primitive recursive, for functions between `Primcodable` types
- `Primcodable α`: well-behaved encoding of `α` into `ℕ`, i.e. one such that roundtripping through
  the encoding functions adds no computational power

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]
-/

open List (Vector)
open Denumerable Encodable Function

namespace Nat

/-- Calls the given function on a pair of entries `n`, encoded via the pairing function. -/
@[simp, reducible]
def unpaired {α} (f : ℕ → ℕ → α) (n : ℕ) : α :=
  f n.unpair.1 n.unpair.2

/-- The primitive recursive functions `ℕ → ℕ`. -/
protected inductive Primrec : (ℕ → ℕ) → Prop
  | zero : Nat.Primrec fun _ => 0
  | protected succ : Nat.Primrec succ
  | left : Nat.Primrec fun n => n.unpair.1
  | right : Nat.Primrec fun n => n.unpair.2
  | pair {f g} : Nat.Primrec f → Nat.Primrec g → Nat.Primrec fun n => pair (f n) (g n)
  | comp {f g} : Nat.Primrec f → Nat.Primrec g → Nat.Primrec fun n => f (g n)
  | prec {f g} :
      Nat.Primrec f →
        Nat.Primrec g →
          Nat.Primrec (unpaired fun z n => n.rec (f z) fun y IH => g <| pair z <| pair y IH)

namespace Primrec

theorem of_eq {f g : ℕ → ℕ} (hf : Nat.Primrec f) (H : ∀ n, f n = g n) : Nat.Primrec g :=
  (funext H : f = g) ▸ hf

theorem const : ∀ n : ℕ, Nat.Primrec fun _ => n
  | 0 => zero
  | n + 1 => Primrec.succ.comp (const n)

protected theorem id : Nat.Primrec id :=
  (left.pair right).of_eq fun n => by simp

theorem prec1 {f} (m : ℕ) (hf : Nat.Primrec f) :
    Nat.Primrec fun n => n.rec m fun y IH => f <| Nat.pair y IH :=
  ((prec (const m) (hf.comp right)).comp (zero.pair Primrec.id)).of_eq fun n => by simp

theorem casesOn1 {f} (m : ℕ) (hf : Nat.Primrec f) : Nat.Primrec (Nat.casesOn · m f) :=
  (prec1 m (hf.comp left)).of_eq <| by simp

theorem casesOn' {f g} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (unpaired fun z n => n.casesOn (f z) fun y => g <| Nat.pair z y) :=
  (prec hf (hg.comp (pair left (left.comp right)))).of_eq fun n => by simp

protected theorem swap : Nat.Primrec (unpaired (swap Nat.pair)) :=
  (pair right left).of_eq fun n => by simp

theorem swap' {f} (hf : Nat.Primrec (unpaired f)) : Nat.Primrec (unpaired (swap f)) :=
  (hf.comp .swap).of_eq fun n => by simp

theorem pred : Nat.Primrec pred :=
  (casesOn1 0 Primrec.id).of_eq fun n => by cases n <;> simp [*]

theorem add : Nat.Primrec (unpaired (· + ·)) :=
  (prec .id ((Primrec.succ.comp right).comp right)).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, Nat.add_assoc]

theorem sub : Nat.Primrec (unpaired (· - ·)) :=
  (prec .id ((pred.comp right).comp right)).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, Nat.sub_add_eq]

theorem mul : Nat.Primrec (unpaired (· * ·)) :=
  (prec zero (add.comp (pair left (right.comp right)))).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, mul_succ, add_comm _ (unpair p).fst]

theorem pow : Nat.Primrec (unpaired (· ^ ·)) :=
  (prec (const 1) (mul.comp (pair (right.comp right) left))).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, Nat.pow_succ]

end Primrec

end Nat

/-- A `Primcodable` type is, essentially, an `Encodable` type for which
the encode/decode functions are primitive recursive.
However, such a definition is circular.

Instead, we ask that the composition of `decode : ℕ → Option α` with
`encode : Option α → ℕ` is primitive recursive. Said composition is
the identity function, restricted to the image of `encode`.
Thus, in a way, the added requirement ensures that no predicates
can be smuggled in through a cunning choice of the subset of `ℕ` into
which the type is encoded. -/
class Primcodable (α : Type*) extends Encodable α where
  prim (α) : Nat.Primrec fun n => Encodable.encode (decode n)

namespace Primcodable

open Nat.Primrec

instance (priority := 10) ofDenumerable (α) [Denumerable α] : Primcodable α :=
  ⟨Nat.Primrec.succ.of_eq <| by simp⟩

/-- Builds a `Primcodable` instance from an equivalence to a `Primcodable` type. -/
def ofEquiv (α) {β} [Primcodable α] (e : β ≃ α) : Primcodable β :=
  { __ := Encodable.ofEquiv α e
    prim := (Primcodable.prim α).of_eq fun n => by
      rw [decode_ofEquiv]
      cases (@decode α _ n) <;>
        simp [encode_ofEquiv] }

instance empty : Primcodable Empty :=
  ⟨zero⟩

instance unit : Primcodable PUnit :=
  ⟨(casesOn1 1 zero).of_eq fun n => by cases n <;> simp⟩

instance option {α : Type*} [h : Primcodable α] : Primcodable (Option α) :=
  ⟨(casesOn1 1 ((casesOn1 0 (.comp .succ .succ)).comp (Primcodable.prim α))).of_eq fun n => by
    cases n with
      | zero => rfl
      | succ n =>
        rw [decode_option_succ]
        cases H : @decode α _ n <;> simp [H]⟩

instance bool : Primcodable Bool :=
  ⟨(casesOn1 1 (casesOn1 2 zero)).of_eq fun n => match n with
    | 0 => rfl
    | 1 => rfl
    | (n + 2) => by rw [decode_ge_two] <;> simp⟩

end Primcodable

/-- `Primrec f` means `f` is primitive recursive (after
  encoding its input and output as natural numbers). -/
def Primrec {α β} [Primcodable α] [Primcodable β] (f : α → β) : Prop :=
  Nat.Primrec fun n => encode ((@decode α _ n).map f)

namespace Primrec

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

open Nat.Primrec

protected theorem encode : Primrec (@encode α _) :=
  (Primcodable.prim α).of_eq fun n => by cases @decode α _ n <;> rfl

protected theorem decode : Primrec (@decode α _) :=
  Nat.Primrec.succ.comp (Primcodable.prim α)

theorem dom_denumerable {α β} [Denumerable α] [Primcodable β] {f : α → β} :
    Primrec f ↔ Nat.Primrec fun n => encode (f (ofNat α n)) :=
  ⟨fun h => (pred.comp h).of_eq fun n => by simp, fun h =>
    (Nat.Primrec.succ.comp h).of_eq fun n => by simp⟩

theorem nat_iff {f : ℕ → ℕ} : Primrec f ↔ Nat.Primrec f :=
  dom_denumerable

theorem encdec : Primrec fun n => encode (@decode α _ n) :=
  nat_iff.2 (Primcodable.prim _)

theorem option_some : Primrec (@some α) :=
  ((casesOn1 0 (Nat.Primrec.succ.comp .succ)).comp (Primcodable.prim α)).of_eq fun n => by
    cases @decode α _ n <;> simp

theorem of_eq {f g : α → σ} (hf : Primrec f) (H : ∀ n, f n = g n) : Primrec g :=
  (funext H : f = g) ▸ hf

theorem const (x : σ) : Primrec fun _ : α => x :=
  ((casesOn1 0 (.const (encode x).succ)).comp (Primcodable.prim α)).of_eq fun n => by
    cases @decode α _ n <;> rfl

protected theorem id : Primrec (@id α) :=
  (Primcodable.prim α).of_eq <| by simp

theorem comp {f : β → σ} {g : α → β} (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f (g a) :=
  ((casesOn1 0 (.comp hf (pred.comp hg))).comp (Primcodable.prim α)).of_eq fun n => by
    cases @decode α _ n <;> simp [encodek]

theorem succ : Primrec Nat.succ :=
  nat_iff.2 Nat.Primrec.succ

theorem pred : Primrec Nat.pred :=
  nat_iff.2 Nat.Primrec.pred

theorem encode_iff {f : α → σ} : (Primrec fun a => encode (f a)) ↔ Primrec f :=
  ⟨fun h => Nat.Primrec.of_eq h fun n => by cases @decode α _ n <;> rfl, Primrec.encode.comp⟩

theorem ofNat_iff {α β} [Denumerable α] [Primcodable β] {f : α → β} :
    Primrec f ↔ Primrec fun n => f (ofNat α n) :=
  dom_denumerable.trans <| nat_iff.symm.trans encode_iff

protected theorem ofNat (α) [Denumerable α] : Primrec (ofNat α) :=
  ofNat_iff.1 Primrec.id

theorem option_some_iff {f : α → σ} : (Primrec fun a => some (f a)) ↔ Primrec f :=
  ⟨fun h => encode_iff.1 <| pred.comp <| encode_iff.2 h, option_some.comp⟩

theorem of_equiv {β} {e : β ≃ α} :
    haveI := Primcodable.ofEquiv α e
    Primrec e :=
  letI : Primcodable β := Primcodable.ofEquiv α e
  encode_iff.1 Primrec.encode

theorem of_equiv_symm {β} {e : β ≃ α} :
    haveI := Primcodable.ofEquiv α e
    Primrec e.symm :=
  letI := Primcodable.ofEquiv α e
  encode_iff.1 (show Primrec fun a => encode (e (e.symm a)) by simp [Primrec.encode])

theorem of_equiv_iff {β} (e : β ≃ α) {f : σ → β} :
    haveI := Primcodable.ofEquiv α e
    (Primrec fun a => e (f a)) ↔ Primrec f :=
  letI := Primcodable.ofEquiv α e
  ⟨fun h => (of_equiv_symm.comp h).of_eq fun a => by simp, of_equiv.comp⟩

theorem of_equiv_symm_iff {β} (e : β ≃ α) {f : σ → α} :
    haveI := Primcodable.ofEquiv α e
    (Primrec fun a => e.symm (f a)) ↔ Primrec f :=
  letI := Primcodable.ofEquiv α e
  ⟨fun h => (of_equiv.comp h).of_eq fun a => by simp, of_equiv_symm.comp⟩

end Primrec

namespace Primcodable

open Nat.Primrec

instance prod {α β} [Primcodable α] [Primcodable β] : Primcodable (α × β) :=
  ⟨((casesOn' zero ((casesOn' zero .succ).comp (pair right ((Primcodable.prim β).comp left)))).comp
          (pair right ((Primcodable.prim α).comp left))).of_eq
      fun n => by
      simp only [Nat.unpaired, Nat.unpair_pair, decode_prod_val]
      cases @decode α _ n.unpair.1; · simp
      cases @decode β _ n.unpair.2 <;> simp⟩

end Primcodable

namespace Primrec

variable {α : Type*} [Primcodable α]

open Nat.Primrec

theorem fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.fst α β) :=
  ((casesOn' zero
            ((casesOn' zero (Nat.Primrec.succ.comp left)).comp
              (pair right ((Primcodable.prim β).comp left)))).comp
        (pair right ((Primcodable.prim α).comp left))).of_eq
    fun n => by
    simp only [Nat.unpaired, Nat.unpair_pair, decode_prod_val]
    cases @decode α _ n.unpair.1 <;> simp
    cases @decode β _ n.unpair.2 <;> simp

theorem snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.snd α β) :=
  ((casesOn' zero
            ((casesOn' zero (Nat.Primrec.succ.comp right)).comp
              (pair right ((Primcodable.prim β).comp left)))).comp
        (pair right ((Primcodable.prim α).comp left))).of_eq
    fun n => by
    simp only [Nat.unpaired, Nat.unpair_pair, decode_prod_val]
    cases @decode α _ n.unpair.1 <;> simp
    cases @decode β _ n.unpair.2 <;> simp

theorem pair {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {f : α → β} {g : α → γ}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => (f a, g a) :=
  ((casesOn1 0
            (Nat.Primrec.succ.comp <|
              .pair (Nat.Primrec.pred.comp hf) (Nat.Primrec.pred.comp hg))).comp
        (Primcodable.prim α)).of_eq
    fun n => by cases @decode α _ n <;> simp [encodek]

theorem unpair : Primrec Nat.unpair :=
  (pair (nat_iff.2 .left) (nat_iff.2 .right)).of_eq fun n => by simp

theorem list_getElem?₁ : ∀ l : List α, Primrec (l[·]? : ℕ → Option α)
  | [] => dom_denumerable.2 zero
  | a :: l =>
    dom_denumerable.2 <|
      (casesOn1 (encode a).succ <| dom_denumerable.1 <| list_getElem?₁ l).of_eq fun n => by
        cases n <;> simp

end Primrec

/-- `Primrec₂ f` means `f` is a binary primitive recursive function.
  This is technically unnecessary since we can always curry all
  the arguments together, but there are enough natural two-arg
  functions that it is convenient to express this directly. -/
def Primrec₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α → β → σ) :=
  Primrec fun p : α × β => f p.1 p.2

/-- `PrimrecPred p` means `p : α → Prop` is a
  primitive recursive predicate, which is to say that
  `decide ∘ p : α → Bool` is primitive recursive. -/
def PrimrecPred {α} [Primcodable α] (p : α → Prop) :=
  ∃ (_ : DecidablePred p), Primrec fun a => decide (p a)

/-- `PrimrecRel p` means `p : α → β → Prop` is a
  primitive recursive relation, which is to say that
  `decide ∘ p : α → β → Bool` is primitive recursive. -/
def PrimrecRel {α β} [Primcodable α] [Primcodable β] (s : α → β → Prop) :=
  PrimrecPred fun p : α × β => s p.1 p.2

namespace Primrec₂

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

theorem mk {f : α → β → σ} (hf : Primrec fun p : α × β => f p.1 p.2) : Primrec₂ f := hf

theorem of_eq {f g : α → β → σ} (hg : Primrec₂ f) (H : ∀ a b, f a b = g a b) : Primrec₂ g :=
  (by funext a b; apply H : f = g) ▸ hg

theorem const (x : σ) : Primrec₂ fun (_ : α) (_ : β) => x :=
  Primrec.const _

protected theorem pair : Primrec₂ (@Prod.mk α β) :=
  Primrec.pair .fst .snd

theorem left : Primrec₂ fun (a : α) (_ : β) => a :=
  .fst

theorem right : Primrec₂ fun (_ : α) (b : β) => b :=
  .snd

theorem natPair : Primrec₂ Nat.pair := by simp [Primrec₂, Primrec]; constructor

theorem unpaired {f : ℕ → ℕ → α} : Primrec (Nat.unpaired f) ↔ Primrec₂ f :=
  ⟨fun h => by simpa using h.comp natPair, fun h => h.comp Primrec.unpair⟩

theorem unpaired' {f : ℕ → ℕ → ℕ} : Nat.Primrec (Nat.unpaired f) ↔ Primrec₂ f :=
  Primrec.nat_iff.symm.trans unpaired

theorem encode_iff {f : α → β → σ} : (Primrec₂ fun a b => encode (f a b)) ↔ Primrec₂ f :=
  Primrec.encode_iff

theorem option_some_iff {f : α → β → σ} : (Primrec₂ fun a b => some (f a b)) ↔ Primrec₂ f :=
  Primrec.option_some_iff

theorem ofNat_iff {α β σ} [Denumerable α] [Denumerable β] [Primcodable σ] {f : α → β → σ} :
    Primrec₂ f ↔ Primrec₂ fun m n : ℕ => f (ofNat α m) (ofNat β n) :=
  (Primrec.ofNat_iff.trans <| by simp).trans unpaired

theorem uncurry {f : α → β → σ} : Primrec (Function.uncurry f) ↔ Primrec₂ f := by
  rw [show Function.uncurry f = fun p : α × β => f p.1 p.2 from funext fun ⟨a, b⟩ => rfl]; rfl

theorem curry {f : α × β → σ} : Primrec₂ (Function.curry f) ↔ Primrec f := by
  rw [← uncurry, Function.uncurry_curry]

end Primrec₂

section Comp

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable σ]

theorem Primrec.comp₂ {f : γ → σ} {g : α → β → γ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec₂ fun a b => f (g a b) :=
  hf.comp hg

theorem Primrec₂.comp {f : β → γ → σ} {g : α → β} {h : α → γ} (hf : Primrec₂ f) (hg : Primrec g)
    (hh : Primrec h) : Primrec fun a => f (g a) (h a) :=
  Primrec.comp hf (hg.pair hh)

theorem Primrec₂.comp₂ {f : γ → δ → σ} {g : α → β → γ} {h : α → β → δ} (hf : Primrec₂ f)
    (hg : Primrec₂ g) (hh : Primrec₂ h) : Primrec₂ fun a b => f (g a b) (h a b) :=
  hf.comp hg hh

protected lemma PrimrecPred.decide {p : α → Prop} [DecidablePred p] (hp : PrimrecPred p) :
    Primrec (fun a => decide (p a)) := by
  convert hp.choose_spec

lemma Primrec.primrecPred {p : α → Prop} [DecidablePred p]
    (hp : Primrec (fun a => decide (p a))) : PrimrecPred p :=
  ⟨inferInstance, hp⟩

lemma primrecPred_iff_primrec_decide {p : α → Prop} [DecidablePred p] :
    PrimrecPred p ↔ Primrec (fun a => decide (p a)) where
  mp := PrimrecPred.decide
  mpr := Primrec.primrecPred

theorem PrimrecPred.comp {p : β → Prop} {f : α → β} :
    (hp : PrimrecPred p) → (hf : Primrec f) → PrimrecPred fun a => p (f a)
  | ⟨_i, hp⟩, hf => hp.comp hf |>.primrecPred

protected lemma PrimrecRel.decide {R : α → β → Prop} [DecidableRel R] (hR : PrimrecRel R) :
    Primrec₂ (fun a b => decide (R a b)) :=
  PrimrecPred.decide hR

lemma Primrec₂.primrecRel {R : α → β → Prop} [DecidableRel R]
    (hp : Primrec₂ (fun a b => decide (R a b))) : PrimrecRel R :=
  Primrec.primrecPred hp

lemma primrecRel_iff_primrec_decide {R : α → β → Prop} [DecidableRel R] :
    PrimrecRel R ↔ Primrec₂ (fun a b => decide (R a b)) where
  mp := PrimrecRel.decide
  mpr := Primrec₂.primrecRel

theorem PrimrecRel.comp {R : β → γ → Prop} {f : α → β} {g : α → γ}
    (hR : PrimrecRel R) (hf : Primrec f) (hg : Primrec g) : PrimrecPred fun a => R (f a) (g a) :=
  PrimrecPred.comp hR (hf.pair hg)

theorem PrimrecRel.comp₂ {R : γ → δ → Prop} {f : α → β → γ} {g : α → β → δ} :
    PrimrecRel R → Primrec₂ f → Primrec₂ g → PrimrecRel fun a b => R (f a b) (g a b) :=
  PrimrecRel.comp

end Comp

theorem PrimrecPred.of_eq {α} [Primcodable α] {p q : α → Prop}
    (hp : PrimrecPred p) (H : ∀ a, p a ↔ q a) : PrimrecPred q :=
  funext (fun a => propext (H a)) ▸ hp

theorem PrimrecRel.of_eq {α β} [Primcodable α] [Primcodable β] {r s : α → β → Prop}
    (hr : PrimrecRel r) (H : ∀ a b, r a b ↔ s a b) : PrimrecRel s :=
  funext₂ (fun a b => propext (H a b)) ▸ hr

namespace Primrec₂

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

open Nat.Primrec

protected theorem swap {f : α → β → σ} (h : Primrec₂ f) : Primrec₂ (swap f) :=
  h.comp₂ Primrec₂.right Primrec₂.left

protected theorem _root_.PrimrecRel.swap {r : α → β → Prop} (h : PrimrecRel r) :
    PrimrecRel (swap r) :=
  h.comp₂ Primrec₂.right Primrec₂.left

theorem nat_iff {f : α → β → σ} : Primrec₂ f ↔ Nat.Primrec
    (.unpaired fun m n => encode <| (@decode α _ m).bind fun a => (@decode β _ n).map (f a)) := by
  have :
    ∀ (a : Option α) (b : Option β),
      Option.map (fun p : α × β => f p.1 p.2)
          (Option.bind a fun a : α => Option.map (Prod.mk a) b) =
        Option.bind a fun a => Option.map (f a) b := fun a b => by
          cases a <;> cases b <;> rfl
  simp [Primrec₂, Primrec, this]

theorem nat_iff' {f : α → β → σ} :
    Primrec₂ f ↔
      Primrec₂ fun m n : ℕ => (@decode α _ m).bind fun a => Option.map (f a) (@decode β _ n) :=
  nat_iff.trans <| unpaired'.trans encode_iff

end Primrec₂

namespace Primrec

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

theorem to₂ {f : α × β → σ} (hf : Primrec f) : Primrec₂ fun a b => f (a, b) :=
  hf

lemma _root_.PrimrecPred.primrecRel {p : α × β → Prop} (hp : PrimrecPred p) :
    PrimrecRel fun a b => p (a, b) :=
  hp

theorem nat_rec {f : α → β} {g : α → ℕ × β → β} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec₂ fun a (n : ℕ) => n.rec (motive := fun _ => β) (f a) fun n IH => g a (n, IH) :=
  Primrec₂.nat_iff.2 <|
    ((Nat.Primrec.casesOn' .zero <|
              (Nat.Primrec.prec hf <|
                    .comp hg <|
                      Nat.Primrec.left.pair <|
                        (Nat.Primrec.left.comp .right).pair <|
                          Nat.Primrec.pred.comp <| Nat.Primrec.right.comp .right).comp <|
                Nat.Primrec.right.pair <| Nat.Primrec.right.comp Nat.Primrec.left).comp <|
          Nat.Primrec.id.pair <| (Primcodable.prim α).comp Nat.Primrec.left).of_eq
      fun n => by
      simp only [Nat.unpaired, id_eq, Nat.unpair_pair, decode_prod_val, decode_nat,
        Option.bind_some, Option.map_map, Option.map_some]
      rcases @decode α _ n.unpair.1 with - | a; · rfl
      simp only [Nat.pred_eq_sub_one, encode_some, Nat.succ_eq_add_one, encodek, Option.map_some,
        Option.bind_some, Option.map_map]
      induction n.unpair.2 <;> simp [*, encodek]

theorem nat_rec' {f : α → ℕ} {g : α → β} {h : α → ℕ × β → β}
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) :
    Primrec fun a => (f a).rec (motive := fun _ => β) (g a) fun n IH => h a (n, IH) :=
  (nat_rec hg hh).comp .id hf

theorem nat_rec₁ {f : ℕ → α → α} (a : α) (hf : Primrec₂ f) : Primrec (Nat.rec a f) :=
  nat_rec' .id (const a) <| comp₂ hf Primrec₂.right

theorem nat_casesOn' {f : α → β} {g : α → ℕ → β} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec₂ fun a (n : ℕ) => (n.casesOn (f a) (g a) : β) :=
  nat_rec hf <| hg.comp₂ Primrec₂.left <| comp₂ fst Primrec₂.right

theorem nat_casesOn {f : α → ℕ} {g : α → β} {h : α → ℕ → β} (hf : Primrec f) (hg : Primrec g)
    (hh : Primrec₂ h) : Primrec fun a => ((f a).casesOn (g a) (h a) : β) :=
  (nat_casesOn' hg hh).comp .id hf

theorem nat_casesOn₁ {f : ℕ → α} (a : α) (hf : Primrec f) :
    Primrec (fun (n : ℕ) => (n.casesOn a f : α)) :=
  nat_casesOn .id (const a) (comp₂ hf .right)

theorem nat_iterate {f : α → ℕ} {g : α → β} {h : α → β → β} (hf : Primrec f) (hg : Primrec g)
    (hh : Primrec₂ h) : Primrec fun a => (h a)^[f a] (g a) :=
  (nat_rec' hf hg (hh.comp₂ Primrec₂.left <| snd.comp₂ Primrec₂.right)).of_eq fun a => by
    induction f a <;> simp [*, -Function.iterate_succ, Function.iterate_succ']

theorem option_casesOn {o : α → Option β} {f : α → σ} {g : α → β → σ} (ho : Primrec o)
    (hf : Primrec f) (hg : Primrec₂ g) :
    @Primrec _ σ _ _ fun a => Option.casesOn (o a) (f a) (g a) :=
  encode_iff.1 <|
    (nat_casesOn (encode_iff.2 ho) (encode_iff.2 hf) <|
          pred.comp₂ <|
            Primrec₂.encode_iff.2 <|
              (Primrec₂.nat_iff'.1 hg).comp₂ ((@Primrec.encode α _).comp fst).to₂
                Primrec₂.right).of_eq
      fun a => by rcases o a with - | b <;> simp [encodek]

theorem option_bind {f : α → Option β} {g : α → β → Option σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => (f a).bind (g a) :=
  (option_casesOn hf (const none) hg).of_eq fun a => by cases f a <;> rfl

theorem option_bind₁ {f : α → Option σ} (hf : Primrec f) : Primrec fun o => Option.bind o f :=
  option_bind .id (hf.comp snd).to₂

theorem option_map {f : α → Option β} {g : α → β → σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => (f a).map (g a) :=
  (option_bind hf (option_some.comp₂ hg)).of_eq fun x => by cases f x <;> rfl

theorem option_map₁ {f : α → σ} (hf : Primrec f) : Primrec (Option.map f) :=
  option_map .id (hf.comp snd).to₂

theorem option_iget [Inhabited α] : Primrec (@Option.iget α _) :=
  (option_casesOn .id (const <| @default α _) .right).of_eq fun o => by cases o <;> rfl

theorem option_isSome : Primrec (@Option.isSome α) :=
  (option_casesOn .id (const false) (const true).to₂).of_eq fun o => by cases o <;> rfl

theorem option_getD : Primrec₂ (@Option.getD α) :=
  Primrec.of_eq (option_casesOn Primrec₂.left Primrec₂.right .right) fun ⟨o, a⟩ => by
    cases o <;> rfl

theorem bind_decode_iff {f : α → β → Option σ} :
    (Primrec₂ fun a n => (@decode β _ n).bind (f a)) ↔ Primrec₂ f :=
  ⟨fun h => by simpa [encodek] using h.comp fst ((@Primrec.encode β _).comp snd), fun h =>
    option_bind (Primrec.decode.comp snd) <| h.comp (fst.comp fst) snd⟩

theorem map_decode_iff {f : α → β → σ} :
    (Primrec₂ fun a n => (@decode β _ n).map (f a)) ↔ Primrec₂ f := by
  simp only [Option.map_eq_bind]
  exact bind_decode_iff.trans Primrec₂.option_some_iff

theorem nat_add : Primrec₂ ((· + ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.add

theorem nat_sub : Primrec₂ ((· - ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.sub

theorem nat_mul : Primrec₂ ((· * ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.mul

theorem cond {c : α → Bool} {f : α → σ} {g : α → σ} (hc : Primrec c) (hf : Primrec f)
    (hg : Primrec g) : Primrec fun a => bif (c a) then (f a) else (g a) :=
  (nat_casesOn (encode_iff.2 hc) hg (hf.comp fst).to₂).of_eq fun a => by cases c a <;> rfl

theorem ite {c : α → Prop} [DecidablePred c] {f : α → σ} {g : α → σ} (hc : PrimrecPred c)
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => if c a then f a else g a := by
  simpa [Bool.cond_decide] using cond hc.decide hf hg

theorem nat_le : PrimrecRel ((· ≤ ·) : ℕ → ℕ → Prop) :=
  Primrec₂.primrecRel ((nat_casesOn nat_sub (const true) (const false).to₂).of_eq fun p => by
    dsimp [swap]
    rcases e : p.1 - p.2 with - | n
    · simp [Nat.sub_eq_zero_iff_le.1 e]
    · simp [not_le.2 (Nat.lt_of_sub_eq_succ e)])

theorem nat_min : Primrec₂ (@min ℕ _) :=
  ite nat_le fst snd

theorem nat_max : Primrec₂ (@max ℕ _) :=
  ite (nat_le.comp fst snd) snd fst

theorem dom_bool (f : Bool → α) : Primrec f :=
  (cond .id (const (f true)) (const (f false))).of_eq fun b => by cases b <;> rfl

theorem dom_bool₂ (f : Bool → Bool → α) : Primrec₂ f :=
  (cond fst ((dom_bool (f true)).comp snd) ((dom_bool (f false)).comp snd)).of_eq fun ⟨a, b⟩ => by
    cases a <;> rfl

protected theorem not : Primrec not :=
  dom_bool _

protected theorem and : Primrec₂ and :=
  dom_bool₂ _

protected theorem or : Primrec₂ or :=
  dom_bool₂ _

protected theorem _root_.PrimrecPred.not {p : α → Prop} :
    (hp : PrimrecPred p) → PrimrecPred fun a => ¬p a
  | ⟨_, hp⟩ => Primrec.primrecPred <| Primrec.not.comp hp |>.of_eq <| by simp

protected theorem _root_.PrimrecPred.and {p q : α → Prop} :
    (hp : PrimrecPred p) → (hq : PrimrecPred q) → PrimrecPred fun a => p a ∧ q a
  | ⟨_, hp⟩, ⟨_, hq⟩ => Primrec.primrecPred <| Primrec.and.comp hp hq |>.of_eq <| by simp

protected theorem _root_.PrimrecPred.or {p q : α → Prop} :
    (hp : PrimrecPred p) → (hq : PrimrecPred q) → PrimrecPred fun a => p a ∨ q a
  | ⟨_, hp⟩, ⟨_, hq⟩ => Primrec.primrecPred <| Primrec.or.comp hp hq |>.of_eq <| by simp

protected theorem eq : PrimrecRel (@Eq α) :=
  have : PrimrecRel fun a b : ℕ => a = b :=
    (PrimrecPred.and nat_le nat_le.swap).of_eq fun a => by simp [le_antisymm_iff]
  (this.decide.comp₂ (Primrec.encode.comp₂ Primrec₂.left)
      (Primrec.encode.comp₂ Primrec₂.right)).primrecRel.of_eq
    fun _ _ => encode_injective.eq_iff

protected theorem beq [DecidableEq α] : Primrec₂ (@BEq.beq α _) := Primrec.eq.decide

theorem nat_lt : PrimrecRel ((· < ·) : ℕ → ℕ → Prop) :=
  (nat_le.comp snd fst).not.of_eq fun p => by simp

theorem option_guard {p : α → β → Prop} [DecidableRel p] (hp : PrimrecRel p) {f : α → β}
    (hf : Primrec f) : Primrec fun a => Option.guard (p a) (f a) :=
  ite (by simpa using hp.comp Primrec.id hf) (option_some_iff.2 hf) (const none)

theorem option_orElse : Primrec₂ ((· <|> ·) : Option α → Option α → Option α) :=
  (option_casesOn fst snd (fst.comp fst).to₂).of_eq fun ⟨o₁, o₂⟩ => by cases o₁ <;> cases o₂ <;> rfl

protected theorem decode₂ : Primrec (decode₂ α) :=
  option_bind .decode <|
    option_guard (Primrec.eq.comp₂ (by exact encode_iff.mpr snd) (by exact fst.comp fst)) snd

theorem list_findIdx₁ {p : α → β → Bool} (hp : Primrec₂ p) :
    ∀ l : List β, Primrec fun a => l.findIdx (p a)
| [] => const 0
| a :: l => (cond (hp.comp .id (const a)) (const 0) (succ.comp (list_findIdx₁ hp l))).of_eq fun n =>
  by simp [List.findIdx_cons]

theorem list_idxOf₁ [DecidableEq α] (l : List α) : Primrec fun a => l.idxOf a :=
  list_findIdx₁ (.swap .beq) l

theorem dom_finite [Finite α] (f : α → σ) : Primrec f :=
  let ⟨l, _, m⟩ := Finite.exists_univ_list α
  option_some_iff.1 <| by
    haveI := decidableEqOfEncodable α
    refine ((list_getElem?₁ (l.map f)).comp (list_idxOf₁ l)).of_eq fun a => ?_
    rw [List.getElem?_map, List.getElem?_idxOf (m a), Option.map_some]

@[deprecated (since := "2025-08-23")] alias dom_fintype := dom_finite

/-- A function is `PrimrecBounded` if its size is bounded by a primitive recursive function -/
def PrimrecBounded (f : α → β) : Prop :=
  ∃ g : α → ℕ, Primrec g ∧ ∀ x, encode (f x) ≤ g x

theorem nat_findGreatest {f : α → ℕ} {p : α → ℕ → Prop} [DecidableRel p]
    (hf : Primrec f) (hp : PrimrecRel p) : Primrec fun x => (f x).findGreatest (p x) :=
  (nat_rec' (h := fun x nih => if p x (nih.1 + 1) then nih.1 + 1 else nih.2)
    hf (const 0) (ite (hp.comp fst (snd |> fst.comp |> succ.comp))
      (snd |> fst.comp |> succ.comp) (snd.comp snd))).of_eq fun x => by
        induction f x <;> simp [Nat.findGreatest, *]

/-- To show a function `f : α → ℕ` is primitive recursive, it is enough to show that the function
  is bounded by a primitive recursive function and that its graph is primitive recursive -/
theorem of_graph {f : α → ℕ} (h₁ : PrimrecBounded f)
    (h₂ : PrimrecRel fun a b => f a = b) : Primrec f := by
  rcases h₁ with ⟨g, pg, hg : ∀ x, f x ≤ g x⟩
  refine (nat_findGreatest pg h₂).of_eq fun n => ?_
  exact (Nat.findGreatest_spec (P := fun b => f n = b) (hg n) rfl).symm

-- We show that division is primitive recursive by showing that the graph is
theorem nat_div : Primrec₂ ((· / ·) : ℕ → ℕ → ℕ) := by
  refine of_graph ⟨_, fst, fun p => Nat.div_le_self _ _⟩ ?_
  have : PrimrecRel fun (a : ℕ × ℕ) (b : ℕ) => (a.2 = 0 ∧ b = 0) ∨
      (0 < a.2 ∧ b * a.2 ≤ a.1 ∧ a.1 < (b + 1) * a.2) :=
    PrimrecPred.or
      (.and (const 0 |> Primrec.eq.comp (fst |> snd.comp)) (const 0 |> Primrec.eq.comp snd))
      (.and (nat_lt.comp (const 0) (fst |> snd.comp)) <|
          .and (nat_le.comp (nat_mul.comp snd (fst |> snd.comp)) (fst |> fst.comp))
          (nat_lt.comp (fst.comp fst) (nat_mul.comp (Primrec.succ.comp snd) (snd.comp fst))))
  refine this.of_eq ?_
  rintro ⟨a, k⟩ q
  if H : k = 0 then simp [H, eq_comm]
  else
    have : q * k ≤ a ∧ a < (q + 1) * k ↔ q = a / k := by
      rw [le_antisymm_iff, ← (@Nat.lt_succ_iff _ q), Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero H),
          Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero H)]
    simpa [H, zero_lt_iff, eq_comm (b := q)]

theorem nat_mod : Primrec₂ ((· % ·) : ℕ → ℕ → ℕ) :=
  (nat_sub.comp fst (nat_mul.comp snd nat_div)).to₂.of_eq fun m n => by
    apply Nat.sub_eq_of_eq_add
    simp [add_comm (m % n), Nat.div_add_mod]

theorem nat_bodd : Primrec Nat.bodd :=
  (Primrec.beq.comp (nat_mod.comp .id (const 2)) (const 1)).of_eq fun n => by
    cases H : n.bodd <;> simp [Nat.mod_two_of_bodd, H]

theorem nat_div2 : Primrec Nat.div2 :=
  (nat_div.comp .id (const 2)).of_eq fun n => n.div2_val.symm

theorem nat_double : Primrec (fun n : ℕ => 2 * n) :=
  nat_mul.comp (const _) Primrec.id

theorem nat_double_succ : Primrec (fun n : ℕ => 2 * n + 1) :=
  nat_double |> Primrec.succ.comp

end Primrec

section

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]
variable (H : Nat.Primrec fun n => Encodable.encode (@decode (List β) _ n))

open Primrec

private def prim : Primcodable (List β) := ⟨H⟩

private theorem list_casesOn' {f : α → List β} {g : α → σ} {h : α → β × List β → σ}
    (hf : haveI := prim H; Primrec f) (hg : Primrec g) (hh : haveI := prim H; Primrec₂ h) :
    @Primrec _ σ _ _ fun a => List.casesOn (f a) (g a) fun b l => h a (b, l) :=
  letI := prim H
  have :
    @Primrec _ (Option σ) _ _ fun a =>
      (@decode (Option (β × List β)) _ (encode (f a))).map fun o => Option.casesOn o (g a) (h a) :=
    ((@map_decode_iff _ (Option (β × List β)) _ _ _ _ _).2 <|
      to₂ <|
        option_casesOn snd (hg.comp fst) (hh.comp₂ (fst.comp₂ Primrec₂.left) Primrec₂.right)).comp
      .id (encode_iff.2 hf)
  option_some_iff.1 <| this.of_eq fun a => by rcases f a with - | ⟨b, l⟩ <;> simp [encodek]

private theorem list_foldl' {f : α → List β} {g : α → σ} {h : α → σ × β → σ}
    (hf : haveI := prim H; Primrec f) (hg : Primrec g) (hh : haveI := prim H; Primrec₂ h) :
    Primrec fun a => (f a).foldl (fun s b => h a (s, b)) (g a) := by
  letI := prim H
  let G (a : α) (IH : σ × List β) : σ × List β := List.casesOn IH.2 IH fun b l => (h a (IH.1, b), l)
  have hG : Primrec₂ G := list_casesOn' H (snd.comp snd) snd <|
    to₂ <|
    pair (hh.comp (fst.comp fst) <| pair ((fst.comp snd).comp fst) (fst.comp snd))
      (snd.comp snd)
  let F := fun (a : α) (n : ℕ) => (G a)^[n] (g a, f a)
  have hF : Primrec fun a => (F a (encode (f a))).1 :=
    (fst.comp <|
      nat_iterate (encode_iff.2 hf) (pair hg hf) <|
      hG)
  suffices ∀ a n, F a n = (((f a).take n).foldl (fun s b => h a (s, b)) (g a), (f a).drop n) by
    refine hF.of_eq fun a => ?_
    rw [this, List.take_of_length_le (length_le_encode _)]
  introv
  dsimp only [F]
  generalize f a = l
  generalize g a = x
  induction n generalizing l x with
  | zero => rfl
  | succ n IH =>
    simp only [iterate_succ, comp_apply]
    rcases l with - | ⟨b, l⟩ <;> simp [G, IH]

private theorem list_cons' : (haveI := prim H; Primrec₂ (@List.cons β)) :=
  letI := prim H
  encode_iff.1 (succ.comp <| Primrec₂.natPair.comp (encode_iff.2 fst) (encode_iff.2 snd))

private theorem list_reverse' :
    haveI := prim H
    Primrec (@List.reverse β) :=
  letI := prim H
  (list_foldl' H .id (const []) <| to₂ <| ((list_cons' H).comp snd fst).comp snd).of_eq
    (suffices ∀ l r, List.foldl (fun (s : List β) (b : β) => b :: s) r l = List.reverseAux l r from
      fun l => this l []
    fun l => by induction l <;> simp [*, List.reverseAux])

end

namespace Primcodable

variable {α : Type*} {β : Type*}
variable [Primcodable α] [Primcodable β]

open Primrec

instance sum : Primcodable (α ⊕ β) :=
  ⟨Primrec.nat_iff.1 <|
      (encode_iff.2
            (cond nat_bodd
              (((@Primrec.decode β _).comp nat_div2).option_map <|
                to₂ <| nat_double_succ.comp (Primrec.encode.comp snd))
              (((@Primrec.decode α _).comp nat_div2).option_map <|
                to₂ <| nat_double.comp (Primrec.encode.comp snd)))).of_eq
        fun n =>
        show _ = encode (decodeSum n) by
          simp only [decodeSum, Nat.boddDiv2_eq]
          cases Nat.bodd n <;> simp
          · cases @decode α _ n.div2 <;> rfl
          · cases @decode β _ n.div2 <;> rfl⟩

instance list : Primcodable (List α) :=
  ⟨letI H := Primcodable.prim (List ℕ)
    have : Primrec₂ fun (a : α) (o : Option (List ℕ)) => o.map (List.cons (encode a)) :=
      option_map snd <| (list_cons' H).comp ((@Primrec.encode α _).comp (fst.comp fst)) snd
    have :
      Primrec fun n =>
        (ofNat (List ℕ) n).reverse.foldl
          (fun o m => (@decode α _ m).bind fun a => o.map (List.cons (encode a))) (some []) :=
      list_foldl' H ((list_reverse' H).comp (.ofNat (List ℕ))) (const (some []))
        (Primrec.comp₂ (bind_decode_iff.2 <| .swap this) Primrec₂.right)
    nat_iff.1 <|
      (encode_iff.2 this).of_eq fun n => by
        rw [List.foldl_reverse]
        apply Nat.case_strong_induction_on n; · simp
        intro n IH; simp
        rcases @decode α _ n.unpair.1 with - | a; · rfl
        simp only [Option.bind_some, Option.map_some]
        suffices ∀ (o : Option (List ℕ)) (p), encode o = encode p →
            encode (Option.map (List.cons (encode a)) o) = encode (Option.map (List.cons a) p) from
          this _ _ (IH _ (Nat.unpair_right_le n))
        intro o p IH
        cases o <;> cases p
        · rfl
        · injection IH
        · injection IH
        · exact congr_arg (fun k => (Nat.pair (encode a) k).succ.succ) (Nat.succ.inj IH)⟩
end Primcodable

namespace Primrec

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

theorem sumInl : Primrec (@Sum.inl α β) :=
  encode_iff.1 <| nat_double.comp Primrec.encode

theorem sumInr : Primrec (@Sum.inr α β) :=
  encode_iff.1 <| nat_double_succ.comp Primrec.encode

theorem sumCasesOn {f : α → β ⊕ γ} {g : α → β → σ} {h : α → γ → σ} (hf : Primrec f)
    (hg : Primrec₂ g) (hh : Primrec₂ h) : @Primrec _ σ _ _ fun a => Sum.casesOn (f a) (g a) (h a) :=
  option_some_iff.1 <|
    (cond (nat_bodd.comp <| encode_iff.2 hf)
          (option_map (Primrec.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hh)
          (option_map (Primrec.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hg)).of_eq
      fun a => by rcases f a with b | c <;> simp [Nat.div2_val, encodek]

theorem list_cons : Primrec₂ (@List.cons α) :=
  list_cons' (Primcodable.prim _)

theorem list_casesOn {f : α → List β} {g : α → σ} {h : α → β × List β → σ} :
    Primrec f →
      Primrec g →
        Primrec₂ h → @Primrec _ σ _ _ fun a => List.casesOn (f a) (g a) fun b l => h a (b, l) :=
  list_casesOn' (Primcodable.prim _)

theorem list_foldl {f : α → List β} {g : α → σ} {h : α → σ × β → σ} :
    Primrec f →
      Primrec g → Primrec₂ h → Primrec fun a => (f a).foldl (fun s b => h a (s, b)) (g a) :=
  list_foldl' (Primcodable.prim _)

theorem list_reverse : Primrec (@List.reverse α) :=
  list_reverse' (Primcodable.prim _)

theorem list_foldr {f : α → List β} {g : α → σ} {h : α → β × σ → σ} (hf : Primrec f)
    (hg : Primrec g) (hh : Primrec₂ h) :
    Primrec fun a => (f a).foldr (fun b s => h a (b, s)) (g a) :=
  (list_foldl (list_reverse.comp hf) hg <| to₂ <| hh.comp fst <| (pair snd fst).comp snd).of_eq
    fun a => by simp [List.foldl_reverse]

theorem list_head? : Primrec (@List.head? α) :=
  (list_casesOn .id (const none) (option_some_iff.2 <| fst.comp snd).to₂).of_eq fun l => by
    cases l <;> rfl

theorem list_headI [Inhabited α] : Primrec (@List.headI α _) :=
  (option_iget.comp list_head?).of_eq fun l => l.head!_eq_head?.symm

theorem list_tail : Primrec (@List.tail α) :=
  (list_casesOn .id (const []) (snd.comp snd).to₂).of_eq fun l => by cases l <;> rfl

theorem list_rec {f : α → List β} {g : α → σ} {h : α → β × List β × σ → σ} (hf : Primrec f)
    (hg : Primrec g) (hh : Primrec₂ h) :
    @Primrec _ σ _ _ fun a => List.recOn (f a) (g a) fun b l IH => h a (b, l, IH) :=
  let F (a : α) := (f a).foldr (fun (b : β) (s : List β × σ) => (b :: s.1, h a (b, s))) ([], g a)
  have : Primrec F :=
    list_foldr hf (pair (const []) hg) <|
      to₂ <| pair ((list_cons.comp fst (fst.comp snd)).comp snd) hh
  (snd.comp this).of_eq fun a => by
    suffices F a = (f a, List.recOn (f a) (g a) fun b l IH => h a (b, l, IH)) by rw [this]
    dsimp [F]
    induction f a <;> simp [*]

theorem list_getElem? : Primrec₂ ((·[·]? : List α → ℕ → Option α)) :=
  let F (l : List α) (n : ℕ) :=
    l.foldl
      (fun (s : ℕ ⊕ α) (a : α) =>
        Sum.casesOn s (@Nat.casesOn (fun _ => ℕ ⊕ α) · (Sum.inr a) Sum.inl) Sum.inr)
      (Sum.inl n)
  have hF : Primrec₂ F :=
    (list_foldl fst (sumInl.comp snd)
      ((sumCasesOn fst (nat_casesOn snd (sumInr.comp <| snd.comp fst) (sumInl.comp snd).to₂).to₂
              (sumInr.comp snd).to₂).comp
          snd).to₂).to₂
  have :
    @Primrec _ (Option α) _ _ fun p : List α × ℕ => Sum.casesOn (F p.1 p.2) (fun _ => none) some :=
    sumCasesOn hF (const none).to₂ (option_some.comp snd).to₂
  this.to₂.of_eq fun l n => by
    dsimp; symm
    induction l generalizing n with
    | nil => rfl
    | cons a l IH =>
      rcases n with - | n
      · dsimp [F]
        clear IH
        induction l <;> simp_all
      · simpa using IH ..

theorem list_getD (d : α) : Primrec₂ fun l n => List.getD l n d := by
  simp only [List.getD_eq_getElem?_getD]
  exact option_getD.comp₂ list_getElem? (const _)

theorem list_getI [Inhabited α] : Primrec₂ (@List.getI α _) :=
  list_getD _

theorem list_append : Primrec₂ ((· ++ ·) : List α → List α → List α) :=
  (list_foldr fst snd <| to₂ <| comp (@list_cons α _) snd).to₂.of_eq fun l₁ l₂ => by
    induction l₁ <;> simp [*]

theorem list_concat : Primrec₂ fun l (a : α) => l ++ [a] :=
  list_append.comp fst (list_cons.comp snd (const []))

theorem list_map {f : α → List β} {g : α → β → σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => (f a).map (g a) :=
  (list_foldr hf (const []) <|
        to₂ <| list_cons.comp (hg.comp fst (fst.comp snd)) (snd.comp snd)).of_eq
    fun a => by induction f a <;> simp [*]

theorem list_range : Primrec List.range :=
  (nat_rec' .id (const []) ((list_concat.comp snd fst).comp snd).to₂).of_eq fun n => by
    simp; induction n <;> simp [*, List.range_succ]

theorem list_flatten : Primrec (@List.flatten α) :=
  (list_foldr .id (const []) <| to₂ <| comp (@list_append α _) snd).of_eq fun l => by
    dsimp; induction l <;> simp [*]

theorem list_flatMap {f : α → List β} {g : α → β → List σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun a => (f a).flatMap (g a)) := list_flatten.comp (list_map hf hg)

theorem optionToList : Primrec (Option.toList : Option α → List α) :=
  (option_casesOn Primrec.id (const [])
    ((list_cons.comp Primrec.id (const [])).comp₂ Primrec₂.right)).of_eq
  (fun o => by rcases o <;> simp)

theorem listFilterMap {f : α → List β} {g : α → β → Option σ}
    (hf : Primrec f) (hg : Primrec₂ g) : Primrec fun a => (f a).filterMap (g a) :=
  (list_flatMap hf (comp₂ optionToList hg)).of_eq
    fun _ ↦ Eq.symm <| List.filterMap_eq_flatMap_toList _ _

variable {p : α → Prop} [DecidablePred p]

theorem list_length : Primrec (@List.length α) :=
  (list_foldr (@Primrec.id (List α) _) (const 0) <| to₂ <| (succ.comp <| snd.comp snd).to₂).of_eq
    fun l => by dsimp; induction l <;> simp [*]

/-- Filtering a list for elements that satisfy a decidable predicate is primitive recursive. -/
theorem listFilter (hf : PrimrecPred p) : Primrec fun L ↦ List.filter (p ·) L := by
  rw [← List.filterMap_eq_filter]
  apply listFilterMap .id
  simp only [Primrec₂, Option.guard, decide_eq_true_eq]
  exact ite (hf.comp snd) (option_some_iff.mpr snd) (const none)

theorem list_findIdx {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) : Primrec fun a => (f a).findIdx (p a) :=
  (list_foldr hf (const 0) <|
        to₂ <| cond (hp.comp fst <| fst.comp snd) (const 0) (succ.comp <| snd.comp snd)).of_eq
    fun a => by dsimp; induction f a <;> simp [List.findIdx_cons, *]

theorem list_idxOf [DecidableEq α] : Primrec₂ (@List.idxOf α _) :=
  to₂ <| list_findIdx snd <| Primrec.beq.comp₂ snd.to₂ (fst.comp fst).to₂

theorem nat_strong_rec (f : α → ℕ → σ) {g : α → List σ → Option σ} (hg : Primrec₂ g)
    (H : ∀ a n, g a ((List.range n).map (f a)) = some (f a n)) : Primrec₂ f :=
  suffices Primrec₂ fun a n => (List.range n).map (f a) from
    Primrec₂.option_some_iff.1 <|
      (list_getElem?.comp (this.comp fst (succ.comp snd)) snd).to₂.of_eq fun a n => by
        simp
  Primrec₂.option_some_iff.1 <|
    (nat_rec (const (some []))
          (to₂ <|
            option_bind (snd.comp snd) <|
              to₂ <|
                option_map (hg.comp (fst.comp fst) snd)
                  (to₂ <| list_concat.comp (snd.comp fst) snd))).of_eq
      fun a n => by
      induction n with
      | zero => rfl
      | succ n IH => simp [IH, H, List.range_succ]

theorem listLookup [DecidableEq α] : Primrec₂ (List.lookup : α → List (α × β) → Option β) :=
  (to₂ <| list_rec snd (const none) <|
    to₂ <|
      cond (Primrec.beq.comp (fst.comp fst) (fst.comp <| fst.comp snd))
        (option_some.comp <| snd.comp <| fst.comp snd)
        (snd.comp <| snd.comp snd)).of_eq
  fun a ps => by
  induction ps with simp [List.lookup, *]
  | cons p ps ih => cases ha : a == p.1 <;> simp

theorem nat_omega_rec' (f : β → σ) {m : β → ℕ} {l : β → List β} {g : β → List σ → Option σ}
    (hm : Primrec m) (hl : Primrec l) (hg : Primrec₂ g)
    (Ord : ∀ b, ∀ b' ∈ l b, m b' < m b)
    (H : ∀ b, g b ((l b).map f) = some (f b)) : Primrec f := by
  haveI : DecidableEq β := Encodable.decidableEqOfEncodable β
  let mapGraph (M : List (β × σ)) (bs : List β) : List σ := bs.flatMap (Option.toList <| M.lookup ·)
  let bindList (b : β) : ℕ → List β := fun n ↦ n.rec [b] fun _ bs ↦ bs.flatMap l
  let graph (b : β) : ℕ → List (β × σ) := fun i ↦ i.rec [] fun i ih ↦
    (bindList b (m b - i)).filterMap fun b' ↦ (g b' <| mapGraph ih (l b')).map (b', ·)
  have mapGraph_primrec : Primrec₂ mapGraph :=
    to₂ <| list_flatMap snd <| optionToList.comp₂ <| listLookup.comp₂ .right (fst.comp₂ .left)
  have bindList_primrec : Primrec₂ (bindList) :=
    nat_rec' snd
      (list_cons.comp fst (const []))
      (to₂ <| list_flatMap (snd.comp snd) (hl.comp₂ .right))
  have graph_primrec : Primrec₂ (graph) :=
    to₂ <| nat_rec' snd (const []) <|
      to₂ <| listFilterMap
        (bindList_primrec.comp
          (fst.comp fst)
          (nat_sub.comp (hm.comp <| fst.comp fst) (fst.comp snd))) <|
            to₂ <| option_map
              (hg.comp snd (mapGraph_primrec.comp (snd.comp <| snd.comp fst) (hl.comp snd)))
              (Primrec₂.pair.comp₂ (snd.comp₂ .left) .right)
  have : Primrec (fun b => (graph b (m b + 1))[0]?.map Prod.snd) :=
    option_map (list_getElem?.comp (graph_primrec.comp Primrec.id (succ.comp hm)) (const 0))
      (snd.comp₂ Primrec₂.right)
  exact option_some_iff.mp <| this.of_eq <| fun b ↦ by
    have graph_eq_map_bindList (i : ℕ) (hi : i ≤ m b + 1) :
        graph b i = (bindList b (m b + 1 - i)).map fun x ↦ (x, f x) := by
      have bindList_eq_nil : bindList b (m b + 1) = [] :=
        have bindList_m_lt (k : ℕ) : ∀ b' ∈ bindList b k, m b' < m b + 1 - k := by
          induction k with simp [bindList]
          | succ k ih =>
            grind
        List.eq_nil_iff_forall_not_mem.mpr
          (by intro b' ha'; by_contra; simpa using bindList_m_lt (m b + 1) b' ha')
      have mapGraph_graph {bs bs' : List β} (has : bs' ⊆ bs) :
          mapGraph (bs.map <| fun x => (x, f x)) bs' = bs'.map f := by
        induction bs' with simp [mapGraph]
        | cons b bs' ih =>
          have : b ∈ bs ∧ bs' ⊆ bs := by simpa using has
          rcases this with ⟨ha, has'⟩
          simpa [List.lookup_graph f ha] using ih has'
      have graph_succ : ∀ i, graph b (i + 1) =
        (bindList b (m b - i)).filterMap fun b' =>
          (g b' <| mapGraph (graph b i) (l b')).map (b', ·) := fun _ => rfl
      have bindList_succ : ∀ i, bindList b (i + 1) = (bindList b i).flatMap l := fun _ => rfl
      induction i with
      | zero => symm; simpa [graph] using bindList_eq_nil
      | succ i ih =>
        simp only [graph_succ, ih (Nat.le_of_lt hi), Nat.succ_sub (Nat.lt_succ_iff.mp hi),
          Nat.succ_eq_add_one, bindList_succ, Nat.reduceSubDiff]
        apply List.filterMap_eq_map_iff_forall_eq_some.mpr
        intro b' ha'; simp; rw [mapGraph_graph]
        · exact H b'
        · exact (List.infix_flatMap_of_mem ha' l).subset
    simp [graph_eq_map_bindList (m b + 1) (Nat.le_refl _), bindList]

theorem nat_omega_rec (f : α → β → σ) {m : α → β → ℕ}
    {l : α → β → List β} {g : α → β × List σ → Option σ}
    (hm : Primrec₂ m) (hl : Primrec₂ l) (hg : Primrec₂ g)
    (Ord : ∀ a b, ∀ b' ∈ l a b, m a b' < m a b)
    (H : ∀ a b, g a (b, (l a b).map (f a)) = some (f a b)) : Primrec₂ f :=
  Primrec₂.uncurry.mp <|
    nat_omega_rec' (Function.uncurry f)
      (Primrec₂.uncurry.mpr hm)
      (list_map (hl.comp fst snd) (Primrec₂.pair.comp₂ (fst.comp₂ .left) .right))
      (hg.comp₂ (fst.comp₂ .left) (Primrec₂.pair.comp₂ (snd.comp₂ .left) .right))
      (by simpa using Ord) (by simpa [Function.comp] using H)

end Primrec

namespace PrimrecPred

open List Primrec

variable {α β : Type*} {p : α → Prop} {L : List α} {b : β}

variable [Primcodable α] [Primcodable β]

/-- Checking if any element of a list satisfies a decidable predicate is primitive recursive. -/
theorem exists_mem_list : (hf : PrimrecPred p) → PrimrecPred fun L : List α ↦ ∃ a ∈ L, p a
  | ⟨_, hf⟩ => .of_eq
      (.not <| Primrec.eq.comp (list_length.comp <| listFilter hf.primrecPred) (const 0)) <| by simp

/-- Checking if every element of a list satisfies a decidable predicate is primitive recursive. -/
theorem forall_mem_list : (hf : PrimrecPred p) → PrimrecPred fun L : List α ↦ ∀ a ∈ L, p a
  | ⟨_, hf⟩ => .of_eq
      (Primrec.eq.comp (list_length.comp <| listFilter hf.primrecPred) (list_length)) <| by simp

variable {p : ℕ → Prop}

/-- Bounded existential quantifiers are primitive recursive. -/
theorem exists_lt (hf : PrimrecPred p) : PrimrecPred fun n ↦ ∃ x < n, p x :=
  of_eq (hf.exists_mem_list.comp list_range) (by simp)

/-- Bounded universal quantifiers are primitive recursive. -/
theorem forall_lt (hf : PrimrecPred p) : PrimrecPred fun n ↦ ∀ x < n, p x :=
  of_eq (hf.forall_mem_list.comp list_range) (by simp)

/-- A helper lemma for proofs about bounded quantifiers on decidable relations. -/
theorem listFilter_listRange {R : ℕ → ℕ → Prop} (s : ℕ) [DecidableRel R] (hf : PrimrecRel R) :
    Primrec fun n ↦ (range s).filter (fun y ↦ R y n) := by
  simp only [← filterMap_eq_filter]
  refine listFilterMap (.const (range s)) ?_
  refine ite (Primrec.eq.comp ?_ (const true)) (option_some_iff.mpr snd) (.const Option.none)
  exact hf.decide.comp snd fst

end PrimrecPred

namespace PrimrecRel

open Primrec List PrimrecPred

variable {α β : Type*} {R : α → β → Prop} {L : List α} {b : β}

variable [Primcodable α] [Primcodable β]

protected theorem not (hf : PrimrecRel R) : PrimrecRel fun a b ↦ ¬ R a b := PrimrecPred.not hf

/-- If `R a b` is decidable, then given `L : List α` and `b : β`, it is primitive recursive
to filter `L` for elements `a` with `R a b` -/
theorem listFilter (hf : PrimrecRel R) [DecidableRel R] :
    Primrec₂ fun (L : List α) b ↦ L.filter (fun a ↦ R a b) := by
  simp only [← List.filterMap_eq_filter]
  refine listFilterMap fst (Primrec.ite ?_ ?_ (Primrec.const Option.none))
  · exact Primrec.eq.comp (hf.decide.comp snd (snd.comp fst)) (.const true)
  · exact (option_some).comp snd

/-- If `R a b` is decidable, then given `L : List α` and `b : β`, `g L b ↔ ∃ a L, R a b`
is a primitive recursive relation. -/
theorem exists_mem_list (hf : PrimrecRel R) : PrimrecRel fun (L : List α) b ↦ ∃ a ∈ L, R a b := by
  classical
  have h (L) (b) : (List.filter (R · b) L).length ≠ 0 ↔ ∃ a ∈ L, R a b := by simp
  refine .of_eq (.not ?_) h
  exact Primrec.eq.comp (list_length.comp hf.listFilter) (const 0)

/-- If `R a b` is decidable, then given `L : List α` and `b : β`, `g L b ↔ ∀ a L, R a b`
is a primitive recursive relation. -/
theorem forall_mem_list (hf : PrimrecRel R) : PrimrecRel fun (L : List α) b ↦ ∀ a ∈ L, R a b := by
  classical
  have h (L) (b) : (List.filter (R · b) L).length = L.length ↔ ∀ a ∈ L, R a b := by simp
  apply PrimrecRel.of_eq ?_ h
  exact (Primrec.eq.comp (list_length.comp <| PrimrecRel.listFilter hf) (.comp list_length fst))

variable {R : ℕ → ℕ → Prop}

/-- If `R a b` is decidable, then for any fixed `n` and `y`, `g n y ↔ ∃ x < n, R x y` is a
primitive recursive relation. -/
theorem exists_lt (hf : PrimrecRel R) : PrimrecRel fun n y ↦ ∃ x < n, R x y :=
  (hf.exists_mem_list.comp (list_range.comp fst) snd).of_eq (by simp)

/-- If `R a b` is decidable, then for any fixed `n` and `y`, `g n y ↔ ∀ x < n, R x y` is a
primitive recursive relation. -/
theorem forall_lt (hf : PrimrecRel R) : PrimrecRel fun n y ↦ ∀ x < n, R x y :=
  (hf.forall_mem_list.comp (list_range.comp fst) snd).of_eq (by simp)

end PrimrecRel

namespace Primcodable

variable {α : Type*} [Primcodable α]

open Primrec

/-- A subtype of a primitive recursive predicate is `Primcodable`. -/
def subtype {p : α → Prop} [DecidablePred p] (hp : PrimrecPred p) : Primcodable (Subtype p) :=
  ⟨have : Primrec fun n => (@decode α _ n).bind fun a => Option.guard p a :=
    option_bind .decode (option_guard (hp.comp snd).primrecRel snd)
  nat_iff.1 <| (encode_iff.2 this).of_eq fun n =>
    show _ = encode ((@decode α _ n).bind fun _ => _) by
      rcases @decode α _ n with - | a; · rfl
      dsimp [Option.guard]
      by_cases h : p a <;> simp [h]; rfl⟩

instance fin {n} : Primcodable (Fin n) :=
  @ofEquiv _ _ (subtype <| nat_lt.comp .id (const n)) Fin.equivSubtype

instance vector {n} : Primcodable (List.Vector α n) :=
  subtype ((@Primrec.eq ℕ _).comp list_length (const _))

instance finArrow {n} : Primcodable (Fin n → α) :=
  ofEquiv _ (Equiv.vectorEquivFin _ _).symm

section ULower

attribute [local instance] Encodable.decidableRangeEncode Encodable.decidableEqOfEncodable

theorem mem_range_encode : PrimrecPred (fun n => n ∈ Set.range (encode : α → ℕ)) :=
  have : PrimrecPred fun n => Encodable.decode₂ α n ≠ none :=
    .not
      (Primrec.eq.comp
        (.option_bind .decode
          (.ite (by simpa using Primrec.eq.comp (Primrec.encode.comp .snd) .fst)
            (Primrec.option_some.comp .snd) (.const _)))
        (.const _))
  this.of_eq fun _ => decode₂_ne_none_iff

instance ulower : Primcodable (ULower α) :=
  Primcodable.subtype mem_range_encode

end ULower

end Primcodable

namespace Primrec

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

theorem subtype_val {p : α → Prop} [DecidablePred p] {hp : PrimrecPred p} :
    haveI := Primcodable.subtype hp
    Primrec (@Subtype.val α p) := by
  letI := Primcodable.subtype hp
  refine (Primcodable.prim (Subtype p)).of_eq fun n => ?_
  rcases @decode (Subtype p) _ n with (_ | ⟨a, h⟩) <;> rfl

theorem subtype_val_iff {p : β → Prop} [DecidablePred p] {hp : PrimrecPred p} {f : α → Subtype p} :
    haveI := Primcodable.subtype hp
    (Primrec fun a => (f a).1) ↔ Primrec f := by
  letI := Primcodable.subtype hp
  refine ⟨fun h => ?_, fun hf => subtype_val.comp hf⟩
  refine Nat.Primrec.of_eq h fun n => ?_
  rcases @decode α _ n with - | a; · rfl
  simp; rfl

theorem subtype_mk {p : β → Prop} [DecidablePred p] {hp : PrimrecPred p} {f : α → β}
    {h : ∀ a, p (f a)} (hf : Primrec f) :
    haveI := Primcodable.subtype hp
    Primrec fun a => @Subtype.mk β p (f a) (h a) :=
  subtype_val_iff.1 hf

theorem option_get {f : α → Option β} {h : ∀ a, (f a).isSome} :
    Primrec f → Primrec fun a => (f a).get (h a) := by
  intro hf
  refine (Nat.Primrec.pred.comp hf).of_eq fun n => ?_
  generalize hx : @decode α _ n = x
  cases x <;> simp

theorem ulower_down : Primrec (ULower.down : α → ULower α) :=
  letI : ∀ a, Decidable (a ∈ Set.range (encode : α → ℕ)) := decidableRangeEncode _
  subtype_mk .encode

theorem ulower_up : Primrec (ULower.up : ULower α → α) :=
  letI : ∀ a, Decidable (a ∈ Set.range (encode : α → ℕ)) := decidableRangeEncode _
  option_get (Primrec.decode₂.comp subtype_val)

theorem fin_val_iff {n} {f : α → Fin n} : (Primrec fun a => (f a).1) ↔ Primrec f := by
  letI : Primcodable { a // id a < n } := Primcodable.subtype (nat_lt.comp .id (const _))
  exact (Iff.trans (by rfl) subtype_val_iff).trans (of_equiv_iff _)

theorem fin_val {n} : Primrec (fun (i : Fin n) => (i : ℕ)) :=
  fin_val_iff.2 .id

theorem fin_succ {n} : Primrec (@Fin.succ n) :=
  fin_val_iff.1 <| by simp [succ.comp fin_val]

theorem vector_toList {n} : Primrec (@List.Vector.toList α n) :=
  subtype_val

theorem vector_toList_iff {n} {f : α → List.Vector β n} :
    (Primrec fun a => (f a).toList) ↔ Primrec f :=
  subtype_val_iff

theorem vector_cons {n} : Primrec₂ (@List.Vector.cons α n) :=
  vector_toList_iff.1 <| by simpa using list_cons.comp fst (vector_toList_iff.2 snd)

theorem vector_length {n} : Primrec (@List.Vector.length α n) :=
  const _

theorem vector_head {n} : Primrec (@List.Vector.head α n) :=
  option_some_iff.1 <| (list_head?.comp vector_toList).of_eq fun ⟨_ :: _, _⟩ => rfl

theorem vector_tail {n} : Primrec (@List.Vector.tail α n) :=
  vector_toList_iff.1 <| (list_tail.comp vector_toList).of_eq fun ⟨l, h⟩ => by cases l <;> rfl

theorem vector_get {n} : Primrec₂ (@List.Vector.get α n) :=
  option_some_iff.1 <|
    (list_getElem?.comp (vector_toList.comp fst) (fin_val.comp snd)).of_eq fun a => by
      simp [Vector.get_eq_get_toList]

theorem list_ofFn :
    ∀ {n} {f : Fin n → α → σ}, (∀ i, Primrec (f i)) → Primrec fun a => List.ofFn fun i => f i a
  | 0, _, _ => by simp only [List.ofFn_zero]; exact const []
  | n + 1, f, hf => by
    simpa using list_cons.comp (hf 0) (list_ofFn fun i => hf i.succ)

theorem vector_ofFn {n} {f : Fin n → α → σ} (hf : ∀ i, Primrec (f i)) :
    Primrec fun a => List.Vector.ofFn fun i => f i a :=
  vector_toList_iff.1 <| by simp [list_ofFn hf]

theorem vector_get' {n} : Primrec (@List.Vector.get α n) :=
  of_equiv_symm

theorem vector_ofFn' {n} : Primrec (@List.Vector.ofFn α n) :=
  of_equiv

theorem fin_app {n} : Primrec₂ (@id (Fin n → σ)) :=
  (vector_get.comp (vector_ofFn'.comp fst) snd).of_eq fun ⟨v, i⟩ => by simp

theorem fin_curry₁ {n} {f : Fin n → α → σ} : Primrec₂ f ↔ ∀ i, Primrec (f i) :=
  ⟨fun h i => h.comp (const i) .id, fun h =>
    (vector_get.comp ((vector_ofFn h).comp snd) fst).of_eq fun a => by simp⟩

theorem fin_curry {n} {f : α → Fin n → σ} : Primrec f ↔ Primrec₂ f :=
  ⟨fun h => fin_app.comp (h.comp fst) snd, fun h =>
    (vector_get'.comp
          (vector_ofFn fun i => show Primrec fun a => f a i from h.comp .id (const i))).of_eq
      fun a => by funext i; simp⟩

end Primrec

namespace Nat

open List.Vector

/-- An alternative inductive definition of `Primrec` which
  does not use the pairing function on ℕ, and so has to
  work with n-ary functions on ℕ instead of unary functions.
  We prove that this is equivalent to the regular notion
  in `to_prim` and `of_prim`. -/
inductive Primrec' : ∀ {n}, (List.Vector ℕ n → ℕ) → Prop
  | zero : @Primrec' 0 fun _ => 0
  | succ : @Primrec' 1 fun v => succ v.head
  | get {n} (i : Fin n) : Primrec' fun v => v.get i
  | comp {m n f} (g : Fin n → List.Vector ℕ m → ℕ) :
      Primrec' f → (∀ i, Primrec' (g i)) → Primrec' fun a => f (List.Vector.ofFn fun i => g i a)
  | prec {n f g} :
      @Primrec' n f →
        @Primrec' (n + 2) g →
          Primrec' fun v : List.Vector ℕ (n + 1) =>
            v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)

end Nat

namespace Nat.Primrec'

open List.Vector Primrec

theorem to_prim {n f} (pf : @Nat.Primrec' n f) : Primrec f := by
  induction pf with
  | zero => exact .const 0
  | succ => exact _root_.Primrec.succ.comp .vector_head
  | get i => exact Primrec.vector_get.comp .id (.const i)
  | comp _ _ _ hf hg => exact hf.comp (.vector_ofFn fun i => hg i)
  | @prec n f g _ _ hf hg =>
    exact
      .nat_rec' .vector_head (hf.comp Primrec.vector_tail)
        (hg.comp <|
          Primrec.vector_cons.comp (Primrec.fst.comp .snd) <|
          Primrec.vector_cons.comp (Primrec.snd.comp .snd) <|
            (@Primrec.vector_tail _ _ (n + 1)).comp .fst).to₂

theorem of_eq {n} {f g : List.Vector ℕ n → ℕ} (hf : Primrec' f) (H : ∀ i, f i = g i) :
    Primrec' g :=
  (funext H : f = g) ▸ hf

theorem const {n} : ∀ m, @Primrec' n fun _ => m
  | 0 => zero.comp Fin.elim0 fun i => i.elim0
  | m + 1 => succ.comp _ fun _ => const m

theorem head {n : ℕ} : @Primrec' n.succ head :=
  (get 0).of_eq fun v => by simp [get_zero]

theorem tail {n f} (hf : @Primrec' n f) : @Primrec' n.succ fun v => f v.tail :=
  (hf.comp _ fun i => @get _ i.succ).of_eq fun v => by
    rw [← ofFn_get v.tail]; congr; funext i; simp

/-- A function from vectors to vectors is primitive recursive when all of its projections are. -/
def Vec {n m} (f : List.Vector ℕ n → List.Vector ℕ m) : Prop :=
  ∀ i, Primrec' fun v => (f v).get i

protected theorem nil {n} : @Vec n 0 fun _ => nil := fun i => i.elim0

protected theorem cons {n m f g} (hf : @Primrec' n f) (hg : @Vec n m g) :
    Vec fun v => f v ::ᵥ g v := fun i => Fin.cases (by simp [*]) (fun i => by simp [hg i]) i

theorem idv {n} : @Vec n n id :=
  get

theorem comp' {n m f g} (hf : @Primrec' m f) (hg : @Vec n m g) : Primrec' fun v => f (g v) :=
  (hf.comp _ hg).of_eq fun v => by simp

theorem comp₁ (f : ℕ → ℕ) (hf : @Primrec' 1 fun v => f v.head) {n g} (hg : @Primrec' n g) :
    Primrec' fun v => f (g v) :=
  hf.comp _ fun _ => hg

theorem comp₂ (f : ℕ → ℕ → ℕ) (hf : @Primrec' 2 fun v => f v.head v.tail.head) {n g h}
    (hg : @Primrec' n g) (hh : @Primrec' n h) : Primrec' fun v => f (g v) (h v) := by
  simpa using hf.comp' (hg.cons <| hh.cons Primrec'.nil)

theorem prec' {n f g h} (hf : @Primrec' n f) (hg : @Primrec' n g) (hh : @Primrec' (n + 2) h) :
    @Primrec' n fun v => (f v).rec (g v) fun y IH : ℕ => h (y ::ᵥ IH ::ᵥ v) := by
  simpa using comp' (prec hg hh) (hf.cons idv)

theorem pred : @Primrec' 1 fun v => v.head.pred :=
  (prec' head (const 0) head).of_eq fun v => by simp; cases v.head <;> rfl

theorem add : @Primrec' 2 fun v => v.head + v.tail.head :=
  (prec head (succ.comp₁ _ (tail head))).of_eq fun v => by
    simp; induction v.head <;> simp [*, Nat.succ_add]

theorem sub : @Primrec' 2 fun v => v.head - v.tail.head := by
  have : @Primrec' 2 fun v ↦ (fun a b ↦ b - a) v.head v.tail.head := by
    refine (prec head (pred.comp₁ _ (tail head))).of_eq fun v => ?_
    simp; induction v.head <;> simp [*, Nat.sub_add_eq]
  simpa using comp₂ (fun a b => b - a) this (tail head) head

theorem mul : @Primrec' 2 fun v => v.head * v.tail.head :=
  (prec (const 0) (tail (add.comp₂ _ (tail head) head))).of_eq fun v => by
    simp; induction v.head <;> simp [*, Nat.succ_mul]; rw [add_comm]

theorem if_lt {n a b f g} (ha : @Primrec' n a) (hb : @Primrec' n b) (hf : @Primrec' n f)
    (hg : @Primrec' n g) : @Primrec' n fun v => if a v < b v then f v else g v :=
  (prec' (sub.comp₂ _ hb ha) hg (tail <| tail hf)).of_eq fun v => by
    cases e : b v - a v
    · simp [not_lt.2 (Nat.sub_eq_zero_iff_le.mp e)]
    · simp [Nat.lt_of_sub_eq_succ e]

theorem natPair : @Primrec' 2 fun v => v.head.pair v.tail.head :=
  if_lt head (tail head) (add.comp₂ _ (tail <| mul.comp₂ _ head head) head)
    (add.comp₂ _ (add.comp₂ _ (mul.comp₂ _ head head) head) (tail head))

protected theorem encode : ∀ {n}, @Primrec' n encode
  | 0 => (const 0).of_eq fun v => by rw [v.eq_nil]; rfl
  | _ + 1 =>
    (succ.comp₁ _ (natPair.comp₂ _ head (tail Primrec'.encode))).of_eq fun ⟨_ :: _, _⟩ => rfl

theorem sqrt : @Primrec' 1 fun v => v.head.sqrt := by
  suffices H : ∀ n : ℕ, n.sqrt =
      n.rec 0 fun x y => if x.succ < y.succ * y.succ then y else y.succ by
    simp only [H, succ_eq_add_one]
    have :=
      @prec' 1 _ _
        (fun v => by
          have x := v.head; have y := v.tail.head
          exact if x.succ < y.succ * y.succ then y else y.succ)
        head (const 0) ?_
    · exact this
    have x1 : @Primrec' 3 fun v => v.head.succ := succ.comp₁ _ head
    have y1 : @Primrec' 3 fun v => v.tail.head.succ := succ.comp₁ _ (tail head)
    exact if_lt x1 (mul.comp₂ _ y1 y1) (tail head) y1
  introv; symm
  induction n with
  | zero => simp
  | succ n IH =>
    dsimp; rw [IH]; split_ifs with h
    · exact le_antisymm (Nat.sqrt_le_sqrt (Nat.le_succ _)) (Nat.lt_succ_iff.1 <| Nat.sqrt_lt.2 h)
    · exact Nat.eq_sqrt.2
        ⟨not_lt.1 h, Nat.sqrt_lt.1 <| Nat.lt_succ_iff.2 <| Nat.sqrt_succ_le_succ_sqrt _⟩

theorem unpair₁ {n f} (hf : @Primrec' n f) : @Primrec' n fun v => (f v).unpair.1 := by
  have s := sqrt.comp₁ _ hf
  have fss := sub.comp₂ _ hf (mul.comp₂ _ s s)
  refine (if_lt fss s fss s).of_eq fun v => ?_
  simp [Nat.unpair]; split_ifs <;> rfl

theorem unpair₂ {n f} (hf : @Primrec' n f) : @Primrec' n fun v => (f v).unpair.2 := by
  have s := sqrt.comp₁ _ hf
  have fss := sub.comp₂ _ hf (mul.comp₂ _ s s)
  refine (if_lt fss s s (sub.comp₂ _ fss s)).of_eq fun v => ?_
  simp [Nat.unpair]; split_ifs <;> rfl

theorem of_prim {n f} : Primrec f → @Primrec' n f :=
  suffices ∀ f, Nat.Primrec f → @Primrec' 1 fun v => f v.head from fun hf =>
    (pred.comp₁ _ <|
          (this _ hf).comp₁ (fun m => Encodable.encode <| (@decode (List.Vector ℕ n) _ m).map f)
            Primrec'.encode).of_eq
      fun i => by simp [encodek]
  fun f hf => by
  induction hf with
  | zero => exact const 0
  | succ => exact succ
  | left => exact unpair₁ head
  | right => exact unpair₂ head
  | pair _ _ hf hg => exact natPair.comp₂ _ hf hg
  | comp _ _ hf hg => exact hf.comp₁ _ hg
  | prec _ _ hf hg =>
    simpa using
      prec' (unpair₂ head) (hf.comp₁ _ (unpair₁ head))
        (hg.comp₁ _ <|
          natPair.comp₂ _ (unpair₁ <| tail <| tail head) (natPair.comp₂ _ head (tail head)))

theorem prim_iff {n f} : @Primrec' n f ↔ Primrec f :=
  ⟨to_prim, of_prim⟩

theorem prim_iff₁ {f : ℕ → ℕ} : (@Primrec' 1 fun v => f v.head) ↔ Primrec f :=
  prim_iff.trans
    ⟨fun h => (h.comp <| .vector_ofFn fun _ => .id).of_eq fun v => by simp, fun h =>
      h.comp .vector_head⟩

theorem prim_iff₂ {f : ℕ → ℕ → ℕ} : (@Primrec' 2 fun v => f v.head v.tail.head) ↔ Primrec₂ f :=
  prim_iff.trans
    ⟨fun h => (h.comp <| Primrec.vector_cons.comp .fst <|
      Primrec.vector_cons.comp .snd (.const nil)).of_eq fun v => by simp,
    fun h => h.comp .vector_head (Primrec.vector_head.comp .vector_tail)⟩

theorem vec_iff {m n f} : @Vec m n f ↔ Primrec f :=
  ⟨fun h => by simpa using Primrec.vector_ofFn fun i => to_prim (h i), fun h i =>
    of_prim <| Primrec.vector_get.comp h (.const i)⟩

end Nat.Primrec'

theorem Primrec.nat_sqrt : Primrec Nat.sqrt :=
  Nat.Primrec'.prim_iff₁.1 Nat.Primrec'.sqrt

set_option linter.style.longFile 1700
