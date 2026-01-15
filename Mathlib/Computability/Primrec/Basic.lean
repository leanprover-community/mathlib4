/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Logic.Encodable.Pi
public import Mathlib.Logic.Function.Iterate

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

@[expose] public section

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

theorem option_getD : Primrec₂ (@Option.getD α) :=
  Primrec.of_eq (option_casesOn Primrec₂.left Primrec₂.right .right) fun ⟨o, a⟩ => by
    cases o <;> rfl

theorem option_getD_default [Inhabited α] : Primrec (fun o : Option α => o.getD default) :=
  option_getD.comp .id (const default)

set_option linter.deprecated false in
@[deprecated option_getD_default (since := "2026-01-05")]
theorem option_iget [Inhabited α] : Primrec (@Option.iget α _) :=
  option_getD_default

theorem option_isSome : Primrec (@Option.isSome α) :=
  (option_casesOn .id (const false) (const true).to₂).of_eq fun o => by cases o <;> rfl

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

end Primrec

namespace PrimrecRel

open Primrec List PrimrecPred

variable {α β : Type*} {R : α → β → Prop} {L : List α} {b : β}

variable [Primcodable α] [Primcodable β]

protected theorem not (hf : PrimrecRel R) : PrimrecRel fun a b ↦ ¬ R a b := PrimrecPred.not hf

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

end Primrec
