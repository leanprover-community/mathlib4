/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Logic.Equiv.List
import Mathlib.Logic.Function.Iterate

#align_import computability.primrec from "leanprover-community/mathlib"@"2738d2ca56cbc63be80c3bd48e9ed90ad94e947d"

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

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]
-/


open Denumerable Encodable Function

namespace Nat

-- porting note: elim is no longer required because lean 4 is better
-- at inferring motive types (I think this is the reason)
-- and worst case, we can always explicitly write (motive := fun _ => C)
-- without having to then add all the other underscores

-- /-- The non-dependent recursor on naturals. -/
-- def elim {C : Sort*} : C → (ℕ → C → C) → ℕ → C :=
--   @Nat.rec fun _ => C
-- example {C : Sort*} (base : C) (succ : ℕ → C → C) (a : ℕ) :
--   a.elim base succ = a.rec base succ := rfl

#align nat.elim Nat.rec

#align nat.elim_zero Nat.rec_zero

#align nat.elim_succ Nat.rec_add_one

-- porting note: cases is no longer required because lean 4 is better
-- at inferring motive types (I think this is the reason)

-- /-- Cases on whether the input is 0 or a successor. -/
-- def cases {C : Sort*} (a : C) (f : ℕ → C) : ℕ → C :=
--   Nat.elim a fun n _ => f n
-- example {C : Sort*} (a : C) (f : ℕ → C) (n : ℕ) :
--   n.cases a f = n.casesOn a f := rfl

#align nat.cases Nat.casesOn

#align nat.cases_zero Nat.rec_zero

#align nat.cases_succ Nat.rec_add_one

/-- Calls the given function on a pair of entries `n`, encoded via the pairing function. -/
@[simp, reducible]
def unpaired {α} (f : ℕ → ℕ → α) (n : ℕ) : α :=
  f n.unpair.1 n.unpair.2
#align nat.unpaired Nat.unpaired

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
#align nat.primrec Nat.Primrec

namespace Primrec

theorem of_eq {f g : ℕ → ℕ} (hf : Nat.Primrec f) (H : ∀ n, f n = g n) : Nat.Primrec g :=
  (funext H : f = g) ▸ hf
#align nat.primrec.of_eq Nat.Primrec.of_eq

theorem const : ∀ n : ℕ, Nat.Primrec fun _ => n
  | 0 => zero
  | n + 1 => Primrec.succ.comp (const n)
#align nat.primrec.const Nat.Primrec.const

protected theorem id : Nat.Primrec id :=
  (left.pair right).of_eq fun n => by simp
                                      -- 🎉 no goals
#align nat.primrec.id Nat.Primrec.id

theorem prec1 {f} (m : ℕ) (hf : Nat.Primrec f) :
    Nat.Primrec fun n => n.rec m fun y IH => f <| Nat.pair y IH :=
  ((prec (const m) (hf.comp right)).comp (zero.pair Primrec.id)).of_eq fun n => by simp
                                                                                   -- 🎉 no goals
#align nat.primrec.prec1 Nat.Primrec.prec1

theorem casesOn1 {f} (m : ℕ) (hf : Nat.Primrec f) : Nat.Primrec (Nat.casesOn · m f) :=
  (prec1 m (hf.comp left)).of_eq <| by simp
                                       -- 🎉 no goals
#align nat.primrec.cases1 Nat.Primrec.casesOn1

-- Porting note: `Nat.Primrec.casesOn` is already declared as a recursor.
theorem casesOn' {f g} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (unpaired fun z n => n.casesOn (f z) fun y => g <| Nat.pair z y) :=
  (prec hf (hg.comp (pair left (left.comp right)))).of_eq <| fun n => by simp
                                                                         -- 🎉 no goals
#align nat.primrec.cases Nat.Primrec.casesOn'

protected theorem swap : Nat.Primrec (unpaired (swap Nat.pair)) :=
  (pair right left).of_eq fun n => by simp
                                      -- 🎉 no goals
#align nat.primrec.swap Nat.Primrec.swap

theorem swap' {f} (hf : Nat.Primrec (unpaired f)) : Nat.Primrec (unpaired (swap f)) :=
  (hf.comp .swap).of_eq fun n => by simp
                                    -- 🎉 no goals
#align nat.primrec.swap' Nat.Primrec.swap'

theorem pred : Nat.Primrec pred :=
  (casesOn1 0 Primrec.id).of_eq fun n => by cases n <;> simp [*]
                                            -- ⊢ Nat.casesOn Nat.zero 0 id = Nat.pred Nat.zero
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
#align nat.primrec.pred Nat.Primrec.pred

theorem add : Nat.Primrec (unpaired (· + ·)) :=
  (prec .id ((Primrec.succ.comp right).comp right)).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, add_succ]
    -- ⊢ Nat.rec (unpair p).fst (fun y IH => succ IH) (unpair p).snd = (unpair p).fst …
          -- ⊢ Nat.rec (unpair p).fst (fun y IH => succ IH) Nat.zero = (unpair p).fst + Nat …
                                   -- 🎉 no goals
                                   -- 🎉 no goals
#align nat.primrec.add Nat.Primrec.add

theorem sub : Nat.Primrec (unpaired (· - ·)) :=
  (prec .id ((pred.comp right).comp right)).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, sub_succ]
    -- ⊢ Nat.rec (unpair p).fst (fun y IH => Nat.pred IH) (unpair p).snd = (unpair p) …
          -- ⊢ Nat.rec (unpair p).fst (fun y IH => Nat.pred IH) Nat.zero = (unpair p).fst - …
                                   -- 🎉 no goals
                                   -- 🎉 no goals
#align nat.primrec.sub Nat.Primrec.sub

theorem mul : Nat.Primrec (unpaired (· * ·)) :=
  (prec zero (add.comp (pair left (right.comp right)))).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, mul_succ, add_comm _ (unpair p).fst]
    -- ⊢ Nat.rec 0 (fun y IH => (unpair p).fst + IH) (unpair p).snd = (unpair p).fst  …
          -- ⊢ Nat.rec 0 (fun y IH => (unpair p).fst + IH) Nat.zero = (unpair p).fst * Nat. …
                                   -- 🎉 no goals
                                   -- 🎉 no goals
#align nat.primrec.mul Nat.Primrec.mul

theorem pow : Nat.Primrec (unpaired (· ^ ·)) :=
  (prec (const 1) (mul.comp (pair (right.comp right) left))).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, pow_succ]
    -- ⊢ Nat.rec 1 (fun y IH => IH * (unpair p).fst) (unpair p).snd = (unpair p).fst  …
          -- ⊢ Nat.rec 1 (fun y IH => IH * (unpair p).fst) Nat.zero = (unpair p).fst ^ Nat. …
                                   -- 🎉 no goals
                                   -- 🎉 no goals
#align nat.primrec.pow Nat.Primrec.pow

end Primrec

end Nat

/-- A `Primcodable` type is an `Encodable` type for which
  the encode/decode functions are primitive recursive. -/
class Primcodable (α : Type*) extends Encodable α where
  -- porting note: was `prim [] `.
  -- This means that `prim` does not take the type explicitly in Lean 4
  prim : Nat.Primrec fun n => Encodable.encode (decode n)
#align primcodable Primcodable

namespace Primcodable

open Nat.Primrec

instance (priority := 10) ofDenumerable (α) [Denumerable α] : Primcodable α :=
  ⟨Nat.Primrec.succ.of_eq <| by simp⟩
                                -- 🎉 no goals
#align primcodable.of_denumerable Primcodable.ofDenumerable

/-- Builds a `Primcodable` instance from an equivalence to a `Primcodable` type. -/
def ofEquiv (α) {β} [Primcodable α] (e : β ≃ α) : Primcodable β :=
  { Encodable.ofEquiv α e with
    prim := (@Primcodable.prim α _).of_eq fun n => by
      rw [decode_ofEquiv]
      -- ⊢ encode (decode n) = encode (Option.map (↑e.symm) (decode n))
      cases (@decode α _ n) <;>
      -- ⊢ encode none = encode (Option.map (↑e.symm) none)
        simp [encode_ofEquiv] }
        -- 🎉 no goals
        -- 🎉 no goals
#align primcodable.of_equiv Primcodable.ofEquiv

instance empty : Primcodable Empty :=
  ⟨zero⟩
#align primcodable.empty Primcodable.empty

instance unit : Primcodable PUnit :=
  ⟨(casesOn1 1 zero).of_eq fun n => by cases n <;> simp⟩
                                       -- ⊢ (Nat.casesOn Nat.zero 1 fun x => 0) = encode (decode Nat.zero)
                                                   -- 🎉 no goals
                                                   -- 🎉 no goals
#align primcodable.unit Primcodable.unit

instance option {α : Type*} [h : Primcodable α] : Primcodable (Option α) :=
  ⟨(casesOn1 1 ((casesOn1 0 (.comp .succ .succ)).comp (@Primcodable.prim α _))).of_eq fun n => by
    cases n with
      | zero => rfl
      | succ n =>
        rw [decode_option_succ]
        cases H : @decode α _ n <;> simp [H]⟩
#align primcodable.option Primcodable.option

instance bool : Primcodable Bool :=
  ⟨(casesOn1 1 (casesOn1 2 zero)).of_eq fun n => match n with
    | 0 => rfl
    | 1 => rfl
    | (n + 2) => by rw [decode_ge_two] <;> simp⟩
                    -- ⊢ (Nat.casesOn (n + 2) 1 fun x => Nat.casesOn x 2 fun x => 0) = encode none
                                           -- 🎉 no goals
                                           -- 🎉 no goals
#align primcodable.bool Primcodable.bool

end Primcodable

/-- `Primrec f` means `f` is primitive recursive (after
  encoding its input and output as natural numbers). -/
def Primrec {α β} [Primcodable α] [Primcodable β] (f : α → β) : Prop :=
  Nat.Primrec fun n => encode ((@decode α _ n).map f)
#align primrec Primrec

namespace Primrec

variable {α : Type*} {β : Type*} {σ : Type*}

variable [Primcodable α] [Primcodable β] [Primcodable σ]

open Nat.Primrec

protected theorem encode : Primrec (@encode α _) :=
  (@Primcodable.prim α _).of_eq fun n => by cases @decode α _ n <;> rfl
                                            -- ⊢ encode none = encode (Option.map encode none)
                                                                    -- 🎉 no goals
                                                                    -- 🎉 no goals
#align primrec.encode Primrec.encode

protected theorem decode : Primrec (@decode α _) :=
  Nat.Primrec.succ.comp (@Primcodable.prim α _)
#align primrec.decode Primrec.decode

theorem dom_denumerable {α β} [Denumerable α] [Primcodable β] {f : α → β} :
    Primrec f ↔ Nat.Primrec fun n => encode (f (ofNat α n)) :=
  ⟨fun h => (pred.comp h).of_eq fun n => by simp, fun h =>
                                            -- 🎉 no goals
    (Nat.Primrec.succ.comp h).of_eq fun n => by simp⟩
                                                -- 🎉 no goals
#align primrec.dom_denumerable Primrec.dom_denumerable

theorem nat_iff {f : ℕ → ℕ} : Primrec f ↔ Nat.Primrec f :=
  dom_denumerable
#align primrec.nat_iff Primrec.nat_iff

theorem encdec : Primrec fun n => encode (@decode α _ n) :=
  nat_iff.2 Primcodable.prim
#align primrec.encdec Primrec.encdec

theorem option_some : Primrec (@some α) :=
  ((casesOn1 0 (Nat.Primrec.succ.comp .succ)).comp (@Primcodable.prim α _)).of_eq fun n => by
    cases @decode α _ n <;> simp
    -- ⊢ (Nat.casesOn (encode none) 0 fun n => Nat.succ (Nat.succ n)) = encode (Optio …
                            -- 🎉 no goals
                            -- 🎉 no goals
#align primrec.option_some Primrec.option_some

theorem of_eq {f g : α → σ} (hf : Primrec f) (H : ∀ n, f n = g n) : Primrec g :=
  (funext H : f = g) ▸ hf
#align primrec.of_eq Primrec.of_eq

theorem const (x : σ) : Primrec fun _ : α => x :=
  ((casesOn1 0 (.const (encode x).succ)).comp (@Primcodable.prim α _)).of_eq fun n => by
    cases @decode α _ n <;> rfl
    -- ⊢ (Nat.casesOn (encode none) 0 fun x_1 => Nat.succ (encode x)) = encode (Optio …
                            -- 🎉 no goals
                            -- 🎉 no goals
#align primrec.const Primrec.const

protected theorem id : Primrec (@id α) :=
  (@Primcodable.prim α).of_eq <| by simp
                                    -- 🎉 no goals
#align primrec.id Primrec.id

theorem comp {f : β → σ} {g : α → β} (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f (g a) :=
  ((casesOn1 0 (.comp hf (pred.comp hg))).comp (@Primcodable.prim α _)).of_eq fun n => by
    cases @decode α _ n <;> simp [encodek]
    -- ⊢ (Nat.casesOn (encode none) 0 fun n => encode (Option.map f (decode (Nat.pred …
                            -- 🎉 no goals
                            -- 🎉 no goals
#align primrec.comp Primrec.comp

theorem succ : Primrec Nat.succ :=
  nat_iff.2 Nat.Primrec.succ
#align primrec.succ Primrec.succ

theorem pred : Primrec Nat.pred :=
  nat_iff.2 Nat.Primrec.pred
#align primrec.pred Primrec.pred

theorem encode_iff {f : α → σ} : (Primrec fun a => encode (f a)) ↔ Primrec f :=
  ⟨fun h => Nat.Primrec.of_eq h fun n => by cases @decode α _ n <;> rfl, Primrec.encode.comp⟩
                                            -- ⊢ encode (Option.map (fun a => encode (f a)) none) = encode (Option.map f none)
                                                                    -- 🎉 no goals
                                                                    -- 🎉 no goals
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

theorem of_equiv {β} {e : β ≃ α} :
    haveI := Primcodable.ofEquiv α e
    Primrec e :=
  letI : Primcodable β := Primcodable.ofEquiv α e
  encode_iff.1 Primrec.encode
#align primrec.of_equiv Primrec.of_equiv

theorem of_equiv_symm {β} {e : β ≃ α} :
    haveI := Primcodable.ofEquiv α e
    Primrec e.symm :=
  letI := Primcodable.ofEquiv α e
  encode_iff.1 (show Primrec fun a => encode (e (e.symm a)) by simp [Primrec.encode])
                                                               -- 🎉 no goals
#align primrec.of_equiv_symm Primrec.of_equiv_symm

theorem of_equiv_iff {β} (e : β ≃ α) {f : σ → β} :
    haveI := Primcodable.ofEquiv α e
    (Primrec fun a => e (f a)) ↔ Primrec f :=
  letI := Primcodable.ofEquiv α e
  ⟨fun h => (of_equiv_symm.comp h).of_eq fun a => by simp, of_equiv.comp⟩
                                                     -- 🎉 no goals
#align primrec.of_equiv_iff Primrec.of_equiv_iff

theorem of_equiv_symm_iff {β} (e : β ≃ α) {f : σ → α} :
    haveI := Primcodable.ofEquiv α e
    (Primrec fun a => e.symm (f a)) ↔ Primrec f :=
  letI := Primcodable.ofEquiv α e
  ⟨fun h => (of_equiv.comp h).of_eq fun a => by simp, of_equiv_symm.comp⟩
                                                -- 🎉 no goals
#align primrec.of_equiv_symm_iff Primrec.of_equiv_symm_iff

end Primrec

namespace Primcodable

open Nat.Primrec

instance prod {α β} [Primcodable α] [Primcodable β] : Primcodable (α × β) :=
  ⟨((casesOn' zero ((casesOn' zero .succ).comp (pair right ((@Primcodable.prim β).comp left)))).comp
          (pair right ((@Primcodable.prim α).comp left))).of_eq
      fun n => by
      simp [Nat.unpaired]
      -- ⊢ Nat.rec 0 (fun n_1 n_ih => Nat.rec 0 (fun n n_ih => Nat.succ (Nat.pair n_1 n …
      cases @decode α _ n.unpair.1; · simp
      -- ⊢ Nat.rec 0 (fun n_1 n_ih => Nat.rec 0 (fun n n_ih => Nat.succ (Nat.pair n_1 n …
                                      -- 🎉 no goals
      cases @decode β _ n.unpair.2 <;> simp⟩
      -- ⊢ Nat.rec 0 (fun n n_ih => Nat.rec 0 (fun n_1 n_ih => Nat.succ (Nat.pair n n_1 …
                                       -- 🎉 no goals
                                       -- 🎉 no goals
#align primcodable.prod Primcodable.prod

end Primcodable

namespace Primrec

variable {α : Type*} {σ : Type*} [Primcodable α] [Primcodable σ]

open Nat.Primrec

theorem fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.fst α β) :=
  ((casesOn' zero
            ((casesOn' zero (Nat.Primrec.succ.comp left)).comp
              (pair right ((@Primcodable.prim β).comp left)))).comp
        (pair right ((@Primcodable.prim α).comp left))).of_eq
    fun n => by
    simp
    -- ⊢ Nat.rec 0 (fun n_1 n_ih => Nat.rec 0 (fun n n_ih => Nat.succ n_1) (encode (d …
    cases @decode α _ n.unpair.1 <;> simp
    -- ⊢ Nat.rec 0 (fun n_1 n_ih => Nat.rec 0 (fun n n_ih => Nat.succ n_1) (encode (d …
                                     -- 🎉 no goals
                                     -- ⊢ Nat.rec 0 (fun n n_ih => Nat.succ (encode val✝)) (encode (decode (Nat.unpair …
    cases @decode β _ n.unpair.2 <;> simp
    -- ⊢ Nat.rec 0 (fun n n_ih => Nat.succ (encode val✝)) (encode none) = encode (Opt …
                                     -- 🎉 no goals
                                     -- 🎉 no goals
#align primrec.fst Primrec.fst

theorem snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.snd α β) :=
  ((casesOn' zero
            ((casesOn' zero (Nat.Primrec.succ.comp right)).comp
              (pair right ((@Primcodable.prim β).comp left)))).comp
        (pair right ((@Primcodable.prim α).comp left))).of_eq
    fun n => by
    simp
    -- ⊢ Nat.rec 0 (fun n_1 n_ih => Nat.rec 0 (fun n n_ih => Nat.succ n) (encode (dec …
    cases @decode α _ n.unpair.1 <;> simp
    -- ⊢ Nat.rec 0 (fun n_1 n_ih => Nat.rec 0 (fun n n_ih => Nat.succ n) (encode (dec …
                                     -- 🎉 no goals
                                     -- ⊢ Nat.rec 0 (fun n n_ih => Nat.succ n) (encode (decode (Nat.unpair n).snd)) =  …
    cases @decode β _ n.unpair.2 <;> simp
    -- ⊢ Nat.rec 0 (fun n n_ih => Nat.succ n) (encode none) = encode none
                                     -- 🎉 no goals
                                     -- 🎉 no goals
#align primrec.snd Primrec.snd

theorem pair {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {f : α → β} {g : α → γ}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => (f a, g a) :=
  ((casesOn1 0
            (Nat.Primrec.succ.comp <|
              .pair (Nat.Primrec.pred.comp hf) (Nat.Primrec.pred.comp hg))).comp
        (@Primcodable.prim α _)).of_eq
    fun n => by cases @decode α _ n <;> simp [encodek]
                -- ⊢ (Nat.casesOn (encode none) 0 fun n => Nat.succ (Nat.pair (Nat.pred (encode ( …
                                        -- 🎉 no goals
                                        -- 🎉 no goals
#align primrec.pair Primrec.pair

theorem unpair : Primrec Nat.unpair :=
  (pair (nat_iff.2 .left) (nat_iff.2 .right)).of_eq fun n => by simp
                                                                -- 🎉 no goals
#align primrec.unpair Primrec.unpair

theorem list_get?₁ : ∀ l : List α, Primrec l.get?
  | [] => dom_denumerable.2 zero
  | a :: l =>
    dom_denumerable.2 <|
      (casesOn1 (encode a).succ <| dom_denumerable.1 <| list_get?₁ l).of_eq fun n => by
        cases n <;> simp
        -- ⊢ (Nat.casesOn Nat.zero (Nat.succ (encode a)) fun n => encode (List.get? l (of …
                    -- 🎉 no goals
                    -- 🎉 no goals
#align primrec.list_nth₁ Primrec.list_get?₁

end Primrec

/-- `Primrec₂ f` means `f` is a binary primitive recursive function.
  This is technically unnecessary since we can always curry all
  the arguments together, but there are enough natural two-arg
  functions that it is convenient to express this directly. -/
def Primrec₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α → β → σ) :=
  Primrec fun p : α × β => f p.1 p.2
#align primrec₂ Primrec₂

/-- `PrimrecPred p` means `p : α → Prop` is a (decidable)
  primitive recursive predicate, which is to say that
  `decide ∘ p : α → Bool` is primitive recursive. -/
def PrimrecPred {α} [Primcodable α] (p : α → Prop) [DecidablePred p] :=
  Primrec fun a => decide (p a)
#align primrec_pred PrimrecPred

/-- `PrimrecRel p` means `p : α → β → Prop` is a (decidable)
  primitive recursive relation, which is to say that
  `decide ∘ p : α → β → Bool` is primitive recursive. -/
def PrimrecRel {α β} [Primcodable α] [Primcodable β] (s : α → β → Prop)
    [∀ a b, Decidable (s a b)] :=
  Primrec₂ fun a b => decide (s a b)
#align primrec_rel PrimrecRel

namespace Primrec₂

variable {α : Type*} {β : Type*} {σ : Type*}

variable [Primcodable α] [Primcodable β] [Primcodable σ]

theorem of_eq {f g : α → β → σ} (hg : Primrec₂ f) (H : ∀ a b, f a b = g a b) : Primrec₂ g :=
  (by funext a b; apply H : f = g) ▸ hg
      -- ⊢ f a b = g a b
                  -- 🎉 no goals
#align primrec₂.of_eq Primrec₂.of_eq

theorem const (x : σ) : Primrec₂ fun (_ : α) (_ : β) => x :=
  Primrec.const _
#align primrec₂.const Primrec₂.const

protected theorem pair : Primrec₂ (@Prod.mk α β) :=
  .pair .fst .snd
#align primrec₂.pair Primrec₂.pair

theorem left : Primrec₂ fun (a : α) (_ : β) => a :=
  .fst
#align primrec₂.left Primrec₂.left

theorem right : Primrec₂ fun (_ : α) (b : β) => b :=
  .snd
#align primrec₂.right Primrec₂.right

theorem natPair : Primrec₂ Nat.pair := by simp [Primrec₂, Primrec]; constructor
                                          -- ⊢ Nat.Primrec fun n => Nat.succ n
                                                                    -- 🎉 no goals
#align primrec₂.mkpair Primrec₂.natPair

theorem unpaired {f : ℕ → ℕ → α} : Primrec (Nat.unpaired f) ↔ Primrec₂ f :=
  ⟨fun h => by simpa using h.comp natPair, fun h => h.comp Primrec.unpair⟩
               -- 🎉 no goals
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
                                 -- 🎉 no goals
#align primrec₂.of_nat_iff Primrec₂.ofNat_iff

theorem uncurry {f : α → β → σ} : Primrec (Function.uncurry f) ↔ Primrec₂ f := by
  rw [show Function.uncurry f = fun p : α × β => f p.1 p.2 from funext fun ⟨a, b⟩ => rfl]; rfl
  -- ⊢ (Primrec fun p => f p.fst p.snd) ↔ Primrec₂ f
                                                                                           -- 🎉 no goals
#align primrec₂.uncurry Primrec₂.uncurry

theorem curry {f : α × β → σ} : Primrec₂ (Function.curry f) ↔ Primrec f := by
  rw [← uncurry, Function.uncurry_curry]
  -- 🎉 no goals
#align primrec₂.curry Primrec₂.curry

end Primrec₂

section Comp

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {σ : Type*}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable σ]

theorem Primrec.comp₂ {f : γ → σ} {g : α → β → γ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec₂ fun a b => f (g a b) :=
  hf.comp hg
#align primrec.comp₂ Primrec.comp₂

theorem Primrec₂.comp {f : β → γ → σ} {g : α → β} {h : α → γ} (hf : Primrec₂ f) (hg : Primrec g)
    (hh : Primrec h) : Primrec fun a => f (g a) (h a) :=
  Primrec.comp hf (hg.pair hh)
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

variable {α : Type*} {β : Type*} {σ : Type*}

variable [Primcodable α] [Primcodable β] [Primcodable σ]

open Nat.Primrec

theorem swap {f : α → β → σ} (h : Primrec₂ f) : Primrec₂ (swap f) :=
  h.comp₂ Primrec₂.right Primrec₂.left
#align primrec₂.swap Primrec₂.swap

theorem nat_iff {f : α → β → σ} : Primrec₂ f ↔ Nat.Primrec
    (.unpaired fun m n => encode <| (@decode α _ m).bind fun a => (@decode β _ n).map (f a)) := by
  have :
    ∀ (a : Option α) (b : Option β),
      Option.map (fun p : α × β => f p.1 p.2)
          (Option.bind a fun a : α => Option.map (Prod.mk a) b) =
        Option.bind a fun a => Option.map (f a) b := fun a b => by
          cases a <;> cases b <;> rfl
  simp [Primrec₂, Primrec, this]
  -- 🎉 no goals
#align primrec₂.nat_iff Primrec₂.nat_iff

theorem nat_iff' {f : α → β → σ} :
    Primrec₂ f ↔
      Primrec₂ fun m n : ℕ => (@decode α _ m).bind fun a => Option.map (f a) (@decode β _ n) :=
  nat_iff.trans <| unpaired'.trans encode_iff
#align primrec₂.nat_iff' Primrec₂.nat_iff'

end Primrec₂

namespace Primrec

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {σ : Type*}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable σ]

theorem to₂ {f : α × β → σ} (hf : Primrec f) : Primrec₂ fun a b => f (a, b) :=
  hf.of_eq fun _ => rfl
#align primrec.to₂ Primrec.to₂

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
          Nat.Primrec.id.pair <| (@Primcodable.prim α).comp Nat.Primrec.left).of_eq
      fun n => by
      simp
      -- ⊢ Nat.rec 0 (fun n_1 n_ih => Nat.rec (encode (Option.map f (decode n_1))) (fun …
      cases' @decode α _ n.unpair.1 with a; · rfl
      -- ⊢ Nat.rec 0 (fun n_1 n_ih => Nat.rec (encode (Option.map f (decode n_1))) (fun …
                                              -- 🎉 no goals
      simp [encodek]
      -- ⊢ Nat.rec (Nat.succ (encode (f a))) (fun y IH => encode (Option.map ((fun p => …
      induction' n.unpair.2 with m <;> simp [encodek]
      -- ⊢ Nat.rec (Nat.succ (encode (f a))) (fun y IH => encode (Option.map ((fun p => …
                                       -- 🎉 no goals
                                       -- ⊢ encode (Option.map ((fun p => g p.fst p.snd) ∘ Prod.mk a ∘ Prod.mk m) (decod …
      simp [*, encodek]
      -- 🎉 no goals
#align primrec.nat_elim Primrec.nat_rec

theorem nat_rec' {f : α → ℕ} {g : α → β} {h : α → ℕ × β → β}
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) :
    Primrec fun a => (f a).rec (motive := fun _ => β) (g a) fun n IH => h a (n, IH) :=
  (nat_rec hg hh).comp .id hf
#align primrec.nat_elim' Primrec.nat_rec'

theorem nat_rec₁ {f : ℕ → α → α} (a : α) (hf : Primrec₂ f) : Primrec (Nat.rec a f) :=
  nat_rec' .id (const a) <| comp₂ hf Primrec₂.right
#align primrec.nat_elim₁ Primrec.nat_rec₁

theorem nat_casesOn' {f : α → β} {g : α → ℕ → β} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec₂ fun a (n : ℕ) => (n.casesOn (f a) (g a) : β) :=
  nat_rec hf <| hg.comp₂ Primrec₂.left <| comp₂ fst Primrec₂.right
#align primrec.nat_cases' Primrec.nat_casesOn'

theorem nat_casesOn {f : α → ℕ} {g : α → β} {h : α → ℕ → β} (hf : Primrec f) (hg : Primrec g)
    (hh : Primrec₂ h) : Primrec fun a => ((f a).casesOn (g a) (h a) : β) :=
  (nat_casesOn' hg hh).comp .id hf
#align primrec.nat_cases Primrec.nat_casesOn

theorem nat_casesOn₁ {f : ℕ → α} (a : α) (hf : Primrec f) :
    Primrec (fun (n : ℕ) => (n.casesOn a f : α)) :=
  nat_casesOn .id (const a) (comp₂ hf .right)
#align primrec.nat_cases₁ Primrec.nat_casesOn₁

theorem nat_iterate {f : α → ℕ} {g : α → β} {h : α → β → β} (hf : Primrec f) (hg : Primrec g)
    (hh : Primrec₂ h) : Primrec fun a => (h a)^[f a] (g a) :=
  (nat_rec' hf hg (hh.comp₂ Primrec₂.left <| snd.comp₂ Primrec₂.right)).of_eq fun a => by
    induction f a <;> simp [*, -Function.iterate_succ, Function.iterate_succ']
    -- ⊢ Nat.rec (g a) (fun n IH => h a (n, IH).snd) Nat.zero = (h a)^[Nat.zero] (g a)
                      -- 🎉 no goals
                      -- 🎉 no goals
#align primrec.nat_iterate Primrec.nat_iterate

theorem option_casesOn {o : α → Option β} {f : α → σ} {g : α → β → σ} (ho : Primrec o)
    (hf : Primrec f) (hg : Primrec₂ g) :
    @Primrec _ σ _ _ fun a => Option.casesOn (o a) (f a) (g a) :=
  encode_iff.1 <|
    (nat_casesOn (encode_iff.2 ho) (encode_iff.2 hf) <|
          pred.comp₂ <|
            Primrec₂.encode_iff.2 <|
              (Primrec₂.nat_iff'.1 hg).comp₂ ((@Primrec.encode α _).comp fst).to₂
                Primrec₂.right).of_eq
      fun a => by cases' o a with b <;> simp [encodek]
                  -- ⊢ (Nat.casesOn (encode none) (encode (f a)) fun b => Nat.pred (encode (Option. …
                                        -- 🎉 no goals
                                        -- 🎉 no goals
#align primrec.option_cases Primrec.option_casesOn

theorem option_bind {f : α → Option β} {g : α → β → Option σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => (f a).bind (g a) :=
  (option_casesOn hf (const none) hg).of_eq fun a => by cases f a <;> rfl
                                                        -- ⊢ Option.casesOn none none (g a) = Option.bind none (g a)
                                                                      -- 🎉 no goals
                                                                      -- 🎉 no goals
#align primrec.option_bind Primrec.option_bind

theorem option_bind₁ {f : α → Option σ} (hf : Primrec f) : Primrec fun o => Option.bind o f :=
  option_bind .id (hf.comp snd).to₂
#align primrec.option_bind₁ Primrec.option_bind₁

theorem option_map {f : α → Option β} {g : α → β → σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => (f a).map (g a) :=
  (option_bind hf (option_some.comp₂ hg)).of_eq fun x => by cases f x <;> rfl
                                                            -- ⊢ (Option.bind none fun b => some (g x b)) = Option.map (g x) none
                                                                          -- 🎉 no goals
                                                                          -- 🎉 no goals
#align primrec.option_map Primrec.option_map

theorem option_map₁ {f : α → σ} (hf : Primrec f) : Primrec (Option.map f) :=
  option_map .id (hf.comp snd).to₂
#align primrec.option_map₁ Primrec.option_map₁

theorem option_iget [Inhabited α] : Primrec (@Option.iget α _) :=
  (option_casesOn .id (const <| @default α _) .right).of_eq fun o => by cases o <;> rfl
                                                                        -- ⊢ (Option.casesOn (id none) default fun b => b) = Option.iget none
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
#align primrec.option_iget Primrec.option_iget

theorem option_isSome : Primrec (@Option.isSome α) :=
  (option_casesOn .id (const false) (const true).to₂).of_eq fun o => by cases o <;> rfl
                                                                        -- ⊢ (Option.casesOn (id none) false fun b => true) = Option.isSome none
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
#align primrec.option_is_some Primrec.option_isSome

theorem option_getD : Primrec₂ (@Option.getD α) :=
  Primrec.of_eq (option_casesOn Primrec₂.left Primrec₂.right .right) fun ⟨o, a⟩ => by
    cases o <;> rfl
    -- ⊢ (Option.casesOn ((fun a x => a) (none, a).fst (none, a).snd) ((fun x b => b) …
                -- 🎉 no goals
                -- 🎉 no goals
#align primrec.option_get_or_else Primrec.option_getD

theorem bind_decode_iff {f : α → β → Option σ} :
    (Primrec₂ fun a n => (@decode β _ n).bind (f a)) ↔ Primrec₂ f :=
  ⟨fun h => by simpa [encodek] using h.comp fst ((@Primrec.encode β _).comp snd), fun h =>
               -- 🎉 no goals
    option_bind (Primrec.decode.comp snd) <| h.comp (fst.comp fst) snd⟩
#align primrec.bind_decode_iff Primrec.bind_decode_iff

theorem map_decode_iff {f : α → β → σ} :
    (Primrec₂ fun a n => (@decode β _ n).map (f a)) ↔ Primrec₂ f := by
  simp only [Option.map_eq_bind]
  -- ⊢ (Primrec₂ fun a n => Option.bind (decode n) (some ∘ f a)) ↔ Primrec₂ f
  exact bind_decode_iff.trans Primrec₂.option_some_iff
  -- 🎉 no goals

#align primrec.map_decode_iff Primrec.map_decode_iff

theorem nat_add : Primrec₂ ((· + ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.add
#align primrec.nat_add Primrec.nat_add

theorem nat_sub : Primrec₂ ((· - ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.sub
#align primrec.nat_sub Primrec.nat_sub

theorem nat_mul : Primrec₂ ((· * ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.mul
#align primrec.nat_mul Primrec.nat_mul

theorem cond {c : α → Bool} {f : α → σ} {g : α → σ} (hc : Primrec c) (hf : Primrec f)
    (hg : Primrec g) : Primrec fun a => bif (c a) then (f a) else (g a) :=
  (nat_casesOn (encode_iff.2 hc) hg (hf.comp fst).to₂).of_eq fun a => by cases c a <;> rfl
                                                                         -- ⊢ (Nat.casesOn (encode false) (g a) fun b => f (a, b).fst) = bif false then f  …
                                                                                       -- 🎉 no goals
                                                                                       -- 🎉 no goals
#align primrec.cond Primrec.cond

theorem ite {c : α → Prop} [DecidablePred c] {f : α → σ} {g : α → σ} (hc : PrimrecPred c)
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => if c a then f a else g a := by
  simpa using cond hc hf hg
  -- 🎉 no goals
#align primrec.ite Primrec.ite

theorem nat_le : PrimrecRel ((· ≤ ·) : ℕ → ℕ → Prop) :=
  (nat_casesOn nat_sub (const true) (const false).to₂).of_eq fun p => by
    dsimp [swap]
    -- ⊢ Nat.rec true (fun n n_ih => false) (p.fst - p.snd) = decide (p.fst ≤ p.snd)
    cases' e : p.1 - p.2 with n
    -- ⊢ Nat.rec true (fun n n_ih => false) Nat.zero = decide (p.fst ≤ p.snd)
    · simp [tsub_eq_zero_iff_le.1 e]
      -- 🎉 no goals
    · simp [not_le.2 (Nat.lt_of_sub_eq_succ e)]
      -- 🎉 no goals
#align primrec.nat_le Primrec.nat_le

theorem nat_min : Primrec₂ (@min ℕ _) :=
  ite nat_le fst snd
#align primrec.nat_min Primrec.nat_min

theorem nat_max : Primrec₂ (@max ℕ _) :=
  ite (nat_le.comp fst snd) snd fst
#align primrec.nat_max Primrec.nat_max

theorem dom_bool (f : Bool → α) : Primrec f :=
  (cond .id (const (f true)) (const (f false))).of_eq fun b => by cases b <;> rfl
                                                                  -- ⊢ (bif id false then f true else f false) = f false
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
#align primrec.dom_bool Primrec.dom_bool

theorem dom_bool₂ (f : Bool → Bool → α) : Primrec₂ f :=
  (cond fst ((dom_bool (f true)).comp snd) ((dom_bool (f false)).comp snd)).of_eq fun ⟨a, b⟩ => by
    cases a <;> rfl
    -- ⊢ (bif (false, b).fst then f true (false, b).snd else f false (false, b).snd)  …
                -- 🎉 no goals
                -- 🎉 no goals
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

theorem _root_.PrimrecPred.not {p : α → Prop} [DecidablePred p] (hp : PrimrecPred p) :
    PrimrecPred fun a => ¬p a :=
  (Primrec.not.comp hp).of_eq fun n => by simp
                                          -- 🎉 no goals
#align primrec.not PrimrecPred.not

theorem _root_.PrimrecPred.and {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hp : PrimrecPred p) (hq : PrimrecPred q) : PrimrecPred fun a => p a ∧ q a :=
  (Primrec.and.comp hp hq).of_eq fun n => by simp
                                             -- 🎉 no goals
#align primrec.and PrimrecPred.and

theorem _root_.PrimrecPred.or {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hp : PrimrecPred p) (hq : PrimrecPred q) : PrimrecPred fun a => p a ∨ q a :=
  (Primrec.or.comp hp hq).of_eq fun n => by simp
                                            -- 🎉 no goals
#align primrec.or PrimrecPred.or

-- porting note: It is unclear whether we want to boolean versions
-- of these lemmas, just the prop versions, or both
-- The boolean versions are often actually easier to use
-- but did not exist in Lean 3
protected theorem beq [DecidableEq α] : Primrec₂ (@BEq.beq α _) :=
  have : PrimrecRel fun a b : ℕ => a = b :=
    (PrimrecPred.and nat_le nat_le.swap).of_eq fun a => by simp [le_antisymm_iff]
                                                           -- 🎉 no goals
  (this.comp₂ (Primrec.encode.comp₂ Primrec₂.left) (Primrec.encode.comp₂ Primrec₂.right)).of_eq
    fun a b => encode_injective.eq_iff

protected theorem eq [DecidableEq α] : PrimrecRel (@Eq α) := Primrec.beq
#align primrec.eq Primrec.eq

theorem nat_lt : PrimrecRel ((· < ·) : ℕ → ℕ → Prop) :=
  (nat_le.comp snd fst).not.of_eq fun p => by simp
                                              -- 🎉 no goals
#align primrec.nat_lt Primrec.nat_lt

theorem option_guard {p : α → β → Prop} [∀ a b, Decidable (p a b)] (hp : PrimrecRel p) {f : α → β}
    (hf : Primrec f) : Primrec fun a => Option.guard (p a) (f a) :=
  ite (hp.comp Primrec.id hf) (option_some_iff.2 hf) (const none)
#align primrec.option_guard Primrec.option_guard

theorem option_orElse : Primrec₂ ((· <|> ·) : Option α → Option α → Option α) :=
  (option_casesOn fst snd (fst.comp fst).to₂).of_eq fun ⟨o₁, o₂⟩ => by cases o₁ <;> cases o₂ <;> rfl
                                                                       -- ⊢ (Option.casesOn (none, o₂).fst (none, o₂).snd fun b => ((none, o₂), b).fst.f …
                                                                                    -- ⊢ (Option.casesOn (none, none).fst (none, none).snd fun b => ((none, none), b) …
                                                                                    -- ⊢ (Option.casesOn (some val✝, none).fst (some val✝, none).snd fun b => ((some  …
                                                                                                 -- 🎉 no goals
                                                                                                 -- 🎉 no goals
                                                                                                 -- 🎉 no goals
                                                                                                 -- 🎉 no goals
#align primrec.option_orelse Primrec.option_orElse

protected theorem decode₂ : Primrec (decode₂ α) :=
  option_bind .decode <|
    option_guard (Primrec.beq.comp₂ (by exact encode_iff.mpr snd) (by exact fst.comp fst)) snd
                                        -- 🎉 no goals
                                                                      -- 🎉 no goals
#align primrec.decode₂ Primrec.decode₂

theorem list_findIdx₁ {p : α → β → Bool} (hp : Primrec₂ p) :
  ∀ l : List β, Primrec fun a => l.findIdx (p a)
| [] => const 0
| a :: l => (cond (hp.comp .id (const a)) (const 0) (succ.comp (list_findIdx₁ hp l))).of_eq fun n =>
  by simp [List.findIdx_cons]
     -- 🎉 no goals
#align primrec.list_find_index₁ Primrec.list_findIdx₁

theorem list_indexOf₁ [DecidableEq α] (l : List α) : Primrec fun a => l.indexOf a :=
  list_findIdx₁ .beq l
#align primrec.list_index_of₁ Primrec.list_indexOf₁

theorem dom_fintype [Fintype α] (f : α → σ) : Primrec f :=
  let ⟨l, _, m⟩ := Finite.exists_univ_list α
  option_some_iff.1 <| by
    haveI := decidableEqOfEncodable α
    -- ⊢ Primrec fun a => some (f a)
    refine ((list_get?₁ (l.map f)).comp (list_indexOf₁ l)).of_eq fun a => ?_
    -- ⊢ List.get? (List.map f l) (List.indexOf a l) = some (f a)
    rw [List.get?_map, List.indexOf_get? (m a), Option.map_some']
    -- 🎉 no goals
#align primrec.dom_fintype Primrec.dom_fintype

-- porting note: These are new lemmas
-- I added it because it actually simplified the proofs
-- and because I couldn't understand the original proof
/-- A function is `PrimrecBounded` if its size is bounded by a primitive recursive function -/
def PrimrecBounded (f : α → β) : Prop :=
  ∃ g : α → ℕ, Primrec g ∧ ∀ x, encode (f x) ≤ g x

theorem nat_findGreatest {f : α → ℕ} {p : α → ℕ → Prop} [∀ x n, Decidable (p x n)]
    (hf : Primrec f) (hp : PrimrecRel p) : Primrec fun x => (f x).findGreatest (p x) :=
  (nat_rec' (h := fun x nih => if p x (nih.1 + 1) then nih.1 + 1 else nih.2)
    hf (const 0) (ite (hp.comp fst (snd |> fst.comp |> succ.comp))
      (snd |> fst.comp |> succ.comp) (snd.comp snd))).of_eq fun x => by
        induction f x <;> simp [Nat.findGreatest, *]
        -- ⊢ Nat.rec 0 (fun n IH => if p x ((n, IH).fst + 1) then (n, IH).fst + 1 else (n …
                          -- 🎉 no goals
                          -- 🎉 no goals

/-- To show a function `f : α → ℕ` is primitive recursive, it is enough to show that the function
  is bounded by a primitive recursive function and that its graph is primitive recursive -/
theorem of_graph {f : α → ℕ} (h₁ : PrimrecBounded f)
    (h₂ : PrimrecRel fun a b => f a = b) : Primrec f := by
  rcases h₁ with ⟨g, pg, hg : ∀ x, f x ≤ g x⟩
  -- ⊢ Primrec f
  refine (nat_findGreatest pg h₂).of_eq fun n => ?_
  -- ⊢ Nat.findGreatest (fun b => f n = b) (g n) = f n
  exact (Nat.findGreatest_spec (P := fun b => f n = b) (hg n) rfl).symm
  -- 🎉 no goals

-- We show that division is primitive recursive by showing that the graph is
theorem nat_div : Primrec₂ ((· / ·) : ℕ → ℕ → ℕ) := by
  refine of_graph ⟨_, fst, fun p => Nat.div_le_self _ _⟩ ?_
  -- ⊢ PrimrecRel fun a b => (fun x x_1 => x / x_1) a.fst a.snd = b
  have : PrimrecRel fun (a : ℕ × ℕ) (b : ℕ) => (a.2 = 0 ∧ b = 0) ∨
      (0 < a.2 ∧ b * a.2 ≤ a.1 ∧ a.1 < (b + 1) * a.2) :=
    PrimrecPred.or
      (.and (const 0 |> Primrec.eq.comp (fst |> snd.comp)) (const 0 |> Primrec.eq.comp snd))
      (.and (nat_lt.comp (const 0) (fst |> snd.comp)) <|
          .and (nat_le.comp (nat_mul.comp snd (fst |> snd.comp)) (fst |> fst.comp))
          (nat_lt.comp (fst.comp fst) (nat_mul.comp (Primrec.succ.comp snd) (snd.comp fst))))
  refine this.of_eq ?_
  -- ⊢ ∀ (a : ℕ × ℕ) (b : ℕ), a.snd = 0 ∧ b = 0 ∨ 0 < a.snd ∧ b * a.snd ≤ a.fst ∧ a …
  rintro ⟨a, k⟩ q
  -- ⊢ (a, k).snd = 0 ∧ q = 0 ∨ 0 < (a, k).snd ∧ q * (a, k).snd ≤ (a, k).fst ∧ (a,  …
  if H : k = 0 then simp [H, eq_comm]
  else
    have : q * k ≤ a ∧ a < (q + 1) * k ↔ q = a / k := by
      rw [le_antisymm_iff, ← (@Nat.lt_succ _ q), Nat.le_div_iff_mul_le' (Nat.pos_of_ne_zero H),
          Nat.div_lt_iff_lt_mul' (Nat.pos_of_ne_zero H)]
    simpa [H, zero_lt_iff, eq_comm (b := q)]
#align primrec.nat_div Primrec.nat_div

theorem nat_mod : Primrec₂ ((· % ·) : ℕ → ℕ → ℕ) :=
  (nat_sub.comp fst (nat_mul.comp snd nat_div)).to₂.of_eq fun m n => by
    apply Nat.sub_eq_of_eq_add
    -- ⊢ (m, n).fst = m % n + (m, n).snd * (fun x x_1 => x / x_1) (m, n).fst (m, n).snd
    simp [add_comm (m % n), Nat.div_add_mod]
    -- 🎉 no goals
#align primrec.nat_mod Primrec.nat_mod

theorem nat_bodd : Primrec Nat.bodd :=
  (Primrec.beq.comp (nat_mod.comp .id (const 2)) (const 1)).of_eq fun n => by
    cases H : n.bodd <;> simp [Nat.mod_two_of_bodd, H]
    -- ⊢ (id n % 2 == 1) = false
                         -- 🎉 no goals
                         -- 🎉 no goals
#align primrec.nat_bodd Primrec.nat_bodd

theorem nat_div2 : Primrec Nat.div2 :=
  (nat_div.comp .id (const 2)).of_eq fun n => n.div2_val.symm
#align primrec.nat_div2 Primrec.nat_div2

-- porting note: this is no longer used
-- theorem nat_boddDiv2 : Primrec Nat.boddDiv2 := pair nat_bodd nat_div2
#noalign primrec.nat_bodd_div2

-- porting note: bit0 is deprecated
theorem nat_double : Primrec (fun n : ℕ => 2 * n) :=
  nat_mul.comp (const _) Primrec.id
#align primrec.nat_bit0 Primrec.nat_double

-- porting note: bit1 is deprecated
theorem nat_double_succ : Primrec (fun n : ℕ => 2 * n + 1) :=
  nat_double |> Primrec.succ.comp
#align primrec.nat_bit1 Primrec.nat_double_succ

-- porting note: this is no longer used
-- theorem nat_div_mod : Primrec₂ fun n k : ℕ => (n / k, n % k) := pair nat_div nat_mod
#noalign primrec.nat_div_mod

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
  option_some_iff.1 <| this.of_eq fun a => by cases' f a with b l <;> simp [encodek]
                                              -- ⊢ Option.map (fun o => Option.casesOn o (g a) (h a)) (decode (encode [])) = so …
                                                                      -- 🎉 no goals
                                                                      -- 🎉 no goals

private theorem list_foldl' {f : α → List β} {g : α → σ} {h : α → σ × β → σ}
    (hf : haveI := prim H; Primrec f) (hg : Primrec g) (hh : haveI := prim H; Primrec₂ h) :
    Primrec fun a => (f a).foldl (fun s b => h a (s, b)) (g a) := by
  letI := prim H
  -- ⊢ Primrec fun a => List.foldl (fun s b => h a (s, b)) (g a) (f a)
  let G (a : α) (IH : σ × List β) : σ × List β := List.casesOn IH.2 IH fun b l => (h a (IH.1, b), l)
  -- ⊢ Primrec fun a => List.foldl (fun s b => h a (s, b)) (g a) (f a)
  have hG : Primrec₂ G := list_casesOn' H (snd.comp snd) snd <|
    to₂ <|
    pair (hh.comp (fst.comp fst) <| pair ((fst.comp snd).comp fst) (fst.comp snd))
      (snd.comp snd)
  let F := fun (a : α) (n : ℕ) => (G a)^[n] (g a, f a)
  -- ⊢ Primrec fun a => List.foldl (fun s b => h a (s, b)) (g a) (f a)
  have hF : Primrec fun a => (F a (encode (f a))).1 :=
    (fst.comp <|
      nat_iterate (encode_iff.2 hf) (pair hg hf) <|
      hG)
  suffices : ∀ a n, F a n = (((f a).take n).foldl (fun s b => h a (s, b)) (g a), (f a).drop n)
  -- ⊢ Primrec fun a => List.foldl (fun s b => h a (s, b)) (g a) (f a)
  · refine hF.of_eq fun a => ?_
    -- ⊢ (F a (encode (f a))).fst = List.foldl (fun s b => h a (s, b)) (g a) (f a)
    rw [this, List.take_all_of_le (length_le_encode _)]
    -- 🎉 no goals
  introv
  -- ⊢ F a n = (List.foldl (fun s b => h a (s, b)) (g a) (List.take n (f a)), List. …
  dsimp only
  -- ⊢ (fun IH => List.rec IH (fun head tail tail_ih => (h a (IH.fst, head), tail)) …
  generalize f a = l
  -- ⊢ (fun IH => List.rec IH (fun head tail tail_ih => (h a (IH.fst, head), tail)) …
  generalize g a = x
  -- ⊢ (fun IH => List.rec IH (fun head tail tail_ih => (h a (IH.fst, head), tail)) …
  induction' n with n IH generalizing l x
  -- ⊢ (fun IH => List.rec IH (fun head tail tail_ih => (h a (IH.fst, head), tail)) …
  · rfl
    -- 🎉 no goals
  simp
  -- ⊢ (fun IH => List.rec IH (fun head tail tail_ih => (h a (IH.fst, head), tail)) …
  cases' l with b l <;> simp [IH]
  -- ⊢ (fun IH => List.rec IH (fun head tail tail_ih => (h a (IH.fst, head), tail)) …
                        -- 🎉 no goals
                        -- 🎉 no goals

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
                -- ⊢ ∀ (r : List β), List.foldl (fun s b => b :: s) r [] = List.reverseAux [] r
                                -- 🎉 no goals
                                -- 🎉 no goals

end

namespace Primcodable

variable {α : Type*} {β : Type*}

variable [Primcodable α] [Primcodable β]

open Primrec

instance sum : Primcodable (Sum α β) :=
  ⟨Primrec.nat_iff.1 <|
      (encode_iff.2
            (cond nat_bodd
              (((@Primrec.decode β _).comp nat_div2).option_map <|
                to₂ <| nat_double_succ.comp (Primrec.encode.comp snd))
              (((@Primrec.decode α _).comp nat_div2).option_map <|
                to₂ <| nat_double.comp (Primrec.encode.comp snd)))).of_eq
        fun n =>
        show _ = encode (decodeSum n) by
          simp [decodeSum]
          -- ⊢ encode (bif Nat.bodd n then Option.map (fun b => 2 * encode b + 1) (decode ( …
          cases Nat.bodd n <;> simp [decodeSum]
                               -- ⊢ encode (Option.map (fun b => 2 * encode b) (decode (Nat.div2 n))) = encode ( …
                               -- ⊢ encode (Option.map (fun b => 2 * encode b + 1) (decode (Nat.div2 n))) = enco …
          · cases @decode α _ n.div2 <;> rfl
            -- ⊢ encode (Option.map (fun b => 2 * encode b) none) = encode (Option.map Sum.in …
                                         -- 🎉 no goals
                                         -- 🎉 no goals
          · cases @decode β _ n.div2 <;> rfl⟩
            -- ⊢ encode (Option.map (fun b => 2 * encode b + 1) none) = encode (Option.map Su …
                                         -- 🎉 no goals
                                         -- 🎉 no goals
#align primcodable.sum Primcodable.sum

instance list : Primcodable (List α) :=
  ⟨letI H := @Primcodable.prim (List ℕ) _
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
        -- ⊢ encode (List.foldr (fun x y => Option.bind (decode x) fun a => Option.map (L …
        apply Nat.case_strong_induction_on n; · simp
        -- ⊢ encode (List.foldr (fun x y => Option.bind (decode x) fun a => Option.map (L …
                                                -- 🎉 no goals
        intro n IH; simp
        -- ⊢ encode (List.foldr (fun x y => Option.bind (decode x) fun a => Option.map (L …
                    -- ⊢ encode (Option.bind (decode (Nat.unpair n).fst) fun a => Option.map (List.co …
        cases' @decode α _ n.unpair.1 with a; · rfl
        -- ⊢ encode (Option.bind none fun a => Option.map (List.cons (encode a)) (List.fo …
                                                -- 🎉 no goals
        simp only [decode_eq_ofNat, Option.some.injEq, Option.some_bind, Option.map_some']
        -- ⊢ encode (Option.map (List.cons (encode a)) (List.foldr (fun x y => Option.bin …
        suffices :
          ∀ (o : Option (List ℕ)) (p) (_ : encode o = encode p),
            encode (Option.map (List.cons (encode a)) o) = encode (Option.map (List.cons a) p)
        exact this _ _ (IH _ (Nat.unpair_right_le n))
        -- ⊢ ∀ (o : Option (List ℕ)) (p : Option (List α)), encode o = encode p → encode  …
        intro o p IH
        -- ⊢ encode (Option.map (List.cons (encode a)) o) = encode (Option.map (List.cons …
        cases o <;> cases p
        -- ⊢ encode (Option.map (List.cons (encode a)) none) = encode (Option.map (List.c …
                    -- ⊢ encode (Option.map (List.cons (encode a)) none) = encode (Option.map (List.c …
                    -- ⊢ encode (Option.map (List.cons (encode a)) (some val✝)) = encode (Option.map  …
        · rfl
          -- 🎉 no goals
        · injection IH
          -- 🎉 no goals
        · injection IH
          -- 🎉 no goals
        · exact congr_arg (fun k => (Nat.pair (encode a) k).succ.succ) (Nat.succ.inj IH)⟩
          -- 🎉 no goals

#align primcodable.list Primcodable.list
end Primcodable

namespace Primrec

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

theorem sum_inl : Primrec (@Sum.inl α β) :=
  encode_iff.1 <| nat_double.comp Primrec.encode
#align primrec.sum_inl Primrec.sum_inl

theorem sum_inr : Primrec (@Sum.inr α β) :=
  encode_iff.1 <| nat_double_succ.comp Primrec.encode
#align primrec.sum_inr Primrec.sum_inr

theorem sum_casesOn {f : α → Sum β γ} {g : α → β → σ} {h : α → γ → σ} (hf : Primrec f)
    (hg : Primrec₂ g) (hh : Primrec₂ h) : @Primrec _ σ _ _ fun a => Sum.casesOn (f a) (g a) (h a) :=
  option_some_iff.1 <|
    (cond (nat_bodd.comp <| encode_iff.2 hf)
          (option_map (Primrec.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hh)
          (option_map (Primrec.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hg)).of_eq
      fun a => by cases' f a with b c <;> simp [Nat.div2_val, encodek]
                  -- ⊢ (bif Nat.bodd (encode (Sum.inl b)) then Option.map (h a) (decode (Nat.div2 ( …
                                          -- 🎉 no goals
                                          -- 🎉 no goals
#align primrec.sum_cases Primrec.sum_casesOn

theorem list_cons : Primrec₂ (@List.cons α) :=
  list_cons' Primcodable.prim
#align primrec.list_cons Primrec.list_cons

theorem list_casesOn {f : α → List β} {g : α → σ} {h : α → β × List β → σ} :
    Primrec f →
      Primrec g →
        Primrec₂ h → @Primrec _ σ _ _ fun a => List.casesOn (f a) (g a) fun b l => h a (b, l) :=
  list_casesOn' Primcodable.prim
#align primrec.list_cases Primrec.list_casesOn

theorem list_foldl {f : α → List β} {g : α → σ} {h : α → σ × β → σ} :
    Primrec f →
      Primrec g → Primrec₂ h → Primrec fun a => (f a).foldl (fun s b => h a (s, b)) (g a) :=
  list_foldl' Primcodable.prim
#align primrec.list_foldl Primrec.list_foldl

theorem list_reverse : Primrec (@List.reverse α) :=
  list_reverse' Primcodable.prim
#align primrec.list_reverse Primrec.list_reverse

theorem list_foldr {f : α → List β} {g : α → σ} {h : α → β × σ → σ} (hf : Primrec f)
    (hg : Primrec g) (hh : Primrec₂ h) :
    Primrec fun a => (f a).foldr (fun b s => h a (b, s)) (g a) :=
  (list_foldl (list_reverse.comp hf) hg <| to₂ <| hh.comp fst <| (pair snd fst).comp snd).of_eq
    fun a => by simp [List.foldl_reverse]
                -- 🎉 no goals
#align primrec.list_foldr Primrec.list_foldr

theorem list_head? : Primrec (@List.head? α) :=
  (list_casesOn .id (const none) (option_some_iff.2 <| fst.comp snd).to₂).of_eq fun l => by
    cases l <;> rfl
    -- ⊢ (List.casesOn (id []) none fun b l => some ([], b, l).snd.fst) = List.head? []
                -- 🎉 no goals
                -- 🎉 no goals
#align primrec.list_head' Primrec.list_head?

theorem list_headI [Inhabited α] : Primrec (@List.headI α _) :=
  (option_iget.comp list_head?).of_eq fun l => l.head!_eq_head?.symm
#align primrec.list_head Primrec.list_headI

theorem list_tail : Primrec (@List.tail α) :=
  (list_casesOn .id (const []) (snd.comp snd).to₂).of_eq fun l => by cases l <;> rfl
                                                                     -- ⊢ (List.casesOn (id []) [] fun b l => ([], b, l).snd.snd) = List.tail []
                                                                                 -- 🎉 no goals
                                                                                 -- 🎉 no goals
#align primrec.list_tail Primrec.list_tail

theorem list_rec {f : α → List β} {g : α → σ} {h : α → β × List β × σ → σ} (hf : Primrec f)
    (hg : Primrec g) (hh : Primrec₂ h) :
    @Primrec _ σ _ _ fun a => List.recOn (f a) (g a) fun b l IH => h a (b, l, IH) :=
  let F (a : α) := (f a).foldr (fun (b : β) (s : List β × σ) => (b :: s.1, h a (b, s))) ([], g a)
  have : Primrec F :=
    list_foldr hf (pair (const []) hg) <|
      to₂ <| pair ((list_cons.comp fst (fst.comp snd)).comp snd) hh
  (snd.comp this).of_eq fun a => by
    suffices F a = (f a, List.recOn (f a) (g a) fun b l IH => h a (b, l, IH)) by rw [this]
    -- ⊢ F a = (f a, List.recOn (f a) (g a) fun b l IH => h a (b, l, IH))
    dsimp
    -- ⊢ List.foldr (fun b s => (b :: s.fst, h a (b, s))) ([], g a) (f a) = (f a, Lis …
    induction' f a with b l IH <;> simp [*]
    -- ⊢ List.foldr (fun b s => (b :: s.fst, h a (b, s))) ([], g a) [] = ([], List.re …
                                   -- 🎉 no goals
                                   -- 🎉 no goals
#align primrec.list_rec Primrec.list_rec

theorem list_get? : Primrec₂ (@List.get? α) :=
  let F (l : List α) (n : ℕ) :=
    l.foldl
      (fun (s : Sum ℕ α) (a : α) =>
        Sum.casesOn s (@Nat.casesOn (fun _ => Sum ℕ α) · (Sum.inr a) Sum.inl) Sum.inr)
      (Sum.inl n)
  have hF : Primrec₂ F :=
    (list_foldl fst (sum_inl.comp snd)
      ((sum_casesOn fst (nat_casesOn snd (sum_inr.comp <| snd.comp fst) (sum_inl.comp snd).to₂).to₂
              (sum_inr.comp snd).to₂).comp
          snd).to₂).to₂
  have :
    @Primrec _ (Option α) _ _ fun p : List α × ℕ => Sum.casesOn (F p.1 p.2) (fun _ => none) some :=
    sum_casesOn hF (const none).to₂ (option_some.comp snd).to₂
  this.to₂.of_eq fun l n => by
    dsimp; symm
    -- ⊢ Sum.rec (fun val => none) (fun val => some val) (List.foldl (fun s a => Sum. …
           -- ⊢ List.get? l n = Sum.rec (fun val => none) (fun val => some val) (List.foldl  …
    induction' l with a l IH generalizing n; · rfl
    -- ⊢ List.get? [] n = Sum.rec (fun val => none) (fun val => some val) (List.foldl …
                                               -- 🎉 no goals
    cases' n with n
    -- ⊢ List.get? (a :: l) Nat.zero = Sum.rec (fun val => none) (fun val => some val …
    · dsimp
      -- ⊢ some a = Sum.rec (fun val => none) (fun val => some val) (List.foldl (fun s  …
      clear IH
      -- ⊢ some a = Sum.rec (fun val => none) (fun val => some val) (List.foldl (fun s  …
      induction' l with _ l IH <;> simp [*]
      -- ⊢ some a = Sum.rec (fun val => none) (fun val => some val) (List.foldl (fun s  …
                                   -- 🎉 no goals
                                   -- 🎉 no goals
    · apply IH
      -- 🎉 no goals
#align primrec.list_nth Primrec.list_get?

theorem list_getD (d : α) : Primrec₂ fun l n => List.getD l n d := by
  simp only [List.getD_eq_getD_get?]
  -- ⊢ Primrec₂ fun l n => Option.getD (List.get? l n) d
  exact option_getD.comp₂ list_get? (const _)
  -- 🎉 no goals
#align primrec.list_nthd Primrec.list_getD

theorem list_getI [Inhabited α] : Primrec₂ (@List.getI α _) :=
  list_getD _
#align primrec.list_inth Primrec.list_getI

theorem list_append : Primrec₂ ((· ++ ·) : List α → List α → List α) :=
  (list_foldr fst snd <| to₂ <| comp (@list_cons α _) snd).to₂.of_eq fun l₁ l₂ => by
    induction l₁ <;> simp [*]
    -- ⊢ List.foldr (fun b s => (([], l₂), b, s).snd.fst :: (([], l₂), b, s).snd.snd) …
                     -- 🎉 no goals
                     -- 🎉 no goals
#align primrec.list_append Primrec.list_append

theorem list_concat : Primrec₂ fun l (a : α) => l ++ [a] :=
  list_append.comp fst (list_cons.comp snd (const []))
#align primrec.list_concat Primrec.list_concat

theorem list_map {f : α → List β} {g : α → β → σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => (f a).map (g a) :=
  (list_foldr hf (const []) <|
        to₂ <| list_cons.comp (hg.comp fst (fst.comp snd)) (snd.comp snd)).of_eq
    fun a => by induction f a <;> simp [*]
                -- ⊢ List.foldr (fun b s => g (a, b, s).fst (a, b, s).snd.fst :: (a, b, s).snd.sn …
                                  -- 🎉 no goals
                                  -- 🎉 no goals
#align primrec.list_map Primrec.list_map

theorem list_range : Primrec List.range :=
  (nat_rec' .id (const []) ((list_concat.comp snd fst).comp snd).to₂).of_eq fun n => by
    simp; induction n <;> simp [*, List.range_succ]
    -- ⊢ Nat.rec [] (fun n IH => IH ++ [n]) n = List.range n
          -- ⊢ Nat.rec [] (fun n IH => IH ++ [n]) Nat.zero = List.range Nat.zero
                          -- 🎉 no goals
                          -- 🎉 no goals
#align primrec.list_range Primrec.list_range

theorem list_join : Primrec (@List.join α) :=
  (list_foldr .id (const []) <| to₂ <| comp (@list_append α _) snd).of_eq fun l => by
    dsimp; induction l <;> simp [*]
    -- ⊢ List.foldr (fun b s => b ++ s) [] l = List.join l
           -- ⊢ List.foldr (fun b s => b ++ s) [] [] = List.join []
                           -- 🎉 no goals
                           -- 🎉 no goals
#align primrec.list_join Primrec.list_join

theorem list_length : Primrec (@List.length α) :=
  (list_foldr (@Primrec.id (List α) _) (const 0) <| to₂ <| (succ.comp <| snd.comp snd).to₂).of_eq
    fun l => by dsimp; induction l <;> simp [*]
                -- ⊢ List.foldr (fun b s => Nat.succ s) 0 l = List.length l
                       -- ⊢ List.foldr (fun b s => Nat.succ s) 0 [] = List.length []
                                       -- 🎉 no goals
                                       -- 🎉 no goals
#align primrec.list_length Primrec.list_length

theorem list_findIdx {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) : Primrec fun a => (f a).findIdx (p a) :=
  (list_foldr hf (const 0) <|
        to₂ <| cond (hp.comp fst <| fst.comp snd) (const 0) (succ.comp <| snd.comp snd)).of_eq
    fun a => by dsimp; induction f a <;> simp [List.findIdx_cons, *]
                -- ⊢ List.foldr (fun b s => bif p a b then 0 else Nat.succ s) 0 (f a) = List.find …
                       -- ⊢ List.foldr (fun b s => bif p a b then 0 else Nat.succ s) 0 [] = List.findIdx …
                                         -- 🎉 no goals
                                         -- 🎉 no goals
#align primrec.list_find_index Primrec.list_findIdx

theorem list_indexOf [DecidableEq α] : Primrec₂ (@List.indexOf α _) :=
  to₂ <| list_findIdx snd <| Primrec.beq.comp₂ (fst.comp fst).to₂ snd.to₂
#align primrec.list_index_of Primrec.list_indexOfₓ

theorem nat_strong_rec (f : α → ℕ → σ) {g : α → List σ → Option σ} (hg : Primrec₂ g)
    (H : ∀ a n, g a ((List.range n).map (f a)) = some (f a n)) : Primrec₂ f :=
  suffices Primrec₂ fun a n => (List.range n).map (f a) from
    Primrec₂.option_some_iff.1 <|
      (list_get?.comp (this.comp fst (succ.comp snd)) snd).to₂.of_eq fun a n => by
        simp [List.get?_range (Nat.lt_succ_self n)]
        -- 🎉 no goals
  Primrec₂.option_some_iff.1 <|
    (nat_rec (const (some []))
          (to₂ <|
            option_bind (snd.comp snd) <|
              to₂ <|
                option_map (hg.comp (fst.comp fst) snd)
                  (to₂ <| list_concat.comp (snd.comp fst) snd))).of_eq
      fun a n => by
      -- ⊢ Nat.rec (some []) (fun n IH => Option.bind IH fun b => Option.map (fun b_1 = …
            -- ⊢ Nat.rec (some []) (fun n IH => Option.bind IH fun b => Option.map (fun b_1 = …
                                      -- 🎉 no goals
      simp; induction' n with n IH; · rfl
      -- 🎉 no goals
      simp [IH, H, List.range_succ]
#align primrec.nat_strong_rec Primrec.nat_strong_rec

end Primrec

namespace Primcodable

variable {α : Type*} {β : Type*}

variable [Primcodable α] [Primcodable β]

open Primrec

/-- A subtype of a primitive recursive predicate is `Primcodable`. -/
def subtype {p : α → Prop} [DecidablePred p] (hp : PrimrecPred p) : Primcodable (Subtype p) :=
  ⟨have : Primrec fun n => (@decode α _ n).bind fun a => Option.guard p a :=
    option_bind .decode (option_guard (hp.comp snd).to₂ snd)
  nat_iff.1 <| (encode_iff.2 this).of_eq fun n =>
    show _ = encode ((@decode α _ n).bind fun a => _) by
      cases' @decode α _ n with a; · rfl
      -- ⊢ encode (Option.bind none fun a => Option.guard p a) = encode (Option.bind no …
                                     -- 🎉 no goals
      dsimp [Option.guard]
      -- ⊢ encode (if p a then some a else none) = encode (if h : p a then some { val : …
      by_cases h : p a <;> simp [h]; rfl⟩
      -- ⊢ encode (if p a then some a else none) = encode (if h : p a then some { val : …
                           -- ⊢ encode a = encode { val := a, property := (_ : p a) }
                           -- 🎉 no goals
                                     -- 🎉 no goals
#align primcodable.subtype Primcodable.subtype

instance fin {n} : Primcodable (Fin n) :=
  @ofEquiv _ _ (subtype <| nat_lt.comp .id (const n)) Fin.equivSubtype
#align primcodable.fin Primcodable.fin

instance vector {n} : Primcodable (Vector α n) :=
  subtype ((@Primrec.eq ℕ _ _).comp list_length (const _))
#align primcodable.vector Primcodable.vector

instance finArrow {n} : Primcodable (Fin n → α) :=
  ofEquiv _ (Equiv.vectorEquivFin _ _).symm
#align primcodable.fin_arrow Primcodable.finArrow

-- porting note: Equiv.arrayEquivFin is not ported yet
-- instance array {n} : Primcodable (Array' n α) :=
--   ofEquiv _ (Equiv.arrayEquivFin _ _)
-- #align primcodable.array Primcodable.array

section ULower

attribute [local instance] Encodable.decidableRangeEncode Encodable.decidableEqOfEncodable

theorem mem_range_encode : PrimrecPred (fun n => n ∈ Set.range (encode : α → ℕ)) :=
  have : PrimrecPred fun n => Encodable.decode₂ α n ≠ none :=
    .not
      (Primrec.eq.comp
        (.option_bind .decode
          (.ite (Primrec.eq.comp (Primrec.encode.comp .snd) .fst)
            (Primrec.option_some.comp .snd) (.const _)))
        (.const _))
  this.of_eq fun _ => decode₂_ne_none_iff

instance ulower : Primcodable (ULower α) :=
  Primcodable.subtype mem_range_encode
#align primcodable.ulower Primcodable.ulower

end ULower

end Primcodable

namespace Primrec

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

theorem subtype_val {p : α → Prop} [DecidablePred p] {hp : PrimrecPred p} :
    haveI := Primcodable.subtype hp
    Primrec (@Subtype.val α p) := by
  letI := Primcodable.subtype hp
  -- ⊢ Primrec Subtype.val
  refine' (@Primcodable.prim (Subtype p)).of_eq fun n => _
  -- ⊢ encode (decode n) = encode (Option.map Subtype.val (decode n))
  rcases @decode (Subtype p) _ n with (_ | ⟨a, h⟩) <;> rfl
  -- ⊢ encode none = encode (Option.map Subtype.val none)
                                                       -- 🎉 no goals
                                                       -- 🎉 no goals
#align primrec.subtype_val Primrec.subtype_val

theorem subtype_val_iff {p : β → Prop} [DecidablePred p] {hp : PrimrecPred p} {f : α → Subtype p} :
    haveI := Primcodable.subtype hp
    (Primrec fun a => (f a).1) ↔ Primrec f := by
  letI := Primcodable.subtype hp
  -- ⊢ (Primrec fun a => ↑(f a)) ↔ Primrec f
  refine' ⟨fun h => _, fun hf => subtype_val.comp hf⟩
  -- ⊢ Primrec f
  refine' Nat.Primrec.of_eq h fun n => _
  -- ⊢ encode (Option.map (fun a => ↑(f a)) (decode n)) = encode (Option.map f (dec …
  cases' @decode α _ n with a; · rfl
  -- ⊢ encode (Option.map (fun a => ↑(f a)) none) = encode (Option.map f none)
                                 -- 🎉 no goals
  simp; rfl
  -- ⊢ Nat.succ (encode ↑(f a)) = encode (some (f a))
        -- 🎉 no goals
#align primrec.subtype_val_iff Primrec.subtype_val_iff

theorem subtype_mk {p : β → Prop} [DecidablePred p] {hp : PrimrecPred p} {f : α → β}
    {h : ∀ a, p (f a)} (hf : Primrec f) :
    haveI := Primcodable.subtype hp
    Primrec fun a => @Subtype.mk β p (f a) (h a) :=
  subtype_val_iff.1 hf
#align primrec.subtype_mk Primrec.subtype_mk

theorem option_get {f : α → Option β} {h : ∀ a, (f a).isSome} :
    Primrec f → Primrec fun a => (f a).get (h a) := by
  intro hf
  -- ⊢ Primrec fun a => Option.get (f a) (_ : Option.isSome (f a) = true)
  refine' (Nat.Primrec.pred.comp hf).of_eq fun n => _
  -- ⊢ Nat.pred (encode (Option.map f (decode n))) = encode (Option.map (fun a => O …
  generalize hx : @decode α _ n = x
  -- ⊢ Nat.pred (encode (Option.map f x)) = encode (Option.map (fun a => Option.get …
  cases x <;> simp
  -- ⊢ Nat.pred (encode (Option.map f none)) = encode (Option.map (fun a => Option. …
              -- 🎉 no goals
              -- 🎉 no goals
#align primrec.option_get Primrec.option_get

theorem ulower_down : Primrec (ULower.down : α → ULower α) :=
  letI : ∀ a, Decidable (a ∈ Set.range (encode : α → ℕ)) := decidableRangeEncode _
  subtype_mk .encode

#align primrec.ulower_down Primrec.ulower_down

theorem ulower_up : Primrec (ULower.up : ULower α → α) :=
  letI : ∀ a, Decidable (a ∈ Set.range (encode : α → ℕ)) := decidableRangeEncode _
  option_get (Primrec.decode₂.comp subtype_val)
#align primrec.ulower_up Primrec.ulower_up

theorem fin_val_iff {n} {f : α → Fin n} : (Primrec fun a => (f a).1) ↔ Primrec f := by
  letI : Primcodable { a // id a < n } := Primcodable.subtype (nat_lt.comp .id (const _))
  -- ⊢ (Primrec fun a => ↑(f a)) ↔ Primrec f
  exact (Iff.trans (by rfl) subtype_val_iff).trans (of_equiv_iff _)
  -- 🎉 no goals

#align primrec.fin_val_iff Primrec.fin_val_iff

theorem fin_val {n} : Primrec (fun (i : Fin n) => (i : ℕ)) :=
  fin_val_iff.2 .id
#align primrec.fin_val Primrec.fin_val

theorem fin_succ {n} : Primrec (@Fin.succ n) :=
  fin_val_iff.1 <| by simp [succ.comp fin_val]
                      -- 🎉 no goals
#align primrec.fin_succ Primrec.fin_succ

theorem vector_toList {n} : Primrec (@Vector.toList α n) :=
  subtype_val
#align primrec.vector_to_list Primrec.vector_toList

theorem vector_toList_iff {n} {f : α → Vector β n} : (Primrec fun a => (f a).toList) ↔ Primrec f :=
  subtype_val_iff
#align primrec.vector_to_list_iff Primrec.vector_toList_iff

theorem vector_cons {n} : Primrec₂ (@Vector.cons α n) :=
  vector_toList_iff.1 <| by simp; exact list_cons.comp fst (vector_toList_iff.2 snd)
                            -- ⊢ Primrec fun a => a.fst :: Vector.toList a.snd
                                  -- 🎉 no goals
#align primrec.vector_cons Primrec.vector_cons

theorem vector_length {n} : Primrec (@Vector.length α n) :=
  const _
#align primrec.vector_length Primrec.vector_length

theorem vector_head {n} : Primrec (@Vector.head α n) :=
  option_some_iff.1 <| (list_head?.comp vector_toList).of_eq fun ⟨_ :: _, _⟩ => rfl
#align primrec.vector_head Primrec.vector_head

theorem vector_tail {n} : Primrec (@Vector.tail α n) :=
  vector_toList_iff.1 <| (list_tail.comp vector_toList).of_eq fun ⟨l, h⟩ => by cases l <;> rfl
                                                                               -- ⊢ List.tail (Vector.toList { val := [], property := h }) = Vector.toList (Vect …
                                                                                           -- 🎉 no goals
                                                                                           -- 🎉 no goals
#align primrec.vector_tail Primrec.vector_tail

theorem vector_get {n} : Primrec₂ (@Vector.get α n) :=
  option_some_iff.1 <|
    (list_get?.comp (vector_toList.comp fst) (fin_val.comp snd)).of_eq fun a => by
      rw [Vector.get_eq_get, ← List.get?_eq_get]
      -- ⊢ List.get? (Vector.toList a.fst) ↑a.snd = List.get? (Vector.toList a.fst) ↑(↑ …
      rfl
      -- 🎉 no goals

#align primrec.vector_nth Primrec.vector_get

theorem list_ofFn :
    ∀ {n} {f : Fin n → α → σ}, (∀ i, Primrec (f i)) → Primrec fun a => List.ofFn fun i => f i a
  | 0, _, _ => const []
  | n + 1, f, hf => by
    simp [List.ofFn_succ]; exact list_cons.comp (hf 0) (list_ofFn fun i => hf i.succ)
    -- ⊢ Primrec fun a => f 0 a :: List.ofFn fun i => f (Fin.succ i) a
                           -- 🎉 no goals
#align primrec.list_of_fn Primrec.list_ofFn

theorem vector_ofFn {n} {f : Fin n → α → σ} (hf : ∀ i, Primrec (f i)) :
    Primrec fun a => Vector.ofFn fun i => f i a :=
  vector_toList_iff.1 <| by simp [list_ofFn hf]
                            -- 🎉 no goals
#align primrec.vector_of_fn Primrec.vector_ofFn

theorem vector_get' {n} : Primrec (@Vector.get α n) :=
  of_equiv_symm
#align primrec.vector_nth' Primrec.vector_get'

theorem vector_ofFn' {n} : Primrec (@Vector.ofFn α n) :=
  of_equiv
#align primrec.vector_of_fn' Primrec.vector_ofFn'

theorem fin_app {n} : Primrec₂ (@id (Fin n → σ)) :=
  (vector_get.comp (vector_ofFn'.comp fst) snd).of_eq fun ⟨v, i⟩ => by simp
                                                                       -- 🎉 no goals
#align primrec.fin_app Primrec.fin_app

theorem fin_curry₁ {n} {f : Fin n → α → σ} : Primrec₂ f ↔ ∀ i, Primrec (f i) :=
  ⟨fun h i => h.comp (const i) .id, fun h =>
    (vector_get.comp ((vector_ofFn h).comp snd) fst).of_eq fun a => by simp⟩
                                                                       -- 🎉 no goals
#align primrec.fin_curry₁ Primrec.fin_curry₁

theorem fin_curry {n} {f : α → Fin n → σ} : Primrec f ↔ Primrec₂ f :=
  ⟨fun h => fin_app.comp (h.comp fst) snd, fun h =>
    (vector_get'.comp
          (vector_ofFn fun i => show Primrec fun a => f a i from h.comp .id (const i))).of_eq
      fun a => by funext i; simp⟩
                  -- ⊢ Vector.get (Vector.ofFn fun i => f a i) i = f a i
                            -- 🎉 no goals
#align primrec.fin_curry Primrec.fin_curry

end Primrec

namespace Nat

open Vector

/-- An alternative inductive definition of `Primrec` which
  does not use the pairing function on ℕ, and so has to
  work with n-ary functions on ℕ instead of unary functions.
  We prove that this is equivalent to the regular notion
  in `to_prim` and `of_prim`. -/
inductive Primrec' : ∀ {n}, (Vector ℕ n → ℕ) → Prop
  | zero : @Primrec' 0 fun _ => 0
  | succ : @Primrec' 1 fun v => succ v.head
  | get {n} (i : Fin n) : Primrec' fun v => v.get i
  | comp {m n f} (g : Fin n → Vector ℕ m → ℕ) :
      Primrec' f → (∀ i, Primrec' (g i)) → Primrec' fun a => f (ofFn fun i => g i a)
  | prec {n f g} :
      @Primrec' n f →
        @Primrec' (n + 2) g →
          Primrec' fun v : Vector ℕ (n + 1) =>
            v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)
#align nat.primrec' Nat.Primrec'

end Nat

namespace Nat.Primrec'

open Vector Primrec

theorem to_prim {n f} (pf : @Nat.Primrec' n f) : Primrec f := by
  induction pf
  case zero => exact .const 0
  -- 🎉 no goals
  case succ => exact _root_.Primrec.succ.comp .vector_head
  -- 🎉 no goals
  case get n i => exact Primrec.vector_get.comp .id (.const i)
  -- ⊢ Primrec fun a => f✝ (ofFn fun i => g✝ i a)
  -- 🎉 no goals
  case comp m n f g _ _ hf hg => exact hf.comp (.vector_ofFn fun i => hg i)
  -- ⊢ Primrec fun v => Nat.rec (f✝ (tail v)) (fun y IH => g✝ (y ::ᵥ IH ::ᵥ tail v) …
  -- 🎉 no goals
  case prec n f g _ _ hf hg =>
    exact
      .nat_rec' .vector_head (hf.comp Primrec.vector_tail)
        (hg.comp <|
          Primrec.vector_cons.comp (Primrec.fst.comp .snd) <|
          Primrec.vector_cons.comp (Primrec.snd.comp .snd) <|
            (@Primrec.vector_tail _ _ (n + 1)).comp .fst).to₂
#align nat.primrec'.to_prim Nat.Primrec'.to_prim

theorem of_eq {n} {f g : Vector ℕ n → ℕ} (hf : Primrec' f) (H : ∀ i, f i = g i) : Primrec' g :=
  (funext H : f = g) ▸ hf
#align nat.primrec'.of_eq Nat.Primrec'.of_eq

theorem const {n} : ∀ m, @Primrec' n fun _ => m
  | 0 => zero.comp Fin.elim0 fun i => i.elim0
  | m + 1 => succ.comp _ fun _ => const m
#align nat.primrec'.const Nat.Primrec'.const

theorem head {n : ℕ} : @Primrec' n.succ head :=
  (get 0).of_eq fun v => by simp [get_zero]
                            -- 🎉 no goals
#align nat.primrec'.head Nat.Primrec'.head

theorem tail {n f} (hf : @Primrec' n f) : @Primrec' n.succ fun v => f v.tail :=
  (hf.comp _ fun i => @get _ i.succ).of_eq fun v => by
    rw [← ofFn_get v.tail]; congr; funext i; simp
    -- ⊢ f (ofFn fun i => Vector.get v (Fin.succ i)) = f (ofFn (Vector.get (Vector.ta …
                            -- ⊢ (fun i => Vector.get v (Fin.succ i)) = Vector.get (Vector.tail v)
                                   -- ⊢ Vector.get v (Fin.succ i) = Vector.get (Vector.tail v) i
                                             -- 🎉 no goals
#align nat.primrec'.tail Nat.Primrec'.tail

/-- A function from vectors to vectors is primitive recursive when all of its projections are. -/
def Vec {n m} (f : Vector ℕ n → Vector ℕ m) : Prop :=
  ∀ i, Primrec' fun v => (f v).get i
#align nat.primrec'.vec Nat.Primrec'.Vec

protected theorem nil {n} : @Vec n 0 fun _ => nil := fun i => i.elim0
#align nat.primrec'.nil Nat.Primrec'.nil

protected theorem cons {n m f g} (hf : @Primrec' n f) (hg : @Vec n m g) :
    Vec fun v => f v ::ᵥ g v := fun i => Fin.cases (by simp [*]) (fun i => by simp [hg i]) i
                                                       -- 🎉 no goals
                                                                              -- 🎉 no goals
#align nat.primrec'.cons Nat.Primrec'.cons

theorem idv {n} : @Vec n n id :=
  get
#align nat.primrec'.idv Nat.Primrec'.idv

theorem comp' {n m f g} (hf : @Primrec' m f) (hg : @Vec n m g) : Primrec' fun v => f (g v) :=
  (hf.comp _ hg).of_eq fun v => by simp
                                   -- 🎉 no goals
#align nat.primrec'.comp' Nat.Primrec'.comp'

theorem comp₁ (f : ℕ → ℕ) (hf : @Primrec' 1 fun v => f v.head) {n g} (hg : @Primrec' n g) :
    Primrec' fun v => f (g v) :=
  hf.comp _ fun _ => hg
#align nat.primrec'.comp₁ Nat.Primrec'.comp₁

theorem comp₂ (f : ℕ → ℕ → ℕ) (hf : @Primrec' 2 fun v => f v.head v.tail.head) {n g h}
    (hg : @Primrec' n g) (hh : @Primrec' n h) : Primrec' fun v => f (g v) (h v) := by
  simpa using hf.comp' (hg.cons <| hh.cons Primrec'.nil)
  -- 🎉 no goals
#align nat.primrec'.comp₂ Nat.Primrec'.comp₂

theorem prec' {n f g h} (hf : @Primrec' n f) (hg : @Primrec' n g) (hh : @Primrec' (n + 2) h) :
    @Primrec' n fun v => (f v).rec (g v) fun y IH : ℕ => h (y ::ᵥ IH ::ᵥ v) := by
  simpa using comp' (prec hg hh) (hf.cons idv)
  -- 🎉 no goals
#align nat.primrec'.prec' Nat.Primrec'.prec'

theorem pred : @Primrec' 1 fun v => v.head.pred :=
  (prec' head (const 0) head).of_eq fun v => by simp; cases v.head <;> rfl
                                                -- ⊢ Nat.rec 0 (fun y IH => y) (Vector.head v) = Nat.pred (Vector.head v)
                                                      -- ⊢ Nat.rec 0 (fun y IH => y) Nat.zero = Nat.pred Nat.zero
                                                                       -- 🎉 no goals
                                                                       -- 🎉 no goals
#align nat.primrec'.pred Nat.Primrec'.pred

theorem add : @Primrec' 2 fun v => v.head + v.tail.head :=
  (prec head (succ.comp₁ _ (tail head))).of_eq fun v => by
    simp; induction v.head <;> simp [*, Nat.succ_add]
    -- ⊢ Nat.rec (Vector.head (Vector.tail v)) (fun y IH => Nat.succ IH) (Vector.head …
          -- ⊢ Nat.rec (Vector.head (Vector.tail v)) (fun y IH => Nat.succ IH) Nat.zero = N …
                               -- 🎉 no goals
                               -- 🎉 no goals
#align nat.primrec'.add Nat.Primrec'.add

theorem sub : @Primrec' 2 fun v => v.head - v.tail.head := by
  suffices; simpa using comp₂ (fun a b => b - a) this (tail head) head
  -- ⊢ Primrec' fun v => Vector.head v - Vector.head (Vector.tail v)
            -- ⊢ Primrec' fun v => (fun a b => b - a) (Vector.head v) (Vector.head (Vector.ta …
  refine' (prec head (pred.comp₁ _ (tail head))).of_eq fun v => _
  -- ⊢ Nat.rec (Vector.head (Vector.tail v)) (fun y IH => Nat.pred (Vector.head (Ve …
  simp; induction v.head <;> simp [*, Nat.sub_succ]
  -- ⊢ Nat.rec (Vector.head (Vector.tail v)) (fun y IH => Nat.pred IH) (Vector.head …
        -- ⊢ Nat.rec (Vector.head (Vector.tail v)) (fun y IH => Nat.pred IH) Nat.zero = V …
                             -- 🎉 no goals
                             -- 🎉 no goals
#align nat.primrec'.sub Nat.Primrec'.sub

theorem mul : @Primrec' 2 fun v => v.head * v.tail.head :=
  (prec (const 0) (tail (add.comp₂ _ (tail head) head))).of_eq fun v => by
    simp; induction v.head <;> simp [*, Nat.succ_mul]; rw [add_comm]
    -- ⊢ Nat.rec 0 (fun y IH => Vector.head (Vector.tail v) + IH) (Vector.head v) = V …
          -- ⊢ Nat.rec 0 (fun y IH => Vector.head (Vector.tail v) + IH) Nat.zero = Nat.zero …
                               -- 🎉 no goals
                               -- ⊢ Vector.head (Vector.tail v) + n✝ * Vector.head (Vector.tail v) = n✝ * Vector …
                                                       -- 🎉 no goals
#align nat.primrec'.mul Nat.Primrec'.mul

theorem if_lt {n a b f g} (ha : @Primrec' n a) (hb : @Primrec' n b) (hf : @Primrec' n f)
    (hg : @Primrec' n g) : @Primrec' n fun v => if a v < b v then f v else g v :=
  (prec' (sub.comp₂ _ hb ha) hg (tail <| tail hf)).of_eq fun v => by
    cases e : b v - a v
    -- ⊢ Nat.rec (g v) (fun y IH => f (Vector.tail (Vector.tail (y ::ᵥ IH ::ᵥ v)))) N …
    · simp [not_lt.2 (tsub_eq_zero_iff_le.mp e)]
      -- 🎉 no goals
    · simp [Nat.lt_of_sub_eq_succ e]
      -- 🎉 no goals
#align nat.primrec'.if_lt Nat.Primrec'.if_lt

theorem natPair : @Primrec' 2 fun v => v.head.pair v.tail.head :=
  if_lt head (tail head) (add.comp₂ _ (tail <| mul.comp₂ _ head head) head)
    (add.comp₂ _ (add.comp₂ _ (mul.comp₂ _ head head) head) (tail head))
#align nat.primrec'.mkpair Nat.Primrec'.natPair

protected theorem encode : ∀ {n}, @Primrec' n encode
  | 0 => (const 0).of_eq fun v => by rw [v.eq_nil]; rfl
                                     -- ⊢ 0 = encode nil
                                                    -- 🎉 no goals
  | n + 1 =>
    (succ.comp₁ _ (natPair.comp₂ _ head (tail Primrec'.encode))).of_eq fun ⟨a :: l, e⟩ => rfl
#align nat.primrec'.encode Nat.Primrec'.encode

theorem sqrt : @Primrec' 1 fun v => v.head.sqrt := by
  suffices H : ∀ n : ℕ, n.sqrt = n.rec 0 fun x y => if x.succ < y.succ * y.succ then y else y.succ
  -- ⊢ Primrec' fun v => Nat.sqrt (Vector.head v)
  · simp [H]
    -- ⊢ Primrec' fun v => Nat.rec 0 (fun x y => if Nat.succ x < Nat.succ y * Nat.suc …
    have :=
      @prec' 1 _ _
        (fun v => by
          have x := v.head; have y := v.tail.head;
            exact if x.succ < y.succ * y.succ then y else y.succ)
        head (const 0) ?_
    · exact this
      -- 🎉 no goals
    have x1 : @Primrec' 3 fun v => v.head.succ := succ.comp₁ _ head
    -- ⊢ Primrec' fun v =>
    have y1 : @Primrec' 3 fun v => v.tail.head.succ := succ.comp₁ _ (tail head)
    -- ⊢ Primrec' fun v =>
    exact if_lt x1 (mul.comp₂ _ y1 y1) (tail head) y1
    -- 🎉 no goals
  introv; symm
  -- ⊢ Nat.sqrt n = Nat.rec 0 (fun x y => if Nat.succ x < Nat.succ y * Nat.succ y t …
          -- ⊢ Nat.rec 0 (fun x y => if Nat.succ x < Nat.succ y * Nat.succ y then y else Na …
  induction' n with n IH; · simp
  -- ⊢ Nat.rec 0 (fun x y => if Nat.succ x < Nat.succ y * Nat.succ y then y else Na …
                            -- 🎉 no goals
  dsimp; rw [IH]; split_ifs with h
  -- ⊢ (if Nat.succ n < Nat.succ (Nat.rec 0 (fun x y => if Nat.succ x < Nat.succ y  …
         -- ⊢ (if Nat.succ n < Nat.succ (Nat.sqrt n) * Nat.succ (Nat.sqrt n) then Nat.sqrt …
                  -- ⊢ Nat.sqrt n = Nat.sqrt (Nat.succ n)
  · exact le_antisymm (Nat.sqrt_le_sqrt (Nat.le_succ _)) (Nat.lt_succ_iff.1 <| Nat.sqrt_lt.2 h)
    -- 🎉 no goals
  · exact
      Nat.eq_sqrt.2 ⟨not_lt.1 h, Nat.sqrt_lt.1 <| Nat.lt_succ_iff.2 <| Nat.sqrt_succ_le_succ_sqrt _⟩
#align nat.primrec'.sqrt Nat.Primrec'.sqrt

theorem unpair₁ {n f} (hf : @Primrec' n f) : @Primrec' n fun v => (f v).unpair.1 := by
  have s := sqrt.comp₁ _ hf
  -- ⊢ Primrec' fun v => (unpair (f v)).fst
  have fss := sub.comp₂ _ hf (mul.comp₂ _ s s)
  -- ⊢ Primrec' fun v => (unpair (f v)).fst
  refine' (if_lt fss s fss s).of_eq fun v => _
  -- ⊢ (if f v - Nat.sqrt (f v) * Nat.sqrt (f v) < Nat.sqrt (f v) then f v - Nat.sq …
  simp [Nat.unpair]; split_ifs <;> rfl
  -- ⊢ (if f v - Nat.sqrt (f v) * Nat.sqrt (f v) < Nat.sqrt (f v) then f v - Nat.sq …
                     -- ⊢ f v - Nat.sqrt (f v) * Nat.sqrt (f v) = (f v - Nat.sqrt (f v) * Nat.sqrt (f  …
                                   -- 🎉 no goals
                                   -- 🎉 no goals
#align nat.primrec'.unpair₁ Nat.Primrec'.unpair₁

theorem unpair₂ {n f} (hf : @Primrec' n f) : @Primrec' n fun v => (f v).unpair.2 := by
  have s := sqrt.comp₁ _ hf
  -- ⊢ Primrec' fun v => (unpair (f v)).snd
  have fss := sub.comp₂ _ hf (mul.comp₂ _ s s)
  -- ⊢ Primrec' fun v => (unpair (f v)).snd
  refine' (if_lt fss s s (sub.comp₂ _ fss s)).of_eq fun v => _
  -- ⊢ (if f v - Nat.sqrt (f v) * Nat.sqrt (f v) < Nat.sqrt (f v) then Nat.sqrt (f  …
  simp [Nat.unpair]; split_ifs <;> rfl
  -- ⊢ (if f v - Nat.sqrt (f v) * Nat.sqrt (f v) < Nat.sqrt (f v) then Nat.sqrt (f  …
                     -- ⊢ Nat.sqrt (f v) = (f v - Nat.sqrt (f v) * Nat.sqrt (f v), Nat.sqrt (f v)).snd
                                   -- 🎉 no goals
                                   -- 🎉 no goals
#align nat.primrec'.unpair₂ Nat.Primrec'.unpair₂

theorem of_prim {n f} : Primrec f → @Primrec' n f :=
  suffices ∀ f, Nat.Primrec f → @Primrec' 1 fun v => f v.head from fun hf =>
    (pred.comp₁ _ <|
          (this _ hf).comp₁ (fun m => Encodable.encode <| (@decode (Vector ℕ n) _ m).map f)
            Primrec'.encode).of_eq
      fun i => by simp [encodek]
                  -- 🎉 no goals
  fun f hf => by
  induction hf
  -- 🎉 no goals
  case zero => exact const 0
  -- 🎉 no goals
  case succ => exact succ
  -- 🎉 no goals
  case left => exact unpair₁ head
  -- 🎉 no goals
  case right => exact unpair₂ head
  -- ⊢ Primrec' fun v => (fun n => f✝ (g✝ n)) (Vector.head v)
  -- 🎉 no goals
  case pair f g _ _ hf hg => exact natPair.comp₂ _ hf hg
  -- ⊢ Primrec' fun v => unpaired (fun z n => Nat.rec (f✝ z) (fun y IH => g✝ (pair  …
  -- 🎉 no goals
  case comp f g _ _ hf hg => exact hf.comp₁ _ hg
  case prec f g _ _ hf hg =>
    simpa using
      prec' (unpair₂ head) (hf.comp₁ _ (unpair₁ head))
        (hg.comp₁ _ <|
          natPair.comp₂ _ (unpair₁ <| tail <| tail head) (natPair.comp₂ _ head (tail head)))
#align nat.primrec'.of_prim Nat.Primrec'.of_prim

theorem prim_iff {n f} : @Primrec' n f ↔ Primrec f :=
  ⟨to_prim, of_prim⟩
#align nat.primrec'.prim_iff Nat.Primrec'.prim_iff

theorem prim_iff₁ {f : ℕ → ℕ} : (@Primrec' 1 fun v => f v.head) ↔ Primrec f :=
  prim_iff.trans
    ⟨fun h => (h.comp <| .vector_ofFn fun _ => .id).of_eq fun v => by simp, fun h =>
                                                                      -- 🎉 no goals
      h.comp .vector_head⟩
#align nat.primrec'.prim_iff₁ Nat.Primrec'.prim_iff₁

theorem prim_iff₂ {f : ℕ → ℕ → ℕ} : (@Primrec' 2 fun v => f v.head v.tail.head) ↔ Primrec₂ f :=
  prim_iff.trans
    ⟨fun h => (h.comp <| Primrec.vector_cons.comp .fst <|
      Primrec.vector_cons.comp .snd (.const nil)).of_eq fun v => by simp,
                                                                    -- 🎉 no goals
    fun h => h.comp .vector_head (Primrec.vector_head.comp .vector_tail)⟩
#align nat.primrec'.prim_iff₂ Nat.Primrec'.prim_iff₂

theorem vec_iff {m n f} : @Vec m n f ↔ Primrec f :=
  ⟨fun h => by simpa using Primrec.vector_ofFn fun i => to_prim (h i), fun h i =>
               -- 🎉 no goals
    of_prim <| Primrec.vector_get.comp h (.const i)⟩
#align nat.primrec'.vec_iff Nat.Primrec'.vec_iff

end Nat.Primrec'

theorem Primrec.nat_sqrt : Primrec Nat.sqrt :=
  Nat.Primrec'.prim_iff₁.1 Nat.Primrec'.sqrt
#align primrec.nat_sqrt Primrec.nat_sqrt
