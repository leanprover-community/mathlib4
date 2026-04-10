/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/
module

public import Mathlib.Computability.Partrec
public import Mathlib.Order.Antisymmetrization

/-!
# Oracle computability

This file defines oracle computability using partial recursive functions.

## Main definitions

* `Nat.RecursiveIn O f`: A partial function `f : ℕ →. ℕ` is partial recursive given access to
  oracles in the set `O`.
* `RecursiveIn O f`: Lifts `Nat.RecursiveIn` to partial functions between `Primcodable` types.
* `ComputableIn O f`: A total function `f : α → σ` is computable given access to oracles in `O`.

## Main results

* `Nat.Partrec.recursiveIn`: Every partial recursive function is recursive in any oracle set.
* `partrec_iff_forall_recursiveIn_singleton`: A function is partial recursive iff it is recursive
  in every singleton oracle set.
* `recursiveIn_empty_iff`: Being recursive in the empty set is equivalent to being
  partial recursive.
* `RecursiveIn.mono`: Monotonicity of `RecursiveIn` with respect to oracle sets.

## Implementation notes

The type of partial functions recursive in a set of oracles `O` is the smallest type containing
the constant zero, the successor, left and right projections, each oracle `g ∈ O`,
and is closed under pairing, composition, primitive recursion, and μ-recursion.

## References

* [Piergiorgio Odifreddi,
  *Classical Recursion Theory: The Theory of Functions and Sets of Natural
  Numbers*][odifreddi1989]

## Tags

Computability, Oracle, Turing Degrees, Reducibility, Equivalence Relation
-/

@[expose] public section

open Encodable Primrec Nat.Partrec Part

variable {α β γ σ : Type*}

namespace Nat

/--
The type of partial functions recursive in a set of oracles `O` is the smallest type containing
the constant zero, the successor, left and right projections, each oracle `g ∈ O`,
and is closed under pairing, composition, primitive recursion, and μ-recursion.
-/
protected inductive RecursiveIn (O : Set (ℕ →. ℕ)) : (ℕ →. ℕ) → Prop
  | zero : Nat.RecursiveIn O fun _ => 0
  | succ : Nat.RecursiveIn O Nat.succ
  | left : Nat.RecursiveIn O fun n => (Nat.unpair n).1
  | right : Nat.RecursiveIn O fun n => (Nat.unpair n).2
  | oracle : ∀ g ∈ O, Nat.RecursiveIn O g
  | pair {f h : ℕ →. ℕ} (hf : Nat.RecursiveIn O f) (hh : Nat.RecursiveIn O h) :
      Nat.RecursiveIn O fun n => (Nat.pair <$> f n <*> h n)
  | comp {f h : ℕ →. ℕ} (hf : Nat.RecursiveIn O f) (hh : Nat.RecursiveIn O h) :
      Nat.RecursiveIn O fun n => h n >>= f
  | prec {f h : ℕ →. ℕ} (hf : Nat.RecursiveIn O f) (hh : Nat.RecursiveIn O h) :
      Nat.RecursiveIn O fun p =>
        let (a, n) := Nat.unpair p
        n.rec (f a) fun y IH => do
          let i ← IH
          h (Nat.pair a (Nat.pair y i))
  | rfind {f : ℕ →. ℕ} (hf : Nat.RecursiveIn O f) :
      Nat.RecursiveIn O fun a =>
        Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a n)

end Nat

/-- A partial function `f : α →. σ` between `Primcodable` types is recursive in a set of oracles
`O` if its encoding as a function `ℕ →. ℕ` is `Nat.RecursiveIn O`. -/
def RecursiveIn {α σ} [Primcodable α] [Primcodable σ] (O : Set (ℕ →. ℕ)) (f : α →. σ) : Prop :=
  Nat.RecursiveIn O fun n => Part.bind (decode (α := α) n) fun a => (f a).map encode

lemma RecursiveIn.iff_nat {f : ℕ →. ℕ} {O} : RecursiveIn O f ↔ Nat.RecursiveIn O f := by
  simp [RecursiveIn, Part.map_id']

/-- A binary partial function is recursive in `O` if the curried form is. -/
def RecursiveIn₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    (O : Set (ℕ →. ℕ)) (f : α → β →. σ) : Prop :=
  RecursiveIn O (fun p : α × β => f p.1 p.2)

/-- A total function is computable in `O` if its constant lift is recursive in `O`. -/
def ComputableIn {α σ} [Primcodable α] [Primcodable σ] (O : Set (ℕ →. ℕ)) (f : α → σ) : Prop :=
  RecursiveIn O (fun a => Part.some (f a))

/-- A binary total function is computable in `O`. -/
def ComputableIn₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    (O : Set (ℕ →. ℕ)) (f : α → β → σ) : Prop :=
  ComputableIn O (fun p : α × β => f p.1 p.2)

namespace Nat.RecursiveIn

variable {f g : ℕ →. ℕ}

theorem of_eq {O} (hf : Nat.RecursiveIn O f) (H : ∀ n, f n = g n) :
    Nat.RecursiveIn O g :=
  (funext H : f = g) ▸ hf

theorem of_eq_tot {g : ℕ → ℕ} {O} (hf : Nat.RecursiveIn O f)
    (H : ∀ n, g n ∈ f n) : Nat.RecursiveIn O g :=
  of_eq hf fun n => eq_some_iff.2 (H n)

/-- If every element of `O` is `Nat.RecursiveIn O'`, then any function which is
`Nat.RecursiveIn O` is also `Nat.RecursiveIn O'`. -/
theorem subst {O O'} {f : ℕ →. ℕ} (hf : Nat.RecursiveIn O f)
    (hO : ∀ g, g ∈ O → Nat.RecursiveIn O' g) : Nat.RecursiveIn O' f := by
  induction hf with
  | zero | succ | left | right => constructor
  | oracle g hg => exact hO g hg
  | pair _ _ ihf ihg => exact .pair ihf ihg
  | comp _ _ ihf ihg => exact .comp ihf ihg
  | prec _ _ ihf ihg => exact .prec ihf ihg
  | rfind _ ihf => exact .rfind ihf

/-- If every function in `O` is partial recursive,
then a function which is `Nat.RecursiveIn O` is also partial recursive. -/
theorem partrec_of_oracle {f : ℕ →. ℕ} {O}
    (hO : ∀ g ∈ O, Nat.Partrec g) (hf : Nat.RecursiveIn O f) : Nat.Partrec f := by
  induction hf with
  | zero | succ | left | right => constructor
  | oracle g gIn => exact hO g gIn
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact .prec ih₁ ih₂
  | rfind _ ih => exact .rfind ih

end Nat.RecursiveIn

/-- If a function is partial recursive, then it is recursive in every partial function. -/
lemma Nat.Partrec.recursiveIn {f : ℕ →. ℕ} {O} (pF : Nat.Partrec f) :
    Nat.RecursiveIn O f := by
  induction pF with
  | zero | succ | left | right => constructor
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact .prec ih₁ ih₂
  | rfind _ ih => exact .rfind ih

/-- If a partial function is partial recursive, then it is `RecursiveIn` any oracle set. -/
lemma Partrec.recursiveIn [Primcodable α] [Primcodable σ] {f : α →. σ} {O}
    (hf : Partrec f) : RecursiveIn O f :=
  Nat.Partrec.recursiveIn hf

theorem Nat.Primrec.recursiveIn {O} {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    Nat.RecursiveIn O (fun n => f n) :=
  Nat.Partrec.recursiveIn (Nat.Partrec.of_primrec hf)

theorem Computable.computableIn [Primcodable α] [Primcodable β] {f : α → β} {O}
    (hf : Computable f) : ComputableIn O f :=
  hf.partrec.recursiveIn

theorem Primrec.computableIn [Primcodable α] [Primcodable σ]
    {f : α → σ} {O} (hf : Primrec f) : ComputableIn O f :=
  (Primrec.to_comp hf).computableIn

nonrec theorem Primrec₂.computableIn₂ [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → β → σ} {O} (hf : Primrec₂ f) : ComputableIn₂ O f :=
  hf.computableIn

protected theorem ComputableIn.recursiveIn [Primcodable α] [Primcodable σ]
    {f : α → σ} {O} (hf : ComputableIn O f) :
    RecursiveIn O (fun a => Part.some (f a)) := hf

protected theorem ComputableIn₂.recursiveIn₂ [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → β → σ} {O} (hf : ComputableIn₂ O f) :
    RecursiveIn₂ O fun a => (f a : β →. σ) := hf

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]
variable {f : α →. σ} {O : Set (ℕ →. ℕ)}

namespace RecursiveIn

lemma of_eq {f g : α →. σ} (hf : RecursiveIn O f)
    (H : ∀ x, f x = g x) : RecursiveIn O g :=
  (funext H : f = g) ▸ hf

lemma of_eq_tot {f : α →. σ} {g : α → σ}
    (hf : RecursiveIn O f) (H : ∀ n, g n ∈ f n) : RecursiveIn O (g : α →. σ) :=
  of_eq hf fun n => eq_some_iff.2 (H n)

lemma oracle : ∀ g ∈ O, RecursiveIn O g := by
  intro g hg; rw [iff_nat]; exact .oracle g hg

protected theorem some : RecursiveIn O (Part.some : α →. α) :=
  Partrec.some.recursiveIn

protected theorem none : RecursiveIn O (fun _ : α => (Part.none : Part σ)) :=
  Partrec.none.recursiveIn

/-- If every element of `O` is `RecursiveIn O'`, then any function which is
`RecursiveIn O` is also `RecursiveIn O'`. -/
theorem subst {O O'} {f : α →. σ} (hf : RecursiveIn O f)
    (hO : ∀ g, g ∈ O → RecursiveIn O' g) : RecursiveIn O' f :=
  Nat.RecursiveIn.subst hf (by simpa only [RecursiveIn.iff_nat] using hO)

/-- Monotonicity of `RecursiveIn` with respect to oracle sets. -/
@[gcongr]
theorem mono {O₁ O₂} (hsub : O₁ ⊆ O₂) (hf : RecursiveIn O₁ f) : RecursiveIn O₂ f :=
  hf.subst (fun g hg => .oracle g (hsub hg))

/-- If every function in `O` is partial recursive,
then a function which is `RecursiveIn O` is also partial recursive. -/
theorem partrec_of_oracle
    (hO : ∀ g ∈ O, Partrec g) (hf : RecursiveIn O f) : Partrec f :=
  Nat.RecursiveIn.partrec_of_oracle (by simpa only [Partrec.nat_iff] using hO) hf

/-- If a function is recursive in a constant partial function, then it is partial recursive. -/
lemma partrec_of_const {s} (hf : RecursiveIn {fun _ => s} f) : Partrec f :=
  hf.partrec_of_oracle
    (fun g hg => by rw [Set.mem_singleton_iff.mp hg]; exact .const' s)

end RecursiveIn

@[simp]
lemma recursiveIn_empty_iff :
    RecursiveIn {} f ↔ Partrec f :=
  ⟨fun hf => hf.partrec_of_oracle (Set.forall_mem_empty.mpr ⟨⟩), fun hf => hf.recursiveIn⟩

/-- A partial function `f` is partial recursive if and only if it is recursive in
every partial function `g`. -/
theorem partrec_iff_forall_recursiveIn_singleton :
    Partrec f ↔ ∀ g, RecursiveIn {g} f :=
  ⟨fun hf _ => hf.recursiveIn, fun hf => (hf (fun _ => .none)).partrec_of_const⟩

namespace ComputableIn

protected theorem const (s : σ) : ComputableIn O (fun _ : α => s) :=
  (Primrec.const s).computableIn

protected theorem id : ComputableIn O (@id α) :=
  Primrec.id.computableIn

protected theorem fst : ComputableIn O (@Prod.fst α β) :=
  Primrec.fst.computableIn

protected theorem snd : ComputableIn O (@Prod.snd α β) :=
  Primrec.snd.computableIn

protected theorem unpair : ComputableIn O Nat.unpair :=
  Primrec.unpair.computableIn

protected theorem succ : ComputableIn O Nat.succ :=
  Primrec.succ.computableIn

protected theorem sumInl : ComputableIn O (@Sum.inl α β) :=
  Primrec.sumInl.computableIn

protected theorem sumInr : ComputableIn O (@Sum.inr α β) :=
  Primrec.sumInr.computableIn

end ComputableIn

section RecursiveInCond

variable {O : Set (ℕ →. ℕ)}

theorem Nat.RecursiveIn.of_primrec {f : ℕ → ℕ}
    (hf : Nat.Primrec f) : Nat.RecursiveIn O ↑f :=
  Nat.Partrec.recursiveIn (Nat.Partrec.of_primrec hf)

theorem Nat.RecursiveIn.of_partrec {f : ℕ →. ℕ}
    (hf : Nat.Partrec f) : Nat.RecursiveIn O f :=
  Nat.Partrec.recursiveIn hf

theorem Nat.RecursiveIn.div2 :
    Nat.RecursiveIn O (fun n => Nat.div2 n : ℕ → ℕ) :=
  Nat.Primrec.recursiveIn (Primrec.nat_iff.1 Primrec.nat_div2)

theorem Nat.RecursiveIn.double :
    Nat.RecursiveIn O (fun n => 2 * n : ℕ → ℕ) :=
  Nat.Primrec.recursiveIn (Primrec.nat_iff.1 Primrec.nat_double)

theorem Nat.RecursiveIn.double_add_one :
    Nat.RecursiveIn O (fun n => 2 * n + 1 : ℕ → ℕ) :=
  Nat.Primrec.recursiveIn
    (Primrec.nat_iff.1 Primrec.nat_double_succ)

theorem Nat.RecursiveIn.comp_at_even {h : ℕ →. ℕ}
    (hh : Nat.RecursiveIn O h) :
    Nat.RecursiveIn O (fun n => h (2 * n)) :=
  (hh.comp .double).of_eq fun _ => by simp [Part.bind_some]

theorem Nat.RecursiveIn.comp_at_odd {h : ℕ →. ℕ}
    (hh : Nat.RecursiveIn O h) :
    Nat.RecursiveIn O (fun n => h (2 * n + 1)) :=
  (hh.comp .double_add_one).of_eq fun _ => by
    simp [Part.bind_some]

theorem Nat.RecursiveIn.encode_even {h : ℕ →. ℕ}
    (hh : Nat.RecursiveIn O h) : Nat.RecursiveIn O (fun n =>
      (Nat.div2 n : ℕ) >>= h >>= fun y => (2 * y : ℕ)) :=
  (Nat.RecursiveIn.double.comp (hh.comp .div2)).of_eq
    fun _ => by congr

theorem Nat.RecursiveIn.encode_odd {h : ℕ →. ℕ}
    (hh : Nat.RecursiveIn O h) : Nat.RecursiveIn O (fun n =>
      (Nat.div2 n : ℕ) >>= h >>= fun y => (2 * y + 1 : ℕ)) :=
  (Nat.RecursiveIn.double_add_one.comp (hh.comp .div2)).of_eq
    fun _ => by congr

namespace Nat.RecursiveIn

variable {O : Set (ℕ →. ℕ)}

/-- Conditional with a computable guard and constant fallback. -/
theorem cond_const {c : ℕ → Bool} {f : ℕ →. ℕ}
    (hc : Computable c) (hf : Nat.RecursiveIn O f) (k : ℕ) :
    Nat.RecursiveIn O
      (fun n => bif c n then f n else Part.some k) := by
  have hid := @of_primrec O _ (.id : Nat.Primrec _)
  have hcode := @of_partrec O _
    (Partrec.nat_iff.1 (Computable.encode.comp hc).partrec)
  refine (comp (prec (of_primrec (.const k))
    ((comp hf left).of_eq fun _ => by aesop))
    (pair hid hcode)).of_eq fun n => ?_
  cases h : c n <;> simp [Seq.seq, Nat.unpair_pair] <;> aesop

private def eqTest (h : ℕ →. ℕ) : ℕ →. ℕ := fun p =>
  ((Nat.pair <$> ((fun n => n.unpair.1) p >>= h) <*>
      (fun n => n.unpair.2) p) >>= Partrec.kronecker) >>=
    fun m => Part.some (1 - m)

private theorem eqTest_recursiveIn {h : ℕ →. ℕ}
    (hh : Nat.RecursiveIn O h) :
    Nat.RecursiveIn O (eqTest h) :=
  ((@of_partrec O _ (Nat.Partrec.of_primrec
      (.comp .sub (.pair (.const 1) .id)))).comp
    ((@of_partrec O _ Partrec.kronecker_partrec).comp
      ((hh.comp .left).pair .right))).of_eq
    fun _ => by simp [eqTest]; congr

private def condCmp (c : ℕ → Bool) (f g : ℕ →. ℕ) : ℕ →. ℕ := fun p =>
  (Nat.pair <$>
    (bif c p.unpair.1 then eqTest f p else Part.some 1) <*>
    (bif !c p.unpair.1 then eqTest g p else Part.some 1)) >>=
    fun q => Part.some (q.unpair.1 * q.unpair.2)

private theorem condCmp_recursiveIn {c : ℕ → Bool} {f g : ℕ →. ℕ}
    (hc : Computable c)
    (hf : Nat.RecursiveIn O f) (hg : Nat.RecursiveIn O g) :
    Nat.RecursiveIn O (condCmp c f g) := by
  have hc1 := hc.comp (Computable.fst.comp Computable.unpair)
  have hmul := @of_partrec O _ ((Nat.Partrec.of_primrec
    .mul).of_eq fun _ => by aesop)
  exact (comp hmul (pair
    ((cond_const hc1 (eqTest_recursiveIn hf) 1).of_eq
      fun _ => by aesop)
    ((cond_const (Primrec.not.to_comp.comp hc1)
      (eqTest_recursiveIn hg) 1).of_eq
      fun _ => by aesop))).of_eq fun _ => by
    simp [condCmp]

private theorem rfind_eqTest_eq (v cmp : ℕ →. ℕ) (n : ℕ)
    (hv : ∀ k, (fun m => decide (m = 0)) <$> cmp (n.pair k) =
      (fun m => decide (m = 0)) <$> eqTest v (n.pair k)) :
    (Nat.rfind fun k => (fun m => decide (m = 0)) <$>
      cmp (n.pair k)) = v n := by
  rw [show _ = fun k => _ <$> eqTest v (n.pair k)
    from funext hv]
  convert Partrec.kronecker_rfind (v := v n) using 1
  simp [eqTest, Nat.unpair_pair, Seq.seq,
    Part.map_eq_map, Part.bind_some_eq_map]

/-- `Nat.RecursiveIn O` is closed under conditionals. -/
theorem cond' {c : ℕ → Bool} {f g : ℕ →. ℕ}
    (hc : Computable c) (hf : Nat.RecursiveIn O f)
    (hg : Nat.RecursiveIn O g) :
    Nat.RecursiveIn O (fun n => cond (c n) (f n) (g n)) := by
  refine (rfind (condCmp_recursiveIn hc hf hg)).of_eq fun n => ?_
  cases hn : c n <;>
    exact rfind_eqTest_eq _ _ n fun k => by
      simp [condCmp, eqTest, hn, Nat.unpair_pair, Seq.seq,
        Part.bind_assoc, Part.bind_some]

end Nat.RecursiveIn
