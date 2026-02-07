/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/

module

public import Mathlib.Computability.Partrec
public import Mathlib.Order.Antisymmetrization

/-!
# Oracle Computability

This file defines oracle computability using partial recursive functions with access to oracles.

## Main Definitions

* `RecursiveIn O f`: A partial function `f : ℕ →. ℕ` is partial recursive given access to oracles
  in the set `O`.
* `Nat.PrimrecIn O f`: A total function `f : ℕ → ℕ` is primitive recursive relative to oracles
  in the set `O`.
* `RecursiveIn' O f`: Lifts `RecursiveIn` to partial functions between `Primcodable` types.
* `ComputableIn O f`: A total function `f : α → σ` is computable given access to oracles in `O`.

## Main Results

* `Nat.Partrec.recursiveIn`: Every partial recursive function is recursive in any oracle set.
* `partrec_iff_forall_recursiveIn`: A function is partial recursive iff it is recursive in every
  singleton oracle set.
* `recursiveIn_empty_iff_partrec`: Being recursive in the empty set is equivalent to being
  partial recursive.
* `RecursiveIn.mono`: Monotonicity of `RecursiveIn` with respect to oracle sets.

## Implementation Notes

The type of partial functions recursive in a set of oracles `O` is the smallest type containing
the constant zero, the successor, left and right projections, each oracle `g ∈ O`,
and is closed under pairing, composition, primitive recursion, and μ-recursion.

## References

* [Odifreddi1989] Odifreddi, Piergiorgio.
  *Classical Recursion Theory: The Theory of Functions and Sets of Natural Numbers,
  Vol. I*. Springer-Verlag, 1989.

## Tags

Computability, Oracle, Turing Degrees, Reducibility, Equivalence Relation
-/

@[expose] public section

open Encodable Primrec Nat.Partrec Part

variable {f g h : ℕ →. ℕ} {O : Set (ℕ →. ℕ)} {α β γ σ : Type*}

/--
The type of partial functions recursive in a set of oracles `O` is the smallest type containing
the constant zero, the successor, left and right projections, each oracle `g ∈ O`,
and is closed under pairing, composition, primitive recursion, and μ-recursion.
-/
inductive RecursiveIn (O : Set (ℕ →. ℕ)) : (ℕ →. ℕ) → Prop
  | zero : RecursiveIn O fun _ => 0
  | succ : RecursiveIn O Nat.succ
  | left : RecursiveIn O fun n => (Nat.unpair n).1
  | right : RecursiveIn O fun n => (Nat.unpair n).2
  | oracle : ∀ g ∈ O, RecursiveIn O g
  | pair {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
      RecursiveIn O fun n => (Nat.pair <$> f n <*> h n)
  | comp {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
      RecursiveIn O fun n => h n >>= f
  | prec {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
      RecursiveIn O fun p =>
        let (a, n) := Nat.unpair p
        n.rec (f a) fun y IH => do
          let i ← IH
          h (Nat.pair a (Nat.pair y i))
  | rfind {f : ℕ →. ℕ} (hf : RecursiveIn O f) :
      RecursiveIn O fun a =>
        Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a n)

namespace Nat
/-- The primitive recursive functions `ℕ → ℕ`. -/
protected inductive PrimrecIn (O : Set (ℕ → ℕ)) : (ℕ → ℕ) → Prop
  | zero : Nat.PrimrecIn O fun _ => 0
  | protected succ : Nat.PrimrecIn O succ
  | left : Nat.PrimrecIn O fun n => n.unpair.1
  | right : Nat.PrimrecIn O fun n => n.unpair.2
  | oracle : ∀ g ∈ O, Nat.PrimrecIn O g
  | pair {f g} : Nat.PrimrecIn O f → Nat.PrimrecIn O g → Nat.PrimrecIn O fun n => pair (f n) (g n)
  | comp {f g} : Nat.PrimrecIn O f → Nat.PrimrecIn O g → Nat.PrimrecIn O fun n => f (g n)
  | prec {f g} :
      Nat.PrimrecIn O f →
        Nat.PrimrecIn O g →
          Nat.PrimrecIn O (unpaired fun z n => n.rec (f z) fun y IH => g <| pair z <| pair y IH)
end Nat

/--
Encode a partial function between `Primcodable` types as a partial function `ℕ →. ℕ`.
-/
def liftPrim {α σ} [Primcodable α] [Primcodable σ] (f : α →. σ) : ℕ →. ℕ :=
  fun n => Part.bind (decode (α := α) n) fun a => (f a).map encode

/--
Encode a total function between `Primcodable` types as a total function `ℕ → ℕ`.
If decoding fails, the output defaults to `0`.
-/
def liftPrimrec {α σ} [Primcodable α] [Primcodable σ] (f : α → σ) : ℕ → ℕ :=
  fun n => (decode (α := α) n).map (fun a => encode (f a)) |>.getD 0

/-- Lift `RecursiveIn` from `ℕ →. ℕ` to partial functions between `Primcodable` types. -/
def RecursiveIn' {α σ} [Primcodable α] [Primcodable σ] (O : Set (ℕ →. ℕ)) (f : α →. σ) : Prop :=
  RecursiveIn O (liftPrim f)

/-- Relative primitive recursion between primcodable types -/
def PrimrecIn' {α σ} [Primcodable α] [Primcodable σ] (O : Set (ℕ → ℕ)) (f : α → σ) : Prop :=
  Nat.PrimrecIn O (liftPrimrec f)

/-- A binary partial function is recursive in `O` if the curried form is. -/
def RecursiveIn₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    (O : Set (ℕ →. ℕ)) (f : α → β →. σ) : Prop :=
  RecursiveIn' O (fun p : α × β => f p.1 p.2)

/-- A total function is computable in `O` if its constant lift is recursive in `O`. -/
def ComputableIn {α σ} [Primcodable α] [Primcodable σ] (O : Set (ℕ →. ℕ)) (f : α → σ) : Prop :=
  RecursiveIn' O (fun a => Part.some (f a))

/-- A binary total function is computable in `O`. -/
def ComputableIn₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    (O : Set (ℕ →. ℕ)) (f : α → β → σ) : Prop :=
  ComputableIn O (fun p : α × β => f p.1 p.2)

namespace RecursiveIn

theorem of_eq {f g : ℕ →. ℕ} {O : Set (ℕ →. ℕ)} (hf : RecursiveIn O f) (H : ∀ n, f n = g n) :
    RecursiveIn O g :=
  (funext H : f = g) ▸ hf

theorem of_eq_tot {f : ℕ →. ℕ} {g : ℕ → ℕ} {O : Set (ℕ →. ℕ)} (hf : RecursiveIn O f)
    (H : ∀ n, g n ∈ f n) : RecursiveIn O g :=
  of_eq hf fun n => eq_some_iff.2 (H n)

end RecursiveIn
/--
If a function is partial recursive, then it is recursive in every partial function.
-/
lemma Nat.Partrec.recursiveIn {O : Set (ℕ →. ℕ)} (pF : Nat.Partrec f) : RecursiveIn O f := by
  induction pF with
  | zero | succ | left | right => constructor
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact .prec ih₁ ih₂
  | rfind _ ih => exact .rfind ih

/--
If a function is computable, then it is computable in every oracle.
-/
theorem Computable.computableIn {f : α → β} [Primcodable α] [Primcodable β]
    (hf : Computable f) : ComputableIn O f :=
  Nat.Partrec.recursiveIn (by simpa [Computable] using hf)

namespace RecursiveIn

theorem of_primrec {O : Set (ℕ →. ℕ)} {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    RecursiveIn O (fun n => f n) :=
  Nat.Partrec.recursiveIn (Nat.Partrec.of_primrec hf)

protected theorem some {O : Set (ℕ →. ℕ)} : RecursiveIn O some :=
  of_primrec (O := O) Nat.Primrec.id

theorem none {O : Set (ℕ →. ℕ)} : RecursiveIn O (fun _ => none) :=
  (of_primrec (O := O) (Nat.Primrec.const 1)).rfind.of_eq fun _ =>
    eq_none_iff.2 fun _ ⟨h, _⟩ => by simp at h

end RecursiveIn

theorem Primrec.to_computableIn {α σ} [Primcodable α] [Primcodable σ]
    {f : α → σ} (hf : Primrec f) (O : Set (ℕ →. ℕ)) :
    ComputableIn O f := Computable.computableIn (Primrec.to_comp hf)

nonrec theorem Primrec₂.to_computableIn₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → β → σ} (hf : Primrec₂ f) (O : Set (ℕ →. ℕ)) :
    ComputableIn₂ O f :=
  Primrec.to_computableIn hf O

protected theorem ComputableIn.recursiveIn' {α σ} [Primcodable α] [Primcodable σ]
    {f : α → σ} {O} (hf : ComputableIn O f) :
    RecursiveIn' O (fun a => Part.some (f a)) := hf

protected theorem ComputableIn₂.recursiveIn₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → β → σ} {O} (hf : ComputableIn₂ O f) :
    RecursiveIn₂ O fun a => (f a : β →. σ) := hf

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

theorem const_in (O : Set (ℕ →. ℕ)) (s : σ) : ComputableIn O (fun _ : α => s) :=
  Primrec.to_computableIn (Primrec.const s) O

theorem id_in (O : Set (ℕ →. ℕ)) : ComputableIn O (@id α) :=
  Primrec.to_computableIn Primrec.id O

theorem fst_in (O : Set (ℕ →. ℕ)) : ComputableIn O (@Prod.fst α β) :=
  Primrec.to_computableIn Primrec.fst O

theorem snd_in (O : Set (ℕ →. ℕ)) : ComputableIn O (@Prod.snd α β) :=
  Primrec.to_computableIn Primrec.snd O

theorem unpair_in (O : Set (ℕ →. ℕ)) : ComputableIn O Nat.unpair :=
  Primrec.to_computableIn Primrec.unpair O

theorem succ_in (O : Set (ℕ →. ℕ)) : ComputableIn O Nat.succ :=
  Primrec.to_computableIn Primrec.succ O

theorem sumInl_in (O : Set (ℕ →. ℕ)) : ComputableIn O (@Sum.inl α β) :=
  Primrec.to_computableIn Primrec.sumInl O

theorem sumInr_in (O : Set (ℕ →. ℕ)) : ComputableIn O (@Sum.inr α β) :=
  Primrec.to_computableIn Primrec.sumInr O

/--
If every function in `O` is partial recursive,
then a function which is RecursiveIn g is also partial recursive.
-/
theorem partrec_of_partrec_oracle (h₁ : ∀ g ∈ O, Nat.Partrec g) (h₂ : RecursiveIn O f) :
  Nat.Partrec f := by
  induction h₂ with
  | zero | succ | left | right => constructor
  | oracle g gIn => exact h₁ g gIn
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact .prec ih₁ ih₂
  | rfind _ ih => exact .rfind ih

/--
If a function is recursive in the constant zero function,
then it is partial recursive.
-/
lemma RecursiveIn.partrec_of_zero (fRecInZero : RecursiveIn {fun _ => Part.some 0} f) :
    Nat.Partrec f :=
  partrec_of_partrec_oracle
    (fun _ gIn =>
      (Set.mem_singleton_iff.mp gIn).symm ▸
        (Nat.Partrec.zero.of_eq fun _ => rfl))
    fRecInZero

/--
If a function is partial recursive in the constant none function,
then it is partial recursive.
-/
lemma RecursiveIn.partrec_of_none (fRecInNone : RecursiveIn {fun _ => Part.none} f) :
    Nat.Partrec f :=
  partrec_of_partrec_oracle
    (fun _ gIn =>
      (Set.mem_singleton_iff.mp gIn).symm ▸
        (Nat.Partrec.none.of_eq fun _ => rfl))
    fRecInNone

/--
A partial function `f` is partial recursive if and only if it is recursive in
every partial function `g`.
-/
theorem partrec_iff_forall_recursiveIn : Nat.Partrec f ↔ ∀ g, RecursiveIn {g} f :=
  ⟨fun hf _ ↦ hf.recursiveIn, (· _ |>.partrec_of_zero)⟩

@[simp]
lemma recursiveIn_empty_iff_partrec : RecursiveIn ({} : Set (ℕ →. ℕ)) f ↔ Nat.Partrec f :=
⟨
  fun hf =>
    partrec_of_partrec_oracle (O := ({} : Set (ℕ →. ℕ))) (f := f)
      (fun g hg => ((Set.mem_empty_iff_false g).mp hg).elim)
      hf,
  fun hf =>
    Nat.Partrec.recursiveIn (O := ({} : Set (ℕ →. ℕ))) hf
⟩

namespace RecursiveIn

/-- If every element of O₁ is RecursiveIn O₂, then any function which is RecursiveIn O₁
 is also RecursiveIn O₂ -/
theorem subst {O O' : Set (ℕ →. ℕ)} {f : ℕ →. ℕ} (hf : RecursiveIn O f)
    (hO : ∀ g, g ∈ O → RecursiveIn O' g) : RecursiveIn O' f := by
  induction hf with
  | zero | succ | left | right =>
      constructor
  | oracle g hg => exact hO g hg
  | pair _ _ ihf ihg => exact .pair ihf ihg
  | comp _ _ ihf ihg => exact .comp ihf ihg
  | prec _ _ ihf ihg => exact .prec ihf ihg
  | rfind _ ihf => exact .rfind ihf

/-- Monotonicity of `RecursiveIn` with respect to oracle sets. -/
theorem mono {O₁ O₂ : Set (ℕ →. ℕ)} (hsub : O₁ ⊆ O₂) {g : ℕ →. ℕ} :
      RecursiveIn O₁ g → RecursiveIn O₂ g :=
      fun gRecInO => .subst (gRecInO) (fun g' g'In => .oracle g' (hsub (g'In)))
/--
`RecursiveIn O` is closed under conditionals with a computable guard and a constant fallback.

If `c n = true` we return `f n`, otherwise we return the
constant value `k`.
-/
theorem cond_const {c : ℕ → Bool} {f : ℕ →. ℕ} (hc : Computable c)
    (hf : RecursiveIn O f) (k : ℕ) :
    RecursiveIn O (fun n => bif (c n) then f n else (Part.some k)) := by
  have hid : RecursiveIn O (fun n : ℕ => n) := by
    simpa using (RecursiveIn.of_primrec (O := O) Nat.Primrec.id)
  have hcode : RecursiveIn O (fun n : ℕ => encode (c n)) := by
    have hcomp : Computable (fun n : ℕ => encode (c n)) := (Computable.encode.comp hc)
    exact Nat.Partrec.recursiveIn (O := O) ((Partrec.nat_iff).1 hcomp.partrec)
  let pairFn : ℕ →. ℕ := fun n =>
    Nat.pair <$> (show Part ℕ from n) <*> (show Part ℕ from encode (c n))
  have hpair : RecursiveIn O pairFn := by
    simpa [pairFn] using (RecursiveIn.pair hid hcode)
  let base : ℕ →. ℕ := fun _ : ℕ => (k : ℕ)
  have hbase : RecursiveIn O base := by
    simpa [base] using (RecursiveIn.of_primrec (O := O) (Nat.Primrec.const k))
  let step : ℕ →. ℕ := fun p : ℕ => (Nat.unpair p).1 >>= f
  have hstep : RecursiveIn O step := by
    simpa [step] using (RecursiveIn.comp hf RecursiveIn.left)
  let precFn : ℕ →. ℕ :=
    fun p : ℕ =>
      let (a, n) := Nat.unpair p
      n.rec (base a) (fun y IH => do
        let i ← IH
        step (Nat.pair a (Nat.pair y i)))
  have hprec : RecursiveIn O precFn := by
    simpa [precFn] using (RecursiveIn.prec hbase hstep)
  let mainFn : ℕ →. ℕ := fun n => pairFn n >>= precFn
  have hmain : RecursiveIn O mainFn := by
    simpa [mainFn] using (RecursiveIn.comp hprec hpair)
  have hEq : mainFn = (fun n => bif (c n) then f n else Part.some k) := by
    funext n
    cases h : c n <;>
      simp [mainFn, pairFn, precFn, base, step, h, Seq.seq, Nat.unpair_pair]
  simpa [hEq] using hmain

/--
Construct `cmp` so that a single `Nat.rfind` over `cmp` computes `cond (c n) (f n) (g n)`.
-/
theorem cond_core_rfind {c : ℕ → Bool} {f g : ℕ →. ℕ}
    (hc : Computable c) (hf : RecursiveIn O f) (hg : RecursiveIn O g) :
    ∃ cmp : ℕ →. ℕ,
      RecursiveIn O cmp ∧
        (fun n => Nat.rfind (fun k => (fun m => m = 0) <$> cmp (Nat.pair n k))) =
          (fun n => cond (c n) (f n) (g n)) := by
  have kronecker_recursiveIn : RecursiveIn O Partrec.kronecker :=
    Nat.Partrec.recursiveIn (O := O) Partrec.kronecker_partrec
  have flip10_recursiveIn : RecursiveIn O (fun m => Part.some (Partrec.flip10 m)) :=
    Nat.Partrec.recursiveIn (O := O) Partrec.flip10_partrec
  let eq (h : ℕ →. ℕ) : ℕ →. ℕ := fun p =>
    ((Nat.pair <$>
          ((fun n : ℕ => (Nat.unpair n).1) p >>= h) <*>
          (fun n : ℕ => (Nat.unpair n).2) p) >>= Partrec.kronecker) >>=
      fun m => Part.some (Partrec.flip10 m)
  have heq {h : ℕ →. ℕ} (hh : RecursiveIn O h) : RecursiveIn O (eq h) := by
    have hbase : RecursiveIn O (fun p =>
        (Nat.pair <$> ((fun n : ℕ => (Nat.unpair n).1) p >>= h) <*>
          (fun n : ℕ => (Nat.unpair n).2) p) >>= Partrec.kronecker) :=
      RecursiveIn.comp kronecker_recursiveIn
        (RecursiveIn.pair (RecursiveIn.comp hh RecursiveIn.left) RecursiveIn.right)
    have : RecursiveIn O (fun p =>
        ((Nat.pair <$> ((fun n : ℕ => (Nat.unpair n).1) p >>= h) <*>
            (fun n : ℕ => (Nat.unpair n).2) p) >>= Partrec.kronecker) >>=
          fun m => Part.some (Partrec.flip10 m)) :=
      RecursiveIn.comp flip10_recursiveIn hbase
    simpa [eq] using this
  let c1 : ℕ → Bool := fun p => c (Nat.unpair p).1
  let c2 : ℕ → Bool := fun p => !c (Nat.unpair p).1
  have hc1 : Computable c1 := by
    simpa [c1] using hc.comp (Computable.fst.comp Computable.unpair)
  have hc2 : Computable c2 := by
    have hnot : Computable not := Primrec.not.to_comp
    simpa [c2] using hnot.comp hc1
  let t1 : ℕ →. ℕ := fun p => bif c1 p then eq f p else Part.some 1
  let t2 : ℕ →. ℕ := fun p => bif c2 p then eq g p else Part.some 1
  have ht1 : RecursiveIn O t1 := by
    simpa [t1] using (cond_const (O := O) (c := c1) (f := eq f) hc1 (heq hf) 1)
  have ht2 : RecursiveIn O t2 := by
    simpa [t2] using (cond_const (O := O) (c := c2) (f := eq g) hc2 (heq hg) 1)
  let mulPair : ℕ →. ℕ := (Nat.unpaired (fun a b : ℕ => a * b) : ℕ → ℕ)
  have hmul : RecursiveIn O mulPair := by
    have hpart : Nat.Partrec (mulPair : ℕ →. ℕ) := by
      simpa [mulPair] using (Nat.Partrec.of_primrec (Nat.Primrec.mul))
    exact Nat.Partrec.recursiveIn (O := O) hpart
  let cmp : ℕ →. ℕ := fun p => (Nat.pair <$> t1 p <*> t2 p) >>= mulPair
  have hcmp : RecursiveIn O cmp := by
    have hpair : RecursiveIn O (fun p => Nat.pair <$> t1 p <*> t2 p) :=
      RecursiveIn.pair ht1 ht2
    have : RecursiveIn O (fun p => (Nat.pair <$> t1 p <*> t2 p) >>= mulPair) :=
      RecursiveIn.comp hmul hpair
    simpa [cmp] using this
  refine ⟨cmp, hcmp, ?_⟩
  funext n
  let φ : ℕ → Bool := fun m => decide (m = 0)
  cases hn : c n with
  | true =>
      simp only [Part.map_eq_map, cond_true]
      have hpred : (fun k => Part.map φ (cmp (Nat.pair n k))) =
          fun k => Part.map φ (eq f (Nat.pair n k)) := by
        funext k
        simp [cmp, t1, t2, c1, c2, eq, mulPair, hn, Nat.unpair_pair, Nat.unpaired,
          Seq.seq, Part.bind_assoc, Part.bind_some]
      rw [hpred]
      simpa [eq, Nat.unpair_pair, Seq.seq, Part.map_eq_map, Part.bind_some_eq_map, φ] using
        (Partrec.kronecker_rfind (v := f n))
  | false =>
      simp only [Part.map_eq_map, cond_false]
      have hpred : (fun k => Part.map φ (cmp (Nat.pair n k))) =
          fun k => Part.map φ (eq g (Nat.pair n k)) := by
        funext k
        simp [cmp, t1, t2, c1, c2, eq, mulPair, hn, Nat.unpair_pair, Nat.unpaired,
          Seq.seq, Part.bind_assoc, Part.bind_some]
      rw [hpred]
      simpa [eq, Nat.unpair_pair, Seq.seq, Part.map_eq_map, Part.bind_some_eq_map, φ] using
        (Partrec.kronecker_rfind (v := g n))

/--
`RecursiveIn O` is closed under conditionals with a computable guard.
-/
theorem cond {c : ℕ → Bool} {f g : ℕ →. ℕ}
    (hc : Computable c) (hf : RecursiveIn O f) (hg : RecursiveIn O g) :
    RecursiveIn O (fun n => cond (c n) (f n) (g n)) := by
  rcases cond_core_rfind (O := O) (c := c) (f := f) (g := g) hc hf hg with ⟨cmp, hcmp, hEq⟩
  have hr : RecursiveIn O (fun n => Nat.rfind (fun k => (fun m => m = 0) <$>
    cmp (Nat.pair n k))) := by
    exact RecursiveIn.rfind hcmp
  refine RecursiveIn.of_eq hr ?_
  intro n
  simpa using congrArg (fun h => h n) hEq

end RecursiveIn
