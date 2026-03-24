/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/
module

public import Mathlib.Computability.Partrec

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
* `partrec_iff_forall_recursiveIn`: A function is partial recursive iff it is recursive in every
  singleton oracle set.
* `Nat.recursiveIn_empty_iff_partrec`: Being recursive in the empty set is equivalent to being
  partial recursive.
* `Nat.RecursiveIn.mono`: Monotonicity of `Nat.RecursiveIn` with respect to oracle sets.

## Implementation notes

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

theorem of_eq {f g : ℕ →. ℕ} {O : Set (ℕ →. ℕ)} (hf : Nat.RecursiveIn O f) (H : ∀ n, f n = g n) :
    Nat.RecursiveIn O g :=
  (funext H : f = g) ▸ hf

theorem of_eq_tot {f : ℕ →. ℕ} {g : ℕ → ℕ} {O : Set (ℕ →. ℕ)} (hf : Nat.RecursiveIn O f)
    (H : ∀ n, g n ∈ f n) : Nat.RecursiveIn O g :=
  of_eq hf fun n => eq_some_iff.2 (H n)

end Nat.RecursiveIn

/--
If a function is partial recursive, then it is recursive in every partial function.
-/
lemma Nat.Partrec.recursiveIn {O : Set (ℕ →. ℕ)} (pF : Nat.Partrec f) :
    Nat.RecursiveIn O f := by
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

namespace Nat.RecursiveIn

theorem of_primrec {O : Set (ℕ →. ℕ)} {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    Nat.RecursiveIn O (fun n => f n) :=
  Nat.Partrec.recursiveIn (Nat.Partrec.of_primrec hf)

protected theorem some {O : Set (ℕ →. ℕ)} : Nat.RecursiveIn O Part.some :=
  of_primrec (O := O) Nat.Primrec.id

theorem none {O : Set (ℕ →. ℕ)} : Nat.RecursiveIn O (fun _ => Part.none) :=
  (of_primrec (O := O) (Nat.Primrec.const 1)).rfind.of_eq fun _ =>
    eq_none_iff.2 fun _ ⟨h, _⟩ => by simp at h

end Nat.RecursiveIn

theorem Primrec.computableIn {α σ} [Primcodable α] [Primcodable σ]
    {f : α → σ} (hf : Primrec f) (O : Set (ℕ →. ℕ)) :
    ComputableIn O f := Computable.computableIn (Primrec.to_comp hf)

nonrec theorem Primrec₂.computableIn₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → β → σ} (hf : Primrec₂ f) (O : Set (ℕ →. ℕ)) :
    ComputableIn₂ O f :=
  hf.computableIn O

protected theorem ComputableIn.recursiveIn {α σ} [Primcodable α] [Primcodable σ]
    {f : α → σ} {O} (hf : ComputableIn O f) :
    RecursiveIn O (fun a => Part.some (f a)) := hf

protected theorem ComputableIn₂.recursiveIn₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → β → σ} {O} (hf : ComputableIn₂ O f) :
    RecursiveIn₂ O fun a => (f a : β →. σ) := hf

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

namespace ComputableIn

protected theorem const (O : Set (ℕ →. ℕ)) (s : σ) : ComputableIn O (fun _ : α => s) :=
  (Primrec.const s).computableIn O

protected theorem id (O : Set (ℕ →. ℕ)) : ComputableIn O (@id α) :=
  Primrec.id.computableIn O

protected theorem fst (O : Set (ℕ →. ℕ)) : ComputableIn O (@Prod.fst α β) :=
  Primrec.fst.computableIn O

protected theorem snd (O : Set (ℕ →. ℕ)) : ComputableIn O (@Prod.snd α β) :=
  Primrec.snd.computableIn O

protected theorem unpair (O : Set (ℕ →. ℕ)) : ComputableIn O Nat.unpair :=
  Primrec.unpair.computableIn O

protected theorem succ (O : Set (ℕ →. ℕ)) : ComputableIn O Nat.succ :=
  Primrec.succ.computableIn O

protected theorem sumInl (O : Set (ℕ →. ℕ)) : ComputableIn O (@Sum.inl α β) :=
  Primrec.sumInl.computableIn O

protected theorem sumInr (O : Set (ℕ →. ℕ)) : ComputableIn O (@Sum.inr α β) :=
  Primrec.sumInr.computableIn O

end ComputableIn

/--
If every function in `O` is partial recursive,
then a function which is `Nat.RecursiveIn O` is also partial recursive.
-/
theorem partrec_of_partrec_oracle (h₁ : ∀ g ∈ O, Nat.Partrec g) (h₂ : Nat.RecursiveIn O f) :
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
lemma Nat.RecursiveIn.partrec_of_zero (fRecInZero : Nat.RecursiveIn {fun _ => Part.some 0} f) :
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
lemma Nat.RecursiveIn.partrec_of_none (fRecInNone : Nat.RecursiveIn {fun _ => Part.none} f) :
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
theorem partrec_iff_forall_recursiveIn :
    Nat.Partrec f ↔ ∀ g, Nat.RecursiveIn {g} f :=
  ⟨fun hf _ ↦ hf.recursiveIn, (· _ |>.partrec_of_zero)⟩

@[simp]
lemma Nat.recursiveIn_empty_iff_partrec :
    Nat.RecursiveIn {} f ↔ Nat.Partrec f :=
⟨
  fun hf =>
    @partrec_of_partrec_oracle f {}
      (fun g hg => ((Set.mem_empty_iff_false g).mp hg).elim)
      hf,
  fun hf =>
    @Nat.Partrec.recursiveIn _ {} hf
⟩

namespace Nat.RecursiveIn

/-- If every element of `O` is `Nat.RecursiveIn O'`, then any function which is
`Nat.RecursiveIn O` is also `Nat.RecursiveIn O'`. -/
theorem subst {O O' : Set (ℕ →. ℕ)} {f : ℕ →. ℕ} (hf : Nat.RecursiveIn O f)
    (hO : ∀ g, g ∈ O → Nat.RecursiveIn O' g) : Nat.RecursiveIn O' f := by
  induction hf with
  | zero | succ | left | right =>
      constructor
  | oracle g hg => exact hO g hg
  | pair _ _ ihf ihg => exact .pair ihf ihg
  | comp _ _ ihf ihg => exact .comp ihf ihg
  | prec _ _ ihf ihg => exact .prec ihf ihg
  | rfind _ ihf => exact .rfind ihf

/-- Monotonicity of `Nat.RecursiveIn` with respect to oracle sets. -/
theorem mono {O₁ O₂ : Set (ℕ →. ℕ)} (hsub : O₁ ⊆ O₂) {g : ℕ →. ℕ} :
    Nat.RecursiveIn O₁ g → Nat.RecursiveIn O₂ g :=
    fun gRecInO => .subst (gRecInO) (fun g' g'In => .oracle g' (hsub (g'In)))

end Nat.RecursiveIn
