/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/

import Mathlib.Computability.Primrec
import Mathlib.Computability.Partrec
import Mathlib.Data.Part
import Mathlib.Order.Antisymmetrization

/-!
# Oracle Computability and Turing Degrees

This file defines a model of oracle computability, introduces Turing reducibility and equivalence,
proves that Turing equivalence is an equivalence relation, and defines Turing degrees as the
quotient under this relation.

## Main Definitions
- `RecursiveIn O f`:
  An inductive definition representing that a partial function `f` is partial recursive given access
  to a set of oracles O.
- `TuringReducible`: A relation defining Turing reducibility between partial functions.
- `TuringEquivalent`: An equivalence relation defining Turing equivalence between partial functions.
- `TuringDegree`: The type of Turing degrees, defined as the quotient of partial functions under
  `TuringEquivalent`.

## Notation
- `f ≤ᵀ g` : `f` is Turing reducible to `g`.
- `f ≡ᵀ g` : `f` is Turing equivalent to `g`.

## Implementation Notes

The type of partial functions recursive in an oracle `g` is the smallest type containing
the constant zero, the successor, projections, the oracle `g`, and is closed under
pairing, composition, primitive recursion, and μ-recursion.

## References
* [Carneiro2018] Carneiro, Mario.
  *Formalizing Computability Theory via Partial Recursive Functions*.
  arXiv preprint arXiv:1810.08380, 2018.
* [Odifreddi1989] Odifreddi, Piergiorgio.
  *Classical Recursion Theory: The Theory of Functions and Sets of Natural Numbers,
  Vol. I*. Springer-Verlag, 1989.
* [Soare1987] Soare, Robert I. *Recursively Enumerable Sets and Degrees*. Springer-Verlag, 1987.
* [Gu2015] Gu, Yi-Zhi. *Turing Degrees*. Institute for Advanced Study, 2015.

## Tags
Computability, Oracle, Turing Degrees, Reducibility, Equivalence Relation
-/
open Primrec Nat.Partrec Part

/-
This section defines a model of oracle computability and defines
Turing reducibility and Turing equivalence. We define the Turing Degrees as the quotient under
Turing equivalence relation
-/

/--
The type of partial functions recursive in a set of oracle `O` is the smallest type containing
the constant zero, the successor, left and right projections, each oracle `g ∈ O`,
and is closed under pairing, composition, primitive recursion, and μ-recursion.
-/
inductive RecursiveIn (O : Set (ℕ →. ℕ)) : (ℕ →. ℕ) → Prop
  | zero : RecursiveIn O (fun _ => 0)
  | succ : RecursiveIn O Nat.succ
  | left : RecursiveIn O (fun n => (Nat.unpair n).1)
  | right : RecursiveIn O (fun n => (Nat.unpair n).2)
  | oracle : ∀ g ∈ O, RecursiveIn O g
  | pair {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
      RecursiveIn O (fun n => (Nat.pair <$> f n <*> h n))
  | comp {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
      RecursiveIn O (fun n => h n >>= f)
  | prec {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
      RecursiveIn O (fun p =>
        let (a, n) := Nat.unpair p
        n.rec (f a) (fun y IH => do
          let i ← IH
          h (Nat.pair a (Nat.pair y i))
        )
      )
  | rfind {f : ℕ →. ℕ} (hf : RecursiveIn O f) :
      RecursiveIn O (fun a =>
        Nat.rfind (fun n => (fun m => m = 0) <$> f (Nat.pair a n))
      )
/--
`f` is turing reducible to `g` if `f` is partial recursive given access to the oracle `g`
-/
abbrev TuringReducible (f g : ℕ →. ℕ) : Prop :=
  RecursiveIn {g} f

@[inherit_doc TuringReducible]
infix:50 "≤ᵀ" => TuringReducible

/--
`f` is Turing equivalent to `g` if `f` is reducible to `g` and `g` is reducible to `f`.
-/
abbrev TuringEquivalent (f g : ℕ →. ℕ) : Prop :=
  AntisymmRel TuringReducible f g

@[inherit_doc TuringEquivalent]
infix:50 "≡ᵀ" => TuringEquivalent

/--
If a function is partial recursive, then it is recursive in every partial function.
-/
lemma Nat.Partrec.turingReducible (f : ℕ →. ℕ) (pF : Nat.Partrec f) (g : ℕ →. ℕ) : f ≤ᵀ g := by
  induction' pF with f' g' _ _ ih₁ ih₂ f' g' _ _ ih₁ ih₂ f' g' _ _ ih₁ ih₂ f' _ ih
  repeat {constructor}
  · case pair =>
    apply RecursiveIn.pair ih₁ ih₂
  · case comp =>
    apply RecursiveIn.comp ih₁ ih₂
  · case prec =>
    apply RecursiveIn.prec ih₁ ih₂
  · case rfind =>
    apply RecursiveIn.rfind ih

/--
If a function is recursive in the constant zero function,
then it is partial recursive.
-/
lemma TuringReducible.partrec_of_zero (f : ℕ →. ℕ) (fRecInZero : f ≤ᵀ fun _ => Part.some 0) :
  Nat.Partrec f := by
  induction' fRecInZero with g hg g h _ _ ih₁ ih₂ g h _ _ ih₁ ih₂ g h _ _ ih₁ ih₂ g _ ih
  repeat {constructor}
  · rw [Set.mem_singleton_iff] at hg; rw [hg];
    exact Nat.Partrec.zero
  repeat {constructor; assumption; try assumption}

/--
A partial function `f` is partial recursive if and only if it is recursive in
every partial function `g`.
-/
theorem partrec_iff_partrec_in_everything (f : ℕ →. ℕ) : Nat.Partrec f ↔ ∀ g, f ≤ᵀ g :=
  ⟨(·.turingReducible), (· _ |>.partrec_of_zero)⟩

theorem TuringReducible.refl (f : ℕ →. ℕ) : f ≤ᵀ f := by
  apply RecursiveIn.oracle; simp

instance : IsRefl (ℕ →. ℕ) TuringReducible :=
  ⟨fun f => TuringReducible.refl f⟩

theorem TuringReducible.trans {f g h : ℕ →. ℕ} (hg : f ≤ᵀ g) (hh : g ≤ᵀ h) :
    f ≤ᵀ h := by
  induction' hg with g' hg g' h' _ _ ih₁ ih₂ g' h' _ _ ih₁ ih₂ g' h' _ _ ih₁ ih₂ g' _ ih
  repeat {constructor}
  · rw [Set.mem_singleton_iff] at hg; rw [hg]; exact hh
  · case pair =>
    apply RecursiveIn.pair ih₁ ih₂
  · case comp =>
    apply RecursiveIn.comp ih₁ ih₂
  · case prec =>
    apply RecursiveIn.prec ih₁ ih₂
  · case rfind =>
    apply RecursiveIn.rfind ih

instance : IsTrans (ℕ →. ℕ) TuringReducible :=
  ⟨@TuringReducible.trans⟩

instance : IsPreorder (ℕ →. ℕ) TuringReducible where
  refl := TuringReducible.refl

theorem TuringEquivalent.equivalence : Equivalence TuringEquivalent :=
  (AntisymmRel.setoid _ _).iseqv

@[refl]
theorem TuringEquivalent.refl (f : ℕ →. ℕ) : f ≡ᵀ f :=
  Equivalence.refl equivalence f

@[symm]
theorem TuringEquivalent.symm {f g : ℕ →. ℕ} (h : f ≡ᵀ g) : g ≡ᵀ f :=
  Equivalence.symm equivalence h

@[trans]
theorem TuringEquivalent.trans (f g h : ℕ →. ℕ) (h₁ : f ≡ᵀ g) (h₂ : g ≡ᵀ h) : f ≡ᵀ h :=
  Equivalence.trans equivalence h₁ h₂

/--
Instance declaring that `RecursiveIn` is a preorder.
-/
instance : IsPreorder (ℕ →. ℕ) TuringReducible where
  refl := TuringReducible.refl
  trans := @TuringReducible.trans

/--
Turing degrees are the equivalence classes of partial functions under Turing equivalence.
-/
abbrev TuringDegree :=
  Antisymmetrization _ TuringReducible

instance TuringDegree.isPartialOrder : PartialOrder TuringDegree :=
  @instPartialOrderAntisymmetrization (ℕ →. ℕ)
    {le := TuringReducible, le_refl := TuringReducible.refl, le_trans := @TuringReducible.trans}

lemma partrec_iff_partrec_in_empty (f : ℕ →. ℕ) : Nat.Partrec f ↔ RecursiveIn {} f := by
  constructor
  intros pF
  · induction' pF with f' g' _ _ ih₁ ih₂ f' g' _ _ ih₁ ih₂ f' g' _ _ ih₁ ih₂ f' _ ih
    repeat {constructor}
    · case pair =>
      apply RecursiveIn.pair ih₁ ih₂
    · case comp =>
      apply RecursiveIn.comp ih₁ ih₂
    · case prec =>
      apply RecursiveIn.prec ih₁ ih₂
    · case rfind =>
      apply RecursiveIn.rfind ih
  · intro fRecInNone
    induction' fRecInNone with g hg g h _ _ ih₁ ih₂ g h _ _ ih₁ ih₂ g h _ _ ih₁ ih₂ g _ ih
    repeat {constructor}
    · simp at hg
    repeat {constructor; assumption; try assumption}

/--
An alternative definition of partial recursive in terms of oracle computability:
A partial recursive function is a function which is recursive in the empty set
-/
def Partrec₃ (f : ℕ →. ℕ) : Prop :=
  RecursiveIn {} f
