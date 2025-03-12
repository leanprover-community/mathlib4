/-
Copyright (c) 2024 Tanner Duve. All rights reserved.
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
- `TuringDegree`:
  The type of Turing degrees, defined as the quotient of partial functions under `TuringEquivalent`.

## Notation

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
The type of partial functions recursive in a set of oracle O is the smallest type containing
the constant zero, the successor, left and right projections, each oracle g ∈ O, and is closed under
pairing, composition, primitive recursion, and μ-recursion.
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
f is turing reducible to g if f is recursive in g
-/
abbrev TuringReducible (f g : ℕ →. ℕ) : Prop :=
  RecursiveIn {g} f

infix:50 "≤ᵀ" => TuringReducible

/--
`f` is Turing equivalent to `g` if `f` is reducible to `g` and `g` is reducible to `f`.
-/
abbrev TuringEquivalent (f g : ℕ →. ℕ) : Prop :=
  AntisymmRel TuringReducible f g

/--
Custom infix notation for `TuringEquivalent`.
-/
infix:50 "≡ᵀ" => TuringEquivalent

/--
If a function is partial recursive, then it is recursive in every partial function.
-/
lemma Nat.Partrec.turingReducible (f : ℕ →. ℕ) (pF : Nat.Partrec f) (g : ℕ →. ℕ) : f ≤ᵀ g := by
  induction pF
  · exact RecursiveIn.zero
  · exact RecursiveIn.succ
  · exact RecursiveIn.left
  · exact RecursiveIn.right
  · case pair f' g' _ _ ih1 ih2 =>
    apply RecursiveIn.pair ih1 ih2
  · case comp f' g' _ _ ih1 ih2 =>
    apply RecursiveIn.comp ih1 ih2
  · case prec f' g' _ _ ih1 ih2 =>
    apply RecursiveIn.prec ih1 ih2
  · case rfind f' _ ih =>
    apply RecursiveIn.rfind ih

/--
If a function is recursive in the constant zero function,
then it is partial recursive.
-/
lemma TuringReducible.partrec_of_zero (f : ℕ →. ℕ) (fRecInZero : f ≤ᵀ fun _ => Part.some 0) :
  Nat.Partrec f := by
  induction fRecInZero
  · exact Nat.Partrec.zero
  · exact Nat.Partrec.succ
  · exact Nat.Partrec.left
  · exact Nat.Partrec.right
  · case oracle g hg =>
    simp at hg; rw [hg]
    exact Nat.Partrec.zero
  · case pair g h _ _ ih1 ih2 =>
    exact Nat.Partrec.pair ih1 ih2
  · case comp g h _ _ ih1 ih2 =>
    exact Nat.Partrec.comp ih1 ih2
  · case prec g h _ _ ih1 ih2 =>
    exact Nat.Partrec.prec ih1 ih2
  · case rfind g _ ih =>
    exact Nat.Partrec.rfind ih

/--
A partial function `f` is partial recursive if and only if it is recursive in
every partial function `g`.
-/
theorem partrec_iff_partrec_in_everything (f : ℕ →. ℕ) : Nat.Partrec f ↔ ∀ g, f ≤ᵀ g :=
  ⟨(·.turingReducible), (· _ |>.partrec_of_zero)⟩

/--
Proof that turing reducibility is reflexive.
-/
theorem TuringReducible.refl (f : ℕ →. ℕ) : f ≤ᵀ f := by
  apply RecursiveIn.oracle; simp

/--
Instance declaring that `TuringReducible` is reflexive.
-/
instance : IsRefl (ℕ →. ℕ) TuringReducible :=
  ⟨fun f => TuringReducible.refl f⟩

/--
Proof that turing reducibility is transitive.
-/
theorem TuringReducible.trans {f g h : ℕ →. ℕ} (hg : f ≤ᵀ g) (hh : g ≤ᵀ h) :
  f ≤ᵀ h := by
  induction hg
  · exact RecursiveIn.zero
  · exact RecursiveIn.succ
  · exact RecursiveIn.left
  · exact RecursiveIn.right
  · case oracle f' fg =>
    simp at fg; rw [fg]; exact hh
  · case pair f' g' _ _ ih1 ih2 =>
    apply RecursiveIn.pair ih1 ih2
  · case comp f' g' _ _ ih1 ih2 =>
    apply RecursiveIn.comp ih1 ih2
  · case prec f' g' _ _ ih1 ih2 =>
    apply RecursiveIn.prec ih1 ih2
  · case rfind f' _ ih =>
    apply RecursiveIn.rfind ih

/--
Instance declaring that `TuringReducible` is transitive.
-/
instance : IsTrans (ℕ →. ℕ) TuringReducible :=
  ⟨@TuringReducible.trans⟩

/--
Instance declaring that `TuringReducible` is a preorder.
-/
instance : IsPreorder (ℕ →. ℕ) TuringReducible where
  refl := TuringReducible.refl

/--
Instance declaring that `TuringEquivalent` is an equivalence relation.
-/
instance TuringEquivalent.equivalence : Equivalence TuringEquivalent :=
  (AntisymmRel.setoid _ _).iseqv

/--
Proof that `TuringEquivalent` is reflexive.
-/
@[refl]
theorem TuringEquivalent.refl (f : ℕ →. ℕ) : f ≡ᵀ f :=
  Equivalence.refl equivalence f

/--
Proof that `TuringEquivalent` is symmetric.
-/
@[symm]
theorem TuringEquivalent.symm {f g : ℕ →. ℕ} (h : f ≡ᵀ g) : g ≡ᵀ f :=
  Equivalence.symm equivalence h

/--
Proof that `TuringEquivalent` is transitive.
-/
@[trans]
theorem TuringEquivalent.trans (f g h : ℕ →. ℕ) (h1 : f ≡ᵀ g) (h2 : g ≡ᵀ h) : f ≡ᵀ h :=
  Equivalence.trans equivalence h1 h2

/--
Instance declaring that `RecursiveIn` is a preorder.
-/
instance : IsPreorder (ℕ →. ℕ) TuringReducible where
  refl := TuringReducible.refl
  trans := @TuringReducible.trans

/--
The Turing degrees as the set of equivalence classes under Turing equivalence.
-/
abbrev TuringDegree :=
  Antisymmetrization _ TuringReducible

/--
Instance declaring that `TuringDegree` is a partially ordered type.
-/
instance TuringDegree.isPartialOrder : PartialOrder TuringDegree :=
  @instPartialOrderAntisymmetrization (ℕ →. ℕ)
    {le := TuringReducible, le_refl := TuringReducible.refl, le_trans := @TuringReducible.trans}

lemma partrec_iff_partrec_in_empty (f : ℕ →. ℕ) : Nat.Partrec f ↔ RecursiveIn {} f := by
  constructor
  intros pF
  induction pF
  case mp.zero =>
    apply RecursiveIn.zero
  case mp.succ =>
    apply RecursiveIn.succ
  case mp.left =>
    apply RecursiveIn.left
  case mp.right =>
    apply RecursiveIn.right
  case mp.pair _ _ _ _ ih1 ih2 =>
    apply RecursiveIn.pair ih1 ih2
  case mp.comp _ _ _ _ ih1 ih2 =>
    apply RecursiveIn.comp ih1 ih2
  case mp.prec _ _ _ _ ih1 ih2 =>
    apply RecursiveIn.prec ih1 ih2
  case mp.rfind _ _ ih =>
    apply RecursiveIn.rfind ih
  intro fRecInNone
  induction' fRecInNone
  case mpr.zero =>
    apply Nat.Partrec.zero
  case mpr.succ =>
    apply Nat.Partrec.succ
  case mpr.left =>
    apply Nat.Partrec.left
  case mpr.right =>
    apply Nat.Partrec.right
  case mpr.oracle g gemp =>
    simp at gemp
  case mpr.pair _ _ _ _ ih1 ih2 =>
    apply Nat.Partrec.pair ih1 ih2
  case mpr.comp _ _ _ _ ih1 ih2 =>
    apply Nat.Partrec.comp ih1 ih2
  case mpr.prec _ _ _ _ ih1 ih2 =>
    apply Nat.Partrec.prec ih1 ih2
  case mpr.rfind _ _ ih =>
    apply Nat.Partrec.rfind ih

/--
An alternative definition of partial recursive in terms of oracle computability:
A partial recursive function is a function which is recursive in the empty set
-/
def Partrec₃ (f : ℕ →. ℕ) : Prop :=
  RecursiveIn {} f
