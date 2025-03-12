/-
Copyright (c) 2024 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/
import Mathlib.Computability.Primrec
import Mathlib.Computability.Partrec
<<<<<<< HEAD
import Mathlib.Data.Part
import Mathlib.Order.Antisymmetrization

=======
import Mathlib.Computability.Reduce
import Mathlib.Data.Part
import Mathlib.Order.Antisymmetrization
>>>>>>> 3a6efec441 (Added Definitions for Oracle Computability)
/-!
# Oracle Computability and Turing Degrees

This file defines a model of oracle computability, introduces Turing reducibility and equivalence,
proves that Turing equivalence is an equivalence relation, and defines Turing degrees as the
quotient under this relation.

## Main Definitions

<<<<<<< HEAD
- `RecursiveIn g f`:
  An inductive definition representing that a partial function `f` is recursive in oracle `g`.
- `TuringEquivalent`: A relation defining Turing equivalence between partial functions.
- `TuringDegree`:
  The type of Turing degrees, defined as equivalence classes under `TuringEquivalent`.
=======
- `RecursiveIn O f`:
  An inductive definition representing that a partial function `f` is partial recursive given access
   to a set of oracles O.
- `TuringReducible`: A relation defining Turing reducibility between partial functions.
- `TuringEquivalent`: An equivalence relation defining Turing equivalence between partial functions.
- `TuringDegree`:
  The type of Turing degrees, defined as the quotient of partial functions under `TuringEquivalent`.
>>>>>>> 3a6efec441 (Added Definitions for Oracle Computability)

## Notation

- `f ≡ᵀ g` : `f` is Turing equivalent to `g`.

## Implementation Notes

The type of partial functions recursive in an oracle `g` is the smallest type containing
the constant zero, the successor, projections, the oracle `g`, and is closed under
pairing, composition, primitive recursion, and μ-recursion.

## References

<<<<<<< HEAD
* [carneiro2019] Carneiro, Mario.
  *Formalizing Computability Theory via Partial Recursive Functions*.
  arXiv preprint arXiv:1810.08380, 2018.
* [soare1987] Soare, Robert I. *Recursively Enumerable Sets and Degrees*. Springer-Verlag, 1987.
=======
* [Carneiro2018] Carneiro, Mario.
  *Formalizing Computability Theory via Partial Recursive Functions*.
  arXiv preprint arXiv:1810.08380, 2018.
* [Odifreddi1989] Odifreddi, Piergiorgio.
  *Classical Recursion Theory: The Theory of Functions and Sets of Natural Numbers,
  Vol. I*. Springer-Verlag, 1989.
* [Soare1987] Soare, Robert I. *Recursively Enumerable Sets and Degrees*. Springer-Verlag, 1987.
* [Gu2015] Gu, Yi-Zhi. *Turing Degrees*. Institute for Advanced Study, 2015.
>>>>>>> 3a6efec441 (Added Definitions for Oracle Computability)

## Tags

Computability, Oracle, Turing Degrees, Reducibility, Equivalence Relation
-/

open Primrec Nat.Partrec Part

<<<<<<< HEAD
/--
The type of partial functions `f` that are recursive in an oracle `g` is the smallest type
containing the constant zero, the successor, left and right projections, the oracle `g`,
and is closed under pairing, composition, primitive recursion, and μ-recursion.

Equivalently one can say that `f` is turing reducible to `g` when `f` is recursive in `g`.
-/

inductive RecursiveIn : (ℕ →. ℕ) → (ℕ →. ℕ) → Prop
  | zero (g) : RecursiveIn (fun _ => 0) g
  | succ (g) : RecursiveIn Nat.succ g
  | left (g) : RecursiveIn (fun n => (Nat.unpair n).1) g
  | right (g) : RecursiveIn (fun n => (Nat.unpair n).2) g
  | oracle (g) : RecursiveIn g g
  | pair (f h g : ℕ →. ℕ) (hf : RecursiveIn f g) (hh : RecursiveIn h g) :
      RecursiveIn (fun n => (Nat.pair <$> f n <*> h n)) g
  | comp (f h g : ℕ →. ℕ) (hf : RecursiveIn f g) (hh : RecursiveIn h g) :
      RecursiveIn (fun n => h n >>= f) g
  /-- primitive recursion -/
  | prec (f h g : ℕ →. ℕ) (hf : RecursiveIn f g) (hh : RecursiveIn h g) :
      RecursiveIn (fun p =>
        let (a, n) := Nat.unpair p
        n.rec (f a) (fun y ih => do
          let i ← ih
          h (Nat.pair a (Nat.pair y i)))) g
  /-- μ-recursion -/
  | rfind (f g : ℕ →. ℕ) (hf : RecursiveIn f g) :
      RecursiveIn (fun a =>
        Nat.rfind (fun n => (fun m => m = 0) <$> f (Nat.pair a n))) g

=======
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
>>>>>>> 3a6efec441 (Added Definitions for Oracle Computability)

/--
`f` is Turing equivalent to `g` if `f` is reducible to `g` and `g` is reducible to `f`.
-/
abbrev TuringEquivalent (f g : ℕ →. ℕ) : Prop :=
<<<<<<< HEAD
  AntisymmRel RecursiveIn f g
=======
  AntisymmRel TuringReducible f g
>>>>>>> 3a6efec441 (Added Definitions for Oracle Computability)

/--
Custom infix notation for `TuringEquivalent`.
-/
<<<<<<< HEAD
infix:50 " ≡ᵀ " => TuringEquivalent
=======
infix:50 "≡ᵀ" => TuringEquivalent
>>>>>>> 3a6efec441 (Added Definitions for Oracle Computability)

/--
If a function is partial recursive, then it is recursive in every partial function.
-/
<<<<<<< HEAD
lemma Nat.Partrec.recursiveIn (f : ℕ →. ℕ) (pF : Nat.Partrec f) (g : ℕ →. ℕ) :
    RecursiveIn f g := by
  induction pF with
  | zero =>
    apply RecursiveIn.zero
  | succ =>
    apply RecursiveIn.succ
  | left =>
    apply RecursiveIn.left
  | right =>
    apply RecursiveIn.right
  | pair _ _ ih1 ih2 =>
    apply RecursiveIn.pair
    · apply ih1
    · apply ih2
  | comp _ _ ih1 ih2 =>
    apply RecursiveIn.comp
    · apply ih1
    · apply ih2
  | prec _ _ ih1 ih2 =>
    apply RecursiveIn.prec
    · apply ih1
    · apply ih2
  | rfind _ ih =>
    apply RecursiveIn.rfind; apply ih
=======
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
>>>>>>> 3a6efec441 (Added Definitions for Oracle Computability)

/--
If a function is recursive in the constant zero function,
then it is partial recursive.
-/
<<<<<<< HEAD
lemma RecursiveIn.partrec_of_zero (f : ℕ →. ℕ) (fRecInZero : RecursiveIn f fun _ => Part.some 0) :
    Nat.Partrec f := by
  generalize h : (fun _ => Part.some 0) = fp at *
  induction fRecInZero with
  | zero =>
    apply Nat.Partrec.zero
  | succ =>
    apply Nat.Partrec.succ
  | left =>
    apply Nat.Partrec.left
  | right =>
    apply Nat.Partrec.right
  | oracle g =>
    rw [← h]
    apply Nat.Partrec.zero
  | pair _ _ _ _ _ ih1 ih2 =>
    apply Nat.Partrec.pair
    · apply ih1
      rw [← h]
    · apply ih2
      rw [← h]
  | comp _ _ _ _ _ ih1 ih2 =>
    apply Nat.Partrec.comp
    · apply ih1
      rw [← h]
    · apply ih2
      rw [← h]
  | prec _ _ _ _ _ ih1 ih2 =>
    apply Nat.Partrec.prec
    · apply ih1
      rw [← h]
    · apply ih2
      rw [← h]
  | rfind _ _ _ ih =>
    apply Nat.Partrec.rfind
    apply ih
    rw [← h]
=======
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
>>>>>>> 3a6efec441 (Added Definitions for Oracle Computability)

/--
A partial function `f` is partial recursive if and only if it is recursive in
every partial function `g`.
-/
<<<<<<< HEAD
theorem partrec_iff_partrec_in_everything (f : ℕ →. ℕ) : Nat.Partrec f ↔ ∀ g, RecursiveIn f g :=
  ⟨(·.recursiveIn), (· _ |>.partrec_of_zero)⟩
=======
theorem partrec_iff_partrec_in_everything (f : ℕ →. ℕ) : Nat.Partrec f ↔ ∀ g, f ≤ᵀ g :=
  ⟨(·.turingReducible), (· _ |>.partrec_of_zero)⟩
>>>>>>> 3a6efec441 (Added Definitions for Oracle Computability)

/--
Proof that turing reducibility is reflexive.
-/
<<<<<<< HEAD
@[refl]
theorem RecursiveIn.refl (f : ℕ →. ℕ) : RecursiveIn f f :=
  RecursiveIn.oracle f

/--
Instance declaring that `RecursiveIn` is reflexive.
-/
instance : IsRefl (ℕ →. ℕ) RecursiveIn :=
  ⟨RecursiveIn.refl⟩
=======
theorem TuringReducible.refl (f : ℕ →. ℕ) : f ≤ᵀ f := by
  apply RecursiveIn.oracle; simp

/--
Instance declaring that `TuringReducible` is reflexive.
-/
instance : IsRefl (ℕ →. ℕ) TuringReducible :=
  ⟨fun f => TuringReducible.refl f⟩
>>>>>>> 3a6efec441 (Added Definitions for Oracle Computability)

/--
Proof that turing reducibility is transitive.
-/
<<<<<<< HEAD
theorem RecursiveIn.trans {f g h : ℕ →. ℕ} (hg : RecursiveIn f g) (hh : RecursiveIn g h) :
    RecursiveIn f h := by
  induction hg with
  | zero =>
    apply RecursiveIn.zero
  | succ =>
    apply RecursiveIn.succ
  | left =>
    apply RecursiveIn.left
  | right =>
    apply RecursiveIn.right
  | oracle =>
    exact hh
  | pair f' h' _ _ _ hf_ih hh_ih =>
    apply RecursiveIn.pair
    · apply hf_ih
      apply hh
    · apply hh_ih
      apply hh
  | comp f' h' _ _ _ hf_ih hh_ih =>
    apply RecursiveIn.comp
    · apply hf_ih
      apply hh
    · apply hh_ih
      apply hh
  | prec f' h' _ _ _ hf_ih hh_ih =>
    apply RecursiveIn.prec
    · apply hf_ih
      apply hh
    · apply hh_ih
      apply hh
  | rfind f' _ _ hf_ih =>
    apply RecursiveIn.rfind
    · apply hf_ih
      apply hh

instance : IsTrans (ℕ →. ℕ) RecursiveIn :=
  ⟨@RecursiveIn.trans⟩

instance : IsPreorder (ℕ →. ℕ) RecursiveIn where
  refl := RecursiveIn.refl
  trans := @RecursiveIn.trans

theorem TuringEquivalent.equivalence : Equivalence TuringEquivalent :=
  (AntisymmRel.setoid _ _).iseqv

@[refl]
theorem TuringEquivalent.refl (f : ℕ →. ℕ) : f ≡ᵀ f :=
  equivalence.refl f

@[symm]
theorem TuringEquivalent.symm {f g : ℕ →. ℕ} (h : f ≡ᵀ g) : g ≡ᵀ f :=
  equivalence.symm h

@[trans]
theorem TuringEquivalent.trans {f g h : ℕ →. ℕ} (h1 : f ≡ᵀ g) (h2 : g ≡ᵀ h) : f ≡ᵀ h :=
  equivalence.trans h1 h2

/-- The type of Turing degrees, implemented as the
quotient of partial functions (`PFun`) under Turing equivalence. -/
abbrev TuringDegree : Type _ :=
  Antisymmetrization _ RecursiveIn
=======
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
>>>>>>> 3a6efec441 (Added Definitions for Oracle Computability)

/--
Instance declaring that `TuringDegree` is a partially ordered type.
-/
instance TuringDegree.isPartialOrder : PartialOrder TuringDegree :=
  @instPartialOrderAntisymmetrization (ℕ →. ℕ)
<<<<<<< HEAD
    {le := RecursiveIn, le_refl := .refl, le_trans _ _ _ := RecursiveIn.trans}
=======
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
>>>>>>> 3a6efec441 (Added Definitions for Oracle Computability)
