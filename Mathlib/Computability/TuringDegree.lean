/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/
module

public import Mathlib.Computability.RecursiveIn
public import Mathlib.Order.Antisymmetrization

/-!
# Turing degrees

This file defines Turing reducibility and equivalence, proves that Turing equivalence is an
equivalence relation, and defines Turing degrees as the quotient under this relation.

## Main definitions

- `TuringReducible`: A relation defining Turing reducibility between partial functions.
- `TuringEquivalent`: An equivalence relation defining Turing equivalence between partial functions.
- `TuringDegree`: The type of Turing degrees, defined as the quotient of partial functions under
  `TuringEquivalent`.

## Notation

- `f ≤ᵀ g` : `f` is Turing reducible to `g`.
- `f ≡ᵀ g` : `f` is Turing equivalent to `g`.

## References

* [Odifreddi1989] Odifreddi, Piergiorgio.
  *Classical Recursion Theory: The Theory of Functions and Sets of Natural Numbers,
  Vol. I*. Springer-Verlag, 1989.

## Tags

Computability, Oracle, Turing Degrees, Reducibility, Equivalence Relation
-/

@[expose] public section

open Primrec

variable {f g h : ℕ →. ℕ}

/--
`f` is Turing reducible to `g` if `f` is partial recursive given access to the oracle `g`
-/
abbrev TuringReducible (f g : ℕ →. ℕ) : Prop :=
  RecursiveIn {g} f

/--
`f` is Turing equivalent to `g` if `f` is reducible to `g` and `g` is reducible to `f`.
-/
abbrev TuringEquivalent (f g : ℕ →. ℕ) : Prop :=
  AntisymmRel TuringReducible f g

@[inherit_doc] scoped[Computability] infix:50 " ≤ᵀ " => TuringReducible
@[inherit_doc] scoped[Computability] infix:50 " ≡ᵀ " => TuringEquivalent

open scoped Computability

/-- If a function is partial recursive, then it is recursive in every partial function. -/
lemma Partrec.turingReducible (pF : Partrec f) : f ≤ᵀ g :=
  pF.recursiveIn

/-- If a function is recursive in a constant partial function, then it is partial recursive. -/
lemma TuringReducible.partrec_of_const {s} (hf : f ≤ᵀ fun _ => s) : Partrec f :=
  RecursiveIn.partrec_of_const hf

/-- A partial function `f` is partial recursive if and only if it is recursive in
every partial function `g`. -/
theorem partrec_iff_forall_turingReducible : Partrec f ↔ ∀ g, f ≤ᵀ g :=
  ⟨fun hf _ => hf.turingReducible, fun hf => hf (fun _ => .none) |>.partrec_of_const⟩

protected theorem TuringReducible.refl (f : ℕ →. ℕ) : f ≤ᵀ f := .oracle _ <| by simp
protected theorem TuringReducible.rfl : f ≤ᵀ f := .refl _

theorem TuringReducible.trans (hg : f ≤ᵀ g) (hh : g ≤ᵀ h) : f ≤ᵀ h :=
  hg.subst (by simpa using hh)

instance : IsPreorder (ℕ →. ℕ) TuringReducible where
  refl _ := .rfl
  trans := @TuringReducible.trans

theorem TuringEquivalent.equivalence : Equivalence TuringEquivalent :=
  (AntisymmRel.setoid _ _).iseqv

@[refl]
protected theorem TuringEquivalent.refl (f : ℕ →. ℕ) : f ≡ᵀ f :=
  Equivalence.refl equivalence f

@[symm]
theorem TuringEquivalent.symm {f g : ℕ →. ℕ} (h : f ≡ᵀ g) : g ≡ᵀ f :=
  Equivalence.symm equivalence h

@[trans]
theorem TuringEquivalent.trans (f g h : ℕ →. ℕ) (h₁ : f ≡ᵀ g) (h₂ : g ≡ᵀ h) : f ≡ᵀ h :=
  Equivalence.trans equivalence h₁ h₂

/--
Turing degrees are the equivalence classes of partial functions under Turing equivalence.
-/
@[informal "Turing degrees"]
@[informal "Turing degrees"]
abbrev TuringDegree :=
  Antisymmetrization _ TuringReducible

set_option backward.privateInPublic true in
private instance : Preorder (ℕ →. ℕ) where
  le := TuringReducible
  le_refl := .refl
  le_trans _ _ _ := TuringReducible.trans

instance TuringDegree.instPartialOrder : PartialOrder TuringDegree :=
  instPartialOrderAntisymmetrization
