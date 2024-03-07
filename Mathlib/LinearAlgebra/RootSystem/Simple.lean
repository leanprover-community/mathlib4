/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.RootSystem.Defs

/-!
# Bases of a root system

This file defines systems of simple roots in a root system.

## Main definitions

* `Thin` : A root system is thin if it admits a functional such that there are only finitely many
roots in the preimage of any interval.  This lets us do inductive constructions of the Cartan
matrix given a basis.
* `RegularElement` : Given a thin root system, a regular element is a linear functional on the
root space that takes no roots to zero.  This corresponds to an element of a Lie algebra with
minimal centralizer.
* `Base`: Given a root pairing and separation, a base is basis a minimal subset that generates the
positive half.


## Results

None yet

## Todo

Make a weaker notion than base, to allow infinite root systems with no base.  Take irreducible
elements and find a characterization?

Prove regular elements yield bases in the positive definite case.

Cartan Matrices.



## References

* Moody, Pianzola, "Infinite root systems"

-/

variable {α ι R M N} [LinearOrderedCommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N) (i : ι)

noncomputable section

namespace RootPairing

/-- An element in the coroot space is preregular if any interval in `R` has finite preimage. -/
def IsPreregular (x : N) : Prop := ∀ (n : R), 0 ≤ n →
  Finite { i | 0 ≤ (P.toLin (P.root i) x) ∧ (P.toLin (P.root i) x) ≤ n}

/-- A root pairing is thin if there is a preregular element.  Borcherds-Kac-Moody Lie
algebras more or less admit a `ℤ`-grading with finite dimensional pieces, so their root systems are
always thin. -/
def IsThin : Prop := ∃ (x : N), IsPreregular P x

/-- A regular element is a preregular element that takes no roots to zero. -/
def IsRegularElement (x : N) : Prop := (IsPreregular P x) ∧ ∀(i : ι), P.toLin (P.root i) x ≠ 0

/-- View a root as an element of the span of roots. -/
def root' : ι → (Submodule.span R (Set.range P.root)) :=
  fun i => ⟨P.root i, Submodule.subset_span <| @Set.mem_range_self _ _ P.root i⟩

/-- A base is a parametrized subset of roots forming an `R`-basis of the span of roots, such
that the coordinates of any root are all nonpositive or all nonnegative. (maybe just restrict this
definition to root systems?)-/
structure Base extends Basis α R (Submodule.span R (Set.range P.root)) where
  /-- An injection from the type parametrizing the basis to the type parametrizing roots. -/
  f : α ↪ ι
  /-- Any basis vector is equal to the corresponding root. -/
  eq_root : ∀ (i : α), DFunLike.coe repr.symm (Finsupp.single i 1) = P.root (f i)
  /-- Any root has same-sign coordinates with respect to the basis. -/
  same_sign : ∀(i : ι) (j k : α), 0 ≤ (repr (P.root' i) j) * (repr (P.root' i) k)

/-- An root is indecomposable if it is positive, and cannot be written as a sum of two positive
roots. -/
def IsIndecomposableFor (x : N) (i : ι) : Prop :=
  P.toLin (P.root i) x > 0 ∧ ¬ ∃(a b : ι),
  P.toLin (P.root a) x > 0 ∧ P.toLin (P.root b) x > 0 ∧ P.root i = P.root a + P.root b

/-!
lemma if `x` is regular, and ι is finite then the indecomposable elements for `x` are a base.
(tricky to generalize, since the proof uses positive-definiteness - maybe semidefinite is okay, so
we can do affine roots.  False in general.)

Make a Cartan matrix.

Show that the Cartan matrix is unique?
Show that there is one Weyl orbit of bases, up to sign?

-/
