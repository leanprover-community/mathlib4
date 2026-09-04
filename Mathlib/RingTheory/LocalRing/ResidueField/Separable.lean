/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances

/-!
# Separable residue field extensions

For a prime `p` of `A`, we introduce a predicate stating that the residue field extensions
`κ(P)/κ(p)` are separable for every prime `P` of `B` lying over `p`.

## Main definitions

* `Algebra.HasSeparableResidueFieldsAt A B p`: the residue field extension `κ(P)/κ(p)` is
  separable for every prime `P` of `B` lying over `p`.

## Main results

* instances deducing `Algebra.HasSeparableResidueFieldsAt` when the residue field `κ(p)` is
  perfect, and when `A` has finite quotients and `p` is nonzero;
* `Algebra.HasSeparableResidueFieldsAt.isSeparable_quotient`: at a maximal prime, the predicate
  also gives the separability of the extensions of quotient rings;
* `Algebra.HasSeparableResidueFieldsAt.tower_top` and
  `Algebra.HasSeparableResidueFieldsAt.tower_bot`: the predicate passes to an intermediate ring.

## Implementation notes

The condition is on the residue fields rather than on the quotient rings `(B ⧸ P)/(A ⧸ p)` so that
it makes sense at any prime: the quotients are fields only at maximal primes.

The algebra structure on `κ(P)` over `κ(p)` in the predicate is the one induced by the algebra
structure on `Localization.AtPrime P` over `Localization.AtPrime p` given by
`Localization.AtPrime.algebraOfLiesOver`. Any other structure making `Localization.AtPrime P` an
algebra over `Localization.AtPrime p` in a compatible way with the action of `A` is equal to that
one, see `Localization.AtPrime.algebraMap_eq`.
-/

@[expose] public section

open Ideal

namespace Algebra

section Prime

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] (p : Ideal A) [p.IsPrime]

/-- `Algebra.HasSeparableResidueFieldsAt A B p` states that for every prime `P` of `B` lying over
`p`, the residue field extension `κ(P)/κ(p)` is separable. -/
class HasSeparableResidueFieldsAt : Prop where
  isSeparable' (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    letI := Localization.AtPrime.algebraOfLiesOver p P
    Algebra.IsSeparable p.ResidueField P.ResidueField

variable {A B p} in
/-- `Algebra.HasSeparableResidueFieldsAt` gives the separability for any compatible choice of the
algebra structure on the localizations. -/
instance HasSeparableResidueFieldsAt.isSeparable (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    [HasSeparableResidueFieldsAt A B p]
    [alg : Algebra (Localization.AtPrime p) (Localization.AtPrime P)]
    [IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime P)] :
    Algebra.IsSeparable p.ResidueField P.ResidueField :=
  have : alg = Localization.AtPrime.algebraOfLiesOver p P :=
    Algebra.algebra_ext _ _ fun _ ↦ by rw [Localization.AtPrime.algebraMap_eq]; rfl
  this ▸ HasSeparableResidueFieldsAt.isSeparable' P

variable [Algebra.IsIntegral A B]

/-- If the residue field `κ(p)` is perfect, the residue field extensions above `p` are separable. -/
instance [PerfectField p.ResidueField] : HasSeparableResidueFieldsAt A B p where
  isSeparable' P _ _ :=
    letI := Localization.AtPrime.algebraOfLiesOver p P
    IsAlgebraic.isSeparable_of_perfectField

/-- If `A` has finite quotients, the residue field extensions above a nonzero prime of `A` are
separable. -/
instance [NeZero p] [Ring.HasFiniteQuotients A] : HasSeparableResidueFieldsAt A B p :=
  haveI : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne p)
  inferInstance

end Prime

section Maximal

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : Ideal A) [p.IsMaximal]

/-- At a maximal prime `p`, `Algebra.HasSeparableResidueFieldsAt` also gives the separability of
the extension of quotient rings `(B ⧸ P)/(A ⧸ p)` for every maximal ideal `P` of `B` lying over
`p`. Maximality is needed for the quotient rings to be fields; they are then canonically
isomorphic to the residue fields. -/
instance HasSeparableResidueFieldsAt.isSeparable_quotient [HasSeparableResidueFieldsAt A B p]
    (P : Ideal B) [P.IsMaximal] [P.LiesOver p] :
    Algebra.IsSeparable (A ⧸ p) (B ⧸ P) :=
  letI := Localization.AtPrime.algebraOfLiesOver p P
  Algebra.isSeparable_residueField_iff.mp (HasSeparableResidueFieldsAt.isSeparable' P)

end Maximal

section Tower

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  (p : Ideal A) [p.IsPrime]

/-- For a tower of rings `C/B/A`, separability of the residue field extensions of `C/A` above `p`
gives separability of those of `B/A` above `p`. -/
theorem HasSeparableResidueFieldsAt.tower_bot [Algebra.IsIntegral B C] [FaithfulSMul B C]
    [HasSeparableResidueFieldsAt A C p] : HasSeparableResidueFieldsAt A B p where
  isSeparable' q _ _ := by
    obtain ⟨r, _, _⟩ : Nonempty (q.primesOver C) := nonempty_primesOver q
    have : r.LiesOver p := Ideal.LiesOver.trans r q p
    let := Localization.AtPrime.algebraOfLiesOver p q
    let := Localization.AtPrime.algebraOfLiesOver p r
    let := Localization.AtPrime.algebraOfLiesOver q r
    exact isSeparable_tower_bot_of_isSeparable p.ResidueField q.ResidueField r.ResidueField

variable (q : Ideal B) [q.IsPrime] [q.LiesOver p]

/-- For a tower of rings `C/B/A` and a prime `q` of `B` lying over `p`, separability of the
residue field extensions of `C/A` above `p` gives separability of those of `C/B` above `q`. -/
theorem HasSeparableResidueFieldsAt.tower_top [HasSeparableResidueFieldsAt A C p] :
    HasSeparableResidueFieldsAt B C q where
  isSeparable' r _ _ :=
    haveI : r.LiesOver p := Ideal.LiesOver.trans r q p
    letI := Localization.AtPrime.algebraOfLiesOver p q
    letI := Localization.AtPrime.algebraOfLiesOver p r
    letI := Localization.AtPrime.algebraOfLiesOver q r
    isSeparable_tower_top_of_isSeparable p.ResidueField _ _

end Tower

end Algebra
