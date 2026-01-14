/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Johan Commelin
-/
import Mathlib.Algebra.Lie.Solvable

/-!
# Semisimple Lie algebras

In this file we define simple and semisimple Lie algebras, together with related concepts.

## Main declarations

* `LieModule.IsIrreducible`
* `LieAlgebra.IsSimple`
* `LieAlgebra.HasTrivialRadical`
* `LieAlgebra.IsSemisimple`

## Tags

lie algebra, radical, simple, semisimple
-/

variable (R L M : Type*)
variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M] [LieRingModule L M]

/-- A nontrivial Lie module is *irreducible* if its only Lie submodules are `⊥` and `⊤`. -/
abbrev LieModule.IsIrreducible : Prop :=
  IsSimpleOrder (LieSubmodule R L M)

variable {R L M} in
lemma LieModule.IsIrreducible.mk [Nontrivial M] (h : ∀ N : LieSubmodule R L M, N ≠ ⊥ → N = ⊤) :
    IsIrreducible R L M :=
  IsSimpleOrder.of_forall_eq_top h

lemma LieSubmodule.eq_top_of_isIrreducible [LieModule.IsIrreducible R L M]
    (N : LieSubmodule R L M) [Nontrivial N] :
    N = ⊤ :=
  (IsSimpleOrder.eq_bot_or_eq_top N).resolve_left <| (nontrivial_iff_ne_bot R L M).mp inferInstance

namespace LieAlgebra

variable [LieAlgebra R L]

/--
A Lie algebra *has trivial radical* if its radical is trivial.
This is equivalent to having no non-trivial solvable ideals,
and further equivalent to having no non-trivial abelian ideals.

In characteristic zero, it is also equivalent to `LieAlgebra.IsSemisimple`.

Note that the label 'semisimple' is apparently not universally agreed
[upon](https://mathoverflow.net/questions/149391/on-radicals-of-a-lie-algebra#comment383669_149391)
for general coefficients.

For example [Seligman, page 15](seligman1967) uses the label for `LieAlgebra.HasTrivialRadical`,
whereas we reserve it for Lie algebras that are a direct sum of simple Lie algebras.
-/
@[mk_iff] class HasTrivialRadical : Prop where
  radical_eq_bot : radical R L = ⊥

export HasTrivialRadical (radical_eq_bot)
attribute [simp] radical_eq_bot

/-- A Lie algebra *has central radical* if its radical coincides with its center. Such Lie algebras
are called *reductive*, if the coefficients are a field of characteristic zero.

Note that there is absolutely [no agreement](https://mathoverflow.net/questions/284713/) on what
the label 'reductive' should mean when the coefficients are not a field of characteristic zero. -/
@[mk_iff] class HasCentralRadical : Prop where
  radical_eq_center : radical R L = center R L

lemma hasCentralRadical_of_radical_le (h : radical R L ≤ center R L) :
    LieAlgebra.HasCentralRadical R L where
  radical_eq_center := le_antisymm h (center_le_radical R L)

instance [Subsingleton L] : HasTrivialRadical R L :=
  ⟨by simpa only [radical_eq_top_of_isSolvable] using Subsingleton.elim ⊤ ⊥⟩

export HasCentralRadical (radical_eq_center)
attribute [simp] radical_eq_center

/-- A Lie algebra is simple if it is irreducible as a Lie module over itself via the adjoint
action, and it is non-Abelian. -/
class IsSimple : Prop where
  eq_bot_or_eq_top : ∀ I : LieIdeal R L, I = ⊥ ∨ I = ⊤
  non_abelian : ¬IsLieAbelian L

/--
A *semisimple* Lie algebra is one that is a direct sum of non-abelian atomic ideals.
These ideals are simple Lie algebras, by `LieAlgebra.IsSemisimple.isSimple_of_isAtom`.

Note that the label 'semisimple' is apparently not universally agreed
[upon](https://mathoverflow.net/questions/149391/on-radicals-of-a-lie-algebra#comment383669_149391)
for general coefficients.

For example [Seligman, page 15](seligman1967) uses the label for `LieAlgebra.HasTrivialRadical`,
the weakest of the various properties which are all equivalent over a field of characteristic zero.
-/
class IsSemisimple : Prop where
  /-- In a semisimple Lie algebra, the supremum of the atoms is the whole Lie algebra. -/
  sSup_atoms_eq_top : sSup {I : LieIdeal R L | IsAtom I} = ⊤
  /-- In a semisimple Lie algebra, the atoms are independent. -/
  sSupIndep_isAtom : sSupIndep {I : LieIdeal R L | IsAtom I}
  /-- In a semisimple Lie algebra, the atoms are non-abelian. -/
  non_abelian_of_isAtom : ∀ I : LieIdeal R L, IsAtom I → ¬ IsLieAbelian I

end LieAlgebra
