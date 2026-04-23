/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.EquivalencePseudoabelian
public import Mathlib.AlgebraicTopology.DoldKan.Normalized
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!

# The Dold-Kan correspondence

The Dold-Kan correspondence states that for any abelian category `A`, there is
an equivalence between the category of simplicial objects in `A` and the
category of chain complexes in `A` (with degrees indexed by `ℕ` and the
homological convention that the degree is decreased by the differentials).

In this file, we finish the construction of this equivalence by providing
`CategoryTheory.Abelian.DoldKan.equivalence` which is of type
`SimplicialObject A ≌ ChainComplex A ℕ` for any abelian category `A`.
The functor `SimplicialObject A ⥤ ChainComplex A ℕ` of this equivalence is
definitionally equal to `normalizedMooreComplex A`.

## Overall strategy of the proof of the correspondence

Before starting the implementation of the proof in Lean, the author noticed
that the Dold-Kan equivalence not only applies to abelian categories, but
should also hold generally for any pseudoabelian category `C`
(i.e. a category with instances `[Preadditive C]`
`[HasFiniteCoproducts C]` and `[IsIdempotentComplete C]`): this is
`CategoryTheory.Idempotents.DoldKan.equivalence`.

When the alternating face map complex `K[X]` of a simplicial object `X` in an
abelian is studied, it is shown that it decomposes as a direct sum of the
normalized subcomplex and of the degenerate subcomplex. The crucial observation
is that in this decomposition, the projection on the normalized subcomplex can
be defined in each degree using simplicial operators. Then, the definition
of this projection `PInfty : K[X] ⟶ K[X]` can be carried out for any
`X : SimplicialObject C` when `C` is a preadditive category.

The construction of the endomorphism `PInfty` is done in the files
`Homotopies.lean`, `Faces.lean`, `Projections.lean` and `PInfty.lean`.
Eventually, as we would also like to show that the inclusion of the normalized
Moore complex is a homotopy equivalence (cf. file `HomotopyEquivalence.lean`),
this projection `PInfty` needs to be homotopic to the identity. In our
construction, we get this for free because `PInfty` is obtained by altering
the identity endomorphism by null homotopic maps. More details about this
aspect of the proof are in the file `Homotopies.lean`.

When the alternating face map complex `K[X]` is equipped with the idempotent
endomorphism `PInfty`, it becomes an object in `Karoubi (ChainComplex C ℕ)`
which is the idempotent completion of the category `ChainComplex C ℕ`. In `FunctorN.lean`,
we obtain this functor `N₁ : SimplicialObject C ⥤ Karoubi (ChainComplex C ℕ)`,
which is formally extended as
`N₂ : Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C ℕ)`. (Here, some functors
have an index which is the number of occurrences of `Karoubi` at the source or the
target.)

In `FunctorGamma.lean`, assuming that the category `C` is additive,
we define the functor in the other direction
`Γ₂ : Karoubi (ChainComplex C ℕ) ⥤ Karoubi (SimplicialObject C)` as the formal
extension of a functor `Γ₀ : ChainComplex C ℕ ⥤ SimplicialObject C` which is
defined similarly as in [*Simplicial Homotopy Theory* by Goerss-Jardine][goerss-jardine-2009].
In `Degeneracies.lean`, we show that `PInfty` vanishes on the image of degeneracy
operators, which is one of the key properties that makes it possible to construct
the isomorphism `N₂Γ₂ : Γ₂ ⋙ N₂ ≅ 𝟭 (Karoubi (ChainComplex C ℕ))`.

The rest of the proof follows the strategy in the [original paper by Dold][dold1958]. We show
that the functor `N₂` reflects isomorphisms in `NReflectsIso.lean`: this relies on a
decomposition of the identity of `X _⦋n⦌` using `PInfty.f n` and degeneracies obtained in
`Decomposition.lean`. Then, in `NCompGamma.lean`, we construct a natural transformation
`Γ₂N₂.trans : N₂ ⋙ Γ₂ ⟶ 𝟭 (Karoubi (SimplicialObject C))`. It is shown that it is an
isomorphism using the fact that `N₂` reflects isomorphisms, and because we can show
that the composition `N₂ ⟶ N₂ ⋙ Γ₂ ⋙ N₂ ⟶ N₂` is the identity (see `identity_N₂`). The fact
that `N₂` is defined as a formal direct factor makes the proof easier because we only
have to compare endomorphisms of an alternating face map complex `K[X]` and we do not
have to worry with inclusions of kernel subobjects.

In `EquivalenceAdditive.lean`, we obtain
the equivalence `equivalence : Karoubi (SimplicialObject C) ≌ Karoubi (ChainComplex C ℕ)`.
It is in the namespace `CategoryTheory.Preadditive.DoldKan`. The functors in this
equivalence are named `N` and `Γ`: by definition, they are `N₂` and `Γ₂`.

In `EquivalencePseudoabelian.lean`, assuming `C` is idempotent complete,
we obtain `equivalence : SimplicialObject C ≌ ChainComplex C ℕ`
in the namespace `CategoryTheory.Idempotents.DoldKan`. This could be roughly
obtained by composing the previous equivalence with the equivalences
`SimplicialObject C ≌ Karoubi (SimplicialObject C)` and
`Karoubi (ChainComplex C ℕ) ≌ ChainComplex C ℕ`. Instead, we polish this construction
in `Compatibility.lean` by ensuring good definitional properties of the equivalence (e.g.
the inverse functor is definitionally equal to
`Γ₀ : ChainComplex C ℕ ⥤ SimplicialObject C`, which is induced by `Γ₀'`) and
showing compatibilities for the unit and counit isomorphisms.

In this file `Equivalence.lean`, assuming the category `A` is abelian, we obtain
`equivalence : SimplicialObject A ≌ ChainComplex A ℕ` in the namespace
`CategoryTheory.Abelian.DoldKan`. This is obtained by replacing the functor
`CategoryTheory.Idempotents.DoldKan.N` of the equivalence in the pseudoabelian case
with the isomorphic functor `normalizedMooreComplex A` thanks to the isomorphism
obtained in `Normalized.lean`.

TODO: Show functoriality properties of the three equivalences above. More precisely,
for example in the case of abelian categories `A` and `B`, if `F : A ⥤ B` is an
additive functor, we can show that the functors `N` for `A` and `B` are compatible
with the functors `SimplicialObject A ⥤ SimplicialObject B` and
`ChainComplex A ℕ ⥤ ChainComplex B ℕ` induced by `F`. (Note that this does not
require that `F` is an exact functor!)

TODO: Introduce the degenerate subcomplex `D[X]` which is generated by
degenerate simplices, show that the projector `PInfty` corresponds to
a decomposition `K[X] ≅ N[X] ⊞ D[X]`.

TODO: dualise all of this as `CosimplicialObject A ⥤ CochainComplex A ℕ`. (It is unclear
what is the best way to do this. The exact design may be decided when it is needed.)

## References
* [Albrecht Dold, Homology of Symmetric Products and Other Functors of Complexes][dold1958]
* [Paul G. Goerss, John F. Jardine, Simplicial Homotopy Theory][goerss-jardine-2009]

-/

@[expose] public section


noncomputable section

open CategoryTheory Category Idempotents

variable {A : Type*} [Category* A] [Abelian A]

namespace CategoryTheory

namespace Abelian

namespace DoldKan

open AlgebraicTopology.DoldKan

/-- The functor `N` for the equivalence is `normalizedMooreComplex A` -/
def N : SimplicialObject A ⥤ ChainComplex A ℕ :=
  AlgebraicTopology.normalizedMooreComplex A

/-- The functor `Γ` for the equivalence is the same as in the pseudoabelian case. -/
def Γ : ChainComplex A ℕ ⥤ SimplicialObject A :=
  Idempotents.DoldKan.Γ

/-- The comparison isomorphism between `normalizedMooreComplex A` and
the functor `Idempotents.DoldKan.N` from the pseudoabelian case -/
@[simps!]
def comparisonN : (N : SimplicialObject A ⥤ _) ≅ Idempotents.DoldKan.N :=
  calc
    N ≅ N ⋙ 𝟭 _ := Functor.leftUnitor N
    _ ≅ N ⋙ (toKaroubiEquivalence _).functor ⋙ (toKaroubiEquivalence _).inverse :=
          Functor.isoWhiskerLeft _ (toKaroubiEquivalence _).unitIso
    _ ≅ (N ⋙ (toKaroubiEquivalence _).functor) ⋙ (toKaroubiEquivalence _).inverse :=
          Iso.refl _
    _ ≅ N₁ ⋙ (toKaroubiEquivalence _).inverse :=
          Functor.isoWhiskerRight (N₁_iso_normalizedMooreComplex_comp_toKaroubi A).symm _
    _ ≅ Idempotents.DoldKan.N := Iso.refl _

/-- The Dold-Kan equivalence for abelian categories -/
@[simps! functor]
def equivalence : SimplicialObject A ≌ ChainComplex A ℕ :=
  (Idempotents.DoldKan.equivalence (C := A)).changeFunctor comparisonN.symm

theorem equivalence_inverse : (equivalence : SimplicialObject A ≌ _).inverse = Γ :=
  rfl

end DoldKan

end Abelian

end CategoryTheory
