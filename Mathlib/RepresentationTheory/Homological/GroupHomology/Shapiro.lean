/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Induced
public import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
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
# Shapiro's lemma for group homology

Given a commutative ring `k` and a subgroup `S ≤ G`,
the file `Mathlib/RepresentationTheory/Coinduced.lean` proves that
the functor `Coind_S^G : Rep k S ⥤ Rep k G` preserves epimorphisms.
Since `Res(S) : Rep k G ⥤ Rep k S` is left adjoint to `Coind_S^G`,
this means `Res(S)` preserves projective objects.
Since `Res(S)` is also exact,
given a projective resolution `P` of `k` as a trivial `k`-linear `G`-representation,
`Res(S)(P)` is a projective resolution of `k` as a trivial `k`-linear `S`-representation.

In `Mathlib/RepresentationTheory/Induced.lean`,
given a `G`-representation `X`,
we define a natural isomorphism between the functors `Rep k S ⥤ ModuleCat k` sending `A` to
`(Ind_S^G A ⊗ X)_G` and to `(A ⊗ Res(S)(X))_S`. Hence a projective resolution `P` of `k` as a
trivial `G`-representation induces an isomorphism of complexes
`(Ind_S^G A ⊗ P)_G ≅ (A ⊗ Res(S)(P))_S`, and since the homology of these complexes calculate
group homology, we conclude Shapiro's lemma: `Hₙ(G, Ind_S^G(A)) ≅ Hₙ(S, A)` for all `n`.

## Main definitions

* `groupHomology.indIso A n`: Shapiro's lemma for group homology: an isomorphism
  `Hₙ(G, Ind_S^G(A)) ≅ Hₙ(S, A)`, given a subgroup `S ≤ G` and an `S`-representation `A`.

-/

@[expose] public section

universe u

namespace groupHomology

open CategoryTheory Finsupp TensorProduct Rep Representation

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) (A : Rep k S)

/-- Given a projective resolution `P` of `k` as a `k`-linear `G`-representation, a subgroup
`S ≤ G`, and a `k`-linear `S`-representation `A`, this is an isomorphism of complexes
`(A ⊗ Res(S)(P))_S ≅ (Ind_S^G(A) ⊗ P)_G`. -/
noncomputable abbrev coinvariantsTensorResProjectiveResolutionIso
    (P : ProjectiveResolution (Rep.trivial k G k)) :
    ((resFunctor S.subtype).mapProjectiveResolution P).complex.coinvariantsTensorObj A ≅
      P.complex.coinvariantsTensorObj (ind S.subtype A) :=
  (NatIso.mapHomologicalComplex (coinvariantsTensorIndNatIso S.subtype A).symm _).app _

-- The smiley face in this proof can be avoided if you replace `ind` with `ind.{_, _, _, u}`.
-- The proof still compiles without this, but it takes much longer because of universe
-- unification issues.
-- Similarly, replacing `resFunctor.{u}` with `resFunctor` works but makes the proof
-- three times as slow.
/-- Shapiro's lemma: given a subgroup `S ≤ G` and an `S`-representation `A`, we have
`Hₙ(G, Ind_S^G(A)) ≅ Hₙ(S, A).` -/
noncomputable def indIso [DecidableEq G] (A : Rep.{u} k S) (n : ℕ) :
    groupHomology (ind S.subtype A) n ≅ groupHomology A n :=
  (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) n).mapIso
  (inhomogeneousChainsIso (ind S.subtype A :) ≪≫
    (coinvariantsTensorResProjectiveResolutionIso S A (barResolution k G)).symm) ≪≫
  (groupHomologyIso A n ((resFunctor.{u} S.subtype).mapProjectiveResolution <|
    barResolution k G)).symm

end groupHomology
