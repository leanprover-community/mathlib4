/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Induced

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

In `Mathlib/RepresentationTheory/Homological/GroupHomology/Induced.lean`,
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

universe u

namespace groupHomology

open CategoryTheory Finsupp TensorProduct Rep Representation

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) (A : Rep k S)

/-- Given a projective resolution `P` of `k` as a `k`-linear `G`-representation, a subgroup
`S ≤ G`, and a `k`-linear `S`-representation `A`, this is an isomorphism of complexes
`(A ⊗ Res(S)(P))_S ≅ (Ind_S^G(A) ⊗ P)_G`. -/
noncomputable abbrev coinvariantsTensorResProjectiveResolutionIso
    (P : ProjectiveResolution (Rep.trivial k G k)) :
    ((Action.res _ S.subtype).mapProjectiveResolution P).complex.coinvariantsTensorObj A ≅
      P.complex.coinvariantsTensorObj (ind S.subtype A) :=
  (NatIso.mapHomologicalComplex (coinvariantsTensorIndNatIso S.subtype A).symm _).app _

/-- Shapiro's lemma: given a subgroup `S ≤ G` and an `S`-representation `A`, we have
`Hₙ(G, Ind_S^G(A)) ≅ Hₙ(S, A).` -/
noncomputable def indIso [DecidableEq G] (A : Rep k S) (n : ℕ) :
    groupHomology (ind S.subtype A) n ≅ groupHomology A n :=
  (HomologicalComplex.homologyFunctor _ _ _).mapIso (inhomogeneousChainsIso (ind S.subtype A) ≪≫
    (coinvariantsTensorResProjectiveResolutionIso S A (barResolution k G)).symm) ≪≫
  (groupHomologyIso A n ((Action.res _ _).mapProjectiveResolution <| barResolution k G)).symm

end groupHomology
