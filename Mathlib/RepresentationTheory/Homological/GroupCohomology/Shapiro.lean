/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.RepresentationTheory.FiniteIndex

/-!
# Shapiro's lemma for group cohomology

Given a commutative ring `k` and a finite index subgroup `S ≤ G`, the file
`RepresentationTheory/FiniteIndex.lean` defines a natural isomorphism between the functors
`Ind_S^G, Coind_S^G : Rep k S ⥤ Rep k G`.

Using this isomorphism, we conclude that the `(Co)ind_S^G` and `Res(S) : Rep k G ⥤ Rep k S` are
both left and right adjoint to each other, and thus that `Res(S)` is an exact functor which
preserves projective objects. In particular, given a projective resolution `P` of `k` as a trivial
`k`-linear `G`-representation, `Res(S)(P)` is a projective resolution of `k` as a trivial
`k`-linear `S`-representation.

Since `Hom(Res(S)(P), A) ≅ Hom(P, Coind_S^G(A))` for any `S`-representation `A`, we conclude
Shapiro's lemma for group cohomology: `Hⁿ(G, Coind_S^G(A)) ≅ Hⁿ(S, A)` for all `n`.

## Main definitions

* `groupCohomology.coindIso A n`: Shapiro's lemma for group cohomology: an isomorphism
  `Hⁿ(G, Coind_S^G(A)) ≅ Hⁿ(S, A)`, given a finite index subgroup `S ≤ G` and an
  `S`-representation `A`.

!-/

universe u

namespace groupCohomology

open CategoryTheory Finsupp TensorProduct Rep

variable {k G : Type u} [CommRing k] [Group G] {S : Subgroup G}
  [DecidableRel (QuotientGroup.rightRel S)] [S.FiniteIndex] (A : Rep k S)

/-- Given a projective resolution `P` of `k` as a `k`-linear `G`-representation, a finite index
subgroup `S ≤ G`, and a `k`-linear `S`-representation `A`, this is an isomorphism of complexes
`Hom(Res(S)(P), A) ≅ Hom(P, Coind_S^G(A)).` -/
noncomputable def linearYonedaObjResProjectiveResolutionIso
    (P : ProjectiveResolution (trivial k G k)) (A : Rep k S) :
    ((Action.res _ S.subtype).mapProjectiveResolution P).complex.linearYonedaObj k A ≅
      P.complex.linearYonedaObj k (coind S.subtype A) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ => (resCoindHomEquiv _ _ _).toModuleIso) fun _ _ _ =>
      ModuleCat.hom_ext (LinearMap.ext fun f => Action.Hom.ext <| by ext; simp [hom_comm_apply])

/-- Shapiro's lemma: given a finite index subgroup `S ≤ G` and an `S`-representation `A`, we have
`Hⁿ(G, Coind_S^G(A)) ≅ Hⁿ(S, A).` -/
noncomputable def coindIso [DecidableEq G] (A : Rep k S) (n : ℕ) :
    groupCohomology (coind S.subtype A) n ≅ groupCohomology A n :=
  (HomologicalComplex.homologyFunctor _ _ _).mapIso
    (inhomogeneousCochainsIso (coind S.subtype A) ≪≫
    (linearYonedaObjResProjectiveResolutionIso (barResolution k G) A).symm) ≪≫
  (groupCohomologyIso A n ((Action.res _ _).mapProjectiveResolution <| barResolution k G)).symm

end groupCohomology
