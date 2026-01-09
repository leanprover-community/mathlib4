/-
Copyright (c) 2026 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.Lie.Cochain
public import Mathlib.GroupTheory.MonoidLocalization.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Loop Lie algebras and their central extensions
Given a Lie algebra `L`, the loop algebra is the Lie algebra of maps from a circle into `L`. This
can mean many different things, e.g., continuous maps, smooth maps, polynomial maps. In this file,
we consider the simplest case of polynomial maps, meaning we take a base change with the ring of
Laurent polynomials.
Representations of loop algebras are not particularly interesting - a theorem of Rao (1993) asserts
that when `L` is complex semisimple, any irreducible representation of `L[z,z^{-1}]` is just given
by evaluation of loops at a finite set of specific points. However, the theory becomes much richer
when one considers projective representations, i.e., representations of a central extension. Common
examples include generalized Verma modules, given by pulling a representation of `L` back to a
representation of `L[z] ⊕ C` along the homomorphism `z ↦ 0` together with a central character, and
inducing to the central extension of the loop algebra.
We implement the basic theory using `AddMonoidAlgebra` instead of `LaurentPolynomial` for
flexibility. The classical loop algebra is then written `LoopAlgebra R ℤ L`.

## Main definitions
* `LieAlgebra.LoopAlgebra`: The tensor product of a Lie algebra with an `AddMonoidAlgebra`.
* `LieAlgebra.LoopAlgebra.twoCochain_of_Bilinear`: The 2-cochain for a loop algebra with trivial
  coefficients attached to a symmetric bilinear form on the base Lie algebra.

## TODO
* Evaluation representations
* Construction of central extensions from invariant forms.
* Positive energy representations induced from a fixed central character

## Tags
lie ring, lie algebra, base change, Laurent polynomial
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

variable (R A L : Type*)

namespace LieAlgebra

variable [CommRing R] [LieRing L] [LieAlgebra R L]


/-- A basis of single elements. -/
def basisMonomial : Module.Basis A R (AddMonoidAlgebra R A) where
  repr := LinearEquiv.refl R (A →₀ R)
--#find_home! basisMonomial --Algebra.Lie.OfAssociative. Move to Algebra.Polynomial.Laurent?

@[simp]
lemma basisMonomial_apply (a : A) :
    basisMonomial R A a = AddMonoidAlgebra.single a 1 :=
  rfl

/-- A loop algebra is the base change of a Lie algebra `L` over `R` by `R[z,z^{-1}]`. -/
abbrev LoopAlgebra := AddMonoidAlgebra R A ⊗[R] L

namespace LoopAlgebra

open Classical in
/-- A linear isomorphism to finitely supported functions. -/
def toFinsupp : LoopAlgebra R A L ≃ₗ[R] A →₀ L :=
  TensorProduct.equivFinsuppOfBasisLeft (basisMonomial R A)

instance instLoopLieRing [AddCommMonoid A] : LieRing (LoopAlgebra R A L) :=
  ExtendScalars.instLieRing R (AddMonoidAlgebra R A) L

instance instLoopLaurentLieAlgebra [AddCommMonoid A] :
    LieAlgebra (AddMonoidAlgebra R A) (LoopAlgebra R A L) :=
  ExtendScalars.instLieAlgebra R (AddMonoidAlgebra R A) L

instance instLieModule [AddCommMonoid A] :
    LieModule (AddMonoidAlgebra R A) (LoopAlgebra R A L) (LoopAlgebra R A L) :=
  lieAlgebraSelfModule (L := LoopAlgebra R A L)

lemma residuePairing_finite_support [AddCommGroup A] [SMulZeroClass A R]
    (Φ : LinearMap.BilinForm R L) (f g : A →₀ L) :
    Finite (fun a ↦ a • (Φ (f (-a)) (g a))).support := by
  refine Finite.Set.subset ((fun a ↦ (-a)) '' f.support) ?_
  intro n hn
  simp only [Set.image_neg_eq_neg, Set.mem_neg, SetLike.mem_coe, Finsupp.mem_support_iff]
  contrapose! hn
  simp [hn]

/-- The residue pairing on finitely supported functions.  When the functions are viewed as Laurent
polynomials with coefficients in `L`, the pairing is interpreted as `(f, g) ↦ Res f dg`. -/
@[simps]
def residuePairingFinsupp [AddCommGroup A] [DistribSMul A R] [SMulCommClass A R R]
    (Φ : LinearMap.BilinForm R L) :
    (A →₀ L) →ₗ[R] (A →₀ L) →ₗ[R] R where
  toFun f := {
    toFun := fun g => ∑ᶠ a, a • (Φ (f (-a)) (g a))
    map_add' x y := by
      rw [← finsum_add_distrib (residuePairing_finite_support R A L Φ f x)
        (residuePairing_finite_support R A L Φ f y), finsum_congr]
      intro n
      simp
    map_smul' r x := by
      rw [RingHom.id_apply, smul_finsum' _ (residuePairing_finite_support R A L Φ f x),
        finsum_congr _]
      intro n
      simp [mul_smul_comm] }
  map_add' x y := by
    ext n z
    simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      Finsupp.lsingle_apply, LinearMap.add_apply]
    rw [← finsum_add_distrib (residuePairing_finite_support R A L Φ x _)
      (residuePairing_finite_support R A L Φ y _), finsum_congr]
    intro m
    simp
  map_smul' r x := by
    ext n y
    simp only [Finsupp.coe_smul, LinearMap.coe_comp, LinearMap.smul_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Function.comp_apply, RingHom.id_apply]
    rw [smul_finsum' _ (residuePairing_finite_support R A L Φ x _), finsum_congr]
    intro k
    simp [mul_smul_comm]

/-- A 2-cochain on a loop algebra given by an invariant bilinear form. The alternating condition
follows from the fact that Res f df = 0 -/
def twoCochainOfBilinear [AddCommGroup A] [IsAddTorsionFree R] [DistribSMul A R]
    [SMulCommClass A R R] (Φ : LinearMap.BilinForm R L) (hΦ : LinearMap.BilinForm.IsSymm Φ)
    (h : ∀ (a b : A) (r : R), (a + b) • r = a • r + b • r) :
    LieModule.Cohomology.twoCochain R (LoopAlgebra R A L)
      (TrivialLieModule R (LoopAlgebra R A L) R) where
  val := (((residuePairingFinsupp R A L Φ).compr₂
    ((TrivialLieModule.equiv R (LoopAlgebra R A L) R).symm.toLinearMap)).compl₂
    (toFinsupp R A L).toLinearMap).comp (toFinsupp R A L).toLinearMap
  property := by
    simp only [LieModule.Cohomology.mem_twoCochain_iff]
    intro f
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.compl₂_apply, LinearMap.compr₂_apply, residuePairingFinsupp_apply_apply,
      EmbeddingLike.map_eq_zero_iff]
    have zerosmul (r : R) : (0 : A) • r = (0 : R) := by
      have : (0 : A) • r = (0 : A) • r + (0 : A) • r := by rw [← h, zero_add (0 : A)]
      rwa [right_eq_add] at this
    set φ := fun n ↦ n • (Φ (((toFinsupp R A L) f) (-n))) (((toFinsupp R A L) f) n) with hφ
    have : Function.Odd φ := by
      intro n
      simp only [hφ, neg_neg, hΦ.eq (toFinsupp R A L f n) (toFinsupp R A L f (-n))]
      rw [eq_neg_iff_add_eq_zero, ← h, neg_add_cancel, zerosmul]
    simpa [neg_eq_self, finsum_neg_distrib, funext this] using finsum_comp_equiv (.neg A) (f := φ)

@[simp]
lemma twoCochain_of_Bilinear_apply_apply [AddCommGroup A] [IsAddTorsionFree R] [DistribSMul A R]
    [SMulCommClass A R R] (Φ : LinearMap.BilinForm R L) (hΦ : LinearMap.BilinForm.IsSymm Φ)
    (h : ∀ (a b : A) (r : R), (a + b) • r = a • r + b • r) (x y : LoopAlgebra R A L) :
    twoCochainOfBilinear R A L Φ hΦ h x y =
      (TrivialLieModule.equiv R (LoopAlgebra R A L) R).symm
        ((residuePairingFinsupp R A L Φ) (toFinsupp R A L x) (toFinsupp R A L y)) :=
  rfl

end LoopAlgebra

end LieAlgebra
