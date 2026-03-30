/-
Copyright (c) 2026 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Algebra.Lie.Cochain
public import Mathlib.Algebra.Lie.InvariantForm
public import Mathlib.Algebra.Polynomial.Laurent

/-!
# Loop Lie algebras and their central extensions
Given a Lie algebra `L`, the loop algebra is the Lie algebra of maps from a circle into `L`. This
can mean many different things, e.g., continuous maps, smooth maps, polynomial maps. In this file,
we consider the simplest case of polynomial maps, meaning we take a base change with the ring of
Laurent polynomials.

Loop Lie algebras admit central extensions attached to invariant inner products on the base Lie
algebra. When the base Lie algebra is finite dimensional and simple, the corresponding central
extension (with an outer derivation attached) admits an infinite root system with affine Weyl group.
These extended Lie algebras are called untwisted affine Kac-Moody Lie algebras.

We implement the basic theory using `AddMonoidAlgebra` instead of `LaurentPolynomial` for
flexibility. The classical loop algebra is then written `loopAlgebra R ℤ L`.

## Main definitions
* `LieAlgebra.loopAlgebra`: The tensor product of a Lie algebra with an `AddMonoidAlgebra`.
* `LieAlgebra.loopAlgebra.toFinsupp`: A linear equivalence from the loop algebra to the space of
  finitely supported functions.
* `LieAlgebra.loopAlgebra.twoCochainOfBilinear`: The 2-cochain for a loop algebra with trivial
  coefficients attached to a symmetric bilinear form on the base Lie algebra.
* `LieAlgebra.loopAlgebra.twoCocycleOfBilinear`: The 2-cocycle for a loop algebra with trivial
  coefficients attached to a symmetric invariant bilinear form on the base Lie algebra.

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

/-- A loop algebra is the base change of a Lie algebra `L` over `R` by `R[z,z⁻¹]`. We make a
slightly more general definition which coincides with the Laurent polynomial construction when
`A = ℤ` -/
abbrev loopAlgebra := AddMonoidAlgebra R A ⊗[R] L

open LaurentPolynomial in
/-- An Lie algebra isomorphism between the Loop algebra (with `A = ℤ`) and the tensor product with
Laurent polynomials. -/
def loopAlgebraEquivLaurent :
    loopAlgebra R ℤ L ≃ₗ⁅R⁆ R[T;T⁻¹] ⊗[R] L :=
  LieEquiv.refl

namespace LoopAlgebra

open Classical in
/-- A linear isomorphism to finitely supported functions. -/
def toFinsupp : loopAlgebra R A L ≃ₗ[R] A →₀ L :=
  TensorProduct.equivFinsuppOfBasisLeft (AddMonoidAlgebra.basis A R)

@[simp]
lemma toFinsupp_symm_single (c : A) (z : L) :
    (toFinsupp R A L).symm (Finsupp.single c z) = AddMonoidAlgebra.single c 1 ⊗ₜ[R] z := by
  simp [toFinsupp]

@[simp]
lemma toFinsupp_single_tmul (c : A) (z : L) :
    (toFinsupp R A L (AddMonoidAlgebra.single c 1 ⊗ₜ[R] z)) = Finsupp.single c z := by
  simp [← toFinsupp_symm_single]

open Finsupp in
/-- The residue pairing on the loop algebra.  When `A = ℤ` and the elements are viewed as Laurent
polynomials with coefficients in `L`, the pairing is interpreted as `(f, g) ↦ Res f dg`. -/
@[simps]
def residuePairing [AddCommGroup A] [DistribSMul A R] [SMulCommClass A R R]
    (Φ : LinearMap.BilinForm R L) :
    LinearMap.BilinForm R (loopAlgebra R A L) where
  toFun f :=
    letI F := toFinsupp R A L
    { toFun g := (F g).sum fun a v ↦ a • Φ (F f (-a)) v
      map_add' x y := by
        classical
        let u : Finset A := (F x).support ∪ (F y).support
        have hu₁ : (F x).support ⊆ u := Finset.subset_union_left
        have hu₂ : (F y).support ⊆ u := Finset.subset_union_right
        have hu₃ : (F (x + y)).support ⊆ u := fun a ha ↦ by
          replace ha : F x a + F y a ≠ 0 := by simpa using ha
          grind
        rw [sum_of_support_subset _ hu₃ _ (by simp), sum_of_support_subset _ hu₁ _ (by simp),
          sum_of_support_subset _ hu₂ _ (by simp)]
        simp [Finset.sum_add_distrib, u]
      map_smul' r x := by
        rw [map_smul, sum_of_support_subset _ support_smul _ (by simp), sum, Finset.smul_sum]
        simp [-smul_eq_mul, smul_comm] }
  map_add' x y := by ext; simp [sum_add]
  map_smul' r x := by ext; simp [-smul_eq_mul, smul_comm]

open LieModule in
/-- A 2-cochain on a loop algebra given by an invariant bilinear form. When `A = ℤ`, the alternating
condition amounts to the fact that Res f df = 0. -/
def twoCochainOfBilinear [CommRing A] [IsAddTorsionFree R] [Algebra A R]
    (Φ : LinearMap.BilinForm R L) (hΦ : Φ.IsSymm) :
    Cohomology.twoCochain R (loopAlgebra R A L) (TrivialLieModule R (loopAlgebra R A L) R) where
  val := (residuePairing R A L Φ).compr₂ (TrivialLieModule.equiv R (loopAlgebra R A L) R).symm
  property := by
    refine Cohomology.mem_twoCochain_iff.mpr fun f ↦ ?_
    letI F := toFinsupp R A L
    suffices ((F f).sum fun a v ↦ a • Φ (F f (-a)) v) = 0 by simpa
    classical
    set s := (F f).support ∪ (F f).support.image (Equiv.neg A) with hs
    have hs' : (F f).support ⊆ s := Finset.subset_union_left
    rw [Finsupp.sum_of_support_subset _ hs' _ (by simp)]
    refine Function.Odd.finset_sum_eq_zero (fun n ↦ by simp [hΦ.eq]) (Finset.map_eq_of_subset ?_)
    intro x hx
    rw [Finset.mem_union]
    replace hx : -x ∈ (F f).support ∨ -x ∈ (F f).support.image Neg.neg := by simpa [hs] using hx
    obtain (h | h) := hx
    · exact Or.inr <| Finset.mem_image.mpr ⟨-x, by simp [h]⟩
    · exact Or.inl <| by simpa using h

@[simp]
lemma twoCochainOfBilinear_apply_apply [CommRing A] [IsAddTorsionFree R] [Algebra A R]
    (Φ : LinearMap.BilinForm R L) (hΦ : Φ.IsSymm) (x y : loopAlgebra R A L) :
    twoCochainOfBilinear R A L Φ hΦ x y =
      (TrivialLieModule.equiv R (loopAlgebra R A L) R).symm (residuePairing R A L Φ x y) :=
  rfl

open LieModule in
/-- A 2-cocycle on a loop algebra given by an invariant bilinear form. -/
@[simps]
def twoCocycleOfBilinear [CommRing A] [IsAddTorsionFree R] [Algebra A R]
    (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) :
    Cohomology.twoCocycle R (loopAlgebra R A L) (TrivialLieModule R (loopAlgebra R A L) R) where
  val := twoCochainOfBilinear R A L Φ hΦs
  property := by
    apply (LieModule.Cohomology.mem_twoCocycle_iff ..).mpr
    ext a x b y c z
    suffices
        b • Φ (Finsupp.single (a + c) ⁅x, z⁆ (-b)) y =
        c • Φ (Finsupp.single (a + b) ⁅x, y⁆ (-c)) z +
        a • Φ (Finsupp.single (b + c) ⁅y, z⁆ (-a)) x by
      simpa [sub_eq_zero, neg_add_eq_iff_eq_add, ← LinearEquiv.map_add, -LinearEquiv.map_add]
    by_cases h0 : a + b + c = 0
    · suffices b • Φ ⁅x, z⁆ y = c • Φ ⁅x, y⁆ z + a • Φ ⁅y, z⁆ x by
        simpa only [show a + b = -c by grind, show a + c = -b by grind, show b + c = -a by grind,
          Finsupp.single_eq_same]
      rw [hΦ, hΦs.eq z ⁅x, y⁆, hΦ y, ← lie_skew y x, hΦs.eq z, Φ.neg_left, neg_neg,
        show b = -(a + c) by grind, neg_smul, smul_neg, neg_neg, add_smul, add_comm]
    · simp [Finsupp.single_eq_of_ne (a := a + c) (a' := -b) (by grind),
        Finsupp.single_eq_of_ne (a := a + b) (a' := -c) (by grind),
        Finsupp.single_eq_of_ne (a := b + c) (a' := -a) (by grind)]

end LoopAlgebra

end LieAlgebra
