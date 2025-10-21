/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Lie.BaseChange
--import Mathlib.Algebra.Lie.InvariantForm
--import Mathlib.Algebra.Lie.Extension.Basic
import Mathlib.Algebra.Polynomial.Laurent

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


## Main definitions

* Loop Algebra
* Evaluation representation
* Construction of central extensions from invariant forms. (todo)
* representation with fixed central character (todo)
* Positive energy representation (todo)

## Tags

lie ring, lie algebra, base change, Laurent polynomial, central extension
-/

suppress_compilation

open scoped TensorProduct

variable (R A L M : Type*)

namespace LieAlgebra

variable [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- A loop algebra is the base change of a Lie algebra `L` over `R` by `R[z,z^{-1}]`, seen
as a Lie algebra over `R`. -/
abbrev LoopAlgebra := RestrictScalars R (LaurentPolynomial R) (LaurentPolynomial R ⊗[R] L)

namespace LoopAlgebra

instance instLieRing : LieRing (LoopAlgebra R L) :=
  ExtendScalars.instLieRing R (LaurentPolynomial R) L

instance instLieAlgebra : LieAlgebra R (LoopAlgebra R L) :=
  LieAlgebra.RestrictScalars.lieAlgebra R (LaurentPolynomial R) (LaurentPolynomial R ⊗[R] L)

/-- The linear map taking `x` to `T ^ n ⊗ x`. -/
def monomial (n : ℤ) : L →ₗ[R] LoopAlgebra R L where
  toFun x := (RestrictScalars.addEquiv R (LaurentPolynomial R) (LaurentPolynomial R ⊗[R] L)).symm
    (LaurentPolynomial.T n ⊗ₜ x)
  map_add' x y := by
    rw [AddEquiv.symm_apply_eq, map_add, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      ← TensorProduct.tmul_add]
  map_smul' r x := by
    rw [AddEquiv.symm_apply_eq, RestrictScalars.addEquiv_map_smul, AddEquiv.apply_symm_apply,
      IsScalarTower.algebraMap_smul, RingHom.id_apply, TensorProduct.tmul_smul]

@[simp]
lemma addEquiv_monomial (n : ℤ) (x : L) :
    (RestrictScalars.addEquiv R (LaurentPolynomial R) (LaurentPolynomial R ⊗[R] L))
      (monomial R L n x) = (LaurentPolynomial.T n ⊗ₜ x) :=
  rfl

lemma monomial_smul (r : R) (n : ℤ) (x : L) : monomial R L n (r • x) = r • (monomial R L n x) :=
  LinearMap.CompatibleSMul.map_smul (monomial R L n) r x

/-!
lemma monomial_eq_iff (n : ℤ) (x : L) : monomial R L n x = 0 ↔ x = 0 := by
  simp only [monomial, LinearMap.coe_mk, AddHom.coe_mk, EmbeddingLike.map_eq_zero_iff]
  constructor
  · cases subsingleton_or_nontrivial R
    · have : Subsingleton L := Module.subsingleton R L
      exact fun a ↦ Subsingleton.eq_zero x
    intro h
    rw [LaurentPolynomial.T] at h
    have : Finsupp.single n 1 ≠ 0 := by
      intro h'
      rw [Finsupp.single_eq_zero] at h'
      apply Nat.one_ne_zero h'
    --rw [← TensorProduct.zero_tmul (LaurentPolynomial R) x] at h



    sorry
  · intro h
    simp [h]
-/
/-- Construct an element of the loop algebra from a finitely supported function. -/
def ofFinsupp : Finsupp ℤ L →ₗ[R] LoopAlgebra R L where
  toFun f := ∑ n ∈ f.support, monomial R L n (f n)
  map_add' x y := by
    simp only [Finsupp.coe_add, Pi.add_apply, map_add]
    have hxy : x.support ⊆ x.support ∪ y.support := Finset.subset_union_left
    have hyx : y.support ⊆ x.support ∪ y.support := Finset.subset_union_right
    rw [Finset.sum_subset Finsupp.support_add, Finset.sum_add_distrib, Finset.sum_subset hxy,
      Finset.sum_subset hyx]
    · intro _ _ h
      rw [Finsupp.notMem_support_iff] at h
      simp [h]
    · intro _ _ h
      rw [Finsupp.notMem_support_iff] at h
      simp [h]
    · intro n hn h
      rw [Finsupp.notMem_support_iff, Finsupp.add_apply, add_eq_zero_iff_eq_neg] at h
      simp [h]
  map_smul' r x := by
    rw [Finset.sum_subset Finsupp.support_smul
      (fun _ _ hs ↦ by rw [Finsupp.notMem_support_iff] at hs; simp [hs]),
      Finset.smul_sum, RingHom.id_apply]
    exact Finset.sum_congr rfl fun _ _ ↦ by simp

-- I need a way to construct linear maps out of LoopAlgebra, by specifying the map on
-- `x ⊗ T ^ n` for `x ∈ L`.  Maybe first a lemma saying LoopAlgebra is spanned by such things.

/-!
/-- The evaluation representation, given by composing a representation with the evaluation map
`L[z,z^{-1}] → L` attached to a unit in `R`. -/
--define eval (x : Units R) : (LoopAlgebra R L) →ₗ⁅R⁆ L where
  toFun l := sorry
  map_add' := sorry
  map_smul' := sorry
  map_lie' := sorry

/-- The evaluation module -/
-- define eval.LieModule
-/

section CentralExt
/-!
/-- The residue pairing on a Loop algebra. -/
def residuePairing (Φ : LinearMap.BilinForm R L)
    (hΦ : LinearMap.BilinForm.lieInvariant L Φ) :
    (LoopAlgebra R L) →ₗ[R] (LoopAlgebra R L) →ₗ[R] R where
  toFun f := {
    toFun := fun g => by

      sorry -- Res_{z = 0} f dg.
    map_add' := sorry
    map_smul' := sorry }
  map_add' := sorry
  map_smul' := sorry

/-- A 2-cocycle on a loop algebra given by an invariant bilinear form. -/
def twoCocycle_of_Bilinear (Φ : LinearMap.BilinForm R L)
    (hΦ : LinearMap.BilinForm.lieInvariant L Φ) :
    LieExtension.twoCocycleTriv R (LoopAlgebra R L) R where
  toFun := sorry -- residue pairing
  map_eq_zero_of_eq' := sorry
  cocycle := sorry

--⁅A ⊗ f(t), B ⊗ g(t)⁆ = ⁅A,B⁆ ⊗ f(t)*g(t) + (Res fdg) * (A,B) • K
-/
-- show that an invariant bilinear form on `L` produces a 2-cocycle for `LoopAlgebra R L`.
-- define central extensions given by invariant bilinear forms
-- extend central characters to reps of positive part
-- induce positive part reps to centrally extended loop algebra
-- monomial basis of induced rep (needs PBW)
-- define positive energy reps (positive part `U+` acts locally nilpotently - `U+ • v` fin dim.)

end CentralExt

end LoopAlgebra

end LieAlgebra
