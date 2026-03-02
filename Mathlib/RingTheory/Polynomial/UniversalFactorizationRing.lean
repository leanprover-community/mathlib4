/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!

# Universal factorization ring

Let `R` be a commutative ring and `p : R[X]` be monic of degree `n` and let `n = m + k`.
We construct the universal ring of the following functors on `R-Alg`:
- `S ↦ "monic polynomials over S of degree n"`:
  Represented by `R[X₁,...,Xₙ]`. See `MvPolynomial.mapEquivMonic`.
- `S ↦ "factorizations of p into (monic deg m) * (monic deg k) in S"`:
  Represented by an `R`-algebra that is finitely-presented as an `R`-module (TODO).
- `S ↦ "factorizations of p into coprime (monic deg m) * (monic deg k) in S"`:
  Represented by an etale `R`-algebra (TODO).

-/

@[expose] public section

open scoped Polynomial TensorProduct

open RingHomClass (toRingHom)

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable (n m k : ℕ) (hn : n = m + k)

noncomputable section

namespace Polynomial

/-- The free monic polynomial of degree `n`, as a polynomial in `R[X₁,...,Xₙ][X]`. -/
def freeMonic : (MvPolynomial (Fin n) R)[X] :=
  .X ^ n + ∑ i : Fin n, .C (.X i) * .X ^ (i : ℕ)

lemma coeff_freeMonic :
    (freeMonic R n).coeff k = if h : k < n then .X ⟨k, h⟩ else if k = n then 1 else 0 := by
  simp only [freeMonic, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finset_sum_coeff,
    Polynomial.coeff_C_mul, mul_ite, mul_one, mul_zero]
  by_cases h : k < n
  · simp +contextual [Finset.sum_eq_single (ι := Fin n) (a := ⟨k, h⟩),
      Fin.ext_iff, @eq_comm _ k, h, h.ne']
  ·rw [Finset.sum_eq_zero fun x _ ↦ if_neg (by cases x; omega), add_zero, dif_neg h]

lemma degree_freeMonic [Nontrivial R] : (freeMonic R n).degree = n :=
  Polynomial.degree_eq_of_le_of_coeff_ne_zero ((Polynomial.degree_le_iff_coeff_zero _ _).mpr
    (by simp +contextual [coeff_freeMonic, LT.lt.not_gt, LT.lt.ne']))
    (by simp [coeff_freeMonic])

lemma natDegree_freeMonic [Nontrivial R] : (freeMonic R n).natDegree = n :=
  natDegree_eq_of_degree_eq_some (degree_freeMonic R n)

lemma monic_freeMonic : (freeMonic R n).Monic := by
  nontriviality R
  simp [Polynomial.Monic, ← Polynomial.coeff_natDegree, natDegree_freeMonic, coeff_freeMonic]

omit [Algebra R S] in
lemma map_map_freeMonic (f : R →+* S) :
    (freeMonic R n).map (MvPolynomial.map f) = freeMonic S n := by
  simp [freeMonic, Polynomial.map_sum]

open Polynomial (MonicDegreeEq)

/-- The free monic polynomial of degree `n`, as a `MonicDegreeEq` in `R[X₁,...,Xₙ][X]`. -/
@[simps]
def MonicDegreeEq.freeMonic : MonicDegreeEq (MvPolynomial (Fin n) R) n :=
  ⟨.freeMonic R n, by simp +contextual [coeff_freeMonic, not_lt_of_gt, LT.lt.ne']⟩

end Polynomial

namespace MvPolynomial

open Polynomial

/-- `MonicDegreeEq · n` is representable by `R[X₁,...,Xₙ]`,
with the universal element being `freeMonic`. -/
def mapEquivMonic : (MvPolynomial (Fin n) R →ₐ[R] S) ≃ MonicDegreeEq S n where
  toFun f := .map (.freeMonic _ _) f.toRingHom
  invFun p := aeval (p.1.coeff ·)
  left_inv f := by ext i; simp [coeff_freeMonic]
  right_inv p := by
    suffices ∀ i ≥ n, (if i = n then 1 else 0) = p.1.coeff i by
      ext i; simp +contextual [coeff_freeMonic, apply_dite, this]
    intro i hi
    split_ifs with hi'
    · simp [hi', p.2.1]
    · simp [p.2.2 _ (hi.lt_of_ne' hi')]

variable {R S T} in
lemma coe_mapEquivMonic_comp (f : MvPolynomial (Fin n) R →ₐ[R] S) (g : S →ₐ[R] T) :
    (mapEquivMonic R T n (g.comp f)).1 = (mapEquivMonic R S n f).1.map g :=
  (Polynomial.map_map ..).symm

variable {R S T} in
lemma coe_mapEquivMonic_comp' (f : MvPolynomial (Fin n) R →ₐ[R] S) (g : S →ₐ[R] T) :
    mapEquivMonic R T n (g.comp f) = (mapEquivMonic R S n f).map g :=
  Subtype.ext (coe_mapEquivMonic_comp ..)

variable {R S T} in
lemma mapEquivMonic_symm_map (p : MonicDegreeEq S n) (g : S →ₐ[R] T) :
    (mapEquivMonic R T n).symm (p.map g) = g.comp ((mapEquivMonic R S n).symm p) := by
  obtain ⟨f, rfl⟩ := (mapEquivMonic R S n).surjective p
  exact (mapEquivMonic R T n).symm_apply_eq.mpr (by simp [coe_mapEquivMonic_comp'])

variable {R S T} in
lemma mapEquivMonic_symm_map_algebraMap
    (p : MonicDegreeEq S n) [Algebra S T] [IsScalarTower R S T] :
    (mapEquivMonic R T n).symm (p.map (algebraMap S T)) =
      (IsScalarTower.toAlgHom R S T).comp ((mapEquivMonic R S n).symm p) := by
  rw [← mapEquivMonic_symm_map]; rfl

/-- In light of the fact that `MonicDegreeEq · n` is representable by `R[X₁,...,Xₙ]`,
this is the map `R[X₁,...,Xₘ₊ₖ] → R[X₁,...,Xₘ] ⊗ R[X₁,...,Xₖ]` corresponding to the multiplication
`MonicDegreeEq · m × MonicDegreeEq · k → MonicDegreeEq · (m + k)`. -/
def universalFactorizationMap (hn : n = m + k) :
    MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R :=
  (mapEquivMonic R _ n).symm
  ⟨(mapEquivMonic R _ m Algebra.TensorProduct.includeLeft).1 *
    (mapEquivMonic R _ k Algebra.TensorProduct.includeRight).1, by
    nontriviality R
    nontriviality MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R
    refine (MonicDegreeEq.mk _ ?_ ?_).2
    · exact ((monic_freeMonic R m).map _).mul ((monic_freeMonic R _).map _)
    dsimp [mapEquivMonic]
    rw [((monic_freeMonic R m).map _).natDegree_mul ((monic_freeMonic R k).map _)]
    simp_rw [(monic_freeMonic R _).natDegree_map, natDegree_freeMonic, hn]⟩

lemma universalFactorizationMap_freeMonic :
    (freeMonic R n).map (toRingHom <| universalFactorizationMap R n m k hn) =
      (freeMonic R m).map (algebraMap _ _) *
        (freeMonic R k).map (toRingHom <| Algebra.TensorProduct.includeRight) := by
  change (mapEquivMonic _ _ _ (universalFactorizationMap R n m k hn)).1 = _
  simp [universalFactorizationMap]
  rfl

lemma universalFactorizationMap_comp_map :
    (universalFactorizationMap S n m k hn).toRingHom.comp (map (algebraMap R S)) =
    .comp (Algebra.TensorProduct.lift (S := R)
      (Algebra.TensorProduct.includeLeft.comp (mapAlgHom (Algebra.ofId R S)))
      ((Algebra.TensorProduct.includeRight.restrictScalars R).comp (mapAlgHom (Algebra.ofId R S)))
      fun _ _ ↦ .all _ _).toRingHom
      (universalFactorizationMap R n m k hn).toRingHom := by
  ext
  · simp
  · dsimp [universalFactorizationMap, mapEquivMonic]
    simp only [map_X, aeval_X, ← AlgHom.coe_toRingHom, ← Polynomial.coeff_map, Polynomial.map_mul,
      Polynomial.map_map, ← map_map_freeMonic (f := algebraMap R S)]
    congr <;> ext <;> simp [← algebraMap_apply]

/-- Lifts along `universalFactorizationMap` corresponds to factorization of `p` into
monic polynomials with fixed degrees. -/
def universalFactorizationMapLiftEquiv (p : MonicDegreeEq S n) :
    { f // AlgHom.comp f (universalFactorizationMap R n m k hn) =
        (mapEquivMonic _ _ n).symm p } ≃
    { q : MonicDegreeEq S m × MonicDegreeEq S k // q.1.1 * q.2.1 = p } where
  toFun f := ⟨(mapEquivMonic R _ _ (f.1.comp Algebra.TensorProduct.includeLeft),
    mapEquivMonic R _ _ (f.1.comp Algebra.TensorProduct.includeRight)), by
      conv_rhs => rw [← (Equiv.eq_symm_apply _).mp f.2]
      simp [MvPolynomial.coe_mapEquivMonic_comp, MvPolynomial.universalFactorizationMap]⟩
  invFun q := ⟨Algebra.TensorProduct.lift ((mapEquivMonic _ _ _).symm q.1.1)
    ((mapEquivMonic _ _ _).symm q.1.2) fun _ _ ↦ .all _ _, by
    refine (mapEquivMonic R S n).eq_symm_apply.mpr <| Subtype.ext ?_
    simp only [universalFactorizationMap, coe_mapEquivMonic_comp, Equiv.apply_symm_apply,
      Polynomial.map_mul]
    simp [← coe_mapEquivMonic_comp, ← q.2]⟩
  left_inv f := by ext <;> simp
  right_inv q := by ext <;> simp

end MvPolynomial
