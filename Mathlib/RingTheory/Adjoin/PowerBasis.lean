/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.PowerBasis
import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Power basis for `Algebra.adjoin R {x}`

This file defines the canonical power basis on `Algebra.adjoin R {x}`,
where `x` is an integral element over `R`.
-/

open Module Polynomial PowerBasis

variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]

namespace Algebra

/-- The elements `1, x, ..., x ^ (d - 1)` for a basis for the `K`-module `K[x]`,
where `d` is the degree of the minimal polynomial of `x`. -/
noncomputable def adjoin.powerBasisAux {x : S} (hx : IsIntegral K x) :
    Basis (Fin (minpoly K x).natDegree) K (adjoin K ({x} : Set S)) := by
  have hST : Function.Injective (algebraMap (adjoin K ({x} : Set S)) S) := Subtype.coe_injective
  have hx' :
    IsIntegral K (⟨x, subset_adjoin (Set.mem_singleton x)⟩ : adjoin K ({x} : Set S)) := by
    apply (isIntegral_algebraMap_iff hST).mp
    convert hx
  apply Basis.mk (v := fun i : Fin _ ↦ ⟨x, subset_adjoin (Set.mem_singleton x)⟩ ^ (i : ℕ))
  · have : LinearIndependent K _ := linearIndependent_pow
      (⟨x, self_mem_adjoin_singleton _ _⟩ : adjoin K {x})
    rwa [← minpoly.algebraMap_eq hST] at this
  · rintro ⟨y, hy⟩ _
    have := hx'.mem_span_pow (y := ⟨y, hy⟩)
    rw [← minpoly.algebraMap_eq hST] at this
    apply this
    rw [adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨f, rfl⟩ := (aeval x).mem_range.mp hy
    use f
    ext
    exact aeval_algebraMap_apply S (⟨x, _⟩ : adjoin K {x}) _

/-- The power basis `1, x, ..., x ^ (d - 1)` for `K[x]`,
where `d` is the degree of the minimal polynomial of `x`. See `Algebra.adjoin.powerBasis'` for
a version over a more general base ring. -/
@[simps gen dim]
noncomputable def adjoin.powerBasis {x : S} (hx : IsIntegral K x) :
    PowerBasis K (adjoin K ({x} : Set S)) where
  gen := ⟨x, subset_adjoin (Set.mem_singleton x)⟩
  dim := (minpoly K x).natDegree
  basis := adjoin.powerBasisAux hx
  basis_eq_pow i := by rw [adjoin.powerBasisAux, Basis.mk_apply]

/--
If `x` generates `S` over `K` and is integral over `K`, then it defines a power basis.
See `PowerBasis.ofAdjoinEqTop'` for a version over a more general base ring.
-/
noncomputable def _root_.PowerBasis.ofAdjoinEqTop {x : S} (hx : IsIntegral K x)
    (hx' : adjoin K {x} = ⊤) : PowerBasis K S :=
  (adjoin.powerBasis hx).map ((Subalgebra.equivOfEq _ _ hx').trans Subalgebra.topEquiv)

@[simp]
theorem _root_.PowerBasis.ofAdjoinEqTop_gen {x : S} (hx : IsIntegral K x)
    (hx' : adjoin K {x} = ⊤) : (PowerBasis.ofAdjoinEqTop hx hx').gen = x := rfl

@[simp]
theorem _root_.PowerBasis.ofAdjoinEqTop_dim {x : S} (hx : IsIntegral K x)
    (hx' : adjoin K {x} = ⊤) :
    (PowerBasis.ofAdjoinEqTop hx hx').dim = (minpoly K x).natDegree := rfl

@[deprecated "Use in combination with `PowerBasis.adjoin_eq_top_of_gen_mem_adjoin` to recover the \
  deprecated definition" (since := "2025-09-29")] alias PowerBasis.ofGenMemAdjoin :=
  PowerBasis.ofAdjoinEqTop

end Algebra

open Algebra

section IsIntegral

namespace PowerBasis

open Polynomial

variable {R : Type*} [CommRing R] [Algebra R S] [Algebra R K] [IsScalarTower R K S]
variable {A : Type*} [CommRing A] [Algebra R A] [Algebra S A]
variable [IsScalarTower R S A] {B : PowerBasis S A}

/-- If `B : PowerBasis S A` is such that `IsIntegral R B.gen`, then
`IsIntegral R (B.basis.repr (B.gen ^ n) i)` for all `i` if
`minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)`. This is the case if `R` is a GCD domain
and `S` is its fraction ring. -/
theorem repr_gen_pow_isIntegral (hB : IsIntegral R B.gen)
    (hmin : minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)) (n : ℕ) :
    ∀ i, IsIntegral R (B.basis.repr (B.gen ^ n) i) := by
  intro i
  nontriviality S
  let Q := X ^ n %ₘ minpoly R B.gen
  have : B.gen ^ n = aeval B.gen Q := by
    rw [← @aeval_X_pow R _ _ _ _ B.gen, ← modByMonic_add_div (X ^ n) (minpoly.monic hB)]
    simp [Q]
  by_cases hQ : Q = 0
  · simp [this, hQ, isIntegral_zero]
  have hlt : Q.natDegree < B.dim := by
    rw [← B.natDegree_minpoly, hmin, (minpoly.monic hB).natDegree_map,
      natDegree_lt_natDegree_iff hQ]
    letI : Nontrivial R := Nontrivial.of_polynomial_ne hQ
    exact degree_modByMonic_lt _ (minpoly.monic hB)
  rw [this, aeval_eq_sum_range' hlt]
  simp only [map_sum, Finset.sum_apply']
  refine IsIntegral.sum _ fun j hj => ?_
  replace hj := Finset.mem_range.1 hj
  rw [← Fin.val_mk hj, ← B.basis_eq_pow, Algebra.smul_def, IsScalarTower.algebraMap_apply R S A, ←
    Algebra.smul_def, LinearEquiv.map_smul]
  simp only [algebraMap_smul, Finsupp.coe_smul, Pi.smul_apply, B.basis.repr_self_apply]
  by_cases hij : (⟨j, hj⟩ : Fin _) = i
  · simp only [hij, if_true]
    rw [Algebra.smul_def, mul_one]
    exact isIntegral_algebraMap
  · simp [hij, isIntegral_zero]

/-- Let `B : PowerBasis S A` be such that `IsIntegral R B.gen`, and let `x y : A` be elements with
integral coordinates in the base `B.basis`. Then `IsIntegral R ((B.basis.repr (x * y) i)` for all
`i` if `minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)`. This is the case if `R` is a GCD
domain and `S` is its fraction ring. -/
theorem repr_mul_isIntegral (hB : IsIntegral R B.gen) {x y : A}
    (hx : ∀ i, IsIntegral R (B.basis.repr x i)) (hy : ∀ i, IsIntegral R (B.basis.repr y i))
    (hmin : minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)) :
    ∀ i, IsIntegral R (B.basis.repr (x * y) i) := by
  intro i
  rw [← B.basis.sum_repr x, ← B.basis.sum_repr y, Finset.sum_mul_sum, ← Finset.sum_product',
    map_sum, Finset.sum_apply']
  refine IsIntegral.sum _ fun I _ => ?_
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, LinearEquiv.map_smulₛₗ,
    RingHom.id_apply, Finsupp.coe_smul, Pi.smul_apply, id.smul_eq_mul]
  refine (hy _).mul ((hx _).mul ?_)
  simp only [coe_basis, ← pow_add]
  exact repr_gen_pow_isIntegral hB hmin _ _

/-- Let `B : PowerBasis S A` be such that `IsIntegral R B.gen`, and let `x : A` be an element
with integral coordinates in the base `B.basis`. Then `IsIntegral R ((B.basis.repr (x ^ n) i)` for
all `i` and all `n` if `minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)`. This is the case
if `R` is a GCD domain and `S` is its fraction ring. -/
theorem repr_pow_isIntegral (hB : IsIntegral R B.gen) {x : A}
    (hx : ∀ i, IsIntegral R (B.basis.repr x i))
    (hmin : minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)) (n : ℕ) :
    ∀ i, IsIntegral R (B.basis.repr (x ^ n) i) := by
  nontriviality A using Subsingleton.elim (x ^ n) 0, isIntegral_zero
  revert hx
  refine Nat.case_strong_induction_on
    -- Porting note: had to hint what to induct on
    (p := fun n ↦ _ → ∀ (i : Fin B.dim), IsIntegral R (B.basis.repr (x ^ n) i))
    n ?_ fun n hn => ?_
  · intro _ i
    rw [pow_zero, ← pow_zero B.gen, ← Fin.val_mk B.dim_pos, ← B.basis_eq_pow,
      B.basis.repr_self_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  · intro hx
    rw [pow_succ]
    exact repr_mul_isIntegral hB (fun _ => hn _ le_rfl (fun _ => hx _) _) hx hmin

/-- Let `B B' : PowerBasis K S` be such that `IsIntegral R B.gen`, and let `P : R[X]` be such that
`aeval B.gen P = B'.gen`. Then `IsIntegral R (B.basis.to_matrix B'.basis i j)` for all `i` and `j`
if `minpoly K B.gen = (minpoly R B.gen).map (algebraMap R L)`. This is the case
if `R` is a GCD domain and `K` is its fraction ring. -/
theorem toMatrix_isIntegral {B B' : PowerBasis K S} {P : R[X]} (h : aeval B.gen P = B'.gen)
    (hB : IsIntegral R B.gen) (hmin : minpoly K B.gen = (minpoly R B.gen).map (algebraMap R K)) :
    ∀ i j, IsIntegral R (B.basis.toMatrix B'.basis i j) := by
  intro i j
  rw [B.basis.toMatrix_apply, B'.coe_basis]
  refine repr_pow_isIntegral hB (fun i => ?_) hmin _ _
  rw [← h, aeval_eq_sum_range, map_sum, Finset.sum_apply']
  refine IsIntegral.sum _ fun n _ => ?_
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R K S, ← Algebra.smul_def,
    LinearEquiv.map_smul, algebraMap_smul]
  exact (repr_gen_pow_isIntegral hB hmin _ _).smul _

end PowerBasis

end IsIntegral
