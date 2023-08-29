/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.PowerBasis
import Mathlib.LinearAlgebra.Matrix.Basis

#align_import ring_theory.adjoin.power_basis from "leanprover-community/mathlib"@"825edd3cd735e87495b0c2a2114fc3929eefce41"

/-!
# Power basis for `Algebra.adjoin R {x}`

This file defines the canonical power basis on `Algebra.adjoin R {x}`,
where `x` is an integral element over `R`.
-/


variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]

namespace Algebra

open BigOperators
open Polynomial
open PowerBasis


-- Porting note:

/-- The elements `1, x, ..., x ^ (d - 1)` for a basis for the `K`-module `K[x]`,
where `d` is the degree of the minimal polynomial of `x`. -/
noncomputable def adjoin.powerBasisAux {x : S} (hx : IsIntegral K x) :
    Basis (Fin (minpoly K x).natDegree) K (adjoin K ({x} : Set S)) := by
  have hST : Function.Injective (algebraMap (adjoin K ({x} : Set S)) S) := Subtype.coe_injective
  -- ⊢ Basis (Fin (natDegree (minpoly K x))) K { x_1 // x_1 ∈ adjoin K {x} }
  have hx' :
    IsIntegral K (⟨x, subset_adjoin (Set.mem_singleton x)⟩ : adjoin K ({x} : Set S)) := by
    apply (isIntegral_algebraMap_iff hST).mp
    convert hx
  have minpoly_eq := minpoly.eq_of_algebraMap_eq hST hx' rfl
  -- ⊢ Basis (Fin (natDegree (minpoly K x))) K { x_1 // x_1 ∈ adjoin K {x} }
  apply
    @Basis.mk (Fin (minpoly K x).natDegree) _ (adjoin K {x}) fun i =>
      ⟨x, subset_adjoin (Set.mem_singleton x)⟩ ^ (i : ℕ)
  · have : LinearIndependent K _ := linearIndependent_pow
      (⟨x, self_mem_adjoin_singleton _ _⟩ : adjoin K {x})
    rwa [minpoly_eq] at this
    -- 🎉 no goals
  · rintro ⟨y, hy⟩ _
    -- ⊢ { val := y, property := hy } ∈ Submodule.span K (Set.range fun i => { val := …
    have := hx'.mem_span_pow (y := ⟨y, hy⟩)
    -- ⊢ { val := y, property := hy } ∈ Submodule.span K (Set.range fun i => { val := …
    rw [minpoly_eq] at this
    -- ⊢ { val := y, property := hy } ∈ Submodule.span K (Set.range fun i => { val := …
    apply this
    -- ⊢ ∃ f, { val := y, property := hy } = ↑(aeval { val := x, property := (_ : x ∈ …
    · rw [adjoin_singleton_eq_range_aeval] at hy
      -- ⊢ ∃ f, { val := y, property := hy✝ } = ↑(aeval { val := x, property := (_ : x  …
      obtain ⟨f, rfl⟩ := (aeval x).mem_range.mp hy
      -- ⊢ ∃ f_1, { val := ↑(aeval x) f, property := hy✝ } = ↑(aeval { val := x, proper …
      use f
      -- ⊢ { val := ↑(aeval x) f, property := hy✝ } = ↑(aeval { val := x, property := ( …
      ext
      -- ⊢ ↑{ val := ↑(aeval x) f, property := hy✝ } = ↑(↑(aeval { val := x, property : …
      exact aeval_algebraMap_apply S (⟨x, _⟩ : adjoin K {x}) _
      -- 🎉 no goals
#align algebra.adjoin.power_basis_aux Algebra.adjoin.powerBasisAux

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
                       -- 🎉 no goals
#align algebra.adjoin.power_basis Algebra.adjoin.powerBasis

end Algebra

open Algebra

/-- The power basis given by `x` if `B.gen ∈ adjoin K {x}`. See `PowerBasis.ofGenMemAdjoin'`
for a version over a more general base ring. -/
@[simps!]
noncomputable def PowerBasis.ofGenMemAdjoin {x : S} (B : PowerBasis K S) (hint : IsIntegral K x)
    (hx : B.gen ∈ adjoin K ({x} : Set S)) : PowerBasis K S :=
  (Algebra.adjoin.powerBasis hint).map <|
    (Subalgebra.equivOfEq _ _ <| PowerBasis.adjoin_eq_top_of_gen_mem_adjoin hx).trans
      Subalgebra.topEquiv
#align power_basis.of_gen_mem_adjoin PowerBasis.ofGenMemAdjoin

section IsIntegral

namespace PowerBasis

open Polynomial

open Polynomial

variable {R : Type*} [CommRing R] [Algebra R S] [Algebra R K] [IsScalarTower R K S]

variable {A : Type*} [CommRing A] [Algebra R A] [Algebra S A]

variable [IsScalarTower R S A] {B : PowerBasis S A} (hB : IsIntegral R B.gen)

/-- If `B : PowerBasis S A` is such that `IsIntegral R B.gen`, then
`IsIntegral R (B.basis.repr (B.gen ^ n) i)` for all `i` if
`minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)`. This is the case if `R` is a GCD domain
and `S` is its fraction ring. -/
theorem repr_gen_pow_isIntegral [IsDomain S]
    (hmin : minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)) (n : ℕ) :
    ∀ i, IsIntegral R (B.basis.repr (B.gen ^ n) i) := by
  intro i
  -- ⊢ IsIntegral R (↑(↑B.basis.repr (B.gen ^ n)) i)
  let Q := X ^ n %ₘ minpoly R B.gen
  -- ⊢ IsIntegral R (↑(↑B.basis.repr (B.gen ^ n)) i)
  have : B.gen ^ n = aeval B.gen Q := by
    rw [← @aeval_X_pow R _ _ _ _ B.gen, ← modByMonic_add_div (X ^ n) (minpoly.monic hB)]
    simp
  by_cases hQ : Q = 0
  -- ⊢ IsIntegral R (↑(↑B.basis.repr (B.gen ^ n)) i)
  · simp [this, hQ, isIntegral_zero]
    -- 🎉 no goals
  have hlt : Q.natDegree < B.dim := by
    rw [← B.natDegree_minpoly, hmin, (minpoly.monic hB).natDegree_map,
      natDegree_lt_natDegree_iff hQ]
    letI : Nontrivial R := Nontrivial.of_polynomial_ne hQ
    exact degree_modByMonic_lt _ (minpoly.monic hB)
  rw [this, aeval_eq_sum_range' hlt]
  -- ⊢ IsIntegral R (↑(↑B.basis.repr (Finset.sum (Finset.range B.dim) fun i => coef …
  simp only [LinearEquiv.map_sum, LinearEquiv.map_smulₛₗ, RingHom.id_apply, Finset.sum_apply']
  -- ⊢ IsIntegral R (Finset.sum (Finset.range B.dim) fun x => ↑(↑B.basis.repr (coef …
  refine' IsIntegral.sum _ fun j hj => _
  -- ⊢ IsIntegral R (↑(↑B.basis.repr (coeff (X ^ n %ₘ minpoly R B.gen) j • B.gen ^  …
  replace hj := Finset.mem_range.1 hj
  -- ⊢ IsIntegral R (↑(↑B.basis.repr (coeff (X ^ n %ₘ minpoly R B.gen) j • B.gen ^  …
  rw [← Fin.val_mk hj, ← B.basis_eq_pow, Algebra.smul_def, IsScalarTower.algebraMap_apply R S A, ←
    Algebra.smul_def, LinearEquiv.map_smul]
  simp only [algebraMap_smul, Finsupp.coe_smul, Pi.smul_apply, B.basis.repr_self_apply]
  -- ⊢ IsIntegral R (coeff (X ^ n %ₘ minpoly R B.gen) j • if { val := j, isLt := hj …
  by_cases hij : (⟨j, hj⟩ : Fin _) = i
  -- ⊢ IsIntegral R (coeff (X ^ n %ₘ minpoly R B.gen) j • if { val := j, isLt := hj …
  · simp only [hij, eq_self_iff_true, if_true]
    -- ⊢ IsIntegral R (coeff (X ^ n %ₘ minpoly R B.gen) j • 1)
    rw [Algebra.smul_def, mul_one]
    -- ⊢ IsIntegral R (↑(algebraMap R S) (coeff (X ^ n %ₘ minpoly R B.gen) j))
    exact isIntegral_algebraMap
    -- 🎉 no goals
  · simp [hij, isIntegral_zero]
    -- 🎉 no goals
#align power_basis.repr_gen_pow_is_integral PowerBasis.repr_gen_pow_isIntegral

/-- Let `B : PowerBasis S A` be such that `IsIntegral R B.gen`, and let `x y : A` be elements with
integral coordinates in the base `B.basis`. Then `IsIntegral R ((B.basis.repr (x * y) i)` for all
`i` if `minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)`. This is the case if `R` is a GCD
domain and `S` is its fraction ring. -/
theorem repr_mul_isIntegral [IsDomain S] {x y : A} (hx : ∀ i, IsIntegral R (B.basis.repr x i))
    (hy : ∀ i, IsIntegral R (B.basis.repr y i))
    (hmin : minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)) :
    ∀ i, IsIntegral R (B.basis.repr (x * y) i) := by
  intro i
  -- ⊢ IsIntegral R (↑(↑B.basis.repr (x * y)) i)
  rw [← B.basis.sum_repr x, ← B.basis.sum_repr y, Finset.sum_mul_sum, LinearEquiv.map_sum,
    Finset.sum_apply']
  refine' IsIntegral.sum _ fun I _ => _
  -- ⊢ IsIntegral R (↑(↑B.basis.repr (↑(↑B.basis.repr x) I.fst • ↑B.basis I.fst * ↑ …
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, LinearEquiv.map_smulₛₗ,
    RingHom.id_apply, Finsupp.coe_smul, Pi.smul_apply, id.smul_eq_mul]
  refine' isIntegral_mul (hy _) (isIntegral_mul (hx _) _)
  -- ⊢ IsIntegral R (↑(↑B.basis.repr (↑B.basis I.fst * ↑B.basis I.snd)) i)
  simp only [coe_basis, ← pow_add]
  -- ⊢ IsIntegral R (↑(↑B.basis.repr (B.gen ^ (↑I.fst + ↑I.snd))) i)
  refine' repr_gen_pow_isIntegral hB hmin _ _
  -- 🎉 no goals
#align power_basis.repr_mul_is_integral PowerBasis.repr_mul_isIntegral

/-- Let `B : PowerBasis S A` be such that `IsIntegral R B.gen`, and let `x : A` be an element
with integral coordinates in the base `B.basis`. Then `IsIntegral R ((B.basis.repr (x ^ n) i)` for
all `i` and all `n` if `minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)`. This is the case
if `R` is a GCD domain and `S` is its fraction ring. -/
theorem repr_pow_isIntegral [IsDomain S] {x : A} (hx : ∀ i, IsIntegral R (B.basis.repr x i))
    (hmin : minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)) (n : ℕ) :
    ∀ i, IsIntegral R (B.basis.repr (x ^ n) i) := by
  nontriviality A using Subsingleton.elim (x ^ n) 0, isIntegral_zero
  -- ⊢ ∀ (i : Fin B.dim), IsIntegral R (↑(↑B.basis.repr (x ^ n)) i)
  revert hx
  -- ⊢ (∀ (i : Fin B.dim), IsIntegral R (↑(↑B.basis.repr x) i)) → ∀ (i : Fin B.dim) …
  refine' Nat.case_strong_induction_on
    -- Porting note: had to hint what to induct on
    (p := fun n ↦ _ → ∀ (i : Fin B.dim), IsIntegral R (B.basis.repr (x ^ n) i))
    n _ fun n hn => _
  · intro _ i
    -- ⊢ IsIntegral R (↑(↑B.basis.repr (x ^ 0)) i)
    rw [pow_zero, ← pow_zero B.gen, ← Fin.val_mk B.dim_pos, ← B.basis_eq_pow,
      B.basis.repr_self_apply]
    split_ifs
    -- ⊢ IsIntegral R 1
    · exact isIntegral_one
      -- 🎉 no goals
    · exact isIntegral_zero
      -- 🎉 no goals
  · intro hx
    -- ⊢ ∀ (i : Fin B.dim), IsIntegral R (↑(↑B.basis.repr (x ^ Nat.succ n)) i)
    rw [pow_succ]
    -- ⊢ ∀ (i : Fin B.dim), IsIntegral R (↑(↑B.basis.repr (x * x ^ n)) i)
    exact repr_mul_isIntegral hB hx (fun _ => hn _ le_rfl (fun _ => hx _) _) hmin
    -- 🎉 no goals
#align power_basis.repr_pow_is_integral PowerBasis.repr_pow_isIntegral

/-- Let `B B' : PowerBasis K S` be such that `IsIntegral R B.gen`, and let `P : R[X]` be such that
`aeval B.gen P = B'.gen`. Then `IsIntegral R (B.basis.to_matrix B'.basis i j)` for all `i` and `j`
if `minpoly K B.gen = (minpoly R B.gen).map (algebraMap R L)`. This is the case
if `R` is a GCD domain and `K` is its fraction ring. -/
theorem toMatrix_isIntegral {B B' : PowerBasis K S} {P : R[X]} (h : aeval B.gen P = B'.gen)
    (hB : IsIntegral R B.gen) (hmin : minpoly K B.gen = (minpoly R B.gen).map (algebraMap R K)) :
    ∀ i j, IsIntegral R (B.basis.toMatrix B'.basis i j) := by
  intro i j
  -- ⊢ IsIntegral R (Basis.toMatrix B.basis (↑B'.basis) i j)
  rw [B.basis.toMatrix_apply, B'.coe_basis]
  -- ⊢ IsIntegral R (↑(↑B.basis.repr ((fun i => B'.gen ^ ↑i) j)) i)
  refine' repr_pow_isIntegral hB (fun i => _) hmin _ _
  -- ⊢ IsIntegral R (↑(↑B.basis.repr B'.gen) i)
  rw [← h, aeval_eq_sum_range, LinearEquiv.map_sum, Finset.sum_apply']
  -- ⊢ IsIntegral R (Finset.sum (Finset.range (natDegree P + 1)) fun k => ↑(↑B.basi …
  refine' IsIntegral.sum _ fun n _ => _
  -- ⊢ IsIntegral R (↑(↑B.basis.repr (coeff P n • B.gen ^ n)) i)
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R K S, ← Algebra.smul_def,
    LinearEquiv.map_smul, algebraMap_smul]
  exact isIntegral_smul _ (repr_gen_pow_isIntegral hB hmin _ _)
  -- 🎉 no goals
#align power_basis.to_matrix_is_integral PowerBasis.toMatrix_isIntegral

end PowerBasis

end IsIntegral
