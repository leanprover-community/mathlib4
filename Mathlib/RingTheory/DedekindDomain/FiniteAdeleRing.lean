/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández

! This file was ported from Lean 3 source module ring_theory.dedekind_domain.finite_adele_ring
! leanprover-community/mathlib commit f0c8bf9245297a541f468be517f1bde6195105e9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.DedekindDomain.AdicValuation

/-!
# The finite adèle ring of a Dedekind domain
We define the ring of finite adèles of a Dedekind domain `R`.

## Main definitions
- `dedekind_domain.finite_integral_adeles` : product of `adic_completion_integers`, where `v`
  runs over all maximal ideals of `R`.
- `dedekind_domain.prod_adic_completions` : the product of `adic_completion`, where `v` runs over
  all maximal ideals of `R`.
- `dedekind_domain.finite_adele_ring` : The finite adèle ring of `R`, defined as the
  restricted product `Π'_v K_v`.

## Implementation notes
We are only interested on Dedekind domains of Krull dimension 1 (i.e., not fields). If `R` is a
field, its finite adèle ring is just defined to be the trivial ring.

## References
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
finite adèle ring, dedekind domain
-/


noncomputable section

open Function Set IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace DedekindDomain

variable (R K : Type _) [CommRing R] [IsDomain R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- The product of all `adic_completion_integers`, where `v` runs over the maximal ideals of `R`. -/
def FiniteIntegralAdeles : Type _ :=
  ∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K
deriving CommRing, TopologicalSpace, Inhabited
#align dedekind_domain.finite_integral_adeles DedekindDomain.FiniteIntegralAdeles

local notation "R_hat" => FiniteIntegralAdeles

/-- The product of all `adic_completion`, where `v` runs over the maximal ideals of `R`. -/
def ProdAdicCompletions :=
  ∀ v : HeightOneSpectrum R, v.adicCompletion K
deriving NonUnitalNonAssocRing, TopologicalSpace, TopologicalRing, CommRing, Inhabited
#align dedekind_domain.prod_adic_completions DedekindDomain.ProdAdicCompletions

local notation "K_hat" => ProdAdicCompletions

namespace FiniteIntegralAdeles

noncomputable instance : Coe (R_hat R K) (K_hat R K) where coe x v := x v

theorem coe_apply (x : R_hat R K) (v : HeightOneSpectrum R) : (x : K_hat R K) v = ↑(x v) :=
  rfl
#align dedekind_domain.finite_integral_adeles.coe_apply DedekindDomain.FiniteIntegralAdeles.coe_apply

/-- The inclusion of `R_hat` in `K_hat` as a homomorphism of additive monoids. -/
@[simps]
def Coe.addMonoidHom : AddMonoidHom (R_hat R K) (K_hat R K)
    where
  toFun := coe
  map_zero' := rfl
  map_add' x y := by ext v; simp only [coe_apply, Pi.add_apply, Subring.coe_add]
#align dedekind_domain.finite_integral_adeles.coe.add_monoid_hom DedekindDomain.FiniteIntegralAdeles.Coe.addMonoidHom

/-- The inclusion of `R_hat` in `K_hat` as a ring homomorphism. -/
@[simps]
def Coe.ringHom : RingHom (R_hat R K) (K_hat R K) :=
  { Coe.addMonoidHom R K with
    toFun := coe
    map_one' := rfl
    map_mul' := fun x y => by ext p; simp only [Pi.mul_apply, Subring.coe_mul]; rfl }
#align dedekind_domain.finite_integral_adeles.coe.ring_hom DedekindDomain.FiniteIntegralAdeles.Coe.ringHom

end FiniteIntegralAdeles

section AlgebraInstances

instance : Algebra K (K_hat R K) :=
  (by infer_instance : Algebra K <| ∀ v : HeightOneSpectrum R, v.adicCompletion K)

instance ProdAdicCompletions.algebra' : Algebra R (K_hat R K) :=
  (by infer_instance : Algebra R <| ∀ v : HeightOneSpectrum R, v.adicCompletion K)
#align dedekind_domain.prod_adic_completions.algebra' DedekindDomain.ProdAdicCompletions.algebra'

instance : IsScalarTower R K (K_hat R K) :=
  (by infer_instance : IsScalarTower R K <| ∀ v : HeightOneSpectrum R, v.adicCompletion K)

instance : Algebra R (R_hat R K) :=
  (by infer_instance : Algebra R <| ∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K)

instance ProdAdicCompletions.algebraCompletions : Algebra (R_hat R K) (K_hat R K) :=
  (FiniteIntegralAdeles.Coe.ringHom R K).toAlgebra
#align dedekind_domain.prod_adic_completions.algebra_completions DedekindDomain.ProdAdicCompletions.algebraCompletions

instance ProdAdicCompletions.isScalarTower_completions : IsScalarTower R (R_hat R K) (K_hat R K) :=
  (by infer_instance :
    IsScalarTower R (∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K) <|
      ∀ v : HeightOneSpectrum R, v.adicCompletion K)
#align dedekind_domain.prod_adic_completions.is_scalar_tower_completions DedekindDomain.ProdAdicCompletions.isScalarTower_completions

end AlgebraInstances

namespace FiniteIntegralAdeles

/-- The inclusion of `R_hat` in `K_hat` as an algebra homomorphism. -/
def Coe.algHom : AlgHom R (R_hat R K) (K_hat R K) :=
  { Coe.ringHom R K with
    toFun := coe
    commutes' := fun r => rfl }
#align dedekind_domain.finite_integral_adeles.coe.alg_hom DedekindDomain.FiniteIntegralAdeles.Coe.algHom

theorem Coe.algHom_apply (x : R_hat R K) (v : HeightOneSpectrum R) : (Coe.algHom R K) x v = x v :=
  rfl
#align dedekind_domain.finite_integral_adeles.coe.alg_hom_apply DedekindDomain.FiniteIntegralAdeles.Coe.algHom_apply

end FiniteIntegralAdeles

/-! ### The finite adèle ring of a Dedekind domain
We define the finite adèle ring of `R` as the restricted product over all maximal ideals `v` of `R`
of `adic_completion` with respect to `adic_completion_integers`. We prove that it is a commutative
ring. TODO: show that it is a topological ring with the restricted product topology. -/


namespace ProdAdicCompletions

variable {R K}

/-- An element `x : K_hat R K` is a finite adèle if for all but finitely many height one ideals
  `v`, the component `x v` is a `v`-adic integer. -/
def IsFiniteAdele (x : K_hat R K) :=
  ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, x v ∈ v.adicCompletionIntegers K
#align dedekind_domain.prod_adic_completions.is_finite_adele DedekindDomain.ProdAdicCompletions.IsFiniteAdele

namespace IsFiniteAdele

/-- The sum of two finite adèles is a finite adèle. -/
theorem add {x y : K_hat R K} (hx : x.IsFiniteAdele) (hy : y.IsFiniteAdele) :
    (x + y).IsFiniteAdele :=
  by
  rw [is_finite_adele, Filter.eventually_cofinite] at hx hy ⊢
  have h_subset :
    {v : height_one_spectrum R | ¬(x + y) v ∈ v.adicCompletionIntegers K} ⊆
      {v : height_one_spectrum R | ¬x v ∈ v.adicCompletionIntegers K} ∪
        {v : height_one_spectrum R | ¬y v ∈ v.adicCompletionIntegers K} :=
    by
    intro v hv
    rw [mem_union, mem_set_of_eq, mem_set_of_eq]
    rw [mem_set_of_eq] at hv 
    contrapose! hv
    rw [mem_adic_completion_integers, mem_adic_completion_integers, ← max_le_iff] at hv 
    rw [mem_adic_completion_integers, Pi.add_apply]
    exact le_trans (valued.v.map_add_le_max' (x v) (y v)) hv
  exact (hx.union hy).Subset h_subset
#align dedekind_domain.prod_adic_completions.is_finite_adele.add DedekindDomain.ProdAdicCompletions.IsFiniteAdele.add

/-- The tuple `(0)_v` is a finite adèle. -/
theorem zero : (0 : K_hat R K).IsFiniteAdele :=
  by
  rw [is_finite_adele, Filter.eventually_cofinite]
  have h_empty :
    {v : height_one_spectrum R | ¬(0 : v.adicCompletion K) ∈ v.adicCompletionIntegers K} = ∅ :=
    by
    ext v; rw [mem_empty_iff_false, iff_false_iff]; intro hv
    rw [mem_set_of_eq] at hv ; apply hv; rw [mem_adic_completion_integers]
    have h_zero : (Valued.v (0 : v.adic_completion K) : WithZero (Multiplicative ℤ)) = 0 :=
      valued.v.map_zero'
    rw [h_zero]; exact zero_le_one' _
  simp_rw [Pi.zero_apply, h_empty]
  exact finite_empty
#align dedekind_domain.prod_adic_completions.is_finite_adele.zero DedekindDomain.ProdAdicCompletions.IsFiniteAdele.zero

/-- The negative of a finite adèle is a finite adèle. -/
theorem neg {x : K_hat R K} (hx : x.IsFiniteAdele) : (-x).IsFiniteAdele :=
  by
  rw [is_finite_adele] at hx ⊢
  have h :
    ∀ v : height_one_spectrum R,
      -x v ∈ v.adicCompletionIntegers K ↔ x v ∈ v.adicCompletionIntegers K :=
    by
    intro v
    rw [mem_adic_completion_integers, mem_adic_completion_integers, Valuation.map_neg]
  simpa only [Pi.neg_apply, h] using hx
#align dedekind_domain.prod_adic_completions.is_finite_adele.neg DedekindDomain.ProdAdicCompletions.IsFiniteAdele.neg

/-- The product of two finite adèles is a finite adèle. -/
theorem mul {x y : K_hat R K} (hx : x.IsFiniteAdele) (hy : y.IsFiniteAdele) :
    (x * y).IsFiniteAdele :=
  by
  rw [is_finite_adele, Filter.eventually_cofinite] at hx hy ⊢
  have h_subset :
    {v : height_one_spectrum R | ¬(x * y) v ∈ v.adicCompletionIntegers K} ⊆
      {v : height_one_spectrum R | ¬x v ∈ v.adicCompletionIntegers K} ∪
        {v : height_one_spectrum R | ¬y v ∈ v.adicCompletionIntegers K} :=
    by
    intro v hv
    rw [mem_union, mem_set_of_eq, mem_set_of_eq]
    rw [mem_set_of_eq] at hv 
    contrapose! hv
    rw [mem_adic_completion_integers, mem_adic_completion_integers] at hv 
    have h_mul : Valued.v (x v * y v) = Valued.v (x v) * Valued.v (y v) :=
      Valued.v.map_mul' (x v) (y v)
    rw [mem_adic_completion_integers, Pi.mul_apply, h_mul]
    exact
      @mul_le_one' (WithZero (Multiplicative ℤ)) _ _ (OrderedCommMonoid.to_covariantClass_left _) _
        _ hv.left hv.right
  exact (hx.union hy).Subset h_subset
#align dedekind_domain.prod_adic_completions.is_finite_adele.mul DedekindDomain.ProdAdicCompletions.IsFiniteAdele.mul

/-- The tuple `(1)_v` is a finite adèle. -/
theorem one : (1 : K_hat R K).IsFiniteAdele :=
  by
  rw [is_finite_adele, Filter.eventually_cofinite]
  have h_empty :
    {v : height_one_spectrum R | ¬(1 : v.adicCompletion K) ∈ v.adicCompletionIntegers K} = ∅ :=
    by
    ext v; rw [mem_empty_iff_false, iff_false_iff]; intro hv
    rw [mem_set_of_eq] at hv ; apply hv; rw [mem_adic_completion_integers]
    exact le_of_eq valued.v.map_one'
  simp_rw [Pi.one_apply, h_empty]
  exact finite_empty
#align dedekind_domain.prod_adic_completions.is_finite_adele.one DedekindDomain.ProdAdicCompletions.IsFiniteAdele.one

end IsFiniteAdele

end ProdAdicCompletions

open ProdAdicCompletions.IsFiniteAdele

variable (R K)

/-- The finite adèle ring of `R` is the restricted product over all maximal ideals `v` of `R`
of `adic_completion` with respect to `adic_completion_integers`. -/
noncomputable def finiteAdeleRing : Subring (K_hat R K)
    where
  carrier := {x : K_hat R K | x.IsFiniteAdele}
  mul_mem' _ _ hx hy := mul hx hy
  one_mem' := one
  add_mem' _ _ hx hy := add hx hy
  zero_mem' := zero
  neg_mem' _ hx := neg hx
#align dedekind_domain.finite_adele_ring DedekindDomain.finiteAdeleRing

variable {R K}

@[simp]
theorem mem_finiteAdeleRing_iff (x : K_hat R K) : x ∈ finiteAdeleRing R K ↔ x.IsFiniteAdele :=
  Iff.rfl
#align dedekind_domain.mem_finite_adele_ring_iff DedekindDomain.mem_finiteAdeleRing_iff

end DedekindDomain

