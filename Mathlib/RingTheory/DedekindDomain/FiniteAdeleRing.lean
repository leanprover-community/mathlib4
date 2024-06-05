/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Algebra.Order.GroupWithZero.WithZero

#align_import ring_theory.dedekind_domain.finite_adele_ring from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!
# The finite adèle ring of a Dedekind domain
We define the ring of finite adèles of a Dedekind domain `R`.

## Main definitions
- `DedekindDomain.FiniteIntegralAdeles` : product of `adicCompletionIntegers`, where `v`
  runs over all maximal ideals of `R`.
- `DedekindDomain.ProdAdicCompletions` : the product of `adicCompletion`, where `v` runs over
  all maximal ideals of `R`.
- `DedekindDomain.finiteAdeleRing` : The finite adèle ring of `R`, defined as the
  restricted product `Π'_v K_v`. We give this ring a `K`-algebra structure.

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

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- The product of all `adicCompletionIntegers`, where `v` runs over the maximal ideals of `R`. -/
def FiniteIntegralAdeles : Type _ :=
  ∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K
-- deriving CommRing, TopologicalSpace, Inhabited
#align dedekind_domain.finite_integral_adeles DedekindDomain.FiniteIntegralAdeles

-- Porting note(https://github.com/leanprover-community/mathlib4/issues/5020): added
section DerivedInstances

instance : CommRing (FiniteIntegralAdeles R K) :=
  inferInstanceAs (CommRing (∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K))

instance : TopologicalSpace (FiniteIntegralAdeles R K) :=
  inferInstanceAs (TopologicalSpace (∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K))

instance : TopologicalRing (FiniteIntegralAdeles R K) :=
  inferInstanceAs (TopologicalRing (∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K))

instance : Inhabited (FiniteIntegralAdeles R K) :=
  inferInstanceAs (Inhabited (∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K))

end DerivedInstances

local notation "R_hat" => FiniteIntegralAdeles

/-- The product of all `adicCompletion`, where `v` runs over the maximal ideals of `R`. -/
def ProdAdicCompletions :=
  ∀ v : HeightOneSpectrum R, v.adicCompletion K
-- deriving NonUnitalNonAssocRing, TopologicalSpace, TopologicalRing, CommRing, Inhabited
#align dedekind_domain.prod_adic_completions DedekindDomain.ProdAdicCompletions

section DerivedInstances

instance : NonUnitalNonAssocRing (ProdAdicCompletions R K) :=
  inferInstanceAs (NonUnitalNonAssocRing (∀ v : HeightOneSpectrum R, v.adicCompletion K))

instance : TopologicalSpace (ProdAdicCompletions R K) :=
  inferInstanceAs (TopologicalSpace (∀ v : HeightOneSpectrum R, v.adicCompletion K))

instance : TopologicalRing (ProdAdicCompletions R K) :=
  inferInstanceAs (TopologicalRing (∀ v : HeightOneSpectrum R, v.adicCompletion K))

instance : CommRing (ProdAdicCompletions R K) :=
  inferInstanceAs (CommRing (∀ v : HeightOneSpectrum R, v.adicCompletion K))

instance : Inhabited (ProdAdicCompletions R K) :=
  inferInstanceAs (Inhabited (∀ v : HeightOneSpectrum R, v.adicCompletion K))

end DerivedInstances

local notation "K_hat" => ProdAdicCompletions

namespace FiniteIntegralAdeles

noncomputable instance : Coe (R_hat R K) (K_hat R K) where coe x v := x v

theorem coe_apply (x : R_hat R K) (v : HeightOneSpectrum R) : (x : K_hat R K) v = ↑(x v) :=
  rfl
#align dedekind_domain.finite_integral_adeles.coe_apply DedekindDomain.FiniteIntegralAdeles.coe_apply

/-- The inclusion of `R_hat` in `K_hat` as a homomorphism of additive monoids. -/
@[simps]
def Coe.addMonoidHom : AddMonoidHom (R_hat R K) (K_hat R K) where
  toFun := (↑)
  map_zero' := rfl
  map_add' x y := by
    -- Porting note: was `ext v`
    refine funext fun v => ?_
    simp only [coe_apply, Pi.add_apply, Subring.coe_add]
    -- Porting note: added
    erw [Pi.add_apply, Pi.add_apply, Subring.coe_add]
#align dedekind_domain.finite_integral_adeles.coe.add_monoid_hom DedekindDomain.FiniteIntegralAdeles.Coe.addMonoidHom

/-- The inclusion of `R_hat` in `K_hat` as a ring homomorphism. -/
@[simps]
def Coe.ringHom : RingHom (R_hat R K) (K_hat R K) :=
  { Coe.addMonoidHom R K with
    toFun := (↑)
    map_one' := rfl
    map_mul' := fun x y => by
      -- Porting note: was `ext p`
      refine funext fun p => ?_
      simp only [Pi.mul_apply, Subring.coe_mul]
      -- Porting note: added
      erw [Pi.mul_apply, Pi.mul_apply, Subring.coe_mul] }
#align dedekind_domain.finite_integral_adeles.coe.ring_hom DedekindDomain.FiniteIntegralAdeles.Coe.ringHom

end FiniteIntegralAdeles

section AlgebraInstances

instance : Algebra K (K_hat R K) :=
  (by infer_instance : Algebra K <| ∀ v : HeightOneSpectrum R, v.adicCompletion K)

@[simp]
lemma ProdAdicCompletions.algebraMap_apply' (k : K) :
    algebraMap K (K_hat R K) k v = (k : v.adicCompletion K) := rfl

instance ProdAdicCompletions.algebra' : Algebra R (K_hat R K) :=
  (by infer_instance : Algebra R <| ∀ v : HeightOneSpectrum R, v.adicCompletion K)
#align dedekind_domain.prod_adic_completions.algebra' DedekindDomain.ProdAdicCompletions.algebra'

@[simp]
lemma ProdAdicCompletions.algebraMap_apply (r : R) :
    algebraMap R (K_hat R K) r v = (algebraMap R K r : v.adicCompletion K) := rfl

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
    toFun := (↑)
    commutes' := fun _ => rfl }
#align dedekind_domain.finite_integral_adeles.coe.alg_hom DedekindDomain.FiniteIntegralAdeles.Coe.algHom

theorem Coe.algHom_apply (x : R_hat R K) (v : HeightOneSpectrum R) : (Coe.algHom R K) x v = x v :=
  rfl
#align dedekind_domain.finite_integral_adeles.coe.alg_hom_apply DedekindDomain.FiniteIntegralAdeles.Coe.algHom_apply

end FiniteIntegralAdeles

/-! ### The finite adèle ring of a Dedekind domain
We define the finite adèle ring of `R` as the restricted product over all maximal ideals `v` of `R`
of `adicCompletion` with respect to `adicCompletionIntegers`. We prove that it is a commutative
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
    (x + y).IsFiniteAdele := by
  rw [IsFiniteAdele, Filter.eventually_cofinite] at hx hy ⊢
  have h_subset :
    {v : HeightOneSpectrum R | ¬(x + y) v ∈ v.adicCompletionIntegers K} ⊆
      {v : HeightOneSpectrum R | ¬x v ∈ v.adicCompletionIntegers K} ∪
        {v : HeightOneSpectrum R | ¬y v ∈ v.adicCompletionIntegers K} := by
    intro v hv
    rw [mem_union, mem_setOf, mem_setOf]
    rw [mem_setOf] at hv
    contrapose! hv
    rw [mem_adicCompletionIntegers, mem_adicCompletionIntegers, ← max_le_iff] at hv
    rw [mem_adicCompletionIntegers, Pi.add_apply]
    exact le_trans (Valued.v.map_add_le_max' (x v) (y v)) hv
  exact (hx.union hy).subset h_subset
#align dedekind_domain.prod_adic_completions.is_finite_adele.add DedekindDomain.ProdAdicCompletions.IsFiniteAdele.add

/-- The tuple `(0)_v` is a finite adèle. -/
theorem zero : (0 : K_hat R K).IsFiniteAdele := by
  rw [IsFiniteAdele, Filter.eventually_cofinite]
  have h_empty :
    {v : HeightOneSpectrum R | ¬(0 : v.adicCompletion K) ∈ v.adicCompletionIntegers K} = ∅ := by
    ext v; rw [mem_empty_iff_false, iff_false_iff]; intro hv
    rw [mem_setOf] at hv; apply hv; rw [mem_adicCompletionIntegers]
    have h_zero : (Valued.v (0 : v.adicCompletion K) : WithZero (Multiplicative ℤ)) = 0 :=
      Valued.v.map_zero'
    rw [h_zero]; exact zero_le_one' _
  -- Porting note: was `exact`, but `OfNat` got in the way.
  convert finite_empty
#align dedekind_domain.prod_adic_completions.is_finite_adele.zero DedekindDomain.ProdAdicCompletions.IsFiniteAdele.zero

/-- The negative of a finite adèle is a finite adèle. -/
theorem neg {x : K_hat R K} (hx : x.IsFiniteAdele) : (-x).IsFiniteAdele := by
  rw [IsFiniteAdele] at hx ⊢
  have h :
    ∀ v : HeightOneSpectrum R,
      -x v ∈ v.adicCompletionIntegers K ↔ x v ∈ v.adicCompletionIntegers K := by
    intro v
    rw [mem_adicCompletionIntegers, mem_adicCompletionIntegers, Valuation.map_neg]
  -- Porting note: was `simpa only [Pi.neg_apply, h] using hx` but `Pi.neg_apply` no longer works
  convert hx using 2 with v
  convert h v
#align dedekind_domain.prod_adic_completions.is_finite_adele.neg DedekindDomain.ProdAdicCompletions.IsFiniteAdele.neg

/-- The product of two finite adèles is a finite adèle. -/
theorem mul {x y : K_hat R K} (hx : x.IsFiniteAdele) (hy : y.IsFiniteAdele) :
    (x * y).IsFiniteAdele := by
  rw [IsFiniteAdele, Filter.eventually_cofinite] at hx hy ⊢
  have h_subset :
    {v : HeightOneSpectrum R | ¬(x * y) v ∈ v.adicCompletionIntegers K} ⊆
      {v : HeightOneSpectrum R | ¬x v ∈ v.adicCompletionIntegers K} ∪
        {v : HeightOneSpectrum R | ¬y v ∈ v.adicCompletionIntegers K} := by
    intro v hv
    rw [mem_union, mem_setOf, mem_setOf]
    rw [mem_setOf] at hv
    contrapose! hv
    rw [mem_adicCompletionIntegers, mem_adicCompletionIntegers] at hv
    have h_mul : Valued.v (x v * y v) = Valued.v (x v) * Valued.v (y v) :=
      Valued.v.map_mul' (x v) (y v)
    rw [mem_adicCompletionIntegers, Pi.mul_apply, h_mul]
    exact mul_le_one' hv.left hv.right
  exact (hx.union hy).subset h_subset
#align dedekind_domain.prod_adic_completions.is_finite_adele.mul DedekindDomain.ProdAdicCompletions.IsFiniteAdele.mul

/-- The tuple `(1)_v` is a finite adèle. -/
theorem one : (1 : K_hat R K).IsFiniteAdele := by
  rw [IsFiniteAdele, Filter.eventually_cofinite]
  have h_empty :
    {v : HeightOneSpectrum R | ¬(1 : v.adicCompletion K) ∈ v.adicCompletionIntegers K} = ∅ := by
    ext v; rw [mem_empty_iff_false, iff_false_iff]; intro hv
    rw [mem_setOf] at hv; apply hv; rw [mem_adicCompletionIntegers]
    exact le_of_eq Valued.v.map_one'
  -- Porting note: was `exact`, but `OfNat` got in the way.
  convert finite_empty
#align dedekind_domain.prod_adic_completions.is_finite_adele.one DedekindDomain.ProdAdicCompletions.IsFiniteAdele.one

open scoped DiscreteValuation

theorem algebraMap' (k : K) : (_root_.algebraMap K (K_hat R K) k).IsFiniteAdele := by
  rw [IsFiniteAdele, Filter.eventually_cofinite]
  simp_rw [mem_adicCompletionIntegers, ProdAdicCompletions.algebraMap_apply',
    Valued.valuedCompletion_apply, not_le]
  change {v : HeightOneSpectrum R | 1 < v.valuation k}.Finite
  -- The goal currently: if k ∈ K = field of fractions of a Dedekind domain R,
  -- then v(k)>1 for only finitely many v.
  -- We now write k=n/d and go via R to solve this goal. Do we need to do this?
  obtain ⟨⟨n, ⟨d, hd⟩⟩, hk⟩ := IsLocalization.surj (nonZeroDivisors R) k
  have hd' : d ≠ 0 := nonZeroDivisors.ne_zero hd
  suffices {v : HeightOneSpectrum R | v.valuation (_root_.algebraMap R K d : K) < 1}.Finite by
    apply Finite.subset this
    intro v hv
    apply_fun v.valuation at hk
    simp only [Valuation.map_mul, valuation_of_algebraMap] at hk
    rw [mem_setOf_eq, valuation_of_algebraMap]
    have := int_valuation_le_one v n
    contrapose! this
    change 1 < v.intValuation n
    rw [← hk, mul_comm]
    exact lt_mul_of_le_of_one_lt' this hv (by simp) (by simp)
  simp_rw [valuation_of_algebraMap]
  change {v : HeightOneSpectrum R | v.intValuationDef d < 1}.Finite
  simp_rw [int_valuation_lt_one_iff_dvd]
  apply Ideal.finite_factors
  simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]

end IsFiniteAdele

end ProdAdicCompletions

open ProdAdicCompletions.IsFiniteAdele

/-- The finite adèle ring of `R` is the restricted product over all maximal ideals `v` of `R`
of `adicCompletion` with respect to `adicCompletionIntegers`. -/
def FiniteAdeleRing : Type _ := (
  { carrier := {x : K_hat R K | x.IsFiniteAdele}
    mul_mem' := mul
    one_mem' := one
    add_mem' := add
    zero_mem' := zero
    algebraMap_mem' := algebraMap'
  } : Subalgebra K (K_hat R K))
#align dedekind_domain.finite_adele_ring DedekindDomain.FiniteAdeleRing

namespace FiniteAdeleRing

instance : CommRing (FiniteAdeleRing R K) := Subalgebra.toCommRing _

instance : Algebra K (FiniteAdeleRing R K) := Subalgebra.algebra _

instance : Coe (FiniteAdeleRing R K) (K_hat R K) where
  coe := fun x ↦ x.1

@[ext]
lemma ext {a₁ a₂ : FiniteAdeleRing R K} (h : (a₁ : K_hat R K) = a₂) : a₁ = a₂ :=
  Subtype.ext h

end FiniteAdeleRing

end DedekindDomain
