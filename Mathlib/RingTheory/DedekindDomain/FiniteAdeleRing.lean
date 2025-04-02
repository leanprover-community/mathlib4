/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Algebra.Order.GroupWithZero.WithZero

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
-- The `CommRing, TopologicalSpace, Inhabited` instances should be constructed by a deriving
-- handler.
-- https://github.com/leanprover-community/mathlib4/issues/380

section DerivedInstances

instance : CommRing (FiniteIntegralAdeles R K) :=
  inferInstanceAs (CommRing (∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K))

instance : TopologicalSpace (FiniteIntegralAdeles R K) :=
  inferInstanceAs (TopologicalSpace (∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K))

instance (v : HeightOneSpectrum R) : IsTopologicalRing (v.adicCompletionIntegers K) :=
  Subring.instIsTopologicalRing ..

instance : IsTopologicalRing (FiniteIntegralAdeles R K) :=
  inferInstanceAs (IsTopologicalRing (∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K))

instance : Inhabited (FiniteIntegralAdeles R K) :=
  inferInstanceAs (Inhabited (∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K))

end DerivedInstances

local notation "R_hat" => FiniteIntegralAdeles

/-- The product of all `adicCompletion`, where `v` runs over the maximal ideals of `R`. -/
def ProdAdicCompletions :=
  ∀ v : HeightOneSpectrum R, v.adicCompletion K
-- deriving NonUnitalNonAssocRing, TopologicalSpace, IsTopologicalRing, CommRing, Inhabited

section DerivedInstances

instance : NonUnitalNonAssocRing (ProdAdicCompletions R K) :=
  inferInstanceAs (NonUnitalNonAssocRing (∀ v : HeightOneSpectrum R, v.adicCompletion K))

instance : TopologicalSpace (ProdAdicCompletions R K) :=
  inferInstanceAs (TopologicalSpace (∀ v : HeightOneSpectrum R, v.adicCompletion K))

instance : IsTopologicalRing (ProdAdicCompletions R K) :=
  inferInstanceAs (IsTopologicalRing (∀ v : HeightOneSpectrum R, v.adicCompletion K))

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

/-- The inclusion of `R_hat` in `K_hat` as a homomorphism of additive monoids. -/
@[simps]
def Coe.addMonoidHom : AddMonoidHom (R_hat R K) (K_hat R K) where
  toFun := (↑)
  map_zero' := rfl
  map_add' x y := by
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): was `ext v`
    refine funext fun v => ?_
    simp only [coe_apply, (Pi.add_apply), (Subring.coe_add)]

/-- The inclusion of `R_hat` in `K_hat` as a ring homomorphism. -/
@[simps]
def Coe.ringHom : RingHom (R_hat R K) (K_hat R K) :=
  { Coe.addMonoidHom R K with
    toFun := (↑)
    map_one' := rfl
    map_mul' := fun x y => by
      -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): was `ext p`
      refine funext fun p => ?_
      simp only [(Pi.mul_apply), (Subring.coe_mul)] }

end FiniteIntegralAdeles

section AlgebraInstances

instance : Algebra K (K_hat R K) :=
  (by infer_instance : Algebra K <| ∀ v : HeightOneSpectrum R, v.adicCompletion K)

@[simp]
lemma ProdAdicCompletions.algebraMap_apply' (k : K) :
    algebraMap K (K_hat R K) k v = (k : v.adicCompletion K) := rfl

instance ProdAdicCompletions.algebra' : Algebra R (K_hat R K) :=
  (by infer_instance : Algebra R <| ∀ v : HeightOneSpectrum R, v.adicCompletion K)

@[simp]
lemma ProdAdicCompletions.algebraMap_apply (r : R) :
    algebraMap R (K_hat R K) r v = (algebraMap R K r : v.adicCompletion K) := rfl

instance : IsScalarTower R K (K_hat R K) :=
  (by infer_instance : IsScalarTower R K <| ∀ v : HeightOneSpectrum R, v.adicCompletion K)

instance : Algebra R (R_hat R K) :=
  (by infer_instance : Algebra R <| ∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K)

instance ProdAdicCompletions.algebraCompletions : Algebra (R_hat R K) (K_hat R K) :=
  (FiniteIntegralAdeles.Coe.ringHom R K).toAlgebra

instance ProdAdicCompletions.isScalarTower_completions : IsScalarTower R (R_hat R K) (K_hat R K) :=
  (by infer_instance :
    IsScalarTower R (∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K) <|
      ∀ v : HeightOneSpectrum R, v.adicCompletion K)

end AlgebraInstances

namespace FiniteIntegralAdeles

/-- The inclusion of `R_hat` in `K_hat` as an algebra homomorphism. -/
def Coe.algHom : AlgHom R (R_hat R K) (K_hat R K) :=
  { Coe.ringHom R K with
    toFun := (↑)
    commutes' := fun _ => rfl }

theorem Coe.algHom_apply (x : R_hat R K) (v : HeightOneSpectrum R) : (Coe.algHom R K) x v = x v :=
  rfl

instance : FaithfulSMul (R_hat R K) (K_hat R K) where
  eq_of_smul_eq_smul h :=
    funext fun v => SetLike.coe_eq_coe.1 (funext_iff.1 (by simpa [Algebra.smul_def] using h 1) v)

end FiniteIntegralAdeles

/-! ### The finite adèle ring of a Dedekind domain
We define the finite adèle ring of `R` as the restricted product over all maximal ideals `v` of `R`
of `adicCompletion` with respect to `adicCompletionIntegers`. We prove that it is a commutative
ring. -/


namespace ProdAdicCompletions

variable {R K}

/-- An element `x : K_hat R K` is a finite adèle if for all but finitely many height one ideals
  `v`, the component `x v` is a `v`-adic integer. -/
def IsFiniteAdele (x : K_hat R K) :=
  ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, x v ∈ v.adicCompletionIntegers K

@[simp]
lemma isFiniteAdele_iff (x : K_hat R K) :
    x.IsFiniteAdele ↔ {v | x v ∉ adicCompletionIntegers K v}.Finite := Iff.rfl

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

/-- The tuple `(0)_v` is a finite adèle. -/
theorem zero : (0 : K_hat R K).IsFiniteAdele := by
  rw [IsFiniteAdele, Filter.eventually_cofinite]
  have h_empty :
    {v : HeightOneSpectrum R | ¬(0 : v.adicCompletion K) ∈ v.adicCompletionIntegers K} = ∅ := by
    ext v; rw [mem_empty_iff_false, iff_false]; intro hv
    rw [mem_setOf] at hv; apply hv; rw [mem_adicCompletionIntegers]
    have h_zero : (Valued.v (0 : v.adicCompletion K) : WithZero (Multiplicative ℤ)) = 0 :=
      Valued.v.map_zero'
    rw [h_zero]; exact zero_le_one' _
  -- Porting note: was `exact`, but `OfNat` got in the way.
  convert finite_empty

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

/-- The tuple `(1)_v` is a finite adèle. -/
theorem one : (1 : K_hat R K).IsFiniteAdele := by
  rw [IsFiniteAdele, Filter.eventually_cofinite]
  have h_empty :
    {v : HeightOneSpectrum R | ¬(1 : v.adicCompletion K) ∈ v.adicCompletionIntegers K} = ∅ := by
    ext v; rw [mem_empty_iff_false, iff_false]; intro hv
    rw [mem_setOf] at hv; apply hv; rw [mem_adicCompletionIntegers]
    exact le_of_eq Valued.v.map_one'
  -- Porting note: was `exact`, but `OfNat` got in the way.
  convert finite_empty

open scoped Multiplicative

open scoped algebraMap in
theorem algebraMap' (k : K) : (algebraMap K (K_hat R K) k).IsFiniteAdele := by
  rw [IsFiniteAdele, Filter.eventually_cofinite]
  simp_rw [mem_adicCompletionIntegers, ProdAdicCompletions.algebraMap_apply',
    adicCompletion, Valuation.valuedCompletion_apply', not_le]
  change {v : HeightOneSpectrum R | 1 < v.valuation K k}.Finite
  -- The goal currently: if k ∈ K = field of fractions of a Dedekind domain R,
  -- then v(k)>1 for only finitely many v.
  -- We now write k=n/d and go via R to solve this goal. Do we need to do this?
  obtain ⟨⟨n, ⟨d, hd⟩⟩, hk⟩ := IsLocalization.surj (nonZeroDivisors R) k
  have hd' : d ≠ 0 := nonZeroDivisors.ne_zero hd
  suffices {v : HeightOneSpectrum R | v.valuation K d < 1}.Finite by
    apply Finite.subset this
    intro v hv
    apply_fun v.valuation K at hk
    simp only [Valuation.map_mul, valuation_of_algebraMap] at hk
    rw [mem_setOf_eq, valuation_of_algebraMap]
    have := intValuation_le_one v n
    contrapose! this
    change 1 < v.intValuation n
    rw [← hk, mul_comm]
    exact (lt_mul_of_one_lt_right (by simp) hv).trans_le <|
      mul_le_mul_of_nonneg_right this (by simp)
  simp_rw [valuation_of_algebraMap]
  change {v : HeightOneSpectrum R | v.intValuationDef d < 1}.Finite
  simp_rw [intValuation_lt_one_iff_dvd]
  apply Ideal.finite_factors
  simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]

end IsFiniteAdele

end ProdAdicCompletions

open ProdAdicCompletions.IsFiniteAdele

/-- The finite adèle ring of `R` is the restricted product over all maximal ideals `v` of `R`
of `adicCompletion`, with respect to `adicCompletionIntegers`.

Note that we make this a `Type` rather than a `Subtype` (e.g., a `Subalgebra`) since we wish
to endow it with a finer topology than that of the subspace topology. -/
def FiniteAdeleRing : Type _ := {x : K_hat R K // x.IsFiniteAdele}

namespace FiniteAdeleRing

/-- The finite adèle ring of `R`, regarded as a `K`-subalgebra of the
product of the local completions of `K`.

Note that this definition exists to streamline the proof that the finite adèles are an algebra
over `K`, rather than to express their relationship to `K_hat R K` which is essentially a
detail of their construction.
-/
def subalgebra : Subalgebra K (K_hat R K) where
  carrier := {x : K_hat R K | x.IsFiniteAdele}
  mul_mem' := mul
  one_mem' := one
  add_mem' := add
  zero_mem' := zero
  algebraMap_mem' := algebraMap'

instance : CommRing (FiniteAdeleRing R K) :=
  Subalgebra.toCommRing (subalgebra R K)

instance : Algebra K (FiniteAdeleRing R K) :=
  Subalgebra.algebra (subalgebra R K)

instance : Algebra R (FiniteAdeleRing R K) :=
  ((algebraMap K (FiniteAdeleRing R K)).comp (algebraMap R K)).toAlgebra

instance : IsScalarTower R K (FiniteAdeleRing R K) :=
  IsScalarTower.of_algebraMap_eq' rfl

instance : Coe (FiniteAdeleRing R K) (K_hat R K) where
  coe x := x.1

@[simp, norm_cast]
theorem coe_one : (1 : FiniteAdeleRing R K) = (1 : K_hat R K) := rfl

@[simp, norm_cast]
theorem coe_zero : (0 : FiniteAdeleRing R K) = (0 : K_hat R K) := rfl

@[simp, norm_cast]
theorem coe_add (x y : FiniteAdeleRing R K) :
    (x + y : FiniteAdeleRing R K) = (x : K_hat R K) + (y : K_hat R K) :=
  rfl

@[simp, norm_cast]
theorem coe_mul (x y : FiniteAdeleRing R K) :
    (x * y : FiniteAdeleRing R K) = (x : K_hat R K) * (y : K_hat R K) :=
  rfl

@[simp, norm_cast]
theorem coe_algebraMap (x : K) :
    (((algebraMap K (FiniteAdeleRing R K)) x) : K_hat R K) =
      (algebraMap K (ProdAdicCompletions R K)) x :=
  rfl

@[ext]
lemma ext {a₁ a₂ : FiniteAdeleRing R K} (h : (a₁ : K_hat R K) = a₂) : a₁ = a₂ :=
  Subtype.ext h

/-- The finite adele ring is an algebra over the finite integral adeles. -/
instance : Algebra (R_hat R K) (FiniteAdeleRing R K) where
  smul rhat fadele := ⟨fun v ↦ rhat v * fadele.1 v, Finite.subset fadele.2 <| fun v hv ↦ by
    simp only [mem_adicCompletionIntegers, mem_compl_iff, mem_setOf_eq, map_mul] at hv ⊢
    exact mt (mul_le_one' (rhat v).2) hv
    ⟩
  algebraMap :=
  { toFun r := ⟨r, by simp_all⟩
    map_one' := by ext; rfl
    map_mul' _ _ := by ext; rfl
    map_zero' := by ext; rfl
    map_add' _ _ := by ext; rfl }
  commutes' _ _ := mul_comm _ _
  smul_def' _ _ := rfl

instance : DFunLike (FiniteAdeleRing R K) (HeightOneSpectrum R) (adicCompletion K) where
  coe a := a.1
  coe_injective' _a _b := ext _ _

open scoped algebraMap -- coercion from R to `FiniteAdeleRing R K`

variable {R K} in
lemma exists_finiteIntegralAdele_iff (a : FiniteAdeleRing R K) :
    (∃ c : R_hat R K, a = c) ↔ ∀ v : HeightOneSpectrum R, a v ∈ adicCompletionIntegers K v :=
  ⟨by rintro ⟨c, rfl⟩ v; exact (c v).2, fun h ↦ ⟨fun v ↦ ⟨a v, h v⟩, rfl⟩⟩

instance : Algebra (FiniteAdeleRing R K) (K_hat R K) := (subalgebra _ _).toAlgebra

instance : IsScalarTower (R_hat R K) (FiniteAdeleRing R K) (K_hat R K) where
  smul_assoc x y z := smul_mul_assoc x y.val z

@[simp, norm_cast]
theorem coe_algebraMap' (r : R_hat R K) :
    algebraMap (R_hat R K) (FiniteAdeleRing R K) r = algebraMap (R_hat R K) (K_hat R K) r :=
  rfl

instance : FaithfulSMul (FiniteAdeleRing R K) (K_hat R K) :=
    Subalgebra.instFaithfulSMulSubtypeMem (subalgebra _ _)

instance : FaithfulSMul (R_hat R K) (FiniteAdeleRing R K) :=
  let h := FaithfulSMul.algebraMap_injective (R_hat R K) (K_hat R K)
  (faithfulSMul_iff_algebraMap_injective _ _).2 ((funext (coe_algebraMap' R K)) ▸ h).of_comp

section Topology

open nonZeroDivisors
open scoped Multiplicative

variable {R K} in
lemma mul_nonZeroDivisor_mem_finiteIntegralAdeles (a : FiniteAdeleRing R K) :
    ∃ (b : R⁰) (c : R_hat R K), a * ((b : R) : FiniteAdeleRing R K) = c := by
  let S := {v | a v ∉ adicCompletionIntegers K v}
  choose b hb h using adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers (R := R) (K := K)
  let p := ∏ᶠ v ∈ S, b v (a v)
  have hp : p ∈ R⁰ := finprod_mem_induction (· ∈ R⁰) (one_mem _) (fun _ _ => mul_mem) <|
    fun _ _ ↦ hb _ _
  use ⟨p, hp⟩
  rw [exists_finiteIntegralAdele_iff]
  intro v
  by_cases hv : a v ∈ adicCompletionIntegers K v
  · exact mul_mem hv <| coe_mem_adicCompletionIntegers _ _
  · dsimp only
    have pprod : p = b v (a v) * ∏ᶠ w ∈ S \ {v}, b w (a w) := by
      rw [← finprod_mem_singleton (a := v) (f := fun v ↦ b v (a v)),
        finprod_mem_mul_diff (singleton_subset_iff.2 ‹v ∈ S›) a.2]
    rw [pprod]
    push_cast
    rw [← mul_assoc]
    exact mul_mem (h v (a v)) <| coe_mem_adicCompletionIntegers _ _

theorem submodulesRingBasis : SubmodulesRingBasis
    (fun (r : R⁰) ↦ Submodule.span (R_hat R K) {((r : R) : FiniteAdeleRing R K)}) where
  inter i j := ⟨i * j, by
    push_cast
    simp only [le_inf_iff, Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    exact ⟨⟨((j : R) : R_hat R K), by rw [mul_comm]; rfl⟩, ⟨((i : R) : R_hat R K), rfl⟩⟩⟩
  leftMul a r := by
    rcases mul_nonZeroDivisor_mem_finiteIntegralAdeles a with ⟨b, c, h⟩
    use r * b
    rintro x ⟨m, hm, rfl⟩
    simp only [Submonoid.coe_mul, SetLike.mem_coe] at hm
    rw [Submodule.mem_span_singleton] at hm ⊢
    rcases hm with ⟨n, rfl⟩
    simp only [LinearMapClass.map_smul, DistribMulAction.toLinearMap_apply, smul_eq_mul]
    use n * c
    push_cast
    rw [mul_left_comm, h, mul_comm _ (c : FiniteAdeleRing R K),
      Algebra.smul_def', Algebra.smul_def', ← mul_assoc]
    rfl
  mul r := ⟨r, by
    intro x hx
    rw [mem_mul] at hx
    rcases hx with ⟨a, ha, b, hb, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_span_singleton] at ha hb ⊢
    rcases ha with ⟨m, rfl⟩
    rcases hb with ⟨n, rfl⟩
    use m * n * (r : R)
    simp only [Algebra.smul_def', map_mul]
    rw [mul_mul_mul_comm, mul_assoc]
    rfl⟩

instance : TopologicalSpace (FiniteAdeleRing R K) :=
  SubmodulesRingBasis.topology (submodulesRingBasis R K)

-- the point of `submodulesRingBasis` above: this now works
example : IsTopologicalRing (FiniteAdeleRing R K) := inferInstance

end Topology

end FiniteAdeleRing

end DedekindDomain
