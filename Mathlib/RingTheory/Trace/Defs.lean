/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Trace

/-!
# Trace for (finite) ring extensions.

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the trace of the linear map given by multiplying by `s` gives information about
the roots of the minimal polynomial of `s` over `R`.

## Main definitions

* `Algebra.trace R S x`: the trace of an element `s` of an `R`-algebra `S`
* `Algebra.traceForm R S`: bilinear form sending `x`, `y` to the trace of `x * y`
* `Algebra.traceMatrix R b`: the matrix whose `(i j)`-th element is the trace of `b i * b j`.

## Main results

* `trace_algebraMap_of_basis`, `trace_algebraMap`: if `x : K`, then `Tr_{L/K} x = [L : K] x`
* `trace_trace_of_basis`, `trace_trace`: `Tr_{L/K} (Tr_{F/L} x) = Tr_{F/K} x`

## Implementation notes

Typically, the trace is defined specifically for finite field extensions.
The definition is as general as possible and the assumption that the extension is finite
is added to the lemmas as needed.

We only define the trace for left multiplication (`Algebra.leftMulMatrix`,
i.e. `LinearMap.mulLeft`).
For now, the definitions assume `S` is commutative, so the choice doesn't matter anyway.

## References

* https://en.wikipedia.org/wiki/Field_trace

-/


universe w

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]
variable {ι : Type w} [Fintype ι]

open Module

open LinearMap (BilinForm)
open LinearMap

open Matrix

open scoped Matrix

namespace Algebra

variable (R S)

/-- The trace of an element `s` of an `R`-algebra is the trace of `(s * ·)`,
as an `R`-linear map. -/
@[stacks 0BIF "Trace"]
noncomputable def trace : S →ₗ[R] R :=
  (LinearMap.trace R S).comp (lmul R S).toLinearMap

variable {S}

-- Not a `simp` lemma since there are more interesting ways to rewrite `trace R S x`,
-- for example `trace_trace`
theorem trace_apply (x) : trace R S x = LinearMap.trace R S (lmul R S x) :=
  rfl

theorem trace_eq_zero_of_not_exists_basis (h : ¬∃ s : Finset S, Nonempty (Basis s R S)) :
    trace R S = 0 := by ext s; simp [trace_apply, LinearMap.trace, h]

variable {R}

-- Can't be a `simp` lemma because it depends on a choice of basis
theorem trace_eq_matrix_trace [DecidableEq ι] (b : Basis ι R S) (s : S) :
    trace R S s = Matrix.trace (Algebra.leftMulMatrix b s) := by
  rw [trace_apply, LinearMap.trace_eq_matrix_trace _ b, ← toMatrix_lmul_eq]; rfl

/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`. -/
theorem trace_algebraMap_of_basis (b : Basis ι R S) (x : R) :
    trace R S (algebraMap R S x) = Fintype.card ι • x := by
  haveI := Classical.decEq ι
  rw [trace_apply, LinearMap.trace_eq_matrix_trace R b, Matrix.trace]
  convert Finset.sum_const x
  simp [-coe_lmul_eq_mul]


/-- The trace map from `R` to itself is the identity map. -/
@[simp] theorem trace_self : trace R R = LinearMap.id := by
  ext; simpa using trace_algebraMap_of_basis (.singleton (Fin 1) R) 1

theorem trace_self_apply (a) : trace R R a = a := by simp

/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`.

(If `L` is not finite-dimensional over `K`, then `trace` and `finrank` return `0`.)
-/
@[simp]
theorem trace_algebraMap [StrongRankCondition R] [Module.Free R S] (x : R) :
    trace R S (algebraMap R S x) = finrank R S • x := by
  by_cases H : ∃ s : Finset S, Nonempty (Basis s R S)
  · rw [trace_algebraMap_of_basis H.choose_spec.some, finrank_eq_card_basis H.choose_spec.some]
  · simp [trace_eq_zero_of_not_exists_basis R H, finrank_eq_zero_of_not_exists_basis_finset H]

theorem trace_trace_of_basis [Algebra S T] [IsScalarTower R S T] {ι κ : Type*} [Finite ι]
    [Finite κ] (b : Basis ι R S) (c : Basis κ S T) (x : T) :
    trace R S (trace S T x) = trace R T x := by
  haveI := Classical.decEq ι
  haveI := Classical.decEq κ
  cases nonempty_fintype ι
  cases nonempty_fintype κ
  rw [trace_eq_matrix_trace (b.smulTower c), trace_eq_matrix_trace b, trace_eq_matrix_trace c,
    Matrix.trace, Matrix.trace, Matrix.trace, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [map_sum, smulTower_leftMulMatrix, Finset.sum_apply, Matrix.diag,
    Finset.sum_apply i (Finset.univ : Finset κ) fun y => leftMulMatrix b (leftMulMatrix c x y y)]

theorem trace_comp_trace_of_basis [Algebra S T] [IsScalarTower R S T] {ι κ : Type*} [Finite ι]
    [Finite κ] (b : Basis ι R S) (c : Basis κ S T) :
    (trace R S).comp ((trace S T).restrictScalars R) = trace R T := by
  ext
  rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, trace_trace_of_basis b c]

@[simp]
theorem trace_trace [Algebra S T] [IsScalarTower R S T]
    [Module.Free R S] [Module.Finite R S] [Module.Free S T] [Module.Finite S T] (x : T) :
    trace R S (trace S T x) = trace R T x :=
  trace_trace_of_basis (Module.Free.chooseBasis R S) (Module.Free.chooseBasis S T) x

/-- Let `T / S / R` be a tower of finite extensions of fields. Then
$\text{Trace}_{T/R} = \text{Trace}_{S/R} \circ \text{Trace}_{T/S}$. -/
@[simp, stacks 0BIJ "Trace"]
theorem trace_comp_trace [Algebra S T] [IsScalarTower R S T]
    [Module.Free R S] [Module.Finite R S] [Module.Free S T] [Module.Finite S T] :
    (trace R S).comp ((trace S T).restrictScalars R) = trace R T :=
  LinearMap.ext trace_trace

@[simp]
theorem trace_prod_apply [Module.Free R S] [Module.Free R T] [Module.Finite R S] [Module.Finite R T]
    (x : S × T) : trace R (S × T) x = trace R S x.fst + trace R T x.snd := by
  nontriviality R
  let f := (lmul R S).toLinearMap.prodMap (lmul R T).toLinearMap
  have : (lmul R (S × T)).toLinearMap = (prodMapLinear R S T S T R).comp f :=
    LinearMap.ext₂ Prod.mul_def
  simp_rw [trace, this]
  exact trace_prodMap' _ _

theorem trace_prod [Module.Free R S] [Module.Free R T] [Module.Finite R S] [Module.Finite R T] :
    trace R (S × T) = (trace R S).coprod (trace R T) :=
  LinearMap.ext fun p => by rw [coprod_apply, trace_prod_apply]

section TraceForm

variable (R S)

/-- The `traceForm` maps `x y : S` to the trace of `x * y`.
It is a symmetric bilinear form and is nondegenerate if the extension is separable. -/
@[stacks 0BIK "Trace pairing"]
noncomputable def traceForm : BilinForm R S :=
  LinearMap.compr₂ (lmul R S).toLinearMap (trace R S)

variable {S}

-- This is a nicer lemma than the one produced by `@[simps] def traceForm`.
@[simp]
theorem traceForm_apply (x y : S) : traceForm R S x y = trace R S (x * y) :=
  rfl

theorem traceForm_isSymm : (traceForm R S).IsSymm :=
  ⟨fun _ _ => congr_arg (trace R S) (mul_comm _ _)⟩

theorem traceForm_toMatrix [DecidableEq ι] (b : Basis ι R S) (i j) :
    BilinForm.toMatrix b (traceForm R S) i j = trace R S (b i * b j) := by
  rw [BilinForm.toMatrix_apply, traceForm_apply]

end TraceForm

end Algebra
