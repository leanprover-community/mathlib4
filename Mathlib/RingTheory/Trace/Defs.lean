/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Trace

/-!
# Trace for (finite) ring extensions.

Suppose we have an `R`-algebra `S` that is finite and projective as an `R`-module. For each `s : S`,
the trace of the linear map given by multiplying by `s` gives information about
the roots of the minimal polynomial of `s` over `R`.

## Main definitions

* `Algebra.trace R S x`: the trace of an element `s` of an `R`-algebra `S`
* `Algebra.traceForm R S`: bilinear form sending `x`, `y` to the trace of `x * y`
* `Algebra.traceMatrix R b`: the matrix whose `(i j)`-th element is the trace of `b i * b j`.

## Main results

* `trace_algebraMap_of_basis`, `trace_algebraMap`: if `x : K`, then `Tr_{L/K} x = [L : K] x`
* `trace_trace`, `trace_comp_trace`: `Tr_{L/K} (Tr_{F/L} x) = Tr_{F/K} x`

## Implementation notes

The trace is defined under the assumption of finiteness and projectiveness.
This includes the common finite free case.

We only define the trace for left multiplication (`Algebra.leftMulMatrix`,
i.e. `LinearMap.mulLeft`).
For now, the definitions assume `S` is commutative, so the choice doesn't matter anyway.

## References

* https://en.wikipedia.org/wiki/Field_trace

-/

@[expose] public section


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

variable (R S) [Module.Finite R S] [Module.Projective R S]

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

variable {R}

-- Can't be a `simp` lemma because it depends on a choice of basis
theorem trace_eq_matrix_trace [DecidableEq ι] (b : Basis ι R S) (s : S) :
    trace R S s = Matrix.trace (Algebra.leftMulMatrix b s) := by
  rw [trace_apply, LinearMap.trace_eq_matrix_trace _ b, ← toMatrix_lmul_eq]; rfl

/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`. -/
theorem trace_algebraMap_of_basis (b : Basis ι R S) (x : R) :
    trace R S (algebraMap R S x) = Fintype.card ι • x := by
  have := Classical.decEq ι
  rw [trace_apply, LinearMap.trace_eq_matrix_trace R b, Matrix.trace]
  convert! Finset.sum_const x
  simp [-coe_lmul_eq_mul]


/-- The trace map from `R` to itself is the identity map. -/
@[simp] theorem trace_self : trace R R = LinearMap.id := by
  ext; simpa using trace_algebraMap_of_basis (.singleton (Fin 1) R) 1

theorem trace_self_apply (a) : trace R R a = a := by simp

/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`. -/
@[simp]
theorem trace_algebraMap [StrongRankCondition R] [Module.Free R S] (x : R) :
    trace R S (algebraMap R S x) = finrank R S • x := by
  rw [trace_algebraMap_of_basis (Module.Free.chooseBasis R S),
    finrank_eq_card_basis (Module.Free.chooseBasis R S)]

/-- Trace along a tower is transitive for finite projective algebras. -/
@[simp]
theorem trace_trace [Algebra S T] [IsScalarTower R S T]
    [Module.Finite S T] [Module.Projective S T]
    [Module.Finite R T] [Module.Projective R T] (x : T) :
    trace R S (trace S T x) = trace R T x := by
  have h (f : T →ₗ[S] T) :
      trace R S (LinearMap.trace S T f) = LinearMap.trace R T (f.restrictScalars R) := by
    obtain ⟨u, rfl⟩ := (dualTensorHomEquiv S T T).surjective f
    induction u using TensorProduct.inductionOn with
    | add u v hu hv => simp_all
    | tmul φ t =>
      let i : S →ₗ[R] T := ((LinearMap.id : S →ₗ[S] S).smulRight t).restrictScalars R
      let p : T →ₗ[R] S := φ.restrictScalars R
      have hcomp : (φ.smulRight t).restrictScalars R = i ∘ₗ p := rfl
      have hmul : p ∘ₗ i = lmul R S (φ t) := by ext s; simp [i, p, mul_comm]
      change trace R S (LinearMap.trace S T (φ.smulRight t)) =
        LinearMap.trace R T ((φ.smulRight t).restrictScalars R)
      rw [LinearMap.trace_smulRight, hcomp, LinearMap.trace_comp_comm' p i, hmul]
      rfl
  exact h (lmul S T x)

/-- Let `T / S / R` be a tower of finite projective algebras. Then
$\text{Trace}_{T/R} = \text{Trace}_{S/R} \circ \text{Trace}_{T/S}$. -/
@[simp, stacks 0BIJ "Trace"]
theorem trace_comp_trace [Algebra S T] [IsScalarTower R S T]
    [Module.Finite S T] [Module.Projective S T]
    [Module.Finite R T] [Module.Projective R T] :
    (trace R S).comp ((trace S T).restrictScalars R) = trace R T := by
  exact LinearMap.ext trace_trace

@[simp]
theorem trace_prod_apply [Module.Projective R T] [Module.Finite R T]
    (x : S × T) : trace R (S × T) x = trace R S x.fst + trace R T x.snd := by
  exact trace_prodMap' (lmul R S x.1) (lmul R T x.2)

theorem trace_prod [Module.Projective R T] [Module.Finite R T] :
    trace R (S × T) = (trace R S).coprod (trace R T) :=
  LinearMap.ext fun p => by rw [coprod_apply, trace_prod_apply]

section TraceForm

variable (R S)
open LinearMap
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
  ⟨fun _ _ => congr(trace R S $(mul_comm ..))⟩

theorem traceForm_toMatrix [DecidableEq ι] (b : Basis ι R S) (i j) :
    (traceForm R S).toMatrix b i j = trace R S (b i * b j) := by
  rw [LinearMap.BilinForm.toMatrix_apply, traceForm_apply]

end TraceForm

end Algebra
